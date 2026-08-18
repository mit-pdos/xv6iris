(* SRegime.v -- the S-mode TRANSLATION REGIME interface: ONE record
   abstracting how an S-mode instruction's fetch/data translation is
   absorbed, so the engine + leaf layer serves Sv39 (paging on, the
   kernel table installed) and BARE (boot, satp=0) without duplication.

   [sr_absorb] is the TrampStepPt-Habs shape, access-generic over the
   four access classes, keyed on a kernel-mapping CLAIM [kmap_at (svpn_of
   va) ppn pc] + the class [pc] it must admit ([kperm_allows]) + the
   regime's own ADMISSIBILITY of that claim ([sr_adm]), with the
   output pa = ppn ++ pageoff (rwx-kmap).  Every consumer presents the
   claim carried in its OWN resource (the fetch window's [↦ₓ□] bytes, a
   datum's [↦ₘ], a device vpn's static bundle claim), so there is no
   identity/region assumption at this altitude.  The PMP grant facts at
   the output state are exposed for the subsequent memory access.
   Instances:
     - [kpt_share_regime root_ppn] (§3): sr_inv := [KptShare.tlb_res_pt
       root_ppn], the per-hart residue of the SHARED kernel table -- the
       whole sconf tier's Sv39 instance.  Its absorb is the one that
       actually uses the mask (it opens [kptN]).
     - [bare_regime]: satp pinned to Mode=Bare + pmp_config, ALL per-hart;
       translation short-circuits to the identity before touching the TLB
       ([exec_translateAddr_bare]), so absorption is trivial -- provided
       the claim IS the identity, which is the [sr_adm] field below.
   There is deliberately NO instance over the EXCLUSIVE [tlb_inv_pt]: the
   userret/uservec island that still owns the kernel tree outright
   (TrampStepPt / UserretEntryPt / UservecExitPt) drives KptTree's
   absorption theorems directly and never goes through this record.    *)
From Stdlib Require Import ZArith Bool.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap ghost_map ghost_var.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec RiscvExtras.
Require Import SmodePte KptPt.
Require Import WpGpr WpMmodeLeafBase ExecCommon.
Require Import KptTree.
Require Import KptPt.
Require Import RiscvExtras.
Require Import SmodePte.
Require Import KptGhost.   (* kptN: the shared kernel table's namespace, named in [sr_absorb]'s mask premise *)
Require Import KptShare.   (* the SHARED-table regime instance (§3) *)
Require Import WpDecodeBridge CommonWalk PtTree PtTreeAdue PtAdBits Pt4kWalk.
Require Import HartSwp HartLift HartRegNode HartSpan HartSpanChar HartGoodb HartEvents.
Require Import HartSTrans HartSKpt KptGoodb.
Require Import Riscv.rv64d_types Riscv.rv64d.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* §1 Pure BARE-mode translateAddr reduction.                             *)
(* ===================================================================== *)

Lemma exec_translationMode_S_bare (satp0 : mword 64) s :
  _get_Mstatus_SXL (register_lookup mstatus s.(sregs)) = 'b"10" ->
  register_lookup satp s.(sregs) = satp0 ->
  _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"0000" : mword 4) ->
  exec (translationMode Supervisor) s = Some (Bare, s).
Proof.
  intros HSXL Hsatp Hmode.
  unfold translationMode.
  replace (generic_eq Supervisor Machine) with false by (vm_compute; reflexivity).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_architecture_Supervisor s HSXL)).
  cbn match.
  change (xlen >=? 64) with true.
  match goal with |- exec (Defs.bind ?ARM _) s = _ =>
    assert (HARM : exec ARM s = Some (_get_Satp64_Mode (Mk_Satp64 satp0), s)) end.
  { assert (Hae : exec (Defs.assert_exp' true "sys/vmem.sail:254.25-254.26") s
                  = Some (eq_refl, s)).
    { unfold assert_exp'. cbn match. apply exec_returnm. }
    rewrite (exec_bind_Some _ _ _ _ _ Hae).
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg satp s)).
    rewrite Hsatp. apply exec_returnm. }
  rewrite (exec_bind_Some _ _ _ _ _ HARM).
  rewrite Hmode.
  replace (satpMode_of_bits RV64 ('b"0000" : mword 4)) with (Some Bare)
    by (vm_compute; reflexivity).
  cbn match. apply exec_returnm.
Qed.

Section BareFront.
  Context (acc : MemoryAccessType mem_payload).

  Lemma exec_translateAddr_bare (va : mword 64) (s : mstate) :
    exec (effectivePrivilege acc (register_lookup mstatus s.(sregs)) Supervisor) s
      = Some (Supervisor, s) ->
    exec (is_shadow_stack_access acc) s = Some (false, s) ->
    register_lookup cur_privilege s.(sregs) = Supervisor ->
    exec (translationMode Supervisor) s = Some (Bare, s) ->
    exec (translateAddr (Virtaddr va) acc) s
    = Some (Ok (Physaddr va, PBMT_PMA, init_ext_ptw), s).
  Proof.
    intros Heff Hss Hcp Htm.
    unfold translateAddr.
    rewrite exec_catch_early_return.
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg mstatus s)).
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg cur_privilege s)).
    rewrite Hcp.
    rewrite (execR_liftR_seq _ _ _ _ _ Heff).
    rewrite (execR_liftR_seq _ _ _ _ _ Htm).
    rewrite (execR_liftR_seq _ _ _ _ _ Hss).
    unfold Defs.bind0.
    replace (generic_eq Bare Bare) with true by (vm_compute; reflexivity).
    rewrite execR_bind. rewrite execR_returnR. cbn match.
    rewrite execR_returnR.
    cbn [bits_of_virtaddr].
    rewrite zero_extend'_id.
    reflexivity.
  Qed.

End BareFront.

(* ===================================================================== *)
(* §1b The pointer-masking effective-address transform is the IDENTITY    *)
(*     at pmlen 0, in EITHER translation mode -- the ONE fact the data    *)
(*     towers need from the mode.                                         *)
(* ===================================================================== *)

Lemma pm_transform_VA_0 (ea : mword 64) :
  pm_transform_VA (Virtaddr ea) 0 = Virtaddr ea.
Proof.
  unfold pm_transform_VA. f_equal.
  change (xlen - 0 - 1) with (xlen - 0 - 1).
  rewrite subrange_id. apply sign_extend'_id.
Qed.

Lemma pm_transform_PA_0 (ea : mword 64) :
  pm_transform_PA (Virtaddr ea) 0 = Virtaddr ea.
Proof.
  unfold pm_transform_PA. f_equal.
  rewrite subrange_id. apply zero_extend'_id.
Qed.

Section TransformFront.
  Context (acc : MemoryAccessType mem_payload).

  (* mode-GENERIC: with PMM off (pmlen 0) the transform is the identity
     whatever [translationMode] returns *)
  Lemma exec_transform_effective_address_mode (md : SATPMode) (ea : mword 64) (s : mstate) :
    register_lookup cur_privilege s.(sregs) = Supervisor ->
    exec (effectivePrivilege acc (register_lookup mstatus s.(sregs)) Supervisor) s
      = Some (Supervisor, s) ->
    exec (get_pmlen acc Supervisor) s = Some (0, s) ->
    exec (translationMode Supervisor) s = Some (md, s) ->
    exec (transform_effective_address (Virtaddr ea) acc) s = Some (Virtaddr ea, s).
  Proof.
    intros Hcp Heff Hpml Htm.
    unfold transform_effective_address.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mstatus s)).
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)).
    rewrite Hcp.
    rewrite (exec_bind_Some _ _ _ _ _ Heff).
    rewrite (exec_bind_Some _ _ _ _ _ Hpml).
    rewrite (exec_bind_Some _ _ _ _ _ Htm).
    destruct (generic_eq md Bare);
      [ rewrite pm_transform_PA_0 | rewrite pm_transform_VA_0 ];
      apply exec_returnM.
  Qed.

End TransformFront.

(* ===================================================================== *)
(* §2 The regime record + the BARE instance (the Sv39 one is §3).          *)
(* ===================================================================== *)

(* the access classes the S-mode leaves use *)
(* [Atomic]'s two booleans are the instruction's aq/rl annotations, which
   nothing in the translation or PMP/PMA path inspects -- so the AMO arm
   quantifies them rather than pinning one annotation pair. *)
Definition s_acc_ok (acc : MemoryAccessType mem_payload) : Prop :=
  acc = InstructionFetch tt \/ acc = Load Data \/ acc = Store Data \/
  (exists aq rl, acc = Atomic (AMOSWAP, aq, rl, Data, Data)).

(* the PMP grant facts at a state: the kernel TOR entry 0 covering RAM
   with R/W/X (what every post-translate memory access checks) *)
Definition pmp_grant_facts (σ : mstate) : Prop :=
  pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n σ.(sregs)) 0)) = TOR /\
  zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n σ.(sregs)) 0) = false /\
  eq_vec (_get_Pmpcfg_ent_X (vec_access_dec (register_lookup pmpcfg_n σ.(sregs)) 0)) ('b"1") = true /\
  eq_vec (_get_Pmpcfg_ent_W (vec_access_dec (register_lookup pmpcfg_n σ.(sregs)) 0)) ('b"1") = true /\
  eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n σ.(sregs)) 0)) ('b"1") = true /\
  (ram_base + ram_size <= uint (vec_access_dec (register_lookup pmpaddr_n σ.(sregs)) 0) * 4)%Z.

(* THE BARE ARM'S ADMISSIBILITY (the [s_regime] field [sr_adm] below): a
   claim is admissible under Bare exactly when it is the IDENTITY -- the pa
   it takes [va] to IS [va].  A [↦ₘ]/[↦ₓ] datum carries this as a conjunct
   and a static device claim is built at [kpt_leaf_ppn], so every consumer
   discharges it locally; the Sv39 arm needs nothing ([True]). *)
Definition kadm_ident (va : mword 64) (ppn : mword 44) : Prop :=
  pa_of ppn va = va.

Section SRegimeDef.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Record s_regime := SRegime {
    sr_inv : iProp Σ;
    (* ADMISSIBILITY of a claim under this regime (claude-notes/projects/
       bare-inv-generic.md).  A pure side condition on the CLAIM the
       consumer presents -- its va and the ppn it maps to -- taken as a
       premise by [sr_absorb].  It cannot be uniform: the Sv39 arm honours
       every claim ([True]), while the BARE arm can only ever honour an
       IDENTITY claim ([kadm_ident]: a hart with satp=Bare translates va to
       va itself).  Every consumer discharges it from its OWN resource --
       [↦ₘ]/[↦ₓ] carry the identity conjunct, a device claim is built at
       [kpt_leaf_ppn] -- so no leaf statement and no whole-function
       contract mentions it. *)
    sr_adm : mword 64 -> mword 44 -> Prop;
    (* ...and the one thing EVERY regime admits: an IDENTITY claim.  This is
       what keeps the premise off the REGIME-GENERIC layer (the fetch engine,
       the walk leaves): they discharge [sr_adm] from their datum's identity
       conjunct through this field, so no statement grows a premise.  A
       consumer that presents a NON-identity claim (a kstack/trampoline va,
       the sp-migration project) must instead know its regime and discharge
       [sr_adm] for it directly -- which is exactly what the Sv39 arm's
       [True] instance makes free and the Bare arm's makes impossible. *)
    sr_adm_id : forall (va : mword 64) (ppn : mword 44),
      kadm_ident va ppn -> sr_adm va ppn;
    (* THE re-keyed absorption (rwx-kmap): keyed on a kernel-mapping CLAIM
       [kmap_at (svpn_of va) ppn pc] + the access class it must admit,
       with the output pa = ppn ++ pageoff.  The claim is supplied by the
       consumer's OWN resource (fetch [↦ₓ□] window / datum [↦ₘ] / device
       static bundle), so no identity or region premise rides here. *)
    (* MASK-CARRYING (claude-notes/completed/kpt-share.md): the SHARED
       kernel-table regime absorbs by OPENING the [kptN] invariant, so the
       field is a fupd at any mask containing [↑kptN].  The two exclusive
       instances below open nothing and merely weaken their [==∗].  Call
       sites leave both the mask and its subset proof as holes:
         unshelve iMod (sr_absorb R acc va pa ppn pc σ _ <pure args> _
                          with "...") as ...; [solve_ndisj |].            *)
    sr_absorb : forall (acc : MemoryAccessType mem_payload) (va pa : mword 64)
        (ppn : mword 44) (pc : kperm) (σ : mstate) (E : coPset),
      s_acc_ok acc ->
      kperm_allows pc acc ->
      neq_vec (bits_of_virtaddr (Virtaddr va))
         (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
      zero_extend' 64 (concat_vec ppn
          (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub pagesize_bits 1) 0)) = pa ->
      register_lookup misa σ.(sregs) = MISA_C ->
      register_lookup menvcfg σ.(sregs) = MENVCFG_S ->
      register_lookup htif_tohost_base σ.(sregs) = None ->
      register_lookup cur_privilege σ.(sregs) = Supervisor ->
      _get_Mstatus_SXL (register_lookup mstatus σ.(sregs)) = 'b"10" ->
      exec (effectivePrivilege acc (register_lookup mstatus σ.(sregs)) Supervisor) σ
        = Some (Supervisor, σ) ->
      exec (is_shadow_stack_access acc) σ = Some (false, σ) ->
      pma_allows_all (register_lookup pma_regions σ.(sregs)) ->
      sr_adm va ppn ->
      ↑kptN ⊆ E ->
      ⊢ kmap_at (svpn_of va) ppn pc -∗
        reg_interp σ.(sregs) -∗ gen_heap_interp σ.(mem) -∗ sr_inv ={E}=∗
        ∃ σ' : mstate,
          ⌜ exec (translateAddr (Virtaddr va) acc) σ
            = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), σ') ⌝ ∗
          ⌜ σ'.(mdev) = σ.(mdev) ⌝ ∗
          ⌜ (σ'.(sregs) = σ.(sregs) \/
             exists tv, σ'.(sregs) = register_set tlb tv σ.(sregs))%type ⌝ ∗
          ⌜ pmp_grant_facts σ' ⌝ ∗
          reg_interp σ'.(sregs) ∗ gen_heap_interp σ'.(mem) ∗ sr_inv;
    sr_transform : forall (acc : MemoryAccessType mem_payload) (ea : mword 64) (σ : mstate),
      s_acc_ok acc ->
      register_lookup cur_privilege σ.(sregs) = Supervisor ->
      _get_Mstatus_SXL (register_lookup mstatus σ.(sregs)) = 'b"10" ->
      exec (effectivePrivilege acc (register_lookup mstatus σ.(sregs)) Supervisor) σ
        = Some (Supervisor, σ) ->
      exec (get_pmlen acc Supervisor) σ = Some (0, σ) ->
      ⊢ reg_interp σ.(sregs) -∗ sr_inv -∗
        ⌜ exec (transform_effective_address (Virtaddr ea) acc) σ = Some (Virtaddr ea, σ) ⌝;
    (* THE TRANSLATION MODE IS DEFINED.  The vmem level now resolves the
       effective privilege and its translation mode BEFORE the access (it is
       the page-split test), so every consumer of a vmem-level lemma needs a
       [translationMode] fact at the PRE-state.  Only the regime knows satp,
       so only the regime can say it -- and every regime can: satp is Bare or
       Sv39 here, never the reserved encoding.  The value is existential
       because nothing downstream cares which. *)
    sr_tmode : forall (σ : mstate),
      _get_Mstatus_SXL (register_lookup mstatus σ.(sregs)) = 'b"10" ->
      ⊢ reg_interp σ.(sregs) -∗ sr_inv -∗
        ⌜ exists md, exec (translationMode Supervisor) σ = Some (md, σ) ⌝;
    (* THE WITNESSED absorption (claude-notes/projects/sp-migration.md
       design §3): a SECOND way to discharge admissibility, gated on a
       PERSISTENT WITNESS instead of the [sr_adm] premise above.  Where
       [sr_adm_id] says "this regime honors an IDENTITY claim", [sr_kwit]
       says "this regime honors EVERY claim" -- and unlike [sr_adm], that
       is not uniformly true, so it cannot be a bare field: a regime that
       does NOT honor every claim (Bare) must make [sr_kwit] itself
       unsatisfiable, so unsoundness surfaces as an unpayable WITNESS
       rather than an unpayable premise.  [kpt_share_regime]'s Sv39 walk
       honors every claim for free, so its witness is [emp].
       [strans_regime]'s witness pins its folded slot's arm at KPT
       ([kpt_on cpu_id]): a Bare arm holder cannot produce it, so the
       Bare arm never has to reconcile a non-identity claim.  This is the
       route a NON-identity claim (a KSTACK/trampoline va) uses once its
       holder knows its hart is at KPT, with no per-address premise
       anywhere in the leaf/engine layer. *)
    sr_kwit : iProp Σ;
    sr_kwit_pers : Persistent sr_kwit;
    sr_absorb_wit : forall (acc : MemoryAccessType mem_payload) (va pa : mword 64)
        (ppn : mword 44) (pc : kperm) (σ : mstate) (E : coPset),
      s_acc_ok acc ->
      kperm_allows pc acc ->
      neq_vec (bits_of_virtaddr (Virtaddr va))
         (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
      zero_extend' 64 (concat_vec ppn
          (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub pagesize_bits 1) 0)) = pa ->
      register_lookup misa σ.(sregs) = MISA_C ->
      register_lookup menvcfg σ.(sregs) = MENVCFG_S ->
      register_lookup htif_tohost_base σ.(sregs) = None ->
      register_lookup cur_privilege σ.(sregs) = Supervisor ->
      _get_Mstatus_SXL (register_lookup mstatus σ.(sregs)) = 'b"10" ->
      exec (effectivePrivilege acc (register_lookup mstatus σ.(sregs)) Supervisor) σ
        = Some (Supervisor, σ) ->
      exec (is_shadow_stack_access acc) σ = Some (false, σ) ->
      pma_allows_all (register_lookup pma_regions σ.(sregs)) ->
      ↑kptN ⊆ E ->
      ⊢ sr_kwit -∗ kmap_at (svpn_of va) ppn pc -∗
        reg_interp σ.(sregs) -∗ gen_heap_interp σ.(mem) -∗ sr_inv ={E}=∗
        ∃ σ' : mstate,
          ⌜ exec (translateAddr (Virtaddr va) acc) σ
            = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), σ') ⌝ ∗
          ⌜ σ'.(mdev) = σ.(mdev) ⌝ ∗
          ⌜ (σ'.(sregs) = σ.(sregs) \/
             exists tv, σ'.(sregs) = register_set tlb tv σ.(sregs))%type ⌝ ∗
          ⌜ pmp_grant_facts σ' ⌝ ∗
          reg_interp σ'.(sregs) ∗ gen_heap_interp σ'.(mem) ∗ sr_inv;
  }.

  (* ---- the PMP facts, off any invariant that carries [pmp_config] ---- *)
  Lemma pmp_config_grant_facts (r : mword 44) (σ : mstate) :
    reg_interp σ.(sregs) -∗ pmp_config r -∗ ⌜pmp_grant_facts σ⌝.
  Proof.
    iIntros "Hri Hpmp".
    iDestruct "Hpmp" as (pmpcfg0 pmpaddr00)
      "(Hpc & Hpa & %HA & %Hord & %HX & %HW & %HR & %Hcov)".
    iDestruct (reg_valid_dq with "Hri Hpc") as %Hpcv.
    iDestruct (reg_valid_dq with "Hri Hpa") as %Hpav.
    iPureIntro. rewrite /pmp_grant_facts Hpcv Hpav. tauto.
  Qed.


  (* ------------------------------------------------------------------- *)
  (* The BARE instance (boot: satp Mode = Bare, translation = identity).   *)
  (* ------------------------------------------------------------------- *)
  (* PER-HART, and holding NOTHING globally unique (claude-notes/projects/
     bare-inv-generic.md): this hart's satp cell pinned at Mode=Bare plus
     its PMP config.  Honoring is not a ghost argument at all -- Bare
     translates va to va, so the arm admits exactly the IDENTITY claims
     ([kadm_ident], the regime's [sr_adm]) and the caller's resource
     supplies that.  Hence EVERY hart can be in its Bare arm at once, and
     the arm survives the kernel map's growth (a secondary hart spins on
     [started] in Bare long after the boot hart's satp switch). *)
  (* THE tlb CELL IS A MEMBER, added 2026-08-18 with the swp layer.  At the
     exec layer nobody owned it (it lived in the sigma the whole-instruction
     rule handed out); at the swp layer the S-mode frame [HartSFrame.s_Drw]
     OWNS it, because a Sv39 fetch WRITES it (the TLB fill) and
     [SRegime.sr_swp_translate] demands [(tlb : register) ∈ Drw].  So every
     S-mode translation slot must fund that cell, and [tlb_res_pt] already
     did -- this is the Bare arm catching up.  The cell is unconstrained
     here: Bare never reads or writes it. *)
  Definition bare_inv : iProp Σ :=
    (∃ (satp0 : mword 64) (tlbv : type_of_register tlb),
       satp ↦ᵣ satp0 ∗
       ⌜ _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"0000" : mword 4) ⌝ ∗
       tlb ↦ᵣ tlbv ∗
       pmp_config (mword_of_int 0))%I.

  Lemma bare_absorb :
    forall acc va pa (ppn : mword 44) (pc : kperm) σ (E : coPset), s_acc_ok acc ->
      kperm_allows pc acc ->
      neq_vec (bits_of_virtaddr (Virtaddr va))
         (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
      zero_extend' 64 (concat_vec ppn
          (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub pagesize_bits 1) 0)) = pa ->
      register_lookup misa σ.(sregs) = MISA_C ->
      register_lookup menvcfg σ.(sregs) = MENVCFG_S ->
      register_lookup htif_tohost_base σ.(sregs) = None ->
      register_lookup cur_privilege σ.(sregs) = Supervisor ->
      _get_Mstatus_SXL (register_lookup mstatus σ.(sregs)) = 'b"10" ->
      exec (effectivePrivilege acc (register_lookup mstatus σ.(sregs)) Supervisor) σ
        = Some (Supervisor, σ) ->
      exec (is_shadow_stack_access acc) σ = Some (false, σ) ->
      pma_allows_all (register_lookup pma_regions σ.(sregs)) ->
      kadm_ident va ppn ->
      ↑kptN ⊆ E ->
      ⊢ kmap_at (svpn_of va) ppn pc -∗
        reg_interp σ.(sregs) -∗ gen_heap_interp σ.(mem) -∗ bare_inv ={E}=∗
        ∃ σ' : mstate,
          ⌜ exec (translateAddr (Virtaddr va) acc) σ
            = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), σ') ⌝ ∗
          ⌜ σ'.(mdev) = σ.(mdev) ⌝ ∗
          ⌜ (σ'.(sregs) = σ.(sregs) \/
             exists tv, σ'.(sregs) = register_set tlb tv σ.(sregs))%type ⌝ ∗
          ⌜ pmp_grant_facts σ' ⌝ ∗
          reg_interp σ'.(sregs) ∗ gen_heap_interp σ'.(mem) ∗ bare_inv.
  Proof.
    intros acc va pa ppn pc σ E Hacc Hallow Hcanon Hconcat Hmisa Hmenv Hhtif Hcp HSXL Heff Hss Hall Hadm HE.
    iIntros "Hat Hri Hgh Hinv".
    iDestruct "Hinv" as (satp0 tlbv0) "(Hsatp & %Hmode & Htlb0 & Hpmp)".
    (* honoring: the claim is ADMISSIBLE, i.e. the identity -- so the pa the
       caller derived from it is va itself, which is what Bare translates to *)
    assert (Hpa : pa = va).
    { rewrite <- Hconcat. exact Hadm. }
    clear Hconcat. subst pa.
    iDestruct (reg_valid_dq with "Hri Hsatp") as %Hsatpv.
    iDestruct (pmp_config_grant_facts (mword_of_int 0) σ with "Hri Hpmp") as %Hpmp.
    iModIntro. iExists σ.
    iSplit.
    { iPureIntro.
      exact (exec_translateAddr_bare acc va σ Heff Hss Hcp
               (exec_translationMode_S_bare satp0 σ HSXL Hsatpv Hmode)). }
    iSplit; [iPureIntro; reflexivity |].
    iSplit; [iPureIntro; left; reflexivity |].
    iSplit; [iPureIntro; exact Hpmp |].
    iFrame "Hri Hgh".
    iExists satp0, tlbv0. iFrame "Hsatp Htlb0 Hpmp". iPureIntro. exact Hmode.
  Qed.

  Lemma bare_transform :
    forall (acc : MemoryAccessType mem_payload) (ea : mword 64) (σ : mstate),
      s_acc_ok acc ->
      register_lookup cur_privilege σ.(sregs) = Supervisor ->
      _get_Mstatus_SXL (register_lookup mstatus σ.(sregs)) = 'b"10" ->
      exec (effectivePrivilege acc (register_lookup mstatus σ.(sregs)) Supervisor) σ
        = Some (Supervisor, σ) ->
      exec (get_pmlen acc Supervisor) σ = Some (0, σ) ->
      ⊢ reg_interp σ.(sregs) -∗ bare_inv -∗
        ⌜ exec (transform_effective_address (Virtaddr ea) acc) σ = Some (Virtaddr ea, σ) ⌝.
  Proof.
    intros acc ea σ Hacc Hcp HSXL Heff Hpml.
    iIntros "Hri Hinv".
    iDestruct "Hinv" as (satp0 tlbv0) "(Hsatp & %Hmode & Htlb0 & Hpmp)".
    iDestruct (reg_valid_dq with "Hri Hsatp") as %Hsatpv.
    iPureIntro.
    exact (exec_transform_effective_address_mode acc Bare ea σ Hcp Heff Hpml
             (exec_translationMode_S_bare satp0 σ HSXL Hsatpv Hmode)).
  Qed.

  Lemma bare_tmode :
    forall (σ : mstate),
      _get_Mstatus_SXL (register_lookup mstatus σ.(sregs)) = 'b"10" ->
      ⊢ reg_interp σ.(sregs) -∗ bare_inv -∗
        ⌜ exists md, exec (translationMode Supervisor) σ = Some (md, σ) ⌝.
  Proof.
    intros σ HSXL.
    iIntros "Hri Hinv".
    iDestruct "Hinv" as (satp0 tlbv0) "(Hsatp & %Hmode & Htlb0 & Hpmp)".
    iDestruct (reg_valid_dq with "Hri Hsatp") as %Hsatpv.
    iPureIntro. exists Bare.
    exact (exec_translationMode_S_bare satp0 σ HSXL Hsatpv Hmode).
  Qed.

  (* Bare + a non-identity claim is UNSOUND (SRegime.v's header comment,
     [kadm_ident]'s), so the witness that would let [sr_absorb_wit] skip
     the identity premise must be UNSATISFIABLE here -- unsoundness shows
     up as an unpayable WITNESS, never an unpayable premise. *)
  Lemma bare_absorb_wit :
    forall acc va pa (ppn : mword 44) (pc : kperm) σ (E : coPset), s_acc_ok acc ->
      kperm_allows pc acc ->
      neq_vec (bits_of_virtaddr (Virtaddr va))
         (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
      zero_extend' 64 (concat_vec ppn
          (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub pagesize_bits 1) 0)) = pa ->
      register_lookup misa σ.(sregs) = MISA_C ->
      register_lookup menvcfg σ.(sregs) = MENVCFG_S ->
      register_lookup htif_tohost_base σ.(sregs) = None ->
      register_lookup cur_privilege σ.(sregs) = Supervisor ->
      _get_Mstatus_SXL (register_lookup mstatus σ.(sregs)) = 'b"10" ->
      exec (effectivePrivilege acc (register_lookup mstatus σ.(sregs)) Supervisor) σ
        = Some (Supervisor, σ) ->
      exec (is_shadow_stack_access acc) σ = Some (false, σ) ->
      pma_allows_all (register_lookup pma_regions σ.(sregs)) ->
      ↑kptN ⊆ E ->
      ⊢ (False : iProp Σ) -∗ kmap_at (svpn_of va) ppn pc -∗
        reg_interp σ.(sregs) -∗ gen_heap_interp σ.(mem) -∗ bare_inv ={E}=∗
        ∃ σ' : mstate,
          ⌜ exec (translateAddr (Virtaddr va) acc) σ
            = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), σ') ⌝ ∗
          ⌜ σ'.(mdev) = σ.(mdev) ⌝ ∗
          ⌜ (σ'.(sregs) = σ.(sregs) \/
             exists tv, σ'.(sregs) = register_set tlb tv σ.(sregs))%type ⌝ ∗
          ⌜ pmp_grant_facts σ' ⌝ ∗
          reg_interp σ'.(sregs) ∗ gen_heap_interp σ'.(mem) ∗ bare_inv.
  Proof.
    intros acc va pa ppn pc σ E Hacc Hallow Hcanon Hconcat Hmisa Hmenv Hhtif Hcp HSXL Heff Hss Hall HE.
    iIntros "H". iDestruct "H" as %[].
  Qed.

  Definition bare_regime : s_regime :=
    SRegime bare_inv kadm_ident (fun _ _ H => H) bare_absorb bare_transform
            bare_tmode (False%I) _ bare_absorb_wit.

End SRegimeDef.

(* ===================================================================== *)
(* §3 THE SHARED-KERNEL-TABLE INSTANCE (claude-notes/projects/            *)
(*    kpt-share.md).  [sr_inv := tlb_res_pt root_ppn] -- the per-hart     *)
(*    residue: this hart's satp/tlb/pmp cells plus a persistent SNAPSHOT   *)
(*    of the shared tree and the [kpt_inv] invariant holding it.  This is  *)
(*    the one regime whose absorb actually USES the mask.                 *)
(* ===================================================================== *)

Section SRegimeShared.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Lemma res_transform (root_ppn : mword 44) :
    forall (acc : MemoryAccessType mem_payload) (ea : mword 64) (σ : mstate),
      s_acc_ok acc ->
      register_lookup cur_privilege σ.(sregs) = Supervisor ->
      _get_Mstatus_SXL (register_lookup mstatus σ.(sregs)) = 'b"10" ->
      exec (effectivePrivilege acc (register_lookup mstatus σ.(sregs)) Supervisor) σ
        = Some (Supervisor, σ) ->
      exec (get_pmlen acc Supervisor) σ = Some (0, σ) ->
      ⊢ reg_interp σ.(sregs) -∗ tlb_res_pt root_ppn -∗
        ⌜ exec (transform_effective_address (Virtaddr ea) acc) σ = Some (Virtaddr ea, σ) ⌝.
  Proof.
    intros acc ea σ Hacc Hcp HSXL Heff Hpml.
    iIntros "Hri Hres".
    iDestruct (tlb_res_pt_open with "Hres") as (satp0 tlbvec)
      "(Hsatp & %Hmode & _ & _ & _)".
    iDestruct (reg_valid_dq with "Hri Hsatp") as %Hsatpv.
    iPureIntro.
    exact (exec_transform_effective_address_mode acc Sv39 ea σ Hcp Heff Hpml
             (exec_translationMode_S_sv39 satp0 σ HSXL Hsatpv Hmode)).
  Qed.

  Lemma res_absorb (root_ppn : mword 44) :
    forall acc va pa (ppn : mword 44) (pc : kperm) σ (E : coPset), s_acc_ok acc ->
      kperm_allows pc acc ->
      neq_vec (bits_of_virtaddr (Virtaddr va))
         (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
      zero_extend' 64 (concat_vec ppn
          (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub pagesize_bits 1) 0)) = pa ->
      register_lookup misa σ.(sregs) = MISA_C ->
      register_lookup menvcfg σ.(sregs) = MENVCFG_S ->
      register_lookup htif_tohost_base σ.(sregs) = None ->
      register_lookup cur_privilege σ.(sregs) = Supervisor ->
      _get_Mstatus_SXL (register_lookup mstatus σ.(sregs)) = 'b"10" ->
      exec (effectivePrivilege acc (register_lookup mstatus σ.(sregs)) Supervisor) σ
        = Some (Supervisor, σ) ->
      exec (is_shadow_stack_access acc) σ = Some (false, σ) ->
      pma_allows_all (register_lookup pma_regions σ.(sregs)) ->
      True ->
      ↑kptN ⊆ E ->
      ⊢ kmap_at (svpn_of va) ppn pc -∗
        reg_interp σ.(sregs) -∗ gen_heap_interp σ.(mem) -∗ tlb_res_pt root_ppn ={E}=∗
        ∃ σ' : mstate,
          ⌜ exec (translateAddr (Virtaddr va) acc) σ
            = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), σ') ⌝ ∗
          ⌜ σ'.(mdev) = σ.(mdev) ⌝ ∗
          ⌜ (σ'.(sregs) = σ.(sregs) \/
             exists tv, σ'.(sregs) = register_set tlb tv σ.(sregs))%type ⌝ ∗
          ⌜ pmp_grant_facts σ' ⌝ ∗
          reg_interp σ'.(sregs) ∗ gen_heap_interp σ'.(mem) ∗ tlb_res_pt root_ppn.
  Proof.
    intros acc va pa ppn pc σ E Hacc Hallow Hcanon Hconcat Hmisa Hmenv Hhtif Hcp HSXL Heff Hss Hall _ HE.
    iIntros "Hat Hri Hgh Hres".
    iMod (tlb_res_pt_translateAddr_at acc root_ppn va pa ppn pc σ E HE
            (fun a d mxr do_sum =>
               kperm_variant_check ppn pc acc a d mxr do_sum Hacc Hallow)
            Hcanon Hconcat Hmisa Hmenv Hhtif Hcp HSXL Heff Hss Hall
            with "Hat Hri Hgh Hres")
      as (σ') "(%Htr & %Hmdev & %Hsh & Hri & Hgh & Hres)".
    iDestruct (tlb_res_pt_grant_facts root_ppn σ' with "Hri Hres") as %Hpmp.
    iModIntro. iExists σ'. iFrame "Hri Hgh Hres". iPureIntro.
    unfold pmp_grant_facts. tauto.
  Qed.

  Lemma res_tmode (root_ppn : mword 44) :
    forall (σ : mstate),
      _get_Mstatus_SXL (register_lookup mstatus σ.(sregs)) = 'b"10" ->
      ⊢ reg_interp σ.(sregs) -∗ tlb_res_pt root_ppn -∗
        ⌜ exists md, exec (translationMode Supervisor) σ = Some (md, σ) ⌝.
  Proof.
    intros σ HSXL.
    iIntros "Hri Hres".
    iDestruct (tlb_res_pt_open with "Hres") as (satp0 tlbvec)
      "(Hsatp & %Hmode & _ & _ & _)".
    iDestruct (reg_valid_dq with "Hri Hsatp") as %Hsatpv.
    iPureIntro. exists Sv39.
    exact (exec_translationMode_S_sv39 satp0 σ HSXL Hsatpv Hmode).
  Qed.

  (* The Sv39 walk honors every claim ([sr_adm := fun _ _ => True]), so its
     witness costs nothing: [emp], and the proof is [res_absorb] with the
     dropped premise's argument supplied as [I] exactly as [res_absorb]
     already takes it. *)
  Lemma res_absorb_wit (root_ppn : mword 44) :
    forall acc va pa (ppn : mword 44) (pc : kperm) σ (E : coPset), s_acc_ok acc ->
      kperm_allows pc acc ->
      neq_vec (bits_of_virtaddr (Virtaddr va))
         (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
      zero_extend' 64 (concat_vec ppn
          (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub pagesize_bits 1) 0)) = pa ->
      register_lookup misa σ.(sregs) = MISA_C ->
      register_lookup menvcfg σ.(sregs) = MENVCFG_S ->
      register_lookup htif_tohost_base σ.(sregs) = None ->
      register_lookup cur_privilege σ.(sregs) = Supervisor ->
      _get_Mstatus_SXL (register_lookup mstatus σ.(sregs)) = 'b"10" ->
      exec (effectivePrivilege acc (register_lookup mstatus σ.(sregs)) Supervisor) σ
        = Some (Supervisor, σ) ->
      exec (is_shadow_stack_access acc) σ = Some (false, σ) ->
      pma_allows_all (register_lookup pma_regions σ.(sregs)) ->
      ↑kptN ⊆ E ->
      ⊢ emp -∗ kmap_at (svpn_of va) ppn pc -∗
        reg_interp σ.(sregs) -∗ gen_heap_interp σ.(mem) -∗ tlb_res_pt root_ppn ={E}=∗
        ∃ σ' : mstate,
          ⌜ exec (translateAddr (Virtaddr va) acc) σ
            = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), σ') ⌝ ∗
          ⌜ σ'.(mdev) = σ.(mdev) ⌝ ∗
          ⌜ (σ'.(sregs) = σ.(sregs) \/
             exists tv, σ'.(sregs) = register_set tlb tv σ.(sregs))%type ⌝ ∗
          ⌜ pmp_grant_facts σ' ⌝ ∗
          reg_interp σ'.(sregs) ∗ gen_heap_interp σ'.(mem) ∗ tlb_res_pt root_ppn.
  Proof.
    intros acc va pa ppn pc σ E Hacc Hallow Hcanon Hconcat Hmisa Hmenv Hhtif Hcp HSXL Heff Hss Hall HE.
    iIntros "_ Hat Hri Hgh Hres".
    iApply (res_absorb root_ppn acc va pa ppn pc σ E Hacc Hallow Hcanon Hconcat Hmisa Hmenv Hhtif Hcp HSXL Heff Hss Hall I HE
              with "Hat Hri Hgh Hres").
  Qed.

  Definition kpt_share_regime (root_ppn : mword 44) : s_regime :=
    SRegime (tlb_res_pt root_ppn) (fun _ _ => True) (fun _ _ _ => I)
            (res_absorb root_ppn) (res_transform root_ppn) (res_tmode root_ppn)
            (emp%I) _ (res_absorb_wit root_ppn).

  Lemma kpt_share_regime_inv (root_ppn : mword 44) :
    sr_inv (kpt_share_regime root_ppn) ⊣⊢ tlb_res_pt root_ppn.
  Proof. reflexivity. Qed.

End SRegimeShared.

(* ===================================================================== *)
(* §4 THE TIER-INDEXED ACCESS WITNESS (claude-notes/projects/             *)
(*    sp-migration.md, design §4 -- phase D).                             *)
(*                                                                        *)
(* A memory datum carries a TIER ([Ktier.ktier], via [RiscvPtsto.         *)
(* ktier_pin]) that is a lower bound on the translation generation of any *)
(* hart that may drive an access with it, and a leaf reconciles the       *)
(* datum's claim with the hardware in one of two ways:                    *)
(*                                                                        *)
(*   - at KT0 the datum's own PIN is the identity, so admissibility comes *)
(*     out of the datum ([sr_adm_id]) and the leaf needs NOTHING from its *)
(*     caller -- which is why the whole tree compiles at KT0 today;       *)
(*   - at KT1 there is no pin at all, so admissibility has to come from   *)
(*     the REGIME's all-claims witness [sr_kwit] ([sr_absorb_wit]), which *)
(*     the accessing hart must actually hold ([kpt_on cpu_id] for         *)
(*     [strans_regime]; unsatisfiable [False] for [bare_regime], which is *)
(*     exactly the soundness gate).                                       *)
(*                                                                        *)
(* [sr_ktier_wit R kt] is that "what a hart at tier [kt] must show" as a  *)
(* single tier-indexed proposition -- [emp] at KT0, [sr_kwit R] at KT1 -- *)
(* so ONE generic leaf rule takes it as a (persistent) hypothesis and     *)
(* both tiers are one lemma.  At the KT0 default the hypothesis is [emp], *)
(* so today's leaf statements are that rule's KT0/KT0 corollaries and no  *)
(* function proof sees the generalization.                               *)
(* ===================================================================== *)

Section SRegimeKtier.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  (* THE TIER-INDEXED ACCESS WITNESS the generic leaves take.  At KT0
     access rides the DATUM's own pin (the identity, discharged through
     [sr_adm_id]) and costs the caller nothing; at KT1 it rides the
     REGIME's all-claims witness [sr_kwit].  Persistent in both arms
     ([emp] trivially, KT1 by [sr_kwit_pers]), so a leaf may take it,
     keep it, and hand it on without threading a linear resource. *)
  Definition sr_ktier_wit (R : s_regime) (kt : ktier) : iProp Σ :=
    match kt with
    | KT0 => emp
    | KT1 => sr_kwit R
    end.

  Global Instance sr_ktier_wit_persistent R kt : Persistent (sr_ktier_wit R kt).
  Proof. destruct kt; [apply _ | exact (sr_kwit_pers R)]. Qed.

  (* the KT0 arm is free -- this is what makes every old leaf statement a
     literal corollary of its generic form (no premise appears). *)
  Lemma sr_ktier_wit_KT0 (R : s_regime) : ⊢ sr_ktier_wit R KT0.
  Proof. done. Qed.

  (* ...and the SHARED-KPT regime's witness is free at BOTH tiers, because
     [kpt_share_regime]'s [sr_kwit] is [emp]: a hart that reaches those
     leaves has the kernel table installed by construction ([tlb_res_pt] IS
     the regime's invariant), so there is nothing left to attest.  This is
     what lets the whole symbolic-block executor ([VcGenS]) be tier-generic
     without growing a resource premise -- kernelvec's frame slots are
     KSTACK words at KT1 and it drives them through exactly these rules. *)
  Lemma sr_ktier_wit_kpt_share (root_ppn : mword 44) (kt : ktier) :
    ⊢ sr_ktier_wit (kpt_share_regime root_ppn) kt.
  Proof. destruct kt; done. Qed.

  (* THE ONE ABSORPTION A TIER-INDEXED LEAF CALLS.  Its premise list is
     [sr_absorb]'s with the [sr_adm va ppn] conjunct replaced by the
     DATUM's pin [ktier_pin kt' ppn va] and the witness [sr_ktier_wit R
     kt] prepended to the resource chain -- i.e. exactly the two things a
     [↦ₘ[kt']] datum and a tier-[kt] hart respectively supply.  Both arms
     land on an existing field, so no leaf proof grows a case split:
       kt' = KT0 -- the pin IS [kadm_ident], fed to [sr_adm]/[sr_absorb];
       kt' = KT1 -- [KtierLe KT1 kt] forces kt = KT1, so the witness IS
                    [sr_kwit R] and [sr_absorb_wit] applies one-for-one. *)
  Lemma sr_absorb_ktier (R : s_regime) (kt kt' : ktier) `{Hle : !KtierLe kt' kt} :
    forall (acc : MemoryAccessType mem_payload) (va pa : mword 64)
        (ppn : mword 44) (pc : kperm) (σ : mstate) (E : coPset),
      s_acc_ok acc ->
      kperm_allows pc acc ->
      neq_vec (bits_of_virtaddr (Virtaddr va))
         (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
      zero_extend' 64 (concat_vec ppn
          (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub pagesize_bits 1) 0)) = pa ->
      register_lookup misa σ.(sregs) = MISA_C ->
      register_lookup menvcfg σ.(sregs) = MENVCFG_S ->
      register_lookup htif_tohost_base σ.(sregs) = None ->
      register_lookup cur_privilege σ.(sregs) = Supervisor ->
      _get_Mstatus_SXL (register_lookup mstatus σ.(sregs)) = 'b"10" ->
      exec (effectivePrivilege acc (register_lookup mstatus σ.(sregs)) Supervisor) σ
        = Some (Supervisor, σ) ->
      exec (is_shadow_stack_access acc) σ = Some (false, σ) ->
      pma_allows_all (register_lookup pma_regions σ.(sregs)) ->
      ktier_pin kt' ppn va ->
      ↑kptN ⊆ E ->
      ⊢ sr_ktier_wit R kt -∗ kmap_at (svpn_of va) ppn pc -∗
        reg_interp σ.(sregs) -∗ gen_heap_interp σ.(mem) -∗ sr_inv R ={E}=∗
        ∃ σ' : mstate,
          ⌜ exec (translateAddr (Virtaddr va) acc) σ
            = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), σ') ⌝ ∗
          ⌜ σ'.(mdev) = σ.(mdev) ⌝ ∗
          ⌜ (σ'.(sregs) = σ.(sregs) \/
             exists tv, σ'.(sregs) = register_set tlb tv σ.(sregs))%type ⌝ ∗
          ⌜ pmp_grant_facts σ' ⌝ ∗
          reg_interp σ'.(sregs) ∗ gen_heap_interp σ'.(mem) ∗ sr_inv R.
  Proof.
    intros acc va pa ppn pc σ E Hacc Hallow Hcanon Hconcat Hmisa Hmenv Hhtif Hcp
           HSXL Heff Hss Hall Hpin HE.
    destruct kt' as [|].
    - (* KT0: the pin IS [kadm_ident va ppn]; the witness is [emp]. *)
      iIntros "_ Hk Hri Hgh Hinv".
      iApply (sr_absorb R acc va pa ppn pc σ E Hacc Hallow Hcanon Hconcat Hmisa
                Hmenv Hhtif Hcp HSXL Heff Hss Hall (sr_adm_id R va ppn Hpin) HE
                with "Hk Hri Hgh Hinv").
    - (* KT1: [KtierLe KT1 kt] leaves only kt = KT1, so the witness IS
         [sr_kwit R] and there is nothing to reconcile per-address. *)
      destruct (ktier_le_cases _ _ Hle) as [Heq | [Hbad _]]; [| discriminate Hbad].
      rewrite -Heq.
      iIntros "Hw Hk Hri Hgh Hinv".
      iApply (sr_absorb_wit R acc va pa ppn pc σ E Hacc Hallow Hcanon Hconcat Hmisa
                Hmenv Hhtif Hcp HSXL Heff Hss Hall HE
                with "Hw Hk Hri Hgh Hinv").
  Qed.

End SRegimeKtier.

(* ===================================================================== *)
(* §5 THE SWP-LAYER REGIME (claude-notes/projects/main-cycle-port.md item  *)
(*    2b / 4).  [sr_absorb] opens the regime's invariant ONCE around a     *)
(*    whole [translateAddr]; at the [swp] layer a translation spans many   *)
(*    nodes and no fupd survives a node boundary, so the shared-table      *)
(*    instance must open [kptN] PER READ NODE.  The obligation the engine  *)
(*    hands a regime is therefore a [swp] fact, not a state-transformer    *)
(*    fupd -- and it needs the regime's NON-CELL RESIDUE at the file, which *)
(*    [sr_absorb] never did (its invariant carried the cells).             *)
(*                                                                        *)
(* IT IS A SEPARATE RECORD, NOT TWO MORE FIELDS OF [s_regime].  Growing    *)
(* [s_regime] changes [SRegime]'s arity and so breaks [IntrDefs]'s         *)
(* [strans_regime] -- a file this change may not touch.  [s_regime_swp R]  *)
(* is indexed by the regime it extends, so an instance is added beside an  *)
(* existing one and the two fold together in one edit once [IntrDefs] can  *)
(* move.                                                                  *)
(* ===================================================================== *)

Local Ltac str_cbn :=
  cbn beta iota zeta delta
    [Defs.bind Defs.bind0 Interface.iMon_bind Defs.liftR Defs.try_catch
     Defs.catch_early_return Defs.returnm returnM returnR Defs.returnR
     Defs.read_reg Defs.early_return Defs.throw Defs.and_boolM Defs.or_boolM
     andb orb negb not].

Local Ltac str_read :=
  rewrite hfrun_read;
  match goal with
  | |- context [ bool_decide ?P ] =>
      rewrite (bool_decide_eq_true_2 P ltac:(assumption))
  end.

(* THE BARE TRANSLATION AS A COMPUTED RUN.  [HartMFetch.hfrun_translateAddr_M]
   one privilege over: at Supervisor the mode is not the syntactic [Bare] of
   the Machine arm, so [translationMode] really runs -- [architecture] off
   mstatus's SXL and then the satp read -- which is the whole difference (two
   extra register nodes, both in the frame). *)
Lemma hfrun_translateAddr_S_bare (D Drw : gset register) (rs : regstate)
    (va : SailStdpp.Values.mword 64) (acc : MemoryAccessType mem_payload) :
  (mstatus : register) ∈ D ->
  (cur_privilege : register) ∈ D ->
  (satp : register) ∈ D ->
  register_lookup cur_privilege rs = Supervisor ->
  effectivePrivilege acc (register_lookup mstatus rs) Supervisor
    = returnM Supervisor ->
  is_shadow_stack_access acc = returnM false ->
  _get_Mstatus_SXL (register_lookup mstatus rs) = 'b"10" ->
  _get_Satp64_Mode (Mk_Satp64 (register_lookup satp rs)) = ('b"0000" : mword 4) ->
  hfrun 12 D Drw rs (translateAddr (Virtaddr va) acc)
  = Some (Values.Ok (Physaddr va, PBMT_PMA, init_ext_ptw), rs).
Proof.
  intros HD1 HD2 HD3 Hpriv Hep Hss HSXL Hmode.
  unfold translateAddr. str_cbn.
  str_read. str_cbn.
  str_read. rewrite Hpriv. str_cbn.
  rewrite Hep. str_cbn.
  unfold translationMode.
  replace (Instances.generic_eq Supervisor Machine) with false
    by (vm_compute; reflexivity).
  str_cbn.
  unfold architecture. cbn match. str_cbn.
  str_read. str_cbn.
  unfold architecture_bits_backwards. rewrite HSXL.
  replace (eq_vec ('b"10") ('b"01")) with false by (vm_compute; reflexivity).
  cbn match.
  replace (eq_vec ('b"10") ('b"10")) with true by (vm_compute; reflexivity).
  cbn match. str_cbn.
  change (xlen >=? 64) with true.
  unfold Defs.assert_exp'. cbn match. str_cbn.
  str_read. str_cbn.
  rewrite Hmode.
  replace (satpMode_of_bits RV64 ('b"0000" : mword 4)) with (Some Bare)
    by (vm_compute; reflexivity).
  cbn match. str_cbn.
  rewrite Hss. str_cbn.
  change (Instances.generic_eq Bare Bare) with true. str_cbn.
  cbn [bits_of_virtaddr]. rewrite zero_extend'_id.
  apply hfrun_ret.
Qed.

(* [SmodePte.pmp_config]'s pure half, named so the OPEN/CLOSE fields below
   can hand it across without unfolding the bundle. *)
Definition pmp_ent0_ok (pcfg : type_of_register pmpcfg_n)
    (paddr : type_of_register pmpaddr_n) : Prop :=
  pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec pcfg 0)) = TOR
  /\ zopz0zKzJ_u (zeros' 64) (vec_access_dec paddr 0) = false
  /\ eq_vec (_get_Pmpcfg_ent_X (vec_access_dec pcfg 0)) ('b"1") = true
  /\ eq_vec (_get_Pmpcfg_ent_W (vec_access_dec pcfg 0)) ('b"1") = true
  /\ eq_vec (_get_Pmpcfg_ent_R (vec_access_dec pcfg 0)) ('b"1") = true
  /\ (ram_base + ram_size <= uint (vec_access_dec paddr 0) * 4)%Z.

(* ---------------------------------------------------------------------- *)
(* THE FOUR PROBE PREMISES EVERY [sr_swp_translate] CALL TAKES, discharged  *)
(* once for the whole S-mode tier.  Both probes are TERM equations at an     *)
(* S-mode access -- [is_shadow_stack_access] because [s_acc_ok] names only   *)
(* Data / fetch payloads (the other payloads are [internal_error] arms, not  *)
(* [Ret]s), and [effectivePrivilege] because MPRV is clear, which the kernel *)
(* never changes.  A term equation settles the [exec] half and the [goodb]   *)
(* half at once, which is why none of the four needs a footprint argument.   *)
(* ---------------------------------------------------------------------- *)
Lemma s_acc_ssa_ret (acc : MemoryAccessType mem_payload) :
  s_acc_ok acc -> is_shadow_stack_access acc = returnM false.
Proof. intros [-> | [-> | [-> | (aq & rl & ->)]]]; reflexivity. Qed.

Lemma s_acc_ssa_exec (acc : MemoryAccessType mem_payload) (dst : mstate) :
  s_acc_ok acc -> exec (is_shadow_stack_access acc) dst = Some (false, dst).
Proof. intros H. rewrite (s_acc_ssa_ret acc H). apply exec_returnM. Qed.

Lemma s_acc_ssa_goodb (acc : MemoryAccessType mem_payload)
    (Db : register -> bool) (dst : mstate) :
  s_acc_ok acc -> goodb Db (is_shadow_stack_access acc) dst = true.
Proof. intros H. rewrite (s_acc_ssa_ret acc H). reflexivity. Qed.

Lemma s_eff_exec (acc : MemoryAccessType mem_payload) (m : mword 64)
    (p : Privilege) (dst : mstate) :
  eq_vec (_get_Mstatus_MPRV m) ('b"1") = false ->
  exec (effectivePrivilege acc m p) dst = Some (p, dst).
Proof. intros H. rewrite (effectivePrivilege_mprv0 acc m p H). apply exec_returnM. Qed.

Lemma s_eff_goodb (acc : MemoryAccessType mem_payload) (m : mword 64)
    (p : Privilege) (Db : register -> bool) (dst : mstate) :
  eq_vec (_get_Mstatus_MPRV m) ('b"1") = false ->
  goodb Db (effectivePrivilege acc m p) dst = true.
Proof. intros H. rewrite (effectivePrivilege_mprv0 acc m p H). reflexivity. Qed.

Section SRegimeSwp.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  (* THE SWP TRANSLATION FIELD, and the two things [sr_absorb] did not need.

     [sr_swp_res] -- the regime's NON-CELL RESIDUE at a file.  [sr_absorb]'s
     invariant carried the satp/tlb/pmp CELLS; at the swp layer those cells
     ride in the caller's FRAME, and what is left over is exactly what
     [WpSFrames.s_frames_intro] hands back untouched ([tlb_snap_ok tlbv] and
     [kpt_inv]).  It is taken at the pre-file and RETURNED AT THE LANDING
     FILE, because a TLB fill moves [tlbv] and only the walk can
     re-establish the snapshot there ([PtTree.tlb_ok_pt_fill]).  [True] for
     Bare.

     [sr_swp_side] -- the regime's own PURE side condition.  A regime-generic
     premise list cannot mention the translation mode (Sv39's walk needs
     [translationMode = Sv39], Bare's needs [= Bare]) nor the page table's
     leaf-test footprint certificates, so each regime names what it needs and
     the caller discharges it knowing which arm it is on.  This is the
     honest home for the facts [sr_absorb] hid inside its invariant. *)
  Record s_regime_swp (R : s_regime) := SRegimeSwp {
    sr_swp_res : regstate -> iProp Σ;
    sr_swp_side : MemoryAccessType mem_payload -> mword 64 -> mword 44 ->
                  kperm -> (register -> bool) -> gset register ->
                  gset register -> regstate -> mstate -> Prop;
    sr_swp_translate : forall (acc : MemoryAccessType mem_payload)
        (Drw Dro : gset register) (Df : register -> dfrac)
        (rs : regstate) (dst : mstate) (Db : register -> bool)
        (va pa : mword 64) (ppn : mword 44) (kp : kperm) (rr : option resv),
      Drw ## Dro ->
      s_acc_ok acc ->
      kperm_allows kp acc ->
      (mstatus : register) ∈ Drw ∪ Dro ->
      (cur_privilege : register) ∈ Drw ∪ Dro ->
      (satp : register) ∈ Drw ∪ Dro ->
      (tlb : register) ∈ Drw ->
      (pma_regions : register) ∈ Drw ∪ Dro ->
      (pmpcfg_n : register) ∈ Drw ∪ Dro ->
      (pmpaddr_n : register) ∈ Drw ∪ Dro ->
      (htif_tohost_base : register) ∈ Drw ∪ Dro ->
      (forall r : register, Db r = true -> r ∈ Drw ∪ Dro) ->
      (forall r : register, Db r = true ->
         register_lookup r rs = register_lookup r dst.(sregs)) ->
      (forall r : register, D_leafchk r = true -> r ∈ Drw ∪ Dro) ->
      (forall r : register, D_leafchk r = true ->
         register_lookup r rs = register_lookup r dst.(sregs)) ->
      register_lookup cur_privilege rs = Supervisor ->
      register_lookup htif_tohost_base rs = None ->
      register_lookup mstatus rs = register_lookup mstatus dst.(sregs) ->
      register_lookup misa dst.(sregs) = MISA_C ->
      register_lookup menvcfg dst.(sregs) = MENVCFG_S ->
      _get_Mstatus_SXL (register_lookup mstatus rs) = 'b"10" ->
      exec (effectivePrivilege acc (register_lookup mstatus dst.(sregs)) Supervisor) dst
        = Some (Supervisor, dst) ->
      goodb Db (effectivePrivilege acc (register_lookup mstatus dst.(sregs)) Supervisor)
        dst = true ->
      exec (is_shadow_stack_access acc) dst = Some (false, dst) ->
      goodb Db (is_shadow_stack_access acc) dst = true ->
      neq_vec (bits_of_virtaddr (Virtaddr va))
        (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va))
                            (Z.sub 39 1) 0)) = false ->
      zero_extend' 64 (concat_vec ppn
        (subrange_vec_dec (bits_of_virtaddr (Virtaddr va))
           (Z.sub pagesize_bits 1) 0)) = pa ->
      sr_adm R va ppn ->
      sr_swp_side acc va ppn kp Db Drw Dro rs dst ->
      ⊢ kmap_at (svpn_of va) ppn kp -∗ gen_cert -∗ resv_frag cpu_id rr -∗
        sr_swp_res rs -∗
        hreg_frame rs Drw -∗ hreg_frame_ro Df rs Dro -∗
        swp (translateAddr (Virtaddr va) acc)
          (fun r => ⌜r = Values.Ok (Physaddr pa, PBMT_PMA, init_ext_ptw)⌝ ∗
                    ∃ rsf : regstate,
                      ⌜ rsf = rs \/ exists tv, rsf = register_set tlb tv rs ⌝ ∗
                      hreg_frame rsf Drw ∗ hreg_frame_ro Df rsf Dro ∗
                      sr_swp_res rsf ∗ resv_any cpu_id);

    (* ---------------- THE BUNDLE FACE (added with the swp layer) --------
       [sr_inv R] is what every S-mode LEAF carries and what the wrappers
       must keep taking, but the swp engine needs the four cells the regime
       hides inside it -- satp, tlb, pmpcfg_n, pmpaddr_n -- IN THE FRAME
       ([HartSFrame.s_Drw] / [s_Dro]), because the walk reads and writes
       them.  So the record gains an OPEN and a CLOSE, plus the residue as
       a function of the two cell values it can depend on.

       WHY THE RESIDUE IS INDEXED BY (satp, tlb) AND NOT BY THE FILE.  A
       wrapper's file is a TOWER whose other components come out of
       [pc_is] / [hw_config] existentially, so "the residue at the tower"
       is not statable as a premise.  Every instance's residue reads the
       file only through those two cells ([sr_swp_res_agree] is the law
       that says so), and both are cells the bundle hands over, so the
       indexed form is exactly as strong and can be named.

       The two PURE side conditions travel the same way: [sr_swp_satp_ok]
       is the regime's own constraint on the satp VALUE (Bare's mode, the
       kernel table's mode/asid/root) and [pmp_ent0_ok] is entry 0's grant,
       which is [SmodePte.pmp_config]'s pure half. *)
    sr_swp_res_at : mword 64 -> type_of_register tlb -> iProp Σ;
    sr_swp_satp_ok : mword 64 -> Prop;
    sr_swp_res_agree : forall rs : regstate,
      sr_swp_res_at (register_lookup satp rs) (register_lookup tlb rs)
      ⊣⊢ sr_swp_res rs;
    sr_swp_open :
      sr_inv R -∗
      ∃ (satp0 : mword 64) (tlbv : type_of_register tlb)
        (pcfg : type_of_register pmpcfg_n)
        (paddr : type_of_register pmpaddr_n),
        ⌜ sr_swp_satp_ok satp0 ⌝ ∗ ⌜ pmp_ent0_ok pcfg paddr ⌝ ∗
        satp ↦ᵣ satp0 ∗ tlb ↦ᵣ tlbv ∗
        pmpcfg_n ↦ᵣ pcfg ∗ pmpaddr_n ↦ᵣ paddr ∗
        sr_swp_res_at satp0 tlbv;
    sr_swp_close : forall (satp0 : mword 64) (tlbv : type_of_register tlb)
        (pcfg : type_of_register pmpcfg_n)
        (paddr : type_of_register pmpaddr_n),
      sr_swp_satp_ok satp0 ->
      pmp_ent0_ok pcfg paddr ->
      ⊢ satp ↦ᵣ satp0 -∗ tlb ↦ᵣ tlbv -∗
        pmpcfg_n ↦ᵣ pcfg -∗ pmpaddr_n ↦ᵣ paddr -∗
        sr_swp_res_at satp0 tlbv -∗ sr_inv R;
  }.

  (* ---------------- the BARE instance ---------------- *)

  (* Bare's residue is nothing: satp is in the frame, and the ONE fact about
     it -- Mode = Bare -- is pure, so it rides in the side condition with the
     access's two monadic reductions. *)
  Definition bare_swp_side (acc : MemoryAccessType mem_payload)
      (va : mword 64) (ppn : mword 44) (kp : kperm) (Db : register -> bool)
      (Drw Dro : gset register) (rs : regstate) (dst : mstate) : Prop :=
    _get_Satp64_Mode (Mk_Satp64 (register_lookup satp rs)) = ('b"0000" : mword 4)
    /\ effectivePrivilege acc (register_lookup mstatus rs) Supervisor
       = returnM Supervisor
    /\ is_shadow_stack_access acc = returnM false.

  Lemma bare_swp_translate :
    forall (acc : MemoryAccessType mem_payload)
        (Drw Dro : gset register) (Df : register -> dfrac)
        (rs : regstate) (dst : mstate) (Db : register -> bool)
        (va pa : mword 64) (ppn : mword 44) (kp : kperm) (rr : option resv),
      Drw ## Dro ->
      s_acc_ok acc ->
      kperm_allows kp acc ->
      (mstatus : register) ∈ Drw ∪ Dro ->
      (cur_privilege : register) ∈ Drw ∪ Dro ->
      (satp : register) ∈ Drw ∪ Dro ->
      (tlb : register) ∈ Drw ->
      (pma_regions : register) ∈ Drw ∪ Dro ->
      (pmpcfg_n : register) ∈ Drw ∪ Dro ->
      (pmpaddr_n : register) ∈ Drw ∪ Dro ->
      (htif_tohost_base : register) ∈ Drw ∪ Dro ->
      (forall r : register, Db r = true -> r ∈ Drw ∪ Dro) ->
      (forall r : register, Db r = true ->
         register_lookup r rs = register_lookup r dst.(sregs)) ->
      (forall r : register, D_leafchk r = true -> r ∈ Drw ∪ Dro) ->
      (forall r : register, D_leafchk r = true ->
         register_lookup r rs = register_lookup r dst.(sregs)) ->
      register_lookup cur_privilege rs = Supervisor ->
      register_lookup htif_tohost_base rs = None ->
      register_lookup mstatus rs = register_lookup mstatus dst.(sregs) ->
      register_lookup misa dst.(sregs) = MISA_C ->
      register_lookup menvcfg dst.(sregs) = MENVCFG_S ->
      _get_Mstatus_SXL (register_lookup mstatus rs) = 'b"10" ->
      exec (effectivePrivilege acc (register_lookup mstatus dst.(sregs)) Supervisor) dst
        = Some (Supervisor, dst) ->
      goodb Db (effectivePrivilege acc (register_lookup mstatus dst.(sregs)) Supervisor)
        dst = true ->
      exec (is_shadow_stack_access acc) dst = Some (false, dst) ->
      goodb Db (is_shadow_stack_access acc) dst = true ->
      neq_vec (bits_of_virtaddr (Virtaddr va))
        (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va))
                            (Z.sub 39 1) 0)) = false ->
      zero_extend' 64 (concat_vec ppn
        (subrange_vec_dec (bits_of_virtaddr (Virtaddr va))
           (Z.sub pagesize_bits 1) 0)) = pa ->
      kadm_ident va ppn ->
      bare_swp_side acc va ppn kp Db Drw Dro rs dst ->
      ⊢ kmap_at (svpn_of va) ppn kp -∗ gen_cert -∗ resv_frag cpu_id rr -∗
        (True : iProp Σ) -∗
        hreg_frame rs Drw -∗ hreg_frame_ro Df rs Dro -∗
        swp (translateAddr (Virtaddr va) acc)
          (fun r => ⌜r = Values.Ok (Physaddr pa, PBMT_PMA, init_ext_ptw)⌝ ∗
                    ∃ rsf : regstate,
                      ⌜ rsf = rs \/ exists tv, rsf = register_set tlb tv rs ⌝ ∗
                      hreg_frame rsf Drw ∗ hreg_frame_ro Df rsf Dro ∗
                      (True : iProp Σ) ∗ resv_any cpu_id).
  Proof.
    intros acc Drw Dro Df rs dst Db va pa ppn kp rr Hdisj Hacc Hallow
      HDmst HDpriv HDsatp HWtlb HDpma HDcfg HDaddr HDhtif HDb Hag HDlc Haglc
      Hcp Hhtif Hmstag Hmisa Hmenv HSXL Heff Heffg Hss Hssg Hcanon Hconcat
      Hadm (Hsatpmode & Hep & Hssr).
    assert (Hpa : pa = va) by (rewrite <- Hconcat; exact Hadm).
    clear Hconcat. subst pa.
    iIntros "_ #Hcert Hfrag _ Hrw Hro".
    iDestruct (resv_any_intro with "Hfrag") as "Hany".
    iApply (swp_mono with "[] [Hrw Hro Hany]").
    2:{ iApply (swp_frame_l _ _ (resv_any cpu_id) with "Hany [Hrw Hro]").
        iApply (swp_hfrun 12 Drw Dro Df rs rs _ _ Hdisj
                  (hfrun_translateAddr_S_bare (Drw ∪ Dro) Drw rs va acc
                     HDmst HDpriv HDsatp Hcp Hep Hssr HSXL Hsatpmode)
                  with "Hcert Hrw Hro"). }
    iIntros (v) "(Hany & -> & Hrw & Hro)".
    iSplit.
    { iPureIntro. reflexivity. }
    iExists rs. iFrame "Hrw Hro Hany".
    iPureIntro. left. reflexivity.
  Qed.

  (* the BARE bundle face.  The residue is nothing, so open/close are just
     [bare_inv]'s own destructor/constructor plus [pmp_config]'s. *)
  Definition bare_satp_ok (satp0 : mword 64) : Prop :=
    _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"0000" : mword 4).

  Lemma bare_swp_res_agree (rs : regstate) :
    (True : iProp Σ) ⊣⊢ (True : iProp Σ).
  Proof. reflexivity. Qed.

  Lemma bare_swp_open :
    bare_inv -∗
    ∃ (satp0 : mword 64) (tlbv : type_of_register tlb)
      (pcfg : type_of_register pmpcfg_n) (paddr : type_of_register pmpaddr_n),
      ⌜ bare_satp_ok satp0 ⌝ ∗ ⌜ pmp_ent0_ok pcfg paddr ⌝ ∗
      satp ↦ᵣ satp0 ∗ tlb ↦ᵣ tlbv ∗
      pmpcfg_n ↦ᵣ pcfg ∗ pmpaddr_n ↦ᵣ paddr ∗ (True : iProp Σ).
  Proof.
    iIntros "H". iDestruct "H" as (satp0 tlbv) "(Hsatp & %Hmode & Htlb & Hpmp)".
    iDestruct "Hpmp" as (pcfg paddr)
      "(Hpcfg & Hpaddr & %HA & %Hord & %HX & %HW & %HR & %Hcov)".
    iExists satp0, tlbv, pcfg, paddr.
    iSplitR; [iPureIntro; exact Hmode |].
    iSplitR;
      [ iPureIntro; unfold pmp_ent0_ok; split_and!; assumption |].
    iFrame "Hsatp Htlb Hpcfg Hpaddr".
  Qed.

  Lemma bare_swp_close (satp0 : mword 64) (tlbv : type_of_register tlb)
      (pcfg : type_of_register pmpcfg_n) (paddr : type_of_register pmpaddr_n) :
    bare_satp_ok satp0 ->
    pmp_ent0_ok pcfg paddr ->
    ⊢ satp ↦ᵣ satp0 -∗ tlb ↦ᵣ tlbv -∗
      pmpcfg_n ↦ᵣ pcfg -∗ pmpaddr_n ↦ᵣ paddr -∗ (True : iProp Σ) -∗ bare_inv.
  Proof.
    intros Hmode (HA & Hord & HX & HW & HR & Hcov).
    iIntros "Hsatp Htlb Hpcfg Hpaddr _".
    rewrite /bare_inv. iExists satp0, tlbv. iFrame "Hsatp Htlb".
    iSplitR; [iPureIntro; exact Hmode |].
    iApply (pmp_config_intro (mword_of_int 0) pcfg paddr HA Hord HX HW HR Hcov
              with "Hpcfg Hpaddr").
  Qed.

  Definition bare_regime_swp : s_regime_swp bare_regime :=
    SRegimeSwp bare_regime (fun _ => True%I) bare_swp_side bare_swp_translate
      (fun _ _ => True%I) bare_satp_ok bare_swp_res_agree
      bare_swp_open bare_swp_close.

  (* ---------------- the SHARED-KERNEL-TABLE instance ---------------- *)

  (* the residue: the hart's TLB coherence at THIS file's vector, and the
     shared table's invariant (persistent, so it rides along for free) *)
  Definition kpt_swp_res (root_ppn : mword 44) (rs : regstate) : iProp Σ :=
    (tlb_snap_ok (register_lookup tlb rs) ∗ kpt_inv root_ppn)%I.

  (* the side condition: the satp facts that make this hart's frame an Sv39
     file rooted at [root_ppn], the mode reduction and its footprint
     certificate, and the PMP/PMA grant facts off the frame's own pmp cells.
     The two PTE tests' [goodb] certificates used to ride here as three more
     conjuncts; they are PROVED now ([KptGoodb]) and discharged inside
     [HartSKpt.swp_translate_kpt] itself. *)
  Definition kpt_swp_side (root_ppn : mword 44)
      (acc : MemoryAccessType mem_payload) (va : mword 64) (ppn : mword 44)
      (kp : kperm) (Db : register -> bool) (Drw Dro : gset register)
      (rs : regstate) (dst : mstate) : Prop :=
    _get_Satp64_Mode (Mk_Satp64 (register_lookup satp rs)) = ('b"1000" : mword 4)
    /\ zero_extend' 16 (satp_to_asid
         (autocast (T := mword) (register_lookup satp rs) : mword 64))
       = (mword_of_int 0 : mword 16)
    /\ autocast (T := mword) (satp_to_ppn
         (autocast (T := mword) (register_lookup satp rs) : mword 64)) = root_ppn
    /\ exec (translationMode Supervisor) dst = Some (Sv39, dst)
    /\ goodb Db (translationMode Supervisor) dst = true
    /\ pmpAddrMatchType_encdec_backwards
         (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n rs) 0)) = TOR
    /\ zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n rs) 0) = false
    /\ eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n rs) 0))
         ('b"1") = true
    /\ eq_vec (_get_Pmpcfg_ent_W (vec_access_dec (register_lookup pmpcfg_n rs) 0))
         ('b"1") = true
    /\ (ram_base + ram_size
        <= uint (vec_access_dec (register_lookup pmpaddr_n rs) 0) * 4)%Z
    /\ pma_allows_ram (register_lookup pma_regions rs).

  Lemma kpt_swp_translate (root_ppn : mword 44) :
    forall (acc : MemoryAccessType mem_payload)
        (Drw Dro : gset register) (Df : register -> dfrac)
        (rs : regstate) (dst : mstate) (Db : register -> bool)
        (va pa : mword 64) (ppn : mword 44) (kp : kperm) (rr : option resv),
      Drw ## Dro ->
      s_acc_ok acc ->
      kperm_allows kp acc ->
      (mstatus : register) ∈ Drw ∪ Dro ->
      (cur_privilege : register) ∈ Drw ∪ Dro ->
      (satp : register) ∈ Drw ∪ Dro ->
      (tlb : register) ∈ Drw ->
      (pma_regions : register) ∈ Drw ∪ Dro ->
      (pmpcfg_n : register) ∈ Drw ∪ Dro ->
      (pmpaddr_n : register) ∈ Drw ∪ Dro ->
      (htif_tohost_base : register) ∈ Drw ∪ Dro ->
      (forall r : register, Db r = true -> r ∈ Drw ∪ Dro) ->
      (forall r : register, Db r = true ->
         register_lookup r rs = register_lookup r dst.(sregs)) ->
      (forall r : register, D_leafchk r = true -> r ∈ Drw ∪ Dro) ->
      (forall r : register, D_leafchk r = true ->
         register_lookup r rs = register_lookup r dst.(sregs)) ->
      register_lookup cur_privilege rs = Supervisor ->
      register_lookup htif_tohost_base rs = None ->
      register_lookup mstatus rs = register_lookup mstatus dst.(sregs) ->
      register_lookup misa dst.(sregs) = MISA_C ->
      register_lookup menvcfg dst.(sregs) = MENVCFG_S ->
      _get_Mstatus_SXL (register_lookup mstatus rs) = 'b"10" ->
      exec (effectivePrivilege acc (register_lookup mstatus dst.(sregs)) Supervisor) dst
        = Some (Supervisor, dst) ->
      goodb Db (effectivePrivilege acc (register_lookup mstatus dst.(sregs)) Supervisor)
        dst = true ->
      exec (is_shadow_stack_access acc) dst = Some (false, dst) ->
      goodb Db (is_shadow_stack_access acc) dst = true ->
      neq_vec (bits_of_virtaddr (Virtaddr va))
        (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va))
                            (Z.sub 39 1) 0)) = false ->
      zero_extend' 64 (concat_vec ppn
        (subrange_vec_dec (bits_of_virtaddr (Virtaddr va))
           (Z.sub pagesize_bits 1) 0)) = pa ->
      True ->
      kpt_swp_side root_ppn acc va ppn kp Db Drw Dro rs dst ->
      ⊢ kmap_at (svpn_of va) ppn kp -∗ gen_cert -∗ resv_frag cpu_id rr -∗
        kpt_swp_res root_ppn rs -∗
        hreg_frame rs Drw -∗ hreg_frame_ro Df rs Dro -∗
        swp (translateAddr (Virtaddr va) acc)
          (fun r => ⌜r = Values.Ok (Physaddr pa, PBMT_PMA, init_ext_ptw)⌝ ∗
                    ∃ rsf : regstate,
                      ⌜ rsf = rs \/ exists tv, rsf = register_set tlb tv rs ⌝ ∗
                      hreg_frame rsf Drw ∗ hreg_frame_ro Df rsf Dro ∗
                      kpt_swp_res root_ppn rsf ∗ resv_any cpu_id).
  Proof.
    intros acc Drw Dro Df rs dst Db va pa ppn kp rr Hdisj Hacc Hallow
      HDmst HDpriv HDsatp HWtlb HDpma HDcfg HDaddr HDhtif HDb Hag HDlc Haglc
      Hcp Hhtif Hmstag Hmisa Hmenv HSXL Heff Heffg Hss Hssg Hcanon Hconcat _
      (Hmode & Hasid & Hppn & Htm & Htmg & HA & Hord & HR & HW & Hcov &
       Hpallow).
    assert (HPBMTE : eq_vec (_get_MEnvcfg_PBMTE (register_lookup menvcfg dst.(sregs)))
                       ('b"0") = true)
      by (rewrite Hmenv; vm_compute; reflexivity).
    assert (HADUE : eq_vec (_get_MEnvcfg_ADUE (register_lookup menvcfg dst.(sregs)))
                      ('b"1") = true)
      by (rewrite Hmenv; vm_compute; reflexivity).
    iIntros "#Hat #Hcert Hfrag [Hsnap #Hkinv] Hrw Hro".
    iApply (swp_mono with "[] [-]").
    2:{ iApply (swp_translate_kpt acc Drw Dro Df rs dst Db root_ppn va pa
                  (register_lookup satp rs)
                  (register_lookup menvcfg dst.(sregs)) ppn kp
                  (register_lookup tlb rs) (register_lookup pma_regions rs)
                  (register_lookup pmpcfg_n rs) (register_lookup pmpaddr_n rs) rr
                  Hdisj HDmst HDpriv HDsatp HWtlb HDpma HDcfg HDaddr HDhtif
                  HDb Hag HDlc Haglc Hcp eq_refl eq_refl Hhtif eq_refl eq_refl
                  eq_refl Hmstag Hmisa eq_refl HPBMTE HADUE
                  Heff Heffg Hss Hssg Htm Htmg Hppn Hasid Hcanon Hconcat
                  HA Hord HR HW Hcov Hpallow
                  (fun a d mxr do_sum =>
                     kperm_variant_check ppn kp acc a d mxr do_sum Hacc Hallow)
                  with "Hat Hkinv Hsnap Hcert Hfrag Hrw Hro"). }
    iIntros (v) "(-> & %rsf & %Hshape & Hrw & Hro & Hsnap & Hany)".
    iSplitR; [done |]. iExists rsf. iFrame "Hrw Hro Hany Hsnap Hkinv".
    iPureIntro. exact Hshape.
  Qed.

  (* the SHARED-KERNEL-TABLE bundle face.  [tlb_res_pt]'s destructor and
     constructor, with the satp facts moved into [sr_swp_satp_ok] (they are
     about the satp VALUE, not the residue) and the TLB coherence plus the
     table invariant left as the residue. *)
  Definition kpt_res_at (root_ppn : mword 44) (satp0 : mword 64)
      (tv : type_of_register tlb) : iProp Σ :=
    (tlb_snap_ok tv ∗ kpt_inv root_ppn)%I.

  Definition kpt_satp_ok (root_ppn : mword 44) (satp0 : mword 64) : Prop :=
    _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4)
    /\ zero_extend' 16 (satp_to_asid (autocast (T := mword) satp0 : mword 64))
       = (mword_of_int 0 : mword 16)
    /\ autocast (T := mword)
         (satp_to_ppn (autocast (T := mword) satp0 : mword 64)) = root_ppn.

  Lemma kpt_swp_res_agree (root_ppn : mword 44) (rs : regstate) :
    kpt_res_at root_ppn (register_lookup satp rs) (register_lookup tlb rs)
    ⊣⊢ kpt_swp_res root_ppn rs.
  Proof. reflexivity. Qed.

  Lemma kpt_swp_open (root_ppn : mword 44) :
    tlb_res_pt root_ppn -∗
    ∃ (satp0 : mword 64) (tlbv : type_of_register tlb)
      (pcfg : type_of_register pmpcfg_n) (paddr : type_of_register pmpaddr_n),
      ⌜ kpt_satp_ok root_ppn satp0 ⌝ ∗ ⌜ pmp_ent0_ok pcfg paddr ⌝ ∗
      satp ↦ᵣ satp0 ∗ tlb ↦ᵣ tlbv ∗
      pmpcfg_n ↦ᵣ pcfg ∗ pmpaddr_n ↦ᵣ paddr ∗
      kpt_res_at root_ppn satp0 tlbv.
  Proof.
    iIntros "H". iDestruct "H" as (satp0 tlbv)
      "(Hsatp & %Hmode & %Hasid & %Hppn & Htlb & Hsnap & Hpmp & #Hkpt)".
    iDestruct "Hpmp" as (pcfg paddr)
      "(Hpcfg & Hpaddr & %HA & %Hord & %HX & %HW & %HR & %Hcov)".
    iExists satp0, tlbv, pcfg, paddr.
    iSplitR;
      [ iPureIntro; unfold kpt_satp_ok; split_and!; assumption |].
    iSplitR;
      [ iPureIntro; unfold pmp_ent0_ok; split_and!; assumption |].
    rewrite /kpt_res_at. iFrame "Hsatp Htlb Hpcfg Hpaddr Hsnap Hkpt".
  Qed.

  Lemma kpt_swp_close (root_ppn : mword 44) (satp0 : mword 64)
      (tlbv : type_of_register tlb) (pcfg : type_of_register pmpcfg_n)
      (paddr : type_of_register pmpaddr_n) :
    kpt_satp_ok root_ppn satp0 ->
    pmp_ent0_ok pcfg paddr ->
    ⊢ satp ↦ᵣ satp0 -∗ tlb ↦ᵣ tlbv -∗
      pmpcfg_n ↦ᵣ pcfg -∗ pmpaddr_n ↦ᵣ paddr -∗
      kpt_res_at root_ppn satp0 tlbv -∗ tlb_res_pt root_ppn.
  Proof.
    intros (Hmode & Hasid & Hppn) (HA & Hord & HX & HW & HR & Hcov).
    iIntros "Hsatp Htlb Hpcfg Hpaddr [Hsnap #Hkpt]".
    rewrite /tlb_res_pt. iExists satp0, tlbv.
    iFrame "Hsatp Htlb Hsnap Hkpt".
    iSplitR; [iPureIntro; exact Hmode |].
    iSplitR; [iPureIntro; exact Hasid |].
    iSplitR; [iPureIntro; exact Hppn |].
    iApply (pmp_config_intro root_ppn pcfg paddr HA Hord HX HW HR Hcov
              with "Hpcfg Hpaddr").
  Qed.

  Definition kpt_share_regime_swp (root_ppn : mword 44)
      : s_regime_swp (kpt_share_regime root_ppn) :=
    SRegimeSwp (kpt_share_regime root_ppn) (kpt_swp_res root_ppn)
      (kpt_swp_side root_ppn) (kpt_swp_translate root_ppn)
      (kpt_res_at root_ppn) (kpt_satp_ok root_ppn)
      (kpt_swp_res_agree root_ppn) (kpt_swp_open root_ppn)
      (kpt_swp_close root_ppn).

  (* -------------------------------------------------------------------- *)
  (* THE SIDE CONDITIONS, INTRODUCED FROM THE PURE CONFIG FACTS A LEAF HAS. *)
  (*                                                                       *)
  (* [sr_swp_side] is where each regime names what its own arm needs, and   *)
  (* every leaf that drives a translation -- the fetch through              *)
  (* [SmodeCorePt.spt_tr_obl_of_regime], the loads/stores/AMOs directly --   *)
  (* has to discharge it.  What it actually has is the bundle's own pure     *)
  (* facts, and these two lemmas are exactly that conversion, so no leaf     *)
  (* ever unfolds a side condition.  Both are ACCESS-GENERIC: nothing below  *)
  (* mentions [acc] except Bare's shadow-stack conjunct, which [s_acc_ok]    *)
  (* settles for the fetch and for all three data accesses at once.          *)
  (*                                                                       *)
  (* The reference state [dst] enters only through the two facts             *)
  (* [translationMode] reads (mstatus.SXL and satp); at the swp layer the    *)
  (* caller takes [dst] to be THIS HART'S OWN FILE, and both are then         *)
  (* [reflexivity] against the tower.                                        *)
  (* -------------------------------------------------------------------- *)
  Lemma bare_swp_side_intro (acc : MemoryAccessType mem_payload)
      (va : mword 64) (ppn : mword 44) (kp : kperm) (Db : register -> bool)
      (Drw Dro : gset register) (rs : regstate) (dst : mstate) :
    s_acc_ok acc ->
    bare_satp_ok (register_lookup satp rs) ->
    eq_vec (_get_Mstatus_MPRV (register_lookup mstatus rs)) ('b"1") = false ->
    bare_swp_side acc va ppn kp Db Drw Dro rs dst.
  Proof.
    intros Hacc Hmode HMPRV. rewrite /bare_swp_side. split_and!.
    - exact Hmode.
    - exact (effectivePrivilege_mprv0 acc _ Supervisor HMPRV).
    - exact (s_acc_ssa_ret acc Hacc).
  Qed.

  Lemma kpt_swp_side_intro (root_ppn : mword 44)
      (acc : MemoryAccessType mem_payload) (va : mword 64) (ppn : mword 44)
      (kp : kperm) (Db : register -> bool) (Drw Dro : gset register)
      (rs : regstate) (dst : mstate) :
    kpt_satp_ok root_ppn (register_lookup satp rs) ->
    pmp_ent0_ok (register_lookup pmpcfg_n rs) (register_lookup pmpaddr_n rs) ->
    pma_allows_ram (register_lookup pma_regions rs) ->
    Db mstatus = true -> Db satp = true ->
    _get_Mstatus_SXL (register_lookup mstatus dst.(sregs)) = 'b"10" ->
    register_lookup satp dst.(sregs) = register_lookup satp rs ->
    kpt_swp_side root_ppn acc va ppn kp Db Drw Dro rs dst.
  Proof.
    intros (Hmode & Hasid & Hppn) (HA & Hord & HX & HW & HR & Hcov) Hpma
      HDm HDs HSXL Hsatp.
    rewrite /kpt_swp_side. split_and!.
    - exact Hmode.
    - exact Hasid.
    - exact Hppn.
    - exact (exec_translationMode_S_sv39 (register_lookup satp rs) dst
               HSXL Hsatp Hmode).
    - exact (goodb_translationMode_S_sv39 Db (register_lookup satp rs) dst
               HDm HDs HSXL Hsatp Hmode).
    - exact HA.
    - exact Hord.
    - exact HR.
    - exact HW.
    - exact Hcov.
    - exact Hpma.
  Qed.

End SRegimeSwp.
