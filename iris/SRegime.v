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
Require Import HartSTrans HartSKpt.
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
  Definition bare_inv : iProp Σ :=
    (∃ satp0 : mword 64,
       satp ↦ᵣ satp0 ∗
       ⌜ _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"0000" : mword 4) ⌝ ∗
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
    iDestruct "Hinv" as (satp0) "(Hsatp & %Hmode & Hpmp)".
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
    iExists satp0. iFrame "Hsatp Hpmp". iPureIntro. exact Hmode.
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
    iDestruct "Hinv" as (satp0) "(Hsatp & %Hmode & Hpmp)".
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
    iDestruct "Hinv" as (satp0) "(Hsatp & %Hmode & Hpmp)".
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

  Definition bare_regime_swp : s_regime_swp bare_regime :=
    SRegimeSwp bare_regime (fun _ => True%I) bare_swp_side bare_swp_translate.

  (* ---------------- the SHARED-KERNEL-TABLE instance ---------------- *)

  (* the residue: the hart's TLB coherence at THIS file's vector, and the
     shared table's invariant (persistent, so it rides along for free) *)
  Definition kpt_swp_res (root_ppn : mword 44) (rs : regstate) : iProp Σ :=
    (tlb_snap_ok (register_lookup tlb rs) ∗ kpt_inv root_ppn)%I.

  (* the side condition: the satp facts that make this hart's frame an Sv39
     file rooted at [root_ppn], the mode reduction and its footprint
     certificate, the PMP/PMA grant facts off the frame's own pmp cells, and
     the two PTE tests' footprint certificates (see HartSKpt's closing note
     for why the last three cannot be proved unconditionally) *)
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
    /\ pma_allows_ram (register_lookup pma_regions rs)
    /\ (forall w : mword 64,
          pte_canon w = pte_canon (mk_pte ppn (kperm_flags kp)) ->
          forall (Db' : register -> bool) s,
            goodb Db' (pte_is_invalid (Mk_PTE_Flags (subrange_vec_dec w 7 0))
                         (ext_bits_of_PTE w)) s = true)
    /\ (forall w : mword 64,
          pte_canon w = pte_canon (mk_pte ppn (kperm_flags kp)) ->
          forall (mxr do_sum : bool) (Db' : register -> bool) s,
            goodb Db' (check_PTE_permission acc Supervisor mxr do_sum
                         (Mk_PTE_Flags (subrange_vec_dec w 7 0))
                         (ext_bits_of_PTE w) tt) s = true)
    /\ (forall w : mword 64,
          pte_is_non_leaf (Mk_PTE_Flags (subrange_vec_dec w 7 0)) = true ->
          forall (Db' : register -> bool) s,
            goodb Db' (pte_is_invalid (Mk_PTE_Flags (subrange_vec_dec w 7 0))
                         (ext_bits_of_PTE w)) s = true).

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
       Hpallow & Higleaf & Hchkgleaf & Higptr).
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
                  Higleaf Hchkgleaf Higptr
                  with "Hat Hkinv Hsnap Hcert Hfrag Hrw Hro"). }
    iIntros (v) "(-> & %rsf & %Hshape & Hrw & Hro & Hsnap & Hany)".
    iSplitR; [done |]. iExists rsf. iFrame "Hrw Hro Hany Hsnap Hkinv".
    iPureIntro. exact Hshape.
  Qed.

  Definition kpt_share_regime_swp (root_ppn : mword 44)
      : s_regime_swp (kpt_share_regime root_ppn) :=
    SRegimeSwp (kpt_share_regime root_ppn) (kpt_swp_res root_ppn)
      (kpt_swp_side root_ppn) (kpt_swp_translate root_ppn).

End SRegimeSwp.
