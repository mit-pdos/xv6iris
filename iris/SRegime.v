(* SRegime.v -- the S-mode TRANSLATION REGIME interface: ONE record
   abstracting how an S-mode instruction's fetch/data translation is
   absorbed, so the engine + leaf layer serves Sv39 (paging on, the
   kernel table installed) and BARE (boot, satp=0) without duplication.

   [sr_absorb] is the TrampStepPt-Habs shape, access-generic over the
   four access classes, keyed on a kernel-mapping CLAIM [kmap_at (svpn_of
   va) ppn pc] + the class [pc] it must admit ([kperm_allows]), with the
   output pa = ppn ++ pageoff (rwx-kmap).  Every consumer presents the
   claim carried in its OWN resource (the fetch window's [↦ₓ□] bytes, a
   datum's [↦ₘ], a device vpn's static bundle claim), so there is no
   identity/region assumption at this altitude.  The PMP grant facts at
   the output state are exposed for the subsequent memory access.
   Instances:
     - [kpt_regime root_ppn]: sr_inv := tlb_inv_pt root_ppn; the fields
       are the existing absorption wrappers + the ktramp-style PMP
       peel-and-reseal.
     - [bare_regime]: satp pinned to Mode=Bare + pmp_config; translation
       short-circuits to the identity before touching the TLB
       ([exec_translateAddr_bare]), so absorption is trivial.           *)
From Stdlib Require Import ZArith Bool.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap ghost_map ghost_var.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec RiscvExtras.
Require Import SmodePte KptPt.
Require Import WpGpr WpMmodeLeafBase ExecCommon.
Require Import SmodeCore KptTree.
Require Import KMap.
Require Import KptGhost.   (* kptN: the shared kernel table's namespace, named in [sr_absorb]'s mask premise *)
Require Import KptShare.   (* the SHARED-table regime instance (§3) *)
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
(* §2 The regime record + the two instances.                              *)
(* ===================================================================== *)

(* the access classes the S-mode leaves use *)
Definition s_acc_ok (acc : MemoryAccessType mem_payload) : Prop :=
  acc = InstructionFetch tt \/ acc = Load Data \/ acc = Store Data \/
  acc = Atomic (AMOSWAP, Data, Data).

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

Section SRegimeDef.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.

  Record s_regime := SRegime {
    sr_inv : iProp Σ;
    (* THE re-keyed absorption (rwx-kmap): keyed on a kernel-mapping CLAIM
       [kmap_at (svpn_of va) ppn pc] + the access class it must admit,
       with the output pa = ppn ++ pageoff.  The claim is supplied by the
       consumer's OWN resource (fetch [↦ₓ□] window / datum [↦ₘ] / device
       static bundle), so no identity or region premise rides here. *)
    (* MASK-CARRYING (claude-notes/projects/kpt-share.md): the SHARED
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
        ⌜ exec (transform_effective_address (Virtaddr ea) acc) σ = Some (Virtaddr ea, σ) ⌝
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

  Lemma tlb_inv_pt_grant_facts (root_ppn : mword 44) (σ : mstate) :
    reg_interp σ.(sregs) -∗ tlb_inv_pt root_ppn -∗ ⌜pmp_grant_facts σ⌝.
  Proof.
    iIntros "Hri Hinv".
    iDestruct (tlb_inv_pt_open with "Hinv") as (satp0 tlbvec t M)
      "(Hsatp & _ & _ & _ & Htlb & _ & _ & _ & Ht & Hpmp)".
    iApply (pmp_config_grant_facts with "Hri Hpmp").
  Qed.

  (* ------------------------------------------------------------------- *)
  (* The Sv39-kernel instance.                                            *)
  (* ------------------------------------------------------------------- *)
  (* SINGLE-PATH (rwx-kmap): the claim + [kperm_variant_check] dispatch
     replaces the old four-way region case bash. *)
  Lemma kpt_absorb (root_ppn : mword 44) :
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
      ⊢ kmap_at (svpn_of va) ppn pc -∗
        reg_interp σ.(sregs) -∗ gen_heap_interp σ.(mem) -∗ tlb_inv_pt root_ppn ={E}=∗
        ∃ σ' : mstate,
          ⌜ exec (translateAddr (Virtaddr va) acc) σ
            = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), σ') ⌝ ∗
          ⌜ σ'.(mdev) = σ.(mdev) ⌝ ∗
          ⌜ (σ'.(sregs) = σ.(sregs) \/
             exists tv, σ'.(sregs) = register_set tlb tv σ.(sregs))%type ⌝ ∗
          ⌜ pmp_grant_facts σ' ⌝ ∗
          reg_interp σ'.(sregs) ∗ gen_heap_interp σ'.(mem) ∗ tlb_inv_pt root_ppn.
  Proof.
    intros acc va pa ppn pc σ E Hacc Hallow Hcanon Hconcat Hmisa Hmenv Hhtif Hcp HSXL Heff Hss Hall HE.
    iIntros "Hat Hri Hgh Hinv".
    iAssert (|==> ∃ σ' : mstate,
      ⌜ exec (translateAddr (Virtaddr va) acc) σ
        = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), σ') ⌝ ∗
      ⌜ σ'.(mdev) = σ.(mdev) ⌝ ∗
      ⌜ (σ'.(sregs) = σ.(sregs) \/
         exists tv, σ'.(sregs) = register_set tlb tv σ.(sregs))%type ⌝ ∗
      reg_interp σ'.(sregs) ∗ gen_heap_interp σ'.(mem) ∗ tlb_inv_pt root_ppn)%I
      with "[Hat Hri Hgh Hinv]" as ">H".
    { iApply (tlb_inv_pt_translateAddr_at acc root_ppn va pa ppn pc σ
                (fun a d mxr do_sum =>
                   kperm_variant_check ppn pc acc a d mxr do_sum Hacc Hallow)
                Hcanon Hconcat Hmisa Hmenv Hhtif Hcp HSXL Heff Hss Hall
                with "Hat Hri Hgh Hinv"). }
    iDestruct "H" as (σ') "(%Htr & %Hmdev & %Hsh & Hri & Hgh & Hinv)".
    iDestruct (tlb_inv_pt_grant_facts root_ppn σ' with "Hri Hinv") as %Hpmp.
    iModIntro. iExists σ'. iFrame "Hri Hgh Hinv". iPureIntro. tauto.
  Qed.

  Lemma kpt_transform (root_ppn : mword 44) :
    forall (acc : MemoryAccessType mem_payload) (ea : mword 64) (σ : mstate),
      s_acc_ok acc ->
      register_lookup cur_privilege σ.(sregs) = Supervisor ->
      _get_Mstatus_SXL (register_lookup mstatus σ.(sregs)) = 'b"10" ->
      exec (effectivePrivilege acc (register_lookup mstatus σ.(sregs)) Supervisor) σ
        = Some (Supervisor, σ) ->
      exec (get_pmlen acc Supervisor) σ = Some (0, σ) ->
      ⊢ reg_interp σ.(sregs) -∗ tlb_inv_pt root_ppn -∗
        ⌜ exec (transform_effective_address (Virtaddr ea) acc) σ = Some (Virtaddr ea, σ) ⌝.
  Proof.
    intros acc ea σ Hacc Hcp HSXL Heff Hpml.
    iIntros "Hri Hinv".
    iDestruct (tlb_inv_pt_open with "Hinv") as (satp0 tlbvec t M)
      "(Hsatp & %Hmode & %Hasid & %Hppn & _)".
    iDestruct (reg_valid_dq with "Hri Hsatp") as %Hsatpv.
    iPureIntro.
    exact (exec_transform_effective_address_mode acc Sv39 ea σ Hcp Heff Hpml
             (exec_translationMode_S_sv39 satp0 σ HSXL Hsatpv Hmode)).
  Qed.

  Definition kpt_regime (root_ppn : mword 44) : s_regime :=
    SRegime (tlb_inv_pt root_ppn) (kpt_absorb root_ppn) (kpt_transform root_ppn).

  (* ------------------------------------------------------------------- *)
  (* The BARE instance (boot: satp Mode = Bare, translation = identity).   *)
  (* ------------------------------------------------------------------- *)
  (* The Bare arm carries the auth over EXACTLY the static map (rwx-kmap):
     any claim honored under Bare is therefore a static identity entry
     ([kmap_at_M0_static]), and once a dynamic (kstack) fragment has been
     persisted this arm can never be re-established — Bare→KPT one-way. *)
  Definition bare_inv : iProp Σ :=
    (∃ satp0 : mword 64,
       satp ↦ᵣ satp0 ∗
       ⌜ _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"0000" : mword 4) ⌝ ∗
       pmp_config (mword_of_int 0) ∗
       kmap_auth kmap_M0)%I.

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
    intros acc va pa ppn pc σ E Hacc Hallow Hcanon Hconcat Hmisa Hmenv Hhtif Hcp HSXL Heff Hss Hall HE.
    iIntros "Hat Hri Hgh Hinv".
    iDestruct "Hinv" as (satp0) "(Hsatp & %Hmode & Hpmp & HM)".
    (* honoring: against the exact static auth, the claim is a static
       identity entry -- so the caller's pa is va itself *)
    iDestruct (kmap_at_M0_static with "HM Hat") as %[Hcls ->].
    assert (Hpa : pa = va).
    { rewrite <- Hconcat. exact (static_ident_4k va pc Hcls Hcanon). }
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
    iExists satp0. iFrame "Hsatp Hpmp HM". iPureIntro. exact Hmode.
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
    iDestruct "Hinv" as (satp0) "(Hsatp & %Hmode & Hpmp & HM)".
    iDestruct (reg_valid_dq with "Hri Hsatp") as %Hsatpv.
    iPureIntro.
    exact (exec_transform_effective_address_mode acc Bare ea σ Hcp Heff Hpml
             (exec_translationMode_S_bare satp0 σ HSXL Hsatpv Hmode)).
  Qed.

  Definition bare_regime : s_regime :=
    SRegime bare_inv bare_absorb bare_transform.

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
  Context `{!kptG Σ}.
  Context `{CID : CpuId}.

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
    intros acc va pa ppn pc σ E Hacc Hallow Hcanon Hconcat Hmisa Hmenv Hhtif Hcp HSXL Heff Hss Hall HE.
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

  Definition kpt_share_regime (root_ppn : mword 44) : s_regime :=
    SRegime (tlb_res_pt root_ppn) (res_absorb root_ppn) (res_transform root_ppn).

  Lemma kpt_share_regime_inv (root_ppn : mword 44) :
    sr_inv (kpt_share_regime root_ppn) ⊣⊢ tlb_res_pt root_ppn.
  Proof. reflexivity. Qed.

End SRegimeShared.
