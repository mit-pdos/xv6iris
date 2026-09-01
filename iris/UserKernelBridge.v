(* UserKernelBridge.v -- item (E) of the user-mode WP worklist: KERNEL
   INTEGRATION.

   This file bridges the postcondition of [wp_userret_pt] (UserretAllPt.v)
   -- the machine state the kernel's userret trampoline leaves once it has
   sret'd into User mode -- into the CONCRETE resume state the trap loop
   feeds to the per-process user-execution contract it holds
   ([UexecRet.uslot] / [uvb]; see claude-notes/projects/user-wp-slot.md).
   That is [userret_to_user_state_ptm]: a [u_regs] bundle at the post-sret
   state, [user_ptm_inv] at the NAMED lazy image, and [user_cfg].  It used
   to deliver the PACKED [user_inv C pt] instead; the packing now happens
   inside the generic slot's own proof (ProofUexecWp.v), because a verified
   program's WP needs the state concrete.  Its [user_pt_inv] twin
   [userret_to_user_state] and the trap-frame opener
   [user_trap_frame_open] went caller-less at milestone J's S5 (the loop
   opens [UserExec.user_trap_frame_atm] by unfolding) and were deleted at
   S6.

   THE OBSERVATION.  [wp_userret_pt]'s continuation already hands back
   EXACTLY [utlb_inv_pt uroot tfp um] -- the very same installed-table
   invariant [user_pt_inv] wraps -- together with a User-privilege machine
   whose mstatus is [sret_ms5 mstatus0].  So the bridge is a pure
   REPACKAGING: no translation move, no page-walk, no fupd.  What it needs
   beyond userret's guarantees are the CELLS userret never touched (they
   stay kernel-owned across the whole trampoline): the two remaining trap
   CSRs [scause]/[stval] (stale until the next trap writes them), the four
   config CSRs userret does not thread ([stvec]/[medeleg] and the
   [mstateen0]/[sstateen0] state-enable pins; [mip] is NOT among them --
   it has no loop-constant value, and the hart owns it inside
   [user_regs]'s [clock_res] rider, which arrives here as part of the
   [pc_is] userret hands back, see [UserExec.ucfg]), and the user data
   memory [umem_any] with its no-aliasing / access-classification
   facts.

   THE ONE PURE OBLIGATION is [user_mstatus_ok (sret_ms5 mstatus0)] -- the
   SXL=64 / MPRV=0 / MXR=0 pins survive the sret transform.  This is
   discharged from the pre-sret pins by the existing bit lemmas
   [sret_ms5_SXL]/[sret_ms5_MXR]/[sret_ms5_MPRV] (MstatusBits.v): sret
   clears MPRV (bit 17) and leaves SXL (bits 35:34) and MXR (bit 19)
   untouched.

   The [ucfg] record's own well-formedness proofs (stvec TV_Direct
   [uc_tvd], the mie&~mideleg=0 M-interrupt pin [uc_mm], the delegation of
   every user exception [uc_del]) ride along inside the abstract [C] the
   caller supplies -- they are established once when the boot config is
   fixed, and this bridge does not re-derive them. *)
From Stdlib Require Import ZArith.
From stdpp Require Import bitvector.definitions gmap.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvExtras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvFetchExec.
Require Import InstrBytes WpGpr RegFile.
Require Import MstatusBits.
Require Import UserFrame.
Require Import UptTree UserPtTree UserExec.
Require Import TsoCtx.
Local Open Scope Z_scope.
Import Defs.

Require Import UserFd.   (* [ufdG] -- the class a minted user slot needs *)
Section UserKernelBridge.
  Context `{!riscvGS Σ}.
  Context `{!ufdG Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.

  (* -------------------------------------------------------------------- *)
  (* The pure mstatus obligation, factored out: the User-execution mstatus *)
  (* pins survive the sret transform.                                      *)
  (* -------------------------------------------------------------------- *)
  Lemma user_mstatus_ok_sret_ms5 (ms0 : mword 64) :
    _get_Mstatus_SXL ms0 = 'b"10" ->
    eq_vec (_get_Mstatus_MXR ms0) ('b"0") = true ->
    eq_vec (_get_Mstatus_FS ms0) ('b"00") = true ->
    eq_vec (_get_Mstatus_VS ms0) ('b"00") = true ->
    eq_vec (_get_Mstatus_TVM ms0) ('b"1") = false ->
    eq_vec (_get_Mstatus_TSR ms0) ('b"1") = false ->
    (* the kernel-tier pins [user_mstatus_ok] now carries: XS/SD/MPP ride
       through the sret untouched, and SIE = 1 in user mode is SPIE = 1
       before it ([sret_ms5_SIE]) -- which is what prepare_return wrote
       and what the trap will copy back ([UserTrap.utrap_ms_SPIE]). *)
    _get_Mstatus_XS ms0 = extStatus_map_forwards Off ->
    _get_Mstatus_SD ms0 = ('b"0" : mword 1) ->
    eq_vec (_get_Mstatus_MPP ms0) ('b"10") = false ->
    _get_Mstatus_SPIE ms0 = ('b"1" : mword 1) ->
    user_mstatus_ok (sret_ms5 ms0).
  Proof.
    intros HSXL HMXR HFS HVS HTVM HTSR HXS HSD HMPP HSPIE.
    unfold user_mstatus_ok.
    split_and!.
    - rewrite sret_ms5_SXL. exact HSXL.
    - rewrite sret_ms5_MPRV. vm_compute. reflexivity.
    - rewrite sret_ms5_MXR. exact HMXR.
    - rewrite sret_ms5_FS. exact HFS.
    - rewrite sret_ms5_VS. exact HVS.
    - rewrite sret_ms5_TVM. exact HTVM.
    - rewrite sret_ms5_TSR. exact HTSR.
    - rewrite sret_ms5_XS. exact HXS.
    - rewrite sret_ms5_SD. exact HSD.
    - rewrite sret_ms5_MPP. exact HMPP.
    - rewrite sret_ms5_SIE HSPIE. vm_compute. reflexivity.
  Qed.

  (* -------------------------------------------------------------------- *)
  (* THE BRIDGE AT THE NAMED LAZY IMAGE (milestone J, stage S5).            *)
  (*                                                                        *)
  (* The deleted twin [userret_to_user_state] delivered                      *)
  (* [UserPtTree.user_pt_inv] -- the MAPPED bundle at an image it invented   *)
  (* out of [umem_any] -- which is what the GENERIC slot                     *)
  (* ([UexecWp.uexec_wp]) consumes.  [UexecRet.uvb]'s image conjunct is      *)
  (* [user_ptm_inv pt sz M], the LAZY sz-region view at a NAMED image: the   *)
  (* key's own, which the loop must hand on unchanged.  That one row is all  *)
  (* that ever differed between the two, so when the loop stopped calling    *)
  (* the mapped form the twin went with it (S6).                             *)
  (* -------------------------------------------------------------------- *)
  Lemma userret_to_user_state_ptm
      (C : ucfg) (pt : uptd) (sz : Z) (Mim : gmap Z (bv 8))
      (mstatus0 sepc0 sc_v stval_v mie_v mdv0 menvcfg0 senvcfg0 : mword 64)
      (stv medeleg_v : mword 64)
      (uroot tfp : mword 44) (um : gmap (mword 27) (mword 64))
      (mstateen0v : mword 64) (sstateen0v : mword 32)
      (mcounteren_v scounteren_v : mword 32)
      (mhpmcounter_v : type_of_register mhpmcounter)
      (g : regfile) :
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    eq_vec (_get_Mstatus_MXR mstatus0) ('b"0") = true ->
    eq_vec (_get_Mstatus_FS mstatus0) ('b"00") = true ->
    eq_vec (_get_Mstatus_VS mstatus0) ('b"00") = true ->
    eq_vec (_get_Mstatus_TVM mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_TSR mstatus0) ('b"1") = false ->
    _get_Mstatus_XS mstatus0 = extStatus_map_forwards Off ->
    _get_Mstatus_SD mstatus0 = ('b"0" : mword 1) ->
    eq_vec (_get_Mstatus_MPP mstatus0) ('b"10") = false ->
    _get_Mstatus_SPIE mstatus0 = ('b"1" : mword 1) ->
    uc_dqc C = DfracOwn 1 ->
    uc_stvec C = stv ->
    uc_mie C = mie_v ->
    uc_mideleg C = mdv0 ->
    uc_medeleg C = medeleg_v ->
    ud_root pt = uroot ->
    ud_tfp pt = tfp ->
    ud_um pt = um ->
    menvcfg0 = MENVCFG_S ->
    senvcfg0 = (mword_of_int 0 : mword 64) ->
    mstateen0v = (mword_of_int 0 : mword 64) ->
    sstateen0v = (mword_of_int 0 : mword 32) ->
    uva_pa_inj pt ->
    upt_acc_wf pt.(ud_um) ->
    hart_state ↦ᵣ HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ User -∗
    mstatus ↦ᵣ sret_ms5 mstatus0 -∗
    mie ↦ᵣ mie_v -∗
    mideleg ↦ᵣ mdv0 -∗
    menvcfg ↦ᵣ menvcfg0 -∗
    senvcfg ↦ᵣ□ senvcfg0 -∗
    sepc ↦ᵣ sepc0 -∗
    utlb_inv_pt uroot tfp um -∗
    pc_is (ret_pc sepc0) -∗
    gpr_file g -∗
    scause ↦ᵣ sc_v -∗
    stval ↦ᵣ stval_v -∗
    stvec ↦ᵣ stv -∗
    medeleg ↦ᵣ□ medeleg_v -∗
    mstateen0 ↦ᵣ□ mstateen0v -∗
    sstateen0 ↦ᵣ□ sstateen0v -∗
    (R_bitvector_32 mcounteren) ↦ᵣ□ mcounteren_v -∗
    (R_bitvector_32 scounteren) ↦ᵣ□ scounteren_v -∗
    mhpmcounter ↦ᵣ□ mhpmcounter_v -∗
    (* ---- the process's memory, NAMED, at the lazy sz-region view ---- *)
    umem_lazy pt sz Mim -∗
    ⌜user_mstatus_ok (sret_ms5 mstatus0)⌝ ∗
    u_regs (HART_ACTIVE tt) (sret_ms5 mstatus0) sc_v stval_v sepc0
           (ret_pc sepc0) (ret_pc sepc0) g ∗
    user_ptm_inv pt sz Mim ∗
    user_cfg C.
  Proof.
    intros HSXL HMXR HFS HVS HTVM HTSR HXS HSD HMPP HSPIE Hdqc Hstvec Hmie Hmdl Hmedl
      Hroot Htfp Hum Hmenv Hsenv Hmse Hsse Hinj Hacc.
    subst menvcfg0 senvcfg0 mstateen0v sstateen0v.
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hsenv Hsepc Hutlb Hpc Hgpr
             Hsc Hstval Hstvec Hmedl Hmse Hsse Hmcen Hscen Hhpm Hmem".
    iSplitR; [iPureIntro; exact (user_mstatus_ok_sret_ms5 mstatus0 HSXL HMXR HFS HVS HTVM HTSR HXS HSD HMPP HSPIE) |].
    iSplitL "Hhs Hpriv Hms Hsc Hstval Hsepc Hpc Hgpr".
    { rewrite u_regs_pc_is.
      iFrame "Hhs Hpriv Hms Hsc Hstval Hsepc Hpc Hgpr". }
    iSplitL "Hutlb Hmem".
    { (* user_ptm_inv, at the NAMED lazy image -- row by row *)
      rewrite /user_ptm_inv.
      rewrite Hroot Htfp Hum.
      iSplitL "Hutlb"; [iExact "Hutlb" |].
      iSplitL "Hmem"; [iExact "Hmem" |].
      rewrite Hum in Hacc.
      iPureIntro. split; [exact Hinj | exact Hacc]. }
    { unfold user_cfg.
      rewrite Hdqc Hstvec Hmie Hmdl Hmedl.
      iFrame "Hstvec Hmie Hmdl Hmedl Hmenv Hsenv Hmse Hsse".
      iSplitL "Hmcen Hscen".
      - iExists mcounteren_v, scounteren_v. iFrame "Hmcen Hscen".
      - iExists mhpmcounter_v. iFrame "Hhpm". }
  Qed.

End UserKernelBridge.
