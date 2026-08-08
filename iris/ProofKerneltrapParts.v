(* ProofKerneltrapParts.v -- kerneltrap()'s shared blocks.

   ONE block, and it is the whole reason this file exists: gcc put
   kerneltrap's epilogue at +0x36, in the MIDDLE of the function, on the
   fall-through of the timer test.  Three paths reach it -- the non-timer
   fall-through at +0x36, the "no current proc" [c.beqz] at +0x8a, and the
   [c.j] after [yield] at +0x90 -- so it is proved ONCE over an arbitrary
   arrival map and applied three times.  Same shape as [ProofClockintr]'s
   [wp_ci_tail] and [ProofDevintr]'s [di_epi].

   WHAT THE EPILOGUE ACTUALLY DOES is restore the trap state:

     +0x36  csrw sepc,s2      the epc saved at entry
     +0x3a  csrw sstatus,s1   the sstatus saved at entry
     +0x3e..+0x46             reload ra / s0 / s1 / s2 / s3
     +0x48  c.addi16sp sp,48  pop the 6-slot frame
     +0x4a  c.jr ra

   THE POSTCONDITION'S THREE mstatus FACTS ARE RE-DERIVED AT THE END, NOT
   CARRIED.  [wp_csrw_sstatus_s_sconf] hands back [sie_cap_gpr_at msf], but
   the five loads and the sp pop all go through the ordinary funnel, whose
   [exists ms] loses [msf] again -- so the [_at] flavour cannot be threaded
   across them and is closed immediately.  What survives is the [sret_bits]
   mirror the write re-tied: at the [c.jr] the bundle is re-opened at some
   [ms_x] and [sconf_at_sret] recovers SPP = 1 and SPIE = 1 there, while
   [sie_arm_half_agree] gives SIE = 0 off the [b = false] index.  This is why
   [SpecKerneltrap]'s postcondition states those bits ABSOLUTELY rather than
   relative to an entry mstatus: an absolute fact is re-derivable after any
   number of round-trips, a relative one is not.                            *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExtras.
Require Import InstrBytes WpMmodeLeafBase.
Require Import RegFile.
Require Import SmodeCore.
Require Import WpGprCsrwCommon WpGprCsrwA.
Require Import StackOwn CalleeSaved KernelText.
Require Import WpLock.
Require Import FdSlots.
Require Import ProcGeom CpuOwn.
Require Import IntrDefs.
Require Import HartTp WpNext.
Require Import VcGen KernelRvcDecode.
Require Import WpSconfAlu WpSconfMem WpSconfCtl WpSconfBtype WpSconfCsr.
Require Import WpSmodeIntr.
Require Import CodeKerneltrap.
Require Import SpecKerneltrap.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Import Defs.

Local Open Scope Z_scope.
Set Printing Depth 40.

Section ProofKerneltrapParts.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.
  Context {p : mword 64}.

  Notation ra_idx := (mword_of_int 1 : mword 5).
  Notation s0_idx := (mword_of_int 8 : mword 5).
  Notation s1_idx := (mword_of_int 9 : mword 5).
  Notation s2_idx := (mword_of_int 18 : mword 5).
  Notation s3_idx := (mword_of_int 19 : mword 5).

  Local Ltac pcw := apply bv_eq; vm_compute; reflexivity.

  (* "every callee-saved register kerneltrap does not itself restore is still
     the caller's".  sp / s0 / s1 / s2 / s3 are the frame's and are put back
     by the epilogue, so they are excluded here and supplied separately. *)
  Definition kt_thr (m0 M : regfile) : Prop :=
    forall r : mword 5, is_cs_idx r = true ->
      r <> csp_rs1 -> r <> s0_idx -> r <> s1_idx -> r <> s2_idx -> r <> s3_idx ->
      M !!! Regidx r = m0 !!! Regidx r.

  Lemma kt_cs_of (m0 mf : regfile) :
    mf !!! Regidx csp_rs1 = m0 !!! Regidx csp_rs1 ->
    mf !!! Regidx s0_idx = m0 !!! Regidx s0_idx ->
    mf !!! Regidx s1_idx = m0 !!! Regidx s1_idx ->
    mf !!! Regidx s2_idx = m0 !!! Regidx s2_idx ->
    mf !!! Regidx s3_idx = m0 !!! Regidx s3_idx ->
    kt_thr m0 mf ->
    callee_saved m0 mf.
  Proof.
    intros Hsp Hs0 Hs1 Hs2 Hs3 Hthr. unfold callee_saved.
    split_and!;
      first [ exact Hsp | exact Hs0 | exact Hs1 | exact Hs2 | exact Hs3
            | apply Hthr; solve [ vm_compute; reflexivity | vm_compute; discriminate ] ].
  Qed.

  (* ================================================================== *)
  (* THE TWO BRANCH OBLIGATIONS -- what makes the panic arms dead.        *)
  (*                                                                     *)
  (* [andi a5,s1,256] tests SPP (bit 8) of the SAVED sstatus, and         *)
  (* [c.andi a5,a5,2] tests SIE (bit 1) of a FRESH read.  The second is   *)
  (* [ProofPushOff.pop_sstatus_clear_neq] already; the first is its dual  *)
  (* and lives here, proved the same way as [WpGprCsrwC.sie_bit].         *)
  (* ================================================================== *)

  Lemma kt_spp_bit (w : mword 64) :
    _get_Sstatus_SPP w = ('b"1" : mword 1) -> Z.testbit (bv_unsigned w) 8 = true.
  Proof.
    intro HS.
    apply (f_equal bv_unsigned) in HS.
    unfold _get_Sstatus_SPP, subrange_vec_dec in HS.
    rewrite autocast_refl in HS.
    unfold to_word_idx, to_word, get_word in HS.
    rewrite MachineWord.MachineWord.cast_idx_refl in HS.
    unfold MachineWord.MachineWord.slice in HS.
    rewrite bv_extract_unsigned in HS.
    change (bv_unsigned ('b"1" : mword 1)) with 1 in HS.
    apply (f_equal (fun z => Z.testbit z 0)) in HS.
    change (Z.testbit 1 0) with true in HS.
    rewrite <- HS.
    unfold bv_wrap, bv_modulus.
    rewrite (Z.mod_pow2_bits_low _ (Z.of_N (MachineWord.MachineWord.Z_idx (8 - 8 + 1))));
      [| vm_compute; reflexivity].
    rewrite Z.shiftr_spec; [| lia]. reflexivity.
  Qed.

  (* SPP = 1 in the saved sstatus makes [andi a5,s1,256] NONZERO, so the
     "not from supervisor mode" [c.beqz] falls through. *)
  Lemma kt_spp_set_neq (ms : mword 64) :
    _get_Mstatus_SPP ms = ('b"1" : mword 1) ->
    eq_vec (and_vec (sstatus_read ms)
              (sign_extend' 64 (mword_of_int 256 : mword 12))) zero_reg = false.
  Proof.
    intro HSPP.
    assert (Hb8 : Z.testbit (bv_unsigned (sstatus_read ms)) 8 = true).
    { apply kt_spp_bit. unfold sstatus_read. rewrite WpGprCsrwC.subrange_full.
      rewrite WpGprCsrwC.sSPP_lower. exact HSPP. }
    assert (Hmask : bv_unsigned (sign_extend' 64 (mword_of_int 256 : mword 12) : mword 64) = 256)
      by (vm_compute; reflexivity).
    apply not_true_iff_false. intro Heq.
    apply eq_vec_true_iff in Heq.
    apply (f_equal bv_unsigned) in Heq.
    rewrite WpGprCsrwC.and_vec_unsigned Hmask in Heq.
    change (bv_unsigned (zero_reg : mword 64)) with 0 in Heq.
    apply (f_equal (fun z => Z.testbit z 8)) in Heq.
    rewrite Z.land_spec Z.bits_0 Hb8 in Heq.
    change (Z.testbit 256 8) with true in Heq.
    discriminate Heq.
  Qed.

  (* ================================================================== *)
  (* THE COMMON EPILOGUE (kerneltrap+0x36 .. +0x4a).                     *)
  (* ================================================================== *)
  Lemma kt_epi (Φ : mval -> iProp Σ)
      (m0 M : regfile) (sp0 ra0 s00 s10 s20 s30 vgap : mword 64)
      (ep epold : mword 64) (ms0 : mword 64)
      (k lvl : nat) (C : iProp Σ) (va vb : mword 1) :
    m0 !!! Regidx csp_rs1 = sp0 ->
    m0 !!! Regidx ra_idx = ra0 ->
    m0 !!! Regidx s0_idx = s00 ->
    m0 !!! Regidx s1_idx = s10 ->
    m0 !!! Regidx s2_idx = s20 ->
    m0 !!! Regidx s3_idx = s30 ->
    M !!! Regidx csp_rs1 = pa_stk sp0 6 ->
    (* the two words the prologue stashed, still in their registers *)
    M !!! Regidx s2_idx = ep ->
    M !!! Regidx s1_idx = sstatus_read ms0 ->
    (* the saved epc is instruction-aligned, so the restore lands verbatim *)
    ret_pc ep = ep ->
    (* what the saved sstatus says: a well-formed kernel mstatus, taken from
       S-mode with interrupts enabled, and SIE cleared by the trap *)
    sconf_ms_facts ms0 ->
    _get_Mstatus_SIE ms0 = ('b"0" : mword 1) ->
    _get_Mstatus_SPP ms0 = ('b"1" : mword 1) ->
    _get_Mstatus_SPIE ms0 = ('b"1" : mword 1) ->
    kt_thr m0 M ->
    sie_cap_gpr M k false p -∗
    sret_bits va vb -∗
    cpu_own lvl false p C false -∗
    kernel_text -∗
    pc_is (mword_of_int (KernelSyms.kerneltrap + 0x36) : mword 64) -∗
    sepc ↦ᵣ epold -∗
    pa_stk sp0 1 ↦₈ ra0 -∗
    pa_stk sp0 2 ↦₈ s00 -∗
    pa_stk sp0 3 ↦₈ s10 -∗
    pa_stk sp0 4 ↦₈ s20 -∗
    pa_stk sp0 5 ↦₈ s30 -∗
    pa_stk sp0 6 ↦₈ vgap -∗
    ( ∀ (mf : regfile) (ms_f : mword 64),
        ⌜ callee_saved m0 mf ⌝ -∗
        ⌜ _get_Mstatus_SPP  ms_f = ('b"1" : mword 1) ⌝ -∗
        ⌜ _get_Mstatus_SPIE ms_f = ('b"1" : mword 1) ⌝ -∗
        ⌜ _get_Mstatus_SIE  ms_f = ('b"0" : mword 1) ⌝ -∗
        sie_cap_gpr_at ms_f mf (k + 6) false p -∗
        sret_bits ('b"1" : mword 1) ('b"1" : mword 1) -∗
        cpu_own lvl false p C false -∗
        sepc ↦ᵣ ep -∗
        pc_is (ret_pc ra0) -∗
        WP (Loop : expr riscv_lang) {{ Φ }} ) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros Hm0sp Hm0ra Hm0s0 Hm0s1 Hm0s2 Hm0s3 HMsp HMs2 HMs1
           Hepal Hms0f Hsie0 Hspp0 Hspie0 Hthr.
    iIntros "Hcg Hmir Hcpu #Htext Hpc Hsepc Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hcont".
    (* the five frame addresses, as offsets off the pushed sp: slot j sits at
       [sp + 8*(6-j)], so ra/s0/s1/s2/s3 are uimm 5/4/3/2/1. *)
    Local Ltac ktpa HMsp :=
      rewrite HMsp; unfold pa_stk, add_vec_int; rewrite add_vec_off2;
      f_equal; try (apply bv_eq; vm_compute; reflexivity).
    assert (Hpa1 : add_vec (M !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000"))) = pa_stk sp0 1)
      by ktpa HMsp.
    assert (Hpa2 : add_vec (M !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000"))) = pa_stk sp0 2)
      by ktpa HMsp.
    assert (Hpa3 : add_vec (M !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000"))) = pa_stk sp0 3)
      by ktpa HMsp.
    assert (Hpa4 : add_vec (M !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000"))) = pa_stk sp0 4)
      by ktpa HMsp.
    assert (Hpa5 : add_vec (M !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) = pa_stk sp0 5)
      by ktpa HMsp.
    (* ---- +0x36: csrw sepc,s2 -- restore the trapped pc ---- *)
    iPoseProof (kti_36 with "Htext") as "Hi36".
    iApply (wp_csrw_sepc_s_sconf Φ (mword_of_int (KernelSyms.kerneltrap + 0x36)) s2_idx
              M k false epold ep
              ltac:(vm_compute; discriminate) ltac:(rgne; exact HMs2)
              with "Hcg Hsepc Hpc Hi36 [-]").
    iApply wp_next_off_intro. iIntros "Hcg Hsepc Hpc".
    iEval (rewrite (_ : mepc_val ep = ep); [| exact Hepal ]) in "Hsepc".
    assert (Hpc3a : add_vec_int (mword_of_int (KernelSyms.kerneltrap + 0x36) : mword 64) 4
                    = mword_of_int (KernelSyms.kerneltrap + 0x3a)) by pcw.
    iEval (rewrite Hpc3a) in "Hpc".
    (* ---- +0x3a: csrw sstatus,s1 -- restore the trapped sstatus.  THE one
       instruction that moves SPP/SPIE, so it takes the mirror. ---- *)
    iPoseProof (kti_3a with "Htext") as "Hi3a".
    iApply (wp_csrw_sstatus_s_sconf Φ (mword_of_int (KernelSyms.kerneltrap + 0x3a)) s1_idx
              M k false ms0 va vb
              ltac:(vm_compute; discriminate) ltac:(rgne; exact HMs1) Hms0f
              ltac:(cbn [sie_bit]; exact Hsie0)
              with "Hcg Hmir Hpc Hi3a [-]").
    iApply wp_next_off_intro.
    iIntros (msf) "%Hf_sie %Hf_spp %Hf_spie Hcgat Hmir Hpc".
    (* the [_at] flavour cannot be threaded across the loads (the funnel's
       [exists ms] loses it again), so close it now; the mirror is what
       carries SPP/SPIE to the end. *)
    iDestruct (sie_cap_gpr_at_close with "Hcgat") as "Hcg".
    rewrite Hspp0 in Hf_spp. rewrite Hspie0 in Hf_spie.
    iEval (rewrite Hf_spp Hf_spie) in "Hmir".
    assert (Hpc3e : add_vec_int (mword_of_int (KernelSyms.kerneltrap + 0x3a) : mword 64) 4
                    = mword_of_int (KernelSyms.kerneltrap + 0x3e)) by pcw.
    iEval (rewrite Hpc3e) in "Hpc".
    (* ---- +0x3e..+0x46: reload ra / s0 / s1 / s2 / s3 ---- *)
    iEval (rewrite -Hpa1) in "Hb1".
    iPoseProof (kti_3e with "Htext") as "Hi3e".
    iApply (wp_cldsp_s_sconf Φ (mword_of_int (KernelSyms.kerneltrap + 0x3e)) (mword_of_int 5 : mword 6) ra_idx
              M k ra0 false (dqm := DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi3e Hb1 [-]").
    iApply wp_next_off_intro. iIntros "Hcg Hpc Hb1".
    set (E1 := <[Regidx ra_idx := regval_into_reg ra0]> M).
    change (<[Regidx ra_idx := regval_into_reg ra0]> M) with E1.
    assert (HE1sp : E1 !!! Regidx csp_rs1 = M !!! Regidx csp_rs1)
      by (rewrite /E1 upd_ne; [reflexivity | vm_compute; discriminate]).
    assert (Hpc40 : add_vec_int (mword_of_int (KernelSyms.kerneltrap + 0x3e) : mword 64) 2
                    = mword_of_int (KernelSyms.kerneltrap + 0x40)) by pcw.
    iEval (rewrite Hpc40) in "Hpc".
    iEval (rewrite -Hpa2 -HE1sp) in "Hb2".
    iPoseProof (kti_40 with "Htext") as "Hi40".
    iApply (wp_cldsp_s_sconf Φ (mword_of_int (KernelSyms.kerneltrap + 0x40)) (mword_of_int 4 : mword 6) s0_idx
              E1 k s00 false (dqm := DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi40 Hb2 [-]").
    iApply wp_next_off_intro. iIntros "Hcg Hpc Hb2".
    set (E2 := <[Regidx s0_idx := regval_into_reg s00]> E1).
    change (<[Regidx s0_idx := regval_into_reg s00]> E1) with E2.
    assert (HE2sp : E2 !!! Regidx csp_rs1 = M !!! Regidx csp_rs1)
      by (rewrite /E2 upd_ne; [exact HE1sp | vm_compute; discriminate]).
    assert (Hpc42 : add_vec_int (mword_of_int (KernelSyms.kerneltrap + 0x40) : mword 64) 2
                    = mword_of_int (KernelSyms.kerneltrap + 0x42)) by pcw.
    iEval (rewrite Hpc42) in "Hpc".
    iEval (rewrite -Hpa3 -HE2sp) in "Hb3".
    iPoseProof (kti_42 with "Htext") as "Hi42".
    iApply (wp_cldsp_s_sconf Φ (mword_of_int (KernelSyms.kerneltrap + 0x42)) (mword_of_int 3 : mword 6) s1_idx
              E2 k s10 false (dqm := DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi42 Hb3 [-]").
    iApply wp_next_off_intro. iIntros "Hcg Hpc Hb3".
    set (E3 := <[Regidx s1_idx := regval_into_reg s10]> E2).
    change (<[Regidx s1_idx := regval_into_reg s10]> E2) with E3.
    assert (HE3sp : E3 !!! Regidx csp_rs1 = M !!! Regidx csp_rs1)
      by (rewrite /E3 upd_ne; [exact HE2sp | vm_compute; discriminate]).
    assert (Hpc44 : add_vec_int (mword_of_int (KernelSyms.kerneltrap + 0x42) : mword 64) 2
                    = mword_of_int (KernelSyms.kerneltrap + 0x44)) by pcw.
    iEval (rewrite Hpc44) in "Hpc".
    iEval (rewrite -Hpa4 -HE3sp) in "Hb4".
    iPoseProof (kti_44 with "Htext") as "Hi44".
    iApply (wp_cldsp_s_sconf Φ (mword_of_int (KernelSyms.kerneltrap + 0x44)) (mword_of_int 2 : mword 6) s2_idx
              E3 k s20 false (dqm := DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi44 Hb4 [-]").
    iApply wp_next_off_intro. iIntros "Hcg Hpc Hb4".
    set (E4 := <[Regidx s2_idx := regval_into_reg s20]> E3).
    change (<[Regidx s2_idx := regval_into_reg s20]> E3) with E4.
    assert (HE4sp : E4 !!! Regidx csp_rs1 = M !!! Regidx csp_rs1)
      by (rewrite /E4 upd_ne; [exact HE3sp | vm_compute; discriminate]).
    assert (Hpc46 : add_vec_int (mword_of_int (KernelSyms.kerneltrap + 0x44) : mword 64) 2
                    = mword_of_int (KernelSyms.kerneltrap + 0x46)) by pcw.
    iEval (rewrite Hpc46) in "Hpc".
    iEval (rewrite -Hpa5 -HE4sp) in "Hb5".
    iPoseProof (kti_46 with "Htext") as "Hi46".
    iApply (wp_cldsp_s_sconf Φ (mword_of_int (KernelSyms.kerneltrap + 0x46)) (mword_of_int 1 : mword 6) s3_idx
              E4 k s30 false (dqm := DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi46 Hb5 [-]").
    iApply wp_next_off_intro. iIntros "Hcg Hpc Hb5".
    set (E5 := <[Regidx s3_idx := regval_into_reg s30]> E4).
    change (<[Regidx s3_idx := regval_into_reg s30]> E4) with E5.
    assert (HE5sp : E5 !!! Regidx csp_rs1 = pa_stk sp0 6)
      by (rewrite /E5 upd_ne; [rewrite HE4sp; exact HMsp | vm_compute; discriminate]).
    assert (Hpc48 : add_vec_int (mword_of_int (KernelSyms.kerneltrap + 0x46) : mword 64) 2
                    = mword_of_int (KernelSyms.kerneltrap + 0x48)) by pcw.
    iEval (rewrite Hpc48) in "Hpc".
    (* ---- +0x48: c.addi16sp sp,48 -- pop the frame ---- *)
    assert (Hwv : add_vec (E5 !!! Regidx csp_rs1)
                    (sign_extend' 64 (caddi16sp_imm (mword_of_int 3 : mword 6))) = sp0).
    { rewrite HE5sp.
      assert (Hps : pa_stk sp0 6
                    = add_vec sp0 (sign_extend' 64 (caddi16sp_imm (mword_of_int 61 : mword 6)))).
      { unfold pa_stk, add_vec_int. apply f_equal. apply bv_eq; vm_compute; reflexivity. }
      rewrite Hps. apply frame_cancel_48. }
    assert (Hpop : E5 !!! Regidx csp_rs1
                   = pa_stk (add_vec (E5 !!! Regidx csp_rs1)
                               (sign_extend' 64 (caddi16sp_imm (mword_of_int 3 : mword 6)))) 6).
    { rewrite Hwv. exact HE5sp. }
    (* the loads handed each cell back addressed off the map they ran at, so
       bridge every one to [pa_stk sp0 j] before rebuilding the frame. *)
    iEval (rewrite Hpa1) in "Hb1".
    iEval (rewrite HE1sp Hpa2) in "Hb2".
    iEval (rewrite HE2sp Hpa3) in "Hb3".
    iEval (rewrite HE3sp Hpa4) in "Hb4".
    iEval (rewrite HE4sp Hpa5) in "Hb5".
    iAssert (stack_own sp0 6) with "[Hb1 Hb2 Hb3 Hb4 Hb5 Hb6]" as "Hframe6".
    { rewrite stack_own_slots. cbn [seq].
      iSplitL "Hb1". { iExists _. iExact "Hb1". }
      iSplitL "Hb2". { iExists _. iExact "Hb2". }
      iSplitL "Hb3". { iExists _. iExact "Hb3". }
      iSplitL "Hb4". { iExists _. iExact "Hb4". }
      iSplitL "Hb5". { iExists _. iExact "Hb5". }
      iSplitL "Hb6". { iExists _. iExact "Hb6". }
      done. }
    iPoseProof (kti_48 with "Htext") as "Hi48".
    iEval (rewrite -Hwv) in "Hframe6".
    iApply (wp_caddi16sp_pop_s_sconf Φ (mword_of_int (KernelSyms.kerneltrap + 0x48))
              (mword_of_int 3 : mword 6) E5 k 6 false Hpop
              with "Hcg Hpc Hi48 Hframe6 [-]").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    set (E6 := <[Regidx csp_rs1 := regval_into_reg
        (add_vec (E5 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 3 : mword 6))))]> E5).
    change (<[Regidx csp_rs1 := regval_into_reg
        (add_vec (E5 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 3 : mword 6))))]> E5) with E6.
    assert (Hpc4a : add_vec_int (mword_of_int (KernelSyms.kerneltrap + 0x48) : mword 64) 2
                    = mword_of_int (KernelSyms.kerneltrap + 0x4a)) by pcw.
    iEval (rewrite Hpc4a) in "Hpc".
    (* ---- +0x4a: c.jr ra ---- *)
    assert (HE6ra : E6 !!! Regidx ra_idx = ra0).
    { rewrite /E6 upd_ne; [| vm_compute; discriminate].
      rewrite /E5 upd_ne; [| vm_compute; discriminate].
      rewrite /E4 upd_ne; [| vm_compute; discriminate].
      rewrite /E3 upd_ne; [| vm_compute; discriminate].
      rewrite /E2 upd_ne; [| vm_compute; discriminate].
      rewrite /E1. apply upd_eq. }
    iPoseProof (kti_4a with "Htext") as "Hi4a".
    iApply (wp_cret_s_sconf Φ (mword_of_int (KernelSyms.kerneltrap + 0x4a)) ra_idx
              E6 (k + 6) false ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi4a [-]").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    assert (Hraf : ret_pc (rget E6 ra_idx) = ret_pc ra0) by (rgne; rewrite HE6ra; reflexivity).
    iEval (rewrite Hraf) in "Hpc".
    (* ---- THE POST.  Re-open the bundle and READ THE THREE BITS BACK OFF THE
       MIRROR: SPP/SPIE by agreement with the tie, SIE off the [b = false]
       arm index.  This is what makes the absolute postcondition provable
       after all the round-trips. ---- *)
    iDestruct (sie_cap_gpr_at_open with "Hcg") as (msx) "Hcgat".
    iDestruct (sconf_at_sret msx ('b"1") ('b"1") with "[Hcgat] Hmir") as %[Hxspp Hxspie].
    { iDestruct "Hcgat" as "(_ & Hsc & _ & _)". iExact "Hsc". }
    iAssert (⌜ _get_Mstatus_SIE msx = ('b"0" : mword 1) ⌝)%I as %Hxsie.
    { iDestruct "Hcgat" as "(_ & [(_ & Hsie & _ & _) _] & (_ & _ & Harm) & _)".
      iApply (sie_arm_half_agree false p msx with "Hsie Harm"). }
    (* the register round-trip: every callee-saved slot is the caller's *)
    assert (Hcs : callee_saved m0 E6).
    { apply kt_cs_of.
      - rewrite /E6 upd_eq. rewrite Hwv. rewrite Hm0sp. reflexivity.
      - rewrite /E6 upd_ne; [| vm_compute; discriminate].
        rewrite /E5 upd_ne; [| vm_compute; discriminate].
        rewrite /E4 upd_ne; [| vm_compute; discriminate].
        rewrite /E3 upd_ne; [| vm_compute; discriminate].
        rewrite /E2 upd_eq. rewrite Hm0s0. reflexivity.
      - rewrite /E6 upd_ne; [| vm_compute; discriminate].
        rewrite /E5 upd_ne; [| vm_compute; discriminate].
        rewrite /E4 upd_ne; [| vm_compute; discriminate].
        rewrite /E3 upd_eq. rewrite Hm0s1. reflexivity.
      - rewrite /E6 upd_ne; [| vm_compute; discriminate].
        rewrite /E5 upd_ne; [| vm_compute; discriminate].
        rewrite /E4 upd_eq. rewrite Hm0s2. reflexivity.
      - rewrite /E6 upd_ne; [| vm_compute; discriminate].
        rewrite /E5 upd_eq. rewrite Hm0s3. reflexivity.
      - intros r Hcs Hrsp Hrs0 Hrs1 Hrs2 Hrs3.
        rewrite /E6 upd_ne; [| congruence].
        rewrite /E5 upd_ne; [| congruence].
        rewrite /E4 upd_ne; [| congruence].
        rewrite /E3 upd_ne; [| congruence].
        rewrite /E2 upd_ne; [| congruence].
        rewrite /E1 upd_ne.
        + apply Hthr; assumption.
        + (* ra is NOT callee-saved, so [is_cs_idx r] already refutes r = ra *)
          intro He. injection He as He2.
          revert Hcs. rewrite He2. vm_compute. discriminate. }
    iApply ("Hcont" $! E6 msx with "[%] [%] [%] [%] Hcgat Hmir Hcpu Hsepc Hpc").
    { exact Hcs. }
    { exact Hxspp. }
    { exact Hxspie. }
    { exact Hxsie. }
  Qed.

End ProofKerneltrapParts.
