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
Require Import CpuOwn.
Require Import IntrDefs.
Require Import HartTp WpNext.
Require Import VcGen KernelRvcDecode.
Require Import WpSconfAlu WpSconfMem WpSconfCtl WpSconfBtype WpSconfCsr.
Require Import ProofPushOff.
Require Import CodeKerneltrap.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Import Defs.

Local Open Scope Z_scope.
Set Printing Depth 40.

(* a5 and ra are CALLER-saved, so [is_cs_idx r = true] already refutes
   [r = a5] / [r = ra].  Both tactics are used by ProofKerneltrap too, so
   they are NOT [Local]. *)
Ltac ktne_a5 :=
  let He := fresh in
  intro He; injection He as He;
  match goal with H : is_cs_idx _ = true |- _ => revert H end;
  rewrite He; vm_compute; discriminate.

Ltac ktne_ra :=
  let He := fresh in
  intro He; injection He as He;
  match goal with H : is_cs_idx _ = true |- _ => revert H end;
  rewrite He; vm_compute; discriminate.

Section ProofKerneltrapParts.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.
  Context {p : mword 64}.

  Notation ra_idx := (mword_of_int 1 : mword 5).
  Notation s0_idx := (mword_of_int 8 : mword 5).
  Notation s1_idx := (mword_of_int 9 : mword 5).
  Notation s2_idx := (mword_of_int 18 : mword 5).
  Notation s3_idx := (mword_of_int 19 : mword 5).
  Notation a5_idx := (mword_of_int 15 : mword 5).

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

  (* [kt_thr] composes with any callee-saved call: a callee preserves every
     cs register, and all five [kt_thr] excludes are cs. *)
  Lemma kt_thr_cs (m M M' : regfile) :
    kt_thr m M -> callee_saved M M' -> kt_thr m M'.
  Proof.
    intros Hthr Hcs r Hr Hsp Hs0 Hs1 Hs2 Hs3.
    rewrite (callee_saved_lookup Hcs r Hr). apply Hthr; assumption.
  Qed.

  (* the five frame-slot addresses off a pushed 6-slot frame: slot j sits at
     [sp + 8*(6-j)], so ra/s0/s1/s2/s3 use uimm 5/4/3/2/1. *)
  Local Ltac ktslot :=
    unfold pa_stk, add_vec_int; rewrite add_vec_off2;
    f_equal; try (apply bv_eq; vm_compute; reflexivity).

  Lemma kt_pa1 (sp0 : mword 64) :
    add_vec (pa_stk sp0 6) (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000"))) = pa_stk sp0 1.
  Proof. ktslot. Qed.
  Lemma kt_pa2 (sp0 : mword 64) :
    add_vec (pa_stk sp0 6) (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000"))) = pa_stk sp0 2.
  Proof. ktslot. Qed.
  Lemma kt_pa3 (sp0 : mword 64) :
    add_vec (pa_stk sp0 6) (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000"))) = pa_stk sp0 3.
  Proof. ktslot. Qed.
  Lemma kt_pa4 (sp0 : mword 64) :
    add_vec (pa_stk sp0 6) (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000"))) = pa_stk sp0 4.
  Proof. ktslot. Qed.
  Lemma kt_pa5 (sp0 : mword 64) :
    add_vec (pa_stk sp0 6) (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) = pa_stk sp0 5.
  Proof. ktslot. Qed.

  (* ================================================================== *)
  (* THE TWO BRANCH OBLIGATIONS -- what makes the panic arms dead.        *)
  (*                                                                     *)
  (* [andi a5,s1,256] tests SPP (bit 8) of the SAVED sstatus, and         *)
  (* [c.andi a5,a5,2] tests SIE (bit 1) of a FRESH read.  The second is   *)
  (* [ProofPushOff.pop_sstatus_clear_neq] already; the first is one       *)
  (* reading of [WpGprCsrwC.sstatus_spp_mask], which sits beside          *)
  (* [sie_bit] because usertrap's panic arm is the other reading of the   *)
  (* same equation and neither parts file may import the other's.         *)
  (* ================================================================== *)

  (* SPP = 1 in the saved sstatus makes [andi a5,s1,256] NONZERO, so the
     "not from supervisor mode" [c.beqz] falls through.  One instance of
     [WpGprCsrwC.sstatus_spp_mask], which is the hypothesis-free form both
     trap handlers read at their own polarity -- usertrap's opposite reading
     is [ProofUsertrapParts.ut_spp_clear_eq]. *)
  Lemma kt_spp_set_neq (ms : mword 64) :
    _get_Mstatus_SPP ms = ('b"1" : mword 1) ->
    eq_vec (and_vec (sstatus_read ms)
              (sign_extend' 64 (mword_of_int 256 : mword 12))) zero_reg = false.
  Proof.
    intro HSPP.
    rewrite WpGprCsrwC.sstatus_spp_mask HSPP. reflexivity.
  Qed.

  (* ================================================================== *)
  (* THE STRAIGHT-LINE HEAD (kerneltrap+0x00 .. +0x2a).                   *)
  (*                                                                     *)
  (* Prologue (6-slot frame, five saves, the frame pointer), the three    *)
  (* CSR reads, and BOTH panic tests -- each of which provably falls      *)
  (* through: [kt_spp_set_neq] for "not from supervisor mode" (SPP = 1 in *)
  (* the saved sstatus makes [andi a5,s1,256] nonzero) and               *)
  (* [ProofPushOff.pop_sstatus_clear_neq] for "interrupts enabled" (a     *)
  (* FRESH sstatus read at +0x22, whose SIE is 0 off the b = false arm).  *)
  (* Ends at the [jal devintr], which is the functor's business.          *)
  (* ================================================================== *)
  Lemma kt_pro
      (m : regfile) (av : nat) (ep sc : mword 64) :
    (6 <= av)%nat ->
    ret_pc ep = ep ->
    sie_cap_gpr m av false p -∗
    sret_bits ('b"1" : mword 1) ('b"1" : mword 1) -∗
    kernel_text -∗
    pc_is (mword_of_int KernelSyms.kerneltrap : mword 64) -∗
    sepc ↦ᵣ ep -∗
    scause ↦ᵣ sc -∗
    ( ∀ (M : regfile) (ms0 : mword 64),
        ⌜ M !!! Regidx csp_rs1 = pa_stk (m !!! Regidx csp_rs1) 6 ⌝ -∗
        ⌜ M !!! Regidx s2_idx = ep ⌝ -∗
        ⌜ M !!! Regidx s1_idx = sstatus_read ms0 ⌝ -∗
        ⌜ sconf_ms_facts ms0 ⌝ -∗
        ⌜ _get_Mstatus_SIE ms0 = ('b"0" : mword 1) ⌝ -∗
        ⌜ _get_Mstatus_SPP ms0 = ('b"1" : mword 1) ⌝ -∗
        ⌜ _get_Mstatus_SPIE ms0 = ('b"1" : mword 1) ⌝ -∗
        ⌜ kt_thr m M ⌝ -∗
        sie_cap_gpr M (av - 6) false p -∗
        sret_bits ('b"1" : mword 1) ('b"1" : mword 1) -∗
        sepc ↦ᵣ ep -∗
        scause ↦ᵣ sc -∗
        pc_is (mword_of_int (KernelSyms.kerneltrap + 0x2a) : mword 64) -∗
        pa_stk (m !!! Regidx csp_rs1) 1 ↦₈ (m !!! Regidx ra_idx) -∗
        pa_stk (m !!! Regidx csp_rs1) 2 ↦₈ (m !!! Regidx s0_idx) -∗
        pa_stk (m !!! Regidx csp_rs1) 3 ↦₈ (m !!! Regidx s1_idx) -∗
        pa_stk (m !!! Regidx csp_rs1) 4 ↦₈ (m !!! Regidx s2_idx) -∗
        pa_stk (m !!! Regidx csp_rs1) 5 ↦₈ (m !!! Regidx s3_idx) -∗
        (∃ v : mword 64, pa_stk (m !!! Regidx csp_rs1) 6 ↦₈ v) -∗
        WP (Loop : expr riscv_lang) ) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hav Hepal.
    iIntros "Hcg Hmir #Htext Hpc Hsepc Hscause Hcont".
    (* ---- +0x00: c.addi16sp sp,-48 -- push the 6-slot frame ---- *)
    assert (Hwv : add_vec (m !!! Regidx csp_rs1)
                    (sign_extend' 64 (caddi16sp_imm (mword_of_int 61 : mword 6)))
                  = pa_stk (m !!! Regidx csp_rs1) 6).
    { symmetry. unfold pa_stk, add_vec_int. apply f_equal.
      apply bv_eq; vm_compute; reflexivity. }
    iPoseProof (kti_00 with "Htext") as "Hi00".
    iApply (wp_caddi16sp_push_s_sconf (mword_of_int KernelSyms.kerneltrap)
              (mword_of_int 61 : mword 6) m av 6 false ltac:(lia) Hwv
              with "Hcg Hpc Hi00").
    iApply wp_next_off_intro. iIntros "Hcg Hframe Hpc".
    set (A0 := <[Regidx csp_rs1 := regval_into_reg
        (add_vec (m !!! Regidx csp_rs1)
           (sign_extend' 64 (caddi16sp_imm (mword_of_int 61 : mword 6))))]> m).
    change (<[Regidx csp_rs1 := regval_into_reg
        (add_vec (m !!! Regidx csp_rs1)
           (sign_extend' 64 (caddi16sp_imm (mword_of_int 61 : mword 6))))]> m) with A0.
    assert (HA0sp : A0 !!! Regidx csp_rs1 = pa_stk (m !!! Regidx csp_rs1) 6)
      by (rewrite /A0 upd_eq; unfold regval_into_reg; exact Hwv).
    assert (Hpc02 : add_vec_int (mword_of_int KernelSyms.kerneltrap : mword 64) 2
                    = mword_of_int (KernelSyms.kerneltrap + 0x02)) by pcw.
    iEval (rewrite Hpc02) in "Hpc".
    (* split the fresh frame into its six slots *)
    iEval (rewrite stack_own_slots; cbn [seq]) in "Hframe".
    iDestruct "Hframe" as "(S1 & S2 & S3 & S4 & S5 & S6 & _)".
    iDestruct "S1" as (u1) "Hb1". iDestruct "S2" as (u2) "Hb2".
    iDestruct "S3" as (u3) "Hb3". iDestruct "S4" as (u4) "Hb4".
    iDestruct "S5" as (u5) "Hb5".
    (* ---- +0x02..+0x0a: save ra / s0 / s1 / s2 / s3 ---- *)
    iEval (rewrite -(kt_pa1 (m !!! Regidx csp_rs1)) -HA0sp) in "Hb1".
    iPoseProof (kti_02 with "Htext") as "Hi02".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.kerneltrap + 0x02))
              (mword_of_int 5 : mword 6) ra_idx A0 (av - 6)%nat u1 false
              with "Hcg Hpc Hi02 Hb1").
    iApply wp_next_off_intro. iIntros "Hcg Hpc Hb1".
    assert (Hpc04 : add_vec_int (mword_of_int (KernelSyms.kerneltrap + 0x02) : mword 64) 2
                    = mword_of_int (KernelSyms.kerneltrap + 0x04)) by pcw.
    iEval (rewrite Hpc04) in "Hpc".
    iEval (rewrite -(kt_pa2 (m !!! Regidx csp_rs1)) -HA0sp) in "Hb2".
    iPoseProof (kti_04 with "Htext") as "Hi04".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.kerneltrap + 0x04))
              (mword_of_int 4 : mword 6) s0_idx A0 (av - 6)%nat u2 false
              with "Hcg Hpc Hi04 Hb2").
    iApply wp_next_off_intro. iIntros "Hcg Hpc Hb2".
    assert (Hpc06 : add_vec_int (mword_of_int (KernelSyms.kerneltrap + 0x04) : mword 64) 2
                    = mword_of_int (KernelSyms.kerneltrap + 0x06)) by pcw.
    iEval (rewrite Hpc06) in "Hpc".
    iEval (rewrite -(kt_pa3 (m !!! Regidx csp_rs1)) -HA0sp) in "Hb3".
    iPoseProof (kti_06 with "Htext") as "Hi06".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.kerneltrap + 0x06))
              (mword_of_int 3 : mword 6) s1_idx A0 (av - 6)%nat u3 false
              with "Hcg Hpc Hi06 Hb3").
    iApply wp_next_off_intro. iIntros "Hcg Hpc Hb3".
    assert (Hpc08 : add_vec_int (mword_of_int (KernelSyms.kerneltrap + 0x06) : mword 64) 2
                    = mword_of_int (KernelSyms.kerneltrap + 0x08)) by pcw.
    iEval (rewrite Hpc08) in "Hpc".
    iEval (rewrite -(kt_pa4 (m !!! Regidx csp_rs1)) -HA0sp) in "Hb4".
    iPoseProof (kti_08 with "Htext") as "Hi08".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.kerneltrap + 0x08))
              (mword_of_int 2 : mword 6) s2_idx A0 (av - 6)%nat u4 false
              with "Hcg Hpc Hi08 Hb4").
    iApply wp_next_off_intro. iIntros "Hcg Hpc Hb4".
    assert (Hpc0a : add_vec_int (mword_of_int (KernelSyms.kerneltrap + 0x08) : mword 64) 2
                    = mword_of_int (KernelSyms.kerneltrap + 0x0a)) by pcw.
    iEval (rewrite Hpc0a) in "Hpc".
    iEval (rewrite -(kt_pa5 (m !!! Regidx csp_rs1)) -HA0sp) in "Hb5".
    iPoseProof (kti_0a with "Htext") as "Hi0a".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.kerneltrap + 0x0a))
              (mword_of_int 1 : mword 6) s3_idx A0 (av - 6)%nat u5 false
              with "Hcg Hpc Hi0a Hb5").
    iApply wp_next_off_intro. iIntros "Hcg Hpc Hb5".
    assert (Hpc0c : add_vec_int (mword_of_int (KernelSyms.kerneltrap + 0x0a) : mword 64) 2
                    = mword_of_int (KernelSyms.kerneltrap + 0x0c)) by pcw.
    iEval (rewrite Hpc0c) in "Hpc".
    (* the five saved words are now the caller's, at their slots *)
    iEval (rewrite HA0sp (kt_pa1 (m !!! Regidx csp_rs1))) in "Hb1".
    iEval (rewrite HA0sp (kt_pa2 (m !!! Regidx csp_rs1))) in "Hb2".
    iEval (rewrite HA0sp (kt_pa3 (m !!! Regidx csp_rs1))) in "Hb3".
    iEval (rewrite HA0sp (kt_pa4 (m !!! Regidx csp_rs1))) in "Hb4".
    iEval (rewrite HA0sp (kt_pa5 (m !!! Regidx csp_rs1))) in "Hb5".
    assert (Hv1 : rget A0 ra_idx = m !!! Regidx ra_idx)
      by (rgne; rewrite /A0 upd_ne; [reflexivity | vm_compute; discriminate]).
    assert (Hv2 : rget A0 s0_idx = m !!! Regidx s0_idx)
      by (rgne; rewrite /A0 upd_ne; [reflexivity | vm_compute; discriminate]).
    assert (Hv3 : rget A0 s1_idx = m !!! Regidx s1_idx)
      by (rgne; rewrite /A0 upd_ne; [reflexivity | vm_compute; discriminate]).
    assert (Hv4 : rget A0 s2_idx = m !!! Regidx s2_idx)
      by (rgne; rewrite /A0 upd_ne; [reflexivity | vm_compute; discriminate]).
    assert (Hv5 : rget A0 s3_idx = m !!! Regidx s3_idx)
      by (rgne; rewrite /A0 upd_ne; [reflexivity | vm_compute; discriminate]).
    iEval (rewrite Hv1) in "Hb1". iEval (rewrite Hv2) in "Hb2".
    iEval (rewrite Hv3) in "Hb3". iEval (rewrite Hv4) in "Hb4".
    iEval (rewrite Hv5) in "Hb5".
    (* ---- +0x0c: c.addi4spn s0,sp,48 -- the frame pointer (dead, but it
       writes s0, so the map moves) ---- *)
    iPoseProof (kti_0c with "Htext") as "Hi0c".
    iApply (wp_caddi4spn_s_sconf (mword_of_int (KernelSyms.kerneltrap + 0x0c))
              (Cregidx (mword_of_int 0)) (mword_of_int 12 : mword 8) s0_idx
              A0 (av - 6)%nat false
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi0c").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    set (A1 := <[Regidx s0_idx := regval_into_reg
        (add_vec (A0 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 12 : mword 8))))]> A0).
    change (<[Regidx s0_idx := regval_into_reg
        (add_vec (A0 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 12 : mword 8))))]> A0) with A1.
    assert (HA1sp : A1 !!! Regidx csp_rs1 = pa_stk (m !!! Regidx csp_rs1) 6)
      by (rewrite /A1 upd_ne; [exact HA0sp | vm_compute; discriminate]).
    assert (Hpc0e : add_vec_int (mword_of_int (KernelSyms.kerneltrap + 0x0c) : mword 64) 2
                    = mword_of_int (KernelSyms.kerneltrap + 0x0e)) by pcw.
    iEval (rewrite Hpc0e) in "Hpc".
    (* ---- +0x0e: csrr s2,sepc ---- *)
    iPoseProof (kti_0e with "Htext") as "Hi0e".
    iApply (wp_csrr_sepc_s_sconf (mword_of_int (KernelSyms.kerneltrap + 0x0e)) s2_idx
              A1 (av - 6)%nat (DfracOwn 1) ep
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hsepc Hpc Hi0e").
    iApply wp_next_off_intro. iIntros "Hcg Hsepc Hpc".
    iEval (rewrite (_ : mepc_val ep = ep); [| exact Hepal ]) in "Hcg".
    set (A2 := <[Regidx s2_idx := regval_into_reg ep]> A1).
    change (<[Regidx s2_idx := regval_into_reg ep]> A1) with A2.
    assert (HA2sp : A2 !!! Regidx csp_rs1 = pa_stk (m !!! Regidx csp_rs1) 6)
      by (rewrite /A2 upd_ne; [exact HA1sp | vm_compute; discriminate]).
    assert (HA2s2 : A2 !!! Regidx s2_idx = ep) by (rewrite /A2; apply upd_eq).
    assert (Hpc12 : add_vec_int (mword_of_int (KernelSyms.kerneltrap + 0x0e) : mword 64) 4
                    = mword_of_int (KernelSyms.kerneltrap + 0x12)) by pcw.
    iEval (rewrite Hpc12) in "Hpc".
    (* ---- +0x12: csrr s1,sstatus.  This leaf DISASSEMBLES the bundle (it is
       push_off's read), so the pieces come back separately and are rejoined
       below.  It also names the mstatus it read, which is what lets the
       [sret_bits] mirror turn into SPP/SPIE facts about that very [ms0]. ---- *)
    iPoseProof (kti_12 with "Htext") as "Hi12".
    iApply (wp_csrr_sstatus_s_sconf (mword_of_int (KernelSyms.kerneltrap + 0x12)) s1_idx
              A2 (av - 6)%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi12").
    iApply wp_next_off_intro.
    iIntros (ms0) "%Hms0f Hhs Hsc Htr Hpc Hfile (Hstk & %Hsie0' & Harm)".
    assert (Hsie0 : _get_Mstatus_SIE ms0 = ('b"0" : mword 1))
      by (cbn [sie_bit] in Hsie0'; exact Hsie0').
    iDestruct (sconf_at_sret ms0 ('b"1") ('b"1") with "Hsc Hmir") as %[Hspp0 Hspie0].
    iDestruct (sconf_at_close with "Hsc") as "Hsc".
    iDestruct (sie_cap_gpr_join with "Hhs Hsc [Hstk Htr Harm] Hfile") as "Hcg".
    { rewrite /sie_cap. iFrame "Hstk Htr Harm". }
    set (A3 := <[Regidx s1_idx := regval_into_reg (sstatus_read ms0)]> A2).
    change (<[Regidx s1_idx := regval_into_reg (sstatus_read ms0)]> A2) with A3.
    assert (HA3sp : A3 !!! Regidx csp_rs1 = pa_stk (m !!! Regidx csp_rs1) 6)
      by (rewrite /A3 upd_ne; [exact HA2sp | vm_compute; discriminate]).
    assert (HA3s1 : A3 !!! Regidx s1_idx = sstatus_read ms0) by (rewrite /A3; apply upd_eq).
    assert (HA3s2 : A3 !!! Regidx s2_idx = ep)
      by (rewrite /A3 upd_ne; [exact HA2s2 | vm_compute; discriminate]).
    assert (Hpc16 : add_vec_int (mword_of_int (KernelSyms.kerneltrap + 0x12) : mword 64) 4
                    = mword_of_int (KernelSyms.kerneltrap + 0x16)) by pcw.
    iEval (rewrite Hpc16) in "Hpc".
    (* ---- +0x16: csrr a5,scause ---- *)
    iPoseProof (kti_16 with "Htext") as "Hi16".
    iApply (wp_csrr_scause_s_sconf (mword_of_int (KernelSyms.kerneltrap + 0x16)) a5_idx
              A3 (av - 6)%nat (DfracOwn 1) sc
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hscause Hpc Hi16").
    iApply wp_next_off_intro. iIntros "Hcg Hscause Hpc".
    set (A4 := <[Regidx a5_idx := regval_into_reg sc]> A3).
    change (<[Regidx a5_idx := regval_into_reg sc]> A3) with A4.
    assert (HA4sp : A4 !!! Regidx csp_rs1 = pa_stk (m !!! Regidx csp_rs1) 6)
      by (rewrite /A4 upd_ne; [exact HA3sp | vm_compute; discriminate]).
    assert (HA4s1 : A4 !!! Regidx s1_idx = sstatus_read ms0)
      by (rewrite /A4 upd_ne; [exact HA3s1 | vm_compute; discriminate]).
    assert (HA4s2 : A4 !!! Regidx s2_idx = ep)
      by (rewrite /A4 upd_ne; [exact HA3s2 | vm_compute; discriminate]).
    assert (Hpc1a : add_vec_int (mword_of_int (KernelSyms.kerneltrap + 0x16) : mword 64) 4
                    = mword_of_int (KernelSyms.kerneltrap + 0x1a)) by pcw.
    iEval (rewrite Hpc1a) in "Hpc".
    (* ---- +0x1a: c.mv s3,a5 (stash the cause; only printk would read it) ---- *)
    iPoseProof (kti_1a with "Htext") as "Hi1a".
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.kerneltrap + 0x1a)) s3_idx a5_idx
              A4 (av - 6)%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi1a").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    set (A5 := <[Regidx s3_idx := regval_into_reg (add_vec zero_reg (rget A4 a5_idx))]> A4).
    change (<[Regidx s3_idx := regval_into_reg (add_vec zero_reg (rget A4 a5_idx))]> A4) with A5.
    assert (HA5sp : A5 !!! Regidx csp_rs1 = pa_stk (m !!! Regidx csp_rs1) 6)
      by (rewrite /A5 upd_ne; [exact HA4sp | vm_compute; discriminate]).
    assert (HA5s1 : A5 !!! Regidx s1_idx = sstatus_read ms0)
      by (rewrite /A5 upd_ne; [exact HA4s1 | vm_compute; discriminate]).
    assert (HA5s2 : A5 !!! Regidx s2_idx = ep)
      by (rewrite /A5 upd_ne; [exact HA4s2 | vm_compute; discriminate]).
    assert (Hpc1c : add_vec_int (mword_of_int (KernelSyms.kerneltrap + 0x1a) : mword 64) 2
                    = mword_of_int (KernelSyms.kerneltrap + 0x1c)) by pcw.
    iEval (rewrite Hpc1c) in "Hpc".
    (* ---- +0x1c: andi a5,s1,256 -- the SPP test ---- *)
    iPoseProof (kti_1c with "Htext") as "Hi1c".
    iApply (wp_andi_s_sconf (mword_of_int (KernelSyms.kerneltrap + 0x1c)) a5_idx s1_idx
              (mword_of_int 256 : mword 12)
              (and_vec (sstatus_read ms0) (sign_extend' 64 (mword_of_int 256 : mword 12)))
              A5 (av - 6)%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(rgne; rewrite HA5s1; reflexivity)
              with "Hcg Hpc Hi1c").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    set (A6 := <[Regidx a5_idx := regval_into_reg
        (and_vec (sstatus_read ms0) (sign_extend' 64 (mword_of_int 256 : mword 12)))]> A5).
    change (<[Regidx a5_idx := regval_into_reg
        (and_vec (sstatus_read ms0) (sign_extend' 64 (mword_of_int 256 : mword 12)))]> A5) with A6.
    assert (HA6sp : A6 !!! Regidx csp_rs1 = pa_stk (m !!! Regidx csp_rs1) 6)
      by (rewrite /A6 upd_ne; [exact HA5sp | vm_compute; discriminate]).
    assert (HA6s1 : A6 !!! Regidx s1_idx = sstatus_read ms0)
      by (rewrite /A6 upd_ne; [exact HA5s1 | vm_compute; discriminate]).
    assert (HA6s2 : A6 !!! Regidx s2_idx = ep)
      by (rewrite /A6 upd_ne; [exact HA5s2 | vm_compute; discriminate]).
    assert (Hpc20 : add_vec_int (mword_of_int (KernelSyms.kerneltrap + 0x1c) : mword 64) 4
                    = mword_of_int (KernelSyms.kerneltrap + 0x20)) by pcw.
    iEval (rewrite Hpc20) in "Hpc".
    (* ---- +0x20: c.beqz a5 -> panic("not from supervisor mode").  DEAD:
       SPP = 1 in the saved sstatus makes a5 nonzero. ---- *)
    iPoseProof (kti_20 with "Htext") as "Hi20".
    iApply (wp_cbeqz_fall_s_sconf (mword_of_int (KernelSyms.kerneltrap + 0x20))
              (mword_of_int 22 : mword 8) (Cregidx (mword_of_int 7)) a5_idx
              A6 (av - 6)%nat false
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
              ltac:(rgne; rewrite /A6 upd_eq; unfold regval_into_reg;
                    exact (kt_spp_set_neq ms0 Hspp0))
              with "Hcg Hpc Hi20").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    assert (Hpc22 : add_vec_int (mword_of_int (KernelSyms.kerneltrap + 0x20) : mword 64) 2
                    = mword_of_int (KernelSyms.kerneltrap + 0x22)) by pcw.
    iEval (rewrite Hpc22) in "Hpc".
    (* ---- +0x22: csrr a5,sstatus -- a SECOND, fresh read, for intr_get() ---- *)
    iPoseProof (kti_22 with "Htext") as "Hi22".
    iApply (wp_csrr_sstatus_s_sconf (mword_of_int (KernelSyms.kerneltrap + 0x22)) a5_idx
              A6 (av - 6)%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi22").
    iApply wp_next_off_intro.
    iIntros (ms1) "%Hms1f Hhs Hsc Htr Hpc Hfile (Hstk & %Hsie1' & Harm)".
    assert (Hsie1 : _get_Mstatus_SIE ms1 = ('b"0" : mword 1))
      by (cbn [sie_bit] in Hsie1'; exact Hsie1').
    iDestruct (sconf_at_close with "Hsc") as "Hsc".
    iDestruct (sie_cap_gpr_join with "Hhs Hsc [Hstk Htr Harm] Hfile") as "Hcg".
    { rewrite /sie_cap. iFrame "Hstk Htr Harm". }
    set (A7 := <[Regidx a5_idx := regval_into_reg (sstatus_read ms1)]> A6).
    change (<[Regidx a5_idx := regval_into_reg (sstatus_read ms1)]> A6) with A7.
    assert (HA7sp : A7 !!! Regidx csp_rs1 = pa_stk (m !!! Regidx csp_rs1) 6)
      by (rewrite /A7 upd_ne; [exact HA6sp | vm_compute; discriminate]).
    assert (HA7s1 : A7 !!! Regidx s1_idx = sstatus_read ms0)
      by (rewrite /A7 upd_ne; [exact HA6s1 | vm_compute; discriminate]).
    assert (HA7s2 : A7 !!! Regidx s2_idx = ep)
      by (rewrite /A7 upd_ne; [exact HA6s2 | vm_compute; discriminate]).
    assert (Hpc26 : add_vec_int (mword_of_int (KernelSyms.kerneltrap + 0x22) : mword 64) 4
                    = mword_of_int (KernelSyms.kerneltrap + 0x26)) by pcw.
    iEval (rewrite Hpc26) in "Hpc".
    (* ---- +0x26: c.andi a5,a5,2 -- mask off SIE ---- *)
    iPoseProof (kti_26 with "Htext") as "Hi26".
    iApply (wp_candi_s_sconf (mword_of_int (KernelSyms.kerneltrap + 0x26)) a5_idx
              (mword_of_int 2 : mword 6) A7 (av - 6)%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi26").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    set (A8 := <[Regidx a5_idx := regval_into_reg
        (and_vec (rget A7 a5_idx) (sign_extend' 64 (sign_extend' 12 (mword_of_int 2 : mword 6))))]> A7).
    change (<[Regidx a5_idx := regval_into_reg
        (and_vec (rget A7 a5_idx) (sign_extend' 64 (sign_extend' 12 (mword_of_int 2 : mword 6))))]> A7) with A8.
    assert (HA8sp : A8 !!! Regidx csp_rs1 = pa_stk (m !!! Regidx csp_rs1) 6)
      by (rewrite /A8 upd_ne; [exact HA7sp | vm_compute; discriminate]).
    assert (HA8s1 : A8 !!! Regidx s1_idx = sstatus_read ms0)
      by (rewrite /A8 upd_ne; [exact HA7s1 | vm_compute; discriminate]).
    assert (HA8s2 : A8 !!! Regidx s2_idx = ep)
      by (rewrite /A8 upd_ne; [exact HA7s2 | vm_compute; discriminate]).
    assert (Hpc28 : add_vec_int (mword_of_int (KernelSyms.kerneltrap + 0x26) : mword 64) 2
                    = mword_of_int (KernelSyms.kerneltrap + 0x28)) by pcw.
    iEval (rewrite Hpc28) in "Hpc".
    (* ---- +0x28: c.bnez a5 -> panic("interrupts enabled").  DEAD: the fresh
       read has SIE = 0, off the [b = false] arm index. ---- *)
    assert (HA7a5 : rget A7 a5_idx = sstatus_read ms1)
      by (rgne; rewrite /A7; apply upd_eq).
    iPoseProof (kti_28 with "Htext") as "Hi28".
    iApply (wp_cbnez_fall_s_sconf (mword_of_int (KernelSyms.kerneltrap + 0x28))
              (mword_of_int 24 : mword 8) (Cregidx (mword_of_int 7)) a5_idx
              A8 (av - 6)%nat false
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
              ltac:(rgne; rewrite /A8 upd_eq; unfold regval_into_reg;
                    rewrite HA7a5;
                    exact (pop_sstatus_clear_neq ms1
                             ltac:(rewrite Hsie1; vm_compute; reflexivity)))
              with "Hcg Hpc Hi28").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    assert (Hpc2a : add_vec_int (mword_of_int (KernelSyms.kerneltrap + 0x28) : mword 64) 2
                    = mword_of_int (KernelSyms.kerneltrap + 0x2a)) by pcw.
    iEval (rewrite Hpc2a) in "Hpc".
    (* ---- hand over to the functor at the [jal devintr] ---- *)
    iApply ("Hcont" $! A8 ms0 with "[%] [%] [%] [%] [%] [%] [%] [%]
                          Hcg Hmir Hsepc Hscause Hpc Hb1 Hb2 Hb3 Hb4 Hb5 S6").
    { exact HA8sp. }
    { exact HA8s2. }
    { exact HA8s1. }
    { exact Hms0f. }
    { exact Hsie0. }
    { exact Hspp0. }
    { exact Hspie0. }
    { intros r Hr Hsp Hs0 Hs1 Hs2 Hs3.
      rewrite /A8 upd_ne; [| ktne_a5 ].
      rewrite /A7 upd_ne; [| ktne_a5 ].
      rewrite /A6 upd_ne; [| ktne_a5 ].
      rewrite /A5 upd_ne; [| congruence ].
      rewrite /A4 upd_ne; [| ktne_a5 ].
      rewrite /A3 upd_ne; [| congruence ].
      rewrite /A2 upd_ne; [| congruence ].
      rewrite /A1 upd_ne; [| congruence ].
      rewrite /A0 upd_ne; [| congruence ].
      reflexivity. }
  Qed.


  (* ================================================================== *)
  (* THE COMMON EPILOGUE (kerneltrap+0x36 .. +0x4a).                     *)
  (* ================================================================== *)
  Lemma kt_epi
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
        WP (Loop : expr riscv_lang) ) -∗
    WP (Loop : expr riscv_lang).
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
    iApply (wp_csrw_sepc_s_sconf (mword_of_int (KernelSyms.kerneltrap + 0x36)) s2_idx
              M k epold ep
              ltac:(vm_compute; discriminate) ltac:(rgne; exact HMs2)
              with "Hcg Hsepc Hpc Hi36").
    iApply wp_next_off_intro. iIntros "Hcg Hsepc Hpc".
    iEval (rewrite (_ : mepc_val ep = ep); [| exact Hepal ]) in "Hsepc".
    assert (Hpc3a : add_vec_int (mword_of_int (KernelSyms.kerneltrap + 0x36) : mword 64) 4
                    = mword_of_int (KernelSyms.kerneltrap + 0x3a)) by pcw.
    iEval (rewrite Hpc3a) in "Hpc".
    (* ---- +0x3a: csrw sstatus,s1 -- restore the trapped sstatus.  THE one
       instruction that moves SPP/SPIE, so it takes the mirror. ---- *)
    iPoseProof (kti_3a with "Htext") as "Hi3a".
    iApply (wp_csrw_sstatus_s_sconf (mword_of_int (KernelSyms.kerneltrap + 0x3a)) s1_idx
              M k ms0 va vb
              ltac:(vm_compute; discriminate) ltac:(rgne; exact HMs1) Hms0f
              ltac:(cbn [sie_bit]; exact Hsie0)
              with "Hcg Hmir Hpc Hi3a").
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
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.kerneltrap + 0x3e)) (mword_of_int 5 : mword 6) ra_idx
              M k ra0 false (dqm := DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi3e Hb1").
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
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.kerneltrap + 0x40)) (mword_of_int 4 : mword 6) s0_idx
              E1 k s00 false (dqm := DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi40 Hb2").
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
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.kerneltrap + 0x42)) (mword_of_int 3 : mword 6) s1_idx
              E2 k s10 false (dqm := DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi42 Hb3").
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
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.kerneltrap + 0x44)) (mword_of_int 2 : mword 6) s2_idx
              E3 k s20 false (dqm := DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi44 Hb4").
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
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.kerneltrap + 0x46)) (mword_of_int 1 : mword 6) s3_idx
              E4 k s30 false (dqm := DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi46 Hb5").
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
    iApply (wp_caddi16sp_pop_s_sconf (mword_of_int (KernelSyms.kerneltrap + 0x48))
              (mword_of_int 3 : mword 6) E5 k 6 false Hpop
              with "Hcg Hpc Hi48 Hframe6").
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
    iApply (wp_cret_s_sconf (mword_of_int (KernelSyms.kerneltrap + 0x4a)) ra_idx
              E6 (k + 6) false ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi4a").
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
