(* ProofSched.v -- the whole-function sconf-tier proof of sched()
   (SpecSched.v), as a sealed functor over its callees' interfaces
   (myproc, holding, swtch).  See claude-notes/projects/yield-sched.md. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExtras.
Require Import WpMmodeLeafBase.
Require Import RegFile.
Require Import SmodeCore.
Require Import StackOwn CalleeSaved.
Require Import IntrDefs WpSmodeIntr.
Require Import WpSconfAlu WpSconfMem WpSconfCtl WpSconfBtype WpSconfCsr.
Require Import WpLock.
Require Import WpMycpu.
Require Import WpAuipc.
Require Import FdSlots.
Require Import ProcGeom.
Require Import SwtchCtx.
Require Import CpuOwn.
Require Import SchedCtx.
Require Import WpGprCsrwCommon.
Require WpGprCsrwC.
Require Import WpSchedDecode.
Require Import SpecMyproc SpecHolding SpecSwtch SpecSched.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Import Defs.
Local Open Scope Z_scope.

(* ===================================================================== *)
(* Pure helpers: address arithmetic + the SIE-bit fact.                   *)
(* ===================================================================== *)

Lemma sched_addv_unsigned (x y : mword 64) :
  bv_unsigned (add_vec x y) = bv_wrap 64 (bv_unsigned x + bv_unsigned y).
Proof.
  unfold add_vec, Operators_mwords.word_binop, Operators_mwords.with_word',
    SailStdpp.Values.with_word, to_word, get_word, MachineWord.MachineWord.add.
  rewrite bv_add_unsigned. reflexivity.
Qed.

Lemma sched_addvC (x y : mword 64) : add_vec x y = add_vec y x.
Proof.
  apply bv_eq. rewrite !sched_addv_unsigned. rewrite Z.add_comm. reflexivity.
Qed.

Lemma sched_addvA (x y z : mword 64) : add_vec (add_vec x y) z = add_vec x (add_vec y z).
Proof.
  apply bv_eq. rewrite !sched_addv_unsigned.
  rewrite bv_wrap_add_idemp_l bv_wrap_add_idemp_r Z.add_assoc. reflexivity.
Qed.

Lemma sched_addv_zero_l (x : mword 64) : add_vec zero_reg x = x.
Proof.
  apply bv_eq. rewrite sched_addv_unsigned.
  assert (Hz : bv_unsigned (zero_reg : mword 64) = 0) by (vm_compute; reflexivity).
  rewrite Hz Z.add_0_l. apply bv_wrap_bv_unsigned.
Qed.

(* the workhorse address reconciliation: pulling the (symbolic) shift term
   [sh] out front on both sides leaves a CLOSED constant equality. *)
Lemma sched_reconcile (sh a b c d : mword 64) :
  bv_unsigned (add_vec a b) = bv_unsigned (add_vec c d) ->
  add_vec (add_vec sh a) b = add_vec (add_vec sh c) d.
Proof.
  intro H. rewrite sched_addv_unsigned in H. rewrite (sched_addv_unsigned c d) in H.
  apply bv_eq.
  rewrite (sched_addv_unsigned (add_vec sh a) b) (sched_addv_unsigned sh a).
  rewrite (sched_addv_unsigned (add_vec sh c) d) (sched_addv_unsigned sh c).
  rewrite !bv_wrap_add_idemp_l.
  rewrite <- !Z.add_assoc.
  rewrite <- (bv_wrap_add_idemp_r 64 (bv_unsigned sh) (bv_unsigned a + bv_unsigned b)).
  rewrite <- (bv_wrap_add_idemp_r 64 (bv_unsigned sh) (bv_unsigned c + bv_unsigned d)).
  rewrite H. reflexivity.
Qed.

(* a variant where the shift sits INSIDE the right factor of the left side. *)
Lemma sched_reconcile2 (sh a b c d : mword 64) :
  bv_unsigned (add_vec a b) = bv_unsigned (add_vec c d) ->
  add_vec a (add_vec sh b) = add_vec (add_vec c sh) d.
Proof.
  intro H.
  rewrite (sched_addvC sh b). rewrite <- (sched_addvA a b sh).
  rewrite (sched_addvC (add_vec a b) sh).
  rewrite (sched_addvC c sh). rewrite (sched_addvA sh c d).
  assert (Hab : add_vec a b = add_vec c d) by (apply bv_eq; exact H).
  rewrite Hab. reflexivity.
Qed.

(* a saved-register frame slot address in terms of the pushed sp. *)
Lemma sched_frame_bridge (sp0 : mword 64) (j : nat) (uimm : mword 6) :
  bv_unsigned (add_vec (sign_extend' 64 (caddi16sp_imm (mword_of_int 61 : mword 6)))
                       (zero_extend' 64 (concat_vec uimm ('b"000"))) : mword 64)
    = bv_wrap 64 (- (8 * Z.of_nat j)) ->
  pa_stk sp0 j
    = add_vec (add_vec sp0 (sign_extend' 64 (caddi16sp_imm (mword_of_int 61 : mword 6))))
              (zero_extend' 64 (concat_vec uimm ('b"000"))).
Proof.
  intro H.
  assert (Heq : add_vec (sign_extend' 64 (caddi16sp_imm (mword_of_int 61 : mword 6)))
                        (zero_extend' 64 (concat_vec uimm ('b"000")))
                = (mword_of_int (- (8 * Z.of_nat j)) : mword 64)).
  { apply bv_eq. rewrite H.
    unfold mword_of_int, Values.to_word, get_word. cbn.
    rewrite Z_to_bv_unsigned. reflexivity. }
  unfold pa_stk, add_vec_int. rewrite sched_addvA. rewrite Heq. reflexivity.
Qed.

Lemma sched_sstatus_clear (ms : mword 64) :
  eq_vec (_get_Mstatus_SIE ms) ('b"1") = false ->
  neq_vec (and_vec (sstatus_read ms)
             (sign_extend' 64 (sign_extend' 12 (mword_of_int 2 : mword 6)))) zero_reg = false.
Proof.
  intro HSIE.
  unfold neq_vec. apply negb_false_iff. apply eq_vec_true_iff.
  assert (Hz : _get_Mstatus_SIE ms = ('b"0" : mword 1))
    by (apply mword1_zero_of_ne_one; exact HSIE).
  assert (Hb1 : Z.testbit (bv_unsigned (sstatus_read ms)) 1 = false).
  { unfold sstatus_read. rewrite WpGprCsrwC.subrange_full.
    apply WpGprCsrwC.sie_bit. rewrite WpGprCsrwC.mSIE_lower. exact Hz. }
  assert (Hmask : bv_unsigned (sign_extend' 64 (sign_extend' 12 (mword_of_int 2 : mword 6)) : mword 64) = 2)
    by (vm_compute; reflexivity).
  assert (Hzr : bv_unsigned (zero_reg : mword 64) = 0) by (vm_compute; reflexivity).
  apply bv_eq. rewrite WpGprCsrwC.and_vec_unsigned. rewrite Hmask. rewrite Hzr.
  apply Z.bits_inj'. intros j Hj. rewrite Z.land_spec. rewrite Z.bits_0.
  destruct (decide (j = 1)) as [->|Hne].
  - rewrite Hb1. reflexivity.
  - assert (Ht2 : Z.testbit 2 j = false).
    { destruct (Z.eq_dec j 0) as [->|Hj0].
      - reflexivity.
      - apply Z.bits_above_log2; [lia|]. change (Z.log2 2) with 1. lia. }
    rewrite Ht2. apply andb_false_r.
Qed.

Module SchedProof (Myproc : MYPROC) (Holding : HOLDING) (Swtch : SWTCH) : SCHED.

Section ProofSched.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ}.
  Context `{CID : CpuId}.

  Lemma wp_sched_sconf (γ : gname) (Φ : mval -> iProp Σ)
      (γs : list gname) (j : nat) (γl : gname) (st : mword 32) (ch : mword 64)
      (m : regfile) (av : nat) (eb : bool)
    : wp_sched_sconf_body γ Φ γs j γl st ch m av eb.
  Proof.
    cbv beta delta [wp_sched_sconf_body].
    intros pcE pj ret_tgt Htp Hj Hgl Hneeds Hav.
    pose (sp0 := (m !!! Regidx csp_rs1 : mword 64)).
    iIntros "Hcg #Htext Hpc #Hprocs Hheld Hcpu Hown Hvc Hcont".
    (* the cpu bundle [cpu_own γ 1 eb pj emp] arrives whole at level 1; unfold
       it to the individual cells + counting token the check-chain threads. *)
    iDestruct "Hheld" as "(Hlocked & Hstate & Hchan & Hpub)".
    (* a persistent copy of the level-1 handler-avail payload (needed only when
       the saved base enable [eb] is true) for the return-path retune. *)
    iAssert (cpu_own γ 1 eb (proc_addr j) emp ∗
             □ (if eb then intr_handler_avail γ else emp))%I
      with "[Hcpu]" as "(Hcpu & #Havail_eb)".
    { destruct eb.
      - iEval (rewrite /cpu_own /intr_count /=) in "Hcpu".
        iDestruct "Hcpu" as "(%Hb & Hnoff & Hint & [Hq0 #Hav] & Hcur & _)".
        iSplitR "".
        2:{ iModIntro. iExact "Hav". }
        rewrite /cpu_own /intr_count /=. iFrame "Hnoff Hint Hcur".
        iSplitR; [iPureIntro; exact Hb |]. iFrame "Hq0". iExact "Hav".
      - iFrame "Hcpu". iModIntro. done. }
    iDestruct "Hown" as (ctxvs) "[%Hctxlen Hctxcells]".
    (* ------------------------------------------------------------------ *)
    (* Prologue: 48-byte frame (push 6), save ra/s0/s1/s2/s3.             *)
    (* ------------------------------------------------------------------ *)
    set (spd := add_vec sp0 (sign_extend' 64 (caddi16sp_imm (mword_of_int 61 : mword 6)))).
    iPoseProof (sdi_00 with "Htext") as "Hi00".
    assert (Hpush : add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 61 : mword 6)))
                    = pa_stk (m !!! Regidx csp_rs1) 6).
    { unfold pa_stk, add_vec_int. apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    iApply (wp_caddi16sp_push_s_sconf γ Φ pcE (mword_of_int 61 : mword 6) m av 6
              ltac:(lia) Hpush with "Hcg Hpc Hi00 [-]").
    iIntros "Hcg Hframe Hpc".
    set (A0 := <[Regidx csp_rs1 := regval_into_reg
        (add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 61 : mword 6))))]> m).
    change (<[Regidx csp_rs1 := regval_into_reg
        (add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 61 : mword 6))))]> m) with A0.
    assert (HcspA0 : A0 !!! Regidx csp_rs1 = spd) by (rewrite /A0 upd_eq; reflexivity).
    assert (Hpc02 : add_vec_int (pcE : mword 64) 2 = mword_of_int (SD + 0x02)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc02) in "Hpc".
    (* split the 6-slot frame into cells. *)
    iEval (rewrite stack_own_slots; cbn [seq]) in "Hframe".
    iDestruct "Hframe" as "(S1c & S2c & S3c & S4c & S5c & S6c & _)".
    iDestruct "S1c" as (vr1) "Hr1". iDestruct "S2c" as (vr2) "Hr2".
    iDestruct "S3c" as (vr3) "Hr3". iDestruct "S4c" as (vr4) "Hr4".
    iDestruct "S5c" as (vr5) "Hr5". iDestruct "S6c" as (vgap) "Hgap".
    assert (Hb1 : pa_stk sp0 1 = add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000"))))
      by (apply sched_frame_bridge; vm_compute; reflexivity).
    assert (Hb2 : pa_stk sp0 2 = add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000"))))
      by (apply sched_frame_bridge; vm_compute; reflexivity).
    assert (Hb3 : pa_stk sp0 3 = add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000"))))
      by (apply sched_frame_bridge; vm_compute; reflexivity).
    assert (Hb4 : pa_stk sp0 4 = add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000"))))
      by (apply sched_frame_bridge; vm_compute; reflexivity).
    assert (Hb5 : pa_stk sp0 5 = add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))))
      by (apply sched_frame_bridge; vm_compute; reflexivity).
    (* +0x02 c.sdsp ra,40 *)
    iPoseProof (sdi_02 with "Htext") as "Hi02".
    iApply (wp_csdsp_s_sconf γ Φ (mword_of_int (SD + 0x02)) (mword_of_int 5 : mword 6) (mword_of_int 1 : mword 5)
              A0 (av - 6)%nat vr1 with "Hcg Hpc Hi02 [Hr1] [-]").
    { iEval (rewrite HcspA0 -Hb1). iExact "Hr1". }
    iIntros "Hcg Hpc Hr1".
    assert (Hpc04 : add_vec_int (mword_of_int (SD + 0x02) : mword 64) 2 = mword_of_int (SD + 0x04)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc04) in "Hpc".
    (* +0x04 c.sdsp s0,32 *)
    iPoseProof (sdi_04 with "Htext") as "Hi04".
    iApply (wp_csdsp_s_sconf γ Φ (mword_of_int (SD + 0x04)) (mword_of_int 4 : mword 6) (mword_of_int 8 : mword 5)
              A0 (av - 6)%nat vr2 with "Hcg Hpc Hi04 [Hr2] [-]").
    { iEval (rewrite HcspA0 -Hb2). iExact "Hr2". }
    iIntros "Hcg Hpc Hr2".
    assert (Hpc06 : add_vec_int (mword_of_int (SD + 0x04) : mword 64) 2 = mword_of_int (SD + 0x06)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc06) in "Hpc".
    (* +0x06 c.sdsp s1,24 *)
    iPoseProof (sdi_06 with "Htext") as "Hi06".
    iApply (wp_csdsp_s_sconf γ Φ (mword_of_int (SD + 0x06)) (mword_of_int 3 : mword 6) (mword_of_int 9 : mword 5)
              A0 (av - 6)%nat vr3 with "Hcg Hpc Hi06 [Hr3] [-]").
    { iEval (rewrite HcspA0 -Hb3). iExact "Hr3". }
    iIntros "Hcg Hpc Hr3".
    assert (Hpc08 : add_vec_int (mword_of_int (SD + 0x06) : mword 64) 2 = mword_of_int (SD + 0x08)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc08) in "Hpc".
    (* +0x08 c.sdsp s2,16 *)
    iPoseProof (sdi_08 with "Htext") as "Hi08".
    iApply (wp_csdsp_s_sconf γ Φ (mword_of_int (SD + 0x08)) (mword_of_int 2 : mword 6) (mword_of_int 18 : mword 5)
              A0 (av - 6)%nat vr4 with "Hcg Hpc Hi08 [Hr4] [-]").
    { iEval (rewrite HcspA0 -Hb4). iExact "Hr4". }
    iIntros "Hcg Hpc Hr4".
    assert (Hpc0a : add_vec_int (mword_of_int (SD + 0x08) : mword 64) 2 = mword_of_int (SD + 0x0a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc0a) in "Hpc".
    (* +0x0a c.sdsp s3,8 *)
    iPoseProof (sdi_0a with "Htext") as "Hi0a".
    iApply (wp_csdsp_s_sconf γ Φ (mword_of_int (SD + 0x0a)) (mword_of_int 1 : mword 6) (mword_of_int 19 : mword 5)
              A0 (av - 6)%nat vr5 with "Hcg Hpc Hi0a [Hr5] [-]").
    { iEval (rewrite HcspA0 -Hb5). iExact "Hr5". }
    iIntros "Hcg Hpc Hr5".
    assert (Hpc0c : add_vec_int (mword_of_int (SD + 0x0a) : mword 64) 2 = mword_of_int (SD + 0x0c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc0c) in "Hpc".
    (* +0x0c c.addi4spn s0,sp,48 *)
    iPoseProof (sdi_0c with "Htext") as "Hi0c".
    iApply (wp_caddi4spn_s_sconf γ Φ (mword_of_int (SD + 0x0c)) (Cregidx (mword_of_int 0)) (mword_of_int 12 : mword 8) (mword_of_int 8 : mword 5)
              A0 (av - 6)%nat ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi0c [-]").
    iIntros "Hcg Hpc".
    set (A1 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg
        (add_vec (A0 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 12 : mword 8))))]> A0).
    change (<[Regidx (mword_of_int 8 : mword 5) := regval_into_reg
        (add_vec (A0 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 12 : mword 8))))]> A0) with A1.
    assert (Hpc0e : add_vec_int (mword_of_int (SD + 0x0c) : mword 64) 2 = mword_of_int (SD + 0x0e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc0e) in "Hpc".
    (* +0x0e jal myproc *)
    iPoseProof (sdi_0e with "Htext") as "Hi0e".
    iApply (wp_jal_s_sconf γ Φ (mword_of_int (SD + 0x0e)) (mword_of_int 1 : mword 5) (mword_of_int 2095832 : mword 21)
              A1 (av - 6)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi0e [-]").
    iIntros "Hcg Hpc".
    set (A2 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (SD + 0x0e) : mword 64) 4)]> A1).
    change (<[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (SD + 0x0e) : mword 64) 4)]> A1) with A2.
    assert (Hpcmp : add_vec (mword_of_int (SD + 0x0e) : mword 64) (sign_extend' 64 (mword_of_int 2095832 : mword 21))
                    = mword_of_int KernelSyms.myproc) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpcmp) in "Hpc".
    (* ------------------------------------------------------------------ *)
    (* +0x0e: myproc() -- returns a0 = proc_addr j; noff/intena untouched. *)
    (* ------------------------------------------------------------------ *)
    assert (HA2ra : A2 !!! Regidx (mword_of_int 1 : mword 5) = add_vec_int (mword_of_int (SD + 0x0e) : mword 64) 4)
      by (rewrite /A2 upd_eq; reflexivity).
    assert (HtpA2 : A2 !!! Regidx (mword_of_int 4 : mword 5) = cid_word).
    { rewrite /A2 upd_ne; [| vm_compute; discriminate].
      rewrite /A1 upd_ne; [| vm_compute; discriminate].
      rewrite /A0 upd_ne; [| vm_compute; discriminate]. exact Htp. }
    iApply (Myproc.wp_myproc_sconf γ Φ A2 (av - 6)%nat 1 eb (proc_addr j) emp
              HtpA2
              ltac:(vm_compute; reflexivity)
              ltac:(lia)
              with "Hcg Hcpu Htext Hpc [-]").
    iIntros (ms mp) "%Hmsf Hcg Hcpu Hpc %Hmp".
    destruct Hmp as [Hcs_mp Ha0_mp].
    (* re-unfold the (unchanged) returned bundle into the individual cells the
       check-chain reads, and name the level-1 intena value. *)
    iEval (rewrite /cpu_own) in "Hcpu".
    iDestruct "Hcpu" as "(_ & Hnoff & Hint & Hcnt & Hcur & _)".
    set (iv := intena_val eb : mword 32).
    assert (Hpc12 : ret_pc (A2 !!! Regidx (mword_of_int 1 : mword 5))
                    = mword_of_int (SD + 0x12)) by (rewrite HA2ra; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc12) in "Hpc".
    (* +0x12 c.mv s1,a0 : s1 := a0 = proc_addr j *)
    iPoseProof (sdi_12 with "Htext") as "Hi12".
    iApply (wp_cmv_s_sconf γ Φ (mword_of_int (SD + 0x12)) (mword_of_int 9 : mword 5) (mword_of_int 10 : mword 5)
              mp (av - 6)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi12 [-]").
    iIntros "Hcg Hpc".
    set (B0 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg
        (add_vec zero_reg (mp !!! Regidx (mword_of_int 10 : mword 5)))]> mp).
    change (<[Regidx (mword_of_int 9 : mword 5) := regval_into_reg
        (add_vec zero_reg (mp !!! Regidx (mword_of_int 10 : mword 5)))]> mp) with B0.
    assert (Hpc14 : add_vec_int (mword_of_int (SD + 0x12) : mword 64) 2 = mword_of_int (SD + 0x14)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc14) in "Hpc".
    (* +0x14 jal holding *)
    iPoseProof (sdi_14 with "Htext") as "Hi14".
    iApply (wp_jal_s_sconf γ Φ (mword_of_int (SD + 0x14)) (mword_of_int 1 : mword 5) (mword_of_int 2092400 : mword 21)
              B0 (av - 6)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi14 [-]").
    iIntros "Hcg Hpc".
    set (B1 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (SD + 0x14) : mword 64) 4)]> B0).
    change (<[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (SD + 0x14) : mword 64) 4)]> B0) with B1.
    assert (Hpchd : add_vec (mword_of_int (SD + 0x14) : mword 64) (sign_extend' 64 (mword_of_int 2092400 : mword 21))
                    = mword_of_int KernelSyms.holding) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpchd) in "Hpc".
    (* ------------------------------------------------------------------ *)
    (* +0x14: holding(&p->lock) -- locked, so a0 := 1.                     *)
    (* ------------------------------------------------------------------ *)
    (* a0 is still proc_addr j (myproc's return, unmodified by c.mv/jal). *)
    assert (Ha0_B1 : B1 !!! Regidx (mword_of_int 10 : mword 5) = proc_addr j).
    { rewrite /B1 upd_ne; [| vm_compute; discriminate].
      rewrite /B0 upd_ne; [| vm_compute; discriminate]. exact Ha0_mp. }
    assert (HtpB1 : B1 !!! Regidx (mword_of_int 4 : mword 5) = cid_word).
    { rewrite /B1 upd_ne; [| vm_compute; discriminate].
      rewrite /B0 upd_ne; [| vm_compute; discriminate].
      rewrite (callee_saved_lookup Hcs_mp (mword_of_int 4) ltac:(vm_compute; reflexivity)). exact HtpA2. }
    iPoseProof (procs_inv_lookup γ Φ γs j γl Hgl with "Hprocs") as "#Hislock".
    assert (Hlkb : add_vec (B1 !!! Regidx (mword_of_int 10 : mword 5)) (sign_extend' 64 (mword_of_int 0 : mword 12)) = proc_addr j).
    { rewrite Ha0_B1.
      assert (H0 : sign_extend' 64 (mword_of_int 0 : mword 12) = (mword_of_int 0 : mword 64)) by (apply bv_eq; vm_compute; reflexivity).
      rewrite H0. apply kv_addv_zero. }
    assert (HB1ra : B1 !!! Regidx (mword_of_int 1 : mword 5) = add_vec_int (mword_of_int (SD + 0x14) : mword 64) 4)
      by (rewrite /B1 upd_eq; reflexivity).
    iApply (Holding.wp_holding_lockinv_locked_s_sconf γ Φ γl (proc_addr j)
              (proc_lock_res γ Φ γs γl (proc_addr j)) False%I B1 (av - 6)%nat
              Hlkb HtpB1 ltac:(lia) (lock_refute_False _)
              with "Hcg Htext Hpc [] Hlocked [-]").
    { iApply (is_lock_openable with "Hislock"). }
    iIntros (mh) "Hcg Hpc %Hmh Hlocked".
    destruct Hmh as [Hcs_mh Ha0_mh].
    assert (Hpc18 : ret_pc (add_vec_int (mword_of_int (SD + 0x14) : mword 64) 4)
                    = mword_of_int (SD + 0x18)) by (apply bv_eq; vm_compute; reflexivity).
    (* pc after holding = ret_tgt = ret_pc(B1!!!x1) = SD+0x18. *)
    iEval (rewrite HB1ra Hpc18) in "Hpc".
    (* +0x18 c.beqz a0 : a0 = 1, falls through. *)
    iPoseProof (sdi_18 with "Htext") as "Hi18".
    assert (Ha0_beqz : eq_vec (mh !!! Regidx (mword_of_int 10 : mword 5)) zero_reg = false)
      by (rewrite Ha0_mh; vm_compute; reflexivity).
    iApply (wp_cbeqz_fall_s_sconf γ Φ (mword_of_int (SD + 0x18)) (mword_of_int 58 : mword 8) (Cregidx (mword_of_int 2)) (mword_of_int 10 : mword 5)
              mh (av - 6)%nat ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) Ha0_beqz
              with "Hcg Hpc Hi18 [-]").
    iIntros "Hcg Hpc".
    assert (Hpc1a : add_vec_int (mword_of_int (SD + 0x18) : mword 64) 2 = mword_of_int (SD + 0x1a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc1a) in "Hpc".
    (* tp and s1 threaded through holding. *)
    assert (Htp_mh : mh !!! Regidx (mword_of_int 4 : mword 5) = cid_word)
      by (rewrite (callee_saved_lookup Hcs_mh (mword_of_int 4) ltac:(vm_compute; reflexivity)); exact HtpB1).
    assert (Hs1_mh : mh !!! Regidx (mword_of_int 9 : mword 5) = add_vec zero_reg (proc_addr j)).
    { rewrite (callee_saved_lookup Hcs_mh (mword_of_int 9) ltac:(vm_compute; reflexivity)).
      rewrite /B1 upd_ne; [| vm_compute; discriminate]. rewrite /B0 upd_eq Ha0_mp. reflexivity. }
    (* ------------------------------------------------------------------ *)
    (* +0x1a..+0x30: read mycpu()->noff (inlined) and check == 1.          *)
    (* ------------------------------------------------------------------ *)
    (* +0x1a c.mv a5,tp *)
    iPoseProof (sdi_1a with "Htext") as "Hi1a".
    iApply (wp_cmv_s_sconf γ Φ (mword_of_int (SD + 0x1a)) (mword_of_int 15 : mword 5) (mword_of_int 4 : mword 5)
              mh (av - 6)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi1a [-]").
    iIntros "Hcg Hpc".
    set (C0 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (add_vec zero_reg (mh !!! Regidx (mword_of_int 4 : mword 5)))]> mh).
    change (<[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (add_vec zero_reg (mh !!! Regidx (mword_of_int 4 : mword 5)))]> mh) with C0.
    assert (Hpc1c : add_vec_int (mword_of_int (SD + 0x1a) : mword 64) 2 = mword_of_int (SD + 0x1c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc1c) in "Hpc".
    (* +0x1c sext.w a5 *)
    iPoseProof (sdi_1c with "Htext") as "Hi1c".
    iApply (wp_caddiw_s_sconf γ Φ (mword_of_int (SD + 0x1c)) (mword_of_int 15 : mword 5) (mword_of_int 0 : mword 6)
              C0 (av - 6)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi1c [-]").
    iIntros "Hcg Hpc".
    set (C1 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg
        (sign_extend' 64 (subrange_vec_dec (add_vec (C0 !!! Regidx (mword_of_int 15 : mword 5)) (sign_extend' 64 (sign_extend' 12 (mword_of_int 0 : mword 6)))) 31 0))]> C0).
    change (<[Regidx (mword_of_int 15 : mword 5) := regval_into_reg
        (sign_extend' 64 (subrange_vec_dec (add_vec (C0 !!! Regidx (mword_of_int 15 : mword 5)) (sign_extend' 64 (sign_extend' 12 (mword_of_int 0 : mword 6)))) 31 0))]> C0) with C1.
    assert (Hpc1e : add_vec_int (mword_of_int (SD + 0x1c) : mword 64) 2 = mword_of_int (SD + 0x1e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc1e) in "Hpc".
    (* +0x1e c.slli a5,7 *)
    iPoseProof (sdi_1e with "Htext") as "Hi1e".
    iApply (wp_cslli_s_sconf γ Φ (mword_of_int (SD + 0x1e)) (Regidx (mword_of_int 15)) (mword_of_int 15 : mword 5) (mword_of_int 7 : mword 6)
              C1 (av - 6)%nat eq_refl ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi1e [-]").
    iIntros "Hcg Hpc".
    set (C2 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg
        (shift_bits_left (C1 !!! Regidx (mword_of_int 15 : mword 5)) (subrange_vec_dec (mword_of_int 7 : mword 6) (Z.sub log2_xlen 1) 0))]> C1).
    change (<[Regidx (mword_of_int 15 : mword 5) := regval_into_reg
        (shift_bits_left (C1 !!! Regidx (mword_of_int 15 : mword 5)) (subrange_vec_dec (mword_of_int 7 : mword 6) (Z.sub log2_xlen 1) 0))]> C1) with C2.
    assert (Hsh : C2 !!! Regidx (mword_of_int 15 : mword 5) = mycpu_a5 cid_word).
    { rewrite /C2 upd_eq /C1 upd_eq /C0 upd_eq Htp_mh. reflexivity. }
    assert (Hpc20 : add_vec_int (mword_of_int (SD + 0x1e) : mword 64) 2 = mword_of_int (SD + 0x20)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc20) in "Hpc".
    (* +0x20 auipc a4,0x10 *)
    iPoseProof (sdi_20 with "Htext") as "Hi20".
    iApply (wp_auipc_s_sconf γ Φ (mword_of_int (SD + 0x20)) (mword_of_int 14 : mword 5) (mword_of_int 0x10 : mword 20)
              C2 (av - 6)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi20 [-]").
    iIntros "Hcg Hpc".
    set (C3 := <[Regidx (mword_of_int 14 : mword 5) := regval_into_reg (add_vec (mword_of_int (SD + 0x20) : mword 64) (auipc_off (mword_of_int 0x10 : mword 20)))]> C2).
    change (<[Regidx (mword_of_int 14 : mword 5) := regval_into_reg (add_vec (mword_of_int (SD + 0x20) : mword 64) (auipc_off (mword_of_int 0x10 : mword 20)))]> C2) with C3.
    assert (Hpc24 : add_vec_int (mword_of_int (SD + 0x20) : mword 64) 4 = mword_of_int (SD + 0x24)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc24) in "Hpc".
    (* +0x24 addi a4,a4,1290 *)
    iPoseProof (sdi_24 with "Htext") as "Hi24".
    iApply (wp_addi4_s_sconf γ Φ (mword_of_int (SD + 0x24)) (mword_of_int 14 : mword 5) (mword_of_int 14 : mword 5) (mword_of_int 0x50a : mword 12)
              C3 (av - 6)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi24 [-]").
    iIntros "Hcg Hpc".
    set (C4 := <[Regidx (mword_of_int 14 : mword 5) := regval_into_reg (add_vec (C3 !!! Regidx (mword_of_int 14 : mword 5)) (sign_extend' 64 (mword_of_int 0x50a : mword 12)))]> C3).
    change (<[Regidx (mword_of_int 14 : mword 5) := regval_into_reg (add_vec (C3 !!! Regidx (mword_of_int 14 : mword 5)) (sign_extend' 64 (mword_of_int 0x50a : mword 12)))]> C3) with C4.
    assert (Hpc28 : add_vec_int (mword_of_int (SD + 0x24) : mword 64) 4 = mword_of_int (SD + 0x28)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc28) in "Hpc".
    (* +0x28 c.add a5,a5,a4 *)
    iPoseProof (sdi_28 with "Htext") as "Hi28".
    iApply (wp_cadd_s_sconf γ Φ (mword_of_int (SD + 0x28)) (mword_of_int 15 : mword 5) (mword_of_int 14 : mword 5)
              C4 (av - 6)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi28 [-]").
    iIntros "Hcg Hpc".
    set (C5 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (add_vec (C4 !!! Regidx (mword_of_int 15 : mword 5)) (C4 !!! Regidx (mword_of_int 14 : mword 5)))]> C4).
    change (<[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (add_vec (C4 !!! Regidx (mword_of_int 15 : mword 5)) (C4 !!! Regidx (mword_of_int 14 : mword 5)))]> C4) with C5.
    assert (Hpc2a : add_vec_int (mword_of_int (SD + 0x28) : mword 64) 2 = mword_of_int (SD + 0x2a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc2a) in "Hpc".
    (* +0x2a lw a4,168(a5) : reconcile to a_cpu_noff *)
    assert (Hrec_noff : add_vec (C5 !!! Regidx (mword_of_int 15 : mword 5)) (sign_extend' 64 (mword_of_int 168 : mword 12))
                        = a_cpu_noff cid_word).
    { assert (HC5v : C5 !!! Regidx (mword_of_int 15 : mword 5)
                     = add_vec (mycpu_a5 cid_word)
                         (add_vec (add_vec (mword_of_int (SD + 0x20) : mword 64) (auipc_off (mword_of_int 0x10 : mword 20)))
                                  (sign_extend' 64 (mword_of_int 0x50a : mword 12)))).
      { rewrite /C5 upd_eq.
        rewrite (_ : C4 !!! Regidx (mword_of_int 15 : mword 5) = mycpu_a5 cid_word).
        2:{ rewrite /C4 upd_ne; [| vm_compute; discriminate]. rewrite /C3 upd_ne; [| vm_compute; discriminate]. exact Hsh. }
        rewrite (_ : C4 !!! Regidx (mword_of_int 14 : mword 5)
                     = add_vec (add_vec (mword_of_int (SD + 0x20) : mword 64) (auipc_off (mword_of_int 0x10 : mword 20))) (sign_extend' 64 (mword_of_int 0x50a : mword 12))).
        2:{ rewrite /C4 upd_eq /C3 upd_eq. reflexivity. }
        reflexivity. }
      rewrite HC5v.
      unfold a_cpu_noff, mycpu_ret.
      rewrite (sched_addvC _ (mycpu_a5 cid_word)).
      apply sched_reconcile. vm_compute. reflexivity. }
    iPoseProof (sdi_2a with "Htext") as "Hi2a".
    iApply (wp_lw_s_sconf γ Φ (mword_of_int (SD + 0x2a)) (mword_of_int 14 : mword 5) (mword_of_int 15 : mword 5)
              (mword_of_int 168 : mword 12) C5 (av - 6)%nat (mword_of_int 1 : mword 32)
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi2a [Hnoff] [-]").
    { iEval (rewrite Hrec_noff). iExact "Hnoff". }
    iIntros "Hcg Hpc Hnoff".
    iEval (rewrite Hrec_noff) in "Hnoff".
    set (C6 := <[Regidx (mword_of_int 14 : mword 5) := regval_into_reg (sign_extend' 64 (mword_of_int 1 : mword 32))]> C5).
    change (<[Regidx (mword_of_int 14 : mword 5) := regval_into_reg (sign_extend' 64 (mword_of_int 1 : mword 32))]> C5) with C6.
    assert (Hpc2e : add_vec_int (mword_of_int (SD + 0x2a) : mword 64) 4 = mword_of_int (SD + 0x2e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc2e) in "Hpc".
    (* +0x2e c.li a5,1 *)
    iPoseProof (sdi_2e with "Htext") as "Hi2e".
    iApply (wp_cli_s_sconf γ Φ (mword_of_int (SD + 0x2e)) (mword_of_int 15 : mword 5) (mword_of_int 1 : mword 6)
              (add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6)))) C6 (av - 6)%nat
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) eq_refl
              with "Hcg Hpc Hi2e [-]").
    iIntros "Hcg Hpc".
    set (C7 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6))))]> C6).
    change (<[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6))))]> C6) with C7.
    assert (Hpc30 : add_vec_int (mword_of_int (SD + 0x2e) : mword 64) 2 = mword_of_int (SD + 0x30)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc30) in "Hpc".
    (* +0x30 bne a4,a5 : a4 = 1 = a5, falls through *)
    iPoseProof (sdi_30 with "Htext") as "Hi30".
    assert (Ha4C7 : C7 !!! Regidx (mword_of_int 14 : mword 5) = sign_extend' 64 (mword_of_int 1 : mword 32)).
    { rewrite /C7 upd_ne; [| vm_compute; discriminate]. rewrite /C6 upd_eq. reflexivity. }
    assert (Ha5C7 : C7 !!! Regidx (mword_of_int 15 : mword 5) = add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6))))
      by (rewrite /C7 upd_eq; reflexivity).
    iApply (wp_bne_fall_s_sconf γ Φ (mword_of_int (SD + 0x30)) (mword_of_int 104 : mword 13) (mword_of_int 15 : mword 5) (mword_of_int 14 : mword 5)
              C7 (av - 6)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha4C7 Ha5C7; vm_compute; reflexivity)
              with "Hcg Hpc Hi30 [-]").
    iIntros "Hcg Hpc".
    assert (Hpc34 : add_vec_int (mword_of_int (SD + 0x30) : mword 64) 4 = mword_of_int (SD + 0x34)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc34) in "Hpc".
    (* ------------------------------------------------------------------ *)
    (* +0x34..+0x38: read p->state and check != RUNNING.                   *)
    (* ------------------------------------------------------------------ *)
    (* +0x34 c.lw a4,24(s1) : reconcile to p_state (proc_addr j) *)
    assert (Hrec_state : add_vec (C7 !!! Regidx (mword_of_int 9 : mword 5)) (sign_extend' 64 (mword_of_int 24 : mword 12))
                         = p_state (proc_addr j)).
    { assert (HC7s1 : C7 !!! Regidx (mword_of_int 9 : mword 5) = add_vec zero_reg (proc_addr j)).
      { rewrite /C7 upd_ne; [| vm_compute; discriminate]. rewrite /C6 upd_ne; [| vm_compute; discriminate].
        rewrite /C5 upd_ne; [| vm_compute; discriminate]. rewrite /C4 upd_ne; [| vm_compute; discriminate].
        rewrite /C3 upd_ne; [| vm_compute; discriminate]. rewrite /C2 upd_ne; [| vm_compute; discriminate].
        rewrite /C1 upd_ne; [| vm_compute; discriminate]. rewrite /C0 upd_ne; [| vm_compute; discriminate].
        exact Hs1_mh. }
      rewrite HC7s1 sched_addv_zero_l. unfold p_state, state_off.
      assert (H24 : sign_extend' 64 (mword_of_int 24 : mword 12) = (mword_of_int 24 : mword 64)) by (apply bv_eq; vm_compute; reflexivity).
      rewrite H24. reflexivity. }
    iPoseProof (sdi_34 with "Htext") as "Hi34".
    iApply (wp_clw_s_sconf γ Φ (mword_of_int (SD + 0x34)) (mword_of_int 14 : mword 5) (mword_of_int 9 : mword 5)
              (mword_of_int 24 : mword 12) C7 (av - 6)%nat st
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi34 [Hstate] [-]").
    { iEval (rewrite Hrec_state). iExact "Hstate". }
    iIntros "Hcg Hpc Hstate".
    iEval (rewrite Hrec_state) in "Hstate".
    set (C8 := <[Regidx (mword_of_int 14 : mword 5) := regval_into_reg (sign_extend' 64 st)]> C7).
    change (<[Regidx (mword_of_int 14 : mword 5) := regval_into_reg (sign_extend' 64 st)]> C7) with C8.
    assert (Hpc36 : add_vec_int (mword_of_int (SD + 0x34) : mword 64) 2 = mword_of_int (SD + 0x36)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc36) in "Hpc".
    (* +0x36 c.li a5,4 *)
    iPoseProof (sdi_36 with "Htext") as "Hi36".
    iApply (wp_cli_s_sconf γ Φ (mword_of_int (SD + 0x36)) (mword_of_int 15 : mword 5) (mword_of_int 4 : mword 6)
              (add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 4 : mword 6)))) C8 (av - 6)%nat
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) eq_refl
              with "Hcg Hpc Hi36 [-]").
    iIntros "Hcg Hpc".
    set (C9 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 4 : mword 6))))]> C8).
    change (<[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 4 : mword 6))))]> C8) with C9.
    assert (Hpc38 : add_vec_int (mword_of_int (SD + 0x36) : mword 64) 2 = mword_of_int (SD + 0x38)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc38) in "Hpc".
    (* +0x38 beq a4,a5 : state != RUNNING (needs_ctx st), falls through *)
    iPoseProof (sdi_38 with "Htext") as "Hi38".
    assert (Ha4C9 : C9 !!! Regidx (mword_of_int 14 : mword 5) = sign_extend' 64 st).
    { rewrite /C9 upd_ne; [| vm_compute; discriminate]. rewrite /C8 upd_eq. reflexivity. }
    assert (Ha5C9 : C9 !!! Regidx (mword_of_int 15 : mword 5) = add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 4 : mword 6))))
      by (rewrite /C9 upd_eq; reflexivity).
    assert (Hbeq : eq_vec (sign_extend' 64 st) (add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 4 : mword 6)))) = false).
    { unfold needs_ctx in Hneeds. apply orb_prop in Hneeds. destruct Hneeds as [H|H];
        apply bool_decide_eq_true in H; subst st; vm_compute; reflexivity. }
    iApply (wp_beq_fall_s_sconf γ Φ (mword_of_int (SD + 0x38)) (mword_of_int 108 : mword 13) (mword_of_int 15 : mword 5) (mword_of_int 14 : mword 5)
              C9 (av - 6)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha4C9 Ha5C9; exact Hbeq)
              with "Hcg Hpc Hi38 [-]").
    iIntros "Hcg Hpc".
    assert (Hpc3c : add_vec_int (mword_of_int (SD + 0x38) : mword 64) 4 = mword_of_int (SD + 0x3c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc3c) in "Hpc".
    (* ------------------------------------------------------------------ *)
    (* +0x3c..+0x42: csrr sstatus; check SIE == 0.                         *)
    (* ------------------------------------------------------------------ *)
    iDestruct (intr_count_pos_off γ 0 with "Hcnt") as "[Hq0cnt Hres]".
    iPoseProof (sdi_3c with "Htext") as "Hi3c".
    iApply (wp_csrr_sstatus_s_sconf γ Φ (mword_of_int (SD + 0x3c)) (mword_of_int 15 : mword 5)
              C9 (av - 6)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi3c [-]").
    iIntros (ms2) "%Hmsf2 Hhs Hsc Htlbinv Hpc Hfile Hcapdisj".
    iDestruct "Hcapdisj" as "[Hstk Hdisj]".
    iAssert (⌜ _get_Mstatus_SIE ms2 = ('b"0" : mword 1) ⌝ ∗ sie_arm γ ∗ ghost_var γ (1/4/2)%Qp ('b"0" : mword 1))%I
      with "[Hdisj Hq0cnt]" as "(%HSIE0 & Harm & Hq0cnt)".
    { iDestruct "Hdisj" as "[[%HS Hq0arm] | (%HS & Hq1arm & Hrest)]".
      - iSplit; [done|]. iSplitL "Hq0arm"; [ iLeft; iExact "Hq0arm" | iExact "Hq0cnt" ].
      - iDestruct (ghost_var_agree with "Hq0cnt Hq1arm") as %Hbad.
        exfalso. apply (f_equal (@bv_unsigned _)) in Hbad. vm_compute in Hbad. discriminate. }
    iAssert (intr_count γ 1 eb) with "[Hq0cnt Hres]" as "Hcnt".
    { rewrite /intr_count. iFrame "Hq0cnt". iExact "Hres". }
    set (C10 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (sstatus_read ms2)]> C9).
    iDestruct (sie_cap_gpr_join γ C10 (av - 6)%nat with "Hhs Hsc [Hstk Htlbinv Harm] Hfile") as "Hcg".
    { rewrite /sie_cap. iFrame "Hstk Htlbinv Harm". }
    assert (Hpc40 : add_vec_int (mword_of_int (SD + 0x3c) : mword 64) 4 = mword_of_int (SD + 0x40)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc40) in "Hpc".
    (* +0x40 c.andi a5,a5,2 *)
    iPoseProof (sdi_40 with "Htext") as "Hi40".
    iApply (wp_candi_s_sconf γ Φ (mword_of_int (SD + 0x40)) (mword_of_int 15 : mword 5) (mword_of_int 2 : mword 6)
              C10 (av - 6)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi40 [-]").
    iIntros "Hcg Hpc".
    set (C11 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg
        (and_vec (C10 !!! Regidx (mword_of_int 15 : mword 5)) (sign_extend' 64 (sign_extend' 12 (mword_of_int 2 : mword 6))))]> C10).
    change (<[Regidx (mword_of_int 15 : mword 5) := regval_into_reg
        (and_vec (C10 !!! Regidx (mword_of_int 15 : mword 5)) (sign_extend' 64 (sign_extend' 12 (mword_of_int 2 : mword 6))))]> C10) with C11.
    assert (Hpc42 : add_vec_int (mword_of_int (SD + 0x40) : mword 64) 2 = mword_of_int (SD + 0x42)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc42) in "Hpc".
    (* +0x42 c.bnez a5 : SIE bit clear, falls through *)
    iPoseProof (sdi_42 with "Htext") as "Hi42".
    assert (HSIEne : eq_vec (_get_Mstatus_SIE ms2) ('b"1") = false) by (rewrite HSIE0; vm_compute; reflexivity).
    assert (Ha5C11 : C11 !!! Regidx (mword_of_int 15 : mword 5)
                     = and_vec (sstatus_read ms2) (sign_extend' 64 (sign_extend' 12 (mword_of_int 2 : mword 6)))).
    { rewrite /C11 upd_eq /C10 upd_eq. reflexivity. }
    iApply (wp_cbnez_fall_s_sconf γ Φ (mword_of_int (SD + 0x42)) (mword_of_int 55 : mword 8) (Cregidx (mword_of_int 7)) (mword_of_int 15 : mword 5)
              C11 (av - 6)%nat ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha5C11; exact (sched_sstatus_clear ms2 HSIEne))
              with "Hcg Hpc Hi42 [-]").
    iIntros "Hcg Hpc".
    assert (Hpc44 : add_vec_int (mword_of_int (SD + 0x42) : mword 64) 2 = mword_of_int (SD + 0x44)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc44) in "Hpc".
    (* tp / s1 threaded through the check chain. *)
    assert (HC11_x4 : C11 !!! Regidx (mword_of_int 4 : mword 5) = cid_word).
    { rewrite /C11 upd_ne; [| vm_compute; discriminate]. rewrite /C10 upd_ne; [| vm_compute; discriminate].
      rewrite /C9 upd_ne; [| vm_compute; discriminate]. rewrite /C8 upd_ne; [| vm_compute; discriminate].
      rewrite /C7 upd_ne; [| vm_compute; discriminate]. rewrite /C6 upd_ne; [| vm_compute; discriminate].
      rewrite /C5 upd_ne; [| vm_compute; discriminate]. rewrite /C4 upd_ne; [| vm_compute; discriminate].
      rewrite /C3 upd_ne; [| vm_compute; discriminate]. rewrite /C2 upd_ne; [| vm_compute; discriminate].
      rewrite /C1 upd_ne; [| vm_compute; discriminate]. rewrite /C0 upd_ne; [| vm_compute; discriminate].
      exact Htp_mh. }
    assert (HC11_x9 : C11 !!! Regidx (mword_of_int 9 : mword 5) = add_vec zero_reg (proc_addr j)).
    { rewrite /C11 upd_ne; [| vm_compute; discriminate]. rewrite /C10 upd_ne; [| vm_compute; discriminate].
      rewrite /C9 upd_ne; [| vm_compute; discriminate]. rewrite /C8 upd_ne; [| vm_compute; discriminate].
      rewrite /C7 upd_ne; [| vm_compute; discriminate]. rewrite /C6 upd_ne; [| vm_compute; discriminate].
      rewrite /C5 upd_ne; [| vm_compute; discriminate]. rewrite /C4 upd_ne; [| vm_compute; discriminate].
      rewrite /C3 upd_ne; [| vm_compute; discriminate]. rewrite /C2 upd_ne; [| vm_compute; discriminate].
      rewrite /C1 upd_ne; [| vm_compute; discriminate]. rewrite /C0 upd_ne; [| vm_compute; discriminate].
      exact Hs1_mh. }
    (* ------------------------------------------------------------------ *)
    (* +0x44..+0x54: read mycpu()->intena into s3.                        *)
    (* ------------------------------------------------------------------ *)
    (* +0x44 c.mv a5,tp *)
    iPoseProof (sdi_44 with "Htext") as "Hi44".
    iApply (wp_cmv_s_sconf γ Φ (mword_of_int (SD + 0x44)) (mword_of_int 15 : mword 5) (mword_of_int 4 : mword 5)
              C11 (av - 6)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi44 [-]").
    iIntros "Hcg Hpc".
    set (D0 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (add_vec zero_reg (C11 !!! Regidx (mword_of_int 4 : mword 5)))]> C11).
    change (<[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (add_vec zero_reg (C11 !!! Regidx (mword_of_int 4 : mword 5)))]> C11) with D0.
    assert (Hpc46 : add_vec_int (mword_of_int (SD + 0x44) : mword 64) 2 = mword_of_int (SD + 0x46)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc46) in "Hpc".
    (* +0x46 auipc s2,0x10 *)
    iPoseProof (sdi_46 with "Htext") as "Hi46".
    iApply (wp_auipc_s_sconf γ Φ (mword_of_int (SD + 0x46)) (mword_of_int 18 : mword 5) (mword_of_int 0x10 : mword 20)
              D0 (av - 6)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi46 [-]").
    iIntros "Hcg Hpc".
    set (D1 := <[Regidx (mword_of_int 18 : mword 5) := regval_into_reg (add_vec (mword_of_int (SD + 0x46) : mword 64) (auipc_off (mword_of_int 0x10 : mword 20)))]> D0).
    change (<[Regidx (mword_of_int 18 : mword 5) := regval_into_reg (add_vec (mword_of_int (SD + 0x46) : mword 64) (auipc_off (mword_of_int 0x10 : mword 20)))]> D0) with D1.
    assert (Hpc4a : add_vec_int (mword_of_int (SD + 0x46) : mword 64) 4 = mword_of_int (SD + 0x4a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc4a) in "Hpc".
    (* +0x4a addi s2,s2,1252 *)
    iPoseProof (sdi_4a with "Htext") as "Hi4a".
    iApply (wp_addi4_s_sconf γ Φ (mword_of_int (SD + 0x4a)) (mword_of_int 18 : mword 5) (mword_of_int 18 : mword 5) (mword_of_int 0x4e4 : mword 12)
              D1 (av - 6)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi4a [-]").
    iIntros "Hcg Hpc".
    set (D2 := <[Regidx (mword_of_int 18 : mword 5) := regval_into_reg (add_vec (D1 !!! Regidx (mword_of_int 18 : mword 5)) (sign_extend' 64 (mword_of_int 0x4e4 : mword 12)))]> D1).
    change (<[Regidx (mword_of_int 18 : mword 5) := regval_into_reg (add_vec (D1 !!! Regidx (mword_of_int 18 : mword 5)) (sign_extend' 64 (mword_of_int 0x4e4 : mword 12)))]> D1) with D2.
    assert (Hpc4e : add_vec_int (mword_of_int (SD + 0x4a) : mword 64) 4 = mword_of_int (SD + 0x4e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc4e) in "Hpc".
    (* +0x4e sext.w a5 *)
    iPoseProof (sdi_4e with "Htext") as "Hi4e".
    iApply (wp_caddiw_s_sconf γ Φ (mword_of_int (SD + 0x4e)) (mword_of_int 15 : mword 5) (mword_of_int 0 : mword 6)
              D2 (av - 6)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi4e [-]").
    iIntros "Hcg Hpc".
    set (D3 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg
        (sign_extend' 64 (subrange_vec_dec (add_vec (D2 !!! Regidx (mword_of_int 15 : mword 5)) (sign_extend' 64 (sign_extend' 12 (mword_of_int 0 : mword 6)))) 31 0))]> D2).
    change (<[Regidx (mword_of_int 15 : mword 5) := regval_into_reg
        (sign_extend' 64 (subrange_vec_dec (add_vec (D2 !!! Regidx (mword_of_int 15 : mword 5)) (sign_extend' 64 (sign_extend' 12 (mword_of_int 0 : mword 6)))) 31 0))]> D2) with D3.
    assert (Hpc50 : add_vec_int (mword_of_int (SD + 0x4e) : mword 64) 2 = mword_of_int (SD + 0x50)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc50) in "Hpc".
    (* +0x50 c.slli a5,7 *)
    iPoseProof (sdi_50 with "Htext") as "Hi50".
    iApply (wp_cslli_s_sconf γ Φ (mword_of_int (SD + 0x50)) (Regidx (mword_of_int 15)) (mword_of_int 15 : mword 5) (mword_of_int 7 : mword 6)
              D3 (av - 6)%nat eq_refl ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi50 [-]").
    iIntros "Hcg Hpc".
    set (D4 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg
        (shift_bits_left (D3 !!! Regidx (mword_of_int 15 : mword 5)) (subrange_vec_dec (mword_of_int 7 : mword 6) (Z.sub log2_xlen 1) 0))]> D3).
    change (<[Regidx (mword_of_int 15 : mword 5) := regval_into_reg
        (shift_bits_left (D3 !!! Regidx (mword_of_int 15 : mword 5)) (subrange_vec_dec (mword_of_int 7 : mword 6) (Z.sub log2_xlen 1) 0))]> D3) with D4.
    assert (HshD : D4 !!! Regidx (mword_of_int 15 : mword 5) = mycpu_a5 cid_word).
    { rewrite /D4 upd_eq /D3 upd_eq.
      rewrite /D2 upd_ne; [| vm_compute; discriminate]. rewrite /D1 upd_ne; [| vm_compute; discriminate].
      rewrite /D0 upd_eq HC11_x4. reflexivity. }
    assert (HD4s2 : D4 !!! Regidx (mword_of_int 18 : mword 5)
                    = add_vec (add_vec (mword_of_int (SD + 0x46) : mword 64) (auipc_off (mword_of_int 0x10 : mword 20))) (sign_extend' 64 (mword_of_int 0x4e4 : mword 12))).
    { rewrite /D4 upd_ne; [| vm_compute; discriminate]. rewrite /D3 upd_ne; [| vm_compute; discriminate].
      rewrite /D2 upd_eq /D1 upd_eq. reflexivity. }
    assert (Hpc52 : add_vec_int (mword_of_int (SD + 0x50) : mword 64) 2 = mword_of_int (SD + 0x52)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc52) in "Hpc".
    (* +0x52 c.add a5,a5,s2 *)
    iPoseProof (sdi_52 with "Htext") as "Hi52".
    iApply (wp_cadd_s_sconf γ Φ (mword_of_int (SD + 0x52)) (mword_of_int 15 : mword 5) (mword_of_int 18 : mword 5)
              D4 (av - 6)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi52 [-]").
    iIntros "Hcg Hpc".
    set (D5 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (add_vec (D4 !!! Regidx (mword_of_int 15 : mword 5)) (D4 !!! Regidx (mword_of_int 18 : mword 5)))]> D4).
    change (<[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (add_vec (D4 !!! Regidx (mword_of_int 15 : mword 5)) (D4 !!! Regidx (mword_of_int 18 : mword 5)))]> D4) with D5.
    assert (Hpc54 : add_vec_int (mword_of_int (SD + 0x52) : mword 64) 2 = mword_of_int (SD + 0x54)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc54) in "Hpc".
    (* +0x54 lw s3,172(a5) : reconcile to a_cpu_int *)
    assert (Hrec_int : add_vec (D5 !!! Regidx (mword_of_int 15 : mword 5)) (sign_extend' 64 (mword_of_int 172 : mword 12))
                       = a_cpu_int cid_word).
    { assert (HD5v : D5 !!! Regidx (mword_of_int 15 : mword 5)
                     = add_vec (mycpu_a5 cid_word)
                         (add_vec (add_vec (mword_of_int (SD + 0x46) : mword 64) (auipc_off (mword_of_int 0x10 : mword 20)))
                                  (sign_extend' 64 (mword_of_int 0x4e4 : mword 12)))).
      { rewrite /D5 upd_eq HshD HD4s2. reflexivity. }
      rewrite HD5v. unfold a_cpu_int, mycpu_ret.
      rewrite (sched_addvC _ (mycpu_a5 cid_word)).
      apply sched_reconcile. vm_compute. reflexivity. }
    iPoseProof (sdi_54 with "Htext") as "Hi54".
    iApply (wp_lw_s_sconf γ Φ (mword_of_int (SD + 0x54)) (mword_of_int 19 : mword 5) (mword_of_int 15 : mword 5)
              (mword_of_int 172 : mword 12) D5 (av - 6)%nat iv
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi54 [Hint] [-]").
    { iEval (rewrite Hrec_int). iExact "Hint". }
    iIntros "Hcg Hpc Hint".
    iEval (rewrite Hrec_int) in "Hint".
    set (D6 := <[Regidx (mword_of_int 19 : mword 5) := regval_into_reg (sign_extend' 64 (iv : mword 32))]> D5).
    change (<[Regidx (mword_of_int 19 : mword 5) := regval_into_reg (sign_extend' 64 (iv : mword 32))]> D5) with D6.
    assert (Hpc58 : add_vec_int (mword_of_int (SD + 0x54) : mword 64) 4 = mword_of_int (SD + 0x58)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc58) in "Hpc".
    assert (HD6_x4 : D6 !!! Regidx (mword_of_int 4 : mword 5) = cid_word).
    { rewrite /D6 upd_ne; [| vm_compute; discriminate]. rewrite /D5 upd_ne; [| vm_compute; discriminate].
      rewrite /D4 upd_ne; [| vm_compute; discriminate]. rewrite /D3 upd_ne; [| vm_compute; discriminate].
      rewrite /D2 upd_ne; [| vm_compute; discriminate]. rewrite /D1 upd_ne; [| vm_compute; discriminate].
      rewrite /D0 upd_ne; [| vm_compute; discriminate]. exact HC11_x4. }
    (* ------------------------------------------------------------------ *)
    (* +0x58..+0x6a: build a1 = &c->context, a0 = &p->context.            *)
    (* ------------------------------------------------------------------ *)
    (* +0x58 c.mv a5,tp *)
    iPoseProof (sdi_58 with "Htext") as "Hi58".
    iApply (wp_cmv_s_sconf γ Φ (mword_of_int (SD + 0x58)) (mword_of_int 15 : mword 5) (mword_of_int 4 : mword 5)
              D6 (av - 6)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi58 [-]").
    iIntros "Hcg Hpc".
    set (D7 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (add_vec zero_reg (D6 !!! Regidx (mword_of_int 4 : mword 5)))]> D6).
    change (<[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (add_vec zero_reg (D6 !!! Regidx (mword_of_int 4 : mword 5)))]> D6) with D7.
    assert (Hpc5a : add_vec_int (mword_of_int (SD + 0x58) : mword 64) 2 = mword_of_int (SD + 0x5a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc5a) in "Hpc".
    (* +0x5a sext.w a5 *)
    iPoseProof (sdi_5a with "Htext") as "Hi5a".
    iApply (wp_caddiw_s_sconf γ Φ (mword_of_int (SD + 0x5a)) (mword_of_int 15 : mword 5) (mword_of_int 0 : mword 6)
              D7 (av - 6)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi5a [-]").
    iIntros "Hcg Hpc".
    set (D8 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg
        (sign_extend' 64 (subrange_vec_dec (add_vec (D7 !!! Regidx (mword_of_int 15 : mword 5)) (sign_extend' 64 (sign_extend' 12 (mword_of_int 0 : mword 6)))) 31 0))]> D7).
    change (<[Regidx (mword_of_int 15 : mword 5) := regval_into_reg
        (sign_extend' 64 (subrange_vec_dec (add_vec (D7 !!! Regidx (mword_of_int 15 : mword 5)) (sign_extend' 64 (sign_extend' 12 (mword_of_int 0 : mword 6)))) 31 0))]> D7) with D8.
    assert (Hpc5c : add_vec_int (mword_of_int (SD + 0x5a) : mword 64) 2 = mword_of_int (SD + 0x5c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc5c) in "Hpc".
    (* +0x5c c.slli a5,7 *)
    iPoseProof (sdi_5c with "Htext") as "Hi5c".
    iApply (wp_cslli_s_sconf γ Φ (mword_of_int (SD + 0x5c)) (Regidx (mword_of_int 15)) (mword_of_int 15 : mword 5) (mword_of_int 7 : mword 6)
              D8 (av - 6)%nat eq_refl ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi5c [-]").
    iIntros "Hcg Hpc".
    set (D9 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg
        (shift_bits_left (D8 !!! Regidx (mword_of_int 15 : mword 5)) (subrange_vec_dec (mword_of_int 7 : mword 6) (Z.sub log2_xlen 1) 0))]> D8).
    change (<[Regidx (mword_of_int 15 : mword 5) := regval_into_reg
        (shift_bits_left (D8 !!! Regidx (mword_of_int 15 : mword 5)) (subrange_vec_dec (mword_of_int 7 : mword 6) (Z.sub log2_xlen 1) 0))]> D8) with D9.
    assert (HshD2 : D9 !!! Regidx (mword_of_int 15 : mword 5) = mycpu_a5 cid_word).
    { rewrite /D9 upd_eq /D8 upd_eq /D7 upd_eq HD6_x4. reflexivity. }
    assert (Hpc5e : add_vec_int (mword_of_int (SD + 0x5c) : mword 64) 2 = mword_of_int (SD + 0x5e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc5e) in "Hpc".
    (* +0x5e c.addi a5,a5,8 *)
    iPoseProof (sdi_5e with "Htext") as "Hi5e".
    iApply (wp_caddi_s_sconf γ Φ (mword_of_int (SD + 0x5e)) (mword_of_int 15 : mword 5) (mword_of_int 8 : mword 6)
              D9 (av - 6)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi5e [-]").
    iIntros "Hcg Hpc".
    set (D10 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg
        (add_vec (D9 !!! Regidx (mword_of_int 15 : mword 5)) (sign_extend' 64 (sign_extend' 12 (mword_of_int 8 : mword 6))))]> D9).
    change (<[Regidx (mword_of_int 15 : mword 5) := regval_into_reg
        (add_vec (D9 !!! Regidx (mword_of_int 15 : mword 5)) (sign_extend' 64 (sign_extend' 12 (mword_of_int 8 : mword 6))))]> D9) with D10.
    assert (HD10a5 : D10 !!! Regidx (mword_of_int 15 : mword 5)
                     = add_vec (mycpu_a5 cid_word) (sign_extend' 64 (sign_extend' 12 (mword_of_int 8 : mword 6))))
      by (rewrite /D10 upd_eq HshD2; reflexivity).
    assert (Hpc60 : add_vec_int (mword_of_int (SD + 0x5e) : mword 64) 2 = mword_of_int (SD + 0x60)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc60) in "Hpc".
    (* +0x60 auipc a1,0x10 *)
    iPoseProof (sdi_60 with "Htext") as "Hi60".
    iApply (wp_auipc_s_sconf γ Φ (mword_of_int (SD + 0x60)) (mword_of_int 11 : mword 5) (mword_of_int 0x10 : mword 20)
              D10 (av - 6)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi60 [-]").
    iIntros "Hcg Hpc".
    set (D11 := <[Regidx (mword_of_int 11 : mword 5) := regval_into_reg (add_vec (mword_of_int (SD + 0x60) : mword 64) (auipc_off (mword_of_int 0x10 : mword 20)))]> D10).
    change (<[Regidx (mword_of_int 11 : mword 5) := regval_into_reg (add_vec (mword_of_int (SD + 0x60) : mword 64) (auipc_off (mword_of_int 0x10 : mword 20)))]> D10) with D11.
    assert (Hpc64 : add_vec_int (mword_of_int (SD + 0x60) : mword 64) 4 = mword_of_int (SD + 0x64)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc64) in "Hpc".
    (* +0x64 addi a1,a1,1274 *)
    iPoseProof (sdi_64 with "Htext") as "Hi64".
    iApply (wp_addi4_s_sconf γ Φ (mword_of_int (SD + 0x64)) (mword_of_int 11 : mword 5) (mword_of_int 11 : mword 5) (mword_of_int 0x4fa : mword 12)
              D11 (av - 6)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi64 [-]").
    iIntros "Hcg Hpc".
    set (D12 := <[Regidx (mword_of_int 11 : mword 5) := regval_into_reg (add_vec (D11 !!! Regidx (mword_of_int 11 : mword 5)) (sign_extend' 64 (mword_of_int 0x4fa : mword 12)))]> D11).
    change (<[Regidx (mword_of_int 11 : mword 5) := regval_into_reg (add_vec (D11 !!! Regidx (mword_of_int 11 : mword 5)) (sign_extend' 64 (mword_of_int 0x4fa : mword 12)))]> D11) with D12.
    assert (HD12a1 : D12 !!! Regidx (mword_of_int 11 : mword 5)
                     = add_vec (add_vec (mword_of_int (SD + 0x60) : mword 64) (auipc_off (mword_of_int 0x10 : mword 20))) (sign_extend' 64 (mword_of_int 0x4fa : mword 12)))
      by (rewrite /D12 upd_eq /D11 upd_eq; reflexivity).
    assert (HD12a5 : D12 !!! Regidx (mword_of_int 15 : mword 5)
                     = add_vec (mycpu_a5 cid_word) (sign_extend' 64 (sign_extend' 12 (mword_of_int 8 : mword 6)))).
    { rewrite /D12 upd_ne; [| vm_compute; discriminate]. rewrite /D11 upd_ne; [| vm_compute; discriminate]. exact HD10a5. }
    assert (Hpc68 : add_vec_int (mword_of_int (SD + 0x64) : mword 64) 4 = mword_of_int (SD + 0x68)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc68) in "Hpc".
    (* +0x68 c.add a1,a1,a5 *)
    iPoseProof (sdi_68 with "Htext") as "Hi68".
    iApply (wp_cadd_s_sconf γ Φ (mword_of_int (SD + 0x68)) (mword_of_int 11 : mword 5) (mword_of_int 15 : mword 5)
              D12 (av - 6)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi68 [-]").
    iIntros "Hcg Hpc".
    set (D13 := <[Regidx (mword_of_int 11 : mword 5) := regval_into_reg (add_vec (D12 !!! Regidx (mword_of_int 11 : mword 5)) (D12 !!! Regidx (mword_of_int 15 : mword 5)))]> D12).
    change (<[Regidx (mword_of_int 11 : mword 5) := regval_into_reg (add_vec (D12 !!! Regidx (mword_of_int 11 : mword 5)) (D12 !!! Regidx (mword_of_int 15 : mword 5)))]> D12) with D13.
    assert (Hpc6a : add_vec_int (mword_of_int (SD + 0x68) : mword 64) 2 = mword_of_int (SD + 0x6a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc6a) in "Hpc".
    (* s1 threaded to D13 *)
    assert (HD13_x9 : D13 !!! Regidx (mword_of_int 9 : mword 5) = add_vec zero_reg (proc_addr j)).
    { rewrite /D13 upd_ne; [| vm_compute; discriminate]. rewrite /D12 upd_ne; [| vm_compute; discriminate].
      rewrite /D11 upd_ne; [| vm_compute; discriminate]. rewrite /D10 upd_ne; [| vm_compute; discriminate].
      rewrite /D9 upd_ne; [| vm_compute; discriminate]. rewrite /D8 upd_ne; [| vm_compute; discriminate].
      rewrite /D7 upd_ne; [| vm_compute; discriminate]. rewrite /D6 upd_ne; [| vm_compute; discriminate].
      rewrite /D5 upd_ne; [| vm_compute; discriminate]. rewrite /D4 upd_ne; [| vm_compute; discriminate].
      rewrite /D3 upd_ne; [| vm_compute; discriminate]. rewrite /D2 upd_ne; [| vm_compute; discriminate].
      rewrite /D1 upd_ne; [| vm_compute; discriminate]. rewrite /D0 upd_ne; [| vm_compute; discriminate].
      exact HC11_x9. }
    (* +0x6a addi a0,s1,96 *)
    iPoseProof (sdi_6a with "Htext") as "Hi6a".
    iApply (wp_addi4_s_sconf γ Φ (mword_of_int (SD + 0x6a)) (mword_of_int 10 : mword 5) (mword_of_int 9 : mword 5) (mword_of_int 0x60 : mword 12)
              D13 (av - 6)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi6a [-]").
    iIntros "Hcg Hpc".
    set (D14 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg (add_vec (D13 !!! Regidx (mword_of_int 9 : mword 5)) (sign_extend' 64 (mword_of_int 0x60 : mword 12)))]> D13).
    change (<[Regidx (mword_of_int 10 : mword 5) := regval_into_reg (add_vec (D13 !!! Regidx (mword_of_int 9 : mword 5)) (sign_extend' 64 (mword_of_int 0x60 : mword 12)))]> D13) with D14.
    assert (Hpc6e : add_vec_int (mword_of_int (SD + 0x6a) : mword 64) 4 = mword_of_int (SD + 0x6e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc6e) in "Hpc".
    (* ------------------------------------------------------------------ *)
    (* +0x6e: jal swtch, then the swtch(&p->context, &c->context) call.    *)
    (* ------------------------------------------------------------------ *)
    iPoseProof (sdi_6e with "Htext") as "Hi6e".
    iApply (wp_jal_s_sconf γ Φ (mword_of_int (SD + 0x6e)) (mword_of_int 1 : mword 5) (mword_of_int 1292 : mword 21)
              D14 (av - 6)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi6e [-]").
    iIntros "Hcg Hpc".
    set (Mc := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (SD + 0x6e) : mword 64) 4)]> D14).
    change (<[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (SD + 0x6e) : mword 64) 4)]> D14) with Mc.
    assert (Hpcsw : add_vec (mword_of_int (SD + 0x6e) : mword 64) (sign_extend' 64 (mword_of_int 1292 : mword 21))
                    = mword_of_int KernelSyms.swtch) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpcsw) in "Hpc".
    (* call-site register facts. *)
    assert (Hra_Mc : Mc !!! Regidx (mword_of_int 1 : mword 5) = add_vec_int (mword_of_int (SD + 0x6e) : mword 64) 4)
      by (rewrite /Mc upd_eq; reflexivity).
    assert (Htp_Mc : Mc !!! Regidx (mword_of_int 4 : mword 5) = cid_word).
    { rewrite /Mc upd_ne; [| vm_compute; discriminate]. rewrite /D14 upd_ne; [| vm_compute; discriminate].
      rewrite /D13 upd_ne; [| vm_compute; discriminate]. rewrite /D12 upd_ne; [| vm_compute; discriminate].
      rewrite /D11 upd_ne; [| vm_compute; discriminate]. rewrite /D10 upd_ne; [| vm_compute; discriminate].
      rewrite /D9 upd_ne; [| vm_compute; discriminate]. rewrite /D8 upd_ne; [| vm_compute; discriminate].
      rewrite /D7 upd_ne; [| vm_compute; discriminate]. exact HD6_x4. }
    assert (Holdc : Mc !!! Regidx (mword_of_int 10 : mword 5) = p_context (proc_addr j)).
    { rewrite /Mc upd_ne; [| vm_compute; discriminate]. rewrite /D14 upd_eq HD13_x9 sched_addv_zero_l.
      unfold p_context, context_off.
      assert (H96 : sign_extend' 64 (mword_of_int 96 : mword 12) = (mword_of_int 96 : mword 64)) by (apply bv_eq; vm_compute; reflexivity).
      rewrite H96. reflexivity. }
    assert (Hnewc : Mc !!! Regidx (mword_of_int 11 : mword 5) = a_cpu_ctx cid_word).
    { rewrite /Mc upd_ne; [| vm_compute; discriminate]. rewrite /D14 upd_ne; [| vm_compute; discriminate].
      rewrite /D13 upd_eq HD12a1 HD12a5. unfold a_cpu_ctx, mycpu_ret.
      apply sched_reconcile2. vm_compute. reflexivity. }
    (* FULL-BUNDLE swtch: hand [sie_cap_gpr] and [cpu_own] whole (the swtch
       proof internally carves the stack/off-eighth and parks them in the OLD
       record).  Refold the check-chain cells into the level-1 [cpu_own]. *)
    iAssert (cpu_own γ 1 eb pj emp) with "[Hnoff Hint Hcnt Hcur]" as "Hcpu".
    { rewrite /cpu_own. iFrame "Hnoff Hint Hcnt Hcur". iPureIntro; vm_compute; reflexivity. }
    (* build the parking-proc payload (proc-held facts only; the cpu bundle
       now crosses at the swtch's [cpu_own] interface, not in the payload). *)
    iPoseProof (p_sched_to_cpu γs cpu_id j γl st ch Hj Hgl Hneeds
                  with "[Hlocked Hstate Hchan Hpub]") as "HP".
    { rewrite /proc_held. iFrame "Hlocked Hstate Hchan Hpub". }
    (* apply swtch. *)
    iApply (Swtch.wp_swtch_sconf γ Φ (p_sched γs cpu_id) (p_context (proc_addr j)) (a_cpu_ctx cid_word)
              Mc ctxvs (av - 6)%nat eb pj
              Hctxlen Holdc Hnewc
              with "Htext Hcg Hcpu Hpc Hctxcells Hvc [HP] [-]").
    { iEval (rewrite Htp_Mc). iExact "HP". }
    iIntros (m' eb') "%Hcallee Hcg Hcpu Hpc Hctxback Hresume".
    (* resume: elim the SECOND disjunct (dispatched proc). *)
    iDestruct "Hresume" as (cret) "[Hvc' Hpay]".
    iDestruct (p_sched_at_proc γs cpu_id j cret (m' !!! Regidx (mword_of_int 4 : mword 5)) pj Hj with "Hpay")
      as "(%Htpv & %Hcret & %Hpidx & Hpay2)".
    iDestruct "Hpay2" as (γl' ch') "(%Hgl' & Hheld')".
    assert (γl' = γl) as -> by (rewrite Hgl in Hgl'; injection Hgl'; auto).
    (* callee-image component equalities. *)
    unfold callee_img, ctx_regs in Hcallee. simpl in Hcallee.
    injection Hcallee as Hm1 Hm2 Hm8 Hm9 Hm18 Hm19 Hm20 Hm21 Hm22 Hm23 Hm24 Hm25 Hm26 Hm27.
    (* sie_cap_gpr [Hcg] and cpu_own [Hcpu] both came back WHOLE from the swtch
       continuation (at [av-6] and at the same [eb], [pj]); no rebuild needed. *)
    (* sp threads unchanged from the prologue push all the way through. *)
    assert (Hcsp_Mc : Mc !!! Regidx csp_rs1 = spd).
    { rewrite /Mc upd_ne; [| vm_compute; discriminate].
      rewrite /D14 upd_ne; [| vm_compute; discriminate]. rewrite /D13 upd_ne; [| vm_compute; discriminate].
      rewrite /D12 upd_ne; [| vm_compute; discriminate]. rewrite /D11 upd_ne; [| vm_compute; discriminate].
      rewrite /D10 upd_ne; [| vm_compute; discriminate]. rewrite /D9 upd_ne; [| vm_compute; discriminate].
      rewrite /D8 upd_ne; [| vm_compute; discriminate]. rewrite /D7 upd_ne; [| vm_compute; discriminate].
      rewrite /D6 upd_ne; [| vm_compute; discriminate]. rewrite /D5 upd_ne; [| vm_compute; discriminate].
      rewrite /D4 upd_ne; [| vm_compute; discriminate]. rewrite /D3 upd_ne; [| vm_compute; discriminate].
      rewrite /D2 upd_ne; [| vm_compute; discriminate]. rewrite /D1 upd_ne; [| vm_compute; discriminate].
      rewrite /D0 upd_ne; [| vm_compute; discriminate].
      rewrite /C11 upd_ne; [| vm_compute; discriminate]. rewrite /C10 upd_ne; [| vm_compute; discriminate].
      rewrite /C9 upd_ne; [| vm_compute; discriminate]. rewrite /C8 upd_ne; [| vm_compute; discriminate].
      rewrite /C7 upd_ne; [| vm_compute; discriminate]. rewrite /C6 upd_ne; [| vm_compute; discriminate].
      rewrite /C5 upd_ne; [| vm_compute; discriminate]. rewrite /C4 upd_ne; [| vm_compute; discriminate].
      rewrite /C3 upd_ne; [| vm_compute; discriminate]. rewrite /C2 upd_ne; [| vm_compute; discriminate].
      rewrite /C1 upd_ne; [| vm_compute; discriminate]. rewrite /C0 upd_ne; [| vm_compute; discriminate].
      rewrite (callee_saved_lookup Hcs_mh csp_rs1 ltac:(vm_compute; reflexivity)).
      rewrite /B1 upd_ne; [| vm_compute; discriminate]. rewrite /B0 upd_ne; [| vm_compute; discriminate].
      rewrite (callee_saved_lookup Hcs_mp csp_rs1 ltac:(vm_compute; reflexivity)).
      rewrite /A2 upd_ne; [| vm_compute; discriminate]. rewrite /A1 upd_ne; [| vm_compute; discriminate].
      exact HcspA0. }
    assert (Hsp_m' : m' !!! Regidx csp_rs1 = spd).
    { change (Regidx csp_rs1) with (Regidx (mword_of_int 2 : mword 5)).
      rewrite Hm2. change (Regidx (mword_of_int 2 : mword 5)) with (Regidx csp_rs1). exact Hcsp_Mc. }
    (* pc lands on the saved return address SD+0x72. *)
    assert (Hpctgt : ret_pc (m' !!! Regidx (mword_of_int 1 : mword 5)) = mword_of_int (SD + 0x72))
      by (rewrite Hm1 Hra_Mc; vm_compute; reflexivity).
    iEval (rewrite Hpctgt) in "Hpc".
    (* the returned cpu bundle came back at the RESUMER's base [eb'] (the wand
       is [∀ eb']); unfold it -- the intena-restore store + a ghost retune below
       bring it back to this thread's own saved base [eb]. *)
    iEval (rewrite /cpu_own) in "Hcpu".
    iDestruct "Hcpu" as "(_ & Hnoff2 & Hint2 & Hcnt2 & Hcur2 & _)".
    set (iv' := intena_val eb' : mword 32).
    (* ------------------------------------------------------------------ *)
    (* +0x72..+0x7a: restore c->intena := s3.                             *)
    (* ------------------------------------------------------------------ *)
    (* +0x72 c.mv a5,tp *)
    iPoseProof (sdi_72 with "Htext") as "Hi72".
    iApply (wp_cmv_s_sconf γ Φ (mword_of_int (SD + 0x72)) (mword_of_int 15 : mword 5) (mword_of_int 4 : mword 5)
              m' (av - 6)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi72 [-]").
    iIntros "Hcg Hpc".
    set (E0 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (add_vec zero_reg (m' !!! Regidx (mword_of_int 4 : mword 5)))]> m').
    change (<[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (add_vec zero_reg (m' !!! Regidx (mword_of_int 4 : mword 5)))]> m') with E0.
    assert (Hpc74 : add_vec_int (mword_of_int (SD + 0x72) : mword 64) 2 = mword_of_int (SD + 0x74)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc74) in "Hpc".
    (* +0x74 sext.w a5 *)
    iPoseProof (sdi_74 with "Htext") as "Hi74".
    iApply (wp_caddiw_s_sconf γ Φ (mword_of_int (SD + 0x74)) (mword_of_int 15 : mword 5) (mword_of_int 0 : mword 6)
              E0 (av - 6)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi74 [-]").
    iIntros "Hcg Hpc".
    set (E1 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg
        (sign_extend' 64 (subrange_vec_dec (add_vec (E0 !!! Regidx (mword_of_int 15 : mword 5)) (sign_extend' 64 (sign_extend' 12 (mword_of_int 0 : mword 6)))) 31 0))]> E0).
    change (<[Regidx (mword_of_int 15 : mword 5) := regval_into_reg
        (sign_extend' 64 (subrange_vec_dec (add_vec (E0 !!! Regidx (mword_of_int 15 : mword 5)) (sign_extend' 64 (sign_extend' 12 (mword_of_int 0 : mword 6)))) 31 0))]> E0) with E1.
    assert (Hpc76 : add_vec_int (mword_of_int (SD + 0x74) : mword 64) 2 = mword_of_int (SD + 0x76)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc76) in "Hpc".
    (* +0x76 c.slli a5,7 *)
    iPoseProof (sdi_76 with "Htext") as "Hi76".
    iApply (wp_cslli_s_sconf γ Φ (mword_of_int (SD + 0x76)) (Regidx (mword_of_int 15)) (mword_of_int 15 : mword 5) (mword_of_int 7 : mword 6)
              E1 (av - 6)%nat eq_refl ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi76 [-]").
    iIntros "Hcg Hpc".
    set (E2 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg
        (shift_bits_left (E1 !!! Regidx (mword_of_int 15 : mword 5)) (subrange_vec_dec (mword_of_int 7 : mword 6) (Z.sub log2_xlen 1) 0))]> E1).
    change (<[Regidx (mword_of_int 15 : mword 5) := regval_into_reg
        (shift_bits_left (E1 !!! Regidx (mword_of_int 15 : mword 5)) (subrange_vec_dec (mword_of_int 7 : mword 6) (Z.sub log2_xlen 1) 0))]> E1) with E2.
    assert (HshE : E2 !!! Regidx (mword_of_int 15 : mword 5) = mycpu_a5 cid_word)
      by (rewrite /E2 upd_eq /E1 upd_eq /E0 upd_eq Htpv; reflexivity).
    assert (Hpc78 : add_vec_int (mword_of_int (SD + 0x76) : mword 64) 2 = mword_of_int (SD + 0x78)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc78) in "Hpc".
    (* +0x78 c.add s2,s2,a5 *)
    iPoseProof (sdi_78 with "Htext") as "Hi78".
    iApply (wp_cadd_s_sconf γ Φ (mword_of_int (SD + 0x78)) (mword_of_int 18 : mword 5) (mword_of_int 15 : mword 5)
              E2 (av - 6)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi78 [-]").
    iIntros "Hcg Hpc".
    set (E3 := <[Regidx (mword_of_int 18 : mword 5) := regval_into_reg (add_vec (E2 !!! Regidx (mword_of_int 18 : mword 5)) (E2 !!! Regidx (mword_of_int 15 : mword 5)))]> E2).
    change (<[Regidx (mword_of_int 18 : mword 5) := regval_into_reg (add_vec (E2 !!! Regidx (mword_of_int 18 : mword 5)) (E2 !!! Regidx (mword_of_int 15 : mword 5)))]> E2) with E3.
    assert (Hpc7a : add_vec_int (mword_of_int (SD + 0x78) : mword 64) 2 = mword_of_int (SD + 0x7a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc7a) in "Hpc".
    (* +0x7a sw s3,172(s2) : reconcile to a_cpu_int, store into the cell *)
    assert (HMc_x18 : Mc !!! Regidx (mword_of_int 18 : mword 5)
                      = add_vec (add_vec (mword_of_int (SD + 0x46) : mword 64) (auipc_off (mword_of_int 0x10 : mword 20))) (sign_extend' 64 (mword_of_int 0x4e4 : mword 12))).
    { rewrite /Mc upd_ne; [| vm_compute; discriminate]. rewrite /D14 upd_ne; [| vm_compute; discriminate].
      rewrite /D13 upd_ne; [| vm_compute; discriminate]. rewrite /D12 upd_ne; [| vm_compute; discriminate].
      rewrite /D11 upd_ne; [| vm_compute; discriminate]. rewrite /D10 upd_ne; [| vm_compute; discriminate].
      rewrite /D9 upd_ne; [| vm_compute; discriminate]. rewrite /D8 upd_ne; [| vm_compute; discriminate].
      rewrite /D7 upd_ne; [| vm_compute; discriminate]. rewrite /D6 upd_ne; [| vm_compute; discriminate].
      rewrite /D5 upd_ne; [| vm_compute; discriminate]. exact HD4s2. }
    assert (HE2s2 : E2 !!! Regidx (mword_of_int 18 : mword 5)
                    = add_vec (add_vec (mword_of_int (SD + 0x46) : mword 64) (auipc_off (mword_of_int 0x10 : mword 20))) (sign_extend' 64 (mword_of_int 0x4e4 : mword 12))).
    { rewrite /E2 upd_ne; [| vm_compute; discriminate]. rewrite /E1 upd_ne; [| vm_compute; discriminate].
      rewrite /E0 upd_ne; [| vm_compute; discriminate]. rewrite Hm18. exact HMc_x18. }
    assert (Hrec_int2 : add_vec (E3 !!! Regidx (mword_of_int 18 : mword 5)) (sign_extend' 64 (mword_of_int 172 : mword 12)) = a_cpu_int cid_word).
    { assert (HE3v : E3 !!! Regidx (mword_of_int 18 : mword 5)
                     = add_vec (add_vec (add_vec (mword_of_int (SD + 0x46) : mword 64) (auipc_off (mword_of_int 0x10 : mword 20))) (sign_extend' 64 (mword_of_int 0x4e4 : mword 12))) (mycpu_a5 cid_word))
        by (rewrite /E3 upd_eq HE2s2 HshE; reflexivity).
      rewrite HE3v. rewrite (sched_addvC _ (mycpu_a5 cid_word)).
      unfold a_cpu_int, mycpu_ret. rewrite (sched_addvC _ (mycpu_a5 cid_word)).
      apply sched_reconcile. vm_compute. reflexivity. }
    iPoseProof (sdi_7a with "Htext") as "Hi7a".
    iApply (wp_sw_s_sconf γ Φ (mword_of_int (SD + 0x7a)) (mword_of_int 19 : mword 5) (mword_of_int 18 : mword 5)
              (mword_of_int 172 : mword 12) E3 (av - 6)%nat iv'
              with "Hcg Hpc Hi7a [Hint2] [-]").
    { iEval (rewrite Hrec_int2). iExact "Hint2". }
    iIntros "Hcg Hpc Hint2".
    iEval (rewrite Hrec_int2) in "Hint2".
    assert (Hpc7e : add_vec_int (mword_of_int (SD + 0x7a) : mword 64) 4 = mword_of_int (SD + 0x7e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc7e) in "Hpc".
    (* the restored intena cell holds this thread's saved base [intena_val eb]
       (s3 = the value read at +0x54, sign-extended then truncated back). *)
    assert (HE3s3 : E3 !!! Regidx (mword_of_int 19 : mword 5) = sign_extend' 64 (intena_val eb)).
    { rewrite /E3 upd_ne; [| vm_compute; discriminate].
      rewrite /E2 upd_ne; [| vm_compute; discriminate].
      rewrite /E1 upd_ne; [| vm_compute; discriminate].
      rewrite /E0 upd_ne; [| vm_compute; discriminate].
      rewrite Hm19.
      rewrite /Mc upd_ne; [| vm_compute; discriminate].
      rewrite /D14 upd_ne; [| vm_compute; discriminate].
      rewrite /D13 upd_ne; [| vm_compute; discriminate].
      rewrite /D12 upd_ne; [| vm_compute; discriminate].
      rewrite /D11 upd_ne; [| vm_compute; discriminate].
      rewrite /D10 upd_ne; [| vm_compute; discriminate].
      rewrite /D9 upd_ne; [| vm_compute; discriminate].
      rewrite /D8 upd_ne; [| vm_compute; discriminate].
      rewrite /D7 upd_ne; [| vm_compute; discriminate].
      rewrite /D6 upd_eq. reflexivity. }
    assert (Hstoreval : trunc32 (E3 !!! Regidx (mword_of_int 19 : mword 5)) = intena_val eb).
    { rewrite HE3s3. destruct eb; vm_compute; reflexivity. }
    iEval (rewrite Hstoreval) in "Hint2".
    (* retune the count token from the resumer's base [eb'] to this thread's own
       saved base [eb] (retune_on when eb = true, using the entry avail copy);
       the intena cell was just restored to [intena_val eb] by the store. *)
    iAssert (intr_count γ 1 eb) with "[Hcnt2]" as "Hcnt2".
    { destruct eb.
      - iApply (intr_count_retune_on γ 0 eb' with "Havail_eb Hcnt2").
      - iApply (intr_count_retune_off γ 0 eb' with "Hcnt2"). }
    (* refold [cpu_own γ 1 eb pj emp]. *)
    iAssert (cpu_own γ 1 eb pj emp) with "[Hcur2 Hnoff2 Hint2 Hcnt2]" as "Hcpu".
    { rewrite /cpu_own. iFrame "Hnoff2 Hcnt2 Hcur2 Hint2". iPureIntro; vm_compute; reflexivity. }
    (* ------------------------------------------------------------------ *)
    (* +0x7e..+0x8a: epilogue -- restore ra/s0/s1/s2/s3, pop frame, ret.   *)
    (* ------------------------------------------------------------------ *)
    (* frame-cell values and addresses in terms of sp0. *)
    assert (HA0ra : A0 !!! Regidx (mword_of_int 1 : mword 5) = m !!! Regidx (mword_of_int 1 : mword 5))
      by (rewrite /A0 upd_ne; [reflexivity | vm_compute; discriminate]).
    assert (HA0s0 : A0 !!! Regidx (mword_of_int 8 : mword 5) = m !!! Regidx (mword_of_int 8 : mword 5))
      by (rewrite /A0 upd_ne; [reflexivity | vm_compute; discriminate]).
    assert (HA0s1 : A0 !!! Regidx (mword_of_int 9 : mword 5) = m !!! Regidx (mword_of_int 9 : mword 5))
      by (rewrite /A0 upd_ne; [reflexivity | vm_compute; discriminate]).
    assert (HA0s2 : A0 !!! Regidx (mword_of_int 18 : mword 5) = m !!! Regidx (mword_of_int 18 : mword 5))
      by (rewrite /A0 upd_ne; [reflexivity | vm_compute; discriminate]).
    assert (HA0s3 : A0 !!! Regidx (mword_of_int 19 : mword 5) = m !!! Regidx (mword_of_int 19 : mword 5))
      by (rewrite /A0 upd_ne; [reflexivity | vm_compute; discriminate]).
    iEval (rewrite HcspA0 HA0ra) in "Hr1". iEval (rewrite HcspA0 HA0s0) in "Hr2".
    iEval (rewrite HcspA0 HA0s1) in "Hr3". iEval (rewrite HcspA0 HA0s2) in "Hr4".
    iEval (rewrite HcspA0 HA0s3) in "Hr5".
    (* sp = spd in the epilogue maps. *)
    assert (Hsp_E3 : E3 !!! Regidx csp_rs1 = spd).
    { rewrite /E3 upd_ne; [| vm_compute; discriminate]. rewrite /E2 upd_ne; [| vm_compute; discriminate].
      rewrite /E1 upd_ne; [| vm_compute; discriminate]. rewrite /E0 upd_ne; [| vm_compute; discriminate].
      exact Hsp_m'. }
    (* +0x7e c.ldsp ra,40 *)
    iPoseProof (sdi_7e with "Htext") as "Hi7e".
    iApply (wp_cldsp_s_sconf γ Φ (mword_of_int (SD + 0x7e)) (mword_of_int 5 : mword 6) (mword_of_int 1 : mword 5)
              E3 (av - 6)%nat (m !!! Regidx (mword_of_int 1 : mword 5))
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi7e [Hr1] [-]").
    { iEval (rewrite Hsp_E3). iExact "Hr1". }
    iIntros "Hcg Hpc Hr1".
    set (E4 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 1 : mword 5))]> E3).
    change (<[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 1 : mword 5))]> E3) with E4.
    assert (Hpc80 : add_vec_int (mword_of_int (SD + 0x7e) : mword 64) 2 = mword_of_int (SD + 0x80)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc80) in "Hpc".
    assert (Hsp_E4 : E4 !!! Regidx csp_rs1 = spd) by (rewrite /E4 upd_ne; [exact Hsp_E3 | vm_compute; discriminate]).
    (* +0x80 c.ldsp s0,32 *)
    iPoseProof (sdi_80 with "Htext") as "Hi80".
    iApply (wp_cldsp_s_sconf γ Φ (mword_of_int (SD + 0x80)) (mword_of_int 4 : mword 6) (mword_of_int 8 : mword 5)
              E4 (av - 6)%nat (m !!! Regidx (mword_of_int 8 : mword 5))
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi80 [Hr2] [-]").
    { iEval (rewrite Hsp_E4). iExact "Hr2". }
    iIntros "Hcg Hpc Hr2".
    set (E5 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 8 : mword 5))]> E4).
    change (<[Regidx (mword_of_int 8 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 8 : mword 5))]> E4) with E5.
    assert (Hpc82 : add_vec_int (mword_of_int (SD + 0x80) : mword 64) 2 = mword_of_int (SD + 0x82)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc82) in "Hpc".
    assert (Hsp_E5 : E5 !!! Regidx csp_rs1 = spd) by (rewrite /E5 upd_ne; [exact Hsp_E4 | vm_compute; discriminate]).
    (* +0x82 c.ldsp s1,24 *)
    iPoseProof (sdi_82 with "Htext") as "Hi82".
    iApply (wp_cldsp_s_sconf γ Φ (mword_of_int (SD + 0x82)) (mword_of_int 3 : mword 6) (mword_of_int 9 : mword 5)
              E5 (av - 6)%nat (m !!! Regidx (mword_of_int 9 : mword 5))
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi82 [Hr3] [-]").
    { iEval (rewrite Hsp_E5). iExact "Hr3". }
    iIntros "Hcg Hpc Hr3".
    set (E6 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 9 : mword 5))]> E5).
    change (<[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 9 : mword 5))]> E5) with E6.
    assert (Hpc84 : add_vec_int (mword_of_int (SD + 0x82) : mword 64) 2 = mword_of_int (SD + 0x84)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc84) in "Hpc".
    assert (Hsp_E6 : E6 !!! Regidx csp_rs1 = spd) by (rewrite /E6 upd_ne; [exact Hsp_E5 | vm_compute; discriminate]).
    (* +0x84 c.ldsp s2,16 *)
    iPoseProof (sdi_84 with "Htext") as "Hi84".
    iApply (wp_cldsp_s_sconf γ Φ (mword_of_int (SD + 0x84)) (mword_of_int 2 : mword 6) (mword_of_int 18 : mword 5)
              E6 (av - 6)%nat (m !!! Regidx (mword_of_int 18 : mword 5))
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi84 [Hr4] [-]").
    { iEval (rewrite Hsp_E6). iExact "Hr4". }
    iIntros "Hcg Hpc Hr4".
    set (E7 := <[Regidx (mword_of_int 18 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 18 : mword 5))]> E6).
    change (<[Regidx (mword_of_int 18 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 18 : mword 5))]> E6) with E7.
    assert (Hpc86 : add_vec_int (mword_of_int (SD + 0x84) : mword 64) 2 = mword_of_int (SD + 0x86)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc86) in "Hpc".
    assert (Hsp_E7 : E7 !!! Regidx csp_rs1 = spd) by (rewrite /E7 upd_ne; [exact Hsp_E6 | vm_compute; discriminate]).
    (* +0x86 c.ldsp s3,8 *)
    iPoseProof (sdi_86 with "Htext") as "Hi86".
    iApply (wp_cldsp_s_sconf γ Φ (mword_of_int (SD + 0x86)) (mword_of_int 1 : mword 6) (mword_of_int 19 : mword 5)
              E7 (av - 6)%nat (m !!! Regidx (mword_of_int 19 : mword 5))
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi86 [Hr5] [-]").
    { iEval (rewrite Hsp_E7). iExact "Hr5". }
    iIntros "Hcg Hpc Hr5".
    set (E8 := <[Regidx (mword_of_int 19 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 19 : mword 5))]> E7).
    change (<[Regidx (mword_of_int 19 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 19 : mword 5))]> E7) with E8.
    assert (Hpc88 : add_vec_int (mword_of_int (SD + 0x86) : mword 64) 2 = mword_of_int (SD + 0x88)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc88) in "Hpc".
    assert (Hsp_E8 : E8 !!! Regidx csp_rs1 = spd) by (rewrite /E8 upd_ne; [exact Hsp_E7 | vm_compute; discriminate]).
    (* +0x88 c.addi16sp sp,48 : pop the frame *)
    iPoseProof (sdi_88 with "Htext") as "Hi88".
    assert (Hspd6 : pa_stk sp0 6 = spd).
    { rewrite /spd. unfold pa_stk, add_vec_int. apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    assert (Hpopsp : add_vec spd (sign_extend' 64 (caddi16sp_imm (mword_of_int 3 : mword 6))) = sp0).
    { rewrite /spd sched_addvA.
      assert (HAB : add_vec (sign_extend' 64 (caddi16sp_imm (mword_of_int 61 : mword 6))) (sign_extend' 64 (caddi16sp_imm (mword_of_int 3 : mword 6))) = mword_of_int 0)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite HAB. apply kv_addv_zero. }
    iEval (rewrite Hsp_E3) in "Hr1". iEval (rewrite Hsp_E4) in "Hr2".
    iEval (rewrite Hsp_E5) in "Hr3". iEval (rewrite Hsp_E6) in "Hr4".
    iEval (rewrite Hsp_E7) in "Hr5".
    iAssert (stack_own sp0 6) with "[Hr1 Hr2 Hr3 Hr4 Hr5 Hgap]" as "Hframe6".
    { rewrite stack_own_slots. cbn [seq].
      iSplitL "Hr1". { iExists _. iEval (rewrite Hb1). iExact "Hr1". }
      iSplitL "Hr2". { iExists _. iEval (rewrite Hb2). iExact "Hr2". }
      iSplitL "Hr3". { iExists _. iEval (rewrite Hb3). iExact "Hr3". }
      iSplitL "Hr4". { iExists _. iEval (rewrite Hb4). iExact "Hr4". }
      iSplitL "Hr5". { iExists _. iEval (rewrite Hb5). iExact "Hr5". }
      iSplitL "Hgap". { iExists _. iExact "Hgap". }
      done. }
    assert (Hpop_prem : E8 !!! Regidx csp_rs1 = pa_stk (add_vec (E8 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 3 : mword 6)))) 6).
    { rewrite Hsp_E8 Hpopsp Hspd6. reflexivity. }
    iApply (wp_caddi16sp_pop_s_sconf γ Φ (mword_of_int (SD + 0x88)) (mword_of_int 3 : mword 6) E8 (av - 6)%nat 6
              Hpop_prem
              with "Hcg Hpc Hi88 [Hframe6] [-]").
    { rewrite Hsp_E8 Hpopsp. iExact "Hframe6". }
    iIntros "Hcg Hpc".
    set (Ef := <[Regidx csp_rs1 := regval_into_reg (add_vec (E8 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 3 : mword 6))))]> E8).
    change (<[Regidx csp_rs1 := regval_into_reg (add_vec (E8 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 3 : mword 6))))]> E8) with Ef.
    assert (Havk : ((av - 6) + 6)%nat = av) by lia.
    iEval (rewrite Havk) in "Hcg".
    assert (Hpc8a : add_vec_int (mword_of_int (SD + 0x88) : mword 64) 2 = mword_of_int (SD + 0x8a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc8a) in "Hpc".
    (* +0x8a c.ret *)
    assert (HEfra : Ef !!! Regidx (mword_of_int 1 : mword 5) = m !!! Regidx (mword_of_int 1 : mword 5)).
    { rewrite /Ef upd_ne; [| vm_compute; discriminate].
      rewrite /E8 upd_ne; [| vm_compute; discriminate]. rewrite /E7 upd_ne; [| vm_compute; discriminate].
      rewrite /E6 upd_ne; [| vm_compute; discriminate]. rewrite /E5 upd_ne; [| vm_compute; discriminate].
      rewrite /E4 upd_eq. reflexivity. }
    iPoseProof (sdi_8a with "Htext") as "Hi8a".
    iApply (wp_cret_s_sconf γ Φ (mword_of_int (SD + 0x8a)) (mword_of_int 1 : mword 5) Ef av
              ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi8a [-]").
    iIntros "Hcg Hpc".
    assert (Hret_final : ret_pc (Ef !!! Regidx (mword_of_int 1 : mword 5)) = ret_tgt)
      by (rewrite HEfra; reflexivity).
    iEval (rewrite Hret_final) in "Hpc".
    (* ------------------------------------------------------------------ *)
    (* Postcondition.                                                      *)
    (* ------------------------------------------------------------------ *)
    (* threading helper for the untouched callee-saved registers s4..s11. *)
    assert (Hthread : forall c : mword 5, is_cs_idx c = true ->
      Regidx c ≠ Regidx (mword_of_int 1) -> Regidx c ≠ Regidx (mword_of_int 8) ->
      Regidx c ≠ Regidx (mword_of_int 9) -> Regidx c ≠ Regidx (mword_of_int 10) ->
      Regidx c ≠ Regidx (mword_of_int 11) -> Regidx c ≠ Regidx (mword_of_int 14) ->
      Regidx c ≠ Regidx (mword_of_int 15) -> Regidx c ≠ Regidx (mword_of_int 18) ->
      Regidx c ≠ Regidx (mword_of_int 19) -> Regidx c ≠ Regidx csp_rs1 ->
      Mc !!! Regidx c = m !!! Regidx c).
    { intros c Hcs H1 H8 H9 H10 H11 H14 H15 H18 H19 Hsp.
      rewrite /Mc upd_ne; [| exact H1].
      rewrite /D14 upd_ne; [| exact H10]. rewrite /D13 upd_ne; [| exact H11].
      rewrite /D12 upd_ne; [| exact H11]. rewrite /D11 upd_ne; [| exact H11].
      rewrite /D10 upd_ne; [| exact H15]. rewrite /D9 upd_ne; [| exact H15].
      rewrite /D8 upd_ne; [| exact H15]. rewrite /D7 upd_ne; [| exact H15].
      rewrite /D6 upd_ne; [| exact H19]. rewrite /D5 upd_ne; [| exact H15].
      rewrite /D4 upd_ne; [| exact H15]. rewrite /D3 upd_ne; [| exact H15].
      rewrite /D2 upd_ne; [| exact H18]. rewrite /D1 upd_ne; [| exact H18].
      rewrite /D0 upd_ne; [| exact H15].
      rewrite /C11 upd_ne; [| exact H15]. rewrite /C10 upd_ne; [| exact H15].
      rewrite /C9 upd_ne; [| exact H15]. rewrite /C8 upd_ne; [| exact H14].
      rewrite /C7 upd_ne; [| exact H15]. rewrite /C6 upd_ne; [| exact H14].
      rewrite /C5 upd_ne; [| exact H15]. rewrite /C4 upd_ne; [| exact H14].
      rewrite /C3 upd_ne; [| exact H14]. rewrite /C2 upd_ne; [| exact H15].
      rewrite /C1 upd_ne; [| exact H15]. rewrite /C0 upd_ne; [| exact H15].
      rewrite (callee_saved_lookup Hcs_mh c Hcs).
      rewrite /B1 upd_ne; [| exact H1]. rewrite /B0 upd_ne; [| exact H9].
      rewrite (callee_saved_lookup Hcs_mp c Hcs).
      rewrite /A2 upd_ne; [| exact H1]. rewrite /A1 upd_ne; [| exact H8].
      rewrite /A0 upd_ne; [| exact Hsp]. reflexivity. }
    (* per-register threading for s4..s11: Ef -> m' -> Mc -> m. *)
    assert (Hs_final : forall c : mword 5, is_cs_idx c = true ->
      m' !!! Regidx c = Mc !!! Regidx c ->
      Regidx c ≠ Regidx (mword_of_int 1) -> Regidx c ≠ Regidx (mword_of_int 8) ->
      Regidx c ≠ Regidx (mword_of_int 9) -> Regidx c ≠ Regidx (mword_of_int 10) ->
      Regidx c ≠ Regidx (mword_of_int 11) -> Regidx c ≠ Regidx (mword_of_int 14) ->
      Regidx c ≠ Regidx (mword_of_int 15) -> Regidx c ≠ Regidx (mword_of_int 18) ->
      Regidx c ≠ Regidx (mword_of_int 19) -> Regidx c ≠ Regidx csp_rs1 ->
      Ef !!! Regidx c = m !!! Regidx c).
    { intros c Hcs Hmm H1 H8 H9 H10 H11 H14 H15 H18 H19 Hsp.
      rewrite /Ef upd_ne; [| exact Hsp].
      rewrite /E8 upd_ne; [| exact H19]. rewrite /E7 upd_ne; [| exact H18].
      rewrite /E6 upd_ne; [| exact H9]. rewrite /E5 upd_ne; [| exact H8].
      rewrite /E4 upd_ne; [| exact H1]. rewrite /E3 upd_ne; [| exact H18].
      rewrite /E2 upd_ne; [| exact H15]. rewrite /E1 upd_ne; [| exact H15].
      rewrite /E0 upd_ne; [| exact H15].
      rewrite Hmm. apply Hthread; assumption. }
    iApply ("Hcont" $! Ef ch' with "[%] Hcg Hpc Hheld' Hcpu [Hctxback] [Hvc']").
    { (* callee_saved m Ef *)
      assert (Hf_sp : Ef !!! Regidx csp_rs1 = m !!! Regidx csp_rs1)
        by (rewrite /Ef upd_eq Hsp_E8; exact Hpopsp).
      assert (Hf_tp : Ef !!! Regidx (mword_of_int 4 : mword 5) = m !!! Regidx (mword_of_int 4 : mword 5)).
      { rewrite /Ef upd_ne; [| vm_compute; discriminate].
        rewrite /E8 upd_ne; [| vm_compute; discriminate]. rewrite /E7 upd_ne; [| vm_compute; discriminate].
        rewrite /E6 upd_ne; [| vm_compute; discriminate]. rewrite /E5 upd_ne; [| vm_compute; discriminate].
        rewrite /E4 upd_ne; [| vm_compute; discriminate]. rewrite /E3 upd_ne; [| vm_compute; discriminate].
        rewrite /E2 upd_ne; [| vm_compute; discriminate]. rewrite /E1 upd_ne; [| vm_compute; discriminate].
        rewrite /E0 upd_ne; [| vm_compute; discriminate]. rewrite Htpv. symmetry. exact Htp. }
      assert (Hf_s0 : Ef !!! Regidx (mword_of_int 8 : mword 5) = m !!! Regidx (mword_of_int 8 : mword 5)).
      { rewrite /Ef upd_ne; [| vm_compute; discriminate].
        rewrite /E8 upd_ne; [| vm_compute; discriminate]. rewrite /E7 upd_ne; [| vm_compute; discriminate].
        rewrite /E6 upd_ne; [| vm_compute; discriminate]. rewrite /E5 upd_eq. reflexivity. }
      assert (Hf_s1 : Ef !!! Regidx (mword_of_int 9 : mword 5) = m !!! Regidx (mword_of_int 9 : mword 5)).
      { rewrite /Ef upd_ne; [| vm_compute; discriminate].
        rewrite /E8 upd_ne; [| vm_compute; discriminate]. rewrite /E7 upd_ne; [| vm_compute; discriminate].
        rewrite /E6 upd_eq. reflexivity. }
      assert (Hf_s2 : Ef !!! Regidx (mword_of_int 18 : mword 5) = m !!! Regidx (mword_of_int 18 : mword 5)).
      { rewrite /Ef upd_ne; [| vm_compute; discriminate].
        rewrite /E8 upd_ne; [| vm_compute; discriminate]. rewrite /E7 upd_eq. reflexivity. }
      assert (Hf_s3 : Ef !!! Regidx (mword_of_int 19 : mword 5) = m !!! Regidx (mword_of_int 19 : mword 5)).
      { rewrite /Ef upd_ne; [| vm_compute; discriminate]. rewrite /E8 upd_eq. reflexivity. }
      assert (Hf_s4 : Ef !!! Regidx (mword_of_int 20 : mword 5) = m !!! Regidx (mword_of_int 20 : mword 5))
        by (apply Hs_final; (first [ vm_compute; reflexivity | exact Hm20 | vm_compute; discriminate ])).
      assert (Hf_s5 : Ef !!! Regidx (mword_of_int 21 : mword 5) = m !!! Regidx (mword_of_int 21 : mword 5))
        by (apply Hs_final; (first [ vm_compute; reflexivity | exact Hm21 | vm_compute; discriminate ])).
      assert (Hf_s6 : Ef !!! Regidx (mword_of_int 22 : mword 5) = m !!! Regidx (mword_of_int 22 : mword 5))
        by (apply Hs_final; (first [ vm_compute; reflexivity | exact Hm22 | vm_compute; discriminate ])).
      assert (Hf_s7 : Ef !!! Regidx (mword_of_int 23 : mword 5) = m !!! Regidx (mword_of_int 23 : mword 5))
        by (apply Hs_final; (first [ vm_compute; reflexivity | exact Hm23 | vm_compute; discriminate ])).
      assert (Hf_s8 : Ef !!! Regidx (mword_of_int 24 : mword 5) = m !!! Regidx (mword_of_int 24 : mword 5))
        by (apply Hs_final; (first [ vm_compute; reflexivity | exact Hm24 | vm_compute; discriminate ])).
      assert (Hf_s9 : Ef !!! Regidx (mword_of_int 25 : mword 5) = m !!! Regidx (mword_of_int 25 : mword 5))
        by (apply Hs_final; (first [ vm_compute; reflexivity | exact Hm25 | vm_compute; discriminate ])).
      assert (Hf_s10 : Ef !!! Regidx (mword_of_int 26 : mword 5) = m !!! Regidx (mword_of_int 26 : mword 5))
        by (apply Hs_final; (first [ vm_compute; reflexivity | exact Hm26 | vm_compute; discriminate ])).
      assert (Hf_s11 : Ef !!! Regidx (mword_of_int 27 : mword 5) = m !!! Regidx (mword_of_int 27 : mword 5))
        by (apply Hs_final; (first [ vm_compute; reflexivity | exact Hm27 | vm_compute; discriminate ])).
      unfold callee_saved. repeat split; assumption. }
    { (* own_ctx (p_context pj) *)
      rewrite /own_ctx. iExists (callee_img Mc). iSplit.
      { iPureIntro. unfold callee_img, ctx_regs. reflexivity. }
      iExact "Hctxback". }
    { (* ▷ sched_vc (a_cpu_ctx cid) *)
      rewrite /sched_vc. iEval (rewrite Hcret) in "Hvc'". iExact "Hvc'". }
  Qed.

End ProofSched.

End SchedProof.
