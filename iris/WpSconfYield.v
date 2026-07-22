(* WpSconfYield.v -- the whole-function sconf-tier proof of yield()
   (SpecYield.v), as a sealed functor over its callees' interfaces
   (myproc, acquire, sched, release).  See claude-notes/projects/yield-sched.md.

   yield() @ 0x80001eda: the 32-byte frame prologue (byte-identical to
   myproc's) / p = myproc() / acquire(&p->lock) / p->state = RUNNABLE (the
   c.sw) / sched() / release(&p->lock) / epilogue.  The proof threads the
   scheduler-swtch protocol resources (SchedCtx.v): it acquires proc j's lock,
   flips the state to RUNNABLE, hands sched the parking-proc payload
   (proc_held + cpu_cells), and -- once dispatched again -- releases with the
   process RUNNING (needs_ctx RUNNING = false, so the lock slot is emp). *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExtras.
Require Import WpMmodeLeafBase.
Require Import WpIntenaBits.
Require Import RegFile.
Require Import SmodeCore.
Require Import StackOwn CalleeSaved.
Require Import WpSmodeIntr.
Require Import VcGen WpSconfAlu WpSconfMem WpSconfCtl.
Require Import WpLock.
Require Import WpMycpu.
Require Import ProcGeom.
Require Import SchedCtx.
Require Import KernelRvcDecode.
Require Import WpYieldDecode.
Require Import SpecMyproc SpecAcquire SpecSched SpecRelease SpecYield.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Import Defs.
Local Open Scope Z_scope.

(* ===================================================================== *)
(* Pure helpers: address arithmetic + the two noff-cell value forms.      *)
(* ===================================================================== *)

Lemma yd_addv_unsigned (x y : mword 64) :
  bv_unsigned (add_vec x y) = bv_wrap 64 (bv_unsigned x + bv_unsigned y).
Proof.
  unfold add_vec, Operators_mwords.word_binop, Operators_mwords.with_word',
    SailStdpp.Values.with_word, to_word, get_word, MachineWord.MachineWord.add.
  rewrite bv_add_unsigned. reflexivity.
Qed.

Lemma yd_addv_zero_l (x : mword 64) : add_vec zero_reg x = x.
Proof.
  apply bv_eq. rewrite yd_addv_unsigned.
  assert (Hz : bv_unsigned (zero_reg : mword 64) = 0) by (vm_compute; reflexivity).
  rewrite Hz Z.add_0_l. apply bv_wrap_bv_unsigned.
Qed.

(* acquire's noff output (push_off's +1 store over the entry value 0) is
   exactly [mword_of_int 1] (closed; needed for sched's cpu_cells). *)
Lemma yd_acq_noff_one :
  (autocast (T := mword) (subrange_vec_dec
     (sign_extend' 64 (subrange_vec_dec (add_vec (sign_extend' 64 (mword_of_int 0 : mword 32))
        (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6)))) 31 0))
     (Z.sub (Z.mul 4 8) 1) 0) : mword 32) = (mword_of_int 1 : mword 32).
Proof. vm_compute. reflexivity. Qed.

(* release's noff output (pop_off's -1 store over the entry value 1) is
   exactly [mword_of_int 0] (closed; needed for yield's postcondition). *)
Lemma yd_rel_noff_zero :
  (autocast (T := mword) (subrange_vec_dec
     (sign_extend' 64 (subrange_vec_dec (add_vec (sign_extend' 64 (mword_of_int 1 : mword 32))
        (sign_extend' 64 (sign_extend' 12 (mword_of_int 63 : mword 6)))) 31 0))
     (Z.sub (Z.mul 4 8) 1) 0) : mword 32) = (mword_of_int 0 : mword 32).
Proof. vm_compute. reflexivity. Qed.

(* the c.li a5,3 value truncated to 32 bits is RUNNABLE = mword_of_int 3. *)
Lemma yd_runnable :
  trunc32 (add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 3 : mword 6))) : mword 64)
  = (mword_of_int 3 : mword 32).
Proof. vm_compute. reflexivity. Qed.

Module YieldProof (Myproc : MYPROC) (Acquire : ACQUIRE) (Sched : SCHED) (Release : RELEASE) : YIELD.

Section WpSconfYield.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ}.
  Context `{CID : CpuId}.

  (* generic register-map peel over the proof's [set]-chain (hit-first). *)
  Local Ltac yd_peel :=
    repeat first
      [ rewrite upd_eq
      | rewrite upd_ne; [| vm_compute; discriminate]
      | lazymatch goal with |- ?M !!! _ = _ => is_var M; progress unfold M end ].

  Lemma wp_yield_sconf (γ : gname) (root_ppn : mword 44) (Φ : mval -> iProp Σ)
      (γs : list gname) (j : nat) (γl : gname)
      (m : regfile) (av : nat)
    : wp_yield_sconf_body γ root_ppn Φ γs j γl m av.
  Proof.
    cbv beta delta [wp_yield_sconf_body].
    intros pcE pj ret_tgt Htp Hj Hgl Hal Hav.
    pose (sp0 := (m !!! Regidx csp_rs1 : mword 64)).
    iIntros "Hsc Hhs Hcg Hcnt Htlbinv #Htext Hpc #Hprocs Hcur Hnoff0 Hint0 Hlk0 Hown Hvc Hcont".
    iDestruct "Hint0" as (iv0) "Hint0".
    (* ------------------------------------------------------------------ *)
    (* Prologue: 32-byte frame (push 4), save ra/s0/s1 (mirror myproc).   *)
    (* ------------------------------------------------------------------ *)
    set (spd := add_vec sp0 (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6)))).
    set (A0 := <[Regidx csp_rs1 := regval_into_reg
        (add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))))]> m).
    assert (HcspA0 : A0 !!! Regidx csp_rs1 = spd) by (rewrite /A0 upd_eq; reflexivity).
    assert (Hspd4 : pa_stk sp0 4 = spd).
    { rewrite /spd. unfold pa_stk, add_vec_int. apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    assert (Hspm : m !!! Regidx csp_rs1 = sp0) by reflexivity.
    assert (Hpush : add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))) = pa_stk (m !!! Regidx csp_rs1) 4).
    { unfold pa_stk, add_vec_int. apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    iPoseProof (ydi_00 with "Htext") as "Hi00".
    iApply (wp_caddi_sp_push_s_sconf γ root_ppn Φ pcE (mword_of_int 32 : mword 6) m av 4 ltac:(lia) Hpush
              with "Hsc Hhs Hcg Htlbinv Hpc Hi00 [-]").
    iIntros "Hhs Hsc Hcg Hframe Htlbinv Hpc".
    iEval (rewrite Hspm) in "Hframe".
    change (<[Regidx csp_rs1 := regval_into_reg
        (add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))))]> m) with A0.
    assert (Hpc02 : add_vec_int (pcE : mword 64) 2 = mword_of_int (YD + 0x02)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc02) in "Hpc".
    iEval (rewrite stack_own_slots; cbn [seq]) in "Hframe".
    iDestruct "Hframe" as "(S1c & S2c & S3c & S4c & _)".
    iDestruct "S1c" as (vr24) "Hr24".
    iDestruct "S2c" as (vr16) "Hr16".
    iDestruct "S3c" as (vr8) "Hr8".
    iDestruct "S4c" as (vgap) "Hgap".
    assert (Hb1 : pa_stk sp0 1
                   = add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000")))).
    { rewrite /spd. unfold sp0, pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb2 : pa_stk sp0 2
                   = add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000")))).
    { rewrite /spd. unfold sp0, pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb3 : pa_stk sp0 3
                   = add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000")))).
    { rewrite /spd. unfold sp0, pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    (* +0x02/0x04/0x06: c.sdsp ra/s0/s1 *)
    iPoseProof (ydi_02 with "Htext") as "Hi02".
    iApply (wp_csdsp_s_sconf γ root_ppn Φ (mword_of_int (YD + 0x02)) (mword_of_int 3 : mword 6) (mword_of_int 1 : mword 5)
              A0 (av - 4)%nat vr24 with "Hsc Hhs Hcg Htlbinv Hpc Hi02 [Hr24] [-]").
    { iEval (rewrite HcspA0 -Hb1). iExact "Hr24". }
    iIntros "Hhs Hsc Hcg Htlbinv Hpc Hr24".
    assert (Hpc04 : add_vec_int (mword_of_int (YD + 0x02) : mword 64) 2 = mword_of_int (YD + 0x04)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc04) in "Hpc".
    iPoseProof (ydi_04 with "Htext") as "Hi04".
    iApply (wp_csdsp_s_sconf γ root_ppn Φ (mword_of_int (YD + 0x04)) (mword_of_int 2 : mword 6) (mword_of_int 8 : mword 5)
              A0 (av - 4)%nat vr16 with "Hsc Hhs Hcg Htlbinv Hpc Hi04 [Hr16] [-]").
    { iEval (rewrite HcspA0 -Hb2). iExact "Hr16". }
    iIntros "Hhs Hsc Hcg Htlbinv Hpc Hr16".
    assert (Hpc06 : add_vec_int (mword_of_int (YD + 0x04) : mword 64) 2 = mword_of_int (YD + 0x06)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc06) in "Hpc".
    iPoseProof (ydi_06 with "Htext") as "Hi06".
    iApply (wp_csdsp_s_sconf γ root_ppn Φ (mword_of_int (YD + 0x06)) (mword_of_int 1 : mword 6) (mword_of_int 9 : mword 5)
              A0 (av - 4)%nat vr8 with "Hsc Hhs Hcg Htlbinv Hpc Hi06 [Hr8] [-]").
    { iEval (rewrite HcspA0 -Hb3). iExact "Hr8". }
    iIntros "Hhs Hsc Hcg Htlbinv Hpc Hr8".
    assert (Hpc08 : add_vec_int (mword_of_int (YD + 0x06) : mword 64) 2 = mword_of_int (YD + 0x08)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc08) in "Hpc".
    (* +0x08: c.addi4spn s0,sp,32 *)
    iPoseProof (ydi_08 with "Htext") as "Hi08".
    iApply (wp_caddi4spn_s_sconf γ root_ppn Φ (mword_of_int (YD + 0x08)) (Cregidx (mword_of_int 0)) (mword_of_int 8 : mword 8) (mword_of_int 8 : mword 5)
              A0 (av - 4)%nat
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi08 [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc".
    set (A1 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg
        (add_vec (A0 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8))))]> A0).
    change (<[Regidx (mword_of_int 8 : mword 5) := regval_into_reg
        (add_vec (A0 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8))))]> A0) with A1.
    assert (Hpc0a : add_vec_int (mword_of_int (YD + 0x08) : mword 64) 2 = mword_of_int (YD + 0x0a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc0a) in "Hpc".
    (* ------------------------------------------------------------------ *)
    (* +0x0a: jal myproc -> a0 = proc_addr j; noff/intena/cur_proc round.  *)
    (* ------------------------------------------------------------------ *)
    iPoseProof (ydi_0a with "Htext") as "Hi0a".
    iApply (wp_jal_s_sconf γ root_ppn Φ (mword_of_int (YD + 0x0a)) (mword_of_int 1 : mword 5) (mword_of_int 2095648 : mword 21)
              A1 (av - 4)%nat
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; reflexivity)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi0a [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc".
    set (A2 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (YD + 0x0a) : mword 64) 4)]> A1).
    change (<[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (YD + 0x0a) : mword 64) 4)]> A1) with A2.
    assert (Hpcmp : add_vec (mword_of_int (YD + 0x0a) : mword 64) (sign_extend' 64 (mword_of_int 2095648 : mword 21))
                    = mword_of_int KernelSyms.myproc) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpcmp) in "Hpc".
    assert (HA2ra : A2 !!! Regidx (mword_of_int 1 : mword 5) = add_vec_int (mword_of_int (YD + 0x0a) : mword 64) 4)
      by (rewrite /A2 upd_eq; reflexivity).
    assert (HtpA2 : A2 !!! Regidx (mword_of_int 4 : mword 5) = cid_word).
    { rewrite /A2 upd_ne; [| vm_compute; discriminate].
      rewrite /A1 upd_ne; [| vm_compute; discriminate].
      rewrite /A0 upd_ne; [| vm_compute; discriminate]. exact Htp. }
    iApply (Myproc.wp_myproc_sconf γ root_ppn Φ A2 (av - 4)%nat 0 (mword_of_int 0) iv0 (proc_addr j)
              HtpA2
              ltac:(split; intros _; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(rewrite HA2ra; vm_compute; reflexivity)
              ltac:(lia)
              with "Hsc Hhs Hcg Hcnt Htlbinv Htext Hpc Hnoff0 Hint0 Hcur [-]").
    iIntros (ms mp) "%Hmsf Hhs Hsc Hcg Hcnt Htlbinv Hpc %Hmp Hnoff Hint Hcur".
    destruct Hmp as [Hcs_mp Ha0_mp].
    set (iem := (if eq_vec (sign_extend' 64 (mword_of_int 0 : mword 32)) zero_reg then po_intena_val ms else iv0)).
    change (if eq_vec (sign_extend' 64 (mword_of_int 0 : mword 32)) zero_reg then po_intena_val ms else iv0) with iem.
    assert (Hpc0e : update_vec_dec (add_vec (A2 !!! Regidx (mword_of_int 1 : mword 5)) (sign_extend' 64 (zeros' 12))) 0 ('b"0")
                    = mword_of_int (YD + 0x0e)) by (rewrite HA2ra; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc0e) in "Hpc".
    (* +0x0e: c.mv s1,a0 : s1 := a0 = proc_addr j *)
    iPoseProof (ydi_0e with "Htext") as "Hi0e".
    iApply (wp_cmv_s_sconf γ root_ppn Φ (mword_of_int (YD + 0x0e)) (mword_of_int 9 : mword 5) (mword_of_int 10 : mword 5)
              mp (av - 4)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi0e [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc".
    set (B0 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg
        (add_vec zero_reg (mp !!! Regidx (mword_of_int 10 : mword 5)))]> mp).
    change (<[Regidx (mword_of_int 9 : mword 5) := regval_into_reg
        (add_vec zero_reg (mp !!! Regidx (mword_of_int 10 : mword 5)))]> mp) with B0.
    assert (Hpc10 : add_vec_int (mword_of_int (YD + 0x0e) : mword 64) 2 = mword_of_int (YD + 0x10)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc10) in "Hpc".
    (* +0x10: jal acquire *)
    iPoseProof (ydi_10 with "Htext") as "Hi10".
    iApply (wp_jal_s_sconf γ root_ppn Φ (mword_of_int (YD + 0x10)) (mword_of_int 1 : mword 5) (mword_of_int 2092318 : mword 21)
              B0 (av - 4)%nat
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; reflexivity)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi10 [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc".
    set (B1 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (YD + 0x10) : mword 64) 4)]> B0).
    change (<[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (YD + 0x10) : mword 64) 4)]> B0) with B1.
    assert (Hpcaq : add_vec (mword_of_int (YD + 0x10) : mword 64) (sign_extend' 64 (mword_of_int 2092318 : mword 21))
                    = mword_of_int KernelSyms.acquire) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpcaq) in "Hpc".
    (* ------------------------------------------------------------------ *)
    (* +0x10: acquire(&p->lock) -- take proc j's lock.                     *)
    (* ------------------------------------------------------------------ *)
    assert (Ha0_B1 : B1 !!! Regidx (mword_of_int 10 : mword 5) = proc_addr j).
    { rewrite /B1 upd_ne; [| vm_compute; discriminate].
      rewrite /B0 upd_ne; [| vm_compute; discriminate]. exact Ha0_mp. }
    assert (HtpB1 : B1 !!! Regidx (mword_of_int 4 : mword 5) = cid_word).
    { rewrite /B1 upd_ne; [| vm_compute; discriminate].
      rewrite /B0 upd_ne; [| vm_compute; discriminate].
      rewrite (callee_saved_lookup Hcs_mp (mword_of_int 4) ltac:(vm_compute; reflexivity)). exact HtpA2. }
    assert (HB1ra : B1 !!! Regidx (mword_of_int 1 : mword 5) = add_vec_int (mword_of_int (YD + 0x10) : mword 64) 4)
      by (rewrite /B1 upd_eq; reflexivity).
    iPoseProof (procs_inv_lookup γ root_ppn Φ γs j γl Hgl with "Hprocs") as "#Hislock".
    iApply (Acquire.wp_acquire_sconf γ root_ppn Φ γl "proc"%string
              (proc_lock_res γ root_ppn Φ γs γl (proc_addr j)) B1 (zero_reg : mword 64) (mword_of_int 0) iem 0 (av - 4)%nat
              ltac:(rewrite HtpB1; exact (mycpu_ret_nonzero cid_word tp_ok_cid))
              ltac:(rewrite HB1ra; vm_compute; reflexivity)
              ltac:(lia)
              with "Hsc Hhs Hcg Hcnt Htlbinv Htext Hpc [Hislock] [Hlk0] [Hnoff] [Hint] [-]").
    { iEval (rewrite Ha0_B1). iExact "Hislock". }
    { iEval (rewrite Ha0_B1). iExact "Hlk0". }
    { iEval (rewrite HtpB1). iExact "Hnoff". }
    { iEval (rewrite HtpB1). iExact "Hint". }
    iIntros (ms2 macq) "%Hmsf2 Hhs Hsc Hcg Htlbinv Hpc %Hcs_acq Hlocked HR Hlkcpu Hnoff Hint Hcnt".
    (* reconcile acquire's cell forms back to the cid_word / proc_addr forms. *)
    iEval (rewrite HtpB1 yd_acq_noff_one) in "Hnoff".
    iEval (rewrite HtpB1) in "Hint".
    iEval (rewrite Ha0_B1 HtpB1) in "Hlkcpu".
    assert (Hpc14 : update_vec_dec (add_vec (B1 !!! Regidx (mword_of_int 1 : mword 5)) (sign_extend' 64 (zeros' 12))) 0 ('b"0")
                    = mword_of_int (YD + 0x14)) by (rewrite HB1ra; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc14) in "Hpc".
    (* unpack the lock resource; drop the (possibly ▷-guarded) context slot. *)
    iDestruct (proc_lock_res_elim γ root_ppn Φ γs γl (proc_addr j) with "HR") as (st0 ch0) "(Hstate & Hchan & Hslot)".
    iClear "Hslot".
    (* +0x14: c.li a5,3 *)
    iPoseProof (ydi_14 with "Htext") as "Hi14".
    iApply (wp_cli_s_sconf γ root_ppn Φ (mword_of_int (YD + 0x14)) (mword_of_int 15 : mword 5) (mword_of_int 3 : mword 6)
              (add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 3 : mword 6)))) macq (av - 4)%nat
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) eq_refl
              with "Hsc Hhs Hcg Htlbinv Hpc Hi14 [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc".
    set (C0 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 3 : mword 6))))]> macq).
    change (<[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 3 : mword 6))))]> macq) with C0.
    assert (Hpc16 : add_vec_int (mword_of_int (YD + 0x14) : mword 64) 2 = mword_of_int (YD + 0x16)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc16) in "Hpc".
    (* the s1 value threads (callee-saved) through acquire, so p->state's
       address reconciles to p_state (proc_addr j). *)
    assert (HC0s1 : C0 !!! Regidx (mword_of_int 9 : mword 5) = add_vec zero_reg (proc_addr j)).
    { rewrite /C0 upd_ne; [| vm_compute; discriminate].
      rewrite (callee_saved_lookup Hcs_acq (mword_of_int 9) ltac:(vm_compute; reflexivity)).
      rewrite /B1 upd_ne; [| vm_compute; discriminate]. rewrite /B0 upd_eq Ha0_mp. reflexivity. }
    assert (Hrec_state : add_vec (C0 !!! Regidx (mword_of_int 9 : mword 5)) (sign_extend' 64 (mword_of_int 24 : mword 12))
                         = p_state (proc_addr j)).
    { rewrite HC0s1 yd_addv_zero_l. unfold p_state, state_off.
      assert (H24 : sign_extend' 64 (mword_of_int 24 : mword 12) = (mword_of_int 24 : mword 64)) by (apply bv_eq; vm_compute; reflexivity).
      rewrite H24. reflexivity. }
    assert (Hsv : trunc32 (C0 !!! Regidx (mword_of_int 15 : mword 5)) = RUNNABLE).
    { rewrite /C0 upd_eq. unfold RUNNABLE. exact yd_runnable. }
    (* +0x16: c.sw a5,24(s1) : p->state := RUNNABLE *)
    iPoseProof (ydi_16 with "Htext") as "Hi16".
    iApply (wp_csw_s_sconf γ root_ppn Φ (mword_of_int (YD + 0x16)) (mword_of_int 15 : mword 5) (mword_of_int 9 : mword 5)
              (mword_of_int 24 : mword 12) C0 (av - 4)%nat st0
              with "Hsc Hhs Hcg Htlbinv Hpc Hi16 [Hstate] [-]").
    { iEval (rewrite Hrec_state). iExact "Hstate". }
    iIntros "Hhs Hsc Hcg Htlbinv Hpc Hstate".
    iEval (rewrite Hrec_state Hsv) in "Hstate".
    assert (Hpc18 : add_vec_int (mword_of_int (YD + 0x16) : mword 64) 2 = mword_of_int (YD + 0x18)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc18) in "Hpc".
    (* +0x18: jal sched *)
    iPoseProof (ydi_18 with "Htext") as "Hi18".
    iApply (wp_jal_s_sconf γ root_ppn Φ (mword_of_int (YD + 0x18)) (mword_of_int 1 : mword 5) (mword_of_int 2096940 : mword 21)
              C0 (av - 4)%nat
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; reflexivity)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi18 [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc".
    set (C1 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (YD + 0x18) : mword 64) 4)]> C0).
    change (<[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (YD + 0x18) : mword 64) 4)]> C0) with C1.
    assert (Hpcsd : add_vec (mword_of_int (YD + 0x18) : mword 64) (sign_extend' 64 (mword_of_int 2096940 : mword 21))
                    = mword_of_int KernelSyms.sched) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpcsd) in "Hpc".
    (* ------------------------------------------------------------------ *)
    (* +0x18: sched() -- park; resumes with the process dispatched again.  *)
    (* ------------------------------------------------------------------ *)
    assert (HtpC1 : C1 !!! Regidx (mword_of_int 4 : mword 5) = cid_word).
    { rewrite /C1 upd_ne; [| vm_compute; discriminate].
      rewrite /C0 upd_ne; [| vm_compute; discriminate].
      rewrite (callee_saved_lookup Hcs_acq (mword_of_int 4) ltac:(vm_compute; reflexivity)). exact HtpB1. }
    assert (HC1ra : C1 !!! Regidx (mword_of_int 1 : mword 5) = add_vec_int (mword_of_int (YD + 0x18) : mword 64) 4)
      by (rewrite /C1 upd_eq; reflexivity).
    iApply (Sched.wp_sched_sconf γ root_ppn Φ γs j γl RUNNABLE ch0 C1 (av - 4)%nat
              HtpC1 Hj Hgl (needs_ctx_RUNNABLE) ltac:(rewrite HC1ra; vm_compute; reflexivity) ltac:(lia)
              with "Hsc Hhs Hcg Hcnt Htlbinv Htext Hpc Hprocs [Hlocked Hstate Hchan Hlkcpu] [Hcur Hnoff Hint] Hown Hvc [-]").
    { rewrite /proc_held. iFrame "Hlocked Hstate Hchan Hlkcpu". }
    { rewrite /cpu_cells. iFrame "Hcur Hnoff". iExists _. iExact "Hint". }
    iIntros (msch ch') "%Hcs_sch Hsc Hhs Hcg Hcnt Htlbinv Hpc Hheld' Hcells' Hown' Hvc'".
    iDestruct "Hheld'" as "(Hlocked & Hstate & Hchan & Hlkcpu)".
    iDestruct "Hcells'" as "(Hcur & Hnoff & Hint)".
    iDestruct "Hint" as (iv1) "Hint".
    assert (Hpc1c : update_vec_dec (add_vec (C1 !!! Regidx (mword_of_int 1 : mword 5)) (sign_extend' 64 (zeros' 12))) 0 ('b"0")
                    = mword_of_int (YD + 0x1c)) by (rewrite HC1ra; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc1c) in "Hpc".
    (* the s1 value threads (callee-saved) through sched. *)
    assert (Hs1_msch : msch !!! Regidx (mword_of_int 9 : mword 5) = add_vec zero_reg (proc_addr j)).
    { rewrite (callee_saved_lookup Hcs_sch (mword_of_int 9) ltac:(vm_compute; reflexivity)).
      rewrite /C1 upd_ne; [| vm_compute; discriminate]. exact HC0s1. }
    (* +0x1c: c.mv a0,s1 : a0 := s1 = proc_addr j *)
    iPoseProof (ydi_1c with "Htext") as "Hi1c".
    iApply (wp_cmv_s_sconf γ root_ppn Φ (mword_of_int (YD + 0x1c)) (mword_of_int 10 : mword 5) (mword_of_int 9 : mword 5)
              msch (av - 4)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi1c [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc".
    set (D0 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg
        (add_vec zero_reg (msch !!! Regidx (mword_of_int 9 : mword 5)))]> msch).
    change (<[Regidx (mword_of_int 10 : mword 5) := regval_into_reg
        (add_vec zero_reg (msch !!! Regidx (mword_of_int 9 : mword 5)))]> msch) with D0.
    assert (Hpc1e : add_vec_int (mword_of_int (YD + 0x1c) : mword 64) 2 = mword_of_int (YD + 0x1e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc1e) in "Hpc".
    (* +0x1e: jal release *)
    iPoseProof (ydi_1e with "Htext") as "Hi1e".
    iApply (wp_jal_s_sconf γ root_ppn Φ (mword_of_int (YD + 0x1e)) (mword_of_int 1 : mword 5) (mword_of_int 2092440 : mword 21)
              D0 (av - 4)%nat
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; reflexivity)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi1e [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc".
    set (D1 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (YD + 0x1e) : mword 64) 4)]> D0).
    change (<[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (YD + 0x1e) : mword 64) 4)]> D0) with D1.
    assert (Hpcrl : add_vec (mword_of_int (YD + 0x1e) : mword 64) (sign_extend' 64 (mword_of_int 2092440 : mword 21))
                    = mword_of_int KernelSyms.release) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpcrl) in "Hpc".
    (* ------------------------------------------------------------------ *)
    (* +0x1e: release(&p->lock) -- with the process RUNNING (slot emp).    *)
    (* ------------------------------------------------------------------ *)
    assert (Ha0_D1 : D1 !!! Regidx (mword_of_int 10 : mword 5) = proc_addr j).
    { rewrite /D1 upd_ne; [| vm_compute; discriminate].
      rewrite /D0 upd_eq Hs1_msch !yd_addv_zero_l. reflexivity. }
    assert (HtpD1 : D1 !!! Regidx (mword_of_int 4 : mword 5) = cid_word).
    { rewrite /D1 upd_ne; [| vm_compute; discriminate].
      rewrite /D0 upd_ne; [| vm_compute; discriminate].
      rewrite (callee_saved_lookup Hcs_sch (mword_of_int 4) ltac:(vm_compute; reflexivity)). exact HtpC1. }
    assert (HD1ra : D1 !!! Regidx (mword_of_int 1 : mword 5) = add_vec_int (mword_of_int (YD + 0x1e) : mword 64) 4)
      by (rewrite /D1 upd_eq; reflexivity).
    assert (Hlka : add_vec (D1 !!! Regidx (mword_of_int 10 : mword 5)) (sign_extend' 64 (mword_of_int 0 : mword 12)) = proc_addr j).
    { rewrite Ha0_D1.
      assert (H0 : sign_extend' 64 (mword_of_int 0 : mword 12) = (mword_of_int 0 : mword 64)) by (apply bv_eq; vm_compute; reflexivity).
      rewrite H0. apply kv_addv_zero. }
    (* rebuild the lock resource: RUNNING needs no context, so the slot is emp. *)
    iAssert (proc_lock_res γ root_ppn Φ γs γl (proc_addr j)) with "[Hstate Hchan]" as "HR2".
    { rewrite /proc_lock_res. iExists RUNNING, ch'. iFrame "Hstate Hchan".
      rewrite needs_ctx_RUNNING. done. }
    (* reconcile the lock-cpu / noff / intena cell addresses for release. *)
    assert (Hcpueq_rel : eq_vec (mycpu_ret cid_word) (mycpu_ret (D1 !!! Regidx (mword_of_int 4 : mword 5))) = true)
      by (rewrite HtpD1; apply eq_vec_true_iff; reflexivity).
    assert (Halr_rel : eq_vec (access_vec_dec (update_vec_dec (add_vec (D1 !!! Regidx (mword_of_int 1 : mword 5)) (sign_extend' 64 (zeros' 12))) 0 ('b"0")) 0) ('b"0") = true)
      by (rewrite HD1ra; vm_compute; reflexivity).
    iApply (Release.wp_release_sconf γ root_ppn Φ γl (proc_addr j) "proc"%string
              (proc_lock_res γ root_ppn Φ γs γl (proc_addr j)) D1 (mycpu_ret cid_word) (mword_of_int 1) iv1 0 (av - 4)%nat (dqi := DfracOwn 1)
              Hlka
              Hcpueq_rel
              ltac:(split; intros _; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              Halr_rel
              ltac:(lia)
              with "Hsc Hhs Hcg Htlbinv Htext Hpc Hislock Hlocked HR2 [Hlkcpu] [Hnoff] [Hint] Hcnt [-]").
    { iEval (rewrite Ha0_D1). iExact "Hlkcpu". }
    { iEval (rewrite HtpD1). iExact "Hnoff". }
    { iEval (rewrite HtpD1). iExact "Hint". }
    iIntros (mrel) "Hhs Hsc Hcg Htlbinv Hpc %Hcs_rel Hlkcpu Hnoff Hint Hcnt".
    (* reconcile release's post cells back to the cid_word / proc_addr forms. *)
    iEval (rewrite Ha0_D1) in "Hlkcpu".
    iEval (rewrite HtpD1 yd_rel_noff_zero) in "Hnoff".
    iEval (rewrite HtpD1) in "Hint".
    assert (Hpc22 : update_vec_dec (add_vec (D1 !!! Regidx (mword_of_int 1 : mword 5)) (sign_extend' 64 (zeros' 12))) 0 ('b"0")
                    = mword_of_int (YD + 0x22)) by (rewrite HD1ra; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc22) in "Hpc".
    (* ------------------------------------------------------------------ *)
    (* Epilogue: restore ra/s0/s1, pop the frame, return (mirror myproc).  *)
    (* ------------------------------------------------------------------ *)
    (* sp threads (callee-saved) through all four callees back to the push. *)
    assert (Hcsp_mrel : mrel !!! Regidx csp_rs1 = spd).
    { rewrite (callee_saved_lookup Hcs_rel csp_rs1 ltac:(vm_compute; reflexivity)).
      rewrite /D1 upd_ne; [| vm_compute; discriminate]. rewrite /D0 upd_ne; [| vm_compute; discriminate].
      rewrite (callee_saved_lookup Hcs_sch csp_rs1 ltac:(vm_compute; reflexivity)).
      rewrite /C1 upd_ne; [| vm_compute; discriminate]. rewrite /C0 upd_ne; [| vm_compute; discriminate].
      rewrite (callee_saved_lookup Hcs_acq csp_rs1 ltac:(vm_compute; reflexivity)).
      rewrite /B1 upd_ne; [| vm_compute; discriminate]. rewrite /B0 upd_ne; [| vm_compute; discriminate].
      rewrite (callee_saved_lookup Hcs_mp csp_rs1 ltac:(vm_compute; reflexivity)).
      rewrite /A2 upd_ne; [| vm_compute; discriminate]. rewrite /A1 upd_ne; [| vm_compute; discriminate].
      exact HcspA0. }
    (* the three frame slots still hold the saved ra/s0/s1 (= m's values). *)
    assert (HraA0 : A0 !!! Regidx (mword_of_int 1 : mword 5) = m !!! Regidx (mword_of_int 1 : mword 5))
      by (rewrite /A0 upd_ne; [reflexivity | vm_compute; discriminate]).
    assert (Hs0A0 : A0 !!! Regidx (mword_of_int 8 : mword 5) = m !!! Regidx (mword_of_int 8 : mword 5))
      by (rewrite /A0 upd_ne; [reflexivity | vm_compute; discriminate]).
    assert (Hs1A0 : A0 !!! Regidx (mword_of_int 9 : mword 5) = m !!! Regidx (mword_of_int 9 : mword 5))
      by (rewrite /A0 upd_ne; [reflexivity | vm_compute; discriminate]).
    iEval (rewrite HcspA0 HraA0) in "Hr24".
    iEval (rewrite HcspA0 Hs0A0) in "Hr16".
    iEval (rewrite HcspA0 Hs1A0) in "Hr8".
    (* +0x22: c.ldsp ra,24 *)
    iPoseProof (ydi_22 with "Htext") as "Hi22".
    iApply (wp_cldsp_s_sconf γ root_ppn Φ (mword_of_int (YD + 0x22)) (mword_of_int 3 : mword 6) (mword_of_int 1 : mword 5)
              mrel (av - 4)%nat (m !!! Regidx (mword_of_int 1 : mword 5))
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi22 [Hr24] [-]").
    { iEval (rewrite Hcsp_mrel). iExact "Hr24". }
    iIntros "Hhs Hsc Hcg Htlbinv Hpc Hr24".
    set (E1 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 1 : mword 5))]> mrel).
    change (<[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 1 : mword 5))]> mrel) with E1.
    assert (Hpc24 : add_vec_int (mword_of_int (YD + 0x22) : mword 64) 2 = mword_of_int (YD + 0x24)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc24) in "Hpc".
    assert (HcspE1 : E1 !!! Regidx csp_rs1 = spd)
      by (rewrite /E1 upd_ne; [exact Hcsp_mrel | vm_compute; discriminate]).
    (* +0x24: c.ldsp s0,16 *)
    iPoseProof (ydi_24 with "Htext") as "Hi24".
    iApply (wp_cldsp_s_sconf γ root_ppn Φ (mword_of_int (YD + 0x24)) (mword_of_int 2 : mword 6) (mword_of_int 8 : mword 5)
              E1 (av - 4)%nat (m !!! Regidx (mword_of_int 8 : mword 5))
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi24 [Hr16] [-]").
    { iEval (rewrite HcspE1). iExact "Hr16". }
    iIntros "Hhs Hsc Hcg Htlbinv Hpc Hr16".
    set (E2 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 8 : mword 5))]> E1).
    change (<[Regidx (mword_of_int 8 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 8 : mword 5))]> E1) with E2.
    assert (Hpc26 : add_vec_int (mword_of_int (YD + 0x24) : mword 64) 2 = mword_of_int (YD + 0x26)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc26) in "Hpc".
    assert (HcspE2 : E2 !!! Regidx csp_rs1 = spd)
      by (rewrite /E2 upd_ne; [exact HcspE1 | vm_compute; discriminate]).
    (* +0x26: c.ldsp s1,8 *)
    iPoseProof (ydi_26 with "Htext") as "Hi26".
    iApply (wp_cldsp_s_sconf γ root_ppn Φ (mword_of_int (YD + 0x26)) (mword_of_int 1 : mword 6) (mword_of_int 9 : mword 5)
              E2 (av - 4)%nat (m !!! Regidx (mword_of_int 9 : mword 5))
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi26 [Hr8] [-]").
    { iEval (rewrite HcspE2). iExact "Hr8". }
    iIntros "Hhs Hsc Hcg Htlbinv Hpc Hr8".
    set (E3 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 9 : mword 5))]> E2).
    change (<[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 9 : mword 5))]> E2) with E3.
    assert (Hpc28 : add_vec_int (mword_of_int (YD + 0x26) : mword 64) 2 = mword_of_int (YD + 0x28)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc28) in "Hpc".
    assert (HcspE3 : E3 !!! Regidx csp_rs1 = spd)
      by (rewrite /E3 upd_ne; [exact HcspE2 | vm_compute; discriminate]).
    (* +0x28: c.addi16sp sp,32 -- pop the frame *)
    set (E4 := <[Regidx csp_rs1 := regval_into_reg
        (add_vec (E3 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))))]> E3).
    assert (Hsp0up : add_vec spd (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))) = sp0).
    { rewrite /spd /sp0 po_addv_assoc.
      assert (HAB : add_vec (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6)))
                            (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))) = mword_of_int 0)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite HAB. apply avi0. }
    assert (HE4sp : E4 !!! Regidx csp_rs1 = sp0).
    { rewrite /E4 upd_eq HcspE3. exact Hsp0up. }
    assert (Hwv : add_vec (E3 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))) = sp0).
    { rewrite HcspE3. exact Hsp0up. }
    assert (Hpop : E3 !!! Regidx csp_rs1
                   = pa_stk (add_vec (E3 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6)))) 4).
    { rewrite Hwv HcspE3. symmetry. exact Hspd4. }
    iPoseProof (ydi_28 with "Htext") as "Hi28".
    iAssert (stack_own sp0 4) with "[Hr24 Hr16 Hr8 Hgap]" as "Hframe4".
    { rewrite stack_own_slots. cbn [seq].
      iSplitL "Hr24". { iExists _. iEval (rewrite Hb1 -Hcsp_mrel). iExact "Hr24". }
      iSplitL "Hr16". { iExists _. iEval (rewrite Hb2 -HcspE1). iExact "Hr16". }
      iSplitL "Hr8".  { iExists _. iEval (rewrite Hb3 -HcspE2). iExact "Hr8". }
      iSplitL "Hgap". { iExists _. iExact "Hgap". }
      done. }
    iEval (rewrite -Hwv) in "Hframe4".
    iApply (wp_caddi16sp_pop_s_sconf γ root_ppn Φ (mword_of_int (YD + 0x28)) (mword_of_int 2 : mword 6) E3 (av - 4)%nat 4 Hpop
              with "Hsc Hhs Hcg Htlbinv Hpc Hi28 Hframe4 [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc".
    assert (Hnk : ((av - 4) + 4)%nat = av) by lia.
    iEval (rewrite Hnk) in "Hcg".
    change (<[Regidx csp_rs1 := regval_into_reg
        (add_vec (E3 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))))]> E3) with E4.
    assert (Hpc2a : add_vec_int (mword_of_int (YD + 0x28) : mword 64) 2 = mword_of_int (YD + 0x2a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc2a) in "Hpc".
    (* +0x2a: c.ret *)
    assert (HE4ra : E4 !!! Regidx (mword_of_int 1 : mword 5) = m !!! Regidx (mword_of_int 1 : mword 5)).
    { rewrite /E4 upd_ne; [| vm_compute; discriminate].
      rewrite /E3 upd_ne; [| vm_compute; discriminate].
      rewrite /E2 upd_ne; [| vm_compute; discriminate].
      rewrite /E1. apply upd_eq. }
    assert (Hal0' : eq_vec (access_vec_dec (update_vec_dec (add_vec (E4 !!! Regidx (mword_of_int 1 : mword 5)) (sign_extend' 64 (zeros' 12))) 0 ('b"0")) 0) ('b"0") = true)
      by (rewrite HE4ra; exact Hal).
    iPoseProof (ydi_2a with "Htext") as "Hi2a".
    iApply (wp_cret_s_sconf γ root_ppn Φ (mword_of_int (YD + 0x2a)) (mword_of_int 1 : mword 5) E4 av
              ltac:(vm_compute; discriminate) Hal0'
              with "Hsc Hhs Hcg Htlbinv Hpc Hi2a [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc".
    assert (Hra_final : update_vec_dec (add_vec (E4 !!! Regidx (mword_of_int 1 : mword 5)) (sign_extend' 64 (zeros' 12))) 0 ('b"0") = ret_tgt)
      by (rewrite HE4ra; reflexivity).
    iEval (rewrite Hra_final) in "Hpc".
    (* ------------------------------------------------------------------ *)
    (* Post: hand every resource straight back; callee_saved via threading.*)
    (* ------------------------------------------------------------------ *)
    iApply ("Hcont" $! E4 with "[%] Hsc Hhs Hcg Hcnt Htlbinv Hpc Hcur Hnoff [Hint] Hlkcpu Hown' Hvc'").
    2:{ iExists iv1. iExact "Hint". }
    (* callee_saved m E4 *)
    assert (Csp : E4 !!! Regidx csp_rs1 = m !!! Regidx csp_rs1)
      by (rewrite HE4sp Hspm; reflexivity).
    assert (Cs0 : E4 !!! Regidx (mword_of_int 8 : mword 5) = m !!! Regidx (mword_of_int 8 : mword 5))
      by (yd_peel; reflexivity).
    assert (Cs1 : E4 !!! Regidx (mword_of_int 9 : mword 5) = m !!! Regidx (mword_of_int 9 : mword 5))
      by (yd_peel; reflexivity).
    assert (Ctp : E4 !!! Regidx (mword_of_int 4 : mword 5) = m !!! Regidx (mword_of_int 4 : mword 5)).
    { yd_peel.
      rewrite (callee_saved_lookup Hcs_rel (mword_of_int 4) ltac:(vm_compute; reflexivity)). yd_peel.
      rewrite (callee_saved_lookup Hcs_sch (mword_of_int 4) ltac:(vm_compute; reflexivity)). yd_peel.
      rewrite (callee_saved_lookup Hcs_acq (mword_of_int 4) ltac:(vm_compute; reflexivity)). yd_peel.
      rewrite (callee_saved_lookup Hcs_mp (mword_of_int 4) ltac:(vm_compute; reflexivity)). yd_peel.
      reflexivity. }
    assert (Cs2 : E4 !!! Regidx (mword_of_int 18 : mword 5) = m !!! Regidx (mword_of_int 18 : mword 5)).
    { yd_peel.
      rewrite (callee_saved_lookup Hcs_rel (mword_of_int 18) ltac:(vm_compute; reflexivity)). yd_peel.
      rewrite (callee_saved_lookup Hcs_sch (mword_of_int 18) ltac:(vm_compute; reflexivity)). yd_peel.
      rewrite (callee_saved_lookup Hcs_acq (mword_of_int 18) ltac:(vm_compute; reflexivity)). yd_peel.
      rewrite (callee_saved_lookup Hcs_mp (mword_of_int 18) ltac:(vm_compute; reflexivity)). yd_peel.
      reflexivity. }
    assert (Cs3 : E4 !!! Regidx (mword_of_int 19 : mword 5) = m !!! Regidx (mword_of_int 19 : mword 5)).
    { yd_peel.
      rewrite (callee_saved_lookup Hcs_rel (mword_of_int 19) ltac:(vm_compute; reflexivity)). yd_peel.
      rewrite (callee_saved_lookup Hcs_sch (mword_of_int 19) ltac:(vm_compute; reflexivity)). yd_peel.
      rewrite (callee_saved_lookup Hcs_acq (mword_of_int 19) ltac:(vm_compute; reflexivity)). yd_peel.
      rewrite (callee_saved_lookup Hcs_mp (mword_of_int 19) ltac:(vm_compute; reflexivity)). yd_peel.
      reflexivity. }
    assert (Cs4 : E4 !!! Regidx (mword_of_int 20 : mword 5) = m !!! Regidx (mword_of_int 20 : mword 5)).
    { yd_peel.
      rewrite (callee_saved_lookup Hcs_rel (mword_of_int 20) ltac:(vm_compute; reflexivity)). yd_peel.
      rewrite (callee_saved_lookup Hcs_sch (mword_of_int 20) ltac:(vm_compute; reflexivity)). yd_peel.
      rewrite (callee_saved_lookup Hcs_acq (mword_of_int 20) ltac:(vm_compute; reflexivity)). yd_peel.
      rewrite (callee_saved_lookup Hcs_mp (mword_of_int 20) ltac:(vm_compute; reflexivity)). yd_peel.
      reflexivity. }
    assert (Cs5 : E4 !!! Regidx (mword_of_int 21 : mword 5) = m !!! Regidx (mword_of_int 21 : mword 5)).
    { yd_peel.
      rewrite (callee_saved_lookup Hcs_rel (mword_of_int 21) ltac:(vm_compute; reflexivity)). yd_peel.
      rewrite (callee_saved_lookup Hcs_sch (mword_of_int 21) ltac:(vm_compute; reflexivity)). yd_peel.
      rewrite (callee_saved_lookup Hcs_acq (mword_of_int 21) ltac:(vm_compute; reflexivity)). yd_peel.
      rewrite (callee_saved_lookup Hcs_mp (mword_of_int 21) ltac:(vm_compute; reflexivity)). yd_peel.
      reflexivity. }
    assert (Cs6 : E4 !!! Regidx (mword_of_int 22 : mword 5) = m !!! Regidx (mword_of_int 22 : mword 5)).
    { yd_peel.
      rewrite (callee_saved_lookup Hcs_rel (mword_of_int 22) ltac:(vm_compute; reflexivity)). yd_peel.
      rewrite (callee_saved_lookup Hcs_sch (mword_of_int 22) ltac:(vm_compute; reflexivity)). yd_peel.
      rewrite (callee_saved_lookup Hcs_acq (mword_of_int 22) ltac:(vm_compute; reflexivity)). yd_peel.
      rewrite (callee_saved_lookup Hcs_mp (mword_of_int 22) ltac:(vm_compute; reflexivity)). yd_peel.
      reflexivity. }
    assert (Cs7 : E4 !!! Regidx (mword_of_int 23 : mword 5) = m !!! Regidx (mword_of_int 23 : mword 5)).
    { yd_peel.
      rewrite (callee_saved_lookup Hcs_rel (mword_of_int 23) ltac:(vm_compute; reflexivity)). yd_peel.
      rewrite (callee_saved_lookup Hcs_sch (mword_of_int 23) ltac:(vm_compute; reflexivity)). yd_peel.
      rewrite (callee_saved_lookup Hcs_acq (mword_of_int 23) ltac:(vm_compute; reflexivity)). yd_peel.
      rewrite (callee_saved_lookup Hcs_mp (mword_of_int 23) ltac:(vm_compute; reflexivity)). yd_peel.
      reflexivity. }
    assert (Cs8 : E4 !!! Regidx (mword_of_int 24 : mword 5) = m !!! Regidx (mword_of_int 24 : mword 5)).
    { yd_peel.
      rewrite (callee_saved_lookup Hcs_rel (mword_of_int 24) ltac:(vm_compute; reflexivity)). yd_peel.
      rewrite (callee_saved_lookup Hcs_sch (mword_of_int 24) ltac:(vm_compute; reflexivity)). yd_peel.
      rewrite (callee_saved_lookup Hcs_acq (mword_of_int 24) ltac:(vm_compute; reflexivity)). yd_peel.
      rewrite (callee_saved_lookup Hcs_mp (mword_of_int 24) ltac:(vm_compute; reflexivity)). yd_peel.
      reflexivity. }
    assert (Cs9 : E4 !!! Regidx (mword_of_int 25 : mword 5) = m !!! Regidx (mword_of_int 25 : mword 5)).
    { yd_peel.
      rewrite (callee_saved_lookup Hcs_rel (mword_of_int 25) ltac:(vm_compute; reflexivity)). yd_peel.
      rewrite (callee_saved_lookup Hcs_sch (mword_of_int 25) ltac:(vm_compute; reflexivity)). yd_peel.
      rewrite (callee_saved_lookup Hcs_acq (mword_of_int 25) ltac:(vm_compute; reflexivity)). yd_peel.
      rewrite (callee_saved_lookup Hcs_mp (mword_of_int 25) ltac:(vm_compute; reflexivity)). yd_peel.
      reflexivity. }
    assert (Cs10 : E4 !!! Regidx (mword_of_int 26 : mword 5) = m !!! Regidx (mword_of_int 26 : mword 5)).
    { yd_peel.
      rewrite (callee_saved_lookup Hcs_rel (mword_of_int 26) ltac:(vm_compute; reflexivity)). yd_peel.
      rewrite (callee_saved_lookup Hcs_sch (mword_of_int 26) ltac:(vm_compute; reflexivity)). yd_peel.
      rewrite (callee_saved_lookup Hcs_acq (mword_of_int 26) ltac:(vm_compute; reflexivity)). yd_peel.
      rewrite (callee_saved_lookup Hcs_mp (mword_of_int 26) ltac:(vm_compute; reflexivity)). yd_peel.
      reflexivity. }
    assert (Cs11 : E4 !!! Regidx (mword_of_int 27 : mword 5) = m !!! Regidx (mword_of_int 27 : mword 5)).
    { yd_peel.
      rewrite (callee_saved_lookup Hcs_rel (mword_of_int 27) ltac:(vm_compute; reflexivity)). yd_peel.
      rewrite (callee_saved_lookup Hcs_sch (mword_of_int 27) ltac:(vm_compute; reflexivity)). yd_peel.
      rewrite (callee_saved_lookup Hcs_acq (mword_of_int 27) ltac:(vm_compute; reflexivity)). yd_peel.
      rewrite (callee_saved_lookup Hcs_mp (mword_of_int 27) ltac:(vm_compute; reflexivity)). yd_peel.
      reflexivity. }
    unfold callee_saved. repeat split; assumption.
  Qed.

End WpSconfYield.

End YieldProof.
