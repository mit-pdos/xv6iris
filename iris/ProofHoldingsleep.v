(* ProofHoldingsleep.v -- holdingsleep() over the SIE-agnostic sconf world.

   holdingsleep(slk) @ 0x80003f4a: acquires the inner spinlock, refutes the
   free arm with the caller's sleeplock token (so the c.bnez is TAKEN
   deterministically), reads the holder pid and myproc()->pid, compares them
   (equal, since the caller supplies both from the same pidv), releases, and
   returns a0 = 1.  48-byte frame (ra/s0/s1/s2 saved; s3 spilled lazily at
   sp+8 on the taken path).  A functor over ACQUIRE / RELEASE / MYPROC. *)
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
Require Import WpLock.
Require Import ProcGeom.
Require Import SleepLock.
Require Import WpSconfAlu WpSconfMem WpSconfCtl WpSconfBtype.
Require Import CodeSleeplock.
Require Import IntrDefs.
Require Import WpNext.
Require Import CpuOwn.
Require Import SpecAcquire SpecRelease SpecMyproc.
Require Import SpecHoldingsleep.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Import Defs.

Local Open Scope Z_scope.

(* seqz over sub of two equal registers = 1 (sltiu (a-a) 1 = 1).  Copied
   self-contained from WpHoldingInv.v to avoid a heavy Require edge. *)
Lemma hsl_seqz_sub (a b : mword 64) :
  eq_vec a b = true ->
  zero_extend' 64 (bool_to_bit (zopz0zI_u (sub_vec a b)
    (sign_extend' 64 (mword_of_int 1 : mword 12)))) = (mword_of_int 1 : mword 64).
Proof.
  intro He.
  assert (Hab : a = b) by (apply eq_vec_true_iff; exact He).
  subst b.
  replace (sub_vec a a) with (zeros' 64 : mword 64);
    [ apply bv_eq; vm_compute; reflexivity | ].
  apply bv_eq.
  unfold sub_vec, Operators_mwords.word_binop, Operators_mwords.with_word',
    SailStdpp.Values.with_word, to_word, get_word, MachineWord.MachineWord.sub.
  rewrite bv_sub_unsigned. rewrite Z.sub_diag. reflexivity.
Qed.



Module HoldingsleepProof (Acquire : ACQUIRE) (Release : RELEASE) (Myproc : MYPROC) : HOLDINGSLEEP.

Section ProofHoldingsleep.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  (* generic register-map peel over the proof's [set]-chain (hit-first). *)
  Local Ltac hpeel :=
    repeat first
      [ rewrite upd_eq
      | rewrite upd_ne; [| vm_compute; discriminate]
      | lazymatch goal with |- ?M !!! _ = _ => is_var M; progress unfold M end ].

  Lemma wp_holdingsleep_sconf
      (γl γsl : gname) (s : string) (R : iProp Σ)
      (m : regfile) (p : mword 64) (pidv : mword 32) (av : nat) (eb : bool) (C : iProp Σ) (dq : dfrac) (b : bool)
    : wp_holdingsleep_sconf_body γl γsl s R m p pidv av eb C dq b.
  Proof.
    cbv beta delta [wp_holdingsleep_sconf_body].
    intros pcE slk ret_tgt Hav.
    pose (sp0 := (m !!! Regidx csp_rs1 : mword 64)).
    set (spr := add_vec sp0 (sign_extend' 64 (caddi16sp_imm (mword_of_int 61 : mword 6)))).
    iIntros "Hcg Hcnt #Htext Hpc #Hsleeplock Hsl Hpidfield #Hpanic Hpidproc Hcont".
    iDestruct (cpu_own_eb_agree with "Hcg Hcnt") as %Heb. cbn in Heb.
    subst eb.
    (* stack-slot address bridges (spr-relative store offset -> pa_stk sp0 k). *)
    assert (Hspr6 : spr = pa_stk sp0 6).
    { unfold spr, pa_stk, add_vec_int. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb1 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000"))) = pa_stk sp0 1).
    { unfold spr, sp0, pa_stk, add_vec_int. rewrite pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb2 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000"))) = pa_stk sp0 2).
    { unfold spr, sp0, pa_stk, add_vec_int. rewrite pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb3 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000"))) = pa_stk sp0 3).
    { unfold spr, sp0, pa_stk, add_vec_int. rewrite pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb4 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000"))) = pa_stk sp0 4).
    { unfold spr, sp0, pa_stk, add_vec_int. rewrite pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb5 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) = pa_stk sp0 5).
    { unfold spr, sp0, pa_stk, add_vec_int. rewrite pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    iDestruct (is_sleeplock_lock with "Hsleeplock") as "#Hlk".
    (* ===================== PROLOGUE ===================== *)
    iPoseProof (hsl_00 with "Htext") as "Hi00".
    assert (Hpush : add_vec sp0 (sign_extend' 64 (caddi16sp_imm (mword_of_int 61 : mword 6))) = pa_stk sp0 6) by exact Hspr6.
    iApply (wp_caddi16sp_push_s_sconf pcE (mword_of_int 61 : mword 6) m av 6 b ltac:(lia) Hpush
              with "Hcg Hpc Hi00 [-]").
    iIntros (CID1 Hs1) "Hcg Hframe Hpc".
    set (M0 := <[Regidx csp_rs1 := regval_into_reg (add_vec sp0 (sign_extend' 64 (caddi16sp_imm (mword_of_int 61 : mword 6))))]> m).
    change (<[Regidx csp_rs1 := regval_into_reg (add_vec sp0 (sign_extend' 64 (caddi16sp_imm (mword_of_int 61 : mword 6))))]> m) with M0.
    assert (HM0csp : M0 !!! Regidx csp_rs1 = spr) by (rewrite /M0 upd_eq; reflexivity).
    iEval (rewrite stack_own_slots; cbn [seq]) in "Hframe".
    iDestruct "Hframe" as "(S1 & S2 & S3 & S4 & S5 & S6 & _)".
    iDestruct "S1" as (vra0) "Hslot_ra".
    iDestruct "S2" as (vs00) "Hslot_s0".
    iDestruct "S3" as (vs10) "Hslot_s1".
    iDestruct "S4" as (vs20) "Hslot_s2".
    assert (Hpp02 : add_vec_int (pcE : mword 64) 2 = mword_of_int (KernelSyms.holdingsleep + 0x02)) by (unfold pcE; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp02) in "Hpc".
    (* +0x02 c.sdsp ra,40(sp) *)
    iPoseProof (hsl_02 with "Htext") as "Hi02".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.holdingsleep + 0x02)) (mword_of_int 5 : mword 6) (mword_of_int 1 : mword 5)
              M0 (av - 6)%nat vra0 b with "Hcg Hpc Hi02 [Hslot_ra] [-]").
    { iEval (rewrite HM0csp Hb1). iExact "Hslot_ra". }
    iIntros (CID2 Hs2) "Hcg Hpc Hslot_ra".
    assert (Hra_v : M0 !!! Regidx (mword_of_int 1 : mword 5) = m !!! Regidx (mword_of_int 1 : mword 5))
      by (rewrite /M0 upd_ne; [reflexivity | vm_compute; discriminate]).
    iEval (rgne) in "Hslot_ra".
    iEval (rewrite HM0csp Hb1 Hra_v) in "Hslot_ra".
    assert (Hpp04 : add_vec_int (mword_of_int (KernelSyms.holdingsleep + 0x02) : mword 64) 2 = mword_of_int (KernelSyms.holdingsleep + 0x04)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp04) in "Hpc".
    (* +0x04 c.sdsp s0,32(sp) *)
    iPoseProof (hsl_04 with "Htext") as "Hi04".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.holdingsleep + 0x04)) (mword_of_int 4 : mword 6) (mword_of_int 8 : mword 5)
              M0 (av - 6)%nat vs00 b with "Hcg Hpc Hi04 [Hslot_s0] [-]").
    { iEval (rewrite HM0csp Hb2). iExact "Hslot_s0". }
    iIntros (CID3 Hs3) "Hcg Hpc Hslot_s0".
    assert (Hs0_v : M0 !!! Regidx (mword_of_int 8 : mword 5) = m !!! Regidx (mword_of_int 8 : mword 5))
      by (rewrite /M0 upd_ne; [reflexivity | vm_compute; discriminate]).
    iEval (rgne) in "Hslot_s0".
    iEval (rewrite HM0csp Hb2 Hs0_v) in "Hslot_s0".
    assert (Hpp06 : add_vec_int (mword_of_int (KernelSyms.holdingsleep + 0x04) : mword 64) 2 = mword_of_int (KernelSyms.holdingsleep + 0x06)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp06) in "Hpc".
    (* +0x06 c.sdsp s1,24(sp) *)
    iPoseProof (hsl_06 with "Htext") as "Hi06".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.holdingsleep + 0x06)) (mword_of_int 3 : mword 6) (mword_of_int 9 : mword 5)
              M0 (av - 6)%nat vs10 b with "Hcg Hpc Hi06 [Hslot_s1] [-]").
    { iEval (rewrite HM0csp Hb3). iExact "Hslot_s1". }
    iIntros (CID4 Hs4) "Hcg Hpc Hslot_s1".
    assert (Hs1_v : M0 !!! Regidx (mword_of_int 9 : mword 5) = m !!! Regidx (mword_of_int 9 : mword 5))
      by (rewrite /M0 upd_ne; [reflexivity | vm_compute; discriminate]).
    iEval (rgne) in "Hslot_s1".
    iEval (rewrite HM0csp Hb3 Hs1_v) in "Hslot_s1".
    assert (Hpp08 : add_vec_int (mword_of_int (KernelSyms.holdingsleep + 0x06) : mword 64) 2 = mword_of_int (KernelSyms.holdingsleep + 0x08)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp08) in "Hpc".
    (* +0x08 c.sdsp s2,16(sp) *)
    iPoseProof (hsl_08 with "Htext") as "Hi08".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.holdingsleep + 0x08)) (mword_of_int 2 : mword 6) (mword_of_int 18 : mword 5)
              M0 (av - 6)%nat vs20 b with "Hcg Hpc Hi08 [Hslot_s2] [-]").
    { iEval (rewrite HM0csp Hb4). iExact "Hslot_s2". }
    iIntros (CID5 Hs5) "Hcg Hpc Hslot_s2".
    assert (Hs2_v : M0 !!! Regidx (mword_of_int 18 : mword 5) = m !!! Regidx (mword_of_int 18 : mword 5))
      by (rewrite /M0 upd_ne; [reflexivity | vm_compute; discriminate]).
    iEval (rgne) in "Hslot_s2".
    iEval (rewrite HM0csp Hb4 Hs2_v) in "Hslot_s2".
    assert (Hpp0a : add_vec_int (mword_of_int (KernelSyms.holdingsleep + 0x08) : mword 64) 2 = mword_of_int (KernelSyms.holdingsleep + 0x0a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0a) in "Hpc".
    (* +0x0a c.addi4spn s0,sp,48 *)
    iPoseProof (hsl_0a with "Htext") as "Hi0a".
    iApply (wp_caddi4spn_s_sconf (mword_of_int (KernelSyms.holdingsleep + 0x0a)) (Cregidx (mword_of_int 0)) (mword_of_int 12 : mword 8) (mword_of_int 8 : mword 5)
              M0 (av - 6)%nat b ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi0a [-]").
    iIntros (CID6 Hs6) "Hcg Hpc".
    set (M1 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg (add_vec (M0 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 12 : mword 8))))]> M0).
    change (<[Regidx (mword_of_int 8 : mword 5) := regval_into_reg (add_vec (M0 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 12 : mword 8))))]> M0) with M1.
    assert (Hpp0c : add_vec_int (mword_of_int (KernelSyms.holdingsleep + 0x0a) : mword 64) 2 = mword_of_int (KernelSyms.holdingsleep + 0x0c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0c) in "Hpc".
    (* +0x0c c.mv s1,a0 : s1 := slk *)
    iPoseProof (hsl_0c with "Htext") as "Hi0c".
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.holdingsleep + 0x0c)) (mword_of_int 9 : mword 5) (mword_of_int 10 : mword 5)
              M1 (av - 6)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi0c [-]").
    iIntros (CID7 Hs7) "Hcg Hpc".
    set (M2 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (add_vec zero_reg (M1 !!! Regidx (mword_of_int 10 : mword 5)))]> M1).
    change (<[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (add_vec zero_reg (M1 !!! Regidx (mword_of_int 10 : mword 5)))]> M1) with M2.
    assert (Hpp0e : add_vec_int (mword_of_int (KernelSyms.holdingsleep + 0x0c) : mword 64) 2 = mword_of_int (KernelSyms.holdingsleep + 0x0e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0e) in "Hpc".
    (* +0x0e addi s2,a0,8 : s2 := sl_lk slk *)
    iPoseProof (hsl_0e with "Htext") as "Hi0e".
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.holdingsleep + 0x0e)) (mword_of_int 18 : mword 5) (mword_of_int 10 : mword 5) (mword_of_int 8 : mword 12)
              M2 (av - 6)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi0e [-]").
    iIntros (CID8 Hs8) "Hcg Hpc".
    set (M3 := <[Regidx (mword_of_int 18 : mword 5) := regval_into_reg (add_vec (M2 !!! Regidx (mword_of_int 10 : mword 5)) (sign_extend' 64 (mword_of_int 8 : mword 12)))]> M2).
    change (<[Regidx (mword_of_int 18 : mword 5) := regval_into_reg (add_vec (M2 !!! Regidx (mword_of_int 10 : mword 5)) (sign_extend' 64 (mword_of_int 8 : mword 12)))]> M2) with M3.
    assert (Hpp12 : add_vec_int (mword_of_int (KernelSyms.holdingsleep + 0x0e) : mword 64) 4 = mword_of_int (KernelSyms.holdingsleep + 0x12)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp12) in "Hpc".
    (* +0x12 c.mv a0,s2 : a0 := sl_lk slk *)
    iPoseProof (hsl_12 with "Htext") as "Hi12".
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.holdingsleep + 0x12)) (mword_of_int 10 : mword 5) (mword_of_int 18 : mword 5)
              M3 (av - 6)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi12 [-]").
    iIntros (CID9 Hs9) "Hcg Hpc".
    set (M4 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg (add_vec zero_reg (M3 !!! Regidx (mword_of_int 18 : mword 5)))]> M3).
    change (<[Regidx (mword_of_int 10 : mword 5) := regval_into_reg (add_vec zero_reg (M3 !!! Regidx (mword_of_int 18 : mword 5)))]> M3) with M4.
    assert (Hpp14 : add_vec_int (mword_of_int (KernelSyms.holdingsleep + 0x12) : mword 64) 2 = mword_of_int (KernelSyms.holdingsleep + 0x14)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp14) in "Hpc".
    (* +0x14 jal ra,acquire *)
    iPoseProof (hsl_14 with "Htext") as "Hi14".
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.holdingsleep + 0x14)) (mword_of_int 1 : mword 5) (mword_of_int 2083828 : mword 21)
              M4 (av - 6)%nat b ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi14 [-]").
    iIntros (CID10 Hs10) "Hcg Hpc".
    set (M5 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.holdingsleep + 0x14) : mword 64) 4)]> M4).
    change (<[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.holdingsleep + 0x14) : mword 64) 4)]> M4) with M5.
    assert (Hjacq : add_vec (mword_of_int (KernelSyms.holdingsleep + 0x14) : mword 64) (sign_extend' 64 (mword_of_int 2083828 : mword 21)) = mword_of_int KernelSyms.acquire)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hjacq) in "Hpc".
    (* register facts at acquire entry. *)
    assert (HM5ra : M5 !!! Regidx (mword_of_int 1 : mword 5) = add_vec_int (mword_of_int (KernelSyms.holdingsleep + 0x14) : mword 64) 4)
      by (rewrite /M5 upd_eq; reflexivity).
    assert (HM5a0 : M5 !!! Regidx (mword_of_int 10 : mword 5) = sl_lk slk).
    { rewrite /M5 upd_ne; [| vm_compute; discriminate].
      rewrite /M4 upd_eq. rewrite add_vec_zero_l.
      rewrite /M3 upd_eq.
      rewrite /M2 upd_ne; [| vm_compute; discriminate].
      rewrite /M1 upd_ne; [| vm_compute; discriminate].
      rewrite /M0 upd_ne; [| vm_compute; discriminate].
      rewrite /sl_lk. reflexivity. }
    assert (HM5s1 : M5 !!! Regidx (mword_of_int 9 : mword 5) = slk).
    { rewrite /M5 upd_ne; [| vm_compute; discriminate].
      rewrite /M4 upd_ne; [| vm_compute; discriminate].
      rewrite /M3 upd_ne; [| vm_compute; discriminate].
      rewrite /M2 upd_eq. rewrite add_vec_zero_l.
      rewrite /M1 upd_ne; [| vm_compute; discriminate].
      rewrite /M0 upd_ne; [| vm_compute; discriminate]. reflexivity. }
    (* [Hcnt] was introduced at the function's ENTRY hart; the ten plain
       instructions above each moved to a FRESH, universally quantified hart
       (CID1..CID10), so acquire wants it at CID10.  ONE line, no case split
       on [b] (see CpuOwn.cpu_own_transport). *)
    iDestruct (cpu_own_transport CID CID10 0%nat b p C b ltac:(wp_next_chain)
                 with "Hcnt") as "Hcnt".
    (* acquire(&slk->lk): intr_count 0 -> 1; is_lock from the sleeplock. *)
    iApply (Acquire.wp_acquire_sconf γl "sleep lock"%string (sl_res γsl slk R) M5
              0%nat b p C (av - 6)%nat b
              ltac:(lia)
              ltac:(lia)
              with "Hcg Hcnt Htext Hpc [Hlk] Hpanic [-]").
    { iEval (rewrite HM5a0). iExact "Hlk". }
    iIntros (CIDacq Hsacq ms A) "%Hms Hcg Hpc %HcsA Htok HR Hcnt Hpay".
    assert (Hpc18 : ret_pc (M5 !!! Regidx (mword_of_int 1 : mword 5)) = mword_of_int (KernelSyms.holdingsleep + 0x18))
      by (rewrite HM5ra; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc18) in "Hpc".
    (* open sl_res with the caller's token: refute the free arm. *)
    iDestruct (sl_res_open_held γsl slk R with "HR Hsl") as "(Hsl & Hcellex)".
    iDestruct "Hcellex" as (v) "(Hslk & %Hvnz)".
    (* +0x18 c.lw a5,0(s1) : a5 := sext v *)
    iPoseProof (hsl_18 with "Htext") as "Hi18".
    assert (HAs1 : A !!! Regidx (mword_of_int 9 : mword 5) = slk).
    { rewrite (callee_saved_lookup HcsA (mword_of_int 9 : mword 5) ltac:(vm_compute; reflexivity)). exact HM5s1. }
    assert (Haddr18 : add_vec (A !!! Regidx (mword_of_int 9 : mword 5)) (sign_extend' 64 (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 5) ('b"00")))) = slk).
    { rewrite HAs1.
      replace (sign_extend' 64 (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 5) ('b"00"))) : mword 64)
        with (sign_extend' 64 (mword_of_int 0 : mword 12) : mword 64) by (apply bv_eq; vm_compute; reflexivity).
      apply addv_sext0. }
    iApply (wp_clw_s_sconf (mword_of_int (KernelSyms.holdingsleep + 0x18)) (mword_of_int 15 : mword 5) (mword_of_int 9 : mword 5)
              (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 5) ('b"00"))) A (trap_res b + (av - 6))%nat v false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi18 [Hslk] [-]").
    { iEval (rewrite Haddr18). iExact "Hslk". }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc Hslk".
    iEval (rewrite Haddr18) in "Hslk".
    set (B18 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (sign_extend' 64 v)]> A).
    change (<[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (sign_extend' 64 v)]> A) with B18.
    assert (Hpp1a : add_vec_int (mword_of_int (KernelSyms.holdingsleep + 0x18) : mword 64) 2 = mword_of_int (KernelSyms.holdingsleep + 0x1a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp1a) in "Hpc".
    assert (HB18a5 : B18 !!! Regidx (mword_of_int 15 : mword 5) = sign_extend' 64 v) by (rewrite /B18 upd_eq; reflexivity).
    assert (HB18s1 : B18 !!! Regidx (mword_of_int 9 : mword 5) = slk) by (rewrite /B18 upd_ne; [exact HAs1 | vm_compute; discriminate]).
    (* +0x1a c.bnez a5,+24 : held arm forces TAKEN *)
    iPoseProof (hsl_1a with "Htext") as "Hi1a".
    iApply (wp_cbnez_taken_s_sconf (mword_of_int (KernelSyms.holdingsleep + 0x1a)) (mword_of_int 12 : mword 8) (Cregidx (mword_of_int 7)) (mword_of_int 15 : mword 5)
              B18 (trap_res b + (av - 6))%nat false
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
              ltac:(rgne; rewrite HB18a5; exact Hvnz) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi1a [-]").
    iApply wp_next_off_intro.
    iApply bi.later_intro. iIntros "Hcg Hpc".
    assert (Htgt32 : add_vec (mword_of_int (KernelSyms.holdingsleep + 0x1a) : mword 64) (sign_extend' 64 (sign_extend' 13 (concat_vec (mword_of_int 12 : mword 8) ('b"0")))) = mword_of_int (KernelSyms.holdingsleep + 0x32))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgt32) in "Hpc".
    (* +0x32 c.sdsp s3,8(sp) : spill s3 to slot 5 *)
    assert (HB18csp : B18 !!! Regidx csp_rs1 = spr).
    { rewrite /B18 upd_ne; [| vm_compute; discriminate].
      rewrite (callee_saved_lookup HcsA csp_rs1 ltac:(vm_compute; reflexivity)).
      hpeel. exact HM0csp. }
    assert (HB18s3 : B18 !!! Regidx (mword_of_int 19 : mword 5) = m !!! Regidx (mword_of_int 19 : mword 5)).
    { rewrite /B18 upd_ne; [| vm_compute; discriminate].
      rewrite (callee_saved_lookup HcsA (mword_of_int 19 : mword 5) ltac:(vm_compute; reflexivity)).
      hpeel. reflexivity. }
    iDestruct "S5" as (vs30) "Hslot5pre".
    iPoseProof (hsl_32 with "Htext") as "Hi32".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.holdingsleep + 0x32)) (mword_of_int 1 : mword 6) (mword_of_int 19 : mword 5)
              B18 (trap_res b + (av - 6))%nat vs30 false with "Hcg Hpc Hi32 [Hslot5pre] [-]").
    { iEval (rewrite HB18csp Hb5). iExact "Hslot5pre". }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc Hslot_s3".
    iEval (rgne) in "Hslot_s3".
    iEval (rewrite HB18csp Hb5 HB18s3) in "Hslot_s3".
    assert (Hpp34 : add_vec_int (mword_of_int (KernelSyms.holdingsleep + 0x32) : mword 64) 2 = mword_of_int (KernelSyms.holdingsleep + 0x34)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp34) in "Hpc".
    (* +0x34 lw s3,40(s1) : s3 := sext pidv *)
    iPoseProof (hsl_34 with "Htext") as "Hi34".
    assert (Haddr34 : add_vec (B18 !!! Regidx (mword_of_int 9 : mword 5)) (sign_extend' 64 (mword_of_int 0x28 : mword 12)) = sl_pid slk).
    { rewrite HB18s1. rewrite /sl_pid. reflexivity. }
    iApply (wp_lw_s_sconf (mword_of_int (KernelSyms.holdingsleep + 0x34)) (mword_of_int 19 : mword 5) (mword_of_int 9 : mword 5)
              (mword_of_int 0x28 : mword 12) B18 (trap_res b + (av - 6))%nat pidv false (dqm := DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi34 [Hpidfield] [-]").
    { iEval (rewrite Haddr34). iExact "Hpidfield". }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc Hpidfield".
    iEval (rewrite Haddr34) in "Hpidfield".
    set (B34 := <[Regidx (mword_of_int 19 : mword 5) := regval_into_reg (sign_extend' 64 pidv)]> B18).
    change (<[Regidx (mword_of_int 19 : mword 5) := regval_into_reg (sign_extend' 64 pidv)]> B18) with B34.
    assert (Hpp38 : add_vec_int (mword_of_int (KernelSyms.holdingsleep + 0x34) : mword 64) 4 = mword_of_int (KernelSyms.holdingsleep + 0x38)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp38) in "Hpc".
    (* +0x38 jal ra,myproc *)
    iPoseProof (hsl_38 with "Htext") as "Hi38".
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.holdingsleep + 0x38)) (mword_of_int 1 : mword 5) (mword_of_int 2087152 : mword 21)
              B34 (trap_res b + (av - 6))%nat false ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi38 [-]").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    set (Bj := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.holdingsleep + 0x38) : mword 64) 4)]> B34).
    change (<[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.holdingsleep + 0x38) : mword 64) 4)]> B34) with Bj.
    assert (Hjmp : add_vec (mword_of_int (KernelSyms.holdingsleep + 0x38) : mword 64) (sign_extend' 64 (mword_of_int 2087152 : mword 21)) = mword_of_int KernelSyms.myproc)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hjmp) in "Hpc".
    assert (HBjra : Bj !!! Regidx (mword_of_int 1 : mword 5) = add_vec_int (mword_of_int (KernelSyms.holdingsleep + 0x38) : mword 64) 4) by (rewrite /Bj upd_eq; reflexivity).
    (* myproc(): a0 = p, callee-saved preserved; noff cell at literal 1.
       Called at [b = false] (holding the lock, level 1): myproc's own
       [wp_next] index is the [false] we pass, so it collapses too -- the
       hart stays at [CIDacq] throughout, no transport needed. *)
    iApply (Myproc.wp_myproc_sconf Bj (trap_res b + (av - 6))%nat 1%nat b p C false
              ltac:(vm_compute; reflexivity)
              ltac:(lia)
              with "Hcg Hcnt Htext Hpc [-]").
    iApply wp_next_off_intro.
    iIntros (ms2 MP) "%Hms2 Hcg Hcnt Hpc %HcsMPa".
    destruct HcsMPa as [HcsMP HMPa0].
    assert (Hpc3c : ret_pc (Bj !!! Regidx (mword_of_int 1 : mword 5)) = mword_of_int (KernelSyms.holdingsleep + 0x3c))
      by (rewrite HBjra; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc3c) in "Hpc".
    (* +0x3c c.lw s1,48(a0) : s1 := sext pidv (myproc()->pid) *)
    iPoseProof (hsl_3c with "Htext") as "Hi3c".
    assert (Haddr3c : add_vec (MP !!! Regidx (mword_of_int 10 : mword 5)) (sign_extend' 64 (zero_extend' 12 (concat_vec (mword_of_int 12 : mword 5) ('b"00")))) = p_pid p).
    { rewrite HMPa0. rewrite /p_pid.
      replace (sign_extend' 64 (zero_extend' 12 (concat_vec (mword_of_int 12 : mword 5) ('b"00"))) : mword 64)
        with (sign_extend' 64 (mword_of_int 48 : mword 12) : mword 64) by (apply bv_eq; vm_compute; reflexivity).
      reflexivity. }
    iApply (wp_clw_s_sconf (mword_of_int (KernelSyms.holdingsleep + 0x3c)) (mword_of_int 9 : mword 5) (mword_of_int 10 : mword 5)
              (zero_extend' 12 (concat_vec (mword_of_int 12 : mword 5) ('b"00"))) MP (trap_res b + (av - 6))%nat pidv false (dqm := dq)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi3c [Hpidproc] [-]").
    { iEval (rewrite Haddr3c). iExact "Hpidproc". }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc Hpidproc".
    iEval (rewrite Haddr3c) in "Hpidproc".
    set (C3c := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (sign_extend' 64 pidv)]> MP).
    change (<[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (sign_extend' 64 pidv)]> MP) with C3c.
    assert (Hpp3e : add_vec_int (mword_of_int (KernelSyms.holdingsleep + 0x3c) : mword 64) 2 = mword_of_int (KernelSyms.holdingsleep + 0x3e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp3e) in "Hpc".
    assert (HC3c_s1 : C3c !!! Regidx (mword_of_int 9 : mword 5) = sign_extend' 64 pidv) by (rewrite /C3c upd_eq; reflexivity).
    assert (HC3c_s3 : C3c !!! Regidx (mword_of_int 19 : mword 5) = sign_extend' 64 pidv).
    { rewrite /C3c upd_ne; [| vm_compute; discriminate].
      rewrite (callee_saved_lookup HcsMP (mword_of_int 19 : mword 5) ltac:(vm_compute; reflexivity)).
      rewrite /Bj upd_ne; [| vm_compute; discriminate].
      rewrite /B34 upd_eq; reflexivity. }
    (* +0x3e sub s1,s1,s3 : s1 := sext pidv - sext pidv *)
    iPoseProof (hsl_3e with "Htext") as "Hi3e".
    iApply (wp_sub_s_sconf (mword_of_int (KernelSyms.holdingsleep + 0x3e)) (mword_of_int 9 : mword 5) (mword_of_int 9 : mword 5) (mword_of_int 19 : mword 5)
              (sub_vec (C3c !!! Regidx (mword_of_int 9 : mword 5)) (C3c !!! Regidx (mword_of_int 19 : mword 5))) C3c (trap_res b + (av - 6))%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(repeat rgne; reflexivity)
              with "Hcg Hpc Hi3e [-]").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    set (C3e := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (sub_vec (C3c !!! Regidx (mword_of_int 9 : mword 5)) (C3c !!! Regidx (mword_of_int 19 : mword 5)))]> C3c).
    change (<[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (sub_vec (C3c !!! Regidx (mword_of_int 9 : mword 5)) (C3c !!! Regidx (mword_of_int 19 : mword 5)))]> C3c) with C3e.
    assert (Hpp42 : add_vec_int (mword_of_int (KernelSyms.holdingsleep + 0x3e) : mword 64) 4 = mword_of_int (KernelSyms.holdingsleep + 0x42)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp42) in "Hpc".
    assert (HC3e_s1 : C3e !!! Regidx (mword_of_int 9 : mword 5) = sub_vec (C3c !!! Regidx (mword_of_int 9 : mword 5)) (C3c !!! Regidx (mword_of_int 19 : mword 5)))
      by (rewrite /C3e upd_eq; reflexivity).
    assert (Heqpid : eq_vec (C3c !!! Regidx (mword_of_int 9 : mword 5)) (C3c !!! Regidx (mword_of_int 19 : mword 5)) = true)
      by (rewrite HC3c_s1 HC3c_s3; apply eq_vec_refl).
    (* +0x42 seqz s1,s1 (sltiu s1,s1,1) : s1 := 1 *)
    iPoseProof (hsl_42 with "Htext") as "Hi42".
    iApply (wp_sltiu_s_sconf (mword_of_int (KernelSyms.holdingsleep + 0x42)) (mword_of_int 9 : mword 5) (mword_of_int 9 : mword 5) (mword_of_int 1 : mword 12)
              (mword_of_int 1 : mword 64) C3e (trap_res b + (av - 6))%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(rgne; rewrite HC3e_s1; exact (hsl_seqz_sub _ _ Heqpid))
              with "Hcg Hpc Hi42 [-]").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    set (C42 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (mword_of_int 1 : mword 64)]> C3e).
    change (<[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (mword_of_int 1 : mword 64)]> C3e) with C42.
    assert (Hpp46 : add_vec_int (mword_of_int (KernelSyms.holdingsleep + 0x42) : mword 64) 4 = mword_of_int (KernelSyms.holdingsleep + 0x46)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp46) in "Hpc".
    assert (HC42csp : C42 !!! Regidx csp_rs1 = spr).
    { rewrite /C42 upd_ne; [| vm_compute; discriminate].
      rewrite /C3e upd_ne; [| vm_compute; discriminate].
      rewrite /C3c upd_ne; [| vm_compute; discriminate].
      rewrite (callee_saved_lookup HcsMP csp_rs1 ltac:(vm_compute; reflexivity)).
      rewrite /Bj upd_ne; [| vm_compute; discriminate].
      rewrite /B34 upd_ne; [| vm_compute; discriminate]. exact HB18csp. }
    (* +0x46 c.ldsp s3,8(sp) : restore s3 *)
    iPoseProof (hsl_46 with "Htext") as "Hi46".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.holdingsleep + 0x46)) (mword_of_int 1 : mword 6) (mword_of_int 19 : mword 5)
              C42 (trap_res b + (av - 6))%nat (m !!! Regidx (mword_of_int 19 : mword 5)) false (dqm := DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi46 [Hslot_s3] [-]").
    { iEval (rewrite HC42csp Hb5). iExact "Hslot_s3". }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc Hslot_s3".
    iEval (rewrite HC42csp Hb5) in "Hslot_s3".
    set (C46 := <[Regidx (mword_of_int 19 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 19 : mword 5))]> C42).
    change (<[Regidx (mword_of_int 19 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 19 : mword 5))]> C42) with C46.
    assert (Hpp48 : add_vec_int (mword_of_int (KernelSyms.holdingsleep + 0x46) : mword 64) 2 = mword_of_int (KernelSyms.holdingsleep + 0x48)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp48) in "Hpc".
    (* +0x48 c.j -42 -> +0x1e (join) *)
    iPoseProof (hsl_48 with "Htext") as "Hi48".
    iApply (wp_cj_s_sconf (mword_of_int (KernelSyms.holdingsleep + 0x48)) (sign_extend' 21 (concat_vec (mword_of_int 2027 : mword 11) ('b"0")))
              C46 (trap_res b + (av - 6))%nat false ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi48 [-]").
    iApply wp_next_off_intro.
    iApply bi.later_intro. iIntros "Hcg Hpc".
    assert (Htgt1e : add_vec (mword_of_int (KernelSyms.holdingsleep + 0x48) : mword 64) (sign_extend' 64 (sign_extend' 21 (concat_vec (mword_of_int 2027 : mword 11) ('b"0")))) = mword_of_int (KernelSyms.holdingsleep + 0x1e))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgt1e) in "Hpc".
    (* +0x1e c.mv a0,s2 : a0 := sl_lk slk *)
    assert (HC46s2 : C46 !!! Regidx (mword_of_int 18 : mword 5) = sl_lk slk).
    { rewrite /C46 upd_ne; [| vm_compute; discriminate].
      rewrite /C42 upd_ne; [| vm_compute; discriminate].
      rewrite /C3e upd_ne; [| vm_compute; discriminate].
      rewrite /C3c upd_ne; [| vm_compute; discriminate].
      rewrite (callee_saved_lookup HcsMP (mword_of_int 18 : mword 5) ltac:(vm_compute; reflexivity)).
      rewrite /Bj upd_ne; [| vm_compute; discriminate].
      rewrite /B34 upd_ne; [| vm_compute; discriminate].
      rewrite /B18 upd_ne; [| vm_compute; discriminate].
      rewrite (callee_saved_lookup HcsA (mword_of_int 18 : mword 5) ltac:(vm_compute; reflexivity)).
      rewrite /M5 upd_ne; [| vm_compute; discriminate].
      rewrite /M4 upd_ne; [| vm_compute; discriminate].
      rewrite /M3 upd_eq. rewrite /sl_lk.
      rewrite /M2 upd_ne; [| vm_compute; discriminate].
      rewrite /M1 upd_ne; [| vm_compute; discriminate].
      rewrite /M0 upd_ne; [| vm_compute; discriminate]. reflexivity. }
    iPoseProof (hsl_1e with "Htext") as "Hi1e".
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.holdingsleep + 0x1e)) (mword_of_int 10 : mword 5) (mword_of_int 18 : mword 5)
              C46 (trap_res b + (av - 6))%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi1e [-]").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    set (D1e := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg (add_vec zero_reg (C46 !!! Regidx (mword_of_int 18 : mword 5)))]> C46).
    change (<[Regidx (mword_of_int 10 : mword 5) := regval_into_reg (add_vec zero_reg (C46 !!! Regidx (mword_of_int 18 : mword 5)))]> C46) with D1e.
    assert (Hpp20 : add_vec_int (mword_of_int (KernelSyms.holdingsleep + 0x1e) : mword 64) 2 = mword_of_int (KernelSyms.holdingsleep + 0x20)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp20) in "Hpc".
    (* +0x20 jal ra,release *)
    iPoseProof (hsl_20 with "Htext") as "Hi20".
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.holdingsleep + 0x20)) (mword_of_int 1 : mword 5) (mword_of_int 2083952 : mword 21)
              D1e (trap_res b + (av - 6))%nat false ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi20 [-]").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    set (D20 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.holdingsleep + 0x20) : mword 64) 4)]> D1e).
    change (<[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.holdingsleep + 0x20) : mword 64) 4)]> D1e) with D20.
    assert (Hjrel : add_vec (mword_of_int (KernelSyms.holdingsleep + 0x20) : mword 64) (sign_extend' 64 (mword_of_int 2083952 : mword 21)) = mword_of_int KernelSyms.release)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hjrel) in "Hpc".
    assert (HD20ra : D20 !!! Regidx (mword_of_int 1 : mword 5) = add_vec_int (mword_of_int (KernelSyms.holdingsleep + 0x20) : mword 64) 4) by (rewrite /D20 upd_eq; reflexivity).
    assert (HD20a0 : D20 !!! Regidx (mword_of_int 10 : mword 5) = sl_lk slk).
    { rewrite /D20 upd_ne; [| vm_compute; discriminate].
      rewrite /D1e upd_eq. rewrite add_vec_zero_l. exact HC46s2. }
    assert (HD20csp : D20 !!! Regidx csp_rs1 = spr).
    { rewrite /D20 upd_ne; [| vm_compute; discriminate].
      rewrite /D1e upd_ne; [| vm_compute; discriminate].
      rewrite /C46 upd_ne; [| vm_compute; discriminate]. exact HC42csp. }
    (* close sl_res again (held), for release's R argument. *)
    iDestruct (sl_res_close_held γsl slk R v Hvnz with "Hslk") as "HR2".
    (* release(&slk->lk): intr_count 1 -> 0. *)
    iApply (Release.wp_release_sconf γl (sl_lk slk) "sleep lock"%string (sl_res γsl slk R) D20
              0%nat b p C (av - 6)%nat
              ltac:(rewrite HD20a0; apply addv_sext0)
              ltac:(lia)
              with "Hcg Htext Hpc [Hlk] [Htok] [HR2] Hcnt Hpay [-]").
    { iExact "Hlk". }
    { iExact "Htok". }
    { iExact "HR2". }
    iIntros (CIDrel Hsrel MR) "Hcg Hpc %HcsMR Hcnt".
    assert (Hpc24 : ret_pc (D20 !!! Regidx (mword_of_int 1 : mword 5)) = mword_of_int (KernelSyms.holdingsleep + 0x24))
      by (rewrite HD20ra; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc24) in "Hpc".
    (* register-preservation facts for the epilogue and callee_saved. *)
    assert (HMRcsp : MR !!! Regidx csp_rs1 = spr).
    { rewrite (callee_saved_lookup HcsMR csp_rs1 ltac:(vm_compute; reflexivity)). exact HD20csp. }
    (* +0x24 c.mv a0,s1 : a0 := 1 *)
    assert (HMRs1 : MR !!! Regidx (mword_of_int 9 : mword 5) = (mword_of_int 1 : mword 64)).
    { rewrite (callee_saved_lookup HcsMR (mword_of_int 9 : mword 5) ltac:(vm_compute; reflexivity)).
      rewrite /D20 upd_ne; [| vm_compute; discriminate].
      rewrite /D1e upd_ne; [| vm_compute; discriminate].
      rewrite /C46 upd_ne; [| vm_compute; discriminate].
      rewrite /C42 upd_eq; reflexivity. }
    iPoseProof (hsl_24 with "Htext") as "Hi24".
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.holdingsleep + 0x24)) (mword_of_int 10 : mword 5) (mword_of_int 9 : mword 5)
              MR (av - 6)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi24 [-]").
    iIntros (CIDe1 Hse1) "Hcg Hpc".
    set (E24 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg (add_vec zero_reg (MR !!! Regidx (mword_of_int 9 : mword 5)))]> MR).
    change (<[Regidx (mword_of_int 10 : mword 5) := regval_into_reg (add_vec zero_reg (MR !!! Regidx (mword_of_int 9 : mword 5)))]> MR) with E24.
    assert (Hpp26 : add_vec_int (mword_of_int (KernelSyms.holdingsleep + 0x24) : mword 64) 2 = mword_of_int (KernelSyms.holdingsleep + 0x26)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp26) in "Hpc".
    assert (HE24a0 : E24 !!! Regidx (mword_of_int 10 : mword 5) = (mword_of_int 1 : mword 64)).
    { rewrite /E24 upd_eq. rewrite HMRs1. apply add_vec_zero_l. }
    assert (HE24csp : E24 !!! Regidx csp_rs1 = spr) by (rewrite /E24 upd_ne; [exact HMRcsp | vm_compute; discriminate]).
    (* +0x26 c.ldsp ra,40(sp) *)
    iPoseProof (hsl_26 with "Htext") as "Hi26".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.holdingsleep + 0x26)) (mword_of_int 5 : mword 6) (mword_of_int 1 : mword 5)
              E24 (av - 6)%nat (m !!! Regidx (mword_of_int 1 : mword 5)) b (dqm := DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi26 [Hslot_ra] [-]").
    { iEval (rewrite HE24csp Hb1). iExact "Hslot_ra". }
    iIntros (CIDe2 Hse2) "Hcg Hpc Hslot_ra".
    iEval (rewrite HE24csp Hb1) in "Hslot_ra".
    set (E26 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 1 : mword 5))]> E24).
    change (<[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 1 : mword 5))]> E24) with E26.
    assert (Hpp28 : add_vec_int (mword_of_int (KernelSyms.holdingsleep + 0x26) : mword 64) 2 = mword_of_int (KernelSyms.holdingsleep + 0x28)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp28) in "Hpc".
    assert (HE26csp : E26 !!! Regidx csp_rs1 = spr) by (rewrite /E26 upd_ne; [exact HE24csp | vm_compute; discriminate]).
    (* +0x28 c.ldsp s0,32(sp) *)
    iPoseProof (hsl_28 with "Htext") as "Hi28".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.holdingsleep + 0x28)) (mword_of_int 4 : mword 6) (mword_of_int 8 : mword 5)
              E26 (av - 6)%nat (m !!! Regidx (mword_of_int 8 : mword 5)) b (dqm := DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi28 [Hslot_s0] [-]").
    { iEval (rewrite HE26csp Hb2). iExact "Hslot_s0". }
    iIntros (CIDe3 Hse3) "Hcg Hpc Hslot_s0".
    iEval (rewrite HE26csp Hb2) in "Hslot_s0".
    set (E28 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 8 : mword 5))]> E26).
    change (<[Regidx (mword_of_int 8 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 8 : mword 5))]> E26) with E28.
    assert (Hpp2a : add_vec_int (mword_of_int (KernelSyms.holdingsleep + 0x28) : mword 64) 2 = mword_of_int (KernelSyms.holdingsleep + 0x2a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp2a) in "Hpc".
    assert (HE28csp : E28 !!! Regidx csp_rs1 = spr) by (rewrite /E28 upd_ne; [exact HE26csp | vm_compute; discriminate]).
    (* +0x2a c.ldsp s1,24(sp) *)
    iPoseProof (hsl_2a with "Htext") as "Hi2a".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.holdingsleep + 0x2a)) (mword_of_int 3 : mword 6) (mword_of_int 9 : mword 5)
              E28 (av - 6)%nat (m !!! Regidx (mword_of_int 9 : mword 5)) b (dqm := DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi2a [Hslot_s1] [-]").
    { iEval (rewrite HE28csp Hb3). iExact "Hslot_s1". }
    iIntros (CIDe4 Hse4) "Hcg Hpc Hslot_s1".
    iEval (rewrite HE28csp Hb3) in "Hslot_s1".
    set (E2a := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 9 : mword 5))]> E28).
    change (<[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 9 : mword 5))]> E28) with E2a.
    assert (Hpp2c : add_vec_int (mword_of_int (KernelSyms.holdingsleep + 0x2a) : mword 64) 2 = mword_of_int (KernelSyms.holdingsleep + 0x2c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp2c) in "Hpc".
    assert (HE2acsp : E2a !!! Regidx csp_rs1 = spr) by (rewrite /E2a upd_ne; [exact HE28csp | vm_compute; discriminate]).
    (* +0x2c c.ldsp s2,16(sp) *)
    iPoseProof (hsl_2c with "Htext") as "Hi2c".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.holdingsleep + 0x2c)) (mword_of_int 2 : mword 6) (mword_of_int 18 : mword 5)
              E2a (av - 6)%nat (m !!! Regidx (mword_of_int 18 : mword 5)) b (dqm := DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi2c [Hslot_s2] [-]").
    { iEval (rewrite HE2acsp Hb4). iExact "Hslot_s2". }
    iIntros (CIDe5 Hse5) "Hcg Hpc Hslot_s2".
    iEval (rewrite HE2acsp Hb4) in "Hslot_s2".
    set (E2c := <[Regidx (mword_of_int 18 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 18 : mword 5))]> E2a).
    change (<[Regidx (mword_of_int 18 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 18 : mword 5))]> E2a) with E2c.
    assert (Hpp2e : add_vec_int (mword_of_int (KernelSyms.holdingsleep + 0x2c) : mword 64) 2 = mword_of_int (KernelSyms.holdingsleep + 0x2e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp2e) in "Hpc".
    assert (HE2ccsp : E2c !!! Regidx csp_rs1 = spr) by (rewrite /E2c upd_ne; [exact HE2acsp | vm_compute; discriminate]).
    (* +0x2e c.addi16sp sp,48 : frame pop (6) *)
    set (E2e := <[Regidx csp_rs1 := regval_into_reg (add_vec (E2c !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 3 : mword 6))))]> E2c).
    assert (Hpopval : add_vec (E2c !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 3 : mword 6))) = sp0).
    { rewrite HE2ccsp. unfold spr. rewrite pa_stk_off2.
      replace (mword_of_int (bv_wrap 64 (uint (sign_extend' 64 (caddi16sp_imm (mword_of_int 61 : mword 6)) : mword 64) + uint (sign_extend' 64 (caddi16sp_imm (mword_of_int 3 : mword 6)) : mword 64))) : mword 64) with (mword_of_int 0 : mword 64) by (apply bv_eq; vm_compute; reflexivity).
      change (add_vec sp0 (mword_of_int 0)) with (add_vec_int sp0 0). apply avi0. }
    assert (Hpop : E2c !!! Regidx csp_rs1 = pa_stk (add_vec (E2c !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 3 : mword 6)))) 6).
    { rewrite Hpopval HE2ccsp. exact Hspr6. }
    iAssert (stack_own sp0 6) with "[Hslot_ra Hslot_s0 Hslot_s1 Hslot_s2 Hslot_s3 S6]" as "Hframe6".
    { rewrite stack_own_slots. cbn [seq].
      iSplitL "Hslot_ra"; [iExists _; iExact "Hslot_ra"|].
      iSplitL "Hslot_s0"; [iExists _; iExact "Hslot_s0"|].
      iSplitL "Hslot_s1"; [iExists _; iExact "Hslot_s1"|].
      iSplitL "Hslot_s2"; [iExists _; iExact "Hslot_s2"|].
      iSplitL "Hslot_s3"; [iExists _; iExact "Hslot_s3"|].
      iSplitL "S6"; [iExact "S6"|]. done. }
    iEval (rewrite -Hpopval) in "Hframe6".
    iPoseProof (hsl_2e with "Htext") as "Hi2e".
    iApply (wp_caddi16sp_pop_s_sconf (mword_of_int (KernelSyms.holdingsleep + 0x2e)) (mword_of_int 3 : mword 6) E2c (av - 6)%nat 6 b Hpop
              with "Hcg Hpc Hi2e Hframe6 [-]").
    iIntros (CIDe6 Hse6) "Hcg Hpc".
    assert (Hav6 : ((av - 6) + 6)%nat = av) by lia.
    iEval (rewrite Hav6) in "Hcg".
    change (<[Regidx csp_rs1 := regval_into_reg (add_vec (E2c !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 3 : mword 6))))]> E2c) with E2e.
    assert (Hpp30 : add_vec_int (mword_of_int (KernelSyms.holdingsleep + 0x2e) : mword 64) 2 = mword_of_int (KernelSyms.holdingsleep + 0x30)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp30) in "Hpc".
    (* +0x30 c.ret *)
    assert (HE2era : E2e !!! Regidx (mword_of_int 1 : mword 5) = m !!! Regidx (mword_of_int 1 : mword 5)).
    { rewrite /E2e upd_ne; [| vm_compute; discriminate].
      rewrite /E2c upd_ne; [| vm_compute; discriminate].
      rewrite /E2a upd_ne; [| vm_compute; discriminate].
      rewrite /E28 upd_ne; [| vm_compute; discriminate].
      rewrite /E26 upd_eq; reflexivity. }
    iPoseProof (hsl_30 with "Htext") as "Hi30".
    iApply (wp_cret_s_sconf (mword_of_int (KernelSyms.holdingsleep + 0x30)) (mword_of_int 1 : mword 5) E2e av b
              ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi30 [-]").
    iIntros (CIDe7 Hse7) "Hcg Hpc".
    assert (Hretfin : ret_pc (E2e !!! Regidx (mword_of_int 1 : mword 5)) = ret_tgt)
      by (rewrite HE2era; reflexivity).
    iEval (rewrite Hretfin) in "Hpc".
    (* ===================== return ===================== *)
    (* register-preservation: sp / restored frame regs / threaded regs. *)
    assert (HE2e_csp : E2e !!! Regidx csp_rs1 = m !!! Regidx csp_rs1)
      by (rewrite /E2e upd_eq; exact Hpopval).
    assert (HE2e_s0 : E2e !!! Regidx (mword_of_int 8 : mword 5) = m !!! Regidx (mword_of_int 8 : mword 5)).
    { rewrite /E2e upd_ne; [| vm_compute; discriminate].
      rewrite /E2c upd_ne; [| vm_compute; discriminate].
      rewrite /E2a upd_ne; [| vm_compute; discriminate].
      rewrite /E28 upd_eq; reflexivity. }
    assert (HE2e_s1 : E2e !!! Regidx (mword_of_int 9 : mword 5) = m !!! Regidx (mword_of_int 9 : mword 5)).
    { rewrite /E2e upd_ne; [| vm_compute; discriminate].
      rewrite /E2c upd_ne; [| vm_compute; discriminate].
      rewrite /E2a upd_eq; reflexivity. }
    assert (HE2e_s2 : E2e !!! Regidx (mword_of_int 18 : mword 5) = m !!! Regidx (mword_of_int 18 : mword 5)).
    { rewrite /E2e upd_ne; [| vm_compute; discriminate].
      rewrite /E2c upd_eq; reflexivity. }
    assert (HE2e_a0 : E2e !!! Regidx (mword_of_int 10 : mword 5) = (mword_of_int 1 : mword 64)).
    { rewrite /E2e upd_ne; [| vm_compute; discriminate].
      rewrite /E2c upd_ne; [| vm_compute; discriminate].
      rewrite /E2a upd_ne; [| vm_compute; discriminate].
      rewrite /E28 upd_ne; [| vm_compute; discriminate].
      rewrite /E26 upd_ne; [| vm_compute; discriminate]. exact HE24a0. }
    assert (HE2e_s3 : E2e !!! Regidx (mword_of_int 19 : mword 5) = m !!! Regidx (mword_of_int 19 : mword 5)).
    { rewrite /E2e upd_ne; [| vm_compute; discriminate].
      rewrite /E2c upd_ne; [| vm_compute; discriminate].
      rewrite /E2a upd_ne; [| vm_compute; discriminate].
      rewrite /E28 upd_ne; [| vm_compute; discriminate].
      rewrite /E26 upd_ne; [| vm_compute; discriminate].
      rewrite /E24 upd_ne; [| vm_compute; discriminate].
      rewrite (callee_saved_lookup HcsMR (mword_of_int 19 : mword 5) ltac:(vm_compute; reflexivity)).
      rewrite /D20 upd_ne; [| vm_compute; discriminate].
      rewrite /D1e upd_ne; [| vm_compute; discriminate].
      rewrite /C46 upd_eq. reflexivity. }
    (* the threaded callee-saved registers (tp, s4..s11): unchanged by holdingsleep. *)
    assert (Hthr : forall r : mword 5, is_cs_idx r = true ->
                     r <> csp_rs1 -> r <> mword_of_int 8 -> r <> mword_of_int 9 ->
                     r <> mword_of_int 18 -> r <> mword_of_int 19 ->
                     E2e !!! Regidx r = m !!! Regidx r).
    { intros r Hr Ncsp N8 N9 N18 N19.
      assert (N1 : r <> mword_of_int 1) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      assert (N10 : r <> mword_of_int 10) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      assert (N15 : r <> mword_of_int 15) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      rewrite /E2e upd_ne; [| congruence].
      rewrite /E2c upd_ne; [| congruence].
      rewrite /E2a upd_ne; [| congruence].
      rewrite /E28 upd_ne; [| congruence].
      rewrite /E26 upd_ne; [| congruence].
      rewrite /E24 upd_ne; [| congruence].
      rewrite (callee_saved_lookup HcsMR r Hr).
      rewrite /D20 upd_ne; [| congruence].
      rewrite /D1e upd_ne; [| congruence].
      rewrite /C46 upd_ne; [| congruence].
      rewrite /C42 upd_ne; [| congruence].
      rewrite /C3e upd_ne; [| congruence].
      rewrite /C3c upd_ne; [| congruence].
      rewrite (callee_saved_lookup HcsMP r Hr).
      rewrite /Bj upd_ne; [| congruence].
      rewrite /B34 upd_ne; [| congruence].
      rewrite /B18 upd_ne; [| congruence].
      rewrite (callee_saved_lookup HcsA r Hr).
      rewrite /M5 upd_ne; [| congruence].
      rewrite /M4 upd_ne; [| congruence].
      rewrite /M3 upd_ne; [| congruence].
      rewrite /M2 upd_ne; [| congruence].
      rewrite /M1 upd_ne; [| congruence].
      rewrite /M0 upd_ne; [| congruence]. reflexivity. }
    (* [Hcnt] was delivered at [CIDrel] by release's own [wp_next]; the seven
       epilogue instructions above each moved to a FRESH hart (CIDe1..CIDe7),
       so holdingsleep's own continuation wants it at CIDe7.  ONE line, no
       case split on [b]. *)
    iDestruct (cpu_own_transport CIDrel CIDe7 0%nat b p C b ltac:(wp_next_chain)
                 with "Hcnt") as "Hcnt".
    iSpecialize ("Hcont" $! CIDe7 with "[%]"); [wp_next_chain|].
    iApply ("Hcont" $! E2e with "[%] Hcg Hcnt Hpc Hsl Hpidfield Hpidproc").
    { split.
      - unfold callee_saved.
        split; [exact HE2e_csp|].
        split; [exact HE2e_s0|].
        split; [exact HE2e_s1|].
        split; [exact HE2e_s2|].
        split; [exact HE2e_s3|].
        split; [apply Hthr; vm_compute; first [reflexivity | discriminate]|].
        split; [apply Hthr; vm_compute; first [reflexivity | discriminate]|].
        split; [apply Hthr; vm_compute; first [reflexivity | discriminate]|].
        split; [apply Hthr; vm_compute; first [reflexivity | discriminate]|].
        split; [apply Hthr; vm_compute; first [reflexivity | discriminate]|].
        split; [apply Hthr; vm_compute; first [reflexivity | discriminate]|].
        split; [apply Hthr; vm_compute; first [reflexivity | discriminate]|].
        apply Hthr; vm_compute; first [reflexivity | discriminate].
      - exact HE2e_a0. }
  Qed.

End ProofHoldingsleep.

End HoldingsleepProof.
