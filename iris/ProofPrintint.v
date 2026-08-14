(* ProofPrintint.v -- the whole-function WP for xv6's printint() over the
   SIE-agnostic sconf world.

     static void printint(long long xx, int base, int sign) {
       char buf[20]; int i; unsigned long long x;
       if (sign && (sign = (xx < 0))) x = -xx; else x = xx;
       i = 0;
       do { buf[i++] = digits[x % base]; } while ((x /= base) != 0);
       if (sign) buf[i++] = '-';
       while (--i >= 0) consputc(buf[i]);
     }

   Fifty instructions, an 8-slot frame, two loops and four join points.  The
   three things that make it more than a longer consputc:

   - [buf] is a BYTE array inside the frame: it starts at [s0-56 = pa_stk sp0 7]
     and covers slots 7, 6 and the low half of 5, so those three slots are
     carved into 24 individual bytes for the duration (StackBytes.v) and rebuilt
     at the epilogue.  Since [bytes_own] does not name contents, a written digit
     and an untouched byte are the same resource -- which is why neither loop
     has to say anything about what it wrote.

   - the do-while's real obligation is that it stays inside those bytes.  That
     is [digit_step] (PrintintArith.v): with [10 <= base] one decimal digit
     falls off [x] per iteration, so a [10^f] bound on the value bounds the
     remaining iterations by [f], and the whole run fits in [buf].  This is
     where the spec's [10 <= uint base] premise is spent; the [<= 16] premise is
     spent on the [digits[x % base]] read.

   - [s1] is saved LAZILY (0x60) and restored at 0x82, only on the path that
     enters the print loop, so slot 3 is owned as a bare [∃ w] on the other
     path.  Both paths reach the epilogue at 0x84, which is therefore proved
     once against an arbitrary map agreeing with the entry map on the
     callee-saved registers it does not itself restore.

   THE CALLEE CHANGED, NOT THIS FUNCTION.  printk.c's [panicking]/[panicked]
   globals are gone and uartputc_sync now takes the [tx_lock] SPINLOCK around
   each byte, so consputc's contract no longer threads flag cells or the
   transmitter token: what printint carries in their place is the ordinary
   spinlock-caller accounting ([cpu_own] in and out UNCHANGED, [panic_wp_any],
   the [n + 1 < 2^31] transient bound) plus the persistent [is_txlock].

   THAT SIMPLIFIES THE PRINT LOOP.  Its induction used to thread the LINEAR
   [uart_tx_own γd (l ++ bs_so_far)] across the back-edge; the trace claim is
   now [uart_sent_sub γd (bs ++ cs_so_far)], a persistent SUBLIST statement
   (the lock is re-acquired per byte, so another hart may interleave between
   two of our digits -- see UartTxInv.v).  So the loop hands on no trace
   resource at all, only a longer list; the one linear thing crossing the edge
   is [cpu_own], and it crosses at the same [n eb p C b] it entered with.
   [cpu_own] is [CpuId]-indexed, which is the only new bookkeeping: every
   branch or call that may land on a different hart needs a
   [cpu_own_transport] first. *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_var gen_heap invariants.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import RiscvLang RiscvPtsto RiscvExtras RiscvModelBytes.
Require Import RegFile InstrBytes WpMmodeLeafBase.
Require Import SmodeCore.
Require Import StackOwn StackBytes CalleeSaved KernelText KernelDataInv.
Require Import KernelRvcDecode.
Require Import WpSconfAlu WpSconfMem WpSconfCtl WpSconfBtype WpSmodeIntr.
Require Import DiskPtsto WpUart.
Require Import IntrDefs HartTp WpNext WpSconfVc.
Require Import WpLock.
Require Import CpuOwn.
Require Import UartTxInv.
Require Import PanicStub.
Require Import ByteCursor PrintintArith.
Require Import CodePrintint.
Require Import SpecConsputc SpecPrintint.
From Kernel Require KernelInstrs KernelData.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.
Import Defs.

(* clean-context (mword-free) nat bounds.  [printint_stack = 24] is printint's
   own 8-slot frame over consputc's 16, so the residual budget handed to the
   callee is exactly [consputc_stack]. *)
Lemma pi_cap_bounds (K : nat) :
  (printint_stack <= K)%nat -> (8 <= K)%nat /\ (consputc_stack <= K - 8)%nat.
Proof. unfold printint_stack, consputc_stack. lia. Qed.

Lemma pi_nk (K : nat) : (8 <= K)%nat -> ((K - 8) + 8)%nat = K.
Proof. lia. Qed.

Module PrintintProof (Consputc : CONSPUTC) : PRINTINT.

Section ProofPrintint.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ}.
  Context `{!uartGhostG Σ, !diskGhostG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.


  Ltac reg_neq :=
    lazymatch goal with
    | |- ?a <> ?b => tryif unify a b then fail else (vm_compute; discriminate)
    end.

  Local Notation ra_idx := (mword_of_int 1 : mword 5).
  Local Notation t1_idx := (mword_of_int 6 : mword 5).
  Local Notation s0_idx := (mword_of_int 8 : mword 5).
  Local Notation s1_idx := (mword_of_int 9 : mword 5).
  Local Notation a0_idx := (mword_of_int 10 : mword 5).
  Local Notation a1_idx := (mword_of_int 11 : mword 5).
  Local Notation a2_idx := (mword_of_int 12 : mword 5).
  Local Notation a3_idx := (mword_of_int 13 : mword 5).
  Local Notation a4_idx := (mword_of_int 14 : mword 5).
  Local Notation a5_idx := (mword_of_int 15 : mword 5).
  Local Notation a6_idx := (mword_of_int 16 : mword 5).
  Local Notation a7_idx := (mword_of_int 17 : mword 5).
  Local Notation s2_idx := (mword_of_int 18 : mword 5).

  (* ================================================================== *)
  (*  THE SHARED EPILOGUE (0x84 .. 0x8c).                                *)
  (* ================================================================== *)

  Lemma wp_printint_epi `{CID0 : CpuId}
      (m mc : regfile) (K : nat) (b : bool) (pcur : mword 64) :
    let sp0 := m !!! Regidx csp_rs1 in
    let spd := add_vec sp0 (sign_extend' 64 (caddi16sp_imm (mword_of_int 60 : mword 6))) in
    (8 <= K)%nat ->
    mc !!! Regidx csp_rs1 = spd ->
    (forall c : mword 5, is_cs_idx c = true -> c <> csp_rs1 -> c <> s0_idx -> c <> s2_idx ->
       mc !!! Regidx c = m !!! Regidx c) ->
    sie_cap_gpr mc (K - 8)%nat b pcur -∗
    kernel_text -∗
    pc_is (mword_of_int (KernelSyms.printint + 0x84) : mword 64) -∗
    (pa_stk sp0 1) ↦₈ (m !!! Regidx ra_idx) -∗
    (pa_stk sp0 2) ↦₈ (m !!! Regidx s0_idx) -∗
    (∃ v : mword 64, (pa_stk sp0 3) ↦₈ v) -∗
    (pa_stk sp0 4) ↦₈ (m !!! Regidx s2_idx) -∗
    (∃ v : mword 64, (pa_stk sp0 5) ↦₈ v) -∗
    (∃ v : mword 64, (pa_stk sp0 6) ↦₈ v) -∗
    (∃ v : mword 64, (pa_stk sp0 7) ↦₈ v) -∗
    (∃ v : mword 64, (pa_stk sp0 8) ↦₈ v) -∗
    wp_next b pcur (fun (CID : CpuId) =>
      ∀ mf,
      sie_cap_gpr mf K b pcur -∗
      pc_is (ret_pc (m !!! Regidx ra_idx)) -∗
      ⌜ callee_saved m mf /\ mf !!! Regidx ra_idx = m !!! Regidx ra_idx ⌝ -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros sp0 spd HK Hsp Hagree.
    iIntros "Hcg #Htext Hpc Hc1 Hc2 Hc3 Hc4 Hc5 Hc6 Hc7 Hc8 Hcont".
    iPoseProof (pii_84 with "Htext") as "Hi84".
    iPoseProof (pii_86 with "Htext") as "Hi86".
    iPoseProof (pii_88 with "Htext") as "Hi88".
    iPoseProof (pii_8a with "Htext") as "Hi8a".
    iPoseProof (pii_8c with "Htext") as "Hi8c".
    (* the pushed sp, in the [pa_stk] form the frame cells are indexed by.  NB
       the two forms must BOTH stay available: the slot addresses want
       [pa_stk], and the epilogue's cancellation wants the [caddi16sp_imm]
       form ([frame_cancel_64]).  Never [vm_compute] a goal mentioning [sp0]. *)
    assert (Hpush : spd = pa_stk sp0 8).
    { unfold spd, pa_stk, add_vec_int. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb1 : add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 7 : mword 6) ('b"000"))) = pa_stk sp0 1).
    { rewrite Hpush. unfold pa_stk, add_vec_int. rewrite pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb2 : add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 6 : mword 6) ('b"000"))) = pa_stk sp0 2).
    { rewrite Hpush. unfold pa_stk, add_vec_int. rewrite pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb4 : add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000"))) = pa_stk sp0 4).
    { rewrite Hpush. unfold pa_stk, add_vec_int. rewrite pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    (* +0x84 ld ra,56(sp) *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.printint + 0x84)) (mword_of_int 7 : mword 6) ra_idx
              mc (K - 8)%nat (m !!! Regidx ra_idx) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi84 [Hc1]").
    { iEval (rewrite Hsp Hb1). iExact "Hc1". }
    iIntros (CID1 Hs1) "Hcg Hpc Hc1". iEval (rewrite Hsp Hb1) in "Hc1".
    set (E1 := <[Regidx ra_idx := regval_into_reg (m !!! Regidx ra_idx)]> mc).
    assert (HE1sp : E1 !!! Regidx csp_rs1 = spd)
      by (rewrite /E1 upd_ne; [exact Hsp | reg_neq]).
    assert (Hp86 : add_vec_int (mword_of_int (KernelSyms.printint + 0x84) : mword 64) 2 = mword_of_int (KernelSyms.printint + 0x86)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp86) in "Hpc".
    (* +0x86 ld s0,48(sp) *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.printint + 0x86)) (mword_of_int 6 : mword 6) s0_idx
              E1 (K - 8)%nat (m !!! Regidx s0_idx) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi86 [Hc2]").
    { iEval (rewrite HE1sp Hb2). iExact "Hc2". }
    iIntros (CID2 Hs2) "Hcg Hpc Hc2". iEval (rewrite HE1sp Hb2) in "Hc2".
    set (E2 := <[Regidx s0_idx := regval_into_reg (m !!! Regidx s0_idx)]> E1).
    assert (HE2sp : E2 !!! Regidx csp_rs1 = spd)
      by (rewrite /E2 upd_ne; [exact HE1sp | reg_neq]).
    assert (Hp88 : add_vec_int (mword_of_int (KernelSyms.printint + 0x86) : mword 64) 2 = mword_of_int (KernelSyms.printint + 0x88)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp88) in "Hpc".
    (* +0x88 ld s2,32(sp) *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.printint + 0x88)) (mword_of_int 4 : mword 6) s2_idx
              E2 (K - 8)%nat (m !!! Regidx s2_idx) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi88 [Hc4]").
    { iEval (rewrite HE2sp Hb4). iExact "Hc4". }
    iIntros (CID3 Hs3) "Hcg Hpc Hc4". iEval (rewrite HE2sp Hb4) in "Hc4".
    set (E3 := <[Regidx s2_idx := regval_into_reg (m !!! Regidx s2_idx)]> E2).
    assert (HE3sp : E3 !!! Regidx csp_rs1 = spd)
      by (rewrite /E3 upd_ne; [exact HE2sp | reg_neq]).
    assert (Hp8a : add_vec_int (mword_of_int (KernelSyms.printint + 0x88) : mword 64) 2 = mword_of_int (KernelSyms.printint + 0x8a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp8a) in "Hpc".
    (* +0x8a addi sp,sp,64 : the frame pop *)
    assert (Hwv : add_vec (E3 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 4 : mword 6))) = sp0).
    { rewrite HE3sp. unfold spd. apply frame_cancel_64. }
    assert (Hpop : E3 !!! Regidx csp_rs1 = pa_stk (add_vec (E3 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 4 : mword 6)))) 8).
    { rewrite Hwv HE3sp. exact Hpush. }
    iAssert (stack_own sp0 8) with "[Hc1 Hc2 Hc3 Hc4 Hc5 Hc6 Hc7 Hc8]" as "Hframe".
    { rewrite stack_own_slots; cbn [seq].
      iSplitL "Hc1". { iExists (m !!! Regidx ra_idx). iExact "Hc1". }
      iSplitL "Hc2". { iExists (m !!! Regidx s0_idx). iExact "Hc2". }
      iSplitL "Hc3". { iExact "Hc3". }
      iSplitL "Hc4". { iExists (m !!! Regidx s2_idx). iExact "Hc4". }
      iSplitL "Hc5". { iExact "Hc5". }
      iSplitL "Hc6". { iExact "Hc6". }
      iSplitL "Hc7". { iExact "Hc7". }
      iSplitL "Hc8". { iExact "Hc8". }
      done. }
    iEval (rewrite -Hwv) in "Hframe".
    iApply (wp_caddi16sp_pop_s_sconf (mword_of_int (KernelSyms.printint + 0x8a)) (mword_of_int 4 : mword 6)
              E3 (K - 8)%nat 8 b Hpop with "Hcg Hpc Hi8a Hframe").
    iIntros (CID4 Hs4) "Hcg Hpc".
    set (E4 := <[Regidx csp_rs1 := regval_into_reg (add_vec (E3 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 4 : mword 6))))]> E3).
    iEval (rewrite (pi_nk K HK)) in "Hcg".
    assert (Hp8c : add_vec_int (mword_of_int (KernelSyms.printint + 0x8a) : mword 64) 2 = mword_of_int (KernelSyms.printint + 0x8c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp8c) in "Hpc".
    (* +0x8c ret *)
    assert (HE4ra : E4 !!! Regidx ra_idx = m !!! Regidx ra_idx).
    { rewrite /E4 upd_ne; [| reg_neq]. rewrite /E3 upd_ne; [| reg_neq].
      rewrite /E2 upd_ne; [| reg_neq]. rewrite /E1 upd_eq. reflexivity. }
    assert (Hrt : ret_pc (E4 !!! Regidx ra_idx) = ret_pc (m !!! Regidx ra_idx)) by (rewrite HE4ra; reflexivity).
    iApply (wp_cret_s_sconf (mword_of_int (KernelSyms.printint + 0x8c)) ra_idx E4 K b
              ltac:(vm_compute; discriminate) with "Hcg Hpc Hi8c").
    iIntros (CID5 Hs5) "Hcg Hpc". iEval (rewrite Hrt) in "Hpc".
    iSpecialize ("Hcont" $! CID5 with "[%]"); [wp_next_chain|].
    iApply ("Hcont" $! E4 with "Hcg Hpc [%]").
    split; [| exact HE4ra ].
    assert (Hthread : forall c : mword 5, is_cs_idx c = true ->
              c <> csp_rs1 -> c <> s0_idx -> c <> s2_idx -> E4 !!! Regidx c = m !!! Regidx c).
    { intros c Hc Nsp N8 N18.
      pose proof (is_cs_idx_true_neq ra_idx c ltac:(vm_compute; reflexivity) Hc) as N1.
      rewrite /E4 upd_ne; [| congruence].
      rewrite /E3 upd_ne; [| congruence].
      rewrite /E2 upd_ne; [| congruence].
      rewrite /E1 upd_ne; [| congruence].
      exact (Hagree c Hc Nsp N8 N18). }
    unfold callee_saved.
    split. { rewrite /E4 upd_eq. exact Hwv. }
    split. { rewrite /E4 upd_ne; [| reg_neq]. rewrite /E3 upd_ne; [| reg_neq].
             rewrite /E2 upd_eq; reflexivity. }
    split. { apply Hthread; vm_compute; first [reflexivity | discriminate]. }
    split. { rewrite /E4 upd_ne; [| reg_neq]. rewrite /E3 upd_eq; reflexivity. }
    repeat split; apply Hthread; vm_compute; first [reflexivity | discriminate].
  Qed.

  (* ================================================================== *)
  (*  THE DIGIT LOOP (0x22 .. 0x40): the do-while that fills [buf].      *)
  (* ================================================================== *)

  (* the [digits] table, as the sixteen persistent image bytes the loop may
     index -- their VALUES are irrelevant (the spec does not say what is
     printed), so they are existentially quantified per byte. *)
  Definition digits_tbl (dg : mword 64) : iProp Σ :=
    ([∗ list] j ∈ seq 0 16, ∃ b : bv 8, (pa_add dg j) ↦ₘ□ b)%I.

  (* the registers the loop body writes; everything else passes through *)
  Definition dl_kept (mf md : regfile) : Prop :=
    forall c : mword 5, c <> a0_idx -> c <> a2_idx -> c <> a3_idx ->
      c <> a4_idx -> c <> a5_idx -> c <> a7_idx -> mf !!! Regidx c = md !!! Regidx c.

  (* ---- ONE iteration, 0x22 .. 0x3e, handing over at the back-edge branch --- *)
  Lemma wp_printint_dbody `{CID0 : CpuId} (K : nat)
      (buf dg : mword 64) (i : nat) (x : mword 64) (md : regfile) (b : bool) (pcur : mword 64) :
    (i < 24)%nat ->
    0 <= Z.of_nat i + 1 < 2^31 ->
    10 <= uint (md !!! Regidx a1_idx) <= 16 ->
    md !!! Regidx a0_idx = x ->
    md !!! Regidx a3_idx = pa_add buf i ->
    md !!! Regidx a4_idx = mword_of_int (Z.of_nat i) ->
    md !!! Regidx a6_idx = dg ->
    sie_cap_gpr md (K - 8)%nat b pcur -∗
    kernel_text -∗
    digits_tbl dg -∗
    pc_is (mword_of_int (KernelSyms.printint + 0x22) : mword 64) -∗
    bytes_own (DfracOwn 1) buf 24 -∗
    wp_next (CID0 := CID0) b pcur (fun (CID : CpuId) =>
      ∀ (mb : regfile),
      ⌜ mb !!! Regidx a0_idx = mword_of_int (Z.quot (uint x) (uint (md !!! Regidx a1_idx))) /\
        mb !!! Regidx a3_idx = pa_add buf (S i) /\
        mb !!! Regidx a4_idx = mword_of_int (Z.of_nat (S i)) /\
        mb !!! Regidx a2_idx = mword_of_int (Z.of_nat (S i)) /\
        mb !!! Regidx a7_idx = mword_of_int (Z.of_nat i) /\
        mb !!! Regidx a5_idx = x /\
        dl_kept mb md ⌝ -∗
      sie_cap_gpr mb (K - 8)%nat b pcur -∗
      pc_is (mword_of_int (KernelSyms.printint + 0x40) : mword 64) -∗
      bytes_own (DfracOwn 1) buf 24 -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hi24 Hi31 Hbase Ha0 Ha3 Ha4 Ha6.
    iIntros "Hcg #Htext #Hdig Hpc Hbuf Hcont".
    iPoseProof (pii_22 with "Htext") as "Hi22".
    iPoseProof (pii_24 with "Htext") as "Hi24".
    iPoseProof (pii_28 with "Htext") as "Hi28".
    iPoseProof (pii_2a with "Htext") as "Hi2a".
    iPoseProof (pii_2e with "Htext") as "Hi2e".
    iPoseProof (pii_30 with "Htext") as "Hi30".
    iPoseProof (pii_34 with "Htext") as "Hi34".
    iPoseProof (pii_38 with "Htext") as "Hi38".
    iPoseProof (pii_3a with "Htext") as "Hi3a".
    iPoseProof (pii_3e with "Htext") as "Hi3e".
    (* the base is nonzero, so both M-extension ops take their ordinary arm *)
    assert (Hbne : Z.eqb (uint (md !!! Regidx a1_idx)) 0 = false).
    { apply Z.eqb_neq. intro Hc. destruct Hbase as [Hb1 Hb2]. rewrite Hc in Hb1. lia. }
    (* the remainder is a legal index into the 16-byte table *)
    assert (Hrem : 0 <= Z.rem (uint x) (uint (md !!! Regidx a1_idx)) < 16).
    { destruct Hbase as [Hb1 Hb2].
      pose proof (pi_uint_nonneg x) as Hx0.
      split.
      - apply Z.rem_nonneg; lia.
      - apply (Z.lt_le_trans _ (uint (md !!! Regidx a1_idx))); [ | lia ].
        apply Z.rem_bound_pos_pos; lia. }
    assert (Hz0 : sign_extend' 64 (mword_of_int 0 : mword 12) = (mword_of_int 0 : mword 64))
      by (apply bv_eq; vm_compute; reflexivity).
    (* +0x22 c.mv a7,a4 *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.printint + 0x22)) a7_idx a4_idx md (K - 8)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi22").
    iIntros (CID1 Hs1) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (D1 := <[Regidx a7_idx := regval_into_reg (add_vec zero_reg (md !!! Regidx a4_idx))]> md).
    assert (HD1a4 : D1 !!! Regidx a4_idx = mword_of_int (Z.of_nat i))
      by (rewrite /D1 upd_ne; [exact Ha4 | reg_neq]).
    assert (Hp24 : add_vec_int (mword_of_int (KernelSyms.printint + 0x22) : mword 64) 2 = mword_of_int (KernelSyms.printint + 0x24)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp24) in "Hpc".
    (* +0x24 addiw a2,a4,1 *)
    iApply (wp_addiw_s_sconf (mword_of_int (KernelSyms.printint + 0x24)) a2_idx a4_idx (mword_of_int 1 : mword 12)
              D1 (K - 8)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi24").
    iIntros (CID2 Hs2) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (D2 := <[Regidx a2_idx := regval_into_reg (sign_extend' 64 (subrange_vec_dec
                 (add_vec (D1 !!! Regidx a4_idx) (sign_extend' 64 (mword_of_int 1 : mword 12))) 31 0))]> D1).
    assert (HD2a2 : D2 !!! Regidx a2_idx = mword_of_int (Z.of_nat (S i))).
    { rewrite /D2 upd_eq. unfold regval_into_reg. rewrite HD1a4.
      (* pass [e] EXPLICITLY: with it left as [_] the inline [vm_compute] runs
         against an evar and diverges (durable-notes: metavar-before-unification) *)
      rewrite (addiw_lit (Z.of_nat i) 1 (sign_extend' 64 (mword_of_int 1 : mword 12))
                 ltac:(apply bv_eq; vm_compute; reflexivity) Hi31).
      f_equal. rewrite Nat2Z.inj_succ. ring. }
    assert (Hp28 : add_vec_int (mword_of_int (KernelSyms.printint + 0x24) : mword 64) 4 = mword_of_int (KernelSyms.printint + 0x28)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp28) in "Hpc".
    (* +0x28 c.mv a4,a2 *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.printint + 0x28)) a4_idx a2_idx D2 (K - 8)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi28").
    iIntros (CID3 Hs3) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (D3 := <[Regidx a4_idx := regval_into_reg (add_vec zero_reg (D2 !!! Regidx a2_idx))]> D2).
    assert (HD3a0 : D3 !!! Regidx a0_idx = x).
    { rewrite /D3 upd_ne; [| reg_neq]. rewrite /D2 upd_ne; [| reg_neq].
      rewrite /D1 upd_ne; [exact Ha0 | reg_neq]. }
    assert (HD3a1 : D3 !!! Regidx a1_idx = md !!! Regidx a1_idx).
    { rewrite /D3 upd_ne; [| reg_neq]. rewrite /D2 upd_ne; [| reg_neq].
      rewrite /D1 upd_ne; [reflexivity | reg_neq]. }
    assert (Hp2a : add_vec_int (mword_of_int (KernelSyms.printint + 0x28) : mword 64) 2 = mword_of_int (KernelSyms.printint + 0x2a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp2a) in "Hpc".
    (* +0x2a remu a5,a0,a1 : x % base *)
    iApply (wp_remu_s_sconf (mword_of_int (KernelSyms.printint + 0x2a)) a5_idx a0_idx a1_idx
              (mword_of_int (Z.rem (uint x) (uint (md !!! Regidx a1_idx))))
              D3 (K - 8)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(rgne; rgne; rewrite HD3a0 HD3a1 Hbne; apply tbt_moi)
              with "Hcg Hpc Hi2a").
    iIntros (CID4 Hs4) "Hcg Hpc".
    set (D4 := <[Regidx a5_idx := regval_into_reg
                  (mword_of_int (Z.rem (uint x) (uint (md !!! Regidx a1_idx))) : mword 64)]> D3).
    assert (HD4a5 : D4 !!! Regidx a5_idx = mword_of_int (Z.rem (uint x) (uint (md !!! Regidx a1_idx))))
      by (rewrite /D4 upd_eq; reflexivity).
    assert (HD4a6 : D4 !!! Regidx a6_idx = dg).
    { rewrite /D4 upd_ne; [| reg_neq]. rewrite /D3 upd_ne; [| reg_neq].
      rewrite /D2 upd_ne; [| reg_neq]. rewrite /D1 upd_ne; [exact Ha6 | reg_neq]. }
    assert (Hp2e : add_vec_int (mword_of_int (KernelSyms.printint + 0x2a) : mword 64) 4 = mword_of_int (KernelSyms.printint + 0x2e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp2e) in "Hpc".
    (* +0x2e c.add a5,a5,a6 : &digits[x % base] *)
    iApply (wp_cadd_s_sconf (mword_of_int (KernelSyms.printint + 0x2e)) a5_idx a6_idx D4 (K - 8)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi2e").
    iIntros (CID5 Hs5) "Hcg Hpc".
    iEval (rgne; rgne) in "Hcg".
    set (D5 := <[Regidx a5_idx := regval_into_reg (add_vec (D4 !!! Regidx a5_idx) (D4 !!! Regidx a6_idx))]> D4).
    assert (HD5a5 : D5 !!! Regidx a5_idx
                    = pa_add dg (Z.to_nat (Z.rem (uint x) (uint (md !!! Regidx a1_idx))))).
    { rewrite /D5 upd_eq. unfold regval_into_reg. rewrite HD4a5 HD4a6.
      rewrite add_vec_pa_add. f_equal. f_equal.
      apply uint_moi_small. destruct Hrem as [Hr0 Hr16].
      change (2^64) with 18446744073709551616. lia. }
    assert (Hp30 : add_vec_int (mword_of_int (KernelSyms.printint + 0x2e) : mword 64) 2 = mword_of_int (KernelSyms.printint + 0x30)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp30) in "Hpc".
    (* +0x30 lbu a5,0(a5) : the digit character, out of the image *)
    iDestruct (big_sepL_lookup _ _ (Z.to_nat (Z.rem (uint x) (uint (md !!! Regidx a1_idx))))
                 (Z.to_nat (Z.rem (uint x) (uint (md !!! Regidx a1_idx)))) with "Hdig") as (dbyte) "Hdb".
    { rewrite lookup_seq_lt; [reflexivity | ].
      destruct Hrem as [Hr0 Hr16]. lia. }
    iApply (wp_lbu_s_sconf (mword_of_int (KernelSyms.printint + 0x30)) a5_idx a5_idx (mword_of_int 0 : mword 12)
              D5 (K - 8)%nat (dbyte : mword 8) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi30 [Hdb]").
    { iEval (rgne; rewrite HD5a5 Hz0 kv_addv_zero). iExact "Hdb". }
    iIntros (CID6 Hs6) "Hcg Hpc _".
    set (D6 := <[Regidx a5_idx := regval_into_reg (zero_extend' 64 (dbyte : mword 8))]> D5).
    assert (HD6a3 : D6 !!! Regidx a3_idx = pa_add buf i).
    { rewrite /D6 upd_ne; [| reg_neq]. rewrite /D5 upd_ne; [| reg_neq].
      rewrite /D4 upd_ne; [| reg_neq]. rewrite /D3 upd_ne; [| reg_neq].
      rewrite /D2 upd_ne; [| reg_neq]. rewrite /D1 upd_ne; [exact Ha3 | reg_neq]. }
    assert (Hp34 : add_vec_int (mword_of_int (KernelSyms.printint + 0x30) : mword 64) 4 = mword_of_int (KernelSyms.printint + 0x34)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp34) in "Hpc".
    (* +0x34 sb a5,0(a3) : buf[i] = digit *)
    iDestruct (bytes_own_acc (DfracOwn 1) buf 24 i Hi24 with "Hbuf") as "[Hbi Hbcl]".
    iDestruct "Hbi" as (bold) "Hbi".
    iApply (wp_sb_s_sconf (mword_of_int (KernelSyms.printint + 0x34)) a5_idx a3_idx (mword_of_int 0 : mword 12)
              D6 (K - 8)%nat (bold : mword 8) b with "Hcg Hpc Hi34 [Hbi]").
    { iEval (rgne; rewrite HD6a3 Hz0 kv_addv_zero). iExact "Hbi". }
    iIntros (CID7 Hs7) "Hcg Hpc Hbi". iEval (rgne; rewrite HD6a3 Hz0 kv_addv_zero) in "Hbi".
    iDestruct ("Hbcl" with "Hbi") as "Hbuf".
    assert (Hp38 : add_vec_int (mword_of_int (KernelSyms.printint + 0x34) : mword 64) 4 = mword_of_int (KernelSyms.printint + 0x38)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp38) in "Hpc".
    (* +0x38 c.mv a5,a0 : keep the OLD x for the back-edge test *)
    assert (HD6a0 : D6 !!! Regidx a0_idx = x).
    { rewrite /D6 upd_ne; [| reg_neq]. rewrite /D5 upd_ne; [| reg_neq].
      rewrite /D4 upd_ne; [| reg_neq]. exact HD3a0. }
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.printint + 0x38)) a5_idx a0_idx D6 (K - 8)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi38").
    iIntros (CID8 Hs8) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (D7 := <[Regidx a5_idx := regval_into_reg (add_vec zero_reg (D6 !!! Regidx a0_idx))]> D6).
    assert (HD7a5 : D7 !!! Regidx a5_idx = x).
    { rewrite /D7 upd_eq. unfold regval_into_reg. rewrite HD6a0. apply add_vec_zero_l. }
    assert (HD7a0 : D7 !!! Regidx a0_idx = x)
      by (rewrite /D7 upd_ne; [exact HD6a0 | reg_neq]).
    assert (HD7a1 : D7 !!! Regidx a1_idx = md !!! Regidx a1_idx).
    { rewrite /D7 upd_ne; [| reg_neq]. rewrite /D6 upd_ne; [| reg_neq].
      rewrite /D5 upd_ne; [| reg_neq]. rewrite /D4 upd_ne; [| reg_neq]. exact HD3a1. }
    assert (Hp3a : add_vec_int (mword_of_int (KernelSyms.printint + 0x38) : mword 64) 2 = mword_of_int (KernelSyms.printint + 0x3a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp3a) in "Hpc".
    (* +0x3a divu a0,a0,a1 : x /= base *)
    iApply (wp_divu_s_sconf (mword_of_int (KernelSyms.printint + 0x3a)) a0_idx a0_idx a1_idx
              (mword_of_int (Z.quot (uint x) (uint (md !!! Regidx a1_idx))))
              D7 (K - 8)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(rgne; rgne; rewrite HD7a0 HD7a1 Hbne; apply tbt_moi)
              with "Hcg Hpc Hi3a").
    iIntros (CID9 Hs9) "Hcg Hpc".
    set (D8 := <[Regidx a0_idx := regval_into_reg
                  (mword_of_int (Z.quot (uint x) (uint (md !!! Regidx a1_idx))) : mword 64)]> D7).
    assert (HD8a3 : D8 !!! Regidx a3_idx = pa_add buf i).
    { rewrite /D8 upd_ne; [| reg_neq]. rewrite /D7 upd_ne; [| reg_neq]. exact HD6a3. }
    assert (Hp3e : add_vec_int (mword_of_int (KernelSyms.printint + 0x3a) : mword 64) 4 = mword_of_int (KernelSyms.printint + 0x3e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp3e) in "Hpc".
    (* +0x3e c.addi a3,a3,1 : the cursor bump *)
    iApply (wp_caddi_s_sconf (mword_of_int (KernelSyms.printint + 0x3e)) a3_idx (mword_of_int 1 : mword 6)
              D8 (K - 8)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi3e").
    iIntros (CID10 Hs10) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (D9 := <[Regidx a3_idx := regval_into_reg
                  (add_vec (D8 !!! Regidx a3_idx) (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6))))]> D8).
    assert (Hp40 : add_vec_int (mword_of_int (KernelSyms.printint + 0x3e) : mword 64) 2 = mword_of_int (KernelSyms.printint + 0x40)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp40) in "Hpc".
    (* hand over at the branch *)
    iSpecialize ("Hcont" $! CID10 with "[%]"); [wp_next_chain|].
    iApply ("Hcont" $! D9 with "[%] Hcg Hpc Hbuf").
    assert (Hkeep : forall c : mword 5, c <> a0_idx -> c <> a2_idx -> c <> a3_idx ->
              c <> a4_idx -> c <> a5_idx -> c <> a7_idx -> D9 !!! Regidx c = md !!! Regidx c).
    { intros c N0 N2 N3 N4 N5 N7.
      rewrite /D9 upd_ne; [| congruence].
      rewrite /D8 upd_ne; [| congruence].
      rewrite /D7 upd_ne; [| congruence].
      rewrite /D6 upd_ne; [| congruence].
      rewrite /D5 upd_ne; [| congruence].
      rewrite /D4 upd_ne; [| congruence].
      rewrite /D3 upd_ne; [| congruence].
      rewrite /D2 upd_ne; [| congruence].
      rewrite /D1 upd_ne; [reflexivity | congruence]. }
    split.
    { rewrite /D9 upd_ne; [| reg_neq]. rewrite /D8 upd_eq. reflexivity. }
    split.
    { rewrite /D9 upd_eq. unfold regval_into_reg. rewrite HD8a3.
      apply pa_add_step. apply bv_eq; vm_compute; reflexivity. }
    split.
    { rewrite /D9 upd_ne; [| reg_neq]. rewrite /D8 upd_ne; [| reg_neq].
      rewrite /D7 upd_ne; [| reg_neq]. rewrite /D6 upd_ne; [| reg_neq].
      rewrite /D5 upd_ne; [| reg_neq]. rewrite /D4 upd_ne; [| reg_neq].
      rewrite /D3 upd_eq. unfold regval_into_reg. rewrite HD2a2. apply add_vec_zero_l. }
    split.
    { rewrite /D9 upd_ne; [| reg_neq]. rewrite /D8 upd_ne; [| reg_neq].
      rewrite /D7 upd_ne; [| reg_neq]. rewrite /D6 upd_ne; [| reg_neq].
      rewrite /D5 upd_ne; [| reg_neq]. rewrite /D4 upd_ne; [| reg_neq].
      rewrite /D3 upd_ne; [| reg_neq]. exact HD2a2. }
    split.
    { rewrite /D9 upd_ne; [| reg_neq]. rewrite /D8 upd_ne; [| reg_neq].
      rewrite /D7 upd_ne; [| reg_neq]. rewrite /D6 upd_ne; [| reg_neq].
      rewrite /D5 upd_ne; [| reg_neq]. rewrite /D4 upd_ne; [| reg_neq].
      rewrite /D3 upd_ne; [| reg_neq]. rewrite /D2 upd_ne; [| reg_neq].
      rewrite /D1 upd_eq. unfold regval_into_reg. rewrite Ha4. apply add_vec_zero_l. }
    split.
    { rewrite /D9 upd_ne; [| reg_neq]. rewrite /D8 upd_ne; [| reg_neq]. exact HD7a5. }
    exact Hkeep.
  Qed.

  (* ---- the loop itself: induction on the digit FUEL ---- *)
  Lemma wp_printint_digits (K : nat)
      (buf dg : mword 64) (b : bool) (pcur : mword 64) :
    forall (f i : nat) `(CID0 : CpuId) (x : mword 64) (md : regfile),
    (i + f <= 20)%nat ->
    uint x < 10 ^ (Z.of_nat f) ->
    10 <= uint (md !!! Regidx a1_idx) <= 16 ->
    md !!! Regidx a0_idx = x ->
    md !!! Regidx a3_idx = pa_add buf i ->
    md !!! Regidx a4_idx = mword_of_int (Z.of_nat i) ->
    md !!! Regidx a6_idx = dg ->
    sie_cap_gpr md (K - 8)%nat b pcur -∗
    kernel_text -∗
    digits_tbl dg -∗
    pc_is (mword_of_int (KernelSyms.printint + 0x22) : mword 64) -∗
    bytes_own (DfracOwn 1) buf 24 -∗
    wp_next (CID0 := CID0) b pcur (fun (CID : CpuId) =>
      ∀ (mf : regfile) (i' : nat),
      ⌜ (1 <= i')%nat /\ (i' <= 21)%nat /\
        mf !!! Regidx a2_idx = mword_of_int (Z.of_nat i') /\
        mf !!! Regidx a4_idx = mword_of_int (Z.of_nat i') /\
        mf !!! Regidx a7_idx = mword_of_int (Z.of_nat (i' - 1)) /\
        dl_kept mf md ⌝ -∗
      sie_cap_gpr mf (K - 8)%nat b pcur -∗
      pc_is (mword_of_int (KernelSyms.printint + 0x44) : mword 64) -∗
      bytes_own (DfracOwn 1) buf 24 -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    induction f as [|f' IH]; intros i CID0 x md Hif Hxf Hbase Ha0 Ha3 Ha4 Ha6;
      iIntros "Hcg #Htext #Hdig Hpc Hbuf Hcont";
      iPoseProof (pii_40 with "Htext") as "Hi40";
      iApply (wp_printint_dbody (CID0 := CID0) K buf dg i x md b pcur
                ltac:(lia) ltac:(change (2^31) with 2147483648; lia)
                Hbase Ha0 Ha3 Ha4 Ha6
                with "Hcg Htext Hdig Hpc Hbuf");
      iIntros (CIDb Hsb mb) "%Hb Hcg Hpc Hbuf";
      destruct Hb as (Hb0 & Hb3 & Hb4 & Hb2 & Hb7 & Hb5 & Hbk);
      destruct (Z.geb (uint x) (uint (md !!! Regidx a1_idx))) eqn:Hcmp.
    - (* fuel 0, back edge taken: impossible -- [x < 10^0 = 1] cannot reach base *)
      exfalso.
      apply Z.geb_le in Hcmp.
      change (Z.of_nat 0) with 0 in Hxf. rewrite Z.pow_0_r in Hxf.
      destruct Hbase as [Hb1 _]. lia.
    - (* fuel 0, fall through: one digit written, done *)
      iApply (wp_bgeu_fall_s_sconf (mword_of_int (KernelSyms.printint + 0x40)) (mword_of_int 8162 : mword 13)
                a1_idx a5_idx mb (K - 8)%nat b
                ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                ltac:(rgne; rgne; unfold zopz0zKzJ_u; rewrite Hb5 (Hbk a1_idx ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)); exact Hcmp)
                with "Hcg Hpc Hi40").
      iIntros (CIDc Hsc) "Hcg Hpc".
      assert (Hp44 : add_vec_int (mword_of_int (KernelSyms.printint + 0x40) : mword 64) 4 = mword_of_int (KernelSyms.printint + 0x44)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp44) in "Hpc".
      iSpecialize ("Hcont" $! CIDc with "[%]"); [wp_next_chain|].
      iApply ("Hcont" $! mb (S i) with "[%] Hcg Hpc Hbuf").
      split; [lia | ]. split; [lia | ]. split; [exact Hb2 | ]. split; [exact Hb4 | ].
      split; [ replace (S i - 1)%nat with i by lia; exact Hb7 | exact Hbk ].
    - (* fuel S f', back edge TAKEN: recurse on the quotient *)
      iApply (wp_bgeu_taken_s_sconf (mword_of_int (KernelSyms.printint + 0x40)) (mword_of_int 8162 : mword 13)
                a1_idx a5_idx mb (K - 8)%nat b
                ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                ltac:(rgne; rgne; unfold zopz0zKzJ_u; rewrite Hb5 (Hbk a1_idx ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)); exact Hcmp)
                ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi40").
      iApply bi.later_intro. iIntros (CIDc Hsc) "Hcg Hpc".
      assert (Htgt : add_vec (mword_of_int (KernelSyms.printint + 0x40) : mword 64) (sign_extend' 64 (mword_of_int 8162 : mword 13)) = mword_of_int (KernelSyms.printint + 0x22)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Htgt) in "Hpc".
      (* the fuel drops because a base-[base] digit fell off *)
      apply Z.geb_le in Hcmp.
      pose proof (digit_step (uint x) (uint (md !!! Regidx a1_idx)) (S f')
                    (pi_uint_nonneg x) (proj1 Hbase) Hcmp Hxf) as [_ Hq].
      replace (S f' - 1)%nat with f' in Hq by lia.
      assert (Hq0 : 0 <= Z.quot (uint x) (uint (md !!! Regidx a1_idx))).
      { apply quot_nonneg; [ apply pi_uint_nonneg | ]. destruct Hbase as [Hb1 _]. lia. }
      assert (Hq64 : Z.quot (uint x) (uint (md !!! Regidx a1_idx)) < 2^64).
      { apply (Z.le_lt_trans _ (uint x)); [ | apply pi_uint_lt64 ].
        apply quot_le_self; [ apply pi_uint_nonneg | ].
        destruct Hbase as [Hb1 _]. lia. }
      (* re-anchor ["Hcont"] (still at the entry hart [CID0]) to the hart
         reached by the back-edge branch ([CIDc]) before recursing. *)
      assert (Hshiftc : b = false \/ pcur = zero_reg -> (CIDc : CPU) = (CID0 : CPU)) by wp_next_chain.
      iDestruct (wp_next_shift Hshiftc with "Hcont") as "Hcont".
      iApply (IH (S i) CIDc (mword_of_int (Z.quot (uint x) (uint (md !!! Regidx a1_idx)))) mb
                ltac:(lia)
                ltac:(rewrite (uint_moi_small _ (conj Hq0 Hq64)); exact Hq)
                ltac:(rewrite (Hbk a1_idx ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)); exact Hbase)
                Hb0 Hb3 Hb4
                ltac:(rewrite (Hbk a6_idx ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)); exact Ha6)
                with "Hcg Htext Hdig Hpc Hbuf").
      iIntros (CIDf Hsf mf i'') "%Hf Hcg Hpc Hbuf".
      destruct Hf as (Hf1 & Hf21 & Hf2 & Hf4 & Hf7 & Hfk).
      iSpecialize ("Hcont" $! CIDf with "[%]"); [wp_next_chain|].
      iApply ("Hcont" $! mf i'' with "[%] Hcg Hpc Hbuf").
      split; [exact Hf1 | ]. split; [exact Hf21 | ]. split; [exact Hf2 | ].
      split; [exact Hf4 | ]. split; [exact Hf7 | ].
      intros c N0 N2 N3 N4 N5 N7.
      rewrite (Hfk c N0 N2 N3 N4 N5 N7). exact (Hbk c N0 N2 N3 N4 N5 N7).
    - (* fuel S f', fall through: done *)
      iApply (wp_bgeu_fall_s_sconf (mword_of_int (KernelSyms.printint + 0x40)) (mword_of_int 8162 : mword 13)
                a1_idx a5_idx mb (K - 8)%nat b
                ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                ltac:(rgne; rgne; unfold zopz0zKzJ_u; rewrite Hb5 (Hbk a1_idx ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)); exact Hcmp)
                with "Hcg Hpc Hi40").
      iIntros (CIDc Hsc) "Hcg Hpc".
      assert (Hp44 : add_vec_int (mword_of_int (KernelSyms.printint + 0x40) : mword 64) 4 = mword_of_int (KernelSyms.printint + 0x44)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp44) in "Hpc".
      iSpecialize ("Hcont" $! CIDc with "[%]"); [wp_next_chain|].
      iApply ("Hcont" $! mb (S i) with "[%] Hcg Hpc Hbuf").
      split; [lia | ]. split; [lia | ]. split; [exact Hb2 | ]. split; [exact Hb4 | ].
      split; [ replace (S i - 1)%nat with i by lia; exact Hb7 | exact Hbk ].
  Qed.

  (* ================================================================== *)
  (*  THE PRINT LOOP (0x74 .. 0x7e): [while (--i >= 0) consputc(buf[i])] *)
  (*                                                                     *)
  (*  A DESCENDING byte cursor in s1, stopping when it meets the sentinel *)
  (*  [buf-1] the setup code computed in s2.  Induction on the cursor     *)
  (*  index; both registers are callee-saved, which is exactly why the    *)
  (*  loop can keep them across the consputc call.                        *)
  (*                                                                      *)
  (*  WHAT THE INDUCTION CARRIES ACROSS THE BACK-EDGE, now that the       *)
  (*  transmitter lives under [tx_lock] and is taken PER BYTE inside      *)
  (*  uartputc_sync: nothing that the loop has to reason about.  The      *)
  (*  trace claim [uart_sent_sub γd (bs ++ cs)] is PERSISTENT -- it is a  *)
  (*  sublist statement, sound even though another hart may interleave    *)
  (*  its own bytes between two of ours -- so the iteration statement     *)
  (*  merely names a longer list, it does not hand a resource on.  The    *)
  (*  one linear thing crossing the edge is [cpu_own], and it crosses     *)
  (*  UNCHANGED: consputc's acquire/release pair per byte leaves the      *)
  (*  interrupt level exactly as it found it, so the same [n eb p C b]    *)
  (*  comes back out.  It is [CpuId]-indexed, hence the [cpu_own_        *)
  (*  transport]s at the hart the branch/call actually lands on.          *)
  (* ================================================================== *)

  Hypothesis wp_consputc :
    forall `{CID0 : CpuId} (γl : gname) (γd : uart_names) (γv : disk_names) (m0 : regfile) (K : nat)
      (bs : list (bv 8)) (n : nat) (eb : bool) (C : iProp Σ) (b : bool) (pcur : mword 64) (lks : gset nat),
      wp_consputc_sconf_body γl γd γv m0 K bs n eb C b pcur lks.

  Lemma wp_printint_ploop (γl : gname) (γd : uart_names) (γv : disk_names) (K : nat)
      (buf : mword 64) (n : nat) (eb : bool) (C : iProp Σ) (b : bool) (pcur : mword 64) (lks : gset nat) :
    (24 <= K)%nat ->
    (Z.of_nat n + 1 < 2 ^ 31)%Z ->
    forall (j : nat) `(CID0 : CpuId) (bs : list (bv 8)) (mp : regfile),
    (j < 24)%nat ->
    mp !!! Regidx s1_idx = pa_add buf j ->
    mp !!! Regidx s2_idx = add_vec buf (mword_of_int (-1) : mword 64) ->
    locks_below lks (lock_rank "uart") ->
    sie_cap_gpr mp (K - 8)%nat b pcur -∗
    cpu_own n eb pcur C b lks -∗
    kernel_text -∗
    pc_is (mword_of_int (KernelSyms.printint + 0x74) : mword 64) -∗
    bytes_own (DfracOwn 1) buf 24 -∗
    panic_wp_any -∗
    dev_inv γd γv -∗ is_txlock γl γd -∗ uart_sent_sub γd bs -∗
    wp_next (CID0 := CID0) b pcur (fun (CID : CpuId) =>
      ∀ (mf : regfile) (cs : list (bv 8)),
      ⌜ forall c : mword 5, is_cs_idx c = true -> c <> s1_idx ->
          mf !!! Regidx c = mp !!! Regidx c ⌝ -∗
      sie_cap_gpr mf (K - 8)%nat b pcur -∗
      cpu_own n eb pcur C b lks -∗
      pc_is (mword_of_int (KernelSyms.printint + 0x82) : mword 64) -∗
      bytes_own (DfracOwn 1) buf 24 -∗
      uart_sent_sub γd (bs ++ cs) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HK Hn31.
    assert (HK16 : (consputc_stack <= K - 8)%nat) by (unfold consputc_stack; lia).
    assert (Hz0 : sign_extend' 64 (mword_of_int 0 : mword 12) = (mword_of_int 0 : mword 64))
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Hm1 : sign_extend' 64 (sign_extend' 12 (mword_of_int 63 : mword 6)) = (mword_of_int (-1) : mword 64))
      by (apply bv_eq; vm_compute; reflexivity).
    (* ONE [;]-chain for the body, so both induction cases run it and the two
       cases are left as the bullets below. Every step is single-goal: the
       loaded byte is put into the leaf's address form BEFORE the [iApply]
       (rather than framed in a bracket), which is what keeps it that way. *)
    induction j as [|j' IH]; intros CID0 bs mp Hj24 Hs1 Hs2 Hlkbelow;
      iIntros "Hcg Hcnt #Htext Hpc Hbuf #Hpanic #Hdev #Htxl #Hsent Hcont";
      iPoseProof (pii_74 with "Htext") as "Hi74";
      iPoseProof (pii_78 with "Htext") as "Hi78";
      iPoseProof (pii_7c with "Htext") as "Hi7c";
      iPoseProof (pii_7e with "Htext") as "Hi7e";
      iDestruct (bytes_own_acc (DfracOwn 1) buf 24 _ Hj24 with "Hbuf") as "[Hbj Hbcl]";
      iDestruct "Hbj" as (bj) "Hbj";
      assert (Hpa : add_vec (mp !!! Regidx s1_idx) (sign_extend' 64 (mword_of_int 0 : mword 12))
                    = pa_add buf _) by (rewrite Hs1 Hz0; apply kv_addv_zero);
      iEval (rewrite -Hpa) in "Hbj";
      (* +0x74 lbu a0,0(s1) : buf[i] *)
      iApply (wp_lbu_s_sconf (mword_of_int (KernelSyms.printint + 0x74)) a0_idx s1_idx (mword_of_int 0 : mword 12)
                mp (K - 8)%nat (bj : mword 8) b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi74 Hbj");
      iIntros (CIDl1 Hsl1) "Hcg Hpc Hbj";
      iEval (rewrite Hpa) in "Hbj";
      iDestruct ("Hbcl" with "Hbj") as "Hbuf";
      set (P1 := <[Regidx a0_idx := regval_into_reg (zero_extend' 64 (bj : mword 8))]> mp);
      assert (Hp78 : add_vec_int (mword_of_int (KernelSyms.printint + 0x74) : mword 64) 4 = mword_of_int (KernelSyms.printint + 0x78))
        by (apply bv_eq; vm_compute; reflexivity);
      iEval (rewrite Hp78) in "Hpc";
      (* +0x78 jal consputc *)
      iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.printint + 0x78)) ra_idx (mword_of_int 2096550 : mword 21)
                P1 (K - 8)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
                ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi78");
      iIntros (CIDj1 Hsj1) "Hcg Hpc";
      set (P2 := <[Regidx ra_idx := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.printint + 0x78) : mword 64) 4)]> P1);
      assert (Htgtc : add_vec (mword_of_int (KernelSyms.printint + 0x78) : mword 64) (sign_extend' 64 (mword_of_int 2096550 : mword 21)) = mword_of_int KernelSyms.consputc)
        by (apply bv_eq; vm_compute; reflexivity);
      iEval (rewrite Htgtc) in "Hpc";
      iDestruct (cpu_own_transport CID0 CIDj1 n eb pcur C b ltac:(wp_next_chain) with "Hcnt") as "Hcnt";
      iApply (wp_consputc (CID0 := CIDj1) γl γd γv P2 (K - 8)%nat bs n eb C b pcur lks HK16 Hn31 Hlkbelow
                with "Hcg Hcnt Htext Hpc Hpanic Hdev Htxl Hsent");
      iIntros (CIDcp Hscp mc cs) "Hcg Hcnt Hpc %Hcs #Hsent2";
      destruct Hcs as [Hcs Hra];
      assert (Hretc : ret_pc (P2 !!! Regidx ra_idx) = mword_of_int (KernelSyms.printint + 0x7c))
        by (rewrite /P2 upd_eq; unfold ret_pc; apply bv_eq; vm_compute; reflexivity);
      iEval (rewrite Hretc) in "Hpc";
      (* s1/s2 survive the call: both are callee-saved *)
      assert (Hmcs1 : mc !!! Regidx s1_idx = pa_add buf _)
        by (rewrite (callee_saved_lookup Hcs s1_idx ltac:(vm_compute; reflexivity));
            rewrite /P2 upd_ne; [| reg_neq]; rewrite /P1 upd_ne; [exact Hs1 | reg_neq]);
      assert (Hmcs2 : mc !!! Regidx s2_idx = add_vec buf (mword_of_int (-1) : mword 64))
        by (rewrite (callee_saved_lookup Hcs s2_idx ltac:(vm_compute; reflexivity));
            rewrite /P2 upd_ne; [| reg_neq]; rewrite /P1 upd_ne; [exact Hs2 | reg_neq]);
      assert (Hkeep1 : forall c : mword 5, is_cs_idx c = true -> c <> s1_idx ->
                mc !!! Regidx c = mp !!! Regidx c)
        by (intros c Hc N9;
            pose proof (is_cs_idx_true_neq ra_idx c ltac:(vm_compute; reflexivity) Hc) as N1;
            pose proof (is_cs_idx_true_neq a0_idx c ltac:(vm_compute; reflexivity) Hc) as N10;
            rewrite (callee_saved_lookup Hcs c Hc);
            rewrite /P2 upd_ne; [| congruence];
            rewrite /P1 upd_ne; [reflexivity | congruence]);
      (* +0x7c c.addi s1,s1,-1 *)
      iApply (wp_caddi_s_sconf (mword_of_int (KernelSyms.printint + 0x7c)) s1_idx (mword_of_int 63 : mword 6)
                mc (K - 8)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi7c");
      iIntros (CIDa1 Hsa1) "Hcg Hpc";
      iEval (rgne) in "Hcg";
      set (P3 := <[Regidx s1_idx := regval_into_reg
                     (add_vec (mc !!! Regidx s1_idx) (sign_extend' 64 (sign_extend' 12 (mword_of_int 63 : mword 6))))]> mc);
      assert (HP3s1 : P3 !!! Regidx s1_idx = add_vec (pa_add buf _) (mword_of_int (-1) : mword 64))
        by (rewrite /P3 upd_eq; unfold regval_into_reg; rewrite Hmcs1 Hm1; reflexivity);
      assert (HP3s2 : P3 !!! Regidx s2_idx = add_vec buf (mword_of_int (-1) : mword 64))
        by (rewrite /P3 upd_ne; [exact Hmcs2 | reg_neq]);
      assert (Hp7e : add_vec_int (mword_of_int (KernelSyms.printint + 0x7c) : mword 64) 2 = mword_of_int (KernelSyms.printint + 0x7e))
        by (apply bv_eq; vm_compute; reflexivity);
      iEval (rewrite Hp7e) in "Hpc";
      assert (Hcmp : neq_vec (P3 !!! Regidx s1_idx) (P3 !!! Regidx s2_idx) = negb (Nat.eqb _ 0))
        by (rewrite HP3s1 HP3s2; apply pa_add_neq_base;
            change (2^64) with 18446744073709551616; lia).
      all: try lkbelow.
    - (* ---- j = 0: the cursor met the sentinel, fall through ---- *)
      iApply (wp_bne_fall_s_sconf (mword_of_int (KernelSyms.printint + 0x7e)) (mword_of_int 8182 : mword 13)
                s2_idx s1_idx P3 (K - 8)%nat b
                ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                ltac:(rgne; rgne; rewrite Hcmp; reflexivity)
                with "Hcg Hpc Hi7e").
      iIntros (CIDbn Hsbn) "Hcg Hpc".
      assert (Hp82 : add_vec_int (mword_of_int (KernelSyms.printint + 0x7e) : mword 64) 4 = mword_of_int (KernelSyms.printint + 0x82))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp82) in "Hpc".
      iDestruct (cpu_own_transport CIDcp CIDbn n eb pcur C b ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
      iSpecialize ("Hcont" $! CIDbn with "[%]"); [wp_next_chain|].
      iApply ("Hcont" $! P3 cs with "[%] Hcg Hcnt Hpc Hbuf Hsent2").
      intros c Hc N9. rewrite /P3 upd_ne; [| congruence]. exact (Hkeep1 c Hc N9).
    - (* ---- j = S j': one more character ---- *)
      iApply (wp_bne_taken_s_sconf (mword_of_int (KernelSyms.printint + 0x7e)) (mword_of_int 8182 : mword 13)
                s2_idx s1_idx P3 (K - 8)%nat b
                ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                ltac:(rgne; rgne; rewrite Hcmp; reflexivity)
                ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi7e").
      iApply bi.later_intro. iIntros (CIDbn Hsbn) "Hcg Hpc".
      assert (Htgtb : add_vec (mword_of_int (KernelSyms.printint + 0x7e) : mword 64) (sign_extend' 64 (mword_of_int 8182 : mword 13)) = mword_of_int (KernelSyms.printint + 0x74))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Htgtb) in "Hpc".
      assert (Hshiftbn : b = false \/ pcur = zero_reg -> (CIDbn : CPU) = (CID0 : CPU)) by wp_next_chain.
      iDestruct (wp_next_shift Hshiftbn with "Hcont") as "Hcont".
      iDestruct (cpu_own_transport CIDcp CIDbn n eb pcur C b ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
      iApply (IH CIDbn (bs ++ cs)%list P3 ltac:(lia)
                ltac:(rewrite HP3s1; apply pa_add_back1; reflexivity)
                HP3s2 Hlkbelow
                with "Hcg Hcnt Htext Hpc Hbuf Hpanic Hdev Htxl Hsent2").
      iIntros (CIDf Hsf mf cs2) "%Hk2 Hcg Hcnt Hpc Hbuf #Hsent3".
      iEval (rewrite -app_assoc) in "Hsent3".
      iSpecialize ("Hcont" $! CIDf with "[%]"); [wp_next_chain|].
      iApply ("Hcont" $! mf (cs ++ cs2)%list with "[%] Hcg Hcnt Hpc Hbuf Hsent3").
      intros c Hc N9.
      rewrite (Hk2 c Hc N9). rewrite /P3 upd_ne; [| congruence]. exact (Hkeep1 c Hc N9).
  Qed.

  (* ================================================================== *)
  (*  THE TAIL (0x5c .. return): print-loop setup, the loop, the         *)
  (*  lazily-saved s1, and the epilogue.                                 *)
  (* ================================================================== *)

  Lemma wp_printint_tail `{CID0 : CpuId} (γl : gname) (γd : uart_names) (γv : disk_names)
      (m mt : regfile) (K nd : nat) (bs : list (bv 8))
      (n : nat) (eb : bool) (C : iProp Σ) (b : bool) (pcur : mword 64) (lks : gset nat) :
    let sp0 := m !!! Regidx csp_rs1 in
    let spd := add_vec sp0 (sign_extend' 64 (caddi16sp_imm (mword_of_int 60 : mword 6))) in
    let buf := pa_stk sp0 7 in
    (24 <= K)%nat ->
    (Z.of_nat n + 1 < 2 ^ 31)%Z ->
    (1 <= nd)%nat -> (nd <= 22)%nat ->
    mt !!! Regidx a4_idx = mword_of_int (Z.of_nat nd) ->
    mt !!! Regidx csp_rs1 = spd ->
    mt !!! Regidx s2_idx = buf ->
    (forall c : mword 5, is_cs_idx c = true -> c <> csp_rs1 -> c <> s0_idx -> c <> s2_idx ->
       mt !!! Regidx c = m !!! Regidx c) ->
    is_aligned_paddr (Physaddr (pa_stk sp0 7)) 8 = true ->
    is_aligned_paddr (Physaddr (pa_stk sp0 6)) 8 = true ->
    is_aligned_paddr (Physaddr (pa_stk sp0 5)) 8 = true ->
    locks_below lks (lock_rank "uart") ->
    sie_cap_gpr mt (K - 8)%nat b pcur -∗
    cpu_own n eb pcur C b lks -∗
    kernel_text -∗
    pc_is (mword_of_int (KernelSyms.printint + 0x5c) : mword 64) -∗
    bytes_own (DfracOwn 1) buf 24 -∗
    (pa_stk sp0 1) ↦₈ (m !!! Regidx ra_idx) -∗
    (pa_stk sp0 2) ↦₈ (m !!! Regidx s0_idx) -∗
    (∃ v : mword 64, (pa_stk sp0 3) ↦₈ v) -∗
    (pa_stk sp0 4) ↦₈ (m !!! Regidx s2_idx) -∗
    (∃ v : mword 64, (pa_stk sp0 8) ↦₈ v) -∗
    panic_wp_any -∗
    dev_inv γd γv -∗ is_txlock γl γd -∗ uart_sent_sub γd bs -∗
    wp_next (CID0 := CID0) b pcur (fun (CID : CpuId) =>
      ∀ (mf : regfile) (cs : list (bv 8)),
      sie_cap_gpr mf K b pcur -∗
      cpu_own n eb pcur C b lks -∗
      pc_is (ret_pc (m !!! Regidx ra_idx)) -∗
      ⌜ callee_saved m mf /\ mf !!! Regidx ra_idx = m !!! Regidx ra_idx ⌝ -∗
      uart_sent_sub γd (bs ++ cs) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros sp0 spd buf HK Hn31 Hn1 Hn22 Ha4 Hsp Hs2 Hkept Hal7 Hal6 Hal5 Hlkbelow.
    iIntros "Hcg Hcnt #Htext Hpc Hbuf Hc1 Hc2 Hc3 Hc4 Hc8 #Hpanic #Hdev #Htxl #Hsent Hcont".
    iPoseProof (pii_5c with "Htext") as "Hi5c".
    iPoseProof (pii_60 with "Htext") as "Hi60".
    iPoseProof (pii_62 with "Htext") as "Hi62".
    iPoseProof (pii_64 with "Htext") as "Hi64".
    iPoseProof (pii_68 with "Htext") as "Hi68".
    iPoseProof (pii_6a with "Htext") as "Hi6a".
    iPoseProof (pii_6c with "Htext") as "Hi6c".
    iPoseProof (pii_6e with "Htext") as "Hi6e".
    iPoseProof (pii_70 with "Htext") as "Hi70".
    iPoseProof (pii_82 with "Htext") as "Hi82".
    assert (Hn63 : 0 <= Z.of_nat nd < 2^63) by (change (2^63) with 9223372036854775808; lia).
    assert (Hpush : spd = pa_stk sp0 8).
    { unfold spd, pa_stk, add_vec_int. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb3 : add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000"))) = pa_stk sp0 3).
    { rewrite Hpush. unfold pa_stk, add_vec_int. rewrite pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    (* +0x5c blez a4 : NOT taken -- the loop always runs at least once *)
    iApply (wp_bge_x0_fall_s_sconf (mword_of_int (KernelSyms.printint + 0x5c)) (mword_of_int 40 : mword 13)
              a4_idx mt (K - 8)%nat b ltac:(vm_compute; discriminate)
              ltac:(rgne; unfold zopz0zKzJ_s; rewrite Ha4 (sint_moi_small _ Hn63);
                    change (sint zero_reg) with 0; rewrite Z.geb_leb; apply Z.leb_gt; lia)
              with "Hcg Hpc Hi5c").
    iIntros (CIDt1 Hst1) "Hcg Hpc".
    assert (Hp60 : add_vec_int (mword_of_int (KernelSyms.printint + 0x5c) : mword 64) 4 = mword_of_int (KernelSyms.printint + 0x60)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp60) in "Hpc".
    (* +0x60 sd s1,40(sp) : the LAZY save, only on this path *)
    iDestruct "Hc3" as (v3) "Hc3".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.printint + 0x60)) (mword_of_int 5 : mword 6) s1_idx
              mt (K - 8)%nat v3 b with "Hcg Hpc Hi60 [Hc3]").
    { iEval (rewrite Hsp Hb3). iExact "Hc3". }
    iIntros (CIDsv Hssv) "Hcg Hpc Hc3". iEval (rewrite Hsp Hb3) in "Hc3".
    iEval (rgne) in "Hc3".
    iEval (rewrite (Hkept s1_idx ltac:(vm_compute; reflexivity) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq))) in "Hc3".
    assert (Hp62 : add_vec_int (mword_of_int (KernelSyms.printint + 0x60) : mword 64) 2 = mword_of_int (KernelSyms.printint + 0x62)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp62) in "Hpc".
    (* +0x62 c.addiw a4,a4,-1 *)
    iApply (wp_caddiw_s_sconf (mword_of_int (KernelSyms.printint + 0x62)) a4_idx (mword_of_int 63 : mword 6)
              mt (K - 8)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi62").
    iIntros (CIDaw Hsaw) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (T1 := <[Regidx a4_idx := regval_into_reg (sign_extend' 64 (subrange_vec_dec
                 (add_vec (mt !!! Regidx a4_idx) (sign_extend' 64 (sign_extend' 12 (mword_of_int 63 : mword 6)))) 31 0))]> mt).
    assert (HT1a4 : T1 !!! Regidx a4_idx = mword_of_int (Z.of_nat (nd - 1))).
    { rewrite /T1 upd_eq. unfold regval_into_reg. rewrite Ha4.
      rewrite (addiw_lit (Z.of_nat nd) (-1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 63 : mword 6)))
                 ltac:(apply bv_eq; vm_compute; reflexivity)
                 ltac:(change (2^31) with 2147483648; lia)).
      f_equal. lia. }
    assert (HT1s2 : T1 !!! Regidx s2_idx = buf) by (rewrite /T1 upd_ne; [exact Hs2 | reg_neq]).
    assert (Hp64 : add_vec_int (mword_of_int (KernelSyms.printint + 0x62) : mword 64) 2 = mword_of_int (KernelSyms.printint + 0x64)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp64) in "Hpc".
    (* +0x64 add s1,s2,a4 : the cursor's start, buf + (nd-1) *)
    iApply (wp_add_s_sconf (mword_of_int (KernelSyms.printint + 0x64)) s1_idx s2_idx a4_idx
              (pa_add buf (nd - 1)) T1 (K - 8)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(rgne; rgne; rewrite HT1s2 HT1a4 add_vec64_comm add_vec_pa_add;
                    f_equal; rewrite (uint_moi_small (Z.of_nat (nd-1)) ltac:(change (2^64) with 18446744073709551616; lia));
                    apply Nat2Z.id)
              with "Hcg Hpc Hi64").
    iIntros (CIDad Hsad) "Hcg Hpc".
    set (T2 := <[Regidx s1_idx := regval_into_reg (pa_add buf (nd - 1))]> T1).
    assert (HT2s2 : T2 !!! Regidx s2_idx = buf) by (rewrite /T2 upd_ne; [exact HT1s2 | reg_neq]).
    assert (HT2a4 : T2 !!! Regidx a4_idx = mword_of_int (Z.of_nat (nd - 1))) by (rewrite /T2 upd_ne; [exact HT1a4 | reg_neq]).
    assert (Hp68 : add_vec_int (mword_of_int (KernelSyms.printint + 0x64) : mword 64) 4 = mword_of_int (KernelSyms.printint + 0x68)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp68) in "Hpc".
    (* +0x68 c.addi s2,s2,-1 : the sentinel *)
    iApply (wp_caddi_s_sconf (mword_of_int (KernelSyms.printint + 0x68)) s2_idx (mword_of_int 63 : mword 6)
              T2 (K - 8)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi68").
    iIntros (CIDci Hsci) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (T3 := <[Regidx s2_idx := regval_into_reg (add_vec (T2 !!! Regidx s2_idx) (sign_extend' 64 (sign_extend' 12 (mword_of_int 63 : mword 6))))]> T2).
    assert (Hm1 : sign_extend' 64 (sign_extend' 12 (mword_of_int 63 : mword 6)) = (mword_of_int (-1) : mword 64))
      by (apply bv_eq; vm_compute; reflexivity).
    assert (HT3s2 : T3 !!! Regidx s2_idx = add_vec buf (mword_of_int (-1) : mword 64))
      by (rewrite /T3 upd_eq; unfold regval_into_reg; rewrite HT2s2 Hm1; reflexivity).
    assert (HT3a4 : T3 !!! Regidx a4_idx = mword_of_int (Z.of_nat (nd - 1))) by (rewrite /T3 upd_ne; [exact HT2a4 | reg_neq]).
    assert (Hp6a : add_vec_int (mword_of_int (KernelSyms.printint + 0x68) : mword 64) 2 = mword_of_int (KernelSyms.printint + 0x6a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp6a) in "Hpc".
    (* +0x6a c.add s2,s2,a4 *)
    iApply (wp_cadd_s_sconf (mword_of_int (KernelSyms.printint + 0x6a)) s2_idx a4_idx T3 (K - 8)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi6a").
    iIntros (CIDca Hsca) "Hcg Hpc".
    iEval (rgne; rgne) in "Hcg".
    set (T4 := <[Regidx s2_idx := regval_into_reg (add_vec (T3 !!! Regidx s2_idx) (T3 !!! Regidx a4_idx))]> T3).
    assert (HT4a4 : T4 !!! Regidx a4_idx = mword_of_int (Z.of_nat (nd - 1))) by (rewrite /T4 upd_ne; [exact HT3a4 | reg_neq]).
    assert (Hp6c : add_vec_int (mword_of_int (KernelSyms.printint + 0x6a) : mword 64) 2 = mword_of_int (KernelSyms.printint + 0x6c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp6c) in "Hpc".
    (* +0x6c/0x6e slli/srli 32 : the (unsigned int) round-trip, an identity here *)
    iApply (wp_cslli_s_sconf (mword_of_int (KernelSyms.printint + 0x6c)) (Regidx a4_idx) a4_idx (mword_of_int 32 : mword 6)
              T4 (K - 8)%nat b eq_refl ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi6c").
    iIntros (CIDsl Hssl) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (T5 := <[Regidx a4_idx := regval_into_reg (shift_bits_left (T4 !!! Regidx a4_idx) (subrange_vec_dec (mword_of_int 32 : mword 6) (Z.sub log2_xlen 1) 0))]> T4).
    assert (Hp6e : add_vec_int (mword_of_int (KernelSyms.printint + 0x6c) : mword 64) 2 = mword_of_int (KernelSyms.printint + 0x6e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp6e) in "Hpc".
    iApply (wp_csrli_s_sconf (mword_of_int (KernelSyms.printint + 0x6e)) (Cregidx (mword_of_int 6)) a4_idx (mword_of_int 32 : mword 6)
              T5 (K - 8)%nat b ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi6e").
    iIntros (CIDsr Hssr) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (T6 := <[Regidx a4_idx := regval_into_reg (shift_bits_right (T5 !!! Regidx a4_idx) (subrange_vec_dec (mword_of_int 32 : mword 6) (Z.sub log2_xlen 1) 0))]> T5).
    assert (HT6a4 : T6 !!! Regidx a4_idx = mword_of_int (Z.of_nat (nd - 1))).
    { rewrite /T6 upd_eq. unfold regval_into_reg. rewrite /T5 upd_eq. unfold regval_into_reg.
      rewrite HT4a4. apply slli32_srli32.
      rewrite moi64_mod.
      rewrite (Z.mod_small (Z.of_nat (nd-1)) 18446744073709551616 ltac:(lia)).
      change (2^32) with 4294967296. lia. }
    assert (HT6s2 : T6 !!! Regidx s2_idx = add_vec (add_vec buf (mword_of_int (-1) : mword 64)) (mword_of_int (Z.of_nat (nd - 1)))).
    { rewrite /T6 upd_ne; [| reg_neq]. rewrite /T5 upd_ne; [| reg_neq].
      rewrite /T4 upd_eq. unfold regval_into_reg. rewrite HT3s2 HT3a4. reflexivity. }
    assert (Hp70 : add_vec_int (mword_of_int (KernelSyms.printint + 0x6e) : mword 64) 2 = mword_of_int (KernelSyms.printint + 0x70)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp70) in "Hpc".
    (* +0x70 sub s2,s2,a4 : back to the sentinel *)
    iApply (wp_sub_s_sconf (mword_of_int (KernelSyms.printint + 0x70)) s2_idx s2_idx a4_idx
              (add_vec buf (mword_of_int (-1) : mword 64)) T6 (K - 8)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(rgne; rgne; rewrite HT6s2 HT6a4; apply add_sub_cancel)
              with "Hcg Hpc Hi70").
    iIntros (CIDsu Hssu) "Hcg Hpc".
    set (T7 := <[Regidx s2_idx := regval_into_reg (add_vec buf (mword_of_int (-1) : mword 64))]> T6).
    assert (HT7s1 : T7 !!! Regidx s1_idx = pa_add buf (nd - 1)).
    { rewrite /T7 upd_ne; [| reg_neq]. rewrite /T6 upd_ne; [| reg_neq].
      rewrite /T5 upd_ne; [| reg_neq]. rewrite /T4 upd_ne; [| reg_neq].
      rewrite /T3 upd_ne; [| reg_neq]. rewrite /T2 upd_eq. reflexivity. }
    assert (HT7s2 : T7 !!! Regidx s2_idx = add_vec buf (mword_of_int (-1) : mword 64))
      by (rewrite /T7 upd_eq; reflexivity).
    assert (Hp74 : add_vec_int (mword_of_int (KernelSyms.printint + 0x70) : mword 64) 4 = mword_of_int (KernelSyms.printint + 0x74)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp74) in "Hpc".
    (* ---- the print loop -- [Hcont] is not consumed here: it is FRAMED
       (via [-]) into the continuation goal ploop hands back, and reused at
       the very end once the epilogue has run. *)
    iDestruct (cpu_own_transport CID0 CIDsu n eb pcur C b ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    iApply (wp_printint_ploop γl γd γv K buf n eb C b pcur lks HK Hn31 (nd - 1)%nat CIDsu bs T7
              ltac:(lia) HT7s1 HT7s2 Hlkbelow
              with "Hcg Hcnt Htext Hpc Hbuf Hpanic Hdev Htxl Hsent").
    iIntros (CIDpl Hspl mf cs) "%Hk Hcg Hcnt Hpc Hbuf #Hsent2".
    (* +0x82 ld s1,40(sp) : undo the lazy save *)
    assert (Hmfsp : mf !!! Regidx csp_rs1 = spd).
    { rewrite (Hk csp_rs1 ltac:(vm_compute; reflexivity) ltac:(reg_neq)).
      rewrite /T7 upd_ne; [| reg_neq]. rewrite /T6 upd_ne; [| reg_neq].
      rewrite /T5 upd_ne; [| reg_neq]. rewrite /T4 upd_ne; [| reg_neq].
      rewrite /T3 upd_ne; [| reg_neq]. rewrite /T2 upd_ne; [| reg_neq].
      rewrite /T1 upd_ne; [exact Hsp | reg_neq]. }
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.printint + 0x82)) (mword_of_int 5 : mword 6) s1_idx
              mf (K - 8)%nat (m !!! Regidx s1_idx) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi82 [Hc3]").
    { iEval (rewrite Hmfsp Hb3). iExact "Hc3". }
    iIntros (CIDld Hsld) "Hcg Hpc Hc3". iEval (rewrite Hmfsp Hb3) in "Hc3".
    set (R1 := <[Regidx s1_idx := regval_into_reg (m !!! Regidx s1_idx)]> mf).
    assert (Hp84 : add_vec_int (mword_of_int (KernelSyms.printint + 0x82) : mword 64) 2 = mword_of_int (KernelSyms.printint + 0x84)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp84) in "Hpc".
    (* ---- rebuild the three byte slots and run the epilogue ---- *)
    iDestruct (bytes_own_slots3 sp0 7 ltac:(lia) Hal7 Hal6 Hal5 with "Hbuf") as (w7 w6 w5) "(Hs7 & Hs6 & Hs5)".
    iApply (wp_printint_epi (CID0 := CIDld) m R1 K b pcur ltac:(lia)
              ltac:(rewrite /R1 upd_ne; [exact Hmfsp | reg_neq])
              ltac:(intros c Hc Nsp N8 N18;
                    pose proof (is_cs_idx_true_neq a4_idx c ltac:(vm_compute; reflexivity) Hc) as N14;
                    destruct (decide (c = s1_idx)) as [-> | N9];
                    [ rewrite /R1 upd_eq; reflexivity
                    | rewrite /R1 upd_ne; [| congruence];
                      rewrite (Hk c Hc N9);
                      rewrite /T7 upd_ne; [| congruence];
                      rewrite /T6 upd_ne; [| congruence];
                      rewrite /T5 upd_ne; [| congruence];
                      rewrite /T4 upd_ne; [| congruence];
                      rewrite /T3 upd_ne; [| congruence];
                      rewrite /T2 upd_ne; [| congruence];
                      rewrite /T1 upd_ne; [| congruence];
                      exact (Hkept c Hc Nsp N8 N18) ])
              with "Hcg Htext Hpc Hc1 Hc2 [Hc3] Hc4 [Hs5] [Hs6] [Hs7] Hc8").
    { iExists (m !!! Regidx s1_idx). iExact "Hc3". }
    { iExists w5. iExact "Hs5". }
    { iExists w6. iExact "Hs6". }
    { iExists w7. iExact "Hs7". }
    iIntros (CIDfin Hsfin mfin) "Hcg Hpc %Hfin".
    iDestruct (cpu_own_transport CIDpl CIDfin n eb pcur C b ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    iSpecialize ("Hcont" $! CIDfin with "[%]"); [wp_next_chain|].
    iApply ("Hcont" $! mfin cs with "Hcg Hcnt Hpc [%] Hsent2").
    exact Hfin.
  Qed.

  (* ================================================================== *)
  (*  THE MAIN BODY (0x12 .. 0x58): buffer setup, the digit loop, and    *)
  (*  the optional '-' -- entered from all THREE sign paths, which is    *)
  (*  why it takes the map at 0x12 abstractly.                           *)
  (* ================================================================== *)

  Lemma wp_printint_main `{CID0 : CpuId} (γl : gname) (γd : uart_names) (γv : disk_names)
      (m mq : regfile) (K : nat) (x : mword 64) (bs : list (bv 8))
      (n : nat) (eb : bool) (C : iProp Σ) (b : bool) (pcur : mword 64) (lks : gset nat) :
    let sp0 := m !!! Regidx csp_rs1 in
    let spd := add_vec sp0 (sign_extend' 64 (caddi16sp_imm (mword_of_int 60 : mword 6))) in
    let buf := pa_stk sp0 7 in
    (24 <= K)%nat ->
    (Z.of_nat n + 1 < 2 ^ 31)%Z ->
    10 <= uint (mq !!! Regidx a1_idx) <= 16 ->
    mq !!! Regidx a0_idx = x ->
    mq !!! Regidx csp_rs1 = spd ->
    mq !!! Regidx s0_idx = sp0 ->
    (forall c : mword 5, is_cs_idx c = true -> c <> csp_rs1 -> c <> s0_idx -> c <> s2_idx ->
       mq !!! Regidx c = m !!! Regidx c) ->
    is_aligned_paddr (Physaddr (pa_stk sp0 7)) 8 = true ->
    is_aligned_paddr (Physaddr (pa_stk sp0 6)) 8 = true ->
    is_aligned_paddr (Physaddr (pa_stk sp0 5)) 8 = true ->
    locks_below lks (lock_rank "uart") ->
    sie_cap_gpr mq (K - 8)%nat b pcur -∗
    cpu_own n eb pcur C b lks -∗
    kernel_text -∗
    digits_tbl (mword_of_int KernelSyms.digits) -∗
    pc_is (mword_of_int (KernelSyms.printint + 0x12) : mword 64) -∗
    bytes_own (DfracOwn 1) buf 24 -∗
    (pa_stk sp0 1) ↦₈ (m !!! Regidx ra_idx) -∗
    (pa_stk sp0 2) ↦₈ (m !!! Regidx s0_idx) -∗
    (∃ v : mword 64, (pa_stk sp0 3) ↦₈ v) -∗
    (pa_stk sp0 4) ↦₈ (m !!! Regidx s2_idx) -∗
    (∃ v : mword 64, (pa_stk sp0 8) ↦₈ v) -∗
    panic_wp_any -∗
    dev_inv γd γv -∗ is_txlock γl γd -∗ uart_sent_sub γd bs -∗
    wp_next (CID0 := CID0) b pcur (fun (CID : CpuId) =>
      ∀ (mf : regfile) (cs : list (bv 8)),
      sie_cap_gpr mf K b pcur -∗
      cpu_own n eb pcur C b lks -∗
      pc_is (ret_pc (m !!! Regidx ra_idx)) -∗
      ⌜ callee_saved m mf /\ mf !!! Regidx ra_idx = m !!! Regidx ra_idx ⌝ -∗
      uart_sent_sub γd (bs ++ cs) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros sp0 spd buf HK Hn31 Hbase Ha0 Hsp Hs0 Hkept Hal7 Hal6 Hal5 Hlkbelow.
    iIntros "Hcg Hcnt #Htext #Hdig Hpc Hbuf Hc1 Hc2 Hc3 Hc4 Hc8 #Hpanic #Hdev #Htxl #Hsent Hcont".
    iPoseProof (pii_12 with "Htext") as "Hi12".
    iPoseProof (pii_16 with "Htext") as "Hi16".
    iPoseProof (pii_18 with "Htext") as "Hi18".
    iPoseProof (pii_1a with "Htext") as "Hi1a".
    iPoseProof (pii_1e with "Htext") as "Hi1e".
    iPoseProof (pii_44 with "Htext") as "Hi44".
    iPoseProof (pii_48 with "Htext") as "Hi48".
    iPoseProof (pii_4c with "Htext") as "Hi4c".
    iPoseProof (pii_50 with "Htext") as "Hi50".
    iPoseProof (pii_54 with "Htext") as "Hi54".
    iPoseProof (pii_58 with "Htext") as "Hi58".
    (* +0x12 addi s2,s0,-56 : s2 := buf *)
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.printint + 0x12)) s2_idx s0_idx (mword_of_int 4040 : mword 12)
              mq (K - 8)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi12").
    iIntros (CIDp1 Hsp1) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (Q1 := <[Regidx s2_idx := regval_into_reg (add_vec (mq !!! Regidx s0_idx) (sign_extend' 64 (mword_of_int 4040 : mword 12)))]> mq).
    assert (HQ1s2 : Q1 !!! Regidx s2_idx = buf).
    { rewrite /Q1 upd_eq. unfold regval_into_reg. rewrite Hs0.
      unfold buf, pa_stk, add_vec_int. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hp16 : add_vec_int (mword_of_int (KernelSyms.printint + 0x12) : mword 64) 4 = mword_of_int (KernelSyms.printint + 0x16)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp16) in "Hpc".
    (* +0x16 c.mv a3,s2 : the write cursor *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.printint + 0x16)) a3_idx s2_idx Q1 (K - 8)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi16").
    iIntros (CIDp2 Hsp2) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (Q2 := <[Regidx a3_idx := regval_into_reg (add_vec zero_reg (Q1 !!! Regidx s2_idx))]> Q1).
    assert (HQ2a3 : Q2 !!! Regidx a3_idx = pa_add buf 0).
    { rewrite /Q2 upd_eq. unfold regval_into_reg. rewrite HQ1s2 add_vec_zero_l pa_add_0. reflexivity. }
    assert (Hp18 : add_vec_int (mword_of_int (KernelSyms.printint + 0x16) : mword 64) 2 = mword_of_int (KernelSyms.printint + 0x18)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp18) in "Hpc".
    (* +0x18 c.li a4,0 : i := 0 *)
    iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.printint + 0x18)) a4_idx (mword_of_int 0 : mword 6)
              (mword_of_int 0 : mword 64) Q2 (K - 8)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc Hi18").
    iIntros (CIDp3 Hsp3) "Hcg Hpc".
    set (Q3 := <[Regidx a4_idx := regval_into_reg (mword_of_int 0 : mword 64)]> Q2).
    assert (Hp1a : add_vec_int (mword_of_int (KernelSyms.printint + 0x18) : mword 64) 2 = mword_of_int (KernelSyms.printint + 0x1a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp1a) in "Hpc".
    (* +0x1a/0x1e auipc/addi a6 : &digits *)
    iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.printint + 0x1a)) a6_idx (mword_of_int 7 : mword 20)
              Q3 (K - 8)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi1a").
    iIntros (CIDp4 Hsp4) "Hcg Hpc".
    set (Q4 := <[Regidx a6_idx := regval_into_reg (add_vec (mword_of_int (KernelSyms.printint + 0x1a) : mword 64) (auipc_off (mword_of_int 7 : mword 20)))]> Q3).
    assert (Hp1e : add_vec_int (mword_of_int (KernelSyms.printint + 0x1a) : mword 64) 4 = mword_of_int (KernelSyms.printint + 0x1e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp1e) in "Hpc".
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.printint + 0x1e)) a6_idx a6_idx (mword_of_int 682 : mword 12)
              Q4 (K - 8)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi1e").
    iIntros (CIDp5 Hsp5) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (Q5 := <[Regidx a6_idx := regval_into_reg (add_vec (Q4 !!! Regidx a6_idx) (sign_extend' 64 (mword_of_int 682 : mword 12)))]> Q4).
    assert (HQ5a6 : Q5 !!! Regidx a6_idx = (mword_of_int KernelSyms.digits : mword 64)).
    { rewrite /Q5 upd_eq. unfold regval_into_reg. rewrite /Q4 upd_eq.
      apply bv_eq; vm_compute; reflexivity. }
    assert (HQ5a0 : Q5 !!! Regidx a0_idx = x).
    { rewrite /Q5 upd_ne; [| reg_neq]. rewrite /Q4 upd_ne; [| reg_neq].
      rewrite /Q3 upd_ne; [| reg_neq]. rewrite /Q2 upd_ne; [| reg_neq].
      rewrite /Q1 upd_ne; [exact Ha0 | reg_neq]. }
    assert (HQ5a1 : Q5 !!! Regidx a1_idx = mq !!! Regidx a1_idx).
    { rewrite /Q5 upd_ne; [| reg_neq]. rewrite /Q4 upd_ne; [| reg_neq].
      rewrite /Q3 upd_ne; [| reg_neq]. rewrite /Q2 upd_ne; [| reg_neq].
      rewrite /Q1 upd_ne; [reflexivity | reg_neq]. }
    assert (HQ5a3 : Q5 !!! Regidx a3_idx = pa_add buf 0).
    { rewrite /Q5 upd_ne; [| reg_neq]. rewrite /Q4 upd_ne; [| reg_neq].
      rewrite /Q3 upd_ne; [| reg_neq]. exact HQ2a3. }
    assert (HQ5a4 : Q5 !!! Regidx a4_idx = mword_of_int (Z.of_nat 0)).
    { rewrite /Q5 upd_ne; [| reg_neq]. rewrite /Q4 upd_ne; [| reg_neq].
      rewrite /Q3 upd_eq. reflexivity. }
    assert (Hp22 : add_vec_int (mword_of_int (KernelSyms.printint + 0x1e) : mword 64) 4 = mword_of_int (KernelSyms.printint + 0x22)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp22) in "Hpc".
    (* ---- the digit loop, twenty digits of fuel ---- *)
    iApply (wp_printint_digits K buf (mword_of_int KernelSyms.digits) b pcur 20%nat 0%nat CIDp5 x Q5
              ltac:(lia) ltac:(apply uint_lt_1020)
              ltac:(rewrite HQ5a1; exact Hbase) HQ5a0 HQ5a3 HQ5a4 HQ5a6
              with "Hcg Htext Hdig Hpc Hbuf").
    iIntros (CIDdig Hsdig mf i') "%Hlp Hcg Hpc Hbuf".
    destruct Hlp as (Hi1 & Hi21 & Hf2 & Hf4 & Hf7 & Hfk).
    (* the callee-saved registers, and s2/sp, survive the loop *)
    assert (Hkept5 : forall c : mword 5, is_cs_idx c = true -> mf !!! Regidx c = Q5 !!! Regidx c).
    { intros c Hc.
      pose proof (is_cs_idx_true_neq a0_idx c ltac:(vm_compute; reflexivity) Hc) as N0.
      pose proof (is_cs_idx_true_neq a2_idx c ltac:(vm_compute; reflexivity) Hc) as N2.
      pose proof (is_cs_idx_true_neq a3_idx c ltac:(vm_compute; reflexivity) Hc) as N3.
      pose proof (is_cs_idx_true_neq a4_idx c ltac:(vm_compute; reflexivity) Hc) as N4.
      pose proof (is_cs_idx_true_neq a5_idx c ltac:(vm_compute; reflexivity) Hc) as N5.
      pose proof (is_cs_idx_true_neq a7_idx c ltac:(vm_compute; reflexivity) Hc) as N7.
      apply Hfk; congruence. }
    assert (HQ5cs : forall c : mword 5, is_cs_idx c = true -> c <> csp_rs1 -> c <> s0_idx -> c <> s2_idx ->
              Q5 !!! Regidx c = m !!! Regidx c).
    { intros c Hc Nsp N8 N18.
      pose proof (is_cs_idx_true_neq a3_idx c ltac:(vm_compute; reflexivity) Hc) as N3.
      pose proof (is_cs_idx_true_neq a4_idx c ltac:(vm_compute; reflexivity) Hc) as N4.
      pose proof (is_cs_idx_true_neq a6_idx c ltac:(vm_compute; reflexivity) Hc) as N6.
      rewrite /Q5 upd_ne; [| congruence].
      rewrite /Q4 upd_ne; [| congruence].
      rewrite /Q3 upd_ne; [| congruence].
      rewrite /Q2 upd_ne; [| congruence].
      rewrite /Q1 upd_ne; [ exact (Hkept c Hc Nsp N8 N18) | congruence ]. }
    assert (Hmfsp : mf !!! Regidx csp_rs1 = spd).
    { rewrite (Hkept5 csp_rs1 ltac:(vm_compute; reflexivity)).
      rewrite /Q5 upd_ne; [| reg_neq]. rewrite /Q4 upd_ne; [| reg_neq].
      rewrite /Q3 upd_ne; [| reg_neq]. rewrite /Q2 upd_ne; [| reg_neq].
      rewrite /Q1 upd_ne; [exact Hsp | reg_neq]. }
    assert (Hmfs2 : mf !!! Regidx s2_idx = buf).
    { rewrite (Hkept5 s2_idx ltac:(vm_compute; reflexivity)).
      rewrite /Q5 upd_ne; [| reg_neq]. rewrite /Q4 upd_ne; [| reg_neq].
      rewrite /Q3 upd_ne; [| reg_neq]. rewrite /Q2 upd_ne; [| reg_neq]. exact HQ1s2. }
    assert (Hmfs0 : mf !!! Regidx s0_idx = sp0).
    { rewrite (Hkept5 s0_idx ltac:(vm_compute; reflexivity)).
      rewrite /Q5 upd_ne; [| reg_neq]. rewrite /Q4 upd_ne; [| reg_neq].
      rewrite /Q3 upd_ne; [| reg_neq]. rewrite /Q2 upd_ne; [| reg_neq].
      rewrite /Q1 upd_ne; [exact Hs0 | reg_neq]. }
    assert (Hmfcs : forall c : mword 5, is_cs_idx c = true -> c <> csp_rs1 -> c <> s0_idx -> c <> s2_idx ->
              mf !!! Regidx c = m !!! Regidx c).
    { intros c Hc Nsp N8 N18. rewrite (Hkept5 c Hc). exact (HQ5cs c Hc Nsp N8 N18). }
    (* +0x44 beqz t1 : was the value negative? *)
    destruct (eq_vec (mf !!! Regidx t1_idx) zero_reg) eqn:Htf.
    - (* no sign digit: straight to the tail with n = i' *)
      iApply (wp_beqz_x0_taken_s_sconf (mword_of_int (KernelSyms.printint + 0x44)) (mword_of_int 24 : mword 13)
                t1_idx mf (K - 8)%nat b ltac:(vm_compute; discriminate) ltac:(rgne; exact Htf)
                ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi44").
      iApply bi.later_intro. iIntros (CIDtk Hstk) "Hcg Hpc".
      assert (Htgt5c : add_vec (mword_of_int (KernelSyms.printint + 0x44) : mword 64) (sign_extend' 64 (mword_of_int 24 : mword 13)) = mword_of_int (KernelSyms.printint + 0x5c)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Htgt5c) in "Hpc".
      assert (HshiftA : b = false \/ pcur = zero_reg -> (CIDtk : CPU) = (CID0 : CPU)) by wp_next_chain.
      iDestruct (wp_next_shift HshiftA with "Hcont") as "Hcont".
      iDestruct (cpu_own_transport CID0 CIDtk n eb pcur C b ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
      iApply (wp_printint_tail (CID0 := CIDtk) γl γd γv m mf K i' bs n eb C b pcur lks HK Hn31
                Hi1 ltac:(lia) Hf4 Hmfsp Hmfs2 Hmfcs Hal7 Hal6 Hal5 Hlkbelow
                with "Hcg Hcnt Htext Hpc Hbuf Hc1 Hc2 Hc3 Hc4 Hc8 Hpanic Hdev Htxl Hsent Hcont").
    - (* a sign digit: buf[i'] = '-' , then the tail with n = i'+1 *)
      iApply (wp_beqz_x0_fall_s_sconf (mword_of_int (KernelSyms.printint + 0x44)) (mword_of_int 24 : mword 13)
                t1_idx mf (K - 8)%nat b ltac:(vm_compute; discriminate) ltac:(rgne; exact Htf)
                with "Hcg Hpc Hi44").
      iIntros (CIDbf Hsbf) "Hcg Hpc".
      assert (Hp48 : add_vec_int (mword_of_int (KernelSyms.printint + 0x44) : mword 64) 4 = mword_of_int (KernelSyms.printint + 0x48)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp48) in "Hpc".
      (* +0x48 addi a5,a2,-32 *)
      iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.printint + 0x48)) a5_idx a2_idx (mword_of_int 4064 : mword 12)
                mf (K - 8)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi48").
      iIntros (CIDb1 Hsb1) "Hcg Hpc".
      iEval (rgne) in "Hcg".
      set (S1 := <[Regidx a5_idx := regval_into_reg (add_vec (mf !!! Regidx a2_idx) (sign_extend' 64 (mword_of_int 4064 : mword 12)))]> mf).
      assert (Hp4c : add_vec_int (mword_of_int (KernelSyms.printint + 0x48) : mword 64) 4 = mword_of_int (KernelSyms.printint + 0x4c)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp4c) in "Hpc".
      (* +0x4c add a2,a5,s0 *)
      assert (HS1s0 : S1 !!! Regidx s0_idx = sp0)
        by (rewrite /S1 upd_ne; [exact Hmfs0 | reg_neq]).
      assert (HS1a5 : S1 !!! Regidx a5_idx
                      = add_vec (mword_of_int (Z.of_nat i')) (mword_of_int (-32))).
      { rewrite /S1 upd_eq. unfold regval_into_reg. rewrite Hf2.
        f_equal; try (apply bv_eq; vm_compute; reflexivity). }
      iApply (wp_add_s_sconf (mword_of_int (KernelSyms.printint + 0x4c)) a2_idx a5_idx s0_idx
                (add_vec (add_vec (mword_of_int (Z.of_nat i')) (mword_of_int (-32))) sp0)
                S1 (K - 8)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
                ltac:(rgne; rgne; rewrite HS1a5 HS1s0; reflexivity)
                with "Hcg Hpc Hi4c").
      iIntros (CIDb2 Hsb2) "Hcg Hpc".
      set (S2 := <[Regidx a2_idx := regval_into_reg (add_vec (add_vec (mword_of_int (Z.of_nat i')) (mword_of_int (-32))) sp0)]> S1).
      assert (Hp50 : add_vec_int (mword_of_int (KernelSyms.printint + 0x4c) : mword 64) 4 = mword_of_int (KernelSyms.printint + 0x50)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp50) in "Hpc".
      (* +0x50 li a5,45 : '-' *)
      iApply (wp_li4_s_sconf (mword_of_int (KernelSyms.printint + 0x50)) a5_idx (mword_of_int 45 : mword 12)
                (mword_of_int 45 : mword 64) S2 (K - 8)%nat b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                with "Hcg Hpc Hi50").
      iIntros (CIDb3 Hsb3) "Hcg Hpc".
      set (S3 := <[Regidx a5_idx := regval_into_reg (mword_of_int 45 : mword 64)]> S2).
      assert (HS3a2 : S3 !!! Regidx a2_idx = add_vec (add_vec (mword_of_int (Z.of_nat i')) (mword_of_int (-32))) sp0)
        by (rewrite /S3 upd_ne; [rewrite /S2 upd_eq; reflexivity | reg_neq]).
      assert (Hp54 : add_vec_int (mword_of_int (KernelSyms.printint + 0x50) : mword 64) 4 = mword_of_int (KernelSyms.printint + 0x54)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp54) in "Hpc".
      (* +0x54 sb a5,-24(a2) : buf[i'] = '-' *)
      assert (Hpa' : add_vec (rget S3 a2_idx) (sign_extend' 64 (mword_of_int 4072 : mword 12)) = pa_add buf i').
      { rgne. rewrite HS3a2.
        replace (sign_extend' 64 (mword_of_int 4072 : mword 12)) with (mword_of_int (-24) : mword 64)
          by (apply bv_eq; vm_compute; reflexivity).
        apply sign_slot_addr. }
      iDestruct (bytes_own_acc (DfracOwn 1) buf 24 i' ltac:(lia) with "Hbuf") as "[Hbi Hbcl]".
      iDestruct "Hbi" as (bold) "Hbi".
      iEval (rewrite -Hpa') in "Hbi".
      iApply (wp_sb_s_sconf (mword_of_int (KernelSyms.printint + 0x54)) a5_idx a2_idx (mword_of_int 4072 : mword 12)
                S3 (K - 8)%nat (bold : mword 8) b with "Hcg Hpc Hi54 Hbi").
      iIntros (CIDb4 Hsb4) "Hcg Hpc Hbi". iEval (rewrite Hpa') in "Hbi".
      iDestruct ("Hbcl" with "Hbi") as "Hbuf".
      assert (Hp58 : add_vec_int (mword_of_int (KernelSyms.printint + 0x54) : mword 64) 4 = mword_of_int (KernelSyms.printint + 0x58)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp58) in "Hpc".
      (* +0x58 addiw a4,a7,2 : the count, now with the sign *)
      assert (HS3a7 : S3 !!! Regidx a7_idx = mword_of_int (Z.of_nat (i' - 1))).
      { rewrite /S3 upd_ne; [| reg_neq]. rewrite /S2 upd_ne; [| reg_neq].
        rewrite /S1 upd_ne; [exact Hf7 | reg_neq]. }
      iApply (wp_addiw_s_sconf (mword_of_int (KernelSyms.printint + 0x58)) a4_idx a7_idx (mword_of_int 2 : mword 12)
                S3 (K - 8)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi58").
      iIntros (CIDb5 Hsb5) "Hcg Hpc".
      iEval (rgne) in "Hcg".
      set (S4 := <[Regidx a4_idx := regval_into_reg (sign_extend' 64 (subrange_vec_dec
                   (add_vec (S3 !!! Regidx a7_idx) (sign_extend' 64 (mword_of_int 2 : mword 12))) 31 0))]> S3).
      assert (HS4a4 : S4 !!! Regidx a4_idx = mword_of_int (Z.of_nat (i' + 1))).
      { rewrite /S4 upd_eq. unfold regval_into_reg. rewrite HS3a7.
        rewrite (addiw_lit (Z.of_nat (i' - 1)) 2 (sign_extend' 64 (mword_of_int 2 : mword 12))
                   ltac:(apply bv_eq; vm_compute; reflexivity)
                   ltac:(change (2^31) with 2147483648; lia)).
        f_equal. lia. }
      assert (Hp5c : add_vec_int (mword_of_int (KernelSyms.printint + 0x58) : mword 64) 4 = mword_of_int (KernelSyms.printint + 0x5c)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp5c) in "Hpc".
      (* the sign arm touched only caller-saved registers *)
      assert (HS4cs : forall c : mword 5, is_cs_idx c = true -> c <> csp_rs1 -> c <> s0_idx -> c <> s2_idx ->
                S4 !!! Regidx c = m !!! Regidx c).
      { intros c Hc Nsp N8 N18.
        pose proof (is_cs_idx_true_neq a2_idx c ltac:(vm_compute; reflexivity) Hc) as N2.
        pose proof (is_cs_idx_true_neq a4_idx c ltac:(vm_compute; reflexivity) Hc) as N4.
        pose proof (is_cs_idx_true_neq a5_idx c ltac:(vm_compute; reflexivity) Hc) as N5.
        rewrite /S4 upd_ne; [| congruence].
        rewrite /S3 upd_ne; [| congruence].
        rewrite /S2 upd_ne; [| congruence].
        rewrite /S1 upd_ne; [| congruence].
        exact (Hmfcs c Hc Nsp N8 N18). }
      assert (HshiftB : b = false \/ pcur = zero_reg -> (CIDb5 : CPU) = (CID0 : CPU)) by wp_next_chain.
      iDestruct (wp_next_shift HshiftB with "Hcont") as "Hcont".
      iDestruct (cpu_own_transport CID0 CIDb5 n eb pcur C b ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
      iApply (wp_printint_tail (CID0 := CIDb5) γl γd γv m S4 K (i' + 1)%nat bs n eb C b pcur lks HK Hn31
                ltac:(lia) ltac:(lia) HS4a4
                ltac:(rewrite /S4 upd_ne; [| reg_neq]; rewrite /S3 upd_ne; [| reg_neq];
                      rewrite /S2 upd_ne; [| reg_neq]; rewrite /S1 upd_ne; [exact Hmfsp | reg_neq])
                ltac:(rewrite /S4 upd_ne; [| reg_neq]; rewrite /S3 upd_ne; [| reg_neq];
                      rewrite /S2 upd_ne; [| reg_neq]; rewrite /S1 upd_ne; [exact Hmfs2 | reg_neq])
                HS4cs Hal7 Hal6 Hal5 Hlkbelow
                with "Hcg Hcnt Htext Hpc Hbuf Hc1 Hc2 Hc3 Hc4 Hc8 Hpanic Hdev Htxl Hsent Hcont").
  Qed.

  (* ================================================================== *)
  (*  THE WHOLE FUNCTION: prologue, the three sign paths, the body.      *)
  (* ================================================================== *)

  (* the sixteen bytes of [digits], as one 128-bit image word *)
  Definition digits_word : mword 128 :=
    mword_of_int 0x66656463626139383736353433323130.

  (* The sixteen [digits] bytes as a PURE lemma, outside any Iris goal.  It is
     stated here — rather than spliced into the [iPoseProof] below as an inline
     [ltac:(…)] — because the proofmode re-elaborates a spliced term without the
     [Qed] vm-seal: that one argument was 66.7 s of this file's 104 s.  Same
     rule (and same fix) as [ProofArgraw.ar_tbl_bytes]; see optimization.md. *)
  Lemma digits_bytes (j : nat) : (j < 16)%nat ->
    KernelData.kernel_data !! (KernelSyms.digits + Z.of_nat j)%Z
      = Some (nth_byte digits_word j).
  Proof.
    intro Hj.
    do 16 (destruct j as [|j]; [vm_compute; f_equal; apply bv_eq; reflexivity | ]).
    lia.
  Qed.

  Lemma digits_from_data : kernel_data -∗ digits_tbl (mword_of_int KernelSyms.digits).
  Proof.
    assert (Hle : text_end <= KernelSyms.digits)
      by (unfold text_end, KernelSyms.digits; lia).
    pose proof digits_bytes as Hb.
    iIntros "#Hkd".
    iPoseProof (kernel_data_window KernelSyms.digits digits_word 16
                  (mword_of_int KernelSyms.digits) eq_refl Hle Hb
                  with "Hkd") as "Hw".
    rewrite /digits_tbl. iApply (big_sepL_impl with "Hw").
    iIntros "!>" (k j Hk) "Hb". by iExists (nth_byte digits_word j).
  Qed.

  Lemma wp_printint_sconf_gen (γl : gname) (γd : uart_names) (γv : disk_names)
      (m : regfile) (K : nat) (bs : list (bv 8))
      (n : nat) (eb : bool) (C : iProp Σ) (b : bool) (pcur : mword 64) (lks : gset nat)
    : wp_printint_sconf_body γl γd γv m K bs n eb C b pcur lks.
  Proof.
    cbv beta delta [wp_printint_sconf_body].
    intros ra_i a1_i pcE ra0 ret_tgt HK Hbase Hn31 Hlkbelow.
    pose proof (pi_cap_bounds K HK) as (HK8 & HK16).
    assert (HK24 : (24 <= K)%nat) by (unfold printint_stack in HK; lia).
    iIntros "Hcg Hcnt #Htext #Hkdata Hpc #Hpanic #Hdev #Htxl #Hsent Hcont".
    iPoseProof (digits_from_data with "Hkdata") as "#Hdig".
    iPoseProof (pii_00 with "Htext") as "Hi00".
    iPoseProof (pii_02 with "Htext") as "Hi02".
    iPoseProof (pii_04 with "Htext") as "Hi04".
    iPoseProof (pii_06 with "Htext") as "Hi06".
    iPoseProof (pii_08 with "Htext") as "Hi08".
    iPoseProof (pii_0a with "Htext") as "Hi0a".
    iPoseProof (pii_0c with "Htext") as "Hi0c".
    iPoseProof (pii_10 with "Htext") as "Hi10".
    iPoseProof (pii_8e with "Htext") as "Hi8e".
    iPoseProof (pii_92 with "Htext") as "Hi92".
    iPoseProof (pii_94 with "Htext") as "Hi94".
    set (sp0 := m !!! Regidx csp_rs1).
    set (spd := add_vec sp0 (sign_extend' 64 (caddi16sp_imm (mword_of_int 60 : mword 6)))).
    assert (Hpush : spd = pa_stk sp0 8).
    { unfold spd, pa_stk, add_vec_int. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb1 : add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 7 : mword 6) ('b"000"))) = pa_stk sp0 1).
    { rewrite Hpush. unfold pa_stk, add_vec_int. rewrite pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb2 : add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 6 : mword 6) ('b"000"))) = pa_stk sp0 2).
    { rewrite Hpush. unfold pa_stk, add_vec_int. rewrite pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb4 : add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000"))) = pa_stk sp0 4).
    { rewrite Hpush. unfold pa_stk, add_vec_int. rewrite pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    (* ===== PROLOGUE ===== *)
    iApply (wp_caddi16sp_push_s_sconf (mword_of_int KernelSyms.printint) (mword_of_int 60 : mword 6) m K 8 b
              HK8 Hpush with "Hcg Hpc Hi00").
    iIntros (CID1 Hs1) "Hcg Hframe Hpc".
    set (W1 := <[Regidx csp_rs1 := regval_into_reg spd]> m).
    iEval (rewrite stack_own_slots; cbn [seq]) in "Hframe".
    iDestruct "Hframe" as "(S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & _)".
    iDestruct "S1" as (v1) "Hc1". iDestruct "S2" as (v2) "Hc2".
    iDestruct "S4" as (v4) "Hc4".
    iDestruct "S5" as (w5) "Hs5". iDestruct "S6" as (w6) "Hs6". iDestruct "S7" as (w7) "Hs7".
    assert (HW1sp : W1 !!! Regidx csp_rs1 = spd) by (rewrite /W1 upd_eq; reflexivity).
    assert (Hp02 : add_vec_int (mword_of_int KernelSyms.printint : mword 64) 2 = mword_of_int (KernelSyms.printint + 0x02)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp02) in "Hpc".
    (* +0x02 sd ra,56(sp) *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.printint + 0x02)) (mword_of_int 7 : mword 6) ra_idx
              W1 (K - 8)%nat v1 b with "Hcg Hpc Hi02 [Hc1]").
    { iEval (rewrite HW1sp Hb1). iExact "Hc1". }
    iIntros (CID2 Hs2) "Hcg Hpc Hc1". iEval (rewrite HW1sp Hb1) in "Hc1".
    iEval (rgne) in "Hc1".
    assert (HW1ra : W1 !!! Regidx ra_idx = m !!! Regidx ra_idx) by (rewrite /W1 upd_ne; [reflexivity | reg_neq]).
    iEval (rewrite HW1ra) in "Hc1".
    assert (Hp04 : add_vec_int (mword_of_int (KernelSyms.printint + 0x02) : mword 64) 2 = mword_of_int (KernelSyms.printint + 0x04)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp04) in "Hpc".
    (* +0x04 sd s0,48(sp) *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.printint + 0x04)) (mword_of_int 6 : mword 6) s0_idx
              W1 (K - 8)%nat v2 b with "Hcg Hpc Hi04 [Hc2]").
    { iEval (rewrite HW1sp Hb2). iExact "Hc2". }
    iIntros (CID3 Hs3) "Hcg Hpc Hc2". iEval (rewrite HW1sp Hb2) in "Hc2".
    iEval (rgne) in "Hc2".
    assert (HW1s0 : W1 !!! Regidx s0_idx = m !!! Regidx s0_idx) by (rewrite /W1 upd_ne; [reflexivity | reg_neq]).
    iEval (rewrite HW1s0) in "Hc2".
    assert (Hp06 : add_vec_int (mword_of_int (KernelSyms.printint + 0x04) : mword 64) 2 = mword_of_int (KernelSyms.printint + 0x06)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp06) in "Hpc".
    (* +0x06 sd s2,32(sp) *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.printint + 0x06)) (mword_of_int 4 : mword 6) s2_idx
              W1 (K - 8)%nat v4 b with "Hcg Hpc Hi06 [Hc4]").
    { iEval (rewrite HW1sp Hb4). iExact "Hc4". }
    iIntros (CID4 Hs4) "Hcg Hpc Hc4". iEval (rewrite HW1sp Hb4) in "Hc4".
    iEval (rgne) in "Hc4".
    assert (HW1s2 : W1 !!! Regidx s2_idx = m !!! Regidx s2_idx) by (rewrite /W1 upd_ne; [reflexivity | reg_neq]).
    iEval (rewrite HW1s2) in "Hc4".
    assert (Hp08 : add_vec_int (mword_of_int (KernelSyms.printint + 0x06) : mword 64) 2 = mword_of_int (KernelSyms.printint + 0x08)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp08) in "Hpc".
    (* +0x08 addi s0,sp,64 : s0 := the ENTRY sp *)
    iApply (wp_caddi4spn_s_sconf (mword_of_int (KernelSyms.printint + 0x08)) (Cregidx (mword_of_int 0)) (mword_of_int 16 : mword 8) s0_idx
              W1 (K - 8)%nat b ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi08").
    iIntros (CID5 Hs5) "Hcg Hpc".
    set (W2 := <[Regidx s0_idx := regval_into_reg (add_vec (W1 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 16 : mword 8))))]> W1).
    assert (HW2s0 : W2 !!! Regidx s0_idx = sp0).
    { rewrite /W2 upd_eq. unfold regval_into_reg. rewrite HW1sp. unfold spd.
      apply frame_cancel. apply bv_eq; vm_compute; reflexivity. }
    assert (HW2sp : W2 !!! Regidx csp_rs1 = spd) by (rewrite /W2 upd_ne; [exact HW1sp | reg_neq]).
    assert (HW2a1 : W2 !!! Regidx a1_idx = m !!! Regidx a1_idx).
    { rewrite /W2 upd_ne; [| reg_neq]. rewrite /W1 upd_ne; [reflexivity | reg_neq]. }
    assert (HW2a0 : W2 !!! Regidx a0_idx = m !!! Regidx a0_idx).
    { rewrite /W2 upd_ne; [| reg_neq]. rewrite /W1 upd_ne; [reflexivity | reg_neq]. }
    assert (HW2cs : forall c : mword 5, is_cs_idx c = true -> c <> csp_rs1 -> c <> s0_idx -> c <> s2_idx ->
              W2 !!! Regidx c = m !!! Regidx c).
    { intros c Hc Nsp N8 N18.
      rewrite /W2 upd_ne; [| congruence]. rewrite /W1 upd_ne; [reflexivity | congruence]. }
    (* the three byte slots [buf] lives in *)
    iDestruct (slots3_bytes_own sp0 7 w7 w6 w5 ltac:(lia) with "Hs7 Hs6 Hs5") as "[%Hals Hbuf]".
    destruct Hals as (Hal7 & Hal6 & Hal5).
    assert (Hp0a : add_vec_int (mword_of_int (KernelSyms.printint + 0x08) : mword 64) 2 = mword_of_int (KernelSyms.printint + 0x0a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp0a) in "Hpc".
    (* ===== the sign decision (0x0a / 0x0c / 0x8e) ===== *)
    destruct (eq_vec (W2 !!! Regidx a2_idx) zero_reg) eqn:Hsg.
    - (* sign == 0: skip the test *)
      iApply (wp_cbeqz_taken_s_sconf (mword_of_int (KernelSyms.printint + 0x0a)) (mword_of_int 3 : mword 8)
                (Cregidx (mword_of_int 4)) a2_idx W2 (K - 8)%nat b
                ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(rgne; exact Hsg)
                ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi0a").
      iApply bi.later_intro. iIntros (CID6 Hs6) "Hcg Hpc".
      assert (Htgt10 : add_vec (mword_of_int (KernelSyms.printint + 0x0a) : mword 64) (sign_extend' 64 (sign_extend' 13 (concat_vec (mword_of_int 3 : mword 8) ('b"0")))) = mword_of_int (KernelSyms.printint + 0x10)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Htgt10) in "Hpc".
      (* +0x10 c.li t1,0 *)
      iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.printint + 0x10)) t1_idx (mword_of_int 0 : mword 6)
                (mword_of_int 0 : mword 64) W2 (K - 8)%nat b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                with "Hcg Hpc Hi10").
      iIntros (CID7 Hs7) "Hcg Hpc".
      set (N1 := <[Regidx t1_idx := regval_into_reg (mword_of_int 0 : mword 64)]> W2).
      assert (Hp12 : add_vec_int (mword_of_int (KernelSyms.printint + 0x10) : mword 64) 2 = mword_of_int (KernelSyms.printint + 0x12)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp12) in "Hpc".
      assert (HshiftA : b = false \/ pcur = zero_reg -> (CID7 : CPU) = (CID : CPU)) by wp_next_chain.
      iDestruct (wp_next_shift HshiftA with "Hcont") as "Hcont".
      iDestruct (cpu_own_transport CID CID7 n eb pcur C b ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
      iApply (wp_printint_main (CID0 := CID7) γl γd γv m N1 K (m !!! Regidx a0_idx) bs n eb C b pcur lks HK24 Hn31
                ltac:(rewrite /N1 upd_ne; [rewrite HW2a1; exact Hbase | reg_neq])
                ltac:(rewrite /N1 upd_ne; [exact HW2a0 | reg_neq])
                ltac:(rewrite /N1 upd_ne; [exact HW2sp | reg_neq])
                ltac:(rewrite /N1 upd_ne; [exact HW2s0 | reg_neq])
                ltac:(intros c Hc Nsp N8 N18;
                      pose proof (is_cs_idx_true_neq t1_idx c ltac:(vm_compute; reflexivity) Hc) as Nt1;
                      rewrite /N1 upd_ne; [ exact (HW2cs c Hc Nsp N8 N18) | congruence ])
                Hal7 Hal6 Hal5 Hlkbelow
                with "Hcg Hcnt Htext Hdig Hpc Hbuf Hc1 Hc2 S3 Hc4 S8 Hpanic Hdev Htxl Hsent Hcont").
    - (* sign != 0: test the value *)
      iApply (wp_cbeqz_fall_s_sconf (mword_of_int (KernelSyms.printint + 0x0a)) (mword_of_int 3 : mword 8)
                (Cregidx (mword_of_int 4)) a2_idx W2 (K - 8)%nat b
                ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(rgne; exact Hsg)
                with "Hcg Hpc Hi0a").
      iIntros (CID6b Hs6b) "Hcg Hpc".
      assert (Hp0c : add_vec_int (mword_of_int (KernelSyms.printint + 0x0a) : mword 64) 2 = mword_of_int (KernelSyms.printint + 0x0c)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp0c) in "Hpc".
      destruct (zopz0zI_s (W2 !!! Regidx a0_idx) zero_reg) eqn:Hneg.
      + (* xx < 0: negate, and remember the sign *)
        iApply (wp_blt_x0_taken_s_sconf (mword_of_int (KernelSyms.printint + 0x0c)) (mword_of_int 130 : mword 13)
                  a0_idx W2 (K - 8)%nat b ltac:(vm_compute; discriminate) ltac:(rgne; exact Hneg)
                  ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc Hi0c").
        iApply bi.later_intro. iIntros (CID7b Hs7b) "Hcg Hpc".
        assert (Htgt8e : add_vec (mword_of_int (KernelSyms.printint + 0x0c) : mword 64) (sign_extend' 64 (mword_of_int 130 : mword 13)) = mword_of_int (KernelSyms.printint + 0x8e)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Htgt8e) in "Hpc".
        (* +0x8e neg a0,a0 = sub a0,x0,a0 *)
        iDestruct (sie_cap_gpr_x0 W2 (K - 8)%nat b pcur (mword_of_int 0 : mword 5)
                     ltac:(vm_compute; reflexivity) with "Hcg") as "[%Hx0 Hcg]".
        iApply (wp_sub_s_sconf (mword_of_int (KernelSyms.printint + 0x8e)) a0_idx (mword_of_int 0 : mword 5) a0_idx
                  (sub_vec zero_reg (W2 !!! Regidx a0_idx)) W2 (K - 8)%nat b
                  ltac:(vm_compute; discriminate) ltac:(rdok)
                  ltac:(rgne; rgne; rewrite Hx0; reflexivity)
                  with "Hcg Hpc Hi8e").
        iIntros (CID8b Hs8b) "Hcg Hpc".
        set (G1 := <[Regidx a0_idx := regval_into_reg (sub_vec zero_reg (W2 !!! Regidx a0_idx))]> W2).
        assert (Hp92 : add_vec_int (mword_of_int (KernelSyms.printint + 0x8e) : mword 64) 4 = mword_of_int (KernelSyms.printint + 0x92)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hp92) in "Hpc".
        (* +0x92 c.li t1,1 *)
        iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.printint + 0x92)) t1_idx (mword_of_int 1 : mword 6)
                  (mword_of_int 1 : mword 64) G1 (K - 8)%nat b
                  ltac:(vm_compute; discriminate) ltac:(rdok)
                  ltac:(apply bv_eq; vm_compute; reflexivity)
                  with "Hcg Hpc Hi92").
        iIntros (CID9b Hs9b) "Hcg Hpc".
        set (G2 := <[Regidx t1_idx := regval_into_reg (mword_of_int 1 : mword 64)]> G1).
        assert (Hp94 : add_vec_int (mword_of_int (KernelSyms.printint + 0x92) : mword 64) 2 = mword_of_int (KernelSyms.printint + 0x94)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hp94) in "Hpc".
        (* +0x94 j 0x12 *)
        iApply (wp_cj_s_sconf (mword_of_int (KernelSyms.printint + 0x94)) (sign_extend' 21 (concat_vec (mword_of_int 1983 : mword 11) ('b"0")))
                  G2 (K - 8)%nat b ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc Hi94").
        iIntros (CID10b Hs10b). iApply bi.later_intro. iIntros "Hcg Hpc".
        assert (Htgt12 : add_vec (mword_of_int (KernelSyms.printint + 0x94) : mword 64) (sign_extend' 64 (sign_extend' 21 (concat_vec (mword_of_int 1983 : mword 11) ('b"0")))) = mword_of_int (KernelSyms.printint + 0x12)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Htgt12) in "Hpc".
        assert (HshiftB : b = false \/ pcur = zero_reg -> (CID10b : CPU) = (CID : CPU)) by wp_next_chain.
        iDestruct (wp_next_shift HshiftB with "Hcont") as "Hcont".
        iDestruct (cpu_own_transport CID CID10b n eb pcur C b ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
        iApply (wp_printint_main (CID0 := CID10b) γl γd γv m G2 K (sub_vec zero_reg (W2 !!! Regidx a0_idx)) bs n eb C b pcur lks HK24 Hn31
                  ltac:(rewrite /G2 upd_ne; [| reg_neq]; rewrite /G1 upd_ne;
                        [rewrite HW2a1; exact Hbase | reg_neq])
                  ltac:(rewrite /G2 upd_ne; [| reg_neq]; rewrite /G1 upd_eq; reflexivity)
                  ltac:(rewrite /G2 upd_ne; [| reg_neq]; rewrite /G1 upd_ne; [exact HW2sp | reg_neq])
                  ltac:(rewrite /G2 upd_ne; [| reg_neq]; rewrite /G1 upd_ne; [exact HW2s0 | reg_neq])
                  ltac:(intros c Hc Nsp N8 N18;
                        pose proof (is_cs_idx_true_neq t1_idx c ltac:(vm_compute; reflexivity) Hc) as Nt1;
                        pose proof (is_cs_idx_true_neq a0_idx c ltac:(vm_compute; reflexivity) Hc) as Na0;
                        rewrite /G2 upd_ne; [| congruence];
                        rewrite /G1 upd_ne; [ exact (HW2cs c Hc Nsp N8 N18) | congruence ])
                  Hal7 Hal6 Hal5 Hlkbelow
                  with "Hcg Hcnt Htext Hdig Hpc Hbuf Hc1 Hc2 S3 Hc4 S8 Hpanic Hdev Htxl Hsent Hcont").
      + (* xx >= 0: the same [t1 := 0] path as the sign==0 case *)
        iApply (wp_blt_x0_fall_s_sconf (mword_of_int (KernelSyms.printint + 0x0c)) (mword_of_int 130 : mword 13)
                  a0_idx W2 (K - 8)%nat b ltac:(vm_compute; discriminate) ltac:(rgne; exact Hneg)
                  with "Hcg Hpc Hi0c").
        iIntros (CID7c Hs7c) "Hcg Hpc".
        assert (Hp10 : add_vec_int (mword_of_int (KernelSyms.printint + 0x0c) : mword 64) 4 = mword_of_int (KernelSyms.printint + 0x10)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hp10) in "Hpc".
        iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.printint + 0x10)) t1_idx (mword_of_int 0 : mword 6)
                  (mword_of_int 0 : mword 64) W2 (K - 8)%nat b
                  ltac:(vm_compute; discriminate) ltac:(rdok)
                  ltac:(apply bv_eq; vm_compute; reflexivity)
                  with "Hcg Hpc Hi10").
        iIntros (CID8c Hs8c) "Hcg Hpc".
        set (N1 := <[Regidx t1_idx := regval_into_reg (mword_of_int 0 : mword 64)]> W2).
        assert (Hp12 : add_vec_int (mword_of_int (KernelSyms.printint + 0x10) : mword 64) 2 = mword_of_int (KernelSyms.printint + 0x12)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hp12) in "Hpc".
        assert (HshiftC : b = false \/ pcur = zero_reg -> (CID8c : CPU) = (CID : CPU)) by wp_next_chain.
        iDestruct (wp_next_shift HshiftC with "Hcont") as "Hcont".
        iDestruct (cpu_own_transport CID CID8c n eb pcur C b ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
        iApply (wp_printint_main (CID0 := CID8c) γl γd γv m N1 K (m !!! Regidx a0_idx) bs n eb C b pcur lks HK24 Hn31
                  ltac:(rewrite /N1 upd_ne; [rewrite HW2a1; exact Hbase | reg_neq])
                  ltac:(rewrite /N1 upd_ne; [exact HW2a0 | reg_neq])
                  ltac:(rewrite /N1 upd_ne; [exact HW2sp | reg_neq])
                  ltac:(rewrite /N1 upd_ne; [exact HW2s0 | reg_neq])
                  ltac:(intros c Hc Nsp N8 N18;
                        pose proof (is_cs_idx_true_neq t1_idx c ltac:(vm_compute; reflexivity) Hc) as Nt1;
                        rewrite /N1 upd_ne; [ exact (HW2cs c Hc Nsp N8 N18) | congruence ])
                  Hal7 Hal6 Hal5 Hlkbelow
                  with "Hcg Hcnt Htext Hdig Hpc Hbuf Hc1 Hc2 S3 Hc4 S8 Hpanic Hdev Htxl Hsent Hcont").
  Qed.

End ProofPrintint.

(* ===================================================================== *)
(* THE SEALED FUNCTOR: instantiate the callee's WP hypothesis with its     *)
(* proven spec, discharging the PRINTINT Module Type.                      *)
(* ===================================================================== *)
  Definition wp_printint_sconf `{!riscvGS Σ, !sieG Σ, !lockG Σ} `{!uartGhostG Σ, !diskGhostG Σ} `{GEN : GenId} `{CID : CpuId}
      (γl : gname) (γd : uart_names) (γv : disk_names) (m0 : regfile) (K : nat)
      (bs : list (bv 8)) (n : nat) (eb : bool) (C : iProp Σ) (b : bool) (pcur : mword 64) (lks : gset nat)
      : wp_printint_sconf_body γl γd γv m0 K bs n eb C b pcur lks :=
    wp_printint_sconf_gen
      (fun `{CID0 : CpuId} γl' γd' γv' m' K' bs' n' eb' C' b' pcur' lks' =>
         Consputc.wp_consputc_sconf (CID:=CID0) γl' γd' γv' m' K' bs' n' eb' C' b' pcur' lks')
      γl γd γv m0 K bs n eb C b pcur lks.

End PrintintProof.
