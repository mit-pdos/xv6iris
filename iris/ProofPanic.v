(* ProofPanic.v -- panic()'s whole-function proof (SpecPanic.v), as a sealed
   functor over printk.

     void panic(char *s) {
       // printk("panic: ");
       // printk("%s\n", s);
       for (;;) ;
     }

   FIVE instructions since 06ea57f, and no callee at all:

     +0x00  c.addi      sp,sp,-16     the frame -fno-omit-frame-pointer keeps
     +0x02  c.sdsp      ra,8(sp)      ... and the saves it keeps with it
     +0x04  c.sdsp      s0,0(sp)
     +0x06  c.addi4spn  s0,sp,16      the frame pointer, never read
     +0x08  c.j         .             and here it stays

   THE SELF-JUMP IS THE WHOLE POINT, and it is the only part of the old
   proof that survived.  [pn_spin] proves it by Löb, hart-generically:
   [wp_cj_s_sconf] hands its continuation back UNDER A LATER (a backward
   jump is a loop back edge), and that later is exactly what discharges the
   induction hypothesis.  Nothing else is needed -- the contract has no
   postcondition to establish, so once the pc is at the self-jump with the
   machine capability in hand there is no obligation left but to keep
   stepping.  Structurally this is ProofSpin.v's [wp_spin] (the M-mode
   self-jump in entry.S) with the S-mode leaf doing the work.

   THE FIRST FOUR INSTRUCTIONS ARE DEAD CODE THAT STILL EXECUTES.  ra and s0
   are stored and never reloaded, s0 is set and never read -- but the stores
   really happen, so the proof still has to own the two words they write.
   The frame is SPENT: panic never pops, so the slots go to the push leaf
   and never come back, and no value written is ever needed again.  That is
   why [P0] below is only ever threaded, never inspected.

   THE CONTRACT IS UNCHANGED APART FROM [panic_env] (SpecPanic.v says why),
   so this proof is handed far more than it uses: [cpu_own], [kernel_data],
   [pk_desc_res] and three pure side conditions all arrive and are dropped.
   That is sound and deliberate -- Iris is affine, and a loose precondition
   keeps every call site's plumbing and stack budget exactly as it was.
   [panic_stack] is still 52 against a function that needs 2.

   THE PRINTK FUNCTOR PARAMETER IS LIKEWISE KEPT AND UNUSED, so [LinkPanic.v]
   and the import graph do not move.  It is the obvious thing to shed if
   panic's cone is ever tidied.

   Gone with the calls: the two .rodata literals and their byte lemmas (the
   image no longer contains "panic: " or "%s\n" at all -- they were the only
   .rodata this commit removed, which is why every later string moved down
   16 bytes), the [uart_sent_sub] baseline, and the message parked in a
   callee-saved register across the first call. *)
Set Printing Depth 40.
From Stdlib Require Import ZArith Bool Lia List String Ascii.
From stdpp Require Import gmap list bitvector.definitions.
From iris.algebra Require Import dfrac.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_var gen_heap invariants.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import RegFile HartTp.
Require Import RiscvExtras.
Require Import InstrBytes KernelText KernelDataInv.
Require Import StackOwn CalleeSaved.
Require Import WpMmodeLeafBase.
Require Import KernelRvcDecode.
Require Import WpSconfAlu WpSconfMem WpSconfCtl.
Require Import IntrDefs WpNext.
Require Import WpLock CpuOwn.
Require Import WpUart.
Require Import UartTxInv.
Require Import PrintkArgs.
Require Import SpecPrintk.
Require Import SpecPanic.
Require Import CodePanic.
From Kernel Require KernelInstrs KernelData KernelSyms.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Require Import TsoCtx.
Import Defs.
Local Open Scope Z_scope.

Notation PA := KernelSyms.panic.

(* ===================================================================== *)
(* 0.  The one numeric side condition left: panic's contract still asks   *)
(*     for 52 slots, and the code uses 2.                                 *)
(* ===================================================================== *)
Lemma pn_K2 (K : nat) : (panic_stack <= K)%nat -> (2 <= K)%nat.
Proof. lia. Qed.

(* ===================================================================== *)
(* 1.  +0x08  [c.j .]  -- the loop panic never leaves.                    *)
(*                                                                        *)
(* Hart-GENERIC and stated OUTSIDE any [CpuId] section: with interrupts   *)
(* enabled the self-jump can be trapped and resumed on another hart, so   *)
(* the induction hypothesis has to hold at every hart, not at the one the *)
(* loop was entered on.                                                   *)
(* ===================================================================== *)
Section PanicSpin.
  Context `{!riscvGS Σ, !xv6G Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.

  Context {kt : ktier}.
  (* [h] is bound as a [CpuId], not as a [CPU]: [Loop] itself is
     [LoopE gen_id cpu_id], so the PROGRAM names the hart it steps and the
     statement has to put one in scope for the body to elaborate at all. *)
  Lemma pn_spin :
    kernel_text -∗
    ∀ (h : CpuId) (m : regfile) (K : nat) (b : bool) (p : mword 64),
      sie_cap_gpr kt m K b p -∗
      pc_is (mword_of_int (PA + 0x8)) -∗
      WP (Loop : expr riscv_lang).
  Proof.
    assert (Htgt : add_vec (mword_of_int (PA + 0x8) : mword 64)
                     (sign_extend' 64 (sign_extend' 21
                        (concat_vec (mword_of_int 0 : mword 11) ('b"0"))))
                   = mword_of_int (PA + 0x8))
      by (apply bv_eq; vm_compute; reflexivity).
    iIntros "#Ht".
    iLöb as "IH".
    iIntros (h m K b p) "Hcg Hpc".
    iApply (wp_cj_s_sconf (CID := h) (mword_of_int (PA + 0x8))
              (sign_extend' 21 (concat_vec (mword_of_int 0 : mword 11) ('b"0")))
              m K b ltac:(rewrite Htgt; vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (pni_08 with "Ht"). }
    iApply wp_next_intro. iIntros (CIDx). iNext.
    iIntros "Hcg Hpc".
    iEval (rewrite Htgt) in "Hpc".
    iApply ("IH" $! CIDx m K b p with "Hcg Hpc").
  Qed.

End PanicSpin.

(* ===================================================================== *)
(* 2.  The whole function.                                                *)
(* ===================================================================== *)
Module PanicProof (Printk : PRINTK) : PANIC.
Section ProofPanic.
  Context `{!riscvGS Σ, !xv6G Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.

  Context {kt : ktier}.
  Local Ltac pcw := apply bv_eq; vm_compute; reflexivity.
  Local Ltac nz := vm_compute; discriminate.

  Notation Rra := (mword_of_int 1 : mword 5).
  Notation Rs0 := (mword_of_int 8 : mword 5).

  Lemma wp_panic_sconf
      (m : regfile) (K : nat)
      (n : nat) (eb : bool) (b : bool) (p : mword 64)
      (dm : pk_arg_desc) (lks : gset string)
    : wp_panic_sconf_body kt m K n eb b p dm lks.
  Proof.
    cbv beta zeta delta [wp_panic_sconf_body].
    intros HK Hdm Hn31 Hbelow.
    (* [Hown], [Hkdata], [Hmsg] and the [panic_env] slot (now [emp]) are the
       contract's surplus -- see the header.  Named and dropped. *)
    iIntros "Hcg Hown #Htext #Hkdata Hpc _ Hmsg".
    (* ================================================================== *)
    (* +0x00  c.addi sp,sp,-16 -- the 2-slot frame (48 is -16 in a 6-bit  *)
    (*        field)                                                      *)
    (* ================================================================== *)
    iApply (wp_caddi_sp_push_s_sconf (mword_of_int PA : mword 64)
              (mword_of_int 48 : mword 6) m K 2%nat b
              (pn_K2 K HK) (stk_push_16 (m !!! Regidx csp_rs1))
              with "Hcg Hpc []").
    { iApply (pni_00 with "Htext"). }
    iIntros (CID1 Hs1) "Hcg Hframe Hpc".
    set (P0 := <[Regidx csp_rs1 := regval_into_reg
                  (add_vec (m !!! Regidx csp_rs1)
                     (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6))))]> m).
    assert (HP0sp : P0 !!! Regidx csp_rs1 = pa_stk (m !!! Regidx csp_rs1) 2)
      by (rewrite /P0 upd_eq; apply stk_push_16).
    (* the two save-slot addresses, as the c.sdsp displacements compute them *)
    assert (Hb1 : add_vec (P0 !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1) 1).
    { rewrite HP0sp. unfold pa_stk, add_vec_int. rewrite !pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb2 : add_vec (P0 !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1) 2).
    { rewrite HP0sp. unfold pa_stk, add_vec_int. rewrite !pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    iEval (rewrite (stack_own_slots (KTR := kt)); cbn [seq]) in "Hframe".
    iDestruct "Hframe" as "(F1 & F2 & _)".
    iDestruct "F1" as (v1) "H1". iDestruct "F2" as (v2) "H2".
    (* ================================================================== *)
    (* +0x02 .. +0x04  sd ra,8(sp) / sd s0,0(sp) -- written, never read   *)
    (* ================================================================== *)
    assert (Hp02 : add_vec_int (mword_of_int PA : mword 64) 2
                   = mword_of_int (PA + 0x2)) by pcw.
    iEval (rewrite Hp02) in "Hpc".
    iApply (wp_csdsp_s_sconf (CID := CID1) (mword_of_int (PA + 0x2))
              (mword_of_int 1 : mword 6) Rra P0 (K - 2)%nat v1 b
              with "Hcg Hpc [] [H1]").
    { iApply (pni_02 with "Htext"). }
    { iEval (rewrite Hb1). iExact "H1". }
    iIntros (CID2 Hs2) "Hcg Hpc H1".
    assert (Hp04 : add_vec_int (mword_of_int (PA + 0x2) : mword 64) 2
                   = mword_of_int (PA + 0x4)) by pcw.
    iEval (rewrite Hp04) in "Hpc".
    iApply (wp_csdsp_s_sconf (CID := CID2) (mword_of_int (PA + 0x4))
              (mword_of_int 0 : mword 6) Rs0 P0 (K - 2)%nat v2 b
              with "Hcg Hpc [] [H2]").
    { iApply (pni_04 with "Htext"). }
    { iEval (rewrite Hb2). iExact "H2". }
    iIntros (CID3 Hs3) "Hcg Hpc H2".
    (* ================================================================== *)
    (* +0x06  c.addi4spn s0,sp,16 -- s0 := the ENTRY sp, and never read   *)
    (* ================================================================== *)
    assert (Hp06 : add_vec_int (mword_of_int (PA + 0x4) : mword 64) 2
                   = mword_of_int (PA + 0x6)) by pcw.
    iEval (rewrite Hp06) in "Hpc".
    iApply (wp_caddi4spn_s_sconf (CID := CID3) (mword_of_int (PA + 0x6))
              (Cregidx (mword_of_int 0)) (mword_of_int 4 : mword 8) Rs0
              P0 (K - 2)%nat b
              ltac:(vm_compute; reflexivity) ltac:(nz) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (pni_06 with "Htext"). }
    iIntros (CID4 Hs4) "Hcg Hpc".
    (* ================================================================== *)
    (* +0x08  and here it stays.                                          *)
    (* ================================================================== *)
    assert (Hp08 : add_vec_int (mword_of_int (PA + 0x6) : mword 64) 2
                   = mword_of_int (PA + 0x8)) by pcw.
    iEval (rewrite Hp08) in "Hpc".
    iApply (pn_spin with "Htext Hcg Hpc").
  Qed.

End ProofPanic.
End PanicProof.
