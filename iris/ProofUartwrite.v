(* ProofUartwrite.v -- the whole-function WP for xv6's uartwrite() as of
   xv6 `d80e61c5` (zeldovich/xv6-riscv `verified`).

     void uartwrite(char buf[], int n) {
       int i = 0;
       while (i < n) {
         sleep_prepare(&tx_chan);
         acquire(&tx_lock);
         if (ReadReg(LSR) & LSR_TX_IDLE) {
           WriteReg(THR, buf[i]);
           release(&tx_lock);
           i += 1;
         } else {
           release(&tx_lock);
           sleep();
         }
       }
     }

   THE SHAPE, AND WHAT IS DIFFERENT FROM EVERY EARLIER VERSION OF THIS PROOF.
   [tx_lock] is a SPINLOCK again, but -- unlike the pre-`ae96fd0` code, whose
   proof this one descends from -- it is taken and released INSIDE the loop,
   once per byte, and the park happens with NOTHING held.  Three consequences,
   and they are the whole design:

   - NOTHING LINEAR CROSSES THE LOOP'S BACK EDGE that the park could
     invalidate.  What rides the loop is the register/frame state, the
     read-only buffer, the caller's pid cell, and the PERSISTENT trace claim
     [UartTxInv.uart_sent_sub] -- no [locked], no [tx_res], no [arm_pay].
     The critical section is entirely inside one turn: acquire mints
     [arm_pay 0 eb pj], release spends it, and the level is back at 0 before
     [sleep] is even reached (which is what makes the park legal at all --
     sched() demands noff = 0 here, i.e. no lock held).

   - THE THR STORE IS LICENSED BY THE WRITER'S OWN LSR POLL, three
     instructions earlier ([UAcc.wp_uart_lsr_read_ea_s_sconf] hands back
     [⌜lsr_thre_clear bt = false⌝ -∗ uart_out_lb γu l] and the [c.beqz] at
     +0x5e is taken exactly when THRE is clear).  ProofUartPutc.v is the
     worked instance of the same acquire / poll / store / release run.

   - THE OUTPUT CLAIM IS A SUBLIST.  uartwrite drops the lock between bytes,
     so another hart's bytes may be accepted in between and a contiguous
     [uart_sent] is simply false; [UartTxInv.uart_sent_sub] is the honest
     claim, accumulated one byte at a time with [uart_tx_own_sent_sub] (a
     plain fupd under [fupd_wp], run while the token is held) and
     [uart_sent_sub_snoc].

   CONTROL FLOW.  The loop is ROTATED: the head is +0x4a and the test is at
   +0x46, reached from BOTH arms (from the park arm with [i] unchanged, from
   the byte arm with [S i]).

     entry --blez a1--> +0x8c ret                      (n = 0: no frame at all)
           \--n>0--> prologue, setup --c.j--> +0x4a
     +0x4a sleep_prepare; acquire; poll LSR; c.beqz
             | THRE clear : +0x3c release, +0x42 sleep, fall to +0x46
             |              +0x46 bge i,n : i < n, so FALL -> +0x4a  (SAME i)
             \ THRE set   : +0x60..+0x6e push the byte, release, i += 1
                            +0x74 c.j -> +0x46
                            +0x46 bge (S i),n : = n -> TAKEN -> +0x76 (exit)
                                                < n -> FALL  -> +0x4a  (S i)

   So ONE iLoeb at +0x4a for the unbounded park at a fixed [i] ([uw_one]),
   nested inside a [nat] INDUCTION on the bytes remaining ([uw_iter], on [k]
   with [i + S k = n] -- the [S] matters, the head is only ever entered with
   at least one byte left).

   THE INDEX.  [cpu_own_eb_agree] at level 0 with the contract's [eb = true]
   pins the entry index to [true].  It stays [true] for the whole loop except
   between acquire's return and release's call, where it is the literal
   [false] and every leaf is a [wp_next_off_intro].  Every other leaf yields a
   fresh hart, so [cpu_own] is moved with [cpu_own_transport] before each
   callee and the two loop continuations are anchored at the function's entry
   hart [CID0].

   A functor over ACQUIRE / RELEASE / SLEEP / SLEEP_PREPARE / UART. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExtras.
Require Import RiscvModelBytes.
Require Import RegFile.
Require Import InstrBytes WpMmodeLeafBase.
Require Import SmodeCore.
Require Import ByteCursor.
Require Import StackOwn CalleeSaved KernelText.
Require Import IntrDefs.
Require Import HartTp WpNext.
Require Import WpSconfAlu WpSconfMem WpSconfCtl WpSconfBtype WpSmodeIntr.
Require Import WpLock ProcGeom CpuOwn KernelRvcDecode.
Require Import DevModel DiskPtsto WpUart.
Require Import SpecUart WpSconfUartAccess.
Require Import UartTxInv.
Require Import SpecPanic.
Require Import SchedCtx.
Require Import FdSlots.
Require Import SpecAcquire SpecRelease SpecSleep SpecSleepPrepare.
Require Import CodeUartwrite.
Require Import SpecUartwrite.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Import Defs.
Local Open Scope Z_scope.

Set Printing Depth 40.

Local Notation Rra  := (mword_of_int 1 : mword 5).
Local Notation Rs0  := (mword_of_int 8 : mword 5).
Local Notation Rs1  := (mword_of_int 9 : mword 5).
Local Notation Ra0  := (mword_of_int 10 : mword 5).
Local Notation Ra1  := (mword_of_int 11 : mword 5).
Local Notation Ra5  := (mword_of_int 15 : mword 5).
Local Notation Rs2  := (mword_of_int 18 : mword 5).
Local Notation Rs3  := (mword_of_int 19 : mword 5).
Local Notation Rs4  := (mword_of_int 20 : mword 5).
Local Notation Rs5  := (mword_of_int 21 : mword 5).
Local Notation Rs6  := (mword_of_int 22 : mword 5).
Local Notation Rs7  := (mword_of_int 23 : mword 5).
Local Notation Rs8  := (mword_of_int 24 : mword 5).
Local Notation Rs9  := (mword_of_int 25 : mword 5).
Local Notation Rs10 := (mword_of_int 26 : mword 5).
Local Notation Rs11 := (mword_of_int 27 : mword 5).


(* ===================================================================== *)
(*  Pure helpers.                                                         *)
(* ===================================================================== *)

(* the [+0(reg)] displacement every load/store in this function uses *)
Lemma uw_addv_0 (x : mword 64) :
  add_vec x (sign_extend' 64 (mword_of_int 0 : mword 12)) = x.
Proof. apply bv_add_0_r. vm_compute. reflexivity. Qed.

(* THE FRAME IS TEN SLOTS ([c.addi16sp sp,-80] at +0x04, [caddi16sp_imm 59]).
   A [c.sdsp]/[c.ldsp] displacement off the pushed sp names slot [10 - imm6]
   counted down from the ENTRY sp; slot 10 is padding and never written. *)
Lemma uw_slot_bridge (X : mword 64) (o : mword 64) (k : nat) :
  add_vec (mword_of_int (- (8 * Z.of_nat 10%nat))) o = mword_of_int (- (8 * Z.of_nat k)) ->
  add_vec (pa_stk X 10%nat) o = pa_stk X k.
Proof.
  intro H. unfold pa_stk, add_vec_int. rewrite po_addv_assoc H. reflexivity.
Qed.

(* the signed comparisons, on literal counts (pipewrite's [pw_geb_s0]). *)
Lemma uw_sint_moi (a : Z) : (- 2 ^ 63 <= a < 2 ^ 63)%Z ->
  sint (mword_of_int a : mword 64) = a.
Proof.
  intro Ha.
  assert (Hhm : bv_half_modulus (MachineWord.MachineWord.Z_idx 64) = 2 ^ 63)
    by (vm_compute; reflexivity).
  change (sint ?x) with (bv_swrap 64 (bv_unsigned x)).
  rewrite moi64_unsigned bv_swrap_wrap.
  apply bv_swrap_small. rewrite Hhm. lia.
Qed.

(* the [blez a1] at +0x00 *)
Lemma uw_geb_s0 (b : Z) : (- 2 ^ 63 <= b < 2 ^ 63)%Z ->
  zopz0zKzJ_s (zero_reg : mword 64) (mword_of_int b : mword 64) = Z.geb 0 b.
Proof.
  intro Hb. unfold zopz0zKzJ_s.
  assert (Hz : sint (zero_reg : mword 64) = 0%Z) by (vm_compute; reflexivity).
  rewrite Hz (uw_sint_moi b Hb). reflexivity.
Qed.

(* THE LOOP TEST IS A TWO-REGISTER [bge s1,s3] (+0x46): the C compares the
   INDEX with the COUNT rather than a moving pointer with its end, so
   [ByteCursor.pa_add_eqb] has no role here and this is what replaces it. *)
Lemma uw_geb_nn (a b : Z) :
  (- 2 ^ 63 <= a < 2 ^ 63)%Z -> (- 2 ^ 63 <= b < 2 ^ 63)%Z ->
  zopz0zKzJ_s (mword_of_int a : mword 64) (mword_of_int b : mword 64) = Z.geb a b.
Proof.
  intros Ha Hb. unfold zopz0zKzJ_s.
  rewrite (uw_sint_moi a Ha) (uw_sint_moi b Hb). reflexivity.
Qed.

(* the byte an [lbu] leaves in a register, read back by the [sb] that follows:
   the low 8 bits of the zero extension are the byte. *)
Lemma uw_sub8_zext (b : mword 8) :
  (autocast (T := mword) (subrange_vec_dec (zero_extend' 64 b : mword 64)
     (Z.sub (Z.mul 1 8) 1) 0) : mword 8) = b.
Proof.
  apply bv_eq. rewrite autocast_id.
  unfold subrange_vec_dec, to_word_idx, to_word, get_word,
         MachineWord.MachineWord.slice.
  rewrite bv_extract_unsigned.
  cbv [zero_extend' Operators_mwords.zero_extend Operators_mwords.extz_vec
       to_word get_word MachineWord.MachineWord.zero_extend].
  rewrite bv_zero_extend_unsigned; [| first [ done | vm_compute; discriminate | lia ] ].
  change (MachineWord.MachineWord.Z_idx 0) with 0%N.
  change (Z.of_N 0) with 0%Z. rewrite Z.shiftr_0_r.
  change (MachineWord.MachineWord.Z_idx (Z.sub (Z.mul 1 8) 1 - 0 + 1)) with 8%N.
  apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.

Lemma uw_zero_reg_add (x : mword 64) : add_vec zero_reg x = x.
Proof. apply add_vec_zero_l. Qed.

(* [pa_add p 0] is [p]: the cursor at entry is the buffer base itself. *)
Lemma uw_pa_add_0 (p : mword 64) : pa_add p 0%nat = p.
Proof. unfold pa_add, add_vec_int. apply bv_add_0_r. vm_compute. reflexivity. Qed.

(* the byte address is computed as [add a5,s6,s1] -- base PLUS INDEX, both
   held in registers -- so this is the bridge the +0x60 leaf's [wval] wants. *)
Lemma uw_pa_add_n (p : mword 64) (k : nat) :
  add_vec p (mword_of_int (Z.of_nat k)) = pa_add p k.
Proof. reflexivity. Qed.

(* a5's compressed-register index (the [c.beqz] at +0x5e) *)
Lemma uw_cr7 : creg2reg_idx (Cregidx (mword_of_int 7)) = Regidx (mword_of_int 15 : mword 5).
Proof. vm_compute. reflexivity. Qed.

(* ---- the [c.addiw s1,s1,1] at +0x72 ---------------------------------- *)
(* i += 1 on a 32-bit int held in a 64-bit register: the ADDIW truncates to
   32 bits and sign-extends back, which is the identity on [0 <= i < 2^31 - 1]. *)
Lemma uw_wrap32 (z : Z) : bv_wrap 32 z = z mod 4294967296.
Proof. unfold bv_wrap, bv_modulus. reflexivity. Qed.

Lemma uw_wrap64 (z : Z) : bv_wrap 64 z = z mod 18446744073709551616.
Proof. unfold bv_wrap, bv_modulus. reflexivity. Qed.

Lemma uw_addiw_p1 (i : nat) : (Z.of_nat i + 1 < 2 ^ 31)%Z ->
  sign_extend' 64 (subrange_vec_dec
     (add_vec (mword_of_int (Z.of_nat i) : mword 64)
              (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6)))) 31 0)
  = (mword_of_int (Z.of_nat (S i)) : mword 64).
Proof.
  intro H31.
  assert (H231 : (2 ^ 31 = 2147483648)%Z) by (vm_compute; reflexivity).
  rewrite H231 in H31.
  assert (HSi : Z.of_nat (S i) = (Z.of_nat i + 1)%Z) by lia.
  assert (E : (subrange_vec_dec
                 (add_vec (mword_of_int (Z.of_nat i) : mword 64)
                    (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6)))) 31 0 : mword 32)
              = (mword_of_int (Z.of_nat i + 1) : mword 32)).
  { apply bv_eq. rewrite subrange_31_0_unsigned add_vec64_unsigned moi64_unsigned.
    assert (Hp1c : bv_unsigned (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6)) : mword 64)
                   = 1%Z)
      by (vm_compute; reflexivity).
    rewrite Hp1c moi32_unsigned uw_wrap32 !uw_wrap64.
    rewrite (Z.mod_small (Z.of_nat i) 18446744073709551616); [| lia].
    rewrite (Z.mod_small (Z.of_nat i + 1) 18446744073709551616); [| lia].
    reflexivity. }
  rewrite E HSi. apply bv_eq.
  rewrite (sext64_moi32_unsigned (Z.of_nat i + 1) ltac:(lia)).
  rewrite moi64_unsigned uw_wrap64. symmetry. apply Z.mod_small. lia.
Qed.

(* ------------------------------------------------------------------ *)
(*  The two register-state predicates.  HART-FREE (no tp conjunct:      *)
(*  [HartTp.tp_pin] pins tp to whichever hart owns the register file).   *)
(* ------------------------------------------------------------------ *)
(* WHAT THE LOOP KEEPS IN REGISTERS: the index and the count (s1, s3), the
   lock address (s2), and the three hoisted constants -- the LSR address
   (s4), the wait channel (s5) and the THR address (s7) -- plus the buffer
   base (s6).  s0 is dead after the prologue and comes back off the frame. *)
Definition uw_loop_regs (m0 M : regfile) (spd buf : mword 64) (n i : nat) : Prop :=
  M !!! Regidx csp_rs1 = spd /\
  M !!! Regidx Rs1 = (mword_of_int (Z.of_nat i) : mword 64) /\
  M !!! Regidx Rs2 = a_tx_lock /\
  M !!! Regidx Rs3 = (mword_of_int (Z.of_nat n) : mword 64) /\
  M !!! Regidx Rs4 = uart_pa 5 /\
  M !!! Regidx Rs5 = a_tx_chan /\
  M !!! Regidx Rs6 = buf /\
  M !!! Regidx Rs7 = uart_pa 0 /\
  M !!! Regidx Rs8 = m0 !!! Regidx Rs8 /\
  M !!! Regidx Rs9 = m0 !!! Regidx Rs9 /\
  M !!! Regidx Rs10 = m0 !!! Regidx Rs10 /\
  M !!! Regidx Rs11 = m0 !!! Regidx Rs11.

(* ...and what the epilogue needs: the stack pointer, plus the four
   callee-saved registers this function never touches (s8..s11).  Everything
   else is read back out of the frame. *)
Definition uw_tail_regs (m0 M : regfile) (spd : mword 64) : Prop :=
  M !!! Regidx csp_rs1 = spd /\
  M !!! Regidx Rs8 = m0 !!! Regidx Rs8 /\
  M !!! Regidx Rs9 = m0 !!! Regidx Rs9 /\
  M !!! Regidx Rs10 = m0 !!! Regidx Rs10 /\
  M !!! Regidx Rs11 = m0 !!! Regidx Rs11.

Lemma uw_loop_regs_cs (m0 M M' : regfile) (spd buf : mword 64) (n i : nat) :
  callee_saved M M' ->
  uw_loop_regs m0 M spd buf n i -> uw_loop_regs m0 M' spd buf n i.
Proof.
  intros Hcs (H1 & H9 & H18 & H19 & H20 & H21 & H22 & H23 & H24 & H25 & H26 & H27).
  unfold uw_loop_regs.
  repeat first
    [ split
    | rewrite (callee_saved_lookup Hcs csp_rs1 ltac:(vm_compute; reflexivity))
    | rewrite (callee_saved_lookup Hcs (mword_of_int 9) ltac:(vm_compute; reflexivity))
    | rewrite (callee_saved_lookup Hcs (mword_of_int 18) ltac:(vm_compute; reflexivity))
    | rewrite (callee_saved_lookup Hcs (mword_of_int 19) ltac:(vm_compute; reflexivity))
    | rewrite (callee_saved_lookup Hcs (mword_of_int 20) ltac:(vm_compute; reflexivity))
    | rewrite (callee_saved_lookup Hcs (mword_of_int 21) ltac:(vm_compute; reflexivity))
    | rewrite (callee_saved_lookup Hcs (mword_of_int 22) ltac:(vm_compute; reflexivity))
    | rewrite (callee_saved_lookup Hcs (mword_of_int 23) ltac:(vm_compute; reflexivity))
    | rewrite (callee_saved_lookup Hcs (mword_of_int 24) ltac:(vm_compute; reflexivity))
    | rewrite (callee_saved_lookup Hcs (mword_of_int 25) ltac:(vm_compute; reflexivity))
    | rewrite (callee_saved_lookup Hcs (mword_of_int 26) ltac:(vm_compute; reflexivity))
    | rewrite (callee_saved_lookup Hcs (mword_of_int 27) ltac:(vm_compute; reflexivity))
    | assumption ].
Qed.

(* the accumulated output claim, and its one-byte step. *)
Definition uw_bytes (f : nat -> bv 8) (i : nat) : list (bv 8) := f <$> seq 0 i.

Lemma uw_bytes_snoc (f : nat -> bv 8) (i : nat) :
  uw_bytes f (S i) = (uw_bytes f i ++ [f i])%list.
Proof. rewrite /uw_bytes seq_S fmap_app. reflexivity. Qed.

(* ===================================================================== *)

Section UwProps.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !irefslotG Σ}.
  Context `{!uartGhostG Σ, !diskGhostG Σ}.
  Context `{GEN : RiscvLang.GenId}.

  (* THE EMPTY SUBLIST CLAIM, out of the device invariant alone.  The [n = 0]
     path never takes the lock, so it never holds a token to snapshot -- but
     [uart_sent] at the CURRENT accepted trace is free for anyone holding
     [dev_inv], and [] is a sublist of anything.  Same open/close shape as
     [UartTxInv.uart_tx_own_snapshot]. *)
  Lemma uw_sent_sub_empty (γu : uart_names) (γv : disk_names) (E : coPset) :
    ↑devN ⊆ E ->
    dev_inv γu γv ={E}=∗ uart_sent_sub γu [].
  Proof.
    iIntros (HE) "#Hinv".
    iDestruct (dev_inv_uart with "Hinv") as "#Huinv".
    iInv "Huinv" as ">Hbody" "Hclose".
    iDestruct "Hbody" as (u) "(Hu & Hg)".
    iEval (rewrite /uart_ghosts) in "Hg".
    iDestruct "Hg" as "(Hs & Hout & Htx & Hdl)".
    iDestruct (uart_sent_get with "Hs") as "[Hs #Hlb]".
    iMod ("Hclose" with "[Hu Hs Hout Htx Hdl]") as "_".
    { iApply bi.later_intro. iExists u. rewrite /uart_ghosts. iFrame. }
    iModIntro. iApply (uart_sent_sub_nil γu (uart_acc u) with "Hlb").
  Qed.

  (* ra/s0/s1/s2/s3/s4/s5/s6/s7 -- ALL NINE saved in the prologue, on the
     n > 0 path only (the [blez] is the function's FIRST instruction, so the
     n = 0 path never builds a frame at all and there is no shrink-wrapping
     to account for). *)
  Definition uw_saved (sp0 : mword 64) (m0 : regfile) : iProp Σ :=
    (pa_stk sp0 1 ↦₈ (m0 !!! Regidx Rra) ∗
     pa_stk sp0 2 ↦₈ (m0 !!! Regidx Rs0) ∗
     pa_stk sp0 3 ↦₈ (m0 !!! Regidx Rs1) ∗
     pa_stk sp0 4 ↦₈ (m0 !!! Regidx Rs2) ∗
     pa_stk sp0 5 ↦₈ (m0 !!! Regidx Rs3) ∗
     pa_stk sp0 6 ↦₈ (m0 !!! Regidx Rs4) ∗
     pa_stk sp0 7 ↦₈ (m0 !!! Regidx Rs5) ∗
     pa_stk sp0 8 ↦₈ (m0 !!! Regidx Rs6) ∗
     pa_stk sp0 9 ↦₈ (m0 !!! Regidx Rs7))%I.

  (* the tenth slot is alignment padding: never written, carried existentially *)
  Definition uw_slot10 (sp0 : mword 64) : iProp Σ :=
    (∃ w : mword 64, pa_stk sp0 10 ↦₈ w)%I.

  Lemma uw_frame_stack_own sp0 m0 :
    uw_saved sp0 m0 -∗ uw_slot10 sp0 -∗ stack_own sp0 10.
  Proof.
    iIntros "(H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9) H10".
    rewrite stack_own_slots. cbn [seq].
    iSplitL "H1"; [by iExists _|]. iSplitL "H2"; [by iExists _|].
    iSplitL "H3"; [by iExists _|]. iSplitL "H4"; [by iExists _|].
    iSplitL "H5"; [by iExists _|]. iSplitL "H6"; [by iExists _|].
    iSplitL "H7"; [by iExists _|]. iSplitL "H8"; [by iExists _|].
    iSplitL "H9"; [by iExists _|]. iSplitL "H10"; [by iExact "H10"|]. done.
  Qed.

  Definition uw_buf (buf : mword 64) (dq : dfrac) (f : nat -> bv 8) (n : nat) : iProp Σ :=
    ([∗ list] k0 ∈ seq 0 n, (pa_add buf k0) ↦ₘ{dq} f k0)%I.

  Definition uw_full (sp0 : mword 64) (m0 : regfile) : iProp Σ :=
    (uw_saved sp0 m0 ∗ uw_slot10 sp0)%I.

  (* ------------------------------------------------------------------ *)
  (*  The joins, each a [wp_next] at an explicit anchor.                  *)
  (*                                                                      *)
  (*  THE LOOP HEAD IS +0x4a (the [c.mv a0,s5] that sets up               *)
  (*  sleep_prepare's argument), NOT the loop TEST: gcc rotated the loop,  *)
  (*  so the test [bge s1,s3] sits at +0x46 and is reached from two places *)
  (*  with two DIFFERENT indices (from +0x74 with [S i] after a byte, and  *)
  (*  from sleep's return with [i] unchanged).  Handling +0x46 inline in   *)
  (*  each arm is therefore right; only +0x4a is a real join.              *)
  (* ------------------------------------------------------------------ *)

  (* the byte loop's back edge: another byte went out, and there is at least
     one more to go, so control is at +0x4a again with the index bumped *)
  Definition uw_next_cont `{CID0 : CpuId} (γu : uart_names)
      (j : nat) (m0 : regfile) (av : nat) (eb : bool) (C : iProp Σ)
      (sp0 buf : mword 64) (n : nat) (f : nat -> bv 8) (dq : dfrac)
      (pidv : mword 32) (dqp : dfrac) (i : nat) : iProp Σ :=
    (wp_next (CID0 := CID0) true (proc_addr j) (fun (CID : CpuId) =>
       ∀ M' : regfile,
       ⌜ (S i < n)%nat ⌝ -∗
       ⌜ uw_loop_regs m0 M' (pa_stk sp0 10) buf n (S i) ⌝ -∗
       sie_cap_gpr M' (av - 10)%nat true (proc_addr j) -∗
       cpu_own 0%nat eb (proc_addr j) C true -∗
       pc_is (mword_of_int (KernelSyms.uartwrite + 0x4a)) -∗
       p_pid (proc_addr j) ↦₄{dqp} pidv -∗
       uart_sent_sub γu (uw_bytes f (S i)) -∗
       uw_full sp0 m0 -∗ uw_buf buf dq f n -∗
       WP (Loop : expr riscv_lang)))%I.

  (* the loop's exit: [i = n], control at the nine restores *)
  Definition uw_exit_cont `{CID0 : CpuId} (γu : uart_names)
      (j : nat) (m0 : regfile) (av : nat) (eb : bool) (C : iProp Σ)
      (sp0 buf : mword 64) (n : nat) (f : nat -> bv 8) (dq : dfrac)
      (pidv : mword 32) (dqp : dfrac) : iProp Σ :=
    (wp_next (CID0 := CID0) true (proc_addr j) (fun (CID : CpuId) =>
       ∀ M' : regfile,
       ⌜ uw_loop_regs m0 M' (pa_stk sp0 10) buf n n ⌝ -∗
       sie_cap_gpr M' (av - 10)%nat true (proc_addr j) -∗
       cpu_own 0%nat eb (proc_addr j) C true -∗
       pc_is (mword_of_int (KernelSyms.uartwrite + 0x76)) -∗
       p_pid (proc_addr j) ↦₄{dqp} pidv -∗
       uart_sent_sub γu (uw_bytes f n) -∗
       uw_full sp0 m0 -∗ uw_buf buf dq f n -∗
       WP (Loop : expr riscv_lang)))%I.

  (* the loop head at +0x4a, ENTERED at whatever hart the last park landed on *)
  Definition uw_head `{CID0 : CpuId} (γu : uart_names)
      (j : nat) (m0 : regfile) (av : nat) (eb : bool) (C : iProp Σ)
      (sp0 buf : mword 64) (n : nat) (f : nat -> bv 8) (dq : dfrac)
      (pidv : mword 32) (dqp : dfrac) (i : nat) : iProp Σ :=
    (wp_next (CID0 := CID0) true (proc_addr j) (fun (CID : CpuId) =>
       ∀ M : regfile,
       ⌜ uw_loop_regs m0 M (pa_stk sp0 10) buf n i ⌝ -∗
       sie_cap_gpr M (av - 10)%nat true (proc_addr j) -∗
       cpu_own 0%nat eb (proc_addr j) C true -∗
       pc_is (mword_of_int (KernelSyms.uartwrite + 0x4a)) -∗
       p_pid (proc_addr j) ↦₄{dqp} pidv -∗
       uart_sent_sub γu (uw_bytes f i) -∗
       uw_full sp0 m0 -∗ uw_buf buf dq f n -∗
       uw_exit_cont (CID0 := CID0) γu j m0 av eb C sp0 buf n f dq pidv dqp -∗
       WP (Loop : expr riscv_lang)))%I.

  (* the tail's own continuation: uartwrite's postcondition, at ANY hart *)
  Definition uw_ret `{CID0 : CpuId} (γu : uart_names)
      (j : nat) (m0 : regfile) (av : nat) (eb : bool) (C : iProp Σ)
      (bs : list (bv 8)) (Rbuf : iProp Σ) (pidv : mword 32) (dqp : dfrac) : iProp Σ :=
    (wp_next (CID0 := CID0) true (proc_addr j) (fun (CID : CpuId) =>
       ∀ mf : regfile,
         ⌜ callee_saved m0 mf ⌝ -∗
         sie_cap_gpr mf av true (proc_addr j) -∗
         cpu_own 0%nat eb (proc_addr j) C true -∗
         pc_is (ret_pc (m0 !!! Regidx Rra)) -∗
         Rbuf -∗
         p_pid (proc_addr j) ↦₄{dqp} pidv -∗
         uart_sent_sub γu bs -∗
         WP (Loop : expr riscv_lang)))%I.

End UwProps.

(* ===================================================================== *)

Module UartwriteProof (Acquire : ACQUIRE) (Release : RELEASE) (Sleep : SLEEP)
                      (SleepPrepare : SLEEP_PREPARE) (Uart : UART) : UARTWRITE.

Module UAcc := UartAccessProof Uart.

Local Ltac reg_neq :=
  lazymatch goal with |- ?a <> ?b =>
    tryif unify a b then fail else (vm_compute; discriminate) end.
Local Ltac nz := vm_compute; discriminate.
Local Ltac pcw := apply bv_eq; vm_compute; reflexivity.

Section UwBodies.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !irefslotG Σ}.
  Context `{!uartGhostG Σ, !diskGhostG Σ}.

  (* [rget m k] at a NON-tp index is the plain map lookup ([rget_ne]). *)
  Local Ltac rgne :=
    rewrite rget_ne;
    [ | let H1 := fresh in let H2 := fresh in
        intro H1; injection H1 as H2; vm_compute in H2; congruence ].

  (* ------------------------------------------------------------------ *)
  (*  The epilogue: +0x76 -> return.  Reached only from the loop exit --   *)
  (*  the n = 0 path never gets a frame.                                  *)
  (* ------------------------------------------------------------------ *)
  Lemma uw_tail `{GEN : GenId} `{CID : CpuId} (CID0 : CPU)
      (γu : uart_names)
      (j : nat) (m0 M : regfile) (av : nat) (eb : bool) (C : iProp Σ) (sp0 : mword 64)
      (bs : list (bv 8)) (Rbuf : iProp Σ) (pidv : mword 32) (dqp : dfrac) :
    let pj := proc_addr j in
    uw_tail_regs m0 M (pa_stk sp0 10) ->
    m0 !!! Regidx csp_rs1 = sp0 ->
    (uartwrite_stack <= av)%nat ->
    eb = true ->
    (true = false \/ pj = zero_reg -> (CID : CPU) = CID0) ->
    kernel_text -∗
    sie_cap_gpr M (av - 10)%nat true pj -∗
    cpu_own 0%nat eb pj C true -∗
    pc_is (mword_of_int (KernelSyms.uartwrite + 0x76)) -∗
    p_pid pj ↦₄{dqp} pidv -∗
    uart_sent_sub γu bs -∗
    uw_saved sp0 m0 -∗ uw_slot10 sp0 -∗
    Rbuf -∗
    uw_ret (CID0 := CID0) γu j m0 av eb C bs Rbuf pidv dqp -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros pj Hregs Hsp0 Hav Heb Hanch. subst eb.
    destruct Hregs as (Hsp & H24 & H25 & H26 & H27).
    iIntros "#Ht Hcg Hcnt Hpc Hpid #Hsub Hsv Hs10 Hbuf Hcont".
    set (spd := pa_stk sp0 10%nat).
    iDestruct "Hsv" as "(H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9)".
    assert (Hb1 : add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 9 : mword 6) ('b"000"))) = pa_stk sp0 1)
      by (apply uw_slot_bridge; pcw).
    assert (Hb2 : add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 8 : mword 6) ('b"000"))) = pa_stk sp0 2)
      by (apply uw_slot_bridge; pcw).
    assert (Hb3 : add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 7 : mword 6) ('b"000"))) = pa_stk sp0 3)
      by (apply uw_slot_bridge; pcw).
    assert (Hb4 : add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 6 : mword 6) ('b"000"))) = pa_stk sp0 4)
      by (apply uw_slot_bridge; pcw).
    assert (Hb5 : add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000"))) = pa_stk sp0 5)
      by (apply uw_slot_bridge; pcw).
    assert (Hb6 : add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000"))) = pa_stk sp0 6)
      by (apply uw_slot_bridge; pcw).
    assert (Hb7 : add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000"))) = pa_stk sp0 7)
      by (apply uw_slot_bridge; pcw).
    assert (Hb8 : add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000"))) = pa_stk sp0 8)
      by (apply uw_slot_bridge; pcw).
    assert (Hb9 : add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) = pa_stk sp0 9)
      by (apply uw_slot_bridge; pcw).
    assert (P78 : add_vec_int (mword_of_int (KernelSyms.uartwrite + 0x76) : mword 64) 2 = mword_of_int (KernelSyms.uartwrite + 0x78)) by pcw.
    assert (P7a : add_vec_int (mword_of_int (KernelSyms.uartwrite + 0x78) : mword 64) 2 = mword_of_int (KernelSyms.uartwrite + 0x7a)) by pcw.
    assert (P7c : add_vec_int (mword_of_int (KernelSyms.uartwrite + 0x7a) : mword 64) 2 = mword_of_int (KernelSyms.uartwrite + 0x7c)) by pcw.
    assert (P7e : add_vec_int (mword_of_int (KernelSyms.uartwrite + 0x7c) : mword 64) 2 = mword_of_int (KernelSyms.uartwrite + 0x7e)) by pcw.
    assert (P80 : add_vec_int (mword_of_int (KernelSyms.uartwrite + 0x7e) : mword 64) 2 = mword_of_int (KernelSyms.uartwrite + 0x80)) by pcw.
    assert (P82 : add_vec_int (mword_of_int (KernelSyms.uartwrite + 0x80) : mword 64) 2 = mword_of_int (KernelSyms.uartwrite + 0x82)) by pcw.
    assert (P84 : add_vec_int (mword_of_int (KernelSyms.uartwrite + 0x82) : mword 64) 2 = mword_of_int (KernelSyms.uartwrite + 0x84)) by pcw.
    assert (P86 : add_vec_int (mword_of_int (KernelSyms.uartwrite + 0x84) : mword 64) 2 = mword_of_int (KernelSyms.uartwrite + 0x86)) by pcw.
    assert (P88 : add_vec_int (mword_of_int (KernelSyms.uartwrite + 0x86) : mword 64) 2 = mword_of_int (KernelSyms.uartwrite + 0x88)) by pcw.
    assert (P8a : add_vec_int (mword_of_int (KernelSyms.uartwrite + 0x88) : mword 64) 2 = mword_of_int (KernelSyms.uartwrite + 0x8a)) by pcw.
    iPoseProof (uwi_76 with "Ht") as "Hi76". iPoseProof (uwi_78 with "Ht") as "Hi78".
    iPoseProof (uwi_7a with "Ht") as "Hi7a". iPoseProof (uwi_7c with "Ht") as "Hi7c".
    iPoseProof (uwi_7e with "Ht") as "Hi7e". iPoseProof (uwi_80 with "Ht") as "Hi80".
    iPoseProof (uwi_82 with "Ht") as "Hi82". iPoseProof (uwi_84 with "Ht") as "Hi84".
    iPoseProof (uwi_86 with "Ht") as "Hi86". iPoseProof (uwi_88 with "Ht") as "Hi88".
    iPoseProof (uwi_8a with "Ht") as "Hi8a".
    (* +0x76  c.ldsp ra,72(sp) *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.uartwrite + 0x76)) (mword_of_int 9 : mword 6) Rra
              M (av - 10)%nat (m0 !!! Regidx Rra) true (dqm := DfracOwn 1)
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi76 [H1]").
    { iEval (rewrite Hsp Hb1). iExact "H1". }
    iIntros (CIDe1 Hse1) "Hcg Hpc H1". iEval (rewrite Hsp Hb1) in "H1".
    set (E1 := <[Regidx Rra := regval_into_reg (m0 !!! Regidx Rra)]> M).
    change (<[Regidx Rra := regval_into_reg (m0 !!! Regidx Rra)]> M) with E1.
    assert (HE1sp : E1 !!! Regidx csp_rs1 = spd) by (rewrite /E1 upd_ne; [exact Hsp | reg_neq]).
    iEval (rewrite P78) in "Hpc".
    (* +0x78  c.ldsp s0,64(sp) *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.uartwrite + 0x78)) (mword_of_int 8 : mword 6) Rs0
              E1 (av - 10)%nat (m0 !!! Regidx Rs0) true (dqm := DfracOwn 1)
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi78 [H2]").
    { iEval (rewrite HE1sp Hb2). iExact "H2". }
    iIntros (CIDe2 Hse2) "Hcg Hpc H2". iEval (rewrite HE1sp Hb2) in "H2".
    set (E2 := <[Regidx Rs0 := regval_into_reg (m0 !!! Regidx Rs0)]> E1).
    change (<[Regidx Rs0 := regval_into_reg (m0 !!! Regidx Rs0)]> E1) with E2.
    assert (HE2sp : E2 !!! Regidx csp_rs1 = spd) by (rewrite /E2 upd_ne; [exact HE1sp | reg_neq]).
    iEval (rewrite P7a) in "Hpc".
    (* +0x7a  c.ldsp s1,56(sp) *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.uartwrite + 0x7a)) (mword_of_int 7 : mword 6) Rs1
              E2 (av - 10)%nat (m0 !!! Regidx Rs1) true (dqm := DfracOwn 1)
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi7a [H3]").
    { iEval (rewrite HE2sp Hb3). iExact "H3". }
    iIntros (CIDe3 Hse3) "Hcg Hpc H3". iEval (rewrite HE2sp Hb3) in "H3".
    set (E3 := <[Regidx Rs1 := regval_into_reg (m0 !!! Regidx Rs1)]> E2).
    change (<[Regidx Rs1 := regval_into_reg (m0 !!! Regidx Rs1)]> E2) with E3.
    assert (HE3sp : E3 !!! Regidx csp_rs1 = spd) by (rewrite /E3 upd_ne; [exact HE2sp | reg_neq]).
    iEval (rewrite P7c) in "Hpc".
    (* +0x7c  c.ldsp s2,48(sp) *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.uartwrite + 0x7c)) (mword_of_int 6 : mword 6) Rs2
              E3 (av - 10)%nat (m0 !!! Regidx Rs2) true (dqm := DfracOwn 1)
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi7c [H4]").
    { iEval (rewrite HE3sp Hb4). iExact "H4". }
    iIntros (CIDe4 Hse4) "Hcg Hpc H4". iEval (rewrite HE3sp Hb4) in "H4".
    set (E4 := <[Regidx Rs2 := regval_into_reg (m0 !!! Regidx Rs2)]> E3).
    change (<[Regidx Rs2 := regval_into_reg (m0 !!! Regidx Rs2)]> E3) with E4.
    assert (HE4sp : E4 !!! Regidx csp_rs1 = spd) by (rewrite /E4 upd_ne; [exact HE3sp | reg_neq]).
    iEval (rewrite P7e) in "Hpc".
    (* +0x7e  c.ldsp s3,40(sp) *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.uartwrite + 0x7e)) (mword_of_int 5 : mword 6) Rs3
              E4 (av - 10)%nat (m0 !!! Regidx Rs3) true (dqm := DfracOwn 1)
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi7e [H5]").
    { iEval (rewrite HE4sp Hb5). iExact "H5". }
    iIntros (CIDe5 Hse5) "Hcg Hpc H5". iEval (rewrite HE4sp Hb5) in "H5".
    set (E5 := <[Regidx Rs3 := regval_into_reg (m0 !!! Regidx Rs3)]> E4).
    change (<[Regidx Rs3 := regval_into_reg (m0 !!! Regidx Rs3)]> E4) with E5.
    assert (HE5sp : E5 !!! Regidx csp_rs1 = spd) by (rewrite /E5 upd_ne; [exact HE4sp | reg_neq]).
    iEval (rewrite P80) in "Hpc".
    (* +0x80  c.ldsp s4,32(sp) *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.uartwrite + 0x80)) (mword_of_int 4 : mword 6) Rs4
              E5 (av - 10)%nat (m0 !!! Regidx Rs4) true (dqm := DfracOwn 1)
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi80 [H6]").
    { iEval (rewrite HE5sp Hb6). iExact "H6". }
    iIntros (CIDe6 Hse6) "Hcg Hpc H6". iEval (rewrite HE5sp Hb6) in "H6".
    set (E6 := <[Regidx Rs4 := regval_into_reg (m0 !!! Regidx Rs4)]> E5).
    change (<[Regidx Rs4 := regval_into_reg (m0 !!! Regidx Rs4)]> E5) with E6.
    assert (HE6sp : E6 !!! Regidx csp_rs1 = spd) by (rewrite /E6 upd_ne; [exact HE5sp | reg_neq]).
    iEval (rewrite P82) in "Hpc".
    (* +0x82  c.ldsp s5,24(sp) *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.uartwrite + 0x82)) (mword_of_int 3 : mword 6) Rs5
              E6 (av - 10)%nat (m0 !!! Regidx Rs5) true (dqm := DfracOwn 1)
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi82 [H7]").
    { iEval (rewrite HE6sp Hb7). iExact "H7". }
    iIntros (CIDe7 Hse7) "Hcg Hpc H7". iEval (rewrite HE6sp Hb7) in "H7".
    set (E7 := <[Regidx Rs5 := regval_into_reg (m0 !!! Regidx Rs5)]> E6).
    change (<[Regidx Rs5 := regval_into_reg (m0 !!! Regidx Rs5)]> E6) with E7.
    assert (HE7sp : E7 !!! Regidx csp_rs1 = spd) by (rewrite /E7 upd_ne; [exact HE6sp | reg_neq]).
    iEval (rewrite P84) in "Hpc".
    (* +0x84  c.ldsp s6,16(sp) *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.uartwrite + 0x84)) (mword_of_int 2 : mword 6) Rs6
              E7 (av - 10)%nat (m0 !!! Regidx Rs6) true (dqm := DfracOwn 1)
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi84 [H8]").
    { iEval (rewrite HE7sp Hb8). iExact "H8". }
    iIntros (CIDe8 Hse8) "Hcg Hpc H8". iEval (rewrite HE7sp Hb8) in "H8".
    set (E8 := <[Regidx Rs6 := regval_into_reg (m0 !!! Regidx Rs6)]> E7).
    change (<[Regidx Rs6 := regval_into_reg (m0 !!! Regidx Rs6)]> E7) with E8.
    assert (HE8sp : E8 !!! Regidx csp_rs1 = spd) by (rewrite /E8 upd_ne; [exact HE7sp | reg_neq]).
    iEval (rewrite P86) in "Hpc".
    (* +0x86  c.ldsp s7,8(sp) *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.uartwrite + 0x86)) (mword_of_int 1 : mword 6) Rs7
              E8 (av - 10)%nat (m0 !!! Regidx Rs7) true (dqm := DfracOwn 1)
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi86 [H9]").
    { iEval (rewrite HE8sp Hb9). iExact "H9". }
    iIntros (CIDe9 Hse9) "Hcg Hpc H9". iEval (rewrite HE8sp Hb9) in "H9".
    set (E9 := <[Regidx Rs7 := regval_into_reg (m0 !!! Regidx Rs7)]> E8).
    change (<[Regidx Rs7 := regval_into_reg (m0 !!! Regidx Rs7)]> E8) with E9.
    assert (HE9sp : E9 !!! Regidx csp_rs1 = spd) by (rewrite /E9 upd_ne; [exact HE8sp | reg_neq]).
    iEval (rewrite P88) in "Hpc".
    (* +0x88  c.addi16sp sp,80 -- the frame pop *)
    iAssert (uw_saved sp0 m0) with "[H1 H2 H3 H4 H5 H6 H7 H8 H9]" as "Hsv".
    { rewrite /uw_saved. iFrame "H1 H2 H3 H4 H5 H6 H7 H8 H9". }
    iAssert (stack_own sp0 10) with "[Hsv Hs10]" as "Hframe".
    { iApply (uw_frame_stack_own sp0 m0 with "Hsv Hs10"). }
    assert (Hpopv : add_vec (E9 !!! Regidx csp_rs1)
                      (sign_extend' 64 (caddi16sp_imm (mword_of_int 5 : mword 6))) = sp0).
    { rewrite HE9sp /spd. unfold pa_stk, add_vec_int. rewrite po_addv_assoc.
      rewrite (_ : add_vec (mword_of_int (- (8 * Z.of_nat 10%nat)) : mword 64)
                     (sign_extend' 64 (caddi16sp_imm (mword_of_int 5 : mword 6)))
                   = (mword_of_int 0 : mword 64)); [| pcw].
      apply bv_add_0_r. vm_compute. reflexivity. }
    assert (Hpop : E9 !!! Regidx csp_rs1
                   = pa_stk (add_vec (E9 !!! Regidx csp_rs1)
                       (sign_extend' 64 (caddi16sp_imm (mword_of_int 5 : mword 6)))) 10%nat)
      by (rewrite Hpopv HE9sp; reflexivity).
    iEval (rewrite -Hpopv) in "Hframe".
    iApply (wp_caddi16sp_pop_s_sconf (mword_of_int (KernelSyms.uartwrite + 0x88)) (mword_of_int 5 : mword 6)
              E9 (av - 10)%nat 10%nat true Hpop with "Hcg Hpc Hi88 Hframe").
    iIntros (CIDe10 Hse10) "Hcg Hpc".
    assert (Hav10 : ((av - 10) + 10)%nat = av) by (unfold uartwrite_stack in Hav; lia).
    iEval (rewrite Hav10) in "Hcg".
    set (E10 := <[Regidx csp_rs1 := regval_into_reg
        (add_vec (E9 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 5 : mword 6))))]> E9).
    change (<[Regidx csp_rs1 := regval_into_reg
        (add_vec (E9 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 5 : mword 6))))]> E9) with E10.
    iEval (rewrite P8a) in "Hpc".
    (* +0x8a  c.ret *)
    assert (HE10ra : E10 !!! Regidx Rra = m0 !!! Regidx Rra).
    { rewrite /E10 upd_ne; [| reg_neq]. rewrite /E9 upd_ne; [| reg_neq].
      rewrite /E8 upd_ne; [| reg_neq]. rewrite /E7 upd_ne; [| reg_neq].
      rewrite /E6 upd_ne; [| reg_neq]. rewrite /E5 upd_ne; [| reg_neq].
      rewrite /E4 upd_ne; [| reg_neq]. rewrite /E3 upd_ne; [| reg_neq].
      rewrite /E2 upd_ne; [| reg_neq]. rewrite /E1 upd_eq. reflexivity. }
    iApply (wp_cret_s_sconf (mword_of_int (KernelSyms.uartwrite + 0x8a)) Rra E10 av true ltac:(nz)
              with "Hcg Hpc Hi8a").
    iIntros (CIDe11 Hse11) "Hcg Hpc". iEval (rgne) in "Hpc".
    iEval (rewrite HE10ra) in "Hpc".
    (* ---- callee_saved m0 E10 ---- *)
    assert (HE10sp : E10 !!! Regidx csp_rs1 = m0 !!! Regidx csp_rs1)
      by (rewrite /E10 upd_eq; unfold regval_into_reg; rewrite Hpopv; symmetry; exact Hsp0).
    assert (HE10s0 : E10 !!! Regidx Rs0 = m0 !!! Regidx Rs0).
    { rewrite /E10 upd_ne; [| reg_neq]. rewrite /E9 upd_ne; [| reg_neq].
      rewrite /E8 upd_ne; [| reg_neq]. rewrite /E7 upd_ne; [| reg_neq].
      rewrite /E6 upd_ne; [| reg_neq]. rewrite /E5 upd_ne; [| reg_neq].
      rewrite /E4 upd_ne; [| reg_neq]. rewrite /E3 upd_ne; [| reg_neq].
      rewrite /E2 upd_eq. reflexivity. }
    assert (HE10s1 : E10 !!! Regidx Rs1 = m0 !!! Regidx Rs1).
    { rewrite /E10 upd_ne; [| reg_neq]. rewrite /E9 upd_ne; [| reg_neq].
      rewrite /E8 upd_ne; [| reg_neq]. rewrite /E7 upd_ne; [| reg_neq].
      rewrite /E6 upd_ne; [| reg_neq]. rewrite /E5 upd_ne; [| reg_neq].
      rewrite /E4 upd_ne; [| reg_neq]. rewrite /E3 upd_eq. reflexivity. }
    assert (HE10s2 : E10 !!! Regidx Rs2 = m0 !!! Regidx Rs2).
    { rewrite /E10 upd_ne; [| reg_neq]. rewrite /E9 upd_ne; [| reg_neq].
      rewrite /E8 upd_ne; [| reg_neq]. rewrite /E7 upd_ne; [| reg_neq].
      rewrite /E6 upd_ne; [| reg_neq]. rewrite /E5 upd_ne; [| reg_neq].
      rewrite /E4 upd_eq. reflexivity. }
    assert (HE10s3 : E10 !!! Regidx Rs3 = m0 !!! Regidx Rs3).
    { rewrite /E10 upd_ne; [| reg_neq]. rewrite /E9 upd_ne; [| reg_neq].
      rewrite /E8 upd_ne; [| reg_neq]. rewrite /E7 upd_ne; [| reg_neq].
      rewrite /E6 upd_ne; [| reg_neq]. rewrite /E5 upd_eq. reflexivity. }
    assert (HE10s4 : E10 !!! Regidx Rs4 = m0 !!! Regidx Rs4).
    { rewrite /E10 upd_ne; [| reg_neq]. rewrite /E9 upd_ne; [| reg_neq].
      rewrite /E8 upd_ne; [| reg_neq]. rewrite /E7 upd_ne; [| reg_neq].
      rewrite /E6 upd_eq. reflexivity. }
    assert (HE10s5 : E10 !!! Regidx Rs5 = m0 !!! Regidx Rs5).
    { rewrite /E10 upd_ne; [| reg_neq]. rewrite /E9 upd_ne; [| reg_neq].
      rewrite /E8 upd_ne; [| reg_neq]. rewrite /E7 upd_eq. reflexivity. }
    assert (HE10s6 : E10 !!! Regidx Rs6 = m0 !!! Regidx Rs6).
    { rewrite /E10 upd_ne; [| reg_neq]. rewrite /E9 upd_ne; [| reg_neq].
      rewrite /E8 upd_eq. reflexivity. }
    assert (HE10s7 : E10 !!! Regidx Rs7 = m0 !!! Regidx Rs7).
    { rewrite /E10 upd_ne; [| reg_neq]. rewrite /E9 upd_eq. reflexivity. }
    assert (Hthr : forall r : mword 5,
                     r <> csp_rs1 -> r <> Rra -> r <> Rs0 -> r <> Rs1 -> r <> Rs2 ->
                     r <> Rs3 -> r <> Rs4 -> r <> Rs5 -> r <> Rs6 -> r <> Rs7 ->
                     E10 !!! Regidx r = M !!! Regidx r).
    { intros r N2 N1 N8 N9 N18 N19 N20 N21 N22 N23.
      rewrite /E10 upd_ne; [| congruence]. rewrite /E9 upd_ne; [| congruence].
      rewrite /E8 upd_ne; [| congruence]. rewrite /E7 upd_ne; [| congruence].
      rewrite /E6 upd_ne; [| congruence]. rewrite /E5 upd_ne; [| congruence].
      rewrite /E4 upd_ne; [| congruence]. rewrite /E3 upd_ne; [| congruence].
      rewrite /E2 upd_ne; [| congruence]. rewrite /E1 upd_ne; [| congruence].
      reflexivity. }
    iDestruct (cpu_own_transport CID CIDe11 0 true pj C true ltac:(wp_next_chain)
                 with "Hcnt") as "Hcnt".
    rewrite /uw_ret.
    iSpecialize ("Hcont" $! CIDe11 with "[%]"); [wp_next_chain|].
    iApply ("Hcont" $! E10 with "[%] Hcg Hcnt Hpc Hbuf Hpid Hsub").
    unfold callee_saved.
    split; [exact HE10sp|].
    split; [exact HE10s0|].
    split; [exact HE10s1|].
    split; [exact HE10s2|].
    split; [exact HE10s3|].
    split; [exact HE10s4|].
    split; [exact HE10s5|].
    split; [exact HE10s6|].
    split; [exact HE10s7|].
    split; [rewrite (Hthr (mword_of_int 24) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)
                       ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)
                       ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)); exact H24|].
    split; [rewrite (Hthr (mword_of_int 25) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)
                       ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)
                       ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)); exact H25|].
    split; [rewrite (Hthr (mword_of_int 26) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)
                       ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)
                       ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)); exact H26|].
    rewrite (Hthr (mword_of_int 27) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)
               ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)
               ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)). exact H27.
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  ONE HEAD ENTRY at +0x4a, with the park's iLoeb inside.              *)
  (* ------------------------------------------------------------------ *)
  Lemma uw_one `{GEN : GenId} `{CID : CpuId} (CID0 : CPU)
      (γl : gname) (γu : uart_names) (γv : disk_names)
      (γs : list gname) (j : nat) (γlp : gname)
      (m0 M : regfile) (av : nat) (eb : bool) (C : iProp Σ)
      (sp0 buf : mword 64) (n : nat) (f : nat -> bv 8) (dq : dfrac)
      (pidv : mword 32) (dqp : dfrac) (i : nat) :
    let pj := proc_addr j in
    (i < n)%nat ->
    (Z.of_nat n < 2 ^ 31)%Z ->
    (j < NPROC)%nat -> γs !! j = Some γlp ->
    (uartwrite_stack <= av)%nat ->
    eb = true ->
    (true = false \/ pj = zero_reg -> (CID : CPU) = CID0) ->
    uw_loop_regs m0 M (pa_stk sp0 10) buf n i ->
    kernel_text -∗ dev_inv γu γv -∗ is_txlock γl γu -∗
    procs_inv γs -∗ panic_wp_any -∗
    sie_cap_gpr M (av - 10)%nat true pj -∗
    cpu_own 0%nat eb pj C true -∗
    pc_is (mword_of_int (KernelSyms.uartwrite + 0x4a)) -∗
    p_pid pj ↦₄{dqp} pidv -∗
    uart_sent_sub γu (uw_bytes f i) -∗
    uw_full sp0 m0 -∗ uw_buf buf dq f n -∗
    ( uw_next_cont (CID0 := CID0) γu j m0 av eb C sp0 buf n f dq pidv dqp i
      ∧ uw_exit_cont (CID0 := CID0) γu j m0 av eb C sp0 buf n f dq pidv dqp ) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros pj Hin Hn31 Hj Hjlp Hav Heb Hanch Hregs. subst eb.
    assert (H231 : (2 ^ 31 = 2147483648)%Z) by (vm_compute; reflexivity).
    assert (H263 : (2 ^ 63 = 9223372036854775808)%Z) by (vm_compute; reflexivity).
    rewrite H231 in Hn31.
    iIntros "#Ht #Hdinv #Htxl #Hpinv #Hpanic".
    iIntros "Hcg Hcnt Hpc Hpid #Hsub Hfull Hbuf Hcont".
    iDestruct (is_txlock_lock with "Htxl") as "#Hlk".
    iDestruct (is_txlock_dlab with "Htxl") as "#Hdlab".
    iPoseProof (uwi_3c with "Ht") as "#Hi3c".
    iPoseProof (uwi_3e with "Ht") as "#Hi3e".
    iPoseProof (uwi_42 with "Ht") as "#Hi42".
    iPoseProof (uwi_46 with "Ht") as "#Hi46".
    iPoseProof (uwi_4a with "Ht") as "#Hi4a".
    iPoseProof (uwi_4c with "Ht") as "#Hi4c".
    iPoseProof (uwi_50 with "Ht") as "#Hi50".
    iPoseProof (uwi_52 with "Ht") as "#Hi52".
    iPoseProof (uwi_56 with "Ht") as "#Hi56".
    iPoseProof (uwi_5a with "Ht") as "#Hi5a".
    iPoseProof (uwi_5e with "Ht") as "#Hi5e".
    iPoseProof (uwi_60 with "Ht") as "#Hi60".
    iPoseProof (uwi_64 with "Ht") as "#Hi64".
    iPoseProof (uwi_68 with "Ht") as "#Hi68".
    iPoseProof (uwi_6c with "Ht") as "#Hi6c".
    iPoseProof (uwi_6e with "Ht") as "#Hi6e".
    iPoseProof (uwi_72 with "Ht") as "#Hi72".
    iPoseProof (uwi_74 with "Ht") as "#Hi74".
    assert (P3e : add_vec_int (mword_of_int (KernelSyms.uartwrite + 0x3c) : mword 64) 2 = mword_of_int (KernelSyms.uartwrite + 0x3e)) by pcw.
    assert (P42 : ret_pc (add_vec_int (mword_of_int (KernelSyms.uartwrite + 0x3e) : mword 64) 4) = mword_of_int (KernelSyms.uartwrite + 0x42)) by pcw.
    assert (P46 : ret_pc (add_vec_int (mword_of_int (KernelSyms.uartwrite + 0x42) : mword 64) 4) = mword_of_int (KernelSyms.uartwrite + 0x46)) by pcw.
    assert (P4a : add_vec_int (mword_of_int (KernelSyms.uartwrite + 0x46) : mword 64) 4 = mword_of_int (KernelSyms.uartwrite + 0x4a)) by pcw.
    assert (P4c : add_vec_int (mword_of_int (KernelSyms.uartwrite + 0x4a) : mword 64) 2 = mword_of_int (KernelSyms.uartwrite + 0x4c)) by pcw.
    assert (P50 : ret_pc (add_vec_int (mword_of_int (KernelSyms.uartwrite + 0x4c) : mword 64) 4) = mword_of_int (KernelSyms.uartwrite + 0x50)) by pcw.
    assert (P52 : add_vec_int (mword_of_int (KernelSyms.uartwrite + 0x50) : mword 64) 2 = mword_of_int (KernelSyms.uartwrite + 0x52)) by pcw.
    assert (P56 : ret_pc (add_vec_int (mword_of_int (KernelSyms.uartwrite + 0x52) : mword 64) 4) = mword_of_int (KernelSyms.uartwrite + 0x56)) by pcw.
    assert (P5a : add_vec_int (mword_of_int (KernelSyms.uartwrite + 0x56) : mword 64) 4 = mword_of_int (KernelSyms.uartwrite + 0x5a)) by pcw.
    assert (P5e : add_vec_int (mword_of_int (KernelSyms.uartwrite + 0x5a) : mword 64) 4 = mword_of_int (KernelSyms.uartwrite + 0x5e)) by pcw.
    assert (P60 : add_vec_int (mword_of_int (KernelSyms.uartwrite + 0x5e) : mword 64) 2 = mword_of_int (KernelSyms.uartwrite + 0x60)) by pcw.
    assert (P64 : add_vec_int (mword_of_int (KernelSyms.uartwrite + 0x60) : mword 64) 4 = mword_of_int (KernelSyms.uartwrite + 0x64)) by pcw.
    assert (P68 : add_vec_int (mword_of_int (KernelSyms.uartwrite + 0x64) : mword 64) 4 = mword_of_int (KernelSyms.uartwrite + 0x68)) by pcw.
    assert (P6c : add_vec_int (mword_of_int (KernelSyms.uartwrite + 0x68) : mword 64) 4 = mword_of_int (KernelSyms.uartwrite + 0x6c)) by pcw.
    assert (P6e : add_vec_int (mword_of_int (KernelSyms.uartwrite + 0x6c) : mword 64) 2 = mword_of_int (KernelSyms.uartwrite + 0x6e)) by pcw.
    assert (P72 : ret_pc (add_vec_int (mword_of_int (KernelSyms.uartwrite + 0x6e) : mword 64) 4) = mword_of_int (KernelSyms.uartwrite + 0x72)) by pcw.
    assert (P74 : add_vec_int (mword_of_int (KernelSyms.uartwrite + 0x72) : mword 64) 2 = mword_of_int (KernelSyms.uartwrite + 0x74)) by pcw.
    assert (Jpark : add_vec (mword_of_int (KernelSyms.uartwrite + 0x5e) : mword 64)
                      (sign_extend' 64 (sign_extend' 13 (concat_vec (mword_of_int 239 : mword 8) ('b"0"))))
                    = mword_of_int (KernelSyms.uartwrite + 0x3c)) by pcw.
    assert (Jback : add_vec (mword_of_int (KernelSyms.uartwrite + 0x74) : mword 64)
                      (sign_extend' 64 (sign_extend' 21 (concat_vec (mword_of_int 2025 : mword 11) ('b"0"))))
                    = mword_of_int (KernelSyms.uartwrite + 0x46)) by pcw.
    assert (Jexit : add_vec (mword_of_int (KernelSyms.uartwrite + 0x46) : mword 64)
                      (sign_extend' 64 (mword_of_int 48 : mword 13))
                    = mword_of_int (KernelSyms.uartwrite + 0x76)) by pcw.
    assert (Jrel1 : add_vec (mword_of_int (KernelSyms.uartwrite + 0x3e) : mword 64)
                      (sign_extend' 64 (mword_of_int 828 : mword 21)) = mword_of_int KernelSyms.release) by pcw.
    assert (Jslp : add_vec (mword_of_int (KernelSyms.uartwrite + 0x42) : mword 64)
                     (sign_extend' 64 (mword_of_int 5654 : mword 21)) = mword_of_int KernelSyms.sleep) by pcw.
    assert (Jprep : add_vec (mword_of_int (KernelSyms.uartwrite + 0x4c) : mword 64)
                      (sign_extend' 64 (mword_of_int 5584 : mword 21)) = mword_of_int KernelSyms.sleep_prepare) by pcw.
    assert (Jacq : add_vec (mword_of_int (KernelSyms.uartwrite + 0x52) : mword 64)
                     (sign_extend' 64 (mword_of_int 672 : mword 21)) = mword_of_int KernelSyms.acquire) by pcw.
    assert (Jrel2 : add_vec (mword_of_int (KernelSyms.uartwrite + 0x6e) : mword 64)
                      (sign_extend' 64 (mword_of_int 780 : mword 21)) = mword_of_int KernelSyms.release) by pcw.
    (* ================================================================= *)
    (*  THE TURN: +0x4a .. back to +0x4a (park) or on to +0x46's two exits *)
    (* ================================================================= *)
    iAssert (wp_next (CID0 := CID) true pj (fun (CIDh : CpuId) =>
      ∀ M1 : regfile,
      ⌜ uw_loop_regs m0 M1 (pa_stk sp0 10) buf n i ⌝ -∗
      sie_cap_gpr M1 (av - 10)%nat true pj -∗
      cpu_own 0%nat true pj C true -∗
      pc_is (mword_of_int (KernelSyms.uartwrite + 0x4a)) -∗
      p_pid pj ↦₄{dqp} pidv -∗
      uw_full sp0 m0 -∗ uw_buf buf dq f n -∗
      ( uw_next_cont (CID0 := CID0) γu j m0 av true C sp0 buf n f dq pidv dqp i
        ∧ uw_exit_cont (CID0 := CID0) γu j m0 av true C sp0 buf n f dq pidv dqp ) -∗
      WP (Loop : expr riscv_lang)))%I with "[]" as "Turn".
    { iLöb as "IH".
      iIntros (CIDh Hsh M1) "%Hregs1 Hcg Hcnt Hpc Hpid Hfull Hbuf Hcont".
      pose proof Hregs1 as Hregs1'.
      destruct Hregs1' as (Hsp & Hs1 & Hs2 & Hs3 & Hs4 & Hs5 & Hs6 & Hs7 & W24 & W25 & W26 & W27).
      (* --- +0x4a  c.mv a0,s5 --- *)
      iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.uartwrite + 0x4a)) Ra0 Rs5
                M1 (av - 10)%nat true ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi4a").
      iIntros (CIDa1 Hsa1) "Hcg Hpc". iEval (rgne) in "Hcg".
      set (Q1 := <[Regidx Ra0 := regval_into_reg (add_vec zero_reg (M1 !!! Regidx Rs5))]> M1).
      change (<[Regidx Ra0 := regval_into_reg (add_vec zero_reg (M1 !!! Regidx Rs5))]> M1) with Q1.
      iEval (rewrite P4c) in "Hpc".
      assert (HQ1a0 : Q1 !!! Regidx Ra0 = a_tx_chan)
        by (rewrite /Q1 upd_eq uw_zero_reg_add; exact Hs5).
      assert (HcsQ1 : callee_saved M1 Q1)
        by (rewrite /Q1; apply callee_saved_insert_r;
            [vm_compute; reflexivity | apply callee_saved_refl]).
      (* --- +0x4c  jal ra,sleep_prepare --- *)
      iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.uartwrite + 0x4c)) Rra (mword_of_int 5584 : mword 21)
                Q1 (av - 10)%nat true ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi4c").
      iIntros (CIDa2 Hsa2) "Hcg Hpc".
      set (Q2 := <[Regidx Rra := regval_into_reg
          (add_vec_int (mword_of_int (KernelSyms.uartwrite + 0x4c) : mword 64) 4)]> Q1).
      change (<[Regidx Rra := regval_into_reg
          (add_vec_int (mword_of_int (KernelSyms.uartwrite + 0x4c) : mword 64) 4)]> Q1) with Q2.
      iEval (rewrite Jprep) in "Hpc".
      assert (HQ2a0 : Q2 !!! Regidx Ra0 = a_tx_chan)
        by (rewrite /Q2 upd_ne; [exact HQ1a0 | reg_neq]).
      assert (HQ2ra : Q2 !!! Regidx Rra = add_vec_int (mword_of_int (KernelSyms.uartwrite + 0x4c) : mword 64) 4)
        by (rewrite /Q2 upd_eq; reflexivity).
      assert (HcsQ2 : callee_saved M1 Q2).
      { rewrite /Q2. apply callee_saved_insert_r; [vm_compute; reflexivity | exact HcsQ1]. }
      iDestruct (cpu_own_transport CIDh CIDa2 0 true pj C true ltac:(wp_next_chain)
                   with "Hcnt") as "Hcnt".
      iApply (SleepPrepare.wp_sleep_prepare_sconf γs j γlp Q2 (av - 10)%nat 0%nat true C true
                Hj Hjlp ltac:(rewrite HQ2a0; vm_compute; reflexivity) ltac:(lia)
                ltac:(unfold uartwrite_stack in Hav; lia)
                with "Hcg Hcnt Ht Hpc Hpinv Hpanic").
      iIntros (CIDp Hsp' MP) "%HcsP Hcg Hcnt Hpc".
      iEval (rewrite HQ2ra P50) in "Hpc".
      assert (HregsP : uw_loop_regs m0 MP (pa_stk sp0 10) buf n i).
      { apply (uw_loop_regs_cs m0 Q2 MP); [exact HcsP|].
        apply (uw_loop_regs_cs m0 M1 Q2); [exact HcsQ2 | exact Hregs1]. }
      pose proof HregsP as HregsP'.
      destruct HregsP' as (Psp & Ps1 & Ps2 & Ps3 & Ps4 & Ps5 & Ps6 & Ps7 & P24 & P25 & P26 & P27).
      (* --- +0x50  c.mv a0,s2 --- *)
      iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.uartwrite + 0x50)) Ra0 Rs2
                MP (av - 10)%nat true ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi50").
      iIntros (CIDa3 Hsa3) "Hcg Hpc". iEval (rgne) in "Hcg".
      set (Q3 := <[Regidx Ra0 := regval_into_reg (add_vec zero_reg (MP !!! Regidx Rs2))]> MP).
      change (<[Regidx Ra0 := regval_into_reg (add_vec zero_reg (MP !!! Regidx Rs2))]> MP) with Q3.
      iEval (rewrite P52) in "Hpc".
      assert (HQ3a0 : Q3 !!! Regidx Ra0 = a_tx_lock)
        by (rewrite /Q3 upd_eq uw_zero_reg_add; exact Ps2).
      assert (HcsQ3 : callee_saved MP Q3)
        by (rewrite /Q3; apply callee_saved_insert_r;
            [vm_compute; reflexivity | apply callee_saved_refl]).
      (* --- +0x52  jal ra,acquire --- *)
      iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.uartwrite + 0x52)) Rra (mword_of_int 672 : mword 21)
                Q3 (av - 10)%nat true ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi52").
      iIntros (CIDa4 Hsa4) "Hcg Hpc".
      set (Q4 := <[Regidx Rra := regval_into_reg
          (add_vec_int (mword_of_int (KernelSyms.uartwrite + 0x52) : mword 64) 4)]> Q3).
      change (<[Regidx Rra := regval_into_reg
          (add_vec_int (mword_of_int (KernelSyms.uartwrite + 0x52) : mword 64) 4)]> Q3) with Q4.
      iEval (rewrite Jacq) in "Hpc".
      assert (HQ4a0 : Q4 !!! Regidx Ra0 = a_tx_lock)
        by (rewrite /Q4 upd_ne; [exact HQ3a0 | reg_neq]).
      assert (HQ4ra : Q4 !!! Regidx Rra = add_vec_int (mword_of_int (KernelSyms.uartwrite + 0x52) : mword 64) 4)
        by (rewrite /Q4 upd_eq; reflexivity).
      assert (HcsQ4 : callee_saved MP Q4).
      { rewrite /Q4. apply callee_saved_insert_r; [vm_compute; reflexivity | exact HcsQ3]. }
      iDestruct (cpu_own_transport CIDp CIDa4 0 true pj C true ltac:(wp_next_chain)
                   with "Hcnt") as "Hcnt".
      iApply (Acquire.wp_acquire_sconf γl "uart"%string (tx_res γu) Q4
                0%nat true pj C (av - 10)%nat true ltac:(lia)
                ltac:(unfold uartwrite_stack in Hav; lia)
                with "Hcg Hcnt Ht Hpc [Hlk] Hpanic").
      { iEval (rewrite HQ4a0). iExact "Hlk". }
      iIntros (CIDacq Hsacq ms MA) "%Hmsf Hcg Hpc %HcsA Htok HR Hcnt Hpay".
      iEval (rewrite HQ4ra P56) in "Hpc".
      assert (HregsA : uw_loop_regs m0 MA (pa_stk sp0 10) buf n i).
      { apply (uw_loop_regs_cs m0 Q4 MA); [exact HcsA|].
        apply (uw_loop_regs_cs m0 MP Q4); [exact HcsQ4 | exact HregsP]. }
      pose proof HregsA as HregsA'.
      destruct HregsA' as (Asp & As1 & As2 & As3 & As4 & As5 & As6 & As7 & A24 & A25 & A26 & A27).
      (* --- +0x56  lbu a5,0(s4)  -- the writer's OWN THRE poll --- *)
      iDestruct "HR" as (l) "Hown".
      iApply (UAcc.wp_uart_lsr_read_ea_s_sconf γu γv (mword_of_int (KernelSyms.uartwrite + 0x56))
                Ra5 Rs4 (mword_of_int 0 : mword 12) MA (trap_res true + (av - 10))%nat l false
                ltac:(nz) ltac:(rdok) ltac:(rgne; rewrite As4; apply uw_addv_0)
                with "Hcg Hpc Hi56 Hdinv Hown").
      iApply wp_next_off_intro. iIntros (bt) "Hcg Hpc Hown Hwlb".
      iEval (rewrite P5a) in "Hpc".
      set (D1 := <[Regidx Ra5 := regval_into_reg (lsr_ldval_of bt)]> MA).
      change (<[Regidx Ra5 := regval_into_reg (lsr_ldval_of bt)]> MA) with D1.
      (* --- +0x5a  andi a5,a5,32 --- *)
      iApply (wp_andi_s_sconf (mword_of_int (KernelSyms.uartwrite + 0x5a)) Ra5 Ra5
                (mword_of_int 32 : mword 12)
                (and_vec (lsr_ldval_of bt) (sign_extend' 64 (mword_of_int 32 : mword 12)))
                D1 (trap_res true + (av - 10))%nat false ltac:(nz) ltac:(rdok)
                ltac:(rgne; rewrite /D1 upd_eq; reflexivity) with "Hcg Hpc Hi5a").
      iApply wp_next_off_intro. iIntros "Hcg Hpc".
      set (D2 := <[Regidx Ra5 := regval_into_reg
          (and_vec (lsr_ldval_of bt) (sign_extend' 64 (mword_of_int 32 : mword 12)))]> D1).
      change (<[Regidx Ra5 := regval_into_reg
          (and_vec (lsr_ldval_of bt) (sign_extend' 64 (mword_of_int 32 : mword 12)))]> D1) with D2.
      iEval (rewrite P5e) in "Hpc".
      assert (HD2a5 : D2 !!! Regidx Ra5
                      = and_vec (lsr_ldval_of bt) (sign_extend' 64 (mword_of_int 32 : mword 12)))
        by (rewrite /D2 upd_eq; reflexivity).
      assert (HD2regs : uw_loop_regs m0 D2 (pa_stk sp0 10) buf n i).
      { unfold uw_loop_regs. split_and!;
          ((rewrite /D2 upd_ne; [| reg_neq]); (rewrite /D1 upd_ne; [| reg_neq]); assumption). }
      (* --- +0x5e  c.beqz a5 --- *)
      destruct (lsr_thre_clear bt) eqn:Hthre.
      - (* THRE clear: release, park, retry at the SAME index *)
        iApply (wp_cbeqz_taken_s_sconf (mword_of_int (KernelSyms.uartwrite + 0x5e))
                  (mword_of_int 239 : mword 8) (Cregidx (mword_of_int 7)) Ra5
                  D2 (trap_res true + (av - 10))%nat false uw_cr7 ltac:(nz)
                  ltac:(rgne; rewrite HD2a5; first [ exact Hthre | reflexivity ])
                  ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi5e").
        (* NOT convertible to [bi.later_intro]: this is the Loeb back edge --
           the continuation this specializes against is itself under a [▷], so
           the later has to come off a HYPOTHESIS, not just the goal. *)
        iNext. iApply wp_next_off_intro. iIntros "Hcg Hpc".
        iEval (rewrite Jpark) in "Hpc".
        (* --- +0x3c  c.mv a0,s2 --- *)
        iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.uartwrite + 0x3c)) Ra0 Rs2
                  D2 (trap_res true + (av - 10))%nat false ltac:(nz) ltac:(rdok)
                  with "Hcg Hpc Hi3c").
        iApply wp_next_off_intro. iIntros "Hcg Hpc". iEval (rgne) in "Hcg".
        set (K1 := <[Regidx Ra0 := regval_into_reg (add_vec zero_reg (D2 !!! Regidx Rs2))]> D2).
        change (<[Regidx Ra0 := regval_into_reg (add_vec zero_reg (D2 !!! Regidx Rs2))]> D2) with K1.
        iEval (rewrite P3e) in "Hpc".
        assert (HK1a0 : K1 !!! Regidx Ra0 = a_tx_lock).
        { rewrite /K1 upd_eq uw_zero_reg_add.
          rewrite /D2 upd_ne; [| reg_neq]. rewrite /D1 upd_ne; [| reg_neq]. exact As2. }
        assert (HcsK1 : callee_saved D2 K1)
          by (rewrite /K1; apply callee_saved_insert_r;
              [vm_compute; reflexivity | apply callee_saved_refl]).
        (* --- +0x3e  jal ra,release --- *)
        iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.uartwrite + 0x3e)) Rra (mword_of_int 828 : mword 21)
                  K1 (trap_res true + (av - 10))%nat false ltac:(nz) ltac:(rdok)
                  ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi3e").
        iApply wp_next_off_intro. iIntros "Hcg Hpc".
        set (K2 := <[Regidx Rra := regval_into_reg
            (add_vec_int (mword_of_int (KernelSyms.uartwrite + 0x3e) : mword 64) 4)]> K1).
        change (<[Regidx Rra := regval_into_reg
            (add_vec_int (mword_of_int (KernelSyms.uartwrite + 0x3e) : mword 64) 4)]> K1) with K2.
        iEval (rewrite Jrel1) in "Hpc".
        assert (HK2a0 : K2 !!! Regidx Ra0 = a_tx_lock)
          by (rewrite /K2 upd_ne; [exact HK1a0 | reg_neq]).
        assert (HK2ra : K2 !!! Regidx Rra = add_vec_int (mword_of_int (KernelSyms.uartwrite + 0x3e) : mword 64) 4)
          by (rewrite /K2 upd_eq; reflexivity).
        assert (HcsK2 : callee_saved D2 K2).
        { rewrite /K2. apply callee_saved_insert_r; [vm_compute; reflexivity | exact HcsK1]. }
        iApply (Release.wp_release_sconf γl a_tx_lock "uart"%string (tx_res γu) K2
                  0%nat true pj C (av - 10)%nat
                  ltac:(rewrite HK2a0; apply uw_addv_0)
                  ltac:(unfold uartwrite_stack in Hav; lia)
                  with "Hcg Ht Hpc Hlk Htok [Hown] Hcnt Hpay").
        { iApply (tx_res_intro γu l with "Hown"). }
        iIntros (CIDr Hsr MR) "Hcg Hpc %HcsR Hcnt".
        iEval (rewrite HK2ra P42) in "Hpc".
        assert (HregsR : uw_loop_regs m0 MR (pa_stk sp0 10) buf n i).
        { apply (uw_loop_regs_cs m0 K2 MR); [exact HcsR|].
          apply (uw_loop_regs_cs m0 D2 K2); [exact HcsK2 | exact HD2regs]. }
        (* --- +0x42  jal ra,sleep --- *)
        iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.uartwrite + 0x42)) Rra (mword_of_int 5654 : mword 21)
                  MR (av - 10)%nat true ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc Hi42").
        iIntros (CIDa5 Hsa5) "Hcg Hpc".
        set (K3 := <[Regidx Rra := regval_into_reg
            (add_vec_int (mword_of_int (KernelSyms.uartwrite + 0x42) : mword 64) 4)]> MR).
        change (<[Regidx Rra := regval_into_reg
            (add_vec_int (mword_of_int (KernelSyms.uartwrite + 0x42) : mword 64) 4)]> MR) with K3.
        iEval (rewrite Jslp) in "Hpc".
        assert (HK3ra : K3 !!! Regidx Rra = add_vec_int (mword_of_int (KernelSyms.uartwrite + 0x42) : mword 64) 4)
          by (rewrite /K3 upd_eq; reflexivity).
        assert (HcsK3 : callee_saved MR K3)
          by (rewrite /K3; apply callee_saved_insert_r;
              [vm_compute; reflexivity | apply callee_saved_refl]).
        iDestruct (cpu_own_transport CIDr CIDa5 0 true pj C true ltac:(wp_next_chain)
                     with "Hcnt") as "Hcnt".
        iApply (Sleep.wp_sleep_sconf γs j γlp K3 (av - 10)%nat true C Hj Hjlp
                  ltac:(unfold uartwrite_stack in Hav; lia)
                  with "Hcg Hcnt Ht Hpc Hpinv Hpanic [] []").
        { rewrite /trap_csrs_ext. done. }
        { rewrite /cpu_claim_ext. done. }
        iIntros (CIDs Hss MS) "%HcsS Hcg Hcnt Hpc _ _".
        iEval (rewrite HK3ra P46) in "Hpc".
        assert (HregsS : uw_loop_regs m0 MS (pa_stk sp0 10) buf n i).
        { apply (uw_loop_regs_cs m0 K3 MS); [exact HcsS|].
          apply (uw_loop_regs_cs m0 MR K3); [exact HcsK3 | exact HregsR]. }
        pose proof HregsS as HregsS'.
        destruct HregsS' as (Ssp & Ss1 & Ss2 & Ss3 & Ss4 & Ss5 & Ss6 & Ss7 & S24 & S25 & S26 & S27).
        (* --- +0x46  bge s1,s3 -- i < n, so FALL THROUGH --- *)
        assert (Hcmp : zopz0zKzJ_s (rget MS Rs1) (rget MS Rs3) = false).
        { rgne. rgne. rewrite Ss1 Ss3.
          rewrite (uw_geb_nn (Z.of_nat i) (Z.of_nat n) ltac:(lia) ltac:(lia)).
          rewrite Z.geb_leb. apply Z.leb_gt. lia. }
        iApply (wp_bge_fall_s_sconf (mword_of_int (KernelSyms.uartwrite + 0x46))
                  (mword_of_int 48 : mword 13) Rs3 Rs1 MS (av - 10)%nat true
                  ltac:(nz) ltac:(nz) Hcmp with "Hcg Hpc Hi46").
        iIntros (CIDb Hsb) "Hcg Hpc".
        iEval (rewrite P4a) in "Hpc".
        iSpecialize ("IH" $! CIDb with "[%]"); [wp_next_chain|].
        iApply ("IH" $! MS with "[%] Hcg Hcnt Hpc Hpid Hfull Hbuf Hcont").
        exact HregsS.
      - (* THRE set: push the byte, release, bump the index *)
        iApply (wp_cbeqz_fall_s_sconf (mword_of_int (KernelSyms.uartwrite + 0x5e))
                  (mword_of_int 239 : mword 8) (Cregidx (mword_of_int 7)) Ra5
                  D2 (trap_res true + (av - 10))%nat false uw_cr7 ltac:(nz)
                  ltac:(rgne; rewrite HD2a5; first [ exact Hthre | reflexivity ]) with "Hcg Hpc Hi5e").
        iApply wp_next_off_intro. iIntros "Hcg Hpc".
        iEval (rewrite P60) in "Hpc".
        iDestruct ("Hwlb" with "[%]") as "#Hlb"; [done|].
        (* --- +0x60  add a5,s6,s1 --- *)
        iApply (wp_add_s_sconf (mword_of_int (KernelSyms.uartwrite + 0x60)) Ra5 Rs6 Rs1
                  (pa_add buf i) D2 (trap_res true + (av - 10))%nat false ltac:(nz) ltac:(rdok)
                  ltac:(rgne; rgne;
                        rewrite (_ : D2 !!! Regidx Rs6 = buf);
                        [| rewrite /D2 upd_ne; [| reg_neq];
                           rewrite /D1 upd_ne; [| reg_neq]; exact As6];
                        rewrite (_ : D2 !!! Regidx Rs1 = (mword_of_int (Z.of_nat i) : mword 64));
                        [| rewrite /D2 upd_ne; [| reg_neq];
                           rewrite /D1 upd_ne; [| reg_neq]; exact As1];
                        apply uw_pa_add_n)
                  with "Hcg Hpc Hi60").
        iApply wp_next_off_intro. iIntros "Hcg Hpc".
        set (G1 := <[Regidx Ra5 := regval_into_reg (pa_add buf i)]> D2).
        change (<[Regidx Ra5 := regval_into_reg (pa_add buf i)]> D2) with G1.
        iEval (rewrite P64) in "Hpc".
        assert (HG1a5 : G1 !!! Regidx Ra5 = pa_add buf i) by (rewrite /G1 upd_eq; reflexivity).
        (* --- +0x64  lbu a5,0(a5) --- *)
        assert (Hlk0 : seq 0 n !! i = Some i) by (apply lookup_seq; split; [lia | exact Hin]).
        iDestruct (big_sepL_lookup_acc (fun _ x => ((pa_add buf x) ↦ₘ{dq} f x)%I) (seq 0 n) i i Hlk0
                     with "Hbuf") as "[Hbyte Hback]".
        assert (Haddrb : add_vec (rget G1 Ra5) (sign_extend' 64 (mword_of_int 0 : mword 12))
                         = pa_add buf i).
        { rgne. rewrite HG1a5. apply uw_addv_0. }
        iApply (wp_lbu_s_sconf (mword_of_int (KernelSyms.uartwrite + 0x64)) Ra5 Ra5
                  (mword_of_int 0 : mword 12) G1 (trap_res true + (av - 10))%nat (f i : mword 8) false
                  (dqm := dq) ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi64 [Hbyte]").
        { iEval (rewrite Haddrb). iExact "Hbyte". }
        iApply wp_next_off_intro. iIntros "Hcg Hpc Hbyte".
        iEval (rewrite Haddrb) in "Hbyte".
        iDestruct ("Hback" with "Hbyte") as "Hbuf".
        set (G2 := <[Regidx Ra5 := regval_into_reg (zero_extend' 64 (f i : mword 8))]> G1).
        change (<[Regidx Ra5 := regval_into_reg (zero_extend' 64 (f i : mword 8))]> G1) with G2.
        iEval (rewrite P68) in "Hpc".
        (* --- the trace re-link, before the push --- *)
        iApply fupd_wp.
        iMod (uart_tx_own_sent_sub γu γv l (uw_bytes f i) ⊤ ltac:(solve_ndisj)
                with "Hdinv Hown Hsub") as "[Hown %Hsublist]".
        iModIntro.
        (* --- +0x68  sb a5,0(s7)  -- the THR write --- *)
        assert (HG2s7 : rget G2 Rs7 = uart_pa 0).
        { rgne. rewrite /G2 upd_ne; [| reg_neq]. rewrite /G1 upd_ne; [| reg_neq].
          rewrite /D2 upd_ne; [| reg_neq]. rewrite /D1 upd_ne; [| reg_neq]. exact As7. }
        assert (HG2a5 : G2 !!! Regidx Ra5 = zero_extend' 64 (f i : mword 8))
          by (rewrite /G2 upd_eq; reflexivity).
        iApply (UAcc.wp_uart_thr_write_s_sconf γu γv (mword_of_int (KernelSyms.uartwrite + 0x68))
                  Ra5 Rs7 G2 (trap_res true + (av - 10))%nat l false HG2s7
                  with "Hcg Hpc Hi68 Hdinv Hown Hlb Hdlab").
        iApply wp_next_off_intro. iIntros "Hcg Hpc Hown #Hsent".
        assert (Hsb : (autocast (T := mword) (subrange_vec_dec (rget G2 Ra5)
                         (Z.sub (Z.mul 1 8) 1) 0) : mword 8) = f i).
        { rgne. rewrite HG2a5. apply uw_sub8_zext. }
        iEval (rewrite Hsb) in "Hown". iEval (rewrite Hsb) in "Hsent".
        iAssert (uart_sent_sub γu (uw_bytes f (S i))) as "#Hsub'".
        { rewrite uw_bytes_snoc.
          iApply (uart_sent_sub_snoc γu (uw_bytes f i) l (f i) Hsublist with "Hsent"). }
        iEval (rewrite P6c) in "Hpc".
        (* --- +0x6c  c.mv a0,s2 --- *)
        iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.uartwrite + 0x6c)) Ra0 Rs2
                  G2 (trap_res true + (av - 10))%nat false ltac:(nz) ltac:(rdok)
                  with "Hcg Hpc Hi6c").
        iApply wp_next_off_intro. iIntros "Hcg Hpc". iEval (rgne) in "Hcg".
        set (G3 := <[Regidx Ra0 := regval_into_reg (add_vec zero_reg (G2 !!! Regidx Rs2))]> G2).
        change (<[Regidx Ra0 := regval_into_reg (add_vec zero_reg (G2 !!! Regidx Rs2))]> G2) with G3.
        iEval (rewrite P6e) in "Hpc".
        assert (HG3a0 : G3 !!! Regidx Ra0 = a_tx_lock).
        { rewrite /G3 upd_eq uw_zero_reg_add.
          rewrite /G2 upd_ne; [| reg_neq]. rewrite /G1 upd_ne; [| reg_neq].
          rewrite /D2 upd_ne; [| reg_neq]. rewrite /D1 upd_ne; [| reg_neq]. exact As2. }
        assert (HcsG3 : callee_saved D2 G3).
        { rewrite /G3 /G2 /G1.
          apply callee_saved_insert_r; [vm_compute; reflexivity|].
          apply callee_saved_insert_r; [vm_compute; reflexivity|].
          apply callee_saved_insert_r; [vm_compute; reflexivity|].
          apply callee_saved_refl. }
        (* --- +0x6e  jal ra,release --- *)
        iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.uartwrite + 0x6e)) Rra (mword_of_int 780 : mword 21)
                  G3 (trap_res true + (av - 10))%nat false ltac:(nz) ltac:(rdok)
                  ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi6e").
        iApply wp_next_off_intro. iIntros "Hcg Hpc".
        set (G4 := <[Regidx Rra := regval_into_reg
            (add_vec_int (mword_of_int (KernelSyms.uartwrite + 0x6e) : mword 64) 4)]> G3).
        change (<[Regidx Rra := regval_into_reg
            (add_vec_int (mword_of_int (KernelSyms.uartwrite + 0x6e) : mword 64) 4)]> G3) with G4.
        iEval (rewrite Jrel2) in "Hpc".
        assert (HG4a0 : G4 !!! Regidx Ra0 = a_tx_lock)
          by (rewrite /G4 upd_ne; [exact HG3a0 | reg_neq]).
        assert (HG4ra : G4 !!! Regidx Rra = add_vec_int (mword_of_int (KernelSyms.uartwrite + 0x6e) : mword 64) 4)
          by (rewrite /G4 upd_eq; reflexivity).
        assert (HcsG4 : callee_saved D2 G4).
        { rewrite /G4. apply callee_saved_insert_r; [vm_compute; reflexivity | exact HcsG3]. }
        iApply (Release.wp_release_sconf γl a_tx_lock "uart"%string (tx_res γu) G4
                  0%nat true pj C (av - 10)%nat
                  ltac:(rewrite HG4a0; apply uw_addv_0)
                  ltac:(unfold uartwrite_stack in Hav; lia)
                  with "Hcg Ht Hpc Hlk Htok [Hown] Hcnt Hpay").
        { iApply (tx_res_intro γu ((l ++ [f i])%list) with "Hown"). }
        iIntros (CIDr2 Hsr2 MR2) "Hcg Hpc %HcsR2 Hcnt".
        iEval (rewrite HG4ra P72) in "Hpc".
        assert (HregsR2 : uw_loop_regs m0 MR2 (pa_stk sp0 10) buf n i).
        { apply (uw_loop_regs_cs m0 G4 MR2); [exact HcsR2|].
          apply (uw_loop_regs_cs m0 D2 G4); [exact HcsG4 | exact HD2regs]. }
        pose proof HregsR2 as HregsR2'.
        destruct HregsR2' as (Rsp & Rs1e & Rs2e & Rs3e & Rs4e & Rs5e & Rs6e & Rs7e & R24 & R25 & R26 & R27).
        (* --- +0x72  c.addiw s1,s1,1 --- *)
        iApply (wp_caddiw_s_sconf (mword_of_int (KernelSyms.uartwrite + 0x72)) Rs1
                  (mword_of_int 1 : mword 6) MR2 (av - 10)%nat true ltac:(nz) ltac:(rdok)
                  with "Hcg Hpc Hi72").
        iIntros (CIDa6 Hsa6) "Hcg Hpc". iEval (rgne) in "Hcg".
        set (G5 := <[Regidx Rs1 := regval_into_reg
            (sign_extend' 64 (subrange_vec_dec
               (add_vec (MR2 !!! Regidx Rs1)
                  (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6)))) 31 0))]> MR2).
        change (<[Regidx Rs1 := regval_into_reg
            (sign_extend' 64 (subrange_vec_dec
               (add_vec (MR2 !!! Regidx Rs1)
                  (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6)))) 31 0))]> MR2) with G5.
        iEval (rewrite P74) in "Hpc".
        assert (HG5s1 : G5 !!! Regidx Rs1 = (mword_of_int (Z.of_nat (S i)) : mword 64)).
        { rewrite /G5 upd_eq. unfold regval_into_reg. rewrite Rs1e.
          apply uw_addiw_p1. lia. }
        assert (HG5regs : uw_loop_regs m0 G5 (pa_stk sp0 10) buf n (S i)).
        { unfold uw_loop_regs. split_and!;
            first [ exact HG5s1
                  | (rewrite /G5 upd_ne; [| reg_neq]); assumption ]. }
        pose proof HG5regs as HG5regs'.
        destruct HG5regs' as (Gsp & Gs1 & Gs2 & Gs3 & Gs4 & Gs5 & Gs6 & Gs7 & G24 & G25 & G26 & G27).
        (* --- +0x74  c.j -> +0x46 --- *)
        iApply (wp_cj_s_sconf (mword_of_int (KernelSyms.uartwrite + 0x74))
                  (sign_extend' 21 (concat_vec (mword_of_int 2025 : mword 11) ('b"0")))
                  G5 (av - 10)%nat true ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc Hi74").
        iIntros (CIDa7 Hsa7). iApply bi.later_intro. iIntros "Hcg Hpc".
        iEval (rewrite Jback) in "Hpc".
        (* --- +0x46  bge s1,s3 --- *)
        assert (Hcmp : zopz0zKzJ_s (rget G5 Rs1) (rget G5 Rs3)
                       = Z.geb (Z.of_nat (S i)) (Z.of_nat n)).
        { rgne. rgne. rewrite Gs1 Gs3.
          apply (uw_geb_nn (Z.of_nat (S i)) (Z.of_nat n) ltac:(lia) ltac:(lia)). }
        destruct (Z.geb (Z.of_nat (S i)) (Z.of_nat n)) eqn:Hend.
        + (* the last byte: leave the loop *)
          assert (Hendn : S i = n).
          { rewrite Z.geb_leb in Hend. apply Z.leb_le in Hend. lia. }
          iApply (wp_bge_taken_s_sconf (mword_of_int (KernelSyms.uartwrite + 0x46))
                    (mword_of_int 48 : mword 13) Rs3 Rs1 G5 (av - 10)%nat true
                    ltac:(nz) ltac:(nz) Hcmp ltac:(vm_compute; reflexivity)
                    with "Hcg Hpc Hi46").
          iApply bi.later_intro. iIntros (CIDx Hsx) "Hcg Hpc".
          iEval (rewrite Jexit) in "Hpc".
          iDestruct (cpu_own_transport CIDa7 CIDx 0 true pj C true ltac:(wp_next_chain)
                       with "Hcnt") as "Hcnt".
          iDestruct "Hcont" as "[_ Hexit]".
          rewrite /uw_exit_cont.
          iSpecialize ("Hexit" $! CIDx with "[%]"); [wp_next_chain|].
          subst n.
          iApply ("Hexit" $! G5 with "[%] Hcg Hcnt Hpc Hpid Hsub' Hfull Hbuf").
          exact HG5regs.
        + (* more bytes: back to the head *)
          assert (Hendn : (S i < n)%nat).
          { rewrite Z.geb_leb in Hend. apply Z.leb_gt in Hend. lia. }
          iApply (wp_bge_fall_s_sconf (mword_of_int (KernelSyms.uartwrite + 0x46))
                    (mword_of_int 48 : mword 13) Rs3 Rs1 G5 (av - 10)%nat true
                    ltac:(nz) ltac:(nz) Hcmp with "Hcg Hpc Hi46").
          iIntros (CIDy Hsy) "Hcg Hpc".
          iEval (rewrite P4a) in "Hpc".
          iDestruct (cpu_own_transport CIDa7 CIDy 0 true pj C true ltac:(wp_next_chain)
                       with "Hcnt") as "Hcnt".
          iDestruct "Hcont" as "[Hnext _]".
          rewrite /uw_next_cont.
          iSpecialize ("Hnext" $! CIDy with "[%]"); [wp_next_chain|].
          iApply ("Hnext" $! G5 with "[%] [%] Hcg Hcnt Hpc Hpid Hsub' Hfull Hbuf").
          * exact Hendn.
          * exact HG5regs. }
    iSpecialize ("Turn" $! CID with "[%]"); [wp_next_chain|].
    iApply ("Turn" $! M with "[%] Hcg Hcnt Hpc Hpid Hfull Hbuf Hcont").
    exact Hregs.
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  THE LOOP: induction on the bytes still to go.                       *)
  (* ------------------------------------------------------------------ *)
  Lemma uw_iter `{GEN : GenId} (CID0 : CPU)
      (γl : gname) (γu : uart_names) (γv : disk_names)
      (γs : list gname) (j : nat) (γlp : gname)
      (m0 : regfile) (av : nat) (eb : bool) (C : iProp Σ)
      (sp0 buf : mword 64) (n : nat) (f : nat -> bv 8) (dq : dfrac)
      (pidv : mword 32) (dqp : dfrac) (k : nat) :
    (Z.of_nat n < 2 ^ 31)%Z ->
    (j < NPROC)%nat -> γs !! j = Some γlp ->
    (uartwrite_stack <= av)%nat ->
    eb = true ->
    forall i : nat, (i + S k)%nat = n ->
    ⊢ kernel_text -∗ dev_inv γu γv -∗ is_txlock γl γu -∗
      procs_inv γs -∗ panic_wp_any -∗
      uw_head (CID0 := CID0) γu j m0 av eb C sp0 buf n f dq pidv dqp i.
  Proof.
    intros Hn31 Hj Hjlp Hav Heb.
    induction k as [|k IH].
    - intros i Hik. iIntros "#Ht #Hdinv #Htxl #Hpinv #Hpanic".
      rewrite /uw_head.
      iIntros (CIDh Hsh M) "%Hregs Hcg Hcnt Hpc Hpid #Hsub Hfull Hbuf Hexit".
      iApply (uw_one (CID := CIDh) CID0 γl γu γv γs j γlp m0 M av eb C sp0 buf n f dq
                pidv dqp i ltac:(lia) Hn31 Hj Hjlp Hav Heb Hsh Hregs
                with "Ht Hdinv Htxl Hpinv Hpanic Hcg Hcnt Hpc Hpid Hsub Hfull Hbuf [Hexit]").
      iSplit.
      + (* the back edge is dead: this was the last byte *)
        rewrite /uw_next_cont. iIntros (CIDx Hsx M') "%Hlt". exfalso. lia.
      + iExact "Hexit".
    - intros i Hik. iIntros "#Ht #Hdinv #Htxl #Hpinv #Hpanic".
      rewrite /uw_head.
      iIntros (CIDh Hsh M) "%Hregs Hcg Hcnt Hpc Hpid #Hsub Hfull Hbuf Hexit".
      iApply (uw_one (CID := CIDh) CID0 γl γu γv γs j γlp m0 M av eb C sp0 buf n f dq
                pidv dqp i ltac:(lia) Hn31 Hj Hjlp Hav Heb Hsh Hregs
                with "Ht Hdinv Htxl Hpinv Hpanic Hcg Hcnt Hpc Hpid Hsub Hfull Hbuf [Hexit]").
      iSplit.
      + rewrite /uw_next_cont.
        iIntros (CIDx Hsx M') "%Hlt %Hregs' Hcg Hcnt Hpc Hpid #Hsub' Hfull Hbuf".
        iPoseProof (IH (S i) ltac:(lia) with "Ht Hdinv Htxl Hpinv Hpanic") as "Next".
        rewrite /uw_head.
        iSpecialize ("Next" $! CIDx with "[%]"); [wp_next_chain|].
        iApply ("Next" $! M' with "[%] Hcg Hcnt Hpc Hpid Hsub' Hfull Hbuf Hexit").
        exact Hregs'.
      + iExact "Hexit".
  Qed.

End UwBodies.

(* ===================================================================== *)

Section ProofUartwrite.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !irefslotG Σ}.
  Context `{!uartGhostG Σ, !diskGhostG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Local Ltac rgne :=
    rewrite rget_ne;
    [ | let H1 := fresh in let H2 := fresh in
        intro H1; injection H1 as H2; vm_compute in H2; congruence ].

  Lemma wp_uartwrite_sconf (γu : uart_names) (γv : disk_names)
      (γs : list gname) (j : nat) (γlp : gname) (γl : gname)
      (m : regfile) (av : nat) (eb : bool) (C : iProp Σ)
      (n : nat) (f : nat -> bv 8) (dq : dfrac) (b : bool)
      (pidv : mword 32) (dqp : dfrac)
    : wp_uartwrite_sconf_body γu γv γs j γlp γl m av eb C n f dq b pidv dqp.
  Proof.
    cbv beta delta [wp_uartwrite_sconf_body].
    intros pcE pj buf ret_tgt Hj Hjlp Ha1 Hn31 Hav Heb.
    iIntros "Hcg Hcnt #Ht Hpc #Hdinv #Htxl Hpid Hbuf #Hpinv #Hpanic Hcont".
    iDestruct (cpu_own_eb_agree with "Hcg Hcnt") as %Hbm.
    assert (Hbt : b = true) by (rewrite -Hbm; exact Heb).
    clear Hbm. subst b.
    assert (H231 : (2 ^ 31 = 2147483648)%Z) by (vm_compute; reflexivity).
    assert (H263 : (2 ^ 63 = 9223372036854775808)%Z) by (vm_compute; reflexivity).
    rewrite H231 in Hn31.
    pose (sp0 := (m !!! Regidx csp_rs1 : mword 64)).
    assert (Hspm : m !!! Regidx csp_rs1 = sp0) by reflexivity.
    set (spd := pa_stk sp0 10%nat).
    (* the empty sublist claim, out of the device invariant: the n = 0 path
       never takes the lock, so it never has a token to snapshot. *)
    iApply fupd_wp.
    iMod (uw_sent_sub_empty γu γv ⊤ ltac:(solve_ndisj) with "Hdinv") as "#Hsub0".
    iModIntro.
    iPoseProof (uwi_00 with "Ht") as "Hi00".
    iPoseProof (uwi_8c with "Ht") as "Hi8c".
    (* ============ +0x00  blez a1 ============ *)
    assert (Hcmp0 : zopz0zKzJ_s (zero_reg : mword 64) (rget m Ra1) = Z.geb 0 (Z.of_nat n)).
    { rgne. rewrite Ha1. apply uw_geb_s0. lia. }
    destruct (Z.geb 0 (Z.of_nat n)) eqn:Hb0z.
    - (* ======== n = 0: two instructions and out ======== *)
      assert (Hn0 : n = 0%nat).
      { rewrite Z.geb_leb in Hb0z. apply Z.leb_le in Hb0z. lia. }
      subst n.
      assert (Hal : eq_vec (access_vec_dec (add_vec (pcE : mword 64)
                      (sign_extend' 64 (mword_of_int 140 : mword 13))) 0) ('b"0") = true)
        by (vm_compute; reflexivity).
      iApply (wp_bge_x0_taken_s_sconf pcE (mword_of_int 140 : mword 13)
                Ra1 m av true ltac:(nz) ltac:(exact Hcmp0) Hal with "Hcg Hpc Hi00").
      iApply bi.later_intro. iIntros (CID1 Hs1) "Hcg Hpc".
      assert (Jret : add_vec (pcE : mword 64) (sign_extend' 64 (mword_of_int 140 : mword 13))
                     = mword_of_int (KernelSyms.uartwrite + 0x8c)) by pcw.
      iEval (rewrite Jret) in "Hpc".
      (* +0x8c  c.ret *)
      iApply (wp_cret_s_sconf (mword_of_int (KernelSyms.uartwrite + 0x8c)) Rra m av true ltac:(nz)
                with "Hcg Hpc Hi8c").
      iIntros (CID2 Hs2) "Hcg Hpc". iEval (rgne) in "Hpc".
      iDestruct (cpu_own_transport CID CID2 0 eb pj C true ltac:(wp_next_chain)
                   with "Hcnt") as "Hcnt".
      iSpecialize ("Hcont" $! CID2 with "[%]"); [wp_next_chain|].
      iApply ("Hcont" $! m with "[%] Hcg Hcnt Hpc Hbuf Hpid [Hsub0]").
      + apply callee_saved_refl.
      + iExact "Hsub0".
    - (* ======== n > 0: the prologue, the setup and the loop ======== *)
      assert (Hnpos : (0 < n)%nat).
      { rewrite Z.geb_leb in Hb0z. apply Z.leb_gt in Hb0z. lia. }
      iApply (wp_bge_x0_fall_s_sconf pcE (mword_of_int 140 : mword 13)
                Ra1 m av true ltac:(nz) ltac:(exact Hcmp0) with "Hcg Hpc Hi00").
      iIntros (CID1 Hs1) "Hcg Hpc".
      assert (P04 : add_vec_int (pcE : mword 64) 4 = mword_of_int (KernelSyms.uartwrite + 0x04)) by pcw.
      iEval (rewrite P04) in "Hpc".
      iPoseProof (uwi_04 with "Ht") as "Hi04". iPoseProof (uwi_06 with "Ht") as "Hi06".
      iPoseProof (uwi_08 with "Ht") as "Hi08". iPoseProof (uwi_0a with "Ht") as "Hi0a".
      iPoseProof (uwi_0c with "Ht") as "Hi0c". iPoseProof (uwi_0e with "Ht") as "Hi0e".
      iPoseProof (uwi_10 with "Ht") as "Hi10". iPoseProof (uwi_12 with "Ht") as "Hi12".
      iPoseProof (uwi_14 with "Ht") as "Hi14". iPoseProof (uwi_16 with "Ht") as "Hi16".
      iPoseProof (uwi_18 with "Ht") as "Hi18". iPoseProof (uwi_1a with "Ht") as "Hi1a".
      iPoseProof (uwi_1c with "Ht") as "Hi1c". iPoseProof (uwi_1e with "Ht") as "Hi1e".
      iPoseProof (uwi_20 with "Ht") as "Hi20". iPoseProof (uwi_24 with "Ht") as "Hi24".
      iPoseProof (uwi_28 with "Ht") as "Hi28". iPoseProof (uwi_2c with "Ht") as "Hi2c".
      iPoseProof (uwi_30 with "Ht") as "Hi30". iPoseProof (uwi_34 with "Ht") as "Hi34".
      iPoseProof (uwi_36 with "Ht") as "Hi36". iPoseProof (uwi_3a with "Ht") as "Hi3a".
      assert (P06 : add_vec_int (mword_of_int (KernelSyms.uartwrite + 0x04) : mword 64) 2 = mword_of_int (KernelSyms.uartwrite + 0x06)) by pcw.
      assert (P08 : add_vec_int (mword_of_int (KernelSyms.uartwrite + 0x06) : mword 64) 2 = mword_of_int (KernelSyms.uartwrite + 0x08)) by pcw.
      assert (P0a : add_vec_int (mword_of_int (KernelSyms.uartwrite + 0x08) : mword 64) 2 = mword_of_int (KernelSyms.uartwrite + 0x0a)) by pcw.
      assert (P0c : add_vec_int (mword_of_int (KernelSyms.uartwrite + 0x0a) : mword 64) 2 = mword_of_int (KernelSyms.uartwrite + 0x0c)) by pcw.
      assert (P0e : add_vec_int (mword_of_int (KernelSyms.uartwrite + 0x0c) : mword 64) 2 = mword_of_int (KernelSyms.uartwrite + 0x0e)) by pcw.
      assert (P10 : add_vec_int (mword_of_int (KernelSyms.uartwrite + 0x0e) : mword 64) 2 = mword_of_int (KernelSyms.uartwrite + 0x10)) by pcw.
      assert (P12 : add_vec_int (mword_of_int (KernelSyms.uartwrite + 0x10) : mword 64) 2 = mword_of_int (KernelSyms.uartwrite + 0x12)) by pcw.
      assert (P14 : add_vec_int (mword_of_int (KernelSyms.uartwrite + 0x12) : mword 64) 2 = mword_of_int (KernelSyms.uartwrite + 0x14)) by pcw.
      assert (P16 : add_vec_int (mword_of_int (KernelSyms.uartwrite + 0x14) : mword 64) 2 = mword_of_int (KernelSyms.uartwrite + 0x16)) by pcw.
      assert (P18 : add_vec_int (mword_of_int (KernelSyms.uartwrite + 0x16) : mword 64) 2 = mword_of_int (KernelSyms.uartwrite + 0x18)) by pcw.
      assert (P1a : add_vec_int (mword_of_int (KernelSyms.uartwrite + 0x18) : mword 64) 2 = mword_of_int (KernelSyms.uartwrite + 0x1a)) by pcw.
      assert (P1c : add_vec_int (mword_of_int (KernelSyms.uartwrite + 0x1a) : mword 64) 2 = mword_of_int (KernelSyms.uartwrite + 0x1c)) by pcw.
      assert (P1e : add_vec_int (mword_of_int (KernelSyms.uartwrite + 0x1c) : mword 64) 2 = mword_of_int (KernelSyms.uartwrite + 0x1e)) by pcw.
      assert (P20 : add_vec_int (mword_of_int (KernelSyms.uartwrite + 0x1e) : mword 64) 2 = mword_of_int (KernelSyms.uartwrite + 0x20)) by pcw.
      assert (P24 : add_vec_int (mword_of_int (KernelSyms.uartwrite + 0x20) : mword 64) 4 = mword_of_int (KernelSyms.uartwrite + 0x24)) by pcw.
      assert (P28 : add_vec_int (mword_of_int (KernelSyms.uartwrite + 0x24) : mword 64) 4 = mword_of_int (KernelSyms.uartwrite + 0x28)) by pcw.
      assert (P2c : add_vec_int (mword_of_int (KernelSyms.uartwrite + 0x28) : mword 64) 4 = mword_of_int (KernelSyms.uartwrite + 0x2c)) by pcw.
      assert (P30 : add_vec_int (mword_of_int (KernelSyms.uartwrite + 0x2c) : mword 64) 4 = mword_of_int (KernelSyms.uartwrite + 0x30)) by pcw.
      assert (P34 : add_vec_int (mword_of_int (KernelSyms.uartwrite + 0x30) : mword 64) 4 = mword_of_int (KernelSyms.uartwrite + 0x34)) by pcw.
      assert (P36 : add_vec_int (mword_of_int (KernelSyms.uartwrite + 0x34) : mword 64) 2 = mword_of_int (KernelSyms.uartwrite + 0x36)) by pcw.
      assert (P3a : add_vec_int (mword_of_int (KernelSyms.uartwrite + 0x36) : mword 64) 4 = mword_of_int (KernelSyms.uartwrite + 0x3a)) by pcw.
      (* ---- +0x04  c.addi16sp sp,-80 : the ten-slot frame ---- *)
      assert (Hpush : add_vec (m !!! Regidx csp_rs1)
                        (sign_extend' 64 (caddi16sp_imm (mword_of_int 59 : mword 6)))
                      = pa_stk (m !!! Regidx csp_rs1) 10%nat).
      { unfold pa_stk, add_vec_int. apply f_equal. apply bv_eq; vm_compute; reflexivity. }
      iApply (wp_caddi16sp_push_s_sconf (mword_of_int (KernelSyms.uartwrite + 0x04))
                (mword_of_int 59 : mword 6) m av 10%nat true
                ltac:(unfold uartwrite_stack in Hav; lia) Hpush with "Hcg Hpc Hi04").
      iIntros (CID2 Hs2) "Hcg Hframe Hpc".
      iEval (rewrite Hspm) in "Hframe".
      set (A0 := <[Regidx csp_rs1 := regval_into_reg
          (add_vec (m !!! Regidx csp_rs1)
             (sign_extend' 64 (caddi16sp_imm (mword_of_int 59 : mword 6))))]> m).
      change (<[Regidx csp_rs1 := regval_into_reg
          (add_vec (m !!! Regidx csp_rs1)
             (sign_extend' 64 (caddi16sp_imm (mword_of_int 59 : mword 6))))]> m) with A0.
      assert (HcspA0 : A0 !!! Regidx csp_rs1 = spd)
        by (rewrite /A0 upd_eq Hpush Hspm; reflexivity).
      iEval (rewrite P06) in "Hpc".
      iEval (rewrite stack_own_slots; cbn [seq]) in "Hframe".
      iDestruct "Hframe" as "(F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & _)".
      iDestruct "F1" as (v1) "H1". iDestruct "F2" as (v2) "H2".
      iDestruct "F3" as (v3) "H3". iDestruct "F4" as (v4) "H4".
      iDestruct "F5" as (v5) "H5". iDestruct "F6" as (v6) "H6".
      iDestruct "F7" as (v7) "H7". iDestruct "F8" as (v8) "H8".
      iDestruct "F9" as (v9) "H9". iDestruct "F10" as (v10) "H10".
      assert (Hb1 : add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 9 : mword 6) ('b"000"))) = pa_stk sp0 1)
        by (apply uw_slot_bridge; pcw).
      assert (Hb2 : add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 8 : mword 6) ('b"000"))) = pa_stk sp0 2)
        by (apply uw_slot_bridge; pcw).
      assert (Hb3 : add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 7 : mword 6) ('b"000"))) = pa_stk sp0 3)
        by (apply uw_slot_bridge; pcw).
      assert (Hb4 : add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 6 : mword 6) ('b"000"))) = pa_stk sp0 4)
        by (apply uw_slot_bridge; pcw).
      assert (Hb5 : add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000"))) = pa_stk sp0 5)
        by (apply uw_slot_bridge; pcw).
      assert (Hb6 : add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000"))) = pa_stk sp0 6)
        by (apply uw_slot_bridge; pcw).
      assert (Hb7 : add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000"))) = pa_stk sp0 7)
        by (apply uw_slot_bridge; pcw).
      assert (Hb8 : add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000"))) = pa_stk sp0 8)
        by (apply uw_slot_bridge; pcw).
      assert (Hb9 : add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) = pa_stk sp0 9)
        by (apply uw_slot_bridge; pcw).
      assert (HA0ra : A0 !!! Regidx Rra = m !!! Regidx Rra)
        by (rewrite /A0 upd_ne; [reflexivity | reg_neq]).
      assert (HA0s0 : A0 !!! Regidx Rs0 = m !!! Regidx Rs0)
        by (rewrite /A0 upd_ne; [reflexivity | reg_neq]).
      assert (HA0s1 : A0 !!! Regidx Rs1 = m !!! Regidx Rs1)
        by (rewrite /A0 upd_ne; [reflexivity | reg_neq]).
      assert (HA0s2 : A0 !!! Regidx Rs2 = m !!! Regidx Rs2)
        by (rewrite /A0 upd_ne; [reflexivity | reg_neq]).
      assert (HA0s3 : A0 !!! Regidx Rs3 = m !!! Regidx Rs3)
        by (rewrite /A0 upd_ne; [reflexivity | reg_neq]).
      assert (HA0s4 : A0 !!! Regidx Rs4 = m !!! Regidx Rs4)
        by (rewrite /A0 upd_ne; [reflexivity | reg_neq]).
      assert (HA0s5 : A0 !!! Regidx Rs5 = m !!! Regidx Rs5)
        by (rewrite /A0 upd_ne; [reflexivity | reg_neq]).
      assert (HA0s6 : A0 !!! Regidx Rs6 = m !!! Regidx Rs6)
        by (rewrite /A0 upd_ne; [reflexivity | reg_neq]).
      assert (HA0s7 : A0 !!! Regidx Rs7 = m !!! Regidx Rs7)
        by (rewrite /A0 upd_ne; [reflexivity | reg_neq]).
      (* ---- the nine saves (+0x06 .. +0x16) ---- *)
      iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.uartwrite + 0x06)) (mword_of_int 9 : mword 6) Rra
                A0 (av - 10)%nat v1 true with "Hcg Hpc Hi06 [H1]").
      { iEval (rewrite HcspA0 Hb1). iExact "H1". }
      iIntros (CID3 Hs3) "Hcg Hpc H1". iEval (rewrite HcspA0 Hb1) in "H1".
      iEval (rgne) in "H1". iEval (rewrite HA0ra) in "H1".
      iEval (rewrite P08) in "Hpc".
      iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.uartwrite + 0x08)) (mword_of_int 8 : mword 6) Rs0
                A0 (av - 10)%nat v2 true with "Hcg Hpc Hi08 [H2]").
      { iEval (rewrite HcspA0 Hb2). iExact "H2". }
      iIntros (CID4 Hs4) "Hcg Hpc H2". iEval (rewrite HcspA0 Hb2) in "H2".
      iEval (rgne) in "H2". iEval (rewrite HA0s0) in "H2".
      iEval (rewrite P0a) in "Hpc".
      iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.uartwrite + 0x0a)) (mword_of_int 7 : mword 6) Rs1
                A0 (av - 10)%nat v3 true with "Hcg Hpc Hi0a [H3]").
      { iEval (rewrite HcspA0 Hb3). iExact "H3". }
      iIntros (CID5 Hs5) "Hcg Hpc H3". iEval (rewrite HcspA0 Hb3) in "H3".
      iEval (rgne) in "H3". iEval (rewrite HA0s1) in "H3".
      iEval (rewrite P0c) in "Hpc".
      iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.uartwrite + 0x0c)) (mword_of_int 6 : mword 6) Rs2
                A0 (av - 10)%nat v4 true with "Hcg Hpc Hi0c [H4]").
      { iEval (rewrite HcspA0 Hb4). iExact "H4". }
      iIntros (CID6 Hs6) "Hcg Hpc H4". iEval (rewrite HcspA0 Hb4) in "H4".
      iEval (rgne) in "H4". iEval (rewrite HA0s2) in "H4".
      iEval (rewrite P0e) in "Hpc".
      iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.uartwrite + 0x0e)) (mword_of_int 5 : mword 6) Rs3
                A0 (av - 10)%nat v5 true with "Hcg Hpc Hi0e [H5]").
      { iEval (rewrite HcspA0 Hb5). iExact "H5". }
      iIntros (CID7 Hs7) "Hcg Hpc H5". iEval (rewrite HcspA0 Hb5) in "H5".
      iEval (rgne) in "H5". iEval (rewrite HA0s3) in "H5".
      iEval (rewrite P10) in "Hpc".
      iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.uartwrite + 0x10)) (mword_of_int 4 : mword 6) Rs4
                A0 (av - 10)%nat v6 true with "Hcg Hpc Hi10 [H6]").
      { iEval (rewrite HcspA0 Hb6). iExact "H6". }
      iIntros (CID8 Hs8) "Hcg Hpc H6". iEval (rewrite HcspA0 Hb6) in "H6".
      iEval (rgne) in "H6". iEval (rewrite HA0s4) in "H6".
      iEval (rewrite P12) in "Hpc".
      iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.uartwrite + 0x12)) (mword_of_int 3 : mword 6) Rs5
                A0 (av - 10)%nat v7 true with "Hcg Hpc Hi12 [H7]").
      { iEval (rewrite HcspA0 Hb7). iExact "H7". }
      iIntros (CID9 Hs9) "Hcg Hpc H7". iEval (rewrite HcspA0 Hb7) in "H7".
      iEval (rgne) in "H7". iEval (rewrite HA0s5) in "H7".
      iEval (rewrite P14) in "Hpc".
      iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.uartwrite + 0x14)) (mword_of_int 2 : mword 6) Rs6
                A0 (av - 10)%nat v8 true with "Hcg Hpc Hi14 [H8]").
      { iEval (rewrite HcspA0 Hb8). iExact "H8". }
      iIntros (CID10 Hs10) "Hcg Hpc H8". iEval (rewrite HcspA0 Hb8) in "H8".
      iEval (rgne) in "H8". iEval (rewrite HA0s6) in "H8".
      iEval (rewrite P16) in "Hpc".
      iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.uartwrite + 0x16)) (mword_of_int 1 : mword 6) Rs7
                A0 (av - 10)%nat v9 true with "Hcg Hpc Hi16 [H9]").
      { iEval (rewrite HcspA0 Hb9). iExact "H9". }
      iIntros (CID11 Hs11) "Hcg Hpc H9". iEval (rewrite HcspA0 Hb9) in "H9".
      iEval (rgne) in "H9". iEval (rewrite HA0s7) in "H9".
      iEval (rewrite P18) in "Hpc".
      iAssert (uw_saved sp0 m) with "[H1 H2 H3 H4 H5 H6 H7 H8 H9]" as "Hsv".
      { rewrite /uw_saved. iFrame "H1 H2 H3 H4 H5 H6 H7 H8 H9". }
      iAssert (uw_slot10 sp0) with "[H10]" as "Hs10". { by iExists v10. }
      iAssert (uw_full sp0 m) with "[Hsv Hs10]" as "Hfull".
      { rewrite /uw_full. iFrame "Hsv Hs10". }
      iAssert (uw_buf buf dq f n) with "[Hbuf]" as "Hbuf". { rewrite /uw_buf. iExact "Hbuf". }
      (* ---- +0x18  c.addi4spn s0,sp,80 ---- *)
      iApply (wp_caddi4spn_s_sconf (mword_of_int (KernelSyms.uartwrite + 0x18)) (Cregidx (mword_of_int 0))
                (mword_of_int 20 : mword 8) Rs0 A0 (av - 10)%nat true
                ltac:(vm_compute; reflexivity) ltac:(nz) ltac:(rdok)
                with "Hcg Hpc Hi18").
      iIntros (CID12 Hs12) "Hcg Hpc".
      set (A1 := <[Regidx Rs0 := regval_into_reg
          (add_vec (A0 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 20 : mword 8))))]> A0).
      change (<[Regidx Rs0 := regval_into_reg
          (add_vec (A0 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 20 : mword 8))))]> A0) with A1.
      iEval (rewrite P1a) in "Hpc".
      (* ---- +0x1a  c.mv s6,a0 ---- *)
      iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.uartwrite + 0x1a)) Rs6 Ra0
                A1 (av - 10)%nat true ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi1a").
      iIntros (CID13 Hs13) "Hcg Hpc". iEval (rgne) in "Hcg".
      set (A2 := <[Regidx Rs6 := regval_into_reg (add_vec zero_reg (A1 !!! Regidx Ra0))]> A1).
      change (<[Regidx Rs6 := regval_into_reg (add_vec zero_reg (A1 !!! Regidx Ra0))]> A1) with A2.
      iEval (rewrite P1c) in "Hpc".
      (* ---- +0x1c  c.mv s3,a1 ---- *)
      iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.uartwrite + 0x1c)) Rs3 Ra1
                A2 (av - 10)%nat true ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi1c").
      iIntros (CID14 Hs14) "Hcg Hpc". iEval (rgne) in "Hcg".
      set (A3 := <[Regidx Rs3 := regval_into_reg (add_vec zero_reg (A2 !!! Regidx Ra1))]> A2).
      change (<[Regidx Rs3 := regval_into_reg (add_vec zero_reg (A2 !!! Regidx Ra1))]> A2) with A3.
      iEval (rewrite P1e) in "Hpc".
      (* ---- +0x1e  c.li s1,0 ---- *)
      iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.uartwrite + 0x1e)) Rs1 (mword_of_int 0 : mword 6)
                (mword_of_int 0 : mword 64) A3 (av - 10)%nat true ltac:(nz) ltac:(rdok)
                ltac:(pcw) with "Hcg Hpc Hi1e").
      iIntros (CID15 Hs15) "Hcg Hpc".
      set (A4 := <[Regidx Rs1 := regval_into_reg (mword_of_int 0 : mword 64)]> A3).
      change (<[Regidx Rs1 := regval_into_reg (mword_of_int 0 : mword 64)]> A3) with A4.
      iEval (rewrite P20) in "Hpc".
      (* ---- +0x20/+0x24  s5 := &tx_chan ---- *)
      iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.uartwrite + 0x20)) Rs5 (mword_of_int 10 : mword 20)
                A4 (av - 10)%nat true ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi20").
      iIntros (CID16 Hs16) "Hcg Hpc".
      set (A5 := <[Regidx Rs5 := regval_into_reg
          (add_vec (mword_of_int (KernelSyms.uartwrite + 0x20) : mword 64) (auipc_off (mword_of_int 10 : mword 20)))]> A4).
      change (<[Regidx Rs5 := regval_into_reg
          (add_vec (mword_of_int (KernelSyms.uartwrite + 0x20) : mword 64) (auipc_off (mword_of_int 10 : mword 20)))]> A4) with A5.
      iEval (rewrite P24) in "Hpc".
      iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.uartwrite + 0x24)) Rs5 Rs5 (mword_of_int 2450 : mword 12)
                A5 (av - 10)%nat true ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi24").
      iIntros (CID17 Hs17) "Hcg Hpc". iEval (rgne) in "Hcg".
      set (A6 := <[Regidx Rs5 := regval_into_reg
          (add_vec (A5 !!! Regidx Rs5) (sign_extend' 64 (mword_of_int 2450 : mword 12)))]> A5).
      change (<[Regidx Rs5 := regval_into_reg
          (add_vec (A5 !!! Regidx Rs5) (sign_extend' 64 (mword_of_int 2450 : mword 12)))]> A5) with A6.
      iEval (rewrite P28) in "Hpc".
      (* ---- +0x28/+0x2c  s2 := &tx_lock ---- *)
      iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.uartwrite + 0x28)) Rs2 (mword_of_int 18 : mword 20)
                A6 (av - 10)%nat true ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi28").
      iIntros (CID18 Hs18) "Hcg Hpc".
      set (A7 := <[Regidx Rs2 := regval_into_reg
          (add_vec (mword_of_int (KernelSyms.uartwrite + 0x28) : mword 64) (auipc_off (mword_of_int 18 : mword 20)))]> A6).
      change (<[Regidx Rs2 := regval_into_reg
          (add_vec (mword_of_int (KernelSyms.uartwrite + 0x28) : mword 64) (auipc_off (mword_of_int 18 : mword 20)))]> A6) with A7.
      iEval (rewrite P2c) in "Hpc".
      iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.uartwrite + 0x2c)) Rs2 Rs2 (mword_of_int 2666 : mword 12)
                A7 (av - 10)%nat true ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi2c").
      iIntros (CID19 Hs19) "Hcg Hpc". iEval (rgne) in "Hcg".
      set (A8 := <[Regidx Rs2 := regval_into_reg
          (add_vec (A7 !!! Regidx Rs2) (sign_extend' 64 (mword_of_int 2666 : mword 12)))]> A7).
      change (<[Regidx Rs2 := regval_into_reg
          (add_vec (A7 !!! Regidx Rs2) (sign_extend' 64 (mword_of_int 2666 : mword 12)))]> A7) with A8.
      iEval (rewrite P30) in "Hpc".
      (* ---- +0x30/+0x34  s4 := &LSR ---- *)
      iApply (wp_lui_s_sconf (mword_of_int (KernelSyms.uartwrite + 0x30)) Rs4 (mword_of_int 65536 : mword 20)
                (luival (mword_of_int 65536 : mword 20)) A8 (av - 10)%nat true
                ltac:(nz) ltac:(rdok) eq_refl with "Hcg Hpc Hi30").
      iIntros (CID20 Hs20) "Hcg Hpc".
      set (A9 := <[Regidx Rs4 := regval_into_reg (luival (mword_of_int 65536 : mword 20))]> A8).
      change (<[Regidx Rs4 := regval_into_reg (luival (mword_of_int 65536 : mword 20))]> A8) with A9.
      iEval (rewrite P34) in "Hpc".
      iApply (wp_caddi_s_sconf (mword_of_int (KernelSyms.uartwrite + 0x34)) Rs4 (mword_of_int 5 : mword 6)
                A9 (av - 10)%nat true ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi34").
      iIntros (CID21 Hs21) "Hcg Hpc". iEval (rgne) in "Hcg".
      set (A10 := <[Regidx Rs4 := regval_into_reg
          (add_vec (A9 !!! Regidx Rs4) (sign_extend' 64 (sign_extend' 12 (mword_of_int 5 : mword 6))))]> A9).
      change (<[Regidx Rs4 := regval_into_reg
          (add_vec (A9 !!! Regidx Rs4) (sign_extend' 64 (sign_extend' 12 (mword_of_int 5 : mword 6))))]> A9) with A10.
      iEval (rewrite P36) in "Hpc".
      (* ---- +0x36  lui s7,0x10000 : &THR ---- *)
      iApply (wp_lui_s_sconf (mword_of_int (KernelSyms.uartwrite + 0x36)) Rs7 (mword_of_int 65536 : mword 20)
                (uart_pa 0) A10 (av - 10)%nat true ltac:(nz) ltac:(rdok)
                ltac:(apply bv_eq; vm_compute; reflexivity) with "Hcg Hpc Hi36").
      iIntros (CID22 Hs22) "Hcg Hpc".
      set (A11 := <[Regidx Rs7 := regval_into_reg (uart_pa 0)]> A10).
      change (<[Regidx Rs7 := regval_into_reg (uart_pa 0)]> A10) with A11.
      iEval (rewrite P3a) in "Hpc".
      (* ---- the loop's register invariant at entry ---- *)
      assert (HA11regs : uw_loop_regs m A11 spd buf n 0%nat).
      { unfold uw_loop_regs. split_and!.
        - rewrite /A11 upd_ne; [| reg_neq]. rewrite /A10 upd_ne; [| reg_neq].
          rewrite /A9 upd_ne; [| reg_neq]. rewrite /A8 upd_ne; [| reg_neq].
          rewrite /A7 upd_ne; [| reg_neq]. rewrite /A6 upd_ne; [| reg_neq].
          rewrite /A5 upd_ne; [| reg_neq]. rewrite /A4 upd_ne; [| reg_neq].
          rewrite /A3 upd_ne; [| reg_neq]. rewrite /A2 upd_ne; [| reg_neq].
          rewrite /A1 upd_ne; [| reg_neq]. exact HcspA0.
        - rewrite /A11 upd_ne; [| reg_neq]. rewrite /A10 upd_ne; [| reg_neq].
          rewrite /A9 upd_ne; [| reg_neq]. rewrite /A8 upd_ne; [| reg_neq].
          rewrite /A7 upd_ne; [| reg_neq]. rewrite /A6 upd_ne; [| reg_neq].
          rewrite /A5 upd_ne; [| reg_neq]. rewrite /A4 upd_eq. reflexivity.
        - rewrite /A11 upd_ne; [| reg_neq]. rewrite /A10 upd_ne; [| reg_neq].
          rewrite /A9 upd_ne; [| reg_neq]. rewrite /A8 upd_eq. rewrite /A7 upd_eq.
          rewrite /a_tx_lock. pcw.
        - rewrite /A11 upd_ne; [| reg_neq]. rewrite /A10 upd_ne; [| reg_neq].
          rewrite /A9 upd_ne; [| reg_neq]. rewrite /A8 upd_ne; [| reg_neq].
          rewrite /A7 upd_ne; [| reg_neq]. rewrite /A6 upd_ne; [| reg_neq].
          rewrite /A5 upd_ne; [| reg_neq]. rewrite /A4 upd_ne; [| reg_neq].
          rewrite /A3 upd_eq. rewrite uw_zero_reg_add.
          rewrite /A2 upd_ne; [| reg_neq]. rewrite /A1 upd_ne; [| reg_neq].
          rewrite /A0 upd_ne; [| reg_neq]. exact Ha1.
        - rewrite /A11 upd_ne; [| reg_neq]. rewrite /A10 upd_eq. rewrite /A9 upd_eq.
          unfold uart_pa. pcw.
        - rewrite /A11 upd_ne; [| reg_neq]. rewrite /A10 upd_ne; [| reg_neq].
          rewrite /A9 upd_ne; [| reg_neq]. rewrite /A8 upd_ne; [| reg_neq].
          rewrite /A7 upd_ne; [| reg_neq]. rewrite /A6 upd_eq. rewrite /A5 upd_eq.
          rewrite /a_tx_chan. pcw.
        - rewrite /A11 upd_ne; [| reg_neq]. rewrite /A10 upd_ne; [| reg_neq].
          rewrite /A9 upd_ne; [| reg_neq]. rewrite /A8 upd_ne; [| reg_neq].
          rewrite /A7 upd_ne; [| reg_neq]. rewrite /A6 upd_ne; [| reg_neq].
          rewrite /A5 upd_ne; [| reg_neq]. rewrite /A4 upd_ne; [| reg_neq].
          rewrite /A3 upd_ne; [| reg_neq]. rewrite /A2 upd_eq. rewrite uw_zero_reg_add.
          rewrite /A1 upd_ne; [| reg_neq]. rewrite /A0 upd_ne; [| reg_neq]. reflexivity.
        - rewrite /A11 upd_eq. reflexivity.
        - rewrite /A11 upd_ne; [| reg_neq]. rewrite /A10 upd_ne; [| reg_neq].
          rewrite /A9 upd_ne; [| reg_neq]. rewrite /A8 upd_ne; [| reg_neq].
          rewrite /A7 upd_ne; [| reg_neq]. rewrite /A6 upd_ne; [| reg_neq].
          rewrite /A5 upd_ne; [| reg_neq]. rewrite /A4 upd_ne; [| reg_neq].
          rewrite /A3 upd_ne; [| reg_neq]. rewrite /A2 upd_ne; [| reg_neq].
          rewrite /A1 upd_ne; [| reg_neq]. rewrite /A0 upd_ne; [| reg_neq]. reflexivity.
        - rewrite /A11 upd_ne; [| reg_neq]. rewrite /A10 upd_ne; [| reg_neq].
          rewrite /A9 upd_ne; [| reg_neq]. rewrite /A8 upd_ne; [| reg_neq].
          rewrite /A7 upd_ne; [| reg_neq]. rewrite /A6 upd_ne; [| reg_neq].
          rewrite /A5 upd_ne; [| reg_neq]. rewrite /A4 upd_ne; [| reg_neq].
          rewrite /A3 upd_ne; [| reg_neq]. rewrite /A2 upd_ne; [| reg_neq].
          rewrite /A1 upd_ne; [| reg_neq]. rewrite /A0 upd_ne; [| reg_neq]. reflexivity.
        - rewrite /A11 upd_ne; [| reg_neq]. rewrite /A10 upd_ne; [| reg_neq].
          rewrite /A9 upd_ne; [| reg_neq]. rewrite /A8 upd_ne; [| reg_neq].
          rewrite /A7 upd_ne; [| reg_neq]. rewrite /A6 upd_ne; [| reg_neq].
          rewrite /A5 upd_ne; [| reg_neq]. rewrite /A4 upd_ne; [| reg_neq].
          rewrite /A3 upd_ne; [| reg_neq]. rewrite /A2 upd_ne; [| reg_neq].
          rewrite /A1 upd_ne; [| reg_neq]. rewrite /A0 upd_ne; [| reg_neq]. reflexivity.
        - rewrite /A11 upd_ne; [| reg_neq]. rewrite /A10 upd_ne; [| reg_neq].
          rewrite /A9 upd_ne; [| reg_neq]. rewrite /A8 upd_ne; [| reg_neq].
          rewrite /A7 upd_ne; [| reg_neq]. rewrite /A6 upd_ne; [| reg_neq].
          rewrite /A5 upd_ne; [| reg_neq]. rewrite /A4 upd_ne; [| reg_neq].
          rewrite /A3 upd_ne; [| reg_neq]. rewrite /A2 upd_ne; [| reg_neq].
          rewrite /A1 upd_ne; [| reg_neq]. rewrite /A0 upd_ne; [| reg_neq]. reflexivity. }
      (* ---- +0x3a  c.j -> the loop head ---- *)
      iApply (wp_cj_s_sconf (mword_of_int (KernelSyms.uartwrite + 0x3a))
                (sign_extend' 21 (concat_vec (mword_of_int 8 : mword 11) ('b"0")))
                A11 (av - 10)%nat true ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi3a").
      iIntros (CID23 Hs23). iApply bi.later_intro. iIntros "Hcg Hpc".
      assert (Jhead : add_vec (mword_of_int (KernelSyms.uartwrite + 0x3a) : mword 64)
                        (sign_extend' 64 (sign_extend' 21 (concat_vec (mword_of_int 8 : mword 11) ('b"0"))))
                      = mword_of_int (KernelSyms.uartwrite + 0x4a)) by pcw.
      iEval (rewrite Jhead) in "Hpc".
      (* ============ the loop ============ *)
      iDestruct (cpu_own_transport CID CID23 0 eb pj C true ltac:(wp_next_chain)
                   with "Hcnt") as "Hcnt".
      iPoseProof (uw_iter CID γl γu γv γs j γlp m av eb C sp0 buf n f dq
                    pidv dqp (n - 1)%nat ltac:(lia) Hj Hjlp Hav Heb 0%nat ltac:(lia)
                    with "Ht Hdinv Htxl Hpinv Hpanic") as "Iter".
      rewrite /uw_head.
      iSpecialize ("Iter" $! CID23 with "[%]"); [wp_next_chain|].
      iApply ("Iter" $! A11 with "[%] Hcg Hcnt Hpc Hpid Hsub0 Hfull Hbuf [Hcont]").
      { exact HA11regs. }
      (* ============ the loop's exit: +0x76 -> the epilogue ============ *)
      rewrite /uw_exit_cont.
      iIntros (CIDx Hsx M') "%Hregs' Hcg Hcnt Hpc Hpid #Hout Hfull Hbuf".
      iDestruct "Hfull" as "(Hsv & Hs10)".
      pose proof Hregs' as Hregs''.
      destruct Hregs'' as (Wsp & Ws1 & Ws2 & Ws3 & Ws4 & Ws5 & Ws6 & Ws7 & W24 & W25 & W26 & W27).
      iApply (uw_tail (CID := CIDx) CID γu j m M' av eb C sp0 (uw_bytes f n)
                (uw_buf buf dq f n) pidv dqp
                ltac:(unfold uw_tail_regs; split_and!; assumption) Hspm Hav Heb
                ltac:(wp_next_chain)
                with "Ht Hcg Hcnt Hpc Hpid Hout Hsv Hs10 Hbuf [Hcont]").
      rewrite /uw_ret.
      iIntros (CIDz Hsz mf) "%Hcs Hcg Hcnt Hpc Hbuf Hpid #Hout2".
      iSpecialize ("Hcont" $! CIDz with "[%]"); [wp_next_chain|].
      iApply ("Hcont" $! mf with "[%] Hcg Hcnt Hpc [Hbuf] Hpid [Hout2]").
      + exact Hcs.
      + rewrite /uw_buf. iExact "Hbuf".
      + iExact "Hout2".
  Qed.

End ProofUartwrite.

End UartwriteProof.
