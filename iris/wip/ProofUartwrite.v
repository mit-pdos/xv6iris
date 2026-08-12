(* ProofUartwrite.v -- the whole-function WP for xv6's uartwrite() after
   upstream ae96fd0 rewrote the transmit path.

     void uartwrite(char buf[], int n) {
       acquiresleep(&tx_lock);
       int i = 0;
       while (i < n) {
         sleep_prepare(&tx_chan);
         if (ReadReg(LSR) & LSR_TX_IDLE) { WriteReg(THR, buf[i]); i += 1; }
         else                            { sleep(); }
       }
       releasesleep(&tx_lock);
     }

   *** STATUS: WORK IN PROGRESS.  This file currently contains the
   DEFINITIONAL LAYER ONLY -- the pure arithmetic helpers, the two register
   predicates and the frame / continuation [iProp]s.  The three body lemmas
   ([uw_tail], [uw_one], [uw_iter]) and [wp_uartwrite_sconf] are NOT here yet;
   the block comment at the foot of the file is the complete instruction-level
   map and proof plan they should be written against, so the next attempt does
   not have to re-derive any of it.  Nothing below has been through [coqc]
   (the tree was being rebuilt); expect the usual spelling churn, not
   structural surprises. ***

   WHAT CHANGED FROM THE PRE-ae96fd0 PROOF, in one paragraph.  The lock is a
   SLEEPLOCK, so there is no [push_off]: the whole function runs at
   [cpu_own 0 eb pj C b] and at the SIE index [b], which [cpu_own_eb_agree]
   pins to [true] from the contract's [eb = true].  That deletes every
   [wp_next_off] / [trap_res] / [arm_pay] move the old proof was full of, and
   replaces them with an ordinary [wp_next]-per-leaf discipline (ProofUartintr
   after the same bump is the worked example).  The THR store is no longer
   licensed by the [tx_busy] flag but by the writer's OWN LSR poll two
   instructions earlier -- uartputc_sync's route, [uart_tx_poll_thre] inside
   [WpSconfUartAccess.wp_uart_lsr_read_ea_s_sconf] -- and the flag, the cell
   and the whole [tx_res] certificate are gone ([tx_res γu] is now just
   [∃ l, uart_tx_own γu l]).  The frame shrank from ten slots to eight and the
   shrink-wrapped set changed from five registers to four.

   A functor over ACQUIRESLEEP / RELEASESLEEP / SLEEP / SLEEP_PREPARE / UART. *)
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
Require Import DiskPtsto WpUart.
Require Import SpecUart WpSconfUartAccess.
Require Import UartTxInv.
Require Import SleepLock.
Require Import SpecPanic.
Require Import SchedCtx.
Require Import FdSlots.
Require Import SpecAcquiresleep SpecReleasesleep SpecSleep SpecSleepPrepare.
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

(* THE FRAME IS EIGHT SLOTS NOW (the prologue is [c.addi16sp sp,-64], i.e.
   [caddi16sp_imm 60]; it used to be ten).  A [c.sdsp]/[c.ldsp] displacement
   off the pushed sp names slot [8 - imm6] counted down from the ENTRY sp. *)
Lemma uw_slot_bridge (X : mword 64) (o : mword 64) (k : nat) :
  add_vec (mword_of_int (- (8 * Z.of_nat 8%nat))) o = mword_of_int (- (8 * Z.of_nat k)) ->
  add_vec (pa_stk X 8%nat) o = pa_stk X k.
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

(* the [blez s2] at +0x1c *)
Lemma uw_geb_s0 (b : Z) : (- 2 ^ 63 <= b < 2 ^ 63)%Z ->
  zopz0zKzJ_s (zero_reg : mword 64) (mword_of_int b : mword 64) = Z.geb 0 b.
Proof.
  intro Hb. unfold zopz0zKzJ_s.
  assert (Hz : sint (zero_reg : mword 64) = 0%Z) by (vm_compute; reflexivity).
  rewrite Hz (uw_sint_moi b Hb). reflexivity.
Qed.

(* THE LOOP TEST IS A TWO-REGISTER [bge s1,s2] NOW (+0x42), not a [beq] on
   two cursors -- the C compares the INDEX with the COUNT rather than a
   moving pointer with its end, so [ByteCursor.pa_add_eqb] has no role here
   and this is the fact that replaces it. *)
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

(* the byte address is computed as [add a5,s5,s1] -- base PLUS INDEX, both
   held in registers -- so this is the bridge the +0x56 leaf's [wval] wants. *)
Lemma uw_pa_add_n (p : mword 64) (k : nat) :
  add_vec p (mword_of_int (Z.of_nat k)) = pa_add p k.
Proof. reflexivity. Qed.

(* a5's compressed-register index (the [c.beqz] at +0x54) *)
Lemma uw_cr7 : creg2reg_idx (Cregidx (mword_of_int 7)) = Regidx (mword_of_int 15 : mword 5).
Proof. vm_compute. reflexivity. Qed.

(* ---- the [c.addiw s1,s1,1] at +0x62 ---------------------------------- *)
(* i += 1 on a 32-bit int held in a 64-bit register: the ADDIW truncates to
   32 bits and sign-extends back, which is the identity on [0 <= i < 2^31 - 1].
   The decrement twin of this is ProofSafestrcpy's [ssc_addiw_m1]; the proof
   below is that one with the sign-extended [-1] replaced by a literal [1]
   (so the [Z.mod_add] step disappears). *)
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
(* WHAT THE LOOP KEEPS IN REGISTERS, and it is a different set from the old
   body: gcc now keeps the COUNT and the INDEX (s2, s1) rather than a pair of
   pointers, and the three constants it hoists are the wait channel, the LSR
   address and the THR address.  [a_tx_busy] and [a_tx_lock] are not among
   them -- the flag no longer exists and the lock address is rematerialized at
   the release. *)
Definition uw_loop_regs (m0 M : regfile) (spd buf : mword 64) (n i : nat) : Prop :=
  M !!! Regidx csp_rs1 = spd /\
  M !!! Regidx Rs1 = (mword_of_int (Z.of_nat i) : mword 64) /\
  M !!! Regidx Rs2 = (mword_of_int (Z.of_nat n) : mword 64) /\
  M !!! Regidx Rs3 = uart_pa 5 /\
  M !!! Regidx Rs4 = a_tx_chan /\
  M !!! Regidx Rs5 = buf /\
  M !!! Regidx Rs6 = uart_pa 0 /\
  M !!! Regidx Rs7 = m0 !!! Regidx Rs7 /\
  M !!! Regidx Rs8 = m0 !!! Regidx Rs8 /\
  M !!! Regidx Rs9 = m0 !!! Regidx Rs9 /\
  M !!! Regidx Rs10 = m0 !!! Regidx Rs10 /\
  M !!! Regidx Rs11 = m0 !!! Regidx Rs11.

(* ...and what the release / epilogue needs: every callee-saved register
   except the four still sitting in the frame (ra, s0, s2, s5). *)
Definition uw_tail_regs (m0 M : regfile) (spd : mword 64) : Prop :=
  M !!! Regidx csp_rs1 = spd /\
  M !!! Regidx Rs1 = m0 !!! Regidx Rs1 /\
  M !!! Regidx Rs3 = m0 !!! Regidx Rs3 /\
  M !!! Regidx Rs4 = m0 !!! Regidx Rs4 /\
  M !!! Regidx Rs6 = m0 !!! Regidx Rs6 /\
  M !!! Regidx Rs7 = m0 !!! Regidx Rs7 /\
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

Lemma uw_tail_regs_cs (m0 M M' : regfile) (spd : mword 64) :
  callee_saved M M' -> uw_tail_regs m0 M spd -> uw_tail_regs m0 M' spd.
Proof.
  intros Hcs (H1 & H9 & H19 & H20 & H22 & H23 & H24 & H25 & H26 & H27).
  unfold uw_tail_regs.
  repeat first
    [ split
    | rewrite (callee_saved_lookup Hcs csp_rs1 ltac:(vm_compute; reflexivity))
    | rewrite (callee_saved_lookup Hcs (mword_of_int 9) ltac:(vm_compute; reflexivity))
    | rewrite (callee_saved_lookup Hcs (mword_of_int 19) ltac:(vm_compute; reflexivity))
    | rewrite (callee_saved_lookup Hcs (mword_of_int 20) ltac:(vm_compute; reflexivity))
    | rewrite (callee_saved_lookup Hcs (mword_of_int 22) ltac:(vm_compute; reflexivity))
    | rewrite (callee_saved_lookup Hcs (mword_of_int 23) ltac:(vm_compute; reflexivity))
    | rewrite (callee_saved_lookup Hcs (mword_of_int 24) ltac:(vm_compute; reflexivity))
    | rewrite (callee_saved_lookup Hcs (mword_of_int 25) ltac:(vm_compute; reflexivity))
    | rewrite (callee_saved_lookup Hcs (mword_of_int 26) ltac:(vm_compute; reflexivity))
    | rewrite (callee_saved_lookup Hcs (mword_of_int 27) ltac:(vm_compute; reflexivity))
    | assumption ].
Qed.

(* the accumulated output claim, and its one-byte step.  UNCHANGED by the
   bump: uartwrite still sleeps between bytes, so the honest claim is still a
   SUBLIST of the accepted trace ([UartTxInv.uart_sent_sub]). *)
Definition uw_bytes (f : nat -> bv 8) (i : nat) : list (bv 8) := f <$> seq 0 i.

Lemma uw_bytes_snoc (f : nat -> bv 8) (i : nat) :
  uw_bytes f (S i) = (uw_bytes f i ++ [f i])%list.
Proof. rewrite /uw_bytes seq_S fmap_app. reflexivity. Qed.

(* ===================================================================== *)

Section UwProps.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !irefslotG Σ}.
  Context `{!uartGhostG Σ, !diskGhostG Σ}.

  (* ra/s0/s2/s5, saved unconditionally in the prologue (+0x02..+0x08) *)
  Definition uw_saved (sp0 : mword 64) (m0 : regfile) : iProp Σ :=
    (pa_stk sp0 1 ↦₈ (m0 !!! Regidx Rra) ∗
     pa_stk sp0 2 ↦₈ (m0 !!! Regidx Rs0) ∗
     pa_stk sp0 4 ↦₈ (m0 !!! Regidx Rs2) ∗
     pa_stk sp0 7 ↦₈ (m0 !!! Regidx Rs5))%I.

  (* s1/s3/s4/s6, SHRINK-WRAPPED onto the n > 0 path (+0x20..+0x26).  FOUR
     registers now, not five, and a different four. *)
  Definition uw_saved4 (sp0 : mword 64) (m0 : regfile) : iProp Σ :=
    (pa_stk sp0 3 ↦₈ (m0 !!! Regidx Rs1) ∗
     pa_stk sp0 5 ↦₈ (m0 !!! Regidx Rs3) ∗
     pa_stk sp0 6 ↦₈ (m0 !!! Regidx Rs4) ∗
     pa_stk sp0 8 ↦₈ (m0 !!! Regidx Rs6))%I.

  (* the same four slots at UNKNOWN contents: what the n = 0 path has, and
     what the two paths agree on at the join (+0x6e). *)
  Definition uw_gap4 (sp0 : mword 64) : iProp Σ :=
    ((∃ w : mword 64, pa_stk sp0 3 ↦₈ w) ∗ (∃ w : mword 64, pa_stk sp0 5 ↦₈ w) ∗
     (∃ w : mword 64, pa_stk sp0 6 ↦₈ w) ∗ (∃ w : mword 64, pa_stk sp0 8 ↦₈ w))%I.

  Lemma uw_saved4_gap sp0 m0 : uw_saved4 sp0 m0 -∗ uw_gap4 sp0.
  Proof.
    iIntros "(H3 & H5 & H6 & H8)". rewrite /uw_gap4.
    iSplitL "H3"; [by iExists _|]. iSplitL "H5"; [by iExists _|].
    iSplitL "H6"; [by iExists _|]. by iExists _.
  Qed.

  (* THE FRAME IS EXACTLY THE EIGHT SLOTS -- there is no tenth-slot leftover
     to carry, which is one bookkeeping item fewer than the old proof. *)
  Lemma uw_frame_stack_own sp0 m0 :
    uw_saved sp0 m0 -∗ uw_gap4 sp0 -∗ stack_own sp0 8.
  Proof.
    iIntros "(H1 & H2 & H4 & H7) (H3 & H5 & H6 & H8)".
    rewrite stack_own_slots. cbn [seq].
    iSplitL "H1"; [by iExists _|]. iSplitL "H2"; [by iExists _|].
    iSplitL "H3"; [by iExact "H3"|]. iSplitL "H4"; [by iExists _|].
    iSplitL "H5"; [by iExact "H5"|]. iSplitL "H6"; [by iExact "H6"|].
    iSplitL "H7"; [by iExists _|]. iSplitL "H8"; [by iExact "H8"|]. done.
  Qed.

  Definition uw_buf (buf : mword 64) (dq : dfrac) (f : nat -> bv 8) (n : nat) : iProp Σ :=
    ([∗ list] k0 ∈ seq 0 n, (pa_add buf k0) ↦ₘ{dq} f k0)%I.

  Definition uw_full (sp0 : mword 64) (m0 : regfile) : iProp Σ :=
    (uw_saved sp0 m0 ∗ uw_saved4 sp0 m0)%I.

  (* WHAT THE HOLDER CARRIES ROUND THE LOOP.  [acquiresleep] hands out three
     things and the caller's pid cell comes back with them; all four have to
     survive every park and reach [releasesleep] (the pid cell only has to
     reach the POSTCONDITION -- releasesleep does not want it). *)
  Definition uw_hold (γsl : gname) (pj : mword 64) (pidv : mword 32) (dqp : dfrac) : iProp Σ :=
    (sleeplocked γsl ∗ sl_pid a_tx_lock ↦₄ pidv ∗ p_pid pj ↦₄{dqp} pidv)%I.

  (* ------------------------------------------------------------------ *)
  (*  The joins, each a [wp_next] at an explicit anchor.                  *)
  (*                                                                      *)
  (*  THE LOOP HEAD IS +0x46 (the [c.mv a0,s4] that sets up               *)
  (*  [sleep_prepare]'s argument), NOT the loop TEST: gcc rotated the      *)
  (*  loop, so the test [bge s1,s2] sits at +0x42 and is reached from two  *)
  (*  places with two DIFFERENT indices (from +0x64 with [S i] after a     *)
  (*  byte, and from sleep's return with [i] unchanged).  Handling +0x42   *)
  (*  inline in each arm is therefore right; only +0x46 is a real join.    *)
  (* ------------------------------------------------------------------ *)

  (* the byte loop's back edge: another byte went out, and there is at least
     one more to go, so control is at +0x46 again with the index bumped *)
  Definition uw_next_cont `{GEN : GenId} (CID0 : CPU) (γsl : gname) (γu : uart_names)
      (j : nat) (m0 : regfile) (av : nat) (eb : bool) (C : iProp Σ)
      (sp0 buf : mword 64) (n : nat) (f : nat -> bv 8) (dq : dfrac)
      (pidv : mword 32) (dqp : dfrac) (i : nat) : iProp Σ :=
    (wp_next (CID0 := CID0) true (proc_addr j) (fun (CID : CpuId) =>
       ∀ M' : regfile,
       ⌜ (S i < n)%nat ⌝ -∗
       ⌜ uw_loop_regs m0 M' (pa_stk sp0 8) buf n (S i) ⌝ -∗
       sie_cap_gpr M' (av - 8)%nat true (proc_addr j) -∗
       cpu_own 0%nat eb (proc_addr j) C true -∗
       pc_is (mword_of_int (KernelSyms.uartwrite + 0x46)) -∗
       uw_hold γsl (proc_addr j) pidv dqp -∗ tx_res γu -∗
       uart_sent_sub γu (uw_bytes f (S i)) -∗
       uw_full sp0 m0 -∗ uw_buf buf dq f n -∗
       WP (Loop : expr riscv_lang)))%I.

  (* the loop's exit: [i = n], control at the four shrink-wrapped restores *)
  Definition uw_exit_cont `{GEN : GenId} (CID0 : CPU) (γsl : gname) (γu : uart_names)
      (j : nat) (m0 : regfile) (av : nat) (eb : bool) (C : iProp Σ)
      (sp0 buf : mword 64) (n : nat) (f : nat -> bv 8) (dq : dfrac)
      (pidv : mword 32) (dqp : dfrac) : iProp Σ :=
    (wp_next (CID0 := CID0) true (proc_addr j) (fun (CID : CpuId) =>
       ∀ M' : regfile,
       ⌜ uw_loop_regs m0 M' (pa_stk sp0 8) buf n n ⌝ -∗
       sie_cap_gpr M' (av - 8)%nat true (proc_addr j) -∗
       cpu_own 0%nat eb (proc_addr j) C true -∗
       pc_is (mword_of_int (KernelSyms.uartwrite + 0x66)) -∗
       uw_hold γsl (proc_addr j) pidv dqp -∗ tx_res γu -∗
       uart_sent_sub γu (uw_bytes f n) -∗
       uw_full sp0 m0 -∗ uw_buf buf dq f n -∗
       WP (Loop : expr riscv_lang)))%I.

  (* the loop head at +0x46, ENTERED at whatever hart the last park landed on *)
  Definition uw_head `{GEN : GenId} (CID0 : CPU) (γsl : gname) (γu : uart_names)
      (j : nat) (m0 : regfile) (av : nat) (eb : bool) (C : iProp Σ)
      (sp0 buf : mword 64) (n : nat) (f : nat -> bv 8) (dq : dfrac)
      (pidv : mword 32) (dqp : dfrac) (i : nat) : iProp Σ :=
    (wp_next (CID0 := CID0) true (proc_addr j) (fun (CID : CpuId) =>
       ∀ M : regfile,
       ⌜ uw_loop_regs m0 M (pa_stk sp0 8) buf n i ⌝ -∗
       sie_cap_gpr M (av - 8)%nat true (proc_addr j) -∗
       cpu_own 0%nat eb (proc_addr j) C true -∗
       pc_is (mword_of_int (KernelSyms.uartwrite + 0x46)) -∗
       uw_hold γsl (proc_addr j) pidv dqp -∗ tx_res γu -∗
       uart_sent_sub γu (uw_bytes f i) -∗
       uw_full sp0 m0 -∗ uw_buf buf dq f n -∗
       uw_exit_cont CID0 γsl γu j m0 av eb C sp0 buf n f dq pidv dqp -∗
       WP (Loop : expr riscv_lang)))%I.

  (* the tail's own continuation: uartwrite's postcondition, at ANY hart *)
  Definition uw_ret `{GEN : GenId} (CID0 : CPU) (γu : uart_names)
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

(* =====================================================================
   THE PROOF PLAN.  Everything below this line is what the next attempt
   should write; nothing in it needs re-deriving from the dump.

   ---- 1.  THE IMAGE, INSTRUCTION BY INSTRUCTION ----------------------
   uartwrite @ 0x800008d6, 134 bytes, 8-slot (64-byte) frame.  Decodes are
   CodeUartwrite.v's [uwi_<off>]; every immediate below is copied from there
   and has already been checked against kernel.asm.

     +0x00  c.addi16sp sp,-64        caddi16sp_imm 60      push 8 slots
     +0x02  c.sdsp  ra,56(sp)        imm6 7  -> slot 1
     +0x04  c.sdsp  s0,48(sp)        imm6 6  -> slot 2
     +0x06  c.sdsp  s2,32(sp)        imm6 4  -> slot 4
     +0x08  c.sdsp  s5,8(sp)         imm6 1  -> slot 7
     +0x0a  c.addi4spn s0,sp,64      caddi4spn_imm 16
     +0x0c  c.mv    s5,a0            s5 := buf
     +0x0e  c.mv    s2,a1            s2 := n
     +0x10  auipc   a0,0x12
     +0x14  addi    a0,a0,2666       a0 := &tx_lock (0x80012350)
     +0x18  jal     ra,acquiresleep  imm21 13844
     +0x1c  bge     zero,s2,+0x6e    imm13 82   ("blez s2": n <= 0)
     +0x20  c.sdsp  s1,40(sp)        imm6 5  -> slot 3   \
     +0x22  c.sdsp  s3,24(sp)        imm6 3  -> slot 5    | SHRINK-WRAPPED
     +0x24  c.sdsp  s4,16(sp)        imm6 2  -> slot 6    | onto n > 0
     +0x26  c.sdsp  s6,0(sp)         imm6 0  -> slot 8   /
     +0x28  c.li    s1,0             i := 0
     +0x2a  auipc   s4,0xa
     +0x2e  addi    s4,s4,2408       s4 := &tx_chan (0x8000a268)
     +0x32  lui     s3,0x10000
     +0x36  c.addi  s3,s3,5          s3 := &LSR   (uart_pa 5)
     +0x38  lui     s6,0x10000       s6 := &THR   (uart_pa 0)
     +0x3c  c.j     +0x46            imm11 5      enter the loop at its HEAD
     +0x3e  jal     ra,sleep         imm21 5636   <- the park arm
     +0x42  bge     s1,s2,+0x66      imm13 36     <- the TEST (two entries)
     +0x46  c.mv    a0,s4                         <- the loop HEAD
     +0x48  jal     ra,sleep_prepare imm21 5566
     +0x4c  lbu     a5,0(s3)                      <- the writer's OWN poll
     +0x50  andi    a5,a5,32
     +0x54  c.beqz  a5,+0x3e         imm8 245     THRE clear -> sleep
     +0x56  add     a5,s5,s1         a5 := buf + i
     +0x5a  lbu     a5,0(a5)         a5 := buf[i]
     +0x5e  sb      a5,0(s6)         THR <- buf[i]
     +0x62  c.addiw s1,s1,1          i += 1
     +0x64  c.j     +0x42            imm11 2031
     +0x66  c.ldsp  s1,40(sp)        \
     +0x68  c.ldsp  s3,24(sp)         | the four shrink-wrapped restores
     +0x6a  c.ldsp  s4,16(sp)         |
     +0x6c  c.ldsp  s6,0(sp)         /
     +0x6e  auipc   a0,0x12                       <- BOTH PATHS JOIN HERE
     +0x72  addi    a0,a0,2572       a0 := &tx_lock
     +0x76  jal     ra,releasesleep  imm21 13834
     +0x7a  c.ldsp  ra,56(sp)
     +0x7c  c.ldsp  s0,48(sp)
     +0x7e  c.ldsp  s2,32(sp)
     +0x80  c.ldsp  s5,8(sp)
     +0x82  c.addi16sp sp,64         caddi16sp_imm 4
     +0x84  c.ret

   ---- 2.  CONTROL FLOW ------------------------------------------------
   The loop is ROTATED: the head is +0x46 and the test is +0x42.

     entry --acquiresleep--> +0x1c --n<=0--> +0x6e (release, return)
                                  \--n>0--> +0x20..+0x3a --c.j--> +0x46
     +0x46 -> sleep_prepare -> poll -> beqz
                | THRE clear : +0x3e jal sleep -> returns at +0x42
                |              +0x42 bge i,n : i < n so FALL -> +0x46   (SAME i)
                \ THRE set   : +0x56..+0x62 push the byte, i := i+1
                               +0x64 c.j -> +0x42
                               +0x42 bge (i+1),n :
                                   S i = n -> TAKEN -> +0x66 (exit)
                                   S i < n -> FALL  -> +0x46             (S i)

   So: an iLoeb at +0x46 for the UNBOUNDED sleep retry at a fixed [i], nested
   inside a [nat] INDUCTION on the bytes remaining -- the same two-level shape
   as the old proof, but the two loops now share a head instead of nesting one
   inside the other's body, and there is no separate [Body] iAssert (only ONE
   edge reaches +0x56, so the old proof's reason for that iAssert is gone).

   ---- 3.  THE INDEX AND THE LEVEL -------------------------------------
   [cpu_own_eb_agree] on the entry resources with [lvl = 0] and the contract's
   [eb = true] gives [b = true] (as in the old proof).  A SLEEPLOCK does not
   push_off, so the level stays 0 and the index stays [true] for the WHOLE
   body: there is no [wp_next_off] anywhere, no [trap_res] in the stack count,
   and no [arm_pay].  Every leaf therefore yields a fresh hart -- follow
   ProofUartintr.v (post-bump) for the [cpu_own_transport] /
   [<cont>_shift] discipline, not the old ProofUartwrite.

   Stack: push 8, so every callee runs at [av - 8].  With
   [uartwrite_stack = 34] that is >= 26, which is exactly acquiresleep's floor
   (releasesleep 22, sleep 20, sleep_prepare 14).

   ---- 4.  THE FOUR CALLS ----------------------------------------------
   * acquiresleep (SpecAcquiresleep.wp_acquiresleep_sconf):
       γs j γl γsl "uart" (tx_res γu) M pidv (av-8) eb C dq b
       premises  (j < NPROC), (26 <= av-8)
       in   sie_cap_gpr, cpu_own 0 eb pj C true,
            trap_csrs_ext true = emp, cpu_claim_ext true pj = emp  (supply []
            and close with [done] -- both reduce definitionally at [eb=true]),
            kernel_text, pc_is, is_sleeplock (from [is_txlock_lock]),
            panic_wp_any, p_pid pj |->4{dqp} pidv, procs_inv
       out  wp_next TRUE pj, then sleeplocked γsl, sl_pid slk |->4 pidv,
            tx_res γu, p_pid pj |->4{dqp} pidv
       [slk] is [M !!! Regidx Ra0], which the call site proves = [a_tx_lock].
   * sleep_prepare (SpecSleepPrepare.wp_sleep_prepare_sconf):
       γs j γlp M (av-8) 0 eb C true
       premises  (j < NPROC), γs !! j = Some γlp,
                 eq_vec a_tx_chan zero_reg = false   ([vm_compute]),
                 (0 + 1 < 2^31), (14 <= av-8)
       POSTCONDITION IS EMPTY apart from the register/level bundle.
   * sleep (SpecSleep.wp_sleep_sconf): γs j γlp M (av-8) eb C
       premises  (j < NPROC), γs !! j = Some γlp, (20 <= av-8)
       needs cpu_own 0 eb pj C eb and the two _ext's (emp at eb = true);
       crossing index is the literal TRUE.
   * releasesleep (SpecReleasesleep.wp_releasesleep_sconf):
       γs γl γsl "uart" (tx_res γu) M pidv pj (av-8) eb C true
       premises  (22 <= av-8)
       consumes sleeplocked, sl_pid slk |->4 pidv, tx_res γu, procs_inv.
   NOTE none of these takes a condition-lock parameter any more, and wakeup is
   not called from here at all.

   ---- 5.  THE THR STORE, AND WHY IT NEEDS NO INVARIANT ----------------
   At +0x4c use [UAcc.wp_uart_lsr_read_ea_s_sconf] (NOT the ghost-free read):
   it takes [uart_tx_own γu l] out of [tx_res γu] and hands back the token
   plus [⌜ lsr_thre_clear bt = false ⌝ -∗ uart_out_lb γu l].  The [c.beqz] at
   +0x54 is TAKEN exactly when [lsr_thre_clear bt = true], so on the
   FALL-THROUGH arm the wand fires and [uart_out_lb γu l] is in hand three
   instructions before the store -- with the token held throughout, so [l]
   cannot move.  Then +0x5e is [UAcc.wp_uart_thr_write_s_sconf] with
   [uart_dlab_off] from [is_txlock_dlab].  This is uartputc_sync's route
   verbatim (ProofUartPutc.v +0x26 -> +0x38); no lock invariant is involved
   and there is nothing to re-close afterwards.

   [uart_sent_sub] accumulation is unchanged: [uart_tx_own_snapshot] once,
   under [fupd_wp], right after acquiresleep (it is what the n = 0 path
   returns, via [uart_sent_sub_nil]); [uart_tx_own_sent_sub] once per byte,
   under [fupd_wp], immediately before the store, then [uart_sent_sub_snoc] on
   the [uart_sent γu (l ++ [f i])] the store leaf returns.

   ---- 6.  THE ARITHMETIC OBLIGATIONS ----------------------------------
   * +0x1c  [wp_bge_x0_{taken,fall}_s_sconf] at rs2 := Rs2, with
            [zopz0zKzJ_s zero_reg (rget M Rs2) = Z.geb 0 (Z.of_nat n)] from
            [uw_geb_s0].  (The old proof read the count out of s1; it is s2
            now.)
   * +0x42  [wp_bge_{taken,fall}_s_sconf] at rs1 := Rs1, rs2 := Rs2, with
            [zopz0zKzJ_s (rget M Rs1) (rget M Rs2)
               = Z.geb (Z.of_nat i) (Z.of_nat n)] from [uw_geb_nn].
            In the sleep arm [i < n] so it is [false] (fall);
            in the byte arm the scrutinee is [Z.geb (Z.of_nat (S i)) (Z.of_nat n)],
            which is [true] iff [S i = n] given [S i <= n].
   * +0x56  [wp_add_s_sconf] rd := Ra5, rs1 := Rs5, rs2 := Rs1, wval via
            [uw_pa_add_n] : [add_vec buf (mword_of_int (Z.of_nat i)) = pa_add buf i].
   * +0x5a  [wp_lbu_s_sconf] rd = rs1 = Ra5, address [uw_addv_0].
   * +0x5e  stored byte is [uw_sub8_zext] applied to [zero_extend' 64 (f i)].
   * +0x62  [wp_caddiw_s_sconf] at Rs1, result [uw_addiw_p1].
   * +0x54  the [c.beqz] scrutinee after [andi a5,a5,32] is
            [and_vec (lsr_ldval_of bt) (sign_extend' 64 (mword_of_int 32 : mword 12))],
            and [eq_vec that zero_reg] is DEFINITIONALLY
            [WpSconfUartAccess.lsr_thre_clear bt] -- close the premise with
            [rgne; rewrite H<reg>a5; unfold neq_vec; rewrite -/(lsr_thre_clear bt) Hthre; reflexivity]
            (uartintr's spelling), remembering [uw_cr7] for the creg.

   ---- 7.  LEMMA SKELETON ----------------------------------------------
     uw_tail  CID0 γl γsl γu j m0 M av eb C sp0 bs Rbuf pidv dqp :
        uw_tail_regs m0 M (pa_stk sp0 8) -> m0 !!! csp = sp0 ->
        (uartwrite_stack <= av) -> eb = true -> <anchor chain> ->
        kernel_text -* is_txlock γl γsl γu -* procs_inv γs -* panic_wp_any -*
        sie_cap_gpr M (av-8) true pj -* cpu_own 0 eb pj C true -*
        pc_is (+0x6e) -* uw_hold γsl pj pidv dqp -* tx_res γu -*
        uart_sent_sub γu bs -* uw_saved sp0 m0 -* uw_gap4 sp0 -* Rbuf -*
        uw_ret CID0 γu j m0 av eb C bs Rbuf pidv dqp -* WP
        (releasesleep, four restores, [c.addi16sp sp,64], [c.ret];
         [uw_frame_stack_own] rebuilds [stack_own sp0 8] for the pop.)

     uw_one   ... i : i < n, the iLoeb at +0x46, offered the CONJUNCTION
        [uw_next_cont ... i /\ uw_exit_cont ...] -- same reason as before
        (exactly one is taken and both need the caller's tail).

     uw_iter  ... k : induction on [k] with [i + S k = n], concluding
        [uw_head ... i]; the [k = 0] case kills the back edge with
        [iIntros (CIDx Hsx M') "%Hlt". exfalso. lia.]

   ---- 8.  WHAT THE OLD PROOF HAD THAT THIS ONE DOES NOT ----------------
   [uw_slot10] (the frame is exactly 8), [uw_one_ne_zero] / [uw_sext_zero] /
   [uw_sext_nonzero] (no [tx_busy] word to test), [tx_res_busy] /
   [tx_res_idle] (deleted with the certificate), [ByteCursor.pa_add_eqb] (the
   test is on the index, not on a moving pointer), the [Body] iAssert, and
   every [wp_next_off_intro].
   ===================================================================== *)
