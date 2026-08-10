(* ProofUartwrite.v -- the whole-function WP for xv6's uartwrite().

     void uartwrite(char buf[], int n)

   The contract is SpecUartwrite.v; the 52 instruction facts are
   WpUartwriteDecode.v ([uwi_<off>]).  Structure of the proof:

   - [uw_tail] is the shared epilogue at +0x7c (release, restore ra/s0/s1/s5,
     pop the frame, ret).  BOTH paths reach it: the n = 0 path branches
     straight there from the [blez] at +0x1c, and the loop path falls into it
     after restoring the five shrink-wrapped registers.  The five slots it
     does not own are existential in its frame ([uw_gap5]), which is exactly
     what makes the two paths joinable -- on the n = 0 path they were never
     written, on the loop path they were written and read back.

   - the byte loop is TWO nested loops.  The outer one is bounded by [n], so
     it is a [nat] INDUCTION on the bytes remaining ([uw_iter], at the loop
     head +0x6c).  The inner one -- "while (tx_busy) sleep()" -- is unbounded,
     so it is an iLöb ([Sleep], an iAssert inside the induction step); its
     continuation is the loop body at +0x5a, which is itself an iAssert
     ([Body]) because two edges arrive there: the [c.j] at +0x70 (tx_busy was
     already 0) and the sleep loop's own fall-through at +0x58.

   - THE THR WRITE is licensed by the lock invariant, not by a poll:
     [tx_res]'s implication hands out [uart_out_lb γu l] exactly when the
     [tx_busy] cell reads 0, and that is [uart_tx_ready_persists]'s missing
     premise (see UartTxInv.v).  After the push the invariant is re-closed on
     its other side -- [tx_busy = 1], no certificate -- which is precisely the
     [sw s6,0(s1)] the C performs one instruction later.

   - THE OUTPUT CLAIM is [uart_sent_sub] (a SUBLIST of the accepted trace),
     because uartwrite sleeps between bytes and other harts push meanwhile.
     Each iteration re-links its accumulated claim to the trace it is about to
     extend with [uart_tx_own_sent_sub], a plain fupd under [fupd_wp] -- no
     physical step, just the token read against [dev_inv].

   THE HART-GENERIC PROTOCOL, IN THE [wp_next] FORM.  Every leaf and every
   callee returns through [wp_next b p (fun CID => ...)], so the resuming hart
   is an ordinary binder and every resource written after it is automatically
   about it -- no [(CID := h)] on a resource and, the SIE ghost being canonical
   per hart, no ghost to thread.  Where the hart can actually move:

     * the entry index is DERIVABLY [true] ([CpuOwn.cpu_own_eb_agree]: level 0
       with an enabled base has no [b = false] instance), so the prologue, the
       acquire crossing, the post-release epilogue and uartwrite's own
       [wp_next] obligation are hart-GENERIC;
     * from acquire's return to release's call the tx_lock is HELD, i.e. the
       index is the literal [false] and every leaf is a plain
       [rewrite wp_next_off] -- that is the whole loop except its one crossing;
     * the ONE genuine hart change inside the lock is the park: [sleep]'s
       crossing index is the literal [true].  It sits inside BOTH loops, so
       both loop invariants have to survive a hart change.

   Every join is therefore a [wp_next] ANCHORED at an explicit hart: the two
   loop exits ([uw_next_cont] / [uw_exit_cont]) and the head [uw_head] at the
   function's entry hart [CID0], the two internal joins ([Body], [Sleep]) at
   the iteration's own entry hart.  [uw_one] and [uw_tail] take [CID] as a
   LEMMA binder plus the chained equality to the anchor.  [uw_iter]'s
   conclusion IS a [wp_next], which is what makes its induction hypothesis
   re-enterable at the hart the next park lands on.

     * [uw_loop_regs] / [uw_tail_regs] have no tp conjunct: [HartTp.tp_pin]
       pins tp to whichever hart owns the register file.
     * the trap CSRs ride the loop: acquire mints [trap_csrs_pay 0 eb], sleep
       carries it across the park, release spends it.  uartwrite is therefore
       trap-CSR-balanced and its contract does not mention them.
     * the parked-scheduler record is not threaded here: it lives in the
       running proc's own [p->lock] ([SchedCtx.run_slot]), which sleep
       reaches by holding that lock.

   A functor over ACQUIRE / RELEASE / SLEEP / UART. *)
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
Require Import SpecPanic.
Require Import SchedCtx.
Require Import FdSlots.
Require Import SpecAcquire SpecRelease SpecSleep.
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

(* the 10-slot frame geometry: a [c.sdsp]/[c.ldsp] displacement off the
   pushed sp names a slot counted down from the ENTRY sp. *)
Lemma uw_slot_bridge (X : mword 64) (o : mword 64) (k : nat) :
  add_vec (mword_of_int (- (8 * Z.of_nat 10%nat))) o = mword_of_int (- (8 * Z.of_nat k)) ->
  add_vec (pa_stk X 10%nat) o = pa_stk X k.
Proof.
  intro H. unfold pa_stk, add_vec_int. rewrite po_addv_assoc H. reflexivity.
Qed.

(* the signed [blez] test, on a literal count (pipewrite's [pw_geb_s0]). *)
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

Lemma uw_geb_s0 (b : Z) : (- 2 ^ 63 <= b < 2 ^ 63)%Z ->
  zopz0zKzJ_s (zero_reg : mword 64) (mword_of_int b : mword 64) = Z.geb 0 b.
Proof.
  intro Hb. unfold zopz0zKzJ_s.
  assert (Hz : sint (zero_reg : mword 64) = 0%Z) by (vm_compute; reflexivity).
  rewrite Hz (uw_sint_moi b Hb). reflexivity.
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

(* [tx_busy := 1] really does store a nonzero word *)
Lemma uw_one_ne_zero :
  trunc32 (mword_of_int 1 : mword 64) <> (mword_of_int 0 : mword 32).
Proof.
  intro Hc. apply (f_equal bv_unsigned) in Hc. vm_compute in Hc. discriminate.
Qed.

Lemma uw_zero_reg_add (x : mword 64) : add_vec zero_reg x = x.
Proof. apply add_vec_zero_l. Qed.

(* [pa_add p 0] is [p]: the cursor at entry is the buffer base itself. *)
Lemma uw_pa_add_0 (p : mword 64) : pa_add p 0%nat = p.
Proof. unfold pa_add, add_vec_int. apply bv_add_0_r. vm_compute. reflexivity. Qed.

Lemma uw_pa_add_n (p : mword 64) (k : nat) :
  add_vec p (mword_of_int (Z.of_nat k)) = pa_add p k.
Proof. reflexivity. Qed.

(* the two compressed-register indices the loop's [c.lw]/[c.bnez] name *)
Lemma uw_cr1 : creg2reg_idx (Cregidx (mword_of_int 1)) = Regidx (mword_of_int 9 : mword 5).
Proof. vm_compute. reflexivity. Qed.

Lemma uw_cr7 : creg2reg_idx (Cregidx (mword_of_int 7)) = Regidx (mword_of_int 15 : mword 5).
Proof. vm_compute. reflexivity. Qed.

(* "tx_busy read as zero": the [c.bnez] test, back on the 32-bit cell *)
Lemma uw_sext_zero (b : mword 32) :
  eq_vec (sign_extend' 64 b : mword 64) (zero_reg : mword 64) = true ->
  b = (mword_of_int 0 : mword 32).
Proof.
  intro H. apply eq_vec_true_iff in H.
  rewrite <- (trunc32_sext64 b), H. apply bv_eq; vm_compute; reflexivity.
Qed.

Lemma uw_sext_nonzero (b : mword 32) :
  eq_vec (sign_extend' 64 b : mword 64) (zero_reg : mword 64) = false ->
  b <> (mword_of_int 0 : mword 32).
Proof.
  intros H Hc. rewrite Hc in H.
  assert (Ht : eq_vec (sign_extend' 64 (mword_of_int 0 : mword 32) : mword 64)
                      (zero_reg : mword 64) = true) by (vm_compute; reflexivity).
  rewrite Ht in H. discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  The two register-state predicates.  HART-FREE (no tp conjunct).     *)
(* ------------------------------------------------------------------ *)
(* what the loop keeps in registers: the three global addresses, the two
   cursors, the constant 1 and the THR base -- plus the callee-saved
   registers uartwrite itself never touches. *)
Definition uw_loop_regs (m0 M : regfile) (spd buf : mword 64) (n i : nat) : Prop :=
  M !!! Regidx csp_rs1 = spd /\
  M !!! Regidx Rs1 = a_tx_busy /\
  M !!! Regidx Rs2 = a_tx_chan /\
  M !!! Regidx Rs3 = a_tx_lock /\
  M !!! Regidx Rs4 = pa_add buf i /\
  M !!! Regidx Rs5 = pa_add buf n /\
  M !!! Regidx Rs6 = (mword_of_int 1 : mword 64) /\
  M !!! Regidx Rs7 = uart_pa 0 /\
  M !!! Regidx Rs8 = m0 !!! Regidx Rs8 /\
  M !!! Regidx Rs9 = m0 !!! Regidx Rs9 /\
  M !!! Regidx Rs10 = m0 !!! Regidx Rs10 /\
  M !!! Regidx Rs11 = m0 !!! Regidx Rs11.

(* ...and what the epilogue needs: every callee-saved register except the
   four still in the frame. *)
Definition uw_tail_regs (m0 M : regfile) (spd : mword 64) : Prop :=
  M !!! Regidx csp_rs1 = spd /\
  M !!! Regidx Rs2 = m0 !!! Regidx Rs2 /\
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
  intros Hcs (H1 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13).
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

(* the accumulated output claim, and its one-byte step *)
Definition uw_bytes (f : nat -> bv 8) (i : nat) : list (bv 8) := f <$> seq 0 i.

Lemma uw_bytes_snoc (f : nat -> bv 8) (i : nat) :
  uw_bytes f (S i) = (uw_bytes f i ++ [f i])%list.
Proof. rewrite /uw_bytes seq_S fmap_app. reflexivity. Qed.

(* ===================================================================== *)

Section UwProps.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !irefNameG Σ, !irefslotG Σ}.
  Context `{!uartGhostG Σ, !diskGhostG Σ}.

  (* ra/s0/s1/s5, saved unconditionally in the prologue *)
  Definition uw_saved (sp0 : mword 64) (m0 : regfile) : iProp Σ :=
    (pa_stk sp0 1 ↦₈ (m0 !!! Regidx Rra) ∗
     pa_stk sp0 2 ↦₈ (m0 !!! Regidx Rs0) ∗
     pa_stk sp0 3 ↦₈ (m0 !!! Regidx Rs1) ∗
     pa_stk sp0 7 ↦₈ (m0 !!! Regidx Rs5))%I.

  (* s2/s3/s4/s6/s7, SHRINK-WRAPPED onto the n > 0 path *)
  Definition uw_saved5 (sp0 : mword 64) (m0 : regfile) : iProp Σ :=
    (pa_stk sp0 4 ↦₈ (m0 !!! Regidx Rs2) ∗
     pa_stk sp0 5 ↦₈ (m0 !!! Regidx Rs3) ∗
     pa_stk sp0 6 ↦₈ (m0 !!! Regidx Rs4) ∗
     pa_stk sp0 8 ↦₈ (m0 !!! Regidx Rs6) ∗
     pa_stk sp0 9 ↦₈ (m0 !!! Regidx Rs7))%I.

  (* the same five slots at UNKNOWN contents: what the n = 0 path has, and
     what the two paths agree on at the join *)
  Definition uw_gap5 (sp0 : mword 64) : iProp Σ :=
    ((∃ w : mword 64, pa_stk sp0 4 ↦₈ w) ∗ (∃ w : mword 64, pa_stk sp0 5 ↦₈ w) ∗
     (∃ w : mword 64, pa_stk sp0 6 ↦₈ w) ∗ (∃ w : mword 64, pa_stk sp0 8 ↦₈ w) ∗
     (∃ w : mword 64, pa_stk sp0 9 ↦₈ w))%I.

  Definition uw_slot10 (sp0 : mword 64) : iProp Σ :=
    (∃ w : mword 64, pa_stk sp0 10 ↦₈ w)%I.

  Lemma uw_saved5_gap sp0 m0 : uw_saved5 sp0 m0 -∗ uw_gap5 sp0.
  Proof.
    iIntros "(H4 & H5 & H6 & H8 & H9)". rewrite /uw_gap5.
    iSplitL "H4"; [by iExists _|]. iSplitL "H5"; [by iExists _|].
    iSplitL "H6"; [by iExists _|]. iSplitL "H8"; [by iExists _|]. by iExists _.
  Qed.

  Lemma uw_frame_stack_own sp0 m0 :
    uw_saved sp0 m0 -∗ uw_gap5 sp0 -∗ uw_slot10 sp0 -∗ stack_own sp0 10.
  Proof.
    iIntros "(H1 & H2 & H3 & H7) (H4 & H5 & H6 & H8 & H9) H10".
    rewrite stack_own_slots. cbn [seq].
    iSplitL "H1"; [by iExists _|]. iSplitL "H2"; [by iExists _|].
    iSplitL "H3"; [by iExists _|]. iSplitL "H4"; [by iExact "H4"|].
    iSplitL "H5"; [by iExact "H5"|]. iSplitL "H6"; [by iExact "H6"|].
    iSplitL "H7"; [by iExists _|]. iSplitL "H8"; [by iExact "H8"|].
    iSplitL "H9"; [by iExact "H9"|]. iSplitL "H10"; [by iExact "H10"|]. done.
  Qed.

  Definition uw_buf (buf : mword 64) (dq : dfrac) (f : nat -> bv 8) (n : nat) : iProp Σ :=
    ([∗ list] k0 ∈ seq 0 n, (pa_add buf k0) ↦ₘ{dq} f k0)%I.

  Definition uw_full (sp0 : mword 64) (m0 : regfile) : iProp Σ :=
    (uw_saved sp0 m0 ∗ uw_saved5 sp0 m0 ∗ uw_slot10 sp0)%I.

  (* ------------------------------------------------------------------ *)
  (*  The joins, each a [wp_next] at an explicit anchor.                  *)
  (* ------------------------------------------------------------------ *)

  (* the byte loop's two exits (+0x6c back edge, +0x72 leave) *)
  Definition uw_next_cont `{GEN : GenId} (CID0 : CPU) (γl : gname) (γu : uart_names) 
      (j : nat) (m0 : regfile) (av : nat) (eb : bool) (C : iProp Σ)
      (sp0 buf : mword 64) (n : nat) (f : nat -> bv 8) (dq : dfrac) (i : nat) : iProp Σ :=
    (wp_next (CID0 := CID0) true (proc_addr j) (fun (CID : CpuId) =>
       ∀ M' : regfile,
       ⌜ (S i < n)%nat ⌝ -∗
       ⌜ uw_loop_regs m0 M' (pa_stk sp0 10) buf n (S i) ⌝ -∗
       sie_cap_gpr M' (av - 10) false (proc_addr j) -∗
       cpu_own 1%nat eb (proc_addr j) C false -∗ arm_pay 0%nat eb (proc_addr j) -∗
       pc_is (mword_of_int (KernelSyms.uartwrite + 0x6c)) -∗
       locked γl cpu_id -∗ tx_res γu -∗
       uart_sent_sub γu (uw_bytes f (S i)) -∗
       uw_full sp0 m0 -∗ uw_buf buf dq f n -∗
       WP (Loop : expr riscv_lang)))%I.

  Definition uw_exit_cont `{GEN : GenId} (CID0 : CPU) (γl : gname) (γu : uart_names) 
      (j : nat) (m0 : regfile) (av : nat) (eb : bool) (C : iProp Σ)
      (sp0 buf : mword 64) (n : nat) (f : nat -> bv 8) (dq : dfrac) : iProp Σ :=
    (wp_next (CID0 := CID0) true (proc_addr j) (fun (CID : CpuId) =>
       ∀ M' : regfile,
       ⌜ uw_loop_regs m0 M' (pa_stk sp0 10) buf n n ⌝ -∗
       sie_cap_gpr M' (av - 10) false (proc_addr j) -∗
       cpu_own 1%nat eb (proc_addr j) C false -∗ arm_pay 0%nat eb (proc_addr j) -∗
       pc_is (mword_of_int (KernelSyms.uartwrite + 0x72)) -∗
       locked γl cpu_id -∗ tx_res γu -∗
       uart_sent_sub γu (uw_bytes f n) -∗
       uw_full sp0 m0 -∗ uw_buf buf dq f n -∗
       WP (Loop : expr riscv_lang)))%I.

  (* the loop head at +0x6c, ENTERED at whatever hart the last park landed on *)
  Definition uw_head `{GEN : GenId} (CID0 : CPU) (γl : gname) (γu : uart_names)
      (j : nat) (m0 : regfile) (av : nat) (eb : bool) (C : iProp Σ)
      (sp0 buf : mword 64) (n : nat) (f : nat -> bv 8) (dq : dfrac) (i : nat) : iProp Σ :=
    (wp_next (CID0 := CID0) true (proc_addr j) (fun (CID : CpuId) =>
       ∀ M : regfile,
       ⌜ uw_loop_regs m0 M (pa_stk sp0 10) buf n i ⌝ -∗
       sie_cap_gpr M (av - 10) false (proc_addr j) -∗
       cpu_own 1%nat eb (proc_addr j) C false -∗ arm_pay 0%nat eb (proc_addr j) -∗
       pc_is (mword_of_int (KernelSyms.uartwrite + 0x6c)) -∗
       locked γl cpu_id -∗ tx_res γu -∗
       uart_sent_sub γu (uw_bytes f i) -∗
       uw_full sp0 m0 -∗ uw_buf buf dq f n -∗
       uw_exit_cont CID0 γl γu j m0 av eb C sp0 buf n f dq -∗
       WP (Loop : expr riscv_lang)))%I.

  (* the tail's own continuation: uartwrite's postcondition, at ANY hart *)
  Definition uw_ret `{GEN : GenId} (CID0 : CPU) (γu : uart_names) 
      (j : nat) (m0 : regfile) (av : nat) (eb : bool) (C : iProp Σ)
      (bs : list (bv 8)) (Rbuf : iProp Σ) : iProp Σ :=
    (wp_next (CID0 := CID0) true (proc_addr j) (fun (CID : CpuId) =>
       ∀ mf : regfile,
         ⌜ callee_saved m0 mf ⌝ -∗
         sie_cap_gpr mf av true (proc_addr j) -∗
         cpu_own 0%nat eb (proc_addr j) C true -∗
         pc_is (ret_pc (m0 !!! Regidx Rra)) -∗
         Rbuf -∗
         uart_sent_sub γu bs -∗
         WP (Loop : expr riscv_lang)))%I.

End UwProps.

(* ===================================================================== *)

Module UartwriteProof (Acquire : ACQUIRE) (Release : RELEASE) (Sleep : SLEEP)
                      (Uart : UART) : UARTWRITE.

Module UAcc := UartAccessProof Uart.

Local Ltac reg_neq :=
  lazymatch goal with |- ?a <> ?b =>
    tryif unify a b then fail else (vm_compute; discriminate) end.
Local Ltac nz := vm_compute; discriminate.
Local Ltac pcw := apply bv_eq; vm_compute; reflexivity.

Section UwBodies.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !irefNameG Σ, !irefslotG Σ}.
  Context `{!uartGhostG Σ, !diskGhostG Σ}.

  (* ------------------------------------------------------------------ *)
  (*  The epilogue, shared by both paths: +0x7c -> return.                *)
  (* ------------------------------------------------------------------ *)
  Lemma uw_tail `{GEN : GenId} `{CID : CpuId} (CID0 : CPU)
      (γl : gname) (γu : uart_names)
      (j : nat) (m0 M : regfile) (av : nat) (eb : bool) (C : iProp Σ) (sp0 : mword 64)
      (bs : list (bv 8)) (Rbuf : iProp Σ) :
    let pj := proc_addr j in
    uw_tail_regs m0 M (pa_stk sp0 10) ->
    m0 !!! Regidx csp_rs1 = sp0 ->
    (uartwrite_stack <= av)%nat ->
    eb = true ->
    (true = false \/ pj = zero_reg -> (CID : CPU) = CID0) ->
    kernel_text -∗ is_txlock γl γu -∗
    sie_cap_gpr M (av - 10) false pj -∗
    cpu_own 1%nat eb pj C false -∗ arm_pay 0%nat eb pj -∗
    pc_is (mword_of_int (KernelSyms.uartwrite + 0x7c)) -∗
    locked γl cpu_id -∗ tx_res γu -∗
    uart_sent_sub γu bs -∗
    uw_saved sp0 m0 -∗ uw_gap5 sp0 -∗ uw_slot10 sp0 -∗
    Rbuf -∗
    uw_ret CID0 γu j m0 av eb C bs Rbuf -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros pj Hregs Hsp0 Hav Heb Hanch. subst eb.
    destruct Hregs as (Hsp & H18 & H19 & H20 & H22 & H23 & H24 & H25 & H26 & H27).
    iIntros "#Ht #Htxl Hcg Hcnt Hpay Hpc Htok HR #Hsub Hsv Hgap Hs10 Hbuf Hcont".
    iDestruct (is_txlock_lock with "Htxl") as "#Hlk".
    set (spd := pa_stk sp0 10).
    (* +0x7c  auipc a0,0x12 *)
    iPoseProof (uwi_7c with "Ht") as "Hi7c".
    iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.uartwrite + 0x7c)) Ra0 (mword_of_int 18 : mword 20)
              M (av - 10)%nat false ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi7c [-]").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    set (T0 := <[Regidx Ra0 := regval_into_reg
        (add_vec (mword_of_int (KernelSyms.uartwrite + 0x7c) : mword 64) (auipc_off (mword_of_int 18 : mword 20)))]> M).
    change (<[Regidx Ra0 := regval_into_reg
        (add_vec (mword_of_int (KernelSyms.uartwrite + 0x7c) : mword 64) (auipc_off (mword_of_int 18 : mword 20)))]> M) with T0.
    assert (P80 : add_vec_int (mword_of_int (KernelSyms.uartwrite + 0x7c) : mword 64) 4 = mword_of_int (KernelSyms.uartwrite + 0x80)) by pcw.
    iEval (rewrite P80) in "Hpc".
    (* +0x80  addi a0,a0,-1608  -> &tx_lock *)
    iPoseProof (uwi_80 with "Ht") as "Hi80".
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.uartwrite + 0x80)) Ra0 Ra0 (mword_of_int 0x9b8 : mword 12)
              T0 (av - 10)%nat false ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi80 [-]").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (T1 := <[Regidx Ra0 := regval_into_reg
        (add_vec (T0 !!! Regidx Ra0) (sign_extend' 64 (mword_of_int 0x9b8 : mword 12)))]> T0).
    change (<[Regidx Ra0 := regval_into_reg
        (add_vec (T0 !!! Regidx Ra0) (sign_extend' 64 (mword_of_int 0x9b8 : mword 12)))]> T0) with T1.
    assert (P84 : add_vec_int (mword_of_int (KernelSyms.uartwrite + 0x80) : mword 64) 4 = mword_of_int (KernelSyms.uartwrite + 0x84)) by pcw.
    iEval (rewrite P84) in "Hpc".
    (* +0x84  jal ra,release *)
    iPoseProof (uwi_84 with "Ht") as "Hi84".
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.uartwrite + 0x84)) Rra (mword_of_int 816 : mword 21)
              T1 (av - 10)%nat false ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi84 [-]").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    set (T2 := <[Regidx Rra := regval_into_reg
        (add_vec_int (mword_of_int (KernelSyms.uartwrite + 0x84) : mword 64) 4)]> T1).
    change (<[Regidx Rra := regval_into_reg
        (add_vec_int (mword_of_int (KernelSyms.uartwrite + 0x84) : mword 64) 4)]> T1) with T2.
    assert (Hjrel : add_vec (mword_of_int (KernelSyms.uartwrite + 0x84) : mword 64)
                      (sign_extend' 64 (mword_of_int 816 : mword 21)) = mword_of_int KernelSyms.release) by pcw.
    iEval (rewrite Hjrel) in "Hpc".
    assert (HT2a0 : T2 !!! Regidx Ra0 = a_tx_lock).
    { rewrite /T2 upd_ne; [| reg_neq]. rewrite /T1 upd_eq. rewrite /T0 upd_eq.
      rewrite /a_tx_lock. pcw. }
    assert (HT2sp : T2 !!! Regidx csp_rs1 = spd).
    { rewrite /T2 upd_ne; [| reg_neq]. rewrite /T1 upd_ne; [| reg_neq].
      rewrite /T0 upd_ne; [| reg_neq]. exact Hsp. }
    assert (HT2ra : T2 !!! Regidx Rra = add_vec_int (mword_of_int (KernelSyms.uartwrite + 0x84) : mword 64) 4)
      by (rewrite /T2 upd_eq; reflexivity).
    iApply (Release.wp_release_sconf γl a_tx_lock "uart"%string (tx_res γu) T2
              0%nat true pj C (av - 10)%nat
              ltac:(rewrite HT2a0; apply uw_addv_0)
              ltac:(unfold uartwrite_stack in Hav; lia)
              with "Hcg Ht Hpc [Hlk] [Htok] [HR] Hcnt Hpay [-]").
    { iExact "Hlk". }
    { iExact "Htok". }
    { iExact "HR". }
    iIntros (CIDr Hsr MR) "Hcg Hpc %HcsR Hcnt".
    assert (P88 : ret_pc (add_vec_int (mword_of_int (KernelSyms.uartwrite + 0x84) : mword 64) 4)
                  = mword_of_int (KernelSyms.uartwrite + 0x88)) by pcw.
    iEval (rewrite HT2ra) in "Hpc". iEval (rewrite P88) in "Hpc".
    assert (HMRsp : MR !!! Regidx csp_rs1 = spd)
      by (rewrite (callee_saved_lookup HcsR csp_rs1 ltac:(vm_compute; reflexivity)); exact HT2sp).
    (* --- the four unconditional restores (+0x88 .. +0x8e) --- *)
    iDestruct "Hsv" as "(H1 & H2 & H3 & H7)".
    assert (Hb1 : add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 9 : mword 6) ('b"000"))) = pa_stk sp0 1)
      by (apply uw_slot_bridge; pcw).
    assert (Hb2 : add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 8 : mword 6) ('b"000"))) = pa_stk sp0 2)
      by (apply uw_slot_bridge; pcw).
    assert (Hb3 : add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 7 : mword 6) ('b"000"))) = pa_stk sp0 3)
      by (apply uw_slot_bridge; pcw).
    assert (Hb7 : add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000"))) = pa_stk sp0 7)
      by (apply uw_slot_bridge; pcw).
    iPoseProof (uwi_88 with "Ht") as "Hi88".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.uartwrite + 0x88)) (mword_of_int 9 : mword 6) Rra
              MR (av - 10)%nat (m0 !!! Regidx Rra) true (dqm := DfracOwn 1)
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi88 [H1] [-]").
    { iEval (rewrite HMRsp Hb1). iExact "H1". }
    iIntros (CIDe1 Hse1) "Hcg Hpc H1". iEval (rewrite HMRsp Hb1) in "H1".
    set (E1 := <[Regidx Rra := regval_into_reg (m0 !!! Regidx Rra)]> MR).
    change (<[Regidx Rra := regval_into_reg (m0 !!! Regidx Rra)]> MR) with E1.
    assert (P8a : add_vec_int (mword_of_int (KernelSyms.uartwrite + 0x88) : mword 64) 2 = mword_of_int (KernelSyms.uartwrite + 0x8a)) by pcw.
    iEval (rewrite P8a) in "Hpc".
    assert (HE1sp : E1 !!! Regidx csp_rs1 = spd)
      by (rewrite /E1 upd_ne; [exact HMRsp | reg_neq]).
    iPoseProof (uwi_8a with "Ht") as "Hi8a".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.uartwrite + 0x8a)) (mword_of_int 8 : mword 6) Rs0
              E1 (av - 10)%nat (m0 !!! Regidx Rs0) true (dqm := DfracOwn 1)
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi8a [H2] [-]").
    { iEval (rewrite HE1sp Hb2). iExact "H2". }
    iIntros (CIDe2 Hse2) "Hcg Hpc H2". iEval (rewrite HE1sp Hb2) in "H2".
    set (E2 := <[Regidx Rs0 := regval_into_reg (m0 !!! Regidx Rs0)]> E1).
    change (<[Regidx Rs0 := regval_into_reg (m0 !!! Regidx Rs0)]> E1) with E2.
    assert (P8c : add_vec_int (mword_of_int (KernelSyms.uartwrite + 0x8a) : mword 64) 2 = mword_of_int (KernelSyms.uartwrite + 0x8c)) by pcw.
    iEval (rewrite P8c) in "Hpc".
    assert (HE2sp : E2 !!! Regidx csp_rs1 = spd)
      by (rewrite /E2 upd_ne; [exact HE1sp | reg_neq]).
    iPoseProof (uwi_8c with "Ht") as "Hi8c".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.uartwrite + 0x8c)) (mword_of_int 7 : mword 6) Rs1
              E2 (av - 10)%nat (m0 !!! Regidx Rs1) true (dqm := DfracOwn 1)
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi8c [H3] [-]").
    { iEval (rewrite HE2sp Hb3). iExact "H3". }
    iIntros (CIDe3 Hse3) "Hcg Hpc H3". iEval (rewrite HE2sp Hb3) in "H3".
    set (E3 := <[Regidx Rs1 := regval_into_reg (m0 !!! Regidx Rs1)]> E2).
    change (<[Regidx Rs1 := regval_into_reg (m0 !!! Regidx Rs1)]> E2) with E3.
    assert (P8e : add_vec_int (mword_of_int (KernelSyms.uartwrite + 0x8c) : mword 64) 2 = mword_of_int (KernelSyms.uartwrite + 0x8e)) by pcw.
    iEval (rewrite P8e) in "Hpc".
    assert (HE3sp : E3 !!! Regidx csp_rs1 = spd)
      by (rewrite /E3 upd_ne; [exact HE2sp | reg_neq]).
    iPoseProof (uwi_8e with "Ht") as "Hi8e".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.uartwrite + 0x8e)) (mword_of_int 3 : mword 6) Rs5
              E3 (av - 10)%nat (m0 !!! Regidx Rs5) true (dqm := DfracOwn 1)
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi8e [H7] [-]").
    { iEval (rewrite HE3sp Hb7). iExact "H7". }
    iIntros (CIDe4 Hse4) "Hcg Hpc H7". iEval (rewrite HE3sp Hb7) in "H7".
    set (E4 := <[Regidx Rs5 := regval_into_reg (m0 !!! Regidx Rs5)]> E3).
    change (<[Regidx Rs5 := regval_into_reg (m0 !!! Regidx Rs5)]> E3) with E4.
    assert (P90 : add_vec_int (mword_of_int (KernelSyms.uartwrite + 0x8e) : mword 64) 2 = mword_of_int (KernelSyms.uartwrite + 0x90)) by pcw.
    iEval (rewrite P90) in "Hpc".
    assert (HE4sp : E4 !!! Regidx csp_rs1 = spd)
      by (rewrite /E4 upd_ne; [exact HE3sp | reg_neq]).
    (* +0x90  c.addi16sp sp,80 -- the frame pop *)
    iAssert (stack_own sp0 10) with "[H1 H2 H3 H7 Hgap Hs10]" as "Hframe".
    { iApply (uw_frame_stack_own sp0 m0 with "[H1 H2 H3 H7] Hgap Hs10").
      rewrite /uw_saved. iFrame "H1 H2 H3 H7". }
    assert (Hpopv : add_vec (E4 !!! Regidx csp_rs1)
                      (sign_extend' 64 (caddi16sp_imm (mword_of_int 5 : mword 6))) = sp0).
    { rewrite HE4sp /spd. unfold pa_stk, add_vec_int. rewrite po_addv_assoc.
      rewrite (_ : add_vec (mword_of_int (- (8 * Z.of_nat 10%nat)) : mword 64)
                     (sign_extend' 64 (caddi16sp_imm (mword_of_int 5 : mword 6)))
                   = (mword_of_int 0 : mword 64)); [| pcw].
      apply bv_add_0_r. vm_compute. reflexivity. }
    assert (Hpop : E4 !!! Regidx csp_rs1
                   = pa_stk (add_vec (E4 !!! Regidx csp_rs1)
                       (sign_extend' 64 (caddi16sp_imm (mword_of_int 5 : mword 6)))) 10%nat)
      by (rewrite Hpopv HE4sp; reflexivity).
    iEval (rewrite -Hpopv) in "Hframe".
    iPoseProof (uwi_90 with "Ht") as "Hi90".
    iApply (wp_caddi16sp_pop_s_sconf (mword_of_int (KernelSyms.uartwrite + 0x90)) (mword_of_int 5 : mword 6)
              E4 (av - 10)%nat 10%nat true Hpop with "Hcg Hpc Hi90 Hframe [-]").
    iIntros (CIDe5 Hse5) "Hcg Hpc".
    assert (Hav10 : ((av - 10) + 10)%nat = av) by (unfold uartwrite_stack in Hav; lia).
    iEval (rewrite Hav10) in "Hcg".
    set (E5 := <[Regidx csp_rs1 := regval_into_reg
        (add_vec (E4 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 5 : mword 6))))]> E4).
    change (<[Regidx csp_rs1 := regval_into_reg
        (add_vec (E4 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 5 : mword 6))))]> E4) with E5.
    assert (P92 : add_vec_int (mword_of_int (KernelSyms.uartwrite + 0x90) : mword 64) 2 = mword_of_int (KernelSyms.uartwrite + 0x92)) by pcw.
    iEval (rewrite P92) in "Hpc".
    (* +0x92  c.ret *)
    assert (HE5ra : E5 !!! Regidx Rra = m0 !!! Regidx Rra).
    { rewrite /E5 upd_ne; [| reg_neq]. rewrite /E4 upd_ne; [| reg_neq].
      rewrite /E3 upd_ne; [| reg_neq]. rewrite /E2 upd_ne; [| reg_neq].
      rewrite /E1 upd_eq. reflexivity. }
    iPoseProof (uwi_92 with "Ht") as "Hi92".
    iApply (wp_cret_s_sconf (mword_of_int (KernelSyms.uartwrite + 0x92)) Rra E5 av true ltac:(nz)
              with "Hcg Hpc Hi92 [-]").
    iIntros (CIDe6 Hse6) "Hcg Hpc". iEval (rgne) in "Hpc".
    iEval (rewrite HE5ra) in "Hpc".
    (* ---- callee_saved m0 E5 ---- *)
    assert (HE5sp : E5 !!! Regidx csp_rs1 = m0 !!! Regidx csp_rs1)
      by (rewrite /E5 upd_eq; unfold regval_into_reg; rewrite Hpopv; symmetry; exact Hsp0).
    assert (HE5s0 : E5 !!! Regidx Rs0 = m0 !!! Regidx Rs0).
    { rewrite /E5 upd_ne; [| reg_neq]. rewrite /E4 upd_ne; [| reg_neq].
      rewrite /E3 upd_ne; [| reg_neq]. rewrite /E2 upd_eq. reflexivity. }
    assert (HE5s1 : E5 !!! Regidx Rs1 = m0 !!! Regidx Rs1).
    { rewrite /E5 upd_ne; [| reg_neq]. rewrite /E4 upd_ne; [| reg_neq].
      rewrite /E3 upd_eq. reflexivity. }
    assert (HE5s5 : E5 !!! Regidx Rs5 = m0 !!! Regidx Rs5).
    { rewrite /E5 upd_ne; [| reg_neq]. rewrite /E4 upd_eq. reflexivity. }
    assert (Hthr : forall r : mword 5, is_cs_idx r = true ->
                     r <> csp_rs1 -> r <> mword_of_int 1 -> r <> mword_of_int 8 ->
                     r <> mword_of_int 9 -> r <> mword_of_int 21 -> r <> mword_of_int 10 ->
                     E5 !!! Regidx r = MR !!! Regidx r).
    { intros r Hr Ncsp N1 N8 N9 N21 N10.
      rewrite /E5 upd_ne; [| congruence]. rewrite /E4 upd_ne; [| congruence].
      rewrite /E3 upd_ne; [| congruence]. rewrite /E2 upd_ne; [| congruence].
      rewrite /E1 upd_ne; [| congruence]. reflexivity. }
    assert (HMRk : forall r : mword 5, is_cs_idx r = true ->
                     r <> csp_rs1 -> r <> mword_of_int 1 -> r <> mword_of_int 8 ->
                     r <> mword_of_int 9 -> r <> mword_of_int 21 -> r <> mword_of_int 10 ->
                     E5 !!! Regidx r = T2 !!! Regidx r).
    { intros r Hr Ncsp N1 N8 N9 N21 N10.
      rewrite (Hthr r Hr Ncsp N1 N8 N9 N21 N10).
      exact (callee_saved_lookup HcsR r Hr). }
    assert (HT2k : forall r : mword 5, r <> csp_rs1 -> r <> mword_of_int 1 -> r <> mword_of_int 10 ->
                     T2 !!! Regidx r = M !!! Regidx r).
    { intros r Ncsp N1 N10.
      rewrite /T2 upd_ne; [| congruence]. rewrite /T1 upd_ne; [| congruence].
      rewrite /T0 upd_ne; [| congruence]. reflexivity. }
    iDestruct (cpu_own_transport CIDr CIDe6 0 true pj C true ltac:(wp_next_chain)
                 with "Hcnt") as "Hcnt".
    rewrite /uw_ret.
    iSpecialize ("Hcont" $! CIDe6 with "[%]"); [wp_next_chain|].
    iApply ("Hcont" $! E5 with "[%] Hcg Hcnt Hpc Hbuf Hsub").
    unfold callee_saved.
    split; [exact HE5sp|].
    split; [exact HE5s0|].
    split; [exact HE5s1|].
    split; [rewrite (HMRk (mword_of_int 18) ltac:(vm_compute; reflexivity)
                       ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq));
            rewrite (HT2k (mword_of_int 18) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)); exact H18|].
    split; [rewrite (HMRk (mword_of_int 19) ltac:(vm_compute; reflexivity)
                       ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq));
            rewrite (HT2k (mword_of_int 19) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)); exact H19|].
    split; [rewrite (HMRk (mword_of_int 20) ltac:(vm_compute; reflexivity)
                       ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq));
            rewrite (HT2k (mword_of_int 20) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)); exact H20|].
    split; [exact HE5s5|].
    split; [rewrite (HMRk (mword_of_int 22) ltac:(vm_compute; reflexivity)
                       ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq));
            rewrite (HT2k (mword_of_int 22) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)); exact H22|].
    split; [rewrite (HMRk (mword_of_int 23) ltac:(vm_compute; reflexivity)
                       ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq));
            rewrite (HT2k (mword_of_int 23) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)); exact H23|].
    split; [rewrite (HMRk (mword_of_int 24) ltac:(vm_compute; reflexivity)
                       ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq));
            rewrite (HT2k (mword_of_int 24) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)); exact H24|].
    split; [rewrite (HMRk (mword_of_int 25) ltac:(vm_compute; reflexivity)
                       ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq));
            rewrite (HT2k (mword_of_int 25) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)); exact H25|].
    split; [rewrite (HMRk (mword_of_int 26) ltac:(vm_compute; reflexivity)
                       ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq));
            rewrite (HT2k (mword_of_int 26) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)); exact H26|].
    rewrite (HMRk (mword_of_int 27) ltac:(vm_compute; reflexivity)
               ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)).
    rewrite (HT2k (mword_of_int 27) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)). exact H27.
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  ONE ITERATION: the head at +0x6c, the sleep retry, the body.        *)
  (* ------------------------------------------------------------------ *)
  Lemma uw_one `{GEN : GenId} `{CID : CpuId} (CID0 : CPU)
      (γl : gname) (γu : uart_names) (γv : disk_names)
      (γs : list gname) (j : nat) (γlp : gname)
      (m0 M : regfile) (av : nat) (eb : bool) (C : iProp Σ)
      (sp0 buf : mword 64) (n : nat) (f : nat -> bv 8) (dq : dfrac) (i : nat) :
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
    sie_cap_gpr M (av - 10) false pj -∗
    cpu_own 1%nat eb pj C false -∗ arm_pay 0%nat eb pj -∗
    pc_is (mword_of_int (KernelSyms.uartwrite + 0x6c)) -∗
    locked γl cpu_id -∗ tx_res γu -∗
    uart_sent_sub γu (uw_bytes f i) -∗
    uw_full sp0 m0 -∗ uw_buf buf dq f n -∗
    ( uw_next_cont CID0 γl γu j m0 av eb C sp0 buf n f dq i
      ∧ uw_exit_cont CID0 γl γu j m0 av eb C sp0 buf n f dq ) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros pj Hin Hn31 Hj Hjlp Hav Heb Hanch Hregs.
    assert (H231 : (2 ^ 31 = 2147483648)%Z) by (vm_compute; reflexivity).
    rewrite H231 in Hn31.
    assert (Hn64 : (Z.of_nat n < 18446744073709551616)%Z) by lia.
    assert (HSi64 : (Z.of_nat (S i) < 18446744073709551616)%Z) by lia.
    iIntros "#Ht #Hdinv #Htxl #Hpinv #Hpanic".
    iIntros "Hcg Hcnt Hpay Hpc Htok Hres #Hsub Hfull Hbuf Hcont".
    iDestruct (is_txlock_lock with "Htxl") as "#Hlk".
    iDestruct (is_txlock_dlab with "Htxl") as "#Hdlab".
    iPoseProof (uwi_4e with "Ht") as "#Hi4e".
    iPoseProof (uwi_50 with "Ht") as "#Hi50".
    iPoseProof (uwi_52 with "Ht") as "#Hi52".
    iPoseProof (uwi_56 with "Ht") as "#Hi56".
    iPoseProof (uwi_58 with "Ht") as "#Hi58".
    iPoseProof (uwi_5a with "Ht") as "#Hi5a".
    iPoseProof (uwi_5e with "Ht") as "#Hi5e".
    iPoseProof (uwi_62 with "Ht") as "#Hi62".
    iPoseProof (uwi_66 with "Ht") as "#Hi66".
    iPoseProof (uwi_68 with "Ht") as "#Hi68".
    iPoseProof (uwi_6c with "Ht") as "#Hi6c".
    iPoseProof (uwi_6e with "Ht") as "#Hi6e".
    iPoseProof (uwi_70 with "Ht") as "#Hi70".
    assert (P50 : add_vec_int (mword_of_int (KernelSyms.uartwrite + 0x4e) : mword 64) 2 = mword_of_int (KernelSyms.uartwrite + 0x50)) by pcw.
    assert (P52 : add_vec_int (mword_of_int (KernelSyms.uartwrite + 0x50) : mword 64) 2 = mword_of_int (KernelSyms.uartwrite + 0x52)) by pcw.
    assert (P56 : ret_pc (add_vec_int (mword_of_int (KernelSyms.uartwrite + 0x52) : mword 64) 4) = mword_of_int (KernelSyms.uartwrite + 0x56)) by pcw.
    assert (P58 : add_vec_int (mword_of_int (KernelSyms.uartwrite + 0x56) : mword 64) 2 = mword_of_int (KernelSyms.uartwrite + 0x58)) by pcw.
    assert (P5a : add_vec_int (mword_of_int (KernelSyms.uartwrite + 0x58) : mword 64) 2 = mword_of_int (KernelSyms.uartwrite + 0x5a)) by pcw.
    assert (P5e : add_vec_int (mword_of_int (KernelSyms.uartwrite + 0x5a) : mword 64) 4 = mword_of_int (KernelSyms.uartwrite + 0x5e)) by pcw.
    assert (P62 : add_vec_int (mword_of_int (KernelSyms.uartwrite + 0x5e) : mword 64) 4 = mword_of_int (KernelSyms.uartwrite + 0x62)) by pcw.
    assert (P66 : add_vec_int (mword_of_int (KernelSyms.uartwrite + 0x62) : mword 64) 4 = mword_of_int (KernelSyms.uartwrite + 0x66)) by pcw.
    assert (P68 : add_vec_int (mword_of_int (KernelSyms.uartwrite + 0x66) : mword 64) 2 = mword_of_int (KernelSyms.uartwrite + 0x68)) by pcw.
    assert (P6c : add_vec_int (mword_of_int (KernelSyms.uartwrite + 0x68) : mword 64) 4 = mword_of_int (KernelSyms.uartwrite + 0x6c)) by pcw.
    assert (P6e : add_vec_int (mword_of_int (KernelSyms.uartwrite + 0x6c) : mword 64) 2 = mword_of_int (KernelSyms.uartwrite + 0x6e)) by pcw.
    assert (P70 : add_vec_int (mword_of_int (KernelSyms.uartwrite + 0x6e) : mword 64) 2 = mword_of_int (KernelSyms.uartwrite + 0x70)) by pcw.
    assert (Jbody : add_vec (mword_of_int (KernelSyms.uartwrite + 0x70) : mword 64)
                      (sign_extend' 64 (sign_extend' 21 (concat_vec (mword_of_int 2037 : mword 11) ('b"0"))))
                    = mword_of_int (KernelSyms.uartwrite + 0x5a)) by pcw.
    assert (Jsleep1 : add_vec (mword_of_int (KernelSyms.uartwrite + 0x58) : mword 64)
                        (sign_extend' 64 (sign_extend' 13 (concat_vec (mword_of_int 251 : mword 8) ('b"0"))))
                      = mword_of_int (KernelSyms.uartwrite + 0x4e)) by pcw.
    assert (Jsleep2 : add_vec (mword_of_int (KernelSyms.uartwrite + 0x6e) : mword 64)
                        (sign_extend' 64 (sign_extend' 13 (concat_vec (mword_of_int 240 : mword 8) ('b"0"))))
                      = mword_of_int (KernelSyms.uartwrite + 0x4e)) by pcw.
    assert (Jexit : add_vec (mword_of_int (KernelSyms.uartwrite + 0x68) : mword 64)
                      (sign_extend' 64 (mword_of_int 10 : mword 13)) = mword_of_int (KernelSyms.uartwrite + 0x72)) by pcw.
    assert (Jcall : add_vec (mword_of_int (KernelSyms.uartwrite + 0x52) : mword 64)
                      (sign_extend' 64 (mword_of_int 5602 : mword 21)) = mword_of_int KernelSyms.sleep) by pcw.
    (* ================================================================= *)
    (*  THE BODY: +0x5a .. +0x68.  ANCHORED at this iteration's own hart. *)
    (* ================================================================= *)
    iAssert (wp_next (CID0 := CID) true pj (fun (CIDb : CpuId) =>
      ∀ (M2 : regfile) (l2 : list (bv 8)) (b2 : mword 32),
      ⌜ uw_loop_regs m0 M2 (pa_stk sp0 10) buf n i ⌝ -∗
      sie_cap_gpr M2 (av - 10) false pj -∗
      cpu_own 1%nat eb pj C false -∗ arm_pay 0%nat eb pj -∗
      pc_is (mword_of_int (KernelSyms.uartwrite + 0x5a)) -∗
      locked γl cpu_id -∗ a_tx_busy ↦₄ b2 -∗
      uart_tx_own γu l2 -∗ uart_out_lb γu l2 -∗
      uw_full sp0 m0 -∗ uw_buf buf dq f n -∗
      ( uw_next_cont CID0 γl γu j m0 av eb C sp0 buf n f dq i
        ∧ uw_exit_cont CID0 γl γu j m0 av eb C sp0 buf n f dq ) -∗
      WP (Loop : expr riscv_lang)))%I with "[]" as "#Body".
    { iIntros (CIDb Hsbd M2 l2 b2) "%Hregs2 Hcg Hcnt Hpay Hpc Htok Hcell Hown #Hlb Hfull Hbuf Hcont".
      destruct Hregs2 as (Hsp & Hs1 & Hs2 & Hs3 & Hs4 & Hs5 & Hs6 & Hs7 & H24 & H25 & H26 & H27).
      (* --- +0x5a  lbu a5,0(s4) --- *)
      assert (Hlk0 : seq 0 n !! i = Some i) by (apply lookup_seq; split; [lia | exact Hin]).
      iDestruct (big_sepL_lookup_acc (fun _ x => ((pa_add buf x) ↦ₘ{dq} f x)%I) (seq 0 n) i i Hlk0
                   with "Hbuf") as "[Hbyte Hback]".
      assert (Haddrb : add_vec (rget M2 Rs4) (sign_extend' 64 (mword_of_int 0 : mword 12)) = pa_add buf i).
      { rgne. rewrite Hs4. apply uw_addv_0. }
      iApply (wp_lbu_s_sconf (mword_of_int (KernelSyms.uartwrite + 0x5a)) Ra5 Rs4 (mword_of_int 0 : mword 12)
                M2 (av - 10)%nat (f i : mword 8) false (dqm := dq) ltac:(nz) ltac:(rdok)
                with "Hcg Hpc Hi5a [Hbyte] [-]").
      { iEval (rewrite Haddrb). iExact "Hbyte". }
      iApply wp_next_off_intro. iIntros "Hcg Hpc Hbyte".
      iEval (rewrite Haddrb) in "Hbyte".
      iDestruct ("Hback" with "Hbyte") as "Hbuf".
      set (B1 := <[Regidx Ra5 := regval_into_reg (zero_extend' 64 (f i : mword 8))]> M2).
      change (<[Regidx Ra5 := regval_into_reg (zero_extend' 64 (f i : mword 8))]> M2) with B1.
      iEval (rewrite P5e) in "Hpc".
      (* --- the trace re-link, before the push --- *)
      iApply fupd_wp.
      iMod (uart_tx_own_sent_sub γu γv l2 (uw_bytes f i) ⊤ ltac:(solve_ndisj)
              with "Hdinv Hown Hsub") as "[Hown %Hsublist]".
      iModIntro.
      (* --- +0x5e  sb a5,0(s7)  -- the THR write --- *)
      assert (HB1s7 : rget B1 Rs7 = uart_pa 0).
      { rgne. rewrite /B1 upd_ne; [exact Hs7 | reg_neq]. }
      assert (HB1a5 : B1 !!! Regidx Ra5 = zero_extend' 64 (f i : mword 8)) by (rewrite /B1 upd_eq; reflexivity).
      iApply (UAcc.wp_uart_thr_write_s_sconf γu γv (mword_of_int (KernelSyms.uartwrite + 0x5e)) Ra5 Rs7
                B1 (av - 10)%nat l2 false HB1s7 with "Hcg Hpc Hi5e Hdinv Hown Hlb Hdlab").
      iApply wp_next_off_intro. iIntros "Hcg Hpc Hown #Hsent".
      assert (Hsb : (autocast (T := mword) (subrange_vec_dec (rget B1 Ra5)
                       (Z.sub (Z.mul 1 8) 1) 0) : mword 8) = f i).
      { rgne. rewrite HB1a5. apply uw_sub8_zext. }
      iEval (rewrite Hsb) in "Hown". iEval (rewrite Hsb) in "Hsent".
      iAssert (uart_sent_sub γu (uw_bytes f (S i))) as "#Hsub'".
      { rewrite uw_bytes_snoc.
        iApply (uart_sent_sub_snoc γu (uw_bytes f i) l2 (f i) Hsublist with "Hsent"). }
      iEval (rewrite P62) in "Hpc".
      (* --- +0x62  sw s6,0(s1)  -- tx_busy := 1 --- *)
      assert (HB1s1 : B1 !!! Regidx Rs1 = a_tx_busy) by (rewrite /B1 upd_ne; [exact Hs1 | reg_neq]).
      assert (HB1s6 : B1 !!! Regidx Rs6 = (mword_of_int 1 : mword 64))
        by (rewrite /B1 upd_ne; [exact Hs6 | reg_neq]).
      assert (Haddrw : add_vec (rget B1 Rs1) (sign_extend' 64 (mword_of_int 0 : mword 12)) = a_tx_busy).
      { rgne. rewrite HB1s1. apply uw_addv_0. }
      iApply (wp_sw_s_sconf (mword_of_int (KernelSyms.uartwrite + 0x62)) Rs6 Rs1 (mword_of_int 0 : mword 12)
                B1 (av - 10)%nat b2 false with "Hcg Hpc Hi62 [Hcell] [-]").
      { iEval (rewrite Haddrw). iExact "Hcell". }
      iApply wp_next_off_intro. iIntros "Hcg Hpc Hcell".
      iEval (rewrite Haddrw) in "Hcell".
      iEval (rgne) in "Hcell".
      iEval (rewrite HB1s6) in "Hcell".
      iDestruct (tx_res_busy γu (trunc32 (mword_of_int 1 : mword 64)) ((l2 ++ [f i])%list)
                   uw_one_ne_zero with "Hcell Hown") as "Hres".
      iEval (rewrite P66) in "Hpc".
      (* --- +0x66  c.addi s4,s4,1 --- *)
      iApply (wp_caddi_s_sconf (mword_of_int (KernelSyms.uartwrite + 0x66)) Rs4 (mword_of_int 1 : mword 6)
                B1 (av - 10)%nat false ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi66 [-]").
      iApply wp_next_off_intro. iIntros "Hcg Hpc".
      iEval (rgne) in "Hcg".
      set (B2 := <[Regidx Rs4 := regval_into_reg
          (add_vec (B1 !!! Regidx Rs4) (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6))))]> B1).
      change (<[Regidx Rs4 := regval_into_reg
          (add_vec (B1 !!! Regidx Rs4) (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6))))]> B1) with B2.
      iEval (rewrite P68) in "Hpc".
      assert (HB1s4 : B1 !!! Regidx Rs4 = pa_add buf i) by (rewrite /B1 upd_ne; [exact Hs4 | reg_neq]).
      assert (HB2s4 : B2 !!! Regidx Rs4 = pa_add buf (S i)).
      { rewrite /B2 upd_eq HB1s4. apply pa_add_step. pcw. }
      assert (HB2s5 : B2 !!! Regidx Rs5 = pa_add buf n).
      { rewrite /B2 upd_ne; [| reg_neq]. rewrite /B1 upd_ne; [| reg_neq]. exact Hs5. }
      assert (HB2regs : uw_loop_regs m0 B2 (pa_stk sp0 10) buf n (S i)).
      { unfold uw_loop_regs. split_and!;
          first [ exact HB2s4
                | rewrite /B2 upd_ne; [| reg_neq]; rewrite /B1 upd_ne; [| reg_neq]; assumption ]. }
      assert (Hcmp : eq_vec (rget B2 Rs4) (rget B2 Rs5) = Nat.eqb (S i) n).
      { rgne. rgne. rewrite HB2s4 HB2s5. apply pa_add_eqb; [exact HSi64 | exact Hn64]. }
      (* --- +0x68  beq s4,s5 --- *)
      destruct (Nat.eqb (S i) n) eqn:Hend.
      - (* the last byte: leave the loop *)
        assert (Hendn : S i = n) by (apply Nat.eqb_eq; exact Hend).
        iApply (wp_beq_taken_s_sconf (mword_of_int (KernelSyms.uartwrite + 0x68)) (mword_of_int 10 : mword 13)
                  Rs5 Rs4 B2 (av - 10)%nat false ltac:(nz) ltac:(nz) Hcmp
                  ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi68 [-]").
        iNext. iApply wp_next_off_intro. iIntros "Hcg Hpc".
        iEval (rewrite Jexit) in "Hpc".
        subst n.
        iDestruct "Hcont" as "[_ Hexit]".
        rewrite /uw_exit_cont.
        iSpecialize ("Hexit" $! CIDb with "[%]"); [wp_next_chain|].
        iApply ("Hexit" $! B2 with "[%] Hcg Hcnt Hpay Hpc Htok Hres Hsub' Hfull Hbuf").
        exact HB2regs.
      - (* more bytes: back to the head *)
        assert (Hendn : S i <> n) by (intro Hc; rewrite Hc Nat.eqb_refl in Hend; discriminate).
        iApply (wp_beq_fall_s_sconf (mword_of_int (KernelSyms.uartwrite + 0x68)) (mword_of_int 10 : mword 13)
                  Rs5 Rs4 B2 (av - 10)%nat false ltac:(nz) ltac:(nz) Hcmp with "Hcg Hpc Hi68 [-]").
        iApply wp_next_off_intro. iIntros "Hcg Hpc". iEval (rewrite P6c) in "Hpc".
        iDestruct "Hcont" as "[Hnext _]".
        rewrite /uw_next_cont.
        iSpecialize ("Hnext" $! CIDb with "[%]"); [wp_next_chain|].
        iApply ("Hnext" $! B2 with "[%] [%] Hcg Hcnt Hpay Hpc Htok Hres Hsub' Hfull Hbuf").
        + lia.
        + exact HB2regs. }
    (* ================================================================= *)
    (*  THE SLEEP RETRY LOOP: +0x4e .. +0x58 (iLöb over the anchored form) *)
    (* ================================================================= *)
    iAssert (wp_next (CID0 := CID) true pj (fun (CIDs0 : CpuId) =>
      ∀ M1 : regfile,
      ⌜ uw_loop_regs m0 M1 (pa_stk sp0 10) buf n i ⌝ -∗
      sie_cap_gpr M1 (av - 10) false pj -∗
      cpu_own 1%nat eb pj C false -∗ arm_pay 0%nat eb pj -∗
      pc_is (mword_of_int (KernelSyms.uartwrite + 0x4e)) -∗
      locked γl cpu_id -∗ tx_res γu -∗
      uw_full sp0 m0 -∗ uw_buf buf dq f n -∗
      ( uw_next_cont CID0 γl γu j m0 av eb C sp0 buf n f dq i
        ∧ uw_exit_cont CID0 γl γu j m0 av eb C sp0 buf n f dq ) -∗
      WP (Loop : expr riscv_lang)))%I with "[]" as "Sleep".
    { iLöb as "IH".
      iIntros (CIDs0 Hss0 M1) "%Hregs1 Hcg Hcnt Hpay Hpc Htok Hres Hfull Hbuf Hcont".
      pose proof Hregs1 as Hregs1'.
      destruct Hregs1' as (Hsp & Hs1 & Hs2 & Hs3 & Hs4 & Hs5 & Hs6 & Hs7 & H24 & H25 & H26 & H27).
      (* --- +0x4e  c.mv a1,s3 --- *)
      iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.uartwrite + 0x4e)) Ra1 Rs3 M1 (av - 10)%nat false
                ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi4e [-]").
      iApply wp_next_off_intro. iIntros "Hcg Hpc". iEval (rgne) in "Hcg".
      set (S1 := <[Regidx Ra1 := regval_into_reg (add_vec zero_reg (M1 !!! Regidx Rs3))]> M1).
      change (<[Regidx Ra1 := regval_into_reg (add_vec zero_reg (M1 !!! Regidx Rs3))]> M1) with S1.
      iEval (rewrite P50) in "Hpc".
      (* --- +0x50  c.mv a0,s2 --- *)
      iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.uartwrite + 0x50)) Ra0 Rs2 S1 (av - 10)%nat false
                ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi50 [-]").
      iApply wp_next_off_intro. iIntros "Hcg Hpc". iEval (rgne) in "Hcg".
      set (S2 := <[Regidx Ra0 := regval_into_reg (add_vec zero_reg (S1 !!! Regidx Rs2))]> S1).
      change (<[Regidx Ra0 := regval_into_reg (add_vec zero_reg (S1 !!! Regidx Rs2))]> S1) with S2.
      iEval (rewrite P52) in "Hpc".
      (* --- +0x52  jal ra,sleep --- *)
      iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.uartwrite + 0x52)) Rra (mword_of_int 5602 : mword 21)
                S2 (av - 10)%nat false ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi52 [-]").
      iApply wp_next_off_intro. iIntros "Hcg Hpc".
      set (S3 := <[Regidx Rra := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.uartwrite + 0x52) : mword 64) 4)]> S2).
      change (<[Regidx Rra := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.uartwrite + 0x52) : mword 64) 4)]> S2) with S3.
      iEval (rewrite Jcall) in "Hpc".
      assert (HS3a1 : S3 !!! Regidx Ra1 = a_tx_lock).
      { rewrite /S3 upd_ne; [| reg_neq]. rewrite /S2 upd_ne; [| reg_neq].
        rewrite /S1 upd_eq. rewrite uw_zero_reg_add. exact Hs3. }
      assert (HS3ra : S3 !!! Regidx Rra = add_vec_int (mword_of_int (KernelSyms.uartwrite + 0x52) : mword 64) 4)
        by (rewrite /S3 upd_eq; reflexivity).
      iApply (Sleep.wp_sleep_sconf γs j γlp γl a_tx_lock "uart"%string (tx_res γu)
                S3 (av - 10)%nat eb C Hj Hjlp
                ltac:(rewrite HS3a1; apply uw_addv_0) Heb
                ltac:(unfold uartwrite_stack in Hav; lia)
                with "Hcg Hcnt Hpay Ht Hpc Hpinv [Hlk] Htok Hres Hpanic [-]").
      { iExact "Hlk". }
      iIntros (CIDs Hss Ms) "%Hscs Hcg Hcnt Hpay Hpc Htok Hres".
      iEval (rewrite HS3ra P56) in "Hpc".
      assert (HcsS3 : callee_saved M1 S3).
      { rewrite /S3 /S2 /S1.
        apply callee_saved_insert_r; [vm_compute; reflexivity|].
        apply callee_saved_insert_r; [vm_compute; reflexivity|].
        apply callee_saved_insert_r; [vm_compute; reflexivity|].
        apply callee_saved_refl. }
      assert (HregsS : uw_loop_regs m0 Ms (pa_stk sp0 10) buf n i).
      { apply (uw_loop_regs_cs m0 S3 Ms); [exact Hscs|].
        apply (uw_loop_regs_cs m0 M1 S3); [exact HcsS3 | exact Hregs1]. }
      pose proof HregsS as HregsS'.
      destruct HregsS' as (Wsp & Ws1 & Ws2 & Ws3 & Ws4 & Ws5 & Ws6 & Ws7 & W24 & W25 & W26 & W27).
      (* --- +0x56  c.lw a5,0(s1) --- *)
      iDestruct "Hres" as (b l) "(Hcell & Hown & Hwand)".
      assert (Haddrc : add_vec (rget Ms Rs1)
                (sign_extend' 64 (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 5) ('b"00")))) = a_tx_busy).
      { rgne. rewrite Ws1 /a_tx_busy. apply bv_eq; vm_compute; reflexivity. }
      iApply (wp_clw_s_sconf (mword_of_int (KernelSyms.uartwrite + 0x56)) Ra5 Rs1
                (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 5) ('b"00")))
                Ms (av - 10)%nat b false (dqm := DfracOwn 1) ltac:(nz) ltac:(rdok)
                with "Hcg Hpc Hi56 [Hcell] [-]").
      { iEval (rewrite Haddrc). iExact "Hcell". }
      iApply wp_next_off_intro. iIntros "Hcg Hpc Hcell". iEval (rewrite Haddrc) in "Hcell".
      set (S4 := <[Regidx Ra5 := regval_into_reg (sign_extend' 64 b)]> Ms).
      change (<[Regidx Ra5 := regval_into_reg (sign_extend' 64 b)]> Ms) with S4.
      iEval (rewrite P58) in "Hpc".
      assert (HS4a5 : S4 !!! Regidx Ra5 = sign_extend' 64 b) by (rewrite /S4 upd_eq; reflexivity).
      assert (HS4regs : uw_loop_regs m0 S4 (pa_stk sp0 10) buf n i).
      { unfold uw_loop_regs. split_and!;
          (rewrite /S4 upd_ne; [| reg_neq]); assumption. }
      (* --- +0x58  c.bnez a5 --- *)
      destruct (eq_vec (sign_extend' 64 b : mword 64) (zero_reg : mword 64)) eqn:Hbz.
      + (* tx_busy == 0: fall through into the body *)
        assert (Hb0 : b = (mword_of_int 0 : mword 32)) by (apply uw_sext_zero; exact Hbz).
        iApply (wp_cbnez_fall_s_sconf (mword_of_int (KernelSyms.uartwrite + 0x58)) (mword_of_int 251 : mword 8)
                  (Cregidx (mword_of_int 7)) Ra5 S4 (av - 10)%nat false uw_cr7 ltac:(nz)
                  ltac:(rgne; rewrite HS4a5; unfold neq_vec; rewrite Hbz; reflexivity)
                  with "Hcg Hpc Hi58 [-]").
        iApply wp_next_off_intro. iIntros "Hcg Hpc". iEval (rewrite P5a) in "Hpc".
        iDestruct ("Hwand" with "[%]") as "#Hlb"; [exact Hb0|].
        iSpecialize ("Body" $! CIDs with "[%]"); [wp_next_chain|].
        iApply ("Body" $! S4 l b with "[%] Hcg Hcnt Hpay Hpc Htok Hcell Hown Hlb Hfull Hbuf Hcont").
        exact HS4regs.
      + (* still busy: sleep again *)
        assert (Hbne : b <> (mword_of_int 0 : mword 32)) by (apply uw_sext_nonzero; exact Hbz).
        iDestruct (tx_res_busy γu b l Hbne with "Hcell Hown") as "Hres".
        iApply (wp_cbnez_taken_s_sconf (mword_of_int (KernelSyms.uartwrite + 0x58)) (mword_of_int 251 : mword 8)
                  (Cregidx (mword_of_int 7)) Ra5 S4 (av - 10)%nat false uw_cr7 ltac:(nz)
                  ltac:(rgne; rewrite HS4a5; unfold neq_vec; rewrite Hbz; reflexivity)
                  ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc Hi58 [-]").
        iNext. iApply wp_next_off_intro. iIntros "Hcg Hpc".
        iEval (rewrite Jsleep1) in "Hpc".
        iSpecialize ("IH" $! CIDs with "[%]"); [wp_next_chain|].
        iApply ("IH" $! S4 with "[%] Hcg Hcnt Hpay Hpc Htok Hres Hfull Hbuf Hcont").
        exact HS4regs. }
    (* ================================================================= *)
    (*  THE HEAD: +0x6c .. +0x70.                                         *)
    (* ================================================================= *)
    pose proof Hregs as Hregs'.
    destruct Hregs' as (Hsp & Hs1 & Hs2 & Hs3 & Hs4 & Hs5 & Hs6 & Hs7 & H24 & H25 & H26 & H27).
    iDestruct "Hres" as (b l) "(Hcell & Hown & Hwand)".
    assert (Haddrc : add_vec (rget M Rs1)
              (sign_extend' 64 (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 5) ('b"00")))) = a_tx_busy).
    { rgne. rewrite Hs1 /a_tx_busy. apply bv_eq; vm_compute; reflexivity. }
    iApply (wp_clw_s_sconf (mword_of_int (KernelSyms.uartwrite + 0x6c)) Ra5 Rs1
              (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 5) ('b"00")))
              M (av - 10)%nat b false (dqm := DfracOwn 1) ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hi6c [Hcell] [-]").
    { iEval (rewrite Haddrc). iExact "Hcell". }
    iApply wp_next_off_intro. iIntros "Hcg Hpc Hcell". iEval (rewrite Haddrc) in "Hcell".
    set (H1 := <[Regidx Ra5 := regval_into_reg (sign_extend' 64 b)]> M).
    change (<[Regidx Ra5 := regval_into_reg (sign_extend' 64 b)]> M) with H1.
    iEval (rewrite P6e) in "Hpc".
    assert (HH1a5 : H1 !!! Regidx Ra5 = sign_extend' 64 b) by (rewrite /H1 upd_eq; reflexivity).
    assert (HH1regs : uw_loop_regs m0 H1 (pa_stk sp0 10) buf n i).
    { unfold uw_loop_regs. split_and!; (rewrite /H1 upd_ne; [| reg_neq]); assumption. }
    destruct (eq_vec (sign_extend' 64 b : mword 64) (zero_reg : mword 64)) eqn:Hbz.
    - (* tx_busy == 0: straight to the body via the +0x70 jump *)
      assert (Hb0 : b = (mword_of_int 0 : mword 32)) by (apply uw_sext_zero; exact Hbz).
      iApply (wp_cbnez_fall_s_sconf (mword_of_int (KernelSyms.uartwrite + 0x6e)) (mword_of_int 240 : mword 8)
                (Cregidx (mword_of_int 7)) Ra5 H1 (av - 10)%nat false uw_cr7 ltac:(nz)
                ltac:(rgne; rewrite HH1a5; unfold neq_vec; rewrite Hbz; reflexivity)
                with "Hcg Hpc Hi6e [-]").
      iApply wp_next_off_intro. iIntros "Hcg Hpc". iEval (rewrite P70) in "Hpc".
      iApply (wp_cj_s_sconf (mword_of_int (KernelSyms.uartwrite + 0x70))
                (sign_extend' 21 (concat_vec (mword_of_int 2037 : mword 11) ('b"0")))
                H1 (av - 10)%nat false ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi70 [-]").
      iApply wp_next_off_intro. iNext. iIntros "Hcg Hpc".
      iEval (rewrite Jbody) in "Hpc".
      iDestruct ("Hwand" with "[%]") as "#Hlb"; [exact Hb0|].
      iSpecialize ("Body" $! CID with "[%]"); [wp_next_chain|].
      iApply ("Body" $! H1 l b with "[%] Hcg Hcnt Hpay Hpc Htok Hcell Hown Hlb Hfull Hbuf Hcont").
      exact HH1regs.
    - (* busy: into the sleep loop *)
      assert (Hbne : b <> (mword_of_int 0 : mword 32)) by (apply uw_sext_nonzero; exact Hbz).
      iDestruct (tx_res_busy γu b l Hbne with "Hcell Hown") as "Hres".
      iApply (wp_cbnez_taken_s_sconf (mword_of_int (KernelSyms.uartwrite + 0x6e)) (mword_of_int 240 : mword 8)
                (Cregidx (mword_of_int 7)) Ra5 H1 (av - 10)%nat false uw_cr7 ltac:(nz)
                ltac:(rgne; rewrite HH1a5; unfold neq_vec; rewrite Hbz; reflexivity)
                ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi6e [-]").
      iNext. iApply wp_next_off_intro. iIntros "Hcg Hpc".
      iEval (rewrite Jsleep2) in "Hpc".
      iSpecialize ("Sleep" $! CID with "[%]"); [wp_next_chain|].
      iApply ("Sleep" $! H1 with "[%] Hcg Hcnt Hpay Hpc Htok Hres Hfull Hbuf Hcont").
      exact HH1regs.
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  THE LOOP: induction on the bytes still to go.                       *)
  (* ------------------------------------------------------------------ *)
  (* The head is only ever entered with at least one byte left ([i + S k =
     n]).  The conclusion IS a [wp_next], so the induction hypothesis is
     re-enterable at whatever hart the next park lands on. *)
  Lemma uw_iter `{GEN : GenId} (CID0 : CPU)
      (γl : gname) (γu : uart_names) (γv : disk_names)
      (γs : list gname) (j : nat) (γlp : gname)
      (m0 : regfile) (av : nat) (eb : bool) (C : iProp Σ)
      (sp0 buf : mword 64) (n : nat) (f : nat -> bv 8) (dq : dfrac) (k : nat) :
    (Z.of_nat n < 2 ^ 31)%Z ->
    (j < NPROC)%nat -> γs !! j = Some γlp ->
    (uartwrite_stack <= av)%nat ->
    eb = true ->
    forall i : nat, (i + S k)%nat = n ->
    ⊢ kernel_text -∗ dev_inv γu γv -∗ is_txlock γl γu -∗
      procs_inv γs -∗ panic_wp_any -∗
      uw_head CID0 γl γu j m0 av eb C sp0 buf n f dq i.
  Proof.
    intros Hn31 Hj Hjlp Hav Heb.
    induction k as [|k IH].
    - intros i Hik. iIntros "#Ht #Hdinv #Htxl #Hpinv #Hpanic".
      rewrite /uw_head.
      iIntros (CIDh Hsh M) "%Hregs Hcg Hcnt Hpay Hpc Htok Hres #Hsub Hfull Hbuf Hexit".
      iApply (uw_one (CID := CIDh) CID0 γl γu γv γs j γlp m0 M av eb C sp0 buf n f dq i
                ltac:(lia) Hn31 Hj Hjlp Hav Heb Hsh Hregs
                with "Ht Hdinv Htxl Hpinv Hpanic Hcg Hcnt Hpay Hpc Htok Hres Hsub Hfull Hbuf [Hexit]").
      iSplit.
      + (* the back edge is dead: this was the last byte *)
        rewrite /uw_next_cont. iIntros (CIDx Hsx M') "%Hlt". exfalso. lia.
      + iExact "Hexit".
    - intros i Hik. iIntros "#Ht #Hdinv #Htxl #Hpinv #Hpanic".
      rewrite /uw_head.
      iIntros (CIDh Hsh M) "%Hregs Hcg Hcnt Hpay Hpc Htok Hres #Hsub Hfull Hbuf Hexit".
      iApply (uw_one (CID := CIDh) CID0 γl γu γv γs j γlp m0 M av eb C sp0 buf n f dq i
                ltac:(lia) Hn31 Hj Hjlp Hav Heb Hsh Hregs
                with "Ht Hdinv Htxl Hpinv Hpanic Hcg Hcnt Hpay Hpc Htok Hres Hsub Hfull Hbuf [Hexit]").
      iSplit.
      + rewrite /uw_next_cont.
        iIntros (CIDx Hsx M') "%Hlt %Hregs' Hcg Hcnt Hpay Hpc Htok Hres #Hsub' Hfull Hbuf".
        iPoseProof (IH (S i) ltac:(lia) with "Ht Hdinv Htxl Hpinv Hpanic") as "Next".
        rewrite /uw_head.
        iSpecialize ("Next" $! CIDx with "[%]"); [wp_next_chain|].
        iApply ("Next" $! M' with "[%] Hcg Hcnt Hpay Hpc Htok Hres Hsub' Hfull Hbuf Hexit").
        exact Hregs'.
      + iExact "Hexit".
  Qed.

End UwBodies.

(* ===================================================================== *)

Section ProofUartwrite.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !irefNameG Σ, !irefslotG Σ}.
  Context `{!uartGhostG Σ, !diskGhostG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Lemma wp_uartwrite_sconf (γu : uart_names) (γv : disk_names)
      (γs : list gname) (j : nat) (γlp : gname) (γl : gname)
      (m : regfile) (av : nat) (eb : bool) (C : iProp Σ)
      (n : nat) (f : nat -> bv 8) (dq : dfrac) (b : bool)
    : wp_uartwrite_sconf_body γu γv γs j γlp γl m av eb C n f dq b.
  Proof.
    cbv beta delta [wp_uartwrite_sconf_body].
    intros pcE pj buf ret_tgt Hj Hjlp Ha1 Hn31 Hav Heb.
    iIntros "Hcg Hcnt #Ht Hpc #Hdinv #Htxl Hbuf #Hpinv #Hpanic Hcont".
    iDestruct (is_txlock_lock with "Htxl") as "#Hlk".
    (* level 0 with an enabled base forces the enabled index *)
    iDestruct (cpu_own_eb_agree with "Hcg Hcnt") as %Hbm.
    assert (Hbt : b = true) by (rewrite -Hbm; exact Heb).
    clear Hbm. subst b.
    assert (H231 : (2 ^ 31 = 2147483648)%Z) by (vm_compute; reflexivity).
    rewrite H231 in Hn31.
    pose (sp0 := (m !!! Regidx csp_rs1 : mword 64)).
    assert (Hspm : m !!! Regidx csp_rs1 = sp0) by reflexivity.
    set (spd := pa_stk sp0 10%nat).
    iPoseProof (uwi_00 with "Ht") as "Hi00".
    iPoseProof (uwi_02 with "Ht") as "Hi02".
    iPoseProof (uwi_04 with "Ht") as "Hi04".
    iPoseProof (uwi_06 with "Ht") as "Hi06".
    iPoseProof (uwi_08 with "Ht") as "Hi08".
    iPoseProof (uwi_0a with "Ht") as "Hi0a".
    iPoseProof (uwi_0c with "Ht") as "Hi0c".
    iPoseProof (uwi_0e with "Ht") as "Hi0e".
    iPoseProof (uwi_10 with "Ht") as "Hi10".
    iPoseProof (uwi_14 with "Ht") as "Hi14".
    iPoseProof (uwi_18 with "Ht") as "Hi18".
    iPoseProof (uwi_1c with "Ht") as "Hi1c".
    assert (P02 : add_vec_int (pcE : mword 64) 2 = mword_of_int (KernelSyms.uartwrite + 0x02)) by pcw.
    assert (P04 : add_vec_int (mword_of_int (KernelSyms.uartwrite + 0x02) : mword 64) 2 = mword_of_int (KernelSyms.uartwrite + 0x04)) by pcw.
    assert (P06 : add_vec_int (mword_of_int (KernelSyms.uartwrite + 0x04) : mword 64) 2 = mword_of_int (KernelSyms.uartwrite + 0x06)) by pcw.
    assert (P08 : add_vec_int (mword_of_int (KernelSyms.uartwrite + 0x06) : mword 64) 2 = mword_of_int (KernelSyms.uartwrite + 0x08)) by pcw.
    assert (P0a : add_vec_int (mword_of_int (KernelSyms.uartwrite + 0x08) : mword 64) 2 = mword_of_int (KernelSyms.uartwrite + 0x0a)) by pcw.
    assert (P0c : add_vec_int (mword_of_int (KernelSyms.uartwrite + 0x0a) : mword 64) 2 = mword_of_int (KernelSyms.uartwrite + 0x0c)) by pcw.
    assert (P0e : add_vec_int (mword_of_int (KernelSyms.uartwrite + 0x0c) : mword 64) 2 = mword_of_int (KernelSyms.uartwrite + 0x0e)) by pcw.
    assert (P10 : add_vec_int (mword_of_int (KernelSyms.uartwrite + 0x0e) : mword 64) 2 = mword_of_int (KernelSyms.uartwrite + 0x10)) by pcw.
    assert (P14 : add_vec_int (mword_of_int (KernelSyms.uartwrite + 0x10) : mword 64) 4 = mword_of_int (KernelSyms.uartwrite + 0x14)) by pcw.
    assert (P18 : add_vec_int (mword_of_int (KernelSyms.uartwrite + 0x14) : mword 64) 4 = mword_of_int (KernelSyms.uartwrite + 0x18)) by pcw.
    assert (P1c : ret_pc (add_vec_int (mword_of_int (KernelSyms.uartwrite + 0x18) : mword 64) 4) = mword_of_int (KernelSyms.uartwrite + 0x1c)) by pcw.
    (* ============ PROLOGUE: the 10-slot frame ============ *)
    assert (Hpush : add_vec (m !!! Regidx csp_rs1)
                      (sign_extend' 64 (caddi16sp_imm (mword_of_int 59 : mword 6)))
                    = pa_stk (m !!! Regidx csp_rs1) 10%nat).
    { unfold pa_stk, add_vec_int. apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    iApply (wp_caddi16sp_push_s_sconf pcE (mword_of_int 59 : mword 6) m av 10%nat true
              ltac:(unfold uartwrite_stack in Hav; lia) Hpush with "Hcg Hpc Hi00 [-]").
    iIntros (CID1 Hs1) "Hcg Hframe Hpc".
    iEval (rewrite Hspm) in "Hframe".
    set (A0 := <[Regidx csp_rs1 := regval_into_reg
        (add_vec (m !!! Regidx csp_rs1)
           (sign_extend' 64 (caddi16sp_imm (mword_of_int 59 : mword 6))))]> m).
    change (<[Regidx csp_rs1 := regval_into_reg
        (add_vec (m !!! Regidx csp_rs1)
           (sign_extend' 64 (caddi16sp_imm (mword_of_int 59 : mword 6))))]> m) with A0.
    assert (HcspA0 : A0 !!! Regidx csp_rs1 = spd)
      by (rewrite /A0 upd_eq Hpush Hspm; reflexivity).
    iEval (rewrite P02) in "Hpc".
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
    (* +0x02 c.sdsp ra,72(sp) *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.uartwrite + 0x02)) (mword_of_int 9 : mword 6) Rra
              A0 (av - 10)%nat v1 true with "Hcg Hpc Hi02 [H1] [-]").
    { iEval (rewrite HcspA0 Hb1). iExact "H1". }
    iIntros (CID2 Hs2) "Hcg Hpc H1". iEval (rewrite HcspA0 Hb1) in "H1".
    iEval (rgne) in "H1".
    iEval (rewrite P04) in "Hpc".
    (* +0x04 c.sdsp s0,64(sp) *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.uartwrite + 0x04)) (mword_of_int 8 : mword 6) Rs0
              A0 (av - 10)%nat v2 true with "Hcg Hpc Hi04 [H2] [-]").
    { iEval (rewrite HcspA0 Hb2). iExact "H2". }
    iIntros (CID3 Hs3) "Hcg Hpc H2". iEval (rewrite HcspA0 Hb2) in "H2".
    iEval (rgne) in "H2".
    iEval (rewrite P06) in "Hpc".
    (* +0x06 c.sdsp s1,56(sp) *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.uartwrite + 0x06)) (mword_of_int 7 : mword 6) Rs1
              A0 (av - 10)%nat v3 true with "Hcg Hpc Hi06 [H3] [-]").
    { iEval (rewrite HcspA0 Hb3). iExact "H3". }
    iIntros (CID4 Hs4) "Hcg Hpc H3". iEval (rewrite HcspA0 Hb3) in "H3".
    iEval (rgne) in "H3".
    iEval (rewrite P08) in "Hpc".
    (* +0x08 c.sdsp s5,24(sp) *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.uartwrite + 0x08)) (mword_of_int 3 : mword 6) Rs5
              A0 (av - 10)%nat v7 true with "Hcg Hpc Hi08 [H7] [-]").
    { iEval (rewrite HcspA0 Hb7). iExact "H7". }
    iIntros (CID5 Hs5) "Hcg Hpc H7". iEval (rewrite HcspA0 Hb7) in "H7".
    iEval (rgne) in "H7".
    iEval (rewrite P0a) in "Hpc".
    assert (HA0ra : A0 !!! Regidx Rra = m !!! Regidx Rra)
      by (rewrite /A0 upd_ne; [reflexivity | reg_neq]).
    assert (HA0s0 : A0 !!! Regidx Rs0 = m !!! Regidx Rs0)
      by (rewrite /A0 upd_ne; [reflexivity | reg_neq]).
    assert (HA0s1 : A0 !!! Regidx Rs1 = m !!! Regidx Rs1)
      by (rewrite /A0 upd_ne; [reflexivity | reg_neq]).
    assert (HA0s5 : A0 !!! Regidx Rs5 = m !!! Regidx Rs5)
      by (rewrite /A0 upd_ne; [reflexivity | reg_neq]).
    iEval (rewrite HA0ra) in "H1". iEval (rewrite HA0s0) in "H2".
    iEval (rewrite HA0s1) in "H3". iEval (rewrite HA0s5) in "H7".
    (* +0x0a c.addi4spn s0,sp,80 *)
    iApply (wp_caddi4spn_s_sconf (mword_of_int (KernelSyms.uartwrite + 0x0a)) (Cregidx (mword_of_int 0))
              (mword_of_int 20 : mword 8) Rs0 A0 (av - 10)%nat true
              ltac:(vm_compute; reflexivity) ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hi0a [-]").
    iIntros (CID6 Hs6) "Hcg Hpc".
    set (A1 := <[Regidx Rs0 := regval_into_reg
        (add_vec (A0 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 20 : mword 8))))]> A0).
    change (<[Regidx Rs0 := regval_into_reg
        (add_vec (A0 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 20 : mword 8))))]> A0) with A1.
    iEval (rewrite P0c) in "Hpc".
    (* +0x0c c.mv s5,a0 *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.uartwrite + 0x0c)) Rs5 Ra0 A1 (av - 10)%nat true
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi0c [-]").
    iIntros (CID7 Hs7) "Hcg Hpc". iEval (rgne) in "Hcg".
    set (A2 := <[Regidx Rs5 := regval_into_reg (add_vec zero_reg (A1 !!! Regidx Ra0))]> A1).
    change (<[Regidx Rs5 := regval_into_reg (add_vec zero_reg (A1 !!! Regidx Ra0))]> A1) with A2.
    iEval (rewrite P0e) in "Hpc".
    (* +0x0e c.mv s1,a1 *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.uartwrite + 0x0e)) Rs1 Ra1 A2 (av - 10)%nat true
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi0e [-]").
    iIntros (CID8 Hs8) "Hcg Hpc". iEval (rgne) in "Hcg".
    set (A3 := <[Regidx Rs1 := regval_into_reg (add_vec zero_reg (A2 !!! Regidx Ra1))]> A2).
    change (<[Regidx Rs1 := regval_into_reg (add_vec zero_reg (A2 !!! Regidx Ra1))]> A2) with A3.
    iEval (rewrite P10) in "Hpc".
    (* +0x10 auipc a0,0x12 / +0x14 addi a0,a0,-1500 *)
    iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.uartwrite + 0x10)) Ra0 (mword_of_int 18 : mword 20)
              A3 (av - 10)%nat true ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi10 [-]").
    iIntros (CID9 Hs9) "Hcg Hpc".
    set (A4 := <[Regidx Ra0 := regval_into_reg
        (add_vec (mword_of_int (KernelSyms.uartwrite + 0x10) : mword 64) (auipc_off (mword_of_int 18 : mword 20)))]> A3).
    change (<[Regidx Ra0 := regval_into_reg
        (add_vec (mword_of_int (KernelSyms.uartwrite + 0x10) : mword 64) (auipc_off (mword_of_int 18 : mword 20)))]> A3) with A4.
    iEval (rewrite P14) in "Hpc".
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.uartwrite + 0x14)) Ra0 Ra0 (mword_of_int 0xa24 : mword 12)
              A4 (av - 10)%nat true ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi14 [-]").
    iIntros (CID10 Hs10) "Hcg Hpc". iEval (rgne) in "Hcg".
    set (A5 := <[Regidx Ra0 := regval_into_reg
        (add_vec (A4 !!! Regidx Ra0) (sign_extend' 64 (mword_of_int 0xa24 : mword 12)))]> A4).
    change (<[Regidx Ra0 := regval_into_reg
        (add_vec (A4 !!! Regidx Ra0) (sign_extend' 64 (mword_of_int 0xa24 : mword 12)))]> A4) with A5.
    iEval (rewrite P18) in "Hpc".
    (* +0x18 jal ra,acquire *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.uartwrite + 0x18)) Rra (mword_of_int 788 : mword 21)
              A5 (av - 10)%nat true ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi18 [-]").
    iIntros (CID11 Hs11) "Hcg Hpc".
    set (A6 := <[Regidx Rra := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.uartwrite + 0x18) : mword 64) 4)]> A5).
    change (<[Regidx Rra := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.uartwrite + 0x18) : mword 64) 4)]> A5) with A6.
    assert (Hjacq : add_vec (mword_of_int (KernelSyms.uartwrite + 0x18) : mword 64)
                      (sign_extend' 64 (mword_of_int 788 : mword 21)) = mword_of_int KernelSyms.acquire) by pcw.
    iEval (rewrite Hjacq) in "Hpc".
    (* the register facts acquire needs, and the ones that survive it *)
    assert (HA6a0 : A6 !!! Regidx Ra0 = a_tx_lock).
    { rewrite /A6 upd_ne; [| reg_neq]. rewrite /A5 upd_eq. rewrite /A4 upd_eq.
      rewrite /a_tx_lock. pcw. }
    assert (HA6csp : A6 !!! Regidx csp_rs1 = spd).
    { rewrite /A6 upd_ne; [| reg_neq]. rewrite /A5 upd_ne; [| reg_neq].
      rewrite /A4 upd_ne; [| reg_neq]. rewrite /A3 upd_ne; [| reg_neq].
      rewrite /A2 upd_ne; [| reg_neq]. rewrite /A1 upd_ne; [| reg_neq]. exact HcspA0. }
    assert (HA6ra : A6 !!! Regidx Rra = add_vec_int (mword_of_int (KernelSyms.uartwrite + 0x18) : mword 64) 4)
      by (rewrite /A6 upd_eq; reflexivity).
    assert (HA6s1 : A6 !!! Regidx Rs1 = (mword_of_int (Z.of_nat n) : mword 64)).
    { rewrite /A6 upd_ne; [| reg_neq]. rewrite /A5 upd_ne; [| reg_neq].
      rewrite /A4 upd_ne; [| reg_neq]. rewrite /A3 upd_eq. rewrite uw_zero_reg_add.
      rewrite /A2 upd_ne; [| reg_neq]. rewrite /A1 upd_ne; [| reg_neq].
      rewrite /A0 upd_ne; [| reg_neq]. exact Ha1. }
    assert (HA6s5 : A6 !!! Regidx Rs5 = buf).
    { rewrite /A6 upd_ne; [| reg_neq]. rewrite /A5 upd_ne; [| reg_neq].
      rewrite /A4 upd_ne; [| reg_neq]. rewrite /A3 upd_ne; [| reg_neq].
      rewrite /A2 upd_eq. rewrite uw_zero_reg_add.
      rewrite /A1 upd_ne; [| reg_neq]. rewrite /A0 upd_ne; [| reg_neq]. reflexivity. }
    assert (HA6oth : forall r : mword 5,
              r <> csp_rs1 -> r <> Rra -> r <> Rs0 -> r <> Rs1 -> r <> Rs5 -> r <> Ra0 ->
              A6 !!! Regidx r = m !!! Regidx r).
    { intros r N2 N1 N8 N9 N21 N10.
      rewrite /A6 upd_ne; [| congruence]. rewrite /A5 upd_ne; [| congruence].
      rewrite /A4 upd_ne; [| congruence]. rewrite /A3 upd_ne; [| congruence].
      rewrite /A2 upd_ne; [| congruence]. rewrite /A1 upd_ne; [| congruence].
      rewrite /A0 upd_ne; [| congruence]. reflexivity. }
    (* ============ acquire(&tx_lock) ============ *)
    iDestruct (cpu_own_transport CID CID11 0 eb pj C true ltac:(wp_next_chain)
                 with "Hcnt") as "Hcnt".
    iApply (Acquire.wp_acquire_sconf γl "uart"%string (tx_res γu) A6
              0%nat eb pj C (av - 10)%nat true ltac:(lia)
              ltac:(unfold uartwrite_stack in Hav; lia)
              with "Hcg Hcnt Ht Hpc [Hlk] Hpanic [-]").
    { iEval (rewrite HA6a0). iExact "Hlk". }
    iIntros (CIDa Hsa ms MA) "%Hms Hcg Hpc %HcsA Htok HR Hcnt Hpay".
    iEval (rewrite HA6ra P1c) in "Hpc".
    (* the opening trace snapshot: what the n = 0 path returns *)
    iDestruct "HR" as (b0 l0) "(Hcell & Hown & Hwand)".
    iApply fupd_wp.
    iMod (uart_tx_own_snapshot γu γv l0 ⊤ ltac:(solve_ndisj) with "Hdinv Hown") as "[Hown #Hsnap]".
    iModIntro.
    iDestruct (uart_sent_sub_nil γu l0 with "Hsnap") as "#Hsub0".
    iAssert (tx_res γu) with "[Hcell Hown Hwand]" as "HR".
    { iExists b0, l0. iFrame "Hcell Hown Hwand". }
    (* the callee-saved facts that survive acquire *)
    assert (HMAcsp : MA !!! Regidx csp_rs1 = spd)
      by (rewrite (callee_saved_lookup HcsA csp_rs1 ltac:(vm_compute; reflexivity)); exact HA6csp).
    assert (HMAs1 : MA !!! Regidx Rs1 = (mword_of_int (Z.of_nat n) : mword 64))
      by (rewrite (callee_saved_lookup HcsA (mword_of_int 9) ltac:(vm_compute; reflexivity)); exact HA6s1).
    assert (HMAs5 : MA !!! Regidx Rs5 = buf)
      by (rewrite (callee_saved_lookup HcsA (mword_of_int 21) ltac:(vm_compute; reflexivity)); exact HA6s5).
    assert (HMAoth : forall r : mword 5, is_cs_idx r = true ->
              r <> csp_rs1 -> r <> Rra -> r <> Rs0 -> r <> Rs1 -> r <> Rs5 -> r <> Ra0 ->
              MA !!! Regidx r = m !!! Regidx r).
    { intros r Hr N2 N1 N8 N9 N21 N10.
      rewrite (callee_saved_lookup HcsA r Hr). apply HA6oth; assumption. }
    assert (HMAs2 : MA !!! Regidx Rs2 = m !!! Regidx Rs2)
      by (apply HMAoth; first [vm_compute; reflexivity | reg_neq]).
    assert (HMAs3 : MA !!! Regidx Rs3 = m !!! Regidx Rs3)
      by (apply HMAoth; first [vm_compute; reflexivity | reg_neq]).
    assert (HMAs4 : MA !!! Regidx Rs4 = m !!! Regidx Rs4)
      by (apply HMAoth; first [vm_compute; reflexivity | reg_neq]).
    assert (HMAs6 : MA !!! Regidx Rs6 = m !!! Regidx Rs6)
      by (apply HMAoth; first [vm_compute; reflexivity | reg_neq]).
    assert (HMAs7 : MA !!! Regidx Rs7 = m !!! Regidx Rs7)
      by (apply HMAoth; first [vm_compute; reflexivity | reg_neq]).
    assert (HMAs8 : MA !!! Regidx Rs8 = m !!! Regidx Rs8)
      by (apply HMAoth; first [vm_compute; reflexivity | reg_neq]).
    assert (HMAs9 : MA !!! Regidx Rs9 = m !!! Regidx Rs9)
      by (apply HMAoth; first [vm_compute; reflexivity | reg_neq]).
    assert (HMAs10 : MA !!! Regidx Rs10 = m !!! Regidx Rs10)
      by (apply HMAoth; first [vm_compute; reflexivity | reg_neq]).
    assert (HMAs11 : MA !!! Regidx Rs11 = m !!! Regidx Rs11)
      by (apply HMAoth; first [vm_compute; reflexivity | reg_neq]).
    (* the tail's frame and register shape, shared by both paths *)
    iAssert (uw_saved sp0 m) with "[H1 H2 H3 H7]" as "Hsv".
    { rewrite /uw_saved. iFrame "H1 H2 H3 H7". }
    iAssert (uw_slot10 sp0) with "[H10]" as "Hs10". { by iExists v10. }
    iAssert (uw_buf buf dq f n) with "[Hbuf]" as "Hbuf". { rewrite /uw_buf. iExact "Hbuf". }
    (* ============ +0x1c  blez s1 ============ *)
    assert (Hcmp0 : zopz0zKzJ_s (zero_reg : mword 64) (rget MA Rs1) = Z.geb 0 (Z.of_nat n)).
    { rgne. rewrite HMAs1. apply uw_geb_s0. assert (H263 : (2 ^ 63 = 9223372036854775808)%Z)
        by (vm_compute; reflexivity). rewrite H263. lia. }
    destruct (Z.geb 0 (Z.of_nat n)) eqn:Hb0z.
    - (* ======== n = 0: straight to the epilogue ======== *)
      assert (Hn0 : n = 0%nat).
      { assert (Hx := Hb0z). rewrite Z.geb_leb in Hx. apply Z.leb_le in Hx. lia. }
      subst n.
      assert (Hal : eq_vec (access_vec_dec (add_vec (mword_of_int (KernelSyms.uartwrite + 0x1c) : mword 64)
                      (sign_extend' 64 (mword_of_int 96 : mword 13))) 0) ('b"0") = true)
        by (vm_compute; reflexivity).
      iApply (wp_bge_x0_taken_s_sconf (mword_of_int (KernelSyms.uartwrite + 0x1c)) (mword_of_int 96 : mword 13)
                Rs1 MA (av - 10)%nat false ltac:(nz) ltac:(exact Hcmp0) Hal
                with "Hcg Hpc Hi1c [-]").
      iNext. iApply wp_next_off_intro. iIntros "Hcg Hpc".
      assert (Jtail : add_vec (mword_of_int (KernelSyms.uartwrite + 0x1c) : mword 64)
                        (sign_extend' 64 (mword_of_int 96 : mword 13)) = mword_of_int (KernelSyms.uartwrite + 0x7c)) by pcw.
      iEval (rewrite Jtail) in "Hpc".
      iAssert (uw_gap5 sp0) with "[H4 H5 H6 H8 H9]" as "Hgap".
      { rewrite /uw_gap5. iSplitL "H4"; [by iExists v4|]. iSplitL "H5"; [by iExists v5|].
        iSplitL "H6"; [by iExists v6|]. iSplitL "H8"; [by iExists v8|]. by iExists v9. }
      iApply (uw_tail (CID := CIDa) CID γl γu j m MA av eb C sp0 ([] : list (bv 8))
                (uw_buf buf dq f 0%nat)
                ltac:(unfold uw_tail_regs; split_and!; assumption) Hspm Hav Heb
                ltac:(wp_next_chain)
                with "Ht Htxl Hcg Hcnt Hpay Hpc Htok HR Hsub0 Hsv Hgap Hs10 Hbuf [Hcont]").
      rewrite /uw_ret.
      iIntros (CIDz Hsz mf) "%Hcs Hcg Hcnt Hpc Hbuf #Hout".
      iSpecialize ("Hcont" $! CIDz with "[%]"); [wp_next_chain|].
      iApply ("Hcont" $! mf with "[%] Hcg Hcnt Hpc [Hbuf] [Hout]").
      + exact Hcs.
      + rewrite /uw_buf. iExact "Hbuf".
      + iExact "Hout".
    - (* ======== n > 0: the byte loop ======== *)
      assert (Hnpos : (0 < n)%nat).
      { assert (Hx := Hb0z). rewrite Z.geb_leb in Hx. apply Z.leb_gt in Hx. lia. }
      iApply (wp_bge_x0_fall_s_sconf (mword_of_int (KernelSyms.uartwrite + 0x1c)) (mword_of_int 96 : mword 13)
                Rs1 MA (av - 10)%nat false ltac:(nz) ltac:(exact Hcmp0)
                with "Hcg Hpc Hi1c [-]").
      iApply wp_next_off_intro. iIntros "Hcg Hpc".
      assert (P20 : add_vec_int (mword_of_int (KernelSyms.uartwrite + 0x1c) : mword 64) 4 = mword_of_int (KernelSyms.uartwrite + 0x20)) by pcw.
      iEval (rewrite P20) in "Hpc".
      (* --- the five shrink-wrapped saves --- *)
      iPoseProof (uwi_20 with "Ht") as "Hi20". iPoseProof (uwi_22 with "Ht") as "Hi22".
      iPoseProof (uwi_24 with "Ht") as "Hi24". iPoseProof (uwi_26 with "Ht") as "Hi26".
      iPoseProof (uwi_28 with "Ht") as "Hi28".
      assert (P22 : add_vec_int (mword_of_int (KernelSyms.uartwrite + 0x20) : mword 64) 2 = mword_of_int (KernelSyms.uartwrite + 0x22)) by pcw.
      assert (P24 : add_vec_int (mword_of_int (KernelSyms.uartwrite + 0x22) : mword 64) 2 = mword_of_int (KernelSyms.uartwrite + 0x24)) by pcw.
      assert (P26 : add_vec_int (mword_of_int (KernelSyms.uartwrite + 0x24) : mword 64) 2 = mword_of_int (KernelSyms.uartwrite + 0x26)) by pcw.
      assert (P28 : add_vec_int (mword_of_int (KernelSyms.uartwrite + 0x26) : mword 64) 2 = mword_of_int (KernelSyms.uartwrite + 0x28)) by pcw.
      assert (P2a : add_vec_int (mword_of_int (KernelSyms.uartwrite + 0x28) : mword 64) 2 = mword_of_int (KernelSyms.uartwrite + 0x2a)) by pcw.
      iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.uartwrite + 0x20)) (mword_of_int 6 : mword 6) Rs2
                MA (av - 10)%nat v4 false with "Hcg Hpc Hi20 [H4] [-]").
      { iEval (rewrite HMAcsp Hb4). iExact "H4". }
      iApply wp_next_off_intro. iIntros "Hcg Hpc H4".
      iEval (rewrite HMAcsp Hb4) in "H4". iEval (rgne) in "H4". iEval (rewrite HMAs2) in "H4".
      iEval (rewrite P22) in "Hpc".
      iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.uartwrite + 0x22)) (mword_of_int 5 : mword 6) Rs3
                MA (av - 10)%nat v5 false with "Hcg Hpc Hi22 [H5] [-]").
      { iEval (rewrite HMAcsp Hb5). iExact "H5". }
      iApply wp_next_off_intro. iIntros "Hcg Hpc H5".
      iEval (rewrite HMAcsp Hb5) in "H5". iEval (rgne) in "H5". iEval (rewrite HMAs3) in "H5".
      iEval (rewrite P24) in "Hpc".
      iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.uartwrite + 0x24)) (mword_of_int 4 : mword 6) Rs4
                MA (av - 10)%nat v6 false with "Hcg Hpc Hi24 [H6] [-]").
      { iEval (rewrite HMAcsp Hb6). iExact "H6". }
      iApply wp_next_off_intro. iIntros "Hcg Hpc H6".
      iEval (rewrite HMAcsp Hb6) in "H6". iEval (rgne) in "H6". iEval (rewrite HMAs4) in "H6".
      iEval (rewrite P26) in "Hpc".
      iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.uartwrite + 0x26)) (mword_of_int 2 : mword 6) Rs6
                MA (av - 10)%nat v8 false with "Hcg Hpc Hi26 [H8] [-]").
      { iEval (rewrite HMAcsp Hb8). iExact "H8". }
      iApply wp_next_off_intro. iIntros "Hcg Hpc H8".
      iEval (rewrite HMAcsp Hb8) in "H8". iEval (rgne) in "H8". iEval (rewrite HMAs6) in "H8".
      iEval (rewrite P28) in "Hpc".
      iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.uartwrite + 0x28)) (mword_of_int 1 : mword 6) Rs7
                MA (av - 10)%nat v9 false with "Hcg Hpc Hi28 [H9] [-]").
      { iEval (rewrite HMAcsp Hb9). iExact "H9". }
      iApply wp_next_off_intro. iIntros "Hcg Hpc H9".
      iEval (rewrite HMAcsp Hb9) in "H9". iEval (rgne) in "H9". iEval (rewrite HMAs7) in "H9".
      iEval (rewrite P2a) in "Hpc".
      iAssert (uw_saved5 sp0 m) with "[H4 H5 H6 H8 H9]" as "Hsv5".
      { rewrite /uw_saved5. iFrame "H4 H5 H6 H8 H9". }
      (* --- the loop's register setup --- *)
      iPoseProof (uwi_2a with "Ht") as "Hi2a". iPoseProof (uwi_2c with "Ht") as "Hi2c".
      iPoseProof (uwi_2e with "Ht") as "Hi2e". iPoseProof (uwi_32 with "Ht") as "Hi32".
      iPoseProof (uwi_36 with "Ht") as "Hi36". iPoseProof (uwi_3a with "Ht") as "Hi3a".
      iPoseProof (uwi_3e with "Ht") as "Hi3e". iPoseProof (uwi_42 with "Ht") as "Hi42".
      iPoseProof (uwi_46 with "Ht") as "Hi46". iPoseProof (uwi_4a with "Ht") as "Hi4a".
      iPoseProof (uwi_4c with "Ht") as "Hi4c".
      assert (P2c : add_vec_int (mword_of_int (KernelSyms.uartwrite + 0x2a) : mword 64) 2 = mword_of_int (KernelSyms.uartwrite + 0x2c)) by pcw.
      assert (P2e : add_vec_int (mword_of_int (KernelSyms.uartwrite + 0x2c) : mword 64) 2 = mword_of_int (KernelSyms.uartwrite + 0x2e)) by pcw.
      assert (P32 : add_vec_int (mword_of_int (KernelSyms.uartwrite + 0x2e) : mword 64) 4 = mword_of_int (KernelSyms.uartwrite + 0x32)) by pcw.
      assert (P36 : add_vec_int (mword_of_int (KernelSyms.uartwrite + 0x32) : mword 64) 4 = mword_of_int (KernelSyms.uartwrite + 0x36)) by pcw.
      assert (P3a : add_vec_int (mword_of_int (KernelSyms.uartwrite + 0x36) : mword 64) 4 = mword_of_int (KernelSyms.uartwrite + 0x3a)) by pcw.
      assert (P3e : add_vec_int (mword_of_int (KernelSyms.uartwrite + 0x3a) : mword 64) 4 = mword_of_int (KernelSyms.uartwrite + 0x3e)) by pcw.
      assert (P42 : add_vec_int (mword_of_int (KernelSyms.uartwrite + 0x3e) : mword 64) 4 = mword_of_int (KernelSyms.uartwrite + 0x42)) by pcw.
      assert (P46 : add_vec_int (mword_of_int (KernelSyms.uartwrite + 0x42) : mword 64) 4 = mword_of_int (KernelSyms.uartwrite + 0x46)) by pcw.
      assert (P4a : add_vec_int (mword_of_int (KernelSyms.uartwrite + 0x46) : mword 64) 4 = mword_of_int (KernelSyms.uartwrite + 0x4a)) by pcw.
      assert (P4c : add_vec_int (mword_of_int (KernelSyms.uartwrite + 0x4a) : mword 64) 2 = mword_of_int (KernelSyms.uartwrite + 0x4c)) by pcw.
      (* +0x2a c.mv s4,s5 *)
      iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.uartwrite + 0x2a)) Rs4 Rs5 MA (av - 10)%nat false
                ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi2a [-]").
      iApply wp_next_off_intro. iIntros "Hcg Hpc". iEval (rgne) in "Hcg".
      set (B0 := <[Regidx Rs4 := regval_into_reg (add_vec zero_reg (MA !!! Regidx Rs5))]> MA).
      change (<[Regidx Rs4 := regval_into_reg (add_vec zero_reg (MA !!! Regidx Rs5))]> MA) with B0.
      iEval (rewrite P2c) in "Hpc".
      (* +0x2c c.add s5,s5,s1 *)
      iApply (wp_cadd_s_sconf (mword_of_int (KernelSyms.uartwrite + 0x2c)) Rs5 Rs1 B0 (av - 10)%nat false
                ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi2c [-]").
      iApply wp_next_off_intro. iIntros "Hcg Hpc". iEval (rgne; rgne) in "Hcg".
      set (B1 := <[Regidx Rs5 := regval_into_reg (add_vec (B0 !!! Regidx Rs5) (B0 !!! Regidx Rs1))]> B0).
      change (<[Regidx Rs5 := regval_into_reg (add_vec (B0 !!! Regidx Rs5) (B0 !!! Regidx Rs1))]> B0) with B1.
      iEval (rewrite P2e) in "Hpc".
      (* +0x2e/+0x32 s1 := &tx_busy *)
      iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.uartwrite + 0x2e)) Rs1 (mword_of_int 10 : mword 20)
                B1 (av - 10)%nat false ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi2e [-]").
      iApply wp_next_off_intro. iIntros "Hcg Hpc".
      set (B2 := <[Regidx Rs1 := regval_into_reg
          (add_vec (mword_of_int (KernelSyms.uartwrite + 0x2e) : mword 64) (auipc_off (mword_of_int 10 : mword 20)))]> B1).
      change (<[Regidx Rs1 := regval_into_reg
          (add_vec (mword_of_int (KernelSyms.uartwrite + 0x2e) : mword 64) (auipc_off (mword_of_int 10 : mword 20)))]> B1) with B2.
      iEval (rewrite P32) in "Hpc".
      iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.uartwrite + 0x32)) Rs1 Rs1 (mword_of_int 0x922 : mword 12)
                B2 (av - 10)%nat false ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi32 [-]").
      iApply wp_next_off_intro. iIntros "Hcg Hpc". iEval (rgne) in "Hcg".
      set (B3 := <[Regidx Rs1 := regval_into_reg
          (add_vec (B2 !!! Regidx Rs1) (sign_extend' 64 (mword_of_int 0x922 : mword 12)))]> B2).
      change (<[Regidx Rs1 := regval_into_reg
          (add_vec (B2 !!! Regidx Rs1) (sign_extend' 64 (mword_of_int 0x922 : mword 12)))]> B2) with B3.
      iEval (rewrite P36) in "Hpc".
      (* +0x36/+0x3a s3 := &tx_lock *)
      iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.uartwrite + 0x36)) Rs3 (mword_of_int 18 : mword 20)
                B3 (av - 10)%nat false ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi36 [-]").
      iApply wp_next_off_intro. iIntros "Hcg Hpc".
      set (B4 := <[Regidx Rs3 := regval_into_reg
          (add_vec (mword_of_int (KernelSyms.uartwrite + 0x36) : mword 64) (auipc_off (mword_of_int 18 : mword 20)))]> B3).
      change (<[Regidx Rs3 := regval_into_reg
          (add_vec (mword_of_int (KernelSyms.uartwrite + 0x36) : mword 64) (auipc_off (mword_of_int 18 : mword 20)))]> B3) with B4.
      iEval (rewrite P3a) in "Hpc".
      iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.uartwrite + 0x3a)) Rs3 Rs3 (mword_of_int 0x9fe : mword 12)
                B4 (av - 10)%nat false ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi3a [-]").
      iApply wp_next_off_intro. iIntros "Hcg Hpc". iEval (rgne) in "Hcg".
      set (B5 := <[Regidx Rs3 := regval_into_reg
          (add_vec (B4 !!! Regidx Rs3) (sign_extend' 64 (mword_of_int 0x9fe : mword 12)))]> B4).
      change (<[Regidx Rs3 := regval_into_reg
          (add_vec (B4 !!! Regidx Rs3) (sign_extend' 64 (mword_of_int 0x9fe : mword 12)))]> B4) with B5.
      iEval (rewrite P3e) in "Hpc".
      (* +0x3e/+0x42 s2 := &tx_chan *)
      iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.uartwrite + 0x3e)) Rs2 (mword_of_int 10 : mword 20)
                B5 (av - 10)%nat false ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi3e [-]").
      iApply wp_next_off_intro. iIntros "Hcg Hpc".
      set (B6 := <[Regidx Rs2 := regval_into_reg
          (add_vec (mword_of_int (KernelSyms.uartwrite + 0x3e) : mword 64) (auipc_off (mword_of_int 10 : mword 20)))]> B5).
      change (<[Regidx Rs2 := regval_into_reg
          (add_vec (mword_of_int (KernelSyms.uartwrite + 0x3e) : mword 64) (auipc_off (mword_of_int 10 : mword 20)))]> B5) with B6.
      iEval (rewrite P42) in "Hpc".
      iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.uartwrite + 0x42)) Rs2 Rs2 (mword_of_int 0x90e : mword 12)
                B6 (av - 10)%nat false ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi42 [-]").
      iApply wp_next_off_intro. iIntros "Hcg Hpc". iEval (rgne) in "Hcg".
      set (B7 := <[Regidx Rs2 := regval_into_reg
          (add_vec (B6 !!! Regidx Rs2) (sign_extend' 64 (mword_of_int 0x90e : mword 12)))]> B6).
      change (<[Regidx Rs2 := regval_into_reg
          (add_vec (B6 !!! Regidx Rs2) (sign_extend' 64 (mword_of_int 0x90e : mword 12)))]> B6) with B7.
      iEval (rewrite P46) in "Hpc".
      (* +0x46 lui s7,0x10000 -- the THR base *)
      iApply (wp_lui_s_sconf (mword_of_int (KernelSyms.uartwrite + 0x46)) Rs7 (mword_of_int 0x10000 : mword 20)
                (uart_pa 0) B7 (av - 10)%nat false ltac:(nz) ltac:(rdok)
                ltac:(apply bv_eq; vm_compute; reflexivity) with "Hcg Hpc Hi46 [-]").
      iApply wp_next_off_intro. iIntros "Hcg Hpc".
      set (B8 := <[Regidx Rs7 := regval_into_reg (uart_pa 0)]> B7).
      change (<[Regidx Rs7 := regval_into_reg (uart_pa 0)]> B7) with B8.
      iEval (rewrite P4a) in "Hpc".
      (* +0x4a c.li s6,1 *)
      iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.uartwrite + 0x4a)) Rs6 (mword_of_int 1 : mword 6)
                (mword_of_int 1 : mword 64) B8 (av - 10)%nat false ltac:(nz) ltac:(rdok)
                ltac:(pcw) with "Hcg Hpc Hi4a [-]").
      iApply wp_next_off_intro. iIntros "Hcg Hpc".
      set (B9 := <[Regidx Rs6 := regval_into_reg (mword_of_int 1 : mword 64)]> B8).
      change (<[Regidx Rs6 := regval_into_reg (mword_of_int 1 : mword 64)]> B8) with B9.
      iEval (rewrite P4c) in "Hpc".
      (* +0x4c c.j -> the loop head *)
      iApply (wp_cj_s_sconf (mword_of_int (KernelSyms.uartwrite + 0x4c))
                (sign_extend' 21 (concat_vec (mword_of_int 16 : mword 11) ('b"0")))
                B9 (av - 10)%nat false ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi4c [-]").
      iApply wp_next_off_intro. iNext. iIntros "Hcg Hpc".
      assert (Jhead : add_vec (mword_of_int (KernelSyms.uartwrite + 0x4c) : mword 64)
                        (sign_extend' 64 (sign_extend' 21 (concat_vec (mword_of_int 16 : mword 11) ('b"0"))))
                      = mword_of_int (KernelSyms.uartwrite + 0x6c)) by pcw.
      iEval (rewrite Jhead) in "Hpc".
      (* the loop's register invariant at entry *)
      assert (HB9regs : uw_loop_regs m B9 spd buf n 0%nat).
      { unfold uw_loop_regs. split_and!.
        - rewrite /B9 upd_ne; [| reg_neq]. rewrite /B8 upd_ne; [| reg_neq].
          rewrite /B7 upd_ne; [| reg_neq]. rewrite /B6 upd_ne; [| reg_neq].
          rewrite /B5 upd_ne; [| reg_neq]. rewrite /B4 upd_ne; [| reg_neq].
          rewrite /B3 upd_ne; [| reg_neq]. rewrite /B2 upd_ne; [| reg_neq].
          rewrite /B1 upd_ne; [| reg_neq]. rewrite /B0 upd_ne; [| reg_neq]. exact HMAcsp.
        - rewrite /B9 upd_ne; [| reg_neq]. rewrite /B8 upd_ne; [| reg_neq].
          rewrite /B7 upd_ne; [| reg_neq]. rewrite /B6 upd_ne; [| reg_neq].
          rewrite /B5 upd_ne; [| reg_neq]. rewrite /B4 upd_ne; [| reg_neq].
          rewrite /B3 upd_eq. rewrite /B2 upd_eq. rewrite /a_tx_busy. pcw.
        - rewrite /B9 upd_ne; [| reg_neq]. rewrite /B8 upd_ne; [| reg_neq].
          rewrite /B7 upd_eq. rewrite /B6 upd_eq. rewrite /a_tx_chan. pcw.
        - rewrite /B9 upd_ne; [| reg_neq]. rewrite /B8 upd_ne; [| reg_neq].
          rewrite /B7 upd_ne; [| reg_neq]. rewrite /B6 upd_ne; [| reg_neq].
          rewrite /B5 upd_eq. rewrite /B4 upd_eq. rewrite /a_tx_lock. pcw.
        - rewrite uw_pa_add_0.
          rewrite /B9 upd_ne; [| reg_neq]. rewrite /B8 upd_ne; [| reg_neq].
          rewrite /B7 upd_ne; [| reg_neq]. rewrite /B6 upd_ne; [| reg_neq].
          rewrite /B5 upd_ne; [| reg_neq]. rewrite /B4 upd_ne; [| reg_neq].
          rewrite /B3 upd_ne; [| reg_neq]. rewrite /B2 upd_ne; [| reg_neq].
          rewrite /B1 upd_ne; [| reg_neq]. rewrite /B0 upd_eq.
          rewrite uw_zero_reg_add. exact HMAs5.
        - rewrite /B9 upd_ne; [| reg_neq]. rewrite /B8 upd_ne; [| reg_neq].
          rewrite /B7 upd_ne; [| reg_neq]. rewrite /B6 upd_ne; [| reg_neq].
          rewrite /B5 upd_ne; [| reg_neq]. rewrite /B4 upd_ne; [| reg_neq].
          rewrite /B3 upd_ne; [| reg_neq]. rewrite /B2 upd_ne; [| reg_neq].
          rewrite /B1 upd_eq.
          rewrite (_ : B0 !!! Regidx Rs5 = buf); [| rewrite /B0 upd_ne; [exact HMAs5 | reg_neq]].
          rewrite (_ : B0 !!! Regidx Rs1 = (mword_of_int (Z.of_nat n) : mword 64));
            [| rewrite /B0 upd_ne; [exact HMAs1 | reg_neq]].
          apply uw_pa_add_n.
        - rewrite /B9 upd_eq. reflexivity.
        - rewrite /B9 upd_ne; [| reg_neq]. rewrite /B8 upd_eq. reflexivity.
        - rewrite /B9 upd_ne; [| reg_neq]. rewrite /B8 upd_ne; [| reg_neq].
          rewrite /B7 upd_ne; [| reg_neq]. rewrite /B6 upd_ne; [| reg_neq].
          rewrite /B5 upd_ne; [| reg_neq]. rewrite /B4 upd_ne; [| reg_neq].
          rewrite /B3 upd_ne; [| reg_neq]. rewrite /B2 upd_ne; [| reg_neq].
          rewrite /B1 upd_ne; [| reg_neq]. rewrite /B0 upd_ne; [| reg_neq]. exact HMAs8.
        - rewrite /B9 upd_ne; [| reg_neq]. rewrite /B8 upd_ne; [| reg_neq].
          rewrite /B7 upd_ne; [| reg_neq]. rewrite /B6 upd_ne; [| reg_neq].
          rewrite /B5 upd_ne; [| reg_neq]. rewrite /B4 upd_ne; [| reg_neq].
          rewrite /B3 upd_ne; [| reg_neq]. rewrite /B2 upd_ne; [| reg_neq].
          rewrite /B1 upd_ne; [| reg_neq]. rewrite /B0 upd_ne; [| reg_neq]. exact HMAs9.
        - rewrite /B9 upd_ne; [| reg_neq]. rewrite /B8 upd_ne; [| reg_neq].
          rewrite /B7 upd_ne; [| reg_neq]. rewrite /B6 upd_ne; [| reg_neq].
          rewrite /B5 upd_ne; [| reg_neq]. rewrite /B4 upd_ne; [| reg_neq].
          rewrite /B3 upd_ne; [| reg_neq]. rewrite /B2 upd_ne; [| reg_neq].
          rewrite /B1 upd_ne; [| reg_neq]. rewrite /B0 upd_ne; [| reg_neq]. exact HMAs10.
        - rewrite /B9 upd_ne; [| reg_neq]. rewrite /B8 upd_ne; [| reg_neq].
          rewrite /B7 upd_ne; [| reg_neq]. rewrite /B6 upd_ne; [| reg_neq].
          rewrite /B5 upd_ne; [| reg_neq]. rewrite /B4 upd_ne; [| reg_neq].
          rewrite /B3 upd_ne; [| reg_neq]. rewrite /B2 upd_ne; [| reg_neq].
          rewrite /B1 upd_ne; [| reg_neq]. rewrite /B0 upd_ne; [| reg_neq]. exact HMAs11. }
      (* ============ the loop ============ *)
      iAssert (uw_full sp0 m) with "[Hsv Hsv5 Hs10]" as "Hfull".
      { rewrite /uw_full. iFrame "Hsv Hsv5 Hs10". }
      iPoseProof (uw_iter CID γl γu γv γs j γlp m av eb C sp0 buf n f dq (n - 1)%nat
                    ltac:(lia) Hj Hjlp Hav Heb 0%nat ltac:(lia)
                    with "Ht Hdinv Htxl Hpinv Hpanic") as "Iter".
      rewrite /uw_head.
      iSpecialize ("Iter" $! CIDa with "[%]"); [wp_next_chain|].
      iApply ("Iter" $! B9 with "[%] Hcg Hcnt Hpay Hpc Htok HR Hsub0 Hfull Hbuf [Hcont]").
      { exact HB9regs. }
      (* ============ the loop's exit: +0x72 -> the epilogue ============ *)
      rewrite /uw_exit_cont.
      iIntros (CIDx Hsx M') "%Hregs' Hcg Hcnt Hpay Hpc Htok HR #Hout Hfull Hbuf".
      iDestruct "Hfull" as "(Hsv & Hsv5 & Hs10)".
      rewrite /uw_saved5.
      iDestruct "Hsv5" as "(G4 & G5 & G6 & G8 & G9)".
      pose proof Hregs' as Hregs''.
      destruct Hregs'' as (Wsp & Ws1 & Ws2 & Ws3 & Ws4 & Ws5 & Ws6 & Ws7 & W24 & W25 & W26 & W27).
      iPoseProof (uwi_72 with "Ht") as "Hi72". iPoseProof (uwi_74 with "Ht") as "Hi74".
      iPoseProof (uwi_76 with "Ht") as "Hi76". iPoseProof (uwi_78 with "Ht") as "Hi78".
      iPoseProof (uwi_7a with "Ht") as "Hi7a".
      assert (P74 : add_vec_int (mword_of_int (KernelSyms.uartwrite + 0x72) : mword 64) 2 = mword_of_int (KernelSyms.uartwrite + 0x74)) by pcw.
      assert (P76 : add_vec_int (mword_of_int (KernelSyms.uartwrite + 0x74) : mword 64) 2 = mword_of_int (KernelSyms.uartwrite + 0x76)) by pcw.
      assert (P78 : add_vec_int (mword_of_int (KernelSyms.uartwrite + 0x76) : mword 64) 2 = mword_of_int (KernelSyms.uartwrite + 0x78)) by pcw.
      assert (P7a : add_vec_int (mword_of_int (KernelSyms.uartwrite + 0x78) : mword 64) 2 = mword_of_int (KernelSyms.uartwrite + 0x7a)) by pcw.
      assert (P7c : add_vec_int (mword_of_int (KernelSyms.uartwrite + 0x7a) : mword 64) 2 = mword_of_int (KernelSyms.uartwrite + 0x7c)) by pcw.
      iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.uartwrite + 0x72)) (mword_of_int 6 : mword 6) Rs2
                M' (av - 10)%nat (m !!! Regidx Rs2) false (dqm := DfracOwn 1) ltac:(nz) ltac:(rdok)
                with "Hcg Hpc Hi72 [G4] [-]").
      { iEval (rewrite Wsp Hb4). iExact "G4". }
      iApply wp_next_off_intro. iIntros "Hcg Hpc G4". iEval (rewrite Wsp Hb4) in "G4".
      set (R1 := <[Regidx Rs2 := regval_into_reg (m !!! Regidx Rs2)]> M').
      change (<[Regidx Rs2 := regval_into_reg (m !!! Regidx Rs2)]> M') with R1.
      assert (HR1sp : R1 !!! Regidx csp_rs1 = spd) by (rewrite /R1 upd_ne; [exact Wsp | reg_neq]).
      iEval (rewrite P74) in "Hpc".
      iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.uartwrite + 0x74)) (mword_of_int 5 : mword 6) Rs3
                R1 (av - 10)%nat (m !!! Regidx Rs3) false (dqm := DfracOwn 1) ltac:(nz) ltac:(rdok)
                with "Hcg Hpc Hi74 [G5] [-]").
      { iEval (rewrite HR1sp Hb5). iExact "G5". }
      iApply wp_next_off_intro. iIntros "Hcg Hpc G5". iEval (rewrite HR1sp Hb5) in "G5".
      set (R2 := <[Regidx Rs3 := regval_into_reg (m !!! Regidx Rs3)]> R1).
      change (<[Regidx Rs3 := regval_into_reg (m !!! Regidx Rs3)]> R1) with R2.
      assert (HR2sp : R2 !!! Regidx csp_rs1 = spd) by (rewrite /R2 upd_ne; [exact HR1sp | reg_neq]).
      iEval (rewrite P76) in "Hpc".
      iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.uartwrite + 0x76)) (mword_of_int 4 : mword 6) Rs4
                R2 (av - 10)%nat (m !!! Regidx Rs4) false (dqm := DfracOwn 1) ltac:(nz) ltac:(rdok)
                with "Hcg Hpc Hi76 [G6] [-]").
      { iEval (rewrite HR2sp Hb6). iExact "G6". }
      iApply wp_next_off_intro. iIntros "Hcg Hpc G6". iEval (rewrite HR2sp Hb6) in "G6".
      set (R3 := <[Regidx Rs4 := regval_into_reg (m !!! Regidx Rs4)]> R2).
      change (<[Regidx Rs4 := regval_into_reg (m !!! Regidx Rs4)]> R2) with R3.
      assert (HR3sp : R3 !!! Regidx csp_rs1 = spd) by (rewrite /R3 upd_ne; [exact HR2sp | reg_neq]).
      iEval (rewrite P78) in "Hpc".
      iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.uartwrite + 0x78)) (mword_of_int 2 : mword 6) Rs6
                R3 (av - 10)%nat (m !!! Regidx Rs6) false (dqm := DfracOwn 1) ltac:(nz) ltac:(rdok)
                with "Hcg Hpc Hi78 [G8] [-]").
      { iEval (rewrite HR3sp Hb8). iExact "G8". }
      iApply wp_next_off_intro. iIntros "Hcg Hpc G8". iEval (rewrite HR3sp Hb8) in "G8".
      set (R4 := <[Regidx Rs6 := regval_into_reg (m !!! Regidx Rs6)]> R3).
      change (<[Regidx Rs6 := regval_into_reg (m !!! Regidx Rs6)]> R3) with R4.
      assert (HR4sp : R4 !!! Regidx csp_rs1 = spd) by (rewrite /R4 upd_ne; [exact HR3sp | reg_neq]).
      iEval (rewrite P7a) in "Hpc".
      iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.uartwrite + 0x7a)) (mword_of_int 1 : mword 6) Rs7
                R4 (av - 10)%nat (m !!! Regidx Rs7) false (dqm := DfracOwn 1) ltac:(nz) ltac:(rdok)
                with "Hcg Hpc Hi7a [G9] [-]").
      { iEval (rewrite HR4sp Hb9). iExact "G9". }
      iApply wp_next_off_intro. iIntros "Hcg Hpc G9". iEval (rewrite HR4sp Hb9) in "G9".
      set (R5 := <[Regidx Rs7 := regval_into_reg (m !!! Regidx Rs7)]> R4).
      change (<[Regidx Rs7 := regval_into_reg (m !!! Regidx Rs7)]> R4) with R5.
      iEval (rewrite P7c) in "Hpc".
      (* the epilogue's register shape *)
      assert (HR5regs : uw_tail_regs m R5 spd).
      { unfold uw_tail_regs. split_and!.
        - rewrite /R5 upd_ne; [| reg_neq]. exact HR4sp.
        - rewrite /R5 upd_ne; [| reg_neq]. rewrite /R4 upd_ne; [| reg_neq].
          rewrite /R3 upd_ne; [| reg_neq]. rewrite /R2 upd_ne; [| reg_neq].
          rewrite /R1 upd_eq. reflexivity.
        - rewrite /R5 upd_ne; [| reg_neq]. rewrite /R4 upd_ne; [| reg_neq].
          rewrite /R3 upd_ne; [| reg_neq]. rewrite /R2 upd_eq. reflexivity.
        - rewrite /R5 upd_ne; [| reg_neq]. rewrite /R4 upd_ne; [| reg_neq].
          rewrite /R3 upd_eq. reflexivity.
        - rewrite /R5 upd_ne; [| reg_neq]. rewrite /R4 upd_eq. reflexivity.
        - rewrite /R5 upd_eq. reflexivity.
        - rewrite /R5 upd_ne; [| reg_neq]. rewrite /R4 upd_ne; [| reg_neq].
          rewrite /R3 upd_ne; [| reg_neq]. rewrite /R2 upd_ne; [| reg_neq].
          rewrite /R1 upd_ne; [| reg_neq]. exact W24.
        - rewrite /R5 upd_ne; [| reg_neq]. rewrite /R4 upd_ne; [| reg_neq].
          rewrite /R3 upd_ne; [| reg_neq]. rewrite /R2 upd_ne; [| reg_neq].
          rewrite /R1 upd_ne; [| reg_neq]. exact W25.
        - rewrite /R5 upd_ne; [| reg_neq]. rewrite /R4 upd_ne; [| reg_neq].
          rewrite /R3 upd_ne; [| reg_neq]. rewrite /R2 upd_ne; [| reg_neq].
          rewrite /R1 upd_ne; [| reg_neq]. exact W26.
        - rewrite /R5 upd_ne; [| reg_neq]. rewrite /R4 upd_ne; [| reg_neq].
          rewrite /R3 upd_ne; [| reg_neq]. rewrite /R2 upd_ne; [| reg_neq].
          rewrite /R1 upd_ne; [| reg_neq]. exact W27. }
      iAssert (uw_gap5 sp0) with "[G4 G5 G6 G8 G9]" as "Hgap".
      { rewrite /uw_gap5. iSplitL "G4"; [by iExists _|]. iSplitL "G5"; [by iExists _|].
        iSplitL "G6"; [by iExists _|]. iSplitL "G8"; [by iExists _|]. by iExists _. }
      iApply (uw_tail (CID := CIDx) CID γl γu j m R5 av eb C sp0 (uw_bytes f n)
                (uw_buf buf dq f n) HR5regs Hspm Hav Heb ltac:(wp_next_chain)
                with "Ht Htxl Hcg Hcnt Hpay Hpc Htok HR Hout Hsv Hgap Hs10 Hbuf [Hcont]").
      rewrite /uw_ret.
      iIntros (CIDz Hsz mf) "%Hcs Hcg Hcnt Hpc Hbuf #Hout2".
      iSpecialize ("Hcont" $! CIDz with "[%]"); [wp_next_chain|].
      iApply ("Hcont" $! mf with "[%] Hcg Hcnt Hpc [Hbuf] [Hout2]").
      + exact Hcs.
      + rewrite /uw_buf. iExact "Hbuf".
      + iExact "Hout2".
  Qed.

End ProofUartwrite.
End UartwriteProof.
