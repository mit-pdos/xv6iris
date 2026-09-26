(* ProofConsoleintr.v -- the whole-function WP for xv6's consoleintr().

     void consoleintr(int c)
     {
       acquire(&cons.lock);
       switch (c) {
       case C('U'):                       // kill line
         while (cons.e != cons.w &&
                cons.buf[(cons.e - 1) % INPUT_BUF_SIZE] != '\n') {
           cons.e--;  consputc(BACKSPACE);
         }
         break;
       case C('H'): case '\x7f':          // backspace / delete
         if (cons.e != cons.w) { cons.e--; consputc(BACKSPACE); }
         break;
       default:
         if (c != 0 && cons.e - cons.r < INPUT_BUF_SIZE) {
           c = (c == '\r') ? '\n' : c;
           consputc(c);
           cons.buf[cons.e++ % INPUT_BUF_SIZE] = c;
           if (c == '\n' || c == C('D') || cons.e - cons.r == INPUT_BUF_SIZE) {
             cons.w = cons.e;  wakeup(&cons.r);
           }
         }
         break;
       }
       release(&cons.lock);
     }

   182 instructions / 364 bytes; the contract is SpecConsoleintr.v, the decode
   layer CodeConsoleintr.v, the console's own state ConsoleInv.v.

   THE FRAME IS SIX SLOTS ([c.addi16sp sp,-48]).  ra/s0/s1 are saved
   unconditionally into slots 1..3; s2 and s3 -- the two constants the
   kill-line loop hoists ('\n' and BACKSPACE) -- are SHRINK-WRAPPED into slots
   4 and 5 by the pair at +0x092, on the one arm that has them.  Slot 6 is
   never touched.

   ONE EXIT (+0x104: release, then the epilogue) and NINE jumps to it, so the
   whole function is three continuations plus the arms that reach them:
   [ct_exit_prop], the wake-up tail [ct_wake_prop] (+0x156) and the kill-line
   loop [ct_kill_prop] (+0x0b8).  EVERY ARM TAKES THE CONTINUATIONS AS
   PREMISES rather than holding them, so each is provable from the PERSISTENT
   context alone and the loop's Löb needs nothing threaded round its back
   edge.  Same rule as consoleread's [cr_exits]; it is the thing to reach for
   first in a function with one exit and many jumps to it.

   THE KILL-LINE LOOP IS AN iLöb, NOT A FUEL INDUCTION, and that is where the
   flat [ConsoleInv.cons_res] shows: with no relation between [cons.e] and
   [cons.w], the loop's [cons.e--] bounds nothing.  It does not need to --
   the back edge is the TAKEN arm of the [bne] at +0x0da, and
   [wp_bne_taken_s_sconf] hands out a [▷ wp_next], which is exactly what the
   Löb IH sits under.  Nothing is returned, so no count has to survive.

   AFTER THE ENTRY [acquire] THE HART IS FIXED, and that is what makes every
   arm below a plain lemma over `{CIDq : CpuId} `{XI : CurCtx} with one chaining premise
   rather than a [wp_next]-wrapped continuation: the whole critical section
   runs at [b = false], where [wp_next_off_intro] hands the callback back at
   the AMBIENT hart, and neither consputc nor wakeup rebinds one.  Only the
   entry (which runs at the caller's [b]) and release cross harts.

   THE ARMS, IN ADDRESS ORDER: [ct_dflt] (+0x02c, the [c != 0] and ring-room
   guards), [ct_store] (+0x04e, echo/append and the three ways to reach
   WAKE), [ct_kill_pre] (+0x092, the C('U') shrink-wrap), [ct_bs] (+0x0f0,
   backspace) and [ct_cr] (+0x12e, the '\r' -> '\n' rewrite). *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes.
Require Import ConsLog.   (* [echo_of], [cons_erase], [cons_echo]: MOVED here, lane CONS-IO *)
Require Import RiscvLang RiscvPtsto.
Require Import ObsTrace.   (* [obs_ends_in Uart0]: the tag premise's byte *)
Require Import RegFile.
Require Import InstrBytes WpMmodeLeafBase.
Require Import RiscvExtras.
Require Import CalleeSaved KernelText.
Require Import StackOwn.
Require Import VcGen WpSconfAlu WpSconfMem WpSconfCtl WpSconfBtype.
Require Import W32Arith.
Require Import IntrDefs WpSmodeIntr.
Require Import HartTp WpNext.
Require Import WpLock ProcGeom CpuOwn.
Require Import FdSlots.
Require Import DiskPtsto WpUart UartTxInv.
Require Import ConsoleInv.
Require Import SchedCtx.
Require Import SpecAcquire SpecRelease SpecConsputc SpecWakeup.
Require Import SpecUartPutc.   (* [cp_byte]: the byte uartputc_sync stores,
     which is what consputc's pinned post names *)
Require Import CodeConsoleintr.
Require Import SpecConsoleintr.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import ProcAvail.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Require Import TsoCtx.

Import Defs.
Local Open Scope Z_scope.

Notation CT := KernelSyms.consoleintr (only parsing).

(* THE FRAME IS SIX SLOTS.  A [c.sdsp]/[c.ldsp] displacement off the pushed sp
   names slot [6 - uimm] counted down from the ENTRY sp. *)
Lemma ct_slot_bridge (X : mword 64) (o : mword 64) (k : nat) :
  add_vec (mword_of_int (- (8 * Z.of_nat 6%nat))) o = mword_of_int (- (8 * Z.of_nat k)) ->
  add_vec (pa_stk X 6%nat) o = pa_stk X k.
Proof.
  intro H. unfold pa_stk, add_vec_int. rewrite add_vec_assoc H. reflexivity.
Qed.

Local Ltac reg_neq :=
  lazymatch goal with |- ?a <> ?b =>
    tryif unify a b then fail else (vm_compute; discriminate) end.
Local Ltac nz := vm_compute; discriminate.
Local Ltac pcw := apply bv_eq; vm_compute; reflexivity.

(* THE CALLEE-SAVED ROLES: s1 = the character [c], and then -- once the
   C('U') arm has hoisted them -- s1 = &cons, s2 = '\n', s3 = BACKSPACE.
   s0 is the frame pointer and is dead after the prologue. *)
Notation Rra  := (mword_of_int 1  : mword 5).
Notation Rs0  := (mword_of_int 8  : mword 5).
Notation Rs1  := (mword_of_int 9  : mword 5).
Notation Ra0  := (mword_of_int 10 : mword 5).
Notation Ra1  := (mword_of_int 11 : mword 5).
Notation Ra2  := (mword_of_int 12 : mword 5).
Notation Ra3  := (mword_of_int 13 : mword 5).
Notation Ra4  := (mword_of_int 14 : mword 5).
Notation Ra5  := (mword_of_int 15 : mword 5).
Notation Rs2  := (mword_of_int 18 : mword 5).
Notation Rs3  := (mword_of_int 19 : mword 5).
Notation Rs4  := (mword_of_int 20 : mword 5).
Notation Rs5  := (mword_of_int 21 : mword 5).
Notation Rs6  := (mword_of_int 22 : mword 5).
Notation Rs7  := (mword_of_int 23 : mword 5).
Notation Rs8  := (mword_of_int 24 : mword 5).
Notation Rs9  := (mword_of_int 25 : mword 5).
Notation Rs10 := (mword_of_int 26 : mword 5).
Notation Rs11 := (mword_of_int 27 : mword 5).

Section CtBodies.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ, !wchG Σ}.
  Context `{GEN : RiscvLang.GenId}.

  Local Ltac rgall := repeat (rewrite rget_ne; [| vm_compute; discriminate]).

  (* ---- the frame, in two pieces ------------------------------------ *)

  (* the three the prologue saves unconditionally *)
  Definition ct_saved `{XI : CurCtx} (sp0 : mword 64) (m0 : regfile) : iProp Σ :=
    (pa_stk sp0 1 ↦₈[KT1] (m0 !!! Regidx Rra) ∗
     pa_stk sp0 2 ↦₈[KT1] (m0 !!! Regidx Rs0) ∗
     pa_stk sp0 3 ↦₈[KT1] (m0 !!! Regidx Rs1))%I.

  (* slots 4 and 5 (s2/s3's shrink-wrap) and slot 6, which nothing writes *)
  Definition ct_rest `{XI : CurCtx} (sp0 : mword 64) : iProp Σ :=
    ((∃ w : mword 64, pa_stk sp0 4 ↦₈[KT1] w) ∗
     (∃ w : mword 64, pa_stk sp0 5 ↦₈[KT1] w) ∗
     (∃ w : mword 64, pa_stk sp0 6 ↦₈[KT1] w))%I.

  Lemma ct_frame_back `{XI : CurCtx} (sp0 : mword 64) (m0 : regfile) :
    ct_saved sp0 m0 -∗ ct_rest sp0 -∗ stack_own (KTR := KT1) sp0 6.
  Proof using .
    iIntros "(H1 & H2 & H3) (H4 & H5 & H6)".
    rewrite (stack_own_slots (KTR := KT1)). cbn [seq].
    iSplitL "H1"; [by iExists _|]. iSplitL "H2"; [by iExists _|].
    iSplitL "H3"; [by iExists _|]. iSplitL "H4"; [iExact "H4"|].
    iSplitL "H5"; [iExact "H5"|]. iSplitL "H6"; [iExact "H6"|]. done.
  Qed.

  (* the ten callee-saved registers the epilogue does NOT reload: s2 and s3
     (restored on the one arm that spilled them) and s4..s11, which nothing
     in this function touches at all. *)
  Definition ct_cs_hi (M m0 : regfile) : Prop :=
    M !!! Regidx Rs2  = m0 !!! Regidx Rs2
    /\ M !!! Regidx Rs3  = m0 !!! Regidx Rs3
    /\ M !!! Regidx Rs4  = m0 !!! Regidx Rs4
    /\ M !!! Regidx Rs5  = m0 !!! Regidx Rs5
    /\ M !!! Regidx Rs6  = m0 !!! Regidx Rs6
    /\ M !!! Regidx Rs7  = m0 !!! Regidx Rs7
    /\ M !!! Regidx Rs8  = m0 !!! Regidx Rs8
    /\ M !!! Regidx Rs9  = m0 !!! Regidx Rs9
    /\ M !!! Regidx Rs10 = m0 !!! Regidx Rs10
    /\ M !!! Regidx Rs11 = m0 !!! Regidx Rs11.

  (* s4..s11 alone.  BELOW THE C('U') ARM'S SPILL THIS IS ALL A BLOCK CAN
     SAY, and saying it POSITIVELY is the point: the tempting form -- "every
     [is_cs_idx] register except s1, s2 and s3 still holds its entry value" --
     is UNSATISFIABLE here, because [is_cs_idx] contains sp (x2) and s0 (x8),
     and the prologue moved both (sp to [pa_stk sp0 6], s0 to the frame
     pointer).  A block premised on it compiles, and nothing can ever apply
     it.  The two registers are accounted for separately: sp by the explicit
     [pa_stk] equation every block carries, s0 by the epilogue's reload. *)
  Definition ct_cs_top (M m0 : regfile) : Prop :=
    M !!! Regidx Rs4  = m0 !!! Regidx Rs4
    /\ M !!! Regidx Rs5  = m0 !!! Regidx Rs5
    /\ M !!! Regidx Rs6  = m0 !!! Regidx Rs6
    /\ M !!! Regidx Rs7  = m0 !!! Regidx Rs7
    /\ M !!! Regidx Rs8  = m0 !!! Regidx Rs8
    /\ M !!! Regidx Rs9  = m0 !!! Regidx Rs9
    /\ M !!! Regidx Rs10 = m0 !!! Regidx Rs10
    /\ M !!! Regidx Rs11 = m0 !!! Regidx Rs11.

  Lemma ct_cs_hi_top (M m0 : regfile) : ct_cs_hi M m0 -> ct_cs_top M m0.
  Proof using .
    intros (_ & _ & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11).
    unfold ct_cs_top. split_and!; assumption.
  Qed.

  (* A CALL, OR ANY RUN OF INSTRUCTIONS THAT WRITES NO CALLEE-SAVED
     REGISTER, transports both claims -- which is every use of them in this
     file, so the two lemmas replace the ten-way [split_and!] at each site. *)
  Lemma ct_cs_hi_thr (M1 M m0 : regfile) :
    (forall r : mword 5, is_cs_idx r = true -> M1 !!! Regidx r = M !!! Regidx r) ->
    ct_cs_hi M m0 -> ct_cs_hi M1 m0.
  Proof using .
    intros Hthr (Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11).
    unfold ct_cs_hi. split_and!;
      [ rewrite (Hthr Rs2  ltac:(vm_compute; reflexivity)); exact Q2
      | rewrite (Hthr Rs3  ltac:(vm_compute; reflexivity)); exact Q3
      | rewrite (Hthr Rs4  ltac:(vm_compute; reflexivity)); exact Q4
      | rewrite (Hthr Rs5  ltac:(vm_compute; reflexivity)); exact Q5
      | rewrite (Hthr Rs6  ltac:(vm_compute; reflexivity)); exact Q6
      | rewrite (Hthr Rs7  ltac:(vm_compute; reflexivity)); exact Q7
      | rewrite (Hthr Rs8  ltac:(vm_compute; reflexivity)); exact Q8
      | rewrite (Hthr Rs9  ltac:(vm_compute; reflexivity)); exact Q9
      | rewrite (Hthr Rs10 ltac:(vm_compute; reflexivity)); exact Q10
      | rewrite (Hthr Rs11 ltac:(vm_compute; reflexivity)); exact Q11 ].
  Qed.

  Lemma ct_cs_top_thr (M1 M m0 : regfile) :
    (forall r : mword 5, is_cs_idx r = true -> M1 !!! Regidx r = M !!! Regidx r) ->
    ct_cs_top M m0 -> ct_cs_top M1 m0.
  Proof using .
    intros Hthr (Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11).
    unfold ct_cs_top. split_and!;
      [ rewrite (Hthr Rs4  ltac:(vm_compute; reflexivity)); exact Q4
      | rewrite (Hthr Rs5  ltac:(vm_compute; reflexivity)); exact Q5
      | rewrite (Hthr Rs6  ltac:(vm_compute; reflexivity)); exact Q6
      | rewrite (Hthr Rs7  ltac:(vm_compute; reflexivity)); exact Q7
      | rewrite (Hthr Rs8  ltac:(vm_compute; reflexivity)); exact Q8
      | rewrite (Hthr Rs9  ltac:(vm_compute; reflexivity)); exact Q9
      | rewrite (Hthr Rs10 ltac:(vm_compute; reflexivity)); exact Q10
      | rewrite (Hthr Rs11 ltac:(vm_compute; reflexivity)); exact Q11 ].
  Qed.

  (* the two RESTRICTED forms the arms below need: an arm that has already
     repurposed s1 (the default path's [c.addi s1,s1,-4]) or s1/s2/s3 and the
     two scratch registers (the C('U') preamble) can only thread the rest. *)
  Lemma ct_cs_hi_thr1 (M1 M m0 : regfile) :
    (forall r : mword 5, is_cs_idx r = true -> r <> Rs1 ->
       M1 !!! Regidx r = M !!! Regidx r) ->
    ct_cs_hi M m0 -> ct_cs_hi M1 m0.
  Proof using .
    intros Hthr (Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11).
    unfold ct_cs_hi. split_and!;
      [ rewrite (Hthr Rs2  ltac:(vm_compute; reflexivity) ltac:(reg_neq)); exact Q2
      | rewrite (Hthr Rs3  ltac:(vm_compute; reflexivity) ltac:(reg_neq)); exact Q3
      | rewrite (Hthr Rs4  ltac:(vm_compute; reflexivity) ltac:(reg_neq)); exact Q4
      | rewrite (Hthr Rs5  ltac:(vm_compute; reflexivity) ltac:(reg_neq)); exact Q5
      | rewrite (Hthr Rs6  ltac:(vm_compute; reflexivity) ltac:(reg_neq)); exact Q6
      | rewrite (Hthr Rs7  ltac:(vm_compute; reflexivity) ltac:(reg_neq)); exact Q7
      | rewrite (Hthr Rs8  ltac:(vm_compute; reflexivity) ltac:(reg_neq)); exact Q8
      | rewrite (Hthr Rs9  ltac:(vm_compute; reflexivity) ltac:(reg_neq)); exact Q9
      | rewrite (Hthr Rs10 ltac:(vm_compute; reflexivity) ltac:(reg_neq)); exact Q10
      | rewrite (Hthr Rs11 ltac:(vm_compute; reflexivity) ltac:(reg_neq)); exact Q11 ].
  Qed.

  Lemma ct_cs_hi_refl (M : regfile) : ct_cs_hi M M.
  Proof using . unfold ct_cs_hi. split_and!; reflexivity. Qed.

  Lemma ct_cs_hi_thr3 (M1 M m0 : regfile) :
    (forall r : mword 5, is_cs_idx r = true ->
       r <> csp_rs1 -> r <> Rs0 -> r <> Rs1 -> M1 !!! Regidx r = M !!! Regidx r) ->
    ct_cs_hi M m0 -> ct_cs_hi M1 m0.
  Proof using .
    intros Hthr (Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11).
    unfold ct_cs_hi. split_and!;
      [ rewrite (Hthr Rs2  ltac:(vm_compute; reflexivity) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)); exact Q2
      | rewrite (Hthr Rs3  ltac:(vm_compute; reflexivity) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)); exact Q3
      | rewrite (Hthr Rs4  ltac:(vm_compute; reflexivity) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)); exact Q4
      | rewrite (Hthr Rs5  ltac:(vm_compute; reflexivity) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)); exact Q5
      | rewrite (Hthr Rs6  ltac:(vm_compute; reflexivity) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)); exact Q6
      | rewrite (Hthr Rs7  ltac:(vm_compute; reflexivity) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)); exact Q7
      | rewrite (Hthr Rs8  ltac:(vm_compute; reflexivity) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)); exact Q8
      | rewrite (Hthr Rs9  ltac:(vm_compute; reflexivity) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)); exact Q9
      | rewrite (Hthr Rs10 ltac:(vm_compute; reflexivity) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)); exact Q10
      | rewrite (Hthr Rs11 ltac:(vm_compute; reflexivity) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)); exact Q11 ].
  Qed.

  Lemma ct_cs_top_thr3 (M1 M m0 : regfile) :
    (forall r : mword 5, r <> Rs1 -> r <> Rs2 -> r <> Rs3 -> r <> Ra4 -> r <> Ra5 ->
       M1 !!! Regidx r = M !!! Regidx r) ->
    ct_cs_top M m0 -> ct_cs_top M1 m0.
  Proof using .
    intros Hthr (Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11).
    unfold ct_cs_top. split_and!;
      [ rewrite (Hthr Rs4  ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)); exact Q4
      | rewrite (Hthr Rs5  ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)); exact Q5
      | rewrite (Hthr Rs6  ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)); exact Q6
      | rewrite (Hthr Rs7  ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)); exact Q7
      | rewrite (Hthr Rs8  ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)); exact Q8
      | rewrite (Hthr Rs9  ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)); exact Q9
      | rewrite (Hthr Rs10 ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)); exact Q10
      | rewrite (Hthr Rs11 ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)); exact Q11 ].
  Qed.

  (* ---- the 32-bit ALU laws the three ring paths share --------------- *)

  (* the [c.addiw a5,a5,-1] the kill loop and the backspace arm open with,
     at the 32-bit value the cell then takes *)
  Lemma ct_addiw_dec (e : mword 32) :
    sign_extend' 64 (subrange_vec_dec
       (add_vec (sign_extend' 64 e)
                (sign_extend' 64 (sign_extend' 12 (mword_of_int 63 : mword 6)))) 31 0)
    = sign_extend' 64 (add_vec e (mword_of_int (-1) : mword 32)).
  Proof using .
    rewrite <- trunc32_subrange. rewrite trunc32_add !trunc32_sext.
    assert (HK : trunc32 (sign_extend' 64 (sign_extend' 12 (mword_of_int 63 : mword 6)))
                 = (mword_of_int (-1) : mword 32))
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite HK. reflexivity.
  Qed.

  (* [cons.e++]: the [addiw rd,rs,1] both store paths open with *)
  Lemma ct_addiw_inc (e : mword 32) :
    sign_extend' 64 (subrange_vec_dec
       (add_vec (sign_extend' 64 e) (sign_extend' 64 (mword_of_int 1 : mword 12))) 31 0)
    = sign_extend' 64 (add_vec e (mword_of_int 1 : mword 32)).
  Proof using .
    rewrite <- trunc32_subrange. rewrite trunc32_add !trunc32_sext.
    assert (HK : trunc32 (sign_extend' 64 (mword_of_int 1 : mword 12))
                 = (mword_of_int 1 : mword 32))
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite HK. reflexivity.
  Qed.

  (* [cons.e - cons.r]: the [c.subw] both guards use, at two cell values *)
  Lemma ct_subw_sext (x y : mword 32) :
    sign_extend' 64
      (sub_vec (subrange_vec_dec (sign_extend' 64 x : mword 64) 31 0 : mword 32)
               (subrange_vec_dec (sign_extend' 64 y : mword 64) 31 0 : mword 32))
    = sign_extend' 64 (sub_vec x y).
  Proof using . rewrite <- !trunc32_subrange. rewrite !trunc32_sext. reflexivity. Qed.

  (* [% INPUT_BUF_SIZE], compiled as [andi …,127]: the index is a nat below
     128 for EVERY value of the word, which is the whole reason
     [ConsoleInv.cons_res] can relate the three indices to nothing.  Three
     sites compute it -- the kill loop and the two store paths. *)
  Lemma ct_ring_idx (e : mword 32) :
    exists i : nat,
      (i < INPUT_BUF_SIZE)%nat /\
      and_vec (sign_extend' 64 e : mword 64) (sign_extend' 64 (mword_of_int 127 : mword 12))
      = (mword_of_int (Z.of_nat i) : mword 64).
  Proof using .
    set (idxw := and_vec (sign_extend' 64 e : mword 64)
                   (sign_extend' 64 (mword_of_int 127 : mword 12))).
    assert (Hb : (0 <= bv_unsigned idxw < 128)%Z)
      by (rewrite /idxw;
          apply (w32_and_mask_bound _ (mword_of_int 127) 7 ltac:(lia)
                   ltac:(vm_compute; reflexivity))).
    exists (Z.to_nat (bv_unsigned idxw)). split.
    - rewrite /INPUT_BUF_SIZE. lia.
    - rewrite Z2Nat.id; [| lia]. symmetry. apply w32_moi_unsigned.
  Qed.

  (* ---- THE TAG PREMISE'S BYTE ---------------------------------------
     a0 arrives ZERO-extended ([Riscv.rv64d.extend_value] at
     [is_unsigned = true], which is what SpecConsoleintr's premise spells),
     so the [sb] that appends it stores the byte itself and the two
     comparisons against '\r' are comparisons of the byte. *)
  Lemma ct_arg_zext (c : bv 8) :
    (extend_value (n := 8) true (c : mword 8) : mword 64)
    = (zero_extend' 64 (c : mword 8) : mword 64).
  Proof using . reflexivity. Qed.

  Lemma ct_arg_trunc8 (c : bv 8) :
    trunc8 (extend_value (n := 8) true (c : mword 8) : mword 64) = c.
  Proof using . rewrite ct_arg_zext. apply trunc8_zext8. Qed.

  Lemma ct_arg_ne13 (c : bv 8) :
    eq_vec (extend_value (n := 8) true (c : mword 8) : mword 64)
           (mword_of_int 13 : mword 64) = false ->
    c <> (mword_of_int 13 : mword 8).
  Proof using . intros Hne Heq. rewrite Heq in Hne. vm_compute in Hne. discriminate. Qed.

  Lemma ct_arg_eq13 (c : bv 8) :
    eq_vec (extend_value (n := 8) true (c : mword 8) : mword 64)
           (mword_of_int 13 : mword 64) = true ->
    c = (mword_of_int 13 : mword 8).
  Proof using .
    intro H. apply eq_vec_true_iff in H.
    apply (f_equal (fun w : mword 64 => trunc8 w)) in H.
    rewrite ct_arg_trunc8 in H. rewrite H.
    apply bv_eq; vm_compute; reflexivity.
  Qed.

  (* THE BYTE OUT OF A ZERO-EXTENDED [switch] COMPARISON (lane OUT-FUPD).
     [ct_arg_eq13] specialised to whatever constant the case tested, which
     is how the three ERASE arms discharge [SpecConsoleintr.cons_erase]'s
     guard: the switch's own [beq] is the only thing that knows which byte
     arrived, and the echo's justification is guarded by it. *)
  Lemma ct_arg_eq_byte (c : bv 8) (z : Z) :
    eq_vec (extend_value (n := 8) true (c : mword 8) : mword 64)
           (mword_of_int z : mword 64) = true ->
    c = trunc8 (mword_of_int z : mword 64).
  Proof using .
    intro H. apply eq_vec_true_iff in H.
    apply (f_equal (fun w : mword 64 => trunc8 w)) in H.
    rewrite ct_arg_trunc8 in H. exact H.
  Qed.

  (* ...AND THE NUL ARM'S OWN READING (relax-d2, lane K2): the [c.beqz]
     at +0x02c decides [c = 0], which is the first disjunct of
     [ConsLog.cons_drop_ok]. *)
  Lemma ct_arg_nul (c : bv 8) :
    eq_vec (extend_value (n := 8) true (c : mword 8) : mword 64)
           (zero_reg : mword 64) = true ->
    bv_unsigned c = 0%Z.
  Proof using .
    intro H.
    assert (Hz : (zero_reg : mword 64) = (mword_of_int 0 : mword 64))
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Hz in H. rewrite (ct_arg_eq_byte c 0 H).
    vm_compute; reflexivity.
  Qed.

  (* the byte the '\r' arm stores, at the translation's own spelling *)
  Lemma ct_trunc8_10 :
    trunc8 (mword_of_int 10 : mword 64) = (mword_of_int 10 : mword 8).
  Proof using . apply bv_eq; vm_compute; reflexivity. Qed.

  (* ---- WHICH BYTE CONSPUTC PUSHED ---------------------------------
     [SpecConsputc.cp_byte] is spelled exactly as [trunc8], so the three
     bridges above apply to it unchanged. *)
  Lemma ct_cp_trunc (w : mword 64) : cp_byte w = trunc8 w.
  Proof using . reflexivity. Qed.

  (* a ZERO-EXTENDED BYTE IS NOT [BACKSPACE].  BACKSPACE is 0x100, which no
     byte reaches, so the store arms take consputc's ordinary arm and the
     byte they echo is the byte itself. *)
  Lemma ct_arg_ne256 (c : bv 8) :
    eq_vec (extend_value (n := 8) true (c : mword 8) : mword 64)
           (mword_of_int 256 : mword 64) = false.
  Proof using .
    destruct (eq_vec (extend_value (n := 8) true (c : mword 8) : mword 64)
                     (mword_of_int 256 : mword 64)) eqn:He; [| reflexivity].
    exfalso. apply eq_vec_true_iff in He.
    pose proof He as He'.
    apply (f_equal (fun w : mword 64 => trunc8 w)) in He'.
    rewrite ct_arg_trunc8 in He'.
    assert (Ht : trunc8 (mword_of_int 256 : mword 64) = (mword_of_int 0 : mword 8))
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Ht in He'. rewrite He' in He.
    apply (f_equal bv_unsigned) in He. vm_compute in He. discriminate.
  Qed.

  (* the translation, at the two arms' own spellings *)
  Lemma ct_echo_of_13 : echo_of (mword_of_int 13 : mword 8) = (mword_of_int 10 : mword 8).
  Proof using .
    unfold echo_of.
    assert (E : eq_vec (mword_of_int 13 : mword 8) (mword_of_int 13 : mword 8) = true)
      by (vm_compute; reflexivity).
    rewrite E. reflexivity.
  Qed.

  Lemma ct_echo_of_ne (c : bv 8) :
    c <> (mword_of_int 13 : mword 8) -> echo_of c = c.
  Proof using .
    intros Hne. unfold echo_of.
    destruct (eq_vec (c : mword 8) (mword_of_int 13 : mword 8)) eqn:E;
      [| reflexivity].
    apply eq_vec_true_iff in E. contradiction.
  Qed.

  (* ---- THE RING INDEX, AS THE COUPLING'S SLOT ------------------------
     [ct_ring_idx] hands out SOME [i] below 128; the row is indexed by
     [ConsoleInv.cons_slot], and the two are the same number. *)
  Lemma ct_idx_slot (x : mword 32) (i : nat) :
    (i < INPUT_BUF_SIZE)%nat ->
    and_vec (sign_extend' 64 x : mword 64)
            (sign_extend' 64 (mword_of_int 127 : mword 12))
      = (mword_of_int (Z.of_nat i) : mword 64) ->
    i = cons_slot x 0.
  Proof using .
    intros Hlt Hw. rewrite <- (cons_slot_of_and x).
    rewrite Hw moi64_unsigned.
    assert (Hb : (0 <= Z.of_nat i < 2 ^ 64)%Z).
    { rewrite /INPUT_BUF_SIZE in Hlt.
      assert (H64 : (2 ^ 64)%Z = 18446744073709551616%Z)
        by (vm_compute; reflexivity).
      rewrite H64. lia. }
    rewrite (bvw64_small (Z.of_nat i) Hb) Nat2Z.id. reflexivity.
  Qed.

  (* ---- THE TWO 32-BIT COMPARISONS, AT THE WORDS THEMSELVES ------------
     both guards compare SIGN-EXTENDED cells, and the extension is
     injective ([RiscvExtras.sext64_32_inj]). *)
  Lemma ct_ne32 (x y : mword 32) :
    neq_vec (sign_extend' 64 x : mword 64) (sign_extend' 64 y : mword 64) = true ->
    x <> y.
  Proof using .
    intros Hn Heq. subst y. unfold neq_vec in Hn.
    rewrite eq_vec_refl in Hn. discriminate.
  Qed.

  Lemma ct_eqf32 (x y : mword 32) :
    eq_vec (sign_extend' 64 x : mword 64) (sign_extend' 64 y : mword 64) = false ->
    x <> y.
  Proof using . intros Hn Heq. subst y. rewrite eq_vec_refl in Hn. discriminate. Qed.

  (* the ring-room guard at +0x044: [bltu a4,a5] NOT taken is
     [cons.e - cons.r <= 127], read off the 32-bit difference the [c.subw]
     computed.  The comparison is UNSIGNED on the sign-extended difference,
     so a difference that does not fit in 7 bits is refuted twice over. *)
  Lemma ct_room (x : mword 32) :
    zopz0zI_u (mword_of_int 127 : mword 64) (sign_extend' 64 x : mword 64) = false ->
    (bv_unsigned x < Z.of_nat INPUT_BUF_SIZE)%Z.
  Proof using .
    intro H. rewrite cons_bufz.
    unfold zopz0zI_u in H. apply Z.ltb_ge in H. rewrite !uint_unsigned in H.
    assert (H127 : bv_unsigned (mword_of_int 127 : mword 64) = 127%Z)
      by (vm_compute; reflexivity).
    rewrite H127 in H.
    pose proof (bv_unsigned_in_range _ (sign_extend' 64 x : mword 64)) as Hr0.
    assert (H32 : (2 ^ 32)%Z = 4294967296%Z) by (vm_compute; reflexivity).
    assert (Hsm : (0 <= bv_unsigned (sign_extend' 64 x : mword 64) < 2 ^ 32)%Z)
      by (rewrite H32; lia).
    assert (Hw : bv_wrap 32 (bv_unsigned (sign_extend' 64 x : mword 64))
                 = bv_unsigned x).
    { rewrite <- (trunc32_unsigned (sign_extend' 64 x)). by rewrite trunc32_sext. }
    rewrite cons_bvw (Z.mod_small _ _ Hsm) in Hw.
    rewrite <- Hw. lia.
  Qed.

  (* ...AND THE GUARD'S OTHER ARM, which the DROP needs (relax-d2, lane
     K2): [bltu 127, e-r] TAKEN is [cons.e - cons.r >= 128], and with
     [cons_ok]'s [<= 128] that pins the live range at exactly the whole
     ring.  The difference is below 2^31 either way, so the sign extension
     the comparison runs on is the identity and the 64-bit test IS the test
     on the difference. *)
  Lemma ct_nofit (x : mword 32) :
    (bv_unsigned x <= Z.of_nat INPUT_BUF_SIZE)%Z ->
    zopz0zI_u (mword_of_int 127 : mword 64) (sign_extend' 64 x : mword 64) = true ->
    (Z.of_nat INPUT_BUF_SIZE <= bv_unsigned x)%Z.
  Proof using .
    intros Hle H. rewrite cons_bufz in Hle. rewrite cons_bufz.
    pose proof (bv_unsigned_in_range _ x) as [Hx0 _].
    assert (Hsg : bv_signed x = bv_unsigned x).
    { unfold bv_signed, bv_swrap.
      change (bv_half_modulus (MachineWord.MachineWord.Z_idx 32))
        with 2147483648%Z.
      unfold bv_wrap.
      change (bv_modulus (MachineWord.MachineWord.Z_idx 32))
        with 4294967296%Z.
      rewrite (Z.mod_small (bv_unsigned x + 2147483648) 4294967296
                 ltac:(lia)). lia. }
    assert (Hsx : bv_unsigned (sign_extend' 64 x : mword 64) = bv_unsigned x).
    { rewrite sext32_64_moi moi64_unsigned Hsg. apply bvw64_small.
      change (2 ^ 64)%Z with 18446744073709551616%Z. lia. }
    unfold zopz0zI_u in H. apply Z.ltb_lt in H. rewrite !uint_unsigned in H.
    assert (H127 : bv_unsigned (mword_of_int 127 : mword 64) = 127%Z)
      by (vm_compute; reflexivity).
    rewrite H127 Hsx in H. lia.
  Qed.

  (* =================================================================== *)
  (*  THE RING'S GHOST HALF, as one proposition (app-echo.md, lane         *)
  (*  CONS-CURSOR, C2).                                                    *)
  (*                                                                       *)
  (*  Every block of this function takes [ConsoleInv.cons_res] APART -- it *)
  (*  reads and writes the three index words, so the ring cannot travel as *)
  (*  an existential -- and the rest of the resource has to travel with it. *)
  (*  Naming it keeps that to ONE conjunct and NO new binders: the committed *)
  (*  prefix, the editable window, the consumed count, the reader's cursor,  *)
  (*  the high-water mark and the dirty marker are all quantified HERE, and  *)
  (*  only the two blocks that MOVE them ([ct_gh_commit], [ct_gh_push]) ever *)
  (*  open it.                                                              *)
  (* =================================================================== *)
  (* ...AND THE INPUT LOG RIDES HERE TOO (app-echo.md, lane CONS-IO,
     milestone B).  [pe] is the log entry this call still OWES: [None]
     everywhere but inside an erase arm, which pops the ring before it has
     echoed anything and so cannot have filed its erase character yet.
     [ConsoleInv.cons_owed] is what the two states mean, and the seal
     ([ct_gh_res]) is only legal at [None] -- which is the whole content of
     "the lock payload holds when the lock is free". *)
  Definition ct_gh `{XI : CurCtx} (cn : cons_names)
      (pe : option (list mobs * bv 8)) (rr ww ee : mword 32)
      (bs : list (bv 8)) (ts : list (option (list mobs))) : iProp Σ :=
    (∃ (cur nrd ndl : nat) (st pd : list (list mobs * bv 8))
       (hh : option (list mobs)) (L0 : list LogEntryDefs.log_entry) (gp : bool),
       ⌜ cons_stored rr ww cur st bs ts ⌝ ∗
       ⌜ cons_pend rr ww ee pd bs ts ⌝ ∗
       ⌜ cons_chain (st ++ pd) ⌝ ∗
       ⌜ cons_below (st ++ pd) hh ⌝ ∗
       (* THE ERA ([ConsoleInv.cons_res]'s, the S2k follow-up) *)
       ⌜ cons_era (st ++ pd) (cn_era cn) ⌝ ∗
       cons_stored_auth cn st ∗ cons_cursor cn nrd ∗ cons_hi cn hh ∗
       cons_logm cn L0 ∗ ⌜ cons_owed L0 pe (st ++ pd) gp ⌝ ∗
       (* THE DELIVERED-COUNT BOUND (relax-d2, lane K2), exactly
          [ConsoleInv.cons_res]'s: nothing in this function moves either
          number, and the full-ring drop arm is the one place that spends
          them. *)
       cons_dlcnt cn ndl ∗ ⌜ (nrd <= cur)%nat ⌝ ∗ ⌜ (ndl <= nrd)%nat ⌝ ∗
       (⌜ cur = nrd ⌝ ∨ cons_dirty_lb cn))%I.

  (* the ring, assembled and taken apart, at the one shape every block of
     this function speaks *)
  Lemma ct_gh_res `{XI : CurCtx} (cn : cons_names) (rr ww ee : mword 32)
      (bs : list (bv 8)) (ts : list (option (list mobs))) :
    length bs = INPUT_BUF_SIZE -> length ts = INPUT_BUF_SIZE ->
    cons_ok rr ww ee -> cons_row rr ee bs ts ->
    a_cons_r ↦₄ rr -∗ a_cons_w ↦₄ ww -∗ a_cons_e ↦₄ ee -∗
    cons_data bs -∗ cons_tags ts -∗ ct_gh cn None rr ww ee bs ts -∗ cons_res cn.
  Proof using .
    intros Hlb Hlt Hok Hrow.
    iIntros "Hrc Hwc Hec Hdat Hts Hgh".
    iDestruct "Hgh" as (cur nrd ndl st pd hh L0 gp)
      "(%Hst & %Hpd & %Hch & %Hbl & %Hera & Ha & Hcur & Hhi & Hlm & %Hlog & Hdc &
        %Hnc & %Hdn & Hmk)".
    rewrite /cons_res.
    iExists rr, ww, ee, bs, ts, cur, nrd, ndl, st, pd, hh, L0, gp.
    iFrame "Hrc Hwc Hec Hdat Hts Ha Hcur Hhi Hlm Hdc Hmk".
    iPureIntro. split_and!;
      [ exact Hlb | exact Hlt | exact Hok | exact Hrow | exact Hst | exact Hpd
      | exact Hch | exact Hbl | exact Hera | exact Hlog | exact Hnc | exact Hdn ].
  Qed.

  Lemma ct_res_gh `{XI : CurCtx} (cn : cons_names) :
    cons_res cn -∗
    ∃ (rr ww ee : mword 32) (bs : list (bv 8))
      (ts : list (option (list mobs))),
      ⌜ length bs = INPUT_BUF_SIZE ⌝ ∗ ⌜ length ts = INPUT_BUF_SIZE ⌝ ∗
      ⌜ cons_ok rr ww ee ⌝ ∗ ⌜ cons_row rr ee bs ts ⌝ ∗
      a_cons_r ↦₄ rr ∗ a_cons_w ↦₄ ww ∗ a_cons_e ↦₄ ee ∗
      cons_data bs ∗ cons_tags ts ∗ ct_gh cn None rr ww ee bs ts.
  Proof using .
    iIntros "H". rewrite /cons_res.
    iDestruct "H" as (rr ww ee bs ts cur nrd ndl st pd hh L0 gp)
      "(Hrc & Hwc & Hec & %Hlb & %Hlt & %Hok & %Hrow & %Hst & %Hpd & %Hch &
        %Hbl & %Hera & Hdat & Hts & Ha & Hcur & Hhi & Hlm & %Hlog & Hdc & %Hnc &
        %Hdn & Hmk)".
    iExists rr, ww, ee, bs, ts.
    iSplitR; [by iPureIntro |]. iSplitR; [by iPureIntro |].
    iSplitR; [by iPureIntro |]. iSplitR; [by iPureIntro |].
    iFrame "Hrc Hwc Hec Hdat Hts".
    rewrite /ct_gh. iExists cur, nrd, ndl, st, pd, hh, L0, gp.
    iFrame "Ha Hcur Hhi Hlm Hdc Hmk". iPureIntro. split_and!;
      [ exact Hst | exact Hpd | exact Hch | exact Hbl | exact Hera | exact Hlog
      | exact Hnc | exact Hdn ].
  Qed.

  (* =================================================================== *)
  (*  K2 (relax-d2): WHAT A FULL RING PAYS THE BOUNDARY.                  *)
  (*                                                                      *)
  (*  A drop arm owes [ConsLog.cons_drop_ok], and the FULL-RING disjunct   *)
  (*  is the only one the switch's guard cannot hand over: it is a fact    *)
  (*  about the LOG and the DELIVERED COUNT.  The ring has both.  Its      *)
  (*  [128] live entries are [cur + 128] entries of the committed-plus-    *)
  (*  pending sequence ([cons_stored_commit]), every one of them an ECHOED *)
  (*  log entry ([cons_logged]) at a history no other entry has            *)
  (*  ([cons_chain]) -- so the log holds at least [cur + 128] echoed       *)
  (*  entries -- and the delivered count is at or below [cur].  The two    *)
  (*  ghost halves come OUT so the open can agree them with the port       *)
  (*  invariant's, and go back unchanged: an open moves neither.           *)
  (* =================================================================== *)
  Lemma ct_gh_full_log `{XI : CurCtx} (cn : cons_names) (rr ww ee : mword 32)
      (bs : list (bv 8)) (ts : list (option (list mobs))) :
    cons_ok rr ww ee ->
    (Z.of_nat INPUT_BUF_SIZE <= bv_unsigned (sub_vec ee rr))%Z ->
    ct_gh cn None rr ww ee bs ts -∗
    ∃ (L0 : list LogEntryDefs.log_entry) (ndl : nat),
      ⌜ (128 + ndl <= ConsLog.echoed_count L0)%nat ⌝ ∗
      cons_logm cn L0 ∗ cons_dlcnt cn ndl ∗
      (cons_logm cn L0 -∗ cons_dlcnt cn ndl -∗
         ct_gh cn None rr ww ee bs ts).
  Proof using .
    intros Hok Hfull. iIntros "Hgh".
    iDestruct "Hgh" as (cur nrd ndl st pd hh L0 gp)
      "(%Hst & %Hpd & %Hch & %Hbl & %Hera & Ha & Hcur & Hhi & Hlm & %Hlog & Hdc &
        %Hnc & %Hdn & Hmk)".
    iExists L0, ndl.
    iSplitR.
    { iPureIntro.
      pose proof (cons_stored_commit rr ww ee cur st pd bs ts Hok Hst Hpd)
        as [Hlen _].
      pose proof (proj2 Hok) as Hle128.
      assert (He128 : bv_unsigned (sub_vec ee rr) = Z.of_nat INPUT_BUF_SIZE)
        by lia.
      rewrite He128 in Hlen.
      pose proof (cons_logged_count L0 (st ++ pd) (proj1 Hlog) Hch) as Hcnt.
      rewrite Hlen in Hcnt. rewrite /INPUT_BUF_SIZE in Hcnt. lia. }
    iFrame "Hlm Hdc". iIntros "Hlm Hdc".
    iExists cur, nrd, ndl, st, pd, hh, L0, gp.
    iFrame "Ha Hcur Hhi Hlm Hdc Hmk". iPureIntro. split_and!;
      [ exact Hst | exact Hpd | exact Hch | exact Hbl | exact Hera | exact Hlog
      | exact Hnc | exact Hdn ].
  Qed.

  (* THE EDIT ([cons.e--], backspace and C('U')): the editable window loses
     its last entry.  The committed prefix is out of reach -- the code tests
     [cons.e != cons.w] first -- so [stored] never shrinks, and the chain
     and the mark survive because a prefix of a chain is a chain. *)
  (* ...AND IT IS ONLY LEGAL WHILE THE ERASE CHARACTER IS OWED (lane
     CONS-IO, milestone B, ruling F2).  A pop takes an ECHOED entry out of
     the ring, so the log now accounts for a byte the reader will never be
     handed -- and the only thing that closes that gap is the erase
     character this call is about to file.  [pe = Some (hb, cb)] is the
     promise, and it is what carries the accumulator at [true] across the
     C('U') loop, whose glyph count nobody knows until it ends. *)
  Lemma ct_gh_pop `{XI : CurCtx} (cn : cons_names)
      (hb : list mobs) (cb : bv 8) (rr ww ee : mword 32)
      (bs : list (bv 8)) (ts : list (option (list mobs))) :
    ee <> ww ->
    ct_gh cn (Some (hb, cb)) rr ww ee bs ts -∗
    ct_gh cn (Some (hb, cb)) rr ww
      (add_vec ee (mword_of_int (-1) : mword 32)) bs ts.
  Proof using .
    intro Hne. iIntros "Hgh".
    iDestruct "Hgh" as (cur nrd ndl st pd hh L0 gp)
      "(%Hst & %Hpd & %Hch & %Hbl & %Hera & Ha & Hcur & Hhi & Hlm & %Hlog & Hdc &
        %Hnc & %Hdn & Hmk)".
    pose proof (cons_sub_ne ee ww Hne) as Hge.
    pose proof (proj1 Hpd) as Hlpd.
    assert (Hpdne : pd <> []).
    { intro Hc. rewrite Hc in Hlpd. cbn [length] in Hlpd. lia. }
    set (dflt := (inhabitant : list mobs * bv 8)).
    pose proof (app_removelast_last dflt Hpdne) as Hsplit.
    assert (Hpfx : removelast pd `prefix_of` pd)
      by (exists [last pd dflt]; exact Hsplit).
    (* the ring, as ONE snoc: that is the shape the pure law is stated at *)
    assert (Hsnoc : (st ++ pd)%list
                    = ((st ++ removelast pd) ++ [last pd dflt])%list).
    { rewrite <- app_assoc. by rewrite <- Hsplit. }
    rewrite /ct_gh.
    iExists cur, nrd, ndl, st, (removelast pd), hh, L0, gp.
    iFrame "Ha Hcur Hhi Hlm Hdc Hmk". iPureIntro. split_and!.
    - exact Hst.
    - apply (cons_pend_pop rr ww ee (removelast pd) (last pd dflt) bs ts Hge).
      rewrite <- Hsplit. exact Hpd.
    - apply (cons_chain_prefix (st ++ removelast pd) (st ++ pd));
        [ apply prefix_app; exact Hpfx | exact Hch ].
    - apply (cons_below_prefix (st ++ removelast pd) (st ++ pd) hh);
        [ apply prefix_app; exact Hpfx | exact Hbl ].
    - apply (cons_era_prefix (st ++ removelast pd) (st ++ pd));
        [ apply prefix_app; exact Hpfx | exact Hera ].
    - destruct Hlog as [-> Hall]. split; [reflexivity |].
      intro cs. apply (cons_log_ok_pop _ _ (last pd dflt));
        [ rewrite <- Hsnoc; exact Hch | rewrite <- Hsnoc; exact (Hall cs) ].
    - exact Hnc.
    - exact Hdn.
  Qed.

  (* THE COMMIT ([cons.w = cons.e]): the editable window becomes part of
     the committed prefix, and the window empties.  THE ONLY TRANSITION THAT
     EXTENDS [stored], reached from '\n', from C('D') and from the store
     that fills the ring. *)
  Lemma ct_gh_commit `{XI : CurCtx} (cn : cons_names)
      (pe : option (list mobs * bv 8)) (rr ww ee : mword 32)
      (bs : list (bv 8)) (ts : list (option (list mobs))) :
    cons_ok rr ww ee ->
    ct_gh cn pe rr ww ee bs ts ==∗ ct_gh cn pe rr ee ee bs ts.
  Proof using .
    intro Hok. iIntros "Hgh".
    iDestruct "Hgh" as (cur nrd ndl st pd hh L0 gp)
      "(%Hst & %Hpd & %Hch & %Hbl & %Hera & Ha & Hcur & Hhi & Hlm & %Hlog & Hdc &
        %Hnc & %Hdn & Hmk)".
    iMod (cons_stored_append cn st pd with "Ha") as "Ha".
    iModIntro. rewrite /ct_gh.
    iExists cur, nrd, ndl, ((st ++ pd)%list), (@nil (list mobs * bv 8)), hh,
            L0, gp.
    iFrame "Ha Hcur Hhi Hlm Hdc Hmk". iPureIntro. rewrite app_nil_r.
    split_and!;
      [ exact (cons_stored_commit rr ww ee cur st pd bs ts Hok Hst Hpd)
      | exact (cons_pend_commit rr ee bs ts) | exact Hch | exact Hbl
      | exact Hera
      (* THE SEQUENCE DOES NOT MOVE: a commit only re-labels which of its
         entries are committed, so every input-log clause is unchanged. *)
      | exact Hlog | exact Hnc | exact Hdn ].
  Qed.

  (* THE STORE at [cons.e]: the byte joins the editable window, its tag
     joins the column, and the ring's HIGH-WATER MARK moves to it.  The
     caller's half of the mark comes in and goes back out at the byte just
     filed, which is what re-establishes the PLIC payload's own clause at
     the popper's new anchor. *)
  (* ...AND THE LOG ENTRY IS FILED IN THE SAME GHOST STEP (lane CONS-IO,
     milestone B, ruling F2).  It has to be: between the append and the
     push the log's top would be an ECHOED entry ABOVE the ring's top,
     which is exactly the state [ConsoleInv.cons_gp_ok] at [false]
     forbids -- and the accumulator cannot be [true] either, because no
     erase character was typed.  So the store arm spends its echo (the
     chain, first), and then files and pushes at once. *)
  (* =================================================================== *)
  (*  WHAT AN ARM OWES THE LOG (redesign R2).                             *)
  (*                                                                      *)
  (*  [in_append]'s successor: the KERNEL's half of the arm, at the        *)
  (*  position it has reached, and the APPLICATION's licence to close it   *)
  (*  there.  The entry filed is [take j cs] -- what actually went out --  *)
  (*  which is why an arm that stops short of its plan ([ct_kill_run])     *)
  (*  needs no second shape, and why the window token is gone: holding     *)
  (*  the arm's half IS the exclusion it stood for.                        *)
  (* =================================================================== *)
  (* THE ERASE RUN IS NEVER ONE BYTE (relax-d2, K3): [consputc_bs] is three
     bytes, so no join of copies of it is a single-glyph echo.  It is what
     makes K3 -- "a store arm sends its byte" -- vacuous on the erase arms,
     which are the ones that may stop short of their plan. *)
  Lemma ct_erase_run_ne_one (i n : nat) (cb : bv 8) :
    ((mjoin (replicate i consputc_bs) ++ mjoin (replicate n consputc_bs))%list
     = [ConsLog.echo_of cb]) -> False.
  Proof using .
    destruct i as [|i']; cbn [replicate mjoin].
    - destruct n as [|n']; cbn [replicate mjoin]; [discriminate|].
      rewrite /consputc_bs. cbn [app]. discriminate.
    - rewrite /consputc_bs. cbn [app]. discriminate.
  Qed.

  Definition ct_append `{XI : CurCtx} (γu : uart_names) (hb : list mobs)
      (cb : bv 8) (cs : list (bv 8)) (j : nat) (Φ : iProp Σ) : iProp Σ :=
    ((* THE BYTE'S TWO ERA FACTS (relax-d2, lane K1): the machine was ON at
        its arrival and the arrival is THIS era's.  They ride the owed
        append because that is what reaches the CLOSE, where K1 places
        uartinit's flush witness at this byte. *)
     ⌜trace_shape hb true⌝ ∗ ⌜obs_boots hb = S gen_id⌝ ∗
     uart_arm γu (1/2) (Some (hb, cb, cs, j)) ∗
     cons_link Uart0 (S gen_id) ConsLog.EvClose Φ)%I.

  Lemma ct_gh_push `{XI : CurCtx} (cn : cons_names) (γu : uart_names)
      (rr ww ee : mword 32)
      (bs : list (bv 8)) (ts : list (option (list mobs)))
      (i : nat) (h : list mobs) (c : bv 8) (hh hg : option (list mobs))
      (cs : list (bv 8)) (j : nat) (Φ : iProp Σ) :
    (* the arms name the port they hold [dev_inv] for; the ring names it
       through [cn].  They are the same name, and that is [console_caps]'s
       own equation -- so it is a premise here rather than a rewrite at
       every call site. *)
    cn_uart cn = γu ->
    (* ...and the ring is THIS era's ([console_caps]'s other equation), so
       the byte's own era stamp is the ring's (the S2k follow-up) *)
    cn_era cn = S gen_id ->
    length bs = INPUT_BUF_SIZE -> length ts = INPUT_BUF_SIZE ->
    cons_ok rr ww ee ->
    (bv_unsigned (sub_vec ee rr) < Z.of_nat INPUT_BUF_SIZE)%Z ->
    i = cons_slot ee 0 ->
    obs_ends_in Uart0 h c ->
    ohist_ext hh h ->
    ohist_ext hg h ->
    (* WHAT ACTUALLY WENT OUT is one glyph: the arm ran its plan to the end *)
    take j cs = [ConsLog.echo_of c] ->
    (* ---- K3 (relax-d2): ...AND THE PLAN WAS THAT GLYPH, so the arm is at
       position 1 when it closes.  The store arms pass [j = length cs]. ---- *)
    (cs = [ConsLog.echo_of c] -> j = 1%nat) ->
    (* ---- K1 (relax-d2): which keystroke this arm is filing.  The byte's
       trace shape and era stamp come off [ct_pay], which every arm already
       carries; together they place uartinit's flush witness at [h]. ---- *)
    k1_next hg h ->
    uart_inv Uart0 γu -∗
    uart_rx_hi γu (1/2) hh -∗
    uart_log_hi γu (1/2) hg -∗
    ct_append γu h c cs j Φ -∗
    ct_gh cn None rr ww ee bs ts ={⊤}=∗
      uart_rx_hi γu (1/2) (Some h) ∗
      uart_log_hi γu (1/2) (Some h) ∗
      (* ...AND THE ARM'S HALF, BACK AT [None] (redesign R2): the close the
         arm just fired ended it, and the next byte may open its own. *)
      uart_arm γu (1/2) None ∗ Φ ∗
      ct_gh cn None rr ww (add_vec ee (mword_of_int 1 : mword 32))
        (<[i := cons_xlate c]> bs) (<[i := Some h]> ts).
  Proof using .
    intros <- Hcne Hlb Hlt Hok Hroom Hi Hends Hx Hxg Hes Hk3 Hk1.
    iIntros "#Hinv Hhi0 Hlgh (%Hsh & %Hbh & Harm & Hap) Hgh".
    iDestruct "Hgh" as (cur nrd ndl st pd hh1 L0 gp)
      "(%Hst & %Hpd & %Hch & %Hbl & %Hera & Ha & Hcur & Hhi & Hlm & %Hlog & Hdc &
        %Hnc & %Hdn & Hmk)".
    (* the two halves of the mark agree, which is what makes the ambient
       [ohist_ext hh h] a statement about the RING's own picture *)
    rewrite /cons_hi /uart_rx_hi.
    iDestruct (ghost_var_agree with "Hhi0 Hhi") as %<-.
    (* THE APPEND, out of the log's own mark, with the mirror moved beside
       it: the two halves agree, so [L0] IS the log. *)
    rewrite /cons_logm.
    iMod (uart_inv_cons_close (cn_uart cn) h c cs j hg L0 Φ
            ltac:(rewrite Hes; right; by left) Hk3
            Hsh Hbh Hk1 with "Hinv Hlgh [Hlm] Harm Hap")
      as "(Hlgh & Hlm & %Hbelow & Harm & HΦ)"; [ rewrite /uart_logm; iExact "Hlm" |].
    iEval (rewrite Hes) in "Hlm".
    iMod (ghost_var_update_halves (Some h) with "Hhi0 Hhi") as "[Hhi0 Hhi]".
    iModIntro. iFrame "Hhi0 Hlgh Harm HΦ". rewrite /ct_gh.
    iExists cur, nrd, ndl, st, ((pd ++ [(h, c)])%list), (Some h),
            ((L0 ++ [(h, c, [ConsLog.echo_of c])])%list), false.
    iFrame "Ha Hcur Hhi". rewrite /cons_logm /uart_logm. iFrame "Hlm".
    iFrame "Hdc Hmk". iPureIntro. rewrite app_assoc.
    split_and!.
    - exact (cons_stored_ins rr ww cur st bs ts i h c ee Hok Hroom Hi Hst).
    - exact (cons_pend_push rr ww ee pd bs ts i h c Hlb Hlt Hok Hroom Hi
               Hends Hpd).
    - exact (cons_chain_snoc ((st ++ pd)%list) hh h c Hch Hbl Hx).
    - exact (cons_below_snoc ((st ++ pd)%list) hh h c Hbl Hx).
    - apply (cons_era_snoc ((st ++ pd)%list) (cn_era cn) h c Hera).
      rewrite Hcne. exact Hbh.
    - exact (cons_log_ok_push L0 ((st ++ pd)%list) gp h c Hch Hbelow
               (cons_gtop_of_below _ hh h Hbl Hx) Hlog).
    - exact Hnc.
    - exact Hdn.
  Qed.

  (* A DROP -- a NUL byte, a full ring, an erase with nothing to erase.
     The ring does not move and the entry has NO echo, so the append is a
     plain step and the accumulator is untouched: this is the arm that
     files a shift where milestone A's predecessor filed nothing. *)
  Lemma ct_gh_drop `{XI : CurCtx} (cn : cons_names) (γu : uart_names)
      (rr ww ee : mword 32)
      (bs : list (bv 8)) (ts : list (option (list mobs)))
      (h : list mobs) (c : bv 8) (hg : option (list mobs))
      (cs : list (bv 8)) (j : nat) (Φ : iProp Σ) :
    cn_uart cn = γu ->
    obs_ends_in Uart0 h c ->
    ohist_ext hg h ->
    (* NOTHING went out: the arm closes where it opened *)
    take j cs = [] ->
    (* ---- K3 (relax-d2): vacuous on every drop, whose plan is [[]] ---- *)
    (cs = [ConsLog.echo_of c] -> j = 1%nat) ->
    (* ---- K1 (relax-d2): which keystroke this arm is filing.  The byte's
       trace shape and era stamp come off [ct_pay], which every arm already
       carries; together they place uartinit's flush witness at [h]. ---- *)
    k1_next hg h ->
    uart_inv Uart0 γu -∗
    uart_log_hi γu (1/2) hg -∗
    ct_append γu h c cs j Φ -∗
    ct_gh cn None rr ww ee bs ts ={⊤}=∗
      uart_log_hi γu (1/2) (Some h) ∗ uart_arm γu (1/2) None ∗ Φ ∗
      ct_gh cn None rr ww ee bs ts.
  Proof using .
    intros <- Hends Hxg Hes Hk3 Hk1.
    iIntros "#Hinv Hlgh (%Hsh & %Hbh & Harm & Hap) Hgh".
    iDestruct "Hgh" as (cur nrd ndl st pd hh L0 gp)
      "(%Hst & %Hpd & %Hch & %Hbl & %Hera & Ha & Hcur & Hhi & Hlm & %Hlog & Hdc &
        %Hnc & %Hdn & Hmk)".
    rewrite /cons_logm.
    iMod (uart_inv_cons_close (cn_uart cn) h c cs j hg L0 Φ
            ltac:(rewrite Hes; by left) Hk3
            Hsh Hbh Hk1 with "Hinv Hlgh [Hlm] Harm Hap")
      as "(Hlgh & Hlm & %Hbelow & Harm & HΦ)"; [ rewrite /uart_logm; iExact "Hlm" |].
    iEval (rewrite Hes) in "Hlm".
    iModIntro. iFrame "Hlgh Harm HΦ". rewrite /ct_gh.
    iExists cur, nrd, ndl, st, pd, hh, ((L0 ++ [(h, c, [])])%list), gp.
    iFrame "Ha Hcur Hhi". rewrite /cons_logm /uart_logm. iFrame "Hlm".
    iFrame "Hdc Hmk". iPureIntro. split_and!;
      [ exact Hst | exact Hpd | exact Hch | exact Hbl | exact Hera
      | exact (cons_log_ok_snoc_nil L0 ((st ++ pd)%list) gp (h, c, [])
                 eq_refl Hlog)
      | exact Hnc | exact Hdn ].
  Qed.

  (* ...AND THE SAME AT THE SEALED RING, which is the shape the two arms
     that never destruct it reach ([ct_dflt]'s NUL exit, [ct_kill_pre]'s
     empty-window exit). *)
  Lemma ct_res_drop `{XI : CurCtx} (cn : cons_names) (γu : uart_names)
      (h : list mobs) (c : bv 8) (hg : option (list mobs))
      (cs : list (bv 8)) (j : nat) (Φ : iProp Σ) :
    cn_uart cn = γu ->
    obs_ends_in Uart0 h c ->
    ohist_ext hg h ->
    take j cs = [] ->
    (* ---- K3 (relax-d2) ---- *)
    (cs = [ConsLog.echo_of c] -> j = 1%nat) ->
    (* ---- K1 (relax-d2): which keystroke this arm is filing.  The byte's
       trace shape and era stamp come off [ct_pay], which every arm already
       carries; together they place uartinit's flush witness at [h]. ---- *)
    k1_next hg h ->
    uart_inv Uart0 γu -∗
    uart_log_hi γu (1/2) hg -∗
    ct_append γu h c cs j Φ -∗
    cons_res cn ={⊤}=∗
      uart_log_hi γu (1/2) (Some h) ∗ uart_arm γu (1/2) None ∗ Φ ∗
      cons_res cn.
  Proof using .
    intros <- Hends Hxg Hes Hk3 Hk1. iIntros "#Hinv Hlgh Hap Hres".
    iDestruct (ct_res_gh cn with "Hres") as (rr ww ee bs ts)
      "(%Hlb & %Hlt & %Hok & %Hrow & Hrc & Hwc & Hec & Hdat & Hts & Hgh)".
    iMod (ct_gh_drop cn (cn_uart cn) rr ww ee bs ts h c hg cs j Φ
            eq_refl Hends Hxg Hes Hk3 Hk1
            with "Hinv Hlgh Hap Hgh") as "(Hlgh & Harm & HΦ & Hgh)".
    iModIntro. iFrame "Hlgh Harm HΦ".
    iApply (ct_gh_res cn rr ww ee bs ts Hlb Hlt Hok Hrow
              with "Hrc Hwc Hec Hdat Hts Hgh").
  Qed.

  (* AN ERASE, BEFORE IT POPS: the character is OWED.  xv6 writes
     [cons.e--] before it calls [consputc(BACKSPACE)], and the C('U') loop
     does it once per glyph, so the ring is short of logged-and-echoed
     entries long before the erase character reaches the log.  Owing it
     flips the accumulator up front, and the clause is stated over EVERY
     legal echo because the glyph count is not known until the loop ends. *)
  Lemma ct_gh_owe `{XI : CurCtx} (cn : cons_names) (γu : uart_names)
      (rr ww ee : mword 32)
      (bs : list (bv 8)) (ts : list (option (list mobs)))
      (h : list mobs) (c : bv 8) (hh : option (list mobs)) :
    cn_uart cn = γu ->
    ConsLog.cons_erase c = true ->
    obs_ends_in Uart0 h c ->
    ohist_ext hh h ->
    uart_rx_hi γu (1/2) hh -∗
    ct_gh cn None rr ww ee bs ts -∗
    uart_rx_hi γu (1/2) hh ∗ ct_gh cn (Some (h, c)) rr ww ee bs ts.
  Proof using .
    intros <- Her Hends Hx. iIntros "Hhi0 Hgh".
    iDestruct "Hgh" as (cur nrd ndl st pd hh1 L0 gp)
      "(%Hst & %Hpd & %Hch & %Hbl & %Hera & Ha & Hcur & Hhi & Hlm & %Hlog & Hdc &
        %Hnc & %Hdn & Hmk)".
    rewrite /cons_hi /uart_rx_hi.
    iDestruct (ghost_var_agree with "Hhi0 Hhi") as %<-.
    iFrame "Hhi0". rewrite /ct_gh.
    iExists cur, nrd, ndl, st, pd, hh, L0, true.
    iFrame "Ha Hcur Hhi Hlm Hdc Hmk". iPureIntro. split_and!;
      [ exact Hst | exact Hpd | exact Hch | exact Hbl | exact Hera | | exact Hnc
      | exact Hdn ].
    split; [reflexivity |]. intro cs.
    exact (cons_log_ok_owe L0 ((st ++ pd)%list) gp h c cs Hch
             (cons_gtop_of_below _ hh h Hbl Hx)
             (cons_ends_in_nonnil Uart0 h c Hends) Her Hlog).
  Qed.

  (* ...AND WHEN IT HAS ECHOED, IT PAYS: the entry goes in at exactly what
     went out, and the owed clause -- which was stated over every legal
     echo -- closes at that one. *)
  Lemma ct_gh_pay `{XI : CurCtx} (cn : cons_names) (γu : uart_names)
      (rr ww ee : mword 32)
      (bs : list (bv 8)) (ts : list (option (list mobs)))
      (h : list mobs) (c : bv 8) (es cs : list (bv 8)) (j : nat)
      (hg : option (list mobs)) (Φ : iProp Σ) :
    cn_uart cn = γu ->
    obs_ends_in Uart0 h c ->
    ohist_ext hg h ->
    ConsLog.cons_echo c es ->
    take j cs = es ->
    (* ---- K3 (relax-d2): the erase arms' plans are never one glyph
       ([ConsLog.cons_bs_join_app_not_single]), so this is vacuous ---- *)
    (cs = [ConsLog.echo_of c] -> j = 1%nat) ->
    (* ---- K1 (relax-d2): which keystroke this arm is filing.  The byte's
       trace shape and era stamp come off [ct_pay], which every arm already
       carries; together they place uartinit's flush witness at [h]. ---- *)
    k1_next hg h ->
    uart_inv Uart0 γu -∗
    uart_log_hi γu (1/2) hg -∗
    ct_append γu h c cs j Φ -∗
    ct_gh cn (Some (h, c)) rr ww ee bs ts ={⊤}=∗
      uart_log_hi γu (1/2) (Some h) ∗ uart_arm γu (1/2) None ∗ Φ ∗
      ct_gh cn None rr ww ee bs ts.
  Proof using .
    intros <- Hends Hxg Hecho Hes Hk3 Hk1.
    iIntros "#Hinv Hlgh (%Hsh & %Hbh & Harm & Hap) Hgh".
    iDestruct "Hgh" as (cur nrd ndl st pd hh L0 gp)
      "(%Hst & %Hpd & %Hch & %Hbl & %Hera & Ha & Hcur & Hhi & Hlm & %Hlog & Hdc &
        %Hnc & %Hdn & Hmk)".
    rewrite /cons_logm.
    iMod (uart_inv_cons_close (cn_uart cn) h c cs j hg L0 Φ
            ltac:(rewrite Hes; exact Hecho) Hk3
            Hsh Hbh Hk1 with "Hinv Hlgh [Hlm] Harm Hap")
      as "(Hlgh & Hlm & %Hbelow & Harm & HΦ)"; [ rewrite /uart_logm; iExact "Hlm" |].
    iEval (rewrite Hes) in "Hlm".
    iModIntro. iFrame "Hlgh Harm HΦ". rewrite /ct_gh.
    iExists cur, nrd, ndl, st, pd, hh, ((L0 ++ [(h, c, es)])%list), true.
    iFrame "Ha Hcur Hhi". rewrite /cons_logm /uart_logm. iFrame "Hlm".
    iFrame "Hdc Hmk". iPureIntro. split_and!;
      [ exact Hst | exact Hpd | exact Hch | exact Hbl | exact Hera
      | exact (proj2 Hlog es) | exact Hnc | exact Hdn ].
  Qed.

  (* WHAT THE CALLER GETS BACK: the high-water half, at whatever history the
     ring ended up holding -- the byte just filed if it was filed, and the
     mark unmoved if the byte was dropped or merely edited away.

     THE ECHO'S RECEIPT IS GONE (lane OUT-FUPD).  What the call put on the
     wire is no longer reported: the bytes were JUSTIFIED BEFORE THE STORE,
     out of [SpecConsoleintr.cons_echo_shift], and the consequence lives in
     the console UART's own invariant rather than in a receipt this
     function hands back.  What is left is the MARK, which is what the
     ring's order needs. *)
  Definition ct_hi_out (γu : uart_names) (hb : list mobs) (cb : bv 8)
      : iProp Σ :=
    (∃ hh' : option (list mobs),
       uart_rx_hi γu (1/2) hh' ∗ ⌜ ohist_le hh' (Some hb) ⌝)%I.

  (* THE KILL LOOP'S ACCUMULATOR is stronger on one count, and that is what
     the loop carries across its back edge: the mark is STRICTLY before
     [hb], because the loop files nothing.  With the echo's receipt retired
     there is nothing else to accumulate -- the erase triples are paid for
     one call at a time out of [ct_pay_erase] below. *)
  Definition ct_hi_kill (γu : uart_names) (hb : list mobs) : iProp Σ :=
    (∃ hh' : option (list mobs),
       uart_rx_hi γu (1/2) hh' ∗ ⌜ ohist_ext hh' hb ⌝)%I.

  Lemma ct_hi_kill_out (γu : uart_names) (hb : list mobs) (cb : bv 8) :
    ct_hi_kill γu hb -∗ ct_hi_out γu hb cb.
  Proof using .
    iIntros "H". iDestruct "H" as (hh') "(Hhi & %Hx)".
    iExists hh'. iFrame "Hhi".
    iPureIntro. exact (ohist_le_of_ext hh' hb Hx).
  Qed.

  (* the function's own exit, as a [wp_next] at the entry hart *)
  Definition ct_ret `{CID0 : CpuId} `{XI : CurCtx} (γu : uart_names)
      (hb : list mobs) (cb : bv 8) (pme : mword 64) (m0 : regfile)
      (K lvl : nat) (eb : bool) (b : bool) (lks : gset string) : iProp Σ :=
    (wp_next (CID0 := CID0) b pme (fun (CID : CpuId) =>
       ∀ Mf : regfile,
         ⌜ callee_saved m0 Mf /\ (forall r : regidx, r ∈ dom (rf_to_gmap Mf)) ⌝ -∗
         sie_cap_gpr KT1 Mf K b pme -∗
         cpu_own lvl eb pme b lks -∗
         kernel_text -∗ pc_is (ret_pc (m0 !!! Regidx Rra)) -∗
         ct_hi_out γu hb cb -∗
         (* ...AND THE LOG'S MARK, AT THIS BYTE (lane CONS-IO).  No
            existential and no disjunction: every arm of the switch logs, so
            the append has run by the time this function returns. *)
         uart_log_hi γu (1/2) (Some hb) -∗
         (* ...AND THE ARM'S HALF, AT [None] (redesign R2): no arm is open,
            which is what the window token used to stand for.  It is spent
            at the open and repaid by the arm's own close, so it leaves
            with the mark. *)
         uart_arm γu (1/2) None -∗
         mWP (Loop : expr riscv_lang)))%I.

  (* =================================================================== *)
  (*  +0x110 .. +0x118 -- THE EPILOGUE.                                   *)
  (* =================================================================== *)
  Lemma ct_epi `{CID : CpuId} `{XI : CurCtx} (CID0 : CPU)
      (γu : uart_names) (hb : list mobs) (cb : bv 8)
      (pme : mword 64) (m0 M : regfile) (K lvl : nat) (eb : bool)
      (sp0 : mword 64) (b : bool) (lks : gset string) :
    m0 !!! Regidx csp_rs1 = sp0 ->
    M !!! Regidx csp_rs1 = pa_stk sp0 6%nat ->
    ct_cs_hi M m0 ->
    (consoleintr_stack <= K)%nat ->
    (b = false \/ pme = zero_reg -> (CID : CPU) = CID0) ->
    kernel_text -∗
    sie_cap_gpr KT1 M (K - 6)%nat b pme -∗
    cpu_own lvl eb pme b lks -∗
    pc_is (mword_of_int (CT + 0x110)) -∗
    ct_saved sp0 m0 -∗ ct_rest sp0 -∗ ct_hi_out γu hb cb -∗
    uart_log_hi γu (1/2) (Some hb) -∗ uart_arm γu (1/2) None -∗
    ct_ret (CID0 := CID0) γu hb cb pme m0 K lvl eb b lks -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Hm0sp HMsp HMcs HK Hcr.
    iIntros "#Ht Hcg Hcnt Hpc (K1 & K2 & K3) Hrest Hhiout Hlgh Hwin Hcont".
    assert (Hb1 : add_vec (pa_stk sp0 6%nat)
                    (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000")))
                  = pa_stk sp0 1) by (apply ct_slot_bridge; pcw).
    assert (Hb2 : add_vec (pa_stk sp0 6%nat)
                    (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000")))
                  = pa_stk sp0 2) by (apply ct_slot_bridge; pcw).
    assert (Hb3 : add_vec (pa_stk sp0 6%nat)
                    (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000")))
                  = pa_stk sp0 3) by (apply ct_slot_bridge; pcw).
    (* +0x110  c.ldsp ra,40(sp) *)
    iApply (wp_cldsp_s_sconf (mword_of_int (CT + 0x110)) (mword_of_int 5 : mword 6) Rra
              M (K - 6)%nat (m0 !!! Regidx Rra) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc [] [K1]").
    { iApply (cnti_110 with "Ht"). }
    { iEval (rewrite HMsp Hb1). iExact "K1". }
    iIntros (CIDe0 Hse0) "Hcg Hpc K1". iEval (rewrite HMsp Hb1) in "K1".
    set (E1 := <[Regidx Rra := regval_into_reg (m0 !!! Regidx Rra)]> M).
    assert (HE1sp : E1 !!! Regidx csp_rs1 = pa_stk sp0 6%nat)
      by (rewrite /E1 upd_ne; [exact HMsp | reg_neq]).
    assert (Pe12 : add_vec_int (mword_of_int (CT + 0x110) : mword 64) 2
                  = mword_of_int (CT + 0x112)) by pcw.
    iEval (rewrite Pe12) in "Hpc".
    (* +0x112  c.ldsp s0,32(sp) *)
    iApply (wp_cldsp_s_sconf (mword_of_int (CT + 0x112)) (mword_of_int 4 : mword 6) Rs0
              E1 (K - 6)%nat (m0 !!! Regidx Rs0) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc [] [K2]").
    { iApply (cnti_112 with "Ht"). }
    { iEval (rewrite HE1sp Hb2). iExact "K2". }
    iIntros (CIDe1 Hse1) "Hcg Hpc K2". iEval (rewrite HE1sp Hb2) in "K2".
    set (E2 := <[Regidx Rs0 := regval_into_reg (m0 !!! Regidx Rs0)]> E1).
    assert (HE2sp : E2 !!! Regidx csp_rs1 = pa_stk sp0 6%nat)
      by (rewrite /E2 upd_ne; [exact HE1sp | reg_neq]).
    assert (Pe14 : add_vec_int (mword_of_int (CT + 0x112) : mword 64) 2
                  = mword_of_int (CT + 0x114)) by pcw.
    iEval (rewrite Pe14) in "Hpc".
    (* +0x114  c.ldsp s1,24(sp) *)
    iApply (wp_cldsp_s_sconf (mword_of_int (CT + 0x114)) (mword_of_int 3 : mword 6) Rs1
              E2 (K - 6)%nat (m0 !!! Regidx Rs1) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc [] [K3]").
    { iApply (cnti_114 with "Ht"). }
    { iEval (rewrite HE2sp Hb3). iExact "K3". }
    iIntros (CIDe2 Hse2) "Hcg Hpc K3". iEval (rewrite HE2sp Hb3) in "K3".
    set (E3 := <[Regidx Rs1 := regval_into_reg (m0 !!! Regidx Rs1)]> E2).
    assert (HE3sp : E3 !!! Regidx csp_rs1 = pa_stk sp0 6%nat)
      by (rewrite /E3 upd_ne; [exact HE2sp | reg_neq]).
    assert (Pe16 : add_vec_int (mword_of_int (CT + 0x114) : mword 64) 2
                  = mword_of_int (CT + 0x116)) by pcw.
    iEval (rewrite Pe16) in "Hpc".
    (* +0x116  c.addi16sp sp,+48 : the pop *)
    assert (Hspv : add_vec (E3 !!! Regidx csp_rs1)
                     (sign_extend' 64 (caddi16sp_imm (mword_of_int 3 : mword 6))) = sp0).
    { rewrite HE3sp. unfold pa_stk, add_vec_int. rewrite add_vec_assoc.
      rewrite (_ : add_vec (mword_of_int (- (8 * Z.of_nat 6%nat)) : mword 64)
                     (sign_extend' 64 (caddi16sp_imm (mword_of_int 3 : mword 6)))
                   = (mword_of_int 0 : mword 64)); [| pcw].
      apply bv_add_0_r. vm_compute. reflexivity. }
    assert (Hpop : E3 !!! Regidx csp_rs1
                   = pa_stk (add_vec (E3 !!! Regidx csp_rs1)
                       (sign_extend' 64 (caddi16sp_imm (mword_of_int 3 : mword 6)))) 6%nat)
      by (rewrite Hspv HE3sp; reflexivity).
    iDestruct (ct_frame_back sp0 m0 with "[K1 K2 K3] Hrest") as "Hframe".
    { rewrite /ct_saved. iFrame "K1 K2 K3". }
    iEval (rewrite -Hspv) in "Hframe".
    iApply (wp_caddi16sp_pop_s_sconf (mword_of_int (CT + 0x116)) (mword_of_int 3 : mword 6)
              E3 (K - 6)%nat 6%nat b Hpop with "Hcg Hpc [] Hframe").
    { iApply (cnti_116 with "Ht"). }
    iIntros (CIDp Hsp') "Hcg Hpc".
    assert (Havx : (K - 6 + 6)%nat = K) by (lia).
    iEval (rewrite Havx) in "Hcg".
    set (E4 := <[Regidx csp_rs1 := regval_into_reg
        (add_vec (E3 !!! Regidx csp_rs1)
           (sign_extend' 64 (caddi16sp_imm (mword_of_int 3 : mword 6))))]> E3).
    assert (Pe18 : add_vec_int (mword_of_int (CT + 0x116) : mword 64) 2
                  = mword_of_int (CT + 0x118)) by pcw.
    iEval (rewrite Pe18) in "Hpc".
    (* +0x118  c.ret *)
    assert (HE4ra : E4 !!! Regidx Rra = m0 !!! Regidx Rra).
    { rewrite /E4 upd_ne; [| reg_neq]. rewrite /E3 upd_ne; [| reg_neq].
      rewrite /E2 upd_ne; [| reg_neq]. rewrite /E1 upd_eq. reflexivity. }
    iApply (wp_cret_s_sconf (mword_of_int (CT + 0x118)) Rra E4 K b
              ltac:(nz) with "Hcg Hpc []").
    { iApply (cnti_118 with "Ht"). }
    iIntros (CIDr Hsr) "Hcg Hpc".
    iEval (rewrite rget_ne; [| reg_neq]) in "Hpc".
    iEval (rewrite HE4ra) in "Hpc".
    assert (Hcs : callee_saved m0 E4).
    { destruct HMcs as (Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11).
      assert (Hthr : forall r : mword 5, r <> csp_rs1 -> r <> Rra -> r <> Rs0 -> r <> Rs1 ->
                E4 !!! Regidx r = M !!! Regidx r).
      { intros r N2 N1 N8 N9.
        rewrite /E4 upd_ne; [| congruence]. rewrite /E3 upd_ne; [| congruence].
        rewrite /E2 upd_ne; [| congruence]. rewrite /E1 upd_ne; [| congruence].
        reflexivity. }
      unfold callee_saved. split_and!.
      - rewrite /E4 upd_eq. unfold regval_into_reg. rewrite Hspv. symmetry. exact Hm0sp.
      - rewrite /E4 upd_ne; [| reg_neq]. rewrite /E3 upd_ne; [| reg_neq].
        rewrite /E2 upd_eq. reflexivity.
      - rewrite /E4 upd_ne; [| reg_neq]. rewrite /E3 upd_eq. reflexivity.
      - rewrite (Hthr Rs2 ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)). exact Q2.
      - rewrite (Hthr Rs3 ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)). exact Q3.
      - rewrite (Hthr Rs4 ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)). exact Q4.
      - rewrite (Hthr Rs5 ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)). exact Q5.
      - rewrite (Hthr Rs6 ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)). exact Q6.
      - rewrite (Hthr Rs7 ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)). exact Q7.
      - rewrite (Hthr Rs8 ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)). exact Q8.
      - rewrite (Hthr Rs9 ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)). exact Q9.
      - rewrite (Hthr Rs10 ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)). exact Q10.
      - rewrite (Hthr Rs11 ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)). exact Q11. }
    iDestruct (cpu_own_transport CID CIDr lvl eb pme b ltac:(wp_next_chain)
                 with "Hcnt") as "Hcnt".
    rewrite /ct_ret.
    iSpecialize ("Hcont" $! CIDr with "[%]"); [wp_next_chain|].
    iApply ("Hcont" $! E4 with "[%] Hcg Hcnt Ht Hpc Hhiout Hlgh Hwin").
    split; [exact Hcs | intro r; apply rf_to_gmap_dom].
  Qed.

End CtBodies.

(* ===================================================================== *)
Module ConsoleintrProof (Acquire : ACQUIRE) (Consputc : CONSPUTC)
                        (Release : RELEASE) (Wakeup : WAKEUP)
                        : CONSOLEINTR.

Section ProofConsoleintr.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ, !wchG Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.

  Local Ltac rgall := repeat (rewrite rget_ne; [| vm_compute; discriminate]).
  Local Typeclasses Opaque cpu_own.

  (* =================================================================== *)
  (*  THE ECHO'S JUSTIFICATION, SPECIALISED TO THIS CALL'S BYTE           *)
  (*  (lane OUT-FUPD, F3).                                                *)
  (*                                                                      *)
  (*  Every store this function makes to the CONSOLE UART goes through     *)
  (*  consputc, whose contract now asks its caller for a CHAIN of view      *)
  (*  shifts over the bytes it will push.  consoleintr runs on the         *)
  (*  interrupt path and has nothing of its own to pay with: the echo is    *)
  (*  the APPLICATION's claim about its own input, and the application      *)
  (*  minted the justification into the console environment at boot         *)
  (*  ([SpecConsoleintr.cons_echo_shift], carried by [console_caps]).       *)
  (*                                                                      *)
  (*  [ct_pay cb] is that shift with the three facts this call holds        *)
  (*  already discharged -- the byte's arrival history, its tag, and the    *)
  (*  monotone bound on it -- so the arms below carry ONE persistent        *)
  (*  proposition where they used to carry a trace baseline.                *)
  (* =================================================================== *)
  Definition ct_pay (γu : uart_names) (hb : list mobs) (cb : bv 8) : iProp Σ :=
    ((* ...AND THE BYTE'S TWO ERA FACTS (relax-d2, lane K1): the machine was
        ON at its arrival, and the arrival belongs to THIS era.  They ride
        here rather than in every arm's premise list because that is what
        [ct_pay] is for -- one persistent bundle the arms already carry --
        and K1's transport of uartinit's flush witness needs both. *)
     ⌜trace_shape hb true⌝ ∗ ⌜obs_boots hb = S gen_id⌝ ∗
     (* the byte's WIRE RIDER, relayed from the receive column (lane
        CONS-IO): the echo's link asks for it at every store, and it is
        persistent, so it travels with the builder. *)
     uart_out_lb γu (obs_wire Uart0 (open_seg hb)) ∗
     (* ...AND THE BUILDER, which takes NOTHING LINEAR (redesign R2): it
        hands back the OPEN event's link, and the arm's exclusion is the
        kernel's own half of [uart_arm], spent at the open and returned at
        the close.  Every arm applies it exactly once, on every path. *)
     □ ∀ (cs : list (bv 8)) (Φ : iProp Σ),
        ⌜ cons_echo cb cs ⌝ -∗ Φ -∗
        cons_link Uart0 (S gen_id) (ConsLog.EvOpen hb cb cs)
                  (cons_run (S gen_id) cs Φ))%I.

  Global Instance ct_pay_persistent γu hb cb : Persistent (ct_pay γu hb cb).
  Proof using . rewrite /ct_pay. apply _. Qed.

  (* the two era facts, read back off the bundle *)
  Lemma ct_pay_facts (γu : uart_names) (hb : list mobs) (cb : bv 8) :
    ct_pay γu hb cb -∗
    ⌜trace_shape hb true /\ obs_boots hb = S gen_id⌝.
  Proof using . iIntros "(%A & %B & _ & _)". by iPureIntro. Qed.

  (* ...AND THE ERA STAMP IS SPENT HERE, ONCE (lane CONS-IO milestone C).
     [cons_echo_shift] is era-indexed and asks for [obs_boots hb = S gen_id];
     the contract carries that fact as a pure premise (relayed from the
     receive column through uartgetc and uartintr), so the builder is
     specialised at the mint and NO ARM has to carry the stamp. *)
  Lemma ct_mk_pay (γu : uart_names) (hb : list mobs) (cb : bv 8) :
    obs_ends_in Uart0 hb cb ->
    obs_boots hb = S gen_id ->
    trace_shape hb true ->
    cons_echo_shift -∗ riscv_rx_tag hb -∗ obs_hist_lb hb -∗
    uart_out_lb γu (obs_wire Uart0 (open_seg hb)) -∗ ct_pay γu hb cb.
  Proof using .
    intros Hends Hbts Hshb. iIntros "#Hsh #Htg #Hlb #Hwlb".
    iSplitR; [by iPureIntro |]. iSplitR; [by iPureIntro |].
    iSplitR; [iExact "Hwlb" |].
    iIntros "!>" (cs Φ) "%Hcs HΦ".
    iApply ("Hsh" $! hb cb cs Φ with "[%] [%] [%] Htg Hlb HΦ");
      [exact Hends | exact Hbts | exact Hcs].
  Qed.

  (* =================================================================== *)
  (*  THE LOG'S MARK, AND WHAT EVERY ARM OWES (lane CONS-IO).             *)
  (*                                                                      *)
  (*  The shift is CHAIN-FIRST and APPEND-LAST: an arm spends its echoed   *)
  (*  bytes one link at a time and closes the log entry at exactly what    *)
  (*  went out.  So the arms carry TWO things -- the log's high-water half *)
  (*  with the fact that licenses this call's append ([ct_mark]), and,     *)
  (*  once the bytes are gone, the append itself ([ct_owed]) -- and EXIT    *)
  (*  fires it, once, for every arm.                                       *)
  (* =================================================================== *)
  (* ...AND THE ARM'S OWN HALF RIDES THE SAME BUNDLE (redesign R2), at
     [None]: no arm is open.  It is what the window token used to stand for
     -- the era's one loan -- except that it says WHICH arm is open rather
     than merely that one may be, so a second open is refuted by the ghost
     rather than by a counting argument.  Putting it here rather than in
     every arm's premise list keeps the arms' statements unchanged. *)
  (* ...AND K1's ONE FACT (relax-d2): this byte is the input right after
     the one the mark names.  It rides the mark because it is a statement
     about the mark, and every arm spends it at its own open and close. *)
  Definition ct_mark (γu : uart_names) (hb : list mobs) : iProp Σ :=
    (∃ hg : option (list mobs),
       ⌜ ohist_ext hg hb ⌝ ∗ ⌜ k1_next hg hb ⌝ ∗
       uart_log_hi γu (1/2) hg ∗
       uart_arm γu (1/2) None)%I.

  (* [es] is what WENT OUT and [cs] is what the arm PLANNED; the two differ
     only for an arm that stops short (the kill loop). *)
  Definition ct_owed (γu : uart_names) (hb : list mobs) (cb : bv 8) : iProp Σ :=
    (∃ (es cs : list (bv 8)) (j : nat) (hg : option (list mobs)),
       ⌜ cons_echo cb es ⌝ ∗ ⌜ take j cs = es ⌝ ∗ ⌜ ohist_ext hg hb ⌝ ∗
       (* ---- K3 (relax-d2): what the arm PLANNED is never the store arm's
          one glyph -- the two arms that own this bundle plan [[]] and a run
          of erase triples ---- *)
       ⌜ cs = [ConsLog.echo_of cb] -> j = 1%nat ⌝ ∗
       (* ---- K1 (relax-d2): which keystroke this arm is filing ---- *)
       ⌜ k1_next hg hb ⌝ ∗
       uart_log_hi γu (1/2) hg ∗ ct_append γu hb cb cs j True)%I.

  (* the arms that echo NOTHING -- a NUL byte, a full ring, an erase that
     found nothing to erase -- and this is the whole of what CONS-IO adds
     to them: a dropped byte is an ACCEPTED byte, logged at [cs = []]. *)
  (* the currency an arm that echoes NOTHING spends: a dropped byte is an
     ACCEPTED byte, logged at [cs = []] (lane CONS-IO). *)
  (* ...AND IT IS THE ONE ARM THAT PAYS K2 (relax-d2): what it files is
     [cs = []], so the boundary asks WHY, and the answer travels in as
     [WpUart.cons_drop_pay] and back out unchanged -- the full-ring caller
     lends the ring's two ghost halves and re-seals with them. *)
  Lemma ct_append_nil (γu : uart_names) (hb : list mobs) (cb : bv 8)
      (hg : option (list mobs)) (Q : iProp Σ) :
    ohist_ext hg hb ->
    obs_ends_in Uart0 hb cb ->
    (* K1 (relax-d2) -- the era facts come off [ct_pay] *)
    k1_next hg hb ->
    uart_inv Uart0 γu -∗ ct_pay γu hb cb -∗
    uart_log_hi γu (1/2) hg -∗ uart_arm γu (1/2) None -∗
    (* ---- K2 ---- *) cons_drop_pay γu cb [] Q
    ={⊤}=∗ uart_log_hi γu (1/2) hg ∗ (* ---- K2 ---- *) Q ∗
           ct_append γu hb cb [] 0%nat True.
  Proof using .
    intros Hx Hends Hk1. iIntros "#Hinv #Hpyc Hlgh Harm Hk2".
    iDestruct (ct_pay_facts with "Hpyc") as %[Hsh Hbh].
    iDestruct "Hpyc" as "(_ & _ & #Hwlb & #Hp)".
    iMod (uart_inv_cons_open γu hb cb [] hg Q
            (cons_run (S gen_id) [] True%I) Hx Hends ltac:(by left)
            Hsh Hbh Hk1
            with "Hinv Hwlb Hlgh Harm Hk2 [] ")
      as "(Hlgh & Harm & HQ & Hrun)".
    { iApply ("Hp" $! [] True%I with "[%] [//]"). by left. }
    iModIntro. iFrame "Hlgh HQ". rewrite /ct_append.
    iSplitR; [by iPureIntro |]. iSplitR; [by iPureIntro |]. iFrame "Harm".
    by cbn [cons_run].
  Qed.

  (* ...AND HOW AN OWED ENTRY IS PAID (lane CONS-IO, milestone B, ruling
     F2).  [ct_owed] survives milestone A unchanged as the ARM'S bundle --
     the echo spent, the mark lent, the append in hand -- but it is spent
     at the arm's own ring, not at EXIT: the erase arms owe their character
     to the ring ([pe = Some]) from before their first pop, and this is
     where that promise is discharged. *)
  Lemma ct_gh_pay_owed (cn : cons_names) (γu : uart_names)
      (rr ww ee : mword 32) (bs : list (bv 8))
      (ts : list (option (list mobs))) (hb : list mobs) (cb : bv 8) :
    cn_uart cn = γu ->
    obs_ends_in Uart0 hb cb ->
    uart_inv Uart0 γu -∗ ct_owed γu hb cb -∗
    ct_gh cn (Some (hb, cb)) rr ww ee bs ts
      ={⊤}=∗ uart_log_hi γu (1/2) (Some hb) ∗ uart_arm γu (1/2) None ∗
             ct_gh cn None rr ww ee bs ts.
  Proof using .
    intros <- Hends. iIntros "#Hinv Howed Hgh".
    iDestruct "Howed" as (es cs j hg)
      "(%Hecho & %Hes & %Hxg & %Hk3 & %Hk1 & Hlgh & Hap)".
    iMod (ct_gh_pay cn (cn_uart cn) rr ww ee bs ts hb cb es cs j hg True%I
            eq_refl Hends Hxg Hecho Hes Hk3 Hk1
            with "Hinv Hlgh Hap Hgh") as "(Hlgh & Harm & _ & Hgh)".
    iModIntro. iFrame "Hlgh Harm Hgh".
  Qed.

  Lemma ct_owed_nil (γu : uart_names) (hb : list mobs) (cb : bv 8) :
    obs_ends_in Uart0 hb cb ->
    (* ---- K2 (relax-d2): this arm files a DROP, so it owes the reason ---- *)
    (bv_unsigned cb = 0%Z \/ bv_unsigned cb = 16%Z
     \/ ConsLog.cons_erase cb = true) ->
    uart_inv Uart0 γu -∗ ct_pay γu hb cb -∗ ct_mark γu hb
    ={⊤}=∗ ct_owed γu hb cb.
  Proof using .
    intros Hends Hk2. iIntros "#Hinv #Hpy Hm".
    iDestruct "Hm" as (hg) "(%Hx & %Hk1 & Hlgh & Harm)".
    iMod (ct_append_nil γu hb cb hg emp%I Hx Hends Hk1
            with "Hinv Hpy Hlgh Harm []") as "(Hlgh & _ & Hap)".
    { iLeft. iSplitR; [by iPureIntro | done]. }
    iModIntro. iExists [], [], 0%nat, hg.
    iSplit; [iPureIntro; by left |].
    iSplit; [by iPureIntro |].
    iSplit; [iPureIntro; exact Hx |].
    iSplit; [iPureIntro; intro Hc; discriminate |].
    iSplit; [iPureIntro; exact Hk1 |].
    iFrame "Hlgh Hap".
  Qed.

  (* WHAT AN ARM HANDS consputc, for a run it will spend WHOLE (the two
     echo arms, and the one-glyph erase): the store chain the contract asks
     for, with the log's mark lent and given back beside the append. *)
  (* ...AND IT IS A FUPD NOW (redesign R2): the arm is OPENED here, with
     the port invariant opened around [EvOpen], where it used to be a
     purely local handoff of a token. *)
  (* ...AND IT TAKES K1 AND [cs <> []] (relax-d2).  The second is what
     discharges K2 here: an arm that echoes something is not a drop, so the
     drop clause is vacuous and this lane owes lane K2 nothing on the two
     echoing arms. *)
  Lemma ct_ch_full (γu : uart_names) (hb : list mobs) (cb : bv 8)
      (hg : option (list mobs)) (cs : list (bv 8)) (Φ : iProp Σ) :
    ohist_ext hg hb ->
    obs_ends_in Uart0 hb cb ->
    ConsLog.cons_echo cb cs ->
    (* ---- K1 (relax-d2) ---- *)
    k1_next hg hb ->
    (* ---- K2 (relax-d2): every caller of this one plans a NON-EMPTY run,
       so the premise is discharged by [discriminate]; it is here rather
       than as a [cs <> []] side condition because that is the shape
       [WpUart.cons_drop_pay] takes. ---- *)
    (cs = [] -> bv_unsigned cb = 0%Z \/ bv_unsigned cb = 16%Z
                \/ ConsLog.cons_erase cb = true) ->
    uart_inv Uart0 γu -∗ ct_pay γu hb cb -∗
    uart_log_hi γu (1/2) hg -∗ uart_arm γu (1/2) None -∗ Φ
    ={⊤}=∗ store_chain Uart0 γu cs
      (uart_log_hi γu (1/2) hg ∗ ct_append γu hb cb cs (length cs) Φ).
  Proof using .
    intros Hx Hends Hecho Hk1 Hk2. iIntros "#Hinv #Hpyc Hlgh Harm HΦ".
    iDestruct (ct_pay_facts with "Hpyc") as %[Hsh Hbh].
    iDestruct "Hpyc" as "(_ & _ & #Hwlb & #Hp)".
    iMod (uart_inv_cons_open γu hb cb cs hg emp%I
            (cons_run (S gen_id) cs Φ) Hx Hends Hecho Hsh Hbh Hk1
            with "Hinv Hwlb Hlgh Harm [] [HΦ]")
      as "(Hlgh & Harm & _ & Hrun)".
    { (* K2 *) iLeft. iSplitR; [by iPureIntro | done]. }
    { iApply ("Hp" $! cs Φ with "[%] HΦ"). exact Hecho. }
    iDestruct (cons_run_full cs Φ with "Hrun") as "Hch".
    iDestruct (store_chain_of_echo_chain γu hb cb cs 0%nat cs
                 (cons_link Uart0 (S gen_id) ConsLog.EvClose Φ)
                 ltac:(intros n b Hn; exact Hn) with "Harm Hch") as "H".
    iModIntro. iApply (store_chain_mono with "[Hlgh] H").
    iIntros "[Harm Hcl]". iFrame "Hlgh". rewrite /ct_append.
    iSplitR; [by iPureIntro |]. iSplitR; [by iPureIntro |]. iFrame "Hcl".
    by rewrite Nat.add_0_l.
  Qed.

  (* ...and for ONE TRIPLE off a run that may go on (the kill-line loop) *)
  (* THE ARM'S POSITION IS THE ONLY PREMISE (redesign R2): the byte links
     are discharged off [uart_arm] against the plan, so neither the wire
     rider nor the log's mark is needed here -- the mark merely rides. *)
  Lemma ct_ch_bs (γu : uart_names) (hb : list mobs) (cb : bv 8)
      (hg : option (list mobs)) (pre bs : list (bv 8)) (Φ : iProp Σ) :
    uart_log_hi γu (1/2) hg -∗
    uart_arm γu (1/2)
      (Some (hb, cb, (pre ++ consputc_bs ++ bs)%list, length pre)) -∗
    cons_run (S gen_id) ((consputc_bs ++ bs)%list) Φ -∗
    store_chain Uart0 γu consputc_bs
      (uart_log_hi γu (1/2) hg ∗
       uart_arm γu (1/2) (Some (hb, cb, (pre ++ consputc_bs ++ bs)%list,
                                (length pre + length consputc_bs)%nat)) ∗
       cons_run (S gen_id) bs Φ).
  Proof using .
    iIntros "Hlgh Harm Hrun".
    iDestruct (cons_run_step consputc_bs bs Φ with "Hrun") as "Hch".
    iDestruct (store_chain_of_echo_split γu hb cb pre consputc_bs bs
                 (cons_run (S gen_id) bs Φ) with "Harm Hch") as "H".
    iApply (store_chain_mono with "[Hlgh] H"). iIntros "[Harm Hrun]".
    iFrame "Hlgh Harm Hrun".
  Qed.

  (* the ERASE arms' currency: the builder, with the switch's own guard.
     [cons_echo]'s erase disjunct is GUARDED by [cons_erase], and the guard
     is a fact only the [beq] chain has -- so it travels with the payment. *)
  Definition ct_pay_erase (γu : uart_names) (hb : list mobs) (cb : bv 8)
      : iProp Σ := (⌜ cons_erase cb = true ⌝ ∗ ct_pay γu hb cb)%I.

  Global Instance ct_pay_erase_persistent γu hb cb :
    Persistent (ct_pay_erase γu hb cb).
  Proof using . rewrite /ct_pay_erase. apply _. Qed.

  Lemma ct_mk_pay_erase (γu : uart_names) (hb : list mobs) (cb : bv 8) :
    cons_erase cb = true -> ct_pay γu hb cb -∗ ct_pay_erase γu hb cb.
  Proof using . intros Her. iIntros "#Hp". by iFrame "Hp". Qed.

  (* the two shapes of a run over erase triples *)
  Lemma ct_bs_cons (n : nat) :
    mjoin (replicate (S n) consputc_bs)
    = (consputc_bs ++ mjoin (replicate n consputc_bs))%list.
  Proof using . reflexivity. Qed.

  Lemma ct_bs_snoc (i : nat) :
    ((mjoin (replicate i consputc_bs)) ++ consputc_bs)%list
    = mjoin (replicate (S i) consputc_bs).
  Proof using .
    induction i as [| i IH]; [by rewrite /= ?app_nil_r |].
    rewrite (ct_bs_cons i) -app_assoc IH (ct_bs_cons (S i)). reflexivity.
  Qed.

  (* =================================================================== *)
  (*  THE KILL LOOP'S ACCUMULATOR (lane CONS-IO).                          *)
  (*                                                                      *)
  (*  The glyph count is the RING'S CONTENT and the shift fires before the *)
  (*  loop runs, so what the loop carries is a run at an UPPER BOUND [n]   *)
  (*  -- the editable window's length at entry -- with [i] triples already *)
  (*  emitted.  Every iteration spends one and decreases [n]; either exit  *)
  (*  stops the run at [i] and logs exactly that.                          *)
  (* =================================================================== *)
  (* THE PLAN IS SPLIT AT THE ARM'S POSITION: [i] triples already emitted,
     [n] still allowed.  The arm's index is the length of the emitted part,
     which is what [store_chain_of_echo_split] reads. *)
  Definition ct_kill_run (γu : uart_names) (hb : list mobs) (cb : bv 8)
      (nrem : Z) : iProp Σ :=
    (∃ (hg : option (list mobs)) (i n : nat),
       ⌜ ohist_ext hg hb ⌝ ∗ ⌜ k1_next hg hb ⌝ ∗
       (* the byte's two era facts, as [ct_append] will want them *)
       ⌜ trace_shape hb true ⌝ ∗ ⌜ obs_boots hb = S gen_id ⌝ ∗
       ⌜ (nrem <= Z.of_nat n)%Z ⌝ ∗
       uart_log_hi γu (1/2) hg ∗
       uart_arm γu (1/2)
         (Some (hb, cb, (mjoin (replicate i consputc_bs)
                         ++ mjoin (replicate n consputc_bs))%list,
                length (mjoin (replicate i consputc_bs)))) ∗
       cons_run (S gen_id) (mjoin (replicate n consputc_bs)) True)%I.

  Lemma ct_mk_kill_run (γu : uart_names) (hb : list mobs) (cb : bv 8)
      (nrem : Z) :
    (0 <= nrem)%Z ->
    obs_ends_in Uart0 hb cb ->
    uart_inv Uart0 γu -∗
    ct_pay_erase γu hb cb -∗ ct_mark γu hb ={⊤}=∗ ct_kill_run γu hb cb nrem.
  Proof using .
    intros Hn Hends. iIntros "#Hinv [%Her #Hpy] Hm".
    iDestruct (ct_pay_facts with "Hpy") as %[Hsh Hbh].
    iDestruct "Hm" as (hg) "(%Hx & %Hk1 & Hlgh & Harm)".
    iDestruct "Hpy" as "(_ & _ & #Hwlb & #Hp)".
    set (cs := mjoin (replicate (Z.to_nat nrem) consputc_bs)).
    assert (Hecho : ConsLog.cons_echo cb cs).
    { right; right. split; [exact Her |]. by eexists. }
    iMod (uart_inv_cons_open γu hb cb cs hg emp%I
            (cons_run (S gen_id) cs True%I) Hx Hends Hecho Hsh Hbh Hk1
            with "Hinv Hwlb Hlgh Harm [] []")
      as "(Hlgh & Harm & _ & Hrun)".
    { (* K2: an erase byte is its own reason to drop *)
      iLeft. iSplitR; [| done]. iPureIntro. intros _. right; right. exact Her. }
    { iApply ("Hp" $! cs True%I with "[%] [//]"). exact Hecho. }
    iModIntro. iExists hg, 0%nat, (Z.to_nat nrem).
    iSplit; [iPureIntro; exact Hx |].
    iSplit; [iPureIntro; exact Hk1 |].
    iSplit; [iPureIntro; exact Hsh |].
    iSplit; [iPureIntro; exact Hbh |].
    iSplit; [iPureIntro; lia |].
    iFrame "Hlgh Hrun".
    by cbn [replicate mjoin length].
  Qed.

  Lemma ct_kill_owed (γu : uart_names) (hb : list mobs) (cb : bv 8)
      (nrem : Z) :
    cons_erase cb = true ->
    ct_kill_run γu hb cb nrem -∗ ct_owed γu hb cb.
  Proof using .
    intros Her. iIntros "H".
    iDestruct "H" as (hg i n)
      "(%Hx & %Hk1 & %Hsh & %Hbh & %Hle & Hlgh & Harm & Hrun)".
    iDestruct (cons_run_stop with "Hrun") as "Hcl".
    iExists (mjoin (replicate i consputc_bs)),
            ((mjoin (replicate i consputc_bs)
              ++ mjoin (replicate n consputc_bs))%list),
            (length (mjoin (replicate i consputc_bs))), hg.
    iSplit; [iPureIntro; right; right; split; [exact Her | by exists i] |].
    iSplit; [iPureIntro; by rewrite take_app_length |].
    iSplit; [iPureIntro; exact Hx |].
    iSplit; [iPureIntro;
             exact (fun Hc => False_ind _
                      (ConsLog.cons_bs_join_app_not_single i n
                         (ConsLog.echo_of cb) Hc)) |].
    iSplit; [iPureIntro; exact Hk1 |].
    rewrite /ct_append. iFrame "Hlgh Harm Hcl".
    iSplitR; [by iPureIntro | by iPureIntro].
  Qed.

  (* =================================================================== *)
  (*  [EXIT] (+0x104): release cons.lock, then the epilogue.              *)
  (*  NINE jumps reach it -- every arm of the switch ends here -- so it   *)
  (*  is a continuation and the epilogue is written once.                 *)
  (* =================================================================== *)
  Definition ct_exit_prop `{CID0 : CpuId}
      (γu : uart_names) (hb : list mobs) (cb : bv 8) (cn : cons_names)
      (γc : gname) (pme : mword 64) (m0 : regfile) (K lvl : nat) (eb : bool)
      (b : bool) (sp0 : mword 64) (lks : gset string) : iProp Σ :=
    (wp_next (CID0 := CID0) b pme (fun (CIDx : CpuId) =>
       ∀ M : regfile,
         ⌜ M !!! Regidx csp_rs1 = pa_stk sp0 6%nat ⌝ -∗
         ⌜ ct_cs_hi M m0 ⌝ -∗
         sie_cap_gpr KT1 M (trap_res b + (K - 6))%nat false pme -∗
         pc_is (mword_of_int (CT + 0x104)) -∗
         cpu_own (S lvl) eb pme false ({["cons"]} ∪ lks) -∗
         arm_pay KT1 lvl eb pme -∗
         locked γc cpu_id -∗
         cons_res cn -∗
         ct_rest sp0 -∗
         ct_hi_out γu hb cb -∗
         (* ...AND THE LOG'S MARK AT THIS BYTE (lane CONS-IO, milestone B,
            ruling F2).  Milestone A owed the append to EXIT and fired it
            once, here; that is no longer possible, because the ring's own
            account of the log has to hold at every point the ring is
            SEALED -- and the arms seal it themselves.  So each arm files
            its entry where its ring transition is (the store's in the same
            ghost step as the push, the erase's when its glyphs have gone
            out, the drops' outright), and what reaches EXIT is the mark
            the append moved. *)
         uart_log_hi γu (1/2) (Some hb) -∗
         (* ...AND THE ARM'S HALF, AT [None] (redesign R2): no arm is open,
            which is what the window token used to stand for.  It is spent
            at the open and repaid by the arm's own close, so it leaves
            with the mark. *)
         uart_arm γu (1/2) None -∗
         mWP (Loop : expr riscv_lang)))%I.

  Lemma ct_mk_exit (γu : uart_names) (hb : list mobs) (cb : bv 8) (cn : cons_names)
      (γc : gname) (pme : mword 64) (m0 : regfile) (K lvl : nat)
      (eb : bool) (b : bool) (sp0 : mword 64) (lks : gset string) :
    (* the byte's own arrival, which the append's entry names *)
    obs_ends_in Uart0 hb cb ->
    m0 !!! Regidx csp_rs1 = sp0 ->
    (consoleintr_stack <= K)%nat ->
    match lvl with O => eb | S _ => false end = b ->
    (* release's set arithmetic: the entry [cpu_own] holds
       [{["cons"]} ∪ lks], and release needs [lock_rank "cons"] to
       drop back OUT of it cleanly, i.e. ["cons" ∉ lks]. *)
    locks_below lks "cons" ->
    kernel_text -∗
    is_lock γc a_cons "cons"%string (cons_res_at cn) -∗ ct_saved sp0 m0 -∗
    ct_ret (CID0 := CID) γu hb cb pme m0 K lvl eb b lks -∗
    ct_exit_prop (CID0 := CID) γu hb cb cn γc pme m0 K lvl eb b sp0 lks.
  Proof using .
    intros Hends Hm0sp HK Hb Hbelow. subst b.
    pose proof (locks_below_not_elem _ _ Hbelow) as Hfresh.
    iIntros "#Ht #Hlk Hsaved Hcont".
    rewrite /ct_exit_prop.
    iIntros (CIDx Hsx M)
      "%Hsp %Hcs Hcg Hpc Hcnt Hpay Hlocked Hres Hrest Hhiout Hlgh Hwin".
    (* THE APPEND IS ALREADY FIRED (lane CONS-IO, milestone B, ruling F2):
       every arm files its entry where its own ring transition is, because
       the ring's account of the log has to hold wherever the ring is
       SEALED -- and the arms seal it.  What reaches here is the mark. *)
    (* +0x104 auipc a0,0x12 ; +0x108 addi a0,a0,-272 : a0 := &cons *)
    iApply (wp_auipc_s_sconf (mword_of_int (CT + 0x104)) Ra0 (mword_of_int 18 : mword 20)
              M (trap_res (match lvl with O => eb | S _ => false end) + (K - 6))%nat false ltac:(nz) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (cnti_104 with "Ht"). }
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    set (X1 := <[Regidx Ra0 := regval_into_reg
        (add_vec (mword_of_int (CT + 0x104) : mword 64)
           (auipc_off (mword_of_int 18 : mword 20)))]> M).
    assert (Hp108 : add_vec_int (mword_of_int (CT + 0x104) : mword 64) 4
                    = mword_of_int (CT + 0x108)) by pcw.
    iEval (rewrite Hp108) in "Hpc".
    iApply (wp_addi4_s_sconf (mword_of_int (CT + 0x108)) Ra0 Ra0 (mword_of_int 4020 : mword 12)
              X1 (trap_res (match lvl with O => eb | S _ => false end) + (K - 6))%nat false ltac:(nz) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (cnti_108 with "Ht"). }
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    set (X2 := <[Regidx Ra0 := regval_into_reg
        (add_vec (X1 !!! Regidx Ra0) (sign_extend' 64 (mword_of_int 4020 : mword 12)))]> X1).
    assert (HX2a0 : X2 !!! Regidx Ra0 = a_cons).
    { rewrite /X2 upd_eq /X1 upd_eq /a_cons. apply bv_eq; vm_compute; reflexivity. }
    assert (Hp10c : add_vec_int (mword_of_int (CT + 0x108) : mword 64) 4
                    = mword_of_int (CT + 0x10c)) by pcw.
    iEval (rewrite Hp10c) in "Hpc".
    (* +0x10c jal ra,release *)
    iApply (wp_jal_s_sconf (mword_of_int (CT + 0x10c)) Rra (mword_of_int 2316 : mword 21)
              X2 (trap_res (match lvl with O => eb | S _ => false end) + (K - 6))%nat false ltac:(nz) ltac:(rdok)
              ltac:(vm_compute; reflexivity) with "Hcg Hpc []").
    { iApply (cnti_10c with "Ht"). }
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    set (X3 := <[Regidx Rra := regval_into_reg
        (add_vec_int (mword_of_int (CT + 0x10c) : mword 64) 4)]> X2).
    assert (Hjrl : add_vec (mword_of_int (CT + 0x10c) : mword 64)
                     (sign_extend' 64 (mword_of_int 2316 : mword 21))
                   = mword_of_int KernelSyms.release) by pcw.
    iEval (rewrite Hjrl) in "Hpc".
    assert (HX3a0 : X3 !!! Regidx Ra0 = a_cons)
      by (rewrite /X3 upd_ne; [exact HX2a0 | reg_neq]).
    assert (HX3ra : X3 !!! Regidx Rra
                    = add_vec_int (mword_of_int (CT + 0x10c) : mword 64) 4)
      by (rewrite /X3; apply upd_eq).
    assert (HX3lka : add_vec (X3 !!! Regidx Ra0)
                       (sign_extend' 64 (mword_of_int 0 : mword 12)) = a_cons).
    { rewrite HX3a0.
      replace (sign_extend' 64 (mword_of_int 0 : mword 12)) with (mword_of_int 0 : mword 64)
        by pcw.
      apply kv_addv_zero. }
    assert (HthrX : forall r : mword 5, is_cs_idx r = true -> X3 !!! Regidx r = M !!! Regidx r).
    { intros r Hr.
      assert (N1 : r <> Rra) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      assert (N10 : r <> Ra0) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      rewrite /X3 upd_ne; [| congruence]. rewrite /X2 upd_ne; [| congruence].
      rewrite /X1 upd_ne; [| congruence]. reflexivity. }
    iApply (Release.wp_release_sconf KT1 γc a_cons "cons"%string (cons_res_at cn) X3
              lvl eb pme (K - 6)%nat ({["cons"]} ∪ lks) HX3lka
              ltac:(lia)
              with "Hcg Ht Hpc Hlk Hlocked Hres Hcnt Hpay").
    iIntros (CIDr Hsr mr) "Hcg Hpc %Hcsr Hcnt". rgall.
    assert (Hsetback : ({["cons"]} ∪ lks) ∖ {["cons"]} = lks)
      by (apply locks_add_del_below; lkbelow).
    iEval (rewrite Hsetback) in "Hcnt".
    iEval (rewrite HX3ra) in "Hpc".
    assert (Hp110 : ret_pc (add_vec_int (mword_of_int (CT + 0x10c) : mword 64) 4)
                    = (mword_of_int (CT + 0x110) : mword 64)) by pcw.
    iEval (rewrite Hp110) in "Hpc".
    assert (Hthr : forall r : mword 5, is_cs_idx r = true -> mr !!! Regidx r = M !!! Regidx r).
    { intros r Hr. rewrite (callee_saved_lookup Hcsr r Hr). apply HthrX; exact Hr. }
    iApply (ct_epi (CID := CIDr) CIDr γu hb cb pme m0 mr K lvl eb sp0 _ lks Hm0sp
              ltac:(rewrite (Hthr csp_rs1 ltac:(vm_compute; reflexivity)); exact Hsp)
              ltac:(exact (ct_cs_hi_thr mr M m0 Hthr Hcs))
              HK ltac:(intros _; reflexivity)
              with "Ht Hcg Hcnt Hpc Hsaved Hrest Hhiout Hlgh Hwin").
    iApply (wp_next_retarget CID CIDr _ pme _ ltac:(wp_next_chain) with "Hcont").
  Qed.

  (* =================================================================== *)
  (*  [WAKE] (+0x156): publish the edit index and wake a blocked reader.  *)
  (*  Four entries reach it -- '\n' and C('D') from the echo path, the    *)
  (*  ring-full test, and the '\r' arm's fall-through -- and every one of *)
  (*  them has already put the new [cons.e] in a2, which is the only      *)
  (*  register this block reads.                                          *)
  (* =================================================================== *)
  Definition ct_wake_prop `{CID0 : CpuId}
      (γu : uart_names) (hb : list mobs) (cb : bv 8) (cn : cons_names)
      (γc : gname) (pme : mword 64) (m0 : regfile)
      (K lvl : nat) (eb : bool) (b : bool) (sp0 : mword 64) (lks : gset string) : iProp Σ :=
    (wp_next (CID0 := CID0) b pme (fun (CIDw : CpuId) =>
       ∀ (M : regfile) (rr ww ee : mword 32) (bs : list (bv 8))
         (ts : list (option (list mobs))),
         ⌜ M !!! Regidx csp_rs1 = pa_stk sp0 6%nat ⌝ -∗
         (* a2 IS THE RING'S OWN [cons.e], and that is why the ring arrives
            DESTRUCTED here rather than as [cons_res]: this block stores a2
            into [cons.w] and [ConsoleInv.cons_ok] is a relation between the
            two, so under [cons_res]'s existential the equation could not
            even be stated.  All four entries have it -- each has just put
            the new [cons.e] in a2. *)
         ⌜ M !!! Regidx Ra2 = sign_extend' 64 ee ⌝ -∗
         ⌜ ct_cs_hi M m0 ⌝ -∗
         ⌜ length bs = INPUT_BUF_SIZE ⌝ -∗
         ⌜ length ts = INPUT_BUF_SIZE ⌝ -∗
         ⌜ cons_ok rr ww ee ⌝ -∗
         ⌜ cons_row rr ee bs ts ⌝ -∗
         sie_cap_gpr KT1 M (trap_res b + (K - 6))%nat false pme -∗
         pc_is (mword_of_int (CT + 0x156)) -∗
         cpu_own (S lvl) eb pme false ({["cons"]} ∪ lks) -∗
         arm_pay KT1 lvl eb pme -∗
         locked γc cpu_id -∗
         a_cons_r ↦₄ rr -∗ a_cons_w ↦₄ ww -∗ a_cons_e ↦₄ ee -∗
         cons_data bs -∗ cons_tags ts -∗ ct_gh cn None rr ww ee bs ts -∗
         ct_rest sp0 -∗
         ct_hi_out γu hb cb -∗
         uart_log_hi γu (1/2) (Some hb) -∗
         (* ...AND THE ARM'S HALF, AT [None] (redesign R2): no arm is open,
            which is what the window token used to stand for.  It is spent
            at the open and repaid by the arm's own close, so it leaves
            with the mark. *)
         uart_arm γu (1/2) None -∗
         ct_exit_prop (CID0 := CID0) γu hb cb cn γc pme m0 K lvl eb b sp0 lks -∗
         mWP (Loop : expr riscv_lang)))%I.

  Lemma ct_mk_wake (γu : uart_names) (hb : list mobs) (cb : bv 8) (cn : cons_names)
      (γc : gname) (γs : list gname) (pme : mword 64) (m0 : regfile)
      (K lvl : nat) (eb : bool) (b : bool) (sp0 : mword 64) (lks : gset string) :
    (consoleintr_stack <= K)%nat ->
    length γs = NPROC ->
    (Z.of_nat lvl + 2 < 2 ^ 31)%Z ->
    match lvl with O => eb | S _ => false end = b ->
    (* wakeup is called while cons.lock is STILL held, i.e. its held set is
       [{["cons"]} ∪ lks], not bare [lks] -- so this is the same
       "cons" order fact as [ct_mk_exit], lifted (via [locks_below_mono] and
       [locks_below_union_singleton]) to wakeup's own "proc" (11) premise
       below. *)
    locks_below lks "cons" ->
    kernel_text -∗ procs_inv γs -∗
    ct_wake_prop (CID0 := CID) γu hb cb cn γc pme m0 K lvl eb b sp0 lks.
  Proof using .
    intros HK Hlen Hlvl Hb Hbelow. subst b.
    assert (Hbelow_proc : locks_below ({["cons"]} ∪ lks) "proc").
    { apply locks_below_union_singleton; [vm_compute; lia |].
      lkbelow. }
    iIntros "#Ht #Hpinv".
    rewrite /ct_wake_prop.
    iIntros (CIDw Hsw M rr ww ee bs ts)
      "%Hsp %Ha2 %Hcs %Hlenb %Hlent %Hok %Hrow Hcg Hpc Hcnt Hpay Hlocked
       Hrc Hwc Hec Hdat Hts Hgh Hrest Hhiout Howed Hwin EXIT".
    (* +0x156 auipc a5,0x12 *)
    iApply (wp_auipc_s_sconf (mword_of_int (CT + 0x156)) Ra5 (mword_of_int 18 : mword 20)
              M (trap_res (match lvl with O => eb | S _ => false end) + (K - 6))%nat false
              ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (cnti_156 with "Ht"). }
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    set (W1 := <[Regidx Ra5 := regval_into_reg
        (add_vec (mword_of_int (CT + 0x156) : mword 64)
           (auipc_off (mword_of_int 18 : mword 20)))]> M).
    assert (Hp15a : add_vec_int (mword_of_int (CT + 0x156) : mword 64) 4
                    = mword_of_int (CT + 0x15a)) by pcw.
    iEval (rewrite Hp15a) in "Hpc".
    (* +0x15a sw a2,-198(a5) : cons.w := cons.e *)
    assert (HW1wa : add_vec (W1 !!! Regidx Ra5)
                      (sign_extend' 64 (mword_of_int 4094 : mword 12)) = a_cons_w).
    { rewrite /W1 upd_eq /a_cons_w /coff_of /a_cons. apply bv_eq; vm_compute; reflexivity. }
    assert (HW1a2 : W1 !!! Regidx Ra2 = sign_extend' 64 ee)
      by (rewrite /W1 upd_ne; [exact Ha2 | reg_neq]).
    iApply (wp_sw_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (CT + 0x15a)) Ra2 Ra5 (mword_of_int 4094 : mword 12)
              W1 (trap_res (match lvl with O => eb | S _ => false end) + (K - 6))%nat ww false
              with "Hcg Hpc [] [Hwc]").
    { iApply (cnti_15a with "Ht"). }
    { rgall. iEval (rewrite HW1wa). iExact "Hwc". }
    iApply wp_next_off_intro. iIntros "Hcg Hpc Hwc". rgall.
    iEval (rewrite HW1wa HW1a2 trunc32_sext) in "Hwc".
    assert (Hp15e : add_vec_int (mword_of_int (CT + 0x15a) : mword 64) 4
                    = mword_of_int (CT + 0x15e)) by pcw.
    iEval (rewrite Hp15e) in "Hpc".
    (* the store moved [cons.w] up to [cons.e]: the row is untouched (it
       speaks of [r .. e)) and [cons_ok] holds because [w = e]. *)
    iMod (ct_gh_commit cn None rr ww ee bs ts Hok with "Hgh") as "Hgh".
    iAssert (cons_res cn) with "[Hrc Hwc Hec Hdat Hts Hgh]" as "Hres".
    { iApply (ct_gh_res cn rr ee ee bs ts Hlenb Hlent
                (cons_ok_set_w rr ww ee Hok) Hrow
                with "Hrc Hwc Hec Hdat Hts Hgh"). }
    (* +0x15e auipc a0,0x12 ; +0x162 addi a0,a0,-210 : a0 := &cons.r *)
    iApply (wp_auipc_s_sconf (mword_of_int (CT + 0x15e)) Ra0 (mword_of_int 18 : mword 20)
              W1 (trap_res (match lvl with O => eb | S _ => false end) + (K - 6))%nat false
              ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (cnti_15e with "Ht"). }
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    set (W2 := <[Regidx Ra0 := regval_into_reg
        (add_vec (mword_of_int (CT + 0x15e) : mword 64)
           (auipc_off (mword_of_int 18 : mword 20)))]> W1).
    assert (Hp162 : add_vec_int (mword_of_int (CT + 0x15e) : mword 64) 4
                    = mword_of_int (CT + 0x162)) by pcw.
    iEval (rewrite Hp162) in "Hpc".
    iApply (wp_addi4_s_sconf (mword_of_int (CT + 0x162)) Ra0 Ra0 (mword_of_int 4082 : mword 12)
              W2 (trap_res (match lvl with O => eb | S _ => false end) + (K - 6))%nat false
              ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (cnti_162 with "Ht"). }
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    set (W3 := <[Regidx Ra0 := regval_into_reg
        (add_vec (W2 !!! Regidx Ra0) (sign_extend' 64 (mword_of_int 4082 : mword 12)))]> W2).
    assert (Hp166 : add_vec_int (mword_of_int (CT + 0x162) : mword 64) 4
                    = mword_of_int (CT + 0x166)) by pcw.
    iEval (rewrite Hp166) in "Hpc".
    (* +0x166 jal ra,wakeup *)
    iApply (wp_jal_s_sconf (mword_of_int (CT + 0x166)) Rra (mword_of_int 7186 : mword 21)
              W3 (trap_res (match lvl with O => eb | S _ => false end) + (K - 6))%nat false
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity) with "Hcg Hpc []").
    { iApply (cnti_166 with "Ht"). }
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    set (W4 := <[Regidx Rra := regval_into_reg
        (add_vec_int (mword_of_int (CT + 0x166) : mword 64) 4)]> W3).
    assert (Hjwk : add_vec (mword_of_int (CT + 0x166) : mword 64)
                     (sign_extend' 64 (mword_of_int 7186 : mword 21))
                   = mword_of_int KernelSyms.wakeup) by pcw.
    iEval (rewrite Hjwk) in "Hpc".
    assert (HW4ra : W4 !!! Regidx Rra
                    = add_vec_int (mword_of_int (CT + 0x166) : mword 64) 4)
      by (rewrite /W4; apply upd_eq).
    assert (HthrW : forall r : mword 5, is_cs_idx r = true -> W4 !!! Regidx r = M !!! Regidx r).
    { intros r Hr.
      assert (N1 : r <> Rra) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      assert (N10 : r <> Ra0) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      assert (N15 : r <> Ra5) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      rewrite /W4 upd_ne; [| congruence]. rewrite /W3 upd_ne; [| congruence].
      rewrite /W2 upd_ne; [| congruence]. rewrite /W1 upd_ne; [| congruence]. reflexivity. }
    iApply (Wakeup.wp_wakeup_sconf W4 γs pme (S lvl)
              (trap_res (match lvl with O => eb | S _ => false end) + (K - 6))%nat eb false
              ({["cons"]} ∪ lks)
              ltac:(lia)
              ltac:(intro r; apply rf_to_gmap_dom) Hlen ltac:(lia) Hbelow_proc
              with "Hcg Hcnt Ht Hpc Hpinv").
    all: try lkbelow.
    iApply wp_next_off_intro. iIntros (Mw) "[%Hwcs %Hwdom] Hcg Hcnt _ Hpc". rgall.
    iEval (rewrite HW4ra) in "Hpc".
    assert (Hp16a : ret_pc (add_vec_int (mword_of_int (CT + 0x166) : mword 64) 4)
                    = (mword_of_int (CT + 0x16a) : mword 64)) by pcw.
    iEval (rewrite Hp16a) in "Hpc".
    assert (Hthr : forall r : mword 5, is_cs_idx r = true -> Mw !!! Regidx r = M !!! Regidx r).
    { intros r Hr. rewrite (callee_saved_lookup Hwcs r Hr). apply HthrW; exact Hr. }
    (* +0x16a c.j -> the exit at +0x104 *)
    iApply (wp_cj_s_sconf (mword_of_int (CT + 0x16a))
              (sign_extend' 21 (concat_vec (mword_of_int 1997 : mword 11) ('b"0")))
              Mw (trap_res (match lvl with O => eb | S _ => false end) + (K - 6))%nat false
              ltac:(vm_compute; reflexivity) with "Hcg Hpc []").
    { iApply (cnti_16a with "Ht"). }
    iApply wp_next_off_intro. iApply bi.later_intro. iIntros "Hcg Hpc". rgall.
    assert (Hj104 : add_vec (mword_of_int (CT + 0x16a) : mword 64)
                      (sign_extend' 64 (sign_extend' 21
                         (concat_vec (mword_of_int 1997 : mword 11) ('b"0"))))
                    = mword_of_int (CT + 0x104)) by pcw.
    iEval (rewrite Hj104) in "Hpc".
    iSpecialize ("EXIT" $! CIDw with "[%]"); [wp_next_chain|].
    iApply ("EXIT" $! Mw with "[%] [%] Hcg Hpc Hcnt Hpay Hlocked Hres Hrest
              Hhiout Howed Hwin").
    - rewrite (Hthr csp_rs1 ltac:(vm_compute; reflexivity)). exact Hsp.
    - exact (ct_cs_hi_thr Mw M m0 Hthr Hcs).
  Qed.

  (* ---- the three-instruction stub the C('U') arm exits through -------
     [c.ldsp s2,16(sp)], [c.ldsp s3,8(sp)], [c.j -> +0x104].  It occurs at
     +0x0de, +0x0e4 and +0x0ea -- once per way out of the kill-line loop --
     so it is a lemma over its three pcs rather than three copies. *)
  Lemma ct_restore23 `{CIDq : CpuId}
      (γu : uart_names) (hb : list mobs) (cb : bv 8) (cn : cons_names)
      (γc : gname) (pme : mword 64) (m0 M : regfile) (K lvl : nat) (eb : bool)
      (b : bool) (sp0 : mword 64) (pc1 pc2 pc3 : mword 64)
      (jimm : mword 11) (lks : gset string) :
    M !!! Regidx csp_rs1 = pa_stk sp0 6%nat ->
    ct_cs_top M m0 ->
    add_vec_int pc1 2 = pc2 ->
    add_vec_int pc2 2 = pc3 ->
    add_vec pc3 (sign_extend' 64 (sign_extend' 21 (concat_vec jimm ('b"0"))))
      = mword_of_int (CT + 0x104) ->
    eq_vec (access_vec_dec (add_vec pc3
      (sign_extend' 64 (sign_extend' 21 (concat_vec jimm ('b"0"))))) 0) ('b"0") = true ->
    (b = false \/ pme = zero_reg -> (CIDq : CPU) = (CID : CPU)) ->
    (* same "cons" bound as the sibling arms: this one reaches consputc,
       whose cone runs up to "uart0" (17). *)
    locks_below lks "cons" ->
    instr pc1 true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")),
                          sp, Regidx Rs2, false, 8)) -∗
    instr pc2 true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")),
                          sp, Regidx Rs3, false, 8)) -∗
    instr pc3 true (JAL (sign_extend' 21 (concat_vec jimm ('b"0")), zreg)) -∗
    sie_cap_gpr KT1 M (trap_res b + (K - 6))%nat false pme -∗
    pc_is pc1 -∗
    cpu_own (S lvl) eb pme false ({["cons"]} ∪ lks) -∗
    arm_pay KT1 lvl eb pme -∗
    locked γc cpu_id -∗
    cons_res cn -∗
    ct_hi_out γu hb cb -∗
    uart_log_hi γu (1/2) (Some hb) -∗ uart_arm γu (1/2) None -∗
    pa_stk sp0 4 ↦₈[KT1] (m0 !!! Regidx Rs2) -∗
    pa_stk sp0 5 ↦₈[KT1] (m0 !!! Regidx Rs3) -∗
    (∃ w : mword 64, pa_stk sp0 6 ↦₈[KT1] w) -∗
    ct_exit_prop (CID0 := CID) γu hb cb cn γc pme m0 K lvl eb b sp0 lks -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Hsp Hthr Hq1 Hq2 Hjt Hal Hchain Hbelow.
    destruct Hthr as (T4 & T5 & T6 & T7 & T8 & T9 & T10 & T11).
    iIntros "Hi1 Hi2 Hi3 Hcg Hpc Hcnt Hpay Hlocked Hres Hhiout Howed Hwin
             H4 H5 H6 EXIT".
    assert (Hb4 : add_vec (pa_stk sp0 6%nat)
                    (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000")))
                  = pa_stk sp0 4) by (apply ct_slot_bridge; pcw).
    assert (Hb5 : add_vec (pa_stk sp0 6%nat)
                    (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000")))
                  = pa_stk sp0 5) by (apply ct_slot_bridge; pcw).
    iApply (wp_cldsp_s_sconf pc1 (mword_of_int 2 : mword 6) Rs2
              M (trap_res b + (K - 6))%nat (m0 !!! Regidx Rs2) false
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi1 [H4]").
    { iEval (rewrite Hsp Hb4). iExact "H4". }
    iApply wp_next_off_intro. iIntros "Hcg Hpc H4". rgall.
    iEval (rewrite Hsp Hb4) in "H4".
    set (R1 := <[Regidx Rs2 := regval_into_reg (m0 !!! Regidx Rs2)]> M).
    assert (HR1sp : R1 !!! Regidx csp_rs1 = pa_stk sp0 6%nat)
      by (rewrite /R1 upd_ne; [exact Hsp | reg_neq]).
    iEval (rewrite Hq1) in "Hpc".
    iApply (wp_cldsp_s_sconf pc2 (mword_of_int 1 : mword 6) Rs3
              R1 (trap_res b + (K - 6))%nat (m0 !!! Regidx Rs3) false
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi2 [H5]").
    { iEval (rewrite HR1sp Hb5). iExact "H5". }
    iApply wp_next_off_intro. iIntros "Hcg Hpc H5". rgall.
    iEval (rewrite HR1sp Hb5) in "H5".
    set (R2 := <[Regidx Rs3 := regval_into_reg (m0 !!! Regidx Rs3)]> R1).
    iEval (rewrite Hq2) in "Hpc".
    iApply (wp_cj_s_sconf pc3 (sign_extend' 21 (concat_vec jimm ('b"0")))
              R2 (trap_res b + (K - 6))%nat false Hal with "Hcg Hpc Hi3").
    iApply wp_next_off_intro. iApply bi.later_intro. iIntros "Hcg Hpc". rgall.
    iEval (rewrite Hjt) in "Hpc".
    iSpecialize ("EXIT" $! CIDq with "[%]"); [exact Hchain|].
    iApply ("EXIT" $! R2 with "[%] [%] Hcg Hpc Hcnt Hpay Hlocked Hres
              [H4 H5 H6] Hhiout Howed Hwin").
    - rewrite /R2 upd_ne; [| reg_neq]. exact HR1sp.
    - unfold ct_cs_hi. split_and!.
      + rewrite /R2 upd_ne; [| reg_neq]. rewrite /R1 upd_eq. reflexivity.
      + rewrite /R2 upd_eq. reflexivity.
      + rewrite /R2 upd_ne; [| reg_neq]. rewrite /R1 upd_ne; [| reg_neq]. exact T4.
      + rewrite /R2 upd_ne; [| reg_neq]. rewrite /R1 upd_ne; [| reg_neq]. exact T5.
      + rewrite /R2 upd_ne; [| reg_neq]. rewrite /R1 upd_ne; [| reg_neq]. exact T6.
      + rewrite /R2 upd_ne; [| reg_neq]. rewrite /R1 upd_ne; [| reg_neq]. exact T7.
      + rewrite /R2 upd_ne; [| reg_neq]. rewrite /R1 upd_ne; [| reg_neq]. exact T8.
      + rewrite /R2 upd_ne; [| reg_neq]. rewrite /R1 upd_ne; [| reg_neq]. exact T9.
      + rewrite /R2 upd_ne; [| reg_neq]. rewrite /R1 upd_ne; [| reg_neq]. exact T10.
      + rewrite /R2 upd_ne; [| reg_neq]. rewrite /R1 upd_ne; [| reg_neq]. exact T11.
    - rewrite /ct_rest. iSplitL "H4"; [by iExists _|].
      iSplitL "H5"; [by iExists _|]. iExact "H6".
  Qed.

  (* =================================================================== *)
  (*  [KILL] (+0x0b8): the C('U') kill-line loop.                         *)
  (*                                                                      *)
  (*  AN iLöb, NOT A FUEL INDUCTION.  [ConsoleInv.cons_res] relates        *)
  (*  [cons.e] to nothing, so the [cons.e--] bounds nothing -- and it does *)
  (*  not have to: the back edge is the TAKEN arm of the [bne] at +0x0da,  *)
  (*  and [wp_bne_taken_s_sconf] hands out a [▷ wp_next], which is what    *)
  (*  the Löb IH sits under.  Nothing is returned, so no count has to      *)
  (*  survive the loop.                                                    *)
  (* =================================================================== *)
  Definition ct_kill_prop `{CID0 : CpuId}
      (γu : uart_names) (hb : list mobs) (cb : bv 8) (cn : cons_names) (γc : gname)
      (pme : mword 64) (m0 : regfile) (K lvl : nat) (eb : bool)
      (b : bool) (sp0 : mword 64) (lks : gset string) : iProp Σ :=
    (wp_next (CID0 := CID0) b pme (fun (CIDk : CpuId) =>
       ∀ (M : regfile) (rr ww ee : mword 32) (bs : list (bv 8))
         (ts : list (option (list mobs))),
         ⌜ M !!! Regidx csp_rs1 = pa_stk sp0 6%nat ⌝ -∗
         ⌜ M !!! Regidx Rs1 = a_cons ⌝ -∗
         ⌜ M !!! Regidx Rs2 = (mword_of_int 10 : mword 64) ⌝ -∗
         ⌜ M !!! Regidx Rs3 = (mword_of_int 256 : mword 64) ⌝ -∗
         ⌜ M !!! Regidx Ra5 = sign_extend' 64 ee ⌝ -∗
         ⌜ ct_cs_top M m0 ⌝ -∗
         ⌜ length bs = INPUT_BUF_SIZE ⌝ -∗
         ⌜ length ts = INPUT_BUF_SIZE ⌝ -∗
         ⌜ cons_ok rr ww ee ⌝ -∗
         ⌜ cons_row rr ee bs ts ⌝ -∗
         (* THE LOOP'S OWN GUARD, HOISTED INTO THE INVARIANT.  The body
            decrements [cons.e] BEFORE the [bne] at +0x0da re-tests it, so
            what makes the decrement legal is the test the ENTRY ran: both
            ways in ([ct_kill_pre]'s [beq] at +0x0b4 and the back edge)
            establish it. *)
         ⌜ ee <> ww ⌝ -∗
         ct_exit_prop (CID0 := CID0) γu hb cb cn γc pme m0 K lvl eb b sp0 lks -∗
         sie_cap_gpr KT1 M (trap_res b + (K - 6))%nat false pme -∗
         pc_is (mword_of_int (CT + 0xb8)) -∗
         cpu_own (S lvl) eb pme false ({["cons"]} ∪ lks) -∗
         arm_pay KT1 lvl eb pme -∗
         locked γc cpu_id -∗
         a_cons_r ↦₄ rr -∗ a_cons_w ↦₄ ww -∗ a_cons_e ↦₄ ee -∗
         cons_data bs -∗ cons_tags ts -∗
         (* THE RING OWES ITS ERASE CHARACTER (lane CONS-IO, milestone B,
            ruling F2).  Every round pops an ECHOED entry out of the ring
            before the character that accounts for it reaches the log, so
            [pe = Some (hb, cb)] is what carries the gap accumulator at
            [true] across the back edge -- the glyph count is not known
            until the loop ends. *)
         ct_gh cn (Some (hb, cb)) rr ww ee bs ts -∗
         ct_hi_kill γu hb -∗
         (* THE ECHO RUN, AT THE WINDOW'S LENGTH (lane CONS-IO).  The upper
            bound is the editable window [cons.e - cons.w], which the entry
            read and every iteration shortens by one; the run's spent prefix
            is what the log entry will record. *)
         ct_kill_run γu hb cb (bv_unsigned (sub_vec ee ww)) -∗
         pa_stk sp0 4 ↦₈[KT1] (m0 !!! Regidx Rs2) -∗
         pa_stk sp0 5 ↦₈[KT1] (m0 !!! Regidx Rs3) -∗
         (∃ w : mword 64, pa_stk sp0 6 ↦₈[KT1] w) -∗
         mWP (Loop : expr riscv_lang)))%I.

  Lemma ct_mk_kill (γu : uart_names) (hb : list mobs) (cb : bv 8) (cn : cons_names)
      (γtx γc : gname) (γv : disk_names)
      (pme : mword 64) (m0 : regfile) (K lvl : nat) (eb : bool)
      (b : bool) (sp0 : mword 64) (lks : gset string) :
    cn_uart cn = γu ->
    obs_ends_in Uart0 hb cb ->
    (consoleintr_stack <= K)%nat ->
    (Z.of_nat lvl + 2 < 2 ^ 31)%Z ->
    match lvl with O => eb | S _ => false end = b ->
    (* the entry [cpu_own] is at the plain [lks] -- consputc's own [uart]
       premise is reached by [lkbelow] pushing this across the [cons]
       singleton [ct_kill_prop]'s continuation adds. *)
    locks_below lks "cons" ->
    kernel_text -∗
    dev_inv γu γv -∗
    (* the .data word consputc's callee LOADS its MMIO base from; it rides
       [SpecConsoleintr.console_caps], so every arm projects it rather than
       threading a new premise (persistent, no ghost name). *)
    uart_base_word Uart0 -∗
    is_txlock γtx γu -∗
    (* THE ERASE ARM'S JUSTIFICATION (lane OUT-FUPD): one triple per glyph,
       paid per call out of the application's boot-fixed echo shift. *)
    ct_pay_erase γu hb cb -∗
    ct_kill_prop (CID0 := CID) γu hb cb cn γc pme m0 K lvl eb b sp0 lks.
  Proof using .
    intros Hcnu Hends HK Hlvl Hb Hbelow. subst b.
    iIntros "#Ht #Hdev #Hbw #Htxl #Hep".
    iPoseProof (dev_inv_uart with "Hdev") as "#Huinv".
    iDestruct "Hep" as "[%Her #Hpy]".
    iDestruct "Hpy" as "(_ & _ & #Hwlb & #Hp)".
    rewrite /ct_kill_prop.
    iLöb as "IH".
    iIntros (CIDk Hsk M rr ww ee bs ts)
      "%Hsp %Hs1 %Hs2 %Hs3 %Ha5 %Hthr %Hlenb %Hlent %Hok %Hrow %Hne
       EXIT Hcg Hpc Hcnt Hpay Hlocked Hrc Hwc Hec Hdat Hts Hgh Hhiout Hrun
       H4 H5 H6".
    (* THE MARK, out of the accumulator: still strictly before this byte's
       history, because the loop files nothing. *)
    iDestruct "Hhiout" as (hk) "(Hhi & %Hxk)".
    (* ---- +0x0b8 c.addiw a5,a5,-1 ---- *)
    iApply (wp_caddiw_s_sconf (mword_of_int (CT + 0xb8)) Ra5 (mword_of_int 63 : mword 6)
              M (trap_res (match lvl with O => eb | S _ => false end) + (K - 6))%nat false
              ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (cnti_0b8 with "Ht"). }
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    iEval (rewrite Ha5 ct_addiw_dec) in "Hcg".
    set (ee' := add_vec ee (mword_of_int (-1) : mword 32)).
    set (L1 := <[Regidx Ra5 := regval_into_reg (sign_extend' 64 ee')]> M).
    assert (Hp0ba : add_vec_int (mword_of_int (CT + 0xb8) : mword 64) 2
                    = mword_of_int (CT + 0xba)) by pcw.
    iEval (rewrite Hp0ba) in "Hpc".
    (* ---- +0x0ba andi a4,a5,127 : the ring index ---- *)
    destruct (ct_ring_idx ee') as (idx & Hidxlt & Hidxw).
    assert (HL1a5 : L1 !!! Regidx Ra5 = sign_extend' 64 ee')
      by (rewrite /L1; apply upd_eq).
    assert (Hwv : and_vec (L1 !!! Regidx Ra5) (sign_extend' 64 (mword_of_int 127 : mword 12))
                  = (mword_of_int (Z.of_nat idx) : mword 64))
      by (rewrite HL1a5; exact Hidxw).
    iApply (wp_andi_s_sconf (mword_of_int (CT + 0xba)) Ra4 Ra5 (mword_of_int 127 : mword 12)
              (mword_of_int (Z.of_nat idx) : mword 64) L1
              (trap_res (match lvl with O => eb | S _ => false end) + (K - 6))%nat false
              ltac:(nz) ltac:(rdok) Hwv with "Hcg Hpc []").
    { iApply (cnti_0ba with "Ht"). }
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    set (L2 := <[Regidx Ra4 := regval_into_reg (mword_of_int (Z.of_nat idx) : mword 64)]> L1).
    assert (Hp0be : add_vec_int (mword_of_int (CT + 0xba) : mword 64) 4
                    = mword_of_int (CT + 0xbe)) by pcw.
    iEval (rewrite Hp0be) in "Hpc".
    (* ---- +0x0be c.add a4,a4,s1 ---- *)
    assert (HL2a4 : L2 !!! Regidx Ra4 = (mword_of_int (Z.of_nat idx) : mword 64))
      by (rewrite /L2; apply upd_eq).
    assert (HL2s1 : L2 !!! Regidx Rs1 = a_cons).
    { rewrite /L2 upd_ne; [| reg_neq]. rewrite /L1 upd_ne; [| reg_neq]. exact Hs1. }
    iApply (wp_cadd_s_sconf (mword_of_int (CT + 0xbe)) Ra4 Rs1 L2
              (trap_res (match lvl with O => eb | S _ => false end) + (K - 6))%nat false
              ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (cnti_0be with "Ht"). }
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    iEval (rewrite HL2a4 HL2s1) in "Hcg".
    set (L3 := <[Regidx Ra4 := regval_into_reg
        (add_vec (mword_of_int (Z.of_nat idx) : mword 64) a_cons)]> L2).
    assert (Hp0c0 : add_vec_int (mword_of_int (CT + 0xbe) : mword 64) 2
                    = mword_of_int (CT + 0xc0)) by pcw.
    iEval (rewrite Hp0c0) in "Hpc".
    (* ---- +0x0c0 lbu a4,24(a4) ---- *)
    destruct (cons_data_lookup_lt bs idx Hlenb Hidxlt) as [db Hlk].
    iDestruct (cons_data_acc bs idx db Hlk with "Hdat") as "[Hbyte Hdback]".
    assert (HL3a4 : L3 !!! Regidx Ra4
                    = add_vec (mword_of_int (Z.of_nat idx) : mword 64) a_cons)
      by (rewrite /L3; apply upd_eq).
    assert (Hbaddr : add_vec (L3 !!! Regidx Ra4)
                       (sign_extend' 64 (mword_of_int 24 : mword 12))
                     = pa_add a_cons (cons_buf_off + idx)).
    { rewrite HL3a4. rewrite <- (cons_byte_addr idx Hidxlt).
      rewrite (_ : add_vec (mword_of_int (Z.of_nat idx) : mword 64) a_cons
                   = add_vec a_cons (mword_of_int (Z.of_nat idx) : mword 64)); [reflexivity|].
      apply bv_eq. rewrite !add_vec64_unsigned. f_equal. ring. }
    iApply (wp_lbu_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (CT + 0xc0)) Ra4 Ra4 (mword_of_int 24 : mword 12)
              L3 (trap_res (match lvl with O => eb | S _ => false end) + (K - 6))%nat
              (db : mword 8) false ltac:(nz) ltac:(rdok) with "Hcg Hpc [] [Hbyte]").
    { iApply (cnti_0c0 with "Ht"). }
    { rgall. iEval (rewrite Hbaddr). iExact "Hbyte". }
    iApply wp_next_off_intro. iIntros "Hcg Hpc Hbyte". rgall.
    iEval (rewrite Hbaddr) in "Hbyte".
    iDestruct ("Hdback" with "Hbyte") as "Hdat".
    set (L4 := <[Regidx Ra4 := regval_into_reg (zero_extend' 64 (db : mword 8))]> L3).
    assert (Hp0c4 : add_vec_int (mword_of_int (CT + 0xc0) : mword 64) 4
                    = mword_of_int (CT + 0xc4)) by pcw.
    iEval (rewrite Hp0c4) in "Hpc".
    (* the register pins at [L4]: only a4 and a5 have moved *)
    assert (HthrL : forall r : mword 5, is_cs_idx r = true -> L4 !!! Regidx r = M !!! Regidx r).
    { intros r Hr.
      assert (N14 : r <> Ra4) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      assert (N15 : r <> Ra5) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      rewrite /L4 upd_ne; [| congruence]. rewrite /L3 upd_ne; [| congruence].
      rewrite /L2 upd_ne; [| congruence]. rewrite /L1 upd_ne; [| congruence]. reflexivity. }
    assert (HL4sp : L4 !!! Regidx csp_rs1 = pa_stk sp0 6%nat)
      by (rewrite (HthrL csp_rs1 ltac:(vm_compute; reflexivity)); exact Hsp).
    assert (HL4s1 : L4 !!! Regidx Rs1 = a_cons)
      by (rewrite (HthrL Rs1 ltac:(vm_compute; reflexivity)); exact Hs1).
    assert (HL4s2 : L4 !!! Regidx Rs2 = (mword_of_int 10 : mword 64))
      by (rewrite (HthrL Rs2 ltac:(vm_compute; reflexivity)); exact Hs2).
    assert (HL4s3 : L4 !!! Regidx Rs3 = (mword_of_int 256 : mword 64))
      by (rewrite (HthrL Rs3 ltac:(vm_compute; reflexivity)); exact Hs3).
    assert (HL4a4 : L4 !!! Regidx Ra4 = zero_extend' 64 (db : mword 8))
      by (rewrite /L4; apply upd_eq).
    assert (HL4a5 : L4 !!! Regidx Ra5 = sign_extend' 64 ee').
    { rewrite /L4 upd_ne; [| reg_neq]. rewrite /L3 upd_ne; [| reg_neq].
      rewrite /L2 upd_ne; [| reg_neq]. exact HL1a5. }
    set (cbv := bv_unsigned (db : mword 8)).
    assert (Hcbr : (0 <= cbv < 256)%Z) by (rewrite /cbv; apply w32_byte_range).
    (* ---- +0x0c4 beq a4,s2 : is it the newline that ends the line? ---- *)
    destruct (Z.eqb cbv 10) eqn:HNL.
    { (* the line ends here: leave WITHOUT the decrement -> +0x0ea *)
      iApply (wp_beq_taken_s_sconf (mword_of_int (CT + 0xc4)) (mword_of_int 38 : mword 13)
                Rs2 Ra4 L4 (trap_res (match lvl with O => eb | S _ => false end) + (K - 6))%nat
                false ltac:(nz) ltac:(nz)
                ltac:(rgall; rewrite HL4a4 HL4s2 w32_zext8_moi
                        (w32_eq_moi cbv 10 ltac:(lia) ltac:(lia)); exact HNL)
                ltac:(vm_compute; reflexivity) with "Hcg Hpc []").
      { iApply (cnti_0c4 with "Ht"). }
      iApply bi.later_intro. iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
      assert (Hj0ea : add_vec (mword_of_int (CT + 0xc4) : mword 64)
                        (sign_extend' 64 (mword_of_int 38 : mword 13))
                      = mword_of_int (CT + 0xea)) by pcw.
      iEval (rewrite Hj0ea) in "Hpc".
      iAssert (ct_hi_out γu hb cb) with "[Hhi]" as "Hhiout".
      { iApply (ct_hi_kill_out γu hb cb). iExists hk. iFrame "Hhi".
        iPureIntro; exact Hxk. }
      (* the run stops HERE, at the triples this loop actually emitted --
         and the ring's promise is discharged at exactly them. *)
      iDestruct (ct_kill_owed γu hb cb _ Her with "Hrun") as "Howed".
      iApply fupd_wp.
      iMod (ct_gh_pay_owed cn γu rr ww ee bs ts hb cb Hcnu Hends
              with "Huinv Howed Hgh") as "(Hlgh & Hwin & Hgh)".
      iModIntro.
      iApply (ct_restore23 (CIDq := CIDk) γu hb cb cn γc pme m0 L4 K lvl eb _ sp0
                (mword_of_int (CT + 0xea)) (mword_of_int (CT + 0xec))
                (mword_of_int (CT + 0xee)) (mword_of_int 11 : mword 11) lks
                HL4sp
                ltac:(exact (ct_cs_top_thr L4 M m0 HthrL Hthr))
                ltac:(pcw) ltac:(pcw) ltac:(pcw) ltac:(vm_compute; reflexivity)
                ltac:(wp_next_chain) Hbelow
                with "[] [] [] Hcg Hpc Hcnt Hpay Hlocked
                      [Hrc Hwc Hec Hdat Hts Hgh] Hhiout Hlgh Hwin H4 H5 H6 EXIT").
      { iApply (cnti_0ea with "Ht"). }
      { iApply (cnti_0ec with "Ht"). }
      { iApply (cnti_0ee with "Ht"). }
      iApply (ct_gh_res cn rr ww ee bs ts Hlenb Hlent Hok Hrow
                with "Hrc Hwc Hec Hdat Hts Hgh"). }
    (* ---- an ordinary byte: erase it ---- *)
    iApply (wp_beq_fall_s_sconf (mword_of_int (CT + 0xc4)) (mword_of_int 38 : mword 13)
              Rs2 Ra4 L4 (trap_res (match lvl with O => eb | S _ => false end) + (K - 6))%nat
              false ltac:(nz) ltac:(nz)
              ltac:(rgall; rewrite HL4a4 HL4s2 w32_zext8_moi
                      (w32_eq_moi cbv 10 ltac:(lia) ltac:(lia)); exact HNL)
              with "Hcg Hpc []").
    { iApply (cnti_0c4 with "Ht"). }
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    assert (Hp0c8 : add_vec_int (mword_of_int (CT + 0xc4) : mword 64) 4
                    = mword_of_int (CT + 0xc8)) by pcw.
    iEval (rewrite Hp0c8) in "Hpc".
    (* ---- +0x0c8 sw a5,160(s1) : cons.e-- ---- *)
    assert (Hea : add_vec (L4 !!! Regidx Rs1)
                    (sign_extend' 64 (mword_of_int 160 : mword 12)) = a_cons_e)
      by (rewrite HL4s1; reflexivity).
    iApply (wp_sw_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (CT + 0xc8)) Ra5 Rs1 (mword_of_int 160 : mword 12)
              L4 (trap_res (match lvl with O => eb | S _ => false end) + (K - 6))%nat ee false
              with "Hcg Hpc [] [Hec]").
    { iApply (cnti_0c8 with "Ht"). }
    { rgall. iEval (rewrite Hea). iExact "Hec". }
    iApply wp_next_off_intro. iIntros "Hcg Hpc Hec". rgall.
    iEval (rewrite Hea HL4a5 trunc32_sext) in "Hec".
    (* THE DECREMENT, AT THE COUPLING.  [ee <> ww] is the loop invariant's
       own clause, so [cons.e--] cannot take [e] below [w]; the live range
       shrinks by one and the row is inherited (the dropped slot's tag
       simply stays in [ts]). *)
    assert (Hok' : cons_ok rr ww ee')
      by (rewrite /ee'; exact (cons_ok_dec_e rr ww ee Hok Hne)).
    assert (Hge1 : (1 <= bv_unsigned (sub_vec ee rr))%Z).
    { destruct Hok as [Hle1 Hle2].
      pose proof (cons_sub_range ww rr) as Hrw.
      destruct (Z.eq_dec (bv_unsigned (sub_vec ww rr))
                         (bv_unsigned (sub_vec ee rr))) as [E | NE].
      - exfalso. apply Hne. symmetry. exact (cons_sub_inj rr ww ee E).
      - lia. }
    assert (Hdec : bv_unsigned (sub_vec ee' rr)
                   = (bv_unsigned (sub_vec ee rr) - 1)%Z)
      by (rewrite /ee'; exact (cons_sub_dec ee rr Hge1)).
    assert (Hrow' : cons_row rr ee' bs ts)
      by (exact (cons_row_mono rr ee ee' bs ts ltac:(lia) Hrow)).
    assert (Hp0cc : add_vec_int (mword_of_int (CT + 0xc8) : mword 64) 4
                    = mword_of_int (CT + 0xcc)) by pcw.
    iEval (rewrite Hp0cc) in "Hpc".
    (* ---- +0x0cc c.mv a0,s3 ; +0x0ce jal consputc ---- *)
    iApply (wp_cmv_s_sconf (mword_of_int (CT + 0xcc)) Ra0 Rs3 L4
              (trap_res (match lvl with O => eb | S _ => false end) + (K - 6))%nat false
              ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (cnti_0cc with "Ht"). }
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    set (L5 := <[Regidx Ra0 := regval_into_reg
        (add_vec zero_reg (L4 !!! Regidx Rs3))]> L4).
    assert (Hp0ce : add_vec_int (mword_of_int (CT + 0xcc) : mword 64) 2
                    = mword_of_int (CT + 0xce)) by pcw.
    iEval (rewrite Hp0ce) in "Hpc".
    iApply (wp_jal_s_sconf (mword_of_int (CT + 0xce)) Rra (mword_of_int 2096886 : mword 21)
              L5 (trap_res (match lvl with O => eb | S _ => false end) + (K - 6))%nat false
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity) with "Hcg Hpc []").
    { iApply (cnti_0ce with "Ht"). }
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    set (L6 := <[Regidx Rra := regval_into_reg
        (add_vec_int (mword_of_int (CT + 0xce) : mword 64) 4)]> L5).
    assert (Hjcp : add_vec (mword_of_int (CT + 0xce) : mword 64)
                     (sign_extend' 64 (mword_of_int 2096886 : mword 21))
                   = mword_of_int KernelSyms.consputc) by pcw.
    iEval (rewrite Hjcp) in "Hpc".
    assert (HL6ra : L6 !!! Regidx Rra
                    = add_vec_int (mword_of_int (CT + 0xce) : mword 64) 4)
      by (rewrite /L6; apply upd_eq).
    (* THE ARGUMENT IS BACKSPACE, so consputc's own [consputc_cs] is the
       three-byte erase triple and the chain this call owes is exactly what
       [ct_pay_erase] pays. *)
    assert (HL6a0 : L6 !!! Regidx Ra0 = (mword_of_int 256 : mword 64)).
    { rewrite /L6 upd_ne; [| reg_neq]. rewrite /L5 upd_eq. rewrite HL4s3.
      apply w32_zero_add. }
    assert (Hcsbs : consputc_cs (L6 !!! Regidx Ra0) = consputc_bs).
    { rewrite HL6a0 /consputc_cs.
      assert (Ebs : eq_vec (mword_of_int 256 : mword 64) cp_backspace = true)
        by (vm_compute; reflexivity).
      by rewrite Ebs. }
    (* ONE TRIPLE OFF THE RUN (lane CONS-IO).  The window is not empty --
       that is the loop's own guard -- so the upper bound has at least one
       triple left in it; the mark is lent to the three stores and comes
       back with the run one triple shorter. *)
    assert (Hnpos : (1 <= bv_unsigned (sub_vec ee ww))%Z)
      by (apply cons_sub_ne; exact Hne).
    iDestruct "Hrun" as (hg ii nn)
      "(%Hxg & %Hk1 & %Hsh & %Hbh & %Hlen0 & Hlgh & Harm & Hru)".
    destruct nn as [| nn]; [exfalso; lia |].
    iEval (rewrite (ct_bs_cons nn)) in "Hru".
    iEval (rewrite (ct_bs_cons nn)) in "Harm".
    (* the arm's own position is what licenses the three byte links; the
       mark merely rides along to consputc and back (redesign R2) *)
    iAssert (store_chain Uart0 γu (consputc_cs (L6 !!! Regidx Ra0))
               (uart_log_hi γu (1/2) hg ∗
                uart_arm γu (1/2)
                  (Some (hb, cb, (mjoin (replicate ii consputc_bs)
                                  ++ consputc_bs
                                  ++ mjoin (replicate nn consputc_bs))%list,
                         (length (mjoin (replicate ii consputc_bs))
                          + length consputc_bs)%nat)) ∗
                cons_run (S gen_id) (mjoin (replicate nn consputc_bs)) True))%I
      with "[Hlgh Harm Hru]" as "Hch".
    { rewrite Hcsbs.
      iApply (ct_ch_bs γu hb cb hg (mjoin (replicate ii consputc_bs))
                (mjoin (replicate nn consputc_bs)) True%I
                with "Hlgh Harm Hru"). }
    iApply (Consputc.wp_consputc_sconf KT1 γtx γu γv L6
              (trap_res (match lvl with O => eb | S _ => false end) + (K - 6))%nat
              (uart_log_hi γu (1/2) hg ∗
               uart_arm γu (1/2)
                 (Some (hb, cb, (mjoin (replicate ii consputc_bs)
                                 ++ consputc_bs
                                 ++ mjoin (replicate nn consputc_bs))%list,
                        (length (mjoin (replicate ii consputc_bs))
                         + length consputc_bs)%nat)) ∗
               cons_run (S gen_id) (mjoin (replicate nn consputc_bs)) True)%I
              (S lvl) eb false pme
              ({["cons"]} ∪ lks)
              ltac:(lia) ltac:(lia)
              with "Hcg Hcnt Ht Hpc Hdev Hbw Htxl Hch").
    all: try lkbelow.
    iApply wp_next_off_intro.
    iIntros (mcp) "Hcg Hcnt Hpc [%Hcpcs %Hcpra] (Hlgh & Harm & Hru)". rgall.
    iAssert (ct_hi_kill γu hb) with "[Hhi]" as "Hhiout".
    { iExists hk. iFrame "Hhi". iPureIntro; exact Hxk. }
    iAssert (ct_kill_run γu hb cb (bv_unsigned (sub_vec ee' ww)))
      with "[Hlgh Harm Hru]" as "Hrun".
    { iExists hg, (S ii), nn.
      iSplit; [iPureIntro; exact Hxg |].
      iSplit; [iPureIntro; exact Hk1 |].
      iSplit; [iPureIntro; exact Hsh |].
      iSplit; [iPureIntro; exact Hbh |].
      iSplit; [iPureIntro;
               rewrite /ee' (cons_sub_dec ee ww Hnpos); lia |].
      iFrame "Hlgh Hru".
      (* the triple just emitted joins the plan's emitted half, and the
         arm's index follows it *)
      iEval (rewrite app_assoc (ct_bs_snoc ii)
               -(length_app (mjoin (replicate ii consputc_bs)) consputc_bs)
               (ct_bs_snoc ii)) in "Harm".
      iExact "Harm". }
    iEval (rewrite HL6ra) in "Hpc".
    assert (Hp0d2 : ret_pc (add_vec_int (mword_of_int (CT + 0xce) : mword 64) 4)
                    = (mword_of_int (CT + 0xd2) : mword 64)) by pcw.
    iEval (rewrite Hp0d2) in "Hpc".
    assert (HthrC : forall r : mword 5, is_cs_idx r = true -> mcp !!! Regidx r = L4 !!! Regidx r).
    { intros r Hr.
      assert (N1 : r <> Rra) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      assert (N10 : r <> Ra0) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      rewrite (callee_saved_lookup Hcpcs r Hr).
      rewrite /L6 upd_ne; [| congruence]. rewrite /L5 upd_ne; [| congruence]. reflexivity. }
    assert (Hmcps1 : mcp !!! Regidx Rs1 = a_cons)
      by (rewrite (HthrC Rs1 ltac:(vm_compute; reflexivity)); exact HL4s1).
    (* ---- +0x0d2 lw a5,160(s1) ; +0x0d6 lw a4,156(s1) ---- *)
    assert (Hea2 : add_vec (mcp !!! Regidx Rs1)
                     (sign_extend' 64 (mword_of_int 160 : mword 12)) = a_cons_e)
      by (rewrite Hmcps1; reflexivity).
    iApply (wp_lw_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (CT + 0xd2)) Ra5 Rs1 (mword_of_int 160 : mword 12)
              mcp (trap_res (match lvl with O => eb | S _ => false end) + (K - 6))%nat
              ee' false ltac:(nz) ltac:(rdok) with "Hcg Hpc [] [Hec]").
    { iApply (cnti_0d2 with "Ht"). }
    { rgall. iEval (rewrite Hea2). iExact "Hec". }
    iApply wp_next_off_intro. iIntros "Hcg Hpc Hec". rgall. iEval (rewrite Hea2) in "Hec".
    set (L7 := <[Regidx Ra5 := regval_into_reg (sign_extend' 64 ee')]> mcp).
    assert (Hp0d6 : add_vec_int (mword_of_int (CT + 0xd2) : mword 64) 4
                    = mword_of_int (CT + 0xd6)) by pcw.
    iEval (rewrite Hp0d6) in "Hpc".
    assert (HL7s1 : L7 !!! Regidx Rs1 = a_cons)
      by (rewrite /L7 upd_ne; [exact Hmcps1 | reg_neq]).
    assert (Hwa2 : add_vec (L7 !!! Regidx Rs1)
                     (sign_extend' 64 (mword_of_int 156 : mword 12)) = a_cons_w)
      by (rewrite HL7s1; reflexivity).
    iApply (wp_lw_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (CT + 0xd6)) Ra4 Rs1 (mword_of_int 156 : mword 12)
              L7 (trap_res (match lvl with O => eb | S _ => false end) + (K - 6))%nat
              ww false ltac:(nz) ltac:(rdok) with "Hcg Hpc [] [Hwc]").
    { iApply (cnti_0d6 with "Ht"). }
    { rgall. iEval (rewrite Hwa2). iExact "Hwc". }
    iApply wp_next_off_intro. iIntros "Hcg Hpc Hwc". rgall. iEval (rewrite Hwa2) in "Hwc".
    set (L8 := <[Regidx Ra4 := regval_into_reg (sign_extend' 64 ww)]> L7).
    assert (Hp0da : add_vec_int (mword_of_int (CT + 0xd6) : mword 64) 4
                    = mword_of_int (CT + 0xda)) by pcw.
    iEval (rewrite Hp0da) in "Hpc".
    assert (HL8a4 : L8 !!! Regidx Ra4 = sign_extend' 64 ww)
      by (rewrite /L8; apply upd_eq).
    assert (HL8a5 : L8 !!! Regidx Ra5 = sign_extend' 64 ee').
    { rewrite /L8 upd_ne; [| reg_neq]. rewrite /L7; apply upd_eq. }
    assert (HthrL8 : forall r : mword 5, is_cs_idx r = true -> L8 !!! Regidx r = M !!! Regidx r).
    { intros r Hr.
      assert (N14 : r <> Ra4) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      assert (N15 : r <> Ra5) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      rewrite /L8 upd_ne; [| congruence]. rewrite /L7 upd_ne; [| congruence].
      rewrite (HthrC r Hr). apply HthrL; exact Hr. }
    destruct (neq_vec (sign_extend' 64 ww : mword 64) (sign_extend' 64 ee')) eqn:Hmore.
    { (* more to erase: THE BACK EDGE to +0x0b8 *)
      iApply (wp_bne_taken_s_sconf (mword_of_int (CT + 0xda)) (mword_of_int 8158 : mword 13)
                Ra5 Ra4 L8 (trap_res (match lvl with O => eb | S _ => false end) + (K - 6))%nat
                false ltac:(nz) ltac:(nz)
                ltac:(rgall; rewrite HL8a4 HL8a5; exact Hmore)
                ltac:(vm_compute; reflexivity) with "Hcg Hpc []").
      { iApply (cnti_0da with "Ht"). }
      (* the Löb back edge: the [▷] has to come off "IH", not just the goal *)
      iNext. iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
      assert (Hbk : add_vec (mword_of_int (CT + 0xda) : mword 64)
                      (sign_extend' 64 (mword_of_int 8158 : mword 13))
                    = mword_of_int (CT + 0xb8)) by pcw.
      iEval (rewrite Hbk) in "Hpc".
      iSpecialize ("IH" $! CIDk with "[%]"); [wp_next_chain|].
      iApply ("IH" $! L8 rr ww ee' bs ts with "[%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%]
                EXIT Hcg Hpc Hcnt Hpay Hlocked Hrc Hwc Hec Hdat Hts [Hgh]
                Hhiout Hrun H4 H5 H6").
      - rewrite (HthrL8 csp_rs1 ltac:(vm_compute; reflexivity)). exact Hsp.
      - rewrite (HthrL8 Rs1 ltac:(vm_compute; reflexivity)). exact Hs1.
      - rewrite (HthrL8 Rs2 ltac:(vm_compute; reflexivity)). exact Hs2.
      - rewrite (HthrL8 Rs3 ltac:(vm_compute; reflexivity)). exact Hs3.
      - exact HL8a5.
      - exact (ct_cs_top_thr L8 M m0 HthrL8 Hthr).
      - exact Hlenb.
      - exact Hlent.
      - exact Hok'.
      - exact Hrow'.
      (* the back edge re-tests [cons.e != cons.w], which is the IH's clause *)
      - intro Hc; exact (ct_ne32 ww ee' Hmore (eq_sym Hc)).
      (* ...AND THE WINDOW LOST ITS LAST ENTRY: [cons.e--] pops the editable
         window's tail, and the committed prefix is out of reach because the
         loop's own guard says [cons.e != cons.w]. *)
      - rewrite /ee'. iApply (ct_gh_pop cn hb cb rr ww ee bs ts Hne with "Hgh"). }
    (* the line is empty: fall out at +0x0de *)
    iApply (wp_bne_fall_s_sconf (mword_of_int (CT + 0xda)) (mword_of_int 8158 : mword 13)
              Ra5 Ra4 L8 (trap_res (match lvl with O => eb | S _ => false end) + (K - 6))%nat
              false ltac:(nz) ltac:(nz)
              ltac:(rgall; rewrite HL8a4 HL8a5; exact Hmore) with "Hcg Hpc []").
    { iApply (cnti_0da with "Ht"). }
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    assert (Hp0de : add_vec_int (mword_of_int (CT + 0xda) : mword 64) 4
                    = mword_of_int (CT + 0xde)) by pcw.
    iEval (rewrite Hp0de) in "Hpc".
    iDestruct (ct_hi_kill_out γu hb cb with "Hhiout") as "Hhiout".
    iDestruct (ct_kill_owed γu hb cb _ Her with "Hrun") as "Howed".
    (* the LAST pop, then the character that accounts for every one of them *)
    iDestruct (ct_gh_pop cn hb cb rr ww ee bs ts Hne with "Hgh") as "Hgh".
    iApply fupd_wp.
    iMod (ct_gh_pay_owed cn γu rr ww ee' bs ts hb cb Hcnu Hends
            with "Huinv Howed Hgh") as "(Hlgh & Hwin & Hgh)".
    iModIntro.
    iApply (ct_restore23 (CIDq := CIDk) γu hb cb cn γc pme m0 L8 K lvl eb _ sp0
              (mword_of_int (CT + 0xde)) (mword_of_int (CT + 0xe0))
              (mword_of_int (CT + 0xe2)) (mword_of_int 17 : mword 11) lks
              ltac:(rewrite (HthrL8 csp_rs1 ltac:(vm_compute; reflexivity)); exact Hsp)
              ltac:(exact (ct_cs_top_thr L8 M m0 HthrL8 Hthr))
              ltac:(pcw) ltac:(pcw) ltac:(pcw) ltac:(vm_compute; reflexivity)
              ltac:(wp_next_chain) Hbelow
              with "[] [] [] Hcg Hpc Hcnt Hpay Hlocked
                    [Hrc Hwc Hec Hdat Hts Hgh] Hhiout Hlgh Hwin H4 H5 H6 EXIT").
    { iApply (cnti_0de with "Ht"). }
    { iApply (cnti_0e0 with "Ht"). }
    { iApply (cnti_0e2 with "Ht"). }
    iApply (ct_gh_res cn rr ww ee' bs ts Hlenb Hlent Hok' Hrow'
              with "Hrc Hwc Hec Hdat Hts Hgh").
  Qed.

  (* =================================================================== *)
  (*  ['\r'] (+0x12e): echo '\n' INSTEAD of the byte, store '\n', and     *)
  (*  FALL INTO [WAKE].  The only arm that reaches the wake tail without   *)
  (*  a test, because the byte it just stored IS the newline.              *)
  (* =================================================================== *)
  Lemma ct_cr `{CIDq : CpuId}
      (γtx γc : gname) (γu : uart_names) (γv : disk_names)
      (cn : cons_names) (hh : option (list mobs))
      (pme : mword 64) (m0 M : regfile) (K lvl : nat) (eb : bool)
      (b : bool) (sp0 : mword 64) (lks : gset string)
      (rr ww ee : mword 32) (bs : list (bv 8))
      (ts : list (option (list mobs))) (h : list mobs) (c : bv 8) :
    cn_uart cn = γu ->
    cn_era cn = S gen_id ->
    ohist_ext hh h ->
    M !!! Regidx csp_rs1 = pa_stk sp0 6%nat ->
    ct_cs_hi M m0 ->
    (consoleintr_stack <= K)%nat ->
    (Z.of_nat lvl + 2 < 2 ^ 31)%Z ->
    (b = false \/ pme = zero_reg -> (CIDq : CPU) = (CID : CPU)) ->
    (* same "cons" bound as the sibling arms: this one reaches consputc,
       whose cone runs up to "uart0" (17). *)
    locks_below lks "cons" ->
    (* THE RING, DESTRUCTED, with [ct_dflt]'s room guard beside it: this arm
       falls straight into WAKE, which needs a2 to be THIS [cons.e]. *)
    length bs = INPUT_BUF_SIZE ->
    length ts = INPUT_BUF_SIZE ->
    cons_ok rr ww ee ->
    cons_row rr ee bs ts ->
    (bv_unsigned (sub_vec ee rr) < Z.of_nat INPUT_BUF_SIZE)%Z ->
    (* the byte and its tag.  This is the arm the '\r' test TOOK, so the
       byte is the carriage return and [ConsoleInv.cons_xlate] of it is the
       newline the code stores. *)
    obs_ends_in Uart0 h c ->
    c = (mword_of_int 13 : mword 8) ->
    kernel_text -∗
    dev_inv γu γv -∗
    (* the .data word consputc's callee LOADS its MMIO base from; it rides
       [SpecConsoleintr.console_caps], so every arm projects it rather than
       threading a new premise (persistent, no ghost name). *)
    uart_base_word Uart0 -∗
    is_txlock γtx γu -∗
    (* THE ECHO'S JUSTIFICATION FOR THIS ARM'S ONE BYTE (lane OUT-FUPD):
       [echo_of c] is the newline the '\r' arm puts out. *)
    ct_pay γu h c -∗
    riscv_rx_tag h -∗
    sie_cap_gpr KT1 M (trap_res b + (K - 6))%nat false pme -∗
    pc_is (mword_of_int (CT + 0x12e)) -∗
    cpu_own (S lvl) eb pme false ({["cons"]} ∪ lks) -∗
    arm_pay KT1 lvl eb pme -∗
    locked γc cpu_id -∗
    a_cons_r ↦₄ rr -∗ a_cons_w ↦₄ ww -∗ a_cons_e ↦₄ ee -∗
    cons_data bs -∗ cons_tags ts -∗ ct_gh cn None rr ww ee bs ts -∗
    uart_rx_hi γu (1/2) hh -∗
    (* THE LOG'S MARK (lane CONS-IO): lent to the echo's store and given
       back, then closed at [echo_of c] on the way to WAKE. *)
    ct_mark γu h -∗
    ct_rest sp0 -∗
    ct_wake_prop (CID0 := CID) γu h c cn γc pme m0 K lvl eb b sp0 lks -∗
    ct_exit_prop (CID0 := CID) γu h c cn γc pme m0 K lvl eb b sp0 lks -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Hcnu Hcne Hx Hsp Hcs HK Hlvl Hchain Hbelow Hlenb Hlent Hok Hrow Hroom
           Hends Hc13.
    iIntros "#Ht #Hdev #Hbw #Htxl #Hp1 #Htg Hcg Hpc Hcnt Hpay Hlocked
             Hrc Hwc Hec Hdat Hts Hgh Hhi Hmark Hrest WAKE EXIT".
    rewrite <- Hcnu.
    (* the console port's own invariant, which the append opens (lane
       CONS-IO, milestone B, ruling F2): [dev_inv] already carries it, so
       no arm takes a new premise for it. *)
    iPoseProof (dev_inv_uart with "Hdev") as "#Huinv".
    (* ---- +0x12e c.li a0,10 ; +0x130 jal consputc ---- *)
    iApply (wp_cli_s_sconf (mword_of_int (CT + 0x12e)) Ra0 (mword_of_int 10 : mword 6)
              (mword_of_int 10 : mword 64) M (trap_res b + (K - 6))%nat false
              ltac:(nz) ltac:(rdok) ltac:(pcw) with "Hcg Hpc []").
    { iApply (cnti_12e with "Ht"). }
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    set (D1 := <[Regidx Ra0 := regval_into_reg (mword_of_int 10 : mword 64)]> M).
    assert (Hp130 : add_vec_int (mword_of_int (CT + 0x12e) : mword 64) 2
                    = mword_of_int (CT + 0x130)) by pcw.
    iEval (rewrite Hp130) in "Hpc".
    iApply (wp_jal_s_sconf (mword_of_int (CT + 0x130)) Rra (mword_of_int 2096788 : mword 21)
              D1 (trap_res b + (K - 6))%nat false ltac:(nz) ltac:(rdok)
              ltac:(vm_compute; reflexivity) with "Hcg Hpc []").
    { iApply (cnti_130 with "Ht"). }
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    set (D2 := <[Regidx Rra := regval_into_reg
        (add_vec_int (mword_of_int (CT + 0x130) : mword 64) 4)]> D1).
    assert (Hjcp : add_vec (mword_of_int (CT + 0x130) : mword 64)
                     (sign_extend' 64 (mword_of_int 2096788 : mword 21))
                   = mword_of_int KernelSyms.consputc) by pcw.
    iEval (rewrite Hjcp) in "Hpc".
    assert (HD2ra : D2 !!! Regidx Rra
                    = add_vec_int (mword_of_int (CT + 0x130) : mword 64) 4)
      by (rewrite /D2; apply upd_eq).
    (* WHICH BYTE GOES OUT: a0 is the newline the '\r' test translates to,
       which is [echo_of c] at this arm's own [c = '\r']. *)
    assert (HD2a0 : D2 !!! Regidx Ra0 = (mword_of_int 10 : mword 64)).
    { rewrite /D2 upd_ne; [| reg_neq]. rewrite /D1; apply upd_eq. }
    assert (Hcsb : consputc_cs (D2 !!! Regidx Ra0) = [echo_of c]).
    { rewrite HD2a0 /consputc_cs.
      assert (Ene : eq_vec (mword_of_int 10 : mword 64) cp_backspace = false)
        by (vm_compute; reflexivity).
      rewrite Ene Hc13 ct_echo_of_13.
      assert (Ecp : cp_byte (mword_of_int 10 : mword 64) = (mword_of_int 10 : mword 8))
        by (apply bv_eq; vm_compute; reflexivity).
      by rewrite Ecp. }
    iDestruct "Hmark" as (hg) "(%Hxg & %Hk1 & Hlgh & Harm)".
    iApply fupd_wp.
    iMod (ct_ch_full (cn_uart cn) h c hg [echo_of c] True%I
            Hxg Hends ltac:(right; left; reflexivity) Hk1
            ltac:(intros Hnil; discriminate)
            with "Huinv Hp1 Hlgh Harm [//]") as "Hch0".
    iAssert (store_chain Uart0 (cn_uart cn) (consputc_cs (D2 !!! Regidx Ra0))
               (uart_log_hi (cn_uart cn) (1/2) hg ∗
                ct_append (cn_uart cn) h c [echo_of c]
                  (length [echo_of c]) True))%I
      with "[Hch0]" as "Hch".
    { rewrite Hcsb. iExact "Hch0". }
    iModIntro.
    iApply (Consputc.wp_consputc_sconf KT1 γtx (cn_uart cn) γv D2
              (trap_res b + (K - 6))%nat
              (uart_log_hi (cn_uart cn) (1/2) hg ∗
               ct_append (cn_uart cn) h c [echo_of c]
                 (length [echo_of c]) True)%I
              (S lvl) eb false pme ({["cons"]} ∪ lks)
              ltac:(lia) ltac:(lia)
              with "Hcg Hcnt Ht Hpc Hdev Hbw Htxl Hch").
    all: try lkbelow.
    iApply wp_next_off_intro.
    iIntros (mcp) "Hcg Hcnt Hpc [%Hcpcs %Hcpra] [Hlgh Hap]". rgall.
    iEval (rewrite HD2ra) in "Hpc".
    assert (Hp134 : ret_pc (add_vec_int (mword_of_int (CT + 0x130) : mword 64) 4)
                    = (mword_of_int (CT + 0x134) : mword 64)) by pcw.
    iEval (rewrite Hp134) in "Hpc".
    assert (HthrC : forall r : mword 5, is_cs_idx r = true ->
              mcp !!! Regidx r = M !!! Regidx r).
    { intros r Hr.
      assert (N1 : r <> Rra) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      assert (N10 : r <> Ra0) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      rewrite (callee_saved_lookup Hcpcs r Hr).
      rewrite /D2 upd_ne; [| congruence]. rewrite /D1 upd_ne; [| congruence]. reflexivity. }
    (* ---- +0x134/+0x138 : a5 := &cons ---- *)
    iApply (wp_auipc_s_sconf (mword_of_int (CT + 0x134)) Ra5 (mword_of_int 18 : mword 20)
              mcp (trap_res b + (K - 6))%nat false ltac:(nz) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (cnti_134 with "Ht"). }
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    set (D3 := <[Regidx Ra5 := regval_into_reg
        (add_vec (mword_of_int (CT + 0x134) : mword 64)
           (auipc_off (mword_of_int 18 : mword 20)))]> mcp).
    assert (Hp138 : add_vec_int (mword_of_int (CT + 0x134) : mword 64) 4
                    = mword_of_int (CT + 0x138)) by pcw.
    iEval (rewrite Hp138) in "Hpc".
    iApply (wp_addi4_s_sconf (mword_of_int (CT + 0x138)) Ra5 Ra5 (mword_of_int 3972 : mword 12)
              D3 (trap_res b + (K - 6))%nat false ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (cnti_138 with "Ht"). }
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    set (D4 := <[Regidx Ra5 := regval_into_reg
        (add_vec (D3 !!! Regidx Ra5) (sign_extend' 64 (mword_of_int 3972 : mword 12)))]> D3).
    assert (HD4a5 : D4 !!! Regidx Ra5 = a_cons).
    { rewrite /D4 upd_eq /D3 upd_eq /a_cons. apply bv_eq; vm_compute; reflexivity. }
    assert (Hp13c : add_vec_int (mword_of_int (CT + 0x138) : mword 64) 4
                    = mword_of_int (CT + 0x13c)) by pcw.
    iEval (rewrite Hp13c) in "Hpc".
    (* ---- +0x13c lw a4,160(a5) : a4 := cons.e ---- *)
    assert (Hea : add_vec (D4 !!! Regidx Ra5)
                    (sign_extend' 64 (mword_of_int 160 : mword 12)) = a_cons_e)
      by (rewrite HD4a5; reflexivity).
    iApply (wp_lw_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (CT + 0x13c)) Ra4 Ra5 (mword_of_int 160 : mword 12)
              D4 (trap_res b + (K - 6))%nat ee false ltac:(nz) ltac:(rdok)
              with "Hcg Hpc [] [Hec]").
    { iApply (cnti_13c with "Ht"). }
    { rgall. iEval (rewrite Hea). iExact "Hec". }
    iApply wp_next_off_intro. iIntros "Hcg Hpc Hec". rgall. iEval (rewrite Hea) in "Hec".
    set (D5 := <[Regidx Ra4 := regval_into_reg (sign_extend' 64 ee)]> D4).
    assert (Hp140 : add_vec_int (mword_of_int (CT + 0x13c) : mword 64) 4
                    = mword_of_int (CT + 0x140)) by pcw.
    iEval (rewrite Hp140) in "Hpc".
    (* ---- +0x140 addiw a3,a4,1 ---- *)
    assert (HD5a4 : D5 !!! Regidx Ra4 = sign_extend' 64 ee)
      by (rewrite /D5; apply upd_eq).
    iApply (wp_addiw_s_sconf (mword_of_int (CT + 0x140)) Ra3 Ra4 (mword_of_int 1 : mword 12)
              D5 (trap_res b + (K - 6))%nat false ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (cnti_140 with "Ht"). }
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    iEval (rewrite HD5a4 ct_addiw_inc) in "Hcg".
    set (ee1 := add_vec ee (mword_of_int 1 : mword 32)).
    set (D6 := <[Regidx Ra3 := regval_into_reg (sign_extend' 64 ee1)]> D5).
    assert (Hp144 : add_vec_int (mword_of_int (CT + 0x140) : mword 64) 4
                    = mword_of_int (CT + 0x144)) by pcw.
    iEval (rewrite Hp144) in "Hpc".
    (* ---- +0x144 c.mv a2,a3 : a2 carries the new [cons.e] into WAKE ---- *)
    assert (HD6a3 : D6 !!! Regidx Ra3 = sign_extend' 64 ee1)
      by (rewrite /D6; apply upd_eq).
    iApply (wp_cmv_s_sconf (mword_of_int (CT + 0x144)) Ra2 Ra3 D6
              (trap_res b + (K - 6))%nat false ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (cnti_144 with "Ht"). }
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    iEval (rewrite HD6a3 w32_zero_add) in "Hcg".
    set (D7 := <[Regidx Ra2 := regval_into_reg (sign_extend' 64 ee1)]> D6).
    assert (Hp146 : add_vec_int (mword_of_int (CT + 0x144) : mword 64) 2
                    = mword_of_int (CT + 0x146)) by pcw.
    iEval (rewrite Hp146) in "Hpc".
    (* ---- +0x146 sw a3,160(a5) : cons.e := e + 1 ---- *)
    assert (HD7a5 : D7 !!! Regidx Ra5 = a_cons).
    { rewrite /D7 upd_ne; [| reg_neq]. rewrite /D6 upd_ne; [| reg_neq].
      rewrite /D5 upd_ne; [| reg_neq]. exact HD4a5. }
    assert (HD7a3 : D7 !!! Regidx Ra3 = sign_extend' 64 ee1)
      by (rewrite /D7 upd_ne; [exact HD6a3 | reg_neq]).
    assert (Hea2 : add_vec (D7 !!! Regidx Ra5)
                     (sign_extend' 64 (mword_of_int 160 : mword 12)) = a_cons_e)
      by (rewrite HD7a5; reflexivity).
    iApply (wp_sw_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (CT + 0x146)) Ra3 Ra5 (mword_of_int 160 : mword 12)
              D7 (trap_res b + (K - 6))%nat ee false with "Hcg Hpc [] [Hec]").
    { iApply (cnti_146 with "Ht"). }
    { rgall. iEval (rewrite Hea2). iExact "Hec". }
    iApply wp_next_off_intro. iIntros "Hcg Hpc Hec". rgall.
    iEval (rewrite Hea2 HD7a3 trunc32_sext) in "Hec".
    assert (Hp14a : add_vec_int (mword_of_int (CT + 0x146) : mword 64) 4
                    = mword_of_int (CT + 0x14a)) by pcw.
    iEval (rewrite Hp14a) in "Hpc".
    (* ---- +0x14a andi a4,a4,127 : the ring index ---- *)
    destruct (ct_ring_idx ee) as (idx & Hidxlt & Hidxw).
    assert (HD7a4 : D7 !!! Regidx Ra4 = sign_extend' 64 ee).
    { rewrite /D7 upd_ne; [| reg_neq]. rewrite /D6 upd_ne; [| reg_neq]. exact HD5a4. }
    assert (Hwv : and_vec (D7 !!! Regidx Ra4)
                    (sign_extend' 64 (mword_of_int 127 : mword 12))
                  = (mword_of_int (Z.of_nat idx) : mword 64))
      by (rewrite HD7a4; exact Hidxw).
    iApply (wp_andi_s_sconf (mword_of_int (CT + 0x14a)) Ra4 Ra4 (mword_of_int 127 : mword 12)
              (mword_of_int (Z.of_nat idx) : mword 64) D7 (trap_res b + (K - 6))%nat false
              ltac:(nz) ltac:(rdok) Hwv with "Hcg Hpc []").
    { iApply (cnti_14a with "Ht"). }
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    set (D8 := <[Regidx Ra4 := regval_into_reg (mword_of_int (Z.of_nat idx) : mword 64)]> D7).
    assert (Hp14e : add_vec_int (mword_of_int (CT + 0x14a) : mword 64) 4
                    = mword_of_int (CT + 0x14e)) by pcw.
    iEval (rewrite Hp14e) in "Hpc".
    (* ---- +0x14e c.add a5,a5,a4 ---- *)
    assert (HD8a5 : D8 !!! Regidx Ra5 = a_cons)
      by (rewrite /D8 upd_ne; [exact HD7a5 | reg_neq]).
    assert (HD8a4 : D8 !!! Regidx Ra4 = (mword_of_int (Z.of_nat idx) : mword 64))
      by (rewrite /D8; apply upd_eq).
    iApply (wp_cadd_s_sconf (mword_of_int (CT + 0x14e)) Ra5 Ra4 D8
              (trap_res b + (K - 6))%nat false ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (cnti_14e with "Ht"). }
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    iEval (rewrite HD8a5 HD8a4) in "Hcg".
    set (D9 := <[Regidx Ra5 := regval_into_reg
        (add_vec a_cons (mword_of_int (Z.of_nat idx) : mword 64))]> D8).
    assert (Hp150 : add_vec_int (mword_of_int (CT + 0x14e) : mword 64) 2
                    = mword_of_int (CT + 0x150)) by pcw.
    iEval (rewrite Hp150) in "Hpc".
    (* ---- +0x150 c.li a4,10 ; +0x152 sb a4,24(a5) ---- *)
    iApply (wp_cli_s_sconf (mword_of_int (CT + 0x150)) Ra4 (mword_of_int 10 : mword 6)
              (mword_of_int 10 : mword 64) D9 (trap_res b + (K - 6))%nat false
              ltac:(nz) ltac:(rdok) ltac:(pcw) with "Hcg Hpc []").
    { iApply (cnti_150 with "Ht"). }
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    set (D10 := <[Regidx Ra4 := regval_into_reg (mword_of_int 10 : mword 64)]> D9).
    assert (Hp152 : add_vec_int (mword_of_int (CT + 0x150) : mword 64) 2
                    = mword_of_int (CT + 0x152)) by pcw.
    iEval (rewrite Hp152) in "Hpc".
    destruct (cons_data_lookup_lt bs idx Hlenb Hidxlt) as [db Hlk].
    iDestruct (cons_data_upd bs idx db (trunc8 (mword_of_int 10 : mword 64)) Hlk
                 with "Hdat") as "[Hbyte Hdback]".
    assert (HD10a5 : D10 !!! Regidx Ra5
                     = add_vec a_cons (mword_of_int (Z.of_nat idx) : mword 64))
      by (rewrite /D10 upd_ne; [rewrite /D9; apply upd_eq | reg_neq]).
    assert (HD10a4 : D10 !!! Regidx Ra4 = (mword_of_int 10 : mword 64))
      by (rewrite /D10; apply upd_eq).
    assert (Hbaddr : add_vec (D10 !!! Regidx Ra5)
                       (sign_extend' 64 (mword_of_int 24 : mword 12))
                     = pa_add a_cons (cons_buf_off + idx)).
    { rewrite HD10a5. rewrite <- (cons_byte_addr idx Hidxlt). reflexivity. }
    iApply (wp_sb_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (CT + 0x152)) Ra4 Ra5 (mword_of_int 24 : mword 12)
              D10 (trap_res b + (K - 6))%nat db false with "Hcg Hpc [] [Hbyte]").
    { iApply (cnti_152 with "Ht"). }
    { rgall. iEval (rewrite Hbaddr). iExact "Hbyte". }
    iApply wp_next_off_intro. iIntros "Hcg Hpc Hbyte". rgall.
    iEval (rewrite Hbaddr HD10a4) in "Hbyte".
    iDestruct ("Hdback" with "Hbyte") as "Hdat".
    assert (Hp156 : add_vec_int (mword_of_int (CT + 0x152) : mword 64) 4
                    = mword_of_int (CT + 0x156)) by pcw.
    iEval (rewrite Hp156) in "Hpc".
    (* ---- fall into [WAKE] ---- *)
    assert (HthrD : forall r : mword 5, is_cs_idx r = true ->
              D10 !!! Regidx r = mcp !!! Regidx r).
    { intros r Hr.
      assert (N12 : r <> Ra2) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      assert (N13 : r <> Ra3) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      assert (N14 : r <> Ra4) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      assert (N15 : r <> Ra5) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      rewrite /D10 upd_ne; [| congruence]. rewrite /D9 upd_ne; [| congruence].
      rewrite /D8 upd_ne; [| congruence]. rewrite /D7 upd_ne; [| congruence].
      rewrite /D6 upd_ne; [| congruence]. rewrite /D5 upd_ne; [| congruence].
      rewrite /D4 upd_ne; [| congruence]. rewrite /D3 upd_ne; [| congruence].
      reflexivity. }
    assert (HthrA : forall r : mword 5, is_cs_idx r = true ->
              D10 !!! Regidx r = M !!! Regidx r)
      by (intros r Hr; rewrite (HthrD r Hr); apply HthrC; exact Hr).
    (* THE APPEND, AT THE COUPLING.  The slot is [cons.e]'s own
       ([ct_idx_slot]), the byte is [cons_xlate '\r'] = '\n', and the tag
       filed beside it is the one the contract handed in. *)
    assert (Hidx : idx = cons_slot ee 0) by (exact (ct_idx_slot ee idx Hidxlt Hidxw)).
    assert (Hbyte10 : trunc8 (mword_of_int 10 : mword 64) = cons_xlate c).
    { rewrite Hc13 cons_xlate_cr. exact ct_trunc8_10. }
    iDestruct (cons_tags_upd ts idx h with "Htg Hts") as "Hts".
    (* THE GHOST HALF MOVES WITH THE BYTE: the editable window gains it and
       the ring's high-water mark becomes its history. *)
    iApply fupd_wp.
    iMod (ct_gh_push cn (cn_uart cn) rr ww ee bs ts idx h c hh hg
            [echo_of c] (length [echo_of c]) True%I
            eq_refl Hcne Hlenb Hlent Hok Hroom Hidx Hends Hx Hxg eq_refl
            (* K3: the store arm's plan IS its one glyph, so it closes at 1 *)
            ltac:(intros _; reflexivity) Hk1
            with "Huinv Hhi Hlgh Hap Hgh") as "(Hhi & Hlgh & Hwin & _ & Hgh)".
    iModIntro.
    iSpecialize ("WAKE" $! CIDq with "[%]"); [exact Hchain|].
    iApply ("WAKE" $! D10 rr ww ee1
              (<[idx := trunc8 (mword_of_int 10 : mword 64)]> bs)
              (<[idx := Some h]> ts)
              with "[%] [%] [%] [%] [%] [%] [%]
              Hcg Hpc Hcnt Hpay Hlocked Hrc Hwc Hec Hdat Hts [Hgh] Hrest
              [Hhi] Hlgh Hwin EXIT").
    - rewrite (HthrA csp_rs1 ltac:(vm_compute; reflexivity)). exact Hsp.
    - rewrite /D10 upd_ne; [| reg_neq]. rewrite /D9 upd_ne; [| reg_neq].
      rewrite /D8 upd_ne; [| reg_neq]. rewrite /D7; apply upd_eq.
    - exact (ct_cs_hi_thr D10 M m0 HthrA Hcs).
    - rewrite length_insert. exact Hlenb.
    - rewrite length_insert. exact Hlent.
    - rewrite /ee1. exact (cons_ok_inc_e rr ww ee Hok Hroom).
    - rewrite Hbyte10 /ee1.
      exact (cons_row_push rr ee idx bs ts h c Hlenb Hlent Hroom Hidx Hends Hrow).
    - rewrite Hbyte10 /ee1. iExact "Hgh".
    - rewrite /ct_hi_out. iExists (Some h). iFrame "Hhi".
      iPureIntro; exact (ohist_le_Some h).
  Qed.

  (* =================================================================== *)
  (*  [C('H') / '\x7f'] (+0x0f0): backspace.  Erase one byte if the line   *)
  (*  is not empty, then leave.  The same [cons.e--] the kill loop makes,  *)
  (*  minus the loop -- and, like it, bounded by nothing.                  *)
  (* =================================================================== *)
  Lemma ct_bs `{CIDq : CpuId}
      (γtx γc : gname) (γu : uart_names) (γv : disk_names)
      (cn : cons_names) (hb : list mobs) (cb : bv 8)
      (pme : mword 64) (m0 M : regfile) (K lvl : nat) (eb : bool)
      (b : bool) (sp0 : mword 64) (lks : gset string) :
    cn_uart cn = γu ->
    obs_ends_in Uart0 hb cb ->
    M !!! Regidx csp_rs1 = pa_stk sp0 6%nat ->
    ct_cs_hi M m0 ->
    (consoleintr_stack <= K)%nat ->
    (Z.of_nat lvl + 2 < 2 ^ 31)%Z ->
    (b = false \/ pme = zero_reg -> (CIDq : CPU) = (CID : CPU)) ->
    (* same "cons" bound as the sibling arms: the backspace path also
       reaches consputc, whose cone runs up to "uart0" (17). *)
    locks_below lks "cons" ->
    kernel_text -∗
    dev_inv γu γv -∗
    (* the .data word consputc's callee LOADS its MMIO base from; it rides
       [SpecConsoleintr.console_caps], so every arm projects it rather than
       threading a new premise (persistent, no ghost name). *)
    uart_base_word Uart0 -∗
    is_txlock γtx γu -∗
    (* THE ERASE ARM'S JUSTIFICATION (lane OUT-FUPD): this arm erases at
       most one glyph, so it spends at most one triple. *)
    ct_pay_erase γu hb cb -∗
    sie_cap_gpr KT1 M (trap_res b + (K - 6))%nat false pme -∗
    pc_is (mword_of_int (CT + 0xf0)) -∗
    cpu_own (S lvl) eb pme false ({["cons"]} ∪ lks) -∗
    arm_pay KT1 lvl eb pme -∗
    locked γc cpu_id -∗
    cons_res cn -∗
    ct_rest sp0 -∗
    ct_hi_kill γu hb -∗
    (* THE LOG'S MARK (lane CONS-IO): closed at [] on the empty-line exit
       and at the one erase triple on the other. *)
    ct_mark γu hb -∗
    ct_exit_prop (CID0 := CID) γu hb cb cn γc pme m0 K lvl eb b sp0 lks -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Hcnu Hends Hsp Hcs HK Hlvl Hchain Hbelow.
    iIntros "#Ht #Hdev #Hbw #Htxl #Hep Hcg Hpc Hcnt Hpay Hlocked Hres Hrest
             Hhiout Hmark EXIT".
    iPoseProof (dev_inv_uart with "Hdev") as "#Huinv".
    iDestruct "Hep" as "[%Her #Hpy]".
    (* THE MARK, out of the accumulator: this arm files nothing, so it goes
       back where it came from on both exits. *)
    iDestruct "Hhiout" as (hk) "(Hhi & %Hxk)".
    (* ---- +0x0f0/+0x0f4 : a4 := &cons ---- *)
    iApply (wp_auipc_s_sconf (mword_of_int (CT + 0xf0)) Ra4 (mword_of_int 18 : mword 20)
              M (trap_res b + (K - 6))%nat false ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (cnti_0f0 with "Ht"). }
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    set (B1 := <[Regidx Ra4 := regval_into_reg
        (add_vec (mword_of_int (CT + 0xf0) : mword 64)
           (auipc_off (mword_of_int 18 : mword 20)))]> M).
    assert (Hp0f4 : add_vec_int (mword_of_int (CT + 0xf0) : mword 64) 4
                    = mword_of_int (CT + 0xf4)) by pcw.
    iEval (rewrite Hp0f4) in "Hpc".
    iApply (wp_addi4_s_sconf (mword_of_int (CT + 0xf4)) Ra4 Ra4 (mword_of_int 4040 : mword 12)
              B1 (trap_res b + (K - 6))%nat false ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (cnti_0f4 with "Ht"). }
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    set (B2 := <[Regidx Ra4 := regval_into_reg
        (add_vec (B1 !!! Regidx Ra4) (sign_extend' 64 (mword_of_int 4040 : mword 12)))]> B1).
    assert (HB2a4 : B2 !!! Regidx Ra4 = a_cons).
    { rewrite /B2 upd_eq /B1 upd_eq /a_cons. apply bv_eq; vm_compute; reflexivity. }
    assert (Hp0f8 : add_vec_int (mword_of_int (CT + 0xf4) : mword 64) 4
                    = mword_of_int (CT + 0xf8)) by pcw.
    iEval (rewrite Hp0f8) in "Hpc".
    (* ---- +0x0f8 lw a5,160(a4) ; +0x0fc lw a4,156(a4) ---- *)
    iDestruct (ct_res_gh cn with "Hres") as (rr ww ee bs ts)
      "(%Hlenb & %Hlent & %Hok & %Hrow & Hrc & Hwc & Hec & Hdat & Hts & Hgh)".
    assert (Hea : add_vec (B2 !!! Regidx Ra4)
                    (sign_extend' 64 (mword_of_int 160 : mword 12)) = a_cons_e)
      by (rewrite HB2a4; reflexivity).
    iApply (wp_lw_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (CT + 0xf8)) Ra5 Ra4 (mword_of_int 160 : mword 12)
              B2 (trap_res b + (K - 6))%nat ee false ltac:(nz) ltac:(rdok)
              with "Hcg Hpc [] [Hec]").
    { iApply (cnti_0f8 with "Ht"). }
    { rgall. iEval (rewrite Hea). iExact "Hec". }
    iApply wp_next_off_intro. iIntros "Hcg Hpc Hec". rgall. iEval (rewrite Hea) in "Hec".
    set (B3 := <[Regidx Ra5 := regval_into_reg (sign_extend' 64 ee)]> B2).
    assert (HB3a4 : B3 !!! Regidx Ra4 = a_cons)
      by (rewrite /B3 upd_ne; [exact HB2a4 | reg_neq]).
    assert (Hwa : add_vec (B3 !!! Regidx Ra4)
                    (sign_extend' 64 (mword_of_int 156 : mword 12)) = a_cons_w)
      by (rewrite HB3a4; reflexivity).
    assert (Hp0fc : add_vec_int (mword_of_int (CT + 0xf8) : mword 64) 4
                    = mword_of_int (CT + 0xfc)) by pcw.
    iEval (rewrite Hp0fc) in "Hpc".
    iApply (wp_lw_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (CT + 0xfc)) Ra4 Ra4 (mword_of_int 156 : mword 12)
              B3 (trap_res b + (K - 6))%nat ww false ltac:(nz) ltac:(rdok)
              with "Hcg Hpc [] [Hwc]").
    { iApply (cnti_0fc with "Ht"). }
    { rgall. iEval (rewrite Hwa). iExact "Hwc". }
    iApply wp_next_off_intro. iIntros "Hcg Hpc Hwc". rgall. iEval (rewrite Hwa) in "Hwc".
    set (B4 := <[Regidx Ra4 := regval_into_reg (sign_extend' 64 ww)]> B3).
    assert (HB4a4 : B4 !!! Regidx Ra4 = sign_extend' 64 ww)
      by (rewrite /B4; apply upd_eq).
    assert (HB4a5 : B4 !!! Regidx Ra5 = sign_extend' 64 ee).
    { rewrite /B4 upd_ne; [| reg_neq]. rewrite /B3; apply upd_eq. }
    assert (HthrB : forall r : mword 5, is_cs_idx r = true ->
              B4 !!! Regidx r = M !!! Regidx r).
    { intros r Hr.
      assert (N14 : r <> Ra4) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      assert (N15 : r <> Ra5) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      rewrite /B4 upd_ne; [| congruence]. rewrite /B3 upd_ne; [| congruence].
      rewrite /B2 upd_ne; [| congruence]. rewrite /B1 upd_ne; [| congruence]. reflexivity. }
    assert (Hp100 : add_vec_int (mword_of_int (CT + 0xfc) : mword 64) 4
                    = mword_of_int (CT + 0x100)) by pcw.
    iEval (rewrite Hp100) in "Hpc".
    (* ---- +0x100 bne a4,a5 : is there anything to erase? ---- *)
    destruct (neq_vec (sign_extend' 64 ww : mword 64) (sign_extend' 64 ee)) eqn:Hne.
    2:{ (* the line is empty: straight out at +0x104 *)
      iApply (wp_bne_fall_s_sconf (mword_of_int (CT + 0x100)) (mword_of_int 26 : mword 13)
                Ra5 Ra4 B4 (trap_res b + (K - 6))%nat false ltac:(nz) ltac:(nz)
                ltac:(rgall; rewrite HB4a4 HB4a5; exact Hne) with "Hcg Hpc []").
      { iApply (cnti_100 with "Ht"). }
      iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
      assert (Hp104 : add_vec_int (mword_of_int (CT + 0x100) : mword 64) 4
                      = mword_of_int (CT + 0x104)) by pcw.
      iEval (rewrite Hp104) in "Hpc".
      iSpecialize ("EXIT" $! CIDq with "[%]"); [exact Hchain|].
      iAssert (ct_hi_out γu hb cb) with "[Hhi]" as "Hhiout".
      { iApply (ct_hi_kill_out γu hb cb). iExists hk. iFrame "Hhi".
        iPureIntro; exact Hxk. }
      (* AN ERASE THAT FOUND NOTHING TO ERASE IS A DROP (lane CONS-IO,
         milestone B): the ring does not move and nothing goes out, so the
         arm files [cs = []] itself and owes the ring nothing. *)
      iApply fupd_wp.
      iDestruct "Hmark" as (hg) "(%Hxg & %Hk1 & Hlgh & Harm)".
      iMod (ct_append_nil γu hb cb hg emp%I Hxg Hends Hk1
              with "Huinv Hpy Hlgh Harm []") as "(Hlgh & _ & Hap)".
      { (* K2: an erase byte is its own reason to drop *)
        iLeft. iSplitR; [| done].
        iPureIntro. intros _. right; right. exact Her. }
      iMod (ct_gh_drop cn γu rr ww ee bs ts hb cb hg [] 0%nat True%I
              Hcnu Hends Hxg eq_refl ltac:(intros Hnil; discriminate) Hk1
              with "Huinv Hlgh Hap Hgh") as "(Hlgh & Hwin & _ & Hgh)".
      iModIntro.
      iApply ("EXIT" $! B4 with "[%] [%] Hcg Hpc Hcnt Hpay Hlocked
                [Hrc Hwc Hec Hdat Hts Hgh] Hrest Hhiout Hlgh Hwin").
      - rewrite (HthrB csp_rs1 ltac:(vm_compute; reflexivity)). exact Hsp.
      - exact (ct_cs_hi_thr B4 M m0 HthrB Hcs).
      - iApply (ct_gh_res cn rr ww ee bs ts Hlenb Hlent Hok Hrow
                  with "Hrc Hwc Hec Hdat Hts Hgh"). }
    (* ---- +0x11a .. +0x12c : erase it ---- *)
    iApply (wp_bne_taken_s_sconf (mword_of_int (CT + 0x100)) (mword_of_int 26 : mword 13)
              Ra5 Ra4 B4 (trap_res b + (K - 6))%nat false ltac:(nz) ltac:(nz)
              ltac:(rgall; rewrite HB4a4 HB4a5; exact Hne)
              ltac:(vm_compute; reflexivity) with "Hcg Hpc []").
    { iApply (cnti_100 with "Ht"). }
    iApply bi.later_intro. iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    assert (Hj11a : add_vec (mword_of_int (CT + 0x100) : mword 64)
                      (sign_extend' 64 (mword_of_int 26 : mword 13))
                    = mword_of_int (CT + 0x11a)) by pcw.
    iEval (rewrite Hj11a) in "Hpc".
    (* +0x11a c.addiw a5,a5,-1 *)
    iApply (wp_caddiw_s_sconf (mword_of_int (CT + 0x11a)) Ra5 (mword_of_int 63 : mword 6)
              B4 (trap_res b + (K - 6))%nat false ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (cnti_11a with "Ht"). }
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    iEval (rewrite HB4a5 ct_addiw_dec) in "Hcg".
    set (ee1 := add_vec ee (mword_of_int (-1) : mword 32)).
    set (B5 := <[Regidx Ra5 := regval_into_reg (sign_extend' 64 ee1)]> B4).
    assert (Hp11c : add_vec_int (mword_of_int (CT + 0x11a) : mword 64) 2
                    = mword_of_int (CT + 0x11c)) by pcw.
    iEval (rewrite Hp11c) in "Hpc".
    (* +0x11c auipc a4,0x12 ; +0x120 sw a5,-136(a4) : cons.e-- *)
    iApply (wp_auipc_s_sconf (mword_of_int (CT + 0x11c)) Ra4 (mword_of_int 18 : mword 20)
              B5 (trap_res b + (K - 6))%nat false ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (cnti_11c with "Ht"). }
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    set (B6 := <[Regidx Ra4 := regval_into_reg
        (add_vec (mword_of_int (CT + 0x11c) : mword 64)
           (auipc_off (mword_of_int 18 : mword 20)))]> B5).
    assert (Hp120 : add_vec_int (mword_of_int (CT + 0x11c) : mword 64) 4
                    = mword_of_int (CT + 0x120)) by pcw.
    iEval (rewrite Hp120) in "Hpc".
    assert (HB6ea : add_vec (B6 !!! Regidx Ra4)
                      (sign_extend' 64 (mword_of_int 60 : mword 12)) = a_cons_e).
    { rewrite /B6 upd_eq /a_cons_e /coff_of /a_cons. apply bv_eq; vm_compute; reflexivity. }
    assert (HB6a5 : B6 !!! Regidx Ra5 = sign_extend' 64 ee1)
      by (rewrite /B6 upd_ne; [rewrite /B5; apply upd_eq | reg_neq]).
    iApply (wp_sw_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (CT + 0x120)) Ra5 Ra4 (mword_of_int 60 : mword 12)
              B6 (trap_res b + (K - 6))%nat ee false with "Hcg Hpc [] [Hec]").
    { iApply (cnti_120 with "Ht"). }
    { rgall. iEval (rewrite HB6ea). iExact "Hec". }
    iApply wp_next_off_intro. iIntros "Hcg Hpc Hec". rgall.
    iEval (rewrite HB6ea HB6a5 trunc32_sext) in "Hec".
    (* THE DECREMENT, AT THE COUPLING.  The [bne] at +0x100 that brought
       control here is the test [cons.e != cons.w], so [cons.e--] cannot
       take [e] below [w]; the live range shrinks by one and the row is
       inherited (the dropped slot's tag simply stays in [ts]). *)
    assert (Hew : ee <> ww)
      by (intro Hc; exact (ct_ne32 ww ee Hne (eq_sym Hc))).
    assert (Hok' : cons_ok rr ww ee1)
      by (rewrite /ee1; exact (cons_ok_dec_e rr ww ee Hok Hew)).
    assert (Hge1 : (1 <= bv_unsigned (sub_vec ee rr))%Z).
    { destruct Hok as [Hle1 Hle2].
      pose proof (cons_sub_range ww rr) as Hrw.
      destruct (Z.eq_dec (bv_unsigned (sub_vec ww rr))
                         (bv_unsigned (sub_vec ee rr))) as [E | NE].
      - exfalso. apply Hew. symmetry. exact (cons_sub_inj rr ww ee E).
      - lia. }
    assert (Hdec : bv_unsigned (sub_vec ee1 rr)
                   = (bv_unsigned (sub_vec ee rr) - 1)%Z)
      by (rewrite /ee1; exact (cons_sub_dec ee rr Hge1)).
    assert (Hrow' : cons_row rr ee1 bs ts)
      by (exact (cons_row_mono rr ee ee1 bs ts ltac:(lia) Hrow)).
    (* THE PROMISE, BEFORE THE POP (lane CONS-IO, milestone B, ruling F2):
       the entry about to leave the ring is a logged-and-echoed one, so the
       ring's account of the log only holds while the erase character this
       call is about to file is OWED. *)
    iDestruct (ct_gh_owe cn γu rr ww ee bs ts hb cb hk Hcnu Her Hends Hxk
                 with "Hhi Hgh") as "[Hhi Hgh]".
    iDestruct (ct_gh_pop cn hb cb rr ww ee bs ts Hew with "Hgh") as "Hgh".
    assert (Hp124 : add_vec_int (mword_of_int (CT + 0x120) : mword 64) 4
                    = mword_of_int (CT + 0x124)) by pcw.
    iEval (rewrite Hp124) in "Hpc".
    (* +0x124 li a0,256 ; +0x128 jal consputc *)
    iApply (wp_li4_s_sconf (mword_of_int (CT + 0x124)) Ra0 (mword_of_int 256 : mword 12)
              (mword_of_int 256 : mword 64) B6 (trap_res b + (K - 6))%nat false
              ltac:(nz) ltac:(rdok) ltac:(pcw) with "Hcg Hpc []").
    { iApply (cnti_124 with "Ht"). }
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    set (B7 := <[Regidx Ra0 := regval_into_reg (mword_of_int 256 : mword 64)]> B6).
    assert (Hp128 : add_vec_int (mword_of_int (CT + 0x124) : mword 64) 4
                    = mword_of_int (CT + 0x128)) by pcw.
    iEval (rewrite Hp128) in "Hpc".
    iApply (wp_jal_s_sconf (mword_of_int (CT + 0x128)) Rra (mword_of_int 2096796 : mword 21)
              B7 (trap_res b + (K - 6))%nat false ltac:(nz) ltac:(rdok)
              ltac:(vm_compute; reflexivity) with "Hcg Hpc []").
    { iApply (cnti_128 with "Ht"). }
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    set (B8 := <[Regidx Rra := regval_into_reg
        (add_vec_int (mword_of_int (CT + 0x128) : mword 64) 4)]> B7).
    assert (Hjcp : add_vec (mword_of_int (CT + 0x128) : mword 64)
                     (sign_extend' 64 (mword_of_int 2096796 : mword 21))
                   = mword_of_int KernelSyms.consputc) by pcw.
    iEval (rewrite Hjcp) in "Hpc".
    assert (HB8ra : B8 !!! Regidx Rra
                    = add_vec_int (mword_of_int (CT + 0x128) : mword 64) 4)
      by (rewrite /B8; apply upd_eq).
    (* the argument is BACKSPACE, so one erase triple goes out *)
    assert (HB8a0 : B8 !!! Regidx Ra0 = (mword_of_int 256 : mword 64)).
    { rewrite /B8 upd_ne; [| reg_neq]. rewrite /B7 upd_eq. reflexivity. }
    assert (Hcsbs : consputc_cs (B8 !!! Regidx Ra0) = consputc_bs).
    { rewrite HB8a0 /consputc_cs.
      assert (Ebs : eq_vec (mword_of_int 256 : mword 64) cp_backspace = true)
        by (vm_compute; reflexivity).
      by rewrite Ebs. }
    assert (Hechobs : cons_echo cb consputc_bs).
    { right; right. split; [exact Her |]. exists 1%nat.
      by rewrite /= ?app_nil_r. }
    iDestruct "Hmark" as (hg) "(%Hxg & %Hk1 & Hlgh & Harm)".
    iApply fupd_wp.
    iMod (ct_ch_full γu hb cb hg consputc_bs True%I Hxg Hends Hechobs Hk1
            ltac:(intros Hnil; unfold consputc_bs in Hnil; discriminate)
            with "Huinv Hpy Hlgh Harm [//]") as "Hch0".
    iAssert (store_chain Uart0 γu (consputc_cs (B8 !!! Regidx Ra0))
               (uart_log_hi γu (1/2) hg ∗
                ct_append γu hb cb consputc_bs (length consputc_bs) True))%I
      with "[Hch0]" as "Hch".
    { rewrite Hcsbs. iExact "Hch0". }
    iModIntro.
    iApply (Consputc.wp_consputc_sconf KT1 γtx γu γv B8
              (trap_res b + (K - 6))%nat
              (uart_log_hi γu (1/2) hg ∗
               ct_append γu hb cb consputc_bs (length consputc_bs) True)%I
              (S lvl) eb false pme ({["cons"]} ∪ lks)
              ltac:(lia) ltac:(lia)
              with "Hcg Hcnt Ht Hpc Hdev Hbw Htxl Hch").
    all: try lkbelow.
    iApply wp_next_off_intro.
    iIntros (mcp) "Hcg Hcnt Hpc [%Hcpcs %Hcpra] [Hlgh Hap]". rgall.
    iAssert (ct_hi_out γu hb cb) with "[Hhi]" as "Hhiout".
    { iApply (ct_hi_kill_out γu hb cb). iExists hk. iFrame "Hhi".
      iPureIntro; exact Hxk. }
    iAssert (ct_owed γu hb cb) with "[Hlgh Hap]" as "Howed".
    { iExists consputc_bs, consputc_bs, (length consputc_bs), hg.
      iSplit; [iPureIntro; exact Hechobs |].
      iSplit; [iPureIntro; apply take_ge; lia |].
      iSplit; [iPureIntro; exact Hxg |].
      (* K3: the backspace arm's plan is one erase TRIPLE, never one glyph *)
      iSplit; [iPureIntro; intros Hc; unfold consputc_bs in Hc; discriminate |].
      iSplit; [iPureIntro; exact Hk1 |].
      iFrame "Hlgh Hap". }
    iEval (rewrite HB8ra) in "Hpc".
    assert (Hp12c : ret_pc (add_vec_int (mword_of_int (CT + 0x128) : mword 64) 4)
                    = (mword_of_int (CT + 0x12c) : mword 64)) by pcw.
    iEval (rewrite Hp12c) in "Hpc".
    assert (HthrM : forall r : mword 5, is_cs_idx r = true ->
              mcp !!! Regidx r = M !!! Regidx r).
    { intros r Hr.
      assert (N1 : r <> Rra) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      assert (N10 : r <> Ra0) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      assert (N14 : r <> Ra4) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      assert (N15 : r <> Ra5) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      rewrite (callee_saved_lookup Hcpcs r Hr).
      rewrite /B8 upd_ne; [| congruence]. rewrite /B7 upd_ne; [| congruence].
      rewrite /B6 upd_ne; [| congruence]. rewrite /B5 upd_ne; [| congruence].
      rewrite (HthrB r Hr). reflexivity. }
    (* +0x12c c.j -> the exit at +0x104 *)
    iApply (wp_cj_s_sconf (mword_of_int (CT + 0x12c))
              (sign_extend' 21 (concat_vec (mword_of_int 2028 : mword 11) ('b"0")))
              mcp (trap_res b + (K - 6))%nat false
              ltac:(vm_compute; reflexivity) with "Hcg Hpc []").
    { iApply (cnti_12c with "Ht"). }
    iApply wp_next_off_intro. iApply bi.later_intro. iIntros "Hcg Hpc". rgall.
    assert (Hj104 : add_vec (mword_of_int (CT + 0x12c) : mword 64)
                      (sign_extend' 64 (sign_extend' 21
                         (concat_vec (mword_of_int 2028 : mword 11) ('b"0"))))
                    = mword_of_int (CT + 0x104)) by pcw.
    iEval (rewrite Hj104) in "Hpc".
    iSpecialize ("EXIT" $! CIDq with "[%]"); [exact Hchain|].
    (* ...AND IT IS PAID once the glyph has gone out. *)
    iApply fupd_wp.
    iMod (ct_gh_pay_owed cn γu rr ww ee1 bs ts hb cb Hcnu Hends
            with "Huinv Howed Hgh") as "(Hlgh2 & Hwin & Hgh)".
    iModIntro.
    iApply ("EXIT" $! mcp with "[%] [%] Hcg Hpc Hcnt Hpay Hlocked
              [Hrc Hwc Hec Hdat Hts Hgh] Hrest Hhiout Hlgh2 Hwin").
    - rewrite (HthrM csp_rs1 ltac:(vm_compute; reflexivity)). exact Hsp.
    - exact (ct_cs_hi_thr mcp M m0 HthrM Hcs).
    - iApply (ct_gh_res cn rr ww ee1 bs ts Hlenb Hlent Hok' Hrow'
                with "Hrc Hwc Hec Hdat Hts Hgh").
  Qed.

  (* =================================================================== *)
  (*  [C('U')] (+0x092): the kill-line arm's PREAMBLE.  It shrink-wraps s2 *)
  (*  and s3 into slots 4 and 5 -- the one arm that uses them -- hoists    *)
  (*  &cons, '\n' and BACKSPACE into s1/s2/s3, and then either enters the  *)
  (*  loop or, on an already-empty line, leaves through the restore stub.  *)
  (* =================================================================== *)
  Lemma ct_kill_pre `{CIDq : CpuId}
      (γu : uart_names) (cn : cons_names) (hb : list mobs) (cb : bv 8)
      (γc : gname) (pme : mword 64) (m0 M : regfile) (K lvl : nat) (eb : bool)
      (b : bool) (sp0 : mword 64) (lks : gset string) :
    cn_uart cn = γu ->
    obs_ends_in Uart0 hb cb ->
    M !!! Regidx csp_rs1 = pa_stk sp0 6%nat ->
    ct_cs_hi M m0 ->
    (b = false \/ pme = zero_reg -> (CIDq : CPU) = (CID : CPU)) ->
    (* same "cons" bound as the sibling arms: this one reaches consputc,
       whose cone runs up to "uart0" (17). *)
    locks_below lks "cons" ->
    kernel_text -∗
    (* the console port's own invariant: the already-empty line files its
       drop here (lane CONS-IO, milestone B). *)
    uart_inv Uart0 γu -∗
    (* the erase arm's currency, which this preamble both SPENDS (nothing,
       on the already-empty line) and hands to the loop as its run *)
    ct_pay_erase γu hb cb -∗
    sie_cap_gpr KT1 M (trap_res b + (K - 6))%nat false pme -∗
    pc_is (mword_of_int (CT + 0x92)) -∗
    cpu_own (S lvl) eb pme false ({["cons"]} ∪ lks) -∗
    arm_pay KT1 lvl eb pme -∗
    locked γc cpu_id -∗
    cons_res cn -∗
    ct_rest sp0 -∗
    ct_hi_kill γu hb -∗
    ct_mark γu hb -∗
    ct_kill_prop (CID0 := CID) γu hb cb cn γc pme m0 K lvl eb b sp0 lks -∗
    ct_exit_prop (CID0 := CID) γu hb cb cn γc pme m0 K lvl eb b sp0 lks -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Hcnu Hends Hsp Hcs Hchain Hbelow.
    pose proof (ct_cs_hi_top M m0 Hcs) as Htop.
    destruct Hcs as (HS2 & HS3 & _ & _ & _ & _ & _ & _ & _ & _).
    iIntros "#Ht #Huinv #Hep Hcg Hpc Hcnt Hpay Hlocked Hres Hrest Hhiout Hmark
             KILL EXIT".
    iDestruct "Hep" as "[%Her #Hpy]".
    (* ---- +0x092/+0x094: the shrink-wrap ---- *)
    iDestruct "Hrest" as "(R4 & R5 & H6)".
    iDestruct "R4" as (u4) "H4". iDestruct "R5" as (u5) "H5".
    assert (Hb4 : add_vec (pa_stk sp0 6%nat)
                    (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000")))
                  = pa_stk sp0 4) by (apply ct_slot_bridge; pcw).
    assert (Hb5 : add_vec (pa_stk sp0 6%nat)
                    (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000")))
                  = pa_stk sp0 5) by (apply ct_slot_bridge; pcw).
    iApply (wp_csdsp_s_sconf (mword_of_int (CT + 0x92)) (mword_of_int 2 : mword 6) Rs2
              M (trap_res b + (K - 6))%nat u4 false with "Hcg Hpc [] [H4]").
    { iApply (cnti_092 with "Ht"). }
    { iEval (rewrite Hsp Hb4). iExact "H4". }
    iApply wp_next_off_intro. iIntros "Hcg Hpc H4". rgall.
    iEval (rewrite Hsp Hb4 HS2) in "H4".
    assert (Hp094 : add_vec_int (mword_of_int (CT + 0x92) : mword 64) 2
                    = mword_of_int (CT + 0x94)) by pcw.
    iEval (rewrite Hp094) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (CT + 0x94)) (mword_of_int 1 : mword 6) Rs3
              M (trap_res b + (K - 6))%nat u5 false with "Hcg Hpc [] [H5]").
    { iApply (cnti_094 with "Ht"). }
    { iEval (rewrite Hsp Hb5). iExact "H5". }
    iApply wp_next_off_intro. iIntros "Hcg Hpc H5". rgall.
    iEval (rewrite Hsp Hb5 HS3) in "H5".
    assert (Hp096 : add_vec_int (mword_of_int (CT + 0x94) : mword 64) 2
                    = mword_of_int (CT + 0x96)) by pcw.
    iEval (rewrite Hp096) in "Hpc".
    (* ---- +0x096/+0x09a : a4 := &cons ---- *)
    iApply (wp_auipc_s_sconf (mword_of_int (CT + 0x96)) Ra4 (mword_of_int 18 : mword 20)
              M (trap_res b + (K - 6))%nat false ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (cnti_096 with "Ht"). }
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    set (E1 := <[Regidx Ra4 := regval_into_reg
        (add_vec (mword_of_int (CT + 0x96) : mword 64)
           (auipc_off (mword_of_int 18 : mword 20)))]> M).
    assert (Hp09a : add_vec_int (mword_of_int (CT + 0x96) : mword 64) 4
                    = mword_of_int (CT + 0x9a)) by pcw.
    iEval (rewrite Hp09a) in "Hpc".
    iApply (wp_addi4_s_sconf (mword_of_int (CT + 0x9a)) Ra4 Ra4 (mword_of_int 34 : mword 12)
              E1 (trap_res b + (K - 6))%nat false ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (cnti_09a with "Ht"). }
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    set (E2 := <[Regidx Ra4 := regval_into_reg
        (add_vec (E1 !!! Regidx Ra4) (sign_extend' 64 (mword_of_int 34 : mword 12)))]> E1).
    assert (HE2a4 : E2 !!! Regidx Ra4 = a_cons).
    { rewrite /E2 upd_eq /E1 upd_eq /a_cons. apply bv_eq; vm_compute; reflexivity. }
    assert (Hp09e : add_vec_int (mword_of_int (CT + 0x9a) : mword 64) 4
                    = mword_of_int (CT + 0x9e)) by pcw.
    iEval (rewrite Hp09e) in "Hpc".
    (* ---- +0x09e lw a5,160(a4) ; +0x0a2 lw a4,156(a4) ---- *)
    iDestruct (ct_res_gh cn with "Hres") as (rr ww ee bs ts)
      "(%Hlenb & %Hlent & %Hok & %Hrow & Hrc & Hwc & Hec & Hdat & Hts & Hgh)".
    assert (Hea : add_vec (E2 !!! Regidx Ra4)
                    (sign_extend' 64 (mword_of_int 160 : mword 12)) = a_cons_e)
      by (rewrite HE2a4; reflexivity).
    iApply (wp_lw_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (CT + 0x9e)) Ra5 Ra4 (mword_of_int 160 : mword 12)
              E2 (trap_res b + (K - 6))%nat ee false ltac:(nz) ltac:(rdok)
              with "Hcg Hpc [] [Hec]").
    { iApply (cnti_09e with "Ht"). }
    { rgall. iEval (rewrite Hea). iExact "Hec". }
    iApply wp_next_off_intro. iIntros "Hcg Hpc Hec". rgall. iEval (rewrite Hea) in "Hec".
    set (E3 := <[Regidx Ra5 := regval_into_reg (sign_extend' 64 ee)]> E2).
    assert (HE3a4 : E3 !!! Regidx Ra4 = a_cons)
      by (rewrite /E3 upd_ne; [exact HE2a4 | reg_neq]).
    assert (Hwa : add_vec (E3 !!! Regidx Ra4)
                    (sign_extend' 64 (mword_of_int 156 : mword 12)) = a_cons_w)
      by (rewrite HE3a4; reflexivity).
    assert (Hp0a2 : add_vec_int (mword_of_int (CT + 0x9e) : mword 64) 4
                    = mword_of_int (CT + 0xa2)) by pcw.
    iEval (rewrite Hp0a2) in "Hpc".
    iApply (wp_lw_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (CT + 0xa2)) Ra4 Ra4 (mword_of_int 156 : mword 12)
              E3 (trap_res b + (K - 6))%nat ww false ltac:(nz) ltac:(rdok)
              with "Hcg Hpc [] [Hwc]").
    { iApply (cnti_0a2 with "Ht"). }
    { rgall. iEval (rewrite Hwa). iExact "Hwc". }
    iApply wp_next_off_intro. iIntros "Hcg Hpc Hwc". rgall. iEval (rewrite Hwa) in "Hwc".
    set (E4 := <[Regidx Ra4 := regval_into_reg (sign_extend' 64 ww)]> E3).
    assert (Hp0a6 : add_vec_int (mword_of_int (CT + 0xa2) : mword 64) 4
                    = mword_of_int (CT + 0xa6)) by pcw.
    iEval (rewrite Hp0a6) in "Hpc".
    (* ---- +0x0a6/+0x0aa : s1 := &cons ---- *)
    iApply (wp_auipc_s_sconf (mword_of_int (CT + 0xa6)) Rs1 (mword_of_int 18 : mword 20)
              E4 (trap_res b + (K - 6))%nat false ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (cnti_0a6 with "Ht"). }
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    set (E5 := <[Regidx Rs1 := regval_into_reg
        (add_vec (mword_of_int (CT + 0xa6) : mword 64)
           (auipc_off (mword_of_int 18 : mword 20)))]> E4).
    assert (Hp0aa : add_vec_int (mword_of_int (CT + 0xa6) : mword 64) 4
                    = mword_of_int (CT + 0xaa)) by pcw.
    iEval (rewrite Hp0aa) in "Hpc".
    iApply (wp_addi4_s_sconf (mword_of_int (CT + 0xaa)) Rs1 Rs1 (mword_of_int 18 : mword 12)
              E5 (trap_res b + (K - 6))%nat false ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (cnti_0aa with "Ht"). }
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    set (E6 := <[Regidx Rs1 := regval_into_reg
        (add_vec (E5 !!! Regidx Rs1) (sign_extend' 64 (mword_of_int 18 : mword 12)))]> E5).
    assert (HE6s1 : E6 !!! Regidx Rs1 = a_cons).
    { rewrite /E6 upd_eq /E5 upd_eq /a_cons. apply bv_eq; vm_compute; reflexivity. }
    assert (Hp0ae : add_vec_int (mword_of_int (CT + 0xaa) : mword 64) 4
                    = mword_of_int (CT + 0xae)) by pcw.
    iEval (rewrite Hp0ae) in "Hpc".
    (* ---- +0x0ae c.li s2,10 ; +0x0b0 li s3,256 : the loop's two constants ---- *)
    iApply (wp_cli_s_sconf (mword_of_int (CT + 0xae)) Rs2 (mword_of_int 10 : mword 6)
              (mword_of_int 10 : mword 64) E6 (trap_res b + (K - 6))%nat false
              ltac:(nz) ltac:(rdok) ltac:(pcw) with "Hcg Hpc []").
    { iApply (cnti_0ae with "Ht"). }
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    set (E7 := <[Regidx Rs2 := regval_into_reg (mword_of_int 10 : mword 64)]> E6).
    assert (Hp0b0 : add_vec_int (mword_of_int (CT + 0xae) : mword 64) 2
                    = mword_of_int (CT + 0xb0)) by pcw.
    iEval (rewrite Hp0b0) in "Hpc".
    iApply (wp_li4_s_sconf (mword_of_int (CT + 0xb0)) Rs3 (mword_of_int 256 : mword 12)
              (mword_of_int 256 : mword 64) E7 (trap_res b + (K - 6))%nat false
              ltac:(nz) ltac:(rdok) ltac:(pcw) with "Hcg Hpc []").
    { iApply (cnti_0b0 with "Ht"). }
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    set (E8 := <[Regidx Rs3 := regval_into_reg (mword_of_int 256 : mword 64)]> E7).
    assert (Hp0b4 : add_vec_int (mword_of_int (CT + 0xb0) : mword 64) 4
                    = mword_of_int (CT + 0xb4)) by pcw.
    iEval (rewrite Hp0b4) in "Hpc".
    (* the register pins at [E8] *)
    assert (HE8s3 : E8 !!! Regidx Rs3 = (mword_of_int 256 : mword 64))
      by (rewrite /E8; apply upd_eq).
    assert (HE8s2 : E8 !!! Regidx Rs2 = (mword_of_int 10 : mword 64))
      by (rewrite /E8 upd_ne; [rewrite /E7; apply upd_eq | reg_neq]).
    assert (HE8s1 : E8 !!! Regidx Rs1 = a_cons).
    { rewrite /E8 upd_ne; [| reg_neq]. rewrite /E7 upd_ne; [| reg_neq]. exact HE6s1. }
    assert (HE8a5 : E8 !!! Regidx Ra5 = sign_extend' 64 ee).
    { rewrite /E8 upd_ne; [| reg_neq]. rewrite /E7 upd_ne; [| reg_neq].
      rewrite /E6 upd_ne; [| reg_neq]. rewrite /E5 upd_ne; [| reg_neq].
      rewrite /E4 upd_ne; [| reg_neq]. rewrite /E3; apply upd_eq. }
    assert (HE8a4 : E8 !!! Regidx Ra4 = sign_extend' 64 ww).
    { rewrite /E8 upd_ne; [| reg_neq]. rewrite /E7 upd_ne; [| reg_neq].
      rewrite /E6 upd_ne; [| reg_neq]. rewrite /E5 upd_ne; [| reg_neq].
      rewrite /E4; apply upd_eq. }
    assert (HthrE : forall r : mword 5, r <> Rs1 -> r <> Rs2 -> r <> Rs3 ->
              r <> Ra4 -> r <> Ra5 -> E8 !!! Regidx r = M !!! Regidx r).
    { intros r N9 N18 N19 N14 N15.
      rewrite /E8 upd_ne; [| congruence]. rewrite /E7 upd_ne; [| congruence].
      rewrite /E6 upd_ne; [| congruence]. rewrite /E5 upd_ne; [| congruence].
      rewrite /E4 upd_ne; [| congruence]. rewrite /E3 upd_ne; [| congruence].
      rewrite /E2 upd_ne; [| congruence]. rewrite /E1 upd_ne; [| congruence].
      reflexivity. }
    assert (HE8sp : E8 !!! Regidx csp_rs1 = pa_stk sp0 6%nat)
      by (rewrite (HthrE csp_rs1 ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)
                     ltac:(reg_neq) ltac:(reg_neq)); exact Hsp).
    assert (HE8top : ct_cs_top E8 m0)
      by (exact (ct_cs_top_thr3 E8 M m0 HthrE Htop)).
    (* ---- +0x0b4 beq a4,a5 : is the line already empty? ---- *)
    destruct (eq_vec (sign_extend' 64 ww : mword 64) (sign_extend' 64 ee)) eqn:Hemp.
    { (* nothing to erase: restore s2/s3 at +0x0e4 and leave *)
      iApply (wp_beq_taken_s_sconf (mword_of_int (CT + 0xb4)) (mword_of_int 48 : mword 13)
                Ra5 Ra4 E8 (trap_res b + (K - 6))%nat false ltac:(nz) ltac:(nz)
                ltac:(rgall; rewrite HE8a4 HE8a5; exact Hemp)
                ltac:(vm_compute; reflexivity) with "Hcg Hpc []").
      { iApply (cnti_0b4 with "Ht"). }
      iApply bi.later_intro. iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
      assert (Hj0e4 : add_vec (mword_of_int (CT + 0xb4) : mword 64)
                        (sign_extend' 64 (mword_of_int 48 : mword 13))
                      = mword_of_int (CT + 0xe4)) by pcw.
      iEval (rewrite Hj0e4) in "Hpc".
      iDestruct (ct_hi_kill_out γu hb cb with "Hhiout") as "Hhiout".
      (* AN ALREADY-EMPTY LINE IS A DROP (lane CONS-IO, milestone B): the
         ring does not move and no glyph goes out, so the byte is logged at
         [cs = []] right here. *)
      iApply fupd_wp.
      iDestruct "Hmark" as (hg) "(%Hxg & %Hk1 & Hlgh & Harm)".
      iMod (ct_append_nil γu hb cb hg emp%I Hxg Hends Hk1
              with "Huinv Hpy Hlgh Harm []") as "(Hlgh & _ & Hap)".
      { (* K2: an erase byte is its own reason to drop *)
        iLeft. iSplitR; [| done].
        iPureIntro. intros _. right; right. exact Her. }
      iMod (ct_gh_drop cn γu rr ww ee bs ts hb cb hg [] 0%nat True%I
              Hcnu Hends Hxg eq_refl ltac:(intros Hnil; discriminate) Hk1
              with "Huinv Hlgh Hap Hgh") as "(Hlgh & Hwin & _ & Hgh)".
      iModIntro.
      iApply (ct_restore23 (CIDq := CIDq) γu hb cb cn γc pme m0 E8 K lvl eb _ sp0
                (mword_of_int (CT + 0xe4)) (mword_of_int (CT + 0xe6))
                (mword_of_int (CT + 0xe8)) (mword_of_int 14 : mword 11) lks
                HE8sp HE8top
                ltac:(pcw) ltac:(pcw) ltac:(pcw) ltac:(vm_compute; reflexivity)
                Hchain Hbelow
                with "[] [] [] Hcg Hpc Hcnt Hpay Hlocked
                      [Hrc Hwc Hec Hdat Hts Hgh] Hhiout Hlgh Hwin H4 H5 H6 EXIT").
      { iApply (cnti_0e4 with "Ht"). }
      { iApply (cnti_0e6 with "Ht"). }
      { iApply (cnti_0e8 with "Ht"). }
      iApply (ct_gh_res cn rr ww ee bs ts Hlenb Hlent Hok Hrow
                with "Hrc Hwc Hec Hdat Hts Hgh"). }
    (* ---- the line is not empty: enter the loop at +0x0b8 ---- *)
    iApply (wp_beq_fall_s_sconf (mword_of_int (CT + 0xb4)) (mword_of_int 48 : mword 13)
              Ra5 Ra4 E8 (trap_res b + (K - 6))%nat false ltac:(nz) ltac:(nz)
              ltac:(rgall; rewrite HE8a4 HE8a5; exact Hemp) with "Hcg Hpc []").
    { iApply (cnti_0b4 with "Ht"). }
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    assert (Hp0b8 : add_vec_int (mword_of_int (CT + 0xb4) : mword 64) 4
                    = mword_of_int (CT + 0xb8)) by pcw.
    iEval (rewrite Hp0b8) in "Hpc".
    iSpecialize ("KILL" $! CIDq with "[%]"); [exact Hchain|].
    (* the [beq] the loop is entered THROUGH is what supplies its invariant's
       [cons.e != cons.w] clause -- the body decrements before the back edge
       re-tests. *)
    iApply fupd_wp.
    iMod (ct_mk_kill_run γu hb cb (bv_unsigned (sub_vec ee ww))
                 ltac:(exact (proj1 (cons_sub_range ee ww))) Hends
                 with "Huinv [] Hmark") as "Hrun";
      [ by iFrame "Hpy" |].
    iModIntro.
    (* THE PROMISE THE LOOP CARRIES (lane CONS-IO, milestone B, ruling F2):
       the first round pops before anything is echoed, so the ring owes its
       erase character from the moment the loop is entered. *)
    iDestruct "Hhiout" as (hk) "(Hhi & %Hxk)".
    iDestruct (ct_gh_owe cn γu rr ww ee bs ts hb cb hk Hcnu Her Hends Hxk
                 with "Hhi Hgh") as "[Hhi Hgh]".
    iAssert (ct_hi_kill γu hb) with "[Hhi]" as "Hhiout".
    { iExists hk. iFrame "Hhi". iPureIntro; exact Hxk. }
    iApply ("KILL" $! E8 rr ww ee bs ts
              with "[%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%]
              EXIT Hcg Hpc Hcnt Hpay Hlocked Hrc Hwc Hec Hdat Hts Hgh Hhiout
              Hrun H4 H5 H6");
      [ exact HE8sp | exact HE8s1 | exact HE8s2 | exact HE8s3 | exact HE8a5
      | exact HE8top | exact Hlenb | exact Hlent | exact Hok | exact Hrow
      | intro Hc; exact (ct_eqf32 ww ee Hemp (eq_sym Hc)) ].
  Qed.

  (* =================================================================== *)
  (*  [STORE] (+0x04e): the default arm's tail -- echo the byte, append it *)
  (*  to the ring, and decide whether the line is complete.  THREE ways    *)
  (*  reach [WAKE] from here ('\n', C('D'), a full ring) and one leaves.   *)
  (* =================================================================== *)
  Lemma ct_store `{CIDq : CpuId}
      (γtx γc : gname) (γu : uart_names) (γv : disk_names)
      (cn : cons_names) (hh : option (list mobs))
      (pme : mword 64) (m0 M : regfile) (K lvl : nat) (eb : bool)
      (b : bool) (sp0 : mword 64) (cv : mword 64) (lks : gset string)
      (rr ww ee : mword 32) (bs : list (bv 8))
      (ts : list (option (list mobs))) (h : list mobs) (c : bv 8) :
    cn_uart cn = γu ->
    cn_era cn = S gen_id ->
    ohist_ext hh h ->
    M !!! Regidx csp_rs1 = pa_stk sp0 6%nat ->
    M !!! Regidx Rs1 = cv ->
    ct_cs_hi M m0 ->
    (consoleintr_stack <= K)%nat ->
    (Z.of_nat lvl + 2 < 2 ^ 31)%Z ->
    (b = false \/ pme = zero_reg -> (CIDq : CPU) = (CID : CPU)) ->
    (* same "cons" bound as the sibling arms: the store path reaches
       consputc, whose cone runs up to "uart0" (17). *)
    locks_below lks "cons" ->
    (* THE RING, DESTRUCTED, with [ct_dflt]'s room guard beside it: the
       three ways out of this block that reach WAKE all need a2 to be THIS
       [cons.e], which [cons_res]'s existential cannot say. *)
    length bs = INPUT_BUF_SIZE ->
    length ts = INPUT_BUF_SIZE ->
    cons_ok rr ww ee ->
    cons_row rr ee bs ts ->
    (bv_unsigned (sub_vec ee rr) < Z.of_nat INPUT_BUF_SIZE)%Z ->
    (* the byte and its tag.  This is the arm the '\r' test did NOT take,
       so [ConsoleInv.cons_xlate] is the identity on the byte. *)
    obs_ends_in Uart0 h c ->
    cv = (extend_value (n := 8) true (c : mword 8) : mword 64) ->
    c <> (mword_of_int 13 : mword 8) ->
    kernel_text -∗
    dev_inv γu γv -∗
    (* the .data word consputc's callee LOADS its MMIO base from; it rides
       [SpecConsoleintr.console_caps], so every arm projects it rather than
       threading a new premise (persistent, no ghost name). *)
    uart_base_word Uart0 -∗
    is_txlock γtx γu -∗
    (* THE ECHO'S JUSTIFICATION FOR THIS ARM'S ONE BYTE (lane OUT-FUPD):
       the default arm echoes the byte that arrived. *)
    ct_pay γu h c -∗
    riscv_rx_tag h -∗
    sie_cap_gpr KT1 M (trap_res b + (K - 6))%nat false pme -∗
    pc_is (mword_of_int (CT + 0x4e)) -∗
    cpu_own (S lvl) eb pme false ({["cons"]} ∪ lks) -∗
    arm_pay KT1 lvl eb pme -∗
    locked γc cpu_id -∗
    a_cons_r ↦₄ rr -∗ a_cons_w ↦₄ ww -∗ a_cons_e ↦₄ ee -∗
    cons_data bs -∗ cons_tags ts -∗ ct_gh cn None rr ww ee bs ts -∗
    uart_rx_hi γu (1/2) hh -∗
    (* THE LOG'S MARK (lane CONS-IO), closed at [echo_of c] after the echo *)
    ct_mark γu h -∗
    ct_rest sp0 -∗
    ct_wake_prop (CID0 := CID) γu h c cn γc pme m0 K lvl eb b sp0 lks -∗
    ct_exit_prop (CID0 := CID) γu h c cn γc pme m0 K lvl eb b sp0 lks -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Hcnu Hcne Hx Hsp Hs1 Hcs HK Hlvl Hchain Hbelow Hlenb Hlent Hok Hrow Hroom
           Hends Hcv Hc13.
    iIntros "#Ht #Hdev #Hbw #Htxl #Hp1 #Htg Hcg Hpc Hcnt Hpay Hlocked
             Hrc Hwc Hec Hdat Hts Hgh Hhi Hmark Hrest WAKE EXIT".
    rewrite <- Hcnu.
    (* the console port's own invariant, which the append opens (lane
       CONS-IO, milestone B, ruling F2): [dev_inv] already carries it, so
       no arm takes a new premise for it. *)
    iPoseProof (dev_inv_uart with "Hdev") as "#Huinv".
    (* ---- +0x04e c.mv a0,s1 ; +0x050 jal consputc : the echo ---- *)
    iApply (wp_cmv_s_sconf (mword_of_int (CT + 0x4e)) Ra0 Rs1 M
              (trap_res b + (K - 6))%nat false ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (cnti_04e with "Ht"). }
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    iEval (rewrite Hs1 w32_zero_add) in "Hcg".
    set (F1 := <[Regidx Ra0 := regval_into_reg cv]> M).
    assert (Hp050 : add_vec_int (mword_of_int (CT + 0x4e) : mword 64) 2
                    = mword_of_int (CT + 0x50)) by pcw.
    iEval (rewrite Hp050) in "Hpc".
    iApply (wp_jal_s_sconf (mword_of_int (CT + 0x50)) Rra (mword_of_int 2097012 : mword 21)
              F1 (trap_res b + (K - 6))%nat false ltac:(nz) ltac:(rdok)
              ltac:(vm_compute; reflexivity) with "Hcg Hpc []").
    { iApply (cnti_050 with "Ht"). }
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    set (F2 := <[Regidx Rra := regval_into_reg
        (add_vec_int (mword_of_int (CT + 0x50) : mword 64) 4)]> F1).
    assert (Hjcp : add_vec (mword_of_int (CT + 0x50) : mword 64)
                     (sign_extend' 64 (mword_of_int 2097012 : mword 21))
                   = mword_of_int KernelSyms.consputc) by pcw.
    iEval (rewrite Hjcp) in "Hpc".
    assert (HF2ra : F2 !!! Regidx Rra
                    = add_vec_int (mword_of_int (CT + 0x50) : mword 64) 4)
      by (rewrite /F2; apply upd_eq).
    (* WHICH BYTE GOES OUT: a0 is the byte itself, zero-extended -- not
       BACKSPACE (0x100 is not a byte value), so consputc takes its ordinary
       arm and stores the byte's low eight bits, which are the byte.  This
       is the arm the '\r' test did NOT take, so [echo_of c] is [c]. *)
    assert (HF2a0 : F2 !!! Regidx Ra0 = cv).
    { rewrite /F2 upd_ne; [| reg_neq]. rewrite /F1; apply upd_eq. }
    assert (Hcsb : consputc_cs (F2 !!! Regidx Ra0) = [echo_of c]).
    { rewrite HF2a0 Hcv /consputc_cs.
      rewrite /cp_backspace (ct_arg_ne256 c).
      rewrite (ct_echo_of_ne c Hc13) ct_cp_trunc ct_arg_trunc8.
      reflexivity. }
    iDestruct "Hmark" as (hg) "(%Hxg & %Hk1 & Hlgh & Harm)".
    iApply fupd_wp.
    iMod (ct_ch_full (cn_uart cn) h c hg [echo_of c] True%I
            Hxg Hends ltac:(right; left; reflexivity) Hk1
            ltac:(intros Hnil; discriminate)
            with "Huinv Hp1 Hlgh Harm [//]") as "Hch0".
    iAssert (store_chain Uart0 (cn_uart cn) (consputc_cs (F2 !!! Regidx Ra0))
               (uart_log_hi (cn_uart cn) (1/2) hg ∗
                ct_append (cn_uart cn) h c [echo_of c]
                  (length [echo_of c]) True))%I
      with "[Hch0]" as "Hch".
    { rewrite Hcsb. iExact "Hch0". }
    iModIntro.
    iApply (Consputc.wp_consputc_sconf KT1 γtx (cn_uart cn) γv F2
              (trap_res b + (K - 6))%nat
              (uart_log_hi (cn_uart cn) (1/2) hg ∗
               ct_append (cn_uart cn) h c [echo_of c]
                 (length [echo_of c]) True)%I
              (S lvl) eb false pme ({["cons"]} ∪ lks)
              ltac:(lia) ltac:(lia)
              with "Hcg Hcnt Ht Hpc Hdev Hbw Htxl Hch").
    all: try lkbelow.
    iApply wp_next_off_intro.
    iIntros (mcp) "Hcg Hcnt Hpc [%Hcpcs %Hcpra] [Hlgh Hap]". rgall.
    iEval (rewrite HF2ra) in "Hpc".
    assert (Hp054 : ret_pc (add_vec_int (mword_of_int (CT + 0x50) : mword 64) 4)
                    = (mword_of_int (CT + 0x54) : mword 64)) by pcw.
    iEval (rewrite Hp054) in "Hpc".
    assert (HthrC : forall r : mword 5, is_cs_idx r = true ->
              mcp !!! Regidx r = M !!! Regidx r).
    { intros r Hr.
      assert (N1 : r <> Rra) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      assert (N10 : r <> Ra0) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      rewrite (callee_saved_lookup Hcpcs r Hr).
      rewrite /F2 upd_ne; [| congruence]. rewrite /F1 upd_ne; [| congruence]. reflexivity. }
    assert (Hmcps1 : mcp !!! Regidx Rs1 = cv)
      by (rewrite (HthrC Rs1 ltac:(vm_compute; reflexivity)); exact Hs1).
    (* ---- +0x054/+0x058 : a4 := &cons ---- *)
    iApply (wp_auipc_s_sconf (mword_of_int (CT + 0x54)) Ra4 (mword_of_int 18 : mword 20)
              mcp (trap_res b + (K - 6))%nat false ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (cnti_054 with "Ht"). }
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    set (F3 := <[Regidx Ra4 := regval_into_reg
        (add_vec (mword_of_int (CT + 0x54) : mword 64)
           (auipc_off (mword_of_int 18 : mword 20)))]> mcp).
    assert (Hp058 : add_vec_int (mword_of_int (CT + 0x54) : mword 64) 4
                    = mword_of_int (CT + 0x58)) by pcw.
    iEval (rewrite Hp058) in "Hpc".
    iApply (wp_addi4_s_sconf (mword_of_int (CT + 0x58)) Ra4 Ra4 (mword_of_int 100 : mword 12)
              F3 (trap_res b + (K - 6))%nat false ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (cnti_058 with "Ht"). }
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    set (F4 := <[Regidx Ra4 := regval_into_reg
        (add_vec (F3 !!! Regidx Ra4) (sign_extend' 64 (mword_of_int 100 : mword 12)))]> F3).
    assert (HF4a4 : F4 !!! Regidx Ra4 = a_cons).
    { rewrite /F4 upd_eq /F3 upd_eq /a_cons. apply bv_eq; vm_compute; reflexivity. }
    assert (Hp05c : add_vec_int (mword_of_int (CT + 0x58) : mword 64) 4
                    = mword_of_int (CT + 0x5c)) by pcw.
    iEval (rewrite Hp05c) in "Hpc".
    (* ---- +0x05c lw a3,160(a4) : a3 := cons.e ---- *)
    assert (Hea : add_vec (F4 !!! Regidx Ra4)
                    (sign_extend' 64 (mword_of_int 160 : mword 12)) = a_cons_e)
      by (rewrite HF4a4; reflexivity).
    iApply (wp_lw_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (CT + 0x5c)) Ra3 Ra4 (mword_of_int 160 : mword 12)
              F4 (trap_res b + (K - 6))%nat ee false ltac:(nz) ltac:(rdok)
              with "Hcg Hpc [] [Hec]").
    { iApply (cnti_05c with "Ht"). }
    { rgall. iEval (rewrite Hea). iExact "Hec". }
    iApply wp_next_off_intro. iIntros "Hcg Hpc Hec". rgall. iEval (rewrite Hea) in "Hec".
    set (F5 := <[Regidx Ra3 := regval_into_reg (sign_extend' 64 ee)]> F4).
    assert (HF5a3 : F5 !!! Regidx Ra3 = sign_extend' 64 ee)
      by (rewrite /F5; apply upd_eq).
    assert (Hp060 : add_vec_int (mword_of_int (CT + 0x5c) : mword 64) 4
                    = mword_of_int (CT + 0x60)) by pcw.
    iEval (rewrite Hp060) in "Hpc".
    (* ---- +0x060 addiw a5,a3,1 ; +0x064 c.mv a2,a5 ---- *)
    iApply (wp_addiw_s_sconf (mword_of_int (CT + 0x60)) Ra5 Ra3 (mword_of_int 1 : mword 12)
              F5 (trap_res b + (K - 6))%nat false ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (cnti_060 with "Ht"). }
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    iEval (rewrite HF5a3 ct_addiw_inc) in "Hcg".
    set (ee1 := add_vec ee (mword_of_int 1 : mword 32)).
    set (F6 := <[Regidx Ra5 := regval_into_reg (sign_extend' 64 ee1)]> F5).
    assert (HF6a5 : F6 !!! Regidx Ra5 = sign_extend' 64 ee1)
      by (rewrite /F6; apply upd_eq).
    assert (Hp064 : add_vec_int (mword_of_int (CT + 0x60) : mword 64) 4
                    = mword_of_int (CT + 0x64)) by pcw.
    iEval (rewrite Hp064) in "Hpc".
    iApply (wp_cmv_s_sconf (mword_of_int (CT + 0x64)) Ra2 Ra5 F6
              (trap_res b + (K - 6))%nat false ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (cnti_064 with "Ht"). }
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    iEval (rewrite HF6a5 w32_zero_add) in "Hcg".
    set (F7 := <[Regidx Ra2 := regval_into_reg (sign_extend' 64 ee1)]> F6).
    assert (Hp066 : add_vec_int (mword_of_int (CT + 0x64) : mword 64) 2
                    = mword_of_int (CT + 0x66)) by pcw.
    iEval (rewrite Hp066) in "Hpc".
    (* ---- +0x066 sw a5,160(a4) : cons.e := e + 1 ---- *)
    assert (HF7a4 : F7 !!! Regidx Ra4 = a_cons).
    { rewrite /F7 upd_ne; [| reg_neq]. rewrite /F6 upd_ne; [| reg_neq].
      rewrite /F5 upd_ne; [| reg_neq]. exact HF4a4. }
    assert (HF7a5 : F7 !!! Regidx Ra5 = sign_extend' 64 ee1)
      by (rewrite /F7 upd_ne; [exact HF6a5 | reg_neq]).
    assert (HF7a3 : F7 !!! Regidx Ra3 = sign_extend' 64 ee).
    { rewrite /F7 upd_ne; [| reg_neq]. rewrite /F6 upd_ne; [| reg_neq]. exact HF5a3. }
    assert (Hea2 : add_vec (F7 !!! Regidx Ra4)
                     (sign_extend' 64 (mword_of_int 160 : mword 12)) = a_cons_e)
      by (rewrite HF7a4; reflexivity).
    iApply (wp_sw_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (CT + 0x66)) Ra5 Ra4 (mword_of_int 160 : mword 12)
              F7 (trap_res b + (K - 6))%nat ee false with "Hcg Hpc [] [Hec]").
    { iApply (cnti_066 with "Ht"). }
    { rgall. iEval (rewrite Hea2). iExact "Hec". }
    iApply wp_next_off_intro. iIntros "Hcg Hpc Hec". rgall.
    iEval (rewrite Hea2 HF7a5 trunc32_sext) in "Hec".
    assert (Hp06a : add_vec_int (mword_of_int (CT + 0x66) : mword 64) 4
                    = mword_of_int (CT + 0x6a)) by pcw.
    iEval (rewrite Hp06a) in "Hpc".
    (* ---- +0x06a andi a3,a3,127 ; +0x06e c.add a4,a4,a3 ---- *)
    destruct (ct_ring_idx ee) as (idx & Hidxlt & Hidxw).
    assert (Hwv : and_vec (F7 !!! Regidx Ra3)
                    (sign_extend' 64 (mword_of_int 127 : mword 12))
                  = (mword_of_int (Z.of_nat idx) : mword 64))
      by (rewrite HF7a3; exact Hidxw).
    iApply (wp_andi_s_sconf (mword_of_int (CT + 0x6a)) Ra3 Ra3 (mword_of_int 127 : mword 12)
              (mword_of_int (Z.of_nat idx) : mword 64) F7 (trap_res b + (K - 6))%nat false
              ltac:(nz) ltac:(rdok) Hwv with "Hcg Hpc []").
    { iApply (cnti_06a with "Ht"). }
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    set (F8 := <[Regidx Ra3 := regval_into_reg (mword_of_int (Z.of_nat idx) : mword 64)]> F7).
    assert (HF8a4 : F8 !!! Regidx Ra4 = a_cons)
      by (rewrite /F8 upd_ne; [exact HF7a4 | reg_neq]).
    assert (HF8a3 : F8 !!! Regidx Ra3 = (mword_of_int (Z.of_nat idx) : mword 64))
      by (rewrite /F8; apply upd_eq).
    assert (Hp06e : add_vec_int (mword_of_int (CT + 0x6a) : mword 64) 4
                    = mword_of_int (CT + 0x6e)) by pcw.
    iEval (rewrite Hp06e) in "Hpc".
    iApply (wp_cadd_s_sconf (mword_of_int (CT + 0x6e)) Ra4 Ra3 F8
              (trap_res b + (K - 6))%nat false ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (cnti_06e with "Ht"). }
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    iEval (rewrite HF8a4 HF8a3) in "Hcg".
    set (F9 := <[Regidx Ra4 := regval_into_reg
        (add_vec a_cons (mword_of_int (Z.of_nat idx) : mword 64))]> F8).
    assert (Hp070 : add_vec_int (mword_of_int (CT + 0x6e) : mword 64) 2
                    = mword_of_int (CT + 0x70)) by pcw.
    iEval (rewrite Hp070) in "Hpc".
    (* ---- +0x070 sb s1,24(a4) : the byte lands in the ring ---- *)
    destruct (cons_data_lookup_lt bs idx Hlenb Hidxlt) as [db Hlk].
    iDestruct (cons_data_upd bs idx db (cons_xlate c) Hlk with "Hdat")
      as "[Hbyte Hdback]".
    assert (HF9a4 : F9 !!! Regidx Ra4
                    = add_vec a_cons (mword_of_int (Z.of_nat idx) : mword 64))
      by (rewrite /F9; apply upd_eq).
    assert (HF9s1 : F9 !!! Regidx Rs1 = cv).
    { rewrite /F9 upd_ne; [| reg_neq]. rewrite /F8 upd_ne; [| reg_neq].
      rewrite /F7 upd_ne; [| reg_neq]. rewrite /F6 upd_ne; [| reg_neq].
      rewrite /F5 upd_ne; [| reg_neq]. rewrite /F4 upd_ne; [| reg_neq].
      rewrite /F3 upd_ne; [| reg_neq]. exact Hmcps1. }
    assert (Hbaddr : add_vec (F9 !!! Regidx Ra4)
                       (sign_extend' 64 (mword_of_int 24 : mword 12))
                     = pa_add a_cons (cons_buf_off + idx)).
    { rewrite HF9a4. rewrite <- (cons_byte_addr idx Hidxlt). reflexivity. }
    iApply (wp_sb_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (CT + 0x70)) Rs1 Ra4 (mword_of_int 24 : mword 12)
              F9 (trap_res b + (K - 6))%nat db false with "Hcg Hpc [] [Hbyte]").
    { iApply (cnti_070 with "Ht"). }
    { rgall. iEval (rewrite Hbaddr). iExact "Hbyte". }
    iApply wp_next_off_intro. iIntros "Hcg Hpc Hbyte". rgall.
    iEval (rewrite Hbaddr HF9s1) in "Hbyte".
    (* THE APPEND, AT THE COUPLING.  a0 arrives zero-extended, so the [sb]
       stores the byte itself; the '\r' test fell through, so [cons_xlate]
       is the identity on it, and the tag the contract handed in is filed
       in the slot [cons.e] names. *)
    assert (Hxl : trunc8 cv = cons_xlate c).
    { rewrite Hcv ct_arg_trunc8. symmetry. exact (cons_xlate_other c Hc13). }
    iEval (rewrite Hxl) in "Hbyte".
    iDestruct ("Hdback" with "Hbyte") as "Hdat".
    assert (Hidx : idx = cons_slot ee 0) by (exact (ct_idx_slot ee idx Hidxlt Hidxw)).
    iDestruct (cons_tags_upd ts idx h with "Htg Hts") as "Hts".
    assert (Hlenb1 : length (<[idx := cons_xlate c]> bs) = INPUT_BUF_SIZE)
      by (rewrite length_insert; exact Hlenb).
    assert (Hlent1 : length (<[idx := Some h]> ts) = INPUT_BUF_SIZE)
      by (rewrite length_insert; exact Hlent).
    assert (Hok1 : cons_ok rr ww ee1)
      by (rewrite /ee1; exact (cons_ok_inc_e rr ww ee Hok Hroom)).
    assert (Hrow1 : cons_row rr ee1 (<[idx := cons_xlate c]> bs)
                      (<[idx := Some h]> ts))
      by (rewrite /ee1;
          exact (cons_row_push rr ee idx bs ts h c Hlenb Hlent Hroom Hidx Hends Hrow)).
    (* THE GHOST HALF MOVES WITH THE BYTE: the editable window gains it and
       the ring's high-water mark becomes its history. *)
    iApply fupd_wp.
    iMod (ct_gh_push cn (cn_uart cn) rr ww ee bs ts idx h c hh hg
            [echo_of c] (length [echo_of c]) True%I
            eq_refl Hcne Hlenb Hlent Hok Hroom Hidx Hends Hx Hxg eq_refl
            (* K3: the store arm's plan IS its one glyph, so it closes at 1 *)
            ltac:(intros _; reflexivity) Hk1
            with "Huinv Hhi Hlgh Hap Hgh") as "(Hhi & Hlgh & Hwin & _ & Hgh)".
    iModIntro.
    (* [ee1] is [add_vec ee 1] by [set], so the window's new end needs no
       rewriting: the two are the same term. *)
    assert (Hp074 : add_vec_int (mword_of_int (CT + 0x70) : mword 64) 4
                    = mword_of_int (CT + 0x74)) by pcw.
    iEval (rewrite Hp074) in "Hpc".
    (* the register pins at [F9], threaded back to the block's entry *)
    assert (HthrF : forall r : mword 5, is_cs_idx r = true -> r <> Rs1 ->
              F9 !!! Regidx r = M !!! Regidx r).
    { intros r Hr N9.
      assert (N12 : r <> Ra2) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      assert (N13 : r <> Ra3) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      assert (N14 : r <> Ra4) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      assert (N15 : r <> Ra5) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      rewrite /F9 upd_ne; [| congruence]. rewrite /F8 upd_ne; [| congruence].
      rewrite /F7 upd_ne; [| congruence]. rewrite /F6 upd_ne; [| congruence].
      rewrite /F5 upd_ne; [| congruence]. rewrite /F4 upd_ne; [| congruence].
      rewrite /F3 upd_ne; [| congruence]. rewrite (HthrC r Hr). reflexivity. }
    (* ---- +0x074 addi a4,s1,-10 ; +0x078 c.beqz a4 : is it '\n'? ---- *)
    iApply (wp_addi4_s_sconf (mword_of_int (CT + 0x74)) Ra4 Rs1 (mword_of_int 4086 : mword 12)
              F9 (trap_res b + (K - 6))%nat false ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (cnti_074 with "Ht"). }
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    iEval (rewrite HF9s1) in "Hcg".
    set (F10 := <[Regidx Ra4 := regval_into_reg
        (add_vec cv (sign_extend' 64 (mword_of_int 4086 : mword 12)))]> F9).
    assert (HF10a4 : F10 !!! Regidx Ra4
                     = add_vec cv (sign_extend' 64 (mword_of_int 4086 : mword 12)))
      by (rewrite /F10; apply upd_eq).
    assert (HF10a2 : F10 !!! Regidx Ra2 = sign_extend' 64 ee1).
    { rewrite /F10 upd_ne; [| reg_neq]. rewrite /F9 upd_ne; [| reg_neq].
      rewrite /F8 upd_ne; [| reg_neq]. rewrite /F7; apply upd_eq. }
    assert (HthrF10 : forall r : mword 5, is_cs_idx r = true -> r <> Rs1 ->
              F10 !!! Regidx r = M !!! Regidx r).
    { intros r Hr N9.
      assert (N14 : r <> Ra4) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      rewrite /F10 upd_ne; [| congruence]. apply HthrF; assumption. }
    assert (Hp078 : add_vec_int (mword_of_int (CT + 0x74) : mword 64) 4
                    = mword_of_int (CT + 0x78)) by pcw.
    iEval (rewrite Hp078) in "Hpc".
    assert (Hcshi10 : ct_cs_hi F10 m0)
      by (exact (ct_cs_hi_thr1 F10 M m0 HthrF10 Hcs)).
    assert (Hsp10 : F10 !!! Regidx csp_rs1 = pa_stk sp0 6%nat)
      by (rewrite (HthrF10 csp_rs1 ltac:(vm_compute; reflexivity) ltac:(reg_neq)); exact Hsp).
    destruct (eq_vec (add_vec cv (sign_extend' 64 (mword_of_int 4086 : mword 12)))
                (zero_reg : mword 64)) eqn:Hnl.
    { (* '\n': the line is complete *)
      iApply (wp_cbeqz_taken_s_sconf (mword_of_int (CT + 0x78)) (mword_of_int 111 : mword 8)
                (Cregidx (mword_of_int 6)) Ra4 F10 (trap_res b + (K - 6))%nat false
                ltac:(vm_compute; reflexivity) ltac:(nz)
                ltac:(rgall; rewrite HF10a4; exact Hnl)
                ltac:(vm_compute; reflexivity) with "Hcg Hpc []").
      { iApply (cnti_078 with "Ht"). }
      iApply bi.later_intro. iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
      assert (Hj156 : add_vec (mword_of_int (CT + 0x78) : mword 64)
                        (sign_extend' 64 (sign_extend' 13
                           (concat_vec (mword_of_int 111 : mword 8) ('b"0"))))
                      = mword_of_int (CT + 0x156)) by pcw.
      iEval (rewrite Hj156) in "Hpc".
      iSpecialize ("WAKE" $! CIDq with "[%]"); [exact Hchain|].
      iApply ("WAKE" $! F10 rr ww ee1 (<[idx := cons_xlate c]> bs)
                (<[idx := Some h]> ts) with "[%] [%] [%] [%] [%] [%] [%]
                Hcg Hpc Hcnt Hpay Hlocked Hrc Hwc Hec Hdat Hts Hgh Hrest
                [Hhi] Hlgh Hwin EXIT");
        [ exact Hsp10 | exact HF10a2 | exact Hcshi10
        | exact Hlenb1 | exact Hlent1 | exact Hok1 | exact Hrow1 | ].
      rewrite /ct_hi_out. iExists (Some h). iFrame "Hhi".
      iPureIntro; exact (ohist_le_Some h). }
    (* ---- +0x07a c.addi s1,s1,-4 ; +0x07c c.beqz s1 : is it C('D')? ---- *)
    iApply (wp_cbeqz_fall_s_sconf (mword_of_int (CT + 0x78)) (mword_of_int 111 : mword 8)
              (Cregidx (mword_of_int 6)) Ra4 F10 (trap_res b + (K - 6))%nat false
              ltac:(vm_compute; reflexivity) ltac:(nz)
              ltac:(rgall; rewrite HF10a4; exact Hnl) with "Hcg Hpc []").
    { iApply (cnti_078 with "Ht"). }
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    assert (Hp07a : add_vec_int (mword_of_int (CT + 0x78) : mword 64) 2
                    = mword_of_int (CT + 0x7a)) by pcw.
    iEval (rewrite Hp07a) in "Hpc".
    assert (HF10s1 : F10 !!! Regidx Rs1 = cv)
      by (rewrite /F10 upd_ne; [exact HF9s1 | reg_neq]).
    iApply (wp_caddi_s_sconf (mword_of_int (CT + 0x7a)) Rs1 (mword_of_int 60 : mword 6)
              F10 (trap_res b + (K - 6))%nat false ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (cnti_07a with "Ht"). }
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    iEval (rewrite HF10s1) in "Hcg".
    set (F11 := <[Regidx Rs1 := regval_into_reg
        (add_vec cv (sign_extend' 64 (sign_extend' 12 (mword_of_int 60 : mword 6))))]> F10).
    assert (HF11s1 : F11 !!! Regidx Rs1
                     = add_vec cv (sign_extend' 64 (sign_extend' 12 (mword_of_int 60 : mword 6))))
      by (rewrite /F11; apply upd_eq).
    assert (HthrF11 : forall r : mword 5, is_cs_idx r = true -> r <> Rs1 ->
              F11 !!! Regidx r = M !!! Regidx r).
    { intros r Hr N9. rewrite /F11 upd_ne; [| congruence]. apply HthrF10; assumption. }
    assert (Hcshi11 : ct_cs_hi F11 m0)
      by (exact (ct_cs_hi_thr1 F11 M m0 HthrF11 Hcs)).
    assert (Hsp11 : F11 !!! Regidx csp_rs1 = pa_stk sp0 6%nat)
      by (rewrite (HthrF11 csp_rs1 ltac:(vm_compute; reflexivity) ltac:(reg_neq)); exact Hsp).
    assert (HF11a2 : F11 !!! Regidx Ra2 = sign_extend' 64 ee1)
      by (rewrite /F11 upd_ne; [exact HF10a2 | reg_neq]).
    assert (Hp07c : add_vec_int (mword_of_int (CT + 0x7a) : mword 64) 2
                    = mword_of_int (CT + 0x7c)) by pcw.
    iEval (rewrite Hp07c) in "Hpc".
    destruct (eq_vec (add_vec cv (sign_extend' 64 (sign_extend' 12 (mword_of_int 60 : mword 6))))
                (zero_reg : mword 64)) eqn:Heof.
    { (* C('D'): end of file, hand the line over *)
      iApply (wp_cbeqz_taken_s_sconf (mword_of_int (CT + 0x7c)) (mword_of_int 109 : mword 8)
                (Cregidx (mword_of_int 1)) Rs1 F11 (trap_res b + (K - 6))%nat false
                ltac:(vm_compute; reflexivity) ltac:(nz)
                ltac:(rgall; rewrite HF11s1; exact Heof)
                ltac:(vm_compute; reflexivity) with "Hcg Hpc []").
      { iApply (cnti_07c with "Ht"). }
      iApply bi.later_intro. iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
      assert (Hj156 : add_vec (mword_of_int (CT + 0x7c) : mword 64)
                        (sign_extend' 64 (sign_extend' 13
                           (concat_vec (mword_of_int 109 : mword 8) ('b"0"))))
                      = mword_of_int (CT + 0x156)) by pcw.
      iEval (rewrite Hj156) in "Hpc".
      iSpecialize ("WAKE" $! CIDq with "[%]"); [exact Hchain|].
      iApply ("WAKE" $! F11 rr ww ee1 (<[idx := cons_xlate c]> bs)
                (<[idx := Some h]> ts) with "[%] [%] [%] [%] [%] [%] [%]
                Hcg Hpc Hcnt Hpay Hlocked Hrc Hwc Hec Hdat Hts Hgh Hrest
                [Hhi] Hlgh Hwin EXIT");
        [ exact Hsp11 | exact HF11a2 | exact Hcshi11
        | exact Hlenb1 | exact Hlent1 | exact Hok1 | exact Hrow1 | ].
      rewrite /ct_hi_out. iExists (Some h). iFrame "Hhi".
      iPureIntro; exact (ohist_le_Some h). }
    (* ---- +0x07e .. +0x08c : is the ring now full? ---- *)
    iApply (wp_cbeqz_fall_s_sconf (mword_of_int (CT + 0x7c)) (mword_of_int 109 : mword 8)
              (Cregidx (mword_of_int 1)) Rs1 F11 (trap_res b + (K - 6))%nat false
              ltac:(vm_compute; reflexivity) ltac:(nz)
              ltac:(rgall; rewrite HF11s1; exact Heof) with "Hcg Hpc []").
    { iApply (cnti_07c with "Ht"). }
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    assert (Hp07e : add_vec_int (mword_of_int (CT + 0x7c) : mword 64) 2
                    = mword_of_int (CT + 0x7e)) by pcw.
    iEval (rewrite Hp07e) in "Hpc".
    iApply (wp_auipc_s_sconf (mword_of_int (CT + 0x7e)) Ra4 (mword_of_int 18 : mword 20)
              F11 (trap_res b + (K - 6))%nat false ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (cnti_07e with "Ht"). }
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    set (F12 := <[Regidx Ra4 := regval_into_reg
        (add_vec (mword_of_int (CT + 0x7e) : mword 64)
           (auipc_off (mword_of_int 18 : mword 20)))]> F11).
    assert (Hp082 : add_vec_int (mword_of_int (CT + 0x7e) : mword 64) 4
                    = mword_of_int (CT + 0x82)) by pcw.
    iEval (rewrite Hp082) in "Hpc".
    (* +0x082 lw a4,14(a4) : a4 := cons.r, off the auipc base.  The ring
       stays DESTRUCTED across this read: the fullness test below compares
       the [cons.e] this block just wrote against this very [cons.r]. *)
    assert (Hra : add_vec (F12 !!! Regidx Ra4)
                    (sign_extend' 64 (mword_of_int 210 : mword 12)) = a_cons_r).
    { rewrite /F12 upd_eq /a_cons_r /coff_of /a_cons. apply bv_eq; vm_compute; reflexivity. }
    iApply (wp_lw_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (CT + 0x82)) Ra4 Ra4 (mword_of_int 210 : mword 12)
              F12 (trap_res b + (K - 6))%nat rr false ltac:(nz) ltac:(rdok)
              with "Hcg Hpc [] [Hrc]").
    { iApply (cnti_082 with "Ht"). }
    { rgall. iEval (rewrite Hra). iExact "Hrc". }
    iApply wp_next_off_intro. iIntros "Hcg Hpc Hrc". rgall. iEval (rewrite Hra) in "Hrc".
    set (F13 := <[Regidx Ra4 := regval_into_reg (sign_extend' 64 rr)]> F12).
    assert (Hp086 : add_vec_int (mword_of_int (CT + 0x82) : mword 64) 4
                    = mword_of_int (CT + 0x86)) by pcw.
    iEval (rewrite Hp086) in "Hpc".
    (* +0x086 c.subw a5,a5,a4 *)
    assert (HF13a4 : F13 !!! Regidx Ra4 = sign_extend' 64 rr)
      by (rewrite /F13; apply upd_eq).
    assert (HF13a5 : F13 !!! Regidx Ra5 = sign_extend' 64 ee1).
    { rewrite /F13 upd_ne; [| reg_neq]. rewrite /F12 upd_ne; [| reg_neq].
      rewrite /F11 upd_ne; [| reg_neq]. rewrite /F10 upd_ne; [| reg_neq].
      rewrite /F9 upd_ne; [| reg_neq]. rewrite /F8 upd_ne; [| reg_neq]. exact HF7a5. }
    iApply (wp_csubw_s_sconf (mword_of_int (CT + 0x86)) Ra5 Ra5 Ra4 F13
              (trap_res b + (K - 6))%nat false ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (cnti_086 with "Ht"). }
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    iEval (rewrite HF13a4 HF13a5 ct_subw_sext) in "Hcg".
    set (F14 := <[Regidx Ra5 := regval_into_reg
        (sign_extend' 64 (sub_vec ee1 rr))]> F13).
    assert (Hp088 : add_vec_int (mword_of_int (CT + 0x86) : mword 64) 2
                    = mword_of_int (CT + 0x88)) by pcw.
    iEval (rewrite Hp088) in "Hpc".
    iApply (wp_li4_s_sconf (mword_of_int (CT + 0x88)) Ra4 (mword_of_int 128 : mword 12)
              (mword_of_int 128 : mword 64) F14 (trap_res b + (K - 6))%nat false
              ltac:(nz) ltac:(rdok) ltac:(pcw) with "Hcg Hpc []").
    { iApply (cnti_088 with "Ht"). }
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    set (F15 := <[Regidx Ra4 := regval_into_reg (mword_of_int 128 : mword 64)]> F14).
    assert (HF15a4 : F15 !!! Regidx Ra4 = (mword_of_int 128 : mword 64))
      by (rewrite /F15; apply upd_eq).
    assert (HF15a5 : F15 !!! Regidx Ra5 = sign_extend' 64 (sub_vec ee1 rr))
      by (rewrite /F15 upd_ne; [rewrite /F14; apply upd_eq | reg_neq]).
    assert (HF15a2 : F15 !!! Regidx Ra2 = sign_extend' 64 ee1).
    { rewrite /F15 upd_ne; [| reg_neq]. rewrite /F14 upd_ne; [| reg_neq].
      rewrite /F13 upd_ne; [| reg_neq]. rewrite /F12 upd_ne; [| reg_neq].
      exact HF11a2. }
    assert (HthrF15 : forall r : mword 5, is_cs_idx r = true -> r <> Rs1 ->
              F15 !!! Regidx r = M !!! Regidx r).
    { intros r Hr N9.
      assert (N14 : r <> Ra4) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      assert (N15 : r <> Ra5) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      rewrite /F15 upd_ne; [| congruence]. rewrite /F14 upd_ne; [| congruence].
      rewrite /F13 upd_ne; [| congruence]. rewrite /F12 upd_ne; [| congruence].
      apply HthrF11; assumption. }
    assert (Hcshi15 : ct_cs_hi F15 m0)
      by (exact (ct_cs_hi_thr1 F15 M m0 HthrF15 Hcs)).
    assert (Hsp15 : F15 !!! Regidx csp_rs1 = pa_stk sp0 6%nat)
      by (rewrite (HthrF15 csp_rs1 ltac:(vm_compute; reflexivity) ltac:(reg_neq)); exact Hsp).
    assert (Hp08c : add_vec_int (mword_of_int (CT + 0x88) : mword 64) 4
                    = mword_of_int (CT + 0x8c)) by pcw.
    iEval (rewrite Hp08c) in "Hpc".
    (* +0x08c bne a5,a4 *)
    destruct (neq_vec (sign_extend' 64 (sub_vec ee1 rr) : mword 64)
                (mword_of_int 128 : mword 64)) eqn:Hfull.
    { (* the ring is NOT full: nothing to hand over, leave *)
      iApply (wp_bne_taken_s_sconf (mword_of_int (CT + 0x8c)) (mword_of_int 120 : mword 13)
                Ra4 Ra5 F15 (trap_res b + (K - 6))%nat false ltac:(nz) ltac:(nz)
                ltac:(rgall; rewrite HF15a4 HF15a5; exact Hfull)
                ltac:(vm_compute; reflexivity) with "Hcg Hpc []").
      { iApply (cnti_08c with "Ht"). }
      iApply bi.later_intro. iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
      assert (Hj104 : add_vec (mword_of_int (CT + 0x8c) : mword 64)
                        (sign_extend' 64 (mword_of_int 120 : mword 13))
                      = mword_of_int (CT + 0x104)) by pcw.
      iEval (rewrite Hj104) in "Hpc".
      iSpecialize ("EXIT" $! CIDq with "[%]"); [exact Hchain|].
      iApply ("EXIT" $! F15 with "[%] [%] Hcg Hpc Hcnt Hpay Hlocked
                [Hrc Hwc Hec Hdat Hts Hgh] Hrest [Hhi] Hlgh Hwin").
      - exact Hsp15.
      - exact Hcshi15.
      - iApply (ct_gh_res cn rr ww ee1 (<[idx := cons_xlate c]> bs)
                  (<[idx := Some h]> ts) Hlenb1 Hlent1 Hok1 Hrow1
                  with "Hrc Hwc Hec Hdat Hts Hgh").
      - rewrite /ct_hi_out. iExists (Some h). iFrame "Hhi".
        iPureIntro; exact (ohist_le_Some h). }
    (* the ring is exactly full: hand the line over at +0x090 *)
    iApply (wp_bne_fall_s_sconf (mword_of_int (CT + 0x8c)) (mword_of_int 120 : mword 13)
              Ra4 Ra5 F15 (trap_res b + (K - 6))%nat false ltac:(nz) ltac:(nz)
              ltac:(rgall; rewrite HF15a4 HF15a5; exact Hfull) with "Hcg Hpc []").
    { iApply (cnti_08c with "Ht"). }
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    assert (Hp090 : add_vec_int (mword_of_int (CT + 0x8c) : mword 64) 4
                    = mword_of_int (CT + 0x90)) by pcw.
    iEval (rewrite Hp090) in "Hpc".
    iApply (wp_cj_s_sconf (mword_of_int (CT + 0x90))
              (sign_extend' 21 (concat_vec (mword_of_int 99 : mword 11) ('b"0")))
              F15 (trap_res b + (K - 6))%nat false
              ltac:(vm_compute; reflexivity) with "Hcg Hpc []").
    { iApply (cnti_090 with "Ht"). }
    iApply wp_next_off_intro. iApply bi.later_intro. iIntros "Hcg Hpc". rgall.
    assert (Hj156 : add_vec (mword_of_int (CT + 0x90) : mword 64)
                      (sign_extend' 64 (sign_extend' 21
                         (concat_vec (mword_of_int 99 : mword 11) ('b"0"))))
                    = mword_of_int (CT + 0x156)) by pcw.
    iEval (rewrite Hj156) in "Hpc".
    iSpecialize ("WAKE" $! CIDq with "[%]"); [exact Hchain|].
    iApply ("WAKE" $! F15 rr ww ee1 (<[idx := cons_xlate c]> bs)
              (<[idx := Some h]> ts) with "[%] [%] [%] [%] [%] [%] [%]
              Hcg Hpc Hcnt Hpay Hlocked Hrc Hwc Hec Hdat Hts Hgh Hrest
              [Hhi] Hlgh Hwin EXIT");
      [ exact Hsp15 | exact HF15a2 | exact Hcshi15
      | exact Hlenb1 | exact Hlent1 | exact Hok1 | exact Hrow1 | ].
    rewrite /ct_hi_out. iExists (Some h). iFrame "Hhi".
    iPureIntro; exact (ohist_le_Some h).
  Qed.

  (* =================================================================== *)
  (*  [DEFAULT] (+0x02c): the guard.  A NUL byte and a full ring both      *)
  (*  leave without touching anything; '\r' is rewritten to '\n' by the    *)
  (*  arm at +0x12e; everything else falls into [ct_store].                *)
  (* =================================================================== *)
  Lemma ct_dflt `{CIDq : CpuId}
      (γtx γc : gname) (γu : uart_names) (γv : disk_names)
      (cn : cons_names) (hh : option (list mobs))
      (pme : mword 64) (m0 M : regfile) (K lvl : nat) (eb : bool)
      (b : bool) (sp0 : mword 64) (cv : mword 64) (lks : gset string)
      (h : list mobs) (c : bv 8) :
    cn_uart cn = γu ->
    cn_era cn = S gen_id ->
    ohist_ext hh h ->
    M !!! Regidx csp_rs1 = pa_stk sp0 6%nat ->
    M !!! Regidx Rs1 = cv ->
    ct_cs_hi M m0 ->
    (consoleintr_stack <= K)%nat ->
    (Z.of_nat lvl + 2 < 2 ^ 31)%Z ->
    (b = false \/ pme = zero_reg -> (CIDq : CPU) = (CID : CPU)) ->
    (* same "cons" bound as the sibling arms: the default path reaches
       consputc, whose cone runs up to "uart0" (17). *)
    locks_below lks "cons" ->
    (* THE BYTE AND ITS TAG, exactly as the contract states them: a0 holds
       the ZERO-EXTENDED byte, [h] is the history it arrived at.  This
       block is where the tag stops being carried and starts being used --
       the guard at +0x044 below is what makes the append legal, so the
       two travel down to [ct_store]/[ct_cr] together. *)
    obs_ends_in Uart0 h c ->
    cv = (extend_value (n := 8) true (c : mword 8) : mword 64) ->
    kernel_text -∗
    dev_inv γu γv -∗
    (* the .data word consputc's callee LOADS its MMIO base from; it rides
       [SpecConsoleintr.console_caps], so every arm projects it rather than
       threading a new premise (persistent, no ghost name). *)
    uart_base_word Uart0 -∗
    is_txlock γtx γu -∗
    (* THE ECHO'S JUSTIFICATION, passed straight down to the two arms that
       echo ([ct_cr], [ct_store]); the two that do not -- a NUL byte, a
       full ring -- echo nothing but STILL LOG (lane CONS-IO), at [cs = []].
       That is the one arm-level change CONS-IO makes here. *)
    ct_pay γu h c -∗
    riscv_rx_tag h -∗
    sie_cap_gpr KT1 M (trap_res b + (K - 6))%nat false pme -∗
    pc_is (mword_of_int (CT + 0x2c)) -∗
    cpu_own (S lvl) eb pme false ({["cons"]} ∪ lks) -∗
    arm_pay KT1 lvl eb pme -∗
    locked γc cpu_id -∗
    cons_res cn -∗
    uart_rx_hi γu (1/2) hh -∗
    ct_mark γu h -∗
    ct_rest sp0 -∗
    ct_wake_prop (CID0 := CID) γu h c cn γc pme m0 K lvl eb b sp0 lks -∗
    ct_exit_prop (CID0 := CID) γu h c cn γc pme m0 K lvl eb b sp0 lks -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Hcnu Hcne Hx Hsp Hs1 Hcs HK Hlvl Hchain Hbelow Hends Hcv.
    iIntros "#Ht #Hdev #Hbw #Htxl #Hp1 #Htg Hcg Hpc Hcnt Hpay Hlocked
             Hres Hhi Hmark Hrest WAKE EXIT".
    (* the console port's own invariant, which the two drop arms' appends
       open (lane CONS-IO, milestone B, ruling F2). *)
    iPoseProof (dev_inv_uart with "Hdev") as "#Huinv".
    (* THE MARK GOES BACK UNMOVED ON EVERY ARM THAT DOES NOT STORE -- a NUL
       byte and a full ring -- and it is already at or before this byte.  It
       is built IN those two arms and not here: the half is exclusive, and
       the two arms that DO store hand it to [ct_cr]/[ct_store], which move
       it to the byte they file. *)
    (* ---- +0x02c c.beqz s1 : [c != 0] ---- *)
    destruct (eq_vec (cv : mword 64) (zero_reg : mword 64)) eqn:Hnul.
    { iApply (wp_cbeqz_taken_s_sconf (mword_of_int (CT + 0x2c)) (mword_of_int 108 : mword 8)
                (Cregidx (mword_of_int 1)) Rs1 M (trap_res b + (K - 6))%nat false
                ltac:(vm_compute; reflexivity) ltac:(nz)
                ltac:(rgall; rewrite Hs1; exact Hnul)
                ltac:(vm_compute; reflexivity) with "Hcg Hpc []").
    { iApply (cnti_02c with "Ht"). }
      iApply bi.later_intro. iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
      assert (Hj104 : add_vec (mword_of_int (CT + 0x2c) : mword 64)
                        (sign_extend' 64 (sign_extend' 13
                           (concat_vec (mword_of_int 108 : mword 8) ('b"0"))))
                      = mword_of_int (CT + 0x104)) by pcw.
      iEval (rewrite Hj104) in "Hpc".
      iSpecialize ("EXIT" $! CIDq with "[%]"); [exact Hchain|].
      (* A NUL BYTE IS AN ACCEPTED BYTE, AND IT IS LOGGED (lane CONS-IO,
         milestone B): [cs = []], the ring does not move, and the arm files
         the entry itself -- EXIT no longer fires anything. *)
      iApply fupd_wp.
      iDestruct "Hmark" as (hg) "(%Hxg & %Hk1 & Hlgh & Harm)".
      iMod (ct_append_nil γu h c hg emp%I Hxg Hends Hk1
              with "Huinv Hp1 Hlgh Harm []") as "(Hlgh & _ & Hap)".
      { (* K2: the switch's [c.beqz] decided the byte is NUL *)
        iLeft. iSplitR; [| done]. iPureIntro. intros _. left.
        exact (ct_arg_nul c ltac:(rewrite <- Hcv; exact Hnul)). }
      iMod (ct_res_drop cn γu h c hg [] 0%nat True%I Hcnu Hends Hxg eq_refl
              ltac:(intros Hnil; discriminate) Hk1
              with "Huinv Hlgh Hap Hres") as "(Hlgh & Hwin & _ & Hres)".
      iModIntro.
      iApply ("EXIT" $! M with "[%] [%] Hcg Hpc Hcnt Hpay Hlocked Hres Hrest
                [Hhi] Hlgh Hwin");
        [ exact Hsp | exact Hcs |].
      rewrite /ct_hi_out. iExists hh. iFrame "Hhi".
      iPureIntro; exact (ohist_le_of_ext hh h Hx). }
    iApply (wp_cbeqz_fall_s_sconf (mword_of_int (CT + 0x2c)) (mword_of_int 108 : mword 8)
              (Cregidx (mword_of_int 1)) Rs1 M (trap_res b + (K - 6))%nat false
              ltac:(vm_compute; reflexivity) ltac:(nz)
              ltac:(rgall; rewrite Hs1; exact Hnul) with "Hcg Hpc []").
    { iApply (cnti_02c with "Ht"). }
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    assert (Hp02e : add_vec_int (mword_of_int (CT + 0x2c) : mword 64) 2
                    = mword_of_int (CT + 0x2e)) by pcw.
    iEval (rewrite Hp02e) in "Hpc".
    (* ---- +0x02e/+0x032 : a4 := &cons ---- *)
    iApply (wp_auipc_s_sconf (mword_of_int (CT + 0x2e)) Ra4 (mword_of_int 18 : mword 20)
              M (trap_res b + (K - 6))%nat false ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (cnti_02e with "Ht"). }
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    set (G1 := <[Regidx Ra4 := regval_into_reg
        (add_vec (mword_of_int (CT + 0x2e) : mword 64)
           (auipc_off (mword_of_int 18 : mword 20)))]> M).
    assert (Hp032 : add_vec_int (mword_of_int (CT + 0x2e) : mword 64) 4
                    = mword_of_int (CT + 0x32)) by pcw.
    iEval (rewrite Hp032) in "Hpc".
    iApply (wp_addi4_s_sconf (mword_of_int (CT + 0x32)) Ra4 Ra4 (mword_of_int 138 : mword 12)
              G1 (trap_res b + (K - 6))%nat false ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (cnti_032 with "Ht"). }
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    set (G2 := <[Regidx Ra4 := regval_into_reg
        (add_vec (G1 !!! Regidx Ra4) (sign_extend' 64 (mword_of_int 138 : mword 12)))]> G1).
    assert (HG2a4 : G2 !!! Regidx Ra4 = a_cons).
    { rewrite /G2 upd_eq /G1 upd_eq /a_cons. apply bv_eq; vm_compute; reflexivity. }
    assert (Hp036 : add_vec_int (mword_of_int (CT + 0x32) : mword 64) 4
                    = mword_of_int (CT + 0x36)) by pcw.
    iEval (rewrite Hp036) in "Hpc".
    (* ---- +0x036 lw a5,160(a4) ; +0x03a lw a4,152(a4) ---- *)
    (* the ring stays DESTRUCTED from here to the two arms that append:
       the guard at +0x044 is a statement about THESE [cons.e] and
       [cons.r], and [ConsoleInv.cons_res]'s existential would hide it. *)
    iDestruct (ct_res_gh cn with "Hres") as (rr ww ee bs ts)
      "(%Hlenb & %Hlent & %Hok & %Hrow & Hrc & Hwc & Hec & Hdat & Hts & Hgh)".
    assert (Hea : add_vec (G2 !!! Regidx Ra4)
                    (sign_extend' 64 (mword_of_int 160 : mword 12)) = a_cons_e)
      by (rewrite HG2a4; reflexivity).
    iApply (wp_lw_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (CT + 0x36)) Ra5 Ra4 (mword_of_int 160 : mword 12)
              G2 (trap_res b + (K - 6))%nat ee false ltac:(nz) ltac:(rdok)
              with "Hcg Hpc [] [Hec]").
    { iApply (cnti_036 with "Ht"). }
    { rgall. iEval (rewrite Hea). iExact "Hec". }
    iApply wp_next_off_intro. iIntros "Hcg Hpc Hec". rgall. iEval (rewrite Hea) in "Hec".
    set (G3 := <[Regidx Ra5 := regval_into_reg (sign_extend' 64 ee)]> G2).
    assert (HG3a4 : G3 !!! Regidx Ra4 = a_cons)
      by (rewrite /G3 upd_ne; [exact HG2a4 | reg_neq]).
    assert (Hra : add_vec (G3 !!! Regidx Ra4)
                    (sign_extend' 64 (mword_of_int 152 : mword 12)) = a_cons_r)
      by (rewrite HG3a4; reflexivity).
    assert (Hp03a : add_vec_int (mword_of_int (CT + 0x36) : mword 64) 4
                    = mword_of_int (CT + 0x3a)) by pcw.
    iEval (rewrite Hp03a) in "Hpc".
    iApply (wp_lw_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (CT + 0x3a)) Ra4 Ra4 (mword_of_int 152 : mword 12)
              G3 (trap_res b + (K - 6))%nat rr false ltac:(nz) ltac:(rdok)
              with "Hcg Hpc [] [Hrc]").
    { iApply (cnti_03a with "Ht"). }
    { rgall. iEval (rewrite Hra). iExact "Hrc". }
    iApply wp_next_off_intro. iIntros "Hcg Hpc Hrc". rgall. iEval (rewrite Hra) in "Hrc".
    set (G4 := <[Regidx Ra4 := regval_into_reg (sign_extend' 64 rr)]> G3).
    assert (Hp03e : add_vec_int (mword_of_int (CT + 0x3a) : mword 64) 4
                    = mword_of_int (CT + 0x3e)) by pcw.
    iEval (rewrite Hp03e) in "Hpc".
    (* ---- +0x03e c.subw a5,a5,a4 ; +0x040 li a4,127 ; +0x044 bltu ---- *)
    assert (HG4a4 : G4 !!! Regidx Ra4 = sign_extend' 64 rr)
      by (rewrite /G4; apply upd_eq).
    assert (HG4a5 : G4 !!! Regidx Ra5 = sign_extend' 64 ee).
    { rewrite /G4 upd_ne; [| reg_neq]. rewrite /G3; apply upd_eq. }
    iApply (wp_csubw_s_sconf (mword_of_int (CT + 0x3e)) Ra5 Ra5 Ra4 G4
              (trap_res b + (K - 6))%nat false ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (cnti_03e with "Ht"). }
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    iEval (rewrite HG4a4 HG4a5 ct_subw_sext) in "Hcg".
    set (G5 := <[Regidx Ra5 := regval_into_reg (sign_extend' 64 (sub_vec ee rr))]> G4).
    assert (Hp040 : add_vec_int (mword_of_int (CT + 0x3e) : mword 64) 2
                    = mword_of_int (CT + 0x40)) by pcw.
    iEval (rewrite Hp040) in "Hpc".
    iApply (wp_li4_s_sconf (mword_of_int (CT + 0x40)) Ra4 (mword_of_int 127 : mword 12)
              (mword_of_int 127 : mword 64) G5 (trap_res b + (K - 6))%nat false
              ltac:(nz) ltac:(rdok) ltac:(pcw) with "Hcg Hpc []").
    { iApply (cnti_040 with "Ht"). }
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    set (G6 := <[Regidx Ra4 := regval_into_reg (mword_of_int 127 : mword 64)]> G5).
    assert (HG6a4 : G6 !!! Regidx Ra4 = (mword_of_int 127 : mword 64))
      by (rewrite /G6; apply upd_eq).
    assert (HG6a5 : G6 !!! Regidx Ra5 = sign_extend' 64 (sub_vec ee rr))
      by (rewrite /G6 upd_ne; [rewrite /G5; apply upd_eq | reg_neq]).
    assert (HthrG6 : forall r : mword 5, is_cs_idx r = true ->
              G6 !!! Regidx r = M !!! Regidx r).
    { intros r Hr.
      assert (N14 : r <> Ra4) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      assert (N15 : r <> Ra5) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      rewrite /G6 upd_ne; [| congruence]. rewrite /G5 upd_ne; [| congruence].
      rewrite /G4 upd_ne; [| congruence]. rewrite /G3 upd_ne; [| congruence].
      rewrite /G2 upd_ne; [| congruence]. rewrite /G1 upd_ne; [| congruence]. reflexivity. }
    assert (Hp044 : add_vec_int (mword_of_int (CT + 0x40) : mword 64) 4
                    = mword_of_int (CT + 0x44)) by pcw.
    iEval (rewrite Hp044) in "Hpc".
    destruct (zopz0zI_u (mword_of_int 127 : mword 64)
                (sign_extend' 64 (sub_vec ee rr) : mword 64)) eqn:Hgd.
    { (* the ring has no room: leave *)
      iApply (wp_bltu_taken_s_sconf (mword_of_int (CT + 0x44)) (mword_of_int 192 : mword 13)
                Ra5 Ra4 G6 (trap_res b + (K - 6))%nat false ltac:(nz) ltac:(nz)
                ltac:(rgall; rewrite HG6a4 HG6a5; exact Hgd)
                ltac:(vm_compute; reflexivity) with "Hcg Hpc []").
      { iApply (cnti_044 with "Ht"). }
      iApply bi.later_intro. iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
      assert (Hj104 : add_vec (mword_of_int (CT + 0x44) : mword 64)
                        (sign_extend' 64 (mword_of_int 192 : mword 13))
                      = mword_of_int (CT + 0x104)) by pcw.
      iEval (rewrite Hj104) in "Hpc".
      iSpecialize ("EXIT" $! CIDq with "[%]"); [exact Hchain|].
      (* A FULL RING DROPS THE BYTE, AND LOGS THE DROP (lane CONS-IO,
         milestone B): this is the arm that fired nothing at all before
         milestone A, and it now files [cs = []] itself. *)
      iApply fupd_wp.
      iDestruct "Hmark" as (hg) "(%Hxg & %Hk1 & Hlgh & Harm)".
      (* K2 (relax-d2): THE RING IS FULL, and that is the one drop reason
         the switch's guard cannot hand over.  The ring's log mirror and its
         delivered count go out as the payment and the wand brings the ring
         straight back -- an open moves neither. *)
      assert (Hfull : (Z.of_nat INPUT_BUF_SIZE
                       <= bv_unsigned (sub_vec ee rr))%Z)
        by (exact (ct_nofit (sub_vec ee rr) (proj2 Hok) Hgd)).
      iDestruct (ct_gh_full_log cn rr ww ee bs ts Hok Hfull with "Hgh")
        as (L0k ndlk) "(%Hcntk & Hlmk & Hdck & Hback)".
      iMod (ct_append_nil γu h c hg
              (ct_gh cn None rr ww ee bs ts) Hxg Hends Hk1
              with "Huinv Hp1 Hlgh Harm [Hlmk Hdck Hback]")
        as "(Hlgh & Hgh & Hap)".
      { rewrite <- Hcnu. iRight. iExists L0k, ndlk.
        iSplitR; [by iPureIntro |].
        iSplitL "Hlmk"; [rewrite /uart_logm; iExact "Hlmk" |].
        iSplitL "Hdck"; [rewrite /uart_dlcnt; iExact "Hdck" |].
        iIntros "Hlm Hdc". iApply ("Hback" with "[Hlm] [Hdc]");
          [ rewrite /cons_logm; iExact "Hlm"
          | rewrite /cons_dlcnt; iExact "Hdc" ]. }
      iMod (ct_gh_drop cn γu rr ww ee bs ts h c hg [] 0%nat True%I
              Hcnu Hends Hxg eq_refl ltac:(intros Hnil; discriminate) Hk1
              with "Huinv Hlgh Hap Hgh") as "(Hlgh & Hwin & _ & Hgh)".
      iModIntro.
      iApply ("EXIT" $! G6 with "[%] [%] Hcg Hpc Hcnt Hpay Hlocked
                [Hrc Hwc Hec Hdat Hts Hgh] Hrest [Hhi] Hlgh Hwin").
      - rewrite (HthrG6 csp_rs1 ltac:(vm_compute; reflexivity)). exact Hsp.
      - exact (ct_cs_hi_thr G6 M m0 HthrG6 Hcs).
      - iApply (ct_gh_res cn rr ww ee bs ts Hlenb Hlent Hok Hrow
                  with "Hrc Hwc Hec Hdat Hts Hgh").
      - rewrite /ct_hi_out. iExists hh. iFrame "Hhi".
        iPureIntro; exact (ohist_le_of_ext hh h Hx). }
    iApply (wp_bltu_fall_s_sconf (mword_of_int (CT + 0x44)) (mword_of_int 192 : mword 13)
              Ra5 Ra4 G6 (trap_res b + (K - 6))%nat false ltac:(nz) ltac:(nz)
              ltac:(rgall; rewrite HG6a4 HG6a5; exact Hgd) with "Hcg Hpc []").
    { iApply (cnti_044 with "Ht"). }
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    (* THE ROOM GUARD, as the coupling states it.  [bltu 127, e-r] NOT
       taken is [cons.e - cons.r <= 127], read off the 32-bit difference
       the [c.subw] at +0x03e computed -- and that is exactly what
       [ConsoleInv.cons_ok_inc_e] and [cons_row_push] ask of the append. *)
    assert (Hroom : (bv_unsigned (sub_vec ee rr) < Z.of_nat INPUT_BUF_SIZE)%Z)
      by (exact (ct_room (sub_vec ee rr) Hgd)).
    assert (Hp048 : add_vec_int (mword_of_int (CT + 0x44) : mword 64) 4
                    = mword_of_int (CT + 0x48)) by pcw.
    iEval (rewrite Hp048) in "Hpc".
    (* ---- +0x048 c.li a5,13 ; +0x04a beq s1,a5 : the '\r' rewrite ---- *)
    iApply (wp_cli_s_sconf (mword_of_int (CT + 0x48)) Ra5 (mword_of_int 13 : mword 6)
              (mword_of_int 13 : mword 64) G6 (trap_res b + (K - 6))%nat false
              ltac:(nz) ltac:(rdok) ltac:(pcw) with "Hcg Hpc []").
    { iApply (cnti_048 with "Ht"). }
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    set (G7 := <[Regidx Ra5 := regval_into_reg (mword_of_int 13 : mword 64)]> G6).
    assert (HG7a5 : G7 !!! Regidx Ra5 = (mword_of_int 13 : mword 64))
      by (rewrite /G7; apply upd_eq).
    assert (HthrG7 : forall r : mword 5, is_cs_idx r = true ->
              G7 !!! Regidx r = M !!! Regidx r).
    { intros r Hr.
      assert (N15 : r <> Ra5) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      rewrite /G7 upd_ne; [| congruence]. apply HthrG6; exact Hr. }
    assert (HG7s1 : G7 !!! Regidx Rs1 = cv)
      by (rewrite (HthrG7 Rs1 ltac:(vm_compute; reflexivity)); exact Hs1).
    assert (HG7sp : G7 !!! Regidx csp_rs1 = pa_stk sp0 6%nat)
      by (rewrite (HthrG7 csp_rs1 ltac:(vm_compute; reflexivity)); exact Hsp).
    assert (Hp04a : add_vec_int (mword_of_int (CT + 0x48) : mword 64) 2
                    = mword_of_int (CT + 0x4a)) by pcw.
    iEval (rewrite Hp04a) in "Hpc".
    destruct (eq_vec (cv : mword 64) (mword_of_int 13 : mword 64)) eqn:Hcr.
    { iApply (wp_beq_taken_s_sconf (mword_of_int (CT + 0x4a)) (mword_of_int 228 : mword 13)
                Ra5 Rs1 G7 (trap_res b + (K - 6))%nat false ltac:(nz) ltac:(nz)
                ltac:(rgall; rewrite HG7s1 HG7a5; exact Hcr)
                ltac:(vm_compute; reflexivity) with "Hcg Hpc []").
    { iApply (cnti_04a with "Ht"). }
      iApply bi.later_intro. iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
      assert (Hj12e : add_vec (mword_of_int (CT + 0x4a) : mword 64)
                        (sign_extend' 64 (mword_of_int 228 : mword 13))
                      = mword_of_int (CT + 0x12e)) by pcw.
      iEval (rewrite Hj12e) in "Hpc".
      iApply (ct_cr (CIDq := CIDq) γtx γc γu γv cn hh pme m0 G7 K lvl eb b sp0
                lks rr ww ee bs ts h c Hcnu Hcne Hx
                HG7sp (ct_cs_hi_thr G7 M m0 HthrG7 Hcs) HK Hlvl Hchain Hbelow
                Hlenb Hlent Hok Hrow Hroom Hends
                ltac:(exact (ct_arg_eq13 c ltac:(rewrite <- Hcv; exact Hcr)))
                with "Ht Hdev Hbw Htxl Hp1 Htg Hcg Hpc Hcnt Hpay Hlocked
                      Hrc Hwc Hec Hdat Hts Hgh Hhi Hmark Hrest WAKE EXIT"). }
    iApply (wp_beq_fall_s_sconf (mword_of_int (CT + 0x4a)) (mword_of_int 228 : mword 13)
              Ra5 Rs1 G7 (trap_res b + (K - 6))%nat false ltac:(nz) ltac:(nz)
              ltac:(rgall; rewrite HG7s1 HG7a5; exact Hcr) with "Hcg Hpc []").
    { iApply (cnti_04a with "Ht"). }
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    assert (Hp04e : add_vec_int (mword_of_int (CT + 0x4a) : mword 64) 4
                    = mword_of_int (CT + 0x4e)) by pcw.
    iEval (rewrite Hp04e) in "Hpc".
    iApply (ct_store (CIDq := CIDq) γtx γc γu γv cn hh pme m0 G7 K lvl eb b sp0
              cv lks rr ww ee bs ts h c Hcnu Hcne Hx
              HG7sp HG7s1 (ct_cs_hi_thr G7 M m0 HthrG7 Hcs) HK Hlvl Hchain Hbelow
              Hlenb Hlent Hok Hrow Hroom Hends Hcv
              ltac:(exact (ct_arg_ne13 c ltac:(rewrite <- Hcv; exact Hcr)))
              with "Ht Hdev Hbw Htxl Hp1 Htg Hcg Hpc Hcnt Hpay Hlocked
                    Hrc Hwc Hec Hdat Hts Hgh Hhi Hmark Hrest WAKE EXIT").
  Qed.

  (* =================================================================== *)
  (*  THE WHOLE FUNCTION.                                                 *)
  (*                                                                      *)
  (*  Prologue, [acquire(&cons.lock)], and the four-way [beq] chain that   *)
  (*  is xv6's [switch (c)].  Nothing here needs arithmetic: the contract  *)
  (*  promises NOTHING about which byte arrived, so every arm is a plain   *)
  (*  [destruct] on the raw comparison of the symbolic character.          *)
  (* =================================================================== *)
  Lemma wp_consoleintr_sconf (γu : uart_names) (γv : disk_names)
      (m : regfile) (γs : list gname)
      (pme : mword 64) (lvl K : nat) (eb : bool) (b : bool) (lks : gset string)
      (hb : list mobs) (cb : bv 8) (hh hg : option (list mobs))
    : wp_consoleintr_sconf_body γu γv m γs pme lvl K eb b lks hb cb hh hg.
  Proof using .
    cbv beta delta [wp_consoleintr_sconf_body].
    intros rettgt HK Hcva Hends Hbts Hx Hxg Hshb Hnext Hlen Hlvl Hbelow.
    iIntros "Hcg Hcnt #Ht Hpc #Hpinv #Hdev #Hcaps #Htg #Hlbh #Hwlb Hhi Hlgh
             Hwin Hcont".
    iDestruct "Hcaps" as (γtx γc cn)
      "(#Htxl & #Hlk & %Hcnu & %Hcne & #Hsh & #Hinitd & #Hwords)".
    iPoseProof (dev_inv_uart with "Hdev") as "#Huinv".
    (* THE LOG'S MARK, as the arms carry it (lane CONS-IO) -- and the ECHO
       WINDOW TOKEN beside it (milestone F): the arms spend it at the shift
       and their own append hands it back, so it rides the same bundle. *)
    iAssert (ct_mark γu hb) with "[Hlgh Hwin]" as "Hmark".
    { iExists hg. iFrame "Hlgh Hwin". iPureIntro; split;
        [exact Hxg | exact Hnext]. }
    (* THE ECHO'S JUSTIFICATION FOR THIS CALL'S BYTE (lane OUT-FUPD): the
       application's boot-fixed shift with this call's three facts -- the
       byte's arrival history, its tag and the monotone bound on it --
       already discharged.  Every arm below spends it. *)
    iPoseProof (ct_mk_pay γu hb cb Hends Hbts Hshb
                  with "Hsh Htg Hlbh Hwlb") as "#Hpy".
    (* the console's own `.data` base word, out of the array's row: the
       bundle carries all four words as one ([SpecUartPutc.uarts_words]) and
       every arm below wants just this one. *)
    iPoseProof (uarts_words_base Uart0 with "Hwords") as "#Hbw".
    (* the byte and its history are the contract's own parameters now: the
       arm that files the byte in the ring is the default arm's store. *)
    iDestruct (cpu_own_eb_agree with "Hcg Hcnt") as %Hbm.
    set (sp0 := (m !!! Regidx csp_rs1 : mword 64)).
    assert (Hspm : m !!! Regidx csp_rs1 = sp0) by reflexivity.
    set (cv := (m !!! Regidx Ra0 : mword 64)).
    assert (Hcv : cv = (extend_value (n := 8) true (cb : mword 8) : mword 64))
      by (rewrite /cv; exact Hcva).
    (* ================= PROLOGUE: the six-slot frame ==================== *)
    assert (Hpush : add_vec (m !!! Regidx csp_rs1)
                      (sign_extend' 64 (caddi16sp_imm (mword_of_int 61 : mword 6)))
                    = pa_stk (m !!! Regidx csp_rs1) 6%nat).
    { unfold pa_stk, add_vec_int. apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    iApply (wp_caddi16sp_push_s_sconf (mword_of_int CT) (mword_of_int 61 : mword 6) m K 6%nat b
              ltac:(lia) Hpush with "Hcg Hpc []").
    { iApply (cnti_000 with "Ht"). }
    iIntros (CIDp1 Hsp1) "Hcg Hframe Hpc". rgall.
    iEval (rewrite Hspm) in "Hframe".
    set (P0 := <[Regidx csp_rs1 := regval_into_reg
        (add_vec (m !!! Regidx csp_rs1)
           (sign_extend' 64 (caddi16sp_imm (mword_of_int 61 : mword 6))))]> m).
    assert (HP0sp : P0 !!! Regidx csp_rs1 = pa_stk sp0 6%nat)
      by (rewrite /P0 upd_eq; rewrite Hpush Hspm; reflexivity).
    assert (Hp002 : add_vec_int (mword_of_int CT : mword 64) 2
                    = mword_of_int (CT + 0x2)) by pcw.
    iEval (rewrite Hp002) in "Hpc".
    assert (Hb1 : add_vec (pa_stk sp0 6%nat)
                    (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000")))
                  = pa_stk sp0 1%nat) by (apply ct_slot_bridge; pcw).
    assert (Hb2 : add_vec (pa_stk sp0 6%nat)
                    (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000")))
                  = pa_stk sp0 2%nat) by (apply ct_slot_bridge; pcw).
    assert (Hb3 : add_vec (pa_stk sp0 6%nat)
                    (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000")))
                  = pa_stk sp0 3%nat) by (apply ct_slot_bridge; pcw).
    iEval (rewrite (stack_own_slots (KTR := KT1)); cbn [seq]) in "Hframe".
    iDestruct "Hframe" as "(Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & _)".
    iDestruct "Z1" as (u1) "Hf1". iDestruct "Z2" as (u2) "Hf2".
    iDestruct "Z3" as (u3) "Hf3".
    iAssert (ct_rest sp0) with "[Z4 Z5 Z6]" as "Hrest".
    { rewrite /ct_rest. iFrame "Z4 Z5 Z6". }
    (* ---- +0x002/+0x004/+0x006: save ra, s0, s1 ---- *)
    iApply (wp_csdsp_s_sconf (mword_of_int (CT + 0x2)) (mword_of_int 5 : mword 6) Rra
              P0 (K - 6)%nat u1 b with "Hcg Hpc [] [Hf1]").
    { iApply (cnti_002 with "Ht"). }
    { iEval (rewrite HP0sp Hb1). iExact "Hf1". }
    iIntros (CIDp2 Hsp2) "Hcg Hpc Hf1". rgall. iEval (rewrite HP0sp Hb1) in "Hf1".
    assert (HP0ra : P0 !!! Regidx Rra = m !!! Regidx Rra)
      by (rewrite /P0 upd_ne; [reflexivity | reg_neq]).
    iEval (rewrite HP0ra) in "Hf1".
    assert (Hp004 : add_vec_int (mword_of_int (CT + 0x2) : mword 64) 2
                    = mword_of_int (CT + 0x4)) by pcw.
    iEval (rewrite Hp004) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (CT + 0x4)) (mword_of_int 4 : mword 6) Rs0
              P0 (K - 6)%nat u2 b with "Hcg Hpc [] [Hf2]").
    { iApply (cnti_004 with "Ht"). }
    { iEval (rewrite HP0sp Hb2). iExact "Hf2". }
    iIntros (CIDp3 Hsp3) "Hcg Hpc Hf2". rgall. iEval (rewrite HP0sp Hb2) in "Hf2".
    assert (HP0s0 : P0 !!! Regidx Rs0 = m !!! Regidx Rs0)
      by (rewrite /P0 upd_ne; [reflexivity | reg_neq]).
    iEval (rewrite HP0s0) in "Hf2".
    assert (Hp006 : add_vec_int (mword_of_int (CT + 0x4) : mword 64) 2
                    = mword_of_int (CT + 0x6)) by pcw.
    iEval (rewrite Hp006) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (CT + 0x6)) (mword_of_int 3 : mword 6) Rs1
              P0 (K - 6)%nat u3 b with "Hcg Hpc [] [Hf3]").
    { iApply (cnti_006 with "Ht"). }
    { iEval (rewrite HP0sp Hb3). iExact "Hf3". }
    iIntros (CIDp4 Hsp4) "Hcg Hpc Hf3". rgall. iEval (rewrite HP0sp Hb3) in "Hf3".
    assert (HP0s1 : P0 !!! Regidx Rs1 = m !!! Regidx Rs1)
      by (rewrite /P0 upd_ne; [reflexivity | reg_neq]).
    iEval (rewrite HP0s1) in "Hf3".
    iAssert (ct_saved sp0 m) with "[Hf1 Hf2 Hf3]" as "Hsaved".
    { rewrite /ct_saved. iFrame "Hf1 Hf2 Hf3". }
    assert (Hp008 : add_vec_int (mword_of_int (CT + 0x6) : mword 64) 2
                    = mword_of_int (CT + 0x8)) by pcw.
    iEval (rewrite Hp008) in "Hpc".
    (* ---- +0x008 c.addi4spn s0,sp,48 : the frame pointer ---- *)
    assert (Hs0v : add_vec (pa_stk sp0 6%nat)
                     (sign_extend' 64 (caddi4spn_imm (mword_of_int 12 : mword 8))) = sp0).
    { unfold pa_stk, add_vec_int. rewrite add_vec_assoc.
      rewrite (_ : add_vec (mword_of_int (- (8 * Z.of_nat 6%nat)) : mword 64)
                     (sign_extend' 64 (caddi4spn_imm (mword_of_int 12 : mword 8)))
                   = (mword_of_int 0 : mword 64)); [| pcw].
      apply bv_add_0_r. vm_compute. reflexivity. }
    iApply (wp_caddi4spn_s_sconf (mword_of_int (CT + 0x8)) (Cregidx (mword_of_int 0))
              (mword_of_int 12 : mword 8) Rs0 P0 (K - 6)%nat b
              ltac:(vm_compute; reflexivity) ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (cnti_008 with "Ht"). }
    iIntros (CIDp5 Hsp5) "Hcg Hpc". rgall.
    iEval (rewrite HP0sp Hs0v) in "Hcg".
    set (P1 := <[Regidx Rs0 := regval_into_reg sp0]> P0).
    assert (Hp00a : add_vec_int (mword_of_int (CT + 0x8) : mword 64) 2
                    = mword_of_int (CT + 0xa)) by pcw.
    iEval (rewrite Hp00a) in "Hpc".
    (* ---- +0x00a c.mv s1,a0 : s1 holds the character for the whole body ---- *)
    assert (HP1a0 : P1 !!! Regidx Ra0 = cv).
    { rewrite /P1 upd_ne; [| reg_neq]. rewrite /P0 upd_ne; [reflexivity | reg_neq]. }
    iApply (wp_cmv_s_sconf (mword_of_int (CT + 0xa)) Rs1 Ra0 P1 (K - 6)%nat b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (cnti_00a with "Ht"). }
    iIntros (CIDp6 Hsp6) "Hcg Hpc". rgall.
    iEval (rewrite HP1a0 w32_zero_add) in "Hcg".
    set (P2 := <[Regidx Rs1 := regval_into_reg cv]> P1).
    assert (Hp00c : add_vec_int (mword_of_int (CT + 0xa) : mword 64) 2
                    = mword_of_int (CT + 0xc)) by pcw.
    iEval (rewrite Hp00c) in "Hpc".
    (* ---- +0x00c/+0x010 : a0 := &cons ; +0x014 jal acquire ---- *)
    iApply (wp_auipc_s_sconf (mword_of_int (CT + 0xc)) Ra0 (mword_of_int 18 : mword 20)
              P2 (K - 6)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (cnti_00c with "Ht"). }
    iIntros (CIDp7 Hsp7) "Hcg Hpc". rgall.
    set (P3 := <[Regidx Ra0 := regval_into_reg
        (add_vec (mword_of_int (CT + 0xc) : mword 64)
           (auipc_off (mword_of_int 18 : mword 20)))]> P2).
    assert (Hp010 : add_vec_int (mword_of_int (CT + 0xc) : mword 64) 4
                    = mword_of_int (CT + 0x10)) by pcw.
    iEval (rewrite Hp010) in "Hpc".
    iApply (wp_addi4_s_sconf (mword_of_int (CT + 0x10)) Ra0 Ra0 (mword_of_int 172 : mword 12)
              P3 (K - 6)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (cnti_010 with "Ht"). }
    iIntros (CIDp8 Hsp8) "Hcg Hpc". rgall.
    set (P4 := <[Regidx Ra0 := regval_into_reg
        (add_vec (P3 !!! Regidx Ra0) (sign_extend' 64 (mword_of_int 172 : mword 12)))]> P3).
    assert (HP4a0 : P4 !!! Regidx Ra0 = a_cons).
    { rewrite /P4 upd_eq /P3 upd_eq /a_cons. apply bv_eq; vm_compute; reflexivity. }
    assert (Hp014 : add_vec_int (mword_of_int (CT + 0x10) : mword 64) 4
                    = mword_of_int (CT + 0x14)) by pcw.
    iEval (rewrite Hp014) in "Hpc".
    iApply (wp_jal_s_sconf (mword_of_int (CT + 0x14)) Rra (mword_of_int 2428 : mword 21)
              P4 (K - 6)%nat b ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (cnti_014 with "Ht"). }
    iIntros (CIDp9 Hsp9) "Hcg Hpc". rgall.
    set (P5 := <[Regidx Rra := regval_into_reg
        (add_vec_int (mword_of_int (CT + 0x14) : mword 64) 4)]> P4).
    assert (Hjaq : add_vec (mword_of_int (CT + 0x14) : mword 64)
                     (sign_extend' 64 (mword_of_int 2428 : mword 21))
                   = mword_of_int KernelSyms.acquire) by pcw.
    iEval (rewrite Hjaq) in "Hpc".
    assert (HP5a0 : P5 !!! Regidx Ra0 = a_cons)
      by (rewrite /P5 upd_ne; [exact HP4a0 | reg_neq]).
    assert (HP5ra : P5 !!! Regidx Rra
                    = add_vec_int (mword_of_int (CT + 0x14) : mword 64) 4)
      by (rewrite /P5; apply upd_eq).
    assert (HP5s1 : P5 !!! Regidx Rs1 = cv).
    { rewrite /P5 upd_ne; [| reg_neq]. rewrite /P4 upd_ne; [| reg_neq].
      rewrite /P3 upd_ne; [| reg_neq]. rewrite /P2; apply upd_eq. }
    assert (HP5sp : P5 !!! Regidx csp_rs1 = pa_stk sp0 6%nat).
    { rewrite /P5 upd_ne; [| reg_neq]. rewrite /P4 upd_ne; [| reg_neq].
      rewrite /P3 upd_ne; [| reg_neq]. rewrite /P2 upd_ne; [| reg_neq].
      rewrite /P1 upd_ne; [| reg_neq]. exact HP0sp. }
    assert (HthrP : forall r : mword 5, is_cs_idx r = true ->
              r <> csp_rs1 -> r <> Rs0 -> r <> Rs1 -> P5 !!! Regidx r = m !!! Regidx r).
    { intros r Hr N2 N8 N9.
      assert (N1 : r <> Rra) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      assert (N10 : r <> Ra0) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      rewrite /P5 upd_ne; [| congruence]. rewrite /P4 upd_ne; [| congruence].
      rewrite /P3 upd_ne; [| congruence]. rewrite /P2 upd_ne; [| congruence].
      rewrite /P1 upd_ne; [| congruence]. rewrite /P0 upd_ne; [| congruence]. reflexivity. }
    assert (HcsP5 : ct_cs_hi P5 m)
      by (exact (ct_cs_hi_thr3 P5 m m HthrP (ct_cs_hi_refl m))).
    (* ---- the three continuations, built the moment the frame is saved ---- *)
    iAssert (ct_ret (CID0 := CID) γu hb cb pme m K lvl eb b lks)
      with "[Hcont]" as "Hcont".
    { rewrite /ct_ret. iExact "Hcont". }
    iAssert (ct_exit_prop (CID0 := CID) γu hb cb cn γc pme m K lvl eb b sp0 lks)
      with "[Hsaved Hcont]" as "EXIT".
    { iApply (ct_mk_exit γu hb cb cn γc pme m K lvl eb b sp0 lks Hends Hspm HK
                Hbm Hbelow with "Ht Hlk Hsaved Hcont"). }
    iAssert (ct_wake_prop (CID0 := CID) γu hb cb cn γc pme m K lvl eb b sp0 lks) as "WAKE".
    { iApply (ct_mk_wake γu hb cb cn γc γs pme m K lvl eb b sp0 lks HK Hlen Hlvl Hbm
                Hbelow with "Ht Hpinv"). }
    (* [KILL] IS BUILT IN THE C('U') ARM AND NOT HERE (lane OUT-FUPD): the
       loop's consputc calls are paid out of [ct_pay_erase], whose guard
       [cons_erase cb] is the switch's own case -- so it is only available
       once the [beq] has decided it.
       THE MARK GOES BACK UNMOVED on every arm but the default's store, and
       it is already at or before this byte.  Built per arm below, because
       the default arm needs the half itself and not the bundle. *)
    (* ---- +0x014 acquire(&cons.lock) ---- *)
    iDestruct (cpu_own_transport CID CIDp9 lvl eb pme b ltac:(wp_next_chain)
                 with "Hcnt") as "Hcnt".
    iApply (Acquire.wp_acquire_sconf KT1 γc "cons"%string (cons_res_at cn) P5 lvl eb pme
              (K - 6)%nat b lks ltac:(lia) ltac:(lia) Hbelow
              with "Hcg Hcnt Ht Hpc []").
    all: try lkbelow.
    { iEval (rewrite HP5a0). iExact "Hlk". }
    iIntros (CIDaq Hsaq ms0 maq) "%Hms0 Hcg Hpc %Hcsaq Hlocked Hres _ Hcnt Hpay". rgall.
    iEval (rewrite HP5ra) in "Hpc".
    assert (Hp018 : ret_pc (add_vec_int (mword_of_int (CT + 0x14) : mword 64) 4)
                    = (mword_of_int (CT + 0x18) : mword 64)) by pcw.
    iEval (rewrite Hp018) in "Hpc".
    assert (Hchain : b = false \/ pme = zero_reg -> (CIDaq : CPU) = (CID : CPU))
      by wp_next_chain.
    assert (HthrA : forall r : mword 5, is_cs_idx r = true ->
              maq !!! Regidx r = P5 !!! Regidx r)
      by (exact (callee_saved_lookup Hcsaq)).
    assert (Hsp : maq !!! Regidx csp_rs1 = pa_stk sp0 6%nat)
      by (rewrite (HthrA csp_rs1 ltac:(vm_compute; reflexivity)); exact HP5sp).
    assert (Hs1 : maq !!! Regidx Rs1 = cv)
      by (rewrite (HthrA Rs1 ltac:(vm_compute; reflexivity)); exact HP5s1).
    assert (Hcs : ct_cs_hi maq m)
      by (exact (ct_cs_hi_thr maq P5 m HthrA HcsP5)).
    (* ================= +0x018 .. +0x02c : switch (c) =================== *)
    iApply (wp_cli_s_sconf (mword_of_int (CT + 0x18)) Ra5 (mword_of_int 21 : mword 6)
              (mword_of_int 21 : mword 64) maq (trap_res b + (K - 6))%nat false
              ltac:(nz) ltac:(rdok) ltac:(pcw) with "Hcg Hpc []").
    { iApply (cnti_018 with "Ht"). }
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    set (S1 := <[Regidx Ra5 := regval_into_reg (mword_of_int 21 : mword 64)]> maq).
    assert (HthrS1 : forall r : mword 5, is_cs_idx r = true ->
              S1 !!! Regidx r = maq !!! Regidx r).
    { intros r Hr.
      assert (N15 : r <> Ra5) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      rewrite /S1 upd_ne; [reflexivity | congruence]. }
    assert (HS1a5 : S1 !!! Regidx Ra5 = (mword_of_int 21 : mword 64))
      by (rewrite /S1; apply upd_eq).
    assert (HS1s1 : S1 !!! Regidx Rs1 = cv)
      by (rewrite (HthrS1 Rs1 ltac:(vm_compute; reflexivity)); exact Hs1).
    assert (HS1sp : S1 !!! Regidx csp_rs1 = pa_stk sp0 6%nat)
      by (rewrite (HthrS1 csp_rs1 ltac:(vm_compute; reflexivity)); exact Hsp).
    assert (HS1cs : ct_cs_hi S1 m) by (exact (ct_cs_hi_thr S1 maq m HthrS1 Hcs)).
    assert (Hp01a : add_vec_int (mword_of_int (CT + 0x18) : mword 64) 2
                    = mword_of_int (CT + 0x1a)) by pcw.
    iEval (rewrite Hp01a) in "Hpc".
    (* ---- +0x01a beq s1,a5 : case C('U') ---- *)
    destruct (eq_vec (cv : mword 64) (mword_of_int 21 : mword 64)) eqn:Hku.
    { iApply (wp_beq_taken_s_sconf (mword_of_int (CT + 0x1a)) (mword_of_int 120 : mword 13)
                Ra5 Rs1 S1 (trap_res b + (K - 6))%nat false ltac:(nz) ltac:(nz)
                ltac:(rgall; rewrite HS1s1 HS1a5; exact Hku)
                ltac:(vm_compute; reflexivity) with "Hcg Hpc []").
    { iApply (cnti_01a with "Ht"). }
      iApply bi.later_intro. iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
      assert (Hj092 : add_vec (mword_of_int (CT + 0x1a) : mword 64)
                        (sign_extend' 64 (mword_of_int 120 : mword 13))
                      = mword_of_int (CT + 0x92)) by pcw.
      iEval (rewrite Hj092) in "Hpc".
      iAssert (ct_hi_kill γu hb) with "[Hhi]" as "Hhiout".
      { rewrite /ct_hi_kill. iExists hh. iFrame "Hhi".
        iPureIntro; exact Hx. }
      (* THE SWITCH DECIDED THE GUARD: this is ^U, an erase byte. *)
      assert (Her : cons_erase cb = true).
      { rewrite (ct_arg_eq_byte cb 21 ltac:(rewrite <- Hcv; exact Hku)).
        vm_compute; reflexivity. }
      iPoseProof (ct_mk_pay_erase γu hb cb Her with "Hpy") as "#Hep".
      iAssert (ct_kill_prop (CID0 := CID) γu hb cb cn γc pme m K lvl eb b sp0 lks)
        as "KILL".
      { iApply (ct_mk_kill γu hb cb cn γtx γc γv pme m K lvl eb b sp0 lks
                  Hcnu Hends HK Hlvl Hbm
                  Hbelow with "Ht Hdev Hbw Htxl Hep"). }
      iApply (ct_kill_pre (CIDq := CIDaq) γu cn hb cb γc pme m S1 K lvl eb b sp0 lks
                Hcnu Hends HS1sp HS1cs Hchain Hbelow
                with "Ht Huinv Hep Hcg Hpc Hcnt Hpay Hlocked Hres Hrest Hhiout
                      Hmark KILL EXIT"). }
    iApply (wp_beq_fall_s_sconf (mword_of_int (CT + 0x1a)) (mword_of_int 120 : mword 13)
              Ra5 Rs1 S1 (trap_res b + (K - 6))%nat false ltac:(nz) ltac:(nz)
              ltac:(rgall; rewrite HS1s1 HS1a5; exact Hku) with "Hcg Hpc []").
    { iApply (cnti_01a with "Ht"). }
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    assert (Hp01e : add_vec_int (mword_of_int (CT + 0x1a) : mword 64) 4
                    = mword_of_int (CT + 0x1e)) by pcw.
    iEval (rewrite Hp01e) in "Hpc".
    (* ---- +0x01e li a5,127 ; +0x022 beq s1,a5 : case '\x7f' ---- *)
    iApply (wp_li4_s_sconf (mword_of_int (CT + 0x1e)) Ra5 (mword_of_int 127 : mword 12)
              (mword_of_int 127 : mword 64) S1 (trap_res b + (K - 6))%nat false
              ltac:(nz) ltac:(rdok) ltac:(pcw) with "Hcg Hpc []").
    { iApply (cnti_01e with "Ht"). }
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    set (S2 := <[Regidx Ra5 := regval_into_reg (mword_of_int 127 : mword 64)]> S1).
    assert (HthrS2 : forall r : mword 5, is_cs_idx r = true ->
              S2 !!! Regidx r = maq !!! Regidx r).
    { intros r Hr.
      assert (N15 : r <> Ra5) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      rewrite /S2 upd_ne; [| congruence]. apply HthrS1; exact Hr. }
    assert (HS2a5 : S2 !!! Regidx Ra5 = (mword_of_int 127 : mword 64))
      by (rewrite /S2; apply upd_eq).
    assert (HS2s1 : S2 !!! Regidx Rs1 = cv)
      by (rewrite (HthrS2 Rs1 ltac:(vm_compute; reflexivity)); exact Hs1).
    assert (HS2sp : S2 !!! Regidx csp_rs1 = pa_stk sp0 6%nat)
      by (rewrite (HthrS2 csp_rs1 ltac:(vm_compute; reflexivity)); exact Hsp).
    assert (HS2cs : ct_cs_hi S2 m) by (exact (ct_cs_hi_thr S2 maq m HthrS2 Hcs)).
    assert (Hp022 : add_vec_int (mword_of_int (CT + 0x1e) : mword 64) 4
                    = mword_of_int (CT + 0x22)) by pcw.
    iEval (rewrite Hp022) in "Hpc".
    destruct (eq_vec (cv : mword 64) (mword_of_int 127 : mword 64)) eqn:Hdel.
    { iApply (wp_beq_taken_s_sconf (mword_of_int (CT + 0x22)) (mword_of_int 206 : mword 13)
                Ra5 Rs1 S2 (trap_res b + (K - 6))%nat false ltac:(nz) ltac:(nz)
                ltac:(rgall; rewrite HS2s1 HS2a5; exact Hdel)
                ltac:(vm_compute; reflexivity) with "Hcg Hpc []").
    { iApply (cnti_022 with "Ht"). }
      iApply bi.later_intro. iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
      assert (Hj0f0 : add_vec (mword_of_int (CT + 0x22) : mword 64)
                        (sign_extend' 64 (mword_of_int 206 : mword 13))
                      = mword_of_int (CT + 0xf0)) by pcw.
      iEval (rewrite Hj0f0) in "Hpc".
      iAssert (ct_hi_kill γu hb) with "[Hhi]" as "Hhiout".
      { rewrite /ct_hi_kill. iExists hh. iFrame "Hhi".
        iPureIntro; exact Hx. }
      assert (Her : cons_erase cb = true).
      { rewrite (ct_arg_eq_byte cb 127 ltac:(rewrite <- Hcv; exact Hdel)).
        vm_compute; reflexivity. }
      iPoseProof (ct_mk_pay_erase γu hb cb Her with "Hpy") as "#Hep".
      iApply (ct_bs (CIDq := CIDaq) γtx γc γu γv cn hb cb pme m S2 K lvl eb b sp0 lks
                Hcnu Hends HS2sp HS2cs HK Hlvl Hchain Hbelow
                with "Ht Hdev Hbw Htxl Hep Hcg Hpc Hcnt Hpay Hlocked Hres Hrest
                      Hhiout Hmark EXIT"). }
    iApply (wp_beq_fall_s_sconf (mword_of_int (CT + 0x22)) (mword_of_int 206 : mword 13)
              Ra5 Rs1 S2 (trap_res b + (K - 6))%nat false ltac:(nz) ltac:(nz)
              ltac:(rgall; rewrite HS2s1 HS2a5; exact Hdel) with "Hcg Hpc []").
    { iApply (cnti_022 with "Ht"). }
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    assert (Hp026 : add_vec_int (mword_of_int (CT + 0x22) : mword 64) 4
                    = mword_of_int (CT + 0x26)) by pcw.
    iEval (rewrite Hp026) in "Hpc".
    (* ---- +0x026 c.li a5,8 ; +0x028 beq s1,a5 : case C('H') ---- *)
    iApply (wp_cli_s_sconf (mword_of_int (CT + 0x26)) Ra5 (mword_of_int 8 : mword 6)
              (mword_of_int 8 : mword 64) S2 (trap_res b + (K - 6))%nat false
              ltac:(nz) ltac:(rdok) ltac:(pcw) with "Hcg Hpc []").
    { iApply (cnti_026 with "Ht"). }
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    set (S3 := <[Regidx Ra5 := regval_into_reg (mword_of_int 8 : mword 64)]> S2).
    assert (HthrS3 : forall r : mword 5, is_cs_idx r = true ->
              S3 !!! Regidx r = maq !!! Regidx r).
    { intros r Hr.
      assert (N15 : r <> Ra5) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      rewrite /S3 upd_ne; [| congruence]. apply HthrS2; exact Hr. }
    assert (HS3a5 : S3 !!! Regidx Ra5 = (mword_of_int 8 : mword 64))
      by (rewrite /S3; apply upd_eq).
    assert (HS3s1 : S3 !!! Regidx Rs1 = cv)
      by (rewrite (HthrS3 Rs1 ltac:(vm_compute; reflexivity)); exact Hs1).
    assert (HS3sp : S3 !!! Regidx csp_rs1 = pa_stk sp0 6%nat)
      by (rewrite (HthrS3 csp_rs1 ltac:(vm_compute; reflexivity)); exact Hsp).
    assert (HS3cs : ct_cs_hi S3 m) by (exact (ct_cs_hi_thr S3 maq m HthrS3 Hcs)).
    assert (Hp028 : add_vec_int (mword_of_int (CT + 0x26) : mword 64) 2
                    = mword_of_int (CT + 0x28)) by pcw.
    iEval (rewrite Hp028) in "Hpc".
    destruct (eq_vec (cv : mword 64) (mword_of_int 8 : mword 64)) eqn:Hbs.
    { iApply (wp_beq_taken_s_sconf (mword_of_int (CT + 0x28)) (mword_of_int 200 : mword 13)
                Ra5 Rs1 S3 (trap_res b + (K - 6))%nat false ltac:(nz) ltac:(nz)
                ltac:(rgall; rewrite HS3s1 HS3a5; exact Hbs)
                ltac:(vm_compute; reflexivity) with "Hcg Hpc []").
    { iApply (cnti_028 with "Ht"). }
      iApply bi.later_intro. iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
      assert (Hj0f0 : add_vec (mword_of_int (CT + 0x28) : mword 64)
                        (sign_extend' 64 (mword_of_int 200 : mword 13))
                      = mword_of_int (CT + 0xf0)) by pcw.
      iEval (rewrite Hj0f0) in "Hpc".
      iAssert (ct_hi_kill γu hb) with "[Hhi]" as "Hhiout".
      { rewrite /ct_hi_kill. iExists hh. iFrame "Hhi".
        iPureIntro; exact Hx. }
      assert (Her : cons_erase cb = true).
      { rewrite (ct_arg_eq_byte cb 8 ltac:(rewrite <- Hcv; exact Hbs)).
        vm_compute; reflexivity. }
      iPoseProof (ct_mk_pay_erase γu hb cb Her with "Hpy") as "#Hep".
      iApply (ct_bs (CIDq := CIDaq) γtx γc γu γv cn hb cb pme m S3 K lvl eb b sp0 lks
                Hcnu Hends HS3sp HS3cs HK Hlvl Hchain Hbelow
                with "Ht Hdev Hbw Htxl Hep Hcg Hpc Hcnt Hpay Hlocked Hres Hrest
                      Hhiout Hmark EXIT"). }
    (* ---- the default arm ---- *)
    iApply (wp_beq_fall_s_sconf (mword_of_int (CT + 0x28)) (mword_of_int 200 : mword 13)
              Ra5 Rs1 S3 (trap_res b + (K - 6))%nat false ltac:(nz) ltac:(nz)
              ltac:(rgall; rewrite HS3s1 HS3a5; exact Hbs) with "Hcg Hpc []").
    { iApply (cnti_028 with "Ht"). }
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    assert (Hp02c : add_vec_int (mword_of_int (CT + 0x28) : mword 64) 4
                    = mword_of_int (CT + 0x2c)) by pcw.
    iEval (rewrite Hp02c) in "Hpc".
    iApply (ct_dflt (CIDq := CIDaq) γtx γc γu γv cn hh pme m S3 K lvl eb b sp0
              cv lks hb cb Hcnu Hcne Hx
              HS3sp HS3s1 HS3cs HK Hlvl Hchain Hbelow Hends Hcv
              with "Ht Hdev Hbw Htxl Hpy Htg Hcg Hpc Hcnt Hpay Hlocked Hres Hhi
                    Hmark Hrest WAKE EXIT").
  Qed.

End ProofConsoleintr.

End ConsoleintrProof.
