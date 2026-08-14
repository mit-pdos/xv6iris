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
   arm below a plain lemma over `{CIDq : CpuId} with one chaining premise
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
Require Import RiscvLang RiscvPtsto RiscvExtras.
Require Import RegFile.
Require Import InstrBytes WpMmodeLeafBase.
Require Import SmodeCore.
Require Import CalleeSaved KernelText.
Require Import StackOwn.
Require Import VcGen WpSconfAlu WpSconfMem WpSconfCtl WpSconfBtype.
Require Import W32Arith.
Require Import IntrDefs WpSmodeIntr.
Require Import HartTp WpNext.
Require Import WpLock ProcGeom CpuOwn KernelRvcDecode.
Require Import FdSlots.
Require Import DiskPtsto WpUart UartTxInv.
Require Import ConsoleInv.
Require Import PanicStub SchedCtx.
Require Import SpecAcquire SpecRelease SpecConsputc SpecWakeup.
Require Import CodeConsoleintr.
Require Import SpecConsoleintr.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.

Import Defs.
Local Open Scope Z_scope.

Notation CT := KernelSyms.consoleintr (only parsing).

(* THE FRAME IS SIX SLOTS.  A [c.sdsp]/[c.ldsp] displacement off the pushed sp
   names slot [6 - uimm] counted down from the ENTRY sp. *)
Lemma ct_slot_bridge (X : mword 64) (o : mword 64) (k : nat) :
  add_vec (mword_of_int (- (8 * Z.of_nat 6%nat))) o = mword_of_int (- (8 * Z.of_nat k)) ->
  add_vec (pa_stk X 6%nat) o = pa_stk X k.
Proof.
  intro H. unfold pa_stk, add_vec_int. rewrite po_addv_assoc H. reflexivity.
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
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !irefslotG Σ}.
  Context `{!uartGhostG Σ, !diskGhostG Σ}.
  Context `{GEN : RiscvLang.GenId}.

  Local Ltac rgall := repeat (rewrite rget_ne; [| vm_compute; discriminate]).

  (* ---- the frame, in two pieces ------------------------------------ *)

  (* the three the prologue saves unconditionally *)
  Definition ct_saved (sp0 : mword 64) (m0 : regfile) : iProp Σ :=
    (pa_stk sp0 1 ↦₈ (m0 !!! Regidx Rra) ∗
     pa_stk sp0 2 ↦₈ (m0 !!! Regidx Rs0) ∗
     pa_stk sp0 3 ↦₈ (m0 !!! Regidx Rs1))%I.

  (* slots 4 and 5 (s2/s3's shrink-wrap) and slot 6, which nothing writes *)
  Definition ct_rest (sp0 : mword 64) : iProp Σ :=
    ((∃ w : mword 64, pa_stk sp0 4 ↦₈ w) ∗
     (∃ w : mword 64, pa_stk sp0 5 ↦₈ w) ∗
     (∃ w : mword 64, pa_stk sp0 6 ↦₈ w))%I.

  Lemma ct_frame_back (sp0 : mword 64) (m0 : regfile) :
    ct_saved sp0 m0 -∗ ct_rest sp0 -∗ stack_own sp0 6.
  Proof.
    iIntros "(H1 & H2 & H3) (H4 & H5 & H6)".
    rewrite stack_own_slots. cbn [seq].
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
  Proof.
    intros (_ & _ & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11).
    unfold ct_cs_top. split_and!; assumption.
  Qed.

  (* A CALL, OR ANY RUN OF INSTRUCTIONS THAT WRITES NO CALLEE-SAVED
     REGISTER, transports both claims -- which is every use of them in this
     file, so the two lemmas replace the ten-way [split_and!] at each site. *)
  Lemma ct_cs_hi_thr (M1 M m0 : regfile) :
    (forall r : mword 5, is_cs_idx r = true -> M1 !!! Regidx r = M !!! Regidx r) ->
    ct_cs_hi M m0 -> ct_cs_hi M1 m0.
  Proof.
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
  Proof.
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
  Proof.
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
  Proof. unfold ct_cs_hi. split_and!; reflexivity. Qed.

  Lemma ct_cs_hi_thr3 (M1 M m0 : regfile) :
    (forall r : mword 5, is_cs_idx r = true ->
       r <> csp_rs1 -> r <> Rs0 -> r <> Rs1 -> M1 !!! Regidx r = M !!! Regidx r) ->
    ct_cs_hi M m0 -> ct_cs_hi M1 m0.
  Proof.
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
  Proof.
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
  Proof.
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
  Proof.
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
  Proof. rewrite <- !trunc32_subrange. rewrite !trunc32_sext. reflexivity. Qed.

  (* [% INPUT_BUF_SIZE], compiled as [andi …,127]: the index is a nat below
     128 for EVERY value of the word, which is the whole reason
     [ConsoleInv.cons_res] can relate the three indices to nothing.  Three
     sites compute it -- the kill loop and the two store paths. *)
  Lemma ct_ring_idx (e : mword 32) :
    exists i : nat,
      (i < INPUT_BUF_SIZE)%nat /\
      and_vec (sign_extend' 64 e : mword 64) (sign_extend' 64 (mword_of_int 127 : mword 12))
      = (mword_of_int (Z.of_nat i) : mword 64).
  Proof.
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

  (* the function's own exit, as a [wp_next] at the entry hart *)
  Definition ct_ret `{CID0 : CpuId} (pme : mword 64) (m0 : regfile)
      (K lvl : nat) (eb : bool) (C : iProp Σ) (b : bool) (lks : gset nat) : iProp Σ :=
    (wp_next (CID0 := CID0) b pme (fun (CID : CpuId) =>
       ∀ Mf : regfile,
         ⌜ callee_saved m0 Mf /\ (forall r : regidx, r ∈ dom (rf_to_gmap Mf)) ⌝ -∗
         sie_cap_gpr Mf K b pme -∗
         cpu_own lvl eb pme C b lks -∗
         kernel_text -∗ pc_is (ret_pc (m0 !!! Regidx Rra)) -∗
         WP (Loop : expr riscv_lang)))%I.

  (* =================================================================== *)
  (*  +0x110 .. +0x118 -- THE EPILOGUE.                                   *)
  (* =================================================================== *)
  Lemma ct_epi `{CID : CpuId} (CID0 : CPU)
      (pme : mword 64) (m0 M : regfile) (K lvl : nat) (eb : bool) (C : iProp Σ)
      (sp0 : mword 64) (b : bool) (lks : gset nat) :
    m0 !!! Regidx csp_rs1 = sp0 ->
    M !!! Regidx csp_rs1 = pa_stk sp0 6%nat ->
    ct_cs_hi M m0 ->
    (consoleintr_stack <= K)%nat ->
    (b = false \/ pme = zero_reg -> (CID : CPU) = CID0) ->
    kernel_text -∗
    sie_cap_gpr M (K - 6)%nat b pme -∗
    cpu_own lvl eb pme C b lks -∗
    pc_is (mword_of_int (CT + 0x110)) -∗
    ct_saved sp0 m0 -∗ ct_rest sp0 -∗
    ct_ret (CID0 := CID0) pme m0 K lvl eb C b lks -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hm0sp HMsp HMcs HK Hcr.
    iIntros "#Ht Hcg Hcnt Hpc (K1 & K2 & K3) Hrest Hcont".
    iPoseProof (cnti_110 with "Ht") as "Hi110".
    iPoseProof (cnti_112 with "Ht") as "Hi112".
    iPoseProof (cnti_114 with "Ht") as "Hi114".
    iPoseProof (cnti_116 with "Ht") as "Hi116".
    iPoseProof (cnti_118 with "Ht") as "Hi118".
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
              with "Hcg Hpc Hi110 [K1]").
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
              with "Hcg Hpc Hi112 [K2]").
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
              with "Hcg Hpc Hi114 [K3]").
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
    { rewrite HE3sp. unfold pa_stk, add_vec_int. rewrite po_addv_assoc.
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
              E3 (K - 6)%nat 6%nat b Hpop with "Hcg Hpc Hi116 Hframe").
    iIntros (CIDp Hsp') "Hcg Hpc".
    assert (Havx : (K - 6 + 6)%nat = K) by (unfold consoleintr_stack in HK; lia).
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
              ltac:(nz) with "Hcg Hpc Hi118").
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
    iDestruct (cpu_own_transport CID CIDr lvl eb pme C b ltac:(wp_next_chain)
                 with "Hcnt") as "Hcnt".
    rewrite /ct_ret.
    iSpecialize ("Hcont" $! CIDr with "[%]"); [wp_next_chain|].
    iApply ("Hcont" $! E4 with "[%] Hcg Hcnt Ht Hpc").
    split; [exact Hcs | intro r; apply rf_to_gmap_dom].
  Qed.

End CtBodies.

(* ===================================================================== *)
Module ConsoleintrProof (Acquire : ACQUIRE) (Consputc : CONSPUTC)
                        (Release : RELEASE) (Wakeup : WAKEUP)
                        : CONSOLEINTR.

Section ProofConsoleintr.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !irefslotG Σ}.
  Context `{!uartGhostG Σ, !diskGhostG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Local Ltac rgall := repeat (rewrite rget_ne; [| vm_compute; discriminate]).
  Local Typeclasses Opaque cpu_own.

  (* =================================================================== *)
  (*  [EXIT] (+0x104): release cons.lock, then the epilogue.              *)
  (*  NINE jumps reach it -- every arm of the switch ends here -- so it   *)
  (*  is a continuation and the epilogue is written once.                 *)
  (* =================================================================== *)
  Definition ct_exit_prop `{CID0 : CpuId}
      (γc : gname) (pme : mword 64) (m0 : regfile) (K lvl : nat) (eb : bool)
      (C : iProp Σ) (b : bool) (sp0 : mword 64) (lks : gset nat) : iProp Σ :=
    (wp_next (CID0 := CID0) b pme (fun (CIDx : CpuId) =>
       ∀ M : regfile,
         ⌜ M !!! Regidx csp_rs1 = pa_stk sp0 6%nat ⌝ -∗
         ⌜ ct_cs_hi M m0 ⌝ -∗
         sie_cap_gpr M (trap_res b + (K - 6))%nat false pme -∗
         pc_is (mword_of_int (CT + 0x104)) -∗
         cpu_own (S lvl) eb pme C false ({[lock_rank "cons"]} ∪ lks) -∗
         arm_pay lvl eb pme -∗
         locked γc cpu_id -∗
         cons_res -∗
         ct_rest sp0 -∗
         WP (Loop : expr riscv_lang)))%I.

  Lemma ct_mk_exit (γc : gname) (pme : mword 64) (m0 : regfile) (K lvl : nat)
      (eb : bool) (C : iProp Σ) (b : bool) (sp0 : mword 64) (lks : gset nat) :
    m0 !!! Regidx csp_rs1 = sp0 ->
    (consoleintr_stack <= K)%nat ->
    match lvl with O => eb | S _ => false end = b ->
    (* release's set arithmetic: the entry [cpu_own] holds
       [{[lock_rank "cons"]} ∪ lks], and release needs [lock_rank "cons"] to
       drop back OUT of it cleanly, i.e. [lock_rank "cons" ∉ lks]. *)
    locks_below lks (lock_rank "cons") ->
    kernel_text -∗ is_conslock γc -∗ ct_saved sp0 m0 -∗
    ct_ret (CID0 := CID) pme m0 K lvl eb C b lks -∗
    ct_exit_prop (CID0 := CID) γc pme m0 K lvl eb C b sp0 lks.
  Proof.
    intros Hm0sp HK Hb Hbelow. subst b.
    pose proof (locks_below_not_elem _ _ Hbelow) as Hfresh.
    iIntros "#Ht #Hlk Hsaved Hcont".
    rewrite /ct_exit_prop.
    iIntros (CIDx Hsx M) "%Hsp %Hcs Hcg Hpc Hcnt Hpay Hlocked Hres Hrest".
    iPoseProof (cnti_104 with "Ht") as "Hi104".
    iPoseProof (cnti_108 with "Ht") as "Hi108".
    iPoseProof (cnti_10c with "Ht") as "Hi10c".
    (* +0x104 auipc a0,0x12 ; +0x108 addi a0,a0,-272 : a0 := &cons *)
    iApply (wp_auipc_s_sconf (mword_of_int (CT + 0x104)) Ra0 (mword_of_int 18 : mword 20)
              M (trap_res (match lvl with O => eb | S _ => false end) + (K - 6))%nat false ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hi104").
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    set (X1 := <[Regidx Ra0 := regval_into_reg
        (add_vec (mword_of_int (CT + 0x104) : mword 64)
           (auipc_off (mword_of_int 18 : mword 20)))]> M).
    assert (Hp108 : add_vec_int (mword_of_int (CT + 0x104) : mword 64) 4
                    = mword_of_int (CT + 0x108)) by pcw.
    iEval (rewrite Hp108) in "Hpc".
    iApply (wp_addi4_s_sconf (mword_of_int (CT + 0x108)) Ra0 Ra0 (mword_of_int 3840 : mword 12)
              X1 (trap_res (match lvl with O => eb | S _ => false end) + (K - 6))%nat false ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hi108").
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    set (X2 := <[Regidx Ra0 := regval_into_reg
        (add_vec (X1 !!! Regidx Ra0) (sign_extend' 64 (mword_of_int 3840 : mword 12)))]> X1).
    assert (HX2a0 : X2 !!! Regidx Ra0 = a_cons).
    { rewrite /X2 upd_eq /X1 upd_eq /a_cons. apply bv_eq; vm_compute; reflexivity. }
    assert (Hp10c : add_vec_int (mword_of_int (CT + 0x108) : mword 64) 4
                    = mword_of_int (CT + 0x10c)) by pcw.
    iEval (rewrite Hp10c) in "Hpc".
    (* +0x10c jal ra,release *)
    iApply (wp_jal_s_sconf (mword_of_int (CT + 0x10c)) Rra (mword_of_int 2170 : mword 21)
              X2 (trap_res (match lvl with O => eb | S _ => false end) + (K - 6))%nat false ltac:(nz) ltac:(rdok)
              ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi10c").
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    set (X3 := <[Regidx Rra := regval_into_reg
        (add_vec_int (mword_of_int (CT + 0x10c) : mword 64) 4)]> X2).
    assert (Hjrl : add_vec (mword_of_int (CT + 0x10c) : mword 64)
                     (sign_extend' 64 (mword_of_int 2170 : mword 21))
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
    iApply (Release.wp_release_sconf γc a_cons "cons"%string cons_res X3
              lvl eb pme C (K - 6)%nat ({[lock_rank "cons"]} ∪ lks) HX3lka
              ltac:(unfold consoleintr_stack in HK; lia)
              with "Hcg Ht Hpc Hlk Hlocked Hres Hcnt Hpay").
    iIntros (CIDr Hsr mr) "Hcg Hpc %Hcsr Hcnt". rgall.
    assert (Hsetback : ({[lock_rank "cons"]} ∪ lks) ∖ {[lock_rank "cons"]} = lks)
      by (apply locks_add_del_below; lkbelow).
    iEval (rewrite Hsetback) in "Hcnt".
    iEval (rewrite HX3ra) in "Hpc".
    assert (Hp110 : ret_pc (add_vec_int (mword_of_int (CT + 0x10c) : mword 64) 4)
                    = (mword_of_int (CT + 0x110) : mword 64)) by pcw.
    iEval (rewrite Hp110) in "Hpc".
    assert (Hthr : forall r : mword 5, is_cs_idx r = true -> mr !!! Regidx r = M !!! Regidx r).
    { intros r Hr. rewrite (callee_saved_lookup Hcsr r Hr). apply HthrX; exact Hr. }
    iApply (ct_epi (CID := CIDr) CIDr pme m0 mr K lvl eb C sp0 _ lks Hm0sp
              ltac:(rewrite (Hthr csp_rs1 ltac:(vm_compute; reflexivity)); exact Hsp)
              ltac:(exact (ct_cs_hi_thr mr M m0 Hthr Hcs))
              HK ltac:(intros _; reflexivity)
              with "Ht Hcg Hcnt Hpc Hsaved Hrest").
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
      (γc : gname) (pme : mword 64) (m0 : regfile)
      (K lvl : nat) (eb : bool) (C : iProp Σ) (b : bool) (sp0 : mword 64) (lks : gset nat) : iProp Σ :=
    (wp_next (CID0 := CID0) b pme (fun (CIDw : CpuId) =>
       ∀ (M : regfile) (wv : mword 64),
         ⌜ M !!! Regidx csp_rs1 = pa_stk sp0 6%nat ⌝ -∗
         ⌜ M !!! Regidx Ra2 = wv ⌝ -∗
         ⌜ ct_cs_hi M m0 ⌝ -∗
         sie_cap_gpr M (trap_res b + (K - 6))%nat false pme -∗
         pc_is (mword_of_int (CT + 0x156)) -∗
         cpu_own (S lvl) eb pme C false ({[lock_rank "cons"]} ∪ lks) -∗
         arm_pay lvl eb pme -∗
         locked γc cpu_id -∗
         cons_res -∗
         ct_rest sp0 -∗
         ct_exit_prop (CID0 := CID0) γc pme m0 K lvl eb C b sp0 lks -∗
         WP (Loop : expr riscv_lang)))%I.

  Lemma ct_mk_wake (γc : gname) (γs : list gname) (pme : mword 64) (m0 : regfile)
      (K lvl : nat) (eb : bool) (C : iProp Σ) (b : bool) (sp0 : mword 64) (lks : gset nat) :
    (consoleintr_stack <= K)%nat ->
    length γs = NPROC ->
    (Z.of_nat lvl + 2 < 2 ^ 31)%Z ->
    match lvl with O => eb | S _ => false end = b ->
    (* wakeup is called while cons.lock is STILL held, i.e. its held set is
       [{[lock_rank "cons"]} ∪ lks], not bare [lks] -- so this is the same
       "cons" order fact as [ct_mk_exit], lifted (via [locks_below_mono] and
       [locks_below_union_singleton]) to wakeup's own "proc" (11) premise
       below. *)
    locks_below lks (lock_rank "cons") ->
    kernel_text -∗ panic_wp_any -∗ procs_inv γs -∗
    ct_wake_prop (CID0 := CID) γc pme m0 K lvl eb C b sp0 lks.
  Proof.
    intros HK Hlen Hlvl Hb Hbelow. subst b.
    assert (Hbelow_proc : locks_below ({[lock_rank "cons"]} ∪ lks) (lock_rank "proc")).
    { apply locks_below_union_singleton; [vm_compute; lia |].
      lkbelow. }
    iIntros "#Ht #Hpanic #Hpinv".
    rewrite /ct_wake_prop.
    iIntros (CIDw Hsw M wv) "%Hsp %Ha2 %Hcs Hcg Hpc Hcnt Hpay Hlocked Hres Hrest EXIT".
    iPoseProof (cnti_156 with "Ht") as "Hi156".
    iPoseProof (cnti_15a with "Ht") as "Hi15a".
    iPoseProof (cnti_15e with "Ht") as "Hi15e".
    iPoseProof (cnti_162 with "Ht") as "Hi162".
    iPoseProof (cnti_166 with "Ht") as "Hi166".
    iPoseProof (cnti_16a with "Ht") as "Hi16a".
    (* +0x156 auipc a5,0x12 *)
    iApply (wp_auipc_s_sconf (mword_of_int (CT + 0x156)) Ra5 (mword_of_int 18 : mword 20)
              M (trap_res (match lvl with O => eb | S _ => false end) + (K - 6))%nat false
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi156").
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    set (W1 := <[Regidx Ra5 := regval_into_reg
        (add_vec (mword_of_int (CT + 0x156) : mword 64)
           (auipc_off (mword_of_int 18 : mword 20)))]> M).
    assert (Hp15a : add_vec_int (mword_of_int (CT + 0x156) : mword 64) 4
                    = mword_of_int (CT + 0x15a)) by pcw.
    iEval (rewrite Hp15a) in "Hpc".
    (* +0x15a sw a2,-198(a5) : cons.w := cons.e *)
    iDestruct "Hres" as (rr ww ee bs) "(Hrc & Hwc & Hec & %Hlenb & Hdat)".
    assert (HW1wa : add_vec (W1 !!! Regidx Ra5)
                      (sign_extend' 64 (mword_of_int 3914 : mword 12)) = a_cons_w).
    { rewrite /W1 upd_eq /a_cons_w /coff_of /a_cons. apply bv_eq; vm_compute; reflexivity. }
    assert (HW1a2 : W1 !!! Regidx Ra2 = wv)
      by (rewrite /W1 upd_ne; [exact Ha2 | reg_neq]).
    iApply (wp_sw_s_sconf (mword_of_int (CT + 0x15a)) Ra2 Ra5 (mword_of_int 3914 : mword 12)
              W1 (trap_res (match lvl with O => eb | S _ => false end) + (K - 6))%nat ww false
              with "Hcg Hpc Hi15a [Hwc]").
    { rgall. iEval (rewrite HW1wa). iExact "Hwc". }
    iApply wp_next_off_intro. iIntros "Hcg Hpc Hwc". rgall.
    iEval (rewrite HW1wa HW1a2) in "Hwc".
    assert (Hp15e : add_vec_int (mword_of_int (CT + 0x15a) : mword 64) 4
                    = mword_of_int (CT + 0x15e)) by pcw.
    iEval (rewrite Hp15e) in "Hpc".
    iAssert (cons_res) with "[Hrc Hwc Hec Hdat]" as "Hres".
    { iExists rr, (trunc32 wv), ee, bs. iFrame "Hrc Hwc Hec Hdat".
      iPureIntro. exact Hlenb. }
    (* +0x15e auipc a0,0x12 ; +0x162 addi a0,a0,-210 : a0 := &cons.r *)
    iApply (wp_auipc_s_sconf (mword_of_int (CT + 0x15e)) Ra0 (mword_of_int 18 : mword 20)
              W1 (trap_res (match lvl with O => eb | S _ => false end) + (K - 6))%nat false
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi15e").
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    set (W2 := <[Regidx Ra0 := regval_into_reg
        (add_vec (mword_of_int (CT + 0x15e) : mword 64)
           (auipc_off (mword_of_int 18 : mword 20)))]> W1).
    assert (Hp162 : add_vec_int (mword_of_int (CT + 0x15e) : mword 64) 4
                    = mword_of_int (CT + 0x162)) by pcw.
    iEval (rewrite Hp162) in "Hpc".
    iApply (wp_addi4_s_sconf (mword_of_int (CT + 0x162)) Ra0 Ra0 (mword_of_int 3902 : mword 12)
              W2 (trap_res (match lvl with O => eb | S _ => false end) + (K - 6))%nat false
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi162").
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    set (W3 := <[Regidx Ra0 := regval_into_reg
        (add_vec (W2 !!! Regidx Ra0) (sign_extend' 64 (mword_of_int 3902 : mword 12)))]> W2).
    assert (Hp166 : add_vec_int (mword_of_int (CT + 0x162) : mword 64) 4
                    = mword_of_int (CT + 0x166)) by pcw.
    iEval (rewrite Hp166) in "Hpc".
    (* +0x166 jal ra,wakeup *)
    iApply (wp_jal_s_sconf (mword_of_int (CT + 0x166)) Rra (mword_of_int 6958 : mword 21)
              W3 (trap_res (match lvl with O => eb | S _ => false end) + (K - 6))%nat false
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi166").
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    set (W4 := <[Regidx Rra := regval_into_reg
        (add_vec_int (mword_of_int (CT + 0x166) : mword 64) 4)]> W3).
    assert (Hjwk : add_vec (mword_of_int (CT + 0x166) : mword 64)
                     (sign_extend' 64 (mword_of_int 6958 : mword 21))
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
              (trap_res (match lvl with O => eb | S _ => false end) + (K - 6))%nat eb C false
              ({[lock_rank "cons"]} ∪ lks)
              ltac:(unfold consoleintr_stack in HK; lia)
              ltac:(intro r; apply rf_to_gmap_dom) Hlen ltac:(lia) Hbelow_proc
              with "Hcg Hcnt Ht Hpc Hpanic Hpinv").
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
              ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi16a").
    iApply wp_next_off_intro. iApply bi.later_intro. iIntros "Hcg Hpc". rgall.
    assert (Hj104 : add_vec (mword_of_int (CT + 0x16a) : mword 64)
                      (sign_extend' 64 (sign_extend' 21
                         (concat_vec (mword_of_int 1997 : mword 11) ('b"0"))))
                    = mword_of_int (CT + 0x104)) by pcw.
    iEval (rewrite Hj104) in "Hpc".
    iSpecialize ("EXIT" $! CIDw with "[%]"); [wp_next_chain|].
    iApply ("EXIT" $! Mw with "[%] [%] Hcg Hpc Hcnt Hpay Hlocked Hres Hrest").
    - rewrite (Hthr csp_rs1 ltac:(vm_compute; reflexivity)). exact Hsp.
    - exact (ct_cs_hi_thr Mw M m0 Hthr Hcs).
  Qed.

  (* ---- the three-instruction stub the C('U') arm exits through -------
     [c.ldsp s2,16(sp)], [c.ldsp s3,8(sp)], [c.j -> +0x104].  It occurs at
     +0x0de, +0x0e4 and +0x0ea -- once per way out of the kill-line loop --
     so it is a lemma over its three pcs rather than three copies. *)
  Lemma ct_restore23 `{CIDq : CpuId}
      (γc : gname) (pme : mword 64) (m0 M : regfile) (K lvl : nat) (eb : bool)
      (C : iProp Σ) (b : bool) (sp0 : mword 64) (pc1 pc2 pc3 : mword 64)
      (jimm : mword 11) (lks : gset nat) :
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
       whose cone runs up to "uart" (15). *)
    locks_below lks (lock_rank "cons") ->
    instr pc1 true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")),
                          sp, Regidx Rs2, false, 8)) -∗
    instr pc2 true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")),
                          sp, Regidx Rs3, false, 8)) -∗
    instr pc3 true (JAL (sign_extend' 21 (concat_vec jimm ('b"0")), zreg)) -∗
    sie_cap_gpr M (trap_res b + (K - 6))%nat false pme -∗
    pc_is pc1 -∗
    cpu_own (S lvl) eb pme C false ({[lock_rank "cons"]} ∪ lks) -∗
    arm_pay lvl eb pme -∗
    locked γc cpu_id -∗
    cons_res -∗
    pa_stk sp0 4 ↦₈ (m0 !!! Regidx Rs2) -∗
    pa_stk sp0 5 ↦₈ (m0 !!! Regidx Rs3) -∗
    (∃ w : mword 64, pa_stk sp0 6 ↦₈ w) -∗
    ct_exit_prop (CID0 := CID) γc pme m0 K lvl eb C b sp0 lks -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hsp Hthr Hq1 Hq2 Hjt Hal Hchain Hbelow.
    destruct Hthr as (T4 & T5 & T6 & T7 & T8 & T9 & T10 & T11).
    iIntros "Hi1 Hi2 Hi3 Hcg Hpc Hcnt Hpay Hlocked Hres H4 H5 H6 EXIT".
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
              [H4 H5 H6]").
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
      (γc : gname)
      (pme : mword 64) (m0 : regfile) (K lvl : nat) (eb : bool)
      (C : iProp Σ) (b : bool) (sp0 : mword 64) (lks : gset nat) : iProp Σ :=
    (wp_next (CID0 := CID0) b pme (fun (CIDk : CpuId) =>
       ∀ (M : regfile) (rr ww ee : mword 32) (bs : list (bv 8)),
         ⌜ M !!! Regidx csp_rs1 = pa_stk sp0 6%nat ⌝ -∗
         ⌜ M !!! Regidx Rs1 = a_cons ⌝ -∗
         ⌜ M !!! Regidx Rs2 = (mword_of_int 10 : mword 64) ⌝ -∗
         ⌜ M !!! Regidx Rs3 = (mword_of_int 256 : mword 64) ⌝ -∗
         ⌜ M !!! Regidx Ra5 = sign_extend' 64 ee ⌝ -∗
         ⌜ ct_cs_top M m0 ⌝ -∗
         ⌜ length bs = INPUT_BUF_SIZE ⌝ -∗
         ct_exit_prop (CID0 := CID0) γc pme m0 K lvl eb C b sp0 lks -∗
         sie_cap_gpr M (trap_res b + (K - 6))%nat false pme -∗
         pc_is (mword_of_int (CT + 0xb8)) -∗
         cpu_own (S lvl) eb pme C false ({[lock_rank "cons"]} ∪ lks) -∗
         arm_pay lvl eb pme -∗
         locked γc cpu_id -∗
         a_cons_r ↦₄ rr -∗ a_cons_w ↦₄ ww -∗ a_cons_e ↦₄ ee -∗ cons_data bs -∗
         pa_stk sp0 4 ↦₈ (m0 !!! Regidx Rs2) -∗
         pa_stk sp0 5 ↦₈ (m0 !!! Regidx Rs3) -∗
         (∃ w : mword 64, pa_stk sp0 6 ↦₈ w) -∗
         WP (Loop : expr riscv_lang)))%I.

  Lemma ct_mk_kill (γtx γc : gname) (γu : uart_names) (γv : disk_names)
      (pme : mword 64) (m0 : regfile) (K lvl : nat) (eb : bool)
      (C : iProp Σ) (b : bool) (sp0 : mword 64) (lks : gset nat) :
    (consoleintr_stack <= K)%nat ->
    (Z.of_nat lvl + 2 < 2 ^ 31)%Z ->
    match lvl with O => eb | S _ => false end = b ->
    (* the entry [cpu_own] is at the plain [lks] -- consputc's own [uart]
       premise is reached by [lkbelow] pushing this across the [cons]
       singleton [ct_kill_prop]'s continuation adds. *)
    locks_below lks (lock_rank "cons") ->
    kernel_text -∗ panic_wp_any -∗
    dev_inv γu γv -∗ is_txlock γtx γu -∗ uart_sent_sub γu [] -∗
    ct_kill_prop (CID0 := CID) γc pme m0 K lvl eb C b sp0 lks.
  Proof.
    intros HK Hlvl Hb Hbelow. subst b.
    iIntros "#Ht #Hpanic #Hdev #Htxl #Hsub".
    rewrite /ct_kill_prop.
    iLöb as "IH".
    iIntros (CIDk Hsk M rr ww ee bs)
      "%Hsp %Hs1 %Hs2 %Hs3 %Ha5 %Hthr %Hlenb EXIT Hcg Hpc Hcnt Hpay Hlocked Hrc Hwc Hec Hdat H4 H5 H6".
    iPoseProof (cnti_0b8 with "Ht") as "Hi0b8".
    iPoseProof (cnti_0ba with "Ht") as "Hi0ba".
    iPoseProof (cnti_0be with "Ht") as "Hi0be".
    iPoseProof (cnti_0c0 with "Ht") as "Hi0c0".
    iPoseProof (cnti_0c4 with "Ht") as "Hi0c4".
    (* ---- +0x0b8 c.addiw a5,a5,-1 ---- *)
    iApply (wp_caddiw_s_sconf (mword_of_int (CT + 0xb8)) Ra5 (mword_of_int 63 : mword 6)
              M (trap_res (match lvl with O => eb | S _ => false end) + (K - 6))%nat false
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi0b8").
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
              ltac:(nz) ltac:(rdok) Hwv with "Hcg Hpc Hi0ba").
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
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi0be").
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
    iApply (wp_lbu_s_sconf (mword_of_int (CT + 0xc0)) Ra4 Ra4 (mword_of_int 24 : mword 12)
              L3 (trap_res (match lvl with O => eb | S _ => false end) + (K - 6))%nat
              (db : mword 8) false ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi0c0 [Hbyte]").
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
                ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi0c4").
      iApply bi.later_intro. iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
      assert (Hj0ea : add_vec (mword_of_int (CT + 0xc4) : mword 64)
                        (sign_extend' 64 (mword_of_int 38 : mword 13))
                      = mword_of_int (CT + 0xea)) by pcw.
      iEval (rewrite Hj0ea) in "Hpc".
      iPoseProof (cnti_0ea with "Ht") as "Hi0ea".
      iPoseProof (cnti_0ec with "Ht") as "Hi0ec".
      iPoseProof (cnti_0ee with "Ht") as "Hi0ee".
      iApply (ct_restore23 (CIDq := CIDk) γc pme m0 L4 K lvl eb C _ sp0
                (mword_of_int (CT + 0xea)) (mword_of_int (CT + 0xec))
                (mword_of_int (CT + 0xee)) (mword_of_int 11 : mword 11) lks
                HL4sp
                ltac:(exact (ct_cs_top_thr L4 M m0 HthrL Hthr))
                ltac:(pcw) ltac:(pcw) ltac:(pcw) ltac:(vm_compute; reflexivity)
                ltac:(wp_next_chain) Hbelow
                with "Hi0ea Hi0ec Hi0ee Hcg Hpc Hcnt Hpay Hlocked [Hrc Hwc Hec Hdat] H4 H5 H6 EXIT").
      iExists rr, ww, ee, bs. iFrame "Hrc Hwc Hec Hdat". iPureIntro. exact Hlenb. }
    (* ---- an ordinary byte: erase it ---- *)
    iApply (wp_beq_fall_s_sconf (mword_of_int (CT + 0xc4)) (mword_of_int 38 : mword 13)
              Rs2 Ra4 L4 (trap_res (match lvl with O => eb | S _ => false end) + (K - 6))%nat
              false ltac:(nz) ltac:(nz)
              ltac:(rgall; rewrite HL4a4 HL4s2 w32_zext8_moi
                      (w32_eq_moi cbv 10 ltac:(lia) ltac:(lia)); exact HNL)
              with "Hcg Hpc Hi0c4").
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    assert (Hp0c8 : add_vec_int (mword_of_int (CT + 0xc4) : mword 64) 4
                    = mword_of_int (CT + 0xc8)) by pcw.
    iEval (rewrite Hp0c8) in "Hpc".
    (* ---- +0x0c8 sw a5,160(s1) : cons.e-- ---- *)
    assert (Hea : add_vec (L4 !!! Regidx Rs1)
                    (sign_extend' 64 (mword_of_int 160 : mword 12)) = a_cons_e)
      by (rewrite HL4s1; reflexivity).
    iPoseProof (cnti_0c8 with "Ht") as "Hi0c8".
    iApply (wp_sw_s_sconf (mword_of_int (CT + 0xc8)) Ra5 Rs1 (mword_of_int 160 : mword 12)
              L4 (trap_res (match lvl with O => eb | S _ => false end) + (K - 6))%nat ee false
              with "Hcg Hpc Hi0c8 [Hec]").
    { rgall. iEval (rewrite Hea). iExact "Hec". }
    iApply wp_next_off_intro. iIntros "Hcg Hpc Hec". rgall.
    iEval (rewrite Hea HL4a5 trunc32_sext) in "Hec".
    assert (Hp0cc : add_vec_int (mword_of_int (CT + 0xc8) : mword 64) 4
                    = mword_of_int (CT + 0xcc)) by pcw.
    iEval (rewrite Hp0cc) in "Hpc".
    (* ---- +0x0cc c.mv a0,s3 ; +0x0ce jal consputc ---- *)
    iPoseProof (cnti_0cc with "Ht") as "Hi0cc".
    iApply (wp_cmv_s_sconf (mword_of_int (CT + 0xcc)) Ra0 Rs3 L4
              (trap_res (match lvl with O => eb | S _ => false end) + (K - 6))%nat false
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi0cc").
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    set (L5 := <[Regidx Ra0 := regval_into_reg
        (add_vec zero_reg (L4 !!! Regidx Rs3))]> L4).
    assert (Hp0ce : add_vec_int (mword_of_int (CT + 0xcc) : mword 64) 2
                    = mword_of_int (CT + 0xce)) by pcw.
    iEval (rewrite Hp0ce) in "Hpc".
    iPoseProof (cnti_0ce with "Ht") as "Hi0ce".
    iApply (wp_jal_s_sconf (mword_of_int (CT + 0xce)) Rra (mword_of_int 2096896 : mword 21)
              L5 (trap_res (match lvl with O => eb | S _ => false end) + (K - 6))%nat false
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi0ce").
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    set (L6 := <[Regidx Rra := regval_into_reg
        (add_vec_int (mword_of_int (CT + 0xce) : mword 64) 4)]> L5).
    assert (Hjcp : add_vec (mword_of_int (CT + 0xce) : mword 64)
                     (sign_extend' 64 (mword_of_int 2096896 : mword 21))
                   = mword_of_int KernelSyms.consputc) by pcw.
    iEval (rewrite Hjcp) in "Hpc".
    assert (HL6ra : L6 !!! Regidx Rra
                    = add_vec_int (mword_of_int (CT + 0xce) : mword 64) 4)
      by (rewrite /L6; apply upd_eq).
    iApply (Consputc.wp_consputc_sconf γtx γu γv L6
              (trap_res (match lvl with O => eb | S _ => false end) + (K - 6))%nat
              [] (S lvl) eb C false pme ({[lock_rank "cons"]} ∪ lks)
              ltac:(unfold consoleintr_stack, consputc_stack in *; lia) ltac:(lia)
              with "Hcg Hcnt Ht Hpc Hpanic Hdev Htxl Hsub").
    all: try lkbelow.
    iApply wp_next_off_intro. iIntros (mcp cs) "Hcg Hcnt Hpc [%Hcpcs %Hcpra] _". rgall.
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
    iPoseProof (cnti_0d2 with "Ht") as "Hi0d2".
    iApply (wp_lw_s_sconf (mword_of_int (CT + 0xd2)) Ra5 Rs1 (mword_of_int 160 : mword 12)
              mcp (trap_res (match lvl with O => eb | S _ => false end) + (K - 6))%nat
              ee' false ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi0d2 [Hec]").
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
    iPoseProof (cnti_0d6 with "Ht") as "Hi0d6".
    iApply (wp_lw_s_sconf (mword_of_int (CT + 0xd6)) Ra4 Rs1 (mword_of_int 156 : mword 12)
              L7 (trap_res (match lvl with O => eb | S _ => false end) + (K - 6))%nat
              ww false ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi0d6 [Hwc]").
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
    iPoseProof (cnti_0da with "Ht") as "Hi0da".
    destruct (neq_vec (sign_extend' 64 ww : mword 64) (sign_extend' 64 ee')) eqn:Hmore.
    { (* more to erase: THE BACK EDGE to +0x0b8 *)
      iApply (wp_bne_taken_s_sconf (mword_of_int (CT + 0xda)) (mword_of_int 8158 : mword 13)
                Ra5 Ra4 L8 (trap_res (match lvl with O => eb | S _ => false end) + (K - 6))%nat
                false ltac:(nz) ltac:(nz)
                ltac:(rgall; rewrite HL8a4 HL8a5; exact Hmore)
                ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi0da").
      (* the Löb back edge: the [▷] has to come off "IH", not just the goal *)
      iNext. iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
      assert (Hbk : add_vec (mword_of_int (CT + 0xda) : mword 64)
                      (sign_extend' 64 (mword_of_int 8158 : mword 13))
                    = mword_of_int (CT + 0xb8)) by pcw.
      iEval (rewrite Hbk) in "Hpc".
      iSpecialize ("IH" $! CIDk with "[%]"); [wp_next_chain|].
      iApply ("IH" $! L8 rr ww ee' bs with "[%] [%] [%] [%] [%] [%] [%]
                EXIT Hcg Hpc Hcnt Hpay Hlocked Hrc Hwc Hec Hdat H4 H5 H6").
      - rewrite (HthrL8 csp_rs1 ltac:(vm_compute; reflexivity)). exact Hsp.
      - rewrite (HthrL8 Rs1 ltac:(vm_compute; reflexivity)). exact Hs1.
      - rewrite (HthrL8 Rs2 ltac:(vm_compute; reflexivity)). exact Hs2.
      - rewrite (HthrL8 Rs3 ltac:(vm_compute; reflexivity)). exact Hs3.
      - exact HL8a5.
      - exact (ct_cs_top_thr L8 M m0 HthrL8 Hthr).
      - exact Hlenb. }
    (* the line is empty: fall out at +0x0de *)
    iApply (wp_bne_fall_s_sconf (mword_of_int (CT + 0xda)) (mword_of_int 8158 : mword 13)
              Ra5 Ra4 L8 (trap_res (match lvl with O => eb | S _ => false end) + (K - 6))%nat
              false ltac:(nz) ltac:(nz)
              ltac:(rgall; rewrite HL8a4 HL8a5; exact Hmore) with "Hcg Hpc Hi0da").
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    assert (Hp0de : add_vec_int (mword_of_int (CT + 0xda) : mword 64) 4
                    = mword_of_int (CT + 0xde)) by pcw.
    iEval (rewrite Hp0de) in "Hpc".
    iPoseProof (cnti_0de with "Ht") as "Hi0de".
    iPoseProof (cnti_0e0 with "Ht") as "Hi0e0".
    iPoseProof (cnti_0e2 with "Ht") as "Hi0e2".
    iApply (ct_restore23 (CIDq := CIDk) γc pme m0 L8 K lvl eb C _ sp0
              (mword_of_int (CT + 0xde)) (mword_of_int (CT + 0xe0))
              (mword_of_int (CT + 0xe2)) (mword_of_int 17 : mword 11) lks
              ltac:(rewrite (HthrL8 csp_rs1 ltac:(vm_compute; reflexivity)); exact Hsp)
              ltac:(exact (ct_cs_top_thr L8 M m0 HthrL8 Hthr))
              ltac:(pcw) ltac:(pcw) ltac:(pcw) ltac:(vm_compute; reflexivity)
              ltac:(wp_next_chain) Hbelow
              with "Hi0de Hi0e0 Hi0e2 Hcg Hpc Hcnt Hpay Hlocked [Hrc Hwc Hec Hdat] H4 H5 H6 EXIT").
    iExists rr, ww, ee', bs. iFrame "Hrc Hwc Hec Hdat". iPureIntro. exact Hlenb.
  Qed.

  (* =================================================================== *)
  (*  ['\r'] (+0x12e): echo '\n' INSTEAD of the byte, store '\n', and     *)
  (*  FALL INTO [WAKE].  The only arm that reaches the wake tail without   *)
  (*  a test, because the byte it just stored IS the newline.              *)
  (* =================================================================== *)
  Lemma ct_cr `{CIDq : CpuId}
      (γtx γc : gname) (γu : uart_names) (γv : disk_names)
      (pme : mword 64) (m0 M : regfile) (K lvl : nat) (eb : bool)
      (C : iProp Σ) (b : bool) (sp0 : mword 64) (lks : gset nat) :
    M !!! Regidx csp_rs1 = pa_stk sp0 6%nat ->
    ct_cs_hi M m0 ->
    (consoleintr_stack <= K)%nat ->
    (Z.of_nat lvl + 2 < 2 ^ 31)%Z ->
    (b = false \/ pme = zero_reg -> (CIDq : CPU) = (CID : CPU)) ->
    (* same "cons" bound as the sibling arms: this one reaches consputc,
       whose cone runs up to "uart" (15). *)
    locks_below lks (lock_rank "cons") ->
    kernel_text -∗ panic_wp_any -∗
    dev_inv γu γv -∗ is_txlock γtx γu -∗ uart_sent_sub γu [] -∗
    sie_cap_gpr M (trap_res b + (K - 6))%nat false pme -∗
    pc_is (mword_of_int (CT + 0x12e)) -∗
    cpu_own (S lvl) eb pme C false ({[lock_rank "cons"]} ∪ lks) -∗
    arm_pay lvl eb pme -∗
    locked γc cpu_id -∗
    cons_res -∗
    ct_rest sp0 -∗
    ct_wake_prop (CID0 := CID) γc pme m0 K lvl eb C b sp0 lks -∗
    ct_exit_prop (CID0 := CID) γc pme m0 K lvl eb C b sp0 lks -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hsp Hcs HK Hlvl Hchain Hbelow.
    iIntros "#Ht #Hpanic #Hdev #Htxl #Hsub Hcg Hpc Hcnt Hpay Hlocked Hres Hrest WAKE EXIT".
    iPoseProof (cnti_12e with "Ht") as "Hi12e".
    iPoseProof (cnti_130 with "Ht") as "Hi130".
    iPoseProof (cnti_134 with "Ht") as "Hi134".
    iPoseProof (cnti_138 with "Ht") as "Hi138".
    iPoseProof (cnti_13c with "Ht") as "Hi13c".
    iPoseProof (cnti_140 with "Ht") as "Hi140".
    iPoseProof (cnti_144 with "Ht") as "Hi144".
    iPoseProof (cnti_146 with "Ht") as "Hi146".
    iPoseProof (cnti_14a with "Ht") as "Hi14a".
    iPoseProof (cnti_14e with "Ht") as "Hi14e".
    iPoseProof (cnti_150 with "Ht") as "Hi150".
    iPoseProof (cnti_152 with "Ht") as "Hi152".
    (* ---- +0x12e c.li a0,10 ; +0x130 jal consputc ---- *)
    iApply (wp_cli_s_sconf (mword_of_int (CT + 0x12e)) Ra0 (mword_of_int 10 : mword 6)
              (mword_of_int 10 : mword 64) M (trap_res b + (K - 6))%nat false
              ltac:(nz) ltac:(rdok) ltac:(pcw) with "Hcg Hpc Hi12e").
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    set (D1 := <[Regidx Ra0 := regval_into_reg (mword_of_int 10 : mword 64)]> M).
    assert (Hp130 : add_vec_int (mword_of_int (CT + 0x12e) : mword 64) 2
                    = mword_of_int (CT + 0x130)) by pcw.
    iEval (rewrite Hp130) in "Hpc".
    iApply (wp_jal_s_sconf (mword_of_int (CT + 0x130)) Rra (mword_of_int 2096798 : mword 21)
              D1 (trap_res b + (K - 6))%nat false ltac:(nz) ltac:(rdok)
              ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi130").
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    set (D2 := <[Regidx Rra := regval_into_reg
        (add_vec_int (mword_of_int (CT + 0x130) : mword 64) 4)]> D1).
    assert (Hjcp : add_vec (mword_of_int (CT + 0x130) : mword 64)
                     (sign_extend' 64 (mword_of_int 2096798 : mword 21))
                   = mword_of_int KernelSyms.consputc) by pcw.
    iEval (rewrite Hjcp) in "Hpc".
    assert (HD2ra : D2 !!! Regidx Rra
                    = add_vec_int (mword_of_int (CT + 0x130) : mword 64) 4)
      by (rewrite /D2; apply upd_eq).
    iApply (Consputc.wp_consputc_sconf γtx γu γv D2
              (trap_res b + (K - 6))%nat [] (S lvl) eb C false pme ({[lock_rank "cons"]} ∪ lks)
              ltac:(unfold consoleintr_stack, consputc_stack in *; lia) ltac:(lia)
              with "Hcg Hcnt Ht Hpc Hpanic Hdev Htxl Hsub").
    all: try lkbelow.
    iApply wp_next_off_intro. iIntros (mcp cs) "Hcg Hcnt Hpc [%Hcpcs %Hcpra] _". rgall.
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
              with "Hcg Hpc Hi134").
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    set (D3 := <[Regidx Ra5 := regval_into_reg
        (add_vec (mword_of_int (CT + 0x134) : mword 64)
           (auipc_off (mword_of_int 18 : mword 20)))]> mcp).
    assert (Hp138 : add_vec_int (mword_of_int (CT + 0x134) : mword 64) 4
                    = mword_of_int (CT + 0x138)) by pcw.
    iEval (rewrite Hp138) in "Hpc".
    iApply (wp_addi4_s_sconf (mword_of_int (CT + 0x138)) Ra5 Ra5 (mword_of_int 3792 : mword 12)
              D3 (trap_res b + (K - 6))%nat false ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi138").
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    set (D4 := <[Regidx Ra5 := regval_into_reg
        (add_vec (D3 !!! Regidx Ra5) (sign_extend' 64 (mword_of_int 3792 : mword 12)))]> D3).
    assert (HD4a5 : D4 !!! Regidx Ra5 = a_cons).
    { rewrite /D4 upd_eq /D3 upd_eq /a_cons. apply bv_eq; vm_compute; reflexivity. }
    assert (Hp13c : add_vec_int (mword_of_int (CT + 0x138) : mword 64) 4
                    = mword_of_int (CT + 0x13c)) by pcw.
    iEval (rewrite Hp13c) in "Hpc".
    (* ---- +0x13c lw a4,160(a5) : a4 := cons.e ---- *)
    iDestruct "Hres" as (rr ww ee bs) "(Hrc & Hwc & Hec & %Hlenb & Hdat)".
    assert (Hea : add_vec (D4 !!! Regidx Ra5)
                    (sign_extend' 64 (mword_of_int 160 : mword 12)) = a_cons_e)
      by (rewrite HD4a5; reflexivity).
    iApply (wp_lw_s_sconf (mword_of_int (CT + 0x13c)) Ra4 Ra5 (mword_of_int 160 : mword 12)
              D4 (trap_res b + (K - 6))%nat ee false ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hi13c [Hec]").
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
              D5 (trap_res b + (K - 6))%nat false ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi140").
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
              (trap_res b + (K - 6))%nat false ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi144").
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
    iApply (wp_sw_s_sconf (mword_of_int (CT + 0x146)) Ra3 Ra5 (mword_of_int 160 : mword 12)
              D7 (trap_res b + (K - 6))%nat ee false with "Hcg Hpc Hi146 [Hec]").
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
              ltac:(nz) ltac:(rdok) Hwv with "Hcg Hpc Hi14a").
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
              (trap_res b + (K - 6))%nat false ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi14e").
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
              ltac:(nz) ltac:(rdok) ltac:(pcw) with "Hcg Hpc Hi150").
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
    iApply (wp_sb_s_sconf (mword_of_int (CT + 0x152)) Ra4 Ra5 (mword_of_int 24 : mword 12)
              D10 (trap_res b + (K - 6))%nat db false with "Hcg Hpc Hi152 [Hbyte]").
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
    iAssert (cons_res) with "[Hrc Hwc Hec Hdat]" as "Hres".
    { iExists rr, ww, ee1, (<[idx := trunc8 (mword_of_int 10 : mword 64)]> bs).
      iFrame "Hrc Hwc Hec Hdat". iPureIntro. rewrite length_insert. exact Hlenb. }
    iSpecialize ("WAKE" $! CIDq with "[%]"); [exact Hchain|].
    iApply ("WAKE" $! D10 (sign_extend' 64 ee1) with "[%] [%] [%]
              Hcg Hpc Hcnt Hpay Hlocked Hres Hrest EXIT").
    - rewrite (HthrA csp_rs1 ltac:(vm_compute; reflexivity)). exact Hsp.
    - rewrite /D10 upd_ne; [| reg_neq]. rewrite /D9 upd_ne; [| reg_neq].
      rewrite /D8 upd_ne; [| reg_neq]. rewrite /D7; apply upd_eq.
    - exact (ct_cs_hi_thr D10 M m0 HthrA Hcs).
  Qed.

  (* =================================================================== *)
  (*  [C('H') / '\x7f'] (+0x0f0): backspace.  Erase one byte if the line   *)
  (*  is not empty, then leave.  The same [cons.e--] the kill loop makes,  *)
  (*  minus the loop -- and, like it, bounded by nothing.                  *)
  (* =================================================================== *)
  Lemma ct_bs `{CIDq : CpuId}
      (γtx γc : gname) (γu : uart_names) (γv : disk_names)
      (pme : mword 64) (m0 M : regfile) (K lvl : nat) (eb : bool)
      (C : iProp Σ) (b : bool) (sp0 : mword 64) (lks : gset nat) :
    M !!! Regidx csp_rs1 = pa_stk sp0 6%nat ->
    ct_cs_hi M m0 ->
    (consoleintr_stack <= K)%nat ->
    (Z.of_nat lvl + 2 < 2 ^ 31)%Z ->
    (b = false \/ pme = zero_reg -> (CIDq : CPU) = (CID : CPU)) ->
    (* same "cons" bound as the sibling arms: the backspace path also
       reaches consputc, whose cone runs up to "uart" (15). *)
    locks_below lks (lock_rank "cons") ->
    kernel_text -∗ panic_wp_any -∗
    dev_inv γu γv -∗ is_txlock γtx γu -∗ uart_sent_sub γu [] -∗
    sie_cap_gpr M (trap_res b + (K - 6))%nat false pme -∗
    pc_is (mword_of_int (CT + 0xf0)) -∗
    cpu_own (S lvl) eb pme C false ({[lock_rank "cons"]} ∪ lks) -∗
    arm_pay lvl eb pme -∗
    locked γc cpu_id -∗
    cons_res -∗
    ct_rest sp0 -∗
    ct_exit_prop (CID0 := CID) γc pme m0 K lvl eb C b sp0 lks -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hsp Hcs HK Hlvl Hchain Hbelow.
    iIntros "#Ht #Hpanic #Hdev #Htxl #Hsub Hcg Hpc Hcnt Hpay Hlocked Hres Hrest EXIT".
    iPoseProof (cnti_0f0 with "Ht") as "Hi0f0".
    iPoseProof (cnti_0f4 with "Ht") as "Hi0f4".
    iPoseProof (cnti_0f8 with "Ht") as "Hi0f8".
    iPoseProof (cnti_0fc with "Ht") as "Hi0fc".
    iPoseProof (cnti_100 with "Ht") as "Hi100".
    (* ---- +0x0f0/+0x0f4 : a4 := &cons ---- *)
    iApply (wp_auipc_s_sconf (mword_of_int (CT + 0xf0)) Ra4 (mword_of_int 18 : mword 20)
              M (trap_res b + (K - 6))%nat false ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi0f0").
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    set (B1 := <[Regidx Ra4 := regval_into_reg
        (add_vec (mword_of_int (CT + 0xf0) : mword 64)
           (auipc_off (mword_of_int 18 : mword 20)))]> M).
    assert (Hp0f4 : add_vec_int (mword_of_int (CT + 0xf0) : mword 64) 4
                    = mword_of_int (CT + 0xf4)) by pcw.
    iEval (rewrite Hp0f4) in "Hpc".
    iApply (wp_addi4_s_sconf (mword_of_int (CT + 0xf4)) Ra4 Ra4 (mword_of_int 3860 : mword 12)
              B1 (trap_res b + (K - 6))%nat false ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi0f4").
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    set (B2 := <[Regidx Ra4 := regval_into_reg
        (add_vec (B1 !!! Regidx Ra4) (sign_extend' 64 (mword_of_int 3860 : mword 12)))]> B1).
    assert (HB2a4 : B2 !!! Regidx Ra4 = a_cons).
    { rewrite /B2 upd_eq /B1 upd_eq /a_cons. apply bv_eq; vm_compute; reflexivity. }
    assert (Hp0f8 : add_vec_int (mword_of_int (CT + 0xf4) : mword 64) 4
                    = mword_of_int (CT + 0xf8)) by pcw.
    iEval (rewrite Hp0f8) in "Hpc".
    (* ---- +0x0f8 lw a5,160(a4) ; +0x0fc lw a4,156(a4) ---- *)
    iDestruct "Hres" as (rr ww ee bs) "(Hrc & Hwc & Hec & %Hlenb & Hdat)".
    assert (Hea : add_vec (B2 !!! Regidx Ra4)
                    (sign_extend' 64 (mword_of_int 160 : mword 12)) = a_cons_e)
      by (rewrite HB2a4; reflexivity).
    iApply (wp_lw_s_sconf (mword_of_int (CT + 0xf8)) Ra5 Ra4 (mword_of_int 160 : mword 12)
              B2 (trap_res b + (K - 6))%nat ee false ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hi0f8 [Hec]").
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
    iApply (wp_lw_s_sconf (mword_of_int (CT + 0xfc)) Ra4 Ra4 (mword_of_int 156 : mword 12)
              B3 (trap_res b + (K - 6))%nat ww false ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hi0fc [Hwc]").
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
                ltac:(rgall; rewrite HB4a4 HB4a5; exact Hne) with "Hcg Hpc Hi100").
      iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
      assert (Hp104 : add_vec_int (mword_of_int (CT + 0x100) : mword 64) 4
                      = mword_of_int (CT + 0x104)) by pcw.
      iEval (rewrite Hp104) in "Hpc".
      iSpecialize ("EXIT" $! CIDq with "[%]"); [exact Hchain|].
      iApply ("EXIT" $! B4 with "[%] [%] Hcg Hpc Hcnt Hpay Hlocked
                [Hrc Hwc Hec Hdat] Hrest").
      - rewrite (HthrB csp_rs1 ltac:(vm_compute; reflexivity)). exact Hsp.
      - exact (ct_cs_hi_thr B4 M m0 HthrB Hcs).
      - iExists rr, ww, ee, bs. iFrame "Hrc Hwc Hec Hdat". iPureIntro. exact Hlenb. }
    (* ---- +0x11a .. +0x12c : erase it ---- *)
    iApply (wp_bne_taken_s_sconf (mword_of_int (CT + 0x100)) (mword_of_int 26 : mword 13)
              Ra5 Ra4 B4 (trap_res b + (K - 6))%nat false ltac:(nz) ltac:(nz)
              ltac:(rgall; rewrite HB4a4 HB4a5; exact Hne)
              ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi100").
    iApply bi.later_intro. iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    assert (Hj11a : add_vec (mword_of_int (CT + 0x100) : mword 64)
                      (sign_extend' 64 (mword_of_int 26 : mword 13))
                    = mword_of_int (CT + 0x11a)) by pcw.
    iEval (rewrite Hj11a) in "Hpc".
    iPoseProof (cnti_11a with "Ht") as "Hi11a".
    iPoseProof (cnti_11c with "Ht") as "Hi11c".
    iPoseProof (cnti_120 with "Ht") as "Hi120".
    iPoseProof (cnti_124 with "Ht") as "Hi124".
    iPoseProof (cnti_128 with "Ht") as "Hi128".
    iPoseProof (cnti_12c with "Ht") as "Hi12c".
    (* +0x11a c.addiw a5,a5,-1 *)
    iApply (wp_caddiw_s_sconf (mword_of_int (CT + 0x11a)) Ra5 (mword_of_int 63 : mword 6)
              B4 (trap_res b + (K - 6))%nat false ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi11a").
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    iEval (rewrite HB4a5 ct_addiw_dec) in "Hcg".
    set (ee1 := add_vec ee (mword_of_int (-1) : mword 32)).
    set (B5 := <[Regidx Ra5 := regval_into_reg (sign_extend' 64 ee1)]> B4).
    assert (Hp11c : add_vec_int (mword_of_int (CT + 0x11a) : mword 64) 2
                    = mword_of_int (CT + 0x11c)) by pcw.
    iEval (rewrite Hp11c) in "Hpc".
    (* +0x11c auipc a4,0x12 ; +0x120 sw a5,-136(a4) : cons.e-- *)
    iApply (wp_auipc_s_sconf (mword_of_int (CT + 0x11c)) Ra4 (mword_of_int 18 : mword 20)
              B5 (trap_res b + (K - 6))%nat false ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi11c").
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    set (B6 := <[Regidx Ra4 := regval_into_reg
        (add_vec (mword_of_int (CT + 0x11c) : mword 64)
           (auipc_off (mword_of_int 18 : mword 20)))]> B5).
    assert (Hp120 : add_vec_int (mword_of_int (CT + 0x11c) : mword 64) 4
                    = mword_of_int (CT + 0x120)) by pcw.
    iEval (rewrite Hp120) in "Hpc".
    assert (HB6ea : add_vec (B6 !!! Regidx Ra4)
                      (sign_extend' 64 (mword_of_int 3976 : mword 12)) = a_cons_e).
    { rewrite /B6 upd_eq /a_cons_e /coff_of /a_cons. apply bv_eq; vm_compute; reflexivity. }
    assert (HB6a5 : B6 !!! Regidx Ra5 = sign_extend' 64 ee1)
      by (rewrite /B6 upd_ne; [rewrite /B5; apply upd_eq | reg_neq]).
    iApply (wp_sw_s_sconf (mword_of_int (CT + 0x120)) Ra5 Ra4 (mword_of_int 3976 : mword 12)
              B6 (trap_res b + (K - 6))%nat ee false with "Hcg Hpc Hi120 [Hec]").
    { rgall. iEval (rewrite HB6ea). iExact "Hec". }
    iApply wp_next_off_intro. iIntros "Hcg Hpc Hec". rgall.
    iEval (rewrite HB6ea HB6a5 trunc32_sext) in "Hec".
    assert (Hp124 : add_vec_int (mword_of_int (CT + 0x120) : mword 64) 4
                    = mword_of_int (CT + 0x124)) by pcw.
    iEval (rewrite Hp124) in "Hpc".
    (* +0x124 li a0,256 ; +0x128 jal consputc *)
    iApply (wp_li4_s_sconf (mword_of_int (CT + 0x124)) Ra0 (mword_of_int 256 : mword 12)
              (mword_of_int 256 : mword 64) B6 (trap_res b + (K - 6))%nat false
              ltac:(nz) ltac:(rdok) ltac:(pcw) with "Hcg Hpc Hi124").
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    set (B7 := <[Regidx Ra0 := regval_into_reg (mword_of_int 256 : mword 64)]> B6).
    assert (Hp128 : add_vec_int (mword_of_int (CT + 0x124) : mword 64) 4
                    = mword_of_int (CT + 0x128)) by pcw.
    iEval (rewrite Hp128) in "Hpc".
    iApply (wp_jal_s_sconf (mword_of_int (CT + 0x128)) Rra (mword_of_int 2096806 : mword 21)
              B7 (trap_res b + (K - 6))%nat false ltac:(nz) ltac:(rdok)
              ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi128").
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    set (B8 := <[Regidx Rra := regval_into_reg
        (add_vec_int (mword_of_int (CT + 0x128) : mword 64) 4)]> B7).
    assert (Hjcp : add_vec (mword_of_int (CT + 0x128) : mword 64)
                     (sign_extend' 64 (mword_of_int 2096806 : mword 21))
                   = mword_of_int KernelSyms.consputc) by pcw.
    iEval (rewrite Hjcp) in "Hpc".
    assert (HB8ra : B8 !!! Regidx Rra
                    = add_vec_int (mword_of_int (CT + 0x128) : mword 64) 4)
      by (rewrite /B8; apply upd_eq).
    iApply (Consputc.wp_consputc_sconf γtx γu γv B8
              (trap_res b + (K - 6))%nat [] (S lvl) eb C false pme ({[lock_rank "cons"]} ∪ lks)
              ltac:(unfold consoleintr_stack, consputc_stack in *; lia) ltac:(lia)
              with "Hcg Hcnt Ht Hpc Hpanic Hdev Htxl Hsub").
    all: try lkbelow.
    iApply wp_next_off_intro. iIntros (mcp cs) "Hcg Hcnt Hpc [%Hcpcs %Hcpra] _". rgall.
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
              ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi12c").
    iApply wp_next_off_intro. iApply bi.later_intro. iIntros "Hcg Hpc". rgall.
    assert (Hj104 : add_vec (mword_of_int (CT + 0x12c) : mword 64)
                      (sign_extend' 64 (sign_extend' 21
                         (concat_vec (mword_of_int 2028 : mword 11) ('b"0"))))
                    = mword_of_int (CT + 0x104)) by pcw.
    iEval (rewrite Hj104) in "Hpc".
    iSpecialize ("EXIT" $! CIDq with "[%]"); [exact Hchain|].
    iApply ("EXIT" $! mcp with "[%] [%] Hcg Hpc Hcnt Hpay Hlocked
              [Hrc Hwc Hec Hdat] Hrest").
    - rewrite (HthrM csp_rs1 ltac:(vm_compute; reflexivity)). exact Hsp.
    - exact (ct_cs_hi_thr mcp M m0 HthrM Hcs).
    - iExists rr, ww, ee1, bs. iFrame "Hrc Hwc Hec Hdat". iPureIntro. exact Hlenb.
  Qed.

  (* =================================================================== *)
  (*  [C('U')] (+0x092): the kill-line arm's PREAMBLE.  It shrink-wraps s2 *)
  (*  and s3 into slots 4 and 5 -- the one arm that uses them -- hoists    *)
  (*  &cons, '\n' and BACKSPACE into s1/s2/s3, and then either enters the  *)
  (*  loop or, on an already-empty line, leaves through the restore stub.  *)
  (* =================================================================== *)
  Lemma ct_kill_pre `{CIDq : CpuId}
      (γc : gname) (pme : mword 64) (m0 M : regfile) (K lvl : nat) (eb : bool)
      (C : iProp Σ) (b : bool) (sp0 : mword 64) (lks : gset nat) :
    M !!! Regidx csp_rs1 = pa_stk sp0 6%nat ->
    ct_cs_hi M m0 ->
    (b = false \/ pme = zero_reg -> (CIDq : CPU) = (CID : CPU)) ->
    (* same "cons" bound as the sibling arms: this one reaches consputc,
       whose cone runs up to "uart" (15). *)
    locks_below lks (lock_rank "cons") ->
    kernel_text -∗
    sie_cap_gpr M (trap_res b + (K - 6))%nat false pme -∗
    pc_is (mword_of_int (CT + 0x92)) -∗
    cpu_own (S lvl) eb pme C false ({[lock_rank "cons"]} ∪ lks) -∗
    arm_pay lvl eb pme -∗
    locked γc cpu_id -∗
    cons_res -∗
    ct_rest sp0 -∗
    ct_kill_prop (CID0 := CID) γc pme m0 K lvl eb C b sp0 lks -∗
    ct_exit_prop (CID0 := CID) γc pme m0 K lvl eb C b sp0 lks -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hsp Hcs Hchain Hbelow.
    pose proof (ct_cs_hi_top M m0 Hcs) as Htop.
    destruct Hcs as (HS2 & HS3 & _ & _ & _ & _ & _ & _ & _ & _).
    iIntros "#Ht Hcg Hpc Hcnt Hpay Hlocked Hres Hrest KILL EXIT".
    iPoseProof (cnti_092 with "Ht") as "Hi092".
    iPoseProof (cnti_094 with "Ht") as "Hi094".
    iPoseProof (cnti_096 with "Ht") as "Hi096".
    iPoseProof (cnti_09a with "Ht") as "Hi09a".
    iPoseProof (cnti_09e with "Ht") as "Hi09e".
    iPoseProof (cnti_0a2 with "Ht") as "Hi0a2".
    iPoseProof (cnti_0a6 with "Ht") as "Hi0a6".
    iPoseProof (cnti_0aa with "Ht") as "Hi0aa".
    iPoseProof (cnti_0ae with "Ht") as "Hi0ae".
    iPoseProof (cnti_0b0 with "Ht") as "Hi0b0".
    iPoseProof (cnti_0b4 with "Ht") as "Hi0b4".
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
              M (trap_res b + (K - 6))%nat u4 false with "Hcg Hpc Hi092 [H4]").
    { iEval (rewrite Hsp Hb4). iExact "H4". }
    iApply wp_next_off_intro. iIntros "Hcg Hpc H4". rgall.
    iEval (rewrite Hsp Hb4 HS2) in "H4".
    assert (Hp094 : add_vec_int (mword_of_int (CT + 0x92) : mword 64) 2
                    = mword_of_int (CT + 0x94)) by pcw.
    iEval (rewrite Hp094) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (CT + 0x94)) (mword_of_int 1 : mword 6) Rs3
              M (trap_res b + (K - 6))%nat u5 false with "Hcg Hpc Hi094 [H5]").
    { iEval (rewrite Hsp Hb5). iExact "H5". }
    iApply wp_next_off_intro. iIntros "Hcg Hpc H5". rgall.
    iEval (rewrite Hsp Hb5 HS3) in "H5".
    assert (Hp096 : add_vec_int (mword_of_int (CT + 0x94) : mword 64) 2
                    = mword_of_int (CT + 0x96)) by pcw.
    iEval (rewrite Hp096) in "Hpc".
    (* ---- +0x096/+0x09a : a4 := &cons ---- *)
    iApply (wp_auipc_s_sconf (mword_of_int (CT + 0x96)) Ra4 (mword_of_int 18 : mword 20)
              M (trap_res b + (K - 6))%nat false ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi096").
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    set (E1 := <[Regidx Ra4 := regval_into_reg
        (add_vec (mword_of_int (CT + 0x96) : mword 64)
           (auipc_off (mword_of_int 18 : mword 20)))]> M).
    assert (Hp09a : add_vec_int (mword_of_int (CT + 0x96) : mword 64) 4
                    = mword_of_int (CT + 0x9a)) by pcw.
    iEval (rewrite Hp09a) in "Hpc".
    iApply (wp_addi4_s_sconf (mword_of_int (CT + 0x9a)) Ra4 Ra4 (mword_of_int 3950 : mword 12)
              E1 (trap_res b + (K - 6))%nat false ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi09a").
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    set (E2 := <[Regidx Ra4 := regval_into_reg
        (add_vec (E1 !!! Regidx Ra4) (sign_extend' 64 (mword_of_int 3950 : mword 12)))]> E1).
    assert (HE2a4 : E2 !!! Regidx Ra4 = a_cons).
    { rewrite /E2 upd_eq /E1 upd_eq /a_cons. apply bv_eq; vm_compute; reflexivity. }
    assert (Hp09e : add_vec_int (mword_of_int (CT + 0x9a) : mword 64) 4
                    = mword_of_int (CT + 0x9e)) by pcw.
    iEval (rewrite Hp09e) in "Hpc".
    (* ---- +0x09e lw a5,160(a4) ; +0x0a2 lw a4,156(a4) ---- *)
    iDestruct "Hres" as (rr ww ee bs) "(Hrc & Hwc & Hec & %Hlenb & Hdat)".
    assert (Hea : add_vec (E2 !!! Regidx Ra4)
                    (sign_extend' 64 (mword_of_int 160 : mword 12)) = a_cons_e)
      by (rewrite HE2a4; reflexivity).
    iApply (wp_lw_s_sconf (mword_of_int (CT + 0x9e)) Ra5 Ra4 (mword_of_int 160 : mword 12)
              E2 (trap_res b + (K - 6))%nat ee false ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hi09e [Hec]").
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
    iApply (wp_lw_s_sconf (mword_of_int (CT + 0xa2)) Ra4 Ra4 (mword_of_int 156 : mword 12)
              E3 (trap_res b + (K - 6))%nat ww false ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hi0a2 [Hwc]").
    { rgall. iEval (rewrite Hwa). iExact "Hwc". }
    iApply wp_next_off_intro. iIntros "Hcg Hpc Hwc". rgall. iEval (rewrite Hwa) in "Hwc".
    set (E4 := <[Regidx Ra4 := regval_into_reg (sign_extend' 64 ww)]> E3).
    assert (Hp0a6 : add_vec_int (mword_of_int (CT + 0xa2) : mword 64) 4
                    = mword_of_int (CT + 0xa6)) by pcw.
    iEval (rewrite Hp0a6) in "Hpc".
    (* ---- +0x0a6/+0x0aa : s1 := &cons ---- *)
    iApply (wp_auipc_s_sconf (mword_of_int (CT + 0xa6)) Rs1 (mword_of_int 18 : mword 20)
              E4 (trap_res b + (K - 6))%nat false ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi0a6").
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    set (E5 := <[Regidx Rs1 := regval_into_reg
        (add_vec (mword_of_int (CT + 0xa6) : mword 64)
           (auipc_off (mword_of_int 18 : mword 20)))]> E4).
    assert (Hp0aa : add_vec_int (mword_of_int (CT + 0xa6) : mword 64) 4
                    = mword_of_int (CT + 0xaa)) by pcw.
    iEval (rewrite Hp0aa) in "Hpc".
    iApply (wp_addi4_s_sconf (mword_of_int (CT + 0xaa)) Rs1 Rs1 (mword_of_int 3934 : mword 12)
              E5 (trap_res b + (K - 6))%nat false ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi0aa").
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    set (E6 := <[Regidx Rs1 := regval_into_reg
        (add_vec (E5 !!! Regidx Rs1) (sign_extend' 64 (mword_of_int 3934 : mword 12)))]> E5).
    assert (HE6s1 : E6 !!! Regidx Rs1 = a_cons).
    { rewrite /E6 upd_eq /E5 upd_eq /a_cons. apply bv_eq; vm_compute; reflexivity. }
    assert (Hp0ae : add_vec_int (mword_of_int (CT + 0xaa) : mword 64) 4
                    = mword_of_int (CT + 0xae)) by pcw.
    iEval (rewrite Hp0ae) in "Hpc".
    (* ---- +0x0ae c.li s2,10 ; +0x0b0 li s3,256 : the loop's two constants ---- *)
    iApply (wp_cli_s_sconf (mword_of_int (CT + 0xae)) Rs2 (mword_of_int 10 : mword 6)
              (mword_of_int 10 : mword 64) E6 (trap_res b + (K - 6))%nat false
              ltac:(nz) ltac:(rdok) ltac:(pcw) with "Hcg Hpc Hi0ae").
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    set (E7 := <[Regidx Rs2 := regval_into_reg (mword_of_int 10 : mword 64)]> E6).
    assert (Hp0b0 : add_vec_int (mword_of_int (CT + 0xae) : mword 64) 2
                    = mword_of_int (CT + 0xb0)) by pcw.
    iEval (rewrite Hp0b0) in "Hpc".
    iApply (wp_li4_s_sconf (mword_of_int (CT + 0xb0)) Rs3 (mword_of_int 256 : mword 12)
              (mword_of_int 256 : mword 64) E7 (trap_res b + (K - 6))%nat false
              ltac:(nz) ltac:(rdok) ltac:(pcw) with "Hcg Hpc Hi0b0").
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
                ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi0b4").
      iApply bi.later_intro. iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
      assert (Hj0e4 : add_vec (mword_of_int (CT + 0xb4) : mword 64)
                        (sign_extend' 64 (mword_of_int 48 : mword 13))
                      = mword_of_int (CT + 0xe4)) by pcw.
      iEval (rewrite Hj0e4) in "Hpc".
      iPoseProof (cnti_0e4 with "Ht") as "Hi0e4".
      iPoseProof (cnti_0e6 with "Ht") as "Hi0e6".
      iPoseProof (cnti_0e8 with "Ht") as "Hi0e8".
      iApply (ct_restore23 (CIDq := CIDq) γc pme m0 E8 K lvl eb C _ sp0
                (mword_of_int (CT + 0xe4)) (mword_of_int (CT + 0xe6))
                (mword_of_int (CT + 0xe8)) (mword_of_int 14 : mword 11) lks
                HE8sp HE8top
                ltac:(pcw) ltac:(pcw) ltac:(pcw) ltac:(vm_compute; reflexivity)
                Hchain Hbelow
                with "Hi0e4 Hi0e6 Hi0e8 Hcg Hpc Hcnt Hpay Hlocked
                      [Hrc Hwc Hec Hdat] H4 H5 H6 EXIT").
      iExists rr, ww, ee, bs. iFrame "Hrc Hwc Hec Hdat". iPureIntro. exact Hlenb. }
    (* ---- the line is not empty: enter the loop at +0x0b8 ---- *)
    iApply (wp_beq_fall_s_sconf (mword_of_int (CT + 0xb4)) (mword_of_int 48 : mword 13)
              Ra5 Ra4 E8 (trap_res b + (K - 6))%nat false ltac:(nz) ltac:(nz)
              ltac:(rgall; rewrite HE8a4 HE8a5; exact Hemp) with "Hcg Hpc Hi0b4").
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    assert (Hp0b8 : add_vec_int (mword_of_int (CT + 0xb4) : mword 64) 4
                    = mword_of_int (CT + 0xb8)) by pcw.
    iEval (rewrite Hp0b8) in "Hpc".
    iSpecialize ("KILL" $! CIDq with "[%]"); [exact Hchain|].
    iApply ("KILL" $! E8 rr ww ee bs with "[%] [%] [%] [%] [%] [%] [%]
              EXIT Hcg Hpc Hcnt Hpay Hlocked Hrc Hwc Hec Hdat H4 H5 H6");
      [ exact HE8sp | exact HE8s1 | exact HE8s2 | exact HE8s3 | exact HE8a5
      | exact HE8top | exact Hlenb ].
  Qed.

  (* =================================================================== *)
  (*  [STORE] (+0x04e): the default arm's tail -- echo the byte, append it *)
  (*  to the ring, and decide whether the line is complete.  THREE ways    *)
  (*  reach [WAKE] from here ('\n', C('D'), a full ring) and one leaves.   *)
  (* =================================================================== *)
  Lemma ct_store `{CIDq : CpuId}
      (γtx γc : gname) (γu : uart_names) (γv : disk_names)
      (pme : mword 64) (m0 M : regfile) (K lvl : nat) (eb : bool)
      (C : iProp Σ) (b : bool) (sp0 : mword 64) (cv : mword 64) (lks : gset nat) :
    M !!! Regidx csp_rs1 = pa_stk sp0 6%nat ->
    M !!! Regidx Rs1 = cv ->
    ct_cs_hi M m0 ->
    (consoleintr_stack <= K)%nat ->
    (Z.of_nat lvl + 2 < 2 ^ 31)%Z ->
    (b = false \/ pme = zero_reg -> (CIDq : CPU) = (CID : CPU)) ->
    (* same "cons" bound as the sibling arms: the store path reaches
       consputc, whose cone runs up to "uart" (15). *)
    locks_below lks (lock_rank "cons") ->
    kernel_text -∗ panic_wp_any -∗
    dev_inv γu γv -∗ is_txlock γtx γu -∗ uart_sent_sub γu [] -∗
    sie_cap_gpr M (trap_res b + (K - 6))%nat false pme -∗
    pc_is (mword_of_int (CT + 0x4e)) -∗
    cpu_own (S lvl) eb pme C false ({[lock_rank "cons"]} ∪ lks) -∗
    arm_pay lvl eb pme -∗
    locked γc cpu_id -∗
    cons_res -∗
    ct_rest sp0 -∗
    ct_wake_prop (CID0 := CID) γc pme m0 K lvl eb C b sp0 lks -∗
    ct_exit_prop (CID0 := CID) γc pme m0 K lvl eb C b sp0 lks -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hsp Hs1 Hcs HK Hlvl Hchain Hbelow.
    iIntros "#Ht #Hpanic #Hdev #Htxl #Hsub Hcg Hpc Hcnt Hpay Hlocked Hres Hrest WAKE EXIT".
    iPoseProof (cnti_04e with "Ht") as "Hi04e".
    iPoseProof (cnti_050 with "Ht") as "Hi050".
    iPoseProof (cnti_054 with "Ht") as "Hi054".
    iPoseProof (cnti_058 with "Ht") as "Hi058".
    iPoseProof (cnti_05c with "Ht") as "Hi05c".
    iPoseProof (cnti_060 with "Ht") as "Hi060".
    iPoseProof (cnti_064 with "Ht") as "Hi064".
    iPoseProof (cnti_066 with "Ht") as "Hi066".
    iPoseProof (cnti_06a with "Ht") as "Hi06a".
    iPoseProof (cnti_06e with "Ht") as "Hi06e".
    iPoseProof (cnti_070 with "Ht") as "Hi070".
    iPoseProof (cnti_074 with "Ht") as "Hi074".
    iPoseProof (cnti_078 with "Ht") as "Hi078".
    (* ---- +0x04e c.mv a0,s1 ; +0x050 jal consputc : the echo ---- *)
    iApply (wp_cmv_s_sconf (mword_of_int (CT + 0x4e)) Ra0 Rs1 M
              (trap_res b + (K - 6))%nat false ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi04e").
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    iEval (rewrite Hs1 w32_zero_add) in "Hcg".
    set (F1 := <[Regidx Ra0 := regval_into_reg cv]> M).
    assert (Hp050 : add_vec_int (mword_of_int (CT + 0x4e) : mword 64) 2
                    = mword_of_int (CT + 0x50)) by pcw.
    iEval (rewrite Hp050) in "Hpc".
    iApply (wp_jal_s_sconf (mword_of_int (CT + 0x50)) Rra (mword_of_int 2097022 : mword 21)
              F1 (trap_res b + (K - 6))%nat false ltac:(nz) ltac:(rdok)
              ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi050").
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    set (F2 := <[Regidx Rra := regval_into_reg
        (add_vec_int (mword_of_int (CT + 0x50) : mword 64) 4)]> F1).
    assert (Hjcp : add_vec (mword_of_int (CT + 0x50) : mword 64)
                     (sign_extend' 64 (mword_of_int 2097022 : mword 21))
                   = mword_of_int KernelSyms.consputc) by pcw.
    iEval (rewrite Hjcp) in "Hpc".
    assert (HF2ra : F2 !!! Regidx Rra
                    = add_vec_int (mword_of_int (CT + 0x50) : mword 64) 4)
      by (rewrite /F2; apply upd_eq).
    iApply (Consputc.wp_consputc_sconf γtx γu γv F2
              (trap_res b + (K - 6))%nat [] (S lvl) eb C false pme ({[lock_rank "cons"]} ∪ lks)
              ltac:(unfold consoleintr_stack, consputc_stack in *; lia) ltac:(lia)
              with "Hcg Hcnt Ht Hpc Hpanic Hdev Htxl Hsub").
    all: try lkbelow.
    iApply wp_next_off_intro. iIntros (mcp cs) "Hcg Hcnt Hpc [%Hcpcs %Hcpra] _". rgall.
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
              mcp (trap_res b + (K - 6))%nat false ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi054").
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    set (F3 := <[Regidx Ra4 := regval_into_reg
        (add_vec (mword_of_int (CT + 0x54) : mword 64)
           (auipc_off (mword_of_int 18 : mword 20)))]> mcp).
    assert (Hp058 : add_vec_int (mword_of_int (CT + 0x54) : mword 64) 4
                    = mword_of_int (CT + 0x58)) by pcw.
    iEval (rewrite Hp058) in "Hpc".
    iApply (wp_addi4_s_sconf (mword_of_int (CT + 0x58)) Ra4 Ra4 (mword_of_int 4016 : mword 12)
              F3 (trap_res b + (K - 6))%nat false ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi058").
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    set (F4 := <[Regidx Ra4 := regval_into_reg
        (add_vec (F3 !!! Regidx Ra4) (sign_extend' 64 (mword_of_int 4016 : mword 12)))]> F3).
    assert (HF4a4 : F4 !!! Regidx Ra4 = a_cons).
    { rewrite /F4 upd_eq /F3 upd_eq /a_cons. apply bv_eq; vm_compute; reflexivity. }
    assert (Hp05c : add_vec_int (mword_of_int (CT + 0x58) : mword 64) 4
                    = mword_of_int (CT + 0x5c)) by pcw.
    iEval (rewrite Hp05c) in "Hpc".
    (* ---- +0x05c lw a3,160(a4) : a3 := cons.e ---- *)
    iDestruct "Hres" as (rr ww ee bs) "(Hrc & Hwc & Hec & %Hlenb & Hdat)".
    assert (Hea : add_vec (F4 !!! Regidx Ra4)
                    (sign_extend' 64 (mword_of_int 160 : mword 12)) = a_cons_e)
      by (rewrite HF4a4; reflexivity).
    iApply (wp_lw_s_sconf (mword_of_int (CT + 0x5c)) Ra3 Ra4 (mword_of_int 160 : mword 12)
              F4 (trap_res b + (K - 6))%nat ee false ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hi05c [Hec]").
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
              F5 (trap_res b + (K - 6))%nat false ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi060").
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
              (trap_res b + (K - 6))%nat false ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi064").
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
    iApply (wp_sw_s_sconf (mword_of_int (CT + 0x66)) Ra5 Ra4 (mword_of_int 160 : mword 12)
              F7 (trap_res b + (K - 6))%nat ee false with "Hcg Hpc Hi066 [Hec]").
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
              ltac:(nz) ltac:(rdok) Hwv with "Hcg Hpc Hi06a").
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
              (trap_res b + (K - 6))%nat false ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi06e").
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    iEval (rewrite HF8a4 HF8a3) in "Hcg".
    set (F9 := <[Regidx Ra4 := regval_into_reg
        (add_vec a_cons (mword_of_int (Z.of_nat idx) : mword 64))]> F8).
    assert (Hp070 : add_vec_int (mword_of_int (CT + 0x6e) : mword 64) 2
                    = mword_of_int (CT + 0x70)) by pcw.
    iEval (rewrite Hp070) in "Hpc".
    (* ---- +0x070 sb s1,24(a4) : the byte lands in the ring ---- *)
    destruct (cons_data_lookup_lt bs idx Hlenb Hidxlt) as [db Hlk].
    iDestruct (cons_data_upd bs idx db (trunc8 cv) Hlk with "Hdat") as "[Hbyte Hdback]".
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
    iApply (wp_sb_s_sconf (mword_of_int (CT + 0x70)) Rs1 Ra4 (mword_of_int 24 : mword 12)
              F9 (trap_res b + (K - 6))%nat db false with "Hcg Hpc Hi070 [Hbyte]").
    { rgall. iEval (rewrite Hbaddr). iExact "Hbyte". }
    iApply wp_next_off_intro. iIntros "Hcg Hpc Hbyte". rgall.
    iEval (rewrite Hbaddr HF9s1) in "Hbyte".
    iDestruct ("Hdback" with "Hbyte") as "Hdat".
    iAssert (cons_res) with "[Hrc Hwc Hec Hdat]" as "Hres".
    { iExists rr, ww, ee1, (<[idx := trunc8 cv]> bs).
      iFrame "Hrc Hwc Hec Hdat". iPureIntro. rewrite length_insert. exact Hlenb. }
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
              F9 (trap_res b + (K - 6))%nat false ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi074").
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
                ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi078").
      iApply bi.later_intro. iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
      assert (Hj156 : add_vec (mword_of_int (CT + 0x78) : mword 64)
                        (sign_extend' 64 (sign_extend' 13
                           (concat_vec (mword_of_int 111 : mword 8) ('b"0"))))
                      = mword_of_int (CT + 0x156)) by pcw.
      iEval (rewrite Hj156) in "Hpc".
      iSpecialize ("WAKE" $! CIDq with "[%]"); [exact Hchain|].
      iApply ("WAKE" $! F10 (sign_extend' 64 ee1) with "[%] [%] [%]
                Hcg Hpc Hcnt Hpay Hlocked Hres Hrest EXIT");
        [ exact Hsp10 | exact HF10a2 | exact Hcshi10 ]. }
    (* ---- +0x07a c.addi s1,s1,-4 ; +0x07c c.beqz s1 : is it C('D')? ---- *)
    iApply (wp_cbeqz_fall_s_sconf (mword_of_int (CT + 0x78)) (mword_of_int 111 : mword 8)
              (Cregidx (mword_of_int 6)) Ra4 F10 (trap_res b + (K - 6))%nat false
              ltac:(vm_compute; reflexivity) ltac:(nz)
              ltac:(rgall; rewrite HF10a4; exact Hnl) with "Hcg Hpc Hi078").
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    assert (Hp07a : add_vec_int (mword_of_int (CT + 0x78) : mword 64) 2
                    = mword_of_int (CT + 0x7a)) by pcw.
    iEval (rewrite Hp07a) in "Hpc".
    iPoseProof (cnti_07a with "Ht") as "Hi07a".
    iPoseProof (cnti_07c with "Ht") as "Hi07c".
    assert (HF10s1 : F10 !!! Regidx Rs1 = cv)
      by (rewrite /F10 upd_ne; [exact HF9s1 | reg_neq]).
    iApply (wp_caddi_s_sconf (mword_of_int (CT + 0x7a)) Rs1 (mword_of_int 60 : mword 6)
              F10 (trap_res b + (K - 6))%nat false ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi07a").
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
                ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi07c").
      iApply bi.later_intro. iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
      assert (Hj156 : add_vec (mword_of_int (CT + 0x7c) : mword 64)
                        (sign_extend' 64 (sign_extend' 13
                           (concat_vec (mword_of_int 109 : mword 8) ('b"0"))))
                      = mword_of_int (CT + 0x156)) by pcw.
      iEval (rewrite Hj156) in "Hpc".
      iSpecialize ("WAKE" $! CIDq with "[%]"); [exact Hchain|].
      iApply ("WAKE" $! F11 (sign_extend' 64 ee1) with "[%] [%] [%]
                Hcg Hpc Hcnt Hpay Hlocked Hres Hrest EXIT");
        [ exact Hsp11 | exact HF11a2 | exact Hcshi11 ]. }
    (* ---- +0x07e .. +0x08c : is the ring now full? ---- *)
    iApply (wp_cbeqz_fall_s_sconf (mword_of_int (CT + 0x7c)) (mword_of_int 109 : mword 8)
              (Cregidx (mword_of_int 1)) Rs1 F11 (trap_res b + (K - 6))%nat false
              ltac:(vm_compute; reflexivity) ltac:(nz)
              ltac:(rgall; rewrite HF11s1; exact Heof) with "Hcg Hpc Hi07c").
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    assert (Hp07e : add_vec_int (mword_of_int (CT + 0x7c) : mword 64) 2
                    = mword_of_int (CT + 0x7e)) by pcw.
    iEval (rewrite Hp07e) in "Hpc".
    iPoseProof (cnti_07e with "Ht") as "Hi07e".
    iPoseProof (cnti_082 with "Ht") as "Hi082".
    iPoseProof (cnti_086 with "Ht") as "Hi086".
    iPoseProof (cnti_088 with "Ht") as "Hi088".
    iPoseProof (cnti_08c with "Ht") as "Hi08c".
    iPoseProof (cnti_090 with "Ht") as "Hi090".
    iApply (wp_auipc_s_sconf (mword_of_int (CT + 0x7e)) Ra4 (mword_of_int 18 : mword 20)
              F11 (trap_res b + (K - 6))%nat false ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi07e").
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    set (F12 := <[Regidx Ra4 := regval_into_reg
        (add_vec (mword_of_int (CT + 0x7e) : mword 64)
           (auipc_off (mword_of_int 18 : mword 20)))]> F11).
    assert (Hp082 : add_vec_int (mword_of_int (CT + 0x7e) : mword 64) 4
                    = mword_of_int (CT + 0x82)) by pcw.
    iEval (rewrite Hp082) in "Hpc".
    (* +0x082 lw a4,14(a4) : a4 := cons.r, off the auipc base *)
    iDestruct "Hres" as (rr' ww' ee' bs') "(Hrc & Hwc & Hec & %Hlenb' & Hdat)".
    assert (Hra : add_vec (F12 !!! Regidx Ra4)
                    (sign_extend' 64 (mword_of_int 30 : mword 12)) = a_cons_r).
    { rewrite /F12 upd_eq /a_cons_r /coff_of /a_cons. apply bv_eq; vm_compute; reflexivity. }
    iApply (wp_lw_s_sconf (mword_of_int (CT + 0x82)) Ra4 Ra4 (mword_of_int 30 : mword 12)
              F12 (trap_res b + (K - 6))%nat rr' false ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hi082 [Hrc]").
    { rgall. iEval (rewrite Hra). iExact "Hrc". }
    iApply wp_next_off_intro. iIntros "Hcg Hpc Hrc". rgall. iEval (rewrite Hra) in "Hrc".
    set (F13 := <[Regidx Ra4 := regval_into_reg (sign_extend' 64 rr')]> F12).
    iAssert (cons_res) with "[Hrc Hwc Hec Hdat]" as "Hres".
    { iExists rr', ww', ee', bs'. iFrame "Hrc Hwc Hec Hdat". iPureIntro. exact Hlenb'. }
    assert (Hp086 : add_vec_int (mword_of_int (CT + 0x82) : mword 64) 4
                    = mword_of_int (CT + 0x86)) by pcw.
    iEval (rewrite Hp086) in "Hpc".
    (* +0x086 c.subw a5,a5,a4 *)
    assert (HF13a4 : F13 !!! Regidx Ra4 = sign_extend' 64 rr')
      by (rewrite /F13; apply upd_eq).
    assert (HF13a5 : F13 !!! Regidx Ra5 = sign_extend' 64 ee1).
    { rewrite /F13 upd_ne; [| reg_neq]. rewrite /F12 upd_ne; [| reg_neq].
      rewrite /F11 upd_ne; [| reg_neq]. rewrite /F10 upd_ne; [| reg_neq].
      rewrite /F9 upd_ne; [| reg_neq]. rewrite /F8 upd_ne; [| reg_neq]. exact HF7a5. }
    iApply (wp_csubw_s_sconf (mword_of_int (CT + 0x86)) Ra5 Ra5 Ra4 F13
              (trap_res b + (K - 6))%nat false ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi086").
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    iEval (rewrite HF13a4 HF13a5 ct_subw_sext) in "Hcg".
    set (F14 := <[Regidx Ra5 := regval_into_reg
        (sign_extend' 64 (sub_vec ee1 rr'))]> F13).
    assert (Hp088 : add_vec_int (mword_of_int (CT + 0x86) : mword 64) 2
                    = mword_of_int (CT + 0x88)) by pcw.
    iEval (rewrite Hp088) in "Hpc".
    iApply (wp_li4_s_sconf (mword_of_int (CT + 0x88)) Ra4 (mword_of_int 128 : mword 12)
              (mword_of_int 128 : mword 64) F14 (trap_res b + (K - 6))%nat false
              ltac:(nz) ltac:(rdok) ltac:(pcw) with "Hcg Hpc Hi088").
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    set (F15 := <[Regidx Ra4 := regval_into_reg (mword_of_int 128 : mword 64)]> F14).
    assert (HF15a4 : F15 !!! Regidx Ra4 = (mword_of_int 128 : mword 64))
      by (rewrite /F15; apply upd_eq).
    assert (HF15a5 : F15 !!! Regidx Ra5 = sign_extend' 64 (sub_vec ee1 rr'))
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
    destruct (neq_vec (sign_extend' 64 (sub_vec ee1 rr') : mword 64)
                (mword_of_int 128 : mword 64)) eqn:Hfull.
    { (* the ring is NOT full: nothing to hand over, leave *)
      iApply (wp_bne_taken_s_sconf (mword_of_int (CT + 0x8c)) (mword_of_int 120 : mword 13)
                Ra4 Ra5 F15 (trap_res b + (K - 6))%nat false ltac:(nz) ltac:(nz)
                ltac:(rgall; rewrite HF15a4 HF15a5; exact Hfull)
                ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi08c").
      iApply bi.later_intro. iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
      assert (Hj104 : add_vec (mword_of_int (CT + 0x8c) : mword 64)
                        (sign_extend' 64 (mword_of_int 120 : mword 13))
                      = mword_of_int (CT + 0x104)) by pcw.
      iEval (rewrite Hj104) in "Hpc".
      iSpecialize ("EXIT" $! CIDq with "[%]"); [exact Hchain|].
      iApply ("EXIT" $! F15 with "[%] [%] Hcg Hpc Hcnt Hpay Hlocked Hres Hrest");
        [ exact Hsp15 | exact Hcshi15 ]. }
    (* the ring is exactly full: hand the line over at +0x090 *)
    iApply (wp_bne_fall_s_sconf (mword_of_int (CT + 0x8c)) (mword_of_int 120 : mword 13)
              Ra4 Ra5 F15 (trap_res b + (K - 6))%nat false ltac:(nz) ltac:(nz)
              ltac:(rgall; rewrite HF15a4 HF15a5; exact Hfull) with "Hcg Hpc Hi08c").
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    assert (Hp090 : add_vec_int (mword_of_int (CT + 0x8c) : mword 64) 4
                    = mword_of_int (CT + 0x90)) by pcw.
    iEval (rewrite Hp090) in "Hpc".
    iApply (wp_cj_s_sconf (mword_of_int (CT + 0x90))
              (sign_extend' 21 (concat_vec (mword_of_int 99 : mword 11) ('b"0")))
              F15 (trap_res b + (K - 6))%nat false
              ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi090").
    iApply wp_next_off_intro. iApply bi.later_intro. iIntros "Hcg Hpc". rgall.
    assert (Hj156 : add_vec (mword_of_int (CT + 0x90) : mword 64)
                      (sign_extend' 64 (sign_extend' 21
                         (concat_vec (mword_of_int 99 : mword 11) ('b"0"))))
                    = mword_of_int (CT + 0x156)) by pcw.
    iEval (rewrite Hj156) in "Hpc".
    iSpecialize ("WAKE" $! CIDq with "[%]"); [exact Hchain|].
    iApply ("WAKE" $! F15 (sign_extend' 64 ee1) with "[%] [%] [%]
              Hcg Hpc Hcnt Hpay Hlocked Hres Hrest EXIT");
      [ exact Hsp15 | exact HF15a2 | exact Hcshi15 ].
  Qed.

  (* =================================================================== *)
  (*  [DEFAULT] (+0x02c): the guard.  A NUL byte and a full ring both      *)
  (*  leave without touching anything; '\r' is rewritten to '\n' by the    *)
  (*  arm at +0x12e; everything else falls into [ct_store].                *)
  (* =================================================================== *)
  Lemma ct_dflt `{CIDq : CpuId}
      (γtx γc : gname) (γu : uart_names) (γv : disk_names)
      (pme : mword 64) (m0 M : regfile) (K lvl : nat) (eb : bool)
      (C : iProp Σ) (b : bool) (sp0 : mword 64) (cv : mword 64) (lks : gset nat) :
    M !!! Regidx csp_rs1 = pa_stk sp0 6%nat ->
    M !!! Regidx Rs1 = cv ->
    ct_cs_hi M m0 ->
    (consoleintr_stack <= K)%nat ->
    (Z.of_nat lvl + 2 < 2 ^ 31)%Z ->
    (b = false \/ pme = zero_reg -> (CIDq : CPU) = (CID : CPU)) ->
    (* same "cons" bound as the sibling arms: the default path reaches
       consputc, whose cone runs up to "uart" (15). *)
    locks_below lks (lock_rank "cons") ->
    kernel_text -∗ panic_wp_any -∗
    dev_inv γu γv -∗ is_txlock γtx γu -∗ uart_sent_sub γu [] -∗
    sie_cap_gpr M (trap_res b + (K - 6))%nat false pme -∗
    pc_is (mword_of_int (CT + 0x2c)) -∗
    cpu_own (S lvl) eb pme C false ({[lock_rank "cons"]} ∪ lks) -∗
    arm_pay lvl eb pme -∗
    locked γc cpu_id -∗
    cons_res -∗
    ct_rest sp0 -∗
    ct_wake_prop (CID0 := CID) γc pme m0 K lvl eb C b sp0 lks -∗
    ct_exit_prop (CID0 := CID) γc pme m0 K lvl eb C b sp0 lks -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hsp Hs1 Hcs HK Hlvl Hchain Hbelow.
    iIntros "#Ht #Hpanic #Hdev #Htxl #Hsub Hcg Hpc Hcnt Hpay Hlocked Hres Hrest WAKE EXIT".
    iPoseProof (cnti_02c with "Ht") as "Hi02c".
    (* ---- +0x02c c.beqz s1 : [c != 0] ---- *)
    destruct (eq_vec (cv : mword 64) (zero_reg : mword 64)) eqn:Hnul.
    { iApply (wp_cbeqz_taken_s_sconf (mword_of_int (CT + 0x2c)) (mword_of_int 108 : mword 8)
                (Cregidx (mword_of_int 1)) Rs1 M (trap_res b + (K - 6))%nat false
                ltac:(vm_compute; reflexivity) ltac:(nz)
                ltac:(rgall; rewrite Hs1; exact Hnul)
                ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi02c").
      iApply bi.later_intro. iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
      assert (Hj104 : add_vec (mword_of_int (CT + 0x2c) : mword 64)
                        (sign_extend' 64 (sign_extend' 13
                           (concat_vec (mword_of_int 108 : mword 8) ('b"0"))))
                      = mword_of_int (CT + 0x104)) by pcw.
      iEval (rewrite Hj104) in "Hpc".
      iSpecialize ("EXIT" $! CIDq with "[%]"); [exact Hchain|].
      iApply ("EXIT" $! M with "[%] [%] Hcg Hpc Hcnt Hpay Hlocked Hres Hrest");
        [ exact Hsp | exact Hcs ]. }
    iApply (wp_cbeqz_fall_s_sconf (mword_of_int (CT + 0x2c)) (mword_of_int 108 : mword 8)
              (Cregidx (mword_of_int 1)) Rs1 M (trap_res b + (K - 6))%nat false
              ltac:(vm_compute; reflexivity) ltac:(nz)
              ltac:(rgall; rewrite Hs1; exact Hnul) with "Hcg Hpc Hi02c").
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    assert (Hp02e : add_vec_int (mword_of_int (CT + 0x2c) : mword 64) 2
                    = mword_of_int (CT + 0x2e)) by pcw.
    iEval (rewrite Hp02e) in "Hpc".
    iPoseProof (cnti_02e with "Ht") as "Hi02e".
    iPoseProof (cnti_032 with "Ht") as "Hi032".
    iPoseProof (cnti_036 with "Ht") as "Hi036".
    iPoseProof (cnti_03a with "Ht") as "Hi03a".
    iPoseProof (cnti_03e with "Ht") as "Hi03e".
    iPoseProof (cnti_040 with "Ht") as "Hi040".
    iPoseProof (cnti_044 with "Ht") as "Hi044".
    iPoseProof (cnti_048 with "Ht") as "Hi048".
    iPoseProof (cnti_04a with "Ht") as "Hi04a".
    (* ---- +0x02e/+0x032 : a4 := &cons ---- *)
    iApply (wp_auipc_s_sconf (mword_of_int (CT + 0x2e)) Ra4 (mword_of_int 18 : mword 20)
              M (trap_res b + (K - 6))%nat false ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi02e").
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    set (G1 := <[Regidx Ra4 := regval_into_reg
        (add_vec (mword_of_int (CT + 0x2e) : mword 64)
           (auipc_off (mword_of_int 18 : mword 20)))]> M).
    assert (Hp032 : add_vec_int (mword_of_int (CT + 0x2e) : mword 64) 4
                    = mword_of_int (CT + 0x32)) by pcw.
    iEval (rewrite Hp032) in "Hpc".
    iApply (wp_addi4_s_sconf (mword_of_int (CT + 0x32)) Ra4 Ra4 (mword_of_int 4054 : mword 12)
              G1 (trap_res b + (K - 6))%nat false ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi032").
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    set (G2 := <[Regidx Ra4 := regval_into_reg
        (add_vec (G1 !!! Regidx Ra4) (sign_extend' 64 (mword_of_int 4054 : mword 12)))]> G1).
    assert (HG2a4 : G2 !!! Regidx Ra4 = a_cons).
    { rewrite /G2 upd_eq /G1 upd_eq /a_cons. apply bv_eq; vm_compute; reflexivity. }
    assert (Hp036 : add_vec_int (mword_of_int (CT + 0x32) : mword 64) 4
                    = mword_of_int (CT + 0x36)) by pcw.
    iEval (rewrite Hp036) in "Hpc".
    (* ---- +0x036 lw a5,160(a4) ; +0x03a lw a4,152(a4) ---- *)
    iDestruct "Hres" as (rr ww ee bs) "(Hrc & Hwc & Hec & %Hlenb & Hdat)".
    assert (Hea : add_vec (G2 !!! Regidx Ra4)
                    (sign_extend' 64 (mword_of_int 160 : mword 12)) = a_cons_e)
      by (rewrite HG2a4; reflexivity).
    iApply (wp_lw_s_sconf (mword_of_int (CT + 0x36)) Ra5 Ra4 (mword_of_int 160 : mword 12)
              G2 (trap_res b + (K - 6))%nat ee false ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hi036 [Hec]").
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
    iApply (wp_lw_s_sconf (mword_of_int (CT + 0x3a)) Ra4 Ra4 (mword_of_int 152 : mword 12)
              G3 (trap_res b + (K - 6))%nat rr false ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hi03a [Hrc]").
    { rgall. iEval (rewrite Hra). iExact "Hrc". }
    iApply wp_next_off_intro. iIntros "Hcg Hpc Hrc". rgall. iEval (rewrite Hra) in "Hrc".
    set (G4 := <[Regidx Ra4 := regval_into_reg (sign_extend' 64 rr)]> G3).
    iAssert (cons_res) with "[Hrc Hwc Hec Hdat]" as "Hres".
    { iExists rr, ww, ee, bs. iFrame "Hrc Hwc Hec Hdat". iPureIntro. exact Hlenb. }
    assert (Hp03e : add_vec_int (mword_of_int (CT + 0x3a) : mword 64) 4
                    = mword_of_int (CT + 0x3e)) by pcw.
    iEval (rewrite Hp03e) in "Hpc".
    (* ---- +0x03e c.subw a5,a5,a4 ; +0x040 li a4,127 ; +0x044 bltu ---- *)
    assert (HG4a4 : G4 !!! Regidx Ra4 = sign_extend' 64 rr)
      by (rewrite /G4; apply upd_eq).
    assert (HG4a5 : G4 !!! Regidx Ra5 = sign_extend' 64 ee).
    { rewrite /G4 upd_ne; [| reg_neq]. rewrite /G3; apply upd_eq. }
    iApply (wp_csubw_s_sconf (mword_of_int (CT + 0x3e)) Ra5 Ra5 Ra4 G4
              (trap_res b + (K - 6))%nat false ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi03e").
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    iEval (rewrite HG4a4 HG4a5 ct_subw_sext) in "Hcg".
    set (G5 := <[Regidx Ra5 := regval_into_reg (sign_extend' 64 (sub_vec ee rr))]> G4).
    assert (Hp040 : add_vec_int (mword_of_int (CT + 0x3e) : mword 64) 2
                    = mword_of_int (CT + 0x40)) by pcw.
    iEval (rewrite Hp040) in "Hpc".
    iApply (wp_li4_s_sconf (mword_of_int (CT + 0x40)) Ra4 (mword_of_int 127 : mword 12)
              (mword_of_int 127 : mword 64) G5 (trap_res b + (K - 6))%nat false
              ltac:(nz) ltac:(rdok) ltac:(pcw) with "Hcg Hpc Hi040").
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
                ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi044").
      iApply bi.later_intro. iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
      assert (Hj104 : add_vec (mword_of_int (CT + 0x44) : mword 64)
                        (sign_extend' 64 (mword_of_int 192 : mword 13))
                      = mword_of_int (CT + 0x104)) by pcw.
      iEval (rewrite Hj104) in "Hpc".
      iSpecialize ("EXIT" $! CIDq with "[%]"); [exact Hchain|].
      iApply ("EXIT" $! G6 with "[%] [%] Hcg Hpc Hcnt Hpay Hlocked Hres Hrest").
      - rewrite (HthrG6 csp_rs1 ltac:(vm_compute; reflexivity)). exact Hsp.
      - exact (ct_cs_hi_thr G6 M m0 HthrG6 Hcs). }
    iApply (wp_bltu_fall_s_sconf (mword_of_int (CT + 0x44)) (mword_of_int 192 : mword 13)
              Ra5 Ra4 G6 (trap_res b + (K - 6))%nat false ltac:(nz) ltac:(nz)
              ltac:(rgall; rewrite HG6a4 HG6a5; exact Hgd) with "Hcg Hpc Hi044").
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    assert (Hp048 : add_vec_int (mword_of_int (CT + 0x44) : mword 64) 4
                    = mword_of_int (CT + 0x48)) by pcw.
    iEval (rewrite Hp048) in "Hpc".
    (* ---- +0x048 c.li a5,13 ; +0x04a beq s1,a5 : the '\r' rewrite ---- *)
    iApply (wp_cli_s_sconf (mword_of_int (CT + 0x48)) Ra5 (mword_of_int 13 : mword 6)
              (mword_of_int 13 : mword 64) G6 (trap_res b + (K - 6))%nat false
              ltac:(nz) ltac:(rdok) ltac:(pcw) with "Hcg Hpc Hi048").
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
                ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi04a").
      iApply bi.later_intro. iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
      assert (Hj12e : add_vec (mword_of_int (CT + 0x4a) : mword 64)
                        (sign_extend' 64 (mword_of_int 228 : mword 13))
                      = mword_of_int (CT + 0x12e)) by pcw.
      iEval (rewrite Hj12e) in "Hpc".
      iApply (ct_cr (CIDq := CIDq) γtx γc γu γv pme m0 G7 K lvl eb C b sp0 lks
                HG7sp (ct_cs_hi_thr G7 M m0 HthrG7 Hcs) HK Hlvl Hchain Hbelow
                with "Ht Hpanic Hdev Htxl Hsub Hcg Hpc Hcnt Hpay Hlocked Hres Hrest
                      WAKE EXIT"). }
    iApply (wp_beq_fall_s_sconf (mword_of_int (CT + 0x4a)) (mword_of_int 228 : mword 13)
              Ra5 Rs1 G7 (trap_res b + (K - 6))%nat false ltac:(nz) ltac:(nz)
              ltac:(rgall; rewrite HG7s1 HG7a5; exact Hcr) with "Hcg Hpc Hi04a").
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    assert (Hp04e : add_vec_int (mword_of_int (CT + 0x4a) : mword 64) 4
                    = mword_of_int (CT + 0x4e)) by pcw.
    iEval (rewrite Hp04e) in "Hpc".
    iApply (ct_store (CIDq := CIDq) γtx γc γu γv pme m0 G7 K lvl eb C b sp0 cv lks
              HG7sp HG7s1 (ct_cs_hi_thr G7 M m0 HthrG7 Hcs) HK Hlvl Hchain Hbelow
              with "Ht Hpanic Hdev Htxl Hsub Hcg Hpc Hcnt Hpay Hlocked Hres Hrest
                    WAKE EXIT").
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
      (pme : mword 64) (lvl K : nat) (eb : bool) (C : iProp Σ) (b : bool) (lks : gset nat)
    : wp_consoleintr_sconf_body γu γv m γs pme lvl K eb C b lks.
  Proof.
    cbv beta delta [wp_consoleintr_sconf_body].
    intros rettgt HK Hlen Hlvl Hbelow.
    iIntros "Hcg Hcnt #Ht Hpc #Hpanic #Hpinv #Hdev #Hcaps Hcont".
    iDestruct "Hcaps" as (γtx γc) "(#Htxl & #Hlk & #Hsub)".
    iDestruct (cpu_own_eb_agree with "Hcg Hcnt") as %Hbm.
    set (sp0 := (m !!! Regidx csp_rs1 : mword 64)).
    assert (Hspm : m !!! Regidx csp_rs1 = sp0) by reflexivity.
    set (cv := (m !!! Regidx Ra0 : mword 64)).
    (* ================= PROLOGUE: the six-slot frame ==================== *)
    assert (Hpush : add_vec (m !!! Regidx csp_rs1)
                      (sign_extend' 64 (caddi16sp_imm (mword_of_int 61 : mword 6)))
                    = pa_stk (m !!! Regidx csp_rs1) 6%nat).
    { unfold pa_stk, add_vec_int. apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    iPoseProof (cnti_000 with "Ht") as "Hi000".
    iApply (wp_caddi16sp_push_s_sconf (mword_of_int CT) (mword_of_int 61 : mword 6) m K 6%nat b
              ltac:(unfold consoleintr_stack in HK; lia) Hpush with "Hcg Hpc Hi000").
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
    iEval (rewrite stack_own_slots; cbn [seq]) in "Hframe".
    iDestruct "Hframe" as "(Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & _)".
    iDestruct "Z1" as (u1) "Hf1". iDestruct "Z2" as (u2) "Hf2".
    iDestruct "Z3" as (u3) "Hf3".
    iAssert (ct_rest sp0) with "[Z4 Z5 Z6]" as "Hrest".
    { rewrite /ct_rest. iFrame "Z4 Z5 Z6". }
    (* ---- +0x002/+0x004/+0x006: save ra, s0, s1 ---- *)
    iPoseProof (cnti_002 with "Ht") as "Hi002".
    iApply (wp_csdsp_s_sconf (mword_of_int (CT + 0x2)) (mword_of_int 5 : mword 6) Rra
              P0 (K - 6)%nat u1 b with "Hcg Hpc Hi002 [Hf1]").
    { iEval (rewrite HP0sp Hb1). iExact "Hf1". }
    iIntros (CIDp2 Hsp2) "Hcg Hpc Hf1". rgall. iEval (rewrite HP0sp Hb1) in "Hf1".
    assert (HP0ra : P0 !!! Regidx Rra = m !!! Regidx Rra)
      by (rewrite /P0 upd_ne; [reflexivity | reg_neq]).
    iEval (rewrite HP0ra) in "Hf1".
    assert (Hp004 : add_vec_int (mword_of_int (CT + 0x2) : mword 64) 2
                    = mword_of_int (CT + 0x4)) by pcw.
    iEval (rewrite Hp004) in "Hpc".
    iPoseProof (cnti_004 with "Ht") as "Hi004".
    iApply (wp_csdsp_s_sconf (mword_of_int (CT + 0x4)) (mword_of_int 4 : mword 6) Rs0
              P0 (K - 6)%nat u2 b with "Hcg Hpc Hi004 [Hf2]").
    { iEval (rewrite HP0sp Hb2). iExact "Hf2". }
    iIntros (CIDp3 Hsp3) "Hcg Hpc Hf2". rgall. iEval (rewrite HP0sp Hb2) in "Hf2".
    assert (HP0s0 : P0 !!! Regidx Rs0 = m !!! Regidx Rs0)
      by (rewrite /P0 upd_ne; [reflexivity | reg_neq]).
    iEval (rewrite HP0s0) in "Hf2".
    assert (Hp006 : add_vec_int (mword_of_int (CT + 0x4) : mword 64) 2
                    = mword_of_int (CT + 0x6)) by pcw.
    iEval (rewrite Hp006) in "Hpc".
    iPoseProof (cnti_006 with "Ht") as "Hi006".
    iApply (wp_csdsp_s_sconf (mword_of_int (CT + 0x6)) (mword_of_int 3 : mword 6) Rs1
              P0 (K - 6)%nat u3 b with "Hcg Hpc Hi006 [Hf3]").
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
    { unfold pa_stk, add_vec_int. rewrite po_addv_assoc.
      rewrite (_ : add_vec (mword_of_int (- (8 * Z.of_nat 6%nat)) : mword 64)
                     (sign_extend' 64 (caddi4spn_imm (mword_of_int 12 : mword 8)))
                   = (mword_of_int 0 : mword 64)); [| pcw].
      apply bv_add_0_r. vm_compute. reflexivity. }
    iPoseProof (cnti_008 with "Ht") as "Hi008".
    iApply (wp_caddi4spn_s_sconf (mword_of_int (CT + 0x8)) (Cregidx (mword_of_int 0))
              (mword_of_int 12 : mword 8) Rs0 P0 (K - 6)%nat b
              ltac:(vm_compute; reflexivity) ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi008").
    iIntros (CIDp5 Hsp5) "Hcg Hpc". rgall.
    iEval (rewrite HP0sp Hs0v) in "Hcg".
    set (P1 := <[Regidx Rs0 := regval_into_reg sp0]> P0).
    assert (Hp00a : add_vec_int (mword_of_int (CT + 0x8) : mword 64) 2
                    = mword_of_int (CT + 0xa)) by pcw.
    iEval (rewrite Hp00a) in "Hpc".
    (* ---- +0x00a c.mv s1,a0 : s1 holds the character for the whole body ---- *)
    assert (HP1a0 : P1 !!! Regidx Ra0 = cv).
    { rewrite /P1 upd_ne; [| reg_neq]. rewrite /P0 upd_ne; [reflexivity | reg_neq]. }
    iPoseProof (cnti_00a with "Ht") as "Hi00a".
    iApply (wp_cmv_s_sconf (mword_of_int (CT + 0xa)) Rs1 Ra0 P1 (K - 6)%nat b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi00a").
    iIntros (CIDp6 Hsp6) "Hcg Hpc". rgall.
    iEval (rewrite HP1a0 w32_zero_add) in "Hcg".
    set (P2 := <[Regidx Rs1 := regval_into_reg cv]> P1).
    assert (Hp00c : add_vec_int (mword_of_int (CT + 0xa) : mword 64) 2
                    = mword_of_int (CT + 0xc)) by pcw.
    iEval (rewrite Hp00c) in "Hpc".
    (* ---- +0x00c/+0x010 : a0 := &cons ; +0x014 jal acquire ---- *)
    iPoseProof (cnti_00c with "Ht") as "Hi00c".
    iApply (wp_auipc_s_sconf (mword_of_int (CT + 0xc)) Ra0 (mword_of_int 18 : mword 20)
              P2 (K - 6)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi00c").
    iIntros (CIDp7 Hsp7) "Hcg Hpc". rgall.
    set (P3 := <[Regidx Ra0 := regval_into_reg
        (add_vec (mword_of_int (CT + 0xc) : mword 64)
           (auipc_off (mword_of_int 18 : mword 20)))]> P2).
    assert (Hp010 : add_vec_int (mword_of_int (CT + 0xc) : mword 64) 4
                    = mword_of_int (CT + 0x10)) by pcw.
    iEval (rewrite Hp010) in "Hpc".
    iPoseProof (cnti_010 with "Ht") as "Hi010".
    iApply (wp_addi4_s_sconf (mword_of_int (CT + 0x10)) Ra0 Ra0 (mword_of_int 4088 : mword 12)
              P3 (K - 6)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi010").
    iIntros (CIDp8 Hsp8) "Hcg Hpc". rgall.
    set (P4 := <[Regidx Ra0 := regval_into_reg
        (add_vec (P3 !!! Regidx Ra0) (sign_extend' 64 (mword_of_int 4088 : mword 12)))]> P3).
    assert (HP4a0 : P4 !!! Regidx Ra0 = a_cons).
    { rewrite /P4 upd_eq /P3 upd_eq /a_cons. apply bv_eq; vm_compute; reflexivity. }
    assert (Hp014 : add_vec_int (mword_of_int (CT + 0x10) : mword 64) 4
                    = mword_of_int (CT + 0x14)) by pcw.
    iEval (rewrite Hp014) in "Hpc".
    iPoseProof (cnti_014 with "Ht") as "Hi014".
    iApply (wp_jal_s_sconf (mword_of_int (CT + 0x14)) Rra (mword_of_int 2282 : mword 21)
              P4 (K - 6)%nat b ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi014").
    iIntros (CIDp9 Hsp9) "Hcg Hpc". rgall.
    set (P5 := <[Regidx Rra := regval_into_reg
        (add_vec_int (mword_of_int (CT + 0x14) : mword 64) 4)]> P4).
    assert (Hjaq : add_vec (mword_of_int (CT + 0x14) : mword 64)
                     (sign_extend' 64 (mword_of_int 2282 : mword 21))
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
    iAssert (ct_ret (CID0 := CID) pme m K lvl eb C b lks) with "[Hcont]" as "Hcont".
    { rewrite /ct_ret. iExact "Hcont". }
    iAssert (ct_exit_prop (CID0 := CID) γc pme m K lvl eb C b sp0 lks)
      with "[Hsaved Hcont]" as "EXIT".
    { iApply (ct_mk_exit γc pme m K lvl eb C b sp0 lks Hspm HK Hbm Hbelow with "Ht Hlk Hsaved Hcont"). }
    iAssert (ct_wake_prop (CID0 := CID) γc pme m K lvl eb C b sp0 lks) as "WAKE".
    { iApply (ct_mk_wake γc γs pme m K lvl eb C b sp0 lks HK Hlen Hlvl Hbm Hbelow
                with "Ht Hpanic Hpinv"). }
    iAssert (ct_kill_prop (CID0 := CID) γc pme m K lvl eb C b sp0 lks) as "KILL".
    { iApply (ct_mk_kill γtx γc γu γv pme m K lvl eb C b sp0 lks HK Hlvl Hbm Hbelow
                with "Ht Hpanic Hdev Htxl Hsub"). }
    (* ---- +0x014 acquire(&cons.lock) ---- *)
    iDestruct (cpu_own_transport CID CIDp9 lvl eb pme C b ltac:(wp_next_chain)
                 with "Hcnt") as "Hcnt".
    iApply (Acquire.wp_acquire_sconf γc "cons"%string cons_res P5 lvl eb pme C
              (K - 6)%nat b lks ltac:(lia) ltac:(unfold consoleintr_stack in HK; lia) Hbelow
              with "Hcg Hcnt Ht Hpc [] Hpanic").
    all: try lkbelow.
    { iEval (rewrite HP5a0). iExact "Hlk". }
    iIntros (CIDaq Hsaq ms0 maq) "%Hms0 Hcg Hpc %Hcsaq Hlocked Hres Hcnt Hpay". rgall.
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
    iPoseProof (cnti_018 with "Ht") as "Hi018".
    iPoseProof (cnti_01a with "Ht") as "Hi01a".
    iApply (wp_cli_s_sconf (mword_of_int (CT + 0x18)) Ra5 (mword_of_int 21 : mword 6)
              (mword_of_int 21 : mword 64) maq (trap_res b + (K - 6))%nat false
              ltac:(nz) ltac:(rdok) ltac:(pcw) with "Hcg Hpc Hi018").
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
                ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi01a").
      iApply bi.later_intro. iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
      assert (Hj092 : add_vec (mword_of_int (CT + 0x1a) : mword 64)
                        (sign_extend' 64 (mword_of_int 120 : mword 13))
                      = mword_of_int (CT + 0x92)) by pcw.
      iEval (rewrite Hj092) in "Hpc".
      iApply (ct_kill_pre (CIDq := CIDaq) γc pme m S1 K lvl eb C b sp0 lks
                HS1sp HS1cs Hchain Hbelow
                with "Ht Hcg Hpc Hcnt Hpay Hlocked Hres Hrest KILL EXIT"). }
    iPoseProof (cnti_01e with "Ht") as "Hi01e".
    iPoseProof (cnti_022 with "Ht") as "Hi022".
    iApply (wp_beq_fall_s_sconf (mword_of_int (CT + 0x1a)) (mword_of_int 120 : mword 13)
              Ra5 Rs1 S1 (trap_res b + (K - 6))%nat false ltac:(nz) ltac:(nz)
              ltac:(rgall; rewrite HS1s1 HS1a5; exact Hku) with "Hcg Hpc Hi01a").
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    assert (Hp01e : add_vec_int (mword_of_int (CT + 0x1a) : mword 64) 4
                    = mword_of_int (CT + 0x1e)) by pcw.
    iEval (rewrite Hp01e) in "Hpc".
    (* ---- +0x01e li a5,127 ; +0x022 beq s1,a5 : case '\x7f' ---- *)
    iApply (wp_li4_s_sconf (mword_of_int (CT + 0x1e)) Ra5 (mword_of_int 127 : mword 12)
              (mword_of_int 127 : mword 64) S1 (trap_res b + (K - 6))%nat false
              ltac:(nz) ltac:(rdok) ltac:(pcw) with "Hcg Hpc Hi01e").
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
                ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi022").
      iApply bi.later_intro. iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
      assert (Hj0f0 : add_vec (mword_of_int (CT + 0x22) : mword 64)
                        (sign_extend' 64 (mword_of_int 206 : mword 13))
                      = mword_of_int (CT + 0xf0)) by pcw.
      iEval (rewrite Hj0f0) in "Hpc".
      iApply (ct_bs (CIDq := CIDaq) γtx γc γu γv pme m S2 K lvl eb C b sp0 lks
                HS2sp HS2cs HK Hlvl Hchain Hbelow
                with "Ht Hpanic Hdev Htxl Hsub Hcg Hpc Hcnt Hpay Hlocked Hres Hrest EXIT"). }
    iApply (wp_beq_fall_s_sconf (mword_of_int (CT + 0x22)) (mword_of_int 206 : mword 13)
              Ra5 Rs1 S2 (trap_res b + (K - 6))%nat false ltac:(nz) ltac:(nz)
              ltac:(rgall; rewrite HS2s1 HS2a5; exact Hdel) with "Hcg Hpc Hi022").
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    assert (Hp026 : add_vec_int (mword_of_int (CT + 0x22) : mword 64) 4
                    = mword_of_int (CT + 0x26)) by pcw.
    iEval (rewrite Hp026) in "Hpc".
    (* ---- +0x026 c.li a5,8 ; +0x028 beq s1,a5 : case C('H') ---- *)
    iPoseProof (cnti_026 with "Ht") as "Hi026".
    iPoseProof (cnti_028 with "Ht") as "Hi028".
    iApply (wp_cli_s_sconf (mword_of_int (CT + 0x26)) Ra5 (mword_of_int 8 : mword 6)
              (mword_of_int 8 : mword 64) S2 (trap_res b + (K - 6))%nat false
              ltac:(nz) ltac:(rdok) ltac:(pcw) with "Hcg Hpc Hi026").
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
                ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi028").
      iApply bi.later_intro. iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
      assert (Hj0f0 : add_vec (mword_of_int (CT + 0x28) : mword 64)
                        (sign_extend' 64 (mword_of_int 200 : mword 13))
                      = mword_of_int (CT + 0xf0)) by pcw.
      iEval (rewrite Hj0f0) in "Hpc".
      iApply (ct_bs (CIDq := CIDaq) γtx γc γu γv pme m S3 K lvl eb C b sp0 lks
                HS3sp HS3cs HK Hlvl Hchain Hbelow
                with "Ht Hpanic Hdev Htxl Hsub Hcg Hpc Hcnt Hpay Hlocked Hres Hrest EXIT"). }
    (* ---- the default arm ---- *)
    iApply (wp_beq_fall_s_sconf (mword_of_int (CT + 0x28)) (mword_of_int 200 : mword 13)
              Ra5 Rs1 S3 (trap_res b + (K - 6))%nat false ltac:(nz) ltac:(nz)
              ltac:(rgall; rewrite HS3s1 HS3a5; exact Hbs) with "Hcg Hpc Hi028").
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    assert (Hp02c : add_vec_int (mword_of_int (CT + 0x28) : mword 64) 4
                    = mword_of_int (CT + 0x2c)) by pcw.
    iEval (rewrite Hp02c) in "Hpc".
    iApply (ct_dflt (CIDq := CIDaq) γtx γc γu γv pme m S3 K lvl eb C b sp0 cv lks
              HS3sp HS3s1 HS3cs HK Hlvl Hchain Hbelow
              with "Ht Hpanic Hdev Htxl Hsub Hcg Hpc Hcnt Hpay Hlocked Hres Hrest
                    WAKE EXIT").
  Qed.

End ProofConsoleintr.

End ConsoleintrProof.
