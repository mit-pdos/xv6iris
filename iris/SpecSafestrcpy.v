(* SpecSafestrcpy.v -- the public interface of safestrcpy() (kernel/string.c),
   stated independently of its proof.  Requires only the definitional layer --
   never a whole-function proof file -- so every function proof can be
   checked in parallel.

     char *safestrcpy(char *s, const char *t, int n) {
       char *os = s;
       if (n <= 0) return os;
       while (--n > 0 && ( *s++ = *t++) != 0) ;
       *s = 0;
       return os;
     }

   @ KernelSyms.safestrcpy = 0x80000e1c, 52 bytes: a 2-slot ra/s0 frame, a
   [blez] fast-return, and one byte-at-a-time copy loop with no callees.

   UNLIKE copyinstr's, THE SOURCE HERE IS A KNOWN, OWNED KERNEL BUFFER --
   [p->name], never user memory -- so the postcondition can and does name the
   exact stop index and the exact bytes copied, rather than copyinstr's
   existential-k, contents-blind [bb_cstr] arm.  [ssc_stop] is that pure
   characterization, worked out by hand-tracing the two ways the loop can
   exit (see below); [ssc_post] is what it implies about the destination.

   THE TWO WAYS THE LOOP STOPS, both already visible in the C:

   - t HOLDS A NUL WITHIN THE FIRST [n-1] BYTES ([k < n-1], [f k = 0], every
     earlier byte nonzero).  The loop's OWN check ([( *s++ = *t++) != 0])
     copies that NUL into [s] at index [k] and then breaks -- but [s]/[t]
     were already incremented as part of the assignment, so the pointer is
     now at [k+1] when the loop exits.  The unconditional [*s = 0] after the
     loop therefore writes a SECOND NUL at index [k+1] (distinct from the
     first, and always in-bounds since [k <= n-2]).  Bytes past [k+1] are
     untouched.
   - t HAS NO NUL IN THE FIRST [n-1] BYTES.  The loop runs its full budget
     ([n-1] iterations, copying indices [0..n-2]) and exits because the
     counter -- not a NUL -- ran out, leaving the pointer at [n-1].  The
     trailing [*s = 0] then writes the ONE terminator at [n-1], truncating
     whatever [t] held there (which the loop never even read).

   Both cases are subsumed by ONE stop index [k] (the first case's own [k],
   or [n-1] as the sentinel for the second) and ONE shape for the result:
   bytes strictly below [k] are copied verbatim, [s]'s byte AT [k] is always
   the NUL terminator (copied-and-zero in the first case, forced in the
   second), [k+1] gets a SECOND explicit NUL when it is still in bounds
   (exactly the first case), and everything past that is untouched.

   HOW MUCH OF THE SOURCE THE CALLER MUST OWN: [ssc_src_ok], and it is a
   DISJUNCTION rather than the [ns = n] this contract used to demand.  The
   loop reads [t[0 .. n-2]] at most and stops early at the first NUL, so
   there are two ways to be safe:

   - [n - 1 <= ns] -- you own everything the loop's BUDGET can reach.  Every
     caller holding a fixed-size buffer at least as long as the field is
     here, kfork's [safestrcpy(np->name, p->name, 16)] included, at
     [ns = n = 16].
   - THERE IS A NUL STRICTLY INSIDE WHAT YOU OWN -- the loop stops at or
     before it and never reads past.

   This header used to record the [ns = n] form as an over-ask that was
   "harmless and simpler, since every caller already owns that much".  It
   stopped being harmless when exec became a caller: kexec's source is
   [last], a pointer INTO the path string, and sixteen bytes past [last] run
   off the end of the caller's [char path[MAXPATH]].  What exec owns is the
   rest of the string, and the string's own terminator is exactly what makes
   that enough -- the second disjunct.

   Note what does NOT need saying alongside it: the postcondition still
   speaks of [f j] only for [j < k], and [k < ns] holds under either
   disjunct (under the second, a NUL inside the owned range refutes
   [bb_nonul f (n-1)] and forces the [k < n-1] arm of [ssc_stop]).  So no
   conjunct of the result reaches a byte the caller does not own, and the
   result shape is unchanged.

   [n <= 0] IS ITS OWN ARM: the destination is untouched and the return
   value is the unmodified [s] pointer -- [os = s], read straight off the
   argument register, since nothing between entry and the early [ret]
   touches [a0]. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre lifting.
From iris.base_logic.lib Require Import gen_heap invariants ghost_var.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import RiscvModelBytes RiscvPtsto RiscvLang.
Require Import InstrBytes KernelText.
Require Import RegFile.
Require Import RiscvExtras.
Require Import CalleeSaved.
Require Import IntrDefs WpNext.
Require Import ByteBuf.
From Kernel Require KernelSyms.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Import Defs.
Local Open Scope Z_scope.


(* THE STOP INDEX, for [n > 0]: either t's own NUL, strictly inside the
   copyable range, or the truncation sentinel [n - 1].  [bb_cstr]/[bb_nonul]
   are exactly the two pure facts each disjunct needs. *)
Definition ssc_stop (f : nat -> bv 8) (n k : nat) : Prop :=
  ((k < n - 1)%nat /\ bb_cstr f k) \/ (k = (n - 1)%nat /\ bb_nonul f (n - 1)).

(* HOW MUCH OF [t] THE CALLER OWNS -- see the header.  [ns] is the length of
   the source big-op; [n] is still the DESTINATION's size, i.e. the loop's
   budget, and the two are independent. *)
Definition ssc_src_ok (f : nat -> bv 8) (n ns : nat) : Prop :=
  (n - 1 <= ns)%nat
  \/ (exists k, (k < ns)%nat /\ f k = (mword_of_int 0 : mword 8)).

(* The old precondition is the first disjunct, so no existing caller moves. *)
Lemma ssc_src_ok_full (f : nat -> bv 8) (n : nat) : ssc_src_ok f n n.
Proof. left. lia. Qed.

(* ...and under the second disjunct the stop index really is inside the owned
   range, which is what makes [ssc_post]'s [forall j, j < k -> s j = f j]
   speak only about bytes the caller has.  (Under the first it is inside by
   [k <= n - 1 <= ns].) *)
Lemma ssc_stop_src (f : nat -> bv 8) (n ns k : nat) :
  ssc_src_ok f n ns -> ssc_stop f n k -> (k <= ns)%nat.
Proof.
  intros [Hbud | (k0 & Hk0 & Hf0)] Hstop.
  - destruct Hstop as [[Hlt _] | [Heq _]]; lia.
  - (* a NUL inside the owned range: either it is inside the loop's budget,
       in which case it forces the [bb_cstr] arm and [k] is at or before it,
       or it is not, in which case [n - 1 <= k0 < ns] anyway. *)
    destruct (Nat.lt_ge_cases k0 (n - 1)) as [Hk0lt | Hk0ge].
    + destruct Hstop as [[_ [Hnn _]] | [_ Hnn]].
      * (* [bb_cstr f k]: no NUL strictly below [k], so [k <= k0 < ns]. *)
        destruct (Nat.lt_ge_cases k0 k) as [Hlt | Hge].
        { exfalso. exact (Hnn k0 Hlt Hf0). }
        lia.
      * exfalso. exact (Hnn k0 Hk0lt Hf0).
    + destruct Hstop as [[Hlt _] | [Heq _]]; lia.
Qed.

(* WHAT [s] LOOKS LIKE AFTERWARDS, given the stop index [k] and the buffer's
   OLD naming function [g] (only the untouched tail reads from it). *)
Definition ssc_post (f g s : nat -> bv 8) (n k : nat) : Prop :=
  (forall j, (j < k)%nat -> s j = f j) /\
  s k = (mword_of_int 0 : mword 8) /\
  ((k + 1 < n)%nat -> s (k + 1)%nat = (mword_of_int 0 : mword 8)) /\
  (forall j, (k + 1 < j)%nat -> (j < n)%nat -> s j = g j).

Definition wp_safestrcpy_sconf_body `{!riscvGS Σ, !xv6G Σ} `{GEN : GenId} `{CID : CpuId} (kts ktt : ktier) (mm : regfile)
    (n ns : nat) (f g : nat -> bv 8) (K : nat) (dq : dfrac) (b : bool) (p : mword 64) :=
  let pcE : mword 64 := mword_of_int KernelSyms.safestrcpy in
  let s := mm !!! Regidx (mword_of_int 10 : mword 5) in
  let t := mm !!! Regidx (mword_of_int 11 : mword 5) in
  let ret_tgt := ret_pc (mm !!! Regidx (mword_of_int 1 : mword 5)) in
  (* the 2-slot frame; safestrcpy calls nothing *)
  (2 <= K)%nat ->
  mm !!! Regidx (mword_of_int 12 : mword 5) = (mword_of_int (Z.of_nat n) : mword 64) ->
  (Z.of_nat n < 2 ^ 31)%Z ->
  (* how much of [t] is owned below -- see the header *)
  ssc_src_ok f n ns ->
  sie_cap_gpr KT1 mm K b p -∗
  kernel_text -∗
  pc_is pcE -∗
  ([∗ list] j ∈ seq 0 ns, (pa_add t j) ↦ₘ[ktt]{dq} f j) -∗
  ([∗ list] j ∈ seq 0 n, (pa_add s j) ↦ₘ[kts] g j) -∗
  wp_next b p (fun (CID : CpuId) =>
    ∀ (mr : regfile) (h : nat -> bv 8),
    sie_cap_gpr KT1 mr K b p -∗
    pc_is ret_tgt -∗
    ([∗ list] j ∈ seq 0 ns, (pa_add t j) ↦ₘ[ktt]{dq} f j) -∗
    ([∗ list] j ∈ seq 0 n, (pa_add s j) ↦ₘ[kts] h j) -∗
    ⌜callee_saved mm mr⌝ -∗
    ⌜mr !!! Regidx (mword_of_int 10 : mword 5) = s⌝ -∗
    ⌜(n = 0%nat /\ h = g) \/
     (0 < n)%nat /\ exists k, ssc_stop f n k /\ ssc_post f g h n k⌝ -∗
    WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type SAFESTRCPY.
  Parameter wp_safestrcpy_sconf :
    forall `{!riscvGS Σ, !xv6G Σ} `{GEN : GenId} `{CID : CpuId} (kts ktt : ktier) (mm : regfile)
      (n ns : nat) (f g : nat -> bv 8) (K : nat) (dq : dfrac) (b : bool) (p : mword 64),
      wp_safestrcpy_sconf_body kts ktt mm n ns f g K dq b p.
End SAFESTRCPY.
