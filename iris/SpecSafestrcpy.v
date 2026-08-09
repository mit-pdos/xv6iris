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
   (exactly the first case), and everything past that is untouched.  Nothing
   about [t] beyond index [n-2] is ever read, so the precondition need not
   own it -- but it is harmless and simpler to ask for the full [n], since
   every caller (this one included) already owns that much.

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
Require Import RiscvModelBytes RiscvPtsto RiscvLang RiscvExtras.
Require Import InstrBytes KernelText.
Require Import RegFile.
Require Import SmodeCore.
Require Import CalleeSaved.
Require Import IntrDefs WpNext.
Require Import ByteBuf.
From Kernel Require KernelSyms.
Import Defs.
Local Open Scope Z_scope.


(* THE STOP INDEX, for [n > 0]: either t's own NUL, strictly inside the
   copyable range, or the truncation sentinel [n - 1].  [bb_cstr]/[bb_nonul]
   are exactly the two pure facts each disjunct needs. *)
Definition ssc_stop (f : nat -> bv 8) (n k : nat) : Prop :=
  ((k < n - 1)%nat /\ bb_cstr f k) \/ (k = (n - 1)%nat /\ bb_nonul f (n - 1)).

(* WHAT [s] LOOKS LIKE AFTERWARDS, given the stop index [k] and the buffer's
   OLD naming function [g] (only the untouched tail reads from it). *)
Definition ssc_post (f g s : nat -> bv 8) (n k : nat) : Prop :=
  (forall j, (j < k)%nat -> s j = f j) /\
  s k = (mword_of_int 0 : mword 8) /\
  ((k + 1 < n)%nat -> s (k + 1)%nat = (mword_of_int 0 : mword 8)) /\
  (forall j, (k + 1 < j)%nat -> (j < n)%nat -> s j = g j).

Definition wp_safestrcpy_sconf_body `{!riscvGS Σ, !sieG Σ} `{GEN : GenId} `{CID : CpuId}
    (Φ : mval -> iProp Σ) (mm : regfile)
    (n : nat) (f g : nat -> bv 8) (K : nat) (dq : dfrac) (b : bool) (p : mword 64) :=
  let pcE : mword 64 := mword_of_int KernelSyms.safestrcpy in
  let s := mm !!! Regidx (mword_of_int 10 : mword 5) in
  let t := mm !!! Regidx (mword_of_int 11 : mword 5) in
  let ret_tgt := ret_pc (mm !!! Regidx (mword_of_int 1 : mword 5)) in
  (* the 2-slot frame; safestrcpy calls nothing *)
  (2 <= K)%nat ->
  mm !!! Regidx (mword_of_int 12 : mword 5) = (mword_of_int (Z.of_nat n) : mword 64) ->
  (Z.of_nat n < 2 ^ 31)%Z ->
  sie_cap_gpr mm K b p -∗
  kernel_text -∗
  pc_is pcE -∗
  ([∗ list] j ∈ seq 0 n, (pa_add t j) ↦ₘ{dq} f j) -∗
  ([∗ list] j ∈ seq 0 n, (pa_add s j) ↦ₘ g j) -∗
  wp_next b p (fun (CID : CpuId) =>
    ∀ (mr : regfile) (h : nat -> bv 8),
    sie_cap_gpr mr K b p -∗
    pc_is ret_tgt -∗
    ([∗ list] j ∈ seq 0 n, (pa_add t j) ↦ₘ{dq} f j) -∗
    ([∗ list] j ∈ seq 0 n, (pa_add s j) ↦ₘ h j) -∗
    ⌜callee_saved mm mr⌝ -∗
    ⌜mr !!! Regidx (mword_of_int 10 : mword 5) = s⌝ -∗
    ⌜(n = 0%nat /\ h = g) \/
     (0 < n)%nat /\ exists k, ssc_stop f n k /\ ssc_post f g h n k⌝ -∗
    WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type SAFESTRCPY.
  Parameter wp_safestrcpy_sconf :
    forall `{!riscvGS Σ, !sieG Σ} `{GEN : GenId} `{CID : CpuId}
      (Φ : mval -> iProp Σ) (mm : regfile)
      (n : nat) (f g : nat -> bv 8) (K : nat) (dq : dfrac) (b : bool) (p : mword 64),
      wp_safestrcpy_sconf_body Φ mm n f g K dq b p.
End SAFESTRCPY.
