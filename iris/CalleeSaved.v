(* CalleeSaved.v -- a predicate for callee-saved register preservation across a
   function call, for use in whole-function WP postconditions.

   A well-behaved RISC-V function preserves the callee-saved registers: it may
   clobber the caller-saved ones (ra, t0-t6, a0-a7) freely, but every
   callee-saved register holds, on return, exactly the value it held on entry.
   [callee_saved m m'] captures precisely that relationship between the entry
   register map [m] and the return register map [m']: it says nothing about the
   caller-saved registers (their values are arbitrary and irrelevant), and
   asserts that each preserved register agrees in [m] and [m'].

   The preserved set is: sp (x2), s0 (x8), s1 (x9), s2..s11 (x18..x27) -- the
   classic RISC-V callee-saved registers -- plus tp (x4), which this kernel pins
   to the cpuid and every function preserves.  Function-call WPs put
   [∃ m', gpr_file m' ∗ ⌜callee_saved m m'⌝] in their postcondition in place of
   an ad-hoc, per-function list of individual register-preservation facts. *)
From Stdlib Require Import ZArith.
From stdpp Require Import gmap bitvector.definitions.
Require Import SailStdpp.Operators_mwords.
Require Import SailStdpp.Values.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import WpGprRvc.

Definition callee_saved (m m' : gmap regidx (mword 64)) : Prop :=
  m' !!! Regidx csp_rs1 = m !!! Regidx csp_rs1 /\                            (* x2  sp  *)
  m' !!! Regidx (mword_of_int 4 : mword 5)  = m !!! Regidx (mword_of_int 4 : mword 5)  /\  (* x4  tp *)
  m' !!! Regidx (mword_of_int 8 : mword 5)  = m !!! Regidx (mword_of_int 8 : mword 5)  /\  (* x8  s0 *)
  m' !!! Regidx (mword_of_int 9 : mword 5)  = m !!! Regidx (mword_of_int 9 : mword 5)  /\  (* x9  s1 *)
  m' !!! Regidx (mword_of_int 18 : mword 5) = m !!! Regidx (mword_of_int 18 : mword 5) /\  (* x18 s2 *)
  m' !!! Regidx (mword_of_int 19 : mword 5) = m !!! Regidx (mword_of_int 19 : mword 5) /\  (* x19 s3 *)
  m' !!! Regidx (mword_of_int 20 : mword 5) = m !!! Regidx (mword_of_int 20 : mword 5) /\  (* x20 s4 *)
  m' !!! Regidx (mword_of_int 21 : mword 5) = m !!! Regidx (mword_of_int 21 : mword 5) /\  (* x21 s5 *)
  m' !!! Regidx (mword_of_int 22 : mword 5) = m !!! Regidx (mword_of_int 22 : mword 5) /\  (* x22 s6 *)
  m' !!! Regidx (mword_of_int 23 : mword 5) = m !!! Regidx (mword_of_int 23 : mword 5) /\  (* x23 s7 *)
  m' !!! Regidx (mword_of_int 24 : mword 5) = m !!! Regidx (mword_of_int 24 : mword 5) /\  (* x24 s8 *)
  m' !!! Regidx (mword_of_int 25 : mword 5) = m !!! Regidx (mword_of_int 25 : mword 5) /\  (* x25 s9 *)
  m' !!! Regidx (mword_of_int 26 : mword 5) = m !!! Regidx (mword_of_int 26 : mword 5) /\  (* x26 s10 *)
  m' !!! Regidx (mword_of_int 27 : mword 5) = m !!! Regidx (mword_of_int 27 : mword 5).     (* x27 s11 *)

Lemma callee_saved_refl (m : gmap regidx (mword 64)) : callee_saved m m.
Proof. unfold callee_saved. repeat split; reflexivity. Qed.

Lemma callee_saved_trans (m1 m2 m3 : gmap regidx (mword 64)) :
  callee_saved m1 m2 -> callee_saved m2 m3 -> callee_saved m1 m3.
Proof.
  unfold callee_saved.
  intros (?&?&?&?&?&?&?&?&?&?&?&?&?&?) (?&?&?&?&?&?&?&?&?&?&?&?&?&?).
  repeat split; etransitivity; eassumption.
Qed.
