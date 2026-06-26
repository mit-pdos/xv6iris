(* ============================================================== *)
(* RiscvAddTryStep.v -- consolidated Iris-over-Sail development.   *)
(* An Iris weakest-precondition for `add a2,a0,a1` executed by the *)
(* real Sail RISC-V `try_step`.  Self-contained except for:        *)
(*   - the generated model    : Riscv.rv64d / rv64d_types          *)
(*   - a small iris-FREE bv-arithmetic prelude : RiscvModelBytes    *)
(*     (kept separate ONLY because it uses vanilla `rewrite .. by`, *)
(*      which ssreflect -- pulled in by iris -- forbids).           *)
(* ============================================================== *)

From Stdlib Require Import Eqdep_dec ZArith Lia.
From stdpp Require Import gmap list list_monad bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre lifting.
(* NOTE: SailStdpp.Base/Values/TypeCasts are imported LATER (before the         *)
(* ExecClose section), NOT here: they make the model's [mword] Countable        *)
(* (Countable_mword) canonical, but the Lang/Iris/Exec sections + the iris-free  *)
(* RiscvModelBytes must agree on stdpp's bv_countable for [gmap Arch.pa (bv 8)]  *)
(* (= the [mstate.mem] type).  Importing them here would retype mstate.mem and   *)
(* clash with read_bytes.  See the import line just above RiscvModelExecClose.    *)
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
(* NB: deliberately NO `Set Default Proof Using "Type"` — some merged sections   *)
(* use bare `Proof.` and rely on Coq's default (generalize over the section      *)
(* Hypotheses actually used), as in their original (Set-free) files.             *)
Local Open Scope Z_scope.


(* ===== RiscvModelLang ===== *)
(* ====================================================================== *)
(* RiscvModelLang.v                                                        *)
(*                                                                         *)
(* Re-architecture of RiscvIrisFetch.v to run the *real* Sail model's      *)
(* [try_step] as the loop body, instead of the hand-written                *)
(* fetch-decode-execute [riscv_step].                                      *)
(*                                                                         *)
(* LAYER 1 (this file): the operational semantics.                         *)
(*   - state  = the model's own [regstate] + a byte memory                 *)
(*   - run    = interpreter over the real monad [M] / [Interface.outcome]  *)
(*   - step   = [try_step 0 false] (one fetch-decode-execute cycle)        *)
(*   - language instance (argument-free, like RiscvIrisFetch).             *)
(* The Iris program-logic layer (gen_heap points-to over registers,        *)
(* state_interp, WP) is deliberately deferred to a follow-up file.         *)
(* ====================================================================== *)




(* ---------------------------------------------------------------------- *)
(* 1. Operational state: the model's register record + byte memory.        *)
(*    Memory is keyed by the model's physical-address type [Arch.pa]       *)
(*    (= mword 64), values are individual bytes.                           *)
(* ---------------------------------------------------------------------- *)

Record mstate := MState {
  sregs : regstate;
  mem   : gmap Arch.pa (bv 8);
}.

Definition set_reg (s : mstate) (r : register) (v : type_of_register r) : mstate :=
  MState (register_set r v s.(sregs)) s.(mem).

Definition set_mem (s : mstate) (a : Arch.pa) (b : bv 8) : mstate :=
  MState s.(sregs) (<[a := b]> s.(mem)).

(* Byte address [a + j] (model's own mword arithmetic) and byte [j] of a value. *)

(* ---------------------------------------------------------------------- *)
(* 2. Interpreter over the real monad [M X = Interface.iMon (const exc) X].*)
(*    A relation (big-step), defined as a dependent Fixpoint to avoid the  *)
(*    UIP axiom that GADT inversion of [Next] would otherwise require.     *)
(*                                                                         *)
(*    Register effects use the model's own [register_lookup]/[register_set]*)
(*    (total, no dependent gmap needed at the operational level).          *)
(*    Memory reads/writes are byte-addressed.  Pure "announce"/trace       *)
(*    outcomes are state no-ops; failure/discard outcomes are stuck.       *)
(* ---------------------------------------------------------------------- *)

Fixpoint run {X} (m : M X) (s : mstate) (x : X) (s' : mstate) {struct m} : Prop :=
  match m with
  | Interface.Ret y => x = y /\ s' = s
  | Interface.Next oc k =>
      (match oc in Interface.outcome _ T return (T -> M X) -> Prop with
       (* registers *)
       | Interface.RegRead r _ =>
           fun k => run (k (register_lookup r s.(sregs))) s x s'
       | Interface.RegWrite r _ v =>
           fun k => run (k tt) (set_reg s r v) x s'
       (* memory: an n-byte read returns the value [w] whose every byte [j] is
          the memory byte at [pa + j] (little-endian, faithful), so the full
          word is pinned by [(mem, pa, n)] -- not just the low byte. *)
       | Interface.MemRead n req =>
           fun k => exists w : bv (8 * n),
             (forall j : nat, (N.of_nat j < n)%N ->
                s.(mem) !! (pa_add (Interface.ReadReq.pa req) j) = Some (nth_byte w j))
             /\ run (k (inl (w, None))) s x s'
       | Interface.MemWrite n req =>
           fun k =>
             run (k (inl None))
                 (MState s.(sregs)
                    (write_bytes s.(mem) (Interface.WriteReq.pa req) n
                                 (Interface.WriteReq.value req))) x s'
       (* trace / announce outcomes: state no-ops *)
       | Interface.InstrAnnounce _   => fun k => run (k tt) s x s'
       | Interface.BranchAnnounce _ _=> fun k => run (k tt) s x s'
       | Interface.Barrier _         => fun k => run (k tt) s x s'
       | Interface.CacheOp _         => fun k => run (k tt) s x s'
       | Interface.TlbOp _           => fun k => run (k tt) s x s'
       | Interface.TakeException _   => fun k => run (k tt) s x s'
       | Interface.ReturnException _ => fun k => run (k tt) s x s'
       | Interface.TranslationStart _=> fun k => run (k tt) s x s'
       | Interface.TranslationEnd _  => fun k => run (k tt) s x s'
       | Interface.CycleCount        => fun k => run (k tt) s x s'
       | Interface.Message _         => fun k => run (k tt) s x s'
       | Interface.GetCycleCount     => fun k => run (k 0%Z) s x s'
       (* nondeterminism: branch over every choice *)
       | Interface.Choose _          => fun k => exists c, run (k c) s x s'
       (* failure / discard / injected exception: stuck *)
       | _ => fun _ => False
       end) k
  end.

(* ---------------------------------------------------------------------- *)
(* 3. The fixed loop body: ONE real fetch-decode-execute cycle.            *)
(* ---------------------------------------------------------------------- *)

Definition riscv_step : M unit :=
  Defs.bind (try_step 0%Z false) (fun _ : bool => Defs.returnm tt).

(* ---------------------------------------------------------------------- *)
(* 4. The argument-free language (same trivial Loop shape as before).      *)
(* ---------------------------------------------------------------------- *)

Inductive mexpr := Loop.
Definition mval := Empty_set.
Definition mobs := Empty_set.
Definition of_val (v : mval) : mexpr := match v with end.
Definition to_val (_ : mexpr) : option mval := None.

Definition prim_step
    (e : mexpr) (s : mstate) (κ : list mobs)
    (e' : mexpr) (s' : mstate) (efs : list mexpr) : Prop :=
  e = Loop /\ e' = Loop /\ κ = [] /\ efs = [] /\ exists u, run riscv_step s u s'.

Lemma riscv_lang_mixin : LanguageMixin of_val to_val prim_step.
Proof.
  split.
  - intros [].
  - intros e v Hv. discriminate Hv.
  - intros e s κ e' s' efs _. reflexivity.
Qed.

Definition riscv_lang : language := Language riscv_lang_mixin.

