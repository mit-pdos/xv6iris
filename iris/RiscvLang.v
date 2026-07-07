(* ============================================================== *)
(* RiscvAddTryStep.v -- consolidated Iris-over-Sail development.   *)
(* An Iris weakest-precondition for `add a2,a0,a1` executed by the *)
(* real Sail RISC-V `try_step`.  Self-contained except for:        *)
(*   - the generated model    : Riscv.rv64d / rv64d_types          *)
(*   - a small iris-FREE bv-arithmetic prelude : RiscvModelBytes    *)
(*     (kept separate ONLY because it uses vanilla `rewrite .. by`, *)
(*      which ssreflect -- pulled in by iris -- forbids).           *)
(* ============================================================== *)

From stdpp Require Import gmap bitvector.definitions.
From iris.program_logic Require Import language.
(* NOTE: SailStdpp.Base/Values/TypeCasts are imported LATER (before the         *)
(* ExecClose section), NOT here: they make the model's [mword] Countable        *)
(* (Countable_mword) canonical, but the Lang/Iris/Exec sections + the iris-free  *)
(* RiscvModelBytes must agree on stdpp's bv_countable for [gmap Arch.pa (bv 8)]  *)
(* (= the [mstate.mem] type).  Importing them here would retype mstate.mem and   *)
(* clash with read_bytes.  See the import line just above RiscvModelExecClose.    *)
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
(* 3b. Multi-hart global state.                                             *)
(*                                                                          *)
(*   [CPU] is the FINITE type of valid HART ids -- every element is a real   *)
(*   hart that is always present.  [gstate] stores one [regstate] per hart   *)
(*   as a TOTAL function [CPU -> regstate] (no partiality, so no membership  *)
(*   side conditions ever arise) together with the single shared byte        *)
(*   memory.  An [mstate] is one hart's view: its own registers paired with  *)
(*   the shared memory.                                                       *)
(* ---------------------------------------------------------------------- *)

Definition NCPU : nat := 8.
Definition CPU : Type := fin NCPU.

Record gstate := GState {
  gregs : CPU -> regstate;
  gmem  : gmap Arch.pa (bv 8);
}.

(* pointwise update of a single hart's register file *)
Global Instance greg_insert : Insert CPU regstate (CPU -> regstate) :=
  fun cpu rs gr c => if decide (c = cpu) then rs else gr c.

(* ---------------------------------------------------------------------- *)
(* 4. The language.  The program [Loop] steps ONE hart forever; which hart   *)
(*    is selected AMBIENTLY: the constructor [LoopE] carries the hart id and  *)
(*    the [Loop] notation fills it in from the surrounding [CpuId] instance.  *)
(*    Every WP therefore keeps the argument-free spelling [WP Loop {{...}}],  *)
(*    while [prim_step] over [gstate] reads the selected hart's registers,    *)
(*    pairs them with [gmem] to reconstruct that hart's [mstate], runs one    *)
(*    [riscv_step], and writes the resulting registers and memory back.       *)
(* ---------------------------------------------------------------------- *)

Class CpuId := cpu_id : CPU.

Inductive mexpr := LoopE (cpu : CPU).
Definition mval := Empty_set.
Definition mobs := Empty_set.
Definition of_val (v : mval) : mexpr := match v with end.
Definition to_val (_ : mexpr) : option mval := None.

Notation Loop := (LoopE cpu_id).

Definition prim_step
    (e : mexpr) (g : gstate) (κ : list mobs)
    (e' : mexpr) (g' : gstate) (efs : list mexpr) : Prop :=
  exists cpu, e = LoopE cpu /\ e' = LoopE cpu /\ κ = [] /\ efs = [] /\
    exists (u : unit) (s' : mstate),
      run riscv_step (MState (g.(gregs) cpu) g.(gmem)) u s' /\
      g' = GState (<[cpu := s'.(sregs)]> g.(gregs)) s'.(mem).

Lemma riscv_lang_mixin : LanguageMixin of_val to_val prim_step.
Proof.
  split.
  - intros [].
  - intros e v Hv. discriminate Hv.
  - intros e s κ e' s' efs (cpu & -> & _). reflexivity.
Qed.

Definition riscv_lang : language := Language riscv_lang_mixin.

