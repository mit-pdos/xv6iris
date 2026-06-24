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
                 (set_mem s (Interface.WriteReq.pa req)
                            (bv_extract 0 8 (Interface.WriteReq.value req))) x s'
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

(* ===== RiscvModelIris ===== *)
(* ====================================================================== *)
(* RiscvModelIris.v                                                        *)
(*                                                                         *)
(* LAYER 2: the Iris program-logic layer over RiscvModelLang.v.            *)
(*                                                                         *)
(*   - register & memory [gen_heap]s, with points-to [r |->r v] / [a|->m b]*)
(*   - state_interp that BRIDGES the model's [regstate] to per-register    *)
(*     points-to via an existential register map + an agreement invariant  *)
(*     (axiom-free: existT injectivity goes through Eqdep_dec, register     *)
(*      has decidable equality; no Finite/UIP needed).                     *)
(*   - the two bridge lemmas [reg_valid] / [reg_update] and a memory read  *)
(*     lemma [mem_valid].                                                   *)
(*                                                                         *)
(* The WP for ADD *through* [try_step] (symbolic unfolding of fetch/decode/*)
(* execute/currentlyEnabled) is the next milestone; this file provides the *)
(* ghost-state foundation it will rest on.                                 *)
(* ====================================================================== *)




(* ---------------------------------------------------------------------- *)
(* 0. Two small facts about the model's [register_beq] and [existT].       *)
(* ---------------------------------------------------------------------- *)

Lemma register_beq_true (k r : register) : register_beq k r = true -> k = r.
Proof.
  destruct k, r; simpl; intro E; try discriminate;
    f_equal; autorewrite with register_beq_iffs in E; exact E.
Qed.

Lemma register_beq_false (k r : register) : k <> r -> register_beq k r = false.
Proof.
  intros Hne. destruct (register_beq k r) eqn:E; [|reflexivity].
  exfalso. apply Hne. by apply register_beq_true.
Qed.

(* existT injectivity on the (decidable) index type [register]: axiom-free. *)
Lemma reg_existT_inj (r : register) (v v' : type_of_register r) :
  existT r v = existT r v' -> v = v'.
Proof.
  apply (inj_pair2_eq_dec register (fun x y => decide (x = y))).
Qed.

(* ---------------------------------------------------------------------- *)
(* 1. Ghost state: a register heap (dependent values) and a memory heap.   *)
(* ---------------------------------------------------------------------- *)

Class riscvGS (Σ : gFunctors) := RiscvGS {
  riscv_invGS :: invGS Σ;
  riscv_regGS :: gen_heapGS register (sigT type_of_register) Σ;
  riscv_memGS :: gen_heapGS Arch.pa (bv 8) Σ;
}.

(* register points-to: [r |->r v] owns register [r] holding [v]. *)
Definition reg_pointsto `{!riscvGS Σ} (r : register) (dq : dfrac)
    (v : type_of_register r) : iProp Σ :=
  pointsto (L:=register) (V:=sigT type_of_register) r dq (existT r v).

Notation "r ↦ᵣ{ dq } v" := (reg_pointsto r dq v)
  (at level 20, dq custom dfrac at level 1, format "r  ↦ᵣ{ dq }  v") : bi_scope.
Notation "r ↦ᵣ v" := (reg_pointsto r (DfracOwn 1) v)
  (at level 20, format "r  ↦ᵣ  v") : bi_scope.
(* A physical byte address lies in "real" RAM iff it is outside the platform
   MMIO ranges.  We capture the two PURE (state-independent) ranges checked by
   the model's [within_clint]/[within_sig]: an access fully inside one of those
   ranges is treated as MMIO.  Owning a memory points-to will require the byte
   to be RAM, which discharges [within_clint]/[within_sig] (see
   [within_clint_false]/[within_sig_false]).  ([within_htif] depends on the
   [htif_tohost_base] register, not the address, so it is handled separately by
   owning that register.) *)
Definition not_in_clint (a : Arch.pa) : Prop :=
  (uint a < uint plat_clint_base \/ uint plat_clint_base + uint plat_clint_size <= uint a)%Z.
Definition not_in_sig (a : Arch.pa) : Prop :=
  (uint a < uint plat_sig_base \/ uint plat_sig_base + uint plat_sig_size <= uint a)%Z.
Definition addr_is_ram (a : Arch.pa) : Prop := not_in_clint a /\ not_in_sig a.

(* memory points-to: owns byte [a |-> v] AND records that [a] is real RAM. *)
Definition mem_pointsto `{!riscvGS Σ} (a : Arch.pa) (v : bv 8) : iProp Σ :=
  (pointsto (L:=Arch.pa) (V:=bv 8) a (DfracOwn 1) v ∗ ⌜addr_is_ram a⌝)%I.
Notation "a ↦ₘ v" := (mem_pointsto a v)
  (at level 20, format "a  ↦ₘ  v") : bi_scope.

(* ---------------------------------------------------------------------- *)
(* 2. The bridge: an existential register map agreeing with [regstate].    *)
(* ---------------------------------------------------------------------- *)

Definition reg_agree (m : gmap register (sigT type_of_register))
    (rs : regstate) : Prop :=
  forall r dv, m !! r = Some dv -> dv = existT r (register_lookup r rs).

Definition reg_interp `{!riscvGS Σ} (rs : regstate) : iProp Σ :=
  (∃ m, gen_heap_interp m ∗ ⌜reg_agree m rs⌝)%I.

(* ---------------------------------------------------------------------- *)
(* 3. irisGS instance: state_interp = (register bridge) * (memory heap).   *)
(* ---------------------------------------------------------------------- *)

Global Program Instance riscv_irisGS `{!riscvGS Σ} : irisGS riscv_lang Σ := {
  iris_invGS := riscv_invGS;
  state_interp s _ _ _ := (reg_interp s.(sregs) ∗ gen_heap_interp s.(mem))%I;
  fork_post _ := True%I;
  num_laters_per_step _ := 0%nat;
}.
Next Obligation. intros. iIntros "H". by iModIntro. Qed.

(* ---------------------------------------------------------------------- *)
(* 4. Bridge lemmas.                                                       *)
(* ---------------------------------------------------------------------- *)

Section Bridge.
  Context `{!riscvGS Σ}.

  (* reading a register cell agrees with the model's [register_lookup]. *)
  Lemma reg_valid rs r v :
    reg_interp rs -∗ r ↦ᵣ v -∗ ⌜register_lookup r rs = v⌝.
  Proof.
    rewrite /reg_pointsto /reg_interp.
    iIntros "Hi Hr". iDestruct "Hi" as (m) "[Hm %Hag]".
    iDestruct (gen_heap_valid with "Hm Hr") as %Hlk.
    iPureIntro. symmetry. by apply reg_existT_inj, (Hag r _ Hlk).
  Qed.

  (* writing a register cell tracks the model's [register_set]. *)
  Lemma reg_update rs r v v' :
    reg_interp rs -∗ r ↦ᵣ v ==∗
      reg_interp (register_set r v' rs) ∗ r ↦ᵣ v'.
  Proof.
    rewrite /reg_pointsto /reg_interp.
    iIntros "Hi Hr". iDestruct "Hi" as (m) "[Hm %Hag]".
    iMod (gen_heap_update _ r _ (existT r v') with "Hm Hr") as "[Hm $]".
    iModIntro. iExists (<[r := existT r v']> m). iFrame "Hm".
    iPureIntro. intros k dv Hk.
    destruct (decide (k = r)) as [->|Hne].
    - rewrite lookup_insert in Hk. injection Hk as <-.
      by rewrite register_lookup_set.
    - rewrite lookup_insert_ne in Hk; [|done].
      rewrite (Hag k dv Hk).
      by rewrite (irrelevant_register_set k r rs v' (register_beq_false k r Hne)).
  Qed.

  (* reading a memory byte agrees with the byte heap. *)
  Lemma mem_valid (mm : gmap Arch.pa (bv 8)) a b :
    gen_heap_interp mm -∗ a ↦ₘ b -∗ ⌜mm !! a = Some b⌝.
  Proof.
    iIntros "Hm [Ha _]". by iDestruct (gen_heap_valid with "Hm Ha") as %?.
  Qed.

  (* owning a memory byte certifies its address is real RAM (not MMIO). *)
  Lemma mem_ram a b : a ↦ₘ b -∗ ⌜addr_is_ram a⌝.
  Proof. by iIntros "[_ %H]". Qed.

End Bridge.

(* ===== RiscvModelExec ===== *)
(* ====================================================================== *)
(* RiscvModelExec.v                                                        *)
(*                                                                         *)
(* A functional partial interpreter [exec] mirroring the relational [run] *)
(* of RiscvModelLang, plus the DETERMINISM bridge:                         *)
(*   exec m s = Some (x,s')  ->  run m s x s'  /\  run m s is unique.      *)
(* From that, a single reusable WP rule [wp_exec_step]: a deterministic    *)
(* op whose [exec] yields [Some (tt, s')] gives a WP step, with NO         *)
(* per-instruction determinism reasoning (the unique-run discharges        *)
(* wp_lift_step's "forall next-state" obligation).                         *)
(*                                                                         *)
(* [run]/[prim_step]/RiscvModelLang are UNCHANGED; [exec] is auxiliary.    *)
(*                                                                         *)
(* The pure byte/bitvector arithmetic ([read_bytes], [read_bytes_spec],    *)
(* [bv_eq_of_bytes], ...) lives in RiscvModelBytes.v, which is iris-free    *)
(* so that vanilla Coq [rewrite ... by ...] / comma-chained rewrites work   *)
(* there.  RiscvModelBytes re-defines [pa_add]/[nth_byte] with the *same*   *)
(* bodies as RiscvModelLang's, so they are definitionally convertible and   *)
(* the lemmas below relate to [run] by conversion (no extra bridging).      *)
(* ====================================================================== *)



Local Open Scope Z_scope.

(* ---------------------------------------------------------------------- *)
(* 1. exec: the functional partial interpreter (mirrors run).              *)
(* ---------------------------------------------------------------------- *)

Fixpoint exec {X} (m : M X) (s : mstate) {struct m} : option (X * mstate) :=
  match m with
  | Interface.Ret y => Some (y, s)
  | Interface.Next oc k =>
      (match oc in Interface.outcome _ T return (T -> M X) -> option (X * mstate) with
       | Interface.RegRead r _ => fun k => exec (k (register_lookup r s.(sregs))) s
       | Interface.RegWrite r _ v => fun k => exec (k tt) (set_reg s r v)
       | Interface.MemRead n req => fun k =>
           match read_bytes s.(mem) (Interface.ReadReq.pa req) n with
           | Some w => exec (k (inl (w, None))) s
           | None => None
           end
       | Interface.MemWrite n req => fun k =>
           exec (k (inl None))
                (set_mem s (Interface.WriteReq.pa req)
                           (bv_extract 0 8 (Interface.WriteReq.value req)))
       | Interface.InstrAnnounce _   => fun k => exec (k tt) s
       | Interface.BranchAnnounce _ _=> fun k => exec (k tt) s
       | Interface.Barrier _         => fun k => exec (k tt) s
       | Interface.CacheOp _         => fun k => exec (k tt) s
       | Interface.TlbOp _           => fun k => exec (k tt) s
       | Interface.TakeException _   => fun k => exec (k tt) s
       | Interface.ReturnException _ => fun k => exec (k tt) s
       | Interface.TranslationStart _=> fun k => exec (k tt) s
       | Interface.TranslationEnd _  => fun k => exec (k tt) s
       | Interface.CycleCount        => fun k => exec (k tt) s
       | Interface.Message _         => fun k => exec (k tt) s
       | Interface.GetCycleCount     => fun k => exec (k 0%Z) s
       | _ => fun _ => None   (* Choose / GenericFail / Discard / ExtraOutcome: stuck *)
       end) k
  end.

(* ---------------------------------------------------------------------- *)
(* 2. Determinism bridge: exec success => the unique run.                  *)
(* ---------------------------------------------------------------------- *)

Lemma exec_run_det {X} (m : M X) :
  forall s x s', exec m s = Some (x, s') ->
    run m s x s' /\ (forall y s2, run m s y s2 -> y = x /\ s2 = s').
Proof.
  induction m as [y|T oc k IH]; intros s x s' Hexec.
  - (* Ret *) simpl in Hexec. injection Hexec as <- <-. simpl. split.
    + done.
    + intros y2 s2 [<- <-]. done.
  - (* Next *) destruct oc; simpl in Hexec; try discriminate;
      (* handle the deterministic non-memory branches uniformly *)
      try (split;
           [ apply (proj1 (IH _ _ _ _ Hexec))
           | intros y2 s2 Hr; simpl in Hr; exact (proj2 (IH _ _ _ _ Hexec) _ _ Hr) ]).
    + (* MemRead *)
      destruct (read_bytes s.(mem) _ _) as [w0|] eqn:Hrb;
        [|discriminate].
      destruct (IH (inl (w0, None)) s x s' Hexec) as [Hrun0 Huniq0].
      split.
      * simpl. exists w0. split; [|exact Hrun0].
        intros j Hj. apply (read_bytes_spec _ _ _ _ Hrb j Hj).
      * intros y2 s2 Hr. simpl in Hr. destruct Hr as (w & Hbytes & Hrun).
        assert (Hweq : w = w0).
        { apply bv_eq_of_bytes. intros j Hj.
          pose proof (read_bytes_spec _ _ _ _ Hrb j Hj) as H0.
          pose proof (Hbytes j Hj) as Hw.
          rewrite Hw in H0. apply Some_inj in H0. exact H0. }
        subst w. exact (Huniq0 _ _ Hrun).
Qed.

(* ---------------------------------------------------------------------- *)
(* 3. The reusable WP rule for deterministic ops.                          *)
(* ---------------------------------------------------------------------- *)

Section WPExec.
  Context `{!riscvGS Σ}.

  Lemma wp_exec_step E Φ :
    (∀ σ ns κs nt, state_interp σ ns κs nt ={E,∅}=∗
       ∃ σ', ⌜exec riscv_step σ = Some (tt, σ')⌝ ∗
          ▷ (|={∅,E}=> state_interp σ' (S ns) κs nt ∗ WP (Loop : expr riscv_lang) @ E {{ Φ }}))
    ⊢ WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    iIntros "H".
    iApply wp_lift_step; first done.
    iIntros (σ ns κ κs nt) "Hσ".
    iMod ("H" with "Hσ") as (σ') "[%Hexec H]".
    pose proof (exec_run_det _ _ _ _ Hexec) as [Hrun Huniq].
    iModIntro. iSplitR.
    { iPureIntro. exists [], Loop, σ', []. red.
      split; [done|]. split; [done|]. split; [done|]. split; [done|].
      exists tt. exact Hrun. }
    iIntros (e2 σ2 efs Hstep) "!>".
    destruct Hstep as (_ & -> & _ & -> & u & Hr2).
    destruct (Huniq _ _ Hr2) as [_ ->].
    iMod "H" as "[$ $]". iIntros "_ !>". done.
  Qed.

End WPExec.

(* Now that the Lang/Iris/Exec sections (which must share stdpp's bv_countable   *)
(* with RiscvModelBytes for [mstate.mem]) are defined, bring in the model's      *)
(* Base/Values/TypeCasts for the remaining proof sections.                        *)
Require Import SailStdpp.Base SailStdpp.TypeCasts.
(* Re-import the model AFTER Base so the model's names (read_kind/Read_plain/…)  *)
(* win over SailStdpp's homonyms for the sections below — matching the original  *)
(* per-file import order (model imported last).  mstate.mem's type is already    *)
(* fixed (bv_countable) from the Lang section above, so this does not retype it.  *)
Require Import Riscv.rv64d_types Riscv.rv64d.

(* ===== RiscvModelExecClose ===== *)
(* ====================================================================== *)
(* RiscvModelExecClose.v                                                   *)
(*                                                                         *)
(* Close the ADD weakest-precondition via the deterministic-step route:    *)
(* prove [exec riscv_step s = Some (tt, s_final)] and apply [wp_exec_step]  *)
(* (no Hcycle, no per-instruction determinism).                            *)
(* ====================================================================== *)




Local Open Scope Z_scope.

(* ---------------------------------------------------------------------- *)
(* 1. run_to_exec: a proven [run]-fact becomes an [exec]-fact, given that  *)
(*    exec makes progress (does not hit Choose/fail).  Free corollary of   *)
(*    exec_run_det.                                                         *)
(* ---------------------------------------------------------------------- *)

Lemma run_to_exec {X} (m : M X) (s : mstate) (x : X) (s' : mstate) :
  run m s x s' -> exec m s <> None -> exec m s = Some (x, s').
Proof.
  intros Hrun Hne.
  destruct (exec m s) as [[x'' s'']|] eqn:He; [|exfalso; by apply Hne].
  destruct (exec_run_det _ _ _ _ He) as [_ Huniq].
  destruct (Huniq _ _ Hrun) as [-> ->]. reflexivity.
Qed.

(* ---------------------------------------------------------------------- *)
(* 2. exec_bind: the option-monad functional equation for exec over bind.  *)
(* ---------------------------------------------------------------------- *)

Lemma bind_Ret {X Y} (y : X) (f : X -> M Y) :
  Defs.bind (Interface.Ret y) f = f y.
Proof. reflexivity. Qed.

Lemma bind_Next {X Y T} (oc : Interface.outcome (fun _ => exception) T)
      (k : T -> M X) (f : X -> M Y) :
  Defs.bind (Interface.Next oc k) f = Interface.Next oc (fun z => Defs.bind (k z) f).
Proof. reflexivity. Qed.

Lemma exec_bind {X Y} (m : M X) (f : X -> M Y) :
  forall s, exec (Defs.bind m f) s
          = match exec m s with
            | Some (x, s1) => exec (f x) s1
            | None => None
            end.
Proof.
  induction m as [y | T oc k IH]; intros s.
  - rewrite bind_Ret. reflexivity.
  - rewrite bind_Next. destruct oc; cbn [exec];
      try (apply IH); try reflexivity;
      (* only MemRead remains *)
      destruct (read_bytes _ _ _) as [w|]; [apply IH | reflexivity].
Qed.

Lemma exec_bind0 {Y} (m : M unit) (n : M Y) :
  forall s, exec (Defs.bind0 m n) s
          = match exec m s with Some (_, s1) => exec n s1 | None => None end.
Proof. intros s. unfold Defs.bind0. rewrite exec_bind. by destruct (exec m s) as [[??]|]. Qed.

Lemma exec_returnm {X} (x : X) s : exec (Defs.returnm x) s = Some (x, s).
Proof. reflexivity. Qed.

(* ===== RiscvModelWPclose ===== *)
(* ====================================================================== *)
(* RiscvModelWPclose.v                                                     *)
(*                                                                         *)
(* Close exec_riscv_step_ADD (the try_step wrapper around the proven       *)
(* exec_hart_active reduction, done FUNCTIONALLY via exec_bind) and        *)
(* wp_add_real_closed (via wp_exec_step) -- no Hcycle, no per-instruction  *)
(* determinism.                                                            *)
(* ====================================================================== *)



Local Open Scope Z_scope.

(* ---------------------------------------------------------------------- *)
(* Rewrite-friendly exec-bind: collapse the [match exec m s with ...] when *)
(* the head's exec result is known.                                        *)
(* ---------------------------------------------------------------------- *)

Lemma exec_bind_Some {X Y} (m : M X) (f : X -> M Y) s v st :
  exec m s = Some (v, st) -> exec (Defs.bind m f) s = exec (f v) st.
Proof. intros H. rewrite exec_bind H. reflexivity. Qed.

Lemma exec_bind0_Some {Y} (m : M unit) (n : M Y) s u st :
  exec m s = Some (u, st) -> exec (Defs.bind0 m n) s = exec n st.
Proof. intros H. rewrite exec_bind0 H. reflexivity. Qed.

(* exec-leaves (functional twins of run_read_reg / run_write_reg). *)
Lemma exec_read_reg (r : register) s :
  exec (Defs.read_reg r : M _) s = Some (register_lookup r s.(sregs), s).
Proof. reflexivity. Qed.

Lemma exec_write_reg (r : register) (v : type_of_register r) s :
  exec (Defs.write_reg r v : M _) s = Some (tt, set_reg s r v).
Proof. reflexivity. Qed.

(* tick_pc copies nextPC -> PC; value is pc_write_callback _ = tt. *)
Lemma exec_tick_pc s :
  exec (tick_pc tt) s = Some (tt, set_reg s PC (register_lookup nextPC s.(sregs))).
Proof.
  unfold tick_pc.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg nextPC s)).
  rewrite (exec_bind0_Some _ _ _ _ _ (exec_write_reg PC _ s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg PC _)).
  reflexivity.
Qed.

(* ---------------------------------------------------------------------- *)
(* exec_riscv_step_ADD: thread the try_step wrapper around the hart-active *)
(* reduction (Hha), FUNCTIONALLY via exec_bind.  s_final is explicit.      *)
(* ---------------------------------------------------------------------- *)

Section StepADD.
  Context (s s_exec : mstate) (w : mword 32) (b : bool) (pc : mword 64).

  Hypothesis Hpriv : register_lookup cur_privilege s.(sregs) = Machine.
  Hypothesis Hsi   : exec (should_inc_minstret Machine) s = Some (b, s).
  Let s_a : mstate := set_reg s (R_bool minstret_increment) b.
  Hypothesis Hhart_a : register_lookup hart_state s_a.(sregs) = HART_ACTIVE tt.
  Hypothesis Hha :
    exec (run_hart_active 0) s_a
      = Some (Step_Execute (RETIRE_SUCCESS, zero_extend' 32 w), s_exec).
  Hypothesis Hhart_exec : register_lookup hart_state s_exec.(sregs) = HART_ACTIVE tt.
  Hypothesis Hmi_exec :
    register_lookup (R_bool minstret_increment) s_exec.(sregs) = b.
  Hypothesis Hrvfi : get_config_rvfi tt = false.

  Let s_tick : mstate := set_reg s_exec PC (register_lookup nextPC s_exec.(sregs)).
  Let s_final : mstate :=
    if b then set_reg s_tick minstret
                      (add_vec_int (register_lookup minstret s_tick.(sregs)) 1)
         else s_tick.

  Lemma exec_riscv_step_ADD : exec riscv_step s = Some (tt, s_final).
  Proof using All.
    unfold riscv_step.
    rewrite (exec_bind_Some _ _ _ _ _
              (_ : exec (try_step 0 false) s = Some (false, s_final))).
    { reflexivity. }
    (* now prove exec (try_step 0 false) s = Some (false, s_final) *)
    unfold try_step.
    cbn [ext_pre_step_hook].
    (* read cur_privilege *)
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)).
    cbn beta. rewrite Hpriv.
    (* should_inc_minstret Machine -> b *)
    rewrite (exec_bind_Some _ _ _ _ _ Hsi). cbn beta.
    (* write minstret_increment b >> read hart_state *)
    rewrite (exec_bind0_Some _ _ _ _ _ (exec_write_reg (R_bool minstret_increment) b s)).
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg hart_state s_a)).
    cbn beta. rewrite Hhart_a. cbn beta iota.
    (* run_hart_active 0 -> Step_Execute (RETIRE_SUCCESS, _), s_exec *)
    rewrite (exec_bind_Some _ _ _ _ _ Hha). cbn beta.
    unfold RETIRE_SUCCESS. cbn beta iota.
    (* try_step TAIL: BODY = bind (bind0 ARM (read hart_state)) (fun w10 => MATCH10). *)
    (* Step A: exec (bind0 ARM (read hart_state)) s_exec = Some (HART_ACTIVE tt, s_exec). *)
    erewrite exec_bind_Some.
    2:{ erewrite exec_bind0_Some.
        2:{ (* exec ARM s_exec = Some(tt, s_exec) *)
            erewrite exec_bind_Some.
            2:{ apply exec_read_reg. }
            rewrite Hhart_exec. unfold Defs.assert_exp. cbn [hart_is_active].
            reflexivity. }
        (* exec (read hart_state) s_exec = Some(HART_ACTIVE tt, s_exec) *)
        apply exec_read_reg. }
    rewrite Hhart_exec. cbn beta iota.
    (* REST10 = bind0 (tick_pc) (bind (and_boolM (returnM true)(read mi)) (fun w12 => TAIL2)) *)
    erewrite exec_bind0_Some.
    2:{ apply exec_tick_pc. }
    erewrite exec_bind_Some.
    2:{ unfold Defs.and_boolM.
        erewrite exec_bind_Some.
        2:{ reflexivity. }
        cbn beta iota. apply (exec_read_reg minstret_increment). }
    rewrite Hrvfi.
    replace (register_lookup minstret_increment
               (set_reg s_exec PC (register_lookup nextPC s_exec.(sregs))).(sregs))
      with b.
    2:{ unfold set_reg; cbn [sregs].
        rewrite irrelevant_register_set;
          [ (exact Hmi_exec || (symmetry; exact Hmi_exec)) | reflexivity ]. }
    unfold s_final, s_tick.
    destruct b.
    - (* b = true: minstret += 1 *)
      erewrite exec_bind0_Some.
      2:{ erewrite exec_bind0_Some.
          2:{ erewrite exec_bind_Some.
              2:{ apply (exec_read_reg minstret). }
              apply exec_write_reg. }
          cbn beta iota. reflexivity. }
      reflexivity.
    - (* b = false *)
      erewrite exec_bind0_Some.
      2:{ erewrite exec_bind0_Some.
          2:{ cbn beta iota. reflexivity. }
          cbn beta iota. reflexivity. }
      reflexivity.
  Qed.

End StepADD.

(* ===== RiscvModelWP ===== *)
(* ====================================================================== *)
(* RiscvModelWP.v  —  machinery toward wp_add THROUGH the real try_step.   *)
(* ====================================================================== *)




(* ---------------------------------------------------------------------- *)
(* Compositional reduction lemmas for the interpreter [run].               *)
(* ---------------------------------------------------------------------- *)

(* NB: these proofs are CONVERSION-LAZY (iff_refl / exact / destruct reduce only
   to weak-head normal form, picking a single [outcome] branch).  We avoid
   [cbn [run]] / [simpl run], which eagerly expand the whole 20-branch GADT
   match of [run] and blow up memory. *)

Lemma run_ret {X} (x0 : X) s y s' :
  run (Defs.returnm x0) s y s' <-> (y = x0 /\ s' = s).
Proof. apply iff_refl. Qed.

Lemma run_bind {X Y} (m : M Y) (f : Y -> M X) s x s' :
  run (Defs.bind m f) s x s' <->
  (exists y s1, run m s y s1 /\ run (f y) s1 x s').
Proof.
  unfold Defs.bind. revert s. induction m as [y0 | T oc k IH]; intros s.
  - split.
    + intro H. exists y0, s. split; [ split; reflexivity | exact H ].
    + intros (y & s1 & [Hy Hs] & H). subst y s1. exact H.
  - destruct oc;
      first
        [ (* simple state-threading outcomes: goal convertible to IH *)
          exact (IH _ _)
        | (* MemRead: exists w, byte-match /\ run (k (inl (w,None))) *)
          (split;
           [ intro H; destruct H as (w & HP & H); apply IH in H;
             destruct H as (yy & s1 & Hk & Hf);
             exists yy, s1; split; [ exists w; split; assumption | assumption ]
           | intros (yy & s1 & H & Hf); destruct H as (w & HP & Hk);
             exists w; split;
             [ assumption | apply IH; exists yy, s1; split; assumption ] ])
        | (* Choose: exists c, run (k c) *)
          (split;
           [ intro H; destruct H as (c & H); apply IH in H;
             destruct H as (yy & s1 & Hk & Hf);
             exists yy, s1; split; [ exists c; assumption | assumption ]
           | intros (yy & s1 & H & Hf); destruct H as (c & Hk);
             exists c; apply IH; exists yy, s1; split; assumption ])
        | (* failure / discard / injected-exception: stuck (False) *)
          (split; [ intro H; destruct H | intros (yy & s1 & H & _); destruct H ]) ].
Qed.

(* Sequencing with unit-result first action. *)
Lemma run_bind0 {X} (m : M unit) (n : M X) s x s' :
  run (Defs.bind0 m n) s x s' <->
  (exists s1, run m s tt s1 /\ run n s1 x s').
Proof.
  unfold Defs.bind0. rewrite run_bind. split.
  - intros (y & s1 & Hm & Hn). destruct y. eauto.
  - intros (s1 & Hm & Hn). exists tt, s1. auto.
Qed.

(* Per-effect step lemmas: register read / write through the real
   [read_reg]/[write_reg] of the model. *)
Lemma run_read_reg (r : register) s (x : type_of_register r) s' :
  run (Defs.read_reg r : M _) s x s' <->
  (x = register_lookup r s.(sregs) /\ s' = s).
Proof. apply iff_refl. Qed.

Lemma run_write_reg (r : register) (v : type_of_register r) s x s' :
  run (Defs.write_reg r v : M _) s x s' <->
  (x = tt /\ s' = set_reg s r v).
Proof. apply iff_refl. Qed.

(* [returnM] is [Defs.returnm] specialised to the model's exception type. *)
Lemma run_returnM {X} (x0 : X) s y s' :
  run (returnM x0) s y s' <-> (y = x0 /\ s' = s).
Proof. unfold returnM. apply run_ret. Qed.

(* ===== RiscvModelMR ===== *)
(* ====================================================================== *)
(* RiscvModelMR.v  —  the MR (early-return) monad bridge.                   *)
(*                                                                         *)
(* run_hart_active runs in the early-return monad                          *)
(*   monadR R E := iMon (fun _ => (R + E))   [= monad (R+E)]               *)
(* via [catch_early_return], [liftR], [early_return], [returnR], with the  *)
(* SAME [>>=]/[>>] (Defs.bind/bind0) as the base monad.                    *)
(*                                                                         *)
(* We give an early-return-aware interpreter [runR] (result [R + X]:       *)
(* [inl r] = early-returned r, [inr x] = fell through with x), its         *)
(* bind/liftR/early_return/ret laws, and the bridge                        *)
(*   run (catch_early_return body) <-> runR body falls-through-or-returns. *)
(*                                                                         *)
(* CONVERSION-LAZY proofs only (iff_refl / destruct-to-WHNF / exact).      *)
(* Never [cbn [run]]/[cbn [runR]] (20-branch GADT -> OOM).                 *)
(* ====================================================================== *)




(* ---------------------------------------------------------------------- *)
(* The early-return-aware interpreter for [monadR R exception X].          *)
(* Same effect handling as [run]; additionally an [ExtraOutcome (inl r)]   *)
(* (i.e. [early_return r]) yields result [inl r], and [ExtraOutcome (inr   *)
(* e)] (a genuine exception) is stuck.                                     *)
(* ---------------------------------------------------------------------- *)

Fixpoint runR {R X} (m : Defs.monadR R exception X)
    (s : mstate) (res : R + X) (s' : mstate) {struct m} : Prop :=
  match m with
  | Interface.Ret y => res = inr y /\ s' = s
  | Interface.Next oc k =>
      (match oc in Interface.outcome _ T
             return (T -> Defs.monadR R exception X) -> Prop with
       | Interface.RegRead r _ =>
           fun k => runR (k (register_lookup r s.(sregs))) s res s'
       | Interface.RegWrite r _ v =>
           fun k => runR (k tt) (set_reg s r v) res s'
       | Interface.MemRead n req =>
           fun k => exists w : bv (8 * n),
             (forall j : nat, (N.of_nat j < n)%N ->
                s.(mem) !! (pa_add (Interface.ReadReq.pa req) j) = Some (nth_byte w j))
             /\ runR (k (inl (w, None))) s res s'
       | Interface.MemWrite n req =>
           fun k =>
             runR (k (inl None))
                  (set_mem s (Interface.WriteReq.pa req)
                             (bv_extract 0 8 (Interface.WriteReq.value req))) res s'
       | Interface.InstrAnnounce _    => fun k => runR (k tt) s res s'
       | Interface.BranchAnnounce _ _ => fun k => runR (k tt) s res s'
       | Interface.Barrier _          => fun k => runR (k tt) s res s'
       | Interface.CacheOp _          => fun k => runR (k tt) s res s'
       | Interface.TlbOp _            => fun k => runR (k tt) s res s'
       | Interface.TakeException _    => fun k => runR (k tt) s res s'
       | Interface.ReturnException _  => fun k => runR (k tt) s res s'
       | Interface.TranslationStart _ => fun k => runR (k tt) s res s'
       | Interface.TranslationEnd _   => fun k => runR (k tt) s res s'
       | Interface.CycleCount         => fun k => runR (k tt) s res s'
       | Interface.Message _          => fun k => runR (k tt) s res s'
       | Interface.GetCycleCount      => fun k => runR (k 0%Z) s res s'
       | Interface.Choose _           => fun k => exists c, runR (k c) s res s'
       | Interface.ExtraOutcome e =>
           fun _ => match e with
                    | inl r => res = inl r /\ s' = s
                    | inr _ => False
                    end
       | _ => fun _ => False
       end) k
  end.

(* ---- cheap (convertibility) laws ------------------------------------- *)


Lemma runR_returnR {R X} (x0 : X) s res s' :
  runR (returnR R x0 : Defs.monadR R exception X) s res s' <-> (res = inr x0 /\ s' = s).
Proof. apply iff_refl. Qed.


(* ---- liftR: a lifted base computation never early-returns; its [runR]   *)
(*      coincides with [run] of the base computation (result tagged inr).  *)
Lemma runR_liftR {R X} (m : M X) s res s' :
  runR (Defs.liftR (R:=R) m) s res s' <-> (exists x, res = inr x /\ run m s x s').
Proof.
  unfold Defs.liftR. revert s. induction m as [x0 | T oc k IH]; intros s.
  - split.
    + intros [Hr Hs]. exists x0. split; [exact Hr | split; [reflexivity | exact Hs]].
    + intros (x & Hr & Hx & Hs). subst x. split; [exact Hr | exact Hs].
  - destruct oc;
      first
        [ exact (IH _ _)
        | (split;
           [ intros (w & HP & H); apply IH in H; destruct H as (x & Hr & Hk);
             exists x; split; [exact Hr | exists w; split; [exact HP | exact Hk]]
           | intros (x & Hr & (w & HP & Hk));
             exists w; split; [exact HP | apply IH; exists x; split; [exact Hr | exact Hk]] ])
        | (split;
           [ intros (c & H); apply IH in H; destruct H as (x & Hr & Hk);
             exists x; split; [exact Hr | exists c; exact Hk]
           | intros (x & Hr & (c & Hk));
             exists c; apply IH; exists x; split; [exact Hr | exact Hk] ])
        | (split; [ intro H; destruct H | intros (x & _ & H); destruct H ]) ].
Qed.

(* ---- the bridge: catch_early_return turns an early-return body back into *)
(*      the base monad; both inl/inr at the same value collapse to it.      *)
Lemma run_catch_early_return {X} (body : Defs.monadR X exception X) s x s' :
  run (Defs.catch_early_return body) s x s' <->
  (runR body s (inl x) s' \/ runR body s (inr x) s').
Proof.
  unfold Defs.catch_early_return. revert s. induction body as [a0 | T oc k IH]; intros s.
  - split.
    + intros [Hx Hs]. right. subst x. split; [reflexivity | exact Hs].
    + intros [ [Hc _] | [Heq Hs] ]; [ discriminate Hc | injection Heq as <-; split; [reflexivity | exact Hs] ].
  - destruct oc;
      first
        [ exact (IH _ _)
        | (split;
           [ intros (w & HP & H); apply IH in H; destruct H as [Hk | Hk];
             [ left; exists w; split; [exact HP | exact Hk]
             | right; exists w; split; [exact HP | exact Hk] ]
           | intros [ (w & HP & Hk) | (w & HP & Hk) ];
             [ exists w; split; [exact HP | apply IH; left; exact Hk]
             | exists w; split; [exact HP | apply IH; right; exact Hk] ] ])
        | (split;
           [ intros (c & H); apply IH in H; destruct H as [Hk | Hk];
             [ left; exists c; exact Hk | right; exists c; exact Hk ]
           | intros [ (c & Hk) | (c & Hk) ];
             [ exists c; apply IH; left; exact Hk | exists c; apply IH; right; exact Hk ] ])
        | (match goal with He : (_ + exception)%type |- _ => destruct He as [a0 | ee] end;
           [ split;
             [ intros [Hx Hs]; left; subst x; split; [reflexivity | exact Hs]
             | intros [ [Heq Hs] | [Hc _] ];
               [ injection Heq as <-; split; [reflexivity | exact Hs] | discriminate Hc ] ]
           | split; [ intro H; destruct H | intros [H | H]; destruct H ] ])
        | (split; [ intro H; destruct H | intros [H | H]; destruct H ]) ].
Qed.

(* ---- bind in the early-return monad: short-circuits on early return.    *)
Lemma runR_bind {R X Y} (m : Defs.monadR R exception Y)
    (f : Y -> Defs.monadR R exception X) s res s' :
  runR (Defs.bind m f) s res s' <->
  ((exists r, res = inl r /\ runR m s (inl r) s')
   \/ (exists a s1, runR m s (inr a) s1 /\ runR (f a) s1 res s')).
Proof.
  unfold Defs.bind. revert s. induction m as [a0 | T oc k IH]; intros s.
  - split.
    + intro H. right. exists a0, s. split; [ split; reflexivity | exact H ].
    + intros [ (r & Hr & [Hc _]) | (a & s1 & [Heq Hs] & Hf) ];
        [ discriminate Hc | injection Heq as <-; subst s1; exact Hf ].
  - destruct oc;
      first
        [ exact (IH _ _)
        | (split;
           [ intros (w & HP & H); apply IH in H;
             destruct H as [ (r & Hr & Hk) | (a & s1 & Hk & Hf) ];
             [ left; exists r; split; [exact Hr | exists w; split; [exact HP | exact Hk]]
             | right; exists a, s1; split; [ exists w; split; [exact HP | exact Hk] | exact Hf ] ]
           | intros [ (r & Hr & (w & HP & Hk)) | (a & s1 & (w & HP & Hk) & Hf) ];
             [ exists w; split; [exact HP | apply IH; left; exists r; split; [exact Hr | exact Hk]]
             | exists w; split; [exact HP | apply IH; right; exists a, s1; split; [exact Hk | exact Hf]] ] ])
        | (split;
           [ intros (c & H); apply IH in H;
             destruct H as [ (r & Hr & Hk) | (a & s1 & Hk & Hf) ];
             [ left; exists r; split; [exact Hr | exists c; exact Hk]
             | right; exists a, s1; split; [ exists c; exact Hk | exact Hf ] ]
           | intros [ (r & Hr & (c & Hk)) | (a & s1 & (c & Hk) & Hf) ];
             [ exists c; apply IH; left; exists r; split; [exact Hr | exact Hk]
             | exists c; apply IH; right; exists a, s1; split; [exact Hk | exact Hf] ] ])
        | (match goal with He : (_ + exception)%type |- _ => destruct He as [r0 | ee] end;
           [ split;
             [ intros [Hres Hs]; left; exists r0; split; [exact Hres | split; [reflexivity | exact Hs]]
             | intros [ (r & Hres & [Heq Hs]) | (a & s1 & Hf0 & _) ];
               [ injection Heq as <-; split; [exact Hres | exact Hs]
               | destruct Hf0 as [Hc _]; discriminate Hc ] ]
           | split;
             [ intro H; destruct H
             | intros [ (r & _ & Hf0) | (a & s1 & Hf0 & _) ]; destruct Hf0 ] ])
        | (split;
           [ intro H; destruct H
           | intros [ (r & _ & Hf0) | (a & s1 & Hf0 & _) ]; destruct Hf0 ]) ].
Qed.

(* ---------------------------------------------------------------------- *)

(* ===== RiscvModelEnabled ===== *)
(* ===================================================================== *)
(* RiscvModelEnabled.v — item (2): taming the Acc-recursive extension     *)
(* predicates (`hartSupports`/`currentlyEnabled`) so they reduce through   *)
(* `run`. Proof-of-concept: the `Acc`-guarded well-founded recursion       *)
(* unfolds AXIOM-FREE by `destruct`-ing the `Zwf_guarded` accessibility    *)
(* proof (no Acc proof-irrelevance / funext needed).                       *)
(* ===================================================================== *)

(* `hartSupports Ext_Zca` is a leaf (statically `returnM true`); it runs
   through one Acc-unfold + the reclimit guard to the concrete bool `true`. *)

(* ===== RiscvModelExecute ===== *)
(* ===================================================================== *)
(* RiscvModelExecute.v — home stretch toward wp_add-through-try_step.      *)
(*                                                                         *)
(*  Verified, axiom-free, building on RiscvModel{Lang,WP,MR,Enabled}:      *)
(*   - run step-lemmas for the boolean monad combinators and_boolM/or_boolM*)
(*     (the shape currentlyEnabled / hartSupports are built from);         *)
(*   - run_execute_RTYPE_ADD: the model's REAL `execute (RTYPE .. ADD)`     *)
(*     reduces, compositionally, to read rs1, read rs2, write rd from       *)
(*     add_vec, retire -- the ADD datapath, modulo the register-file        *)
(*     primitives rX_bits/wX_bits (whose concrete-index dispatch + the     *)
(*     run_read_reg/run_write_reg bridge discharge separately).            *)
(* ===================================================================== *)
Import Defs.

(* --------------------------------------------------------------------- *)
(* 1. Boolean-monad combinators step through `run`.                       *)
(*    [and_boolM l r = l >>= fun b => if b then r else returnm false]      *)
(*    [or_boolM  l r = l >>= fun b => if b then returnm true else r]       *)
(*    The `returnm` branches are definitionally the `run`-of-`Ret` facts,  *)
(*    so each side of the `if` lands on the obvious shape.                 *)
(* --------------------------------------------------------------------- *)

Lemma run_and_boolM (l r : M bool) s b s' :
  run (and_boolM l r) s b s' <->
  (exists bl s1, run l s bl s1 /\
                 (if bl then run r s1 b s' else (b = false /\ s' = s1))).
Proof.
  unfold and_boolM. rewrite run_bind. split.
  - intros (bl & s1 & Hl & H). exists bl, s1. split; [exact Hl|]. destruct bl; exact H.
  - intros (bl & s1 & Hl & H). exists bl, s1. split; [exact Hl|]. destruct bl; exact H.
Qed.

Lemma run_or_boolM (l r : M bool) s b s' :
  run (or_boolM l r) s b s' <->
  (exists bl s1, run l s bl s1 /\
                 (if bl then (b = true /\ s' = s1) else run r s1 b s')).
Proof.
  unfold or_boolM. rewrite run_bind. split.
  - intros (bl & s1 & Hl & H). exists bl, s1. split; [exact Hl|]. destruct bl; exact H.
  - intros (bl & s1 & Hl & H). exists bl, s1. split; [exact Hl|]. destruct bl; exact H.
Qed.

(* --------------------------------------------------------------------- *)
(* 2. execute (RTYPE .. ADD) reduces to the ADD datapath.                 *)
(*                                                                         *)
(*    execute_RTYPE rs2 rs1 rd ADD                                         *)
(*      = (rX_bits rs1 >>= fun a => rX_bits rs2 >>= fun b =>               *)
(*           returnM (add_vec a b))                                         *)
(*        >>= fun w => wX_bits rd w >> returnM RETIRE_SUCCESS.             *)
(*                                                                         *)
(*    Register reads don't change state, so given the rs1/rs2 reads and    *)
(*    the rd write, the whole thing runs to RETIRE_SUCCESS with exactly    *)
(*    the rd-write's effect.                                               *)
(* --------------------------------------------------------------------- *)

Lemma run_execute_RTYPE_ADD (rs2 rs1 rd : regidx) (a b : mword 64) s s' :
  run (rX_bits rs1) s a s ->
  run (rX_bits rs2) s b s ->
  run (wX_bits rd (add_vec a b)) s tt s' ->
  run (execute_RTYPE rs2 rs1 rd ADD) s RETIRE_SUCCESS s'.
Proof.
  intros Ha Hb Hw.
  unfold execute_RTYPE. cbn match.
  (* outer bind: inner computes (add_vec a b) leaving state s *)
  apply run_bind. exists (add_vec a b), s. split.
  - (* inner: rX_bits rs1 >>= rX_bits rs2 >>= returnM (add_vec) *)
    apply run_bind. exists a, s. split; [exact Ha|].
    apply run_bind. exists b, s. split; [exact Hb|].
    apply run_returnM. split; reflexivity.
  - (* wX_bits rd (add_vec a b) >> returnM RETIRE_SUCCESS *)
    apply run_bind0. exists s'. split; [exact Hw|].
    apply run_returnM. split; reflexivity.
Qed.

(* ===== RiscvModelRegs ===== *)
(* ===================================================================== *)
(* RiscvModelRegs.v — clears the read_reg-wrapper "blocker" and gives a    *)
(* FULLY CONCRETE execute(ADD) over the real model's register file.        *)
(*                                                                         *)
(* KEY FINDING: the model's `read_reg`/`write_reg` AS USED INSIDE rX/wX     *)
(* (defined in rv64d.v after `Import Defs`) resolve to Defs.read_reg /      *)
(* Defs.write_reg — the Interface-monad ones that run_read_reg/run_write_reg*)
(* already target.  (The `rv64d_types.read_reg` wrapper is the *Prompt*     *)
(* monad and is shadowed; the earlier "mismatch" was a misread.)  So rX/wX  *)
(* reduce by conversion + the existing bridge lemmas, no new axioms.        *)
(* ===================================================================== *)
Import Defs.

(* --------------------------------------------------------------------- *)
(* 1. rX / wX at concrete registers reduce to Defs.read_reg/write_reg.     *)
(*    These hold BY CONVERSION (the 32-way Z.eqb index dispatch computes;   *)
(*    regval_into_reg is the identity on mword 64).                         *)
(* --------------------------------------------------------------------- *)

Lemma rX_x10 : rX (Regno 10) = Defs.read_reg (R_bitvector_64 x10).
Proof. reflexivity. Qed.
Lemma rX_x11 : rX (Regno 11) = Defs.read_reg (R_bitvector_64 x11).
Proof. reflexivity. Qed.
(* wX threads the value through [regval_into_reg] (= identity on mword 64, but
   kept symbolic here since it does not auto-reduce under conversion). *)

(* run versions: register reads are state-pure, writes go via set_reg. *)
Lemma run_rX_x10 s :
  run (rX (Regno 10)) s (register_lookup (R_bitvector_64 x10) s.(sregs)) s.
Proof. rewrite rX_x10. split; reflexivity. Qed.
Lemma run_rX_x11 s :
  run (rX (Regno 11)) s (register_lookup (R_bitvector_64 x11) s.(sregs)) s.
Proof. rewrite rX_x11. split; reflexivity. Qed.
(* wX = write_reg .. >> returnM (xreg_full_write_callback ..); the callback is
   [tt] (xreg_full_write_callback _ _ _ := tt), so wX is a write then return tt. *)
Lemma wX_x12_eq (v : mword 64) :
  wX (Regno 12) v
  = Defs.bind0 (Defs.write_reg (R_bitvector_64 x12) (regval_into_reg v)) (returnM tt).
Proof. reflexivity. Qed.

Lemma run_wX_x12 s (v : mword 64) :
  run (wX (Regno 12) v) s tt (set_reg s (R_bitvector_64 x12) (regval_into_reg v)).
Proof.
  rewrite wX_x12_eq. apply run_bind0.
  exists (set_reg s (R_bitvector_64 x12) (regval_into_reg v)). split.
  - split; reflexivity.
  - split; reflexivity.
Qed.

(* --------------------------------------------------------------------- *)
(* 2. Lift to rX_bits / wX_bits given the register index value.            *)
(*    rX_bits (Regidx i) = rX (Regno (uint i)); supply `uint i = n`.        *)
(* --------------------------------------------------------------------- *)

Lemma run_rX_bits_x10 (i : mword 5) s :
  uint i = 10 ->
  run (rX_bits (Regidx i)) s (register_lookup (R_bitvector_64 x10) s.(sregs)) s.
Proof. intro H. unfold rX_bits; cbn match. rewrite H. apply run_rX_x10. Qed.
Lemma run_rX_bits_x11 (i : mword 5) s :
  uint i = 11 ->
  run (rX_bits (Regidx i)) s (register_lookup (R_bitvector_64 x11) s.(sregs)) s.
Proof. intro H. unfold rX_bits; cbn match. rewrite H. apply run_rX_x11. Qed.
Lemma run_wX_bits_x12 (i : mword 5) s (v : mword 64) :
  uint i = 12 ->
  run (wX_bits (Regidx i) v) s tt (set_reg s (R_bitvector_64 x12) (regval_into_reg v)).
Proof. intro H. unfold wX_bits; cbn match. rewrite H. apply run_wX_x12. Qed.

(* --------------------------------------------------------------------- *)
(* 3. FULLY CONCRETE execute(ADD): add x12, x10, x11 over the real model.  *)
(*    rd=x12, rs1=x10, rs2=x11 (distinct, non-zero).  No hypotheses beyond  *)
(*    the register-index values; no axioms.                                *)
(* --------------------------------------------------------------------- *)

Lemma run_execute_ADD_x12_x10_x11 (rd rs1 rs2 : mword 5) s :
  uint rs1 = 10 -> uint rs2 = 11 -> uint rd = 12 ->
  run (execute_RTYPE (Regidx rs2) (Regidx rs1) (Regidx rd) ADD) s RETIRE_SUCCESS
      (set_reg s (R_bitvector_64 x12)
         (regval_into_reg
            (add_vec (register_lookup (R_bitvector_64 x10) s.(sregs))
                     (register_lookup (R_bitvector_64 x11) s.(sregs))))).
Proof.
  intros H1 H2 H3.
  eapply run_execute_RTYPE_ADD.
  - apply run_rX_bits_x10; exact H1.
  - apply run_rX_bits_x11; exact H2.
  - apply run_wX_bits_x12; exact H3.
Qed.

(* ===== RiscvModelMem ===== *)
(* ====================================================================== *)
(* RiscvModelMem.v                                                         *)
(*                                                                         *)
(* Fetch memory subsystem toward discharging Hcycle.                       *)
(* MAIN RESULT: translateAddr = IDENTITY in Machine mode (Bare paging),    *)
(* i.e. the address-translation half of fetch reduces axiom-free.          *)
(* The pmpCheck/mem_read half is mapped + scoped at the bottom.            *)
(* ====================================================================== *)



(* ---------------------------------------------------------------------- *)
(* Forward versions of the iff stepping lemmas (apply needs these to PROVE *)
(* a run/runR goal; the iffs can't be `apply`'d directly).                 *)
(* ---------------------------------------------------------------------- *)

Lemma run_returnM_fwd {X} (x : X) s : run (returnM x) s x s.
Proof. rewrite run_returnM. split; reflexivity. Qed.

Lemma run_read_reg_fwd (r : register) s :
  run (Defs.read_reg r) s (register_lookup r s.(sregs)) s.
Proof. rewrite run_read_reg. split; reflexivity. Qed.

Lemma runR_returnR_fwd {R X} (x : X) s :
  runR (returnR R x : Defs.monadR R exception X) s (inr x) s.
Proof. rewrite runR_returnR. split; reflexivity. Qed.

(* Forward-chaining: walk a `liftR m >>= f` when m is a state-preserving    *)
(* base computation (the read-only effects of fetch).                       *)
Lemma runR_liftR_seq {R X Y} (m : M Y) (f : Y -> Defs.monadR R exception X)
    (a : Y) s res s' :
  run m s a s ->
  runR (f a) s res s' ->
  runR (Defs.bind (Defs.liftR (R:=R) m) f) s res s'.
Proof.
  intros Hm Hf. apply runR_bind. right. exists a, s. split; [|exact Hf].
  apply runR_liftR. exists a. split; [reflexivity|exact Hm].
Qed.

(* ---------------------------------------------------------------------- *)
(* Pure sub-functions on the fetch path reduce to a value (no effects).    *)
(* ---------------------------------------------------------------------- *)

Lemma run_effectivePrivilege_fetch (m : mword 64) (p : Privilege) s :
  run (effectivePrivilege (InstructionFetch tt) m p) s p s.
Proof.
  unfold effectivePrivilege.
  replace (generic_neq (InstructionFetch tt) (InstructionFetch tt)) with false
    by (vm_compute; reflexivity).
  apply run_returnM_fwd.
Qed.

Lemma run_translationMode_M s :
  run (translationMode Machine) s Bare s.
Proof.
  unfold translationMode.
  replace (generic_eq Machine Machine) with true by (vm_compute; reflexivity).
  apply run_returnM_fwd.
Qed.

Lemma run_is_shadow_stack_fetch s :
  run (is_shadow_stack_access (InstructionFetch tt)) s false s.
Proof. unfold is_shadow_stack_access. apply run_returnM_fwd. Qed.

(* ---------------------------------------------------------------------- *)
(* MAIN: translateAddr is the identity in Machine mode (Bare paging).      *)
(* Precondition: cur_privilege reads as Machine.  mstatus value is         *)
(* irrelevant (effectivePrivilege of a fetch ignores MPRV); satp unread.   *)
(* ---------------------------------------------------------------------- *)

Lemma run_translateAddr_identity (a : mword 64) s :
  register_lookup cur_privilege s.(sregs) = Machine ->
  run (translateAddr (Virtaddr a) (InstructionFetch tt)) s
      (Ok (Physaddr (zero_extend' 64 (bits_of_virtaddr (Virtaddr a))),
           PBMT_PMA, init_ext_ptw)) s.
Proof.
  intros Hcp.
  assert (Hrd : run (Defs.read_reg cur_privilege) s Machine s).
  { rewrite run_read_reg. split; [symmetry; exact Hcp | reflexivity]. }
  unfold translateAddr.
  apply run_catch_early_return. right.
  eapply runR_liftR_seq; [ exact (run_read_reg_fwd mstatus s) | ]. (* mstatus *)
  eapply runR_liftR_seq; [ exact Hrd | ].                       (* cur_privilege = Machine *)
  eapply runR_liftR_seq; [ apply run_effectivePrivilege_fetch | ]. (* effPriv = Machine *)
  eapply runR_liftR_seq; [ apply run_translationMode_M | ].     (* mode = Bare *)
  eapply runR_liftR_seq; [ apply run_is_shadow_stack_fetch | ]. (* shadow = false *)
  (* remaining: (if false .. else returnR tt) >> (if generic_eq Bare Bare then returnR (Ok ..)) *)
  unfold Defs.bind0.
  replace (generic_eq Bare Bare) with true by (vm_compute; reflexivity).
  rewrite runR_bind. right. exists tt, s.
  split; apply runR_returnR_fwd.
Qed.

(* ====================================================================== *)
(* RESIDUE (scoped, not proven here): the read side of fetch.             *)
(*   fetch_bytes -> mem_read -> mem_read_priv -> checked_mem_read ->       *)
(*     phys_access_check (= pmpCheck + pmaCheck) + within_mmio_readable    *)
(*     + read_ram (MemRead x4).                                            *)
(*   pmpCheck: catch_early_return over `foreach_ZM_up 0 15 1` ; with all   *)
(*     pmpcfg=0 every iteration hits PMP_NoMatch (pmpMatchAddr: cfg.A=OFF) *)
(*     => state-preserving no-op, then Machine-mode falls to None. Needs a *)
(*     loop-invariant lemma over foreach_ZM_up (the analogue of the Lean   *)
(*     pmpCheck_machine_none / forIn_run_const).                           *)
(*   This is the substantial remaining memory-subsystem milestone.         *)
(* ====================================================================== *)

(* ===== RiscvModelReadRam ===== *)
(* ====================================================================== *)
(* RiscvModelReadRam.v                                                     *)
(*                                                                         *)
(* Payoff of the strengthened `run` MemRead rule: the model's real         *)
(* `read_ram` (which issues ONE `MemRead width`, via `sail_mem_read`)       *)
(* now reduces through `run` given the `width` consecutive memory bytes.    *)
(* This is exactly what the OLD single-byte rule could NOT do (it left the  *)
(* upper bytes of a multi-byte read unconstrained).                        *)
(* ====================================================================== *)



(* read_ram for a plain 4-byte read at [addr], given the 4 consecutive bytes
   of [w] in memory, runs (state-preserving) to a successful value. *)
Lemma run_read_ram_plain_4 (addr : mword 64) (w : bv 32) s :
  (forall j : nat, (N.of_nat j < 4)%N ->
     s.(mem) !! (pa_add addr j) = Some (nth_byte w j)) ->
  exists value : mword (8 * 4),
    run (read_ram Read_plain (Physaddr addr) 4 false) s (value, default_meta) s.
Proof.
  intro Hbytes.
  unfold read_ram. cbn match.
  (* rk = Read_plain : the access-kind computation is a pure returnM *)
  eapply (ex_intro _ _).
  apply (proj2 (run_bind _ _ _ _ _)).
  eexists _, s. split; [ apply run_returnM_fwd | ]. cbn beta zeta.
  (* now: sail_mem_read request >>= match ... *)
  apply (proj2 (run_bind _ _ _ _ _)).
  unfold Defs.sail_mem_read. cbn beta zeta.
  (* the MemRead outcome: provide w as the read value *)
  eexists _, s. split.
  - (* run (Next (MemRead 4 req') k) : the strengthened rule, witness w *)
    cbn match beta. exists w. split.
    + intros j Hj. exact (Hbytes j Hj).
    + apply run_returnM_fwd.
  - cbn match beta. apply run_returnM_fwd.
Qed.

(* ===== RiscvModelPending ===== *)
(* ====================================================================== *)
(* RiscvModelPending.v                                                     *)
(*                                                                         *)
(* Keystone: run (getPendingSet Machine) s None s under boot CSRs.         *)
(*                                                                         *)
(* For priv = Machine the result is None as soon as mIE = false and        *)
(* sIE = false.  sIE = false is FREE (Machine <> Supervisor/User), and     *)
(* mIE = false follows from the boot fact mstatus.MIE = 0.  So both         *)
(* `andb mIE _` and `andb sIE _` are false by computation and pending_m/    *)
(* pending_s are never inspected -- no read_mip=0 / and_vec-zero needed.    *)
(* The only deep sub-call, currentlyEnabled Ext_S (a 2nd Acc-recursion),   *)
(* is carried as a state-preserving hypothesis HcES.                       *)
(* ====================================================================== *)



Import Defs.


(* forward-form helpers (BUILD a run goal from the iff lemmas). *)
Lemma run_bind_fwd {X Y} (m : M Y) (f : Y -> M X) s y s1 x s' :
  run m s y s1 -> run (f y) s1 x s' -> run (Defs.bind m f) s x s'.
Proof. intros H1 H2. apply (proj2 (run_bind _ _ _ _ _)). exists y, s1. split; assumption. Qed.


Lemma run_ret_fwd {X} (x : X) s : run (Defs.returnm x) s x s.
Proof. apply (proj2 (run_ret _ _ _ _)). split; reflexivity. Qed.


Section Pending.
  Context (s : mstate) (cES : bool).

  Hypothesis HcES : run (currentlyEnabled Ext_S) s cES s.
  Hypothesis Hmideleg : register_lookup mideleg s.(sregs) = zeros' 64.
  Hypothesis HmIE :
    eq_vec (_get_Mstatus_MIE (register_lookup mstatus s.(sregs))) ('b"1") = false.

  (* The or_boolM guard before assert_exp' evaluates to true. *)
  Lemma guard_true :
    run (or_boolM (currentlyEnabled Ext_S)
                  (Defs.bind (read_reg mideleg)
                     (fun w1 : mword 64 => returnM (eq_vec w1 (zeros' 64))))) s true s.
  Proof using All.
    apply (proj2 (run_or_boolM _ _ _ _ _)). exists cES, s. split; [exact HcES|].
    destruct cES.
    - split; reflexivity.
    - eapply run_bind_fwd; [exact (run_read_reg_fwd mideleg s)|].
      rewrite Hmideleg.
      rewrite (proj2 (eq_vec_true_iff (zeros' 64) (zeros' 64)) eq_refl).
      apply run_returnM_fwd.
  Qed.

  (* read_mip threads to *some* value (state-preserving); value irrelevant. *)
  Lemma read_mip_runs : exists v, run (read_mip IncludePlatformInterrupts) s v s.
  Proof using All.
    unfold read_mip. cbn match.
    destruct cES.
    - eexists.
      eapply run_bind_fwd; [exact (run_read_reg_fwd mip s)|].
      eapply run_bind_fwd.
      { unfold external_interrupts_pending.
        eapply run_bind_fwd; [exact (run_read_reg_fwd sig_meip s)|].
        eapply run_bind_fwd; [exact HcES|]. cbn match.
        eapply run_bind_fwd; [exact (run_read_reg_fwd sig_seip s)|].
        apply run_returnM_fwd. }
      apply run_returnM_fwd.
    - eexists.
      eapply run_bind_fwd; [exact (run_read_reg_fwd mip s)|].
      eapply run_bind_fwd.
      { unfold external_interrupts_pending.
        eapply run_bind_fwd; [exact (run_read_reg_fwd sig_meip s)|].
        eapply run_bind_fwd; [exact HcES|]. cbn match.
        eapply run_bind_fwd; [apply run_returnM_fwd|].
        apply run_returnM_fwd. }
      apply run_returnM_fwd.
  Qed.

  Lemma run_getPendingSet_machine_none :
    run (getPendingSet Machine) s None s.
  Proof using All.
    destruct read_mip_runs as [mipv Hmip].
    unfold getPendingSet.
    (* guard >>= fun w2 => assert_exp' w2 >>= fun _ => ... *)
    eapply run_bind_fwd; [exact guard_true|].
    (* assert_exp' true _ = returnm eq_refl *)
    eapply run_bind_fwd; [cbn match; apply run_ret_fwd|].
    (* read_mip *)
    eapply run_bind_fwd; [exact Hmip|].
    (* read mie, mideleg (pending_m let), mie, mideleg (pending_s let) *)
    eapply run_bind_fwd; [exact (run_read_reg_fwd mie s)|].
    eapply run_bind_fwd; [exact (run_read_reg_fwd mideleg s)|].
    eapply run_bind_fwd; [exact (run_read_reg_fwd mie s)|].
    eapply run_bind_fwd; [exact (run_read_reg_fwd mideleg s)|].
    (* mIE = false *)
    eapply run_bind_fwd.
    { apply (proj2 (run_or_boolM _ _ _ _ _)). exists false, s. split.
      - (* l = and_boolM (returnM (generic_eq Machine Machine)) (...) = false *)
        apply (proj2 (run_and_boolM _ _ _ _ _)). exists true, s. split.
        + (* returnM (generic_eq Machine Machine) -> true *)
          change (generic_eq Machine Machine) with true. apply run_returnM_fwd.
        + (* read mstatus >>= returnM (eq_vec (MIE) 'b1) -> false (HmIE) *)
          eapply run_bind_fwd; [exact (run_read_reg_fwd mstatus s)|].
          rewrite HmIE. apply run_returnM_fwd.
      - (* bl=false: run r s false s, r = returnM (orb (M=S)(M=U)) = false *)
        change (orb (generic_eq Machine Supervisor) (generic_eq Machine User)) with false.
        apply run_returnM_fwd. }
    (* sIE = false *)
    eapply run_bind_fwd.
    { apply (proj2 (run_or_boolM _ _ _ _ _)). exists false, s. split.
      - (* l = and_boolM (returnM (generic_eq Machine Supervisor=false)) _ = false *)
        apply (proj2 (run_and_boolM _ _ _ _ _)). exists false, s. split.
        + change (generic_eq Machine Supervisor) with false. apply run_returnM_fwd.
        + split; reflexivity.
      - change (generic_eq Machine User) with false. apply run_returnM_fwd. }
    (* final: andb false _ = false twice -> None *)
    cbn [andb]. apply run_returnM_fwd.
  Qed.

End Pending.

(* ===== RiscvModelExecR ===== *)
(* ====================================================================== *)
(* RiscvModelExecR.v  —  the exec-side twin of the runR (MR) bridge.        *)
(*                                                                         *)
(* run_hart_active runs in the early-return monad                          *)
(*   monadR R E := iMon (fun _ => (R+E))   [= monad (R+E)]                  *)
(* via catch_early_return / liftR (built on try_catch).  [exec] is         *)
(* monomorphic to M = monad exception and so does NOT reduce INTO a        *)
(* monadR body.  We give the functional early-return interpreter [execR]   *)
(* (result [R+X]), its bind/liftR laws, and the bridge                     *)
(*   exec (catch_early_return body) s = (execR body, both arms -> value).   *)
(* Plus the determinism transfer (execR success => unique runR), hence     *)
(* runR_to_execR (mirror of run_to_exec).                                  *)
(*                                                                         *)
(* Proof style mirrors the proven exec_bind: rewrite the Ret/Next unfold,  *)
(* then [destruct oc; cbn [execR ...]] (cbn is safe on a CONCRETE oc),     *)
(* then [apply IH] / reflexivity / read_bytes-split / ExtraOutcome-split.  *)
(* ====================================================================== *)




(* ---------------------------------------------------------------------- *)
(* execR: functional early-return interpreter for [monadR R exception X].   *)
(* Mirrors [exec] (functional; Choose/GenericFail/Discard -> None;          *)
(* MemRead via read_bytes) AND [runR]'s early-return handling               *)
(* (ExtraOutcome (inl r) = early-returned r; ExtraOutcome (inr _) stuck).   *)
(* ---------------------------------------------------------------------- *)

Fixpoint execR {R X} (m : Defs.monadR R exception X)
    (s : mstate) {struct m} : option ((R + X) * mstate) :=
  match m with
  | Interface.Ret y => Some (inr y, s)
  | Interface.Next oc k =>
      (match oc in Interface.outcome _ T
             return (T -> Defs.monadR R exception X) -> option ((R + X) * mstate) with
       | Interface.RegRead r _ =>
           fun k => execR (k (register_lookup r s.(sregs))) s
       | Interface.RegWrite r _ v =>
           fun k => execR (k tt) (set_reg s r v)
       | Interface.MemRead n req =>
           fun k =>
             match read_bytes s.(mem) (Interface.ReadReq.pa req) n with
             | Some w => execR (k (inl (w, None))) s
             | None => None
             end
       | Interface.MemWrite n req =>
           fun k =>
             execR (k (inl None))
                   (set_mem s (Interface.WriteReq.pa req)
                              (bv_extract 0 8 (Interface.WriteReq.value req)))
       | Interface.InstrAnnounce _    => fun k => execR (k tt) s
       | Interface.BranchAnnounce _ _ => fun k => execR (k tt) s
       | Interface.Barrier _          => fun k => execR (k tt) s
       | Interface.CacheOp _          => fun k => execR (k tt) s
       | Interface.TlbOp _            => fun k => execR (k tt) s
       | Interface.TakeException _    => fun k => execR (k tt) s
       | Interface.ReturnException _  => fun k => execR (k tt) s
       | Interface.TranslationStart _ => fun k => execR (k tt) s
       | Interface.TranslationEnd _   => fun k => execR (k tt) s
       | Interface.CycleCount         => fun k => execR (k tt) s
       | Interface.Message _          => fun k => execR (k tt) s
       | Interface.GetCycleCount      => fun k => execR (k 0%Z) s
       | Interface.ExtraOutcome e =>
           fun _ => match e with
                    | inl r => Some (inl r, s)
                    | inr _ => None
                    end
       | _ => fun _ => None   (* Choose / GenericFail / Discard: stuck *)
       end) k
  end.

(* ---- Ret/Next unfolding for the monadR-level [Defs.bind] (definitional). *)

Lemma bindR_Ret {R X Y} (y : Y) (f : Y -> Defs.monadR R exception X) :
  Defs.bind (Interface.Ret y : Defs.monadR R exception Y) f = f y.
Proof. reflexivity. Qed.

Lemma bindR_Next {R X Y T} (oc : Interface.outcome (fun _ => (R + exception)%type) T)
    (k : T -> Defs.monadR R exception Y) (f : Y -> Defs.monadR R exception X) :
  Defs.bind (Interface.Next oc k) f = Interface.Next oc (fun z => Defs.bind (k z) f).
Proof. reflexivity. Qed.

(* ---------------------------------------------------------------------- *)
(* bind in the early-return monad (same Defs.bind): short-circuits on inl. *)
(* ---------------------------------------------------------------------- *)

Lemma execR_bind {R X Y} (m : Defs.monadR R exception Y)
    (f : Y -> Defs.monadR R exception X) :
  forall s, execR (Defs.bind m f) s =
    match execR m s with
    | Some (inl r, s') => Some (inl r, s')
    | Some (inr a, s') => execR (f a) s'
    | None => None
    end.
Proof.
  induction m as [a0 | T oc k IH]; intros s.
  - rewrite bindR_Ret. reflexivity.
  - rewrite bindR_Next. destruct oc; cbn [execR];
      try (apply IH); try reflexivity;
      first
        [ match goal with
          | |- context[read_bytes ?mm ?pa ?n] =>
              destruct (read_bytes mm pa n) as [w|]; [apply IH | reflexivity]
          end
        | match goal with
          | He : (_ + exception)%type |- _ => destruct He; reflexivity
          end ].
Qed.

(* ---------------------------------------------------------------------- *)
(* liftR: a lifted base computation never early-returns; execR = exec (inr).*)
(* ---------------------------------------------------------------------- *)

Lemma execR_liftR {R X} (m : M X) :
  forall s, execR (Defs.liftR (R:=R) m) s =
    match exec m s with
    | Some (x, s') => Some (inr x, s')
    | None => None
    end.
Proof.
  unfold Defs.liftR. induction m as [x0 | T oc k IH]; intros s.
  - reflexivity.
  - destruct oc; cbn [Defs.try_catch execR exec Defs.throw];
      try (apply IH); try reflexivity;
      match goal with
      | |- context[read_bytes ?mm ?pa ?n] =>
          destruct (read_bytes mm pa n) as [w|]; [apply IH | reflexivity]
      end.
Qed.

(* ---------------------------------------------------------------------- *)
(* the bridge: catch_early_return back into the base monad.                 *)
(* ---------------------------------------------------------------------- *)

Lemma exec_catch_early_return {X} (body : Defs.monadR X exception X) :
  forall s, exec (Defs.catch_early_return body) s =
    match execR body s with
    | Some (inl r, s') => Some (r, s')
    | Some (inr r, s') => Some (r, s')
    | None => None
    end.
Proof.
  unfold Defs.catch_early_return. induction body as [a0 | T oc k IH]; intros s.
  - reflexivity.
  - destruct oc; cbn [Defs.try_catch exec execR Defs.throw Defs.returnm];
      try (apply IH); try reflexivity;
      first
        [ match goal with
          | |- context[read_bytes ?mm ?pa ?n] =>
              destruct (read_bytes mm pa n) as [w|]; [apply IH | reflexivity]
          end
        | match goal with
          | He : (_ + exception)%type |- _ => destruct He; reflexivity
          end ].
Qed.

(* ---------------------------------------------------------------------- *)
(* determinism transfer: execR success => the unique runR.                 *)
(* ---------------------------------------------------------------------- *)

Lemma execR_runR_det {R X} (m : Defs.monadR R exception X) :
  forall s res s', execR m s = Some (res, s') ->
    runR m s res s' /\ (forall res2 s2, runR m s res2 s2 -> res2 = res /\ s2 = s').
Proof.
  induction m as [y|T oc k IH]; intros s res s' Hexec.
  - simpl in Hexec. injection Hexec as <- <-. simpl.
    split; [done | intros res2 s2 [<- <-]; done].
  - destruct oc; simpl in Hexec; try discriminate;
      try (split;
           [ apply (proj1 (IH _ _ _ _ Hexec))
           | intros res2 s2 Hr; simpl in Hr; exact (proj2 (IH _ _ _ _ Hexec) _ _ Hr) ]).
    + (* MemRead *)
      destruct (read_bytes s.(mem) _ _) as [w0|] eqn:Hrb; [|discriminate].
      destruct (IH (inl (w0, None)) s res s' Hexec) as [Hrun0 Huniq0].
      split.
      * simpl. exists w0. split;
          [ intros j Hj; apply (read_bytes_spec _ _ _ _ Hrb j Hj) | exact Hrun0 ].
      * intros res2 s2 Hr. simpl in Hr. destruct Hr as (w & Hbytes & Hrun).
        assert (Hweq : w = w0).
        { apply bv_eq_of_bytes. intros j Hj.
          pose proof (read_bytes_spec _ _ _ _ Hrb j Hj) as H0.
          assert (Hw : mem s !! RiscvModelBytes.pa_add (Interface.ReadReq.pa t) j
                       = Some (RiscvModelBytes.nth_byte w j))
            by (apply Hbytes; exact Hj).
          rewrite Hw in H0. apply Some_inj in H0. exact H0. }
        subst w. exact (Huniq0 _ _ Hrun).
    + (* ExtraOutcome *)
      match goal with He : (_ + exception)%type |- _ => destruct He as [r0|ee] end;
        simpl in Hexec; [|discriminate].
      injection Hexec as <- <-. simpl.
      split; [done | intros res2 s2 [<- <-]; done].
Qed.

(* mirror of run_to_exec: a proven runR-fact + execR-progress => the exec fact. *)
Lemma runR_to_execR {R X} (m : Defs.monadR R exception X) s res s' :
  runR m s res s' -> execR m s <> None -> execR m s = Some (res, s').
Proof.
  intros Hr Hne. destruct (execR m s) as [[res2 s2]|] eqn:He; [|exfalso; apply Hne; reflexivity].
  pose proof (execR_runR_det _ _ _ _ He) as [_ Huniq].
  destruct (Huniq _ _ Hr) as [-> ->]. reflexivity.
Qed.

(* ===== RiscvModelHne1 ===== *)
(* ====================================================================== *)
(* RiscvModelHne1.v                                                        *)
(*                                                                         *)
(* STAGE 1 of discharging Hne (= exec (run_hart_active 0) s <> None):       *)
(* trace execR through run_hart_active's F_Base/ADD body and reduce Hne to  *)
(* leaf exec-facts.  Cheap leaf twins (dispatchInterrupt, is_landing_pad)   *)
(* are proven; the structural reduction `exec_hart_active_progress` carries  *)
(* the remaining leaves (fetch [stage 2], ext_decode [decode wall],         *)
(* getPendingSet, execute) as hypotheses.                                   *)
(* ====================================================================== *)




(* targeted reduction for returnR (avoids cbn [execR] which over-unfolds). *)
Lemma execR_returnR {R X} (x : X) s :
  execR (Defs.returnR R x) s = Some (inr x, s).
Proof. reflexivity. Qed.

Lemma execR_bind0 {R X} (m : Defs.monadR R exception unit)
    (n : Defs.monadR R exception X) s :
  execR (Defs.bind0 m n) s =
    match execR m s with
    | Some (inl r, s') => Some (inl r, s')
    | Some (inr _, s') => execR n s'
    | None => None
    end.
Proof. unfold Defs.bind0. rewrite execR_bind. reflexivity. Qed.

(* ---------------------------------------------------------------------- *)
(* Cheap leaf twin 1: dispatchInterrupt = None (given getPendingSet=None).  *)
(* ---------------------------------------------------------------------- *)

Lemma exec_dispatchInterrupt_none s :
  exec (getPendingSet Machine) s = Some (None, s) ->
  exec (dispatchInterrupt Machine) s = Some (None, s).
Proof.
  intros Hgp. unfold dispatchInterrupt.
  rewrite (exec_bind_Some _ _ _ _ _ Hgp). cbn match.
  apply exec_returnm.
Qed.

(* ---------------------------------------------------------------------- *)
(* Cheap leaf twin 2: is_landing_pad_expected reduces to the elp eq_vec.    *)
(* ---------------------------------------------------------------------- *)

Lemma exec_is_landing_pad s :
  exec (is_landing_pad_expected tt) s
  = Some (eq_vec (register_lookup elp s.(sregs))
                 (landing_pad_bits_backwards LP_EXPECTED), s).
Proof.
  unfold is_landing_pad_expected.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg elp s)).
  apply exec_returnm.
Qed.


(* ---------------------------------------------------------------------- *)
(* Structural reduction: exec (run_hart_active 0) s = Some (.., s_final),    *)
(* hence <> None, from the leaf exec-facts (F_Base/ADD path).               *)
(* ---------------------------------------------------------------------- *)

Section HartActiveProgress.
  Context (s s_f s_x s_final : mstate) (w : mword 32) (instr : instruction)
          (pc : mword 64) (resf : ExecutionResult).

  Hypothesis Hpriv : register_lookup cur_privilege s.(sregs) = Machine.
  Hypothesis Hdisp : exec (dispatchInterrupt Machine) s = Some (None, s).
  Hypothesis Hfetch : exec (fetch tt) s = Some (F_Base w, s_f).
  Hypothesis Hdec : exec (ext_decode w) s_f = Some (instr, s_f).
  Hypothesis Hlpad : eq_vec (register_lookup elp s_f.(sregs))
                            (landing_pad_bits_backwards LP_EXPECTED) = false.
  Hypothesis Hnotlpad : is_lpad_instruction instr = false.
  Hypothesis HpcF : register_lookup PC s_f.(sregs) = pc.
  Let s_pc : mstate := set_reg s_f nextPC (add_vec_int pc 4).
  Hypothesis Hexec : exec (execute instr) s_pc = Some (resf, s_x).
  Hypothesis Hnotexec : match resf with ExecuteAs _ => False | _ => True end.

  Lemma exec_hart_active_progress :
    exec (run_hart_active 0) s
    = Some (Step_Execute (resf, zero_extend' 32 w), s_x).
  Proof using All.
    unfold run_hart_active.
    rewrite exec_catch_early_return.
    (* read cur_privilege -> Machine *)
    rewrite execR_bind execR_liftR exec_read_reg Hpriv. cbn match.
    (* dispatchInterrupt -> None ; the `fun w1 =>` body is
       (match w1) >> liftR(fetch) >>= fun w2 => ..  =  bind (bind0 MATCH (liftR fetch)) k *)
    rewrite execR_bind execR_liftR Hdisp. cbn match.
    (* outer bind; inner bind0 (returnR tt) (liftR fetch) *)
    rewrite execR_bind. rewrite execR_bind0 execR_returnR. cbn match.
    rewrite execR_liftR Hfetch. cbn match. cbn match.
    (* ext_fetch_hook (F_Base w) = F_Base w ; F_Base branch (announce/callback lets) *)
    unfold ext_fetch_hook. cbn match. cbn beta iota.
    (* ext_decode w -> instr *)
    rewrite execR_bind execR_liftR Hdec. cbn match.
    (* (if print=false then.. else returnR tt) >> and_boolM(..) >>= fun w21 => ..
       = bind (bind0 (returnR tt) and_boolM) k *)
    unfold get_config_print_instr. cbn match.
    rewrite execR_bind. rewrite execR_bind0 execR_returnR. cbn match.
    (* and_boolM (liftR is_landing_pad) (returnR (not lpad)) -> false (short-circuit) *)
    unfold and_boolM.
    rewrite execR_bind execR_liftR exec_is_landing_pad Hlpad. cbn match. cbn match.
    rewrite execR_returnR. cbn match. cbn match.
    (* w21 = false -> else: read PC >>= fun w22 => bind0 (write nextPC) (liftR execute) >>= ... *)
    rewrite execR_bind execR_liftR (exec_read_reg PC) HpcF. cbn match.
    rewrite execR_bind. rewrite execR_bind0 execR_liftR (exec_write_reg nextPC). cbn match.
    fold s_pc. rewrite execR_liftR Hexec. cbn match. cbn match.
    (* (match resf : not ExecuteAs => resf) >>= fun result' => returnR (Step_Execute ..) *)
    rewrite execR_bind.
    destruct resf; cbn in Hnotexec; try contradiction;
      cbn match; rewrite execR_returnR; cbn match; rewrite execR_returnR; reflexivity.
  Qed.

End HartActiveProgress.

(* ===== RiscvModelFetch ===== *)
(* ===================================================================== *)
(* RiscvModelFetch.v — item (2/3) cont'd: the extension predicates        *)
(* (`hartSupports`/`currentlyEnabled`) reduced through `run`, INCLUDING    *)
(* the full nested capability tree (not just leaves).  All AXIOM-FREE.     *)
(*                                                                         *)
(* Findings from reading `fetch` (rv64d.v):                                *)
(*  - On a 4-byte-aligned PC (the ADD path) the only `currentlyEnabled`    *)
(*    that fires is `Ext_Ziccif` (a leaf = true).  `Ext_Zca` sits under    *)
(*    `and_boolM (PC[1] != 0) …`, short-circuited away when PC aligned.    *)
(*  - `fetch` then calls `fetch_bytes` = address translation (Bare/M-mode  *)
(*    ⇒ identity) + PMP + MemRead — a separate sub-effort (see README).    *)
(*                                                                         *)
(* `run_hartSupports_C` shows the WHOLE capability tree (nested and/or-     *)
(* boolM over 5 sub-extensions) reduces — not just the leaves — confirming  *)
(* the Acc recipe scales past depth 1.                                     *)
(* ===================================================================== *)

(* Unfold one `_rec_hartSupports` level: destruct its Acc proof, step the
   {struct _acc} fixpoint, discharge the (concrete, >=0) reclimit guard, and
   peel the leading `assert_exp' … >>=`.  Leaves goal = `run <arm> s _ s`. *)
Ltac hs_open s :=
  match goal with
  | |- run (_rec_hartSupports ?e ?r ?a) _ _ _ =>
      destruct a; cbn [_rec_hartSupports]; unfold Defs.assert_exp';
      match goal with |- context[Z.geb ?x 0] => replace (Z.geb x 0) with true by reflexivity end;
      cbn match;
      apply run_bind; exists eq_refl, s; split;
      [apply run_ret; split; reflexivity | cbn match]
  end.

(* --- leaves the aligned ADD fetch path actually queries --- *)
Lemma run_hartSupports_Ziccif s : run (hartSupports Ext_Ziccif) s true s.
Proof.
  unfold hartSupports. destruct (Defs.Zwf_guarded _).
  cbn [_rec_hartSupports]. unfold Defs.assert_exp'.
  replace (Z.geb (hartSupports_measure Ext_Ziccif) 0) with true by reflexivity.
  cbn match.
  apply run_bind. exists eq_refl, s. split.
  - apply run_ret. split; reflexivity.
  - apply run_returnM. split; reflexivity.
Qed.

Lemma run_currentlyEnabled_Ziccif s : run (currentlyEnabled Ext_Ziccif) s true s.
Proof.
  unfold currentlyEnabled. destruct (Defs.Zwf_guarded _).
  cbn [_rec_currentlyEnabled]. unfold Defs.assert_exp'.
  replace (Z.geb (currentlyEnabled_measure Ext_Ziccif) 0) with true by reflexivity.
  cbn match.
  apply run_bind. exists eq_refl, s. split.
  - apply run_ret. split; reflexivity.
  - cbn match. apply run_hartSupports_Ziccif.
Qed.

(* --- the full Ext_C capability tree reduces to `true` (CSR-free, xlen=64) --- *)
Lemma run_hartSupports_C s : run (hartSupports Ext_C) s true s.
Proof.
  unfold hartSupports. destruct (Defs.Zwf_guarded _).
  cbn [_rec_hartSupports]. unfold Defs.assert_exp'.
  replace (Z.geb (hartSupports_measure Ext_C) 0) with true by reflexivity.
  cbn match.
  apply run_bind. exists eq_refl, s. split; [apply run_ret; split; reflexivity| cbn match].
  apply run_and_boolM. exists true, s. split.
  { hs_open s. apply run_returnM. split; reflexivity. }
  apply run_and_boolM. exists true, s. split.
  { apply run_or_boolM. exists false, s. split.
    { hs_open s. apply run_returnM. split; reflexivity. }
    apply run_or_boolM. exists false, s. split.
    { apply run_bind. exists true, s. split.
      { hs_open s. apply run_returnM. split; reflexivity. }
      apply run_returnM. split; reflexivity. }
    { apply run_returnM. split; [vm_compute; reflexivity| reflexivity]. } }
  { apply run_or_boolM. exists true, s. split.
    { hs_open s. apply run_returnM. split; reflexivity. }
    split; reflexivity. }
Qed.

(* ===== RiscvModelEnabledS ===== *)
(* ====================================================================== *)
(* RiscvModelEnabledS.v                                                    *)
(*                                                                         *)
(* Gate 1 toward discharging Hstep: currentlyEnabled Ext_S is              *)
(* state-preserving (HcES for the getPendingSet keystone).                 *)
(*   currentlyEnabled Ext_S                                                *)
(*     = and_boolM (hartSupports Ext_S)              [= returnM true]       *)
(*         (and_boolM (read misa; misa.S check)                            *)
(*                    (currentlyEnabled Ext_Zicsr))  [= hartSupports = true]*)
(* All read-only; value = misa.S bit; final state = s.                     *)
(* ====================================================================== *)




(* leaves: hartSupports Ext_S / Ext_Zicsr both reduce to returnM true *)
Lemma run_hartSupports_S s : run (hartSupports Ext_S) s true s.
Proof. unfold hartSupports. hs_open s. apply run_returnM. split; reflexivity. Qed.

Lemma run_hartSupports_Zicsr s : run (hartSupports Ext_Zicsr) s true s.
Proof. unfold hartSupports. hs_open s. apply run_returnM. split; reflexivity. Qed.

(* the inner Ext_Zicsr sub-call (a reduced-limit _rec node) reduces to
   hartSupports Ext_Zicsr = true, for any acc. *)
Lemma run_rec_cE_Zicsr s (acc : Acc (Zwf 0) 0) :
  run (_rec_currentlyEnabled Ext_Zicsr 0 acc) s true s.
Proof.
  destruct acc. cbn [_rec_currentlyEnabled]. unfold Defs.assert_exp'.
  replace (Z.geb 0 0) with true by reflexivity. cbn match.
  apply run_bind. exists eq_refl, s. split; [apply run_ret; split; reflexivity | cbn match].
  apply run_hartSupports_Zicsr.
Qed.

(* HcES: currentlyEnabled Ext_S is state-preserving, value = misa.S bit. *)
Lemma run_currentlyEnabled_S s :
  run (currentlyEnabled Ext_S) s
      (eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1")) s.
Proof.
  unfold currentlyEnabled. destruct (Defs.Zwf_guarded _).
  cbn [_rec_currentlyEnabled]. unfold Defs.assert_exp'.
  replace (Z.geb (currentlyEnabled_measure Ext_S) 0) with true by reflexivity.
  cbn match.
  apply run_bind. exists eq_refl, s. split; [apply run_ret; split; reflexivity | cbn match].
  (* outer and_boolM (hartSupports Ext_S = true) INNER *)
  apply run_and_boolM. exists true, s. split; [apply run_hartSupports_S|].
  (* bl = true -> run INNER s (misa.S bit) s *)
  apply run_and_boolM.
  exists (eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1")), s. split.
  { (* misa check: read_reg misa >>= fun w => returnM (eq_vec (_get_Misa_S w) 0b1) *)
    apply run_bind. exists (register_lookup misa s.(sregs)), s. split.
    { exact (run_read_reg_fwd misa s). }
    apply run_returnM. split; reflexivity. }
  (* if (misa.S bit) then run (cE Ext_Zicsr) s _ s else (_ = false /\ s' = s) *)
  destruct (eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1")) eqn:Hb2.
  - apply run_rec_cE_Zicsr.
  - split; reflexivity.
Qed.

(* ===== RiscvModelHne2 ===== *)
(* ===================================================================== *)
(* RiscvModelHne2.v — leaf exec-twins discharging Hne's residual leaf      *)
(* facts: exec_execute_ADD and exec_getPendingSet_machine_none.            *)
(* Functional mirrors of the proven run-facts (exec_bind instead of        *)
(* run_bind).                                                              *)
(* ===================================================================== *)
Import Defs.

(* --------------------------------------------------------------------- *)
(* Task A: exec twins of rX / wX at concrete registers, then execute(ADD). *)
(* --------------------------------------------------------------------- *)

Lemma exec_rX_x10 s :
  exec (rX (Regno 10)) s = Some (register_lookup (R_bitvector_64 x10) s.(sregs), s).
Proof. rewrite rX_x10. exact (exec_read_reg (R_bitvector_64 x10) s). Qed.

Lemma exec_rX_x11 s :
  exec (rX (Regno 11)) s = Some (register_lookup (R_bitvector_64 x11) s.(sregs), s).
Proof. rewrite rX_x11. exact (exec_read_reg (R_bitvector_64 x11) s). Qed.

Lemma exec_wX_x12 s (v : mword 64) :
  exec (wX (Regno 12) v) s = Some (tt, set_reg s (R_bitvector_64 x12) (regval_into_reg v)).
Proof.
  rewrite wX_x12_eq.
  rewrite (exec_bind0_Some _ _ _ _ _
            (exec_write_reg (R_bitvector_64 x12) (regval_into_reg v) s)).
  apply exec_returnm.
Qed.

Lemma exec_rX_bits_x10 (i : mword 5) s :
  uint i = 10 ->
  exec (rX_bits (Regidx i)) s = Some (register_lookup (R_bitvector_64 x10) s.(sregs), s).
Proof. intro H. unfold rX_bits; cbn match. rewrite H. apply exec_rX_x10. Qed.

Lemma exec_rX_bits_x11 (i : mword 5) s :
  uint i = 11 ->
  exec (rX_bits (Regidx i)) s = Some (register_lookup (R_bitvector_64 x11) s.(sregs), s).
Proof. intro H. unfold rX_bits; cbn match. rewrite H. apply exec_rX_x11. Qed.

Lemma exec_wX_bits_x12 (i : mword 5) s (v : mword 64) :
  uint i = 12 ->
  exec (wX_bits (Regidx i) v) s = Some (tt, set_reg s (R_bitvector_64 x12) (regval_into_reg v)).
Proof. intro H. unfold wX_bits; cbn match. rewrite H. apply exec_wX_x12. Qed.

(* compositional exec twin of run_execute_RTYPE_ADD *)
Lemma exec_execute_RTYPE_ADD (rs2 rs1 rd : regidx) (a b : mword 64) s s' :
  exec (rX_bits rs1) s = Some (a, s) ->
  exec (rX_bits rs2) s = Some (b, s) ->
  exec (wX_bits rd (add_vec a b)) s = Some (tt, s') ->
  exec (execute_RTYPE rs2 rs1 rd ADD) s = Some (RETIRE_SUCCESS, s').
Proof.
  intros Ha Hb Hw.
  unfold execute_RTYPE. cbn match.
  (* outer bind: inner computes (add_vec a b) leaving state s *)
  rewrite (exec_bind_Some _ _ _ (add_vec a b) s).
  2:{ (* inner = rX_bits rs1 >>= rX_bits rs2 >>= returnM (add_vec) *)
      rewrite (exec_bind_Some _ _ _ _ _ Ha).
      rewrite (exec_bind_Some _ _ _ _ _ Hb).
      apply exec_returnm. }
  (* now: bind0 (wX_bits rd (add_vec a b)) (returnM RETIRE_SUCCESS) *)
  rewrite (exec_bind0_Some _ _ _ _ _ Hw).
  apply exec_returnm.
Qed.

Lemma exec_execute_ADD (rd rs1 rs2 : mword 5) s :
  uint rs1 = 10 -> uint rs2 = 11 -> uint rd = 12 ->
  exec (execute_RTYPE (Regidx rs2) (Regidx rs1) (Regidx rd) ADD) s
    = Some (RETIRE_SUCCESS,
            set_reg s (R_bitvector_64 x12)
              (regval_into_reg
                 (add_vec (register_lookup (R_bitvector_64 x10) s.(sregs))
                          (register_lookup (R_bitvector_64 x11) s.(sregs))))).
Proof.
  intros H1 H2 H3.
  eapply exec_execute_RTYPE_ADD.
  - apply exec_rX_bits_x10; exact H1.
  - apply exec_rX_bits_x11; exact H2.
  - apply exec_wX_bits_x12; exact H3.
Qed.

(* --------------------------------------------------------------------- *)
(* Task B: exec twin of the getPendingSet keystone.                        *)
(* Mirrors run_getPendingSet_machine_none; carries the currentlyEnabled    *)
(* Ext_S exec-twin (HecES), parallel to the run keystone's HcES.           *)
(* --------------------------------------------------------------------- *)

(* model's returnM = Defs.returnm (E:=exception); needs its own exec lemma so
   syntactic rewrites match the [returnM ...] that appears in the model terms. *)
Lemma exec_returnM {X} (x : X) s : exec (returnM x) s = Some (x, s).
Proof. unfold returnM. apply exec_returnm. Qed.

Lemma exec_and_boolM_Some (l r : M bool) s bl sl :
  exec l s = Some (bl, sl) ->
  exec (and_boolM l r) s = (if bl then exec r sl else Some (false, sl)).
Proof.
  intro H. unfold and_boolM. rewrite (exec_bind_Some _ _ _ _ _ H).
  destruct bl; [reflexivity | apply exec_returnm].
Qed.

Lemma exec_or_boolM_Some (l r : M bool) s bl sl :
  exec l s = Some (bl, sl) ->
  exec (or_boolM l r) s = (if bl then Some (true, sl) else exec r sl).
Proof.
  intro H. unfold or_boolM. rewrite (exec_bind_Some _ _ _ _ _ H).
  destruct bl; [apply exec_returnm | reflexivity].
Qed.

Section ExecPending.
  Context (s : mstate) (cES : bool).
  Hypothesis HecES : exec (currentlyEnabled Ext_S) s = Some (cES, s).
  Hypothesis Hmideleg : register_lookup mideleg s.(sregs) = zeros' 64.
  Hypothesis HmIE :
    eq_vec (_get_Mstatus_MIE (register_lookup mstatus s.(sregs))) ('b"1") = false.

  Lemma exec_guard_true :
    exec (or_boolM (currentlyEnabled Ext_S)
                   (Defs.bind (read_reg mideleg)
                      (fun w1 : mword 64 => returnM (eq_vec w1 (zeros' 64))))) s
      = Some (true, s).
  Proof using All.
    rewrite (exec_or_boolM_Some _ _ _ _ _ HecES). destruct cES; [reflexivity|].
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mideleg s)).
    rewrite Hmideleg.
    replace (eq_vec (zeros' 64) (zeros' 64)) with true
      by (symmetry; apply eq_vec_true_iff; reflexivity).
    apply exec_returnm.
  Qed.

  Lemma exec_ext_int_some :
    exists ev, exec (external_interrupts_pending tt) s = Some (ev, s).
  Proof using All.
    unfold external_interrupts_pending.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg sig_meip s)).
    rewrite (exec_bind_Some _ _ _ _ _ HecES).
    destruct cES; cbn match.
    - rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg sig_seip s)). eexists. apply exec_returnm.
    - rewrite (exec_bind_Some _ _ _ _ _ (exec_returnm ('b"0") s)). eexists. apply exec_returnm.
  Qed.

  Lemma exec_read_mip_some :
    exists v, exec (read_mip IncludePlatformInterrupts) s = Some (v, s).
  Proof using All.
    destruct exec_ext_int_some as [ev Hext].
    unfold read_mip. cbn match. eexists.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mip s)).
    rewrite (exec_bind_Some _ _ _ _ _ Hext).
    apply exec_returnm.
  Qed.

  Lemma exec_mIE_false :
    exec (or_boolM
            (and_boolM (returnM (generic_eq Machine Machine))
               (Defs.bind (read_reg mstatus)
                  (fun w7 : mword 64 => returnM (eq_vec (_get_Mstatus_MIE w7) ('b"1")))))
            (returnM (orb (generic_eq Machine Supervisor) (generic_eq Machine User)))) s
      = Some (false, s).
  Proof using All.
    assert (Hand : exec (and_boolM (returnM (generic_eq Machine Machine))
                     (Defs.bind (read_reg mstatus)
                        (fun w7 : mword 64 => returnM (eq_vec (_get_Mstatus_MIE w7) ('b"1"))))) s
                   = Some (false, s)).
    { rewrite (exec_and_boolM_Some _ _ _ _ _ (exec_returnM (generic_eq Machine Machine) s)).
      change (generic_eq Machine Machine) with true. cbn match.
      rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mstatus s)).
      rewrite HmIE. apply exec_returnm. }
    rewrite (exec_or_boolM_Some _ _ _ _ _ Hand).
    change (orb (generic_eq Machine Supervisor) (generic_eq Machine User)) with false.
    apply exec_returnm.
  Qed.

  Lemma exec_sIE_false :
    exec (or_boolM
            (and_boolM (returnM (generic_eq Machine Supervisor))
               (Defs.bind (read_reg mstatus)
                  (fun w : mword 64 => returnM (eq_vec (_get_Mstatus_SIE w) ('b"1")))))
            (returnM (generic_eq Machine User))) s
      = Some (false, s).
  Proof using All.
    assert (Hand : exec (and_boolM (returnM (generic_eq Machine Supervisor))
                     (Defs.bind (read_reg mstatus)
                        (fun w : mword 64 => returnM (eq_vec (_get_Mstatus_SIE w) ('b"1"))))) s
                   = Some (false, s)).
    { rewrite (exec_and_boolM_Some _ _ _ _ _ (exec_returnM (generic_eq Machine Supervisor) s)).
      change (generic_eq Machine Supervisor) with false. cbn match. reflexivity. }
    rewrite (exec_or_boolM_Some _ _ _ _ _ Hand).
    change (generic_eq Machine User) with false. apply exec_returnm.
  Qed.

  Lemma exec_getPendingSet_machine_none :
    exec (getPendingSet Machine) s = Some (None, s).
  Proof using All.
    destruct exec_read_mip_some as [mipv Hmip].
    assert (Hae : exec (assert_exp' true "sys/sys_control.sail:107.58-107.59") s
                  = Some (eq_refl, s)).
    { unfold assert_exp'. cbn match. apply exec_returnm. }
    unfold getPendingSet.
    rewrite (exec_bind_Some _ _ _ _ _ exec_guard_true).
    rewrite (exec_bind_Some _ _ _ _ _ Hae).
    rewrite (exec_bind_Some _ _ _ _ _ Hmip).
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mie s)).
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mideleg s)).
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mie s)).
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mideleg s)).
    rewrite (exec_bind_Some _ _ _ _ _ exec_mIE_false).
    rewrite (exec_bind_Some _ _ _ _ _ exec_sIE_false).
    cbn [andb]. apply exec_returnm.
  Qed.

End ExecPending.

(* ===== RiscvModelHneFetch ===== *)
(* ====================================================================== *)
(* RiscvModelHneFetch.v                                                    *)
(*                                                                         *)
(* Hne STAGE 2: the fetch exec-twin.                                       *)
(*   - execR_foreach_ZM_up_const: the exec/execR loop-invariant for the    *)
(*     PMP foreach (twin of runR_foreach_ZM_up_const).                     *)
(*   - exec_fetch_F_Base via run_to_exec on the proven run_fetch_F_Base    *)
(*     + exec-progress (exec (fetch tt) s <> None).                        *)
(* ====================================================================== *)



Local Open Scope Z_scope.

(* returnm vars (= Ret vars = returnR) yields Some (inr vars, s) under execR. *)
Lemma execR_returnm_fwd {R X} (x : X) s :
  execR (Defs.returnm x : Defs.monadR R exception X) s = Some (inr x, s).
Proof. reflexivity. Qed.

(* ---------------------------------------------------------------------- *)
(* The exec/execR loop-invariant over the nat-fueled [foreach_ZM_up'].     *)
(* Twin of runR_foreach_ZM_up'_const: a body that is Some(inr v,s) at every *)
(* index makes the whole loop Some(inr vars, s).                           *)
(* ---------------------------------------------------------------------- *)

Lemma execR_foreach_ZM_up'_const {R Vars} (to step : Z)
    (body : forall (z : Z), Vars -> Defs.monadR R exception Vars) (s : mstate) :
  (forall i v, execR (body i v) s = Some (inr v, s)) ->
  forall (n : nat) (from : Z) (vars : Vars),
    execR (Defs.foreach_ZM_up' (E := (R + exception)%type) from to step n vars body)
          s = Some (inr vars, s).
Proof.
  intros Hbody. induction n as [|n IH]; intros from vars.
  - cbn [Defs.foreach_ZM_up']. destruct (from <=? to); apply execR_returnm_fwd.
  - destruct (Z.leb_spec from to) as [Hle|Hgt].
    + rewrite (Defs.unroll_foreach_ZM_up' _ _ from to step n vars body Hle).
      rewrite execR_bind. rewrite (Hbody from vars). exact (IH (from + step) vars).
    + cbn [Defs.foreach_ZM_up'].
      replace (from <=? to) with false.
      * apply execR_returnm_fwd.
      * symmetry. apply Z.leb_gt. lia.
Qed.

Lemma execR_foreach_ZM_up_const {R Vars} (from to step : Z)
    (body : forall (z : Z), Vars -> Defs.monadR R exception Vars)
    (s : mstate) (vars : Vars) :
  (forall i v, execR (body i v) s = Some (inr v, s)) ->
  execR (Defs.foreach_ZM_up (E := (R + exception)%type) from to step vars body)
        s = Some (inr vars, s).
Proof.
  intros Hbody. unfold Defs.foreach_ZM_up.
  apply execR_foreach_ZM_up'_const; exact Hbody.
Qed.

(* ---------------------------------------------------------------------- *)
(* The fetch exec-twin, reduced to exec-progress via run_to_exec on the    *)
(* proven run_fetch_F_Base.  The remaining residue (exec (fetch tt) s <>   *)
(* None) is the memory-subsystem exec mirror, now equipped with            *)
(* execR_foreach_ZM_up_const above for the PMP loop.                       *)
(* ---------------------------------------------------------------------- *)

Lemma exec_fetch_F_Base (w : mword 32) (s : mstate) :
  run (fetch tt) s (F_Base w) s ->
  exec (fetch tt) s <> None ->
  exec (fetch tt) s = Some (F_Base w, s).
Proof. intros Hrun Hprog. exact (run_to_exec (fetch tt) s (F_Base w) s Hrun Hprog). Qed.

(* ===== RiscvModelPmp ===== *)
(* ====================================================================== *)
(* RiscvModelPmp.v                                                         *)
(*                                                                         *)
(* Fetch read-side toward discharging Hcycle's fetch dependency.           *)
(*                                                                         *)
(*  - run[R] loop-INVARIANT over [Defs.foreach_ZM_up'] / [foreach_ZM_up]:  *)
(*    a per-iteration state-preserving no-op body ⇒ the whole bounded loop  *)
(*    is a no-op (NO unrolling — induction on the nat fuel).  This is the   *)
(*    reusable analogue of the Lean loop_run_const / forIn_run_const.      *)
(*  - applied to [pmpCheck]: PMP-disabled (all pmpcfg=0) in Machine mode    *)
(*    ⇒ [run (pmpCheck ..) s None s], MODULO the per-iteration body no-op.  *)
(* ====================================================================== *)



(* returnm = Ret, so runR yields a plain (inr) return with no state change. *)
Lemma runR_returnm_fwd {R X} (x : X) (s : mstate) :
  runR (R:=R) (Defs.returnm x : Defs.monadR R exception X) s (inr x) s.
Proof. split; reflexivity. Qed.

(* ---------------------------------------------------------------------- *)
(* The loop invariant over the nat-fueled fixpoint [foreach_ZM_up'].       *)
(* Generalised over [from] and [vars] so the IH covers the [from+step]     *)
(* recursive call.                                                         *)
(* ---------------------------------------------------------------------- *)

Lemma runR_foreach_ZM_up'_const {R Vars} (to step : Z)
    (body : forall (z : Z), Vars -> Defs.monadR R exception Vars) (s : mstate) :
  (forall i v, runR (body i v) s (inr v) s) ->
  forall (n : nat) (from : Z) (vars : Vars),
    runR (Defs.foreach_ZM_up' (E := (R + exception)%type) from to step n vars body)
         s (inr vars) s.
Proof.
  intros Hbody. induction n as [|n IH]; intros from vars.
  - (* fuel exhausted: returnm vars in both branches *)
    cbn [Defs.foreach_ZM_up']. destruct (from <=? to); apply runR_returnm_fwd.
  - destruct (Z.leb_spec from to) as [Hle|Hgt].
    + (* one iteration, then recurse with from+step *)
      rewrite (Defs.unroll_foreach_ZM_up' _ _ _ _ _ _ _ _ Hle).
      apply (proj2 (runR_bind _ _ _ _ _)).
      right. exists vars, s. split.
      * exact (Hbody from vars).
      * exact (IH (from + step) vars).
    + (* from > to: immediate returnm vars *)
      cbn [Defs.foreach_ZM_up'].
      replace (from <=? to) with false by (symmetry; apply Z.leb_gt; lia).
      apply runR_returnm_fwd.
Qed.

(* The user-facing wrapper [foreach_ZM_up from to step vars body]. *)
Lemma runR_foreach_ZM_up_const {R Vars} (from to step : Z)
    (body : forall (z : Z), Vars -> Defs.monadR R exception Vars)
    (s : mstate) (vars : Vars) :
  (forall i v, runR (body i v) s (inr v) s) ->
  runR (Defs.foreach_ZM_up (E := (R + exception)%type) from to step vars body)
       s (inr vars) s.
Proof.
  intros Hbody. unfold Defs.foreach_ZM_up.
  apply runR_foreach_ZM_up'_const; exact Hbody.
Qed.

(* ===== RiscvModelFetchClose ===== *)
(* ====================================================================== *)
(* RiscvModelFetchClose.v                                                  *)
(*                                                                         *)
(* Fetch read-side, continued: reduce pmpCheck to "None" (access allowed)  *)
(* in Machine mode when every PMP entry's address-match-type is OFF        *)
(* (which holds when all pmpcfg = 0).  Uses the loop-invariant             *)
(* runR_foreach_ZM_up_const from RiscvModelPmp.                            *)
(*                                                                         *)
(* CONVERSION-LAZY: never cbn [run]/[runR]; only cbn zeta/beta/match +     *)
(* the forward stepping lemmas.                                            *)
(* ====================================================================== *)



(* pmpReadAddrReg only READS pmpcfg_n/pmpaddr_n and returns a pure value:   *)
(* state-preserving.  We just need existence of the returned value.         *)
Lemma run_pmpReadAddrReg_ex (n : Z) s : exists v, run (pmpReadAddrReg n) s v s.
Proof.
  unfold pmpReadAddrReg. cbn zeta. eexists.
  apply (proj2 (run_bind _ _ _ _ _)).
  exists (register_lookup pmpcfg_n s.(sregs)), s.
  split; [ exact (run_read_reg_fwd pmpcfg_n s) | ]. cbn beta.
  apply (proj2 (run_bind _ _ _ _ _)).
  exists (register_lookup pmpaddr_n s.(sregs)), s.
  split; [ exact (run_read_reg_fwd pmpaddr_n s) | ]. cbn beta.
  apply run_returnM_fwd.
Qed.

(* pmpMatchAddr with an OFF address-match-type yields PMP_NoMatch, purely. *)
Lemma run_pmpMatchAddr_OFF (pa : physaddr) (width : mword 64) (ent : mword 8)
    (pmpaddr prev : mword 64) s :
  pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A ent) = OFF ->
  run (pmpMatchAddr pa width ent pmpaddr prev) s PMP_NoMatch s.
Proof.
  intro HOFF. destruct pa as [addr0]. unfold pmpMatchAddr. cbn zeta.
  rewrite HOFF. cbn match. apply run_returnM_fwd.
Qed.

(* The body of pmpCheck's loop is a no-op when the i-th pmpcfg A-field=OFF. *)
Lemma run_pmpCheck_machine_none
    (addr : physaddr) (width : Z) (access : MemoryAccessType mem_payload) s :
  (forall i, pmpAddrMatchType_encdec_backwards
               (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) i))
             = OFF) ->
  run (pmpCheck addr width access Machine) s None s.
Proof.
  intro HpmpOFF.
  unfold pmpCheck.
  apply run_catch_early_return. right.
  replace (Z.eqb sys_pmp_count 0) with false by (vm_compute; reflexivity).
  cbn zeta. unfold Defs.bind0.
  apply (proj2 (runR_bind _ _ _ _ _)). right. exists tt, s. split.
  - (* the loop is a no-op *)
    apply runR_foreach_ZM_up_const. intros i v. destruct v. cbn beta.
    (* first bind: (if i>0 then liftR (pmpReadAddrReg (i-1)) else returnR 0) >>= REST *)
    destruct (Z.gtb i 0) eqn:Hi.
    + destruct (run_pmpReadAddrReg_ex (i - 1) s) as [pv Hpv].
      eapply runR_liftR_seq; [ exact Hpv | ]. cbn beta.
      (* REST with prev := pv *)
      eapply runR_liftR_seq; [ exact (run_read_reg_fwd pmpcfg_n s) | ]. cbn beta.
      destruct (run_pmpReadAddrReg_ex i s) as [w2 Hw2].
      eapply runR_liftR_seq; [ exact Hw2 | ]. cbn beta.
      eapply runR_liftR_seq;
        [ apply run_pmpMatchAddr_OFF; exact (HpmpOFF i) | ]. cbn beta.
      cbn match. apply runR_returnR_fwd.
    + apply (proj2 (runR_bind _ _ _ _ _)). right. eexists. exists s.
      split; [ apply runR_returnR_fwd | ]. cbn beta.
      (* REST with prev := zeros' 64 *)
      eapply runR_liftR_seq; [ exact (run_read_reg_fwd pmpcfg_n s) | ]. cbn beta.
      destruct (run_pmpReadAddrReg_ex i s) as [w2 Hw2].
      eapply runR_liftR_seq; [ exact Hw2 | ]. cbn beta.
      eapply runR_liftR_seq;
        [ apply run_pmpMatchAddr_OFF; exact (HpmpOFF i) | ]. cbn beta.
      cbn match. apply runR_returnR_fwd.
  - (* Machine mode falls through to None *)
    replace (generic_eq Machine Machine) with true by (vm_compute; reflexivity).
    cbn match. apply runR_returnR_fwd.
Qed.

(* ===== RiscvModelHneFetch2 ===== *)
(* ====================================================================== *)
(* RiscvModelHneFetch2.v                                                    *)
(*                                                                         *)
(* Hne stage 2 (fetch exec-progress mirror).  The centerpiece: the exec    *)
(* twin of run_pmpCheck_machine_none, using the execR loop-invariant        *)
(* execR_foreach_ZM_up_const for the PMP foreach.  Plus the body leaves     *)
(* exec_pmpReadAddrReg_ex / exec_pmpMatchAddr_OFF.                          *)
(*                                                                         *)
(* RESIDUE (carried, documented): exec_translateAddr / exec_mem_read /      *)
(* exec_fetch_progress (the rest of the memory-subsystem exec mirror) — see *)
(* README; the pmpCheck loop (the one non-mechanical piece) is done here.   *)
(* ====================================================================== *)



Local Open Scope Z_scope.

(* ---------------------------------------------------------------------- *)
(* Forward helper: a [liftR m] prefix of a bind, when [exec m] is known.   *)
(* (exec/execR twin of runR_liftR_seq.)                                    *)
(* ---------------------------------------------------------------------- *)
Lemma execR_liftR_seq {R X Y} (m : M Y) (f : Y -> Defs.monadR R exception X)
    (s s' : mstate) (x : Y) :
  exec m s = Some (x, s') ->
  execR (Defs.bind (Defs.liftR m) f) s = execR (f x) s'.
Proof.
  intro Hm. rewrite execR_bind. rewrite execR_liftR. rewrite Hm. reflexivity.
Qed.

(* ---------------------------------------------------------------------- *)
(* Leaf twins of the PMP body (mirror run_pmpReadAddrReg_ex /              *)
(* run_pmpMatchAddr_OFF).                                                   *)
(* ---------------------------------------------------------------------- *)
Lemma exec_pmpReadAddrReg_ex (n : Z) s :
  exists v, exec (pmpReadAddrReg n) s = Some (v, s).
Proof.
  unfold pmpReadAddrReg. cbn zeta. eexists.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg pmpcfg_n s)). cbn beta.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg pmpaddr_n s)). cbn beta.
  apply exec_returnM.
Qed.

Lemma exec_pmpMatchAddr_OFF (pa : physaddr) (width : mword 64) (ent : mword 8)
    (pmpaddr prev : mword 64) s :
  pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A ent) = OFF ->
  exec (pmpMatchAddr pa width ent pmpaddr prev) s = Some (PMP_NoMatch, s).
Proof.
  intro HOFF. destruct pa as [addr0]. unfold pmpMatchAddr. cbn zeta.
  rewrite HOFF. cbn match. apply exec_returnM.
Qed.

(* ---------------------------------------------------------------------- *)
(* CENTERPIECE: exec twin of run_pmpCheck_machine_none (the PMP foreach     *)
(* loop), via execR_foreach_ZM_up_const.                                    *)
(* ---------------------------------------------------------------------- *)
Lemma exec_pmpCheck_machine_none
    (addr : physaddr) (width : Z) (access : MemoryAccessType mem_payload) s :
  (forall i, pmpAddrMatchType_encdec_backwards
               (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) i))
             = OFF) ->
  exec (pmpCheck addr width access Machine) s = Some (None, s).
Proof.
  intro HpmpOFF.
  unfold pmpCheck.
  rewrite exec_catch_early_return.
  replace (Z.eqb sys_pmp_count 0) with false by (vm_compute; reflexivity).
  cbn zeta.
  rewrite execR_bind0.
  match goal with
  | |- context[Defs.foreach_ZM_up ?F ?T ?S ?vars ?body] =>
      assert (Hloop : execR (Defs.foreach_ZM_up F T S vars body) s
                      = Some (inr vars, s))
  end.
  { apply execR_foreach_ZM_up_const. intros i v. destruct v. cbn beta.
    destruct (Z.gtb i 0) eqn:Hi; cbn match.
    - destruct (exec_pmpReadAddrReg_ex (i - 1) s) as [pv Hpv].
      rewrite (execR_liftR_seq _ _ _ _ _ Hpv). cbn beta.
      rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg pmpcfg_n s)). cbn beta.
      destruct (exec_pmpReadAddrReg_ex i s) as [w2 Hw2].
      rewrite (execR_liftR_seq _ _ _ _ _ Hw2). cbn beta.
      rewrite (execR_liftR_seq _ _ _ _ _
                 (exec_pmpMatchAddr_OFF _ _ _ _ _ s (HpmpOFF i))). cbn beta.
      cbn match. apply execR_returnR.
    - rewrite execR_bind. rewrite execR_returnR. cbn match. cbn beta.
      rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg pmpcfg_n s)). cbn beta.
      destruct (exec_pmpReadAddrReg_ex i s) as [w2 Hw2].
      rewrite (execR_liftR_seq _ _ _ _ _ Hw2). cbn beta.
      rewrite (execR_liftR_seq _ _ _ _ _
                 (exec_pmpMatchAddr_OFF _ _ _ _ _ s (HpmpOFF i))). cbn beta.
      cbn match. apply execR_returnR. }
  rewrite Hloop. cbn match. reflexivity.
Qed.

Print Assumptions exec_pmpCheck_machine_none.

(* ===== RiscvModelFetchAsm ===== *)
(* ====================================================================== *)
(* RiscvModelFetchAsm.v                                                    *)
(*                                                                         *)
(* Read-path gates toward `run_fetch_F_Base`:                              *)
(*   - within_mmio_readable = false  (RAM, not MMIO)                       *)
(*   - phys_access_check = None      (composes pmpCheck=None + pmaCheck=None)*)
(*   - checked_mem_read reduces to read_ram (the value the memory holds)   *)
(* built on the proven leaf lemmas (translateAddr-identity, pmpCheck=None, *)
(* read_ram_plain_4) and the run/runR machinery.                           *)
(* ====================================================================== *)



(* ---------------------------------------------------------------------- *)
(* 1. within_mmio_readable = false for a non-MMIO (RAM) address.           *)
(*    The CLINT/SIG/HTIF range tests are geometric facts about the address *)
(*    (false for kernel-code addresses >= 0x80000000); we take them as     *)
(*    hypotheses (their concrete reduction depends on the plat_* config).  *)
(* ---------------------------------------------------------------------- *)

Lemma run_within_mmio_readable_false (addr : physaddr) (width : Z) s :
  run (within_clint addr width) s false s ->
  run (within_sig addr width) s false s ->
  run (within_htif_readable addr width) s false s ->
  run (within_mmio_readable addr width) s false s.
Proof.
  intros Hc Hsig Hh.
  unfold within_mmio_readable.
  cbn [get_config_rvfi].
  apply (proj2 (run_or_boolM _ _ _ _ _)). exists false, s. split; [exact Hc|].
  cbn match.
  apply (proj2 (run_or_boolM _ _ _ _ _)). exists false, s. split; [exact Hsig|].
  cbn match.
  apply (proj2 (run_and_boolM _ _ _ _ _)). exists false, s. split; [exact Hh|].
  cbn match. split; reflexivity.
Qed.

(* ---------------------------------------------------------------------- *)
(* 2. phys_access_check = None when both PMP and PMA allow the access.     *)
(* ---------------------------------------------------------------------- *)

Lemma run_phys_access_check_none
    (access : MemoryAccessType mem_payload) (pbmt : page_based_mem_type)
    (priv : Privilege) (paddr : physaddr) (width : Z) (res : bool) s :
  run (pmpCheck paddr width access priv) s None s ->
  run (pmaCheck paddr width access pbmt res) s None s ->
  run (phys_access_check access pbmt priv paddr width res) s None s.
Proof.
  intros Hpmp Hpma.
  unfold phys_access_check.
  apply (proj2 (run_bind _ _ _ _ _)). exists None, s. split; [exact Hpmp|].
  apply (proj2 (run_bind _ _ _ _ _)). exists None, s. split; [exact Hpma|].
  cbn match. apply (proj2 (run_returnM _ _ _ _)). split; reflexivity.
Qed.

(* ---------------------------------------------------------------------- *)
(* 3. checked_mem_read reduces to read_ram for an allowed, non-MMIO,       *)
(*    plain (aq=rl=res=false) read.                                        *)
(* ---------------------------------------------------------------------- *)


(* ===== RiscvModelFetchF ===== *)
(* ====================================================================== *)
(* RiscvModelFetchF.v                                                      *)
(*                                                                         *)
(* Toward run_fetch_F_Base : run (fetch tt) s (F_Base word) s with a       *)
(* CONCRETE word.  Resolves the pmaCheck representation issue, pins the    *)
(* read value, threads the mem_read wrapper, and assembles fetch_bytes /   *)
(* fetch.                                                                   *)
(* ====================================================================== *)



(* ---------------------------------------------------------------------- *)
(* 1. Pinned read: the read value is exactly [w] (not just existential).   *)
(*    Same proof as run_read_ram_plain_4, but the strengthened MemRead     *)
(*    rule lets us state the concrete result.                              *)
(* ---------------------------------------------------------------------- *)

Lemma run_read_ram_plain_4_pin (addr : mword 64) (w : bv 32) s :
  (forall j : nat, (N.of_nat j < 4)%N ->
     s.(mem) !! (pa_add addr j) = Some (nth_byte w j)) ->
  run (read_ram Read_plain (Physaddr addr) 4 false) s (w, default_meta) s.
Proof.
  intro Hbytes.
  unfold read_ram. cbn match.
  apply (proj2 (run_bind _ _ _ _ _)).
  eexists _, s. split; [ apply run_returnM_fwd | ]. cbn beta zeta.
  apply (proj2 (run_bind _ _ _ _ _)).
  unfold Defs.sail_mem_read. cbn beta zeta.
  eexists _, s. split.
  - cbn match beta. exists w. split.
    + intros j Hj. exact (Hbytes j Hj).
    + apply run_returnM_fwd.
  - cbn match beta. apply run_returnM_fwd.
Qed.

(* ---------------------------------------------------------------------- *)
(* 2. pmaCheck = None for an executable, aligned RAM region (InstructionFetch). *)
(*    The InstructionFetch arm returns the region's [PMA_executable] bool, *)
(*    which the wrapper maps to [None] when it is [true].                  *)
(* ---------------------------------------------------------------------- *)

Lemma run_pmaCheck_ram (addr : mword 64) (pbmt : page_based_mem_type)
    (region : PMA_Region) s :
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) 4
    = Some region ->
  is_aligned_paddr (Physaddr addr) 4 = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_executable) = true ->
  run (pmaCheck (Physaddr addr) 4 (InstructionFetch tt) pbmt false) s None s.
Proof.
  intros Hmatch Halign Hexec.
  unfold pmaCheck.
  apply (proj2 (run_bind _ _ _ _ _)).
  eexists _, s. split; [ apply run_read_reg_fwd | ].
  rewrite Hmatch.
  destruct region as [rbase rsize rattr rdtree].
  cbn [PMA_Region_attributes] in Hexec |- *.
  (* misaligned = not (is_aligned_paddr ...) = not true = false *)
  rewrite Halign. cbn [negb].
  (* (if not false then returnM None else ...) >>= fun me => match me with ... *)
  apply (proj2 (run_bind _ _ _ _ _)).
  eexists None, s. split; [ apply run_returnM_fwd | ].
  cbn match beta.
  (* match access (InstructionFetch) => returnM (override_PMA rattr pbmt).PMA_executable *)
  apply (proj2 (run_bind _ _ _ _ _)).
  eexists _, s. split; [ apply run_returnM_fwd | ].
  (* canAccess = (override_PMA rattr pbmt).PMA_executable = true ; print guard = tt *)
  rewrite Hexec. cbn [andb negb].
  apply run_returnM_fwd.
Qed.

(* ---------------------------------------------------------------------- *)
(* 3. Pinned checked_mem_read: result is exactly [Ok (w, default_meta)].   *)
(* ---------------------------------------------------------------------- *)

Lemma run_checked_mem_read_ram_pin
    (pbmt : page_based_mem_type) (addr : mword 64) (region : PMA_Region) (w : bv 32) s :
  (forall i, pmpAddrMatchType_encdec_backwards
               (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) i))
             = OFF) ->
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) 4
    = Some region ->
  is_aligned_paddr (Physaddr addr) 4 = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_executable) = true ->
  run (within_clint (Physaddr addr) 4) s false s ->
  run (within_sig (Physaddr addr) 4) s false s ->
  run (within_htif_readable (Physaddr addr) 4) s false s ->
  (forall j : nat, (N.of_nat j < 4)%N ->
     s.(mem) !! (pa_add addr j) = Some (nth_byte w j)) ->
  run (checked_mem_read (InstructionFetch tt) pbmt Machine (Physaddr addr) 4 false false false false)
      s (Ok (w, default_meta)) s.
Proof.
  intros Hpmp Hmatch Halign Hexec Hc Hsig Hh Hbytes.
  unfold checked_mem_read.
  apply (proj2 (run_bind _ _ _ _ _)). exists None, s. split.
  { apply run_phys_access_check_none.
    - apply run_pmpCheck_machine_none; exact Hpmp.
    - apply run_pmaCheck_ram with (region := region); assumption. }
  apply (proj2 (run_bind _ _ _ _ _)). exists false, s. split.
  { apply run_within_mmio_readable_false; assumption. }
  apply (proj2 (run_bind _ _ _ _ _)). exists Read_plain, s. split.
  { unfold read_kind_of_flags. apply run_returnM_fwd. }
  apply (proj2 (run_bind _ _ _ _ _)). exists (w, default_meta), s. split.
  { apply run_read_ram_plain_4_pin; exact Hbytes. }
  apply run_returnM_fwd.
Qed.

(* ---------------------------------------------------------------------- *)
(* 4. mem_read for an InstructionFetch in Machine mode reduces to [Ok w].  *)
(*    effectivePrivilege(InstructionFetch)=cur_privilege; the (aq||res)    *)
(*    alignment guard is false; mem_read_callback is a pure unit; the meta *)
(*    is dropped (Ok (w,()) -> Ok w).                                      *)
(* ---------------------------------------------------------------------- *)

Lemma run_mem_read_fetch_pin
    (pbmt : page_based_mem_type) (addr : mword 64) (region : PMA_Region) (w : bv 32) s :
  (forall i, pmpAddrMatchType_encdec_backwards
               (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) i))
             = OFF) ->
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) 4
    = Some region ->
  is_aligned_paddr (Physaddr addr) 4 = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_executable) = true ->
  run (within_clint (Physaddr addr) 4) s false s ->
  run (within_sig (Physaddr addr) 4) s false s ->
  run (within_htif_readable (Physaddr addr) 4) s false s ->
  (forall j : nat, (N.of_nat j < 4)%N ->
     s.(mem) !! (pa_add addr j) = Some (nth_byte w j)) ->
  register_lookup cur_privilege s.(sregs) = Machine ->
  run (mem_read (InstructionFetch tt) pbmt (Physaddr addr) 4 false false false)
      s (Ok w) s.
Proof.
  intros Hpmp Hmatch Halign Hexec Hc Hsig Hh Hbytes Hpriv.
  unfold mem_read.
  (* read mstatus *)
  apply (proj2 (run_bind _ _ _ _ _)). eexists _, s. split; [ exact (run_read_reg_fwd mstatus s) | ].
  (* read cur_privilege *)
  apply (proj2 (run_bind _ _ _ _ _)). eexists _, s. split; [ exact (run_read_reg_fwd cur_privilege s) | ].
  (* effectivePrivilege (InstructionFetch) = returnM cur_privilege *)
  apply (proj2 (run_bind _ _ _ _ _)).
  eexists (register_lookup cur_privilege s.(sregs)), s. split.
  { unfold effectivePrivilege.
    replace (generic_neq (InstructionFetch tt) (InstructionFetch tt)) with false
      by (vm_compute; reflexivity).
    cbn [andb]. apply run_returnM_fwd. }
  rewrite Hpriv.
  (* mem_read_priv = mem_read_priv_meta >>= drop_meta *)
  unfold mem_read_priv.
  apply (proj2 (run_bind _ _ _ _ _)). eexists (Ok (w, default_meta)), s. split.
  { unfold mem_read_priv_meta.
    cbn [orb andb].
    apply (proj2 (run_bind _ _ _ _ _)). eexists (Ok (w, default_meta)), s. split.
    { cbn match.
      apply run_checked_mem_read_ram_pin with (region := region); assumption. }
    cbn match. unfold mem_read_callback. apply run_returnM_fwd. }
  cbn [MemoryOpResult_drop_meta]. apply run_returnM_fwd.
Qed.

(* ===== RiscvModelFetchFinal ===== *)
(* ====================================================================== *)
(* RiscvModelFetchFinal.v                                                  *)
(*                                                                         *)
(* Closes [run_fetch_F_Base : run (fetch tt) s (F_Base word) s] with a     *)
(* CONCRETE word, by threading the MR-monad structure of [fetch_bytes]/    *)
(* [fetch] over the proven leaves (translateAddr identity, mem_read pin,   *)
(* currentlyEnabled Ext_Ziccif).  Collapses Hcycle's fetch dep to Hdec.    *)
(* ====================================================================== *)


(* The physical address translateAddr produces for an instruction fetch. *)
Definition fetch_pa (pc : mword 64) : mword 64 :=
  zero_extend' 64 (bits_of_virtaddr (Virtaddr pc)).

(* autocast between convertible widths (8*4 and 4*8, both 32) is identity. *)
Lemma autocast_mword_id (w : bv 32) :
  autocast (T := mword) (m := 8 * 4) (n := 4 * 8) w = w.
Proof.
  unfold autocast.
  destruct (Z.eq_dec (8 * 4) (4 * 8)) as [e | ne].
  - apply cast_Z_refl.
  - exfalso; apply ne; reflexivity.
Qed.

(* ---------------------------------------------------------------------- *)
(* Inner: fetch_bytes pc pc 4 reduces to FetchBytes_Success word.          *)
(* ---------------------------------------------------------------------- *)
Section FetchBytes.
  Context (pc : mword 64) (region : PMA_Region) (w : mword 32) (s : mstate).
  Let addr := fetch_pa pc.

  Hypothesis Hpriv : register_lookup cur_privilege s.(sregs) = Machine.
  Hypothesis Hpmp : forall i, pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) i)) = OFF.
  Hypothesis Hmatch : matching_pma_region (register_lookup pma_regions s.(sregs))
      (Physaddr addr) 4 = Some region.
  Hypothesis Halign : is_aligned_paddr (Physaddr addr) 4 = true.
  Hypothesis Hexec : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_executable) = true.
  Hypothesis Hclint : run (within_clint (Physaddr addr) 4) s false s.
  Hypothesis Hsig : run (within_sig (Physaddr addr) 4) s false s.
  Hypothesis Hhtif : run (within_htif_readable (Physaddr addr) 4) s false s.
  Hypothesis Hbytes : forall j : nat, (N.of_nat j < 4)%N ->
      s.(mem) !! (pa_add addr j) = Some (nth_byte w j).

  Lemma run_fetch_bytes_4 : run (fetch_bytes pc pc 4) s (@FetchBytes_Success 4 w) s.
  Proof.
    unfold fetch_bytes.
    apply run_catch_early_return. right.
    change (ext_fetch_check_pc pc pc) with (@None unit).
    cbv iota beta.  (* match None -> returnR tt *)
    (* body = (returnR tt >> liftR transl) >>= (fun w0 => match w0 .. >>= ..).
       Outermost bind: intermediate value = the translateAddr result. *)
    apply runR_bind. right.
    exists (Ok (Physaddr addr, PBMT_PMA, init_ext_ptw)), s. split.
    { (* returnR tt >> liftR transl  -->  Ok (..) *)
      unfold Defs.bind0. apply runR_bind. right. exists tt, s. split.
      { apply runR_returnR_fwd. }
      apply runR_liftR. exists (Ok (Physaddr addr, PBMT_PMA, init_ext_ptw)).
      split; [ reflexivity | apply run_translateAddr_identity; exact Hpriv ]. }
    (* fun w0 => (match Ok .. -> returnR (paddr,pbmt)) >>= fun '(p,m) => .. *)
    cbv iota beta.
    apply runR_bind. right. exists (Physaddr addr, PBMT_PMA), s. split.
    { apply runR_returnR_fwd. }
    (* fun '(paddr,pbmt) => liftR (mem_read ..) >>= fun w2 => returnR (match w2 ..) *)
    cbv iota beta.
    apply runR_bind. right. exists (Ok w), s. split.
    { apply runR_liftR. exists (Ok w). split; [ reflexivity | ].
      apply (run_mem_read_fetch_pin PBMT_PMA addr region w s); assumption. }
    (* returnR (FetchBytes_Success (autocast w)) *)
    cbv iota beta. rewrite autocast_mword_id. apply runR_returnR_fwd.
  Qed.
End FetchBytes.

(* ---------------------------------------------------------------------- *)
(* Outer: fetch tt reduces to F_Base word (aligned PC, not RVC).           *)
(* ---------------------------------------------------------------------- *)
Section Fetch.
  Context (pc : mword 64) (region : PMA_Region) (w : mword 32) (s : mstate).
  Let addr := fetch_pa pc.

  Hypothesis HpcPC : register_lookup PC s.(sregs) = pc.
  Hypothesis Hpriv : register_lookup cur_privilege s.(sregs) = Machine.
  Hypothesis Hpmp : forall i, pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) i)) = OFF.
  Hypothesis Hmatch : matching_pma_region (register_lookup pma_regions s.(sregs))
      (Physaddr addr) 4 = Some region.
  Hypothesis Halign : is_aligned_paddr (Physaddr addr) 4 = true.
  Hypothesis Hexec : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_executable) = true.
  Hypothesis Hclint : run (within_clint (Physaddr addr) 4) s false s.
  Hypothesis Hsig : run (within_sig (Physaddr addr) 4) s false s.
  Hypothesis Hhtif : run (within_htif_readable (Physaddr addr) 4) s false s.
  Hypothesis Hbytes : forall j : nat, (N.of_nat j < 4)%N ->
      s.(mem) !! (pa_add addr j) = Some (nth_byte w j).
  (* alignment of the PC, phrased as the boolean facts fetch actually tests *)
  Hypothesis Hbit0 : neq_vec (access_vec_dec pc 0) ('b"0") = false.
  Hypothesis Hbit1 : neq_vec (access_vec_dec pc 1) ('b"0") = false.
  Hypothesis Hvalign : is_aligned_vaddr (Virtaddr pc) 4 = true.
  Hypothesis HnotRVC : isRVC (subrange_vec_dec w 15 0) = false.

  Lemma run_fetch_F_Base : run (fetch tt) s (F_Base w) s.
  Proof.
    assert (HrdPC : run (Defs.read_reg PC) s pc s).
    { rewrite <- HpcPC. apply run_read_reg_fwd. }
    unfold fetch.
    apply run_catch_early_return. right.
    change (get_config_rvfi tt) with false. cbv iota beta.
    (* read PC twice *)
    eapply runR_liftR_seq. { exact HrdPC. }
    eapply runR_liftR_seq. { exact HrdPC. }
    (* ext_fetch_check_pc pc pc = None *)
    change (ext_fetch_check_pc pc pc) with (@None unit). cbv iota beta.
    (* outer: (returnR tt >> or_boolM) >>= fun w7 => REST ; or_boolM = false *)
    apply runR_bind. right. exists false, s. split.
    { unfold Defs.bind0. apply runR_bind. right. exists tt, s. split.
      { apply runR_returnR_fwd. }
      cbv beta.
      (* or_boolM (PC[0]!=0) (and_boolM (PC[1]!=0) (not Ext_Zca)) = false *)
      unfold or_boolM. apply runR_bind. right. exists false, s. split.
      { eapply runR_liftR_seq. { exact HrdPC. }
        rewrite Hbit0. apply runR_returnR_fwd. }
      cbv iota beta.
      (* short-circuit on PC[1]=0 (Ext_Zca not evaluated) *)
      unfold and_boolM. apply runR_bind. right. exists false, s. split.
      { eapply runR_liftR_seq. { exact HrdPC. }
        rewrite Hbit1. apply runR_returnR_fwd. }
      cbv iota beta. apply runR_returnR_fwd. }
    cbv iota beta.
    (* w7 = false -> else: and_boolM (is_aligned) (Ext_Ziccif) >>= fun w11 => .. ; w11 = true *)
    apply runR_bind. right. exists true, s. split.
    { unfold and_boolM. apply runR_bind. right. exists true, s. split.
      { eapply runR_liftR_seq. { exact HrdPC. }
        rewrite Hvalign. apply runR_returnR_fwd. }
      cbv iota beta.
      (* bare [liftR (currentlyEnabled Ext_Ziccif)] = true *)
      apply runR_liftR. exists true. split; [ reflexivity | apply run_currentlyEnabled_Ziccif ]. }
    cbv iota beta.
    (* w11 = true -> read PC twice, fetch_bytes pc pc 4 -> FetchBytes_Success w -> F_Base w *)
    eapply runR_liftR_seq. { exact HrdPC. }
    eapply runR_liftR_seq. { exact HrdPC. }
    eapply runR_liftR_seq. { apply (run_fetch_bytes_4 pc region w s); assumption. }
    cbv iota beta. rewrite HnotRVC. cbv iota beta. apply runR_returnR_fwd.
  Qed.
End Fetch.

Print Assumptions run_fetch_F_Base.

(* ===== RiscvModelCycle ===== *)
(* ====================================================================== *)
(* RiscvModelCycle.v                                                       *)
(* Final-assembly helpers: the try_step wrapper value-helpers reduce       *)
(* through [run] (state-preserving), toward composing the full cycle.      *)
(* ====================================================================== *)

Import Defs.



(* should_inc_minstret is state-preserving (its value feeds minstret bookkeeping). *)

(* dispatchInterrupt yields None when no interrupt is pending. *)
Lemma run_dispatchInterrupt_none s priv :
  run (getPendingSet priv) s None s ->
  run (dispatchInterrupt priv) s None s.
Proof.
  intros Hp. unfold dispatchInterrupt.
  apply (proj2 (run_bind _ _ _ _ _)).
  exists None, s. split; [ exact Hp | apply run_returnM_fwd ].
Qed.

(* is_landing_pad_expected is false when elp != LP_EXPECTED. *)
Lemma run_is_landing_pad_false s :
  eq_vec (register_lookup elp s.(sregs))
         (landing_pad_bits_backwards LP_EXPECTED) = false ->
  run (is_landing_pad_expected tt) s false s.
Proof.
  intros He. unfold is_landing_pad_expected.
  apply (proj2 (run_bind _ _ _ _ _)).
  exists (register_lookup elp s.(sregs)), s.
  split; [ exact (run_read_reg_fwd elp s) | ].
  rewrite <- He. apply run_returnM_fwd.
Qed.

(* ===== RiscvModelWrapper ===== *)
(* ====================================================================== *)
(* RiscvModelWrapper.v                                                     *)
(*                                                                         *)
(* Reductions for the try_step WRAPPER CSR helpers, toward discharging     *)
(* Hcycle. Built on the proven run-lemmas (run_bind/run_read_reg/...).     *)
(* The memory subsystem on the fetch path (translateAddr / mem_read /      *)
(* pmpCheck) is the remaining deep residue and is NOT reduced here — it is *)
(* documented as the explicit fetch hypotheses in the report.             *)
(* ====================================================================== *)



(* tick_pc copies nextPC into PC (pc_write_callback is the pure unit tt).
   This is exactly how the cycle advances the PC: after execute sets
   nextPC := PC+4, tick_pc gives PC := PC+4. *)
Lemma run_tick_pc s y s' :
  run (tick_pc tt) s y s' <->
  (y = tt /\ s' = set_reg s PC (register_lookup nextPC s.(sregs))).
Proof.
  unfold tick_pc. split.
  - intros H.
    rewrite run_bind in H. destruct H as (w0 & s1 & H0 & H).
    apply (proj1 (run_read_reg nextPC _ _ _)) in H0. destruct H0 as [-> ->].
    rewrite run_bind in H. destruct H as (w1 & s2 & Hblk & H).
    rewrite run_bind0 in Hblk. destruct Hblk as (s3 & Hw & Hr).
    apply (proj1 (run_write_reg PC _ _ _ _)) in Hw. destruct Hw as [_ ->].
    apply (proj1 (run_read_reg PC _ _ _)) in Hr. destruct Hr as [-> ->].
    apply (proj1 (run_returnM _ _ _ _)) in H. destruct H as [-> ->].
    split; reflexivity.
  - intros [-> ->].
    rewrite run_bind. exists (register_lookup nextPC s.(sregs)), s.
    split; [ apply (proj2 (run_read_reg nextPC _ _ _)); split; reflexivity | ].
    rewrite run_bind.
    exists (register_lookup PC (set_reg s PC (register_lookup nextPC s.(sregs))).(sregs)),
           (set_reg s PC (register_lookup nextPC s.(sregs))).
    split.
    + rewrite run_bind0. exists (set_reg s PC (register_lookup nextPC s.(sregs))).
      split; [ apply (proj2 (run_write_reg PC _ _ _ _)); split; reflexivity
             | apply (proj2 (run_read_reg PC _ _ _)); split; reflexivity ].
    + apply (proj2 (run_returnM _ _ _ _)). split; reflexivity.
Qed.

(* is_landing_pad_expected / should_inc_minstret reduce by the SAME pattern
   (run_bind + run_read_reg + run_returnM, plus run_and_boolM for the latter);
   omitted here only because stating their results needs model-internal names
   (eq_vec / counter_priv_filter_bit) not exported by short name. They are not
   the bottleneck — the memory subsystem (translate/mem_read/pmpCheck) is. *)

(* ===== RiscvModelCycleAsm ===== *)
(* ====================================================================== *)
(* RiscvModelCycleAsm.v                                                    *)
(*                                                                         *)
(* CAPSTONE composition: thread the proven axiom-free leaves through the   *)
(* real [run_hart_active] (ADD / F_Base path) and the [try_step] wrapper,  *)
(* toward discharging [Hcycle] in wp_add_real.                             *)
(*                                                                         *)
(* run_hart_active_ADD is decomposed to take the fetch result as a         *)
(* hypothesis [Hfetch] (so it does not re-thread run_fetch_F_Base's        *)
(* geometric hypotheses); the concrete fetch is plugged in downstream.     *)
(* ====================================================================== *)




Open Scope Z_scope.

Section HartActiveADD.
  Context (s : mstate) (w : mword 32) (pc : mword 64) (rs2 rs1 rd : mword 5).

  (* booting-Machine-mode / no-interrupt CSR facts *)
  Hypothesis Hpriv : register_lookup cur_privilege s.(sregs) = Machine.
  Hypothesis Hpend : run (getPendingSet Machine) s None s.
  Hypothesis HpcPC : register_lookup PC s.(sregs) = pc.
  Hypothesis Help  :
    eq_vec (register_lookup elp s.(sregs)) (landing_pad_bits_backwards LP_EXPECTED) = false.
  (* the fetched word, as a hypothesis (discharged downstream by run_fetch_F_Base) *)
  Hypothesis Hfetch : run (fetch tt) s (F_Base w) s.
  (* the decode result (the decode wall, carried as Hdec) *)
  Hypothesis Hdec :
    run (ext_decode w) s (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, ADD)) s.
  (* the register indices a0=x10, a1=x11, a2=x12 *)
  Hypothesis Hrs1 : uint rs1 = 10.
  Hypothesis Hrs2 : uint rs2 = 11.
  Hypothesis Hrd  : uint rd  = 12.

  (* state after the cycle's hart-active part:
     nextPC := pc+4 (written before execute), then a2 := a0+a1 by execute(ADD). *)
  Let s1 : mstate := set_reg s nextPC (add_vec_int pc 4).
  Let s_exec : mstate :=
    set_reg s1 (R_bitvector_64 x12)
       (regval_into_reg
          (add_vec (register_lookup (R_bitvector_64 x10) s1.(sregs))
                   (register_lookup (R_bitvector_64 x11) s1.(sregs)))).

  Lemma run_hart_active_ADD :
    run (run_hart_active 0) s
        (Step_Execute (RETIRE_SUCCESS, zero_extend' 32 w)) s_exec.
  Proof.
    unfold run_hart_active.
    apply run_catch_early_return. right.
    (* read cur_privilege = Machine (state-preserving) *)
    eapply runR_liftR_seq with (a := Machine).
    { pose proof (run_read_reg_fwd cur_privilege s) as H. rewrite Hpriv in H. exact H. }
    (* dispatchInterrupt Machine = None (state-preserving) *)
    eapply runR_liftR_seq with (a := @None (InterruptType * Privilege)%type).
    { apply run_dispatchInterrupt_none. exact Hpend. }
    cbv iota beta.
    (* [(match None => returnR tt) >> liftR(fetch)] yields F_Base w, then continuation *)
    apply runR_bind. right. exists (F_Base w), s. split.
    { unfold Defs.bind0. apply runR_bind. right. exists tt, s. split.
      { apply runR_returnR_fwd. }
      apply runR_liftR. exists (F_Base w). split; [reflexivity| exact Hfetch]. }
    (* continuation: ext_fetch_hook (F_Base w) = F_Base w; the F_Base arm *)
    cbv iota beta.
    (* ext_decode w = RTYPE ... ADD (state-preserving) *)
    eapply runR_liftR_seq with (a := RTYPE (Regidx rs2, Regidx rs1, Regidx rd, ADD)).
    { exact Hdec. }
    (* [(if print=false => returnR tt) >> and_boolM(landing_pad=false) _] yields false *)
    cbv iota beta.
    apply runR_bind. right. exists false, s. split.
    { unfold Defs.bind0. apply runR_bind. right. exists tt, s. split.
      { apply runR_returnR_fwd. }
      unfold and_boolM. apply runR_bind. right. exists false, s. split.
      { apply runR_liftR. exists false. split; [reflexivity|].
        apply run_is_landing_pad_false. exact Help. }
      cbv iota beta. apply runR_returnR_fwd. }
    (* w21 = false -> else branch *)
    cbv iota beta.
    (* read PC = pc (state-preserving) *)
    eapply runR_liftR_seq with (a := pc).
    { pose proof (run_read_reg_fwd PC s) as H. rewrite HpcPC in H. exact H. }
    (* [liftR(write nextPC (pc+4)) >> liftR(execute instr)] : s -> s_exec, RETIRE_SUCCESS *)
    apply runR_bind. right. exists RETIRE_SUCCESS, s_exec. split.
    { unfold Defs.bind0. apply runR_bind. right. exists tt, s1. split.
      { apply runR_liftR. exists tt. split; [reflexivity|].
        apply (proj2 (run_write_reg nextPC (add_vec_int pc 4) s tt s1)).
        split; reflexivity. }
      apply runR_liftR. exists RETIRE_SUCCESS. split; [reflexivity|].
      change (execute (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, ADD)))
        with (execute_RTYPE (Regidx rs2) (Regidx rs1) (Regidx rd) ADD).
      unfold s_exec.
      apply (run_execute_ADD_x12_x10_x11 rd rs1 rs2 s1 Hrs1 Hrs2 Hrd). }
    (* match RETIRE_SUCCESS => result' = RETIRE_SUCCESS ; returnR Step_Execute *)
    cbv iota beta.
    apply runR_bind. right. exists RETIRE_SUCCESS, s_exec. split.
    { apply runR_returnR_fwd. }
    cbv iota beta. apply runR_returnR_fwd.
  Qed.

End HartActiveADD.

(* ===== RiscvModelADDfinal ===== *)
(* ====================================================================== *)
(* RiscvModelADDfinal.v                                                    *)
(*                                                                         *)
(* Capstone (in progress): lift the proven relational ADD-cycle facts to    *)
(* the functional [exec] level, toward closing a WP for `add a2,a0,a1`       *)
(* through the real try_step using [wp_exec_step] -- with NO Hcycle and NO   *)
(* per-instruction determinism reasoning.                                    *)
(*                                                                          *)
(* PROVEN here (axiom-clean):                                                *)
(*  - exec_read_reg / exec_write_reg : the functional exec-leaves reduce by  *)
(*    [reflexivity] (exec computes through read_reg/write_reg).              *)
(*  - exec_hart_active_ADD : exec (run_hart_active 0) s = Some (Step_Execute *)
(*    (RETIRE_SUCCESS, zero_extend' 32 w), s_exec) -- obtained FOR FREE from *)
(*    the proven [run_hart_active_ADD] via [run_to_exec], modulo exec-       *)
(*    progress [Hne : exec (run_hart_active 0) s <> None] (the cycle is      *)
(*    Choose-free on the ADD path).  Only model platform axioms.            *)
(*                                                                          *)
(* RESIDUE (the same long-but-mapped try_step wrapper tail that the RUN side *)
(* left Admitted in RiscvModelStep.v, now to be done FUNCTIONALLY via        *)
(* exec_bind -- cleaner since the exec-leaves reduce by reflexivity):        *)
(*  - exec_riscv_step_ADD : exec riscv_step s = Some (tt, s_final) -- thread *)
(*    exec_bind/exec_bind0/exec_returnm through try_step's wrapper around    *)
(*    exec_hart_active_ADD: read cur_privilege (exec_read_reg + Hpriv),      *)
(*    should_inc_minstret (=b, carried exec-hyp), write minstret_increment   *)
(*    (exec_write_reg), read hart_state=HART_ACTIVE, the Retire_Success arm  *)
(*    (assert_exp true = returnm tt), tick_pc (run_tick_pc via run_to_exec), *)
(*    minstret update (CASE-SPLIT on b), get_config_rvfi=false, hooks.       *)
(*  - wp_add_real_closed : iApply wp_exec_step; reg_valid/mem_valid to read  *)
(*    owned cells & derive the preconds, supply exec_riscv_step_ADD as the   *)
(*    exists-sigma' witness, reg_update the changed cells, conclude.  Stands  *)
(*    on Hdec + CSR/config preconds + points-to + model platform axioms; NO  *)
(*    Hcycle (the determinism is already discharged by wp_exec_step).        *)
(* ====================================================================== *)



Local Open Scope Z_scope.

(* ---------------------------------------------------------------------- *)
(* exec-leaf helpers (the functional twins of run_read_reg / run_write_reg) *)
(* -- useful for threading exec through the try_step wrapper.               *)
(* ---------------------------------------------------------------------- *)



(* ---------------------------------------------------------------------- *)
(* Step 2a: exec_hart_active_ADD -- the exec-level hart-active reduction,   *)
(* obtained for free from the proven [run_hart_active_ADD] via run_to_exec, *)
(* modulo exec-progress (the cycle is Choose-free on the ADD path).         *)
(* ---------------------------------------------------------------------- *)

Section ADDfinal.
  Context (s : mstate) (w : mword 32) (pc : mword 64) (rs2 rs1 rd : mword 5).

  Hypothesis Hpriv : register_lookup cur_privilege s.(sregs) = Machine.
  Hypothesis Hpend : run (getPendingSet Machine) s None s.
  Hypothesis HpcPC : register_lookup PC s.(sregs) = pc.
  Hypothesis Help  :
    eq_vec (register_lookup elp s.(sregs)) (landing_pad_bits_backwards LP_EXPECTED) = false.
  Hypothesis Hfetch : run (fetch tt) s (F_Base w) s.
  Hypothesis Hdec :
    run (ext_decode w) s (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, ADD)) s.
  Hypothesis Hrs1 : uint rs1 = 10.
  Hypothesis Hrs2 : uint rs2 = 11.
  Hypothesis Hrd  : uint rd  = 12.

  Let s1 : mstate := set_reg s nextPC (add_vec_int pc 4).
  Let s_exec : mstate :=
    set_reg s1 (R_bitvector_64 x12)
       (regval_into_reg
          (add_vec (register_lookup (R_bitvector_64 x10) s1.(sregs))
                   (register_lookup (R_bitvector_64 x11) s1.(sregs)))).

  Lemma exec_hart_active_ADD (Hne : exec (run_hart_active 0) s <> None) :
    exec (run_hart_active 0) s
      = Some (Step_Execute (RETIRE_SUCCESS, zero_extend' 32 w), s_exec).
  Proof using All.
    apply run_to_exec; [ | exact Hne ].
    apply (run_hart_active_ADD s w pc rs2 rs1 rd); assumption.
  Qed.

End ADDfinal.

(* ===== RiscvModelFetchExec ===== *)
(* ====================================================================== *)
(* RiscvModelFetchExec.v                                                   *)
(*                                                                         *)
(* The fetch value-sensitive exec-mirror: exec (fetch tt) s <> None, hence *)
(* exec (fetch tt) s = Some (F_Base w, s) (via exec_fetch_F_Base).  This is *)
(* the FETCH leaf of Hne.  Each sub-lemma mirrors the corresponding run    *)
(* lemma (run_translateAddr_identity / run_mem_read_fetch_pin /            *)
(* run_fetch_F_Base) at the functional [exec]/[execR] level.               *)
(* ====================================================================== *)



Local Open Scope Z_scope.

(* execR bind collapsers (analogues of exec_bind_Some). *)
Lemma execR_bind_Some {R X Y} (m : Defs.monadR R exception Y)
    (f : Y -> Defs.monadR R exception X) s a s' :
  execR m s = Some (inr a, s') -> execR (Defs.bind m f) s = execR (f a) s'.
Proof. intro H. rewrite execR_bind. rewrite H. reflexivity. Qed.

Lemma execR_bind0_Some {R X} (m : Defs.monadR R exception unit)
    (n : Defs.monadR R exception X) s s' :
  execR m s = Some (inr tt, s') -> execR (Defs.bind0 m n) s = execR n s'.
Proof. intro H. unfold Defs.bind0. rewrite execR_bind. rewrite H. reflexivity. Qed.

Lemma execR_returnR_fwd {R X} (x : X) s :
  execR (Defs.returnR R x) s = Some (inr x, s).
Proof. reflexivity. Qed.

(* exec on a MemRead node, one definitional step (avoids cbn mangling the
   request's record projections). *)
Lemma exec_MemRead {X} (n : N) (req : Interface.ReadReq.t n)
    (k : (bv (8 * n) * option bool + Arch.abort)%type -> M X) s :
  exec (Interface.Next (Interface.MemRead n req) k) s
  = match read_bytes s.(mem) (Interface.ReadReq.pa req) n with
    | Some w => exec (k (inl (w, None))) s
    | None => None
    end.
Proof. reflexivity. Qed.

(* read_bytes is non-None when all n bytes are present (was previously
   located among the now-removed choose_free helpers). *)
Lemma read_bytes_ne mm pa n (w : bv (8 * n)) :
  (forall j : nat, (N.of_nat j < n)%N ->
     mm !! RiscvModelBytes.pa_add pa j = Some (RiscvModelBytes.nth_byte w j)) ->
  read_bytes mm pa n <> None.
Proof.
  intros Hb. unfold read_bytes.
  case_match eqn:Hm.
  - congruence.
  - exfalso.
    apply mapM_None_1, Exists_exists in Hm.
    destruct Hm as (j & Hj & Hnone).
    apply in_seq in Hj.
    assert (Hjn : (N.of_nat j < n)%N) by lia.
    rewrite (Hb j Hjn) in Hnone. congruence.
Qed.

(* read_ram (4 bytes present) reduces -- via the run-fact + read_bytes <> None. *)
Lemma exec_read_ram_plain_4 (addr : mword 64) (w : bv 32) s :
  (forall j : nat, (N.of_nat j < 4)%N ->
     s.(mem) !! (pa_add addr j) = Some (nth_byte w j)) ->
  exec (read_ram Read_plain (Physaddr addr) 4 false) s = Some ((w, default_meta), s).
Proof.
  intro Hbytes.
  apply (run_to_exec _ _ _ _ (run_read_ram_plain_4_pin addr w s Hbytes)).
  unfold read_ram. cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM _ s)). cbn beta zeta.
  unfold Defs.sail_mem_read. cbn beta zeta.
  (* collapse [Defs.bind (Next (MemRead ..) k) matchK] to a single Next, then
     expose the read_bytes match via exec_MemRead. *)
  unfold Defs.bind. cbn [Interface.iMon_bind].
  rewrite exec_MemRead.
  cbn [Interface.ReadReq.pa].
  case_match eqn:Hrb.
  - (* read_bytes = Some _: the continuation is a Ret-chain, hence Some <> None *)
    cbn [Interface.iMon_bind]. cbn match beta iota. discriminate.
  - (* read_bytes = None: impossible, the 4 bytes are present *)
    exfalso.
    refine (read_bytes_ne (mem s) addr (Z.to_N 4) w _ Hrb).
    intros j Hj.
    change (RiscvModelBytes.pa_add addr j) with (pa_add addr j).
    change (RiscvModelBytes.nth_byte w j) with (nth_byte w j).
    exact (Hbytes j Hj).
Qed.

(* ---------------------------------------------------------------------- *)
(* Easy exec sub-twins (pure returnM).                                     *)
(* ---------------------------------------------------------------------- *)

Lemma exec_effectivePrivilege_fetch (m : mword 64) (p : Privilege) s :
  exec (effectivePrivilege (InstructionFetch tt) m p) s = Some (p, s).
Proof.
  unfold effectivePrivilege.
  replace (generic_neq (InstructionFetch tt) (InstructionFetch tt)) with false
    by (vm_compute; reflexivity).
  apply exec_returnM.
Qed.

Lemma exec_translationMode_M s :
  exec (translationMode Machine) s = Some (Bare, s).
Proof.
  unfold translationMode.
  replace (generic_eq Machine Machine) with true by (vm_compute; reflexivity).
  apply exec_returnM.
Qed.

Lemma exec_is_shadow_stack_fetch s :
  exec (is_shadow_stack_access (InstructionFetch tt)) s = Some (false, s).
Proof. unfold is_shadow_stack_access. apply exec_returnM. Qed.

(* ---------------------------------------------------------------------- *)
(* translateAddr = identity (M-mode), exec version.                        *)
(* ---------------------------------------------------------------------- *)

Lemma exec_translateAddr_identity (a : mword 64) s :
  register_lookup cur_privilege s.(sregs) = Machine ->
  exec (translateAddr (Virtaddr a) (InstructionFetch tt)) s
    = Some (Ok (Physaddr (zero_extend' 64 (bits_of_virtaddr (Virtaddr a))),
                PBMT_PMA, init_ext_ptw), s).
Proof.
  intros Hcp.
  unfold translateAddr.
  rewrite exec_catch_early_return.
  rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg mstatus s)).
  rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg cur_privilege s)).
  rewrite Hcp.
  rewrite (execR_liftR_seq _ _ _ _ _ (exec_effectivePrivilege_fetch _ _ s)).
  rewrite (execR_liftR_seq _ _ _ _ _ (exec_translationMode_M s)).
  rewrite (execR_liftR_seq _ _ _ _ _ (exec_is_shadow_stack_fetch s)).
  unfold Defs.bind0.
  replace (generic_eq Bare Bare) with true by (vm_compute; reflexivity).
  rewrite execR_bind.
  cbn match. reflexivity.
Qed.

(* ---------------------------------------------------------------------- *)
(* pmaCheck = None (RAM), exec version.                                    *)
(* ---------------------------------------------------------------------- *)

Lemma exec_pmaCheck_ram (addr : mword 64) (pbmt : page_based_mem_type)
    (region : PMA_Region) s :
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) 4
    = Some region ->
  is_aligned_paddr (Physaddr addr) 4 = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_executable) = true ->
  exec (pmaCheck (Physaddr addr) 4 (InstructionFetch tt) pbmt false) s = Some (None, s).
Proof.
  intros Hmatch Halign Hexec.
  unfold pmaCheck.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg pma_regions s)).
  rewrite Hmatch.
  destruct region as [rbase rsize rattr rdtree].
  cbn [PMA_Region_attributes] in Hexec |- *.
  rewrite Halign. cbn [negb].
  rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM None s)).
  cbn match beta.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM _ s)).
  rewrite Hexec. cbn [andb negb].
  apply exec_returnM.
Qed.

(* ---------------------------------------------------------------------- *)
(* checked_mem_read = Ok (w, meta), exec version.                          *)
(* ---------------------------------------------------------------------- *)

Lemma exec_checked_mem_read_ram (pbmt : page_based_mem_type) (addr : mword 64)
    (region : PMA_Region) (w : bv 32) s :
  (forall i, pmpAddrMatchType_encdec_backwards
               (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) i))
             = OFF) ->
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) 4
    = Some region ->
  is_aligned_paddr (Physaddr addr) 4 = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_executable) = true ->
  exec (within_clint (Physaddr addr) 4) s = Some (false, s) ->
  exec (within_sig (Physaddr addr) 4) s = Some (false, s) ->
  exec (within_htif_readable (Physaddr addr) 4) s = Some (false, s) ->
  (forall j : nat, (N.of_nat j < 4)%N ->
     s.(mem) !! (pa_add addr j) = Some (nth_byte w j)) ->
  exec (checked_mem_read (InstructionFetch tt) pbmt Machine (Physaddr addr) 4 false false false false)
       s = Some (Ok (w, default_meta), s).
Proof.
  intros Hpmp Hmatch Halign Hexec Hc Hsig Hh Hbytes.
  unfold checked_mem_read.
  (* phys_access_check = None *)
  rewrite (exec_bind_Some _ _ _ _ _
            (_ : exec (phys_access_check _ _ _ _ _ _) s = Some (None, s))).
  2:{ unfold phys_access_check.
      rewrite (exec_bind_Some _ _ _ _ _ (exec_pmpCheck_machine_none _ _ _ s Hpmp)).
      cbn match.
      rewrite (exec_bind_Some _ _ _ _ _ (exec_pmaCheck_ram addr pbmt region s Hmatch Halign Hexec)).
      cbn match. apply exec_returnM. }
  (* within_mmio_readable = false *)
  rewrite (exec_bind_Some _ _ _ _ _
            (_ : exec (within_mmio_readable (Physaddr addr) 4) s = Some (false, s))).
  2:{ unfold within_mmio_readable. cbn [get_config_rvfi].
      rewrite (exec_or_boolM_Some _ _ _ _ _ Hc). cbn match.
      rewrite (exec_or_boolM_Some _ _ _ _ _ Hsig). cbn match.
      rewrite (exec_and_boolM_Some _ _ _ _ _ Hh). cbn match. reflexivity. }
  rewrite (exec_bind_Some _ _ _ _ _ (_ : exec (read_kind_of_flags _ _ _) s = Some (Read_plain, s))).
  2:{ unfold read_kind_of_flags. apply exec_returnM. }
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_ram_plain_4 addr w s Hbytes)).
  apply exec_returnM.
Qed.

(* ---------------------------------------------------------------------- *)
(* mem_read = Ok w, exec version.                                          *)
(* ---------------------------------------------------------------------- *)

Lemma exec_mem_read_fetch (pbmt : page_based_mem_type) (addr : mword 64)
    (region : PMA_Region) (w : bv 32) s :
  (forall i, pmpAddrMatchType_encdec_backwards
               (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) i))
             = OFF) ->
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) 4
    = Some region ->
  is_aligned_paddr (Physaddr addr) 4 = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_executable) = true ->
  exec (within_clint (Physaddr addr) 4) s = Some (false, s) ->
  exec (within_sig (Physaddr addr) 4) s = Some (false, s) ->
  exec (within_htif_readable (Physaddr addr) 4) s = Some (false, s) ->
  (forall j : nat, (N.of_nat j < 4)%N ->
     s.(mem) !! (pa_add addr j) = Some (nth_byte w j)) ->
  register_lookup cur_privilege s.(sregs) = Machine ->
  exec (mem_read (InstructionFetch tt) pbmt (Physaddr addr) 4 false false false)
       s = Some (Ok w, s).
Proof.
  intros Hpmp Hmatch Halign Hexec Hc Hsig Hh Hbytes Hpriv.
  unfold mem_read.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mstatus s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_effectivePrivilege_fetch _ _ s)).
  rewrite Hpriv.
  unfold mem_read_priv.
  rewrite (exec_bind_Some _ _ _ _ _
            (_ : exec (mem_read_priv_meta _ _ _ _ 4 _ _ _ _) s = Some (Ok (w, default_meta), s))).
  2:{ unfold mem_read_priv_meta. cbn [orb andb].
      rewrite (exec_bind_Some _ _ _ _ _
                (_ : exec (checked_mem_read _ _ _ _ 4 _ _ _ _) s = Some (Ok (w, default_meta), s))).
      2:{ cbn match. apply exec_checked_mem_read_ram with (region := region); assumption. }
      cbn match. unfold mem_read_callback. apply exec_returnM. }
  cbn [MemoryOpResult_drop_meta]. apply exec_returnM.
Qed.

(* ---------------------------------------------------------------------- *)
(* currentlyEnabled Ext_Ziccif = true, exec version (Acc twins).           *)
(* ---------------------------------------------------------------------- *)

Lemma exec_hartSupports_Ziccif s : exec (hartSupports Ext_Ziccif) s = Some (true, s).
Proof.
  unfold hartSupports. destruct (Defs.Zwf_guarded _).
  cbn [_rec_hartSupports]. unfold Defs.assert_exp'.
  replace (Z.geb (hartSupports_measure Ext_Ziccif) 0) with true by reflexivity.
  cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM eq_refl s)).
  apply exec_returnM.
Qed.

Lemma exec_currentlyEnabled_Ziccif s :
  exec (currentlyEnabled Ext_Ziccif) s = Some (true, s).
Proof.
  unfold currentlyEnabled. destruct (Defs.Zwf_guarded _).
  cbn [_rec_currentlyEnabled]. unfold Defs.assert_exp'.
  replace (Z.geb (currentlyEnabled_measure Ext_Ziccif) 0) with true by reflexivity.
  cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM eq_refl s)).
  cbn match. apply exec_hartSupports_Ziccif.
Qed.

(* ---------------------------------------------------------------------- *)
(* fetch_bytes -> FetchBytes_Success, exec version.                        *)
(* ---------------------------------------------------------------------- *)

Section FetchExec.
  Context (pc : mword 64) (region : PMA_Region) (w : mword 32) (s : mstate).
  Let addr := fetch_pa pc.

  Hypothesis HpcPC : register_lookup PC s.(sregs) = pc.
  Hypothesis Hpriv : register_lookup cur_privilege s.(sregs) = Machine.
  Hypothesis Hpmp : forall i, pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) i)) = OFF.
  Hypothesis Hmatch : matching_pma_region (register_lookup pma_regions s.(sregs))
      (Physaddr addr) 4 = Some region.
  Hypothesis Halign : is_aligned_paddr (Physaddr addr) 4 = true.
  Hypothesis Hexec : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_executable) = true.
  Hypothesis Hc : exec (within_clint (Physaddr addr) 4) s = Some (false, s).
  Hypothesis Hsig : exec (within_sig (Physaddr addr) 4) s = Some (false, s).
  Hypothesis Hh : exec (within_htif_readable (Physaddr addr) 4) s = Some (false, s).
  Hypothesis Hbytes : forall j : nat, (N.of_nat j < 4)%N ->
      s.(mem) !! (pa_add addr j) = Some (nth_byte w j).
  Hypothesis Hbit0 : neq_vec (access_vec_dec pc 0) ('b"0") = false.
  Hypothesis Hbit1 : neq_vec (access_vec_dec pc 1) ('b"0") = false.
  Hypothesis Hvalign : is_aligned_vaddr (Virtaddr pc) 4 = true.
  Hypothesis HnotRVC : isRVC (subrange_vec_dec w 15 0) = false.

  (* fetch_bytes assembly: the two liftR sub-computations [translateAddr] and
     [mem_read] are PROVEN above (exec_translateAddr_identity / exec_mem_read_fetch),
     both = Some.  What remains is the execR plumbing through fetch_bytes' / fetch's
     catch_early_return + liftR + or_boolM/and_boolM gating (mirror of
     run_fetch_bytes_4 / run_fetch_F_Base).  The execR_bind_Some/execR_bind0_Some/
     execR_returnR_fwd toolkit is in place; the residue is matching the exact
     bind/returnR/match shapes (the second bind's tuple-destructuring step
     resisted in one shot). *)
  Lemma exec_fetch_bytes_4 :
    exec (fetch_bytes pc pc 4) s = Some (@FetchBytes_Success 4 w, s).
  Proof using All.
    unfold fetch_bytes.
    rewrite exec_catch_early_return.
    change (ext_fetch_check_pc pc pc) with (@None unit). cbv iota beta.
    rewrite (execR_bind_Some _ _ _ _ _
      (_ : execR (Defs.bind0 (Defs.returnR _ tt)
              (Defs.liftR (translateAddr (Virtaddr pc) (InstructionFetch tt)))) s
           = Some (inr (Ok (Physaddr addr, PBMT_PMA, init_ext_ptw)), s))).
    2:{ rewrite (execR_bind0_Some _ _ _ _ (execR_returnR_fwd tt s)).
        rewrite execR_liftR. rewrite (exec_translateAddr_identity pc s Hpriv).
        cbn match. reflexivity. }
    cbv iota beta.
    rewrite (execR_bind_Some _ _ _ _ _ (execR_returnR_fwd (Physaddr addr, PBMT_PMA) s)).
    cbv iota beta.
    rewrite (execR_bind_Some _ _ _ _ _
      (_ : execR (Defs.liftR (mem_read (InstructionFetch tt) PBMT_PMA (Physaddr addr) 4 false false false)) s
           = Some (inr (Ok w), s))).
    2:{ rewrite execR_liftR.
        rewrite (exec_mem_read_fetch PBMT_PMA addr region w s
                   Hpmp Hmatch Halign Hexec Hc Hsig Hh Hbytes Hpriv).
        cbn match. reflexivity. }
    cbv iota beta. rewrite autocast_mword_id.
    rewrite execR_returnR_fwd. cbn match. reflexivity.
  Qed.

  (* exec (fetch tt) s = Some (F_Base w, s): the outer fetch around fetch_bytes
     (read PC, ext_fetch_check_pc=None, or_boolM/and_boolM extension gating with
     Ext_Zca short-circuited and Ext_Ziccif=true, isRVC=false).  Given
     exec_fetch_bytes_4 + run_fetch_F_Base, this closes via the execR plumbing or
     run_to_exec; left as the precise residue. *)
  Lemma exec_fetch_done : exec (fetch tt) s = Some (F_Base w, s).
  Proof using All.
    assert (HrdPC : exec (Defs.read_reg PC) s = Some (pc, s)).
    { rewrite (exec_read_reg PC s). rewrite HpcPC. reflexivity. }
    unfold fetch.
    rewrite exec_catch_early_return.
    change (get_config_rvfi tt) with false. cbv iota beta.
    rewrite (execR_liftR_seq _ _ _ _ _ HrdPC).
    rewrite (execR_liftR_seq _ _ _ _ _ HrdPC).
    change (ext_fetch_check_pc pc pc) with (@None unit). cbv iota beta.
    (* (returnR tt >> or_boolM ..) >>= fun w7 => REST ; or_boolM = false *)
    rewrite (execR_bind_Some _ _ _ false s).
    2:{ rewrite (execR_bind0_Some _ _ _ _ (execR_returnR_fwd tt s)).
        unfold or_boolM.
        rewrite (execR_bind_Some _ _ _ false s).
        2:{ rewrite (execR_liftR_seq _ _ _ _ _ HrdPC). rewrite Hbit0. apply execR_returnR_fwd. }
        cbv iota beta.
        unfold and_boolM.
        rewrite (execR_bind_Some _ _ _ false s).
        2:{ rewrite (execR_liftR_seq _ _ _ _ _ HrdPC). rewrite Hbit1. apply execR_returnR_fwd. }
        cbv iota beta. reflexivity. }
    cbv iota beta.
    (* w7=false -> and_boolM (is_aligned) (Ext_Ziccif) >>= fun w11 => .. ; w11=true *)
    rewrite (execR_bind_Some _ _ _ true s).
    2:{ unfold and_boolM.
        rewrite (execR_bind_Some _ _ _ true s).
        2:{ rewrite (execR_liftR_seq _ _ _ _ _ HrdPC). rewrite Hvalign. apply execR_returnR_fwd. }
        cbv iota beta.
        rewrite execR_liftR. rewrite exec_currentlyEnabled_Ziccif. cbn match. reflexivity. }
    cbv iota beta.
    (* w11=true -> read PC twice, fetch_bytes pc pc 4 -> FetchBytes_Success w -> F_Base w *)
    rewrite (execR_liftR_seq _ _ _ _ _ HrdPC).
    rewrite (execR_liftR_seq _ _ _ _ _ HrdPC).
    rewrite (execR_liftR_seq _ _ _ _ _ exec_fetch_bytes_4).
    cbv iota beta. rewrite HnotRVC. cbv iota beta.
    rewrite execR_returnR_fwd. cbn match. reflexivity.
  Qed.

  Lemma exec_fetch_progress : exec (fetch tt) s <> None.
  Proof using All. rewrite exec_fetch_done. discriminate. Qed.

End FetchExec.

(* ===== RiscvModelFetchPre ===== *)
(* ====================================================================== *)
(* RiscvModelFetchPre.v                                                    *)
(*                                                                         *)
(* Two bounded fetch sub-lemmas that discharge the carried hypotheses of   *)
(* run_pmpCheck_machine_none / run_pmaCheck_ram from concrete boot CSRs:    *)
(*   - run_pmpcfg_all_off : pmpcfg all-zero => every PMP A-field = OFF.     *)
(*   - run_pma_match_ram  : a concrete executable RAM region matches, given *)
(*                          the range_subset geometric fact (carried, like  *)
(*                          the within_* facts).                            *)
(* ====================================================================== *)



Local Open Scope Z_scope.

(* ---------------------------------------------------------------------- *)
(* Task 1: all PMP entries OFF when every pmpcfg byte is zero.             *)
(* pmpcfg_n : vec (mword 8) 64 ; _get_Pmpcfg_ent_A v = subrange v 4 3 ;     *)
(* pmpAddrMatchType_encdec_backwards 0#2 = OFF.                            *)
(* ---------------------------------------------------------------------- *)

(* The boot zero cfg byte makes the address-match-type OFF (pure compute). *)
Lemma pmpcfg_zero_off :
  pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A (zeros' 8)) = OFF.
Proof. vm_compute. reflexivity. Qed.

Lemma run_pmpcfg_all_off (s : mstate) :
  (forall i, vec_access_dec (register_lookup pmpcfg_n s.(sregs)) i = zeros' 8) ->
  forall i, pmpAddrMatchType_encdec_backwards
              (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) i))
            = OFF.
Proof. intros H i. rewrite H. exact pmpcfg_zero_off. Qed.

(* ---------------------------------------------------------------------- *)
(* Task 2: a concrete executable RAM region (base 0x80000000, size         *)
(* 0x10000000).  matching_pma_region [ramRegion] addr 4 reduces to         *)
(*   if range_subset .. then Some ramRegion else None,                     *)
(* so given the range_subset geometric fact it yields Some ramRegion;      *)
(* PMA_executable is true by construction (override_PMA keeps it).         *)
(* ---------------------------------------------------------------------- *)

Definition ramRegion : PMA_Region :=
  {| PMA_Region_base := to_bits 64 2147483648;   (* 0x80000000 *)
     PMA_Region_size := to_bits 64 268435456;    (* 0x10000000 *)
     PMA_Region_attributes :=
       {| PMA_mem_type := MainMemory;
          PMA_cacheable := true;
          PMA_coherent := true;
          PMA_executable := true;
          PMA_readable := true;
          PMA_writable := true;
          PMA_read_idempotent := true;
          PMA_write_idempotent := true;
          PMA_misaligned_exceptions :=
            {| PMAMisalignedExceptions_load_store := None;
               PMAMisalignedExceptions_vector := None;
               PMAMisalignedExceptions_amo := AccessFault |};
          PMA_atomic_support := AMOArithmetic;
          PMA_reservability := RsrvEventual;
          PMA_supports_cbo_zero := true;
          PMA_supports_pte_read := true;
          PMA_supports_pte_write := true |};
     PMA_Region_include_in_device_tree := false |}.


(* matching_pma_region for the single-region list, given range_subset. *)
Lemma run_pma_match_ram (addr : mword 64) s :
  register_lookup pma_regions s.(sregs) = [ramRegion] ->
  range_subset (zero_extend' 64 (bits_of_physaddr (Physaddr addr))) (to_bits 64 4)
               (PMA_Region_base ramRegion) (PMA_Region_size ramRegion) = true ->
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) 4
    = Some ramRegion.
Proof.
  intros Hreg Hrs. rewrite Hreg.
  unfold matching_pma_region. cbn [matching_pma_region_bits_range].
  rewrite Hrs. reflexivity.
Qed.

(* ===== RiscvModelFinal ===== *)
(* ====================================================================== *)
(* RiscvModelFinal.v                                                       *)
(*                                                                         *)
(* The CONDITIONED Hne: exec (run_hart_active 0) s <> None, assembled from  *)
(* the proven leaf exec-facts via exec_hart_active_progress.  Unlike        *)
(* wp_add_real_closed'' 's `Hne_gen` (the UNCONDITIONAL `forall s, exec     *)
(* (run_hart_active 0) s <> None`, which is over-strong / unsatisfiable for *)
(* arbitrary s), this carries the boot-config preconditions explicitly.     *)
(* ====================================================================== *)


Local Open Scope Z_scope.

Section HneClosed.
  Context (s : mstate) (pc : mword 64) (w : mword 32)
          (rs1 rs2 rd : mword 5) (cES : bool).

  (* GPR indices = a0/a1/a2. *)
  Hypothesis Hrs1 : uint rs1 = 10.
  Hypothesis Hrs2 : uint rs2 = 11.
  Hypothesis Hrd  : uint rd  = 12.

  (* booting-Machine register state. *)
  Hypothesis Hpriv : register_lookup cur_privilege s.(sregs) = Machine.
  Hypothesis HpcS  : register_lookup (R_bitvector_64 PC) s.(sregs) = pc.
  Hypothesis HecES : exec (currentlyEnabled Ext_S) s = Some (cES, s).
  Hypothesis Hmideleg :
    register_lookup (R_bitvector_64 mideleg) s.(sregs) = zeros' 64.
  Hypothesis HmIE :
    eq_vec (_get_Mstatus_MIE
              (register_lookup (R_bitvector_64 mstatus) s.(sregs)))
           ('b"1" : mword 1) = false.

  (* fetch leaf, carried as the (proven, via exec_fetch_done) fetch exec-fact. *)
  Hypothesis Hfetch : exec (fetch tt) s = Some (F_Base w, s).

  (* the decode wall: the bytes at the PC decode to `add a2,a0,a1`. *)
  Hypothesis Hdec :
    exec (ext_decode w) s
      = Some (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, ADD), s).

  (* landing-pad: elp <> EXPECTED (Zicfilp off at boot). *)
  Hypothesis Hlpad :
    eq_vec (register_lookup elp s.(sregs))
           (landing_pad_bits_backwards LP_EXPECTED) = false.

  (* dispatchInterrupt leaf, via the getPendingSet keystone. *)
  Let Hdisp : exec (dispatchInterrupt Machine) s = Some (None, s) :=
    exec_dispatchInterrupt_none s
      (exec_getPendingSet_machine_none s cES HecES Hmideleg HmIE).

  (* the execute leaf at s_pc := set_reg s nextPC (pc+4). *)
  Let Hexec :
    exec (execute (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, ADD)))
         (set_reg s nextPC (add_vec_int pc 4))
    = Some (RETIRE_SUCCESS,
            set_reg (set_reg s nextPC (add_vec_int pc 4)) (R_bitvector_64 x12)
              (regval_into_reg
                 (add_vec
                    (register_lookup (R_bitvector_64 x10)
                                     (set_reg s nextPC (add_vec_int pc 4)).(sregs))
                    (register_lookup (R_bitvector_64 x11)
                                     (set_reg s nextPC (add_vec_int pc 4)).(sregs))))).
  Proof.
    change (execute (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, ADD)))
      with (execute_RTYPE (Regidx rs2) (Regidx rs1) (Regidx rd) ADD).
    exact (exec_execute_ADD rd rs1 rs2 _ Hrs1 Hrs2 Hrd).
  Defined.

  (* the conditioned Hne. *)
  Lemma exec_hart_active_done :
    exec (run_hart_active 0) s <> None.
  Proof using All.
    erewrite (exec_hart_active_progress s s _ s w _ pc RETIRE_SUCCESS
                Hpriv Hdisp Hfetch Hdec Hlpad ltac:(reflexivity) HpcS Hexec
                ltac:(now unfold RETIRE_SUCCESS)).
    discriminate.
  Qed.

End HneClosed.

(* ===== RiscvModelFinalWP ===== *)
(* ====================================================================== *)
(* RiscvModelFinalWP.v                                                     *)
(*                                                                         *)
(* THE capstone: wp_add_real_final -- an Iris WP for `add a2,a0,a1` through *)
(* the real Sail try_step, with Hne DISCHARGED at the quantified state via *)
(* exec_hart_active_done (NOT the over-strong unconditional Hne_gen).       *)
(* Remaining genuine assumptions: Hdec (decode wall) + reducible geometric. *)
(* ====================================================================== *)



Local Open Scope Z_scope.

(* ---------------------------------------------------------------------- *)
(* Step 1: exec_currentlyEnabled_S -- exec twin of run_currentlyEnabled_S. *)
(* Supplies HecES for exec_hart_active_done.                               *)
(* ---------------------------------------------------------------------- *)

Lemma exec_hartSupports_S s : exec (hartSupports Ext_S) s = Some (true, s).
Proof.
  unfold hartSupports. destruct (Defs.Zwf_guarded _).
  cbn [_rec_hartSupports]. unfold Defs.assert_exp'.
  replace (Z.geb (hartSupports_measure Ext_S) 0) with true by reflexivity.
  cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM eq_refl s)).
  apply exec_returnM.
Qed.

Lemma exec_hartSupports_Zicsr s : exec (hartSupports Ext_Zicsr) s = Some (true, s).
Proof.
  unfold hartSupports. destruct (Defs.Zwf_guarded _).
  cbn [_rec_hartSupports]. unfold Defs.assert_exp'.
  replace (Z.geb (hartSupports_measure Ext_Zicsr) 0) with true by reflexivity.
  cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM eq_refl s)).
  apply exec_returnM.
Qed.

Lemma exec_rec_cE_Zicsr s (acc : Acc (Zwf 0) 0) :
  exec (_rec_currentlyEnabled Ext_Zicsr 0 acc) s = Some (true, s).
Proof.
  destruct acc. cbn [_rec_currentlyEnabled]. unfold Defs.assert_exp'.
  replace (Z.geb 0 0) with true by reflexivity. cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM eq_refl s)). cbn match.
  apply exec_hartSupports_Zicsr.
Qed.

Lemma exec_currentlyEnabled_S s :
  exec (currentlyEnabled Ext_S) s
    = Some (eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1"), s).
Proof.
  unfold currentlyEnabled. destruct (Defs.Zwf_guarded _).
  cbn [_rec_currentlyEnabled]. unfold Defs.assert_exp'.
  replace (Z.geb (currentlyEnabled_measure Ext_S) 0) with true by reflexivity.
  cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM eq_refl s)). cbn match.
  (* outer and_boolM (hartSupports Ext_S = true) INNER *)
  rewrite (exec_and_boolM_Some _ _ _ _ _ (exec_hartSupports_S s)).
  (* INNER = and_boolM (read misa; misa.S check) (cE Ext_Zicsr) *)
  rewrite (exec_and_boolM_Some _ _ s
             (eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1")) s).
  2:{ rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg misa s)). apply exec_returnM. }
  destruct (eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1")) eqn:Hb.
  - apply exec_rec_cE_Zicsr.
  - reflexivity.
Qed.

(* ---------------------------------------------------------------------- *)
(* Step 2: the capstone WP, with Hne DERIVED via exec_hart_active_done.    *)
(* ---------------------------------------------------------------------- *)

Ltac trans_mi := rewrite irrelevant_register_set; [ | vm_compute; reflexivity ].

Section FinalWP.
  Context `{!riscvGS Σ}.
  Context (b : bool) (pc a0 a1 mst0 npc v2old : mword 64) (mi0 : bool)
          (w : mword 32) (rs2 rs1 rd : mword 5).

  Definition sA (s : mstate) : mstate := set_reg s (R_bool minstret_increment) b.
  Definition sX (s : mstate) : mstate :=
    let s1 := set_reg (sA s) nextPC (add_vec_int pc 4) in
    set_reg s1 (R_bitvector_64 x12)
       (regval_into_reg
          (add_vec (register_lookup (R_bitvector_64 x10) s1.(sregs))
                   (register_lookup (R_bitvector_64 x11) s1.(sregs)))).
  Definition sT (s : mstate) : mstate :=
    set_reg (sX s) PC (register_lookup nextPC (sX s).(sregs)).
  Definition sF (s : mstate) : mstate :=
    if b then set_reg (sT s) minstret
                      (add_vec_int (register_lookup minstret (sT s).(sregs)) 1)
         else sT s.

  (* fetch/decode facts, stated once at the EXEC level; the relational [run]
     twins needed by run_hart_active_ADD are derived on the spot via
     [exec_run_det] (exec = Some -> run), so no separate run hypotheses. *)
  Hypothesis Hfetch_exec_gen : forall s : mstate,
    register_lookup PC s.(sregs) = pc ->
    register_lookup cur_privilege s.(sregs) = Machine ->
    exec (fetch tt) s = Some (F_Base w, s).
  Hypothesis Hdec_exec_gen : forall s : mstate,
    exec (ext_decode w) s = Some (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, ADD), s).
  Hypothesis Hsi_gen : forall s : mstate,
    register_lookup cur_privilege s.(sregs) = Machine ->
    exec (should_inc_minstret Machine) s = Some (b, s).
  Hypothesis Hrs1 : uint rs1 = 10.
  Hypothesis Hrs2 : uint rs2 = 11.
  Hypothesis Hrd  : uint rd  = 12.
  Hypothesis Hrvfi : get_config_rvfi tt = false.

  Lemma forward_exec_final (s : mstate) :
    register_lookup (R_bitvector_64 x10) s.(sregs) = a0 ->
    register_lookup (R_bitvector_64 x11) s.(sregs) = a1 ->
    register_lookup PC s.(sregs) = pc ->
    register_lookup minstret s.(sregs) = mst0 ->
    register_lookup cur_privilege s.(sregs) = Machine ->
    register_lookup hart_state s.(sregs) = HART_ACTIVE tt ->
    register_lookup (R_bitvector_64 mideleg) s.(sregs) = zeros' 64 ->
    eq_vec (_get_Mstatus_MIE (register_lookup (R_bitvector_64 mstatus) s.(sregs)))
           ('b"1") = false ->
    eq_vec (register_lookup elp s.(sregs)) (landing_pad_bits_backwards LP_EXPECTED) = false ->
    exec riscv_step s = Some (tt, sF s).
  Proof using All.
    intros Lx10 Lx11 Lpc Lmst Lpriv Lhs Lmideleg LmIE Lelp.
    (* Hne at sA s via exec_hart_active_done. *)
    assert (Hne_at : exec (run_hart_active 0) (sA s) <> None).
    { apply (exec_hart_active_done (sA s) pc w rs1 rs2 rd
               (eq_vec (_get_Misa_S (register_lookup misa (sA s).(sregs))) ('b"1"))).
      - exact Hrs1.
      - exact Hrs2.
      - exact Hrd.
      - unfold sA; trans_mi; exact Lpriv.
      - unfold sA; trans_mi; exact Lpc.
      - apply exec_currentlyEnabled_S.
      - unfold sA; trans_mi; exact Lmideleg.
      - unfold sA; trans_mi; exact LmIE.
      - apply Hfetch_exec_gen; [ unfold sA; trans_mi; exact Lpc | unfold sA; trans_mi; exact Lpriv ].
      - apply Hdec_exec_gen.
      - unfold sA; trans_mi; exact Lelp. }
    (* Hpend at sA s via the keystone. *)
    assert (HpendA : run (getPendingSet Machine) (sA s) None (sA s)).
    { apply (run_getPendingSet_machine_none (sA s) _ (run_currentlyEnabled_S (sA s))).
      - unfold sA. trans_mi. exact Lmideleg.
      - unfold sA. trans_mi. exact LmIE. }
    (* Hha at sA s via exec_hart_active_ADD, with Hne supplied by exec_hart_active_done. *)
    assert (Hha : exec (run_hart_active 0) (sA s)
                  = Some (Step_Execute (RETIRE_SUCCESS, zero_extend' 32 w), sX s)).
    { unfold sX.
      apply (exec_hart_active_ADD (sA s) w pc rs2 rs1 rd); try assumption.
      - unfold sA; trans_mi; exact Lpriv.
      - unfold sA; trans_mi; exact Lpc.
      - unfold sA; trans_mi; exact Lelp.
      - apply (proj1 (exec_run_det _ _ _ _
                 (Hfetch_exec_gen (sA s)
                    ltac:(unfold sA; trans_mi; exact Lpc)
                    ltac:(unfold sA; trans_mi; exact Lpriv)))).
      - apply (proj1 (exec_run_det _ _ _ _ (Hdec_exec_gen (sA s)))). }
    apply (exec_riscv_step_ADD s (sX s) w b pc).
    - exact Lpriv.
    - apply Hsi_gen; exact Lpriv.
    - unfold sA; trans_mi; exact Lhs.
    - exact Hha.
    - unfold sX, sA. trans_mi. trans_mi. trans_mi. exact Lhs.
    - unfold sX, sA. trans_mi. trans_mi. rewrite register_lookup_set. reflexivity.
    - exact Hrvfi.
  Qed.

  Definition mst_final : mword 64 := if b then add_vec_int mst0 1 else mst0.

  Definition base_upd (s : mstate) : mstate :=
    set_reg
      (set_reg
        (set_reg
          (set_reg s (R_bool minstret_increment) b)
          nextPC (add_vec_int pc 4))
        (R_bitvector_64 x12) (add_vec a0 a1))
      PC (add_vec_int pc 4).

  Definition sFc (s : mstate) : mstate :=
    if b then set_reg (base_upd s) minstret (add_vec_int mst0 1) else base_upd s.

  Ltac tmiss := rewrite irrelevant_register_set; [ | vm_compute; reflexivity ].

  Lemma sF_eq (s : mstate) :
    register_lookup (R_bitvector_64 x10) s.(sregs) = a0 ->
    register_lookup (R_bitvector_64 x11) s.(sregs) = a1 ->
    register_lookup minstret s.(sregs) = mst0 ->
    sF s = sFc s.
  Proof using All.
    intros Lx10 Lx11 Lmst.
    assert (E10 : register_lookup (R_bitvector_64 x10)
                    (set_reg (sA s) nextPC (add_vec_int pc 4)).(sregs) = a0).
    { unfold sA, set_reg; cbn [sregs]. tmiss. tmiss. exact Lx10. }
    assert (E11 : register_lookup (R_bitvector_64 x11)
                    (set_reg (sA s) nextPC (add_vec_int pc 4)).(sregs) = a1).
    { unfold sA, set_reg; cbn [sregs]. tmiss. tmiss. exact Lx11. }
    assert (Enpc : register_lookup nextPC (sX s).(sregs) = add_vec_int pc 4).
    { unfold sX; cbv zeta. unfold sA, set_reg; cbn [sregs]. tmiss.
      rewrite register_lookup_set. reflexivity. }
    assert (HsT : sT s = base_upd s).
    { unfold sT. rewrite Enpc. unfold sX; cbv zeta. rewrite E10 E11.
      unfold regval_into_reg, base_upd, sA. reflexivity. }
    unfold sF, sFc. rewrite HsT. destruct b; [ | reflexivity ].
    assert (Emst : register_lookup minstret (base_upd s).(sregs) = mst0).
    { unfold base_upd, sA, set_reg; cbn [sregs]. tmiss. tmiss. tmiss. tmiss. exact Lmst. }
    rewrite Emst. reflexivity.
  Qed.

  Lemma wp_add_real_final
      (mstatus0 : mword 64) (elp0 : mword 1) E (Φ : mval -> iProp Σ) :
    eq_vec (_get_Mstatus_MIE mstatus0) ('b"1") = false ->
    eq_vec elp0 (landing_pad_bits_backwards LP_EXPECTED) = false ->
    (R_bitvector_64 x10) ↦ᵣ a0 -∗
    (R_bitvector_64 x11) ↦ᵣ a1 -∗
    (R_bitvector_64 x12) ↦ᵣ v2old -∗
    PC ↦ᵣ pc -∗
    nextPC ↦ᵣ npc -∗
    (R_bool minstret_increment) ↦ᵣ mi0 -∗
    minstret ↦ᵣ mst0 -∗
    cur_privilege ↦ᵣ Machine -∗
    hart_state ↦ᵣ HART_ACTIVE tt -∗
    (R_bitvector_64 mideleg) ↦ᵣ zeros' 64 -∗
    (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
    elp ↦ᵣ elp0 -∗
    ▷ ( (R_bitvector_64 x10) ↦ᵣ a0 -∗
        (R_bitvector_64 x11) ↦ᵣ a1 -∗
        (R_bitvector_64 x12) ↦ᵣ (add_vec a0 a1) -∗
        PC ↦ᵣ (add_vec_int pc 4) -∗
        nextPC ↦ᵣ (add_vec_int pc 4) -∗
        (R_bool minstret_increment) ↦ᵣ b -∗
        minstret ↦ᵣ mst_final -∗
        cur_privilege ↦ᵣ Machine -∗
        hart_state ↦ᵣ HART_ACTIVE tt -∗
        (R_bitvector_64 mideleg) ↦ᵣ zeros' 64 -∗
        (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
        elp ↦ᵣ elp0 -∗
        WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof using All.
    iIntros (HmIE0 Help0)
      "Hx10 Hx11 Hx12 Hpc Hnpc Hmi Hmst Hpriv Hhs Hmdl Hmst' Help Hcont".
    iApply wp_exec_step.
    iIntros (s ns κs nt) "[Hreg Hmem]".
    iDestruct (reg_valid with "Hreg Hx10")  as %Lx10.
    iDestruct (reg_valid with "Hreg Hx11")  as %Lx11.
    iDestruct (reg_valid with "Hreg Hpc")   as %Lpc.
    iDestruct (reg_valid with "Hreg Hmst")  as %Lmst.
    iDestruct (reg_valid with "Hreg Hpriv") as %Lpriv.
    iDestruct (reg_valid with "Hreg Hhs")   as %Lhs.
    iDestruct (reg_valid with "Hreg Hmdl")  as %Lmdl.
    iDestruct (reg_valid with "Hreg Hmst'") as %Lmst2.
    iDestruct (reg_valid with "Hreg Help")  as %Lelp.
    iApply fupd_mask_intro; [set_solver|]. iIntros "Hclose".
    iExists (sFc s). iSplitR.
    { iPureIntro. rewrite <- (sF_eq s Lx10 Lx11 Lmst).
      apply forward_exec_final; try assumption.
      - rewrite Lmst2. exact HmIE0.
      - rewrite Lelp. exact Help0. }
    iIntros "!>".
    iMod (reg_update _ (R_bool minstret_increment) _ b with "Hreg Hmi")  as "[Hreg Hmi]".
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iMod (reg_update _ (R_bitvector_64 x12) _ (add_vec a0 a1) with "Hreg Hx12") as "[Hreg Hx12]".
    iMod (reg_update _ PC _ (add_vec_int pc 4) with "Hreg Hpc") as "[Hreg Hpc]".
    unfold sFc, base_upd, mst_final.
    destruct b.
    - iMod (reg_update _ minstret _ (add_vec_int mst0 1) with "Hreg Hmst") as "[Hreg Hmst]".
      iMod "Hclose" as "_". iModIntro.
      unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iApply ("Hcont" with "Hx10 Hx11 Hx12 Hpc Hnpc Hmi Hmst Hpriv Hhs Hmdl Hmst' Help").
    - iMod "Hclose" as "_". iModIntro.
      unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iApply ("Hcont" with "Hx10 Hx11 Hx12 Hpc Hnpc Hmi Hmst Hpriv Hhs Hmdl Hmst' Help").
  Qed.

End FinalWP.

