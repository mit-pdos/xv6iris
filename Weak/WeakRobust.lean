/-
Weak: **the violation pattern and the Layer-1 robustness goal** (M6 W2, slice 1).

Rocq: `iris/WeakRobust.v` @ xxvzwolszwmp (1cc222280).

The Rocq header, in substance (`claude-notes/projects/weak-memory-m6.md`, stage W2): the
vocabulary of the robustness theorem — the store classification, the violation predicate
(decision D-M6-2: a STATE predicate), and the Layer-1 goal statement over the W1 artifacts
(`WeakPromise` behaviors on one side, `wpPfRun` runs on the other).

PARAMETERS, NOT PLUMBING: Layer 1 takes the classification `cls : Wmsg → StoreClass` and the
publication predicate `pub` as parameters with stated properties; the Iris side (W3, D-M6-6)
instantiates `cls` from the message's access kind and `pub` from the storing agent's inert
watermark.  Nothing here depends on that representation.

THE OBSERVATION FLOOR IS `coh`.  A foreign agent that reads byte `a` at timestamp `t` raises its
`coh` floor for `a` to at least `t` (`loadPostAt` joins the RAW timestamp into `coh`, forwarding
notwithstanding), and a foreign write raises it likewise — while a plain read raises neither
`wVrNew` nor `wVwNew`.  So "some foreign `coh` floor reached the message" is the tightest per-byte
state witness of "some foreign agent observed the message".

THE VIOLATION IS HART-RESTRICTED where it is CONSUMED.  `violation` quantifies author and
observer over all agents; φ speaks only about harts, and with the DMA-tid unification the disk is
an ordinary agent, so the unrestricted form is refutable for xv6 (see `violationHart`).
`violationHart nh` / `pfViolationFreeHart nh` are the forms `WeakRobustMain`'s exhibit produces.

Slice 1: definitions + the goal statement + the cheap sanity lemmas.  W2a (the dependency graph
and its acyclicity) and W2b (the π-permuted simulation) build on top, in follow-up files.

**Deviations from Rocq.**

1. NAMES: as `Weak/WeakMem.lean` deviation 1.  Types UpperCamelCase (`store_class` ↦
   `StoreClass`); constructors keep their Rocq spelling (`SCowned`, `SCfenced`, `SCexcl`).  The
   Rocq instance `store_class_eq_dec` is a `deriving DecidableEq` clause.
2. VOCABULARY: as `WeakPromise` deviation 2; `is_Some o` ↦ `o.isSome`, `S p` ↦ `p + 1`,
   `pa_st <$> pc_ags c` ↦ `c.pcAgs.map Wpagent.paSt`, `bv 8` ↦ `BitVec 8`, `Z` ↦ `Int`.
3. The section variables (`cls`, `pub`; `pstep`, `pcls`) are explicit arguments of the
   declarations that use them, in Rocq's order.
4. O2: nothing changes here.  `robust` quantifies over every program LTS, fetching ones included
   (`LIFetch` steps are ordinary `wpPfStep`/`wpstep` arms); `latFreeProg` is unaffected.

**Rocq → Lean name map.**  `store_class` ↦ `StoreClass`; `obs_flr` ↦ `obsFlr`; `violation` ↦
`violation`; `violation_hart` ↦ `violationHart`; `violation_hart_violation` ↦
`violationHartViolation`; `pf_violation_free` ↦ `pfViolationFree`; `pf_violation_free_hart` ↦
`pfViolationFreeHart`; `pf_violation_free_hart_weaken` ↦ `pfViolationFreeHartWeaken`;
`violation_init` ↦ `violationInit`; `mem_of` ↦ `memOf`; `prog_of` ↦ `progOf`; `robust` ↦
`robust`.

**Not ported:** nothing — every Rocq definition and lemma has a Lean twin.

**Statements checked** (by hand, against Rocq): all of them.
-/
import Weak.WeakPromiseBridge

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std

/-! ## The classification -/

/-- The three store classes of the Layer-2 enumeration: `SCowned` — the storing agent
exclusively owns the bytes until publication; `SCfenced` — an enumerated release-fenced sync
site; `SCexcl` — the exclusive-conditional (walker A/D CAS) class. -/
inductive StoreClass where
  | SCowned
  | SCfenced
  | SCexcl
  deriving DecidableEq

/-! ## The violation predicate -/

section violation

variable {P D : Type}

/-- The per-byte observation floor of agent `j` in configuration `c`: its coherence floor. -/
def obsFlr (c : Wpcfg P D) (j : Nat) (a : Int) : Nat :=
  match c.pcAgs[j]? with
  | some ag => coh ag.paWs a
  | none => 0

variable (cls : Wmsg → StoreClass)
/- Publication: `pub c ts` — the message at timestamp `ts` has been published.  Layer 1 needs
only MONOTONICITY along runs, required where used (W2a). -/
variable (pub : Wpcfg P D → Nat → Prop)

/-- The violation (D-M6-2): an owned, unpublished message some FOREIGN agent's floor has
reached.  `ts = p + 1` for log position `p`, as everywhere in `WeakMem`. -/
def violation (c : Wpcfg P D) : Prop :=
  ∃ (p : Nat) (m : Wmsg) (i j : Nat) (a : Int),
    c.pcLog[p]? = some m ∧ m.wmTid = some i ∧
    cls m = .SCowned ∧ ¬ pub c (p + 1) ∧
    j ≠ i ∧ (msgByte m a).isSome ∧
    p + 1 ≤ obsFlr c j a

/-- THE HART-RESTRICTED VIOLATION, the one every CONSUMER takes: both the AUTHOR `i` and the
OBSERVER `j` are harts (`tidHart nh`).  The restriction is not optional: for xv6 the
unrestricted `pfViolationFree` is REFUTABLE through the virtio DMA agent (see the Rocq
comment); both witnesses disappear under the hart restriction. -/
def violationHart (nh : Nat) (c : Wpcfg P D) : Prop :=
  ∃ (p : Nat) (m : Wmsg) (i j : Nat) (a : Int),
    c.pcLog[p]? = some m ∧ m.wmTid = some i ∧ tidHart nh m.wmTid ∧
    cls m = .SCowned ∧ ¬ pub c (p + 1) ∧
    j ≠ i ∧ tidHart nh (some j) ∧ (msgByte m a).isSome ∧
    p + 1 ≤ obsFlr c j a

theorem violationHartViolation (nh : Nat) (c : Wpcfg P D) :
    violationHart cls pub nh c → violation cls pub c := by
  rintro ⟨p, m, i, j, a, h1, h2, _, h3, h4, h5, _, h6, h7⟩
  exact ⟨p, m, i, j, a, h1, h2, h3, h4, h5, h6, h7⟩

/-- The Layer-2 premise, as Layer 1 consumes it: no promise-free run of the program reaches a
violating configuration (the UNRESTRICTED form). -/
def pfViolationFree (pstep : P → D → Wlabel → P → D → Prop)
    (pcls : P → Wlabel → Wstate → WmClass) (img : Image) (d0 : D) (ps : List P) : Prop :=
  ∀ c, rtc (wpPfRun pstep pcls) (wpInit img d0 ps) c → ¬ violation cls pub c

/-- The hart-restricted form `WeakRobustMain` and `WeakCompose` actually consume. -/
def pfViolationFreeHart (nh : Nat) (pstep : P → D → Wlabel → P → D → Prop)
    (pcls : P → Wlabel → Wstate → WmClass) (img : Image) (d0 : D) (ps : List P) : Prop :=
  ∀ c, rtc (wpPfRun pstep pcls) (wpInit img d0 ps) c → ¬ violationHart cls pub nh c

theorem pfViolationFreeHartWeaken (nh : Nat) (pstep : P → D → Wlabel → P → D → Prop)
    (pcls : P → Wlabel → Wstate → WmClass) (img : Image) (d0 : D) (ps : List P) :
    pfViolationFree cls pub pstep pcls img d0 ps →
    pfViolationFreeHart cls pub nh pstep pcls img d0 ps :=
  fun h c hrun hv => h c hrun (violationHartViolation cls pub nh c hv)

/-- Sanity: the initial configuration violates nothing (empty log). -/
theorem violationInit (img : Image) (d0 : D) (ps : List P) :
    ¬ violation cls pub (wpInit (P := P) (D := D) img d0 ps) := by
  rintro ⟨p, m, _, _, _, hm, _⟩
  simp [wpInit] at hm

end violation

/-! ## Observables -/

/-- The flat memory a configuration's log denotes: byte `a` is the value of the LATEST write to
`a` (timestamp 0 = the era-initial image). -/
def memOf {P D : Type} (c : Wpcfg P D) (a : Int) : Option (BitVec 8) :=
  logByte c.pcImg c.pcLog (latestTs c.pcLog a) a

/-- The per-agent program observables. -/
def progOf {P D : Type} (c : Wpcfg P D) : List P := c.pcAgs.map Wpagent.paSt

/-! ## The Layer-1 goal -/

section goal

variable {P D : Type} (pstep : P → D → Wlabel → P → D → Prop)
variable (pcls : P → Wlabel → Wstate → WmClass)
variable (cls : Wmsg → StoreClass)
variable (pub : Wpcfg P D → Nat → Prop)

/-- THE ROBUSTNESS GOAL (the theorem W2a+W2b prove): for a lat-free program whose promise-free
runs never violate, every full-machine BEHAVIOR is matched by a promise-free run with the same
per-agent program states and the same flat memory.  It deliberately does NOT say: equal logs
(the pf log is a permutation π of the behavior's), equal views, or anything about incomplete
prefixes. -/
def robust : Prop :=
  ∀ (img : Image) (d0 : D) (ps : List P) (c : Wpcfg P D),
    latFreeProg pstep →
    pfViolationFree cls pub pstep pcls img d0 ps →
    wpBehavior pstep img d0 ps c →
    ∃ c', rtc (wpPfRun pstep pcls) (wpInit img d0 ps) c' ∧
      progOf c' = progOf c ∧
      (∀ a : Int, memOf c' a = memOf c a)

end goal

end Weak
