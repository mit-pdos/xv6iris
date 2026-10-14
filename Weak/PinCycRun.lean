/-
Weak: **W9a (B) B5 — `cycRun` from `hartConf`, part 1: THE CYCLE PREDICATE `cyB` and its run
soundness** (plan `notes/weak-allocproc-plan.md` rev 52 §C "W9a (B)" (B5); [OWN.85]
Q-B5-CYCLE = C1; report `PROGRESS-cycRun.md`).  Lean-only, no Rocq twin.

`PinCycRun.cyB A Aa S T P m st` is an all-paths predicate on a Sail tree `m` that follows the hart's
OWN step (`WeakEvInst.pnodeStep`) along every path of `m`, with a MIRROR of the hart's register
file (`st.rv`) and B1's dataflow bookkeeping (`st.d`, `PinDataflow.dfB`'s state):
* a register read is answered by the mirror (`st.rv r`) — except the two PLIC wire registers
  `sig_meip`/`sig_seip`, which the PLIC writes BETWEEN the hart's nodes (`pstepPlic`), answered
  by every value; the read set grows (`dfRd`);
* a write to a STOP register (`S r = true`; in the instance the trap handler's cause registers
  `scause`/`mcause`, the first write of every trap, `SysControl.lean:751,769`) ENDS the
  obligation with the stop post `T st r v`; any other write writes an `Rboot`-admitted value,
  updates the mirror and moves the slots (`dfWr`);
* a RAM instruction-fetch read is answered by every value whose bytes the FETCH FILTER `A`
  admits, and is LOGGED (`st.fe`: physical address, bytes, in order); every other read by every
  successful answer `.Ok (w, none)` (the only answers a hart step gives, `pnodeStep`);
* the ANNOUNCE — at most one (`st.an`) — sets the decoded role and empties the read set
  (`dfAnn`, the emission's `ibAnn`);
* every other node continues for every answer; a failure is stuck (`True`); at `.pure x`, `P`.

**Run soundness** (§3): along a run of real `pstepEv` steps of the hart (Sail nodes, parked
fences, PLIC wire writes) from a tree satisfying `cyB` at a state MATCHED to the hart
(`cyMatch`: the mirror agrees off the wires, the channel `Ibch` is the dataflow state's), with
every fetch read's bytes `A`-admitted, either the run reaches a STOP node with the stop post
(`cyRunStop`), or it reaches the end of the cycle (`.pure`) with the post (`cyRunEnd`), or it
ends inside the cycle still under `cyB` (`cyRunMid`); in each case the fetch log is the run's
`LIFetch` items (`feLab`, `feLabs`) and the slots are B1's scan of the run's labels at the role the cycle
ends with (`dfScan`).

Spec: Sail is the reference for the tree (`Step.lean`, `SysControl.lean`); the predicate is
proof organisation.  Every Lean-only helper is `Weak.PinCycRun.*`.
-/
import Weak.PinDataflowGlue

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Sail Sail.ConcurrencyInterfaceV1 LeanRV64D LeanRV64D.Functions
open Sail.ArchSem (FreeM)
open Wlabel

namespace PinCycRun
open SailCycleOrderK PinDataflow

/-! ## 1. The state and the predicate -/

/-- One logged instruction-fetch read: physical address, width, value. -/
structure FeEnt where
  a : Int
  n : Nat
  w : BitVec (8 * n)

/-- The tracked state of one cycle: the register mirror, the fetch log, whether the instruction
was announced, B1's dataflow state. -/
structure CySt where
  rv : RegFile
  fe : List FeEnt
  an : Bool
  d : DfSt

/-- The PLIC wire registers (written by the PLIC between the hart's own nodes). -/
def wireReg (r : Register) : Bool := decide (r = .sig_meip) || decide (r = .sig_seip)

/-- A register read's answer: the mirror's value, or anything at a wire. -/
def rdOk (st : CySt) (r : Register) (v : RegisterType r) : Prop :=
  wireReg r = false → v = st.rv r

def cyRd (st : CySt) (r : Register) : CySt := { st with d := dfRd st.d r }

def cyWr (st : CySt) (r : Register) (v : RegisterType r) : CySt :=
  { st with rv := st.rv.set r v, d := dfWr st.d r }

def cyFe (st : CySt) (a : Int) (n : Nat) (w : BitVec (8 * n)) : CySt :=
  { st with fe := st.fe ++ [⟨a, n, w⟩] }

def cyAnn (st : CySt) (n : Nat) (w : BitVec n) : CySt :=
  { st with an := true, d := dfAnn st.d n w }

/-- **THE CYCLE PREDICATE** (header). -/
def cyB {X : Type} (A : Int → BitVec 8 → Prop) (Aa : Nat → Int → Prop) (S : Register → Bool)
    (T : CySt → (r : Register) → RegisterType r → Prop) (P : X → CySt → Prop) :
    SailM X → CySt → Prop
  | .pure x, st => P x st
  | .impure (.error _) _, _ => True
  | .impure (.ok o) k, st =>
    match o, k with
    | .regRead r, k => ∀ v, rdOk st r v → cyB A Aa S T P (k v) (cyRd st r)
    | .regWrite r v, k =>
        (S r = true → T st r v) ∧
        (S r = false → Rboot r v ∧ ∀ u, cyB A Aa S T P (k u) (cyWr st r v))
    | .memRead n _ req, k =>
        (devAddr req.pa = false → (classify req.access_kind).akIfetch = true →
          Aa st.fe.length (paZ req.pa) →
          ∀ w : BitVec (8 * n), (∀ j, j < n → A (paZ req.pa + (j : Int)) (nthByte w j)) →
            cyB A Aa S T P (k (.Ok (w, none))) (cyFe st (paZ req.pa) n w)) ∧
        ((devAddr req.pa = false → (classify req.access_kind).akIfetch = false) →
          ∀ w : BitVec (8 * n), cyB A Aa S T P (k (.Ok (w, none))) st)
    | .instrAnnounce n w, k => st.an = false ∧ ∀ u, cyB A Aa S T P (k u) (cyAnn st n w)
    | .barrier _, k => ∀ v, cyB A Aa S T P (k v) st
    | .memWrite .., k => ∀ v, cyB A Aa S T P (k v) st
    | .branchAnnounce .., k => ∀ v, cyB A Aa S T P (k v) st
    | .cacheOp _, k => ∀ v, cyB A Aa S T P (k v) st
    | .tlbi _, k => ∀ v, cyB A Aa S T P (k v) st
    | .takeException _, k => ∀ v, cyB A Aa S T P (k v) st
    | .returnException _, k => ∀ v, cyB A Aa S T P (k v) st
    | .translationStart _, k => ∀ v, cyB A Aa S T P (k v) st
    | .translationEnd _, k => ∀ v, cyB A Aa S T P (k v) st
    | .cycleCount, k => ∀ v, cyB A Aa S T P (k v) st
    | .getCycleCount, k => cyB A Aa S T P (k (0 : Nat)) st
    | .message _, k => ∀ v, cyB A Aa S T P (k v) st
    | .choose _, k => ∀ v, cyB A Aa S T P (k v) st
    | .readRam .., k => ∀ v, cyB A Aa S T P (k v) st
    | .writeRam .., k => ∀ v, cyB A Aa S T P (k v) st

/-! ## 2. The bind law, monotonicity -/

section kit
variable {A : Int → BitVec 8 → Prop} {Aa : Nat → Int → Prop} {S : Register → Bool}
  {T : CySt → (r : Register) → RegisterType r → Prop}

theorem cyBBind {X Y : Type} (Q : X → CySt → Prop) (P : Y → CySt → Prop) (m : SailM X)
    (f : X → SailM Y) :
    ∀ st, cyB A Aa S T Q m st → (∀ x st', Q x st' → cyB A Aa S T P (f x) st') →
      cyB A Aa S T P (m >>= f) st := by
  induction m with
  | pure y => intro st hm hf; exact hf y st hm
  | impure call k ih =>
    intro st hm hf
    cases call with
    | error e => trivial
    | ok o =>
      show cyB A Aa S T P (FreeM.impure (.ok o) (fun v => k v >>= f)) st
      cases o
      case regRead => exact fun v hv => ih v _ (hm v hv) hf
      case regWrite => exact ⟨hm.1, fun h => ⟨(hm.2 h).1, fun u => ih u _ ((hm.2 h).2 u) hf⟩⟩
      case memRead =>
        exact ⟨fun h1 h2 ha w hw => ih _ _ (hm.1 h1 h2 ha w hw) hf, fun h w => ih _ _ (hm.2 h w) hf⟩
      case instrAnnounce => exact ⟨hm.1, fun u => ih u _ (hm.2 u) hf⟩
      case getCycleCount => exact ih _ _ hm hf
      all_goals exact fun v => ih v _ (hm v) hf

theorem cyBMono {X : Type} (P P' : X → CySt → Prop) (hP : ∀ x st, P x st → P' x st) :
    ∀ (m : SailM X) st, cyB A Aa S T P m st → cyB A Aa S T P' m st := by
  intro m
  induction m with
  | pure y => exact fun st h => hP y st h
  | impure call k ih =>
    intro st hm
    cases call with
    | error e => trivial
    | ok o =>
      cases o
      case regRead => exact fun v hv => ih v _ (hm v hv)
      case regWrite => exact ⟨hm.1, fun h => ⟨(hm.2 h).1, fun u => ih u _ ((hm.2 h).2 u)⟩⟩
      case memRead =>
        exact ⟨fun h1 h2 ha w hw => ih _ _ (hm.1 h1 h2 ha w hw), fun h w => ih _ _ (hm.2 h w)⟩
      case instrAnnounce => exact ⟨hm.1, fun u => ih u _ (hm.2 u)⟩
      case getCycleCount => exact ih _ _ hm
      all_goals exact fun v => ih v _ (hm v)

theorem cyBPure {X : Type} (P : X → CySt → Prop) (x : X) (st : CySt) :
    P x st → cyB A Aa S T P (pure x : SailM X) st := fun h => h

end kit

/-! ## 3. Run soundness -/

/-- The predicate's state MATCHES the hart: the mirror agrees off the wires, every register is
`Rboot`-admitted, the dataflow state is the hart's channel, `an` iff announced. -/
def cyMatch (st : CySt) (rs : RegFile) (ib : Ibch) : Prop :=
  (∀ r, wireReg r = false → rs r = st.rv r) ∧ RbootAll rs ∧ RbootAll st.rv ∧
  st.d.ro = depsOfIb ib.ibBits ∧ st.d.rds = ib.ibRds ∧ st.an = ib.ibBits.isSome

/-- A label is an instruction-fetch read. -/
def isFeLab (l : Wlabel) : Bool :=
  match l with
  | LIFetch .. => true
  | _ => false

/-- A log entry IS a fetch label: its address, its width, its bytes the value's. -/
def feLab (e : FeEnt) (l : Wlabel) : Prop :=
  ∃ tvs : List (Nat × BitVec 8), l = LIFetch e.a tvs ∧ tvs.length = e.n ∧
    ∀ j, j < e.n → (tvs.map Prod.snd)[j]? = some (nthByte e.w j)

/-- The fetch labels of a label list. -/
def feLabs (ls : List Wlabel) : List Wlabel := ls.filter isFeLab

/-- One step's log move: a fetch label logs one matching entry, any other label none. -/
def feStep (fe fe' : List FeEnt) (l : Wlabel) : Prop :=
  (isFeLab l = false ∧ fe' = fe) ∨ (∃ e, fe' = fe ++ [e] ∧ feLab e l)

/-- A fetch label is admitted as the `k`-th fetch read: its address by `Aa k`, every byte at its
address by `A`. -/
def feAdm (A : Int → BitVec 8 → Prop) (Aa : Nat → Int → Prop) (k : Nat) (l : Wlabel) : Prop :=
  ∀ a tvs, l = LIFetch a tvs → Aa k a ∧ ∀ j (hj : j < tvs.length), A (a + (j : Int)) (tvs[j]'hj).2

/-- The hart is at a STOP node: a write to a stop register, with the stop post. -/
def cyStopAt (S : Register → Bool) (T : CySt → (r : Register) → RegisterType r → Prop)
    (st : CySt) (m : SailM Unit) : Prop :=
  ∃ (r : Register) (v : RegisterType r) (k : Unit → SailM Unit),
    m = .impure (.ok (.regWrite r v)) k ∧ S r = true ∧ T st r v

/-- One step's conclusion off a stop: a state for the new tree, matched to the new hart state,
the log extended by the label's fetch entry, the slots moved by the label, the role kept unless
the step announced. -/
def cyStepOk (A : Int → BitVec 8 → Prop) (Aa : Nat → Int → Prop) (S : Register → Bool)
    (T : CySt → (r : Register) → RegisterType r → Prop) (P : Unit → CySt → Prop) (st : CySt)
    (l : Wlabel) (m' : SailM Unit) (ib' : Ibch) (rs' : RegFile) : Prop :=
  ∃ st', cyB A Aa S T P m' st' ∧ cyMatch st' rs' ib' ∧ feStep st.fe st'.fe l ∧
    (st'.d.n, st'.d.ok) = dfLab st.d.ro st.d.n st.d.ok l ∧
    (st.an = true → st'.d.ro = st.d.ro ∧ st'.an = true) ∧
    (st.an = false → ∀ rd srcs, l ≠ LRegW rd srcs)

/-- The mirror agrees after the same write on both sides. -/
theorem PinCycRun.agreeSet (rs rv : RegFile) (r : Register) (v : RegisterType r)
    (h : ∀ r', wireReg r' = false → rs r' = rv r') :
    ∀ r', wireReg r' = false → rs.set r v r' = rv.set r v r' := by
  intro r' hr'
  by_cases e : r' = r
  · subst e; rw [RegFile.set_same, RegFile.set_same]
  · rw [RegFile.set_other _ _ _ _ e, RegFile.set_other _ _ _ _ e]; exact h r' hr'

/-- The mirror agrees after a write on the hart side to a wire register. -/
theorem PinCycRun.agreeSetWire (rs rv : RegFile) (r : Register) (v : RegisterType r)
    (hw : wireReg r = true) (h : ∀ r', wireReg r' = false → rs r' = rv r') :
    ∀ r', wireReg r' = false → rs.set r v r' = rv r' := by
  intro r' hr'
  have e : r' ≠ r := by rintro rfl; rw [hw] at hr'; cases hr'
  rw [RegFile.set_other _ _ _ _ e]; exact h r' hr'

/-- The pre-announce channel is provenance-neutral at a node (`dfNoneNeutral` for one node). -/
theorem PinCycRun.noneNeutralNode (cpu : CPU) (m : SailM Unit) (rs : RegFile) (ib : Ibch)
    (d : Efab) (l : Wlabel) (m' : SailM Unit) (ors : Option RegFile)
    (fn' : Option (Bool × Bool × Bool × Bool)) (d' : Efab) (oib : Option Ibch)
    (obar : Option barrier_kind) (hib : ib.ibBits = none)
    (h : pnodeStep m rs ib d.efDev l m' ors fn' d'.efDev oib obar) (hd : d' = { d with efDev := d'.efDev }) :
    ∀ rd srcs, l ≠ LRegW rd srcs :=
  dfNoneNeutral cpu m rs none ib d l m' ors fn' d' oib obar hib (Or.inl ⟨h, hd⟩)

/-- The stay case of a node step (state unchanged, label not a register write). -/
theorem PinCycRun.stepStay (A : Int → BitVec 8 → Prop) (Aa : Nat → Int → Prop) (S : Register → Bool)
    (T : CySt → (r : Register) → RegisterType r → Prop) (P : Unit → CySt → Prop) (st : CySt)
    (l : Wlabel) (m' : SailM Unit) (ib : Ibch) (rs : RegFile) (hcy : cyB A Aa S T P m' st)
    (hm : cyMatch st rs ib) (hl : ∀ rd srcs, l ≠ LRegW rd srcs) (hfe : isFeLab l = false) :
    cyStepOk A Aa S T P st l m' ib rs :=
  ⟨st, hcy, hm, Or.inl ⟨hfe, rfl⟩, (dfLabNeutral _ _ _ l hl).symm,
    fun h => ⟨rfl, h⟩, fun _ => hl⟩

/-- **One Sail node** (header): a step of the hart's own node from a tree satisfying `cyB` at a
matched state either sits at a stop node, or lands on a tree satisfying `cyB` again. -/
theorem cyNodeStep (A : Int → BitVec 8 → Prop) (Aa : Nat → Int → Prop) (S : Register → Bool)
    (T : CySt → (r : Register) → RegisterType r → Prop) (P : Unit → CySt → Prop)
    (m : SailM Unit) (rs : RegFile) (ib : Ibch) (dd : DevStates) (l : Wlabel) (m' : SailM Unit)
    (ors : Option RegFile) (fn' : Option (Bool × Bool × Bool × Bool)) (dd' : DevStates)
    (oib : Option Ibch) (obar : Option barrier_kind) (st : CySt)
    (hstep : pnodeStep m rs ib dd l m' ors fn' dd' oib obar) (hpure : ∀ x, m ≠ .pure x)
    (hcy : cyB A Aa S T P m st) (hm : cyMatch st rs ib) (hA : feAdm A Aa st.fe.length l)
    (hnn : st.an = false → ∀ rd srcs, l ≠ LRegW rd srcs) :
    cyStopAt S T st m ∨ cyStepOk A Aa S T P st l m' (oib.getD ib) (ors.getD rs) := by
  obtain ⟨hag, hrb, hrbv, hro, hrds, han⟩ := hm
  match m, hstep with
  | .pure x, _ => exact absurd rfl (hpure x)
  | .impure (.error _) _, h => exact h.elim
  | .impure (.ok o) k, h =>
    cases o with
    | regRead r =>
      obtain ⟨rfl, rfl, rfl, -, -, rfl, -⟩ := h
      right
      have hv : rdOk st r (rs r) := fun hw => hag r hw
      refine ⟨cyRd st r, hcy (rs r) hv, ⟨hag, hrb, hrbv, ?_, ?_, ?_⟩, Or.inl ⟨rfl, rfl⟩,
        rfl, fun h => ⟨rfl, h⟩, fun _ _ _ e => by cases e⟩
      · show st.d.ro = depsOfIb (ibRd ib r).ibBits
        rw [ibRdBits]; exact hro
      · show dfRdsAdd st.d.rds (eregNum r) = (ibRd ib r).ibRds
        rw [hrds]; exact (dfRdsAddIb ib (eregNum r)).symm
      · show st.an = (ibRd ib r).ibBits.isSome
        rw [ibRdBits]; exact han
    | regWrite r v =>
      obtain ⟨rfl, rfl, rfl, -, -, rfl, -⟩ := h
      cases hs : S r with
      | true => exact Or.inl ⟨r, v, k, rfl, hs, hcy.1 hs⟩
      | false =>
        right
        obtain ⟨hrv, hk⟩ := hcy.2 hs
        refine ⟨cyWr st r v, hk (), ⟨PinCycRun.agreeSet rs st.rv r v hag,
          rbootAllSet rs r v hrb hrv, rbootAllSet st.rv r v hrbv hrv, hro, hrds, han⟩,
          ?_, ?_, fun h => ⟨rfl, h⟩, hnn⟩
        · refine Or.inl ⟨?_, rfl⟩
          unfold erwLabel; split <;> rfl
        · simp only [cyWr, dfWr, hro, hrds]
    | memRead n va req =>
      simp only [pnodeStep] at h
      split at h
      · rename_i hdev
        obtain ⟨w, -, rfl, rfl, rfl, -, rfl, -⟩ := h
        right
        exact PinCycRun.stepStay A Aa S T P st _ _ ib rs
          (hcy.2 (fun h' => absurd (hdev.symm.trans h') (by decide)) _)
          ⟨hag, hrb, hrbv, hro, hrds, han⟩ (fun _ _ e => by cases e) rfl
      · rename_i hdev
        have hdev' : devAddr req.pa = false := by simpa using hdev
        rcases h with ⟨hif, w, tvs, hlen, hb, rfl, rfl, rfl, -, -, rfl, -⟩ |
          ⟨hif, ⟨-, w, tvs, -, -, rfl, rfl, rfl, -, -, rfl, -⟩ |
            ⟨-, w, tvs, -, -, rfl, rfl, rfl, -, -, rfl, -⟩⟩
        · right
          have hel : ∀ j (hj : j < tvs.length), (tvs[j]'hj).2 = nthByte w j := by
            intro j hj
            have h2 := hb j (by rw [← hlen]; exact hj)
            simp only [List.getElem?_map, List.getElem?_eq_getElem hj, Option.map_some,
              Option.some.injEq] at h2
            exact h2
          have hAw : ∀ j, j < n → A (paZ req.pa + (j : Int)) (nthByte w j) := by
            intro j hj
            have hj' : j < tvs.length := by rw [hlen]; exact hj
            rw [← hel j hj']; exact (hA _ tvs rfl).2 j hj'
          exact ⟨cyFe st (paZ req.pa) n w, hcy.1 hdev' hif (hA _ tvs rfl).1 w hAw,
            ⟨hag, hrb, hrbv, hro, hrds, han⟩, Or.inr ⟨⟨paZ req.pa, n, w⟩, rfl, tvs, rfl, hlen, hb⟩,
            rfl, fun h => ⟨rfl, h⟩, fun _ _ _ e => by cases e⟩
        · right
          exact PinCycRun.stepStay A Aa S T P st _ _ ib rs (hcy.2 (fun _ => hif) _)
            ⟨hag, hrb, hrbv, hro, hrds, han⟩ (fun _ _ e => by cases e) rfl
        · right
          exact PinCycRun.stepStay A Aa S T P st _ _ ib rs (hcy.2 (fun _ => hif) _)
            ⟨hag, hrb, hrbv, hro, hrds, han⟩ (fun _ _ e => by cases e) rfl
    | memWrite n va req =>
      simp only [pnodeStep] at h
      right
      split at h
      · split at h
        · obtain ⟨-, rfl, rfl, rfl, -, rfl, -⟩ := h
          exact PinCycRun.stepStay A Aa S T P st _ _ ib rs (hcy _) ⟨hag, hrb, hrbv, hro, hrds, han⟩
            (fun _ _ e => by cases e) rfl
        · exact h.elim
      · split at h
        · obtain ⟨-, h⟩ := h
          rcases h with ⟨-, rfl, rfl, rfl, -, -, rfl, -⟩ |
            ⟨-, ⟨rfl, rfl, rfl, -, -, rfl, -⟩ | ⟨rfl, rfl, rfl, -, -, rfl, -⟩⟩
          · exact PinCycRun.stepStay A Aa S T P st _ _ ib rs (hcy _) ⟨hag, hrb, hrbv, hro, hrds, han⟩
              (fun _ _ e => by cases e) rfl
          · exact PinCycRun.stepStay A Aa S T P st _ _ ib rs (hcy _) ⟨hag, hrb, hrbv, hro, hrds, han⟩
              (fun _ _ e => by cases e) rfl
          · exact PinCycRun.stepStay A Aa S T P st _ _ ib rs hcy ⟨hag, hrb, hrbv, hro, hrds, han⟩
              (fun _ _ e => by cases e) rfl
        · exact h.elim
    | barrier b =>
      obtain ⟨rfl, rfl, rfl, -, -, rfl, -⟩ := h
      right
      refine PinCycRun.stepStay A Aa S T P st _ _ ib rs (hcy ()) ⟨hag, hrb, hrbv, hro, hrds, han⟩
        (fun _ _ e => ?_) ?_
      · unfold ebarLabel at e
        split at e <;> cases e
      · unfold ebarLabel
        split <;> rfl
    | instrAnnounce n w =>
      obtain ⟨rfl, rfl, rfl, -, -, rfl, -⟩ := h
      right
      obtain ⟨han0, hk⟩ := hcy
      have hl : ∀ rd srcs, annLabel n w ≠ LRegW rd srcs := by
        intro rd srcs e
        unfold annLabel at e
        split at e <;> cases e
      refine ⟨cyAnn st n w, hk (), ⟨hag, hrb, hrbv, rfl, rfl, rfl⟩, ?_, ?_,
        fun h => absurd (h.symm.trans han0) (by decide), fun _ => hl⟩
      · refine Or.inl ⟨?_, rfl⟩
        unfold annLabel; split <;> rfl
      · exact (dfLabNeutral _ _ _ _ hl).symm
    | choose s =>
      obtain ⟨ch, rfl, rfl, rfl, -, -, rfl, -⟩ := h
      right
      exact PinCycRun.stepStay A Aa S T P st _ _ ib rs (hcy ch) ⟨hag, hrb, hrbv, hro, hrds, han⟩
        (fun _ _ e => by cases e) rfl
    | readRam => exact h.elim
    | writeRam => exact h.elim
    | getCycleCount =>
      obtain ⟨rfl, rfl, rfl, -, -, rfl, -⟩ := h
      right
      exact PinCycRun.stepStay A Aa S T P st _ _ ib rs hcy ⟨hag, hrb, hrbv, hro, hrds, han⟩
        (fun _ _ e => by cases e) rfl
    | branchAnnounce =>
      obtain ⟨rfl, rfl, rfl, -, -, rfl, -⟩ := h
      right
      exact PinCycRun.stepStay A Aa S T P st _ _ ib rs (hcy _) ⟨hag, hrb, hrbv, hro, hrds, han⟩
        (fun _ _ e => by cases e) rfl
    | cacheOp =>
      obtain ⟨rfl, rfl, rfl, -, -, rfl, -⟩ := h
      right
      exact PinCycRun.stepStay A Aa S T P st _ _ ib rs (hcy _) ⟨hag, hrb, hrbv, hro, hrds, han⟩
        (fun _ _ e => by cases e) rfl
    | tlbi =>
      obtain ⟨rfl, rfl, rfl, -, -, rfl, -⟩ := h
      right
      exact PinCycRun.stepStay A Aa S T P st _ _ ib rs (hcy _) ⟨hag, hrb, hrbv, hro, hrds, han⟩
        (fun _ _ e => by cases e) rfl
    | takeException =>
      obtain ⟨rfl, rfl, rfl, -, -, rfl, -⟩ := h
      right
      exact PinCycRun.stepStay A Aa S T P st _ _ ib rs (hcy _) ⟨hag, hrb, hrbv, hro, hrds, han⟩
        (fun _ _ e => by cases e) rfl
    | returnException =>
      obtain ⟨rfl, rfl, rfl, -, -, rfl, -⟩ := h
      right
      exact PinCycRun.stepStay A Aa S T P st _ _ ib rs (hcy _) ⟨hag, hrb, hrbv, hro, hrds, han⟩
        (fun _ _ e => by cases e) rfl
    | translationStart =>
      obtain ⟨rfl, rfl, rfl, -, -, rfl, -⟩ := h
      right
      exact PinCycRun.stepStay A Aa S T P st _ _ ib rs (hcy _) ⟨hag, hrb, hrbv, hro, hrds, han⟩
        (fun _ _ e => by cases e) rfl
    | translationEnd =>
      obtain ⟨rfl, rfl, rfl, -, -, rfl, -⟩ := h
      right
      exact PinCycRun.stepStay A Aa S T P st _ _ ib rs (hcy _) ⟨hag, hrb, hrbv, hro, hrds, han⟩
        (fun _ _ e => by cases e) rfl
    | cycleCount =>
      obtain ⟨rfl, rfl, rfl, -, -, rfl, -⟩ := h
      right
      exact PinCycRun.stepStay A Aa S T P st _ _ ib rs (hcy _) ⟨hag, hrb, hrbv, hro, hrds, han⟩
        (fun _ _ e => by cases e) rfl
    | message =>
      obtain ⟨rfl, rfl, rfl, -, -, rfl, -⟩ := h
      right
      exact PinCycRun.stepStay A Aa S T P st _ _ ib rs (hcy _) ⟨hag, hrb, hrbv, hro, hrds, han⟩
        (fun _ _ e => by cases e) rfl

/-- **One hart step** (header): a Sail node, a parked fence firing, or a PLIC wire write. -/
theorem cyHartStep (A : Int → BitVec 8 → Prop) (Aa : Nat → Int → Prop) (S : Register → Bool)
    (T : CySt → (r : Register) → RegisterType r → Prop) (P : Unit → CySt → Prop)
    (cpu : CPU) (m : SailM Unit) (rs : RegFile) (fn : Option (Bool × Bool × Bool × Bool))
    (ib : Ibch) (d : Efab) (l : Wlabel) (m' : SailM Unit) (ors : Option RegFile)
    (fn' : Option (Bool × Bool × Bool × Bool)) (d' : Efab) (oib : Option Ibch)
    (obar : Option barrier_kind) (st : CySt)
    (hstep : pstepHart cpu m rs fn ib d l m' ors fn' d' oib obar) (hpure : ∀ x, m ≠ .pure x)
    (hcy : cyB A Aa S T P m st) (hm : cyMatch st rs ib) (hA : feAdm A Aa st.fe.length l) :
    cyStopAt S T st m ∨ cyStepOk A Aa S T P st l m' (oib.getD ib) (ors.getD rs) := by
  rcases hstep with ⟨H, hd⟩ | H
  · cases fn with
    | some f =>
      obtain ⟨pr, pw, sr, sw⟩ := f
      obtain ⟨rfl, rfl, rfl, -, -, rfl, -⟩ := H
      exact Or.inr (PinCycRun.stepStay A Aa S T P st _ _ ib rs hcy hm (fun _ _ e => by cases e) rfl)
    | none =>
      have hnn : st.an = false → ∀ rd srcs, l ≠ LRegW rd srcs := by
        intro han
        have hib : ib.ibBits = none := by
          have := hm.2.2.2.2.2
          rw [han] at this
          cases h : ib.ibBits with
          | none => rfl
          | some _ => rw [h] at this; cases this
        exact PinCycRun.noneNeutralNode cpu m rs ib d l m' ors fn' d' oib obar hib H hd
      exact cyNodeStep A Aa S T P m rs ib d.efDev l m' ors fn' d'.efDev oib obar st H hpure hcy hm hA
        hnn
  · obtain ⟨mm, b, k, -, rfl, rfl, -, -, rfl, -, rfl⟩ := H
    right
    obtain ⟨hag, hrb, hrbv, hro, hrds, han⟩ := hm
    have hw : ∀ v, RbootAll ((if mm then rs.set .sig_meip v else rs.set .sig_seip v)) := by
      intro v
      split
      · exact rbootAllSet rs _ _ hrb trivial
      · exact rbootAllSet rs _ _ hrb trivial
    refine PinCycRun.stepStay A Aa S T P st _ _ ib _ hcy ⟨?_, ?_, hrbv, hro, hrds, han⟩
      (fun _ _ e => by cases e) rfl
    · show ∀ r, wireReg r = false → (pinSet rs mm b) r = st.rv r
      unfold pinSet
      split
      · exact PinCycRun.agreeSetWire rs st.rv _ _ rfl hag
      · exact PinCycRun.agreeSetWire rs st.rv _ _ rfl hag
    · show RbootAll (pinSet rs mm b)
      unfold pinSet
      exact hw _

/-- The trace facts of a run segment: the log grows by the segment's fetch items, the slots are
B1's scan of its labels at the role the segment ends with, the role and the announce flag are
kept once announced. -/
def cyTrace (st : CySt) (ls : List Wlabel) (st1 : CySt) : Prop :=
  (∃ fe', st1.fe = st.fe ++ fe' ∧ List.Forall₂ feLab fe' (feLabs ls)) ∧
  (st1.d.n, st1.d.ok) = dfScan st1.d.ro (st.d.n, st.d.ok) ls ∧
  (st.an = true → st1.d.ro = st.d.ro ∧ st1.an = true)

theorem PinCycRun.cyTraceNil (st : CySt) : cyTrace st [] st :=
  ⟨⟨[], by simp, by simp [feLabs]⟩, rfl, fun h => ⟨rfl, h⟩⟩

theorem PinCycRun.cyTraceCons (A : Int → BitVec 8 → Prop) (Aa : Nat → Int → Prop) (S : Register → Bool)
    (T : CySt → (r : Register) → RegisterType r → Prop) (P : Unit → CySt → Prop) (st st' st1 : CySt)
    (l : Wlabel) (ls : List Wlabel)
    (h1 : feStep st.fe st'.fe l) (h2 : (st'.d.n, st'.d.ok) = dfLab st.d.ro st.d.n st.d.ok l)
    (h3 : st.an = true → st'.d.ro = st.d.ro ∧ st'.an = true)
    (h4 : st.an = false → ∀ rd srcs, l ≠ LRegW rd srcs) (ht : cyTrace st' ls st1) :
    cyTrace st (l :: ls) st1 := by
  obtain ⟨⟨fe', t1, t1'⟩, t2, t3⟩ := ht
  refine ⟨?_, ?_, ?_⟩
  · rcases h1 with ⟨hl, e⟩ | ⟨e, e1, he⟩
    · refine ⟨fe', by rw [t1, e], ?_⟩
      simp only [feLabs, List.filter_cons, hl, Bool.false_eq_true, ↓reduceIte]
      exact t1'
    · refine ⟨e :: fe', by rw [t1, e1, List.append_assoc]; rfl, ?_⟩
      have hl : isFeLab l = true := by
        obtain ⟨tvs, rfl, -⟩ := he; rfl
      simp only [feLabs, List.filter_cons, hl, ↓reduceIte]
      exact List.Forall₂.cons he t1'
  · rw [t2, h2]
    show dfScan st1.d.ro (dfLab st.d.ro st.d.n st.d.ok l) ls =
      dfScan st1.d.ro (dfLab st1.d.ro st.d.n st.d.ok l) ls
    cases han : st.an with
    | true =>
      obtain ⟨e1, e2⟩ := h3 han
      rw [(t3 e2).1, e1]
    | false =>
      rw [dfLabNeutral _ _ _ l (h4 han), dfLabNeutral _ _ _ l (h4 han)]
  · intro han
    obtain ⟨e1, e2⟩ := h3 han
    obtain ⟨f1, f2⟩ := t3 e2
    exact ⟨f1.trans e1, f2⟩

/-- An IN-CYCLE run: a plain chain whose every step leaves a hart sitting inside a cycle (an impure
tree) — it never takes the boundary step. -/
inductive irun : List Wlabel → Pexv6 → Efab → Pexv6 → Efab → Prop where
  | nil (p : Pexv6) (d : Efab) : irun [] p d p d
  | more {l : Wlabel} {ls : List Wlabel} {cpu : CPU} {c : Eff RegisterType exception}
      {k : Sail.ArchSem.Effect.ret c → SailM Unit} {rs : RegFile}
      {fn : Option (Bool × Bool × Bool × Bool)} {ib : Ibch} {d : Efab} {p1 : Pexv6} {d1 : Efab}
      {p2 : Pexv6} {d2 : Efab} :
      pstepEv (.PHart cpu (.impure c k) rs fn ib) d l p1 d1 → irun ls p1 d1 p2 d2 →
      irun (l :: ls) (.PHart cpu (.impure c k) rs fn ib) d p2 d2

theorem irunPevrun (ls : List Wlabel) (p : Pexv6) (d : Efab) (p' : Pexv6) (d' : Efab) :
    irun ls p d p' d' → pevrun ls p d p' d' := by
  intro h
  induction h with
  | nil p d => exact .nil p d
  | more hs _ ih => exact .more hs ih

/-- **THE RUN** (header): the three outcomes of a run of the hart from a tree under `cyB`. -/
def cyOut (A : Int → BitVec 8 → Prop) (Aa : Nat → Int → Prop) (S : Register → Bool)
    (T : CySt → (r : Register) → RegisterType r → Prop) (P : Unit → CySt → Prop) (cpu : CPU)
    (st : CySt) (ls : List Wlabel) (p : Pexv6) (d : Efab) (p' : Pexv6) (d' : Efab) : Prop :=
  -- a STOP node is reached
  (∃ (ls1 ls2 : List Wlabel) (m1 : SailM Unit) (rs1 : RegFile)
      (fn1 : Option (Bool × Bool × Bool × Bool)) (ib1 : Ibch) (d1 : Efab) (st1 : CySt),
    ls = ls1 ++ ls2 ∧ irun ls1 p d (.PHart cpu m1 rs1 fn1 ib1) d1 ∧
    pevrun ls2 (.PHart cpu m1 rs1 fn1 ib1) d1 p' d' ∧
    cyStopAt S T st1 m1 ∧ cyMatch st1 rs1 ib1 ∧ cyTrace st ls1 st1) ∨
  -- the END of the cycle is reached (first `.pure`)
  (∃ (ls1 ls2 : List Wlabel) (rs1 : RegFile) (fn1 : Option (Bool × Bool × Bool × Bool))
      (ib1 : Ibch) (d1 : Efab) (st1 : CySt),
    ls = ls1 ++ ls2 ∧ irun ls1 p d (.PHart cpu (.pure ()) rs1 fn1 ib1) d1 ∧
    pevrun ls2 (.PHart cpu (.pure ()) rs1 fn1 ib1) d1 p' d' ∧
    P () st1 ∧ cyMatch st1 rs1 ib1 ∧ cyTrace st ls1 st1) ∨
  -- the run ends INSIDE the cycle
  (∃ (m1 : SailM Unit) (rs1 : RegFile) (fn1 : Option (Bool × Bool × Bool × Bool)) (ib1 : Ibch)
      (st1 : CySt),
    p' = .PHart cpu m1 rs1 fn1 ib1 ∧ (∀ x, m1 ≠ .pure x) ∧ irun ls p d p' d' ∧
    cyB A Aa S T P m1 st1 ∧ cyMatch st1 rs1 ib1 ∧ cyTrace st ls st1)

theorem cyRun (A : Int → BitVec 8 → Prop) (Aa : Nat → Int → Prop) (S : Register → Bool)
    (T : CySt → (r : Register) → RegisterType r → Prop) (P : Unit → CySt → Prop) :
    ∀ (ls : List Wlabel) (p : Pexv6) (d : Efab) (p' : Pexv6) (d' : Efab), pevrun ls p d p' d' →
    ∀ (cpu : CPU) (m : SailM Unit) (rs : RegFile) (fn : Option (Bool × Bool × Bool × Bool))
      (ib : Ibch) (st : CySt), p = .PHart cpu m rs fn ib → cyB A Aa S T P m st → cyMatch st rs ib →
      (∀ ls1 l ls2 pm dm, ls = ls1 ++ l :: ls2 → irun ls1 p d pm dm →
        feAdm A Aa (st.fe.length + (feLabs ls1).length) l) →
      cyOut A Aa S T P cpu st ls p d p' d' := by
  intro ls p d p' d' h
  induction h with
  | nil p d =>
    intro cpu m rs fn ib st hp hcy hm _
    subst hp
    cases m with
    | pure u =>
      cases u
      exact Or.inr (Or.inl ⟨[], [], rs, fn, ib, d, st, rfl, irun.nil _ _, .nil _ _, hcy, hm,
        PinCycRun.cyTraceNil st⟩)
    | impure c k =>
      exact Or.inr (Or.inr ⟨_, rs, fn, ib, st, rfl, (fun x e => by cases e), irun.nil _ _, hcy, hm,
        PinCycRun.cyTraceNil st⟩)
  | @more l ls p d p1 d1 p2 d2 hstep hrest ih =>
    intro cpu m rs fn ib st hp hcy hm hA
    subst hp
    -- the start is the end of the cycle
    cases m with
    | pure u =>
      cases u
      exact Or.inr (Or.inl ⟨[], l :: ls, rs, fn, ib, d, st, rfl, irun.nil _ _, .more hstep hrest, hcy,
        hm, PinCycRun.cyTraceNil st⟩)
    | impure c k =>
    cases p1 with
    | PDisk dp => exact (show False from hstep).elim
    | PHart cpu1 m1 rs1 fn1 ib1 =>
    obtain ⟨rfl, ors, oib, obar, rfl, rfl, hh⟩ := hstep
    have hst : pstepEv (.PHart cpu1 (.impure c k) rs fn ib) d l
        (.PHart cpu1 m1 (ors.getD rs) fn1 (oib.getD ib)) d1 :=
      ⟨rfl, ors, oib, obar, rfl, rfl, hh⟩
    have hA0 : feAdm A Aa st.fe.length l := by
      have := hA [] l ls _ d rfl (irun.nil _ _)
      simpa [feLabs] using this
    rcases cyHartStep A Aa S T P cpu1 _ rs fn ib d l m1 ors fn1 d1 oib obar st hh
        (fun x e => by cases e) hcy hm hA0 with hstop |
      ⟨st', hcy', hm', h1, h2, h3, h4⟩
    · exact Or.inl ⟨[], l :: ls, _, rs, fn, ib, d, st, rfl, irun.nil _ _,
        .more hst hrest, hstop, hm, PinCycRun.cyTraceNil st⟩
    · have hlen : st'.fe.length = st.fe.length + (feLabs [l]).length := by
        rcases h1 with ⟨hl, e⟩ | ⟨e, e1, he⟩
        · rw [e]; simp [feLabs, hl]
        · obtain ⟨tvs, rfl, -⟩ := he
          rw [e1]; simp [feLabs, isFeLab]
      rcases ih cpu1 m1 (ors.getD rs) fn1 (oib.getD ib) st' rfl hcy' hm'
          (fun ls1 l' ls2 pm dm e hir1 => by
            have := hA (l :: ls1) l' ls2 pm dm (by rw [e]; rfl) (irun.more hst hir1)
            rw [hlen, Nat.add_assoc, ← List.length_append]
            have e2 : feLabs [l] ++ feLabs ls1 = feLabs (l :: ls1) := by
              simp only [feLabs, List.filter_cons, List.filter_nil]
              split <;> rfl
            rw [e2]; exact this) with
        ⟨ls1, ls2, mm, rr, ff, ii, dd, st1, rfl, r1, r2, hs, hmm, ht⟩ |
        ⟨ls1, ls2, rr, ff, ii, dd, st1, rfl, r1, r2, hs, hmm, ht⟩ |
        ⟨mm, rr, ff, ii, st1, rfl, hnp, hir, hc, hmm, ht⟩
      · exact Or.inl ⟨l :: ls1, ls2, mm, rr, ff, ii, dd, st1, rfl, irun.more hst r1, r2, hs, hmm,
          PinCycRun.cyTraceCons A Aa S T P st st' st1 l ls1 h1 h2 h3 h4 ht⟩
      · exact Or.inr (Or.inl ⟨l :: ls1, ls2, rr, ff, ii, dd, st1, rfl, irun.more hst r1, r2, hs, hmm,
          PinCycRun.cyTraceCons A Aa S T P st st' st1 l ls1 h1 h2 h3 h4 ht⟩)
      · exact Or.inr (Or.inr ⟨mm, rr, ff, ii, st1, rfl, hnp, irun.more hst hir, hc, hmm,
          PinCycRun.cyTraceCons A Aa S T P st st' st1 l ls h1 h2 h3 h4 ht⟩)

end PinCycRun
end Weak
