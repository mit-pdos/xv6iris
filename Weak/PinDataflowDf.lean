/-
Weak: **W9a (B) B1 — the STATE-INDEXED dataflow predicate `dfB`** (plan
`notes/weak-allocproc-plan.md` rev 49 §C "W9a (B)" (B1); spike `notes/W9aB-spike.md` §4).
Lean-only (no Rocq source).

The emission labels a register write by the instruction's DECODED role and the per-instruction
READ SET (`WeakEvInst.pnodeStep`'s `regWrite` arm: `erwLabel (erwOf (depsOfIb ib.ibBits) ib.ibRds r)`,
DEC-7), and `WeakRvwmoPinBridge2.grpOkb` asks of one instruction's item group that its `LRegW`
labels are exactly the decoded destinations, in `taintStep`'s order (`depsRd` then `depsRd2`),
each with a source list covering the decoded one (`dsubb`).  `dfB P m st` follows the emission's
OWN bookkeeping along every path of `m`:

* the state `DfSt` is the decoded role `ro` (the announced word's `depsOfIb`), the read set `rds`
  (`Ibch.ibRds`: a register read appends `eregNum r`, `WeakLang.ibRead`), and the SLOT counter
  `n`/flag `ok`: an `LRegW rd srcs` label fills slot `n` of `dfDests ro` (= `depsRd ro` then
  `depsRd2 ro`) when `rd` is that slot's destination and `srcs` covers its decoded sources
  (`slotOk`), else it clears `ok`;
* a register read is answered by any value `Rboot` admits, a register write writes an
  `Rboot`-admitted value (W-SCO's boot register filter, `SailCycleOrderK.Rboot`); an announce sets
  the role and empties the read set (`dfAnn`, the emission's `ibAnn`); every other node continues
  for every answer; a failure is stuck (`True`); at `.pure x` the post `P x st`.

`dfB` never refuses a node: it is an all-paths POST predicate whose state is a function of the
path.  The bind law `dfBBind` composes it; `dfOfNw` lifts W9a (B)'s `nwB` (no write to a numbered
register, `Weak/PinDataflow.lean`) to `dfB` with the state unchanged but for a longer read set
(`dfExt`) at a role with no `mip`/`mtime` destination (`dfNwRole`); `dfRX` / `dfWX` are the GPR leaves (`rX_bits` reads, `wX_bits` writes, `x0` neither).

Every helper is `Weak.PinDataflow.*`.
-/
import Weak.PinDataflow
import Weak.SailCycleOrderFp
import Weak.WeakRvwmoPinBridge2
import MachCSL.UExecAluGpr

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Sail Sail.ConcurrencyInterfaceV1 LeanRV64D LeanRV64D.Functions
open Sail.ArchSem (FreeM)

namespace PinDataflow
open SailCycleOrderK

/-! ## 1. The state and its moves -/

/-- The dataflow state: decoded role, read set, filled slots, no bad write yet. -/
structure DfSt where
  ro : OpRoles
  rds : List Nat
  n : Nat
  ok : Bool

/-- The decoded destinations, in `taintStep`'s order. -/
def dfDests (ro : OpRoles) : List (Nat × List Dsrc) := (depsRd ro).toList ++ (depsRd2 ro).toList

/-- An `LRegW rd srcs` fills slot `n`: the slot's destination, sources covering the decoded ones. -/
def slotOk (ro : OpRoles) (n rd : Nat) (srcs : List Dsrc) : Bool :=
  match (dfDests ro)[n]? with
  | some (rd', dec) => Nat.beq rd rd' && dsubb dec srcs
  | none => false

/-- The slot bookkeeping of one label. -/
def dfLab (ro : OpRoles) (n : Nat) (ok : Bool) (l : Wlabel) : Nat × Bool :=
  match l with
  | .LRegW rd srcs => if slotOk ro n rd srcs = true then (n + 1, ok) else (n, false)
  | _ => (n, ok)

/-- `WeakLang.ibRead` on the read set. -/
def dfRdsAdd (rds : List Nat) (o : Option Nat) : List Nat :=
  match o with
  | some k => rds ++ [k]
  | none => rds

theorem dfRdsAddIb (i : Ibch) (o : Option Nat) : (ibRead i o).ibRds = dfRdsAdd i.ibRds o := by
  cases o <;> rfl

def dfRd (st : DfSt) (r : Register) : DfSt := { st with rds := dfRdsAdd st.rds (eregNum r) }

def dfWr (st : DfSt) (r : Register) : DfSt :=
  { st with n := (dfLab st.ro st.n st.ok (erwLabel (erwOf st.ro st.rds r))).1,
            ok := (dfLab st.ro st.n st.ok (erwLabel (erwOf st.ro st.rds r))).2 }

def dfAnn (st : DfSt) (n : Nat) (w : BitVec n) : DfSt :=
  { st with ro := depsOfIb (some (ibOfBvn w)), rds := [] }

/-- **THE DATAFLOW PREDICATE** (header). -/
def dfB {X : Type} (P : X → DfSt → Prop) : SailM X → DfSt → Prop
  | .pure x, st => P x st
  | .impure (.error _) _, _ => True
  | .impure (.ok o) k, st =>
    match o, k with
    | .regRead r, k => ∀ v, Rboot r v → dfB P (k v) (dfRd st r)
    | .regWrite r v, k => Rboot r v ∧ ∀ u, dfB P (k u) (dfWr st r)
    | .instrAnnounce n w, k => ∀ u, dfB P (k u) (dfAnn st n w)
    | .memRead .., k => ∀ v, dfB P (k v) st
    | .barrier _, k => ∀ v, dfB P (k v) st
    | .memWrite .., k => ∀ v, dfB P (k v) st
    | .branchAnnounce .., k => ∀ v, dfB P (k v) st
    | .cacheOp _, k => ∀ v, dfB P (k v) st
    | .tlbi _, k => ∀ v, dfB P (k v) st
    | .takeException _, k => ∀ v, dfB P (k v) st
    | .returnException _, k => ∀ v, dfB P (k v) st
    | .translationStart _, k => ∀ v, dfB P (k v) st
    | .translationEnd _, k => ∀ v, dfB P (k v) st
    | .cycleCount, k => ∀ v, dfB P (k v) st
    | .getCycleCount, k => ∀ v, dfB P (k v) st
    | .message _, k => ∀ v, dfB P (k v) st
    | .choose _, k => ∀ v, dfB P (k v) st
    | .readRam .., k => ∀ v, dfB P (k v) st
    | .writeRam .., k => ∀ v, dfB P (k v) st

/-! ## 2. The bind law, monotonicity -/

theorem dfBBind {X Y : Type} (Q : X → DfSt → Prop) (P : Y → DfSt → Prop) (m : SailM X)
    (f : X → SailM Y) :
    ∀ st, dfB Q m st → (∀ x st', Q x st' → dfB P (f x) st') → dfB P (m >>= f) st := by
  induction m with
  | pure y => intro st hm hf; exact hf y st hm
  | impure call k ih =>
    intro st hm hf
    cases call with
    | error e => trivial
    | ok o =>
      show dfB P (FreeM.impure (.ok o) (fun v => k v >>= f)) st
      cases o
      case regRead => exact fun v hv => ih v _ (hm v hv) hf
      case regWrite => exact ⟨hm.1, fun u => ih u _ (hm.2 u) hf⟩
      case instrAnnounce => exact fun u => ih u _ (hm u) hf
      all_goals exact fun v => ih v _ (hm v) hf

theorem dfBMono {X : Type} (P P' : X → DfSt → Prop) (hP : ∀ x st, P x st → P' x st) :
    ∀ (m : SailM X) st, dfB P m st → dfB P' m st := by
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
      case regWrite => exact ⟨hm.1, fun u => ih u _ (hm.2 u)⟩
      case instrAnnounce => exact fun u => ih u _ (hm u)
      all_goals exact fun v => ih v _ (hm v)

theorem dfBPure {X : Type} (P : X → DfSt → Prop) (x : X) (st : DfSt) :
    P x st → dfB P (pure x : SailM X) st := fun h => h

/-- A bind whose head is `pure`. -/
theorem dfBPureBind {X Y : Type} (P : Y → DfSt → Prop) (x : X) (f : X → SailM Y) (st : DfSt) :
    dfB P (f x) st → dfB P ((pure x : SailM X) >>= f) st := fun h => h

/-! ## 3. Growth of the read set -/

/-- `st'` is `st` with a longer read set (role, slots, flag unchanged). -/
def dfExt (st st' : DfSt) : Prop :=
  st'.ro = st.ro ∧ st'.n = st.n ∧ st'.ok = st.ok ∧ ∃ l, st'.rds = st.rds ++ l

theorem dfExtRefl (st : DfSt) : dfExt st st := ⟨rfl, rfl, rfl, [], (List.append_nil _).symm⟩

theorem dfExtTrans (s1 s2 s3 : DfSt) : dfExt s1 s2 → dfExt s2 s3 → dfExt s1 s3 := by
  rintro ⟨h1, h2, h3, l, hl⟩ ⟨g1, g2, g3, l', hl'⟩
  exact ⟨g1.trans h1, g2.trans h2, g3.trans h3, l ++ l', by rw [hl', hl, List.append_assoc]⟩

theorem dfExtRd (st : DfSt) (r : Register) : dfExt st (dfRd st r) := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  simp only [dfRd, dfRdsAdd]
  split
  · exact ⟨_, rfl⟩
  · exact ⟨[], (List.append_nil _).symm⟩

theorem dfExtMem (st st' : DfSt) (k : Nat) : dfExt st st' → k ∈ st.rds → k ∈ st'.rds := by
  rintro ⟨-, -, -, l, hl⟩ h
  rw [hl]; exact List.mem_append_left _ h

/-- A role with no `mip`/`mtime` destination (every role but a Zicsr write of `sip`/`mip`/`time`). -/
def dfNwRole (ro : OpRoles) : Prop := ∀ p, p ∈ dfDests ro → p.1 ≠ wcsr MIP ∧ p.1 ≠ wcsr TIME

theorem dfNwRoleRd (ro : OpRoles) (h : dfNwRole ro) (rd : Nat) (srcs : List Dsrc)
    (hd : depsRd ro = some (rd, srcs)) : rd ≠ wcsr MIP ∧ rd ≠ wcsr TIME :=
  h (rd, srcs) (List.mem_append_left _ (by rw [hd]; exact List.mem_singleton.2 rfl))

theorem dfNwRoleRd2 (ro : OpRoles) (h : dfNwRole ro) (rd : Nat) (srcs : List Dsrc)
    (hd : depsRd2 ro = some (rd, srcs)) : rd ≠ wcsr MIP ∧ rd ≠ wcsr TIME :=
  h (rd, srcs) (List.mem_append_right _ (by rw [hd]; exact List.mem_singleton.2 rfl))

/-- An `nwRegOk` write misses a destination that is not `mip`/`mtime`. -/
theorem erwDestNw (rds : List Nat) (r : Register) (d : Option (Nat × List Dsrc))
    (hr : nwRegOk r = true) (hd : ∀ rd srcs, d = some (rd, srcs) → rd ≠ wcsr MIP ∧ rd ≠ wcsr TIME) :
    erwDest rds r d = .ERWnone := by
  cases d with
  | none => rfl
  | some p =>
    obtain ⟨rd, srcs⟩ := p
    have hne := hd rd srcs rfl
    simp only [erwDest]
    cases h : eregNum r with
    | none => rfl
    | some n =>
      simp only [nwRegOk, h, Bool.or_eq_true, beq_iff_eq] at hr
      have hne' : n ≠ rd := by
        rintro rfl
        rcases hr with hr | hr
        · exact hne.1 hr
        · exact hne.2 hr
      simp only [hne', ↓reduceIte]

/-- **An `nwRegOk` write moves no slot of an `dfNwRole` role.** -/
theorem dfWrNone (st : DfSt) (r : Register) (hr : nwRegOk r = true) (hro : dfNwRole st.ro) :
    dfWr st r = st := by
  unfold dfWr erwOf
  by_cases hn : r = .nextPC
  · simp only [hn, ↓reduceIte, erwLabel, dfLab]
  · simp only [hn, ↓reduceIte,
      erwDestNw _ _ _ hr (fun rd srcs h => dfNwRoleRd _ hro rd srcs h),
      erwDestNw _ _ _ hr (fun rd srcs h => dfNwRoleRd2 _ hro rd srcs h), erwLabel, dfLab]

/-- ... nor does any write when the role has no destination. -/
theorem dfWrNoDest (st : DfSt) (r : Register) (h1 : depsRd st.ro = none)
    (h2 : depsRd2 st.ro = none) : dfWr st r = st := by
  unfold dfWr erwOf
  by_cases hn : r = .nextPC
  · simp only [hn, ↓reduceIte, erwLabel, dfLab]
  · simp only [hn, ↓reduceIte, h1, h2, erwDest, erwLabel, dfLab]

/-! ## 4. `nwB` (and, for a destination-free role, `fpB`) lift to `dfB` -/

/-- **The bridge**: an `nwB` tree is dataflow-neutral. -/
theorem dfOfNwAux {X : Type} (b : Bool) (P : X → Prop) (st0 : DfSt) (hro : dfNwRole st0.ro) :
    ∀ (m : SailM X) st, dfExt st0 st → nwB b P m →
      dfB (fun x st' => P x ∧ dfExt st0 st') m st := by
  intro m
  induction m with
  | pure y => intro st he hm; exact ⟨hm, he⟩
  | impure call k ih =>
    intro st he hm
    cases call with
    | error e => trivial
    | ok o =>
      cases o
      case regRead => exact fun v hv => ih v _ (dfExtTrans _ _ _ he (dfExtRd st _)) (hm v hv)
      case regWrite =>
        refine ⟨hm.1.1, fun u => ?_⟩
        rw [dfWrNone st _ hm.1.2 (he.1 ▸ hro)]
        exact ih u _ he (hm.2 u)
      case instrAnnounce => exact hm.elim
      case memRead => exact fun v => ih v _ he (hm.2 v)
      case barrier => exact fun v => ih v _ he hm.2
      all_goals exact fun v => ih v _ he (hm v)

theorem dfOfNw {X : Type} (b : Bool) (P : X → Prop) (m : SailM X) (st : DfSt)
    (hro : dfNwRole st.ro) (h : nwB b P m) :
    dfB (fun x st' => P x ∧ dfExt st st') m st :=
  dfOfNwAux b P st hro m st (dfExtRefl st) h

/-- An `nwB` head of a bind. -/
theorem dfNwBind {X Y : Type} (b : Bool) (Q : X → Prop) (P : Y → DfSt → Prop) (m : SailM X)
    (f : X → SailM Y) (st : DfSt) (hro : dfNwRole st.ro) (hm : nwB b Q m)
    (hf : ∀ x st', Q x → dfExt st st' → dfB P (f x) st') : dfB P (m >>= f) st :=
  dfBBind _ P m f st (dfOfNw b Q m st hro hm) (fun x st' h => hf x st' h.1 h.2)

/-- For a role with NO destination, W-SCO's footprint suffices (no announce on any path). -/
theorem dfOfFpAux {X : Type} (b : Bool) (P : X → Prop) (st0 : DfSt)
    (h1 : depsRd st0.ro = none) (h2 : depsRd2 st0.ro = none) :
    ∀ (m : SailM X) st, dfExt st0 st → SailCycleOrderFp.fpB b P m →
      dfB (fun x st' => P x ∧ dfExt st0 st') m st := by
  intro m
  induction m with
  | pure y => intro st he hm; exact ⟨hm, he⟩
  | impure call k ih =>
    intro st he hm
    cases call with
    | error e => trivial
    | ok o =>
      cases o
      case regRead => exact fun v hv => ih v _ (dfExtTrans _ _ _ he (dfExtRd st _)) (hm v hv)
      case regWrite =>
        refine ⟨hm.1, fun u => ?_⟩
        rw [dfWrNoDest st _ (he.1 ▸ h1) (he.1 ▸ h2)]
        exact ih u _ he (hm.2 u)
      case instrAnnounce => exact hm.elim
      case memRead => exact fun v => ih v _ he (hm.2 v)
      case barrier => exact fun v => ih v _ he hm.2
      all_goals exact fun v => ih v _ he (hm v)

theorem dfOfFp {X : Type} (b : Bool) (P : X → Prop) (m : SailM X) (st : DfSt)
    (h1 : depsRd st.ro = none) (h2 : depsRd2 st.ro = none) (h : SailCycleOrderFp.fpB b P m) :
    dfB (fun x st' => P x ∧ dfExt st st') m st :=
  dfOfFpAux b P st h1 h2 m st (dfExtRefl st) h

/-! ## 5. The GPR leaves -/

/-- The dependency number of GPR index `i` (`x0`: none). -/
def gprNum (i : BitVec 5) : Option Nat := if i.toNat = 0 then none else some i.toNat

/-- The read set after reading GPR `i`. -/
def dfGprRd (st : DfSt) (i : BitVec 5) : DfSt := { st with rds := dfRdsAdd st.rds (gprNum i) }

/-- `erwOf` at a non-`nextPC` register of dependency number `o`. -/
def erwOfNum (ro : OpRoles) (rds : List Nat) (o : Option Nat) : ErwKind :=
  let dst := fun (d : Option (Nat × List Dsrc)) =>
    match d with
    | some (rd, srcs) =>
        match o with
        | some n => if n = rd then ErwKind.ERWreg rd (erwSrcs srcs rds) else .ERWnone
        | none => .ERWnone
    | none => .ERWnone
  match dst (depsRd ro) with
  | .ERWnone => dst (depsRd2 ro)
  | k => k

/-- The state after writing GPR `i` (`x0`: no write). -/
def dfGprWr (st : DfSt) (i : BitVec 5) : DfSt :=
  match gprNum i with
  | none => st
  | some k =>
    { st with n := (dfLab st.ro st.n st.ok (erwLabel (erwOfNum st.ro st.rds (some k)))).1,
              ok := (dfLab st.ro st.n st.ok (erwLabel (erwOfNum st.ro st.rds (some k)))).2 }

theorem dfExtGprRd (st : DfSt) (i : BitVec 5) : dfExt st (dfGprRd st i) := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  simp only [dfGprRd, dfRdsAdd]
  split
  · exact ⟨_, rfl⟩
  · exact ⟨[], (List.append_nil _).symm⟩

theorem dfGprRdMem (st : DfSt) (i : BitVec 5) (h : i.toNat ≠ 0) : i.toNat ∈ (dfGprRd st i).rds := by
  simp only [dfGprRd, gprNum, h, ↓reduceIte, dfRdsAdd]
  exact List.mem_append_right _ (List.mem_singleton.2 rfl)

set_option maxRecDepth 4000 in
/-- **GPR read**: `rX_bits` appends the index (none for `x0`). -/
theorem dfRX (i : BitVec 5) (st : DfSt) :
    dfB (fun _ st' => st' = dfGprRd st i) (rX_bits (regidx.Regidx i)) st := by
  rcases uxa_bv5_cases i with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact rfl
  all_goals exact fun _ _ => rfl

/-- The CPS form of the read leaf. -/
theorem dfRXBind {Y : Type} (P : Y → DfSt → Prop) (i : BitVec 5) (f : BitVec 64 → SailM Y)
    (st : DfSt) (hf : ∀ v, dfB P (f v) (dfGprRd st i)) :
    dfB P (rX_bits (regidx.Regidx i) >>= f) st :=
  dfBBind _ P _ f st (dfRX i st) (fun v st' h => h ▸ hf v)

set_option maxHeartbeats 4000000 in
@[nw_reg] theorem nwXregWriteCallback (reg : regidx) (value : BitVec 64) :
    nwT (xreg_write_callback reg value) := by
  nw_walk

set_option maxRecDepth 4000 in
/-- **GPR write**: `wX_bits` fills the slot of GPR `i` (no write for `x0`); 32 closed cases, each one
register write and the model's callback (an `nwB` tree). -/
theorem dfWX (i : BitVec 5) (v : BitVec 64) (st : DfSt) (hro : dfNwRole st.ro) :
    dfB (fun _ st' => dfExt (dfGprWr st i) st') (wX_bits (regidx.Regidx i) v) st := by
  rcases uxa_bv5_cases i with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact dfExtRefl _
  all_goals exact ⟨trivial, fun _ => dfBMono _ _ (fun _ _ h' => h'.2) _ _
    (dfOfNw false _ _ _ hro (nwXregWriteCallback _ _))⟩

/-- The CPS form of the write leaf. -/
theorem dfWXBind {Y : Type} (P : Y → DfSt → Prop) (i : BitVec 5) (v : BitVec 64)
    (f : Unit → SailM Y) (st : DfSt) (hro : dfNwRole st.ro)
    (hf : ∀ u st', dfExt (dfGprWr st i) st' → dfB P (f u) st') :
    dfB P (wX_bits (regidx.Regidx i) v >>= f) st :=
  dfBBind _ P _ f st (dfWX i v st hro) hf

end PinDataflow
end Weak
