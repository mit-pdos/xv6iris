/-
Weak: AxEpiRet, part 2 (Lean-only split; header in `Weak/AxEpiRet.lean`).
-/
import Weak.AxEpiRetCert
import Weak.AxEpiLdJr
import Weak.AxEpiSound3

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std Iris.Std.PartialMap MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D
open Wlabel

/-! # 4. THE STAGED FORWARD REGION (Lean-only, deviation 1)

Every state FORWARD-reachable (`rstep` at the one graph `GD0`) from hart 0's start
`⟨riscvStep false, probeRegs pcSd, 0⟩` is certified by one of ten stage checkers (`chk` walks):
c.sdsp (`sdA` pre-fetch, `sdB` to the store at row item 0, `sdC` its tail at position 1), c.ldsp
(`ldA`, `ldB` to the load at row item 1, `ldC` its tail at position 2), c.jr (`jrA`, `jrB`), and
the target's c.sdsp (`tgA`, `tgB`, stuck at its store: the row is over).  Stage boundaries are CUT:
a `.pure` leaf compares the written registers `W` with a canonical file (`mkW`), and the next
stage is certified once at that file (pin-insensitivity + `offW`: off `W` every file is
`probeRegs pcSd`).  At position 2 every node has PC = `pcJr`, PC = the target, or provably differs
from `riscvStep` (`diverge`). -/

namespace AxEpiRet

/-- The registers the walked instructions write. -/
def W : List Register :=
  [.mip, .mtime, .mcycle, .minstret, .PC, .nextPC, .minstret_increment, .x1]

/-- The node writes only `W`. -/
def wq (m : SailM Unit) : Bool :=
  match m with
  | .impure (.ok (.regWrite r _)) _ => decide (r ∈ W)
  | _ => true

def eqW (a b : RegFile) : Bool :=
  decide (a .mip = b .mip) && decide (a .mtime = b .mtime) && decide (a .mcycle = b .mcycle) &&
  decide (a .minstret = b .minstret) && decide (a .PC = b .PC) && decide (a .nextPC = b .nextPC) &&
  decide (a .minstret_increment = b .minstret_increment) && decide (a .x1 = b .x1)

/-- The c.jr's jump target. -/
def tgt : BitVec 64 := jalrTarget sdWord

/-- Node predicate before the row end (positions 0, 1). -/
def QA (m : SailM Unit) (_ : RegFile) : Bool := wq m

/-- Node predicate at the row end: PC is `pcJr` or the target, or the node is not a boundary. -/
noncomputable def QB (m : SailM Unit) (rs : RegFile) : Bool :=
  wq m && (pcEqb (rs .PC) (BitVec.ofNat 64 pcJr) || pcEqb (rs .PC) tgt ||
    (diverge 2 m (riscvStep false) rs && diverge 2 m (riscvStep true) rs))

/-- A data access (non-fetch read, non-exclusive write): stuck at the row end. -/
def exitRam (m : SailM Unit) (_ : RegFile) : Bool :=
  match m with
  | .impure (.ok (.memRead _ _ req)) _ => !(classify req.access_kind).akIfetch
  | .impure (.ok (.memWrite _ _ req)) _ => !(classify req.access_kind).akLatest
  | _ => false

/-- A pinned fetch of `vs` at `base`, continued by `cont`. -/
def fetchCont (base : Int) (vs : List (BitVec 8)) (cont : SailM Unit → RegFile → Bool)
    (m : SailM Unit) (rs : RegFile) : Bool :=
  match m with
  | .impure (.ok (.memRead n _ req)) KK =>
      (classify req.access_kind).akIfetch && decide (paZ req.pa = base) &&
        decide (vs.length = n) && cont (KK (.Ok (wordOfBytes n vs, none))) rs
  | _ => false

/-- The reload, answered with the spilled bytes, continued by `cont`. -/
def loadCont (cont : SailM Unit → RegFile → Bool) (m : SailM Unit) (rs : RegFile) : Bool :=
  match m with
  | .impure (.ok (.memRead n _ req)) KK =>
      !(classify req.access_kind).akIfetch && !(classify req.access_kind).akLatest &&
        decide (sdData.length = n) && cont (KK (.Ok (wordOfBytes n sdData, none))) rs
  | _ => false

/-- The spill (a plain store), continued by `cont`. -/
def storeCont (cont : SailM Unit → RegFile → Bool) (m : SailM Unit) (rs : RegFile) : Bool :=
  match m with
  | .impure (.ok (.memWrite _ _ req)) KK =>
      !(classify req.access_kind).akLatest && cont (KK (.Ok (some true))) rs
  | _ => false

/-- The cut: the written registers are those of one of the canonical files. -/
def cut (cs : List RegFile) (rs : RegFile) : Bool := cs.any fun c => eqW rs c

/-- Every file agrees with this one off `W` and the pins. -/
def C0 : RegFile := probeRegs pcSd

/-- `C0` with the `W`-registers of `c`. -/
def mkW (c : RegFile) : RegFile :=
  (((((((C0.set .mip (c .mip)).set .mtime (c .mtime)).set .mcycle (c .mcycle)).set .minstret
    (c .minstret)).set .PC (c .PC)).set .nextPC (c .nextPC)).set .minstret_increment
    (c .minstret_increment)).set .x1 (c .x1)

/-- The register file after a run of the tracing interpreter (pins as in the file). -/
noncomputable def exitOf (m : SailM Unit) (rs : RegFile) : RegFile :=
  match ftp m ⟨rs, probeMem, testDevs⟩ [] [] with
  | .TOk _ t _ _ => t.regs
  | .TStuck _ _ => rs

/-- The canonical files at the stage boundaries. -/
noncomputable def Cld : RegFile := mkW (tAfterSd 0#1 0#1).regs
noncomputable def CjrF : RegFile := mkW (ldOut ⟨0#1, 0#1, 0#1, 0#1, none⟩ sdData)
noncomputable def CjrT : RegFile := mkW (ldOut ⟨0#1, 0#1, 0#1, 0#1, some (0#1, 0#1)⟩ sdData)
noncomputable def CjrL : List RegFile := [CjrF, CjrT]
noncomputable def CtgL : List RegFile :=
  [mkW (exitOf (riscvStep false) CjrF), mkW (exitOf (riscvStep true) CjrF),
   mkW (exitOf (riscvStep false) CjrT), mkW (exitOf (riscvStep true) CjrT)]

/-! ## The ten stages (last first) -/

noncomputable def tgB : SailM Unit → RegFile → Bool := chk QB exitRam (fun _ => false)
noncomputable def ramTg (m : SailM Unit) (rs : RegFile) : Bool :=
  fetchCont ((tgt.toNat : Nat) : Int) AxEpiRace2Run.h1Vs4 tgB m rs || exitRam m rs
noncomputable def tgA : SailM Unit → RegFile → Bool := chk QB ramTg (fun _ => false)
noncomputable def jrB : SailM Unit → RegFile → Bool := chk QB exitRam (cut CtgL)
noncomputable def jrA : SailM Unit → RegFile → Bool :=
  chk QB (fetchCont (pcJr : Int) cjrVs4 jrB) (fun _ => false)
noncomputable def ldC : SailM Unit → RegFile → Bool := chk QB exitRam (cut CjrL)
noncomputable def ldB : SailM Unit → RegFile → Bool := chk QA (loadCont ldC) (fun _ => false)
noncomputable def ldA : SailM Unit → RegFile → Bool :=
  chk QA (fetchCont (pcLd : Int) AxEpiLedger.ldVs ldB) (fun _ => false)
noncomputable def sdC : SailM Unit → RegFile → Bool := chk QA (fun _ _ => false) (cut [Cld])
noncomputable def sdB : SailM Unit → RegFile → Bool := chk QA (storeCont sdC) (fun _ => false)
noncomputable def sdA : SailM Unit → RegFile → Bool :=
  chk QA (fetchCont (pcSd : Int) sdVs sdB) (fun _ => false)

/-! ## The certificates (kernel) -/

set_option maxRecDepth 100000 in
theorem certSd : sdA (riscvStep false) C0 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem certLd : ∀ tk, ldA (riscvStep tk) Cld = true := by
  intro tk; cases tk <;> decide +kernel

set_option maxRecDepth 100000 in
theorem certJr : ∀ c ∈ CjrL, ∀ tk, jrA (riscvStep tk) c = true := by
  intro c hc tk
  simp only [CjrL, List.mem_cons, List.not_mem_nil, _root_.or_false] at hc
  rcases hc with rfl | rfl <;> cases tk <;> decide +kernel

set_option maxRecDepth 100000 in
theorem certTg : ∀ c ∈ CtgL, ∀ tk, tgA (riscvStep tk) c = true := by
  intro c hc tk
  simp only [CtgL, List.mem_cons, List.not_mem_nil, _root_.or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> cases tk <;> decide +kernel

/-! ## Bookkeeping: `W`, `offW`, the cut -/

theorem notPin (r : Register) (hr : r ∈ W) : ¬ AxRunClose.pinReg r := by
  rintro (rfl | rfl) <;> exact absurd hr (by decide)

theorem mkWOff (c : RegFile) (r : Register) (hr : r ∉ W) : mkW c r = C0 r := by
  simp only [W, List.mem_cons, List.not_mem_nil, _root_.or_false, not_or] at hr
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hr
  unfold mkW
  rw [RegFile.set_other _ _ _ _ h8, RegFile.set_other _ _ _ _ h7, RegFile.set_other _ _ _ _ h6,
    RegFile.set_other _ _ _ _ h5, RegFile.set_other _ _ _ _ h4, RegFile.set_other _ _ _ _ h3,
    RegFile.set_other _ _ _ _ h2, RegFile.set_other _ _ _ _ h1]

theorem eqWSpec (a b : RegFile) (h : eqW a b = true) : ∀ r ∈ W, a r = b r := by
  simp only [eqW, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  intro r hr
  simp only [W, List.mem_cons, List.not_mem_nil, _root_.or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption

/-- Off `W` and the pins, the file is `C0`. -/
def offW (rs : RegFile) : Prop := ∀ r, r ∉ W → ¬ AxRunClose.pinReg r → rs r = C0 r

theorem cutAgree (cs : List RegFile) (Hcs : ∀ c ∈ cs, ∀ r, r ∉ W → c r = C0 r) (rs : RegFile)
    (Hc : cut cs rs = true) (Hw : offW rs) : ∃ c ∈ cs, regsAgree AxRunClose.pinReg c rs := by
  obtain ⟨c, hc, he⟩ := List.any_eq_true.1 Hc
  refine ⟨c, hc, fun r hp => ?_⟩
  by_cases hr : r ∈ W
  · exact (eqWSpec rs c he r hr).symm
  · rw [Hcs c hc r hr, Hw r hr hp]

theorem cldOff : ∀ c ∈ [Cld], ∀ r, r ∉ W → c r = C0 r := by
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, _root_.or_false] at hc
  subst hc
  exact mkWOff _

theorem cjrOff : ∀ c ∈ CjrL, ∀ r, r ∉ W → c r = C0 r := by
  intro c hc
  simp only [CjrL, List.mem_cons, List.not_mem_nil, _root_.or_false] at hc
  rcases hc with rfl | rfl <;> exact mkWOff _

theorem ctgOff : ∀ c ∈ CtgL, ∀ r, r ∉ W → c r = C0 r := by
  intro c hc
  simp only [CtgL, List.mem_cons, List.not_mem_nil, _root_.or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> exact mkWOff _

/-! ## Pin-insensitivity of the stages -/

theorem qaIns : seipInsens QA := fun _ _ _ _ => rfl

theorem qbIns : seipInsens QB := by
  intro m rs rs' hag
  simp only [QB]
  rw [hag .PC (notPin _ (by decide)), divergeAgree 2 m _ rs rs' hag,
    divergeAgree 2 m _ rs rs' hag]

theorem exitIns : seipInsens exitRam := fun _ _ _ _ => rfl

theorem fetchContIns (base : Int) (vs : List (BitVec 8)) (cont : SailM Unit → RegFile → Bool)
    (Hc : seipInsens cont) : seipInsens (fetchCont base vs cont) := by
  intro m rs rs' hag
  rcases m with y | ⟨call, KK⟩
  · rfl
  rcases call with e | o
  · rfl
  cases o <;> try rfl
  simp only [fetchCont]
  rw [Hc _ _ _ hag]

theorem loadContIns (cont : SailM Unit → RegFile → Bool) (Hc : seipInsens cont) :
    seipInsens (loadCont cont) := by
  intro m rs rs' hag
  rcases m with y | ⟨call, KK⟩
  · rfl
  rcases call with e | o
  · rfl
  cases o <;> try rfl
  simp only [loadCont]
  rw [Hc _ _ _ hag]

theorem storeContIns (cont : SailM Unit → RegFile → Bool) (Hc : seipInsens cont) :
    seipInsens (storeCont cont) := by
  intro m rs rs' hag
  rcases m with y | ⟨call, KK⟩
  · rfl
  rcases call with e | o
  · rfl
  cases o <;> try rfl
  simp only [storeCont]
  rw [Hc _ _ _ hag]

theorem cutIns (cs : List RegFile) :
    ∀ rs rs', regsAgree AxRunClose.pinReg rs rs' → cut cs rs = cut cs rs' := by
  intro rs rs' hag
  have h : ∀ c, eqW rs c = eqW rs' c := by
    intro c
    simp only [eqW]
    rw [hag .mip (notPin _ (by decide)), hag .mtime (notPin _ (by decide)),
      hag .mcycle (notPin _ (by decide)), hag .minstret (notPin _ (by decide)),
      hag .PC (notPin _ (by decide)), hag .nextPC (notPin _ (by decide)),
      hag .minstret_increment (notPin _ (by decide)), hag .x1 (notPin _ (by decide))]
  simp only [cut, h]

theorem tgBIns : seipInsens tgB := fun m => chkAgree _ _ _ qbIns exitIns (fun _ _ _ => rfl) m

theorem ramTgIns : seipInsens ramTg := by
  intro m rs rs' hag
  simp only [ramTg]
  rw [fetchContIns _ _ _ tgBIns m rs rs' hag]
  rfl

theorem tgAIns : seipInsens tgA := fun m => chkAgree _ _ _ qbIns ramTgIns (fun _ _ _ => rfl) m

theorem jrBIns : seipInsens jrB := fun m => chkAgree _ _ _ qbIns exitIns (cutIns _) m

theorem jrAIns : seipInsens jrA :=
  fun m => chkAgree _ _ _ qbIns (fetchContIns _ _ _ jrBIns) (fun _ _ _ => rfl) m

theorem ldCIns : seipInsens ldC := fun m => chkAgree _ _ _ qbIns exitIns (cutIns _) m

theorem ldBIns : seipInsens ldB :=
  fun m => chkAgree _ _ _ qaIns (loadContIns _ ldCIns) (fun _ _ _ => rfl) m

theorem ldAIns : seipInsens ldA :=
  fun m => chkAgree _ _ _ qaIns (fetchContIns _ _ _ ldBIns) (fun _ _ _ => rfl) m

theorem sdCIns : seipInsens sdC :=
  fun m => chkAgree _ _ _ qaIns (fun _ _ _ _ => rfl) (cutIns _) m

theorem sdBIns : seipInsens sdB :=
  fun m => chkAgree _ _ _ qaIns (storeContIns _ sdCIns) (fun _ _ _ => rfl) m

theorem sdAIns : seipInsens sdA :=
  fun m => chkAgree _ _ _ qaIns (fetchContIns _ _ _ sdBIns) (fun _ _ _ => rfl) m

/-! ## The invariant -/

/-- The stages at each row position. -/
def stageAt : Nat → SailM Unit → RegFile → Prop
  | 0, m, rs => sdA m rs = true ∨ sdB m rs = true
  | 1, m, rs => sdC m rs = true ∨ ldA m rs = true ∨ ldB m rs = true
  | 2, m, rs => ldC m rs = true ∨ jrA m rs = true ∨ jrB m rs = true ∨ tgA m rs = true ∨
      tgB m rs = true
  | _ + 3, _, _ => False

def Inv (s : Athread) : Prop :=
  ∃ cpu m rs ib k, s = ⟨.PHart cpu m rs none ib, k⟩ ∧ offW rs ∧ stageAt k m rs

theorem stageAgree (k : Nat) (m : SailM Unit) (rs rs' : RegFile)
    (hag : regsAgree AxRunClose.pinReg rs rs') : stageAt k m rs → stageAt k m rs' := by
  match k with
  | 0 =>
    rintro (h | h)
    · exact .inl (by rw [← sdAIns m rs rs' hag]; exact h)
    · exact .inr (by rw [← sdBIns m rs rs' hag]; exact h)
  | 1 =>
    rintro (h | h | h)
    · exact .inl (by rw [← sdCIns m rs rs' hag]; exact h)
    · exact .inr (.inl (by rw [← ldAIns m rs rs' hag]; exact h))
    · exact .inr (.inr (by rw [← ldBIns m rs rs' hag]; exact h))
  | 2 =>
    rintro (h | h | h | h | h)
    · exact .inl (by rw [← ldCIns m rs rs' hag]; exact h)
    · exact .inr (.inl (by rw [← jrAIns m rs rs' hag]; exact h))
    · exact .inr (.inr (.inl (by rw [← jrBIns m rs rs' hag]; exact h)))
    · exact .inr (.inr (.inr (.inl (by rw [← tgAIns m rs rs' hag]; exact h))))
    · exact .inr (.inr (.inr (.inr (by rw [← tgBIns m rs rs' hag]; exact h))))
  | _ + 3 => exact id

end AxEpiRet

end Weak
