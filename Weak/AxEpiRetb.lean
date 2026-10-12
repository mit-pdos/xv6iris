/-
Weak: AxEpiRet, part 2 (Lean-only split of `iris/AxEpiRet.v`; header, deviations and name map in
`Weak/AxEpiRet.lean`).  The staged forward region of hart 0 (`namespace Weak.AxEpiRet`: ten
`chk` stages, 15 kernel certificates, the invariant `Inv` and its step `invStep` under `rstep`,
`invGood`), then Rocq §4 (`epiRetPost2`, `epiRetReachPc`, `wpdEpiRetGa2`), §5 (`epiRetAdeq`,
`epiRetReloadSound`), §6 (`epiRetStmtPremisesReload`, `raceRetNoWpd1`) and §8, the capstone
`epiRetSound2 : epiRetSound2Stmt`.
-/
import Weak.AxEpiRet
import Weak.AxEpiRetCert
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

/-! ## The step lemmas -/

/-- Admin labels have no graph halves. -/
theorem adminHalves (l : Wlabel) (h : AxOpsem.lbAdminAx true l) :
    wlRd l = none ∧ wlWr l = none ∧ wlFence l = none := by
  cases l <;> simp_all [AxOpsem.lbAdminAx, wlRd, wlWr, wlFence]

/-- Only a register write writes the register file. -/
theorem orsCases (m : SailM Unit) (rs : RegFile) (ib : Ibch) (d : DevStates) (l : Wlabel)
    (m' : SailM Unit) (ors : Option RegFile) (fn' : Option (Bool × Bool × Bool × Bool))
    (d' : DevStates) (oib : Option Ibch) (obar : Option barrier_kind) :
    pnodeStep m rs ib d l m' ors fn' d' oib obar →
    ors = none ∨ ∃ r v k, m = .impure (.ok (.regWrite r v)) k ∧ ors = some (rs.set r v) := by
  intro h
  cases m with
  | pure y =>
    obtain ⟨_, _, _, h, _⟩ := h
    exact .inl h
  | impure call k =>
    cases call with
    | error e => exact h.elim
    | ok o =>
      cases o
      case regWrite r v =>
        obtain ⟨_, _, h, _⟩ := h
        exact .inr ⟨r, v, k, rfl, h⟩
      case memRead n va req =>
        simp only [pnodeStep] at h
        by_cases hd : devAddr req.pa = true
        · rw [if_pos hd] at h
          obtain ⟨_, _, _, _, h, _⟩ := h
          exact .inl h
        · rw [if_neg hd] at h
          rcases h with ⟨_, _, _, _, _, _, _, h, _⟩ |
            ⟨_, ⟨_, _, _, _, _, _, _, h, _⟩ | ⟨_, _, _, _, _, _, _, h, _⟩⟩ <;> exact .inl h
      case memWrite n va req =>
        simp only [pnodeStep] at h
        by_cases hd : devAddr req.pa = true
        · rw [if_pos hd] at h
          cases hv : req.value with
          | none => rw [hv] at h; exact h.elim
          | some v =>
            rw [hv] at h
            obtain ⟨_, _, _, h, _⟩ := h
            exact .inl h
        · rw [if_neg hd] at h
          cases hv : req.value with
          | none => rw [hv] at h; exact h.elim
          | some v =>
            rw [hv] at h
            rcases h with ⟨_, ⟨_, _, _, h, _⟩ | ⟨_, ⟨_, _, h, _⟩ | ⟨_, _, h, _⟩⟩⟩ <;> exact .inl h
      case choose =>
        obtain ⟨_, _, _, h, _⟩ := h
        exact .inl h
      all_goals first
        | exact h.elim
        | (obtain ⟨_, _, h, _⟩ := h; exact .inl h)

/-- A step from a `W`-only node keeps `offW`. -/
theorem offWStep (m : SailM Unit) (rs : RegFile) (ib : Ibch) (d : DevStates) (l : Wlabel)
    (m' : SailM Unit) (ors : Option RegFile) (fn' : Option (Bool × Bool × Bool × Bool))
    (d' : DevStates) (oib : Option Ibch) (obar : Option barrier_kind) (Hw : offW rs)
    (hq : wq m = true) (hn : pnodeStep m rs ib d l m' ors fn' d' oib obar) :
    offW (ors.getD rs) := by
  rcases orsCases m rs ib d l m' ors fn' d' oib obar hn with rfl | ⟨r, v, k, rfl, rfl⟩
  · exact Hw
  · intro r' hr' hp
    simp only [wq, decide_eq_true_eq] at hq
    have hne : r' ≠ r := fun h => hr' (h ▸ hq)
    show (rs.set r v) r' = C0 r'
    rw [RegFile.set_other _ _ _ _ hne]
    exact Hw r' hr' hp

/-- The labels of a RAM read node: a fetch, or a graph read (no write/fence half, not admin). -/
theorem memReadStep (cpu : CPU) (n va : Nat)
    (req : Mem_read_request n va Arch.pa Arch.translation Arch.arch_ak)
    (KK : Result (BitVec (8 * n) × Option Bool) Arch.abort → SailM Unit) (rs : RegFile)
    (ib : Ibch) (d : Efab) (l : Wlabel) (p' : Pexv6) (d' : Efab)
    (hdev : devAddr req.pa = false)
    (h : pstepProg (.PHart cpu (.impure (.ok (.memRead n va req)) KK) rs none ib) d l p' d') :
    ((classify req.access_kind).akIfetch = true ∧ ∃ tvs : List (Nat × BitVec 8),
        tvs.length = n ∧ l = .LIFetch (paZ req.pa) tvs ∧
        p' = .PHart cpu (KK (.Ok (wordOfBytes n (tvs.map Prod.snd), none))) rs none ib) ∨
    ((classify req.access_kind).akIfetch = false ∧ ¬ AxOpsem.lbAdminAx true l ∧ wlWr l = none ∧
        wlFence l = none ∧
        p' = .PHart cpu (KK (.Ok (wordOfBytes n (wlRvals l), none))) rs none ib) := by
  cases hfe : (classify req.access_kind).akIfetch
  · refine .inr ⟨rfl, ?_⟩
    cases p' with
    | PDisk _ => exact False.elim h
    | PHart c m' rs' fn' ib' =>
      obtain ⟨rfl, ors, oib, obar, rfl, rfl, hn, -⟩ := h
      simp only [pstepNode, pnodeStep, hdev, Bool.false_eq_true, ↓reduceIte] at hn
      rcases hn with ⟨hif, -⟩ | ⟨-, ⟨-, w, tvs, hlen, hby, rfl, rfl, rfl, rfl, -, rfl, -⟩ |
          ⟨-, w, tvs, hlen, hby, rfl, rfl, rfl, rfl, -, rfl, -⟩⟩
      · rw [hfe] at hif
        exact absurd hif Bool.false_ne_true
      · refine ⟨by simp [AxOpsem.lbAdminAx], rfl, rfl, ?_⟩
        simp only [wlRvals]
        rw [← bytesWordEq n w tvs hlen hby]
        rfl
      · refine ⟨by simp [AxOpsem.lbAdminAx], rfl, rfl, ?_⟩
        simp only [wlRvals]
        rw [← bytesWordEq n w tvs hlen hby]
        rfl
  · exact .inl ⟨rfl, AxCjrWpd.fetchStepInv cpu n va req KK rs ib d l p' d' hdev hfe h⟩

/-- The program step / graph read of `rstep` (everything but the wire). -/
def progOrRead (G : Gdexec → Prop) (s s' : Athread) : Prop :=
  (∃ GD l, G GD ∧ AxOpsem.astepProg (AxOpsem.grow GD 0) s l s' ∧
     WeakAxRealize.fetchPin GD.gdG.gxImg l) ∨
  (∃ GD id K v, G GD ∧ areadStep (AxOpsem.grow GD 0) s id K ∧
     graphValue GD (0, s.atK) = some v ∧ v.length = aidentN id ∧ s' = K v)

/-- THE GENERIC STAGE STEP: a non-wire step from a `chk`-certified node stays in the stage, takes
the `.pure` exit, the fetch, the graph read, or the write. -/
theorem stageStep (Q ram : SailM Unit → RegFile → Bool) (ret : RegFile → Bool)
    (HQ : ∀ m rs, Q m rs = true → wq m = true)
    (HramWr : ∀ (n va : Nat) (req : Mem_write_request n va Arch.pa Arch.translation Arch.arch_ak)
      (KK : Result (Option Bool) Arch.abort → SailM Unit) (rs : RegFile),
      ram (.impure (.ok (.memWrite n va req)) KK) rs = true →
      (classify req.access_kind).akLatest = false)
    (G : Gdexec → Prop) (cpu : CPU) (m : SailM Unit) (rs : RegFile) (ib : Ibch) (k : Nat)
    (Hc : chk Q ram ret m rs = true) (Hw : offW rs) (s' : Athread)
    (Hst : progOrRead G ⟨.PHart cpu m rs none ib, k⟩ s') :
    ∃ m' rs' ib' k', s' = ⟨.PHart cpu m' rs' none ib', k'⟩ ∧ offW rs' ∧
      ((k' = k ∧ chk Q ram ret m' rs' = true) ∨
       (k' = k ∧ ret rs = true ∧ rs' = rs ∧ ∃ tk, m' = riscvStep tk) ∨
       (k' = k ∧ rs' = rs ∧ ∃ (GD : Gdexec) (n va : Nat)
          (req : Mem_read_request n va Arch.pa Arch.translation Arch.arch_ak)
          (KK : Result (BitVec (8 * n) × Option Bool) Arch.abort → SailM Unit)
          (tvs : List (Nat × BitVec 8)),
          G GD ∧ m = .impure (.ok (.memRead n va req)) KK ∧ ram m rs = true ∧
          (classify req.access_kind).akIfetch = true ∧ tvs.length = n ∧
          WeakAxRealize.fetchPin GD.gdG.gxImg (.LIFetch (paZ req.pa) tvs) ∧
          m' = KK (.Ok (wordOfBytes n (tvs.map Prod.snd), none))) ∨
       (rs' = rs ∧ ∃ (GD : Gdexec) (n va : Nat)
          (req : Mem_read_request n va Arch.pa Arch.translation Arch.arch_ak)
          (KK : Result (BitVec (8 * n) × Option Bool) Arch.abort → SailM Unit) (lb : Lbl)
          (v : List (BitVec 8)),
          G GD ∧ m = .impure (.ok (.memRead n va req)) KK ∧ ram m rs = true ∧
          (classify req.access_kind).akIfetch = false ∧ (AxOpsem.grow GD 0)[k]? = some lb ∧
          k' = k + aidentAdvRd (aident lb) ∧ graphValue GD (0, k) = some v ∧
          m' = KK (.Ok (wordOfBytes n v, none))) ∨
       (k' = k + 1 ∧ rs' = rs ∧ ∃ (GD : Gdexec) (n va : Nat)
          (req : Mem_write_request n va Arch.pa Arch.translation Arch.arch_ak)
          (KK : Result (Option Bool) Arch.abort → SailM Unit) (lb : Lbl),
          G GD ∧ m = .impure (.ok (.memWrite n va req)) KK ∧ ram m rs = true ∧
          (AxOpsem.grow GD 0)[k]? = some lb ∧ m' = KK (.Ok (some true)))) := by
  have hq := HQ m rs (chkQ Q ram ret m rs Hc)
  rcases Hst with ⟨GD, l, HGD, Hast, Hpin⟩ | ⟨GD, id, K, v, HGD, Hrd, Hgv, Hvl, rfl⟩
  · cases Hast with
    | AStepAdmin _ _ d _ p' d' hadm hps =>
      obtain ⟨m', ors, fn', oib, obar, rfl, hn⟩ := pstepProgHart cpu m rs ib d l p' d' hps
      have Hw' := offWStep m rs ib d.efDev l m' ors fn' d'.efDev oib obar Hw hq hn
      rcases chkPnode Q ram ret m rs ib d.efDev l m' ors fn' d'.efDev oib obar Hc hn with
        ⟨-, rfl, Hc' | ⟨y, rfl, hr, rfl, tk, rfl⟩⟩ | ⟨n, va, req, KK, rfl, hdev, hram, hif⟩ |
        ⟨n, va, req, KK, rfl, -, hram, hlat⟩
      · exact ⟨m', ors.getD rs, oib.getD ib, k, rfl, Hw', .inl ⟨rfl, Hc'⟩⟩
      · exact ⟨riscvStep tk, rs, oib.getD ib, k, rfl, Hw, .inr (.inl ⟨rfl, hr, rfl, tk, rfl⟩)⟩
      · have hfe := hif hadm
        obtain ⟨tvs, hlen, rfl, hp⟩ :=
          AxCjrWpd.fetchStepInv cpu n va req KK rs ib d _ _ d' hdev hfe hps
        simp only [Pexv6.PHart.injEq] at hp
        obtain ⟨-, rfl, hrs, hfn, hib⟩ := hp
        refine ⟨_, rs, ib, k, ?_, Hw,
          .inr (.inr (.inl ⟨rfl, rfl, GD, n, va, req, KK, tvs, HGD, rfl, hram, hfe, hlen, Hpin,
            rfl⟩))⟩
        rw [hrs, hfn, hib]
      · have h1 := hlat hadm
        rw [HramWr n va req KK rs hram] at h1
        exact Bool.noConfusion h1
    | AStepWrite _ _ d _ lb p' d' hrow hwr _ _ hps =>
      obtain ⟨m', ors, fn', oib, obar, rfl, hn⟩ := pstepProgHart cpu m rs ib d l p' d' hps
      rcases chkPnode Q ram ret m rs ib d.efDev l m' ors fn' d'.efDev oib obar Hc hn with
        ⟨hadm, -, -⟩ | ⟨n, va, req, KK, rfl, hdev, hram, -⟩ | ⟨n, va, req, KK, rfl, hdev, hram, -⟩
      · rw [(adminHalves l hadm).2.1] at hwr
        exact Bool.noConfusion hwr
      · rcases memReadStep cpu n va req KK rs ib d l _ d' hdev hps with
          ⟨-, tvs, -, rfl, -⟩ | ⟨-, -, hw, -, -⟩
        · simp [wlWr] at hwr
        · rw [hw] at hwr
          exact Bool.noConfusion hwr
      · obtain ⟨v, -, rfl, hp⟩ :=
          storeNodePstep cpu n va req KK rs ib d _ _ d' hdev (HramWr n va req KK rs hram) hps
        simp only [Pexv6.PHart.injEq] at hp
        obtain ⟨-, rfl, hrs, hfn, hib⟩ := hp
        refine ⟨_, rs, ib, k + 1, ?_, Hw,
          .inr (.inr (.inr (.inr ⟨rfl, rfl, GD, n, va, req, KK, lb, HGD, rfl, hram, hrow,
            rfl⟩)))⟩
        rw [hrs, hfn, hib]
    | AStepFence _ _ d _ lb p' d' hrow hf _ hps =>
      obtain ⟨m', ors, fn', oib, obar, rfl, hn⟩ := pstepProgHart cpu m rs ib d l p' d' hps
      rcases chkPnode Q ram ret m rs ib d.efDev l m' ors fn' d'.efDev oib obar Hc hn with
        ⟨hadm, -, -⟩ | ⟨n, va, req, KK, rfl, hdev, hram, -⟩ | ⟨n, va, req, KK, rfl, hdev, hram, -⟩
      · rw [(adminHalves l hadm).2.2] at hf
        exact Bool.noConfusion hf
      · rcases memReadStep cpu n va req KK rs ib d l _ d' hdev hps with
          ⟨-, tvs, -, rfl, -⟩ | ⟨-, -, -, hw, -⟩
        · simp [wlFence] at hf
        · rw [hw] at hf
          exact Bool.noConfusion hf
      · obtain ⟨v, -, rfl, -⟩ :=
          storeNodePstep cpu n va req KK rs ib d _ _ d' hdev (HramWr n va req KK rs hram) hps
        simp [wlFence] at hf
  · obtain ⟨lb, hlb, hid, hrdS, HK⟩ := Hrd
    obtain ⟨l, d, d', hwl, hwv, hps, hk⟩ := HK v Hvl
    generalize hKv : K v = s'' at hps hk ⊢
    obtain ⟨p', k'⟩ := s''
    simp only at hps hk hlb Hgv
    obtain ⟨m', ors, fn', oib, obar, rfl, hn⟩ := pstepProgHart cpu m rs ib d l p' d' hps
    rcases chkPnode Q ram ret m rs ib d.efDev l m' ors fn' d'.efDev oib obar Hc hn with
      ⟨hadm, -, -⟩ | ⟨n, va, req, KK, rfl, hdev, hram, -⟩ | ⟨n, va, req, KK, rfl, hdev, hram, -⟩
    · rw [← hwl, (adminHalves l hadm).1] at hrdS
      exact absurd hrdS (by simp)
    · rcases memReadStep cpu n va req KK rs ib d l _ d' hdev hps with
        ⟨-, tvs, -, rfl, -⟩ | ⟨hnf, -, -, -, hp⟩
      · rw [← hwl] at hrdS
        exact absurd hrdS (by simp [wlRd])
      · simp only [Pexv6.PHart.injEq] at hp
        obtain ⟨-, rfl, hrs, hfn, hib⟩ := hp
        refine ⟨KK (.Ok (wordOfBytes n v, none)), rs, ib, k', ?_, Hw,
          .inr (.inr (.inr (.inl ⟨rfl, GD, n, va, req, KK, lb, v, HGD, rfl, hram, hnf, hlb, ?_,
            Hgv, rfl⟩)))⟩
        · rw [hrs, hfn, hib, hwv]
        · rw [hk, hid]
    · obtain ⟨v, -, rfl, -⟩ :=
        storeNodePstep cpu n va req KK rs ib d _ _ d' hdev (HramWr n va req KK rs hram) hps
      rw [← hwl] at hrdS
      exact absurd hrdS (by simp [wlRd])

/-! ## The ram specifications -/

theorem fetchContSpec {base : Int} {vs : List (BitVec 8)} {cont : SailM Unit → RegFile → Bool}
    {n va : Nat} {req : Mem_read_request n va Arch.pa Arch.translation Arch.arch_ak}
    {KK : Result (BitVec (8 * n) × Option Bool) Arch.abort → SailM Unit} {rs : RegFile}
    (h : fetchCont base vs cont (.impure (.ok (.memRead n va req)) KK) rs = true) :
    (classify req.access_kind).akIfetch = true ∧ paZ req.pa = base ∧ vs.length = n ∧
      cont (KK (.Ok (wordOfBytes n vs, none))) rs = true := by
  simp only [fetchCont, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

theorem loadContSpec {cont : SailM Unit → RegFile → Bool}
    {n va : Nat} {req : Mem_read_request n va Arch.pa Arch.translation Arch.arch_ak}
    {KK : Result (BitVec (8 * n) × Option Bool) Arch.abort → SailM Unit} {rs : RegFile}
    (h : loadCont cont (.impure (.ok (.memRead n va req)) KK) rs = true) :
    (classify req.access_kind).akIfetch = false ∧ (classify req.access_kind).akLatest = false ∧
      sdData.length = n ∧ cont (KK (.Ok (wordOfBytes n sdData, none))) rs = true := by
  simp only [loadCont, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

theorem storeContSpec {cont : SailM Unit → RegFile → Bool}
    {n va : Nat} {req : Mem_write_request n va Arch.pa Arch.translation Arch.arch_ak}
    {KK : Result (Option Bool) Arch.abort → SailM Unit} {rs : RegFile}
    (h : storeCont cont (.impure (.ok (.memWrite n va req)) KK) rs = true) :
    (classify req.access_kind).akLatest = false ∧ cont (KK (.Ok (some true))) rs = true := by
  simp only [storeCont, Bool.and_eq_true, Bool.not_eq_true'] at h
  exact h

/-- The pinned fetch of a `fetchCont` node returns the image's bytes. -/
theorem fetchNext {base : Int} {vs : List (BitVec 8)} {cont : SailM Unit → RegFile → Bool}
    {img : Image} (Himg : ∀ j : Nat, j < vs.length → img (base + j) = vs[j]?)
    {n va : Nat} {req : Mem_read_request n va Arch.pa Arch.translation Arch.arch_ak}
    {KK : Result (BitVec (8 * n) × Option Bool) Arch.abort → SailM Unit} {rs : RegFile}
    {tvs : List (Nat × BitVec 8)}
    (hram : fetchCont base vs cont (.impure (.ok (.memRead n va req)) KK) rs = true)
    (hlen : tvs.length = n) (hpin : WeakAxRealize.fetchPin img (.LIFetch (paZ req.pa) tvs)) :
    KK (.Ok (wordOfBytes n (tvs.map Prod.snd), none)) = KK (.Ok (wordOfBytes n vs, none)) ∧
      cont (KK (.Ok (wordOfBytes n vs, none))) rs = true := by
  obtain ⟨-, hb, hl, hc⟩ := fetchContSpec hram
  rw [hb] at hpin
  rw [AxCjrWpd.pinnedBytes img base tvs vs (by omega) Himg hpin]
  exact ⟨rfl, hc⟩

/-! ## The graph facts and the invariant step -/

/-- What `rstep`'s graphs must satisfy: hart 0's row has two items, the reload item at 1 reads
the spill (`graphValue`), and the image holds the four instruction texts. -/
structure GFacts (GD : Gdexec) : Prop where
  len : (AxOpsem.grow GD 0).length = 2
  ldRow : loadRowOk GD 0 1
  gv : graphValue GD (0, 1) = some sdData
  imgSd : AxEpiRetCert.imgAt GD (pcSd : Int) sdVs
  imgLd : AxEpiRetCert.imgAt GD (pcLd : Int) AxEpiLedger.ldVs
  imgJr : AxEpiRetCert.imgAt GD (pcJr : Int) cjrVs4
  imgTg : AxEpiRetCert.imgAt GD ((tgt.toNat : Nat) : Int) AxEpiRace2Run.h1Vs4

theorem rowEnd2 (G : Gdexec → Prop) (HG : ∀ GD, G GD → GFacts GD) (GD : Gdexec) (HGD : G GD)
    (lb : Lbl) : (AxOpsem.grow GD 0)[2]? = some lb → False := by
  intro h
  rw [List.getElem?_eq_none (Nat.le_of_eq (HG GD HGD).len)] at h
  cases h

theorem hQA : ∀ m rs, QA m rs = true → wq m = true := fun _ _ h => h

theorem hQB : ∀ m rs, QB m rs = true → wq m = true := by
  intro m rs h
  simp only [QB, Bool.and_eq_true] at h
  exact h.1

theorem invStep (G : Gdexec → Prop) (HG : ∀ GD, G GD → GFacts GD) (s s' : Athread) :
    Inv s → rstep G 0 s s' → Inv s' := by
  rintro ⟨cpu, m, rs, ib, k, rfl, Hw, HS⟩ Hst0
  have Hst' : awire ⟨.PHart cpu m rs none ib, k⟩ s' ∨
      progOrRead G ⟨.PHart cpu m rs none ib, k⟩ s' := by
    rcases Hst0 with Hp | Hwr | Hr
    · exact .inr (.inl Hp)
    · exact .inl Hwr
    · exact .inr (.inr Hr)
  rcases Hst' with Hwr | Hst
  · obtain ⟨hk, hp⟩ := awireAeqv _ _ Hwr
    obtain ⟨p', k'⟩ := s'
    simp only at hk hp
    subst hk
    match p', hp with
    | .PHart c m' rs' fn' ib', hp =>
      obtain ⟨rfl, rfl, rfl, rfl, hag⟩ := hp
      exact ⟨_, _, rs', _, _, rfl, fun r hr hp => (hag r hp).trans (Hw r hr hp),
        stageAgree _ _ rs rs' (regsAgreeSym _ _ _ hag) HS⟩
  match k, HS with
  | 0, .inl h =>
    obtain ⟨m', rs', ib', k', rfl, Hw', H⟩ := stageStep QA (fetchCont (pcSd : Int) sdVs sdB) _
      hQA (fun _ _ _ _ _ h => by simp [fetchCont] at h) G cpu m rs ib 0 h Hw s' Hst
    rcases H with ⟨rfl, Hc'⟩ | ⟨-, hr, -⟩ |
      ⟨rfl, rfl, GD, n, va, req, KK, tvs, HGD, rfl, hram, -, hlen, hpin, rfl⟩ |
      ⟨-, GD, n, va, req, KK, lb, v, HGD, rfl, hram, hnf, -⟩ |
      ⟨-, -, GD, n, va, req, KK, lb, HGD, rfl, hram, -⟩
    · exact ⟨cpu, m', rs', ib', 0, rfl, Hw', .inl Hc'⟩
    · exact absurd hr (by simp)
    · obtain ⟨he, hc⟩ := fetchNext (HG GD HGD).imgSd hram hlen hpin
      rw [he]
      exact ⟨cpu, _, _, ib', 0, rfl, Hw', .inr hc⟩
    · simp [fetchCont, hnf] at hram
    · simp [fetchCont] at hram
  | 0, .inr h =>
    obtain ⟨m', rs', ib', k', rfl, Hw', H⟩ := stageStep QA (storeCont sdC) _ hQA
      (fun _ _ _ _ _ h => (storeContSpec h).1) G cpu m rs ib 0 h Hw s' Hst
    rcases H with ⟨rfl, Hc'⟩ | ⟨-, hr, -⟩ |
      ⟨-, -, GD, n, va, req, KK, tvs, HGD, rfl, hram, -⟩ |
      ⟨-, GD, n, va, req, KK, lb, v, HGD, rfl, hram, -⟩ |
      ⟨rfl, rfl, GD, n, va, req, KK, lb, HGD, rfl, hram, -, rfl⟩
    · exact ⟨cpu, m', rs', ib', 0, rfl, Hw', .inr Hc'⟩
    · exact absurd hr (by simp)
    · simp [storeCont] at hram
    · simp [storeCont] at hram
    · exact ⟨cpu, _, _, ib', 1, rfl, Hw', .inl (storeContSpec hram).2⟩
  | 1, .inl h =>
    obtain ⟨m', rs', ib', k', rfl, Hw', H⟩ := stageStep QA (fun _ _ => false) (cut [Cld]) hQA
      (fun _ _ _ _ _ h => by simp at h) G cpu m rs ib 1 h Hw s' Hst
    rcases H with ⟨rfl, Hc'⟩ | ⟨rfl, hr, rfl, tk, rfl⟩ |
      ⟨-, -, GD, n, va, req, KK, tvs, HGD, rfl, hram, -⟩ |
      ⟨-, GD, n, va, req, KK, lb, v, HGD, rfl, hram, -⟩ |
      ⟨-, -, GD, n, va, req, KK, lb, HGD, rfl, hram, -⟩
    · exact ⟨cpu, m', rs', ib', 1, rfl, Hw', .inl Hc'⟩
    · obtain ⟨c, hc, hag⟩ := cutAgree [Cld] cldOff _ hr Hw'
      simp only [List.mem_singleton] at hc
      subst hc
      refine ⟨cpu, _, _, ib', 1, rfl, Hw', .inr (.inl ?_)⟩
      rw [← ldAIns _ _ _ hag]
      exact certLd tk
    · simp at hram
    · simp at hram
    · simp at hram
  | 1, .inr (.inl h) =>
    obtain ⟨m', rs', ib', k', rfl, Hw', H⟩ :=
      stageStep QA (fetchCont (pcLd : Int) AxEpiLedger.ldVs ldB) _ hQA
        (fun _ _ _ _ _ h => by simp [fetchCont] at h) G cpu m rs ib 1 h Hw s' Hst
    rcases H with ⟨rfl, Hc'⟩ | ⟨-, hr, -⟩ |
      ⟨rfl, rfl, GD, n, va, req, KK, tvs, HGD, rfl, hram, -, hlen, hpin, rfl⟩ |
      ⟨-, GD, n, va, req, KK, lb, v, HGD, rfl, hram, hnf, -⟩ |
      ⟨-, -, GD, n, va, req, KK, lb, HGD, rfl, hram, -⟩
    · exact ⟨cpu, m', rs', ib', 1, rfl, Hw', .inr (.inl Hc')⟩
    · exact absurd hr (by simp)
    · obtain ⟨he, hc⟩ := fetchNext (HG GD HGD).imgLd hram hlen hpin
      rw [he]
      exact ⟨cpu, _, _, ib', 1, rfl, Hw', .inr (.inr hc)⟩
    · simp [fetchCont, hnf] at hram
    · simp [fetchCont] at hram
  | 1, .inr (.inr h) =>
    obtain ⟨m', rs', ib', k', rfl, Hw', H⟩ := stageStep QA (loadCont ldC) _ hQA
      (fun _ _ _ _ _ h => by simp [loadCont] at h) G cpu m rs ib 1 h Hw s' Hst
    rcases H with ⟨rfl, Hc'⟩ | ⟨-, hr, -⟩ |
      ⟨-, -, GD, n, va, req, KK, tvs, HGD, rfl, hram, hfe, -⟩ |
      ⟨rfl, GD, n, va, req, KK, lb, v, HGD, rfl, hram, -, hlb, rfl, hgv, rfl⟩ |
      ⟨-, -, GD, n, va, req, KK, lb, HGD, rfl, hram, -⟩
    · exact ⟨cpu, m', rs', ib', 1, rfl, Hw', .inr (.inr Hc')⟩
    · exact absurd hr (by simp)
    · rw [(loadContSpec hram).1] at hfe
      exact Bool.noConfusion hfe
    · obtain ⟨-, -, -, hc⟩ := loadContSpec hram
      have F := HG GD HGD
      obtain ⟨lb', hlb', hadv⟩ := F.ldRow
      rw [hlb, Option.some.injEq] at hlb'
      subst hlb'
      rw [F.gv, Option.some.injEq] at hgv
      subst hgv
      rw [hadv]
      exact ⟨cpu, _, _, ib', 2, rfl, Hw', .inl hc⟩
    · simp [loadCont] at hram
  | 2, .inl h =>
    obtain ⟨m', rs', ib', k', rfl, Hw', H⟩ := stageStep QB exitRam (cut CjrL) hQB
      (fun _ _ _ _ _ h => by simpa [exitRam] using h) G cpu m rs ib 2 h Hw s' Hst
    rcases H with ⟨rfl, Hc'⟩ | ⟨rfl, hr, rfl, tk, rfl⟩ |
      ⟨-, -, GD, n, va, req, KK, tvs, HGD, rfl, hram, hfe, -⟩ |
      ⟨-, GD, n, va, req, KK, lb, v, HGD, -, -, -, hlb, -⟩ |
      ⟨-, -, GD, n, va, req, KK, lb, HGD, -, -, hlb, -⟩
    · exact ⟨cpu, m', rs', ib', 2, rfl, Hw', .inl Hc'⟩
    · obtain ⟨c, hc, hag⟩ := cutAgree CjrL cjrOff _ hr Hw'
      refine ⟨cpu, _, _, ib', 2, rfl, Hw', .inr (.inl ?_)⟩
      rw [← jrAIns _ _ _ hag]
      exact certJr c hc tk
    · simp [exitRam, hfe] at hram
    · exact (rowEnd2 G HG GD HGD lb hlb).elim
    · exact (rowEnd2 G HG GD HGD lb hlb).elim
  | 2, .inr (.inl h) =>
    obtain ⟨m', rs', ib', k', rfl, Hw', H⟩ := stageStep QB (fetchCont (pcJr : Int) cjrVs4 jrB) _
      hQB (fun _ _ _ _ _ h => by simp [fetchCont] at h) G cpu m rs ib 2 h Hw s' Hst
    rcases H with ⟨rfl, Hc'⟩ | ⟨-, hr, -⟩ |
      ⟨rfl, rfl, GD, n, va, req, KK, tvs, HGD, rfl, hram, -, hlen, hpin, rfl⟩ |
      ⟨-, GD, n, va, req, KK, lb, v, HGD, -, -, -, hlb, -⟩ |
      ⟨-, -, GD, n, va, req, KK, lb, HGD, -, -, hlb, -⟩
    · exact ⟨cpu, m', rs', ib', 2, rfl, Hw', .inr (.inl Hc')⟩
    · exact absurd hr (by simp)
    · obtain ⟨he, hc⟩ := fetchNext (HG GD HGD).imgJr hram hlen hpin
      rw [he]
      exact ⟨cpu, _, _, ib', 2, rfl, Hw', .inr (.inr (.inl hc))⟩
    · exact (rowEnd2 G HG GD HGD lb hlb).elim
    · exact (rowEnd2 G HG GD HGD lb hlb).elim
  | 2, .inr (.inr (.inl h)) =>
    obtain ⟨m', rs', ib', k', rfl, Hw', H⟩ := stageStep QB exitRam (cut CtgL) hQB
      (fun _ _ _ _ _ h => by simpa [exitRam] using h) G cpu m rs ib 2 h Hw s' Hst
    rcases H with ⟨rfl, Hc'⟩ | ⟨rfl, hr, rfl, tk, rfl⟩ |
      ⟨-, -, GD, n, va, req, KK, tvs, HGD, rfl, hram, hfe, -⟩ |
      ⟨-, GD, n, va, req, KK, lb, v, HGD, -, -, -, hlb, -⟩ |
      ⟨-, -, GD, n, va, req, KK, lb, HGD, -, -, hlb, -⟩
    · exact ⟨cpu, m', rs', ib', 2, rfl, Hw', .inr (.inr (.inl Hc'))⟩
    · obtain ⟨c, hc, hag⟩ := cutAgree CtgL ctgOff _ hr Hw'
      refine ⟨cpu, _, _, ib', 2, rfl, Hw', .inr (.inr (.inr (.inl ?_)))⟩
      rw [← tgAIns _ _ _ hag]
      exact certTg c hc tk
    · simp [exitRam, hfe] at hram
    · exact (rowEnd2 G HG GD HGD lb hlb).elim
    · exact (rowEnd2 G HG GD HGD lb hlb).elim
  | 2, .inr (.inr (.inr (.inl h))) =>
    obtain ⟨m', rs', ib', k', rfl, Hw', H⟩ := stageStep QB ramTg _ hQB
      (fun _ _ _ _ _ h => by simpa [ramTg, fetchCont, exitRam] using h) G cpu m rs ib 2 h Hw s'
      Hst
    rcases H with ⟨rfl, Hc'⟩ | ⟨-, hr, -⟩ |
      ⟨rfl, rfl, GD, n, va, req, KK, tvs, HGD, rfl, hram, hfe, hlen, hpin, rfl⟩ |
      ⟨-, GD, n, va, req, KK, lb, v, HGD, -, -, -, hlb, -⟩ |
      ⟨-, -, GD, n, va, req, KK, lb, HGD, -, -, hlb, -⟩
    · exact ⟨cpu, m', rs', ib', 2, rfl, Hw', .inr (.inr (.inr (.inl Hc')))⟩
    · exact absurd hr (by simp)
    · have hram' : fetchCont ((tgt.toNat : Nat) : Int) AxEpiRace2Run.h1Vs4 tgB
          (.impure (.ok (.memRead n va req)) KK) rs' = true := by
        simp only [ramTg, exitRam, hfe, Bool.not_true, Bool.or_false] at hram
        exact hram
      obtain ⟨he, hc⟩ := fetchNext (HG GD HGD).imgTg hram' hlen hpin
      rw [he]
      exact ⟨cpu, _, _, ib', 2, rfl, Hw', .inr (.inr (.inr (.inr hc)))⟩
    · exact (rowEnd2 G HG GD HGD lb hlb).elim
    · exact (rowEnd2 G HG GD HGD lb hlb).elim
  | 2, .inr (.inr (.inr (.inr h))) =>
    obtain ⟨m', rs', ib', k', rfl, Hw', H⟩ := stageStep QB exitRam _ hQB
      (fun _ _ _ _ _ h => by simpa [exitRam] using h) G cpu m rs ib 2 h Hw s' Hst
    rcases H with ⟨rfl, Hc'⟩ | ⟨-, hr, -⟩ |
      ⟨-, -, GD, n, va, req, KK, tvs, HGD, rfl, hram, hfe, -⟩ |
      ⟨-, GD, n, va, req, KK, lb, v, HGD, -, -, -, hlb, -⟩ |
      ⟨-, -, GD, n, va, req, KK, lb, HGD, -, -, hlb, -⟩
    · exact ⟨cpu, m', rs', ib', 2, rfl, Hw', .inr (.inr (.inr (.inr Hc')))⟩
    · exact absurd hr (by simp)
    · simp [exitRam, hfe] at hram
    · exact (rowEnd2 G HG GD HGD lb hlb).elim
    · exact (rowEnd2 G HG GD HGD lb hlb).elim
  | _ + 3, HS => exact HS.elim

theorem rtcInv (G : Gdexec → Prop) (HG : ∀ GD, G GD → GFacts GD) (s0 s : Athread) :
    Inv s0 → rtc (rstep G 0) s0 s → Inv s := by
  intro H0 Hr
  induction Hr with
  | refl => exact H0
  | tail _ hst ih => exact invStep G HG _ _ ih hst

theorem invStart (cpu : CPU) (ib : Ibch) :
    Inv ⟨.PHart cpu (riscvStep false) (probeRegs pcSd) none ib, 0⟩ :=
  ⟨cpu, _, _, ib, 0, rfl, fun _ _ _ => rfl, .inl certSd⟩

/-- At a boundary at the row end: PC is `pcJr` or the target. -/
theorem invGood (s : Athread) (HI : Inv s) (c : CPU) (tk : Bool) (rs' : RegFile) (ib' : Ibch)
    (Heq : s = ⟨.PHart c (riscvStep tk) rs' none ib', 2⟩) :
    rs' .PC = BitVec.ofNat 64 pcJr ∨ rs' .PC = tgt := by
  obtain ⟨cpu, m, rs, ib, k, rfl, -, HS⟩ := HI
  simp only [Athread.AThread.injEq, Pexv6.PHart.injEq] at Heq
  obtain ⟨⟨-, rfl, hrs, -, -⟩, rfl⟩ := Heq
  rw [← hrs]
  have hq : QB (riscvStep tk) rs = true := by
    rcases HS with h | h | h | h | h <;> exact chkQ _ _ _ _ _ h
  simp only [QB, Bool.and_eq_true, Bool.or_eq_true, pcEqb, decide_eq_true_eq] at hq
  obtain ⟨-, (h | h) | ⟨h0, h1⟩⟩ := hq
  · exact .inl h
  · exact .inr h
  · cases tk
    · rw [divergeSelf] at h0
      exact absurd h0 Bool.false_ne_true
    · rw [divergeSelf] at h1
      exact absurd h1 Bool.false_ne_true

end AxEpiRet

/-! # 4. AT `axGA2`: the reload read the spill, and the PC at the post-c.jr boundary -/

/-- The post: at the row end (position 2), the reload read the spill. -/
def epiRetPost (GD : Gdexec) (i : Agent) (s : Athread) : Prop :=
  i = 0 → s.atK = 2 → graphValue GD (0, 1) = some sdData

/-- The register post: at an INSTRUCTION BOUNDARY at the row end reached after the c.jr
(deviation 1: PC ≠ `pcJr`), PC is the jump target of the spilled word. -/
def epiRetPcPost (i : Agent) (s : Athread) : Prop :=
  i = 0 → ∀ (c : CPU) (tk : Bool) (rs : RegFile) (ib : Ibch),
    s = ⟨.PHart c (riscvStep tk) rs none ib, 2⟩ → rs .PC ≠ BitVec.ofNat 64 pcJr →
    rs .PC = jalrTarget sdWord

def epiRetPost2 (GD : Gdexec) (i : Agent) (s : Athread) : Prop :=
  epiRetPost GD i s ∧ epiRetPcPost i s

theorem postRaSymSeip (r : BitVec 64) (rs rs' : RegFile) :
    regsAgree AxRunClose.pinReg rs rs' → postRaSym r rs = postRaSym r rs' := by
  intro hag
  unfold postRaSym
  rw [hag .PC (AxEpiRet.notPin _ (by decide))]

/-- FORWARD REACHABILITY ⇒ PC (deviation 1: from hart 0's START, over the staged region): every
state reachable by `rstep G 0` (at graphs with `AxEpiRet.GFacts`) from the start that is an
instruction boundary at the row end with PC ≠ `pcJr` has PC = `jalrTarget sdWord`. -/
theorem epiRetReachPc (G : Gdexec → Prop) (HG : ∀ GD, G GD → AxEpiRet.GFacts GD) (cpu : CPU)
    (ib : Ibch) (s : Athread) :
    rtc (rstep G 0) ⟨.PHart cpu (riscvStep false) (probeRegs pcSd) none ib, 0⟩ s →
    ∀ (c : CPU) (tk : Bool) (rs' : RegFile) (ib' : Ibch),
      s = ⟨.PHart c (riscvStep tk) rs' none ib', 2⟩ → rs' .PC ≠ BitVec.ofNat 64 pcJr →
      rs' .PC = jalrTarget sdWord := by
  intro Hr c tk rs' ib' Heq Hne
  rcases AxEpiRet.invGood s (AxEpiRet.rtcInv G HG _ _ (AxEpiRet.invStart cpu ib) Hr) c tk rs' ib'
    Heq with h | h
  · exact absurd h Hne
  · exact h

section ga2Ret
variable {hlc : HasLC} {GF : BundledGFunctors.{0,0,0}} [InvGS_gen hlc GF] [AxannotGS GF]
  [AxlogG GF Hent] [pol : Axpol]

/-- The per-hart `wpd` at `axGA2`, `Φ := ⌜epiRetPost2 GD0 0 ·⌝`. -/
theorem wpdEpiRetGa2 (GD0 : Gdexec) (γ : GName) (cpu : CPU) (ib : Ibch) (a : Int)
    (Hgd_sd : AxCjrWpd.fetchImgOk GD0 0 0 pcSd sdVs)
    (Hrow_sd : storeRowOk GD0 0 0)
    (Hw_sd : sdWriteOk GD0 0 0 a)
    (Hgd_ld : AxCjrWpd.fetchImgOk GD0 0 1 pcLd AxEpiLedger.ldVs)
    (Hrow_ld : loadRowOk GD0 0 1)
    (Hok_ld : ldspOwnOk GD0 0 1 (0, 0) a (writenHist (0, 0) sdData epiHs0))
    (Hgd_jr : AxEpiRetCert.imgAt GD0 (pcJr : Int) cjrVs4)
    (Hgd_tg : AxEpiRetCert.imgAt GD0 ((jalrTarget sdWord).toNat : Int) AxEpiRace2Run.h1Vs4)
    (Hlen : (AxOpsem.grow GD0 0).length = 2) :
    ⊢ ([∗list] j ↦ H ∈ epiHs0, histAuth (GF := GF) γ (a + (j : Int)) 1 H) -∗
      @wpd hlc GF _ (epiGa2 GD0 γ) pol .MaybeStuck 0
        ⟨.PHart cpu (riscvStep false) (probeRegs pcSd) none ib, 0⟩
        (fun s => iprop(⌜epiRetPost2 GD0 0 s⌝)) := by
  have hg : ∀ GD', AxirisG.gconstInterp (self := epiGa2 (GF := GF) GD0 γ) GD' ⊢ ⌜GD' = GD0⌝ := by
    intro GD'
    show iprop(⌜GD' = GD0⌝) ⊢ iprop(⌜GD' = GD0⌝)
    iintro %h
    ipureintro
    exact h
  have Hpre : ⊢ ∀ (GD : Gdexec) (s1 : Athread), ⌜s1.atK ≤ 1⌝ -∗
      ⌜s1.atK = (AxOpsem.grow GD 0).length⌝ -∗
      @postLifting GF (epiGa2 GD0 γ) (fun s => iprop(⌜epiRetPost2 GD0 0 s⌝)) 0 s1 := by
    iintro %GD %s1 %Hle %_
    iapply (@postLiftingTrue GF (epiGa2 GD0 γ) pol (fun s => iprop(⌜epiRetPost2 GD0 0 s⌝)) 0 s1)
    iintro _
    ipureintro
    refine And.intro (fun _ h => absurd h (by omega)) (fun _ c tk rs ib' he _ => ?_)
    subst he
    simp at Hle
  have Hpost : ⊢ ∀ w, ldRbv (axG := epiGa2 GD0 γ) 0 1 sdData w -∗
      ∀ (GD : Gdexec) (s1 : Athread), ⌜s1.atK = (AxOpsem.grow GD 0).length⌝ -∗
        @postLifting GF (epiGa2 GD0 γ) (fun s' => iprop(⌜rtc (rstep (fun GD => GD = GD0) 0)
          ⟨.PHart cpu (riscvStep false) (probeRegs pcSd) none ib, 0⟩ s'⌝ -∗
            ⌜epiRetPost2 GD0 0 s'⌝)) 0 s1 := by
    unfold ldRbv
    iintro %w ⟨%GD', Hfrag, %Hgv, #Hg⟩ %GD %s1 %_
    ihave %HGD := hg GD' $$ Hg
    rw [HGD] at Hgv
    unfold postLifting
    iintro %na Hna
    have hag : AxirisG.annotInterp (self := epiGa2 (GF := GF) GD0 γ) na ∗
        AxAnnot.annotOwn (0, 1) iprop(⌜w = sdData⌝) ⊢
        iprop(⌜(0, 1) ∈ (FiniteMap.dom_set na : GSet Geid)⌝ ∗
          AxWp.fromOption (fun P' => iprop(▷ □ (P' -∗ ⌜w = sdData⌝))) iprop(emp)
            (get? na (0, 1))) := by
      iintro ⟨Hna, Hp⟩
      iapply annotAgree na (0, 1) iprop(⌜w = sdData⌝) $$ Hna Hp
    cases hget : get? na (0, 1) with
    | none =>
      rw [hget] at hag
      simp only [AxWp.fromOption] at hag
      icases persistent_entails_left hag $$ [$Hna $Hfrag] with ⟨-, %Hdom, -⟩
      have h := elemOfDom.1 Hdom
      rw [hget] at h
      cases h
    | some P0 =>
      rw [hget] at hag
      simp only [AxWp.fromOption] at hag
      icases persistent_entails_left hag $$ [$Hna $Hfrag] with ⟨⟨Hna, -⟩, %Hdom, #Hw⟩
      imodintro
      isplitl [Hna]
      · iexact Hna
      iintro Hbig
      have Hlk : ([∗map] e ↦ R ∈ na, if e.1 = 0 then R else iprop(True)) ⊢ P0 :=
        (BigSepM.bigSepM_lookup (Φ := fun e R => if e.1 = 0 then R else iprop(True)) hget).trans
          (by dsimp only; rw [if_pos rfl])
      ihave HP0 := Hlk $$ Hbig
      inext
      ihave Hpp := Hw $$ HP0
      icases Hpp with %Hv
      imodintro
      iintro %HR
      ipureintro
      rw [Hv] at Hgv
      have F : AxEpiRet.GFacts GD0 :=
        ⟨Hlen, Hrow_ld, Hgv, Hgd_sd.2, Hgd_ld.2, Hgd_jr, Hgd_tg⟩
      exact And.intro (fun _ _ => Hgv)
        (fun _ c tk rs ib' he hne => epiRetReachPc (fun GD => GD = GD0)
          (fun GD h => by subst h; exact F) cpu ib s1 HR c tk rs ib' he hne)
  iintro Hauths
  iapply (wpdEpiRetOwnedRb (axG := epiGa2 GD0 γ) γ (obEqGa2 GD0 γ) (annEqGa2 GD0 γ) 0 _ cpu ib
    a epiHs0
    (pinGa2 GD0 γ (fun GD => AxCjrWpd.fetchImgOk GD 0 0 pcSd sdVs) Hgd_sd)
    (pinGa2 GD0 γ (fun GD => storeRowOk GD 0 0) Hrow_sd)
    (pinGa2 GD0 γ (fun GD => sdWriteOk GD 0 0 a) Hw_sd)
    (fun GD ls _ => locGa2 GD0 γ GD 0 0 ls)
    (pinGa2 GD0 γ (fun GD => AxCjrWpd.fetchImgOk GD 0 1 pcLd AxEpiLedger.ldVs) Hgd_ld)
    (pinGa2 GD0 γ (fun GD => loadRowOk GD 0 1) Hrow_ld)
    (pinGa2 GD0 γ (fun GD => ldspOwnOk GD 0 1 (0, 0) a (writenHist (0, 0) sdData epiHs0))
      Hok_ld)
    (fun GD ls _ => locGa2' GD0 γ GD 0 1 ls) rfl
    (pinGa2 GD0 γ (fun GD => (AxOpsem.grow GD 0).length = 2) Hlen)
    (fun GD => GD = GD0) (fun GD _ => hg GD)) $$ Hauths [] []
  · iapply Hpre
  · iapply Hpost

end ga2Ret

/-! # 5. ADEQUACY: 2 harts, the capstone's premises -/

theorem epiRetAdeq (GD : Gdexec) (cpu : CPU) (a b : Int)
    (Hdisj : slotsDisjoint a b)
    (Hcons : rvwmoCatConsistent GD)
    (Hharts : ∀ e, e ∈ GD.gdG.gxGmo → e.1 = 0 ∨ e.1 = 1)
    (Hgd_sd : AxCjrWpd.fetchImgOk GD 0 0 pcSd sdVs)
    (Hrow_sd : storeRowOk GD 0 0)
    (Hw_sd : sdWriteOk GD 0 0 a)
    (Hgd_ld : AxCjrWpd.fetchImgOk GD 0 1 pcLd AxEpiLedger.ldVs)
    (Hrow_ld : loadRowOk GD 0 1)
    (Hok_ld : @ldspOwnOk epiPol GD 0 1 (0, 0) a (writenHist (0, 0) sdData epiHs0))
    (Hgd_jr : AxEpiRetCert.imgAt GD (pcJr : Int) cjrVs4)
    (Hgd_tg : AxEpiRetCert.imgAt GD ((jalrTarget sdWord).toNat : Int) AxEpiRace2Run.h1Vs4)
    (Hlen0 : (AxOpsem.grow GD 0).length = 2)
    (Hlob_gmo : gmoLt GD.gdG (0, 0) (0, 1))
    (sN : Athread) (n : Nat)
    (Hrun0 : ∀ (_ : AxannotGS epiGF) (nm : GName),
      nsteps (tierAAstep GD nm 0) n
        ⟨.PHart cpu (riscvStep false) (probeRegs pcSd) none ibNone, 0⟩ sN)
    (Hend : sN.atK = (AxOpsem.grow GD 0).length)
    (s0_1 sN1 : Athread) (n1 : Nat)
    (Hk1 : s0_1.atK = 0)
    (Hrun1 : ∀ (_ : AxannotGS epiGF) (nm : GName), nsteps (tierAAstep GD nm 1) n1 s0_1 sN1)
    (Hend1 : sN1.atK = (AxOpsem.grow GD 1).length)
    (Hwp1 : ∀ [InvGS_gen .hasNoLC epiGF] [AxannotGS epiGF] (nm : GName),
      ⊢ epiInit3 a b nm 1 -∗
        @tierAWpd epiGF .hasNoLC _ _ epiPol GD GName Unit epiObInterp nm s0_1 .MaybeStuck 1
          (fun _ => iprop(True))) :
    epiRetPost2 GD 0 sN := by
  let s00 : Athread := ⟨.PHart cpu (riscvStep false) (probeRegs pcSd) none ibNone, 0⟩
  let s0 : Agent → Athread := fun i => if i = 0 then s00 else s0_1
  let sNf : Agent → Athread := fun i => if i = 0 then sN else sN1
  let nf : Agent → Nat := fun i => if i = 0 then n else n1
  have Hin01 : ∀ i : Agent, i ∈ [0, 1] → i = 0 ∨ i = 1 := by
    intro i Hi
    simp only [List.mem_cons, List.not_mem_nil, _root_.or_false] at Hi
    exact Hi
  have Hharts' : ∀ e, e ∈ GD.gdG.gxGmo → e.1 ∈ [0, 1] := by
    intro e He
    rcases Hharts e He with h | h <;> rw [h] <;> simp
  have Hs_pol : ∀ e e', e' ∈ Axpol.sPol (self := epiPol) GD e → gmoLt GD.gdG e' e :=
    fun e e' he' => gmoPrefixGmoLt _ Hcons.1 e e' (elemOfListToSet.1 he')
  have Hlobp : ∀ e e', e' ∈ Axpol.lobp (self := epiPol) GD e → gmoLt GD.gdG e' e := by
    intro e e' he'
    change e' ∈ epiLobp GD e at he'
    unfold epiLobp at he'
    split at he'
    · rename_i heq
      subst heq
      have h1 := elemOfSingleton.1 (elemOfIntersection.1 he').1
      subst h1
      exact Hlob_gmo
    · exact absurd he' notElemOfEmpty
  have HrunA : ∀ (Hann : AxannotGS epiGF) (nm : GName) i, i ∈ [0, 1] →
      nsteps (tierAAstep GD nm i) (nf i) (s0 i) (sNf i) := by
    intro Hann nm i Hi
    rcases Hin01 i Hi with rfl | rfl
    · exact Hrun0 Hann nm
    · exact Hrun1 Hann nm
  have Hk0 : ∀ i, i ∈ [0, 1] → (s0 i).atK = 0 := by
    intro i Hi
    rcases Hin01 i Hi with rfl | rfl
    · rfl
    · exact Hk1
  have HendA : ∀ i, i ∈ [0, 1] → (sNf i).atK = (AxOpsem.grow GD i).length := by
    intro i Hi
    rcases Hin01 i Hi with rfl | rfl
    · exact Hend
    · exact Hend1
  have Hwp : ∀ [InvGS_gen .hasNoLC epiGF] [AxannotGS epiGF] (nm : GName),
      ⊢ ([∗list] i ∈ [0, 1], epiInit3 a b nm i) -∗
        [∗list] i ∈ [0, 1],
          @tierAWpd epiGF .hasNoLC _ _ epiPol GD GName Unit epiObInterp nm (s0 i) .MaybeStuck i
            (fun s => iprop(⌜epiRetPost2 GD i s⌝)) := by
    intro _ _ nm
    have HA : ⊢ ([∗list] j ↦ H ∈ epiHs0, histAuth (GF := epiGF) nm (a + (j : Int)) 1 H) -∗
        @tierAWpd epiGF .hasNoLC _ _ epiPol GD GName Unit epiObInterp nm (s0 0) .MaybeStuck 0
          (fun s => iprop(⌜epiRetPost2 GD 0 s⌝)) := by
      have h := wpdEpiRetGa2 (hlc := .hasNoLC) (GF := epiGF) (pol := epiPol) GD nm cpu ibNone a
        Hgd_sd Hrow_sd Hw_sd Hgd_ld Hrow_ld Hok_ld Hgd_jr Hgd_tg Hlen0
      unfold tierAWpd
      exact h
    have HB : ⊢ epiInit3 a b nm 1 -∗
        @tierAWpd epiGF .hasNoLC _ _ epiPol GD GName Unit epiObInterp nm (s0 1)
        .MaybeStuck 1 (fun s => iprop(⌜epiRetPost2 GD 1 s⌝)) := by
      have h := Hwp1 nm
      unfold tierAWpd at h
      unfold tierAWpd
      exact h.trans (wand_mono .rfl (@wpdMono .hasNoLC epiGF _
        (axGA2 GD GName Unit epiObInterp nm) epiPol _ _ _
        _ _ (fun _ => pure_intro (And.intro (fun h => absurd h (by decide))
          (fun h => absurd h (by decide))))))
    iintro Hi
    ihave Hi := BigSepL.bigSepL_cons.1 $$ Hi
    icases Hi with ⟨Hi0, Hi1⟩
    ihave Hi1 := BigSepL.bigSepL_singleton.1 $$ Hi1
    ihave Hi0 := (AxEpiSound3.epiInit3Zero a b nm).1 $$ Hi0
    iapply BigSepL.bigSepL_cons.2
    isplitl [Hi0]
    · iapply HA $$ Hi0
    iapply BigSepL.bigSepL_singleton.2
    iapply HB $$ Hi1
  have Hfin := @tierAAdequacyAnnGmo epiGF _ _ epiPol GD GName Unit epiObInterp (epiInit3 a b)
    epiAxpolWf Hcons [0, 1] (by decide) Hharts' s0 sNf nf HrunA Hk0 HendA
    (epiRetPost2 GD) Hwp (epiHobAlloc3 a b Hdisj GD) Hs_pol Hlobp 0 (by simp)
  exact Hfin

theorem epiRetReloadSound (GD : Gdexec) (cpu : CPU) (a b : Int)
    (Hdisj : slotsDisjoint a b)
    (Hcons : rvwmoCatConsistent GD)
    (Hharts : ∀ e, e ∈ GD.gdG.gxGmo → e.1 = 0 ∨ e.1 = 1)
    (Hgd_sd : AxCjrWpd.fetchImgOk GD 0 0 pcSd sdVs)
    (Hrow_sd : storeRowOk GD 0 0)
    (Hw_sd : sdWriteOk GD 0 0 a)
    (Hgd_ld : AxCjrWpd.fetchImgOk GD 0 1 pcLd AxEpiLedger.ldVs)
    (Hrow_ld : loadRowOk GD 0 1)
    (Hok_ld : @ldspOwnOk epiPol GD 0 1 (0, 0) a (writenHist (0, 0) sdData epiHs0))
    (Hgd_jr : AxEpiRetCert.imgAt GD (pcJr : Int) cjrVs4)
    (Hgd_tg : AxEpiRetCert.imgAt GD ((jalrTarget sdWord).toNat : Int) AxEpiRace2Run.h1Vs4)
    (Hlen0 : (AxOpsem.grow GD 0).length = 2)
    (Hlob_gmo : gmoLt GD.gdG (0, 0) (0, 1))
    (sN : Athread) (n : Nat)
    (Hrun0 : ∀ (_ : AxannotGS epiGF) (nm : GName),
      nsteps (tierAAstep GD nm 0) n
        ⟨.PHart cpu (riscvStep false) (probeRegs pcSd) none ibNone, 0⟩ sN)
    (Hend : sN.atK = (AxOpsem.grow GD 0).length)
    (s0_1 sN1 : Athread) (n1 : Nat)
    (Hk1 : s0_1.atK = 0)
    (Hrun1 : ∀ (_ : AxannotGS epiGF) (nm : GName), nsteps (tierAAstep GD nm 1) n1 s0_1 sN1)
    (Hend1 : sN1.atK = (AxOpsem.grow GD 1).length)
    (Hwp1 : ∀ [InvGS_gen .hasNoLC epiGF] [AxannotGS epiGF] (nm : GName),
      ⊢ epiInit3 a b nm 1 -∗
        @tierAWpd epiGF .hasNoLC _ _ epiPol GD GName Unit epiObInterp nm s0_1 .MaybeStuck 1
          (fun _ => iprop(True))) :
    graphValue GD (0, 1) = some sdData :=
  (epiRetAdeq GD cpu a b Hdisj Hcons Hharts Hgd_sd Hrow_sd Hw_sd Hgd_ld Hrow_ld Hok_ld Hgd_jr
    Hgd_tg Hlen0 Hlob_gmo sN n Hrun0 Hend s0_1 sN1 n1 Hk1 Hrun1 Hend1 Hwp1).1 rfl
    (by rw [Hend, Hlen0])

/-! # 6. Consequences at the `AxEpiRetCert` certificates -/

/-- The capstone's premise list (boundary form `Hend0`, `Hafter`) implies the reload read the
spill. -/
theorem epiRetStmtPremisesReload (GD : Gdexec) (cpu : CPU) (a b : Int)
    (Hdisj : slotsDisjoint a b)
    (Hcons : rvwmoCatConsistent GD)
    (Hharts : ∀ e, e ∈ GD.gdG.gxGmo → e.1 = 0 ∨ e.1 = 1)
    (Hgd_sd : AxCjrWpd.fetchImgOk GD 0 0 pcSd sdVs)
    (Hrow_sd : storeRowOk GD 0 0)
    (Hw_sd : sdWriteOk GD 0 0 a)
    (Hgd_ld : AxCjrWpd.fetchImgOk GD 0 1 pcLd AxEpiLedger.ldVs)
    (Hrow_ld : loadRowOk GD 0 1)
    (Hok_ld : @ldspOwnOk epiPol GD 0 1 (0, 0) a (writenHist (0, 0) sdData epiHs0))
    (Hgd_jr : AxEpiRetCert.imgAt GD (pcJr : Int) cjrVs4)
    (Hgd_tg : AxEpiRetCert.imgAt GD ((jalrTarget sdWord).toNat : Int) AxEpiRace2Run.h1Vs4)
    (Hlen0 : (AxOpsem.grow GD 0).length = 2)
    (Hlob_gmo : gmoLt GD.gdG (0, 0) (0, 1))
    (sN : Athread) (n : Nat)
    (Hrun0 : ∀ (_ : AxannotGS epiGF) (nm : GName),
      nsteps (tierAAstep GD nm 0) n
        ⟨.PHart cpu (riscvStep false) (probeRegs pcSd) none ibNone, 0⟩ sN)
    (tk : Bool) (rsN : RegFile) (ibN : Ibch)
    (Hend0 : sN = ⟨.PHart cpu (riscvStep tk) rsN none ibN, 2⟩)
    (_Hafter : rsN .PC ≠ BitVec.ofNat 64 pcJr)
    (s0_1 sN1 : Athread) (n1 : Nat)
    (Hk1 : s0_1.atK = 0)
    (Hrun1 : ∀ (_ : AxannotGS epiGF) (nm : GName), nsteps (tierAAstep GD nm 1) n1 s0_1 sN1)
    (Hend1 : sN1.atK = (AxOpsem.grow GD 1).length)
    (Hwp1 : ∀ [InvGS_gen .hasNoLC epiGF] [AxannotGS epiGF] (nm : GName),
      ⊢ epiInit3 a b nm 1 -∗
        @tierAWpd epiGF .hasNoLC _ _ epiPol GD GName Unit epiObInterp nm s0_1 .MaybeStuck 1
          (fun _ => iprop(True))) :
    graphValue GD (0, 1) = some sdData :=
  epiRetReloadSound GD cpu a b Hdisj Hcons Hharts Hgd_sd Hrow_sd Hw_sd Hgd_ld Hrow_ld Hok_ld
    Hgd_jr Hgd_tg Hlen0 Hlob_gmo sN n Hrun0 (by rw [Hend0, Hlen0]) s0_1 sN1 n1 Hk1 Hrun1 Hend1
    Hwp1

/-- UNCONDITIONAL refutation of the racing hart's WPd at `raceRet` (every other premise holds
there, and the reload reads `raceData`). -/
theorem raceRetNoWpd1 (cpu : CPU) :
    ¬ (∀ [InvGS_gen .hasNoLC epiGF] [AxannotGS epiGF] (nm : GName),
      ⊢ epiInit3 ldAddr race2B nm 1 -∗
        @tierAWpd epiGF .hasNoLC _ _ epiPol raceRet GName Unit epiObInterp nm
          (h1rState cpu) .MaybeStuck 1 (fun _ => iprop(True))) := by
  intro Hwp1
  obtain ⟨sN, n, tk, rsN, ibN, sN1, n1, Hdisj, Hcons, Hharts, Hgd_sd, Hrow_sd, Hw_sd, Hgd_ld,
    Hrow_ld, Hok_ld, Hgd_jr, Hgd_tg, Hlen0, Hlob, Hrun0, Hend0, Hafter, Hk1, Hrun1, Hend1,
    -⟩ := raceRetPremisesButNotConcl cpu
  have H := epiRetStmtPremisesReload raceRet cpu ldAddr race2B Hdisj Hcons Hharts Hgd_sd Hrow_sd
    Hw_sd Hgd_ld Hrow_ld Hok_ld Hgd_jr Hgd_tg Hlen0 Hlob sN n Hrun0 tk rsN ibN Hend0 Hafter
    (h1rState cpu) sN1 n1 Hk1 Hrun1 Hend1 Hwp1
  rw [raceRetValue, Option.some.injEq] at H
  exact absurd H (by decide)

/-! # 8. THE CAPSTONE, through the forward-precise WPd (`AxCjrReach`) -/

theorem epiRetSound2 : epiRetSound2Stmt := by
  intro GD cpu a b Hdisj Hcons Hharts Hgd_sd Hrow_sd Hw_sd Hgd_ld Hrow_ld Hok_ld Hgd_jr Hgd_tg
    Hlen0 Hlob_gmo sN n Hrun0 tk rsN ibN Hend0 Hafter s0_1 sN1 n1 Hk1 Hrun1 Hend1 Hwp1
  have Hend : sN.atK = (AxOpsem.grow GD 0).length := by rw [Hend0, Hlen0]
  exact (epiRetAdeq GD cpu a b Hdisj Hcons Hharts Hgd_sd Hrow_sd Hw_sd Hgd_ld Hrow_ld Hok_ld
    Hgd_jr Hgd_tg Hlen0 Hlob_gmo sN n Hrun0 Hend s0_1 sN1 n1 Hk1 Hrun1 Hend1 Hwp1).2 rfl cpu tk
    rsN ibN Hend0 Hafter

end Weak
