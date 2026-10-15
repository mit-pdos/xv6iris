/-
Weak: **W9a (B) B5 cycRun — the table glue: `cycRun` from `hartConf` modulo the per-instruction
facts** ([OWN.85] Q-B5-CYCLE = C1; report `PROGRESS-cycRun.md`).  Lean-only.

* `walkNw`: at every reached non-pin walk state the decoded role has no `mip`/`mtime`
  destination (`dfNwRole`), checked over B5's generated table (`Weak/PinWalkTab.lean`) by
  `decide +kernel`;
* `cySailOfWalk`: the Sail cycle fact `cySailAt` at a reached non-pin state from the two
  per-instruction facts (`fetchCyR1`, `execCyAt`) — `cySailOf` with the table's decode
  (`walkDec`), text bounds (`walkText`) and `walkNw`;
* `cycRunOfHartConfI`: `cycRunOfHartConf` (`Weak/PinCycRunAsm.lean`) with its Sail premise so
  discharged.

Every helper is `Weak.PinCycRun.*`.
-/
import Weak.PinCycRunCyc3

namespace Weak

open MachCSL KernelPinsDef LeanRV64D
open WeakRvwmoPinBridge3 (preach)
open WeakRvwmoPinBridge4 (walkOwn)
open PinWalkTab

namespace PinCycRun
open PinDataflow

/-- `dfNwRole`, decided. -/
def dfNwRoleB (ro : OpRoles) : Bool :=
  (dfDests ro).all (fun p => p.1 != wcsr MIP && p.1 != wcsr TIME)

theorem PinCycRun.dfNwRoleOfB (ro : OpRoles) (h : dfNwRoleB ro = true) : dfNwRole ro := by
  intro p hp
  have := List.all_eq_true.mp h p hp
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at this
  exact this

/-- The per-state check: a non-pin state's role has no `mip`/`mtime` destination. -/
def nwOk (own : Bool) (s : PState) : Bool :=
  match pstep own s with
  | some (_ :: _) => dfNwRoleB (krole s.psPc)
  | _ => true

/-- The row check. -/
def nwRowOk (r : WRow) : Bool := r.wSts.all (nwOk r.wOwn)

theorem nwRowsOk0 : walkRows0.all nwRowOk = true := by decide +kernel
theorem nwRowsOk1 : walkRows1.all nwRowOk = true := by decide +kernel
theorem nwRowsOk2 : walkRows2.all nwRowOk = true := by decide +kernel
theorem nwRowsOk3 : walkRows3.all nwRowOk = true := by decide +kernel
theorem nwRowsOk4 : walkRows4.all nwRowOk = true := by decide +kernel
theorem nwRowsOk5 : walkRows5.all nwRowOk = true := by decide +kernel
theorem nwRowsOk6 : walkRows6.all nwRowOk = true := by decide +kernel
theorem nwRowsOk7 : walkRows7.all nwRowOk = true := by decide +kernel
theorem nwRowsOk8 : walkRows8.all nwRowOk = true := by decide +kernel
theorem nwRowsOk9 : walkRows9.all nwRowOk = true := by decide +kernel
theorem nwRowsOk10 : walkRows10.all nwRowOk = true := by decide +kernel
theorem nwRowsOk11 : walkRows11.all nwRowOk = true := by decide +kernel

theorem nwRowsOk : walkRows.all nwRowOk = true := by
  simp only [walkRows, List.all_append, nwRowsOk0, nwRowsOk1, nwRowsOk2, nwRowsOk3, nwRowsOk4,
    nwRowsOk5, nwRowsOk6, nwRowsOk7, nwRowsOk8, nwRowsOk9, nwRowsOk10, nwRowsOk11, Bool.and_self]

/-- **`dfNwRole` AT EVERY REACHED NON-PIN STATE** (header). -/
theorem walkNw (pc : Int) (w : Pin) (own : Bool) (x : PState) (n : Nat) (l : List PState) :
    (pc, w) ∈ pinsW9a → walkOwn w = some own → preach own (pinStart pc) x n →
    pstep own x = some l → l ≠ [] → dfNwRole (krole x.psPc) := by
  intro hm hw hx hp hne
  have hin : (pc, own) ∈ walkRows.map (fun r => (r.wPc, r.wOwn)) := by
    rw [walkRowsCover]
    exact List.mem_filterMap.2 ⟨(pc, w), hm, by simp [hw]⟩
  obtain ⟨r, hr, he⟩ := List.mem_map.1 hin
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  have hrow := List.all_eq_true.mp walkRowsOk r hr
  unfold rowOk at hrow
  rw [Bool.and_eq_true] at hrow
  obtain ⟨h0, h1⟩ := hrow
  obtain ⟨y, hy, hey⟩ := List.any_eq_true.mp h0
  have hst : pinStart r.wPc ∈ r.wSts := by
    rw [WeakRvwmoPinBridge3.pstateEqbEq _ _ hey]; exact hy
  have hall := List.all_eq_true.mp h1
  have hx' := PinWalkTab.closedReach r.wOwn r.wSts
    (fun s hs => (Bool.and_eq_true _ _ ▸ hall s hs).2) _ x n hx hst
  have hnw := List.all_eq_true.mp (List.all_eq_true.mp nwRowsOk r hr) x hx'
  unfold nwOk at hnw
  rw [hp] at hnw
  cases l with
  | nil => exact absurd rfl hne
  | cons a l => exact PinCycRun.dfNwRoleOfB _ hnw

/-- **THE SAIL CYCLE FACT AT A REACHED NON-PIN STATE** (header), from the two per-instruction
facts. -/
theorem cySailOfWalk (pc : Int) (w : Pin) (own : Bool) (x : PState) (n : Nat) (l : List PState)
    (hm : (pc, w) ∈ pinsW9a) (hw : walkOwn w = some own) (hx : preach own (pinStart pc) x n)
    (hp : pstep own x = some l) (hne : l ≠ [])
    (hfetch : fetchCyR1 x.psPc) (hexec : execCyAt x.psPc) : cySailAt x.psPc := by
  obtain ⟨a, hdec, -⟩ := walkDec pc w own x n l hm hw hx hp hne
  exact cySailOf x.psPc (walkText pc w own x n l hm hw hx hp hne) a hdec hfetch hexec
    (walkNw pc w own x n l hm hw hx hp hne)

/-- **`cycRun` FROM `hartConf`, the Sail premise reduced to the per-instruction facts**
(header): `cycRunOfHartConf` with `cySailAt` discharged by `cySailOfWalk` — the remaining
premises: r1 at the cycle (`fetchCyR1`), the execute stage (`execCyAt`), the run obligations
`fetchOkR2` / `dataOkR` / `excRetR`, and the walk start. -/
theorem cycRunOfHartConfI (G : Gexec) (i : Nat) (row : List Lbl) (p0 : Pexv6) (dv : Nat → Efab)
    (em : Hemission) (pcL : Int) (w : Pin) (own : Bool)
    (hcf : hartConf i row p0 dv em) (hm : (pcL, w) ∈ pinsW9a) (hw : walkOwn w = some own)
    (hft : kFetchText em)
    (hR1 : ∀ s n l, preach own (pinStart pcL) s n → pstep own s = some l → l ≠ [] →
      fetchCyR1 s.psPc)
    (hEx : ∀ s n l, preach own (pinStart pcL) s n → pstep own s = some l → l ≠ [] →
      execCyAt s.psPc)
    (hfetch : ∀ s n, preach own (pinStart pcL) s n → fetchOkRF p0 (dv 0) em s.psPc)
    (hdata : ∀ s n, preach own (pinStart pcL) s n → dataOkRF p0 (dv 0) em s.psPc)
    (hexc : ∀ s n, preach own (pinStart pcL) s n → excRetR G i p0 (dv 0) em s.psPc)
    (base rest : List Eitem) (hes : em.emItems = base ++ rest)
    (hstart : ∀ p d, pevrun (base.map Prod.fst) p0 (dv 0) p d →
      ∃ (cpu : CPU) (rs : RegFile) (fn : Option (Bool × Bool × Bool × Bool)) (ib : Ibch),
        p = .PHart cpu (.pure ()) rs fn ib ∧ kInv (pinStart pcL).psPc rs) :
    ∃ (mid rest' : List Eitem) (s : PState) (n : Nat) (p' : Pexv6) (d' : Efab),
      rest = mid ++ rest' ∧ cycRun G i em own base (pinStart pcL) mid s ∧
      preach own (pinStart pcL) s n ∧ walkBd p0 (dv 0) em (base ++ mid) s.psPc p' d' ∧
      cycStop G i p0 (dv 0) em own (base ++ mid) s rest' :=
  cycRunOfHartConf G i row p0 dv em pcL w own hcf hm hw hft
    (fun s n l hs hp hne => cySailOfWalk pcL w own s n l hm hw hs hp hne (hR1 s n l hs hp hne)
      (hEx s n l hs hp hne))
    hfetch hdata hexc base rest hes hstart

end PinCycRun
end Weak
