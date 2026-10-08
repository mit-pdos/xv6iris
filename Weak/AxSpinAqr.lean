/-
Weak: **ROW SHAPE of xv6's REAL `acquire`** (pure), step-3 plan [ID-1]: `List Ritem` pieces
composed by position, the value / RMW conditions as separate Prop conjuncts next to `RowSh` (as
in `RowHolding`).

Rocq: `iris/AxSpinAqr.v` @ xxvzwolszwmp.

## The Rocq header, in substance (as restated under Stage C)

Under O2 Stage C an instruction fetch is an ADMIN step with no row item, so acquire's row window
holds only its memory events.  Positions, `k` = acquire's first memory event:
  k+0 … k+2       `aqHead`: the spills of ra / s0 / s1 (c.sdsp at + 0x02 / + 0x04 / + 0x06);
  k+3 …           `poSh b …` (push_off, 17 / 22 items, AxSpinPO4);
  `aqKp k b` = k + 20 (+ 5 if b)   the boundary after push_off's c.ret = holding's first event;
  `RowHolding (aqKp k b) row hb …` (AxSpinHd8, 1 / 12 items);
  `aqKh k b hb` = aqKp + 1 | aqKp + 12 (hb)   the boundary after holding's c.ret;
  it_j := aqKh + j, j = 0 … n  (n FAILED iterations, then the claim): the amoswap's RMW item
                  (`.IRmw true false plk 4`) — c.mv, sext.w and c.bnez have no memory event;
  `aqKm` := aqKh + (n + 1)  `aqTail`: mycpu's window at aqKm (spills aqKm / +1, reloads +2 / +3),
                  the `lk->cpu` store (c.sd a0,16(s1)) at aqKm + 4, the three reloads at
                  aqKm + 5 / 6 / 7; the row continues past aqKm + 7 (the boundary after the
                  c.ret at aqKm + 8).
  The claim RMW is at `aqKA := aqKh + n`.
The panic arm of `if(holding(lk))` and the loop's exit are decided by GRAPH VALUES in the WPd
(Q20' Option V; the Rocq row decided them by pinned fetch items).  `spinVals`: the value
condition the row family imposes (iteration `j`'s read bytes fail the branch test iff `j < n`).

Kernel words: this file states no instruction word.  The offsets above were cross-checked against
`Xv6/KernelImage.lean` (acquire = 0x80000c58: c.sdsp at 0x80000c5a/5c/5e, jal push_off
0x80000c64, jal holding 0x80000c6a, amoswap 0x80000c74, jal mycpu 0x80000c7c, c.sd a0,16(s1)
0x80000c80).  NOTE: the 4-byte `jal holding` at acquire + 0x12 = 0x80000c6a is 2 mod 4 (the other
4-byte words + 0x0c / + 0x1c / + 0x24 are 4-aligned) — `AxSpinAq.acquireText`'s conjunct
`textAt4S … (pac 0x12) Wa12` demands `is_aligned_vaddr pc 4`, so it is unsatisfiable in this tree
(as `AxSpinE8f.mycpuTextFalse`; open Q22).  Not used here.

## Deviations from Rocq

1. O2 STAGE C / Q20' (provisional Option V; protocol "Cross-file facts", AxSpinPOr / PO4 / Hd8
   entries): every Rocq `RF` / `RP` item is DELETED, and so are the fetch parameters.
   * `aq_head pra ps0 ps1` (10 items) ↦ `aqHead pra ps0 ps1` (3: the spills; Rocq 2/4/6).
   * `aq_tail p24 pmra pms0 p28 pcl pra ps0 ps1 pret nret` (30) ↦ `aqTail pmra pms0 pcl pra ps0
     ps1` (8): `mycSh pmra pms0` at 0..3 (Rocq `myc_sh … p28 2` at 1..19), the `lk->cpu` store at
     4 (Rocq 20), reloads at 5/6/7 (Rocq 22/24/26); no return fetch.  `aqTailLen` is 8 (Rocq 30).
   * `spin_it u row p1a plk` (`RP p1a 2; RF 4; RMW; RF 2; RF 2`) ↦ `spinIt u row plk` = the RMW
     item alone (`rmwAt row u plk`); `Row_spin`/`spin_vals` stride 1 (Rocq 5): iteration `j` at
     `u + j` (Rocq `u + 5 j`, RMW at `u + 5 j + 2`); `p1a` dropped.
   * `aq_kp k b` (Rocq `k + 74 (+24)`, push_off's pinned return fetch) ↦ `k + 20 (+5)` (push_off's
     continuation boundary, `tk + 9` of `wpdPushOff` at `k + 3`); `aq_kh` (Rocq `kp + 2 + 5|43`,
     holding's pinned return fetch) ↦ `aqKp + 1|12` (holding's continuation boundary, AxSpinHd8);
     `aq_km` (Rocq `kh + 2 + 5 (n+1)`) ↦ `aqKh + (n + 1)`; `aq_kA` (Rocq `kh + 4 + 5 n`) ↦
     `aqKh + n`.
   * `Row_acquire`: the conjuncts `RowSh (aq_kp+1) row [RF 4]` (jal holding) and
     `RowSh (aq_kh+1) row [RF 2]` (c.bnez a0) are DROPPED; push_off's window is `poSh b pra' …`
     at `k + 3` (Rocq `po_sh b … p10 2` at `k + 10`), holding's `RowHolding` without
     `hretm p16 2`; the fetch parameters `q14 q2c q30 q18 q1c hretm p10 p16 p1a p24 p28 pret
     nret` are DROPPED.  NEW conjunct `aqKm k b hb n + 8 < row.length` (the boundary after the
     c.ret needs a next row item — Rocq's last item `RP pret nret`; as `RowHolding`'s length
     conjuncts and `wpdPushOff`'s `tk + 9 < row.length`).
   * `aq_kp_pos` is stated over Lean's push_off length: `k + 3 + (17 + (if b then 5 else 0)) =
     aqKp k b` (push_off's window ends where its continuation boundary is; Rocq: the window's
     last item, the return fetch, is at `aq_kp`).
   * `Row_spin_S`: `Row_spin (u + 1) n` (Rocq `u + 5`).
2. SPELLING: `l !! j` ↦ `l[j]?`; `bool_decide` ↦ `decide`; `lbl_value` ↦ `lblValue`; `aq_fail` ↦
   `aqFail` (AxSpinAq); `myc_sh`/`po_sh`/`Row_holding` ↦ `mycSh`/`poSh`/`RowHolding`.

**Rocq → Lean name map.**  `aq_head` `aqHead`, `aq_tail` `aqTail`, `aq_tail_len` `aqTailLen`,
`rmw_at` `rmwAt`, `spin_it` `spinIt`, `Row_spin` `RowSpin`, `spin_vals` `spinVals`, `aq_kp`
`aqKp`, `aq_kh` `aqKh`, `aq_km` `aqKm`, `aq_kA` `aqKA`, `Row_acquire` `RowAcquire`, `aq_kp_pos`
`aqKpPos`, `Row_spin_S` `rowSpinS`, `Row_spin_0` `rowSpin0`.  (No name is in the duplicated-name
table; all short names grepped absent from the tip.)  No Lean-only declarations.

**Dropped:** `spin_pin` (deviation 1: it extracted iteration `j`'s PINNED FETCH item `RP p1a 2`,
which Stage C deletes; no Rocq file imports AxSpinAqr).  Rocq 16 definitions/lemmas; Lean 15.
-/
import Weak.AxSpinPO4
import Weak.AxSpinHd8
import Weak.AxSpinAq

namespace Weak

/-- Rocq `aq_head`: acquire + 0x00 … + 0x0c (deviation 1: the three spills). -/
def aqHead (pra ps0 ps1 : Int) : List Ritem :=
  [.RS pra 8, .RS ps0 8, .RS ps1 8]

/-- Rocq `aq_tail`: acquire + 0x24 … + 0x32 (deviation 1: mycpu's window, the `lk->cpu` store,
the three reloads; no return fetch). -/
def aqTail (pmra pms0 pcl pra ps0 ps1 : Int) : List Ritem :=
  mycSh pmra pms0 ++ [.RS pcl 8, .RL pra 8, .RL ps0 8, .RL ps1 8]

/-- Rocq `aq_tail_len` (deviation 1: 8 items). -/
theorem aqTailLen (pmra pms0 pcl pra ps0 ps1 : Int) :
    (aqTail pmra pms0 pcl pra ps0 ps1).length = 8 := rfl

/-- Rocq `rmw_at`: the amoswap's RMW item. -/
def rmwAt (row : List Lbl) (j : Nat) (plk : Int) : Prop :=
  ∃ lb, row[j]? = some lb ∧ aident lb = .IRmw true false plk 4

/-- Rocq `spin_it`: one spin iteration at `u` (deviation 1: the RMW item alone). -/
def spinIt (u : Nat) (row : List Lbl) (plk : Int) : Prop :=
  rmwAt row u plk

/-- Rocq `Row_spin` (deviation 1: stride 1). -/
def RowSpin (u n : Nat) (row : List Lbl) (plk : Int) : Prop :=
  ∀ j, j ≤ n → spinIt (u + j) row plk

/-- Rocq `spin_vals`: the row family's value condition — iteration `j` fails iff `j < n`
(deviation 1: the RMW of iteration `j` at `u + j`). -/
def spinVals (row : List Lbl) (u n : Nat) : Prop :=
  ∀ j, j ≤ n → ∃ lb vs, row[u + j]? = some lb ∧ lblValue lb = some vs ∧
    aqFail vs = decide (j < n)

/-- Rocq `aq_kp` (deviation 1: push_off's continuation boundary). -/
def aqKp (k : Nat) (b : Bool) : Nat := k + 20 + (if b then 5 else 0)
/-- Rocq `aq_kh` (deviation 1: holding's continuation boundary). -/
def aqKh (k : Nat) (b hb : Bool) : Nat := aqKp k b + (if hb then 12 else 1)
/-- Rocq `aq_km` (deviation 1). -/
def aqKm (k : Nat) (b hb : Bool) (n : Nat) : Nat := aqKh k b hb + (n + 1)
/-- Rocq `aq_kA` (deviation 1): the claim RMW. -/
def aqKA (k : Nat) (b hb : Bool) (n : Nat) : Nat := aqKh k b hb + n

/-- Rocq `Row_acquire`: THE ROW OF acquire at `k` — push_off's arm `b`, holding's lock bit `hb`,
`n` failed spins (deviation 1: no fetch items / parameters; the length conjunct).  PAs:
acquire's slots `pra ps0 ps1`; push_off's (`qra qs0 qs1`, mycpu's inside it `qmra qms0`, fields
`pn pint`); holding's (`hra hs0 hs1 hram hs0m`); the lock word `plk` and `lk->cpu` `pcl`;
mycpu's slots from acquire `mra ms0`. -/
def RowAcquire (k : Nat) (b hb : Bool) (n : Nat) (row : List Lbl)
    (pra ps0 ps1 qra qs0 qs1 qmra qms0 pn pint hra hs0 hs1 hram hs0m plk pcl mra ms0 : Int) :
    Prop :=
  RowSh k row (aqHead pra ps0 ps1) ∧
  RowSh (k + 3) row (poSh b qra qs0 qs1 qmra qms0 pn pint) ∧
  RowHolding (aqKp k b) row hb plk pcl hra hs0 hs1 hram hs0m ∧
  RowSpin (aqKh k b hb) n row plk ∧
  RowSh (aqKm k b hb n) row (aqTail mra ms0 pcl pra ps0 ps1) ∧
  aqKm k b hb n + 8 < row.length

/-- Rocq `aq_kp_pos` (deviation 1): push_off's window, started at `k + 3`, ends at `aqKp`. -/
theorem aqKpPos (k : Nat) (b : Bool) : k + 3 + (17 + (if b then 5 else 0)) = aqKp k b := by
  unfold aqKp
  cases b <;> simp <;> omega

/-- Rocq `Row_spin_S` (deviation 1: `u + 1`). -/
theorem rowSpinS (u n : Nat) (row : List Lbl) (plk : Int) :
    RowSpin u (n + 1) row plk → RowSpin (u + 1) n row plk := by
  intro H j Hj
  rw [show u + 1 + j = u + (j + 1) by omega]
  exact H (j + 1) (by omega)

/-- Rocq `Row_spin_0`. -/
theorem rowSpin0 (u n : Nat) (row : List Lbl) (plk : Int) :
    RowSpin u n row plk → spinIt u row plk := by
  intro H
  have h := H 0 (Nat.zero_le _)
  rw [Nat.add_zero] at h
  exact h

end Weak
