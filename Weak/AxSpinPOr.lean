/-
Weak: **ROW SHAPES for `push_off` / `pop_off`** (pure).

Rocq: `iris/AxSpinPOr.v` @ xxvzwolszwmp.

## The Rocq header, in substance (as restated under Stage C)

A row window is described by a list of items `Ritem`, one per row position (the shape a function
occupies in hart `i`'s row from a position `k`):
  `RF n`     (Rocq: an instruction FETCH of `n` bytes) — any `n`-byte read;
  `RP pa n`  (Rocq: a PINNED fetch) — an `n`-byte read of `pa`;
  `RS pa n`  a plain `n`-byte store at `pa` (data existential);
  `RL pa n`  an `n`-byte read of `pa` (value existential).
`RowSh k row sh`: every item of `sh` is matched by the row at `k + j`.

§1 the shape language and its generic facts (read items are not writes; NO-WRITE-BETWEEN for a
   reload from the stores of the window).
§2 `mycSh`: mycpu's window, and `rowMycpuOf` — a matched `mycSh` is `RowMycpu` (so `wpdMycpu`
   composes at any inner position).
§3 the windows of push_off (`poHead` / `poInt` / `poTail`) and pop_off (`ppHead` / `ppMid` /
   `ppTail`), and the pinned-fetch predicate `fpin`.

## Deviations from Rocq

1. O2 STAGE C (protocol "Cross-file facts": fetches are NOT graph events) / Q20' (provisional
   Option V, `notes/weak-port-q20-offrow.md` §C.2 item 4): an instruction fetch consumes NO row
   item, so the WINDOWS hold only the memory events — every Rocq `RF` item and every Rocq `RP`
   item (the pinned fetches: return fetches and the branch arms' next fetches) is DELETED from
   `mycSh`/`poHead`/`poInt`/`poTail`/`ppHead`/`ppMid`/`ppTail`, and so are their address / width
   parameters (control flow is pinned by GRAPH VALUES in the PO capstones, as `AxSpinE8.wpdMycpu`'s
   `Hval`):
   * `myc_sh pra ps0 pret nret` (19 items) ↦ `mycSh pra ps0` = spills at 0/1, reloads at 2/3
     (Rocq 2/4, 13/15; return fetch 18);
   * `po_head pra ps0 ps1 pmra pms0 p14 pn` (32) ↦ `poHead pra ps0 ps1 pmra pms0 pn` (8): the
     three spills at 0..2, mycpu at 3 (Rocq 11), the `noff` load at 7 (Rocq 30);
   * `po_int pmra pms0 p2c p30 pint` (24) ↦ `poInt pmra pms0 pint` (5): mycpu at 0 (Rocq 1),
     the intena store at 4 (Rocq 22);
   * `po_tail pra ps0 ps1 pmra pms0 p18 p1c pn pret nret` (33) ↦ `poTail pra ps0 ps1 pmra pms0
     pn` (9): mycpu at 0 (Rocq 1), noff load/store at 4/5 (Rocq 20/23), the reloads at 6..8
     (Rocq 25/27/29);
   * `pp_head pra ps0 pmra pms0 p0c pn p1a` (35) ↦ `ppHead pra ps0 pmra pms0 pn` (8): spills at
     0/1 (Rocq 2/4), mycpu at 2 (Rocq 7), noff load at 6 (Rocq 29), noff store at 7 (Rocq 33);
   * `pp_mid p20 pint` (3) ↦ `ppMid pint` (1): the intena load at 0 (Rocq 1);
   * `pp_tail pra ps0 p28 pret nret` (7) ↦ `ppTail pra ps0` (2): the reloads at 0/1 (Rocq 1/3).
   The shape LANGUAGE (`Ritem` with all four constructors, `ishape`, `RowSh`) and every generic
   lemma (incl. the fetch-item lemmas `ishFetchNw`, `ishRdWidth`, `shFetchNw`, `shFetchNe`,
   `shPin`) are kept faithfully: they are true of `RF`/`RP` items read as plain reads, but no
   Stage C window uses `RF`/`RP` (consumer-less, like `AxSpinE3.FirstRd`).
2. `rowMycpuOf` (Rocq `Row_mycpu_of`): Rocq's length conjunct came from the return-fetch item at
   18; Lean's `RowMycpu` needs `k + 4 < row.length` (the c.ret's continuation boundary), which
   the 4-item window does not give — NEW premise `k + 4 < row.length` (every PO window has an
   item after mycpu's, so callers get it from `rowShLen` of the enclosing window).  Rocq's
   `nret = 2 ∨ nret = 4` premise is gone with `nret`.  `myc_len` is 4 (Rocq 19); `myc_item`
   ranges over `j < 4` (Rocq 18).
3. `fpin` is ported faithfully (`uint (fetch_pa pte v)` ↦ `paZ (AxSpinE6.fetchPa pte v)`,
   `svpn_of` ↦ `WeakKpt.svpnOf`, `ptree_maps` ↦ `AxPtProt.ptreeMaps`, `va_canon` ↦ `vaCanon`)
   but has no Stage C consumer: under Option V the PO capstones take value pins instead (Q20
   note §C.2 item 4).
4. SPELLING: `Forall P l` ↦ `∀ it ∈ l, P it` (in `rowShNowr`); `l !! j` ↦ `l[j]?`;
   `(kw < k' < kr)` ↦ `kw < k' ∧ k' < kr`; `Z.of_nat n` ↦ `(n : Int)`; `ritem` ↦ `Ritem`;
   `WeakAxiomatic.LStore` ↦ `Lbl.LStore`; `aident_wr`/`aident_rd` ↦ `aidentWr`/`aidentRd`;
   `mword_of_int 9 : mword 5` ↦ `9#5`.
5. TACTICS: Rocq `dj_close` / `nowr_tac` ↦ the macros `ax_spin_por_dj_close` /
   `ax_spin_por_nowr` (unique names; `nowr_tac` closes the `∀ it ∈ drop (jw+1) (take jr sh),
   itDisj pa w it` side goal of `rowShNowr` for the concrete windows, discharging each `dj` from
   a hypothesis or its `djSym`).

**Rocq → Lean name map.**  `ritem` `Ritem` (`RF`/`RP`/`RS`/`RL`), `ishape` `ishape`, `RowSh`
`RowSh`, `RowSh_app_l` `rowShAppL`, `RowSh_app_r` `rowShAppR`, `RowSh_at` `rowShAt`, `RowSh_len`
`rowShLen`, `ish_fetch_nw` `ishFetchNw`, `ish_rd_width` `ishRdWidth`, `ish_store` `ishStore`,
`dj` `dj`, `nowr` `nowr`, `nowr_join` `nowrJoin`, `it_disj` `itDisj`, `RowSh_nowr` `rowShNowr`,
`dj_sym` `djSym`, `alldj` `alldj`, `sh_fetch_nw` `shFetchNw`, `sh_fetch_ne` `shFetchNe`, `sh_pin`
`shPin`, `sh_store` `shStore`, `r9` `AxSpinPOr.r9` (duplicated-name table), `myc_sh` `mycSh`,
`myc_len` `mycLen`, `myc_item` `mycItem`, `Row_mycpu_of` `rowMycpuOf`, `fpin` `fpin`, `po_head`
`poHead`, `po_int` `poInt`, `po_tail` `poTail`, `pp_head` `ppHead`, `pp_mid` `ppMid`, `pp_tail`
`ppTail`; Ltac `dj_close` `ax_spin_por_dj_close`, `nowr_tac` `ax_spin_por_nowr`.  No Lean-only
declarations.

**Dropped:** nothing (Rocq 33 definitions/lemmas + 2 Ltac; Lean 33 + 2 macros).
-/
import Weak.AxSpinE8

namespace Weak

open MachCSL MachCSL.Stdpp

/-! # 1. Shapes -/

/-- Rocq `ritem`. -/
inductive Ritem where
  | RF (n : Nat)
  | RP (pa : Int) (n : Nat)
  | RS (pa : Int) (n : Nat)
  | RL (pa : Int) (n : Nat)

/-- Rocq `ishape`. -/
def ishape (it : Ritem) (lb : Lbl) : Prop :=
  match it with
  | .RF n => ∃ aq b, aident lb = .IRead aq b n
  | .RP pa n => ∃ aq, aident lb = .IRead aq pa n
  | .RS pa n => ∃ vw cls, lb = .LStore false pa vw cls ∧ vw.length = n
  | .RL pa n => ∃ aq, aident lb = .IRead aq pa n

/-- Rocq `RowSh`. -/
def RowSh (k : Nat) (row : List Lbl) (sh : List Ritem) : Prop :=
  ∀ j it, sh[j]? = some it → ∃ lb, row[k + j]? = some lb ∧ ishape it lb

theorem rowShAppL (k : Nat) (row : List Lbl) (s1 s2 : List Ritem) :
    RowSh k row (s1 ++ s2) → RowSh k row s1 := by
  intro H j it Hj
  exact H j it (lookup_app_l_Some Hj)

theorem rowShAppR (k : Nat) (row : List Lbl) (s1 s2 : List Ritem) :
    RowSh k row (s1 ++ s2) → RowSh (k + s1.length) row s2 := by
  intro H j it Hj
  obtain ⟨lb, Hlb, Hs⟩ := H (s1.length + j) it (by
    rw [List.getElem?_append_right (by omega)]
    rw [show s1.length + j - s1.length = j by omega]
    exact Hj)
  exact ⟨lb, by rw [show k + s1.length + j = k + (s1.length + j) by omega]; exact Hlb, Hs⟩

theorem rowShAt (k : Nat) (row : List Lbl) (sh : List Ritem) (j : Nat) (it : Ritem) :
    RowSh k row sh → sh[j]? = some it → ∃ lb, row[k + j]? = some lb ∧ ishape it lb :=
  fun H Hj => H j it Hj

theorem rowShLen (k : Nat) (row : List Lbl) (sh : List Ritem) :
    RowSh k row sh → sh ≠ [] → k + sh.length ≤ row.length := by
  intro H Hne
  have Hl : 0 < sh.length := by
    cases sh with
    | nil => exact absurd rfl Hne
    | cons _ _ => simp
  obtain ⟨it, Hit⟩ : ∃ it, sh[sh.length - 1]? = some it :=
    ⟨_, List.getElem?_eq_getElem (by omega)⟩
  obtain ⟨lb, Hlb, _⟩ := H _ _ Hit
  have := (List.getElem?_eq_some_iff.1 Hlb).1
  omega

/-- Rocq `ish_fetch_nw`: fetch / read items are not writes. -/
theorem ishFetchNw (it : Ritem) (lb : Lbl) :
    ((∃ n, it = .RF n) ∨ (∃ pa n, it = .RP pa n) ∨ (∃ pa n, it = .RL pa n)) →
    ishape it lb → aidentWr (aident lb) = none := by
  rintro (⟨n, rfl⟩ | ⟨pa, n, rfl⟩ | ⟨pa, n, rfl⟩)
  · rintro ⟨aq, b, E⟩; rw [E]; rfl
  · rintro ⟨aq, E⟩; rw [E]; rfl
  · rintro ⟨aq, E⟩; rw [E]; rfl

/-- Rocq `ish_rd_width`. -/
theorem ishRdWidth (it : Ritem) (lb : Lbl) (n : Nat) (aq : Bool) (b : Int) (m : Nat) :
    (it = .RF n ∨ ∃ pa, it = .RP pa n) → ishape it lb →
    aidentRd (aident lb) = some (aq, b, m) → m = n := by
  rintro (rfl | ⟨pa, rfl⟩)
  · rintro ⟨aq', b', E⟩ H; rw [E] at H; simp only [aidentRd, Option.some.injEq,
      Prod.mk.injEq] at H; exact H.2.2.symm
  · rintro ⟨aq', E⟩ H; rw [E] at H; simp only [aidentRd, Option.some.injEq,
      Prod.mk.injEq] at H; exact H.2.2.symm

/-- Rocq `ish_store`: the store item, its data. -/
theorem ishStore (pa : Int) (n : Nat) (lb : Lbl) :
    ishape (.RS pa n) lb → ∃ vw cls, lb = .LStore false pa vw cls ∧ vw.length = n :=
  id

/-- Rocq `dj`: the byte ranges `[a, a+n)` and `[b, b+m)` are disjoint. -/
def dj (a : Int) (n : Nat) (b : Int) (m : Nat) : Prop :=
  a + (n : Int) ≤ b ∨ b + (m : Int) ≤ a

/-- Rocq `nowr`: NO WRITE BETWEEN — the writes strictly between two positions miss a range. -/
def nowr (row : List Lbl) (kw kr : Nat) (pa : Int) (w : Nat) : Prop :=
  ∀ (k' : Nat) (lb : Lbl) (rl : Bool) (b : Int) (m : Nat), kw < k' ∧ k' < kr →
    row[k']? = some lb → aidentWr (aident lb) = some (rl, b, m) → dj b m pa w

theorem nowrJoin (row : List Lbl) (kw t kr : Nat) (pa : Int) (w : Nat) :
    kw < t + 1 → nowr row kw (t + 1) pa w → nowr row t kr pa w → nowr row kw kr pa w := by
  intro _ H1 H2 k' lb rl b m Hk
  by_cases h : k' ≤ t
  · exact H1 k' lb rl b m ⟨Hk.1, by omega⟩
  · exact H2 k' lb rl b m ⟨by omega, Hk.2⟩

/-- Rocq `it_disj`. -/
def itDisj (pa : Int) (w : Nat) (it : Ritem) : Prop :=
  match it with
  | .RS pb m => dj pb m pa w
  | _ => True

theorem rowShNowr (k : Nat) (row : List Lbl) (sh : List Ritem) (jw jr : Nat) (pa : Int)
    (w : Nat) :
    RowSh k row sh → jr ≤ sh.length →
    (∀ it ∈ (sh.take jr).drop (jw + 1), itDisj pa w it) →
    nowr row (k + jw) (k + jr) pa w := by
  intro H Hle HF k' lb rl b m Hk Hlb Hid
  obtain ⟨it, Hit⟩ : ∃ it, sh[k' - k]? = some it :=
    ⟨_, List.getElem?_eq_getElem (by omega)⟩
  obtain ⟨lb', Hlb', Hs⟩ := H (k' - k) it Hit
  rw [show k + (k' - k) = k' by omega, Hlb] at Hlb'
  cases Hlb'
  have Hj : ((sh.take jr).drop (jw + 1))[k' - k - (jw + 1)]? = some it := by
    rw [List.getElem?_drop, List.getElem?_take]
    rw [if_pos (by omega), show jw + 1 + (k' - k - (jw + 1)) = k' - k by omega]
    exact Hit
  have Hd : itDisj pa w it := HF it (List.mem_of_getElem? Hj)
  cases it with
  | RF n => obtain ⟨aq, b', E⟩ := Hs; rw [E] at Hid; cases Hid
  | RP pb n => obtain ⟨aq, E⟩ := Hs; rw [E] at Hid; cases Hid
  | RS pb n =>
    obtain ⟨vw, cls, rfl, Hl⟩ := Hs
    simp only [aident, aidentWr, Option.some.injEq, Prod.mk.injEq] at Hid
    obtain ⟨_, rfl, rfl⟩ := Hid
    rw [Hl]
    exact Hd
  | RL pb n => obtain ⟨aq, E⟩ := Hs; rw [E] at Hid; cases Hid

theorem djSym (a : Int) (n : Nat) (b : Int) (m : Nat) : dj a n b m → dj b m a n := by
  unfold dj
  omega

/-- Rocq `alldj`: all pairwise disjoint. -/
def alldj (l : List (Int × Nat)) : Prop :=
  ∀ (j1 j2 : Nat) (x y : Int × Nat), l[j1]? = some x → l[j2]? = some y → j1 ≠ j2 →
    dj x.1 x.2 y.1 y.2

/-- Rocq `sh_fetch_nw`: fetch items at a known position. -/
theorem shFetchNw (k : Nat) (row : List Lbl) (sh : List Ritem) (j n : Nat) :
    RowSh k row sh → (sh[j]? = some (.RF n) ∨ ∃ pa, sh[j]? = some (.RP pa n)) →
    ∀ lb, row[k + j]? = some lb → aidentWr (aident lb) = none := by
  intro H Hj lb Hlb
  rcases Hj with Hj | ⟨pa, Hj⟩
  · obtain ⟨lb', Hlb', aq, b, E⟩ := H _ _ Hj
    rw [Hlb] at Hlb'; cases Hlb'; rw [E]; rfl
  · obtain ⟨lb', Hlb', aq, E⟩ := H _ _ Hj
    rw [Hlb] at Hlb'; cases Hlb'; rw [E]; rfl

theorem shFetchNe (k : Nat) (row : List Lbl) (sh : List Ritem) (j n n' : Nat) :
    RowSh k row sh → (sh[j]? = some (.RF n) ∨ ∃ pa, sh[j]? = some (.RP pa n)) → n ≠ n' →
    ∀ (lb : Lbl) (aq : Bool) (b : Int) (m : Nat), row[k + j]? = some lb →
      aidentRd (aident lb) = some (aq, b, m) → m ≠ n' := by
  intro H Hj Hne lb aq b m Hlb Hrd
  rcases Hj with Hj | ⟨pa, Hj⟩
  · obtain ⟨lb', Hlb', aq', b', E⟩ := H _ _ Hj
    rw [Hlb] at Hlb'; cases Hlb'; rw [E] at Hrd
    simp only [aidentRd, Option.some.injEq, Prod.mk.injEq] at Hrd
    rw [← Hrd.2.2]; exact Hne
  · obtain ⟨lb', Hlb', aq', E⟩ := H _ _ Hj
    rw [Hlb] at Hlb'; cases Hlb'; rw [E] at Hrd
    simp only [aidentRd, Option.some.injEq, Prod.mk.injEq] at Hrd
    rw [← Hrd.2.2]; exact Hne

/-- Rocq `sh_pin`: a pinned item, the read identity at that position. -/
theorem shPin (k : Nat) (row : List Lbl) (sh : List Ritem) (j : Nat) (pa : Int) (n : Nat) :
    RowSh k row sh → sh[j]? = some (.RP pa n) →
    ∃ lb aq, row[k + j]? = some lb ∧ aidentRd (aident lb) = some (aq, pa, n) := by
  intro H Hj
  obtain ⟨lb, Hlb, aq, E⟩ := H _ _ Hj
  exact ⟨lb, aq, Hlb, by rw [E]; rfl⟩

/-- Rocq `sh_store`: a store item, the row label. -/
theorem shStore (k : Nat) (row : List Lbl) (sh : List Ritem) (j : Nat) (pa : Int) (n : Nat) :
    RowSh k row sh → sh[j]? = some (.RS pa n) →
    ∃ vw cls, row[k + j]? = some (.LStore false pa vw cls) ∧ vw.length = n := by
  intro H Hj
  obtain ⟨lb, Hlb, vw, cls, rfl, Hl⟩ := H _ _ Hj
  exact ⟨vw, cls, Hlb, Hl⟩

/-- Rocq `r9`. -/
abbrev AxSpinPOr.r9 : BitVec 5 := 9#5

/-! # 2. mycpu's window -/

/-- Rocq `myc_sh` (deviation 1: the four memory events; no fetch items, no `pret`/`nret`). -/
def mycSh (pra ps0 : Int) : List Ritem :=
  [.RS pra 8, .RS ps0 8, .RL pra 8, .RL ps0 8]

theorem mycLen (pra ps0 : Int) : (mycSh pra ps0).length = 4 := rfl

theorem mycItem (pra ps0 : Int) (j : Nat) : j < 4 →
    ∃ it, (mycSh pra ps0)[j]? = some it ∧ ∀ lb, ishape it lb → mshape pra ps0 j lb := by
  intro Hj
  match j, Hj with
  | 0, _ => exact ⟨_, rfl, fun _ h => h⟩
  | 1, _ => exact ⟨_, rfl, fun _ h => h⟩
  | 2, _ => exact ⟨_, rfl, fun _ h => h⟩
  | 3, _ => exact ⟨_, rfl, fun _ h => h⟩

/-- Rocq `Row_mycpu_of` (deviation 2: the length premise `k + 4 < row.length`). -/
theorem rowMycpuOf (k : Nat) (row : List Lbl) (pra ps0 : Int) :
    RowSh k row (mycSh pra ps0) → k + 4 < row.length → RowMycpu k row pra ps0 := by
  intro H Hlen
  refine ⟨Hlen, fun j Hj => ?_⟩
  obtain ⟨it, Hit, Hm⟩ := mycItem pra ps0 j Hj
  obtain ⟨lb, Hlb, Hs⟩ := H j it Hit
  exact ⟨lb, Hlb, Hm lb Hs⟩

/-! # 3. push_off / pop_off windows, pinned fetches -/

/-- Rocq `fpin` (deviation 3: no Stage C consumer): among CANONICAL VAs only `v` fetches from
`pa`; the trap vector does not. -/
def fpin (T : PTree) (stv v : BitVec 64) (pa : Int) : Prop :=
  (∀ (v' p2 p1 pte : BitVec 64), vaCanon v' →
      AxPtProt.ptreeMaps T (WeakKpt.svpnOf v') p2 p1 pte → paZ (AxSpinE6.fetchPa pte v') = pa →
      v' = v) ∧
  (∀ (p2 p1 pte : BitVec 64), AxPtProt.ptreeMaps T (WeakKpt.svpnOf stv) p2 p1 pte →
      paZ (AxSpinE6.fetchPa pte stv) ≠ pa)

/-- Rocq `po_head`: push_off + 0x00 … 0x16 (deviation 1: 8 items; the spills at 0..2, mycpu at 3,
the `noff` load at 7). -/
def poHead (pra ps0 ps1 pmra pms0 pn : Int) : List Ritem :=
  [.RS pra 8, .RS ps0 8, .RS ps1 8] ++ mycSh pmra pms0 ++ [.RL pn 4]

/-- Rocq `po_int`: + 0x2c … 0x38, the `noff == 0` arm (deviation 1: 5 items; mycpu at 0, the
intena store at 4). -/
def poInt (pmra pms0 pint : Int) : List Ritem :=
  mycSh pmra pms0 ++ [.RS pint 4]

/-- Rocq `po_tail`: + 0x18 … 0x2a (deviation 1: 9 items; mycpu at 0, the `noff` load / store at
4 / 5, the reloads at 6..8; no return fetch). -/
def poTail (pra ps0 ps1 pmra pms0 pn : Int) : List Ritem :=
  mycSh pmra pms0 ++ [.RL pn 4, .RS pn 4, .RL pra 8, .RL ps0 8, .RL ps1 8]

/-- Rocq `pp_head`: pop_off + 0x00 … 0x1e (deviation 1: 8 items; the spills at 0/1, mycpu at 2,
the `noff` load / store at 6 / 7). -/
def ppHead (pra ps0 pmra pms0 pn : Int) : List Ritem :=
  [.RS pra 8, .RS ps0 8] ++ mycSh pmra pms0 ++ [.RL pn 4, .RS pn 4]

/-- Rocq `pp_mid`: + 0x20, 0x22, the `noff == 0` arm (deviation 1: the intena load only). -/
def ppMid (pint : Int) : List Ritem := [.RL pint 4]

/-- Rocq `pp_tail`: + 0x28 … 0x2e (deviation 1: the two reloads; no return fetch). -/
def ppTail (pra ps0 : Int) : List Ritem := [.RL pra 8, .RL ps0 8]

/-- Rocq `dj_close`. -/
macro "ax_spin_por_dj_close" : tactic =>
  `(tactic| first | assumption | (apply djSym; assumption))

/-- Rocq `nowr_tac`: the `rowShNowr` side goal for the concrete windows. -/
macro "ax_spin_por_nowr" : tactic =>
  `(tactic| (
    simp only [poHead, poInt, poTail, ppHead, ppMid, ppTail, mycSh, List.cons_append,
      List.nil_append, List.take_succ_cons, List.take_zero, List.take_nil, List.drop_succ_cons,
      List.drop_zero, List.drop_nil, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, itDisj, true_and, and_true, imp_self, implies_true,
      forall_const]
    all_goals (repeat' apply And.intro)
    all_goals (first | trivial | ax_spin_por_dj_close)))

end Weak
