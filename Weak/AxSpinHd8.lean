/-
Weak: **PHASE 5, stage 3: `RowHolding` and the EPILOGUE of xv6's REAL `holding`** as a
positional CPS WPd at the joint instance Ixv6.

Rocq: `iris/AxSpinHd8.v` @ xxvzwolszwmp.

## The Rocq header, in substance (as restated under Stage C)

§1 `RowHolding k row hb plk pcl pra ps0 ps1 pram ps0m` — the piece of hart `i`'s row that
   holding occupies from position `k`.  Under O2 Stage C an instruction fetch is an ADMIN step
   with no row item, so the window holds only holding's memory events:
   common: `k` the `c.lw` of `lk->locked` (a 4-byte read at `plk`) whose ROW VALUE `vs` fixes
   the CFG path: `hb = (ldRes false 4 vs != 0)` (c.bnez's direction — `lkBranch`).
   SHORT path (`hb = false`: locked = 0, return 0): no further memory event; the row continues
   past `k` (`k + 1 < row.length`: the boundary after the c.ret).
   LONG path (`hb = true`):
     k+1 / k+2 / k+3   the SPILLS of ra / s0 / s1: plain 8-byte stores at `pra` / `ps0` / `ps1`;
     k+4               the `c.ld` of `lk->cpu`: an 8-byte read at `pcl`;
     k+5 .. k+8        `RowMycpu (k + 5) row pram ps0m` (AxSpinE8): mycpu's four events;
     k+9 / k+10 / k+11 the RELOADS of ra / s0 / s1;
   and the row continues past `k + 11` (`k + 12 < row.length`).
§2 row facts: `holdWr` (the only writes of the long window are the five spills), shape
   inversions.
§3 `holdEpi` — holding + 0x1a … + 0x2a (sub, seqz, three reloads, c.addi16sp, c.ret) from the
   boundary at `k + 9` (after mycpu's return) to the boundary after the c.ret at the EXACT
   position `k + 12`: a0 := `hres s1 a0` (= seqz (s1 − a0)), sp restored, ra/s0/s1 = the
   RELOADED words with the three reload annotations (Phase 1c private-slot facts,
   `AxSpinE6.XxLd`); the c.ret continues at `PC = ret` (`AxSpinE6.XxRet`, Q20' Option V).

GRAPH-VALUE PINNING (Q20', provisional Option V, `notes/weak-port-q20-offrow.md`; the Rocq
"TEMPORARY ROW-PINNING ASSUMPTION" of AxSpinHdA): the return address is pinned by the ra
reload's GRAPH VALUE `Hval : graphValue (gtAdGd GT) (i, k + 9) = some (stBytes 8 ret)` (the row
cannot pin control flow under Stage C).  The theorem proves nothing about a graph whose reload
value differs.

## Stage 2 P-FORM (Lean-only; notes/weak-lb-thm2-stage2.md §B, §C row `AxSpinHd9/HdA/HdC`)

`RowHoldingP k row hb …` is `RowHolding` on a PREFIX row: the branch fact `lkBranch row k hb`
guarded by `k < row.length`, every PRESENT window item (`k + j < row.length`) shaped, mycpu's
window `RowMycpuP (k + 5)` (AxSpinE8), no length conjunct (`AxSpinHd8.rowHoldingPOfFull`:
`RowHolding → RowHoldingP`; `holdWrP` = `holdWr` on it).  `holdEpiP` is `holdEpi`'s script with
a `by_cases` on `LEN ≤ position` at `k + 9 .. k + 12`; the ends at `k + 9 .. k + 11` are the
windowed, resource-free hook (exact form shared with `AxSpinE8.wpdMycpuP`, window `[k+9, k+11]`)
  `HΨend : ∀ k', klo ≤ k' → k' ≤ khi → (grow (gtAdGd GT) i).length ≤ k' → ∀ pr : Pexv6,
     ⊢ wpdM … .MaybeStuck i ⟨pr, k'⟩ Ψ`
and the end at `k + 12` (all reloads done, before c.addi16sp) is NOT the hook: it is the second
conjunct (iProp `∧`, same resources) of the continuation, which RECEIVES the three reloads'
graph values and annotations — `k + 12` is where the CALLER's (acquire's / release's) panic
branch is decided (designated cuts `aq` / `rlL`; their arms are proved in `AxSpinT2h`).  The
`Hval` pin is guarded (`k + 9 < LEN →`).  `holdEpi` keeps its exact statement as the corollary.

## P1 GATE FORM (Lean-only; notes/weak-lb-thm2-pins.md §P1, as AxSpinE8's "P1 GATE FORM")

`AxSpinHd8.holdEpiGr` is the shared gated core: `holdEpiP`'s premises with the ra pin replaced by
`AxSpinT2i.Gate GT i (k + 9) (stBytes 8 ret)` (same slot), and the main continuation prefixed by
`⌜k + 12 < LEN⌝ -∗`.  At the boundary `k + 10` a `by_cases` on the reloaded value: equal ⇒ the
old script; else `AxSpinT2i.cutReloadG` with the reload's `RLfact` (when `ret`'s bytes are the
spill `ra0`'s; the G call sites take `ret := ra0`), otherwise the hook.  `holdEpiP` = core ∘
`AxSpinT2i.gateOfPinG` (statement unchanged).  HONESTY: no return-address pin left in the core.

## Deviations from Rocq

1. O2 STAGE C / Q20' (provisional Option V; protocol "Cross-file facts" Q20' and AxSpinE8
   entries):
   * `Row_holding k row hb plk pcl pra ps0 ps1 pram ps0m pretm pret nret` ↦
     `RowHolding k row hb plk pcl pra ps0 ps1 pram ps0m`: no fetch items.  Positions: lw `k`
     (Rocq `k+1`), spills `k+1/2/3` (Rocq `k+5/7/9`), `lk->cpu` read `k+4` (Rocq `k+12`), mycpu
     window `RowMycpu (k + 5)` (Rocq `Row_mycpu (k+15) … pretm 4`), reloads `k+9/10/11` (Rocq
     `k+36/38/40`), boundary after the c.ret `k+12` (Rocq return fetch `k+43`).  Length
     conjuncts `k + 12 < row.length` (Rocq `k + 43 < length row`) and, short path,
     `k + 1 < row.length` (Rocq `k + 5`).  The return-fetch conjunct (`ret_pin`), `pretm`,
     `pret`, `nret` and the `nret ∈ {2,4}` conjunct are gone; the shapes' fetch arms
     (`fe 2`/`fe 4`) are `False` and the ranges are `j < 12` (long, outside mycpu's
     `5 ≤ j ≤ 8`) / `j < 1` (short).  Rocq's `if hb then … else …` is a `match hb`.
   * `lkBranch` reads the row item at `k` (Rocq `k + 1`).
   * `holdWr`: `j < 12` (Rocq `j ≤ 43`; Rocq's `j = 43` was the return-fetch read); the spill
     positions are `1/2/3/5/6` (Rocq `5/7/9/17/19`).  `mshapeInv` is stated over AxSpinE8's
     Lean `mshape` (positions `0/1`, Rocq `2/4`).
   * `holdEpi`: boundary `k + 9` (Rocq `k+33`), continuation `k + 12` (Rocq `k+43`); spill data
     premises at `(i, k+1/2/3)`; reload graph values and annotations at `(i, k+9/10/11)`.
     Rocq's return-page premises `Hinj`/`Hstv`, the section context `stv` and the Sail premise
     `va_first_read` are DROPPED (as `AxSpinE8.wpdMycpu`); NEW premises
     `Hval : graphValue (gtAdGd GT) (i, k + 9) = some (stBytes 8 ret)` and
     `Hret : jalrTgt 0#12 ret = ret` (as AxSpinE8).  Rocq's fetch-width uses of `fe2_facts`
     (the reloads' `Hn` premises) are gone with `AxSpinE6.XxLd`'s dropped fetch premise.
2. TYPES / SPELLING (as AxSpinE8 deviation 3): `uint P` ↦ `paZ P`; `gpr_val` ↦ `gprVal`;
   `register_lookup PC rs` ↦ `rs .PC`; `uint r ≠ n` ↦ `r.toNat ≠ n`; `l !! k` ↦ `l[k]?`;
   `neq_vec x zero_reg` ↦ `x != 0#64`; `lbl_value` ↦ `lblValue`; `sub_vec` ↦ `-`;
   `(i,k) ↦ₐ P` ↦ `AxAnnot.annotOwn (i, k) P`; the `let`s `va_ra`/`va_s0`/`va_s1` are inlined;
   `slots_disj`'s list is a Lean list literal; `rsp` (`zero_extend' 5 'b"10"`) is `2#5`.
3. INSTANCES / SECTION (as AxSpinE8 deviation 4): `[InvGS_gen hlc GF]` (any `hlc`); the local
   instances `h8_pol`/`h8_G` are inlined as `xv6Pol GT` / `AxSpinX2.xG L GT nm`; section
   variables are explicit arguments in AxSpinE6's order (+ `Htxh`).
4. TACTICS: `pcs`/`nz` ↦ `decide`; `zsimp` ↦ the file-local macro `ax_spin_hd8_zsimp`
   (= AxSpinE8's); `lia` ↦ `omega`; `zq` subsumed.  `Print Assumptions` is not ported.

**Rocq → Lean name map.**  `fe` `AxSpinHd8.fe`, `st8` `AxSpinHd8.st8`, `rd8` `AxSpinHd8.rd8`,
`lshape` `AxSpinHd8.lshape`, `sshape` `AxSpinHd8.sshape` (short generic names qualified; `lshape`
also exists in Xv6/PipesDisc), `lk_branch` `lkBranch`, `Row_holding` `RowHolding`, `disj8`
`disj8`, `slots_disj` `slotsDisj`, `slots_disj_at` `slotsDisjAt`, `hres` `hres`, `lshape_inv`
`lshapeInv`, `mshape_inv` `mshapeInv`, `st8_wr` `st8Wr`, `rd_nowr` `rdNowr`, `hold_wr`
`holdWr`, `fe2_facts` `fe2Facts`, `hold_epi` `holdEpi`; duplicated names (file-qualified)
`r9` `AxSpinHd8.r9`, `imm24` `AxSpinHd8.imm24`, `imm16` `AxSpinHd8.imm16`, `imm8`
`AxSpinHd8.imm8`, `rsp` `AxSpinHd8.rsp`.  Lean-only: `AxSpinHd8.rowHoldingPOfFull`, `AxSpinHd8.holdEpiGr` (P1); stage-2 P-form
(unqualified, grepped unique): `RowHoldingP`, `holdWrP`, `holdEpiP` (+ 1 local macro).

**Dropped:** `ret_pin` (deviation 1: the return-fetch conjunct is gone; no other Rocq file uses
it).  Rocq 24 definitions/lemmas (+ 2 local instances, inlined); Lean 23.
-/
import Weak.AxSpinE8
import Weak.AxSpinHd4
import Weak.AxSpinHd5
import Weak.AxSpinHd6

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D LeanRV64D.Functions

/-! # 1. `RowHolding` -/

/-- Rocq `fe`: a read of `n` bytes (a fetch-shaped item). -/
def AxSpinHd8.fe (n : Nat) (lb : Lbl) : Prop := ∃ aq b, aident lb = .IRead aq b n
/-- Rocq `st8`: a plain 8-byte store at `pa`. -/
def AxSpinHd8.st8 (pa : Int) (lb : Lbl) : Prop :=
  ∃ vw cls, lb = .LStore false pa vw cls ∧ vw.length = 8
/-- Rocq `rd8`: an 8-byte read at `pa`. -/
def AxSpinHd8.rd8 (pa : Int) (lb : Lbl) : Prop := ∃ aq, aident lb = .IRead aq pa 8

/-- Rocq `lshape`: the long window outside mycpu's (deviation 1: offsets `0..4` and `9..11`;
no fetch arms). -/
def AxSpinHd8.lshape (plk pcl pra ps0 ps1 : Int) (j : Nat) (lb : Lbl) : Prop :=
  match j with
  | 0 => ∃ aq, aident lb = .IRead aq plk 4
  | 1 => AxSpinHd8.st8 pra lb
  | 2 => AxSpinHd8.st8 ps0 lb
  | 3 => AxSpinHd8.st8 ps1 lb
  | 4 => AxSpinHd8.rd8 pcl lb
  | 9 => AxSpinHd8.rd8 pra lb
  | 10 => AxSpinHd8.rd8 ps0 lb
  | 11 => AxSpinHd8.rd8 ps1 lb
  | _ => False

/-- Rocq `sshape`: the short window (deviation 1: only the lw). -/
def AxSpinHd8.sshape (plk : Int) (j : Nat) (lb : Lbl) : Prop :=
  match j with
  | 0 => ∃ aq, aident lb = .IRead aq plk 4
  | _ => False

/-- Rocq `lk_branch`: the lw's ROW VALUE fixes c.bnez's direction (deviation 1: item `k`). -/
def lkBranch (row : List Lbl) (k : Nat) (hb : Bool) : Prop :=
  ∃ lb vs, row[k]? = some lb ∧ lblValue lb = some vs ∧ hb = (ldRes false 4 vs != 0#64)

/-- Rocq `Row_holding` (deviation 1: no fetch items, no `pretm`/`pret`/`nret`). -/
def RowHolding (k : Nat) (row : List Lbl) (hb : Bool) (plk pcl pra ps0 ps1 pram ps0m : Int) :
    Prop :=
  lkBranch row k hb ∧
  match hb with
  | true =>
    k + 12 < row.length ∧
    (∀ j, j < 12 → (j < 5 ∨ 8 < j) →
      ∃ lb, row[k + j]? = some lb ∧ AxSpinHd8.lshape plk pcl pra ps0 ps1 j lb) ∧
    RowMycpu (k + 5) row pram ps0m
  | false =>
    k + 1 < row.length ∧
    (∀ j, j < 1 → ∃ lb, row[k + j]? = some lb ∧ AxSpinHd8.sshape plk j lb)

/-- (Lean-only, stage 2 P-form) `RowHolding` on a PREFIX row: the branch fact is guarded by the
lw's presence (`k < row.length`) and every window item that is PRESENT (`k + j < row.length`) has
its shape; no length conjunct (the row may end anywhere in the window; the end cases are the
P-forms' hook / end continuations). -/
def RowHoldingP (k : Nat) (row : List Lbl) (hb : Bool) (plk pcl pra ps0 ps1 pram ps0m : Int) :
    Prop :=
  (k < row.length → lkBranch row k hb) ∧
  match hb with
  | true =>
    (∀ j, j < 12 → (j < 5 ∨ 8 < j) → k + j < row.length →
      ∃ lb, row[k + j]? = some lb ∧ AxSpinHd8.lshape plk pcl pra ps0 ps1 j lb) ∧
    RowMycpuP (k + 5) row pram ps0m
  | false =>
    (∀ j, j < 1 → k + j < row.length → ∃ lb, row[k + j]? = some lb ∧ AxSpinHd8.sshape plk j lb)

/-- (Lean-only) a full holding window is a prefix window. -/
theorem AxSpinHd8.rowHoldingPOfFull (k : Nat) (row : List Lbl) (hb : Bool)
    (plk pcl pra ps0 ps1 pram ps0m : Int) :
    RowHolding k row hb plk pcl pra ps0 ps1 pram ps0m →
    RowHoldingP k row hb plk pcl pra ps0 ps1 pram ps0m := by
  intro HR
  obtain ⟨Hb, HRp⟩ := HR
  refine ⟨fun _ => Hb, ?_⟩
  cases hb with
  | true =>
    obtain ⟨_, Hsh, HRm⟩ := HRp
    exact ⟨fun j Hj Hr _ => Hsh j Hj Hr, AxSpinE8.rowMycpuPOfFull _ _ _ _ HRm⟩
  | false =>
    obtain ⟨_, Hsh⟩ := HRp
    exact fun j Hj _ => Hsh j Hj

/-- Rocq `disj8`: disjoint 8-byte slots. -/
def disj8 (a b : Int) : Prop := a + 8 ≤ b ∨ b + 8 ≤ a

/-- Rocq `slots_disj`: pairwise-disjoint 8-byte slots. -/
def slotsDisj (l : List Int) : Prop :=
  ∀ (j1 j2 : Nat) (a b : Int), j1 ≠ j2 → l[j1]? = some a → l[j2]? = some b → disj8 a b

/-- Rocq `slots_disj_at`. -/
theorem slotsDisjAt (l : List Int) (j1 j2 : Nat) (a b : Int) :
    slotsDisj l → j1 ≠ j2 → l[j1]? = some a → l[j2]? = some b → disj8 a b :=
  fun H => H j1 j2 a b

/-- Rocq `hres`: seqz (s1 − a0). -/
def hres (s1 a0 : BitVec 64) : BitVec 64 :=
  zero_extend (m := 64) (bool_to_bit (zopz0zI_u (s1 - a0) (sign_extend (m := 64) (1#12))))

/-! # 2. Row facts -/

/-- Rocq `lshape_inv` (deviation 1: spills at `1/2/3`). -/
theorem lshapeInv (plk pcl pra ps0 ps1 : Int) (j : Nat) (lb : Lbl) :
    AxSpinHd8.lshape plk pcl pra ps0 ps1 j lb →
    (j = 1 ∧ AxSpinHd8.st8 pra lb) ∨ (j = 2 ∧ AxSpinHd8.st8 ps0 lb) ∨
    (j = 3 ∧ AxSpinHd8.st8 ps1 lb) ∨ ∃ aq b n, aident lb = .IRead aq b n := by
  intro Hs
  match j, Hs with
  | 0, ⟨aq, h⟩ => exact Or.inr (Or.inr (Or.inr ⟨aq, _, _, h⟩))
  | 1, Hs => exact Or.inl ⟨rfl, Hs⟩
  | 2, Hs => exact Or.inr (Or.inl ⟨rfl, Hs⟩)
  | 3, Hs => exact Or.inr (Or.inr (Or.inl ⟨rfl, Hs⟩))
  | 4, ⟨aq, h⟩ => exact Or.inr (Or.inr (Or.inr ⟨aq, _, _, h⟩))
  | 9, ⟨aq, h⟩ => exact Or.inr (Or.inr (Or.inr ⟨aq, _, _, h⟩))
  | 10, ⟨aq, h⟩ => exact Or.inr (Or.inr (Or.inr ⟨aq, _, _, h⟩))
  | 11, ⟨aq, h⟩ => exact Or.inr (Or.inr (Or.inr ⟨aq, _, _, h⟩))
  | 5, Hs => exact Hs.elim
  | 6, Hs => exact Hs.elim
  | 7, Hs => exact Hs.elim
  | 8, Hs => exact Hs.elim
  | n + 12, Hs => exact Hs.elim

/-- Rocq `mshape_inv` (deviation 1: over AxSpinE8's `mshape`, spills at `0/1`). -/
theorem mshapeInv (pra ps0 : Int) (j : Nat) (lb : Lbl) :
    mshape pra ps0 j lb →
    (j = 0 ∧ AxSpinHd8.st8 pra lb) ∨ (j = 1 ∧ AxSpinHd8.st8 ps0 lb) ∨
    ∃ aq b n, aident lb = .IRead aq b n := by
  intro Hs
  match j, Hs with
  | 0, Hs => exact Or.inl ⟨rfl, Hs⟩
  | 1, Hs => exact Or.inr (Or.inl ⟨rfl, Hs⟩)
  | 2, ⟨aq, h⟩ => exact Or.inr (Or.inr ⟨aq, _, _, h⟩)
  | 3, ⟨aq, h⟩ => exact Or.inr (Or.inr ⟨aq, _, _, h⟩)
  | n + 4, Hs => exact Hs.elim

/-- Rocq `st8_wr`. -/
theorem st8Wr (pa : Int) (lb : Lbl) (rl : Bool) (b : Int) (m : Nat) :
    AxSpinHd8.st8 pa lb → aidentWr (aident lb) = some (rl, b, m) → b = pa ∧ m = 8 := by
  rintro ⟨vw, cls, rfl, Hl⟩ Hw
  simp only [aident, aidentWr, Option.some.injEq, Prod.mk.injEq] at Hw
  obtain ⟨-, rfl, rfl⟩ := Hw
  exact ⟨rfl, Hl⟩

/-- Rocq `rd_nowr`. -/
theorem rdNowr (lb : Lbl) (aq : Bool) (b : Int) (n : Nat) (rl : Bool) (b' : Int) (m : Nat) :
    aident lb = .IRead aq b n → aidentWr (aident lb) = some (rl, b', m) → False := by
  intro h Hw
  rw [h] at Hw
  simp only [aidentWr, reduceCtorEq] at Hw

/-- Rocq `hold_wr`: the only writes of the long window are the five spills (deviation 1). -/
theorem holdWr (k : Nat) (row : List Lbl) (plk pcl pra ps0 ps1 pram ps0m : Int) :
    RowHolding k row true plk pcl pra ps0 ps1 pram ps0m →
    ∀ (j : Nat) (lb : Lbl) (rl : Bool) (b : Int) (m : Nat), j < 12 → row[k + j]? = some lb →
      aidentWr (aident lb) = some (rl, b, m) →
      m = 8 ∧ ((j = 1 ∧ b = pra) ∨ (j = 2 ∧ b = ps0) ∨ (j = 3 ∧ b = ps1) ∨
               (j = 5 ∧ b = pram) ∨ (j = 6 ∧ b = ps0m)) := by
  intro HR j lb rl b m Hj Hlb Hw
  obtain ⟨_, _, Hsh, HRm⟩ := HR
  by_cases Hm : 5 ≤ j ∧ j ≤ 8
  · obtain ⟨_, Hmsh⟩ := HRm
    obtain ⟨lb0, Hlb0, Hs⟩ := Hmsh (j - 5) (by omega)
    rw [show k + 5 + (j - 5) = k + j by omega, Hlb] at Hlb0
    cases Hlb0
    rcases mshapeInv _ _ _ _ Hs with ⟨Hj0, Hst⟩ | ⟨Hj1, Hst⟩ | ⟨aq, b0, n0, Hid⟩
    · obtain ⟨rfl, rfl⟩ := st8Wr _ _ _ _ _ Hst Hw
      exact ⟨rfl, Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, rfl⟩)))⟩
    · obtain ⟨rfl, rfl⟩ := st8Wr _ _ _ _ _ Hst Hw
      exact ⟨rfl, Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega, rfl⟩)))⟩
    · exact (rdNowr _ _ _ _ _ _ _ Hid Hw).elim
  · obtain ⟨lb0, Hlb0, Hs⟩ := Hsh j Hj (by omega)
    rw [Hlb] at Hlb0
    cases Hlb0
    rcases lshapeInv _ _ _ _ _ _ _ Hs with
      ⟨rfl, Hst⟩ | ⟨rfl, Hst⟩ | ⟨rfl, Hst⟩ | ⟨aq, b0, n0, Hid⟩
    · obtain ⟨rfl, rfl⟩ := st8Wr _ _ _ _ _ Hst Hw
      exact ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩
    · obtain ⟨rfl, rfl⟩ := st8Wr _ _ _ _ _ Hst Hw
      exact ⟨rfl, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
    · obtain ⟨rfl, rfl⟩ := st8Wr _ _ _ _ _ Hst Hw
      exact ⟨rfl, Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))⟩
    · exact (rdNowr _ _ _ _ _ _ _ Hid Hw).elim

/-- (Lean-only, stage 2) `holdWr` on a PREFIX window (`RowHoldingP`): a present item is
inside the row, so the same case analysis applies. -/
theorem holdWrP (k : Nat) (row : List Lbl) (plk pcl pra ps0 ps1 pram ps0m : Int) :
    RowHoldingP k row true plk pcl pra ps0 ps1 pram ps0m →
    ∀ (j : Nat) (lb : Lbl) (rl : Bool) (b : Int) (m : Nat), j < 12 → row[k + j]? = some lb →
      aidentWr (aident lb) = some (rl, b, m) →
      m = 8 ∧ ((j = 1 ∧ b = pra) ∨ (j = 2 ∧ b = ps0) ∨ (j = 3 ∧ b = ps1) ∨
               (j = 5 ∧ b = pram) ∨ (j = 6 ∧ b = ps0m)) := by
  intro HR j lb rl b m Hj Hlb Hw
  have Hin : k + j < row.length := (List.getElem?_eq_some_iff.1 Hlb).1
  obtain ⟨_, Hsh, Hmsh⟩ := HR
  by_cases Hm : 5 ≤ j ∧ j ≤ 8
  · obtain ⟨lb0, Hlb0, Hs⟩ := Hmsh (j - 5) (by omega) (by omega)
    rw [show k + 5 + (j - 5) = k + j by omega, Hlb] at Hlb0
    cases Hlb0
    rcases mshapeInv _ _ _ _ Hs with ⟨Hj0, Hst⟩ | ⟨Hj1, Hst⟩ | ⟨aq, b0, n0, Hid⟩
    · obtain ⟨rfl, rfl⟩ := st8Wr _ _ _ _ _ Hst Hw
      exact ⟨rfl, Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, rfl⟩)))⟩
    · obtain ⟨rfl, rfl⟩ := st8Wr _ _ _ _ _ Hst Hw
      exact ⟨rfl, Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega, rfl⟩)))⟩
    · exact (rdNowr _ _ _ _ _ _ _ Hid Hw).elim
  · obtain ⟨lb0, Hlb0, Hs⟩ := Hsh j Hj (by omega) Hin
    rw [Hlb] at Hlb0
    cases Hlb0
    rcases lshapeInv _ _ _ _ _ _ _ Hs with
      ⟨rfl, Hst⟩ | ⟨rfl, Hst⟩ | ⟨rfl, Hst⟩ | ⟨aq, b0, n0, Hid⟩
    · obtain ⟨rfl, rfl⟩ := st8Wr _ _ _ _ _ Hst Hw
      exact ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩
    · obtain ⟨rfl, rfl⟩ := st8Wr _ _ _ _ _ Hst Hw
      exact ⟨rfl, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
    · obtain ⟨rfl, rfl⟩ := st8Wr _ _ _ _ _ Hst Hw
      exact ⟨rfl, Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))⟩
    · exact (rdNowr _ _ _ _ _ _ _ Hid Hw).elim

/-- Rocq `fe2_facts`: a 2-byte read item is neither a write nor a read of `n ≠ 2` bytes. -/
theorem fe2Facts (row : List Lbl) (k' : Nat) (lb : Lbl) :
    row[k']? = some lb → AxSpinHd8.fe 2 lb →
    (∀ lb', row[k']? = some lb' → aidentWr (aident lb') = none) ∧
    (∀ (lb' : Lbl) (aq : Bool) (b : Int) (n : Nat), row[k']? = some lb' →
      aidentRd (aident lb') = some (aq, b, n) → n = 2) := by
  rintro Hlb ⟨aq, b, Hid⟩
  refine ⟨fun lb' Hlb' => ?_, fun lb' aq' b' n Hlb' Hrd => ?_⟩
  · rw [Hlb] at Hlb'
    cases Hlb'
    rw [Hid]
    rfl
  · rw [Hlb] at Hlb'
    cases Hlb'
    rw [Hid] at Hrd
    simp only [aidentRd, Option.some.injEq, Prod.mk.injEq] at Hrd
    exact Hrd.2.2.symm

/-! # 3. THE EPILOGUE -/

/-- Rocq `r9`. -/
abbrev AxSpinHd8.r9 : BitVec 5 := 9#5
/-- Rocq `imm24`. -/
def AxSpinHd8.imm24 : BitVec 12 := zero_extend (m := 12) (3#6 +++ 0b000#3)
/-- Rocq `imm16`. -/
def AxSpinHd8.imm16 : BitVec 12 := zero_extend (m := 12) (2#6 +++ 0b000#3)
/-- Rocq `imm8`. -/
def AxSpinHd8.imm8 : BitVec 12 := zero_extend (m := 12) (1#6 +++ 0b000#3)
/-- Rocq `rsp` (deviation 2: `2#5`). -/
abbrev AxSpinHd8.rsp : BitVec 5 := 2#5

/-- (Rocq `zsimp`) evaluate the closed `upd` tests. -/
local macro "ax_spin_hd8_zsimp" loc:(ppSpace Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| simp (disch := decide) only [AxSpinE8.updSame, AxSpinE8.updOther, AxSpinE8.updZero]
    $[$loc]?)

section epi
variable {hlc : HasLC} {GF : BundledGFunctors.{0,0,0}} [InvGS_gen hlc GF] [AxannotGS GF]
  [AxSpinX.Xv6G GF]
variable (L : Xlay) (GT : GdexecT) (nm : Xv6N)
variable (HL : xlayOk L) (Hcons : rvwmoCatConsistent (gtAdGd GT))
variable (σi : ExecSt) (T : PTree) (satp0 : BitVec 64)
variable (hmode : _get_Satp64_Mode (Mk_Satp64 satp0) = 8#4)
variable (hasid : zero_extend (m := 16) (satp_to_asid satp0) = 0#16)
variable (hppn : BitVec.setWidth 44 (satp_to_ppn satp0) = T.base)
variable (i : Agent) (cpu : CPU)
variable (Hfix : textFixed (gtAdGd GT) i (imgS σi))
variable (Htxh : holdingText σi T)
variable (Ψ : Athread → IProp GF)
variable (HΨmid : ∀ s, midState s → s.atK = (AxOpsem.grow (gtAdGd GT) i).length →
  ⊢ @postLifting GF (AxSpinX2.xG L GT nm) Ψ i s)

include HL Hcons hmode hasid hppn Hfix Htxh HΨmid in
/-- (Lean-only, P1) THE GATED CORE of `holdEpiP`: its script with the ra pin replaced by the reload
GATE `AxSpinT2i.Gate GT i (k + 9) (stBytes 8 ret)` (`ret` still a parameter) and the main
continuation additionally RECEIVING `k + 12 < LEN` (it is only reached past the end boundary).  At
the ra reload's boundary `k + 10`: `by_cases` on the reloaded value — equal ⇒ the P-form script;
else the gate gives `LEN ≤ k + 10` and the arm is `AxSpinT2i.cutReloadG` with the reload's
`RLfact` when `ret`'s bytes are the spill's (`stBytes 8 ret = stBytes 8 ra0`; always so at the G
call sites, `ret := ra0`), otherwise the hook `HΨend` at `k + 10` (only reachable from
`holdEpiP`'s free `ret`). -/
theorem AxSpinHd8.holdEpiGr (k : Nat) (rs : RegFile) (ib : Ibch) (ret : BitVec 64) (plk pcl : Int)
    (Pra Ps0 Ps1 Pram Ps0m : BitVec 64) (hsp1 ra0 s00 s10 : BitVec 64) :
    -- the row
    RowHoldingP k (AxOpsem.grow (gtAdGd GT) i) true plk pcl (paZ Pra) (paZ Ps0) (paZ Ps1)
      (paZ Pram) (paZ Ps0m) →
    noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Pra) →
    noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Ps0) →
    noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Ps1) →
    slotsDisj [paZ Pra, paZ Ps0, paZ Ps1, paZ Pram, paZ Ps0m] →
    graphData (gtAdGd GT) (i, k + 1) = some (stBytes 8 ra0) →
    graphData (gtAdGd GT) (i, k + 2) = some (stBytes 8 s00) →
    graphData (gtAdGd GT) (i, k + 3) = some (stBytes 8 s10) →
    -- the boundary state
    ctrlOkSW T satp0 rs → rs .PC = pch 0x1a → hitW rs (pch 0) → gprVal rs AxSpinE8.r2 = hsp1 →
    -- the three stack slots
    dataAtS σi T (.Load .Data) (hsp1 + sign_extend (m := 64) AxSpinHd8.imm24) 8 Pra →
    hitW rs (hsp1 + sign_extend (m := 64) AxSpinHd8.imm24) →
    dataAtS σi T (.Load .Data) (hsp1 + sign_extend (m := 64) AxSpinHd8.imm16) 8 Ps0 →
    hitW rs (hsp1 + sign_extend (m := 64) AxSpinHd8.imm16) →
    dataAtS σi T (.Load .Data) (hsp1 + sign_extend (m := 64) AxSpinHd8.imm8) 8 Ps1 →
    hitW rs (hsp1 + sign_extend (m := 64) AxSpinHd8.imm8) →
    (∀ j : Nat, j < 8 → priv L (paZ Pra + (j : Int)) i) → ¬ L.xlText (paZ Pra) →
    (∀ j : Nat, j < 8 → priv L (paZ Ps0 + (j : Int)) i) → ¬ L.xlText (paZ Ps0) →
    (∀ j : Nat, j < 8 → priv L (paZ Ps1 + (j : Int)) i) → ¬ L.xlText (paZ Ps1) →
    -- the return address (P1: the ra reload GATE against `ret`'s bytes)
    AxSpinT2i.Gate GT i (k + 9) (stBytes 8 ret) → jalrTgt 0#12 ret = ret →
    -- the row-end hook (stage 2, design §B / Q-S2-2), over the window [k + 9, k + 11]
    (∀ k' : Nat, k + 9 ≤ k' → k' ≤ k + 11 → (AxOpsem.grow (gtAdGd GT) i).length ≤ k' →
      ∀ pr : Pexv6,
        ⊢ @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
          ⟨pr, k'⟩ Ψ) →
    ⊢ ((⌜k + 12 < (AxOpsem.grow (gtAdGd GT) i).length⌝ -∗
        ∀ (vra vs0 vs1 : List (BitVec 8)) (rs' : RegFile) (ib' : Ibch),
        ⌜ctrlOkSW T satp0 rs' ∧ rs' .PC = ret ∧ rs' .tlb = rs .tlb ∧
          gprVal rs' AxSpinE8.r10 = hres (gprVal rs AxSpinHd8.r9) (gprVal rs AxSpinE8.r10) ∧
          gprVal rs' AxSpinE8.r2 = hsp1 + sign_extend (m := 64) (caddi16spImm 2#6) ∧
          vra.length = 8 ∧ vs0.length = 8 ∧ vs1.length = 8 ∧
          gprVal rs' AxSpinE8.r1 = ldRes false 8 vra ∧ gprVal rs' AxSpinE8.r8 = ldRes false 8 vs0 ∧
          gprVal rs' AxSpinHd8.r9 = ldRes false 8 vs1 ∧
          (∀ r : BitVec 5, r.toNat ≠ 1 → r.toNat ≠ 2 → r.toNat ≠ 8 → r.toNat ≠ 9 →
            r.toNat ≠ 10 → gprVal rs' r = gprVal rs r) ∧
          graphValue (gtAdGd GT) (i, k + 9) = some vra ∧
          graphValue (gtAdGd GT) (i, k + 10) = some vs0 ∧
          graphValue (gtAdGd GT) (i, k + 11) = some vs1⌝ -∗
        AxAnnot.annotOwn (GF := GF) (i, k + 9)
          iprop(⌜RLfact GT i (paZ Pra) (k + 9) (stBytes 8 ra0)⌝) -∗
        AxAnnot.annotOwn (GF := GF) (i, k + 10)
          iprop(⌜RLfact GT i (paZ Ps0) (k + 10) (stBytes 8 s00)⌝) -∗
        AxAnnot.annotOwn (GF := GF) (i, k + 11)
          iprop(⌜RLfact GT i (paZ Ps1) (k + 11) (stBytes 8 s10)⌝) -∗
        @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
          ⟨.PHart cpu (.pure ()) rs' none ib', k + 12⟩ Ψ) ∧
      (∀ (vra vs0 vs1 : List (BitVec 8)) (pr : Pexv6),
        ⌜(AxOpsem.grow (gtAdGd GT) i).length = k + 12 ∧
          vra.length = 8 ∧ vs0.length = 8 ∧ vs1.length = 8 ∧
          graphValue (gtAdGd GT) (i, k + 9) = some vra ∧
          graphValue (gtAdGd GT) (i, k + 10) = some vs0 ∧
          graphValue (gtAdGd GT) (i, k + 11) = some vs1⌝ -∗
        AxAnnot.annotOwn (GF := GF) (i, k + 9)
          iprop(⌜RLfact GT i (paZ Pra) (k + 9) (stBytes 8 ra0)⌝) -∗
        AxAnnot.annotOwn (GF := GF) (i, k + 10)
          iprop(⌜RLfact GT i (paZ Ps0) (k + 10) (stBytes 8 s00)⌝) -∗
        AxAnnot.annotOwn (GF := GF) (i, k + 11)
          iprop(⌜RLfact GT i (paZ Ps1) (k + 11) (stBytes 8 s10)⌝) -∗
        @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
          ⟨pr, k + 12⟩ Ψ)) -∗
      @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
        ⟨.PHart cpu (.pure ()) rs none ib, k + 9⟩ Ψ := by
  intro HR Hnr_ra Hnr_s0 Hnr_s1 HD Hd1 Hd2 Hd3 Hc0 HPC0 Hhit0 Hsp0 HdaL_ra Hh_ra HdaL_s0 Hh_s0
    HdaL_s1 Hh_s1 Hpr_ra Hnt_ra Hpr_s0 Hnt_s0 Hpr_s1 Hnt_s1 Hgate Hret HΨend
  iintro C
  -- row end at k + 9
  by_cases E9 : (AxOpsem.grow (gtAdGd GT) i).length ≤ k + 9
  · iclear C
    iapply (HΨend _ (by omega) (by omega) (by omega) _)
  have HW := holdWrP _ _ _ _ _ _ _ _ _ HR
  obtain ⟨_, Hsh, _⟩ := HR
  obtain ⟨lb9, Hlb9, aq9, Hid9⟩ := Hsh 9 (by omega) (by omega) (by omega)
  unfold slotsDisj disj8 at HD
  have XR := XxReg L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu Hfix Ψ HΨmid
  have XL := XxLd L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu Hfix Ψ HΨmid
  have XT := XxRet L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu Hfix Ψ HΨmid
  -- the spills, as row labels
  obtain ⟨lb1, Hlb1, vw1, cls1, rfl, Hlvw1⟩ := Hsh 1 (by omega) (by omega) (by omega)
  obtain ⟨lb2, Hlb2, vw2, cls2, rfl, Hlvw2⟩ := Hsh 2 (by omega) (by omega) (by omega)
  obtain ⟨lb3, Hlb3, vw3, cls3, rfl, Hlvw3⟩ := Hsh 3 (by omega) (by omega) (by omega)
  have Hvw1 : vw1 = stBytes 8 ra0 := by
    rw [graphData, AxWp.growLookup _ _ _ _ Hlb1] at Hd1
    exact Option.some.inj Hd1
  have Hvw2 : vw2 = stBytes 8 s00 := by
    rw [graphData, AxWp.growLookup _ _ _ _ Hlb2] at Hd2
    exact Option.some.inj Hd2
  have Hvw3 : vw3 = stBytes 8 s10 := by
    rw [graphData, AxWp.growLookup _ _ _ _ Hlb3] at Hd3
    exact Option.some.inj Hd3
  subst Hvw1 Hvw2 Hvw3
  -- ---- 0x1a: sub a0,s1,a0 (k+9) ----
  iapply (XR _ rs (k + 9) (pch 0x1a) false h1a _ _ (retxRefl cpu rs (k + 9) ib) Hc0 HPC0
    (hitWSvpn rs (pch 0x1a) (pch 0) (by decide) Hhit0) (htok1a σi T satp0 Htxh)
    (AxSpinE8.owOkSome 10#5 _ (by decide)) rfFH1a
    (certSub _ rs (pch 0x1a) false 10#5 9#5 10#5 (by decide)) (by omega))
  iintro %rs1 %ib1 %HG1
  have HF1 := stepRegs T satp0 _ rs _ _ _ _ _ rs1 (fun _ => rfl) HG1
  have HPC1 : rs1 .PC = pch 0x1e := by rw [gbPc T satp0 _ _ _ _ _ _ HG1]; decide
  have Htl1 : rs1 .tlb = rs .tlb := gbTlb T satp0 _ _ _ _ _ _ HG1
  -- ---- 0x1e: seqz a0,a0 (k+9) ----
  have Hc1 := certSltiu (ctrlOkSW T satp0) rs1 (pch 0x1e) false 10#5 10#5 1#12 (by decide)
  simp only [HF1] at Hc1
  ax_spin_hd8_zsimp at Hc1
  iapply (XR _ rs1 (k + 9) (pch 0x1e) false h1e _ _ (retxRefl cpu rs1 (k + 9) ib1)
    (gbCtrl T satp0 _ _ _ _ _ _ HG1) HPC1
    (hitWSvpn rs1 (pch 0x1e) (pch 0) (by decide) (hitWAgree rs rs1 _ Htl1 Hhit0))
    (htok1e σi T satp0 Htxh) (AxSpinE8.owOkSome 10#5 _ (by decide)) rfFH1e Hc1 (by omega))
  iintro %rs2 %ib2 %HG2
  have HF2 := stepRegs T satp0 _ rs1 _ _ _ _ _ rs2 HF1 HG2
  have HPC2 : rs2 .PC = pch 0x22 := by rw [gbPc T satp0 _ _ _ _ _ _ HG2]; decide
  have Htl2 : rs2 .tlb = rs .tlb := (gbTlb T satp0 _ _ _ _ _ _ HG2).trans Htl1
  -- ---- 0x22: c.ldsp ra,24(sp) — RELOAD of ra's spill (k+1), at k+9 ----
  iapply (XL _ rs2 (k + 9) (pch 0x22) true AxSpinHd8.imm24 2#5 1#5
    (hsp1 + sign_extend (m := 64) AxSpinHd8.imm24) Pra (k + 1) (stBytes 8 ra0) cls1
    (retxRefl cpu rs2 (k + 9) ib2) (gbCtrl T satp0 _ _ _ _ _ _ HG2) HPC2
    (hitWSvpn rs2 (pch 0x22) (pch 0) (by decide) (hitWAgree rs rs2 _ Htl2 Hhit0))
    (htok22 σi T satp0 Htxh) (by decide) (by rw [HF2]; ax_spin_hd8_zsimp; rw [← Hsp0])
    HdaL_ra (hitWAgree rs rs2 _ Htl2 Hh_ra) Hpr_ra Hnt_ra Hnr_ra Hlb1 Hlvw1 (by omega) ?_
    (by omega))
  · intro k' lb' rl b m ⟨h1, h2⟩ Hl Hid
    rw [show k' = k + (k' - k) by omega] at Hl
    obtain ⟨rfl, Hc⟩ := HW (k' - k) lb' rl b m (by omega) Hl Hid
    rcases Hc with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩
    · omega
    · rcases HD 0 1 _ _ (by decide) rfl rfl with h | h <;> omega
    · rcases HD 0 2 _ _ (by decide) rfl rfl with h | h <;> omega
    · rcases HD 0 3 _ _ (by decide) rfl rfl with h | h <;> omega
    · rcases HD 0 4 _ _ (by decide) rfl rfl with h | h <;> omega
  iintro %vra %rs3 %ib3 %Hlvra %HG3 %Hgv9 H9
  -- P1 GATE at the ra reload's boundary k + 10: a wrong reloaded value ends the row there
  by_cases Hv : ¬ vra = stBytes 8 ret
  · iclear C
    by_cases Hs : stBytes 8 ret = stBytes 8 ra0
    · -- `ret`'s bytes are the spill's: the reload CUT refutes the arm (RLfact read back)
      rw [Hs] at Hv Hgate
      iapply (AxSpinT2i.cutReloadG L GT nm Hcons i (k + 9) (paZ Pra) (stBytes 8 ra0) vra Ψ
        ⟨lb9, Hlb9, aq9, Hid9⟩ Hlvw1 Hgv9 Hv Hgate _) $$ H9
    · have Hend := AxSpinT2i.lenOfGate Hgate Hgv9 Hv
      iclear H9
      iapply (HΨend _ (by omega) (by omega) (by omega) _)
  have Hvra : vra = stBytes 8 ret := Classical.byContradiction Hv
  -- row end at k + 10
  by_cases E10 : (AxOpsem.grow (gtAdGd GT) i).length ≤ k + 9 + 1
  · iclear C
    iclear H9
    iapply (HΨend _ (by omega) (by omega) (by omega) _)
  have HF3 := stepRegs T satp0 _ rs2 _ _ _ _ _ rs3 HF2 HG3
  have HPC3 : rs3 .PC = pch 0x24 := by rw [gbPc T satp0 _ _ _ _ _ _ HG3]; decide
  have Htl3 : rs3 .tlb = rs .tlb := (gbTlb T satp0 _ _ _ _ _ _ HG3).trans Htl2
  -- ---- 0x24: c.ldsp s0,16(sp) — RELOAD of s0's spill (k+2), at k+10 ----
  iapply (XL _ rs3 (k + 10) (pch 0x24) true AxSpinHd8.imm16 2#5 8#5
    (hsp1 + sign_extend (m := 64) AxSpinHd8.imm16) Ps0 (k + 2) (stBytes 8 s00) cls2
    (retxRefl cpu rs3 (k + 10) ib3) (gbCtrl T satp0 _ _ _ _ _ _ HG3) HPC3
    (hitWSvpn rs3 (pch 0x24) (pch 0) (by decide) (hitWAgree rs rs3 _ Htl3 Hhit0))
    (htok24 σi T satp0 Htxh) (by decide) (by rw [HF3]; ax_spin_hd8_zsimp; rw [← Hsp0])
    HdaL_s0 (hitWAgree rs rs3 _ Htl3 Hh_s0) Hpr_s0 Hnt_s0 Hnr_s0 Hlb2 Hlvw2 (by omega) ?_
    (by omega))
  · intro k' lb' rl b m ⟨h1, h2⟩ Hl Hid
    rw [show k' = k + (k' - k) by omega] at Hl
    obtain ⟨rfl, Hc⟩ := HW (k' - k) lb' rl b m (by omega) Hl Hid
    rcases Hc with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩
    · omega
    · omega
    · rcases HD 1 2 _ _ (by decide) rfl rfl with h | h <;> omega
    · rcases HD 1 3 _ _ (by decide) rfl rfl with h | h <;> omega
    · rcases HD 1 4 _ _ (by decide) rfl rfl with h | h <;> omega
  iintro %vs0 %rs4 %ib4 %Hlvs0 %HG4 %Hgv10 H10
  -- row end at k + 11
  by_cases E11 : (AxOpsem.grow (gtAdGd GT) i).length ≤ k + 10 + 1
  · iclear C
    iclear H9
    iclear H10
    iapply (HΨend _ (by omega) (by omega) (by omega) _)
  have HF4 := stepRegs T satp0 _ rs3 _ _ _ _ _ rs4 HF3 HG4
  have HPC4 : rs4 .PC = pch 0x26 := by rw [gbPc T satp0 _ _ _ _ _ _ HG4]; decide
  have Htl4 : rs4 .tlb = rs .tlb := (gbTlb T satp0 _ _ _ _ _ _ HG4).trans Htl3
  -- ---- 0x26: c.ldsp s1,8(sp) — RELOAD of s1's spill (k+3), at k+11 ----
  iapply (XL _ rs4 (k + 11) (pch 0x26) true AxSpinHd8.imm8 2#5 9#5
    (hsp1 + sign_extend (m := 64) AxSpinHd8.imm8) Ps1 (k + 3) (stBytes 8 s10) cls3
    (retxRefl cpu rs4 (k + 11) ib4) (gbCtrl T satp0 _ _ _ _ _ _ HG4) HPC4
    (hitWSvpn rs4 (pch 0x26) (pch 0) (by decide) (hitWAgree rs rs4 _ Htl4 Hhit0))
    (htok26 σi T satp0 Htxh) (by decide) (by rw [HF4]; ax_spin_hd8_zsimp; rw [← Hsp0])
    HdaL_s1 (hitWAgree rs rs4 _ Htl4 Hh_s1) Hpr_s1 Hnt_s1 Hnr_s1 Hlb3 Hlvw3 (by omega) ?_
    (by omega))
  · intro k' lb' rl b m ⟨h1, h2⟩ Hl Hid
    rw [show k' = k + (k' - k) by omega] at Hl
    obtain ⟨rfl, Hc⟩ := HW (k' - k) lb' rl b m (by omega) Hl Hid
    rcases Hc with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩
    · omega
    · omega
    · omega
    · rcases HD 2 3 _ _ (by decide) rfl rfl with h | h <;> omega
    · rcases HD 2 4 _ _ (by decide) rfl rfl with h | h <;> omega
  iintro %vs1 %rs5 %ib5 %Hlvs1 %HG5 %Hgv11 H11
  -- row end at k + 12: the END CONTINUATION (the caller's designated-cut boundary)
  by_cases E12 : (AxOpsem.grow (gtAdGd GT) i).length ≤ k + 11 + 1
  · icases C with ⟨-, C⟩
    iapply C $$ %vra %vs0 %vs1 %(.PHart cpu (.pure ()) rs5 none ib5 : Pexv6) [] H9 H10 H11
    ipureintro
    exact ⟨by omega, Hlvra, Hlvs0, Hlvs1, Hgv9, Hgv10, Hgv11⟩
  icases C with ⟨C, -⟩
  ispecialize C $$ %(show k + 12 < (AxOpsem.grow (gtAdGd GT) i).length by omega)
  have HF5 := stepRegs T satp0 _ rs4 _ _ _ _ _ rs5 HF4 HG5
  have HPC5 : rs5 .PC = pch 0x28 := by rw [gbPc T satp0 _ _ _ _ _ _ HG5]; decide
  have Htl5 : rs5 .tlb = rs .tlb := (gbTlb T satp0 _ _ _ _ _ _ HG5).trans Htl4
  -- ---- 0x28: c.addi16sp sp,32 (k+12) ----
  have Hc5 := certAddi (ctrlOkSW T satp0) rs5 (pch 0x28) true 2#5 2#5 (caddi16spImm 2#6)
    (by decide)
  simp only [HF5] at Hc5
  ax_spin_hd8_zsimp at Hc5
  iapply (XR _ rs5 (k + 12) (pch 0x28) true h28 _ _ (retxRefl cpu rs5 (k + 12) ib5)
    (gbCtrl T satp0 _ _ _ _ _ _ HG5) HPC5
    (hitWSvpn rs5 (pch 0x28) (pch 0) (by decide) (hitWAgree rs rs5 _ Htl5 Hhit0))
    (htok28 σi T satp0 Htxh) (AxSpinE8.owOkSome 2#5 _ (by decide)) rfFH28 Hc5 (by omega))
  iintro %rs6 %ib6 %HG6
  have HF6 := stepRegs T satp0 _ rs5 _ _ _ _ _ rs6 HF5 HG6
  have HPC6 : rs6 .PC = pch 0x2a := by rw [gbPc T satp0 _ _ _ _ _ _ HG6]; decide
  have Htl6 : rs6 .tlb = rs .tlb := (gbTlb T satp0 _ _ _ _ _ _ HG6).trans Htl5
  -- ---- 0x2a: c.ret (k+12; Q20': no stuck branch, the target is the reloaded ra) ----
  iapply (XT _ rs6 (k + 12) (pch 0x2a) (retxRefl cpu rs6 (k + 12) ib6)
    (gbCtrl T satp0 _ _ _ _ _ _ HG6) HPC6
    (hitWSvpn rs6 (pch 0x2a) (pch 0) (by decide) (hitWAgree rs rs6 _ Htl6 Hhit0))
    (htok2a σi T satp0 Htxh) rfFH2a (by omega))
  iintro %rs' %ib' %HGr
  have HFr := stepRegs0 T satp0 _ rs6 _ _ _ rs' HF6 HGr
  iapply C $$ %vra %vs0 %vs1 %rs' %ib' [] H9 H10 H11
  ipureintro
  refine ⟨gbCtrl T satp0 _ _ _ _ _ _ HGr, ?_, (gbTlb T satp0 _ _ _ _ _ _ HGr).trans Htl6, ?_, ?_,
    Hlvra, Hlvs0, Hlvs1, ?_, ?_, ?_, ?_, Hgv9, Hgv10, Hgv11⟩
  · -- PC = ret: the c.ret target is the reloaded ra (`Hvra`, the gate's equal arm)
    rw [gbPc T satp0 _ _ _ _ _ _ HGr]
    show jalrTgt 0#12 (gprVal rs6 1#5) = ret
    rw [HF6]
    ax_spin_hd8_zsimp
    rw [Hvra, AxSpinE8.ldResStBytes8, Hret]
  · -- a0 = seqz (s1 − a0)
    rw [HFr]
    ax_spin_hd8_zsimp
    rfl
  · -- sp restored
    rw [HFr]
    ax_spin_hd8_zsimp
    rw [Hsp0]
  · rw [HFr]
    ax_spin_hd8_zsimp
  · rw [HFr]
    ax_spin_hd8_zsimp
  · rw [HFr]
    ax_spin_hd8_zsimp
  · -- every other GPR kept
    intro r Hr1 Hr2 Hr8 Hr9 Hr10
    rw [HFr]
    by_cases E0 : r.toNat = 0
    · rw [AxSpinE8.updZero _ _ _ _ E0, AxSpinE8.gprValZero rs r E0]
    · have n1 : r ≠ 1#5 := fun h => Hr1 (by rw [h]; rfl)
      have n2 : r ≠ 2#5 := fun h => Hr2 (by rw [h]; rfl)
      have n8 : r ≠ 8#5 := fun h => Hr8 (by rw [h]; rfl)
      have n9 : r ≠ 9#5 := fun h => Hr9 (by rw [h]; rfl)
      have n10 : r ≠ 10#5 := fun h => Hr10 (by rw [h]; rfl)
      simp (disch := assumption) only [AxSpinE8.updOther]

include HL Hcons hmode hasid hppn Hfix Htxh HΨmid in
/-- (Lean-only, stage 2) THE P-FORM of `holdEpi` on a PREFIX row (`RowHoldingP`; the `Hval` pin
guarded by `k + 9 < LEN`): a `by_cases` on `LEN ≤ position` at the epilogue's row positions
`k + 9 .. k + 12`; the ends at `k + 9 .. k + 11` are the WINDOWED, RESOURCE-FREE hook `HΨend`
(as `AxSpinE8.wpdMycpuP`); the end at `k + 12` (all three reloads done, before c.addi16sp — the
boundary where the CALLER's panic branch is decided) is the second conjunct of the continuation,
which RECEIVES the reloads' graph values and their three annotations (not dropped).
P1: the corollary of the gated core `AxSpinHd8.holdEpiGr` via `AxSpinT2i.gateOfPinG`. -/
theorem holdEpiP (k : Nat) (rs : RegFile) (ib : Ibch) (ret : BitVec 64) (plk pcl : Int)
    (Pra Ps0 Ps1 Pram Ps0m : BitVec 64) (hsp1 ra0 s00 s10 : BitVec 64) :
    -- the row
    RowHoldingP k (AxOpsem.grow (gtAdGd GT) i) true plk pcl (paZ Pra) (paZ Ps0) (paZ Ps1)
      (paZ Pram) (paZ Ps0m) →
    noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Pra) →
    noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Ps0) →
    noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Ps1) →
    slotsDisj [paZ Pra, paZ Ps0, paZ Ps1, paZ Pram, paZ Ps0m] →
    graphData (gtAdGd GT) (i, k + 1) = some (stBytes 8 ra0) →
    graphData (gtAdGd GT) (i, k + 2) = some (stBytes 8 s00) →
    graphData (gtAdGd GT) (i, k + 3) = some (stBytes 8 s10) →
    -- the boundary state
    ctrlOkSW T satp0 rs → rs .PC = pch 0x1a → hitW rs (pch 0) → gprVal rs AxSpinE8.r2 = hsp1 →
    -- the three stack slots
    dataAtS σi T (.Load .Data) (hsp1 + sign_extend (m := 64) AxSpinHd8.imm24) 8 Pra →
    hitW rs (hsp1 + sign_extend (m := 64) AxSpinHd8.imm24) →
    dataAtS σi T (.Load .Data) (hsp1 + sign_extend (m := 64) AxSpinHd8.imm16) 8 Ps0 →
    hitW rs (hsp1 + sign_extend (m := 64) AxSpinHd8.imm16) →
    dataAtS σi T (.Load .Data) (hsp1 + sign_extend (m := 64) AxSpinHd8.imm8) 8 Ps1 →
    hitW rs (hsp1 + sign_extend (m := 64) AxSpinHd8.imm8) →
    (∀ j : Nat, j < 8 → priv L (paZ Pra + (j : Int)) i) → ¬ L.xlText (paZ Pra) →
    (∀ j : Nat, j < 8 → priv L (paZ Ps0 + (j : Int)) i) → ¬ L.xlText (paZ Ps0) →
    (∀ j : Nat, j < 8 → priv L (paZ Ps1 + (j : Int)) i) → ¬ L.xlText (paZ Ps1) →
    -- the return address (Q20': the ra reload's graph value; deviation 1)
    (k + 9 < (AxOpsem.grow (gtAdGd GT) i).length →
      graphValue (gtAdGd GT) (i, k + 9) = some (stBytes 8 ret)) → jalrTgt 0#12 ret = ret →
    -- the row-end hook (stage 2, design §B / Q-S2-2), over the window [k + 9, k + 11]
    (∀ k' : Nat, k + 9 ≤ k' → k' ≤ k + 11 → (AxOpsem.grow (gtAdGd GT) i).length ≤ k' →
      ∀ pr : Pexv6,
        ⊢ @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
          ⟨pr, k'⟩ Ψ) →
    ⊢ ((∀ (vra vs0 vs1 : List (BitVec 8)) (rs' : RegFile) (ib' : Ibch),
        ⌜ctrlOkSW T satp0 rs' ∧ rs' .PC = ret ∧ rs' .tlb = rs .tlb ∧
          gprVal rs' AxSpinE8.r10 = hres (gprVal rs AxSpinHd8.r9) (gprVal rs AxSpinE8.r10) ∧
          gprVal rs' AxSpinE8.r2 = hsp1 + sign_extend (m := 64) (caddi16spImm 2#6) ∧
          vra.length = 8 ∧ vs0.length = 8 ∧ vs1.length = 8 ∧
          gprVal rs' AxSpinE8.r1 = ldRes false 8 vra ∧ gprVal rs' AxSpinE8.r8 = ldRes false 8 vs0 ∧
          gprVal rs' AxSpinHd8.r9 = ldRes false 8 vs1 ∧
          (∀ r : BitVec 5, r.toNat ≠ 1 → r.toNat ≠ 2 → r.toNat ≠ 8 → r.toNat ≠ 9 →
            r.toNat ≠ 10 → gprVal rs' r = gprVal rs r) ∧
          graphValue (gtAdGd GT) (i, k + 9) = some vra ∧
          graphValue (gtAdGd GT) (i, k + 10) = some vs0 ∧
          graphValue (gtAdGd GT) (i, k + 11) = some vs1⌝ -∗
        AxAnnot.annotOwn (GF := GF) (i, k + 9)
          iprop(⌜RLfact GT i (paZ Pra) (k + 9) (stBytes 8 ra0)⌝) -∗
        AxAnnot.annotOwn (GF := GF) (i, k + 10)
          iprop(⌜RLfact GT i (paZ Ps0) (k + 10) (stBytes 8 s00)⌝) -∗
        AxAnnot.annotOwn (GF := GF) (i, k + 11)
          iprop(⌜RLfact GT i (paZ Ps1) (k + 11) (stBytes 8 s10)⌝) -∗
        @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
          ⟨.PHart cpu (.pure ()) rs' none ib', k + 12⟩ Ψ) ∧
      (∀ (vra vs0 vs1 : List (BitVec 8)) (pr : Pexv6),
        ⌜(AxOpsem.grow (gtAdGd GT) i).length = k + 12 ∧
          vra.length = 8 ∧ vs0.length = 8 ∧ vs1.length = 8 ∧
          graphValue (gtAdGd GT) (i, k + 9) = some vra ∧
          graphValue (gtAdGd GT) (i, k + 10) = some vs0 ∧
          graphValue (gtAdGd GT) (i, k + 11) = some vs1⌝ -∗
        AxAnnot.annotOwn (GF := GF) (i, k + 9)
          iprop(⌜RLfact GT i (paZ Pra) (k + 9) (stBytes 8 ra0)⌝) -∗
        AxAnnot.annotOwn (GF := GF) (i, k + 10)
          iprop(⌜RLfact GT i (paZ Ps0) (k + 10) (stBytes 8 s00)⌝) -∗
        AxAnnot.annotOwn (GF := GF) (i, k + 11)
          iprop(⌜RLfact GT i (paZ Ps1) (k + 11) (stBytes 8 s10)⌝) -∗
        @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
          ⟨pr, k + 12⟩ Ψ)) -∗
      @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
        ⟨.PHart cpu (.pure ()) rs none ib, k + 9⟩ Ψ := by
  intro HR Hnr_ra Hnr_s0 Hnr_s1 HD Hd1 Hd2 Hd3 Hc0 HPC0 Hhit0 Hsp0 HdaL_ra Hh_ra HdaL_s0 Hh_s0
    HdaL_s1 Hh_s1 Hpr_ra Hnt_ra Hpr_s0 Hnt_s0 Hpr_s1 Hnt_s1 Hval Hret HΨend
  iintro C
  iapply (AxSpinHd8.holdEpiGr L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu Hfix Htxh Ψ HΨmid
    k rs ib ret plk pcl Pra Ps0 Ps1 Pram Ps0m hsp1 ra0 s00 s10 HR Hnr_ra Hnr_s0 Hnr_s1 HD Hd1 Hd2
    Hd3 Hc0 HPC0 Hhit0 Hsp0 HdaL_ra Hh_ra HdaL_s0 Hh_s0 HdaL_s1 Hh_s1 Hpr_ra Hnt_ra Hpr_s0 Hnt_s0
    Hpr_s1 Hnt_s1 (AxSpinT2i.gateOfPinG Hval) Hret HΨend)
  isplit
  · icases C with ⟨C, -⟩
    iintro %-
    iexact C
  · icases C with ⟨-, C⟩
    iexact C


include HL Hcons hmode hasid hppn Hfix Htxh HΨmid in
/-- Rocq `hold_epi` (deviation 1: Stage C positions; `Hval`/`Hret` replace the return-fetch pin
`Hinj`/`Hstv`/`va_first_read`).  Stage 2: the full-row corollary of `holdEpiP` (hook and end
continuation vacuous: `k + 12 < LEN`). -/
theorem holdEpi (k : Nat) (rs : RegFile) (ib : Ibch) (ret : BitVec 64) (plk pcl : Int)
    (Pra Ps0 Ps1 Pram Ps0m : BitVec 64) (hsp1 ra0 s00 s10 : BitVec 64) :
    -- the row
    RowHolding k (AxOpsem.grow (gtAdGd GT) i) true plk pcl (paZ Pra) (paZ Ps0) (paZ Ps1)
      (paZ Pram) (paZ Ps0m) →
    noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Pra) →
    noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Ps0) →
    noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Ps1) →
    slotsDisj [paZ Pra, paZ Ps0, paZ Ps1, paZ Pram, paZ Ps0m] →
    graphData (gtAdGd GT) (i, k + 1) = some (stBytes 8 ra0) →
    graphData (gtAdGd GT) (i, k + 2) = some (stBytes 8 s00) →
    graphData (gtAdGd GT) (i, k + 3) = some (stBytes 8 s10) →
    -- the boundary state
    ctrlOkSW T satp0 rs → rs .PC = pch 0x1a → hitW rs (pch 0) → gprVal rs AxSpinE8.r2 = hsp1 →
    -- the three stack slots
    dataAtS σi T (.Load .Data) (hsp1 + sign_extend (m := 64) AxSpinHd8.imm24) 8 Pra →
    hitW rs (hsp1 + sign_extend (m := 64) AxSpinHd8.imm24) →
    dataAtS σi T (.Load .Data) (hsp1 + sign_extend (m := 64) AxSpinHd8.imm16) 8 Ps0 →
    hitW rs (hsp1 + sign_extend (m := 64) AxSpinHd8.imm16) →
    dataAtS σi T (.Load .Data) (hsp1 + sign_extend (m := 64) AxSpinHd8.imm8) 8 Ps1 →
    hitW rs (hsp1 + sign_extend (m := 64) AxSpinHd8.imm8) →
    (∀ j : Nat, j < 8 → priv L (paZ Pra + (j : Int)) i) → ¬ L.xlText (paZ Pra) →
    (∀ j : Nat, j < 8 → priv L (paZ Ps0 + (j : Int)) i) → ¬ L.xlText (paZ Ps0) →
    (∀ j : Nat, j < 8 → priv L (paZ Ps1 + (j : Int)) i) → ¬ L.xlText (paZ Ps1) →
    -- the return address (Q20': the ra reload's graph value; deviation 1)
    graphValue (gtAdGd GT) (i, k + 9) = some (stBytes 8 ret) → jalrTgt 0#12 ret = ret →
    ⊢ (∀ (vra vs0 vs1 : List (BitVec 8)) (rs' : RegFile) (ib' : Ibch),
        ⌜ctrlOkSW T satp0 rs' ∧ rs' .PC = ret ∧ rs' .tlb = rs .tlb ∧
          gprVal rs' AxSpinE8.r10 = hres (gprVal rs AxSpinHd8.r9) (gprVal rs AxSpinE8.r10) ∧
          gprVal rs' AxSpinE8.r2 = hsp1 + sign_extend (m := 64) (caddi16spImm 2#6) ∧
          vra.length = 8 ∧ vs0.length = 8 ∧ vs1.length = 8 ∧
          gprVal rs' AxSpinE8.r1 = ldRes false 8 vra ∧ gprVal rs' AxSpinE8.r8 = ldRes false 8 vs0 ∧
          gprVal rs' AxSpinHd8.r9 = ldRes false 8 vs1 ∧
          (∀ r : BitVec 5, r.toNat ≠ 1 → r.toNat ≠ 2 → r.toNat ≠ 8 → r.toNat ≠ 9 →
            r.toNat ≠ 10 → gprVal rs' r = gprVal rs r) ∧
          graphValue (gtAdGd GT) (i, k + 9) = some vra ∧
          graphValue (gtAdGd GT) (i, k + 10) = some vs0 ∧
          graphValue (gtAdGd GT) (i, k + 11) = some vs1⌝ -∗
        AxAnnot.annotOwn (GF := GF) (i, k + 9)
          iprop(⌜RLfact GT i (paZ Pra) (k + 9) (stBytes 8 ra0)⌝) -∗
        AxAnnot.annotOwn (GF := GF) (i, k + 10)
          iprop(⌜RLfact GT i (paZ Ps0) (k + 10) (stBytes 8 s00)⌝) -∗
        AxAnnot.annotOwn (GF := GF) (i, k + 11)
          iprop(⌜RLfact GT i (paZ Ps1) (k + 11) (stBytes 8 s10)⌝) -∗
        @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
          ⟨.PHart cpu (.pure ()) rs' none ib', k + 12⟩ Ψ) -∗
      @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
        ⟨.PHart cpu (.pure ()) rs none ib, k + 9⟩ Ψ := by
  intro HR Hnr_ra Hnr_s0 Hnr_s1 HD Hd1 Hd2 Hd3 Hc0 HPC0 Hhit0 Hsp0 HdaL_ra Hh_ra HdaL_s0 Hh_s0
    HdaL_s1 Hh_s1 Hpr_ra Hnt_ra Hpr_s0 Hnt_s0 Hpr_s1 Hnt_s1 Hval Hret
  have Hlen : k + 12 < (AxOpsem.grow (gtAdGd GT) i).length := HR.2.1
  iintro C
  iapply (holdEpiP L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu Hfix Htxh Ψ HΨmid
    k rs ib ret plk pcl Pra Ps0 Ps1 Pram Ps0m hsp1 ra0 s00 s10
    (AxSpinHd8.rowHoldingPOfFull _ _ _ _ _ _ _ _ _ _ HR) Hnr_ra Hnr_s0 Hnr_s1 HD Hd1 Hd2 Hd3
    Hc0 HPC0 Hhit0 Hsp0 HdaL_ra Hh_ra HdaL_s0 Hh_s0 HdaL_s1 Hh_s1 Hpr_ra Hnt_ra Hpr_s0 Hnt_s0
    Hpr_s1 Hnt_s1 (fun _ => Hval) Hret (fun _ _ _ h3 => absurd h3 (by omega)))
  isplit
  · iexact C
  · iintro %vra %vs0 %vs1 %pr %Hp
    exact absurd Hp.1 (by omega)
end epi

end Weak
