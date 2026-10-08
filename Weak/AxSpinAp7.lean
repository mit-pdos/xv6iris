/-
Weak: **the inlined allocpid's CRITICAL-SECTION BODY: the row shape `RowAllocpidBody` and the
32-bit arithmetic of `nextpid = nextpid + 1`** (the copy that this tree's kernel INLINES into
`allocproc`, `allocproc + 0x44 .. + 0x94`).

Rocq: `iris/AxSpinAp7.v` @ xxvzwolszwmp (owner ruling Q18: RETARGETED to the inlined code; the
code and the Rocq ↦ inlined mapping are in `Weak/AxSpinAp.lean`'s header, "Design"; the plan is
`PROGRESS-Q18.md`, "AxSpinAp7").

§1 THE ARITHMETIC (`npBytes`): the bytes `sw a1,1936(a5)` (+0x86) stores, where
   `a1 = addiw a3,1` (+0x68) and `a3 = lw 1998(a3)` (+0x48) reads the four bytes `vs`, are the
   little-endian bytes of `wordOfBytes 4 vs + 1` (mod 2³²) — the word `fxuNpIncr` needs
   (`w8 + one32`).  Pure (`bv_decide` after generalising the read word).
§2 `RowAllocpidBody k row pnp ppid` = `RowSh k row (apBodySh pnp ppid)` (AxSpinPOr's shape
   language) ∧ the reads are plain: the 67 row items the body occupies from position `k` on the
   NORMAL path (pid ≠ 1000, no collision; Ap9 pins it by premises):
     k              THE nextpid READ (`lw`, +0x48): `RL pnp 4`, aq = false;
     k + 1 + j      the scan read of `proc[j].pid` (`c.lw a4,48(a5)`, +0x74, round j < 64):
                    `RL (AxSpinAp7.scanAddr j) 4`, aq = false;
     k + 65         THE nextpid WRITE (`sw`, +0x86): `RS pnp 4` (plain store, data existential);
     k + 66         the `p->pid` WRITE (`c.sw a3,48(s1)`, +0x8a): `RS ppid 4` (`ppid = p + 48`).
   The data VALUES are existential.

## Deviations from Rocq

1. KERNEL INLINING (`AxSpinAp` deviation 1, Q18) + O2 STAGE C (fetches are not row items).
   Mapping:

   | Rocq (allocpid, +0x16 .. +0x2a)                  | Lean (inlined, `allocproc +` 0x44 .. 0x94)   |
   |--------------------------------------------------|----------------------------------------------|
   | `addiw1` = `addiw a4,s1,1` (+0x20)               | `AxSpinAp7.addiw1` = `addiw a1,a3,1` (+0x68); same function of the read value |
   | `np_bytes` (`c.sw a4,0(a5)`, +0x24)              | `npBytes` (`sw a1,1936(a5)`, +0x86)          |
   | `ap_body_sh pnp` (9 items: 7 fetches `RF`, `RL pnp 4` at 3, `RS pnp 4` at 6) | `apBodySh pnp ppid` (67 items, no `RF`: `RL pnp 4` at 0, 64 scan `RL`s at 1..64, `RS pnp 4` at 65, `RS ppid 4` at 66) |
   | `Row_allocpid_body k row pnp` (+ plain-read bit at `k + 3`) | `RowAllocpidBody k row pnp ppid` (+ plain-read bits at `k` and at each `k + 1 + j`) |
   | `b_len : k + 9 ≤ length row`                     | `bLen : k + 67 ≤ row.length`                 |
   | `b_rd` at `k + 3`                                | `bRd` at `k`                                 |
   | `b_wr` at `k + 6`                                | `AxSpinAp7.bWr` at `k + 65`                  |
   | (none: `p->pid` was stored by the caller)        | NEW `AxSpinAp7.bWpid` at `k + 66`            |
   | (none: no scan)                                  | NEW `AxSpinAp7.bScan j` at `k + 1 + j`       |
   | `bf_nw` (fetch positions are not writes), `b_f2` (the 2-byte fetch is not a 4-byte read) | DROPPED: no fetch items under Stage C |

   On the normal path the 1000-wrap (`beq a3,a6` at +0x64 taken ⇒ `a1 = 1`) and the collision
   retry (`beq a4,a3` at +0x76 taken) are not executed; `addiw1` is the not-wrapped value.
2. `RowAllocpidBody` takes the slot address `ppid` (= `p + 48`, the caller's `proc` slot) for the
   `p->pid` store; the scan addresses are fixed (`AxSpinAp7.scanAddr j = proc + 376 j + 48`,
   Lean-only, from `MachCSL.KernelSyms.«proc»`; NPROC = 64, `sizeof(struct proc)` = 376, `pid`
   at offset 48 — the `addi a5,a5,376` / `c.lw a4,48(a5)` of the scan).
3. `trunc32` (RiscvExtras) is spelled `BitVec.setWidth 32` in `st4Trunc` (= `AxLeafS4.trunc32`,
   not imported here); `rrv4` is `rfl` (Lean `rrv` is `wordOfBytes`, no cast); `sign_extend' 64
   (mword_of_int 1 : mword 12)` ↦ `sign_extend (m := 64) (1#12)`; `subrange_vec_dec x 31 0` ↦
   `Sail.BitVec.extractLsb x 31 0` (the model's `execute_ADDIW`); `bv_add w one32` ↦ `w + one32`
   with the sum stated at `BitVec 32` (explicit `@HAdd.hAdd (BitVec 32) …`, so `npBytes`'s right
   side is syntactically `fxuNpIncr`'s `wbytes 4 (w8 + one32)` at `w8 := wordOfBytes 4 vs`); `word_of_bytes` ↦ `wordOfBytes`, `st_bytes`/`ld_res` ↦
   `stBytes`/`ldRes`, `l !! j` ↦ `l[j]?`, `WeakAxiomatic.LStore` ↦ `Lbl.LStore`.
4. Rocq section `rowfacts` (`Context k row pnp HR`) ↦ explicit arguments `k row pnp ppid HR`.

**Rocq → Lean name map.**  `rrv4` `rrv4`, `st4_trunc` `st4Trunc`, `trunc32_one12`
`trunc32One12`, `addiw1` `AxSpinAp7.addiw1` (duplicated name: AxSpinAp7, AxSpinPO3), `np_bytes`
`npBytes`, `ap_body_sh` `apBodySh`, `Row_allocpid_body` `RowAllocpidBody`, `b_len` `bLen`, `b_rd`
`bRd`, `b_wr` `AxSpinAp7.bWr` (duplicated name: AxSpinAp7, AxSpinX5).  Lean-only
(file-qualified): `AxSpinAp7.scanAddr`, `AxSpinAp7.bWpid`, `AxSpinAp7.bScan`,
`AxSpinAp7.apBodyShScan`, `AxSpinAp7.apBodyShLen`.

**Dropped:** `bf_nw`, `b_f2` (deviation 1: they are about fetch items, which Stage C removes;
their Rocq consumer AxSpinAp9 is restated without fetch steps).  **Not ported:** the
`Print Assumptions` line (the lint's axiom check covers it).
-/
import Weak.AxSpinPOr
import Weak.AxSpinX4
import Weak.AxDataX2

namespace Weak

open MachCSL
open Sail
open LeanRV64D LeanRV64D.Functions

/-! # 1. The arithmetic -/

theorem rrv4 (vs : List (BitVec 8)) : rrv 4 vs = wordOfBytes 4 vs := rfl

theorem st4Trunc (x : BitVec 64) :
    stBytes 4 x = WeakInterpProj.wbytes 4 (BitVec.setWidth 32 x) := by
  unfold stBytes AxDataX.wrb AxDataX.stData
  congr 1

theorem trunc32One12 : BitVec.setWidth 32 (sign_extend (m := 64) (1#12)) = one32 := by
  decide

/-- Rocq `addiw1`: the value `addiw a1,a3,1` (+0x68) computes from `a3` (the `lw`'s result). -/
def AxSpinAp7.addiw1 (v : BitVec 64) : BitVec 64 :=
  sign_extend (m := 64) (Sail.BitVec.extractLsb (v + sign_extend (m := 64) (1#12)) 31 0)

theorem npBytes (vs : List (BitVec 8)) :
    stBytes 4 (AxSpinAp7.addiw1 (ldRes false 4 vs)) =
      WeakInterpProj.wbytes 4
        (@HAdd.hAdd (BitVec 32) (BitVec 32) (BitVec 32) _ (wordOfBytes 4 vs) one32) := by
  unfold stBytes AxDataX.wrb ldRes rrv
  congr 1
  generalize (wordOfBytes 4 vs : BitVec 32) = w
  show BitVec.setWidth 32 (Sail.BitVec.extractLsb (AxSpinAp7.addiw1
    (extend_value false w)) 31 0) = w + one32
  unfold AxSpinAp7.addiw1 extend_value sign_extend Sail.BitVec.signExtend Sail.BitVec.extractLsb one32
  simp only [Bool.false_eq_true, ↓reduceIte]
  bv_decide

/-! # 2. The row shape -/

/-- (Lean-only) The address of `proc[j].pid` (`proc + 376 j + 48`), the `j`-th scan read. -/
def AxSpinAp7.scanAddr (j : Nat) : Int := (KernelSyms.«proc» : Int) + 376 * (j : Int) + 48

/-- Rocq `ap_body_sh` (deviation 1): the body's 67 memory items from the nextpid read —
`[RL pnp 4] ++ (List.range 64).map (RL (scanAddr j) 4) ++ [RS pnp 4, RS ppid 4]`. -/
def apBodySh (pnp ppid : Int) : List Ritem :=
  .RL pnp 4 :: ((List.range 64).map (fun j => .RL (AxSpinAp7.scanAddr j) 4) ++
    [.RS pnp 4, .RS ppid 4])

/-- `RowSh` plus the reads' identity bits (plain, non-acquire loads — what `lw`/`c.lw` emit). -/
def RowAllocpidBody (k : Nat) (row : List Lbl) (pnp ppid : Int) : Prop :=
  RowSh k row (apBodySh pnp ppid) ∧
  (∀ lb, row[k]? = some lb → aident lb = .IRead false pnp 4) ∧
  (∀ j, j < 64 → ∀ lb, row[k + 1 + j]? = some lb →
    aident lb = .IRead false (AxSpinAp7.scanAddr j) 4)

theorem AxSpinAp7.apBodyShLen (pnp ppid : Int) : (apBodySh pnp ppid).length = 67 := by
  simp [apBodySh]

/-- (Lean-only) The scan items of the shape. -/
theorem AxSpinAp7.apBodyShScan (pnp ppid : Int) (j : Nat) (hj : j < 64) :
    (apBodySh pnp ppid)[1 + j]? = some (.RL (AxSpinAp7.scanAddr j) 4) := by
  unfold apBodySh
  rw [show 1 + j = j + 1 by omega, List.getElem?_cons_succ,
    List.getElem?_append_left (by simp; omega), List.getElem?_map, List.getElem?_range hj]
  rfl

theorem bLen (k : Nat) (row : List Lbl) (pnp ppid : Int) (HR : RowAllocpidBody k row pnp ppid) :
    k + 67 ≤ row.length := by
  have H := rowShLen k row _ HR.1 (by simp [apBodySh])
  rw [AxSpinAp7.apBodyShLen] at H
  exact H

theorem bRd (k : Nat) (row : List Lbl) (pnp ppid : Int) (HR : RowAllocpidBody k row pnp ppid) :
    ∃ lb, row[k]? = some lb ∧ aident lb = .IRead false pnp 4 := by
  obtain ⟨lb, Hlb, _⟩ := rowShAt k row _ 0 _ HR.1 rfl
  exact ⟨lb, Hlb, HR.2.1 lb Hlb⟩

theorem AxSpinAp7.bWr (k : Nat) (row : List Lbl) (pnp ppid : Int)
    (HR : RowAllocpidBody k row pnp ppid) :
    ∃ vw cls, row[k + 65]? = some (.LStore false pnp vw cls) ∧ vw.length = 4 :=
  shStore k row _ 65 pnp 4 HR.1 rfl

/-- (Lean-only) The `p->pid` store at `k + 66`. -/
theorem AxSpinAp7.bWpid (k : Nat) (row : List Lbl) (pnp ppid : Int)
    (HR : RowAllocpidBody k row pnp ppid) :
    ∃ vw cls, row[k + 66]? = some (.LStore false ppid vw cls) ∧ vw.length = 4 :=
  shStore k row _ 66 ppid 4 HR.1 rfl

/-- (Lean-only) The `j`-th scan read at `k + 1 + j`. -/
theorem AxSpinAp7.bScan (k : Nat) (row : List Lbl) (pnp ppid : Int)
    (HR : RowAllocpidBody k row pnp ppid) (j : Nat) (hj : j < 64) :
    ∃ lb, row[k + 1 + j]? = some lb ∧ aident lb = .IRead false (AxSpinAp7.scanAddr j) 4 := by
  obtain ⟨lb, Hlb, _⟩ := rowShAt k row _ (1 + j) _ HR.1 (AxSpinAp7.apBodyShScan pnp ppid j hj)
  rw [← Nat.add_assoc] at Hlb
  exact ⟨lb, Hlb, HR.2.2 j hj lb Hlb⟩

end Weak
