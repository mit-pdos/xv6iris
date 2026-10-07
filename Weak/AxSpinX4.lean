/-
Weak: **Phase 1c, part 4 of the spinlock plan -- the CERTIFICATES' concrete layout `Lx`** (with
`xlayOk Lx` proved), the hand programs at REAL WIDTHS and their rows and runs.

Rocq: `iris/AxSpinX4.v` @ xxvzwolszwmp.

LAYOUT `Lx`: pid_lock word at 0x80002000 (4 bytes), lk->cpu at 0x80002010 (8 bytes), nextpid at
0x80002020 (4 bytes); hart B (=1) owns a stack word at 0x80003000 (8 bytes) and a struct-cpu
field (noff) at 0x80005000 (4 bytes); the read-only class is the text/PT word at 0x80000000
(8 bytes); harts `[A; B] = [0; 1]`; empty fetch region.  lk->cpu values: the REAL
`cvx i` = bytes of `cpuAddr (cpuOf i)`.

PROGRAMS (hand `Pexv6` nodes, `AxSpinX3`):
  B `AxSpinX4.bM0` (14 memory events): sd stack ← X; ld stack; sw noff ← 1; lw noff;
    ld text/PT word; ld lk->cpu (racy, non-holder); amoswap.w.aq lk ← 1; sd lk->cpu ← cpuAddr B;
    lw nextpid; sw nextpid ← v + 1; ld lk->cpu (holder); sd lk->cpu ← 0; fence rw,w;
    sw lk ← 0 (WCrel).
  A `AxSpinX4.aM0`: amoswap.w.aq; sd lk->cpu ← cpuAddr A; lw nextpid; sw nextpid ← v+1;
    sd lk->cpu ← 0; fence rw,w; sw lk ← 0.
  A' `AxSpinX4.rM0` (the Φ_cpu / lk->cpu race): sd lk->cpu ← cpuAddr A WITHOUT the lock.

## Deviations from Rocq

1. VOCABULARY (as `AxSpinX` deviation 1): `Z` ↦ `Int`, `bv n` ↦ `BitVec n`, `z_pa` ↦ `zPa`,
   `pa_z` ↦ `paZ`, `cl_range` ↦ `clRange`, `list_to_set` ↦ `LawfulSet.ofList`, `NoDup` ↦
   `List.Nodup`, `l !! j` ↦ `l[j]?`, `B0` ↦ `b0`, `Z_to_bv` ↦ `BitVec.ofInt`, `bv_add` ↦ `+`,
   `cpus_ptr` ↦ `MachCSL.cpuAddr` (`AxSpinX` deviation 2), `init_regstate` ↦ `zeroRegs`,
   `M unit` ↦ `SailM Unit`, `decide (i = hB)` ↦ `if i = hB`, `bool_decide (w = zero32)` ↦
   `if w = zero32`; `a < b < c` ↦ `a ≤ b ∧ b < c`.
2. lean-sail shapes (as `AxSpinX3` deviation 3): widths are `Nat`; `Interface.Next (MemRead n r) k`
   ↦ `.impure (.ok (.memRead n 64 r)) k`, writes/barriers likewise; read answers
   `.Ok (w, _)` / `.Err _` (Rocq `inl (w, _)` / `inr _`); `amoK` takes the lean-sail result type
   `Result (BitVec (8 * 4) × Option Bool) Arch.abort`.  The hand-program defs are `abbrev`s (so
   the run lemmas unify through them).
3. CONTEXTS: the runs' section `axirisG Σ` is unused and dropped; `cpu` is an explicit leading
   argument (as `AxSpinX3` deviation 4).  `AThread p k` ↦ `⟨p, k⟩`.
4. PROOFS: the concrete `devAddr` / `paZ` facts by `decide +kernel` (Rocq `vm_compute`);
   `xlayOk Lx`'s two `Nodup` conjuncts by `decide +kernel`.

**Rocq → Lean name map.**  `lkpa` `lkpa`, `lcpa` `lcpa`, `nppa` `nppa`, `skpa` `skpa`, `nfpa`
`nfpa`, `ropa` `ropa`, `lkpa_ram` … `ropa_ram` `lkpaRam` … `ropaRam`, `lkZ_v` … `roZ_v` `lkZV` …
`roZV`, `in_clr` `inClr`, `cl_range_lookup` `AxSpinX4.clRangeLookup` (dup: AxSpinH4),
`cl_range_lookup_2` `clRangeLookup2`, `NoDup_cl_range` `NoDupClRange`, `stkB` `stkB`, `nfB` `nfB`,
`Lx` `Lx`, `priv_Lx` `privLx`, `lwb_Lx` `lwbLx`, `clb_Lx` `clbLx`, `npb_Lx` `npbLx`, `XO_Lx`
`XOLx`, `clb_lcpa` `clbLcpa`, `Lx_ok` `LxOk`, `Xv` `Xv`, `zero32` `zero32`, `one32` `one32`,
`zero64` `zero64`, `cpA` `cpA`, `cpB` `cpB`, `cvx_A` `cvxA`, `cvx_B` `cvxB`, `zero64_bytes`
`zero64Bytes`, `ldk` `ldk`, `ld0` `ld0`, `stv` `stv`, `fnc` `fnc`, `amo_w` `amoW`, `amo_k`
`amoK`, `acq4` `AxSpinX4.acq4` (dup), `b_end` … `b_ls` `bEnd` … `bLs`, `b_m0`
`AxSpinX4.bM0` (dup), `a_end` … `a_cs` `aEnd` … `aCs`, `a_m0` `AxSpinX4.aM0` (dup), `r_m0`
`AxSpinX4.rM0` (dup), `z4` `AxSpinX4.z4` (dup), `o4` `AxSpinX4.o4` (dup), `b_row`
`AxSpinX4.bRow`, `a_row` `AxSpinX4.aRow`, `r_row` `AxSpinX4.rRow`, `acq_after_claim`
`acqAfterClaim`, `amo_claim_next` `amoClaimNext`, `b_run` `AxSpinX4.bRun`, `a_run`
`AxSpinX4.aRun`, `r_run` `AxSpinX4.rRun` (all dup with AxSpinProt3).
Lean-only (file-qualified): `AxSpinX4.ldkK` (`ldk`'s answer continuation, named),
`AxSpinX4.ldkRun` (one `ldk` read step at the graph value: Rocq's
inline `nrun_read` + `cbn; rewrite word_of_bytes_wbytes`).

**Dropped:** none (Rocq 78 decls; Lean 80 = 78 + 2 Lean-only).
-/
import Weak.AxSpinX
import Weak.AxSpinX3

namespace Weak

open Iris Iris.BI Iris.Std MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D

/-! # 1. Addresses and the layout -/

def lkpa : PAddr := zPa 0x80002000
def lcpa : PAddr := zPa 0x80002010
def nppa : PAddr := zPa 0x80002020
def skpa : PAddr := zPa 0x80003000
def nfpa : PAddr := zPa 0x80005000
def ropa : PAddr := zPa 0x80000000

theorem lkpaRam : devAddr lkpa = false := by decide +kernel
theorem lcpaRam : devAddr lcpa = false := by decide +kernel
theorem nppaRam : devAddr nppa = false := by decide +kernel
theorem skpaRam : devAddr skpa = false := by decide +kernel
theorem nfpaRam : devAddr nfpa = false := by decide +kernel
theorem ropaRam : devAddr ropa = false := by decide +kernel

theorem lkZV : paZ lkpa = 0x80002000 := by decide +kernel
theorem lcZV : paZ lcpa = 0x80002010 := by decide +kernel
theorem npZV : paZ nppa = 0x80002020 := by decide +kernel
theorem skZV : paZ skpa = 0x80003000 := by decide +kernel
theorem nfZV : paZ nfpa = 0x80005000 := by decide +kernel
theorem roZV : paZ ropa = 0x80000000 := by decide +kernel

theorem inClr (a b : Int) (n : Nat) : a ∈ clRange b n ↔ b ≤ a ∧ a < b + (n : Int) := by
  unfold clRange
  rw [List.mem_map]
  constructor
  · rintro ⟨j, Hj, rfl⟩
    have := List.mem_range.1 Hj
    omega
  · intro Ha
    refine ⟨(a - b).toNat, List.mem_range.2 (by omega), by omega⟩

theorem AxSpinX4.clRangeLookup (b : Int) (n j : Nat) (a : Int) :
    (clRange b n)[j]? = some a → a = b + (j : Int) ∧ j < n := by
  unfold clRange
  rw [List.getElem?_map]
  by_cases hj : j < n
  · rw [List.getElem?_range hj]
    intro h
    simp only [Option.map_some, Option.some.injEq] at h
    exact ⟨h.symm, hj⟩
  · rw [List.getElem?_eq_none (by simp; omega)]
    intro h
    simp at h

theorem clRangeLookup2 (b : Int) (n j : Nat) :
    j < n → (clRange b n)[j]? = some (b + (j : Int)) := by
  intro hj
  unfold clRange
  rw [List.getElem?_map, List.getElem?_range hj]
  rfl

theorem NoDupClRange (b : Int) (n : Nat) : (clRange b n).Nodup := by
  unfold clRange
  exact List.Pairwise.map (R := (· ≠ ·)) _ (fun x y h e => h (by omega)) List.nodup_range

def stkB : GSet Int := LawfulSet.ofList (clRange (paZ skpa) 8)
def nfB : GSet Int := LawfulSet.ofList (clRange (paZ nfpa) 4)

def Lx : Xlay where
  xlLk := paZ lkpa
  xlNp := paZ nppa
  xlHarts := [hA, hB]
  xlStk := fun i => if i = hB then stkB else ∅
  xlCpuf := fun i => if i = hB then nfB else ∅
  xlRo := fun a => a ∈ clRange (paZ ropa) 8
  xlText := Tf

theorem privLx (a : Int) (j : Agent) :
    priv Lx a j ↔ j = hB ∧ (a ∈ clRange (paZ skpa) 8 ∨ a ∈ clRange (paZ nfpa) 4) := by
  unfold priv
  simp only [Lx]
  constructor
  · rintro ⟨-, Hs⟩
    by_cases hj : j = hB
    · subst hj
      simp only [if_true, stkB, nfB] at Hs
      exact ⟨rfl, Hs.imp LawfulSet.mem_ofList.2 LawfulSet.mem_ofList.2⟩
    · simp only [if_neg hj] at Hs
      rcases Hs with Hs | Hs <;> exact (notElemOfEmpty Hs).elim
  · rintro ⟨rfl, Hs⟩
    refine ⟨by simp, ?_⟩
    simp only [if_true, stkB, nfB]
    exact Hs.imp LawfulSet.mem_ofList.1 LawfulSet.mem_ofList.1

theorem lwbLx (a : Int) : a ∈ lwb Lx ↔ paZ lkpa ≤ a ∧ a < paZ lkpa + 4 := by
  unfold lwb
  rw [inClr]
  rfl

theorem clbLx (a : Int) : a ∈ clb Lx ↔ paZ lkpa + 16 ≤ a ∧ a < paZ lkpa + 24 := by
  unfold clb
  rw [inClr]
  simp only [Lx]
  omega

theorem npbLx (a : Int) : a ∈ npb Lx ↔ paZ nppa ≤ a ∧ a < paZ nppa + 4 := by
  unfold npb
  rw [inClr]
  rfl

theorem XOLx (a : Int) :
    a ∈ XO Lx ↔ ((paZ lkpa + 16 ≤ a ∧ a < paZ lkpa + 24) ∨ (paZ nppa ≤ a ∧ a < paZ nppa + 4)) := by
  unfold XO
  rw [elemOfUnion, ← LawfulSet.mem_ofList, ← LawfulSet.mem_ofList, clbLx, npbLx]

theorem clbLcpa : clb Lx = clRange (paZ lcpa) 8 := by
  unfold clb
  simp only [Lx]
  rw [lkZV, lcZV]
  rfl

theorem LxOk : xlayOk Lx := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold lwb clb npb
    simp only [Lx]
    decide +kernel
  · intro a j Hp
    obtain ⟨-, Hs⟩ := (privLx a j).1 Hp
    rw [inClr, inClr, skZV, nfZV] at Hs
    rw [lwbLx, XOLx, lkZV, npZV]
    omega
  · intro a j1 j2 H1 H2
    rw [((privLx a j1).1 H1).1, ((privLx a j2).1 H2).1]
  · intro a j Hro Hw
    have Hro' : a ∈ clRange (paZ ropa) 8 := Hro
    rw [inClr, roZV] at Hro'
    rcases Hw with Hw | Hw | Hw
    · rw [lwbLx, lkZV] at Hw
      omega
    · rw [XOLx, lkZV, npZV] at Hw
      omega
    · obtain ⟨-, Hs⟩ := (privLx a j).1 Hw
      rw [inClr, inClr, skZV, nfZV] at Hs
      omega
  · decide
  · intro i Hi
    simp only [Lx, List.mem_cons, List.not_mem_nil, or_false] at Hi
    unfold NCPU
    rcases Hi with rfl | rfl <;> decide

/-! # 2. Values -/

def Xv : BitVec 64 := BitVec.ofInt 64 0x1122334455667788
def zero32 : BitVec 32 := BitVec.ofInt 32 0
def one32 : BitVec 32 := BitVec.ofInt 32 1
def zero64 : BitVec 64 := BitVec.ofInt 64 0
def cpA : BitVec 64 := cpuAddr (cpuOf hA)
def cpB : BitVec 64 := cpuAddr (cpuOf hB)

theorem cvxA : cvx hA = WeakInterpProj.wbytes 8 cpA := rfl
theorem cvxB : cvx hB = WeakInterpProj.wbytes 8 cpB := rfl
theorem zero64Bytes : WeakInterpProj.wbytes 8 zero64 = List.replicate 8 b0 := by decide +kernel

/-! # 3. Hand programs -/

/-- Lean-only: `ldk`'s answer continuation (named so the run lemma can pass it). -/
abbrev AxSpinX4.ldkK (n : Nat) (k : BitVec (8 * n) → SailM Unit)
    (res : Result (BitVec (8 * n) × Option Bool) Arch.abort) : SailM Unit :=
  match res with
  | .Ok (w, _) => k w
  | .Err _ => hlt
abbrev ldk (n : Nat) (pa : PAddr) (k : BitVec (8 * n) → SailM Unit) : SailM Unit :=
  .impure (.ok (.memRead n 64 (rreqn n l3pAkP pa))) (AxSpinX4.ldkK n k)
abbrev ld0 (n : Nat) (pa : PAddr) (k : SailM Unit) : SailM Unit := ldk n pa (fun _ => k)
abbrev stv (n : Nat) (pa : PAddr) (v : BitVec (8 * n)) (k : SailM Unit) : SailM Unit :=
  .impure (.ok (.memWrite n 64 (wreqn n l3pAkP pa v))) (fun _ => k)
abbrev fnc (k : SailM Unit) : SailM Unit :=
  .impure (.ok (.barrier .Barrier_RISCV_rw_w)) (fun _ => k)
abbrev amoW (kok kf : SailM Unit) (w : BitVec 32) : SailM Unit :=
  .impure (.ok (.memWrite 4 64 (wreqn 4 l3pAkXpl lkpa one32)))
    (fun _ => if w = zero32 then kok else kf)
abbrev amoK (kok kf : SailM Unit) (res : Result (BitVec (8 * 4) × Option Bool) Arch.abort) :
    SailM Unit :=
  match res with
  | .Ok (w, _) => amoW kok kf w
  | .Err _ => hlt
abbrev AxSpinX4.acq4 (kok kf : SailM Unit) : SailM Unit :=
  .impure (.ok (.memRead 4 64 (rreqn 4 l3pAkXaq lkpa))) (amoK kok kf)

/-! hart B -/
abbrev bEnd : SailM Unit := stv 4 lkpa zero32 hlt
abbrev bRel : SailM Unit := stv 8 lcpa zero64 (fnc bEnd)
abbrev bHold : SailM Unit := ld0 8 lcpa bRel
abbrev bInc (v : BitVec 32) : SailM Unit := stv 4 nppa (v + one32) bHold
abbrev bNp : SailM Unit := ldk 4 nppa bInc
abbrev bCs : SailM Unit := stv 8 lcpa cpB bNp
abbrev bAcq : SailM Unit := AxSpinX4.acq4 bCs hlt
abbrev bRc : SailM Unit := ld0 8 lcpa bAcq
abbrev bRo : SailM Unit := ld0 8 ropa bRc
abbrev bLn : SailM Unit := ld0 4 nfpa bRo
abbrev bSn : SailM Unit := stv 4 nfpa one32 bLn
abbrev bLs : SailM Unit := ld0 8 skpa bSn
abbrev AxSpinX4.bM0 : SailM Unit := stv 8 skpa Xv bLs

/-! hart A (positive) -/
abbrev aEnd : SailM Unit := stv 4 lkpa zero32 hlt
abbrev aRel : SailM Unit := stv 8 lcpa zero64 (fnc aEnd)
abbrev aInc (v : BitVec 32) : SailM Unit := stv 4 nppa (v + one32) aRel
abbrev aNp : SailM Unit := ldk 4 nppa aInc
abbrev aCs : SailM Unit := stv 8 lcpa cpA aNp
abbrev AxSpinX4.aM0 : SailM Unit := AxSpinX4.acq4 aCs hlt

/-! hart A' (the race: lk->cpu written WITHOUT the lock) -/
abbrev AxSpinX4.rM0 : SailM Unit := stv 8 lcpa cpA hlt

/-! # 4. Rows -/

def AxSpinX4.z4 : List (BitVec 8) := WeakInterpProj.wbytes 4 zero32
def AxSpinX4.o4 : List (BitVec 8) := WeakInterpProj.wbytes 4 one32

def AxSpinX4.bRow (t1 t3 t4 t5 : List Nat) (t6 : Nat) (t8 t10 : List Nat)
    (v1 v4 v5 v10 : BitVec 64) (v3 v8 : BitVec 32) : List Lbl :=
  [.LStore false (paZ skpa) (WeakInterpProj.wbytes 8 Xv) .WCplain,
   .LLoad false (paZ skpa) t1 (WeakInterpProj.wbytes 8 v1),
   .LStore false (paZ nfpa) (WeakInterpProj.wbytes 4 one32) .WCplain,
   .LLoad false (paZ nfpa) t3 (WeakInterpProj.wbytes 4 v3),
   .LLoad false (paZ ropa) t4 (WeakInterpProj.wbytes 8 v4),
   .LLoad false (paZ lcpa) t5 (WeakInterpProj.wbytes 8 v5),
   .LRmw true false (paZ lkpa) [t6, t6, t6, t6] AxSpinX4.z4 AxSpinX4.o4 .WCplain,
   .LStore false (paZ lcpa) (WeakInterpProj.wbytes 8 cpB) .WCplain,
   .LLoad false (paZ nppa) t8 (WeakInterpProj.wbytes 4 v8),
   .LStore false (paZ nppa) (WeakInterpProj.wbytes 4 (v8 + one32)) .WCplain,
   .LLoad false (paZ lcpa) t10 (WeakInterpProj.wbytes 8 v10),
   .LStore false (paZ lcpa) (WeakInterpProj.wbytes 8 zero64) .WCplain,
   .LFence true true false true,
   .LStore false (paZ lkpa) AxSpinX4.z4 .WCrel]

def AxSpinX4.aRow (t0 : Nat) (t2 : List Nat) (v2 : BitVec 32) : List Lbl :=
  [.LRmw true false (paZ lkpa) [t0, t0, t0, t0] AxSpinX4.z4 AxSpinX4.o4 .WCplain,
   .LStore false (paZ lcpa) (WeakInterpProj.wbytes 8 cpA) .WCplain,
   .LLoad false (paZ nppa) t2 (WeakInterpProj.wbytes 4 v2),
   .LStore false (paZ nppa) (WeakInterpProj.wbytes 4 (v2 + one32)) .WCplain,
   .LStore false (paZ lcpa) (WeakInterpProj.wbytes 8 zero64) .WCplain,
   .LFence true true false true,
   .LStore false (paZ lkpa) AxSpinX4.z4 .WCrel]

def AxSpinX4.rRow : List Lbl := [.LStore false (paZ lcpa) (WeakInterpProj.wbytes 8 cpA) .WCplain]

/-! # 5. Runs over an ABSTRACT graph, row pinned -/

theorem acqAfterClaim (kok kf : SailM Unit) :
    amoK kok kf (.Ok (wordOfBytes 4 AxSpinX4.z4, none)) = amoW kok kf zero32 := by
  unfold AxSpinX4.z4
  rw [wordOfBytesWbytes]

theorem amoClaimNext (kok kf : SailM Unit) :
    (if zero32 = zero32 then kok else kf) = kok := if_pos rfl

section runsx
variable (cpu : CPU)

/-- Lean-only: one `ldk` read step at the graph value (Rocq: `nrun_read` followed by
`cbn beta iota; rewrite word_of_bytes_wbytes`). -/
theorem AxSpinX4.ldkRun (GD : Gdexec) (i : Agent) (n : Nat) (pa : PAddr)
    (Hdev : devAddr pa = false) (ts : List Nat) (v : BitVec (8 * n))
    (k : BitVec (8 * n) → SailM Unit) (rs : RegFile) (kk : Nat) :
    (AxOpsem.grow GD i)[kk]? = some (.LLoad false (paZ pa) ts (WeakInterpProj.wbytes n v)) →
    astepAnyNfGv GD i ⟨hp cpu (ldk n pa k) rs, kk⟩ ⟨hp cpu (k v) rs, kk + 1⟩ := by
  intro Hl
  have H := nrunRead cpu GD i n pa Hdev ts (WeakInterpProj.wbytes n v)
    (AxSpinX4.ldkK n k) rs kk Hl (wbytesLength n v)
  rw [wordOfBytesWbytes] at H
  exact H

theorem AxSpinX4.bRun (GD : Gdexec) (t1 t3 t4 t5 : List Nat) (t6 : Nat) (t8 t10 : List Nat)
    (v1 v4 v5 v10 : BitVec 64) (v3 v8 : BitVec 32)
    (Hrow : AxOpsem.grow GD hB = AxSpinX4.bRow t1 t3 t4 t5 t6 t8 t10 v1 v4 v5 v10 v3 v8) :
    nsteps (astepAnyNfGv GD hB) 15 ⟨hp cpu AxSpinX4.bM0 zeroRegs, 0⟩ ⟨hp cpu hlt zeroRegs, 14⟩ := by
  refine nsteps_l (nrunWrite cpu GD hB 8 (by decide) skpa skpaRam Xv bLs zeroRegs 0 .WCplain
    (by rw [Hrow]; rfl)) ?_
  refine nsteps_l (AxSpinX4.ldkRun cpu GD hB 8 skpa skpaRam t1 v1 (fun _ => bSn) zeroRegs 1
    (by rw [Hrow]; rfl)) ?_
  refine nsteps_l (nrunWrite cpu GD hB 4 (by decide) nfpa nfpaRam one32 bLn zeroRegs 2 .WCplain
    (by rw [Hrow]; rfl)) ?_
  refine nsteps_l (AxSpinX4.ldkRun cpu GD hB 4 nfpa nfpaRam t3 v3 (fun _ => bRo) zeroRegs 3
    (by rw [Hrow]; rfl)) ?_
  refine nsteps_l (AxSpinX4.ldkRun cpu GD hB 8 ropa ropaRam t4 v4 (fun _ => bRc) zeroRegs 4
    (by rw [Hrow]; rfl)) ?_
  refine nsteps_l (AxSpinX4.ldkRun cpu GD hB 8 lcpa lcpaRam t5 v5 (fun _ => bAcq) zeroRegs 5
    (by rw [Hrow]; rfl)) ?_
  have H6 := nrunRmwRead cpu GD hB 6 4 lkpa lkpaRam [t6, t6, t6, t6] AxSpinX4.z4 AxSpinX4.o4
    .WCplain (amoK bCs hlt) zeroRegs (by rw [Hrow]; rfl) (by decide +kernel) (by decide +kernel)
  rw [acqAfterClaim] at H6
  refine nsteps_l H6 ?_
  have H6' := nrunRmwWrite cpu GD hB 6 4 (by decide) lkpa lkpaRam [t6, t6, t6, t6] AxSpinX4.z4
    one32 .WCplain (if zero32 = zero32 then bCs else hlt) zeroRegs (by rw [Hrow]; rfl)
  rw [amoClaimNext] at H6'
  refine nsteps_l H6' ?_
  refine nsteps_l (nrunWrite cpu GD hB 8 (by decide) lcpa lcpaRam cpB bNp zeroRegs 7 .WCplain
    (by rw [Hrow]; rfl)) ?_
  refine nsteps_l (AxSpinX4.ldkRun cpu GD hB 4 nppa nppaRam t8 v8 bInc zeroRegs 8
    (by rw [Hrow]; rfl)) ?_
  refine nsteps_l (nrunWrite cpu GD hB 4 (by decide) nppa nppaRam (v8 + one32) bHold zeroRegs 9
    .WCplain (by rw [Hrow]; rfl)) ?_
  refine nsteps_l (AxSpinX4.ldkRun cpu GD hB 8 lcpa lcpaRam t10 v10 (fun _ => bRel) zeroRegs 10
    (by rw [Hrow]; rfl)) ?_
  refine nsteps_l (nrunWrite cpu GD hB 8 (by decide) lcpa lcpaRam zero64 (fnc bEnd) zeroRegs 11
    .WCplain (by rw [Hrow]; rfl)) ?_
  refine nsteps_l (runFence cpu GD hB 12 bEnd zeroRegs (by rw [Hrow]; rfl)) ?_
  refine nsteps_l (nrunWrite cpu GD hB 4 (by decide) lkpa lkpaRam zero32 hlt zeroRegs 13 .WCrel
    (by rw [Hrow]; rfl)) ?_
  exact nsteps_O _

theorem AxSpinX4.aRun (GD : Gdexec) (t0 : Nat) (t2 : List Nat) (v2 : BitVec 32)
    (Hrow : AxOpsem.grow GD hA = AxSpinX4.aRow t0 t2 v2) :
    nsteps (astepAnyNfGv GD hA) 8 ⟨hp cpu AxSpinX4.aM0 zeroRegs, 0⟩ ⟨hp cpu hlt zeroRegs, 7⟩ := by
  have H0 := nrunRmwRead cpu GD hA 0 4 lkpa lkpaRam [t0, t0, t0, t0] AxSpinX4.z4 AxSpinX4.o4
    .WCplain (amoK aCs hlt) zeroRegs (by rw [Hrow]; rfl) (by decide +kernel) (by decide +kernel)
  rw [acqAfterClaim] at H0
  refine nsteps_l H0 ?_
  have H0' := nrunRmwWrite cpu GD hA 0 4 (by decide) lkpa lkpaRam [t0, t0, t0, t0] AxSpinX4.z4
    one32 .WCplain (if zero32 = zero32 then aCs else hlt) zeroRegs (by rw [Hrow]; rfl)
  rw [amoClaimNext] at H0'
  refine nsteps_l H0' ?_
  refine nsteps_l (nrunWrite cpu GD hA 8 (by decide) lcpa lcpaRam cpA aNp zeroRegs 1 .WCplain
    (by rw [Hrow]; rfl)) ?_
  refine nsteps_l (AxSpinX4.ldkRun cpu GD hA 4 nppa nppaRam t2 v2 aInc zeroRegs 2
    (by rw [Hrow]; rfl)) ?_
  refine nsteps_l (nrunWrite cpu GD hA 4 (by decide) nppa nppaRam (v2 + one32) aRel zeroRegs 3
    .WCplain (by rw [Hrow]; rfl)) ?_
  refine nsteps_l (nrunWrite cpu GD hA 8 (by decide) lcpa lcpaRam zero64 (fnc aEnd) zeroRegs 4
    .WCplain (by rw [Hrow]; rfl)) ?_
  refine nsteps_l (runFence cpu GD hA 5 aEnd zeroRegs (by rw [Hrow]; rfl)) ?_
  refine nsteps_l (nrunWrite cpu GD hA 4 (by decide) lkpa lkpaRam zero32 hlt zeroRegs 6 .WCrel
    (by rw [Hrow]; rfl)) ?_
  exact nsteps_O _

theorem AxSpinX4.rRun (GD : Gdexec) (Hrow : AxOpsem.grow GD hA = AxSpinX4.rRow) :
    nsteps (astepAnyNfGv GD hA) 1 ⟨hp cpu AxSpinX4.rM0 zeroRegs, 0⟩ ⟨hp cpu hlt zeroRegs, 1⟩ := by
  refine nsteps_l (nrunWrite cpu GD hA 8 (by decide) lcpa lcpaRam cpA hlt zeroRegs 0 .WCplain
    (by rw [Hrow]; rfl)) ?_
  exact nsteps_O _

end runsx

end Weak
