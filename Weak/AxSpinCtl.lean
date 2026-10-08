/-
Weak: spinlock plan, Phase 3 (control leaves) — the D3 CHECK and the VACUITY / OBSTRUCTION facts
that decide what the control leaves can and cannot discharge on SURFACE v4 (AxRelease).  Pure
lemmas (graph generator, ASTs, the exact-register map); the leaves are in AxSpinCtl2.

Rocq: `iris/AxSpinCtl.v` @ xxvzwolszwmp.

WHAT THIS FILE PROVES.
§1 D3 CHECK.  The spike generator's (`Weak.AxSpinSpike`, Stage C) dependency edges into the
   lock stores on hart 0's pid-allocation path (0 failed spins), named by instruction pc, by
   `decide +kernel`: `d3LockcpuAddrSrc` (DTaddr into the 8-byte stores to lk+16 =
   `[(release+0x12, holding+0x26), (acquire+0x28, push_off+0x26)]`), `d3LockwordAddrSrc`
   (`[(release+0x1a, holding+0x26)]`), `d3AmoAddrSrc` (`[(acquire+0x1c, push_off+0x26)]`),
   `d3Spills` (no DTdata into stores to hsp − 88) — all FOUR as in Rocq — and
   `d3RelSpillDataSrc` (the DTdata source of release+0x06's `c.sdsp s1` spill; deviation 2).
§2 the exact map cannot carry s1 / ra across a reload: `holdRetS1NotExact`,
   `holdRetCannotJustifyS1`, `retRaNotExact`, `exRelS110`, `relEntryS1NeedsExact`.
§3 `rf0` is false for release's c.beqz (`notRf0Cbeqz`, via `rf0ExecSome` and the odd-pc state
   `badT`, `execCbeqzFails`), hence `instr4Rli10False`: `instr4 … (release+0x10) true cbeqz10
   ⊢ False` at every instance.

KERNEL CROSS-CHECK (Xv6/KernelImage.lean; holding = 0x80000bf2, release = 0x80000ce0):
holding+0x26/+0x28/+0x2a = 0x64a2 `c.ldsp s1,8(sp)` / 0x6105 `c.addi16sp sp,32` / 0x8082
`c.ret`; release+0x10 = 0xcd11 `c.beqz a0,+28`; release+0x22..+0x2a = 0x60e2/0x6442/0x64a2
`c.ldsp ra/s0/s1`, 0x6105, 0x8082 — NO DRIFT in the words this file uses (pinned by the Lean-only
`AxSpinCtl.epiWords`, `decide +kernel` against `Xv6.Kernel.textTree`).  The address drift
(Rocq build → this tree) is in the symbols only (`KernelSyms`, see AxSpinSpike's header).

## Deviations from Rocq

1. SPELLING: `mword n` ↦ `BitVec n`, `mword_of_int` ↦ `BitVec.ofInt`, `add_vec_int pc 2` ↦
   `pc + 2#64` (= `pc + instrLen true`, `exOk`'s successor), `zero_extend' 12 (concat_vec u
   'b"000")` ↦ `zero_extend (m := 12) (u +++ 0b000#3)`, `caddi16sp_imm` ↦ `caddi16spImm`,
   `RiscvExec.exec` ↦ `Weak.exec`, `Ex_rel` ↦ AxRelease5's `exRel`, `AxEpiProbe.t_at` ↦ `tAt`,
   `wr_opt` ↦ AxSymCtl2's `wrOpt`, `zero_reg` ↦ `0#64`; `vm_compute` ↦ `decide +kernel`
   (`execCbeqzFails` through the boolean `AxSpinCtl.execCbeqzFailsB`, `Option` of a state has no
   `DecidableEq`).  `rf0` is AxSymEngine2's Lean `rf0` (pin-register and sfence-announce
   conditions; `rf0ExecSome`'s statement is unchanged).
2. KERNEL / Stage C DRIFT in §1.  (a) The Lean `AxSpinSpike.gen` lists the ADMINISTRATIVE fetch
   events in its event list without giving them graph positions (Stage C), so an edge's
   position no longer indexes `gen`'s list: the Lean-only `AxSpinCtl.genG` drops the fetch
   events (class 1) and `depSrcs` / `depPcs` / `d3Hart0` index that list (positions = indices,
   167 events for hart 0).  `spans` counts graph positions as before.  (b) This build has no
   `allocpid` (inlined into `allocproc`, AxSpinSpike header): release is entered with
   `allocproc`'s s1 (= p) as acquire+0x2e `c.ldsp s1` restored it, so `d3RelSpillDataSrc` is
   `[(rel 0x06, acq 0x2e)]` (Rocq `[(rel 0x06, apid 0x1e)]`, allocpid's `lw s1,0(a5)` of
   nextpid).  The Rocq header's "release is entered with s1 = the LOADED pid" therefore does NOT
   hold here (s1 is a restored spill of an exact register); `relEntryS1NeedsExact` (a fact about
   `exRel`) is unchanged.  `apid o` is kept (= the inlined copy's start + o; no statement uses it).
3. Rocq `Print Assumptions` lines dropped (no Lean analogue; the lint bans axioms).

**Rocq → Lean name map.**  `ak_eqb` `akEqb`, `ev_is` `evIs`, `dep_srcs` `depSrcs`, `d3_tr`
`d3Tr`, `d3_hart0` `d3Hart0`, `d3_lk` `d3Lk`, `d3_sp` `d3Sp`, `dep_pcs` `depPcs`, `d3_*_src` /
`d3_spills` `d3LockcpuAddrSrc` `d3LockwordAddrSrc` `d3AmoAddrSrc` `d3Spills` `d3RelSpillDataSrc`,
`ldsp_ins` `ldspIns`, `addi16_ins` `addi16Ins`, `r5_9_2` `r592`, `r5_1_2` `r512`, `sp_r5` `spR5`,
`ex_ok_ldsp` `exOkLdsp`, `ex_ok_addi16` `exOkAddi16`, `hold_at` `holdAt`, `rel_at` `relAt`,
`hold_26_28` … `rel_28_2a` `hold2628` `hold282a` `rel2224` `rel2426` `rel2628` `rel282a`,
`hold_ret_s1_not_exact` `holdRetS1NotExact`, `Ex_rel_s1_10` `exRelS110`,
`hold_ret_cannot_justify_s1` `holdRetCannotJustifyS1`, `ret_ra_not_exact` `retRaNotExact`,
`rel_entry_s1_needs_exact` `relEntryS1NeedsExact`, `rf0_exec_some` `rf0ExecSome`, `cbeqz10`
`cbeqz10`, `bad_t` `badT`, `exec_cbeqz_fails` `execCbeqzFails`, `not_rf0_cbeqz` `notRf0Cbeqz`,
`instr4_rli10_false` `instr4Rli10False`.  FILE-QUALIFIED (duplicated Rocq names): `pc_of`
`AxSpinCtl.pcOf`, `rel` `AxSpinCtl.rel`, `hold` `AxSpinCtl.hold`, `acq` `AxSpinCtl.acq`, `w64`
`AxSpinCtl.w64`, `r5` `AxSpinCtl.r5`; also (generic short names) `spans` `AxSpinCtl.spans`,
`push` `AxSpinCtl.push`, `apid` `AxSpinCtl.apid`.  Lean-only: `AxSpinCtl.genG`,
`AxSpinCtl.epiWords`, `AxSpinCtl.execCbeqzFailsB`.

**Dropped:** nothing.  Rocq 23 definitions + 25 lemmas; Lean 23 definitions + 25 theorems
(+ 3 Lean-only).
-/
import Weak.AxSpinSpike
import Weak.AxRelease5
import Weak.AxEpiProbe
import Weak.AxSymCtl2

namespace Weak

open MachCSL
open Dtag
open AxSpinSpike (Akind Aev Ti Gst)

def akEqb (a b : AxSpinSpike.Akind) : Bool :=
  match a, b with
  | .KR, .KR | .KW, .KW | .KRmw, .KRmw | .KF, .KF => true
  | _, _ => false

def evIs (k : AxSpinSpike.Akind) (a : Int) (n : Nat) (cls : Nat) (e : AxSpinSpike.Aev) : Bool :=
  akEqb e.aeK k && decide (e.aeA = a) && Nat.beq e.aeN n && Nat.beq e.aeCls cls

def AxSpinCtl.genG (tr : List AxSpinSpike.Ti) :
    List AxSpinSpike.Aev × List ((Nat × Nat) × Dtag) :=
  let G := AxSpinSpike.gen tr
  (G.1.filter fun e => !Nat.beq e.aeCls 1, G.2)

def depSrcs (tg : Dtag) (tgt : AxSpinSpike.Aev → Bool)
    (G : List AxSpinSpike.Aev × List ((Nat × Nat) × Dtag)) : List AxSpinSpike.Aev :=
  G.2.filterMap fun d =>
    match d with
    | ((j, k), t) =>
      if t = tg then
        match G.1[k]? with
        | some e => if tgt e then G.1[j]? else none
        | none => none
      else none

def d3Tr : List AxSpinSpike.Ti := AxSpinSpike.hartTr 0 0
def d3Hart0 : List AxSpinSpike.Aev × List ((Nat × Nat) × Dtag) := AxSpinCtl.genG d3Tr
def d3Lk : Int := AxSpinSpike.sPidLock
def d3Sp : Int := AxSpinSpike.hsp 0

def AxSpinCtl.spans (tr : List AxSpinSpike.Ti) : List (Nat × Nat × Int) :=
  (tr.foldl (fun (acc : AxSpinSpike.Gst × List (Nat × Nat × Int)) t =>
      let s' := AxSpinSpike.step acc.1 t
      (s', (acc.1.gPos, s'.gPos, t.tPc) :: acc.2))
    (AxSpinSpike.g0, [])).2

def AxSpinCtl.pcOf : List (Nat × Nat × Int) → Nat → Int
  | [], _ => 0
  | (lo, hi, pc) :: r, j => if Nat.ble lo j && Nat.blt j hi then pc else AxSpinCtl.pcOf r j

def depPcs (tg : Dtag) (tgt : AxSpinSpike.Aev → Bool) (tr : List AxSpinSpike.Ti) :
    List (Int × Int) :=
  let G := AxSpinCtl.genG tr
  let sp := AxSpinCtl.spans tr
  G.2.filterMap fun d =>
    match d with
    | ((j, k), t) =>
      if t = tg then
        match G.1[k]? with
        | some e => if tgt e then some (AxSpinCtl.pcOf sp k, AxSpinCtl.pcOf sp j) else none
        | none => none
      else none

def AxSpinCtl.rel (o : Int) : Int := AxSpinSpike.sRelease + o
def AxSpinCtl.hold (o : Int) : Int := AxSpinSpike.sHolding + o
def AxSpinCtl.acq (o : Int) : Int := AxSpinSpike.sAcquire + o
def AxSpinCtl.push (o : Int) : Int := AxSpinSpike.sPushOff + o
def AxSpinCtl.apid (o : Int) : Int := AxSpinSpike.sAllocpid + o

/-! ### The edges (kernel evaluation of the spike generator) -/

/-- the 8-byte stores to lk->cpu (lk + 16) on the path, with their ADDRESS sources:
release+0x12 `sd zero,16(s1)` ← holding+0x26 `c.ldsp s1`; acquire+0x28 `sd a0,16(s1)` ←
push_off+0x26 `c.ldsp s1`. -/
theorem d3LockcpuAddrSrc :
    depPcs DTaddr (evIs .KW (d3Lk + 16) 8 0) d3Tr =
      [(AxSpinCtl.rel 0x12, AxSpinCtl.hold 0x26), (AxSpinCtl.acq 0x28, AxSpinCtl.push 0x26)] := by
  decide +kernel

/-- the lock-word store release+0x1a `sw zero,0(s1)` ← holding+0x26 -/
theorem d3LockwordAddrSrc :
    depPcs DTaddr (evIs .KW d3Lk 4 0) d3Tr = [(AxSpinCtl.rel 0x1a, AxSpinCtl.hold 0x26)] := by
  decide +kernel

/-- acquire's `amoswap.w.aq` (acquire+0x1c) ← push_off+0x26 as well -/
theorem d3AmoAddrSrc :
    depPcs DTaddr (evIs .KRmw d3Lk 4 0) d3Tr = [(AxSpinCtl.acq 0x1c, AxSpinCtl.push 0x26)] := by
  decide +kernel

/-- no store to holding's / push_off's slot 8(sp) (hsp − 88) has a DATA source -/
theorem d3Spills :
    depPcs DTdata (evIs .KW (d3Sp - 88) 8 0) d3Tr = [] := by
  decide +kernel

/-- release+0x06 `c.sdsp s1,8(sp)` stores `allocproc`'s s1 as acquire+0x2e `c.ldsp s1` restored
it (deviation 2: Rocq `[(rel 0x06, apid 0x1e)]`, allocpid's `lw s1`) -/
theorem d3RelSpillDataSrc :
    depPcs DTdata (evIs .KW (d3Sp - 56) 8 0) d3Tr = [(AxSpinCtl.rel 0x06, AxSpinCtl.acq 0x2e)] := by
  decide +kernel

/-! ## 2. The exact map cannot carry s1 / ra across a reload -/

open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D LeanRV64D.Functions

def AxSpinCtl.w64 (z : Int) : BitVec 64 := BitVec.ofInt 64 z
def AxSpinCtl.r5 (z : Int) : BitVec 5 := BitVec.ofInt 5 z

/-- the epilogue words (`c.ldsp rd, 8u(sp)`; `c.addi16sp sp, 32`) -/
def ldspIns (u : Int) (rd : Int) : instruction :=
  .LOAD (zero_extend (m := 12) (BitVec.ofInt 6 u +++ 0b000#3), sp, .Regidx (AxSpinCtl.r5 rd),
    false, 8)
def addi16Ins : instruction :=
  .ITYPE (caddi16spImm (BitVec.ofInt 6 2), sp, sp, .ADDI)

theorem r592 : AxSpinCtl.r5 9 ≠ AxSpinCtl.r5 2 := by decide
theorem r512 : AxSpinCtl.r5 1 ≠ AxSpinCtl.r5 2 := by decide

theorem spR5 : (sp : regidx) = .Regidx (AxSpinCtl.r5 2) := rfl

/-- one c.ldsp step: a register exact at the successor that is NOT the loaded one was exact
before; the loaded one is never exact after -/
theorem exOkLdsp (Ex : BitVec 64 → BitVec 5 → Prop) (pc : BitVec 64) (u rd : Int)
    (r : BitVec 5) :
    exOk Ex pc true (ldspIns u rd) → Ex (pc + 2#64) r → Ex pc r ∧ r ≠ AxSpinCtl.r5 rd :=
  fun H Hr => H r Hr

theorem exOkAddi16 (Ex : BitVec 64 → BitVec 5 → Prop) (pc : BitVec 64) (r : BitVec 5) :
    exOk Ex pc true addi16Ins → Ex (pc + 2#64) r → r ≠ AxSpinCtl.r5 2 → Ex pc r := by
  intro H Hr Hne
  rcases H r Hr with ⟨h, _⟩ | ⟨E, _⟩
  · exact h
  · exact absurd E Hne

def holdAt (o : Int) : BitVec 64 := AxSpinCtl.w64 ((KernelSyms.«holding» : Int) + o)
def relAt (o : Int) : BitVec 64 := AxSpinCtl.w64 ((KernelSyms.«release» : Int) + o)

theorem hold2628 : holdAt 0x26 + 2#64 = holdAt 0x28 := by decide +kernel
theorem hold282a : holdAt 0x28 + 2#64 = holdAt 0x2a := by decide +kernel
theorem rel2224 : relAt 0x22 + 2#64 = relAt 0x24 := by decide +kernel
theorem rel2426 : relAt 0x24 + 2#64 = relAt 0x26 := by decide +kernel
theorem rel2628 : relAt 0x26 + 2#64 = relAt 0x28 := by decide +kernel
theorem rel282a : relAt 0x28 + 2#64 = relAt 0x2a := by decide +kernel

/-- (Lean-only) the kernel cross-check: this tree's image holds, at the epilogue offsets and
release+0x10, exactly the words the ASTs above / `cbeqz10` below are: holding+0x26/28/2a
`0x64a2 0x6105 0x8082`, release+0x10 `0xcd11`, release+0x22..0x2a
`0x60e2 0x6442 0x64a2 0x6105 0x8082`. -/
theorem AxSpinCtl.epiWords :
    ([(holdAt 0x26, 0x64a2), (holdAt 0x28, 0x6105), (holdAt 0x2a, 0x8082),
      (relAt 0x10, 0xcd11), (relAt 0x22, 0x60e2), (relAt 0x24, 0x6442), (relAt 0x26, 0x64a2),
      (relAt 0x28, 0x6105), (relAt 0x2a, 0x8082)] : List (BitVec 64 × Nat)).all
      (fun p => match Xv6.Kernel.textTree.find? p.1.toNat with
        | some k => Nat.beq k.width 2 && Nat.beq k.enc p.2
        | none => false) = true := by
  decide +kernel

/-- holding's epilogue: s1 (x9) is NOT exact at holding's c.ret, for ANY exact map
satisfying `instr4`'s `exOk` at holding+0x26 / +0x28 -/
theorem holdRetS1NotExact (Ex : BitVec 64 → BitVec 5 → Prop) :
    exOk Ex (holdAt 0x26) true (ldspIns 1 9) →
    exOk Ex (holdAt 0x28) true addi16Ins →
    ¬ Ex (holdAt 0x2a) (AxSpinCtl.r5 9) := by
  intro H26 H28 Hs1
  rw [← hold282a] at Hs1
  have H1 := exOkAddi16 Ex _ _ H28 Hs1 r592
  rw [← hold2628] at H1
  exact (exOkLdsp Ex _ 1 9 _ H26 H1).2 rfl

/-- `exRel` (the map `release_wpd4` runs on) has s1 exact at release+0x10 -/
theorem exRelS110 : exRel (relAt 0x10) (AxSpinCtl.r5 9) := by
  unfold exRel relOff relAt AxSpinCtl.w64 AxSpinCtl.r5 Xv6.releaseAddr
  decide +kernel

/-- hence NO exact-form return (target's exact set ⊆ the c.ret's) from holding+0x2a can
establish release+0x10's s1 -/
theorem holdRetCannotJustifyS1 (Ex : BitVec 64 → BitVec 5 → Prop) :
    exOk Ex (holdAt 0x26) true (ldspIns 1 9) →
    exOk Ex (holdAt 0x28) true addi16Ins →
    Ex (relAt 0x10) (AxSpinCtl.r5 9) →
    ¬ (∀ r, Ex (relAt 0x10) r → Ex (holdAt 0x2a) r) :=
  fun H26 H28 Hs Hsub => holdRetS1NotExact Ex H26 H28 (Hsub _ Hs)

/-- release's epilogue: ra (x1) is NOT exact at release's c.ret (+0x2a) -/
theorem retRaNotExact (Ex : BitVec 64 → BitVec 5 → Prop) :
    exOk Ex (relAt 0x22) true (ldspIns 3 1) →
    exOk Ex (relAt 0x24) true (ldspIns 2 8) →
    exOk Ex (relAt 0x26) true (ldspIns 1 9) →
    exOk Ex (relAt 0x28) true addi16Ins →
    ¬ Ex (relAt 0x2a) (AxSpinCtl.r5 1) := by
  intro H22 H24 H26 H28 Hra
  rw [← rel282a] at Hra
  have H1 := exOkAddi16 Ex _ _ H28 Hra r512
  rw [← rel2628] at H1
  have H2 := (exOkLdsp Ex _ 1 9 _ H26 H1).1
  rw [← rel2426] at H2
  have H3 := (exOkLdsp Ex _ 2 8 _ H24 H2).1
  rw [← rel2224] at H3
  exact (exOkLdsp Ex _ 3 1 _ H22 H3).2 rfl

/-- `exRel` needs s1 exact at release+0x06 (the c.sdsp s1 spill's data, `exBase`) — the caller
must justify it -/
theorem relEntryS1NeedsExact : exRel (relAt 0x06) (AxSpinCtl.r5 9) := by
  unfold exRel relOff relAt AxSpinCtl.w64 AxSpinCtl.r5 Xv6.releaseAddr
  decide +kernel

/-! ## 3. `rf0` is false for a branch ⇒ `instr4` at a compressed branch is ⌜False⌝ -/

theorem rf0ExecSome {X : Type} (m : SailM X) : rf0 m → ∀ s, exec m s ≠ none := by
  induction m with
  | pure y => intro _ s h; exact Option.some_ne_none (y, s) h
  | impure call k ih =>
    intro hrf s
    cases call with
    | error e => exact hrf.elim
    | ok o =>
      cases o
      case regRead r => exact ih _ (hrf.2 _) _
      case regWrite r v => exact ih _ hrf.2 _
      case instrAnnounce n w => exact ih _ hrf.2 _
      case branchAnnounce n a => exact ih _ hrf _
      case cacheOp c => exact ih _ hrf _
      case tlbi c => exact ih _ hrf _
      case takeException c => exact ih _ hrf _
      case returnException c => exact ih _ hrf _
      case translationStart c => exact ih _ hrf _
      case translationEnd c => exact ih _ hrf _
      case cycleCount => exact ih _ hrf _
      case message c => exact ih _ hrf _
      case getCycleCount => exact ih _ hrf _
      all_goals exact hrf.elim

/-- release+0x10's AST (`c.beqz a0,+28`; AxRelease5's `p10`) -/
def cbeqz10 : instruction :=
  .BTYPE (sign_extend (m := 13) (14#8 +++ 0b0#1), zreg, creg2reg_idx (.Cregidx 2#3), .BEQ)

/-- a state with an ODD pc and a0 = 0: the branch is taken to an odd target and `jump_to`'s
alignment assert fails -/
def badT : ExecSt := wrOpt (some (AxSpinCtl.r5 10, 0#64)) (tAt 0x80000001)

theorem AxSpinCtl.execCbeqzFailsB : (exec (execute cbeqz10) badT).isNone = true := by
  decide +kernel

theorem execCbeqzFails : exec (execute cbeqz10) badT = none :=
  Option.isNone_iff_eq_none.1 AxSpinCtl.execCbeqzFailsB

theorem notRf0Cbeqz : ¬ rf0 (execute cbeqz10) :=
  fun H => rf0ExecSome _ H badT execCbeqzFails

open Iris Iris.BI Iris.ProofMode in
/-- `instr4` at release+0x10 (the `rli_10` premise of `release_wpd4`) is ⌜False⌝ — at EVERY
instance (σi, T, satp0, Armed, Ex) -/
theorem instr4Rli10False {GF : BundledGFunctors} (σi : ExecSt) (T : PTree) (satp0 : BitVec 64)
    (Armed : BitVec 64 → Prop) (Ex : BitVec 64 → BitVec 5 → Prop) :
    instr4 (GF := GF) σi T satp0 Armed Ex (relAt 0x10) true cbeqz10 ⊢ (iprop(False) : IProp GF) := by
  unfold instr4
  iintro %H
  rcases H with ⟨⟨Hf, _⟩ | ⟨_, _, Hd | Hrf, _⟩, _⟩
  · cases Hf
  · exact False.elim Hd
  · exact (notRf0Cbeqz Hrf).elim

end Weak
