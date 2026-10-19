/-
Weak: **allocproc route P — [R46.2] = [OWN.124] (a): THE THIRD EXEMPT PC, `holding+0x12`**
(`notes/weak-allocproc-plan-review-R46.md` §4, §7 [R46.2]; PROGRESS-P.md §HEADHOP2 F-HH2-1, §HH2A).
Lean-only, no Rocq twin.  A PRIMED TWIN: nothing registered imports this file.

**REVISIT [OWN.124]** — the owner accepted option (a) and asked that it be FLAGGED TO LOOK AT AGAIN; the
alternative kept on file is (b), a custody-aware `waitedOn` (R46 §4: a write counts as waited-on only on
a BUSY byte — a pending entry, an AMO head, or another row's head load reading it — plus a NEW per-load
MachCSL footprint record "a load's footprint avoids other harts' live frames"; 1.1–2.2k).

**Spec, stated first.**  RVWMO orders a plain load before a po-later store only by rules 4 (fence),
9–11 (addr/data/ctrl into the write) and 13; `holding+0x12`'s `ld a5,16(a0)` (`lk->cpu`) reaches
`mycpu`'s frame stores (`sd ra,8(sp)`, `sd s0,0(sp)`) by no dependency, so GF may put them gmo-before
it, and the walk's measure cannot descend through a BLOCKED `holding+0x12` head (F-HH2-1).  The
exemption replays the read UNGATED (`SbOrd.enbL`'s `X` arm, P-W2's `rdXArm`): the member reads the top
of `[L+16, L+24)`, GF reads its source; both differ from the row's own `&cpus[x]`, so `holding`
returns 0 on both sides — the read is value-insensitive exactly like `ip->ref`'s ([OWN.112]).
FAITHFUL (proof device: same rf/co elsewhere; RVWMO says nothing about values).

  §1  **the exemption predicate** `holdCpuX` (the emission block of the event realizes at `holding+0x12`
      AND the block starts with `ra = acquire+0x16`, the return point of acquire's `jal holding` — the
      `release`/`sched` calls are NOT exempt: there the reader is the holder and both values ARE its own
      pointer, never blocked); `exemptX` = `ipRefX ∨ holdCpuX`, the walk's `X`;
  §2  static facts (`decide +kernel`): the taint walk re-hosted (`SilSite.holding12Ok`: from
      `holding+0x12`, the loaded word reaches only `seqz a0` at `holding+0x1e`, where the value kill
      fires; `holding12NeedsKill`), the path's shape (`mv s1,a5; jal mycpu; sub a0,s1,a0; seqz a0,a0`),
      `mycpu`'s frame (its two stores carry `ra`/`s0` at `sp`, it writes no `s1`–`s11`), acquire's call;
  §3  the VALUE RULE: two 8-byte words neither of which is `cpuB x` take the same `seqz` result
      (`SilSite.ruleOfLkCpuNe` at `me = leNat (cpuB x)`, `leNatInj`);
  §4  **the member side**: `CpuTop` (the `lk->cpu` half of `SbReplay.ExValTop`) from the P-W6 state-map
      interface `CpuTopMap` and the merged export twin `Xv6.AccessDiscipline.lkCpuReadAtP` (a non-holder
      reading `lk->cpu` at ANY landing view from an initial value ≠ its own pointer never obtains it);
  §5  the GF side `CpuGF` (the `lk->cpu` half of `SbReplay.ExValGF`) from `SbHeadHop2.HoldZero`
      (proved from its floor decomposition in `Weak/SbHoldZero.lean`), and **`holdCpuExempt`** — THE
      MAIN EXEMPTION THEOREM: the two exempt-value interfaces of the walk from their halves.

Spec mark: FAITHFUL.  Named inputs (FAITHFUL statements, WEAKER while named): `CpuTopMap` (P-W6's state
map), `IrefTop`/`IrefGF` (F-P-W2-1, unchanged), `HoldZero`'s residuals (`Weak/SbHoldZero.lean`), the Sail
meaning of the taint walk (`SilSiteStep.sailQ`, O-P-W2-a — as for the two `ip->ref` pcs).
Lean-only helpers `SbHoldX.*`.
-/
import Weak.SbHeadHop2
import Weak.AxSpinT2a
import Xv6.AccessDiscipline

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open KernelPinsDef
open Lbl SbWalk SbAgree SbReplay SbOrd

/-! # 1. The exemption predicate -/

/-- `holding+0x12` (`0x80000c04`, `ld a5,16(a0)`: `lk->cpu`, `spinlock.c:holding`). -/
def SbHoldX.holdCpuPc (pc : Int) : Prop := pc = SilSite.sym KernelSyms.«holding» 0x12

/-- The return point of `acquire`'s `jal holding` (`acquire+0x16`). -/
def SbHoldX.acqHoldRet : BitVec 64 := BitVec.ofNat 64 (KernelSyms.«acquire» + 0x16)

/-- **REVISIT [OWN.124]** (the owner asked to look at this exemption again; the alternative on file is
(b), a custody-aware `waitedOn` with a per-load MachCSL footprint record, R46 §4).
**THE THIRD EXEMPT READ**: GF event `e`'s emission block realizes at `holding+0x12` and starts from a
hart state whose `ra` is `acquire+0x16` — the `lk->cpu` read of `holding(lk)` called from
`acquire(lk)` (the `release`/`sched` calls, where the reader holds `lk`, are not exempt). -/
def SbHoldX.holdCpuX (D : Nat → CertZ7.EmData) (e : Geid) : Prop :=
  SilSite.blockPc ((D e.1).g e.2) = some (SilSite.sym KernelSyms.«holding» 0x12) ∧
    ∃ cpu m rs fn ib, (D e.1).f e.2 = .PHart cpu m rs fn ib ∧ gprVal rs 1#5 = SbHoldX.acqHoldRet

/-- The walk's exempt set: the two `ip->ref` reads ([OWN.112]) and `holding+0x12` from `acquire`
([OWN.124]). -/
def SbHoldX.exemptX (D : Nat → CertZ7.EmData) (e : Geid) : Prop := ipRefX D e ∨ SbHoldX.holdCpuX D e

theorem SbHoldX.holdCpuPcEq : SilSite.sym KernelSyms.«holding» 0x12 = 0x80000c04 := by decide

/-! # 2. Static facts (`decide +kernel`) -/

/-- **THE TAINT, RE-HOSTED** (`SilSiteTaint`'s static walk, landed): from `holding+0x12`, with the
loaded word fully poisoned, every path kills the difference at `seqz a0` (`holding+0x1e`, rule
`ruHolding`) before any sink — across `jal mycpu` (the walk descends into the call); without the kill
it fails. -/
theorem SbHoldX.holdCpuTaint :
    SilSite.siteOk (SilSite.sym KernelSyms.«holding» 0x12) SilSite.FULL SilSite.ruHolding = true ∧
      SilSite.siteOk (SilSite.sym KernelSyms.«holding» 0x12) SilSite.FULL SilSite.noRules = false :=
  ⟨SilSite.holding12Ok, SilSite.holding12NeedsKill⟩

/-- `mycpu`'s instructions (`0x8000195c`–`0x8000197a`, 14 instructions, the last a `ret`). -/
def SbHoldX.mycpuPcs : List Int :=
  [0x8000195c, 0x8000195e, 0x80001960, 0x80001962, 0x80001964, 0x80001966, 0x80001968, 0x8000196a,
    0x8000196e, 0x80001972, 0x80001974, 0x80001976, 0x80001978, 0x8000197a]

/-- A destination register is NOT callee-saved `s1`–`s11` (`x9`, `x18`–`x27`). -/
def SbHoldX.notS1to11 (r : Nat) : Bool := !(r == 9 || (18 ≤ r && r ≤ 27))

/-- **THE PATH'S SHAPE** from `holding+0x12` to the kill: `mv s1,a5` (`holding+0x14`), `jal mycpu`
(`holding+0x16`, returning to `holding+0x1a`), `sub a0,s1,a0` (`holding+0x1a`), `seqz a0,a0`
(`holding+0x1e`); the load writes `a5`.  `mycpu` is straight-line from its entry to its `ret`: its only
stores are `sd ra,8(sp)` and `sd s0,0(sp)` (address `sp`, data `ra` / `s0`), and none of its
instructions writes `s1`–`s11` (`s0` is restored from its own spill).  `acquire+0x12` is acquire's
`jal holding`, returning to `acquire+0x16`. -/
theorem SbHoldX.holdCpuShape :
    loadRd (SilSite.sym KernelSyms.«holding» 0x12) = some 15 ∧
      SilSite.sym KernelSyms.«holding» 0x12 + wSize (kw (SilSite.sym KernelSyms.«holding» 0x12)) =
        SilSite.sym KernelSyms.«holding» 0x14 ∧
      depsRd (krole (SilSite.sym KernelSyms.«holding» 0x14)) = some (9, [.DReg 15]) ∧
      SilSite.sym KernelSyms.«holding» 0x14 + wSize (kw (SilSite.sym KernelSyms.«holding» 0x14)) =
        SilSite.sym KernelSyms.«holding» 0x16 ∧
      kflowOf (SilSite.sym KernelSyms.«holding» 0x16) = .FLcall (KernelSyms.«mycpu» : Int) ∧
      SilSite.sym KernelSyms.«holding» 0x16 + wSize (kw (SilSite.sym KernelSyms.«holding» 0x16)) =
        SilSite.sym KernelSyms.«holding» 0x1a ∧
      SilSite.sym KernelSyms.«holding» 0x1a + wSize (kw (SilSite.sym KernelSyms.«holding» 0x1a)) =
        SilSite.sym KernelSyms.«holding» 0x1e ∧
      SbHoldX.mycpuPcs.head? = some (KernelSyms.«mycpu» : Int) ∧
      (SbHoldX.mycpuPcs.zip SbHoldX.mycpuPcs.tail).all (fun p => p.1 + wSize (kw p.1) == p.2) = true ∧
      (SbHoldX.mycpuPcs.dropLast).all (fun pc => match kflowOf pc with
        | .FLnone => true
        | _ => false) = true ∧
      kflowOf 0x8000197a = .FLret ∧
      SbHoldX.mycpuPcs.filter (fun pc => roleIsStore (krole pc)) = [0x8000195e, 0x80001960] ∧
      depsVsrc (krole 0x8000195e) = [.DReg 1] ∧ depsAddr (krole 0x8000195e) = [.DReg 2] ∧
      depsVsrc (krole 0x80001960) = [.DReg 8] ∧ depsAddr (krole 0x80001960) = [.DReg 2] ∧
      SbHoldX.mycpuPcs.all (fun pc =>
        (match depsRd (krole pc) with
         | some (rd, _) => SbHoldX.notS1to11 rd
         | none => true) &&
        (match depsRd2 (krole pc) with
         | some (rd, _) => SbHoldX.notS1to11 rd
         | none => true)) = true ∧
      kflowOf (SilSite.sym KernelSyms.«acquire» 0x12) = .FLcall (KernelSyms.«holding» : Int) ∧
      SilSite.sym KernelSyms.«acquire» 0x12 + wSize (kw (SilSite.sym KernelSyms.«acquire» 0x12)) =
        SilSite.sym KernelSyms.«acquire» 0x16 ∧
      SbHoldX.acqHoldRet = BitVec.ofInt 64 (SilSite.sym KernelSyms.«acquire» 0x16) := by
  decide +kernel

/-! # 3. The value rule -/

theorem SbHoldX.leNatInj : ∀ (a b : List (BitVec 8)), a.length = b.length →
    SilSite.leNat a = SilSite.leNat b → a = b
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | x :: xs, y :: ys, h, hv => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at h
    simp only [SilSite.leNat] at hv
    have hx := x.isLt
    have hy := y.isLt
    have h1 : x.toNat = y.toNat := by omega
    have h2 : SilSite.leNat xs = SilSite.leNat ys := by omega
    rw [BitVec.eq_of_toNat_eq h1, SbHoldX.leNatInj xs ys h h2]

theorem SbHoldX.cpuBLength (x : Nat) : (cpuB x).length = 8 := by simp [cpuB]

/-- **THE VALUE RULE of the third pc**: two 8-byte words with the exempt-value fact of row `x` (neither
is `&cpus[x]`) meet `holding+0x12`'s rule (`seqz (v − mycpu())` is 0 on both sides) at
`me = leNat (cpuB x)`. -/
theorem SbHoldX.holdCpuRule (x : Nat) (vs vs' : List (BitVec 8)) :
    vs.length = 8 → vs'.length = 8 → exValV x vs → exValV x vs' →
    SilSite.vRule (SilSite.sym KernelSyms.«holding» 0x12) (SilSite.leNat (cpuB x)) vs vs' := by
  intro h1 h2 hv hv'
  apply SilSite.ruleOfLkCpuNe
  · exact fun e => hv.2 h1 (SbHoldX.leNatInj _ _ (by rw [h1, SbHoldX.cpuBLength]) e)
  · exact fun e => hv'.2 h2 (SbHoldX.leNatInj _ _ (by rw [h2, SbHoldX.cpuBLength]) e)

/-! # 4. The member side -/

open Xv6 Xv6.AccessDiscipline in
/-- What P-W6's state map gives at an exempt `holding+0x12` head of hart `c`: for EVERY decomposition
of the lock's merged word histories that `lkCpuReadAtP` speaks of, `c` is not the decomposition's
holder (x's own events are realized: its last write to `L` is a release, or it has none) and the word
`wd` the member reads at the top is one of `c`'s readings of `lk->cpu` from an initial value other than
`&cpus[c]` (the image's 0, resp. `initlock`'s 0 at a pipe lock's window opening). -/
def SbHoldX.NonHolderRd (σ : MState) (b : PAddr) (t : Nat) (c : CPU) (wd : BitVec 64) : Prop :=
  (b ∈ xv6StaticLocks →
    ∀ (W : WordHist 4) (W' : WordHist 8) (Hold Hold' : Nat → Hist) (st : Option (CPU × Bool)) (B : Nat),
      wordHistAt σ.mem b 4 W Hold → wordHistAt σ.mem (b + 16#64) 8 W' Hold' →
      lockDiscW (cpuPtrAt KernelGeom.cpusBase) st B W W' →
      (∀ k, st ≠ some (c, k)) ∧ ∃ tvn v0, v0 ≠ cpuAddr c ∧ ReadCasesP σ.lp W' (hartAgent c) tvn v0 wd) ∧
  (xv6DynLockP σ b t →
    ∀ (L : List (PAddr × HEnt)) (te p : Nat) (W : WordHist 4) (W' : WordHist 8) (st : Option (CPU × Bool))
      (B : Nat), slotWit xv6Rsv L b te → p ≤ te → te ≤ t →
      (∀ j, j < 4 → ∃ H, (σ.mem.lview σ.lp)[b + BitVec.ofNat 64 j]? = some H ∧
        H.filter (lkWinIn p t) = W.map (WEnt.proj j)) →
      (∀ j, j < 8 → ∃ H, (σ.mem.lview σ.lp)[b + 16#64 + BitVec.ofNat 64 j]? = some H ∧
        H.filter (lkWinIn p t) = W'.map (WEnt.proj j)) →
      lockDiscWin (cpuPtrAt KernelGeom.cpusBase) st B W W' →
      (∀ k, st ≠ some (c, k)) ∧ ∃ tvn v0, v0 ≠ cpuAddr c ∧ ReadCases W' (hartAgent c) tvn v0 wd)

open Xv6 Xv6.AccessDiscipline in
/-- **THE EXPORT TWIN AT A NON-HOLDER'S READ**: `lkCpuReadAtP` at a lock word `b` and a non-holder
reading `wd` ⇒ `wd ≠ &cpus[c]`. -/
theorem SbHoldX.cpuNeOfRd (σ : MState) (b : PAddr) (t : Nat) (c : CPU) (wd : BitVec 64) :
    lkCpuReadAtP σ → xv6LockWordP σ b t → SbHoldX.NonHolderRd σ b t c wd → wd ≠ cpuAddr c := by
  intro hR hlw hN
  obtain ⟨hs, hd⟩ := hR b t hlw
  rcases hlw with hst | hdyn
  · obtain ⟨W, W', Hold, Hold', st, B, h1, h2, h3, h4⟩ := hs hst
    obtain ⟨hnh, tvn, v0, hv0, hrc⟩ := hN.1 hst W W' Hold Hold' st B h1 h2 h3
    exact h4 c hnh tvn v0 wd hv0 hrc
  · obtain ⟨L, te, p, W, W', st, B, h1, h2, h3, h4, h5, h6, h7⟩ := hd hdyn
    obtain ⟨hnh, tvn, v0, hv0, hrc⟩ := hN.2 hdyn L te p W W' st B h1 h2 h3 h4 h5 h6
    exact h7 c hnh tvn v0 wd hv0 hrc

/-- `&cpus[c]`'s word from `cpuB` is `cpuAddr c`. -/
theorem SbHoldX.cpuBWord : ∀ c : CPU, wordOfBytes 8 (cpuB c.val) = cpuAddr c := by decide +kernel

/-- `cpuB` is the store data of `cpuAddr c` (`stBytes 8`, the emission's 8-byte store bytes). -/
theorem SbHoldX.cpuBStBytes : ∀ c : CPU, stBytes 8 (cpuAddr c) = cpuB c.val := by decide +kernel

/-- **THE `lk->cpu` HALF OF `ExValTop`**: at a walk state, the top word an 8-byte exempt read of a row's
next GF event would read is not the row's `&cpus[x]`. -/
def SbHoldX.CpuTop (G : Gexec) (X : Geid → Prop) (w : WS) : Prop :=
  ∀ (x : Nat) (base : Int) (ts : List Nat) (vs vs' : List (BitVec 8)), X (x, (w.rows x).length) →
    gxLbl G (x, (w.rows x).length) = some (LLoad false base ts vs) → vs'.length = ts.length →
    ts.length = 8 → topVals w x base vs' → vs' ≠ cpuB x

open Xv6 Xv6.AccessDiscipline in
/-- **THE P-W6 INTERFACE (member side, NAMED)**: P-W6's state map sends the walk state to a reachable
route-P machine state `σ` (where the export twin `lkCpuReadAtP` holds), row `x` to hart `c`, an 8-byte
exempt head's footprint to `lk->cpu` of a lock word `b` (`base = b + 16`), and the member's top word to a
non-holder reading of it (`NonHolderRd`). -/
def SbHoldX.CpuTopMap (G : Gexec) (X : Geid → Prop) (w : WS) : Prop :=
  ∀ (x : Nat) (base : Int) (ts : List Nat) (vs vs' : List (BitVec 8)), X (x, (w.rows x).length) →
    gxLbl G (x, (w.rows x).length) = some (LLoad false base ts vs) → vs'.length = ts.length →
    ts.length = 8 → topVals w x base vs' →
    ∃ (σ : MState) (b : PAddr) (t : Nat) (c : CPU), lkCpuReadAtP σ ∧ c.val = x ∧
      base = (b.toNat : Int) + 16 ∧ xv6LockWordP σ b t ∧ SbHoldX.NonHolderRd σ b t c (wordOfBytes 8 vs')

/-- **THE MEMBER SIDE FROM THE EXPORT TWIN**: `CpuTopMap` ⇒ `CpuTop` (through `lkCpuReadAtP`). -/
theorem SbHoldX.cpuTopOfMap (G : Gexec) (X : Geid → Prop) (w : WS) :
    SbHoldX.CpuTopMap G X w → SbHoldX.CpuTop G X w := by
  intro hM x base ts vs vs' hx hl hlen h8 htop he
  obtain ⟨σ, b, t, c, hR, hc, -, hlw, hN⟩ := hM x base ts vs vs' hx hl hlen h8 htop
  subst hc
  apply SbHoldX.cpuNeOfRd σ b t c _ hR hlw hN
  rw [he]
  exact SbHoldX.cpuBWord c

/-! # 5. The GF side and the main theorem -/

/-- **THE `lk->cpu` HALF OF `ExValGF`**: GF's 8-byte exempt reads do not see the row's `&cpus[x]`. -/
def SbHoldX.CpuGF (G : Gexec) (X : Geid → Prop) : Prop :=
  ∀ e base ts vs, X e → gxLbl G e = some (LLoad false base ts vs) → vs.length = 8 → vs ≠ cpuB e.1

/-- `CpuGF` from `SbHeadHop2.HoldZero`, given that every 8-byte exempt read is an `acquire`-context
`holding+0x12` read of the lock at `base − 16` (the realization's label ↔ pc transport (T)). -/
theorem SbHoldX.cpuGFOfHoldZero (G : Gexec) (X : Geid → Prop) (AcqCpuRd : Geid → Int → Prop) :
    (∀ e base ts vs, X e → gxLbl G e = some (LLoad false base ts vs) → vs.length = 8 →
      AcqCpuRd e (base - 16)) →
    SbHeadHop2.HoldZero G cpuB AcqCpuRd → SbHoldX.CpuGF G X := by
  intro hT hZ e base ts vs hx hl h8
  exact hZ e (base - 16) base ts vs (hT e base ts vs hx hl h8) hl (by omega)

/-- **REVISIT [OWN.124]** (the owner asked to look at this exemption again; the alternative on file is
(b), a custody-aware `waitedOn` with a per-load MachCSL footprint record, R46 §4).
**THE MAIN EXEMPTION THEOREM**: the walk's two exempt-value interfaces from their halves — member side
`ExValTop` from the `ip->ref` half `IrefTop` (F-P-W2-1) and the `lk->cpu` half through P-W6's state map
and the export twin `lkCpuReadAtP` (`CpuTopMap`); GF side `ExValGF` from `IrefGF` and `HoldZero` (given
the transport of 8-byte exempt reads to `acquire`-context `holding+0x12` reads) — with the third pc's
taint and value rule (`holdCpuTaint`, `holdCpuRule`) for the lockstep. -/
theorem SbHoldX.holdCpuExempt (G : Gexec) (X : Geid → Prop) (w : WS) (AcqCpuRd : Geid → Int → Prop)
    (hXL : ∀ e l, X e → gxLbl G e = some l → ∃ base ts vs, l = LLoad false base ts vs)
    (hIT : IrefTop G X w) (hCT : SbHoldX.CpuTopMap G X w)
    (hIG : IrefGF G X) (hT : ∀ e base ts vs, X e → gxLbl G e = some (LLoad false base ts vs) →
      vs.length = 8 → AcqCpuRd e (base - 16))
    (hZ : SbHeadHop2.HoldZero G cpuB AcqCpuRd) :
    ExValTop G X w ∧ ExValGF G X ∧
      SilSite.siteOk (SilSite.sym KernelSyms.«holding» 0x12) SilSite.FULL SilSite.ruHolding = true ∧
      (∀ x vs vs', vs.length = 8 → vs'.length = 8 → exValV x vs → exValV x vs' →
        SilSite.vRule (SilSite.sym KernelSyms.«holding» 0x12) (SilSite.leNat (cpuB x)) vs vs') := by
  have hCT' := SbHoldX.cpuTopOfMap G X w hCT
  have hCG := SbHoldX.cpuGFOfHoldZero G X AcqCpuRd hT hZ
  refine ⟨?_, ?_, SbHoldX.holdCpuTaint.1, SbHoldX.holdCpuRule⟩
  · intro x base ts vs vs' hx hl hlen htop
    exact ⟨fun h4 => hIT x base ts vs vs' hx hl hlen (by omega) htop,
      fun h8 => hCT' x base ts vs vs' hx hl hlen (by omega) htop⟩
  · intro e l hx hl
    obtain ⟨base, ts, vs, rfl⟩ := hXL e l hx hl
    exact ⟨base, ts, vs, rfl, fun h4 => hIG e base ts vs hx hl h4,
      fun h8 => hCG e base ts vs hx hl h8⟩

end Weak
