/-
Weak: **the two LOCK-WORD-NEIGHBOUR LEAVES of xv6's real `release` (and acquire's `lk->cpu`
store)** at the joint instance Ixv6 — Theorem 2 design (`notes/weak-lb-thm2-design.md` §C.1,
§C.2, §D row `AxSpinRl2`).  NEW Lean file (no Rocq source: Rocq's `AxSpinRs`/`AxSpinRl*` were
never written).

## What this file provides

§1 KERNEL CROSS-CHECK.  `AxSpinRl2.cpuWords` (`decide +kernel` on `Xv6.Kernel.textTree`): this
   tree's image holds exactly the three words the leaves are about —
     acquire + 0x28 = 0x80000c80  `c.sd a0,16(s1)`   0xe888      (2 bytes, RVC)
     release + 0x12 = 0x80000cf2  `sd zero,16(s1)`   0x0004b823  (4 bytes)
     release + 0x16 = 0x80000cf6  `fence rw,w`       0x0310000f  (4 bytes)
   (release+0x12/+0x16 are 2 mod 4 — fine since the Q22 rework of `textAt4S`).  The ASTs:
   `0x0004b823` = `.STORE (16#12, x0, x9, 8)`, `0xe888` expands to `.STORE (16#12, x10, x9, 8)`,
   `0x0310000f` = `fenceRwW` (pred = rw, succ = w).  The leaves take `textOkB …` of these
   ASTs as premises (the callers discharge them with the `*TextOf` certificates).
§2 `XxFence` — THE POSITIONAL FENCE LEAF (`fence rw,w`): one row item at `k`, continuation at
   `k + 1`, GPRs unchanged, no flow resource (data region `dok0`).  Built as every positional
   leaf of AxSpinE6 (`XBk` over a `CertB`); the certificate `AxSpinRl2.certFenceB` is
   `AxCert4.certExecuteFence` at a FINITE budget (`BFin (1 + b)` → `BFin b`, the `cFence` arm),
   and `XBk`'s bridge (`AxSpinE4.wpdOfCertK`) discharges that arm with `AxCert2.wpdFenceNodeM`
   (`Weak/AxCert2.lean:337`) — the node lemma the design names.  The `CertB` also records that the
   release-pending flag is ARMED after the fence (`PX d r := d = d0 ∧ r = true`).
§3 THE lk->cpu FLOW.  `CpuWin L GT i e` (design Q-T2-9, "the handle window is a row premise"):
   every row write of hart `i` to `lk->cpu` (`L.xlLk + 16`) po-AFTER the anchor `e` is a plain
   8-byte store of `cvx i` or of 0, and `e` is lob-before it.  `FstMCpu`: given the anchor's
   annotation `e ↦ₐ P` with `P -∗ Q ∗ ∃ vold, RVL (clb L) e vold`, a position-generic store flow
   `FstM (dokAtP (L.xlLk + 16) 8) i (OCpu … Q)`: at every lk->cpu store position `k > e.2` it is
   `AxSpinX2.fxCpuWrite` drawing the handle from `e` (`AxSpinHdB.dflowODraw`), depositing
   `(i, k) ↦ₐ Q ∗ RVL (clb L) (i, k) data` (`OCpu`, + the row label); a position `k ≤ e.2` is
   refuted by the annotation itself (`AxSpinRl2.dflowOPast`: an owned annotation of hart `i`
   lies before the current position, `annotAgree` + `naAtProgress`).  Helpers for the callers:
   `cpuWinOfList` (CpuWin from a finite list of lk->cpu store positions), and the two anchor
   kinds' lob facts — `AxSpinRl2.lobpAcq` (acquire's `.aq` claim RMW: ppo rule 5, `acqGob`) and
   `AxSpinRl2.lobpCpuSt` / `AxSpinRl2.lobpCpuLd` (an earlier lk->cpu store / load: ppo rule 1,
   `locLobp`).
§4 `XxSdCpu` — THE 8-BYTE OWNED lk->cpu STORE LEAF, VALUE GENERIC: `XxStF` (AxSpinAp8) over
   `FstMCpu`; the store is at `k`, the continuation at `k + 1` learns the graph data
   (`wbytes 8 val`, `val` = the source register's value), the row label
   `LStore false (L.xlLk + 16) (wbytes 8 val) cls` (exactly `AxSpinHdB.FldMCpuOwn`'s `Hw`
   premise, so release's holding can read acquire's store back) and the deposited handle
   `(i, k) ↦ₐ Q ∗ RVL (clb L) (i, k) (wbytes 8 val)` (exactly `FldMCpuOwn`'s `Hh`).  ONE leaf
   serves both call sites:
     * acquire (`c.sd a0,16(s1)`, `is_rvc = true`, `val = cpuAddr (cpuOf i)`): anchor `e` = the
       claim `(i, aqKA …)`, `P` = its `RCPU` half after `wpdAnnotSplit` (`Q := True`);
     * release (`sd zero,16(s1)`, `is_rvc = false`, `rs2 = x0`, `val = 0`): anchor `e'` ∈
       {acquire's sd `(i, kw)`, holding's lk->cpu read `(i, kr)`} — `FldMCpuOwn`'s `OOwn`
       output, `P = Q ∗ RVL (clb L) e' (wbytes 8 val)`.
   Shape-positioned corollaries: `XxFenceRel` (at `relKf k`, continuation `relKw k`),
   `XxSdCpuRel` (at `relKc k`, continuation `relKf k`), both over AxSpinRl1's `RowRelease`;
   `XxSdCpuAcq` (at `aqKm … + 4`, continuation `+ 5`) over AxSpinAqr's `RowAcquire`, with the
   row-label projection `rowAcquireCpu`.

## Deviations from the design / honesty notes

1. `XxFence` uses the `XBk` route (CertB + the positional bridge) rather than calling
   `wpdFenceNodeM` directly: the bridge's fence arm IS `wpdFenceNodeM`, and `XBk` supplies the
   fetch / regime / Stage C bookkeeping every other leaf uses.  Same statement shape as `XxReg`
   with continuation `k + 1`.
2. Q-T2-9 REALISED WITH A DATA CONDITION.  `FstM` (AxSymMem) quantifies over EVERY row position
   (`XBk`'s store bridge has no window, unlike `AxCertP3.FldMW` for loads), so the flow must be a
   legal owned write at every lk->cpu store position after the anchor — and `fxCpuWrite` needs
   the written value to be `cvx i` or 0 (Φ_cpu, `cpuOk`).  Hence `CpuWin` constrains the DATA of
   hart `i`'s own lk->cpu stores after the anchor (acquire's anchor sees BOTH acquire's and
   release's sd), not only "no other write between".  This is a graph-value condition on hart
   `i`'s OWN stores (of the same kind as `FldMCpuOwn`'s exact-label premise `Hw` and the Option V
   pins): true on every row of the real code (`cpuAddr` from mycpu, `x0`), and to be listed among
   `allocFull`'s value conditions (AxSpinT2a).  It says nothing about other harts.  OPEN QUESTION
   for the orchestrator: confirm that T2a's row family carries "hart i's lk->cpu stores write
   `cvx i` / 0" (else a windowed store bridge, `FstRmwW`-style for `DKSt`, is needed — M).
3. The value is generic (`val` with `gprVal rs rs2 = val`); nothing about `val` is assumed by
   the leaf — `CpuWin` already pins the row data, so the caller knows `wbytes 8 val ∈ {cvx i, 0}`
   from the continuation's label fact.

**Reused:** `XBk`, `HGX`/`HtextX`/`HflowX`/`HlocX`/`HL0`/`HGex0`, `AxSpinE6.Hmid0`, `FstDok0M`
(AxSpinE4/E5/E6, AxCert4), `executeFenceRwW`, `AxCert4.cFactRead`, `relpUpdRwW`,
`ctrlOkSPriv` (AxCert4, AxCert), `XxStF`, `a8Gmo` (AxSpinAp8), `fxCpuWrite` (AxSpinX2),
`dflowODraw` (AxSpinHdB), `annotAgree`, `elemOfEidsBefore` (AxWp), `gwbStoren`, `inClr`,
`AxSpinX4.clRangeLookup`, `lblOfRow`, `gpoRow`, `acqGob`, `gobGmo`, `lobpIntro`, `locLobp`,
`loadnReads`/`lblTsLen` (AxSpinX3/X4/X5, AxSpinE5, AxSpinProt3/5), `RowRelease`/`relK*`/
`rowReleaseLen` (AxSpinRl1), `RowAcquire`/`aqKm`/`aqTail` (AxSpinAqr).  New names grepped
absent from the tree.
-/
import Weak.AxSpinRl1
import Weak.AxSpinAp8

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std Iris.Std.PartialMap MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D LeanRV64D.Functions

/-! # 1. Kernel cross-check -/

/-- (Lean-only) this tree's image holds acquire+0x28 `c.sd a0,16(s1)` (0xe888, 2 bytes),
release+0x12 `sd zero,16(s1)` (0x0004b823) and release+0x16 `fence rw,w` (0x0310000f). -/
theorem AxSpinRl2.cpuWords :
    ([(0x80000c80, 2, 0xe888), (0x80000cf2, 4, 0x0004b823), (0x80000cf6, 4, 0x0310000f)] :
        List (Nat × Nat × Nat)).all
      (fun p => match Xv6.Kernel.textTree.find? p.1 with
        | some k => Nat.beq k.width p.2.1 && Nat.beq k.enc p.2.2
        | none => false) = true := by
  decide +kernel

/-- (Lean-only) the offsets: acquire = 0x80000c58, release = 0x80000ce0. -/
theorem AxSpinRl2.cpuOffsets :
    (KernelSyms.«acquire» : Nat) + 0x28 = 0x80000c80 ∧
    (KernelSyms.«release» : Nat) + 0x12 = 0x80000cf2 ∧
    (KernelSyms.«release» : Nat) + 0x16 = 0x80000cf6 := by
  decide +kernel

/-- (Lean-only) an 8-byte store's bus bytes are the register's bytes. -/
theorem AxSpinRl2.stData8 (v : BitVec 64) : AxDataX.stData 8 v = v := by
  unfold AxDataX.stData
  show BitVec.setWidth 64 (Sail.BitVec.extractLsb v 63 0) = v
  unfold Sail.BitVec.extractLsb
  bv_decide

theorem AxSpinRl2.stBytes8 (v : BitVec 64) : stBytes 8 v = WeakInterpProj.wbytes 8 v := by
  unfold stBytes AxDataX.wrb
  rw [AxSpinRl2.stData8]

/-! # 2. The fence leaf -/

section certF
variable (σi : ExecSt) (T : PTree) (satp0 : BitVec 64)

/-- (Lean-only) `execute (fence rw,w)` consumes exactly one row item (the `cFence` arm) and arms
the release-pending flag. -/
theorem AxSpinRl2.certFenceB (dok : Int → Nat → Prop) (kind : Dkind) (rs : RegFile)
    (pc : BitVec 64) (d0 : Cdata) (r0 : Bool) :
    CertB σi T satp0 dok kind rs pc false fenceRwW 1 none (fun _ => none) d0 r0
      (fun d r => d = d0 ∧ r = true) := by
  intro tpc Hct _ _ _ _ b
  have Hpriv : tpc.regs .cur_privilege = .Supervisor := ctrlOkSPriv T satp0 _ Hct.1
  rw [executeFenceRwW, Nat.add_comm 1 b]
  apply CertBind
  unfold is_fiom_active
  refine AxCert4.cFactRead (AxSymEngine2.notPin _ (by decide) (by decide)) ?_
  rw [Hpriv]
  refine AxCert4.cFactRead (AxSymEngine2.notPin _ (by decide) (by decide)) ?_
  refine .cRet _ _ _ ?_
  exact .cFence d0 (.BFin b) r0 _ _ tpc rfl
    (.cRet _ _ _ ⟨rfl, d0, _, rfl, ⟨rfl, relpUpdRwW r0⟩, rfl⟩)

end certF

section leaves
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
variable (Ψ : Athread → IProp GF)
variable (HΨmid : ∀ s, midState s → s.atK = (AxOpsem.grow (gtAdGd GT) i).length →
  ⊢ @postLifting GF (AxSpinX2.xG L GT nm) Ψ i s)

include HL Hcons hmode hasid hppn Hfix HΨmid in
/-- THE POSITIONAL FENCE LEAF: `fence rw,w` at `k` (one row item, no flow), continuation at
`k + 1` with the GPRs unchanged. -/
theorem XxFence (s : Athread) (rs : RegFile) (k : Nat) (pc : BitVec 64) :
    RetX cpu rs k s → ctrlOkSW T satp0 rs → rs .PC = pc → hitW rs pc →
    textOkB σi T satp0 pc false fenceRwW →
    k + 1 ≤ (AxOpsem.grow (gtAdGd GT) i).length →
    ⊢ (∀ (rs' : RegFile) (ib' : Ibch), ⌜GoodB T satp0 rs pc false none none rs'⌝ -∗
        @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
          ⟨.PHart cpu (.pure ()) rs' none ib', k + 1⟩ Ψ) -∗
      @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i s Ψ := by
  intro HRet Hc HPC Hhit Htx Hle
  have H := @XBk hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) σi T satp0 hmode hasid hppn i cpu
    (fun GD => GD = gtAdGd GT) (HGX L GT nm) (AxOpsem.grow (gtAdGd GT) i).length (HL0 GT i)
    (HGex0 GT) Ψ (AxSpinE6.Hmid0 L GT nm i Ψ HΨmid) (HtextX L GT nm (imgS σi) i Hfix)
    (HflowX L GT nm HL Hcons (imgS σi) i) (HlocX L GT nm i)
    dok0 .DKSt (by intro h; cases h) (by intro h; cases h) (fun _ _ => iprop(True))
    s rs k pc false fenceRwW 1 none (fun _ => none) .CPend false
    (fun d r => d = .CPend ∧ r = true)
    HRet Hc HPC Hhit Htx (fun _ _ _ => trivial)
    (AxSpinRl2.certFenceB σi T satp0 dok0 .DKSt rs pc .CPend false)
    (by omega) Hle
  iintro C
  iapply H $$ [] [C]
  · simp only [CResK, CFkM]
    letI : AxirisG GF := AxSpinX2.xG L GT nm
    letI : Axpol := xv6Pol GT
    iapply (FstDok0M (GF := GF) rvwmoCatConsistent i)
  · iintro %d %r %rs' %ib' %_ %HGB -
    iapply C $$ %rs' %ib' %HGB

end leaves

/-! # 3. The lk->cpu flow -/

/-- Q-T2-9, THE lk->cpu HANDLE WINDOW: every row write of hart `i` to `lk->cpu` po-after the
anchor `e` is a plain 8-byte store of `cvx i` or 0, and `e` is lob-before it. -/
def CpuWin (L : Xlay) (GT : GdexecT) (i : Agent) (e : Geid) : Prop :=
  ∀ (k : Nat) (lb : Lbl) (rl : Bool) (m : Nat), e.2 < k →
    (AxOpsem.grow (gtAdGd GT) i)[k]? = some lb →
    aidentWr (aident lb) = some (rl, L.xlLk + 16, m) →
    (∃ vw cls, lb = .LStore false (L.xlLk + 16) vw cls ∧
      (vw = cvx i ∨ vw = List.replicate 8 b0)) ∧
    e ∈ @Axpol.lobp (xv6Pol GT) (gtAdGd GT) (i, k)

/-- `CpuWin` from a finite list `ks` containing every lk->cpu write position after the anchor. -/
theorem cpuWinOfList (L : Xlay) (GT : GdexecT) (i : Agent) (e : Geid) (ks : List Nat) :
    (∀ (k : Nat) (lb : Lbl) (rl : Bool) (m : Nat), e.2 < k →
      (AxOpsem.grow (gtAdGd GT) i)[k]? = some lb →
      aidentWr (aident lb) = some (rl, L.xlLk + 16, m) → k ∈ ks) →
    (∀ k ∈ ks, e.2 < k → ∃ vw cls,
      (AxOpsem.grow (gtAdGd GT) i)[k]? = some (.LStore false (L.xlLk + 16) vw cls) ∧
      (vw = cvx i ∨ vw = List.replicate 8 b0) ∧
      e ∈ @Axpol.lobp (xv6Pol GT) (gtAdGd GT) (i, k)) →
    CpuWin L GT i e := by
  intro Hall Hks k lb rl m hk Hlb Hid
  obtain ⟨vw, cls, Hl, Hv, Hin⟩ := Hks k (Hall k lb rl m hk Hlb Hid) hk
  rw [Hl] at Hlb
  cases Hlb
  exact ⟨⟨vw, cls, rfl, Hv⟩, Hin⟩

section lobs
variable (GT : GdexecT) (Hcons : rvwmoCatConsistent (gtAdGd GT))

include Hcons in
/-- (Lean-only) ppo rule 5: acquire's `.aq` claim RMW is lob-before every later memory event. -/
theorem AxSpinRl2.lobpAcq (i : Agent) (kA k : Nat) (la lb : Lbl) (base : Int) (n : Nat) :
    (AxOpsem.grow (gtAdGd GT) i)[kA]? = some la → aident la = .IRmw true false base n →
    (AxOpsem.grow (gtAdGd GT) i)[k]? = some lb → lbIsMem lb = true → kA < k →
    (i, kA) ∈ @Axpol.lobp (xv6Pol GT) (gtAdGd GT) (i, k) := by
  intro Ha Hid Hb Hm Hlt
  cases la with
  | LLoad _ _ _ _ => cases Hid
  | LStore _ _ _ _ => cases Hid
  | LFence _ _ _ _ => cases Hid
  | LIo _ _ _ => cases Hid
  | LRmw aq rl b ts rvs wvs cls =>
    simp only [aident, AidentT.IRmw.injEq] at Hid
    obtain ⟨rfl, rfl, -, -⟩ := Hid
    have Hla := lblOfRow _ _ _ _ Ha
    have Hlb := lblOfRow _ _ _ _ Hb
    exact lobpIntro (gtAdGd GT) (i, kA) (i, k) _ Hla rfl (gpoRow (gtAdGd GT) i kA k _ _ Hla Hlb Hlt)
      (gobGmo (gtAdGd GT) Hcons _ _ (acqGob (gtAdGd GT) i kA k _ _ _ _ _ _ Hla Hlb Hm Hlt))

include Hcons in
/-- (Lean-only) ppo rule 1: an earlier lk->cpu STORE is lob-before a later lk->cpu store. -/
theorem AxSpinRl2.lobpCpuSt (pcl : Int) (i : Agent) (kw k : Nat) (vs vw : List (BitVec 8))
    (cls cls' : WmClass) :
    (AxOpsem.grow (gtAdGd GT) i)[kw]? = some (.LStore false pcl vs cls) → vs ≠ [] →
    (AxOpsem.grow (gtAdGd GT) i)[k]? = some (.LStore false pcl vw cls') → vw ≠ [] → kw < k →
    (i, kw) ∈ @Axpol.lobp (xv6Pol GT) (gtAdGd GT) (i, k) := by
  intro Hw Hvs Hs Hvw Hlt
  have Hlw := lblOfRow _ _ _ _ Hw
  have Hls := lblOfRow _ _ _ _ Hs
  obtain ⟨v0, Hv0⟩ : ∃ v, vs[0]? = some v := ⟨_, List.getElem?_eq_getElem
    (List.length_pos_iff.2 Hvs)⟩
  obtain ⟨w0, Hw0⟩ : ∃ v, vw[0]? = some v := ⟨_, List.getElem?_eq_getElem
    (List.length_pos_iff.2 Hvw)⟩
  exact locLobp (gtAdGd GT) Hcons (i, kw) (i, k) _ (pcl + ((0 : Nat) : Int)) w0 Hlw rfl
    (gpoRow (gtAdGd GT) i kw k _ _ Hlw Hls Hlt)
    (Or.inl ⟨v0, (gwbStoren _ _ _ _ _ Hlw).1 0 v0 Hv0⟩) ((gwbStoren _ _ _ _ _ Hls).1 0 w0 Hw0)

include Hcons in
/-- (Lean-only) ppo rule 1: an earlier lk->cpu LOAD is lob-before a later lk->cpu store. -/
theorem AxSpinRl2.lobpCpuLd (pcl : Int) (i : Agent) (kr k : Nat) (aq : Bool) (ts : List Nat)
    (vs vw : List (BitVec 8)) (cls' : WmClass) :
    (AxOpsem.grow (gtAdGd GT) i)[kr]? = some (.LLoad aq pcl ts vs) → vs ≠ [] →
    (AxOpsem.grow (gtAdGd GT) i)[k]? = some (.LStore false pcl vw cls') → vw ≠ [] → kr < k →
    (i, kr) ∈ @Axpol.lobp (xv6Pol GT) (gtAdGd GT) (i, k) := by
  intro Hr Hvs Hs Hvw Hlt
  have Hlr := lblOfRow _ _ _ _ Hr
  have Hls := lblOfRow _ _ _ _ Hs
  have Hlen := lblTsLen _ Hcons.1 _ _ _ _ _ Hlr
  have hv : 0 < vs.length := List.length_pos_iff.2 Hvs
  obtain ⟨w0, Hw0⟩ : ∃ v, vw[0]? = some v := ⟨_, List.getElem?_eq_getElem
    (List.length_pos_iff.2 Hvw)⟩
  have Hrd : greadsByte (gtAdGd GT).gdG (i, kr) (pcl + ((0 : Nat) : Int)) (ts[0]'(by omega))
      (vs[0]'hv) :=
    ⟨_, pcl, ts, vs, 0, Hlr, rfl, List.getElem?_eq_getElem _, List.getElem?_eq_getElem _, rfl⟩
  exact locLobp (gtAdGd GT) Hcons (i, kr) (i, k) _ (pcl + ((0 : Nat) : Int)) w0 Hlr rfl
    (gpoRow (gtAdGd GT) i kr k _ _ Hlr Hls Hlt) (Or.inr ⟨_, _, Hrd⟩)
    ((gwbStoren _ _ _ _ _ Hls).1 0 w0 Hw0)

end lobs

section flow
variable {hlc : HasLC} {GF : BundledGFunctors.{0,0,0}} [InvGS_gen hlc GF] [AxannotGS GF]
  [AxSpinX.Xv6G GF]
variable (L : Xlay) (GT : GdexecT) (nm : Xv6N)
variable (HL : xlayOk L) (Hcons : rvwmoCatConsistent (gtAdGd GT))

/-- The lk->cpu store's output at `k`: its row label and the deposited last-value handle. -/
def OCpu (i : Agent) (Q : IProp GF) (k : Nat) (data : List (BitVec 8)) : IProp GF :=
  iprop(⌜∃ cls, (AxOpsem.grow (gtAdGd GT) i)[k]? =
      some (.LStore false (L.xlLk + 16) data cls)⌝ ∗
    AxAnnot.annotOwn (i, k) iprop(Q ∗ RVL nm.xnH (gtAdGd GT) (clb L) (i, k) data))

/-- (Lean-only) an owned annotation of hart `i` at `e` lies BEFORE the current position: a flow
at `k ≤ e.2` is vacuous. -/
theorem AxSpinRl2.dflowOPast (i : Agent) (k : Nat) (e : Geid) (P O : IProp GF) :
    e.1 = i → k ≤ e.2 →
    ⊢ AxAnnot.annotOwn e P -∗
      @dflowO hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) i (gtAdGd GT) k O := by
  intro He Hk
  iintro Hp
  unfold dflowO naAtProgress
  iintro %na ⟨%Hprog, Hannot⟩
  ihave ⟨%Hdom, -⟩ := annotAgree na e P $$ Hannot Hp
  have Hf : e ∈ FiniteSet.filter (fun e' : Geid => decide (e'.1 = i))
      (FiniteMap.dom_set na : GSet Geid) := elemOfFilter.2 ⟨by simp [He], Hdom⟩
  rw [Hprog, elemOfEidsBefore] at Hf
  exact absurd Hf.2.1 (by omega)

include HL Hcons in
/-- THE lk->cpu STORE FLOW: the handle drawn from the anchor `e` (any lk->cpu store after it,
value `cvx i` or 0 by `CpuWin`), deposited at the store (`OCpu`). -/
theorem FstMCpu (i : Agent) (e : Geid) (P Q : IProp GF) :
    e.1 = i → CpuWin L GT i e →
    (⊢ P -∗ iprop(Q ∗ ∃ vold, RVL nm.xnH (gtAdGd GT) (clb L) e vold)) →
    ⊢ AxAnnot.annotOwn e P -∗
      @FstM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent
        (dokAtP (L.xlLk + 16) 8) i (OCpu L GT nm i Q) := by
  intro He Hwin HP
  iintro Hh
  unfold FstM
  iintro %GD %ls %k %data %base %n %Hcs #Hg _ %Hgd %Hd
  ihave %Heq := (HGX L GT nm GD Hcs) $$ Hg
  subst Heq
  obtain ⟨⟨rfl, -⟩, lb, rl, Hlb, Hid⟩ := Hd
  rcases Nat.lt_or_ge k (e.2 + 1) with hk | hk
  · iapply (AxSpinRl2.dflowOPast L GT nm i k e P _ He (by omega)) $$ Hh
  obtain ⟨⟨vw, cls, rfl, Hv⟩, Hin⟩ := Hwin k lb rl _ (by omega) Hlb Hid
  have Hls := lblOfRow _ _ _ _ Hlb
  have Hvw : data = vw := by
    rw [graphData, Hls] at Hgd
    simpa [lblData] using Hgd.symm
  subst Hvw
  obtain ⟨Hwb, Hsg⟩ := gwbStoren _ _ _ _ _ Hls
  have Hl8 : data.length = 8 := by
    rcases Hv with rfl | rfl
    · exact cvxLength i
    · exact List.length_replicate
  have Honly : ∀ a v', gwritesByte (gtAdGd GT).gdG (i, k) a v' → a ∈ clb L := by
    intro a v' Hw
    obtain ⟨j, Hj, rfl⟩ := Hsg a v' Hw
    have hj := (List.getElem?_eq_some_iff.1 Hj).1
    unfold clb
    rw [inClr]
    omega
  have Hall : ∀ (j : Nat) a v, (clb L)[j]? = some a → data[j]? = some v →
      gwritesByte (gtAdGd GT).gdG (i, k) a v := by
    intro j a v Hj Hv'
    obtain ⟨rfl, -⟩ := AxSpinX4.clRangeLookup _ _ _ _ Hj
    exact Hwb j v Hv'
  have Hisw : gisW (gtAdGd GT).gdG (i, k) = true := by unfold gisW; rw [Hls]; rfl
  have Hsing : ⊢ ([∗map] Rin ∈ ({[e := P]} : Mea GF), Rin) -∗
      iprop(Q ∗ ∃ vold, RVL nm.xnH (gtAdGd GT) (clb L) e vold) := by
    iintro H
    ihave H2 := (BigSepM.bigSepM_singleton (M := GMapF Geid)).1 $$ H
    ihave HPw := HP
    iapply HPw $$ H2
  have Hfe0 := fxCpuWrite L GT nm HL Hcons (i, k) e data Q ({[e := P]} : Mea GF) Hisw
    (a8Gmo GT _ _ Hin) Hv Hall Honly
  have Hmono : ⊢ ▷ (iprop(Q ∗ RVL (GF := GF) nm.xnH (gtAdGd GT) (clb L) (i, k) data) -∗
      iprop((Q ∗ RVL nm.xnH (gtAdGd GT) (clb L) (i, k) data) ∗ True)) := by
    inext
    iintro H
    isplitl [H]
    · iexact H
    · itrivial
  ihave Hw0 := Hsing
  ihave Hfe1 := Hfe0
  ihave Hfe2 := Hfe1 $$ Hw0
  ihave Hm := Hmono
  ihave Hmn := (@flowEqDynMono hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) (gtAdGd GT) (i, k)
    (@Axpol.sPol (xv6Pol GT) (gtAdGd GT) (i, k)) ({[e := P]} : Mea GF)
    iprop(Q ∗ RVL nm.xnH (gtAdGd GT) (clb L) (i, k) data)
    iprop((Q ∗ RVL nm.xnH (gtAdGd GT) (clb L) (i, k) data) ∗ True))
  ihave Hfe := Hmn $$ Hm Hfe2
  iapply (dflowODraw L GT nm HL Hcons i k e P
    iprop(Q ∗ RVL nm.xnH (gtAdGd GT) (clb L) (i, k) data) iprop(True) _ Hin) $$ Hh Hfe
  iintro H1 -
  unfold OCpu
  isplitr
  · ipureintro
    exact ⟨cls, Hlb⟩
  · iexact H1

end flow

/-! # 4. The lk->cpu store leaf -/

section sdcpu
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
variable (Ψ : Athread → IProp GF)
variable (HΨmid : ∀ s, midState s → s.atK = (AxOpsem.grow (gtAdGd GT) i).length →
  ⊢ @postLifting GF (AxSpinX2.xG L GT nm) Ψ i s)

include HL Hcons hmode hasid hppn Hfix HΨmid in
/-- THE OWNED 8-BYTE lk->cpu STORE (acquire's `c.sd a0,16(s1)`, release's `sd zero,16(s1)`),
VALUE GENERIC: store at `k`, continuation at `k + 1` with the graph data, the row label and the
deposited last-value handle. -/
theorem XxSdCpu (s : Athread) (rs : RegFile) (k : Nat) (pc : BitVec 64) (is_rvc : Bool)
    (imm : BitVec 12) (rs2 rs1 : BitVec 5) (va pa val : BitVec 64) (e : Geid) (P Q : IProp GF) :
    RetX cpu rs k s → ctrlOkSW T satp0 rs → rs .PC = pc → hitW rs pc →
    textOkB σi T satp0 pc is_rvc (.STORE (imm, .Regidx rs2, .Regidx rs1, 8)) →
    va = gprVal rs rs1 + sign_extend (m := 64) imm →
    dataAtS σi T (.Store .Data) va 8 pa → hitW rs va → paZ pa = L.xlLk + 16 →
    gprVal rs rs2 = val →
    e.1 = i → CpuWin L GT i e →
    (⊢ P -∗ iprop(Q ∗ ∃ vold, RVL nm.xnH (gtAdGd GT) (clb L) e vold)) →
    k + 1 ≤ (AxOpsem.grow (gtAdGd GT) i).length →
    ⊢ AxAnnot.annotOwn e P -∗
      (∀ (rs' : RegFile) (ib' : Ibch), ⌜GoodB T satp0 rs pc is_rvc none none rs'⌝ -∗
        ⌜graphData (gtAdGd GT) (i, k) = some (WeakInterpProj.wbytes 8 val) ∧
          ∃ cls, (AxOpsem.grow (gtAdGd GT) i)[k]? =
            some (.LStore false (L.xlLk + 16) (WeakInterpProj.wbytes 8 val) cls)⌝ -∗
        AxAnnot.annotOwn (i, k)
          iprop(Q ∗ RVL nm.xnH (gtAdGd GT) (clb L) (i, k) (WeakInterpProj.wbytes 8 val)) -∗
        @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
          ⟨.PHart cpu (.pure ()) rs' none ib', k + 1⟩ Ψ) -∗
      @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i s Ψ := by
  intro HRet Hc HPC Hhit Htx Hva Hda Hhv Hpa Hval He Hwin HP Hle
  have HF := FstMCpu L GT nm HL Hcons i e P Q He Hwin HP
  rw [← Hpa] at HF
  have H := XxStF L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu Hfix Ψ HΨmid s rs k pc
    is_rvc imm rs2 rs1 8 va pa (OCpu L GT nm i Q) HRet Hc HPC Hhit Htx vw8 (by omega) (by omega)
    Hva Hda Hhv Hle
  have E : stBytes 8 (gprVal rs rs2) = WeakInterpProj.wbytes 8 val := by
    rw [AxSpinRl2.stBytes8, Hval]
  rw [E] at H
  iintro Hh C
  ihave F := HF $$ Hh
  iapply H $$ F
  iintro %rs' %ib' %HGB %Hgd HO
  unfold OCpu
  icases HO with ⟨%Hlb, HO⟩
  iapply C $$ %rs' %ib' %HGB %⟨Hgd, Hlb⟩ HO

/-! ## Shape-positioned corollaries -/

include HL Hcons hmode hasid hppn Hfix HΨmid in
/-- release's `fence rw,w` at `relKf kr` (continuation `relKw kr`), over AxSpinRl1's shape. -/
theorem XxFenceRel (kr : Nat) (c : Bool)
    (pra ps0 ps1 plk pcl hra hs0 hs1 hram hs0m qra qs0 qmra qms0 pn pint : Int)
    (s : Athread) (rs : RegFile) (pc : BitVec 64) :
    RowRelease kr c (AxOpsem.grow (gtAdGd GT) i)
      pra ps0 ps1 plk pcl hra hs0 hs1 hram hs0m qra qs0 qmra qms0 pn pint →
    RetX cpu rs (relKf kr) s → ctrlOkSW T satp0 rs → rs .PC = pc → hitW rs pc →
    textOkB σi T satp0 pc false fenceRwW →
    ⊢ (∀ (rs' : RegFile) (ib' : Ibch), ⌜GoodB T satp0 rs pc false none none rs'⌝ -∗
        @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
          ⟨.PHart cpu (.pure ()) rs' none ib', relKw kr⟩ Ψ) -∗
      @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i s Ψ := by
  intro HR HRet Hc HPC Hhit Htx
  have Hlen := (rowReleaseLen HR).1
  exact XxFence L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu Hfix Ψ HΨmid s rs
    (relKf kr) pc HRet Hc HPC Hhit Htx (by simp only [relKe, relKr, relKp, relKf] at Hlen ⊢; omega)

include HL Hcons hmode hasid hppn Hfix HΨmid in
/-- release's `sd zero,16(s1)` at `relKc kr` (continuation `relKf kr`), over AxSpinRl1's
shape. -/
theorem XxSdCpuRel (kr : Nat) (c : Bool)
    (pra ps0 ps1 plk pcl hra hs0 hs1 hram hs0m qra qs0 qmra qms0 pn pint : Int)
    (s : Athread) (rs : RegFile) (pc : BitVec 64) (is_rvc : Bool) (imm : BitVec 12)
    (rs2 rs1 : BitVec 5) (va pa val : BitVec 64) (e : Geid) (P Q : IProp GF) :
    RowRelease kr c (AxOpsem.grow (gtAdGd GT) i)
      pra ps0 ps1 plk pcl hra hs0 hs1 hram hs0m qra qs0 qmra qms0 pn pint →
    RetX cpu rs (relKc kr) s → ctrlOkSW T satp0 rs → rs .PC = pc → hitW rs pc →
    textOkB σi T satp0 pc is_rvc (.STORE (imm, .Regidx rs2, .Regidx rs1, 8)) →
    va = gprVal rs rs1 + sign_extend (m := 64) imm →
    dataAtS σi T (.Store .Data) va 8 pa → hitW rs va → paZ pa = L.xlLk + 16 →
    gprVal rs rs2 = val →
    e.1 = i → CpuWin L GT i e →
    (⊢ P -∗ iprop(Q ∗ ∃ vold, RVL nm.xnH (gtAdGd GT) (clb L) e vold)) →
    ⊢ AxAnnot.annotOwn e P -∗
      (∀ (rs' : RegFile) (ib' : Ibch), ⌜GoodB T satp0 rs pc is_rvc none none rs'⌝ -∗
        ⌜graphData (gtAdGd GT) (i, relKc kr) = some (WeakInterpProj.wbytes 8 val) ∧
          ∃ cls, (AxOpsem.grow (gtAdGd GT) i)[relKc kr]? =
            some (.LStore false (L.xlLk + 16) (WeakInterpProj.wbytes 8 val) cls)⌝ -∗
        AxAnnot.annotOwn (i, relKc kr)
          iprop(Q ∗ RVL nm.xnH (gtAdGd GT) (clb L) (i, relKc kr) (WeakInterpProj.wbytes 8 val)) -∗
        @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
          ⟨.PHart cpu (.pure ()) rs' none ib', relKf kr⟩ Ψ) -∗
      @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i s Ψ := by
  intro HR HRet Hc HPC Hhit Htx Hva Hda Hhv Hpa Hval He Hwin HP
  have Hlen := (rowReleaseLen HR).1
  exact XxSdCpu L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu Hfix Ψ HΨmid s rs (relKc kr)
    pc is_rvc imm rs2 rs1 va pa val e P Q HRet Hc HPC Hhit Htx Hva Hda Hhv Hpa Hval He Hwin HP
    (by simp only [relKe, relKr, relKp, relKc] at Hlen ⊢; omega)

end sdcpu

/-- acquire's lk->cpu store item (`aqTail`'s index 4). -/
theorem rowAcquireCpu {k : Nat} {b hb : Bool} {n : Nat} {row : List Lbl}
    {pra ps0 ps1 qra qs0 qs1 qmra qms0 pn pint hra hs0 hs1 hram hs0m plk pcl mra ms0 : Int} :
    RowAcquire k b hb n row pra ps0 ps1 qra qs0 qs1 qmra qms0 pn pint hra hs0 hs1 hram hs0m plk
      pcl mra ms0 →
    ∃ vw cls, row[aqKm k b hb n + 4]? = some (.LStore false pcl vw cls) ∧ vw.length = 8 := by
  intro H
  obtain ⟨lb, Hlb, vw, cls, rfl, Hl⟩ := H.2.2.2.2.1 4 (.RS pcl 8) rfl
  exact ⟨vw, cls, Hlb, Hl⟩

section sdcpuAcq
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
variable (Ψ : Athread → IProp GF)
variable (HΨmid : ∀ s, midState s → s.atK = (AxOpsem.grow (gtAdGd GT) i).length →
  ⊢ @postLifting GF (AxSpinX2.xG L GT nm) Ψ i s)

include HL Hcons hmode hasid hppn Hfix HΨmid in
/-- acquire's `c.sd a0,16(s1)` at `aqKm … + 4` (continuation `+ 5`), over AxSpinAqr's shape. -/
theorem XxSdCpuAcq (ka : Nat) (b hb : Bool) (n : Nat)
    (pra ps0 ps1 qra qs0 qs1 qmra qms0 pn pint hra hs0 hs1 hram hs0m plk pcl mra ms0 : Int)
    (s : Athread) (rs : RegFile) (pc : BitVec 64) (is_rvc : Bool) (imm : BitVec 12)
    (rs2 rs1 : BitVec 5) (va pa val : BitVec 64) (e : Geid) (P Q : IProp GF) :
    RowAcquire ka b hb n (AxOpsem.grow (gtAdGd GT) i) pra ps0 ps1 qra qs0 qs1 qmra qms0 pn pint
      hra hs0 hs1 hram hs0m plk pcl mra ms0 →
    RetX cpu rs (aqKm ka b hb n + 4) s → ctrlOkSW T satp0 rs → rs .PC = pc → hitW rs pc →
    textOkB σi T satp0 pc is_rvc (.STORE (imm, .Regidx rs2, .Regidx rs1, 8)) →
    va = gprVal rs rs1 + sign_extend (m := 64) imm →
    dataAtS σi T (.Store .Data) va 8 pa → hitW rs va → paZ pa = L.xlLk + 16 →
    gprVal rs rs2 = val →
    e.1 = i → CpuWin L GT i e →
    (⊢ P -∗ iprop(Q ∗ ∃ vold, RVL nm.xnH (gtAdGd GT) (clb L) e vold)) →
    ⊢ AxAnnot.annotOwn e P -∗
      (∀ (rs' : RegFile) (ib' : Ibch), ⌜GoodB T satp0 rs pc is_rvc none none rs'⌝ -∗
        ⌜graphData (gtAdGd GT) (i, aqKm ka b hb n + 4) = some (WeakInterpProj.wbytes 8 val) ∧
          ∃ cls, (AxOpsem.grow (gtAdGd GT) i)[aqKm ka b hb n + 4]? =
            some (.LStore false (L.xlLk + 16) (WeakInterpProj.wbytes 8 val) cls)⌝ -∗
        AxAnnot.annotOwn (i, aqKm ka b hb n + 4)
          iprop(Q ∗ RVL nm.xnH (gtAdGd GT) (clb L) (i, aqKm ka b hb n + 4)
            (WeakInterpProj.wbytes 8 val)) -∗
        @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
          ⟨.PHart cpu (.pure ()) rs' none ib', aqKm ka b hb n + 5⟩ Ψ) -∗
      @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i s Ψ := by
  intro HR HRet Hc HPC Hhit Htx Hva Hda Hhv Hpa Hval He Hwin HP
  have Hlen := HR.2.2.2.2.2
  exact XxSdCpu L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu Hfix Ψ HΨmid s rs
    (aqKm ka b hb n + 4) pc is_rvc imm rs2 rs1 va pa val e P Q HRet Hc HPC Hhit Htx Hva Hda Hhv
    Hpa Hval He Hwin HP (by omega)

end sdcpuAcq

end Weak
