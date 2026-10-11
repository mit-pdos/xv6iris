/-
Weak: **THE BRIDGE `AxCert.Cert` ⇒ WPd** (the one certificate of `AxCert`), with the BARRIER
arm and the RMW arm.

Rocq: `iris/AxCert2.v` @ xxvzwolszwmp.

## The Rocq header, in substance

§1 pstep inversions at the new node kinds: `barrierPstep` (a `barrier` node emits
`ebarLabel bk`, parks `ebarPark bk`), `xreadPstep` (an `akLatest` RAM read emits `LExLoad`),
`xwritePstep` (an `akLatest` RAM write emits `LExStore` OR takes the silent RETRY SELF-LOOP).
Budget positions `AxCert2.bpos G i k b` (for `BFin n`: the row has exactly `n` items after `k`
under `G`), `bposSucc`.
§2 NODE LEMMAS (section `bridgeC`, premises = `AxSymEngine3`'s `G HG Hmid Htext Hflow` plus `Hloc`
and the data-region premises):
- `wpdFenceNodeM` — THE BARRIER ARM: `AStepFence` is the only step, one row item, NO flow (a fence
  event deposits no annotation: WPd clause (b)'s `none` arm is a skip step), `Hloc` advances the
  local interpretation;
- `wpdXrdNodeM` — the RMW ARM's read half: matched against the FUSED row item (`IRmw`,
  `aidentAdvRd = 0`) it is a skip step at the SAME row position, the value demonic (WPd pins it
  to `graphValue`); the SPLIT matching (a plain `IRead` row item at an RMW target) is refuted by
  `HnoSplit`;
- `wpdXwrNodeM` — the RMW ARM's write half: `AStepWrite` of the exclusive store (flow `FstM`, the
  row checks the bytes, one row item) OR the silent retry self-loop (Löb);
- `wpdDrdNodeM` / `wpdDwrNodeM` — EvD's data nodes restated with the EXACT next row position
  (`k + 1`; `AxSymMem`'s versions quantify it away, which the budget needs).
§3 THE BRIDGE `wpdOfCertM` / `wpdInstrOfCertM`: a `Cert` of the thread's tree at any state
agreeing off the pins with the thread's registers, with `CResM d` (the data event's flow resource)
and `bpos k b`, gives its WPd, with continuation at every `.pure ()` reached — the continuation
learns the final certificate state (data event, budget ⇒ exact row position, release flag).
Premises beyond `AxSymEngine3`'s (all instance-level): `Hloc` (the fence's local-interp advance);
`HnoRmw` (kind `DKLd` only): no fused RMW row item at a data-load address; `HnoSplit` (kind
`DKRmw` only): no plain `IRead` row item of hart `i` at an RMW-target address.  (Rocq's CONCERN,
kept: both are region side conditions; xv6's `holding()` plainly reads the lock word, so the
region form is too coarse for whole-kernel use; the positional fix is expressible in `BFin` mode.)

## Deviations from Rocq

1. O2 STAGE C (as `AxSymMem` deviation 1, `AxCert` deviation 1).  Rocq's section premise
   `Hntext` is DROPPED (Rocq used it only to refute `AStepFetch` at a data read; `Cert.cDrd`
   carries `akIfetch = false`, and `wpdDrdNodeM` takes it as `Hnf`).  `Hloc` is KEPT (the fence
   node needs it) — its only use is now the fence.  `Cert.cMrd` runs through
   `AxSymEngine3.wpdImgRead3M` (to `k + 1`), the Lean-only `Cert.cIf` through
   `AxSymEngine3.wpdImgFetch3M` (at `k`, budget kept); `cEnd` through `wpdStuckReadM` (`Hnf`).
   Lean's `astepProg` has three arms (no fetch arm), so the inversions have one case less.
   Section premises: `G HG Hmid Htext Hflow Hloc HnoRmw HnoSplit Out` after
   `M img dok kind i Φ cpu`.
2. LEAN-SAIL WRITE VALUES ARE `Option` (`AxSymMem` deviation 2): `wpdXwrNodeM` / `wpdDwrNodeM`
   take `v` with `req.value = some v` and hand `Out k (WeakInterpProj.wbytes n v)`; the store's
   answer is `.Ok (some true)` (Rocq `inl None`); `xwritePstep` returns that `v`.  Read answers
   are `.Ok (wordOfBytes n vs, none)`.
3. THE PINS (`AxRunClose` deviation 1): `regs_agree seip_reg` ↦ `regsAgree AxRunClose.pinReg`.
4. TYPES as `AxSymMem` deviation 4; `invGS_gen HasNoLc Σ` ↦ `[InvGS_gen hlc GF]` (any `hlc`).
   `CFkM`/`CResM` take their section variables explicitly (`CResM M dok kind i Out d`).  Rocq's
   `Definition … := …M rvwmo_cat_consistent` ↦ theorems typed `type_of% (…M
   rvwmoCatConsistent)`; the notations `CFk`/`CRes` ↦ abbrevs.
5. `ebar_label_fence` is NOT redeclared: it is `Weak.ebarLabelFence` (WeakEvInst, same
   statement).  Lean-only (file-qualified): `AxCert2.nfOfLatest` (an `akLatest` access is not a
   fetch), `AxCert2.barrierAstepInv`, `AxCert2.xreadAstepFalse`, `AxCert2.xwriteAstepInv`.
6. Q19 (provisional): the case of the Lean-only `Cert.cSf` (AxCert deviation 10) in
   `wpdOfCertM` is the Lean-only node lemma `AxCert2.wpdSfNodeM` — the twin of `wpdFenceNodeM`
   at an SFENCE.VMA announce node: `pnodeStep`'s announce arm emits `annLabel n w` = the marker
   `LFence false false false false` (`annLabelSf`) and banks the announced bits, so
   `AStepFence` is its only step (`AxCert2.sfAnnPstep`, `AxCert2.sfAnnAstepInv`), one row item,
   no flow, `Hloc` advancing the local interpretation; the continuation takes any `ib'`.
7. (Lean-only, Theorem 2 / P4) the case of the Lean-only `Cert.cWrEnd` (AxCert deviation 11) is
   the Lean-only `AxCert2.wpdStuckWriteM` (§2b) — the write twin of `wpdStuckReadM`: a plain
   RAM write at the row end has no step (`storeNodePstep`: its only program step is the store,
   whose `AStepWrite` needs a row item), so its post is `Hmid`'s (the write node is mid).

**Rocq → Lean name map.**  `ebar_label_fence` `ebarLabelFence` (existing), `barrier_pstep`
`barrierPstep`, `xread_pstep` `xreadPstep`, `xwrite_pstep` `xwritePstep`, `bpos` `AxCert2.bpos`
(duplicated with WeakRobustCone), `bpos_succ` `bposSucc`, `CFkM` `CFkM`, `CResM` `CResM`,
`wpd_fence_nodeM` `wpdFenceNodeM`, `wpd_xrd_nodeM` `wpdXrdNodeM`, `wpd_xwr_nodeM` `wpdXwrNodeM`,
`wpd_drd_nodeM` `wpdDrdNodeM`, `wpd_dwr_nodeM` `wpdDwrNodeM`, `wpd_of_CertM` `wpdOfCertM`,
`wpd_instr_of_CertM` `wpdInstrOfCertM`, and the riscv.cat instances `wpd_fence_node`
`wpdFenceNode`, `wpd_xrd_node` `wpdXrdNode`, `wpd_xwr_node` `wpdXwrNode`, `wpd_drd_node`
`wpdDrdNode`, `wpd_dwr_node` `wpdDwrNode`, `wpd_of_Cert` `wpdOfCert`, `wpd_instr_of_Cert`
`wpdInstrOfCert`, notations `CFk` `CFk`, `CRes` `CRes`.

**Dropped:** nothing (Rocq 22 definitions/lemmas + 2 notations; Lean 21 + `ebarLabelFence` reused,
+ 2 abbrevs, + 8 Lean-only).  The section premise `Hntext` is dropped (deviation 1).
**Not ported:** the Ltac `silent_psC` (↦ `AxSymEngine3.wpdSilentNode3M`) and the
`Print Assumptions` lines (the lint's axiom check covers them).
-/
import Weak.AxCert

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std Iris.Std.PartialMap MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D
open Wlabel

/-! # 1. pstep inversions at the new nodes -/

/-- (Lean-only) An `akLatest` (exclusive) access is not an instruction fetch. -/
theorem AxCert2.nfOfLatest (ak : AK) (h : (classify ak).akLatest = true) :
    (classify ak).akIfetch = false := by
  cases hf : (classify ak).akIfetch with
  | false => rfl
  | true =>
    have hx := akExcl_of_ifetch ak hf
    rw [classifyAkLatest, hx] at h
    exact absurd h Bool.false_ne_true

theorem barrierPstep (cpu : CPU) (bk : barrier_kind) (KK : Unit → SailM Unit) (rs : RegFile)
    (ib : Ibch) (d : Efab) (l : Wlabel) (p' : Pexv6) (d' : Efab) :
    pstepProg (.PHart cpu (.impure (.ok (.barrier bk)) KK) rs none ib) d l p' d' →
    l = ebarLabel bk ∧ p' = .PHart cpu (KK ()) rs (ebarPark bk) ib := by
  intro h
  cases p' with
  | PDisk _ => exact False.elim h
  | PHart c m' rs' fn' ib' =>
    obtain ⟨rfl, ors, oib, obar, rfl, rfl, hn, -⟩ := h
    simp only [pstepNode, pnodeStep] at hn
    obtain ⟨rfl, rfl, rfl, rfl, -, rfl, -⟩ := hn
    exact ⟨rfl, rfl⟩

theorem xreadPstep (cpu : CPU) (n va : Nat)
    (req : Mem_read_request n va Arch.pa Arch.translation Arch.arch_ak)
    (KK : Result (BitVec (8 * n) × Option Bool) Arch.abort → SailM Unit) (rs : RegFile)
    (ib : Ibch) (d : Efab) (l : Wlabel) (p' : Pexv6) (d' : Efab) :
    devAddr req.pa = false → (classify req.access_kind).akLatest = true →
    pstepProg (.PHart cpu (.impure (.ok (.memRead n va req)) KK) rs none ib) d l p' d' →
    ∃ tvs : List (Nat × BitVec 8), tvs.length = n ∧
      l = LExLoad (classify req.access_kind).akSync (paZ req.pa) tvs
            (depsAsrc (depsOfIb ib.ibBits)) ∧
      p' = .PHart cpu (KK (.Ok (wordOfBytes n (tvs.map Prod.snd), none))) rs none ib := by
  intro hdev hlat h
  cases p' with
  | PDisk _ => exact False.elim h
  | PHart c m' rs' fn' ib' =>
    obtain ⟨rfl, ors, oib, obar, rfl, rfl, hn, -⟩ := h
    simp only [pstepNode, pnodeStep, hdev, Bool.false_eq_true, ↓reduceIte] at hn
    rcases hn with ⟨hif, -⟩ | ⟨-, ⟨hl', -⟩ | ⟨-, w, tvs, hlen, hby, rfl, rfl, rfl, rfl, -, rfl, -⟩⟩
    · rw [AxCert2.nfOfLatest _ hlat] at hif
      exact absurd hif Bool.false_ne_true
    · rw [hlat] at hl'
      exact Bool.noConfusion hl'
    · refine ⟨tvs, hlen, rfl, ?_⟩
      rw [← bytesWordEq n w tvs hlen hby]
      rfl

theorem xwritePstep (cpu : CPU) (n va : Nat)
    (req : Mem_write_request n va Arch.pa Arch.translation Arch.arch_ak)
    (KK : Result (Option Bool) Arch.abort → SailM Unit) (rs : RegFile) (ib : Ibch) (d : Efab)
    (l : Wlabel) (p' : Pexv6) (d' : Efab) :
    devAddr req.pa = false → (classify req.access_kind).akLatest = true →
    pstepProg (.PHart cpu (.impure (.ok (.memWrite n va req)) KK) rs none ib) d l p' d' →
    ∃ v, req.value = some v ∧
      ((l = LExStore (classify req.access_kind).akSync (paZ req.pa) (WeakInterpProj.wbytes n v)
              (depsAsrc (depsOfIb ib.ibBits)) (depsVsrc (depsOfIb ib.ibBits)) ∧
          p' = .PHart cpu (KK (.Ok (some true))) rs none ib) ∨
       (l = LSilent ∧ p' = .PHart cpu (.impure (.ok (.memWrite n va req)) KK) rs none ib)) := by
  intro hdev hlat h
  cases p' with
  | PDisk _ => exact False.elim h
  | PHart c m' rs' fn' ib' =>
    obtain ⟨rfl, ors, oib, obar, rfl, rfl, hn, -⟩ := h
    simp only [pstepNode, pnodeStep, hdev, Bool.false_eq_true, ↓reduceIte] at hn
    cases hv : req.value with
    | none => simp only [hv] at hn
    | some v =>
      simp only [hv] at hn
      rcases hn with ⟨-, ⟨hl', -⟩ |
        ⟨-, ⟨rfl, rfl, rfl, rfl, -, rfl, -⟩ | ⟨rfl, rfl, rfl, rfl, -, rfl, -⟩⟩⟩
      · rw [hlat] at hl'
        exact Bool.noConfusion hl'
      · exact ⟨v, rfl, .inl ⟨rfl, rfl⟩⟩
      · exact ⟨v, rfl, .inr ⟨rfl, rfl⟩⟩

/-- (Lean-only) The only `astepProg` step of a `barrier` node: its `AStepFence`. -/
theorem AxCert2.barrierAstepInv (row : List Lbl) (cpu : CPU) (bk : barrier_kind)
    (KK : Unit → SailM Unit) (rs : RegFile) (ib : Ibch) (k : Nat) (l : Wlabel) (s' : Athread) :
    AxOpsem.astepProg row ⟨.PHart cpu (.impure (.ok (.barrier bk)) KK) rs none ib, k⟩ l s' →
    l = ebarLabel bk ∧ s' = ⟨.PHart cpu (KK ()) rs (ebarPark bk) ib, k + 1⟩ := by
  intro h
  obtain ⟨pr, pw, sr, sw, hlab⟩ := ebarLabelFence bk
  cases h with
  | AStepAdmin _ _ d _ p' d' hadm hps =>
    obtain ⟨rfl, -⟩ := barrierPstep cpu bk KK rs ib d l p' d' hps
    rw [hlab] at hadm
    exact (hadm : False).elim
  | AStepWrite _ _ d _ lb p' d' _ hsome _ _ hps =>
    obtain ⟨rfl, -⟩ := barrierPstep cpu bk KK rs ib d l p' d' hps
    rw [hlab] at hsome
    simp [wlWr] at hsome
  | AStepFence _ _ d _ lb p' d' _ _ _ hps =>
    obtain ⟨rfl, rfl⟩ := barrierPstep cpu bk KK rs ib d l p' d' hps
    exact ⟨rfl, rfl⟩

/-- (Lean-only, Q19) The program step of an SFENCE.VMA announce node: the marker label
`annLabel n w`, the announced bits banked. -/
theorem AxCert2.sfAnnPstep (cpu : CPU) (n : Nat) (w : BitVec n) (KK : Unit → SailM Unit)
    (rs : RegFile) (ib : Ibch) (d : Efab) (l : Wlabel) (p' : Pexv6) (d' : Efab) :
    pstepProg (.PHart cpu (.impure (.ok (.instrAnnounce n w)) KK) rs none ib) d l p' d' →
    l = annLabel n w ∧ p' = .PHart cpu (KK ()) rs none (ibAnn (ibOfBvn w)) := by
  intro h
  cases p' with
  | PDisk _ => exact False.elim h
  | PHart c m' rs' fn' ib' =>
    obtain ⟨rfl, ors, oib, obar, rfl, rfl, hn, -⟩ := h
    simp only [pstepNode, pnodeStep] at hn
    obtain ⟨rfl, rfl, rfl, rfl, -, rfl, -⟩ := hn
    exact ⟨rfl, rfl⟩

/-- (Lean-only, Q19) The only `astepProg` step of an SFENCE.VMA announce node: the
`AStepFence` of its marker `LFence false false false false`. -/
theorem AxCert2.sfAnnAstepInv (row : List Lbl) (cpu : CPU) (n : Nat) (w : BitVec n)
    (KK : Unit → SailM Unit) (rs : RegFile) (ib : Ibch) (k : Nat) (l : Wlabel) (s' : Athread)
    (Hsf : sfAnnB n w = true) :
    AxOpsem.astepProg row ⟨.PHart cpu (.impure (.ok (.instrAnnounce n w)) KK) rs none ib, k⟩ l s' →
    l = .LFence false false false false ∧
      s' = ⟨.PHart cpu (KK ()) rs none (ibAnn (ibOfBvn w)), k + 1⟩ := by
  intro h
  cases h with
  | AStepAdmin _ _ d _ p' d' hadm hps =>
    obtain ⟨rfl, -⟩ := AxCert2.sfAnnPstep cpu n w KK rs ib d l p' d' hps
    rw [annLabelSf Hsf] at hadm
    exact (hadm : False).elim
  | AStepWrite _ _ d _ lb p' d' _ hsome _ _ hps =>
    obtain ⟨rfl, -⟩ := AxCert2.sfAnnPstep cpu n w KK rs ib d l p' d' hps
    rw [annLabelSf Hsf] at hsome
    simp [wlWr] at hsome
  | AStepFence _ _ d _ lb p' d' _ _ _ hps =>
    obtain ⟨rfl, rfl⟩ := AxCert2.sfAnnPstep cpu n w KK rs ib d l p' d' hps
    exact ⟨annLabelSf Hsf, rfl⟩

/-- (Lean-only) No `astepProg` step at an exclusive RAM read node (only the read step). -/
theorem AxCert2.xreadAstepFalse (row : List Lbl) (cpu : CPU) (n va : Nat)
    (req : Mem_read_request n va Arch.pa Arch.translation Arch.arch_ak)
    (KK : Result (BitVec (8 * n) × Option Bool) Arch.abort → SailM Unit) (rs : RegFile)
    (ib : Ibch) (k : Nat) (l : Wlabel) (s' : Athread) :
    devAddr req.pa = false → (classify req.access_kind).akLatest = true →
    ¬ AxOpsem.astepProg row ⟨.PHart cpu (.impure (.ok (.memRead n va req)) KK) rs none ib, k⟩ l s' := by
  intro hdev hlat h
  obtain ⟨d, d', hps⟩ := astepProgPstep _ _ _ _ h
  obtain ⟨tvs, -, hl, -⟩ := xreadPstep cpu n va req KK rs ib d l _ d' hdev hlat hps
  subst hl
  cases h with
  | AStepAdmin _ _ _ _ _ _ hadm _ => exact hadm
  | AStepWrite _ _ _ _ _ _ _ _ hwr _ _ _ => simp [wlWr] at hwr
  | AStepFence _ _ _ _ _ _ _ _ hf _ _ => simp [wlFence] at hf

/-- (Lean-only) The `astepProg` steps of an exclusive RAM write node: the `AStepWrite` of its
`LExStore` (the row item's data checked), or the silent retry self-loop. -/
theorem AxCert2.xwriteAstepInv (row : List Lbl) (cpu : CPU) (n va : Nat)
    (req : Mem_write_request n va Arch.pa Arch.translation Arch.arch_ak)
    (KK : Result (Option Bool) Arch.abort → SailM Unit) (rs : RegFile) (ib : Ibch) (k : Nat)
    (l : Wlabel) (s' : Athread) :
    devAddr req.pa = false → (classify req.access_kind).akLatest = true →
    AxOpsem.astepProg row ⟨.PHart cpu (.impure (.ok (.memWrite n va req)) KK) rs none ib, k⟩ l s' →
    ∃ v, req.value = some v ∧
      ((∃ lb, row[k]? = some lb ∧ wlWr l = aidentWr (aident lb) ∧ wlWdata l = lblData lb ∧
          l = LExStore (classify req.access_kind).akSync (paZ req.pa) (WeakInterpProj.wbytes n v)
              (depsAsrc (depsOfIb ib.ibBits)) (depsVsrc (depsOfIb ib.ibBits)) ∧
          s' = ⟨.PHart cpu (KK (.Ok (some true))) rs none ib, k + 1⟩) ∨
       (l = LSilent ∧ s' = ⟨.PHart cpu (.impure (.ok (.memWrite n va req)) KK) rs none ib, k⟩)) := by
  intro hdev hlat h
  cases h with
  | AStepAdmin _ _ d _ p' d' hadm hps =>
    obtain ⟨v, hv, ⟨rfl, -⟩ | ⟨rfl, rfl⟩⟩ := xwritePstep cpu n va req KK rs ib d l p' d' hdev hlat hps
    · exact (hadm : False).elim
    · exact ⟨v, hv, .inr ⟨rfl, rfl⟩⟩
  | AStepWrite _ _ d _ lb p' d' hrow hsome hwr hwd hps =>
    obtain ⟨v, hv, ⟨hl, rfl⟩ | ⟨rfl, -⟩⟩ := xwritePstep cpu n va req KK rs ib d l p' d' hdev hlat hps
    · exact ⟨v, hv, .inl ⟨lb, hrow, hwr, hwd, hl, rfl⟩⟩
    · simp [wlWr] at hsome
  | AStepFence _ _ d _ lb p' d' _ hf _ hps =>
    obtain ⟨v, -, ⟨rfl, -⟩ | ⟨rfl, -⟩⟩ := xwritePstep cpu n va req KK rs ib d l p' d' hdev hlat hps
    · simp [wlFence] at hf
    · simp [wlFence] at hf

/-- Budget positions. -/
def AxCert2.bpos (G : Gdexec → Prop) (i : Agent) (k : Nat) (b : Bud) : Prop :=
  match b with
  | .BInf => True
  | .BFin n => ∀ GD, G GD → (AxOpsem.grow GD i).length = k + n

theorem bposSucc (G : Gdexec → Prop) (i : Agent) (k : Nat) (b : Bud) :
    AxCert2.bpos G i k (bsucc b) → AxCert2.bpos G i (k + 1) b := by
  cases b with
  | BInf => intro _; trivial
  | BFin n =>
    simp only [AxCert2.bpos, bsucc]
    intro H GD HG
    rw [H GD HG]
    omega

/-! # 2. Node lemmas -/

section bridgeDefs
variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF] [Axpol]

/-- The data event's resource while it is pending. -/
def CFkM (M : Gdexec → Prop) (dok : Int → Nat → Prop) (kind : Dkind) (i : Agent)
    (Out : Nat → List (BitVec 8) → IProp GF) : IProp GF :=
  match kind with
  | .DKLd => FldM M dok i Out
  | _ => FstM M dok i Out

/-- The data event's resource at each certificate data state. -/
def CResM (M : Gdexec → Prop) (dok : Int → Nat → Prop) (kind : Dkind) (i : Agent)
    (Out : Nat → List (BitVec 8) → IProp GF) (d : Cdata) : IProp GF :=
  match d with
  | .CPend => CFkM M dok kind i Out
  | .CRmwR _ _ => FstM M dok i Out
  | .CLd vs | .CSt vs _ | .CRmw _ _ _ vs _ => iprop(∃ k, Out k vs)

end bridgeDefs

section bridgeC
variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF] [Axpol]
variable (M : Gdexec → Prop)
variable (img : Image) (dok : Int → Nat → Prop) (kind : Dkind)
variable (i : Agent) (Φ : Athread → IProp GF) (cpu : CPU)
variable (G : Gdexec → Prop) (HG : ∀ GD, M GD → AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜G GD⌝)
variable (Hmid : ∀ GD s, G GD → midState s → s.atK = (AxOpsem.grow GD i).length →
  ⊢ postLifting Φ i s)
variable (Htext : ∀ GD, M GD →
  AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜textFixed GD i img⌝)
variable (Hflow : ∀ GD ls k, M GD →
  (∃ lb aq base n vs, (AxOpsem.grow GD i)[k]? = some lb ∧ aident lb = .IRead aq base n ∧
     imgBytes img base n = some vs) →
  AxirisG.gconstInterp (GF := GF) GD ∗ AxirisG.localInterp GD i k ls ⊢ fetchFlow GD i k)
variable (Hloc : ∀ GD ls k, M GD →
  AxirisG.gconstInterp (GF := GF) GD ∗ AxirisG.localInterp GD i k ls ⊢
    |==> ∃ ls', AxirisG.localInterp GD i (k + 1) ls')
variable (HnoRmw : kind = .DKLd → ∀ GD, M GD → AxirisG.gconstInterp (GF := GF) GD ⊢
  ⌜∀ (k : Nat) (lb : Lbl) (aq rl : Bool) (base : Int) (n : Nat),
    (AxOpsem.grow GD i)[k]? = some lb → aident lb = .IRmw aq rl base n → ¬ dok base n⌝)
variable (HnoSplit : kind = .DKRmw → ∀ GD, M GD → AxirisG.gconstInterp (GF := GF) GD ⊢
  ⌜∀ (k : Nat) (lb : Lbl) (aq : Bool) (base : Int) (n : Nat),
    (AxOpsem.grow GD i)[k]? = some lb → aident lb = .IRead aq base n → ¬ dok base n⌝)
variable (Out : Nat → List (BitVec 8) → IProp GF)

include HG Hmid Hloc in
/-- THE BARRIER ARM. -/
theorem wpdFenceNodeM (bk : barrier_kind) (KK : Unit → SailM Unit) (ib : Ibch) (k : Nat)
    (A : RegFile → Prop)
    (HA : ∀ rs rs', A rs → regsAgree AxRunClose.pinReg rs' rs → A rs')
    (Hpark : ebarPark bk = none) :
    ⊢ ∀ rs, ⌜A rs⌝ -∗
      (∀ rs', ⌜A rs'⌝ -∗ wpdM M .MaybeStuck i ⟨.PHart cpu (KK ()) rs' none ib, k + 1⟩ Φ) -∗
      wpdM M .MaybeStuck i ⟨.PHart cpu (.impure (.ok (.barrier bk)) KK) rs none ib, k⟩ Φ := by
  obtain ⟨pr, pw, sr, sw, Hlab⟩ := ebarLabelFence bk
  iloeb as IH
  iintro %rs %HP C
  iapply (AxWpD.wpdMUnfoldStep M .MaybeStuck i _ Φ).2
  isplit
  · iapply (progressOblMaybestuck (GF := GF) i _).2
    itrivial
  unfold wpdMPreStepDef
  iintro %GD %ls ⟨%Hc, #Hg, Hloc⟩
  ihave HGD := (HG GD Hc) $$ Hg
  icases HGD with %HGD
  isplit
  · -- (a) no read at a barrier node
    iintro %id %K %Hst
    have hfalse : False := by
      obtain ⟨lb, -, -, Hsome, HK⟩ := Hst
      obtain ⟨l, d, d', Hrd, -, Hps, -⟩ := HK (List.replicate (aidentN id) 0) List.length_replicate
      obtain ⟨rfl, -⟩ := barrierPstep cpu bk KK rs ib d l _ d' Hps
      rw [Hlab] at Hrd
      simp only [wlRd] at Hrd
      simp [← Hrd] at Hsome
    exact hfalse.elim
  isplit
  · -- (b) THE FENCE: one row item, no flow
    iintro %l %s' %Hst %Hpin
    obtain ⟨rfl, rfl⟩ := AxCert2.barrierAstepInv _ cpu bk KK rs ib k l s' Hst
    rw [Hlab, Hpark]
    simp only [wlWdata]
    unfold wpSkipStep
    iintro %na Hna
    ihave Hl := (BI.wand_intro (Hloc GD ls k Hc)) $$ Hg Hloc
    imod Hl with ⟨%ls', Hl⟩
    imodintro
    inext
    imodintro
    iexists ls'
    iframe Hna Hl
    iapply C $$ %rs %HP
  isplit
  · -- (c) the PLIC wire
    iintro %s' %Hw
    obtain ⟨hk, hp⟩ := awireAeqv _ _ Hw
    obtain ⟨p', k'⟩ := s'
    simp only at hk hp
    subst hk
    match p', hp with
    | .PHart c m' rs' fn' ib', hp =>
      obtain ⟨rfl, rfl, rfl, rfl, hag⟩ := hp
      unfold wpSkipStep
      iintro %na Hna
      imodintro
      inext
      imodintro
      iexists ls
      iframe Hna Hloc
      iapply IH $$ %rs' %(HA rs rs' HP hag) C
  · -- (d) row end: a mid-instruction state
    iintro %Heq
    iapply (Hmid GD _ HGD (by exact trivial) Heq)

include HG Hmid Hloc in
/-- (Lean-only, Q19) THE SFENCE.VMA ANNOUNCE ARM (twin of `wpdFenceNodeM`): the marker
`LFence false false false false` is the only step, one row item, no flow. -/
theorem AxCert2.wpdSfNodeM (n : Nat) (w : BitVec n) (KK : Unit → SailM Unit) (ib : Ibch)
    (k : Nat) (A : RegFile → Prop)
    (HA : ∀ rs rs', A rs → regsAgree AxRunClose.pinReg rs' rs → A rs')
    (Hsf : sfAnnB n w = true) :
    ⊢ ∀ rs, ⌜A rs⌝ -∗
      (∀ rs' ib', ⌜A rs'⌝ -∗ wpdM M .MaybeStuck i ⟨.PHart cpu (KK ()) rs' none ib', k + 1⟩ Φ) -∗
      wpdM M .MaybeStuck i ⟨.PHart cpu (.impure (.ok (.instrAnnounce n w)) KK) rs none ib, k⟩ Φ := by
  iloeb as IH
  iintro %rs %HP C
  iapply (AxWpD.wpdMUnfoldStep M .MaybeStuck i _ Φ).2
  isplit
  · iapply (progressOblMaybestuck (GF := GF) i _).2
    itrivial
  unfold wpdMPreStepDef
  iintro %GD %ls ⟨%Hc, #Hg, Hloc⟩
  ihave HGD := (HG GD Hc) $$ Hg
  icases HGD with %HGD
  isplit
  · -- (a) no read at the marker
    iintro %id %K %Hst
    have hfalse : False := by
      obtain ⟨lb, -, -, Hsome, HK⟩ := Hst
      obtain ⟨l, d, d', Hrd, -, Hps, -⟩ := HK (List.replicate (aidentN id) 0) List.length_replicate
      obtain ⟨rfl, -⟩ := AxCert2.sfAnnPstep cpu n w KK rs ib d l _ d' Hps
      rw [annLabelSf Hsf] at Hrd
      simp only [wlRd] at Hrd
      simp [← Hrd] at Hsome
    exact hfalse.elim
  isplit
  · -- (b) THE MARKER: one row item, no flow
    iintro %l %s' %Hst %Hpin
    obtain ⟨rfl, rfl⟩ := AxCert2.sfAnnAstepInv _ cpu n w KK rs ib k l s' Hsf Hst
    simp only [wlWdata]
    unfold wpSkipStep
    iintro %na Hna
    ihave Hl := (BI.wand_intro (Hloc GD ls k Hc)) $$ Hg Hloc
    imod Hl with ⟨%ls', Hl⟩
    imodintro
    inext
    imodintro
    iexists ls'
    iframe Hna Hl
    iapply C $$ %rs %_ %HP
  isplit
  · -- (c) the PLIC wire
    iintro %s' %Hw
    obtain ⟨hk, hp⟩ := awireAeqv _ _ Hw
    obtain ⟨p', k'⟩ := s'
    simp only at hk hp
    subst hk
    match p', hp with
    | .PHart c m' rs' fn' ib', hp =>
      obtain ⟨rfl, rfl, rfl, rfl, hag⟩ := hp
      unfold wpSkipStep
      iintro %na Hna
      imodintro
      inext
      imodintro
      iexists ls
      iframe Hna Hloc
      iapply IH $$ %rs' %(HA rs rs' HP hag) C
  · -- (d) row end: a mid-instruction state
    iintro %Heq
    iapply (Hmid GD _ HGD (by exact trivial) Heq)

include HG Hmid HnoSplit in
/-- THE RMW ARM, read half. -/
theorem wpdXrdNodeM (n va : Nat)
    (req : Mem_read_request n va Arch.pa Arch.translation Arch.arch_ak)
    (KK : Result (BitVec (8 * n) × Option Bool) Arch.abort → SailM Unit) (ib : Ibch) (k : Nat)
    (A : RegFile → Prop)
    (HA : ∀ rs rs', A rs → regsAgree AxRunClose.pinReg rs' rs → A rs')
    (Hkind : kind = .DKRmw)
    (Hdev : devAddr req.pa = false) (Hlat : (classify req.access_kind).akLatest = true)
    (Hdok : dok (paZ req.pa) n) :
    ⊢ ∀ rs, ⌜A rs⌝ -∗
      (∀ (vs : List (BitVec 8)) (rs' : RegFile), ⌜vs.length = n⌝ -∗ ⌜A rs'⌝ -∗
         wpdM M .MaybeStuck i ⟨.PHart cpu (KK (.Ok (wordOfBytes n vs, none))) rs' none ib, k⟩ Φ) -∗
      wpdM M .MaybeStuck i ⟨.PHart cpu (.impure (.ok (.memRead n va req)) KK) rs none ib, k⟩ Φ := by
  iloeb as IH
  iintro %rs %HP C
  iapply (AxWpD.wpdMUnfoldStep M .MaybeStuck i _ Φ).2
  isplit
  · iapply (progressOblMaybestuck (GF := GF) i _).2
    itrivial
  unfold wpdMPreStepDef
  iintro %GD %ls ⟨%Hc, #Hg, Hloc⟩
  ihave HGD := (HG GD Hc) $$ Hg
  icases HGD with %HGD
  ihave Hns := (HnoSplit Hkind GD Hc) $$ Hg
  icases Hns with %Hns
  isplit
  · -- (a) the exclusive read
    iintro %id %K %Hst
    obtain ⟨lb, Hlb, Hid, -, HK⟩ := Hst
    simp only at Hlb
    subst Hid
    obtain ⟨l0, d0, d0', Hl0, -, Hps0, -⟩ :=
      HK (List.replicate (aidentN (aident lb)) 0) List.length_replicate
    obtain ⟨tvs0, Htl0, rfl, -⟩ := xreadPstep cpu n va req KK rs ib d0 _ _ d0' Hdev Hlat Hps0
    simp only [wlRd, Htl0] at Hl0
    -- the SPLIT matching (a plain `IRead` row item) is refuted
    have Had : aidentAdvRd (aident lb) = 0 := by
      cases hid : aident lb with
      | IRead aq base n' =>
        exfalso
        rw [hid] at Hl0
        simp only [aidentRd, Option.some.injEq, Prod.mk.injEq] at Hl0
        obtain ⟨-, hb, hn⟩ := Hl0
        subst hb
        subst hn
        exact Hns k lb aq _ _ Hlb hid Hdok
      | IRmw _ _ _ _ => rfl
      | IWrite _ _ _ =>
        rw [hid] at Hl0
        simp [aidentRd] at Hl0
      | IFence _ _ _ _ =>
        rw [hid] at Hl0
        simp [aidentRd] at Hl0
      | IIo _ _ _ =>
        rw [hid] at Hl0
        simp [aidentRd] at Hl0
    simp only [Had, Nat.zero_ne_one, ↓reduceIte]
    -- the FUSED matching: a skip step at the same position
    iintro %v %Hv %Hlenv
    obtain ⟨l, d, d', -, Hrv, Hps, Hk'⟩ := HK v Hlenv
    obtain ⟨tvs, Htl, rfl, Hp'⟩ := xreadPstep cpu n va req KK rs ib d _ _ d' Hdev Hlat Hps
    simp only [wlRvals] at Hrv
    subst Hrv
    rw [Had] at Hk'
    have hKv : K (tvs.map Prod.snd) =
        ⟨.PHart cpu (KK (.Ok (wordOfBytes n (tvs.map Prod.snd), none))) rs none ib, k⟩ := by
      cases hK : K (tvs.map Prod.snd) with
      | AThread p' k' =>
        rw [hK] at Hp' Hk'
        simp only [Nat.add_zero] at Hp' Hk'
        rw [Hp', Hk']
    rw [hKv]
    unfold wpSkipStep
    iintro %na Hna
    imodintro
    inext
    imodintro
    iexists ls
    iframe Hna Hloc
    iapply C $$ %(tvs.map Prod.snd) %rs
    · ipureintro
      rw [List.length_map]
      exact Htl
    · ipureintro
      exact HP
  isplit
  · -- (b) no program step at an exclusive read
    iintro %l %s' %Hst %Hpin
    exact (AxCert2.xreadAstepFalse _ cpu n va req KK rs ib k l s' Hdev Hlat Hst).elim
  isplit
  · -- (c) the PLIC wire
    iintro %s' %Hw
    obtain ⟨hk, hp⟩ := awireAeqv _ _ Hw
    obtain ⟨p', k'⟩ := s'
    simp only at hk hp
    subst hk
    match p', hp with
    | .PHart c m' rs' fn' ib', hp =>
      obtain ⟨rfl, rfl, rfl, rfl, hag⟩ := hp
      unfold wpSkipStep
      iintro %na Hna
      imodintro
      inext
      imodintro
      iexists ls
      iframe Hna Hloc
      iapply IH $$ %rs' %(HA rs rs' HP hag) C
  · iintro %Heq
    iapply (Hmid GD _ HGD (by exact trivial) Heq)

include HG Hmid in
/-- THE RMW ARM, write half (the exclusive store, or its retry loop). -/
theorem wpdXwrNodeM (n va : Nat)
    (req : Mem_write_request n va Arch.pa Arch.translation Arch.arch_ak)
    (KK : Result (Option Bool) Arch.abort → SailM Unit) (ib : Ibch) (k : Nat) (v : BitVec (8 * n))
    (A : RegFile → Prop)
    (HA : ∀ rs rs', A rs → regsAgree AxRunClose.pinReg rs' rs → A rs')
    (Hdev : devAddr req.pa = false) (Hlat : (classify req.access_kind).akLatest = true)
    (Hval : req.value = some v)
    (Hdok : dok (paZ req.pa) n) :
    ⊢ ∀ rs, ⌜A rs⌝ -∗ FstM M dok i Out -∗
      (∀ rs', ⌜A rs'⌝ -∗ Out k (WeakInterpProj.wbytes n v) -∗
         wpdM M .MaybeStuck i ⟨.PHart cpu (KK (.Ok (some true))) rs' none ib, k + 1⟩ Φ) -∗
      wpdM M .MaybeStuck i ⟨.PHart cpu (.impure (.ok (.memWrite n va req)) KK) rs none ib, k⟩ Φ := by
  unfold FstM dflowO
  iloeb as IH
  iintro %rs %HP F C
  iapply (AxWpD.wpdMUnfoldStep M .MaybeStuck i _ Φ).2
  isplit
  · iapply (progressOblMaybestuck (GF := GF) i _).2
    itrivial
  unfold wpdMPreStepDef
  iintro %GD %ls ⟨%Hc, #Hg, Hloc⟩
  ihave HGD := (HG GD Hc) $$ Hg
  icases HGD with %HGD
  isplit
  · -- (a) no read at a write node
    iintro %id %K %Hst
    have hfalse : False := by
      obtain ⟨lb, -, -, Hsome, HK⟩ := Hst
      obtain ⟨l, d, d', Hrd, -, Hps, -⟩ := HK (List.replicate (aidentN id) 0) List.length_replicate
      obtain ⟨v', -, ⟨rfl, -⟩ | ⟨rfl, -⟩⟩ := xwritePstep cpu n va req KK rs ib d l _ d' Hdev Hlat Hps
      · simp only [wlRd] at Hrd
        simp [← Hrd] at Hsome
      · simp only [wlRd] at Hrd
        simp [← Hrd] at Hsome
    exact hfalse.elim
  isplit
  · -- (b) THE EXCLUSIVE STORE, or the retry self-loop
    iintro %l %s' %Hst %Hpin
    obtain ⟨v', hv', hcase⟩ := AxCert2.xwriteAstepInv _ cpu n va req KK rs ib k l s' Hdev Hlat Hst
    have hvv : v' = v := by
      rw [Hval] at hv'
      exact (Option.some.inj hv').symm
    subst hvv
    rcases hcase with ⟨lb, hrow, hwr, hwd, hl, hs'⟩ | ⟨hl, hs'⟩
    · have Hgd : graphData GD (i, k) = some (WeakInterpProj.wbytes n v') ∧
          rowWr i GD k (paZ req.pa) (WeakInterpProj.wbytes n v').length := by
        rw [hl] at hwr hwd
        simp only [wlWr] at hwr
        simp only [wlWdata] at hwd
        refine ⟨?_, lb, _, hrow, hwr.symm⟩
        unfold graphData
        rw [AxWp.growLookup _ _ _ _ hrow, Option.bind_some, ← hwd]
      rw [hl, hs']
      simp only [wlWdata]
      unfold wpEvStep
      iintro %na Hpg
      ihave Hf := F $$ %GD %ls %k %(WeakInterpProj.wbytes n v') %(paZ req.pa) %n %Hc Hg Hloc
        %Hgd.1 %⟨Hdok, Hgd.2⟩
      imod Hf $$ %na Hpg with Hf
      imodintro
      inext
      imod Hf with ⟨%R, %nu, %nuu, %ls', Hs, Hfe, Hna, Hl, HO⟩
      imodintro
      iexists (), R, nu, nuu, ls'
      isplitr
      · ipureintro
        trivial
      iframe Hs Hna Hl
      isplitl [Hfe]
      · iapply (flowEqDynMono GD (i, k) _ nu R
          iprop(R ∗ ⌜graphData GD (i, k) = some (WeakInterpProj.wbytes n v')⌝))
        · inext
          iintro HR
          iframe HR
          ipureintro
          exact Hgd.1
        · iexact Hfe
      · iapply C $$ %rs
        · ipureintro
          exact HP
        · iexact HO
    · -- the retry self-loop
      rw [hl, hs']
      simp only [wlWdata]
      unfold wpSkipStep
      iintro %na Hna
      imodintro
      inext
      imodintro
      iexists ls
      iframe Hna Hloc
      iapply IH $$ %rs %HP F C
  isplit
  · -- (c) the PLIC wire
    iintro %s' %Hw
    obtain ⟨hk, hp⟩ := awireAeqv _ _ Hw
    obtain ⟨p', k'⟩ := s'
    simp only at hk hp
    subst hk
    match p', hp with
    | .PHart c m' rs' fn' ib', hp =>
      obtain ⟨rfl, rfl, rfl, rfl, hag⟩ := hp
      unfold wpSkipStep
      iintro %na Hna
      imodintro
      inext
      imodintro
      iexists ls
      iframe Hna Hloc
      iapply IH $$ %rs' %(HA rs rs' HP hag) F C
  · iintro %Heq
    iapply (Hmid GD _ HGD (by exact trivial) Heq)

include HG Hmid HnoRmw in
/-- EvD's data read, exact next position (deviation 1: `Hnf`). -/
theorem wpdDrdNodeM (n va : Nat)
    (req : Mem_read_request n va Arch.pa Arch.translation Arch.arch_ak)
    (KK : Result (BitVec (8 * n) × Option Bool) Arch.abort → SailM Unit) (ib : Ibch) (k : Nat)
    (A : RegFile → Prop)
    (HA : ∀ rs rs', A rs → regsAgree AxRunClose.pinReg rs' rs → A rs')
    (Hkind : kind = .DKLd)
    (Hdev : devAddr req.pa = false) (Hlat : (classify req.access_kind).akLatest = false)
    (Hnf : (classify req.access_kind).akIfetch = false)
    (Hdok : dok (paZ req.pa) n) :
    ⊢ ∀ rs, ⌜A rs⌝ -∗ FldM M dok i Out -∗
      (∀ (vs : List (BitVec 8)) (rs' : RegFile), ⌜vs.length = n⌝ -∗ ⌜A rs'⌝ -∗ Out k vs -∗
         wpdM M .MaybeStuck i ⟨.PHart cpu (KK (.Ok (wordOfBytes n vs, none))) rs' none ib, k + 1⟩ Φ) -∗
      wpdM M .MaybeStuck i ⟨.PHart cpu (.impure (.ok (.memRead n va req)) KK) rs none ib, k⟩ Φ := by
  unfold FldM dflowO
  iloeb as IH
  iintro %rs %HP F C
  iapply (AxWpD.wpdMUnfoldStep M .MaybeStuck i _ Φ).2
  isplit
  · iapply (progressOblMaybestuck (GF := GF) i _).2
    itrivial
  unfold wpdMPreStepDef
  iintro %GD %ls ⟨%Hc, #Hg, Hloc⟩
  ihave HGD := (HG GD Hc) $$ Hg
  icases HGD with %HGD
  ihave Hnr := (HnoRmw Hkind GD Hc) $$ Hg
  icases Hnr with %Hnr
  isplit
  · -- (a) THE DATA READ, demonic
    iintro %id %K %Hst
    obtain ⟨lb, Hlb, Hid, -, HK⟩ := Hst
    simp only at Hlb
    subst Hid
    obtain ⟨l0, d0, d0', Hl0, -, Hps0, -⟩ :=
      HK (List.replicate (aidentN (aident lb)) 0) List.length_replicate
    obtain ⟨tvs0, Htl0, rfl, -⟩ :=
      AxLdspWpd.loadStepInv cpu n va req KK rs ib d0 _ _ d0' Hdev Hlat Hnf Hps0
    simp only [wlRd, Htl0] at Hl0
    have Hadv0 : aidentAdvRd (aident lb) = 1 := by
      cases hid : aident lb with
      | IRmw aq rl base n' =>
        exfalso
        rw [hid] at Hl0
        simp only [aidentRd, Option.some.injEq, Prod.mk.injEq] at Hl0
        obtain ⟨-, hb, hn⟩ := Hl0
        subst hb
        subst hn
        exact Hnr k lb aq rl _ _ Hlb hid Hdok
      | IRead _ _ _ => rfl
      | IWrite _ _ _ => rfl
      | IFence _ _ _ _ => rfl
      | IIo _ _ _ => rfl
    simp only [Hadv0, ↓reduceIte]
    iintro %v %Hv %Hlenv
    obtain ⟨l, d, d', -, Hrv, Hps, Hk'⟩ := HK v Hlenv
    obtain ⟨tvs, Htl, rfl, Hp'⟩ :=
      AxLdspWpd.loadStepInv cpu n va req KK rs ib d _ _ d' Hdev Hlat Hnf Hps
    simp only [wlRvals] at Hrv
    subst Hrv
    rw [Hadv0] at Hk'
    have hKv : K (tvs.map Prod.snd) =
        ⟨.PHart cpu (KK (.Ok (wordOfBytes n (tvs.map Prod.snd), none))) rs none ib, k + 1⟩ := by
      cases hK : K (tvs.map Prod.snd) with
      | AThread p' k' =>
        rw [hK] at Hp' Hk'
        simp only at Hp' Hk'
        rw [Hp', Hk']
    rw [hKv]
    unfold wpEvStep
    iintro %na Hpg
    ihave Hf := F $$ %GD %ls %k %(tvs.map Prod.snd) %(paZ req.pa) %n %Hc Hg Hloc %Hv
      %⟨Hdok, lb, _, Hlb, Hl0.symm⟩
    imod Hf $$ %na Hpg with Hf
    imodintro
    inext
    imod Hf with ⟨%R, %nu, %nuu, %ls', Hs, Hfe, Hna, Hl, HO⟩
    imodintro
    iexists (), R, nu, nuu, ls'
    isplitr
    · ipureintro
      trivial
    iframe Hs Hna Hl
    isplitl [Hfe]
    · iapply (flowEqDynMono GD (i, k) _ nu R
        iprop(R ∗ ⌜graphValue GD (i, k) = some (tvs.map Prod.snd)⌝))
      · inext
        iintro HR
        iframe HR
        ipureintro
        exact Hv
      · iexact Hfe
    · iapply C $$ %(tvs.map Prod.snd) %rs
      · ipureintro
        rw [List.length_map]
        exact Htl
      · ipureintro
        exact HP
      · iexact HO
  isplit
  · -- (b) no program step at a data read (`akIfetch = false`: no admin fetch)
    iintro %l %s' %Hst %Hpin
    have hfalse : False := by
      obtain ⟨d, d', hps⟩ := astepProgPstep _ _ _ _ Hst
      obtain ⟨tvs, -, hl, -⟩ :=
        AxLdspWpd.loadStepInv cpu n va req KK rs ib d l _ d' Hdev Hlat Hnf hps
      subst hl
      cases Hst with
      | AStepAdmin _ _ _ _ _ _ hadm _ => exact hadm
      | AStepWrite _ _ _ _ _ _ _ _ hwr _ _ _ => simp [wlWr] at hwr
      | AStepFence _ _ _ _ _ _ _ _ hf _ _ => simp [wlFence] at hf
    exact hfalse.elim
  isplit
  · -- (c) the PLIC wire
    iintro %s' %Hw
    obtain ⟨hk, hp⟩ := awireAeqv _ _ Hw
    obtain ⟨p', k'⟩ := s'
    simp only at hk hp
    subst hk
    match p', hp with
    | .PHart c m' rs' fn' ib', hp =>
      obtain ⟨rfl, rfl, rfl, rfl, hag⟩ := hp
      unfold wpSkipStep
      iintro %na Hna
      imodintro
      inext
      imodintro
      iexists ls
      iframe Hna Hloc
      iapply IH $$ %rs' %(HA rs rs' HP hag) F C
  · iintro %Heq
    iapply (Hmid GD _ HGD (by exact trivial) Heq)

include HG Hmid in
/-- EvD's data write, exact next position. -/
theorem wpdDwrNodeM (n va : Nat)
    (req : Mem_write_request n va Arch.pa Arch.translation Arch.arch_ak)
    (KK : Result (Option Bool) Arch.abort → SailM Unit) (ib : Ibch) (k : Nat) (v : BitVec (8 * n))
    (A : RegFile → Prop)
    (HA : ∀ rs rs', A rs → regsAgree AxRunClose.pinReg rs' rs → A rs')
    (Hdev : devAddr req.pa = false) (Hlat : (classify req.access_kind).akLatest = false)
    (Hval : req.value = some v)
    (Hdok : dok (paZ req.pa) n) :
    ⊢ ∀ rs, ⌜A rs⌝ -∗ FstM M dok i Out -∗
      (∀ rs', ⌜A rs'⌝ -∗ Out k (WeakInterpProj.wbytes n v) -∗
         wpdM M .MaybeStuck i ⟨.PHart cpu (KK (.Ok (some true))) rs' none ib, k + 1⟩ Φ) -∗
      wpdM M .MaybeStuck i ⟨.PHart cpu (.impure (.ok (.memWrite n va req)) KK) rs none ib, k⟩ Φ := by
  unfold FstM dflowO
  iloeb as IH
  iintro %rs %HP F C
  iapply (AxWpD.wpdMUnfoldStep M .MaybeStuck i _ Φ).2
  isplit
  · iapply (progressOblMaybestuck (GF := GF) i _).2
    itrivial
  unfold wpdMPreStepDef
  iintro %GD %ls ⟨%Hc, #Hg, Hloc⟩
  ihave HGD := (HG GD Hc) $$ Hg
  icases HGD with %HGD
  isplit
  · -- (a) no read at a store node
    iintro %id %K %Hst
    exact (AxEpiLedgerSd.storeNoRead _ cpu n va req KK rs ib k id K Hdev Hlat Hst).elim
  isplit
  · -- (b) THE WRITE
    iintro %l %s' %Hst %Hpin
    obtain ⟨v', hv', hl, hs'⟩ :=
      AxEpiLedgerSd.storeAstepInv _ cpu n va req KK rs ib k l s' Hdev Hlat Hst
    have hvv : v' = v := by
      rw [Hval] at hv'
      exact (Option.some.inj hv').symm
    subst hvv
    have Hgd : graphData GD (i, k) = some (WeakInterpProj.wbytes n v') ∧
        rowWr i GD k (paZ req.pa) (WeakInterpProj.wbytes n v').length := by
      cases Hst with
      | AStepAdmin _ _ _ _ _ _ hadm _ =>
        rw [hl] at hadm
        exact (hadm : False).elim
      | AStepWrite _ _ _ _ lb _ _ hrow _ hwr hwd _ =>
        rw [hl] at hwr hwd
        simp only [wlWr] at hwr
        simp only [wlWdata] at hwd
        refine ⟨?_, lb, _, hrow, hwr.symm⟩
        unfold graphData
        rw [AxWp.growLookup _ _ _ _ hrow, Option.bind_some, ← hwd]
      | AStepFence _ _ _ _ _ _ _ _ hf _ _ =>
        rw [hl] at hf
        simp [wlFence] at hf
    rw [hl, hs']
    simp only [wlWdata]
    unfold wpEvStep
    iintro %na Hpg
    ihave Hf := F $$ %GD %ls %k %(WeakInterpProj.wbytes n v') %(paZ req.pa) %n %Hc Hg Hloc
      %Hgd.1 %⟨Hdok, Hgd.2⟩
    imod Hf $$ %na Hpg with Hf
    imodintro
    inext
    imod Hf with ⟨%R, %nu, %nuu, %ls', Hs, Hfe, Hna, Hl, HO⟩
    imodintro
    iexists (), R, nu, nuu, ls'
    isplitr
    · ipureintro
      trivial
    iframe Hs Hna Hl
    isplitl [Hfe]
    · iapply (flowEqDynMono GD (i, k) _ nu R
        iprop(R ∗ ⌜graphData GD (i, k) = some (WeakInterpProj.wbytes n v')⌝))
      · inext
        iintro HR
        iframe HR
        ipureintro
        exact Hgd.1
      · iexact Hfe
    · iapply C $$ %rs
      · ipureintro
        exact HP
      · iexact HO
  isplit
  · -- (c) the PLIC wire
    iintro %s' %Hw
    obtain ⟨hk, hp⟩ := awireAeqv _ _ Hw
    obtain ⟨p', k'⟩ := s'
    simp only at hk hp
    subst hk
    match p', hp with
    | .PHart c m' rs' fn' ib', hp =>
      obtain ⟨rfl, rfl, rfl, rfl, hag⟩ := hp
      unfold wpSkipStep
      iintro %na Hna
      imodintro
      inext
      imodintro
      iexists ls
      iframe Hna Hloc
      iapply IH $$ %rs' %(HA rs rs' HP hag) F C
  · iintro %Heq
    iapply (Hmid GD _ HGD (by exact trivial) Heq)

/-! # 2b. (Lean-only, deviation 7) THE STUCK WRITE: a plain RAM write at the row end -/

section stuckWrite
variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF] [Axpol]

/-- (Lean-only, P4) A plain RAM WRITE at the row end is stuck: no row item ⇒ no `AStepWrite`, and
a plain store node has no other program step (`storeNodePstep`); the write node is a `midState`,
so the post is `Hmid`'s.  The write twin of `wpdStuckReadM` (AxSymCtl); the bridge case of
`AxCert.Cert.cWrEnd`. -/
theorem AxCert2.wpdStuckWriteM (M : Gdexec → Prop) (i : Agent) (Φ : Athread → IProp GF)
    (cpu : CPU) (G : Gdexec → Prop)
    (HG : ∀ GD, M GD → AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜G GD⌝)
    (Hmid : ∀ GD s, G GD → midState s → s.atK = (AxOpsem.grow GD i).length →
      ⊢ postLifting Φ i s)
    (kend : Nat) (HGl : ∀ GD, G GD → (AxOpsem.grow GD i).length = kend) (n va : Nat)
    (req : Mem_write_request n va Arch.pa Arch.translation Arch.arch_ak)
    (KK : Result (Option Bool) Arch.abort → SailM Unit) (ib : Ibch)
    (A : RegFile → Prop)
    (HA : ∀ rs rs', A rs → regsAgree AxRunClose.pinReg rs' rs → A rs')
    (Hdev : devAddr req.pa = false) (Hlat : (classify req.access_kind).akLatest = false) :
    ∀ rs, A rs →
    ⊢ wpdM M .MaybeStuck i ⟨.PHart cpu (.impure (.ok (.memWrite n va req)) KK) rs none ib, kend⟩ Φ := by
  intro rs HAr
  let P : Athread → Prop := fun s => ∃ rs1 ib1,
    s = ⟨.PHart cpu (.impure (.ok (.memWrite n va req)) KK) rs1 none ib1, kend⟩ ∧ A rs1
  have Hnord : ∀ GD s1 id K, G GD → P s1 → ¬ areadStep (AxOpsem.grow GD i) s1 id K := by
    rintro GD s1 id K - ⟨rs1, ib1, rfl, -⟩
    exact AxEpiLedgerSd.storeNoRead _ cpu n va req KK rs1 ib1 kend id K Hdev Hlat
  have Hclos : ∀ GD s1 l s2, G GD → P s1 → AxOpsem.astepProg (AxOpsem.grow GD i) s1 l s2 →
      wlWdata l = none ∧ s2.atK = s1.atK ∧ (P s2 ∨ False) := by
    rintro GD s1 l s2 HGD ⟨rs1, ib1, rfl, -⟩ Hst
    exfalso
    cases Hst with
    | AStepAdmin _ _ d _ p' d' hadm hps =>
      obtain ⟨v, -, rfl, -⟩ := storeNodePstep cpu n va req KK rs1 ib1 d l p' d' Hdev Hlat hps
      exact (hadm : False).elim
    | AStepWrite _ _ d _ lb p' d' hrow _ _ _ _ =>
      rw [List.getElem?_eq_none (by rw [HGl GD HGD]; exact Nat.le_refl _)] at hrow
      cases hrow
    | AStepFence _ _ d _ lb p' d' _ hf _ hps =>
      obtain ⟨v, -, rfl, -⟩ := storeNodePstep cpu n va req KK rs1 ib1 d l p' d' Hdev Hlat hps
      simp [wlFence] at hf
  have Hwire : ∀ s1 s2, P s1 → awire s1 s2 → P s2 ∨ False := by
    rintro s1 s2 ⟨rs1, ib1, rfl, HA1⟩ Hw
    obtain ⟨hk, hp⟩ := awireAeqv _ _ Hw
    obtain ⟨p2, k2⟩ := s2
    simp only at hk hp
    subst hk
    cases p2 with
    | PDisk _ => exact hp.elim
    | PHart c m2 rs2 fn2 ib2 =>
      obtain ⟨rfl, rfl, rfl, rfl, hag⟩ := hp
      exact .inl ⟨rs2, ib2, rfl, HA rs1 rs2 HA1 hag⟩
  iapply (wpdOfClosedRunGM M i G P (fun _ => False) Φ HG Hnord (fun GD s1 l s2 h1 h2 h3 _ => Hclos GD s1 l s2 h1 h2 h3) Hwire) $$
    %⟨.PHart cpu (.impure (.ok (.memWrite n va req)) KK) rs none ib, kend⟩ %⟨rs, ib, rfl, HAr⟩
  isplit
  · iintro %s2 %H
    exact H.elim
  · iintro %GD %s1 %HGD %HP1 %Heq
    obtain ⟨rs1, ib1, rfl, -⟩ := HP1
    iapply (Hmid GD _ HGD (by exact trivial) Heq)

end stuckWrite

/-! # 3. THE BRIDGE -/

include HG Hmid Htext Hflow Hloc HnoRmw HnoSplit in
theorem wpdOfCertM (Q : Cst → Unit → ExecSt → Prop) (m : SailM Unit) (s : Cst) (t : ExecSt) :
    AxCert.Cert img dok kind (fun _ _ _ => False) Q s m t →
    ∀ rs ib k, regsAgree AxRunClose.pinReg rs t.regs → AxCert2.bpos G i k s.csB →
    ⊢ CResM M dok kind i Out s.csD -∗
      (∀ s' t' rs' ib' k', ⌜Q s' () t'⌝ -∗ ⌜regsAgree AxRunClose.pinReg rs' t'.regs⌝ -∗
         ⌜AxCert2.bpos G i k' s'.csB⌝ -∗ CResM M dok kind i Out s'.csD -∗
         wpdM M .MaybeStuck i ⟨.PHart cpu (.pure ()) rs' none ib', k'⟩ Φ) -∗
      wpdM M .MaybeStuck i ⟨.PHart cpu m rs none ib, k⟩ Φ := by
  intro H
  induction H with
  | cRet s x t HQ =>
    intro rs ib kk Hag Hb
    iintro Hd C
    iapply C $$ %s %t %rs %ib %kk %HQ %Hag %Hb Hd
  | cExt s e k t he => exact he.elim
  | cRd s r k t _ _ IHs IHn =>
    intro rs ib kk Hag Hb
    iintro Hd C
    iapply (wpdAdminNode3M M i Φ cpu G HG Hmid _ ?_ kk
      (fun rs1 => regsAgree AxRunClose.pinReg rs1 t.regs)
      (fun s2 => ∃ rs1 ib1, s2 = ⟨.PHart cpu (k (rs1 r)) rs1 none ib1, kk⟩ ∧
        regsAgree AxRunClose.pinReg rs1 t.regs)
      (fun _ _ h1 h2 => regsAgreeTrans _ _ _ _ h2 h1) ?_ rs ib Hag)
    all_goals try exact trivial
    · intro rs1 ib1 d l p' d' HA1 Hp
      obtain ⟨rfl, rfl⟩ := pstepRdInv cpu r k rs1 ib1 d l p' d' Hp
      exact ⟨trivial, rs1, _, rfl, HA1⟩
    · iintro %s2 %HN
      obtain ⟨rs1, ib1, rfl, HA1⟩ := HN
      by_cases Hs : AxRunClose.pinReg r
      · iapply (IHs Hs (rs1 r) rs1 ib1 kk HA1 Hb) $$ Hd C
      · have h := IHn Hs rs1 ib1 kk HA1 Hb
        rw [← HA1 r Hs] at h
        iapply h $$ Hd C
  | cWr s r v k t Hr _ IH =>
    intro rs ib kk Hag Hb
    iintro Hd C
    iapply (wpdAdminNode3M M i Φ cpu G HG Hmid _ ?_ kk
      (fun rs1 => regsAgree AxRunClose.pinReg rs1 t.regs)
      (fun s2 => ∃ rs1 ib1, s2 = ⟨.PHart cpu (k PUnit.unit) (rs1.set r v) none ib1, kk⟩ ∧
        regsAgree AxRunClose.pinReg rs1 t.regs)
      (fun _ _ h1 h2 => regsAgreeTrans _ _ _ _ h2 h1) ?_ rs ib Hag)
    all_goals try exact trivial
    · intro rs1 ib1 d l p' d' HA1 Hp
      obtain ⟨Hl, rfl⟩ := pstepWrInv cpu r v k rs1 ib1 d l p' d' Hp
      exact ⟨Hl, rs1, ib1, rfl, HA1⟩
    · iintro %s2 %HN
      obtain ⟨rs1, ib1, rfl, HA1⟩ := HN
      iapply (IH (rs1.set r v) ib1 kk (regsAgreeSet _ _ _ r v HA1) Hb) $$ Hd C
  | cMrd d b r n va req k t vs Hdev Hlat Hnf Hvs _ IH =>
    intro rs ib kk Hag Hb
    iintro Hd C
    iapply (AxSymEngine3.wpdImgRead3M M img i Φ cpu G HG Hmid Htext Hflow n va req k ib kk vs
      (fun rs1 => regsAgree AxRunClose.pinReg rs1 t.regs)
      (fun _ _ h1 h2 => regsAgreeTrans _ _ _ _ h2 h1) Hdev Hlat Hnf Hvs) $$ %rs %Hag
    iintro %rs' %HA'
    iapply (IH rs' ib (kk + 1) HA' (bposSucc G i kk b Hb)) $$ Hd C
  | cIf s n va req k t vs Hdev Hlat Hfe Hvs _ IH =>
    intro rs ib kk Hag Hb
    iintro Hd C
    iapply (AxSymEngine3.wpdImgFetch3M M img i Φ cpu G HG Hmid Htext n va req k ib kk vs
      (fun rs1 => regsAgree AxRunClose.pinReg rs1 t.regs)
      (fun _ _ h1 h2 => regsAgreeTrans _ _ _ _ h2 h1) Hdev Hfe Hvs) $$ %rs %Hag
    iintro %rs' %HA'
    iapply (IH rs' ib kk HA' Hb) $$ Hd C
  | cEnd d r n va req k t Hdev Hlat Hnf =>
    intro rs ib kk Hag Hb
    have Hb' : ∀ GD, G GD → (AxOpsem.grow GD i).length = kk + 0 := Hb
    iintro - -
    iapply (wpdStuckReadM M i Φ cpu G HG Hmid kk (fun GD h => Hb' GD h) n va req k ib
      (fun rs1 => regsAgree AxRunClose.pinReg rs1 t.regs)
      (fun _ _ h1 h2 => regsAgreeTrans _ _ _ _ h2 h1) Hdev Hlat Hnf rs Hag)
  | cWrEnd d r n va req k t Hdev Hlat =>
    intro rs ib kk Hag Hb
    have Hb' : ∀ GD, G GD → (AxOpsem.grow GD i).length = kk + 0 := Hb
    iintro - -
    iapply (AxCert2.wpdStuckWriteM M i Φ cpu G HG Hmid kk (fun GD h => Hb' GD h) n va req k ib
      (fun rs1 => regsAgree AxRunClose.pinReg rs1 t.regs)
      (fun _ _ h1 h2 => regsAgreeTrans _ _ _ _ h2 h1) Hdev Hlat rs Hag)
  | cDrd b r n va req k t Hkd Hdev Hlat Hnf Hdok _ IH =>
    intro rs ib kk Hag Hb
    have hconv : CResM M dok kind i Out .CPend ⊢ FldM M dok i Out := by
      subst Hkd
      exact .rfl
    iintro Hd C
    ihave Hd := hconv $$ Hd
    iapply (wpdDrdNodeM M dok kind i Φ cpu G HG Hmid HnoRmw Out n va req k ib kk
      (fun rs1 => regsAgree AxRunClose.pinReg rs1 t.regs)
      (fun _ _ h1 h2 => regsAgreeTrans _ _ _ _ h2 h1) Hkd Hdev Hlat Hnf Hdok) $$ %rs %Hag Hd
    iintro %vs %rs' %Hlen %HA' HO
    have hdone : iprop(∃ k, Out k vs) ⊢ CResM M dok kind i Out (.CLd vs) := .rfl
    iapply (IH vs Hlen rs' ib (kk + 1) HA' (bposSucc G i kk b Hb)) $$ [HO] C
    iapply hdone
    iexists kk
    iexact HO
  | cDwr b r n va req k t v Hkd Hdev Hlat Hval Hdok _ IH =>
    intro rs ib kk Hag Hb
    have hconv : CResM M dok kind i Out .CPend ⊢ FstM M dok i Out := by
      subst Hkd
      exact .rfl
    iintro Hd C
    ihave Hd := hconv $$ Hd
    iapply (wpdDwrNodeM M dok i Φ cpu G HG Hmid Out n va req k ib kk v
      (fun rs1 => regsAgree AxRunClose.pinReg rs1 t.regs)
      (fun _ _ h1 h2 => regsAgreeTrans _ _ _ _ h2 h1) Hdev Hlat Hval Hdok) $$ %rs %Hag Hd
    iintro %rs' %HA' HO
    have hdone : iprop(∃ k, Out k (WeakInterpProj.wbytes n v)) ⊢
        CResM M dok kind i Out (.CSt (WeakInterpProj.wbytes n v) (wcls req.access_kind r)) := .rfl
    iapply (IH rs' ib (kk + 1) HA' (bposSucc G i kk b Hb)) $$ [HO] C
    iapply hdone
    iexists kk
    iexact HO
  | cFence d b r bk k t Hpark _ IH =>
    intro rs ib kk Hag Hb
    iintro Hd C
    iapply (wpdFenceNodeM M i Φ cpu G HG Hmid Hloc bk k ib kk
      (fun rs1 => regsAgree AxRunClose.pinReg rs1 t.regs)
      (fun _ _ h1 h2 => regsAgreeTrans _ _ _ _ h2 h1) Hpark) $$ %rs %Hag
    iintro %rs' %HA'
    iapply (IH rs' ib (kk + 1) HA' (bposSucc G i kk b Hb)) $$ Hd C
  | cXrd b r n va req k t Hkd Hdev Hlat Hdok _ IH =>
    intro rs ib kk Hag Hb
    iintro Hd C
    iapply (wpdXrdNodeM M dok kind i Φ cpu G HG Hmid HnoSplit n va req k ib kk
      (fun rs1 => regsAgree AxRunClose.pinReg rs1 t.regs)
      (fun _ _ h1 h2 => regsAgreeTrans _ _ _ _ h2 h1) Hkd Hdev Hlat Hdok) $$ %rs %Hag
    iintro %vs %rs' %Hlen %HA'
    have hconv : CResM M dok kind i Out .CPend ⊢
        CResM M dok kind i Out (.CRmwR (classify req.access_kind).akSync vs) := by
      subst Hkd
      exact .rfl
    ihave Hd := hconv $$ Hd
    iapply (IH vs Hlen rs' ib kk HA' Hb) $$ Hd C
  | cXwr aq rvs b r n va req k t v Hkd Hdev Hlat Hval Hdok _ IH =>
    intro rs ib kk Hag Hb
    have hconv : CResM M dok kind i Out (.CRmwR aq rvs) ⊢ FstM M dok i Out := .rfl
    iintro Hd C
    ihave Hd := hconv $$ Hd
    iapply (wpdXwrNodeM M dok i Φ cpu G HG Hmid Out n va req k ib kk v
      (fun rs1 => regsAgree AxRunClose.pinReg rs1 t.regs)
      (fun _ _ h1 h2 => regsAgreeTrans _ _ _ _ h2 h1) Hdev Hlat Hval Hdok) $$ %rs %Hag Hd
    iintro %rs' %HA' HO
    have hdone : iprop(∃ k, Out k (WeakInterpProj.wbytes n v)) ⊢
        CResM M dok kind i Out (.CRmw aq (classify req.access_kind).akSync rvs
          (WeakInterpProj.wbytes n v) (wcls req.access_kind r)) := .rfl
    iapply (IH rs' ib (kk + 1) HA' (bposSucc G i kk b Hb)) $$ [HO] C
    iapply hdone
    iexists kk
    iexact HO
  | cIa s n w k t Hsf _ IH =>
    intro rs ib kk Hag Hb
    iintro Hd C
    iapply (AxSymEngine3.wpdSilentNode3M M i Φ cpu G HG Hmid _ (k ()) ?_ kk t ?_ rs ib Hag)
    all_goals try exact trivial
    · intro rs ib d l m' ors fn' d' oib obar h
      obtain ⟨rfl, rfl, rfl, rfl, -⟩ := h
      rw [annLabelNot Hsf]
      exact ⟨rfl, rfl, rfl, rfl⟩
    · iintro %rs1 %ib1 %HA1
      iapply (IH rs1 ib1 kk HA1 Hb) $$ Hd C
  | cSf d b r n w k t Hsf _ IH =>
    intro rs ib kk Hag Hb
    iintro Hd C
    iapply (AxCert2.wpdSfNodeM M i Φ cpu G HG Hmid Hloc n w k ib kk
      (fun rs1 => regsAgree AxRunClose.pinReg rs1 t.regs)
      (fun _ _ h1 h2 => regsAgreeTrans _ _ _ _ h2 h1) Hsf) $$ %rs %Hag
    iintro %rs' %ib' %HA'
    iapply (IH rs' ib' (kk + 1) HA' (bposSucc G i kk b Hb)) $$ Hd C
  | cBa s _ _ k t _ IH | cCo s _ k t _ IH | cTl s _ k t _ IH | cTe s _ k t _ IH
  | cRx s _ k t _ IH | cTs s _ k t _ IH | cTx s _ k t _ IH | cCc s k t _ IH
  | cMsg s _ k t _ IH | cGcc s k t _ IH =>
    intro rs ib kk Hag Hb
    iintro Hd C
    iapply (AxSymEngine3.wpdSilentNode3M M i Φ cpu G HG Hmid _ _ ?_ kk t ?_ rs ib Hag)
    all_goals try exact trivial
    · intro rs ib d l m' ors fn' d' oib obar h
      obtain ⟨rfl, rfl, rfl, rfl, -⟩ := h
      exact ⟨trivial, rfl, rfl, rfl⟩
    · iintro %rs1 %ib1 %HA1
      iapply (IH rs1 ib1 kk HA1 Hb) $$ Hd C

include HG Hmid Htext Hflow Hloc HnoRmw HnoSplit in
/-- ONE INSTRUCTION from a `.pure ()` boundary at position `k`: certificates for BOTH ticks at
any state agreeing with the boundary registers off the pins, from the start state `s0`
(`bpos k` of its budget). -/
theorem wpdInstrOfCertM (Q : Cst → Unit → ExecSt → Prop) (s0 : Cst) (rs : RegFile) (k : Nat)
    (s : Athread) (Hs : RetX cpu rs k s)
    (Hbp : AxCert2.bpos G i k s0.csB)
    (Hb : ∀ GD s1, G GD → RetX cpu rs k s1 → s1.atK = (AxOpsem.grow GD i).length →
      ⊢ postLifting Φ i s1)
    (Hcert : ∀ (tick : Bool) (t : ExecSt), regsAgree AxRunClose.pinReg t.regs rs →
       AxCert.Cert img dok kind (fun _ _ _ => False) Q s0 (riscvStep tick) t) :
    ⊢ CResM M dok kind i Out s0.csD -∗
      (∀ s' t' rs' ib' k', ⌜Q s' () t'⌝ -∗ ⌜regsAgree AxRunClose.pinReg rs' t'.regs⌝ -∗
         ⌜AxCert2.bpos G i k' s'.csB⌝ -∗ CResM M dok kind i Out s'.csD -∗
         wpdM M .MaybeStuck i ⟨.PHart cpu (.pure ()) rs' none ib', k'⟩ Φ) -∗
      wpdM M .MaybeStuck i s Φ := by
  iintro Hd C
  iapply (wpdRetNode3M M i Φ cpu G HG rs k s Hs Hb)
  iintro %s2 %HN
  obtain ⟨tick, rs', Hag, rfl⟩ := HN
  iapply (wpdOfCertM M img dok kind i Φ cpu G HG Hmid Htext Hflow Hloc HnoRmw HnoSplit Out Q _ s0
    ⟨rs', fun _ => none, testDevs⟩
    (Hcert tick ⟨rs', fun _ => none, testDevs⟩ (regsAgreeSym _ _ _ Hag)) rs' ibNone k
    (regsAgreeRefl _ _) Hbp) $$ Hd C

end bridgeC

/-! ### The riscv.cat instances under the Rocq names (`…M` at `rvwmoCatConsistent`) -/

section bridgeCCat
variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF] [Axpol]

/-- (Rocq notation) -/
abbrev CFk (dok : Int → Nat → Prop) (kind : Dkind) (i : Agent)
    (Out : Nat → List (BitVec 8) → IProp GF) : IProp GF :=
  CFkM rvwmoCatConsistent dok kind i Out

/-- (Rocq notation) -/
abbrev CRes (dok : Int → Nat → Prop) (kind : Dkind) (i : Agent)
    (Out : Nat → List (BitVec 8) → IProp GF) (d : Cdata) : IProp GF :=
  CResM rvwmoCatConsistent dok kind i Out d

theorem wpdFenceNode :
    type_of% (wpdFenceNodeM (hlc := hlc) (GF := GF) rvwmoCatConsistent) :=
  wpdFenceNodeM rvwmoCatConsistent

theorem wpdXrdNode :
    type_of% (wpdXrdNodeM (hlc := hlc) (GF := GF) rvwmoCatConsistent) :=
  wpdXrdNodeM rvwmoCatConsistent

theorem wpdXwrNode :
    type_of% (wpdXwrNodeM (hlc := hlc) (GF := GF) rvwmoCatConsistent) :=
  wpdXwrNodeM rvwmoCatConsistent

theorem wpdDrdNode :
    type_of% (wpdDrdNodeM (hlc := hlc) (GF := GF) rvwmoCatConsistent) :=
  wpdDrdNodeM rvwmoCatConsistent

theorem wpdDwrNode :
    type_of% (wpdDwrNodeM (hlc := hlc) (GF := GF) rvwmoCatConsistent) :=
  wpdDwrNodeM rvwmoCatConsistent

theorem wpdOfCert :
    type_of% (wpdOfCertM (hlc := hlc) (GF := GF) rvwmoCatConsistent) :=
  wpdOfCertM rvwmoCatConsistent

theorem wpdInstrOfCert :
    type_of% (wpdInstrOfCertM (hlc := hlc) (GF := GF) rvwmoCatConsistent) :=
  wpdInstrOfCertM rvwmoCatConsistent

end bridgeCCat

end Weak
