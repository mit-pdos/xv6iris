/-
Weak: **allocproc route P, row P-W6 — THE BUFFERED TWIN'S STATE MAP (`rmemP`), the memory rows**
(plan rev 57 row P-W6; design `notes/weak-allocproc-routeP-design.md` §3.6 (b); `PROGRESS-PW6.md`).
Lean-only, no Rocq twin.  A PRIMED TWIN: nothing registered imports this file.

The registered W4 relates a pf configuration to a MachCSL state by `PfStepTsoMem.rmem` (`R-log`,
`R-img`, `R-hist`, `R-resv`, every buffer empty).  Under route P the twin's machine is `SbCand`
(`Weak/SbCand.lean`): its LOG is the LANDED log (landing order) and each agent has a buffer of pending
entries.  **`SbRealP.rmemP img c σ`** relates an `SbCand` state `c` to a MachCSL state `σ`:

* `R-log`  — the twin's log authors are MachCSL's LANDED authors (`landAuthors σ.log σ.llog`): pf log
  position `k` is landing position `k + 1` (`R-lp`: `σ.llog[k]` is the issue stamp of `c.ms.msLog[k]`);
* `R-hist` — **the LANDED VIEW of the MachCSL memory is the pf projection of the twin's log**
  (`rhist (σ.mem.lview σ.lp) img c.ms.msLog`: W4's `R-hist` read through `FlatMem.lview`);
* `R-sb`   — hart `cpu`'s MachCSL buffer (issue stamp, epoch) and the twin's buffer of agent
  `hartAgent cpu` agree entry by entry (`entRel`): the entry's bytes are the history entries at its
  stamp (`memStamp`), its fence counter is the epoch distance `σ.sbEp cpu - ep`, it is not `.rl`, its
  author is the hart; every non-hart agent's twin buffer is EMPTY (the DMA engine lands at once);
* `R-resv` — no reservation between items; `σ.okP` (MachCSL's route-P invariant) and `stampsNodup`
  (one entry per stamp per byte).

The rows proved here (memory side only; views are not needed — a member read is a TOP read and a
MachCSL read at `tvn = σ.ltop` is always enabled, `topLoadEnabled`):
* §2 boot (`rmemPBoot`); §3 the ISSUE (`rmemPIssue`); §4 the FENCE (`rmemPFence`, the epoch,
  `fenceEpochOfEbar`; the barrier guard from the twin's drain, `fenceGuardOf`, with `fence.i`'s drain
  a PREMISE `hfi` that [OWN.143] (non-draining `fence.i`) makes vacuous — nothing here uses it);
* §5 the LANDING (`rmemPLand`: the twin's `SbPol.epoch` landing IS a MachCSL `landOk` landing of the
  matching stamp, GIVEN `ForeignBelowLanded` — finding F-PW6-1);
* §6 the plain load's bytes at the landed top (`byteFwdTop`: MachCSL's `byteFwd` at `σ.ltop` = the
  twin's forwarded byte, else the member-latest byte `topByte`) and the exclusive read's (`topLEq`);
* §7 the AMO (`amoGuardOf`: `amoOk` gives MachCSL's `¬ sbOverlaps` and `landNowOk`; `rmemPRmw`: the
  exclusive read at the landed top then the write that lands at once);
* §8 the read side (`topLoadEnabled`, `rmemPLoad`, `rmemPIo`);
* §9 F-PW6-1 both sides: `landBlockedForeign` (MachCSL lands two harts' same-byte pending stores in
  ISSUE order) and `wit1Run`/`wit1Log` (an `SbCand` run, every lawful policy, landing them in the
  reverse order).

Spec: FAITHFUL (proof organisation over `SbCand` and MachCSL's route-P memory; the one premise
`ForeignBelowLanded` is a MachCSL-strength item: MachCSL orders same-byte plain stores of DIFFERENT
harts by ISSUE, RVWMO does not — F-PW6-1).  Lean-only helpers `SbRealP.*`.
-/
import Weak.SbCand
import Weak.PfStepTsoMem
import Weak.WeakEvInst

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std LeanRV64D
open Lbl PfStepTsoMem

namespace SbRealP

/-! # 1. The state map -/

/-- The byte history `H` holds at issue stamp `t` (its first entry at `t`). -/
def stampByte (H : Hist) (t : Nat) : Option (BitVec 8) := (H.find? (fun e => e.t == t)).map HEnt.v

/-- The byte the memory holds at `a` at issue stamp `t`. -/
def memStamp (m : FlatMem) (a : PAddr) (t : Nat) : Option (BitVec 8) := (m[a]?).bind (stampByte · t)

/-- One entry per stamp per byte. -/
def stampsNodup (m : FlatMem) : Prop := ∀ (a : PAddr) (H : Hist), m[a]? = some H → (H.map HEnt.t).Nodup

/-- **`R-sb`, one entry**: MachCSL's pending `(stamp, epoch)` of hart `cpu` and the twin's entry. -/
def entRel (σ : MState) (cpu : CPU) (p : Nat × Nat) (e : SbEnt) : Prop :=
  e.fs = σ.sbEp cpu - p.2 ∧ e.rl = false ∧ e.msg.wmTid = some (hartAgent cpu) ∧
  ∀ a : PAddr, memStamp σ.mem a p.1 = msgByte e.msg (paZ a)

/-- **THE STATE MAP of the buffered twin** (`R-log` + `R-hist` over the landed view + `R-sb` (+epochs)
+ `R-lp` (through `R-log`) + `R-resv` + MachCSL's route-P invariant). -/
def rmemP (img : Image) (c : SbCand.CandS) (σ : MState) : Prop :=
  c.ms.msImg = img ∧
  c.ms.msLog.map Wmsg.wmTid = (landAuthors σ.log σ.llog).map some ∧
  (∀ a ∈ σ.log, a ≤ NCPU) ∧
  rhist (σ.mem.lview σ.lp) img c.ms.msLog ∧
  (∀ cpu, List.Forall₂ (entRel σ cpu) (σ.sb cpu) (c.sb (hartAgent cpu))) ∧
  (∀ i, (∀ cpu : CPU, i ≠ hartAgent cpu) → c.sb i = []) ∧
  (∀ cpu, σ.resv cpu = none) ∧
  stampsNodup σ.mem ∧
  σ.okP

/-! ## 1.1 Generic helpers -/

theorem hartAgentInj {c c' : CPU} (h : hartAgent c = hartAgent c') : c = c' := Fin.ext h

theorem landAuthorsSnocLog (log : List Agent) (llog : List Nat) (x : Agent)
    (h : ∀ t ∈ llog, 1 ≤ t ∧ t ≤ log.length) :
    landAuthors (log ++ [x]) llog = landAuthors log llog := by
  unfold landAuthors
  apply List.map_congr_left
  intro t ht
  have := h t ht
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_append_left (by omega)]

theorem landAuthorsSnoc (log : List Agent) (llog : List Nat) (t : Nat) :
    landAuthors log (llog ++ [t]) = landAuthors log llog ++ [log.getD (t - 1) diskAgent] := by
  simp [landAuthors]

theorem stampByteCons (e : HEnt) (H : Hist) (t : Nat) :
    stampByte (e :: H) t = if e.t = t then some e.v else stampByte H t := by
  unfold stampByte
  by_cases h : e.t = t
  · simp [h]
  · simp [h]

theorem stampByteNone (H : Hist) (t : Nat) (h : ∀ e ∈ H, e.t ≠ t) : stampByte H t = none := by
  unfold stampByte
  rw [List.find?_eq_none.2 (fun e he => by simpa using h e he)]
  rfl

/-- A pending push leaves the landed view of a history alone. -/
theorem lviewConsPending (lp : LandPos) (e : HEnt) (H : Hist) (he : lp e.t = none) :
    Hist.lview lp (e :: H) = Hist.lview lp H := Hist.lview_cons_pending lp e H he

/-- `getD` of a present history. -/
theorem getDOfSome {m : FlatMem} {a : PAddr} {H : Hist} (h : m[a]? = some H) : m.getD a [] = H := by
  rw [Std.ExtTreeMap.getD_eq_getD_getElem?, h]; rfl

/-- The landed view is present exactly where the memory is. -/
theorem lviewSomeInv {m : FlatMem} {lp : LandPos} {a : PAddr} {L : Hist} (h : (m.lview lp)[a]? = some L) :
    ∃ H, m[a]? = some H ∧ Hist.lview lp H = L := by
  obtain ⟨H, h1, h2⟩ := FlatMem.lview_get?_eq_some h
  exact ⟨H, h1, h2.symm⟩

theorem lviewNoneOf {m : FlatMem} {lp : LandPos} {a : PAddr} (h : (m.lview lp)[a]? = none) : m[a]? = none := by
  rw [FlatMem.lview_get?] at h
  cases hm : m[a]? with
  | none => rfl
  | some _ => rw [hm] at h; cases h

/-- Under the invariant, the stamps a history holds are at most the issue top. -/
theorem stampLeTop {σ : MState} (h : σ.okP) {a : PAddr} {H : Hist} (hH : σ.mem[a]? = some H)
    {e : HEnt} (he : e ∈ H) : e.t ≤ σ.top := σ.okP_le_top h a H hH e he

/-- A buffered stamp is at least 1 and at most the issue top. -/
theorem sbStampBound {σ : MState} (h : σ.okP) {cpu : CPU} {p : Nat × Nat} (hp : p ∈ σ.sb cpu) :
    1 ≤ p.1 ∧ p.1 ≤ σ.top := by
  have := (h.2.2.2.2.2.2.1 cpu p.1).1 ⟨p.2, hp⟩
  exact ⟨this.1, this.2.1⟩

theorem forall2Append {α β : Type} {R : α → β → Prop} {l1 l2 : List α} {m1 m2 : List β}
    (h1 : List.Forall₂ R l1 m1) (h2 : List.Forall₂ R l2 m2) : List.Forall₂ R (l1 ++ l2) (m1 ++ m2) := by
  induction h1 with
  | nil => exact h2
  | cons hab _ ih => exact List.Forall₂.cons hab ih

theorem forall2ImpMem {α β : Type} {R S : α → β → Prop} {l : List α} {m : List β}
    (h : List.Forall₂ R l m) (hi : ∀ a b, a ∈ l → R a b → S a b) : List.Forall₂ S l m := by
  induction h with
  | nil => exact List.Forall₂.nil
  | cons hab _ ih =>
    exact List.Forall₂.cons (hi _ _ List.mem_cons_self hab)
      (ih (fun a b ha hr => hi a b (List.mem_cons_of_mem _ ha) hr))

theorem forall2MapRight {α β : Type} {R S : α → β → Prop} {l : List α} {m : List β} {f : β → β}
    (h : List.Forall₂ R l m) (hi : ∀ a b, a ∈ l → R a b → S a (f b)) : List.Forall₂ S l (m.map f) := by
  induction h with
  | nil => exact List.Forall₂.nil
  | cons hab _ ih =>
    exact List.Forall₂.cons (hi _ _ List.mem_cons_self hab)
      (ih (fun a b ha hr => hi a b (List.mem_cons_of_mem _ ha) hr))

theorem forall2NilRight {α β : Type} {R : α → β → Prop} {l : List α} (h : List.Forall₂ R l ([] : List β)) :
    l = [] := by
  cases h; rfl

theorem forall2NilLeft {α β : Type} {R : α → β → Prop} {m : List β} (h : List.Forall₂ R ([] : List α) m) :
    m = [] := by
  cases h; rfl

/-! ## 1.2 The plain store's footprint -/

theorem writeBytesIn (m : FlatMem) (pa : PAddr) (n : Nat) (w : BitVec (8 * n)) (t : Nat) (h : Agent)
    (hnw : pa.toNat + n ≤ 2 ^ 64) {j : Nat} (hj : j < n) :
    (m.writeBytes pa n w t h)[pa + BitVec.ofNat 64 j]? =
      some (⟨t, h, nthByte w j⟩ :: m.getD (pa + BitVec.ofNat 64 j) []) := by
  unfold FlatMem.writeBytes
  exact foldPushIn m pa (fun j => ⟨t, h, nthByte w j⟩) n hnw n (Nat.le_refl _) j hj

/-- A plain store moves no other stamp's byte. -/
theorem memStampWriteNe (m : FlatMem) (pa : PAddr) (n : Nat) (w : BitVec (8 * n)) (t0 : Nat) (h : Agent)
    (hnw : pa.toNat + n ≤ 2 ^ 64) (a : PAddr) (t : Nat) (ht : t ≠ t0) :
    memStamp (m.writeBytes pa n w t0 h) a t = memStamp m a t := by
  unfold memStamp
  by_cases hfp : ∃ j, j < n ∧ a = pa + BitVec.ofNat 64 j
  · obtain ⟨j, hj, rfl⟩ := hfp
    rw [writeBytesIn m pa n w t0 h hnw hj, Option.bind_some, stampByteCons, if_neg (Ne.symm ht),
      Std.ExtTreeMap.getD_eq_getD_getElem?]
    cases m[pa + BitVec.ofNat 64 j]? with
    | none => rfl
    | some H => rfl
  · rw [FlatMem.writeBytes_get?_notin _ _ _ _ _ _ (fun j hj he => hfp ⟨j, hj, he⟩)]

/-- The new stamp's byte is the store's byte (inside the footprint), nothing outside. -/
theorem memStampWriteSelf (m : FlatMem) (pa : PAddr) (n : Nat) (w : BitVec (8 * n)) (t0 : Nat) (h : Agent)
    (hnw : pa.toNat + n ≤ 2 ^ 64) (hfresh : ∀ (a : PAddr) (H : Hist), m[a]? = some H → ∀ e ∈ H, e.t ≠ t0)
    (data : List (BitVec 8)) (tid : Option Nat) (k : WmClass) (hd : data.length = n)
    (hb : ∀ j, j < n → data[j]? = some (nthByte w j)) (a : PAddr) :
    memStamp (m.writeBytes pa n w t0 h) a t0 = msgByte ⟨paZ pa, data, tid, k⟩ (paZ a) := by
  unfold memStamp
  by_cases hfp : ∃ j, j < n ∧ a = pa + BitVec.ofNat 64 j
  · obtain ⟨j, hj, rfl⟩ := hfp
    rw [writeBytesIn m pa n w t0 h hnw hj, Option.bind_some, stampByteCons, if_pos rfl,
      msgByteIn pa n j data tid k hnw hj, hb j hj]
  · have hne : ∀ j, j < n → a ≠ pa + BitVec.ofNat 64 j := fun j hj he => hfp ⟨j, hj, he⟩
    rw [FlatMem.writeBytes_get?_notin _ _ _ _ _ _ hne, msgByteOut pa a n data tid k hd hne]
    cases hm : m[a]? with
    | none => rfl
    | some H => exact stampByteNone H t0 (hfresh a H hm)

/-- One entry per stamp per byte survives a plain store of a fresh stamp. -/
theorem stampsNodupWrite (m : FlatMem) (pa : PAddr) (n : Nat) (w : BitVec (8 * n)) (t0 : Nat) (h : Agent)
    (hnw : pa.toNat + n ≤ 2 ^ 64) (hfresh : ∀ (a : PAddr) (H : Hist), m[a]? = some H → ∀ e ∈ H, e.t ≠ t0)
    (hnd : stampsNodup m) : stampsNodup (m.writeBytes pa n w t0 h) := by
  intro a H hH
  by_cases hfp : ∃ j, j < n ∧ a = pa + BitVec.ofNat 64 j
  · obtain ⟨j, hj, rfl⟩ := hfp
    rw [writeBytesIn m pa n w t0 h hnw hj] at hH
    obtain rfl := Option.some.inj hH
    rw [Std.ExtTreeMap.getD_eq_getD_getElem?]
    cases hm : m[pa + BitVec.ofNat 64 j]? with
    | none => simp
    | some H0 =>
      simp only [Option.getD_some, List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and]
      exact ⟨fun e he het => hfresh _ H0 hm e he het, hnd _ H0 hm⟩
  · rw [FlatMem.writeBytes_get?_notin _ _ _ _ _ _ (fun j hj he => hfp ⟨j, hj, he⟩)] at hH
    exact hnd a H hH

/-- A plain store of a PENDING stamp leaves the landed view's `R-hist` alone. -/
theorem rhistLviewWrite (m : FlatMem) (lp : LandPos) (img : Image) (log : List Wmsg) (pa : PAddr) (n : Nat)
    (w : BitVec (8 * n)) (t0 : Nat) (h : Agent) (hram : ramBytes pa n) (hpend : lp t0 = none)
    (hH : rhist (m.lview lp) img log) : rhist ((m.writeBytes pa n w t0 h).lview lp) img log := by
  have hnw := noWrapOfRam pa n hram
  refine ⟨fun a ha => ?_, fun a ha => ?_⟩
  · rw [FlatMem.lview_get?]
    by_cases hfp : ∃ j, j < n ∧ a = pa + BitVec.ofNat 64 j
    · obtain ⟨j, hj, rfl⟩ := hfp
      obtain ⟨H, hm, hl⟩ := lviewSomeInv (hH.1 _ ha)
      rw [writeBytesIn m pa n w t0 h hnw hj, getDOfSome hm, Option.map_some,
        lviewConsPending lp _ H hpend, hl]
    · rw [FlatMem.writeBytes_get?_notin _ _ _ _ _ _ (fun j hj he => hfp ⟨j, hj, he⟩),
        ← FlatMem.lview_get?]
      exact hH.1 a ha
  · rw [FlatMem.lview_get?, FlatMem.writeBytes_get?_notin _ _ _ _ _ _
      (fun j hj he => ha (by rw [he]; exact hram j hj)), lviewNoneOf (hH.2 a ha)]
    rfl

/-! # 2. Boot -/

/-- The twin's initial state (empty log and buffers) against a booted machine. -/
theorem rmemPBoot (c : SbCand.CandS) (σ : MState) (hb : bootFacts σ) (hc : SbCand.initS c)
    (himg : c.ms.msImg = imgZ bootImage) : rmemP (imgZ bootImage) c σ := by
  obtain ⟨hl0, -, hsb0⟩ := hc
  have hok := σ.okP_boot hb
  obtain ⟨hmem, hlog, hcpu, -, -, hll, hsb⟩ := hb
  have hlp : σ.lp = lpOf [] := by rw [show σ.lp = lpOf σ.llog from rfl, hll]
  refine ⟨himg, by simp [hl0, hll, landAuthors], by simp [hlog], ⟨fun pa hpa => ?_, fun pa hpa => ?_⟩,
    fun cpu => ?_, fun i _ => hsb0 i, fun cpu => (hcpu cpu).2.2.2, ?_, hok⟩
  · rw [FlatMem.lview_get?, hmem, imgFlat_get?, if_pos hpa, hl0, histOfNil, imgZLookup,
      bootImage_get?, if_pos hpa]
    simp only [Option.map_some]
    rw [hlp]
    simp [Hist.lview, HEnt.atLanding, lpOf]
  · rw [FlatMem.lview_get?, hmem, imgFlat_get?, if_neg hpa]; rfl
  · rw [(hsb cpu).1, hsb0]; exact List.Forall₂.nil
  · intro a H hH
    rw [hmem, imgFlat_get?] at hH
    split at hH
    · cases hv : bootImage[a]? with
      | none => rw [hv] at hH; cases hH
      | some v => rw [hv] at hH; obtain rfl := Option.some.inj hH; simp
    · cases hH

/-! # 3. The ISSUE of a plain store -/

/-- **THE ISSUE ROW**: the twin's buffered `LStore` (not `.rl`) by hart `cpu` is MachCSL's issue
(`MState.issue`) of the same bytes. -/
theorem rmemPIssue (img : Image) (c : SbCand.CandS) (σ : MState) (cpu : CPU) (pa : PAddr) (n : Nat)
    (w : BitVec (8 * n)) (vs : List (BitVec 8)) (k : WmClass) (hram : ramBytes pa n)
    (hd : vs.length = n) (hb : ∀ j, j < n → vs[j]? = some (nthByte w j))
    (hR : rmemP img c σ) :
    rmemP img (SbCand.nextE c (hartAgent cpu) (LStore false (paZ pa) vs k)) (σ.issue cpu pa n w) := by
  obtain ⟨himg, hlog, hlogB, hH, hsb, hoth, hresv, hnd, hok⟩ := hR
  have hnw := noWrapOfRam pa n hram
  have hll := hok.2.2.2.2.1
  have hfresh : ∀ (a : PAddr) (H : Hist), σ.mem[a]? = some H → ∀ e ∈ H, e.t ≠ σ.top + 1 :=
    fun a H hH e he het => by have := stampLeTop hok hH he; omega
  have hpend : σ.lp (σ.top + 1) = none := σ.okP_fresh hok
  refine ⟨himg, ?_, ?_, ?_, fun c' => ?_, fun i hi => ?_, fun c' => ?_, ?_, σ.okP_issue cpu pa n w hok⟩
  · show c.ms.msLog.map Wmsg.wmTid = (landAuthors (σ.log ++ [hartAgent cpu]) σ.llog).map some
    rw [landAuthorsSnocLog σ.log σ.llog _ (fun t ht => hll t ht)]
    exact hlog
  · intro a ha
    rcases List.mem_append.1 ha with ha | ha
    · exact hlogB a ha
    · simp at ha; rw [ha]; exact Nat.le_of_lt (hartAgent_lt cpu)
  · exact rhistLviewWrite σ.mem σ.lp img c.ms.msLog pa n w (σ.top + 1) (hartAgent cpu) hram hpend hH
  · -- R-sb
    have hst : ∀ (p : Nat × Nat) (e : SbEnt), p ∈ σ.sb c' → entRel σ c' p e →
        entRel (σ.issue cpu pa n w) c' p e := by
      intro p e hp ⟨h1, h2, h3, h4⟩
      refine ⟨h1, h2, h3, fun a => ?_⟩
      have hb' := sbStampBound hok hp
      show memStamp (σ.mem.writeBytes pa n w (σ.top + 1) (hartAgent cpu)) a p.1 = _
      rw [memStampWriteNe σ.mem pa n w _ _ hnw a p.1 (by omega)]
      exact h4 a
    by_cases hc : c' = cpu
    · subst hc
      show List.Forall₂ (entRel (σ.issue c' pa n w) c')
        (updCpu σ.sb c' (σ.sb c' ++ [(σ.top + 1, σ.sbEp c')]) c')
        (SbCand.updSb c.sb (hartAgent c') (c.sb (hartAgent c') ++
          [SbCand.issueEnt c (hartAgent c') false (paZ pa) vs k]) (hartAgent c'))
      rw [SbCand.updSbEq]
      simp only [updCpu, if_true]
      refine forall2Append ?_ (List.Forall₂.cons ?_ List.Forall₂.nil)
      · exact forall2ImpMem (hsb c') (fun p e hp hr => hst p e hp hr)
      · refine ⟨by simp [SbCand.issueEnt], rfl, rfl, fun a => ?_⟩
        exact memStampWriteSelf σ.mem pa n w (σ.top + 1) (hartAgent c') hnw hfresh vs
          (some (hartAgent c')) k hd hb a
    · show List.Forall₂ (entRel (σ.issue cpu pa n w) c')
        (updCpu σ.sb cpu (σ.sb cpu ++ [(σ.top + 1, σ.sbEp cpu)]) c')
        (SbCand.updSb c.sb (hartAgent cpu) _ (hartAgent c'))
      rw [SbCand.updSbNe _ _ _ _ (fun he => hc (hartAgentInj he))]
      simp only [updCpu, hc, if_false]
      exact forall2ImpMem (hsb c') (fun p e hp hr => hst p e hp hr)
  · show SbCand.updSb c.sb (hartAgent cpu) _ i = []
    rw [SbCand.updSbNe _ _ _ _ (hi cpu)]
    exact hoth i hi
  · show updCpu σ.resv cpu none c' = none
    by_cases hc : c' = cpu
    · subst hc; simp [updCpu]
    · simp only [updCpu, hc, if_false]; exact hresv c'
  · exact stampsNodupWrite σ.mem pa n w (σ.top + 1) (hartAgent cpu) hnw hfresh hnd

/-! # 4. The FENCE -/

/-- **THE FENCE ROW**: the twin's fence (bits `pr pw sr sw`) is MachCSL's `MState.fence cpu b` when
MachCSL's epoch bump is the twin's (`fenceEpoch b = pw && sw`: every barrier but `fence.tso`, whose
W→W half the pf twin PARKS, `fenceEpochOfEbar`). -/
theorem rmemPFence (img : Image) (c : SbCand.CandS) (σ : MState) (cpu : CPU) (b : barrier_kind)
    (pr pw sr sw : Bool) (hep : fenceEpoch b = (pw && sw)) (hR : rmemP img c σ) :
    rmemP img (SbCand.nextE c (hartAgent cpu) (LFence pr pw sr sw)) (σ.fence cpu b) := by
  obtain ⟨himg, hlog, hlogB, hH, hsb, hoth, hresv, hnd, hok⟩ := hR
  have hep9 := hok.2.2.2.2.2.2.2.2
  refine ⟨himg, hlog, hlogB, hH, fun c' => ?_, fun i hi => ?_, hresv, hnd, σ.okP_fence cpu b hok⟩
  · have hrel : ∀ (p : Nat × Nat) (e : SbEnt), entRel σ c' p e → (σ.fence cpu b).mem = σ.mem →
        (σ.fence cpu b).sbEp c' = σ.sbEp c' → entRel (σ.fence cpu b) c' p e := by
      intro p e ⟨h1, h2, h3, h4⟩ hm hs
      exact ⟨by rw [hs]; exact h1, h2, h3, by rw [hm]; exact h4⟩
    by_cases hc : c' = cpu
    · subst hc
      cases hpw : (pw && sw)
      · -- no bump on either side
        have hs : (σ.fence c' b).sbEp c' = σ.sbEp c' := by
          show (if c' = c' then (if fenceEpoch b then σ.sbEp c' + 1 else σ.sbEp c') else σ.sbEp c') = _
          rw [if_pos rfl, hep, hpw]; rfl
        show List.Forall₂ (entRel (σ.fence c' b) c') (σ.sb c')
          ((if pw && sw then SbCand.updSb c.sb (hartAgent c') ((c.sb (hartAgent c')).map SbEnt.bump)
            else c.sb) (hartAgent c'))
        rw [hpw, if_neg (by simp)]
        exact (hsb c').imp (fun {p e} hr => hrel p e hr rfl hs)
      · have hs : (σ.fence c' b).sbEp c' = σ.sbEp c' + 1 := by
          show (if c' = c' then (if fenceEpoch b then σ.sbEp c' + 1 else σ.sbEp c') else σ.sbEp c') = _
          rw [if_pos rfl, hep, hpw]; rfl
        show List.Forall₂ (entRel (σ.fence c' b) c') (σ.sb c')
          ((if pw && sw then SbCand.updSb c.sb (hartAgent c') ((c.sb (hartAgent c')).map SbEnt.bump)
            else c.sb) (hartAgent c'))
        rw [hpw, if_pos rfl, SbCand.updSbEq]
        refine forall2MapRight (hsb c') (fun p e hp hr => ?_)
        obtain ⟨h1, h2, h3, h4⟩ := hr
        have := hep9 c' p hp
        refine ⟨?_, h2, h3, h4⟩
        rw [hs]; simp only [SbEnt.bump]; omega
    · have hs : (σ.fence cpu b).sbEp c' = σ.sbEp c' := by
        show (if c' = cpu then _ else σ.sbEp c') = _
        rw [if_neg hc]
      show List.Forall₂ (entRel (σ.fence cpu b) c') (σ.sb c')
        ((if pw && sw then SbCand.updSb c.sb (hartAgent cpu) ((c.sb (hartAgent cpu)).map SbEnt.bump)
          else c.sb) (hartAgent c'))
      have hne : hartAgent c' ≠ hartAgent cpu := fun he => hc (hartAgentInj he)
      split
      · rw [SbCand.updSbNe _ _ _ _ hne]; exact (hsb c').imp (fun {p e} hr => hrel p e hr rfl hs)
      · exact (hsb c').imp (fun {p e} hr => hrel p e hr rfl hs)
  · show (if pw && sw then SbCand.updSb c.sb (hartAgent cpu) ((c.sb (hartAgent cpu)).map SbEnt.bump)
      else c.sb) i = []
    split
    · rw [SbCand.updSbNe _ _ _ _ (hi cpu)]; exact hoth i hi
    · exact hoth i hi

/-- MachCSL's epoch bump IS the pf label's `pw ∧ sw`, for every barrier but `fence.tso` (whose W→W
half the pf twin parks: `ebarPark`). -/
theorem fenceEpochOfEbar (b : barrier_kind) (hb : b ≠ .Barrier_RISCV_tso) (pr pw sr sw : Bool)
    (hl : ebarLabel b = .LFence pr pw sr sw) : fenceEpoch b = (pw && sw) := by
  cases b <;> simp_all [ebarLabel, ebarNow, fenceEpoch]

/-- MachCSL's W→R drain IS the pf label's `pw ∧ sr` (every barrier; `fence.tso`'s `r,r` half and
`fence.i`'s all-false label do not drain on either side's DATA rule). -/
theorem fenceDrainsOfEbar (b : barrier_kind) (pr pw sr sw : Bool) (hl : ebarLabel b = .LFence pr pw sr sw) :
    fenceDrains b = (pw && sr) := by
  cases b <;> simp_all [ebarLabel, ebarNow, fenceDrains]

/-- **The barrier step's guard from the twin's**: the twin's drain (`pw ∧ sr` ⇒ empty buffer) gives
MachCSL's `fenceDrainsSb` guard — except `fence.i`'s drain on the CURRENT tip machine, a premise
(`hfi`) that [OWN.143] (non-draining `fence.i`) removes; nothing here uses that drain. -/
theorem fenceGuardOf (img : Image) (c : SbCand.CandS) (σ : MState) (cpu : CPU) (b : barrier_kind)
    (pr pw sr sw : Bool) (hl : ebarLabel b = .LFence pr pw sr sw) (hR : rmemP img c σ)
    (hdr : SbCand.drains pw sr = true → c.sb (hartAgent cpu) = [])
    (hfi : fenceIfetch b = true → σ.sb cpu = []) :
    fenceDrainsSb b = true → σ.sb cpu = [] := by
  intro h
  unfold fenceDrainsSb at h
  rcases Bool.or_eq_true_iff.1 h with h | h
  · rw [fenceDrainsOfEbar b pr pw sr sw hl] at h
    have := hdr (by simpa [SbCand.drains] using h)
    have hf := hR.2.2.2.2.1 cpu
    rw [this] at hf
    exact forall2NilRight hf
  · exact hfi h

/-! # 5. The LANDING -/

/-- **F-PW6-1, the realization's MachCSL-strength premise**: at every byte of stamp `t`'s
footprint, every entry of ANOTHER author below `t`'s entry has landed.  MachCSL keeps a byte's
pending entries in ISSUE order across authors (`histOkP`'s pending prefix) and lands an entry only
over landed ones (`MState.landFootOk`), so two harts' same-byte plain stores land in issue order;
RVWMO and `SbCand` let them land in either order (`PROGRESS-PW6.md` §2 F-PW6-1, the S-shape
witness).  For xv6 it is the design's `pendOne` (§2.4: no foreign pending entry at a plain
store's issue). -/
def ForeignBelowLanded (σ : MState) (cpu : CPU) (t : Nat) : Prop :=
  ∀ (a : PAddr) (H : Hist), σ.mem[a]? = some H → ∀ H1 x H2, H = H1 ++ x :: H2 → x.t = t →
    ∀ y ∈ H2, y.tid ≠ hartAgent cpu → (σ.lp y.t).isSome

theorem forall2Get {α β : Type} {R : α → β → Prop} :
    ∀ {l : List α} {m : List β}, List.Forall₂ R l m → ∀ {k : Nat} {b : β}, m[k]? = some b →
      ∃ a, l[k]? = some a ∧ R a b
  | _, _, .nil, _, _, h => by simp at h
  | _, _, .cons hab hr, 0, _, h => by simp at h; subst h; exact ⟨_, rfl, hab⟩
  | _, _, .cons _ hr, k + 1, _, h => by simpa using forall2Get hr (by simpa using h)

theorem forall2GetL {α β : Type} {R : α → β → Prop} :
    ∀ {l : List α} {m : List β}, List.Forall₂ R l m → ∀ {k : Nat} {a : α}, l[k]? = some a →
      ∃ b, m[k]? = some b ∧ R a b
  | _, _, .nil, _, _, h => by simp at h
  | _, _, .cons hab hr, 0, _, h => by simp at h; subst h; exact ⟨_, rfl, hab⟩
  | _, _, .cons _ hr, k + 1, _, h => by simpa using forall2GetL hr (by simpa using h)

/-- Two positions of a pairwise list. -/
theorem pairwiseGet {α : Type} {R : α → α → Prop} :
    ∀ {l : List α}, l.Pairwise R → ∀ {i j : Nat} {x y : α}, l[i]? = some x → l[j]? = some y → i < j → R x y
  | [], _, _, _, _, _, h, _, _ => by simp at h
  | z :: l, hp, i, j, x, y, hi, hj, hij => by
    rw [List.pairwise_cons] at hp
    cases i with
    | zero =>
      cases j with
      | zero => omega
      | succ j =>
        simp at hi hj; subst hi
        exact hp.1 y (List.mem_of_getElem? hj)
    | succ i =>
      cases j with
      | zero => omega
      | succ j => exact pairwiseGet hp.2 (by simpa using hi) (by simpa using hj) (by omega)

/-- The index of a member. -/
theorem idxOfMem {α : Type} {l : List α} {x : α} (h : x ∈ l) : ∃ i : Nat, l[i]? = some x := by
  obtain ⟨i, hi, he⟩ := List.getElem_of_mem h
  exact ⟨i, by rw [List.getElem?_eq_getElem hi, he]⟩

/-- The landed buffer entry leaves both buffers together. -/
theorem forall2FilterErase {β : Type} {R : Nat × Nat → β → Prop} :
    ∀ {l : List (Nat × Nat)} {m : List β}, List.Forall₂ R l m → l.Pairwise (fun p q => p.1 < q.1) →
      ∀ {k : Nat} {p : Nat × Nat}, l[k]? = some p →
        List.Forall₂ R (l.filter (fun q => q.1 != p.1)) (m.eraseIdx k)
  | _, _, .nil, _, _, _, h => by simp at h
  | q :: l, b :: m, .cons hab hr, hp, k, p, h => by
    rw [List.pairwise_cons] at hp
    cases k with
    | zero =>
      simp at h; subst h
      have hl : l.filter (fun q' => q'.1 != q.1) = l := by
        rw [List.filter_eq_self]
        intro q' hq'
        have := hp.1 q' hq'
        simp only [bne_iff_ne, ne_eq]; omega
      simp [hl, hr]
    | succ k =>
      have hpm : p ∈ l := List.mem_of_getElem? (by simpa using h)
      have hne : q.1 ≠ p.1 := by have := hp.1 p hpm; omega
      simp only [List.filter_cons, bne_iff_ne, ne_eq, hne, not_false_eq_true, if_true,
        List.eraseIdx_cons_succ]
      exact List.Forall₂.cons hab (forall2FilterErase hr hp.2 (by simpa using h))

theorem stampByteSome {H : Hist} {t : Nat} : (stampByte H t).isSome ↔ ∃ y ∈ H, y.t = t := by
  unfold stampByte
  rw [Option.isSome_map]
  constructor
  · intro h
    obtain ⟨y, hy⟩ := Option.isSome_iff_exists.1 h
    exact ⟨y, List.mem_of_find?_eq_some hy, by simpa using List.find?_some hy⟩
  · rintro ⟨y, hy, hyt⟩
    rw [List.find?_isSome]
    exact ⟨y, hy, by simp [hyt]⟩

/-- **The landing, on one history, exactly**: the first entry at the landing stamp `t` enters the
landed view on top at its new position `q`. -/
theorem lviewLandExact (lp lp' : LandPos) (t q : Nat) (ht : lp t = none) (ht' : lp' t = some q)
    (hother : ∀ s, s ≠ t → lp' s = lp s) : ∀ (H : Hist), H.Pairwise (coAbove lp) →
      (∀ H1 e H2, H = H1 ++ e :: H2 → e.t = t → ∀ e' ∈ H2, (lp e'.t).isSome) →
      Hist.lview lp' H =
        ((H.find? (fun e => e.t == t)).map (fun x => (⟨q, x.tid, x.v⟩ : HEnt))).toList ++ Hist.lview lp H
  | [], _, _ => rfl
  | x :: H, hco, hlow => by
    rw [List.pairwise_cons] at hco
    have hcong : (∀ y ∈ H, (lp y.t).isSome) → Hist.lview lp' H = Hist.lview lp H := fun hall =>
      Hist.lview_congr lp lp' H (fun y hy => hother y.t (fun hyt => by
        have := hall y hy; rw [hyt, ht] at this; cases this))
    have hnone : (∀ y ∈ H, (lp y.t).isSome) → H.find? (fun e => e.t == t) = none := fun hall => by
      rw [List.find?_eq_none]
      intro y hy hyt
      have := hall y hy
      rw [show y.t = t by simpa using hyt, ht] at this
      cases this
    cases hx : lp x.t with
    | some r =>
      have hall : ∀ y ∈ H, (lp y.t).isSome := fun y hy => by
        have hxy := hco.1 y hy
        unfold coAbove at hxy
        rw [hx] at hxy
        cases hy' : lp y.t with
        | none => rw [hy'] at hxy; exact (hxy : False).elim
        | some _ => rfl
      have hxt : x.t ≠ t := fun h => by rw [h, ht] at hx; cases hx
      rw [List.find?_cons, show (x.t == t) = false by simpa using hxt, hnone hall,
        Hist.lview_cons_landed lp x H hx,
        Hist.lview_cons_landed lp' x H (by rw [hother x.t hxt, hx]), hcong hall]
      rfl
    | none =>
      by_cases hxt : x.t = t
      · have hall := hlow [] x H rfl hxt
        rw [List.find?_cons, show (x.t == t) = true by simpa using hxt,
          Hist.lview_cons_landed lp' x H (by rw [hxt]; exact ht'), Hist.lview_cons_pending lp x H hx,
          hcong hall]
        rfl
      · rw [List.find?_cons, show (x.t == t) = false by simpa using hxt,
          Hist.lview_cons_pending lp' x H (by rw [hother x.t hxt, hx]), Hist.lview_cons_pending lp x H hx,
          lviewLandExact lp lp' t q ht ht' hother H hco.2
            (fun H1 e H2 hH he => hlow (x :: H1) e H2 (by rw [hH]; rfl) he)]

/-- A twin entry's byte at a footprint byte locates the byte in its range. -/
theorem msgByteRange {m : Wmsg} {z : Int} (h : (msgByte m z).isSome) :
    ∃ j, j < m.wmData.length ∧ z = accAddr m.wmPa j := by
  unfold msgByte at h
  split at h
  · rename_i hle
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 h
    have hlt := (List.getElem?_eq_some_iff.1 hv).1
    exact ⟨(z - m.wmPa).toNat, hlt, by unfold accAddr; omega⟩
  · cases h

/-- **THE LANDING ROW**: the twin's `SbPol.epoch` landing of agent `hartAgent cpu`'s `k`-th pending
entry IS a MachCSL landing (`MState.landOk`, `MState.land`) of the matching stamp — given
F-PW6-1's `ForeignBelowLanded` at that stamp. -/
theorem rmemPLand (img : Image) (c : SbCand.CandS) (σ : MState) (cpu : CPU) (k : Nat)
    (hR : rmemP img c σ) (hpol : SbPol.epochOk (c.sb (hartAgent cpu)) k) :
    ∃ p, (σ.sb cpu)[k]? = some p ∧
      (ForeignBelowLanded σ cpu p.1 →
        σ.landOk cpu p.1 ∧ rmemP img (SbCand.nextL c (hartAgent cpu) k) (σ.land cpu p.1)) := by
  obtain ⟨himg, hlog, hlogB, hH, hsb, hoth, hresv, hnd, hok⟩ := hR
  obtain ⟨h1, h2, h3, hndl, hll, hph, hsbA, hord, hep9⟩ := hok
  obtain ⟨e, he⟩ : ∃ e, (c.sb (hartAgent cpu))[k]? = some e :=
    ⟨_, List.getElem?_eq_getElem hpol.1⟩
  obtain ⟨p, hp, hpe⟩ := forall2Get (hsb cpu) he
  obtain ⟨hfs, hrl, htid, hbytes⟩ := hpe
  have hpm : p ∈ σ.sb cpu := List.mem_of_getElem? hp
  obtain ⟨hp1, hp2, hp3, hp4⟩ := (hsbA cpu p.1).1 ⟨p.2, hpm⟩
  have hlpt : σ.lp p.1 = none := lpOf_none_of_not_mem σ.llog p.1 hp4 (by omega)
  refine ⟨p, hp, fun hfor => ?_⟩
  have hokP : σ.okP := ⟨h1, h2, h3, hndl, hll, hph, hsbA, hord, hep9⟩
  -- the guard
  have hland : σ.landOk cpu p.1 := by
    refine ⟨p.2, hpm, ?_, ?_⟩
    · intro q hq
      obtain ⟨k', hk'⟩ := idxOfMem hq
      rcases Nat.lt_trichotomy k' k with hlt | heq | hgt
      · obtain ⟨e', he', hqe'⟩ := forall2GetL (hsb cpu) hk'
        have hfe := (hpol.2 k' e' e hlt he' he).1
        have := hep9 cpu q hq
        have := hep9 cpu p hpm
        rw [hqe'.1, hfs] at hfe
        omega
      · subst heq; rw [hk'] at hp; obtain rfl := Option.some.inj hp; exact Nat.le_refl _
      · exact (pairwiseGet (hord cpu) hp hk' hgt).2
    · intro a H hHa _
      refine ⟨fun c' r hr => ?_, ?_⟩
      · rw [hresv c'] at hr; cases hr
      intro H1 x H2 hHe hxt y hy
      cases hly : σ.lp y.t with
      | some _ => rfl
      | none =>
        exfalso
        have hyH : y ∈ H := by rw [hHe]; simp [hy]
        obtain ⟨hyt, hya⟩ := (h1 a H hHa).2 y hyH
        have hy0 : y.t ≠ 0 := fun h0 => by rw [h0] at hly; simp [MState.lp, lpOf] at hly
        have hyll : y.t ∉ σ.llog := fun hm => by
          have := (lpOf_isSome_iff σ.llog y.t hy0).2 hm
          rw [show lpOf σ.llog y.t = none from hly] at this; cases this
        obtain ⟨c', hc'⟩ := hph y.t (by omega) hyt hyll
        have hyau : y.tid = hartAgent c' := by
          rcases hya with h0 | hya
          · exact absurd h0 hy0
          · rw [hc'] at hya; exact (Option.some.inj hya).symm
        by_cases hcc : c' = cpu
        · subst hcc
          -- an OWN older pending entry at the same byte: rule 1 (the policy's overlap clause)
          obtain ⟨ep', hy'⟩ := (hsbA c' y.t).2 ⟨by omega, hyt, hc', hyll⟩
          obtain ⟨k', hk'⟩ := idxOfMem hy'
          have hcoxy : coAbove σ.lp x y := by
            have hpw := (h1 a H hHa).1
            rw [hHe] at hpw
            rw [List.pairwise_append] at hpw
            exact List.rel_of_pairwise_cons hpw.2.1 hy
          unfold coAbove at hcoxy
          rw [hxt, hlpt, hly] at hcoxy
          have hne : y.t ≠ p.1 := by
            intro hyx
            have hndH := hnd a H hHa
            rw [hHe, List.map_append, List.map_cons] at hndH
            have := (List.nodup_cons.1 (List.nodup_append.1 hndH).2.1).1
            exact this (List.mem_map.2 ⟨y, hy, by rw [hyx, hxt]⟩)
          have hlt : k' < k := by
            rcases Nat.lt_trichotomy k' k with h | h | h
            · exact h
            · subst h; rw [hk'] at hp; obtain rfl := Option.some.inj hp; exact absurd rfl hne
            · have := (pairwiseGet (hord c') hp hk' h).1; simp at this; omega
          obtain ⟨e', he', hqe'⟩ := forall2GetL (hsb c') hk'
          have hov := (hpol.2 k' e' e hlt he' he).2
          apply hov
          have hxin : (msgByte e.msg (paZ a)).isSome := by
            rw [← hbytes a]
            unfold memStamp; rw [hHa, Option.bind_some]
            exact stampByteSome.2 ⟨x, by rw [hHe]; simp, hxt⟩
          have hyin : (msgByte e'.msg (paZ a)).isSome := by
            rw [← hqe'.2.2.2 a]
            unfold memStamp; rw [hHa, Option.bind_some]
            exact stampByteSome.2 ⟨y, hyH, rfl⟩
          obtain ⟨j, hj, hz⟩ := msgByteRange hxin
          exact ⟨j, hj, by rw [← hz]; exact hyin⟩
        · have := hfor a H hHa H1 x H2 hHe hxt y hy (by rw [hyau]; exact fun h => hcc (hartAgentInj h))
          rw [hly] at this; cases this
  refine ⟨hland, ?_⟩
  obtain ⟨_, _, _, hfoot⟩ := id hland
  -- the state map after the landing
  have hll' : σ.llog.length = c.ms.msLog.length := by
    have := congrArg List.length hlog
    simp [landAuthors] at this; omega
  have hauth : σ.log.getD (p.1 - 1) diskAgent = hartAgent cpu := by
    rw [List.getD_eq_getElem?_getD, hp3]; rfl
  have hnl : SbCand.nextL c (hartAgent cpu) k =
      ⟨⟨c.ms.msImg, c.ms.msLog ++ [e.msg],
        updWs c.ms.msWs (hartAgent cpu) (SbCand.landPost (c.ms.msWs (hartAgent cpu)) e (c.ms.msLog.length + 1))⟩,
       SbCand.updSb c.sb (hartAgent cpu) ((c.sb (hartAgent cpu)).eraseIdx k)⟩ := by
    unfold SbCand.nextL; rw [he]
  rw [hnl]
  have hlp' : (σ.land cpu p.1).lp p.1 = some (σ.ltop + 1) := by
    show lpOf (σ.llog ++ [p.1]) p.1 = some (σ.llog.length + 1)
    exact lpOf_snoc_self σ.llog p.1 (by omega) hp4
  refine ⟨himg, ?_, hlogB, ⟨fun a ha => ?_, fun a ha => ?_⟩, fun c' => ?_, fun i hi => ?_, hresv, hnd,
    σ.okP_land cpu p.1 hland hokP⟩
  · show (c.ms.msLog ++ [e.msg]).map Wmsg.wmTid = (landAuthors σ.log (σ.llog ++ [p.1])).map some
    rw [landAuthorsSnoc, List.map_append, List.map_append, hlog, hauth]
    simp [htid]
  · obtain ⟨H, hm, hl⟩ := lviewSomeInv (hH.1 a ha)
    rw [FlatMem.lview_get?]
    show (σ.mem[a]?).map (Hist.lview (lpOf (σ.llog ++ [p.1]))) = _
    rw [hm, Option.map_some]
    congr 1
    rw [lviewLandExact σ.lp (lpOf (σ.llog ++ [p.1])) p.1 (σ.llog.length + 1) hlpt
      (lpOf_snoc_self σ.llog p.1 (by omega) hp4) (fun s hs => lpOf_snoc_ne σ.llog p.1 s hs) H
      (h1 a H hm).1 (fun H1 x H2 hHe hxt => (hfoot a H hm ⟨x, by rw [hHe]; simp, hxt⟩).2 H1 x H2 hHe hxt),
      hl, histOfSnoc]
    have hb := hbytes a
    unfold memStamp at hb
    rw [hm, Option.bind_some] at hb
    unfold stampByte at hb
    cases hf : H.find? (fun e => e.t == p.1) with
    | none =>
      rw [hf] at hb
      rw [← hb]; rfl
    | some x =>
      rw [hf] at hb
      rw [← hb]
      have hxH := List.mem_of_find?_eq_some hf
      have hxt : x.t = p.1 := by simpa using List.find?_some hf
      have hxa : x.tid = hartAgent cpu := by
        rcases ((h1 a H hm).2 x hxH).2 with h0 | hya
        · omega
        · rw [hxt, hp3] at hya; exact (Option.some.inj hya).symm
      simp only [Option.map_some, Option.toList_some, List.singleton_append, htid, Option.getD_some,
        hll', hxa]
  · rw [FlatMem.lview_get?]
    show (σ.mem[a]?).map _ = none
    rw [lviewNoneOf (hH.2 a ha)]; rfl
  · by_cases hc : c' = cpu
    · subst hc
      show List.Forall₂ (entRel σ c') (updCpu σ.sb c' ((σ.sb c').filter (fun q => q.1 != p.1)) c')
        (SbCand.updSb c.sb (hartAgent c') ((c.sb (hartAgent c')).eraseIdx k) (hartAgent c'))
      rw [SbCand.updSbEq]
      simp only [updCpu, if_true]
      exact forall2FilterErase (hsb c') ((hord c').imp (fun h => h.1)) hp
    · show List.Forall₂ (entRel σ c') (updCpu σ.sb cpu ((σ.sb cpu).filter (fun q => q.1 != p.1)) c')
        (SbCand.updSb c.sb (hartAgent cpu) ((c.sb (hartAgent cpu)).eraseIdx k) (hartAgent c'))
      rw [SbCand.updSbNe _ _ _ _ (fun he => hc (hartAgentInj he))]
      simp only [updCpu, hc, if_false]
      exact hsb c'
  · show SbCand.updSb c.sb (hartAgent cpu) _ i = []
    rw [SbCand.updSbNe _ _ _ _ (hi cpu)]
    exact hoth i hi

/-! # 6. LOADS at the landed top: forwarding and the member-latest byte -/

/-- The top byte of the pf projection (the twin's latest write to `z`, else the image). -/
def topByte (img : Image) (log : List Wmsg) (z : Int) : Option (BitVec 8) :=
  (TsoOfPf.histOf img log z).head?.map HEnt.v

theorem findCongr {α : Type} (p q : α → Bool) : ∀ (l : List α), (∀ x ∈ l, p x = q x) → l.find? p = l.find? q
  | [], _ => rfl
  | x :: l, h => by
    rw [List.find?_cons, List.find?_cons, h x List.mem_cons_self,
      findCongr p q l (fun y hy => h y (List.mem_cons_of_mem _ hy))]

/-- The landed top of a history is the head of its landed view. -/
theorem topLLview (lp : LandPos) : ∀ (H : Hist), Hist.topL lp H = (Hist.lview lp H).head?.map HEnt.v
  | [] => rfl
  | x :: H => by
    cases hx : lp x.t with
    | some q =>
      rw [Hist.lview_cons_landed lp x H hx]
      simp [Hist.topL, hx]
    | none =>
      rw [Hist.lview_cons_pending lp x H hx, ← topLLview lp H]
      simp [Hist.topL, hx]

/-- **The exclusive read's bytes** (`FlatMem.topBytesL`'s byte): MachCSL's landed top IS the twin's
member-latest byte. -/
theorem topLEq (img : Image) (c : SbCand.CandS) (σ : MState) (hR : rmemP img c σ) (a : PAddr)
    (ha : inRam a 1) : (σ.mem[a]?).bind (Hist.topL σ.lp) = topByte img c.ms.msLog (paZ a) := by
  obtain ⟨H, hm, hl⟩ := lviewSomeInv (hR.2.2.2.1.1 a ha)
  rw [hm, Option.bind_some, topLLview, hl]
  rfl

/-- The twin's forwarded byte, one entry more. -/
theorem fwdByteSnoc (l : List SbEnt) (e : SbEnt) (z : Int) :
    SbCand.fwdByte (l ++ [e]) z = (msgByte e.msg z).or (SbCand.fwdByte l z) := by
  unfold SbCand.fwdByte
  rw [List.foldl_append]
  rfl

/-- No covering entry: nothing forwarded. -/
theorem fwdByteNone : ∀ (l : List SbEnt) (z : Int), (∀ e ∈ l, msgByte e.msg z = none) →
    SbCand.fwdByte l z = none := by
  intro l z
  induction l using Weak.snocInd with
  | h0 => intro _; rfl
  | hs l e ih =>
    intro h
    rw [fwdByteSnoc, h e (by simp), ih (fun e' he' => h e' (by simp [he']))]
    rfl

/-- The YOUNGEST covering entry is forwarded. -/
theorem fwdByteMax : ∀ (l : List SbEnt) (z : Int) (k : Nat) (e : SbEnt), l[k]? = some e →
    (msgByte e.msg z).isSome → (∀ k' e', k < k' → l[k']? = some e' → msgByte e'.msg z = none) →
    SbCand.fwdByte l z = msgByte e.msg z := by
  intro l z
  induction l using Weak.snocInd with
  | h0 => intro k e h; simp at h
  | hs l e0 ih =>
    intro k e hk hs hmax
    rw [fwdByteSnoc]
    by_cases hkl : k = l.length
    · subst hkl
      rw [List.getElem?_concat_length] at hk
      obtain rfl := Option.some.inj hk
      obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hs
      rw [hv]; rfl
    · have hlt : k < l.length := by
        have := (List.getElem?_eq_some_iff.1 hk).1
        simp at this; omega
      rw [List.getElem?_append_left hlt] at hk
      rw [hmax l.length e0 hlt (List.getElem?_concat_length ..), Option.none_or]
      exact ih k e hk hs (fun k' e' hk' he' => hmax k' e' hk'
        (by rw [List.getElem?_append_left (List.getElem?_eq_some_iff.1 he').1]; exact he'))

/-- **THE PLAIN LOAD'S BYTE at the landed top** (route P's `MState.byteFwd` at `tvn = σ.ltop`, the
read a member TOP read is realized by): the hart's youngest covering pending store's byte (the
twin's `SbCand.fwdByte`), else the member-latest byte (`topByte`). -/
theorem byteFwdTop (img : Image) (c : SbCand.CandS) (σ : MState) (hR : rmemP img c σ) (cpu : CPU)
    (a : PAddr) (ha : inRam a 1) :
    σ.byteFwd cpu σ.ltop a =
      (SbCand.fwdByte (c.sb (hartAgent cpu)) (paZ a)).or (topByte img c.ms.msLog (paZ a)) := by
  obtain ⟨himg, hlog, hlogB, hH, hsb, hoth, hresv, hnd, hok⟩ := hR
  obtain ⟨H, hm, hl⟩ := lviewSomeInv (hH.1 a ha)
  have hhist := (hok.1 a H hm)
  have hord := hok.2.2.2.2.2.2.2.1
  let P : HEnt → Bool := fun e => decide (e.tid = hartAgent cpu) && (σ.sb cpu).any (fun p => p.1 == e.t)
  -- an own pending entry of the buffer at stamp `p.1`, with its index
  have hown : ∀ x ∈ H, P x = true → ∃ (k' : Nat) (p' : Nat × Nat) (e' : SbEnt),
      (σ.sb cpu)[k']? = some p' ∧ p'.1 = x.t ∧
      (c.sb (hartAgent cpu))[k']? = some e' ∧ memStamp σ.mem a x.t = msgByte e'.msg (paZ a) ∧
      (msgByte e'.msg (paZ a)).isSome := by
    intro x hx hP
    simp only [P, Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true, beq_iff_eq] at hP
    obtain ⟨-, p', hp', hpt⟩ := hP
    obtain ⟨k', hk'⟩ := idxOfMem hp'
    obtain ⟨e', he', hr⟩ := forall2GetL (hsb cpu) hk'
    have hms := hr.2.2.2 a
    refine ⟨k', p', e', hk', hpt, he', by rw [← hpt]; exact hms, ?_⟩
    rw [← hms]
    unfold memStamp; rw [hm, Option.bind_some]
    exact stampByteSome.2 ⟨x, hx, hpt.symm⟩
  -- a covering twin entry has its own pending entry in `H`
  have hcov : ∀ (k' : Nat) (p' : Nat × Nat) (e' : SbEnt), (σ.sb cpu)[k']? = some p' →
      (c.sb (hartAgent cpu))[k']? = some e' →
      (msgByte e'.msg (paZ a)).isSome → ∃ x ∈ H, x.t = p'.1 ∧ P x = true := by
    intro k' p' e' hk' he' hs
    obtain ⟨b, hb, hr⟩ := forall2GetL (hsb cpu) hk'
    rw [he'] at hb; obtain rfl := Option.some.inj hb
    have hms := hr.2.2.2 a
    rw [← hms] at hs
    unfold memStamp at hs; rw [hm, Option.bind_some] at hs
    obtain ⟨x, hx, hxt⟩ := stampByteSome.1 hs
    have hpm := List.mem_of_getElem? hk'
    obtain ⟨-, -, hp3, -⟩ := (hok.2.2.2.2.2.2.1 cpu p'.1).1 ⟨p'.2, hpm⟩
    refine ⟨x, hx, hxt, ?_⟩
    have hxa : x.tid = hartAgent cpu := by
      rcases (hhist.2 x hx).2 with h0 | hya
      · have := (hok.2.2.2.2.2.2.1 cpu p'.1).1 ⟨p'.2, hpm⟩; omega
      · rw [hxt, hp3] at hya; exact (Option.some.inj hya).symm
    simp only [P, Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true, beq_iff_eq]
    exact ⟨hxa, p', hpm, hxt.symm⟩
  unfold MState.byteFwd
  rw [hm, Option.bind_some]
  cases hf : H.find? P with
  | none =>
    -- nothing forwarded on either side; the read is the landed top
    have hnone : ∀ e ∈ c.sb (hartAgent cpu), msgByte e.msg (paZ a) = none := by
      intro e he
      obtain ⟨k', hk'⟩ := idxOfMem he
      obtain ⟨p', hp', -⟩ := forall2Get (hsb cpu) hk'
      cases hs : msgByte e.msg (paZ a) with
      | none => rfl
      | some v =>
        obtain ⟨x, hx, -, hP⟩ := hcov k' p' e hp' hk' (by rw [hs]; rfl)
        rw [List.find?_eq_none] at hf
        exact absurd hP (hf x hx)
    show Hist.readP σ.lp (hartAgent cpu) σ.ltop H = _
    rw [fwdByteNone _ _ hnone, Option.none_or]
    unfold Hist.readP
    rw [findCongr (HEnt.visibleP σ.lp (hartAgent cpu) σ.ltop) (fun e => (σ.lp e.t).isSome) H ?_]
    · show Hist.topL σ.lp H = _
      rw [topLLview, hl]; rfl
    · intro x hx
      rw [HEnt.visibleP_eq_landedLe]
      cases hlx : σ.lp x.t with
      | some q =>
        simp [HEnt.landedLe, hlx, lpOf_le σ.llog x.t q hlx]
      | none =>
        simp only [HEnt.landedLe, hlx, Option.any_none, Bool.false_or, Option.isSome_none,
          decide_eq_false_iff_not]
        intro hxa
        have := (σ.okP_own_pending hok cpu a H hm x hx hxa).2 hlx
        rw [List.find?_eq_none] at hf
        exact hf x hx (by simp only [P, Bool.and_eq_true, decide_eq_true_eq]; exact ⟨hxa, this⟩)
  | some y =>
    obtain ⟨hPy, as0, bs, hHy, has⟩ := List.find?_eq_some_iff_append.1 hf
    have hyH : y ∈ H := by rw [hHy]; simp
    obtain ⟨k', p', e', hk', hpt, he', hms, hs⟩ := hown y hyH hPy
    -- `y` is the youngest covering own entry
    have hmax : ∀ k'' e'', k' < k'' → (c.sb (hartAgent cpu))[k'']? = some e'' →
        msgByte e''.msg (paZ a) = none := by
      intro k'' e'' hlt he''
      cases hs'' : msgByte e''.msg (paZ a) with
      | none => rfl
      | some v =>
        exfalso
        obtain ⟨p'', hp'', -⟩ := forall2Get (hsb cpu) he''
        obtain ⟨x, hx, hxt, hPx⟩ := hcov k'' p'' e'' hp'' he'' (by rw [hs'']; rfl)
        have hgt := (pairwiseGet (hord cpu) hk' hp'' hlt).1
        have hxbs : x ∈ bs := by
          rw [hHy] at hx
          rcases List.mem_append.1 hx with hx | hx
          · have := has x hx; rw [hPx] at this; cases this
          · rcases List.mem_cons.1 hx with rfl | hx
            · omega
            · exact hx
        have hco : coAbove σ.lp y x := by
          have hpw := hhist.1
          rw [hHy, List.pairwise_append] at hpw
          exact List.rel_of_pairwise_cons hpw.2.1 hxbs
        have hpend : ∀ z ∈ H, P z = true → σ.lp z.t = none := fun z hz hPz => by
          simp only [P, Bool.and_eq_true, decide_eq_true_eq] at hPz
          exact (σ.okP_own_pending hok cpu a H hm z hz hPz.1).1 hPz.2
        unfold coAbove at hco
        rw [hpend y hyH hPy, hpend x hx hPx] at hco
        omega
    rw [fwdByteMax _ _ k' e' he' hs hmax, ← hms]
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hs
    -- the first entry at `y`'s stamp is `y`
    have hfirst : H.find? (fun e => e.t == y.t) = some y := by
      rw [List.find?_eq_some_iff_append]
      refine ⟨by simp, as0, bs, hHy, fun z hz => ?_⟩
      simp only [Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq]
      intro hzt
      have hzH : z ∈ H := by rw [hHy]; simp [hz]
      have hPz : P z = true := by
        simp only [P, Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true, beq_iff_eq]
        simp only [P, Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true, beq_iff_eq] at hPy
        obtain ⟨hya, q, hq, hqt⟩ := hPy
        refine ⟨?_, q, hq, by rw [hqt, hzt]⟩
        rcases (hhist.2 z hzH).2 with h0 | hza
        · obtain ⟨h1, -⟩ := sbStampBound hok hq; omega
        · rcases (hhist.2 y hyH).2 with h0 | hya'
          · obtain ⟨h1, -⟩ := sbStampBound hok hq; omega
          · rw [hzt, hya'] at hza; rw [← hya]; exact (Option.some.inj hza).symm
      have := has z hz; rw [hPz] at this; cases this
    unfold memStamp
    rw [hm, Option.bind_some]
    unfold stampByte
    rw [hfirst]
    rfl

/-! # 7. The AMO: its guards and its write (lands at once) -/

/-- A RAM footprint is shorter than the address space. -/
theorem ramLen (pa : PAddr) (n : Nat) (h : ramBytes pa n) : n < 2 ^ 64 := by
  cases n with
  | zero => omega
  | succ n => have := ramLt pa (n + 1) h n (by omega); simp only [ramEnd] at this; omega

/-- A buffered entry that does not hit the footprint holds no entry on it. -/
theorem notStampInOf (img : Image) (c : SbCand.CandS) (σ : MState) (cpu : CPU) (pa : PAddr) (n : Nat)
    (hnw : pa.toNat + n ≤ 2 ^ 64) (p : Nat × Nat) (e : SbEnt) (hr : entRel σ cpu p e)
    (hh : ¬ e.hits (paZ pa) n) : ¬ σ.mem.stampIn p.1 pa n := by
  rintro ⟨j, hj, H, hH, x, hx, hxt⟩
  apply hh
  refine ⟨j, hj, ?_⟩
  rw [← paZAddJ pa n j hnw hj, ← hr.2.2.2 (pa + BitVec.ofNat 64 j)]
  unfold memStamp; rw [hH, Option.bind_some]
  exact stampByteSome.2 ⟨x, hx, hxt⟩

/-- **The AMO's buffer guards from the twin's `amoOk`**: MachCSL's exclusive read finds no own
pending entry on its footprint (`MState.sbOverlaps`), and its write may overtake every own pending
entry (`MState.landNowOk`'s second clause: current epoch, other bytes); a release AMO's empty
buffer from the twin's (`hrl`). -/
theorem amoGuardOf (img : Image) (c : SbCand.CandS) (σ : MState) (cpu : CPU) (pa : PAddr) (n : Nat)
    (ak : AK) (hR : rmemP img c σ) (hram : ramBytes pa n)
    (hamo : SbCand.amoOk (c.sb (hartAgent cpu)) (paZ pa) n)
    (hrl : akRel ak = true → c.sb (hartAgent cpu) = []) :
    ¬ σ.sbOverlaps cpu pa n ∧ σ.landNowOk cpu pa n ak := by
  have hnw := noWrapOfRam pa n hram
  have hok := hR.2.2.2.2.2.2.2.2
  have hall : ∀ p ∈ σ.sb cpu, p.2 = σ.sbEp cpu ∧ ¬ σ.mem.stampIn p.1 pa n := by
    intro p hp
    obtain ⟨k', hk'⟩ := idxOfMem hp
    obtain ⟨e, he, hr⟩ := forall2GetL (hR.2.2.2.2.1 cpu) hk'
    obtain ⟨hf0, hh⟩ := hamo e (List.mem_of_getElem? he)
    have := hok.2.2.2.2.2.2.2.2 cpu p hp
    refine ⟨by have := hr.1; omega, notStampInOf img c σ cpu pa n hnw p e hr hh⟩
  refine ⟨fun ⟨p, hp, hin⟩ => (hall p hp).2 hin, fun h => ?_, hall⟩
  have hf := hR.2.2.2.2.1 cpu
  rw [hrl h] at hf
  exact forall2NilRight hf

/-- A landed insert of a fresh stamp moves no other stamp's byte. -/
theorem stampByteInsLanded (lp : LandPos) (e : HEnt) (H : Hist) (t : Nat) (ht : e.t ≠ t) :
    stampByte (Hist.insLanded lp e H) t = stampByte H t := by
  unfold stampByte Hist.insLanded
  rw [List.find?_append, List.find?_cons, show (e.t == t) = false by simpa using ht]
  conv => rhs; rw [← List.takeWhile_append_dropWhile (p := fun x => (lp x.t).isNone) (l := H),
    List.find?_append]

theorem insLandedPerm (lp : LandPos) (e : HEnt) (H : Hist) : (Hist.insLanded lp e H).Perm (e :: H) := by
  unfold Hist.insLanded
  have := List.perm_middle (a := e) (l₁ := H.takeWhile (fun x => (lp x.t).isNone))
    (l₂ := H.dropWhile (fun x => (lp x.t).isNone))
  rw [List.takeWhile_append_dropWhile] at this
  exact this

theorem landBytesIn (m : FlatMem) (lp : LandPos) (pa : PAddr) (n : Nat) (w : BitVec (8 * n)) (t : Nat)
    (h : Agent) (hn : n ≤ 2 ^ 64) {j : Nat} (hj : j < n) :
    (m.landBytes lp pa n w t h)[pa + BitVec.ofNat 64 j]? =
      some (Hist.insLanded lp ⟨t, h, nthByte w j⟩ (m.getD (pa + BitVec.ofNat 64 j) [])) :=
  FlatMem.landBytes_atD m lp pa w t h hn hj

/-- **THE AMO ROW**: the twin's `LRmw` (read at the landed log, write landing at once) by hart
`cpu` is MachCSL's exclusive read at the landed top (`MState.afterExcl`, bytes `r`) followed by its
exclusive write (`MState.storeL`, bytes `w` = the label's write bytes). -/
theorem rmemPRmw (img : Image) (c : SbCand.CandS) (σ : MState) (cpu : CPU) (pa : PAddr) (n : Nat)
    (r w : BitVec (8 * n)) (aq rl : Bool) (ts : List Nat) (rvs wvs : List (BitVec 8)) (k : WmClass)
    (hram : ramBytes pa n) (hd : wvs.length = n) (hb : ∀ j, j < n → wvs[j]? = some (nthByte w j))
    (htop : σ.mem.topBytesL σ.lp pa n r) (hR : rmemP img c σ) :
    rmemP img (SbCand.nextE c (hartAgent cpu) (LRmw aq rl (paZ pa) ts rvs wvs k))
      ((σ.afterExcl cpu pa n r aq).storeL cpu pa n w) := by
  obtain ⟨himg, hlog, hlogB, hH, hsb, hoth, hresv, hnd, hok⟩ := hR
  have hnw := noWrapOfRam pa n hram
  have hn := ramLen pa n hram
  have hll := hok.2.2.2.2.1
  have hok1 : (σ.afterExcl cpu pa n r aq).okP := by
    refine σ.okP_afterExcl cpu pa n r aq hok (fun c' rr hrr a v hv => ?_)
    by_cases hc : c' = cpu
    · rw [hc] at hrr
      have hrr' : rr = snapOf pa n r := by
        have : (σ.afterExcl cpu pa n r aq).resv cpu = some (snapOf pa n r) := by simp [updCpu]
        rw [this] at hrr; exact (Option.some.inj hrr).symm
      subst hrr'
      by_cases hfp : ∃ j, j < n ∧ a = pa + BitVec.ofNat 64 j
      · obtain ⟨j, hj, rfl⟩ := hfp
        rw [snapOf_get? pa n r hn j hj] at hv
        obtain rfl := Option.some.inj hv
        exact htop j hj
      · rw [snapOf_get?_notin pa n r a hfp] at hv; cases hv
    · have : (σ.afterExcl cpu pa n r aq).resv c' = σ.resv c' := by simp [updCpu, hc]
      rw [this, hresv c'] at hrr; cases hrr
  have hno : ¬ othersReserve (σ.afterExcl cpu pa n r aq).resv cpu pa n := by
    rintro ⟨c', hc', rr, hrr, -⟩
    have : (σ.afterExcl cpu pa n r aq).resv c' = σ.resv c' := by simp [updCpu, hc']
    rw [this, hresv c'] at hrr; cases hrr
  have hok2 := (σ.afterExcl cpu pa n r aq).okP_storeL cpu pa n w hno hok1
  have hfresh : ∀ (a : PAddr) (H : Hist), σ.mem[a]? = some H → ∀ e ∈ H, e.t ≠ σ.top + 1 :=
    fun a H hH e he het => by have := stampLeTop hok hH he; omega
  have hlp2 : lpOf (σ.llog ++ [σ.top + 1]) (σ.top + 1) = some (σ.ltop + 1) := σ.okP_snoc_self hok
  have hcong : ∀ (a : PAddr) (H : Hist), σ.mem[a]? = some H →
      Hist.lview (lpOf (σ.llog ++ [σ.top + 1])) H = Hist.lview σ.lp H := fun a H hH =>
    Hist.lview_congr _ _ H (fun e he => σ.okP_lp_snoc hok a H hH e he)
  have hll' : σ.llog.length = c.ms.msLog.length := by
    have := congrArg List.length hlog
    simp [landAuthors] at this; omega
  -- the moved fields
  have hmem : ((σ.afterExcl cpu pa n r aq).storeL cpu pa n w).mem =
      σ.mem.landBytes (lpOf (σ.llog ++ [σ.top + 1])) pa n w (σ.top + 1) (hartAgent cpu) := rfl
  have hlogE : ((σ.afterExcl cpu pa n r aq).storeL cpu pa n w).log = σ.log ++ [hartAgent cpu] := rfl
  have hllE : ((σ.afterExcl cpu pa n r aq).storeL cpu pa n w).llog = σ.llog ++ [σ.top + 1] := rfl
  have hsbE : ((σ.afterExcl cpu pa n r aq).storeL cpu pa n w).sb = σ.sb := rfl
  have hepE : ((σ.afterExcl cpu pa n r aq).storeL cpu pa n w).sbEp = σ.sbEp := rfl
  have hnext : SbCand.nextE c (hartAgent cpu) (LRmw aq rl (paZ pa) ts rvs wvs k) =
      ⟨mnext c.ms (hartAgent cpu) (LRmw aq rl (paZ pa) ts rvs wvs k), c.sb⟩ := rfl
  rw [hnext]
  have hstamp : ∀ (a : PAddr) (t : Nat), t ≠ σ.top + 1 →
      memStamp (σ.mem.landBytes (lpOf (σ.llog ++ [σ.top + 1])) pa n w (σ.top + 1) (hartAgent cpu)) a t =
        memStamp σ.mem a t := by
    intro a t ht
    unfold memStamp
    by_cases hfp : ∃ j, j < n ∧ a = pa + BitVec.ofNat 64 j
    · obtain ⟨j, hj, rfl⟩ := hfp
      rw [landBytesIn _ _ pa n w _ _ (Nat.le_of_lt hn) hj, Option.bind_some, stampByteInsLanded _ _ _ t (Ne.symm ht),
        Std.ExtTreeMap.getD_eq_getD_getElem?]
      cases σ.mem[pa + BitVec.ofNat 64 j]? with
      | none => rfl
      | some H => rfl
    · rw [FlatMem.landBytes_get?_notin _ _ _ _ _ _ _ (fun j hj he => hfp ⟨j, hj, he⟩)]
  refine ⟨himg, ?_, ?_, ⟨fun a ha => ?_, fun a ha => ?_⟩, fun c' => ?_, hoth, fun c' => ?_, ?_, hok2⟩
  · show (c.ms.msLog ++ [(⟨paZ pa, wvs, some (hartAgent cpu), k⟩ : Wmsg)]).map Wmsg.wmTid =
      (landAuthors (σ.log ++ [hartAgent cpu]) (σ.llog ++ [σ.top + 1])).map some
    rw [landAuthorsSnoc, landAuthorsSnocLog σ.log σ.llog _ (fun t ht => hll t ht), List.map_append,
      List.map_append, hlog]
    simp [MState.top]
  · intro a ha
    rw [hlogE] at ha
    rcases List.mem_append.1 ha with ha | ha
    · exact hlogB a ha
    · simp at ha; rw [ha]; exact Nat.le_of_lt (hartAgent_lt cpu)
  · show ((σ.mem.landBytes (lpOf (σ.llog ++ [σ.top + 1])) pa n w (σ.top + 1) (hartAgent cpu)).lview
      (lpOf (σ.llog ++ [σ.top + 1])))[a]? = some (TsoOfPf.histOf img (c.ms.msLog ++
        [(⟨paZ pa, wvs, some (hartAgent cpu), k⟩ : Wmsg)]) (paZ a))
    obtain ⟨H, hm, hl⟩ := lviewSomeInv (hH.1 a ha)
    rw [FlatMem.lview_get?, histOfSnoc]
    by_cases hfp : ∃ j, j < n ∧ a = pa + BitVec.ofNat 64 j
    · obtain ⟨j, hj, rfl⟩ := hfp
      rw [landBytesIn _ _ pa n w _ _ (Nat.le_of_lt hn) hj, getDOfSome hm, Option.map_some,
        Hist.lview_insLanded _ _ hlp2, hcong _ H hm, hl, msgByteIn pa n j wvs _ k hnw hj, hb j hj]
      simp [hll']
    · have hne : ∀ j, j < n → a ≠ pa + BitVec.ofNat 64 j := fun j hj he => hfp ⟨j, hj, he⟩
      rw [FlatMem.landBytes_get?_notin _ _ _ _ _ _ _ hne, hm, Option.map_some, hcong a H hm, hl,
        msgByteOut pa a n wvs _ k hd hne]
  · rw [FlatMem.lview_get?, hmem, FlatMem.landBytes_get?_notin _ _ _ _ _ _ _
      (fun j hj he => ha (by rw [he]; exact hram j hj)), lviewNoneOf (hH.2 a ha)]
    rfl
  · rw [hsbE]
    refine forall2ImpMem (hsb c') ?_
    intro p e hp hr
    refine ⟨by rw [hepE]; exact hr.1, hr.2.1, hr.2.2.1, fun a => ?_⟩
    have := sbStampBound hok hp
    rw [hmem, hstamp a p.1 (by omega)]
    exact hr.2.2.2 a
  · show updCpu (σ.afterExcl cpu pa n r aq).resv cpu none c' = none
    by_cases hc : c' = cpu
    · subst hc; simp [updCpu]
    · simp only [updCpu, hc, if_false]
      exact hresv c'
  · rw [hmem]
    intro a H hH
    by_cases hfp : ∃ j, j < n ∧ a = pa + BitVec.ofNat 64 j
    · obtain ⟨j, hj, rfl⟩ := hfp
      rw [landBytesIn _ _ pa n w _ _ (Nat.le_of_lt hn) hj] at hH
      obtain rfl := Option.some.inj hH
      refine ((insLandedPerm _ _ _).map HEnt.t).nodup_iff.2 ?_
      rw [Std.ExtTreeMap.getD_eq_getD_getElem?]
      cases hm : σ.mem[pa + BitVec.ofNat 64 j]? with
      | none => simp
      | some H0 =>
        simp only [Option.getD_some, List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and]
        exact ⟨fun e he het => hfresh _ H0 hm e he het, hnd _ H0 hm⟩
    · rw [FlatMem.landBytes_get?_notin _ _ _ _ _ _ _ (fun j hj he => hfp ⟨j, hj, he⟩)] at hH
      exact hnd a H hH

/-! # 8. The read side: a TOP read is always enabled and moves only the read side -/

/-- **A plain load at the landed top is enabled** (`evStep`'s plain-read arm: view and coherence
bounds) — whatever the hart's floors, by `MState.okP`'s bound. -/
theorem topLoadEnabled (img : Image) (c : SbCand.CandS) (σ : MState) (hR : rmemP img c σ) (cpu : CPU)
    (pa : PAddr) (n : Nat) : σ.tv cpu ≤ σ.ltop ∧ (σ.hr cpu).cohOk pa n σ.ltop := by
  obtain ⟨a1, -, -, a4⟩ := hR.2.2.2.2.2.2.2.2.2.2.1 cpu
  exact ⟨a1, fun j _ => a4 _⟩

/-- **THE LOAD ROW** (state map): a twin load (forwarding or at the log) by hart `cpu` against
MachCSL's plain read at the landed top — only read sides move. -/
theorem rmemPLoad (img : Image) (c : SbCand.CandS) (σ : MState) (cpu : CPU) (pa : PAddr) (n : Nat)
    (aq : Bool) (base : Int) (ts : List Nat) (vs : List (BitVec 8)) (hR : rmemP img c σ) :
    rmemP img (SbCand.nextE c (hartAgent cpu) (LLoad aq base ts vs)) (σ.afterLoad cpu pa n σ.ltop) := by
  obtain ⟨himg, hlog, hlogB, hH, hsb, hoth, hresv, hnd, hok⟩ := hR
  exact ⟨himg, hlog, hlogB, hH, hsb, hoth, hresv, hnd,
    σ.okP_afterLoad cpu pa n σ.ltop (Nat.le_refl _) hok⟩

/-- **THE I/O ROW** (state map): the twin's inert I/O step against an MMIO access (devices only). -/
theorem rmemPIo (img : Image) (c : SbCand.CandS) (σ : MState) (i : Nat) (kd : IoKind) (base : Int)
    (vs : List (BitVec 8)) (ds : DevStates) (hR : rmemP img c σ) :
    rmemP img (SbCand.nextE c i (LIo kd base vs)) { σ with devs := ds } := hR

/-! # 9. F-PW6-1 — the cross-author landing order -/

/-- **MachCSL's side of F-PW6-1**: two PENDING plain stores of DIFFERENT harts on a common byte
land in ISSUE order — the later-issued one may not land first (`MState.landOk` fails), whatever the
landing policy.  (RVWMO's store order and `SbCand` impose no such order across harts.) -/
theorem landBlockedForeign (σ : MState) (hok : σ.okP) (cpuA cpuB : CPU) (tA tB : Nat) (a : PAddr)
    (H : Hist) (hH : σ.mem[a]? = some H) (xA xB : HEnt) (hxA : xA ∈ H) (hxB : xB ∈ H)
    (htA : xA.t = tA) (htB : xB.t = tB) (hpA : σ.lp tA = none) (hpB : σ.lp tB = none) (hlt : tA < tB) :
    ¬ σ.landOk cpuB tB := by
  rintro ⟨_, _, _, hfoot⟩
  obtain ⟨H1, H2, hsplit⟩ := List.append_of_mem hxB
  have hxA2 : xA ∈ H2 := by
    rw [hsplit] at hxA
    rcases List.mem_append.1 hxA with h | h
    · -- `xA` above `xB`: co order puts the larger stamp first
      exfalso
      have hpw := (hok.1 a H hH).1
      rw [hsplit, List.pairwise_append] at hpw
      have := hpw.2.2 xA h xB List.mem_cons_self
      unfold coAbove at this
      rw [htA, htB, hpA, hpB] at this
      omega
    · rcases List.mem_cons.1 h with h | h
      · subst h; omega
      · exact h
  have := (hfoot a H hH ⟨xB, hxB, htB⟩).2 H1 xB H2 hsplit htB xA hxA2
  rw [htA, hpA] at this
  cases this

/-- **The twin's side of F-PW6-1** (a 2-hart witness, every lawful policy): hart 0 issues `x := 1`,
then hart 1 issues `x := 2`; hart 1's store LANDS FIRST, then hart 0's — the final log (co) is the
reverse of the issue order.  A MachCSL realization of this walk is stuck at the first landing
(`landBlockedForeign`). -/
def wit1Steps : List (Estep × List Nat) :=
  [(⟨0, LStore false 0 [1#8] .WCplain⟩, []), (⟨1, LStore false 0 [2#8] .WCplain⟩, [1, 0])]

theorem wit1Run (pol : SbPol) :
    SbCand.execWfP pol ⟨SbCand.statesOf ⟨⟨fun _ => some 0#8, [], fun _ => wsInit⟩, fun _ => []⟩ wit1Steps,
      wit1Steps.map Prod.fst⟩ :=
  SbCand.runOfB pol _ _ ⟨rfl, fun _ => rfl, fun _ => rfl⟩ (by decide +kernel)

theorem wit1Log :
    (SbCand.statesOf ⟨⟨fun _ => some 0#8, [], fun _ => wsInit⟩, fun _ => []⟩ wit1Steps).getLast?.map
      (·.ms.msLog) =
      some [⟨0, [2#8], some 1, .WCplain⟩, ⟨0, [1#8], some 0, .WCplain⟩] := by
  decide +kernel

#print axioms Weak.SbRealP.rmemPLand
#print axioms Weak.SbRealP.rmemPRmw
#print axioms Weak.SbRealP.byteFwdTop
#print axioms Weak.SbRealP.rmemPIssue
#print axioms Weak.SbRealP.landBlockedForeign
#print axioms Weak.SbRealP.wit1Run

end SbRealP

end Weak
