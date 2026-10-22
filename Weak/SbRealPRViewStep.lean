/-
Weak: **allocproc route P, row P-W6 on the S-R walk — `R-view` ALONG THE REALIZATION** (the producer half of
`SimRelP`'s view conjunct, `Weak/SbRealPRView.lean`).  Lean-only, no Rocq twin.  A PRIMED TWIN: nothing
registered imports this file.

**Spec first.**  Each MachCSL floor moves only where an RVWMO ordering lets it (`MState.fence`: ppo rule 4 via
`fencePost`; the exclusive pair: rules 5/6; a store issue resets the footprint's coherence floors: rule 2's
`po-loc-no-w`); the bounds of `SbRealPRView.RView` are `SbDom`'s GF predicates (from-read successors of the
hart's future loads), so each row's preservation is a riscv.cat fact: `SbDom.fenceBefore` (rule 4),
`SbDom.frOfGmo`, and the weakening lemmas (`dRWk`/`dFWk`/`dCWk`: a longer row has fewer future loads).

  §1  **`rviewFrame`**: a step that moves none of the hart's floors, adds no own write and only extends the twin
      log (another hart's step, a landing's view half, an I/O step, a DMA write, an admin step).
  §2  **`rviewIssue`**: the hart's plain store ISSUE (`MState.issue`: the footprint's floors reset).
  §3  **`rviewFence`**: the hart's barrier (`MState.fence`: `fencePost` delivers `rv` behind an R→R fence and the
      last landed store behind a W→R fence — `dF` delivered to `dR`).
  §4  **`rviewLandOwn`** / `pubSnocNe`: a landing of the hart's own store raises `pub` to its position — the
      write is GF's next one (S-P), realized, so gmo-before every future load behind a W→R fence (rule 4).

The load row (`rv := max rv tvn`, CoRR for `coh`) and the exclusive pair are the next increment.

Spec: FAITHFUL (theorems about the existing models; no xv6 fact, no named input).  Lean-only helpers
`SbRealPRViewStep.*`.
-/
import Weak.SbRealPRView

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Sail Sail.ConcurrencyInterfaceV1 LeanRV64D
open Lbl PfStepTsoMem SbRealP SbRealPView SbRealPRView

namespace SbRealPRViewStep

open SbWalk SbAgree SbReplay SbOrd SpikeSP SbDom SpikeSR

/-! # 1. The frame -/

theorem prefixGet {α : Type} {l l' : List α} (h : l <+: l') {i : Nat} {x : α} (hi : l[i]? = some x) :
    l'[i]? = some x := by
  obtain ⟨T, rfl⟩ := h
  rw [List.getElem?_append_left (lookup_lt_Some hi)]; exact hi

/-- **THE FRAME, the last landed store's bound given**: the hart's floors unchanged, its row only longer with no
new own write, the twin log only extended, the hart's twin buffer only smaller. -/
theorem rviewFrameP (G : Gexec) (w w' : WS) (σ σ' : MState) (cpu : CPU) (hV : RView G w σ cpu)
    (htv : σ'.tv cpu = σ.tv cpu) (hhr : σ'.hr cpu = σ.hr cpu)
    (hpubD : dF G (hartAgent cpu) (w'.rows (hartAgent cpu)).length false (ownPubL (hartAgent cpu) σ'.log σ'.llog))
    (hlen : (w.rows (hartAgent cpu)).length ≤ (w'.rows (hartAgent cpu)).length)
    (hnew : ∀ (W : Geid) (a : Int) (u : BitVec 8), W.1 = hartAgent cpu →
      (w.rows (hartAgent cpu)).length ≤ W.2 → W.2 < (w'.rows (hartAgent cpu)).length → ¬ gwritesByte G W a u)
    (hlog : w.σ.ms.msLog <+: w'.σ.ms.msLog)
    (hsb : ∀ e ∈ w'.σ.sb (hartAgent cpu), ∃ e0 ∈ w.σ.sb (hartAgent cpu), e0.msg = e.msg) :
    RView G w' σ' cpu where
  tvD := by rw [htv]; exact dRWk _ _ _ _ hlen hV.tvD
  rvD := by rw [hhr]; exact dFWk _ _ _ _ _ hlen hV.rvD
  pubD := hpubD
  cohD a := by rw [hhr]; exact dCWk _ _ _ _ _ hlen (hV.cohD a)
  cohSrc a h := by
    rw [hhr] at h ⊢
    obtain ⟨m, hm, h1, h2⟩ := hV.cohSrc a h
    exact ⟨m, prefixGet hlog hm, h1, h2⟩
  cohFwd a h := by
    rw [hhr]
    obtain ⟨e, he, hc⟩ := h
    obtain ⟨e0, he0, hm⟩ := hsb e he
    exact hV.cohFwd a ⟨e0, he0, by rw [hm]; exact hc⟩
  cohOwn a h W u hx hW hwb := by
    rw [hhr] at h ⊢
    by_cases hlt : W.2 < (w.rows W.1).length
    · exact hV.cohOwn a h W u hx hlt hwb
    · exact absurd hwb (hnew W _ u hx (by rw [← hx]; omega) (by rw [← hx]; exact hW))

/-- **THE FRAME**: as `rviewFrameP`, the hart's last landed store unchanged. -/
theorem rviewFrame (G : Gexec) (w w' : WS) (σ σ' : MState) (cpu : CPU) (hV : RView G w σ cpu)
    (htv : σ'.tv cpu = σ.tv cpu) (hhr : σ'.hr cpu = σ.hr cpu)
    (hpub : ownPubL (hartAgent cpu) σ'.log σ'.llog = ownPubL (hartAgent cpu) σ.log σ.llog)
    (hlen : (w.rows (hartAgent cpu)).length ≤ (w'.rows (hartAgent cpu)).length)
    (hnew : ∀ (W : Geid) (a : Int) (u : BitVec 8), W.1 = hartAgent cpu →
      (w.rows (hartAgent cpu)).length ≤ W.2 → W.2 < (w'.rows (hartAgent cpu)).length → ¬ gwritesByte G W a u)
    (hlog : w.σ.ms.msLog <+: w'.σ.ms.msLog)
    (hsb : ∀ e ∈ w'.σ.sb (hartAgent cpu), ∃ e0 ∈ w.σ.sb (hartAgent cpu), e0.msg = e.msg) :
    RView G w' σ' cpu :=
  rviewFrameP G w w' σ σ' cpu hV htv hhr (by rw [hpub]; exact dFWk _ _ _ _ _ hlen hV.pubD) hlen hnew hlog hsb

/-! # 2. The issue -/

/-- The footprint test of `HRead.resetCoh`. -/
def inFp (pa : PAddr) (n : Nat) (a : PAddr) : Bool := (List.range n).any (fun j => a == pa + BitVec.ofNat 64 j)

theorem resetCohAt (hr : HRead) (pa : PAddr) (n : Nat) (a : PAddr) :
    (hr.resetCoh pa n).coh a = if inFp pa n a then 0 else hr.coh a := rfl

/-- **THE ISSUE** of hart `cpu`'s plain store of the footprint `pa .. pa+n-1`: its floors reset, its row grows by
the store (whose GF bytes and twin entry lie in the footprint). -/
theorem rviewIssue (G : Gexec) (hwf : gwf G) (w w' : WS) (σ : MState) (cpu : CPU) (pa : PAddr) (n : Nat)
    (v : BitVec (8 * n)) (hV : RView G w σ cpu) (hok : σ.okP)
    (hrows : (w'.rows (hartAgent cpu)).length = (w.rows (hartAgent cpu)).length + 1)
    (hwr : ∀ (a : PAddr) (u : BitVec 8), gwritesByte G (hartAgent cpu, (w.rows (hartAgent cpu)).length) (paZ a) u →
      inFp pa n a = true)
    (hlog : w.σ.ms.msLog <+: w'.σ.ms.msLog)
    (hsb : ∀ e ∈ w'.σ.sb (hartAgent cpu), (∃ e0 ∈ w.σ.sb (hartAgent cpu), e0.msg = e.msg) ∨
      ∀ a : PAddr, (msgByte e.msg (paZ a)).isSome → inFp pa n a = true) :
    RView G w' (σ.issue cpu pa n v) cpu := by
  have hlen : (w.rows (hartAgent cpu)).length ≤ (w'.rows (hartAgent cpu)).length := by omega
  have htv : (σ.issue cpu pa n v).tv cpu = σ.tv cpu := rfl
  have hhr : (σ.issue cpu pa n v).hr cpu = ((σ.hr cpu).clearAcq).resetCoh pa n := by
    show (if cpu = cpu then _ else _) = _; rw [if_pos rfl]
  have hpub : ownPubL (hartAgent cpu) (σ.issue cpu pa n v).log (σ.issue cpu pa n v).llog =
      ownPubL (hartAgent cpu) σ.log σ.llog := by
    unfold ownPubL
    show ownPub _ (landAuthors (σ.log ++ [hartAgent cpu]) σ.llog) = _
    rw [landAuthorsSnocLog σ.log σ.llog _ hok.2.2.2.2.1]
  refine ⟨?_, ?_, ?_, fun a => ?_, fun a h => ?_, fun a h => ?_, fun a h W u hx hW hwb => ?_⟩
  · rw [htv]; exact dRWk _ _ _ _ hlen hV.tvD
  · rw [hhr]; exact dFWk _ _ _ _ _ hlen hV.rvD
  · rw [hpub]; exact dFWk _ _ _ _ _ hlen hV.pubD
  · rw [hhr, resetCohAt]
    split
    · exact (maxclDC hwf _ _ _).1
    · exact dCWk _ _ _ _ _ hlen (hV.cohD a)
  · rw [hhr, resetCohAt] at h ⊢
    split at h
    · exact absurd rfl h
    · rename_i hf
      rw [if_neg hf]
      obtain ⟨m, hm, h1, h2⟩ := hV.cohSrc a h
      exact ⟨m, prefixGet hlog hm, h1, h2⟩
  · rw [hhr, resetCohAt]
    split
    · rfl
    · rename_i hf
      obtain ⟨e, he, hc⟩ := h
      rcases hsb e he with ⟨e0, he0, hm⟩ | hnewe
      · exact hV.cohFwd a ⟨e0, he0, by rw [hm]; exact hc⟩
      · exact absurd (hnewe a hc) hf
  · rw [hhr, resetCohAt] at h ⊢
    split at h
    · exact absurd rfl h
    · rename_i hf
      rw [if_neg hf]
      by_cases hlt : W.2 < (w.rows W.1).length
      · exact hV.cohOwn a h W u hx hlt hwb
      · have hW2 : W.2 = (w.rows (hartAgent cpu)).length := by rw [hx] at hlt hW; omega
        have hWeq : W = (hartAgent cpu, (w.rows (hartAgent cpu)).length) := Prod.ext hx hW2
        rw [hWeq] at hwb
        exact absurd (hwr a u hwb) hf

/-! # 3. The fence -/

theorem fenceAcqOfEbar (b : barrier_kind) (pr pw sr sw : Bool) (hl : ebarLabel b = .LFence pr pw sr sw) :
    fenceAcq b = (pr && sr) := by
  cases b <;> simp_all [ebarLabel, ebarNow, fenceAcq]

/-- **`dF` DELIVERED**: past a fence with the successor bit `sr` and the window's predecessor bit, a `dF`-bounded
value bounds every future load. -/
theorem dFDeliver {G : Gexec} (x len : Nat) (rd : Bool) (V : Nat) (pr pw sw : Bool)
    (hf : gxLbl G (x, len) = some (LFence pr pw true sw)) (hb : (if rd then pr else pw) = true)
    (h : dF G x len rd V) : dR G x (len + 1) V := by
  intro r a hr
  have hr2 : len < r.2 := by obtain ⟨-, h2, -⟩ := hr; omega
  exact h r a (futWk x len (len + 1) r (by omega) hr) ⟨len, pr, pw, sw, Nat.le_refl _, hr2, hf, hb⟩

/-- **THE FENCE** of hart `cpu` (barrier `b`, GF label `LFence pr pw sr sw` its `ebarLabel`): `fencePost` delivers
`pub` (W→R) and `rv` (R→R) to the floor. -/
theorem rviewFence (G : Gexec) (hwf : gwf G) (w w' : WS) (σ : MState) (cpu : CPU) (b : barrier_kind)
    (pr pw sr sw : Bool) (hV : RView G w σ cpu) (hl : ebarLabel b = .LFence pr pw sr sw)
    (hgl : gxLbl G (hartAgent cpu, (w.rows (hartAgent cpu)).length) = some (LFence pr pw sr sw))
    (hrows : (w'.rows (hartAgent cpu)).length = (w.rows (hartAgent cpu)).length + 1)
    (hlog : w.σ.ms.msLog <+: w'.σ.ms.msLog)
    (hsb : ∀ e ∈ w'.σ.sb (hartAgent cpu), ∃ e0 ∈ w.σ.sb (hartAgent cpu), e0.msg = e.msg) :
    RView G w' (σ.fence cpu b) cpu := by
  have hlen : (w.rows (hartAgent cpu)).length ≤ (w'.rows (hartAgent cpu)).length := by omega
  have hnew : ∀ (W : Geid) (a : Int) (u : BitVec 8), W.1 = hartAgent cpu →
      (w.rows (hartAgent cpu)).length ≤ W.2 → W.2 < (w'.rows (hartAgent cpu)).length → ¬ gwritesByte G W a u := by
    intro W a u hx h1 h2 hwb
    have hW : W = (hartAgent cpu, (w.rows (hartAgent cpu)).length) := Prod.ext hx (by omega)
    obtain ⟨l, bs, vs0, j, hlw, hlwr, -, -⟩ := hwb
    rw [hW, hgl, Option.some.injEq] at hlw
    subst hlw; cases hlwr
  -- the floor after the fence
  have htv : dR G (hartAgent cpu) (w'.rows (hartAgent cpu)).length ((σ.fence cpu b).tv cpu) := by
    have hft : (σ.fence cpu b).tv cpu = MachCSL.fencePost (fenceDrains b) (fenceAcq b) (σ.tv cpu) (σ.hr cpu).rv
        (ownPubL (hartAgent cpu) σ.log σ.llog) := by
      show (if cpu = cpu then _ else _) = _; rw [if_pos rfl]
    rw [hft, hrows]
    unfold MachCSL.fencePost
    have mc := maxclDR hwf (hartAgent cpu) ((w.rows (hartAgent cpu)).length + 1)
    refine mc.2 _ _ (dRWk _ _ _ _ (by omega) hV.tvD) (mc.2 _ _ ?_ ?_)
    · rw [fenceDrainsOfEbar b pr pw sr sw hl]
      cases hd : (pw && sr)
      · exact mc.1
      · simp only [Bool.and_eq_true] at hd
        obtain ⟨rfl, rfl⟩ := hd
        exact dFDeliver _ _ false _ pr true sw hgl rfl hV.pubD
    · rw [fenceAcqOfEbar b pr pw sr sw hl]
      cases ha : (pr && sr)
      · exact mc.1
      · simp only [Bool.and_eq_true] at ha
        obtain ⟨rfl, rfl⟩ := ha
        exact dFDeliver _ _ true _ true pw sw hgl rfl hV.rvD
  have hfr := rviewFrame G w w' σ σ cpu hV rfl rfl rfl hlen hnew hlog hsb
  exact { hfr with tvD := htv }

/-! # 4. The landing -/

theorem ownPubAuxSnocNe (h a : Agent) (hne : a ≠ h) : ∀ (l : List Agent) (b : Nat),
    ownPubAux h (l ++ [a]) b = ownPubAux h l b
  | [], b => by simp [ownPubAux, hne]
  | x :: l, b => by
    simp only [List.cons_append, ownPubAux]
    rw [ownPubAuxSnocNe h a hne l (b + 1)]

theorem ownPubSnocNe (h a : Agent) (hne : a ≠ h) (l : List Agent) : ownPub h (l ++ [a]) = ownPub h l :=
  ownPubAuxSnocNe h a hne l 0

theorem ownPubSnocSelf (h : Agent) (l : List Agent) : ownPub h (l ++ [h]) = l.length + 1 := by
  have h1 := ownPub_le h (l ++ [h])
  have h2 := ownPub_ge h (l ++ [h]) (l.length + 1) (by omega) (by simp)
  simp at h1; omega

/-- A landing by another agent leaves the hart's last landed store. -/
theorem pubLandOther (σ : MState) (cpu : CPU) (t : Nat) (hne : σ.log.getD (t - 1) diskAgent ≠ hartAgent cpu) :
    ownPubL (hartAgent cpu) σ.log (σ.llog ++ [t]) = ownPubL (hartAgent cpu) σ.log σ.llog := by
  unfold ownPubL
  rw [landAuthorsSnoc, ownPubSnocNe _ _ hne]

/-- **THE HART'S OWN LANDING**: its last landed store rises to the landed write `W`, GF's next write (S-P),
realized and a store of the hart: gmo-before every future load behind a W→R fence (rule 4). -/
theorem rviewLandOwn (G : Gexec) (hc : CatH G) (w w' : WS) (σ : MState) (cpu : CPU) (t : Nat)
    (hV : RView G w σ cpu) (hown : σ.log.getD (t - 1) diskAgent = hartAgent cpu)
    (W : Geid) (hW : W ∈ gwrites G) (hgw : gwix G W = σ.llog.length + 1) (hWx : W.1 = hartAgent cpu)
    (hWlt : W.2 < (w.rows (hartAgent cpu)).length) (l : Lbl) (hWl : gxLbl G W = some l) (hWw : lbIsW l = true)
    (hrows : w'.rows (hartAgent cpu) = w.rows (hartAgent cpu))
    (hlog : w.σ.ms.msLog <+: w'.σ.ms.msLog)
    (hsb : ∀ e ∈ w'.σ.sb (hartAgent cpu), ∃ e0 ∈ w.σ.sb (hartAgent cpu), e0.msg = e.msg) :
    RView G w' (σ.land cpu t) cpu := by
  have hlen : (w.rows (hartAgent cpu)).length ≤ (w'.rows (hartAgent cpu)).length := Nat.le_of_eq (by rw [hrows])
  have hnew : ∀ (W' : Geid) (a : Int) (u : BitVec 8), W'.1 = hartAgent cpu →
      (w.rows (hartAgent cpu)).length ≤ W'.2 → W'.2 < (w'.rows (hartAgent cpu)).length →
      ¬ gwritesByte G W' a u := by
    intro W' a u _ h1 h2; rw [hrows] at h2; omega
  have hpub : dF G (hartAgent cpu) (w'.rows (hartAgent cpu)).length false
      (ownPubL (hartAgent cpu) (σ.land cpu t).log (σ.land cpu t).llog) := by
    have : ownPubL (hartAgent cpu) (σ.land cpu t).log (σ.land cpu t).llog = σ.llog.length + 1 := by
      show ownPubL _ σ.log (σ.llog ++ [t]) = _
      unfold ownPubL
      rw [landAuthorsSnoc, hown, ownPubSnocSelf]
      simp [landAuthors]
    rw [this, hrows, ← hgw]
    intro r a hr hwin
    exact frOfGmo hc _ _ r hr a W _ hW
      (fenceBefore hc _ _ false W l hWl hWx hWlt (by simpa using hWw) r hr hwin) (Nat.le_refl _)
  exact rviewFrameP G w w' σ (σ.land cpu t) cpu hV rfl rfl hpub hlen hnew hlog hsb

/-! # 5. The plain load: MachCSL's sources at the cut -/

theorem fwdByteNoneAll : ∀ (l : List SbEnt) (z : Int), SbCand.fwdByte l z = none →
    ∀ e ∈ l, msgByte e.msg z = none := by
  intro l z
  induction l using Weak.snocInd with
  | h0 => intro _ e he; cases he
  | hs l e0 ih =>
    intro h e he
    rw [fwdByteSnoc] at h
    cases h0 : msgByte e0.msg z with
    | some _ => rw [h0] at h; cases h
    | none =>
      rw [h0, Option.none_or] at h
      rcases List.mem_append.1 he with he | he
      · exact ih h e he
      · simp at he; subst he; exact h0

/-- With no own PENDING entry, the source a read takes is the landed view's TsoMem reading. -/
theorem readEntNoOwn (lp : LandPos) (h : Agent) (tv : Nat) : ∀ H : Hist,
    (∀ e ∈ H, lp e.t = none → e.tid ≠ h) →
    (H.find? (HEnt.visibleP lp h tv)).map (fun e => (e.tid, (lp e.t).getD 0)) =
      ((Hist.lview lp H).find? (HEnt.visible h tv)).map (fun e => (e.tid, e.t))
  | [], _ => rfl
  | e :: H, hH => by
    have ih := readEntNoOwn lp h tv H (fun x hx => hH x (List.mem_cons_of_mem _ hx))
    cases hl : lp e.t with
    | none =>
      rw [Hist.lview_cons_pending lp e H hl, List.find?_cons]
      have : HEnt.visibleP lp h tv e = false := by
        simp [HEnt.visibleP, hl, hH e List.mem_cons_self hl]
      rw [this]; exact ih
    | some q =>
      rw [Hist.lview_cons_landed lp e H hl, List.find?_cons, List.find?_cons]
      have : HEnt.visibleP lp h tv e = HEnt.visible h tv ⟨q, e.tid, e.v⟩ := by
        simp [HEnt.visibleP, HEnt.visible, hl]
      rw [this]
      cases HEnt.visible h tv ⟨q, e.tid, e.v⟩
      · exact ih
      · simp [hl]

/-- **MachCSL'S SOURCE OF A NON-FORWARDED BYTE AT A SINGLE-COPY CUT** is the twin's log entry at `t`. -/
theorem readSrcSca (img : Image) (c : SbCand.CandS) (σ : MState) (hR : rmemP img c σ) (cpu : CPU)
    (tvn : Nat) (a : PAddr) (ha : inRam a 1) (t : Nat) (v : BitVec 8)
    (hnf : SbCand.fwdByte (c.sb (hartAgent cpu)) (paZ a) = none)
    (hv : logByte img c.ms.msLog t (paZ a) = some v)
    (hs : scaByte img c.ms.msLog (hartAgent cpu) tvn (paZ a) t) :
    (σ.mem[a]?).bind (Hist.readSrcP σ.lp (hartAgent cpu) tvn) = some (logAuthor c.ms.msLog t, t) := by
  obtain ⟨himg, hlog, hlogB, hH, hsb, hoth, hresv, hnd, hok⟩ := hR
  obtain ⟨H, hm, hl⟩ := lviewSomeInv (hH.1 a ha)
  rw [hm, Option.bind_some]
  have hno : ∀ e ∈ H, σ.lp e.t = none → e.tid ≠ hartAgent cpu := by
    intro x hx hlx hxa
    have hany := (σ.okP_own_pending hok cpu a H hm x hx hxa).2 hlx
    simp only [List.any_eq_true, beq_iff_eq] at hany
    obtain ⟨p', hp', hpt⟩ := hany
    obtain ⟨k', hk'⟩ := idxOfMem hp'
    obtain ⟨e', he', hr⟩ := forall2GetL (hsb cpu) hk'
    have hms := hr.2.2.2 a
    have hs' : (msgByte e'.msg (paZ a)).isSome := by
      rw [← hms]; unfold memStamp; rw [hm, Option.bind_some]
      exact stampByteSome.2 ⟨x, hx, hpt.symm⟩
    have := fwdByteNoneAll _ _ hnf e' (List.mem_of_getElem? he')
    rw [this] at hs'; cases hs'
  unfold Hist.readSrcP Hist.readEntP
  rw [readEntNoOwn σ.lp _ tvn H hno, hl,
    histOfFind img c.ms.msLog (hartAgent cpu) tvn (paZ a) t v (SbRealPView.logAuthored img c σ ⟨himg, hlog, hlogB, hH, hsb,
      hoth, hresv, hnd, hok⟩) hv hs]
  rfl

/-- **MachCSL'S SOURCE OF A BYTE AN OWN PENDING STORE COVERS** is the hart's own entry (stamp `0`). -/
theorem readSrcFwd (img : Image) (c : SbCand.CandS) (σ : MState) (hR : rmemP img c σ) (cpu : CPU)
    (tvn : Nat) (a : PAddr) (ha : inRam a 1)
    (hcov : ∃ e ∈ c.sb (hartAgent cpu), (msgByte e.msg (paZ a)).isSome) :
    ∃ q, (σ.mem[a]?).bind (Hist.readSrcP σ.lp (hartAgent cpu) tvn) = some (hartAgent cpu, q) := by
  obtain ⟨himg, hlog, hlogB, hH, hsb, hoth, hresv, hnd, hok⟩ := hR
  obtain ⟨H, hm, hl⟩ := lviewSomeInv (hH.1 a ha)
  have hhist := hok.1 a H hm
  rw [hm, Option.bind_some]
  let P : HEnt → Bool := fun e => decide (e.tid = hartAgent cpu) && (σ.sb cpu).any (fun p => p.1 == e.t)
  -- a covering twin entry has its own pending entry in `H`
  obtain ⟨e, he, hc⟩ := hcov
  obtain ⟨k', hk'⟩ := idxOfMem he
  obtain ⟨p', hp', hr⟩ := forall2Get (hsb cpu) hk'
  have hms := hr.2.2.2 a
  rw [← hms] at hc
  unfold memStamp at hc; rw [hm, Option.bind_some] at hc
  obtain ⟨x, hx, hxt⟩ := stampByteSome.1 hc
  have hpm := List.mem_of_getElem? hp'
  obtain ⟨-, -, hp3, -⟩ := (hok.2.2.2.2.2.2.1 cpu p'.1).1 ⟨p'.2, hpm⟩
  have hxa : x.tid = hartAgent cpu := by
    rcases (hhist.2 x hx).2 with h0 | hya
    · have := (hok.2.2.2.2.2.2.1 cpu p'.1).1 ⟨p'.2, hpm⟩; omega
    · rw [hxt, hp3] at hya; exact (Option.some.inj hya).symm
  have hPx : P x = true := by
    simp only [P, Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true, beq_iff_eq]
    exact ⟨hxa, p', hpm, hxt.symm⟩
  obtain ⟨y, hy⟩ : ∃ y, H.find? P = some y := by
    cases hf : H.find? P with
    | none => rw [List.find?_eq_none] at hf; exact absurd hPx (hf x hx)
    | some y => exact ⟨y, rfl⟩
  obtain ⟨hPy, as0, bs, hHy, has⟩ := List.find?_eq_some_iff_append.1 hy
  have hyH : y ∈ H := by rw [hHy]; simp
  have hya : y.tid = hartAgent cpu := by
    simp only [P, Bool.and_eq_true, decide_eq_true_eq] at hPy; exact hPy.1
  have hyp : σ.lp y.t = none := by
    simp only [P, Bool.and_eq_true, decide_eq_true_eq] at hPy
    exact (σ.okP_own_pending hok cpu a H hm y hyH hPy.1).1 hPy.2
  -- the first visible entry is `y`
  have hvis : H.find? (HEnt.visibleP σ.lp (hartAgent cpu) tvn) = some y := by
    rw [List.find?_eq_some_iff_append]
    refine ⟨by simp [HEnt.visibleP, hya], as0, bs, hHy, fun z hz => ?_⟩
    have hzH : z ∈ H := by rw [hHy]; simp [hz]
    have hco : coAbove σ.lp z y := by
      have hpw := hhist.1
      rw [hHy, List.pairwise_append] at hpw
      exact hpw.2.2 z hz y List.mem_cons_self
    cases hlz : σ.lp z.t with
    | some q =>
      unfold coAbove at hco; rw [hlz, hyp] at hco; exact hco.elim
    | none =>
      simp only [HEnt.visibleP, hlz, Option.any_none, Bool.false_or, Bool.not_eq_true',
        decide_eq_false_iff_not]
      intro hza
      have hany := (σ.okP_own_pending hok cpu a H hm z hzH hza).2 hlz
      have hPz : P z = true := by
        simp only [P, Bool.and_eq_true, decide_eq_true_eq]; exact ⟨hza, hany⟩
      have := has z hz; rw [hPz] at this; cases this
  unfold Hist.readSrcP Hist.readEntP
  rw [hvis]
  refine ⟨(σ.lp y.t).getD 0, ?_⟩
  simp only [Option.map_some, hya]

/-- A `foldr max` is `0` or one of its entries. -/
theorem foldrMaxCases : ∀ l : List Nat, l.foldr max 0 = 0 ∨ l.foldr max 0 ∈ l
  | [] => .inl rfl
  | x :: l => by
    simp only [List.foldr_cons]
    rcases foldrMaxCases l with h | h
    · rw [h]; exact .inr (by simp)
    · by_cases hle : x ≤ l.foldr max 0
      · rw [Nat.max_eq_right hle]; exact .inr (List.mem_cons_of_mem _ h)
      · rw [Nat.max_eq_left (by omega)]; exact .inr List.mem_cons_self

/-- **A NON-ZERO LOAD STAMP** at `a` comes from a footprint byte `j` at `a`. -/
theorem stampCases (srcs : LoadSrcs) (me : Agent) (pa : PAddr) (n : Nat) (a : PAddr)
    (h : srcs.stamp me pa n a ≠ 0) :
    ∃ j, j < n ∧ a = pa + BitVec.ofNat 64 j ∧ srcs.stampAt me j = srcs.stamp me pa n a := by
  unfold LoadSrcs.stamp at h ⊢
  rcases foldrMaxCases ((List.range n).map
      (fun j => if a = pa + BitVec.ofNat 64 j then srcs.stampAt me j else 0)) with h0 | hm
  · exact absurd h0 h
  · obtain ⟨j, hj, hje⟩ := List.mem_map.1 hm
    by_cases ha : a = pa + BitVec.ofNat 64 j
    · rw [if_pos ha] at hje
      exact ⟨j, List.mem_range.1 hj, ha, hje⟩
    · rw [if_neg ha] at hje; rw [← hje] at h; exact absurd rfl h

theorem stampAtSrcs (m : FlatMem) (lp : LandPos) (h : Agent) (tv : Nat) (pa : PAddr) (n j : Nat) (hj : j < n) :
    (m.loadSrcsP lp h tv pa n).stampAt h j =
      match (m[pa + BitVec.ofNat 64 j]?).bind (Hist.readSrcP lp h tv) with
      | some (tid, t) => if tid = h then 0 else t
      | none => 0 := by
  unfold LoadSrcs.stampAt FlatMem.loadSrcsP
  rw [List.getElem?_map, List.getElem?_range hj]
  simp only [Option.map_some]
  cases (m[pa + BitVec.ofNat 64 j]?).bind (Hist.readSrcP lp h tv) with
  | none => rfl
  | some q => obtain ⟨tid, t⟩ := q; rfl

/-! # 6. The plain load -/

/-- The single-copy cut at `max T (max tv cohMax)` of one byte (`SbRealPView.viewCutOf`'s per-byte step). -/
theorem scaAt (c : SbCand.CandS) (σ : MState) (cpu : CPU) (pa : PAddr) (n T t : Nat) (a : Int)
    (hv : (logByte c.ms.msImg c.ms.msLog t a).isSome) (hvis : scaVis c.ms.msLog (hartAgent cpu) T t)
    (hlater : ∀ t', t < t' → (logByte c.ms.msImg c.ms.msLog t' a).isSome →
      T < t' ∧ σ.tv cpu < t' ∧ (∀ i, i < n → (σ.hr cpu).coh (pa + BitVec.ofNat 64 i) < t') ∧
      ¬ (0 < t' ∧ ∃ m, c.ms.msLog[t' - 1]? = some m ∧ m.wmTid = some (hartAgent cpu))) :
    scaByte c.ms.msImg c.ms.msLog (hartAgent cpu) (max T (max (σ.tv cpu) (cohMax (σ.hr cpu) pa n))) a t := by
  refine ⟨hv, ?_, fun t' htt' hs' hvis' => ?_⟩
  · rcases hvis with h | h
    · exact .inl (by omega)
    · exact .inr h
  · obtain ⟨b1, b2, b3, b4⟩ := hlater t' htt' hs'
    rcases hvis' with h | h
    · have hcmt : cohMax (σ.hr cpu) pa n ≤ t' - 1 :=
        cohFoldLe (σ.hr cpu) pa (t' - 1) _ (fun i hi => by have := b3 i (List.mem_range.1 hi); omega)
      omega
    · exact b4 h

/-- **THE PLAIN LOAD** of hart `cpu` at the cut `tvn = max T (max tv cohMax)` (`SbRealPRView.cutBytesOfRView`'s
`T`): `rv` rises to `tvn` (bounded behind an R→R fence: the cut's GF witness is gmo-before the load, the load
gmo-before every future load behind the fence, rule 4), each coherence floor to the byte's FOREIGN source
(CoRR), own-sourced and forwarded bytes contributing `0`. -/
theorem rviewLoad {N : Nat} {img : Image} {X : Geid → Prop} {dev : List Geid} (G : Gexec) (hc : CatH G)
    (hnd : G.gxGmo.Nodup) (w w' : WS) (σ : MState) (cpu : CPU) (hP : SbOrdR.PInvR N img G X dev w)
    (hR : rmemP img w.σ σ) (hV : RView G w σ cpu)
    (aq : Bool) (base : Int) (ts : List Nat) (vs : List (BitVec 8))
    (hl : gxLbl G (hd w (hartAgent cpu)) = some (LLoad aq base ts vs))
    (pa : PAddr) (n : Nat) (hbase : base = paZ pa) (hram : ramBytes pa n) (hlen : ts.length = n)
    (T : Nat) (hcut : CutBytes w.σ σ cpu pa n base ts vs T)
    (hcohT : ∀ i, i < n → (σ.hr cpu).coh (pa + BitVec.ofNat 64 i) ≤ T)
    (hTw : T = 0 ∨ ∃ s, s ∈ gwrites G ∧ gwix G s = T ∧ gmoLt G s (hd w (hartAgent cpu)))
    (hrows : (w'.rows (hartAgent cpu)).length = (w.rows (hartAgent cpu)).length + 1)
    (hlog : w.σ.ms.msLog <+: w'.σ.ms.msLog)
    (hsb : ∀ e ∈ w'.σ.sb (hartAgent cpu), ∃ e0 ∈ w.σ.sb (hartAgent cpu), e0.msg = e.msg) :
    RView G w' (σ.afterLoad cpu pa n (max T (max (σ.tv cpu) (cohMax (σ.hr cpu) pa n)))) cpu := by
  have hI := hP.inv
  have hpf := hP.pf
  have hW := hP.spw
  have hnw := noWrapOfRam pa n hram
  have hvl : vs.length = ts.length := lblShape G hc.wf _ _ hl
  have himg' : w.σ.ms.msImg = img := hR.1
  have hlen' : (w.rows (hartAgent cpu)).length ≤ (w'.rows (hartAgent cpu)).length := by omega
  have hhr : (σ.afterLoad cpu pa n (max T (max (σ.tv cpu) (cohMax (σ.hr cpu) pa n)))).hr cpu =
      (σ.hr cpu).afterLoad (hartAgent cpu) pa n (max T (max (σ.tv cpu) (cohMax (σ.hr cpu) pa n)))
        (σ.mem.loadSrcsP σ.lp (hartAgent cpu) (max T (max (σ.tv cpu) (cohMax (σ.hr cpu) pa n))) pa n) := by
    show (if cpu = cpu then _ else _) = _; rw [if_pos rfl]
  have hpai : ∀ j, j < n → paZ (pa + BitVec.ofNat 64 j) = accAddr base j := fun j hj => by
    rw [hbase]; exact paZAddJ pa n j hnw hj
  -- the per-byte MachCSL source stamp
  have hstampJ : ∀ (j t : Nat) (v : BitVec 8), j < n → ts[j]? = some t → vs[j]? = some v →
      (σ.mem.loadSrcsP σ.lp (hartAgent cpu) (max T (max (σ.tv cpu) (cohMax (σ.hr cpu) pa n))) pa n).stampAt
        (hartAgent cpu) j = 0 ∨
      ((σ.mem.loadSrcsP σ.lp (hartAgent cpu) (max T (max (σ.tv cpu) (cohMax (σ.hr cpu) pa n))) pa n).stampAt
        (hartAgent cpu) j = t ∧
        SbCand.fwdByte (w.σ.sb (hartAgent cpu)) (accAddr base j) = none ∧
        logByte w.σ.ms.msImg w.σ.ms.msLog t (accAddr base j) = some v ∧
        logAuthor w.σ.ms.msLog t ≠ hartAgent cpu) := by
    intro j t v hj htj hvj
    rw [stampAtSrcs _ _ _ _ _ _ _ hj]
    rcases hcut j t v hj htj hvj with hf | ⟨hnf, hlb, hvis, hlater⟩
    · obtain ⟨q, hq⟩ := readSrcFwd img w.σ σ hR cpu (max T (max (σ.tv cpu) (cohMax (σ.hr cpu) pa n))) _
        (hram j hj) (by rw [hpai j hj]; exact fwdCover _ _ _ hf)
      left; rw [hq]; simp
    · have hsca := scaAt w.σ σ cpu pa n T t (accAddr base j) (by rw [hlb]; rfl) hvis hlater
      have hlb' : logByte img w.σ.ms.msLog t (paZ (pa + BitVec.ofNat 64 j)) = some v := by
        rw [hpai j hj, ← himg']; exact hlb
      have hsca' : scaByte img w.σ.ms.msLog (hartAgent cpu) (max T (max (σ.tv cpu) (cohMax (σ.hr cpu) pa n)))
          (paZ (pa + BitVec.ofNat 64 j)) t := by
        rw [hpai j hj, ← himg']; exact hsca
      have hnf' : SbCand.fwdByte (w.σ.sb (hartAgent cpu)) (paZ (pa + BitVec.ofNat 64 j)) = none := by
        rw [hpai j hj]; exact hnf
      rw [readSrcSca img w.σ σ hR cpu _ _ (hram j hj) t v hnf' hlb' hsca']
      by_cases hau : logAuthor w.σ.ms.msLog t = hartAgent cpu
      · left; simp [hau]
      · right; exact ⟨by simp [hau], hnf, hlb, hau⟩
  -- a non-zero new stamp: a foreign source `t` of a footprint byte `j` at `a`
  have hstampA : ∀ a : PAddr,
      (σ.mem.loadSrcsP σ.lp (hartAgent cpu) (max T (max (σ.tv cpu) (cohMax (σ.hr cpu) pa n))) pa n).stamp
        (hartAgent cpu) pa n a ≠ 0 →
      ∃ j t v, j < n ∧ a = pa + BitVec.ofNat 64 j ∧ ts[j]? = some t ∧ vs[j]? = some v ∧
        (σ.mem.loadSrcsP σ.lp (hartAgent cpu) (max T (max (σ.tv cpu) (cohMax (σ.hr cpu) pa n))) pa n).stamp
          (hartAgent cpu) pa n a = t ∧
        SbCand.fwdByte (w.σ.sb (hartAgent cpu)) (accAddr base j) = none ∧
        logByte w.σ.ms.msImg w.σ.ms.msLog t (accAddr base j) = some v ∧
        logAuthor w.σ.ms.msLog t ≠ hartAgent cpu := by
    intro a hne
    obtain ⟨j, hj, haj, hsj⟩ := stampCases _ _ pa n a hne
    obtain ⟨t, htj⟩ : ∃ t, ts[j]? = some t := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    obtain ⟨v, hvj⟩ : ∃ v, vs[j]? = some v := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    rcases hstampJ j t v hj htj hvj with h0 | ⟨h1, h2, h3, h4⟩
    · rw [h0] at hsj; exact absurd hsj.symm hne
    · exact ⟨j, t, v, hj, haj, htj, hvj, by rw [← hsj, h1], h2, h3, h4⟩
  -- the head's reads
  have hrd : ∀ (j t : Nat) (v : BitVec 8), ts[j]? = some t → vs[j]? = some v →
      greadsByte G (hd w (hartAgent cpu)) (accAddr base j) t v :=
    fun j t v htj hvj => ⟨_, base, ts, vs, j, hl, rfl, htj, hvj, rfl⟩
  have hhdx : (hd w (hartAgent cpu)).1 = hartAgent cpu := rfl
  have hhd2 : (hd w (hartAgent cpu)).2 = (w.rows (hartAgent cpu)).length := rfl
  refine ⟨?_, ?_, ?_, fun a => ?_, fun a h => ?_, fun a h => ?_, fun a h W u hx hWl hwb => ?_⟩
  · -- the floor: unchanged
    exact dRWk _ _ _ _ hlen' hV.tvD
  · -- the read watermark
    rw [hhr]
    show dF G _ _ true (max (σ.hr cpu).rv (max T (max (σ.tv cpu) (cohMax (σ.hr cpu) pa n))))
    have mc := maxclDF hc.wf (hartAgent cpu) (w'.rows (hartAgent cpu)).length true
    have hTd : dF G (hartAgent cpu) (w'.rows (hartAgent cpu)).length true T := by
      rcases hTw with h0 | ⟨s, hs, hgs, hlt⟩
      · rw [h0]; exact mc.1
      · intro r a hr hwin
        have hrg := fenceBefore hc (hartAgent cpu) (w'.rows (hartAgent cpu)).length true _ _ hl hhdx
          (by rw [hhd2]; omega) (by simp [lbIsR]) r hr hwin
        exact frOfGmo hc _ _ r hr a s T hs (SbDom.gmoTrans s _ r hlt hrg) (Nat.le_of_eq hgs.symm)
    refine mc.2 _ _ (dFWk _ _ _ _ _ hlen' hV.rvD) (mc.2 _ _ hTd (mc.2 _ _ ?_ ?_))
    · intro r a hr _
      exact hV.tvD r a (futWk _ _ _ r hlen' hr)
    · have hle : cohMax (σ.hr cpu) pa n ≤ T :=
        cohFoldLe (σ.hr cpu) pa T _ (fun i hi => hcohT i (List.mem_range.1 hi))
      intro r a hr hwin
      exact frBLe r a T _ hle (hTd r a hr hwin)
  · -- the last landed store: unchanged
    exact dFWk _ _ _ _ _ hlen' hV.pubD
  · -- a coherence floor
    rw [hhr]
    show dC G _ _ _ (max ((σ.hr cpu).coh a) (LoadSrcs.stamp _ _ pa n a))
    have mc := maxclDC hc.wf (hartAgent cpu) (w'.rows (hartAgent cpu)).length (paZ a)
    refine mc.2 _ _ (dCWk _ _ _ _ _ hlen' (hV.cohD a)) ?_
    by_cases hs0 : (σ.mem.loadSrcsP σ.lp (hartAgent cpu) (max T (max (σ.tv cpu) (cohMax (σ.hr cpu) pa n)))
        pa n).stamp (hartAgent cpu) pa n a = 0
    · rw [hs0]; exact mc.1
    · obtain ⟨j, t, v, hj, haj, htj, hvj, hst, -, -, -⟩ := hstampA a hs0
      rw [hst]
      intro r hr t2 v2 n2 u2 hrd2 hwb2 hlt2
      obtain ⟨hrx, hr2, aq', base', ts', vs', hlr⟩ := hr
      have hpo : WeakRvwmoGraph.gpo G (hd w (hartAgent cpu)) r :=
        SbHeadHop.gpoOfLbl G _ r _ _ hl hlr (by rw [hhdx, hrx]) (by rw [hhd2]; omega)
      have hpaj : paZ a = accAddr base j := by rw [haj]; exact hpai j hj
      have := SbDom.corr hc (hd w (hartAgent cpu)) r (paZ a) t t2 v v2 hpo
        (fun u hw => plainNe r aq' base' ts' vs' hlr r (paZ a) u hw rfl)
        (by rw [hpaj]; exact hrd j t v htj hvj) hrd2
      omega
  · -- the provenance of a non-zero floor
    rw [hhr] at h ⊢
    show ∃ m, w'.σ.ms.msLog[max ((σ.hr cpu).coh a) (LoadSrcs.stamp _ _ pa n a) - 1]? = some m ∧ _
    change max ((σ.hr cpu).coh a) (LoadSrcs.stamp _ _ pa n a) ≠ 0 at h
    by_cases hle : LoadSrcs.stamp (σ.mem.loadSrcsP σ.lp (hartAgent cpu)
        (max T (max (σ.tv cpu) (cohMax (σ.hr cpu) pa n))) pa n) (hartAgent cpu) pa n a ≤ (σ.hr cpu).coh a
    · rw [Nat.max_eq_left hle] at h ⊢
      obtain ⟨m, hm, h1, h2⟩ := hV.cohSrc a h
      exact ⟨m, prefixGet hlog hm, h1, h2⟩
    · rw [Nat.max_eq_right (by omega)] at h ⊢
      obtain ⟨j, t, v, hj, haj, htj, hvj, hst, -, hlb, hau⟩ := hstampA a h
      rw [hst]
      have hpaj : paZ a = accAddr base j := by rw [haj]; exact hpai j hj
      cases t with
      | zero => rw [hst] at h; exact absurd rfl h
      | succ q =>
        simp only [logByte] at hlb
        cases hm : w.σ.ms.msLog[q]? with
        | none => rw [hm] at hlb; cases hlb
        | some m =>
          rw [hm] at hlb
          refine ⟨m, prefixGet hlog (by simpa using hm), by rw [hpaj]; simp only [Option.bind_some] at hlb; rw [hlb]; rfl, ?_⟩
          intro hmt
          apply hau
          simp only [logAuthor, hm, Option.bind_some, hmt, Option.getD_some]
  · -- a byte an own pending store covers
    rw [hhr]
    show max ((σ.hr cpu).coh a) (LoadSrcs.stamp _ _ pa n a) = 0
    obtain ⟨e, he, hce⟩ := h
    obtain ⟨e0, he0, hm0⟩ := hsb e he
    have hcov : ∃ e ∈ w.σ.sb (hartAgent cpu), (msgByte e.msg (paZ a)).isSome := ⟨e0, he0, by rw [hm0]; exact hce⟩
    have h1 := hV.cohFwd a hcov
    have h2 : LoadSrcs.stamp (σ.mem.loadSrcsP σ.lp (hartAgent cpu)
        (max T (max (σ.tv cpu) (cohMax (σ.hr cpu) pa n))) pa n) (hartAgent cpu) pa n a = 0 := by
      refine Classical.byContradiction fun hne => ?_
      obtain ⟨j, t, v, hj, haj, -, -, -, hnf, -, -⟩ := hstampA a hne
      have hpaj : paZ a = accAddr base j := by rw [haj]; exact hpai j hj
      rw [← hpaj] at hnf
      have := fwdByteNoneAll _ _ hnf e0 he0
      rw [hm0] at this
      rw [this] at hce; cases hce
    rw [h1, h2]; rfl
  · -- a non-zero floor is above every own realized store
    rw [hhr] at h ⊢
    change max ((σ.hr cpu).coh a) (LoadSrcs.stamp _ _ pa n a) ≠ 0 at h
    show gwix G W < max ((σ.hr cpu).coh a) (LoadSrcs.stamp _ _ pa n a)
    have hWne : W.2 < (w.rows (hartAgent cpu)).length := by
      rcases Nat.lt_or_ge W.2 (w.rows (hartAgent cpu)).length with h' | h'
      · exact h'
      · exfalso
        have hW2 : W.2 = (w.rows (hartAgent cpu)).length := by rw [hx] at hWl; omega
        have hWe : W = hd w (hartAgent cpu) := Prod.ext hx hW2
        exact plainNe _ aq base ts vs hl W _ u hwb hWe.symm
    by_cases hle : LoadSrcs.stamp (σ.mem.loadSrcsP σ.lp (hartAgent cpu)
        (max T (max (σ.tv cpu) (cohMax (σ.hr cpu) pa n))) pa n) (hartAgent cpu) pa n a ≤ (σ.hr cpu).coh a
    · rw [Nat.max_eq_left hle] at h ⊢
      exact hV.cohOwn a h W u hx (by rw [hx]; exact hWne) hwb
    · rw [Nat.max_eq_right (by omega)] at h ⊢
      obtain ⟨j, t, v, hj, haj, htj, hvj, hst, -, hlb, hau⟩ := hstampA a h
      rw [hst]
      have hpaj : paZ a = accAddr base j := by rw [haj]; exact hpai j hj
      obtain ⟨lW, -, -, -, hlW, -, -, -⟩ := id hwb
      have hpo : WeakRvwmoGraph.gpo G W (hd w (hartAgent cpu)) :=
        SbHeadHop.gpoOfLbl G W _ lW _ hlW hl hx (by rw [hhd2]; exact hWne)
      have hle2 := (hc.lv _ _ t v (hrd j t v htj hvj)).2 W u (by rw [← hpaj]; exact hwb) (.inr hpo)
      rcases Nat.lt_or_ge (gwix G W) t with hlt | hge
      · exact hlt
      · exfalso
        have heq : gwix G W = t := by omega
        cases t with
        | zero =>
          have := gwixPos G W (gwritesOf G W _ u hc.wf hwb); omega
        | succ q =>
          simp only [logByte] at hlb
          cases hm : w.σ.ms.msLog[q]? with
          | none => rw [hm] at hlb; cases hlb
          | some m =>
            obtain ⟨n0, -, hg0, hgw0, htid0, -⟩ := logPos hI hpf hW hnd (q + 1) m (by omega) (by simpa using hm)
            have hWn : W = n0 := SbOrd.gwixInj G W n0 (gwritesOf G W _ u hc.wf hwb) (List.mem_of_getElem? hg0)
              (by rw [heq, hgw0])
            apply hau
            simp only [logAuthor, hm, Option.bind_some, htid0, Option.getD_some]
            rw [← hWn]; exact hx

/-! # 7. The exclusive pair (an AMO, `sc`) -/

/-- **THE EXCLUSIVE PAIR** of hart `cpu` (`MState.afterExcl` at the landed top, admin steps that move no floor,
`MState.storeL` landing at once): the row's event `A` is GF's next write (S-P), so `rv := ltop` is the position of a
write gmo-before `A` and `A`'s position bounds `pub` and (`.aq`) the floor (rules 4 and 5); the footprint's floors
reset. -/
theorem rviewExcl (G : Gexec) (hc : CatH G) (hnd : G.gxGmo.Nodup) (w w' : WS) (σ σ1 : MState) (cpu : CPU)
    (pa : PAddr) (n : Nat) (r : BitVec (8 * n)) (v : BitVec (8 * n)) (acq : Bool) (hV : RView G w σ cpu)
    (hok : σ.okP) (lA : Lbl) (hgl : gxLbl G (hartAgent cpu, (w.rows (hartAgent cpu)).length) = some lA)
    (hR : lbIsR lA = true) (hWr : lbIsW lA = true) (hacq : acq = true → lbAq lA = true)
    (hAw : (hartAgent cpu, (w.rows (hartAgent cpu)).length) ∈ gwrites G)
    (hAgw : gwix G (hartAgent cpu, (w.rows (hartAgent cpu)).length) = σ.ltop + 1)
    (hpre : σ.ltop = 0 ∨ ∃ W0, W0 ∈ gwrites G ∧ gwix G W0 = σ.ltop ∧
      gmoLt G W0 (hartAgent cpu, (w.rows (hartAgent cpu)).length))
    (h1tv : σ1.tv = (σ.afterExcl cpu pa n r acq).tv) (h1hr : σ1.hr = (σ.afterExcl cpu pa n r acq).hr)
    (h1log : σ1.log = σ.log) (h1ll : σ1.llog = σ.llog)
    (hrows : (w'.rows (hartAgent cpu)).length = (w.rows (hartAgent cpu)).length + 1)
    (hwr : ∀ (a : PAddr) (u : BitVec 8), gwritesByte G (hartAgent cpu, (w.rows (hartAgent cpu)).length) (paZ a) u →
      inFp pa n a = true)
    (hlog : w.σ.ms.msLog <+: w'.σ.ms.msLog)
    (hsb : ∀ e ∈ w'.σ.sb (hartAgent cpu), ∃ e0 ∈ w.σ.sb (hartAgent cpu), e0.msg = e.msg) :
    RView G w' (σ1.storeL cpu pa n v) cpu := by
  have hlen : (w.rows (hartAgent cpu)).length ≤ (w'.rows (hartAgent cpu)).length := by omega
  have hA : (hartAgent cpu, (w.rows (hartAgent cpu)).length).1 = hartAgent cpu := rfl
  have hAlt : (hartAgent cpu, (w.rows (hartAgent cpu)).length).2 < (w'.rows (hartAgent cpu)).length := by
    show _ < _; omega
  have hhr1 : σ1.hr cpu = ⟨σ.ltop, (σ.hr cpu).coh, acq⟩ := by
    rw [h1hr]; show (if cpu = cpu then _ else _) = _; rw [if_pos rfl]; rfl
  have hltop1 : σ1.ltop = σ.ltop := by show σ1.llog.length = σ.llog.length; rw [h1ll]
  have htop1 : σ1.top = σ.top := by show σ1.log.length = σ.log.length; rw [h1log]
  have htv2 : (σ1.storeL cpu pa n v).tv cpu = if acq then σ.ltop + 1 else σ.tv cpu := by
    show (if cpu = cpu then (if (σ1.hr cpu).acq then σ1.ltop + 1 else σ1.tv cpu) else _) = _
    rw [if_pos rfl, hhr1, hltop1]
    cases acq
    · show σ1.tv cpu = σ.tv cpu
      rw [h1tv]; show (if cpu = cpu then (if false = true then σ.ltop else σ.tv cpu) else _) = _; simp
    · rfl
  have hhr2 : (σ1.storeL cpu pa n v).hr cpu = ((⟨σ.ltop, (σ.hr cpu).coh, acq⟩ : HRead).clearAcq).resetCoh pa n := by
    show (if cpu = cpu then _ else _) = _; rw [if_pos rfl, hhr1]
  have hpub2 : ownPubL (hartAgent cpu) (σ1.storeL cpu pa n v).log (σ1.storeL cpu pa n v).llog = σ.ltop + 1 := by
    show ownPubL _ (σ1.log ++ [hartAgent cpu]) (σ1.llog ++ [σ1.top + 1]) = _
    unfold ownPubL
    rw [landAuthorsSnoc, h1log, h1ll, htop1]
    have hget : (σ.log ++ [hartAgent cpu]).getD (σ.top + 1 - 1) diskAgent = hartAgent cpu := by
      simp [MState.top]
    rw [hget, landAuthorsSnocLog σ.log σ.llog _ hok.2.2.2.2.1, ownPubSnocSelf]
    simp [landAuthors]
  -- the event is gmo-before every future load behind a fence of the right kind, or after `.aq`
  have hbefore : ∀ (rd : Bool) (rr : Geid), fut G (hartAgent cpu) (w'.rows (hartAgent cpu)).length rr →
      fwin G (hartAgent cpu) (w'.rows (hartAgent cpu)).length rd rr →
      gmoLt G (hartAgent cpu, (w.rows (hartAgent cpu)).length) rr := by
    intro rd rr hr hw
    refine fenceBefore hc _ _ rd _ lA hgl hA hAlt ?_ rr hr hw
    cases rd <;> simp [hR, hWr]
  refine ⟨?_, ?_, ?_, fun a => ?_, fun a h => ?_, fun a h => ?_, fun a h W u hx hW hwb => ?_⟩
  · rw [htv2]
    cases hq : acq
    · exact dRWk _ _ _ _ hlen hV.tvD
    · intro rr a hr
      have hlt := acqBefore hc _ _ _ lA hgl hA hAlt hR (hacq hq) rr hr
      exact frOfGmo hc _ _ rr hr a _ _ hAw hlt (Nat.le_of_eq hAgw.symm)
  · rw [hhr2]
    show dF G _ _ true σ.ltop
    rcases hpre with h0 | ⟨W0, hW0, hgw0, hlt0⟩
    · rw [h0]; exact (maxclDF hc.wf _ _ true).1
    · intro rr a hr hw
      exact frOfGmo hc _ _ rr hr a W0 _ hW0 (SbDom.gmoTrans W0 _ rr hlt0 (hbefore true rr hr hw))
        (Nat.le_of_eq hgw0.symm)
  · rw [hpub2]
    intro rr a hr hw
    exact frOfGmo hc _ _ rr hr a _ _ hAw (hbefore false rr hr hw) (Nat.le_of_eq hAgw.symm)
  · rw [hhr2, resetCohAt]
    split
    · exact (maxclDC hc.wf _ _ _).1
    · exact dCWk _ _ _ _ _ hlen (hV.cohD a)
  · rw [hhr2, resetCohAt] at h ⊢
    split at h
    · exact absurd rfl h
    · rename_i hf
      rw [if_neg hf]
      obtain ⟨m, hm, h1, h2⟩ := hV.cohSrc a h
      exact ⟨m, prefixGet hlog hm, h1, h2⟩
  · rw [hhr2, resetCohAt]
    split
    · rfl
    · obtain ⟨e, he, hce⟩ := h
      obtain ⟨e0, he0, hm0⟩ := hsb e he
      exact hV.cohFwd a ⟨e0, he0, by rw [hm0]; exact hce⟩
  · rw [hhr2, resetCohAt] at h ⊢
    split at h
    · exact absurd rfl h
    · rename_i hf
      rw [if_neg hf]
      by_cases hlt : W.2 < (w.rows W.1).length
      · exact hV.cohOwn a h W u hx hlt hwb
      · have hW2 : W.2 = (w.rows (hartAgent cpu)).length := by rw [hx] at hlt hW; omega
        have hWeq : W = (hartAgent cpu, (w.rows (hartAgent cpu)).length) := Prod.ext hx hW2
        rw [hWeq] at hwb
        exact absurd (hwr a u hwb) hf

/-! # 8. Boot -/

/-- **AT POWER-ON** (every floor `0`, nothing landed): `R-view` holds at every walk state. -/
theorem rviewBoot (G : Gexec) (hwf : gwf G) (w : WS) (σ : MState) (cpu : CPU) (htv : σ.tv cpu = 0)
    (hrv : (σ.hr cpu).rv = 0) (hcoh : ∀ a, (σ.hr cpu).coh a = 0) (hll : σ.llog = []) :
    RView G w σ cpu where
  tvD := by rw [htv]; exact (maxclDR hwf _ _).1
  rvD := by rw [hrv]; exact (maxclDF hwf _ _ _).1
  pubD := by
    have : ownPubL (hartAgent cpu) σ.log σ.llog = 0 := by unfold ownPubL; rw [hll]; rfl
    rw [this]; exact (maxclDF hwf _ _ _).1
  cohD a := by rw [hcoh a]; exact (maxclDC hwf _ _ _).1
  cohSrc a h := absurd (hcoh a) h
  cohFwd a _ := hcoh a
  cohOwn a h := absurd (hcoh a) h

#print axioms Weak.SbRealPRViewStep.rviewExcl
#print axioms Weak.SbRealPRViewStep.rviewLoad
#print axioms Weak.SbRealPRViewStep.readSrcSca
#print axioms Weak.SbRealPRViewStep.readSrcFwd
#print axioms Weak.SbRealPRViewStep.rviewIssue
#print axioms Weak.SbRealPRViewStep.rviewFence
#print axioms Weak.SbRealPRViewStep.rviewLandOwn

end SbRealPRViewStep

end Weak
