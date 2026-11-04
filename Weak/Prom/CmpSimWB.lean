/-
Weak/Prom: **completeness S3b — `s{b,h,w,d}.[aq]rl` (Zalasr) and `sc`** (S3b-LRSC).

* `fvOk_deps` (rule 12) and `fvOk_rmw` (rule 3): the two forward views a write records (M2: address ⊔ data view;
  M1: an exclusive write's own timestamp).
* `sim_storeRl` — the Zalasr store-release (unpriv_zalasr.adoc:122–123 "always has a release-RCsc annotation, and
  if the bit aq is set … an acquire-RCsc annotation"): `LStore aq true …`, class `rel`.
* `sim_scOk` — a SUCCESSFUL SC: the reference pairs it with an LR (`scAx`, rvwmo.adoc:114–116); `ExtraInv.res`
  makes that LR the machine's reservation (`pair_resv`); the machine's premises are the atomicity axiom on the
  LR's bytes (`exclOk`, rvwmo.adoc:331–337; for a byte the LR read from the image, the §zalrsc reservation
  condition `resvOk`), every LR source before the SC's write, and rule 8 for the reservation's view.  Post: the
  reservation cleared ("Regardless of success or failure, executing an SC … invalidates any reservation",
  zalrsc.adoc:23–24), `rd` gets the SC's own view (M4).
* `sim_scFail` — a FAILED SC (`LExFail`, no store: rvwmo.adoc:117–118): the reservation cleared, `rd` = 1 with no
  view.  No premise ("these definitions permit an implementation to fail an sc instruction occasionally for any
  reason", zalrsc.adoc:245–246).
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.CmpSimW

namespace Weak.Prom.Cmp

open MachCSL MachCSL.Stdpp Iris.Std
open Weak (Image Dsrc)
open Weak.Prom Weak.Prom.Mach Weak.Prom.Mach.Cert
open Weak.Prom.Ref
open PLabel

variable {T : Test} {trs : List SSt} {ν : Val} {X : Exec} {h : Nat} {sf : SSt}

/-! ## 1. Forward views -/

section fv

variable {s : SSt} {lp : LP} {ws : PState} {prom : GSet Nat}

theorem fut_po (c : HCtx T trs ν X h sf) {se : SEv} (hm : sf.evs[s.evs.length]? = some se) (hii : se.sk.ii = s.ii)
    {s' : SSt} (hfut' : Future s' sf) (hn1 : s'.evs.length = s.evs.length + 1) (hii1 : s'.ii = s.ii + 1) {j : Nat}
    (h1 : s.evs.length < j) (h2 : j < sf.evs.length) : poX X (h, s.evs.length) (h, j) = true := by
  have hjii := fut_ii hfut' hii1 (by rw [hn1]; exact h1) h2
  exact c.po_of hm (List.getElem?_eq_getElem h2) (by omega)

/-- Rule 12: the address ⊔ data view of a store is below every later load reading it. -/
theorem fvOk_deps (c : HCtx T trs ν X h sf) (hinv : SimInv T X ν h sf s lp ws prom) {rs1 rs2 : Nat}
    (hrs1 : rs1 < 32) (hrs2 : rs2 < 32) {se : SEv} (hm : sf.evs[s.evs.length]? = some se)
    (hst : se.sk.kind.isStore = true) (hii : se.sk.ii = s.ii) (hadep : se.sk.adep = (s.rd rs1).2)
    (hddep : se.sk.ddep = (s.rd rs2).2) {s' : SSt} (hfut' : Future s' sf) (hn1 : s'.evs.length = s.evs.length + 1)
    (hii1 : s'.ii = s.ii + 1) :
    fvOk X h s.evs.length sf.evs.length (max (srcsView ws (srcR rs1)) (srcsView ws (srcR rs2))) := by
  intro j' h1 h2 h3 x h4 hsrc
  have hml := (List.getElem?_eq_some_iff.1 hm).1
  have hid := c.id hm
  have hsk := c.sk hm
  have hst' : (X.sk (h, s.evs.length)).kind.isStore = true := by rw [hsk]; exact hst
  obtain ⟨hjid, _, _⟩ := fut_ev c h2
  have hpo2 := fut_po c hm hii hfut' hn1 hii1 h1 h2
  have hk : x - (X.ev (h, j')).pa < (X.sk (h, j')).sz := by rw [touches_iff] at h4; unfold Exec.sk; omega
  have hxk : (X.ev (h, j')).pa + (x - (X.ev (h, j')).pa) = x := by rw [touches_iff] at h4; omega
  have hbg : ∀ r, r < 32 → (∀ d ∈ (s.rd r).2, d ∈ (X.sk (h, s.evs.length)).adep ∨ d ∈ (X.sk (h, s.evs.length)).ddep) →
      ∀ d ∈ (s.rd r).2, gB X.gmo (h, d) (h, j') = true := by
    intro r _ hsub d hd
    obtain ⟨hdid, hdm, hpo1⟩ := pf_po c hinv.wf hinv.fut (hinv.wf.taint r d hd) (Nat.le_refl _) hml
    exact gB_of_ppo c.ref c.io hdid hjid
      (ppo_r12 c.io hdm h3 hid hst' hpo1 hpo2 (hsub d hd) hk (by rw [hxk]; exact hsrc))
  have g1 := hbg rs1 hrs1 (fun d hd => .inl (by rw [hsk, hadep]; exact hd))
  have g2 := hbg rs2 hrs2 (fun d hd => .inr (by rw [hsk, hddep]; exact hd))
  have e1 := domF_bound (domF_srcR hinv.regv hrs1) (fun d hd => vo_le_of_gB (g1 d hd))
  have e2 := domF_bound (domF_srcR hinv.regv hrs2) (fun d hd => vo_le_of_gB (g2 d hd))
  refine ⟨by omega, fun hjs => ?_⟩
  have hj0 : 0 < vo X (h, j') := Nat.lt_of_lt_of_le (Nat.zero_lt_one)
    (voG_st_pos X X.gmo _ ((mem_gmo c.ref _).2 ⟨hjid, Kind.isMem_of_isStore _ hjs⟩) hjs)
  have f1 := domF_lt (domF_srcR hinv.regv hrs1) (fun d hd => vo_lt_of_gB (g1 d hd) hjs) hj0
  have f2 := domF_lt (domF_srcR hinv.regv hrs2) (fun d hd => vo_lt_of_gB (g2 d hd) hjs) hj0
  omega

/-- Rule 3: an AMO's or SC's own timestamp is below every later load reading it (M1). -/
theorem fvOk_rmw (c : HCtx T trs ν X h sf) {se : SEv} (hm : sf.evs[s.evs.length]? = some se)
    (hrmw : se.sk.kind.isRmwW = true) (hii : se.sk.ii = s.ii) {s' : SSt} (hfut' : Future s' sf)
    (hn1 : s'.evs.length = s.evs.length + 1) (hii1 : s'.ii = s.ii + 1) :
    fvOk X h s.evs.length sf.evs.length (vo X (h, s.evs.length)) := by
  intro j' h1 h2 h3 x h4 hsrc
  have hid := c.id hm
  have hsk := c.sk hm
  obtain ⟨hjid, _, _⟩ := fut_ev c h2
  have hpo2 := fut_po c hm hii hfut' hn1 hii1 h1 h2
  have hk : x - (X.ev (h, j')).pa < (X.sk (h, j')).sz := by rw [touches_iff] at h4; unfold Exec.sk; omega
  have hxk : (X.ev (h, j')).pa + (x - (X.ev (h, j')).pa) = x := by rw [touches_iff] at h4; omega
  exact vo_of_gB (gB_of_ppo c.ref c.io hid hjid
    (ppo_r3 c.io (by rw [hsk]; exact hrmw) h3 hpo2 hk (by rw [hxk]; exact hsrc)))

end fv

/-! ## 2. Memory facts -/

/-- Every write by an author satisfying `Q` that `memOf X` holds in a window is a store of `X`. -/
theorem writesInBy_memOf {X : Exec} (hX : rvwmoRef X) {Q : Option Nat → Prop} {x : Nat} {lo hi : Nat}
    (h : writesInBy (memOf X) Q (x : Int) lo hi) :
    ∃ w, w ∈ X.gmo ∧ isSt X w = true ∧ writesB (X.ev w) x = true ∧ lo < vo X w ∧ vo X w ≤ hi ∧ Q (some w.1) := by
  obtain ⟨t, h1, h2, m, hm, hb, hq⟩ := h
  have hlen : t ≤ (memOf X).length := by
    have := (List.getElem?_eq_some_iff.1 hm).1; omega
  obtain ⟨w, hw, hws, hv, hm'⟩ := memG_at X X.gmo (gmo_nodup hX) t (by omega) hlen
  unfold memOf at hm
  rw [hm'] at hm
  cases hm
  rw [msgOf_byteAt hX ((mem_gmo hX w).1 hw).1 hws] at hb
  have ht : touches (X.ev w) x = true := by
    cases htt : touches (X.ev w) x
    · rw [htt] at hb; simp at hb
    · rfl
  refine ⟨w, hw, hws, ?_, by unfold vo; omega, by unfold vo; omega, hq⟩
  simp [writesB, ht]
  exact hws

theorem exclOk_rep (log : List PMsg) (i ts t : Nat) : ∀ (len : Nat) (a : Int),
    (∀ k, k < len → ¬ writesInBy log (fun tid => tid ≠ some i) (a + k) t (ts - 1)) →
      exclOk log i a (List.replicate len t) ts
  | 0, _, _ => trivial
  | n + 1, a, hk => by
    refine ⟨by have := hk 0 (by omega); simpa using this, exclOk_rep log i ts t n (a + 1) (fun k hk' => ?_)⟩
    have := hk (k + 1) (by omega)
    rwa [show a + ((k + 1 : Nat) : Int) = a + 1 + (k : Int) by push_cast; omega] at this

theorem HCtx.alignedEv {T : Test} {trs : List SSt} {ν : Val} {X : Exec} {h : Nat} {sf : SSt}
    (c : HCtx T trs ν X h sf) {j : Nat} {se : SEv} (hj : sf.evs[j]? = some se) (hacc : se.sk.kind.isAcc = true) :
    Ref.aligned (X.ev (h, j)) = true := by
  have := List.all_eq_true.1 (c.condsSf).2 _ (List.mem_of_getElem? hj)
  simp only [hacc, Bool.not_true, Bool.false_or, beq_iff_eq] at this
  rw [c.ev hj]
  simp [Ref.aligned, concEv, this]

/-! ## 3. The SC's tail and rows -/

theorem solo_scTail (img : Image) (M : List PMsg) (i : Nat) (lp : LP) (ws : PState) (prom : GSet Nat) (rd : Nat)
    (srcs : List Dsrc) (hq : lp.q = regWL rd srcs ++ [LExFail, LInstr]) :
    soloSteps litStep img M i (lp, ws, prom) ((regWL rd srcs ++ [LExFail, LInstr]).map (fun l => (l, none)))
      ({ lp with q := [] }, instrE { regWE ws rd srcs with wRes := none }, prom) := by
  have hpop : ∀ (lp : LP) (l : PLabel) (rest : List PLabel), lp.q = l :: rest →
      litStep lp () l { lp with q := rest } () := fun lp l rest hq => by
    show litNext lp l = some _; simp [litNext, hq]
  unfold regWL at hq ⊢
  unfold regWE
  by_cases h0 : rd = 0
  · simp only [h0, if_true, List.nil_append] at hq ⊢
    exact .step _ _ _ _ _ _ _ _ (hpop lp _ _ hq) (.scFail _ _)
      (.step _ _ _ _ _ _ _ _ (hpop _ _ _ rfl) (.instr _ _) (.refl _))
  · simp only [h0, if_false, List.singleton_append] at hq ⊢
    exact .step _ _ _ _ _ _ _ _ (hpop lp _ _ hq) (.regW _ _ _ _)
      (.step _ _ _ _ _ _ _ _ (hpop _ _ _ rfl) (.scFail _ _)
        (.step _ _ _ _ _ _ _ _ (hpop _ _ _ rfl) (.instr _ _) (.refl _)))

theorem machRow_scTail (rd : Nat) (srcs : List Dsrc) :
    machRow ((regWL rd srcs ++ [LExFail, LInstr]).map (fun l => (l, (none : Option Nat)))) = [] := by
  unfold regWL; split <;> simp [machRow, PF.loadsOf, PF.loadLikeTvs]

theorem regWE_sc_fields (ws : PState) (rd : Nat) (srcs : List Dsrc) :
    (instrE { regWE ws rd srcs with wRes := none }).wVrOld = ws.wVrOld ∧
    (instrE { regWE ws rd srcs with wRes := none }).wVwOld = ws.wVwOld ∧
    (instrE { regWE ws rd srcs with wRes := none }).wVrNew = ws.wVrNew ∧
    (instrE { regWE ws rd srcs with wRes := none }).wVwNew = ws.wVwNew ∧
    (instrE { regWE ws rd srcs with wRes := none }).wVcap = ws.wVcap ∧
    (∀ x : Int, coh (instrE { regWE ws rd srcs with wRes := none }) x = coh ws x) ∧
    (instrE { regWE ws rd srcs with wRes := none }).wFwd = ws.wFwd ∧
    (instrE { regWE ws rd srcs with wRes := none }).wVRel = ws.wVRel ∧
    (instrE { regWE ws rd srcs with wRes := none }).wRes = none ∧
    (instrE { regWE ws rd srcs with wRes := none }).wLdv = 0 ∧
    (instrE { regWE ws rd srcs with wRes := none }).wIfv = 0 ∧
    (∀ r, regv (instrE { regWE ws rd srcs with wRes := none }) r = regv (regWE ws rd srcs) r) := by
  unfold regWE; split <;> exact ⟨rfl, rfl, rfl, rfl, rfl, fun _ => rfl, rfl, rfl, rfl, rfl, rfl, fun _ => rfl⟩

/-- `resOk none` after an SC instruction at index `n`. -/
theorem resOk_afterSc {X : Exec} {h n : Nat} (hk : (X.sk (h, n)).kind.isLrSc = true)
    (hnl : (X.sk (h, n)).kind ≠ .lr) : resOk X h (n + 1) none := by
  intro jr hjr hlr
  have : jr ≠ n := fun e => hnl (e ▸ hlr)
  exact ⟨n, by omega, by omega, hk⟩

end Weak.Prom.Cmp
