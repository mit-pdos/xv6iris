/-
Weak/Prom: **completeness S3a — simulating FENCE and FENCE.TSO** (rule 4, rvwmo.adoc:286; FENCE.TSO as its two
halves `fence r,rw` + `fence w,w`, Ref.lean `rule4`).

A fence raises `vrNew` (if `sr`) and `vwNew` (if `sw`) to `max (pr ? vrOld) (pw ? vwOld)`; `vrOld` (`vwOld`) is
dominated by a past load (store), which is in the fence's predecessor set, and every future load (store) after the
fence is in its successor set, so rule 4 orders them in gmo (`fence_le`).
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.CmpSimN

namespace Weak.Prom.Cmp

open MachCSL MachCSL.Stdpp Iris.Std
open Weak (Image Dsrc)
open Weak.Prom Weak.Prom.Mach Weak.Prom.Mach.Cert
open Weak.Prom.Ref
open PLabel

variable {T : Test} {trs : List SSt} {ν : Val} {X : Exec} {h : Nat} {sf : SSt}

theorem prefix_get {l1 l2 : List SEv} (hp : l1 <+: l2) {k : Nat} {x : SEv} (h : l1[k]? = some x) : l2[k]? = some x := by
  obtain ⟨tl, rfl⟩ := hp
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.1 h).1]; exact h

/-- A past event's index facts. -/
theorem past_ii {s : SSt} (hwf : SymWf s) (hfut : Future s sf) {e : Nat} (he : e < s.evs.length) :
    ∃ se, sf.evs[e]? = some se ∧ se.sk.ii < s.ii :=
  ⟨s.evs[e], prefix_get hfut.evs (List.getElem?_eq_getElem he),
    hwf.iiLt e _ (List.getElem?_eq_getElem he)⟩

/-- RULE 4 FROM A FENCE AT THE CURRENT INSTRUCTION. -/
theorem fence_le (c : HCtx T trs ν X h sf) {s : SSt} (hwf : SymWf s) (hfut : Future s sf) {fs : FenceSet}
    {m : Nat} {fe : SEv} (hm : sf.evs[m]? = some fe) (hfk : fe.sk.kind = .fence fs) (hfii : fe.sk.ii = s.ii)
    {j : Nat} (hjl : j < sf.evs.length) (hjii : s.ii < sf.evs[j].sk.ii)
    (hjm : (X.sk (h, j)).kind.isMem = true) (hsucc : inSucc X.sk (isIo X) fs (h, j) = true) {v : Nat}
    (hv : domF (fun e => vo X (h, e)) (fun e => e < s.evs.length ∧ (X.sk (h, e)).kind.isMem = true ∧
      inPred X.sk (isIo X) fs (h, e) = true) v) :
    v ≤ vo X (h, j) ∧ ((X.sk (h, j)).kind.isStore = true → v < vo X (h, j)) := by
  obtain ⟨hjid, hsk, _⟩ := fut_ev c hjl
  have hord : ∀ e, e < s.evs.length → (X.sk (h, e)).kind.isMem = true → inPred X.sk (isIo X) fs (h, e) = true →
      gB X.gmo (h, e) (h, j) = true := by
    intro e he hem hp
    obtain ⟨se, hse, hii⟩ := past_ii hwf hfut he
    have h1 : poX X (h, e) (h, m) = true := c.po_of hse hm (by omega)
    have h2 : poX X (h, m) (h, j) = true := c.po_of hm (List.getElem?_eq_getElem hjl) (by omega)
    exact gB_of_ppo c.ref c.io (c.id hse) hjid (ppo_r4 hem hjm (c.id hm) (by rw [c.sk hm]; exact hfk) h1 h2 hp hsucc)
  refine ⟨domF_bound hv (fun e ⟨he, hem, hp⟩ => vo_le_of_gB (hord e he hem hp)), fun hst => ?_⟩
  exact domF_lt hv (fun e ⟨he, hem, hp⟩ => vo_lt_of_gB (hord e he hem hp) hst)
    (by have := voG_st_pos X X.gmo (h, j) (c.gmo_of (List.getElem?_eq_getElem hjl) (by rw [← hsk]; exact hjm))
          hst; unfold vo; omega)

/-- `vrOld` is dominated by past loads in the predecessor set of a fence with `pr`. -/
theorem domF_rOld (c : HCtx T trs ν X h sf) {s : SSt} {ws : PState}
    (hro : domF (fun j => vo X (h, j)) (fun j => j < s.evs.length ∧ (X.sk (h, j)).kind.isLoad = true) ws.wVrOld)
    {fs : FenceSet} (hpr : fs.pr = true) :
    domF (fun e => vo X (h, e)) (fun e => e < s.evs.length ∧ (X.sk (h, e)).kind.isMem = true ∧
      inPred X.sk (isIo X) fs (h, e) = true) ws.wVrOld :=
  domF_mono hro (fun e ⟨he, hl⟩ => ⟨he, Kind.isMem_of_isLoad _ hl, by simp [inPred, hl, c.io', hpr]⟩)

theorem domF_wOld (c : HCtx T trs ν X h sf) {s : SSt} {ws : PState}
    (hwo : domF (fun j => vo X (h, j)) (fun j => j < s.evs.length ∧ (X.sk (h, j)).kind.isStore = true) ws.wVwOld)
    {fs : FenceSet} (hpw : fs.pw = true) :
    domF (fun e => vo X (h, e)) (fun e => e < s.evs.length ∧ (X.sk (h, e)).kind.isMem = true ∧
      inPred X.sk (isIo X) fs (h, e) = true) ws.wVwOld :=
  domF_mono hwo (fun e ⟨he, hl⟩ => ⟨he, Kind.isMem_of_isStore _ hl, by simp [inPred, hl, c.io', hpw]⟩)

/-- The fence's raise value `max (pr ? vrOld) (pw ? vwOld)` is dominated by its predecessor set. -/
theorem domF_fenceV (c : HCtx T trs ν X h sf) {s : SSt} {ws : PState} {prom : GSet Nat} {lp' : LP}
    (hinv : SimInv T X ν h sf s lp' ws prom) (fs : FenceSet) :
    domF (fun e => vo X (h, e)) (fun e => e < s.evs.length ∧ (X.sk (h, e)).kind.isMem = true ∧
      inPred X.sk (isIo X) fs (h, e) = true)
      (max (if fs.pr then ws.wVrOld else 0) (if fs.pw then ws.wVwOld else 0)) := by
  refine domF_max ?_ ?_
  · cases hp : fs.pr
    · exact domF_zero _ _
    · exact domF_rOld c hinv.vrOld hp
  · cases hp : fs.pw
    · exact domF_zero _ _
    · exact domF_wOld c hinv.vwOld hp

theorem inSucc_load {X : Exec} (hio : X.io = []) {fs : FenceSet} (hsr : fs.sr = true) {j : EvId}
    (hl : (X.sk j).kind.isLoad = true) : inSucc X.sk (isIo X) fs j = true := by
  simp [inSucc, hl, isIo_nil X hio, hsr]

theorem inSucc_store {X : Exec} (hio : X.io = []) {fs : FenceSet} (hsw : fs.sw = true) {j : EvId}
    (hl : (X.sk j).kind.isStore = true) : inSucc X.sk (isIo X) fs j = true := by
  simp [inSucc, hl, isIo_nil X hio, hsw]

section instrs

variable {s : SSt} {lp : LP} {ws : PState} {prom : GSet Nat}

/-- `FENCE pred,succ`. -/
theorem sim_fence (c : HCtx T trs ν X h sf) (hinv : SimInv T X ν h sf s lp ws prom) {fs : FenceSet}
    (hi : (T.prog h)[s.pc]? = some (.fence fs)) {s' : SSt}
    (hs : stepI h (T.prog h).length s (.fence fs) = .next s') (hfut : Future s' sf) :
    StepOk T X ν h sf s lp ws prom s' := by
  have hwf' := (symWf_step h _ hinv.wf _).1 s' hs
  simp only [stepI, Ref.StepR.next.injEq] at hs
  subst hs
  have hm : sf.evs[s.evs.length]? = some ⟨{ kind := .fence fs, ii := s.ii, sz := 0 }, .c 0, .c 0⟩ :=
    prefix_get hfut.evs (by simp)
  have hlabs : ∀ l, instrNext lp.prog.length lp (.fence fs) l =
      go1 lp lp.regs (lp.pc + 1) [LFence fs.pr fs.pw fs.sr fs.sw, LInstr] l := fun l => rfl
  have hsolo := solo_go1' (testImg T) (memOf X) h lp ws prom _ lp.regs (lp.pc + 1)
    [LFence fs.pr fs.pw fs.sr fs.sw, LInstr] (by simp) hinv.q (lpi_of hinv hi) hlabs (by simp [afOk])
  have hn' : (s.emit ⟨{ kind := .fence fs, ii := s.ii, sz := 0 }, .c 0, .c 0⟩).adv.evs.length =
      s.evs.length + 1 := by simp
  refine ⟨_, _, _, _, hsolo, ?_, ?_, keepRR_fold _ _⟩  -- S3b: `keepRR`
  · rw [machRow_af _ (by simp [afOk]), hn', rowSeg_one]
    rw [c.sk hm]; rfl
  have hfold : [LFence fs.pr fs.pw fs.sr fs.sw, LInstr].foldl afEff ws =
      instrE (fencePost ws fs.pr fs.pw fs.sr fs.sw) := rfl
  rw [hfold]
  have hv := domF_fenceV c hinv fs
  refine inv_nomem hinv hwf' hfut (by simp) ?_ (by rw [lp_after, hinv.prog]) (by simp [hinv.pc]) rfl hinv.lpLen
    (fun r => hinv.regEq r) (fun r => hinv.regLt r) (fun r h0 h32 => hinv.regv r h0 h32) rfl rfl ?_ ?_ ?_
    (fun _ => rfl) rfl rfl rfl
  · intro j h1 h2
    simp only [hn'] at h2
    have : j = s.evs.length := by omega
    subst this
    rw [c.sk hm]; rfl
  · intro j h1 h2 h3
    have hjii : s.ii < sf.evs[j].sk.ii := by
      have := (hfut.later j _ h1 (List.getElem?_eq_getElem h2)).1; simp at this; omega
    show (if fs.sr then max ws.wVrNew _ else ws.wVrNew) ≤ _ ∧ (_ → (if fs.sr then max ws.wVrNew _ else ws.wVrNew) < _)
    have hold := hinv.vrNew j (by simp at h1; omega) h2 h3
    split
    · rename_i hsr
      have := fence_le c hinv.wf hinv.fut hm rfl rfl h2 hjii (Kind.isMem_of_isLoad _ h3)
        (inSucc_load c.io hsr h3) hv
      exact ⟨by omega, fun hs => by have := this.2 hs; have := hold.2 hs; omega⟩  -- S3b: strict for an AMO
    · exact hold
  · intro j h1 h2 h3
    have hjii : s.ii < sf.evs[j].sk.ii := by
      have := (hfut.later j _ h1 (List.getElem?_eq_getElem h2)).1; simp at this; omega
    show (if fs.sw then max ws.wVwNew _ else ws.wVwNew) < _
    have hold := hinv.vwNew j (by simp at h1; omega) h2 h3
    split
    · rename_i hsw
      have := (fence_le c hinv.wf hinv.fut hm rfl rfl h2 hjii (Kind.isMem_of_isStore _ h3)
        (inSucc_store c.io hsw h3) hv).2 h3
      omega
    · exact hold
  · intro j h1 h2 h3
    exact hinv.vcap j (by simp at h1; omega) h2 h3

/-- `FENCE.TSO` = `fence r,rw` then `fence w,w` (two fence events, one instruction). -/
theorem sim_fenceTso (c : HCtx T trs ν X h sf) (hinv : SimInv T X ν h sf s lp ws prom)
    (hi : (T.prog h)[s.pc]? = some .fenceTso) {s' : SSt}
    (hs : stepI h (T.prog h).length s .fenceTso = .next s') (hfut : Future s' sf) :
    StepOk T X ν h sf s lp ws prom s' := by
  have hwf' := (symWf_step h _ hinv.wf _).1 s' hs
  simp only [stepI, Ref.StepR.next.injEq] at hs
  subst hs
  have hm1 : sf.evs[s.evs.length]? = some ⟨{ kind := .fence fR, ii := s.ii, sz := 0 }, .c 0, .c 0⟩ :=
    prefix_get hfut.evs (by simp)
  have hm2 : sf.evs[s.evs.length + 1]? = some ⟨{ kind := .fence fW, ii := s.ii, sz := 0 }, .c 0, .c 0⟩ :=
    prefix_get hfut.evs (by simp)
  have hlabs : ∀ l, instrNext lp.prog.length lp .fenceTso l =
      go1 lp lp.regs (lp.pc + 1) [LFence true false true true, LFence false true false true, LInstr] l :=
    fun l => rfl
  have hsolo := solo_go1' (testImg T) (memOf X) h lp ws prom _ lp.regs (lp.pc + 1)
    [LFence true false true true, LFence false true false true, LInstr] (by simp) hinv.q (lpi_of hinv hi) hlabs
    (by simp [afOk])
  have hn' : ((s.emit ⟨{ kind := .fence fR, ii := s.ii, sz := 0 }, .c 0, .c 0⟩).emit
      ⟨{ kind := .fence fW, ii := s.ii, sz := 0 }, .c 0, .c 0⟩).adv.evs.length = s.evs.length + 2 := by simp
  refine ⟨_, _, _, _, hsolo, ?_, ?_, keepRR_fold _ _⟩  -- S3b: `keepRR`
  · rw [machRow_af _ (by simp [afOk]), hn', ← rowSeg_append X h _ (s.evs.length + 1) _ (by omega) (by omega),
      rowSeg_one, rowSeg_one, c.sk hm1, c.sk hm2]; rfl
  have hfold : [LFence true false true true, LFence false true false true, LInstr].foldl afEff ws =
      instrE (fencePost (fencePost ws true false true true) false true false true) := rfl
  rw [hfold]
  have hv1 := domF_fenceV c hinv fR
  have hv2 := domF_fenceV c hinv fW
  have hfut2 : ∀ j, s.evs.length + 2 ≤ j → (hj : j < sf.evs.length) → s.ii < sf.evs[j].sk.ii := by
    intro j h1 h2
    have := (hfut.later j _ (by simpa using h1) (List.getElem?_eq_getElem h2)).1; simp at this; omega
  refine inv_nomem hinv hwf' hfut (by simp) ?_ (by rw [lp_after, hinv.prog]) (by simp [hinv.pc]) rfl hinv.lpLen
    (fun r => hinv.regEq r) (fun r => hinv.regLt r) (fun r h0 h32 => hinv.regv r h0 h32) rfl rfl ?_ ?_ ?_
    (fun _ => rfl) rfl rfl rfl
  · intro j h1 h2
    simp only [hn'] at h2
    rcases (by omega : j = s.evs.length ∨ j = s.evs.length + 1) with rfl | rfl
    · rw [c.sk hm1]; rfl
    · rw [c.sk hm2]; rfl
  · intro j h1 h2 h3
    simp only [hn'] at h1
    have hjii := hfut2 j h1 h2
    show max ws.wVrNew (max ws.wVrOld 0) ≤ _ ∧ (_ → max ws.wVrNew (max ws.wVrOld 0) < _)
    have hold := hinv.vrNew j (by omega) h2 h3
    have := fence_le c hinv.wf hinv.fut hm1 rfl rfl h2 hjii (Kind.isMem_of_isLoad _ h3)
      (inSucc_load c.io rfl h3) hv1
    simp only [fR, if_true, Bool.false_eq_true, if_false] at this
    exact ⟨by omega, fun hs => by have := this.2 hs; have := hold.2 hs; omega⟩  -- S3b: strict for an AMO
  · intro j h1 h2 h3
    simp only [hn'] at h1
    have hjii := hfut2 j h1 h2
    show max (max ws.wVwNew (max ws.wVrOld 0)) (max 0 ws.wVwOld) < _
    have hold := hinv.vwNew j (by omega) h2 h3
    have e1 := (fence_le c hinv.wf hinv.fut hm1 rfl rfl h2 hjii (Kind.isMem_of_isStore _ h3)
      (inSucc_store c.io rfl h3) hv1).2 h3
    have e2 := (fence_le c hinv.wf hinv.fut hm2 rfl rfl h2 hjii (Kind.isMem_of_isStore _ h3)
      (inSucc_store c.io rfl h3) hv2).2 h3
    simp only [fR, fW, if_true, Bool.false_eq_true, if_false] at e1 e2
    omega
  · intro j h1 h2 h3
    exact hinv.vcap j (by simp at h1; omega) h2 h3

end instrs

end Weak.Prom.Cmp
