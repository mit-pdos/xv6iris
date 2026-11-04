/-
Weak/Prom: **completeness S3b — the write of a release store, an SC or an AMO** (AtoP.v's fulfil case, with
rules 3, 5–8).

* `MemOk` — the memory fields of S3a's `SimInv` (everything but the program side, `regv`, `ldv`, `ifv`), with
  `simInv_mk` / `memOk_of` / `memOk_congr`, so a write's post-state is checked once (`mem_storeG`) and each instruction
  only adds its register side.
* `stPreA_lt` — the write's pre-view `stPreA ws aq rl va vd` is strictly below its timestamp: rules 9, 10 (address,
  data), the invariant's `vcap` (rules 11, 13) and `vwNew` (rules 4, 5), rule 6 for a release (`vrOld ⊔ vwOld`),
  rule 7 for an acquire (`wVRel`, `ExtraInv.vrel`).
* `mem_storeG` — COH (`cohBelow`, rule 1), EXT (`stPreA_lt`) and the post-state `acqPost (storeRun …) aq ts` at the
  new length, for any forward view `fv` that is below every later load reading the store (`fvOk`: rule 12 for a plain
  or release store, `fvOk_deps`; rule 3 for an AMO or SC, whose forward view is its own timestamp, M1, `fvOk_rmw`).
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.CmpSimLB

namespace Weak.Prom.Cmp

open MachCSL MachCSL.Stdpp Iris.Std
open Weak (Image Dsrc)
open Weak.Prom Weak.Prom.Mach Weak.Prom.Mach.Cert
open Weak.Prom.Ref
open PLabel

/-! ## 1. The memory fields of `SimInv` -/

/-- The memory fields of `SimInv` after `n` events, with `nF` the final number. -/
structure MemOk (X : Exec) (h nF n : Nat) (ws : PState) (prom : GSet Nat) : Prop where
  vrOld : domF (fun j => vo X (h, j)) (fun j => j < n ∧ (X.sk (h, j)).kind.isLoad = true) ws.wVrOld
  vwOld : domF (fun j => vo X (h, j)) (fun j => j < n ∧ (X.sk (h, j)).kind.isStore = true) ws.wVwOld
  vrNew : ∀ j, n ≤ j → j < nF → (X.sk (h, j)).kind.isLoad = true →
    ws.wVrNew ≤ vo X (h, j) ∧ ((X.sk (h, j)).kind.isStore = true → ws.wVrNew < vo X (h, j))
  vwNew : ∀ j, n ≤ j → j < nF → (X.sk (h, j)).kind.isStore = true → ws.wVwNew < vo X (h, j)
  vcap : ∀ j, n ≤ j → j < nF → (X.sk (h, j)).kind.isStore = true → ws.wVcap < vo X (h, j)
  coh1 : ∀ (x : Nat) j, n ≤ j → j < nF → (X.sk (h, j)).kind.isStore = true →
    touches (X.ev (h, j)) x = true → coh ws x < vo X (h, j)
  coh2 : ∀ (x : Nat) j, n ≤ j → j < nF → (X.sk (h, j)).kind.isLoad = true →
    touches (X.ev (h, j)) x = true → ∀ w ∈ X.gmo, writesB (X.ev w) x = true → vo X w ≤ coh ws x →
      vo X w ≤ kts X (rfSrc X (h, j) x)
  fwd : ∀ x : Nat, fwdOk X h nF n x (get? ws.wFwd (x : Int))
  prom : ∀ t, t ∈ prom ↔ ∃ j, n ≤ j ∧ j < nF ∧ (X.sk (h, j)).kind.isStore = true ∧ vo X (h, j) = t

variable {T : Test} {trs : List SSt} {ν : Val} {X : Exec} {h : Nat} {sf : SSt}

theorem memOk_of {s : SSt} {lp : LP} {ws : PState} {prom : GSet Nat} (hinv : SimInv T X ν h sf s lp ws prom) :
    MemOk X h sf.evs.length s.evs.length ws prom :=
  ⟨hinv.vrOld, hinv.vwOld, hinv.vrNew, hinv.vwNew, hinv.vcap, hinv.coh1, hinv.coh2, hinv.fwd, hinv.prom⟩

theorem simInv_mk {s : SSt} {lp : LP} {ws : PState} {prom : GSet Nat} (hwf : SymWf s) (hfut : Future s sf)
    (hprog : lp.prog = T.prog h) (hpc : lp.pc = s.pc) (hq : lp.q = []) (hlen : lp.regs.length = 32)
    (hregEq : ∀ r, lp.rd r = (s.rd r).1.eval ν) (hregLt : ∀ r, (s.rd r).1.eval ν < two64)
    (hregv : ∀ r, 0 < r → r < 32 → domF (fun j => vo X (h, j)) (· ∈ (s.rd r).2) (regv ws r))
    (hm : MemOk X h sf.evs.length s.evs.length ws prom) (hldv : ws.wLdv = 0) (hifv : ws.wIfv = 0) :
    SimInv T X ν h sf s lp ws prom :=
  ⟨hwf, hfut, hprog, hpc, hq, hlen, hregEq, hregLt, hregv, hm.vrOld, hm.vwOld, hm.vrNew, hm.vwNew, hm.vcap, hm.coh1,
    hm.coh2, hm.fwd, hldv, hifv, hm.prom⟩

/-- `MemOk` depends only on the fields it names. -/
theorem memOk_congr {nF n : Nat} {ws ws' : PState} {prom : GSet Nat} (hm : MemOk X h nF n ws prom)
    (h1 : ws'.wVrOld = ws.wVrOld) (h2 : ws'.wVwOld = ws.wVwOld) (h3 : ws'.wVrNew = ws.wVrNew)
    (h4 : ws'.wVwNew = ws.wVwNew) (h5 : ws'.wVcap = ws.wVcap) (h6 : ∀ x : Int, coh ws' x = coh ws x)
    (h7 : ws'.wFwd = ws.wFwd) : MemOk X h nF n ws' prom := by
  refine ⟨by rw [h1]; exact hm.vrOld, by rw [h2]; exact hm.vwOld, by rw [h3]; exact hm.vrNew,
    by rw [h4]; exact hm.vwNew, by rw [h5]; exact hm.vcap, fun x => by rw [h6]; exact hm.coh1 x,
    fun x => by rw [h6]; exact hm.coh2 x, fun x => by rw [h7]; exact hm.fwd x, hm.prom⟩

/-! ## 2. The write's pre-view -/

section write

variable {s : SSt} {lp : LP} {ws : PState} {prom : GSet Nat}

/-- THE PRE-VIEW OF A WRITE IS STRICTLY BELOW ITS TIMESTAMP. -/
theorem stPreA_lt (c : HCtx T trs ν X h sf) (hinv : SimInv T X ν h sf s lp ws prom)
    (hx : ExtraInv X h s.evs.length ws.wVRel ws.wRes) {rs1 rs2 : Nat} (hrs1 : rs1 < 32) (hrs2 : rs2 < 32)
    {se : SEv} (hm : sf.evs[s.evs.length]? = some se) (hst : se.sk.kind.isStore = true) (hii : se.sk.ii = s.ii)
    (hadep : se.sk.adep = (s.rd rs1).2) (hddep : se.sk.ddep = (s.rd rs2).2) (aq rl : Bool)
    (haq : aq = true → se.sk.aqSc = true) (hrl : rl = true → se.sk.rlSc = true) (vd : Nat)
    (hvd : vd = srcsView ws (srcR rs2)) :
    stPreA ws aq rl (srcsView ws (srcR rs1)) vd < vo X (h, s.evs.length) := by
  subst hvd
  have hl := List.getElem?_eq_some_iff.1 hm
  have hsk := c.sk hm
  have hid := c.id hm
  have hst' : (X.sk (h, s.evs.length)).kind.isStore = true := by rw [hsk]; exact hst
  have hem := Kind.isMem_of_isStore _ hst'
  have heg := c.gmo_of hm (by rw [← hsk]; exact hem)
  have hpos := voG_st_pos X X.gmo _ heg hst'
  have hdep : ∀ r, r < 32 → (∀ d ∈ (s.rd r).2, d ∈ (X.sk (h, s.evs.length)).adep ∨
      d ∈ (X.sk (h, s.evs.length)).ddep) → srcsView ws (srcR r) < vo X (h, s.evs.length) := by
    intro r hr hsub
    refine domF_lt (domF_srcR hinv.regv hr) (fun d hd => ?_) (by unfold vo; omega)
    obtain ⟨hdid, hdm, hpo⟩ := pf_po c hinv.wf hinv.fut (hinv.wf.taint r d hd) (Nat.le_refl _) hl.1
    rcases hsub d hd with h1 | h1
    · exact vo_lt_of_gB (gB_of_ppo c.ref c.io hdid hid (ppo_r9 hdm hem hpo h1)) hst'
    · exact vo_lt_of_gB (gB_of_ppo c.ref c.io hdid hid (ppo_r10 hdm hst' hpo h1)) hst'
  have hva := hdep rs1 hrs1 (fun d hd => .inl (by rw [hsk, hadep]; exact hd))
  have hvd := hdep rs2 hrs2 (fun d hd => .inr (by rw [hsk, hddep]; exact hd))
  have h1 := hinv.vcap s.evs.length (Nat.le_refl _) hl.1 hst'
  have h2 := hinv.vwNew s.evs.length (Nat.le_refl _) hl.1 hst'
  have h3 := hinv.ifv
  have hvrel : (if aq then ws.wVRel else 0) < vo X (h, s.evs.length) := by
    cases haq' : aq
    · simp only [Bool.false_eq_true, if_false]; unfold vo; omega
    · simp only [if_true]
      exact (domF_gB hx.vrel (fun j ⟨hj, hjm, hjr⟩ => by
        obtain ⟨hid', hpo⟩ := past_po c hinv hm hii hj
        exact gB_of_ppo c.ref c.io hid' hid (ppo_r7 c.io hjm hem hpo hjr (by rw [hsk]; exact haq haq'))) heg).2 hst'
  have hold : (if rl then max ws.wVrOld ws.wVwOld else 0) < vo X (h, s.evs.length) := by
    cases hrl' : rl
    · simp only [Bool.false_eq_true, if_false]; unfold vo; omega
    · simp only [if_true]
      have hr6 : ∀ j, j < s.evs.length → (X.sk (h, j)).kind.isMem = true →
          gB X.gmo (h, j) (h, s.evs.length) = true := fun j hj hjm => by
        obtain ⟨hid', hpo⟩ := past_po c hinv hm hii hj
        exact gB_of_ppo c.ref c.io hid' hid (ppo_r6 c.io hjm hem hpo (by rw [hsk]; exact hrl hrl'))
      have e1 := (domF_gB hinv.vrOld (fun j ⟨hj, hjl⟩ => hr6 j hj (Kind.isMem_of_isLoad _ hjl)) heg).2 hst'
      have e2 := (domF_gB hinv.vwOld (fun j ⟨hj, hjl⟩ => hr6 j hj (Kind.isMem_of_isStore _ hjl)) heg).2 hst'
      omega
  simp only [stPreA, stPre]
  omega

/-! ## 3. The write's post-state -/

/-- A forward view below every later load that reads the store (strictly below a later AMO). -/
def fvOk (X : Exec) (h n nF fv : Nat) : Prop :=
  ∀ j', n < j' → j' < nF → (X.sk (h, j')).kind.isLoad = true → ∀ x, touches (X.ev (h, j')) x = true →
    rfSrc X (h, j') x = some (h, n) → fv ≤ vo X (h, j') ∧ ((X.sk (h, j')).kind.isStore = true → fv < vo X (h, j'))

theorem storeRun_fields (ws : PState) (rl : Bool) (va fv : Nat) (base : Int) (n ts : Nat) (aq : Bool) :
    (acqPost (storeRun ws rl va fv base n ts) aq ts).wVrOld = ws.wVrOld ∧
    (acqPost (storeRun ws rl va fv base n ts) aq ts).wVwOld = max ws.wVwOld ts ∧
    (acqPost (storeRun ws rl va fv base n ts) aq ts).wVrNew = (if aq then max ws.wVrNew ts else ws.wVrNew) ∧
    (acqPost (storeRun ws rl va fv base n ts) aq ts).wVwNew = (if aq then max ws.wVwNew ts else ws.wVwNew) ∧
    (acqPost (storeRun ws rl va fv base n ts) aq ts).wVcap = max va ws.wVcap ∧
    (acqPost (storeRun ws rl va fv base n ts) aq ts).wVRel = (if rl then max ws.wVRel ts else ws.wVRel) ∧
    (acqPost (storeRun ws rl va fv base n ts) aq ts).wRegv = ws.wRegv ∧
    (acqPost (storeRun ws rl va fv base n ts) aq ts).wLdv = ws.wLdv ∧
    (acqPost (storeRun ws rl va fv base n ts) aq ts).wIfv = ws.wIfv ∧
    (acqPost (storeRun ws rl va fv base n ts) aq ts).wRes = ws.wRes ∧
    (∀ b : Int, coh (acqPost (storeRun ws rl va fv base n ts) aq ts) b =
      if base ≤ b ∧ b < base + n then max (coh ws b) ts else coh ws b) ∧
    (∀ b : Int, get? (acqPost (storeRun ws rl va fv base n ts) aq ts).wFwd b =
      if base ≤ b ∧ b < base + n then some (ts, fv) else get? ws.wFwd b) := by
  obtain ⟨i1, i2, i3, i4, i5, i6, i7, i8, i9, i10, i11⟩ := storeBytes_spec n ws base ts fv
  have iR := (keepRR_storeBytes ws base n ts fv).2
  refine ⟨i5, by simp only [acqPost, storeRun]; rw [i6], ?_, ?_, by simp only [acqPost, storeRun]; rw [i4],
    by simp only [acqPost, storeRun]; rw [i11], by simp only [acqPost, storeRun]; rw [i3], i9, i10, iR, ?_, ?_⟩
  · simp only [acqPost, storeRun]; rw [i7]
  · simp only [acqPost, storeRun]; rw [i8]
  · intro b; exact i1 b
  · intro b; exact i2 b

/-- **THE WRITE: COH, EXT and the post-state** (for a store or SC event). -/
theorem mem_storeG (c : HCtx T trs ν X h sf) (hinv : SimInv T X ν h sf s lp ws prom)
    (hx : ExtraInv X h s.evs.length ws.wVRel ws.wRes) {rs1 rs2 : Nat} (hrs1 : rs1 < 32) (hrs2 : rs2 < 32)
    {se : SEv} (hm : sf.evs[s.evs.length]? = some se) (hst : se.sk.kind.isStore = true) (hii : se.sk.ii = s.ii)
    (hadep : se.sk.adep = (s.rd rs1).2) (hddep : se.sk.ddep = (s.rd rs2).2) (aq rl : Bool)
    (haq : aq = true → se.sk.aqSc = true) (hrl : rl = true → se.sk.rlSc = true) (fv : Nat)
    (hfv : fvOk X h s.evs.length sf.evs.length fv) {s' : SSt} (hfut' : Future s' sf)
    (hn1 : s'.evs.length = s.evs.length + 1) (hii1 : s'.ii = s.ii + 1) :
    cohBelow ws ((X.ev (h, s.evs.length)).pa : Int) se.sk.sz (vo X (h, s.evs.length)) ∧
    stPreA ws aq rl (srcsView ws (srcR rs1)) (srcsView ws (srcR rs2)) < vo X (h, s.evs.length) ∧
    MemOk X h sf.evs.length (s.evs.length + 1)
      (acqPost (storeRun ws rl (srcsView ws (srcR rs1)) fv ((X.ev (h, s.evs.length)).pa : Int) se.sk.sz
        (vo X (h, s.evs.length))) aq (vo X (h, s.evs.length))) (prom \ {vo X (h, s.evs.length)}) ∧
    domF (fun j => vo X (h, j)) (fun j => j < s.evs.length + 1 ∧ (X.sk (h, j)).kind.isMem = true ∧
      (X.sk (h, j)).rlSc = true)
      (acqPost (storeRun ws rl (srcsView ws (srcR rs1)) fv ((X.ev (h, s.evs.length)).pa : Int) se.sk.sz
        (vo X (h, s.evs.length))) aq (vo X (h, s.evs.length))).wVRel := by
  have hl := List.getElem?_eq_some_iff.1 hm
  have hml := hl.1
  have hid := c.id hm
  have hsk := c.sk hm
  have hst' : (X.sk (h, s.evs.length)).kind.isStore = true := by rw [hsk]; exact hst
  have hwm := Kind.isMem_of_isStore _ hst'
  have hwg : (h, s.evs.length) ∈ X.gmo := (mem_gmo c.ref _).2 ⟨hid, hwm⟩
  have hsz' : (X.ev (h, s.evs.length)).sk.sz = se.sk.sz := congrArg Skel.sz hsk
  generalize hts : vo X (h, s.evs.length) = ts
  have hts1 : 1 ≤ ts := by rw [← hts]; exact voG_st_pos X X.gmo _ hwg hst'
  have hrange : ∀ x : Nat, (((X.ev (h, s.evs.length)).pa : Int) ≤ (x : Int) ∧
      (x : Int) < ((X.ev (h, s.evs.length)).pa : Int) + (se.sk.sz : Int)) ↔
        touches (X.ev (h, s.evs.length)) x = true := by
    intro x; rw [touches_iff, hsz']; omega
  -- order facts for a future event
  have hfutpo : ∀ j, s.evs.length + 1 ≤ j → j < sf.evs.length → poX X (h, s.evs.length) (h, j) = true := by
    intro j h1 h2
    have hjii := fut_ii hfut' hii1 (by rw [hn1]; exact h1) h2
    exact c.po_of hm (List.getElem?_eq_getElem h2) (by omega)
  have hacq : aq = true → ∀ j, s.evs.length + 1 ≤ j → j < sf.evs.length →
      (X.sk (h, j)).kind.isMem = true → gB X.gmo (h, s.evs.length) (h, j) = true := by
    intro haq' j h1 h2 hjm
    exact gB_of_ppo c.ref c.io hid (fut_ev c h2).1 (ppo_r5 c.io hwm hjm (hfutpo j h1 h2) (by rw [hsk]; exact haq haq'))
  obtain ⟨f1, f2, f3, f4, f5, f6, _, _, _, _, f11, f12⟩ := storeRun_fields ws rl (srcsView ws (srcR rs1)) fv
    ((X.ev (h, s.evs.length)).pa : Int) se.sk.sz ts aq
  refine ⟨cohBelow_of ws ts _ _ (fun k hk => ?_), ?_, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [show ((X.ev (h, s.evs.length)).pa : Int) + (k : Int) = (((X.ev (h, s.evs.length)).pa + k : Nat) : Int) by
      push_cast; rfl, ← hts]
    exact hinv.coh1 _ s.evs.length (Nat.le_refl _) hml hst' (by rw [touches_iff, hsz']; omega)
  · rw [← hts]
    exact stPreA_lt c hinv hx hrs1 hrs2 hm hst hii hadep hddep aq rl haq hrl _ rfl
  · -- vrOld
    rw [f1]; exact domF_mono hinv.vrOld (fun j hj => ⟨by omega, hj.2⟩)
  · -- vwOld
    rw [f2]
    exact domF_max (domF_mono hinv.vwOld (fun j hj => ⟨by omega, hj.2⟩))
      (domF_of _ s.evs.length ⟨by omega, hst'⟩ (Nat.le_of_eq hts.symm))
  · -- vrNew: rule 5
    intro j h1 h2 h3
    rw [f3]
    have hold := hinv.vrNew j (by omega) h2 h3
    cases haq' : aq
    · simp only [Bool.false_eq_true, if_false]; exact hold
    · simp only [if_true]
      have hg := vo_of_gB (hacq haq' j h1 h2 (Kind.isMem_of_isLoad _ h3))
      rw [hts] at hg
      exact ⟨by omega, fun hs => by have := hold.2 hs; have := hg.2 hs; omega⟩
  · -- vwNew: rule 5
    intro j h1 h2 h3
    rw [f4]
    have hold := hinv.vwNew j (by omega) h2 h3
    cases haq' : aq
    · simp only [Bool.false_eq_true, if_false]; exact hold
    · simp only [if_true]
      have := (vo_of_gB (hacq haq' j h1 h2 (Kind.isMem_of_isStore _ h3))).2 h3
      rw [hts] at this
      omega
  · -- vcap: rule 13 through the address
    intro j h1 h2 h3
    rw [f5]
    obtain ⟨hjid, _, _⟩ := fut_ev c h2
    have hpo2 := hfutpo j h1 h2
    have hold := hinv.vcap j (by omega) h2 h3
    have hva' : srcsView ws (srcR rs1) < vo X (h, j) := by
      refine domF_lt (domF_srcR hinv.regv hrs1) (fun d hd => ?_) (by omega)
      obtain ⟨hdid, hdm, hpo1⟩ := pf_po c hinv.wf hinv.fut (hinv.wf.taint rs1 d hd) (Nat.le_refl _) hml
      exact vo_lt_of_gB (gB_of_ppo c.ref c.io hdid hjid
        (ppo_r13 hdm h3 hid hwm hpo1 hpo2 (by rw [hsk, hadep]; exact hd))) h3
    omega
  · -- coh1: rule 1
    intro x j h1 h2 h3 h4
    rw [f11]
    have hold := hinv.coh1 x j (by omega) h2 h3 h4
    split
    · rename_i hin
      have htx := (hrange x).1 hin
      obtain ⟨hjid, _, _⟩ := fut_ev c h2
      have := vo_lt_of_gB (gB_of_ppo c.ref c.io hid hjid (ppo_r1 hwm h3 (hfutpo j h1 h2)
        (overlap_of_touch htx h4))) h3
      rw [hts] at this
      omega
    · exact hold
  · -- coh2: the store is a candidate of every later load of its bytes
    intro x j h1 h2 h3 h4 w hw hww hle
    rw [f11] at hle
    split at hle
    · rename_i hin
      have htx := (hrange x).1 hin
      by_cases hc : vo X w ≤ coh ws x
      · exact hinv.coh2 x j (by omega) h2 h3 h4 w hw hww hc
      · have hwr : writesB (X.ev (h, s.evs.length)) x = true := by
          simp only [writesB, Bool.and_eq_true]; exact ⟨hst', htx⟩
        have := kts_ge c.ref hwg hwr (.inr (hfutpo j h1 h2))
        rw [hts] at this
        omega
    · exact hinv.coh2 x j (by omega) h2 h3 h4 w hw hww hle
  · -- fwd
    intro x
    rw [f12]
    split
    · rename_i hin
      have htx := (hrange x).1 hin
      refine ⟨s.evs.length, by omega, hst', htx, fun j2 h1 h2 _ => by omega, hts.symm, ?_⟩
      intro j' h1 h2 h3 h4 hsrc
      exact hfv j' (by omega) h2 h3 x h4 hsrc
    · rename_i hout
      refine fwdOk_mono (hinv.fwd x) (by omega) (fun j hj1 hj2 hjs => ?_)
      have : j = s.evs.length := by omega
      subst this
      cases ht : touches (X.ev (h, s.evs.length)) x
      · rfl
      · exact absurd ((hrange x).2 ht) hout
  · -- prom
    intro tt
    rw [elemOfDifference, elemOfSingleton, hinv.prom tt]
    constructor
    · rintro ⟨⟨j, h1, h2, h3, h4⟩, hne⟩
      refine ⟨j, ?_, h2, h3, h4⟩
      rcases Nat.lt_or_ge j (s.evs.length + 1) with h5 | h5
      · have : j = s.evs.length := by omega
        subst this; exact absurd (h4.symm.trans hts) hne
      · exact h5
    · rintro ⟨j, h1, h2, h3, h4⟩
      refine ⟨⟨j, by omega, h2, h3, h4⟩, fun he => ?_⟩
      have hjg : (h, j) ∈ X.gmo := (mem_gmo c.ref _).2 ⟨(fut_ev c h2).1, Kind.isMem_of_isStore _ h3⟩
      have := voG_inj X X.gmo (h, j) (h, s.evs.length) hjg hwg h3 hst' (by unfold vo at h4 hts; omega)
      simp at this; omega
  · -- the release view (ExtraInv.vrel)
    rw [f6]
    have hv0 : domF (fun j => vo X (h, j)) (fun j => j < s.evs.length + 1 ∧ (X.sk (h, j)).kind.isMem = true ∧
        (X.sk (h, j)).rlSc = true) ws.wVRel := domF_mono hx.vrel (fun j hj => ⟨by omega, hj.2⟩)
    cases hrl' : rl
    · exact hv0
    · simp only [if_true]
      exact domF_max hv0 (domF_of _ s.evs.length ⟨by omega, hwm, by rw [hsk]; exact hrl hrl'⟩
        (Nat.le_of_eq hts.symm))

end write

end Weak.Prom.Cmp
