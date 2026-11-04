/-
Weak/Prom: **completeness S3a — simulating a plain store** (AtoP.v's fulfil case): the store fulfils its own
promise at its gmo timestamp `vo X w`; COH holds by `coh1` (rule 1), EXT (`stPre < ts`) by rules 9, 10 (address and
data taints), and the invariant's `vcap`/`vwNew` (rules 11, 13, 4).  The forward bank's new entry is bounded for
every later load reading the store by rule 12.
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.CmpSimLd

namespace Weak.Prom.Cmp

open MachCSL MachCSL.Stdpp Iris.Std
open Weak (Image Dsrc)
open Weak.Prom Weak.Prom.Mach Weak.Prom.Mach.Cert
open Weak.Prom.Ref
open PLabel

variable {T : Test} {trs : List SSt} {ν : Val} {X : Exec} {h : Nat} {sf : SSt}

theorem cohBelow_of (ws : PState) (ts : Nat) : ∀ (n : Nat) (a : Int), (∀ k, k < n → coh ws (a + k) < ts) →
    cohBelow ws a n ts
  | 0, _, _ => trivial
  | n + 1, a, hk => by
    refine ⟨by have := hk 0 (by omega); simpa using this, cohBelow_of ws ts n (a + 1) (fun k hkn => ?_)⟩
    have := hk (k + 1) (by omega)
    rwa [show a + ((k + 1 : Nat) : Int) = a + 1 + (k : Int) by push_cast; omega] at this

theorem acqPost_f (ws : PState) (ts : Nat) : acqPost ws false ts = ws := by cases ws; rfl

theorem machRow_store (aq rl : Bool) (b : Int) (d : List (BitVec 8)) (asrc vsrc : List Dsrc) (o : Option Nat)
    (tl : PF.Trace) : machRow ((LStore aq rl b d asrc vsrc, o) :: tl) = machRow tl := by
  simp [machRow, PF.loadsOf, PF.loadLikeTvs]

section store

variable {s : SSt} {lp : LP} {ws : PState} {prom : GSet Nat}

/-- **A PLAIN STORE** `s{b,h,w,d} rs2, off(rs1)`. -/
theorem sim_store (c : HCtx T trs ν X h sf) (hinv : SimInv T X ν h sf s lp ws prom) {sz rs2 rs1 off : Nat}
    (hi : (T.prog h)[s.pc]? = some (.store sz rs2 rs1 off)) (hok : instrS3a (.store sz rs2 rs1 off) = true)
    {s' : SSt} (hs : stepI h (T.prog h).length s (.store sz rs2 rs1 off) = .next s') (hfut : Future s' sf) :
    StepOk T X ν h sf s lp ws prom s' := by
  have hwf' := (symWf_step h _ hinv.wf _).1 s' hs
  simp only [instrS3a, rOk, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨hsz, hrs2⟩, hrs1⟩ := hok
  obtain ⟨hsz0, _⟩ := szOk_le hsz
  have hev1 := hinv.regEq rs1
  have hev2 := hinv.regEq rs2
  rcases hr1 : s.rd rs1 with ⟨e1, t1⟩
  rcases hr2 : s.rd rs2 with ⟨e2, t2⟩
  rw [hr1] at hev1
  rw [hr2] at hev2
  simp only [stepI, hr1, hr2, Ref.StepR.next.injEq] at hs
  subst hs
  have hm : sf.evs[s.evs.length]? = some ⟨{ kind := .st, ii := s.ii, sz := sz, adep := t1, ddep := t2, cdep := s.ctl }, .bin .add e1 (.c off), e2⟩ := prefix_get hfut.evs (by simp)
  have hml := (List.getElem?_eq_some_iff.1 hm).1
  have hid := c.id hm
  have hsk := c.sk hm
  have hev := c.ev hm
  have hsk' : (X.ev (h, s.evs.length)).sk = _ := hsk
  have hst : (X.sk (h, s.evs.length)).kind.isStore = true := by rw [hsk]; rfl
  have hwm := Kind.isMem_of_isStore _ hst
  have hwg : (h, s.evs.length) ∈ X.gmo := (mem_gmo c.ref _).2 ⟨hid, hwm⟩
  have hsz' : (X.ev (h, s.evs.length)).sk.sz = sz := congrArg Skel.sz hsk
  have hpa : (X.ev (h, s.evs.length)).pa = (Ex.bin .add e1 (.c off)).eval ν := by rw [hev]; rfl
  have hwdat : (X.ev (h, s.evs.length)).wdat = byteList (e2.eval ν) sz := by rw [hev]; rfl
  have haddr : (lp.rd rs1 + off) % two64 = (X.ev (h, s.evs.length)).pa := by
    rw [hpa, hev1]
    show _ = (e1.eval ν + off % two64) % two64
    rw [Nat.add_mod, Nat.add_mod (e1.eval ν) (off % two64), Nat.mod_mod]
  have halign : Mach.aligned ((lp.rd rs1 + off) % two64) sz = true := by
    have := List.all_eq_true.1 (c.condsSf).2 _ (List.mem_of_getElem? hm)
    simp only [Kind.isAcc, Kind.isMem, Bool.true_or, Bool.not_true, Bool.false_or, beq_iff_eq] at this
    rw [haddr, hpa]
    simp [Mach.aligned, this]
  have hdata : toBytes (lp.rd rs2) sz = (X.ev (h, s.evs.length)).wdat.map bv8 := by rw [hwdat, hev2]; rfl
  generalize hts : vo X (h, s.evs.length) = ts
  have hts1 : 1 ≤ ts := by rw [← hts]; exact voG_st_pos X X.gmo _ hwg hst
  -- the label and the program half
  have hlab : litNext lp (LStore false false ((X.ev (h, s.evs.length)).pa : Int)
      ((X.ev (h, s.evs.length)).wdat.map bv8) (srcR rs1) (srcR rs2)) = some { lp with pc := lp.pc + 1, q := [LInstr] } := by
    simp only [litNext, hinv.q, lpi_of hinv hi, instrNext]
    rw [halign]
    simp only [Bool.not_true, Bool.false_eq_true, if_false]
    rw [haddr, hdata]
    simp
  -- the memory half
  have hdl : ((X.ev (h, s.evs.length)).wdat.map bv8).length = sz := by
    rw [List.length_map, HCtx.wdat_len' c.ref hid hst, hsk]
  have hpr : ts ∈ prom := (hinv.prom ts).2 ⟨s.evs.length, Nat.le_refl _, hml, hst, hts⟩
  have hlog : (memOf X)[ts - 1]? = some ⟨((X.ev (h, s.evs.length)).pa : Int), (X.ev (h, s.evs.length)).wdat.map bv8,
      some h, stClass false⟩ := by
    rw [← hts]; refine (memG_voG X X.gmo _ hwg hst).trans ?_; unfold msgOf; rw [hsk]; rfl  -- S3b: `skCls`
  have hcohb : cohBelow ws ((X.ev (h, s.evs.length)).pa : Int) ((X.ev (h, s.evs.length)).wdat.map bv8).length ts := by
    rw [hdl]
    refine cohBelow_of ws ts sz _ (fun k hk => ?_)
    rw [show ((X.ev (h, s.evs.length)).pa : Int) + (k : Int) = (((X.ev (h, s.evs.length)).pa + k : Nat) : Int) by
      push_cast; rfl, ← hts]
    exact hinv.coh1 _ s.evs.length (Nat.le_refl _) hml hst (by rw [touches_iff, hsz']; omega)
  -- the pre-view
  have hdep : ∀ d, d ∈ t1 ∨ d ∈ t2 → vo X (h, d) < ts := by
    intro d hd
    have hok : okIdx s.evs d := by
      rcases hd with hd | hd
      · exact hinv.wf.taint rs1 d (by rw [hr1]; exact hd)
      · exact hinv.wf.taint rs2 d (by rw [hr2]; exact hd)
    obtain ⟨hdid, hdm, hpo⟩ := pf_po c hinv.wf hinv.fut hok (Nat.le_refl _) hml
    rw [← hts]
    rcases hd with hd | hd
    · exact vo_lt_of_gB (gB_of_ppo c.ref c.io hdid hid (ppo_r9 hdm hwm hpo (by rw [hsk]; exact hd))) hst
    · exact vo_lt_of_gB (gB_of_ppo c.ref c.io hdid hid (ppo_r10 hdm hst hpo (by rw [hsk]; exact hd))) hst
  have hva : srcsView ws (srcR rs1) < ts :=
    domF_lt (domF_srcR hinv.regv hrs1) (fun d hd => hdep d (.inl (by rw [hr1] at hd; exact hd))) (by omega)
  have hvd : srcsView ws (srcR rs2) < ts :=
    domF_lt (domF_srcR hinv.regv hrs2) (fun d hd => hdep d (.inr (by rw [hr2] at hd; exact hd))) (by omega)
  have hpre : stPreA ws false false (srcsView ws (srcR rs1)) (srcsView ws (srcR rs2)) < ts := by
    have h1 := hinv.vcap s.evs.length (Nat.le_refl _) hml hst
    have h2 := hinv.vwNew s.evs.length (Nat.le_refl _) hml hst
    have h3 := hinv.ifv
    rw [hts] at h1 h2
    simp only [stPreA, stPre, Bool.false_eq_true, if_false]
    omega
  have hmem := memStep.store (img := testImg T) (log := memOf X) (i := h) prom ws false false
    ((X.ev (h, s.evs.length)).pa : Int) ((X.ev (h, s.evs.length)).wdat.map bv8) (srcR rs1) (srcR rs2) ts hpr hlog
    hcohb hpre
  rw [acqPost_f, hdl] at hmem
  have htail := solo_af (testImg T) (memOf X) h [LInstr] { lp with pc := lp.pc + 1, q := [LInstr] }
    (storeRun ws false (srcsView ws (srcR rs1)) (max (srcsView ws (srcR rs1)) (srcsView ws (srcR rs2)))
      ((X.ev (h, s.evs.length)).pa : Int) sz ts) (prom \ {ts}) (by simp [afOk]) rfl
  refine ⟨_, _, _, _, .step _ _ (some ts) _ _ _ _ _ hlab hmem htail, ?_, ?_,
    keepRR_trans (keepRR_storeRun _ _ _ _ _ _) (keepRR_fold [LInstr] _)⟩  -- S3b: `keepRR`
  · rw [machRow_store, machRow_af _ (by simp [afOk])]
    have : (s.emit ⟨{ kind := .st, ii := s.ii, sz := sz, adep := t1, ddep := t2, cdep := s.ctl },
        .bin .add e1 (.c off), e2⟩).adv.evs.length = s.evs.length + 1 := by simp
    rw [this, rowSeg_one, hsk]; rfl
  -- the invariant
  obtain ⟨i1, i2, i3, i4, i5, i6, i7, i8, i9, i10, i11⟩ := storeBytes_spec sz ws ((X.ev (h, s.evs.length)).pa : Int) ts
    (max (srcsView ws (srcR rs1)) (srcsView ws (srcR rs2)))
  generalize hws1 : storeBytes ws ((X.ev (h, s.evs.length)).pa : Int) sz ts
    (max (srcsView ws (srcR rs1)) (srcsView ws (srcR rs2))) = ws1 at i1 i2 i3 i4 i5 i6 i7 i8 i9 i10 i11
  have hfin : [LInstr].foldl afEff (storeRun ws false (srcsView ws (srcR rs1))
      (max (srcsView ws (srcR rs1)) (srcsView ws (srcR rs2))) ((X.ev (h, s.evs.length)).pa : Int) sz ts) =
      instrE { ws1 with wVwOld := max ws1.wVwOld ts, wVcap := max (srcsView ws (srcR rs1)) ws1.wVcap } := by
    rw [← hws1]; rfl
  rw [hfin]
  have hn1 : (s.emit ⟨{ kind := .st, ii := s.ii, sz := sz, adep := t1, ddep := t2, cdep := s.ctl },
      .bin .add e1 (.c off), e2⟩).adv.evs.length = s.evs.length + 1 := by simp
  have hii1 : (s.emit ⟨{ kind := .st, ii := s.ii, sz := sz, adep := t1, ddep := t2, cdep := s.ctl },
      .bin .add e1 (.c off), e2⟩).adv.ii = s.ii + 1 := by simp
  have hrange : ∀ x : Nat, (((X.ev (h, s.evs.length)).pa : Int) ≤ (x : Int) ∧
      (x : Int) < ((X.ev (h, s.evs.length)).pa : Int) + (sz : Int)) ↔ touches (X.ev (h, s.evs.length)) x = true := by
    intro x; rw [touches_iff, hsz']; omega
  refine ⟨hwf', hfut, by simp [hinv.prog], by simp [hinv.pc], rfl, hinv.lpLen, fun r => hinv.regEq r,
    fun r => hinv.regLt r, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro r h0 h32
    have : regv (instrE { ws1 with wVwOld := max ws1.wVwOld ts, wVcap := max (srcsView ws (srcR rs1)) ws1.wVcap }) r =
        regv ws r := by unfold regv; simp only [instrE]; rw [i3]
    rw [this]; exact hinv.regv r h0 h32
  · show domF _ _ ws1.wVrOld
    rw [i5, hn1]; exact domF_mono hinv.vrOld (fun j hj => ⟨by omega, hj.2⟩)
  · show domF _ _ (max ws1.wVwOld ts)
    rw [i6, hn1]
    exact domF_max (domF_mono hinv.vwOld (fun j hj => ⟨by omega, hj.2⟩))
      (domF_of _ s.evs.length ⟨by omega, hst⟩ (Nat.le_of_eq hts.symm))
  · intro j h1 h2 h3; show ws1.wVrNew ≤ _ ∧ (_ → ws1.wVrNew < _); rw [i7]  -- S3b: strict part
    exact hinv.vrNew j (by rw [hn1] at h1; omega) h2 h3
  · intro j h1 h2 h3; show ws1.wVwNew < _; rw [i8]; exact hinv.vwNew j (by rw [hn1] at h1; omega) h2 h3
  · -- vcap: rule 13 through the store's address
    intro j h1 h2 h3
    show max (srcsView ws (srcR rs1)) ws1.wVcap < _
    rw [i4]
    rw [hn1] at h1
    have hjii := fut_ii hfut hii1 (by rw [hn1]; exact h1) h2
    obtain ⟨hjid, _, _⟩ := fut_ev c h2
    have hpo2 : poX X (h, s.evs.length) (h, j) = true := c.po_of hm (List.getElem?_eq_getElem h2) hjii
    have hold := hinv.vcap j (by omega) h2 h3
    have hva' : srcsView ws (srcR rs1) < vo X (h, j) := by
      refine domF_lt (domF_srcR hinv.regv hrs1) (fun d hd => ?_) (by omega)
      rw [hr1] at hd
      obtain ⟨hdid, hdm, hpo1⟩ := pf_po c hinv.wf hinv.fut (hinv.wf.taint rs1 d (by rw [hr1]; exact hd))
        (Nat.le_refl _) hml
      exact vo_lt_of_gB (gB_of_ppo c.ref c.io hdid hjid
        (ppo_r13 hdm h3 hid hwm hpo1 hpo2 (by rw [hsk]; exact hd))) h3
    omega
  · -- coh1: rule 1
    intro x j h1 h2 h3 h4
    show coh ws1 x < _
    rw [i1]
    rw [hn1] at h1
    have hold := hinv.coh1 x j (by omega) h2 h3 h4
    split
    · rename_i hin
      have htx := (hrange x).1 hin
      have hjii := fut_ii hfut hii1 (by rw [hn1]; exact h1) h2
      obtain ⟨hjid, _, _⟩ := fut_ev c h2
      have hpo2 : poX X (h, s.evs.length) (h, j) = true := c.po_of hm (List.getElem?_eq_getElem h2) hjii
      have := vo_lt_of_gB (gB_of_ppo c.ref c.io hid hjid (ppo_r1 hwm h3 hpo2 (overlap_of_touch htx h4))) h3
      rw [hts] at this
      omega
    · exact hold
  · -- coh2: the store is a candidate of every later load of its bytes
    intro x j h1 h2 h3 h4 w hw hww hle
    change vo X w ≤ coh ws1 x at hle
    rw [i1] at hle
    rw [hn1] at h1
    split at hle
    · rename_i hin
      have htx := (hrange x).1 hin
      by_cases hc : vo X w ≤ coh ws x
      · exact hinv.coh2 x j (by omega) h2 h3 h4 w hw hww hc
      · have hjii := fut_ii hfut hii1 (by rw [hn1]; exact h1) h2
        have hpo2 : poX X (h, s.evs.length) (h, j) = true := c.po_of hm (List.getElem?_eq_getElem h2) hjii
        have hwr : writesB (X.ev (h, s.evs.length)) x = true := by
          simp only [writesB, Bool.and_eq_true]; exact ⟨hst, htx⟩
        have := kts_ge c.ref hwg hwr (.inr hpo2)
        rw [hts] at this
        omega
    · exact hinv.coh2 x j (by omega) h2 h3 h4 w hw hww hle
  · -- fwd
    intro x
    show fwdOk X h _ _ x (get? ws1.wFwd (x : Int))
    rw [i2, hn1]
    split
    · rename_i hin
      have htx := (hrange x).1 hin
      refine ⟨s.evs.length, by omega, hst, htx, fun j2 h1 h2 _ => by omega, hts.symm, ?_⟩
      intro j' h1 h2 h3 h4 hsrc
      have hjii := fut_ii hfut hii1 (by rw [hn1]; exact h1) h2
      obtain ⟨hjid, _, _⟩ := fut_ev c h2
      have hpo2 : poX X (h, s.evs.length) (h, j') = true := c.po_of hm (List.getElem?_eq_getElem h2) hjii
      have hk : x - (X.ev (h, j')).pa < (X.sk (h, j')).sz := by
        rw [touches_iff] at h4; unfold Exec.sk; omega
      have hxk : (X.ev (h, j')).pa + (x - (X.ev (h, j')).pa) = x := by rw [touches_iff] at h4; omega
      have hbg : ∀ d, d ∈ t1 ++ t2 → gB X.gmo (h, d) (h, j') = true := by
        intro d hd
        have hok : okIdx s.evs d := by
          rcases List.mem_append.1 hd with hd | hd
          · exact hinv.wf.taint rs1 d (by rw [hr1]; exact hd)
          · exact hinv.wf.taint rs2 d (by rw [hr2]; exact hd)
        obtain ⟨hdid, hdm, hpo1⟩ := pf_po c hinv.wf hinv.fut hok (Nat.le_refl _) hml
        have hdd : d ∈ (X.sk (h, s.evs.length)).adep ∨ d ∈ (X.sk (h, s.evs.length)).ddep := by
          rw [hsk]; simpa using List.mem_append.1 hd
        exact gB_of_ppo c.ref c.io hdid hjid
          (ppo_r12 c.io hdm h3 hid hst hpo1 hpo2 hdd hk (by rw [hxk]; exact hsrc))
      have hb : ∀ d, d ∈ t1 ++ t2 → vo X (h, d) ≤ vo X (h, j') := fun d hd => vo_le_of_gB (hbg d hd)
      have e1 := domF_bound (domF_srcR hinv.regv hrs1) (fun d hd => hb d (List.mem_append_left _
        (by rw [hr1] at hd; exact hd)))
      have e2 := domF_bound (domF_srcR hinv.regv hrs2) (fun d hd => hb d (List.mem_append_right _
        (by rw [hr2] at hd; exact hd)))
      refine ⟨by omega, fun hjs => ?_⟩  -- S3b: strict into an AMO (rule 12 into a store)
      have hj0 : 0 < vo X (h, j') := Nat.lt_of_lt_of_le (Nat.zero_lt_one)
        (voG_st_pos X X.gmo _ ((mem_gmo c.ref _).2 ⟨hjid, Kind.isMem_of_isStore _ hjs⟩) hjs)
      have f1 := domF_lt (domF_srcR hinv.regv hrs1) (fun d hd => vo_lt_of_gB (hbg d (List.mem_append_left _
        (by rw [hr1] at hd; exact hd))) hjs) hj0
      have f2 := domF_lt (domF_srcR hinv.regv hrs2) (fun d hd => vo_lt_of_gB (hbg d (List.mem_append_right _
        (by rw [hr2] at hd; exact hd))) hjs) hj0
      omega
    · rename_i hout
      refine fwdOk_mono (hinv.fwd x) (by omega) (fun j hj1 hj2 hjs => ?_)
      have : j = s.evs.length := by omega
      subst this
      cases ht : touches (X.ev (h, s.evs.length)) x
      · rfl
      · exact absurd ((hrange x).2 ht) hout
  · rfl
  · rfl
  · -- prom
    intro tt
    rw [elemOfDifference, elemOfSingleton, hinv.prom tt, hn1]
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
      have := voG_inj X X.gmo (h, j) (h, s.evs.length) hjg hwg h3 hst (by unfold vo at h4 hts; omega)
      simp at this; omega

end store

end Weak.Prom.Cmp
