/-
Weak/Prom: **completeness S3b — the Zalasr load-acquire and the LR** (one generic step, `sim_loadG`).

A load operation that is not a store (`ld` with an acquire-RCsc and maybe a release-RCsc annotation, Zalasr
`l{b,h,w,d}.aq[rl]`; or `lr` with its `aq`/`rl` bits) answers every byte with the load value axiom's store
(`loadOk_refG` at `ldPre_le`'s pre-view).  On top of S3a's plain load (Weak/Prom/CmpSimLd.lean):
* an ACQUIRE raises `vrNew`, `vwNew` to its post-view, which is below every later load's (store's) view by rule 5
  (rvwmo.adoc:287 "a has an acquire annotation");
* a RELEASE raises `wVRel` to its read view (`readView_le`), so `ExtraInv.vrel` holds with the operation itself;
* the LR's reservation (`res'`) is the caller's (`resOk` at the new length).
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.CmpSimR

namespace Weak.Prom.Cmp

open MachCSL MachCSL.Stdpp Iris.Std
open Weak (Image Dsrc)
open Weak.Prom Weak.Prom.Mach Weak.Prom.Mach.Cert
open Weak.Prom.Ref
open PLabel

variable {T : Test} {trs : List SSt} {ν : Val} {X : Exec} {h : Nat} {sf : SSt}

section loadG

variable {s : SSt} {lp : LP} {ws : PState} {prom : GSet Nat}

/-- THE READ VIEW (an LR's rule-8 view, a release load's `wVRel` raise) is below the operation's view. -/
theorem readView_le (c : HCtx T trs ν X h sf) (hinv : SimInv T X ν h sf s lp ws prom)
    (hx : ExtraInv X h s.evs.length ws.wVRel ws.wRes) {rs1 : Nat} (hrs : rs1 < 32) {se : SEv}
    (hm : sf.evs[s.evs.length]? = some se) (hld : se.sk.kind.isLoad = true) (hii : se.sk.ii = s.ii)
    (hadep : se.sk.adep = (s.rd rs1).2) (aq rl : Bool) (haq : aq = true → se.sk.aqSc = true)
    (hrl : rl = true → se.sk.rlSc = true) (vs : List (BitVec 8)) (hvs : vs.length = se.sk.sz) :
    readView ws aq rl (srcsView ws (srcR rs1)) ((X.ev (h, s.evs.length)).pa : Int)
      (uniTvs (kts X (rfSrc X (h, s.evs.length) (X.ev (h, s.evs.length)).pa)) vs) ≤ vo X (h, s.evs.length) := by
  have hpre := (ldPre_le c hinv hx hrs hm hld hii hadep aq rl haq hrl).1
  have hid := c.id hm
  have hsk := c.sk hm
  have hrm : (X.sk (h, s.evs.length)).kind.isMem = true := by rw [hsk]; exact Kind.isMem_of_isLoad _ hld
  have hsz' : (X.ev (h, s.evs.length)).sk.sz = se.sk.sz := congrArg Skel.sz hsk
  have hb := bytesMax_uni_le (fun a t => fwdView ws aq a t) (kts X (rfSrc X (h, s.evs.length)
    (X.ev (h, s.evs.length)).pa)) (vo X (h, s.evs.length)) vs ((X.ev (h, s.evs.length)).pa : Int) (fun k hk => by
      have htx : touches (X.ev (h, s.evs.length)) ((X.ev (h, s.evs.length)).pa + k) = true := by
        rw [touches_iff, hsz']; omega
      have htp : touches (X.ev (h, s.evs.length)) (X.ev (h, s.evs.length)).pa = true := by
        rw [touches_iff, hsz']; omega
      rw [rfSrc_bytes c.ref c.ss hid hrm htp htx,
        show ((X.ev (h, s.evs.length)).pa : Int) + (k : Int) = (((X.ev (h, s.evs.length)).pa + k : Nat) : Int) by
          push_cast; rfl]
      exact (fwdView_leG c hinv hm hld hii aq htx).1)
  unfold readView
  omega

/-- **A LOAD OPERATION THAT IS NOT A STORE, with annotations** (Zalasr load-acquire; LR). -/
theorem sim_loadG (c : HCtx T trs ν X h sf) (hinv : SimInv T X ν h sf s lp ws prom)
    (hx : ExtraInv X h s.evs.length ws.wVRel ws.wRes) {sk : Skel} {e1 : Ex} {t1 : List Nat} {rd rs1 sz : Nat}
    (aq rl : Bool) (hr1 : s.rd rs1 = (e1, t1)) (hrs : rs1 < 32) (hsz0 : 0 < sz) (hsz8 : sz ≤ 8)
    (hkind : sk.kind = .ld ∨ sk.kind = .lr) (hskii : sk.ii = s.ii) (hsksz : sk.sz = sz) (hadep : sk.adep = t1)
    (haq : aq = true → sk.aqSc = true) (hrl : rl = true → sk.rlSc = true)
    {s' : SSt} (hs' : s' = ((s.emit ⟨sk, e1, .c 0⟩).wr rd (.ld (h, s.evs.length) sz true, [s.evs.length])).adv)
    (hwf' : SymWf s') (hfut : Future s' sf)
    (lab : List (Nat × BitVec 8) → PLabel) (res' : List (Nat × BitVec 8) → Option PResv)
    (hlab : ∀ tvs : List (Nat × BitVec 8), tvs.length = sz → litNext lp (lab tvs) = some { lp with
      regs := lp.wr rd (sext sz (ofBytes (tvs.map Prod.snd))), pc := lp.pc + 1, q := regWL rd [.DLdRes] ++ [LInstr] })
    (hmem : ∀ tvs, loadOk (testImg T) (memOf X) ws (ldPre ws aq rl (srcsView ws (srcR rs1)))
      ((X.ev (h, s.evs.length)).pa : Int) tvs → memStep (testImg T) (memOf X) h prom ws (lab tvs) none
        { loadRun ws aq rl (srcsView ws (srcR rs1)) ((X.ev (h, s.evs.length)).pa : Int) tvs with wRes := res' tvs }
        prom)
    (hrow : ∀ tvs (tl : PF.Trace), machRow ((lab tvs, none) :: tl) = tvs.map (fun tv => tv.2.toNat) :: machRow tl)
    (hres : resOk X h (s.evs.length + 1) (res' (uniTvs (kts X (rfSrc X (h, s.evs.length) (X.ev (h, s.evs.length)).pa))
      ((X.ev (h, s.evs.length)).rdat.map bv8)))) :
    StepOkB T X ν h sf s lp ws prom s' := by
  subst hs'
  have hm : sf.evs[s.evs.length]? = some ⟨sk, e1, .c 0⟩ := prefix_get hfut.evs (by simp)
  have hml := (List.getElem?_eq_some_iff.1 hm).1
  have hid := c.id hm
  have hsk := c.sk hm
  have hev := c.ev hm
  have hldk : sk.kind.isLoad = true := by rcases hkind with e | e <;> rw [e] <;> rfl
  have hnst : sk.kind.isStore = false := by rcases hkind with e | e <;> rw [e] <;> rfl
  have hrl' : (X.sk (h, s.evs.length)).kind.isLoad = true := by rw [hsk]; exact hldk
  have hrm := Kind.isMem_of_isLoad _ hrl'
  have hrdat : (X.ev (h, s.evs.length)).rdat = ν (h, s.evs.length) := by rw [hev]; simp [concEv, hldk]
  have hsz' : (X.ev (h, s.evs.length)).sk.sz = sz := by
    rw [show (X.ev (h, s.evs.length)).sk = X.sk (h, s.evs.length) from rfl, hsk, hsksz]
  have hlen : (ν (h, s.evs.length)).length = sz := by rw [← hrdat, c.rdat_len hid hrl', hsk, hsksz]
  have hbyt : ∀ b ∈ ν (h, s.evs.length), b < 256 := by rw [← hrdat]; exact c.rdat_lt hid hrl'
  have hadep' : (⟨sk, e1, .c 0⟩ : SEv).sk.adep = (s.rd rs1).2 := by rw [hr1]; exact hadep
  -- the read
  have hpre := ldPre_le c hinv hx hrs hm hldk hskii hadep' aq rl haq hrl
  have hlok := loadOk_refG c hinv hm hldk (by show 0 < sk.sz; omega) hpre.1
    (fun h' => by simp only at h'; rw [hnst] at h'; cases h')
  have hrv := readView_le c hinv hx hrs hm hldk hskii hadep' aq rl haq hrl
    ((X.ev (h, s.evs.length)).rdat.map bv8) (by rw [List.length_map, c.rdat_len hid hrl', hsk])
  generalize htt : kts X (rfSrc X (h, s.evs.length) (X.ev (h, s.evs.length)).pa) = t at hlok hres hrv
  rw [hrdat] at hlok hres hrv
  have hstep := hmem _ hlok
  have hlab' := hlab (uniTvs t ((ν (h, s.evs.length)).map bv8)) (by simp [uniTvs_length, hlen])
  rw [uniTvs_snd] at hlab'
  generalize hwsP : { loadRun ws aq rl (srcsView ws (srcR rs1)) ((X.ev (h, s.evs.length)).pa : Int)
    (uniTvs t ((ν (h, s.evs.length)).map bv8)) with wRes := res' (uniTvs t ((ν (h, s.evs.length)).map bv8)) } = wsP
    at hstep
  have htail := solo_af (testImg T) (memOf X) h (regWL rd [.DLdRes] ++ [LInstr]) { lp with
      regs := lp.wr rd (sext sz (ofBytes ((ν (h, s.evs.length)).map bv8))), pc := lp.pc + 1,
      q := regWL rd [.DLdRes] ++ [LInstr] } wsP prom (regWL_af _ _) rfl
  rw [foldl_regWL] at htail
  have hn1 : ((s.emit ⟨sk, e1, .c 0⟩).wr rd (Ex.ld (h, s.evs.length) sz true, [s.evs.length])).adv.evs.length =
      s.evs.length + 1 := by simp
  have hii1 : ((s.emit ⟨sk, e1, .c 0⟩).wr rd (Ex.ld (h, s.evs.length) sz true, [s.evs.length])).adv.ii =
      s.ii + 1 := by simp
  refine ⟨_, _, _, _, .step _ _ none _ _ _ _ _ hlab' hstep htail, ?_, ?_⟩
  · rw [hrow, machRow_af _ (regWL_af _ _), uniTvs_toNat _ _ hbyt, hn1, rowSeg_one, if_pos hrl', hrdat]
  -- the post-view bound per byte
  have hvp : ∀ k, k < ((ν (h, s.evs.length)).map bv8).length →
      max (ldPre ws aq rl (srcsView ws (srcR rs1)))
        (fwdView ws aq (((X.ev (h, s.evs.length)).pa : Int) + k) t) ≤ vo X (h, s.evs.length) := by
    intro k hk
    rw [List.length_map, hlen] at hk
    have htx : touches (X.ev (h, s.evs.length)) ((X.ev (h, s.evs.length)).pa + k) = true := by
      rw [touches_iff, hsz']; omega
    have htp : touches (X.ev (h, s.evs.length)) (X.ev (h, s.evs.length)).pa = true := by
      rw [touches_iff, hsz']; omega
    rw [← htt, rfSrc_bytes c.ref c.ss hid hrm htp htx,
      show ((X.ev (h, s.evs.length)).pa : Int) + (k : Int) = (((X.ev (h, s.evs.length)).pa + k : Nat) : Int) by
        push_cast; rfl]
    have := (fwdView_leG c hinv hm hldk hskii aq htx).1
    have := hpre.1
    omega
  obtain ⟨i1, i2, i3, i4, i5, i8, iR, i9, i10⟩ := loadBytes_uniG aq (ldPre ws aq rl (srcsView ws (srcR rs1)))
    t ((ν (h, s.evs.length)).map bv8) ws ((X.ev (h, s.evs.length)).pa : Int)
  obtain ⟨j1, j2, j3, j4⟩ := i9 _ hvp
  have hld0 := hinv.ldv
  rw [hld0] at j2
  generalize hws1 : loadBytes aq (ldPre ws aq rl (srcsView ws (srcR rs1))) ws
    ((X.ev (h, s.evs.length)).pa : Int) (uniTvs t ((ν (h, s.evs.length)).map bv8)) = ws1
    at i1 i2 i3 i4 i5 i8 iR j1 j2 j3 j4 i10
  have hla : wsP = { ws1 with
      wVcap := max (srcsView ws (srcR rs1)) ws1.wVcap
      wVRel := if rl then max ws1.wVRel (readView ws aq rl (srcsView ws (srcR rs1))
        ((X.ev (h, s.evs.length)).pa : Int) (uniTvs t ((ν (h, s.evs.length)).map bv8))) else ws1.wVRel
      wRes := res' (uniTvs t ((ν (h, s.evs.length)).map bv8)) } := by
    rw [← hwsP, ← hws1]; rfl
  rw [hla]
  generalize hwsQ : ({ ws1 with
      wVcap := max (srcsView ws (srcR rs1)) ws1.wVcap
      wVRel := if rl then max ws1.wVRel (readView ws aq rl (srcsView ws (srcR rs1))
        ((X.ev (h, s.evs.length)).pa : Int) (uniTvs t ((ν (h, s.evs.length)).map bv8))) else ws1.wVRel
      wRes := res' (uniTvs t ((ν (h, s.evs.length)).map bv8)) } : PState) = wsQ
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8⟩ := regWE_fields wsQ rd [.DLdRes]
  obtain ⟨kV, kR⟩ := keepRR_regWE wsQ rd [.DLdRes]
  have q_vro : wsQ.wVrOld = ws1.wVrOld := by rw [← hwsQ]
  have q_vwo : wsQ.wVwOld = ws1.wVwOld := by rw [← hwsQ]
  have q_vrn : wsQ.wVrNew = ws1.wVrNew := by rw [← hwsQ]
  have q_vwn : wsQ.wVwNew = ws1.wVwNew := by rw [← hwsQ]
  have q_vcap : wsQ.wVcap = max (srcsView ws (srcR rs1)) ws1.wVcap := by rw [← hwsQ]
  have q_fwd : wsQ.wFwd = ws1.wFwd := by rw [← hwsQ]
  have q_coh : ∀ x : Int, coh wsQ x = coh ws1 x := fun x => by rw [← hwsQ]; rfl
  have q_regv : ∀ r, regv wsQ r = regv ws r := fun r => by unfold regv; rw [← hwsQ]; simp only; rw [i2]
  have q_ldv : wsQ.wLdv = ws1.wLdv := by rw [← hwsQ]
  have q_vrel : wsQ.wVRel = if rl then max ws.wVRel (readView ws aq rl (srcsView ws (srcR rs1))
      ((X.ev (h, s.evs.length)).pa : Int) (uniTvs t ((ν (h, s.evs.length)).map bv8))) else ws.wVRel := by
    rw [← hwsQ]; simp only; rw [i4]
  have q_res : wsQ.wRes = res' (uniTvs t ((ν (h, s.evs.length)).map bv8)) := by rw [← hwsQ]
  obtain ⟨hve, hvlt⟩ := ldVal_eq hlen hbyt hsz8 true (h, s.evs.length) ν rfl
  simp only [if_true] at hve
  -- order facts for a future event
  have hfutpo : ∀ j, s.evs.length + 1 ≤ j → j < sf.evs.length → poX X (h, s.evs.length) (h, j) = true := by
    intro j h1 h2
    have hjii := fut_ii hfut hii1 (by rw [hn1]; exact h1) h2
    exact c.po_of hm (List.getElem?_eq_getElem h2) (by simp only; omega)
  have hacq : aq = true → ∀ j, s.evs.length + 1 ≤ j → j < sf.evs.length →
      (X.sk (h, j)).kind.isMem = true → gB X.gmo (h, s.evs.length) (h, j) = true := by
    intro haq' j h1 h2 hjm
    exact gB_of_ppo c.ref c.io hid (fut_ev c h2).1 (ppo_r5 c.io hrm hjm (hfutpo j h1 h2) (by rw [hsk]; exact haq haq'))
  refine ⟨⟨hwf', hfut, by simp [hinv.prog], by simp [hinv.pc], rfl, by simp [LP.wr_len, hinv.lpLen], ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · -- regEq
    intro r
    rw [SSt.adv_rd]
    exact regs_wr (s := s.emit _) hinv.lpLen hinv.wf.len (fun r => by rw [SSt.emit_rd]; exact hinv.regEq r) rd _ _
      hve r
  · intro r
    rw [SSt.adv_rd]
    exact regsLt_wr (s := s.emit _) (fun r => by rw [SSt.emit_rd]; exact hinv.regLt r) rd _ hvlt r
  · -- regv
    intro r h0 h32
    rw [SSt.adv_rd]
    have hregv' : ∀ r, 0 < r → r < 32 → domF (fun j => vo X (h, j))
        (· ∈ ((s.emit ⟨sk, e1, .c 0⟩).rd r).2) (regv wsQ r) := by
      intro r h0 h32
      rw [SSt.emit_rd, q_regv]; exact hinv.regv r h0 h32
    exact regv_wr hregv' hinv.wf.len rd _ _
      (by rw [srcsView_ld, q_ldv]; exact domF_of _ _ (List.mem_singleton_self _) (by omega)) r h0 h32
  · -- vrOld
    show domF _ _ (instrE (regWE wsQ rd [.DLdRes])).wVrOld
    rw [show (instrE (regWE wsQ rd [.DLdRes])).wVrOld = wsQ.wVrOld from f1, q_vro, hn1]
    exact domF_le (domF_max (domF_mono hinv.vrOld (fun j hj => ⟨by omega, hj.2⟩))
      (domF_of _ s.evs.length ⟨by omega, hrl'⟩ (Nat.le_refl _))) j1
  · -- vwOld
    show domF _ _ (instrE (regWE wsQ rd [.DLdRes])).wVwOld
    rw [show (instrE (regWE wsQ rd [.DLdRes])).wVwOld = wsQ.wVwOld from f2, q_vwo, i5, hn1]
    exact domF_mono hinv.vwOld (fun j hj => ⟨by omega, hj.2⟩)
  · -- vrNew: rule 5
    intro j h1 h2 h3
    show (instrE (regWE wsQ rd [.DLdRes])).wVrNew ≤ _ ∧ (_ → (instrE (regWE wsQ rd [.DLdRes])).wVrNew < _)
    rw [show (instrE (regWE wsQ rd [.DLdRes])).wVrNew = wsQ.wVrNew from f3, q_vrn]
    rw [hn1] at h1
    have hold := hinv.vrNew j (by omega) h2 h3
    cases haq' : aq
    · rw [haq'] at j3; simp only [Bool.false_eq_true, if_false] at j3
      exact ⟨by omega, fun hs => by have := hold.2 hs; omega⟩
    · rw [haq'] at j3; simp only [if_true] at j3
      have hg := vo_of_gB (hacq haq' j h1 h2 (Kind.isMem_of_isLoad _ h3))
      exact ⟨by omega, fun hs => by have := hold.2 hs; have := hg.2 hs; omega⟩
  · -- vwNew: rule 5
    intro j h1 h2 h3
    show (instrE (regWE wsQ rd [.DLdRes])).wVwNew < _
    rw [show (instrE (regWE wsQ rd [.DLdRes])).wVwNew = wsQ.wVwNew from f4, q_vwn]
    rw [hn1] at h1
    have hold := hinv.vwNew j (by omega) h2 h3
    cases haq' : aq
    · rw [haq'] at j4; simp only [Bool.false_eq_true, if_false] at j4; omega
    · rw [haq'] at j4; simp only [if_true] at j4
      have := (vo_of_gB (hacq haq' j h1 h2 (Kind.isMem_of_isStore _ h3))).2 h3
      omega
  · -- vcap: rule 13 through the address
    intro j h1 h2 h3
    show (instrE (regWE wsQ rd [.DLdRes])).wVcap < _
    rw [show (instrE (regWE wsQ rd [.DLdRes])).wVcap = wsQ.wVcap from f5, q_vcap, i3]
    rw [hn1] at h1
    obtain ⟨hjid, _, _⟩ := fut_ev c h2
    have hpo2 := hfutpo j h1 h2
    have hva : srcsView ws (srcR rs1) < vo X (h, j) := by
      refine domF_lt (domF_srcR hinv.regv hrs) (fun d hd => ?_) (by have := hinv.vcap j (by omega) h2 h3; omega)
      rw [hr1] at hd
      obtain ⟨hdid, hdm, hpo1⟩ := pf_po c hinv.wf hinv.fut (hinv.wf.taint rs1 d (by rw [hr1]; exact hd))
        (Nat.le_refl _) hml
      exact vo_lt_of_gB (gB_of_ppo c.ref c.io hdid hjid
        (ppo_r13 hdm h3 hid hrm hpo1 hpo2 (by rw [hsk, hadep]; exact hd))) h3
    have := hinv.vcap j (by omega) h2 h3
    omega
  · -- coh1
    intro x j h1 h2 h3 h4
    show coh (instrE (regWE wsQ rd [.DLdRes])) x < _
    rw [show coh (instrE (regWE wsQ rd [.DLdRes])) x = coh wsQ x from f7 x, q_coh]
    rw [hn1] at h1
    have hold := hinv.coh1 x j (by omega) h2 h3 h4
    rcases i10 x with e | ⟨k, hk, hxk, e⟩
    · rw [e]; exact hold
    · rw [e]
      rw [List.length_map, hlen] at hk
      have hx : x = (X.ev (h, s.evs.length)).pa + k := by omega
      have htx : touches (X.ev (h, s.evs.length)) x = true := by rw [touches_iff, hsz', hx]; omega
      have htp : touches (X.ev (h, s.evs.length)) (X.ev (h, s.evs.length)).pa = true := by
        rw [touches_iff, hsz']; omega
      obtain ⟨k1, k2⟩ := kts_lt_storeG c hm hldk htx h2 h3 h4 (hfutpo j h1 h2)
      have hfv := (fwdView_leG c hinv hm hldk hskii aq htx).1
      have htx' : t = kts X (rfSrc X (h, s.evs.length) x) := by rw [← htt, rfSrc_bytes c.ref c.ss hid hrm htp htx]
      rw [htx']
      have := hpre.1
      omega
  · -- coh2
    intro x j h1 h2 h3 h4 w hw hww hle
    change vo X w ≤ coh (instrE (regWE wsQ rd [.DLdRes])) x at hle
    rw [show coh (instrE (regWE wsQ rd [.DLdRes])) x = coh wsQ x from f7 x, q_coh] at hle
    rw [hn1] at h1
    rcases i10 x with e | ⟨k, hk, hxk, e⟩
    · rw [e] at hle; exact hinv.coh2 x j (by omega) h2 h3 h4 w hw hww hle
    · rw [e] at hle
      rw [List.length_map, hlen] at hk
      have hx : x = (X.ev (h, s.evs.length)).pa + k := by omega
      have htx : touches (X.ev (h, s.evs.length)) x = true := by rw [touches_iff, hsz', hx]; omega
      have htp : touches (X.ev (h, s.evs.length)) (X.ev (h, s.evs.length)).pa = true := by
        rw [touches_iff, hsz']; omega
      obtain ⟨hjid, _, _⟩ := fut_ev c h2
      have hpo2 := hfutpo j h1 h2
      have hco := corr c.ref c.io hid hjid hrl' h3 hpo2 htx h4
      have hfv := (fwdView_leG c hinv hm hldk hskii aq htx).1
      have htx' : t = kts X (rfSrc X (h, s.evs.length) x) := by rw [← htt, rfSrc_bytes c.ref c.ss hid hrm htp htx]
      rw [htx'] at hle
      have := hpre.1
      by_cases hc1 : vo X w ≤ coh ws x
      · exact hinv.coh2 x j (by omega) h2 h3 h4 w hw hww hc1
      · by_cases hc2 : vo X w ≤ kts X (rfSrc X (h, s.evs.length) x)
        · omega
        · have hvw : vo X w ≤ vo X (h, s.evs.length) := by omega
          have hws := writesB_store hww
          have hgB : gB X.gmo w (h, s.evs.length) = true :=
            gB_of_voG_le X X.gmo w _ hw hws (c.gmo_of hm (Kind.isMem_of_isLoad _ hldk))
              (by unfold vo at hvw; omega)
              (fun he => by
                subst he
                have hsk' : (X.ev (h, s.evs.length)).sk = _ := hsk
                rw [hsk'] at hws; rw [hnst] at hws; cases hws)
          have := kts_ge c.ref hw hww (.inl hgB)
          omega
  · -- fwd
    intro x
    show fwdOk X h _ _ x (get? (instrE (regWE wsQ rd [.DLdRes])).wFwd (x : Int))
    rw [show (instrE (regWE wsQ rd [.DLdRes])).wFwd = wsQ.wFwd from f6, q_fwd, i1, hn1]
    exact fwdOk_mono (hinv.fwd x) (by omega) (fun j hj1 hj2 hjs => by
      have : j = s.evs.length := by omega
      subst this; rw [hsk, hnst] at hjs; cases hjs)
  · rfl
  · rfl
  · -- prom
    intro tt
    rw [hinv.prom tt, hn1]
    constructor
    · rintro ⟨j, h1, h2, h3, h4⟩
      refine ⟨j, ?_, h2, h3, h4⟩
      rcases Nat.lt_or_ge j (s.evs.length + 1) with h5 | h5
      · have : j = s.evs.length := by omega
        subst this; rw [hsk, hnst] at h3; cases h3
      · exact h5
    · rintro ⟨j, h1, h2, h3, h4⟩
      exact ⟨j, by omega, h2, h3, h4⟩
  · -- ExtraInv
    rw [hn1, show (instrE (regWE wsQ rd [.DLdRes])).wVRel = wsQ.wVRel from kV,
      show (instrE (regWE wsQ rd [.DLdRes])).wRes = wsQ.wRes from kR, q_vrel, q_res]
    refine ⟨?_, hres⟩
    have hv0 : domF (fun j => vo X (h, j)) (fun j => j < s.evs.length + 1 ∧ (X.sk (h, j)).kind.isMem = true ∧
        (X.sk (h, j)).rlSc = true) ws.wVRel := domF_mono hx.vrel (fun j hj => ⟨by omega, hj.2⟩)
    cases hrl' : rl
    · exact hv0
    · simp only [if_true]
      exact domF_max hv0 (domF_of _ s.evs.length ⟨by omega, hrm, by rw [hsk]; exact hrl hrl'⟩ (hrl' ▸ hrv))

end loadG

end Weak.Prom.Cmp
