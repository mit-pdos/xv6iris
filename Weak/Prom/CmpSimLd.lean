/-
Weak/Prom: **completeness S3a — the load step** (`loadOk_ref`: the machine read is admissible; `sim_load`: the
whole instruction `l{b,h,w,d}[u] rd, off(rs1)` — `LLoad`, the result register write, the boundary).
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.CmpSimL

namespace Weak.Prom.Cmp

open MachCSL MachCSL.Stdpp Iris.Std
open Weak (Image Dsrc)
open Weak.Prom Weak.Prom.Mach Weak.Prom.Mach.Cert
open Weak.Prom.Ref
open PLabel

variable {T : Test} {trs : List SSt} {ν : Val} {X : Exec} {h : Nat} {sf : SSt}

theorem touches_iff (v : Ev) (x : Nat) : touches v x = true ↔ v.pa ≤ x ∧ x < v.pa + v.sk.sz := by
  simp [touches]

section load

variable {s : SSt} {lp : LP} {ws : PState} {prom : GSet Nat}

/-- THE MACHINE READ IS ADMISSIBLE: every byte answered with the load value axiom's store. -/
theorem loadOk_ref (c : HCtx T trs ν X h sf) (hinv : SimInv T X ν h sf s lp ws prom) {rs1 : Nat} (hrs : rs1 < 32)
    {se : SEv} (hm : sf.evs[s.evs.length]? = some se) (hld : se.sk.kind = .ld)
    (hadep : se.sk.adep = (s.rd rs1).2) (hpos : 0 < se.sk.sz) :
    loadOk (testImg T) (memOf X) ws (ldPre ws false false (srcsView ws (srcR rs1))) ((X.ev (h, s.evs.length)).pa : Int)
      (uniTvs (kts X (rfSrc X (h, s.evs.length) (X.ev (h, s.evs.length)).pa))
        ((X.ev (h, s.evs.length)).rdat.map bv8)) := by
  have hl := List.getElem?_eq_some_iff.1 hm
  have hid := c.id hm
  have hrl : (X.sk (h, s.evs.length)).kind.isLoad = true := by rw [c.sk hm, hld]; rfl
  have hrm := Kind.isMem_of_isLoad _ hrl
  have hlen := c.rdat_len hid hrl
  have hszr : (X.sk (h, s.evs.length)).sz = se.sk.sz := by rw [c.sk hm]
  have hpre := load_pre_le c hinv hrs hm hld hadep
  unfold loadOk
  apply bytesAll_uni
  intro k v hv
  rw [List.getElem?_map] at hv
  cases hk : (X.ev (h, s.evs.length)).rdat[k]? with
  | none => rw [hk] at hv; cases hv
  | some b =>
    rw [hk] at hv
    simp only [Option.map_some, Option.some.injEq] at hv
    subst hv
    have hkl : k < (X.sk (h, s.evs.length)).sz := by rw [← hlen]; exact (List.getElem?_eq_some_iff.1 hk).1
    obtain ⟨x, hx⟩ : ∃ x, x = (X.ev (h, s.evs.length)).pa + k := ⟨_, rfl⟩
    have hcast : ((X.ev (h, s.evs.length)).pa : Int) + (k : Int) = (x : Int) := by rw [hx]; push_cast; rfl
    rw [hcast]
    have htx : touches (X.ev (h, s.evs.length)) x = true := by
      rw [touches_iff]; unfold Exec.sk at hkl; omega
    have htp : touches (X.ev (h, s.evs.length)) (X.ev (h, s.evs.length)).pa = true := by
      rw [touches_iff]; unfold Exec.sk at hkl; omega
    have hsrc : rfSrc X (h, s.evs.length) (X.ev (h, s.evs.length)).pa = rfSrc X (h, s.evs.length) x :=
      rfSrc_bytes c.ref c.ss hid hrm htp htx
    rw [hsrc]
    have hval := ldVal c.ref c.io hid hrl hkl
    rw [hk, ← hx] at hval
    cases hval
    refine ⟨?_, .inl ?_⟩
    · -- the answered byte is the byte memory holds at the answer's timestamp
      unfold lvVal
      cases hs0 : rfSrc X (h, s.evs.length) x with
      | none =>
        simp only [kts, memByte, testImg, Int.toNat_natCast]
        rw [c.img]
      | some w =>
        obtain ⟨hwg, hww, _⟩ := rfSrc_spec hs0
        simp only [kts]
        exact memByte_st c.ref _ hwg (writesB_store hww) (writesB_touches hww)
    · -- no write between the answer and the read floor
      intro hwr
      obtain ⟨w, hwg, hws, hww, hlo, hhi⟩ := writesIn_memOf c.ref hwr
      have hnf := nonFwdMax_uni_le ws (kts X (rfSrc X (h, s.evs.length) x))
        ((X.ev (h, s.evs.length)).rdat.map bv8) ((X.ev (h, s.evs.length)).pa : Int)
      have hcases : vo X w ≤ coh ws x ∨ vo X w ≤ ldPre ws false false (srcsView ws (srcR rs1)) ∨
          vo X w ≤ kts X (rfSrc X (h, s.evs.length) x) := by
        revert hhi
        split <;> intro hhi <;> omega
      rcases hcases with h1 | h1 | h1
      · have := hinv.coh2 x s.evs.length (Nat.le_refl _) hl.1 hrl htx w hwg hww h1
        omega
      · have hgB : gB X.gmo w (h, s.evs.length) = true :=
          gB_of_voG_le X X.gmo w _ hwg hws (c.gmo_of hm (by rw [hld]; rfl)) (by unfold vo at hpre h1; omega)
            (fun he => by subst he; rw [isSt, c.sk hm, hld] at hws; cases hws)
        have := kts_ge c.ref hwg hww (.inl hgB)
        omega
      · omega

end load

theorem machRow_load (aq rl : Bool) (b : Int) (tvs : List (Nat × BitVec 8)) (asrc : List Dsrc) (o : Option Nat)
    (tl : PF.Trace) : machRow ((LLoad aq rl b tvs asrc, o) :: tl) = tvs.map (fun tv => tv.2.toNat) :: machRow tl := by
  simp [machRow, PF.loadsOf, PF.loadLikeTvs]

theorem uniTvs_toNat (t : Nat) (l : List Nat) (hb : ∀ b ∈ l, b < 256) :
    (uniTvs t (l.map bv8)).map (fun tv => tv.2.toNat) = l := by
  have : (uniTvs t (l.map bv8)).map (fun tv => tv.2.toNat) = ((uniTvs t (l.map bv8)).map Prod.snd).map BitVec.toNat := by
    simp [List.map_map, Function.comp_def]
  rw [this, uniTvs_snd, map_bv8_toNat l hb]

theorem fut_ii {s s' : SSt} (hfut : Future s' sf) (hii : s'.ii = s.ii + 1) {j : Nat} (hj : s'.evs.length ≤ j)
    (hjl : j < sf.evs.length) : s.ii < sf.evs[j].sk.ii := by
  have := (hfut.later j _ hj (List.getElem?_eq_getElem hjl)).1; omega

section load

variable {s : SSt} {lp : LP} {ws : PState} {prom : GSet Nat}

/-- **A PLAIN LOAD** `l{b,h,w,d}[u] rd, off(rs1)`. -/
theorem sim_load (c : HCtx T trs ν X h sf) (hinv : SimInv T X ν h sf s lp ws prom) {sz : Nat} {sgn : Bool}
    {rd rs1 off : Nat} (hi : (T.prog h)[s.pc]? = some (.load sz sgn rd rs1 off))
    (hok : instrS3a (.load sz sgn rd rs1 off) = true) {s' : SSt}
    (hs : stepI h (T.prog h).length s (.load sz sgn rd rs1 off) = .next s') (hfut : Future s' sf) :
    StepOk T X ν h sf s lp ws prom s' := by
  have hwf' := (symWf_step h _ hinv.wf _).1 s' hs
  simp only [instrS3a, rOk, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨hsz, hrd⟩, hrs⟩ := hok
  obtain ⟨hsz0, hsz8⟩ := szOk_le hsz
  have hev1 := hinv.regEq rs1
  have hlt1 := hinv.regLt rs1
  rcases hr1 : s.rd rs1 with ⟨e1, t1⟩
  rw [hr1] at hev1 hlt1
  simp only [stepI, hr1, Ref.StepR.next.injEq] at hs
  subst hs
  -- the reference event
  have hm : sf.evs[s.evs.length]? = some ⟨{ kind := .ld, ii := s.ii, sz := sz, adep := t1, cdep := s.ctl },
      .bin .add e1 (.c off), .c 0⟩ := prefix_get hfut.evs (by simp)
  have hml := (List.getElem?_eq_some_iff.1 hm).1
  have hid := c.id hm
  have hsk := c.sk hm
  have hev := c.ev hm
  have hrl : (X.sk (h, s.evs.length)).kind.isLoad = true := by rw [hsk]; rfl
  have hrm := Kind.isMem_of_isLoad _ hrl
  have hrdat : (X.ev (h, s.evs.length)).rdat = ν (h, s.evs.length) := by rw [hev]; rfl
  have hsz' : (X.ev (h, s.evs.length)).sk.sz = sz := congrArg Skel.sz hsk
  have hpa : (X.ev (h, s.evs.length)).pa = (Ex.bin .add e1 (.c off)).eval ν := by rw [hev]; rfl
  have hlen : (ν (h, s.evs.length)).length = sz := by rw [← hrdat, c.rdat_len hid hrl, hsk]
  have hbyt : ∀ b ∈ ν (h, s.evs.length), b < 256 := by rw [← hrdat]; exact c.rdat_lt hid hrl
  -- the machine address is the reference address, and it is aligned
  have haddr : (lp.rd rs1 + off) % two64 = (X.ev (h, s.evs.length)).pa := by
    rw [hpa, hev1]
    show _ = (e1.eval ν + off % two64) % two64
    rw [Nat.add_mod, Nat.add_mod (e1.eval ν) (off % two64), Nat.mod_mod]
  have halign : aligned ((lp.rd rs1 + off) % two64) sz = true := by
    have := List.all_eq_true.1 (c.condsSf).2 _ (List.mem_of_getElem? hm)
    simp only [Kind.isAcc, Kind.isMem, Bool.true_or, Bool.not_true, Bool.false_or, beq_iff_eq] at this
    rw [haddr, hpa]
    simp [Mach.aligned, this]
  -- the machine label
  have hpos : 0 < (⟨{ kind := .ld, ii := s.ii, sz := sz, adep := t1, cdep := s.ctl }, .bin .add e1 (.c off),
      .c 0⟩ : SEv).sk.sz := hsz0
  have hlok := loadOk_ref c hinv hrs hm rfl (by rw [hr1]) hpos
  generalize htt : kts X (rfSrc X (h, s.evs.length) (X.ev (h, s.evs.length)).pa) = t at hlok
  rw [hrdat] at hlok
  have hlab : litNext lp (LLoad false false ((X.ev (h, s.evs.length)).pa : Int) (uniTvs t ((ν (h, s.evs.length)).map bv8))
      (srcR rs1)) = some { lp with regs := lp.wr rd (if sgn then sext sz (ofBytes ((ν (h, s.evs.length)).map bv8))
        else ofBytes ((ν (h, s.evs.length)).map bv8)), pc := lp.pc + 1, q := regWL rd [.DLdRes] ++ [LInstr] } := by
    simp only [litNext, hinv.q, lpi_of hinv hi, instrNext]
    rw [halign]
    simp only [Bool.not_true, Bool.false_eq_true, if_false]
    rw [haddr, uniTvs_snd]
    simp [uniTvs_length, List.length_map, hlen]
  have hmem : memStep (testImg T) (memOf X) h prom ws
      (LLoad false false ((X.ev (h, s.evs.length)).pa : Int) (uniTvs t ((ν (h, s.evs.length)).map bv8)) (srcR rs1))
      none (loadRun ws false false (srcsView ws (srcR rs1)) ((X.ev (h, s.evs.length)).pa : Int)
        (uniTvs t ((ν (h, s.evs.length)).map bv8))) prom := .load _ _ _ _ _ _ _ hlok
  have htail := solo_af (testImg T) (memOf X) h (regWL rd [.DLdRes] ++ [LInstr]) { lp with
      regs := lp.wr rd (if sgn then sext sz (ofBytes ((ν (h, s.evs.length)).map bv8))
        else ofBytes ((ν (h, s.evs.length)).map bv8)), pc := lp.pc + 1, q := regWL rd [.DLdRes] ++ [LInstr] }
    (loadRun ws false false (srcsView ws (srcR rs1)) ((X.ev (h, s.evs.length)).pa : Int)
      (uniTvs t ((ν (h, s.evs.length)).map bv8))) prom (regWL_af _ _) rfl
  rw [foldl_regWL] at htail
  refine ⟨_, _, _, _, .step _ _ none _ _ _ _ _ hlab hmem htail, ?_, ?_⟩
  · -- the row
    rw [machRow_load, machRow_af _ (regWL_af _ _), uniTvs_toNat _ _ hbyt]
    have : ((s.emit ⟨{ kind := .ld, ii := s.ii, sz := sz, adep := t1, cdep := s.ctl }, .bin .add e1 (.c off), .c 0⟩).wr
        rd (Ex.ld (h, s.evs.length) sz sgn, [s.evs.length])).adv.evs.length = s.evs.length + 1 := by simp
    rw [this, rowSeg_one, if_pos hrl, hrdat]
  -- the invariant
  have hvpre := load_pre_le c hinv hrs hm rfl (by rw [hr1])
  have hvp : ∀ k, k < ((ν (h, s.evs.length)).map bv8).length →
      max (ldPre ws false false (srcsView ws (srcR rs1)))
        (fwdView ws false (((X.ev (h, s.evs.length)).pa : Int) + k) t) ≤ vo X (h, s.evs.length) := by
    intro k hk
    rw [List.length_map, hlen] at hk
    have htx : touches (X.ev (h, s.evs.length)) ((X.ev (h, s.evs.length)).pa + k) = true := by
      rw [touches_iff, hsz']; omega
    have htp : touches (X.ev (h, s.evs.length)) (X.ev (h, s.evs.length)).pa = true := by
      rw [touches_iff, hsz']; omega
    rw [← htt, rfSrc_bytes c.ref c.ss hid hrm htp htx,
      show ((X.ev (h, s.evs.length)).pa : Int) + (k : Int) = (((X.ev (h, s.evs.length)).pa + k : Nat) : Int) by
        push_cast; rfl]
    have := fwdView_le_vo c hinv hm rfl rfl htx
    omega
  obtain ⟨i1, i2, i3, i4, i5, i6, i7, i8, i9, i10⟩ := loadBytes_uni (ldPre ws false false (srcsView ws (srcR rs1)))
    t ((ν (h, s.evs.length)).map bv8) ws ((X.ev (h, s.evs.length)).pa : Int)
  obtain ⟨j1, j2⟩ := i9 _ hvp
  have hld0 := hinv.ldv
  rw [hld0] at j2
  -- field facts of the final agent state
  generalize hws1 : loadBytes false (ldPre ws false false (srcsView ws (srcR rs1))) ws
    ((X.ev (h, s.evs.length)).pa : Int) (uniTvs t ((ν (h, s.evs.length)).map bv8)) = ws1 at i1 i2 i3 i4 i5 i6 i7 i8 j1 j2 i10
  have hla : loadRun ws false false (srcsView ws (srcR rs1)) ((X.ev (h, s.evs.length)).pa : Int)
      (uniTvs t ((ν (h, s.evs.length)).map bv8)) = { ws1 with wVcap := max (srcsView ws (srcR rs1)) ws1.wVcap } := by
    rw [← hws1]; rfl
  rw [hla]
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8⟩ := regWE_fields { ws1 with wVcap := max (srcsView ws (srcR rs1)) ws1.wVcap }
    rd [.DLdRes]
  have g_vro : (instrE (regWE { ws1 with wVcap := max (srcsView ws (srcR rs1)) ws1.wVcap } rd [.DLdRes])).wVrOld =
      ws1.wVrOld := f1
  have g_vwo : (instrE (regWE { ws1 with wVcap := max (srcsView ws (srcR rs1)) ws1.wVcap } rd [.DLdRes])).wVwOld =
      ws.wVwOld := f2.trans i5
  have g_vrn : (instrE (regWE { ws1 with wVcap := max (srcsView ws (srcR rs1)) ws1.wVcap } rd [.DLdRes])).wVrNew =
      ws.wVrNew := f3.trans i6
  have g_vwn : (instrE (regWE { ws1 with wVcap := max (srcsView ws (srcR rs1)) ws1.wVcap } rd [.DLdRes])).wVwNew =
      ws.wVwNew := f4.trans i7
  have g_vcap : (instrE (regWE { ws1 with wVcap := max (srcsView ws (srcR rs1)) ws1.wVcap } rd [.DLdRes])).wVcap =
      max (srcsView ws (srcR rs1)) ws.wVcap := by rw [← i3]; exact f5
  have g_fwd : (instrE (regWE { ws1 with wVcap := max (srcsView ws (srcR rs1)) ws1.wVcap } rd [.DLdRes])).wFwd =
      ws.wFwd := f6.trans i1
  have g_coh : ∀ x : Int, coh (instrE (regWE { ws1 with wVcap := max (srcsView ws (srcR rs1)) ws1.wVcap } rd
      [.DLdRes])) x = coh ws1 x := fun x => f7 x
  have hn1 : ((s.emit ⟨{ kind := .ld, ii := s.ii, sz := sz, adep := t1, cdep := s.ctl }, .bin .add e1 (.c off), .c 0⟩).wr
      rd (Ex.ld (h, s.evs.length) sz sgn, [s.evs.length])).adv.evs.length = s.evs.length + 1 := by simp
  have hii1 : ((s.emit ⟨{ kind := .ld, ii := s.ii, sz := sz, adep := t1, cdep := s.ctl }, .bin .add e1 (.c off), .c 0⟩).wr
      rd (Ex.ld (h, s.evs.length) sz sgn, [s.evs.length])).adv.ii = s.ii + 1 := by simp
  obtain ⟨hve, hvlt⟩ := ldVal_eq hlen hbyt hsz8 sgn (h, s.evs.length) ν rfl
  refine ⟨hwf', hfut, by simp [hinv.prog], by simp [hinv.pc], rfl, by simp [LP.wr_len, hinv.lpLen], ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- regEq
    intro r
    rw [SSt.adv_rd]
    exact regs_wr (s := s.emit _) hinv.lpLen hinv.wf.len (fun r => by rw [SSt.emit_rd]; exact hinv.regEq r) rd _ _
      hve r
  · -- regLt
    intro r
    rw [SSt.adv_rd]
    exact regsLt_wr (s := s.emit _) (fun r => by rw [SSt.emit_rd]; exact hinv.regLt r) rd _ hvlt r
  · -- regv
    intro r h0 h32
    rw [SSt.adv_rd]
    have hregv' : ∀ r, 0 < r → r < 32 → domF (fun j => vo X (h, j))
        (· ∈ ((s.emit ⟨{ kind := .ld, ii := s.ii, sz := sz, adep := t1, cdep := s.ctl }, .bin .add e1 (.c off),
          .c 0⟩).rd r).2) (regv { ws1 with wVcap := max (srcsView ws (srcR rs1)) ws1.wVcap } r) := by
      intro r h0 h32
      rw [SSt.emit_rd]
      have : regv { ws1 with wVcap := max (srcsView ws (srcR rs1)) ws1.wVcap } r = regv ws r := by
        unfold regv; simp only; rw [i2]
      rw [this]; exact hinv.regv r h0 h32
    exact regv_wr hregv' hinv.wf.len rd _ _ (by rw [srcsView_ld]; exact domF_of _ _ (List.mem_singleton_self _) j2)
      r h0 h32
  · -- vrOld
    rw [g_vro, hn1]
    exact domF_le (domF_max (domF_mono hinv.vrOld (fun j hj => ⟨by omega, hj.2⟩))
      (domF_of _ s.evs.length ⟨by omega, hrl⟩ (Nat.le_refl _))) j1
  · -- vwOld
    rw [g_vwo, hn1]
    exact domF_mono hinv.vwOld (fun j hj => ⟨by omega, hj.2⟩)
  · intro j h1 h2 h3
    rw [g_vrn]
    exact hinv.vrNew j (by rw [hn1] at h1; omega) h2 h3
  · intro j h1 h2 h3
    rw [g_vwn]
    exact hinv.vwNew j (by rw [hn1] at h1; omega) h2 h3
  · -- vcap: rule 13 through the load's address
    intro j h1 h2 h3
    rw [g_vcap]
    rw [hn1] at h1
    have hjii := fut_ii hfut hii1 (by rw [hn1]; exact h1) h2
    obtain ⟨hjid, _, _⟩ := fut_ev c h2
    have hpo2 : poX X (h, s.evs.length) (h, j) = true := c.po_of hm (List.getElem?_eq_getElem h2) hjii
    have hva : srcsView ws (srcR rs1) < vo X (h, j) := by
      refine domF_lt (domF_srcR hinv.regv hrs) (fun d hd => ?_) (by have := hinv.vcap j (by omega) h2 h3; omega)
      rw [hr1] at hd
      obtain ⟨hdid, hdm, hpo1⟩ := pf_po c hinv.wf hinv.fut (hinv.wf.taint rs1 d (by rw [hr1]; exact hd))
        (Nat.le_refl _) hml
      exact vo_lt_of_gB (gB_of_ppo c.ref c.io hdid hjid
        (ppo_r13 hdm h3 hid hrm hpo1 hpo2 (by rw [hsk]; exact hd))) h3
    have := hinv.vcap j (by omega) h2 h3
    omega
  · -- coh1
    intro x j h1 h2 h3 h4
    rw [g_coh]
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
      have hjii := fut_ii hfut hii1 (by rw [hn1]; exact h1) h2
      obtain ⟨k1, k2⟩ := kts_lt_store c hinv hm rfl rfl htx (by omega) h2 h3 h4 hjii
      have hfv := fwdView_le_vo c hinv hm rfl rfl htx
      have htx' : t = kts X (rfSrc X (h, s.evs.length) x) := by rw [← htt, rfSrc_bytes c.ref c.ss hid hrm htp htx]
      rw [htx']
      omega
  · -- coh2
    intro x j h1 h2 h3 h4 w hw hww hle
    rw [g_coh] at hle
    rw [hn1] at h1
    rcases i10 x with e | ⟨k, hk, hxk, e⟩
    · rw [e] at hle; exact hinv.coh2 x j (by omega) h2 h3 h4 w hw hww hle
    · rw [e] at hle
      rw [List.length_map, hlen] at hk
      have hx : x = (X.ev (h, s.evs.length)).pa + k := by omega
      have htx : touches (X.ev (h, s.evs.length)) x = true := by rw [touches_iff, hsz', hx]; omega
      have htp : touches (X.ev (h, s.evs.length)) (X.ev (h, s.evs.length)).pa = true := by
        rw [touches_iff, hsz']; omega
      have hjii := fut_ii hfut hii1 (by rw [hn1]; exact h1) h2
      obtain ⟨hjid, _, _⟩ := fut_ev c h2
      have hpo2 : poX X (h, s.evs.length) (h, j) = true := c.po_of hm (List.getElem?_eq_getElem h2) hjii
      have hco := corr c.ref c.io hid hjid hrl h3 hpo2 htx h4
      have hfv := fwdView_le_vo c hinv hm rfl rfl htx
      have htx' : t = kts X (rfSrc X (h, s.evs.length) x) := by rw [← htt, rfSrc_bytes c.ref c.ss hid hrm htp htx]
      rw [htx'] at hle
      by_cases hc1 : vo X w ≤ coh ws x
      · exact hinv.coh2 x j (by omega) h2 h3 h4 w hw hww hc1
      · by_cases hc2 : vo X w ≤ kts X (rfSrc X (h, s.evs.length) x)
        · omega
        · -- below the post-view, hence gmo-before the load
          have hvw : vo X w ≤ vo X (h, s.evs.length) := by omega
          have hws := writesB_store hww
          have hgB : gB X.gmo w (h, s.evs.length) = true :=
            gB_of_voG_le X X.gmo w _ hw hws (c.gmo_of hm rfl) (by unfold vo at hvw; omega)
              (fun he => by
                subst he
                have hsk' : (X.ev (h, s.evs.length)).sk = _ := hsk
                rw [hsk'] at hws; cases hws)
          have := kts_ge c.ref hw hww (.inl hgB)
          omega
  · -- fwd
    intro x
    rw [g_fwd, hn1]
    exact fwdOk_mono (hinv.fwd x) (by omega) (fun j hj1 hj2 hjs => by
      have : j = s.evs.length := by omega
      subst this; rw [hsk] at hjs; cases hjs)
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
        subst this; rw [hsk] at h3; cases h3
      · exact h5
    · rintro ⟨j, h1, h2, h3, h4⟩
      exact ⟨j, by omega, h2, h3, h4⟩

end load

end Weak.Prom.Cmp
