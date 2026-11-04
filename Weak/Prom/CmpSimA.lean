/-
Weak/Prom: **completeness S3b — the AMO** (S3b-AMO; plan §6 table: rules 3, 5, 6, 7, atomicity, M0).

`amo<op>{.aq}{.rl} rd, rs2, (rs1)` is ONE memory operation that is both a load and a store (rvwmo.adoc:73–74 "An
aligned AMO gives rise to a single memory operation that is both a load operation and a store operation
simultaneously"): the reference event `e` is at gmo view `ts = vo X e`.  Machine v2's fused arm `memStep.rmw` (M0)
reads at `ldPre ws aq false va` (no release on the read half) and writes at `ts`:
* the read is admissible STRICTLY below `ts` (`ldPre_le`, `fwdView_leG`, the strict invariant conjuncts);
* the atomicity window `exclOk` (no other write to a read byte in `(t, ts)`) holds because a write between the
  answer and the AMO in gmo would be a later candidate of the load value axiom (`rfSrc_max`) — the AMO reads its
  bytes' gmo-immediate predecessor;
* COH at the post-read state (the read raised `coh` to values below `ts`), EXT (`stPre` at the post-read state:
  `stPreA_lt`, rule 6 for `rl`, the read's post-views below `ts`);
* post `amoPost (storeRun …)`: `vrOld ⊔= ts` (the AMO is a load), forward view `ts` (M1; rule 3, `fvOk_rmw`), an
  acquire raises both new-floors to `ts` (rule 5), a release raises `wVRel` (rule 7, `ExtraInv.vrel`).
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.CmpSimSC

namespace Weak.Prom.Cmp

open MachCSL MachCSL.Stdpp Iris.Std
open Weak (Image Dsrc)
open Weak.Prom Weak.Prom.Mach Weak.Prom.Mach.Cert
open Weak.Prom.Ref
open PLabel

variable {T : Test} {trs : List SSt} {ν : Val} {X : Exec} {h : Nat} {sf : SSt}

/-! ## 1. Values -/

theorem sext_mod {sz v : Nat} (hsz : sz ≤ 8) (hv : v < 2 ^ (8 * sz)) : sext sz v % 2 ^ (8 * sz) = v := by
  unfold sext
  split
  · have h64 : two64 = 2 ^ (8 * sz) * 2 ^ (64 - 8 * sz) := by
      rw [← Nat.pow_add, show 8 * sz + (64 - 8 * sz) = 64 by omega]; rfl
    have hk : two64 - 2 ^ (8 * sz) = 2 ^ (8 * sz) * (2 ^ (64 - 8 * sz) - 1) := by
      rw [h64, Nat.mul_sub_one]
    rw [hk, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hv]
  · exact Nat.mod_eq_of_lt hv

/-- The AMO's written bytes, machine side (MachCert.lean `instrNext`) = reference side (RefProg.lean `Ex.amo`). -/
theorem amo_data {rdat : List Nat} {sz : Nat} (hl : rdat.length = sz) (hb : ∀ b ∈ rdat, b < 256) (hsz : sz ≤ 8)
    (op : AmoOp) (e : EvId) (ν : Val) (hν : ν e = rdat) (e2 : Ex) (v2 : Nat) (hv2 : v2 = e2.eval ν) :
    toBytes (amoOp op sz (ofBytes (rdat.map bv8)) (v2 % 2 ^ (8 * sz))) sz =
      (byteList ((Ex.amo op sz (.ld e sz true) e2).eval ν) sz).map bv8 := by
  have hof : ofBytes (rdat.map bv8) = bytesVal rdat := by unfold ofBytes; rw [map_bv8_toNat rdat hb]
  have hlt : bytesVal rdat < 2 ^ (8 * sz) := hl ▸ bytesVal_lt rdat hb
  have hev : (Ex.ld e sz true).eval ν = sext sz (bytesVal rdat) := by
    simp only [Ex.eval, hν, ← hl, List.take_length, if_true]
    rw [Nat.mod_eq_of_lt (hl ▸ hlt)]
  have : (Ex.amo op sz (.ld e sz true) e2).eval ν = amoOp op sz ((Ex.ld e sz true).eval ν % 2 ^ (8 * sz))
      (e2.eval ν % 2 ^ (8 * sz)) := rfl
  rw [this, hev, sext_mod hsz hlt, hof, hv2]
  rfl

theorem machRow_rmw (aq rl : Bool) (b : Int) (tvs : List (Nat × BitVec 8)) (d : List (BitVec 8))
    (asrc vsrc : List Dsrc) (o : Option Nat) (tl : PF.Trace) :
    machRow ((LRmw aq rl b tvs d asrc vsrc, o) :: tl) = tvs.map (fun tv => tv.2.toNat) :: machRow tl := by
  simp [machRow, PF.loadsOf, PF.loadLikeTvs]

theorem amoPost_fields (ws : PState) (rl : Bool) (va : Nat) (base : Int) (n ts : Nat) (aq : Bool) :
    (amoPost (storeRun ws rl va ts base n ts) aq ts).wVrOld = max ws.wVrOld ts ∧
    (amoPost (storeRun ws rl va ts base n ts) aq ts).wVwOld = max ws.wVwOld ts ∧
    (amoPost (storeRun ws rl va ts base n ts) aq ts).wVrNew = (if aq then max ws.wVrNew ts else ws.wVrNew) ∧
    (amoPost (storeRun ws rl va ts base n ts) aq ts).wVwNew = (if aq then max ws.wVwNew ts else ws.wVwNew) ∧
    (amoPost (storeRun ws rl va ts base n ts) aq ts).wVcap = max va ws.wVcap ∧
    (amoPost (storeRun ws rl va ts base n ts) aq ts).wVRel = (if rl then max ws.wVRel ts else ws.wVRel) ∧
    (amoPost (storeRun ws rl va ts base n ts) aq ts).wRegv = ws.wRegv ∧
    (amoPost (storeRun ws rl va ts base n ts) aq ts).wLdv = max ws.wLdv ts ∧
    (amoPost (storeRun ws rl va ts base n ts) aq ts).wIfv = ws.wIfv ∧
    (amoPost (storeRun ws rl va ts base n ts) aq ts).wRes = ws.wRes ∧
    (∀ b : Int, coh (amoPost (storeRun ws rl va ts base n ts) aq ts) b =
      if base ≤ b ∧ b < base + n then max (coh ws b) ts else coh ws b) ∧
    (∀ b : Int, get? (amoPost (storeRun ws rl va ts base n ts) aq ts).wFwd b =
      if base ≤ b ∧ b < base + n then some (ts, ts) else get? ws.wFwd b) := by
  obtain ⟨i1, i2, i3, i4, i5, i6, i7, i8, i9, i10, i11⟩ := storeBytes_spec n ws base ts ts
  have iR := (keepRR_storeBytes ws base n ts ts).2
  refine ⟨by simp only [amoPost, storeRun]; rw [i5], by simp only [amoPost, storeRun]; rw [i6], ?_, ?_,
    by simp only [amoPost, storeRun]; rw [i4], by simp only [amoPost, storeRun]; rw [i11],
    by simp only [amoPost, storeRun]; rw [i3], by simp only [amoPost, storeRun]; rw [i9], i10, iR,
    fun b => i1 b, fun b => i2 b⟩
  · simp only [amoPost, storeRun]; rw [i7]
  · simp only [amoPost, storeRun]; rw [i8]

/-- The AMO's write pre-view at the post-read state (arithmetic only). -/
theorem stPre_post_lt {ws ws1 : PState} {va vd ts B : Nat} (aq rl : Bool) (hw : stPreA ws false rl va vd < ts)
    (hB : B < ts) (hifv : ws1.wIfv = ws.wIfv) (hvwo : ws1.wVwOld = ws.wVwOld) (hcap : ws1.wVcap = ws.wVcap)
    (hrn : ws1.wVrOld ≤ max ws.wVrOld B) (hwn : ws1.wVwNew ≤ max ws.wVwNew (if aq then B else 0)) :
    stPre { ws1 with wVcap := max va ws1.wVcap } rl va vd < ts := by
  simp only [stPreA, stPre, Bool.false_eq_true, if_false] at hw ⊢
  rw [hifv, hvwo, hcap]
  have hwn' : ws1.wVwNew < ts := by
    cases aq <;> simp only [Bool.false_eq_true, if_false, if_true] at hwn
    · simp only [Nat.max_lt] at hw; omega
    · simp only [Nat.max_lt] at hw; omega
  cases rl
  · simp only [Bool.false_eq_true, if_false, Nat.max_lt] at hw ⊢
    obtain ⟨⟨a1, a2, a3, a4, _, a6⟩, _⟩ := hw
    exact ⟨a1, a2, a3, ⟨a1, a4⟩, hwn', a6⟩
  · simp only [if_true, Nat.max_lt] at hw ⊢
    obtain ⟨⟨a1, a2, a3, a4, _, a6, a7⟩, _⟩ := hw
    exact ⟨a1, a2, a3, ⟨a1, a4⟩, hwn', ⟨by omega, a7⟩⟩

section amo

variable {s : SSt} {lp : LP} {ws : PState} {prom : GSet Nat}

/-- A store's answer for a byte it writes is strictly below it (rule 1 makes every candidate gmo-before it). -/
theorem kts_lt_self (c : HCtx T trs ν X h sf) {se : SEv} (hm : sf.evs[s.evs.length]? = some se)
    (hst : se.sk.kind.isStore = true) {x : Nat} (htx : touches (X.ev (h, s.evs.length)) x = true) :
    kts X (rfSrc X (h, s.evs.length) x) < vo X (h, s.evs.length) := by
  have hid := c.id hm
  have hst' : (X.sk (h, s.evs.length)).kind.isStore = true := by rw [c.sk hm]; exact hst
  have heg := c.gmo_of hm (Kind.isMem_of_isStore _ hst)
  cases hs0 : rfSrc X (h, s.evs.length) x with
  | none =>
    simp only [kts]
    have := voG_st_pos X X.gmo _ heg hst'; unfold vo; omega
  | some s0 =>
    simp only [kts]
    obtain ⟨hsg, hsw, _⟩ := rfSrc_spec hs0
    have hg : gB X.gmo s0 (h, s.evs.length) = true := by
      cases hg : gB X.gmo s0 (h, s.evs.length)
      · obtain ⟨hpo0, _⟩ := srcFwd c.ref c.io hs0 hg
        have := gB_of_ppo c.ref c.io (ids_of_gmo hsg c.ref) hid
          (ppo_r1 (Kind.isMem_of_isStore _ (writesB_store hsw)) hst' hpo0 (overlap_of_touch (writesB_touches hsw) htx))
        rw [hg] at this; cases this
      · rfl
    exact vo_lt_of_gB hg hst'

-- The proof term is large (one memory operation that is both a load and a store); elaboration only.
set_option maxHeartbeats 1000000 in
/-- **`amo<op>{.aq}{.rl} rd, rs2, (rs1)`** (Zaamo; the fused AMO, M0). -/
theorem sim_amo (c : HCtx T trs ν X h sf) (hinv : SimInv T X ν h sf s lp ws prom)
    (hx : ExtraInv X h s.evs.length ws.wVRel ws.wRes) {op : AmoOp} {sz : Nat} {aq0 rl0 : Bool} {rd rs2 rs1 : Nat}
    (hi : (T.prog h)[s.pc]? = some (.amo op sz aq0 rl0 rd rs2 rs1))
    (hok : instrS3b (.amo op sz aq0 rl0 rd rs2 rs1) = true) {s' : SSt}
    (hs : stepI h (T.prog h).length s (.amo op sz aq0 rl0 rd rs2 rs1) = .next s') (hfut : Future s' sf) :
    StepOkB T X ν h sf s lp ws prom s' := by
  have hwf' := (symWf_step h _ hinv.wf _).1 s' hs
  simp only [instrS3b, rOk, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨hsz, hrd⟩, hrs2⟩, hrs1⟩ := hok
  obtain ⟨hsz0, hsz8⟩ := szOk_le hsz
  have hev2 := hinv.regEq rs2
  rcases hr1 : s.rd rs1 with ⟨e1, t1⟩
  rcases hr2 : s.rd rs2 with ⟨e2, t2⟩
  rw [hr2] at hev2
  simp only [stepI, hr1, hr2, Ref.StepR.next.injEq] at hs
  subst hs
  have hm : sf.evs[s.evs.length]? = some
      ⟨{ kind := .amo, ii := s.ii, sz := sz, aqSc := aq0, rlSc := rl0, adep := t1, ddep := t2, cdep := s.ctl },
        e1, .amo op sz (.ld (h, s.evs.length) sz true) e2⟩ := prefix_get hfut.evs (by simp)
  have hml := (List.getElem?_eq_some_iff.1 hm).1
  have hid := c.id hm
  have hsk := c.sk hm
  have hev := c.ev hm
  have hrl' : (X.sk (h, s.evs.length)).kind.isLoad = true := by rw [hsk]; rfl
  have hst : (X.sk (h, s.evs.length)).kind.isStore = true := by rw [hsk]; rfl
  have hrm := Kind.isMem_of_isLoad _ hrl'
  have hwg : (h, s.evs.length) ∈ X.gmo := (mem_gmo c.ref _).2 ⟨hid, hrm⟩
  have hrdat : (X.ev (h, s.evs.length)).rdat = ν (h, s.evs.length) := by rw [hev]; rfl
  have hwdat : (X.ev (h, s.evs.length)).wdat =
      byteList ((Ex.amo op sz (.ld (h, s.evs.length) sz true) e2).eval ν) sz := by rw [hev]; rfl
  have hsz' : (X.ev (h, s.evs.length)).sk.sz = sz := by
    rw [show (X.ev (h, s.evs.length)).sk = X.sk (h, s.evs.length) from rfl, hsk]
  have hlen : (ν (h, s.evs.length)).length = sz := by rw [← hrdat, c.rdat_len hid hrl', hsk]
  have hbyt : ∀ b ∈ ν (h, s.evs.length), b < 256 := by rw [← hrdat]; exact c.rdat_lt hid hrl'
  obtain ⟨haddr, halign⟩ := addr_noOff c hinv hr1 hm rfl
  have hn1 : ((s.emit ⟨{ kind := .amo, ii := s.ii, sz := sz, aqSc := aq0, rlSc := rl0, adep := t1, ddep := t2, cdep := s.ctl }, e1, .amo op sz (.ld (h, s.evs.length) sz true) e2⟩).wr rd (Ex.ld (h, s.evs.length) sz true, [s.evs.length])).adv.evs.length = s.evs.length + 1 := by simp
  have hii1 : ((s.emit ⟨{ kind := .amo, ii := s.ii, sz := sz, aqSc := aq0, rlSc := rl0, adep := t1, ddep := t2, cdep := s.ctl }, e1, .amo op sz (.ld (h, s.evs.length) sz true) e2⟩).wr rd (Ex.ld (h, s.evs.length) sz true, [s.evs.length])).adv.ii = s.ii + 1 := by simp
  have hpos := voG_st_pos X X.gmo _ hwg hst
  -- the read: strictly below the AMO's view
  have hpre := ldPre_le c hinv hx hrs1 hm rfl rfl (by rw [hr1]) aq0 false (fun h' => h') (fun h' => by cases h')
  have hpreS := hpre.2 rfl
  have hlok := loadOk_refG c hinv hm rfl (by show 0 < sz; omega) hpre.1 hpre.2
  have hwpre := stPreA_lt c hinv hx hrs1 hrs2 hm rfl rfl (by rw [hr1]) (by rw [hr2]) false rl0 (fun h' => by cases h')
    (fun h' => h') _ rfl
  -- per byte facts
  have hbyte : ∀ k, k < sz →
      kts X (rfSrc X (h, s.evs.length) (X.ev (h, s.evs.length)).pa) =
        kts X (rfSrc X (h, s.evs.length) ((X.ev (h, s.evs.length)).pa + k)) ∧
      touches (X.ev (h, s.evs.length)) ((X.ev (h, s.evs.length)).pa + k) = true := by
    intro k hk
    have htx : touches (X.ev (h, s.evs.length)) ((X.ev (h, s.evs.length)).pa + k) = true := by
      rw [touches_iff, hsz']; omega
    have htp : touches (X.ev (h, s.evs.length)) (X.ev (h, s.evs.length)).pa = true := by
      rw [touches_iff, hsz']; omega
    exact ⟨by rw [rfSrc_bytes c.ref c.ss hid hrm htp htx], htx⟩
  generalize htt : kts X (rfSrc X (h, s.evs.length) (X.ev (h, s.evs.length)).pa) = t at hlok hbyte
  rw [hrdat] at hlok
  generalize hts : vo X (h, s.evs.length) = ts at hpre hpreS hwpre hpos
  have hfw : ∀ k, k < sz → fwdView ws aq0 (((X.ev (h, s.evs.length)).pa : Int) + k) t < ts ∧ t < ts := by
    intro k hk
    obtain ⟨e, htx⟩ := hbyte k hk
    rw [e, show ((X.ev (h, s.evs.length)).pa : Int) + (k : Int) = (((X.ev (h, s.evs.length)).pa + k : Nat) : Int) by
      push_cast; rfl]
    have a1 := (fwdView_leG c hinv hm rfl rfl aq0 htx).2 rfl
    have a2 := kts_lt_self c hm rfl htx
    rw [hts] at a1 a2
    exact ⟨a1, a2⟩
  have hvp : ∀ k, k < ((ν (h, s.evs.length)).map bv8).length →
      max (ldPre ws aq0 false (srcsView ws (srcR rs1))) (fwdView ws aq0 (((X.ev (h, s.evs.length)).pa : Int) + k) t)
        ≤ ts - 1 := by
    intro k hk
    rw [List.length_map, hlen] at hk
    have := (hfw k hk).1
    omega
  obtain ⟨i1, i2, i3, i4, i5, i8, iR, i9, i10⟩ := loadBytes_uniG aq0 (ldPre ws aq0 false (srcsView ws (srcR rs1)))
    t ((ν (h, s.evs.length)).map bv8) ws ((X.ev (h, s.evs.length)).pa : Int)
  obtain ⟨j1, j2, j3, j4⟩ := i9 _ hvp
  rw [hinv.ldv] at j2
  -- the post-read state
  have hcohR : ∀ x : Int, coh (loadRun ws aq0 false (srcsView ws (srcR rs1)) ((X.ev (h, s.evs.length)).pa : Int)
      (uniTvs t ((ν (h, s.evs.length)).map bv8))) x = coh (loadBytes aq0 (ldPre ws aq0 false (srcsView ws (srcR rs1)))
        ws ((X.ev (h, s.evs.length)).pa : Int) (uniTvs t ((ν (h, s.evs.length)).map bv8))) x := fun _ => rfl
  generalize hws1 : loadBytes aq0 (ldPre ws aq0 false (srcsView ws (srcR rs1))) ws
    ((X.ev (h, s.evs.length)).pa : Int) (uniTvs t ((ν (h, s.evs.length)).map bv8)) = ws1
    at i1 i2 i3 i4 i5 i8 iR j1 j2 j3 j4 i10 hcohR
  have hlr : loadRun ws aq0 false (srcsView ws (srcR rs1)) ((X.ev (h, s.evs.length)).pa : Int)
      (uniTvs t ((ν (h, s.evs.length)).map bv8)) = { ws1 with wVcap := max (srcsView ws (srcR rs1)) ws1.wVcap } := by
    rw [← hws1]; rfl
  rw [hlr] at hcohR
  -- coh of the post-read state on the AMO's bytes is below ts
  have hcoh1 : ∀ k, k < sz → coh ws1 (((X.ev (h, s.evs.length)).pa : Int) + k) < ts := by
    intro k hk
    obtain ⟨_, htx⟩ := hbyte k hk
    have hold := hinv.coh1 _ s.evs.length (Nat.le_refl _) hml hst htx
    rw [hts] at hold
    push_cast at hold
    rcases i10 (((X.ev (h, s.evs.length)).pa : Int) + k) with e | ⟨k', hk', hxk, e⟩
    · rw [e]; exact hold
    · rw [e]
      rw [List.length_map, hlen] at hk'
      have hkk : k = k' := by omega
      subst hkk
      have := hfw k hk
      omega
  -- the premises of the rmw arm
  have hpr : ts ∈ prom := (hinv.prom ts).2 ⟨s.evs.length, Nat.le_refl _, hml, hst, hts⟩
  have hlog : (memOf X)[ts - 1]? = some ⟨((X.ev (h, s.evs.length)).pa : Int), (X.ev (h, s.evs.length)).wdat.map bv8,
      some h, .excl⟩ := by
    rw [← hts]; refine (memG_voG X X.gmo _ hwg hst).trans ?_; unfold msgOf; rw [hsk]; rfl
  have hdl : ((X.ev (h, s.evs.length)).wdat.map bv8).length = sz := by
    rw [List.length_map, HCtx.wdat_len' c.ref hid hst, hsk]
  have htl : (uniTvs t ((ν (h, s.evs.length)).map bv8)).length = ((X.ev (h, s.evs.length)).wdat.map bv8).length := by
    rw [hdl, uniTvs_length, List.length_map, hlen]
  have hexcl : exclOk (memOf X) h ((X.ev (h, s.evs.length)).pa : Int)
      ((uniTvs t ((ν (h, s.evs.length)).map bv8)).map Prod.fst) ts := by
    rw [uniTvs_fst, List.length_map, hlen]
    refine exclOk_rep _ _ _ _ _ _ (fun k hk hw => ?_)
    obtain ⟨e, htx⟩ := hbyte k hk
    rw [show ((X.ev (h, s.evs.length)).pa : Int) + (k : Int) = (((X.ev (h, s.evs.length)).pa + k : Nat) : Int) by
      push_cast; rfl] at hw
    obtain ⟨w', hw'g, hw's, hw'w, hlo, hhi, _⟩ := writesInBy_memOf c.ref hw
    have hgw : gB X.gmo w' (h, s.evs.length) = true :=
      gB_of_voG_le X X.gmo w' _ hw'g hw's hwg (by unfold vo at hhi hts; omega) (fun e => by rw [e] at hhi; omega)
    have := kts_ge c.ref hw'g hw'w (.inl hgw)
    rw [← e] at this
    omega
  have hcohb : cohBelow { ws1 with wVcap := max (srcsView ws (srcR rs1)) ws1.wVcap }
      ((X.ev (h, s.evs.length)).pa : Int) ((X.ev (h, s.evs.length)).wdat.map bv8).length ts := by
    rw [hdl]; exact cohBelow_of _ ts _ _ (fun k hk => hcoh1 k hk)
  have hstp : stPre { ws1 with wVcap := max (srcsView ws (srcR rs1)) ws1.wVcap } rl0 (srcsView ws (srcR rs1))
      (srcsView ws (srcR rs2)) < ts :=
    stPre_post_lt aq0 rl0 hwpre (by omega) i8 i5 i3 j1 j4
  have hmem := memStep.rmw0 (img := testImg T) (log := memOf X) (i := h) (memOf_noInval X) prom ws aq0 rl0   -- MachFix-R-b5
    ((X.ev (h, s.evs.length)).pa : Int) (uniTvs t ((ν (h, s.evs.length)).map bv8))
    ((X.ev (h, s.evs.length)).wdat.map bv8) (srcR rs1) (srcR rs2) ts htl hpr hlog hlok hexcl
    (by rw [hlr]; exact hcohb) (by rw [hlr]; exact hstp)
  rw [hlr, hdl] at hmem
  -- the program half
  have hdata : toBytes (amoOp op sz (ofBytes ((ν (h, s.evs.length)).map bv8)) (lp.rd rs2 % 2 ^ (8 * sz))) sz =
      (X.ev (h, s.evs.length)).wdat.map bv8 := by
    rw [hwdat]; exact amo_data hlen hbyt hsz8 op _ ν rfl e2 _ hev2
  have hlab : litNext lp (LRmw aq0 rl0 ((X.ev (h, s.evs.length)).pa : Int) (uniTvs t ((ν (h, s.evs.length)).map bv8))
      ((X.ev (h, s.evs.length)).wdat.map bv8) (srcR rs1) (srcR rs2)) = some { lp with
        regs := lp.wr rd (sext sz (ofBytes ((ν (h, s.evs.length)).map bv8))), pc := lp.pc + 1,
        q := regWL rd [.DLdRes] ++ [LInstr] } := by
    simp only [litNext, hinv.q, lpi_of hinv hi, instrNext]
    rw [halign, uniTvs_snd]
    simp [haddr, hdata, uniTvs_length, hlen]
  generalize hwsA : amoPost (storeRun { ws1 with wVcap := max (srcsView ws (srcR rs1)) ws1.wVcap } rl0
    (srcsView ws (srcR rs1)) ts ((X.ev (h, s.evs.length)).pa : Int) sz ts) aq0 ts = wsA at hmem
  have htail := solo_af (testImg T) (memOf X) h (regWL rd [.DLdRes] ++ [LInstr]) { lp with
      regs := lp.wr rd (sext sz (ofBytes ((ν (h, s.evs.length)).map bv8))), pc := lp.pc + 1,
      q := regWL rd [.DLdRes] ++ [LInstr] } wsA (prom \ {ts}) (regWL_af _ _) rfl
  rw [foldl_regWL] at htail
  refine ⟨_, _, _, _, .step _ _ (some ts) _ _ _ _ _ hlab hmem htail, ?_, ?_⟩
  · rw [machRow_rmw, machRow_af _ (regWL_af _ _), uniTvs_toNat _ _ hbyt, hn1, rowSeg_one, if_pos hrl', hrdat]
  -- the post-state
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12⟩ := amoPost_fields
    { ws1 with wVcap := max (srcsView ws (srcR rs1)) ws1.wVcap } rl0 (srcsView ws (srcR rs1))
    ((X.ev (h, s.evs.length)).pa : Int) sz ts aq0
  rw [hwsA] at a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8⟩ := regWE_fields wsA rd [.DLdRes]
  obtain ⟨kV, kR⟩ := keepRR_regWE wsA rd [.DLdRes]
  obtain ⟨hve, hvlt⟩ := ldVal_eq hlen hbyt hsz8 true (h, s.evs.length) ν rfl
  simp only [if_true] at hve
  have hrange : ∀ x : Nat, (((X.ev (h, s.evs.length)).pa : Int) ≤ (x : Int) ∧
      (x : Int) < ((X.ev (h, s.evs.length)).pa : Int) + (sz : Int)) ↔ touches (X.ev (h, s.evs.length)) x = true := by
    intro x; rw [touches_iff, hsz']; omega
  have hfutpo : ∀ j, s.evs.length + 1 ≤ j → j < sf.evs.length → poX X (h, s.evs.length) (h, j) = true := by
    intro j h1 h2
    have hjii := fut_ii hfut hii1 (by rw [hn1]; exact h1) h2
    exact c.po_of hm (List.getElem?_eq_getElem h2) (by simp only; omega)
  have hacq : aq0 = true → ∀ j, s.evs.length + 1 ≤ j → j < sf.evs.length →
      (X.sk (h, j)).kind.isMem = true → gB X.gmo (h, s.evs.length) (h, j) = true := by
    intro haq' j h1 h2 hjm
    exact gB_of_ppo c.ref c.io hid (fut_ev c h2).1 (ppo_r5 c.io hrm hjm (hfutpo j h1 h2) (by rw [hsk]; exact haq'))
  have hfvA := fvOk_rmw c hm rfl rfl hfut hn1 hii1
  rw [hts] at hfvA
  refine ⟨⟨hwf', hfut, by simp [hinv.prog], by simp [hinv.pc], rfl, by simp [LP.wr_len, hinv.lpLen], ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro r
    rw [SSt.adv_rd]
    exact regs_wr (s := s.emit _) hinv.lpLen hinv.wf.len (fun r => by rw [SSt.emit_rd]; exact hinv.regEq r) rd _ _
      hve r
  · intro r
    rw [SSt.adv_rd]
    exact regsLt_wr (s := s.emit _) (fun r => by rw [SSt.emit_rd]; exact hinv.regLt r) rd _ hvlt r
  · -- regv: the result register gets the AMO's own view (M0 (v))
    intro r h0 h32
    rw [SSt.adv_rd]
    have hregv' : ∀ r, 0 < r → r < 32 → domF (fun j => vo X (h, j))
        (· ∈ ((s.emit ⟨{ kind := .amo, ii := s.ii, sz := sz, aqSc := aq0, rlSc := rl0, adep := t1, ddep := t2, cdep := s.ctl }, e1, .amo op sz (.ld (h, s.evs.length) sz true) e2⟩).rd r).2) (regv wsA r) := by
      intro r h0 h32
      rw [SSt.emit_rd]
      have : regv wsA r = regv ws r := by unfold regv; rw [a7]; simp only; rw [i2]
      rw [this]; exact hinv.regv r h0 h32
    exact regv_wr hregv' hinv.wf.len rd _ _
      (by rw [srcsView_ld, a8]; exact domF_of _ _ (List.mem_singleton_self _) (by simp only; omega)) r h0 h32
  · -- vrOld: the AMO is a load
    show domF _ _ (instrE (regWE wsA rd [.DLdRes])).wVrOld
    rw [show (instrE (regWE wsA rd [.DLdRes])).wVrOld = wsA.wVrOld from f1, a1, hn1]
    simp only
    refine domF_le (domF_max (domF_mono hinv.vrOld (fun j hj => ⟨by omega, hj.2⟩))
      (domF_of _ s.evs.length ⟨by omega, hrl'⟩ (Nat.le_of_eq hts.symm))) ?_
    omega
  · -- vwOld: the AMO is a store
    show domF _ _ (instrE (regWE wsA rd [.DLdRes])).wVwOld
    rw [show (instrE (regWE wsA rd [.DLdRes])).wVwOld = wsA.wVwOld from f2, a2, hn1]
    simp only
    rw [i5]
    exact domF_max (domF_mono hinv.vwOld (fun j hj => ⟨by omega, hj.2⟩))
      (domF_of _ s.evs.length ⟨by omega, hst⟩ (Nat.le_of_eq hts.symm))
  · -- vrNew: rule 5
    intro j h1 h2 h3
    show (instrE (regWE wsA rd [.DLdRes])).wVrNew ≤ _ ∧ (_ → (instrE (regWE wsA rd [.DLdRes])).wVrNew < _)
    rw [show (instrE (regWE wsA rd [.DLdRes])).wVrNew = wsA.wVrNew from f3, a3]
    rw [hn1] at h1
    have hold := hinv.vrNew j (by omega) h2 h3
    simp only
    cases haq' : aq0
    · rw [haq'] at j3; simp only [Bool.false_eq_true, if_false] at j3 ⊢
      exact ⟨by omega, fun hs => by have := hold.2 hs; omega⟩
    · rw [haq'] at j3; simp only [if_true] at j3 ⊢
      have hg := vo_of_gB (hacq haq' j h1 h2 (Kind.isMem_of_isLoad _ h3))
      rw [hts] at hg
      exact ⟨by omega, fun hs => by have := hold.2 hs; have := hg.2 hs; omega⟩
  · -- vwNew: rule 5
    intro j h1 h2 h3
    show (instrE (regWE wsA rd [.DLdRes])).wVwNew < _
    rw [show (instrE (regWE wsA rd [.DLdRes])).wVwNew = wsA.wVwNew from f4, a4]
    rw [hn1] at h1
    have hold := hinv.vwNew j (by omega) h2 h3
    simp only
    cases haq' : aq0
    · rw [haq'] at j4; simp only [Bool.false_eq_true, if_false] at j4 ⊢; omega
    · rw [haq'] at j4; simp only [if_true] at j4 ⊢
      have := (vo_of_gB (hacq haq' j h1 h2 (Kind.isMem_of_isStore _ h3))).2 h3
      rw [hts] at this
      omega
  · -- vcap: rule 13 through the address
    intro j h1 h2 h3
    show (instrE (regWE wsA rd [.DLdRes])).wVcap < _
    rw [show (instrE (regWE wsA rd [.DLdRes])).wVcap = wsA.wVcap from f5, a5]
    simp only
    rw [i3]
    rw [hn1] at h1
    obtain ⟨hjid, _, _⟩ := fut_ev c h2
    have hpo2 := hfutpo j h1 h2
    have hold := hinv.vcap j (by omega) h2 h3
    have hva : srcsView ws (srcR rs1) < vo X (h, j) := by
      refine domF_lt (domF_srcR hinv.regv hrs1) (fun d hd => ?_) (by omega)
      rw [hr1] at hd
      obtain ⟨hdid, hdm, hpo1⟩ := pf_po c hinv.wf hinv.fut (hinv.wf.taint rs1 d (by rw [hr1]; exact hd))
        (Nat.le_refl _) hml
      exact vo_lt_of_gB (gB_of_ppo c.ref c.io hdid hjid
        (ppo_r13 hdm h3 hid hrm hpo1 hpo2 (by rw [hsk]; exact hd))) h3
    omega
  · -- coh1: rule 1
    intro x j h1 h2 h3 h4
    show coh (instrE (regWE wsA rd [.DLdRes])) x < _
    rw [show coh (instrE (regWE wsA rd [.DLdRes])) x = coh wsA x from f7 x, a11]
    rw [hn1] at h1
    split
    · rename_i hin
      have htx := (hrange x).1 hin
      obtain ⟨hjid, _, _⟩ := fut_ev c h2
      have hlt := vo_lt_of_gB (gB_of_ppo c.ref c.io hid hjid (ppo_r1 hrm h3 (hfutpo j h1 h2)
        (overlap_of_touch htx h4))) h3
      rw [hts] at hlt
      have hk : x - (X.ev (h, s.evs.length)).pa < sz := by rw [touches_iff, hsz'] at htx; omega
      have := hcoh1 _ hk
      rw [show ((X.ev (h, s.evs.length)).pa : Int) + ((x - (X.ev (h, s.evs.length)).pa : Nat) : Int) = (x : Int) by
        rw [touches_iff] at htx; push_cast; omega] at this
      show max (coh ws1 x) ts < _
      omega
    · show coh ws1 x < _
      have hold := hinv.coh1 x j (by omega) h2 h3 h4
      rcases i10 x with e | ⟨k, hk, hxk, e⟩
      · rw [e]; exact hold
      · exfalso
        rename_i hout
        rw [List.length_map, hlen] at hk
        exact hout ⟨by omega, by omega⟩
  · -- coh2
    intro x j h1 h2 h3 h4 w hw hww hle
    change vo X w ≤ coh (instrE (regWE wsA rd [.DLdRes])) x at hle
    rw [show coh (instrE (regWE wsA rd [.DLdRes])) x = coh wsA x from f7 x, a11] at hle
    rw [hn1] at h1
    split at hle
    · rename_i hin
      have htx := (hrange x).1 hin
      have hk : x - (X.ev (h, s.evs.length)).pa < sz := by rw [touches_iff, hsz'] at htx; omega
      have hc1 := hcoh1 _ hk
      rw [show ((X.ev (h, s.evs.length)).pa : Int) + ((x - (X.ev (h, s.evs.length)).pa : Nat) : Int) = (x : Int) by
        rw [touches_iff] at htx; push_cast; omega] at hc1
      have hwr : writesB (X.ev (h, s.evs.length)) x = true := by
        simp only [writesB, Bool.and_eq_true]; exact ⟨hst, htx⟩
      have := kts_ge c.ref hwg hwr (.inr (hfutpo j h1 h2))
      rw [hts] at this
      change vo X w ≤ max (coh ws1 x) ts at hle
      omega
    · change vo X w ≤ coh ws1 x at hle
      rcases i10 x with e | ⟨k, hk, hxk, e⟩
      · rw [e] at hle; exact hinv.coh2 x j (by omega) h2 h3 h4 w hw hww hle
      · exfalso
        rename_i hout
        rw [List.length_map, hlen] at hk
        exact hout ⟨by omega, by omega⟩
  · -- fwd: forward view = the AMO's own timestamp (M1, rule 3)
    intro x
    show fwdOk X h _ _ x (get? (instrE (regWE wsA rd [.DLdRes])).wFwd (x : Int))
    rw [show (instrE (regWE wsA rd [.DLdRes])).wFwd = wsA.wFwd from f6, a12, hn1]
    split
    · rename_i hin
      have htx := (hrange x).1 hin
      refine ⟨s.evs.length, by omega, hst, htx, fun j2 h1 h2 _ => by omega, hts.symm, ?_⟩
      intro j' h1 h2 h3 h4 hsrc
      exact hfvA j' (by omega) h2 h3 x h4 hsrc
    · rename_i hout
      show fwdOk X h _ _ x (get? ws1.wFwd (x : Int))
      rw [i1]
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
  · -- ExtraInv
    rw [hn1, show (instrE (regWE wsA rd [.DLdRes])).wVRel = wsA.wVRel from kV,
      show (instrE (regWE wsA rd [.DLdRes])).wRes = wsA.wRes from kR, a6, a10]
    simp only
    rw [i4, iR]
    refine ⟨?_, resOk_mono hx.res (by omega) (fun j h1 h2 => ?_)⟩
    · have hv0 : domF (fun j => vo X (h, j)) (fun j => j < s.evs.length + 1 ∧ (X.sk (h, j)).kind.isMem = true ∧
          (X.sk (h, j)).rlSc = true) ws.wVRel := domF_mono hx.vrel (fun j hj => ⟨by omega, hj.2⟩)
      cases hrl' : rl0
      · exact hv0
      · simp only [if_true]
        exact domF_max hv0 (domF_of _ s.evs.length ⟨by omega, hrm, by rw [hsk]; exact hrl'⟩
          (Nat.le_of_eq hts.symm))
    · have : j = s.evs.length := by omega
      subst this; rw [hsk]; rfl

end amo

end Weak.Prom.Cmp
