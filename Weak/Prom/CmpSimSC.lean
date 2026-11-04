/-
Weak/Prom: **completeness S3b — the steps `s*.[aq]rl` (Zalasr), successful `sc`, failed `sc`** (see
Weak/Prom/CmpSimWB.lean's header).
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.CmpSimWB

namespace Weak.Prom.Cmp

open MachCSL MachCSL.Stdpp Iris.Std
open Weak (Image Dsrc)
open Weak.Prom Weak.Prom.Mach Weak.Prom.Mach.Cert
open Weak.Prom.Ref
open PLabel

variable {T : Test} {trs : List SSt} {ν : Val} {X : Exec} {h : Nat} {sf : SSt}

theorem machRow_exStore (aq rl : Bool) (b : Int) (d : List (BitVec 8)) (asrc vsrc : List Dsrc) (o : Option Nat)
    (tl : PF.Trace) : machRow ((LExStore aq rl b d asrc vsrc, o) :: tl) = machRow tl := by
  simp [machRow, PF.loadsOf, PF.loadLikeTvs]

theorem machRow_exFail (o : Option Nat) (tl : PF.Trace) : machRow ((LExFail, o) :: tl) = machRow tl := by
  simp [machRow, PF.loadsOf, PF.loadLikeTvs]

section instrs

variable {s : SSt} {lp : LP} {ws : PState} {prom : GSet Nat}

/-- **`s{b,h,w,d}.[aq]rl rs2, (rs1)`** (Zalasr store-release). -/
theorem sim_storeRl (c : HCtx T trs ν X h sf) (hinv : SimInv T X ν h sf s lp ws prom)
    (hx : ExtraInv X h s.evs.length ws.wVRel ws.wRes) {sz : Nat} {aq0 : Bool} {rs2 rs1 : Nat}
    (hi : (T.prog h)[s.pc]? = some (.storeRl sz aq0 rs2 rs1)) (hok : instrS3b (.storeRl sz aq0 rs2 rs1) = true)
    {s' : SSt} (hs : stepI h (T.prog h).length s (.storeRl sz aq0 rs2 rs1) = .next s') (hfut : Future s' sf) :
    StepOkB T X ν h sf s lp ws prom s' := by
  have hwf' := (symWf_step h _ hinv.wf _).1 s' hs
  simp only [instrS3b, rOk, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨hsz, hrs2⟩, hrs1⟩ := hok
  have hev2 := hinv.regEq rs2
  rcases hr1 : s.rd rs1 with ⟨e1, t1⟩
  rcases hr2 : s.rd rs2 with ⟨e2, t2⟩
  rw [hr2] at hev2
  simp only [stepI, hr1, hr2, Ref.StepR.next.injEq] at hs
  subst hs
  have hm : sf.evs[s.evs.length]? = some
      ⟨{ kind := .st, ii := s.ii, sz := sz, aqSc := aq0, rlSc := true, adep := t1, ddep := t2, cdep := s.ctl },
        e1, e2⟩ := prefix_get hfut.evs (by simp)
  have hml := (List.getElem?_eq_some_iff.1 hm).1
  have hid := c.id hm
  have hsk := c.sk hm
  have hev := c.ev hm
  have hst : (X.sk (h, s.evs.length)).kind.isStore = true := by rw [hsk]; rfl
  have hwm := Kind.isMem_of_isStore _ hst
  have hwg : (h, s.evs.length) ∈ X.gmo := (mem_gmo c.ref _).2 ⟨hid, hwm⟩
  have hwdat : (X.ev (h, s.evs.length)).wdat = byteList (e2.eval ν) sz := by rw [hev]; rfl
  obtain ⟨haddr, halign⟩ := addr_noOff c hinv hr1 hm rfl
  have hdata : toBytes (lp.rd rs2) sz = (X.ev (h, s.evs.length)).wdat.map bv8 := by rw [hwdat, hev2]; rfl
  have hn1 : (s.emit ⟨{ kind := .st, ii := s.ii, sz := sz, aqSc := aq0, rlSc := true, adep := t1, ddep := t2, cdep := s.ctl }, e1, e2⟩).adv.evs.length = s.evs.length + 1 := by simp
  have hii1 : (s.emit ⟨{ kind := .st, ii := s.ii, sz := sz, aqSc := aq0, rlSc := true, adep := t1, ddep := t2, cdep := s.ctl }, e1, e2⟩).adv.ii = s.ii + 1 := by simp
  obtain ⟨hcohb, hpre, hmo, hvrel⟩ := mem_storeG c hinv hx hrs1 hrs2 hm rfl rfl (by rw [hr1]) (by rw [hr2]) aq0 true
    (fun h' => h') (fun _ => rfl) _ (fvOk_deps c hinv hrs1 hrs2 hm rfl rfl (by rw [hr1]) (by rw [hr2]) hfut hn1 hii1)
    hfut hn1 hii1
  dsimp only at hcohb hmo hvrel
  generalize hts : vo X (h, s.evs.length) = ts at hcohb hpre hmo hvrel
  have hpr : ts ∈ prom := (hinv.prom ts).2 ⟨s.evs.length, Nat.le_refl _, hml, hst, hts⟩
  have hlog : (memOf X)[ts - 1]? = some ⟨((X.ev (h, s.evs.length)).pa : Int), (X.ev (h, s.evs.length)).wdat.map bv8,
      some h, stClass true⟩ := by
    rw [← hts]; refine (memG_voG X X.gmo _ hwg hst).trans ?_; unfold msgOf; rw [hsk]; rfl
  have hdl : ((X.ev (h, s.evs.length)).wdat.map bv8).length = sz := by
    rw [List.length_map, HCtx.wdat_len' c.ref hid hst, hsk]
  have hmem := memStep.store (img := testImg T) (log := memOf X) (i := h) prom ws aq0 true
    ((X.ev (h, s.evs.length)).pa : Int) ((X.ev (h, s.evs.length)).wdat.map bv8) (srcR rs1) (srcR rs2) ts hpr hlog
    (by rw [hdl]; exact hcohb) hpre
  rw [hdl] at hmem
  have hlab : litNext lp (LStore aq0 true ((X.ev (h, s.evs.length)).pa : Int) ((X.ev (h, s.evs.length)).wdat.map bv8)
      (srcR rs1) (srcR rs2)) = some { lp with pc := lp.pc + 1, q := [LInstr] } := by
    simp only [litNext, hinv.q, lpi_of hinv hi, instrNext]
    rw [halign]
    simp [haddr, hdata]
  generalize hws2 : acqPost (storeRun ws true (srcsView ws (srcR rs1))
    (max (srcsView ws (srcR rs1)) (srcsView ws (srcR rs2))) ((X.ev (h, s.evs.length)).pa : Int) sz ts) aq0 ts = ws2
    at hmo hvrel hmem
  have htail := solo_af (testImg T) (memOf X) h [LInstr] { lp with pc := lp.pc + 1, q := [LInstr] }
    ws2 (prom \ {ts}) (by simp [afOk]) rfl
  refine ⟨_, _, _, _, .step _ _ (some ts) _ _ _ _ _ hlab hmem htail, ?_, ?_⟩
  · rw [machRow_store, machRow_af _ (by simp [afOk]), hn1, rowSeg_one, hsk]; rfl
  obtain ⟨_, _, _, _, _, _, f7, f8, f9, f10, _, _⟩ := storeRun_fields ws true (srcsView ws (srcR rs1))
    (max (srcsView ws (srcR rs1)) (srcsView ws (srcR rs2))) ((X.ev (h, s.evs.length)).pa : Int) sz ts aq0
  rw [hws2] at f7 f10
  refine ⟨simInv_mk hwf' hfut (by simp [hinv.prog]) (by simp [hinv.pc]) rfl hinv.lpLen (fun r => hinv.regEq r)
    (fun r => hinv.regLt r) (fun r h0 h32 => ?_) ?_ (by show (instrE _).wLdv = 0; rfl)
    (by show (instrE _).wIfv = 0; rfl), ?_⟩
  · have : regv ([LInstr].foldl afEff ws2) r = regv ws r := by
      unfold regv; show (get? ws2.wRegv r).getD 0 = _; rw [f7]
    rw [this]; exact hinv.regv r h0 h32
  · rw [hn1]; exact memOk_congr hmo rfl rfl rfl rfl rfl (fun _ => rfl) rfl
  · rw [hn1]
    refine ⟨hvrel, ?_⟩
    show resOk X h _ ws2.wRes
    rw [f10]
    refine resOk_mono hx.res (by omega) (fun j h1 h2 => ?_)
    have : j = s.evs.length := by omega
    subst this; rw [hsk]; rfl

/-- THE RESERVATION OF A SUCCESSFUL SC IS ITS PAIRED LR (`ExtraInv.res` + pairing, rvwmo.adoc:114–116). -/
theorem pair_resv (c : HCtx T trs ν X h sf) (hinv : SimInv T X ν h sf s lp ws prom)
    (hx : ExtraInv X h s.evs.length ws.wVRel ws.wRes) {se : SEv} (hm : sf.evs[s.evs.length]? = some se)
    (hii : se.sk.ii = s.ii) {jr : Nat} (hjr : jr < s.evs.length)
    (hpair : pairedS X.ids X.sk (h, jr) (h, s.evs.length) = true) :
    ∃ R, ws.wRes = some R ∧ R.rvBase = ((X.ev (h, jr)).pa : Int) ∧
      R.rvTs = List.replicate (X.sk (h, jr)).sz (kts X (rfSrc X (h, jr) (X.ev (h, jr)).pa)) ∧
      R.rvView ≤ vo X (h, jr) := by
  have hlr : (X.sk (h, jr)).kind = .lr := by
    simp only [pairedS, Bool.and_eq_true, beq_iff_eq] at hpair; exact hpair.1.1.1
  have hall := hpair
  simp only [pairedS, Bool.and_eq_true, List.all_eq_true] at hall
  have hnone := hall.2
  -- no LR/SC instruction strictly between the LR and the SC
  have hbetw : ∀ j, jr < j → j < s.evs.length → (X.sk (h, j)).kind.isLrSc = false := by
    intro j h1 h2
    have hjrs : s.evs[jr]? = some s.evs[jr] := List.getElem?_eq_getElem (by omega)
    have hjs : s.evs[j]? = some s.evs[j] := List.getElem?_eq_getElem h2
    have hmono := hinv.wf.iiMono jr j _ _ h1 hjrs hjs
    have e1 := c.sk (prefix_get hinv.fut.evs hjrs)
    have e2 := c.sk (prefix_get hinv.fut.evs hjs)
    have hmem : s.evs[jr].sk.kind.isMem = true := by rw [← e1, hlr]; rfl
    have hp1 : poX X (h, jr) (h, j) = true := by
      rw [c.po (prefix_get hinv.fut.evs hjrs) (prefix_get hinv.fut.evs hjs)]; simpa using hmono.2 hmem
    obtain ⟨hjid, hp2⟩ := past_po c hinv hm hii h2
    have := hnone (h, j) hjid
    simp only [Bool.not_eq_true', Bool.and_eq_false_iff] at this
    simp only [poX] at hp1 hp2
    rcases this with (h3 | h3) | h3
    · rw [hp1] at h3; cases h3
    · rw [hp2] at h3; cases h3
    · exact h3
  have hres := hx.res
  revert hres
  cases hR : ws.wRes with
  | none =>
    intro hres
    obtain ⟨j, h1, h2, h3⟩ := hres jr hjr hlr
    rw [hbetw j h1 h2] at h3; cases h3
  | some R =>
    rintro ⟨jr', h1, h2, h3, h4, h5, h6⟩
    rcases Nat.lt_trichotomy jr' jr with hlt | heq | hgt
    · have := h3 jr hlt hjr; rw [hlr] at this; cases this
    · subst heq; exact ⟨R, rfl, h4, h5, h6⟩
    · have := hbetw jr' hgt h1; rw [h2] at this; cases this

/-- **A SUCCESSFUL `sc{.aq}{.rl} rd, rs2, (rs1)`** (Zalrsc, the `true` arm of the reference's fork). -/
theorem sim_scOk (c : HCtx T trs ν X h sf) (hinv : SimInv T X ν h sf s lp ws prom)
    (hx : ExtraInv X h s.evs.length ws.wVRel ws.wRes) {sz : Nat} {aq0 rl0 : Bool} {rd rs2 rs1 : Nat}
    (hi : (T.prog h)[s.pc]? = some (.sc sz aq0 rl0 rd rs2 rs1)) (hok : instrS3b (.sc sz aq0 rl0 rd rs2 rs1) = true)
    {t f : SSt} (hs : stepI h (T.prog h).length s (.sc sz aq0 rl0 rd rs2 rs1) = .fork t f) (hfut : Future t sf) :
    StepOkB T X ν h sf s lp ws prom t := by
  have hwf' := ((symWf_step h _ hinv.wf _).2 t f hs).1
  simp only [instrS3b, rOk, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨hsz, hrd⟩, hrs2⟩, hrs1⟩ := hok
  have hev2 := hinv.regEq rs2
  rcases hr1 : s.rd rs1 with ⟨e1, t1⟩
  rcases hr2 : s.rd rs2 with ⟨e2, t2⟩
  rw [hr2] at hev2
  simp only [stepI, hr1, hr2, Ref.StepR.fork.injEq] at hs
  obtain ⟨rfl, rfl⟩ := hs
  have hm : sf.evs[s.evs.length]? = some
      ⟨{ kind := .sc, ii := s.ii, sz := sz, aqSc := (aq0 && rl0), rlSc := rl0, adep := t1, ddep := t2, cdep := s.ctl }, e1, e2⟩ := prefix_get hfut.evs (by simp)
  have hml := (List.getElem?_eq_some_iff.1 hm).1
  have hid := c.id hm
  have hsk := c.sk hm
  have hev := c.ev hm
  have hst : (X.sk (h, s.evs.length)).kind.isStore = true := by rw [hsk]; rfl
  have hwm := Kind.isMem_of_isStore _ hst
  have hwg : (h, s.evs.length) ∈ X.gmo := (mem_gmo c.ref _).2 ⟨hid, hwm⟩
  have hwdat : (X.ev (h, s.evs.length)).wdat = byteList (e2.eval ν) sz := by rw [hev]; rfl
  obtain ⟨haddr, halign⟩ := addr_noOff c hinv hr1 hm rfl
  have hdata : toBytes (lp.rd rs2) sz = (X.ev (h, s.evs.length)).wdat.map bv8 := by rw [hwdat, hev2]; rfl
  have hn1 : (((s.emit ⟨{ kind := .sc, ii := s.ii, sz := sz, aqSc := (aq0 && rl0), rlSc := rl0, adep := t1, ddep := t2, cdep := s.ctl }, e1, e2⟩).wr rd (.c 0, [s.evs.length])).adv).evs.length = s.evs.length + 1 := by
    simp
  have hii1 : (((s.emit ⟨{ kind := .sc, ii := s.ii, sz := sz, aqSc := (aq0 && rl0), rlSc := rl0, adep := t1, ddep := t2, cdep := s.ctl }, e1, e2⟩).wr rd (.c 0, [s.evs.length])).adv).ii = s.ii + 1 := by simp
  obtain ⟨hcohb, hpre, hmo, hvrel⟩ := mem_storeG c hinv hx hrs1 hrs2 hm rfl rfl (by rw [hr1]) (by rw [hr2])
    (aq0 && rl0) rl0 (fun h' => h') (fun h' => h') _ (fvOk_rmw c hm rfl rfl hfut hn1 hii1) hfut hn1 hii1
  dsimp only at hcohb hmo hvrel
  -- the paired LR and the reservation
  obtain ⟨r, hr, hpair, hresv⟩ := scAx_of c.ref hid (by rw [hsk])
  have hpo_r : poX X r (h, s.evs.length) = true := by
    simp only [pairedS, Bool.and_eq_true] at hpair; exact hpair.1.2
  obtain ⟨hrh, hjr⟩ := idx_lt_of_po c hinv hr hm rfl hpo_r
  obtain ⟨r1, jr⟩ := r
  simp only at hrh hjr; subst hrh
  obtain ⟨R, hR, hRb, hRts, hRv⟩ := pair_resv c hinv hx hm rfl hjr hpair
  have hlr : (X.sk (r1, jr)).kind = .lr := by
    simp only [pairedS, Bool.and_eq_true, beq_iff_eq] at hpair; exact hpair.1.1.1
  have hjre : sf.evs[jr]? = some sf.evs[jr] := List.getElem?_eq_getElem (by
    have := hinv.fut.evs.length_le; omega)
  have hrm : (X.sk (r1, jr)).kind.isMem = true := by rw [hlr]; rfl
  have hrg : (r1, jr) ∈ X.gmo := (mem_gmo c.ref _).2 ⟨hr, hrm⟩
  have halr : Ref.aligned (X.ev (r1, jr)) = true :=
    c.alignedEv hjre (by rw [← c.sk hjre, hlr]; rfl)
  have halw : Ref.aligned (X.ev (r1, s.evs.length)) = true := c.alignedEv hm rfl
  generalize hts : vo X (r1, s.evs.length) = ts at hcohb hpre hmo hvrel
  have hts1 : 1 ≤ ts := by rw [← hts]; exact voG_st_pos X X.gmo _ hwg hst
  -- the premises of the SC arm
  have hpr : ts ∈ prom := (hinv.prom ts).2 ⟨s.evs.length, Nat.le_refl _, hml, hst, hts⟩
  have hlog : (memOf X)[ts - 1]? = some ⟨((X.ev (r1, s.evs.length)).pa : Int),
      (X.ev (r1, s.evs.length)).wdat.map bv8, some r1, .excl⟩ := by
    rw [← hts]; refine (memG_voG X X.gmo _ hwg hst).trans ?_; unfold msgOf; rw [hsk]; rfl
  have hdl : ((X.ev (r1, s.evs.length)).wdat.map bv8).length = sz := by
    rw [List.length_map, HCtx.wdat_len' c.ref hid hst, hsk]
  have hrsz : (X.ev (r1, jr)).sk.sz = (X.sk (r1, jr)).sz := rfl
  have hexcl : exclOk (memOf X) r1 R.rvBase R.rvTs ts := by
    rw [hRb, hRts]
    refine exclOk_rep _ _ _ _ _ _ (fun k hk hw => ?_)
    rw [show ((X.ev (r1, jr)).pa : Int) + (k : Int) = (((X.ev (r1, jr)).pa + k : Nat) : Int) by push_cast; rfl] at hw
    obtain ⟨w', hw'g, hw's, hw'w, hlo, hhi, hq⟩ := writesInBy_memOf c.ref hw
    have hw'i := ids_of_gmo hw'g c.ref
    have hne : w'.1 ≠ r1 := fun e => hq (by rw [e])
    have htp : touches (X.ev (r1, jr)) (X.ev (r1, jr)).pa = true := by rw [touches_iff, hrsz]; omega
    have htx : touches (X.ev (r1, jr)) ((X.ev (r1, jr)).pa + k) = true := by rw [touches_iff, hrsz]; omega
    rw [rfSrc_bytes c.ref c.ss hr hrm htp htx] at hlo
    have hgw : gB X.gmo w' (r1, s.evs.length) = true :=
      gB_of_voG_le X X.gmo w' _ hw'g hw's hwg (by unfold vo at hhi hts; omega)
        (fun e => by rw [e] at hhi; omega)
    cases hs0 : rfSrc X (r1, jr) ((X.ev (r1, jr)).pa + k) with
    | some s0 =>
      rw [hs0] at hlo
      simp only [kts] at hlo
      obtain ⟨hs0g, hs0w, _⟩ := rfSrc_spec hs0
      obtain ⟨_, hno⟩ := atomAx c.ref hr hid hpair halr halw hk hs0
      have hg0 : gB X.gmo s0 w' = true :=
        gB_of_voG_le X X.gmo s0 w' hs0g (writesB_store hs0w) hw'g (by unfold vo at hlo; omega)
          (fun e => by rw [e] at hlo; omega)
      exact hno w' hw'i hw'w hne ⟨hg0, hgw⟩
    | none =>
      obtain ⟨R', hR1, _, hR3⟩ := hresv
      have hgr : gB X.gmo (r1, jr) w' = true := by
        rcases gB_total X.gmo (r1, jr) w' hrg hw'g with e | e | e
        · rw [← e] at hw's; simp only [isSt] at hw's; rw [hlr] at hw's; cases hw's
        · exact e
        · obtain ⟨s1, hs1, _⟩ := rfSrc_max c.ref hw'g hw'w (.inl e)
          rw [hs0] at hs1; cases hs1
      exact hR3 w' hw'i hw's hne ⟨_, hR1 _ htx, hw'w⟩ ⟨hgr, hgw⟩
  have hlt : ∀ t ∈ R.rvTs, t < ts := by
    intro t ht
    rw [hRts] at ht
    obtain ⟨hpos, rfl⟩ : 0 < (X.sk (r1, jr)).sz ∧ t = kts X (rfSrc X (r1, jr) (X.ev (r1, jr)).pa) := by
      refine ⟨?_, List.eq_of_mem_replicate ht⟩
      rcases Nat.eq_zero_or_pos (X.sk (r1, jr)).sz with e | e
      · rw [e] at ht; simp at ht
      · exact e
    cases hs0 : rfSrc X (r1, jr) (X.ev (r1, jr)).pa with
    | none => simp only [kts]; omega
    | some s0 =>
      simp only [kts]
      have hs0' : rfSrc X (r1, jr) ((X.ev (r1, jr)).pa + 0) = some s0 := by rw [Nat.add_zero]; exact hs0
      obtain ⟨hg, _⟩ := atomAx c.ref hr hid hpair halr halw hpos hs0'
      have := vo_lt_of_gB hg hst
      rw [hts] at this; exact this
  have hrv : R.rvView < ts := by
    have := vo_lt_of_gB (gB_of_ppo c.ref c.io hr hid (ppo_r8 hrm hwm hpair)) hst
    rw [hts] at this; omega
  have hmem := memStep.sc (img := testImg T) (log := memOf X) (i := r1) prom ws (aq0 && rl0) rl0
    ((X.ev (r1, s.evs.length)).pa : Int) ((X.ev (r1, s.evs.length)).wdat.map bv8) (srcR rs1) (srcR rs2) ts R hR hpr
    hlog hexcl hlt (by rw [hdl]; exact hcohb) (by omega)
  rw [hdl] at hmem
  have hlab : litNext lp (LExStore (aq0 && rl0) rl0 ((X.ev (r1, s.evs.length)).pa : Int)
      ((X.ev (r1, s.evs.length)).wdat.map bv8) (srcR rs1) (srcR rs2)) =
      some { lp with regs := lp.wr rd 0, pc := lp.pc + 1, q := regWL rd [.DLdRes] ++ [LExFail, LInstr] } := by
    simp only [litNext, hinv.q, lpi_of hinv hi, instrNext]
    rw [halign]
    simp [haddr, hdata]
  generalize hws2 : acqPost (storeRun ws rl0 (srcsView ws (srcR rs1)) ts ((X.ev (r1, s.evs.length)).pa : Int) sz ts)
    (aq0 && rl0) ts = ws2 at hmo hvrel hmem
  obtain ⟨_, _, _, _, _, _, f7, f8, f9, f10, _, _⟩ := storeRun_fields ws rl0 (srcsView ws (srcR rs1)) ts
    ((X.ev (r1, s.evs.length)).pa : Int) sz ts (aq0 && rl0)
  rw [hws2] at f7 f8
  have hld2 : (storeRun ws rl0 (srcsView ws (srcR rs1)) ts ((X.ev (r1, s.evs.length)).pa : Int) sz ts).wLdv = 0 := by
    rw [← hinv.ldv, ← f8, ← hws2]; rfl
  rw [hld2] at hmem
  have htail := solo_scTail (testImg T) (memOf X) r1
    { lp with regs := lp.wr rd 0, pc := lp.pc + 1, q := regWL rd [.DLdRes] ++ [LExFail, LInstr] }
    { ws2 with wLdv := max 0 ts, wRes := none } (prom \ {ts}) rd [.DLdRes] rfl
  refine ⟨_, _, _, _, .step _ _ (some ts) _ _ _ _ _ hlab hmem htail, ?_, ?_⟩
  · rw [machRow_exStore, machRow_scTail, hn1, rowSeg_one, hsk]; rfl
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12⟩ :=
    regWE_sc_fields { ws2 with wLdv := max 0 ts, wRes := none } rd [.DLdRes]
  refine ⟨simInv_mk hwf' hfut (by simp [hinv.prog]) (by simp [hinv.pc]) rfl (by simp [LP.wr_len, hinv.lpLen])
    ?_ ?_ ?_ ?_ g10 g11, ?_⟩
  · intro r
    rw [SSt.adv_rd]
    exact regs_wr (s := s.emit _) hinv.lpLen hinv.wf.len (fun r => by rw [SSt.emit_rd]; exact hinv.regEq r) rd 0 _
      rfl r
  · intro r
    rw [SSt.adv_rd]
    exact regsLt_wr (s := s.emit _) (fun r => by rw [SSt.emit_rd]; exact hinv.regLt r) rd _ (eval_c_lt 0 ν) r
  · intro r h0 h32
    rw [SSt.adv_rd, g12]
    have hregv' : ∀ r, 0 < r → r < 32 → domF (fun j => vo X (r1, j))
        (· ∈ ((s.emit ⟨{ kind := .sc, ii := s.ii, sz := sz, aqSc := (aq0 && rl0), rlSc := rl0, adep := t1, ddep := t2, cdep := s.ctl }, e1, e2⟩).rd r).2) (regv { ws2 with wLdv := max 0 ts, wRes := none } r) := by
      intro r h0 h32
      rw [SSt.emit_rd]
      have : regv { ws2 with wLdv := max 0 ts, wRes := none } r = regv ws r := by
        unfold regv; show (get? ws2.wRegv r).getD 0 = _; rw [f7]
      rw [this]; exact hinv.regv r h0 h32
    exact regv_wr hregv' hinv.wf.len rd _ _ (by
      rw [srcsView_ld]; exact domF_of _ s.evs.length (List.mem_singleton_self _) (by show max 0 ts ≤ _; omega))
      r h0 h32
  · rw [hn1]
    exact memOk_congr hmo g1 g2 g3 g4 g5 g6 g7
  · rw [hn1]
    refine ⟨by rw [g8]; exact hvrel, ?_⟩
    rw [g9]
    exact resOk_afterSc (by rw [hsk]; rfl) (by rw [hsk]; simp)

/-- **A FAILED `sc`** (the `false` arm of the reference's fork): `LExFail`, no store, the reservation cleared. -/
theorem sim_scFail (c : HCtx T trs ν X h sf) (hinv : SimInv T X ν h sf s lp ws prom)
    (hx : ExtraInv X h s.evs.length ws.wVRel ws.wRes) {sz : Nat} {aq0 rl0 : Bool} {rd rs2 rs1 : Nat}
    (hi : (T.prog h)[s.pc]? = some (.sc sz aq0 rl0 rd rs2 rs1)) (hok : instrS3b (.sc sz aq0 rl0 rd rs2 rs1) = true)
    {t f : SSt} (hs : stepI h (T.prog h).length s (.sc sz aq0 rl0 rd rs2 rs1) = .fork t f) (hfut : Future f sf) :
    StepOkB T X ν h sf s lp ws prom f := by
  have hwf' := ((symWf_step h _ hinv.wf _).2 t f hs).2
  rcases hr1 : s.rd rs1 with ⟨e1, t1⟩
  rcases hr2 : s.rd rs2 with ⟨e2, t2⟩
  simp only [stepI, hr1, hr2, Ref.StepR.fork.injEq] at hs
  obtain ⟨rfl, rfl⟩ := hs
  have hm : sf.evs[s.evs.length]? = some
      ⟨{ kind := .scFail, ii := s.ii, sz := sz, adep := t1, ddep := t2, cdep := s.ctl }, e1, .c 0⟩ :=
    prefix_get hfut.evs (by simp)
  have hsk := c.sk hm
  obtain ⟨haddr, halign⟩ := addr_noOff c hinv hr1 hm rfl
  have hlab : litNext lp LExFail =
      some { lp with regs := lp.wr rd 1, pc := lp.pc + 1, q := regWL rd [] ++ [LExFail, LInstr] } := by
    simp only [litNext, hinv.q, lpi_of hinv hi, instrNext]
    rw [halign]
    simp
  have htail := solo_scTail (testImg T) (memOf X) h
    { lp with regs := lp.wr rd 1, pc := lp.pc + 1, q := regWL rd [] ++ [LExFail, LInstr] }
    { ws with wRes := none } prom rd [] rfl
  have hn1 : ((s.emit ⟨{ kind := .scFail, ii := s.ii, sz := sz, adep := t1, ddep := t2, cdep := s.ctl }, e1,
      .c 0⟩).wr rd (.c 1, (s.rd rd).2)).adv.evs.length = s.evs.length + 1 := by simp
  refine ⟨_, _, _, _, .step _ _ none _ _ _ _ _ hlab (.scFail _ _) htail, ?_, ?_⟩
  · rw [machRow_exFail, machRow_scTail, hn1, rowSeg_one, hsk]; rfl
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12⟩ := regWE_sc_fields { ws with wRes := none } rd []
  have hnm : ∀ j, s.evs.length ≤ j → j < s.evs.length + 1 → (X.sk (h, j)).kind.isMem = false := by
    intro j h1 h2
    have : j = s.evs.length := by omega
    subst this; rw [hsk]; rfl
  refine ⟨inv_nomem hinv hwf' hfut (by rw [hn1]; omega) (by rw [hn1]; exact hnm) (by simp [hinv.prog])
    (by simp [hinv.pc]) rfl (by simp [LP.wr_len, hinv.lpLen]) ?_ ?_ ?_ g1 g2 ?_ ?_ ?_ g6 g7 g10 g11, ?_⟩
  · intro r
    rw [SSt.adv_rd]
    exact regs_wr (s := s.emit _) hinv.lpLen hinv.wf.len (fun r => by rw [SSt.emit_rd]; exact hinv.regEq r) rd 1 _
      rfl r
  · intro r
    rw [SSt.adv_rd]
    exact regsLt_wr (s := s.emit _) (fun r => by rw [SSt.emit_rd]; exact hinv.regLt r) rd _ (eval_c_lt 1 ν) r
  · intro r h0 h32
    rw [SSt.adv_rd, g12]
    have hregv' : ∀ r, 0 < r → r < 32 → domF (fun j => vo X (h, j))
        (· ∈ ((s.emit ⟨{ kind := .scFail, ii := s.ii, sz := sz, adep := t1, ddep := t2, cdep := s.ctl }, e1,
          .c 0⟩).rd r).2) (regv { ws with wRes := none } r) := by
      intro r h0 h32
      rw [SSt.emit_rd]; exact hinv.regv r h0 h32
    exact regv_wr hregv' hinv.wf.len rd _ _ (by rw [srcsView_nil]; exact domF_zero _ _) r h0 h32
  · intro j h1 h2 h3; rw [g3]; exact hinv.vrNew j (by rw [hn1] at h1; omega) h2 h3
  · intro j h1 h2 h3; rw [g4]; exact hinv.vwNew j (by rw [hn1] at h1; omega) h2 h3
  · intro j h1 h2 h3; rw [g5]; exact hinv.vcap j (by rw [hn1] at h1; omega) h2 h3
  · rw [hn1, g8, g9]
    exact ⟨domF_mono hx.vrel (fun j hj => ⟨by omega, hj.2⟩), resOk_afterSc (by rw [hsk]; rfl) (by rw [hsk]; simp)⟩

end instrs

end Weak.Prom.Cmp
