/-
Weak/Prom: **completeness S3b — `l{b,h,w,d}.aq[rl]` (Zalasr) and `lr`** (instances of `sim_loadG`).

* `sim_loadAq` — the Zalasr load-acquire (unpriv_zalasr.adoc:68–69 "The instruction always has an acquire-RCsc
  annotation, and if the bit rl is set the instruction has a release-RCsc annotation"): label
  `LLoad true rl …` (MachCert.lean `instrNext`), the reservation untouched.
* `sim_lr` — `lr{.aq}{.rl}` (rvwmo.adoc:124–128: aq gives acquire-RCsc, aq ∧ rl also release-RCsc): label
  `LExLoad aq (aq && rl) …`; the reservation (M16) is the LR itself: its base, its read timestamps and its read view
  (`readView_le`), with no LR/SC instruction after it.
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.CmpSimLA

namespace Weak.Prom.Cmp

open MachCSL MachCSL.Stdpp Iris.Std
open Weak (Image Dsrc)
open Weak.Prom Weak.Prom.Mach Weak.Prom.Mach.Cert
open Weak.Prom.Ref
open PLabel

variable {T : Test} {trs : List SSt} {ν : Val} {X : Exec} {h : Nat} {sf : SSt}

theorem loadRun_wRes (ws : PState) (aq rl : Bool) (va : Nat) (base : Int) (tvs : List (Nat × BitVec 8)) :
    (loadRun ws aq rl va base tvs).wRes = ws.wRes := (keepRR_loadBytes aq _ ws base tvs).2

theorem uniTvs_fst (t : Nat) : ∀ vs : List (BitVec 8), (uniTvs t vs).map Prod.fst = List.replicate vs.length t
  | [] => rfl
  | v :: vs => by simp only [uniTvs, List.map_cons, List.length_cons, List.replicate_succ] at *; rw [← uniTvs_fst t vs]; rfl

theorem machRow_exLoad (aq rl : Bool) (b : Int) (tvs : List (Nat × BitVec 8)) (asrc : List Dsrc) (o : Option Nat)
    (tl : PF.Trace) : machRow ((LExLoad aq rl b tvs asrc, o) :: tl) = tvs.map (fun tv => tv.2.toNat) :: machRow tl := by
  simp [machRow, PF.loadsOf, PF.loadLikeTvs]

section instrs

variable {s : SSt} {lp : LP} {ws : PState} {prom : GSet Nat}

/-- The address and alignment of an access `op (rs1)` without offset (Zalasr, LR, SC, AMO). -/
theorem addr_noOff (c : HCtx T trs ν X h sf) (hinv : SimInv T X ν h sf s lp ws prom) {rs1 : Nat} {e1 : Ex}
    {t1 : List Nat} (hr1 : s.rd rs1 = (e1, t1)) {sk : Skel} {wv : Ex} (hm : sf.evs[s.evs.length]? = some ⟨sk, e1, wv⟩)
    (hacc : sk.kind.isAcc = true) :
    lp.rd rs1 = (X.ev (h, s.evs.length)).pa ∧ Mach.aligned (lp.rd rs1) sk.sz = true := by
  have hev := c.ev hm
  have hev1 := hinv.regEq rs1
  rw [hr1] at hev1
  have hpa : (X.ev (h, s.evs.length)).pa = e1.eval ν := by rw [hev]; rfl
  have haddr : lp.rd rs1 = (X.ev (h, s.evs.length)).pa := by rw [hpa, hev1]
  refine ⟨haddr, ?_⟩
  have := List.all_eq_true.1 (c.condsSf).2 _ (List.mem_of_getElem? hm)
  simp only [hacc, Bool.not_true, Bool.false_or, beq_iff_eq] at this
  rw [haddr, hpa]
  simp [Mach.aligned, this]

/-- **`l{b,h,w,d}.aq[rl] rd, (rs1)`** (Zalasr). -/
theorem sim_loadAq (c : HCtx T trs ν X h sf) (hinv : SimInv T X ν h sf s lp ws prom)
    (hx : ExtraInv X h s.evs.length ws.wVRel ws.wRes) {sz : Nat} {rl0 : Bool} {rd rs1 : Nat}
    (hi : (T.prog h)[s.pc]? = some (.loadAq sz rl0 rd rs1)) (hok : instrS3b (.loadAq sz rl0 rd rs1) = true)
    {s' : SSt} (hs : stepI h (T.prog h).length s (.loadAq sz rl0 rd rs1) = .next s') (hfut : Future s' sf) :
    StepOkB T X ν h sf s lp ws prom s' := by
  have hwf' := (symWf_step h _ hinv.wf _).1 s' hs
  simp only [instrS3b, rOk, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨hsz, _⟩, hrs⟩ := hok
  obtain ⟨hsz0, hsz8⟩ := szOk_le hsz
  rcases hr1 : s.rd rs1 with ⟨e1, t1⟩
  simp only [stepI, hr1, Ref.StepR.next.injEq] at hs
  subst hs
  have hm : sf.evs[s.evs.length]? = some
      ⟨{ kind := .ld, ii := s.ii, sz := sz, aqSc := true, rlSc := rl0, adep := t1, cdep := s.ctl }, e1, .c 0⟩ :=
    prefix_get hfut.evs (by simp)
  obtain ⟨haddr, halign⟩ := addr_noOff c hinv hr1 hm rfl
  refine sim_loadG c hinv hx true rl0 hr1 hrs hsz0 hsz8 (.inl rfl) rfl rfl rfl (fun _ => rfl) (fun h' => h') rfl
    hwf' hfut (fun tvs => LLoad true rl0 ((X.ev (h, s.evs.length)).pa : Int) tvs (srcR rs1)) (fun _ => ws.wRes)
    ?_ ?_ (fun tvs tl => machRow_load _ _ _ _ _ _ _) ?_
  · intro tvs htl
    simp only [litNext, hinv.q, lpi_of hinv hi, instrNext]
    rw [halign]
    simp [haddr, htl]
  · intro tvs hl
    have e : ({ loadRun ws true rl0 (srcsView ws (srcR rs1)) ((X.ev (h, s.evs.length)).pa : Int) tvs with
        wRes := ws.wRes } : PState) = loadRun ws true rl0 (srcsView ws (srcR rs1)) ((X.ev (h, s.evs.length)).pa : Int)
          tvs := by
      rw [← loadRun_wRes ws true rl0 (srcsView ws (srcR rs1)) _ tvs]
    rw [e]
    exact .load _ _ _ _ _ _ _ hl
  · refine resOk_mono hx.res (by omega) (fun j h1 h2 => ?_)
    have : j = s.evs.length := by omega
    subst this; rw [c.sk hm]; rfl

/-- **`lr{.aq}{.rl} rd, (rs1)`** (Zalrsc). -/
theorem sim_lr (c : HCtx T trs ν X h sf) (hinv : SimInv T X ν h sf s lp ws prom)
    (hx : ExtraInv X h s.evs.length ws.wVRel ws.wRes) {sz : Nat} {aq0 rl0 : Bool} {rd rs1 : Nat}
    (hi : (T.prog h)[s.pc]? = some (.lr sz aq0 rl0 rd rs1)) (hok : instrS3b (.lr sz aq0 rl0 rd rs1) = true)
    {s' : SSt} (hs : stepI h (T.prog h).length s (.lr sz aq0 rl0 rd rs1) = .next s') (hfut : Future s' sf) :
    StepOkB T X ν h sf s lp ws prom s' := by
  have hwf' := (symWf_step h _ hinv.wf _).1 s' hs
  simp only [instrS3b, rOk, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨hsz, _⟩, hrs⟩ := hok
  obtain ⟨hsz0, hsz8⟩ := szOk_le hsz
  rcases hr1 : s.rd rs1 with ⟨e1, t1⟩
  simp only [stepI, hr1, Ref.StepR.next.injEq] at hs
  subst hs
  have hm : sf.evs[s.evs.length]? = some
      ⟨{ kind := .lr, ii := s.ii, sz := sz, aqSc := aq0, rlSc := (aq0 && rl0), adep := t1, cdep := s.ctl }, e1, .c 0⟩ :=
    prefix_get hfut.evs (by simp)
  obtain ⟨haddr, halign⟩ := addr_noOff c hinv hr1 hm rfl
  refine sim_loadG c hinv hx aq0 (aq0 && rl0) hr1 hrs hsz0 hsz8 (.inr rfl) rfl rfl rfl (fun h' => h') (fun h' => h')
    rfl hwf' hfut (fun tvs => LExLoad aq0 (aq0 && rl0) ((X.ev (h, s.evs.length)).pa : Int) tvs (srcR rs1))
    (fun tvs => some ⟨((X.ev (h, s.evs.length)).pa : Int), tvs.map Prod.fst, readView ws aq0 (aq0 && rl0)
      (srcsView ws (srcR rs1)) ((X.ev (h, s.evs.length)).pa : Int) tvs⟩)
    ?_ (fun tvs hl => .lr _ _ _ _ _ _ _ hl) (fun tvs tl => machRow_exLoad _ _ _ _ _ _ _) ?_
  · intro tvs htl
    simp only [litNext, hinv.q, lpi_of hinv hi, instrNext]
    rw [halign]
    simp [haddr, htl]
  · have hsk := c.sk hm
    have hid := c.id hm
    have hrl' : (X.sk (h, s.evs.length)).kind.isLoad = true := by rw [hsk]; rfl
    have hlen := c.rdat_len hid hrl'
    refine ⟨s.evs.length, by omega, by rw [hsk], fun j h1 h2 => by omega, rfl, ?_, ?_⟩
    · simp only
      rw [uniTvs_fst, List.length_map, hlen]
    · exact readView_le c hinv hx hrs hm rfl rfl (by rw [hr1]) aq0 (aq0 && rl0) (fun h' => h') (fun h' => h')
        _ (by rw [List.length_map, hlen, hsk])

end instrs

end Weak.Prom.Cmp
