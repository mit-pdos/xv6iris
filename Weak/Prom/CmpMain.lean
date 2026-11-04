/-
Weak/Prom: **completeness S3a — `rvwmo_complete`** (plan rev 7 §0 "(T-cmp)", promises-first form; §6; §8 S3a).
See Weak/Prom/CmpRun.lean's header for the statement in words; the proof assembles `promsRun` (the promise phase,
MachFactor.lean), `sim_hart` (each hart's path, CmpSim.lean) and `statePhase` (hart after hart, CmpRun.lean).

* `rvwmo_complete` — the theorem, over a reference execution given by its paths `trs`;
* `rvwmo_complete_exec` — the same from RefProg.lean's `progExec T chs ν g` (the form `forbiddenRef` uses);
* `obsLoad_eq` — the machine run's `obsLoad` (the outcome vocabulary of the logic's `lit_` theorems) is the
  reference's `refObsLoad`; `finalMem_eq` — its final memory is the reference's.
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.CmpRun

namespace Weak.Prom.Cmp

open MachCSL MachCSL.Stdpp Iris.Std
open Weak (Image Dsrc)
open Weak.Prom Weak.Prom.Mach Weak.Prom.Mach.Cert
open Weak.Prom.Ref
open PLabel

/-! ## 1. Final memory -/

theorem filter_memOf {X : Exec} (hX : rvwmoRef X) (x : Nat) :
    (memOf X).filter (fun m => (m.byteAt (x : Int)).isSome) = (X.gmo.filter (fun w => writesB (X.ev w) x)).map (msgOf X) := by
  unfold memOf memG
  rw [List.filter_map, List.filter_filter]
  congr 1
  apply List.filter_congr
  intro w hw
  simp only [Function.comp]
  cases hs : isSt X w
  · simp only [Bool.and_false, writesB]
    have : (X.ev w).sk.kind.isStore = false := hs
    rw [this]; rfl
  · rw [msgOf_byteAt hX ((mem_gmo hX w).1 hw).1 hs]
    simp only [Bool.and_true, writesB]
    have : (X.ev w).sk.kind.isStore = true := hs
    rw [this, Bool.true_and]
    cases touches (X.ev w) x <;> rfl

/-- The machine's final memory is the reference's (MachLitmus.lean `finalMem`, Ref.lean `finalByte`). -/
theorem finalMem_eq {T : Test} (hT : progS3aB T = true) {X : Exec} (hX : rvwmoRef X) (himg : X.img = T.imgF)
    (hw : ∀ e, ∀ b ∈ (X.ev e).wdat, b < 256) (a n : Nat) :
    finalMem (testImg T) (memOf X) a n = refFinalMem X a n := by
  unfold finalMem refFinalMem
  congr 1
  apply List.map_congr_left
  intro k _
  simp only
  rw [show (a : Int) + (k : Int) = ((a + k : Nat) : Int) by push_cast; rfl, filter_memOf hX, List.getLast?_map]
  unfold finalByte
  cases hl : (X.gmo.filter (fun w => writesB (X.ev w) (a + k))).getLast? with
  | none =>
    simp only [Option.map_none, testImg, Int.toNat_natCast, Option.map_some, Option.getD_some, himg]
    exact bv8_toNat _ (imgF_lt T hT _)
  | some w =>
    obtain ⟨hwg, hww⟩ := getLast?_filter_mem _ _ _ hl
    simp only [Option.map_some]
    rw [msgOf_byteAt hX ((mem_gmo hX w).1 hwg).1 (writesB_store hww), if_pos (writesB_touches hww)]
    simp only [Option.map_some, Option.getD_some]
    exact bv8_toNat _ (wbyte_lt hw _ _)

/-! ## 2. Observations -/

theorem obsOf_eq (tvs : List (Nat × BitVec 8)) : PF.obsOf tvs = bytesVal (tvs.map (fun tv => tv.2.toNat)) := by
  induction tvs with
  | nil => rfl
  | cons tv r ih => simp only [PF.obsOf, List.foldr_cons, List.map_cons] at ih ⊢; rw [ih]; rfl

/-- **THE LOAD OBSERVATIONS AGREE**: the machine run's `obsLoad` is the reference's. -/
theorem obsLoad_eq {P D : Type} {run : PF.PFRun P D} {X : Exec} {h : Nat}
    (hrow : machRow (run.trace h) = refRow X h) (k : Nat) : run.obsLoad h k = refObsLoad X h k := by
  unfold PF.PFRun.obsLoad refObsLoad
  rw [← hrow]
  unfold machRow
  rw [List.getElem?_map]
  cases (PF.loadsOf (run.trace h))[k]? with
  | none => rfl
  | some tvs => simp [obsOf_eq]

/-! ## 3. The theorem -/

/-- **(T-cmp), S3a: REFERENCE ⊆ MACHINE V2** (plan §0, promises-first form).  Every execution the reference
allows of an S3a program — paths `trs` (`T.runAll chs = some trs`), load values `ν` satisfying the path
conditions, a global memory order `g` with `rvwmoRef` — that is single-size (NA-6) is a valid run of machine v2 over
the same program, promises first, every hart done, with the same per-hart load observations, final registers and
final memory.  `platformOrd` is `True` with translation off (CmpDefs.lean). -/
theorem rvwmo_complete (T : Test) (hT : progS3aB T = true) {chs : List (List Bool)} {trs : List SSt} {ν : Val}
    {g : List EvId} (hrun : T.runAll chs = some trs) (hc : condsOk ν trs = true)
    (hX : rvwmoRef (conc T trs ν g)) (hss : singleSize (conc T trs ν g)) (_ : platformOrd (conc T trs ν g)) :
    ∃ run : PF.PFRun LP Unit,
      PF.validRun litStep (testImg T) () (progs T) (memOf (conc T trs ν g)) run ∧ promisesFirst run.evs ∧
      run.cfg.pcAgs.length = T.harts.length ∧ allDone run.cfg ∧
      (∀ h, machRow (run.trace h) = refRow (conc T trs ν g) h) ∧
      (∀ h r, regOf run.cfg h r = finalReg trs ν h r) ∧
      (∀ a n, finalMem (testImg T) (memOf (conc T trs ν g)) a n = refFinalMem (conc T trs ν g) a n) := by
  -- the setting
  obtain ⟨hlen, hpaths⟩ := runAll_spec hrun
  have hio : T.io = [] := by
    simp only [progS3aB, Bool.and_eq_true, List.isEmpty_iff] at hT; exact hT.1.1
  have hxio : (conc T trs ν g).io = [] := hio
  generalize hXd : conc T trs ν g = X at hX hss ⊢
  have hxc : X = conc T trs ν X.gmo := by rw [← hXd]; rfl
  have hxio' : X.io = [] := by rw [← hXd]; exact hio
  have hctx : ∀ i (hi : i < trs.length), HCtx T trs ν X i trs[i] :=
    fun i hi => ⟨hxc, hX, hxio', hss, hc, hT, List.getElem?_eq_getElem hi⟩
  have hprog : ∀ i, ∀ ins ∈ T.prog i, instrS3a ins = true := by
    intro i ins hins
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hins
    exact instr_scope (h := i) hT (List.getElem?_eq_getElem hk)
  -- every message is promisable
  have hmsg : ∀ m ∈ memOf X, msgOk (pmInit (testImg T) () (progs T)).pcAgs.length m := by
    intro m hm
    unfold memOf memG at hm
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hm
    obtain ⟨hwg, hws⟩ := List.mem_filter.1 hw
    have hwi := ids_of_gmo hwg hX
    obtain ⟨w1, w2⟩ := w
    have hw1 : w1 < trs.length := by
      rw [hxc, conc_ids] at hwi
      obtain ⟨l, hl1, _⟩ := (mem_idsOf _ _).1 hwi
      simp only [List.getElem?_map] at hl1
      exact (List.getElem?_eq_some_iff.1 (Option.map_eq_some_iff.1 hl1 |>.choose_spec.1)).1
    have c := hctx w1 hw1
    have hw2 := c.idx_lt hwi
    obtain ⟨ch, hch⟩ := hpaths w1 hw1
    have hsz := symRun_stSz _ (hprog w1) w1 _ _ _ _ hch (fun se hse => by simp [Test.init] at hse)
      trs[w1].evs[w2] (List.getElem_mem hw2)
    have hsk := c.sk (List.getElem?_eq_getElem hw2)
    have hst : trs[w1].evs[w2].sk.kind.isStore = true := by rw [← hsk]; exact hws
    have hpos := hsz hst
    have hdl := HCtx.wdat_len' hX hwi hws
    refine ⟨.inl ?_, w1, rfl, ?_⟩
    · simp only [msgOf]
      intro he
      have := congrArg List.length he
      rw [List.length_map, hdl, hsk] at this
      simp at this; omega
    · simp [pmInit, progs_len, ← hlen, hw1]
  -- the promise phase
  obtain ⟨c0, hps, himg0, hlog0, hdev0, hlen0, hags0⟩ := promsRun (pstep := litStep) (memOf X)
    (pmInit (testImg T) () (progs T)) hmsg
  have hlog0' : c0.pcLog = memOf X := by rw [hlog0]; rfl
  have hlen0' : c0.pcAgs.length = T.harts.length := by rw [hlen0]; simp [pmInit, progs_len]
  let P : Nat → GSet Nat := fun i => match c0.pcAgs[i]? with | some ag => ag.paProm | none => ∅
  have hag : ∀ i, i < T.harts.length → c0.pcAgs[i]? = some ⟨lpInit T i, psInit, P i⟩ ∧
      ∀ t, t ∈ P i ↔ 0 < t ∧ ownTs (memOf X) i t := by
    intro i hi
    have hi0 : (pmInit (testImg T) () (progs T)).pcAgs[i]? = some ⟨lpInit T i, psInit, ∅⟩ := by
      simp [pmInit, progs_get T hi]
    obtain ⟨ag', h1, h2, h3, h4⟩ := hags0 i _ hi0
    have hP : P i = ag'.paProm := by simp only [P, h1]
    refine ⟨by rw [h1, hP]; cases ag'; simp only at h2 h3; rw [h2, h3], fun t => ?_⟩
    rw [hP, h4 t]
    simp only [pmInit, List.length_nil, List.nil_append]
    constructor
    · rintro (h | h)
      · exact absurd h notElemOfEmpty
      · exact h
    · exact .inr
  -- every hart's path
  have hsolo : ∀ i, i < T.harts.length → ∃ tr lp' ws', soloSteps litStep (testImg T) (memOf X) i
      (lpInit T i, psInit, P i) tr (lp', ws', ∅) ∧
      (machRow tr = refRow X i ∧ lp'.pc = lp'.prog.length ∧ lp'.q = [] ∧ ∀ r, lp'.rd r = finalReg trs ν i r) := by
    intro i hi
    have hi' : i < trs.length := by omega
    obtain ⟨ch, hch⟩ := hpaths i hi'
    obtain ⟨tr, lp', ws', hs, hrow, hpc, hq, hreg⟩ := sim_hart (hctx i hi') hch (P i) (hag i hi).2
    refine ⟨tr, lp', ws', hs, hrow, hpc, hq, fun r => ?_⟩
    rw [hreg r]
    simp [finalReg, List.getElem?_eq_getElem hi']
  obtain ⟨evs, cfg, hs, himg, hlog, hlenc, hdone, _, htr, hst⟩ := statePhase
    (fun i tr lp' (_ : PState) => machRow tr = refRow X i ∧ lp'.pc = lp'.prog.length ∧ lp'.q = [] ∧
      ∀ r, lp'.rd r = finalReg trs ν i r)
    P (lpInit T) c0 himg0 hlog0' hlen0' (fun i hi => (hag i hi).1) hsolo T.harts.length (Nat.le_refl _)
  -- the run
  have htrace : ∀ h, traceOf h ((memOf X).map promEv ++ evs) = traceOf h evs := by
    intro h; rw [traceOf_append, traceOf_proms, List.nil_append]
  refine ⟨⟨(memOf X).map promEv ++ evs, cfg⟩, ⟨⟨pmSteps_append hps hs, fun i ag hi => ?_⟩, hlog⟩,
    ⟨(memOf X).length, fun e he => ?_, fun e he => ?_⟩, hlenc, fun i ag hi => ?_, fun h => ?_, fun h r => ?_,
    fun a n => ?_⟩
  · -- no outstanding promise
    have hil : i < T.harts.length := by rw [← hlenc]; exact (List.getElem?_eq_some_iff.1 hi).1
    obtain ⟨lp', ws', h1, _⟩ := hdone i hil
    rw [h1] at hi; cases hi; rfl
  · rw [List.take_left' (by simp)] at he
    obtain ⟨m, _, rfl⟩ := List.mem_map.1 he; rfl
  · rw [List.drop_left' (by simp)] at he; exact hst e he
  · -- every hart done
    have hil : i < T.harts.length := by rw [← hlenc]; exact (List.getElem?_eq_some_iff.1 hi).1
    obtain ⟨lp', ws', h1, _, h2, h3, _⟩ := hdone i hil
    rw [h1] at hi; cases hi; exact ⟨h2, h3⟩
  · -- the rows
    show machRow (traceOf h ((memOf X).map promEv ++ evs)) = refRow X h
    rw [htrace]
    by_cases hh : h < T.harts.length
    · obtain ⟨lp', ws', _, h2, _⟩ := hdone h hh; exact h2
    · rw [htr h (by omega)]
      have : X.evs[h]? = none := by
        rw [hxc]; simp only [conc, List.getElem?_mapIdx]
        rw [List.getElem?_eq_none (by omega)]; rfl
      simp [refRow, this, machRow, PF.loadsOf]
  · -- the final registers
    by_cases hh : h < T.harts.length
    · obtain ⟨lp', ws', h1, _, _, _, h4⟩ := hdone h hh
      simp only [regOf, h1]; exact h4 r
    · have h1 : cfg.pcAgs[h]? = none := List.getElem?_eq_none (by omega)
      have h2 : trs[h]? = none := List.getElem?_eq_none (by omega)
      simp [regOf, h1, finalReg, h2, Ex.eval]
  · -- the final memory
    have c0' : X.img = T.imgF := by rw [hxc]; rfl
    have hw : ∀ e, ∀ b ∈ (X.ev e).wdat, b < 256 := by
      cases htl : trs with
      | nil =>
        intro e b hb
        rw [hxc] at hb
        unfold Exec.ev conc at hb
        simp [htl] at hb
        have hd : (default : Ev).wdat = [] := rfl
        rw [hd] at hb; cases hb
      | cons s0 rest =>
        exact (hctx 0 (by rw [htl]; simp)).wdatAll
    exact finalMem_eq hT hX c0' hw a n

/-- **(T-cmp), S3a, from `progExec`** (RefProg.lean's executions, the form `forbiddenRef`/`allowedRef` quantify
over). -/
theorem rvwmo_complete_exec (T : Test) (hT : progS3aB T = true) {chs : List (List Bool)} {ν : Val}
    {g : List EvId} (hE : progExec T chs ν g)
    (hss : ∀ trs, T.runAll chs = some trs → singleSize (conc T trs ν g)) :
    ∃ trs, T.runAll chs = some trs ∧ ∃ run : PF.PFRun LP Unit,
      PF.validRun litStep (testImg T) () (progs T) (memOf (conc T trs ν g)) run ∧ promisesFirst run.evs ∧
      run.cfg.pcAgs.length = T.harts.length ∧ allDone run.cfg ∧
      (∀ h k, run.obsLoad h k = refObsLoad (conc T trs ν g) h k) ∧
      (∀ h r, regOf run.cfg h r = finalReg trs ν h r) ∧
      (∀ a n, finalMem (testImg T) (memOf (conc T trs ν g)) a n = refFinalMem (conc T trs ν g) a n) := by
  unfold progExec at hE
  cases hr : T.runAll chs with
  | none => rw [hr] at hE; cases hE
  | some trs =>
    rw [hr] at hE
    obtain ⟨hc, hX⟩ := hE
    obtain ⟨run, h1, h2, h0, h3, h4, h5, h6⟩ := rvwmo_complete T hT hr hc hX (hss trs hr) trivial
    exact ⟨trs, rfl, run, h1, h2, h0, h3, fun h k => obsLoad_eq (h4 h) k, h5, h6⟩

end Weak.Prom.Cmp
