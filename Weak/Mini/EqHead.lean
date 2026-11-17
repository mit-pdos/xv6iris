/-
Weak/Mini: **CROSS-CHECKS — the full stack's verdicts recovered from the mini headlines via E1** (mini plan rev 4
§2 L6 "Cross-checks via E1/E2: `inf_mpLoop` and `ref_lbdd`/`ref_mpFF` recovered as corollaries").

* §1 the constants coincide: the mini program texts are the full tests (`lbddP.toTest Lit.lbdd.cond = Lit.lbdd`,
  `mpFFP.toTest Lit.mpFF.cond = Lit.mpFF`, `loopP.toTest tLoop.cond = tLoop`, all `rfl`), `lbddP = lbddM` (the
  EqRefWit.lean witness program), and the loop front end's texts are `xsLoop` (`loopP.xs = xsLoop`).
* §3 `ref_lbdd_of_mini : forbiddenRef Lit.lbdd` and `ref_mpFF_of_mini : forbiddenRef Lit.mpFF` (the statements of
  RefLitmus.lean's `ref_lbdd`/`ref_mpFF`, there proved by the kernel checker), from `mini_forbidden_lbdd`/
  `mini_forbidden_mpFF` through the loop-free E1b (`e1bLF`): a `progExec` execution is a halted mini cut, the
  outcome's final registers are the cut's load values (the loads are the only sources of `x5`/`x7`).
* §4 `inf_mpLoop_of_mini` (every `cond`) and `inf_mpLoop_recovered` (= Weak/Prom/InfLoop.lean:172 `inf_mpLoop`,
  verbatim statement) from `mini_inf_mpLoop` through E1b (`e1b`) and the correspondence `Corr` of `toFull`.
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Mini.Head
import Weak.Mini.EqRefLF
import Weak.Mini.EqRefWit
import Weak.Prom.InfLoop

namespace Weak.Mini

open Weak.Prom.Ref
open Weak.Prom.Pfx
open Weak.Mini.Logic (lbddP mpFFP loopP)

/-! ## 1. The constants -/

theorem lbddP_eq : lbddP = lbddM := rfl

theorem lbddP_toTest : lbddP.toTest Lit.lbdd.cond = Lit.lbdd := rfl

theorem mpFFP_toTest : mpFFP.toTest Lit.mpFF.cond = Lit.mpFF := rfl

theorem loopP_toTest : loopP.toTest Weak.Prom.PF.Loop.tLoop.cond = Weak.Prom.PF.Loop.tLoop := rfl

theorem loopP_xs : loopP.xs = Weak.Prom.PF.Loop.xsLoop := rfl

/-! ## 2. Facts about the finite correspondence -/

theorem toKind_ld {k : MK} (h : k.toKind = .ld) : k = .ld := by cases k <;> simp_all [MK.toKind]

/-- A full load event of a simulated state is a mini load event with the cut's value. -/
theorem sim_ld {sz h : Nat} {V : EvId → Nat} {ν : Val} {m : Weak.Mini.MSt} {s : SSt} (H : SimSt sz h V ν m s)
    {i : Nat} (hi : i < s.evs.length) (hk : s.evs[i].sk.kind = .ld) :
    ∃ hm : i < m.evs.length, m.evs[i].kind = .ld ∧ m.evs[i].v = V (h, i) % 2 ^ (8 * sz) := by
  have hm : i < m.evs.length := by rw [← H.evl]; exact hi
  have hE := H.ev i hi hm
  have hk' : m.evs[i].kind = .ld := toKind_ld (by rw [← hk, hE.sk]; rfl)
  exact ⟨hm, hk', hE.lv hk'⟩

/-- A full non-load event of a simulated state is a mini non-load event. -/
theorem sim_nld {sz h : Nat} {V : EvId → Nat} {ν : Val} {m : Weak.Mini.MSt} {s : SSt} (H : SimSt sz h V ν m s)
    {i : Nat} (hi : i < s.evs.length) (hk : s.evs[i].sk.kind ≠ .ld) :
    ∃ hm : i < m.evs.length, m.evs[i].kind ≠ .ld := by
  have hm : i < m.evs.length := by rw [← H.evl]; exact hi
  have hE := H.ev i hi hm
  refine ⟨hm, fun hk' => hk ?_⟩
  rw [hE.sk]; simp [MEv.toEv, hk', MK.toKind]

/-- A run of a branch-free two-hart test is the run along the empty choice lists. -/
theorem runAll_two {T : Test} (h2 : T.harts.length = 2) (h0 : ∀ b t, T.runH 0 (b :: t) = none)
    (h1 : ∀ b t, T.runH 1 (b :: t) = none) {chs : List (List Bool)} {trs : List SSt}
    (h : T.runAll chs = some trs) : trs = (T.runAll [[], []]).getD [] := by
  unfold Test.runAll at h
  split at h
  · rename_i hl
    rw [h2] at hl
    match chs, hl, h with
    | [c0, c1], _, h =>
      cases c0 with
      | cons b t => simp [Test.runFrom, h0] at h
      | nil =>
        cases c1 with
        | cons b t => simp [Test.runFrom, h1] at h
        | nil => unfold Test.runAll; rw [if_pos (by rw [h2]; rfl), h]; rfl
  · cases h

/-- The value of a sign-extending word load whose register value is `v` (`v` a word). -/
theorem sext_word {w v : Nat} (hw : w < 2 ^ 32) (h : Weak.Prom.Ref.sext 4 w = v % Weak.Prom.Ref.two64)
    (hv : v < 2 ^ 31) : w = v := by
  unfold Weak.Prom.Ref.sext at h
  have : v % Weak.Prom.Ref.two64 = v := Nat.mod_eq_of_lt (by unfold Weak.Prom.Ref.two64; omega)
  rw [this] at h
  split at h
  · unfold Weak.Prom.Ref.two64 at h; omega
  · exact h

/-- A load event's bytes `ν e = byteList (C.V e) 4` give the register value `sext 4 (C.V e % 2^32)`. -/
theorem eval_ld {ν : Val} {V : EvId → Nat} {e : EvId} (he : ν e = byteList (V e) 4) :
    (Ex.ld e 4 true).eval ν = Weak.Prom.Ref.sext 4 (V e % 2 ^ 32) := by
  simp only [Ex.eval, he, List.take_of_length_le (Nat.le_of_eq (byteList_length _ _)), bytesVal_byteList,
    Nat.mod_mod, if_true]

/-- The first load value of an event list whose first event is a load. -/
theorem obs_first {l : List MEv} (hm : 0 < l.length) (hk : l[0].kind = .ld) :
    (l.filterMap (fun e => if e.kind = .ld then some e.v else none))[0]? = some l[0].v := by
  match l, hm, hk with
  | e :: _, _, hk => simp only [List.getElem_cons_zero] at hk ⊢; simp [hk]

/-- The second load value of an event list `ld, non-load, ld, …`. -/
theorem obs_second {l : List MEv} (hm : 2 < l.length) (hk0 : l[0].kind = .ld) (hk1 : l[1].kind ≠ .ld)
    (hk2 : l[2].kind = .ld) :
    (l.filterMap (fun e => if e.kind = .ld then some e.v else none))[1]? = some l[2].v := by
  match l, hm, hk0, hk1, hk2 with
  | e0 :: e1 :: e2 :: _, _, hk0, hk1, hk2 =>
    simp only [List.getElem_cons_zero, List.getElem_cons_succ] at hk0 hk1 hk2 ⊢
    simp [hk0, hk1, hk2]

/-! ## 3. The finite corollaries -/

/-- The run of `lbdd` (no branch: the only run). -/
def lbddTrs (c : OC) : List SSt := ((lbddP.toTest c).runAll [[], []]).getD []

/-- **`ref_lbdd` recovered from `mini_forbidden_lbdd`** (for `lbdd`'s own condition `x5@0 = 1 ∧ x5@1 = 1`). -/
theorem ref_lbdd_mini : forbiddenRef (lbddP.toTest Lit.lbdd.cond) := by
  intro chs ν g hE hO
  obtain ⟨C, hC, _, hrun, _, hev, _⟩ := e1bLF lbddP lbddP_wf _ chs ν g hE
  have htrs : toCut lbddP Lit.lbdd.cond C = lbddTrs Lit.lbdd.cond :=
    runAll_two rfl (fun _ _ => rfl) (fun _ _ => rfl) hrun
  unfold outcome at hO
  rw [hrun, htrs] at hO
  rw [htrs] at hev
  have H := simC_toCut lbddP_wf Lit.lbdd.cond C
  rw [htrs] at H
  -- the two loads' bytes are the cut's values
  have hν0 : ν (0, 0) = byteList (C.V (0, 0)) 4 := by
    have := congrArg Ev.rdat (hev (0, 0) (by rw [conc_ids]; decide))
    exact this
  have hν1 : ν (1, 0) = byteList (C.V (1, 0)) 4 := by
    have := congrArg Ev.rdat (hev (1, 0) (by rw [conc_ids]; decide))
    exact this
  -- the outcome: both registers `x5` are 1
  have hf0 : finalReg (lbddTrs Lit.lbdd.cond) ν 0 5 = (Ex.ld (0, 0) 4 true).eval ν := rfl
  have hf1 : finalReg (lbddTrs Lit.lbdd.cond) ν 1 5 = (Ex.ld (1, 0) 4 true).eval ν := rfl
  have hO' : finalReg (lbddTrs Lit.lbdd.cond) ν 0 5 = 1 % Weak.Prom.Ref.two64 ∧
      finalReg (lbddTrs Lit.lbdd.cond) ν 1 5 = 1 % Weak.Prom.Ref.two64 := by
    simpa [OC.eval, MProg.toTest, Lit.lbdd, Lit.mk, Lit.ands, Lit.r] using hO
  rw [hf0, eval_ld hν0] at hO'
  rw [hf1, eval_ld hν1] at hO'
  have hw0 := sext_word (Nat.mod_lt _ (by decide)) hO'.1 (by decide)
  have hw1 := sext_word (Nat.mod_lt _ (by decide)) hO'.2 (by decide)
  -- the cut's first loads
  obtain ⟨hm0, hk0, hv0⟩ := sim_ld (H.sim 0 (by decide)) (i := 0) (by decide) rfl
  obtain ⟨hm1, hk1, hv1⟩ := sim_ld (H.sim 1 (by decide)) (i := 0) (by decide) rfl
  apply mini_forbidden_lbdd C hC
  exact ⟨by rw [MCut.obsLoad, obs_first hm0 hk0, hv0]; exact congrArg some hw0,
    by rw [MCut.obsLoad, obs_first hm1 hk1, hv1]; exact congrArg some hw1⟩

/-- **`ref_lbdd`, the full stack's statement** (RefLitmus.lean:20), recovered from the mini headline. -/
theorem ref_lbdd_of_mini : forbiddenRef Lit.lbdd := lbddP_toTest ▸ ref_lbdd_mini

/-- The run of `mpFF` (no branch: the only run). -/
def mpFFTrs (c : OC) : List SSt := ((mpFFP.toTest c).runAll [[], []]).getD []

/-- **`ref_mpFF` recovered from `mini_forbidden_mpFF`** (for `mpFF`'s own condition `x5@1 = 1 ∧ x7@1 = 0`). -/
theorem ref_mpFF_mini : forbiddenRef (mpFFP.toTest Lit.mpFF.cond) := by
  intro chs ν g hE hO
  obtain ⟨C, hC, _, hrun, _, hev, _⟩ := e1bLF mpFFP mpFFP_wf _ chs ν g hE
  have htrs : toCut mpFFP Lit.mpFF.cond C = mpFFTrs Lit.mpFF.cond :=
    runAll_two rfl (fun _ _ => rfl) (fun _ _ => rfl) hrun
  unfold outcome at hO
  rw [hrun, htrs] at hO
  rw [htrs] at hev
  have H := simC_toCut mpFFP_wf Lit.mpFF.cond C
  rw [htrs] at H
  have hν0 : ν (1, 0) = byteList (C.V (1, 0)) 4 := by
    have := congrArg Ev.rdat (hev (1, 0) (by rw [conc_ids]; decide))
    exact this
  have hν2 : ν (1, 2) = byteList (C.V (1, 2)) 4 := by
    have := congrArg Ev.rdat (hev (1, 2) (by rw [conc_ids]; decide))
    exact this
  have hf5 : finalReg (mpFFTrs Lit.mpFF.cond) ν 1 5 = (Ex.ld (1, 0) 4 true).eval ν := rfl
  have hf7 : finalReg (mpFFTrs Lit.mpFF.cond) ν 1 7 = (Ex.ld (1, 2) 4 true).eval ν := rfl
  have hO' : finalReg (mpFFTrs Lit.mpFF.cond) ν 1 5 = 1 % Weak.Prom.Ref.two64 ∧
      finalReg (mpFFTrs Lit.mpFF.cond) ν 1 7 = 0 % Weak.Prom.Ref.two64 := by
    simpa [OC.eval, MProg.toTest, Lit.mpFF, Lit.mk, Lit.ands, Lit.r] using hO
  rw [hf5, eval_ld hν0] at hO'
  rw [hf7, eval_ld hν2] at hO'
  have hw0 := sext_word (Nat.mod_lt _ (by decide)) hO'.1 (by decide)
  have hw2 := sext_word (Nat.mod_lt _ (by decide)) hO'.2 (by decide)
  obtain ⟨_, hk0, hv0⟩ := sim_ld (H.sim 1 (by decide)) (i := 0) (by decide) rfl
  obtain ⟨_, hk1⟩ := sim_nld (H.sim 1 (by decide)) (i := 1) (by decide) (by decide)
  obtain ⟨hm2, hk2, hv2⟩ := sim_ld (H.sim 1 (by decide)) (i := 2) (by decide) rfl
  apply mini_forbidden_mpFF C hC
  exact ⟨by rw [MCut.obsLoad, obs_first (by omega) hk0, hv0]; exact congrArg some hw0,
    by rw [MCut.obsLoad, obs_second hm2 hk0 hk1 hk2, hv2]; exact congrArg some hw2⟩

/-- **`ref_mpFF`, the full stack's statement** (RefLitmus.lean:53), recovered from the mini headline. -/
theorem ref_mpFF_of_mini : forbiddenRef Lit.mpFF := mpFFP_toTest ▸ ref_mpFF_mini

/-! ## 4. The infinite corollary -/

section inf

variable {P : MProg} {cond : OC} {X : MExec} {E : IExec}

/-- The correspondence of `toFull` for a mini execution (EqRef.lean). -/
theorem corr_toFull (hwf : P.wf) (hX : miniExec P X) : Corr P.sz P.ini (X.evs P) (toFull P cond X) :=
  (simE_toFull hwf cond X).toA.corr hwf hX.1 (fun _ _ _ => rfl)

theorem toKind_isMem (k : MK) : k.toKind.isMem = true ↔ k = .ld ∨ k = .st := by
  cases k <;> simp [MK.toKind, Kind.isMem]

theorem toKind_isLoad (k : MK) : k.toKind.isLoad = true ↔ k = .ld := by
  cases k <;> simp [MK.toKind, Kind.isLoad]

/-- **E1b, read event by event**: a full execution `E` of an F program is a mini execution `X` whose memory
operations, loads, addresses and load bytes are `E`'s (`byteList` of a word value). -/
theorem transfer (hwf : P.wf) (hE : infExec (P.toTest cond) E) :
    ∃ X, miniExec P X ∧ (∀ e, E.has e ↔ (X.evs P).has e) ∧ (∀ e, E.isMem e ↔ (X.evs P).isMem e) ∧
      (∀ e, E.has e → ((E.sk e).kind.isLoad = true ↔ (X.evs P).isLd e)) ∧
      (∀ e, E.has e → (E.ev e).pa = ((X.evs P).ev e).pa) ∧
      (∀ e, E.has e → (X.evs P).isLd e → (E.ev e).rdat = byteList ((X.evs P).ev e).v P.sz ∧
        ((X.evs P).ev e).v < 2 ^ (8 * P.sz)) := by
  obtain ⟨X, hX, hhas, hev, _⟩ := e1b P hwf cond E hE
  have C := corr_toFull (cond := cond) hwf hX
  have hH : ∀ e, E.has e ↔ (X.evs P).has e := fun e => (hhas e).trans (C.has e)
  have hV : ∀ e, E.has e → E.ev e = ((X.evs P).ev e).toEv P.sz := fun e he => by
    rw [hev e he, C.ev e ((C.has e).1 ((hhas e).1 he))]
  have hsk : ∀ e, E.has e → (E.sk e).kind = ((X.evs P).ev e).kind.toKind := fun e he => by
    unfold IExec.sk; rw [hV e he]; rfl
  refine ⟨X, hX, hH, fun e => ⟨?_, ?_⟩, fun e he => ?_, fun e he => by rw [hV e he]; rfl, fun e he hl => ?_⟩
  · rintro ⟨he, hm⟩
    rw [hsk e he, toKind_isMem] at hm
    exact ⟨(hH e).1 he, hm⟩
  · rintro ⟨he, hm⟩
    have he' := (hH e).2 he
    exact ⟨he', by rw [hsk e he', toKind_isMem]; exact hm⟩
  · rw [hsk e he, toKind_isLoad]; rfl
  · refine ⟨?_, C.vlt e ((hH e).1 he) (.inl hl)⟩
    rw [hV e he]; simp [MEv.toEv, show ((X.evs P).ev e).kind = .ld from hl]

/-- A word load whose four bytes are `[1, 0, 0, 0]` returned 1. -/
theorem word_one {v : Nat} (hlt : v < 2 ^ 32) (h : byteList v 4 = [1, 0, 0, 0]) : v = 1 := by
  have := congrArg bytesVal h
  rw [bytesVal_byteList, Nat.mod_eq_of_lt hlt] at this
  exact this

end inf

/-- **`inf_mpLoop` recovered from `mini_inf_mpLoop`**, for `loopP.toTest cond` (any outcome condition: no
execution notion reads it). -/
theorem inf_mpLoop_of_mini (cond : OC) {E : IExec} (hE : infExec (loopP.toTest cond) E) (h i j : Nat)
    (hi : E.isMem (h, i)) (hj : E.isMem (h, j)) (hij : i < j)
    (hnext : ∀ k, i < k → k < j → ¬ E.isMem (h, k))
    (hfl : (E.sk (h, i)).kind.isLoad = true) (hfa : (E.ev (h, i)).pa = Lit.Y) (hfv : (E.ev (h, i)).rdat = [1, 0, 0, 0])
    (hdl : (E.sk (h, j)).kind.isLoad = true) (hda : (E.ev (h, j)).pa = Lit.X) :
    (E.ev (h, j)).rdat = [1, 0, 0, 0] := by
  obtain ⟨X, hX, _, hmem, hld, hpa, hrd⟩ := transfer loopP_wf hE
  have hfl' := (hld _ hi.1).1 hfl
  have hdl' := (hld _ hj.1).1 hdl
  have hfv' : ((X.evs loopP).ev (h, i)).v = 1 :=
    word_one (hrd _ hi.1 hfl').2 ((hrd _ hi.1 hfl').1.symm.trans hfv)
  have hv := mini_inf_mpLoop hX h i j ((hmem _).1 hi) ((hmem _).1 hj) hij
    (fun k h1 h2 hk => hnext k h1 h2 ((hmem _).2 hk)) hfl' (by rw [← hpa _ hi.1]; exact hfa) hfv' hdl'
    (by rw [← hpa _ hj.1]; exact hda)
  rw [(hrd _ hj.1 hdl').1, hv]
  rfl

/-- **`inf_mpLoop`, the full stack's statement verbatim** (Weak/Prom/InfLoop.lean:172), recovered from the mini
headline `mini_inf_mpLoop` via E1b (`loopP.toTest tLoop.cond = tLoop`). -/
theorem inf_mpLoop_recovered {E : IExec} (hE : infExec Weak.Prom.PF.Loop.tLoop E) (h i j : Nat)
    (hi : E.isMem (h, i)) (hj : E.isMem (h, j)) (hij : i < j)
    (hnext : ∀ k, i < k → k < j → ¬ E.isMem (h, k))
    (hfl : (E.sk (h, i)).kind.isLoad = true) (hfa : (E.ev (h, i)).pa = Lit.Y) (hfv : (E.ev (h, i)).rdat = [1, 0, 0, 0])
    (hdl : (E.sk (h, j)).kind.isLoad = true) (hda : (E.ev (h, j)).pa = Lit.X) :
    (E.ev (h, j)).rdat = [1, 0, 0, 0] :=
  inf_mpLoop_of_mini Weak.Prom.PF.Loop.tLoop.cond (by rw [loopP_toTest]; exact hE) h i j hi hj hij hnext hfl hfa hfv
    hdl hda

end Weak.Mini
