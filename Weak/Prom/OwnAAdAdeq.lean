/-
Weak/Prom: **SchedAD — THE CONCURRENT ADEQUACY of track (a) over E-c's A/D variant, `adequacyAV`** (owner ruling
[OWN.P14]; G4-review3.md §5 A-2, §6 item 2; plan rev 7 §2 [R2.s11], §3 rev 5; OwnAAdeq.lean is the v2 original).

```
theorem adequacyAV (π Φ Ψ Dd) :
    PO_img π img → PO_adV π img M → adEmit pstep → (∀ h, Ψ h []) → wpPremiseV … → Ad.validRunV pstep img () ps evs cfg →
    cfg.pcLog = M →
      (i) termination ∧ (ii) Ψ at every prefix of every hart's v2 trace ∧ (iii) the non-A/D partition ∧
      (vi) adExactV img M ∧ (iv) Valid π img M |M|
```
* PO-ad is a PREMISE the client discharges (A0's PO_ad, plan §2 (iv)), not an assumption about runs; `adExactV` is
  PROVED from the run (`adExactV_of_run`, the variant's `PF.validRun_adExact` of plan §0 [R5.1]).  Its one generic
  side condition is `adEmit pstep`: the program half's A/D labels write `update_PTE_Bits` of the bytes they read
  (M20 (6), "`adData` is emission": AdMachine.lean leaves the written data to `pstep`, as for every write label;
  Sail computes it).  `adEmit` is a property of the hardware front end, not of a program, and holds vacuously for a
  program half that emits no A/D label (OwnAAdMP.lean `adEmit_liftV`).
* Allocation (plan R-a5): as OwnAAdeq.lean, except that the one-shot of every A/D timestamp is SHOT at once
  (`pendsV_alloc`; "A/D writes carry no obligation"), so the client receives `pend g t` only for non-A/D `t`.
* Proof: the schedule lemma over non-A/D timestamps (OwnAAdSched.lean `schedV`) turns the valid run into an execution
  of the guarded language; `wp_strong_adequacy_gen` gives the state interpretation at its end.  There every
  non-A/D timestamp is fulfilled and every A/D timestamp was shot at the start, so the doom box holds no `pend s`.
* Not re-exported: A0 (iii′) fulfil-nodup and (v) `traceWf` (machine lemmas of the variant, not track-(a) content).
No named assumption.  No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.OwnAAdWp

namespace Weak.Prom.OAd

open MachCSL MachCSL.Stdpp Iris.Std
open Weak (Image Dsrc)
open Weak.Prom Weak.Prom.PF Weak.Prom.OA
open PLabel
open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode
open Iris.ProgramLogic.Language Iris.ProgramLogic.Language.Notation

variable {P D V : Type} {hlc : HasLC}

/-! ## 1. Machine facts of the variant's valid runs -/

/-- A timestamp leaving the promise set along a solo run is fulfilled by one of its steps. -/
theorem soloQV_fulfil {pst : P → Unit → Ad.VLabel → P → Unit → Prop} {img : Image} {M : List PMsg} {i : Nat}
    {Q : PState → Ad.VLabel → Option Nat → Prop} :
    ∀ {x y : P × PState × GSet Nat} {tr : List (Ad.VLabel × Option Nat)}, Ad.soloQV pst img M i Q x tr y →
      ∀ {t : Nat}, t ∈ x.2.2 → t ∉ y.2.2 →
      ∃ (z : P × PState × GSet Nat) (l : Ad.VLabel) (p' : P) (ws' : PState) (prom' : GSet Nat),
        pst z.1 () l p' () ∧ Ad.memStepV img M i z.2.2 z.2.1 l (some t) ws' prom' ∧ (l, some t) ∈ tr := by
  intro x y tr h
  induction h with
  | refl x => intro t h1 h2; exact absurd h1 h2
  | step x l ots p' ws' prom' tr y _ hp hm _ ih =>
    intro t h1 h2
    by_cases ht : t ∈ prom'
    · obtain ⟨z, l', p'', ws'', prom'', a, b, c⟩ := ih ht h2
      exact ⟨z, l', p'', ws'', prom'', a, b, List.mem_cons_of_mem _ c⟩
    · rcases Ad.memStepV_prom hm with ⟨_, e⟩ | ⟨ts, hots, _, e⟩
      · rw [e] at ht; exact absurd h1 ht
      · have : t = ts := by
          apply Classical.byContradiction; intro hne
          exact ht (by rw [e]; exact elemOfDifference.2 ⟨h1, fun hs => hne (elemOfSingleton.1 hs)⟩)
        subst this hots
        exact ⟨x, l, p', ws', prom', hp, hm, List.mem_cons_self⟩

section run

variable {pstep : P → Unit → Ad.VLabel → P → Unit → Prop} {img : Image} {ps : List P} {evs : List Ad.VEvt}
  {cfg : PCfg P Unit}

theorem validRunV_len (hv : Ad.validRunV pstep img () ps evs cfg) : cfg.pcAgs.length = ps.length := by
  have := (Ad.pmStepsV_inv hv.1).2.2.1; simpa [pmInit] using this

/-- EVERY TIMESTAMP IS FULFILLED BY ITS AUTHOR (the variant's A0 (iii)): a step of the author's solo run. -/
theorem validRunV_fulfil (hv : Ad.validRunV pstep img () ps evs cfg) :
    ∀ t, 1 ≤ t → t ≤ cfg.pcLog.length → ∃ i, i < ps.length ∧
      ∃ (z : P × PState × GSet Nat) (l : Ad.VLabel) (p' : P) (ws' : PState) (prom' : GSet Nat),
        pstep z.1 () l p' () ∧ Ad.memStepV img cfg.pcLog i z.2.2 z.2.1 l (some t) ws' prom' ∧
        (l, some t) ∈ Ad.traceOfV i evs := by
  intro t h1 h2
  have hwf := Ad.pmStepsV_wf hv.1 (pmInit_wf img () ps)
  have hmt : cfg.pcLog[t - 1]? = some cfg.pcLog[t - 1] := List.getElem?_eq_getElem (by omega)
  obtain ⟨_, i, hti, hil⟩ := hwf.2 _ (List.mem_of_getElem? hmt)
  rw [validRunV_len hv] at hil
  obtain ⟨ag, hag, P0, hP0, hs⟩ := Ad.validRunV_solo hv i _ (List.getElem?_eq_getElem hil)
  have hin : t ∈ P0 := (hP0 t).2 ⟨by omega, _, hmt, hti⟩
  have hout : t ∉ ag.paProm := by rw [hv.2 i ag hag]; exact notElemOfEmpty
  obtain ⟨z, l, p', ws', prom', hp, hm, hmem⟩ := soloQV_fulfil hs hin hout
  exact ⟨i, hil, z, l, p', ws', prom', hp, hm, hmem⟩

end run

/-- The written bytes of a v2 write label are never A/D-class with data (`labelMsg`, MachNota.lean): the only
`.cmo`-class label is `LCmo`, whose message has no data. -/
theorem labelMsg_ad {i : Nat} {l : PLabel} {m : PMsg} (h : Mach.labelMsg i l = some m) (hc : isAdV m) :
    m.data = [] := by
  unfold isAdV PClass.ad at hc
  cases l <;> simp only [Mach.labelMsg, Option.some.injEq, reduceCtorEq] at h <;> subst h <;>
    simp_all [stClass] <;> split at hc <;> cases hc

/-- An entry of a byte run. -/
theorem bytesAll_getV {Q : Int → Nat → BitVec 8 → Prop} : ∀ {a : Int} {tvs : List (Nat × BitVec 8)} {j : Nat}
    {tv : Nat × BitVec 8}, bytesAll Q a tvs → tvs[j]? = some tv → Q (a + j) tv.1 tv.2
  | _, [], _, _, _, h => by cases h
  | a, (t0, v0) :: r, j, tv, ⟨h0, hr⟩, h => by
    cases j with
    | zero => simp at h; subst h; simpa using h0
    | succ j =>
      have := bytesAll_getV hr (by simpa using h)
      rw [show a + 1 + (j : Int) = a + ((j + 1 : Nat) : Int) by omega] at this
      exact this

/-- A byte read at `t` with no write in `(t, V]` is the byte-wise latest content at `V` (CoreDefs.lean `memAt`). -/
theorem memAt_of {img : Image} {M : List PMsg} {a : Int} {t : Nat} {v : BitVec 8}
    (hb : memByte img M t a = some v) : ∀ V, t ≤ V → ¬ writesIn M a t V → memAt img M V a = some v := by
  intro V
  induction V with
  | zero => intro ht _; have : t = 0 := by omega
            subst this; simpa [memAt, memByte] using hb
  | succ V ih =>
    intro ht hw
    by_cases htV : t = V + 1
    · subst htV
      simp only [memByte] at hb
      simp only [memAt, msgAt, hb]
    · have hnw : (M[V]?.bind (fun m => m.byteAt a)) = none := by
        cases hmV : M[V]? with
        | none => rfl
        | some m =>
          cases hba : m.byteAt a with
          | none => simp [hba]
          | some b0 => exact absurd ⟨V + 1, by omega, Nat.le_refl _, m, by simpa using hmV, by simp [hba]⟩ hw
      simp only [memAt, msgAt, hnw]
      exact ih (by omega) (fun ⟨t', a1, a2, rest⟩ => hw ⟨t', a1, by omega, rest⟩)

/-- THE A/D EMISSION FACT (M20 (6), "`adData` is emission"): an A/D label writes, byte by byte, the A (or A and D)
update of the bytes it read.  A property of the program half's hardware front end. -/
def adEmit (pstep : P → Unit → Ad.VLabel → P → Unit → Prop) : Prop :=
  ∀ s s' b tvs data, pstep s () (.ad b tvs data) s' () →
    ∃ setD, ∀ (j : Nat) bt, data[j]? = some bt → ∃ tv : Nat × BitVec 8, tvs[j]? = some tv ∧ bt = adUpdByte setD j tv.2

/-- **`adExact` OF EVERY VALID RUN OF THE VARIANT** (plan §0 [R5.1] `PF.validRun_adExact`): an A/D message is
fulfilled by its author's A/D update, which reads the latest bytes below it (`adReadOk`) and writes their update. -/
theorem adExactV_of_run {pstep : P → Unit → Ad.VLabel → P → Unit → Prop} {img : Image} {ps : List P}
    {evs : List Ad.VEvt} {cfg : PCfg P Unit} (hemit : adEmit pstep) (hv : Ad.validRunV pstep img () ps evs cfg) :
    adExactV img cfg.pcLog := by
  intro t m h1 h2 hm hc
  obtain ⟨i, _, z, l, p', ws', prom', hp, hmem, -⟩ := validRunV_fulfil hv t h1 h2
  have hmt : cfg.pcLog[t - 1]? = some m := by
    obtain ⟨k, rfl⟩ : ∃ k, t = k + 1 := ⟨t - 1, by omega⟩
    simpa [msgAt] using hm
  cases l with
  | v l0 =>
    exfalso
    have hm2 := (Mach.memStep_msg (memStepV_v_some hmem)).1 t rfl
    rw [hmt] at hm2
    have hd := labelMsg_ad hm2.symm hc
    have hwf := Ad.pmStepsV_wf hv.1 (pmInit_wf img () ps)
    rcases (hwf.2 m (List.mem_of_getElem? hmt)).1 with hne | ⟨k, len, hcl, hlen⟩
    · exact hne hd
    · unfold isAdV PClass.ad at hc; rw [hc] at hcl; cases hcl; omega
  | ad b tvs d =>
    obtain ⟨ts, hts, -, -, -, -, -, hlog, hrd⟩ := Ad.memStepV_ad_inv hmem
    cases hts
    rw [hmt] at hlog; cases hlog
    obtain ⟨setD, hD⟩ := hemit _ _ b tvs d hp
    refine ⟨setD, fun j bt hj => ?_⟩
    obtain ⟨tv, htv, hbt⟩ := hD j bt hj
    obtain ⟨hr1, hr2, hr3⟩ := bytesAll_getV hrd htv
    exact ⟨tv.2, memAt_of hr1 (t - 1) (by omega) hr3, hbt⟩

/-- `Valid` at the end of an execution in which every NON-A/D timestamp is fulfilled (plan §3 second rule). -/
theorem valid_finV {π : Proto} {img : Image} {M : List PMsg} {Ψ : Nat → Trace → Prop} {n : Nat} {σ : CSt}
    (hf : cFacts π img M Ψ n σ) (hout : ∀ k, n ≤ k → (σ k).2.2 = [])
    (hall : ∀ t, 1 ≤ t → t ≤ M.length → ¬ Ad.adAt M t → fulAt σ t) (had : PO_adV π img M) (hex : adExactV img M) :
    Valid π img M M.length := by
  refine valid_of_protoOk hf.1 (fun t h1 h2 => ?_)
  by_cases hat : Ad.adAt M t
  · exact protoOk_ad had hex h1 (by omega) hat
  · obtain ⟨k, e, he, het⟩ := hall t h1 (by omega) hat
    have hk : k < n := by
      apply Classical.byContradiction; intro hk
      rw [hout k (by omega)] at he; cases he
    exact (hf.2 k hk).2.1 e he t het

/-! ## 2. Allocation: the one-shots of A/D timestamps are shot at once -/

section alloc

variable {GF : BundledGFunctors} [GhostVarG GF HSt] [GhostVarG GF Bool]

/-- `m` message one-shots; those with `f k` (A/D timestamps `k + 1`) are shot (plan §3 rev 5: "A/D writes carry no
obligation"). -/
theorem pendsV_alloc : ∀ (f : Nat → Prop) (m : Nat), ⊢@{IProp GF} |==> ∃ mn : List GName, ⌜mn.length = m⌝ ∗
    ([∗list] k ↦ γ ∈ mn, (⌜¬ f k⌝ -∗ ghost_var γ (.own 1) false)) ∗
    □ ([∗list] k ↦ γ ∈ mn, ∀ (_h : f k), ghost_var γ .discard true)
  | _, 0 => by
    iapply bupd_intro
    iexists []
    isplitr
    · ipureintro; rfl
    isplitl
    · exact BigSepL.bigSepL_nil.2
    · imodintro; exact BigSepL.bigSepL_nil.2
  | f, m + 1 => by
    have ih := pendsV_alloc (fun k => f (k + 1)) m
    iintro
    imod ghost_var_alloc false with ⟨%γ, H⟩
    imod ih with ⟨%mn, %hl, K1, #K2⟩
    by_cases hf : f 0
    · imod ghost_var_update true _ false $$ H with H
      imod ghost_var_persist $$ H with #H
      imodintro
      iexists γ :: mn
      isplitr
      · ipureintro; simp [hl]
      isplitl [K1]
      · iapply (BigSepL.bigSepL_cons).2
        iframe K1
        iintro %hn
        exact absurd hf hn
      · imodintro
        iapply (BigSepL.bigSepL_cons).2
        iframe K2
        iintro %_
        iexact H
    · imodintro
      iexists γ :: mn
      isplitr
      · ipureintro; simp [hl]
      isplitl [K1 H]
      · iapply (BigSepL.bigSepL_cons).2
        iframe K1
        iintro -
        iexact H
      · imodintro
        iapply (BigSepL.bigSepL_cons).2
        iframe K2
        iintro %h
        exact absurd h hf

end alloc

/-! ## 3. The core: from any execution to the final facts -/

section core

variable {GF : BundledGFunctors} [InvGpreS GF] [GhostVarG GF HSt] [GhostVarG GF Bool]
variable {pstep : P → Unit → Ad.VLabel → P → Unit → Prop} {pdone : P → Option V} {img : Image} {M : List PMsg}
  {ps : List P}

/-- The client premise of the concurrent adequacy over the variant (OwnAAdeq.lean `wpPremise`; the client receives
the `pend` of every NON-A/D timestamp). -/
def wpPremiseV (hlc : HasLC) (GF : BundledGFunctors) [InvGpreS GF] [GhostVarG GF HSt] [GhostVarG GF Bool]
    (pstep : P → Unit → Ad.VLabel → P → Unit → Prop) (pdone : P → Option V) (img : Image) (M : List PMsg)
    (ps : List P) (π : Proto) (Φ : Nat → V → Prop) (Ψ : Nat → Trace → Prop) (Dd : Nat → Prop) : Prop :=
  ∀ [InvGS_gen hlc GF] (g : AGN) (P0 : Nat → GSet Nat), g.hn.length = ps.length → g.mn.length = M.length →
    g.dd = Dd →
    (∀ h, h < ps.length → ∀ t, t ∈ P0 h ↔ 0 < t ∧ ownTs M h t) →
    ⊢@{IProp GF} doomInv g M -∗ ([∗list] k ↦ _x ∈ g.hn, hartA g k psInit (P0 k) []) -∗
      ([∗list] k ↦ _x ∈ g.mn, (⌜¬ Ad.adAt M (k + 1)⌝ -∗ pend g (k + 1))) ={⊤}=∗
      [∗list] k ↦ p ∈ ps, wpAV g π (hwV pstep pdone img M k) Ψ p
        (fun v => iprop(⌜∃ V, grd π img M V (Φ k v)⌝ ∨ dshot g))

/-- The initial thread pool. -/
def esInitV [Inhabited P] (pstep : P → Unit → Ad.VLabel → P → Unit → Prop) (pdone : P → Option V) (img : Image)
    (M : List PMsg) (ps : List P) : List (CExprV P Unit V) :=
  (List.range ps.length).map (fun k => CExprV.run (hwV pstep pdone img M k) (ps.getD k default))

/-- **THE ADEQUACY CORE over the variant**: after any execution from the initial configuration that ends with every
NON-A/D timestamp fulfilled, the facts hold and every value reached meets its (guarded) postcondition. -/
theorem adeq_coreV [Inhabited P] {π : Proto} {Φ : Nat → V → Prop} {Ψ : Nat → Trace → Prop} {Dd : Nat → Prop}
    (himg : PO_img π img) (had : PO_adV π img M) (hex : adExactV img M)
    (hΨ0 : ∀ h, Ψ h []) (hwp : wpPremiseV hlc GF pstep pdone img M ps π Φ Ψ Dd) (P0 : Nat → GSet Nat)
    (hP0 : ∀ h, h < ps.length → ∀ t, t ∈ P0 h ↔ 0 < t ∧ ownTs M h t)
    {k : Nat} {es2 : List (CExprV P Unit V)} {σ2 : CSt}
    (hsteps : NSteps k (esInitV pstep pdone img M ps, σInit ps.length P0) [] (es2, σ2))
    (hall : ∀ t, 1 ≤ t → t ≤ M.length → ¬ Ad.adAt M t → fulAt σ2 t) (hsel : Nat) :
    cFacts π img M Ψ ps.length σ2 ∧
      (hsel < ps.length → ∀ v, es2[hsel]? = some (CExprV.ret v) → ∃ V, grd π img M V (Φ hsel v)) := by
  refine wp_strong_adequacy_gen (hlc := hlc) (GF := GF) Stuckness.MaybeStuck (esInitV pstep pdone img M ps)
    (σInit ps.length P0) k [] es2 σ2 _ (fun _ => 0) ?_ hsteps
  intro Hinv
  iintro
  imod harts_alloc (GF := GF) ps.length (σInit ps.length P0) with ⟨%hn, %hlen, H1, H2⟩
  imod pendsV_alloc (GF := GF) (fun k => Ad.adAt M (k + 1)) M.length with ⟨%mn, %hmlen, Hp, #Hsh⟩
  imod ghost_var_alloc (GF := GF) false with ⟨%dn, Hd⟩
  imod ghost_var_alloc (GF := GF) false with ⟨%fn, Hfn⟩
  imod inv_alloc doomN ⊤ iprop((dpend (GF := GF) ⟨hn, mn, dn, fn, Dd⟩ ∗ dfpend ⟨hn, mn, dn, fn, Dd⟩) ∨
      (dshot ⟨hn, mn, dn, fn, Dd⟩ ∗ ∃ s, ⌜1 ≤ s ∧ s ≤ M.length⌝ ∗ pend ⟨hn, mn, dn, fn, Dd⟩ s ∗
        (dfpend ⟨hn, mn, dn, fn, Dd⟩ ∨ (dfree ⟨hn, mn, dn, fn, Dd⟩ ∗ ⌜(⟨hn, mn, dn, fn, Dd⟩ : AGN).dd s⌝))))
      $$ [Hd Hfn] with #Hdoom
  · inext; ileft; unfold dpend dfpend; iframe Hd Hfn
  ihave #Hdoom' : doomInv (GF := GF) ⟨hn, mn, dn, fn, Dd⟩ M $$ []
  · unfold doomInv; iexact Hdoom
  -- the A/D shots
  ihave #Hads : (∀ t, ⌜1 ≤ t ∧ t ≤ M.length ∧ Ad.adAt M t⌝ → shot (GF := GF) ⟨hn, mn, dn, fn, Dd⟩ t) $$ []
  · iintro %t %ht
    have hj : mn[t - 1]? = some mn[t - 1] := List.getElem?_eq_getElem (by omega)
    have hat' : Ad.adAt M (t - 1 + 1) := by rw [Nat.sub_add_cancel ht.1]; exact ht.2.2
    ihave H := BigSepL.bigSepL_lookup (Φ := fun k γ => iprop(∀ (_h : Ad.adAt M (k + 1)),
      ghost_var (GF := GF) γ .discard true)) hj $$ Hsh
    unfold shot
    dsimp only
    rw [getD_of_get? hj]
    iapply H $$ %hat'
  have hwp' := @hwp Hinv ⟨hn, mn, dn, fn, Dd⟩ P0 hlen hmlen rfl hP0
  ihave Hw := hwp'
  imod Hw $$ Hdoom' [H2] [Hp] with Hwps
  · iapply BigSepL.bigSepL_mono (Φ := fun k γ => ghost_var (GF := GF) γ (.own (1 : Qp).half) (σInit ps.length P0 k))
      ?_ $$ H2
    intro j γ hj
    have hjl : j < hn.length := (List.getElem?_eq_some_iff.1 hj).1
    have hjp : j < ps.length := by rw [← hlen]; exact hjl
    unfold hartA
    iintro H
    isplitr
    · ipureintro; exact hjl
    · simp only [σInit, if_pos hjp]
      rw [getD_of_get? hj]; iexact H
  · iapply BigSepL.bigSepL_mono (Φ := fun k γ => iprop(⌜¬ Ad.adAt M (k + 1)⌝ -∗ ghost_var (GF := GF) γ (.own 1) false))
      ?_ $$ Hp
    intro j γ hj
    unfold pend
    simp only [Nat.add_sub_cancel]
    rw [getD_of_get? hj]
  imodintro
  iexists (fun σ _ _ _ => stAV (GF := GF) ⟨hn, mn, dn, fn, Dd⟩ π img M Ψ σ),
    (List.range ps.length).map (fun k => fun v => iprop(⌜∃ V, grd π img M V (Φ k v)⌝ ∨
      dshot (GF := GF) ⟨hn, mn, dn, fn, Dd⟩)),
    (fun _ => iprop(True)), (fun _ _ _ _ => fupd_intro)
  dsimp only
  isplitl [H1]
  · -- the initial state interpretation
    unfold stAV
    iframe H1
    isplitr
    · ipureintro
      intro j hj
      dsimp only at hj
      have hj' : ¬ j < ps.length := by omega
      simp only [σInit, if_neg hj']
    isplitr
    · ipureintro
      intro j t h1 _ h3 _
      have : wfr (σInit ps.length P0 j).1 = 0 := by
        unfold σInit; split <;> rfl
      omega
    isplitr
    · imodintro
      iintro %t %ht
      rcases ht.2.2 with ⟨j, e, he, _⟩ | hat
      · exfalso; unfold σInit at he; split at he <;> cases he
      · unfold fulT; ileft; iapply Hads; ipureintro; exact ⟨ht.1, ht.2.1, hat⟩
    isplitr
    · ipureintro; exact ⟨had, hex⟩
    · ileft; ipureintro
      refine ⟨himg, fun j hj0 => ?_⟩
      have hj : j < ps.length := by dsimp only at hj0; omega
      refine ⟨fun _ => ⟨0, fun _ => ?_⟩, ?_, ?_, ?_⟩
      · simp only [σInit, if_pos hj, List.take_nil]; exact hΨ0 j
      · simp only [σInit, if_pos hj]; intro e he; cases he
      · simp only [σInit, if_pos hj]; exact Nat.le_refl _
      · simp only [σInit, if_pos hj]
        intro a tf vf h
        rw [show psInit.wFwd = ∅ from rfl, lookupEmpty] at h; cases h
  isplitl [Hwps]
  · -- the thread pool's wps
    unfold esInitV
    iapply bsl2_map (E := fun k => CExprV.run (hwV pstep pdone img M k) (ps.getD k default))
      (Q := fun k => fun v => iprop(⌜∃ V, grd π img M V (Φ k v)⌝ ∨ dshot (GF := GF) ⟨hn, mn, dn, fn, Dd⟩))
    iapply BigSepL.bigSepL_mono (Φ := fun j _ => wpAV (GF := GF) ⟨hn, mn, dn, fn, Dd⟩ π (hwV pstep pdone img M j) Ψ
      (ps.getD j default) (fun v => iprop(⌜∃ V, grd π img M V (Φ j v)⌝ ∨ dshot (GF := GF) ⟨hn, mn, dn, fn, Dd⟩))) ?_
    · intro j i hj
      have : i = j := by
        have hjl := (List.getElem?_eq_some_iff.1 hj).1
        rw [List.length_range] at hjl
        simp only [List.getElem?_range hjl, Option.some.injEq] at hj
        exact hj.symm
      subst this
      dsimp only [wpAV]
      exact .rfl
    iapply bsl_len ps (List.range ps.length) _ (by simp)
    iapply BigSepL.bigSepL_mono (Φ := fun j p => wpAV (GF := GF) ⟨hn, mn, dn, fn, Dd⟩ π (hwV pstep pdone img M j) Ψ p
      (fun v => iprop(⌜∃ V, grd π img M V (Φ j v)⌝ ∨ dshot (GF := GF) ⟨hn, mn, dn, fn, Dd⟩))) ?_ $$ Hwps
    intro j p hj
    rw [List.getD_eq_getElem?_getD, hj]
    exact .rfl
  -- the end
  iintro %es' %t2' %Heq %Hlen %_ Hσ Hpost _
  unfold stAV
  icases Hσ with ⟨_, %Hout, %Hok, #Hshots, %Had, #Hfacts⟩
  imod inv_acc_timeless (E := ⊤) CoPset.subseteq_top $$ Hdoom with ⟨Hb, -⟩
  iapply fupd_mask_intro_discard Std.LawfulSet.empty_subset
  icases Hb with (⟨Hd, Hdf⟩ | ⟨Hds, %s, %hs, Hps, Hmode⟩)
  · icases Hfacts with (%Hf | #Hds)
    · have Hf' : cFacts π img M Ψ ps.length σ2 := by have := Hf; simp only at this; rw [hlen] at this; exact this
      by_cases hs : hsel < ps.length
      · cases hq : es2[hsel]? with
        | none => ipureintro; exact ⟨Hf', fun _ v hv => by cases hv⟩
        | some e =>
          cases e with
          | run w0 s0 => ipureintro; exact ⟨Hf', fun _ v hv => by cases hv⟩
          | ret v =>
            have h1 : es'[hsel]? = some (CExprV.ret v) := by
              rw [Heq, List.getElem?_append_left (by rw [Hlen]; simp [esInitV]; exact hs)] at hq; exact hq
            have h2 : ((List.range ps.length).map (fun k => fun v => iprop(⌜∃ V, grd π img M V (Φ k v)⌝ ∨
                dshot (GF := GF) ⟨hn, mn, dn, fn, Dd⟩)))[hsel]? =
                some (fun v => iprop(⌜∃ V, grd π img M V (Φ hsel v)⌝ ∨ dshot (GF := GF) ⟨hn, mn, dn, fn, Dd⟩)) := by
              rw [List.getElem?_map, List.getElem?_range hs]; rfl
            ihave Hp := BigSepL2.bigSepL2_lookup h1 h2 $$ Hpost
            dsimp only [ToVal.toVal, CExprV.toV, Option.elim]
            icases Hp with (%Hg | #Hds)
            · ipureintro
              exact ⟨Hf', fun _ v' hv' => by cases hv'; exact Hg⟩
            · iexfalso
              iapply dpend_dshot
              iframe Hd Hds
      · ipureintro; exact ⟨Hf', fun h => absurd h hs⟩
    · iexfalso
      iapply dpend_dshot
      iframe Hd Hds
  · iexfalso
    ihave #Hfs := Hshots $$ %s %⟨hs.1, hs.2, by
      by_cases hat : Ad.adAt M s
      · exact .inr hat
      · exact .inl (hall s hs.1 hs.2 hat)⟩
    unfold fulT
    icases Hfs with (#Hsh | ⟨#Hfr, %hnd⟩)
    · iapply pend_shot
      iframe Hps Hsh
    · icases Hmode with (Hdf | ⟨_, %hdd⟩)
      · iapply dfpend_dfree; iframe Hdf Hfr
      · exact absurd hdd hnd

end core

/-! ## 4. The concurrent adequacy over the variant -/

section main

variable {GF : BundledGFunctors} [InvGpreS GF] [GhostVarG GF HSt] [GhostVarG GF Bool]

/-- **THE CONCURRENT ADEQUACY OF TRACK (a) OVER THE A/D VARIANT** (plan §2 [R2.s11], §3 rev 5; header).  Exports:
(i) termination, (ii) the trace part at every prefix of every hart's v2 trace, (iii) the non-A/D partition,
(vi) `adExactV`, (iv) `Valid`. -/
theorem adequacyAV [Inhabited P] {pstep : P → Unit → Ad.VLabel → P → Unit → Prop} {pdone : P → Option V}
    {img : Image} {ps : List P} {M : List PMsg} {evs : List Ad.VEvt} {cfg : PCfg P Unit}
    (π : Proto) (Φ : Nat → V → Prop) (Ψ : Nat → Trace → Prop) (Dd : Nat → Prop) :
    PO_img π img → PO_adV π img M → adEmit pstep →
    (∀ h, Ψ h []) →
    wpPremiseV hlc GF pstep pdone img M ps π Φ Ψ Dd →
    Ad.validRunV pstep img () ps evs cfg → cfg.pcLog = M →
      (∀ h ag v, cfg.pcAgs[h]? = some ag → pdone ag.paSt = some v → Φ h v)
    ∧ (∀ h k, Ψ h ((prjT (Ad.traceOfV h evs)).take k))
    ∧ (∀ t, 1 ≤ t → t ≤ M.length → ¬ Ad.adAt M t →
        ∃ h, h < ps.length ∧ ∃ l, (Ad.VLabel.v l, some t) ∈ Ad.traceOfV h evs)
    ∧ adExactV img M
    ∧ Valid π img M M.length := by
  intro himg had hemit hΨ0 hwp hv hM
  have hlen := validRunV_len hv
  have hex : adExactV img M := hM ▸ adExactV_of_run hemit hv
  have hpart : ∀ t, 1 ≤ t → t ≤ M.length → ¬ Ad.adAt M t →
      ∃ h, h < ps.length ∧ ∃ l, (Ad.VLabel.v l, some t) ∈ Ad.traceOfV h evs := by
    intro t h1 h2 hna
    obtain ⟨i, hi, z, l, p', ws', prom', _, hm, hmem⟩ := validRunV_fulfil hv t h1 (by rw [hM]; exact h2)
    cases l with
    | v l0 => exact ⟨i, hi, l0, hmem⟩
    | ad b tvs d => exact absurd (hM ▸ memStepV_ad_at hm) hna
  -- every hart's solo run (chosen)
  have hexs : ∀ h, ∃ q : PAgent P × GSet Nat, h < ps.length → cfg.pcAgs[h]? = some q.1 ∧
      (∀ t, t ∈ q.2 ↔ 0 < t ∧ ownTs M h t) ∧
      Ad.soloQV pstep img M h Ad.QTV (ps.getD h default, psInit, q.2) (Ad.traceOfV h evs)
        (q.1.paSt, q.1.paWs, q.1.paProm) := by
    intro h
    by_cases hh : h < ps.length
    · obtain ⟨ag, hag, P0, hP0, hs⟩ := Ad.validRunV_solo hv h (ps.getD h default)
        (by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hh]; rfl)
      rw [hM] at hP0 hs
      exact ⟨(ag, P0), fun _ => ⟨hag, hP0, hs⟩⟩
    · exact ⟨(⟨default, psInit, ∅⟩, ∅), fun h' => absurd h' hh⟩
  let Q := fun h => Classical.choose (hexs h)
  have hQ : ∀ h, h < ps.length → _ := fun h => Classical.choose_spec (hexs h)
  let x : Nat → P × PState × GSet Nat := fun h => (ps.getD h default, psInit, (Q h).2)
  let y : Nat → P × PState × GSet Nat := fun h => ((Q h).1.paSt, (Q h).1.paWs, (Q h).1.paProm)
  let tr : Nat → List (Ad.VLabel × Option Nat) := fun h => Ad.traceOfV h evs
  obtain ⟨k, hk⟩ := schedV (pdone := pdone) ps.length x y tr (fun h hh => (hQ h hh).2.2) hpart
  have hσ2 : ∀ h, h < ps.length → ((cfgOfV pstep pdone img M ps.length y tr).2 h).2.2 = prjT (Ad.traceOfV h evs) := by
    intro h hh; simp [cfgOfV, hh, tr]
  have hall : ∀ t, 1 ≤ t → t ≤ M.length → ¬ Ad.adAt M t → fulAt (cfgOfV pstep pdone img M ps.length y tr).2 t := by
    intro t h1 h2 hna
    obtain ⟨h, hh, l, he⟩ := hpart t h1 h2 hna
    exact ⟨h, (l, some t), by rw [hσ2 h hh]; exact prjT_mem he, rfl⟩
  have hout : ∀ j, ps.length ≤ j → ((cfgOfV pstep pdone img M ps.length y tr).2 j).2.2 = [] := by
    intro j hj; simp [cfgOfV, show ¬ j < ps.length by omega]
  have hk0 : NSteps k (esInitV pstep pdone img M ps, σInit ps.length (fun h => (Q h).2)) []
      (cfgOfV pstep pdone img M ps.length y tr) := hk
  obtain ⟨hF, _⟩ := adeq_coreV (hlc := hlc) (GF := GF) himg had hex hΨ0 hwp (fun h => (Q h).2)
    (fun h hh => (hQ h hh).2.1) hk0 hall 0
  have hValid := valid_finV hF hout hall had hex
  refine ⟨fun h ag v hag hdv => ?_, fun h j => ?_, hpart, hex, hValid⟩
  · -- (i)
    have hh : h < ps.length := by
      rw [← hlen]; exact (List.getElem?_eq_some_iff.1 hag).1
    have hq1 : (Q h).1 = ag := (Option.some.inj (hag.symm.trans (hQ h hh).1)).symm
    have hfin : cstepV (CExprV.run (hwV pstep pdone img M h) (y h).1,
        (cfgOfV pstep pdone img M ps.length y tr).2) []
        (CExprV.ret v, (cfgOfV pstep pdone img M ps.length y tr).2, []) :=
      .fin _ _ _ v (by show pdone (Q h).1.paSt = some v; rw [hq1]; exact hdv)
    obtain ⟨t₁, t₂, h1, h2⟩ := map_range_split (fun j => CExprV.run (hwV pstep pdone img M j) (y j).1)
      (fun j => if j = h then CExprV.ret v else CExprV.run (hwV pstep pdone img M j) (y j).1) h
      (fun j hj => by simp [hj]) ps.length hh
    have hS := Language.Step.atomic (Λ := (inferInstance : Language (CExprV P Unit V) CSt Unit V)) hfin t₁ t₂
    simp only [List.append_nil] at hS
    have e1 : cfgOfV pstep pdone img M ps.length y tr =
        (t₁ ++ CExprV.run (hwV pstep pdone img M h) (y h).1 :: t₂,
          (cfgOfV pstep pdone img M ps.length y tr).2) := by
      rw [← h1]; rfl
    rw [← e1] at hS
    have hk1 := nsteps_snoc hk0 hS
    have hsel : (t₁ ++ CExprV.ret v :: t₂)[h]? = some (CExprV.ret v) := by
      have := congrArg (fun l => l[h]?) h2
      simp only at this
      rw [List.getElem?_map, List.getElem?_range hh] at this
      simp only [Option.map_some, if_true] at this
      exact this.symm.trans (by rfl) |>.symm ▸ rfl
    obtain ⟨_, hfv⟩ := adeq_coreV (hlc := hlc) (GF := GF) himg had hex hΨ0 hwp (fun h => (Q h).2)
      (fun h hh => (hQ h hh).2.1) hk1 hall h
    obtain ⟨V', hg⟩ := hfv hh v hsel
    exact grd_elim hValid hg
  · -- (ii)
    by_cases hh : h < ps.length
    · obtain ⟨V', hg⟩ := (hF.2 h hh).1 j
      dsimp only at hg
      simp only [if_pos hh] at hg
      exact grd_elim hValid hg
    · rw [(Ad.pmStepsV_inv hv.1).2.2.2 h (by simp [pmInit]; omega)]
      simpa [prjT] using hΨ0 h

end main

end Weak.Prom.OAd

#print axioms Weak.Prom.OAd.adequacyAV
