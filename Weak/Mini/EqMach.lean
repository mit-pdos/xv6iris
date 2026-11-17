/-
Weak/Mini: **E2 — MiniMach is machine v2 on F** (mini plan rev 4 §2 L2, E2a/E2b; K7: an a/b pair).

With `P.xs` (EqProg.lean: `P.harts.map (·.map (XI.i ∘ MI.toInstr))`), `embM` (messages), `embRun` (events; the final
configuration is the one the embedded events reach), for every well-formed F program `P` and every condition `cond`:
* `e2a : miniValidRun P Mm r ↔ PF.validRun (xStep P.xs) (testImg (P.toTest cond)) () (progs (P.toTest cond))
    (embM P Mm) (embRun P cond r)`;
* `e2b : PF.validRun (xStep P.xs) … M run → untorn run → ∃ Mm r, M = embM P Mm ∧ miniValidRun P Mm r ∧
    ∀ h, run.trace h = (r.trace h).map (embTr P)` — `untorn` exactly as plan §2 L2 (CoreDefs.lean:52, :66–71): the
  mini machine is STRONGER than machine v2 exactly on torn runs (finding F3, Weak/Prom/MachTornWit.lean; owner
  ruling [OWN.P19]);
* corollaries `e2a_obsLoad`, `e2b_obsLoad`: equal load observations.
Proof: simulations both ways under `Rel` (`RelWs` carries the inertness invariant), after a first pass (`pass1`) that
shows every message of a valid run is an aligned word write (every promise is fulfilled, and on F only by a plain
aligned store).
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Mini.EqMachMem

namespace MiniEq

open MachCSL MachCSL.Stdpp Iris.Std
open Weak.Prom Weak.Prom.Mach Weak.Prom.Mach.Cert Weak.Prom.OA
open Weak.Mini
open PLabel

/-! ## 1. Embeddings of events, runs, memories -/

def embEv (P : MProg) : Mach.MEvt → PEvt
  | .prom i m => .prom i (embMsg P m)
  | .st i l ots => .st i (embL P l) ots

/-- A mini trace entry as a machine v2 trace entry. -/
def embTr (P : MProg) (e : Mach.MLab × Option Nat) : PF.PEv := (embL P e.1, e.2)

/-- A mini final memory as a machine v2 final memory. -/
def embM (P : MProg) (Mm : List Mach.MMsg) : List PMsg := Mm.map (embMsg P)

/-- Machine v2's initial configuration for `P`. -/
def fInit (P : MProg) (cond : Weak.Prom.Ref.OC) : PCfg LP Unit :=
  pmInit (testImg (P.toTest cond)) () (progs (P.toTest cond))

open Classical in
/-- A mini run as a machine v2 run: the embedded events, and the configuration they reach (if any; machine v2 is
deterministic on them, see `e2a`). -/
noncomputable def embRun (P : MProg) (cond : Weak.Prom.Ref.OC) (r : Mach.MRun) : PF.PFRun LP Unit :=
  ⟨r.evs.map (embEv P),
   if h : ∃ C, pmSteps (xStep P.xs) (fInit P cond) (r.evs.map (embEv P)) C then Classical.choose h else fInit P cond⟩

/-- UNTORN RUN (mini plan rev 4 §2 L2, verbatim): every load-like trace entry's answers share one timestamp. -/
def untorn {Q D : Type} (run : PF.PFRun Q D) : Prop :=
  ∀ h, ∀ e ∈ run.trace h, ∀ tvs, PF.loadLikeTvs e.1 = some tvs → ∀ p ∈ tvs, ∀ q ∈ tvs, p.1 = q.1

def untornE : PEvt → Prop
  | .prom .. => True
  | .st _ l _ => untornL l

/-! ## 2. The configuration relation -/

structure RelAg (P : MProg) (i : Nat) (h : Mach.MHart) (ag : PAgent LP) : Prop where
  st : ag.paSt = embF P i h.fr
  q : qOk h.fr.q
  ws : RelWs P h.ws ag.paWs
  prom : ∀ t, t ∈ ag.paProm ↔ t ∈ h.prom

structure Rel (P : MProg) (cond : Weak.Prom.Ref.OC) (c : Mach.MCfg) (C : PCfg LP Unit) : Prop where
  img : C.pcImg = testImg (P.toTest cond)
  log : C.pcLog = c.log.map (embMsg P)
  good : ∀ m ∈ c.log, goodM P m
  len : C.pcAgs.length = c.hs.length
  hlen : c.hs.length = P.harts.length
  ags : ∀ i h ag, c.hs[i]? = some h → C.pcAgs[i]? = some ag → RelAg P i h ag

theorem ags_set {P : MProg} {hs : List Mach.MHart} {ags : List (PAgent LP)} (hlen : ags.length = hs.length)
    (hags : ∀ j h ag, hs[j]? = some h → ags[j]? = some ag → RelAg P j h ag) {i : Nat} {h' : Mach.MHart}
    {ag' : PAgent LP} (hi : i < hs.length) (hrel : RelAg P i h' ag') :
    ∀ j h ag, (hs.set i h')[j]? = some h → (ags.set i ag')[j]? = some ag → RelAg P j h ag := by
  intro j h ag h1 h2
  rw [List.getElem?_set] at h1 h2
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl, if_pos hi] at h1
    rw [if_pos rfl, if_pos (by omega)] at h2
    cases h1; cases h2; exact hrel
  · rw [if_neg hij] at h1 h2; exact hags j h ag h1 h2

theorem agent_of {P : MProg} {cond : Weak.Prom.Ref.OC} {c : Mach.MCfg} {C : PCfg LP Unit} (hR : Rel P cond c C)
    {i : Nat} {h : Mach.MHart} (hh : c.hs[i]? = some h) : ∃ ag, C.pcAgs[i]? = some ag ∧ RelAg P i h ag := by
  have hi : i < c.hs.length := (List.getElem?_eq_some_iff.1 hh).1
  refine ⟨C.pcAgs[i]'(by rw [hR.len]; exact hi), List.getElem?_eq_getElem _, ?_⟩
  exact hR.ags i h _ hh (List.getElem?_eq_getElem _)

theorem hart_of {P : MProg} {cond : Weak.Prom.Ref.OC} {c : Mach.MCfg} {C : PCfg LP Unit} (hR : Rel P cond c C)
    {i : Nat} {ag : PAgent LP} (hag : C.pcAgs[i]? = some ag) : ∃ h, c.hs[i]? = some h ∧ RelAg P i h ag := by
  have hi : i < C.pcAgs.length := (List.getElem?_eq_some_iff.1 hag).1
  refine ⟨c.hs[i]'(by rw [← hR.len]; exact hi), List.getElem?_eq_getElem _, ?_⟩
  exact hR.ags i _ ag (List.getElem?_eq_getElem _) hag

theorem progs_get (P : MProg) (cond : Weak.Prom.Ref.OC) {i : Nat} (hi : i < P.harts.length) :
    (progs (P.toTest cond))[i]? = some (embF P i ⟨0, (List.range 32).map (fun r => P.reg0 i r % Mach.two64), []⟩) := by
  have hi' : i < (P.toTest cond).harts.length := by simpa [MProg.toTest] using hi
  simp only [progs, List.getElem?_map, List.getElem?_range hi', Option.map_some, embF, progF_eq, List.map_nil]
  rfl

theorem progs_len (P : MProg) (cond : Weak.Prom.Ref.OC) : (progs (P.toTest cond)).length = P.harts.length := by
  simp [progs, MProg.toTest]

theorem minit_get (P : MProg) {i : Nat} {h : Mach.MHart} (hh : (Mach.mInit P).hs[i]? = some h) :
    i < P.harts.length ∧ h = ⟨⟨0, (List.range 32).map (fun r => P.reg0 i r % Mach.two64), []⟩, Mach.msInit, []⟩ := by
  simp only [Mach.mInit, List.getElem?_map] at hh
  by_cases hi : i < P.harts.length
  · rw [List.getElem?_range hi] at hh; cases hh; exact ⟨hi, rfl⟩
  · rw [List.getElem?_eq_none (by simpa using hi)] at hh; cases hh

theorem finit_get (P : MProg) (cond : Weak.Prom.Ref.OC) {i : Nat} {ag : PAgent LP}
    (hag : (fInit P cond).pcAgs[i]? = some ag) :
    i < P.harts.length ∧ ag = ⟨embF P i ⟨0, (List.range 32).map (fun r => P.reg0 i r % Mach.two64), []⟩, psInit, ∅⟩ := by
  simp only [fInit, pmInit, List.getElem?_map] at hag
  by_cases hi : i < P.harts.length
  · rw [progs_get P cond hi] at hag; cases hag; exact ⟨hi, rfl⟩
  · rw [List.getElem?_eq_none (by rw [progs_len]; omega)] at hag; cases hag

theorem rel_init (P : MProg) (cond : Weak.Prom.Ref.OC) : Rel P cond (Mach.mInit P) (fInit P cond) := by
  refine ⟨rfl, rfl, (fun m hm => nomatch hm), ?_, by simp [Mach.mInit], fun i h ag hh hag => ?_⟩
  · simp [fInit, pmInit, progs_len, Mach.mInit]
  · obtain ⟨-, rfl⟩ := minit_get P hh
    obtain ⟨-, rfl⟩ := finit_get P cond hag
    exact ⟨rfl, qOk_nil, relWs_init P, fun t => by simp [elemOfEmpty]⟩

/-! ## 3. One step, both ways -/

theorem wordB_good {P : MProg} (hwf : Mach.progWf P) {m : Mach.MMsg} : (embMsg P m).data ≠ [] :=
  wordB_ne_nil hwf.1 m.v

theorem step_fwd (P : MProg) (hwf : Mach.progWf P) (cond : Weak.Prom.Ref.OC) {c c' : Mach.MCfg} {e : Mach.MEvt}
    (hs : Mach.mStep P c e c') {C : PCfg LP Unit} (hR : Rel P cond c C) :
    ∃ C', pmStep (xStep P.xs) C (embEv P e) C' ∧ Rel P cond c' C' := by
  cases hs with
  | promise i h m hh htid hpa hv =>
    obtain ⟨ag, hag, hra⟩ := agent_of hR hh
    have hi : i < c.hs.length := (List.getElem?_eq_some_iff.1 hh).1
    refine ⟨_, .promise C i ag (embMsg P m) hag (.inl (wordB_good hwf)) (by simp [embMsg, htid]), ?_⟩
    have hll : C.pcLog.length = c.log.length := by rw [hR.log, List.length_map]
    refine ⟨hR.img, by simp [hR.log, embMsg], fun m' hm' => ?_, by simp [hR.len], by simp [hR.hlen],
      ags_set hR.len hR.ags hi ⟨hra.st, hra.q, hra.ws, fun t => ?_⟩⟩
    · rcases List.mem_append.1 hm' with h1 | h1
      · exact hR.good m' h1
      · simp at h1; subst h1; exact ⟨hpa, hv⟩
    · rw [elemOfUnion, elemOfSingleton, hra.prom, hll]; simp
  | state i h l ots fr' ws' prom' hh hn hm =>
    obtain ⟨ag, hag, hra⟩ := agent_of hR hh
    have hi : i < c.hs.length := (List.getElem?_eq_some_iff.1 hh).1
    have hiP : i < P.harts.length := hR.hlen ▸ hi
    obtain ⟨hq', hlab⟩ := mNext_ok hra.q hn
    obtain ⟨ws'', prom'', hmf, hrw, hrp⟩ := mem_fwd P hwf cond hm hlab hR.good hra.ws hra.prom
    have hx : xNext P.xs ag.paSt (embL P l) = some (embF P i fr') := by
      rw [hra.st, xNext_emb P hwf hiP, hn]; rfl
    refine ⟨_, .state C i ag (embL P l) ots (embF P i fr') () ws'' prom'' hag hx
      (by rw [hR.img, hR.log]; exact hmf), ?_⟩
    exact ⟨hR.img, hR.log, hR.good, by simp [hR.len], by simp [hR.hlen],
      ags_set hR.len hR.ags hi ⟨rfl, hq', hrw, hrp⟩⟩

theorem step_bwd (P : MProg) (hwf : Mach.progWf P) (cond : Weak.Prom.Ref.OC) {C C' : PCfg LP Unit} {e : PEvt}
    (hs : pmStep (xStep P.xs) C e C') {c : Mach.MCfg} (hR : Rel P cond c C) (hg : ∀ m ∈ C'.pcLog, good P m)
    (hu : untornE e) : ∃ me c', e = embEv P me ∧ Mach.mStep P c me c' ∧ Rel P cond c' C' := by
  cases hs with
  | promise i ag m hag hne htid =>
    obtain ⟨h, hh, hra⟩ := hart_of hR hag
    have hi : i < c.hs.length := (List.getElem?_eq_some_iff.1 hh).1
    obtain ⟨mm, rfl, hmg⟩ := hg m (List.mem_append_right _ (List.mem_singleton_self _))
    have htid' : mm.tid = i := by simpa [embMsg] using htid
    refine ⟨.prom i mm, _, rfl, .promise c i h mm hh htid' hmg.1 hmg.2, ?_⟩
    have hll : C.pcLog.length = c.log.length := by rw [hR.log, List.length_map]
    refine ⟨hR.img, by simp [hR.log], fun m' hm' => ?_, by simp [hR.len], by simp [hR.hlen],
      ags_set hR.len hR.ags hi ⟨hra.st, hra.q, hra.ws, fun t => ?_⟩⟩
    · rcases List.mem_append.1 hm' with h1 | h1
      · exact hR.good m' h1
      · simp at h1; subst h1; exact hmg
    · rw [elemOfUnion, elemOfSingleton, hra.prom, hll]; simp
  | state i ag l ots st' d' ws' prom' hag hx hm =>
    obtain ⟨h, hh, hra⟩ := hart_of hR hag
    have hi : i < c.hs.length := (List.getElem?_eq_some_iff.1 hh).1
    have hiP : i < P.harts.length := hR.hlen ▸ hi
    have hx' : xNext P.xs (embF P i h.fr) l = some st' := by rw [← hra.st]; exact hx
    obtain ⟨ml, rfl⟩ := xNext_image P hwf hiP h.fr hx' hu
    rw [xNext_emb P hwf hiP] at hx'
    obtain ⟨fr', hn, rfl⟩ := Option.map_eq_some_iff.1 hx'
    obtain ⟨hq', hlab⟩ := mNext_ok hra.q hn
    rw [hR.img, hR.log] at hm
    obtain ⟨ms', mprom', hmm, hrw, hrp⟩ := mem_bwd P hwf cond hm hlab hR.good hra.ws hra.prom
    refine ⟨.st i ml ots, _, rfl, .state c i h ml ots fr' ms' mprom' hh hn hmm, ?_⟩
    exact ⟨hR.img, hR.log, hR.good, by simp [hR.len], by simp [hR.hlen],
      ags_set hR.len hR.ags hi ⟨rfl, hq', hrw, hrp⟩⟩

/-! ## 4. Runs -/

theorem pmSteps_log {Xs : List (List XI)} {C C' : PCfg LP Unit} {es : List PEvt} (hs : pmSteps (xStep Xs) C es C') :
    ∀ m ∈ C.pcLog, m ∈ C'.pcLog := by
  induction hs with
  | refl => exact fun m hm => hm
  | step c0 c1 c2 e es h1 _ ih =>
    intro m hm
    apply ih
    cases h1 with
    | promise => exact List.mem_append_left _ hm
    | state => exact hm

/-- The promises of an event list. -/
def promsOf : List PEvt → List PMsg
  | [] => []
  | .prom _ m :: es => m :: promsOf es
  | .st .. :: es => promsOf es

theorem pmSteps_logEq {Xs : List (List XI)} {C C' : PCfg LP Unit} {es : List PEvt}
    (hs : pmSteps (xStep Xs) C es C') : C'.pcLog = C.pcLog ++ promsOf es := by
  induction hs with
  | refl => simp [promsOf]
  | step c0 c1 c2 e es h1 _ ih =>
    rw [ih]
    cases h1 with
    | promise => simp [promsOf]
    | state => simp [promsOf]

theorem run_fwd (P : MProg) (hwf : Mach.progWf P) (cond : Weak.Prom.Ref.OC) {c0 c : Mach.MCfg} {es : List Mach.MEvt}
    (hs : Mach.mSteps P c0 es c) : ∀ {C0 : PCfg LP Unit}, Rel P cond c0 C0 →
      ∃ C, pmSteps (xStep P.xs) C0 (es.map (embEv P)) C ∧ Rel P cond c C := by
  induction hs with
  | refl c => exact fun hR => ⟨_, .refl _, hR⟩
  | step c0 c1 c2 e es h1 _ ih =>
    intro C0 hR
    obtain ⟨C1, hC1, hR1⟩ := step_fwd P hwf cond h1 hR
    obtain ⟨C2, hC2, hR2⟩ := ih hR1
    exact ⟨C2, .step _ _ _ _ _ hC1 hC2, hR2⟩

theorem run_bwd (P : MProg) (hwf : Mach.progWf P) (cond : Weak.Prom.Ref.OC) {C0 C : PCfg LP Unit} {es : List PEvt}
    (hs : pmSteps (xStep P.xs) C0 es C) (hg : ∀ m ∈ C.pcLog, good P m) (hu : ∀ e ∈ es, untornE e) :
    ∀ {c0 : Mach.MCfg}, Rel P cond c0 C0 →
      ∃ mes c, es = mes.map (embEv P) ∧ Mach.mSteps P c0 mes c ∧ Rel P cond c C := by
  induction hs with
  | refl C => exact fun hR => ⟨[], _, rfl, .refl _, hR⟩
  | step C0 C1 C2 e es h1 h2 ih =>
    intro c0 hR
    obtain ⟨me, c1, rfl, hm1, hR1⟩ :=
      step_bwd P hwf cond h1 hR (fun m hm => hg m (pmSteps_log h2 m hm)) (hu _ (List.mem_cons_self ..))
    obtain ⟨mes, c, rfl, hms, hR2⟩ := ih hg (fun e he => hu e (List.mem_cons_of_mem _ he)) hR1
    exact ⟨me :: mes, c, rfl, .step _ _ _ _ _ hm1 hms, hR2⟩

/-! ## 5. Pass 1: every message of a valid run is an aligned word write -/

theorem memStep_prom_emb {P : MProg} {img : Weak.Image} {log : List PMsg} {i : Nat} {prom : GSet Nat} {ws : PState}
    {ml : Mach.MLab} {ots : Option Nat} {ws' : PState} {prom' : GSet Nat}
    (hm : memStep img log i prom ws (embL P ml) ots ws' prom') :
    prom' = prom ∨ ∃ a v x y ts, ml = .store a v x y ∧ prom' = prom \ {ts} ∧
      log[ts - 1]? = some ⟨(a : Int), wordB P v, some i, .plain⟩ := by
  cases ml with
  | load => simp only [embL] at hm; cases hm; exact .inl rfl
  | store a v x y =>
    simp only [embL] at hm
    cases hm with
    | store _ _ _ _ _ _ ts _ hmsg _ _ => exact .inr ⟨a, v, x, y, ts, rfl, rfl, hmsg⟩
  | fence => simp only [embL] at hm; cases hm; exact .inl rfl
  | regW => simp only [embL] at hm; cases hm; exact .inl rfl
  | ctrl => simp only [embL] at hm; cases hm; exact .inl rfl
  | instr => simp only [embL] at hm; cases hm; exact .inl rfl

/-- THE PASS-1 INVARIANT: every hart runs an embedded mini program state; every message is outstanding or good. -/
def Inv1 (P : MProg) (C : PCfg LP Unit) : Prop :=
  C.pcAgs.length = P.harts.length ∧
  (∀ i ag, C.pcAgs[i]? = some ag → ∃ f, ag.paSt = embF P i f ∧ qOk f.q) ∧
  ∀ t m, C.pcLog[t]? = some m → (∃ (i : Nat) (ag : PAgent LP), C.pcAgs[i]? = some ag ∧ t + 1 ∈ ag.paProm) ∨ good P m

theorem inv1_init (P : MProg) (cond : Weak.Prom.Ref.OC) : Inv1 P (fInit P cond) := by
  refine ⟨by simp [fInit, pmInit, progs_len], fun i ag hag => ?_, fun t m hm => by simp [fInit, pmInit] at hm⟩
  obtain ⟨-, rfl⟩ := finit_get P cond hag
  exact ⟨_, rfl, qOk_nil⟩

theorem inv1_step (P : MProg) (hwf : Mach.progWf P) {C C' : PCfg LP Unit} {e : PEvt}
    (hs : pmStep (xStep P.xs) C e C') (hI : Inv1 P C) (hu : untornE e) : Inv1 P C' := by
  obtain ⟨hlen, hst, hlog⟩ := hI
  cases hs with
  | promise i ag m hag _ _ =>
    have hi : i < C.pcAgs.length := (List.getElem?_eq_some_iff.1 hag).1
    refine ⟨by simp [hlen], fun j ag' hj => ?_, fun t m' hm => ?_⟩
    · rw [List.getElem?_set] at hj
      by_cases hij : i = j
      · subst hij; rw [if_pos rfl, if_pos hi] at hj; cases hj; exact hst i ag hag
      · rw [if_neg hij] at hj; exact hst j ag' hj
    · simp only at hm
      rw [List.getElem?_append] at hm
      split at hm
      · rcases hlog t m' hm with ⟨j, agj, hj, hjt⟩ | hg
        · left
          by_cases hij : i = j
          · subst hij
            rw [hag] at hj; cases hj
            exact ⟨i, _, by rw [List.getElem?_set_self hi], elemOfUnion.2 (.inr hjt)⟩
          · exact ⟨j, agj, by rw [List.getElem?_set_ne hij]; exact hj, hjt⟩
        · exact .inr hg
      · next hge =>
        have ht : t = C.pcLog.length := by
          have := (List.getElem?_eq_some_iff.1 hm).1; simp at this; omega
        left
        have hmem : t + 1 ∈ ({C.pcLog.length + 1} ∪ ag.paProm : GSet Nat) :=
          elemOfUnion.2 (.inl (elemOfSingleton.2 (by omega)))
        exact ⟨i, ⟨ag.paSt, ag.paWs, {C.pcLog.length + 1} ∪ ag.paProm⟩, by rw [List.getElem?_set_self hi], hmem⟩
  | state i ag l ots st' d' ws' prom' hag hx hm =>
    have hi : i < C.pcAgs.length := (List.getElem?_eq_some_iff.1 hag).1
    have hiP : i < P.harts.length := hlen ▸ hi
    obtain ⟨f, hf, hq⟩ := hst i ag hag
    have hx' : xNext P.xs (embF P i f) l = some st' := by rw [← hf]; exact hx
    obtain ⟨ml, rfl⟩ := xNext_image P hwf hiP f hx' hu
    rw [xNext_emb P hwf hiP] at hx'
    obtain ⟨fr', hn, rfl⟩ := Option.map_eq_some_iff.1 hx'
    obtain ⟨hq', hlab⟩ := mNext_ok hq hn
    refine ⟨by simp [hlen], fun j ag' hj => ?_, fun t m' hm' => ?_⟩
    · rw [List.getElem?_set] at hj
      by_cases hij : i = j
      · subst hij; rw [if_pos rfl, if_pos hi] at hj; cases hj; exact ⟨fr', rfl, hq'⟩
      · rw [if_neg hij] at hj; exact hst j ag' hj
    · rcases hlog t m' hm' with ⟨j, agj, hj, hjt⟩ | hg
      · by_cases hij : i = j
        · subst hij
          rw [hag] at hj; cases hj
          rcases memStep_prom_emb hm with rfl | ⟨a, v, x, y, ts, rfl, rfl, hmsg⟩
          · exact .inl ⟨i, ⟨embF P i fr', ws', ag.paProm⟩, by rw [List.getElem?_set_self hi], hjt⟩
          · by_cases hts : t + 1 = ts
            · subst hts
              simp only [Nat.add_sub_cancel] at hmsg
              rw [hmsg] at hm'; cases hm'
              exact .inr ⟨⟨a, v, i⟩, rfl, hlab⟩
            · have hmem : t + 1 ∈ (ag.paProm \ {ts} : GSet Nat) :=
                elemOfDifference.2 ⟨hjt, fun h => hts (elemOfSingleton.1 h)⟩
              exact .inl ⟨i, ⟨embF P i fr', ws', ag.paProm \ {ts}⟩, by rw [List.getElem?_set_self hi], hmem⟩
        · exact .inl ⟨j, agj, by rw [List.getElem?_set_ne hij]; exact hj, hjt⟩
      · exact .inr hg

theorem inv1_run (P : MProg) (hwf : Mach.progWf P) {C0 C : PCfg LP Unit} {es : List PEvt}
    (hs : pmSteps (xStep P.xs) C0 es C) (hI : Inv1 P C0) (hu : ∀ e ∈ es, untornE e) : Inv1 P C := by
  induction hs with
  | refl => exact hI
  | step c0 c1 c2 e es h1 _ ih =>
    exact ih (inv1_step P hwf h1 hI (hu _ (List.mem_cons_self ..))) (fun e he => hu e (List.mem_cons_of_mem _ he))

/-- PASS 1: in a valid run of an F program, every message is the embedding of an aligned word. -/
theorem pass1 (P : MProg) (hwf : Mach.progWf P) (cond : Weak.Prom.Ref.OC) {es : List PEvt} {C : PCfg LP Unit}
    (hv : Weak.Prom.validRun (xStep P.xs) (testImg (P.toTest cond)) () (progs (P.toTest cond)) es C)
    (hu : ∀ e ∈ es, untornE e) : ∀ m ∈ C.pcLog, good P m := by
  obtain ⟨-, -, hlog⟩ := inv1_run P hwf hv.1 (inv1_init P cond) hu
  intro m hm
  obtain ⟨t, ht⟩ := List.getElem?_of_mem hm
  rcases hlog t m ht with ⟨i, ag, hag, hp⟩ | hg
  · rw [hv.2 i ag hag] at hp; exact absurd hp (elemOfEmpty.1 · |>.elim)
  · exact hg

/-! ## 6. Determinism, injectivity, traces -/

theorem mMem_det {P : MProg} {log : List Mach.MMsg} {i : Nat} {prom : List Nat} {ws : Mach.MSt} {l : Mach.MLab}
    {ots : Option Nat} {ws1 ws2 : Mach.MSt} {p1 p2 : List Nat} (h1 : Mach.mMem P log i prom ws l ots ws1 p1)
    (h2 : Mach.mMem P log i prom ws l ots ws2 p2) : ws1 = ws2 ∧ p1 = p2 := by
  cases h1 <;> cases h2 <;> exact ⟨rfl, rfl⟩

theorem mStep_det {P : MProg} {c c1 c2 : Mach.MCfg} {e : Mach.MEvt} (h1 : Mach.mStep P c e c1)
    (h2 : Mach.mStep P c e c2) : c1 = c2 := by
  cases h1 with
  | promise i h m hh =>
    cases h2 with
    | promise _ h' _ hh' => rw [hh] at hh'; cases hh'; rfl
  | state i h l ots fr ws prom hh hn hm =>
    cases h2 with
    | state _ h' _ _ fr' ws' prom' hh' hn' hm' =>
      rw [hh] at hh'; cases hh'
      rw [hn] at hn'; cases hn'
      obtain ⟨rfl, rfl⟩ := mMem_det hm hm'
      rfl

theorem mSteps_det {P : MProg} {c c1 c2 : Mach.MCfg} {es : List Mach.MEvt} (h1 : Mach.mSteps P c es c1)
    (h2 : Mach.mSteps P c es c2) : c1 = c2 := by
  induction h1 generalizing c2 with
  | refl => cases h2; rfl
  | step c0 ca cb e es s1 _ ih =>
    cases h2 with
    | step _ cb' _ _ _ s2 r2 => rw [mStep_det s1 s2] at *; exact ih r2

theorem embEv_inj {P : MProg} (hsz : 0 < P.sz) {e1 e2 : Mach.MEvt} (h : embEv P e1 = embEv P e2) : e1 = e2 := by
  cases e1 <;> cases e2 <;> simp only [embEv, PEvt.prom.injEq, PEvt.st.injEq, reduceCtorEq] at h
  · rw [h.1, embMsg_inj h.2]
  · rw [h.1, embL_inj hsz h.2.1, h.2.2]

theorem map_inj {α β : Type} {f : α → β} (hf : ∀ a b, f a = f b → a = b) :
    ∀ {l1 l2 : List α}, l1.map f = l2.map f → l1 = l2
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | a :: l1, b :: l2, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    rw [hf a b h.1, map_inj hf h.2]

theorem untornE_emb (P : MProg) (me : Mach.MEvt) : untornE (embEv P me) := by
  cases me with
  | prom => trivial
  | st i l ots =>
    cases l <;> simp only [embEv, untornE, untornL, embL, PF.loadLikeTvs, reduceCtorEq, false_imp_iff,
      implies_true, Option.some.injEq]
    rintro tvs rfl p hp q hq
    simp only [List.mem_map] at hp hq
    obtain ⟨_, -, rfl⟩ := hp; obtain ⟨_, -, rfl⟩ := hq; rfl

theorem traceOf_emb (P : MProg) (h : Nat) :
    ∀ mes : List Mach.MEvt, traceOf h (mes.map (embEv P)) = (Mach.traceOf h mes).map (embTr P)
  | [] => rfl
  | .prom _ _ :: es => by simp only [List.map_cons, embEv, traceOf, Mach.traceOf]; exact traceOf_emb P h es
  | .st i l ots :: es => by
    simp only [List.map_cons, embEv, traceOf, Mach.traceOf]
    split <;> simp [traceOf_emb P h es, embTr]

theorem mem_traceOf {i : Nat} {l : PLabel} {ots : Option Nat} :
    ∀ {es : List PEvt}, PEvt.st i l ots ∈ es → (l, ots) ∈ traceOf i es
  | [], h => nomatch h
  | e :: es, h => by
    rcases List.mem_cons.1 h with rfl | h'
    · simp [traceOf]
    · cases e with
      | prom => simp only [traceOf]; exact mem_traceOf h'
      | st j l' o' => simp only [traceOf]; split <;> simp [mem_traceOf h']

theorem untorn_evs {Q D : Type} {run : PF.PFRun Q D} (hu : untorn run) : ∀ e ∈ run.evs, untornE e := by
  intro e he
  cases e with
  | prom => trivial
  | st i l ots => exact hu i (l, ots) (mem_traceOf he)

/-! ## 7. E2a, E2b -/

theorem noProm_of_rel {P : MProg} {cond : Weak.Prom.Ref.OC} {c : Mach.MCfg} {C : PCfg LP Unit}
    (hR : Rel P cond c C) (hn : noPromises C) : Mach.noProm c := by
  intro i h hh
  obtain ⟨ag, hag, hra⟩ := agent_of hR hh
  rw [List.eq_nil_iff_forall_not_mem]
  intro t ht
  have := (hra.prom t).2 ht
  rw [hn i ag hag] at this
  exact elemOfEmpty.1 this

theorem noPromises_of_rel {P : MProg} {cond : Weak.Prom.Ref.OC} {c : Mach.MCfg} {C : PCfg LP Unit}
    (hR : Rel P cond c C) (hn : Mach.noProm c) : noPromises C := by
  intro i ag hag
  obtain ⟨h, hh, hra⟩ := hart_of hR hag
  rw [setEq]
  intro t
  rw [hra.prom, hn i h hh, elemOfEmpty]; simp

/-- **E2a** (mini plan rev 4 §2 L2): a mini run is valid iff its embedding is a valid run of machine v2 with the
loop front end, with the embedded final memory. -/
theorem e2a (P : MProg) (hwf : Mach.progWf P) (cond : Weak.Prom.Ref.OC) (Mm : List Mach.MMsg) (r : Mach.MRun) :
    Mach.miniValidRun P Mm r ↔
      PF.validRun (xStep P.xs) (testImg (P.toTest cond)) () (progs (P.toTest cond)) (embM P Mm) (embRun P cond r) := by
  constructor
  · rintro ⟨c, hms, hnp, rfl⟩
    obtain ⟨C, hC, hR⟩ := run_fwd P hwf cond hms (rel_init P cond)
    have hex : ∃ C, pmSteps (xStep P.xs) (fInit P cond) (r.evs.map (embEv P)) C := ⟨C, hC⟩
    have hcfg : (embRun P cond r).cfg = Classical.choose hex := by unfold embRun; exact dif_pos hex
    have hC' := Classical.choose_spec hex
    rw [← hcfg] at hC'
    have hlog : (embRun P cond r).cfg.pcLog = C.pcLog := by rw [pmSteps_logEq hC', pmSteps_logEq hC]
    obtain ⟨mes, c', he, hms', hR'⟩ := run_bwd P hwf cond hC'
      (fun m hm => by rw [hlog, hR.log] at hm; obtain ⟨mm, hmm, rfl⟩ := List.mem_map.1 hm; exact ⟨mm, rfl, hR.good mm hmm⟩)
      (fun e he => by obtain ⟨me, -, rfl⟩ := List.mem_map.1 he; exact untornE_emb P me) (rel_init P cond)
    have hmes : mes = r.evs := (map_inj (fun _ _ h => embEv_inj hwf.1 h) he).symm
    subst hmes
    obtain rfl := mSteps_det hms hms'
    exact ⟨⟨hC', noPromises_of_rel hR' hnp⟩, hR'.log⟩
  · rintro ⟨hv, hlog⟩
    have hg := pass1 P hwf cond hv (fun e he => by obtain ⟨me, -, rfl⟩ := List.mem_map.1 he; exact untornE_emb P me)
    obtain ⟨mes, c, he, hms, hR⟩ := run_bwd P hwf cond hv.1 hg
      (fun e he => by obtain ⟨me, -, rfl⟩ := List.mem_map.1 he; exact untornE_emb P me) (rel_init P cond)
    have hmes : mes = r.evs := (map_inj (fun _ _ h => embEv_inj hwf.1 h) he).symm
    subst hmes
    refine ⟨c, hms, noProm_of_rel hR hv.2, ?_⟩
    have := hR.log.symm.trans hlog
    exact map_inj (fun _ _ h => embMsg_inj h) this

/-- **E2b** (mini plan rev 4 §2 L2): every UNTORN valid run of machine v2 with the loop front end on an F program is
the embedding of a valid mini run, with the same final memory and the same traces. -/
theorem e2b (P : MProg) (hwf : Mach.progWf P) (cond : Weak.Prom.Ref.OC) (M : List PMsg) (run : PF.PFRun LP Unit)
    (hv : PF.validRun (xStep P.xs) (testImg (P.toTest cond)) () (progs (P.toTest cond)) M run) (hu : untorn run) :
    ∃ Mm r, M = embM P Mm ∧ Mach.miniValidRun P Mm r ∧ ∀ h, run.trace h = (r.trace h).map (embTr P) := by
  have hue := untorn_evs hu
  have hg := pass1 P hwf cond hv.1 hue
  obtain ⟨mes, c, he, hms, hR⟩ := run_bwd P hwf cond hv.1.1 hg hue (rel_init P cond)
  refine ⟨c.log, ⟨mes⟩, by rw [← hv.2, hR.log]; rfl, ⟨c, hms, noProm_of_rel hR hv.1.2, rfl⟩, fun h => ?_⟩
  show traceOf h run.evs = _
  rw [he, traceOf_emb]
  rfl

/-! ## 8. Corollary: load observations -/

theorem obsOf_map (t : Nat) : ∀ bs : List (BitVec 8), PF.obsOf (bs.map (fun b => (t, b))) = ofBytes bs
  | [] => rfl
  | b :: r => by simp only [List.map_cons, PF.obsOf, List.foldr_cons, ofBytes_cons] at *; rw [← obsOf_map t r]; rfl

theorem loads_emb (P : MProg) :
    ∀ τ : List (Mach.MLab × Option Nat), (PF.loadsOf (τ.map (embTr P))).map PF.obsOf = Mach.loadVals τ
  | [] => rfl
  | (l, o) :: τ => by
    have ih := loads_emb P τ
    cases l with
    | load a t v asrc =>
      show PF.obsOf ((wordB P v).map (fun b => (t, b))) :: (PF.loadsOf (τ.map (embTr P))).map PF.obsOf =
        v :: Mach.loadVals τ
      rw [ih, obsOf_map, ofBytes_wordB]
    | store => exact ih
    | fence => exact ih
    | regW => exact ih
    | ctrl => exact ih
    | instr => exact ih

theorem obsLoad_of_trace {P : MProg} {run : PF.PFRun LP Unit} {r : Mach.MRun}
    (ht : ∀ h, run.trace h = (r.trace h).map (embTr P)) (h k : Nat) : run.obsLoad h k = r.obsLoad h k := by
  simp only [PF.PFRun.obsLoad, Mach.MRun.obsLoad, ht h, ← loads_emb P (r.trace h), List.getElem?_map]

/-- Corollary of E2a: the embedded run has the mini run's load observations. -/
theorem e2a_obsLoad (P : MProg) (cond : Weak.Prom.Ref.OC) (r : Mach.MRun) (h k : Nat) :
    (embRun P cond r).obsLoad h k = r.obsLoad h k :=
  obsLoad_of_trace (P := P) (run := embRun P cond r) (r := r) (fun h => traceOf_emb P h r.evs) h k

/-- Corollary of E2b: an untorn valid run of machine v2 has the load observations of a valid mini run. -/
theorem e2b_obsLoad (P : MProg) (hwf : Mach.progWf P) (cond : Weak.Prom.Ref.OC) (M : List PMsg)
    (run : PF.PFRun LP Unit)
    (hv : PF.validRun (xStep P.xs) (testImg (P.toTest cond)) () (progs (P.toTest cond)) M run) (hu : untorn run) :
    ∃ Mm r, M = embM P Mm ∧ Mach.miniValidRun P Mm r ∧ ∀ h k, run.obsLoad h k = r.obsLoad h k := by
  obtain ⟨Mm, r, h1, h2, h3⟩ := e2b P hwf cond M run hv hu
  exact ⟨Mm, r, h1, h2, obsLoad_of_trace h3⟩

end MiniEq
