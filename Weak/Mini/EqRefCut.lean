/-
Weak/Mini: **E1 — MiniRef = the full reference on F, finite cuts** (mini plan rev 4 §2 L1: "the same pair for the
finite cut against `partExec`"; [R4]: the finite-cut E1b also returns the cut states).

* `toCut P cond C` — every hart's state after `C.ks h` REPLAYED steps under C's load values.
* `e1aCut` — `miniCut P C ↔ partExec (P.toTest cond) (toCut P cond C) (nuOf P.sz C.V) C.g`.
* `e1bCut` — every finite partial execution of `P.toTest cond` is `toCut` of a mini cut: the SAME states
  (`trs = toCut P cond C`, so `finalReg` agrees: review-R4 3(b)), the same events, the same contents, the same gmo.
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Mini.EqRefList

namespace Weak.Mini

open Weak.Prom.Ref
open Weak.Prom.Pfx

/-! ## 1. Steps keep or extend the path conditions -/

theorem stepL_conds {h n sz : Nat} {s : SSt} (mi : MI) :
    (∀ s', stepL h n s (mi.toInstr sz) = .next s' → s'.conds = s.conds) ∧
    (∀ t f, stepL h n s (mi.toInstr sz) = .fork t f → ∃ c rs1 rs2,
      t.conds = s.conds ++ [(c, (s.rd rs1).1, (s.rd rs2).1, true)] ∧
      f.conds = s.conds ++ [(c, (s.rd rs1).1, (s.rd rs2).1, false)]) := by
  cases mi with
  | br c rs1 rs2 tgt =>
    simp only [MI.toInstr, stepL]
    split
    · exact ⟨(fun _ h => by cases h), (fun _ _ h => by cases h)⟩
    · refine ⟨(fun _ h => by cases h), (fun t f h => ?_)⟩
      simp only [StepR.fork.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨c.toBrC, rs1, rs2, rfl, rfl⟩
  | jmp tgt =>
    simp only [MI.toInstr, stepL]
    split
    · exact ⟨(fun _ h => by cases h), (fun _ _ h => by cases h)⟩
    · exact ⟨(fun _ h => by cases h; rfl), (fun _ _ h => by cases h)⟩
  | alui => exact ⟨(fun _ h => by cases h; simp [SSt.adv]), (fun _ _ h => by cases h)⟩
  | alu => exact ⟨(fun _ h => by cases h; simp [SSt.adv]), (fun _ _ h => by cases h)⟩
  | load => exact ⟨(fun _ h => by cases h; simp [SSt.adv, SSt.emit]), (fun _ _ h => by cases h)⟩
  | store => exact ⟨(fun _ h => by cases h; rfl), (fun _ _ h => by cases h)⟩
  | fence => exact ⟨(fun _ h => by cases h; rfl), (fun _ _ h => by cases h)⟩
  | nop => exact ⟨(fun _ h => by cases h; rfl), (fun _ _ h => by cases h)⟩

theorem instr_at {P : MProg} {cond : OC} {h : Nat} {s : SSt} {i : Instr}
    (hi : ((P.toTest cond).prog h)[s.pc]? = some i) : ∃ mi, (P.prog h)[s.pc]? = some mi ∧ i = mi.toInstr P.sz := by
  rw [prog_toTest, List.getElem?_map] at hi
  cases hmi : (P.prog h)[s.pc]? with
  | none => rw [hmi] at hi; cases hi
  | some mi => rw [hmi] at hi; exact ⟨mi, rfl, (Option.some.inj hi).symm⟩

theorem lstep_conds {P : MProg} {cond : OC} {h : Nat} {s s' : SSt} (hl : LStep ((P.toTest cond).prog h) h s s') :
    s.conds <+: s'.conds := by
  rcases hl with ⟨_, rfl⟩ | ⟨i, hi, hs⟩
  · exact List.prefix_refl _
  · obtain ⟨mi, _, rfl⟩ := instr_at hi
    rcases hs with hs | ⟨t, f, hs, rfl | rfl⟩
    · rw [(stepL_conds mi).1 _ hs]; exact List.prefix_refl _
    · obtain ⟨_, _, _, h1, _⟩ := (stepL_conds mi).2 _ _ hs; rw [h1]; exact List.prefix_append _ _
    · obtain ⟨_, _, _, _, h2⟩ := (stepL_conds mi).2 _ _ hs; rw [h2]; exact List.prefix_append _ _

theorem condsHold_prefix {ν : Val} {s s' : SSt} (hp : s.conds <+: s'.conds) (h : condsHold ν s' = true) :
    condsHold ν s = true := by
  unfold condsHold at h ⊢
  rw [List.all_eq_true] at h ⊢
  exact fun x hx => h x (hp.subset hx)

theorem rstep_of_fstep {p : List Instr} {h : Nat} {ν : Val} {s s' : SSt} (hs : FStep p h ν s s') :
    rstep p h ν s = s' := by
  unfold rstep
  rcases hs with ⟨hp, rfl⟩ | ⟨i, hi, hc⟩
  · rw [hp]; simp
  · simp only [hi, hc, Option.getD_some]

/-- A reachable state whose path conditions hold is a replayed one. -/
theorem reach_replay {P : MProg} {cond : OC} {h : Nat} {ν : Val} {s : SSt}
    (hr : LReach ((P.toTest cond).prog h) h ((P.toTest cond).init h) s) (hc : condsHold ν s = true) :
    ∃ k, s = replay (P.toTest cond) h ν k := by
  induction hr with
  | refl => exact ⟨0, rfl⟩
  | step _ hl ih =>
    obtain ⟨k, rfl⟩ := ih (condsHold_prefix (lstep_conds hl) hc)
    exact ⟨k + 1, (rstep_of_fstep (fstep_of_lstep hl hc)).symm⟩

theorem reach_of_replay {P : MProg} {cond : OC} {h : Nat} {ν : Val}
    (hs : ∀ k, FStep ((P.toTest cond).prog h) h ν (replay (P.toTest cond) h ν k) (replay (P.toTest cond) h ν (k + 1))) :
    ∀ k, LReach ((P.toTest cond).prog h) h ((P.toTest cond).init h) (replay (P.toTest cond) h ν k)
  | 0 => .refl
  | k + 1 => .step (reach_of_replay hs k) (lstep_of_fstep (hs k))

/-- The replay does not depend on which valuation gives the (same) mini values. -/
theorem replay_congr {P : MProg} {cond : OC} {h : Nat} {V : EvId → Nat} {ν ν' : Val}
    (h1 : ∀ k, SimSt P.sz h V ν (mrun P V h k) (replay (P.toTest cond) h ν k))
    (h2 : ∀ k, SimSt P.sz h V ν' (mrun P V h k) (replay (P.toTest cond) h ν' k)) :
    ∀ k, replay (P.toTest cond) h ν k = replay (P.toTest cond) h ν' k
  | 0 => rfl
  | k + 1 => by
    have ih := replay_congr h1 h2 k
    have hS1 := h1 k; have hS2 := h2 k
    rw [ih] at hS1
    show rstep _ h ν (replay _ h ν k) = rstep _ h ν' (replay _ h ν' k)
    rw [ih]
    unfold rstep
    generalize replay (P.toTest cond) h ν' k = s at hS1 hS2
    cases hi : ((P.toTest cond).prog h)[s.pc]? with
    | none => rfl
    | some i =>
      simp only
      obtain ⟨mi, _, rfl⟩ := instr_at hi
      cases hst : stepL h ((P.toTest cond).prog h).length s (mi.toInstr P.sz) with
      | stuck => rfl
      | next _ => rfl
      | fork t f =>
        obtain ⟨c, rs1, rs2, ht, _⟩ := (stepL_conds mi).2 t f hst
        have e1 := congrArg Prod.fst ((hS1.rd rs1).trans (hS2.rd rs1).symm)
        have e2 := congrArg Prod.fst ((hS1.rd rs2).trans (hS2.rd rs2).symm)
        simp only [chosen, forkOk, ht, getLast_conds] at e1 e2 ⊢
        rw [e1, e2]

/-! ## 2. toCut -/

/-- **`toCut P cond C`**: hart `h`'s state after `C.ks h` replayed steps under C's load values. -/
def toCut (P : MProg) (cond : OC) (C : MCut) : List SSt :=
  (List.range P.harts.length).map (fun h => replay (P.toTest cond) h (nuOf P.sz C.V) (C.ks h))

/-- A single-state alignment check is the mini events' alignment. -/
theorem evsAligned_iff {sz h : Nat} {V : EvId → Nat} {ν : Val} {m : MSt} {s : SSt} (H : SimSt sz h V ν m s) :
    evsAligned ν s = true ↔ ∀ i (hi : i < m.evs.length), (m.evs[i].kind = .ld ∨ m.evs[i].kind = .st) →
      m.evs[i].pa % sz = 0 := by
  unfold evsAligned
  rw [List.all_eq_true]
  constructor
  · intro ha i hi hk
    have hi' : i < s.evs.length := by rw [H.evl]; exact hi
    have := ha _ (List.getElem_mem hi')
    have hE := H.ev i hi' hi
    rw [hE.sk, hE.pa] at this
    generalize m.evs[i] = me at this hk ⊢
    obtain ⟨kd, ii, pa, v, ad, dd, cd⟩ := me
    rcases hk with hk | hk <;> simp only at hk <;> subst hk <;>
      simpa [MEv.toEv, MK.toKind, MK.szOf, Kind.isAcc, Kind.isMem] using this
  · intro ha se hse
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hse
    have hi' : i < m.evs.length := by rw [← H.evl]; exact hi
    have hE := H.ev i hi hi'
    have := ha i hi'
    rw [hE.sk, hE.pa]
    generalize m.evs[i] = me at this ⊢
    obtain ⟨kd, ii, pa, v, ad, dd, cd⟩ := me
    cases kd <;> simp_all [MEv.toEv, MK.toKind, MK.szOf, Kind.isAcc, Kind.isMem]

section cut

variable {P : MProg} {cond : OC} {C : MCut} {trs : List SSt} {ν : Val}

/-- The hypotheses: the cut states are simulated by C's mini states. -/
structure SimC (P : MProg) (C : MCut) (trs : List SSt) (ν : Val) : Prop where
  len : trs.length = P.harts.length
  sim : ∀ h (hh : h < trs.length), SimSt P.sz h C.V ν (C.st P h) trs[h]

theorem SimC.mem_sids (H : SimC P C trs ν) (e : EvId) : e ∈ sids trs ↔ (C.evs P).has e := by
  rw [sids, mem_idsOf]
  simp only [List.getElem?_map, MCut.evs]
  constructor
  · rintro ⟨l, hl, hi⟩
    cases h : trs[e.1]? with
    | none => rw [h] at hl; cases hl
    | some s =>
      rw [h] at hl; simp only [Option.map_some, Option.some.injEq] at hl; subst hl
      obtain ⟨hh, rfl⟩ := List.getElem?_eq_some_iff.1 h
      exact ⟨by rw [← H.len]; exact hh, by rw [← (H.sim e.1 hh).evl]; exact hi⟩
  · rintro ⟨hh, hi⟩
    have hh' : e.1 < trs.length := by rw [H.len]; exact hh
    exact ⟨trs[e.1].evs, by simp [List.getElem?_eq_getElem hh'], by rw [(H.sim e.1 hh').evl]; exact hi⟩

theorem posIn_eq (g : List EvId) (e : EvId) : pos g e = posIn g e := by
  induction g with
  | nil => rfl
  | cons x t ih => simp only [pos, posIn, ih]

theorem SimC.sevSim (H : SimC P C trs ν) {e : EvId} (he : (C.evs P).has e) :
    SimEv P.sz e.1 e.2 C.V ν (sevAt trs e) ((C.evs P).ev e) := by
  have hh : e.1 < trs.length := by rw [H.len]; exact he.1
  have hS := H.sim e.1 hh
  have hi : e.2 < trs[e.1].evs.length := by rw [hS.evl]; exact he.2
  have h1 : sevAt trs e = trs[e.1].evs[e.2] := by
    simp [sevAt, List.getElem?_eq_getElem hh, List.getElem?_eq_getElem hi]
  have h2 : (C.evs P).ev e = (C.st P e.1).evs[e.2]'he.2 := by
    simp [MCut.evs, List.getElem?_eq_getElem he.2]
  rw [h1, h2]
  exact hS.ev e.2 hi he.2

theorem SimC.simA (H : SimC P C trs ν) :
    SimA P cond (C.evs P) C.V (cutI (P.toTest cond) trs ν C.g) := by
  have hlen : trs.length = (P.toTest cond).harts.length := by rw [H.len, harts_toTest]
  refine ⟨rfl, fun e => by rw [cutI_has hlen, H.mem_sids], fun e he => ?_, ?_⟩
  · rw [cutI_sev hlen ((H.mem_sids e).2 he)]; exact H.sevSim he
  · funext a b
    simp only [cutI, MCut.evs, gB, Bool.and_eq_true, List.contains_iff_mem, decide_eq_true_eq, posIn_eq, and_assoc]

theorem SimC.kind (H : SimC P C trs ν) {e : EvId} (he : e ∈ sids trs) :
    (sskOf trs e).kind = ((C.evs P).ev e).kind.toKind := by
  unfold sskOf; rw [(H.sevSim ((H.mem_sids e).1 he)).sk]; rfl

theorem SimC.fkinds (H : SimC P C trs ν) (e : EvId) (he : e ∈ sids trs) :
    (sskOf trs e).kind.isLrSc = false ∧ (sskOf trs e).kind.isRmwW = false := by
  rw [H.kind he]
  cases (C.evs P).ev e |>.kind <;> simp [MK.toKind, Kind.isLrSc, Kind.isRmwW]

theorem SimC.aligned_iff (H : SimC P C trs ν) :
    (C.evs P).aligned P.sz ↔ trs.all (evsAligned ν) = true := by
  rw [List.all_eq_true]
  constructor
  · intro ha s hs
    obtain ⟨h, hh, rfl⟩ := List.getElem_of_mem hs
    rw [evsAligned_iff (H.sim h hh)]
    intro i hi hk
    have hh' : h < P.harts.length := by rw [← H.len]; exact hh
    have := ha (h, i) ⟨⟨hh', hi⟩, by
      show ((C.evs P).ev (h, i)).kind = .ld ∨ ((C.evs P).ev (h, i)).kind = .st
      simp only [MCut.evs, List.getElem?_eq_getElem hi, Option.getD_some]; exact hk⟩
    simp only [MCut.evs, List.getElem?_eq_getElem hi, Option.getD_some] at this
    exact this
  · intro ha e ⟨⟨hh, hi⟩, hk⟩
    have hh' : e.1 < trs.length := by rw [H.len]; exact hh
    have := (evsAligned_iff (H.sim e.1 hh')).1 (ha _ (List.getElem_mem hh')) e.2 hi
    show ((C.evs P).ev e).pa % P.sz = 0
    simp only [MCut.evs, MEvs.isLd, MEvs.isSt, List.getElem?_eq_getElem hi, Option.getD_some] at hk ⊢
    exact this hk

theorem SimC.gmoWf_iff (H : SimC P C trs ν) (g : List EvId) (hg : g = C.g) :
    gmoWf (conc (P.toTest cond) trs ν g) ↔ C.g.Nodup ∧ ∀ e, e ∈ C.g ↔ (C.evs P).isMem e := by
  subst hg
  have hk : ∀ e, e ∈ sids trs → ((sskOf trs e).kind.isMem = true ↔ (C.evs P).isLd e ∨ (C.evs P).isSt e) := by
    intro e he
    rw [H.kind he]
    simp only [MEvs.isLd, MEvs.isSt]
    cases (C.evs P).ev e |>.kind <;> simp [MK.toKind, Kind.isMem]
  unfold gmoWf
  simp only [conc_ids, conc_skf]
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, fun e => ⟨fun he => ?_, fun ⟨he, hm⟩ => ?_⟩⟩
    · exact ⟨(H.mem_sids e).1 (h2 e he).1, (hk e (h2 e he).1).1 (h2 e he).2⟩
    · have he' := (H.mem_sids e).2 he
      exact h3 e he' ((hk e he').2 hm)
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun e he => ?_, fun e he hm => (h2 e).2 ⟨(H.mem_sids e).1 he, (hk e he).1 hm⟩⟩
    obtain ⟨he', hm⟩ := (h2 e).1 he
    have he'' := (H.mem_sids e).2 he'
    exact ⟨he'', (hk e he'').2 hm⟩

/-- The cut's memory side, both ways. -/
theorem SimC.ref_iff (hwf : P.wf) (H : SimC P C trs ν) (hal : (C.evs P).aligned P.sz)
    (hg : gmoWf (conc (P.toTest cond) trs ν C.g))
    (hl : ∀ e, (C.evs P).has e → ((C.evs P).ev e).kind = .ld → ν e = byteList (C.V e) P.sz) :
    rvwmoRef (conc (P.toTest cond) trs ν C.g) ↔ (C.evs P).ax P.ini := by
  have hlen : trs.length = (P.toTest cond).harts.length := by rw [H.len, harts_toTest]
  rw [refCore_cut hlen rfl H.fkinds hg]
  exact corr_iff (H.simA.corr hwf hal hl)

end cut

theorem toCut_len (P : MProg) (cond : OC) (C : MCut) : (toCut P cond C).length = P.harts.length := by
  simp [toCut]

theorem toCut_get (P : MProg) (cond : OC) (C : MCut) {h : Nat} (hh : h < (toCut P cond C).length) :
    (toCut P cond C)[h] = replay (P.toTest cond) h (nuOf P.sz C.V) (C.ks h) := by
  simp [toCut]

theorem simC_toCut {P : MProg} (hwf : P.wf) (cond : OC) (C : MCut) :
    SimC P C (toCut P cond C) (nuOf P.sz C.V) :=
  ⟨toCut_len P cond C, fun h hh => by
    rw [toCut_get]; exact (replay_sim (agree_nuOf P.sz C.V) (tgtOk_of_wf hwf h) (C.ks h)).1⟩

/-! ## 3. E1a, E1b for the finite cut -/

theorem condsOk_list (ν : Val) (trs : List SSt) :
    condsOk ν trs = true ↔ trs.all (condsHold ν) = true ∧ trs.all (evsAligned ν) = true := by
  simp only [condsOk, condsHold, evsAligned, List.all_eq_true, Bool.and_eq_true]
  exact ⟨fun h => ⟨fun s hs => (h s hs).1, fun s hs => (h s hs).2⟩, fun h s hs => ⟨h.1 s hs, h.2 s hs⟩⟩

/-- **E1a (finite cut)**: a mini cut is exactly a finite partial execution of `toCut`. -/
theorem e1aCut (P : MProg) (hwf : P.wf) (cond : OC) (C : MCut) :
    miniCut P C ↔ partExec (P.toTest cond) (toCut P cond C) (nuOf P.sz C.V) C.g := by
  have H := simC_toCut hwf cond C
  have hc : (toCut P cond C).all (condsHold (nuOf P.sz C.V)) = true := by
    rw [List.all_eq_true]
    intro s hs
    obtain ⟨h, hh, rfl⟩ := List.getElem_of_mem hs
    rw [toCut_get]
    exact (replay_sim (cond := cond) (agree_nuOf P.sz C.V) (tgtOk_of_wf hwf h) (C.ks h)).2.2
  have hreach : ∀ h (hh : h < (toCut P cond C).length),
      LReach ((P.toTest cond).prog h) h ((P.toTest cond).init h) (toCut P cond C)[h] := by
    intro h hh
    rw [toCut_get]
    exact reach_of_replay (fun k => (replay_sim (agree_nuOf P.sz C.V) (tgtOk_of_wf hwf h) k).2.1) _
  have hlen : (toCut P cond C).length = (P.toTest cond).harts.length := by rw [toCut_len, harts_toTest]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    have hg := (H.gmoWf_iff (cond := cond) C.g rfl).2 ⟨h1, h2⟩
    exact ⟨hlen, hreach, (condsOk_list _ _).2 ⟨hc, H.aligned_iff.1 h3⟩,
      (H.ref_iff hwf h3 hg (fun _ _ _ => rfl)).2 h4⟩
  · rintro ⟨_, _, h3, h4⟩
    have hal := H.aligned_iff.2 ((condsOk_list _ _).1 h3).2
    have hg := h4.1.1
    obtain ⟨g1, g2⟩ := (H.gmoWf_iff (cond := cond) C.g rfl).1 hg
    exact ⟨g1, g2, hal, (H.ref_iff hwf hal hg (fun _ _ _ => rfl)).1 h4⟩

/-- **E1b (finite cut)**: every finite partial execution of an F program is `toCut` of a mini cut: the same
states, hence the same events; the same contents on existing events; the same gmo. -/
theorem e1bCut (P : MProg) (hwf : P.wf) (cond : OC) (trs : List SSt) (ν : Val) (g : List EvId)
    (hE : partExec (P.toTest cond) trs ν g) :
    ∃ C, miniCut P C ∧ trs = toCut P cond C ∧
      (∀ e, e ∈ (conc (P.toTest cond) trs ν g).ids ↔
        e ∈ (conc (P.toTest cond) (toCut P cond C) (nuOf P.sz C.V) C.g).ids) ∧
      (∀ e ∈ (conc (P.toTest cond) trs ν g).ids,
        (conc (P.toTest cond) trs ν g).ev e = (conc (P.toTest cond) (toCut P cond C) (nuOf P.sz C.V) C.g).ev e) ∧
      g = C.g := by
  obtain ⟨hlen, hreach, hcond, href⟩ := hE
  have hlen' : trs.length = P.harts.length := by rw [hlen, harts_toTest]
  let V : EvId → Nat := fun e => bytesVal ((ν e).take P.sz)
  have hA : Agree P.sz V ν := fun e => rfl
  have hcs := ((condsOk_list _ _).1 hcond)
  have hk : ∀ h, ∃ k, ∀ hh : h < trs.length, trs[h] = replay (P.toTest cond) h ν k := by
    intro h
    by_cases hh : h < trs.length
    · obtain ⟨k, hk⟩ := reach_replay (hreach h hh) (List.all_eq_true.1 hcs.1 _ (List.getElem_mem hh))
      exact ⟨k, fun _ => hk⟩
    · exact ⟨0, fun h' => absurd h' hh⟩
  let C : MCut := ⟨fun h => Classical.choose (hk h), V, g⟩
  have hkC : ∀ h (hh : h < trs.length), trs[h] = replay (P.toTest cond) h ν (C.ks h) :=
    fun h hh => Classical.choose_spec (hk h) hh
  have H : SimC P C trs ν := ⟨hlen', fun h hh => by
    rw [hkC h hh]; exact (replay_sim hA (tgtOk_of_wf hwf h) (C.ks h)).1⟩
  have htrs : trs = toCut P cond C := by
    apply List.ext_getElem (by rw [toCut_len, hlen'])
    intro h h1 h2
    rw [toCut_get, hkC h h1]
    exact replay_congr (fun k => (replay_sim hA (tgtOk_of_wf hwf h) k).1)
      (fun k => (replay_sim (agree_nuOf P.sz C.V) (tgtOk_of_wf hwf h) k).1) _
  have hal := H.aligned_iff.2 hcs.2
  have hg := href.1.1
  have hlenT : trs.length = (P.toTest cond).harts.length := hlen
  have hinf := (refCore_cut hlenT rfl H.fkinds hg).1 href
  have hl : ∀ e, (C.evs P).has e → ((C.evs P).ev e).kind = .ld → ν e = byteList (C.V e) P.sz :=
    fun e he hk => (H.simA (cond := cond)).bytes hwf hal hinf.2.1 hinf.2.2.2.1 e he hk
  obtain ⟨g1, g2⟩ := (H.gmoWf_iff (cond := cond) g rfl).1 hg
  have hx := (H.ref_iff hwf hal hg hl).1 href
  have H' := simC_toCut hwf cond C
  have hC := (H.simA (cond := cond)).corr hwf hal hl
  have hC' := (H'.simA (cond := cond)).corr hwf hal (fun _ _ _ => rfl)
  refine ⟨C, ⟨g1, g2, hal, hx⟩, htrs, fun e => by rw [← htrs, conc_ids, conc_ids], fun e he => ?_, rfl⟩
  rw [conc_ids] at he
  have hlenT' : (toCut P cond C).length = (P.toTest cond).harts.length := by rw [← htrs]; exact hlen
  have he' := (H.mem_sids e).1 he
  rw [← cutI_ev hlenT he, hC.ev e he', ← cutI_ev hlenT' (by rw [← htrs]; exact he), hC'.ev e he']

end Weak.Mini
