/-
Weak/Mini: **facts about MiniMach runs used by `mini_adequacy`** (mini plan rev 4 §2 L3; the full stack's template is
`Weak/Prom/CoreRun.lean`).  No logic: MiniMach (`Weak/Mini/Mach.lean`) only.

* `solo` — a hart's SOLO RUN against a fixed log: its own state steps only.  `mSteps_solo`: every run from a
  configuration whose views are bounded by its log (`cfgOk`; `mInit_ok`) gives every hart a solo run against the
  FINAL log, with the hart's trace.  The full stack obtains this from the promises-first factorization
  (`validRun_factorL`); MiniMach needs no factorization: a state step's admissibility reads the log only below the
  hart's views (`vle`), and a log only grows, so a step against the current log is a step against the final one
  (`mMem_ext`).
* `mSteps_pinv` — the PROMISE INVARIANT behind the fulfil partition (A0 (iii)): each hart's fulfilled timestamps and
  outstanding promises are, together and without repetition, exactly its own messages.
* `solo_wf` — A0 (v): every entry of a solo trace is well-formed against the log (`entryWf`).
Imports: only `Weak.Mini.Mach`.  No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Mini.Mach

namespace Weak.Mini.Mach

open Weak.Mini

/-! ## 1. Trace vocabulary of the adequacy statement -/

/-- A trace entry: the label of one state step and its fulfil timestamp (Mach.lean `traceOf`). -/
abbrev Trace : Type := List (MLab × Option Nat)

/-- `fulfilsOf h evs`: the fulfil timestamps of hart `h`, in order (Machine.lean `fulfilsOf`, :787). -/
def fulfilsOf (h : Nat) (evs : List MEvt) : List Nat := (traceOf h evs).filterMap (fun e => e.2)

/-- `ownAt log h t`: the message at timestamp `t` (`t ≥ 1`) of `log` is hart `h`'s. -/
def ownAt (log : List MMsg) (h t : Nat) : Prop := ∃ m, log[t - 1]? = some m ∧ m.tid = h

/-- A WELL-FORMED TRACE ENTRY of hart `h` against the log `M` (Machine.lean `traceWf`, :813, word form): a load
reads the word it returns at its timestamp (the image at 0), fulfils nothing; a store fulfils a timestamp `ts ≥ 1`
whose message is this word by hart `h`; no other label fulfils. -/
def entryWf (P : MProg) (M : List MMsg) (h : Nat) : MLab × Option Nat → Prop
  | (.load a t v _, ots) => ots = none ∧ memv P M t a = some v
  | (.store a v _ _, ots) => ∃ ts, ots = some ts ∧ 0 < ts ∧ M[ts - 1]? = some ⟨a, v, h⟩
  | (_, ots) => ots = none

/-! ## 2. Solo runs and view bounds -/

/-- A SOLO RUN of hart `h` against the fixed log `M`: state steps only, each with some promise sets. -/
inductive solo (P : MProg) (M : List MMsg) (h : Nat) : MFront → MSt → Trace → MFront → MSt → Prop
  | refl (f : MFront) (ws : MSt) : solo P M h f ws [] f ws
  | step (f : MFront) (ws : MSt) (l : MLab) (ots : Option Nat) (f' : MFront) (ws' : MSt) (pr pr' : List Nat)
      (τ : Trace) (f'' : MFront) (ws'' : MSt) :
      mNext P h f l = some f' → mMem P M h pr ws l ots ws' pr' → solo P M h f' ws' τ f'' ws'' →
      solo P M h f ws ((l, ots) :: τ) f'' ws''

/-- Every view of `ws` is at most `n`. -/
structure vle (n : Nat) (ws : MSt) : Prop where
  coh : ∀ a, ws.coh a ≤ n
  rO : ws.vrOld ≤ n
  wO : ws.vwOld ≤ n
  rN : ws.vrNew ≤ n
  wN : ws.vwNew ≤ n
  fwd : ∀ a t v, ws.fwd a = some (t, v) → t ≤ n ∧ v ≤ n
  regv : ∀ r, ws.regv r ≤ n
  cap : ws.vcap ≤ n
  ldv : ws.ldv ≤ n

theorem vle_mono {n n' : Nat} {ws : MSt} (h : vle n ws) (hn : n ≤ n') : vle n' ws :=
  ⟨fun a => Nat.le_trans (h.coh a) hn, Nat.le_trans h.rO hn, Nat.le_trans h.wO hn, Nat.le_trans h.rN hn,
   Nat.le_trans h.wN hn, fun a t v hf => ⟨Nat.le_trans (h.fwd a t v hf).1 hn, Nat.le_trans (h.fwd a t v hf).2 hn⟩,
   fun r => Nat.le_trans (h.regv r) hn, Nat.le_trans h.cap hn, Nat.le_trans h.ldv hn⟩

theorem srcsView_le {n : Nat} {ws : MSt} (h : vle n ws) : ∀ srcs, srcsView ws srcs ≤ n
  | [] => Nat.zero_le _
  | s :: r => by
    have h1 := srcsView_le h r
    have h2 : srcView ws s ≤ n := by
      cases s with
      | reg r => exact h.regv r
      | ldres => exact h.ldv
    show max (srcView ws s) (srcsView ws r) ≤ n
    omega

theorem fwdView_le {n : Nat} {ws : MSt} {a t : Nat} (hv : vle n ws) (ht : t ≤ n) : fwdView ws a t ≤ n := by
  unfold fwdView
  split
  · next tf vf hf =>
    split
    · exact (hv.fwd a tf vf hf).2
    · exact ht
  · exact ht

theorem memv_len {P : MProg} {log : List MMsg} {t a v : Nat} (h : memv P log t a = some v) : t ≤ log.length := by
  cases t with
  | zero => exact Nat.zero_le _
  | succ k =>
    simp only [memv] at h
    split at h
    · next m hm => exact (List.getElem?_eq_some_iff.1 hm).1
    · cases h

theorem memv_ext {P : MProg} {log u : List MMsg} {t a v : Nat} (h : memv P log t a = some v) :
    memv P (log ++ u) t a = some v := by
  cases t with
  | zero => exact h
  | succ k =>
    have hk := memv_len h
    simp only [memv] at h ⊢
    rw [List.getElem?_append_left (by omega)]
    exact h

theorem writesIn_ext {log u : List MMsg} {a lo hi : Nat} (hh : hi ≤ log.length) (h : writesIn (log ++ u) a lo hi) :
    writesIn log a lo hi := by
  obtain ⟨t, h1, h2, m, hm, hpa⟩ := h
  refine ⟨t, h1, h2, m, ?_, hpa⟩
  rwa [List.getElem?_append_left (by omega)] at hm

/-- A state step against a log is a state step against every extension of it, when the hart's views are bounded
by the log. -/
theorem mMem_ext {P : MProg} {log u : List MMsg} {i : Nat} {pr : List Nat} {ws : MSt} {l : MLab}
    {ots : Option Nat} {ws' : MSt} {pr' : List Nat} (hv : vle log.length ws) (h : mMem P log i pr ws l ots ws' pr') :
    mMem P (log ++ u) i pr ws l ots ws' pr' := by
  cases h with
  | load a t v asrc hl =>
    refine .load _ _ _ _ _ _ ⟨memv_ext hl.1, fun hw => hl.2 (writesIn_ext ?_ hw)⟩
    have := srcsView_le hv asrc
    have := hv.rN
    have := hv.coh a
    simp only [ldPre]
    omega
  | store a v asrc vsrc ts h1 h2 h3 h4 =>
    have := (List.getElem?_eq_some_iff.1 h2).1
    exact .store _ _ _ _ _ _ _ h1 (by rw [List.getElem?_append_left (by omega)]; exact h2) h3 h4
  | fence => exact .fence _ _ _ _ _ _
  | regW => exact .regW _ _ _ _
  | ctrl => exact .ctrl _ _ _
  | instr => exact .instr _ _

/-- A state step keeps the views bounded by the log. -/
theorem mMem_vle {P : MProg} {log : List MMsg} {i : Nat} {pr : List Nat} {ws : MSt} {l : MLab}
    {ots : Option Nat} {ws' : MSt} {pr' : List Nat} (hv : vle log.length ws) (h : mMem P log i pr ws l ots ws' pr') :
    vle log.length ws' := by
  cases h with
  | load a t v asrc hl =>
    have ht := memv_len hl.1
    have hva := srcsView_le hv asrc
    have hrN := hv.rN
    have hfv := fwdView_le (a := a) hv ht
    have hca := hv.coh a
    refine ⟨fun b => ?_, ?_, hv.wO, hv.rN, hv.wN, hv.fwd, hv.regv, ?_, ?_⟩ <;> simp only [loadPost, ldPre]
    · have := hv.coh b
      split <;> omega
    · have := hv.rO
      omega
    · have := hv.cap
      omega
    · have := hv.ldv
      omega
  | store a v asrc vsrc ts h1 h2 h3 h4 =>
    have hts : ts ≤ log.length := by have := (List.getElem?_eq_some_iff.1 h2).1; omega
    have hva := srcsView_le hv asrc
    have hvd := srcsView_le hv vsrc
    refine ⟨fun b => ?_, hv.rO, ?_, hv.rN, hv.wN, fun b t' v' hb => ?_, hv.regv, ?_, hv.ldv⟩
    · simp only [storePost]
      have := hv.coh b
      have := hv.coh a
      split <;> omega
    · simp only [storePost]
      have := hv.wO
      omega
    · simp only [storePost] at hb
      split at hb
      · simp only [Option.some.injEq, Prod.mk.injEq] at hb
        obtain ⟨rfl, rfl⟩ := hb
        exact ⟨hts, by omega⟩
      · exact hv.fwd b t' v' hb
    · simp only [storePost]
      have := hv.cap
      omega
  | fence fpr fpw fsr fsw =>
    have := hv.rO
    have := hv.wO
    have := hv.rN
    have := hv.wN
    refine ⟨hv.coh, hv.rO, hv.wO, ?_, ?_, hv.fwd, hv.regv, hv.cap, hv.ldv⟩ <;> simp only [fencePost] <;>
      (repeat' split) <;> omega
  | regW rd srcs =>
    refine ⟨hv.coh, hv.rO, hv.wO, hv.rN, hv.wN, hv.fwd, fun r => ?_, hv.cap, hv.ldv⟩
    show (if r = rd then srcsView ws srcs else ws.regv r) ≤ _
    split
    · exact srcsView_le hv srcs
    · exact hv.regv r
  | ctrl srcs =>
    refine ⟨hv.coh, hv.rO, hv.wO, hv.rN, hv.wN, hv.fwd, hv.regv, ?_, hv.ldv⟩
    show max (srcsView ws srcs) ws.vcap ≤ _
    have := srcsView_le hv srcs
    have := hv.cap
    omega
  | instr =>
    exact ⟨hv.coh, hv.rO, hv.wO, hv.rN, hv.wN, hv.fwd, hv.regv, hv.cap, Nat.zero_le _⟩

/-! ## 3. Configurations: bounded views, growing logs, solo projection -/

/-- Every hart's views are bounded by the log. -/
def cfgOk (c : MCfg) : Prop := ∀ (i : Nat) (hs : MHart), c.hs[i]? = some hs → vle c.log.length hs.ws

theorem msInit_vle (n : Nat) : vle n msInit :=
  ⟨fun _ => Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _,
   fun _ _ _ h => (by cases h), fun _ => Nat.zero_le _, Nat.zero_le _, Nat.zero_le _⟩

theorem mInit_get {P : MProg} {h : Nat} {hs : MHart} (hh : (mInit P).hs[h]? = some hs) :
    h < P.harts.length ∧ hs = ⟨⟨0, (List.range 32).map (fun r => P.reg0 h r % two64), []⟩, msInit, []⟩ := by
  simp only [mInit, List.getElem?_map] at hh
  by_cases hl : h < P.harts.length
  · rw [List.getElem?_range hl] at hh
    simp only [Option.map_some, Option.some.injEq] at hh
    exact ⟨hl, hh.symm⟩
  · rw [List.getElem?_eq_none (by simp; omega)] at hh
    cases hh

theorem mInit_ok (P : MProg) : cfgOk (mInit P) := by
  unfold cfgOk
  intro i hs hh
  rw [(mInit_get hh).2]
  exact msInit_vle _

theorem mStep_log {P : MProg} {c c' : MCfg} {e : MEvt} (h : mStep P c e c') : ∃ u, c.log ++ u = c'.log := by
  cases h with
  | promise => exact ⟨_, rfl⟩
  | state => exact ⟨[], List.append_nil _⟩

theorem mSteps_log {P : MProg} {c c' : MCfg} {evs : List MEvt} (h : mSteps P c evs c') :
    ∃ u, c.log ++ u = c'.log := by
  induction h with
  | refl => exact ⟨[], List.append_nil _⟩
  | step c0 c1 c2 e es hst _ ih =>
    obtain ⟨u1, h1⟩ := mStep_log hst
    obtain ⟨u2, h2⟩ := ih
    exact ⟨u1 ++ u2, by rw [← List.append_assoc, h1, h2]⟩

theorem get_set_self {l : List MHart} {i : Nat} {x y : MHart} (h : l[i]? = some x) : (l.set i y)[i]? = some y :=
  List.getElem?_set_self (List.getElem?_eq_some_iff.1 h).1

theorem mStep_ok {P : MProg} {c c' : MCfg} {e : MEvt} (hok : cfgOk c) (h : mStep P c e c') : cfgOk c' := by
  cases h with
  | promise i hi m hgi _ _ _ =>
    unfold cfgOk
    intro j hs hj
    by_cases hij : i = j
    · subst hij
      rw [get_set_self hgi] at hj
      cases hj
      exact vle_mono (hok i hi hgi) (by simp)
    · rw [List.getElem?_set_ne hij] at hj
      exact vle_mono (hok j hs hj) (by simp)
  | state i hi l ots fr' ws' prom' hgi _ hm =>
    unfold cfgOk
    intro j hs hj
    by_cases hij : i = j
    · subst hij
      rw [get_set_self hgi] at hj
      cases hj
      exact mMem_vle (hok i hi hgi) hm
    · rw [List.getElem?_set_ne hij] at hj
      exact hok j hs hj

theorem mStep_len {P : MProg} {c c' : MCfg} {e : MEvt} (h : mStep P c e c') : c'.hs.length = c.hs.length := by
  cases h <;> simp

theorem mSteps_len {P : MProg} {c c' : MCfg} {evs : List MEvt} (h : mSteps P c evs c') :
    c'.hs.length = c.hs.length := by
  induction h with
  | refl => rfl
  | step c0 c1 c2 e es hst _ ih => rw [ih, mStep_len hst]

theorem mSteps_ok {P : MProg} {c c' : MCfg} {evs : List MEvt} (h : mSteps P c evs c') (hok : cfgOk c) : cfgOk c' := by
  induction h with
  | refl => exact hok
  | step c0 c1 c2 e es hst _ ih => exact ih (mStep_ok hok hst)

/-- **SOLO PROJECTION**: every hart of a run from a bounded configuration has a solo run against the FINAL log,
whose trace is the hart's trace of the run. -/
theorem mSteps_solo {P : MProg} : ∀ {c c' : MCfg} {evs : List MEvt}, mSteps P c evs c' → cfgOk c →
    ∀ (h : Nat) (hs : MHart), c.hs[h]? = some hs →
      ∃ hs' : MHart, c'.hs[h]? = some hs' ∧ solo P c'.log h hs.fr hs.ws (traceOf h evs) hs'.fr hs'.ws := by
  intro c c' evs hr
  induction hr with
  | refl c => intro _ h hs hh; exact ⟨hs, hh, .refl _ _⟩
  | step c0 c1 c2 e es hst hrest ih =>
    intro hok h hs hh
    have hok1 := mStep_ok hok hst
    obtain ⟨u, hu⟩ := mSteps_log hrest
    cases hst with
    | promise i hi m hgi _ _ _ =>
      simp only [traceOf]
      by_cases hih : i = h
      · subst hih
        have e : hi = hs := Option.some.inj (hgi.symm.trans hh)
        subst e
        exact ih hok1 i { hi with prom := (c0.log.length + 1) :: hi.prom } (get_set_self hgi)
      · exact ih hok1 h hs (by rw [List.getElem?_set_ne hih]; exact hh)
    | state i hi l ots fr' ws' prom' hgi hn hm =>
      by_cases hih : i = h
      · subst hih
        have e : hi = hs := Option.some.inj (hgi.symm.trans hh)
        subst e
        obtain ⟨hs', h1, h2⟩ := ih hok1 i _ (get_set_self hgi)
        refine ⟨hs', h1, ?_⟩
        simp only [traceOf]
        refine .step _ _ l ots fr' ws' hi.prom prom' _ _ _ hn ?_ h2
        rw [← hu]
        exact mMem_ext (hok i hi hgi) hm
      · simp only [traceOf, if_neg hih]
        exact ih hok1 h hs (by rw [List.getElem?_set_ne hih]; exact hh)

/-- A hart with no slot takes no step. -/
theorem mSteps_none {P : MProg} {h : Nat} : ∀ {c c' : MCfg} {evs : List MEvt}, mSteps P c evs c' →
    c.hs[h]? = none → traceOf h evs = [] := by
  intro c c' evs hr
  induction hr with
  | refl => intro _; rfl
  | step c0 c1 c2 e es hst _ ih =>
    intro hn
    cases hst with
    | promise i hi m hgi _ _ _ =>
      have hih : i ≠ h := by intro e; subst e; rw [hgi] at hn; cases hn
      simp only [traceOf]
      exact ih (by rw [List.getElem?_set_ne hih]; exact hn)
    | state i hi l ots fr' ws' prom' hgi _ _ =>
      have hih : i ≠ h := by intro e; subst e; rw [hgi] at hn; cases hn
      simp only [traceOf, if_neg hih]
      exact ih (by rw [List.getElem?_set_ne hih]; exact hn)

theorem solo_take {P : MProg} {M : List MMsg} {h : Nat} : ∀ {f : MFront} {ws : MSt} {τ : Trace} {f' : MFront}
    {ws' : MSt}, solo P M h f ws τ f' ws' → ∀ k, ∃ f'' ws'', solo P M h f ws (τ.take k) f'' ws'' := by
  intro f ws τ f' ws' hs
  induction hs with
  | refl f ws => intro k; exact ⟨f, ws, by simpa using solo.refl f ws⟩
  | step f ws l ots f1 ws1 pr pr' τ f2 ws2 hn hm _ ih =>
    intro k
    cases k with
    | zero => exact ⟨f, ws, .refl _ _⟩
    | succ k =>
      obtain ⟨f'', ws'', h⟩ := ih k
      exact ⟨f'', ws'', by simpa using solo.step _ _ _ _ _ _ _ _ _ _ _ hn hm h⟩

/-! ## 4. A0 (v): well-formed entries -/

theorem mMem_wf {P : MProg} {M : List MMsg} {i : Nat} {pr : List Nat} {ws : MSt} {l : MLab}
    {ots : Option Nat} {ws' : MSt} {pr' : List Nat} (h : mMem P M i pr ws l ots ws' pr') : entryWf P M i (l, ots) := by
  cases h with
  | load a t v asrc hl => exact ⟨rfl, hl.1⟩
  | store a v asrc vsrc ts _ h2 h3 _ => exact ⟨ts, rfl, by omega, h2⟩
  | fence => rfl
  | regW => rfl
  | ctrl => rfl
  | instr => rfl

theorem solo_wf {P : MProg} {M : List MMsg} {h : Nat} : ∀ {f : MFront} {ws : MSt} {τ : Trace} {f' : MFront}
    {ws' : MSt}, solo P M h f ws τ f' ws' → ∀ e ∈ τ, entryWf P M h e := by
  intro f ws τ f' ws' hs
  induction hs with
  | refl => intro e he; cases he
  | step f ws l ots f1 ws1 pr pr' τ f2 ws2 _ hm _ ih =>
    intro e he
    rcases List.mem_cons.1 he with rfl | he
    · exact mMem_wf hm
    · exact ih e he

/-! ## 5. A0 (iii): the promise invariant -/

/-- Hart `i`'s outstanding promises (none outside the harts). -/
def promOf (c : MCfg) (i : Nat) : List Nat := ((c.hs[i]?).map MHart.prom).getD []

/-- THE PROMISE INVARIANT after the events `evs`: a hart's fulfils and its promises are its own messages,
each once. -/
structure PInv (evs : List MEvt) (c : MCfg) : Prop where
  own : ∀ i t, (t ∈ fulfilsOf i evs ∨ t ∈ promOf c i) ↔ (0 < t ∧ ownAt c.log i t)
  nd : ∀ i, (fulfilsOf i evs).Nodup
  disj : ∀ i t, t ∈ fulfilsOf i evs → t ∉ promOf c i

theorem traceOf_append (h : Nat) : ∀ (a b : List MEvt), traceOf h (a ++ b) = traceOf h a ++ traceOf h b
  | [], _ => rfl
  | .prom _ _ :: a, b => by simp only [List.cons_append, traceOf]; exact traceOf_append h a b
  | .st i l ots :: a, b => by
    simp only [List.cons_append, traceOf]
    split <;> simp [traceOf_append h a b]

theorem fulfilsOf_prom (j i : Nat) (m : MMsg) (evs : List MEvt) :
    fulfilsOf j (evs ++ [.prom i m]) = fulfilsOf j evs := by
  simp [fulfilsOf, traceOf_append, traceOf]

theorem fulfilsOf_st (j i : Nat) (l : MLab) (ots : Option Nat) (evs : List MEvt) :
    fulfilsOf j (evs ++ [.st i l ots]) = fulfilsOf j evs ++ (if i = j then ots.toList else []) := by
  unfold fulfilsOf
  rw [traceOf_append]
  simp only [traceOf]
  by_cases hij : i = j
  · subst hij; cases ots <;> simp
  · simp [hij]

theorem ownAt_snoc {log : List MMsg} {m : MMsg} {j t : Nat} (ht : 0 < t) :
    ownAt (log ++ [m]) j t ↔ ownAt log j t ∨ (t = log.length + 1 ∧ m.tid = j) := by
  unfold ownAt
  rw [List.getElem?_append]
  split
  · next hlt =>
    constructor
    · exact .inl
    · rintro (h | ⟨rfl, _⟩)
      · exact h
      · omega
  · next hlt =>
    rw [List.getElem?_singleton, List.getElem?_eq_none (by omega)]
    split
    · next h0 =>
      have e : t = log.length + 1 := by omega
      subst e
      simp
    · next h0 =>
      simp only [reduceCtorEq, false_and, exists_false, false_or, false_iff, not_and]
      intro e; omega

theorem ownAt_le {log : List MMsg} {j t : Nat} (h : ownAt log j t) : t - 1 < log.length := by
  obtain ⟨m, hm, _⟩ := h
  exact (List.getElem?_eq_some_iff.1 hm).1

theorem mMem_prom {P : MProg} {log : List MMsg} {i : Nat} {pr : List Nat} {ws : MSt} {l : MLab}
    {ots : Option Nat} {ws' : MSt} {pr' : List Nat} (h : mMem P log i pr ws l ots ws' pr') :
    (ots = none ∧ pr' = pr) ∨ (∃ ts, ots = some ts ∧ ts ∈ pr ∧ pr' = pr.filter (fun t => t != ts)) := by
  cases h with
  | store a v asrc vsrc ts h1 _ _ _ => exact .inr ⟨ts, rfl, h1, rfl⟩
  | load => exact .inl ⟨rfl, rfl⟩
  | fence => exact .inl ⟨rfl, rfl⟩
  | regW => exact .inl ⟨rfl, rfl⟩
  | ctrl => exact .inl ⟨rfl, rfl⟩
  | instr => exact .inl ⟨rfl, rfl⟩

theorem promOf_set_self {c : MCfg} {i : Nat} {hi x : MHart} {log : List MMsg} (h : c.hs[i]? = some hi) :
    promOf ⟨log, c.hs.set i x⟩ i = x.prom := by
  simp [promOf, get_set_self h]

theorem promOf_set_ne {c : MCfg} {i j : Nat} {x : MHart} {log : List MMsg} (h : i ≠ j) :
    promOf ⟨log, c.hs.set i x⟩ j = promOf c j := by
  simp [promOf, List.getElem?_set_ne h]

theorem promOf_get {c : MCfg} {i : Nat} {hi : MHart} (h : c.hs[i]? = some hi) : promOf c i = hi.prom := by
  simp [promOf, h]

theorem mStep_pinv {P : MProg} {c c' : MCfg} {e : MEvt} {evs : List MEvt} (hinv : PInv evs c)
    (h : mStep P c e c') : PInv (evs ++ [e]) c' := by
  cases h with
  | promise i hi m hgi htid _ _ =>
    have hle : ∀ j t, (t ∈ fulfilsOf j evs ∨ t ∈ promOf c j) → t - 1 < c.log.length :=
      fun j t ht => ownAt_le ((hinv.own j t).1 ht).2
    refine ⟨fun j t => ?_, fun j => ?_, fun j t ht => ?_⟩
    · rw [fulfilsOf_prom]
      by_cases hij : i = j
      · subst hij
        rw [promOf_set_self hgi]
        simp only [List.mem_cons]
        have hown := hinv.own i t
        rw [promOf_get hgi] at hown
        constructor
        · rintro (h1 | rfl | h1)
          · have := (hown.1 (.inl h1))
            exact ⟨this.1, (ownAt_snoc this.1).2 (.inl this.2)⟩
          · exact ⟨by omega, (ownAt_snoc (by omega)).2 (.inr ⟨rfl, htid⟩)⟩
          · have := (hown.1 (.inr h1))
            exact ⟨this.1, (ownAt_snoc this.1).2 (.inl this.2)⟩
        · rintro ⟨h0, ho⟩
          rcases (ownAt_snoc h0).1 ho with ho | ⟨rfl, _⟩
          · rcases hown.2 ⟨h0, ho⟩ with h1 | h1
            · exact .inl h1
            · exact .inr (.inr h1)
          · exact .inr (.inl rfl)
      · rw [promOf_set_ne hij]
        rw [hinv.own j t]
        constructor
        · rintro ⟨h0, ho⟩; exact ⟨h0, (ownAt_snoc h0).2 (.inl ho)⟩
        · rintro ⟨h0, ho⟩
          rcases (ownAt_snoc h0).1 ho with ho | ⟨_, ht⟩
          · exact ⟨h0, ho⟩
          · exact absurd (htid.symm.trans ht) hij
    · rw [fulfilsOf_prom]; exact hinv.nd j
    · rw [fulfilsOf_prom] at ht
      by_cases hij : i = j
      · subst hij
        rw [promOf_set_self hgi]
        simp only [List.mem_cons, not_or]
        have := hle i t (.inl ht)
        refine ⟨by omega, ?_⟩
        rw [← promOf_get hgi]
        exact hinv.disj i t ht
      · rw [promOf_set_ne hij]; exact hinv.disj j t ht
  | state i hi l ots fr' ws' prom' hgi _ hm =>
    refine ⟨fun j t => ?_, fun j => ?_, fun j t ht => ?_⟩ <;> rw [fulfilsOf_st] at *
    · by_cases hij : i = j
      · subst hij
        rw [promOf_set_self hgi, if_pos rfl]
        have hown := hinv.own i t
        rw [promOf_get hgi] at hown
        rw [← hown]
        rcases mMem_prom hm with ⟨rfl, rfl⟩ | ⟨ts, rfl, hts, rfl⟩
        · simp
        · simp only [Option.toList_some, List.mem_append, List.mem_singleton, List.mem_filter, bne_iff_ne, ne_eq]
          constructor
          · rintro ((h1 | rfl) | ⟨h1, _⟩)
            · exact .inl h1
            · exact .inr hts
            · exact .inr h1
          · rintro (h1 | h1)
            · exact .inl (.inl h1)
            · by_cases e : t = ts
              · exact .inl (.inr e)
              · exact .inr ⟨h1, e⟩
      · rw [promOf_set_ne hij, if_neg hij, List.append_nil]
        exact hinv.own j t
    · by_cases hij : i = j
      · subst hij
        rw [if_pos rfl]
        rcases mMem_prom hm with ⟨rfl, rfl⟩ | ⟨ts, rfl, hts, rfl⟩
        · simpa using hinv.nd i
        · simp only [Option.toList_some]
          rw [List.nodup_append]
          refine ⟨hinv.nd i, List.nodup_cons.2 ⟨by simp, List.nodup_nil⟩, fun a ha b hb => ?_⟩
          rw [List.mem_singleton] at hb
          subst hb
          intro e; subst e
          exact hinv.disj i a ha (by rw [promOf_get hgi]; exact hts)
      · rw [if_neg hij, List.append_nil]; exact hinv.nd j
    · by_cases hij : i = j
      · subst hij
        rw [promOf_set_self hgi]
        rw [if_pos rfl] at ht
        rcases mMem_prom hm with ⟨rfl, rfl⟩ | ⟨ts, rfl, hts, rfl⟩
        · rw [← promOf_get hgi]; exact hinv.disj i t (by simpa using ht)
        · simp only [Option.toList_some, List.mem_append, List.mem_singleton] at ht
          simp only [List.mem_filter, bne_iff_ne, ne_eq, not_and, Decidable.not_not]
          intro h1
          rcases ht with ht | rfl
          · exact absurd (by rw [promOf_get hgi]; exact h1) (hinv.disj i t ht)
          · rfl
      · rw [if_neg hij, List.append_nil] at ht
        rw [promOf_set_ne hij]; exact hinv.disj j t ht

theorem mSteps_pinv {P : MProg} : ∀ {c c' : MCfg} {es : List MEvt}, mSteps P c es c' →
    ∀ evs, PInv evs c → PInv (evs ++ es) c' := by
  intro c c' es hr
  induction hr with
  | refl => intro evs h; simpa using h
  | step c0 c1 c2 e es hst _ ih =>
    intro evs h
    have := ih (evs ++ [e]) (mStep_pinv h hst)
    simpa using this

theorem pinv_init (P : MProg) : PInv [] (mInit P) := by
  refine ⟨fun i t => ?_, fun i => List.nodup_nil, fun i t ht => by cases ht⟩
  have hp : promOf (mInit P) i = [] := by
    unfold promOf
    cases hh : (mInit P).hs[i]? with
    | none => rfl
    | some hs => rw [(mInit_get hh).2]; rfl
  rw [hp]
  simp only [fulfilsOf, traceOf, List.filterMap_nil, List.not_mem_nil, or_self, false_iff, not_and]
  intro _ ho
  have := ownAt_le ho
  simp [mInit] at this

/-- **A0 (iii) for MiniMach**: in a run with no outstanding promise at the end, hart `h` fulfils exactly its own
messages of the final log, each once. -/
theorem mSteps_partition {P : MProg} {evs : List MEvt} {c : MCfg} (hr : mSteps P (mInit P) evs c)
    (hnp : noProm c) :
    (∀ h t, t ∈ fulfilsOf h evs ↔ 0 < t ∧ ownAt c.log h t) ∧ (∀ h, (fulfilsOf h evs).Nodup) := by
  have hinv := mSteps_pinv hr [] (pinv_init P)
  rw [List.nil_append] at hinv
  have hp : ∀ i, promOf c i = [] := by
    intro i
    unfold promOf
    cases hh : c.hs[i]? with
    | none => rfl
    | some hs => simp [hnp i hs hh]
  refine ⟨fun h t => ?_, hinv.nd⟩
  rw [← hinv.own h t, hp h]
  simp

end Weak.Mini.Mach
