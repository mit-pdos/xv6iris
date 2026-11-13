/-
Weak/Prom: **InfLoop part 3 — THE BRIDGE: a `litStep` run of an unrolling of `tLoop` is an `xStep xsLoop` run of
`tLoop` itself, with the SAME event list** (owner request 2026-11-13; PfxUnroll.lean header "the remaining bridge
is machine-level (a litStep run of the unrolled program is an xStep run of the loop program with the same labels:
same instruction texts, branch labels `LCtrl`/`LInstr` identical, only `pc` differs)").

TLOOP-SPECIFIC (recorded in PROGRESS-InfLoop.md): the hypothesis on the unrolled test `T'` (`UOk`) is that its
`j`-th instruction of hart `h` is `unr j` of `tLoop`'s instruction at `pc = j % 4` — the path every execution of
`tLoop` takes before it halts (InfLoopRef.lean `pc_pat`).  The simulation relation `SR` keeps the registers, the
queued labels, the memory half (`PState`, promises) and the log identical; the loop hart's `pc` is the unrolled
hart's `pc % 4`.  Straight-line instructions step identically (the litmus front end's `instrNext` reads only the
registers); the branch `beq zero,zero,0` is ALWAYS taken on the loop machine (`brEval .eq 0 0`), going to `0 =
(j + 1) % 4`, and the unrolled branch goes to `j + 1` either way: same labels `LCtrl []`, `LInstr`.  A generic
bridge (any loop program, branch directions fixed by `condsOk`) is not needed here.
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.InfLoopRef

namespace Weak.Prom.InfLoop

open MachCSL MachCSL.Stdpp Iris.Std
open Weak (Image Dsrc)
open Weak.Prom Weak.Prom.PF Weak.Prom.Mach Weak.Prom.Mach.Cert
open Weak.Prom.Ref (Instr Test two64 brEval sext)
open Weak.Prom.Pfx (unr)
open Weak.Prom.OA (XI xNext xStep xOf)
open Weak.Prom.PF.Loop (tLoop xsLoop pL0 pL1 bL0 bL1)
open PLabel

/-! ## 1. Litmus-front-end steps, introduced -/

theorem rd_of_regs {s t : LP} (h : s.regs = t.regs) (r : Nat) : s.rd r = t.rd r := by
  unfold LP.rd; rw [h]

theorem wr_of_regs {s t : LP} (h : s.regs = t.regs) (r v : Nat) : s.wr r v = t.wr r v := by
  unfold LP.wr; rw [h]

theorem litNext_load_intro {s : LP} {sz rd rs1 off : Nat} {sgn : Bool} (hq : s.q = [])
    (hp : s.prog[s.pc]? = some (.load sz sgn rd rs1 off)) (ha : aligned ((s.rd rs1 + off) % two64) sz = true)
    {tvs : List (Nat × BitVec 8)} (hl : tvs.length = sz) :
    litNext s (LLoad false false (((s.rd rs1 + off) % two64 : Nat) : Int) tvs (srcR rs1)) =
      some { s with regs := s.wr rd (if sgn then sext sz (ofBytes (tvs.map Prod.snd)) else ofBytes (tvs.map Prod.snd)),
                    pc := s.pc + 1, q := regWL rd [.DLdRes] ++ [LInstr] } := by
  unfold litNext
  rw [hq]
  simp [hp, instrNext, ha, hl]

theorem litNext_store_intro {s : LP} {sz rs2 rs1 off : Nat} (hq : s.q = [])
    (hp : s.prog[s.pc]? = some (.store sz rs2 rs1 off)) (ha : aligned ((s.rd rs1 + off) % two64) sz = true) :
    litNext s (LStore false false (((s.rd rs1 + off) % two64 : Nat) : Int) (toBytes (s.rd rs2) sz) (srcR rs1)
      (srcR rs2)) = some { s with pc := s.pc + 1, q := [LInstr] } := by
  unfold litNext
  rw [hq]
  simp [hp, instrNext, ha]

theorem litNext_fence_intro {s : LP} {f : Weak.Prom.Ref.FenceSet} (hq : s.q = [])
    (hp : s.prog[s.pc]? = some (.fence f)) :
    litNext s (LFence f.pr f.pw f.sr f.sw) = some { s with regs := s.regs, pc := s.pc + 1, q := [LInstr] } := by
  unfold litNext
  rw [hq]
  simp [hp, instrNext, go1]

theorem litNext_q_intro {s : LP} {l0 : PLabel} {rest : List PLabel} (hq : s.q = l0 :: rest) :
    litNext s l0 = some { s with q := rest } := by
  unfold litNext; rw [hq]; simp

/-- A misaligned load is stuck. -/
theorem litNext_load_al {s : LP} {sz rd rs1 off : Nat} {sgn : Bool} (hq : s.q = [])
    (hp : s.prog[s.pc]? = some (.load sz sgn rd rs1 off)) {l : PLabel} {s' : LP} (h : litNext s l = some s') :
    aligned ((s.rd rs1 + off) % two64) sz = true := by
  cases ha : aligned ((s.rd rs1 + off) % two64) sz
  · unfold litNext at h; rw [hq] at h; simp [hp, instrNext, ha] at h
  · rfl

theorem litNext_store_al {s : LP} {sz rs2 rs1 off : Nat} (hq : s.q = [])
    (hp : s.prog[s.pc]? = some (.store sz rs2 rs1 off)) {l : PLabel} {s' : LP} (h : litNext s l = some s') :
    aligned ((s.rd rs1 + off) % two64) sz = true := by
  cases ha : aligned ((s.rd rs1 + off) % two64) sz
  · unfold litNext at h; rw [hq] at h; simp [hp, instrNext, ha] at h
  · rfl

/-! ## 2. The per-hart simulation relation -/

/-- The unrolled program of hart `h`: its `j`-th instruction is `unr j` of `tLoop`'s instruction at `j % 4`. -/
def UOk (h : Nat) (U : List Instr) : Prop :=
  ∀ j (i : Instr), U[j]? = some i → ∃ i0, (tLoop.prog h)[j % 4]? = some i0 ∧ i = unr j i0

/-- `s'` (the unrolled hart) and `s` (the loop hart) agree: registers, queued labels; `pc` modulo 4. -/
def SR (h : Nat) (s' s : LP) : Prop :=
  (h = 0 ∨ h = 1) ∧ s.prog = tLoop.prog h ∧ UOk h s'.prog ∧ s.regs = s'.regs ∧ s.q = s'.q ∧
    (s'.pc < s'.prog.length → s.pc = s'.pc % 4)

theorem bind_at (h p : Nat) (hh : h = 0 ∨ h = 1) (hp : p < 4) :
    ∃ i0, (tLoop.prog h)[p]? = some i0 ∧ (xOf xsLoop (tLoop.prog h)).bind (fun X => X[p]?) = some (.i i0) := by
  rcases hh with rfl | rfl <;>
    rcases (by omega : p = 0 ∨ p = 1 ∨ p = 2 ∨ p = 3) with rfl | rfl | rfl | rfl <;> exact ⟨_, rfl, by decide⟩

/-- **ONE LABEL** of the unrolled hart is one label of the loop hart. -/
theorem sr_step {h : Nat} {s' s s'1 : LP} {l : PLabel} (hr : SR h s' s) (hs : litNext s' l = some s'1) :
    ∃ s1, xNext xsLoop s l = some s1 ∧ SR h s'1 s1 := by
  obtain ⟨hh, hP, hU, hregs, hqq, hpc⟩ := hr
  cases hq' : s'.q with
  | cons l0 rest =>
    obtain ⟨rfl, rfl⟩ := litNext_q hq' hs
    have hq : s.q = l :: rest := by rw [hqq, hq']
    refine ⟨{ s with q := rest }, ?_, hh, hP, hU, hregs, rfl, hpc⟩
    rw [OA.xNext_q (s := s) (by rw [hq]; simp)]
    exact litNext_q_intro hq
  | nil =>
    have hq : s.q = [] := by rw [hqq, hq']
    cases hget' : s'.prog[s'.pc]? with
    | none => rw [litNext_end hq' hget'] at hs; cases hs
    | some ins =>
      have hlt : s'.pc < s'.prog.length := (List.getElem?_eq_some_iff.1 hget').1
      have hspc := hpc hlt
      obtain ⟨i0, hi0, rfl⟩ := hU _ _ hget'
      have hm4 : s'.pc % 4 < 4 := Nat.mod_lt _ (by decide)
      obtain ⟨i1, hi1, hbind⟩ := bind_at h (s'.pc % 4) hh hm4
      rw [hi0, Option.some.injEq] at hi1
      subst hi1
      have hget : s.prog[s.pc]? = some i0 := by rw [hP, hspc]; exact hi0
      rw [← hspc, ← hP] at hbind
      have hrd := rd_of_regs hregs
      have hwr := wr_of_regs hregs
      -- the plain case
      have plain : ∀ (hpl : (XI.i i0).plain = true)
          (hst : ∀ s1', litNext s' l = some s1' → s1'.prog = s'.prog ∧ s1'.pc = s'.pc + 1 ∧
            ∃ s1, litNext s l = some s1 ∧ s1.prog = s.prog ∧ s1.pc = s.pc + 1 ∧ s1.regs = s1'.regs ∧ s1.q = s1'.q),
          s'.pc % 4 < 3 → ∃ s1, xNext xsLoop s l = some s1 ∧ SR h s'1 s1 := by
        intro hpl hst h3
        obtain ⟨h2, h3', s1, h1, k1, k2, k3, k4⟩ := hst s'1 hs
        refine ⟨s1, ?_, hh, ?_, ?_, k3, k4, fun _ => ?_⟩
        · rw [OA.xNext_plain hq (fun x hx => by rw [hbind, Option.some.injEq] at hx; subst hx; exact hpl)]
          exact h1
        · rw [k1]; exact hP
        · rw [h2]; exact hU
        · rw [k2, h3', hspc]; omega
      rcases hh with rfl | rfl <;>
        rcases (by omega : s'.pc % 4 = 0 ∨ s'.pc % 4 = 1 ∨ s'.pc % 4 = 2 ∨ s'.pc % 4 = 3) with hc | hc | hc | hc <;>
        rw [hc] at hi0 <;> simp only [Weak.Prom.InfLoop.prog0, Weak.Prom.InfLoop.prog1, List.getElem?_cons_zero,
          List.getElem?_cons_succ, Option.some.injEq] at hi0 <;> subst hi0
      -- hart 0
      · refine plain rfl (fun s1' h1 => ?_) (by omega)
        have ha := litNext_store_al hq' hget' h1
        obtain ⟨rfl, rfl⟩ := litNext_store hq' hget' ha h1
        have ha' := ha
        rw [← hrd 12] at ha'
        have hi := litNext_store_intro hq hget ha'
        rw [hrd 12, hrd 6] at hi
        exact ⟨rfl, rfl, _, hi, rfl, rfl, hregs, rfl⟩
      · refine plain rfl (fun s1' h1 => ?_) (by omega)
        obtain ⟨rfl, rfl⟩ := litNext_fence hq' hget' h1
        exact ⟨rfl, rfl, _, litNext_fence_intro hq hget, rfl, rfl, hregs, rfl⟩
      · refine plain rfl (fun s1' h1 => ?_) (by omega)
        have ha := litNext_store_al hq' hget' h1
        obtain ⟨rfl, rfl⟩ := litNext_store hq' hget' ha h1
        have ha' := ha
        rw [← hrd 13] at ha'
        have hi := litNext_store_intro hq hget ha'
        rw [hrd 13, hrd 6] at hi
        exact ⟨rfl, rfl, _, hi, rfl, rfl, hregs, rfl⟩
      · exact brCase hq hq' hget' hlt hspc hc hbind hs ⟨Or.inl rfl, hP, hU, hregs, hqq, hpc⟩
      -- hart 1
      · refine plain rfl (fun s1' h1 => ?_) (by omega)
        have ha := litNext_load_al hq' hget' h1
        obtain ⟨tvs, rfl, rfl, hl⟩ := litNext_load hq' hget' ha h1
        have ha' := ha
        rw [← hrd 13] at ha'
        have hi := litNext_load_intro hq hget ha' hl
        rw [hrd 13] at hi
        exact ⟨rfl, rfl, _, hi, rfl, rfl, by simp only [hwr], rfl⟩
      · refine plain rfl (fun s1' h1 => ?_) (by omega)
        obtain ⟨rfl, rfl⟩ := litNext_fence hq' hget' h1
        exact ⟨rfl, rfl, _, litNext_fence_intro hq hget, rfl, rfl, hregs, rfl⟩
      · refine plain rfl (fun s1' h1 => ?_) (by omega)
        have ha := litNext_load_al hq' hget' h1
        obtain ⟨tvs, rfl, rfl, hl⟩ := litNext_load hq' hget' ha h1
        have ha' := ha
        rw [← hrd 12] at ha'
        have hi := litNext_load_intro hq hget ha' hl
        rw [hrd 12] at hi
        exact ⟨rfl, rfl, _, hi, rfl, rfl, by simp only [hwr], rfl⟩
      · exact brCase hq hq' hget' hlt hspc hc hbind hs ⟨Or.inr rfl, hP, hU, hregs, hqq, hpc⟩
where
  /-- The branch `beq zero,zero,0` (unrolled: `beq zero,zero,j+1`). -/
  brCase {h : Nat} {s' s s'1 : LP} {l : PLabel} (hq : s.q = []) (hq' : s'.q = [])
      (hget' : s'.prog[s'.pc]? = some (unr s'.pc (.br .eq 0 0 0))) (hlt : s'.pc < s'.prog.length)
      (hspc : s.pc = s'.pc % 4) (hc : s'.pc % 4 = 3)
      (hbind : (xOf xsLoop s.prog).bind (fun X => X[s.pc]?) = some (.i (.br .eq 0 0 0)))
      (hs : litNext s' l = some s'1) (hr : SR h s' s) : ∃ s1, xNext xsLoop s l = some s1 ∧ SR h s'1 s1 := by
    obtain ⟨hh, hP, hU, hregs, hqq, _⟩ := hr
    obtain ⟨rfl, rfl⟩ := litNext_br hq' hget' (by omega) hs
    refine ⟨{ s with regs := s.regs, pc := 0, q := [LInstr] }, ?_, hh, hP, hU, hregs, rfl, fun _ => ?_⟩
    · unfold xNext
      rw [hq]
      simp only [hbind]
      simp [go1, LP.rd, brEval]
    · simp only [ite_self]; omega

/-! ## 3. Configurations -/

/-- Agent-wise agreement of two configurations (same image, log, fabric; same memory halves; `SR` programs). -/
def CR (c' c : PCfg LP Unit) : Prop :=
  c.pcImg = c'.pcImg ∧ c.pcLog = c'.pcLog ∧ c.pcAgs.length = c'.pcAgs.length ∧
    ∀ h a' a, c'.pcAgs[h]? = some a' → c.pcAgs[h]? = some a → a.paWs = a'.paWs ∧ a.paProm = a'.paProm ∧
      SR h a'.paSt a.paSt

theorem get_some_of_len {α β : Type} {l : List α} {m : List β} (hl : m.length = l.length) {h : Nat} {a : α}
    (ha : l[h]? = some a) : ∃ b, m[h]? = some b := by
  have : h < m.length := by rw [hl]; exact (List.getElem?_eq_some_iff.1 ha).1
  exact ⟨_, List.getElem?_eq_getElem this⟩

theorem set_get {α : Type} (l : List α) (i h : Nat) (a : α) (hi : i < l.length) :
    (l.set i a)[h]? = if i = h then some a else l[h]? := by
  by_cases hih : i = h
  · subst hih; simp [hi]
  · simp [List.getElem?_set_ne hih, hih]

theorem cr_set {c' c : PCfg LP Unit} (hc : CR c' c) {i : Nat} {a' a : PAgent LP} (hi' : c'.pcAgs[i]? = some a')
    (hi : c.pcAgs[i]? = some a) (b' b : PAgent LP) (hb : b.paWs = b'.paWs ∧ b.paProm = b'.paProm ∧ SR i b'.paSt b.paSt)
    (img : Image) (log : List PMsg) :
    CR ⟨img, log, (), c'.pcAgs.set i b'⟩ ⟨img, log, (), c.pcAgs.set i b⟩ := by
  obtain ⟨_, _, hl, hag⟩ := hc
  have hlt' : i < c'.pcAgs.length := (List.getElem?_eq_some_iff.1 hi').1
  have hlt : i < c.pcAgs.length := (List.getElem?_eq_some_iff.1 hi).1
  refine ⟨rfl, rfl, by simp [hl], fun h x' x hx' hx => ?_⟩
  simp only at hx' hx
  rw [set_get _ _ _ _ hlt'] at hx'
  rw [set_get _ _ _ _ hlt] at hx
  by_cases hih : i = h
  · subst hih
    simp only [if_true, Option.some.injEq] at hx' hx
    subst hx' hx; exact hb
  · simp only [hih, if_false] at hx' hx
    exact hag h x' x hx' hx

/-- **ONE MACHINE STEP** of the unrolled program is one machine step of the loop program, with the same event. -/
theorem cr_step {c' c'1 c : PCfg LP Unit} {e : PEvt} (hs : pmStep litStep c' e c'1) (hc : CR c' c) :
    ∃ c1, pmStep (xStep xsLoop) c e c1 ∧ CR c'1 c1 := by
  obtain ⟨himg, hlog, hl, hag⟩ := hc
  cases hs with
  | promise i ag' m hag' hm htid =>
    obtain ⟨ag, hagc⟩ := get_some_of_len hl hag'
    obtain ⟨hws, hpr, hsr⟩ := hag i ag' ag hag' hagc
    refine ⟨_, .promise c i ag m hagc hm htid, ?_⟩
    rw [himg, hlog]
    exact cr_set ⟨himg, hlog, hl, hag⟩ hag' hagc ⟨ag'.paSt, ag'.paWs, {c'.pcLog.length + 1} ∪ ag'.paProm⟩
      ⟨ag.paSt, ag.paWs, {c'.pcLog.length + 1} ∪ ag.paProm⟩ ⟨hws, by rw [hpr], hsr⟩ _ _
  | state i ag' l ots st' d' ws' prom' hag' hp hm =>
    obtain ⟨ag, hagc⟩ := get_some_of_len hl hag'
    obtain ⟨hws, hpr, hsr⟩ := hag i ag' ag hag' hagc
    obtain ⟨s1, hs1, hsr1⟩ := sr_step hsr hp
    have hm' : memStep c.pcImg c.pcLog i ag.paProm ag.paWs l ots ws' prom' := by
      rw [himg, hlog, hws, hpr]; exact hm
    refine ⟨_, .state c i ag l ots s1 () ws' prom' hagc hs1 hm', ?_⟩
    rw [himg, hlog]
    exact cr_set ⟨himg, hlog, hl, hag⟩ hag' hagc ⟨st', ws', prom'⟩ ⟨s1, ws', prom'⟩ ⟨rfl, rfl, hsr1⟩ _ _

theorem cr_steps {c' c'' : PCfg LP Unit} {evs : List PEvt} (hs : pmSteps litStep c' evs c'') :
    ∀ {c : PCfg LP Unit}, CR c' c → ∃ c2, pmSteps (xStep xsLoop) c evs c2 ∧ CR c'' c2 := by
  induction hs with
  | refl => intro c hc; exact ⟨c, .refl _, hc⟩
  | step c0 c1 c2 e es hst _ ih =>
    intro c hc
    obtain ⟨d1, hd1, hcr1⟩ := cr_step hst hc
    obtain ⟨d2, hd2, hcr2⟩ := ih hcr1
    exact ⟨d2, .step _ _ _ _ _ hd1 hd2, hcr2⟩

/-! ## 4. THE BRIDGE -/

theorem progs_at (T : Test) {h : Nat} (hh : h < T.harts.length) :
    (progs T)[h]? = some (LP.mk (T.prog h) 0
      ((List.range 32).map (fun r => ((((T.regs0[h]?).getD []).lookup r).getD 0) % two64)) []) := by
  unfold progs
  rw [List.getElem?_map, List.getElem?_range hh]; rfl

/-- **THE BRIDGE** (tLoop-specific): a valid `litStep` run of an unrolling `T'` of `tLoop` whose harts follow the
loop's path (`UOk`) is — event for event — a valid `xStep xsLoop` run of `tLoop`, with the same final memory. -/
theorem bridge {T' : Test} (hlen : T'.harts.length = 2) (hregs : T'.regs0 = tLoop.regs0) (himg : T'.img = tLoop.img)
    (hU : ∀ h < 2, UOk h (T'.prog h)) {M : List PMsg} {run : PFRun LP Unit}
    (hv : PF.validRun litStep (testImg T') () (progs T') M run) :
    ∃ cfg : PCfg LP Unit, PF.validRun (xStep xsLoop) (testImg tLoop) () (progs tLoop) M ⟨run.evs, cfg⟩ := by
  obtain ⟨⟨hsteps, hnp⟩, hM⟩ := hv
  have hti : testImg T' = testImg tLoop := by
    funext a; simp [testImg, Ref.Test.imgF, himg]
  have h0 : CR (pmInit (testImg T') () (progs T')) (pmInit (testImg tLoop) () (progs tLoop)) := by
    refine ⟨hti.symm, rfl, by simp [pmInit, progs, hlen, tLoop_len], fun h a' a ha' ha => ?_⟩
    simp only [pmInit, List.getElem?_map] at ha' ha
    have hh : h < 2 := by
      have : h < (progs T').length := by
        rcases hx : (progs T')[h]? with _ | p
        · rw [hx] at ha'; cases ha'
        · exact (List.getElem?_eq_some_iff.1 hx).1
      simpa [progs, hlen] using this
    rw [progs_at T' (by rw [hlen]; exact hh)] at ha'
    rw [progs_at tLoop (by rw [tLoop_len]; exact hh)] at ha
    simp only [Option.map_some, Option.some.injEq] at ha' ha
    subst ha' ha
    refine ⟨rfl, rfl, by omega, rfl, hU h hh, by rw [hregs], rfl, fun _ => rfl⟩
  obtain ⟨c2, hs2, hcr⟩ := cr_steps hsteps h0
  obtain ⟨_, hlog, hl, hag⟩ := hcr
  refine ⟨c2, ⟨hs2, fun i ag hag2 => ?_⟩, hlog.trans hM⟩
  obtain ⟨ag', hag'⟩ := get_some_of_len hl.symm hag2
  rw [(hag i ag' ag hag' hag2).2.1]
  exact hnp i ag' hag'

end Weak.Prom.InfLoop
