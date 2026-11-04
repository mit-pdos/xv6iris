/-
Weak/Prom: **the split-AMO litmus front end and the completeness / logic corollaries of `amoSplitFused`**
(S1M-proof, plan rev 7 §1 M10 (4); NA-5).

`litStepS` is `litStep` (MachCert.lean) with each AMO emitted AS SAIL EMITS IT (emission v2, Emit.lean `ramRead` /
`ramWrite`; MachSail.lean's runner): the read half `LAmoLd aq0 a tvs (srcR rs1)` with the answers, then the queued
write half `LAmoSt rl0 a data (srcR rs1) (srcR rs2)` (Sail: `mem_read … aq (aq && rl)` / `mem_write_value …
(aq && rl) rl`, whose `akAcq` bits are aq and rl, M10 (2)), then `rd`'s register write and `LInstr`.  Every other
instruction is `litStep`'s.

* `fuseOk_lit`, `splitOk_lit` — the premises of AmoSplit.lean's run theorems, PROVED for this pair (tightness holds
  by construction: the write half is queued right behind the read half).
* `rvwmo_complete_split` — **(T-cmp) for split AMOs**: `rvwmo_complete`'s conclusion with the run over `litStepS`
  (promises first, every hart done, same load observations, final registers, final memory).
* `litS_of_lit` — **the logic transfers**: a property `Q` of the load observations and final memory of every
  finished valid `litStep` run (the form of every `lit_` theorem and of `refFromLit`'s premise) holds of every
  finished valid `litStepS` run.
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.AmoSplit
import Weak.Prom.CmpLit

namespace Weak.Prom.Cmp

open MachCSL MachCSL.Stdpp Iris.Std
open Weak (Image Dsrc)
open Weak.Prom Weak.Prom.Mach Weak.Prom.Mach.Cert
open Weak.Prom.Ref
open Weak.Prom.AS (isHalf regOnly silentRun silentRunD SplitOk FuseOk TrRel pendS closedS fusedToSplit
  splitToFused_closed)
open PLabel

/-! ## 1. The split front end -/

/-- The bytes an AMO writes (as `instrNext`'s fused AMO). -/
def amoData (s : LP) (op : AmoOp) (sz rs2 : Nat) (tvs : List (Nat × BitVec 8)) : List (BitVec 8) :=
  toBytes (amoOp op sz (ofBytes (tvs.map Prod.snd)) (s.rd rs2 % 2 ^ (8 * sz))) sz

/-- The state after an AMO's read half: `rd` written, the write half queued. -/
def amoMid (s : LP) (op : AmoOp) (sz : Nat) (rl0 : Bool) (rd rs2 rs1 : Nat) (tvs : List (Nat × BitVec 8)) : LP :=
  { s with
    regs := s.wr rd (sext sz (ofBytes (tvs.map Prod.snd)))
    pc := s.pc + 1
    q := LAmoSt rl0 (s.rd rs1 : Int) (amoData s op sz rs2 tvs) (srcR rs1) (srcR rs2) ::
      (regWL rd [.DLdRes] ++ [LInstr]) }

/-- An instruction's first label, with the AMO split as Sail emits it. -/
def instrNextS (n : Nat) (s : LP) (ins : Instr) (l : PLabel) : Option LP :=
  match ins with
  | .amo op sz aq0 rl0 rd rs2 rs1 =>
      let a := s.rd rs1
      if !aligned a sz then none else
      match l with
      | LAmoLd aq b tvs asrc =>
          if aq = aq0 ∧ b = (a : Int) ∧ tvs.length = sz ∧ asrc = srcR rs1 then
            some (amoMid s op sz rl0 rd rs2 rs1 tvs)
          else none
      | _ => none
  | ins => instrNext n s ins l

/-- One label of a split litmus hart. -/
def litNextS (s : LP) (l : PLabel) : Option LP :=
  match s.q with
  | l0 :: rest => if l = l0 then some { s with q := rest } else none
  | [] =>
    match s.prog[s.pc]? with
    | some ins => instrNextS s.prog.length s ins l
    | none => none

/-- THE SPLIT-AMO PROGRAM HALF (no device fabric). -/
def litStepS (s : LP) (_ : Unit) (l : PLabel) (s' : LP) (_ : Unit) : Prop := litNextS s l = some s'

/-! ## 2. Label facts -/

theorem qLab_half {l : PLabel} (h : qLab l = true) : isHalf l = false := by
  cases l <;> first | rfl | cases h

theorem regOnly_srcR (r : Nat) : regOnly (srcR r) := by
  intro x hx
  unfold srcR at hx
  split at hx
  · cases hx
  · simp at hx; subst hx; intro h; cases h

theorem go1_half {s : LP} {regs' : List Nat} {pc' : Nat} {labs : List PLabel} {l : PLabel} {s' : LP}
    (h : go1 s regs' pc' labs l = some s') (hl : ∀ x ∈ labs, isHalf x = false) : isHalf l = false := by
  obtain ⟨rest, h1, _⟩ := go1_eq h
  exact hl l (by rw [h1]; simp)

theorem regWL_half (rd : Nat) (srcs : List Dsrc) (tail : List PLabel) (ht : ∀ x ∈ tail, isHalf x = false) :
    ∀ x ∈ regWL rd srcs ++ tail, isHalf x = false := by
  intro x hx
  unfold regWL at hx
  split at hx
  · exact ht x (by simpa using hx)
  · rcases List.mem_append.1 hx with hx | hx
    · simp at hx; subst hx; rfl
    · exact ht x hx

/-- The fused front end never emits a half. -/
theorem instrNext_half {n : Nat} {s s' : LP} {ins : Instr} {l : PLabel} (h : instrNext n s ins l = some s') :
    isHalf l = false := by
  have hI : ∀ x ∈ [LInstr], isHalf x = false := by simp [isHalf]
  cases ins with
  | alui op rd rs1 imm => exact go1_half h (regWL_half _ _ _ hI)
  | alu op rd rs1 rs2 => exact go1_half h (regWL_half _ _ _ hI)
  | fence f => simp only [instrNext] at h; exact go1_half h (by simp [isHalf])
  | fenceTso => simp only [instrNext] at h; exact go1_half h (by simp [isHalf])
  | br c rs1 rs2 tgt =>
    simp only [instrNext] at h
    split at h
    · cases h
    · exact go1_half h (by simp [isHalf])
  | jmp tgt =>
    simp only [instrNext] at h
    split at h
    · cases h
    · exact go1_half h (by simp [isHalf])
  | csrr rd v => exact go1_half h (regWL_half _ _ _ hI)
  | fencei => simp only [instrNext] at h; exact go1_half h (by simp [isHalf])
  | nop => simp only [instrNext] at h; exact go1_half h (by simp [isHalf])
  | loadAqPc => cases h
  | storeRlPc => cases h
  | _ =>
    simp only [instrNext] at h
    split at h
    · cases h
    · split at h <;> first | rfl | cases h

theorem litNext_half {s s' : LP} {l : PLabel} (hq : qOk s.q) (h : litNext s l = some s') : isHalf l = false := by
  unfold litNext at h
  cases hq' : s.q with
  | cons l0 rest =>
    rw [hq'] at h hq
    simp only at h
    split at h
    · rename_i he; subst he; exact qLab_half (hq.1 _ (by simp))
    · cases h
  | nil =>
    rw [hq'] at h
    simp only at h
    cases hp : s.prog[s.pc]? with
    | none => rw [hp] at h; cases h
    | some ins => rw [hp] at h; exact instrNext_half h

/-! ## 3. The split invariant -/

/-- A split hart's queue: a fused one, or a queued write half in front of a fused one. -/
def qOkS (q : List PLabel) : Prop :=
  qOk q ∨ ∃ rl b data asrc vsrc rest, q = LAmoSt rl b data asrc vsrc :: rest ∧ qOk rest

theorem instrNextS_eq {n : Nat} {s : LP} {ins : Instr} {l : PLabel} (hins : ∀ op sz aq rl rd rs2 rs1,
    ins ≠ .amo op sz aq rl rd rs2 rs1) : instrNextS n s ins l = instrNext n s ins l := by
  cases ins with
  | amo op sz aq rl rd rs2 rs1 => exact absurd rfl (hins op sz aq rl rd rs2 rs1)
  | _ => rfl

/-- The split AMO step, inverted. -/
theorem instrNextS_amo {n : Nat} {s s' : LP} {op : AmoOp} {sz : Nat} {aq0 rl0 : Bool} {rd rs2 rs1 : Nat}
    {l : PLabel} (h : instrNextS n s (.amo op sz aq0 rl0 rd rs2 rs1) l = some s') :
    aligned (s.rd rs1) sz = true ∧ ∃ tvs, l = LAmoLd aq0 (s.rd rs1 : Int) tvs (srcR rs1) ∧ tvs.length = sz ∧
      s' = amoMid s op sz rl0 rd rs2 rs1 tvs := by
  simp only [instrNextS] at h
  split at h
  · cases h
  · rename_i hal
    refine ⟨by simpa using hal, ?_⟩
    split at h
    · rename_i aq b tvs asrc
      split at h
      · rename_i hc
        obtain ⟨h1, h2, h3, h4⟩ := hc
        cases h
        subst h1 h2 h4
        exact ⟨tvs, rfl, h3, rfl⟩
      · cases h
    · cases h

theorem instrNextS_amo_intro {n : Nat} {s : LP} {op : AmoOp} {sz : Nat} {aq0 rl0 : Bool} {rd rs2 rs1 : Nat}
    {tvs : List (Nat × BitVec 8)} (hal : aligned (s.rd rs1) sz = true) (hlen : tvs.length = sz) :
    instrNextS n s (.amo op sz aq0 rl0 rd rs2 rs1) (LAmoLd aq0 (s.rd rs1 : Int) tvs (srcR rs1)) =
      some (amoMid s op sz rl0 rd rs2 rs1 tvs) := by
  simp [instrNextS, hal, hlen]

/-- The fused AMO step, inverted. -/
theorem instrNext_amo {n : Nat} {s s' : LP} {op : AmoOp} {sz : Nat} {aq0 rl0 : Bool} {rd rs2 rs1 : Nat}
    {l : PLabel} (h : instrNext n s (.amo op sz aq0 rl0 rd rs2 rs1) l = some s') :
    aligned (s.rd rs1) sz = true ∧ ∃ tvs, l = LRmw aq0 rl0 (s.rd rs1 : Int) tvs (amoData s op sz rs2 tvs)
      (srcR rs1) (srcR rs2) ∧ tvs.length = sz ∧
      s' = { amoMid s op sz rl0 rd rs2 rs1 tvs with q := regWL rd [.DLdRes] ++ [LInstr] } := by
  simp only [instrNext] at h
  split at h
  · cases h
  · rename_i hal
    refine ⟨by simpa using hal, ?_⟩
    split at h
    · rename_i aq rl b tvs data asrc vsrc
      split at h
      · rename_i hc
        obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hc
        cases h
        subst h1 h2 h3 h5 h6 h7
        exact ⟨tvs, rfl, h4, rfl⟩
      · cases h
    · cases h

theorem instrNext_amo_intro {n : Nat} {s : LP} {op : AmoOp} {sz : Nat} {aq0 rl0 : Bool} {rd rs2 rs1 : Nat}
    {tvs : List (Nat × BitVec 8)} (hal : aligned (s.rd rs1) sz = true) (hlen : tvs.length = sz) :
    instrNext n s (.amo op sz aq0 rl0 rd rs2 rs1)
      (LRmw aq0 rl0 (s.rd rs1 : Int) tvs (amoData s op sz rs2 tvs) (srcR rs1) (srcR rs2)) =
      some { amoMid s op sz rl0 rd rs2 rs1 tvs with q := regWL rd [.DLdRes] ++ [LInstr] } := by
  simp [instrNext, hal, hlen, amoData, amoMid]

theorem litNextS_inv {s s' : LP} {l : PLabel} (hq : qOkS s.q) (h : litNextS s l = some s') : qOkS s'.q := by
  unfold litNextS at h
  cases hq' : s.q with
  | cons l0 rest =>
    rw [hq'] at h hq
    simp only at h
    split at h
    · cases h
      rcases hq with hq | ⟨_, _, _, _, _, rest', he, hr⟩
      · exact .inl (qOk_tail hq)
      · cases he; exact .inl hr
    · cases h
  | nil =>
    rw [hq'] at h
    simp only at h
    cases hp : s.prog[s.pc]? with
    | none => rw [hp] at h; cases h
    | some ins =>
      rw [hp] at h
      simp only at h
      cases ins with
      | amo op sz aq0 rl0 rd rs2 rs1 =>
        obtain ⟨_, tvs, _, _, rfl⟩ := instrNextS_amo h
        exact .inr ⟨_, _, _, _, _, _, rfl, qOk_regWL1 rd [.DLdRes]⟩
      | _ =>
        rw [instrNextS_eq (by intro _ _ _ _ _ _ _ he; cases he)] at h
        exact .inl (instrNext_q h)

/-- From a `qOkS` state, the split front end's read half is the AMO instruction's. -/
theorem litNextS_ld {s s' : LP} {aq : Bool} {b : Int} {tvs : List (Nat × BitVec 8)} {asrc : List Dsrc}
    (hq : qOkS s.q) (h : litNextS s (LAmoLd aq b tvs asrc) = some s') :
    ∃ op sz rl0 rd rs2 rs1, s.q = [] ∧ s.prog[s.pc]? = some (.amo op sz aq rl0 rd rs2 rs1) ∧
      instrNextS s.prog.length s (.amo op sz aq rl0 rd rs2 rs1) (LAmoLd aq b tvs asrc) = some s' := by
  unfold litNextS at h
  cases hq' : s.q with
  | cons l0 rest =>
    rw [hq'] at h hq
    simp only at h
    split at h
    · rename_i he
      subst he
      rcases hq with hq | ⟨_, _, _, _, _, _, he, _⟩
      · exact absurd (hq.1 (LAmoLd aq b tvs asrc) (by simp)) (by simp [qLab])
      · cases he
    · cases h
  | nil =>
    rw [hq'] at h
    simp only at h
    cases hp : s.prog[s.pc]? with
    | none => rw [hp] at h; cases h
    | some ins =>
      rw [hp] at h
      simp only at h
      cases ins with
      | amo op sz aq0 rl0 rd rs2 rs1 =>
        have h' := h
        obtain ⟨_, _, hl, _⟩ := instrNextS_amo h
        cases hl
        exact ⟨op, sz, rl0, rd, rs2, rs1, rfl, rfl, h'⟩
      | _ =>
        rw [instrNextS_eq (by intro _ _ _ _ _ _ _ he; cases he)] at h
        exact absurd (instrNext_half h) (by simp [isHalf])

/-- A state whose queue starts with a write half takes no silent step. -/
theorem silentRun_stuck {s hk : LP} {rl : Bool} {b : Int} {data : List (BitVec 8)} {asrc vsrc : List Dsrc}
    {rest : List PLabel} (hq : s.q = LAmoSt rl b data asrc vsrc :: rest) (h : silentRun litStepS s hk) : hk = s := by
  cases h with
  | refl => rfl
  | step _ h1 _ hs _ =>
    have := hs ()
    simp only [litStepS, litNextS, hq] at this
    split at this <;> simp_all

/-! ## 4. The premises of the run theorems -/

theorem splitOk_lit : SplitOk litStepS litStep (fun s => qOkS s.q) := by
  refine ⟨fun h d l h' d' hq hs => litNextS_inv hq hs, ?plain, ?fab, ?tight, ?fuse⟩
  · intro h d l h' d' hq hs hl
    show litNext h l = some h'
    have hs' : litNextS h l = some h' := hs
    unfold litNextS at hs'
    unfold litNext
    cases hq' : h.q with
    | cons l0 rest => rw [hq'] at hs'; exact hs'
    | nil =>
      rw [hq'] at hs'
      simp only at hs' ⊢
      cases hp : h.prog[h.pc]? with
      | none => rw [hp] at hs'; cases hs'
      | some ins =>
        rw [hp] at hs'
        simp only at hs' ⊢
        cases ins with
        | amo op sz aq0 rl0 rd rs2 rs1 =>
          obtain ⟨_, _, rfl, _⟩ := instrNextS_amo hs'
          cases hl
        | _ =>
          rw [instrNextS_eq (by intro _ _ _ _ _ _ _ he; cases he)] at hs'
          exact hs'
  · intro h d l h' d' _ hs _
    cases d; cases d'
    exact ⟨rfl, fun d2 => by cases d2; exact hs⟩
  · intro h d aq base tvs asrc h1 d1 hq hs
    obtain ⟨op, sz, rl0, rd, rs2, rs1, _, _, hn⟩ := litNextS_ld hq hs
    obtain ⟨_, tvs', hl, _, rfl⟩ := instrNextS_amo hn
    cases hl
    refine ⟨regOnly_srcR rs1, fun hk hsr d l h' d' hs' => .inr ?_⟩
    have hk1 := silentRun_stuck rfl hsr
    subst hk1
    have hs'' : litNextS (amoMid h op sz rl0 rd rs2 rs1 _) l = some h' := hs'
    simp only [litNextS, amoMid] at hs''
    split at hs''
    · rename_i he
      subst he
      exact ⟨rl0, _, _, srcR rs2, rfl, regOnly_srcR rs2⟩
    · cases hs''
  · intro h aq base tvs asrc h1 hk d rl data vsrc h' d' hq hld hsr hst _ _
    obtain ⟨op, sz, rl0, rd, rs2, rs1, hq0, hpc, hn⟩ := litNextS_ld hq (hld ())
    obtain ⟨hal, tvs', hl, hlen, rfl⟩ := instrNextS_amo hn
    cases hl
    have hk1 := silentRun_stuck rfl hsr
    subst hk1
    have hst' : litNextS (amoMid h op sz rl0 rd rs2 rs1 _) (LAmoSt rl _ data _ vsrc) = some h' := hst
    simp only [litNextS, amoMid] at hst'
    split at hst'
    · rename_i he
      injection he with e1 e2 e3 e4 e5
      subst_vars
      cases hst'
      show litNext h _ = some _
      unfold litNext
      rw [hq0]
      simp only [hpc]
      exact instrNext_amo_intro hal rfl
    · cases hst'

theorem fuseOk_lit : FuseOk litStep litStepS (fun s => qOk s.q) := by
  refine ⟨fun h d l h' d' hq hs => litNext_q hq hs, fun h d l h' d' hq hs => ?_⟩
  have hl := litNext_half hq hs
  have hs' : litNext h l = some h' := hs
  unfold litNext at hs'
  cases hq' : h.q with
  | cons l0 rest =>
    rw [hq'] at hs'
    refine .inl ⟨hl, ?_⟩
    show litNextS h l = some h'
    unfold litNextS
    rw [hq']
    exact hs'
  | nil =>
    rw [hq'] at hs'
    simp only at hs'
    cases hp : h.prog[h.pc]? with
    | none => rw [hp] at hs'; cases hs'
    | some ins =>
      rw [hp] at hs'
      simp only at hs'
      cases ins with
      | amo op sz aq0 rl0 rd rs2 rs1 =>
        obtain ⟨hal, tvs, rfl, hlen, rfl⟩ := instrNext_amo hs'
        refine .inr ⟨aq0, rl0, _, tvs, _, srcR rs1, srcR rs2, amoMid h op sz rl0 rd rs2 rs1 tvs, (),
          amoMid h op sz rl0 rd rs2 rs1 tvs, (), rfl, regOnly_srcR rs1, regOnly_srcR rs2, ?_, .refl _ _, ?_⟩
        · show litNextS h _ = some _
          unfold litNextS
          rw [hq']
          simp only [hp]
          exact instrNextS_amo_intro hal hlen
        · show litNextS _ _ = some _
          simp only [litNextS, amoMid, ↓reduceIte]
      | _ =>
        refine .inl ⟨hl, ?_⟩
        show litNextS h l = some h'
        unfold litNextS
        rw [hq']
        simp only [hp]
        rw [instrNextS_eq (by intro _ _ _ _ _ _ _ he; cases he)]
        exact hs'

/-! ## 5. Observations across `TrRel` -/

theorem loadsOf_sil : ∀ {sil : List (PLabel × Option Nat)}, Weak.Prom.AS.allSil sil → PF.loadsOf sil = []
  | [], _ => rfl
  | x :: sil, h => by
    have hx := h x (by simp)
    subst hx
    simp only [PF.loadsOf, List.filterMap_cons, PF.loadLikeTvs]
    exact loadsOf_sil (fun y hy => h y (List.mem_cons_of_mem _ hy))

theorem loadsOf_trRel {f s : List (PLabel × Option Nat)} (h : TrRel f s) : PF.loadsOf f = PF.loadsOf s := by
  induction h with
  | nil => rfl
  | keep f s l o _ _ ih =>
    simp only [PF.loadsOf, List.filterMap_append] at ih ⊢
    rw [ih]
  | amo f s aq rl base tvs data asrc vsrc ts sil _ hsil ih =>
    have := loadsOf_sil hsil
    simp only [PF.loadsOf, List.filterMap_append, List.filterMap_cons, PF.loadLikeTvs] at ih this ⊢
    rw [ih, this]
    simp

theorem machRow_trRel {f s : List (PLabel × Option Nat)} (h : TrRel f s) : machRow f = machRow s := by
  unfold machRow
  rw [loadsOf_trRel h]

theorem progs_qNil (T : Test) : ∀ p ∈ progs T, p.q = [] := by
  intro p hp
  simp only [progs, List.mem_map] at hp
  obtain ⟨_, _, rfl⟩ := hp
  rfl

theorem promisesFirst_factor (L : List PMsg) (evs : List PEvt) :
    promisesFirst (L.map promEv ++ evs.filter PEvt.isSt) := by
  refine ⟨L.length, fun e he => ?_, fun e he => ?_⟩
  · rw [List.take_left' (by simp)] at he
    obtain ⟨m, _, rfl⟩ := List.mem_map.1 he
    rfl
  · rw [List.drop_left' (by simp)] at he
    exact (List.mem_filter.1 he).2

/-! ## 6. The corollaries -/

/-- **(T-cmp) WITH SAIL'S SPLIT AMO** (`rvwmo_complete` + `amoSplitFused`): every single-size reference execution
of an S3b program is a valid run of machine v2 over the SPLIT front end `litStepS`, promises first, every hart
done, with the same per-hart load observations, final registers and final memory. -/
theorem rvwmo_complete_split (T : Test) (hT : progS3bB T = true) {chs : List (List Bool)} {trs : List SSt}
    {ν : Val} {g : List EvId} (hrun : T.runAll chs = some trs) (hc : condsOk ν trs = true)
    (hX : rvwmoRef (conc T trs ν g)) (hss : singleSize (conc T trs ν g)) (hpo : platformOrd (conc T trs ν g)) :
    ∃ run : PF.PFRun LP Unit,
      PF.validRun litStepS (testImg T) () (progs T) (memOf (conc T trs ν g)) run ∧ promisesFirst run.evs ∧
      run.cfg.pcAgs.length = T.harts.length ∧ allDone run.cfg ∧
      (∀ h, machRow (run.trace h) = refRow (conc T trs ν g) h) ∧
      (∀ h r, regOf run.cfg h r = finalReg trs ν h r) ∧
      (∀ a n, finalMem (testImg T) (memOf (conc T trs ν g)) a n = refFinalMem (conc T trs ν g) a n) := by
  obtain ⟨run, ⟨hv, hM⟩, _, hlen, hdone, hrow, hreg, hmem⟩ := rvwmo_complete T hT hrun hc hX hss hpo
  obtain ⟨evsS, hvS, htr⟩ := fusedToSplit fuseOk_lit (fun p hp => by rw [progs_qNil T p hp]; exact qOk_nil) hv
  obtain ⟨evs', hv', he', htr'⟩ := validRun_factorL_trace hvS
  refine ⟨⟨evs', run.cfg⟩, ⟨hv', hM⟩, he' ▸ promisesFirst_factor _ _, hlen, hdone, fun h => ?_, hreg, hmem⟩
  show machRow (traceOf h evs') = _
  rw [htr' h, ← machRow_trRel (htr h)]
  exact hrow h

/-- A split hart between its halves has a non-empty queue. -/
theorem pendS_q {hk : LP} (h : pendS litStepS (fun s => qOkS s.q) hk) : hk.q ≠ [] := by
  obtain ⟨h0, aq, base, tvs, asrc, h1, hq, hld, hsr⟩ := h
  obtain ⟨op, sz, rl0, rd, rs2, rs1, _, _, hn⟩ := litNextS_ld hq (hld ())
  obtain ⟨_, _, _, _, rfl⟩ := instrNextS_amo hn
  rw [silentRun_stuck rfl hsr]
  simp [amoMid]

/-- **THE LOGIC TRANSFERS TO SPLIT AMOs** (`amoSplitFused`): a property of the load observations and final memory
of every finished valid `litStep` run holds of every finished valid `litStepS` run. -/
theorem litS_of_lit (T : Test) (Q : (Nat → Nat → Option Nat) → (Nat → Nat → Nat) → Prop)
    (hlit : ∀ (M : List PMsg) (run : PF.PFRun LP Unit), PF.validRun litStep (testImg T) () (progs T) M run →
      (∀ h, h < T.harts.length → run.done PF.litDone h ()) → Q run.obsLoad (finalMem (testImg T) M)) :
    ∀ (M : List PMsg) (run : PF.PFRun LP Unit), PF.validRun litStepS (testImg T) () (progs T) M run →
      (∀ h, h < T.harts.length → run.done PF.litDone h ()) → Q run.obsLoad (finalMem (testImg T) M) := by
  intro M run ⟨hv, hM⟩ hdone
  have hlen : run.cfg.pcAgs.length = T.harts.length := by
    rw [pmSteps_len hv.1]; simp [pmInit, progs]
  have hcl : closedS litStepS (fun s => qOkS s.q) run.cfg := by
    intro k ag hk
    right
    intro hp
    have hlt : k < T.harts.length := by rw [← hlen]; exact (List.getElem?_eq_some_iff.1 hk).1
    obtain ⟨ag', h1, h2⟩ := hdone k hlt
    rw [hk] at h1
    cases h1
    unfold PF.litDone at h2
    split at h2
    · rename_i hq
      exact pendS_q hp hq.1
    · cases h2
  obtain ⟨evsF, hvF, htr⟩ := splitToFused_closed splitOk_lit
    (fun p hp => by rw [progs_qNil T p hp]; exact .inl qOk_nil) hv hcl
  have hobs : (⟨evsF, run.cfg⟩ : PF.PFRun LP Unit).obsLoad = run.obsLoad := by
    funext h k
    simp only [PF.PFRun.obsLoad, PF.PFRun.trace]
    rw [loadsOf_trRel (htr h)]
  have := hlit M ⟨evsF, run.cfg⟩ ⟨hvF, hM⟩ hdone
  rwa [hobs] at this

end Weak.Prom.Cmp
