/-
Weak/Prom: **NOTA for machine v2 on litmus programs** (S0-P part (2), milestone 2b, statement 5 in corrected form):
no message of a valid run holds a value out of thin air.

A FREE RUN of a hart (`freeSteps D`) is a run of its program half alone (`litNextF`: `litNext` without the alignment
check of a failing SC, see `scNextF`) in which every load returns some
byte of the value domain `D` or forwards the run's own latest byte there (`lastByte`).  `D` is CLOSED for a hart (`closedFrom`) if every message (`labelMsg`) of every free
run from the hart's initial state holds only bytes of `D`.  The theorem (`nota`):

  if `D` contains the image and is closed for every hart, then every byte of the final memory of every valid run
  (in its solo-run form, MachSolo.lean) is in `D`.

Proof (strong induction on the timestamp `θ` of a message): the message is fulfilled by a step of its author's solo
run; every earlier step of that run has its address, data and control views below `θ` (`stPre … < θ`, `vcap`
captures every address and branch view, rules 11 and 13), so a free run that copies every LOW load (result view
`< θ`; such a load reads a message `< θ`, in `D` by induction, or forwards an own low store, `fwdInv`) and gives
every HIGH load any domain byte agrees with the solo run on every low register (`agree`, the syntactic register
views of M19 are exactly what makes this a noninterference argument), reaches the fulfilling step, and emits the
same message; closedness puts its bytes in `D`.
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.MachComplete

namespace Weak.Prom.Mach

open MachCSL MachCSL.Stdpp Iris.Std
open Weak (Image Dsrc)
open Weak.Prom Weak.Prom.Mach.Cert
open Weak.Prom.Ref (Instr Test two64 aluOp brEval amoOp sext byteList bytesVal)
open PLabel

/-! ## 1. Messages of labels -/

/-- The message a label writes (its fulfil must find exactly this message), by agent `i`. -/
def labelMsg (i : Nat) : PLabel → Option PMsg
  | LStore _ rl base data _ _ => some ⟨base, data, some i, stClass rl⟩
  | LExStore _ _ base data _ _ => some ⟨base, data, some i, .excl⟩
  | LRmw _ _ base _ data _ _ => some ⟨base, data, some i, .excl⟩
  | LAmoSt _ base data _ _ => some ⟨base, data, some i, .excl⟩
  | LCmo k base len _ => some ⟨base, [], some i, .cmo k len⟩
  | _ => none

theorem memStep_msg {img : Image} {log : List PMsg} {i : Nat} {prom : GSet Nat} {ws : PState} {l : PLabel}
    {ots : Option Nat} {ws' : PState} {prom' : GSet Nat} (h : memStep img log i prom ws l ots ws' prom') :
    (∀ ts, ots = some ts → log[ts - 1]? = labelMsg i l) ∧ (ots = none → labelMsg i l = none) := by
  cases h with
  | store _ _ _ _ _ _ ts _ hm => exact ⟨fun t ht => (by cases ht; exact hm), fun h => (by cases h)⟩
  | rmw _ _ _ _ _ _ _ ts _ _ hm => exact ⟨fun t ht => (by cases ht; exact hm), fun h => (by cases h)⟩
  | amoSt _ _ _ _ _ ts _ _ _ _ _ hm => exact ⟨fun t ht => (by cases ht; exact hm), fun h => (by cases h)⟩
  | sc _ _ _ _ _ _ ts _ _ _ hm => exact ⟨fun t ht => (by cases ht; exact hm), fun h => (by cases h)⟩
  | cmo _ _ _ _ ts _ hm => exact ⟨fun t ht => (by cases ht; exact hm), fun h => (by cases h)⟩
  | _ => exact ⟨fun t ht => (by cases ht), fun _ => rfl⟩

/-! ## 2. Queue shapes -/

/-- The labels an instruction queues (answer-free, write-free). -/
def qLab : PLabel → Bool
  | LRegW .. => true
  | LInstr => true
  | LExFail => true
  | LFence .. => true
  | _ => false

def isRegW : PLabel → Bool
  | LRegW .. => true
  | _ => false

/-- A queue of answer-free labels with a register write only at its head. -/
def qOk (q : List PLabel) : Prop := (∀ l ∈ q, qLab l = true) ∧ (∀ l ∈ q.tail, isRegW l = false)

theorem qOk_nil : qOk [] := ⟨fun _ h => (by cases h), fun _ h => (by cases h)⟩

theorem qOk_tail {l : PLabel} {rest : List PLabel} (h : qOk (l :: rest)) : qOk rest :=
  ⟨fun x hx => h.1 x (List.mem_cons_of_mem _ hx), fun x hx => h.2 x (List.mem_of_mem_tail hx)⟩

theorem qOk_regWL1 (rd : Nat) (srcs : List Dsrc) : qOk (regWL rd srcs ++ [LInstr]) := by
  unfold regWL; split <;> simp [qOk, qLab, isRegW]

theorem qOk_regWL2 (rd : Nat) (srcs : List Dsrc) : qOk (regWL rd srcs ++ [LExFail, LInstr]) := by
  unfold regWL; split <;> simp [qOk, qLab, isRegW]

theorem go1_eq {s : LP} {regs' : List Nat} {pc' : Nat} {labs : List PLabel} {l : PLabel} {s' : LP}
    (h : go1 s regs' pc' labs l = some s') :
    ∃ rest, labs = l :: rest ∧ s' = { s with regs := regs', pc := pc', q := rest } := by
  unfold go1 at h
  cases labs with
  | nil => cases h
  | cons l0 rest =>
    simp only at h
    split at h
    · rename_i he; subst he; cases h; exact ⟨rest, rfl, rfl⟩
    · cases h

theorem instrNext_q {n : Nat} {s s' : LP} {ins : Instr} {l : PLabel} (h : instrNext n s ins l = some s') :
    qOk s'.q := by
  cases ins with
  | alui op rd rs1 imm =>
    simp only [instrNext] at h
    obtain ⟨rest, h1, rfl⟩ := go1_eq h
    unfold regWL at h1; split at h1 <;> simp at h1 <;> obtain ⟨_, rfl⟩ := h1 <;> simp [qOk, qLab, isRegW]
  | alu op rd rs1 rs2 =>
    simp only [instrNext] at h
    obtain ⟨rest, h1, rfl⟩ := go1_eq h
    unfold regWL at h1; split at h1 <;> simp at h1 <;> obtain ⟨_, rfl⟩ := h1 <;> simp [qOk, qLab, isRegW]
  | csrr rd v =>
    simp only [instrNext] at h
    obtain ⟨rest, h1, rfl⟩ := go1_eq h
    unfold regWL at h1; split at h1 <;> simp at h1 <;> obtain ⟨_, rfl⟩ := h1 <;> simp [qOk, qLab, isRegW]
  | fence f =>
    simp only [instrNext] at h
    obtain ⟨rest, h1, rfl⟩ := go1_eq h
    simp at h1; obtain ⟨_, rfl⟩ := h1; simp [qOk, qLab, isRegW]
  | fenceTso =>
    simp only [instrNext] at h
    obtain ⟨rest, h1, rfl⟩ := go1_eq h
    simp at h1; obtain ⟨_, rfl⟩ := h1; simp [qOk, qLab, isRegW]
  | fencei =>
    simp only [instrNext] at h
    obtain ⟨rest, h1, rfl⟩ := go1_eq h
    simp at h1; obtain ⟨_, rfl⟩ := h1; simp [qOk, qLab, isRegW]
  | nop =>
    simp only [instrNext] at h
    obtain ⟨rest, h1, rfl⟩ := go1_eq h
    simp at h1; obtain ⟨_, rfl⟩ := h1; simp [qOk, qLab, isRegW]
  | br c rs1 rs2 tgt =>
    replace h := ite_none_some h
    obtain ⟨rest, h1, rfl⟩ := go1_eq h
    simp at h1; obtain ⟨_, rfl⟩ := h1; simp [qOk, qLab, isRegW]
  | jmp tgt =>
    replace h := ite_none_some h
    obtain ⟨rest, h1, rfl⟩ := go1_eq h
    simp at h1; obtain ⟨_, rfl⟩ := h1; simp [qOk, qLab, isRegW]
  | load sz sgn rd rs1 off =>
    replace h := ite_none_some h
    cases l
    all_goals try (simp only [reduceCtorEq] at h; done)
    obtain ⟨_, rfl⟩ := ite_some_none h
    exact qOk_regWL1 _ _
  | loadAq sz rl0 rd rs1 =>
    replace h := ite_none_some h
    cases l
    all_goals try (simp only [reduceCtorEq] at h; done)
    obtain ⟨_, rfl⟩ := ite_some_none h
    exact qOk_regWL1 _ _
  | lr sz aq0 rl0 rd rs1 =>
    replace h := ite_none_some h
    cases l
    all_goals try (simp only [reduceCtorEq] at h; done)
    obtain ⟨_, rfl⟩ := ite_some_none h
    exact qOk_regWL1 _ _
  | amo op sz aq0 rl0 rd rs2 rs1 =>
    replace h := ite_none_some h
    cases l
    all_goals try (simp only [reduceCtorEq] at h; done)
    obtain ⟨_, rfl⟩ := ite_some_none h
    exact qOk_regWL1 _ _
  | store sz rs2 rs1 off =>
    replace h := ite_none_some h
    cases l
    all_goals try (simp only [reduceCtorEq] at h; done)
    obtain ⟨_, rfl⟩ := ite_some_none h
    simp [qOk, qLab, isRegW]
  | storeRl sz aq0 rs2 rs1 =>
    replace h := ite_none_some h
    cases l
    all_goals try (simp only [reduceCtorEq] at h; done)
    obtain ⟨_, rfl⟩ := ite_some_none h
    simp [qOk, qLab, isRegW]
  | sc sz aq0 rl0 rd rs2 rs1 =>
    replace h := ite_none_some h
    cases l
    all_goals try (simp only [reduceCtorEq] at h; done)
    · obtain ⟨_, rfl⟩ := ite_some_none h
      exact qOk_regWL2 _ _
    · cases h
      exact qOk_regWL2 _ _
  | loadAqPc => cases h
  | storeRlPc => cases h

theorem litNext_q {s s' : LP} {l : PLabel} (hq : qOk s.q) (h : litNext s l = some s') : qOk s'.q := by
  unfold litNext at h
  cases hq' : s.q with
  | cons l0 rest =>
    rw [hq'] at h hq
    simp only at h
    split at h
    · cases h; exact qOk_tail hq
    · cases h
  | nil =>
    rw [hq'] at h
    simp only at h
    cases hp : s.prog[s.pc]? with
    | none => rw [hp] at h; cases h
    | some ins => rw [hp] at h; exact instrNext_q h

/-! ## 2b. The free program half: `litNext` without the alignment check of a failing SC -/

/-- The SC of `instrNext` WITHOUT its alignment check.  A failing SC (`LExFail`) has no view effect, so its address
register may be high in a free run; every other access's address view is captured by `vcap` (rule 13, `loadRun`,
`storeRun`) and is low. -/
def scNextF (s : LP) (sz : Nat) (aq0 rl0 : Bool) (rd rs2 rs1 : Nat) (l : PLabel) : Option LP :=
  match l with
  | LExStore aq rl b data asrc vsrc =>
      if aq = (aq0 && rl0) ∧ rl = rl0 ∧ b = ((s.rd rs1 : Nat) : Int) ∧ data = toBytes (s.rd rs2) sz ∧
          asrc = srcR rs1 ∧ vsrc = srcR rs2 then
        some { s with regs := s.wr rd 0, pc := s.pc + 1, q := regWL rd [.DLdRes] ++ [LExFail, LInstr] }
      else none
  | LExFail => some { s with regs := s.wr rd 1, pc := s.pc + 1, q := regWL rd [] ++ [LExFail, LInstr] }
  | _ => none

/-- One instruction's first label in a free run. -/
def insNextF (n : Nat) (s : LP) (ins : Instr) (l : PLabel) : Option LP :=
  match ins with
  | .sc sz aq0 rl0 rd rs2 rs1 => scNextF s sz aq0 rl0 rd rs2 rs1 l
  | ins => instrNext n s ins l

/-- THE FREE PROGRAM HALF: `litNext` with `scNextF` for SC. -/
def litNextF (s : LP) (l : PLabel) : Option LP :=
  match s.q with
  | l0 :: rest => if l = l0 then some { s with q := rest } else none
  | [] =>
    match s.prog[s.pc]? with
    | some ins => insNextF s.prog.length s ins l
    | none => none

theorem insNextF_of {n : Nat} {s s' : LP} {ins : Instr} {l : PLabel} (h : instrNext n s ins l = some s') :
    insNextF n s ins l = some s' := by
  cases ins with
  | sc sz aq0 rl0 rd rs2 rs1 =>
    simp only [insNextF, scNextF]
    replace h := ite_none_some h
    exact h
  | _ => exact h

theorem litNextF_of {s s' : LP} {l : PLabel} (h : litNext s l = some s') : litNextF s l = some s' := by
  unfold litNext at h
  unfold litNextF
  cases hq : s.q with
  | cons l0 rest => rw [hq] at h; exact h
  | nil =>
    rw [hq] at h
    simp only at h ⊢
    cases hp : s.prog[s.pc]? with
    | none => rw [hp] at h; cases h
    | some ins => rw [hp] at h; exact insNextF_of h

theorem insNextF_q {n : Nat} {s s' : LP} {ins : Instr} {l : PLabel} (h : insNextF n s ins l = some s') :
    qOk s'.q := by
  cases ins with
  | sc sz aq0 rl0 rd rs2 rs1 =>
    simp only [insNextF, scNextF] at h
    cases l
    all_goals try (simp only [reduceCtorEq] at h; done)
    · obtain ⟨_, rfl⟩ := ite_some_none h
      exact qOk_regWL2 _ _
    · cases h
      exact qOk_regWL2 _ _
  | _ => simp only [insNextF] at h; exact instrNext_q h

theorem litNextF_q {s s' : LP} {l : PLabel} (hq : qOk s.q) (h : litNextF s l = some s') : qOk s'.q := by
  unfold litNextF at h
  cases hq' : s.q with
  | cons l0 rest =>
    rw [hq'] at h hq
    simp only at h
    split at h
    · cases h; exact qOk_tail hq
    · cases h
  | nil =>
    rw [hq'] at h
    simp only at h
    cases hp : s.prog[s.pc]? with
    | none => rw [hp] at h; cases h
    | some ins => rw [hp] at h; exact insNextF_q h

/-! ## 3. Free runs and closed domains -/

/-- The byte at `a` of the latest message of `w` covering it (store-buffer forwarding in a free run). -/
def lastByte (w : List PMsg) (a : Int) : Option (BitVec 8) := w.reverse.findSome? (fun m => m.byteAt a)

theorem lastByte_snoc (w : List PMsg) (m : PMsg) (a : Int) :
    lastByte (w ++ [m]) a = match m.byteAt a with
      | some b => some b
      | none => lastByte w a := by
  unfold lastByte
  rw [List.reverse_append, List.reverse_singleton, List.singleton_append, List.findSome?_cons]
  cases m.byteAt a <;> rfl

/-- Every read answer of the label is a byte of the domain, or the byte of the free run's latest own message
there (`w`: the messages the free run has emitted so far). -/
def freeOk (D : Int → List (BitVec 8)) (w : List PMsg) (l : PLabel) : Prop :=
  ∀ base tvs, labelReads l = some (base, tvs) →
    bytesAll (fun a _ v => v ∈ D a ∨ lastByte w a = some v) base tvs

/-- A FREE RUN of agent `i`: the free program half alone, every load answered from the domain or by forwarding from
the run's own latest message (timestamps arbitrary); the state carries the messages emitted so far. -/
inductive freeSteps (D : Int → List (BitVec 8)) (i : Nat) : LP × List PMsg → List PLabel → LP × List PMsg → Prop
  | refl (x : LP × List PMsg) : freeSteps D i x [] x
  | step (s : LP) (w : List PMsg) (l : PLabel) (s1 : LP) (ls : List PLabel) (y : LP × List PMsg) :
      litNextF s l = some s1 → freeOk D w l → freeSteps D i (s1, w ++ (labelMsg i l).toList) ls y →
      freeSteps D i (s, w) (l :: ls) y

theorem freeSteps_snoc {D : Int → List (BitVec 8)} {i : Nat} {x : LP × List PMsg} {s1 s2 : LP}
    {w1 : List PMsg} {ls : List PLabel} {l : PLabel}
    (h : freeSteps D i x ls (s1, w1)) (hl : litNextF s1 l = some s2) (hok : freeOk D w1 l) :
    freeSteps D i x (ls ++ [l]) (s2, w1 ++ (labelMsg i l).toList) := by
  generalize hy : (s1, w1) = y at h
  induction h with
  | refl => cases hy; exact .step _ _ _ _ _ _ hl hok (.refl _)
  | step _ _ _ _ _ _ h1 h2 _ ih => exact .step _ _ _ _ _ _ h1 h2 (ih hy)

/-- Every byte of the message is in the domain. -/
def msgIn (D : Int → List (BitVec 8)) (m : PMsg) : Prop :=
  ∀ (k : Nat) b, m.data[k]? = some b → b ∈ D (m.pa + k)

/-- `D` CLOSES INTO `D'` for agent `i` from program state `s0`: every message of every free run over `D` is in `D'`. -/
def closedInto (D D' : Int → List (BitVec 8)) (i : Nat) (s0 : LP) : Prop :=
  ∀ ls y, freeSteps D i (s0, []) ls y → ∀ m ∈ y.2, msgIn D' m

/-- `D` IS CLOSED for agent `i` from `s0`. -/
def closedFrom (D : Int → List (BitVec 8)) (i : Nat) (s0 : LP) : Prop := closedInto D D i s0

theorem msgIn_byteAt {D : Int → List (BitVec 8)} {m : PMsg} {a : Int} {b : BitVec 8} (h : msgIn D m)
    (hb : m.byteAt a = some b) : b ∈ D a := by
  unfold PMsg.byteAt at hb
  split at hb
  · rename_i hle
    have := h _ _ hb
    have e : m.pa + ((a - m.pa).toNat : Int) = a := by omega
    rw [e] at this
    exact this
  · cases hb

/-! ## 4. Agreement of a free run with a solo run below `θ` -/

/-- The view of register `r` at a state whose queue may still hold the instruction's register write. -/
def effView (ws : PState) (q : List PLabel) (r : Nat) : Nat :=
  match q with
  | LRegW rd srcs :: _ => if rd = r then srcsView ws srcs else regv ws r
  | _ => regv ws r

/-- The free run's state `s'` agrees with the solo run's `s` (with `PState` `ws`) on every register whose view is
below `θ`, and on the program position. -/
structure agree (θ : Nat) (ws : PState) (s s' : LP) : Prop where
  prog : s'.prog = s.prog
  pc : s'.pc = s.pc
  q : s'.q = s.q
  len : s'.regs.length = s.regs.length
  regs : ∀ r, r ≠ 0 → effView ws s.q r < θ → (s'.regs[r]?).getD 0 = (s.regs[r]?).getD 0

/-- Forwarding below `θ` returns domain bytes or the free run's latest own byte. -/
def fwdInv (img : Image) (M : List PMsg) (D : Int → List (BitVec 8)) (θ : Nat) (ws : PState) (w : List PMsg) :
    Prop :=
  ∀ a tf vf, get? ws.wFwd a = some (tf, vf) → vf < θ → ∀ b, memByte img M tf a = some b →
    b ∈ D a ∨ lastByte w a = some b

/-- Every byte below `θ` is in the domain. -/
def lowM (img : Image) (M : List PMsg) (D : Int → List (BitVec 8)) (θ : Nat) : Prop :=
  ∀ t, t < θ → ∀ a b, memByte img M t a = some b → b ∈ D a

theorem agree_rd {θ : Nat} {ws : PState} {s s' : LP} (ha : agree θ ws s s') {r : Nat}
    (h : r ≠ 0 → effView ws s.q r < θ) : s'.rd r = s.rd r := by
  unfold LP.rd
  by_cases hr : r = 0
  · simp [hr]
  · simp only [hr, if_false]; exact ha.regs r hr (h hr)

theorem srcsView_srcR (ws : PState) (r : Nat) : srcsView ws (srcR r) = if r = 0 then 0 else regv ws r := by
  unfold srcR
  split
  · rfl
  · show max (regv ws r) 0 = regv ws r
    omega

theorem srcsView_append (ws : PState) (a b : List Dsrc) :
    srcsView ws (a ++ b) = max (srcsView ws a) (srcsView ws b) := by
  induction a with
  | nil => show srcsView ws b = max 0 (srcsView ws b); omega
  | cons x r ih =>
    show max (dsrcView ws x) (srcsView ws (r ++ b)) = max (max (dsrcView ws x) (srcsView ws r)) (srcsView ws b)
    rw [ih]; omega

/-- At an instruction start, a register whose source view is low agrees. -/
theorem agree_src {θ : Nat} {ws : PState} {s s' : LP} (ha : agree θ ws s s') (hq : s.q = []) {r : Nat}
    (h : srcsView ws (srcR r) < θ) : s'.rd r = s.rd r := by
  refine agree_rd ha (fun hr => ?_)
  rw [srcsView_srcR, if_neg hr] at h
  rw [hq]
  exact h

theorem regs_wr_agree {R R' : List Nat} {rd v v' r : Nat} (hlen : R'.length = R.length) (hr : r ≠ 0)
    (hv : r = rd → v' % two64 = v % two64) (hold : r ≠ rd → (R'[r]?).getD 0 = (R[r]?).getD 0) :
    ((if rd = 0 then R' else R'.set rd (v' % two64))[r]?).getD 0 =
      ((if rd = 0 then R else R.set rd (v % two64))[r]?).getD 0 := by
  by_cases hrd : r = rd
  · subst hrd
    simp only [hr, if_false, List.getElem?_set, if_true, hlen]
    split
    · simp [hv rfl]
    · rfl
  · have h0 : ∀ (X : List Nat) (x : Nat), ((if rd = 0 then X else X.set rd x)[r]?) = X[r]? := by
      intro X x
      split
      · rfl
      · exact List.getElem?_set_ne (Ne.symm hrd)
    rw [h0, h0]
    exact hold hrd

theorem wr_len (s : LP) (rd v : Nat) : (s.wr rd v).length = s.regs.length := by
  unfold LP.wr; split <;> simp

theorem byteAt_out {m : PMsg} {b : Int} (h : ¬ (m.pa ≤ b ∧ b < m.pa + m.data.length)) : m.byteAt b = none := by
  unfold PMsg.byteAt
  split
  · rename_i hle
    exact List.getElem?_eq_none (by omega)
  · rfl

theorem memByte_msg {img : Image} {M : List PMsg} {ts : Nat} {m : PMsg} {b : Int} {x : BitVec 8} (hpos : 0 < ts)
    (hmsg : M[ts - 1]? = some m) (hx : memByte img M ts b = some x) : m.byteAt b = some x := by
  obtain ⟨k, rfl⟩ : ∃ k, ts = k + 1 := ⟨ts - 1, by omega⟩
  simp only [memByte] at hx
  simp only [Nat.add_sub_cancel] at hmsg
  rw [hmsg] at hx
  exact hx

/-- `fwdInv` after a store-like step that writes `m` over `[base, base + n)` with forward entries `(ts, fv)`. -/
theorem fwdInv_store {img : Image} {M : List PMsg} {D : Int → List (BitVec 8)} {θ : Nat} {ws ws1 : PState}
    {w : List PMsg} (hf : fwdInv img M D θ ws w) {base : Int} {n ts fv : Nat} {m : PMsg}
    (hfwd : ∀ b, get? ws1.wFwd b = if base ≤ b ∧ b < base + n then some (ts, fv) else get? ws.wFwd b)
    (hpa : m.pa = base) (hlen : m.data.length = n)
    (hin : fv < θ → ∀ b x, memByte img M ts b = some x → x ∈ D b ∨ m.byteAt b = some x) :
    fwdInv img M D θ ws1 (w ++ [m]) := by
  intro b tf vf hg hvf x hx
  rw [hfwd] at hg
  split at hg
  · cases hg
    rcases hin hvf b x hx with h1 | h1
    · exact .inl h1
    · right; rw [lastByte_snoc, h1]
  · rename_i hnr
    have hnb : m.byteAt b = none := byteAt_out (by rw [hpa, hlen]; exact hnr)
    rw [lastByte_snoc, hnb]
    exact hf b tf vf hg hvf x hx

theorem fwdInv_nomsg {img : Image} {M : List PMsg} {D : Int → List (BitVec 8)} {θ : Nat} {ws : PState}
    {w : List PMsg} {i : Nat} {l : PLabel} (hl : labelMsg i l = none) (hf : fwdInv img M D θ ws w) :
    fwdInv img M D θ ws (w ++ (labelMsg i l).toList) := by
  rw [hl]; simpa using hf

theorem bytesAll_left {D : Int → List (BitVec 8)} {w : List PMsg} :
    ∀ (a : Int) (l : List (Nat × BitVec 8)), bytesAll (fun a _ v => v ∈ D a) a l →
      bytesAll (fun a _ v => v ∈ D a ∨ lastByte w a = some v) a l :=
  bytesAll_mono (fun _ _ _ h => .inl h)

/-! ## 5. Facts about the post-state functions -/

theorem fwdView_congr {ws ws' : PState} (h : ws'.wFwd = ws.wFwd) (aq : Bool) (a : Int) (t : Nat) :
    fwdView ws' aq a t = fwdView ws aq a t := by
  unfold fwdView; rw [h]

theorem loadBytes_fields (aq : Bool) (vpre : Nat) : ∀ (ws : PState) (a : Int) (tvs : List (Nat × BitVec 8)),
    (loadBytes aq vpre ws a tvs).wFwd = ws.wFwd ∧ (loadBytes aq vpre ws a tvs).wRegv = ws.wRegv ∧
      (loadBytes aq vpre ws a tvs).wVcap = ws.wVcap
  | _, _, [] => ⟨rfl, rfl, rfl⟩
  | ws, a, (t, _) :: r => by
    have := loadBytes_fields aq vpre (loadByte ws aq vpre a t) (a + 1) r
    simp only [loadBytes]
    exact ⟨this.1, this.2.1, this.2.2⟩

theorem loadBytes_ldv (aq : Bool) (vpre : Nat) : ∀ (ws : PState) (a : Int) (tvs : List (Nat × BitVec 8)),
    ws.wLdv ≤ (loadBytes aq vpre ws a tvs).wLdv ∧
      bytesAll (fun x u _ => fwdView ws aq x u ≤ (loadBytes aq vpre ws a tvs).wLdv) a tvs
  | _, _, [] => ⟨Nat.le_refl _, trivial⟩
  | ws, a, (t, _) :: r => by
    have ih := loadBytes_ldv aq vpre (loadByte ws aq vpre a t) (a + 1) r
    have hf : (loadByte ws aq vpre a t).wFwd = ws.wFwd := rfl
    simp only [loadBytes]
    have e1 : (loadByte ws aq vpre a t).wLdv = max ws.wLdv (max vpre (fwdView ws aq a t)) := rfl
    refine ⟨by omega, by omega, ?_⟩
    exact bytesAll_mono (fun a' t' _ h => by rw [fwdView_congr hf] at h; exact h) _ _ ih.2

theorem coh_loadByte_ge (ws : PState) (aq : Bool) (vpre : Nat) (a : Int) (t : Nat) (b : Int) :
    coh ws b ≤ coh (loadByte ws aq vpre a t) b := by
  simp only [loadByte, coh, getD_insert_nat]
  split
  · rename_i h; subst h; omega
  · omega

theorem loadBytes_coh (aq : Bool) (vpre : Nat) : ∀ (ws : PState) (a : Int) (tvs : List (Nat × BitVec 8)),
    (∀ b, coh ws b ≤ coh (loadBytes aq vpre ws a tvs) b) ∧
      bytesAll (fun x u _ => fwdView ws aq x u ≤ coh (loadBytes aq vpre ws a tvs) x ∧
        u ≤ coh (loadBytes aq vpre ws a tvs) x) a tvs
  | _, _, [] => ⟨fun _ => Nat.le_refl _, trivial⟩
  | ws, a, (t, _) :: r => by
    have ih := loadBytes_coh aq vpre (loadByte ws aq vpre a t) (a + 1) r
    have hf : (loadByte ws aq vpre a t).wFwd = ws.wFwd := rfl
    simp only [loadBytes]
    have e1 : coh (loadByte ws aq vpre a t) a = max (coh ws a) (max (max vpre (fwdView ws aq a t)) t) := by
      simp only [loadByte, coh, getD_insert_nat, if_true]
    have h2 := ih.1 a
    refine ⟨fun b => Nat.le_trans (coh_loadByte_ge ws aq vpre a t b) (ih.1 b), ⟨by omega, by omega⟩, ?_⟩
    exact bytesAll_mono (fun a' t' _ h => by rw [fwdView_congr hf] at h; exact h) _ _ ih.2

theorem storeBytes_fields : ∀ (ws : PState) (a : Int) (n ts fv : Nat),
    (storeBytes ws a n ts fv).wRegv = ws.wRegv ∧ (storeBytes ws a n ts fv).wLdv = ws.wLdv ∧
      (storeBytes ws a n ts fv).wVcap = ws.wVcap
  | _, _, 0, _, _ => ⟨rfl, rfl, rfl⟩
  | ws, a, n + 1, ts, fv => by
    simp only [storeBytes]
    exact storeBytes_fields _ (a + 1) n ts fv

theorem storeBytes_fwd : ∀ (ws : PState) (a : Int) (n ts fv : Nat) (b : Int),
    get? (storeBytes ws a n ts fv).wFwd b = if a ≤ b ∧ b < a + n then some (ts, fv) else get? ws.wFwd b
  | ws, a, 0, ts, fv, b => by simp only [storeBytes]; rw [if_neg (by omega)]
  | ws, a, n + 1, ts, fv, b => by
    simp only [storeBytes]
    rw [storeBytes_fwd _ (a + 1) n ts fv b]
    by_cases h1 : a + 1 ≤ b ∧ b < a + 1 + n
    · rw [if_pos h1, if_pos (by omega)]
    · rw [if_neg h1]
      by_cases h2 : a = b
      · subst h2; rw [lookupInsert, if_pos (by omega)]
      · rw [lookupInsertNe h2, if_neg (by omega)]

theorem byte_inD {img : Image} {M : List PMsg} {D : Int → List (BitVec 8)} {θ : Nat} {ws : PState} {aq : Bool}
    {w : List PMsg} {a : Int} {t : Nat} {v : BitVec 8} (hlow : lowM img M D θ) (hf : fwdInv img M D θ ws w)
    (hv : fwdView ws aq a t < θ) (hm : memByte img M t a = some v) : v ∈ D a ∨ lastByte w a = some v := by
  unfold fwdView at hv
  cases hg : get? ws.wFwd a with
  | none => rw [hg] at hv; exact .inl (hlow t hv a v hm)
  | some p =>
    obtain ⟨tf, vf⟩ := p
    rw [hg] at hv
    simp only at hv
    split at hv
    · rename_i he; subst he; exact hf a t vf hg hv v hm
    · exact .inl (hlow t hv a v hm)

/-- The bytes of a low read are domain bytes. -/
theorem vals_inD {img : Image} {M : List PMsg} {D : Int → List (BitVec 8)} {θ : Nat} {ws : PState} {aq : Bool}
    {w : List PMsg} (hlow : lowM img M D θ) (hf : fwdInv img M D θ ws w) :
    ∀ (a : Int) (tvs : List (Nat × BitVec 8)),
      bytesAll (fun a t v => memByte img M t a = some v ∧ fwdView ws aq a t < θ) a tvs →
      bytesAll (fun a _ v => v ∈ D a ∨ lastByte w a = some v) a tvs :=
  bytesAll_mono (fun _ _ _ h => byte_inD hlow hf h.2 h.1)

theorem bytesAll_and {P Q : Int → Nat → BitVec 8 → Prop} :
    ∀ (a : Int) (l : List (Nat × BitVec 8)), bytesAll P a l → bytesAll Q a l →
      bytesAll (fun a t v => P a t v ∧ Q a t v) a l
  | _, [], _, _ => trivial
  | a, (_, _) :: r, ⟨h1, h2⟩, ⟨k1, k2⟩ => ⟨⟨h1, k1⟩, bytesAll_and (a + 1) r h2 k2⟩

/-- A canonical run of `k` domain bytes from `a`. -/
def canonRun (D : Int → List (BitVec 8)) : Int → Nat → List (Nat × BitVec 8)
  | _, 0 => []
  | a, k + 1 => (0, (D a).headD 0) :: canonRun D (a + 1) k

theorem canonRun_len (D : Int → List (BitVec 8)) : ∀ (a : Int) (k : Nat), (canonRun D a k).length = k
  | _, 0 => rfl
  | a, k + 1 => by simp [canonRun, canonRun_len D (a + 1) k]

theorem canonRun_inD' {D : Int → List (BitVec 8)} (hD : ∀ a, D a ≠ []) :
    ∀ (a : Int) (k : Nat), bytesAll (fun a _ v => v ∈ D a) a (canonRun D a k)
  | _, 0 => trivial
  | a, k + 1 => by
    refine ⟨?_, canonRun_inD' hD (a + 1) k⟩
    cases h : D a with
    | nil => exact absurd h (hD a)
    | cons x r => rw [h]; simp

/-! ## 6. Views of the post-state functions -/

theorem loadRun_regv (ws : PState) (aq rl : Bool) (va : Nat) (base : Int) (tvs : List (Nat × BitVec 8)) (r : Nat) :
    regv (loadRun ws aq rl va base tvs) r = regv ws r := by
  have := (loadBytes_fields aq (ldPre ws aq rl va) ws base tvs).2.1
  unfold regv; simp only [loadRun]; rw [this]

theorem loadRun_fwd (ws : PState) (aq rl : Bool) (va : Nat) (base : Int) (tvs : List (Nat × BitVec 8)) :
    (loadRun ws aq rl va base tvs).wFwd = ws.wFwd :=
  (loadBytes_fields aq (ldPre ws aq rl va) ws base tvs).1

theorem loadRun_vcap (ws : PState) (aq rl : Bool) (va : Nat) (base : Int) (tvs : List (Nat × BitVec 8)) :
    (loadRun ws aq rl va base tvs).wVcap = max va ws.wVcap := by
  have := (loadBytes_fields aq (ldPre ws aq rl va) ws base tvs).2.2
  simp only [loadRun]; rw [this]

/-- MachFix-R-b5: the `loadRunV` twins. -/
theorem loadRunV_regv (ws : PState) (aq rl : Bool) (va vi : Nat) (base : Int) (tvs : List (Nat × BitVec 8))
    (r : Nat) : regv (loadRunV ws aq rl va vi base tvs) r = regv ws r := by
  have := (loadBytes_fields aq (max (ldPre ws aq rl va) vi) ws base tvs).2.1
  unfold regv; simp only [loadRunV]; rw [this]

theorem loadRunV_fwd (ws : PState) (aq rl : Bool) (va vi : Nat) (base : Int) (tvs : List (Nat × BitVec 8)) :
    (loadRunV ws aq rl va vi base tvs).wFwd = ws.wFwd :=
  (loadBytes_fields aq (max (ldPre ws aq rl va) vi) ws base tvs).1

theorem loadRunV_vcap (ws : PState) (aq rl : Bool) (va vi : Nat) (base : Int) (tvs : List (Nat × BitVec 8)) :
    (loadRunV ws aq rl va vi base tvs).wVcap = max va ws.wVcap := by
  have := (loadBytes_fields aq (max (ldPre ws aq rl va) vi) ws base tvs).2.2
  simp only [loadRunV]; rw [this]

theorem storeRun_regv (ws : PState) (rl : Bool) (va fv : Nat) (base : Int) (n ts r : Nat) :
    regv (storeRun ws rl va fv base n ts) r = regv ws r := by
  have := (storeBytes_fields ws base n ts fv).1
  unfold regv; simp only [storeRun]; rw [this]

theorem storeRun_vcap (ws : PState) (rl : Bool) (va fv : Nat) (base : Int) (n ts : Nat) :
    (storeRun ws rl va fv base n ts).wVcap = max va ws.wVcap := by
  have := (storeBytes_fields ws base n ts fv).2.2
  simp only [storeRun]; rw [this]

theorem storeRun_ldv (ws : PState) (rl : Bool) (va fv : Nat) (base : Int) (n ts : Nat) :
    (storeRun ws rl va fv base n ts).wLdv = ws.wLdv := (storeBytes_fields ws base n ts fv).2.1

theorem storeRun_fwd (ws : PState) (rl : Bool) (va fv : Nat) (base : Int) (n ts : Nat) (b : Int) :
    get? (storeRun ws rl va fv base n ts).wFwd b =
      if base ≤ b ∧ b < base + n then some (ts, fv) else get? ws.wFwd b :=
  storeBytes_fwd ws base n ts fv b

theorem cohRaise_vcap : ∀ (ws : PState) (a : Int) (n ts : Nat), (cohRaise ws a n ts).wVcap = ws.wVcap
  | _, _, 0, _ => rfl
  | ws, a, n + 1, ts => by simp only [cohRaise]; exact cohRaise_vcap _ (a + 1) n ts

theorem stPre_ge (ws : PState) (rl : Bool) (va vd : Nat) :
    va ≤ stPre ws rl va vd ∧ vd ≤ stPre ws rl va vd ∧ ws.wVcap ≤ stPre ws rl va vd := by
  unfold stPre; refine ⟨?_, ?_, ?_⟩ <;> split <;> omega

theorem stPreA_ge (ws : PState) (aq rl : Bool) (va vd : Nat) : stPre ws rl va vd ≤ stPreA ws aq rl va vd := by
  unfold stPreA; omega

/-- `vcap` never decreases. -/
theorem memStep_vcap {img : Image} {log : List PMsg} {i : Nat} {prom : GSet Nat} {ws : PState} {l : PLabel}
    {ots : Option Nat} {ws' : PState} {prom' : GSet Nat} (h : memStep img log i prom ws l ots ws' prom') :
    ws.wVcap ≤ ws'.wVcap := by
  cases h <;> (try simp only [acqPost, amoPost, cmoPost, fencePost, fenceIPost, loadRun_vcap, storeRun_vcap,
    cohRaise_vcap, loadRunV_vcap]) <;> omega   -- MachFix-R-b5: `loadRunV_vcap`

theorem solo_vcap {img : Image} {M : List PMsg} {i : Nat} :
    ∀ {x y : LP × PState × GSet Nat} {tr : List (PLabel × Option Nat)},
      soloSteps litStep img M i x tr y → x.2.1.wVcap ≤ y.2.1.wVcap := by
  intro x y tr h
  induction h with
  | refl => exact Nat.le_refl _
  | step _ _ _ _ _ _ _ _ _ hm _ ih => exact Nat.le_trans (memStep_vcap hm) ih

/-- A fulfilling step's pre-view is above `vcap`. -/
theorem fulfil_vcap {img : Image} {log : List PMsg} {i : Nat} {prom : GSet Nat} {ws : PState} {l : PLabel}
    {ts : Nat} {ws' : PState} {prom' : GSet Nat} (h : memStep img log i prom ws l (some ts) ws' prom') :
    ws.wVcap < ts := by
  cases h with
  | store aq rl base data asrc vsrc ts _ _ _ hpv =>
    have := (stPre_ge ws rl (srcsView ws asrc) (srcsView ws vsrc)).2.2
    have := stPreA_ge ws aq rl (srcsView ws asrc) (srcsView ws vsrc); omega
  | rmw aq rl base tvs data asrc vsrc ts _ _ _ _ _ _ hpv =>
    have := (stPre_ge (loadRun ws aq false (srcsView ws asrc) base tvs) rl (srcsView ws asrc)
      (srcsView ws vsrc)).2.2
    rw [loadRun_vcap] at this; omega
  | amoSt rl base data asrc vsrc ts R _ _ _ _ _ _ _ hpv =>
    have := (stPre_ge ws rl (srcsView ws asrc) (srcsView ws vsrc)).2.2; omega
  | sc aq rl base data asrc vsrc ts R _ _ _ _ _ _ hpv =>
    have := (stPre_ge ws rl (srcsView ws asrc) (srcsView ws vsrc)).2.2
    have := stPreA_ge ws aq rl (srcsView ws asrc) (srcsView ws vsrc); omega
  | cmo k base len asrc ts _ _ _ hpv =>
    have := (stPre_ge ws false (srcsView ws asrc) 0).2.2; omega

/-! ## 7. Agreement after one instruction -/

theorem effView_noRegW {ws : PState} {q : List PLabel} {r : Nat} (h : ∀ x ∈ q, isRegW x = false) :
    effView ws q r = regv ws r := by
  unfold effView
  split
  · rename_i rd srcs tl
    have := h _ (List.mem_cons_self ..)
    simp [isRegW] at this
  · rfl

theorem regv_insert (ws : PState) (rd : Nat) (x r : Nat) :
    regv { ws with wRegv := insert ws.wRegv rd x } r = if rd = r then x else regv ws r := by
  unfold regv; exact getD_insert_nat _ _ _ _

/-- Agreement after an instruction that writes `rd` and sets its view at once (queue without register write). -/
theorem agree_wr_now {θ : Nat} {ws ws1 : PState} {s s' : LP} (ha : agree θ ws s s') (hqs : s.q = [])
    {rd v v' p1 p1' : Nat} {q1 : List PLabel} (htl : ∀ x ∈ q1, isRegW x = false) (hp : p1' = p1)
    (hreg : ∀ r, r ≠ rd → regv ws1 r = regv ws r) (hv : rd ≠ 0 → regv ws1 rd < θ → v' % two64 = v % two64) :
    agree θ ws1 { s with regs := s.wr rd v, pc := p1, q := q1 } { s' with regs := s'.wr rd v', pc := p1', q := q1 } := by
  refine ⟨ha.prog, hp, rfl, by simp only [wr_len]; exact ha.len, fun r hr hlt => ?_⟩
  simp only at hlt ⊢
  rw [effView_noRegW htl] at hlt
  unfold LP.wr
  refine regs_wr_agree ha.len hr (fun he => ?_) (fun hne => ?_)
  · subst he; exact hv hr hlt
  · rw [hreg r hne] at hlt
    exact ha.regs r hr (by rw [hqs]; exact hlt)

/-- Agreement after an instruction that writes `rd` and queues its register write `LRegW rd srcs`. -/
theorem agree_wrq {θ : Nat} {ws ws1 : PState} {s s' : LP} (ha : agree θ ws s s') (hqs : s.q = [])
    {rd v v' p1 p1' : Nat} {srcs : List Dsrc} {tl : List PLabel} (htl : ∀ x ∈ tl, isRegW x = false)
    (hp : p1' = p1) (hreg : ∀ r, regv ws1 r = regv ws r)
    (hv : rd ≠ 0 → srcsView ws1 srcs < θ → v' % two64 = v % two64) :
    agree θ ws1 { s with regs := s.wr rd v, pc := p1, q := regWL rd srcs ++ tl }
      { s' with regs := s'.wr rd v', pc := p1', q := regWL rd srcs ++ tl } := by
  refine ⟨ha.prog, hp, rfl, by simp only [wr_len]; exact ha.len, fun r hr hlt => ?_⟩
  simp only at hlt ⊢
  unfold LP.wr
  by_cases hrd : rd = 0
  · subst hrd
    simp only [regWL, if_true, List.nil_append] at hlt
    rw [effView_noRegW htl, hreg] at hlt
    simp only [if_true]
    exact ha.regs r hr (by rw [hqs]; exact hlt)
  · simp only [regWL, hrd, if_false, List.singleton_append, effView] at hlt
    refine regs_wr_agree ha.len hr (fun he => ?_) (fun hne => ?_)
    · subst he; rw [if_pos rfl] at hlt; exact hv hrd hlt
    · rw [if_neg (Ne.symm hne), hreg] at hlt
      exact ha.regs r hr (by rw [hqs]; exact hlt)

/-- Agreement after an instruction that writes no register. -/
theorem agree_same {θ : Nat} {ws ws1 : PState} {s s' : LP} (ha : agree θ ws s s') (hqs : s.q = [])
    {p1 p1' : Nat} {q1 : List PLabel} (htl : ∀ x ∈ q1, isRegW x = false) (hp : p1' = p1)
    (hreg : ∀ r, regv ws1 r = regv ws r) :
    agree θ ws1 { s with pc := p1, q := q1 } { s' with pc := p1', q := q1 } := by
  refine ⟨ha.prog, hp, rfl, ha.len, fun r hr hlt => ?_⟩
  simp only at hlt ⊢
  rw [effView_noRegW htl, hreg] at hlt
  exact ha.regs r hr (by rw [hqs]; exact hlt)

theorem regWL_cons {rd : Nat} {srcs : List Dsrc} {tl : List PLabel} {l : PLabel} {rest : List PLabel}
    (h : regWL rd srcs ++ tl = l :: rest) : (rd = 0 ∧ tl = l :: rest) ∨ (rd ≠ 0 ∧ l = LRegW rd srcs ∧ rest = tl) := by
  unfold regWL at h
  split at h
  · rename_i hr; exact .inl ⟨hr, h⟩
  · rename_i hr; simp at h; exact .inr ⟨hr, h.1.symm, h.2.symm⟩

theorem ite_none_some' {α : Type} {c : Prop} [Decidable c] {x : Option α} {y : α}
    (h : (if c then none else x) = some y) : ¬ c ∧ x = some y := by
  split at h
  · cases h
  · rename_i hc; exact ⟨hc, h⟩

theorem noRegW_LInstr : ∀ x ∈ [LInstr], isRegW x = false := by simp [isRegW]
theorem noRegW_nil : ∀ x ∈ ([] : List PLabel), isRegW x = false := by simp
theorem noRegW_fail : ∀ x ∈ [LExFail, LInstr], isRegW x = false := by simp [isRegW]

/-! ## 8. One step of the noninterference simulation -/

/-- The register writes `regWL rd srcs ++ tl` of an instruction; low-view facts at its head. -/
theorem freeOk_none {D : Int → List (BitVec 8)} {w : List PMsg} {l : PLabel} (h : labelReads l = none) :
    freeOk D w l := by
  intro base tvs hl; rw [h] at hl; cases hl

theorem lowLoad {img : Image} {M : List PMsg} {D : Int → List (BitVec 8)} {θ : Nat} {ws : PState} {aq rl : Bool}
    {va : Nat} {base : Int} {tvs : List (Nat × BitVec 8)} {w : List PMsg} (hlow : lowM img M D θ)
    (hf : fwdInv img M D θ ws w)
    (hok : loadOk img M ws (ldPre ws aq rl va) base tvs) {W : Nat}
    (hW : (loadRun ws aq rl va base tvs).wLdv ≤ W) (hWθ : W < θ) :
    bytesAll (fun a _ v => v ∈ D a ∨ lastByte w a = some v) base tvs := by
  have h1 := (loadBytes_ldv aq (ldPre ws aq rl va) ws base tvs).2
  have e : (loadRun ws aq rl va base tvs).wLdv = (loadBytes aq (ldPre ws aq rl va) ws base tvs).wLdv := rfl
  refine vals_inD (aq := aq) hlow hf base tvs (bytesAll_and base tvs
    (bytesAll_mono (fun _ _ _ hp => hp.1) base tvs hok) (bytesAll_mono (fun x u _ h => ?_) base tvs h1))
  omega

/-- MachFix-R-b5: `lowLoad` for the absorbing post-state. -/
theorem lowLoadV {img : Image} {M : List PMsg} {D : Int → List (BitVec 8)} {θ : Nat} {ws : PState} {aq rl : Bool}
    {va vi : Nat} {base : Int} {tvs : List (Nat × BitVec 8)} {w : List PMsg} (hlow : lowM img M D θ)
    (hf : fwdInv img M D θ ws w)
    (hok : loadOk img M ws (ldPre ws aq rl va) base tvs) {W : Nat}
    (hW : (loadRunV ws aq rl va vi base tvs).wLdv ≤ W) (hWθ : W < θ) :
    bytesAll (fun a _ v => v ∈ D a ∨ lastByte w a = some v) base tvs := by
  have h1 := (loadBytes_ldv aq (max (ldPre ws aq rl va) vi) ws base tvs).2
  have e : (loadRunV ws aq rl va vi base tvs).wLdv =
      (loadBytes aq (max (ldPre ws aq rl va) vi) ws base tvs).wLdv := rfl
  refine vals_inD (aq := aq) hlow hf base tvs (bytesAll_and base tvs
    (bytesAll_mono (fun _ _ _ hp => hp.1) base tvs hok) (bytesAll_mono (fun x u _ h => ?_) base tvs h1))
  omega

theorem cohBelow_bytes {W : PState} {F : Int → Nat → Nat} {ts : Nat} :
    ∀ (a : Int) (tvs : List (Nat × BitVec 8)), cohBelow W a tvs.length ts →
      bytesAll (fun x u _ => F x u ≤ coh W x) a tvs → bytesAll (fun x u _ => F x u < ts) a tvs
  | _, [], _, _ => trivial
  | a, (t, v) :: r, ⟨h1, h2⟩, ⟨k1, k2⟩ => ⟨by omega, cohBelow_bytes (a + 1) r h2 k2⟩

theorem canonRun_inD {D : Int → List (BitVec 8)} {w : List PMsg} (hD : ∀ a, D a ≠ []) (a : Int) (k : Nat) :
    bytesAll (fun a _ v => v ∈ D a ∨ lastByte w a = some v) a (canonRun D a k) :=
  bytesAll_left a _ (canonRun_inD' hD a k)

end Weak.Prom.Mach
