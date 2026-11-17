/-
Weak/Mini: **the leaf rules of MiniLogic, one per instruction of F** (mini plan rev 4 §2 L3: "leaf rules for F's
instructions incl. backward branches"; the full stack's templates are `Weak/Prom/CoreRules.lean` (label-level rules)
and `Weak/Prom/CoreKit.lean` (instruction-level kit)).

Every rule is an iProp lemma over the hart's EXACT state (`hartSt γ ws τ`), proved from the one lifting lemma
`wpH_lift` (Logic.lean); none unfolds `WP`.  A rule applies at a front-end state `f` with nothing queued whose
instruction at `pc` is the rule's; it runs the WHOLE instruction (all its labels) and continues at the next
front-end state with the post memory state and the extended trace; exactly one `▷` is in front of the
continuation (so a Löb hypothesis can be used after any instruction: loops).

* The trace invariant `Ψ` must be QUIET-STABLE (`qstable`): appending a non-memory entry (register write, control,
  fence, instruction end) keeps it.  Only the memory labels carry an obligation, `Ψ` of the extended trace, proved
  by the client with the step's facts and `Ψ τ` in hand.
* `qWs ws labs`, `qTr τ labs`: the memory state and the trace after the quiet labels `labs` (their memory half is
  deterministic: `qpost`).
* ALU (`wp_alui`, `wp_alu`), FENCE (`wp_fence`), BRANCH with ANY target ≤ the text length, so BACKWARD branches
  (`wp_br`), JUMP (`wp_jmp`), NOP (`wp_nop`): quiet instructions, no obligation.
* LOAD (`wp_load`): every answer `(t, v)` with `v` a word and `loadOk` at the load's pre-view (address view ⊔ load
  floor, rules 4, 9); the post-state is `loadPost` then the register write of the load result.
* STORE (`wp_store`): every fulfil timestamp `ts` whose message in the final log is this word by this hart, with
  COH (`coh a < ts`) and EXT (pre-view `< ts`).
* A finished hart: `wp_done`.
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Mini.Logic

namespace Weak.Mini.Logic

open Weak.Mini Weak.Mini.Mach
open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode

/-! ## 1. Quiet labels -/

/-- The memory labels (loads, stores); every other label is QUIET. -/
def isMem : MLab → Bool
  | .load .. => true
  | .store .. => true
  | _ => false

/-- The post memory state of a quiet label (`mMem`'s fence, regW, ctrl, instr arms). -/
def qpost (ws : MSt) : MLab → MSt
  | .fence pr pw sr sw => fencePost ws pr pw sr sw
  | .regW rd srcs => { ws with regv := fun r => if r = rd then srcsView ws srcs else ws.regv r }
  | .ctrl srcs => { ws with vcap := max (srcsView ws srcs) ws.vcap }
  | .instr => { ws with ldv := 0 }
  | _ => ws

/-- The memory state after the quiet labels `labs`. -/
def qWs (ws : MSt) (labs : List MLab) : MSt := labs.foldl qpost ws

/-- The trace after the quiet labels `labs`. -/
def qTr (τ : Trace) (labs : List MLab) : Trace := labs.foldl (fun τ l => τ ++ [(l, none)]) τ

theorem qWs_nil (ws : MSt) : qWs ws [] = ws := rfl
theorem qTr_nil (τ : Trace) : qTr τ [] = τ := rfl
theorem qWs_cons (ws : MSt) (l : MLab) (rest : List MLab) : qWs ws (l :: rest) = qWs (qpost ws l) rest := rfl
theorem qTr_cons (τ : Trace) (l : MLab) (rest : List MLab) : qTr τ (l :: rest) = qTr (τ ++ [(l, none)]) rest := rfl

/-- `Ψ` is kept by every quiet entry. -/
def qstable (Ψ : Trace → Prop) : Prop := ∀ τ l, isMem l = false → Ψ τ → Ψ (τ ++ [(l, none)])

theorem mMem_quiet {P : MProg} {log : List MMsg} {i : Nat} {pr : List Nat} {ws : MSt} {l : MLab}
    {ots : Option Nat} {ws' : MSt} {pr' : List Nat} (hl : isMem l = false) (h : mMem P log i pr ws l ots ws' pr') :
    ots = none ∧ ws' = qpost ws l := by
  cases h <;> first | exact ⟨rfl, rfl⟩ | simp [isMem] at hl

theorem mNext_q {P : MProg} {i : Nat} {f : MFront} {l0 : MLab} {rest : List MLab} (hq : f.q = l0 :: rest)
    {l : MLab} {f' : MFront} (h : mNext P i f l = some f') : l = l0 ∧ f' = { f with q := rest } := by
  simp only [mNext, hq] at h
  split at h
  · next he => exact ⟨he, (Option.some.inj h).symm⟩
  · cases h

theorem mNext_ins {P : MProg} {i : Nat} {f : MFront} {ins : MI} (hq : f.q = []) (hi : (P.prog i)[f.pc]? = some ins)
    (l : MLab) : mNext P i f l = instrNext P (P.prog i).length f ins l := by
  simp only [mNext, hq, hi]

theorem mNext_done {P : MProg} {i : Nat} {f : MFront} (hq : f.q = []) (hi : (P.prog i)[f.pc]? = none) (l : MLab) :
    mNext P i f l = none := by
  simp only [mNext, hq, hi]

theorem go1_inv {f : MFront} {regs' : List Nat} {pc' : Nat} {labs : List MLab} {l : MLab} {f' : MFront}
    (h : go1 f regs' pc' labs l = some f') : ∃ l0 rest, labs = l0 :: rest ∧ l = l0 ∧ f' = ⟨pc', regs', rest⟩ := by
  unfold go1 at h
  split at h
  · next l0 rest =>
    split at h
    · next he => exact ⟨l0, rest, rfl, he, (Option.some.inj h).symm⟩
    · cases h
  · cases h

/-! ## 2. Draining quiet labels, and the quiet instructions -/

section rules

variable {hlc : HasLC} {GF : BundledGFunctors} [GhostVarG GF HSt] [InvGS_gen hlc GF]
variable {γ : GName} {P : MProg} {M : List MMsg} {h : Nat} {Ψ : Trace → Prop} {Φ : MFront → IProp GF}

/-- Queued quiet labels are taken one by one, without a later in front of the continuation. -/
theorem wp_drain (hst : qstable Ψ) : ∀ (labs : List MLab) (f : MFront) (ws : MSt) (τ : Trace), f.q = labs →
    (∀ l ∈ labs, isMem l = false) →
    hartSt γ ws τ ∗ (hartSt γ (qWs ws labs) (qTr τ labs) -∗ wpH γ ⟨P, M, h⟩ Ψ { f with q := [] } Φ)
      ⊢ wpH γ ⟨P, M, h⟩ Ψ f Φ
  | [], f, ws, τ, hq, _ => by
    have e : { f with q := [] } = f := by cases f; simp_all
    rw [e]
    iintro ⟨Hst, Hk⟩
    iapply Hk
    rw [qWs_nil, qTr_nil]
    iexact Hst
  | l0 :: rest, f, ws, τ, hq, hall => by
    iintro ⟨Hst, Hk⟩
    iapply wpH_lift
    iframe Hst
    inext
    isplit
    · iintro %hd
      exact absurd (hd.1.symm.trans hq) (fun e => nomatch e)
    · iintro %l %ots %f' %ws' %pr %pr' %hn %hm %hΨ
      obtain ⟨rfl, rfl⟩ := mNext_q hq hn
      have hl0 := hall l (List.mem_cons_self ..)
      obtain ⟨rfl, rfl⟩ := mMem_quiet hl0 hm
      imodintro
      isplitr
      · ipureintro; exact hst τ l hl0 hΨ
      iintro Hst
      iapply (wp_drain hst rest { f with q := rest } (qpost ws l) (τ ++ [(l, none)]) rfl
        (fun l' hl' => hall l' (List.mem_cons_of_mem _ hl')))
      iframe Hst
      rw [qWs_cons, qTr_cons]
      iexact Hk

/-- **A QUIET INSTRUCTION** (its first label and all later ones are quiet): the general rule behind the ALU,
fence, branch, jump and nop rules. -/
theorem wp_quietI {f : MFront} {ins : MI} {regs' : List Nat} {pc' : Nat} {labs : List MLab} {ws : MSt} {τ : Trace}
    (hq : f.q = []) (hi : (P.prog h)[f.pc]? = some ins)
    (hn : ∀ l, instrNext P (P.prog h).length f ins l = go1 f regs' pc' labs l)
    (hall : ∀ l ∈ labs, isMem l = false) (hst : qstable Ψ) :
    hartSt γ ws τ ∗ ▷ (hartSt γ (qWs ws labs) (qTr τ labs) -∗ wpH γ ⟨P, M, h⟩ Ψ ⟨pc', regs', []⟩ Φ)
      ⊢ wpH γ ⟨P, M, h⟩ Ψ f Φ := by
  iintro ⟨Hst, Hk⟩
  iapply wpH_lift
  iframe Hst
  inext
  isplit
  · iintro %hd
    exact absurd (hd.2.symm.trans hi) (fun e => nomatch e)
  · iintro %l %ots %f' %ws' %pr %pr' %hn' %hm %hΨ
    rw [mNext_ins hq hi, hn] at hn'
    obtain ⟨l0, rest, rfl, rfl, rfl⟩ := go1_inv hn'
    have hl0 := hall l (List.mem_cons_self ..)
    obtain ⟨rfl, rfl⟩ := mMem_quiet hl0 hm
    imodintro
    isplitr
    · ipureintro; exact hst τ l hl0 hΨ
    iintro Hst
    iapply (wp_drain hst rest ⟨pc', regs', rest⟩ (qpost ws l) (τ ++ [(l, none)]) rfl
      (fun l' hl' => hall l' (List.mem_cons_of_mem _ hl')))
    iframe Hst
    rw [qWs_cons, qTr_cons]
    iexact Hk

theorem regWL_quiet (rd : Nat) (srcs : List MSrc) : ∀ l ∈ regWL rd srcs ++ [.instr], isMem l = false := by
  intro l hl
  unfold regWL at hl
  split at hl <;> simp at hl <;> rcases hl with rfl | rfl <;> rfl

/-- **ALU, immediate**: `op rd, rs1, imm` — `LRegW rd [rs1]` (unless `rd = x0`), `LInstr`. -/
theorem wp_alui {f : MFront} {op : MAlu} {rd rs1 imm : Nat} {ws : MSt} {τ : Trace} (hq : f.q = [])
    (hi : (P.prog h)[f.pc]? = some (.alui op rd rs1 imm)) (hst : qstable Ψ) :
    hartSt γ ws τ ∗ ▷ (hartSt γ (qWs ws (regWL rd (srcR rs1) ++ [.instr])) (qTr τ (regWL rd (srcR rs1) ++ [.instr])) -∗
        wpH γ ⟨P, M, h⟩ Ψ ⟨f.pc + 1, f.wr rd (op.eval (f.rd rs1) imm), []⟩ Φ)
      ⊢ wpH γ ⟨P, M, h⟩ Ψ f Φ :=
  wp_quietI hq hi (fun _ => rfl) (regWL_quiet _ _) hst

/-- **ALU, registers**: `op rd, rs1, rs2` — `LRegW rd [rs1, rs2]` (unless `rd = x0`), `LInstr`. -/
theorem wp_alu {f : MFront} {op : MAlu} {rd rs1 rs2 : Nat} {ws : MSt} {τ : Trace} (hq : f.q = [])
    (hi : (P.prog h)[f.pc]? = some (.alu op rd rs1 rs2)) (hst : qstable Ψ) :
    hartSt γ ws τ ∗ ▷ (hartSt γ (qWs ws (regWL rd (srcR rs1 ++ srcR rs2) ++ [.instr]))
          (qTr τ (regWL rd (srcR rs1 ++ srcR rs2) ++ [.instr])) -∗
        wpH γ ⟨P, M, h⟩ Ψ ⟨f.pc + 1, f.wr rd (op.eval (f.rd rs1) (f.rd rs2)), []⟩ Φ)
      ⊢ wpH γ ⟨P, M, h⟩ Ψ f Φ :=
  wp_quietI hq hi (fun _ => rfl) (regWL_quiet _ _) hst

/-- **FENCE** `pred, succ`: `LFence`, `LInstr` (rule 4). -/
theorem wp_fence {f : MFront} {fs : MFence} {ws : MSt} {τ : Trace} (hq : f.q = [])
    (hi : (P.prog h)[f.pc]? = some (.fence fs)) (hst : qstable Ψ) :
    hartSt γ ws τ ∗ ▷ (hartSt γ (qWs ws [.fence fs.pr fs.pw fs.sr fs.sw, .instr])
          (qTr τ [.fence fs.pr fs.pw fs.sr fs.sw, .instr]) -∗
        wpH γ ⟨P, M, h⟩ Ψ ⟨f.pc + 1, f.regs, []⟩ Φ)
      ⊢ wpH γ ⟨P, M, h⟩ Ψ f Φ :=
  wp_quietI hq hi (fun _ => rfl) (by simp [isMem]) hst

/-- **BRANCH**, any target `tgt ≤` the text length, so FORWARD OR BACKWARD: `LCtrl (rs1 ++ rs2)` (rule 11),
`LInstr`; then `pc := tgt` if the condition holds, else `pc + 1`. -/
theorem wp_br {f : MFront} {c : MBrC} {rs1 rs2 tgt : Nat} {ws : MSt} {τ : Trace} (hq : f.q = [])
    (hi : (P.prog h)[f.pc]? = some (.br c rs1 rs2 tgt)) (ht : tgt ≤ (P.prog h).length) (hst : qstable Ψ) :
    hartSt γ ws τ ∗ ▷ (hartSt γ (qWs ws [.ctrl (srcR rs1 ++ srcR rs2), .instr])
          (qTr τ [.ctrl (srcR rs1 ++ srcR rs2), .instr]) -∗
        wpH γ ⟨P, M, h⟩ Ψ ⟨if c.eval (f.rd rs1) (f.rd rs2) then tgt else f.pc + 1, f.regs, []⟩ Φ)
      ⊢ wpH γ ⟨P, M, h⟩ Ψ f Φ :=
  wp_quietI hq hi (fun _ => by simp only [instrNext, if_neg (Nat.not_lt.2 ht)]) (by simp [isMem]) hst

/-- **JUMP** `jal x0, tgt`, any target `tgt ≤` the text length: `LInstr`; `pc := tgt`. -/
theorem wp_jmp {f : MFront} {tgt : Nat} {ws : MSt} {τ : Trace} (hq : f.q = [])
    (hi : (P.prog h)[f.pc]? = some (.jmp tgt)) (ht : tgt ≤ (P.prog h).length) (hst : qstable Ψ) :
    hartSt γ ws τ ∗ ▷ (hartSt γ (qWs ws [.instr]) (qTr τ [.instr]) -∗ wpH γ ⟨P, M, h⟩ Ψ ⟨tgt, f.regs, []⟩ Φ)
      ⊢ wpH γ ⟨P, M, h⟩ Ψ f Φ :=
  wp_quietI hq hi (fun _ => by simp only [instrNext, if_neg (Nat.not_lt.2 ht)]) (by simp [isMem]) hst

/-- **NOP**: `LInstr`. -/
theorem wp_nop {f : MFront} {ws : MSt} {τ : Trace} (hq : f.q = []) (hi : (P.prog h)[f.pc]? = some .nop)
    (hst : qstable Ψ) :
    hartSt γ ws τ ∗ ▷ (hartSt γ (qWs ws [.instr]) (qTr τ [.instr]) -∗ wpH γ ⟨P, M, h⟩ Ψ ⟨f.pc + 1, f.regs, []⟩ Φ)
      ⊢ wpH γ ⟨P, M, h⟩ Ψ f Φ :=
  wp_quietI hq hi (fun _ => rfl) (by simp [isMem]) hst

/-! ## 3. Loads, stores, the end -/

theorem instrNext_load {n : Nat} {f : MFront} {sgn : Bool} {rd rs1 off : Nat} {l : MLab} {f' : MFront}
    (ha : (f.rd rs1 + off) % two64 % P.sz = 0) (h : instrNext P n f (.load sgn rd rs1 off) l = some f') :
    ∃ t v, l = .load ((f.rd rs1 + off) % two64) t v (srcR rs1) ∧ v < wordW P ∧
      f' = ⟨f.pc + 1, f.wr rd (if sgn then sext P.sz v else v), regWL rd [.ldres] ++ [.instr]⟩ := by
  simp only [instrNext, ha, ne_eq, not_true_eq_false, if_false] at h
  split at h
  · next b t v asrc =>
    split at h
    · next hc =>
      obtain ⟨rfl, hv, rfl⟩ := hc
      exact ⟨t, v, rfl, hv, (Option.some.inj h).symm⟩
    · cases h
  · cases h

theorem instrNext_store {n : Nat} {f : MFront} {rs2 rs1 off : Nat} {l : MLab} {f' : MFront}
    (ha : (f.rd rs1 + off) % two64 % P.sz = 0) (h : instrNext P n f (.store rs2 rs1 off) l = some f') :
    l = .store ((f.rd rs1 + off) % two64) (f.rd rs2 % wordW P) (srcR rs1) (srcR rs2) ∧
      f' = ⟨f.pc + 1, f.regs, [.instr]⟩ := by
  simp only [instrNext, ha, ne_eq, not_true_eq_false, if_false] at h
  split at h
  · next b v asrc vsrc =>
    split at h
    · next hc =>
      obtain ⟨rfl, rfl, rfl, rfl⟩ := hc
      exact ⟨rfl, (Option.some.inj h).symm⟩
    · cases h
  · cases h

/-- **LOAD** `rd, off(rs1)` at the aligned address `a`: for every answer `(t, v)` — `v` a word, `loadOk` at the
pre-view `ldPre ws va` (address view `va`, rule 9; load floor, rule 4) — the client proves `Ψ` of the trace with
the load entry; then `LRegW rd [ldres]` (unless `rd = x0`) and `LInstr`. -/
theorem wp_load {f : MFront} {sgn : Bool} {rd rs1 off : Nat} {ws : MSt} {τ : Trace} (hq : f.q = [])
    (hi : (P.prog h)[f.pc]? = some (.load sgn rd rs1 off)) (ha : (f.rd rs1 + off) % two64 % P.sz = 0)
    (hst : qstable Ψ) :
    hartSt γ ws τ ∗ ▷ (∀ t v, ⌜v < wordW P⌝ -∗
        ⌜loadOk P M ws (ldPre ws (srcsView ws (srcR rs1))) ((f.rd rs1 + off) % two64) t v⌝ -∗ ⌜Ψ τ⌝ -∗
        ⌜Ψ (τ ++ [(.load ((f.rd rs1 + off) % two64) t v (srcR rs1), none)])⌝ ∗
        (hartSt γ (qWs (loadPost ws (srcsView ws (srcR rs1)) (ldPre ws (srcsView ws (srcR rs1)))
              ((f.rd rs1 + off) % two64) t) (regWL rd [.ldres] ++ [.instr]))
            (qTr (τ ++ [(.load ((f.rd rs1 + off) % two64) t v (srcR rs1), none)]) (regWL rd [.ldres] ++ [.instr])) -∗
          wpH γ ⟨P, M, h⟩ Ψ ⟨f.pc + 1, f.wr rd (if sgn then sext P.sz v else v), []⟩ Φ))
      ⊢ wpH γ ⟨P, M, h⟩ Ψ f Φ := by
  iintro ⟨Hst, Hk⟩
  iapply wpH_lift
  iframe Hst
  inext
  isplit
  · iintro %hd
    exact absurd (hd.2.symm.trans hi) (fun e => nomatch e)
  · iintro %l %ots %f' %ws' %pr %pr' %hn %hm %hΨ
    rw [mNext_ins hq hi] at hn
    obtain ⟨t, v, rfl, hv, rfl⟩ := instrNext_load ha hn
    cases hm with
    | load _ _ _ _ hl =>
      ihave Hk := Hk $$ %t %v %hv %hl %hΨ
      icases Hk with ⟨%hΨ', Hk⟩
      imodintro
      isplitr
      · ipureintro; exact hΨ'
      iintro Hst
      iapply (wp_drain hst (regWL rd [.ldres] ++ [.instr]) _ _ _ rfl (regWL_quiet _ _))
      iframe Hst
      iexact Hk

/-- **STORE** `rs2, off(rs1)` at the aligned address `a`, value `v = rs2 mod 2^(8·sz)`: for every fulfil
timestamp `ts` whose message in the final log is `(a, v, h)` with COH (`coh a < ts`) and EXT (pre-view `< ts`;
address and data views, rules 9–10; capture view, rules 11, 13; store floor, rule 4) — the client proves `Ψ` of
the trace with the store entry; then `LInstr`. -/
theorem wp_store {f : MFront} {rs2 rs1 off : Nat} {ws : MSt} {τ : Trace} (hq : f.q = [])
    (hi : (P.prog h)[f.pc]? = some (.store rs2 rs1 off)) (ha : (f.rd rs1 + off) % two64 % P.sz = 0)
    (hst : qstable Ψ) :
    hartSt γ ws τ ∗ ▷ (∀ ts, ⌜M[ts - 1]? = some ⟨(f.rd rs1 + off) % two64, f.rd rs2 % wordW P, h⟩⌝ -∗
        ⌜ws.coh ((f.rd rs1 + off) % two64) < ts⌝ -∗
        ⌜stPre ws (srcsView ws (srcR rs1)) (srcsView ws (srcR rs2)) < ts⌝ -∗ ⌜Ψ τ⌝ -∗
        ⌜Ψ (τ ++ [(.store ((f.rd rs1 + off) % two64) (f.rd rs2 % wordW P) (srcR rs1) (srcR rs2), some ts)])⌝ ∗
        (hartSt γ (qWs (storePost ws (srcsView ws (srcR rs1)) (max (srcsView ws (srcR rs1)) (srcsView ws (srcR rs2)))
              ((f.rd rs1 + off) % two64) ts) [.instr])
            (qTr (τ ++ [(.store ((f.rd rs1 + off) % two64) (f.rd rs2 % wordW P) (srcR rs1) (srcR rs2), some ts)])
              [.instr]) -∗
          wpH γ ⟨P, M, h⟩ Ψ ⟨f.pc + 1, f.regs, []⟩ Φ))
      ⊢ wpH γ ⟨P, M, h⟩ Ψ f Φ := by
  iintro ⟨Hst, Hk⟩
  iapply wpH_lift
  iframe Hst
  inext
  isplit
  · iintro %hd
    exact absurd (hd.2.symm.trans hi) (fun e => nomatch e)
  · iintro %l %ots %f' %ws' %pr %pr' %hn %hm %hΨ
    rw [mNext_ins hq hi] at hn
    obtain ⟨rfl, rfl⟩ := instrNext_store ha hn
    cases hm with
    | store _ _ _ _ ts _ hM hc he =>
      ihave Hk := Hk $$ %ts %hM %hc %he %hΨ
      icases Hk with ⟨%hΨ', Hk⟩
      imodintro
      isplitr
      · ipureintro; exact hΨ'
      iintro Hst
      iapply (wp_drain hst [.instr] _ _ _ rfl (by simp [isMem]))
      iframe Hst
      iexact Hk

/-- **A FINISHED HART**: its postcondition. -/
theorem wp_done {f : MFront} {ws : MSt} {τ : Trace} (hq : f.q = []) (hi : (P.prog h)[f.pc]? = none) :
    hartSt γ ws τ ∗ Φ f ⊢ wpH γ ⟨P, M, h⟩ Ψ f Φ := by
  iintro ⟨Hst, HΦ⟩
  iapply wpH_lift
  iframe Hst
  inext
  isplit
  · iintro _ _
    imodintro
    iexact HΦ
  · iintro %l %ots %f' %ws' %pr %pr' %hn
    rw [mNext_done hq hi] at hn
    cases hn

end rules

end Weak.Mini.Logic
