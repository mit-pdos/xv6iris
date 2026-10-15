/-
Weak: **W9a (B) B5 cycRun — the execute stage, part 3: the walk's instructions are in the four
classes; `execCyAt`** ([OWN.85] Q-B5-CYCLE = C1; report `PROGRESS-cycRun.md`).  Lean-only.

`walkClass`: at every reached non-pin walk state, Sail's decode of the image (`decS`) is a PLAIN
instruction (`plainC`), a conditional branch or a direct jump at a non-store role, or the read of
`sepc`/`satp` — checked over B5's generated table by `decide +kernel`.

Every helper is `Weak.PinCycRun.*`.
-/
import Weak.PinCycRunExec2

namespace Weak

open MachCSL KernelPinsDef LeanRV64D LeanRV64D.Functions
open WeakRvwmoPinBridge3 (preach)
open WeakRvwmoPinBridge4 (walkOwn)
open PinWalkTab

attribute [local semireducible] LeanRV64D.Functions.hartSupports LeanRV64D.Functions.currentlyEnabled

namespace PinCycRun

/-- A conditional branch AST, base or compressed. -/
def brC (c : instruction) : Bool :=
  match c with
  | .BTYPE _ | .C_BEQZ _ | .C_BNEZ _ => true
  | _ => false

/-- A direct jump AST, base or compressed. -/
def jalC (c : instruction) : Bool :=
  match c with
  | .JAL _ | .C_J _ => true
  | _ => false

/-- The read of `sepc` or `satp` (`csrrs rd, c, x0`). -/
def csrC (c : instruction) : Bool :=
  match c with
  | .CSRReg (k, regidx.Regidx r1, _, .CSRRS) => r1 == 0#5 && (k == 0x141#12 || k == 0x180#12)
  | _ => false

/-- The class check at a pc. -/
noncomputable def classOk (pc : Int) : Bool :=
  match decS pc with
  | some a => plainC a || ((brC a || jalC a) && !roleIsStore (krole pc)) || csrC a
  | none => false

/-- The per-state check: a non-pin state's instruction is in a class. -/
noncomputable def clsOk (own : Bool) (s : PState) : Bool :=
  match pstep own s with
  | some (_ :: _) => classOk s.psPc
  | _ => true

noncomputable def clsRowOk (r : WRow) : Bool := r.wSts.all (clsOk r.wOwn)

theorem clsRowsOk0 : walkRows0.all clsRowOk = true := by decide +kernel
theorem clsRowsOk1 : walkRows1.all clsRowOk = true := by decide +kernel
theorem clsRowsOk2 : walkRows2.all clsRowOk = true := by decide +kernel
theorem clsRowsOk3 : walkRows3.all clsRowOk = true := by decide +kernel
theorem clsRowsOk4 : walkRows4.all clsRowOk = true := by decide +kernel
theorem clsRowsOk5 : walkRows5.all clsRowOk = true := by decide +kernel
theorem clsRowsOk6 : walkRows6.all clsRowOk = true := by decide +kernel
theorem clsRowsOk7 : walkRows7.all clsRowOk = true := by decide +kernel
theorem clsRowsOk8 : walkRows8.all clsRowOk = true := by decide +kernel
theorem clsRowsOk9 : walkRows9.all clsRowOk = true := by decide +kernel
theorem clsRowsOk10 : walkRows10.all clsRowOk = true := by decide +kernel
theorem clsRowsOk11 : walkRows11.all clsRowOk = true := by decide +kernel

theorem clsRowsOk : walkRows.all clsRowOk = true := by
  simp only [walkRows, List.all_append, clsRowsOk0, clsRowsOk1, clsRowsOk2, clsRowsOk3,
    clsRowsOk4, clsRowsOk5, clsRowsOk6, clsRowsOk7, clsRowsOk8, clsRowsOk9, clsRowsOk10,
    clsRowsOk11, Bool.and_self]

/-- **EVERY REACHED NON-PIN INSTRUCTION IS IN A CLASS** (header). -/
theorem walkClass (pc : Int) (w : Pin) (own : Bool) (x : PState) (n : Nat) (l : List PState) :
    (pc, w) ∈ pinsW9a → walkOwn w = some own → preach own (pinStart pc) x n →
    pstep own x = some l → l ≠ [] → classOk x.psPc = true := by
  intro hm hw hx hp hne
  have hin : (pc, own) ∈ walkRows.map (fun r => (r.wPc, r.wOwn)) := by
    rw [walkRowsCover]
    exact List.mem_filterMap.2 ⟨(pc, w), hm, by simp [hw]⟩
  obtain ⟨r, hr, he⟩ := List.mem_map.1 hin
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  have hrow := List.all_eq_true.mp walkRowsOk r hr
  unfold rowOk at hrow
  rw [Bool.and_eq_true] at hrow
  obtain ⟨h0, h1⟩ := hrow
  obtain ⟨y, hy, hey⟩ := List.any_eq_true.mp h0
  have hst : pinStart r.wPc ∈ r.wSts := by
    rw [WeakRvwmoPinBridge3.pstateEqbEq _ _ hey]; exact hy
  have hall := List.all_eq_true.mp h1
  have hx' := PinWalkTab.closedReach r.wOwn r.wSts
    (fun s hs => (Bool.and_eq_true _ _ ▸ hall s hs).2) _ x n hx hst
  have hc := List.all_eq_true.mp (List.all_eq_true.mp clsRowsOk r hr) x hx'
  unfold clsOk at hc
  rw [hp] at hc
  cases l with
  | nil => exact absurd rfl hne
  | cons a l => exact hc

/-! ## 2. Glue -/

open PinDataflow PinCycRunFp

/-- Two dataflow facts of one tree. -/
theorem PinCycRun.dfAnd {X : Type} (P Q : X → DfSt → Prop) :
    ∀ (m : SailM X) (d : DfSt), dfB P m d → dfB Q m d → dfB (fun x d' => P x d' ∧ Q x d') m d := by
  intro m
  induction m with
  | pure x => intro d h1 h2; exact ⟨h1, h2⟩
  | impure call k ih =>
    intro d h1 h2
    cases call with
    | error e => trivial
    | ok o =>
      cases o
      case regRead => exact fun v hv => ih v _ (h1 v hv) (h2 v hv)
      case regWrite => exact ⟨h1.1, fun u => ih u _ (h1.2 u) (h2.2 u)⟩
      case instrAnnounce => exact fun u => ih u _ (h1 u) (h2 u)
      all_goals exact fun v => ih v _ (h1 v) (h2 v)

/-- A plain instruction's control class is fall-through. -/
theorem PinCycRun.astFlowPlain (pc : Int) (a : instruction) (h : plainC a = true) :
    astFlow pc a = .FLnone := by
  cases a <;> first | rfl | (exfalso; revert h; simp only [plainC]; decide)

/-- The fall-through successor at a non-fence pc of fall-through class. -/
theorem PinCycRun.succFall (pc : Int) (hf : wIsFence (kw pc) = false) (hk : kflowOf pc = .FLnone) :
    pc + wSize (kw pc) ∈ succPcs pc := by
  unfold succPcs
  rw [hf]
  simp only [Bool.false_eq_true, ↓reduceIte]
  split
  · exact List.mem_singleton.2 rfl
  · rw [hk]; exact List.mem_singleton.2 rfl

theorem PinCycRun.memPcOf (pc : Int) (a : instruction) (hdec : decS pc = some a) :
    memPc pc = memC a := by
  unfold memPc; rw [hdec]

/-- **THE PLAIN CLASS AT A WALK PC** (header). -/
theorem execPlain (pc : Int) (a : instruction) (hdec : decS pc = some a) (hc : plainC a = true)
    (hok : dfInstrOkB5 (krole pc) a = true) (hflow : astFlow pc a = kflowOf pc)
    (hf : wIsFence (kw pc) = false) (T : CySt → (r : Register) → RegisterType r → Prop)
    (st : CySt) (hpre : execPre pc st) :
    cyB kA (kAa pc) cyS T (execPost pc st) (uxaExecAs a) st := by
  obtain ⟨hpc, hcfg, hrb, hnpc, han, hro, hn, hok0⟩ := hpre
  have hb := dfInstrB5 a st.d hn hok0 (by rw [hro]; exact hok)
  have hp := pfUxaPlain a hc
  refine cyOfPfDf kA (kAa pc) cyS T ?_ _ _ _ _ st hp
    (PinCycRun.dfAnd _ _ _ _ hb (PinCycRun.dfRoKeep _ _ _ hp)) hrb
    (fun r st' hP hfr hd => ?_)
  · intro r hr
    simp only [cyS, Bool.or_eq_true, decide_eq_true_eq] at hr
    rcases hr with rfl | rfl <;> rfl
  obtain ⟨hdone, hro'⟩ := hd
  refine ⟨hfr.2.2.1, hfr.2.2.2, hro', hfr.2.1, fun r' h' _ => hfr.1 r' h', ?_⟩
  rcases hP with rfl | ⟨hm, ht⟩
  · rcases hdone with h | h
    · cases h
    refine Or.inl ⟨rfl, h.1, h.2, pc + wSize (kw pc), ?_, ?_⟩
    · exact PinCycRun.succFall pc hf (hflow ▸ PinCycRun.astFlowPlain pc a hc)
    · rw [hfr.1 .nextPC (by decide)]; exact hnpc
  · cases r
    case Trap x => exact Or.inr ⟨x, rfl, by rw [PinCycRun.memPcOf pc a hdec]; exact hm⟩
    all_goals simp [isTrapR] at ht

/-! ## 3. The control and CSR classes -/

theorem PinCycRun.addSext {n : Nat} (pc : Int) (x : BitVec n) :
    BitVec.ofInt 64 pc + sign_extend (m := 64) x = BitVec.ofInt 64 (pc + x.toInt) := by
  rw [BitVec.ofInt_add]; rfl

/-- `uxaExecAs` of an instruction whose `execute` does not redirect, at the cycle predicate. -/
theorem cyUxaOf (A : Int → BitVec 8 → Prop) (Aa : Nat → Int → Prop)
    (T : CySt → (r : Register) → RegisterType r → Prop) (c : instruction)
    (P : ExecutionResult → CySt → Prop) (st : CySt)
    (h : cyB A Aa cyS T (fun r st' => P r st' ∧ isExecAsR r = false) (execute c) st) :
    cyB A Aa cyS T P (uxaExecAs c) st := by
  unfold uxaExecAs
  refine cyBBind _ _ _ _ st h (fun r st' hr => ?_)
  cases r
  case ExecuteAs i => exact absurd hr.2 (by simp [isExecAsR])
  all_goals exact hr.1

/-- `uxaExecAs` of a compressed instruction redirecting to `b`. -/
theorem cyUxaRedir (A : Int → BitVec 8 → Prop) (Aa : Nat → Int → Prop)
    (T : CySt → (r : Register) → RegisterType r → Prop) (c b : instruction)
    (P : ExecutionResult → CySt → Prop) (st : CySt) (he : execute c = pure (.ExecuteAs b))
    (h : cyB A Aa cyS T P (execute b) st) : cyB A Aa cyS T P (uxaExecAs c) st := by
  unfold uxaExecAs; rw [he]; exact h

/-- A retired control transfer's post, with B1's slots, is the execute stage's post. -/
theorem PinCycRun.ctlExec (pc : Int) (ok : BitVec 64 → Prop) (st : CySt) (r : ExecutionResult)
    (st' : CySt) (h : ctlPost ok st r st') (hd : dfDone r st'.d)
    (hs : ∀ v, ok v → ∃ pc', pc' ∈ succPcs pc ∧ v = BitVec.ofInt 64 pc') : execPost pc st r st' := by
  obtain ⟨rfl, h1, h2, h3, h4, h5, h6⟩ := h
  rcases hd with hd | hd
  · cases hd
  exact ⟨h1, h2, h3, h4, h5, Or.inl ⟨rfl, hd.1, hd.2, hs _ h6⟩⟩

theorem PinCycRun.ctlPostRetire (ok : BitVec 64 → Prop) (st : CySt) (r : ExecutionResult)
    (st' : CySt) (h : ctlPost ok st r st') : ctlPost ok st r st' ∧ isExecAsR r = false := by
  refine ⟨h, ?_⟩; rw [h.1]; rfl

/-- The successors at a non-fence, non-store pc of class `FLbranch tgt`. -/
theorem PinCycRun.succBranch (pc tgt : Int) (hf : wIsFence (kw pc) = false)
    (hs : roleIsStore (krole pc) = false) (hk : kflowOf pc = .FLbranch tgt) :
    pc + wSize (kw pc) ∈ succPcs pc ∧ tgt ∈ succPcs pc := by
  unfold succPcs
  rw [hf, hs, hk]
  simp

theorem PinCycRun.succJump (pc tgt : Int) (hf : wIsFence (kw pc) = false)
    (hs : roleIsStore (krole pc) = false) (hk : kflowOf pc = .FLjump tgt ∨ kflowOf pc = .FLcall tgt) :
    tgt ∈ succPcs pc := by
  unfold succPcs
  rw [hf, hs]
  rcases hk with hk | hk <;> rw [hk] <;> simp

/-! ## 4. `execCyAt` at the walk -/

theorem PinCycRun.notFence (own : Bool) (x : PState) (l : List PState) (hp : pstep own x = some l)
    (hne : l ≠ []) : wIsFence (kw x.psPc) = false := by
  cases h : wIsFence (kw x.psPc)
  · rfl
  · exfalso
    unfold pstep at hp
    simp only [h, ↓reduceIte] at hp
    split at hp
    · cases hp
    · cases hp; exact hne rfl

/-- The branch target's arithmetic. -/
theorem PinCycRun.brOk (pc : Int) (st : CySt) (hpc : st.rv .PC = BitVec.ofInt 64 pc) {n : Nat}
    (imm : BitVec n) (v : BitVec 64) (hv : v = st.rv .PC + sign_extend (m := 64) imm) :
    v = BitVec.ofInt 64 (pc + imm.toInt) := by
  rw [hv, hpc, PinCycRun.addSext]

set_option maxHeartbeats 4000000 in
/-- **THE EXECUTE STAGE AT EVERY REACHED NON-PIN WALK STATE** (header). -/
theorem execCyOfWalk (pcL : Int) (w : Pin) (own : Bool) (x : PState) (n : Nat) (l : List PState)
    (hm : (pcL, w) ∈ pinsW9a) (hw : walkOwn w = some own) (hx : preach own (pinStart pcL) x n)
    (hp : pstep own x = some l) (hne : l ≠ []) : execCyAt x.psPc := by
  intro a hdec T st hpre
  obtain ⟨a', hdec', hokB⟩ := walkDec pcL w own x n l hm hw hx hp hne
  obtain ⟨a'', hdec'', hflow⟩ := walkFlow pcL w own x n l hm hw hx hp hne
  rw [hdec] at hdec' hdec''
  cases hdec'; cases hdec''
  have hcls := walkClass pcL w own x n l hm hw hx hp hne
  have hf := PinCycRun.notFence own x l hp hne
  generalize x.psPc = pc at *
  obtain ⟨hpc, hcfg, hrb, hnpc, han, hro, hn, hok0⟩ := hpre
  have hb := dfInstrB5 a st.d hn hok0 (by rw [hro]; exact hokB)
  unfold classOk at hcls
  rw [hdec] at hcls
  by_cases hpl : plainC a = true
  · exact execPlain pc a hdec hpl hokB hflow hf T st ⟨hpc, hcfg, hrb, hnpc, han, hro, hn, hok0⟩
  have hpl' : plainC a = false := by simpa using hpl
  simp only [hpl', Bool.false_or] at hcls
  have hfin : ∀ (ok : BitVec 64 → Prop),
      cyB kA (kAa pc) cyS T (ctlPost ok st) (uxaExecAs a) st →
      (∀ v, ok v → ∃ pc', pc' ∈ succPcs pc ∧ v = BitVec.ofInt 64 pc') →
      cyB kA (kAa pc) cyS T (execPost pc st) (uxaExecAs a) st := by
    intro ok hC hs
    exact cyBMono _ _ (fun r st' h => PinCycRun.ctlExec pc ok st r st' h.1 h.2 hs) _ _
      (cyDf kA (kAa pc) cyS T _ _ _ st hrb hC hb)
  have hret : ∀ (ok : BitVec 64 → Prop) (c : instruction),
      cyB kA (kAa pc) cyS T (ctlPost ok st) (execute c) st →
      cyB kA (kAa pc) cyS T (ctlPost ok st) (uxaExecAs c) st := fun ok c h =>
    cyUxaOf kA (kAa pc) T c _ st
      (cyBMono _ _ (fun r st' h => PinCycRun.ctlPostRetire ok st r st' h) _ _ h)
  rcases Bool.or_eq_true_iff.1 hcls with h1 | h2
  · rw [Bool.and_eq_true] at h1
    obtain ⟨h1, hst⟩ := h1
    have hst' : roleIsStore (krole pc) = false := by simpa using hst
    cases a
    case BTYPE x =>
      obtain ⟨imm, rs2, rs1, op⟩ := x
      have hk : kflowOf pc = .FLbranch (pc + imm.toInt) := hflow.symm.trans (by rfl)
      obtain ⟨hsF, hsT⟩ := PinCycRun.succBranch pc _ hf hst' hk
      refine hfin _ (hret _ _ (cyExecBtype kA (kAa pc) T imm rs2 rs1 op st hcfg hrb)) ?_
      intro v hv
      rcases hv with hv | hv
      · exact ⟨_, hsF, hv.trans hnpc⟩
      · exact ⟨_, hsT, PinCycRun.brOk pc st hpc imm v hv⟩
    case C_BEQZ x =>
      obtain ⟨imm, rs⟩ := x
      have hk : kflowOf pc = .FLbranch (pc + (BitVec.signExtend 13 (imm ++ 0#1)).toInt) :=
        hflow.symm.trans (by rfl)
      obtain ⟨hsF, hsT⟩ := PinCycRun.succBranch pc _ hf hst' hk
      refine hfin _ (cyUxaRedir kA (kAa pc) T _ _ _ st rfl
        (by simp only [execute]; exact cyExecBtype kA (kAa pc) T _ _ _ _ st hcfg hrb)) ?_
      intro v hv
      rcases hv with hv | hv
      · exact ⟨_, hsF, hv.trans hnpc⟩
      · exact ⟨_, hsT, PinCycRun.brOk pc st hpc _ v hv⟩
    case C_BNEZ x =>
      obtain ⟨imm, rs⟩ := x
      have hk : kflowOf pc = .FLbranch (pc + (BitVec.signExtend 13 (imm ++ 0#1)).toInt) :=
        hflow.symm.trans (by rfl)
      obtain ⟨hsF, hsT⟩ := PinCycRun.succBranch pc _ hf hst' hk
      refine hfin _ (cyUxaRedir kA (kAa pc) T _ _ _ st rfl
        (by simp only [execute]; exact cyExecBtype kA (kAa pc) T _ _ _ _ st hcfg hrb)) ?_
      intro v hv
      rcases hv with hv | hv
      · exact ⟨_, hsF, hv.trans hnpc⟩
      · exact ⟨_, hsT, PinCycRun.brOk pc st hpc _ v hv⟩
    case JAL x =>
      obtain ⟨imm, ⟨rd⟩⟩ := x
      have hk : kflowOf pc = .FLjump (pc + imm.toInt) ∨ kflowOf pc = .FLcall (pc + imm.toInt) := by
        rw [← hflow]; simp only [astFlow]; split <;> simp
      have hsJ := PinCycRun.succJump pc _ hf hst' hk
      refine hfin _ (hret _ _ (cyExecJal kA (kAa pc) T imm _ st hcfg hrb)) ?_
      intro v hv
      exact ⟨_, hsJ, PinCycRun.brOk pc st hpc imm v hv⟩
    case C_J imm =>
      have hk : kflowOf pc = .FLjump (pc + (BitVec.signExtend 21 (imm ++ 0#1)).toInt) ∨
          kflowOf pc = .FLcall (pc + (BitVec.signExtend 21 (imm ++ 0#1)).toInt) :=
        Or.inl (hflow.symm.trans (by rfl))
      have hsJ := PinCycRun.succJump pc _ hf hst' hk
      refine hfin _ (cyUxaRedir kA (kAa pc) T _ _ _ st rfl
        (by simp only [execute]; exact cyExecJal kA (kAa pc) T _ _ st hcfg hrb)) ?_
      intro v hv
      exact ⟨_, hsJ, PinCycRun.brOk pc st hpc _ v hv⟩
    all_goals simp [brC, jalC] at h1
  · cases a
    case CSRReg x =>
      obtain ⟨k, ⟨r1⟩, rd, op⟩ := x
      cases op
      case CSRRS =>
        simp only [csrC, Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true] at h2
        obtain ⟨rfl, hk⟩ := h2
        have hk0 : kflowOf pc = .FLnone := hflow.symm.trans (by rfl)
        have hsF := PinCycRun.succFall pc hf hk0
        rcases hk with rfl | rfl
        · refine hfin _ (hret _ _ (cyExecCsrRead kA (kAa pc) T _ _ (by decide) (by decide)
            (fun st' h1 h2 => cyCheckSepc kA (kAa pc) T st' h1 h2) st hcfg hrb)) ?_
          intro v hv; exact ⟨_, hsF, hv.trans hnpc⟩
        · refine hfin _ (hret _ _ (cyExecCsrRead kA (kAa pc) T _ _ (by decide) (by decide)
            (fun st' h1 h2 => cyCheckSatp kA (kAa pc) T st' h1 h2) st hcfg hrb)) ?_
          intro v hv; exact ⟨_, hsF, hv.trans hnpc⟩
      all_goals simp [csrC] at h2
    all_goals simp [csrC] at h2

/-- **`cycRun` FROM `hartConf`, the execute stage discharged** (header): `cycRunOfHartConfI` with
`execCyAt` proved at every reached non-pin state (`execCyOfWalk`) — the remaining premises: r1 at
the cycle (`fetchCyR1`), the run obligations `fetchOkR2` / `dataOkR` / `excRetR`, and the walk
start. -/
theorem cycRunOfHartConfE (G : Gexec) (i : Nat) (row : List Lbl) (p0 : Pexv6) (dv : Nat → Efab)
    (em : Hemission) (pcL : Int) (w : Pin) (own : Bool)
    (hcf : hartConf i row p0 dv em) (hm : (pcL, w) ∈ pinsW9a) (hw : walkOwn w = some own)
    (hft : kFetchText em)
    (hR1 : ∀ s n l, preach own (pinStart pcL) s n → pstep own s = some l → l ≠ [] →
      fetchCyR1 s.psPc)
    (hfetch : ∀ s n, preach own (pinStart pcL) s n → fetchOkRF p0 (dv 0) em s.psPc)
    (hdata : ∀ s n, preach own (pinStart pcL) s n → dataOkRF p0 (dv 0) em s.psPc)
    (hexc : ∀ s n, preach own (pinStart pcL) s n → excRetR G i p0 (dv 0) em s.psPc)
    (base rest : List Eitem) (hes : em.emItems = base ++ rest)
    (hstart : ∀ p d, pevrun (base.map Prod.fst) p0 (dv 0) p d →
      ∃ (cpu : CPU) (rs : RegFile) (fn : Option (Bool × Bool × Bool × Bool)) (ib : Ibch),
        p = .PHart cpu (.pure ()) rs fn ib ∧ kInv (pinStart pcL).psPc rs) :
    ∃ (mid rest' : List Eitem) (s : PState) (n : Nat) (p' : Pexv6) (d' : Efab),
      rest = mid ++ rest' ∧ cycRun G i em own base (pinStart pcL) mid s ∧
      preach own (pinStart pcL) s n ∧ walkBd p0 (dv 0) em (base ++ mid) s.psPc p' d' ∧
      cycStop G i p0 (dv 0) em own (base ++ mid) s rest' :=
  cycRunOfHartConfI G i row p0 dv em pcL w own hcf hm hw hft hR1
    (fun s n l hs hp hne => execCyOfWalk pcL w own s n l hm hw hs hp hne)
    hfetch hdata hexc base rest hes hstart

end PinCycRun
end Weak
