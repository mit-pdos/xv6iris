/-
Weak: **W9a (B) B5 — `cycRun` from `hartConf`, part 2: THE ASSEMBLY** (plan
`notes/weak-allocproc-plan.md` rev 52 §C "W9a (B)" (B5); [OWN.85] Q-B5-CYCLE = C1; report
`PROGRESS-cycRun.md`).  Lean-only, no Rocq twin.

`cycRun` (`Weak/WeakRvwmoPinBridge5.lean:295`, r4) is PROVED from the hart's conformance
(`hartConf`), cut into:
* **(1) the cycle split** (FAITHFUL, proved here): the emission is the label sequence of a run of
  real `pstepEv` steps (`hemitPevrun`); from a cycle boundary (`.pure`) the run takes PLIC wire
  writes and a parked fence, then the boundary step `LInstr` to `riscvStep tick` (`pureSplit`);
  `PinCycRun.cyRun` then follows the cycle to its first `.pure` (or a stop node, or the end of
  the emission);
* **(2)–(3) the Sail cycle fact** `cySailAt pc` (NAMED here, the B1-style value walk of
  `riscvStep`): every path of the cycle from a register file in the kernel configuration
  `kInv pc` (PC = pc; the decoder's registers `cur_privilege`/`misa`/`menvcfg`/`mseccfg` at
  `drefS`'s values, `hart_state` active, `mstatus.TVM = 0`) satisfies `cyB` with the post
  `cyPost pc` — once the fetch log is a complete arm AT `pc`: the announced role is the arm's,
  B1's slots are full, the next PC is a walk successor (`succPcs`, `tick_pc`), the configuration
  is kept — and the stop post `cyT pc`: a trap after a complete fetch is an EXCEPTION at a
  load/store (no illegal instruction, no misaligned target, no `ecall`/`ebreak`);
* **(4) the run obligations** (NAMED, each its own Prop): **r2-shaped** `fetchOkR2` — a walk
  cycle that takes no interrupt fetches a complete arm whose reads are at `pc` (and `pc + 2`):
  Sail's `translateAddr (Virtaddr PC)` is the identity on the kernel text and raises no
  translation / access fault (`Fetch.lean:217-232`); `dataOkR` — a walk load/store takes no
  synchronous exception (its data address translates and passes PMP/PMA); `excRetR` — an
  interrupt taken at a walk boundary whose excursion is fence-free (`texcRes`) returns to the
  boundary at the same pc in the kernel configuration (`sret` to `sepc`); the walk START
  (`kInv` at the boundary after the load's cycle) is the caller's.

**THE THEOREM** `cycRunOfRun` (header): at a walk-certifying row of `pinsW9a`, from a boundary
in the kernel configuration at the walk start, the emission continues with a cycle alignment
`cycRun` to a walk state `s` the walk reaches, after which the emission EITHER is at `s`'s
boundary with `s` a PIN (`pstep own s = some []`), OR ends inside `s`'s cycle, OR takes an
interrupt at `s` with no fence-free aligned excursion (B2-fenced's case, `trapFencedSegPinC`).

Spec: Sail `Step.lean:331-404` (dispatch before fetch, fetch, announce, decode, `nextPC := PC +
len`, execute, `tick_pc`), `SysControl.lean:733-792` (every trap writes `scause`/`mcause` first,
bit 63 = interrupt); RVWMO silent (po is the instruction sequence); Zifencei: B4's fetch clause
(`kFetchText`); PMAs: the fetch PMA/PMP checks are inside `fetchOkR2`.  FAITHFUL; the named
Props are proof obligations (FAITHFUL to discharge, WEAKER while named).  Every Lean-only helper
is `Weak.PinCycRun.*`.
-/
import Weak.PinCycRun
import Weak.WeakRvwmoPinBridge5

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Sail Sail.ConcurrencyInterfaceV1 LeanRV64D LeanRV64D.Functions
open Sail.ArchSem (FreeM)
open Wlabel
open KernelPinsDef
open WeakRvwmoPinBridge3 (preach)
open WeakRvwmoPinBridge4 (walkOwn)

namespace PinCycRun
open SailCycleOrderK PinDataflow

/-! ## 1. The emission is a run -/

theorem PinCycRun.admRunPevrun (instr : Bool) (p : Pexv6) (d : Efab) (ls : List Wlabel) (p' : Pexv6)
    (d' : Efab) : admRun instr p d ls p' d' → pevrun ls p d p' d' := by
  intro h
  induction h with
  | ARnil p d => exact .nil p d
  | ARcons p d l p1 d1 ls p' d' _ hs _ ih => exact .more hs ih

theorem pevrunApp {l1 l2 : List Wlabel} {p : Pexv6} {d : Efab} {p1 : Pexv6} {d1 : Efab}
    {p2 : Pexv6} {d2 : Efab} :
    pevrun l1 p d p1 d1 → pevrun l2 p1 d1 p2 d2 → pevrun (l1 ++ l2) p d p2 d2 := by
  intro h1 h2
  induction h1 with
  | nil => exact h2
  | more hs _ ih => exact .more hs (ih h2)

theorem pevrunSplit (l1 l2 : List Wlabel) :
    ∀ (p : Pexv6) (d : Efab) (p2 : Pexv6) (d2 : Efab), pevrun (l1 ++ l2) p d p2 d2 →
      ∃ p1 d1, pevrun l1 p d p1 d1 ∧ pevrun l2 p1 d1 p2 d2 := by
  induction l1 with
  | nil => intro p d p2 d2 h; exact ⟨p, d, .nil p d, h⟩
  | cons l l1 ih =>
    intro p d p2 d2 h
    cases h with
    | more hs hr =>
      obtain ⟨p1, d1, h1, h2⟩ := ih _ _ _ _ hr
      exact ⟨p1, d1, .more hs h1, h2⟩

theorem PinCycRun.eadmFst (ls : List Wlabel) : (eadm ls).map Prod.fst = ls := by
  induction ls with
  | nil => rfl
  | cons l ls ih => simp only [eadm, List.map_cons] at ih ⊢; rw [ih]

/-- **The emission is a run** of real `pstepEv` steps, label by label. -/
theorem hemitPevrun (dv : Nat → Efab) (k : Nat) (ws : Wstate) (row : List Lbl) (p : Pexv6)
    (es : List Eitem) (pfin : Pexv6) :
    hemit dv k ws row p es pfin → pevrun (es.map Prod.fst) p (dv k) pfin (dv (k + row.length)) := by
  intro h
  induction h with
  | HEnil k ws p => exact .nil _ _
  | HEone k ws lb row p ls pa da l p' es pfin har _ hst _ ih =>
    rw [List.map_append, PinCycRun.eadmFst, List.map_cons]
    have e : k + 1 + row.length = k + (lb :: row).length := by simp; omega
    rw [e] at ih
    exact pevrunApp (PinCycRun.admRunPevrun _ _ _ _ _ _ har) (.more hst ih)
  | HEpair k ws lb row p ls1 pa da l1 pm dm ls2 pm2 dm2 l2 p' es pfin har1 _ hst1 har2 hst2 _ ih =>
    rw [List.map_append, PinCycRun.eadmFst, List.map_cons, List.map_append, PinCycRun.eadmFst,
      List.map_cons]
    have e : k + 1 + row.length = k + (lb :: row).length := by simp; omega
    rw [e] at ih
    exact pevrunApp (PinCycRun.admRunPevrun _ _ _ _ _ _ har1)
      (.more hst1 (pevrunApp (PinCycRun.admRunPevrun _ _ _ _ _ _ har2) (.more hst2 ih)))

theorem hartConfPevrun (i : Nat) (row : List Lbl) (p0 : Pexv6) (dv : Nat → Efab) (em : Hemission) :
    hartConf i row p0 dv em →
    pevrun (em.emItems.map Prod.fst) p0 (dv 0) em.emFin (dv row.length) := by
  intro h
  have := hemitPevrun dv 0 wsInit row p0 em.emItems em.emFin h
  rwa [Nat.zero_add] at this

/-- A fetch label is never a row label: its item is administrative. -/
theorem hemitFeNone (dv : Nat → Efab) (k : Nat) (ws : Wstate) (row : List Lbl) (p : Pexv6)
    (es : List Eitem) (pfin : Pexv6) :
    hemit dv k ws row p es pfin → ∀ a tvs t, (LIFetch a tvs, t) ∈ es → t = none := by
  intro h
  induction h with
  | HEnil k ws p => intro a tvs t hit; exact absurd hit List.not_mem_nil
  | HEone k ws lb row p ls pa da l p' es pfin _ hre _ _ ih =>
    intro a tvs t hit
    rcases List.mem_append.1 hit with hit | hit
    · simp only [eadm, List.mem_map] at hit
      obtain ⟨_, _, e⟩ := hit
      simp only [Prod.mk.injEq] at e
      exact e.2.symm
    rcases List.mem_cons.1 hit with e | hit
    · simp only [Prod.mk.injEq] at e
      obtain ⟨rfl, -⟩ := e
      obtain ⟨_, _, _, hpr⟩ := hre
      simp [projLbl] at hpr
    · exact ih a tvs t hit
  | HEpair k ws lb row p ls1 pa da l1 pm dm ls2 pm2 dm2 l2 p' es pfin _ hre _ _ _ _ ih =>
    intro a tvs t hit
    obtain ⟨aq, rl, base, tvs0, data, asrc1, asrc2, vsrc2, rfl, rfl, _, _, _⟩ := hre
    rcases List.mem_append.1 hit with hit | hit
    · simp only [eadm, List.mem_map] at hit
      obtain ⟨_, _, e⟩ := hit
      simp only [Prod.mk.injEq] at e
      exact e.2.symm
    rcases List.mem_cons.1 hit with e | hit
    · simp at e
    rcases List.mem_append.1 hit with hit | hit
    · simp only [eadm, List.mem_map] at hit
      obtain ⟨_, _, e⟩ := hit
      simp only [Prod.mk.injEq] at e
      exact e.2.symm
    rcases List.mem_cons.1 hit with e | hit
    · simp at e
    · exact ih a tvs t hit

/-! ## 2. The kernel instance -/

/-- The fetch filter of the kernel text: a text byte is the tracked byte (B4's `kFetchText`). -/
def kA (a : Int) (b : BitVec 8) : Prop := textLo ≤ a → a < textHi → b = BitVec.ofNat 8 (kbyte a)

/-- The fetch-address oracle of a walk cycle at `pc`: the `k`-th instruction-fetch read is at
`pc + 2k` (the fetch's VA is `PC` then `PC + 2`, `Fetch.lean:265-288`, translated to itself). -/
def kAa (pc : Int) (k : Nat) (a : Int) : Prop := a = pc + 2 * (k : Int)

/-- The stop registers: the trap handler's cause registers (`SysControl.lean:751,769`). -/
def cyS (r : Register) : Bool := decide (r = .scause) || decide (r = .mcause)

/-- The written cause's interrupt bit (bit 63, `trap_handler`'s first write). -/
def causeBit : (r : Register) → RegisterType r → Bool
  | .scause, v => v.getLsbD 63
  | .mcause, v => v.getLsbD 63
  | _, _ => false

/-- The fetch log as one of Sail's four fetch arms AT `pc` (`Fetch.lean:253-288`): one 4-byte
read (announced whole, or its low half when compressed), one 2-byte compressed read, or two
2-byte reads at `pc` and `pc + 2`. -/
def armOf (pc : Int) : List FeEnt → Option FetchArm
  | [⟨a, 4, w⟩] =>
      if a = pc then
        some (if isRVC (Sail.BitVec.extractLsb w 15 0) then .rvc4 w else .base4 w)
      else none
  | [⟨a, 2, h⟩] => if a = pc ∧ isRVC h = true then some (.rvc2 h) else none
  | [⟨a, 2, lo⟩, ⟨a', 2, hi⟩] => if a = pc ∧ a' = pc + 2 then some (.base22 lo hi) else none
  | _ => none

/-- The kernel configuration the walk runs in: the decoder's registers at `drefS`'s values
(`MachCSL/DecodeBridge.lean:262`), supervisor mode, an active hart, `mstatus.TVM = 0`, no
landing pad expected (`elp`, Zicfilp: `is_landing_pad_expected`, `Step.lean:362,386`). -/
def kCfg (rv : RegFile) : Prop :=
  rv .cur_privilege = Privilege.Supervisor ∧ rv .misa = 0x800000000014112D#64 ∧
  rv .menvcfg = menvcfgS ∧ rv .mseccfg = 0#64 ∧ rv .hart_state = HartState.HART_ACTIVE () ∧
  _get_Mstatus_TVM (rv .mstatus) = 0#1 ∧ rv .elp = 0#1

/-- The boundary invariant at a walk pc. -/
def kInv (pc : Int) (rs : RegFile) : Prop := rs .PC = BitVec.ofInt 64 pc ∧ kCfg rs ∧ RbootAll rs

/-- The walk's successor pcs (`pstep`'s, by the instruction's class). -/
def succPcs (pc : Int) : List Int :=
  if wIsFence (kw pc) then []
  else if roleIsStore (krole pc) then [pc + wSize (kw pc)]
  else
    match kflowOf pc with
    | .FLnone => [pc + wSize (kw pc)]
    | .FLbranch tgt => [pc + wSize (kw pc), tgt]
    | .FLjump tgt => [tgt]
    | .FLcall tgt => [tgt]
    | _ => []

/-- A load or a store AST (an instruction with a data access), base or compressed. -/
def memC (c : instruction) : Bool :=
  match c with
  | .LOAD _ | .STORE _ | .C_LW _ | .C_LD _ | .C_SW _ | .C_SD _ | .C_LWSP _ | .C_LDSP _
  | .C_SWSP _ | .C_SDSP _ | .C_LBU _ | .C_LHU _ | .C_LH _ | .C_SB _ | .C_SH _ => true
  | _ => false

/-- The instruction at `pc` (Sail's decode of the image, `PinWalkTab.decS`) is a load or a
store. -/
noncomputable def memPc (pc : Int) : Bool :=
  match PinWalkTab.decS pc with
  | some c => memC c
  | none => false

/-- **THE CYCLE POST** at `pc` (header): the fetch log is a complete arm at `pc`, the announced
role is the arm's, B1's slots are full, the next PC is a walk successor, the configuration kept. -/
def cyPost (pc : Int) : Unit → CySt → Prop := fun _ st =>
  ∃ fa, armOf pc st.fe = some fa ∧
    st.an = true ∧ st.d.ok = true ∧ st.d.n = (dfDests st.d.ro).length ∧ st.d.ro = fa.annRole ∧
    (∃ pc', pc' ∈ succPcs pc ∧ st.rv .PC = BitVec.ofInt 64 pc') ∧ kCfg st.rv

/-- **THE STOP POST** at `pc` (header): a trap after the announce is an EXCEPTION at a load/store
(no illegal instruction, no misaligned target, no `ecall`/`ebreak` at a walk instruction). -/
def cyT (pc : Int) (st : CySt) (r : Register) (v : RegisterType r) : Prop :=
  st.an = true → causeBit r v = false ∧ memPc pc = true

/-- The cycle's initial state: the boundary register file in the kernel configuration, an empty
log, no announce, the reset channel (`ibNone`: role `ORnone`, no reads, empty slots). -/
def cyInit (pc : Int) (st : CySt) : Prop :=
  kInv pc st.rv ∧ st.fe = [] ∧ st.an = false ∧ st.d = ⟨OpRoles.ORnone, [], 0, true⟩

/-- **(2)–(3) THE SAIL CYCLE FACT at `pc` (NAMED, header)**: the B1-style value walk of
`riscvStep` — the next-pc arithmetic, the decode on the kernel configuration, the no-exception
causes that are not translation / access faults. -/
def cySailAt (pc : Int) : Prop :=
  ∀ (tick : Bool) (st : CySt), cyInit pc st →
    cyB kA (kAa pc) cyS (cyT pc) (cyPost pc) (riscvStep tick) st

/-! ## 3. The boundary: PLIC writes, a parked fence, then the boundary step -/

/-- The labels a hart at a cycle boundary can take before its boundary step: a parked fence
firing, a PLIC wire write — never a register write, never a fetch. -/
theorem PinCycRun.pureStepFacts (cpu : CPU) (rs : RegFile) (fn : Option (Bool × Bool × Bool × Bool))
    (ib : Ibch) (d : Efab) (l : Wlabel) (p1 : Pexv6) (d1 : Efab) :
    pstepEv (.PHart cpu (.pure ()) rs fn ib) d l p1 d1 →
    (l = LInstr ∧ fn = none ∧ ∃ tick, p1 = .PHart cpu (riscvStep tick) rs none ibNone) ∨
    (l ≠ LInstr ∧ (∀ rd srcs, l ≠ LRegW rd srcs) ∧ isFeLab l = false ∧
      ∃ rs1 fn1, p1 = .PHart cpu (.pure ()) rs1 fn1 ib ∧
        (∀ r, wireReg r = false → rs1 r = rs r) ∧ (RbootAll rs → RbootAll rs1)) := by
  intro h
  cases p1 with
  | PDisk dp => exact (show False from h).elim
  | PHart cpu1 m1 rs1 fn1 ib1 =>
  obtain ⟨rfl, ors, oib, obar, rfl, rfl, hh⟩ := h
  rcases hh with ⟨H, -⟩ | H
  · cases fn with
    | some f =>
      obtain ⟨pr, pw, sr, sw⟩ := f
      obtain ⟨rfl, rfl, rfl, rfl, -, rfl, -⟩ := H
      exact Or.inr ⟨(by intro e; cases e), (fun _ _ e => by cases e), rfl, rs, none, rfl,
        (fun _ _ => rfl), id⟩
    | none =>
      obtain ⟨tick, rfl, rfl, rfl, rfl, -, rfl, -⟩ := H
      exact Or.inl ⟨rfl, rfl, tick, rfl⟩
  · obtain ⟨mm, b, k, -, rfl, rfl, rfl, -, rfl, -, rfl⟩ := H
    right
    refine ⟨(by intro e; cases e), (fun _ _ e => by cases e), rfl, _, _, rfl, ?_, ?_⟩
    · intro r hr
      show pinSet rs mm b r = rs r
      unfold pinSet
      split
      · exact RegFile.set_other _ _ _ _ (by rintro rfl; cases hr)
      · exact RegFile.set_other _ _ _ _ (by rintro rfl; cases hr)
    · intro hrb
      show RbootAll (pinSet rs mm b)
      unfold pinSet
      split
      · exact rbootAllSet rs _ _ hrb trivial
      · exact rbootAllSet rs _ _ hrb trivial

/-- **The boundary split** (header): from a cycle boundary, the run either never takes the
boundary step, or takes PLIC writes / a parked fence (`ls0`) and then the boundary step `LInstr`
to the fresh cycle `riscvStep tick`, the register file kept off the wires. -/
theorem pureSplit : ∀ (ls : List Wlabel) (p : Pexv6) (d : Efab) (pE : Pexv6) (dE : Efab),
    pevrun ls p d pE dE → ∀ cpu rs fn ib, p = .PHart cpu (.pure ()) rs fn ib → RbootAll rs →
    LInstr ∉ ls ∨
    ∃ (ls0 ls1 : List Wlabel) (rs' : RegFile) (tick : Bool) (d1 : Efab),
      ls = ls0 ++ LInstr :: ls1 ∧ LInstr ∉ ls0 ∧
      (∀ l, l ∈ ls0 → (∀ rd srcs, l ≠ LRegW rd srcs) ∧ isFeLab l = false) ∧
      pevrun (ls0 ++ [LInstr]) p d (.PHart cpu (riscvStep tick) rs' none ibNone) d1 ∧
      pevrun ls1 (.PHart cpu (riscvStep tick) rs' none ibNone) d1 pE dE ∧
      (∀ r, wireReg r = false → rs' r = rs r) ∧ RbootAll rs' := by
  intro ls p d pE dE h
  induction h with
  | nil p d => intro _ _ _ _ _ _; exact Or.inl List.not_mem_nil
  | @more l ls p d p1 d1 p2 d2 hst hrest ih =>
    intro cpu rs fn ib hp hrb
    subst hp
    rcases PinCycRun.pureStepFacts cpu rs fn ib d l p1 d1 hst with
      ⟨rfl, rfl, tick, rfl⟩ | ⟨hne, hnr, hnf, rs1, fn1, rfl, hag, hrb1⟩
    · right
      exact ⟨[], ls, rs, tick, d1, rfl, List.not_mem_nil, (fun _ h => absurd h List.not_mem_nil),
        .more hst (.nil _ _), hrest, (fun _ _ => rfl), hrb⟩
    · rcases ih cpu rs1 fn1 ib rfl (hrb1 hrb) with hni |
        ⟨ls0, ls1, rs', tick, dd, rfl, hn0, h0, r1, r2, hag', hrb'⟩
      · left
        intro hm
        rcases List.mem_cons.1 hm with e | hm
        · exact hne e.symm
        · exact hni hm
      · right
        refine ⟨l :: ls0, ls1, rs', tick, dd, rfl, ?_, ?_, .more hst r1, r2,
          fun r hr => (hag' r hr).trans (hag r hr), hrb'⟩
        · intro hm
          rcases List.mem_cons.1 hm with e | hm
          · exact hne e.symm
          · exact hn0 hm
        intro l' hl'
        rcases List.mem_cons.1 hl' with rfl | hl'
        · exact ⟨hnr, hnf⟩
        · exact h0 l' hl'

/-! ## 4. The walk's successors, the slots, the arm's reads -/

/-- Every successor pc of a non-pin step is a successor state's pc. -/
theorem pstepSucc (own : Bool) (s : PState) (l : List PState) :
    pstep own s = some l → l ≠ [] → ∀ pc', pc' ∈ succPcs s.psPc → ∃ s', s' ∈ l ∧ s'.psPc = pc' := by
  obtain ⟨pc, t, rs⟩ := s
  intro h hne pc' hpc
  unfold pstep at h
  unfold succPcs at hpc
  dsimp only at h hpc
  split at h
  · cases h
  · split at h
    · cases h; exact absurd rfl hne
    · rename_i hf
      simp only [hf, Bool.false_eq_true, ↓reduceIte] at hpc
      split at h
      · rename_i hst
        simp only [hst, ↓reduceIte, List.mem_singleton] at hpc
        subst hpc
        split at h
        · cases h; exact absurd rfl hne
        · split at h
          · cases h; exact ⟨_, List.mem_singleton.2 rfl, rfl⟩
          · cases h
      · rename_i hst
        simp only [hst, Bool.false_eq_true, ↓reduceIte] at hpc
        split at h <;> rename_i hk <;> rw [hk] at hpc
        · split at h
          · cases h; exact absurd rfl hne
          · cases h
            rcases List.mem_cons.1 hpc with rfl | hpc
            · exact ⟨_, List.mem_cons_self, rfl⟩
            · rw [List.mem_singleton] at hpc; subst hpc
              exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton.2 rfl), rfl⟩
        · cases h
          rw [List.mem_singleton] at hpc; subst hpc
          exact ⟨_, List.mem_singleton.2 rfl, rfl⟩
        · split at h
          · cases h
            rw [List.mem_singleton] at hpc; subst hpc
            exact ⟨_, List.mem_singleton.2 rfl, rfl⟩
          · cases h
        · cases hpc
        · cases hpc
        · cases h
          rw [List.mem_singleton] at hpc; subst hpc
          exact ⟨_, List.mem_singleton.2 rfl, rfl⟩

theorem PinCycRun.dfScanNeutral (ro : OpRoles) (p : Nat × Bool) (ls : List Wlabel)
    (h : ∀ l, l ∈ ls → ∀ rd srcs, l ≠ LRegW rd srcs) : dfScan ro p ls = p := by
  induction ls generalizing p with
  | nil => rfl
  | cons l ls ih =>
    show dfScan ro (dfLab ro p.1 p.2 l) ls = p
    rw [dfLabNeutral ro p.1 p.2 l (h l List.mem_cons_self)]
    exact ih p (fun l' hl' => h l' (List.mem_cons_of_mem _ hl'))

theorem PinCycRun.feLabsMem (ls : List Wlabel) (l : Wlabel) : l ∈ feLabs ls → l ∈ ls := by
  intro h; exact (List.mem_filter.1 h).1

theorem PinCycRun.fetchItemOf (g : List Eitem) (e : FeEnt) (l : Wlabel)
    (hg : (l, none) ∈ g) (h : feLab e l) : fetchItem g e.a e.n e.w := by
  obtain ⟨tvs, rfl, hl, hb⟩ := h
  exact ⟨tvs, hg, hl, hb⟩

/-- A complete arm in the log, with its labels' items in `g`, IS the arm's reads in `g`. -/
theorem armItems (pc : Int) (fe : List FeEnt) (fa : FetchArm) (ls : List Wlabel) (g : List Eitem)
    (ha : armOf pc fe = some fa) (h2 : List.Forall₂ feLab fe (feLabs ls))
    (hg : ∀ l, l ∈ ls → isFeLab l = true → (l, none) ∈ g) : fa.items g pc := by
  have hin : ∀ l, l ∈ feLabs ls → (l, none) ∈ g := fun l hl =>
    hg l (PinCycRun.feLabsMem ls l hl) (List.mem_filter.1 hl).2
  generalize feLabs ls = L at h2 hin
  unfold armOf at ha
  split at ha
  · rename_i a w
    split at ha
    · rename_i hpc
      subst hpc
      cases h2 with
      | cons he hr =>
        cases hr
        rename_i l1
        have hit := PinCycRun.fetchItemOf g ⟨a, 4, w⟩ l1 (hin l1 List.mem_cons_self) he
        split at ha
        · rename_i hrvc
          cases ha
          exact ⟨hit, hrvc⟩
        · cases ha
          exact hit
    · cases ha
  · rename_i a h
    split at ha
    · rename_i hc
      obtain ⟨rfl, hrvc⟩ := hc
      cases ha
      cases h2 with
      | cons he hr =>
        cases hr
        rename_i l1
        exact ⟨PinCycRun.fetchItemOf g ⟨a, 2, h⟩ l1 (hin l1 List.mem_cons_self) he, hrvc⟩
    · cases ha
  · rename_i a lo a' hi
    split at ha
    · rename_i hc
      obtain ⟨rfl, rfl⟩ := hc
      cases ha
      cases h2 with
      | cons he hr =>
        cases hr with
        | cons he' hr' =>
          cases hr'
          rename_i l1 l2
          exact ⟨PinCycRun.fetchItemOf g ⟨a, 2, lo⟩ l1 (hin l1 List.mem_cons_self) he,
            PinCycRun.fetchItemOf g ⟨a + 2, 2, hi⟩ l2
              (hin l2 (List.mem_cons_of_mem _ List.mem_cons_self)) he'⟩
    · cases ha
  · cases ha

/-! ## 5. The run obligations (named) -/

/-- The hart sits at a stop write (a cause register) whose interrupt bit is `b`. -/
def atCause (b : Bool) (p : Pexv6) : Prop :=
  ∃ (cpu : CPU) (r : Register) (v : RegisterType r) (k : Unit → SailM Unit) (rs : RegFile)
    (fn : Option (Bool × Bool × Bool × Bool)) (ib : Ibch),
    p = .PHart cpu (.impure (.ok (.regWrite r v)) k) rs fn ib ∧ cyS r = true ∧ causeBit r v = b

/-- The hart sits at a cycle boundary. -/
def atPure (p : Pexv6) : Prop :=
  ∃ (cpu : CPU) (rs : RegFile) (fn : Option (Bool × Bool × Bool × Bool)) (ib : Ibch),
    p = .PHart cpu (.pure ()) rs fn ib

/-- A WALK BOUNDARY: a state of the hart's run after the emission prefix `pfx`, at a cycle
boundary, in the kernel configuration at `pc`. -/
def walkBd (p0 : Pexv6) (d0 : Efab) (em : Hemission) (pfx : List Eitem) (pc : Int) (p : Pexv6)
    (d : Efab) : Prop :=
  (∃ rest, em.emItems = pfx ++ rest) ∧ pevrun (pfx.map Prod.fst) p0 d0 p d ∧
  ∃ (cpu : CPU) (rs : RegFile) (fn : Option (Bool × Bool × Bool × Bool)) (ib : Ibch),
    p = .PHart cpu (.pure ()) rs fn ib ∧ kInv pc rs

/-- A WALK CYCLE's start: from a walk boundary after `pfx`, the labels `ls0` (PLIC writes, a
parked fence) and the boundary step reach the fresh cycle `q`. -/
def cycStart (p0 : Pexv6) (d0 : Efab) (em : Hemission) (pfx : List Eitem) (pc : Int)
    (ls0 : List Wlabel) (q : Pexv6) (d1 : Efab) : Prop :=
  ∃ p d, walkBd p0 d0 em pfx pc p d ∧ pevrun (ls0 ++ [LInstr]) p d q d1 ∧
    ∃ (cpu : CPU) (tick : Bool) (rs : RegFile), q = .PHart cpu (riscvStep tick) rs none ibNone

/-- The cycle's labels are the emission's after `pfx`. -/
def cycIn (em : Hemission) (pfx : List Eitem) (ls0 ls1 : List Wlabel) : Prop :=
  ∃ rest, em.emItems = pfx ++ rest ∧ (ls0 ++ LInstr :: ls1) <+: rest.map Prod.fst

/-- The hart's instruction has been announced (its channel carries the announced bits). -/
def atAnn (p : Pexv6) : Prop :=
  ∃ (cpu : CPU) (m : SailM Unit) (rs : RegFile) (fn : Option (Bool × Bool × Bool × Bool))
    (ib : Ibch), p = .PHart cpu m rs fn ib ∧ ib.ibBits.isSome = true

/-- **(4a) r2-SHAPED: THE FETCH OF A WALK CYCLE** (NAMED, header): in a walk cycle (i) the `k`-th
instruction-fetch read is at physical address `pc + 2k` — Sail fetches at `translateAddr
(Virtaddr PC)` and `translateAddr (Virtaddr (PC + 2))` (`Fetch.lean:217-288`), the identity on
the kernel text under Sv39 after `kvminithart`; (ii) the fetch raises no fault — a synchronous
exception's cause write in a walk cycle comes after the instruction's announce (no translation /
access fault: the kernel's PTEs, PMP and PMAs admit the text fetch). -/
def fetchOkR2 (p0 : Pexv6) (d0 : Efab) (em : Hemission) (pc : Int) : Prop :=
  (∀ (pfx : List Eitem) (ls0 : List Wlabel) (q : Pexv6) (d1 : Efab) (ls1 : List Wlabel)
    (pm : Pexv6) (dm : Efab) (a : Int) (tvs : List (Nat × BitVec 8)),
    cycStart p0 d0 em pfx pc ls0 q d1 → cycIn em pfx ls0 (ls1 ++ [LIFetch a tvs]) →
    irun ls1 q d1 pm dm → a = pc + 2 * ((feLabs ls1).length : Int)) ∧
  (∀ (pfx : List Eitem) (ls0 : List Wlabel) (q : Pexv6) (d1 : Efab) (ls1 : List Wlabel)
    (pm : Pexv6) (dm : Efab),
    cycStart p0 d0 em pfx pc ls0 q d1 → cycIn em pfx ls0 ls1 → irun ls1 q d1 pm dm →
    atCause false pm → atAnn pm)

/-- **(4a′) r2 AT THE FIRST `LInstr`** (NAMED, header; the restated `fetchOkR2`, plan of
`PROGRESS-r2glue-inc1.md` "Design (fixed)"): as `fetchOkR2`, with the premise `LInstr ∉ ls0` (the
boundary labels before the cycle's `LInstr` hold no other `LInstr`) and, in (i), the fetch label a
STEP of the in-cycle run (`irun (ls1 ++ [LIFetch a tvs])`). `fetchOkR2` implies it
(`fetchOkRFOfR2`); its use `cycWalk` builds exactly these premises. -/
def fetchOkRF (p0 : Pexv6) (d0 : Efab) (em : Hemission) (pc : Int) : Prop :=
  (∀ (pfx : List Eitem) (ls0 : List Wlabel) (q : Pexv6) (d1 : Efab) (ls1 : List Wlabel)
    (pm : Pexv6) (dm : Efab) (a : Int) (tvs : List (Nat × BitVec 8)),
    LInstr ∉ ls0 → cycStart p0 d0 em pfx pc ls0 q d1 → cycIn em pfx ls0 (ls1 ++ [LIFetch a tvs]) →
    irun (ls1 ++ [LIFetch a tvs]) q d1 pm dm → a = pc + 2 * ((feLabs ls1).length : Int)) ∧
  (∀ (pfx : List Eitem) (ls0 : List Wlabel) (q : Pexv6) (d1 : Efab) (ls1 : List Wlabel)
    (pm : Pexv6) (dm : Efab),
    LInstr ∉ ls0 → cycStart p0 d0 em pfx pc ls0 q d1 → cycIn em pfx ls0 ls1 →
    irun ls1 q d1 pm dm → atCause false pm → atAnn pm)

/-- `irun` of a prefix. -/
theorem PinCycRun.irunPrefix : ∀ (ls1 ls2 : List Wlabel) (p : Pexv6) (d : Efab) (p' : Pexv6)
    (d' : Efab), irun (ls1 ++ ls2) p d p' d' → ∃ pm dm, irun ls1 p d pm dm := by
  intro ls1
  induction ls1 with
  | nil => intro _ p d _ _ _; exact ⟨p, d, irun.nil _ _⟩
  | cons l ls ih =>
    intro ls2 p d p' d' h
    cases h with
    | more hst hr =>
      obtain ⟨pm, dm, h'⟩ := ih ls2 _ _ _ _ hr
      exact ⟨pm, dm, irun.more hst h'⟩

theorem fetchOkRFOfR2 (p0 : Pexv6) (d0 : Efab) (em : Hemission) (pc : Int)
    (h : fetchOkR2 p0 d0 em pc) : fetchOkRF p0 d0 em pc := by
  refine ⟨fun pfx ls0 q d1 ls1 pm dm a tvs _ hcs hcin hir => ?_,
    fun pfx ls0 q d1 ls1 pm dm _ hcs hcin hir hac => h.2 pfx ls0 q d1 ls1 pm dm hcs hcin hir hac⟩
  obtain ⟨pm', dm', hir'⟩ := PinCycRun.irunPrefix ls1 _ q d1 pm dm hir
  exact h.1 pfx ls0 q d1 ls1 pm' dm' a tvs hcs hcin hir'

/-- **(4b) THE DATA ACCESS OF A WALK LOAD/STORE** (NAMED, header): a walk load/store cycle takes
no synchronous exception (its data address translates, and passes PMP/PMA). -/
def dataOkR (p0 : Pexv6) (d0 : Efab) (em : Hemission) (pc : Int) : Prop :=
  memPc pc = true →
  ∀ (pfx : List Eitem) (ls0 : List Wlabel) (q : Pexv6) (d1 : Efab) (ls1 : List Wlabel)
    (pm : Pexv6) (dm : Efab),
    cycStart p0 d0 em pfx pc ls0 q d1 → cycIn em pfx ls0 ls1 → irun ls1 q d1 pm dm →
    ¬ atCause false pm

/-- **(4b′) `dataOkR` at the first `LInstr`** (header; moved here from `PinDataOkAsm.lean`, where
`dataOkRFOf` proves it from `dataRealized`): `dataOkR` with the premise `LInstr ∉ ls0`. -/
def dataOkRF (p0 : Pexv6) (d0 : Efab) (em : Hemission) (pc : Int) : Prop :=
  memPc pc = true →
  ∀ (pfx : List Eitem) (ls0 : List Wlabel) (q : Pexv6) (d1 : Efab) (ls1 : List Wlabel)
    (pm : Pexv6) (dm : Efab),
    LInstr ∉ ls0 → cycStart p0 d0 em pfx pc ls0 q d1 → cycIn em pfx ls0 ls1 → irun ls1 q d1 pm dm →
    ¬ atCause false pm

theorem dataOkRFOfR (p0 : Pexv6) (d0 : Efab) (em : Hemission) (pc : Int)
    (h : dataOkR p0 d0 em pc) : dataOkRF p0 d0 em pc :=
  fun hm pfx ls0 q d1 ls1 pm dm _ => h hm pfx ls0 q d1 ls1 pm dm

/-- **(4c) THE RETURN OF A FENCE-FREE INTERRUPT EXCURSION** (NAMED, header): an interrupt taken
at a walk boundary whose excursion is fence-free and aligned (`texcRes`) has such an excursion
after which the hart is back at a boundary at the same pc in the kernel configuration (Sail:
`sepc ← pc` at the trap, `sret` jumps to `sepc` and restores the privilege). -/
def excRetR (G : Gexec) (i : Nat) (p0 : Pexv6) (d0 : Efab) (em : Hemission) (pc : Int) : Prop :=
  ∀ (pfx : List Eitem) (ls0 : List Wlabel) (q : Pexv6) (d1 : Efab) (ls1 : List Wlabel)
    (pm : Pexv6) (dm : Efab) (rest : List Eitem),
    cycStart p0 d0 em pfx pc ls0 q d1 → cycIn em pfx ls0 ls1 → irun ls1 q d1 pm dm →
    atCause true pm → em.emItems = pfx ++ rest →
    (∃ gx rest', rest = gx ++ rest' ∧ texcRes G i em pfx gx) →
    ∃ gx rest', rest = gx ++ rest' ∧ texcRes G i em pfx gx ∧ gx ≠ [] ∧
      ∀ p d p' d', walkBd p0 d0 em pfx pc p d → pevrun (gx.map Prod.fst) p d p' d' →
        ∃ (cpu : CPU) (rs : RegFile) (fn : Option (Bool × Bool × Bool × Bool)) (ib : Ibch),
          p' = .PHart cpu (.pure ()) rs fn ib ∧ kInv pc rs

/-- How the walk stops (after the alignment `cycRun` reached `s` at a walk boundary after `pfx`,
the remaining emission `rest`): at a PIN; with the emission ending inside `s`'s cycle; or at an
interrupt with no fence-free aligned excursion. -/
def cycStop (G : Gexec) (i : Nat) (p0 : Pexv6) (d0 : Efab) (em : Hemission) (own : Bool)
    (pfx : List Eitem) (s : PState) (rest : List Eitem) : Prop :=
  pstep own s = some [] ∨
  (∃ (ls0 ls1 : List Wlabel) (q : Pexv6) (d1 : Efab) (pE : Pexv6) (dE : Efab),
    cycStart p0 d0 em pfx s.psPc ls0 q d1 ∧ rest.map Prod.fst = ls0 ++ LInstr :: ls1 ∧
    irun ls1 q d1 pE dE ∧ ¬ atPure pE) ∨
  LInstr ∉ rest.map Prod.fst ∨
  ((∃ (ls0 ls1 : List Wlabel) (q : Pexv6) (d1 : Efab) (pm : Pexv6) (dm : Efab),
      cycStart p0 d0 em pfx s.psPc ls0 q d1 ∧ cycIn em pfx ls0 ls1 ∧ irun ls1 q d1 pm dm ∧
      atCause true pm) ∧
    ¬ ∃ gx rest', rest = gx ++ rest' ∧ texcRes G i em pfx gx)

/-! ## 6. THE ASSEMBLY -/

theorem PinCycRun.kInvAgree (pc : Int) (rs rs' : RegFile)
    (hag : ∀ r, wireReg r = false → rs' r = rs r) (hrb : RbootAll rs') :
    kInv pc rs → kInv pc rs' := by
  rintro ⟨h1, ⟨c1, c2, c3, c4, c5, c6, c7⟩, -⟩
  refine ⟨?_, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, hrb⟩
  · rw [hag .PC (by decide)]; exact h1
  · rw [hag .cur_privilege (by decide)]; exact c1
  · rw [hag .misa (by decide)]; exact c2
  · rw [hag .menvcfg (by decide)]; exact c3
  · rw [hag .mseccfg (by decide)]; exact c4
  · rw [hag .hart_state (by decide)]; exact c5
  · rw [hag .mstatus (by decide)]; exact c6
  · rw [hag .elp (by decide)]; exact c7

theorem PinCycRun.kCfgAgree (pc : Int) (rs : RegFile) (rv : RegFile)
    (hag : ∀ r, wireReg r = false → rs r = rv r) (hrb : RbootAll rs) (hcfg : kCfg rv)
    (hpc : rv .PC = BitVec.ofInt 64 pc) : kInv pc rs := by
  obtain ⟨c1, c2, c3, c4, c5, c6, c7⟩ := hcfg
  refine ⟨?_, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, hrb⟩
  · rw [hag .PC (by decide)]; exact hpc
  · rw [hag .cur_privilege (by decide)]; exact c1
  · rw [hag .misa (by decide)]; exact c2
  · rw [hag .menvcfg (by decide)]; exact c3
  · rw [hag .mseccfg (by decide)]; exact c4
  · rw [hag .hart_state (by decide)]; exact c5
  · rw [hag .mstatus (by decide)]; exact c6
  · rw [hag .elp (by decide)]; exact c7

/-- A fetch label of the emission has `kA`-admitted bytes (`kFetchText`). -/
theorem PinCycRun.kAOfText (em : Hemission) (hft : kFetchText em)
    (hfeN : ∀ a tvs t, (LIFetch a tvs, t) ∈ em.emItems → t = none) (a : Int)
    (tvs : List (Nat × BitVec 8)) :
    LIFetch a tvs ∈ em.emItems.map Prod.fst →
    ∀ j (hj : j < tvs.length), kA (a + (j : Int)) (tvs[j]'hj).2 := by
  intro hl j hj h1 h2
  obtain ⟨⟨l', t⟩, hit, e⟩ := List.mem_map.1 hl
  simp only at e
  subst e
  have ht := hfeN a tvs t hit
  subst ht
  obtain ⟨n, hn⟩ := List.mem_iff_getElem?.1 hit
  have := hft n a tvs hn j hj h1 h2
  simp only [List.getElem?_map, List.getElem?_eq_getElem hj, Option.map_some,
    Option.some.injEq] at this
  exact this

/-- **THE WALK ALONG THE EMISSION** (header): from a walk boundary at a state the walk reaches,
the emission continues with a cycle alignment `cycRun` to a reached state at which the walk
stops (`cycStop`). -/
theorem cycWalk (G : Gexec) (i : Nat) (em : Hemission) (own : Bool) (p0 : Pexv6) (d0 : Efab)
    (a0 : PState)
    (hfeN : ∀ a tvs t, (LIFetch a tvs, t) ∈ em.emItems → t = none) (hft : kFetchText em)
    (hsome : ∀ s n, preach own a0 s n → pstep own s ≠ none)
    (hsail : ∀ s n l, preach own a0 s n → pstep own s = some l → l ≠ [] → cySailAt s.psPc)
    (hfetch : ∀ s n l, preach own a0 s n → pstep own s = some l → l ≠ [] →
      fetchOkRF p0 d0 em s.psPc)
    (hdata : ∀ s n l, preach own a0 s n → pstep own s = some l → l ≠ [] →
      dataOkRF p0 d0 em s.psPc)
    (hexc : ∀ s n l, preach own a0 s n → pstep own s = some l → l ≠ [] →
      excRetR G i p0 d0 em s.psPc) :
    ∀ (N : Nat) (rest : List Eitem), rest.length ≤ N →
    ∀ (pfx : List Eitem) (s : PState) (n : Nat) (p : Pexv6) (d : Efab) (pE : Pexv6) (dE : Efab),
      preach own a0 s n → walkBd p0 d0 em pfx s.psPc p d → em.emItems = pfx ++ rest →
      pevrun (rest.map Prod.fst) p d pE dE →
      ∃ (mid rest' : List Eitem) (s' : PState) (n' : Nat) (p' : Pexv6) (d' : Efab),
        rest = mid ++ rest' ∧ cycRun G i em own pfx s mid s' ∧ preach own a0 s' n' ∧
        walkBd p0 d0 em (pfx ++ mid) s'.psPc p' d' ∧ pevrun (rest'.map Prod.fst) p' d' pE dE ∧
        cycStop G i p0 d0 em own (pfx ++ mid) s' rest' := by
  intro N
  induction N with
  | zero =>
    intro rest hlen pfx s n p d pE dE hreach hbd hes hrun
    have hr : rest = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hr
    refine ⟨[], [], s, n, p, d, rfl, .stop pfx s, hreach, by rwa [List.append_nil], hrun, ?_⟩
    exact Or.inr (Or.inr (Or.inl List.not_mem_nil))
  | succ N ih =>
    intro rest hlen pfx s n p d pE dE hreach hbd hes hrun
    -- a pin: stop
    by_cases hpin : pstep own s = some []
    · exact ⟨[], rest, s, n, p, d, rfl, .stop pfx s, hreach, by rwa [List.append_nil], hrun,
        by rw [List.append_nil]; exact Or.inl hpin⟩
    obtain ⟨l, hps⟩ : ∃ l, pstep own s = some l := by
      cases h : pstep own s with
      | none => exact absurd h (hsome s n hreach)
      | some l => exact ⟨l, rfl⟩
    have hl : l ≠ [] := by rintro rfl; exact hpin hps
    have hbd0 := hbd
    obtain ⟨-, hrun0, cpu, rs, fn, ib, rfl, hkinv⟩ := hbd
    rcases pureSplit _ _ _ _ _ hrun cpu rs fn ib rfl hkinv.2.2 with hni |
      ⟨ls0, ls1, rs', tick, d1, hls, hni0, h0, hr0, hr1, hag, hrb'⟩
    · exact ⟨[], rest, s, n, _, d, rfl, .stop pfx s, hreach, by rwa [List.append_nil], hrun,
        by rw [List.append_nil]; exact Or.inr (Or.inr (Or.inl hni))⟩
    have hkinv' : kInv s.psPc rs' := PinCycRun.kInvAgree s.psPc rs rs' hag hrb' hkinv
    let st0 : CySt := ⟨rs', [], false, ⟨OpRoles.ORnone, [], 0, true⟩⟩
    have hcy0 := hsail s n l hreach hps hl tick st0 ⟨hkinv', rfl, rfl, rfl⟩
    have hm0 : cyMatch st0 rs' ibNone := ⟨fun _ _ => rfl, hrb', hrb', rfl, rfl, rfl⟩
    have hsub : ∀ l', l' ∈ rest.map Prod.fst → l' ∈ em.emItems.map Prod.fst := by
      intro l' hl'
      rw [hes, List.map_append]; exact List.mem_append_right _ hl'
    have hcs : cycStart p0 d0 em pfx s.psPc ls0 (.PHart cpu (riscvStep tick) rs' none ibNone) d1 :=
      ⟨_, d, hbd0, hr0, cpu, tick, rs', rfl⟩
    have hA : ∀ ls1' l' ls2 pm dm, ls1 = ls1' ++ l' :: ls2 →
        irun (ls1' ++ [l']) (.PHart cpu (riscvStep tick) rs' none ibNone) d1 pm dm →
        feAdm kA (kAa s.psPc) (st0.fe.length + (feLabs ls1').length) l' := by
      intro ls1' l' ls2 pm dm e hir a tvs hl'
      subst hl'
      refine ⟨?_, PinCycRun.kAOfText em hft hfeN a tvs (hsub _ ?_)⟩
      · show a = s.psPc + 2 * ((0 + (feLabs ls1').length : Nat) : Int)
        rw [Nat.zero_add]
        exact (hfetch s n l hreach hps hl).1 pfx ls0 _ d1 ls1' pm dm a tvs hni0 hcs
          ⟨rest, hes, ⟨ls2, by rw [hls, e]; simp⟩⟩ hir
      · rw [hls, e]; simp
    rcases cyRun kA (kAa s.psPc) cyS (cyT s.psPc) (cyPost s.psPc) ls1 _ d1 pE dE hr1 cpu
        (riscvStep tick) rs' none ibNone st0 rfl hcy0 hm0 hA with
      ⟨la, lb, m1, rs1, fn1, ib1, dm, st1, rfl, hira, hrb, ⟨r, v, k, rfl, hsr, hT⟩, hm1, htr⟩ |
      ⟨la, lb, rs1, fn1, ib1, dm, st1, rfl, hira, hrb, hpost, hm1, htr⟩ |
      ⟨m1, rs1, fn1, ib1, st1, rfl, hnp, hir, -, -, -⟩
    · -- a STOP: a trap
      have hcin : cycIn em pfx ls0 la :=
        ⟨rest, hes, ⟨lb, by rw [hls]; simp⟩⟩
      cases hcb : causeBit r v with
      | false =>
        exfalso
        have hac : atCause false (.PHart cpu (.impure (.ok (.regWrite r v)) k) rs1 fn1 ib1) :=
          ⟨cpu, r, v, k, rs1, fn1, ib1, rfl, hsr, hcb⟩
        obtain ⟨_, _, _, _, _, e, hib⟩ := (hfetch s n l hreach hps hl).2 pfx ls0 _ d1 la _ dm hni0 hcs hcin hira hac
        cases e
        have han : st1.an = true := by rw [hm1.2.2.2.2.2]; exact hib
        have hmem := (hT han).2
        exact hdata s n l hreach hps hl hmem pfx ls0 _ d1 la _ dm hni0 hcs hcin hira hac
      | true =>
        have hac : atCause true (.PHart cpu (.impure (.ok (.regWrite r v)) k) rs1 fn1 ib1) :=
          ⟨cpu, r, v, k, rs1, fn1, ib1, rfl, hsr, hcb⟩
        by_cases hx : ∃ gx rest', rest = gx ++ rest' ∧ texcRes G i em pfx gx
        · obtain ⟨gx, rest', hrs, htx, hne, hret⟩ :=
            hexc s n l hreach hps hl pfx ls0 _ d1 la _ dm rest hcs hcin hira hac hes hx
          rw [hrs, List.map_append] at hrun
          obtain ⟨p'', d'', hg, hr'⟩ := pevrunSplit _ _ _ _ _ _ hrun
          obtain ⟨cpu'', rs'', fn'', ib'', rfl, hk''⟩ := hret _ d p'' d'' hbd0 hg
          have hbd'' : walkBd p0 d0 em (pfx ++ gx) s.psPc
              (.PHart cpu'' (.pure ()) rs'' fn'' ib'') d'' :=
            ⟨⟨rest', by rw [hes, hrs, List.append_assoc]⟩,
              by rw [List.map_append]; exact pevrunApp hrun0 hg, cpu'', rs'', fn'', ib'', rfl, hk''⟩
          have hlen' : rest'.length ≤ N := by
            have : gx.length ≠ 0 := by intro h; exact hne (List.eq_nil_of_length_eq_zero h)
            rw [hrs, List.length_append] at hlen; omega
          obtain ⟨mid, rest2, s2, n2, p2, d2, hmid, hcr, hreach2, hbd2, hrun2, hstop2⟩ :=
            ih rest' hlen' (pfx ++ gx) s n _ d'' pE dE hreach hbd''
              (by rw [hes, hrs, List.append_assoc]) hr'
          refine ⟨gx ++ mid, rest2, s2, n2, p2, d2, by rw [hrs, hmid, List.append_assoc],
            .trap pfx s gx mid s2 htx hcr, hreach2, by rwa [← List.append_assoc], hrun2,
            by rwa [← List.append_assoc]⟩
        · exact ⟨[], rest, s, n, _, d, rfl, .stop pfx s, hreach, by rwa [List.append_nil], hrun,
            by rw [List.append_nil]; exact Or.inr (Or.inr (Or.inr
              ⟨⟨ls0, la, _, d1, _, dm, hcs, hcin, hira, hac⟩, hx⟩))⟩
    · -- the END of the cycle: a retired walk instruction
      have hcin : cycIn em pfx ls0 la :=
        ⟨rest, hes, ⟨lb, by rw [hls]; simp⟩⟩
      obtain ⟨⟨fe', hfe1, hfe2⟩, hscan, -⟩ := htr
      have hfe : st1.fe = fe' := by rw [hfe1]; rfl
      obtain ⟨fa, hfa, -, hok, hn, hro, ⟨pc', hpc', hPC⟩, hcfg⟩ := hpost
      rw [hfe] at hfa
      obtain ⟨s', hs'l, hs'pc⟩ := pstepSucc own s l hps hl pc' hpc'
      have hreach' : preach own a0 s' (n + 1) :=
        WeakRvwmoPinBridge5.preachSnoc own a0 s s' l n hreach hps hs'l
      -- the cycle's items
      have hls' : rest.map Prod.fst = (ls0 ++ LInstr :: la) ++ lb := by rw [hls]; simp
      obtain ⟨g, restB, hrsplit, hgl, hrl⟩ := List.map_eq_append_iff.1 hls'
      have hgsub : ∀ it, it ∈ g → it ∈ em.emItems := by
        intro it hit; rw [hes, hrsplit]
        exact List.mem_append_right _ (List.mem_append_left _ hit)
      have hitems : fa.items g s.psPc := by
        refine armItems s.psPc fe' fa la g hfa hfe2 (fun l' hl' hfl => ?_)
        have hlg : l' ∈ g.map Prod.fst := by
          rw [hgl]; exact List.mem_append_right _ (List.mem_cons_of_mem _ hl')
        obtain ⟨⟨l'', t⟩, hit, e⟩ := List.mem_map.1 hlg
        simp only at e
        subst e
        cases l'' with
        | LIFetch a tvs =>
          have := hfeN a tvs t (hgsub _ hit)
          subst this; exact hit
        | _ => cases hfl
      have hscan' : dfScan fa.annRole (0, true) (g.map Prod.fst) =
          ((dfDests fa.annRole).length, true) := by
        rw [hgl, show ls0 ++ LInstr :: la = (ls0 ++ [LInstr]) ++ la by simp, dfScanApp,
          PinCycRun.dfScanNeutral fa.annRole (0, true) (ls0 ++ [LInstr]) (fun l' hl' => by
            rcases List.mem_append.1 hl' with hl' | hl'
            · exact (h0 l' hl').1
            · rw [List.mem_singleton] at hl'; subst hl'; intro _ _ e; cases e)]
        rw [← hro]
        have e2 := hscan
        simp only [st0] at e2
        rw [← e2, hn, hok]
      let c : CycCert g := ⟨s.psPc, fa, fa.annRole, hitems, hscan'⟩
      have hbd' : walkBd p0 d0 em (pfx ++ g) s'.psPc (.PHart cpu (.pure ()) rs1 fn1 ib1) dm :=
        ⟨⟨restB, by rw [hes, hrsplit, List.append_assoc]⟩,
          by rw [List.map_append, hgl, show ls0 ++ LInstr :: la = (ls0 ++ [LInstr]) ++ la by simp]
             exact pevrunApp hrun0 (pevrunApp hr0 (irunPevrun _ _ _ _ _ hira)),
          cpu, rs1, fn1, ib1, rfl,
          PinCycRun.kCfgAgree s'.psPc rs1 st1.rv hm1.1 hm1.2.1 hcfg (by rw [hs'pc]; exact hPC)⟩
      have hlenB : restB.length ≤ N := by
        have h1 : g.length ≠ 0 := by
          intro h; rw [List.eq_nil_of_length_eq_zero h] at hgl; simp at hgl
        rw [hrsplit, List.length_append] at hlen; omega
      have hrunB : pevrun (restB.map Prod.fst) (.PHart cpu (.pure ()) rs1 fn1 ib1) dm pE dE := by
        rw [hrl]; exact hrb
      obtain ⟨mid, rest2, s2, n2, p2, d2, hmid, hcr, hreach2, hbd2, hrun2, hstop2⟩ :=
        ih restB hlenB (pfx ++ g) s' (n + 1) _ dm pE dE hreach' hbd'
          (by rw [hes, hrsplit, List.append_assoc]) hrunB
      refine ⟨g ++ mid, rest2, s2, n2, p2, d2, by rw [hrsplit, hmid, List.append_assoc],
        .step pfx s g l s' mid s2 c rfl rfl hps hs'l hcr, hreach2,
        by rwa [← List.append_assoc], hrun2, by rwa [← List.append_assoc]⟩
    · -- the emission ends INSIDE the cycle
      refine ⟨[], rest, s, n, _, d, rfl, .stop pfx s, hreach, by rwa [List.append_nil], hrun, ?_⟩
      rw [List.append_nil]
      refine Or.inr (Or.inl ⟨ls0, ls1, _, d1, _, dE, hcs, hls, hir, ?_⟩)
      rintro ⟨_, _, _, _, e⟩
      cases e
      exact hnp () rfl

/-- At a reached state of a claimed site's walk, the walk step is defined (the table's `stOk`). -/
theorem PinCycRun.pstepSomeOfReach (pcL : Int) (w : Pin) (own : Bool) (hm : (pcL, w) ∈ pinsW9a)
    (hw : walkOwn w = some own) :
    ∀ s n, preach own (pinStart pcL) s n → pstep own s ≠ none := by
  intro s n hs h
  have := walkReach pcL w own hm hw s n hs
  unfold PinWalkTab.stOk at this
  rw [h] at this
  simp at this

/-- **`cycRun` FROM `hartConf` (header)**: at a walk-certifying row `(pcL, w)` of `pinsW9a`, for
hart `i`'s conformant emission `em` whose fetched text bytes are the image's (`kFetchText`, r3 +
B4), if every state the hart's run can be in after the prefix `base` is a cycle boundary in the
kernel configuration at the walk start (`pinStart pcL`'s pc — the load's cycle retired), then the
emission after `base` continues with a cycle alignment `cycRun … base (pinStart pcL) mid s` to a
state `s` the walk reaches, at which the walk STOPS (`cycStop`: a pin; the emission ends inside
`s`'s cycle; an interrupt with no fence-free aligned excursion).  Premises: the Sail cycle fact
`cySailAt` at every reached non-pin state ((2)–(3), named) and the run obligations `fetchOkR2`
(r2-shaped), `dataOkR`, `excRetR` ((4), named). -/
theorem cycRunOfHartConf (G : Gexec) (i : Nat) (row : List Lbl) (p0 : Pexv6) (dv : Nat → Efab)
    (em : Hemission) (pcL : Int) (w : Pin) (own : Bool)
    (hcf : hartConf i row p0 dv em) (hm : (pcL, w) ∈ pinsW9a) (hw : walkOwn w = some own)
    (hft : kFetchText em)
    (hsail : ∀ s n l, preach own (pinStart pcL) s n → pstep own s = some l → l ≠ [] →
      cySailAt s.psPc)
    (hfetch : ∀ s n l, preach own (pinStart pcL) s n → pstep own s = some l → l ≠ [] →
      fetchOkRF p0 (dv 0) em s.psPc)
    (hdata : ∀ s n l, preach own (pinStart pcL) s n → pstep own s = some l → l ≠ [] →
      dataOkRF p0 (dv 0) em s.psPc)
    (hexc : ∀ s n l, preach own (pinStart pcL) s n → pstep own s = some l → l ≠ [] →
      excRetR G i p0 (dv 0) em s.psPc)
    (base rest : List Eitem) (hes : em.emItems = base ++ rest)
    (hstart : ∀ p d, pevrun (base.map Prod.fst) p0 (dv 0) p d →
      ∃ (cpu : CPU) (rs : RegFile) (fn : Option (Bool × Bool × Bool × Bool)) (ib : Ibch),
        p = .PHart cpu (.pure ()) rs fn ib ∧ kInv (pinStart pcL).psPc rs) :
    ∃ (mid rest' : List Eitem) (s : PState) (n : Nat) (p' : Pexv6) (d' : Efab),
      rest = mid ++ rest' ∧ cycRun G i em own base (pinStart pcL) mid s ∧
      preach own (pinStart pcL) s n ∧ walkBd p0 (dv 0) em (base ++ mid) s.psPc p' d' ∧
      cycStop G i p0 (dv 0) em own (base ++ mid) s rest' := by
  have hrun := hartConfPevrun i row p0 dv em hcf
  rw [hes, List.map_append] at hrun
  obtain ⟨p1, d1, h1, h2⟩ := pevrunSplit _ _ _ _ _ _ hrun
  obtain ⟨cpu, rs, fn, ib, rfl, hk⟩ := hstart _ _ h1
  have hfeN : ∀ a tvs t, (LIFetch a tvs, t) ∈ em.emItems → t = none :=
    hemitFeNone dv 0 wsInit row p0 em.emItems em.emFin hcf
  obtain ⟨mid, rest', s, n, p', d', h3, h4, h5, h6, -, h8⟩ :=
    cycWalk G i em own p0 (dv 0) (pinStart pcL) hfeN hft
      (PinCycRun.pstepSomeOfReach pcL w own hm hw) hsail hfetch hdata hexc rest.length rest
      (Nat.le_refl _) base (pinStart pcL) 0 _ d1 _ _ (.prRefl _)
      ⟨⟨rest, hes⟩, h1, cpu, rs, fn, ib, rfl, hk⟩ hes h2
  exact ⟨mid, rest', s, n, p', d', h3, h4, h5, h6, h8⟩

end PinCycRun
end Weak
