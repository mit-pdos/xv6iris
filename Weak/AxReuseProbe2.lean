/-
Weak: FEASIBILITY PROBE (part 2 of 2) -- instantiating the SC leaf interface of
`AxReuseProbe.AbsCpuid` over `WPd`.

Rocq: `iris/AxReuseProbe2.v` @ xxvzwolszwmp.

## The Rocq header, in substance

§1 THE WPd SURFACE.  A thread's registers live INSIDE the `WPd` thread expression
(`AThread (PHart cpu m rs fn ib) k`), not in a state interpretation, so the SC goal `WP Loop`
cannot be a fixed `WPd s`.  It becomes a goal QUANTIFIED over the current thread:
`goalD := ∀ s m pc, ⌜cur m pc s⌝ -∗ ghost_var γm ½ m -∗ ghost_var γp ½ pc -∗ WPd s {{ True }}`,
with the SC register bundle / pc assertion as the OTHER halves of two ghost variables mirroring
the thread's GPR map and PC (`sieCapD`, `pcIsD`) and `cur` the pure tie (Ret-state at `rs`,
`gprRel m rs`, `PC rs = pc`, abstract control predicate `ctrlOk rs`).
§2 THE LIFTING THEOREM X for register-writing instructions (`XGprWrite`, a definition: the WPd
twin of the SC engine `wp_gpr_write_s_sconf` / `wp_instr_s_sconf`, with the SAME pure
`exec (execute ins)` certificate premise).
§3 `wpCmvD`: the real leaf statement `wp_cmv_s_sconf`, unchanged except `WP Loop` := `goalD`,
`sie_cap_gpr` := `sieCapD`, `pc_is` := `pcIsD`, `instr` := `instrD`, proved over WPd FROM X;
the certificate is discharged by the SC leaf's own script.  Also `wpCaddiwD` (same family).
§4 WHY X IS NOT PROVABLE WITH TODAY'S ENGINE (a comment in Rocq; summarised at the end of this
file).  NOT VACUOUS?  `XGprWrite` is a premise (not proved here): above X nothing else is needed.

## Deviations from Rocq

1. TYPES / SPELLING (the `Weak/ExecSC*.lean` conventions): `regstate` ↦ `RegFile`, `mstate` ↦
   `ExecSt`, `mword n` ↦ `BitVec n`, `uint x ≠ 0` ↦ `x.toNat ≠ 0`; the GPR read
   `if uint r =? 0 then zero_reg else register_lookup (R_bitvector_64 (gpr_of_Z (uint r))) rs`
   ↦ `uxaXget rs r` (`s.gpr r` on a state); `register_lookup PC rs` ↦ `rs .PC`;
   `set_reg s (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg v)` ↦ `s.setGpr rd v`
   (the `uint rd ≠ 0` premise is there); `add_vec_int pc (if is_rvc then 2 else 4)` ↦
   `pc + instrLen is_rvc` (`pc + 2#64` at `is_rvc = true`); `Z.eqb (uint r) (uint rd)` ↦
   `r = rd` (decidable; equivalent by `uint5Inj`).
2. THE SC REGISTER MAP is the Lean SC tree's: `regfile` ↦ `RegMap`, `rget m r` (tp pinned to the
   implicit `CpuId`) ↦ `rget cid m r` with an explicit hart `cid : CPU` (Rocq's `CID`, kept
   distinct from the weak hart `cpu` as in Rocq), `<[Regidx rd := v]> m` ↦ `m.set rd v`,
   `Regidx rd ≠ Regidx Rtp` ↦ `rd ≠ 4#5`, `rd_ok` ↦ `MachCSL.rdOk` (`Weak.rdOk` is WeakAxiomatic's).  Lean's `rget` reads `x0` as zero
   (Rocq's does not special-case it), so `rgetUpd` takes the extra premise `rd.toNat ≠ 0`
   (every caller has it: `gprRelUpd` takes it in Rocq too).
3. `wp_next` (Rocq: logic-generic) ↦ `MachCSL.wpNext`; its continuation is indexed by the
   resuming hart `cpu' : CPU` (Rocq `fun (CID : CpuId) => …`), so `sieCapD` takes the hart
   first (Rocq's implicit `CID0`).
4. `invGS_gen HasNoLc Σ` ↦ `[InvGS_gen hlc GF]` for any `hlc` (as `AxWpD`, deviation 2);
   `ghost_varG Σ regfile` / `ghost_varG Σ (mword 64)` ↦ `[GhostVarG GF RegMap]` /
   `[GhostVarG GF (BitVec 64)]`; `ghost_var γ (1/2) a` ↦ `ghost_var γ (.own (1 : Qp).half) a`.
   `GenId` is unused and dropped.  `WPd s @ MaybeStuck; i {{ Φ }}` ↦ `wpd .MaybeStuck i s Φ`.
5. STATEMENT SHAPES: Rocq wand chains `A -∗ B -∗ … -∗ C` (Coq Props) ↦ `⊢ A -∗ B -∗ … -∗ C`;
   the `let wval := …` of the two leaves is inlined.
6. Lean-only helper (file-qualified): `AxReuseProbe2.uxaXgetZero`.

**Rocq → Lean name map.**  `gpr_rel` `gprRel`, `gpr_agree` `gprAgree`, `uint5_inj` `uint5Inj`,
`rget_upd` `rgetUpd`, `gpr_rel_upd` `gprRelUpd`, `Φ0` `Φ0`, `cur` `cur`, `Goal_d` `goalD`,
`sie_cap_d` `sieCapD`, `pc_is_d` `pcIsD`, `instr_d` `instrD`, `X_gpr_write` `XGprWrite`,
`wp_gpr_write_d` `wpGprWriteD`, `wp_cmv_d` `wpCmvD`, `wp_caddiw_d` `wpCaddiwD`.  Section
contexts keep their roles: `ctrl_ok` `ctrlOk`, `text_ok` `textOk`.  None is in the
duplicated-name table.

**Dropped:** nothing (Rocq 15 definitions/lemmas, Lean 15 + 1 helper).  **Not ported:** the
`Print Assumptions` line (the lint's axiom check covers it).
-/
import Weak.AxEpiLedgerTick
import Weak.ExecSC
import MachCSL.KCtx

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std MachCSL
open Sail
open LeanRV64D LeanRV64D.Functions

/-! # 0. Pure register-map bridge -/

/-- The SC register map `m` (tp pinned via `rget`) and a thread's register file. -/
def gprRel (cid : CPU) (m : RegMap) (rs : RegFile) : Prop :=
  ∀ r : BitVec 5, uxaXget rs r = rget cid m r

def gprAgree (a b : RegFile) : Prop :=
  ∀ r : BitVec 5, r.toNat ≠ 0 → uxaXget a r = uxaXget b r

theorem uint5Inj (r1 r2 : BitVec 5) : r1.toNat = r2.toNat → r1 = r2 :=
  BitVec.eq_of_toNat_eq

theorem AxReuseProbe2.uxaXgetZero (f : RegFile) (r : BitVec 5) (h : r.toNat = 0) :
    uxaXget f r = 0#64 := by
  have : r = 0#5 := BitVec.eq_of_toNat_eq (by simpa using h)
  subst this
  rfl

theorem rgetUpd (cid : CPU) (m : RegMap) (rd r : BitVec 5) (v : BitVec 64)
    (hrd : rd ≠ 4#5) (hrd0 : rd.toNat ≠ 0) :
    rget cid (m.set rd v) r = if r = rd then v else rget cid m r := by
  have hrd0' : rd ≠ 0#5 := fun h => hrd0 (by subst h; rfl)
  by_cases h : r = rd
  · subst h
    simp only [if_true]
    rw [rget_ne _ _ _ hrd0' hrd, RegMap.set_same]
  · simp [rget, RegMap.get, tpPin, RegMap.set, h]

/-- THE UPDATE: X's post GPR fact re-establishes `gprRel` at the SC leaf's updated map. -/
theorem gprRelUpd (cid : CPU) (m : RegMap) (rs rs' : RegFile) (rd : BitVec 5) (v : BitVec 64) :
    gprRel cid m rs → rd.toNat ≠ 0 → rd ≠ 4#5 →
    (∀ r : BitVec 5, r.toNat ≠ 0 →
      uxaXget rs' r = if r = rd then v else uxaXget rs r) →
    gprRel cid (m.set rd v) rs' := by
  intro Hrel Hrd0 Hrdtp Hpost r
  rw [rgetUpd cid m rd r v Hrdtp Hrd0]
  by_cases h0 : r.toNat = 0
  · have hne : r ≠ rd := fun e => Hrd0 (e ▸ h0)
    simp only [hne, if_false]
    rw [AxReuseProbe2.uxaXgetZero rs' r h0, ← Hrel r, AxReuseProbe2.uxaXgetZero rs r h0]
  · rw [Hpost r h0]
    by_cases e : r = rd
    · simp only [e, if_true]
    · simp only [e, if_false]
      exact Hrel r

/-! # 1-2. The WPd surface and the lifting theorem X -/

section wpdSurface
variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF] [Axpol]
variable [GhostVarG GF RegMap] [GhostVarG GF (BitVec 64)]
variable (i : Agent) (cid cpu : CPU) (γm γp : GName)
/- the control part of the S-mode configuration (`sconf` minus GPRs): kept ABSTRACT; X must
preserve it. -/
variable (ctrlOk : RegFile → Prop)
/- "the graph's text has `ins` at `pc`" -- the WPd reading of `instr pc is_rvc ins`; kept
ABSTRACT; X consumes it. -/
variable (textOk : BitVec 64 → Bool → instruction → Prop)

def Φ0 : Athread → IProp GF := fun _ => iprop(True)

def cur (m : RegMap) (pc : BitVec 64) (s : Athread) : Prop :=
  ∃ rs k, RetX cpu rs k s ∧ ctrlOk rs ∧ gprRel cid m rs ∧ rs .PC = pc

/-- `WP (Loop : expr riscv_lang)` ↦ `goalD`. -/
def goalD : IProp GF :=
  iprop(∀ s m pc, ⌜cur cid cpu ctrlOk m pc s⌝ -∗ ghost_var γm (.own (1 : Qp).half) m -∗
    ghost_var γp (.own (1 : Qp).half) pc -∗ wpd .MaybeStuck i s Φ0)

/-- `sie_cap_gpr m n b p` ↦ `sieCapD`: interrupts off, the GPR half.  (`n` = stack capacity and
`p` = cpus[].proc are memory/invariant content -- dropped here.) -/
def sieCapD (_cid0 : CPU) (m : RegMap) (_n : Nat) (b : Bool) (_p : BitVec 64) : IProp GF :=
  iprop(⌜b = false⌝ ∗ ghost_var γm (.own (1 : Qp).half) m)

def pcIsD (pc : BitVec 64) : IProp GF := ghost_var γp (.own (1 : Qp).half) pc

def instrD (pc : BitVec 64) (is_rvc : Bool) (ins : instruction) : IProp GF :=
  iprop(⌜textOk pc is_rvc ins⌝)

/-- THE LIFTING THEOREM X (register-writing, memory-free instruction).  Premises = exactly the
SC engine's: the pure `exec (execute ins)` certificate from any state agreeing with the thread on
GPRs and with nextPC set; plus the WPd-side facts (the thread is at a Ret boundary at `rs`,
control ok, text).  Conclusion: WPd from `s` given a continuation at EVERY next Ret boundary whose
registers are the certificate's successor (GPRs), PC advanced, control still ok -- for EVERY
tick and row position. -/
def XGprWrite : Prop :=
  ∀ (s : Athread) (rs : RegFile) (k : Nat) (pc : BitVec 64) (is_rvc : Bool)
    (ins : instruction) (rd : BitVec 5) (wval : BitVec 64),
    RetX cpu rs k s → ctrlOk rs → rs .PC = pc →
    textOk pc is_rvc ins → rd.toNat ≠ 0 →
    (∀ s_pc : ExecSt,
       s_pc.regs .nextPC = pc + instrLen is_rvc →
       gprAgree s_pc.regs rs →
       exec (execute ins) s_pc = some (RETIRE_SUCCESS, s_pc.setGpr rd wval)) →
    ⊢ (∀ s' rs' k',
         ⌜RetX cpu rs' k' s'⌝ -∗ ⌜ctrlOk rs'⌝ -∗
         ⌜rs' .PC = pc + instrLen is_rvc⌝ -∗
         ⌜∀ r : BitVec 5, r.toNat ≠ 0 →
            uxaXget rs' r = if r = rd then wval else uxaXget rs r⌝ -∗
         wpd .MaybeStuck i s' (Φ0 (GF := GF))) -∗
       wpd .MaybeStuck i s (Φ0 (GF := GF))

/-- The generic register-write leaf over X: the WPd twin of `wp_gpr_write_s_sconf`, SAME
statement shape (rsa/rsb source-value certificate), `b = false`. -/
theorem wpGprWriteD (HX : XGprWrite (GF := GF) i cpu ctrlOk textOk)
    (pc : BitVec 64) (rd rsa rsb : BitVec 5) (base : instruction) (wval : BitVec 64)
    (m : RegMap) (n : Nat) (b : Bool) (p : BitVec 64) :
    rd.toNat ≠ 0 →
    MachCSL.rdOk rd →
    (∀ s_pc : ExecSt,
       s_pc.regs .nextPC = pc + 2#64 →
       s_pc.gpr rsa = rget cid m rsa →
       s_pc.gpr rsb = rget cid m rsb →
       exec (execute base) s_pc = some (RETIRE_SUCCESS, s_pc.setGpr rd wval)) →
    ⊢ sieCapD (GF := GF) γm cid m n b p -∗
      pcIsD (GF := GF) γp pc -∗
      instrD (GF := GF) textOk pc true base -∗
      wpNext b p cid (fun cpu' => iprop(
        sieCapD γm cpu' (m.set rd wval) n b p -∗
        pcIsD γp (pc + 2#64) -∗
        goalD i cid cpu γm γp ctrlOk)) -∗
      goalD i cid cpu γm γp ctrlOk := by
  intro Hrd Hrdok Hbexec
  unfold sieCapD pcIsD instrD
  iintro ⟨%Hb, Hm⟩ Hp %Htext Hcont
  subst Hb
  ihave Hcont := wpNext_off p cid _ $$ Hcont
  unfold goalD
  iintro %s %m' %pc' %Hcur Hm' Hp'
  ihave %h1 := ghost_var_agree _ _ _ _ _ $$ Hm Hm'
  ihave %h2 := ghost_var_agree _ _ _ _ _ $$ Hp Hp'
  subst h1 h2
  obtain ⟨rs, k, HRet, Hctrl, Hrel, HPC⟩ := Hcur
  -- source values: the SC hypotheses, from `gprRel`
  have Hsrc : ∀ (s_pc : ExecSt) (r : BitVec 5), gprAgree s_pc.regs rs →
      s_pc.gpr r = rget cid m r := by
    intro s_pc r Hag
    rw [← Hrel r]
    show uxaXget s_pc.regs r = uxaXget rs r
    by_cases h0 : r.toNat = 0
    · rw [AxReuseProbe2.uxaXgetZero _ r h0, AxReuseProbe2.uxaXgetZero _ r h0]
    · exact Hag r h0
  have HXi := HX s rs k pc true base rd wval HRet Hctrl HPC Htext Hrd
    (fun s_pc Hnpc Hag => Hbexec s_pc Hnpc (Hsrc s_pc rsa Hag) (Hsrc s_pc rsb Hag))
  iapply HXi
  iintro %s' %rs' %k' %HRet' %Hctrl' %HPC' %Hgpr
  iapply bupdWpd
  imod ghost_var_update_halves (m.set rd wval) γm m m $$ Hm Hm' with ⟨Hm, Hm'⟩
  imod ghost_var_update_halves (pc + 2#64) γp pc pc $$ Hp Hp' with ⟨Hp, Hp'⟩
  imodintro
  have Hcur' : cur cid cpu ctrlOk (m.set rd wval) (pc + 2#64) s' :=
    ⟨rs', k', HRet', Hctrl', gprRelUpd cid m rs rs' rd wval Hrel Hrd Hrdok.2.2 Hgpr, HPC'⟩
  iapply Hcont $$ [Hm] Hp %s' %(m.set rd wval) %(pc + 2#64) %Hcur' Hm' Hp'
  isplitr
  · ipureintro; rfl
  · iexact Hm

/-! # 3. The REAL leaf statements, over WPd, from X -/

theorem wpCmvD (HX : XGprWrite (GF := GF) i cpu ctrlOk textOk)
    (pc : BitVec 64) (rd rs2 : BitVec 5)
    (m : RegMap) (n : Nat) (b : Bool) (p : BitVec 64) :
    rd.toNat ≠ 0 →
    MachCSL.rdOk rd →
    ⊢ sieCapD (GF := GF) γm cid m n b p -∗
      pcIsD (GF := GF) γp pc -∗ instrD (GF := GF) textOk pc true (.RTYPE (.Regidx rs2, zreg, .Regidx rd, .ADD)) -∗
      wpNext b p cid (fun cpu' => iprop(
        sieCapD γm cpu' (m.set rd (0#64 + rget cid m rs2)) n b p -∗
        pcIsD γp (pc + 2#64) -∗
        goalD i cid cpu γm γp ctrlOk)) -∗
      goalD i cid cpu γm γp ctrlOk := by
  intro Hrd Hrdok
  refine wpGprWriteD i cid cpu γm γp ctrlOk textOk HX pc rd rs2 rs2
    (.RTYPE (.Regidx rs2, zreg, .Regidx rd, .ADD)) (0#64 + rget cid m rs2) m n b p Hrd Hrdok ?_
  intro s_pc _ Hva _
  show exec (execute_RTYPE (.Regidx rs2) (.Regidx 0#5) (.Regidx rd) .ADD) s_pc = _
  rw [execExecuteRTYPEADDGpr rs2 0#5 rd s_pc]
  unfold gprRdVal
  rw [Hva]
  rfl

theorem wpCaddiwD (HX : XGprWrite (GF := GF) i cpu ctrlOk textOk)
    (pc : BitVec 64) (rd : BitVec 5) (imm : BitVec 6)
    (m : RegMap) (n : Nat) (b : Bool) (p : BitVec 64) :
    rd.toNat ≠ 0 →
    MachCSL.rdOk rd →
    ⊢ sieCapD (GF := GF) γm cid m n b p -∗
      pcIsD (GF := GF) γp pc -∗
      instrD (GF := GF) textOk pc true (.ADDIW (sign_extend (m := 12) imm, .Regidx rd, .Regidx rd)) -∗
      wpNext b p cid (fun cpu' => iprop(
        sieCapD γm cpu' (m.set rd (sign_extend (m := 64) (Sail.BitVec.extractLsb
          (rget cid m rd + sign_extend (m := 64) (sign_extend (m := 12) imm)) 31 0))) n b p -∗
        pcIsD γp (pc + 2#64) -∗
        goalD i cid cpu γm γp ctrlOk)) -∗
      goalD i cid cpu γm γp ctrlOk := by
  intro Hrd Hrdok
  refine wpGprWriteD i cid cpu γm γp ctrlOk textOk HX pc rd rd rd
    (.ADDIW (sign_extend (m := 12) imm, .Regidx rd, .Regidx rd)) _ m n b p Hrd Hrdok ?_
  intro s_pc _ Hva _
  rw [execExecuteADDIWGpr rd rd (sign_extend (m := 12) imm) s_pc]
  unfold gprAddiwVal
  rw [Hva]

end wpdSurface

/- # 4. Where the rest of cpuid breaks (Rocq analysis; nothing proved)

(a) X itself quantifies over a SYMBOLIC pc, SYMBOLIC control state and both ticks; today's WPd
engines (AxLdgSeal & co.) are kernel-checked ledgers at a CONCRETE pc / control base, and
mtime/mip must stay concrete (tick_clock compares mtime with mtimecmp).  X needs a SYMBOLIC WPd
instruction engine (fetch + Sv39 walk + decode + tick + retire, driven by the SC tier's pure
`exec` lemmas), plus a kernel page-table image fact for the walk's demonic PTE reads.
(b) Memory leaves: c.sdsp is expressible (AxEpiLedgerSd's store step); c.ldsp is NOT in this
physical-register surface (WPd reads are ∀ v, the owned fact only an annotation) -- needs
AxSymReg's conditional surface plus a ctrl gate (AxEpiRet's epilogue).
(c) `n`/`p` and the Iris invariants the SC bundle opens: WPd steps have only `|==>`, no fancy
updates. -/

end Weak
