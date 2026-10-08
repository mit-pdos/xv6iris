/-
Weak: **spinlock plan, Phase 3: the CONTROL LEAVES on SURFACE v4** (`AxRelease`: `cur4` /
`goal4` / `cap4` / `pcIs4`), interrupts OFF (regime `ctrlOkSW`, spine `SpineOkTSW` /
`SpineFetch4TSW`, engine `AxSymCtl2.XJal` / `XBtype` / `XCjr`) (AxSL tier).

Rocq: `iris/AxSpinCtl2.v` @ xxvzwolszwmp.

## The Rocq header, in substance

THE CONTROL WORDS OF THE SPINLOCK CODE: `jal ra` (4-byte), `c.j` (push_off+0x38), `c.beqz`
(release+0x10, push_off+0x16, pop_off+0x22), `c.bnez` (holding+0x02, acquire+0x18/+0x22,
pop_off+0x12/+0x1e), `bge` (4-byte `blez`, pop_off+0x16), `c.ret` (acquire, release, push_off,
pop_off, holding ×2, mycpu).  The leaves are generic over the width (`is_rvc`) and the branch
op, so they cover all of them.

THE TEXT FACT FOR CONTROL WORDS.  `instr4`'s compressed arm requires `rf0 (execute ins)`, false
for a branch; the control arm uses the engine's own text fact `textOkCtl` (fail-tolerant
`rfF`) plus `ctlOk5`:
  jal / c.j : target aligned, not `Armed`, the exact map at the target ⊆ (exact here minus rd)
              ∪ {rd};
  branch    : target aligned, neither successor `Armed`, the exact map at both successors ⊆
              the exact map here, operands ≠ tp;
  jalr      : nothing (its leaf takes the facts as hypotheses).
`instr5` = `instr4` on non-control words, the control arm + `deadOk` on control words
(`deadOk`: a branch's TAKEN target is in `Dead` — a panic arm — unless both operands are
exact).

THE LEAVES (no `Cond_gate` premise, no LCtrl gate arm; the engine runs the PHYSICAL
instruction, the continuation is chosen by the physical outcome):
- `wpJalC5` (jal rd ≠ 0, any width) / `wpJC5` (c.j / jal x0): static target; the link
  `pc + incr` is a constant ⇒ EXACT.
- `wpBrC5` (ANY branch, BOTH arms): the continuation is taken at the physical direction `dir`;
  it gets ⌜operands exact → logical direction = dir⌝, and the condition is STRENGTHENED to
  `C ∧ (logical direction = dir)` (`CondMono`) — D4's mechanism.
- `wpBrFallC5` (the SC slot shape, the LOGICAL direction is "fall"): a physically-taken branch
  has a REFUTED condition and lands at a `Dead` target; the obligation goes to the premise
  `Hdead : ∀ p, Dead p → ⊢ refGoal4 p` (`refGoal4 p` = `goal4` at pc p restricted to REFUTED
  conditions; it gives the continuation nothing).
- `wpCretC5` (c.ret / c.jr rs1, EXACT form): rs1 exact at pc, the exact map at the logical
  target `retPc (rget m rs1)` ⊆ the one here, that target not `Armed`.  (Rocq header: on
  surface v4 `ra` is exact only before a reload; after a reload a c.ret needs a phase-1 graph
  fact or the address/ctrl gate.)

KERNEL CROSS-CHECK (Xv6/KernelImage.lean): this file states no kernel word (all leaves are
generic in pc / registers / immediates / width / op).  The header's sites agree with the Lean
image: holding 0x80000bf2 (+0x02 `c.bnez` 0xe399, `c.ret` at +0x06 and +0x2a), push_off
0x80000c1e (+0x16 `c.beqz` 0xcb99, +0x38 `c.j` 0xb7c5, `c.ret` +0x2a), acquire 0x80000c58
(+0x18 `c.bnez` 0xed11, +0x22 `c.bnez` 0xffe5, `c.ret` +0x32), pop_off 0x80000c98 (+0x12
`c.bnez` 0xef99, +0x16 `blez` = `bge zero,a5` 0x02f05363, +0x1e `c.bnez` 0xe789, +0x22
`c.beqz` 0xc399, `c.ret` +0x2e), release 0x80000ce0 (+0x10 `c.beqz` 0xcd11, `c.ret` +0x2a),
mycpu 0x8000195c (`c.ret` +0x1e); `jal ra` at holding+0x16, push_off+0x10/+0x18/+0x2c,
acquire+0x0c/+0x12/+0x24, pop_off+0x08, release+0x0c/+0x1e (+ the panic `jal unreachable`
at acquire+0x3c, pop_off+0x38/+0x44, release+0x34).  DRIFT (Q18): `allocpid` is inlined into
`allocproc` in this build; the inlined copy (allocproc+0x38..+0x98) contains 4-byte `beq` ×3 /
`bne` ×1 (+0x5c, +0x64, +0x76, +0x7e), a `c.j` (+0x5a) and `jal ra` to acquire/release
(+0x40, +0x94) — so Rocq's "no 4-byte beq/bne" does not hold for the Lean image; the generic
leaves (`wpBrC5` / `wpBrFallC5` at `is_rvc = false`) cover them unchanged.

## Deviations from Rocq

1. O2 STAGE C (as AxRelease deviation 1 / AxSymCtl2 deviation 1): the engine `XJal` / `XBtype`
   / `XCjr` takes no `Hloc`, so the leaves do not take Rocq's section premise `Hloc`.
2. TYPES / SPELLING as AxRelease deviation 3: `regfile` ↦ `RegMap`, `rget m r` ↦ `rget cid m r`
   (explicit SC hart `cid`), `<[Regidx rd := regval_into_reg v]> m` ↦ `m.set rd v`,
   `m !!! Regidx csp_rs1` ↦ `m 2#5`, `Rtp` ↦ `4#5`, `uint r = 0` ↦ `r.toNat = 0`,
   `register_lookup PC rs` ↦ `rs .PC`, `gpr r rs` ↦ `uxaXget rs r`, `add_vec pc (sign_extend'
   64 imm)` ↦ `pc + sign_extend (m := 64) imm`, `add_vec_int pc (incr is_rvc)` ↦
   `BitVec.addInt pc (incr is_rvc)` (`XBtype`'s form), `eq_vec (access_vec_dec v 0) 'b"0" =
   true` ↦ `(BitVec.access v 0 == 0#1) = true`, `zeros' 12` ↦ `zeros (n := 12)`, `ret_pc` ↦
   `WeakLeafMret.retPc`, `ghost_var γ (1/2)` ↦ `ghost_var γ (.own (1 : Qp).half)`, `WPd s @
   MaybeStuck; i {{ Φ0 }}` ↦ `wpd .MaybeStuck i s Φ0`.  The `let`s of `ctl_ok5` / `dead_ok`
   are inlined.  `IntrDefs.rd_ok` ↦ `MachCSL.rdOk` (three conjuncts, AxRelease deviation 6).
   Section variables are explicit arguments of each declaration that uses them; the
   iProp-valued premise `Cond_mono` is `⊢ Cond C -∗ Cond C'`.
3. `wp_next`'s continuation is indexed by the resuming hart `cpu'` (AxSymMem3 deviation 2):
   `cap4` and `wpBrC5`'s `lv` are at `cpu'` (Rocq's `CID`), `goal4` at the ambient `cid` (as
   AxRelease).
4. `cur5Upd` is proved by AxRelease's `cur4Write` (at `val = v`, `C' = C`); `gvalLv` /
   `gvalLvExact` by unfolding (Lean's `gprRel` already covers x0).

**Rocq → Lean name map.**  `lv` `AxSpinCtl2.lv` (duplicated name), `exact_lv` `exactLv`,
`is_ctl` `isCtl`, `ctl_ok5` `ctlOk5`, `dead_ok` `deadOk`, `ctl_txt5` `ctlTxt5`, `instr5`
`instr5`, `ctl_regime_SW` `AxSpinCtl2.ctlRegimeSW` (duplicated name; AxSpinE6 has its own),
`gval_lv` `gvalLv`, `gval_lv_exact` `gvalLvExact`, `ret_pc_jalr` `retPcJalr`, `cur5_keep`
`cur5Keep`, `cur5_upd` `cur5Upd`, `sf_upd_keep` `sfUpdKeep`, `wp_jal_c5` `wpJalC5`, `wp_j_c5`
`wpJC5`, `wp_br_c5` `wpBrC5`, `RefGoal4` `refGoal4`, `wp_br_fall_c5` `wpBrFallC5`,
`wp_cret_c5` `wpCretC5`.  Section parameters: `Cond_mono` `CondMono`, others unchanged.

**Dropped:** nothing (Rocq 20 definitions/lemmas; Lean 20).  **Not ported:** the Ltac
`open_goal5` (inlined), the section notations (`img`, `CK`, `cur`, `Goal`, `cap`, `pcis`, `TX`,
`Hsp`, `Hf4`: written out) and the `Print Assumptions` lines (the lint's axiom check covers
them).
-/
import Weak.AxRelease

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std MachCSL
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D LeanRV64D.Functions

/-! # 1. Pure vocabulary -/

/-- Rocq `lv`: the LOGICAL value an instruction reads (x0 = 0). -/
def AxSpinCtl2.lv (cid : CPU) (m : RegMap) (r : BitVec 5) : BitVec 64 :=
  if r.toNat = 0 then zero_reg else rget cid m r

def exactLv (Ex : BitVec 64 → BitVec 5 → Prop) (pc : BitVec 64) (r : BitVec 5) : Prop :=
  r.toNat = 0 ∨ exactAt Ex pc r

def isCtl (ins : instruction) : Bool :=
  match ins with
  | .JAL _ | .JALR _ | .BTYPE _ => true
  | _ => false

def ctlOk5 (Armed : BitVec 64 → Prop) (Ex : BitVec 64 → BitVec 5 → Prop)
    (pc : BitVec 64) (is_rvc : Bool) (ins : instruction) : Prop :=
  match ins with
  | .JAL (imm, .Regidx rd) =>
      (BitVec.access (pc + sign_extend (m := 64) imm) 0 == 0#1) = true ∧
      ¬ Armed (pc + sign_extend (m := 64) imm) ∧
      (∀ r, Ex (pc + sign_extend (m := 64) imm) r → (Ex pc r ∧ r ≠ rd) ∨ (r = rd ∧ rd.toNat ≠ 0))
  | .BTYPE (imm, .Regidx rs2, .Regidx rs1, _) =>
      (BitVec.access (pc + sign_extend (m := 64) imm) 0 == 0#1) = true ∧
      ¬ Armed (pc + sign_extend (m := 64) imm) ∧ ¬ Armed (BitVec.addInt pc (incr is_rvc)) ∧
      (∀ r, Ex (pc + sign_extend (m := 64) imm) r → Ex pc r) ∧
      (∀ r, Ex (BitVec.addInt pc (incr is_rvc)) r → Ex pc r) ∧
      (regidx.Regidx rs1 ≠ regidx.Regidx 4#5 ∧ regidx.Regidx rs2 ≠ regidx.Regidx 4#5)
  | .JALR _ => True
  | _ => False

def deadOk (Dead : BitVec 64 → Prop) (Ex : BitVec 64 → BitVec 5 → Prop)
    (pc : BitVec 64) (ins : instruction) : Prop :=
  match ins with
  | .BTYPE (imm, .Regidx rs2, .Regidx rs1, _) =>
      Dead (pc + sign_extend (m := 64) imm) ∨ (exactLv Ex pc rs1 ∧ exactLv Ex pc rs2)
  | _ => True

/-- The instruction fact on control words: the engine's text fact + `ctlOk5`. -/
def ctlTxt5 (σi : ExecSt) (T : PTree) (satp0 : BitVec 64)
    (Armed : BitVec 64 → Prop) (Ex : BitVec 64 → BitVec 5 → Prop)
    (pc : BitVec 64) (is_rvc : Bool) (ins : instruction) : Prop :=
  textOkCtl (imgS σi) (ctrlOkSW T satp0) (textAtS σi T) (textAt4S σi T) pc is_rvc ins ∧
  ctlOk5 Armed Ex pc is_rvc ins

section instr5Def
variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF] [Axpol]

/-- `instr4` on non-control words, the control arm on jal / jalr / branches. -/
def instr5 (σi : ExecSt) (T : PTree) (satp0 : BitVec 64)
    (Armed : BitVec 64 → Prop) (Ex : BitVec 64 → BitVec 5 → Prop) (Dead : BitVec 64 → Prop)
    (pc : BitVec 64) (is_rvc : Bool) (ins : instruction) : IProp GF :=
  if isCtl ins then iprop(⌜ctlTxt5 σi T satp0 Armed Ex pc is_rvc ins ∧ deadOk Dead Ex pc ins⌝)
  else instr4 (GF := GF) σi T satp0 Armed Ex pc is_rvc ins

end instr5Def

theorem AxSpinCtl2.ctlRegimeSW (T : PTree) (satp0 : BitVec 64) :
    ctlRegime (ctrlOkSW T satp0) :=
  fun s hc => ctlRegimeS T satp0 s hc.1

theorem gvalLv (cid : CPU) (m : RegMap) (rs : RegFile) (r : BitVec 5) :
    gprRel cid m rs → gval r rs = AxSpinCtl2.lv cid m r := by
  intro Hrel
  unfold gval AxSpinCtl2.lv
  split
  · rfl
  · exact Hrel r

theorem gvalLvExact (cid : CPU) (Ex : BitVec 64 → BitVec 5 → Prop) (m : RegMap)
    (pc : BitVec 64) (rs : RegFile) (r : BitVec 5) :
    phys5 rs 2#5 = rget cid m 2#5 → (∀ r, Ex pc r → phys5 rs r = rget cid m r) →
    exactLv Ex pc r → gval r rs = AxSpinCtl2.lv cid m r := by
  intro Hsp Hex He
  unfold gval AxSpinCtl2.lv
  split
  · rfl
  · rename_i h0
    rcases He with h | He
    · exact absurd h h0
    · exact exactPhys cid Ex m pc rs r Hsp Hex He

theorem retPcJalr (v : BitVec 64) : jalrTgt (zeros (n := 12)) v = WeakLeafMret.retPc v :=
  WeakLeafJump.retPcJalr v

/-! # 2. The leaves -/

section ctl5
variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF] [Axpol]
variable [GhostVarG GF RegMap] [GhostVarG GF (BitVec 64 × Bool)] [GhostVarG GF Nat]
variable (i : Agent) (cid cpu : CPU) (γm γp γn : GName)
variable (σi : ExecSt) (T : PTree) (satp0 : BitVec 64)
variable (hmode : _get_Satp64_Mode (Mk_Satp64 satp0) = 8#4)
  (hasid : zero_extend (m := 16) (satp_to_asid satp0) = 0#16)
  (hppn : BitVec.setWidth 44 (satp_to_ppn satp0) = T.base)
variable (Armed : BitVec 64 → Prop) (Ex : BitVec 64 → BitVec 5 → Prop)
variable (SF : BitVec 64 → Nat → IProp GF)
variable (Cond : Prop → IProp GF)
variable (Htext : ∀ GD, rvwmoCatConsistent GD →
  AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜textFixed GD i (imgS σi)⌝)
variable (Hflow : ∀ GD ls k, rvwmoCatConsistent GD →
  (∃ lb aq base n vs, (AxOpsem.grow GD i)[k]? = some lb ∧ aident lb = .IRead aq base n ∧
     imgBytes (imgS σi) base n = some vs) →
  AxirisG.gconstInterp (GF := GF) GD ∗ AxirisG.localInterp GD i k ls ⊢ fetchFlow GD i k)
variable (G : Gdexec → Prop)
  (HG : ∀ GD, rvwmoCatConsistent GD → AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜G GD⌝)

/-- `cur4` at an ARBITRARY landing pc, registers unchanged. -/
theorem cur5Keep (m : RegMap) (pc pc' : BitVec 64) (rs rs' : RegFile) (k' : Nat)
    (s' : Athread) (C : Prop) :
    RetX cpu rs' k' s' → ctrlOkSW T satp0 rs' → rs' .PC = pc' →
    (∀ r : BitVec 5, r.toNat ≠ 0 → uxaXget rs' r = uxaXget rs r) →
    phys5 rs 4#5 = rget cid m 4#5 → phys5 rs 2#5 = rget cid m 2#5 →
    (∀ r, Ex pc r → phys5 rs r = rget cid m r) → (∀ r, Ex pc' r → Ex pc r) →
    (C → gprRel cid m rs) → cur4 cid cpu T satp0 Ex m pc' s' C := by
  intro HR Hc HPC Hg Htp Hsp Hex Hsub Hrel
  have Hsame : ∀ r, phys5 rs' r = phys5 rs r := by
    intro r
    show uxaXget rs' r = uxaXget rs r
    by_cases h0 : r.toNat = 0
    · rw [AxReuseProbe2.uxaXgetZero _ r h0, AxReuseProbe2.uxaXgetZero _ r h0]
    · exact Hg r h0
  refine ⟨rs', k', HR, Hc, HPC, by rw [Hsame]; exact Htp, by rw [Hsame]; exact Hsp, ?_, ?_⟩
  · intro r Hr
    rw [Hsame]
    exact Hex r (Hsub r Hr)
  · intro HCC r
    exact (Hsame r).trans (Hrel HCC r)

/-- `cur4` at an arbitrary landing pc after a LINK write of `rd := v`. -/
theorem cur5Upd (m : RegMap) (pc pc' : BitVec 64) (rs rs' : RegFile) (k' : Nat)
    (s' : Athread) (rd : BitVec 5) (v : BitVec 64) (C : Prop) :
    rd.toNat ≠ 0 → MachCSL.rdOk rd →
    RetX cpu rs' k' s' → ctrlOkSW T satp0 rs' → rs' .PC = pc' →
    (∀ r : BitVec 5, r.toNat ≠ 0 → uxaXget rs' r = gprPost (some (rd, v)) rs r) →
    phys5 rs 4#5 = rget cid m 4#5 → phys5 rs 2#5 = rget cid m 2#5 →
    (∀ r, Ex pc r → phys5 rs r = rget cid m r) →
    (∀ r, Ex pc' r → (Ex pc r ∧ r ≠ rd) ∨ (r = rd ∧ rd.toNat ≠ 0)) →
    (C → gprRel cid m rs) →
    cur4 cid cpu T satp0 Ex (m.set rd v) pc' s' C := by
  intro Hrd Hrdok HR Hc HPC Hg Htp Hsp Hex Hex' Hrel
  exact cur4Write cid cpu T satp0 Ex m pc pc' rs rs' k' s' rd v v C C HR Hc HPC Hrd Hrdok.2.2
    Hg Htp Hsp Hex (fun _ => rfl)
    (fun r Hr => (Hex' r Hr).imp id (fun h => ⟨h.1, rfl⟩)) Hrel (fun HCC => ⟨HCC, rfl⟩)

omit [InvGS_gen hlc GF] [AxirisG GF] [Axpol] [GhostVarG GF RegMap]
  [GhostVarG GF (BitVec 64 × Bool)] [GhostVarG GF Nat] in
theorem sfUpdKeep (m : RegMap) (rd : BitVec 5) (v : BitVec 64) (n : Nat) :
    MachCSL.rdOk rd → SF (m 2#5) n ⊢ SF ((m.set rd v) 2#5) n := by
  intro Hrd
  rw [RegMap.set_other _ _ _ _ (fun e => Hrd.2.1 e.symm)]
  try exact .rfl

include hmode hasid hppn Htext Hflow HG in
/-- Rocq `wp_jal_c5`: jal rd, imm (rd ≠ 0, either width): rd := pc + incr (EXACT). -/
theorem wpJalC5 (pc : BitVec 64) (is_rvc : Bool) (imm : BitVec 21) (rd : BitVec 5)
    (m : RegMap) (n : Nat) (b : Bool) (p : BitVec 64) :
    rd.toNat ≠ 0 → MachCSL.rdOk rd →
    ⊢ cap4 (GF := GF) γm γn SF cid m n b p -∗ pcIs4 (GF := GF) γp Armed pc -∗
      ⌜ctlTxt5 σi T satp0 Armed Ex pc is_rvc (.JAL (imm, .Regidx rd))⌝ -∗
      wpNext b p cid (fun cpu' => iprop(
        cap4 γm γn SF cpu' (m.set rd (BitVec.addInt pc (incr is_rvc))) n b p -∗
        pcIs4 γp Armed (pc + sign_extend (m := 64) imm) -∗
        goal4 i cid cpu γm γp γn T satp0 Ex Cond)) -∗
      goal4 i cid cpu γm γp γn T satp0 Ex Cond := by
  intro Hrd Hrdok
  unfold cap4 pcIs4
  iintro ⟨%Hb, Hm, Hn, HS⟩ ⟨%r0, Hp, %_⟩ %Hi Hcont
  subst Hb
  obtain ⟨Htx, Hal, HnA, Hext⟩ := Hi
  ihave Hcont := wpNext_off p cid _ $$ Hcont
  unfold goal4
  iintro %s %m' %n' %pc' %r' %C %Hcur Hm' Hn' Hp' HC
  ihave %h1 := ghost_var_agree _ _ _ _ _ $$ Hm Hm'
  ihave %h2 := ghost_var_agree _ _ _ _ _ $$ Hn Hn'
  ihave %h3 := ghost_var_agree _ _ _ _ _ $$ Hp Hp'
  subst h1 h2
  injection h3 with h3a h3b
  subst h3a h3b
  obtain ⟨rs, k, HRet, Hctrl, HPC, Htp, Hspx, Hex, Hrel⟩ := Hcur
  iapply (XJal (imgS σi) i cpu (ctrlOkSW T satp0) (textAtS σi T) (textAt4S σi T)
    (SpineOkTSW σi T satp0 hmode hasid hppn) (SpineFetch4TSW σi T satp0 hmode hasid hppn)
    (AxSpinCtl2.ctlRegimeSW T satp0) Htext Hflow G HG (Φ0 (GF := GF)) (Hmid3 i G)
    s rs k pc is_rvc imm rd HRet Hctrl HPC Htx Hal (Hb3 i cpu G rs k))
  unfold XPost
  iintro %s' %rs' %k' %HRet' %Hctrl' %HPC' %Hg
  have Hg' : ∀ r : BitVec 5, r.toNat ≠ 0 →
      uxaXget rs' r = gprPost (some (rd, BitVec.addInt pc (incr is_rvc))) rs r := by
    intro r Hr
    have h := Hg r Hr
    unfold linkOw at h
    rw [if_neg Hrd] at h
    exact h
  iapply bupdWpd
  imod ghost_var_update_halves (m.set rd (BitVec.addInt pc (incr is_rvc))) γm m m $$ Hm Hm'
    with ⟨Hm, Hm'⟩
  imod ghost_var_update_halves (pc + sign_extend (m := 64) imm, r0) γp (pc, r0) (pc, r0) $$
    Hp Hp' with ⟨Hp, Hp'⟩
  imodintro
  have Hcur' := cur5Upd cid cpu T satp0 Ex m pc _ rs rs' k' s' rd (BitVec.addInt pc (incr is_rvc))
    C Hrd Hrdok HRet' Hctrl' HPC' Hg' Htp Hspx Hex Hext Hrel
  iapply Hcont $$ [Hm Hn HS] [Hp] %_ %(m.set rd (BitVec.addInt pc (incr is_rvc))) %n
    %(pc + sign_extend (m := 64) imm) %r0 %C %Hcur' Hm' Hn' Hp' HC
  · isplitr
    · ipureintro; rfl
    · isplitl [Hm]
      · iexact Hm
      · isplitl [Hn]
        · iexact Hn
        · iapply (sfUpdKeep SF m rd _ n Hrdok)
          iexact HS
  · iexists r0
    isplitl [Hp]
    · iexact Hp
    · ipureintro
      intro Ha
      exact absurd Ha HnA

include hmode hasid hppn Htext Hflow HG in
/-- Rocq `wp_j_c5`: j imm (jal x0 / c.j): no link. -/
theorem wpJC5 (pc : BitVec 64) (is_rvc : Bool) (imm : BitVec 21) (rd : BitVec 5)
    (m : RegMap) (n : Nat) (b : Bool) (p : BitVec 64) :
    rd.toNat = 0 →
    ⊢ cap4 (GF := GF) γm γn SF cid m n b p -∗ pcIs4 (GF := GF) γp Armed pc -∗
      ⌜ctlTxt5 σi T satp0 Armed Ex pc is_rvc (.JAL (imm, .Regidx rd))⌝ -∗
      wpNext b p cid (fun cpu' => iprop(
        cap4 γm γn SF cpu' m n b p -∗
        pcIs4 γp Armed (pc + sign_extend (m := 64) imm) -∗
        goal4 i cid cpu γm γp γn T satp0 Ex Cond)) -∗
      goal4 i cid cpu γm γp γn T satp0 Ex Cond := by
  intro Hrd
  unfold cap4 pcIs4
  iintro ⟨%Hb, Hm, Hn, HS⟩ ⟨%r0, Hp, %_⟩ %Hi Hcont
  subst Hb
  obtain ⟨Htx, Hal, HnA, Hext⟩ := Hi
  ihave Hcont := wpNext_off p cid _ $$ Hcont
  unfold goal4
  iintro %s %m' %n' %pc' %r' %C %Hcur Hm' Hn' Hp' HC
  ihave %h1 := ghost_var_agree _ _ _ _ _ $$ Hm Hm'
  ihave %h2 := ghost_var_agree _ _ _ _ _ $$ Hn Hn'
  ihave %h3 := ghost_var_agree _ _ _ _ _ $$ Hp Hp'
  subst h1 h2
  injection h3 with h3a h3b
  subst h3a h3b
  obtain ⟨rs, k, HRet, Hctrl, HPC, Htp, Hspx, Hex, Hrel⟩ := Hcur
  iapply (XJal (imgS σi) i cpu (ctrlOkSW T satp0) (textAtS σi T) (textAt4S σi T)
    (SpineOkTSW σi T satp0 hmode hasid hppn) (SpineFetch4TSW σi T satp0 hmode hasid hppn)
    (AxSpinCtl2.ctlRegimeSW T satp0) Htext Hflow G HG (Φ0 (GF := GF)) (Hmid3 i G)
    s rs k pc is_rvc imm rd HRet Hctrl HPC Htx Hal (Hb3 i cpu G rs k))
  unfold XPost
  iintro %s' %rs' %k' %HRet' %Hctrl' %HPC' %Hg
  have Hg' : ∀ r : BitVec 5, r.toNat ≠ 0 → uxaXget rs' r = uxaXget rs r := by
    intro r Hr
    have h := Hg r Hr
    rw [linkOwZero _ _ Hrd] at h
    exact h
  iapply bupdWpd
  imod ghost_var_update_halves (pc + sign_extend (m := 64) imm, r0) γp (pc, r0) (pc, r0) $$
    Hp Hp' with ⟨Hp, Hp'⟩
  imodintro
  have Hcur' := cur5Keep cid cpu T satp0 Ex m pc _ rs rs' k' s' C HRet' Hctrl' HPC' Hg' Htp Hspx
    Hex (fun r Hr => by
      rcases Hext r Hr with ⟨h, _⟩ | ⟨_, h⟩
      · exact h
      · exact absurd Hrd h) Hrel
  iapply Hcont $$ [Hm Hn HS] [Hp] %_ %m %n %(pc + sign_extend (m := 64) imm) %r0 %C %Hcur'
    Hm' Hn' Hp' HC
  · isplitr
    · ipureintro; rfl
    · isplitl [Hm]
      · iexact Hm
      · isplitl [Hn]
        · iexact Hn
        · iexact HS
  · iexists r0
    isplitl [Hp]
    · iexact Hp
    · ipureintro
      intro Ha
      exact absurd Ha HnA

/- the condition is monotone (Rocq `Cond_mono`; proved at `AxCondM.CondA`) -/
variable (CondMono : ∀ C C' : Prop, (C → C') → ⊢ Cond C -∗ Cond C')

include hmode hasid hppn Htext Hflow HG CondMono in
/-- Rocq `wp_br_c5`: a branch, BOTH arms: the hart proceeds on the PHYSICAL direction; the arm
learns the logical direction for exact operands, and the condition carries it (D4). -/
theorem wpBrC5 (pc : BitVec 64) (is_rvc : Bool) (imm : BitVec 13) (rs2 rs1 : BitVec 5)
    (op : bop) (m : RegMap) (n : Nat) (b : Bool) (p : BitVec 64) :
    ⊢ cap4 (GF := GF) γm γn SF cid m n b p -∗ pcIs4 (GF := GF) γp Armed pc -∗
      ⌜ctlTxt5 σi T satp0 Armed Ex pc is_rvc (.BTYPE (imm, .Regidx rs2, .Regidx rs1, op))⌝ -∗
      wpNext b p cid (fun cpu' => iprop(
        ∀ dir : Bool,
        cap4 γm γn SF cpu' m n b p -∗
        pcIs4 γp Armed (if dir then pc + sign_extend (m := 64) imm
          else BitVec.addInt pc (incr is_rvc)) -∗
        ⌜exactLv Ex pc rs1 → exactLv Ex pc rs2 →
          AxSymCtl2.bcond op (AxSpinCtl2.lv cpu' m rs1) (AxSpinCtl2.lv cpu' m rs2) = dir⌝ -∗
        goal4 i cid cpu γm γp γn T satp0 Ex Cond)) -∗
      goal4 i cid cpu γm γp γn T satp0 Ex Cond := by
  unfold cap4 pcIs4
  iintro ⟨%Hb, Hm, Hn, HS⟩ ⟨%r0, Hp, %_⟩ %Hi Hcont
  subst Hb
  obtain ⟨Htx, Hal, HnAt, HnAf, Hsubt, Hsubf, _⟩ := Hi
  ihave Hcont := wpNext_off p cid _ $$ Hcont
  unfold goal4
  iintro %s %m' %n' %pc' %r' %C %Hcur Hm' Hn' Hp' HC
  ihave %h1 := ghost_var_agree _ _ _ _ _ $$ Hm Hm'
  ihave %h2 := ghost_var_agree _ _ _ _ _ $$ Hn Hn'
  ihave %h3 := ghost_var_agree _ _ _ _ _ $$ Hp Hp'
  subst h1 h2
  injection h3 with h3a h3b
  subst h3a h3b
  obtain ⟨rs, k, HRet, Hctrl, HPC, Htp, Hspx, Hex, Hrel⟩ := Hcur
  iapply (XBtype (imgS σi) i cpu (ctrlOkSW T satp0) (textAtS σi T) (textAt4S σi T)
    (SpineOkTSW σi T satp0 hmode hasid hppn) (SpineFetch4TSW σi T satp0 hmode hasid hppn)
    (AxSpinCtl2.ctlRegimeSW T satp0) Htext Hflow G HG (Φ0 (GF := GF)) (Hmid3 i G)
    s rs k pc is_rvc imm rs2 rs1 op HRet Hctrl HPC Htx Hal (Hb3 i cpu G rs k))
  unfold XPost
  iintro %s' %rs' %k' %HRet' %Hctrl' %HPC' %Hg
  obtain ⟨dir, Hdir⟩ : ∃ d, AxSymCtl2.bcond op (gval rs1 rs) (gval rs2 rs) = d := ⟨_, rfl⟩
  rw [Hdir] at HPC'
  iapply bupdWpd
  imod ghost_var_update_halves (if dir then pc + sign_extend (m := 64) imm
      else BitVec.addInt pc (incr is_rvc), r0) γp (pc, r0) (pc, r0) $$ Hp Hp' with ⟨Hp, Hp'⟩
  imodintro
  have Hcur' := cur5Keep cid cpu T satp0 Ex m pc _ rs rs' k' s'
    (C ∧ AxSymCtl2.bcond op (AxSpinCtl2.lv cid m rs1) (AxSpinCtl2.lv cid m rs2) = dir)
    HRet' Hctrl' HPC' (fun r Hr => Hg r Hr) Htp Hspx Hex
    (fun r Hr => by
      cases dir
      · exact Hsubf r Hr
      · exact Hsubt r Hr)
    (fun HCC => Hrel HCC.1)
  have Hlog : exactLv Ex pc rs1 → exactLv Ex pc rs2 →
      AxSymCtl2.bcond op (AxSpinCtl2.lv cid m rs1) (AxSpinCtl2.lv cid m rs2) = dir := by
    intro H1 H2
    rw [← gvalLvExact cid Ex m pc rs rs1 Hspx Hex H1, ← gvalLvExact cid Ex m pc rs rs2 Hspx Hex H2]
    exact Hdir
  have HCstr : C →
      C ∧ AxSymCtl2.bcond op (AxSpinCtl2.lv cid m rs1) (AxSpinCtl2.lv cid m rs2) = dir := by
    intro HCC
    refine ⟨HCC, ?_⟩
    rw [← gvalLv cid m rs rs1 (Hrel HCC), ← gvalLv cid m rs rs2 (Hrel HCC)]
    exact Hdir
  ihave HC := (CondMono C _ HCstr) $$ HC
  iapply Hcont $$ %dir [Hm Hn HS] [Hp] %Hlog %_ %m %n
    %(if dir then pc + sign_extend (m := 64) imm else BitVec.addInt pc (incr is_rvc)) %r0
    %(C ∧ AxSymCtl2.bcond op (AxSpinCtl2.lv cid m rs1) (AxSpinCtl2.lv cid m rs2) = dir)
    %Hcur' Hm' Hn' Hp' HC
  · isplitr
    · ipureintro; rfl
    · isplitl [Hm]
      · iexact Hm
      · isplitl [Hn]
        · iexact Hn
        · iexact HS
  · iexists r0
    isplitl [Hp]
    · iexact Hp
    · ipureintro
      intro Ha
      cases dir
      · exact absurd Ha HnAf
      · exact absurd Ha HnAt

/-! ## A branch whose LOGICAL direction is fall-through (the SC slot shape) -/

variable (Dead : BitVec 64 → Prop)

/-- Rocq `RefGoal4`: `goal4` at pc `pt` restricted to REFUTED conditions. -/
def refGoal4 (pt : BitVec 64) : IProp GF :=
  iprop(∀ (s : Athread) (m : RegMap) (n : Nat) (r : Bool) (C : Prop),
    ⌜cur4 cid cpu T satp0 Ex m pt s C⌝ -∗ ⌜¬ C⌝ -∗
    ghost_var γm (.own (1 : Qp).half) m -∗ ghost_var γn (.own (1 : Qp).half) n -∗
    ghost_var γp (.own (1 : Qp).half) (pt, r) -∗ Cond C -∗
    wpd .MaybeStuck i s (Φ0 (GF := GF)))

variable (Hdead : ∀ pt, Dead pt → ⊢ refGoal4 i cid cpu γm γp γn T satp0 Ex Cond pt)

include hmode hasid hppn Htext Hflow HG Hdead in
/-- Rocq `wp_br_fall_c5`: a physically-taken branch has a REFUTED condition and lands at a
`Dead` target. -/
theorem wpBrFallC5 (pc : BitVec 64) (is_rvc : Bool) (imm : BitVec 13) (rs2 rs1 : BitVec 5)
    (op : bop) (m : RegMap) (n : Nat) (b : Bool) (p : BitVec 64) :
    AxSymCtl2.bcond op (AxSpinCtl2.lv cid m rs1) (AxSpinCtl2.lv cid m rs2) = false →
    ⊢ cap4 (GF := GF) γm γn SF cid m n b p -∗ pcIs4 (GF := GF) γp Armed pc -∗
      ⌜ctlTxt5 σi T satp0 Armed Ex pc is_rvc (.BTYPE (imm, .Regidx rs2, .Regidx rs1, op)) ∧
        deadOk Dead Ex pc (.BTYPE (imm, .Regidx rs2, .Regidx rs1, op))⌝ -∗
      wpNext b p cid (fun cpu' => iprop(
        cap4 γm γn SF cpu' m n b p -∗
        pcIs4 γp Armed (BitVec.addInt pc (incr is_rvc)) -∗
        goal4 i cid cpu γm γp γn T satp0 Ex Cond)) -∗
      goal4 i cid cpu γm γp γn T satp0 Ex Cond := by
  intro Hfall
  unfold cap4 pcIs4
  iintro ⟨%Hb, Hm, Hn, HS⟩ ⟨%r0, Hp, %_⟩ %Hi Hcont
  subst Hb
  obtain ⟨⟨Htx, Hal, _, HnAf, Hsubt, Hsubf, _⟩, Hdd⟩ := Hi
  ihave Hcont := wpNext_off p cid _ $$ Hcont
  unfold goal4
  iintro %s %m' %n' %pc' %r' %C %Hcur Hm' Hn' Hp' HC
  ihave %h1 := ghost_var_agree _ _ _ _ _ $$ Hm Hm'
  ihave %h2 := ghost_var_agree _ _ _ _ _ $$ Hn Hn'
  ihave %h3 := ghost_var_agree _ _ _ _ _ $$ Hp Hp'
  subst h1 h2
  injection h3 with h3a h3b
  subst h3a h3b
  obtain ⟨rs, k, HRet, Hctrl, HPC, Htp, Hspx, Hex, Hrel⟩ := Hcur
  iapply (XBtype (imgS σi) i cpu (ctrlOkSW T satp0) (textAtS σi T) (textAt4S σi T)
    (SpineOkTSW σi T satp0 hmode hasid hppn) (SpineFetch4TSW σi T satp0 hmode hasid hppn)
    (AxSpinCtl2.ctlRegimeSW T satp0) Htext Hflow G HG (Φ0 (GF := GF)) (Hmid3 i G)
    s rs k pc is_rvc imm rs2 rs1 op HRet Hctrl HPC Htx Hal (Hb3 i cpu G rs k))
  unfold XPost
  iintro %s' %rs' %k' %HRet' %Hctrl' %HPC' %Hg
  have Hkeep : ∀ r : BitVec 5, r.toNat ≠ 0 → uxaXget rs' r = uxaXget rs r := fun r Hr => Hg r Hr
  cases Hdir : AxSymCtl2.bcond op (gval rs1 rs) (gval rs2 rs)
  · -- physically FALLS: the logical continuation
    rw [Hdir] at HPC'
    iapply bupdWpd
    imod ghost_var_update_halves (BitVec.addInt pc (incr is_rvc), r0) γp (pc, r0) (pc, r0) $$
      Hp Hp' with ⟨Hp, Hp'⟩
    imodintro
    have Hcur' := cur5Keep cid cpu T satp0 Ex m pc _ rs rs' k' s' C HRet' Hctrl' HPC' Hkeep
      Htp Hspx Hex Hsubf Hrel
    iapply Hcont $$ [Hm Hn HS] [Hp] %_ %m %n %(BitVec.addInt pc (incr is_rvc)) %r0 %C %Hcur'
      Hm' Hn' Hp' HC
    · isplitr
      · ipureintro; rfl
      · isplitl [Hm]
        · iexact Hm
        · isplitl [Hn]
          · iexact Hn
          · iexact HS
    · iexists r0
      isplitl [Hp]
      · iexact Hp
      · ipureintro
        intro Ha
        exact absurd Ha HnAf
  · -- physically TAKEN: the condition is refuted, the target is dead
    rw [Hdir] at HPC'
    have HnC : ¬ C := by
      intro HCC
      rw [gvalLv cid m rs rs1 (Hrel HCC), gvalLv cid m rs rs2 (Hrel HCC), Hfall] at Hdir
      exact Bool.noConfusion Hdir
    rcases Hdd with Hd | ⟨H1, H2⟩
    · iapply bupdWpd
      imod ghost_var_update_halves (pc + sign_extend (m := 64) imm, r0) γp (pc, r0) (pc, r0) $$
        Hp Hp' with ⟨Hp, Hp'⟩
      imodintro
      have Hcur' := cur5Keep cid cpu T satp0 Ex m pc _ rs rs' k' s' C HRet' Hctrl' HPC' Hkeep
        Htp Hspx Hex Hsubt Hrel
      have HD := Hdead _ Hd
      unfold refGoal4 at HD
      ihave HD := HD
      iapply HD $$ %s' %m %n %r0 %C %Hcur' %HnC Hm' Hn' Hp' HC
    · exfalso
      rw [gvalLvExact cid Ex m pc rs rs1 Hspx Hex H1, gvalLvExact cid Ex m pc rs rs2 Hspx Hex H2,
        Hfall] at Hdir
      exact Bool.noConfusion Hdir

include hmode hasid hppn Htext Hflow HG in
/-- Rocq `wp_cret_c5`: c.jr rs1 / c.ret, EXACT form: rs1 exact here, the logical target's exact
map ⊆ this one, the target not armed. -/
theorem wpCretC5 (pc : BitVec 64) (rs1 : BitVec 5) (m : RegMap) (n : Nat) (b : Bool)
    (p : BitVec 64) :
    rs1.toNat ≠ 0 → exactAt Ex pc rs1 →
    (∀ r, Ex (WeakLeafMret.retPc (rget cid m rs1)) r → Ex pc r) →
    ¬ Armed (WeakLeafMret.retPc (rget cid m rs1)) →
    ⊢ cap4 (GF := GF) γm γn SF cid m n b p -∗ pcIs4 (GF := GF) γp Armed pc -∗
      ⌜textOkCtl (imgS σi) (ctrlOkSW T satp0) (textAtS σi T) (textAt4S σi T) pc true
        (.JALR (zeros (n := 12), .Regidx rs1, zreg))⌝ -∗
      wpNext b p cid (fun cpu' => iprop(
        cap4 γm γn SF cpu' m n b p -∗
        pcIs4 γp Armed (WeakLeafMret.retPc (rget cid m rs1)) -∗
        goal4 i cid cpu γm γp γn T satp0 Ex Cond)) -∗
      goal4 i cid cpu γm γp γn T satp0 Ex Cond := by
  intro Hrs1 Hx Hsub HnA
  unfold cap4 pcIs4
  iintro ⟨%Hb, Hm, Hn, HS⟩ ⟨%r0, Hp, %_⟩ %Htx Hcont
  subst Hb
  ihave Hcont := wpNext_off p cid _ $$ Hcont
  unfold goal4
  iintro %s %m' %n' %pc' %r' %C %Hcur Hm' Hn' Hp' HC
  ihave %h1 := ghost_var_agree _ _ _ _ _ $$ Hm Hm'
  ihave %h2 := ghost_var_agree _ _ _ _ _ $$ Hn Hn'
  ihave %h3 := ghost_var_agree _ _ _ _ _ $$ Hp Hp'
  subst h1 h2
  injection h3 with h3a h3b
  subst h3a h3b
  obtain ⟨rs, k, HRet, Hctrl, HPC, Htp, Hspx, Hex, Hrel⟩ := Hcur
  iapply (XCjr (imgS σi) i cpu (ctrlOkSW T satp0) (textAtS σi T) (textAt4S σi T)
    (SpineOkTSW σi T satp0 hmode hasid hppn) (SpineFetch4TSW σi T satp0 hmode hasid hppn)
    (AxSpinCtl2.ctlRegimeSW T satp0) Htext Hflow G HG (Φ0 (GF := GF)) (Hmid3 i G)
    s rs k pc rs1 HRet Hctrl HPC Htx Hrs1 (Hb3 i cpu G rs k))
  unfold XPost
  iintro %s' %rs' %k' %HRet' %Hctrl' %HPC' %Hg
  have Htg : jalrTgt (zeros (n := 12)) (uxaXget rs rs1) = WeakLeafMret.retPc (rget cid m rs1) := by
    rw [retPcJalr]
    exact congrArg WeakLeafMret.retPc (exactPhys cid Ex m pc rs rs1 Hspx Hex Hx)
  rw [Htg] at HPC'
  iapply bupdWpd
  imod ghost_var_update_halves (WeakLeafMret.retPc (rget cid m rs1), r0) γp (pc, r0) (pc, r0) $$
    Hp Hp' with ⟨Hp, Hp'⟩
  imodintro
  have Hcur' := cur5Keep cid cpu T satp0 Ex m pc _ rs rs' k' s' C HRet' Hctrl' HPC'
    (fun r Hr => Hg r Hr) Htp Hspx Hex Hsub Hrel
  iapply Hcont $$ [Hm Hn HS] [Hp] %_ %m %n %(WeakLeafMret.retPc (rget cid m rs1)) %r0 %C %Hcur'
    Hm' Hn' Hp' HC
  · isplitr
    · ipureintro; rfl
    · isplitl [Hm]
      · iexact Hm
      · isplitl [Hn]
        · iexact Hn
        · iexact HS
  · iexists r0
    isplitl [Hp]
    · iexact Hp
    · ipureintro
      intro Ha
      exact absurd Ha HnA

end ctl5

end Weak
