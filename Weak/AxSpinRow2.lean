/-
Weak: **spinlock plan, ROW-PINNED leaves, part 2** — the leaves on SURFACE v4 (`AxRelease`:
`cur4` / `goal4` / `cap4` / `pcIs4`), interrupts OFF (regime `ctrlOkSW`), and the EXACT-MAP
GROWTH LAW (AxSL tier).

Rocq: `iris/AxSpinRow2.v` @ xxvzwolszwmp.

## The Rocq header, in substance

§1 GROWTH LAW.  `exAt Ex pc b` = `Ex` plus "register `b` is exact AT `pc`".  `cur4GrowSplit`:
at a state of `cur4 Ex m pc`, EITHER the physical `b` equals the logical one (then
`cur4 (exAt Ex pc b)` holds — `b` is exact HERE, by the physical state, not by provenance) OR
the state is in the OFF set (physical ≠ logical).  The decision is on the PHYSICAL register
file — graph-free.  `exOkGrowStore` (THE LAW, pure): `exOk` of a store at the grown map
`exAt Ex pc b` says exactly "the successor's exact set ⊆ this pc's exact set ∪ {b}" — the
base register (re-)ENTERS the exact map at a row-pinned access.  `goal4Sub`: `goal4` is
antitone in `Ex`'s strength, so a leaf proved at the grown map composes with continuations
at `Ex`.  (Why the old obstruction — AxSpinCtl `hold_ret_s1_not_exact` / `ret_ra_not_exact` —
was an artefact: surface v4's only source of exactness was PROVENANCE; once a callee-saved
register is reloaded it can never be exact again, although its physical value is pinned at
the next access by the ROW.  The grown map records that second source.)

§2 THE LEAVES.  Each has an ON arm (physical = logical: the old exact leaf at the grown map)
and an OFF arm, delegated to an explicit premise stated at the instruction's START state:
  `offBase pc r v` := every boundary state at `pc` whose physical `r` is not `v` has
    `⊢ wpd .MaybeStuck i s Φ0`;
  `offRet pc r L`  := likewise for `retPc (physical r) ≠ L`.
These are what ROW PINNING discharges (such a state's next data label or next fetch
mismatches the row ⇒ `AxSpinRow.rowStuck` ⇒ `wpdStuck`); they are NOT discharged here.
- `wpStoreRow` (sd / sw, any width) and `wpAmoswapRow`: base NOT exact at `Ex`; text fact at
  the grown map `exAt Ex pc rs1`.
- `wpCretRow`: c.ret / c.jr rs1 with rs1 NOT exact: on-arm = `retPc (physical rs1) = retPc
  (logical rs1)`; no `¬ Armed target` premise (the landing flag is set to `true`, admissible:
  `goal4` quantifies the flag).  Still needs `Ex(target) ⊆ Ex(pc)`.
- `wpCsdspCond`: c.sdsp with NON-exact data: the new word is the PHYSICAL value `v`, the
  continuation gets `wpt pa 1 v` for an arbitrary `v` and the condition is strengthened to
  `C ∧ v = logical` (`CondMono`).
RESIDUALS (Rocq): the OFF premises are not discharged (needs `firstEv` of a boundary at a
symbolic pc and a row cursor); CURSOR FINDING (AxSpinRow4 `twoSitePin`): `offRet` is false
for callees called from two sites in one row; continuation contracts Φ0 = True.

KERNEL CROSS-CHECK (Xv6/KernelImage.lean): this file states no kernel word (every leaf is
generic in pc / registers / immediates / width).

## Deviations from Rocq

1. O2 STAGE C (as AxSpinCtl2 deviation 1): the engine `XCjr` takes no `Hloc`, so `wpCretRow`
   does not take Rocq's section premise `Hloc` (the store / AMO / c.sdsp leaves keep it:
   their X bridges use it).
2. TYPES / SPELLING as AxRelease deviation 3 and AxSpinCtl2 deviation 2: `regfile` ↦ `RegMap`,
   `rget m r` ↦ `rget cid m r` (explicit SC hart `cid`), `m !!! Regidx csp_rs1` ↦ `m 2#5`,
   `<[Regidx rd := regval_into_reg v]> m` ↦ `m.set rd v`, `uint r = 0` ↦ `r.toNat = 0`,
   `register_lookup PC rs` ↦ `rs .PC`, `gpr r rs` / `gpr_val rs r` ↦ `uxaXget rs r` /
   `gprVal rs r`, `add_vec_int pc (if is_rvc then 2 else 4)` ↦ `pc + instrLen is_rvc`
   (`pc + 4#64` / `pc + 2#64` at a fixed width), `zeros' 64` ↦ `zeros (n := 64)`, `ret_pc` ↦
   `WeakLeafMret.retPc`, `concat_vec uimm ('b"000")` ↦ `uimm +++ 0b000#3`, `WPd s @
   MaybeStuck; i {{ Φ0 }}` ↦ `wpd .MaybeStuck i s Φ0`.  The statements' `let`s are inlined.
   Section variables are explicit arguments of each declaration that uses them; the
   iProp-valued Rocq premises (`Hrule`, `amo_rule3`, `st_rule`, `Cond_mono`) are entailments.
3. `wp_next`'s continuation is indexed by the resuming hart `cpu'` (AxSpinCtl2 deviation 3):
   `cap4` at `cpu'`, `goal4` at the ambient `cid`.

**Rocq → Lean name map.**  `Ex_at` `exAt`, `Ex_at_sub` `exAtSub`, `cur4_sub` `cur4Sub`,
`cur4_grow_split` `cur4GrowSplit`, `ex_ok_grow_store` `exOkGrowStore`, `ex_ok_store_no_entry`
`exOkStoreNoEntry`, `Goal4_sub` `goal4Sub`, `OffBase` `offBase`, `OffRet` `offRet`,
`wp_store_row` `wpStoreRow`, `wp_amoswap_row` `wpAmoswapRow`, `wp_cret_row` `wpCretRow`,
`wp_csdsp_cond` `wpCsdspCond`.  Section parameters: `amo_res` `amoRes`, `amo_rule3`
`amoRule3`, `HnoSplit_reg` `HnoSplitReg`, `st_rule` `stRule`, `Cond_mono` `CondMono`, others
unchanged.

**Dropped:** nothing (Rocq 13 definitions/lemmas; Lean 13).  **Not ported:** the Ltac
`agree5` (inlined), the section notations (`img`, `CK`, `GoalE`, `Goal`, `cap`, `pcis`, `TX`:
written out) and the `Print Assumptions` lines (the lint's axiom check covers them).
-/
import Weak.AxSpinCtl2

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std MachCSL
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D LeanRV64D.Functions

/-! # 1. The exact-map growth law -/

/-- Rocq `Ex_at`: `Ex` plus "register `r0` is exact at `pc0`". -/
def exAt (Ex : BitVec 64 → BitVec 5 → Prop) (pc0 : BitVec 64) (r0 : BitVec 5) :
    BitVec 64 → BitVec 5 → Prop :=
  fun p r => Ex p r ∨ (p = pc0 ∧ r = r0)

theorem exAtSub (Ex : BitVec 64 → BitVec 5 → Prop) (pc0 : BitVec 64) (r0 : BitVec 5) :
    ∀ p r, Ex p r → exAt Ex pc0 r0 p r :=
  fun _ _ H => Or.inl H

theorem cur4Sub (cid cpu : CPU) (T : PTree) (satp0 : BitVec 64)
    (E E' : BitVec 64 → BitVec 5 → Prop) (m : RegMap) (pc : BitVec 64) (s : Athread)
    (C : Prop) :
    (∀ p r, E p r → E' p r) → cur4 cid cpu T satp0 E' m pc s C →
      cur4 cid cpu T satp0 E m pc s C := by
  rintro Hs ⟨rs, k, H1, H2, H3, H4, H5, H6, H7⟩
  exact ⟨rs, k, H1, H2, H3, H4, H5, fun r Hr => H6 r (Hs _ _ Hr), H7⟩

/-- The graph-free decision: the base is physically the logical one, or not. -/
theorem cur4GrowSplit (cid cpu : CPU) (T : PTree) (satp0 : BitVec 64)
    (Ex : BitVec 64 → BitVec 5 → Prop) (m : RegMap) (pc : BitVec 64) (s : Athread) (C : Prop)
    (r0 : BitVec 5) :
    cur4 cid cpu T satp0 Ex m pc s C →
    cur4 cid cpu T satp0 (exAt Ex pc r0) m pc s C ∨
    ∃ rs k, RetX cpu rs k s ∧ ctrlOkSW T satp0 rs ∧ rs .PC = pc ∧
      phys5 rs r0 ≠ rget cid m r0 := by
  rintro ⟨rs, k, H1, H2, H3, H4, H5, H6, H7⟩
  by_cases E : phys5 rs r0 = rget cid m r0
  · refine Or.inl ⟨rs, k, H1, H2, H3, H4, H5, ?_, H7⟩
    rintro r (Hr | ⟨-, rfl⟩)
    · exact H6 r Hr
    · exact E
  · exact Or.inr ⟨rs, k, H1, H2, H3, E⟩

/-- THE GROWTH LAW (pure): at a store, `exOk` of the grown map lets the successor's exact set
contain the base register. -/
theorem exOkGrowStore (Ex : BitVec 64 → BitVec 5 → Prop) (pc : BitVec 64) (is_rvc : Bool)
    (x : BitVec 12 × regidx × regidx × word_width) (b : BitVec 5) :
    pc + instrLen is_rvc ≠ pc →
    (exOk (exAt Ex pc b) pc is_rvc (.STORE x) ↔
      ∀ r, Ex (pc + instrLen is_rvc) r → Ex pc r ∨ r = b) := by
  intro Hne
  constructor
  · intro H r Hr
    rcases (H r (Or.inl Hr) : exAt Ex pc b pc r) with h | ⟨-, h⟩
    · exact Or.inl h
    · exact Or.inr h
  · intro H r Hr
    show exAt Ex pc b pc r
    rcases Hr with Hr | ⟨E, -⟩
    · rcases H r Hr with h | h
      · exact Or.inl h
      · exact Or.inr ⟨rfl, h⟩
    · exact absurd E Hne

/-- ... and the OLD law at the un-grown map forbids it: a register not exact at a store's pc
is not exact after it. -/
theorem exOkStoreNoEntry (Ex : BitVec 64 → BitVec 5 → Prop) (pc : BitVec 64) (is_rvc : Bool)
    (x : BitVec 12 × regidx × regidx × word_width) (r : BitVec 5) :
    exOk Ex pc is_rvc (.STORE x) → ¬ Ex pc r → ¬ Ex (pc + instrLen is_rvc) r :=
  fun H Hn Hr => Hn (H r Hr)

section goalSub
variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF] [Axpol]
variable [GhostVarG GF RegMap] [GhostVarG GF (BitVec 64 × Bool)] [GhostVarG GF Nat]

theorem goal4Sub (i : Agent) (cid cpu : CPU) (γm γp γn : GName) (T : PTree)
    (satp0 : BitVec 64) (E E' : BitVec 64 → BitVec 5 → Prop) (Cond : Prop → IProp GF) :
    (∀ p r, E p r → E' p r) →
    goal4 (hlc := hlc) i cid cpu γm γp γn T satp0 E Cond ⊢
      goal4 (hlc := hlc) i cid cpu γm γp γn T satp0 E' Cond := by
  intro Hs
  unfold goal4
  iintro G %s %m %n %pc %r %C %Hcur
  iapply G $$ %s %m %n %pc %r %C %(cur4Sub cid cpu T satp0 E E' m pc s C Hs Hcur)

end goalSub

/-! # 2. The row-pinned leaves -/

section rowleaves
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
variable (Hloc : ∀ GD ls k, rvwmoCatConsistent GD →
  AxirisG.gconstInterp (GF := GF) GD ∗ AxirisG.localInterp GD i k ls ⊢
    |==> ∃ ls', AxirisG.localInterp GD i (k + 1) ls')
variable (G : Gdexec → Prop)
  (HG : ∀ GD, rvwmoCatConsistent GD → AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜G GD⌝)

/-- Rocq `OffBase`: at the instruction's START state, a physical register that disagrees with
the logical value makes the hart's WPd trivial. -/
def offBase (pc : BitVec 64) (r0 : BitVec 5) (v : BitVec 64) : Prop :=
  ∀ s rs k, RetX cpu rs k s → ctrlOkSW T satp0 rs → rs .PC = pc → phys5 rs r0 ≠ v →
    ⊢ wpd .MaybeStuck i s (Φ0 (GF := GF))

/-- Rocq `OffRet`: likewise for a return target that disagrees with the logical one. -/
def offRet (pc : BitVec 64) (r0 : BitVec 5) (L : BitVec 64) : Prop :=
  ∀ s rs k, RetX cpu rs k s → ctrlOkSW T satp0 rs → rs .PC = pc →
    WeakLeafMret.retPc (phys5 rs r0) ≠ L →
    ⊢ wpd .MaybeStuck i s (Φ0 (GF := GF))

section stores
variable (dreg damo : Int → Nat → Prop)
variable (Hdmap : ∀ (acc : MemoryAccessType mem_payload) (va : BitVec 64) (w : Nat),
  dreg (paZ va) w ∨ damo (paZ va) w → dataAtS σi T acc va w va)

include hmode hasid hppn Htext Hflow Hloc HG Hdmap in
/-- Rocq `wp_store_row`: a STORE whose base register is NOT exact. -/
theorem wpStoreRow (pc : BitVec 64) (rs2 rs1 : BitVec 5) (imm : BitVec 12) (wd : Nat)
    (m : RegMap) (n : Nat) (b : Bool) (p : BitVec 64) (Pre Post : IProp GF) :
    offBase (hlc := hlc) (GF := GF) i cpu T satp0 pc rs1 (rget cid m rs1) →
    vmemWidth wd → 1 ≤ wd ∧ wd ≤ 8 →
    (∀ c : WmClass, ⊢ ⌜Armed pc → c = .WCrel⌝ -∗ Pre -∗
      ⌜dreg (paZ (rget cid m rs1 + sign_extend (m := 64) imm)) wd⌝ ∗
      FstM rvwmoCatConsistent (dk3 (paZ (rget cid m rs1 + sign_extend (m := 64) imm)) wd) i
        (fun _ data => iprop(⌜(exactAt (exAt Ex pc rs1) pc rs2 →
            data = stBytes wd (rget cid m rs2)) ∧
          (rs2.toNat = 0 → data = stBytes wd 0#64)⌝ -∗ Post))) →
    ⊢ cap4 (GF := GF) γm γn SF cid m n b p -∗ pcIs4 (GF := GF) γp Armed pc -∗
      instr4 (GF := GF) σi T satp0 Armed (exAt Ex pc rs1) pc false
        (.STORE (imm, .Regidx rs2, .Regidx rs1, wd)) -∗
      Pre -∗
      wpNext b p cid (fun cpu' => iprop(
        cap4 γm γn SF cpu' m n b p -∗ pcIs4 γp Armed (pc + 4#64) -∗ Post -∗
        goal4 i cid cpu γm γp γn T satp0 Ex Cond)) -∗
      goal4 i cid cpu γm γp γn T satp0 Ex Cond := by
  intro Hoff Hvw Hw Hrule
  have HL := wpStoreC4 i cid cpu γm γp γn σi T satp0 hmode hasid hppn Armed (exAt Ex pc rs1)
    SF Cond Htext Hflow Hloc G HG dreg damo Hdmap pc rs2 rs1 imm wd m n false p Pre Post
    Hvw Hw Hrule
  unfold cap4 pcIs4 at HL ⊢
  iintro ⟨%Hb, Hm, Hn, HS⟩ ⟨%r0, Hp, %Har⟩ Hi Hpre Hcont
  subst Hb
  unfold goal4
  iintro %s %m' %n' %pc' %r' %C %Hcur Hm' Hn' Hp' HC
  ihave %h1 := ghost_var_agree _ _ _ _ _ $$ Hm Hm'
  ihave %h2 := ghost_var_agree _ _ _ _ _ $$ Hn Hn'
  ihave %h3 := ghost_var_agree _ _ _ _ _ $$ Hp Hp'
  subst h1 h2
  injection h3 with h3a h3b
  subst h3a h3b
  rcases cur4GrowSplit cid cpu T satp0 Ex m pc s C rs1 Hcur with
    Hcur' | ⟨rs, k, HR, Hc, HPC, Hne⟩
  · ihave HG4 := HL $$ [Hm Hn HS] [Hp] Hi Hpre [Hcont]
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
      · ipureintro; exact Har
    · ihave Hcont := wpNext_off p cid _ $$ Hcont
      iapply wpNext_off_intro
      iintro Hc Hp Hpost
      ihave Hg := Hcont $$ Hc Hp Hpost
      iapply (goal4Sub i cid cpu γm γp γn T satp0 Ex (exAt Ex pc rs1) Cond (exAtSub Ex pc rs1))
      unfold goal4
      iexact Hg
    iunfold goal4 at HG4
    iapply HG4 $$ %s %m %n %pc %r0 %C %Hcur' Hm' Hn' Hp' HC
  · ihave Hw := Hoff s rs k HR Hc HPC Hne
    iexact Hw

/- `amoswap.w{.aq}` whose base register is NOT exact -/
variable (Hagree : ∀ GD GD', rvwmoCatConsistent GD → rvwmoCatConsistent GD' →
  ⊢ AxirisG.gconstInterp (GF := GF) GD -∗ AxirisG.gconstInterp GD' -∗ ⌜GD = GD'⌝)
variable (HnoSplitReg : ∀ GD, rvwmoCatConsistent GD → AxirisG.gconstInterp (GF := GF) GD ⊢
  ⌜∀ (k : Nat) (lb : Lbl) (aq : Bool) (base : Int) (n : Nat),
    (AxOpsem.grow GD i)[k]? = some lb → aident lb = .IRead aq base n → ¬ damo base n⌝)
variable (amoRes : PAddr → BitVec 32 → (BitVec 32 → IProp GF) → IProp GF)
variable (amoRule3 : ∀ pa wnew Post, ⊢ amoRes pa wnew Post -∗ ⌜damo (paZ pa) 4⌝ ∗
  FstM rvwmoCatConsistent (dk3 (paZ pa) 4) i
    (OutOfV i (fun _ ov data => iprop(⌜data = AxDataX.wrb 4 wnew⌝ -∗
      ∀ rvs, ⌜ov = some rvs⌝ -∗ Post (rrv 4 rvs)))))

include hmode hasid hppn Htext Hflow Hloc HG Hagree Hdmap HnoSplitReg amoRule3 in
/-- Rocq `wp_amoswap_row`: amoswap.w{.aq} whose base register is NOT exact. -/
theorem wpAmoswapRow (pc : BitVec 64) (aq : Bool) (rd rs2 rs1 : BitVec 5)
    (m : RegMap) (n : Nat) (b : Bool) (p : BitVec 64) (Post : BitVec 32 → IProp GF) :
    offBase (hlc := hlc) (GF := GF) i cpu T satp0 pc rs1 (rget cid m rs1) →
    rd.toNat ≠ 0 → MachCSL.rdOk rd →
    ⊢ cap4 (GF := GF) γm γn SF cid m n b p -∗
      pcIs4 (GF := GF) γp Armed pc -∗
      instr4 (GF := GF) σi T satp0 Armed (exAt Ex pc rs1) pc false
        (.AMO (.AMOSWAP, aq, false, .Regidx rs2, .Regidx rs1, 4, .Regidx rd)) -∗
      amoRes (rget cid m rs1 + zeros (n := 64)) (AxCondM3.amoswapStored (rget cid m rs2)) Post -∗
      (∀ w : BitVec 32,
        wpNext b p cid (fun cpu' => iprop(
          cap4 γm γn SF cpu' (m.set rd (AxCondM3.amoswapLoaded w)) n b p -∗
          pcIs4 γp Armed (pc + 4#64) -∗
          Post w -∗
          goal4 i cid cpu γm γp γn T satp0 Ex Cond))) -∗
      goal4 i cid cpu γm γp γn T satp0 Ex Cond := by
  intro Hoff Hrd Hrdok
  have HL := wpAmoswapC4 i cid cpu γm γp γn σi T satp0 hmode hasid hppn Armed (exAt Ex pc rs1)
    SF Cond Htext Hflow Hloc G HG Hagree dreg damo Hdmap HnoSplitReg amoRes amoRule3
    pc aq rd rs2 rs1 m n false p Post Hrd Hrdok
  unfold cap4 pcIs4 at HL ⊢
  iintro ⟨%Hb, Hm, Hn, HS⟩ ⟨%r0, Hp, %Har⟩ Hi Hres Hcont
  subst Hb
  unfold goal4
  iintro %s %m' %n' %pc' %r' %C %Hcur Hm' Hn' Hp' HC
  ihave %h1 := ghost_var_agree _ _ _ _ _ $$ Hm Hm'
  ihave %h2 := ghost_var_agree _ _ _ _ _ $$ Hn Hn'
  ihave %h3 := ghost_var_agree _ _ _ _ _ $$ Hp Hp'
  subst h1 h2
  injection h3 with h3a h3b
  subst h3a h3b
  rcases cur4GrowSplit cid cpu T satp0 Ex m pc s C rs1 Hcur with
    Hcur' | ⟨rs, k, HR, Hc, HPC, Hne⟩
  · ihave HG4 := HL $$ [Hm Hn HS] [Hp] Hi Hres [Hcont]
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
      · ipureintro; exact Har
    · iintro %w
      ihave Hcont := Hcont $$ %w
      ihave Hcont := wpNext_off p cid _ $$ Hcont
      iapply wpNext_off_intro
      iintro Hc Hp Hpost
      ihave Hg := Hcont $$ Hc Hp Hpost
      iapply (goal4Sub i cid cpu γm γp γn T satp0 Ex (exAt Ex pc rs1) Cond (exAtSub Ex pc rs1))
      unfold goal4
      iexact Hg
    iunfold goal4 at HG4
    iapply HG4 $$ %s %m %n %pc %r0 %C %Hcur' Hm' Hn' Hp' HC
  · ihave Hw := Hoff s rs k HR Hc HPC Hne
    iexact Hw

end stores

include hmode hasid hppn Htext Hflow HG in
/-- Rocq `wp_cret_row`: c.ret / c.jr rs1 with rs1 NOT exact. -/
theorem wpCretRow (pc : BitVec 64) (rs1 : BitVec 5) (m : RegMap) (n : Nat) (b : Bool)
    (p : BitVec 64) :
    rs1.toNat ≠ 0 →
    (∀ r, Ex (WeakLeafMret.retPc (rget cid m rs1)) r → Ex pc r) →
    offRet (hlc := hlc) (GF := GF) i cpu T satp0 pc rs1 (WeakLeafMret.retPc (rget cid m rs1)) →
    ⊢ cap4 (GF := GF) γm γn SF cid m n b p -∗ pcIs4 (GF := GF) γp Armed pc -∗
      ⌜textOkCtl (imgS σi) (ctrlOkSW T satp0) (textAtS σi T) (textAt4S σi T) pc true
        (.JALR (zeros (n := 12), .Regidx rs1, zreg))⌝ -∗
      wpNext b p cid (fun cpu' => iprop(
        cap4 γm γn SF cpu' m n b p -∗
        pcIs4 γp Armed (WeakLeafMret.retPc (rget cid m rs1)) -∗
        goal4 i cid cpu γm γp γn T satp0 Ex Cond)) -∗
      goal4 i cid cpu γm γp γn T satp0 Ex Cond := by
  intro Hrs1 Hsub Hoff
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
  by_cases Heq : WeakLeafMret.retPc (phys5 rs rs1) = WeakLeafMret.retPc (rget cid m rs1)
  case neg =>
    ihave Hw := Hoff s rs k HRet Hctrl HPC Heq
    iexact Hw
  iapply (XCjr (imgS σi) i cpu (ctrlOkSW T satp0) (textAtS σi T) (textAt4S σi T)
    (SpineOkTSW σi T satp0 hmode hasid hppn) (SpineFetch4TSW σi T satp0 hmode hasid hppn)
    (AxSpinCtl2.ctlRegimeSW T satp0) Htext Hflow G HG (Φ0 (GF := GF)) (Hmid3 i G)
    s rs k pc rs1 HRet Hctrl HPC Htx Hrs1 (Hb3 i cpu G rs k))
  unfold XPost
  iintro %s' %rs' %k' %HRet' %Hctrl' %HPC' %Hg
  have Htg : jalrTgt (zeros (n := 12)) (uxaXget rs rs1) = WeakLeafMret.retPc (rget cid m rs1) := by
    rw [retPcJalr]
    exact Heq
  rw [Htg] at HPC'
  iapply bupdWpd
  imod ghost_var_update_halves (WeakLeafMret.retPc (rget cid m rs1), true) γp (pc, r0) (pc, r0) $$
    Hp Hp' with ⟨Hp, Hp'⟩
  imodintro
  have Hcur' := cur5Keep cid cpu T satp0 Ex m pc _ rs rs' k' s' C HRet' Hctrl' HPC'
    (fun r Hr => Hg r Hr) Htp Hspx Hex Hsub Hrel
  iapply Hcont $$ [Hm Hn HS] [Hp] %_ %m %n %(WeakLeafMret.retPc (rget cid m rs1)) %true %C %Hcur'
    Hm' Hn' Hp' HC
  · isplitr
    · ipureintro; rfl
    · isplitl [Hm]
      · iexact Hm
      · isplitl [Hn]
        · iexact Hn
        · iexact HS
  · iexists true
    isplitl [Hp]
    · iexact Hp
    · ipureintro
      exact fun _ => rfl

/- c.sdsp rs2, uimm(sp) with NON-exact data: the stored word is the PHYSICAL value, the
condition carries "= logical" -/
section csdsp
variable (dreg damo : Int → Nat → Prop)
variable (Hdmap : ∀ (acc : MemoryAccessType mem_payload) (va : BitVec 64) (w : Nat),
  dreg (paZ va) w ∨ damo (paZ va) w → dataAtS σi T acc va w va)
variable (wpt : PAddr → DFrac → BitVec 64 → IProp GF)
variable (stRule : ∀ pa vold vnew, ⊢ wpt pa (.own 1) vold -∗
  ⌜dreg (paZ pa) 8⌝ ∗
  Fst (dk3 (paZ pa) 8) i (fun _ data => iprop(⌜data = stBytes 8 vnew⌝ -∗ wpt pa (.own 1) vnew)))
variable (CondMono : ∀ C C' : Prop, (C → C') → ⊢ Cond C -∗ Cond C')

include hmode hasid hppn Htext Hflow Hloc HG Hdmap stRule CondMono in
/-- Rocq `wp_csdsp_cond`. -/
theorem wpCsdspCond (pc : BitVec 64) (uimm : BitVec 6) (rs2 : BitVec 5)
    (m : RegMap) (n : Nat) (vold : BitVec 64) (b : Bool) (p : BitVec 64) :
    ⊢ cap4 (GF := GF) γm γn SF cid m n b p -∗ pcIs4 (GF := GF) γp Armed pc -∗
      ⌜textOkM (imgS σi) (ctrlOkSW T satp0) (textAtS σi T) pc true
          (.STORE (zero_extend (m := 12) (uimm +++ 0b000#3), .Regidx rs2, sp, 8)) ∧
        ¬ Armed (pc + 2#64) ∧
        exOk Ex pc true (.STORE (zero_extend (m := 12) (uimm +++ 0b000#3), .Regidx rs2, sp, 8))⌝ -∗
      wpt (m 2#5 + zero_extend (m := 64) (uimm +++ 0b000#3)) (.own 1) vold -∗
      wpNext b p cid (fun cpu' => iprop(
        cap4 γm γn SF cpu' m n b p -∗ pcIs4 γp Armed (pc + 2#64) -∗
        ∀ v : BitVec 64, wpt (m 2#5 + zero_extend (m := 64) (uimm +++ 0b000#3)) (.own 1) v -∗
        goal4 i cid cpu γm γp γn T satp0 Ex Cond)) -∗
      goal4 i cid cpu γm γp γn T satp0 Ex Cond := by
  generalize Hpa0 : m 2#5 + zero_extend (m := 64) (uimm +++ 0b000#3) = pa
  unfold cap4 pcIs4
  iintro ⟨%Hb, Hm, Hn, HS⟩ ⟨%r0, Hp, %Har⟩ %Hi Hpt Hcont
  subst Hb
  obtain ⟨Htm, HnA, Hexo⟩ := Hi
  obtain ⟨-, h, i0, Hat, Hdec, Hexp⟩ := Htm
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
  ihave Hst := stRule pa vold (gprVal rs rs2) $$ Hpt
  icases Hst with ⟨%Hdr, F⟩
  have Hva : pa = gprVal rs 2#5 + sign_extend (m := 64) (zero_extend (m := 12) (uimm +++ 0b000#3)) := by
    rw [← Hpa0]
    exact spPa cid m rs uimm Hspx
  iapply (XStoreS2 σi T satp0 hmode hasid hppn i cpu Htext Hflow Hloc G HG Φ0 (Hmid3 i G)
    (dk3 (paZ pa) 8) _ s rs k pc h i0 (zero_extend (m := 12) (uimm +++ 0b000#3)) rs2 2#5 8 pa pa
    r0 HRet Hctrl HPC Hat Hdec Hexp (Or.inr (Or.inr (Or.inr rfl))) ⟨by decide, by decide⟩ Hva
    (Hdmap _ pa 8 (Or.inl Hdr)) ⟨rfl, rfl⟩ (Hb3 i cpu G rs k)) $$ F
  iintro %t' %rs' %ib' %k' %HG' %Hag Hpt
  obtain ⟨Hc', HPC', Hg'⟩ := HG'
  icases Hpt with ⟨%kd, Hpt⟩
  ispecialize Hpt $$ %rfl
  iapply bupdWpd
  imod ghost_var_update_halves (pc + 2#64, false) γp (pc, r0) (pc, r0) $$ Hp Hp' with ⟨Hp, Hp'⟩
  imodintro
  have Hcur' := cur4Keep cid cpu T satp0 Ex m pc rs t' rs' ib' k'
    (C ∧ gprVal rs rs2 = rget cid m rs2) true _ Hc'
    (by rw [HPC']; rfl) Hg' Hag Htp Hspx Hex Hexo (fun _ H => H) (fun HCC => Hrel HCC.1)
  iapply Hcont $$ [Hm Hn HS] [Hp] %(gprVal rs rs2) Hpt %_ %m %n %(pc + 2#64) %false
    %(C ∧ gprVal rs rs2 = rget cid m rs2) %Hcur' Hm' Hn' Hp' [HC]
  · isplitr
    · ipureintro; rfl
    · isplitl [Hm]
      · iexact Hm
      · isplitl [Hn]
        · iexact Hn
        · iexact HS
  · iexists false
    isplitl [Hp]
    · iexact Hp
    · ipureintro
      intro Ha
      exact absurd Ha HnA
  · iapply (CondMono C (C ∧ gprVal rs rs2 = rget cid m rs2)
      (fun HCC => ⟨HCC, Hrel HCC rs2⟩))
    iexact HC

end csdsp

end rowleaves

end Weak
