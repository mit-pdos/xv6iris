/-
Weak: **the lock protocol STORE rules (and the AMO rule) at a CONCRETE protocol instance, JOINTLY
(`rlRulesJoint`), with a REAL cross-hart hand-off of the lock's protected resource** (AxSL tier).

Rocq: `iris/AxRelease3.v` @ xxvzwolszwmp.

## The Rocq header, in substance

CHOICE OF INSTANCE.  `AxProtLock''`'s lock protocol is BYTE-level (one byte, values b0/b1, flow
equations baked to hand-built rows, the write touches ONLY the lock byte) — xv6's `sw zero,0(s1)` /
`amoswap.w` are 4-byte and `sd zero,16(s1)` 8-byte, so its rules cannot be stated for them; the
ledger (`AxTokLedgerWp`) is per-byte but carries only ledger TOKENS, forces the full-gmo-prefix
handout and needs the class-pinned run for `tok_release`.  We take the ledger's STRUCTURE (a
phase-2 MAILBOX in the base state — annotations cannot cross harts: `lobp` is same-hart) at the
`axGA2` instance with the real lock policy `lockAxpol` (sPol = external rf-sources), and carry an
ARBITRARY protected `R` through a saved proposition `γb`:
  `Box s := if release ∈ s ∧ next-acquire ∉ s then ∃ P, γb ⤇□ P ∗ P`.
The graph `rlg` (machine-checked cat-consistent, `rlgCat`): hart 0 = genesis acquire
(amoswap.aq), sd lk->cpu, fence rw,w, sw.rel; hart 1 = amoswap.aq reading hart 0's release.
RESULTS: `feRel` (the release parks `R`), `feAcq1` (hart 1's acquire's flow equation DEPOSITS `R`
— the hand-off), `AxRelease3.feNeutral`; `dflowOFe` (flow equation + phase-1 output ⇒ `dflowO`);
`rlSdlkRule`, `rlSwlkRule`, `rlAmoRule` (AxCondM4's / AxCondM3's rule shapes, `i := 0`,
`dreg`/`damo` := `rlDreg`/`rlDamo`); `rlRulesJoint`: all three + the hand-off at ONE instance.
DESIGN WRINKLE: an `FstM` rule is POSITION-AGNOSTIC — `amoRule3`'s FstM must also cover the
RELEASE store's position (same word), and the swlk rule's the AMO's.  Hence `rlAmoRes` carries
the protected `R` (hart 0's acquire is the genesis acquire) so its k = 3 branch can park it; the
swlk rule's k = 0 branch is refuted by the data (`o4 ≠ z4`).
HONESTY: `rlLockFinisher := Out` (the caller pre-pays `Out`); `rlLocked`/`rlLockedPre` are a full
ghost_var (the sd's rule flips it in phase 1); the instance is pinned to ONE graph
(`gconstInterp` = `⌜GD = rlg⌝`).

## Deviations from Rocq

1. INSTANCES: Rocq's `Local Instance rl_axirisG := AxGA2 rlg (λ _, False) gname unit (λ γ _ _ s,
   Box s) γb` is the named `@[reducible] def rlAxirisG γb := axGA2 rlg GName Unit (fun _ _ _ s =>
   Box γb s) γb` (no text argument: Stage C, `AxTierA2` deviation 2); the global policy
   `lock_axpol` is `lockAxpol` (AxProtLock3 deviation 4).  Both are passed with `@` in every
   statement (`@flowEqDyn hlc GF _ (rlAxirisG γb) …`, `@FstM …`, `@dflowO …`,
   `@OutOfV …`).  `invGS_gen HasNoLc Σ` ↦ `[InvGS_gen hlc GF]` (any `hlc`), `axannotGS Σ` ↦
   `[AxannotGS GF]` (its saved-prop camera serves `γb`), `ghost_varG Σ (CPU * bool)` ↦
   `[GhostVarG GF (CPU × Bool)]` (only on the declarations that use it).  The section variable
   `γb` is an explicit leading argument where Rocq's section discharge includes it.
2. VOCABULARY: `mword 64` ↦ `BitVec 64` / `PAddr`, `mword 32` ↦ `BitVec 32`, `bv 8` ↦ `BitVec 8`,
   `uint` ↦ `paZ`, `B0`/`B1` (`WeakLitmus.b0/b1`) ↦ `0#8`/`1#8`, `zero_reg` ↦ `0#64`,
   `st_bytes` ↦ `stBytes` (AxDataX2), `wrb` ↦ `AxDataX.wrb`, `bool_decide` ↦ `if … then … else`,
   `saved_prop_own γ DfracDiscarded P` ↦ `saved_prop_own γ DFrac.discard P`, `ghost_var γ 1 a` ↦
   `ghost_var γ (DFrac.own 1) a`, `coPset` ↦ `CoPset`.  `L0 := mword_of_int 0` ↦ `0#64`.
3. `lock_cpu` (Rocq `WpLock`, an SC file with no Lean counterpart of that name) is the Lean-only
   `AxRelease3.lockCpu lk := lk + 16#64` (the Lean SC tree's spelling of `lk->cpu`, MachCSL.Lock).
4. `iProp` statements are `⊢ … -∗ …`; `⊣⊢` lemmas are proved by `⟨.rfl, .rfl⟩`.  Rocq's
   notations `e_rel`/`e_acq0`/`e_acq1` are `abbrev`s.  The Ltac `neq` is replaced by `decide`.

**Rocq → Lean name map.**  `z4` `AxRelease3.z4`, `o4` `AxRelease3.o4` (duplicated names), `z8`
`z8`, `rlg` `rlg`, `rlg_cat` `rlgCat`, `e_rel` `AxRelease3.eRel`, `e_acq0` `AxRelease3.eAcq0`,
`e_acq1` `AxRelease3.eAcq1`, `rlg_pol_acq1` `rlgPolAcq1`, `L0` `L0`, `uint_L0` `uintL0`,
`uint_lkcpu_L0` `uintLkcpuL0`, `st4_zero` `st4Zero`, `o4_ne_z4` `o4NeZ4`, `rl_dreg` `rlDreg`,
`rl_damo` `rlDamo`, `rlg_row_wr0` `rlgRowWr0`, `Box` `Box`, `rl_axirisG` `rlAxirisG`, `rl_ob`
`rlOb`, `rl_gconst` `rlGconst`, `dflowO_fe` `dflowOFe`, `box_ext` `boxExt`, `fe_neutral`
`AxRelease3.feNeutral` (duplicated name), `fe_rel` `feRel`, `fe_acq1` `feAcq1`, `rl_locked`
`rlLocked`, `rl_locked_pre` `rlLockedPre`, `rl_lock_openable` `rlLockOpenable`,
`rl_lock_openable_pers` `rlLockOpenablePers`, `rl_lock_finisher` `rlLockFinisher`, `rl_amo_res`
`rlAmoRes`, `gd00` `gd00`, `gv00` `gv00`, `gv03` `gv03`, `rl_sdlk_rule` `rlSdlkRule`,
`rl_swlk_rule` `rlSwlkRule`, `rl_amo_rule` `rlAmoRule`, `rl_rules_joint` `rlRulesJoint`.
Lean-only (file-qualified): `AxRelease3.lockCpu` (deviation 3).

**Dropped:** nothing (Rocq 39 definitions/lemmas/notations/instances; Lean 39 + 1).  **Not
ported:** the Ltac `neq`, the local notations `B0`/`B1` (inlined) and the `Print Assumptions`
line (the lint's axiom check covers it).
-/
import Weak.AxCondM3
import Weak.AxProtLock3
import Weak.AxDataX2
import Weak.AxGraphDec
import Weak.AxViol
import Weak.AxLockWp

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std Iris.Std.PartialMap MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D LeanRV64D.Functions

/-! # 1. THE GRAPH

Lock word at 0 (4 bytes), lk->cpu at 16 (8 bytes).
H0: (0,0) amoswap.w.aq 0 ← 1 reading the GENESIS 0; (0,1) sd zero, 16; (0,2) fence rw,w;
(0,3) sw zero, 0 RELEASE-class.  H1: (1,0) amoswap.w.aq 0 ← 1 reading H0's release.
gmo = [(0,0); (0,1); (0,3); (1,0)]. -/

def AxRelease3.z4 : List (BitVec 8) := [0#8, 0#8, 0#8, 0#8]
def AxRelease3.o4 : List (BitVec 8) := [1#8, 0#8, 0#8, 0#8]
def z8 : List (BitVec 8) := [0#8, 0#8, 0#8, 0#8, 0#8, 0#8, 0#8, 0#8]

def rlg : Gdexec :=
  ⟨⟨vimg,
    [[.LRmw true false 0 [0, 0, 0, 0] AxRelease3.z4 AxRelease3.o4 .WCexcl,
      .LStore false 16 z8 .WCplain,
      .LFence true true false true,
      .LStore false 0 AxRelease3.z4 .WCrel],
     [.LRmw true false 0 [3, 3, 3, 3] AxRelease3.z4 AxRelease3.o4 .WCexcl]],
    [(0, 0), (0, 1), (0, 3), (1, 0)]⟩, []⟩

theorem rlgCat : rvwmoCatConsistent rlg := catConsistentBSound _ (by decide +kernel)

abbrev AxRelease3.eRel : Geid := (0, 3)
abbrev AxRelease3.eAcq0 : Geid := (0, 0)
abbrev AxRelease3.eAcq1 : Geid := (1, 0)

theorem rlgPolAcq1 : AxRelease3.eRel ∈ lockPolS rlg AxRelease3.eAcq1 :=
  LawfulSet.mem_ofList.1 (by decide +kernel)

def L0 : BitVec 64 := 0#64

/-- Lean-only: Rocq `WpLock.lock_cpu` (`lk->cpu`, the owner word at `lk + 16`). -/
def AxRelease3.lockCpu (lk : BitVec 64) : BitVec 64 := lk + 16#64

theorem uintL0 : paZ L0 = 0 := by decide +kernel
theorem uintLkcpuL0 : paZ (AxRelease3.lockCpu L0) = 16 := by decide +kernel
theorem st4Zero : stBytes 4 0#64 = AxRelease3.z4 := by decide +kernel
theorem o4NeZ4 : AxRelease3.o4 ≠ AxRelease3.z4 := by decide

/-- The data regions of the instance. -/
def rlDreg (a : Int) (n : Nat) : Prop := (a = 0 ∧ n = 4) ∨ (a = 16 ∧ n = 8)
def rlDamo (a : Int) (n : Nat) : Prop := a = 0 ∧ n = 4

/-- The row positions of hart 0 that write at `base`. -/
theorem rlgRowWr0 (k : Nat) (base : Int) (n0 : Nat) :
    (∃ lb rl, (AxOpsem.grow rlg 0)[k]? = some lb ∧ aidentWr (aident lb) = some (rl, base, n0)) →
    (k = 0 ∧ base = 0 ∧ n0 = 4) ∨ (k = 1 ∧ base = 16 ∧ n0 = 8) ∨ (k = 3 ∧ base = 0 ∧ n0 = 4) := by
  rintro ⟨lb, rl, Hlb, Hid⟩
  have hrow : AxOpsem.grow rlg 0 =
      [.LRmw true false 0 [0, 0, 0, 0] AxRelease3.z4 AxRelease3.o4 .WCexcl,
       .LStore false 16 z8 .WCplain,
       .LFence true true false true,
       .LStore false 0 AxRelease3.z4 .WCrel] := rfl
  rw [hrow] at Hlb
  rcases k with _ | _ | _ | _ | k
  · cases Hlb
    simp only [aident, aidentWr, Option.some.injEq, Prod.mk.injEq] at Hid
    obtain ⟨_, rfl, rfl⟩ := Hid
    exact .inl ⟨rfl, rfl, rfl⟩
  · cases Hlb
    simp only [aident, aidentWr, Option.some.injEq, Prod.mk.injEq] at Hid
    obtain ⟨_, rfl, rfl⟩ := Hid
    exact .inr (.inl ⟨rfl, rfl, rfl⟩)
  · cases Hlb
    simp [aident, aidentWr] at Hid
  · cases Hlb
    simp only [aident, aidentWr, Option.some.injEq, Prod.mk.injEq] at Hid
    obtain ⟨_, rfl, rfl⟩ := Hid
    exact .inr (.inr ⟨rfl, rfl, rfl⟩)
  · simp at Hlb

theorem gd00 : graphData rlg (0, 0) = some AxRelease3.o4 := rfl
theorem gv00 : graphValue rlg (0, 0) = some AxRelease3.z4 := rfl
theorem gv03 : graphValue rlg (0, 3) = none := rfl

/-! # 2. THE PROTOCOL STATE: a MAILBOX, and the flow equations -/

section inst
variable {hlc : HasLC} {GF : BundledGFunctors.{0,0,0}} [InvGS_gen hlc GF] [AxannotGS GF]
variable (γb : GName)

/-- Between the release's and the acquire's validation, the lock's protected resource `P`
(named by the saved proposition `γb`) is parked in the phase-2 state. -/
def Box (s : GSet Geid) : IProp GF :=
  if AxRelease3.eRel ∈ s ∧ AxRelease3.eAcq1 ∉ s then
    iprop(∃ P : IProp GF, saved_prop_own γb DFrac.discard P ∗ P)
  else iprop(True)

/-- Rocq's `Local Instance rl_axirisG` (deviation 1). -/
@[reducible] def rlAxirisG : AxirisG GF :=
  axGA2 rlg GName Unit (fun _ _ _ s => Box γb s) γb

theorem rlOb (GD : Gdexec) (σ : Unit) (s : GSet Geid) :
    @AxirisG.obStInterp GF (rlAxirisG γb) GD σ s ⊣⊢ Box (GF := GF) γb s := ⟨.rfl, .rfl⟩

theorem rlGconst (GD : Gdexec) :
    @AxirisG.gconstInterp GF (rlAxirisG γb) GD ⊣⊢ iprop(⌜GD = rlg⌝) := ⟨.rfl, .rfl⟩

/-- A flow equation + an output ⇒ the data event's `dflowO` (deposit `R` allocated at the event,
nothing pulled). -/
theorem dflowOFe (i k : Nat) (O R : IProp GF) :
    ⊢ @flowEqDyn hlc GF _ (rlAxirisG γb) rlg (i, k)
        (@Axpol.sPol lockAxpol rlg (i, k)) ∅ R -∗
      (|==> O) -∗ @dflowO hlc GF _ (rlAxirisG γb) lockAxpol i rlg k O := by
  iintro Hfe HO
  unfold dflowO
  iintro %na ⟨Hpg, Hannot⟩
  ihave %Hnin := naAtProgressNotElemOf rlg i k na $$ Hpg
  imod HO
  imod annotAlloc na (i, k) R Hnin $$ Hannot with ⟨Hannot, -⟩
  imodintro
  inext
  imodintro
  iexists R, (∅ : Mea GF), (∅ : Mea GF), (() : Unit)
  isplitr
  · unfold naSplittingWf
    isplitr
    · ipureintro
      rw [domEmpty]
      exact LawfulSet.empty_subset
    · iapply (BigSepM2.bigSepM2_empty _).2
      itrivial
  isplitl [Hfe]
  · iexact Hfe
  isplitl [Hannot]
  · rw [AxLockWp.annotInsertEq na (i, k) R]
    iexact Hannot
  isplitr
  · iapply (show ⊢ @AxirisG.localInterp GF (rlAxirisG γb) rlg i (k + 1) () from
      (show ⊢ iprop(True) by itrivial))
  · iexact HO

theorem boxExt (s1 s2 : GSet Geid) :
    (AxRelease3.eRel ∈ s1 ↔ AxRelease3.eRel ∈ s2) →
    (AxRelease3.eAcq1 ∈ s1 ↔ AxRelease3.eAcq1 ∈ s2) → Box (GF := GF) γb s1 ⊣⊢ Box γb s2 := by
  intro H1 H2
  unfold Box
  by_cases h : AxRelease3.eRel ∈ s1 ∧ AxRelease3.eAcq1 ∉ s1
  · have h' : AxRelease3.eRel ∈ s2 ∧ AxRelease3.eAcq1 ∉ s2 :=
      ⟨H1.1 h.1, fun hh => h.2 (H2.2 hh)⟩
    rw [if_pos h, if_pos h']
    exact ⟨.rfl, .rfl⟩
  · have h' : ¬ (AxRelease3.eRel ∈ s2 ∧ AxRelease3.eAcq1 ∉ s2) :=
      fun hh => h ⟨H1.2 hh.1, fun x => hh.2 (H2.1 x)⟩
    rw [if_neg h, if_neg h']
    exact ⟨.rfl, .rfl⟩

/-- An event that is neither the release nor the second acquire leaves the mailbox alone. -/
theorem AxRelease3.feNeutral (e : Geid) (s0 : GSet Geid) :
    e ≠ AxRelease3.eRel → e ≠ AxRelease3.eAcq1 →
    ⊢ @flowEqDyn hlc GF _ (rlAxirisG γb) rlg e s0 ∅ iprop(True) := by
  intro Hr Ha
  unfold flowEqDyn
  iintro %σ %s %_ %_ Hob _
  ihave Hob := (rlOb γb rlg σ s).1 $$ Hob
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro Hclose
  inext
  imod Hclose
  imodintro
  iexists σ
  isplitl [Hob]
  · iapply (rlOb γb rlg σ (({e} : GSet Geid) ∪ s)).2
    iapply (boxExt γb (({e} : GSet Geid) ∪ s) s
      ⟨fun h => (elemOfUnion.1 h).resolve_left (fun h' => Hr (elemOfSingleton.1 h').symm),
        elemOfUnionR⟩
      ⟨fun h => (elemOfUnion.1 h).resolve_left (fun h' => Ha (elemOfSingleton.1 h').symm),
        elemOfUnionR⟩).2
    iexact Hob
  · itrivial

/-- THE RELEASE parks `R` in the mailbox. -/
theorem feRel (s0 : GSet Geid) (R : IProp GF) :
    ⊢ saved_prop_own γb DFrac.discard R -∗ R -∗
      @flowEqDyn hlc GF _ (rlAxirisG γb) rlg AxRelease3.eRel s0 ∅ iprop(True) := by
  iintro #Hsv HR
  unfold flowEqDyn
  iintro %σ %s %_ %_ _ _
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro Hclose
  inext
  imod Hclose
  imodintro
  iexists σ
  isplitl [HR]
  · iapply (rlOb γb rlg σ (({AxRelease3.eRel} : GSet Geid) ∪ s)).2
    unfold Box
    by_cases hc : AxRelease3.eRel ∈ (({AxRelease3.eRel} : GSet Geid) ∪ s) ∧
        AxRelease3.eAcq1 ∉ (({AxRelease3.eRel} : GSet Geid) ∪ s)
    · rw [if_pos hc]
      iexists R
      isplitr
      · iexact Hsv
      · iexact HR
    · rw [if_neg hc]
      itrivial
  · itrivial

/-- THE SECOND ACQUIRE (hart 1, reading the release) takes `R` out of the mailbox: its flow
equation's deposit — hart 1's annotation at `eAcq1` — IS `R`.  The cross-hart hand-off. -/
theorem feAcq1 (R : IProp GF) :
    ⊢ saved_prop_own γb DFrac.discard R -∗
      @flowEqDyn hlc GF _ (rlAxirisG γb) rlg AxRelease3.eAcq1
        (lockPolS rlg AxRelease3.eAcq1) ∅ R := by
  iintro #Hsv
  unfold flowEqDyn
  iintro %σ %s %Hsub %Hnin Hob _
  have Hin : AxRelease3.eRel ∈ s := Hsub _ rlgPolAcq1
  have hb : Box γb s ⊢ iprop(∃ P : IProp GF, saved_prop_own γb DFrac.discard P ∗ P) := by
    unfold Box
    split
    · exact .rfl
    · rename_i hn
      exact (hn ⟨Hin, Hnin⟩).elim
  ihave Hob := (rlOb γb rlg σ s).1 $$ Hob
  ihave Hob := hb $$ Hob
  icases Hob with ⟨%P, #HsP, HP⟩
  ihave #Heq := AxWp.savedPropAgreeW γb _ _ P R $$ HsP Hsv
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro Hclose
  inext
  imod Hclose
  imodintro
  iexists σ
  isplitr
  · iapply (rlOb γb rlg σ (({AxRelease3.eAcq1} : GSet Geid) ∪ s)).2
    unfold Box
    rw [if_neg (fun h => h.2 (elemOfUnionL (elemOfSingleton.2 rfl)))]
    itrivial
  · ihave #Hw := AxWp.eqWand P R $$ Heq
    iapply Hw $$ HP

/-! # 3. THE LOCK RESOURCES of the instance -/

def rlLockOpenable (γ : GName) (lk : BitVec 64) (R _D : IProp GF) : IProp GF :=
  iprop(⌜lk = L0 ∧ γ = γb⌝ ∗ saved_prop_own γb DFrac.discard R)

instance rlLockOpenablePers (γ : GName) (lk : BitVec 64) (R D : IProp GF) :
    Persistent (rlLockOpenable γb γ lk R D) := by
  unfold rlLockOpenable
  infer_instance

def rlLockFinisher (_γ : GName) (_lk : BitVec 64) (_R _D Out : IProp GF) (_E : CoPset) :
    IProp GF := Out

/-- The AMO's resource: the lock's resource `R` (hart 0's acquire is the GENESIS acquire: the
initial owner) and what the acquirer makes of it. -/
def rlAmoRes (pa : PAddr) (_wnew : BitVec 32) (Post : BitVec 32 → IProp GF) : IProp GF :=
  iprop(⌜pa = L0⌝ ∗ ∃ R : IProp GF, saved_prop_own γb DFrac.discard R ∗ R ∗
    (R -∗ Post (rrv 4 AxRelease3.z4)))

/-- amo_rule3 (the acquire's amoswap): the output at the event's OWN read value (the genesis 0
here). -/
theorem rlAmoRule (pa : PAddr) (wnew : BitVec 32) (Post : BitVec 32 → IProp GF) :
    ⊢ rlAmoRes γb pa wnew Post -∗ ⌜rlDamo (paZ pa) 4⌝ ∗
      @FstM hlc GF _ (rlAxirisG γb) lockAxpol rvwmoCatConsistent (dk3 (paZ pa) 4) 0
        (@OutOfV GF (rlAxirisG γb) 0 (fun _ ov data =>
          iprop(⌜data = AxDataX.wrb 4 wnew⌝ -∗ ∀ rvs, ⌜ov = some rvs⌝ -∗ Post (rrv 4 rvs)))) := by
  unfold rlAmoRes
  iintro ⟨%Hpa, %R, #Hsv, HR, HP⟩
  subst Hpa
  rw [uintL0]
  isplitr
  · ipureintro
    exact ⟨rfl, rfl⟩
  unfold FstM
  iintro %GD %ls %k %data %base %n %_ #Hg _ %_ %Hd
  ihave %Heq := (rlGconst γb GD).1 $$ Hg
  subst Heq
  obtain ⟨⟨rfl, rfl⟩, Hrw⟩ := Hd
  rcases rlgRowWr0 _ _ _ Hrw with ⟨rfl, _, _⟩ | ⟨_, h, _⟩ | ⟨rfl, _, _⟩
  · ihave Hfe := AxRelease3.feNeutral (hlc := hlc) γb (0, 0) (@Axpol.sPol lockAxpol rlg (0, 0))
      (by decide) (by decide)
    iapply (dflowOFe γb 0 0 _ iprop(True)) $$ Hfe
    imodintro
    unfold OutOfV
    iexists rlg
    isplitr
    · ipureintro
      exact rlgCat
    isplitr
    · iexact Hg
    rw [gv00]
    iintro _ %rvs %Hrv
    obtain rfl := Option.some.inj Hrv
    iapply HP $$ HR
  · exact absurd h (by decide)
  · ihave Hfe := feRel (hlc := hlc) γb (@Axpol.sPol lockAxpol rlg (0, 3)) R $$ Hsv HR
    iapply (dflowOFe γb 0 3 _ iprop(True)) $$ Hfe
    imodintro
    unfold OutOfV
    iexists rlg
    isplitr
    · ipureintro
      exact rlgCat
    isplitr
    · iexact Hg
    rw [gv03]
    iintro _ %rvs %Habs
    cases Habs

section ghost
variable [GhostVarG GF (CPU × Bool)]

def rlLocked (γ : GName) (c : CPU) : IProp GF := ghost_var γ (DFrac.own 1) (c, true)
def rlLockedPre (γ : GName) (c : CPU) : IProp GF := ghost_var γ (DFrac.own 1) (c, false)

/-- sdlk_rule (sd zero, lk->cpu): the owner's plain store; locked ⇒ locked_pre (a phase-1 ghost
update), the mailbox untouched. -/
theorem rlSdlkRule (h0 : CPU) (_c : WmClass) (γl : GName) (lk : BitVec 64) (R Dc : IProp GF)
    (Pd : List (BitVec 8) → Prop) :
    (∀ data, Pd data → data = stBytes 8 0#64) →
    ⊢ rlLockOpenable γb γl lk R Dc -∗ rlLocked γl h0 -∗
      ⌜rlDreg (paZ (AxRelease3.lockCpu lk)) 8⌝ ∗
      @FstM hlc GF _ (rlAxirisG γb) lockAxpol rvwmoCatConsistent
        (dk3 (paZ (AxRelease3.lockCpu lk)) 8) 0
        (fun _ data => iprop(⌜Pd data⌝ -∗ rlLockedPre γl h0)) := by
  intro _
  unfold rlLockOpenable rlLocked rlLockedPre
  iintro ⟨%Hlk, -⟩ Hl
  obtain ⟨rfl, -⟩ := Hlk
  rw [uintLkcpuL0]
  isplitr
  · ipureintro
    exact .inr ⟨rfl, rfl⟩
  unfold FstM
  iintro %GD %ls %k %data %base %n %_ #Hg _ %_ %Hd
  ihave %Heq := (rlGconst γb GD).1 $$ Hg
  subst Heq
  obtain ⟨⟨rfl, rfl⟩, Hrw⟩ := Hd
  rcases rlgRowWr0 _ _ _ Hrw with ⟨_, h, _⟩ | ⟨rfl, _, _⟩ | ⟨_, h, _⟩
  · exact absurd h (by decide)
  · ihave Hfe := AxRelease3.feNeutral (hlc := hlc) γb (0, 1) (@Axpol.sPol lockAxpol rlg (0, 1))
      (by decide) (by decide)
    iapply (dflowOFe γb 0 1 _ iprop(True)) $$ Hfe
    imod ghost_var_update (h0, false) γl (h0, true) $$ Hl with Hl
    imodintro
    iintro _
    iexact Hl
  · exact absurd h (by decide)

/-- swlk_rule (THE RELEASE STORE, class WCrel): the protected `R` is PARKED in the mailbox by
the release's flow equation (`feRel`), where hart 1's acquire takes it (`feAcq1`); the
finisher's `Out` returns to the releaser. -/
theorem rlSwlkRule (h0 : CPU) (c : WmClass) (γl : GName) (lk : BitVec 64)
    (R Dc Out : IProp GF) (E : CoPset) (Pd : List (BitVec 8) → Prop) :
    (∀ data, Pd data → data = stBytes 4 0#64) → c = .WCrel →
    ⊢ rlLockOpenable γb γl lk R Dc -∗ rlLockedPre γl h0 -∗ R -∗
      rlLockFinisher γl lk R Dc Out E -∗
      ⌜rlDreg (paZ lk) 4⌝ ∗
      @FstM hlc GF _ (rlAxirisG γb) lockAxpol rvwmoCatConsistent (dk3 (paZ lk) 4) 0
        (fun _ data => iprop(⌜Pd data⌝ -∗ Out)) := by
  intro HPd _
  unfold rlLockOpenable rlLockFinisher
  iintro ⟨%Hlk, #Hsv⟩ _ HR Hfin
  obtain ⟨rfl, -⟩ := Hlk
  rw [uintL0]
  isplitr
  · ipureintro
    exact .inl ⟨rfl, rfl⟩
  unfold FstM
  iintro %GD %ls %k %data %base %n %_ #Hg _ %Hgd %Hd
  ihave %Heq := (rlGconst γb GD).1 $$ Hg
  subst Heq
  obtain ⟨⟨rfl, rfl⟩, Hrw⟩ := Hd
  rcases rlgRowWr0 _ _ _ Hrw with ⟨rfl, _, _⟩ | ⟨_, h, _⟩ | ⟨rfl, _, _⟩
  · rw [gd00] at Hgd
    obtain rfl := Option.some.inj Hgd
    ihave Hfe := AxRelease3.feNeutral (hlc := hlc) γb (0, 0) (@Axpol.sPol lockAxpol rlg (0, 0))
      (by decide) (by decide)
    iapply (dflowOFe γb 0 0 _ iprop(True)) $$ Hfe
    imodintro
    iintro %HP
    have h := HPd _ HP
    rw [st4Zero] at h
    exact (o4NeZ4 h).elim
  · exact absurd h (by decide)
  · ihave Hfe := feRel (hlc := hlc) γb (@Axpol.sPol lockAxpol rlg (0, 3)) R $$ Hsv HR
    iapply (dflowOFe γb 0 3 _ iprop(True)) $$ Hfe
    imodintro
    iintro _
    iexact Hfin

/-- JOINT SATISFIABILITY: the three rules hold TOGETHER at ONE instance (ONE `AxirisG` =
`rlAxirisG γb`, ONE policy `lockAxpol`, ONE set of lock resources) — and the release's deposit
reaches the next acquirer (`feAcq1`). -/
theorem rlRulesJoint :
    (∀ (h0 : CPU) (c : WmClass) (γl : GName) (lk : BitVec 64) (R Dc : IProp GF)
        (Pd : List (BitVec 8) → Prop), (∀ data, Pd data → data = stBytes 8 0#64) →
      ⊢ rlLockOpenable γb γl lk R Dc -∗ rlLocked γl h0 -∗
        ⌜rlDreg (paZ (AxRelease3.lockCpu lk)) 8⌝ ∗
        @FstM hlc GF _ (rlAxirisG γb) lockAxpol rvwmoCatConsistent
          (dk3 (paZ (AxRelease3.lockCpu lk)) 8) 0
          (fun _ data => iprop(⌜Pd data⌝ -∗ rlLockedPre γl h0))) ∧
    (∀ (h0 : CPU) (c : WmClass) (γl : GName) (lk : BitVec 64) (R Dc Out : IProp GF)
        (E : CoPset) (Pd : List (BitVec 8) → Prop),
      (∀ data, Pd data → data = stBytes 4 0#64) → c = .WCrel →
      ⊢ rlLockOpenable γb γl lk R Dc -∗ rlLockedPre γl h0 -∗ R -∗
        rlLockFinisher γl lk R Dc Out E -∗
        ⌜rlDreg (paZ lk) 4⌝ ∗
        @FstM hlc GF _ (rlAxirisG γb) lockAxpol rvwmoCatConsistent (dk3 (paZ lk) 4) 0
          (fun _ data => iprop(⌜Pd data⌝ -∗ Out))) ∧
    (∀ (pa : PAddr) (wnew : BitVec 32) (Post : BitVec 32 → IProp GF),
      ⊢ rlAmoRes γb pa wnew Post -∗ ⌜rlDamo (paZ pa) 4⌝ ∗
        @FstM hlc GF _ (rlAxirisG γb) lockAxpol rvwmoCatConsistent (dk3 (paZ pa) 4) 0
          (@OutOfV GF (rlAxirisG γb) 0 (fun _ ov data =>
            iprop(⌜data = AxDataX.wrb 4 wnew⌝ -∗ ∀ rvs, ⌜ov = some rvs⌝ -∗
              Post (rrv 4 rvs))))) ∧
    (∀ R : IProp GF, ⊢ saved_prop_own γb DFrac.discard R -∗
      @flowEqDyn hlc GF _ (rlAxirisG γb) rlg AxRelease3.eAcq1
        (@Axpol.sPol lockAxpol rlg AxRelease3.eAcq1) ∅ R) :=
  ⟨fun h0 c γl lk R Dc Pd H => rlSdlkRule γb h0 c γl lk R Dc Pd H,
   fun h0 c γl lk R Dc Out E Pd H Hc => rlSwlkRule γb h0 c γl lk R Dc Out E Pd H Hc,
   fun pa wnew Post => rlAmoRule γb pa wnew Post,
   fun R => feAcq1 γb R⟩

end ghost

end inst

end Weak
