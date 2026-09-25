/-
**THE PROCESS'S LIVE CHILDREN, AS A RESOURCE, AND WHAT A WAIT ANSWERS** -- a
port of Rocq `UserChildren.v` (`/shared/xv6rocq/iris/UserChildren.v`, 510
lines), wave 7 decision D8 (the definitional layer of the fork/exit
generation machinery).

## Rocq's header, in short (every clause is kept)

The key a user process is resumed at carries the GENERATIONS of its live
children (Rocq `UexecSlot.uvis_ch`), bound existentially by the run.  A
program that DOES care -- one whose wait(2) has to know that the child it is
waiting for is still its child -- needs a carrier for "my children are
exactly S": one ghost variable split in half (`uchAuth` the ENGINE's half,
`uch` the PROGRAM's), the shape of `UserCwd` at a set.  The same at a pid
(`upidAuth` / `upid`), which is what makes a caller able to NAME its own pid.

Then the two answers a wait gives, relayed from kwait to the program:

* `waitAns` -- IT FAILED (`-1`, the children reading does not move, and the
  REASON: a non-null status pointer, an empty column, or the kill shot), or
  IT REAPED: the reaped generation leaves the reading, the ESCROW
  (`ChildTok.exitTok`) at the zombie's status rides with it, and PID
  UNIQUENESS over the caller's reading (`ChildTok.genUniq`).  The arms are
  disjoint AT THE RETURN VALUE (`sext32_rng_not_neg1`).
* `waitAnsGen` -- the same at the GENERATION, kwait's own form; the step
  across is `waitAns_of_gen`, taken once at kwait's exit.

## Deviations from Rocq

1. **The two U-tier ghost-variable cameras are SECTION HYPOTHESES** (as in
   Rocq, `Context ghost_varG Σ (gset gname)` / `ghost_varG Σ Z`), not class
   fields.  In Lean `GName = Nat`, so `GhostVarG GF (ExtTreeSet GName
   compare)` IS `IcacheG.poolG`'s type, and `GhostVarG GF Int` IS
   `OffboxG.offG`'s: the one-instance rule forbids a second provider.
   Whoever instantiates these sections (the U tier, not yet ported) must
   take the one instance -- which, by the rule, means hoisting both into
   `Xv6G`.  Reported.
2. `gset gname` is `ExtTreeSet GName compare`; `cs ∖ {[γ']}` is
   `cs \ {γ'}`; `sign_extend' 64 w` is `BitVec.signExtend 64 w` (the form
   `SpecKwait` states a0 at); `mword_of_int (-1)` is `-1#32` / `-1#64`;
   `PIDMAX` is `SlotGen.genPidMax` (SlotGen deviation 3); `Z` is `Int`.

Imports only definitional files.
-/
import Xv6.SlotGen

namespace Xv6

open Iris Iris.BI Iris.ProofMode Iris.Std Std MachCSL

set_option linter.unusedSectionVars false

/-! ## The children set, as a resource (Rocq `Section UserChildren`) -/

section UserChildren
variable {GF : BundledGFunctors} [GhostVarG GF (ExtTreeSet GName compare)]

/-- the ENGINE's half: the run carries it at the key's children reading -/
def uchAuth (γs : GName) (S : ExtTreeSet GName compare) : IProp GF :=
  ghost_var γs (.own (1 : Qp).half) S

/-- the PROGRAM's half -/
def uch (γs : GName) (S : ExtTreeSet GName compare) : IProp GF :=
  ghost_var γs (.own (1 : Qp).half) S

instance uchAuth_timeless (γs : GName) (S : ExtTreeSet GName compare) :
    Timeless (uchAuth (GF := GF) γs S) := by unfold uchAuth ghost_var; infer_instance
instance uch_timeless (γs : GName) (S : ExtTreeSet GName compare) :
    Timeless (uch (GF := GF) γs S) := by unfold uch ghost_var; infer_instance

/-- the fragment READS the engine's half -/
theorem uch_agree (γs : GName) (S S' : ExtTreeSet GName compare) :
    uchAuth (GF := GF) γs S ∗ uch γs S' ⊢ ⌜S = S'⌝ := by
  unfold uchAuth uch
  iintro ⟨H1, H2⟩
  iapply ghost_var_agree $$ H1 H2

/-- ...and BOTH halves move it: what fork, wait and exit spend -/
theorem uch_update (γs : GName) (S S' S'' : ExtTreeSet GName compare) :
    uchAuth (GF := GF) γs S ∗ uch γs S' ⊢ |==> (uchAuth γs S'' ∗ uch γs S'') := by
  unfold uchAuth uch
  iintro ⟨H1, H2⟩
  iapply ghost_var_update_halves S'' γs S S' $$ H1 H2

/-- the mint, at the set the key carries -/
theorem uch_alloc (S : ExtTreeSet GName compare) :
    ⊢@{IProp GF} |==> ∃ γs : GName, uchAuth γs S ∗ uch γs S := by
  imod ghost_var_alloc (GF := GF) S with ⟨%γs, Hc⟩
  imodintro
  iexists γs
  unfold uchAuth uch
  have H := ghost_var_split (GF := GF) γs S (1 : Qp).half (1 : Qp).half
  rw [Qp.half_add_half] at H
  iapply H $$ Hc

/-- A FRAGMENT AT A SET THE CARRIER IS NOT READING (Rocq `uch_any`). -/
def uchAny (γs : GName) : IProp GF := iprop(∃ S : ExtTreeSet GName compare, uch γs S)

instance uchAny_timeless (γs : GName) : Timeless (uchAny (GF := GF) γs) := by
  unfold uchAny; infer_instance

theorem uchAny_of (γs : GName) (S : ExtTreeSet GName compare) : uch (GF := GF) γs S ⊢ uchAny γs := by
  unfold uchAny
  iintro H
  iexists S
  iexact H

end UserChildren

/-! ## A running process's own pid, as a handle (Rocq `Section UserPid`)

OVER `Int` (Rocq `Z`) and the fragment is at the pid's value.  NO UPDATE
LAW: a process's pid never changes. -/

section UserPid
variable {GF : BundledGFunctors} [GhostVarG GF Int]

def upidAuth (γp : GName) (p : Int) : IProp GF := ghost_var γp (.own (1 : Qp).half) p

def upid (γp : GName) (p : Int) : IProp GF := ghost_var γp (.own (1 : Qp).half) p

instance upidAuth_timeless (γp : GName) (p : Int) : Timeless (upidAuth (GF := GF) γp p) := by
  unfold upidAuth ghost_var; infer_instance
instance upid_timeless (γp : GName) (p : Int) : Timeless (upid (GF := GF) γp p) := by
  unfold upid ghost_var; infer_instance

theorem upid_agree (γp : GName) (p p' : Int) : upidAuth (GF := GF) γp p ∗ upid γp p' ⊢ ⌜p = p'⌝ := by
  unfold upidAuth upid
  iintro ⟨H1, H2⟩
  iapply ghost_var_agree $$ H1 H2

theorem upid_alloc (p : Int) : ⊢@{IProp GF} |==> ∃ γp : GName, upidAuth γp p ∗ upid γp p := by
  imod ghost_var_alloc (GF := GF) p with ⟨%γp, Hc⟩
  imodintro
  iexists γp
  unfold upidAuth upid
  have H := ghost_var_split (GF := GF) γp p (1 : Qp).half (1 : Qp).half
  rw [Qp.half_add_half] at H
  iapply H $$ Hc

def upidAny (γp : GName) : IProp GF := iprop(∃ p : Int, upid γp p)

instance upidAny_timeless (γp : GName) : Timeless (upidAny (GF := GF) γp) := by
  unfold upidAny; infer_instance

theorem upidAny_of (γp : GName) (p : Int) : upid (GF := GF) γp p ⊢ upidAny γp := by
  unfold upidAny
  iintro H
  iexists p
  iexact H

end UserPid

/-! ## What a reap does to the reading (Rocq `ch_reaped`)

AT MOST ONE generation leaves it -- the one that was reaped -- and every
failing arm leaves it alone. -/

def chReaped (cs cs' : ExtTreeSet GName compare) : Prop :=
  cs' = cs ∨ ∃ γ' : GName, cs' = cs \ {γ'}

theorem chReaped_refl (cs : ExtTreeSet GName compare) : chReaped cs cs := Or.inl rfl

theorem chReaped_del (cs : ExtTreeSet GName compare) (γ' : GName) : chReaped cs (cs \ {γ'}) :=
  Or.inr ⟨γ', rfl⟩

/-- THE TWO ARMS ARE DISJOINT AT THE RETURN VALUE, as a pure fact about the
word: a pid in `[1, PIDMAX]` sign-extends to a small POSITIVE 64-bit word,
while a failing wait returns the all-ones one. -/
theorem sext32_rng_not_neg1 (w : BitVec 32) (h : 1 ≤ w.toNat ∧ w.toNat ≤ genPidMax) :
    BitVec.signExtend 64 w ≠ -1#64 := by
  unfold genPidMax at h
  have hle : w ≤ 1000#32 := by
    rw [BitVec.le_def]; simpa using h.2
  clear h
  bv_decide

/-! ## The caller is init, as a ghost (Rocq `Section GenIsInit`) -/

section GenIsInit
variable {GF : BundledGFunctors} [CtokG GF] [WchG GF]

/-- THE CALLER IS INIT, AT THE CALLER'S OWN GENERATION (Rocq
`gen_is_init`).  It is the kernel's own form and stops at kwait. -/
def genIsInit (g : GName) : IProp GF := iprop(∃ p0 : BitVec 32, initPidIs p0 ∗ genPid g p0)

instance genIsInit_persistent (g : GName) : Persistent (genIsInit (GF := GF) g) := by
  unfold genIsInit; infer_instance

/-- the pid form, for a caller that can name its own pid -/
theorem genIsInit_pid (g : GName) (pidv : BitVec 32) :
    genIsInit (GF := GF) g ∗ genPid g pidv ⊢ ∃ p0 : BitVec 32, initPidIs p0 ∗ ⌜pidv = p0⌝ := by
  unfold genIsInit
  iintro ⟨⟨%p0, #Hi, #Hp0⟩, #Hp⟩
  ihave %h := genPid_agree g pidv p0 $$ [Hp Hp0]
  · isplitl []
    · iexact Hp
    · iexact Hp0
  iexists p0
  isplitr
  · iexact Hi
  · ipureintro; exact h

/-- ...AND THE REFUTATION A FORKED CHILD SPENDS -/
theorem genIsInit_ne (g : GName) (pidv p0 : BitVec 32) (hne : pidv ≠ p0) :
    initPidIs (GF := GF) p0 ∗ genPid g pidv ∗ genIsInit g ⊢ False := by
  iintro ⟨#Hi, #Hp, #Hg⟩
  ihave ⟨%p1, #Hi1, %Heq⟩ := genIsInit_pid g pidv $$ [Hg Hp]
  · isplitl []
    · iexact Hg
    · iexact Hp
  ihave %h := initPidIs_agree p0 p1 $$ [Hi Hi1]
  · isplitl []
    · iexact Hi
    · iexact Hi1
  exact absurd (Heq.trans h.symm) hne

end GenIsInit

/-! ## What a wait answers (Rocq `Section WaitAns`) -/

section WaitAns
variable {GF : BundledGFunctors} [CtokG GF]

/-- THE REASON a wait failed, at a NULL status pointer (Rocq `wait_why`):
the pointer was not null (the guard, not a claim), or the caller's own
children column is empty, or the caller was killed.  Persistent. -/
def waitWhy (cs : ExtTreeSet GName compare) (gn : GName) (nullst : Bool) : IProp GF :=
  iprop(⌜nullst = false⌝ ∨ ⌜cs = ∅⌝ ∨ killShot gn)

instance waitWhy_persistent (cs : ExtTreeSet GName compare) (gn : GName) (b : Bool) :
    Persistent (waitWhy (GF := GF) cs gn b) := by
  unfold waitWhy; infer_instance

/-- Rocq `wait_ans`.  `pidv` is the CALLER'S OWN pid; init's is the LITERAL
1.  The reaping arm says the generation it took out was in the caller's own
column -- unless the caller IS init (the one process that reaps orphans). -/
def waitAns (rv : BitVec 32) (xs : Int) (cs cs' : ExtTreeSet GName compare) (gn : GName)
    (nullst : Bool) (pidv : BitVec 32) : IProp GF :=
  iprop((⌜rv = -1#32 ∧ cs' = cs⌝ ∗ waitWhy cs gn nullst) ∨
    ∃ γ' : GName,
      ⌜cs' = cs \ {γ'} ∧ 1 ≤ rv.toNat ∧ rv.toNat ≤ genPidMax⌝ ∗
      ⌜γ' ∈ cs ∨ pidv = 1#32⌝ ∗
      exitTok γ' rv xs ∗ genUniq cs rv γ')

/-- the pure row, which is all the relays between kwait and the program
ever look at -/
theorem waitAns_reaped (rv : BitVec 32) (xs : Int) (cs cs' : ExtTreeSet GName compare) (gn : GName)
    (nullst : Bool) (pidv : BitVec 32) :
    waitAns (GF := GF) rv xs cs cs' gn nullst pidv ⊢ ⌜chReaped cs cs'⌝ := by
  unfold waitAns
  iintro (⟨%h, -⟩ | ⟨%γ', %h, -, -, -⟩)
  · ipureintro; exact Or.inl h.2
  · ipureintro; exact Or.inr ⟨γ', h.1⟩

/-- ...AND THE ARM A -1 RETURN IS ON: the whole answer is persistent there. -/
theorem waitAns_m1 (rv : BitVec 32) (xs : Int) (cs cs' : ExtTreeSet GName compare) (gn : GName)
    (nullst : Bool) (pidv : BitVec 32) (hm1 : BitVec.signExtend 64 rv = -1#64) :
    waitAns (GF := GF) rv xs cs cs' gn nullst pidv ⊢
      ⌜rv = -1#32 ∧ cs' = cs⌝ ∗ waitWhy cs gn nullst := by
  unfold waitAns
  iintro (⟨%hf, #Hwhy⟩ | ⟨%γ', %h, -, -, -⟩)
  · isplitr
    · ipureintro; exact hf
    · iexact Hwhy
  · exact absurd hm1 (sext32_rng_not_neg1 rv h.2)

/-- the failing arm, for the three exits that reap nothing -/
theorem waitAns_neg (xs : Int) (cs : ExtTreeSet GName compare) (gn : GName) (nullst : Bool)
    (pidv : BitVec 32) :
    waitWhy (GF := GF) cs gn nullst ⊢ waitAns (-1#32) xs cs cs gn nullst pidv := by
  unfold waitAns
  iintro #Hwhy
  ileft
  isplitr
  · ipureintro; exact ⟨rfl, rfl⟩
  · iexact Hwhy

/-- ...and the three ways to build that reason -/
theorem waitWhy_notnull (cs : ExtTreeSet GName compare) (gn : GName) (nullst : Bool)
    (h : nullst = false) : ⊢@{IProp GF} waitWhy cs gn nullst := by
  unfold waitWhy
  ileft; ipureintro; exact h

theorem waitWhy_empty (cs : ExtTreeSet GName compare) (gn : GName) (nullst : Bool)
    (h : cs = ∅) : ⊢@{IProp GF} waitWhy cs gn nullst := by
  unfold waitWhy
  iright; ileft; ipureintro; exact h

theorem waitWhy_shot (cs : ExtTreeSet GName compare) (gn : GName) (nullst : Bool) :
    killShot (GF := GF) gn ⊢ waitWhy cs gn nullst := by
  unfold waitWhy
  iintro #H
  iright; iright; iexact H

end WaitAns

/-! ## The same answer, at the generation -- kwait's own form
(Rocq `Section WaitAnsGen`) -/

section WaitAnsGen
variable {GF : BundledGFunctors} [CtokG GF] [WchG GF]

/-- Rocq `wait_ans_gen`. -/
def waitAnsGen (rv : BitVec 32) (xs : Int) (cs cs' : ExtTreeSet GName compare) (gn : GName)
    (nullst : Bool) : IProp GF :=
  iprop((⌜rv = -1#32 ∧ cs' = cs⌝ ∗ waitWhy cs gn nullst) ∨
    ∃ γ' : GName,
      ⌜cs' = cs \ {γ'} ∧ 1 ≤ rv.toNat ∧ rv.toNat ≤ genPidMax⌝ ∗
      (⌜γ' ∈ cs⌝ ∨ genIsInit gn) ∗
      exitTok γ' rv xs ∗ genUniq cs rv γ')

theorem waitAnsGen_neg (xs : Int) (cs : ExtTreeSet GName compare) (gn : GName) (nullst : Bool) :
    waitWhy (GF := GF) cs gn nullst ⊢ waitAnsGen (-1#32) xs cs cs gn nullst := by
  unfold waitAnsGen
  iintro #Hwhy
  ileft
  isplitr
  · ipureintro; exact ⟨rfl, rfl⟩
  · iexact Hwhy

/-- THE ONE STEP ACROSS, and it is two agreements: the caller's own
registration says which pid its generation was given, and the sealed pid
says which pid init was given. -/
theorem waitAns_of_gen (rv : BitVec 32) (xs : Int) (cs cs' : ExtTreeSet GName compare) (gn : GName)
    (nullst : Bool) (pidme : BitVec 32) :
    genPid (GF := GF) gn pidme ∗ initPidIs 1#32 ∗ waitAnsGen rv xs cs cs' gn nullst ⊢
      waitAns rv xs cs cs' gn nullst pidme := by
  unfold waitAnsGen waitAns
  iintro ⟨#Hgp, #Hi, (Hneg | ⟨%γ', %Hrng, Hoci, Hesc, Huniq⟩)⟩
  · ileft; iexact Hneg
  · iright
    iexists γ'
    isplitr
    · ipureintro; exact Hrng
    isplitr [Hesc Huniq]
    · icases Hoci with (%Hin | #Hgi)
      · ipureintro; exact Or.inl Hin
      · ihave ⟨%p1, #Hi1, %Heq⟩ := genIsInit_pid gn pidme $$ [Hgi Hgp]
        · isplitl []
          · iexact Hgi
          · iexact Hgp
        ihave %h := initPidIs_agree 1#32 p1 $$ [Hi Hi1]
        · isplitl []
          · iexact Hi
          · iexact Hi1
        ipureintro; exact Or.inr (Heq.trans h.symm)
    isplitl [Hesc]
    · iexact Hesc
    · iexact Huniq

end WaitAnsGen

end Xv6
