/-
Weak: **UNIFY, part 2 of the spinlock plan -- the allocpid-SHAPED critical section at `Ixv6`,
verified ONLY with the handle surface of `AxSpinU`.**

Rocq: `iris/AxSpinU2.v` @ xxvzwolszwmp.

## The Rocq header, in substance

PROGRAM (hand `Pexv6` nodes at REAL widths, layout `Lx`; one per hart):
  k0  `amoswap.w.aq lk ← 1`  (`AxSpinX4.acq4`: the 4-byte claim; the spin's failure branch is
      `hlt` in this row)
  k1  `lw nextpid` (value `w8`); `addiw 1` (register-only: the continuation computes `w8 + one32`)
  k2  `sw nextpid ← w8 + 1`  (MINTS the issued fragment ◯{v})
  k3  `fence rw,w`
  k4  `sw lk ← 0`            (release, WCrel)
Row `uRow t ts w8`; run `uRun` (6 steps, row pinned).
WPd `wpdCs` (any hart `i`, any graph whose row for `i` is `uRow`, `Hnowrap`): written ONLY with
`wpdAcquireX` (claim annotation pre-split into `locked ∗ lk->cpu` and `RNp`), `wpdNpLwX`,
`wpdNpSwX`, `wpdReleaseX` (lk->cpu still at the claim, nextpid at the sw), and the row-end
readback `shHltReadbackP` (an iProp generalisation of `AxSpinProt7`'s `shHltReadbackM`).
POST `UPost nm G i w8` = `⌜npSrc G Lx (i,1) (i,0)⌝` (the lw read the image or a write gmo-before
the claim) `∗ FRAG nm w8` (the minted EXCLUSIVE ◯{v}, v's word = the read word, READ BACK).
`upost` is its pure shadow; `wpdCsPure` the WPd at the pure post (what adequacy consumes).
`upostJoint`: two harts' posts at ONE ghost name give DIFFERENT read words (issued-fragment
exclusivity) -- the JOINT step, not fed through adequacy here.

## Deviations from Rocq

1. VOCABULARY (as `AxSpinU` deviation 1): `Z` ↦ `Int`, `bv n` ↦ `BitVec n`, `gd_g GD` ↦
   `GD.gdG`, `l !! j` ↦ `l[j]?` (indices `Nat`), `Z_to_bv 32` ↦ `BitVec.ofInt 32`,
   `bv_add w8 one32` ↦ `w8 + one32`, `bv_unsigned w8 + 1 < 2^32` ↦ `w8.toNat + 1 < 2 ^ 32`,
   `0 ≤ v < 2^32` ↦ `0 ≤ v ∧ v < 2 ^ 32`, `a ≤ b < c` ↦ `a ≤ b ∧ b < c`, `B0`/`B1` ↦ `b0`/`b1`,
   `init_regstate` ↦ `zeroRegs`, `AThread p k` ↦ `⟨p, k⟩`, `M unit` ↦ `SailM Unit`, `dom m` ↦
   `FiniteMap.dom_set m`.  The hand programs are `abbrev`s (as `AxSpinX4`).
2. CONTEXTS (as `AxSpinU` deviation 2): Rocq section variables are explicit leading arguments in
   Rocq's order, only where Rocq's section mechanism includes them (§2 `GD N obSt0 obi nm`, then
   `cpu`; §4 `GT nm cpu`, then `Hcons i t ts w8 Hrow Hnowrap` as `Proof using` names them).
   `invGS_gen HasNoLc Σ` ↦ `[InvGS_gen hlc GF]` for any `hlc`; `axannotG Σ`+`axannotGS Σ` ↦
   `[AxannotGS GF]`; `xv6G Σ` ↦ `[AxSpinX.Xv6G GF]`.  The local instances `shUG`, `uw_pol`,
   `uw_G` are inlined (policy `pol` / `xv6Pol GT` and `AxSpinX2.xG Lx GT nm` passed explicitly).
   `u_run`'s unused `axirisG Σ` context is dropped.  O2 STAGE C: Rocq's `Tf` argument of
   `AxGA2`/`tierA_wpd` is gone.
3. STATEMENT SHAPES: wand chains ↦ `⊢ A -∗ B -∗ …`; the Rocq notations `TW`/`TWU`/`Φu`/`LK`/
   `NH`/`RP`/`RNP`/`RCPU`/`ISL`/`c0` are file-local Lean notations with the same expansions
   (`c0` written `(i, 0)`).  `wU5`/`wU3`'s `set (m := …)` are the Lean-only reducible maps
   `AxSpinU2.m5`/`AxSpinU2.m3`.  The `zv` Ltac is inlined as `simp only [lkZV, npZV]`.
4. PROOFS: Rocq `vm_compute` facts by `decide +kernel`; `upostJoint` derives `vA = vB` from
   `BitVec.toNat_ofInt` (Rocq: `Z_to_bv_unsigned` + `bv_wrap_small`).
5. The trailing `Print Assumptions` commands are not ported.

**Rocq → Lean name map.**  `u_end` `uEnd`, `u_rel` `uRel`, `u_inc` `uInc`, `u_np` `uNp`,
`u_m0` `uM0`, `u_row` `uRow`, `u_run` `uRun`, `z4_all` `z4All`, `o4_0` `o40`, `u_wr` `uWr`,
`sh_hlt_readbackP` `shHltReadbackP`, `UPost` `UPost`, `upost` `upost`, `UPost_pure`
`UPostPure`, `upost_joint` `upostJoint`, `uL` `uL`, `wU5` `wU5`, `wU3` `wU3`, `wU2` `wU2`,
`wU1` `wU1`, `wpd_cs` `wpdCs`, `wpd_cs_pure` `wpdCsPure`.  No duplicated Rocq names.
Lean-only (file-qualified): `AxSpinU2.m5`, `AxSpinU2.m3` (the readback / release maps).

**Dropped:** none (26 Rocq decls incl. the 3 local instances `shUG`/`uw_pol`/`uw_G` (inlined)
and the `zv` Ltac (inlined); 24 Lean = 22 + 2 Lean-only).

**W13 (I) (plan `notes/weak-allocproc-plan.md` §C W13 (I); [OWN.27]).** the release lemmas' anchor-domain premise is `(lbIsR l || lbIsW l) = true` (was `lbIsMem l = true`): `gwf` admits I/O events, which `fence rw,w` does not order (RVWMO; D48).
-/
import Weak.AxSpinU

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std Iris.Std.PartialMap MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D

/-! # 1. Program, row, run -/

abbrev uEnd : SailM Unit := stv 4 lkpa zero32 hlt
abbrev uRel : SailM Unit := fnc uEnd
abbrev uInc (v : BitVec 32) : SailM Unit := stv 4 nppa (v + one32) uRel
abbrev uNp : SailM Unit := ldk 4 nppa uInc
abbrev uM0 : SailM Unit := AxSpinX4.acq4 uNp hlt

def uRow (t : Nat) (ts : List Nat) (w8 : BitVec 32) : List Lbl :=
  [.LRmw true false (paZ lkpa) [t, t, t, t] AxSpinX4.z4 AxSpinX4.o4 .WCplain,
   .LLoad false (paZ nppa) ts (WeakInterpProj.wbytes 4 w8),
   .LStore false (paZ nppa) (WeakInterpProj.wbytes 4 (w8 + one32)) .WCplain,
   .LFence true true false true,
   .LStore false (paZ lkpa) AxSpinX4.z4 .WCrel]

theorem uRun (cpu : CPU) (GD : Gdexec) (i : Agent) (t : Nat) (ts : List Nat) (w8 : BitVec 32)
    (Hrow : AxOpsem.grow GD i = uRow t ts w8) :
    nsteps (astepAnyNfGv GD i) 6 ⟨hp cpu uM0 zeroRegs, 0⟩ ⟨hp cpu hlt zeroRegs, 5⟩ := by
  have H0 := nrunRmwRead cpu GD i 0 4 lkpa lkpaRam [t, t, t, t] AxSpinX4.z4 AxSpinX4.o4
    .WCplain (amoK uNp hlt) zeroRegs (by rw [Hrow]; rfl) (by decide +kernel) (by decide +kernel)
  rw [acqAfterClaim] at H0
  refine nsteps_l H0 ?_
  have H0' := nrunRmwWrite cpu GD i 0 4 (by decide) lkpa lkpaRam [t, t, t, t] AxSpinX4.z4
    one32 .WCplain (if zero32 = zero32 then uNp else hlt) zeroRegs (by rw [Hrow]; rfl)
  rw [amoClaimNext] at H0'
  refine nsteps_l H0' ?_
  refine nsteps_l (AxSpinX4.ldkRun cpu GD i 4 nppa nppaRam ts w8 uInc zeroRegs 1
    (by rw [Hrow]; rfl)) ?_
  refine nsteps_l (nrunWrite cpu GD i 4 (by decide) nppa nppaRam (w8 + one32) uRel zeroRegs 2
    .WCplain (by rw [Hrow]; rfl)) ?_
  refine nsteps_l (runFence cpu GD i 3 uEnd zeroRegs (by rw [Hrow]; rfl)) ?_
  refine nsteps_l (nrunWrite cpu GD i 4 (by decide) lkpa lkpaRam zero32 hlt zeroRegs 4 .WCrel
    (by rw [Hrow]; rfl)) ?_
  exact nsteps_O _

/-- The row's writes. -/
theorem z4All (j : Nat) (v : BitVec 8) : AxSpinX4.z4[j]? = some v → v = b0 := by
  intro H
  have Hj := (List.getElem?_eq_some_iff.1 H).1
  simp only [AxSpinX4.z4, wbytesLength] at Hj
  rcases j with _ | _ | _ | _ | j
  · have Hz : AxSpinX4.z4[0]? = some b0 := by decide +kernel
    rw [Hz] at H; exact (Option.some.inj H).symm
  · have Hz : AxSpinX4.z4[1]? = some b0 := by decide +kernel
    rw [Hz] at H; exact (Option.some.inj H).symm
  · have Hz : AxSpinX4.z4[2]? = some b0 := by decide +kernel
    rw [Hz] at H; exact (Option.some.inj H).symm
  · have Hz : AxSpinX4.z4[3]? = some b0 := by decide +kernel
    rw [Hz] at H; exact (Option.some.inj H).symm
  · omega

theorem o40 : AxSpinX4.o4[0]? = some b1 := by decide +kernel

theorem uWr (GD : Gdexec) (i : Agent) (t : Nat) (ts : List Nat) (w8 : BitVec 32) (k : Nat)
    (a : Int) (v : BitVec 8) :
    AxOpsem.grow GD i = uRow t ts w8 → gwritesByte GD.gdG (i, k) a v →
    (k = 0 ∧ (paZ lkpa ≤ a ∧ a < paZ lkpa + 4) ∧ (a = paZ lkpa → v = b1)) ∨
    (k = 2 ∧ ∃ j : Nat, j < 4 ∧ a = paZ nppa + (j : Int) ∧
      (WeakInterpProj.wbytes 4 (w8 + one32))[j]? = some v) ∨
    (k = 4 ∧ (paZ lkpa ≤ a ∧ a < paZ lkpa + 4) ∧ v = b0) := by
  rintro Hrow ⟨l, base, vs, j, Hl, Hwr, Hv, Ha⟩
  rw [gxLblGrow, Hrow] at Hl
  have Hj := (List.getElem?_eq_some_iff.1 Hv).1
  unfold accAddr at Ha
  subst Ha
  rcases k with _ | _ | _ | _ | _ | k <;> simp [uRow] at Hl
  all_goals (subst Hl; simp only [lbWr, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at Hwr)
  all_goals (obtain ⟨rfl, rfl⟩ := Hwr)
  · left
    simp only [wbytesLength, AxSpinX4.o4] at Hj
    refine ⟨rfl, ⟨by omega, by omega⟩, ?_⟩
    intro Heq
    have hj0 : j = 0 := by omega
    subst hj0
    rw [o40] at Hv
    exact (Option.some.inj Hv).symm
  · right; left
    simp only [wbytesLength] at Hj
    exact ⟨rfl, j, Hj, rfl, Hv⟩
  · right; right
    simp only [wbytesLength, AxSpinX4.z4] at Hj
    exact ⟨rfl, ⟨by omega, by omega⟩, z4All j v Hv⟩

/-! # 2. The iProp row-end readback -/

section shellsU
variable {hlc : HasLC} {GF : BundledGFunctors.{0,0,0}} [InvGS_gen hlc GF] [AxannotGS GF]
  (GD : Gdexec) (N obSt0 : Type) (obi : N → Gdexec → obSt0 → GSet Geid → IProp GF) (nm : N)
  [pol : Axpol]

/-- `shHltReadbackM` with ANY iProp post: the annotations' contents (own-hart, phase 2) ARE the
post. -/
theorem shHltReadbackP (cpu : CPU) (i : Agent) (k : Nat) (m : Mea GF)
    (Hm : ∀ e, e ∈ (FiniteMap.dom_set m : GSet Geid) → e.1 = i) (P : IProp GF)
    (HRQ : ([∗map] R ∈ m, R) ⊢ P) :
    ⊢ ([∗map] e ↦ R ∈ m, AxAnnot.annotOwn e R) -∗ ∀ rs : RegFile,
      tierAWpd (hlc := hlc) GD N obSt0 obi nm ⟨hp cpu hlt rs, k⟩ .MaybeStuck i
        (fun _ => P) := by
  have H : ⊢ ∀ rs : RegFile, ([∗map] e ↦ R ∈ m, AxAnnot.annotOwn e R) -∗
      tierAWpd (hlc := hlc) GD N obSt0 obi nm ⟨hp cpu hlt rs, k⟩ .MaybeStuck i
        (fun _ => P) := by
    iloeb as IH
    iintro %rs Hp
    iapply (AxSpinWit.twUnfold (hlc := hlc) GD N obSt0 obi nm _ i _).2
    isplit
    · simp only [progressObl]
      itrivial
    unfold wpdMPreStepDef
    iintro %GD' %ls ⟨%Hc, #Hg, Hloc⟩
    ihave Hok := AxSpinWit.gconstEq GD N obSt0 obi nm GD' $$ Hg
    icases Hok with %HGD
    subst GD'
    isplit
    · iintro %id %K %Hst
      exact (hltNoRead cpu _ rs k id K Hst).elim
    isplit
    · iintro %l %s' %Hst %_
      exact (hltNoAstep cpu _ rs k l s' Hst).elim
    isplit
    · iintro %s' %Hw
      obtain ⟨rs', rfl⟩ := awireRsOnly2 cpu hlt rs k s' Hw
      iapply shSkip
      inext
      iapply IH $$ %rs' Hp
    · iintro %_
      unfold postLifting
      iintro %na Hna
      ihave ⟨%Hdomi, #Hw⟩ := annotAgreeBig na m $$ Hna Hp
      imodintro
      isplitl [Hna]
      · iexact Hna
      iintro Hbig
      ihave HR := AxSpinProt7.readbackBig na m i Hdomi Hm $$ Hbig Hw
      inext
      imodintro
      iapply HRQ $$ HR
  iintro Hp %rs
  iapply H $$ %rs Hp

end shellsU

/-! # 3. The per-hart post -/

def UPost {GF : BundledGFunctors} [AxSpinX.Xv6G GF] (nm : Xv6N) (G : Gexec) (i : Agent)
    (w8 : BitVec 32) : IProp GF :=
  iprop(⌜npSrc G Lx (i, 1) (i, 0)⌝ ∗ FRAG nm w8)

def upost (G : Gexec) (i : Agent) (w8 : BitVec 32) : Prop :=
  npSrc G Lx (i, 1) (i, 0) ∧ ∃ v : Int, (0 ≤ v ∧ v < 2 ^ 32) ∧ BitVec.ofInt 32 v = w8

theorem UPostPure {GF : BundledGFunctors} [AxSpinX.Xv6G GF] (nm : Xv6N) (G : Gexec) (i : Agent)
    (w8 : BitVec 32) : UPost (GF := GF) nm G i w8 ⊢ ⌜upost G i w8⌝ := by
  unfold UPost FRAG
  iintro ⟨%Hs, %v, -, %Hv⟩
  ipureintro
  exact ⟨Hs, v, Hv⟩

/-- THE JOINT STEP (ghost level): two harts' posts at one ghost name read DIFFERENT words --
issued-fragment exclusivity. -/
theorem upostJoint {GF : BundledGFunctors} [AxSpinX.Xv6G GF] (nm : Xv6N) (G : Gexec)
    (A B : Agent) (wA wB : BitVec 32) :
    UPost (GF := GF) nm G A wA ∗ UPost nm G B wB ⊢ ⌜wA ≠ wB⌝ := by
  unfold UPost FRAG
  iintro ⟨⟨-, %vA, HA, %HvA⟩, ⟨-, %vB, HB, %HvB⟩⟩
  by_cases hw : wA = wB
  · have key : ∀ v : Int, 0 ≤ v ∧ v < 2 ^ 32 → ((BitVec.ofInt 32 v).toNat : Int) = v := by
      intro v hv
      rw [BitVec.toNat_ofInt]
      omega
    have Heq : vA = vB := by
      have h1 := key vA HvA.1
      have h2 := key vB HvB.1
      rw [HvA.2] at h1
      rw [HvB.2, ← hw] at h2
      omega
    subst Heq
    iexfalso
    iapply issuedFragExcl nm.xnI vA
    isplitl [HA]
    · iexact HA
    · iexact HB
  · ipureintro
    exact hw

/-! # 4. THE WPd -- handle surface only -/

/-- Lean-only: `wU5`'s readback map (Rocq `set (m := …)`). -/
abbrev AxSpinU2.m5 {GF : BundledGFunctors.{0,0,0}} [AxSpinX.Xv6G GF] (G : Gexec) (nm : Xv6N)
    (i : Agent) (w8 : BitVec 32) : Mea GF :=
  insert ({[((i, 2) : Geid) := FRAG nm w8]} : Mea GF) (i, 1) iprop(⌜npSrc G Lx (i, 1) (i, 0)⌝)

/-- Lean-only: `wU3`'s release map (Rocq `set (m := …)`). -/
abbrev AxSpinU2.m3 {GF : BundledGFunctors.{0,0,0}} [AxSpinX.Xv6G GF] (GT : GdexecT) (nm : Xv6N)
    (i : Agent) : Mea GF :=
  insert ({[((i, 2) : Geid) := RNp Lx nm.xnH nm.xnM nm.xnI (gtAdGd GT) (i, 2)]} : Mea GF) (i, 0)
    iprop(locked nm.xnReg Lx.xlLk i (i, 0) ∗ RCpu Lx nm.xnH (gtAdGd GT) (i, 0))

section wpdU
variable {hlc : HasLC} {GF : BundledGFunctors.{0,0,0}} [InvGS_gen hlc GF] [AxannotGS GF]
  [AxSpinX.Xv6G GF]

set_option hygiene false in
local notation "TWU " s:max => @tierAWpd GF hlc _ _ (xv6Pol GT) (gtAdGd GT) Xv6N Unit
  (protXv6 Lx) nm s .MaybeStuck i (fun _ => UPost nm (gtAdGd GT).gdG i w8)
set_option hygiene false in
local notation "LK " c:max => locked (GF := GF) nm.xnReg Lx.xlLk i c
set_option hygiene false in
local notation "NH" => notheld (GF := GF) nm.xnReg Lx.xlLk i
set_option hygiene false in
local notation "RP" => RPid (GF := GF) Lx nm.xnH nm.xnM nm.xnI (gtAdGd GT)
set_option hygiene false in
local notation "RNP " e:max => RNp (GF := GF) Lx nm.xnH nm.xnM nm.xnI (gtAdGd GT) e
set_option hygiene false in
local notation "RCPU " e:max => RCpu (GF := GF) Lx nm.xnH (gtAdGd GT) e
set_option hygiene false in
local notation "ISL" =>
  isLock (GF := GF) nm.xnReg Lx.xlLk (RPid Lx nm.xnH nm.xnM nm.xnI (gtAdGd GT))

theorem uL (GT : GdexecT) (i : Agent) (t : Nat) (ts : List Nat) (w8 : BitVec 32)
    (Hrow : AxOpsem.grow (gtAdGd GT) i = uRow t ts w8) (k : Nat) (l : Lbl) :
    (uRow t ts w8)[k]? = some l → gxLbl (gtAdGd GT).gdG (i, k) = some l := by
  intro Hk
  rw [gxLblGrow, Hrow]
  exact Hk

/-- k5 (row end): the post READ BACK from the lw's and the sw's annotations. -/
theorem wU5 (GT : GdexecT) (nm : Xv6N) (cpu : CPU) (i : Agent) (w8 : BitVec 32) :
    ⊢ AxAnnot.annotOwn (i, 1) iprop(⌜npSrc (gtAdGd GT).gdG Lx (i, 1) (i, 0)⌝) -∗
      AxAnnot.annotOwn (i, 2) (FRAG nm w8) -∗ ∀ rs : RegFile, TWU ⟨hp cpu hlt rs, 5⟩ := by
  have Hlk : get? ({[((i, 2) : Geid) := FRAG (GF := GF) nm w8]} : Mea GF) (i, 1) = none :=
    lookupSingletonNe (by simp)
  have Hm : ∀ e, e ∈ (FiniteMap.dom_set (AxSpinU2.m5 (GF := GF) (gtAdGd GT).gdG nm i w8) :
      GSet Geid) → e.1 = i := by
    intro e He
    unfold AxSpinU2.m5 at He
    rw [domInsert, domSingleton] at He
    rcases elemOfUnion.1 He with H | H <;> rw [elemOfSingleton.1 H]
  have HRQ : ([∗map] R ∈ AxSpinU2.m5 (GF := GF) (gtAdGd GT).gdG nm i w8, R) ⊢
      UPost nm (gtAdGd GT).gdG i w8 := by
    unfold UPost
    iintro H
    icases (BigSepM.bigSepM_insert Hlk).1 $$ H with ⟨H1, H⟩
    ihave H2 := (BigSepM.bigSepM_singleton (M := GMapF Geid)).1 $$ H
    isplitl [H1]
    · iexact H1
    · iexact H2
  have Hmk : ⊢ AxAnnot.annotOwn (i, 1) iprop(⌜npSrc (gtAdGd GT).gdG Lx (i, 1) (i, 0)⌝) -∗
      AxAnnot.annotOwn (i, 2) (FRAG nm w8) -∗
      [∗map] e ↦ P ∈ AxSpinU2.m5 (GF := GF) (gtAdGd GT).gdG nm i w8, AxAnnot.annotOwn e P := by
    iintro H1 H2
    iapply (BigSepM.bigSepM_insert Hlk).2
    isplitl [H1]
    · iexact H1
    iapply BigSepM.bigSepM_singleton.2
    iexact H2
  iintro H1 H2
  ihave Hm' := Hmk $$ H1 H2
  iapply (shHltReadbackP (hlc := hlc) (pol := xv6Pol GT) (gtAdGd GT) Xv6N Unit (protXv6 Lx) nm
    cpu i 5 _ Hm _ HRQ) $$ Hm'

/-- k3–k4: THE RELEASE -- `locked ∗ lk->cpu` still at the claim, `RNp` at the sw. -/
theorem wU3 (GT : GdexecT) (nm : Xv6N) (cpu : CPU) (Hcons : rvwmoCatConsistent (gtAdGd GT))
    (i : Agent) (t : Nat) (ts : List Nat) (w8 : BitVec 32)
    (Hrow : AxOpsem.grow (gtAdGd GT) i = uRow t ts w8) :
    ⊢ ISL -∗ AxAnnot.annotOwn (i, 0) iprop(LK (i, 0) ∗ RCPU (i, 0)) -∗
      AxAnnot.annotOwn (i, 2) (RNP (i, 2)) -∗
      AxAnnot.annotOwn (i, 1) iprop(⌜npSrc (gtAdGd GT).gdG Lx (i, 1) (i, 0)⌝) -∗
      AxAnnot.annotOwn (i, 2) (FRAG nm w8) -∗
      ∀ rs : RegFile, TWU ⟨hp cpu uRel rs, 3⟩ := by
  have Hlk : get? ({[((i, 2) : Geid) := RNP (i, 2)]} : Mea GF) (i, 0) = none :=
    lookupSingletonNe (by simp)
  have Hdom : ∀ e, e ∈ (FiniteMap.dom_set (AxSpinU2.m3 (GF := GF) GT nm i) : GSet Geid) →
      e.1 = i ∧ e.2 < 3 ∧
        ∃ l, (AxOpsem.grow (gtAdGd GT) i)[e.2]? = some l ∧ (lbIsR l || lbIsW l) = true := by
    intro e He
    unfold AxSpinU2.m3 at He
    rw [domInsert, domSingleton] at He
    rcases elemOfUnion.1 He with H | H <;> rw [elemOfSingleton.1 H]
    · exact ⟨rfl, by simp,
        .LRmw true false (paZ lkpa) [t, t, t, t] AxSpinX4.z4 AxSpinX4.o4 .WCplain,
        by rw [Hrow]; rfl, rfl⟩
    · exact ⟨rfl, by simp,
        .LStore false (paZ nppa) (WeakInterpProj.wbytes 4 (w8 + one32)) .WCplain,
        by rw [Hrow]; rfl, rfl⟩
  have Ha1 : ((i, 0) : Geid) ∈ (FiniteMap.dom_set (AxSpinU2.m3 (GF := GF) GT nm i) :
      GSet Geid) := by
    unfold AxSpinU2.m3
    rw [domInsert]
    exact elemOfUnion.2 (Or.inl (elemOfSingleton.2 rfl))
  have Ha2 : ((i, 2) : Geid) ∈ (FiniteMap.dom_set (AxSpinU2.m3 (GF := GF) GT nm i) :
      GSet Geid) := by
    unfold AxSpinU2.m3
    rw [domInsert, domSingleton]
    exact elemOfUnion.2 (Or.inr (elemOfSingleton.2 rfl))
  have H := wpdReleaseX (hlc := hlc) GT nm cpu Hcons i 3 hlt (i, 0) (i, 0) (i, 2)
    (AxSpinU2.m3 (GF := GF) GT nm i) (fun _ => UPost nm (gtAdGd GT).gdG i w8)
    (by rw [Hrow]; simp [uRow]) (by rw [Hrow]; simp [uRow]) (by rw [Hrow]; rfl)
    (by rw [Hrow]; rfl) Hdom Ha1 Ha2
  iintro #Hil Hc H2 H1s H2f
  iapply H $$ Hil [Hc H2] [] [H1s H2f]
  · unfold AxSpinU2.m3
    iapply (BigSepM.bigSepM_insert Hlk).2
    isplitl [Hc]
    · iexact Hc
    iapply BigSepM.bigSepM_singleton.2
    iexact H2
  · unfold AxSpinU2.m3
    iintro Hb
    icases (BigSepM.bigSepM_insert Hlk).1 $$ Hb with ⟨⟨Hl, Hcpu⟩, Hb⟩
    ihave Hn := (BigSepM.bigSepM_singleton (M := GMapF Geid)).1 $$ Hb
    isplitl [Hl]
    · iexact Hl
    isplitl [Hcpu]
    · iexact Hcpu
    · iexact Hn
  · iintro - %rs
    iapply (wU5 (hlc := hlc) GT nm cpu i w8) $$ H1s H2f %rs

/-- k2: `sw nextpid ← w8+1` from the lw's value handle (ppo rule 1); the fragment is minted. -/
theorem wU2 (GT : GdexecT) (nm : Xv6N) (cpu : CPU) (Hcons : rvwmoCatConsistent (gtAdGd GT))
    (i : Agent) (t : Nat) (ts : List Nat) (w8 : BitVec 32)
    (Hrow : AxOpsem.grow (gtAdGd GT) i = uRow t ts w8) (Hnowrap : w8.toNat + 1 < 2 ^ 32) :
    ⊢ ISL -∗ AxAnnot.annotOwn (i, 0) iprop(LK (i, 0) ∗ RCPU (i, 0)) -∗
      AxAnnot.annotOwn (i, 1) (NPh Lx GT nm (i, 1) w8) -∗
      AxAnnot.annotOwn (i, 1) iprop(⌜npSrc (gtAdGd GT).gdG Lx (i, 1) (i, 0)⌝) -∗
      ∀ rs : RegFile, TWU ⟨hp cpu (uInc w8) rs, 2⟩ := by
  have Hwf := Hcons.1
  have Hl1 := uL GT i t ts w8 Hrow 1 _ rfl
  have Hl2 := uL GT i t ts w8 Hrow 2 _ rfl
  have Hin : ((i, 1) : Geid) ∈ @Axpol.lobp (xv6Pol GT) (gtAdGd GT) (i, 2) := by
    obtain ⟨t0, Ht0⟩ := loadnReads (gtAdGd GT).gdG Hwf (i, 1) (paZ nppa) ts 4 w8 0 Hl1
      (by decide)
    obtain ⟨Hw2, -⟩ := gwbStoren _ _ _ _ _ Hl2
    exact locLobp (gtAdGd GT) Hcons (i, 1) (i, 2) _ _ _ Hl1 rfl
      (gpoRow (gtAdGd GT) i 1 2 _ _ Hl1 Hl2 (by decide)) (Or.inr ⟨t0, _, Ht0⟩)
      (Hw2 0 _ (wbytesLookupGen 4 (w8 + one32) 0 (by decide)))
  iintro #Hil Hc H1 H1s
  iapply (wpdNpSwX (hlc := hlc) GT nm cpu Hcons i 2 w8 uRel .WCplain (i, 1)
    (fun _ => UPost nm (gtAdGd GT).gdG i w8) (by rw [Hrow]; simp [uRow]) (by rw [Hrow]; rfl)
    Hnowrap Hin) $$ H1
  iintro H2 H2f %rs
  iapply (wU3 (hlc := hlc) GT nm cpu Hcons i t ts w8 Hrow) $$ Hil Hc H2 H1s H2f %rs

/-- k1: `lw nextpid`, `RNp` drawn from the claim (ppo rule 5). -/
theorem wU1 (GT : GdexecT) (nm : Xv6N) (cpu : CPU) (Hcons : rvwmoCatConsistent (gtAdGd GT))
    (i : Agent) (t : Nat) (ts : List Nat) (w8 : BitVec 32)
    (Hrow : AxOpsem.grow (gtAdGd GT) i = uRow t ts w8) (Hnowrap : w8.toNat + 1 < 2 ^ 32) :
    ⊢ ISL -∗ AxAnnot.annotOwn (i, 0) iprop(LK (i, 0) ∗ RCPU (i, 0)) -∗
      AxAnnot.annotOwn (i, 0) (RNP (i, 0)) -∗ ∀ rs : RegFile, TWU ⟨hp cpu uNp rs, 1⟩ := by
  have Hl0 := uL GT i t ts w8 Hrow 0 _ rfl
  have Hl1 := uL GT i t ts w8 Hrow 1 _ rfl
  have Hin : ((i, 0) : Geid) ∈ @Axpol.lobp (xv6Pol GT) (gtAdGd GT) (i, 1) :=
    acqLobp (gtAdGd GT) Hcons i 0 1 _ _ _ _ _ _ Hl0 Hl1 rfl (by decide)
  have Hpo : ∀ w a v', a ∈ npb Lx → gwritesByte (gtAdGd GT).gdG w a v' →
      WeakRvwmoGraph.gpo (gtAdGd GT).gdG w (i, 1) → gmoLt (gtAdGd GT).gdG w (i, 1) := by
    rintro ⟨wi, wk⟩ a v' Ha Hw ⟨Hh, Hk, -, -⟩
    dsimp only at Hh Hk
    subst Hh
    exfalso
    rw [npbLx] at Ha
    rcases uWr (gtAdGd GT) wi t ts w8 wk a v' Hrow Hw with ⟨-, h2, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩
    · simp only [lkZV, npZV] at Ha h2
      omega
    · omega
    · omega
  iintro #Hil Hc Hn
  iapply (wpdNpLwX (hlc := hlc) GT nm cpu Hcons i 1 (AxSpinX4.ldkK 4 uInc) ts w8 (i, 0)
    (fun _ => UPost nm (gtAdGd GT).gdG i w8) (by rw [Hrow]; simp [uRow]) (by rw [Hrow]; rfl)
    Hin Hpo) $$ Hn
  iintro H1 H1s %rs
  iapply (wU2 (hlc := hlc) GT nm cpu Hcons i t ts w8 Hrow Hnowrap) $$ Hil Hc H1 H1s %rs

/-- k0: THE CLAIM -- `RPid` deposited pre-split: `locked ∗ lk->cpu` and `RNp`. -/
theorem wpdCs (GT : GdexecT) (nm : Xv6N) (cpu : CPU) (Hcons : rvwmoCatConsistent (gtAdGd GT))
    (i : Agent) (t : Nat) (ts : List Nat) (w8 : BitVec 32)
    (Hrow : AxOpsem.grow (gtAdGd GT) i = uRow t ts w8) (Hnowrap : w8.toNat + 1 < 2 ^ 32) :
    ⊢ ISL -∗ NH -∗ TWU ⟨hp cpu uM0 zeroRegs, 0⟩ := by
  have Hsplit : iprop(LK (i, 0) ∗ RP (i, 0)) ⊢ iprop((LK (i, 0) ∗ RCPU (i, 0)) ∗ RNP (i, 0)) := by
    unfold RPid
    iintro ⟨Hl, Hc, Hn⟩
    isplitl [Hl Hc]
    · isplitl [Hl]
      · iexact Hl
      · iexact Hc
    · iexact Hn
  iintro #Hil Hnh
  iapply (wpdAcquireX (hlc := hlc) GT nm cpu Hcons i 0 t uNp hlt _ _
    (fun _ => UPost nm (gtAdGd GT).gdG i w8) (by rw [Hrow]; simp [uRow]) (by rw [Hrow]; rfl)
    Hsplit) $$ Hil Hnh [] %zeroRegs
  iintro - Hc Hn %rs
  iapply (wU1 (hlc := hlc) GT nm cpu Hcons i t ts w8 Hrow Hnowrap) $$ Hil Hc Hn %rs

theorem wpdCsPure (GT : GdexecT) (nm : Xv6N) (cpu : CPU) (Hcons : rvwmoCatConsistent (gtAdGd GT))
    (i : Agent) (t : Nat) (ts : List Nat) (w8 : BitVec 32)
    (Hrow : AxOpsem.grow (gtAdGd GT) i = uRow t ts w8) (Hnowrap : w8.toNat + 1 < 2 ^ 32) :
    ⊢ ISL -∗ NH -∗
      @tierAWpd GF hlc _ _ (xv6Pol GT) (gtAdGd GT) Xv6N Unit (protXv6 Lx) nm
        ⟨hp cpu uM0 zeroRegs, 0⟩ .MaybeStuck i (fun _ => iprop(⌜upost (gtAdGd GT).gdG i w8⌝)) := by
  have h := wpdCs (hlc := hlc) (GF := GF) GT nm cpu Hcons i t ts w8 Hrow Hnowrap
  unfold tierAWpd at h
  unfold tierAWpd
  exact h.trans (wand_mono .rfl (wand_mono .rfl
    (@wpdMono hlc GF _ (axGA2 (gtAdGd GT) Xv6N Unit (protXv6 Lx) nm) (xv6Pol GT) _ _ _ _ _
      (fun _ => UPostPure nm _ i w8))))

end wpdU

end Weak
