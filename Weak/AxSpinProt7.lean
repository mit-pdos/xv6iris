/-
Weak: **Phase 1b, part 3 of the spinlock plan (first half) -- hand programs, rows, runs, the
multi-annotation shells, the two-component `R` and HART A's WPd at `spinOb5`.**  (Files:
`AxSpinProt5`/`AxSpinProt6` the 1b rules; this one §1–§6; the Lean-only `AxSpinProt7b` §7–§8
(hart B's WPd `wpdB5`, the race twin `wpdR5Triv`); `AxSpinProt8` the capstone.)

Rocq: `iris/AxSpinProt7.v` @ xxvzwolszwmp (§1–§6 here, §7–§8 in `Weak/AxSpinProt7b.lean`).

## The Rocq header, in substance

Lock byte at `ya`, owned `x` at `xa`, a lk->cpu-like byte at `ca = ya + 16`; ONE-byte lock and
ONE-byte lk->cpu, hand `Pexv6` nodes, no fetch/decode.  `cv5` is the hand stand-in for
`mycpu_ret (cid_word_of i)`: `[b2]` for B, `[b1]` otherwise.
PROGRAMS
  B `b5M0`: `ld cpu` (non-holder: acquire's `holding` check); acquire (spin unrolled once);
     CS = `ld x; lw lk` (the holder's lock-word read: release's `holding` check);
     `fence rw,w; sw lk ← 0`; RE-ACQUIRE (one attempt); `fence rw,w; sw lk ← 0`; HALT.
  A `a5M0`: acquire; `sd cpu ← cv A; sd x ← 1; sd cpu ← 0`; `fence rw,w; sw lk ← 0` -- at the
     release `x` is anchored at `(A,2)` and lk->cpu at `(A,3)`: TWO DIFFERENT ANCHORS.
  A' `r5M0` (race): acquire; `fence; sw lk ← 0`; `sd x ← 1` (the value A writes, AFTER the
     release).
SHELLS: `evDrawM` (one event draws a FAMILY of lob-predecessor annotations -- the multi-anchor
release), `shHltReadbackM` (the row-end post read back from SEVERAL annotations).
WPDs: `wpdA5` (A: claim → two owned writes of lk->cpu (Φ_cpu: `cv A`, then 0) and one of `x` →
`fe5Release'` drawing the two components from two annotations); `wpdB5` and `wpdR5Triv` are in
`AxSpinProt7b`.  FINDING (lobp): B's `lw lk` cannot draw from the x-read's annotation (two loads
to different addresses are not ppo-ordered), so `locked` is kept in its OWN fragment at the
claim and the components travel separately.

## Deviations from Rocq

1. O2 STAGE C (as `AxSpinProt3` deviation 1): no text oracle -- Rocq's `Tf` arguments of
   `AxGA2`/`tierA_wpd` are gone.
2. CONTEXTS: Rocq section variables are explicit leading arguments, only where Rocq's section
   mechanism includes them; `invGS_gen HasNoLc Σ` ↦ `[InvGS_gen hlc GF]` for any `hlc`; local
   instances `sh5G`/`a5_G` are the reducible `shG …` passed explicitly, the policy `a5_pol` is
   `splPol GT` passed explicitly; `ev_drawM`'s `Hwf` is an explicit argument (as `evDraw`).
   The Rocq notations `OB5`/`R5`/`RX`/`RC`/`TWA`/`LKA`/`SH` are unfolded.
3. lean-sail shapes (as `AxSpinProt3` deviation 3): read answers `.Ok (w, none)`; `acqW` uses
   a decidable `if w = b0`; `init_regstate` ↦ `zeroRegs`; `S k` ↦ `k + 1`; `l !! k` ↦ `l[k]?`;
   `Forall P l` ↦ `∀ p, p ∈ l → P p`.  The rows' lock address is `ya` (= `paZ ypaM` by `rfl`).
4. SPLIT: Rocq §7–§8 live in the Lean-only `Weak/AxSpinProt7b.lean` (importers of Rocq
   `AxSpinProt7` import `Weak.AxSpinProt7b`).

**Rocq → Lean name map.**  `cpa_m` `cpaM`, `cpa_m_ram` `cpaMRam`, `ca` `ca`, `ca_ne_ya`
`caNeYa`, `ca_ne_xa` `caNeXa`, `ca_lk16` `caLk16`, `cv5` `cv5`, `ya_nX5` `yaNX5`, `xa_X5`
`xaX5`, `acq_w` `acqW`, `acq_k` `acqK`, `acq_rmw` `acqRmw`, `rel_m` `relM`, `fence_m` `fenceM`,
`ld_m` `AxSpinProt7.ldM`, `sd_m` `AxSpinProt7.sdM`, `b5_acq2` `b5Acq2`, `b5_cs` `b5Cs`,
`b5_acq1` `b5Acq1`, `b5_m0` `b5M0`, `b5_row` `b5Row`, `a5_cs` `a5Cs`, `a5_m0` `a5M0`, `a5_row`
`a5Row`, `r5_m0` `r5M0`, `r5_row` `r5Row`, `b5_run` `b5Run`, `a5_run` `a5Run`, `r5_run` `r5Run`,
`ev_drawM` `evDrawM`, `sh_hlt_readbackM` `shHltReadbackM`, `HF5` `HF5`, `HRs5` `HRs5`, `b5L`
`b5L`, `b5_writes_ya` `b5WritesYa`, `b5_no_x` `b5NoX`, `b5_no_ca` `b5NoCa`, `b5_nolk` `b5Nolk`,
`a5L` `a5L`, `wA5/4/3/2/1` `AxSpinProt7.wA5/4/3/2/1`, `wA0w` `AxSpinProt7.wA0w`, `wpdA5`
`wpdA5`.  Lean-only (file-qualified): `AxSpinProt7.acqKOk` (`acqK` at any `Ok` answer),
`AxSpinProt7.readbackBig` (`sh_hlt_readbackM`'s big-map read-back step).

**Dropped:** none (§1–§6: 49 Rocq decls incl. the 3 local instances `sh5G`/`a5_G`/`a5_pol`
(inlined); 48 Lean = 46 + 2 Lean-only).
-/
import Weak.AxSpinProt6

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std Iris.Std.PartialMap MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D

/-! # 1. Addresses, the hand cpu-pointer table, programs and rows -/

/-- lk->cpu-like byte at `lk + 16` (lock word at `ya`). -/
def cpaM : PAddr := zPa 0x80002010
theorem cpaMRam : devAddr cpaM = false := by decide +kernel
def ca : Int := paZ cpaM
theorem caNeYa : ca ≠ ya := by decide +kernel
theorem caNeXa : ca ≠ xa := by decide +kernel
theorem caLk16 : ca = ya + 16 := by decide +kernel

/-- The hand stand-in for `mycpu_ret (cid_word_of i)` (one byte): nonzero, and B's differs from
everyone else's. -/
def cv5 (i : Agent) : List (BitVec 8) := if i = hB then [b2] else [b1]

theorem yaNX5 : ya ∉ X5 xa [ca] := by
  unfold X5
  intro H
  rcases elemOfUnion.1 H with H | H
  · exact xaNeYa (elemOfSingleton.1 H).symm
  · exact caNeYa (List.mem_singleton.1 (LawfulSet.mem_ofList.2 H)).symm

theorem xaX5 : xa ∈ X5 xa [ca] := elemOfUnionL (elemOfSingleton.2 rfl)

abbrev acqW (kok kf : SailM Unit) (w : BitVec 8) : SailM Unit :=
  .impure (.ok (.memWrite 1 64 (l3pWreq l3pAkXpl ypaM b1))) (fun _ => if w = b0 then kok else kf)
def acqK (kok kf : SailM Unit) (res : Result (BitVec (8 * 1) × Option Bool) Arch.abort) :
    SailM Unit :=
  match res with
  | .Ok (w, _) => acqW kok kf w
  | .Err _ => hlt
/-- One acquire attempt: `amoswap.aq lk ← 1; if old = 0 then kok else kf`. -/
abbrev acqRmw (kok kf : SailM Unit) : SailM Unit :=
  .impure (.ok (.memRead 1 64 (l3pRreq l3pAkXaq ypaM))) (acqK kok kf)
abbrev relM (k : SailM Unit) : SailM Unit :=
  .impure (.ok (.memWrite 1 64 (l3pWreq l3pAkP ypaM b0))) (fun _ => k)
abbrev fenceM (k : SailM Unit) : SailM Unit :=
  .impure (.ok (.barrier .Barrier_RISCV_rw_w)) (fun _ => k)
abbrev AxSpinProt7.ldM (pa : PAddr) (k : SailM Unit) : SailM Unit :=
  .impure (.ok (.memRead 1 64 (l3pRreq l3pAkP pa))) (fun _ => k)
abbrev AxSpinProt7.sdM (pa : PAddr) (b : BitVec 8) (k : SailM Unit) : SailM Unit :=
  .impure (.ok (.memWrite 1 64 (l3pWreq l3pAkP pa b))) (fun _ => k)

/-- Lean-only: `acqK` at any `Ok` answer. -/
theorem AxSpinProt7.acqKOk (kok kf : SailM Unit) (w : BitVec (8 * 1)) (o : Option Bool) :
    acqK kok kf (.Ok (w, o)) = acqW kok kf w := rfl

/-- HART B: `ld cpu` (NON-holder lk->cpu read); acquire (spin unrolled once); CS = `ld x; lw lk`;
`fence rw,w; sw lk ← 0`; RE-ACQUIRE (one attempt); `fence rw,w; sw lk ← 0`; HALT. -/
abbrev b5Acq2 : SailM Unit := acqRmw (fenceM (relM hlt)) hlt
abbrev b5Cs : SailM Unit := AxSpinProt7.ldM xpaM (AxSpinProt7.ldM ypaM (fenceM (relM b5Acq2)))
abbrev b5Acq1 : SailM Unit := acqRmw b5Cs (acqRmw b5Cs hlt)
abbrev b5M0 : SailM Unit := AxSpinProt7.ldM cpaM b5Acq1

def b5Row (tc : Nat) (vc : BitVec 8) (t1 t2 tx : Nat) (vx : BitVec 8) (tl : Nat) (vl : BitVec 8)
    (t3 : Nat) : List Lbl :=
  [.LLoad false ca [tc] [vc],
   .LRmw true false ya [t1] [b1] [b1] .WCplain,
   .LRmw true false ya [t2] [b0] [b1] .WCplain,
   .LLoad false xa [tx] [vx],
   .LLoad false ya [tl] [vl],
   .LFence true true false true,
   .LStore false ya [b0] .WCrel,
   .LRmw true false ya [t3] [b0] [b1] .WCplain,
   .LFence true true false true,
   .LStore false ya [b0] .WCrel]

/-- HART A (positive): acquire; `sd cpu ← cv A`; `sd x ← 1`; `sd cpu ← 0`; `fence rw,w;
sw lk ← 0`.  At the release the two components of `R` sit at DIFFERENT anchors. -/
abbrev a5Cs : SailM Unit :=
  AxSpinProt7.sdM cpaM b1 (AxSpinProt7.sdM xpaM b1 (AxSpinProt7.sdM cpaM b0 (fenceM (relM hlt))))
abbrev a5M0 : SailM Unit := acqRmw a5Cs hlt

def a5Row (tA : Nat) : List Lbl :=
  [.LRmw true false ya [tA] [b0] [b1] .WCplain,
   .LStore false ca [b1] .WCplain,
   .LStore false xa [b1] .WCplain,
   .LStore false ca [b0] .WCplain,
   .LFence true true false true,
   .LStore false ya [b0] .WCrel]

/-- RACE A': acquire; `fence; sw lk ← 0`; `sd x ← 1` -- the SAME value A writes, but AFTER the
release. -/
abbrev r5M0 : SailM Unit := acqRmw (fenceM (relM (AxSpinProt7.sdM xpaM b1 hlt))) hlt

def r5Row : List Lbl :=
  [.LRmw true false ya [0] [b0] [b1] .WCplain,
   .LFence true true false true,
   .LStore false ya [b0] .WCrel,
   .LStore false xa [b1] .WCplain]

/-! # 2. Runs over an ABSTRACT graph, row pinned -/

section runs5
variable (cpu : CPU)

theorem b5Run (GD : Gdexec) (tc : Nat) (vc : BitVec 8) (t1 t2 tx : Nat) (vx : BitVec 8) (tl : Nat)
    (vl : BitVec 8) (t3 : Nat) (Hrow : AxOpsem.grow GD hB = b5Row tc vc t1 t2 tx vx tl vl t3) :
    nsteps (astepAnyNfGv GD hB) 13 ⟨hp cpu b5M0 zeroRegs, 0⟩ ⟨hp cpu hlt zeroRegs, 10⟩ := by
  refine nsteps_l (spRunRead cpu GD hB cpaM cpaMRam [tc] vc (fun _ => b5Acq1) zeroRegs 0
    (by rw [Hrow]; rfl)) ?_
  refine nsteps_l (runRmwRead cpu GD hB 1 ypaM ypaMRam t1 b1 .WCplain
    (acqK b5Cs (acqRmw b5Cs hlt)) zeroRegs (by rw [Hrow]; rfl)) ?_
  have H2 := runRmwWrite cpu GD hB 1 ypaM ypaMRam t1 b1 .WCplain
    (if b1 = b0 then b5Cs else acqRmw b5Cs hlt) zeroRegs (by rw [Hrow]; rfl)
  rw [if_neg (Ne.symm b0NeB1)] at H2
  refine nsteps_l H2 ?_
  refine nsteps_l (runRmwRead cpu GD hB 2 ypaM ypaMRam t2 b0 .WCplain (acqK b5Cs hlt) zeroRegs
    (by rw [Hrow]; rfl)) ?_
  have H4 := runRmwWrite cpu GD hB 2 ypaM ypaMRam t2 b0 .WCplain
    (if b0 = b0 then b5Cs else hlt) zeroRegs (by rw [Hrow]; rfl)
  rw [if_pos rfl] at H4
  refine nsteps_l H4 ?_
  refine nsteps_l (spRunRead cpu GD hB xpaM xpaMRam [tx] vx
    (fun _ => AxSpinProt7.ldM ypaM (fenceM (relM b5Acq2))) zeroRegs 3 (by rw [Hrow]; rfl)) ?_
  refine nsteps_l (spRunRead cpu GD hB ypaM ypaMRam [tl] vl (fun _ => fenceM (relM b5Acq2))
    zeroRegs 4 (by rw [Hrow]; rfl)) ?_
  refine nsteps_l (runFence cpu GD hB 5 (relM b5Acq2) zeroRegs (by rw [Hrow]; rfl)) ?_
  refine nsteps_l (spRunWrite cpu GD hB ypaM ypaMRam b0 b5Acq2 zeroRegs 6 .WCrel
    (by rw [Hrow]; rfl)) ?_
  refine nsteps_l (runRmwRead cpu GD hB 7 ypaM ypaMRam t3 b0 .WCplain
    (acqK (fenceM (relM hlt)) hlt) zeroRegs (by rw [Hrow]; rfl)) ?_
  have H10 := runRmwWrite cpu GD hB 7 ypaM ypaMRam t3 b0 .WCplain
    (if b0 = b0 then fenceM (relM hlt) else hlt) zeroRegs (by rw [Hrow]; rfl)
  rw [if_pos rfl] at H10
  refine nsteps_l H10 ?_
  refine nsteps_l (runFence cpu GD hB 8 (relM hlt) zeroRegs (by rw [Hrow]; rfl)) ?_
  refine nsteps_l (spRunWrite cpu GD hB ypaM ypaMRam b0 hlt zeroRegs 9 .WCrel
    (by rw [Hrow]; rfl)) ?_
  exact nsteps_O _

theorem a5Run (GD : Gdexec) (tA : Nat) (Hrow : AxOpsem.grow GD hA = a5Row tA) :
    nsteps (astepAnyNfGv GD hA) 7 ⟨hp cpu a5M0 zeroRegs, 0⟩ ⟨hp cpu hlt zeroRegs, 6⟩ := by
  refine nsteps_l (runRmwRead cpu GD hA 0 ypaM ypaMRam tA b0 .WCplain (acqK a5Cs hlt) zeroRegs
    (by rw [Hrow]; rfl)) ?_
  have H1 := runRmwWrite cpu GD hA 0 ypaM ypaMRam tA b0 .WCplain
    (if b0 = b0 then a5Cs else hlt) zeroRegs (by rw [Hrow]; rfl)
  rw [if_pos rfl] at H1
  refine nsteps_l H1 ?_
  refine nsteps_l (spRunWrite cpu GD hA cpaM cpaMRam b1 _ zeroRegs 1 .WCplain
    (by rw [Hrow]; rfl)) ?_
  refine nsteps_l (spRunWrite cpu GD hA xpaM xpaMRam b1 _ zeroRegs 2 .WCplain
    (by rw [Hrow]; rfl)) ?_
  refine nsteps_l (spRunWrite cpu GD hA cpaM cpaMRam b0 _ zeroRegs 3 .WCplain
    (by rw [Hrow]; rfl)) ?_
  refine nsteps_l (runFence cpu GD hA 4 (relM hlt) zeroRegs (by rw [Hrow]; rfl)) ?_
  refine nsteps_l (spRunWrite cpu GD hA ypaM ypaMRam b0 hlt zeroRegs 5 .WCrel
    (by rw [Hrow]; rfl)) ?_
  exact nsteps_O _

theorem r5Run (GD : Gdexec) (Hrow : AxOpsem.grow GD hA = r5Row) :
    nsteps (astepAnyNfGv GD hA) 5 ⟨hp cpu r5M0 zeroRegs, 0⟩ ⟨hp cpu hlt zeroRegs, 4⟩ := by
  refine nsteps_l (runRmwRead cpu GD hA 0 ypaM ypaMRam 0 b0 .WCplain
    (acqK (fenceM (relM (AxSpinProt7.sdM xpaM b1 hlt))) hlt) zeroRegs (by rw [Hrow]; rfl)) ?_
  have H1 := runRmwWrite cpu GD hA 0 ypaM ypaMRam 0 b0 .WCplain
    (if b0 = b0 then fenceM (relM (AxSpinProt7.sdM xpaM b1 hlt)) else hlt) zeroRegs
    (by rw [Hrow]; rfl)
  rw [if_pos rfl] at H1
  refine nsteps_l H1 ?_
  refine nsteps_l (runFence cpu GD hA 1 (relM (AxSpinProt7.sdM xpaM b1 hlt)) zeroRegs
    (by rw [Hrow]; rfl)) ?_
  refine nsteps_l (spRunWrite cpu GD hA ypaM ypaMRam b0 (AxSpinProt7.sdM xpaM b1 hlt) zeroRegs 2
    .WCrel (by rw [Hrow]; rfl)) ?_
  refine nsteps_l (spRunWrite cpu GD hA xpaM xpaMRam b1 hlt zeroRegs 3 .WCplain
    (by rw [Hrow]; rfl)) ?_
  exact nsteps_O _

end runs5

/-! # 3. Shells: drawing a FAMILY of lob-predecessor annotations at one event (`evDrawM` --
REQUIRED (1)'s multi-anchor release), and reading back SEVERAL annotations at the row end
(`shHltReadbackM`). -/

/-- Lean-only: the big-map read-back step of `shHltReadbackM` (Rocq: `big_sepM_impl_dom_subseteq`
+ `big_sepM_sep_2` + `big_sepM_later` inline). -/
theorem AxSpinProt7.readbackBig {GF : BundledGFunctors} (na m : Mea GF) (i : Agent)
    (Hdomi : (FiniteMap.dom_set m : GSet Geid) ⊆ FiniteMap.dom_set na)
    (Hm : ∀ e, e ∈ (FiniteMap.dom_set m : GSet Geid) → e.1 = i) :
    ⊢ ([∗map] e ↦ R' ∈ na, if e.1 = i then R' else iprop(True)) -∗
      ([∗map] e ↦ R ∈ m, AxWp.fromOption (fun P' => iprop(▷ □ (P' -∗ R))) iprop(emp)
        (get? na e)) -∗
      ▷ [∗map] R ∈ m, R := by
  have Hkey : ∀ (e : Geid) (x y : IProp GF), get? na e = some x → get? m e = some y →
      ⊢ iprop((if e.1 = i then x else iprop(True)) -∗
        (AxWp.fromOption (fun P' => iprop(▷ □ (P' -∗ y))) iprop(emp) (get? na e) -∗ ▷ y)) := by
    intro e x y Hx Hy
    have He : e.1 = i := Hm e (elemOfDom2 Hy)
    rw [Hx]
    simp only [He, ↓reduceIte, AxWp.fromOption]
    iintro HP Hwd
    inext
    iapply Hwd $$ HP
  have Himpl : ⊢ iprop(□ (∀ (e : Geid) (x y : IProp GF), ⌜get? na e = some x⌝ →
      ⌜get? m e = some y⌝ → (if e.1 = i then x else iprop(True)) -∗
        (AxWp.fromOption (fun P' => iprop(▷ □ (P' -∗ y))) iprop(emp) (get? na e) -∗ ▷ y))) := by
    imodintro
    iintro %e %x %y %Hx %Hy
    ihave Hk := Hkey e x y Hx Hy
    iexact Hk
  iintro Hbig Hw
  ihave H := (BigSepM.bigSepM_impl_dom_subseteq
      (Φ := fun (e : Geid) (R' : IProp GF) => iprop(if e.1 = i then R' else iprop(True)))
      (Ψ := fun (e : Geid) (y : IProp GF) =>
        iprop(AxWp.fromOption (fun P' => iprop(▷ □ (P' -∗ y))) iprop(emp) (get? na e) -∗ ▷ y))
      Hdomi) $$ Hbig
  ihave Hi := Himpl
  ihave ⟨Hres, -⟩ := H $$ Hi
  ihave H2 := (BigSepM.bigSepM_wand
      (Φ := fun (e : Geid) (y : IProp GF) =>
        AxWp.fromOption (fun P' => iprop(▷ □ (P' -∗ y))) iprop(emp) (get? na e))
      (Ψ := fun (_ : Geid) (y : IProp GF) => iprop(▷ y)) (m := m)) $$ Hw Hres
  iapply BigSepM.bigSepM_later.2
  iexact H2

section shells5
variable {hlc : HasLC} {GF : BundledGFunctors.{0,0,0}} [InvGS_gen hlc GF] [AxannotGS GF]
  (GD : Gdexec) (N obSt0 : Type) (obi : N → Gdexec → obSt0 → GSet Geid → IProp GF) (nm : N)
  [pol : Axpol]

theorem evDrawM (Hwf : @axpolWf pol) (i : Agent) (k : Nat) (m : Mea GF) (R1 R2 : IProp GF)
    (val : Prop) (Ψ : IProp GF) :
    val → (FiniteMap.dom_set m : GSet Geid) ⊆ Axpol.lobp GD (i, k) →
    ⊢ ([∗map] e ↦ P ∈ m, AxAnnot.annotOwn e P) -∗
      @flowEqDyn hlc GF _ (shG GD N obSt0 obi nm) GD (i, k) (Axpol.sPol GD (i, k)) m
        iprop(R1 ∗ R2) -∗
      (AxAnnot.annotOwn (i, k) R1 -∗ AxAnnot.annotOwn (i, k) R2 -∗ Ψ) -∗
      @wpEvStep hlc GF _ (shG GD N obSt0 obi nm) pol Unit GD i k (fun _ => True)
        (fun _ => val) (fun _ => k + 1) (fun _ => Ψ) := by
  intro Hval Hsub
  iintro Hm Hfe HΨ
  unfold wpEvStep naAtProgress
  iintro %na ⟨%Hprog, Hannot⟩
  have Hdom : (FiniteMap.dom_set m : GSet Geid) ⊆ FiniteMap.dom_set na := by
    intro e' He'
    have Hb := Hwf GD i k e' (Hsub e' He')
    rw [← Hprog] at Hb
    exact (elemOfFilter.1 Hb).2
  have Hnin : (i, k) ∉ (FiniteMap.dom_set na : GSet Geid) := by
    intro Hd
    have Hf : (i, k) ∈ FiniteSet.filter (fun e : Geid => decide (e.1 = i))
        (FiniteMap.dom_set na : GSet Geid) := elemOfFilter.2 ⟨by simp, Hd⟩
    rw [Hprog, elemOfEidsBefore] at Hf
    exact Nat.lt_irrefl _ Hf.2.1
  imod annotDetachBig na m $$ Hannot Hm with ⟨%m'', %Hdm, Hannot, Hw⟩
  have Hnin' : (i, k) ∉ (FiniteMap.dom_set (PartialMap.union m'' na) : GSet Geid) := by
    intro Hd
    have hn : get? m'' (i, k) = none := by
      apply notElemOfDom1 (S := GSet Geid)
      rw [Hdm]
      exact fun h => Hnin (Hdom _ h)
    apply Hnin
    have h := elemOfDom.1 Hd
    have hl : get? (PartialMap.union m'' na) (i, k) = get? na (i, k) := lookupUnionR hn
    rw [hl] at h
    exact elemOfDom.2 h
  have Hmono : ([∗map] e ↦ R;R' ∈ m;m'',
        AxWp.fromOption (fun P' => iprop(▷ □ (P' -∗ R ∗ R'))) iprop(emp) (get? na e)) ⊢
      [∗map] e ↦ Pu;Puu ∈ m;m'',
        iprop(▷ □ (AxWp.fromOption (fun P => P) iprop(emp) (get? na e) -∗ Pu ∗ Puu)) :=
    BigSepM2.bigSepM2_mono fun {e _ _} h1 _ => by
      obtain ⟨P0, HP0⟩ := Option.isSome_iff_exists.1 (elemOfDom.1 (Hdom _ (elemOfDom2 h1)))
      rw [HP0]
      exact .rfl
  imod annotAlloc (PartialMap.union m'' na) (i, k) iprop(R1 ∗ R2) Hnin' $$ Hannot
    with ⟨Hannot, Hfrag⟩
  imod (annotSplit (i, k) R1 R2) $$ Hfrag %_ Hannot with ⟨⟨Hf1, Hf2⟩, Hannot⟩
  imodintro
  inext
  imodintro
  iexists (), iprop(R1 ∗ R2), m, m'', ()
  isplitr
  · ipureintro
    trivial
  isplitl [Hw]
  · unfold naSplittingWf
    isplitr
    · ipureintro
      exact Hsub
    · iapply Hmono
      iexact Hw
  isplitl [Hfe]
  · iapply (@flowEqDynMono hlc GF _ (shG GD N obSt0 obi nm) pol GD (i, k) _ m
      iprop(R1 ∗ R2) iprop((R1 ∗ R2) ∗ ⌜val⌝)) $$ [] Hfe
    inext
    iintro H
    isplitl [H]
    · iexact H
    · ipureintro
      exact Hval
  isplitl [Hannot]
  · have Heq : insert (PartialMap.union m'' na) (i, k) iprop(R1 ∗ R2) =
        PartialMap.union (PartialMap.union {[(i, k) := iprop(R1 ∗ R2)]} m'') na := by
      rw [insertUnionSingletonL (M := GMapF Geid)]
      exact mapUnionAssoc (M := GMapF Geid)
    rw [← Heq]
    iexact Hannot
  isplitr
  · iapply AxSpinWit.localTrue
  · iapply HΨ $$ Hf1 Hf2

theorem shHltReadbackM (cpu : CPU) (i : Agent) (k : Nat) (m : Mea GF)
    (Hm : ∀ e, e ∈ (FiniteMap.dom_set m : GSet Geid) → e.1 = i) (Q : Prop)
    (HRQ : ([∗map] R ∈ m, R) ⊢ ⌜Q⌝) :
    ⊢ ([∗map] e ↦ R ∈ m, AxAnnot.annotOwn e R) -∗ ∀ rs : RegFile,
      tierAWpd (hlc := hlc) GD N obSt0 obi nm ⟨hp cpu hlt rs, k⟩ .MaybeStuck i
        (fun _ => iprop(⌜Q⌝)) := by
  have H : ⊢ ∀ rs : RegFile, ([∗map] e ↦ R ∈ m, AxAnnot.annotOwn e R) -∗
      tierAWpd (hlc := hlc) GD N obSt0 obi nm ⟨hp cpu hlt rs, k⟩ .MaybeStuck i
        (fun _ => iprop(⌜Q⌝)) := by
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

end shells5

/-! # 4. The two-component `R`: its family form -/

section comps
variable {GF : BundledGFunctors} [AxlogG GF Hent] [SpinlockG GF]

theorem HF5 (nm : spinN) (GD : Gdexec) : rvwmoCatConsistent GD →
    ∀ Rj, Rj ∈ [RL (GF := GF) nm.1 GD [xa], RL nm.1 GD [ca]] → lkTransportable GD Rj := by
  intro Hcons Rj H
  simp only [List.mem_cons, List.not_mem_nil, or_false] at H
  rcases H with rfl | rfl <;> exact RLTransportable _ _ _ Hcons

theorem HRs5 (nm : spinN) (GD : Gdexec) (w : Geid) :
    ([∗list] Rj ∈ [RL (GF := GF) nm.1 GD [xa], RL nm.1 GD [ca]], Rj w) ⊢
      spinR5 xa [ca] nm GD w := by
  unfold spinR5
  iintro ⟨H1, H2⟩
  ihave H2 := BigSepL.bigSepL_singleton.1 $$ H2
  isplitl [H1]
  · iexact H1
  · iexact H2

end comps

/-! # 5. Row facts -/

section rowB
variable (GD : Gdexec) (tc : Nat) (vc : BitVec 8) (t1 t2 tx : Nat) (vx : BitVec 8) (tl : Nat)
  (vl : BitVec 8) (t3 : Nat) (Hrow : AxOpsem.grow GD hB = b5Row tc vc t1 t2 tx vx tl vl t3)
include Hrow

theorem b5L (k : Nat) (lb : Lbl) :
    (b5Row tc vc t1 t2 tx vx tl vl t3)[k]? = some lb → gxLbl GD.gdG (hB, k) = some lb := by
  intro Hk
  rw [gxLblGrow, Hrow]
  exact Hk

/-- Hart B writes only the lock byte. -/
theorem b5WritesYa (w : Geid) (a : Int) (v : BitVec 8) :
    gwritesByte GD.gdG w a v → w.1 = hB → a = ya := by
  rintro ⟨l, base, vs, j, Hl, Hwr, Hv, Ha⟩ Hh
  obtain ⟨wi, wk⟩ := w
  simp only at Hh
  subst Hh
  rw [gxLblGrow, Hrow] at Hl
  have hj : ∀ (b : Int) (vs : List (BitVec 8)), vs.length = 1 → vs[j]? = some v →
      accAddr b j = a → a = b := by
    intro b vs hl hv ha
    have : j < vs.length := by
      rcases Nat.lt_or_ge j vs.length with h | h
      · exact h
      · rw [List.getElem?_eq_none h] at hv; cases hv
    rw [← ha]; simp [accAddr]; omega
  match wk, Hl with
  | 0, Hl => cases Hl; simp [lbWr] at Hwr
  | 1, Hl =>
    cases Hl; simp only [lbWr, Option.some.injEq, Prod.mk.injEq] at Hwr
    obtain ⟨rfl, rfl⟩ := Hwr
    exact hj ya _ rfl Hv Ha
  | 2, Hl =>
    cases Hl; simp only [lbWr, Option.some.injEq, Prod.mk.injEq] at Hwr
    obtain ⟨rfl, rfl⟩ := Hwr
    exact hj ya _ rfl Hv Ha
  | 3, Hl => cases Hl; simp [lbWr] at Hwr
  | 4, Hl => cases Hl; simp [lbWr] at Hwr
  | 5, Hl => cases Hl; simp [lbWr] at Hwr
  | 6, Hl =>
    cases Hl; simp only [lbWr, Option.some.injEq, Prod.mk.injEq] at Hwr
    obtain ⟨rfl, rfl⟩ := Hwr
    exact hj ya _ rfl Hv Ha
  | 7, Hl =>
    cases Hl; simp only [lbWr, Option.some.injEq, Prod.mk.injEq] at Hwr
    obtain ⟨rfl, rfl⟩ := Hwr
    exact hj ya _ rfl Hv Ha
  | 8, Hl => cases Hl; simp [lbWr] at Hwr
  | 9, Hl =>
    cases Hl; simp only [lbWr, Option.some.injEq, Prod.mk.injEq] at Hwr
    obtain ⟨rfl, rfl⟩ := Hwr
    exact hj ya _ rfl Hv Ha
  | _ + 10, Hl => simp [b5Row] at Hl

theorem b5NoX (w : Geid) (v : BitVec 8) : gwritesByte GD.gdG w xa v → w.1 = hB → False :=
  fun Hw Hh => xaNeYa (b5WritesYa GD tc vc t1 t2 tx vx tl vl t3 Hrow w xa v Hw Hh)

theorem b5NoCa (w : Geid) (v : BitVec 8) : gwritesByte GD.gdG w ca v → w.1 = hB → False :=
  fun Hw Hh => caNeYa (b5WritesYa GD tc vc t1 t2 tx vx tl vl t3 Hrow w ca v Hw Hh)

theorem b5Nolk : nolk ya GD.gdG (hB, 2) (hB, 4) := by
  rintro ⟨wi, wk⟩ v ⟨l, base, vs, j, Hl, Hwr, -⟩ ⟨Hh1, Hlt1, -⟩ ⟨-, Hlt2, -⟩
  simp only at Hh1 Hlt1 Hlt2
  subst Hh1
  have hk : wk = 3 := by omega
  subst hk
  rw [gxLblGrow, Hrow] at Hl
  cases Hl
  simp [lbWr] at Hwr

end rowB

/-! # 6. HART A's WPd at `spinOb5` (positive writer, TWO anchors at the release: `x` re-tied at
`(A,2)`, lk->cpu at `(A,3)`) -/

section wpdA5
variable {hlc : HasLC} {GF : BundledGFunctors.{0,0,0}} [InvGS_gen hlc GF] [AxannotGS GF]
  [AxlogG GF Hent] [SpinlockG GF]

theorem a5L (GT : GdexecT) (tA : Nat) (Hrow : AxOpsem.grow (gtAdGd GT) hA = a5Row tA) (k : Nat)
    (lb : Lbl) : (a5Row tA)[k]? = some lb → gxLbl (gtAdGd GT).gdG (hA, k) = some lb := by
  intro Hk
  rw [gxLblGrow, Hrow]
  exact Hk

theorem AxSpinProt7.wA5 (GT : GdexecT) (nm : spinN) (cpu : CPU)
    (Hcons : rvwmoCatConsistent (gtAdGd GT)) (tA : Nat)
    (Hrow : AxOpsem.grow (gtAdGd GT) hA = a5Row tA) :
    ⊢ isLock (GF := GF) nm.2 ya (spinR5 xa [ca] nm (gtAdGd GT)) -∗
      AxAnnot.annotOwn (hA, 2)
        iprop(locked nm.2 ya hA (hA, 0) ∗ RL nm.1 (gtAdGd GT) [xa] (hA, 2)) -∗
      AxAnnot.annotOwn (hA, 3) (RL nm.1 (gtAdGd GT) [ca] (hA, 3)) -∗
      ∀ rs : RegFile, @tierAWpd GF hlc _ _ (splPol GT) (gtAdGd GT) spinN Unit
        (spinOb5 ya xa [ca] cv5) nm ⟨hp cpu (relM hlt) rs, 5⟩ .MaybeStuck hA
        (fun _ => iprop(True)) := by
  have Hne : 5 ≠ (AxOpsem.grow (gtAdGd GT) hA).length := by rw [Hrow]; simp [a5Row]
  have Hl2 := a5L GT tA Hrow 2 _ rfl
  have Hl3 := a5L GT tA Hrow 3 _ rfl
  have Hl4 := a5L GT tA Hrow 4 _ rfl
  have Hl5 := a5L GT tA Hrow 5 _ rfl
  have hnone : get? ({[((hA, 3) : Geid) := RL (GF := GF) nm.1 (gtAdGd GT) [ca] (hA, 3)]} :
      Mea GF) (hA, 2) = none := lookupSingletonNe (by decide)
  have Hmk : ⊢ AxAnnot.annotOwn (GF := GF) (hA, 2)
        iprop(locked nm.2 ya hA (hA, 0) ∗ RL nm.1 (gtAdGd GT) [xa] (hA, 2)) -∗
      AxAnnot.annotOwn (hA, 3) (RL nm.1 (gtAdGd GT) [ca] (hA, 3)) -∗
      [∗map] e ↦ P ∈ (insert {[((hA, 3) : Geid) := RL (GF := GF) nm.1 (gtAdGd GT) [ca] (hA, 3)]}
        (hA, 2) iprop(locked nm.2 ya hA (hA, 0) ∗ RL nm.1 (gtAdGd GT) [xa] (hA, 2)) : Mea GF),
        AxAnnot.annotOwn e P := by
    iintro Ha Hb
    iapply (BigSepM.bigSepM_insert hnone).2
    isplitl [Ha]
    · iexact Ha
    · iapply BigSepM.bigSepM_singleton.2
      iexact Hb
  have H := shPos (hlc := hlc) (pol := splPol GT) (gtAdGd GT) spinN Unit (spinOb5 ya xa [ca] cv5)
    nm cpu hA (fun _ => iprop(True))
    iprop(isLock (GF := GF) nm.2 ya (spinR5 xa [ca] nm (gtAdGd GT)) ∗
      AxAnnot.annotOwn (hA, 2)
        iprop(locked nm.2 ya hA (hA, 0) ∗ RL nm.1 (gtAdGd GT) [xa] (hA, 2)) ∗
      AxAnnot.annotOwn (hA, 3) (RL nm.1 (gtAdGd GT) [ca] (hA, 3)))
    5 (relM hlt) Hne
    (fun rs id K => noReadAtWrite cpu _ ypaM ypaMRam b0 hlt rs 5 id K)
    (fun rs l s' Hst => by
      obtain ⟨rfl, Hs', -⟩ := writeInv2 cpu _ ypaM ypaMRam b0 hlt rs 5 l s' Hst
      simp only [wlWdata]
      subst Hs'
      obtain ⟨Hzw, Hsg⟩ := gwbStore _ _ _ _ _ Hl5
      have Hval : graphData (gtAdGd GT) (hA, 5) = some (WeakInterpProj.wbytes 1 b0) := by
        unfold graphData; rw [Hl5]; simp [lblData, l3pWbytes1]
      have Hob2 : gobCat (gtAdGd GT) (hA, 2) (hA, 5) :=
        fenceGob (gtAdGd GT) hA 2 4 5 _ _ _ _ Hl2 rfl Hl4 Hl5 (by decide) (by decide)
      have Hob3 : gobCat (gtAdGd GT) (hA, 3) (hA, 5) :=
        fenceGob (gtAdGd GT) hA 3 4 5 _ _ _ _ Hl3 rfl Hl4 Hl5 (by decide) (by decide)
      have H2 : ((hA, 2) : Geid) ∈ @Axpol.lobp (splPol GT) (gtAdGd GT) (hA, 5) :=
        fenceLobp (gtAdGd GT) Hcons hA 2 4 5 _ _ _ _ Hl2 rfl Hl4 Hl5 (by decide) (by decide)
      have H3 : ((hA, 3) : Geid) ∈ @Axpol.lobp (splPol GT) (gtAdGd GT) (hA, 5) :=
        fenceLobp (gtAdGd GT) Hcons hA 3 4 5 _ _ _ _ Hl3 rfl Hl4 Hl5 (by decide) (by decide)
      have Hsub : (FiniteMap.dom_set (insert
          {[((hA, 3) : Geid) := RL (GF := GF) nm.1 (gtAdGd GT) [ca] (hA, 3)]}
          (hA, 2) iprop(locked nm.2 ya hA (hA, 0) ∗ RL nm.1 (gtAdGd GT) [xa] (hA, 2)) : Mea GF) :
            GSet Geid) ⊆ @Axpol.lobp (splPol GT) (gtAdGd GT) (hA, 5) := by
        rw [domInsert, domSingleton]
        intro x hx
        rcases elemOfUnion.1 hx with h | h
        · rw [elemOfSingleton.1 h]; exact H2
        · rw [elemOfSingleton.1 h]; exact H3
      have Hsplit : ⊢ ([∗map] Rin ∈ (insert
          {[((hA, 3) : Geid) := RL (GF := GF) nm.1 (gtAdGd GT) [ca] (hA, 3)]}
          (hA, 2) iprop(locked nm.2 ya hA (hA, 0) ∗ RL nm.1 (gtAdGd GT) [xa] (hA, 2)) : Mea GF),
            Rin) -∗
          iprop(locked nm.2 ya hA (hA, 0) ∗ [∗list] Rj ∈ [RL (GF := GF) nm.1 (gtAdGd GT) [xa],
            RL nm.1 (gtAdGd GT) [ca]], ∃ a, ⌜gobCat (gtAdGd GT) a (hA, 5)⌝ ∗ Rj a) := by
        iintro H
        icases (BigSepM.bigSepM_insert hnone).1 $$ H with ⟨⟨Hlk, HX⟩, HC⟩
        ihave HC := (BigSepM.bigSepM_singleton (M := GMapF Geid)).1 $$ HC
        isplitl [Hlk]
        · iexact Hlk
        isplitl [HX]
        · iexists (hA, 2)
          isplitr
          · ipureintro; exact Hob2
          · iexact HX
        · iapply BigSepL.bigSepL_singleton.2
          iexists (hA, 3)
          isplitr
          · ipureintro; exact Hob3
          · iexact HC
      iintro ⟨#Hil, Hx, Hc⟩
      ihave Hm := Hmk $$ Hx Hc
      ihave Hw := Hsplit
      ihave Hfe := (fe5Release' (hlc := hlc) ya xa [ca] cv5 GT nm Hcons yaNX5 (hA, 5) hA (hA, 0)
        (spinR5 xa [ca] nm (gtAdGd GT))
        [RL (GF := GF) nm.1 (gtAdGd GT) [xa], RL nm.1 (gtAdGd GT) [ca]] _ Hzw
        (fun t v => storeNoRead _ _ _ _ _ _ _ _ Hl5) (fun a v H => (Hsg a v H).1)
        (HF5 nm (gtAdGd GT) Hcons) (HRs5 nm (gtAdGd GT) (hA, 5))) $$ Hil Hw
      iapply (evDrawM (hlc := hlc) (pol := splPol GT) (gtAdGd GT) spinN Unit
        (spinOb5 ya xa [ca] cv5) nm (splAxpolWf GT) hA 5 _ (notheld nm.2 ya hA) iprop(True) _ _
        Hval Hsub) $$ Hm [Hfe]
      · iapply (@flowEqDynMono hlc GF _ (shG (gtAdGd GT) spinN Unit (spinOb5 ya xa [ca] cv5) nm)
          (splPol GT) (gtAdGd GT) (hA, 5) _ _ (notheld nm.2 ya hA)
          iprop(notheld nm.2 ya hA ∗ True)) $$ [] Hfe
        inext
        iintro H
        isplitl [H]
        · iexact H
        · itrivial
      iintro _ _
      iapply (shHltTrue (hlc := hlc) (pol := splPol GT) (gtAdGd GT) spinN Unit
        (spinOb5 ya xa [ca] cv5) nm cpu hA (5 + 1)) $$ %rs)
  iintro #Hil Hx Hc
  iapply H $$ [$Hil $Hx $Hc]

theorem AxSpinProt7.wA4 (GT : GdexecT) (nm : spinN) (cpu : CPU)
    (Hcons : rvwmoCatConsistent (gtAdGd GT)) (tA : Nat)
    (Hrow : AxOpsem.grow (gtAdGd GT) hA = a5Row tA) :
    ⊢ isLock (GF := GF) nm.2 ya (spinR5 xa [ca] nm (gtAdGd GT)) -∗
      AxAnnot.annotOwn (hA, 2)
        iprop(locked nm.2 ya hA (hA, 0) ∗ RL nm.1 (gtAdGd GT) [xa] (hA, 2)) -∗
      AxAnnot.annotOwn (hA, 3) (RL nm.1 (gtAdGd GT) [ca] (hA, 3)) -∗
      ∀ rs : RegFile, @tierAWpd GF hlc _ _ (splPol GT) (gtAdGd GT) spinN Unit
        (spinOb5 ya xa [ca] cv5) nm ⟨hp cpu (fenceM (relM hlt)) rs, 4⟩ .MaybeStuck hA
        (fun _ => iprop(True)) := by
  have Hne : 4 ≠ (AxOpsem.grow (gtAdGd GT) hA).length := by rw [Hrow]; simp [a5Row]
  have H := shPos (hlc := hlc) (pol := splPol GT) (gtAdGd GT) spinN Unit (spinOb5 ya xa [ca] cv5)
    nm cpu hA (fun _ => iprop(True))
    iprop(isLock (GF := GF) nm.2 ya (spinR5 xa [ca] nm (gtAdGd GT)) ∗
      AxAnnot.annotOwn (hA, 2)
        iprop(locked nm.2 ya hA (hA, 0) ∗ RL nm.1 (gtAdGd GT) [xa] (hA, 2)) ∗
      AxAnnot.annotOwn (hA, 3) (RL nm.1 (gtAdGd GT) [ca] (hA, 3)))
    4 (fenceM (relM hlt)) Hne
    (fun rs id K => noReadAtFence cpu _ (relM hlt) rs 4 id K)
    (fun rs l s' Hst => by
      obtain ⟨rfl, Hs', -⟩ := fenceInv2 cpu _ (relM hlt) rs 4 l s' Hst
      simp only [wlWdata]
      subst Hs'
      iintro ⟨#Hil, Hx, Hc⟩
      iapply (shSkip2 (GF := GF) (gtAdGd GT) spinN Unit (spinOb5 ya xa [ca] cv5) nm hA _ _)
      inext
      iapply (AxSpinProt7.wA5 (hlc := hlc) GT nm cpu Hcons tA Hrow) $$ Hil Hx Hc %rs)
  iintro #Hil Hx Hc
  iapply H $$ [$Hil $Hx $Hc]

theorem AxSpinProt7.wA3 (GT : GdexecT) (nm : spinN) (cpu : CPU)
    (Hcons : rvwmoCatConsistent (gtAdGd GT)) (tA : Nat)
    (Hrow : AxOpsem.grow (gtAdGd GT) hA = a5Row tA) :
    ⊢ isLock (GF := GF) nm.2 ya (spinR5 xa [ca] nm (gtAdGd GT)) -∗
      AxAnnot.annotOwn (hA, 2)
        iprop(locked nm.2 ya hA (hA, 0) ∗ RL nm.1 (gtAdGd GT) [xa] (hA, 2)) -∗
      AxAnnot.annotOwn (hA, 1) (RL nm.1 (gtAdGd GT) [ca] (hA, 1)) -∗
      ∀ rs : RegFile, @tierAWpd GF hlc _ _ (splPol GT) (gtAdGd GT) spinN Unit
        (spinOb5 ya xa [ca] cv5) nm ⟨hp cpu (AxSpinProt7.sdM cpaM b0 (fenceM (relM hlt))) rs, 3⟩
        .MaybeStuck hA (fun _ => iprop(True)) := by
  have Hne : 3 ≠ (AxOpsem.grow (gtAdGd GT) hA).length := by rw [Hrow]; simp [a5Row]
  have Hl1 := a5L GT tA Hrow 1 _ rfl
  have Hl3 := a5L GT tA Hrow 3 _ rfl
  have H := shPos (hlc := hlc) (pol := splPol GT) (gtAdGd GT) spinN Unit (spinOb5 ya xa [ca] cv5)
    nm cpu hA (fun _ => iprop(True))
    iprop(isLock (GF := GF) nm.2 ya (spinR5 xa [ca] nm (gtAdGd GT)) ∗
      AxAnnot.annotOwn (hA, 2)
        iprop(locked nm.2 ya hA (hA, 0) ∗ RL nm.1 (gtAdGd GT) [xa] (hA, 2)) ∗
      AxAnnot.annotOwn (hA, 1) (RL nm.1 (gtAdGd GT) [ca] (hA, 1)))
    3 (AxSpinProt7.sdM cpaM b0 (fenceM (relM hlt))) Hne
    (fun rs id K => noReadAtWrite cpu _ cpaM cpaMRam b0 (fenceM (relM hlt)) rs 3 id K)
    (fun rs l s' Hst => by
      obtain ⟨rfl, Hs', -⟩ := writeInv2 cpu _ cpaM cpaMRam b0 (fenceM (relM hlt)) rs 3 l s' Hst
      simp only [wlWdata]
      subst Hs'
      obtain ⟨Hw1, -⟩ := gwbStore _ _ _ _ _ Hl1
      obtain ⟨Hw3, Hsg3⟩ := gwbStore _ _ _ _ _ Hl3
      have Hval : graphData (gtAdGd GT) (hA, 3) = some (WeakInterpProj.wbytes 1 b0) := by
        unfold graphData; rw [Hl3]; simp [lblData, l3pWbytes1]
      have Hpo : WeakRvwmoGraph.gpo (gtAdGd GT).gdG (hA, 1) (hA, 3) :=
        gpoRow (gtAdGd GT) hA 1 3 _ _ Hl1 Hl3 (by decide)
      have Hlt : gmoLt (gtAdGd GT).gdG (hA, 1) (hA, 3) :=
        gobGmo (gtAdGd GT) Hcons _ _ (ppo1Gob (gtAdGd GT) (hA, 1) (hA, 3) ca b0 Hpo
          (.inl ⟨b1, Hw1⟩) Hw3)
      have Hin : ((hA, 1) : Geid) ∈ @Axpol.lobp (splPol GT) (gtAdGd GT) (hA, 3) :=
        lobpIntro (gtAdGd GT) _ _ _ Hl1 rfl Hpo Hlt
      have Hisw : gisW (gtAdGd GT).gdG (hA, 3) = true := by unfold gisW; rw [Hl3]; rfl
      have Hcpu : cpuOk [ca] cv5 (gtAdGd GT).gdG (hA, 3) := by
        left
        intro j a v Hj Hw
        have Hv := (Hsg3 a v Hw).2
        subst Hv
        cases j with
        | zero => rfl
        | succ j => simp at Hj
      have Hsing : ⊢ ([∗map] Rin ∈ ({[((hA, 1) : Geid) :=
          RL (GF := GF) nm.1 (gtAdGd GT) [ca] (hA, 1)]} : Mea GF), Rin) -∗
          iprop(True ∗ RL (GF := GF) nm.1 (gtAdGd GT) [ca] (hA, 1)) := by
        iintro H
        ihave H := (BigSepM.bigSepM_singleton (M := GMapF Geid)).1 $$ H
        isplitr
        · itrivial
        · iexact H
      iintro ⟨#Hil, Hx, Hc⟩
      ihave Hw := Hsing
      ihave Hfe := (fe5RLwrite (hlc := hlc) ya xa [ca] cv5 GT nm Hcons yaNX5 (hA, 3) (hA, 1) [ca]
        iprop(True) ({[((hA, 1) : Geid) := RL (GF := GF) nm.1 (gtAdGd GT) [ca] (hA, 1)]} : Mea GF)
        Hisw Hlt
        (fun a Ha => ⟨b0, by rw [List.mem_singleton.1 Ha]; exact Hw3⟩)
        (fun a v H => by rw [(Hsg3 a v H).1]; exact List.mem_singleton.2 rfl)
        (fun H => caNeYa (List.mem_singleton.1 H).symm) Hcpu) $$ Hw
      iapply (evDraw (hlc := hlc) (pol := splPol GT) (gtAdGd GT) spinN Unit
        (spinOb5 ya xa [ca] cv5) nm (splAxpolWf GT) hA 3 (hA, 1) _ iprop(True)
        (RL (GF := GF) nm.1 (gtAdGd GT) [ca] (hA, 3)) _ _ Hval Hin) $$ Hc Hfe
      iintro _ Hc3
      iapply (AxSpinProt7.wA4 (hlc := hlc) GT nm cpu Hcons tA Hrow) $$ Hil Hx Hc3 %rs)
  iintro #Hil Hx Hc
  iapply H $$ [$Hil $Hx $Hc]

theorem AxSpinProt7.wA2 (GT : GdexecT) (nm : spinN) (cpu : CPU)
    (Hcons : rvwmoCatConsistent (gtAdGd GT)) (tA : Nat)
    (Hrow : AxOpsem.grow (gtAdGd GT) hA = a5Row tA) :
    ⊢ isLock (GF := GF) nm.2 ya (spinR5 xa [ca] nm (gtAdGd GT)) -∗
      AxAnnot.annotOwn (hA, 0)
        iprop(locked nm.2 ya hA (hA, 0) ∗ RL nm.1 (gtAdGd GT) [xa] (hA, 0)) -∗
      AxAnnot.annotOwn (hA, 1) (RL nm.1 (gtAdGd GT) [ca] (hA, 1)) -∗
      ∀ rs : RegFile, @tierAWpd GF hlc _ _ (splPol GT) (gtAdGd GT) spinN Unit
        (spinOb5 ya xa [ca] cv5) nm
        ⟨hp cpu (AxSpinProt7.sdM xpaM b1 (AxSpinProt7.sdM cpaM b0 (fenceM (relM hlt)))) rs, 2⟩
        .MaybeStuck hA (fun _ => iprop(True)) := by
  have Hne : 2 ≠ (AxOpsem.grow (gtAdGd GT) hA).length := by rw [Hrow]; simp [a5Row]
  have Hl0 := a5L GT tA Hrow 0 _ rfl
  have Hl2 := a5L GT tA Hrow 2 _ rfl
  have H := shPos (hlc := hlc) (pol := splPol GT) (gtAdGd GT) spinN Unit (spinOb5 ya xa [ca] cv5)
    nm cpu hA (fun _ => iprop(True))
    iprop(isLock (GF := GF) nm.2 ya (spinR5 xa [ca] nm (gtAdGd GT)) ∗
      AxAnnot.annotOwn (hA, 0)
        iprop(locked nm.2 ya hA (hA, 0) ∗ RL nm.1 (gtAdGd GT) [xa] (hA, 0)) ∗
      AxAnnot.annotOwn (hA, 1) (RL nm.1 (gtAdGd GT) [ca] (hA, 1)))
    2 (AxSpinProt7.sdM xpaM b1 (AxSpinProt7.sdM cpaM b0 (fenceM (relM hlt)))) Hne
    (fun rs id K => noReadAtWrite cpu _ xpaM xpaMRam b1
      (AxSpinProt7.sdM cpaM b0 (fenceM (relM hlt))) rs 2 id K)
    (fun rs l s' Hst => by
      obtain ⟨rfl, Hs', -⟩ := writeInv2 cpu _ xpaM xpaMRam b1
        (AxSpinProt7.sdM cpaM b0 (fenceM (relM hlt))) rs 2 l s' Hst
      simp only [wlWdata]
      subst Hs'
      obtain ⟨Hw2, Hsg2⟩ := gwbStore _ _ _ _ _ Hl2
      have Hval : graphData (gtAdGd GT) (hA, 2) = some (WeakInterpProj.wbytes 1 b1) := by
        unfold graphData; rw [Hl2]; simp [lblData, l3pWbytes1]
      have Hlt : gmoLt (gtAdGd GT).gdG (hA, 0) (hA, 2) :=
        gobGmo (gtAdGd GT) Hcons _ _ (acqGob (gtAdGd GT) hA 0 2 _ _ _ _ _ _ Hl0 Hl2 rfl (by decide))
      have Hin : ((hA, 0) : Geid) ∈ @Axpol.lobp (splPol GT) (gtAdGd GT) (hA, 2) :=
        acqLobp (gtAdGd GT) Hcons hA 0 2 _ _ _ _ _ _ Hl0 Hl2 rfl (by decide)
      have Hisw : gisW (gtAdGd GT).gdG (hA, 2) = true := by unfold gisW; rw [Hl2]; rfl
      have Hcpu : cpuOk [ca] cv5 (gtAdGd GT).gdG (hA, 2) :=
        cpuOkNw [ca] cv5 _ _ (fun a v Ha Hw =>
          caNeXa ((List.mem_singleton.1 Ha).symm.trans (Hsg2 a v Hw).1))
      have Hsing : ⊢ ([∗map] Rin ∈ ({[((hA, 0) : Geid) :=
          iprop(locked (GF := GF) nm.2 ya hA (hA, 0) ∗ RL nm.1 (gtAdGd GT) [xa] (hA, 0))]} :
            Mea GF), Rin) -∗
          iprop(locked (GF := GF) nm.2 ya hA (hA, 0) ∗ RL nm.1 (gtAdGd GT) [xa] (hA, 0)) := by
        iintro H
        ihave H := (BigSepM.bigSepM_singleton (M := GMapF Geid)).1 $$ H
        iexact H
      iintro ⟨#Hil, Hx, Hc⟩
      ihave Hw := Hsing
      ihave Hfe := (fe5RLwrite (hlc := hlc) ya xa [ca] cv5 GT nm Hcons yaNX5 (hA, 2) (hA, 0) [xa]
        (locked nm.2 ya hA (hA, 0))
        ({[((hA, 0) : Geid) :=
          iprop(locked (GF := GF) nm.2 ya hA (hA, 0) ∗ RL nm.1 (gtAdGd GT) [xa] (hA, 0))]} :
            Mea GF)
        Hisw Hlt
        (fun a Ha => ⟨b1, by rw [List.mem_singleton.1 Ha]; exact Hw2⟩)
        (fun a v H => by rw [(Hsg2 a v H).1]; exact List.mem_singleton.2 rfl)
        (fun H => xaNeYa (List.mem_singleton.1 H).symm) Hcpu) $$ Hw
      iapply (evDraw (hlc := hlc) (pol := splPol GT) (gtAdGd GT) spinN Unit
        (spinOb5 ya xa [ca] cv5) nm (splAxpolWf GT) hA 2 (hA, 0) _
        iprop(locked nm.2 ya hA (hA, 0) ∗ RL nm.1 (gtAdGd GT) [xa] (hA, 2)) iprop(True) _ _
        Hval Hin) $$ Hx [Hfe]
      · iapply (@flowEqDynMono hlc GF _ (shG (gtAdGd GT) spinN Unit (spinOb5 ya xa [ca] cv5) nm)
          (splPol GT) (gtAdGd GT) (hA, 2) _ _
          iprop(locked nm.2 ya hA (hA, 0) ∗ RL nm.1 (gtAdGd GT) [xa] (hA, 2))
          iprop((locked nm.2 ya hA (hA, 0) ∗ RL nm.1 (gtAdGd GT) [xa] (hA, 2)) ∗ True)) $$ [] Hfe
        inext
        iintro H
        isplitl [H]
        · iexact H
        · itrivial
      iintro Hx _
      iapply (AxSpinProt7.wA3 (hlc := hlc) GT nm cpu Hcons tA Hrow) $$ Hil Hx Hc %rs)
  iintro #Hil Hx Hc
  iapply H $$ [$Hil $Hx $Hc]

theorem AxSpinProt7.wA1 (GT : GdexecT) (nm : spinN) (cpu : CPU)
    (Hcons : rvwmoCatConsistent (gtAdGd GT)) (tA : Nat)
    (Hrow : AxOpsem.grow (gtAdGd GT) hA = a5Row tA) :
    ⊢ isLock (GF := GF) nm.2 ya (spinR5 xa [ca] nm (gtAdGd GT)) -∗
      AxAnnot.annotOwn (hA, 0)
        iprop(locked nm.2 ya hA (hA, 0) ∗ RL nm.1 (gtAdGd GT) [xa] (hA, 0)) -∗
      AxAnnot.annotOwn (hA, 0) (RL nm.1 (gtAdGd GT) [ca] (hA, 0)) -∗
      ∀ rs : RegFile, @tierAWpd GF hlc _ _ (splPol GT) (gtAdGd GT) spinN Unit
        (spinOb5 ya xa [ca] cv5) nm ⟨hp cpu a5Cs rs, 1⟩ .MaybeStuck hA
        (fun _ => iprop(True)) := by
  have Hne : 1 ≠ (AxOpsem.grow (gtAdGd GT) hA).length := by rw [Hrow]; simp [a5Row]
  have Hl0 := a5L GT tA Hrow 0 _ rfl
  have Hl1 := a5L GT tA Hrow 1 _ rfl
  have H := shPos (hlc := hlc) (pol := splPol GT) (gtAdGd GT) spinN Unit (spinOb5 ya xa [ca] cv5)
    nm cpu hA (fun _ => iprop(True))
    iprop(isLock (GF := GF) nm.2 ya (spinR5 xa [ca] nm (gtAdGd GT)) ∗
      AxAnnot.annotOwn (hA, 0)
        iprop(locked nm.2 ya hA (hA, 0) ∗ RL nm.1 (gtAdGd GT) [xa] (hA, 0)) ∗
      AxAnnot.annotOwn (hA, 0) (RL nm.1 (gtAdGd GT) [ca] (hA, 0)))
    1 a5Cs Hne
    (fun rs id K => noReadAtWrite cpu _ cpaM cpaMRam b1 _ rs 1 id K)
    (fun rs l s' Hst => by
      obtain ⟨rfl, Hs', -⟩ := writeInv2 cpu _ cpaM cpaMRam b1 _ rs 1 l s' Hst
      simp only [wlWdata]
      subst Hs'
      obtain ⟨Hw1, Hsg1⟩ := gwbStore _ _ _ _ _ Hl1
      have Hval : graphData (gtAdGd GT) (hA, 1) = some (WeakInterpProj.wbytes 1 b1) := by
        unfold graphData; rw [Hl1]; simp [lblData, l3pWbytes1]
      have Hlt : gmoLt (gtAdGd GT).gdG (hA, 0) (hA, 1) :=
        gobGmo (gtAdGd GT) Hcons _ _ (acqGob (gtAdGd GT) hA 0 1 _ _ _ _ _ _ Hl0 Hl1 rfl (by decide))
      have Hin : ((hA, 0) : Geid) ∈ @Axpol.lobp (splPol GT) (gtAdGd GT) (hA, 1) :=
        acqLobp (gtAdGd GT) Hcons hA 0 1 _ _ _ _ _ _ Hl0 Hl1 rfl (by decide)
      have Hisw : gisW (gtAdGd GT).gdG (hA, 1) = true := by unfold gisW; rw [Hl1]; rfl
      have Hcpu : cpuOk [ca] cv5 (gtAdGd GT).gdG (hA, 1) := by
        right
        intro j a v Hj Hw
        have Hv := (Hsg1 a v Hw).2
        subst Hv
        cases j with
        | zero => rfl
        | succ j => simp at Hj
      have Hsing : ⊢ ([∗map] Rin ∈ ({[((hA, 0) : Geid) :=
          RL (GF := GF) nm.1 (gtAdGd GT) [ca] (hA, 0)]} : Mea GF), Rin) -∗
          iprop(True ∗ RL (GF := GF) nm.1 (gtAdGd GT) [ca] (hA, 0)) := by
        iintro H
        ihave H := (BigSepM.bigSepM_singleton (M := GMapF Geid)).1 $$ H
        isplitr
        · itrivial
        · iexact H
      iintro ⟨#Hil, Hx, Hc⟩
      ihave Hw := Hsing
      ihave Hfe := (fe5RLwrite (hlc := hlc) ya xa [ca] cv5 GT nm Hcons yaNX5 (hA, 1) (hA, 0) [ca]
        iprop(True) ({[((hA, 0) : Geid) := RL (GF := GF) nm.1 (gtAdGd GT) [ca] (hA, 0)]} : Mea GF)
        Hisw Hlt
        (fun a Ha => ⟨b1, by rw [List.mem_singleton.1 Ha]; exact Hw1⟩)
        (fun a v H => by rw [(Hsg1 a v H).1]; exact List.mem_singleton.2 rfl)
        (fun H => caNeYa (List.mem_singleton.1 H).symm) Hcpu) $$ Hw
      iapply (evDraw (hlc := hlc) (pol := splPol GT) (gtAdGd GT) spinN Unit
        (spinOb5 ya xa [ca] cv5) nm (splAxpolWf GT) hA 1 (hA, 0) _ iprop(True)
        (RL (GF := GF) nm.1 (gtAdGd GT) [ca] (hA, 1)) _ _ Hval Hin) $$ Hc Hfe
      iintro _ Hc1
      iapply (AxSpinProt7.wA2 (hlc := hlc) GT nm cpu Hcons tA Hrow) $$ Hil Hx Hc1 %rs)
  iintro #Hil Hx Hc
  iapply H $$ [$Hil $Hx $Hc]

theorem AxSpinProt7.wA0w (GT : GdexecT) (nm : spinN) (cpu : CPU)
    (Hcons : rvwmoCatConsistent (gtAdGd GT)) (tA : Nat)
    (Hrow : AxOpsem.grow (gtAdGd GT) hA = a5Row tA) :
    ⊢ isLock (GF := GF) nm.2 ya (spinR5 xa [ca] nm (gtAdGd GT)) -∗ notheld nm.2 ya hA -∗
      ∀ rs : RegFile, @tierAWpd GF hlc _ _ (splPol GT) (gtAdGd GT) spinN Unit
        (spinOb5 ya xa [ca] cv5) nm ⟨hp cpu (acqW a5Cs hlt b0) rs, 0⟩ .MaybeStuck hA
        (fun _ => iprop(True)) := by
  have Hne : 0 ≠ (AxOpsem.grow (gtAdGd GT) hA).length := by rw [Hrow]; simp [a5Row]
  have Hl0 := a5L GT tA Hrow 0 _ rfl
  obtain ⟨Hrd, Hw, Hsg, -⟩ := gwbRmw _ _ _ _ _ _ _ Hl0
  have Hval : graphData (gtAdGd GT) (hA, 0) = some (WeakInterpProj.wbytes 1 b1) := by
    unfold graphData; rw [Hl0]; simp [lblData, l3pWbytes1]
  have H := shRmwWrite (hlc := hlc) (pol := splPol GT) (gtAdGd GT) spinN Unit
    (spinOb5 ya xa [ca] cv5) nm cpu hA (fun _ => iprop(True)) ypaM ypaMRam
    (if b0 = b0 then a5Cs else hlt) 0 Hne
    iprop(isLock (GF := GF) nm.2 ya (spinR5 xa [ca] nm (gtAdGd GT)) ∗ notheld nm.2 ya hA)
    (fun rs => by
      iintro ⟨#Hil, Hnh⟩
      ihave Hfe := (fe5Claim (hlc := hlc) ya xa [ca] cv5 GT nm Hcons yaNX5 (hA, 0)
        (gwriteAt (gtAdGd GT).gdG tA) ⟨tA, Hrd, rfl, Hw⟩ (fun a v H => (Hsg a v H).1))
        $$ Hnh Hil
      iapply (evPlain (hlc := hlc) (pol := splPol GT) (gtAdGd GT) spinN Unit
        (spinOb5 ya xa [ca] cv5) nm hA 0
        iprop(locked nm.2 ya hA (hA, 0) ∗ RL nm.1 (gtAdGd GT) [xa] (hA, 0))
        (RL (GF := GF) nm.1 (gtAdGd GT) [ca] (hA, 0)) _ _ Hval) $$ [Hfe]
      · iapply (@flowEqDynMono hlc GF _ (shG (gtAdGd GT) spinN Unit (spinOb5 ya xa [ca] cv5) nm)
          (splPol GT) (gtAdGd GT) (hA, 0) _ (∅ : Mea GF)
          iprop(locked nm.2 ya hA (hA, 0) ∗ spinR5 xa [ca] nm (gtAdGd GT) (hA, 0))
          iprop((locked nm.2 ya hA (hA, 0) ∗ RL nm.1 (gtAdGd GT) [xa] (hA, 0)) ∗
            RL nm.1 (gtAdGd GT) [ca] (hA, 0))) $$ [] Hfe
        inext
        iintro ⟨Hl, H⟩
        iunfold spinR5 at H
        icases H with ⟨H1, H2⟩
        isplitl [Hl H1]
        · isplitl [Hl]
          · iexact Hl
          · iexact H1
        · iexact H2
      iintro Hx Hc
      rw [if_pos rfl]
      iapply (AxSpinProt7.wA1 (hlc := hlc) GT nm cpu Hcons tA Hrow) $$ Hil Hx Hc %rs)
  iintro #Hil Hnh
  iapply H $$ [$Hil $Hnh]

theorem wpdA5 (GT : GdexecT) (nm : spinN) (cpu : CPU)
    (Hcons : rvwmoCatConsistent (gtAdGd GT)) (tA : Nat)
    (Hrow : AxOpsem.grow (gtAdGd GT) hA = a5Row tA) :
    ⊢ isLock (GF := GF) nm.2 ya (spinR5 xa [ca] nm (gtAdGd GT)) -∗ notheld nm.2 ya hA -∗
      @tierAWpd GF hlc _ _ (splPol GT) (gtAdGd GT) spinN Unit (spinOb5 ya xa [ca] cv5) nm
        ⟨hp cpu a5M0 zeroRegs, 0⟩ .MaybeStuck hA (fun _ => iprop(True)) := by
  have Hne : 0 ≠ (AxOpsem.grow (gtAdGd GT) hA).length := by rw [Hrow]; simp [a5Row]
  have Hl0 : (AxOpsem.grow (gtAdGd GT) hA)[0]? =
      some (.LRmw true false (paZ ypaM) [tA] [b0] [b1] .WCplain) := by rw [Hrow]; rfl
  have H := shRmwRead (hlc := hlc) (pol := splPol GT) (gtAdGd GT) spinN Unit
    (spinOb5 ya xa [ca] cv5) nm cpu hA (fun _ => iprop(True)) ypaM ypaMRam (acqK a5Cs hlt) 0 tA
    b0 .WCplain Hne Hl0
    iprop(isLock (GF := GF) nm.2 ya (spinR5 xa [ca] nm (gtAdGd GT)) ∗ notheld nm.2 ya hA)
    (fun rs => by
      iintro ⟨#Hil, Hnh⟩
      rw [AxSpinProt7.acqKOk]
      iapply (AxSpinProt7.wA0w (hlc := hlc) GT nm cpu Hcons tA Hrow) $$ Hil Hnh %rs)
  iintro #Hil Hnh
  iapply H $$ [$Hil $Hnh] %zeroRegs

end wpdA5

end Weak
