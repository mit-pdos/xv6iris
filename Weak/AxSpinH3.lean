/-
Weak: **Phase 2, part 3 of the spinlock plan -- the CRITICAL-SECTION CERTIFICATE.**  Hart B runs
`acquire; ld x (v); [addi: v+2]; sd x (v+2); ld x (v'); fence rw,w; sw lk ← 0` (hand `Pexv6`
nodes `hM0`, row `hRow`) and its WPd `wpdH` is written ONLY with the handle surface:
`wpdAcquireH`, `wpdLdOwn`, `wpdSdOwn`, `wpdReloadOwn`, `wpdReleaseH`; the post `⌜v' = v + 2⌝` is
READ BACK at the row end from the reload's annotation (`shHltReadback`).

Rocq: `iris/AxSpinH3.v` @ xxvzwolszwmp.

## The Rocq header, in substance

PROVED
  `csReloadOwned`: for ANY hart A with a WPd at `spinOb5` from `spinInit5` and any run, on every
    tagged-consistent ctrl-closed 2-hart graph where B's row is `hRow t1 tx vx ty vy`:
    `vy = vx + 2`.
  CERTIFICATES
    (a) `ghPremises` -- EVERY premise on `gha` (ORDERED: B's store gmo-before its reload) and on
        `ghf` (FORWARDED: the reload gmo-before the store, reading it by forwarding), A = the
        `AxSpinProt7` writer `a5` PROVED at the real protocol (`wpdA5`); `ghShape`: both cases
        of the reload leaf's split are really taken, B's first load reads A's `x := 1`, B claims
        A's release; `ghaSound`/`ghfSound`: the capstone fires (3 = 1 + 2).
    (b) `ghrWpdUnprovable` -- RACE: A' = `AxSpinProt7`'s `r5` (writes `x := 1` AFTER its
        release); on the consistent ctrl-closed `ghr` B reads 0, stores 2, A''s write lands
        gmo-between B's store and reload, the reload reads 1 (`ghrShape`): the conclusion is
        false, so A''s WPd at `spinOb5` is UNPROVABLE.
    (c) `ghrWpdTrivial` -- SANITY TWIN: the same A' IS verifiable at the trivial protocol.
  MILESTONE aspects: hand rows (no fetch/decode, one-byte lock and data); the tagged deps
  `hDeps` are graph data, not tied to the program.  The client proof: one leaf per access, each
  with a ppo admissibility premise about the handle's ANCHOR (rule 5 from the claim for the
  first `ld`, rule 1 `ld → sd`, the reload's internal split); the reload leaf returns the handle
  at an EXISTENTIAL anchor which the release takes; the value conclusion is a row-end readback.

## Deviations from Rocq

1. O2 STAGE C (as `AxSpinProt8` deviation 1): no text oracle -- Rocq's `Tf` arguments of
   `tierA_astep`/`tierA_wpd`/`AxGA2` are gone.
2. CONTEXTS: Rocq section `wpdH`'s variables are explicit leading arguments in Rocq's order
   (`GT nm cpu Hcons t1 tx vx ty vy Hrow`; `hL` takes only `GT t1 tx vx ty vy Hrow`);
   `invGS_gen HasNoLc Σ` ↦ `[InvGS_gen hlc GF]` for any `hlc` (as `AxSpinH2` deviation 2).  The
   local instances `hb_pol` ↦ `splPol GT` and `hb_G` ↦ `shG …` (= `AxSpinProt6.s5G`) are passed
   explicitly; the Rocq notations `GD`/`G`/`R5`/`ΦB`/`TWB`/`O`/`HOw`/`HOr`/`HOp` are unfolded
   (`TWB` is a file-local notation).  Section `runH`'s unused `axirisG Σ` is dropped (as
   `AxSpinH4` deviation 2).  The capstone's `set` locals are the Lean-only defs
   `AxSpinH3.cS0`/`cSN`/`cN`/`cPost` (as `AxSpinProt8`); `HwpA` and the certificate statements
   take `[InvGS_gen .hasNoLC spinGF] [AxannotGS spinGF]` instance binders; `spinΣ` ↦ `spinGF`.
3. lean-sail shapes (as `AxSpinProt7` deviation 3): `hcK` matches `.Ok (w, _)` / `.Err _`;
   `bv_add w B2` ↦ `w + b2`; `B0/B1/B2` ↦ `b0/b1/b2`; `init_regstate` ↦ `zeroRegs`;
   `gt_g GT` ↦ `GT.gtG`; `vm_compute` ↦ `decide +kernel`.
4. `harts_tac` (Rocq Ltac) is not a declaration: each `gh*Harts` is proved by one kernel-decided
   `List.all` check (as `AxSpinProt8.spa5Harts`).

**Rocq → Lean name map.**  `hc_k` `hcK`, `h_tail` `hTail`, `h_reload` `hReload`, `h_store`
`hStore`, `h_cs` `hCs`, `h_m0` `hM0`, `h_row` `hRow`, `h_run` `hRun`, `hL` `hL`, `wpdH` `wpdH`,
`cs_reload_owned` `csReloadOwned`, `h_deps` `hDeps`, `gha` `gha`, `ghf` `ghf`, `ghr` `ghr`,
`gha_cat_t` `ghaCatT`, `ghf_cat_t` `ghfCatT`, `ghr_cat_t` `ghrCatT`, `gha_ctrl_closed`
`ghaCtrlClosed`, `ghf_ctrl_closed` `ghfCtrlClosed`, `ghr_ctrl_closed` `ghrCtrlClosed`,
`gha_harts` `ghaHarts`, `ghf_harts` `ghfHarts`, `ghr_harts` `ghrHarts`, `gh_shape` `ghShape`,
`a5_wpd_at` `a5WpdAt`, `a5_run_at` `a5RunAt`, `gh_premises` `ghPremises`, `gha_sound`
`ghaSound`, `ghf_sound` `ghfSound`, `ghr_shape` `ghrShape`, `ghr_wpd_unprovable`
`ghrWpdUnprovable`, `ghr_wpd_trivial` `ghrWpdTrivial`.  Lean-only (file-qualified):
`AxSpinH3.cS0`/`cSN`/`cN`/`cPost`.

**Dropped:** the local instances `hb_pol`/`hb_G` (inlined), the Ltac `harts_tac` (deviation 4),
the §5 `Check`/`Print Assumptions` lines (the lint's axiom check covers them).  (36 Rocq items =
33 decls + 2 instances + 1 Ltac; 37 Lean = 33 + 4 Lean-only.)

**W13 (I) (plan `notes/weak-allocproc-plan.md` §C W13 (I); [OWN.27]).** the release lemmas' anchor-domain premise is `(lbIsR l || lbIsW l) = true` (was `lbIsMem l = true`): `gwf` admits I/O events, which `fence rw,w` does not order (RVWMO; D48).
-/
import Weak.AxSpinH2
import Weak.AxClsStep2b

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std Iris.Std.PartialMap MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D
open Dtag

/-! # 1. The critical-section program, its row, its run -/

def hcK (m' : BitVec 8 → SailM Unit) (res : Result (BitVec (8 * 1) × Option Bool) Arch.abort) :
    SailM Unit :=
  match res with
  | .Ok (w, _) => m' w
  | .Err _ => hlt
abbrev hTail : SailM Unit := fenceM (relM hlt)
abbrev hReload : SailM Unit := AxSpinProt7.ldM xpaM hTail
/-- `addi` is register-only (no event): the stored value is `v + 2`. -/
abbrev hStore (w : BitVec 8) : SailM Unit := AxSpinProt7.sdM xpaM (w + b2) hReload
abbrev hCs : SailM Unit := .impure (.ok (.memRead 1 64 (l3pRreq l3pAkP xpaM))) (hcK hStore)
/-- HART B: `acquire; ld x (v); sd x (v+2); ld x (v'); fence rw,w; sw lk ← 0; HALT`. -/
abbrev hM0 : SailM Unit := acqRmw hCs hlt

def hRow (t1 tx : Nat) (vx : BitVec 8) (ty : Nat) (vy : BitVec 8) : List Lbl :=
  [.LRmw true false ya [t1] [b0] [b1] .WCplain,
   .LLoad false xa [tx] [vx],
   .LStore false xa [vx + b2] .WCplain,
   .LLoad false xa [ty] [vy],
   .LFence true true false true,
   .LStore false ya [b0] .WCrel]

section runH
variable (cpu : CPU)

theorem hRun (GD : Gdexec) (t1 tx : Nat) (vx : BitVec 8) (ty : Nat) (vy : BitVec 8)
    (Hrow : AxOpsem.grow GD hB = hRow t1 tx vx ty vy) :
    nsteps (astepAnyNfGv GD hB) 7 ⟨hp cpu hM0 zeroRegs, 0⟩ ⟨hp cpu hlt zeroRegs, 6⟩ := by
  refine nsteps_l (runRmwRead cpu GD hB 0 ypaM ypaMRam t1 b0 .WCplain (acqK hCs hlt) zeroRegs
    (by rw [Hrow]; rfl)) ?_
  have H1 := runRmwWrite cpu GD hB 0 ypaM ypaMRam t1 b0 .WCplain
    (if b0 = b0 then hCs else hlt) zeroRegs (by rw [Hrow]; rfl)
  rw [if_pos rfl] at H1
  refine nsteps_l H1 ?_
  have H2 := spRunRead cpu GD hB xpaM xpaMRam [tx] vx (hcK hStore) zeroRegs 1
    (by rw [Hrow]; rfl)
  rw [wob1] at H2
  refine nsteps_l H2 ?_
  refine nsteps_l (spRunWrite cpu GD hB xpaM xpaMRam (vx + b2) hReload zeroRegs 2 .WCplain
    (by rw [Hrow]; rfl)) ?_
  refine nsteps_l (spRunRead cpu GD hB xpaM xpaMRam [ty] vy (fun _ => hTail) zeroRegs 3
    (by rw [Hrow]; rfl)) ?_
  refine nsteps_l (runFence cpu GD hB 4 (relM hlt) zeroRegs (by rw [Hrow]; rfl)) ?_
  refine nsteps_l (spRunWrite cpu GD hB ypaM ypaMRam b0 hlt zeroRegs 5 .WCrel
    (by rw [Hrow]; rfl)) ?_
  exact nsteps_O _

end runH

/-! # 2. HART B's WPd, written ONLY with the handle leaves / contracts -/

section wpdH
variable {hlc : HasLC} {GF : BundledGFunctors.{0,0,0}} [InvGS_gen hlc GF] [AxannotGS GF]
  [AxlogG GF Hent] [SpinlockG GF]

set_option hygiene false in
local notation:max "TWB " s:max => @tierAWpd GF hlc _ _ (splPol GT) (gtAdGd GT) spinN Unit
  (spinOb5 ya xa [ca] cv5) nm s .MaybeStuck hB (fun _ => iprop(⌜vy = vx + b2⌝))

theorem hL (GT : GdexecT) (t1 tx : Nat) (vx : BitVec 8) (ty : Nat) (vy : BitVec 8)
    (Hrow : AxOpsem.grow (gtAdGd GT) hB = hRow t1 tx vx ty vy) (k : Nat) (lb : Lbl) :
    (hRow t1 tx vx ty vy)[k]? = some lb → gxLbl (gtAdGd GT).gdG (hB, k) = some lb := by
  intro Hk
  rw [gxLblGrow, Hrow]
  exact Hk

theorem wpdH (GT : GdexecT) (nm : spinN) (cpu : CPU) (Hcons : rvwmoCatConsistent (gtAdGd GT))
    (t1 tx : Nat) (vx : BitVec 8) (ty : Nat) (vy : BitVec 8)
    (Hrow : AxOpsem.grow (gtAdGd GT) hB = hRow t1 tx vx ty vy) :
    ⊢ isLock (GF := GF) nm.2 ya (spinR5 xa [ca] nm (gtAdGd GT)) -∗ notheld nm.2 ya hB -∗
      TWB ⟨hp cpu hM0 zeroRegs, 0⟩ := by
  have Hl0 := hL GT t1 tx vx ty vy Hrow 0 _ rfl
  have Hl1 := hL GT t1 tx vx ty vy Hrow 1 _ rfl
  have Hl2 := hL GT t1 tx vx ty vy Hrow 2 _ rfl
  have Hlen : (AxOpsem.grow (gtAdGd GT) hB).length = 6 := by rw [Hrow]; rfl
  -- acquire (handle form)
  have H0 : ⊢ isLock (GF := GF) nm.2 ya (spinR5 xa [ca] nm (gtAdGd GT)) -∗ notheld nm.2 ya hB -∗
      (⌜lkClaim ya (gtAdGd GT).gdG (hB, 0) (gwriteAt (gtAdGd GT).gdG t1)⌝ -∗
        AxAnnot.annotOwn (hB, 0)
          iprop(locked nm.2 ya hB (hB, 0) ∗ RL nm.1 (gtAdGd GT) [ca] (hB, 0)) -∗
        hdl (Rbo nm.1 (gtAdGd GT)) xa (hB, 0) none -∗
        ∀ rs : RegFile, TWB ⟨hp cpu hCs rs, 1⟩) -∗
      ∀ rs : RegFile, TWB ⟨hp cpu hM0 rs, 0⟩ :=
    wpdAcquireH (hlc := hlc) xa [ca] cv5 GT nm cpu Hcons yaNX5 hB 0 t1 hCs hlt _
      (by rw [Hlen]; decide) (by rw [Hrow]; rfl)
  -- ld x : the handle moves claim → (B,1) (ppo rule 5)
  have Hin1 : ((hB, 0) : Geid) ∈ @Axpol.lobp (splPol GT) (gtAdGd GT) (hB, 1) :=
    acqLobp (gtAdGd GT) Hcons hB 0 1 ya [t1] [b0] [b1] .WCplain _ Hl0 Hl1 rfl (by decide)
  have Hfw1 : ∀ w v', gwritesByte (gtAdGd GT).gdG w (paZ xpaM) v' →
      WeakRvwmoGraph.gpo (gtAdGd GT).gdG w (hB, 1) → gmoLt (gtAdGd GT).gdG w (hB, 1) := by
    rintro ⟨wi, wk⟩ v' Hw ⟨Hh, Hlt, -⟩
    exfalso
    simp only at Hh Hlt
    subst Hh
    obtain rfl : wk = 0 := by omega
    obtain ⟨-, -, Hsg, -⟩ := gwbRmw _ _ _ _ _ _ _ Hl0
    exact xaNeYa (Hsg _ _ Hw).1
  have H1 : ⊢ hdl (Rbo (GF := GF) nm.1 (gtAdGd GT)) xa (hB, 0) none -∗
      (hdl (Rbo nm.1 (gtAdGd GT)) xa (hB, 1) (some vx) -∗
        AxAnnot.annotOwn (hB, 1)
          iprop(⌜∀ v0, (none : Option (BitVec 8)) = some v0 → vx = v0⌝) -∗
        ∀ rs : RegFile, TWB ⟨hp cpu (hStore vx) rs, 2⟩) -∗
      ∀ rs : RegFile, TWB ⟨hp cpu hCs rs, 1⟩ :=
    wpdLdOwn (hlc := hlc) (pol := splPol GT) (gtAdGd GT) spinN Unit (spinOb5 ya xa [ca] cv5) nm
      (splAxpolWf GT) cpu (Rbo nm.1 (gtAdGd GT)) (okr5 xa [ca]) (splPolGmo GT)
      (fe5hRead ya xa [ca] cv5 GT nm Hcons yaNX5) hB 1 xpaM xpaMRam (hcK hStore) tx vx (hB, 0)
      none _ (by rw [Hlen]; decide) (by rw [Hrow]; rfl) xaX5 Hin1 Hfw1
  -- sd x (v+2) : the handle moves (B,1) → (B,2) (ppo rule 1)
  have Hok2 : okw5 xa [ca] cv5 GT (hB, 2) (paZ xpaM) (vx + b2) := by
    refine ⟨xaX5, cpuOkNw [ca] cv5 _ _ (fun a v' Ha Hw => ?_)⟩
    rw [List.mem_singleton] at Ha
    subst Ha
    exact caNeXa ((gwbStore _ _ _ _ _ Hl2).2 _ _ Hw).1
  have Hin2 : ((hB, 1) : Geid) ∈ @Axpol.lobp (splPol GT) (gtAdGd GT) (hB, 2) :=
    locLobp (gtAdGd GT) Hcons (hB, 1) (hB, 2) _ xa (vx + b2) Hl1 rfl
      (gpoRow (gtAdGd GT) hB 1 2 _ _ Hl1 Hl2 (by decide))
      (.inr ⟨tx, vx, grbLoad _ _ _ _ _ Hl1⟩) (gwbStore _ _ _ _ _ Hl2).1
  have H2 : ⊢ hdl (Rbo (GF := GF) nm.1 (gtAdGd GT)) xa (hB, 1) (some vx) -∗
      (hdl (Rbo nm.1 (gtAdGd GT)) xa (hB, 2) (some (vx + b2)) -∗
        ∀ rs : RegFile, TWB ⟨hp cpu hReload rs, 3⟩) -∗
      ∀ rs : RegFile, TWB ⟨hp cpu (hStore vx) rs, 2⟩ :=
    wpdSdOwn (hlc := hlc) (pol := splPol GT) (gtAdGd GT) spinN Unit (spinOb5 ya xa [ca] cv5) nm
      (splAxpolWf GT) cpu (Rbo nm.1 (gtAdGd GT)) (okw5 xa [ca] cv5 GT) (splPolGmo GT)
      (fe5hWrite ya xa [ca] cv5 GT nm Hcons yaNX5) hB 2 xpaM xpaMRam (vx + b2) hReload .WCplain
      (hB, 1) (some vx) _ (by rw [Hlen]; decide) (by rw [Hrow]; rfl) Hok2 Hin2
  -- ld x (reload) : the forwarded / ordered case split
  have Hnoint : ∀ w v', gwritesByte (gtAdGd GT).gdG w (paZ xpaM) v' →
      WeakRvwmoGraph.gpo (gtAdGd GT).gdG (hB, 2) w →
      WeakRvwmoGraph.gpo (gtAdGd GT).gdG w (hB, 3) → False := by
    rintro ⟨wi, wk⟩ v' - ⟨-, H1, -⟩ ⟨-, H2, -⟩
    simp only at H1 H2
    omega
  have H3 : ⊢ hdl (Rbo (GF := GF) nm.1 (gtAdGd GT)) xa (hB, 2) (some (vx + b2)) -∗
      ((∃ (e' : Geid), ⌜e' = (hB, 2) ∨ e' = (hB, 3)⌝ ∗
          hdl (Rbo nm.1 (gtAdGd GT)) xa e' (some (vx + b2))) -∗
        AxAnnot.annotOwn (hB, 3) iprop(⌜vy = vx + b2⌝) -∗
        ∀ rs : RegFile, TWB ⟨hp cpu hTail rs, 4⟩) -∗
      ∀ rs : RegFile, TWB ⟨hp cpu hReload rs, 3⟩ :=
    wpdReloadOwn (hlc := hlc) (pol := splPol GT) (gtAdGd GT) spinN Unit (spinOb5 ya xa [ca] cv5)
      nm (splAxpolWf GT) cpu Hcons (Rbo nm.1 (gtAdGd GT)) (okr5 xa [ca]) (splPolGmo GT)
      (splPolIntro GT) (fe5hRead ya xa [ca] cv5 GT nm Hcons yaNX5)
      (fe5hPlain ya xa [ca] cv5 GT nm Hcons yaNX5) hB 2 3 xpaM xpaMRam (fun _ => hTail)
      (vx + b2) .WCplain ty vy _ (by rw [Hlen]; decide) (by rw [Hrow]; rfl) (by rw [Hrow]; rfl)
      (by decide) xaX5 Hnoint
  -- release: `locked` + lk->cpu from the claim, `x` from wherever the handle is
  have H4 : ∀ e' : Geid, (e' = (hB, 2) ∨ e' = (hB, 3)) →
      ⊢ isLock (GF := GF) nm.2 ya (spinR5 xa [ca] nm (gtAdGd GT)) -∗
        AxAnnot.annotOwn (hB, 0)
          iprop(locked nm.2 ya hB (hB, 0) ∗ RL nm.1 (gtAdGd GT) [ca] (hB, 0)) -∗
        hdl (Rbo nm.1 (gtAdGd GT)) xa e' (some (vx + b2)) -∗
        (AxAnnot.annotOwn (hB, 5) (notheld nm.2 ya hB) -∗
          ∀ rs : RegFile, TWB ⟨hp cpu hlt rs, 6⟩) -∗
        ∀ rs : RegFile, TWB ⟨hp cpu hTail rs, 4⟩ := by
    intro e' He'
    have Hce : ((hB, 0) : Geid) ≠ e' := by
      rcases He' with rfl | rfl <;> decide
    have Hev : ∀ e : Geid, e = (hB, 0) ∨ e = e' → e.1 = hB ∧ e.2 < 4 ∧
        ∃ l, (AxOpsem.grow (gtAdGd GT) hB)[e.2]? = some l ∧ (lbIsR l || lbIsW l) = true := by
      intro e He
      rcases He with rfl | rfl
      · exact ⟨rfl, by decide, _, by rw [Hrow]; rfl, rfl⟩
      · rcases He' with rfl | rfl
        · exact ⟨rfl, by decide, _, by rw [Hrow]; rfl, rfl⟩
        · exact ⟨rfl, by decide, _, by rw [Hrow]; rfl, rfl⟩
    exact wpdReleaseH (hlc := hlc) xa [ca] cv5 GT nm cpu Hcons yaNX5 hB 4 hlt (hB, 0) e'
      (some (vx + b2)) _ (by rw [Hlen]; decide) (by rw [Hlen]; decide) (by rw [Hrow]; rfl)
      (by rw [Hrow]; rfl) Hce Hev
  -- row end: the conclusion READ BACK from the reload's annotation
  have H5 : ⊢ AxAnnot.annotOwn (GF := GF) (hB, 3) iprop(⌜vy = vx + b2⌝) -∗
      ∀ rs : RegFile, TWB ⟨hp cpu hlt rs, 6⟩ :=
    shHltReadback (hlc := hlc) (pol := splPol GT) (gtAdGd GT) spinN Unit (spinOb5 ya xa [ca] cv5)
      nm cpu hB 6 (hB, 3) rfl iprop(⌜vy = vx + b2⌝) (vy = vx + b2) .rfl
  iintro #Hil Hnh
  iapply H0 $$ Hil Hnh [] %zeroRegs
  iintro %_ Hc Hx %rs
  iapply H1 $$ Hx [Hc] %rs
  iintro Hx _ %rs
  iapply H2 $$ Hx [Hc] %rs
  iintro Hx %rs
  iapply H3 $$ Hx [Hc] %rs
  iintro ⟨%e', %He', Hx⟩ Hr %rs
  iapply (H4 e' He') $$ Hil Hc Hx [Hr] %rs
  iintro _ %rs
  iapply H5 $$ Hr %rs

end wpdH

/-! # 3. THE CAPSTONE -/

/-- Lean-only (Rocq `set s0`). -/
def AxSpinH3.cS0 (sA0 : Athread) (i : Agent) : Athread :=
  if i = hA then sA0 else ⟨hp cpu0 hM0 zeroRegs, 0⟩
/-- Lean-only (Rocq `set sN`). -/
def AxSpinH3.cSN (sAN : Athread) (i : Agent) : Athread :=
  if i = hA then sAN else ⟨hp cpu0 hlt zeroRegs, 6⟩
/-- Lean-only (Rocq `set nf`). -/
def AxSpinH3.cN (nA : Nat) (i : Agent) : Nat := if i = hA then nA else 7
/-- Lean-only (Rocq `set post`). -/
def AxSpinH3.cPost (vx vy : BitVec 8) (i : Agent) (_ : Athread) : Prop :=
  if i = hB then vy = vx + b2 else True

theorem csReloadOwned (GT : GdexecT)
    (HconsT : rvwmoCatConsistentT GT) (Hcl : ctrlClosed GT)
    (Hharts : ∀ e, e ∈ GT.gtG.gxGmo → e.1 = hA ∨ e.1 = hB)
    (t1 tx : Nat) (vx : BitVec 8) (ty : Nat) (vy : BitVec 8)
    (HrowB : AxOpsem.grow (gtAdGd GT) hB = hRow t1 tx vx ty vy)
    (sA0 sAN : Athread) (nA : Nat)
    (HrunA : ∀ (_ : AxannotGS spinGF) (nm : spinN),
      nsteps (tierAAstep (gtAdGd GT) nm hA) nA sA0 sAN)
    (HkA : sA0.atK = 0) (HendA : sAN.atK = (AxOpsem.grow (gtAdGd GT) hA).length)
    (HwpA : ∀ [InvGS_gen .hasNoLC spinGF] [AxannotGS spinGF] (nm : spinN),
      ⊢ spinInit5 ya xa [ca] (gtAdGd GT) nm hA -∗
        @tierAWpd spinGF .hasNoLC _ _ (splPol GT) (gtAdGd GT) spinN Unit
          (spinOb5 ya xa [ca] cv5) nm sA0 .MaybeStuck hA (fun _ => iprop(True))) :
    vy = vx + b2 := by
  have Hin01 : ∀ i : Agent, i ∈ [hA, hB] → i = hA ∨ i = hB := by
    intro i Hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at Hi
    exact Hi
  have Hnd : [hA, hB].Nodup := by decide
  have Hharts' : ∀ e, e ∈ GT.gtG.gxGmo → e.1 ∈ [hA, hB] := by
    intro e He
    rcases Hharts e He with H | H <;> rw [H] <;> simp
  have Hcons := catTAd GT HconsT
  have Hrun : ∀ (_ : AxannotGS spinGF) (nm : spinN) i, i ∈ [hA, hB] →
      nsteps (tierAAstep (gtAdGd GT) nm i) (AxSpinH3.cN nA i) (AxSpinH3.cS0 sA0 i)
        (AxSpinH3.cSN sAN i) := by
    intro Hann nm i Hi
    rcases Hin01 i Hi with rfl | rfl
    · exact HrunA Hann nm
    · exact hRun cpu0 (gtAdGd GT) t1 tx vx ty vy HrowB
  have Hk0 : ∀ i, i ∈ [hA, hB] → (AxSpinH3.cS0 sA0 i).atK = 0 := by
    intro i Hi
    rcases Hin01 i Hi with rfl | rfl
    · exact HkA
    · rfl
  have Hend : ∀ i, i ∈ [hA, hB] →
      (AxSpinH3.cSN sAN i).atK = (AxOpsem.grow (gtAdGd GT) i).length := by
    intro i Hi
    rcases Hin01 i Hi with rfl | rfl
    · exact HendA
    · show 6 = (AxOpsem.grow (gtAdGd GT) hB).length
      rw [HrowB]
      rfl
  have Hwp : ∀ [InvGS_gen .hasNoLC spinGF] [AxannotGS spinGF] (nm : spinN),
      ⊢ ([∗list] i ∈ [hA, hB], spinInit5 ya xa [ca] (gtAdGd GT) nm i) -∗
        [∗list] i ∈ [hA, hB],
          @tierAWpd spinGF .hasNoLC _ _ (splPol GT) (gtAdGd GT) spinN Unit
            (spinOb5 ya xa [ca] cv5) nm (AxSpinH3.cS0 sA0 i) .MaybeStuck i
            (fun s => iprop(⌜AxSpinH3.cPost vx vy i s⌝)) := by
    intro Hinv Hann nm
    iintro HI
    icases (AxTokLedgerMp.bigSepLPair hA hB
      (fun i => spinInit5 (GF := spinGF) ya xa [ca] (gtAdGd GT) nm i)).1 $$ HI with ⟨HA, HB⟩
    iapply (AxTokLedgerMp.bigSepLPair hA hB _).2
    rw [show AxSpinH3.cS0 sA0 hA = sA0 from if_pos rfl,
      show AxSpinH3.cS0 sA0 hB = ⟨hp cpu0 hM0 zeroRegs, 0⟩ from if_neg (by decide)]
    isplitl [HA]
    · iapply (AxSpinWit.tierAWpdMono (hlc := .hasNoLC) (pol := splPol GT) (gtAdGd GT) spinN Unit
        (spinOb5 ya xa [ca] cv5) nm sA0 .MaybeStuck hA (fun _ => iprop(True))
        (fun s => iprop(⌜AxSpinH3.cPost vx vy hA s⌝))
        (fun _ => pure_mono (fun _ => by
          unfold AxSpinH3.cPost; rw [if_neg (by decide)]; trivial)))
      iapply HwpA nm $$ HA
    · iapply (AxSpinWit.tierAWpdMono (hlc := .hasNoLC) (pol := splPol GT) (gtAdGd GT) spinN Unit
        (spinOb5 ya xa [ca] cv5) nm ⟨hp cpu0 hM0 zeroRegs, 0⟩ .MaybeStuck hB
        (fun _ => iprop(⌜vy = vx + b2⌝))
        (fun s => iprop(⌜AxSpinH3.cPost vx vy hB s⌝))
        (fun _ => pure_mono (fun Hv => by
          unfold AxSpinH3.cPost; rw [if_pos rfl]; exact Hv)))
      unfold spinInit5
      icases HB with ⟨Hil, Hnh⟩
      iapply (wpdH (hlc := .hasNoLC) (GF := spinGF) GT nm cpu0 Hcons t1 tx vx ty vy HrowB)
        $$ Hil Hnh
  have HxC : xa ∉ [ca] := by
    rw [List.mem_singleton]
    exact fun h => caNeXa h.symm
  have HndC : [ca].Nodup := by simp
  have Hfin := @tierAAdequacyAnnGateT spinGF _ _ (splPol GT) GT spinN Unit
    (spinOb5 ya xa [ca] cv5) (spinInit5 ya xa [ca] (gtAdGd GT)) (splAxpolWf GT) HconsT [hA, hB]
    Hnd Hharts' (AxSpinH3.cS0 sA0) (AxSpinH3.cSN sAN) (AxSpinH3.cN nA) Hrun Hk0 Hend
    (AxSpinH3.cPost vx vy) Hwp
    (spinHobAlloc5 (GF := spinGF) ya xa [ca] cv5 (gtAdGd GT) [hA, hB] Hnd HxC HndC)
    (splHok GT HconsT Hcl) hB (by simp)
  exact (if_pos rfl : AxSpinH3.cPost vx vy hB _ = (vy = vx + b2)) ▸ Hfin

/-! # 4. CERTIFICATES -/

/-- B's claim RMW controls every po-later store; B's first load feeds the stored value (data). -/
def hDeps : List Tdep :=
  [(((hB, 0), (hB, 2)), DTctrl), (((hB, 0), (hB, 5)), DTctrl),
   (((hB, 1), (hB, 2)), DTdata)]

/-- (a1) ORDERED: A (= `a5`: claim; cpu := cv A; x := 1; cpu := 0; release) then B claims A's
release, reads x = 1, stores 3, the reload is gmo-AFTER the store and reads it. -/
def gha : GdexecT :=
  mkgt [a5Row 0, hRow 5 3 b1 7 (b1 + b2)]
    [(hA, 0), (hA, 1), (hA, 2), (hA, 3), (hA, 5),
     (hB, 0), (hB, 1), (hB, 2), (hB, 3), (hB, 5)] hDeps

/-- (a2) FORWARDED: the same rows, the reload gmo-BEFORE the store (it reads the store by
forwarding). -/
def ghf : GdexecT :=
  mkgt [a5Row 0, hRow 5 3 b1 7 (b1 + b2)]
    [(hA, 0), (hA, 1), (hA, 2), (hA, 3), (hA, 5),
     (hB, 0), (hB, 1), (hB, 3), (hB, 2), (hB, 5)] hDeps

/-- (b) RACE: A' (= `r5`: claim; fence; release; x := 1 AFTER the release).  B claims A''s
release, reads x = 0 (image), stores 2, A''s x := 1 lands gmo-between B's store and B's reload,
which reads 1. -/
def ghr : GdexecT :=
  mkgt [r5Row, hRow 2 0 b0 5 b1]
    [(hA, 0), (hA, 2), (hB, 0), (hB, 1), (hB, 2), (hA, 3), (hB, 3), (hB, 5)] hDeps

theorem ghaCatT : rvwmoCatConsistentT gha := catTConsistentBSound _ (by decide +kernel)
theorem ghfCatT : rvwmoCatConsistentT ghf := catTConsistentBSound _ (by decide +kernel)
theorem ghrCatT : rvwmoCatConsistentT ghr := catTConsistentBSound _ (by decide +kernel)
theorem ghaCtrlClosed : ctrlClosed gha := ctrlClosedBSound _ ghaCatT.1 (by decide +kernel)
theorem ghfCtrlClosed : ctrlClosed ghf := ctrlClosedBSound _ ghfCatT.1 (by decide +kernel)
theorem ghrCtrlClosed : ctrlClosed ghr := ctrlClosedBSound _ ghrCatT.1 (by decide +kernel)

theorem ghaHarts : ∀ e, e ∈ gha.gtG.gxGmo → e.1 = hA ∨ e.1 = hB := by
  intro e He
  have h : gha.gtG.gxGmo.all (fun e : Geid => decide (e.1 = hA ∨ e.1 = hB)) = true := by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.1 h e He)

theorem ghfHarts : ∀ e, e ∈ ghf.gtG.gxGmo → e.1 = hA ∨ e.1 = hB := by
  intro e He
  have h : ghf.gtG.gxGmo.all (fun e : Geid => decide (e.1 = hA ∨ e.1 = hB)) = true := by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.1 h e He)

theorem ghrHarts : ∀ e, e ∈ ghr.gtG.gxGmo → e.1 = hA ∨ e.1 = hB := by
  intro e He
  have h : ghr.gtG.gxGmo.all (fun e : Geid => decide (e.1 = hA ∨ e.1 = hB)) = true := by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.1 h e He)

/-- The two cases of the reload leaf are REALLY exercised: on `gha` the store is gmo-before the
reload (handle moved through the owned-read flow equation); on `ghf` it is not, and the reload
reads the store (forwarding).  B's first load reads A's `x := 1` on both. -/
theorem ghShape :
    gmoLt gha.gtG (hB, 2) (hB, 3) ∧ grfAt gha.gtG xa (hB, 2) (hB, 3) ∧
    ¬ gmoLt ghf.gtG (hB, 2) (hB, 3) ∧ grfAt ghf.gtG xa (hB, 2) (hB, 3) ∧
    grfAt gha.gtG xa (hA, 2) (hB, 1) ∧ grfAt ghf.gtG xa (hA, 2) (hB, 1) ∧
    grfAt gha.gtG ya (hA, 5) (hB, 0) ∧ grfAt ghf.gtG ya (hA, 5) (hB, 0) := by
  refine ⟨(gmoLtBSpec _ _ _).1 (by decide +kernel), (grfAtBSpec _ _ _ _).1 (by decide +kernel),
    fun Hx => ?_, (grfAtBSpec _ _ _ _).1 (by decide +kernel),
    (grfAtBSpec _ _ _ _).1 (by decide +kernel), (grfAtBSpec _ _ _ _).1 (by decide +kernel),
    (grfAtBSpec _ _ _ _).1 (by decide +kernel), (grfAtBSpec _ _ _ _).1 (by decide +kernel)⟩
  have Hb := (gmoLtBSpec _ _ _).2 Hx
  have Hf : gmoLtB ghf.gtG (hB, 2) (hB, 3) = false := by decide +kernel
  rw [Hf] at Hb
  cases Hb

theorem a5WpdAt (GT : GdexecT) (Hc : rvwmoCatConsistentT GT)
    (Hr : AxOpsem.grow (gtAdGd GT) hA = a5Row 0) :
    ∀ [InvGS_gen .hasNoLC spinGF] [AxannotGS spinGF] (nm : spinN),
      ⊢ spinInit5 ya xa [ca] (gtAdGd GT) nm hA -∗
        @tierAWpd spinGF .hasNoLC _ _ (splPol GT) (gtAdGd GT) spinN Unit
          (spinOb5 ya xa [ca] cv5) nm ⟨hp cpu0 a5M0 zeroRegs, 0⟩ .MaybeStuck hA
          (fun _ => iprop(True)) := by
  intro _ _ nm
  unfold spinInit5
  iintro ⟨Hil, Hnh⟩
  iapply (wpdA5 (hlc := .hasNoLC) (GF := spinGF) GT nm cpu0 (catTAd GT Hc) 0 Hr) $$ Hil Hnh

theorem a5RunAt (GT : GdexecT) (Hr : AxOpsem.grow (gtAdGd GT) hA = a5Row 0) :
    ∀ (_ : AxannotGS spinGF) (nm : spinN),
      nsteps (tierAAstep (gtAdGd GT) nm hA) 7
        ⟨hp cpu0 a5M0 zeroRegs, 0⟩ ⟨hp cpu0 hlt zeroRegs, 6⟩ :=
  fun _ _ => a5Run cpu0 (gtAdGd GT) 0 Hr

/-- (a) SATISFIABILITY -- EVERY premise of `csReloadOwned` on `gha` (ordered) and on `ghf`
(forwarded), A PROVED at the real protocol. -/
theorem ghPremises (GT : GdexecT) :
    GT = gha ∨ GT = ghf →
    rvwmoCatConsistentT GT ∧ ctrlClosed GT ∧
    (∀ e, e ∈ GT.gtG.gxGmo → e.1 = hA ∨ e.1 = hB) ∧
    AxOpsem.grow (gtAdGd GT) hB = hRow 5 3 b1 7 (b1 + b2) ∧
    (∀ (_ : AxannotGS spinGF) (nm : spinN),
      nsteps (tierAAstep (gtAdGd GT) nm hA) 7
        ⟨hp cpu0 a5M0 zeroRegs, 0⟩ ⟨hp cpu0 hlt zeroRegs, 6⟩) ∧
    (⟨hp cpu0 a5M0 zeroRegs, 0⟩ : Athread).atK = 0 ∧
    (⟨hp cpu0 hlt zeroRegs, 6⟩ : Athread).atK = (AxOpsem.grow (gtAdGd GT) hA).length ∧
    (∀ [InvGS_gen .hasNoLC spinGF] [AxannotGS spinGF] (nm : spinN),
      ⊢ spinInit5 ya xa [ca] (gtAdGd GT) nm hA -∗
        @tierAWpd spinGF .hasNoLC _ _ (splPol GT) (gtAdGd GT) spinN Unit
          (spinOb5 ya xa [ca] cv5) nm ⟨hp cpu0 a5M0 zeroRegs, 0⟩ .MaybeStuck hA
          (fun _ => iprop(True))) := by
  rintro (rfl | rfl)
  · exact ⟨ghaCatT, ghaCtrlClosed, ghaHarts, rfl, a5RunAt gha rfl, rfl, rfl,
      a5WpdAt gha ghaCatT rfl⟩
  · exact ⟨ghfCatT, ghfCtrlClosed, ghfHarts, rfl, a5RunAt ghf rfl, rfl, rfl,
      a5WpdAt ghf ghfCatT rfl⟩

/-- The capstone fires on both; the conclusion is TRUE there (`3 = 1 + 2`). -/
theorem ghaSound : b1 + b2 = b1 + b2 :=
  csReloadOwned gha ghaCatT ghaCtrlClosed ghaHarts 5 3 b1 7 (b1 + b2) rfl _ _ 7
    (a5RunAt gha rfl) rfl rfl (a5WpdAt gha ghaCatT rfl)

theorem ghfSound : b1 + b2 = b1 + b2 :=
  csReloadOwned ghf ghfCatT ghfCtrlClosed ghfHarts 5 3 b1 7 (b1 + b2) rfl _ _ 7
    (a5RunAt ghf rfl) rfl rfl (a5WpdAt ghf ghfCatT rfl)

/-- (b) THE RACE: on the consistent, ctrl-closed `ghr` the reload reads A''s post-release
`x := 1` ≠ B's own `0 + 2`; every other premise holds, so A''s WPd at `spinOb5` is UNPROVABLE. -/
theorem ghrShape :
    grfAt ghr.gtG ya (hA, 2) (hB, 0) ∧ grfAt ghr.gtG xa (hA, 3) (hB, 3) ∧
    gmoLt ghr.gtG (hB, 2) (hA, 3) ∧ gmoLt ghr.gtG (hA, 3) (hB, 3) ∧
    b1 ≠ b0 + b2 :=
  ⟨(grfAtBSpec _ _ _ _).1 (by decide +kernel), (grfAtBSpec _ _ _ _).1 (by decide +kernel),
    (gmoLtBSpec _ _ _).1 (by decide +kernel), (gmoLtBSpec _ _ _).1 (by decide +kernel),
    by decide⟩

theorem ghrWpdUnprovable :
    ¬ (∀ [InvGS_gen .hasNoLC spinGF] [AxannotGS spinGF] (nm : spinN),
        ⊢ spinInit5 ya xa [ca] (gtAdGd ghr) nm hA -∗
          @tierAWpd spinGF .hasNoLC _ _ (splPol ghr) (gtAdGd ghr) spinN Unit
            (spinOb5 ya xa [ca] cv5) nm ⟨hp cpu0 r5M0 zeroRegs, 0⟩ .MaybeStuck hA
            (fun _ => iprop(True))) := by
  intro Hwp
  have Hrun : ∀ (_ : AxannotGS spinGF) (nm : spinN),
      nsteps (tierAAstep (gtAdGd ghr) nm hA) 5
        ⟨hp cpu0 r5M0 zeroRegs, 0⟩ ⟨hp cpu0 hlt zeroRegs, 4⟩ :=
    fun _ _ => r5Run cpu0 (gtAdGd ghr) rfl
  have Hv := csReloadOwned ghr ghrCatT ghrCtrlClosed ghrHarts 2 0 b0 5 b1 rfl _ _ 5 Hrun rfl rfl
    Hwp
  exact ghrShape.2.2.2.2 Hv

/-- (c) SANITY TWIN: the same A' IS verifiable at the trivial protocol. -/
theorem ghrWpdTrivial :
    ∀ [InvGS_gen .hasNoLC spinGF] [AxannotGS spinGF] (nm : Unit),
      ⊢ (iprop(emp) : IProp spinGF) -∗
        @tierAWpd spinGF .hasNoLC _ _ (splPol ghr) (gtAdGd ghr) Unit Unit trivOb nm
          ⟨hp cpu0 r5M0 zeroRegs, 0⟩ .MaybeStuck hA (fun _ => iprop(True)) := by
  intro _ _ nm
  cases nm
  iintro _
  iapply (wpdR5Triv (hlc := .hasNoLC) (GF := spinGF) ghr cpu0 rfl)

end Weak
