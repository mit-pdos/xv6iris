/-
Weak: **Phase 2b, part 3 of the spinlock plan -- CERTIFICATE 1: a critical section on a 4-BYTE
protected word with TWO same-address loads.**  Hart B runs
`acquire; lw x (vs1); lw x (vs2); addiw (+1); sw x (vs1 + 1); fence rw,w; sw lk ← 0` (hand `Pexv6`
nodes: the 1-byte lock instructions of `AxSpinProt7`, the 4-byte `memRead 4`/`memWrite 4` nodes of
`AxSpinH4`; row `g6Row`).  The WPd `wpdG6` is written ONLY with the handle surface:
`wpdAcquireH6`, `hdlwSplit` (the word handle split into two READ HALVES at the claim),
`wpdLdOwnN` ×2 (each `lw` draws a half from the claim -- ppo rule 5; the two loads are NOT ordered
with each other), `wpdSdOwnN2` (the store recombines the halves -- ppo rule 1 from each load -- and
deposits that their values AGREE), `wpdReleaseH6`; the post `⌜vs2 = vs1⌝` is READ BACK at the row
end from the store's annotation.

Rocq: `iris/AxSpinH6.v` @ xxvzwolszwmp.

## The Rocq header, in substance

PROVED
  `csDblLoad`: for ANY hart A with a WPd at `spinOb6 ya (clRange xa 4) [ca] cv5` from `spinInit6`
    and any run, on every tagged-consistent ctrl-closed 2-hart graph where B's row is
    `g6Row t1 ts1 vs1 ts2 vs2` (all lists of length 4): `vs2 = vs1`.
  CERTIFICATES
    (a) `gs6Premises`: EVERY premise on the concrete `gs6` (A = `a6`: acquire; sw x ← 1 (4
        bytes); fence; release -- PROVED at the real protocol, `wpdA6`); `gs6Shape`: B claims A's
        release, both loads read A's word; `gs6Sound`: the capstone fires.
    (b) `gr6WpdUnprovable` -- RACE: A' = `AxSpinProt7`'s `r5` (writes byte `x` AFTER its
        release); on the consistent ctrl-closed `gr6` B's first load reads 0, A''s write lands
        gmo-BETWEEN B's two loads, the second reads 1 (`gr6Shape`): the conclusion is false, so
        A''s WPd at `spinOb6` is UNPROVABLE.
    (c) `gr6WpdTrivial` -- SANITY TWIN: the same A' IS verifiable at the trivial protocol.
  MEANINGFUL in the Theorem-2 sense (A arbitrary; (b) shows the conclusion is false without
  ownership).  MILESTONE aspects: hand rows (no fetch/decode, one-byte lock), the tagged deps
  `g6Deps` are graph data.

## Deviations from Rocq

1. O2 STAGE C (as `AxSpinH3` deviation 1): no text oracle -- Rocq's `Tf` arguments of
   `tierA_astep`/`tierA_wpd`/`AxGA2` are gone.
2. CONTEXTS (as `AxSpinH3` deviation 2): Rocq section variables are explicit leading arguments in
   Rocq's order (`wpdA6`: `GT nm cpu Hcons tA Hrow`; `wpdG6`: `GT nm cpu Hcons t1 ts1 vs1 ts2 vs2
   Hrow Hts1 Hvs1 Hts2 Hvs2`; `gL`/`g6Nopre`: `GT t1 ts1 vs1 ts2 vs2 Hrow`, the only ones their
   `Proof using` names); `invGS_gen HasNoLc Σ` ↦ `[InvGS_gen hlc GF]` for any `hlc`.  The local
   instance `g6_G` and the policy `l6_pol` ↦ `splPol GT` passed explicitly; the Rocq notations
   `XS6`/`OB6`/`R6`/`TW6`/`ΦB`/`TWB` are unfolded (`TWA`/`TWB` file-local notations).  Section
   `runs6`'s unused `axirisG Σ` is dropped.  The capstone's `set` locals are the Lean-only defs
   `AxSpinH6.cS0`/`cSN`/`cN`/`cPost`; `HwpA` and the certificate statements take
   `[InvGS_gen .hasNoLC spinGF] [AxannotGS spinGF]` instance binders; `spinΣ` ↦ `spinGF`.
3. lean-sail shapes (as `AxSpinH3` deviation 3 / `AxSpinH4`): `g6K1`/`g6K2` match `.Ok (w, _)` /
   `.Err _`; `bv_add w one4` ↦ `w + one4`; `BV 32 1` ↦ `1 : BitVec (8 * 4)`; `B0/B1` ↦ `b0/b1`;
   `init_regstate` ↦ `zeroRegs`; `gt_g GT` ↦ `GT.gtG`; `1/2 : Qp` ↦ `Qp.half 1`;
   `vm_compute`/`vmr` ↦ `decide +kernel`; `N.to_nat 4` ↦ `4`.
4. `harts6_tac` (Rocq Ltac) is not a declaration: each `gs6Harts`/`gr6Harts` is one
   kernel-decided `List.all` check (as `AxSpinH3`).

**Rocq → Lean name map.**  `xa_val` `xaVal`, `ya_val` `yaVal`, `ca_val` `caVal`, `xs6_range`
`xs6Range`, `XS6_X` `XS6X`, `XS6_ne_ya` `XS6NeYa`, `ya_nX6` `yaNX6`, `XS6_nodup` `XS6Nodup`,
`XS6_disj` `XS6Disj`, `ldst_lobp` `ldstLobp`, `one4` `one4`, `g6_tail` `g6Tail`, `g6_k2` `g6K2`,
`g6_k1` `g6K1`, `g6_cs` `g6Cs`, `g6_m0` `g6M0`, `g6_val` `g6Val`, `g6_row` `g6Row`, `a6_cs`
`a6Cs`, `a6_m0` `a6M0`, `a6_row` `a6Row`, `g6_run` `g6Run`, `a6_run` `a6Run`, `wpdA6` `wpdA6`,
`gL` `gL`, `g6_nopre` `g6Nopre`, `wpdG6` `wpdG6`, `cs_dbl_load` `csDblLoad`, `g6_deps` `g6Deps`,
`w1000` `w1000`, `w0000` `w0000`, `w1000'` `w1000'`, `gs6` `gs6`, `gr6` `gr6`, `gs6_cat_t`
`gs6CatT`, `gr6_cat_t` `gr6CatT`, `gs6_ctrl_closed` `gs6CtrlClosed`, `gr6_ctrl_closed`
`gr6CtrlClosed`, `gs6_harts` `gs6Harts`, `gr6_harts` `gr6Harts`, `gs6_shape` `gs6Shape`,
`a6_wpd_at` `a6WpdAt`, `a6_run_at` `a6RunAt`, `gs6_premises` `gs6Premises`, `gs6_sound`
`gs6Sound`, `gr6_shape` `gr6Shape`, `gr6_wpd_unprovable` `gr6WpdUnprovable`, `gr6_wpd_trivial`
`gr6WpdTrivial`.  Lean-only (file-qualified): `AxSpinH6.cS0`/`cSN`/`cN`/`cPost`.

**Dropped:** the local instance `g6_G` (inlined), the Ltac `harts6_tac` (deviation 4), the §5
`Check`/`Print Assumptions` lines (the lint's axiom check covers them).  (50 Rocq items = 48 decls
+ 1 instance + 1 Ltac; 52 Lean = 48 + 4 Lean-only.)

**W13 (I) (plan `notes/weak-allocproc-plan.md` §C W13 (I); [OWN.27]).** the release lemmas' anchor-domain premise is `(lbIsR l || lbIsW l) = true` (was `lbIsMem l = true`): `gwf` admits I/O events, which `fence rw,w` does not order (RVWMO; D48).
-/
import Weak.AxSpinH5
import Weak.AxClsStep2b

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std Iris.Std.PartialMap MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D
open Dtag

/-! # 1. Addresses, the instance, programs, rows, runs -/

theorem xaVal : xa = 0x80001000 := by decide +kernel
theorem yaVal : ya = 0x80002000 := by decide +kernel
theorem caVal : ca = 0x80002010 := by decide +kernel

theorem xs6Range (b : Int) : b ∈ clRange xa 4 → xa ≤ b ∧ b < xa + 4 := by
  intro Hb
  obtain ⟨k, Hk⟩ := List.mem_iff_getElem?.1 Hb
  obtain ⟨Hk, rfl⟩ := (AxSpinH4.clRangeLookup xa 4 k b).1 Hk
  omega

theorem XS6X (b : Int) : b ∈ clRange xa 4 → b ∈ X6 (clRange xa 4) [ca] ∧ b ∉ [ca] := by
  intro Hb
  refine ⟨elemOfUnionL (LawfulSet.mem_ofList.1 Hb), fun H => ?_⟩
  rw [List.mem_singleton] at H
  subst H
  have h := xs6Range _ Hb
  rw [xaVal, caVal] at h
  omega

theorem XS6NeYa (b : Int) : b ∈ clRange xa 4 → b ≠ ya := by
  intro Hb H
  subst H
  have h := xs6Range _ Hb
  rw [xaVal, yaVal] at h
  omega

theorem yaNX6 : ya ∉ X6 (clRange xa 4) [ca] := by
  unfold X6
  intro H
  rcases elemOfUnion.1 H with H | H
  · exact XS6NeYa ya (LawfulSet.mem_ofList.2 H) rfl
  · exact caNeYa (List.mem_singleton.1 (LawfulSet.mem_ofList.2 H)).symm

theorem XS6Nodup : (clRange xa 4).Nodup := by decide +kernel

theorem XS6Disj (a : Int) : a ∈ clRange xa 4 → a ∉ [ca] := fun Ha => (XS6X a Ha).2

/-- A load and a later same-base store of the same hart (both non-empty): the load is a
lob-predecessor of the store (ppo rule 1). -/
theorem ldstLobp (GD : Gdexec) (Hcons : rvwmoCatConsistent GD) (i : Agent) (k1 k2 : Nat)
    (a : Int) (ts : List Nat) (vs bs : List (BitVec 8)) (cls : WmClass) :
    gxLbl GD.gdG (i, k1) = some (.LLoad false a ts vs) →
    gxLbl GD.gdG (i, k2) = some (.LStore false a bs cls) →
    k1 < k2 → 0 < vs.length → ts.length = vs.length → 0 < bs.length →
    (i, k1) ∈ splLobp GD (i, k2) := by
  intro H1 H2 Hlt Hv Ht Hb
  have Hr : (clRange a vs.length)[0]? = some a :=
    (AxSpinH4.clRangeLookup a vs.length 0 a).2 ⟨Hv, by simp⟩
  obtain ⟨t, v, -, -, Hrd⟩ := (loadNBytes _ _ _ _ _ H1 Ht).1 0 a Hr
  have Hw0 : (clRange a bs.length)[0]? = some a :=
    (AxSpinH4.clRangeLookup a bs.length 0 a).2 ⟨Hb, by simp⟩
  obtain ⟨b, -, Hwb⟩ := (storeNBytes _ _ _ _ _ H2).1 0 a Hw0
  exact locLobp GD Hcons (i, k1) (i, k2) _ a b H1 rfl (gpoRow GD i k1 k2 _ _ H1 H2 Hlt)
    (.inr ⟨t, v, Hrd⟩) Hwb

def one4 : BitVec (8 * 4) := 1

/-- HART B. -/
abbrev g6Tail : SailM Unit := fenceM (relM hlt)
def g6K2 (w1 : BitVec (8 * 4)) (res : Result (BitVec (8 * 4) × Option Bool) Arch.abort) :
    SailM Unit :=
  match res with
  | .Ok _ => .impure (.ok (.memWrite 4 64 (h4wreq 4 l3pAkP xpaM (w1 + one4)))) (fun _ => g6Tail)
  | .Err _ => hlt
def g6K1 (res : Result (BitVec (8 * 4) × Option Bool) Arch.abort) : SailM Unit :=
  match res with
  | .Ok (w1, _) => .impure (.ok (.memRead 4 64 (h4rreq 4 l3pAkP xpaM))) (g6K2 w1)
  | .Err _ => hlt
abbrev g6Cs : SailM Unit := .impure (.ok (.memRead 4 64 (h4rreq 4 l3pAkP xpaM))) g6K1
abbrev g6M0 : SailM Unit := acqRmw g6Cs hlt

def g6Val (vs1 : List (BitVec 8)) : BitVec (8 * 4) := wordOfBytes 4 vs1 + one4

def g6Row (t1 : Nat) (ts1 : List Nat) (vs1 : List (BitVec 8)) (ts2 : List Nat)
    (vs2 : List (BitVec 8)) : List Lbl :=
  [.LRmw true false ya [t1] [b0] [b1] .WCplain,
   .LLoad false xa ts1 vs1,
   .LLoad false xa ts2 vs2,
   .LStore false xa (WeakInterpProj.wbytes 4 (g6Val vs1)) .WCplain,
   .LFence true true false true,
   .LStore false ya [b0] .WCrel]

/-- HART A (positive writer): acquire; sw x ← 1 (4 bytes); fence; release. -/
abbrev a6Cs : SailM Unit :=
  .impure (.ok (.memWrite 4 64 (h4wreq 4 l3pAkP xpaM one4))) (fun _ => fenceM (relM hlt))
abbrev a6M0 : SailM Unit := acqRmw a6Cs hlt

def a6Row (tA : Nat) : List Lbl :=
  [.LRmw true false ya [tA] [b0] [b1] .WCplain,
   .LStore false xa (WeakInterpProj.wbytes 4 one4) .WCplain,
   .LFence true true false true,
   .LStore false ya [b0] .WCrel]

section runs6
variable (cpu : CPU)

theorem g6Run (GD : Gdexec) (t1 : Nat) (ts1 : List Nat) (vs1 : List (BitVec 8)) (ts2 : List Nat)
    (vs2 : List (BitVec 8)) (Hrow : AxOpsem.grow GD hB = g6Row t1 ts1 vs1 ts2 vs2)
    (H1 : vs1.length = 4) (H2 : vs2.length = 4) :
    nsteps (astepAnyNfGv GD hB) 7 ⟨hp cpu g6M0 zeroRegs, 0⟩ ⟨hp cpu hlt zeroRegs, 6⟩ := by
  refine nsteps_l (runRmwRead cpu GD hB 0 ypaM ypaMRam t1 b0 .WCplain (acqK g6Cs hlt) zeroRegs
    (by rw [Hrow]; rfl)) ?_
  have Hw := runRmwWrite cpu GD hB 0 ypaM ypaMRam t1 b0 .WCplain
    (if b0 = b0 then g6Cs else hlt) zeroRegs (by rw [Hrow]; rfl)
  rw [if_pos rfl] at Hw
  refine nsteps_l Hw ?_
  refine nsteps_l (h4runRead cpu GD hB 4 xpaM xpaMRam ts1 vs1 g6K1 zeroRegs 1
    (by rw [Hrow]; rfl) H1) ?_
  refine nsteps_l (h4runRead cpu GD hB 4 xpaM xpaMRam ts2 vs2 (g6K2 (wordOfBytes 4 vs1)) zeroRegs 2
    (by rw [Hrow]; rfl) H2) ?_
  refine nsteps_l (h4runWrite cpu GD hB 4 (by decide) xpaM xpaMRam (wordOfBytes 4 vs1 + one4)
    g6Tail zeroRegs 3 .WCplain (by rw [Hrow]; rfl)) ?_
  refine nsteps_l (runFence cpu GD hB 4 (relM hlt) zeroRegs (by rw [Hrow]; rfl)) ?_
  refine nsteps_l (spRunWrite cpu GD hB ypaM ypaMRam b0 hlt zeroRegs 5 .WCrel
    (by rw [Hrow]; rfl)) ?_
  exact nsteps_O _

theorem a6Run (GD : Gdexec) (tA : Nat) (Hrow : AxOpsem.grow GD hA = a6Row tA) :
    nsteps (astepAnyNfGv GD hA) 5 ⟨hp cpu a6M0 zeroRegs, 0⟩ ⟨hp cpu hlt zeroRegs, 4⟩ := by
  refine nsteps_l (runRmwRead cpu GD hA 0 ypaM ypaMRam tA b0 .WCplain (acqK a6Cs hlt) zeroRegs
    (by rw [Hrow]; rfl)) ?_
  have Hw := runRmwWrite cpu GD hA 0 ypaM ypaMRam tA b0 .WCplain
    (if b0 = b0 then a6Cs else hlt) zeroRegs (by rw [Hrow]; rfl)
  rw [if_pos rfl] at Hw
  refine nsteps_l Hw ?_
  refine nsteps_l (h4runWrite cpu GD hA 4 (by decide) xpaM xpaMRam one4 (fenceM (relM hlt))
    zeroRegs 1 .WCplain (by rw [Hrow]; rfl)) ?_
  refine nsteps_l (runFence cpu GD hA 2 (relM hlt) zeroRegs (by rw [Hrow]; rfl)) ?_
  refine nsteps_l (spRunWrite cpu GD hA ypaM ypaMRam b0 hlt zeroRegs 3 .WCrel
    (by rw [Hrow]; rfl)) ?_
  exact nsteps_O _

end runs6

/-! # 2. The WPds, written ONLY with the handle surface -/

section wpds6
variable {hlc : HasLC} {GF : BundledGFunctors.{0,0,0}} [InvGS_gen hlc GF] [AxannotGS GF]
  [AxlogG GF Hent] [SpinlockG GF]

set_option hygiene false in
local notation:max "TWA " s:max => @tierAWpd GF hlc _ _ (splPol GT) (gtAdGd GT) spinN Unit
  (spinOb6 ya (clRange xa 4) [ca] cv5) nm s .MaybeStuck hA (fun _ => iprop(True))

/-- HART A at the real protocol. -/
theorem wpdA6 (GT : GdexecT) (nm : spinN) (cpu : CPU) (Hcons : rvwmoCatConsistent (gtAdGd GT))
    (tA : Nat) (Hrow : AxOpsem.grow (gtAdGd GT) hA = a6Row tA) :
    ⊢ isLock (GF := GF) nm.2 ya (spinR6 (clRange xa 4) [ca] nm (gtAdGd GT)) -∗
      notheld nm.2 ya hA -∗ TWA ⟨hp cpu a6M0 zeroRegs, 0⟩ := by
  have Hlen : (AxOpsem.grow (gtAdGd GT) hA).length = 4 := by rw [Hrow]; rfl
  have Hl0 : gxLbl (gtAdGd GT).gdG (hA, 0) = some (.LRmw true false ya [tA] [b0] [b1] .WCplain) := by
    rw [gxLblGrow, Hrow]; rfl
  have Hl1 : gxLbl (gtAdGd GT).gdG (hA, 1) =
      some (.LStore false xa (WeakInterpProj.wbytes 4 one4) .WCplain) := by
    rw [gxLblGrow, Hrow]; rfl
  have H0 : ⊢ isLock (GF := GF) nm.2 ya (spinR6 (clRange xa 4) [ca] nm (gtAdGd GT)) -∗
      notheld nm.2 ya hA -∗
      (⌜lkClaim ya (gtAdGd GT).gdG (hA, 0) (gwriteAt (gtAdGd GT).gdG tA)⌝ -∗
        AxAnnot.annotOwn (hA, 0)
          iprop(locked nm.2 ya hA (hA, 0) ∗ RL nm.1 (gtAdGd GT) [ca] (hA, 0)) -∗
        hdlw GT nm 1 xa 4 (hA, 0) [] -∗
        ∀ rs : RegFile, TWA ⟨hp cpu a6Cs rs, 1⟩) -∗
      ∀ rs : RegFile, TWA ⟨hp cpu a6M0 rs, 0⟩ :=
    wpdAcquireH6 (hlc := hlc) xa 4 [ca] cv5 GT nm cpu Hcons yaNX6 hA 0 tA a6Cs hlt _
      (by rw [Hlen]; decide) (by rw [Hrow]; rfl)
  have Hin1 : ((hA, 0) : Geid) ∈ @Axpol.lobp (splPol GT) (gtAdGd GT) (hA, 1) :=
    acqLobp (gtAdGd GT) Hcons hA 0 1 ya [tA] [b0] [b1] .WCplain _ Hl0 Hl1 rfl (by decide)
  have H1 : ⊢ hdlw (GF := GF) GT nm 1 xa 4 (hA, 0) [] -∗
      (hdlw GT nm 1 xa 4 (hA, 1) (WeakInterpProj.wbytes 4 one4) -∗
        ∀ rs : RegFile, TWA ⟨hp cpu (fenceM (relM hlt)) rs, 2⟩) -∗
      ∀ rs : RegFile, TWA ⟨hp cpu a6Cs rs, 1⟩ :=
    wpdSdOwnN (hlc := hlc) xa 4 [ca] cv5 GT nm cpu Hcons yaNX6 hA 1 4 xpaM xpaMRam one4
      (fenceM (relM hlt)) .WCplain (hA, 0) [] _ (by rw [Hlen]; decide) (by rw [Hrow]; rfl)
      (fun b Hb => XS6X b Hb) Hin1
  have Hev : ∀ e : Geid, e = (hA, 0) ∨ e = (hA, 1) → e.1 = hA ∧ e.2 < 2 ∧
      ∃ l, (AxOpsem.grow (gtAdGd GT) hA)[e.2]? = some l ∧ (lbIsR l || lbIsW l) = true := by
    intro e He
    rcases He with rfl | rfl
    · exact ⟨rfl, by decide, _, by rw [Hrow]; rfl, rfl⟩
    · exact ⟨rfl, by decide, _, by rw [Hrow]; rfl, rfl⟩
  have H2 : ⊢ isLock (GF := GF) nm.2 ya (spinR6 (clRange xa 4) [ca] nm (gtAdGd GT)) -∗
      AxAnnot.annotOwn (hA, 0)
        iprop(locked nm.2 ya hA (hA, 0) ∗ RL nm.1 (gtAdGd GT) [ca] (hA, 0)) -∗
      hdlw GT nm 1 xa 4 (hA, 1) (WeakInterpProj.wbytes 4 one4) -∗
      (AxAnnot.annotOwn (hA, 3) (notheld nm.2 ya hA) -∗
        ∀ rs : RegFile, TWA ⟨hp cpu hlt rs, 4⟩) -∗
      ∀ rs : RegFile, TWA ⟨hp cpu (fenceM (relM hlt)) rs, 2⟩ :=
    wpdReleaseH6 (hlc := hlc) xa 4 [ca] cv5 GT nm cpu Hcons yaNX6 hA 2 hlt (hA, 0) (hA, 1)
      (WeakInterpProj.wbytes 4 one4) _ (by rw [Hlen]; decide) (by rw [Hlen]; decide)
      (by rw [Hrow]; rfl) (by rw [Hrow]; rfl) (by decide) Hev
  have H3 : ⊢ ∀ rs : RegFile, TWA ⟨hp cpu hlt rs, 4⟩ :=
    shHltTrue (hlc := hlc) (pol := splPol GT) (gtAdGd GT) spinN Unit
      (spinOb6 ya (clRange xa 4) [ca] cv5) nm cpu hA 4
  iintro #Hil Hnh
  iapply H0 $$ Hil Hnh [] %zeroRegs
  iintro %_ Hc Hx %rs
  iapply H1 $$ Hx [Hc] %rs
  iintro Hw %rs
  iapply H2 $$ Hil Hc Hw [] %rs
  iintro _ %rs
  iapply H3 $$ %rs

set_option hygiene false in
local notation:max "TWB " s:max => @tierAWpd GF hlc _ _ (splPol GT) (gtAdGd GT) spinN Unit
  (spinOb6 ya (clRange xa 4) [ca] cv5) nm s .MaybeStuck hB (fun _ => iprop(⌜vs2 = vs1⌝))

theorem gL (GT : GdexecT) (t1 : Nat) (ts1 : List Nat) (vs1 : List (BitVec 8)) (ts2 : List Nat)
    (vs2 : List (BitVec 8)) (Hrow : AxOpsem.grow (gtAdGd GT) hB = g6Row t1 ts1 vs1 ts2 vs2)
    (k : Nat) (lb : Lbl) :
    (g6Row t1 ts1 vs1 ts2 vs2)[k]? = some lb → gxLbl (gtAdGd GT).gdG (hB, k) = some lb := by
  intro Hk
  rw [gxLblGrow, Hrow]
  exact Hk

/-- B has no write to the word po-before its loads. -/
theorem g6Nopre (GT : GdexecT) (t1 : Nat) (ts1 : List Nat) (vs1 : List (BitVec 8))
    (ts2 : List Nat) (vs2 : List (BitVec 8))
    (Hrow : AxOpsem.grow (gtAdGd GT) hB = g6Row t1 ts1 vs1 ts2 vs2) (k : Nat) (b : Int)
    (w : Geid) (v' : BitVec 8) :
    k ≤ 2 → b ∈ clRange xa 4 → gwritesByte (gtAdGd GT).gdG w b v' →
    WeakRvwmoGraph.gpo (gtAdGd GT).gdG w (hB, k) → False := by
  rintro Hk Hb Hw ⟨Hh, Hlt, -⟩
  obtain ⟨wi, wk⟩ := w
  simp only at Hh Hlt
  subst Hh
  have Hl0 := gL GT t1 ts1 vs1 ts2 vs2 Hrow 0 _ rfl
  have Hl1 := gL GT t1 ts1 vs1 ts2 vs2 Hrow 1 _ rfl
  rcases wk with _ | _ | wk
  · obtain ⟨-, -, Hsg, -⟩ := gwbRmw _ _ _ _ _ _ _ Hl0
    exact XS6NeYa b Hb (Hsg _ _ Hw).1
  · obtain ⟨l, base, vs, j, Hl, Hwr, -⟩ := Hw
    rw [Hl1] at Hl
    cases Hl
    simp [lbWr] at Hwr
  · omega

theorem wpdG6 (GT : GdexecT) (nm : spinN) (cpu : CPU) (Hcons : rvwmoCatConsistent (gtAdGd GT))
    (t1 : Nat) (ts1 : List Nat) (vs1 : List (BitVec 8)) (ts2 : List Nat) (vs2 : List (BitVec 8))
    (Hrow : AxOpsem.grow (gtAdGd GT) hB = g6Row t1 ts1 vs1 ts2 vs2)
    (Hts1 : ts1.length = 4) (Hvs1 : vs1.length = 4) (Hts2 : ts2.length = 4)
    (Hvs2 : vs2.length = 4) :
    ⊢ isLock (GF := GF) nm.2 ya (spinR6 (clRange xa 4) [ca] nm (gtAdGd GT)) -∗
      notheld nm.2 ya hB -∗ TWB ⟨hp cpu g6M0 zeroRegs, 0⟩ := by
  have Hl0 := gL GT t1 ts1 vs1 ts2 vs2 Hrow 0 _ rfl
  have Hl1 := gL GT t1 ts1 vs1 ts2 vs2 Hrow 1 _ rfl
  have Hl2 := gL GT t1 ts1 vs1 ts2 vs2 Hrow 2 _ rfl
  have Hl3 := gL GT t1 ts1 vs1 ts2 vs2 Hrow 3 _ rfl
  have Hlen : (AxOpsem.grow (gtAdGd GT) hB).length = 6 := by rw [Hrow]; rfl
  -- acquire, handle form
  have H0 : ⊢ isLock (GF := GF) nm.2 ya (spinR6 (clRange xa 4) [ca] nm (gtAdGd GT)) -∗
      notheld nm.2 ya hB -∗
      (⌜lkClaim ya (gtAdGd GT).gdG (hB, 0) (gwriteAt (gtAdGd GT).gdG t1)⌝ -∗
        AxAnnot.annotOwn (hB, 0)
          iprop(locked nm.2 ya hB (hB, 0) ∗ RL nm.1 (gtAdGd GT) [ca] (hB, 0)) -∗
        hdlw GT nm 1 xa 4 (hB, 0) [] -∗
        ∀ rs : RegFile, TWB ⟨hp cpu g6Cs rs, 1⟩) -∗
      ∀ rs : RegFile, TWB ⟨hp cpu g6M0 rs, 0⟩ :=
    wpdAcquireH6 (hlc := hlc) xa 4 [ca] cv5 GT nm cpu Hcons yaNX6 hB 0 t1 g6Cs hlt _
      (by rw [Hlen]; decide) (by rw [Hrow]; rfl)
  -- the word handle split into two READ halves, both at the claim
  have Hsp : ∀ rs : RegFile, ⊢ hdlw (GF := GF) GT nm 1 xa 4 (hB, 0) [] -∗
      (hdlw GT nm (Qp.half 1) xa 4 (hB, 0) [] -∗ hdlw GT nm (Qp.half 1) xa 4 (hB, 0) [] -∗
        TWB ⟨hp cpu g6Cs rs, 1⟩) -∗
      TWB ⟨hp cpu g6Cs rs, 1⟩ := by
    intro rs
    have h := hdlwSplit (hlc := hlc) (GF := GF) xa 4 [ca] cv5 GT nm hB
      (fun _ => iprop(⌜vs2 = vs1⌝)) ⟨hp cpu g6Cs rs, 1⟩ (Qp.half 1) (Qp.half 1) xa 4 (hB, 0) []
    rw [Qp.half_add_half] at h
    exact h
  -- lw x, 1st: a half drawn from the claim (ppo rule 5)
  have Hin1 : ((hB, 0) : Geid) ∈ @Axpol.lobp (splPol GT) (gtAdGd GT) (hB, 1) :=
    acqLobp (gtAdGd GT) Hcons hB 0 1 ya [t1] [b0] [b1] .WCplain _ Hl0 Hl1 rfl (by decide)
  have H1 : ⊢ hdlw (GF := GF) GT nm (Qp.half 1) xa 4 (hB, 0) [] -∗
      (hdlw GT nm (Qp.half 1) xa 4 (hB, 1) vs1 -∗
        AxAnnot.annotOwn (hB, 1)
          iprop(⌜∀ (j : Nat) v0 v, ([] : List (BitVec 8))[j]? = some v0 → vs1[j]? = some v →
            v = v0⌝) -∗
        ∀ rs : RegFile, TWB ⟨hp cpu (g6K1 (.Ok (wordOfBytes 4 vs1, none))) rs, 2⟩) -∗
      ∀ rs : RegFile, TWB ⟨hp cpu g6Cs rs, 1⟩ :=
    wpdLdOwnN (hlc := hlc) xa 4 [ca] cv5 GT nm cpu Hcons yaNX6 hB 1 4 (by decide) xpaM xpaMRam
      g6K1 ts1 vs1 (Qp.half 1) (hB, 0) [] _ (by rw [Hlen]; decide) (by rw [Hrow]; rfl) Hts1 Hvs1
      (fun b Hb => (XS6X b Hb).1) Hin1
      (fun b w v' Hb Hw Hpo => (g6Nopre GT t1 ts1 vs1 ts2 vs2 Hrow 1 b w v' (by decide) Hb Hw
        Hpo).elim)
  -- lw x, 2nd: the OTHER half, also from the claim (unordered with the 1st)
  have Hin2 : ((hB, 0) : Geid) ∈ @Axpol.lobp (splPol GT) (gtAdGd GT) (hB, 2) :=
    acqLobp (gtAdGd GT) Hcons hB 0 2 ya [t1] [b0] [b1] .WCplain _ Hl0 Hl2 rfl (by decide)
  have H2 : ⊢ hdlw (GF := GF) GT nm (Qp.half 1) xa 4 (hB, 0) [] -∗
      (hdlw GT nm (Qp.half 1) xa 4 (hB, 2) vs2 -∗
        AxAnnot.annotOwn (hB, 2)
          iprop(⌜∀ (j : Nat) v0 v, ([] : List (BitVec 8))[j]? = some v0 → vs2[j]? = some v →
            v = v0⌝) -∗
        ∀ rs : RegFile,
          TWB ⟨hp cpu (g6K2 (wordOfBytes 4 vs1) (.Ok (wordOfBytes 4 vs2, none))) rs, 3⟩) -∗
      ∀ rs : RegFile, TWB ⟨hp cpu (g6K1 (.Ok (wordOfBytes 4 vs1, none))) rs, 2⟩ :=
    wpdLdOwnN (hlc := hlc) xa 4 [ca] cv5 GT nm cpu Hcons yaNX6 hB 2 4 (by decide) xpaM xpaMRam
      (g6K2 (wordOfBytes 4 vs1)) ts2 vs2 (Qp.half 1) (hB, 0) [] _ (by rw [Hlen]; decide)
      (by rw [Hrow]; rfl) Hts2 Hvs2 (fun b Hb => (XS6X b Hb).1) Hin2
      (fun b w v' Hb Hw Hpo => (g6Nopre GT t1 ts1 vs1 ts2 vs2 Hrow 2 b w v' (by decide) Hb Hw
        Hpo).elim)
  -- sw x: the two halves RECOMBINED (ppo rule 1 from each load)
  have Hin31 : ((hB, 1) : Geid) ∈ @Axpol.lobp (splPol GT) (gtAdGd GT) (hB, 3) :=
    ldstLobp (gtAdGd GT) Hcons hB 1 3 xa ts1 vs1 _ .WCplain Hl1 Hl3 (by decide)
      (by rw [Hvs1]; decide) (by rw [Hts1, Hvs1]) (by rw [wbytesLength]; decide)
  have Hin32 : ((hB, 2) : Geid) ∈ @Axpol.lobp (splPol GT) (gtAdGd GT) (hB, 3) :=
    ldstLobp (gtAdGd GT) Hcons hB 2 3 xa ts2 vs2 _ .WCplain Hl2 Hl3 (by decide)
      (by rw [Hvs2]; decide) (by rw [Hts2, Hvs2]) (by rw [wbytesLength]; decide)
  have H3 : ⊢ hdlw (GF := GF) GT nm (Qp.half 1) xa 4 (hB, 1) vs1 -∗
      hdlw GT nm (Qp.half 1) xa 4 (hB, 2) vs2 -∗
      (hdlw GT nm 1 xa 4 (hB, 3) (WeakInterpProj.wbytes 4 (wordOfBytes 4 vs1 + one4)) -∗
        AxAnnot.annotOwn (hB, 3)
          iprop(⌜∀ (j : Nat) v1 v2, j < 4 → vs1[j]? = some v1 → vs2[j]? = some v2 → v1 = v2⌝) -∗
        ∀ rs : RegFile, TWB ⟨hp cpu g6Tail rs, 4⟩) -∗
      ∀ rs : RegFile,
        TWB ⟨hp cpu (g6K2 (wordOfBytes 4 vs1) (.Ok (wordOfBytes 4 vs2, none))) rs, 3⟩ :=
    wpdSdOwnN2 (hlc := hlc) xa 4 [ca] cv5 GT nm cpu Hcons yaNX6 hB 3 4 xpaM xpaMRam
      (wordOfBytes 4 vs1 + one4) g6Tail .WCplain (Qp.half 1) (Qp.half 1) (hB, 1) (hB, 2) vs1 vs2
      _ (Qp.half_add_half 1) (by rw [Hlen]; decide) (by rw [Hrow]; rfl) (fun b Hb => XS6X b Hb)
      (by decide) Hin31 Hin32
  -- release: `locked` + lk->cpu from the claim, the word from the store
  have Hev : ∀ e : Geid, e = (hB, 0) ∨ e = (hB, 3) → e.1 = hB ∧ e.2 < 4 ∧
      ∃ l, (AxOpsem.grow (gtAdGd GT) hB)[e.2]? = some l ∧ (lbIsR l || lbIsW l) = true := by
    intro e He
    rcases He with rfl | rfl
    · exact ⟨rfl, by decide, _, by rw [Hrow]; rfl, rfl⟩
    · exact ⟨rfl, by decide, _, by rw [Hrow]; rfl, rfl⟩
  have H4 : ⊢ isLock (GF := GF) nm.2 ya (spinR6 (clRange xa 4) [ca] nm (gtAdGd GT)) -∗
      AxAnnot.annotOwn (hB, 0)
        iprop(locked nm.2 ya hB (hB, 0) ∗ RL nm.1 (gtAdGd GT) [ca] (hB, 0)) -∗
      hdlw GT nm 1 xa 4 (hB, 3) (WeakInterpProj.wbytes 4 (wordOfBytes 4 vs1 + one4)) -∗
      (AxAnnot.annotOwn (hB, 5) (notheld nm.2 ya hB) -∗
        ∀ rs : RegFile, TWB ⟨hp cpu hlt rs, 6⟩) -∗
      ∀ rs : RegFile, TWB ⟨hp cpu g6Tail rs, 4⟩ :=
    wpdReleaseH6 (hlc := hlc) xa 4 [ca] cv5 GT nm cpu Hcons yaNX6 hB 4 hlt (hB, 0) (hB, 3)
      (WeakInterpProj.wbytes 4 (wordOfBytes 4 vs1 + one4)) _ (by rw [Hlen]; decide)
      (by rw [Hlen]; decide) (by rw [Hrow]; rfl) (by rw [Hrow]; rfl) (by decide) Hev
  -- row end: `vs2 = vs1` READ BACK from the store's annotation
  have HRQ : (iprop(⌜∀ (j : Nat) v1 v2, j < 4 → vs1[j]? = some v1 → vs2[j]? = some v2 →
      v1 = v2⌝) : IProp GF) ⊢ ⌜vs2 = vs1⌝ := by
    refine pure_mono (fun Hag => ?_)
    apply List.ext_getElem?
    intro j
    by_cases Hj : j < 4
    · rw [List.getElem?_eq_getElem (by omega : j < vs1.length),
        List.getElem?_eq_getElem (by omega : j < vs2.length)]
      exact congrArg some (Hag j _ _ Hj (List.getElem?_eq_getElem _)
        (List.getElem?_eq_getElem _)).symm
    · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]
  have H5 : ⊢ AxAnnot.annotOwn (GF := GF) (hB, 3)
      iprop(⌜∀ (j : Nat) v1 v2, j < 4 → vs1[j]? = some v1 → vs2[j]? = some v2 → v1 = v2⌝) -∗
      ∀ rs : RegFile, TWB ⟨hp cpu hlt rs, 6⟩ :=
    shHltReadback (hlc := hlc) (pol := splPol GT) (gtAdGd GT) spinN Unit
      (spinOb6 ya (clRange xa 4) [ca] cv5) nm cpu hB 6 (hB, 3) rfl _ (vs2 = vs1) HRQ
  iintro #Hil Hnh
  iapply H0 $$ Hil Hnh [] %zeroRegs
  iintro %_ Hc Hx %rs
  iapply (Hsp rs) $$ Hx
  iintro Hx1 Hx2
  iapply H1 $$ Hx1 [Hc Hx2] %rs
  iintro Hr1 _ %rs
  iapply H2 $$ Hx2 [Hc Hr1] %rs
  iintro Hr2 _ %rs
  iapply H3 $$ Hr1 Hr2 [Hc] %rs
  iintro Hw Hag %rs
  iapply H4 $$ Hil Hc Hw [Hag] %rs
  iintro _ %rs
  iapply H5 $$ Hag %rs

end wpds6

/-! # 3. THE CAPSTONE -/

/-- Lean-only (Rocq `set s0`). -/
def AxSpinH6.cS0 (sA0 : Athread) (i : Agent) : Athread :=
  if i = hA then sA0 else ⟨hp cpu0 g6M0 zeroRegs, 0⟩
/-- Lean-only (Rocq `set sN`). -/
def AxSpinH6.cSN (sAN : Athread) (i : Agent) : Athread :=
  if i = hA then sAN else ⟨hp cpu0 hlt zeroRegs, 6⟩
/-- Lean-only (Rocq `set nf`). -/
def AxSpinH6.cN (nA : Nat) (i : Agent) : Nat := if i = hA then nA else 7
/-- Lean-only (Rocq `set post`). -/
def AxSpinH6.cPost (vs1 vs2 : List (BitVec 8)) (i : Agent) (_ : Athread) : Prop :=
  if i = hB then vs2 = vs1 else True

theorem csDblLoad (GT : GdexecT)
    (HconsT : rvwmoCatConsistentT GT) (Hcl : ctrlClosed GT)
    (Hharts : ∀ e, e ∈ GT.gtG.gxGmo → e.1 = hA ∨ e.1 = hB)
    (t1 : Nat) (ts1 : List Nat) (vs1 : List (BitVec 8)) (ts2 : List Nat) (vs2 : List (BitVec 8))
    (Hts1 : ts1.length = 4) (Hvs1 : vs1.length = 4) (Hts2 : ts2.length = 4)
    (Hvs2 : vs2.length = 4)
    (HrowB : AxOpsem.grow (gtAdGd GT) hB = g6Row t1 ts1 vs1 ts2 vs2)
    (sA0 sAN : Athread) (nA : Nat)
    (HrunA : ∀ (_ : AxannotGS spinGF) (nm : spinN),
      nsteps (tierAAstep (gtAdGd GT) nm hA) nA sA0 sAN)
    (HkA : sA0.atK = 0) (HendA : sAN.atK = (AxOpsem.grow (gtAdGd GT) hA).length)
    (HwpA : ∀ [InvGS_gen .hasNoLC spinGF] [AxannotGS spinGF] (nm : spinN),
      ⊢ spinInit6 ya (clRange xa 4) [ca] (gtAdGd GT) nm hA -∗
        @tierAWpd spinGF .hasNoLC _ _ (splPol GT) (gtAdGd GT) spinN Unit
          (spinOb6 ya (clRange xa 4) [ca] cv5) nm sA0 .MaybeStuck hA (fun _ => iprop(True))) :
    vs2 = vs1 := by
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
      nsteps (tierAAstep (gtAdGd GT) nm i) (AxSpinH6.cN nA i) (AxSpinH6.cS0 sA0 i)
        (AxSpinH6.cSN sAN i) := by
    intro Hann nm i Hi
    rcases Hin01 i Hi with rfl | rfl
    · exact HrunA Hann nm
    · exact g6Run cpu0 (gtAdGd GT) t1 ts1 vs1 ts2 vs2 HrowB Hvs1 Hvs2
  have Hk0 : ∀ i, i ∈ [hA, hB] → (AxSpinH6.cS0 sA0 i).atK = 0 := by
    intro i Hi
    rcases Hin01 i Hi with rfl | rfl
    · exact HkA
    · rfl
  have Hend : ∀ i, i ∈ [hA, hB] →
      (AxSpinH6.cSN sAN i).atK = (AxOpsem.grow (gtAdGd GT) i).length := by
    intro i Hi
    rcases Hin01 i Hi with rfl | rfl
    · exact HendA
    · show 6 = (AxOpsem.grow (gtAdGd GT) hB).length
      rw [HrowB]
      rfl
  have Hwp : ∀ [InvGS_gen .hasNoLC spinGF] [AxannotGS spinGF] (nm : spinN),
      ⊢ ([∗list] i ∈ [hA, hB], spinInit6 ya (clRange xa 4) [ca] (gtAdGd GT) nm i) -∗
        [∗list] i ∈ [hA, hB],
          @tierAWpd spinGF .hasNoLC _ _ (splPol GT) (gtAdGd GT) spinN Unit
            (spinOb6 ya (clRange xa 4) [ca] cv5) nm (AxSpinH6.cS0 sA0 i) .MaybeStuck i
            (fun s => iprop(⌜AxSpinH6.cPost vs1 vs2 i s⌝)) := by
    intro Hinv Hann nm
    iintro HI
    icases (AxTokLedgerMp.bigSepLPair hA hB
      (fun i => spinInit6 (GF := spinGF) ya (clRange xa 4) [ca] (gtAdGd GT) nm i)).1 $$ HI
      with ⟨HA, HB⟩
    iapply (AxTokLedgerMp.bigSepLPair hA hB _).2
    rw [show AxSpinH6.cS0 sA0 hA = sA0 from if_pos rfl,
      show AxSpinH6.cS0 sA0 hB = ⟨hp cpu0 g6M0 zeroRegs, 0⟩ from if_neg (by decide)]
    isplitl [HA]
    · iapply (AxSpinWit.tierAWpdMono (hlc := .hasNoLC) (pol := splPol GT) (gtAdGd GT) spinN Unit
        (spinOb6 ya (clRange xa 4) [ca] cv5) nm sA0 .MaybeStuck hA (fun _ => iprop(True))
        (fun s => iprop(⌜AxSpinH6.cPost vs1 vs2 hA s⌝))
        (fun _ => pure_mono (fun _ => by
          unfold AxSpinH6.cPost; rw [if_neg (by decide)]; trivial)))
      iapply HwpA nm $$ HA
    · iapply (AxSpinWit.tierAWpdMono (hlc := .hasNoLC) (pol := splPol GT) (gtAdGd GT) spinN Unit
        (spinOb6 ya (clRange xa 4) [ca] cv5) nm ⟨hp cpu0 g6M0 zeroRegs, 0⟩ .MaybeStuck hB
        (fun _ => iprop(⌜vs2 = vs1⌝))
        (fun s => iprop(⌜AxSpinH6.cPost vs1 vs2 hB s⌝))
        (fun _ => pure_mono (fun Hv => by
          unfold AxSpinH6.cPost; rw [if_pos rfl]; exact Hv)))
      unfold spinInit6
      icases HB with ⟨Hil, Hnh⟩
      iapply (wpdG6 (hlc := .hasNoLC) (GF := spinGF) GT nm cpu0 Hcons t1 ts1 vs1 ts2 vs2 HrowB
        Hts1 Hvs1 Hts2 Hvs2) $$ Hil Hnh
  have HndC : [ca].Nodup := by simp
  have Hfin := @tierAAdequacyAnnGateT spinGF _ _ (splPol GT) GT spinN Unit
    (spinOb6 ya (clRange xa 4) [ca] cv5) (spinInit6 ya (clRange xa 4) [ca] (gtAdGd GT))
    (splAxpolWf GT) HconsT [hA, hB] Hnd Hharts' (AxSpinH6.cS0 sA0) (AxSpinH6.cSN sAN)
    (AxSpinH6.cN nA) Hrun Hk0 Hend (AxSpinH6.cPost vs1 vs2) Hwp
    (spinHobAlloc6 (GF := spinGF) ya (clRange xa 4) [ca] cv5 (gtAdGd GT) [hA, hB] Hnd XS6Nodup
      HndC XS6Disj)
    (splHok GT HconsT Hcl) hB (by simp)
  exact (if_pos rfl : AxSpinH6.cPost vs1 vs2 hB _ = (vs2 = vs1)) ▸ Hfin

/-! # 4. CERTIFICATES -/

/-- B's claim controls every po-later store; B's first load feeds the stored value (data). -/
def g6Deps : List Tdep :=
  [(((hB, 0), (hB, 3)), DTctrl), (((hB, 0), (hB, 5)), DTctrl),
   (((hB, 1), (hB, 3)), DTdata)]

def w1000 : List (BitVec 8) := WeakInterpProj.wbytes 4 one4
def w0000 : List (BitVec 8) := [b0, b0, b0, b0]
def w1000' : List (BitVec 8) := [b1, b0, b0, b0]

/-- (a) A claims (image), writes the word 1, releases; B claims A's release and BOTH loads read
A's word. -/
def gs6 : GdexecT :=
  mkgt [a6Row 0, g6Row 3 [2, 2, 2, 2] w1000 [2, 2, 2, 2] w1000]
    [(hA, 0), (hA, 1), (hA, 3), (hB, 0), (hB, 1), (hB, 2), (hB, 3), (hB, 5)] g6Deps

/-- (b) RACE: A' = `r5` (claim; fence; release; x := 1 (one byte) AFTER the release).  B claims
A''s release, its 1st load reads 0, A''s x := 1 lands gmo-BETWEEN B's two loads, the 2nd load
reads 1. -/
def gr6 : GdexecT :=
  mkgt [r5Row, g6Row 2 [0, 0, 0, 0] w0000 [4, 0, 0, 0] w1000']
    [(hA, 0), (hA, 2), (hB, 0), (hB, 1), (hA, 3), (hB, 2), (hB, 3), (hB, 5)] g6Deps

theorem gs6CatT : rvwmoCatConsistentT gs6 := catTConsistentBSound _ (by decide +kernel)
theorem gr6CatT : rvwmoCatConsistentT gr6 := catTConsistentBSound _ (by decide +kernel)
theorem gs6CtrlClosed : ctrlClosed gs6 := ctrlClosedBSound _ gs6CatT.1 (by decide +kernel)
theorem gr6CtrlClosed : ctrlClosed gr6 := ctrlClosedBSound _ gr6CatT.1 (by decide +kernel)

theorem gs6Harts : ∀ e, e ∈ gs6.gtG.gxGmo → e.1 = hA ∨ e.1 = hB := by
  intro e He
  have h : gs6.gtG.gxGmo.all (fun e : Geid => decide (e.1 = hA ∨ e.1 = hB)) = true := by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.1 h e He)

theorem gr6Harts : ∀ e, e ∈ gr6.gtG.gxGmo → e.1 = hA ∨ e.1 = hB := by
  intro e He
  have h : gr6.gtG.gxGmo.all (fun e : Geid => decide (e.1 = hA ∨ e.1 = hB)) = true := by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.1 h e He)

/-- B claims A's release; both of B's loads read A's word (every byte). -/
theorem gs6Shape :
    grfAt gs6.gtG ya (hA, 3) (hB, 0) ∧
    grfAt gs6.gtG xa (hA, 1) (hB, 1) ∧ grfAt gs6.gtG xa (hA, 1) (hB, 2) ∧
    grfAt gs6.gtG (xa + 3) (hA, 1) (hB, 1) ∧ grfAt gs6.gtG (xa + 3) (hA, 1) (hB, 2) :=
  ⟨(grfAtBSpec _ _ _ _).1 (by decide +kernel), (grfAtBSpec _ _ _ _).1 (by decide +kernel),
    (grfAtBSpec _ _ _ _).1 (by decide +kernel), (grfAtBSpec _ _ _ _).1 (by decide +kernel),
    (grfAtBSpec _ _ _ _).1 (by decide +kernel)⟩

theorem a6WpdAt (GT : GdexecT) (Hc : rvwmoCatConsistentT GT)
    (Hr : AxOpsem.grow (gtAdGd GT) hA = a6Row 0) :
    ∀ [InvGS_gen .hasNoLC spinGF] [AxannotGS spinGF] (nm : spinN),
      ⊢ spinInit6 ya (clRange xa 4) [ca] (gtAdGd GT) nm hA -∗
        @tierAWpd spinGF .hasNoLC _ _ (splPol GT) (gtAdGd GT) spinN Unit
          (spinOb6 ya (clRange xa 4) [ca] cv5) nm ⟨hp cpu0 a6M0 zeroRegs, 0⟩ .MaybeStuck hA
          (fun _ => iprop(True)) := by
  intro _ _ nm
  unfold spinInit6
  iintro ⟨Hil, Hnh⟩
  iapply (wpdA6 (hlc := .hasNoLC) (GF := spinGF) GT nm cpu0 (catTAd GT Hc) 0 Hr) $$ Hil Hnh

theorem a6RunAt (GT : GdexecT) (Hr : AxOpsem.grow (gtAdGd GT) hA = a6Row 0) :
    ∀ (_ : AxannotGS spinGF) (nm : spinN),
      nsteps (tierAAstep (gtAdGd GT) nm hA) 5
        ⟨hp cpu0 a6M0 zeroRegs, 0⟩ ⟨hp cpu0 hlt zeroRegs, 4⟩ :=
  fun _ _ => a6Run cpu0 (gtAdGd GT) 0 Hr

/-- (a) SATISFIABILITY -- EVERY premise of `csDblLoad` on `gs6`, A PROVED at the real
protocol. -/
theorem gs6Premises :
    rvwmoCatConsistentT gs6 ∧ ctrlClosed gs6 ∧
    (∀ e, e ∈ gs6.gtG.gxGmo → e.1 = hA ∨ e.1 = hB) ∧
    ([2, 2, 2, 2] : List Nat).length = 4 ∧ w1000.length = 4 ∧
    AxOpsem.grow (gtAdGd gs6) hB = g6Row 3 [2, 2, 2, 2] w1000 [2, 2, 2, 2] w1000 ∧
    (∀ (_ : AxannotGS spinGF) (nm : spinN),
      nsteps (tierAAstep (gtAdGd gs6) nm hA) 5
        ⟨hp cpu0 a6M0 zeroRegs, 0⟩ ⟨hp cpu0 hlt zeroRegs, 4⟩) ∧
    (⟨hp cpu0 a6M0 zeroRegs, 0⟩ : Athread).atK = 0 ∧
    (⟨hp cpu0 hlt zeroRegs, 4⟩ : Athread).atK = (AxOpsem.grow (gtAdGd gs6) hA).length ∧
    (∀ [InvGS_gen .hasNoLC spinGF] [AxannotGS spinGF] (nm : spinN),
      ⊢ spinInit6 ya (clRange xa 4) [ca] (gtAdGd gs6) nm hA -∗
        @tierAWpd spinGF .hasNoLC _ _ (splPol gs6) (gtAdGd gs6) spinN Unit
          (spinOb6 ya (clRange xa 4) [ca] cv5) nm ⟨hp cpu0 a6M0 zeroRegs, 0⟩ .MaybeStuck hA
          (fun _ => iprop(True))) :=
  ⟨gs6CatT, gs6CtrlClosed, gs6Harts, rfl, wbytesLength 4 one4, rfl, a6RunAt gs6 rfl, rfl, rfl,
    a6WpdAt gs6 gs6CatT rfl⟩

/-- The capstone fires on `gs6`; the conclusion is TRUE there. -/
theorem gs6Sound : w1000 = w1000 :=
  csDblLoad gs6 gs6CatT gs6CtrlClosed gs6Harts 3 [2, 2, 2, 2] w1000 [2, 2, 2, 2] w1000 rfl
    (wbytesLength 4 one4) rfl (wbytesLength 4 one4) rfl _ _ 5 (a6RunAt gs6 rfl) rfl rfl
    (a6WpdAt gs6 gs6CatT rfl)

/-- (b) THE RACE: on the consistent, ctrl-closed `gr6` the second load reads A''s post-release
byte; every other premise holds, so A''s WPd at `spinOb6` is UNPROVABLE. -/
theorem gr6Shape :
    grfAt gr6.gtG ya (hA, 2) (hB, 0) ∧ grfAt gr6.gtG xa (hA, 3) (hB, 2) ∧
    gmoLt gr6.gtG (hB, 1) (hA, 3) ∧ gmoLt gr6.gtG (hA, 3) (hB, 2) ∧
    w1000' ≠ w0000 :=
  ⟨(grfAtBSpec _ _ _ _).1 (by decide +kernel), (grfAtBSpec _ _ _ _).1 (by decide +kernel),
    (gmoLtBSpec _ _ _).1 (by decide +kernel), (gmoLtBSpec _ _ _).1 (by decide +kernel),
    by decide⟩

theorem gr6WpdUnprovable :
    ¬ (∀ [InvGS_gen .hasNoLC spinGF] [AxannotGS spinGF] (nm : spinN),
        ⊢ spinInit6 ya (clRange xa 4) [ca] (gtAdGd gr6) nm hA -∗
          @tierAWpd spinGF .hasNoLC _ _ (splPol gr6) (gtAdGd gr6) spinN Unit
            (spinOb6 ya (clRange xa 4) [ca] cv5) nm ⟨hp cpu0 r5M0 zeroRegs, 0⟩ .MaybeStuck hA
            (fun _ => iprop(True))) := by
  intro Hwp
  have Hrun : ∀ (_ : AxannotGS spinGF) (nm : spinN),
      nsteps (tierAAstep (gtAdGd gr6) nm hA) 5
        ⟨hp cpu0 r5M0 zeroRegs, 0⟩ ⟨hp cpu0 hlt zeroRegs, 4⟩ :=
    fun _ _ => r5Run cpu0 (gtAdGd gr6) rfl
  have Hv := csDblLoad gr6 gr6CatT gr6CtrlClosed gr6Harts 2 [0, 0, 0, 0] w0000 [4, 0, 0, 0]
    w1000' rfl rfl rfl rfl rfl _ _ 5 Hrun rfl rfl Hwp
  exact gr6Shape.2.2.2.2 Hv

/-- (c) SANITY TWIN: the same A' IS verifiable at the trivial protocol. -/
theorem gr6WpdTrivial :
    ∀ [InvGS_gen .hasNoLC spinGF] [AxannotGS spinGF] (nm : Unit),
      ⊢ (iprop(emp) : IProp spinGF) -∗
        @tierAWpd spinGF .hasNoLC _ _ (splPol gr6) (gtAdGd gr6) Unit Unit trivOb nm
          ⟨hp cpu0 r5M0 zeroRegs, 0⟩ .MaybeStuck hA (fun _ => iprop(True)) := by
  intro _ _ nm
  cases nm
  iintro _
  iapply (wpdR5Triv (hlc := .hasNoLC) (GF := spinGF) gr6 cpu0 rfl)

end Weak
