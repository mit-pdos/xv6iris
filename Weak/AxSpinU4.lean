/-
Weak: **UNIFY, part 4 of the spinlock plan -- CAPSTONES at `Ixv6` and CERTIFICATES** for the
allocpid-shaped critical section of `AxSpinU2` (hand nodes at real widths, no fetch/decode,
layout `Lx`, certificate graphs decided by the shipped checker).

Rocq: `iris/AxSpinU4.v` @ xxvzwolszwmp.

## The Rocq header, in substance

CAPSTONES (GF := `AxSpinX7.xv6GF`; adequacy `tierAAdequacyAnnGateT`, `xv6HobAlloc`, `xv6Hok`):
  `uAlloc2` -- both harts `[hA, hB]` run `uRow`: on every tagged-consistent, ctrl-closed graph
    with only these harts, image lk->cpu = 0 and nextpid = n0 < 2³², nowrap for both read words:
      `upost A wA ∧ upost B wB ∧ wA ≠ wB`.
    `upost i w` (each hart's post, READ BACK at its row end from the lw's and the sw's
    annotations) = `npSrc` (ownership-derived, at the lw's flow equation) ∧ the minted
    fragment's value is the read word.  `wA ≠ wB` comes from the PURE DICHOTOMY
    `AxSpinU3.uDistinct`, NOT from fragment exclusivity (`AxSpinU2.upostJoint` is the
    ghost-level joint step; no joint adequacy theorem exists -- stated, not used).
  `uCsSrc` -- hart A ARBITRARY (any WPd at `Ixv6` from `xv6Init`, any run), hart B runs `uRow`:
    `upost B wB`.  Ownership is load-bearing in the STATEMENT (certificate (b)).
CERTIFICATES
  (a) `uaPremises`: every premise of `uAlloc2` on the concrete `ua` (A claims the genesis lock,
      reads nextpid = 0, writes 1, releases; B claims A's release, reads A's 1 -- `uaShape`);
      `uaSound`: the capstone fires; `uaSrcSound`: `uCsSrc` fires on `ua` with A's WPd =
      `AxSpinU2.wpdCs`.
  (b) `urWpdUnprovable` -- RACE: A' = an UNLOCKED nextpid writer (`sw nextpid ← 5`); on the
      consistent, ctrl-closed `ur` B claims the genesis lock, A''s store lands gmo-AFTER B's
      claim and B's lw reads it (`urShape`): `upost B` is false (`urNotSrc`), so A''s WPd at
      `Ixv6` is UNPROVABLE.
  (c) `urWpdTrivial` -- SANITY TWIN: the same A' IS verifiable at the trivial protocol.

## Deviations from Rocq

1. VOCABULARY (as `AxSpinX7` deviation 1): `Z` ↦ `Int`, `bv n` ↦ `BitVec n`, `gt_g GT` ↦
   `GT.gtG`, `gd_g GD` ↦ `GD.gdG`, `l !! j` ↦ `l[j]?` (indices `Nat`), `pa_z` ↦ `paZ`,
   `Z_to_bv 32` ↦ `BitVec.ofInt 32`, `bv_unsigned w + 1 < 2^32` ↦ `w.toNat + 1 < 2 ^ 32`
   (over `Nat`), `a ≤ b < c` ↦ `a ≤ b ∧ b < c`, `B0` ↦ `b0`, `init_regstate` ↦ `zeroRegs`,
   `AThread p k` ↦ `⟨p, k⟩`, `M unit` ↦ `SailM Unit` (`rnM0` an `abbrev`, as the hand programs
   of `AxSpinX4`/`AxSpinU2`).  The notation `OBX` is `protXv6 Lx` inline; `xv6Σ` is
   `AxSpinX7.xv6GF`.
2. CONTEXTS (as `AxSpinX7` deviation 3): the capstones' `set` locals are the Lean-only defs
   `AxSpinU4.cPost2` (u_alloc2's `post`; `s0`/`sN`/`nf` there are constant lambdas) and
   `AxSpinU4.cS0`/`cSN`/`cN`/`cPost` (u_cs_src's); `HwpA` and the certificate statements take
   `[InvGS_gen .hasNoLC xv6GF] [AxannotGS xv6GF]` instance binders; the policy `xv6Pol GT` is
   passed explicitly.  Section `runrn`'s unused `axirisG Σ` is dropped (`cpu` an explicit
   leading argument); section `wpdRN`'s variables are `{hlc GF} [InvGS_gen hlc GF]
   [AxannotGS GF]` then explicit `GT cpu Hrow` (any `hlc`); its local instances `rn_pol`/`rn_G`
   are inlined (`xv6Pol GT` and `shG (gtAdGd GT) Unit Unit trivOb ()` passed explicitly).
   O2 STAGE C: Rocq's `Tf` argument of `tierA_astep`/`tierA_wpd` is gone (the rows contain no
   fetch events, so row positions, gmo lists and ctrl edges are Rocq's verbatim).
3. PROOFS: `vm_compute`/`vmr` ↦ `decide +kernel`; `ua_harts`-style `repeat constructor` ↦ a
   decided `List.all` (as `AxSpinX7`); `harts_of_gmo`/`imgt_clb`/`imgt_np`/`nowrap_zero`/
   `nowrap_one` are `AxSpinX7`'s `hartsOfGmo`/`imgtClb`/`imgtNp`/`nowrapZero`/`nowrapOne`.
   `feTrivu` reuses `AxSpinProt3.feTriv` (same statement at this policy).
4. The §4 `Check`/`Print Assumptions` lines are not ported (the lint's axiom check covers them).

**Rocq → Lean name map.**  `u_alloc2` `uAlloc2`, `u_cs_src` `uCsSrc`, `u_ctrl` `uCtrl`,
`ua_rowA` `uaRowA`, `ua_rowB` `uaRowB`, `ua` `ua`, `xr` `AxSpinU4.xr` (dup: AxLockRace),
`rn_m0` `rnM0`, `rn_row` `rnRow`, `ur_rowB` `urRowB`, `ur` `ur`, `ua_cat_t` `uaCatT`,
`ur_cat_t` `urCatT`, `ua_ctrl_closed` `uaCtrlClosed`, `ur_ctrl_closed` `urCtrlClosed`,
`ua_harts` `uaHarts`, `ur_harts` `urHarts`, `nowrap_xr` `nowrapXr`, `u_wpd_on` `uWpdOn`,
`u_run_on` `uRunOn`, `ua_shape` `uaShape`, `ua_premises` `uaPremises`, `ua_sound` `uaSound`,
`ua_src_sound` `uaSrcSound`, `rn_run` `rnRun`, `rn_run_ur` `rnRunUr`, `ur_shape` `urShape`,
`ur_not_src` `urNotSrc`, `ur_wpd_unprovable` `urWpdUnprovable`, `fe_trivu` `feTrivu`,
`wpdRN_triv` `wpdRNTriv`, `ur_wpd_trivial` `urWpdTrivial`.
Lean-only (file-qualified): `AxSpinU4.cPost2`, `AxSpinU4.cS0`/`cSN`/`cN`/`cPost`.

**Dropped:** none.  Rocq 34 decls (32 definitions/theorems + the 2 local instances `rn_pol`/
`rn_G`, inlined); Lean 37 = 32 ported + 5 Lean-only.
-/
import Weak.AxSpinU3
import Weak.AxSpinX7

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std Iris.Std.PartialMap MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D
open Dtag

/-! # 1. CAPSTONES -/

/-- Lean-only (Rocq `u_alloc2`'s `set post`). -/
def AxSpinU4.cPost2 (GT : GdexecT) (wA wB : BitVec 32) (i : Agent) (_ : Athread) : Prop :=
  if i = hA then upost (gtAdGd GT).gdG hA wA else upost (gtAdGd GT).gdG hB wB

theorem uAlloc2 (GT : GdexecT)
    (HconsT : rvwmoCatConsistentT GT) (Hcl : ctrlClosed GT)
    (Hharts : ∀ e, e ∈ GT.gtG.gxGmo → e.1 = hA ∨ e.1 = hB)
    (Himgc : ∀ a, a ∈ clb Lx → GT.gtG.gxImg a = some b0)
    (n0 : Int) (Hn0 : 0 ≤ n0 ∧ n0 < 2 ^ 32)
    (Himgn : ∀ (j : Nat) a v, (npb Lx)[j]? = some a →
      (WeakInterpProj.wbytes 4 (BitVec.ofInt 32 n0))[j]? = some v → GT.gtG.gxImg a = some v)
    (tA : Nat) (tsA : List Nat) (wA : BitVec 32) (tB : Nat) (tsB : List Nat) (wB : BitVec 32)
    (HrA : AxOpsem.grow (gtAdGd GT) hA = uRow tA tsA wA)
    (HrB : AxOpsem.grow (gtAdGd GT) hB = uRow tB tsB wB)
    (HnA : wA.toNat + 1 < 2 ^ 32) (HnB : wB.toNat + 1 < 2 ^ 32) :
    upost GT.gtG hA wA ∧ upost GT.gtG hB wB ∧ wA ≠ wB := by
  have Hin01 : ∀ i : Agent, i ∈ [hA, hB] → i = hA ∨ i = hB := by
    intro i Hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at Hi
    exact Hi
  have Hnd : [hA, hB].Nodup := by decide
  have Hharts' : ∀ e, e ∈ GT.gtG.gxGmo → e.1 ∈ [hA, hB] := by
    intro e He
    rcases Hharts e He with H | H <;> rw [H] <;> simp
  have Hcons := catTAd GT HconsT
  have Hrun : ∀ (_ : AxannotGS AxSpinX7.xv6GF) (nm : Xv6N) i, i ∈ [hA, hB] →
      nsteps (tierAAstep (gtAdGd GT) nm i) ((fun _ => 6) i)
        ((fun _ => (⟨hp cpu0 uM0 zeroRegs, 0⟩ : Athread)) i)
        ((fun _ => (⟨hp cpu0 hlt zeroRegs, 5⟩ : Athread)) i) := by
    intro _ nm i Hi
    rcases Hin01 i Hi with rfl | rfl
    · exact uRun cpu0 (gtAdGd GT) hA tA tsA wA HrA
    · exact uRun cpu0 (gtAdGd GT) hB tB tsB wB HrB
  have Hk0 : ∀ i, i ∈ [hA, hB] →
      ((fun _ => (⟨hp cpu0 uM0 zeroRegs, 0⟩ : Athread)) i).atK = 0 := fun _ _ => rfl
  have Hend : ∀ i, i ∈ [hA, hB] →
      ((fun _ => (⟨hp cpu0 hlt zeroRegs, 5⟩ : Athread)) i).atK =
        (AxOpsem.grow (gtAdGd GT) i).length := by
    intro i Hi
    rcases Hin01 i Hi with rfl | rfl
    · show 5 = (AxOpsem.grow (gtAdGd GT) hA).length
      rw [HrA]
      rfl
    · show 5 = (AxOpsem.grow (gtAdGd GT) hB).length
      rw [HrB]
      rfl
  have Hwp : ∀ [InvGS_gen .hasNoLC AxSpinX7.xv6GF] [AxannotGS AxSpinX7.xv6GF] (nm : Xv6N),
      ⊢ ([∗list] i ∈ [hA, hB], xv6Init Lx (gtAdGd GT) nm i) -∗
        [∗list] i ∈ [hA, hB],
          @tierAWpd AxSpinX7.xv6GF .hasNoLC _ _ (xv6Pol GT) (gtAdGd GT) Xv6N Unit (protXv6 Lx)
            nm ((fun _ => (⟨hp cpu0 uM0 zeroRegs, 0⟩ : Athread)) i) .MaybeStuck i
            (fun s => iprop(⌜AxSpinU4.cPost2 GT wA wB i s⌝)) := by
    intro Hinv Hann nm
    iintro HI
    icases (AxTokLedgerMp.bigSepLPair hA hB
      (fun i => xv6Init (GF := AxSpinX7.xv6GF) Lx (gtAdGd GT) nm i)).1 $$ HI with ⟨HA, HB⟩
    iapply (AxTokLedgerMp.bigSepLPair hA hB _).2
    isplitl [HA]
    · iapply (AxSpinWit.tierAWpdMono (hlc := .hasNoLC) (pol := xv6Pol GT) (gtAdGd GT) Xv6N Unit
        (protXv6 Lx) nm ⟨hp cpu0 uM0 zeroRegs, 0⟩ .MaybeStuck hA
        (fun _ => iprop(⌜upost (gtAdGd GT).gdG hA wA⌝))
        (fun s => iprop(⌜AxSpinU4.cPost2 GT wA wB hA s⌝))
        (fun _ => pure_mono (fun Hv => by
          unfold AxSpinU4.cPost2; rw [if_pos rfl]; exact Hv)))
      unfold xv6Init
      icases HA with ⟨-, -, -, Hil, Hnh⟩
      iapply (wpdCsPure (hlc := .hasNoLC) (GF := AxSpinX7.xv6GF) GT nm cpu0 Hcons hA tA tsA wA
        HrA HnA) $$ Hil Hnh
    · iapply (AxSpinWit.tierAWpdMono (hlc := .hasNoLC) (pol := xv6Pol GT) (gtAdGd GT) Xv6N Unit
        (protXv6 Lx) nm ⟨hp cpu0 uM0 zeroRegs, 0⟩ .MaybeStuck hB
        (fun _ => iprop(⌜upost (gtAdGd GT).gdG hB wB⌝))
        (fun s => iprop(⌜AxSpinU4.cPost2 GT wA wB hB s⌝))
        (fun _ => pure_mono (fun Hv => by
          unfold AxSpinU4.cPost2; rw [if_neg (by decide)]; exact Hv)))
      unfold xv6Init
      icases HB with ⟨-, -, -, Hil, Hnh⟩
      iapply (wpdCsPure (hlc := .hasNoLC) (GF := AxSpinX7.xv6GF) GT nm cpu0 Hcons hB tB tsB wB
        HrB HnB) $$ Hil Hnh
  have Hfin := @tierAAdequacyAnnGateT AxSpinX7.xv6GF _ _ (xv6Pol GT) GT Xv6N Unit (protXv6 Lx)
    (xv6Init Lx (gtAdGd GT)) (xv6AxpolWf GT) HconsT [hA, hB] Hnd Hharts'
    (fun _ => (⟨hp cpu0 uM0 zeroRegs, 0⟩ : Athread))
    (fun _ => (⟨hp cpu0 hlt zeroRegs, 5⟩ : Athread)) (fun _ => 6) Hrun Hk0 Hend
    (AxSpinU4.cPost2 GT wA wB) Hwp
    (xv6HobAlloc (GF := AxSpinX7.xv6GF) Lx (gtAdGd GT) n0 LxOk Himgc Hn0 Himgn)
    (xv6Hok GT HconsT Hcl)
  have HA : upost (gtAdGd GT).gdG hA wA := by
    have h := Hfin hA (by simp)
    unfold AxSpinU4.cPost2 at h
    rw [if_pos rfl] at h
    exact h
  have HB : upost (gtAdGd GT).gdG hB wB := by
    have h := Hfin hB (by simp)
    unfold AxSpinU4.cPost2 at h
    rw [if_neg (by decide)] at h
    exact h
  exact ⟨HA, HB, uDistinct (gtAdGd GT) Hcons hA hB (by decide) Hharts tA tB tsA tsB wA wB HrA HrB
    HnA HnB⟩

/-- Lean-only (Rocq `u_cs_src`'s `set s0`). -/
def AxSpinU4.cS0 (sA0 : Athread) (i : Agent) : Athread :=
  if i = hA then sA0 else ⟨hp cpu0 uM0 zeroRegs, 0⟩
/-- Lean-only (Rocq `u_cs_src`'s `set sN`). -/
def AxSpinU4.cSN (sAN : Athread) (i : Agent) : Athread :=
  if i = hA then sAN else ⟨hp cpu0 hlt zeroRegs, 5⟩
/-- Lean-only (Rocq `u_cs_src`'s `set nf`). -/
def AxSpinU4.cN (nA : Nat) (i : Agent) : Nat := if i = hA then nA else 6
/-- Lean-only (Rocq `u_cs_src`'s `set post`). -/
def AxSpinU4.cPost (GT : GdexecT) (wB : BitVec 32) (i : Agent) (_ : Athread) : Prop :=
  if i = hB then upost (gtAdGd GT).gdG hB wB else True

theorem uCsSrc (GT : GdexecT)
    (HconsT : rvwmoCatConsistentT GT) (Hcl : ctrlClosed GT)
    (Hharts : ∀ e, e ∈ GT.gtG.gxGmo → e.1 = hA ∨ e.1 = hB)
    (Himgc : ∀ a, a ∈ clb Lx → GT.gtG.gxImg a = some b0)
    (n0 : Int) (Hn0 : 0 ≤ n0 ∧ n0 < 2 ^ 32)
    (Himgn : ∀ (j : Nat) a v, (npb Lx)[j]? = some a →
      (WeakInterpProj.wbytes 4 (BitVec.ofInt 32 n0))[j]? = some v → GT.gtG.gxImg a = some v)
    (tB : Nat) (tsB : List Nat) (wB : BitVec 32)
    (HrB : AxOpsem.grow (gtAdGd GT) hB = uRow tB tsB wB) (HnB : wB.toNat + 1 < 2 ^ 32)
    (sA0 sAN : Athread) (nA : Nat)
    (HrunA : ∀ (_ : AxannotGS AxSpinX7.xv6GF) (nm : Xv6N),
      nsteps (tierAAstep (gtAdGd GT) nm hA) nA sA0 sAN)
    (HkA : sA0.atK = 0) (HendA : sAN.atK = (AxOpsem.grow (gtAdGd GT) hA).length)
    (HwpA : ∀ [InvGS_gen .hasNoLC AxSpinX7.xv6GF] [AxannotGS AxSpinX7.xv6GF] (nm : Xv6N),
      ⊢ xv6Init Lx (gtAdGd GT) nm hA -∗
        @tierAWpd AxSpinX7.xv6GF .hasNoLC _ _ (xv6Pol GT) (gtAdGd GT) Xv6N Unit (protXv6 Lx) nm
          sA0 .MaybeStuck hA (fun _ => iprop(True))) :
    upost GT.gtG hB wB := by
  have Hin01 : ∀ i : Agent, i ∈ [hA, hB] → i = hA ∨ i = hB := by
    intro i Hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at Hi
    exact Hi
  have Hnd : [hA, hB].Nodup := by decide
  have Hharts' : ∀ e, e ∈ GT.gtG.gxGmo → e.1 ∈ [hA, hB] := by
    intro e He
    rcases Hharts e He with H | H <;> rw [H] <;> simp
  have Hcons := catTAd GT HconsT
  have Hrun : ∀ (_ : AxannotGS AxSpinX7.xv6GF) (nm : Xv6N) i, i ∈ [hA, hB] →
      nsteps (tierAAstep (gtAdGd GT) nm i) (AxSpinU4.cN nA i) (AxSpinU4.cS0 sA0 i)
        (AxSpinU4.cSN sAN i) := by
    intro Hann nm i Hi
    rcases Hin01 i Hi with rfl | rfl
    · exact HrunA Hann nm
    · exact uRun cpu0 (gtAdGd GT) hB tB tsB wB HrB
  have Hk0 : ∀ i, i ∈ [hA, hB] → (AxSpinU4.cS0 sA0 i).atK = 0 := by
    intro i Hi
    rcases Hin01 i Hi with rfl | rfl
    · exact HkA
    · rfl
  have Hend : ∀ i, i ∈ [hA, hB] →
      (AxSpinU4.cSN sAN i).atK = (AxOpsem.grow (gtAdGd GT) i).length := by
    intro i Hi
    rcases Hin01 i Hi with rfl | rfl
    · exact HendA
    · show 5 = (AxOpsem.grow (gtAdGd GT) hB).length
      rw [HrB]
      rfl
  have Hwp : ∀ [InvGS_gen .hasNoLC AxSpinX7.xv6GF] [AxannotGS AxSpinX7.xv6GF] (nm : Xv6N),
      ⊢ ([∗list] i ∈ [hA, hB], xv6Init Lx (gtAdGd GT) nm i) -∗
        [∗list] i ∈ [hA, hB],
          @tierAWpd AxSpinX7.xv6GF .hasNoLC _ _ (xv6Pol GT) (gtAdGd GT) Xv6N Unit (protXv6 Lx)
            nm (AxSpinU4.cS0 sA0 i) .MaybeStuck i
            (fun s => iprop(⌜AxSpinU4.cPost GT wB i s⌝)) := by
    intro Hinv Hann nm
    iintro HI
    icases (AxTokLedgerMp.bigSepLPair hA hB
      (fun i => xv6Init (GF := AxSpinX7.xv6GF) Lx (gtAdGd GT) nm i)).1 $$ HI with ⟨HA, HB⟩
    iapply (AxTokLedgerMp.bigSepLPair hA hB _).2
    rw [show AxSpinU4.cS0 sA0 hA = sA0 from if_pos rfl,
      show AxSpinU4.cS0 sA0 hB = ⟨hp cpu0 uM0 zeroRegs, 0⟩ from if_neg (by decide)]
    isplitl [HA]
    · iapply (AxSpinWit.tierAWpdMono (hlc := .hasNoLC) (pol := xv6Pol GT) (gtAdGd GT) Xv6N Unit
        (protXv6 Lx) nm sA0 .MaybeStuck hA (fun _ => iprop(True))
        (fun s => iprop(⌜AxSpinU4.cPost GT wB hA s⌝))
        (fun _ => pure_mono (fun _ => by
          unfold AxSpinU4.cPost; rw [if_neg (by decide)]; trivial)))
      iapply HwpA nm $$ HA
    · iapply (AxSpinWit.tierAWpdMono (hlc := .hasNoLC) (pol := xv6Pol GT) (gtAdGd GT) Xv6N Unit
        (protXv6 Lx) nm ⟨hp cpu0 uM0 zeroRegs, 0⟩ .MaybeStuck hB
        (fun _ => iprop(⌜upost (gtAdGd GT).gdG hB wB⌝))
        (fun s => iprop(⌜AxSpinU4.cPost GT wB hB s⌝))
        (fun _ => pure_mono (fun Hv => by
          unfold AxSpinU4.cPost; rw [if_pos rfl]; exact Hv)))
      unfold xv6Init
      icases HB with ⟨-, -, -, Hil, Hnh⟩
      iapply (wpdCsPure (hlc := .hasNoLC) (GF := AxSpinX7.xv6GF) GT nm cpu0 Hcons hB tB tsB wB
        HrB HnB) $$ Hil Hnh
  have Hfin := @tierAAdequacyAnnGateT AxSpinX7.xv6GF _ _ (xv6Pol GT) GT Xv6N Unit (protXv6 Lx)
    (xv6Init Lx (gtAdGd GT)) (xv6AxpolWf GT) HconsT [hA, hB] Hnd Hharts'
    (AxSpinU4.cS0 sA0) (AxSpinU4.cSN sAN) (AxSpinU4.cN nA) Hrun Hk0 Hend
    (AxSpinU4.cPost GT wB) Hwp
    (xv6HobAlloc (GF := AxSpinX7.xv6GF) Lx (gtAdGd GT) n0 LxOk Himgc Hn0 Himgn)
    (xv6Hok GT HconsT Hcl) hB (by simp)
  unfold AxSpinU4.cPost at Hfin
  rw [if_pos rfl] at Hfin
  exact Hfin

/-! # 2. Certificate graphs -/

/-- The branch-feeding amoswap controls every po-later store (closed). -/
def uCtrl (i : Agent) : List Tdep :=
  [(((i, 0), (i, 2)), DTctrl), (((i, 0), (i, 4)), DTctrl)]

/-- (a) A claims genesis, reads nextpid 0, writes 1, releases; B claims A's release, reads A's
1, writes 2, releases. -/
def uaRowA : List Lbl := uRow 0 [0, 0, 0, 0] zero32
def uaRowB : List Lbl := uRow 3 [2, 2, 2, 2] one32
def ua : GdexecT :=
  mkgt [uaRowA, uaRowB]
    [(hA, 0), (hA, 1), (hA, 2), (hA, 4), (hB, 0), (hB, 1), (hB, 2), (hB, 4)]
    (uCtrl hA ++ uCtrl hB)

/-- (b) THE RACE: A' stores nextpid := 5 WITHOUT the lock, gmo-after B's claim of the genesis
lock; B's lw reads it. -/
def AxSpinU4.xr : BitVec 32 := BitVec.ofInt 32 5
abbrev rnM0 : SailM Unit := stv 4 nppa AxSpinU4.xr hlt
def rnRow : List Lbl :=
  [.LStore false (paZ nppa) (WeakInterpProj.wbytes 4 AxSpinU4.xr) .WCplain]
def urRowB : List Lbl := uRow 0 [2, 2, 2, 2] AxSpinU4.xr
def ur : GdexecT :=
  mkgt [rnRow, urRowB] [(hB, 0), (hA, 0), (hB, 1), (hB, 2), (hB, 4)] (uCtrl hB)

theorem uaCatT : rvwmoCatConsistentT ua :=
  catTConsistentBSound _ (by decide +kernel)
theorem urCatT : rvwmoCatConsistentT ur :=
  catTConsistentBSound _ (by decide +kernel)
theorem uaCtrlClosed : ctrlClosed ua :=
  ctrlClosedBSound _ uaCatT.1 (by decide +kernel)
theorem urCtrlClosed : ctrlClosed ur :=
  ctrlClosedBSound _ urCatT.1 (by decide +kernel)

theorem uaHarts : ∀ e, e ∈ ua.gtG.gxGmo → e.1 = hA ∨ e.1 = hB := by
  apply hartsOfGmo
  intro e He
  have h : ua.gtG.gxGmo.all (fun e : Geid => decide (e.1 = hA ∨ e.1 = hB)) = true := by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.1 h e He)

theorem urHarts : ∀ e, e ∈ ur.gtG.gxGmo → e.1 = hA ∨ e.1 = hB := by
  apply hartsOfGmo
  intro e He
  have h : ur.gtG.gxGmo.all (fun e : Geid => decide (e.1 = hA ∨ e.1 = hB)) = true := by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.1 h e He)

theorem nowrapXr : AxSpinU4.xr.toNat + 1 < 2 ^ 32 := by decide +kernel

/-! # 3. Certificates -/

/-- The CS hart's WPd at `Ixv6` with the trivial post (as an "arbitrary A"). -/
theorem uWpdOn (GT : GdexecT) (HconsT : rvwmoCatConsistentT GT) (i : Agent) (t : Nat)
    (ts : List Nat) (w8 : BitVec 32) (Hrow : AxOpsem.grow (gtAdGd GT) i = uRow t ts w8)
    (Hn : w8.toNat + 1 < 2 ^ 32) :
    ∀ [InvGS_gen .hasNoLC AxSpinX7.xv6GF] [AxannotGS AxSpinX7.xv6GF] (nm : Xv6N),
      ⊢ xv6Init Lx (gtAdGd GT) nm i -∗
        @tierAWpd AxSpinX7.xv6GF .hasNoLC _ _ (xv6Pol GT) (gtAdGd GT) Xv6N Unit (protXv6 Lx) nm
          ⟨hp cpu0 uM0 zeroRegs, 0⟩ .MaybeStuck i (fun _ => iprop(True)) := by
  intro _ _ nm
  unfold xv6Init
  iintro ⟨-, -, -, Hil, Hnh⟩
  iapply (AxSpinWit.tierAWpdMono (hlc := .hasNoLC) (pol := xv6Pol GT) (gtAdGd GT) Xv6N Unit
    (protXv6 Lx) nm ⟨hp cpu0 uM0 zeroRegs, 0⟩ .MaybeStuck i
    (fun _ => iprop(⌜upost (gtAdGd GT).gdG i w8⌝)) (fun _ => iprop(True))
    (fun _ => pure_mono (fun _ => trivial)))
  iapply (wpdCsPure (hlc := .hasNoLC) (GF := AxSpinX7.xv6GF) GT nm cpu0 (catTAd GT HconsT) i t ts
    w8 Hrow Hn) $$ Hil Hnh

theorem uRunOn (GT : GdexecT) (i : Agent) (t : Nat) (ts : List Nat) (w8 : BitVec 32)
    (Hrow : AxOpsem.grow (gtAdGd GT) i = uRow t ts w8) :
    ∀ (_ : AxannotGS AxSpinX7.xv6GF) (nm : Xv6N),
      nsteps (tierAAstep (gtAdGd GT) nm i) 6
        ⟨hp cpu0 uM0 zeroRegs, 0⟩ ⟨hp cpu0 hlt zeroRegs, 5⟩ :=
  fun _ _ => uRun cpu0 (gtAdGd GT) i t ts w8 Hrow

/-- (a) the shape of `ua`: B claims A's release and reads A's increment. -/
theorem uaShape :
    grfAt ua.gtG (paZ lkpa) (hA, 4) (hB, 0) ∧ grfAt ua.gtG (paZ nppa) (hA, 2) (hB, 1) :=
  ⟨(grfAtBSpec _ _ _ _).1 (by decide +kernel), (grfAtBSpec _ _ _ _).1 (by decide +kernel)⟩

/-- EVERY premise of `uAlloc2` on `ua`. -/
theorem uaPremises :
    rvwmoCatConsistentT ua ∧ ctrlClosed ua ∧
    (∀ e, e ∈ ua.gtG.gxGmo → e.1 = hA ∨ e.1 = hB) ∧
    (∀ a, a ∈ clb Lx → ua.gtG.gxImg a = some b0) ∧
    (∀ (j : Nat) a v, (npb Lx)[j]? = some a →
      (WeakInterpProj.wbytes 4 (BitVec.ofInt 32 0))[j]? = some v → ua.gtG.gxImg a = some v) ∧
    AxOpsem.grow (gtAdGd ua) hA = uaRowA ∧ AxOpsem.grow (gtAdGd ua) hB = uaRowB ∧
    zero32.toNat + 1 < 2 ^ 32 ∧ one32.toNat + 1 < 2 ^ 32 :=
  ⟨uaCatT, uaCtrlClosed, uaHarts, imgtClb ua rfl, imgtNp ua rfl, rfl, rfl, nowrapZero,
    nowrapOne⟩

/-- The capstone fires on `ua`; its conclusion is TRUE there. -/
theorem uaSound : upost ua.gtG hA zero32 ∧ upost ua.gtG hB one32 ∧ zero32 ≠ one32 :=
  uAlloc2 ua uaCatT uaCtrlClosed uaHarts (imgtClb ua rfl) 0 ⟨by decide, by decide⟩
    (imgtNp ua rfl) 0 [0, 0, 0, 0] zero32 3 [2, 2, 2, 2] one32 rfl rfl nowrapZero nowrapOne

/-- The Theorem-2-shaped capstone fires on `ua` with A = the CS hart. -/
theorem uaSrcSound : upost ua.gtG hB one32 :=
  uCsSrc ua uaCatT uaCtrlClosed uaHarts (imgtClb ua rfl) 0 ⟨by decide, by decide⟩
    (imgtNp ua rfl) 3 [2, 2, 2, 2] one32 rfl nowrapOne _ _ 6
    (uRunOn ua hA 0 [0, 0, 0, 0] zero32 rfl) rfl rfl
    (uWpdOn ua uaCatT hA 0 [0, 0, 0, 0] zero32 rfl nowrapZero)

/-! (b) THE RACE -/

theorem rnRun (cpu : CPU) (GD : Gdexec) (Hrow : AxOpsem.grow GD hA = rnRow) :
    nsteps (astepAnyNfGv GD hA) 1 ⟨hp cpu rnM0 zeroRegs, 0⟩ ⟨hp cpu hlt zeroRegs, 1⟩ := by
  refine nsteps_l (nrunWrite cpu GD hA 4 (by decide) nppa nppaRam AxSpinU4.xr hlt zeroRegs 0
    .WCplain (by rw [Hrow]; rfl)) ?_
  exact nsteps_O _

theorem rnRunUr : ∀ (_ : AxannotGS AxSpinX7.xv6GF) (nm : Xv6N),
    nsteps (tierAAstep (gtAdGd ur) nm hA) 1
      ⟨hp cpu0 rnM0 zeroRegs, 0⟩ ⟨hp cpu0 hlt zeroRegs, 1⟩ :=
  fun _ _ => rnRun cpu0 (gtAdGd ur) rfl

/-- B claims the GENESIS lock; A''s unlocked store is gmo-AFTER B's claim and B's lw reads it. -/
theorem urShape :
    graphValue (gtAdGd ur) (hB, 0) = some AxSpinX4.z4 ∧
    gmoLt ur.gtG (hB, 0) (hA, 0) ∧ gmoLt ur.gtG (hA, 0) (hB, 1) ∧
    grfAt ur.gtG (paZ nppa) (hA, 0) (hB, 1) :=
  ⟨by decide +kernel, (gmoLtBSpec _ _ _).1 (by decide +kernel),
    (gmoLtBSpec _ _ _).1 (by decide +kernel), (grfAtBSpec _ _ _ _).1 (by decide +kernel)⟩

theorem urNotSrc : ¬ upost ur.gtG hB AxSpinU4.xr := by
  rintro ⟨Hs, -⟩
  have Ha : paZ nppa ∈ npb Lx := (npbLx _).2 ⟨Int.le_refl _, by omega⟩
  have Hl : gxLbl ur.gtG (hB, 1) =
      some (.LLoad false (paZ nppa) [2, 2, 2, 2] (WeakInterpProj.wbytes 4 AxSpinU4.xr)) := rfl
  have Hrd : greadsByte ur.gtG (hB, 1) (paZ nppa) 2 (nthByte (n := 4) AxSpinU4.xr 0) := by
    have H := (grbLoadn _ _ _ _ _ Hl).1 0 2 (nthByte (n := 4) AxSpinU4.xr 0) rfl
      (wbytesLookup 4 (m := 4) AxSpinU4.xr 0 (by omega))
    have e0 : paZ nppa + ((0 : Nat) : Int) = paZ nppa := by omega
    rw [e0] at H
    exact H
  have H2 : gwriteAt ur.gtG 2 = some (hA, 0) := by decide +kernel
  rcases Hs _ Ha _ _ Hrd with H0 | ⟨w, Hga, Hw | Hlt⟩
  · exact absurd H0 (by decide)
  · rw [H2] at Hga
    obtain rfl := Option.some.inj Hga
    exact absurd Hw (by decide)
  · rw [H2] at Hga
    obtain rfl := Option.some.inj Hga
    have Hb := (gmoLtBSpec _ _ _).2 Hlt
    have Hf : gmoLtB ur.gtG (hA, 0) (hB, 0) = false := by decide +kernel
    rw [Hf] at Hb
    exact Bool.noConfusion Hb

theorem urWpdUnprovable :
    ¬ (∀ [InvGS_gen .hasNoLC AxSpinX7.xv6GF] [AxannotGS AxSpinX7.xv6GF] (nm : Xv6N),
        ⊢ xv6Init Lx (gtAdGd ur) nm hA -∗
          @tierAWpd AxSpinX7.xv6GF .hasNoLC _ _ (xv6Pol ur) (gtAdGd ur) Xv6N Unit (protXv6 Lx) nm
            ⟨hp cpu0 rnM0 zeroRegs, 0⟩ .MaybeStuck hA (fun _ => iprop(True))) := by
  intro Hwp
  apply urNotSrc
  exact uCsSrc ur urCatT urCtrlClosed urHarts (imgtClb ur rfl) 0 ⟨by decide, by decide⟩
    (imgtNp ur rfl) 0 [2, 2, 2, 2] AxSpinU4.xr rfl nowrapXr _ _ 1 rnRunUr rfl rfl Hwp

/-! (c) THE SANITY TWIN at the trivial protocol -/

section wpdRN
variable {hlc : HasLC} {GF : BundledGFunctors.{0,0,0}} [InvGS_gen hlc GF] [AxannotGS GF]

theorem feTrivu (GT : GdexecT) (e : Geid) (s0 : GSet Geid) (fi : Mea GF) :
    ⊢ @flowEqDyn hlc GF _ (shG (gtAdGd GT) Unit Unit trivOb ()) (gtAdGd GT) e s0 fi
      iprop(True ∗ True) :=
  feTriv (hlc := hlc) (pol := xv6Pol GT) (gtAdGd GT) e s0 fi

theorem wpdRNTriv (GT : GdexecT) (cpu : CPU) (Hrow : AxOpsem.grow (gtAdGd GT) hA = rnRow) :
    ⊢ @tierAWpd GF hlc _ _ (xv6Pol GT) (gtAdGd GT) Unit Unit trivOb ()
      ⟨hp cpu rnM0 zeroRegs, 0⟩ .MaybeStuck hA (fun _ => iprop(True)) := by
  have Hne : 0 ≠ (AxOpsem.grow (gtAdGd GT) hA).length := by rw [Hrow]; simp [rnRow]
  have Hl0 : gxLbl (gtAdGd GT).gdG (hA, 0) =
      some (.LStore false (paZ nppa) (WeakInterpProj.wbytes 4 AxSpinU4.xr) .WCplain) := by
    rw [gxLblGrow, Hrow]; rfl
  have H := nshWrite (hlc := hlc) (GF := GF) (pol := xv6Pol GT) (gtAdGd GT) Unit Unit trivOb ()
    cpu hA (fun _ => iprop(True)) 4 nppa nppaRam AxSpinU4.xr hlt 0 Hne iprop(True)
    (fun rs => by
      have Hval : graphData (gtAdGd GT) (hA, 0) = some (WeakInterpProj.wbytes 4 AxSpinU4.xr) := by
        unfold graphData; rw [Hl0]; rfl
      iintro _
      iapply (evPlain (hlc := hlc) (pol := xv6Pol GT) (gtAdGd GT) Unit Unit trivOb () hA 0
        iprop(True) iprop(True) _ _ Hval) $$ []
      · iapply feTrivu
      iintro _ _
      iapply (shHltTrue (hlc := hlc) (pol := xv6Pol GT) (gtAdGd GT) Unit Unit trivOb () cpu hA
        (0 + 1)) $$ %rs)
  iapply H $$ [] %zeroRegs
  itrivial

end wpdRN

theorem urWpdTrivial :
    ∀ [InvGS_gen .hasNoLC AxSpinX7.xv6GF] [AxannotGS AxSpinX7.xv6GF] (nm : Unit),
      ⊢ (iprop(emp) : IProp AxSpinX7.xv6GF) -∗
        @tierAWpd AxSpinX7.xv6GF .hasNoLC _ _ (xv6Pol ur) (gtAdGd ur) Unit Unit trivOb nm
          ⟨hp cpu0 rnM0 zeroRegs, 0⟩ .MaybeStuck hA (fun _ => iprop(True)) := by
  intro _ _ nm
  cases nm
  iintro _
  iapply (wpdRNTriv (hlc := .hasNoLC) (GF := AxSpinX7.xv6GF) ur cpu0 rfl)

end Weak
