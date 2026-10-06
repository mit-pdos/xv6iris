/-
Weak: **xv6's BOOT HANDOFF as a message-passing theorem** -- the example that is not a spinlock.

Rocq: `iris/WkStartedMp.v` @ xxvzwolszwmp.

The Rocq header, in substance (Rocq vocabulary).  Every fence-mediated transfer proved so far in
the weak tier was the lock's release/acquire pair, where the acquiring `amoswap.w.aq` does the work
with no fence.  xv6's boot handoff is the other shape -- plain store, plain load, two ORDINARY
fences -- and it is the one the kernel uses to hand every secondary hart the results of hart 0's
initialisation (`kernel/main.c`: hart 0 `__atomic_store_n(&started, 1, __ATOMIC_RELEASE)`; every
other hart spins on `__atomic_load_n(&started, __ATOMIC_ACQUIRE)`).  WHERE THE ORDERING COMES FROM
in this machine: not from the writer's `fence rw,w` (promise-free, a store lands at the log's fresh
top, which dominates the writer's whole index, so the release deposit needs no fence -- design
doc, Decision 1); ALL of the content is on the reader: a plain load gains the timestamp it read
only at the BYTE it read, and `fence r,rw` turns that into a SCALAR index gain and so delivers the
deposit.  §3 makes that precise in both directions.  Nothing here is new machinery: §1 is
`WeakStarted.wstarted_set`, §2 is `WeakStarted.wstarted_reader` at `Barrier_RISCV_r_rw`, §4 is
`WeakVProp.wpt_load_rule`; the file adds the COMPOSITION: the byte a secondary hart loads after its
acquire fence is the byte hart 0 wrote before its release.  Still above this file: the
per-instruction leaves (`main` is S-mode; batch 6c).

**The kernel image (Lean, `Xv6/KernelImage.lean`).**  The comments' sites are checked against the
LEAN image: `main = 0x80000ece`; writer `main+0xac = 0x80000f7a` is `fence rw,w` (`0x0310000f`,
`Weak.ksFenceMainAcWord`), `main+0xb0 = 0x80000f7e` is `sw a4,0(a5)` -- in the Lean image the
COMPRESSED `c.sw` (`0xc398`, 2 bytes; Rocq's comment just says `sw`); reader `main+0x16 =
0x80000ee4` `c.lw a5,0(a4)` (`0x431c`), `main+0x18 = 0x80000ee6` `fence r,rw` (`0x0230000f`,
`Weak.ksFenceMain18Word`), `main+0x1c = 0x80000eea` `sext.w`, `main+0x1e = 0x80000eec` `beqz a5,
main+0x16`.  **Drift: none** in the offsets (Rocq's image places `main` elsewhere, but every
offset named is the same).  No statement names a kernel address, so nothing imports the image.

**Deviations from Rocq.**

1. NAMES / VOCABULARY: the tree's camelCase (map below); no name of this file is in
   `notes/weak-port-dupnames.json`.  `ak_coh akn = false` is `akn.akIfetch = false` (WeakRacy
   deviation 4); `monPred_at P V` is `P.monPred_at V`; `⊑` on views is `≤`; `Z` is `Int`;
   `nth_byte` is `nthByte (n := 4)`; `lock_one`/`lock_zero` are `lockOne`/`lockZero`;
   `DfracDiscarded` is `DFrac.discard`.  The section's `GenId`/`CpuId` context is unused by every
   statement and is dropped.
2. STATEMENT SHAPES (WeakAcquire deviation 2): Rocq `A -∗ B -∗ C` is `A ⊢ B -∗ C`; the release's
   `==∗` is `-∗ |==> (…)`; the `Corollary` is a `theorem`.
3. `wstartedMpRelease`: the deposited witness is `wstartedAt a P (σ.wmLog.length + 1) lockOne`
   (Lean's `wstartedSet`), Rocq `S (length (wm_log σ))` -- the same timestamp.

**Rocq → Lean name map.**  `wstarted_mp_release` `wstartedMpRelease`, `wstarted_mp_acquire`
`wstartedMpAcquire`, `mp_load_alone_does_not_deliver` `mpLoadAloneDoesNotDeliver`,
`mp_fence_delivers` `mpFenceDelivers`, `mp_payload_arrives` `mpPayloadArrives`,
`wstarted_mp_byte` `wstartedMpByte`.  (Rocq 6 declarations; Lean 6.)

**Dropped:** nothing.  (`Print Assumptions` ↦ the CI axiom audit.)

**Statements checked** (by hand, against Rocq): all; the changed ones are deviations 1-3.
-/
import Weak.WkStartedLoad
import MachCSL.MonPredExtra

namespace Weak

open Iris Iris.BI Iris.BI.MonPred Iris.ProofMode Iris.Std
open MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D

section mp

variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [WeakGS GF]

/-! ## 1. HART 0: the release

`WeakStarted.wstartedSet` with the escrow repackaged, so the two sides compose over the SAME
`wstartedBody`.  The premises: the `sw`'s own step effect and `wsBounded` -- and, since the
φ-upgrade, the `wRelp` the preceding `fence rw,w` sets (it keeps the escrow's bundle CLEAN). -/

theorem wstartedMpRelease (a : PAddr) (P : VProp GF) (tid : Option Nat) (σ σ' : Wmstate) :
    wQStore tid a lockOne σ σ' →
    σ.wmWs.wRelp = true →
    wsBounded σ.wmWs σ.wmLog.length →
    wlogLb (GF := GF) σ.wmLog ⊢
      wlatInterp (GF := GF) σ.wmImg σ.wmLog -∗
        wstartedBody a P -∗
          vwpHold P σ.wmWs -∗
            |==> (wlatInterp (GF := GF) σ'.wmImg σ'.wmLog ∗ wstartedBody a P) := by
  intro hQ hrelp hbnd
  iintro #Hlb Hi Hbody HP
  imod wstartedSet a P tid σ σ' hQ hrelp hbnd $$ Hlb Hi Hbody HP with ⟨Hi, Hat⟩
  imodintro
  isplitl [Hi]
  · iexact Hi
  · unfold wstartedBody
    iexists (σ.wmLog.length + 1), lockOne
    iexact Hat

/-! ## 2. HART k: the withdrawal

`WeakStarted.wstartedReader` at the kernel's own fence kind.  A hart whose plain load of the flag
came back NON-CLEAR read a timestamp at or above the escrow's deposit, and its `fence r,rw`
delivers the deposit to its own index.  The view premise `t ≤ wVrOld` is `WeakRacy.wgain`.  The two
sides are not one lemma: `wlatInterp` is the authority over the latest-write map, so no
proposition holds it at hart 0's state and hart k's later state at once; the escrow (under an
`inv`, literally the same `P`) is the medium. -/

theorem wstartedMpAcquire (a : PAddr) (P : VProp GF) [Persistent P] (σr σf : Wmstate)
    (ws' : Wstate) (rak : AkInfo) (j t : Nat) (b : BitVec 8) :
    wstartedImgClear σr a →
    j < 4 →
    wbyteOk σr rak (WeakInterp.accAddr a j) t b →
    b ≠ nthByte (n := 4) lockZero 0 →
    t ≤ σf.wmWs.wVrOld →
    wVFence .Barrier_RISCV_r_rw σf ws' →
    wlogLb (GF := GF) σr.wmLog ⊢
      wlatInterp (GF := GF) σr.wmImg σr.wmLog -∗
        wstartedBody a P -∗
          wlatInterp (GF := GF) σr.wmImg σr.wmLog ∗ wstartedBody a P ∗
            ⌜b = nthByte (n := 4) lockOne j⌝ ∗ vwpHold P ws' :=
  fun himg hj hok hne hgain hF =>
    wstartedReader a P σr σf ws' rak j t b .Barrier_RISCV_r_rw himg hj hok hne hgain
      acqPredR_r_rw hF

end mp

/-! ## 3. WHY THE FENCE IS THERE

Both directions, at the machine's own step functions and on the SAME load: a plain load of the
flag at the deposited timestamp `T`, by a hart with an empty forward bank and an empty index.
(a) WITHOUT the fence the payload does not arrive: the load raises `wVrOld` and the coherence floor
at the flag's byte, nothing else; the deposit `viewScl T` is a floor at EVERY address, so an
untouched address is still at 0 -- the MP litmus test's non-SC outcome.  (b) WITH `fence r,rw` it
does, because a pred-R fence lifts `wVrOld` into the scalar component of the index. -/

theorem mpLoadAloneDoesNotDeliver (T : Nat) (a : Int) :
    0 < T → ¬ (viewScl T ≤ wsView (loadPost wsInit false a T)) := by
  intro hT hle
  have h := (View.le_spec _ _).1 hle (a + 1)
  rw [flr_scl_eq, flr_wsView] at h
  have hc : coh (loadPost wsInit false a T) (a + 1) = 0 := by
    show (get? (insert wsInit.wCoh a _) (a + 1)).getD 0 = 0
    rw [lookupInsertNe (by omega)]
    rfl
  have hn : (loadPost wsInit false a T).wVrNew = 0 := rfl
  rw [hc, hn] at h
  omega

theorem mpFenceDelivers (T : Nat) (a : Int) :
    viewScl T ≤ wsView (barrierPost (loadPost wsInit false a T) .Barrier_RISCV_r_rw) :=
  viewScl_acqPredR _ _ _ acqPredR_r_rw (loadPostVrOldNofwd wsInit false a T rfl)

section payload

variable {GF : BundledGFunctors}

/-- ... and the same contrast one level up, on the payload itself: what the fence turns into an
index gain is exactly what makes `vwpHold P` hold. -/
theorem mpPayloadArrives (P : VProp GF) (ws_r : Wstate) (T : Nat) :
    T ≤ ws_r.wVrOld →
    P.monPred_at (viewScl T) ⊢ vwpHold P (barrierPost ws_r .Barrier_RISCV_r_rw) := by
  intro hT
  unfold vwpHold
  exact P.monPred_mono (viewScl_acqPredR _ _ _ acqPredR_r_rw hT)

end payload

/-! ## 4. THE PAYOFF: the secondary hart's next load reads hart 0's value

The smallest instance of the payload -- one byte hart 0 wrote and then persisted (the shape of
every conjunct of xv6's own `main_deposit`).  After the acquire fence hart k holds it AT ITS OWN
INDEX, and `WeakVProp.wpt_load_rule` collapses its next plain load: every admissible timestamp for
that byte carries hart 0's value.  No staleness is reachable. -/

section mpByte

variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [WeakGS GF]

theorem wstartedMpByte (a : PAddr) (d : Int) (v : BitVec 8) (σr σf σn : Wmstate)
    (rak akn : AkInfo) (j t t' : Nat) (b bn : BitVec 8) :
    -- hart k's racy flag load, non-clear, and its acquire fence
    wstartedImgClear σr a →
    j < 4 →
    wbyteOk σr rak (WeakInterp.accAddr a j) t b →
    b ≠ nthByte (n := 4) lockZero 0 →
    t ≤ σf.wmWs.wVrOld →
    wVFence .Barrier_RISCV_r_rw σf σn.wmWs →
    -- and then a PLAIN load of `d` at some state with the same log, returning byte `bn`
    akn.akIfetch = false →
    σn.wmImg = σr.wmImg →
    σn.wmLog = σr.wmLog →
    wbyteOk σn akn d t' bn →
    wlogLb (GF := GF) σr.wmLog ⊢
      wlatInterp (GF := GF) σr.wmImg σr.wmLog -∗
        wstartedBody a (d ↦w□ v) -∗
          wlatInterp (GF := GF) σn.wmImg σn.wmLog ∗ wstartedBody a (d ↦w□ v) ∗ ⌜bn = v⌝ := by
  intro himg hj hok hne hgain hF hcoh hi' hl' hokn
  iintro #Hlb Hi Hbody
  icases wstartedMpAcquire a (d ↦w□ v) σr σf σn.wmWs rak j t b himg hj hok hne hgain hF
    $$ Hlb Hi Hbody with ⟨Hi, Hbody, -, HPr⟩
  rw [← hi', ← hl']
  icases wpt_load_rule σn σn akn d DFrac.discard v t' bn hcoh hokn rfl rfl (Nat.le_refl _)
    $$ [Hi HPr] with ⟨%hv, Hi, -⟩
  · isplitl [Hi]
    · iexact Hi
    · iexact HPr
  isplitl [Hi]
  · iexact Hi
  isplitl [Hbody]
  · iexact Hbody
  · ipureintro; exact hv

end mpByte

end Weak
