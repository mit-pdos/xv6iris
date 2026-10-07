/-
Weak: **`epiReloadSound2`: the 2-hart epilogue theorem, where OWNERSHIP IS LOAD-BEARING.**

Rocq: `iris/AxEpiSound2.v` @ xxvzwolszwmp.

## What this file proves

Harts `[0, 1]`.  Hart 0 runs the concrete `c.sdsp ; c.ldsp` program of
`AxEpiAdeq.epiReloadSound`, with the same pure premises and the same run.  Hart 1 runs an
ARBITRARY program `s0_1`; its only premise is its WPd at the SAME protocol instance (`axGA2`,
`obStInterp := protInv γ`), proved from NO resources (`epiInit a nm 1 = emp`).  Hart 1 gets no
`histAuth` and no token for the slot bytes.  Conclusion: the reload reads the spill,
`graphValue GD (0, 1) = some sdData` (Lean positions).

The Rocq header's STEP-0 AUDIT (why hart 1 cannot write the slot without the token: a write
step must be discharged by `wpEvStep`'s `flowEqDyn`, which at `axGA2` needs a `histSnap` whose
last entry is the write — obtainable only from the full `histAuth`, which hart 0 holds until the
spill deposits it in the spill's annotation and only the reload detaches it; and the reload's
coverage step quantifies over ALL gmo-earlier writers, whatever the hart) carries over to the
Lean model unchanged.  VERDICT (Rocq): `Hwp1` is unprovable for the race witness
`AxEpiRace2.race2`, where hart 1 writes the slot — §2 states this:
`epiReloadSound2Race2Premises` (every pure premise holds at race2, the conclusion fails) and
`epiReloadSound2Race2NoWpd` (so hart 1's WPd from no resources is not provable there).

SPEC CONCERN (Rocq, still applies): at this instance hart 1 cannot write ANY byte (`γ` holds a
key only for the 8 slot bytes and hart 1 gets no auth), so `Hwp1` effectively says "hart 1
performs no writes at all" — ownership against a write-free environment, not a slot-disjoint
one.

Hart 0's proof (`AxEpiAdeq.wpdEpiGa2`) is reused UNCHANGED; no new pure premise mentions hart 1.

## Deviations from Rocq

1. O2 STAGE C (fetches are not graph events; `AxEpiAdeq` deviation 1, `AxEpiRace2`
   deviation 1): hart 0's premises are `epiReloadSound`'s Lean forms —
   `fetch_gd_ok GD 0 0 pc_sd sd_vs` ↦ `AxCjrWpd.fetchImgOk GD 0 0 pcSd sdVs`,
   `store_row_ok GD 0 1` ↦ `storeRowOk GD 0 0`, `sd_write_ok GD 0 1 a` ↦ `sdWriteOk GD 0 0 a`,
   `fetch_gd_ok GD 0 2 pc_ld ld_vs` ↦ `AxCjrWpd.fetchImgOk GD 0 1 pcLd AxEpiLedger.ldVs`,
   `load_row_ok GD 0 3` ↦ `loadRowOk GD 0 1`, `ldsp_own_ok GD 0 3 (0,1) a (writen_hist (0,1) …)`
   ↦ `ldspOwnOk GD 0 1 (0,0) a (writenHist (0,0) …)`, length `4` ↦ `2`,
   `gmo_lt (0,1) (0,3)` ↦ `gmoLt (0,0) (0,1)`; the conclusion is at `(0,1)` (Rocq `(0,3)`).
   DROPPED premises: `Hnw_sd`, `Hnw_ld` (`gis_w` of the fetch events) and `Hntext`
   (`¬ T ld_addr`), as in `epiReloadSound`; the text parameter `T` is gone (`tierAAstep`/
   `tierAWpd` take none, AxTierA2 deviation 2).  §2's premise bundle accordingly drops the two
   `gis_w` conjuncts but KEEPS `¬ race2Text ldAddr` (as `AxEpiRace2.race2Sat`), and
   `epiReloadSound2Race2NoWpd` is stated over `race2` without the text argument.
2. TYPES/CONTEXTS (as `AxEpiAdeq` deviations 4–7): `invGS_gen HasNoLc epiΣ` ↦
   `[InvGS_gen .hasNoLC epiGF]`, `axannotGS epiΣ` ↦ `AxannotGS epiGF`; `Hrun`/`Hrun1` are
   `∀ (_ : AxannotGS epiGF) (nm : GName), nsteps (tierAAstep GD nm i) …`; `Hwp1` is
   `∀ [InvGS_gen .hasNoLC epiGF] [AxannotGS epiGF] (nm : GName), ⊢ @tierAWpd … epiPol …`
   (the policy passed explicitly; Rocq's `Local Existing Instance EpiSat.epi_pol` is not
   replicated); `epiHobAlloc2` is generic in `GF` with `[AxlogG GF Hent]`, like
   `epiHobAlloc`.

**Rocq → Lean name map.**  `epi_post2` `epiPost2`, `epi_Hob_alloc2` `epiHobAlloc2`,
`epi_reload_sound2` `epiReloadSound2`, `epi_reload_sound2_race2_premises`
`epiReloadSound2Race2Premises`, `epi_reload_sound2_race2_no_wpd` `epiReloadSound2Race2NoWpd`.
None is in the duplicated-name table.  Lean-only (file-qualified): `AxEpiSound2.epiInit1`.

**Dropped:** nothing (Rocq 5 definitions/lemmas; Lean 5 + 1 Lean-only helper).  **Not ported:**
the `Print Assumptions` lines (the lint's axiom check covers them).
-/
import Weak.AxEpiAdeq
import Weak.AxEpiRace2

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std Iris.Std.PartialMap MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D

/-! # 1. THE 2-HART THEOREM -/

/-- The per-hart post: hart 0's is `epiPost`, hart 1's is trivial. -/
def epiPost2 (GD : Gdexec) (i : Agent) (s : Athread) : Prop :=
  i = 0 → epiPost GD i s

/-- (Lean-only) hart 1's initial resources are `emp`. -/
theorem AxEpiSound2.epiInit1 {GF : BundledGFunctors} [AxlogG GF Hent] (a : Int) (γ : GName) :
    epiInit (GF := GF) a γ 1 ⊣⊢ iprop(emp) := by
  unfold epiInit
  rw [if_neg (by decide)]
  exact .rfl

/-- `HobAlloc` for harts `[0, 1]`: the allocation of `epiHobAlloc` (fresh `γ`, 8 empty slot
histories, all to hart 0); hart 1's `init` is `emp`. -/
theorem epiHobAlloc2 {GF : BundledGFunctors} [AxlogG GF Hent] (a : Int) (GD : Gdexec) :
    ⊢@{IProp GF} |==> ∃ (nm : GName) (σ0 : Unit),
      epiObInterp nm GD σ0 ∅ ∗ [∗list] i ∈ [0, 1], epiInit a nm i := by
  ihave Halloc := epiHobAlloc (GF := GF) a GD
  imod Halloc with ⟨%nm, %σ0, Hob, Hi⟩
  imodintro
  iexists nm, σ0
  isplitl [Hob]
  · iexact Hob
  ihave Hi := BigSepL.bigSepL_singleton.1 $$ Hi
  iapply BigSepL.bigSepL_cons.2
  isplitl [Hi]
  · iexact Hi
  iapply BigSepL.bigSepL_singleton.2
  iapply (AxEpiSound2.epiInit1 (GF := GF) a nm).2
  iempintro

/-- OWNERSHIP IS LOAD-BEARING: hart 1 runs an arbitrary program whose WPd at the protocol
instance is proved from no resources; the reload still reads the spill. -/
theorem epiReloadSound2 (GD : Gdexec) (cpu : CPU) (a : Int)
    (Hcons : rvwmoCatConsistent GD)
    (Hharts : ∀ e, e ∈ GD.gdG.gxGmo → e.1 = 0 ∨ e.1 = 1)
    -- hart 0's row: exactly `epiReloadSound`'s pure premises
    (Hgd_sd : AxCjrWpd.fetchImgOk GD 0 0 pcSd sdVs)
    (Hrow_sd : storeRowOk GD 0 0)
    (Hw_sd : sdWriteOk GD 0 0 a)
    (Hgd_ld : AxCjrWpd.fetchImgOk GD 0 1 pcLd AxEpiLedger.ldVs)
    (Hrow_ld : loadRowOk GD 0 1)
    (Hok_ld : @ldspOwnOk epiPol GD 0 1 (0, 0) a (writenHist (0, 0) sdData epiHs0))
    (Hlen : (AxOpsem.grow GD 0).length = 2)
    (Hlob_gmo : gmoLt GD.gdG (0, 0) (0, 1))
    -- hart 0's run
    (sN : Athread) (n : Nat)
    (Hrun : ∀ (_ : AxannotGS epiGF) (nm : GName),
      nsteps (tierAAstep GD nm 0) n
        ⟨.PHart cpu (riscvStep false) (probeRegs pcSd) none ibNone, 0⟩ sN)
    (Hend : sN.atK = (AxOpsem.grow GD 0).length)
    -- hart 1: an ARBITRARY program, its run, and its WPd from NO resources
    (s0_1 sN1 : Athread) (n1 : Nat)
    (Hk1 : s0_1.atK = 0)
    (Hrun1 : ∀ (_ : AxannotGS epiGF) (nm : GName), nsteps (tierAAstep GD nm 1) n1 s0_1 sN1)
    (Hend1 : sN1.atK = (AxOpsem.grow GD 1).length)
    (Hwp1 : ∀ [InvGS_gen .hasNoLC epiGF] [AxannotGS epiGF] (nm : GName),
      ⊢ @tierAWpd epiGF .hasNoLC _ _ epiPol GD GName Unit epiObInterp nm s0_1 .MaybeStuck 1
          (fun _ => iprop(True))) :
    graphValue GD (0, 1) = some sdData := by
  let s00 : Athread := ⟨.PHart cpu (riscvStep false) (probeRegs pcSd) none ibNone, 0⟩
  let s0 : Agent → Athread := fun i => if i = 0 then s00 else s0_1
  let sNf : Agent → Athread := fun i => if i = 0 then sN else sN1
  let nf : Agent → Nat := fun i => if i = 0 then n else n1
  have Hin01 : ∀ i : Agent, i ∈ [0, 1] → i = 0 ∨ i = 1 := by
    intro i Hi
    simp only [List.mem_cons, List.not_mem_nil, _root_.or_false] at Hi
    exact Hi
  have Hharts' : ∀ e, e ∈ GD.gdG.gxGmo → e.1 ∈ [0, 1] := by
    intro e He
    rcases Hharts e He with h | h <;> rw [h] <;> simp
  have Hs_pol : ∀ e e', e' ∈ Axpol.sPol (self := epiPol) GD e → gmoLt GD.gdG e' e :=
    fun e e' he' => gmoPrefixGmoLt _ Hcons.1 e e' (elemOfListToSet.1 he')
  have Hlobp : ∀ e e', e' ∈ Axpol.lobp (self := epiPol) GD e → gmoLt GD.gdG e' e := by
    intro e e' he'
    change e' ∈ epiLobp GD e at he'
    unfold epiLobp at he'
    split at he'
    · rename_i heq
      subst heq
      have h1 := elemOfSingleton.1 (elemOfIntersection.1 he').1
      subst h1
      exact Hlob_gmo
    · exact absurd he' notElemOfEmpty
  have HrunA : ∀ (Hann : AxannotGS epiGF) (nm : GName) i, i ∈ [0, 1] →
      nsteps (tierAAstep GD nm i) (nf i) (s0 i) (sNf i) := by
    intro Hann nm i Hi
    rcases Hin01 i Hi with rfl | rfl
    · exact Hrun Hann nm
    · exact Hrun1 Hann nm
  have Hk0 : ∀ i, i ∈ [0, 1] → (s0 i).atK = 0 := by
    intro i Hi
    rcases Hin01 i Hi with rfl | rfl
    · rfl
    · exact Hk1
  have HendA : ∀ i, i ∈ [0, 1] → (sNf i).atK = (AxOpsem.grow GD i).length := by
    intro i Hi
    rcases Hin01 i Hi with rfl | rfl
    · exact Hend
    · exact Hend1
  have Hwp : ∀ [InvGS_gen .hasNoLC epiGF] [AxannotGS epiGF] (nm : GName),
      ⊢ ([∗list] i ∈ [0, 1], epiInit a nm i) -∗
        [∗list] i ∈ [0, 1],
          @tierAWpd epiGF .hasNoLC _ _ epiPol GD GName Unit epiObInterp nm (s0 i) .MaybeStuck i
            (fun s => iprop(⌜epiPost2 GD i s⌝)) := by
    intro _ _ nm
    have HA : ⊢ ([∗list] j ↦ H ∈ epiHs0, histAuth (GF := epiGF) nm (a + (j : Int)) 1 H) -∗
        @tierAWpd epiGF .hasNoLC _ _ epiPol GD GName Unit epiObInterp nm (s0 0) .MaybeStuck 0
          (fun s => iprop(⌜epiPost2 GD 0 s⌝)) := by
      have h := wpdEpiGa2 (hlc := .hasNoLC) (GF := epiGF) (pol := epiPol) GD nm cpu ibNone a
        Hgd_sd Hrow_sd Hw_sd Hgd_ld Hrow_ld Hok_ld Hlen
      unfold tierAWpd
      refine h.trans (wand_mono .rfl ?_)
      exact @wpdMono .hasNoLC epiGF _ (axGA2 GD GName Unit epiObInterp nm) epiPol _ _ _ _ _
        (fun _ => pure_mono (fun hp _ => hp))
    have HB : ⊢ @tierAWpd epiGF .hasNoLC _ _ epiPol GD GName Unit epiObInterp nm (s0 1)
        .MaybeStuck 1 (fun s => iprop(⌜epiPost2 GD 1 s⌝)) := by
      have h := Hwp1 nm
      unfold tierAWpd at h
      unfold tierAWpd
      exact h.trans (@wpdMono .hasNoLC epiGF _ (axGA2 GD GName Unit epiObInterp nm) epiPol _ _ _
        _ _ (fun _ => pure_intro (fun h => absurd h (by decide))))
    iintro Hi
    ihave Hi := BigSepL.bigSepL_cons.1 $$ Hi
    icases Hi with ⟨Hi0, -⟩
    ihave Hi0 := (AxEpiAdeq.epiInit0 a nm).1 $$ Hi0
    iapply BigSepL.bigSepL_cons.2
    isplitl [Hi0]
    · iapply HA $$ Hi0
    iapply BigSepL.bigSepL_singleton.2
    iapply HB
  have Hfin := @tierAAdequacyAnnGmo epiGF _ _ epiPol GD GName Unit epiObInterp (epiInit a)
    epiAxpolWf Hcons [0, 1] (by decide) Hharts' s0 sNf nf HrunA Hk0 HendA
    (epiPost2 GD) Hwp (epiHobAlloc2 a GD) Hs_pol Hlobp 0 (by simp)
  exact Hfin rfl (by show sN.atK = 2; rw [Hend, Hlen])

/-! # 2. THE RACE WITNESS SATISFIES EVERY PURE PREMISE

At `race2` (`a := ldAddr`) every PURE premise of `epiReloadSound2` holds, yet the reload reads
`raceData ≠ sdData`.  So only the ownership premise `Hwp1` (with the run premises) can rule race2
out. -/

theorem epiReloadSound2Race2Premises :
    rvwmoCatConsistent race2 ∧
    (∀ e, e ∈ race2.gdG.gxGmo → e.1 = 0 ∨ e.1 = 1) ∧
    AxCjrWpd.fetchImgOk race2 0 0 pcSd sdVs ∧
    storeRowOk race2 0 0 ∧
    sdWriteOk race2 0 0 ldAddr ∧
    AxCjrWpd.fetchImgOk race2 0 1 pcLd AxEpiLedger.ldVs ∧
    ¬ race2Text ldAddr ∧
    loadRowOk race2 0 1 ∧
    @ldspOwnOk epiPol race2 0 1 (0, 0) ldAddr (writenHist (0, 0) sdData epiHs0) ∧
    (AxOpsem.grow race2 0).length = 2 ∧
    gmoLt race2.gdG (0, 0) (0, 1) ∧
    -- ... and the conclusion FAILS
    graphValue race2 (0, 1) ≠ some sdData := by
  obtain ⟨H1, H2, H3, H4, H5, H6, H7, H8, H9, H10, H11, -, -⟩ := race2Sat
  exact ⟨H1, H2, H3, H4, H5, H6, H7, H8, H9, H10, H11, race2NotSd⟩

/-- The contrapositive at race2: whatever hart 1's program, whenever both harts' runs reach
their row ends, hart 1's WPd from no resources is NOT provable.  Ownership is exactly what
excludes the race. -/
theorem epiReloadSound2Race2NoWpd (cpu : CPU)
    (sN : Athread) (n : Nat)
    (Hrun : ∀ (_ : AxannotGS epiGF) (nm : GName),
      nsteps (tierAAstep race2 nm 0) n
        ⟨.PHart cpu (riscvStep false) (probeRegs pcSd) none ibNone, 0⟩ sN)
    (Hend : sN.atK = (AxOpsem.grow race2 0).length)
    (s0_1 sN1 : Athread) (n1 : Nat)
    (Hk1 : s0_1.atK = 0)
    (Hrun1 : ∀ (_ : AxannotGS epiGF) (nm : GName), nsteps (tierAAstep race2 nm 1) n1 s0_1 sN1)
    (Hend1 : sN1.atK = (AxOpsem.grow race2 1).length) :
    ¬ (∀ [InvGS_gen .hasNoLC epiGF] [AxannotGS epiGF] (nm : GName),
      ⊢ @tierAWpd epiGF .hasNoLC _ _ epiPol race2 GName Unit epiObInterp nm s0_1 .MaybeStuck 1
          (fun _ => iprop(True))) := by
  intro Hwp1
  obtain ⟨H1, H2, H3, H4, H5, H6, -, H8, H9, H10, H11, Hne⟩ := epiReloadSound2Race2Premises
  exact Hne (epiReloadSound2 race2 cpu ldAddr H1 H2 H3 H4 H5 H6 H8 H9 H10 H11 sN n Hrun Hend
    s0_1 sN1 n1 Hk1 Hrun1 Hend1 Hwp1)

end Weak
