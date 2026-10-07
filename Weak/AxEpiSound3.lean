/-
Weak: **`epiReloadSound3`: the 2-hart epilogue theorem where hart 1 OWNS ITS OWN SLOT.**

Rocq: `iris/AxEpiSound3.v` @ xxvzwolszwmp.

## What this file proves

Generalises `epiReloadSound2`: hart 1 starts with the 8 full auths `histAuth γ (b+j) 1 []`
for its own slot `b..b+7`, allocated at the same `γ` as hart 0's 8 auths for `a..a+7`
(`epiHobAlloc3`, premise `slotsDisjoint a b`).  Hart 0's proof (`AxEpiAdeq.wpdEpiGa2`) is
reused unchanged.  §2: race2 meets every pure premise (with `b := ldAddr + 8`) and the
refutation `epiReloadSound3Race2NoWpd`.  §3: the sanity twin — hart 1's own-slot store IS
provable (`wpdHart1OwnSdHwp1`), the racing twin's is not.

## Deviations from Rocq

1. O2 STAGE C / types: hart 0's premises are exactly `epiReloadSound2`'s Lean forms (see
   AxEpiSound2 deviations 1–2): no `T`, no `Hnw_sd`/`Hnw_ld`/`Hntext`, positions
   `(0,0)`/`(0,1)`, length 2, conclusion at `(0,1)`.  §2's bundle keeps `¬ race2Text ldAddr`.
2. §3 sanity twin (Stage C, as `AxEpiOwned` deviation 1): hart 1's row is `[SD]`, so
   `wpdHart1OwnSd`/`wpdHart1OwnSdHwp1` take `fetchImgOk GD 1 0`, `storeRowOk GD 1 0`,
   `sdWriteOk GD 1 0 race2B` (Rocq `1 1`) and `length (grow GD 1) = 1` (Rocq 2); Rocq's `Hnw1`
   (the fetch is not a write) is DROPPED (no fetch flow).  The store exit `SdRetX` is at `k = 1`.
   `h1Regs` sets `x2` to `BitVec.ofInt 64 (race2B - 8)`; `dev0_state` ↦ `testDevs`; the ledger
   `h1LedgerCsdsp` uses `AxEpiProbe.drNopin` (as `epiLedgerCsdsp`, two-pin forms) and
   `decide +kernel` for `vm_compute`.  Rocq's section context `T` is gone (Stage C); the section
   lemma `wpdHart1OwnSd` is generic in `hlc` and the policy (Rocq: `HasNoLc`, `epi_pol`), the
   `Hwp1` corollary is at `.hasNoLC`/`epiPol`.

**Rocq → Lean name map.**  `epi_init3` `epiInit3`, `slots_disjoint` `slotsDisjoint`,
`epi_Hob_alloc3` `epiHobAlloc3`, `epi_reload_sound3` `epiReloadSound3`, `race2_b` `race2B`,
`epi_reload_sound3_race2_premises` `epiReloadSound3Race2Premises`,
`epi_reload_sound3_race2_no_wpd` `epiReloadSound3Race2NoWpd`, `h1_regs` `h1Regs`, `h1_t` `h1T`,
`h1_ledger_csdsp` `h1LedgerCsdsp`, `h1_state` `h1State`, `h1_race_state` `h1RaceState`,
`wpd_hart1_own_sd` `wpdHart1OwnSd`, `wpd_hart1_own_sd_Hwp1` `wpdHart1OwnSdHwp1`,
`epi_reload_sound3_race2_racing_twin_no_wpd` `epiReloadSound3Race2RacingTwinNoWpd`.
Lean-only (file-qualified): `AxEpiSound3.epiInit3Zero`, `AxEpiSound3.epiInit3One`.

**Dropped:** none.  **Not ported:** the `Print Assumptions` lines.
-/
import Weak.AxEpiSound2

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std Iris.Std.PartialMap MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D

/-! # 1. THE 2-HART THEOREM, HART 1 OWNING SLOT `b` -/

/-- Hart `i`'s initial resource: hart 0 gets the auths of slot `a`, hart 1 those of slot `b`,
every other hart nothing. -/
def epiInit3 {GF : BundledGFunctors} [AxlogG GF Hent] (a b : Int) (γ : GName) (i : Agent) :
    IProp GF :=
  if i = 0 then iprop([∗list] j ↦ H ∈ epiHs0, histAuth γ (a + (j : Int)) 1 H)
  else if i = 1 then iprop([∗list] j ↦ H ∈ epiHs0, histAuth γ (b + (j : Int)) 1 H)
  else iprop(emp)

/-- Disjointness of the two 8-byte slots. -/
def slotsDisjoint (a b : Int) : Prop := a + 8 ≤ b ∨ b + 8 ≤ a

/-- (Lean-only) hart 0's initial resources. -/
theorem AxEpiSound3.epiInit3Zero {GF : BundledGFunctors} [AxlogG GF Hent] (a b : Int)
    (γ : GName) :
    epiInit3 (GF := GF) a b γ 0 ⊣⊢
      iprop([∗list] j ↦ H ∈ epiHs0, histAuth γ (a + (j : Int)) 1 H) :=
  .rfl

/-- (Lean-only) hart 1's initial resources. -/
theorem AxEpiSound3.epiInit3One {GF : BundledGFunctors} [AxlogG GF Hent] (a b : Int)
    (γ : GName) :
    epiInit3 (GF := GF) a b γ 1 ⊣⊢
      iprop([∗list] j ↦ H ∈ epiHs0, histAuth γ (b + (j : Int)) 1 H) := by
  unfold epiInit3
  rw [if_neg (by decide), if_pos rfl]
  exact .rfl

/-- `HobAlloc`: ONE fresh `γ` with 16 empty histories, `a..a+7` to hart 0 and `b..b+7` to
hart 1. -/
theorem epiHobAlloc3 {GF : BundledGFunctors} [AxlogG GF Hent] (a b : Int)
    (Hdisj : slotsDisjoint a b) (GD : Gdexec) :
    ⊢@{IProp GF} |==> ∃ (nm : GName) (σ0 : Unit),
      epiObInterp nm GD σ0 ∅ ∗ [∗list] i ∈ [0, 1], epiInit3 a b nm i := by
  have Hinj : ∀ c : Int, Function.Injective (fun j : Nat => c + (j : Int)) := by
    intro c x y h
    simp only at h
    omega
  have Hnd8 : ∀ c : Int,
      (([0, 1, 2, 3, 4, 5, 6, 7] : List Nat).map (fun j : Nat => c + (j : Int))).Nodup :=
    fun c => List.Pairwise.map (R := fun x y : Nat => x ≠ y) _
      (fun _ _ h hxy => h (Hinj c hxy)) (by decide)
  have Hnd : ((([0, 1, 2, 3, 4, 5, 6, 7] : List Nat).map (fun j : Nat => a + (j : Int))) ++
      (([0, 1, 2, 3, 4, 5, 6, 7] : List Nat).map (fun j : Nat => b + (j : Int)))).Nodup := by
    refine List.pairwise_append.2 ⟨Hnd8 a, Hnd8 b, ?_⟩
    intro x hx y hy
    simp only [List.mem_map, List.mem_cons, List.not_mem_nil, _root_.or_false] at hx hy
    obtain ⟨j, hj, rfl⟩ := hx
    obtain ⟨k, hk, rfl⟩ := hy
    unfold slotsDisjoint at Hdisj
    omega
  have Hconv : ∀ γ : GName, iprop([∗set] x ∈ (LawfulSet.ofList
        ((([0, 1, 2, 3, 4, 5, 6, 7] : List Nat).map (fun j : Nat => a + (j : Int))) ++
          (([0, 1, 2, 3, 4, 5, 6, 7] : List Nat).map (fun j : Nat => b + (j : Int)))) :
          GSet Int),
        histAuth (GF := GF) γ x 1 ([] : List Hent)) ⊢
      iprop(([∗list] j ↦ H ∈ epiHs0, histAuth (GF := GF) γ (a + (j : Int)) 1 H) ∗
        ([∗list] j ↦ H ∈ epiHs0, histAuth (GF := GF) γ (b + (j : Int)) 1 H)) := by
    intro γ
    refine (BigSepS.bigSepS_of_list Hnd).1.trans ?_
    refine BigSepL.bigSepL_append.1.trans ?_
    rw [BigSepL.bigSepL_map, BigSepL.bigSepL_map]
    exact .rfl
  ihave Halloc := histAlloc (GF := GF) (LawfulSet.ofList
    ((([0, 1, 2, 3, 4, 5, 6, 7] : List Nat).map (fun j : Nat => a + (j : Int))) ++
      (([0, 1, 2, 3, 4, 5, 6, 7] : List Nat).map (fun j : Nat => b + (j : Int)))) : GSet Int)
    ([] : List Hent)
  imod Halloc with ⟨%γ, H⟩
  ihave H := Hconv γ $$ H
  icases H with ⟨Ha, Hb⟩
  imodintro
  iexists γ, ()
  isplitr [Ha Hb]
  · unfold epiObInterp protInv
    iapply BigSepS.bigSepS_empty.2
    iempintro
  · iapply BigSepL.bigSepL_cons.2
    isplitl [Ha]
    · iapply (AxEpiSound3.epiInit3Zero a b γ).2
      iexact Ha
    iapply BigSepL.bigSepL_singleton.2
    iapply (AxEpiSound3.epiInit3One a b γ).2
    iexact Hb

/-- Hart 1 runs an arbitrary program whose WPd at the protocol instance is proved from ITS OWN
slot-`b` auths; the reload still reads the spill. -/
theorem epiReloadSound3 (GD : Gdexec) (cpu : CPU) (a b : Int)
    (Hdisj : slotsDisjoint a b)
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
    -- hart 1: an ARBITRARY program, its run, and its WPd from ITS OWN auths
    (s0_1 sN1 : Athread) (n1 : Nat)
    (Hk1 : s0_1.atK = 0)
    (Hrun1 : ∀ (_ : AxannotGS epiGF) (nm : GName), nsteps (tierAAstep GD nm 1) n1 s0_1 sN1)
    (Hend1 : sN1.atK = (AxOpsem.grow GD 1).length)
    (Hwp1 : ∀ [InvGS_gen .hasNoLC epiGF] [AxannotGS epiGF] (nm : GName),
      ⊢ epiInit3 a b nm 1 -∗
        @tierAWpd epiGF .hasNoLC _ _ epiPol GD GName Unit epiObInterp nm s0_1 .MaybeStuck 1
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
      ⊢ ([∗list] i ∈ [0, 1], epiInit3 a b nm i) -∗
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
    have HB : ⊢ epiInit3 a b nm 1 -∗
        @tierAWpd epiGF .hasNoLC _ _ epiPol GD GName Unit epiObInterp nm (s0 1)
        .MaybeStuck 1 (fun s => iprop(⌜epiPost2 GD 1 s⌝)) := by
      have h := Hwp1 nm
      unfold tierAWpd at h
      unfold tierAWpd
      exact h.trans (wand_mono .rfl (@wpdMono .hasNoLC epiGF _
        (axGA2 GD GName Unit epiObInterp nm) epiPol _ _ _
        _ _ (fun _ => pure_intro (fun h => absurd h (by decide)))))
    iintro Hi
    ihave Hi := BigSepL.bigSepL_cons.1 $$ Hi
    icases Hi with ⟨Hi0, Hi1⟩
    ihave Hi1 := BigSepL.bigSepL_singleton.1 $$ Hi1
    ihave Hi0 := (AxEpiSound3.epiInit3Zero a b nm).1 $$ Hi0
    iapply BigSepL.bigSepL_cons.2
    isplitl [Hi0]
    · iapply HA $$ Hi0
    iapply BigSepL.bigSepL_singleton.2
    iapply HB $$ Hi1
  have Hfin := @tierAAdequacyAnnGmo epiGF _ _ epiPol GD GName Unit epiObInterp (epiInit3 a b)
    epiAxpolWf Hcons [0, 1] (by decide) Hharts' s0 sNf nf HrunA Hk0 HendA
    (epiPost2 GD) Hwp (epiHobAlloc3 a b Hdisj GD) Hs_pol Hlobp 0 (by simp)
  exact Hfin rfl (by show sN.atK = 2; rw [Hend, Hlen])

/-! # 2. THE RACE WITNESS SATISFIES EVERY PURE PREMISE (for `b := ldAddr + 8`) -/

def race2B : Int := ldAddr + 8

theorem epiReloadSound3Race2Premises :
    slotsDisjoint ldAddr race2B ∧
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
  refine ⟨?_, epiReloadSound2Race2Premises⟩
  unfold slotsDisjoint race2B
  omega

/-- The contrapositive at race2: whatever hart 1's program, whenever both harts' runs reach
their row ends, hart 1's WPd from ITS OWN slot-`b` auths is NOT provable (hart 1's store in
race2 hits `a = ldAddr`). -/
theorem epiReloadSound3Race2NoWpd (cpu : CPU)
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
      ⊢ epiInit3 ldAddr race2B nm 1 -∗
        @tierAWpd epiGF .hasNoLC _ _ epiPol race2 GName Unit epiObInterp nm s0_1 .MaybeStuck 1
          (fun _ => iprop(True))) := by
  intro Hwp1
  obtain ⟨H0, H1, H2, H3, H4, H5, H6, -, H8, H9, H10, H11, Hne⟩ := epiReloadSound3Race2Premises
  exact Hne (epiReloadSound3 race2 cpu ldAddr race2B H0 H1 H2 H3 H4 H5 H6 H8 H9 H10 H11 sN n
    Hrun Hend s0_1 sN1 n1 Hk1 Hrun1 Hend1 Hwp1)

/-! # 3. SANITY TWIN: hart 1 CAN write ITS OWN slot

Hart 1 runs the concrete `c.sdsp ra,8(sp)` (the 4-byte fetch `sdVs` at `pcSd`, exactly hart 0's
first instruction) with `sp := race2B - 8`, so the store hits hart 1's OWN slot
`race2B = ldAddr + 8`.  Its WPd at the same protocol instance (`epiGa2`, `protInv γ`) IS provable
from `epiInit3 _ race2B nm 1`, through the real owned-write flow `storeFlowOwned`.  After the
store the thread sits at `k = 1 = length (grow GD 1)` (Stage C: the row is `[SD]`), closed by
`wpdPastRowEnd`.  So the refutation of §2 is due to OWNERSHIP (the racing twin, identical but
with `sp = spVal`, writes bytes hart 1 has no auth for), not to a calculus in which no write is
ever provable. -/

/-- Hart 1's registers: hart 0's `probeRegs pcSd` with `sp` overridden. -/
def h1Regs : RegFile := (probeRegs pcSd).set .x2 (BitVec.ofInt 64 (race2B - 8))

def h1T : ExecSt := ⟨h1Regs, probeMem, testDevs⟩

/-- The store ledger of the sanity twin: c.sdsp at `pcSd` stores `sdData` (the value of `ra`)
at `race2B`. -/
theorem h1LedgerCsdsp :
    AxSdModelFacts h1T AxEpiProbe.drNopin DwAll DPost (pcSd : Int) sdVs race2B sdData
      sdPost where
  lsSeipDr := by decide +kernel
  lsMeipDr := by decide +kernel
  lsSeipD := by decide +kernel
  lsMeipD := by decide +kernel
  lsHead := by decide +kernel
  lsToSeip := by decide +kernel
  lsBranch00 := by decide +kernel
  lsBranch01 := by decide +kernel
  lsBranch10 := by decide +kernel
  lsBranch11 := by decide +kernel

noncomputable def h1State (cpu : CPU) (ib : Ibch) : Athread :=
  ⟨.PHart cpu (riscvStep false) h1Regs none ib, 0⟩

/-- The racing twin: identical, but `sp = spVal`, so the store hits `sdAddr = ldAddr` (hart 0's
slot `a`). -/
noncomputable def h1RaceState (cpu : CPU) (ib : Ibch) : Athread :=
  ⟨.PHart cpu (riscvStep false) (probeRegs pcSd) none ib, 0⟩

section h1
variable {hlc : HasLC} {GF : BundledGFunctors.{0,0,0}} [InvGS_gen hlc GF] [AxannotGS GF]
  [AxlogG GF Hent] [pol : Axpol]

theorem wpdHart1OwnSd (GD0 : Gdexec) (γ : GName) (cpu : CPU) (ib : Ibch)
    (Hgd1 : AxCjrWpd.fetchImgOk GD0 1 0 pcSd sdVs)
    (Hrow1 : storeRowOk GD0 1 0)
    (Hw1 : sdWriteOk GD0 1 0 race2B)
    (Hlen1 : (AxOpsem.grow GD0 1).length = 1) :
    ⊢ ([∗list] j ↦ H ∈ epiHs0, histAuth (GF := GF) γ (race2B + (j : Int)) 1 H) -∗
      @wpd hlc GF _ (epiGa2 GD0 γ) pol .MaybeStuck 1 (h1State cpu ib)
        (fun _ => iprop(True)) := by
  have HF := @storeFlowOwned hlc GF _ (epiGa2 GD0 γ) pol _ _ γ (obEqGa2 GD0 γ) (annEqGa2 GD0 γ)
    1 0 race2B epiHs0 rfl (pinGa2 GD0 γ (fun GD => sdWriteOk GD 1 0 race2B) Hw1)
    (fun GD ls _ => locGa2 GD0 γ GD 1 0 ls)
  have HE : ∀ s0, SdRetX h1T AxEpiProbe.drNopin DwAll DPost sdVs cpu (0 + 1) s0 →
      s0.atK = 1 := by
    rintro s0 ⟨v', v, t3, -, ib', Hk, -⟩
    exact Hk
  have Hle : ∀ GD, rvwmoCatConsistent GD →
      AxirisG.gconstInterp (self := epiGa2 (GF := GF) GD0 γ) GD ⊢
        ⌜(AxOpsem.grow GD 1).length ≤ 1⌝ :=
    pinGa2 GD0 γ (fun GD => (AxOpsem.grow GD 1).length ≤ 1) (Nat.le_of_eq Hlen1)
  show ⊢ _ -∗ @wpd hlc GF _ (epiGa2 GD0 γ) pol .MaybeStuck 1
    ⟨.PHart cpu (riscvStep false) h1T.regs none ib, 0⟩ (fun _ => iprop(True))
  iintro Hauths
  ihave F := HF $$ Hauths
  iapply (@wpdCsdspStepExactRes hlc GF _ (epiGa2 GD0 γ) pol 1 (fun _ => iprop(True)) cpu ib 0
    h1T _ _ _ _ _ _ _ _ _ h1LedgerCsdsp
    (pinGa2 GD0 γ (fun GD => AxCjrWpd.fetchImgOk GD 1 0 (pcSd : Int) sdVs) Hgd1)
    (pinGa2 GD0 γ (fun GD => storeRowOk GD 1 0) Hrow1)) $$ F
  isplit
  · iintro _ %s' %Hs'
    iapply (@wpdPastRowEnd hlc GF _ (epiGa2 GD0 γ) pol 1 (fun _ => iprop(True))
      (SdRetX h1T AxEpiProbe.drNopin DwAll DPost sdVs cpu (0 + 1)) 1 s' Hs' HE Hle)
    iintro %GD %s1 %_ %_
    iapply (@postLiftingTrue GF (epiGa2 GD0 γ) pol (fun _ => iprop(True)) 1 s1 .rfl)
  · iintro %GD %s1 %_ %_
    iapply (@postLiftingTrue GF (epiGa2 GD0 γ) pol (fun _ => iprop(True)) 1 s1 .rfl)

end h1

/-- The sanity twin in exactly the shape of `epiReloadSound3`'s `Hwp1`. -/
theorem wpdHart1OwnSdHwp1 (GD : Gdexec) (a : Int) (cpu : CPU) (ib : Ibch)
    (Hgd1 : AxCjrWpd.fetchImgOk GD 1 0 pcSd sdVs)
    (Hrow1 : storeRowOk GD 1 0)
    (Hw1 : sdWriteOk GD 1 0 race2B)
    (Hlen1 : (AxOpsem.grow GD 1).length = 1) :
    ∀ [InvGS_gen .hasNoLC epiGF] [AxannotGS epiGF] (nm : GName),
      ⊢ epiInit3 a race2B nm 1 -∗
        @tierAWpd epiGF .hasNoLC _ _ epiPol GD GName Unit epiObInterp nm (h1State cpu ib)
          .MaybeStuck 1 (fun _ => iprop(True)) := by
  intro _ _ nm
  unfold tierAWpd
  iintro H
  ihave H := (AxEpiSound3.epiInit3One a race2B nm).1 $$ H
  iapply (@wpdHart1OwnSd .hasNoLC epiGF _ _ _ epiPol GD nm cpu ib Hgd1 Hrow1 Hw1 Hlen1) $$ H

/-- The racing twin at race2: its WPd from hart 1's own (`race2B`) auths is NOT provable, given
hart 0's run and hart 1's run `Hrun1` (left as a hypothesis).  An instance of
`epiReloadSound3Race2NoWpd`. -/
theorem epiReloadSound3Race2RacingTwinNoWpd (cpu : CPU)
    (sN : Athread) (n : Nat)
    (Hrun : ∀ (_ : AxannotGS epiGF) (nm : GName),
      nsteps (tierAAstep race2 nm 0) n
        ⟨.PHart cpu (riscvStep false) (probeRegs pcSd) none ibNone, 0⟩ sN)
    (Hend : sN.atK = (AxOpsem.grow race2 0).length)
    (sN1 : Athread) (n1 : Nat)
    (Hrun1 : ∀ (_ : AxannotGS epiGF) (nm : GName),
      nsteps (tierAAstep race2 nm 1) n1 (h1RaceState cpu ibNone) sN1)
    (Hend1 : sN1.atK = (AxOpsem.grow race2 1).length) :
    ¬ (∀ [InvGS_gen .hasNoLC epiGF] [AxannotGS epiGF] (nm : GName),
      ⊢ epiInit3 ldAddr race2B nm 1 -∗
        @tierAWpd epiGF .hasNoLC _ _ epiPol race2 GName Unit epiObInterp nm
          (h1RaceState cpu ibNone) .MaybeStuck 1 (fun _ => iprop(True))) :=
  epiReloadSound3Race2NoWpd cpu sN n Hrun Hend (h1RaceState cpu ibNone) sN1 n1 rfl Hrun1 Hend1

end Weak
