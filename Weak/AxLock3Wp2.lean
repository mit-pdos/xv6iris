/-
Weak: **A7-T2c continuation: the tie-carrying `x`-write flow equation and the register-only PLIC
wire** (AxSL tier).

Rocq: `iris/AxLock3Wp2.v` @ xxvzwolszwmp.

## The Rocq header, in substance

§1 GAP (1) — `lockXwriteFlowEq3ATie`.  `lockXwriteFlowEq3A`'s output is only
`⌜graphData GD w = some data⌝`; the release equation (`lockRelFlowEq3A`) needs its `flowIn` to
entail `xTok`/`tokTie GD nm.1 x Hh {[e_last := 1]}` for `e_last` = the SAME hart's own `x`-write.
This lemma is `lockXwriteFlowEq3A`'s script with `AxProt.protInvWriteStep` (the tie-producing
form) in place of `protInvWriteStepAuth`, so `R` carries the graph-data fact, the fresh tie at
`w` itself (history `Hl ++ [(w, v)]`), and `histXWf x GD (Hl ++ [(w, v)])` — derived here by
`histXWfSnoc` from the old history's well-formedness and the gmo link of `w` after `Hl`'s last
entry, both handed back by the `flowIn`-wand.

§2 GAP (3) — the PLIC wire is register-only (`l3pAwireRsOnly`): a wire step keeps the cpu, the
monad continuation, the parked fence, the instruction-bits field and the row position; only the
register file moves.  Every per-position step lemma of `AxLock3Prog` is register-generic, so the
per-hart `WPd` induction is stated `∀ rs` and the wire arm re-enters the Löb hypothesis at the
perturbed `rs'`.

§3 (Rocq closing note, prose only): the retry self-loop of the exclusive write
(`l3pWriteExclDet`) and the per-position assembly are left to AxLock3Writer/AxLock3Reader.

**Fetches.** Nothing here depends on instruction fetches (graph labels, ghosts, the wire).

## Deviations from Rocq

1. NAMES: camelCase (map below); no name of this file is in the duplicated-name table; no
   Lean-only helpers.
2. THE INSTANCE: Rocq's restated `Local Instance AxGA2_lock3'` (it could not edit
   `AxLock3Wp.v`) is NOT restated: Lean names the instance `axGA2Lock3 L x GD0 nm` (AxLock3Wp,
   reducible def) in statements, so `AxGA2_lock3'` ↦ `axGA2Lock3` and `lock3_ob_st_interp_A'`
   ↦ `AxLock3Wp.lock3ObStInterpA` (the same `.rfl` fact; not redeclared).
3. CONTEXTS (as AxLock3Wp deviation 3): `invGS_gen HasNoLc Σ` ↦ `[InvGS_gen hlc GF]` for any
   `hlc`; Rocq's `T` is gone (O2 Stage C).  Only the `x`-write lemma takes `hxy : x ≠ L`.
4. STATEMENT SHAPES (as AxLock3Wp deviation 4): `P -∗ flowEqDyn …` ↦ `P ⊢ flowEqDyn …`;
   `s_pol GD w` ↦ `lockPolS GD w`; `last Hl` ↦ `Hl.getLast?`; `gmo_lt (gd_g GD)` ↦
   `gmoLt GD.gdG`.
5. THE WIRE: `oib32` ↦ `Ibch`; Rocq's `pstep_wire`/`pstep_plic` inversion ↦
   `pstepWireInv` (AxOpsem) (which also exhibits the new register file as `pinSet rs mm b`; the
   statement keeps Rocq's `∃ rs'`).

**Rocq → Lean name map.**  `lock_xwrite_flow_eq3_A_tie` `lockXwriteFlowEq3ATie`,
`l3p_awire_rs_only` `l3pAwireRsOnly`, `AxGA2_lock3'` `axGA2Lock3` (existing),
`lock3_ob_st_interp_A'` `lock3ObStInterpA` (existing).

**Not ported:** the `Print Assumptions` audit (the lint's axiom check covers it).
-/
import Weak.AxLock3Wp
import Weak.AxLock3Prog

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std Iris.Std.PartialMap MachCSL MachCSL.Stdpp

section lock3Transport2

variable {GF : BundledGFunctors.{0,0,0}} [AxlogG GF Hent] [AxLockG GF] (L x : Int)
variable {hlc : HasLC} [InvGS_gen hlc GF] [AxannotGS GF] (GD0 : Gdexec) (nm : lock3N)

/-! ## 1. GAP (1): the `x`-write flow equation, carrying the tie -/

theorem lockXwriteFlowEq3ATie (hxy : x ≠ L) (GD : Gdexec) (w : Geid) (v : BitVec 8)
    (Hl : List Hent) (flowIn : Mea GF) (data : List (BitVec 8)) :
    gwritesByte GD.gdG w x v →
    (∀ a' v', gwritesByte GD.gdG w a' v' → a' = x) →
    graphData GD w = some data →
    iprop(([∗map] Rin ∈ flowIn, Rin) -∗
      histAuth nm.1 x 1 Hl ∗
      ⌜histXWf x GD Hl ∧
        ∀ wlast vlast, Hl.getLast? = some (wlast, vlast) → gmoLt GD.gdG wlast w⌝) ⊢
    @flowEqDyn hlc GF _ (axGA2Lock3 L x GD0 nm) GD w (lockPolS GD w) flowIn
      iprop(⌜graphData GD w = some data⌝ ∗ tokTie GD nm.1 x (Hl ++ [(w, v)]) {[w := (1 : Qp)]} ∗
        ⌜histXWf x GD (Hl ++ [(w, v)])⌝) := by
  intro hwb hsingle hgd
  unfold flowEqDyn
  iintro Hflowin %σ %sOb %Hsub %Hnin Hob Hflow
  obtain ⟨g, D, hm⟩ := σ
  icases ((lock3ObStInterpA L x GD0 nm GD g D hm sOb).trans
    (protInvLock3Unfold L x nm.1 nm.2 GD sOb D hm g)).1 $$ Hob with ⟨Hlock'', Hgen⟩
  icases (AxProtLock2.protInvLockUnfold'' L x nm.1 nm.2 GD sOb D hm).1 $$ Hlock''
    with ⟨Hlock', HHL, %Hclaims, %Hhmc⟩
  icases Hflowin $$ Hflow with ⟨Hauth, %Hpayload⟩
  obtain ⟨hxwf, hlink⟩ := Hpayload
  icases (protInvLockUnfold' L x nm.1 nm.2 GD sOb D hm).1 $$ Hlock' with ⟨Hc, Hpo, Hlocks⟩
  imod protInvWriteStep nm.1 GD sOb w x v Hl Hnin hwb hsingle $$ [$Hpo $Hauth]
    with ⟨Hpo', Htie⟩
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro Hclose
  inext
  imod Hclose
  imodintro
  iexists ((g, D, hm) : Bool × GSet Geid × GMapF Geid (List Hent))
  isplitl [Hc Hpo' Hlocks HHL Hgen]
  · iapply ((lock3ObStInterpA L x GD0 nm GD g D hm (({w} : GSet Geid) ∪ sOb)).trans
      (protInvLock3Unfold L x nm.1 nm.2 GD (({w} : GSet Geid) ∪ sOb) D hm g)).2
    isplitl [Hc Hpo' Hlocks HHL]
    · iapply (AxProtLock2.protInvLockUnfold'' L x nm.1 nm.2 GD (({w} : GSet Geid) ∪ sOb)
        D hm).2
      isplitl [Hc Hpo' Hlocks]
      · iapply (protInvLockUnfold' L x nm.1 nm.2 GD (({w} : GSet Geid) ∪ sOb) D hm).2
        isplitl [Hc]
        · iexact Hc
        isplitl [Hpo']
        · iexact Hpo'
        iapply (AxProtLock.bigSepSUnionSingleton
          (Φ := fun e => ΦLock' L x nm.1 nm.2 GD e ((get? hm e).getD [])) Hnin).2
        isplitl []
        · iapply AxProtLock.ΦLock'Vacuous L x nm.1 nm.2 GD w _
            (fun hbad => hxy (hsingle L _ hbad).symm)
        · iexact Hlocks
      · isplitl [HHL]
        · iexact HHL
        · isplitl []
          · ipureintro
            intro r hr
            obtain ⟨e, he, hre⟩ := Hclaims r hr
            exact ⟨e, elemOfUnionR he, hre⟩
          · ipureintro
            intro w' hw' hwb0'
            rcases elemOfUnion.1 hw' with hw' | hw'
            · rw [elemOfSingleton.1 hw'] at hwb0'
              exact (hxy (hsingle L _ hwb0').symm).elim
            · exact Hhmc w' hw' hwb0'
    · iapply lockGenesisMono L x nm.1 GD g sOb (({w} : GSet Geid) ∪ sOb)
        (fun _ h => elemOfUnionR h)
      iexact Hgen
  · isplitl []
    · ipureintro
      exact hgd
    isplitl [Htie]
    · iexact Htie
    · ipureintro
      exact histXWfSnoc x GD Hl w v hxwf hwb hlink

end lock3Transport2

/-! ## 2. GAP (3): the PLIC wire is register-only -/

section wire

open Sail Sail.ConcurrencyInterfaceV1 LeanRV64D Wlabel

/-- A wire step moves only the register file: same cpu, monad, parked fence, instruction-bits
field and row position. -/
theorem l3pAwireRsOnly (cpu : CPU) (m : SailM Unit) (rs : RegFile)
    (fn : Option (Bool × Bool × Bool × Bool)) (ib : Ibch) (k : Nat) (s' : Athread) :
    awire (.AThread (.PHart cpu m rs fn ib) k) s' →
    ∃ rs', s' = .AThread (.PHart cpu m rs' fn ib) k := by
  rintro ⟨hk, d, d', hp⟩
  obtain ⟨-, cpu0, m0, rs0, fn0, ib0, mm, b, k0, hp0, -, -, hp'⟩ :=
    pstepWireInv _ d (LDev .dev 0 []) _ d' hp
  cases hp0
  obtain ⟨p', k'⟩ := s'
  simp only at hk hp'
  subst hk hp'
  exact ⟨_, rfl⟩

end wire

end Weak
