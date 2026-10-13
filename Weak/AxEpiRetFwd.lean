/-
Weak: **the epilogue capstone WITHOUT `Hlob_gmo`: `epiRetSound2Fwd : epiRetSound2FwdStmt`**.

Rocq: `iris/AxEpiRetFwd.v` @ xxvzwolszwmp.

## What this file proves

STATEMENT.  `epiRetSound2FwdStmt` is `AxEpiRetCert.epiRetSound2Stmt` word for word MINUS the
premise `Hlob_gmo : gmoLt (0,0) (0,1)` (spill gmo-before reload), so it also covers
STORE-FORWARDING graphs (the reload performed gmo-before its own po-earlier spill).  Same
`ldspOwnOk`, same `Hwp1` (both at `epiPol`).  `epiRetSound2FwdStronger`: it implies
`epiRetSound2Stmt`.

PROOF = "ownership ⇒ reload value; run ⇒ PC from the reload value".
(A) RELOAD VALUE `graphValue GD (0,1) = some sdData`, case split on `gmoLt (0,0) (0,1)`
    (decidable, `AxEpiRetFwd.gmoLtDecRet`), as in `AxEpiSoundFwd`: (i) spill gmo-before reload:
    `epiRetStmtPremisesReload` (ownership + the 2-hart adequacy run; `Hwp1` load-bearing);
    (ii) otherwise `AxEpiSoundFwd.epiFwdOfNotLob` (pure graph fact, `AxFwdSource`).
(B) PC FROM THE RELOAD VALUE, PURE: `epiRetPcOfReload` (§3) — hart 0's pure row premises +
    `graphValue GD (0,1) = some sdData` + hart 0's run to a boundary at the row end reached after
    the c.jr ⇒ PC = `jalrTarget sdWord`.  No ownership, no hart 1, no policy/gmo premise.
So the gmo split is used ONLY for the reload value.

NON-VACUITY (§5).  `okRetFwd`: `AxEpiRetCert.okRet`'s rows with the spill moved gmo-AFTER the
reload (gmo `[LD; SD; W1]`: an rfi-forwarded reload); cat-consistent by `decide +kernel`.
`okRetFwdAllPremisesAndConcl`: EVERY premise of `epiRetSound2FwdStmt` (runs of both harts and hart
1's WPd included) holds, `Hlob_gmo` FAILS, and the conclusion holds.  OWNERSHIP STAYS
LOAD-BEARING: `raceRetNoWpd1Fwd` refutes the racing hart's WPd at `AxEpiRetCert.raceRet` (where
`Hlob_gmo` holds) from the new statement.

## Deviations from Rocq

1. PROOF ROUTE OF (B) (the KEY change; statements unaffected).  Rocq proves
   `epi_ret_pc_of_reload` by a ONE-HART phase-1 adequacy at a TRIVIAL `axirisG` instance
   (`triv_axiris`): the ledger WPd lemmas run with trivial flows (`wpd_epi_ret_triv`), the
   forward-reachability post closes at the c.jr boundary by `AxEpiRet.epi_ret_reach_pc` (the
   `chk_pre_exits` certificate), `wpd_nsteps` + `step_fupdN_soundness_no_lc'` extract the Prop,
   and the run transfers across instances (`nsteps_gv_transfer`, since Rocq's `astep_any_nf_gv`
   depends on the instance through `ax_text`).  In Lean (O2 Stage C + Q11/Q15) none of this is
   needed: `tierAAstep GD nm 0` is `astepAnyNfGv GD 0` (instance-free), each of its steps is an
   `rstep (· = GD) 0` step (`AxEpiRetFwd.rstepOfGv`, the same three arms), and AxEpiRet's
   `epiRetReachPc` is stated over FORWARD reachability from hart 0's START (AxEpiRet deviation
   1(b)) at graphs with `AxEpiRet.GFacts` — whose fields are exactly (B)'s premises, the reload
   value included.  So `epiRetPcOfReload` is `epiRetReachPc` applied to the run.  (Rocq's
   `chk_pre_exits` route is false under Stage C, AxEpiRet deviation 1(c); and AxEpiRet's
   `wpdEpiRetOwnedRb` is stated at the real ownership protocol, so it cannot run at a trivial
   instance — it is not needed.)
2. STAGE C POSITIONS AND PREMISES (as `AxEpiRetCert` deviation 1, `AxEpiRet` deviation 1(e)):
   row `[SD @0; LD @1]`, length 2; `fetchImgOk` for `fetch_gd_ok`; the c.jr fetch is the image
   conjunct `AxEpiRetCert.imgAt GD pcJr cjrVs4`; new premises `Hgd_tg` (the target's text) and
   `Hafter : rsN .PC ≠ pcJr`; `Hend0` at position 2; the `Hnw_*` premises, `T` and `Hntext` are
   dropped (AxEpiSound2 deviation 1).  The reload value is at `(0,1)` (Rocq `(0,3)`), the dropped
   premise is `gmoLt (0,0) (0,1)` (Rocq `(0,1) (0,3)`).  `epiRetPcOfReload` keeps Rocq's
   `Hcons`/`Hrow_sd`/`Hw_sd` (unused, as Rocq's proof only used them in the WPd), drops `T`,
   `Hntext`, takes `Hgd_tg`/`Hafter`, and its `Hrun0` ends at the boundary state itself.
   §5: gmo `[eLD; eSD; eW1]` (Rocq `[F0; F1; LD; SD; G0; W1; JR]`); `okRetFwdRfi` is
   `gmoLt (0,1) (0,0)` (Rocq `(0,3) (0,1)`); `okRetFwdFetchJr` is the image form; Lean-only
   `okRetFwdFetchTg` (as `AxEpiRetCert.okRetFetchTg`).  Hart 0's run reuses
   `AxEpiRetCert.driveO0Ok` and hart 1's `driveO1Ok` (same image and rows), as Rocq.
3. INSTANCES/TYPES: `#[local] Existing Instance EpiSat.epi_pol` ↦ `epiPol` passed explicitly;
   `gmo_lt_dec_ret` is the local instance `AxEpiRetFwd.gmoLtDecRet`; `Hrun*` are
   `∀ (_ : AxannotGS epiGF) (nm : GName)`, `Hwp1` `∀ [InvGS_gen .hasNoLC epiGF]
   [AxannotGS epiGF] nm`; `register_lookup PC rs` ↦ `rs .PC`; `vm_compute` ↦ `decide +kernel`.
   Rocq `Module EpiRetFwdSat` ↦ plain names.

**Rocq → Lean name map.**  `epi_ret_pc_of_reload` `epiRetPcOfReload`, `gmo_lt_dec_ret`
`AxEpiRetFwd.gmoLtDecRet`, `epi_ret_sound2_fwd_stmt` `epiRetSound2FwdStmt`, `epi_ret_sound2_fwd`
`epiRetSound2Fwd`, `epi_ret_sound2_fwd_stronger` `epiRetSound2FwdStronger`,
`race_ret_no_wpd1_fwd` `raceRetNoWpd1Fwd`; §5 `ok_ret_fwd` `okRetFwd`, `ok_ret_fwd_cat`
`okRetFwdCat`, `ok_ret_fwd_not_lob` `okRetFwdNotLob`, `ok_ret_fwd_rfi` `okRetFwdRfi`,
`ok_ret_fwd_harts` `okRetFwdHarts`, `ok_ret_fwd_fetch_sd` `okRetFwdFetchSd`,
`ok_ret_fwd_store_row` `okRetFwdStoreRow`, `ok_ret_fwd_sd_write_ok` `okRetFwdSdWriteOk`,
`ok_ret_fwd_fetch_ld` `okRetFwdFetchLd`, `ok_ret_fwd_load_row` `okRetFwdLoadRow`,
`ok_ret_fwd_ldsp_own_ok` `okRetFwdLdspOwnOk`, `ok_ret_fwd_fetch_jr` `okRetFwdFetchJr`,
`ok_ret_fwd_fetch1` `okRetFwdFetch1`, `ok_ret_fwd_sd_write_ok1` `okRetFwdSdWriteOk1`,
`ok_ret_fwd_value` `okRetFwdValue`, `ok_ret_fwd_all_premises_and_concl`
`okRetFwdAllPremisesAndConcl`.  None is in the duplicated-name table.  Lean-only:
`AxEpiRetFwd.rstepOfGv`, `AxEpiRetFwd.rtcOfRun`, `okRetFwdFetchTg`.

**Dropped** (deviation 1; no weak file uses them): §1 `triv_axiris`, `astep_gv_transfer`,
`nsteps_gv_transfer`; §2 `pin_triv`, `triv_flow_eq`, `triv_split`, `triv_fetch_flow`,
`triv_loc`, `triv_fflow`, `epi_ret_pc_Φ`, `epi_ret_pc_Φ_early`, `wpd_epi_ret_triv`,
`epi_ret_triv_run` (with the section-local instance `triv_inst`).  **Not ported:** the
`Print Assumptions` lines (the lint's axiom check covers them).  Rocq 36 declarations (incl. the
local instances); Lean 22 + 3 Lean-only.
-/
import Weak.AxEpiRetb
import Weak.AxEpiSoundFwd

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std Iris.Std.PartialMap MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D

/-! # 1. The run is forward reachability (Lean-only, deviation 1) -/

/-- A graph-pinned step is an `rstep` at the one graph `GD`. -/
theorem AxEpiRetFwd.rstepOfGv (GD : Gdexec) (i : Agent) (s s' : Athread) :
    astepAnyNfGv GD i s s' → rstep (fun GD' => GD' = GD) i s s'
  | .ANFGVProg _ _ ⟨l, h, hp⟩ => .inl ⟨GD, l, rfl, h, hp⟩
  | .ANFGVWire _ _ h => .inr (.inl h)
  | .ANFGVRead _ id K v hrd hgv hlen => .inr (.inr ⟨GD, id, K, v, rfl, hrd, hgv, hlen, rfl⟩)

theorem AxEpiRetFwd.rtcOfRun (GD : Gdexec) (i : Agent) (n : Nat) (s s' : Athread)
    (H : nsteps (astepAnyNfGv GD i) n s s') : rtc (rstep (fun GD' => GD' = GD) i) s s' :=
  rtc_subrel (AxEpiRetFwd.rstepOfGv GD i) (rtc_nsteps_2 H)

/-! # 3. THE PURE BRIDGE: reload value ⇒ PC -/

theorem epiRetPcOfReload (GD : Gdexec) (cpu : CPU) (a : Int)
    (_Hcons : rvwmoCatConsistent GD)
    (Hgd_sd : AxCjrWpd.fetchImgOk GD 0 0 pcSd sdVs)
    (_Hrow_sd : storeRowOk GD 0 0)
    (_Hw_sd : sdWriteOk GD 0 0 a)
    (Hgd_ld : AxCjrWpd.fetchImgOk GD 0 1 pcLd AxEpiLedger.ldVs)
    (Hrow_ld : loadRowOk GD 0 1)
    (Hgv_ld : graphValue GD (0, 1) = some sdData)
    (Hgd_jr : AxEpiRetCert.imgAt GD (pcJr : Int) cjrVs4)
    (Hgd_tg : AxEpiRetCert.imgAt GD ((jalrTarget sdWord).toNat : Int) AxEpiRace2Run.h1Vs4)
    (Hlen0 : (AxOpsem.grow GD 0).length = 2)
    (n : Nat) (tk : Bool) (rsN : RegFile) (ibN : Ibch)
    (Hrun0 : ∀ (_ : AxannotGS epiGF) (nm : GName),
      nsteps (tierAAstep GD nm 0) n
        ⟨.PHart cpu (riscvStep false) (probeRegs pcSd) none ibNone, 0⟩
        ⟨.PHart cpu (riscvStep tk) rsN none ibN, 2⟩)
    (Hafter : rsN .PC ≠ BitVec.ofNat 64 pcJr) :
    rsN .PC = jalrTarget sdWord := by
  have Hr := Hrun0 { axannotName := 1 } 1
  have F : AxEpiRet.GFacts GD := ⟨Hlen0, Hrow_ld, Hgv_ld, Hgd_sd.2, Hgd_ld.2, Hgd_jr, Hgd_tg⟩
  exact epiRetReachPc (fun GD' => GD' = GD) (fun GD' h => by subst h; exact F) cpu ibNone _
    (AxEpiRetFwd.rtcOfRun GD 0 n _ _ Hr) cpu tk rsN ibN rfl Hafter

/-! # 4. THE CAPSTONE WITHOUT `Hlob_gmo` -/

local instance AxEpiRetFwd.gmoLtDecRet (G : Gexec) (e1 e2 : Geid) :
    Decidable (gmoLt G e1 e2) := by
  unfold gmoLt; infer_instance

/-- `AxEpiRetCert.epiRetSound2Stmt` with the `Hlob_gmo` line removed; every other binder
IDENTICAL. -/
def epiRetSound2FwdStmt : Prop :=
  ∀ (GD : Gdexec) (cpu : CPU) (a b : Int)
    (_Hdisj : slotsDisjoint a b)
    (_Hcons : rvwmoCatConsistent GD)
    (_Hharts : ∀ e, e ∈ GD.gdG.gxGmo → e.1 = 0 ∨ e.1 = 1)
    (_Hgd_sd : AxCjrWpd.fetchImgOk GD 0 0 pcSd sdVs)
    (_Hrow_sd : storeRowOk GD 0 0)
    (_Hw_sd : sdWriteOk GD 0 0 a)
    (_Hgd_ld : AxCjrWpd.fetchImgOk GD 0 1 pcLd AxEpiLedger.ldVs)
    (_Hrow_ld : loadRowOk GD 0 1)
    (_Hok_ld : @ldspOwnOk epiPol GD 0 1 (0, 0) a (writenHist (0, 0) sdData epiHs0))
    (_Hgd_jr : AxEpiRetCert.imgAt GD (pcJr : Int) cjrVs4)
    (_Hgd_tg : AxEpiRetCert.imgAt GD ((jalrTarget sdWord).toNat : Int) AxEpiRace2Run.h1Vs4)
    (_Hlen0 : (AxOpsem.grow GD 0).length = 2)
    -- NO `Hlob_gmo`
    (sN : Athread) (n : Nat)
    (_Hrun0 : ∀ (_ : AxannotGS epiGF) (nm : GName),
      nsteps (tierAAstep GD nm 0) n
        ⟨.PHart cpu (riscvStep false) (probeRegs pcSd) none ibNone, 0⟩ sN)
    (tk : Bool) (rsN : RegFile) (ibN : Ibch)
    (_Hend0 : sN = ⟨.PHart cpu (riscvStep tk) rsN none ibN, 2⟩)
    (_Hafter : rsN .PC ≠ BitVec.ofNat 64 pcJr)
    (s0_1 sN1 : Athread) (n1 : Nat)
    (_Hk1 : s0_1.atK = 0)
    (_Hrun1 : ∀ (_ : AxannotGS epiGF) (nm : GName), nsteps (tierAAstep GD nm 1) n1 s0_1 sN1)
    (_Hend1 : sN1.atK = (AxOpsem.grow GD 1).length)
    (_Hwp1 : ∀ [InvGS_gen .hasNoLC epiGF] [AxannotGS epiGF] (nm : GName),
      ⊢ epiInit3 a b nm 1 -∗
        @tierAWpd epiGF .hasNoLC _ _ epiPol GD GName Unit epiObInterp nm s0_1 .MaybeStuck 1
          (fun _ => iprop(True))),
    rsN .PC = jalrTarget sdWord

theorem epiRetSound2Fwd : epiRetSound2FwdStmt := by
  intro GD cpu a b Hdisj Hcons Hharts Hgd_sd Hrow_sd Hw_sd Hgd_ld Hrow_ld Hok_ld Hgd_jr Hgd_tg
    Hlen0 sN n Hrun0 tk rsN ibN Hend0 Hafter s0_1 sN1 n1 Hk1 Hrun1 Hend1 Hwp1
  -- (A) ownership (or forwarding) ⇒ the reload value
  have Hgv : graphValue GD (0, 1) = some sdData := by
    by_cases Hlob_gmo : gmoLt GD.gdG (0, 0) (0, 1)
    · exact epiRetStmtPremisesReload GD cpu a b Hdisj Hcons Hharts Hgd_sd Hrow_sd Hw_sd Hgd_ld
        Hrow_ld Hok_ld Hgd_jr Hgd_tg Hlen0 Hlob_gmo sN n Hrun0 tk rsN ibN Hend0 Hafter s0_1 sN1
        n1 Hk1 Hrun1 Hend1 Hwp1
    · exact epiFwdOfNotLob GD a _ Hcons Hw_sd Hok_ld Hlob_gmo
  -- (B) the run ⇒ the PC, from the reload value alone
  subst Hend0
  exact epiRetPcOfReload GD cpu a Hcons Hgd_sd Hrow_sd Hw_sd Hgd_ld Hrow_ld Hgv Hgd_jr Hgd_tg
    Hlen0 n tk rsN ibN Hrun0 Hafter

/-- The new statement is STRONGER than the old one. -/
theorem epiRetSound2FwdStronger : epiRetSound2FwdStmt → epiRetSound2Stmt := by
  intro H GD cpu a b Hdisj Hcons Hharts Hgd_sd Hrow_sd Hw_sd Hgd_ld Hrow_ld Hok_ld Hgd_jr Hgd_tg
    Hlen0 _ sN n Hrun0 tk rsN ibN Hend0 Hafter s0_1 sN1 n1 Hk1 Hrun1 Hend1 Hwp1
  exact H GD cpu a b Hdisj Hcons Hharts Hgd_sd Hrow_sd Hw_sd Hgd_ld Hrow_ld Hok_ld Hgd_jr Hgd_tg
    Hlen0 sN n Hrun0 tk rsN ibN Hend0 Hafter s0_1 sN1 n1 Hk1 Hrun1 Hend1 Hwp1

/-- OWNERSHIP STAYS LOAD-BEARING: `raceRet` has `Hlob_gmo` true, so the racing hart's WPd is
refuted by the NEW statement too. -/
theorem raceRetNoWpd1Fwd (cpu : CPU) :
    ¬ (∀ [InvGS_gen .hasNoLC epiGF] [AxannotGS epiGF] (nm : GName),
      ⊢ epiInit3 ldAddr race2B nm 1 -∗
        @tierAWpd epiGF .hasNoLC _ _ epiPol raceRet GName Unit epiObInterp nm
          (h1rState cpu) .MaybeStuck 1 (fun _ => iprop(True))) :=
  raceRetRefutesHwp1 cpu (epiRetSound2FwdStronger epiRetSound2Fwd)

/-! # 5. NON-VACUITY ON A FORWARDING GRAPH -/

/-- `okRet`'s rows; the spill `(0,0)` is gmo-AFTER the reload `(0,1)` (it stays the first WRITE
in gmo): the reload is forwarded (rfi) from its po-earlier spill. -/
def okRetFwd : Gdexec :=
  ⟨⟨retImg, [AxEpiRetCert.row0o, row1x], [AxEpiRace2.eLD, AxEpiRace2.eSD, AxEpiRace2.eW1]⟩, [], []⟩

theorem okRetFwdCat : rvwmoCatConsistent okRetFwd :=
  catConsistentBSound _ (by decide +kernel)

theorem okRetFwdNotLob : ¬ gmoLt okRetFwd.gdG (0, 0) (0, 1) := by
  intro h
  have h' := (gmoLtBSpec _ _ _).2 h
  revert h'
  decide +kernel

theorem okRetFwdRfi : gmoLt okRetFwd.gdG (0, 1) (0, 0) :=
  (gmoLtBSpec _ _ _).1 (by decide +kernel)

theorem okRetFwdHarts : ∀ e, e ∈ okRetFwd.gdG.gxGmo → e.1 = 0 ∨ e.1 = 1 := by
  intro e He
  have hg : okRetFwd.gdG.gxGmo = [(0, 1), (0, 0), (1, 0)] := rfl
  rw [hg] at He
  simp only [List.mem_cons, List.not_mem_nil, _root_.or_false] at He
  rcases He with rfl | rfl | rfl
  · exact Or.inl rfl
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem okRetFwdFetchSd : AxCjrWpd.fetchImgOk okRetFwd 0 0 pcSd sdVs := by
  refine ⟨by decide, ?_⟩
  intro j hj
  have hj' : j < 4 := hj
  match j, hj' with
  | 0, _ => decide +kernel
  | 1, _ => decide +kernel
  | 2, _ => decide +kernel
  | 3, _ => decide +kernel

theorem okRetFwdStoreRow : storeRowOk okRetFwd 0 0 := ⟨_, rfl⟩

theorem okRetFwdSdWriteOk : sdWriteOk okRetFwd 0 0 ldAddr := by
  refine ⟨by decide +kernel, ?_, rfl⟩
  rintro a' v' ⟨l, base, vs, j, Hl, Hw, Hv, Ha⟩
  have Hl0 : gxLbl okRetFwd.gdG (0, 0) = some (Lbl.LStore false sdAddr sdData .WCplain) := rfl
  rw [Hl0, Option.some.injEq] at Hl
  subst Hl
  simp only [lbWr, Option.some.injEq, Prod.mk.injEq] at Hw
  obtain ⟨rfl, rfl⟩ := Hw
  exact ⟨j, Hv, Ha.symm⟩

theorem okRetFwdFetchLd : AxCjrWpd.fetchImgOk okRetFwd 0 1 pcLd AxEpiLedger.ldVs := by
  refine ⟨by decide, ?_⟩
  intro j hj
  have hj' : j < 2 := hj
  match j, hj' with
  | 0, _ => decide +kernel
  | 1, _ => decide +kernel

theorem okRetFwdLoadRow : loadRowOk okRetFwd 0 1 := ⟨_, rfl, rfl⟩

theorem okRetFwdLdspOwnOk :
    @ldspOwnOk epiPol okRetFwd 0 1 (0, 0) ldAddr (writenHist (0, 0) sdData epiHs0) := by
  have hbef : ((0, 0) : Geid) ∈ eidsBefore okRetFwd 0 1 :=
    (elemOfEidsBefore _ _ _ _).2 ⟨rfl, by decide, by decide +kernel⟩
  refine ⟨?_, hbef, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change ((0, 0) : Geid) ∈ epiLobp okRetFwd (0, 1)
    unfold epiLobp
    split
    · exact elemOfIntersection.2 ⟨elemOfSingleton.2 rfl, hbef⟩
    · rename_i hne
      exact absurd rfl hne
  · decide +kernel
  · decide +kernel
  · intro x hx
    exact hx
  · exact ⟨false, [1, 1, 1, 1, 1, 1, 1, 1], sdData, rfl, rfl, rfl⟩
  · intro j H hH p hp
    obtain ⟨v, rfl, hv⟩ := race2Hs1Lookup j H hH
    rw [List.mem_singleton] at hp
    subst hp
    exact AxEpilogue.gwritesOfStore _ (0, 0) false sdAddr sdData .WCplain j v rfl hv
  · intro j H hH n w1 w2 _ hw2
    obtain ⟨v, rfl, _⟩ := race2Hs1Lookup j H hH
    cases n <;> simp at hw2
  · intro j H hH w v' _ hpo
    obtain ⟨v, rfl, _⟩ := race2Hs1Lookup j H hH
    obtain ⟨w1, w2⟩ := w
    obtain ⟨h1, h2, _, _⟩ := hpo
    simp only at h1 h2
    have hw2 : w2 = 0 := by omega
    subst h1 hw2
    exact List.mem_singleton.2 rfl
  · exact (gpoBSpec _ _ _).1 (by decide +kernel)

theorem okRetFwdFetchJr : AxEpiRetCert.imgAt okRetFwd (pcJr : Int) cjrVs4 := by
  intro j hj
  have hj' : j < 4 := hj
  match j, hj' with
  | 0, _ => decide +kernel
  | 1, _ => decide +kernel
  | 2, _ => decide +kernel
  | 3, _ => decide +kernel

/-- (Lean-only, deviation 2) The target's text. -/
theorem okRetFwdFetchTg :
    AxEpiRetCert.imgAt okRetFwd ((jalrTarget sdWord).toNat : Int) AxEpiRace2Run.h1Vs4 := by
  rw [jalrTargetSdWord]
  intro j hj
  have hj' : j < 4 := hj
  match j, hj' with
  | 0, _ => decide +kernel
  | 1, _ => decide +kernel
  | 2, _ => decide +kernel
  | 3, _ => decide +kernel

theorem okRetFwdFetch1 : AxCjrWpd.fetchImgOk okRetFwd 1 0 AxEpiRace2.pc1 AxEpiRace2Run.h1Vs4 := by
  refine ⟨by decide, ?_⟩
  intro j hj
  have hj' : j < 4 := hj
  match j, hj' with
  | 0, _ => decide +kernel
  | 1, _ => decide +kernel
  | 2, _ => decide +kernel
  | 3, _ => decide +kernel

theorem okRetFwdSdWriteOk1 : sdWriteOkGen okRetFwd 1 0 race2B raceData := by
  refine ⟨by decide +kernel, ?_, rfl⟩
  rintro a' v' ⟨l, base, vs, j, Hl, Hw, Hv, Ha⟩
  have Hl0 : gxLbl okRetFwd.gdG (1, 0) = some (Lbl.LStore false race2B raceData .WCplain) := rfl
  rw [Hl0, Option.some.injEq] at Hl
  subst Hl
  simp only [lbWr, Option.some.injEq, Prod.mk.injEq] at Hw
  obtain ⟨rfl, rfl⟩ := Hw
  exact ⟨j, Hv, Ha.symm⟩

/-- The reload reads the spill — by FORWARDING. -/
theorem okRetFwdValue : graphValue okRetFwd (0, 1) = some sdData := by
  decide +kernel

/-- EVERY premise of `epiRetSound2FwdStmt` holds at `okRetFwd` (runs of both harts and hart 1's
WPd included), `Hlob_gmo` FAILS, and the conclusion holds. -/
theorem okRetFwdAllPremisesAndConcl (cpu : CPU) :
    ∃ (sN : Athread) (n : Nat) (tk : Bool) (rsN : RegFile) (ibN : Ibch) (sN1 : Athread)
      (n1 : Nat),
      slotsDisjoint ldAddr race2B ∧
      rvwmoCatConsistent okRetFwd ∧
      (∀ e, e ∈ okRetFwd.gdG.gxGmo → e.1 = 0 ∨ e.1 = 1) ∧
      AxCjrWpd.fetchImgOk okRetFwd 0 0 pcSd sdVs ∧
      storeRowOk okRetFwd 0 0 ∧
      sdWriteOk okRetFwd 0 0 ldAddr ∧
      AxCjrWpd.fetchImgOk okRetFwd 0 1 pcLd AxEpiLedger.ldVs ∧
      loadRowOk okRetFwd 0 1 ∧
      @ldspOwnOk epiPol okRetFwd 0 1 (0, 0) ldAddr (writenHist (0, 0) sdData epiHs0) ∧
      AxEpiRetCert.imgAt okRetFwd (pcJr : Int) cjrVs4 ∧
      AxEpiRetCert.imgAt okRetFwd ((jalrTarget sdWord).toNat : Int) AxEpiRace2Run.h1Vs4 ∧
      (AxOpsem.grow okRetFwd 0).length = 2 ∧
      ¬ gmoLt okRetFwd.gdG (0, 0) (0, 1) ∧
      (∀ (_ : AxannotGS epiGF) (nm : GName),
        nsteps (tierAAstep okRetFwd nm 0) n
          ⟨.PHart cpu (riscvStep false) (probeRegs pcSd) none ibNone, 0⟩ sN) ∧
      sN = ⟨.PHart cpu (riscvStep tk) rsN none ibN, 2⟩ ∧
      rsN .PC ≠ BitVec.ofNat 64 pcJr ∧
      (h1xState cpu ibNone).atK = 0 ∧
      (∀ (_ : AxannotGS epiGF) (nm : GName),
        nsteps (tierAAstep okRetFwd nm 1) n1 (h1xState cpu ibNone) sN1) ∧
      sN1.atK = (AxOpsem.grow okRetFwd 1).length ∧
      (∀ [InvGS_gen .hasNoLC epiGF] [AxannotGS epiGF] (nm : GName),
        ⊢ epiInit3 ldAddr race2B nm 1 -∗
          @tierAWpd epiGF .hasNoLC _ _ epiPol okRetFwd GName Unit epiObInterp nm
            (h1xState cpu ibNone) .MaybeStuck 1 (fun _ => iprop(True))) ∧
      rsN .PC = jalrTarget sdWord := by
  -- hart 0's row and the image are `okRet`'s: reuse the driver computations
  have Hok0 : driveBdPc (driveBd okRetFwd.gdG.gxImg (AxOpsem.grow okRetFwd 0) 2 1 runFuel
      (riscvStep false) (probeRegs pcSd) ibNone 0) = some 0x80000100 :=
    AxEpiRetCert.driveO0Ok
  unfold driveBdPc at Hok0
  cases Hd0 : driveBd okRetFwd.gdG.gxImg (AxOpsem.grow okRetFwd 0) 2 1 runFuel
      (riscvStep false) (probeRegs pcSd) ibNone 0 with
  | none => rw [Hd0] at Hok0; exact absurd Hok0 (by simp)
  | some r =>
    obtain ⟨rs, ib⟩ := r
    rw [Hd0, Option.some.injEq] at Hok0
    obtain ⟨n, Hr0⟩ := driveBdSound okRetFwd 0 2 runFuel 1 _ _ _ _ rs ib Hd0
    have Hok1 : AxEpiRace2Run.driveK (drive okRetFwd.gdG.gxImg (AxOpsem.grow okRetFwd 1) 1
        runFuel (riscvStep false) h1xRegs ibNone 0) = some 1 :=
      AxEpiRetCert.driveO1Ok
    unfold AxEpiRace2Run.driveK at Hok1
    cases Hd1 : drive okRetFwd.gdG.gxImg (AxOpsem.grow okRetFwd 1) 1 runFuel (riscvStep false)
        h1xRegs ibNone 0 with
    | none => rw [Hd1] at Hok1; exact absurd Hok1 (by simp)
    | some r1 =>
      obtain ⟨m1, rs1, ib1, k1⟩ := r1
      obtain ⟨Hk, n1, Hr1⟩ := driveSound okRetFwd 1 1 runFuel _ _ _ _ m1 rs1 ib1 k1 Hd1
      subst Hk
      refine ⟨AxEpiRun.st cpu (riscvStep false) rs ib 2, n, false, rs, ib,
        AxEpiRun.st cpu m1 rs1 ib1 1, n1, ?_, okRetFwdCat, okRetFwdHarts, okRetFwdFetchSd,
        okRetFwdStoreRow, okRetFwdSdWriteOk, okRetFwdFetchLd, okRetFwdLoadRow, okRetFwdLdspOwnOk,
        okRetFwdFetchJr, okRetFwdFetchTg, rfl, okRetFwdNotLob, fun _ _ => Hr0 cpu, rfl,
        ?_, rfl, fun _ _ => Hr1 cpu, rfl,
        wpdHart1xOwnSdHwp1 okRetFwd ldAddr cpu ibNone okRetFwdFetch1 ⟨_, rfl⟩ okRetFwdSdWriteOk1
          rfl, ?_⟩
      · unfold slotsDisjoint race2B
        omega
      · intro He
        rw [He] at Hok0
        exact absurd Hok0 (by decide)
      · apply BitVec.eq_of_toNat_eq
        rw [Hok0, jalrTargetSdWord]

end Weak
