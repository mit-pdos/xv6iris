/-
Weak: **the CAPSTONE STATEMENT "the epilogue returns to the spilled `ra` BY OWNERSHIP"**
(`epiRetSound2Stmt`, a `def` of the `Prop`, NOT proved here) and its two CERTIFICATES.

Rocq: `iris/AxEpiRetCert.v` @ xxvzwolszwmp.

## What this file states and proves

STATEMENT.  2 harts.  Hart 0 runs the concrete `c.sdsp ra,8(sp); c.ldsp ra,8(sp); c.jr ra`
(Sail `riscvStep false` from `probeRegs pcSd`); its row is the 2 events `[store sdData at a;
8-byte reload at a]` (Stage C: the three fetches are pinned admin steps, no row items).  Hart 1
is arbitrary, with a WPd from its own slot-`b` auths (`Hwp1`, as in
`AxEpiSound3.epiReloadSound3`).  Hart 0's run ends at an INSTRUCTION BOUNDARY reached AFTER the
c.jr step (`Hend0` + `Hafter`, see deviation 1).  CONCLUSION: PC = `jalrTarget sdWord`.

§1 the statement.  §2 `driveBd`: the `AxEpiRun` driver continued past the row end up to a chosen
`.pure`→`riscvStep false` junction, sound for `astepAnyNfGv`.  §3 the shared image and text.
§4 CERTIFICATE 1 (`raceRet`: hart 1 races a store of `raceData` into hart 0's slot): every
premise but `Hwp1` holds and the conclusion is FALSE (`raceRetPremisesButNotConcl`); hence the
statement refutes that racing hart's WPd (`raceRetRefutesHwp1`).  §5 CERTIFICATE 2 (`okRet`:
hart 1 = `AxEpiTwinExact`'s exact twin, own slot): EVERY premise, `Hwp1` included, holds and the
conclusion is TRUE (`okRetAllPremisesAndConcl`).  CAVEAT (as Rocq): the statement keeps
`Hlob_gmo` (spill gmo-before reload), so store forwarding is excluded.

## Deviations from Rocq

1. O2 STAGE C + OWNER Q11 (after-step boundaries + second pinned fetch stage at the target).
   (a) Fetches are no row items: hart 0's row has 2 items (Rocq 5), positions shift
       (`storeRowOk GD 0 0`, `sdWriteOk GD 0 0 a`, `loadRowOk GD 0 1`,
       `ldspOwnOk GD 0 1 (0,0) a (writenHist (0,0) …)`, `gmoLt (0,0) (0,1)`, length 2); the
       fetch premises are `AxCjrWpd.fetchImgOk GD 0 0 pcSd sdVs` / `… 0 1 pcLd ldVs`; the c.jr
       fetch sits AT the row end, so `Hgd_jr` is the image conjunct only
       (`AxEpiRetCert.imgAt GD pcJr cjrVs4`; with `Hlen0` it is `AxCjrReach.Gf 2 pcJr cjrVs4 0 GD`,
       `AxEpiRetCert.gfJr`).  The `Hnw_*` premises (`gis_w` of fetch events) are dropped, and with
       them the `*_nw_*` certificate lemmas; `jr_lbl`/`eJR` are dropped (no c.jr fetch event);
       `row0r`/`row0o` are the Stage-C rows `AxEpiRace2.row0` / `AxEpiSdLdSat.row`; gmo
       `[eSD; eW1; eLD]` (Rocq `[eF0; eSD; eF1; eG0; eW1; eLD; eJR]`).
   (b) `Hend0`: the boundary is at row position 2 (Rocq 5).  In Rocq position 5 lies strictly
       after the c.jr's fetch EVENT, so it excludes the boundary before the c.jr; in Lean the
       boundary after the c.ldsp (PC = `pcJr`) is itself at position 2.  Per Q11 the statement
       is restated over boundaries reached AFTER the c.jr step: new premise
       `Hafter : rsN .PC ≠ BitVec.ofNat 64 pcJr` (the hart has left the c.jr; the start boundary
       and its PLIC-wire variants have PC = `pcJr`).
   (c) In Lean the NEXT instruction's fetch at the target is not stuck at the row end (an admin
       step answered from the image; Rocq: stuck at its RAM fetch).  Per Q11 the statement pins
       the target's text — new premise `Hgd_tg : AxEpiRetCert.imgAt GD (jalrTarget sdWord).toNat
       AxEpiRace2Run.h1Vs4` (the 4 image bytes at 0x80000100 are `c.sdsp ra,8(sp); 0; 0`, whose
       store is the next data access, stuck at the row end), so a walk with a second pinned fetch
       stage (`base2`/`vs2`) at the target excludes any further boundary.  Both certificates
       satisfy it (`raceRetFetchTg`, `okRetFetchTg`: `race2Img` holds `h1Vs4` at `pc1`).
   (d) `driveBd` takes the image (first argument, `AxEpiRun` deviation 1) and a SKIP count
       `nskip` (Lean-only): it stops at the `(nskip+1)`-th `.pure` node at position `kend`
       (Rocq: the first).  The certificates use `nskip = 1`: the first `.pure` at position 2 ends
       the c.ldsp, the second ends the c.jr.
2. TEXT (`AxEpiSound2` deviation 1): `tierAAstep`/`tierAWpd` take no text `T`; the statement's
   `T` and `Hntext` are dropped, and `¬ retText ldAddr` leaves the certificate bundles.
   `retText`/`retNtext` are kept (name map).
3. INSTANCES (`AxEpiRun` deviation 4, `AxEpiSound2` deviation 2): `driveBdSound` quantifies over
   `cpu` only; `Hrun0`/`Hrun1` are `∀ (_ : AxannotGS epiGF) (nm : GName)`; `Hwp1` is
   `∀ [InvGS_gen .hasNoLC epiGF] [AxannotGS epiGF] (nm : GName)` with `epiPol` explicit.
4. TYPES: `register_lookup PC rs` ↦ `rs .PC`; `bv_unsigned` ↦ `BitVec.toNat`; `oib32` ↦
   `Ibch`; `Interface.Ret` ↦ `.pure`; `S k` ↦ `k + 1`; `vm_compute` ↦ `decide +kernel`; the
   Rocq `fetch_ok` Ltac is unfolded at each use.
5. NAMES: generic short names are file-qualified (`AxEpiRetCert.row0r`, `.row0o`, `.driveR0`,
   `.driveR1`, `.driveO0`, `.driveO1`, `.driveR0Ok`, `.driveR1Ok`, `.driveO0Ok`, `.driveO1Ok`).

**Rocq → Lean name map.**  `sd_word` `sdWord`, `epi_ret_sound2_stmt` `epiRetSound2Stmt`,
`drive_bd` `driveBd`, `drive_bd_sound` `driveBdSound`, `drive_bd_pc` `driveBdPc`,
`jalr_target_sd_word` `jalrTargetSdWord`, `ret_img` `retImg`, `ret_text` `retText`, `ret_ntext`
`retNtext`, `row0r` `AxEpiRetCert.row0r`, `race_ret` `raceRet`, `race_ret_cat` `raceRetCat`,
`race_ret_harts` `raceRetHarts`, `race_ret_fetch_sd` `raceRetFetchSd`, `race_ret_store_row`
`raceRetStoreRow`, `race_ret_sd_write_ok` `raceRetSdWriteOk`, `race_ret_fetch_ld`
`raceRetFetchLd`, `race_ret_load_row` `raceRetLoadRow`, `race_ret_ldsp_own_ok`
`raceRetLdspOwnOk`, `race_ret_fetch_jr` `raceRetFetchJr`, `race_ret_len0` `raceRetLen0`,
`race_ret_lob_gmo` `raceRetLobGmo`, `race_ret_value` `raceRetValue`, `race_ret_gmo_sd_w1`
`raceRetGmoSdW1`, `drive_r0` `AxEpiRetCert.driveR0`, `drive_r1` `AxEpiRetCert.driveR1`,
`drive_r0_ok` `AxEpiRetCert.driveR0Ok`, `drive_r1_ok` `AxEpiRetCert.driveR1Ok`, `h1r_state`
`h1rState`, `race_ret_premises_but_not_concl` `raceRetPremisesButNotConcl`,
`race_ret_refutes_Hwp1` `raceRetRefutesHwp1`, `row0o` `AxEpiRetCert.row0o`, `ok_ret` `okRet`,
`ok_ret_cat` `okRetCat`, `ok_ret_harts` `okRetHarts`, `ok_ret_fetch_sd` `okRetFetchSd`,
`ok_ret_store_row` `okRetStoreRow`, `ok_ret_sd_write_ok` `okRetSdWriteOk`, `ok_ret_fetch_ld`
`okRetFetchLd`, `ok_ret_load_row` `okRetLoadRow`, `ok_ret_ldsp_own_ok` `okRetLdspOwnOk`,
`ok_ret_fetch_jr` `okRetFetchJr`, `ok_ret_len0` `okRetLen0`, `ok_ret_lob_gmo` `okRetLobGmo`,
`ok_ret_fetch1` `okRetFetch1`, `ok_ret_store_row1` `okRetStoreRow1`, `ok_ret_sd_write_ok1`
`okRetSdWriteOk1`, `ok_ret_len1` `okRetLen1`, `ok_ret_value` `okRetValue`, `drive_o0`
`AxEpiRetCert.driveO0`, `drive_o1` `AxEpiRetCert.driveO1`, `drive_o0_ok` `AxEpiRetCert.driveO0Ok`,
`drive_o1_ok` `AxEpiRetCert.driveO1Ok`, `ok_ret_all_premises_and_concl`
`okRetAllPremisesAndConcl`.  None is in the duplicated-name table.  Lean-only (file-qualified
or new): `AxEpiRetCert.imgAt`, `AxEpiRetCert.gfJr`, `raceRetFetchTg`, `okRetFetchTg`.

**Dropped:** `jr_lbl`, `eJR`, `race_ret_nw_sd/ld/jr`, `ok_ret_nw_sd/ld/jr`, `ok_ret_nw1`
(deviation 1(a)); the `fetch_ok` Ltac (deviation 4); the `Print Assumptions` lines (the lint's
axiom check covers them).  Rocq 65 declarations (incl. the Ltac); Lean 54 + 4 Lean-only.
-/
import Weak.AxEpiTwinExact
import Weak.AxEpiCjrSym
import Weak.AxCjrReach

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std Iris.Std.PartialMap MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D
open Lbl

/-! # 1. THE CAPSTONE STATEMENT -/

/-- The spilled return address, as the 64-bit word the reload writes to `x1`. -/
def sdWord : BitVec 64 := wordOfBytes 8 sdData

/-- (Lean-only, deviation 1(a)) The image holds `vs` at `base` (`AxCjrReach.Gf`'s first
conjunct, verbatim). -/
def AxEpiRetCert.imgAt (GD : Gdexec) (base : Int) (vs : List (BitVec 8)) : Prop :=
  ∀ j : Nat, j < vs.length → GD.gdG.gxImg (base + j) = vs[j]?

/-- (Lean-only) The c.jr premises are `AxCjrReach`'s region geometry. -/
theorem AxEpiRetCert.gfJr (GD : Gdexec) (Hgd_jr : AxEpiRetCert.imgAt GD (pcJr : Int) cjrVs4)
    (Hlen0 : (AxOpsem.grow GD 0).length = 2) : Gf 2 (pcJr : Int) cjrVs4 0 GD :=
  ⟨Hgd_jr, Hlen0⟩

def epiRetSound2Stmt : Prop :=
  ∀ (GD : Gdexec) (cpu : CPU) (a b : Int)
    (_Hdisj : slotsDisjoint a b)
    (_Hcons : rvwmoCatConsistent GD)
    (_Hharts : ∀ e, e ∈ GD.gdG.gxGmo → e.1 = 0 ∨ e.1 = 1)
    -- hart 0's row: sound3's pure premises + the c.jr fetch + the target's text (dev. 1)
    (_Hgd_sd : AxCjrWpd.fetchImgOk GD 0 0 pcSd sdVs)
    (_Hrow_sd : storeRowOk GD 0 0)
    (_Hw_sd : sdWriteOk GD 0 0 a)
    (_Hgd_ld : AxCjrWpd.fetchImgOk GD 0 1 pcLd AxEpiLedger.ldVs)
    (_Hrow_ld : loadRowOk GD 0 1)
    (_Hok_ld : @ldspOwnOk epiPol GD 0 1 (0, 0) a (writenHist (0, 0) sdData epiHs0))
    (_Hgd_jr : AxEpiRetCert.imgAt GD (pcJr : Int) cjrVs4)
    (_Hgd_tg : AxEpiRetCert.imgAt GD ((jalrTarget sdWord).toNat : Int) AxEpiRace2Run.h1Vs4)
    (_Hlen0 : (AxOpsem.grow GD 0).length = 2)
    (_Hlob_gmo : gmoLt GD.gdG (0, 0) (0, 1))
    -- hart 0's run, to a FIXED sN
    (sN : Athread) (n : Nat)
    (_Hrun0 : ∀ (_ : AxannotGS epiGF) (nm : GName),
      nsteps (tierAAstep GD nm 0) n
        ⟨.PHart cpu (riscvStep false) (probeRegs pcSd) none ibNone, 0⟩ sN)
    -- ... ending at an INSTRUCTION BOUNDARY at the row end, AFTER the c.jr step (dev. 1(b))
    (tk : Bool) (rsN : RegFile) (ibN : Ibch)
    (_Hend0 : sN = ⟨.PHart cpu (riscvStep tk) rsN none ibN, 2⟩)
    (_Hafter : rsN .PC ≠ BitVec.ofNat 64 pcJr)
    -- hart 1: an ARBITRARY program, its run, and its WPd from ITS OWN auths
    (s0_1 sN1 : Athread) (n1 : Nat)
    (_Hk1 : s0_1.atK = 0)
    (_Hrun1 : ∀ (_ : AxannotGS epiGF) (nm : GName), nsteps (tierAAstep GD nm 1) n1 s0_1 sN1)
    (_Hend1 : sN1.atK = (AxOpsem.grow GD 1).length)
    (_Hwp1 : ∀ [InvGS_gen .hasNoLC epiGF] [AxannotGS epiGF] (nm : GName),
      ⊢ epiInit3 a b nm 1 -∗
        @tierAWpd epiGF .hasNoLC _ _ epiPol GD GName Unit epiObInterp nm s0_1 .MaybeStuck 1
          (fun _ => iprop(True))),
    rsN .PC = jalrTarget sdWord

/-! # 2. The boundary driver -/

/-- Like `drive`, but it runs until the `(nskip+1)`-th `.pure` node at row position `kend`,
takes that `.pure`→`riscvStep false` junction and stops: the result is the register file and
ib at the boundary state `st cpu (riscvStep false) rs ib kend` (deviation 1(d)). -/
noncomputable def driveBd (img : Image) (row : List Lbl) (kend : Nat) :
    Nat → Nat → SailM Unit → RegFile → Ibch → Nat → Option (RegFile × Ibch)
  | _, 0, _, _, _, _ => none
  | nskip, f + 1, m, rs, ib, k =>
    match nodeStep img row m rs ib k with
    | none => none
    | some (m1, rs1, ib1, k1) =>
      match m with
      | .pure _ =>
        if k = kend then
          match nskip with
          | 0 => some (rs1, ib1)
          | j + 1 => driveBd img row kend j f m1 rs1 ib1 k1
        else driveBd img row kend nskip f m1 rs1 ib1 k1
      | _ => driveBd img row kend nskip f m1 rs1 ib1 k1

theorem driveBdSound (GD : Gdexec) (i : Agent) (kend : Nat) :
    ∀ (fuel nskip : Nat) (m : SailM Unit) (rs : RegFile) (ib : Ibch) (k : Nat)
      (rs' : RegFile) (ib' : Ibch),
      driveBd GD.gdG.gxImg (AxOpsem.grow GD i) kend nskip fuel m rs ib k = some (rs', ib') →
      ∃ n, ∀ cpu : CPU,
        nsteps (astepAnyNfGv GD i) n (AxEpiRun.st cpu m rs ib k)
          (AxEpiRun.st cpu (riscvStep false) rs' ib' kend) := by
  intro fuel
  induction fuel with
  | zero =>
    intro nskip m rs ib k rs' ib' Hd
    simp only [driveBd, reduceCtorEq] at Hd
  | succ f ih =>
    intro nskip m rs ib k rs' ib' Hd
    simp only [driveBd] at Hd
    cases Hn : nodeStep GD.gdG.gxImg (AxOpsem.grow GD i) m rs ib k with
    | none => rw [Hn] at Hd; exact absurd Hd (by simp)
    | some r =>
      obtain ⟨m1, rs1, ib1, k1⟩ := r
      rw [Hn] at Hd
      have Hs : ∀ cpu : CPU, astepAnyNfGv GD i (AxEpiRun.st cpu m rs ib k)
          (AxEpiRun.st cpu m1 rs1 ib1 k1) :=
        fun cpu => nodeStepSound GD i cpu m rs ib k m1 rs1 ib1 k1 Hn
      have Hcont : ∀ j, driveBd GD.gdG.gxImg (AxOpsem.grow GD i) kend j f m1 rs1 ib1 k1 =
          some (rs', ib') → ∃ n, ∀ cpu : CPU,
            nsteps (astepAnyNfGv GD i) n (AxEpiRun.st cpu m rs ib k)
              (AxEpiRun.st cpu (riscvStep false) rs' ib' kend) := by
        intro j Hd'
        obtain ⟨n, Hr⟩ := ih j m1 rs1 ib1 k1 rs' ib' Hd'
        exact ⟨n + 1, fun cpu => nsteps_l (Hs cpu) (Hr cpu)⟩
      cases m with
      | impure c kk => exact Hcont nskip Hd
      | pure y =>
        simp only at Hd
        split at Hd
        · rename_i hk
          cases nskip with
          | zero =>
            simp only [Option.some.injEq, Prod.mk.injEq] at Hd
            obtain ⟨rfl, rfl⟩ := Hd
            simp only [nodeStep, Option.some.injEq, Prod.mk.injEq] at Hn
            obtain ⟨rfl, rfl, rfl, rfl⟩ := Hn
            refine ⟨1, fun cpu => ?_⟩
            rw [← hk]
            exact nsteps_l (Hs cpu) (nsteps_O _)
          | succ j => exact Hcont j Hd
        · exact Hcont nskip Hd

def driveBdPc (d : Option (RegFile × Ibch)) : Option Nat :=
  match d with
  | some (rs, _) => some (rs .PC).toNat
  | none => none

theorem jalrTargetSdWord : (jalrTarget sdWord).toNat = 0x80000100 := by
  decide +kernel

/-! # 3. The shared image and text -/

/-- `race2Img` with the 4 bytes `cjrVs4` at `[pcJr, pcJr+4)`. -/
def retImg : Image := fun a =>
  if (pcJr : Int) ≤ a ∧ a < (pcJr : Int) + 4 then cjrVs4[(a - (pcJr : Int)).toNat]?
  else race2Img a

def retText (a : Int) : Prop :=
  ((pcSd : Int) ≤ a ∧ a < (pcSd : Int) + 8) ∨
  ((AxEpiRace2.pc1 : Int) ≤ a ∧ a < (AxEpiRace2.pc1 : Int) + 4)

theorem retNtext : ¬ retText ldAddr := by
  unfold retText ldAddr spVal pcSd AxEpiRace2.pc1
  omega

/-! # 4. CERTIFICATE 1: the race -/

/-- Hart 0: `race2`'s row (the reload reads hart 1's `raceData`; Stage C: no c.jr fetch item). -/
def AxEpiRetCert.row0r : List Lbl := AxEpiRace2.row0

def raceRet : Gdexec :=
  ⟨⟨retImg, [AxEpiRetCert.row0r, AxEpiRace2Run.row1'],
    [AxEpiRace2.eSD, AxEpiRace2.eW1, AxEpiRace2.eLD]⟩, []⟩

theorem raceRetCat : rvwmoCatConsistent raceRet :=
  catConsistentBSound _ (by decide +kernel)

theorem raceRetHarts : ∀ e, e ∈ raceRet.gdG.gxGmo → e.1 = 0 ∨ e.1 = 1 := by
  intro e He
  have hg : raceRet.gdG.gxGmo = [(0, 0), (1, 0), (0, 1)] := rfl
  rw [hg] at He
  simp only [List.mem_cons, List.not_mem_nil, or_false] at He
  rcases He with rfl | rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exact Or.inl rfl

theorem raceRetFetchSd : AxCjrWpd.fetchImgOk raceRet 0 0 pcSd sdVs := by
  refine ⟨by decide, ?_⟩
  intro j hj
  have hj' : j < 4 := hj
  match j, hj' with
  | 0, _ => decide +kernel
  | 1, _ => decide +kernel
  | 2, _ => decide +kernel
  | 3, _ => decide +kernel

theorem raceRetStoreRow : storeRowOk raceRet 0 0 := ⟨_, rfl⟩

theorem raceRetSdWriteOk : sdWriteOk raceRet 0 0 ldAddr := by
  refine ⟨by decide +kernel, ?_, rfl⟩
  rintro a' v' ⟨l, base, vs, j, Hl, Hw, Hv, Ha⟩
  have Hl0 : gxLbl raceRet.gdG (0, 0) = some (Lbl.LStore false sdAddr sdData .WCplain) := rfl
  rw [Hl0, Option.some.injEq] at Hl
  subst Hl
  simp only [lbWr, Option.some.injEq, Prod.mk.injEq] at Hw
  obtain ⟨rfl, rfl⟩ := Hw
  exact ⟨j, Hv, Ha.symm⟩

theorem raceRetFetchLd : AxCjrWpd.fetchImgOk raceRet 0 1 pcLd AxEpiLedger.ldVs := by
  refine ⟨by decide, ?_⟩
  intro j hj
  have hj' : j < 2 := hj
  match j, hj' with
  | 0, _ => decide +kernel
  | 1, _ => decide +kernel

theorem raceRetLoadRow : loadRowOk raceRet 0 1 := ⟨_, rfl, rfl⟩

theorem raceRetLdspOwnOk :
    @ldspOwnOk epiPol raceRet 0 1 (0, 0) ldAddr (writenHist (0, 0) sdData epiHs0) := by
  have hbef : ((0, 0) : Geid) ∈ eidsBefore raceRet 0 1 :=
    (elemOfEidsBefore _ _ _ _).2 ⟨rfl, by decide, by decide +kernel⟩
  refine ⟨?_, hbef, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change ((0, 0) : Geid) ∈ epiLobp raceRet (0, 1)
    unfold epiLobp
    split
    · exact elemOfIntersection.2 ⟨elemOfSingleton.2 rfl, hbef⟩
    · rename_i hne
      exact absurd rfl hne
  · decide +kernel
  · decide +kernel
  · intro x hx
    exact hx
  · exact ⟨false, AxEpiRace2.t2, raceData, rfl, rfl, rfl⟩
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

theorem raceRetFetchJr : AxEpiRetCert.imgAt raceRet (pcJr : Int) cjrVs4 := by
  intro j hj
  have hj' : j < 4 := hj
  match j, hj' with
  | 0, _ => decide +kernel
  | 1, _ => decide +kernel
  | 2, _ => decide +kernel
  | 3, _ => decide +kernel

/-- (Lean-only, deviation 1(c)) The target's text. -/
theorem raceRetFetchTg :
    AxEpiRetCert.imgAt raceRet ((jalrTarget sdWord).toNat : Int) AxEpiRace2Run.h1Vs4 := by
  rw [jalrTargetSdWord]
  intro j hj
  have hj' : j < 4 := hj
  match j, hj' with
  | 0, _ => decide +kernel
  | 1, _ => decide +kernel
  | 2, _ => decide +kernel
  | 3, _ => decide +kernel

theorem raceRetLen0 : (AxOpsem.grow raceRet 0).length = 2 := rfl

theorem raceRetLobGmo : gmoLt raceRet.gdG (0, 0) (0, 1) :=
  (gmoLtBSpec _ _ _).1 (by decide +kernel)

/-- The race: the reload reads `raceData`, hart 1's write is gmo-after the spill. -/
theorem raceRetValue : graphValue raceRet (0, 1) = some raceData := rfl

theorem raceRetGmoSdW1 : gmoLt raceRet.gdG AxEpiRace2.eSD AxEpiRace2.eW1 :=
  (gmoLtBSpec _ _ _).1 (by decide +kernel)

/-- The runs. -/
noncomputable def AxEpiRetCert.driveR0 : Option (RegFile × Ibch) :=
  driveBd raceRet.gdG.gxImg (AxOpsem.grow raceRet 0) 2 1 runFuel (riscvStep false)
    (probeRegs pcSd) ibNone 0

noncomputable def AxEpiRetCert.driveR1 : Option (SailM Unit × RegFile × Ibch × Nat) :=
  drive raceRet.gdG.gxImg (AxOpsem.grow raceRet 1) 1 runFuel (riscvStep false)
    AxEpiRace2Run.regs1 ibNone 0

/-- Hart 0 reaches the post-c.jr boundary with PC = 0x80000200 (= `raceData`'s word). -/
theorem AxEpiRetCert.driveR0Ok : driveBdPc AxEpiRetCert.driveR0 = some 0x80000200 := by
  decide +kernel

theorem AxEpiRetCert.driveR1Ok : AxEpiRace2Run.driveK AxEpiRetCert.driveR1 = some 1 := by
  decide +kernel

noncomputable def h1rState (cpu : CPU) : Athread :=
  ⟨.PHart cpu (riscvStep false) AxEpiRace2Run.regs1 none ibNone, 0⟩

theorem raceRetPremisesButNotConcl (cpu : CPU) :
    ∃ (sN : Athread) (n : Nat) (tk : Bool) (rsN : RegFile) (ibN : Ibch) (sN1 : Athread)
      (n1 : Nat),
      slotsDisjoint ldAddr race2B ∧
      rvwmoCatConsistent raceRet ∧
      (∀ e, e ∈ raceRet.gdG.gxGmo → e.1 = 0 ∨ e.1 = 1) ∧
      AxCjrWpd.fetchImgOk raceRet 0 0 pcSd sdVs ∧
      storeRowOk raceRet 0 0 ∧
      sdWriteOk raceRet 0 0 ldAddr ∧
      AxCjrWpd.fetchImgOk raceRet 0 1 pcLd AxEpiLedger.ldVs ∧
      loadRowOk raceRet 0 1 ∧
      @ldspOwnOk epiPol raceRet 0 1 (0, 0) ldAddr (writenHist (0, 0) sdData epiHs0) ∧
      AxEpiRetCert.imgAt raceRet (pcJr : Int) cjrVs4 ∧
      AxEpiRetCert.imgAt raceRet ((jalrTarget sdWord).toNat : Int) AxEpiRace2Run.h1Vs4 ∧
      (AxOpsem.grow raceRet 0).length = 2 ∧
      gmoLt raceRet.gdG (0, 0) (0, 1) ∧
      (∀ (_ : AxannotGS epiGF) (nm : GName),
        nsteps (tierAAstep raceRet nm 0) n
          ⟨.PHart cpu (riscvStep false) (probeRegs pcSd) none ibNone, 0⟩ sN) ∧
      sN = ⟨.PHart cpu (riscvStep tk) rsN none ibN, 2⟩ ∧
      rsN .PC ≠ BitVec.ofNat 64 pcJr ∧
      (h1rState cpu).atK = 0 ∧
      (∀ (_ : AxannotGS epiGF) (nm : GName),
        nsteps (tierAAstep raceRet nm 1) n1 (h1rState cpu) sN1) ∧
      sN1.atK = (AxOpsem.grow raceRet 1).length ∧
      rsN .PC ≠ jalrTarget sdWord := by
  have Hok0 := AxEpiRetCert.driveR0Ok
  unfold driveBdPc at Hok0
  cases Hd0 : AxEpiRetCert.driveR0 with
  | none => rw [Hd0] at Hok0; exact absurd Hok0 (by simp)
  | some r =>
    obtain ⟨rs, ib⟩ := r
    rw [Hd0, Option.some.injEq] at Hok0
    obtain ⟨n, Hr0⟩ := driveBdSound raceRet 0 2 runFuel 1 _ _ _ _ rs ib Hd0
    have Hok1 := AxEpiRetCert.driveR1Ok
    unfold AxEpiRace2Run.driveK at Hok1
    cases Hd1 : AxEpiRetCert.driveR1 with
    | none => rw [Hd1] at Hok1; exact absurd Hok1 (by simp)
    | some r1 =>
      obtain ⟨m1, rs1, ib1, k1⟩ := r1
      obtain ⟨Hk, n1, Hr1⟩ := driveSound raceRet 1 1 runFuel _ _ _ _ m1 rs1 ib1 k1 Hd1
      subst Hk
      refine ⟨AxEpiRun.st cpu (riscvStep false) rs ib 2, n, false, rs, ib,
        AxEpiRun.st cpu m1 rs1 ib1 1, n1, ?_, raceRetCat, raceRetHarts, raceRetFetchSd,
        raceRetStoreRow, raceRetSdWriteOk, raceRetFetchLd, raceRetLoadRow, raceRetLdspOwnOk,
        raceRetFetchJr, raceRetFetchTg, raceRetLen0, raceRetLobGmo, fun _ _ => Hr0 cpu, rfl,
        ?_, rfl, fun _ _ => Hr1 cpu, rfl, ?_⟩
      · unfold slotsDisjoint race2B
        omega
      · intro He
        rw [He] at Hok0
        exact absurd Hok0 (by decide)
      · intro He
        rw [He, jalrTargetSdWord] at Hok0
        exact absurd Hok0 (by decide)

/-- Sanity: the certificate matches the statement's premises exactly — the statement refutes
the racing hart's WPd from its own slot-`race2B` auths. -/
theorem raceRetRefutesHwp1 (cpu : CPU) :
    epiRetSound2Stmt →
    ¬ (∀ [InvGS_gen .hasNoLC epiGF] [AxannotGS epiGF] (nm : GName),
      ⊢ epiInit3 ldAddr race2B nm 1 -∗
        @tierAWpd epiGF .hasNoLC _ _ epiPol raceRet GName Unit epiObInterp nm
          (h1rState cpu) .MaybeStuck 1 (fun _ => iprop(True))) := by
  intro Hstmt Hwp1
  obtain ⟨sN, n, tk, rsN, ibN, sN1, n1, Hdisj, Hcons, Hharts, Hgd_sd, Hrow_sd, Hw_sd, Hgd_ld,
    Hrow_ld, Hok_ld, Hgd_jr, Hgd_tg, Hlen0, Hlob, Hrun0, Hend0, Hafter, Hk1, Hrun1, Hend1,
    Hnot⟩ := raceRetPremisesButNotConcl cpu
  exact Hnot (Hstmt raceRet cpu ldAddr race2B Hdisj Hcons Hharts Hgd_sd Hrow_sd Hw_sd Hgd_ld
    Hrow_ld Hok_ld Hgd_jr Hgd_tg Hlen0 Hlob sN n Hrun0 tk rsN ibN Hend0 Hafter (h1rState cpu)
    sN1 n1 Hk1 Hrun1 Hend1 Hwp1)

/-! # 5. CERTIFICATE 2: satisfiable (no race) -/

/-- Hart 0: `AxEpiSdLdSat.row` (the reload reads the spill; Stage C: no c.jr fetch item). -/
def AxEpiRetCert.row0o : List Lbl := AxEpiSdLdSat.row

def okRet : Gdexec :=
  ⟨⟨retImg, [AxEpiRetCert.row0o, row1x], [AxEpiRace2.eSD, AxEpiRace2.eW1, AxEpiRace2.eLD]⟩, []⟩

theorem okRetCat : rvwmoCatConsistent okRet :=
  catConsistentBSound _ (by decide +kernel)

theorem okRetHarts : ∀ e, e ∈ okRet.gdG.gxGmo → e.1 = 0 ∨ e.1 = 1 := by
  intro e He
  have hg : okRet.gdG.gxGmo = [(0, 0), (1, 0), (0, 1)] := rfl
  rw [hg] at He
  simp only [List.mem_cons, List.not_mem_nil, or_false] at He
  rcases He with rfl | rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exact Or.inl rfl

theorem okRetFetchSd : AxCjrWpd.fetchImgOk okRet 0 0 pcSd sdVs := by
  refine ⟨by decide, ?_⟩
  intro j hj
  have hj' : j < 4 := hj
  match j, hj' with
  | 0, _ => decide +kernel
  | 1, _ => decide +kernel
  | 2, _ => decide +kernel
  | 3, _ => decide +kernel

theorem okRetStoreRow : storeRowOk okRet 0 0 := ⟨_, rfl⟩

theorem okRetSdWriteOk : sdWriteOk okRet 0 0 ldAddr := by
  refine ⟨by decide +kernel, ?_, rfl⟩
  rintro a' v' ⟨l, base, vs, j, Hl, Hw, Hv, Ha⟩
  have Hl0 : gxLbl okRet.gdG (0, 0) = some (Lbl.LStore false sdAddr sdData .WCplain) := rfl
  rw [Hl0, Option.some.injEq] at Hl
  subst Hl
  simp only [lbWr, Option.some.injEq, Prod.mk.injEq] at Hw
  obtain ⟨rfl, rfl⟩ := Hw
  exact ⟨j, Hv, Ha.symm⟩

theorem okRetFetchLd : AxCjrWpd.fetchImgOk okRet 0 1 pcLd AxEpiLedger.ldVs := by
  refine ⟨by decide, ?_⟩
  intro j hj
  have hj' : j < 2 := hj
  match j, hj' with
  | 0, _ => decide +kernel
  | 1, _ => decide +kernel

theorem okRetLoadRow : loadRowOk okRet 0 1 := ⟨_, rfl, rfl⟩

theorem okRetLdspOwnOk :
    @ldspOwnOk epiPol okRet 0 1 (0, 0) ldAddr (writenHist (0, 0) sdData epiHs0) := by
  have hbef : ((0, 0) : Geid) ∈ eidsBefore okRet 0 1 :=
    (elemOfEidsBefore _ _ _ _).2 ⟨rfl, by decide, by decide +kernel⟩
  refine ⟨?_, hbef, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change ((0, 0) : Geid) ∈ epiLobp okRet (0, 1)
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

theorem okRetFetchJr : AxEpiRetCert.imgAt okRet (pcJr : Int) cjrVs4 := by
  intro j hj
  have hj' : j < 4 := hj
  match j, hj' with
  | 0, _ => decide +kernel
  | 1, _ => decide +kernel
  | 2, _ => decide +kernel
  | 3, _ => decide +kernel

/-- (Lean-only, deviation 1(c)) The target's text. -/
theorem okRetFetchTg :
    AxEpiRetCert.imgAt okRet ((jalrTarget sdWord).toNat : Int) AxEpiRace2Run.h1Vs4 := by
  rw [jalrTargetSdWord]
  intro j hj
  have hj' : j < 4 := hj
  match j, hj' with
  | 0, _ => decide +kernel
  | 1, _ => decide +kernel
  | 2, _ => decide +kernel
  | 3, _ => decide +kernel

theorem okRetLen0 : (AxOpsem.grow okRet 0).length = 2 := rfl

theorem okRetLobGmo : gmoLt okRet.gdG (0, 0) (0, 1) :=
  (gmoLtBSpec _ _ _).1 (by decide +kernel)

/-- Hart 1's graph premises (for `wpdHart1xOwnSdHwp1`). -/
theorem okRetFetch1 : AxCjrWpd.fetchImgOk okRet 1 0 AxEpiRace2.pc1 AxEpiRace2Run.h1Vs4 := by
  refine ⟨by decide, ?_⟩
  intro j hj
  have hj' : j < 4 := hj
  match j, hj' with
  | 0, _ => decide +kernel
  | 1, _ => decide +kernel
  | 2, _ => decide +kernel
  | 3, _ => decide +kernel

theorem okRetStoreRow1 : storeRowOk okRet 1 0 := ⟨_, rfl⟩

theorem okRetSdWriteOk1 : sdWriteOkGen okRet 1 0 race2B raceData := by
  refine ⟨by decide +kernel, ?_, rfl⟩
  rintro a' v' ⟨l, base, vs, j, Hl, Hw, Hv, Ha⟩
  have Hl0 : gxLbl okRet.gdG (1, 0) = some (Lbl.LStore false race2B raceData .WCplain) := rfl
  rw [Hl0, Option.some.injEq] at Hl
  subst Hl
  simp only [lbWr, Option.some.injEq, Prod.mk.injEq] at Hw
  obtain ⟨rfl, rfl⟩ := Hw
  exact ⟨j, Hv, Ha.symm⟩

theorem okRetLen1 : (AxOpsem.grow okRet 1).length = 1 := rfl

theorem okRetValue : graphValue okRet (0, 1) = some sdData := rfl

noncomputable def AxEpiRetCert.driveO0 : Option (RegFile × Ibch) :=
  driveBd okRet.gdG.gxImg (AxOpsem.grow okRet 0) 2 1 runFuel (riscvStep false)
    (probeRegs pcSd) ibNone 0

noncomputable def AxEpiRetCert.driveO1 : Option (SailM Unit × RegFile × Ibch × Nat) :=
  drive okRet.gdG.gxImg (AxOpsem.grow okRet 1) 1 runFuel (riscvStep false) h1xRegs ibNone 0

/-- Hart 0 reaches the post-c.jr boundary with PC = 0x80000100 (= the spilled word). -/
theorem AxEpiRetCert.driveO0Ok : driveBdPc AxEpiRetCert.driveO0 = some 0x80000100 := by
  decide +kernel

theorem AxEpiRetCert.driveO1Ok : AxEpiRace2Run.driveK AxEpiRetCert.driveO1 = some 1 := by
  decide +kernel

theorem okRetAllPremisesAndConcl (cpu : CPU) :
    ∃ (sN : Athread) (n : Nat) (tk : Bool) (rsN : RegFile) (ibN : Ibch) (sN1 : Athread)
      (n1 : Nat),
      slotsDisjoint ldAddr race2B ∧
      rvwmoCatConsistent okRet ∧
      (∀ e, e ∈ okRet.gdG.gxGmo → e.1 = 0 ∨ e.1 = 1) ∧
      AxCjrWpd.fetchImgOk okRet 0 0 pcSd sdVs ∧
      storeRowOk okRet 0 0 ∧
      sdWriteOk okRet 0 0 ldAddr ∧
      AxCjrWpd.fetchImgOk okRet 0 1 pcLd AxEpiLedger.ldVs ∧
      loadRowOk okRet 0 1 ∧
      @ldspOwnOk epiPol okRet 0 1 (0, 0) ldAddr (writenHist (0, 0) sdData epiHs0) ∧
      AxEpiRetCert.imgAt okRet (pcJr : Int) cjrVs4 ∧
      AxEpiRetCert.imgAt okRet ((jalrTarget sdWord).toNat : Int) AxEpiRace2Run.h1Vs4 ∧
      (AxOpsem.grow okRet 0).length = 2 ∧
      gmoLt okRet.gdG (0, 0) (0, 1) ∧
      (∀ (_ : AxannotGS epiGF) (nm : GName),
        nsteps (tierAAstep okRet nm 0) n
          ⟨.PHart cpu (riscvStep false) (probeRegs pcSd) none ibNone, 0⟩ sN) ∧
      sN = ⟨.PHart cpu (riscvStep tk) rsN none ibN, 2⟩ ∧
      rsN .PC ≠ BitVec.ofNat 64 pcJr ∧
      (h1xState cpu ibNone).atK = 0 ∧
      (∀ (_ : AxannotGS epiGF) (nm : GName),
        nsteps (tierAAstep okRet nm 1) n1 (h1xState cpu ibNone) sN1) ∧
      sN1.atK = (AxOpsem.grow okRet 1).length ∧
      (∀ [InvGS_gen .hasNoLC epiGF] [AxannotGS epiGF] (nm : GName),
        ⊢ epiInit3 ldAddr race2B nm 1 -∗
          @tierAWpd epiGF .hasNoLC _ _ epiPol okRet GName Unit epiObInterp nm
            (h1xState cpu ibNone) .MaybeStuck 1 (fun _ => iprop(True))) ∧
      rsN .PC = jalrTarget sdWord := by
  have Hok0 := AxEpiRetCert.driveO0Ok
  unfold driveBdPc at Hok0
  cases Hd0 : AxEpiRetCert.driveO0 with
  | none => rw [Hd0] at Hok0; exact absurd Hok0 (by simp)
  | some r =>
    obtain ⟨rs, ib⟩ := r
    rw [Hd0, Option.some.injEq] at Hok0
    obtain ⟨n, Hr0⟩ := driveBdSound okRet 0 2 runFuel 1 _ _ _ _ rs ib Hd0
    have Hok1 := AxEpiRetCert.driveO1Ok
    unfold AxEpiRace2Run.driveK at Hok1
    cases Hd1 : AxEpiRetCert.driveO1 with
    | none => rw [Hd1] at Hok1; exact absurd Hok1 (by simp)
    | some r1 =>
      obtain ⟨m1, rs1, ib1, k1⟩ := r1
      obtain ⟨Hk, n1, Hr1⟩ := driveSound okRet 1 1 runFuel _ _ _ _ m1 rs1 ib1 k1 Hd1
      subst Hk
      refine ⟨AxEpiRun.st cpu (riscvStep false) rs ib 2, n, false, rs, ib,
        AxEpiRun.st cpu m1 rs1 ib1 1, n1, ?_, okRetCat, okRetHarts, okRetFetchSd,
        okRetStoreRow, okRetSdWriteOk, okRetFetchLd, okRetLoadRow, okRetLdspOwnOk,
        okRetFetchJr, okRetFetchTg, okRetLen0, okRetLobGmo, fun _ _ => Hr0 cpu, rfl,
        ?_, rfl, fun _ _ => Hr1 cpu, rfl,
        wpdHart1xOwnSdHwp1 okRet ldAddr cpu ibNone okRetFetch1 okRetStoreRow1 okRetSdWriteOk1
          okRetLen1, ?_⟩
      · unfold slotsDisjoint race2B
        omega
      · intro He
        rw [He] at Hok0
        exact absurd Hok0 (by decide)
      · apply BitVec.eq_of_toNat_eq
        rw [Hok0, jalrTargetSdWord]

end Weak
