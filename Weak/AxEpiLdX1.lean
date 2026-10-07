/-
Weak: **after the concrete `c.ldsp ra,8(sp)`, `x1` holds the loaded word.**

Rocq: `iris/AxEpiLdX1.v` @ xxvzwolszwmp.

## The Rocq header, in substance

`AxEpiLedger.epiLedgerCldsp` certifies the post-load continuation for EVERY loaded word `x`, but
its post (`ldPost`) pins only the PC.  Here the post is `ldPostX1` = `ldPost` ∧ "x1 holds the
loaded word".  The model's value written to `x1` for loaded word `x` is `ldVal x` (the
`checked_mem_read` loop and `vmem_read_addr` splices of `x` into zeros, then `sign_extend`); the
kernel's lazy conversion checks the model's term against `ldVal x` head-first without normalising
the stuck arithmetic on the free `x`, and `ldVal x = x` is plain bitvector algebra (`ldValId`).
RESULTS: `epiLedgerCldspX1` (`AxLdModelFacts` at `tAt pcLd` with `ldPostX1`),
`epiLedgerCldspAfterSdX1` (the same at every `AxEpiLedgerTick.tAfterSd v' v`, the tick = false
handoff after `c.sdsp`), `cldspPostLoadX1` (the `epure`-level statement).

## Deviations from Rocq

1. THE KERNEL ROUTE (Rocq: `change_no_check` to a hand-written reduced form `ld_branch_nf`, checked
   by the kernel at `Qed`).  Lean has no `change_no_check`; the same kernel conversion is obtained
   with `ax_epi_ledger_krfl` (`AxEpiLedger`) on an EQUATION: the Lean-only value twins
   `AxEpiLdX1.ldLoadE/ldFetchE/ldBranchE/ldBranchAtE` (the `AxEpiLedger.ld*B` twins returning the
   final register file instead of a boolean, at ONE free 64-bit word) observed through
   `AxEpiLdX1.obs` (`(ldPostB rs, rs .x1)`) must equal `some (true, ldVal x)` — the kernel unfolds
   the model on the left and compares the stuck `x1` value with `ldVal x` lazily.  So
   `ldBranchNf t v' v` is that equation for every `x` (Rocq: one closed `Prop`, the same at every
   state and answer), and `ldBranchNfHolds` is the BRIDGE `ldBranchNf t v' v → ldBranchAt … ldPostX1
   t v' v` (Rocq: the proof of the reduced form); the equation itself is kernel-checked per state
   and answer pair (via the Lean-only bridges `AxEpiLdX1.ldLoadOfE/ldFetchOfE/ldBranchOfE/
   ldBranchAtOfE`).
2. THE TWO-PIN BOUNDARY (`AxEpiLedger` deviation 1): four branch fields, `tAfterSd v' v` takes both
   answers (`epiLedgerCldspAfterSdX1 v' v`), and `cldspPostLoadX1` walks `toPin` to the `sig_meip`
   node (answered `v'`) and then to the `sig_seip` node (answered `v`); Rocq's `dir` flag is gone.
   Stage C: as `AxEpiLedger` deviation 3 (the fetch node is matched exactly as there).
3. TYPES (`AxEpiLedger` deviation 4): `Dr_noseip` ↦ `AxEpiProbe.drNopin`, `Dw_all` ↦ `DwAll`,
   `D_post` ↦ `DPost`, `ld_vs` ↦ `AxEpiLedger.ldVs`; the request types carry `va`; `uint (register_lookup
   r rs)` ↦ `(rs r).toNat`, `bv_unsigned x` ↦ `x.toNat`; `ldPostX1` takes the `Int` of the ledger
   (`((rs .x1).toNat : Int) = x`) and `cldspPostLoadX1` concludes in `Nat` (as `ldPost`).
   `ldVal` is in the Lean model's vocabulary (`sign_extend`, `Sail.BitVec.updateSubrange`, `zeros`
   over `8 * 8` / `8 * 1 * 8`, the shapes the model's term carries); `ldValId` states
   `(ldVal x).toNat = x.toNat` (Rocq `bv_unsigned`), via the Lean-only `AxEpiLdX1.ldValEq`.

**Rocq → Lean name map.**  `ld_post_x1` `ldPostX1`, `ld_val` `ldVal`, `ld_val_id` `ldValId`,
`ld_branch_nf` `ldBranchNf`, `ld_branch_nf_holds` `ldBranchNfHolds`, `epi_ledger_cldsp_x1`
`epiLedgerCldspX1`, `epi_ledger_cldsp_after_sd_x1` `epiLedgerCldspAfterSdX1`,
`cldsp_post_load_x1` `cldspPostLoadX1`.  None is in the duplicated-name table.  Lean-only
(file-qualified, `AxEpiLdX1.*`): `ldLoadE`, `ldFetchE`, `ldBranchE`, `ldBranchAtE`, `obs`,
`ldValEq`, `ldLoadOfE`, `ldFetchOfE`, `ldBranchOfE`, `ldBranchAtOfE`.

**Dropped:** nothing (Rocq 8 definitions/lemmas; Lean 8 + 10 Lean-only).  **Not ported:** the
`Print Assumptions` block (the lint's axiom check covers it).
-/
import Weak.AxEpiLedgerTick

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std Iris.Std.PartialMap MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D
open LeanRV64D.Functions
open Wlabel

/-- The post-load predicate: `ldPost` plus "x1 holds the loaded word". -/
def ldPostX1 (x : Int) (rs : RegFile) : Prop :=
  ldPost x rs ∧ ((rs .x1).toNat : Int) = x

/-- The model's value written to x1 by the load, for loaded word `x`. -/
def ldVal (x : BitVec 64) : BitVec 64 :=
  sign_extend (m := 64) (k_n := 8 * 8)
    (Sail.BitVec.updateSubrange (zeros (n := 8 * 8)) (8 * 8 - 1) 0
      (Sail.BitVec.updateSubrange (zeros (n := 8 * 1 * 8)) (8 * 1 * 8 - 1) (8 * 0 * 8) x))

/-- (Lean-only) `ldVal` is the identity. -/
theorem AxEpiLdX1.ldValEq (x : BitVec 64) : ldVal x = x := by
  simp [ldVal, sign_extend, zeros, Sail.BitVec.signExtend, Sail.BitVec.updateSubrange,
    Sail.BitVec.updateSubrange']

theorem ldValId (x : BitVec 64) : (ldVal x).toNat = x.toNat := by
  rw [AxEpiLdX1.ldValEq]

/-! # The value twins -/

/-- (Lean-only) The value twin of `ldLoadOk` at a 64-bit word `x`: the final register file. -/
def AxEpiLdX1.ldLoadE (D : List Register) (ldaddr : Int) (ml : SailM Unit) (tl : ExecSt)
    (x : BitVec 64) : Option RegFile :=
  match ml with
  | .impure (.ok (.memRead nl _ reql)) KK =>
    if (!devAddr reql.pa && !(classify reql.access_kind).akLatest &&
        !(classify reql.access_kind).akIfetch && decide (paZ reql.pa = ldaddr)) = true then
      if h : nl = 8 then
        match epure D (KK (.Ok (x.cast (by omega), none))) tl with
        | some (_, s) => some s.regs
        | none => none
      else none
    else none
  | _ => none

/-- (Lean-only) The value twin of `ldFetchOk`. -/
def AxEpiLdX1.ldFetchE (Dr Dw D : List Register) (base : Int) (vs : List (BitVec 8))
    (ldaddr : Int) (mf : SailM Unit) (t2 : ExecSt) (x : BitVec 64) : Option RegFile :=
  match mf with
  | .impure (.ok (.memRead n _ req)) KKf =>
    if (!devAddr req.pa && (classify req.access_kind).akIfetch &&
        decide (paZ req.pa = base) && decide (vs.length = n)) = true then
      match erd Dr Dw (KKf (.Ok (wordOfBytes n vs, none))) t2 with
      | some (ml, tl) => AxEpiLdX1.ldLoadE D ldaddr ml tl x
      | none => none
    else none
  | _ => none

/-- (Lean-only) The value twin of `ldBranchOk`. -/
def AxEpiLdX1.ldBranchE (Dr Dw D : List Register) (base : Int) (vs : List (BitVec 8))
    (ldaddr : Int) (m : SailM Unit) (t1 : ExecSt) (x : BitVec 64) : Option RegFile :=
  match erd Dr Dw m t1 with
  | some (mf, t2) => AxEpiLdX1.ldFetchE Dr Dw D base vs ldaddr mf t2 x
  | none => none

/-- (Lean-only) The value twin of `ldBranchAt`. -/
noncomputable def AxEpiLdX1.ldBranchAtE (Dr Dw D : List Register) (base : Int)
    (vs : List (BitVec 8)) (ldaddr : Int) (t : ExecSt) (v' v : BitVec 1) (x : BitVec 64) :
    Option RegFile :=
  match AxEpiLedger.toPin (riscvStep false) t with
  | some (m0, t0) =>
    match AxEpiLedger.toPin (AxEpiLedger.ansMeip m0 v') t0 with
    | some (m1, t1) => AxEpiLdX1.ldBranchE Dr Dw D base vs ldaddr (ansSeip m1 v) t1 x
    | none => none
  | none => none

/-- (Lean-only) What the kernel check observes of the final register file. -/
def AxEpiLdX1.obs (rs : RegFile) : Bool × BitVec 64 := (AxEpiLedger.ldPostB rs, rs .x1)

/-! # The bridges -/

theorem AxEpiLdX1.ldLoadOfE (D : List Register) (ldaddr : Int) (postLd : Int → RegFile → Prop)
    (ml : SailM Unit) (tl : ExecSt)
    (H : ∀ x : BitVec 64, ∃ rs, AxEpiLdX1.ldLoadE D ldaddr ml tl x = some rs ∧
      postLd (x.toNat : Int) rs) :
    ldLoadOk D ldaddr postLd ml tl := by
  obtain ⟨rs0, h0, -⟩ := H 0
  cases ml with
  | pure _ => simp [AxEpiLdX1.ldLoadE] at h0
  | impure call KK =>
    cases call with
    | error _ => simp [AxEpiLdX1.ldLoadE] at h0
    | ok o =>
      cases o
      case memRead nl va reql =>
        simp only [AxEpiLdX1.ldLoadE] at h0
        split at h0
        · rename_i hc
          simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hc
          obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hc
          by_cases hn : nl = 8
          · subst hn
            simp only [ldLoadOk]
            refine ⟨h1, h2, h3, h4, by omega, fun x => ?_⟩
            obtain ⟨rs, hx, hp⟩ := H (x.cast (by omega))
            simp only [AxEpiLdX1.ldLoadE, BitVec.cast_eq, dite_true] at hx
            split at hx
            · cases he : epure D (KK (.Ok (x, none))) tl with
              | none => rw [he] at hx; simp at hx
              | some p =>
                obtain ⟨u, s⟩ := p
                rw [he] at hx
                have hs : s.regs = rs := Option.some.inj hx
                rw [BitVec.toNat_cast] at hp
                dsimp only
                rw [hs]
                exact hp
            · simp at hx
          · simp [hn] at h0
        · simp at h0
      all_goals simp [AxEpiLdX1.ldLoadE] at h0

theorem AxEpiLdX1.ldFetchOfE (Dr Dw D : List Register) (base : Int) (vs : List (BitVec 8))
    (ldaddr : Int) (postLd : Int → RegFile → Prop) (mf : SailM Unit) (t2 : ExecSt)
    (H : ∀ x : BitVec 64, ∃ rs, AxEpiLdX1.ldFetchE Dr Dw D base vs ldaddr mf t2 x = some rs ∧
      postLd (x.toNat : Int) rs) :
    ldFetchOk Dr Dw D base vs ldaddr postLd mf t2 := by
  obtain ⟨rs0, h0, -⟩ := H 0
  cases mf with
  | pure _ => simp [AxEpiLdX1.ldFetchE] at h0
  | impure call KKf =>
    cases call with
    | error _ => simp [AxEpiLdX1.ldFetchE] at h0
    | ok o =>
      cases o
      case memRead n va req =>
        simp only [AxEpiLdX1.ldFetchE] at h0
        split at h0
        · rename_i hc
          simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hc
          obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hc
          cases he : erd Dr Dw (KKf (.Ok (wordOfBytes n vs, none))) t2 with
          | none => rw [he] at h0; simp at h0
          | some p =>
            obtain ⟨ml, tl⟩ := p
            simp only [ldFetchOk, he]
            refine ⟨h1, h2, h3, h4, AxEpiLdX1.ldLoadOfE D ldaddr postLd ml tl (fun x => ?_)⟩
            obtain ⟨rs, hx, hp⟩ := H x
            simp only [AxEpiLdX1.ldFetchE, he] at hx
            split at hx
            · exact ⟨rs, hx, hp⟩
            · simp at hx
        · simp at h0
      all_goals simp [AxEpiLdX1.ldFetchE] at h0

theorem AxEpiLdX1.ldBranchOfE (Dr Dw D : List Register) (base : Int) (vs : List (BitVec 8))
    (ldaddr : Int) (postLd : Int → RegFile → Prop) (m : SailM Unit) (t1 : ExecSt)
    (H : ∀ x : BitVec 64, ∃ rs, AxEpiLdX1.ldBranchE Dr Dw D base vs ldaddr m t1 x = some rs ∧
      postLd (x.toNat : Int) rs) :
    ldBranchOk Dr Dw D base vs ldaddr postLd m t1 := by
  unfold ldBranchOk
  cases he : erd Dr Dw m t1 with
  | none =>
    obtain ⟨rs0, h0, -⟩ := H 0
    simp [AxEpiLdX1.ldBranchE, he] at h0
  | some p =>
    obtain ⟨mf, t2⟩ := p
    refine AxEpiLdX1.ldFetchOfE Dr Dw D base vs ldaddr postLd mf t2 (fun x => ?_)
    obtain ⟨rs, hx, hp⟩ := H x
    simp only [AxEpiLdX1.ldBranchE, he] at hx
    exact ⟨rs, hx, hp⟩

theorem AxEpiLdX1.ldBranchAtOfE (Dr Dw D : List Register) (base : Int)
    (vs : List (BitVec 8)) (ldaddr : Int) (postLd : Int → RegFile → Prop) (t : ExecSt)
    (v' v : BitVec 1)
    (H : ∀ x : BitVec 64, ∃ rs,
      AxEpiLdX1.ldBranchAtE Dr Dw D base vs ldaddr t v' v x = some rs ∧
      postLd (x.toNat : Int) rs) :
    ldBranchAt Dr Dw D base vs ldaddr postLd t v' v := by
  unfold ldBranchAt
  cases h1 : AxEpiLedger.toPin (riscvStep false) t with
  | none =>
    obtain ⟨rs0, h0, -⟩ := H 0
    simp [AxEpiLdX1.ldBranchAtE, h1] at h0
  | some p =>
    obtain ⟨m0, t0⟩ := p
    dsimp only
    cases h2 : AxEpiLedger.toPin (AxEpiLedger.ansMeip m0 v') t0 with
    | none =>
      obtain ⟨rs0, h0, -⟩ := H 0
      simp [AxEpiLdX1.ldBranchAtE, h1, h2] at h0
    | some p2 =>
      obtain ⟨m1, t1⟩ := p2
      dsimp only
      refine AxEpiLdX1.ldBranchOfE Dr Dw D base vs ldaddr postLd _ t1 (fun x => ?_)
      obtain ⟨rs, hx, hp⟩ := H x
      simp only [AxEpiLdX1.ldBranchAtE, h1, h2] at hx
      exact ⟨rs, hx, hp⟩

/-! # The reduced form and the ledgers -/

/-- The kernel-checked form of `ldBranchAt … ldPostX1 t v' v` (deviation 1): along the branch, for
every loaded word `x`, the run ends with the PC check passing and `x1 = ldVal x`. -/
def ldBranchNf (t : ExecSt) (v' v : BitVec 1) : Prop :=
  ∀ x : BitVec 64,
    (AxEpiLdX1.ldBranchAtE AxEpiProbe.drNopin DwAll DPost (pcLd : Int) AxEpiLedger.ldVs ldAddr
      t v' v x).map AxEpiLdX1.obs = some (true, ldVal x)

theorem ldBranchNfHolds (t : ExecSt) (v' v : BitVec 1) (H : ldBranchNf t v' v) :
    ldBranchAt AxEpiProbe.drNopin DwAll DPost (pcLd : Int) AxEpiLedger.ldVs ldAddr ldPostX1
      t v' v := by
  refine AxEpiLdX1.ldBranchAtOfE _ _ _ _ _ _ _ t v' v (fun x => ?_)
  have h := H x
  cases he : AxEpiLdX1.ldBranchAtE AxEpiProbe.drNopin DwAll DPost (pcLd : Int)
      AxEpiLedger.ldVs ldAddr t v' v x with
  | none => rw [he] at h; simp at h
  | some rs =>
    rw [he] at h
    have h' : AxEpiLdX1.obs rs = (true, ldVal x) := Option.some.inj h
    have hpc : AxEpiLedger.ldPostB rs = true := congrArg Prod.fst h'
    have hx1 : rs .x1 = ldVal x := congrArg Prod.snd h'
    refine ⟨rs, rfl, AxEpiLedger.ldPostOfB _ _ hpc, ?_⟩
    rw [hx1, ldValId]

theorem epiLedgerCldspX1 :
    AxLdModelFacts (tAt pcLd) AxEpiProbe.drNopin DwAll DPost (pcLd : Int) AxEpiLedger.ldVs
      ldAddr ldPostX1 where
  lgSeipDr := by decide +kernel
  lgMeipDr := by decide +kernel
  lgSeipD := by decide +kernel
  lgMeipD := by decide +kernel
  lgHead := by decide +kernel
  lgToSeip := by decide +kernel
  lgBranch00 := ldBranchNfHolds _ _ _ (by intro x; ax_epi_ledger_krfl)
  lgBranch01 := ldBranchNfHolds _ _ _ (by intro x; ax_epi_ledger_krfl)
  lgBranch10 := ldBranchNfHolds _ _ _ (by intro x; ax_epi_ledger_krfl)
  lgBranch11 := ldBranchNfHolds _ _ _ (by intro x; ax_epi_ledger_krfl)

theorem epiLedgerCldspAfterSdX1 (v' v : BitVec 1) :
    AxLdModelFacts (tAfterSd v' v) AxEpiProbe.drNopin DwAll DPost (pcLd : Int)
      AxEpiLedger.ldVs ldAddr ldPostX1 := by
  rcases bv1Cases v' with rfl | rfl <;> rcases bv1Cases v with rfl | rfl <;>
  exact {
    lgSeipDr := by decide +kernel
    lgMeipDr := by decide +kernel
    lgSeipD := by decide +kernel
    lgMeipD := by decide +kernel
    lgHead := by decide +kernel
    lgToSeip := by decide +kernel
    lgBranch00 := ldBranchNfHolds _ _ _ (by intro x; ax_epi_ledger_krfl)
    lgBranch01 := ldBranchNfHolds _ _ _ (by intro x; ax_epi_ledger_krfl)
    lgBranch10 := ldBranchNfHolds _ _ _ (by intro x; ax_epi_ledger_krfl)
    lgBranch11 := ldBranchNfHolds _ _ _ (by intro x; ax_epi_ledger_krfl) }

/-- The `epure`-level statement: along the path of `riscvStep false` from `tAt pcLd` — `toPin` to
the `sig_meip` read (answered `v'`), `toPin` to the `sig_seip` read (answered `v`), `erd` to the
fetch, fetch answered with the instruction bytes, `erd` to the data load — for EVERY loaded word
`x`, a successful post-load `epure` run ends with `x1 = x` (and PC = pcLd + 2). -/
theorem cldspPostLoadX1 (km : RegisterType Register.sig_meip → SailM Unit) (t0 : ExecSt)
    (v' : BitVec 1) (k0 : RegisterType Register.sig_seip → SailM Unit) (t1 : ExecSt)
    (v : BitVec 1) (n va : Nat) (req : Mem_read_request n va Arch.pa Arch.translation Arch.arch_ak)
    (KKf : Result (BitVec (8 * n) × Option Bool) Arch.abort → SailM Unit) (t2 : ExecSt)
    (nl val : Nat) (reql : Mem_read_request nl val Arch.pa Arch.translation Arch.arch_ak)
    (KK : Result (BitVec (8 * nl) × Option Bool) Arch.abort → SailM Unit) (tl : ExecSt)
    (x : BitVec (8 * nl)) (sEnd : ExecSt)
    (Hts : AxEpiLedger.toPin (riscvStep false) (tAt pcLd)
      = some (.impure (.ok (.regRead Register.sig_meip)) km, t0))
    (Hts1 : AxEpiLedger.toPin (km v') t0
      = some (.impure (.ok (.regRead Register.sig_seip)) k0, t1))
    (He1 : erd AxEpiProbe.drNopin DwAll (k0 v) t1
      = some (.impure (.ok (.memRead n va req)) KKf, t2))
    (He2 : erd AxEpiProbe.drNopin DwAll (KKf (.Ok (wordOfBytes n AxEpiLedger.ldVs, none))) t2
      = some (.impure (.ok (.memRead nl val reql)) KK, tl))
    (Hep : epure DPost (KK (.Ok (x, none))) tl = some ((), sEnd)) :
    (sEnd.regs .x1).toNat = x.toNat ∧ (sEnd.regs .PC).toNat = pcLd + 2 := by
  have Hb := ldLedgerBranch _ _ _ _ _ _ _ _ km t0 v' k0 t1 epiLedgerCldspX1 Hts Hts1 v
  unfold ldBranchOk at Hb
  rw [He1] at Hb
  simp only [ldFetchOk] at Hb
  obtain ⟨-, -, -, -, Hb⟩ := Hb
  rw [He2] at Hb
  simp only [ldLoadOk] at Hb
  obtain ⟨-, -, -, -, -, Hb⟩ := Hb
  have Hx := Hb x
  rw [Hep] at Hx
  obtain ⟨Hpc, Hx1⟩ := (Hx : ldPostX1 (x.toNat : Int) sEnd.regs)
  exact ⟨by exact_mod_cast Hx1, Hpc⟩

end Weak
