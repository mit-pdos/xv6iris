/-
Weak: **THE INSTRUCTION RULE `wpAinstr`** (AxSL tier): the flat SC state at a graph position and
its exec-level certificate, administrative batching under the axiomatic WP, the explicit target
ledger `AxInstrTargets`, the owned-event steps, the fetch (an admin skip), the instruction rule
and a non-vacuity graph.

Rocq: `iris/AxInstr.v` @ xxvzwolszwmp.

## The Rocq header, in substance

Design `claude-notes/design/weak-memory-lb-axsl.md` §0.5 "The step case", §1-L3.  One whole
instruction (fetch + its memory events + admin nodes) discharged from an EXEC-LEVEL certificate
(`WeakLeafLd8`/`WeakLeafSd8`-style), so the SC-tier leaf lemmas drive the axiomatic WP
(`AxWp.wp`) without re-verifying Sail nodes one `pnodeStep` at a time.  The file has NO
admitted proof: every former gap is a field of the explicit class `AxInstrTargets` that the
affected lemmas take as a premise.
  §1  `ainstrFlat`/`acert` — PURE.  The flat SC machine state at a graph position (registers,
      device, and memory built from `AxBridge.flatMemBytes` over an explicit list of
      `(base, width)` WINDOWS — the instruction's own finite footprint, `WeakInstr.wstepCert`'s
      move), and the exec-level certificate mirroring the two-successor (`tick`) shape.
  §2  `arunAdmin`/`awpAdminBatch` — admin batching, under one named simplification: the PLIC
      wire's interleaving is an explicit hypothesis (`arunWireStable`), not derived.
  §2.5 `AxInstrTargets` — THE LEDGER (five targets: `tOwnedRead`/`tOwnedWrite`, discharged by
      AxProt; `tAinstr`, `tAinstrLd8`, `tAinstrSd8`, discharged by track F + AxProt).
  §3/§4 `awpOwnedRead`/`awpOwnedWrite` — the owned memory-event steps, projections of the
      targets (the token is an ordinary ambient resource `Rtok`).
  §5  `awpFetch` — the fetch step.
  §6  `wpAinstr` (general, from `tAinstr`) and `wpAinstrLd8`/`wpAinstrSd8`.
  §7  NON-VACUITY: a hand-built 1-hart graph where a load is forwarded from the hart's own
      store, gmo-reordered (the L2 case (ii) FORWARDING shape), showing the PURE hypotheses of
      `wpAinstrSd8`/`wpAinstrLd8` are satisfiable together; depends on no target.

## Deviations from Rocq

1. NAMES: the tree's camelCase (map below).  No name of this file is in
   `notes/weak-port-dupnames.json`.  Lean-only helpers (file-qualified): `AxInstr.lbAdminWlWr`,
   `AxInstr.lbAdminWlFence` (an admin label is neither a write nor a fence), and (Q8)
   `AxInstr.aadminExclPin`, `AxInstr.aadminExclPinOf`, `AxInstr.awpAdminStepPin`.  The §7 module is
   the namespace `AxInstr.NonVacuity` (Rocq `Module NonVacuity`).
2. O2 STAGE C (`notes/weak-port-o2-stageC.md` §D, track F; `AxOpsem` deviation 2, `AxWp`
   deviation 10) — THE FETCH IS AN ADMINISTRATIVE LABEL, not a row read.
   - `astep_prog row T img` ↦ `AxOpsem.astepProg row` (the oracle parameters `T`/`img`, Rocq's
     `ax_text`/`gx_img` arguments, are gone): `aadminRel`'s `∃ row T img l` is `∃ row l`,
     `aadminExcl`'s second clause quantifies `row l s''`, `tOwnedWrite`/`awpOwnedWrite` take
     `AxOpsem.astepProg (AxOpsem.grow GD i) s l s'`.  `astepProgAdminK` has no `AStep_fetch`
     case (there is no such constructor).
   - `awpFetch` IS THE ADMIN SKIP.  Rocq: `awp_owned_read` at `Rtok := True` over an
     `aread_step` (the fetch was a row `LLoad` item answered by the oracle), hence dependent on
     `AxInstrTargets` through `t_owned_read`.  Lean: a fetch is an `AStepAdmin` step at
     `AxOpsem.lbAdminAx true (LIFetch base tvs)` that keeps the row position; `awpFetch` takes that step
     `AxOpsem.astepProg (AxOpsem.grow GD i) s (.LIFetch base tvs) a`, the wire hypothesis of
     `awpAdminStep`, and the PINNED exclusivity (owner Q8): `∀ GD', rvwmoCatConsistent GD' →
     gconstInterp GD' ⊢ ⌜AxInstr.aadminExclPin GD'.gdG.gxImg s a⌝` — only fetches of the
     graph's boot-image bytes (`WeakAxRealize.fetchPin`, the premise `AxWp.wpPreStepDef`'s step
     clause now offers) must land at `a`.  (Before Q8 it took `aadminExcl s a`, which quantifies
     fetches of ANY bytes and so is unsatisfiable at a real fetch node.)  It is the Lean-only
     `AxInstr.awpAdminStepPin` instantiated and needs NO target (it moved from §3-5's targets
     section to its own).  There is no value premise: the fetched bytes are not a graph value.
   - §7's rows lose their two fetch items: Rocq `[F0; W; F1; R]` at positions 0..3 with gmo
     `[F0; F1; R; W]` ↦ `[W; R]` at positions 0..1 with gmo `[R; W]`; the load's timestamp tag
     (the store's 1-based gmo write index, `1`) is unchanged.  `sliceForwarded`'s
     no-intervening-write obligation is now an empty interval (`omega`), where Rocq excluded the
     fetch at position 2 by `gwa_b`.  `WeakLitmus.b0` (only in the fetch items) is unused.
3. STATE (`Weak.Exec` deviation 1): Rocq `RiscvLang.mstate` (`MState rs mem dv`, `sregs`,
   `mem : gmap`, `mdev`) ↦ `ExecSt` (`regs : RegFile`, `mem : BMap`, `dev : DevStates`);
   `regstate` ↦ `RegFile`; `dev_state` ↦ `DevStates` (the exec state's device, not
   `AxOpsem`'s `Efab`); `RiscvExec.exec (riscv_step b)` ↦ `exec (riscvStep b)`; `Some (tt, t)`
   ↦ `some ((), t)`.  The finite map `gmap Arch.pa (bv 8)` is the partial function `BMap`, so
   `ainstrWin` is `fun a => get? (bytesMap base bs) a` (`WeakLang.bytesMap`) or `none`, and the
   left-biased map union `∪` of `ainstrMem` is pointwise `Option.or`; `mem t !! addr` ↦
   `t.mem addr`; `pa_z` ↦ `paZ`.
4. VOCABULARY: `agent` ↦ `Agent`; `Z` ↦ `Int`; `bv 8` ↦ `BitVec 8`; `mword 5` ↦ `BitVec 5`,
   `uint rd ≠ 0` ↦ `rd.toNat ≠ 0`; `wbytes` ↦ `WeakInterpProj.wbytes`; `gd_g`/`gd_deps` ↦
   `.gdG`/`.gdDeps`; `GDExec` ↦ the structure literal; `length v` ↦ `v.length`; `rtc` ↦
   `MachCSL.rtc` (tail-built: `awpAdminBatch` inducts with `head_induction_on`).
5. IRIS (`AxWp` deviations 6/7): `invGS_gen HasNoLc Σ` ↦ `[InvGS_gen hlc GF]` for any `hlc`;
   `WP s @ st; i {{ Φ }}` ↦ `AxWp.wp st i s Φ`; a wand-chain statement `A -∗ B -∗ C` is
   `⊢ A -∗ B -∗ C`.  `AxInstrTargets` is a `Prop`-valued class over `hlc GF`, used as
   `[AxInstrTargets hlc GF]` (Rocq `` `{!AxInstrTargets} ``).  Rocq's UNPARENTHESISED
   `Rtok ==∗ Rtok' -∗ Rtok -∗ … -∗ WP s` in `t_owned_write`/`awp_owned_write` parses as
   `Rtok ==∗ (Rtok' -∗ Rtok -∗ … -∗ WP s)`; the Lean statement keeps that parse literally
   (`⊢ Rtok -∗ |==> (Rtok' -∗ Rtok -∗ … )`).  `tAinstrSd8`'s parenthesised `(Rtok ==∗ Rtok')`
   is kept as is.  `slice_token_write_then_read`'s `axlogG Σ hent` ↦ `[AxlogG GF Hent]`.
6. Unused section arguments stay in the signatures (`arunAdmin`'s `GD i`, `ea` of the ld8/sd8
   shapes), as in Rocq; `arunAdmin`'s are named `_GD`/`_i`.
7. PROOFS: §7's `vm_compute`/`vmr` steps are `decide +kernel` on the boolean twins
   (`catConsistentBSound`, `gpoBSpec`, `gwbBSpec`, `grbBSpec`, `gmoLtBSpec`), as
   `AxToken.fwdDemoWriteThenRead`.
8. IMPORTS: Rocq imports `WeakLeafLd8`/`WeakLeafSd8` but uses none of their names (they are
   cited in prose only); they are not imported here (the file is a hub).

**Rocq → Lean name map.**  `ainstr_win` `ainstrWin`, `ainstr_mem` `ainstrMem`, `ainstr_flat`
`ainstrFlat`, `acert` `acert`, `acert_mono` `acertMono`, `astep_prog_admin_k`
`astepProgAdminK`, `aadmin_excl` `aadminExcl`, `aadmin_rel` `aadminRel`, `arun_admin`
`arunAdmin`, `arun_wire_stable` `arunWireStable`, `awp_admin_step` `awpAdminStep`,
`awp_admin_batch` `awpAdminBatch`, `ainstr_agree` `ainstrAgree`, `AxInstrTargets`
`AxInstrTargets` (fields `t_owned_read` `tOwnedRead`, `t_owned_write` `tOwnedWrite`,
`t_ainstr` `tAinstr`, `t_ainstr_ld8` `tAinstrLd8`, `t_ainstr_sd8` `tAinstrSd8`),
`awp_owned_read` `awpOwnedRead`, `awp_owned_write` `awpOwnedWrite`, `awp_fetch` `awpFetch`,
`wp_ainstr` `wpAinstr`, `wp_ainstr_ld8` `wpAinstrLd8`, `wp_ainstr_sd8` `wpAinstrSd8`;
`NonVacuity.slice` `AxInstr.NonVacuity.slice`, `slice_cat` `sliceCat`, `slice_forwarded`
`sliceForwarded`, `slice_flat_mem_at_load` `sliceFlatMemAtLoad`, `slice_graph_data_at_store`
`sliceGraphDataAtStore`, `slice_token_write_then_read` `sliceTokenWriteThenRead`.

**Dropped:** none (the §7/§8 `Print Assumptions` lines have no Lean twin; the lint's axiom check
covers them).
-/
import Weak.AxWp2
import Weak.AxBridge
import Weak.AxToken
import Weak.Exec
import Weak.WeakLang
import Weak.WeakInterpProj

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std Iris.Std.PartialMap MachCSL MachCSL.Stdpp
open Lbl

/-! # 1. `ainstrFlat` / `acert` — the flat SC state and its certificate -/

/-- The flat memory of one window `(base, n)` at graph position `e`: the bytes
`AxBridge.flatMemBytes` gives, or nothing if some byte has no flat value. -/
def ainstrWin (G : Gexec) (i : Nat) (e : Geid) (base : Int) (n : Nat) : BMap :=
  fun a =>
    match flatMemBytes G i e base n with
    | some bs => get? (bytesMap base bs) a
    | none => none

/-- The union (left-biased) of the windows' flat memories. -/
def ainstrMem (G : Gexec) (i : Nat) (e : Geid) : List (Int × Nat) → BMap
  | [] => fun _ => none
  | (base, n) :: ws => fun a => (ainstrWin G i e base n a).or (ainstrMem G i e ws a)

/-- The flat SC machine state at graph position `e` of hart `i`. -/
def ainstrFlat (GD : Gdexec) (i : Nat) (e : Geid) (rs : RegFile) (dv : DevStates)
    (windows : List (Int × Nat)) : ExecSt :=
  ⟨rs, ainstrMem GD.gdG i e windows, dv⟩

/-- THE INSTRUCTION CERTIFICATE: both tick values succeed and land in `Q`. -/
def acert (GD : Gdexec) (i : Nat) (e : Geid) (rs : RegFile) (dv : DevStates)
    (windows : List (Int × Nat)) (Q : ExecSt → Prop) : Prop :=
  (∃ t, exec (riscvStep false) (ainstrFlat GD i e rs dv windows) = some ((), t) ∧ Q t) ∧
  (∃ t, exec (riscvStep true) (ainstrFlat GD i e rs dv windows) = some ((), t) ∧ Q t)

theorem acertMono (GD : Gdexec) (i : Nat) (e : Geid) (rs : RegFile) (dv : DevStates)
    (windows : List (Int × Nat)) (Q Q' : ExecSt → Prop) :
    (∀ t, Q t → Q' t) → acert GD i e rs dv windows Q → acert GD i e rs dv windows Q' := by
  rintro HQ ⟨⟨t0, Ht0, HQ0⟩, ⟨t1, Ht1, HQ1⟩⟩
  exact ⟨⟨t0, Ht0, HQ _ HQ0⟩, ⟨t1, Ht1, HQ _ HQ1⟩⟩

/-! # 2. Silent/admin batching -/

/-- An administrative label is not a write. -/
theorem AxInstr.lbAdminWlWr (l : Wlabel) : AxOpsem.lbAdminAx true l → (wlWr l).isSome = false := by
  cases l <;> simp [AxOpsem.lbAdminAx, wlWr]

/-- An administrative label is not a fence. -/
theorem AxInstr.lbAdminWlFence (l : Wlabel) : AxOpsem.lbAdminAx true l → (wlFence l).isSome = false := by
  cases l <;> simp [AxOpsem.lbAdminAx, wlFence]

/-- An admin-labelled `astepProg` step preserves the row position. -/
theorem astepProgAdminK (row : List Lbl) (s : Athread) (l : Wlabel) (s' : Athread) :
    AxOpsem.astepProg row s l s' → AxOpsem.lbAdminAx true l → s'.atK = s.atK := by
  intro h hadm
  cases h with
  | AStepAdmin => rfl
  | AStepWrite _ _ _ _ _ _ _ _ hwr =>
    rw [AxInstr.lbAdminWlWr _ hadm] at hwr
    cases hwr
  | AStepFence _ _ _ _ _ _ _ _ hf =>
    rw [AxInstr.lbAdminWlFence _ hadm] at hf
    cases hf

/-- The two facts a concrete admin step must supply: no read is available, and every other
program step lands at `a` with no write data. -/
def aadminExcl (s a : Athread) : Prop :=
  (∀ row id K, ¬ areadStep row s id K) ∧
  (∀ row l s'', AxOpsem.astepProg row s l s'' → s'' = a ∧ wlWdata l = none)

def aadminRel (s a : Athread) : Prop :=
  (∃ row l, AxOpsem.astepProg row s l a ∧ AxOpsem.lbAdminAx true l) ∧ aadminExcl s a

def arunAdmin (_GD : Gdexec) (_i : Agent) : Athread → Athread → Prop :=
  rtc aadminRel

section adminBatch
variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF] [Axpol]

/-- THE WIRE SIMPLIFICATION: WP already holds at every wire-successor of every state the admin
run passes through (an explicit hypothesis the caller supplies once per run). -/
def arunWireStable (GD : Gdexec) (i : Agent) (st : Stuckness) (Φ : Athread → IProp GF)
    (s0 : Athread) : IProp GF :=
  iprop(□ ∀ s1 s2, ⌜arunAdmin GD i s0 s1 ∧ awire s1 s2⌝ -∗ AxWp.wp st i s2 Φ)

theorem awpAdminStep (GD : Gdexec) (i : Agent) (s a : Athread) (Φ : Athread → IProp GF)
    (st : Stuckness) :
    aadminRel s a →
    ⊢ (□ ∀ s'', ⌜awire s s''⌝ -∗ AxWp.wp st i s'' Φ) -∗
      AxWp.wp st i a Φ -∗ AxWp.wp st i s Φ := by
  rintro ⟨⟨row, l, Hstep, Hladm⟩, Hexclrd, Hexclwr⟩
  obtain ⟨p, k⟩ := s
  obtain ⟨p', k'⟩ := a
  have Hk : k' = k := astepProgAdminK row _ l _ Hstep Hladm
  subst Hk
  obtain ⟨d, d', Hp⟩ := astepProgPstep _ _ _ _ Hstep
  have Hred : ∀ GD', reducibleGd GD' i ⟨p, k'⟩ := fun GD' =>
    ⟨[], ⟨p', k'⟩, .inl ⟨l, .AStepAdmin p k' d l p' d' Hladm Hp⟩⟩
  iintro #Hwire Ha
  iapply (wpProgressIntro st i ⟨p, k'⟩ Φ Hred)
  unfold wpPreStepDef
  iintro %GD' %ls ⟨%_Hcons, #_Hgc, Hloc⟩
  isplit
  · -- the read: vacuous
    iintro %id %K %Hrd
    exact (Hexclrd _ id K Hrd).elim
  isplit
  · -- every other program step: lands at `a`, no write data
    iintro %l0 %s'' %Hstep0 %_
    obtain ⟨rfl, Hwd⟩ := Hexclwr _ _ _ Hstep0
    rw [Hwd]
    unfold wpSkipStep
    iintro %na Hna
    imodintro
    inext
    imodintro
    iexists ls
    iframe Hna Hloc
    iexact Ha
  · -- the wire, from `s` itself
    iintro %s'' %Hw
    have Hkw : s''.atK = k' := Hw.1
    rw [Hkw]
    unfold wpSkipStep
    iintro %na Hna
    imodintro
    inext
    imodintro
    iexists ls
    iframe Hna Hloc
    iapply Hwire
    ipureintro
    exact Hw

theorem awpAdminBatch (GD : Gdexec) (i : Agent) :
    ∀ s s' : Athread, arunAdmin GD i s s' →
    ∀ (Φ : Athread → IProp GF) (st : Stuckness),
      ⊢ arunWireStable GD i st Φ s -∗ AxWp.wp st i s' Φ -∗ AxWp.wp st i s Φ := by
  intro s s' Hrun
  induction Hrun using FromMathlib.Relation.ReflTransGen.head_induction_on with
  | refl =>
    intro Φ st
    iintro _ H
    iexact H
  | head Hstep Hrest IH =>
    intro Φ st
    unfold arunWireStable
    iintro #Hwire H
    iapply (awpAdminStep GD i _ _ Φ st Hstep) $$ [] [H]
    · imodintro
      iintro %s'' %Hw
      iapply Hwire
      ipureintro
      exact ⟨rtc_refl _, Hw⟩
    · iapply (IH Φ st) $$ [] H
      unfold arunWireStable
      imodintro
      iintro %s1 %s2 %Hr
      iapply Hwire
      ipureintro
      exact ⟨rtc_l Hstep Hr.1, Hr.2⟩

end adminBatch

/-! # 2.5. The honest ledger: `AxInstrTargets`

| target        | discharged by                                                          |
|---------------|------------------------------------------------------------------------|
| `tOwnedRead`  | AxProt (the protocol `obStInterp` over AxToken's history ghost)        |
| `tOwnedWrite` | AxProt, dual (write-side redemption, `ownedWriteRule` re-tying)        |
| `tAinstr`     | track F (the `acert` → Sail fetch/decode → `exec (riscvStep _)` bridge) |
|               | + AxProt (the owned-event shell at each memory event)                  |
| `tAinstrLd8`  | track F (`WeakLeafLd8`'s certificate) + AxProt (one owned read)        |
| `tAinstrSd8`  | track F (`WeakLeafSd8`'s certificate) + AxProt (one owned write)       |
-/

/-- The successor agreement item 6's leaves need: registers, device, and memory agreeing with
`flatMem` at the successor's position. -/
def ainstrAgree (GD : Gdexec) (i : Agent) (a : Athread) (dv : DevStates) (t : ExecSt) : Prop :=
  (∀ cpu m rs fn ib, a.atP = .PHart cpu m rs fn ib → rs = t.regs) ∧
  t.dev = dv ∧
  (∀ (addr : PAddr) (v : BitVec 8), t.mem addr = some v →
     flatMem GD.gdG i (i, a.atK) (paZ addr) = some v)

/-- THE LEDGER: the five explicit targets. -/
class AxInstrTargets (hlc : HasLC) (GF : BundledGFunctors) [InvGS_gen hlc GF] [AxirisG GF]
    [Axpol] : Prop where
  /-- The old `awpOwnedRead` statement (§3). -/
  tOwnedRead : ∀ (GD : Gdexec) (i : Agent) (s : Athread) (id : AidentT) (v : List (BitVec 8))
      (K : List (BitVec 8) → Athread) (Φ : Athread → IProp GF) (st : Stuckness)
      (Rtok : IProp GF),
    areadStep (AxOpsem.grow GD i) s id K →
    v.length = aidentN id →
    (∀ v', graphValue GD (i, s.atK) = some v' → v' = v) →
    ⊢ Rtok -∗ (Rtok -∗ AxWp.wp st i (K v) Φ) -∗ AxWp.wp st i s Φ
  /-- The old `awpOwnedWrite` statement (§4), Rocq's parse (deviation 5). -/
  tOwnedWrite : ∀ (GD : Gdexec) (i : Agent) (s s' : Athread) (l : Wlabel)
      (data : List (BitVec 8)) (Φ : Athread → IProp GF) (st : Stuckness)
      (Rtok Rtok' : IProp GF),
    AxOpsem.astepProg (AxOpsem.grow GD i) s l s' →
    wlWdata l = some data →
    graphData GD (i, s.atK) = some data →
    ⊢ Rtok -∗ |==> (Rtok' -∗ Rtok -∗ (Rtok' -∗ AxWp.wp st i s' Φ) -∗ AxWp.wp st i s Φ)
  /-- The old general `wpAinstr` statement (§6). -/
  tAinstr : ∀ (GD : Gdexec) (i : Agent) (s s0 : Athread) (rs : RegFile) (dv : DevStates)
      (windows : List (Int × Nat)) (Φ : Athread → IProp GF) (st : Stuckness)
      (Rtok : IProp GF),
    acert GD i (i, s.atK) rs dv windows
      (fun t => ∀ a, arunAdmin GD i s0 a → ainstrAgree GD i a dv t) →
    arunAdmin GD i s s0 →
    ⊢ arunWireStable GD i st Φ s -∗
      Rtok -∗
      (∀ a t, ⌜ainstrAgree GD i a dv t⌝ -∗ Rtok -∗ AxWp.wp st i a Φ) -∗
      AxWp.wp st i s Φ
  /-- The old `wpAinstrLd8` statement (§6). -/
  tAinstrLd8 : ∀ (GD : Gdexec) (i : Agent) (s : Athread) (rd : BitVec 5) (ea : Int)
      (v : BitVec 64) (Φ : Athread → IProp GF) (st : Stuckness) (Rtok : IProp GF),
    rd.toNat ≠ 0 →
    (∀ v', graphValue GD (i, s.atK) = some v' → v' = WeakInterpProj.wbytes 8 v) →
    ⊢ arunWireStable GD i st Φ s -∗
      Rtok -∗
      (∀ a, ⌜True⌝ -∗ Rtok -∗ AxWp.wp st i a Φ) -∗
      AxWp.wp st i s Φ
  /-- The old `wpAinstrSd8` statement (§6). -/
  tAinstrSd8 : ∀ (GD : Gdexec) (i : Agent) (s : Athread) (ea : Int) (vs : BitVec 64)
      (Φ : Athread → IProp GF) (st : Stuckness) (Rtok Rtok' : IProp GF),
    (∀ data, graphData GD (i, s.atK) = some data → data = WeakInterpProj.wbytes 8 vs) →
    ⊢ arunWireStable GD i st Φ s -∗
      (Rtok ==∗ Rtok') -∗
      Rtok -∗
      (∀ a, ⌜True⌝ -∗ Rtok' -∗ AxWp.wp st i a Φ) -∗
      AxWp.wp st i s Φ

/-! # 3-4. The owned memory-event steps (projections of the targets) -/

section ownedStep
variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF] [Axpol]
  [AxInstrTargets hlc GF]

/-- ITEM 3, THE OWNED-READ EVENT STEP. -/
theorem awpOwnedRead (GD : Gdexec) (i : Agent) (s : Athread) (id : AidentT)
    (v : List (BitVec 8)) (K : List (BitVec 8) → Athread) (Φ : Athread → IProp GF)
    (st : Stuckness) (Rtok : IProp GF) :
    areadStep (AxOpsem.grow GD i) s id K →
    v.length = aidentN id →
    (∀ v', graphValue GD (i, s.atK) = some v' → v' = v) →
    ⊢ Rtok -∗ (Rtok -∗ AxWp.wp st i (K v) Φ) -∗ AxWp.wp st i s Φ :=
  AxInstrTargets.tOwnedRead GD i s id v K Φ st Rtok

/-- ITEM 4, THE OWNED-WRITE EVENT STEP (Rocq's parse, deviation 5). -/
theorem awpOwnedWrite (GD : Gdexec) (i : Agent) (s s' : Athread) (l : Wlabel)
    (data : List (BitVec 8)) (Φ : Athread → IProp GF) (st : Stuckness)
    (Rtok Rtok' : IProp GF) :
    AxOpsem.astepProg (AxOpsem.grow GD i) s l s' →
    wlWdata l = some data →
    graphData GD (i, s.atK) = some data →
    ⊢ Rtok -∗ |==> (Rtok' -∗ Rtok -∗ (Rtok' -∗ AxWp.wp st i s' Φ) -∗ AxWp.wp st i s Φ) :=
  AxInstrTargets.tOwnedWrite GD i s s' l data Φ st Rtok Rtok'

end ownedStep

/-! # 5. The fetch step: the admin skip (O2 Stage C, deviation 2) -/

section fetchStep
variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF] [Axpol]

/-- (Lean-only, Q8) `aadminExcl` against the WP's PINNED step clause: no read, and every
program step whose label is pinned to `img` lands at `a` with no write data.  At a fetch node
`aadminExcl` itself is unsatisfiable (a fetch of ANY bytes is a program step, and the successor
depends on the bytes); the pinned form only speaks of the image's bytes. -/
def AxInstr.aadminExclPin (img : Image) (s a : Athread) : Prop :=
  (∀ row id K, ¬ areadStep row s id K) ∧
  (∀ row l s'', AxOpsem.astepProg row s l s'' → WeakAxRealize.fetchPin img l →
     s'' = a ∧ wlWdata l = none)

theorem AxInstr.aadminExclPinOf (img : Image) (s a : Athread) :
    aadminExcl s a → AxInstr.aadminExclPin img s a :=
  fun ⟨h1, h2⟩ => ⟨h1, fun row l s'' h _ => h2 row l s'' h⟩

/-- (Lean-only, Q8) `awpAdminStep` with the exclusivity read off the graph's image (through
`gconstInterp`, as Rocq's `fetch_gd_ok`-style premises). -/
theorem AxInstr.awpAdminStepPin (i : Agent) (s a : Athread) (Φ : Athread → IProp GF)
    (st : Stuckness) (row : List Lbl) (l : Wlabel) :
    AxOpsem.astepProg row s l a → AxOpsem.lbAdminAx true l →
    (∀ GD', rvwmoCatConsistent GD' →
      AxirisG.gconstInterp (GF := GF) GD' ⊢ ⌜AxInstr.aadminExclPin GD'.gdG.gxImg s a⌝) →
    ⊢ (□ ∀ s'', ⌜awire s s''⌝ -∗ AxWp.wp st i s'' Φ) -∗
      AxWp.wp st i a Φ -∗ AxWp.wp st i s Φ := by
  intro Hstep Hladm Hexcl
  obtain ⟨p, k⟩ := s
  obtain ⟨p', k'⟩ := a
  have Hk : k' = k := astepProgAdminK row _ l _ Hstep Hladm
  subst Hk
  obtain ⟨d, d', Hp⟩ := astepProgPstep _ _ _ _ Hstep
  have Hred : ∀ GD', reducibleGd GD' i ⟨p, k'⟩ := fun GD' =>
    ⟨[], ⟨p', k'⟩, .inl ⟨l, .AStepAdmin p k' d l p' d' Hladm Hp⟩⟩
  iintro #Hwire Ha
  iapply (wpProgressIntro st i ⟨p, k'⟩ Φ Hred)
  unfold wpPreStepDef
  iintro %GD' %ls ⟨%Hcons, #Hgc, Hloc⟩
  ihave Hx := (Hexcl GD' Hcons) $$ Hgc
  icases Hx with %Hx
  isplit
  · -- the read: vacuous
    iintro %id %K %Hrd
    exact (Hx.1 _ id K Hrd).elim
  isplit
  · -- every other PINNED program step: lands at `a`, no write data
    iintro %l0 %s'' %Hstep0 %Hpin
    obtain ⟨rfl, Hwd⟩ := Hx.2 _ _ _ Hstep0 Hpin
    rw [Hwd]
    unfold wpSkipStep
    iintro %na Hna
    imodintro
    inext
    imodintro
    iexists ls
    iframe Hna Hloc
    iexact Ha
  · -- the wire, from `s` itself
    iintro %s'' %Hw
    have Hkw : s''.atK = k' := Hw.1
    rw [Hkw]
    unfold wpSkipStep
    iintro %na Hna
    imodintro
    inext
    imodintro
    iexists ls
    iframe Hna Hloc
    iapply Hwire
    ipureintro
    exact Hw

/-- ITEM 5, THE FETCH STEP.  The fetch has no protocol content and no graph event: it is an
`AStepAdmin` step at `AxOpsem.lbAdminAx true (LIFetch base tvs)` keeping the row position, so the WP
passes straight to the post-fetch state.  The exclusivity is the PINNED one (Q8): only the
fetches of the image's bytes must land at `a`. -/
theorem awpFetch (GD : Gdexec) (i : Agent) (s a : Athread) (base : Int)
    (tvs : List (Nat × BitVec 8)) (Φ : Athread → IProp GF) (st : Stuckness) :
    AxOpsem.astepProg (AxOpsem.grow GD i) s (.LIFetch base tvs) a →
    (∀ GD', rvwmoCatConsistent GD' →
      AxirisG.gconstInterp (GF := GF) GD' ⊢ ⌜AxInstr.aadminExclPin GD'.gdG.gxImg s a⌝) →
    ⊢ (□ ∀ s'', ⌜awire s s''⌝ -∗ AxWp.wp st i s'' Φ) -∗
      AxWp.wp st i a Φ -∗ AxWp.wp st i s Φ := by
  intro Hstep Hexcl
  exact AxInstr.awpAdminStepPin i s a Φ st _ _ Hstep rfl Hexcl

end fetchStep

/-! # 6. The instruction rule -/

section wpAinstr
variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF] [Axpol]
  [AxInstrTargets hlc GF]

/-- THE GENERAL TARGET, driven by `tAinstr`. -/
theorem wpAinstr (GD : Gdexec) (i : Agent) (s s0 : Athread) (rs : RegFile) (dv : DevStates)
    (windows : List (Int × Nat)) (Φ : Athread → IProp GF) (st : Stuckness) (Rtok : IProp GF) :
    acert GD i (i, s.atK) rs dv windows
      (fun t => ∀ a, arunAdmin GD i s0 a → ainstrAgree GD i a dv t) →
    arunAdmin GD i s s0 →
    ⊢ arunWireStable GD i st Φ s -∗
      Rtok -∗
      (∀ a t, ⌜ainstrAgree GD i a dv t⌝ -∗ Rtok -∗ AxWp.wp st i a Φ) -∗
      AxWp.wp st i s Φ :=
  AxInstrTargets.tAinstr GD i s s0 rs dv windows Φ st Rtok

/-- The LOAD-8 shape, driven by `tAinstrLd8`. -/
theorem wpAinstrLd8 (GD : Gdexec) (i : Agent) (s : Athread) (rd : BitVec 5) (ea : Int)
    (v : BitVec 64) (Φ : Athread → IProp GF) (st : Stuckness) (Rtok : IProp GF) :
    rd.toNat ≠ 0 →
    (∀ v', graphValue GD (i, s.atK) = some v' → v' = WeakInterpProj.wbytes 8 v) →
    ⊢ arunWireStable GD i st Φ s -∗
      Rtok -∗
      (∀ a, ⌜True⌝ -∗ Rtok -∗ AxWp.wp st i a Φ) -∗
      AxWp.wp st i s Φ :=
  AxInstrTargets.tAinstrLd8 GD i s rd ea v Φ st Rtok

/-- The STORE-8 shape, driven by `tAinstrSd8`. -/
theorem wpAinstrSd8 (GD : Gdexec) (i : Agent) (s : Athread) (ea : Int) (vs : BitVec 64)
    (Φ : Athread → IProp GF) (st : Stuckness) (Rtok Rtok' : IProp GF) :
    (∀ data, graphData GD (i, s.atK) = some data → data = WeakInterpProj.wbytes 8 vs) →
    ⊢ arunWireStable GD i st Φ s -∗
      (Rtok ==∗ Rtok') -∗
      Rtok -∗
      (∀ a, ⌜True⌝ -∗ Rtok' -∗ AxWp.wp st i a Φ) -∗
      AxWp.wp st i s Φ :=
  AxInstrTargets.tAinstrSd8 GD i s ea vs Φ st Rtok Rtok'

end wpAinstr

/-! # 7. Non-vacuity

A hand-built 1-hart graph: rows `[W a; R a]` (positions 0..1; Rocq's two fetch items are gone,
deviation 2), gmo `[R; W]` — `R` gmo-BEFORE `W` — so the load is served by hart 0's OWN
forwarded write (L2 case (ii)). -/

namespace AxInstr.NonVacuity

/-- Row: `W` (store `b1` at byte 0), `R` (load byte 0, forwarded from `W`); gmo `[R; W]`. -/
def slice : Gdexec :=
  AxGraphWit.mkgd
    [[LStore false 0 [b1] .WCplain, LLoad false 0 [1] [b1]]]
    [(0, 1), (0, 0)]
    []

theorem sliceCat : rvwmoCatConsistent slice :=
  catConsistentBSound _ (by decide +kernel)

/-- The load `R` (position 1) is forwarded from the store `W` (position 0). -/
theorem sliceForwarded :
    grfAt slice.gdG 0 (0, 0) (0, 1) ∧
    ∀ t' v', greadsByte slice.gdG (0, 1) 0 t' v' → v' = b1 := by
  refine ownedReadRuleFwd slice 0 (0, 1) (0, 0) b1 1 b1 sliceCat
    ((gpoBSpec _ _ _).1 (by decide +kernel))
    ((gwbBSpec _ _ _ _).1 (by decide +kernel))
    ((grbBSpec _ _ _ _ _).1 (by decide +kernel)) ?_ ?_
  · intro h
    have h' := (gmoLtBSpec _ _ _).2 h
    have hf : gmoLtB slice.gdG (0, 0) (0, 1) = false := by decide +kernel
    rw [hf] at h'
    cases h'
  · rintro w' v' _ ⟨_, hlt, _⟩ ⟨_, hlt', _⟩
    dsimp only at hlt hlt'
    omega

/-- The `flatMem` agreement `wpAinstrLd8`'s pure premise needs at `R`. -/
theorem sliceFlatMemAtLoad : flatMem slice.gdG 0 (0, 1) 0 = some b1 := by decide +kernel

/-- The write-side pure premise `wpAinstrSd8` needs at `W`. -/
theorem sliceGraphDataAtStore :
    graphData { gdG := slice.gdG, gdDeps := slice.gdDeps } (0, 0) = some [b1] := by
  decide +kernel

/-- Allocating a token and driving `ownedWriteRule` then `ownedReadRuleFwd` on this graph. -/
theorem sliceTokenWriteThenRead {GF : BundledGFunctors} [AxlogG GF Hent] :
    ⊢@{IProp GF} |==> ∃ γ, histAuth γ 0 1 [((0, 0), b1)] ∗
      ⌜grfAt slice.gdG 0 (0, 0) (0, 1) ∧
        ∀ t v, greadsByte slice.gdG (0, 1) 0 t v → v = b1⌝ := by
  have hw := fun γ => ownedWriteRule (GF := GF) γ 0 [] (0, 0) b1
  simp only [List.nil_append] at hw
  imod histAlloc (GF := GF) ({0} : GSet Int) ([] : List Hent) with ⟨%γ, H⟩
  ihave H := BigSepS.bigSepS_singleton.1 $$ H
  imod hw γ $$ H with ⟨H, -⟩
  imodintro
  iexists γ
  isplitl [H]
  · iexact H
  · ipureintro
    exact sliceForwarded

end AxInstr.NonVacuity

end Weak
