/-
Weak: **GENERIC CLOSURE MACHINERY for `wpdOfClosedRunMaybe`** (spike S3a): the premises
`Hclos` / `Hwire` / `Hnord` DERIVED from an EXISTING ∃-run of `AxOpsem.astepProg` at
`atK`-preserving (admin) steps.

Rocq: `iris/AxRunClose.v` @ xxvzwolszwmp.

## The Rocq header, in substance

§1 `nodeOk m`: the program nodes at which the program half is deterministic AND insensitive to
the PLIC pins: every node except
  - `.pure _` (the boundary tick),
  - `.choose` (the chosen value),
  - `.memRead`/`.memWrite` (MMIO arms are `LDev` with a device-chosen value / device-gated
    existence, and `astepProg` quantifies the device per step; the RAM exclusive-store node has
    an extra `LSilent` self-loop next to its `LExStore`; in Lean the read node also carries the
    fetch arm),
  - `.regRead r` for a pin register `r` (the registers the PLIC wire changes).
`pnodeStepNd`: at such a node the LABEL and the whole result are determined, for ANY two device
inputs.
§2 `peqv`/`aeqv`: equal except the register files, which agree off the pin registers
(`regsAgree AxRunClose.pinReg`).  Simulation `astepProgSim` (any `astepProg` step, at any row,
is matched with the same label), wire `awireAeqv`.
§3 `gstep` (a guarded, `atK`-keeping, row-uniform program step), the invariant
`Pbefore q s := ∃ t, aeqv s t ∧ tc gstep t q` and exit `Qat q := aeqv · q`;
`runCloseHclos` / `runCloseHwire` / `runCloseHnord` are exactly `Hclos` / `Hwire` / `Hnord`;
`gstepRunOfRun` turns the delivered ∃-run into a `gstep` run; `wpdOfRunMaybe` plugs it all
into `wpdOfClosedRunMaybe` (`Hend` stays a premise).

## Deviations from Rocq

1. THE PIN SET (owner decision Q1, `WeakEvInst` deviation 5, `AxOpsem` deviation 3).  The Lean
   PLIC wire writes EITHER pin (`pinSet rs mm b` sets `sig_meip` or `sig_seip`), where Rocq's
   wire writes `sig_seip` only.  So the excluded register set is the Lean-only
   `AxRunClose.pinReg r := r = sig_seip ∨ r = sig_meip` (Rocq `seip_reg`): `peqv` is stated
   with `regsAgree AxRunClose.pinReg`, and `nodeOk` excludes `.regRead` of BOTH pins.
   Downstream files using `peqv`/`aeqv` (and Rocq `regs_agree seip_reg` facts about them) must
   use `AxRunClose.pinReg`.
2. O2 STAGE C: the oracle parameters (`T`, `img`, `ax_text`, `gx_img`) of `astep_prog` are
   deleted (AxOpsem deviation 2), so they disappear from every statement here
   (`astepProgAdmDet` keeps two rows; `gstep` quantifies the row and the label only); the
   `AStep_fetch` arm of the simulation is gone (a fetch is an `AStepAdmin` step).
3. `nodeOk` on lean-sail outcomes: a `.impure (.error _)` node (stuck in `pnodeStep`) is `True`
   (vacuous); every other constructor not listed above is `True` (Rocq `_ => True`).
4. THE BARRIER REPORT (`AxOpsem` deviation 4): `pnodeStepNd` also concludes equality of the
   `obar` outputs; `pnodeStepSim` carries `obar`.
5. `astepProgSim` / `runCloseHclos` …: the `axirisG Σ` section context of Rocq's `run_close`
   section is unused by its statements and is dropped (pure lemmas, parameters `i q`).
   `wpdOfRunMaybe`: `invGS_gen HasNoLc Σ` ↦ `[InvGS_gen hlc GF]` (any `hlc`, as AxWpdLift);
   `A -∗ B` ↦ `⊢ A -∗ B`.
6. Lean-only helpers (file-qualified): `AxRunClose.pinReg`, `AxRunClose.pinSetAgree`
   (the wire's register file agrees off the pins), `AxRunClose.pstepNodeSim` (the parked-fence
   case of the simulation, factored), `AxRunClose.aeqvReflOk` (reflexivity at a hart node;
   inline in Rocq's `wpd_of_run_maybe`).

**Rocq → Lean name map.**  `node_ok` `nodeOk`, `pnode_step_nd` `pnodeStepNd`, `pnode_ok`
`pnodeOk`, `pstep_prog_nd` `pstepProgNd`, `astep_prog_admin_k'` `astepProgAdminK'`,
`astep_prog_keep_admin` `astepProgKeepAdmin`, `anode_ok` `anodeOk`, `astep_prog_adm_det`
`astepProgAdmDet`, `lb_admin_wdata` `AxRunClose.lbAdminWdata` (duplicated name), `lb_admin_rd`
`lbAdminRd`, `peqv` `peqv`, `aeqv` `aeqv`, `peqv_sym` `peqvSym`, `peqv_trans` `peqvTrans`,
`aeqv_sym` `aeqvSym`, `aeqv_trans` `aeqvTrans`, `aeqv_ok` `aeqvOk`, `pnode_step_sim`
`pnodeStepSim`, `pstep_prog_sim` `pstepProgSim`, `astep_prog_sim` `astepProgSim`, `awire_aeqv`
`awireAeqv`, `gstep` `gstep`, `Pbefore` `Pbefore`, `Qat` `Qat`, `run_close_step`
`runCloseStep`, `run_close_hclos` `runCloseHclos`, `run_close_hwire` `runCloseHwire`,
`run_close_hnord` `runCloseHnord`, `arun_k_le` `arunKLe`, `gstep_run_of_run` `gstepRunOfRun`,
`wpd_of_run_maybe` `wpdOfRunMaybe`.

**Not ported:** the `Print Assumptions` block (the lint's axiom check covers it).
-/
import Weak.AxWpdLift
import Weak.WeakSailComplete

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std Iris.Std.PartialMap MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D
open Wlabel

/-! # 1. Admin determinism -/

/-- (Lean-only, deviation 1) The registers the PLIC wire writes: both pins. -/
def AxRunClose.pinReg (r : Register) : Prop := r = .sig_seip ∨ r = .sig_meip

def nodeOk (m : SailM Unit) : Prop :=
  match m with
  | .pure _ => False
  | .impure (.error _) _ => True
  | .impure (.ok o) _ =>
    match o with
    | .regRead r => ¬ AxRunClose.pinReg r
    | .memRead .. => False
    | .memWrite .. => False
    | .choose _ => False
    | _ => True

theorem pnodeStepNd (m : SailM Unit) (rs : RegFile) (ib : Ibch)
    (d1 : DevStates) (l1 : Wlabel) (m1 : SailM Unit) (o1 : Option RegFile)
    (f1 : Option (Bool × Bool × Bool × Bool)) (d1' : DevStates) (i1 : Option Ibch)
    (b1 : Option barrier_kind)
    (d2 : DevStates) (l2 : Wlabel) (m2 : SailM Unit) (o2 : Option RegFile)
    (f2 : Option (Bool × Bool × Bool × Bool)) (d2' : DevStates) (i2 : Option Ibch)
    (b2 : Option barrier_kind) :
    nodeOk m →
    pnodeStep m rs ib d1 l1 m1 o1 f1 d1' i1 b1 →
    pnodeStep m rs ib d2 l2 m2 o2 f2 d2' i2 b2 →
    l1 = l2 ∧ m1 = m2 ∧ o1 = o2 ∧ f1 = f2 ∧ i1 = i2 ∧ b1 = b2 := by
  intro hok h1 h2
  match m, hok, h1, h2 with
  | .pure _, hok, _, _ => exact hok.elim
  | .impure (.error _) _, _, h1, _ => exact h1.elim
  | .impure (.ok o) k, hok, h1, h2 =>
    cases o <;> simp only [nodeOk] at hok <;> simp only [pnodeStep] at h1 h2 <;>
      (obtain ⟨rfl, rfl, rfl, rfl, -, rfl, rfl⟩ := h1
       obtain ⟨rfl, rfl, rfl, rfl, -, rfl, rfl⟩ := h2
       exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩)

def pnodeOk (p : Pexv6) : Prop :=
  match p with
  | .PHart _ m _ _ _ => nodeOk m
  | .PDisk _ => False

theorem pstepProgNd (p : Pexv6) (d1 : Efab) (l1 : Wlabel) (p1 : Pexv6) (d1' : Efab)
    (d2 : Efab) (l2 : Wlabel) (p2 : Pexv6) (d2' : Efab) :
    pnodeOk p →
    pstepProg p d1 l1 p1 d1' → pstepProg p d2 l2 p2 d2' →
    l1 = l2 ∧ p1 = p2 := by
  intro hok h1 h2
  match p, p1, p2, hok, h1, h2 with
  | .PHart cpu m rs fn ib, .PHart c1 m1 rs1 fn1 ib1, .PHart c2 m2 rs2 fn2 ib2, hok, h1, h2 =>
    obtain ⟨rfl, o1, i1, b1, rfl, rfl, H1, -⟩ := h1
    obtain ⟨rfl, o2, i2, b2, rfl, rfl, H2, -⟩ := h2
    cases fn with
    | some f =>
      obtain ⟨pr, pw, sr, sw⟩ := f
      obtain ⟨rfl, rfl, rfl, rfl, -, rfl, -⟩ := H1
      obtain ⟨rfl, rfl, rfl, rfl, -, rfl, -⟩ := H2
      exact ⟨rfl, rfl⟩
    | none =>
      obtain ⟨rfl, rfl, rfl, rfl, rfl, -⟩ :=
        pnodeStepNd m rs ib _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hok H1 H2
      exact ⟨rfl, rfl⟩
  | .PDisk _, _, _, hok, _, _ => exact (hok : False).elim
  | .PHart .., .PDisk _, _, _, h1, _ => exact (h1 : False).elim
  | .PHart .., .PHart .., .PDisk _, _, _, h2 => exact (h2 : False).elim

/-- An admin-labelled `astepProg` step keeps `atK` (local copy of `AxInstr`'s
`astep_prog_admin_k`). -/
theorem astepProgAdminK' (row : List Lbl) (s : Athread) (l : Wlabel) (s' : Athread) :
    AxOpsem.astepProg row s l s' → AxOpsem.lbAdminAx true l → s'.atK = s.atK := by
  intro h hadm
  cases h with
  | AStepAdmin => rfl
  | AStepWrite _ _ _ _ _ _ _ _ hwr =>
    cases l <;> simp [wlWr, AxOpsem.lbAdminAx] at hwr hadm
  | AStepFence _ _ _ _ _ _ _ _ hf =>
    cases l <;> simp [wlFence, AxOpsem.lbAdminAx] at hf hadm

/-- A `atK`-keeping step is `AStepAdmin`. -/
theorem astepProgKeepAdmin (row : List Lbl) (s : Athread) (l : Wlabel) (s' : Athread) :
    AxOpsem.astepProg row s l s' → s'.atK = s.atK → AxOpsem.lbAdminAx true l := by
  intro h hk
  cases h with
  | AStepAdmin _ _ _ _ _ _ hadm => exact hadm
  | AStepWrite => simp at hk
  | AStepFence => simp at hk

def anodeOk (s : Athread) : Prop := pnodeOk s.atP

/-- (1) THE ADMIN DETERMINISM, uniform in the row. -/
theorem astepProgAdmDet (row1 row2 : List Lbl) (t : Athread) (l1 : Wlabel) (t1 : Athread)
    (l2 : Wlabel) (t2 : Athread) :
    anodeOk t →
    AxOpsem.astepProg row1 t l1 t1 → t1.atK = t.atK →
    AxOpsem.astepProg row2 t l2 t2 →
    l2 = l1 ∧ t2 = t1 ∧ AxOpsem.lbAdminAx true l1 := by
  intro hok H1 hk1 H2
  have hadm := astepProgKeepAdmin row1 _ _ _ H1 hk1
  obtain ⟨d1, d1', P1⟩ := astepProgPstep row1 _ _ _ H1
  obtain ⟨d2, d2', P2⟩ := astepProgPstep row2 _ _ _ H2
  obtain ⟨rfl, hp⟩ := pstepProgNd _ _ _ _ _ _ _ _ _ hok P1 P2
  have hk2 := astepProgAdminK' row2 _ _ _ H2 hadm
  refine ⟨rfl, ?_, hadm⟩
  obtain ⟨p1, k1⟩ := t1
  obtain ⟨p2, k2⟩ := t2
  simp only at hp hk1 hk2
  subst hp
  rw [hk1, hk2]

theorem AxRunClose.lbAdminWdata (l : Wlabel) : AxOpsem.lbAdminAx true l → wlWdata l = none := by
  cases l <;> simp [AxOpsem.lbAdminAx, wlWdata]

theorem lbAdminRd (l : Wlabel) : AxOpsem.lbAdminAx true l → wlRd l = none := by
  cases l <;> simp [AxOpsem.lbAdminAx, wlRd]

/-! # 2. Pin insensitivity -/

def peqv (p q : Pexv6) : Prop :=
  match p, q with
  | .PHart c m rs fn ib, .PHart c' m' rs' fn' ib' =>
      c = c' ∧ m = m' ∧ fn = fn' ∧ ib = ib' ∧ regsAgree AxRunClose.pinReg rs rs'
  | _, _ => False

def aeqv (s t : Athread) : Prop := s.atK = t.atK ∧ peqv s.atP t.atP

theorem peqvSym (p q : Pexv6) : peqv p q → peqv q p := by
  match p, q with
  | .PHart _ _ _ _ _, .PHart _ _ _ _ _ =>
    rintro ⟨rfl, rfl, rfl, rfl, h⟩
    exact ⟨rfl, rfl, rfl, rfl, regsAgreeSym _ _ _ h⟩
  | .PHart _ _ _ _ _, .PDisk _ => exact False.elim
  | .PDisk _, _ => exact False.elim

theorem peqvTrans (p q r : Pexv6) : peqv p q → peqv q r → peqv p r := by
  cases p <;> cases q <;> cases r
  all_goals first
    | (intro h1 _; exact (h1 : False).elim)
    | (intro _ h2; exact (h2 : False).elim)
    | (rintro ⟨rfl, rfl, rfl, rfl, h⟩ ⟨rfl, rfl, rfl, rfl, h'⟩
       exact ⟨rfl, rfl, rfl, rfl, regsAgreeTrans _ _ _ _ h h'⟩)

theorem aeqvSym (s t : Athread) : aeqv s t → aeqv t s :=
  fun ⟨hk, hp⟩ => ⟨hk.symm, peqvSym _ _ hp⟩

theorem aeqvTrans (s t u : Athread) : aeqv s t → aeqv t u → aeqv s u :=
  fun ⟨h1, p1⟩ ⟨h2, p2⟩ => ⟨h1.trans h2, peqvTrans _ _ _ p1 p2⟩

theorem aeqvOk (s t : Athread) : aeqv s t → anodeOk s → anodeOk t := by
  obtain ⟨ps, ks⟩ := s
  obtain ⟨pt, kt⟩ := t
  unfold aeqv anodeOk
  simp only
  match ps, pt with
  | .PHart _ _ _ _ _, .PHart _ _ _ _ _ =>
    rintro ⟨_, _, rfl, _⟩ h
    exact h
  | .PHart _ _ _ _ _, .PDisk _ => exact fun h => h.2.elim
  | .PDisk _, _ => exact fun _ h => h.elim

/-- (Lean-only) Reflexivity at a hart node. -/
theorem AxRunClose.aeqvReflOk (s : Athread) : anodeOk s → aeqv s s := by
  obtain ⟨p, k⟩ := s
  unfold anodeOk aeqv
  match p with
  | .PHart _ _ rs _ _ => exact fun _ => ⟨rfl, rfl, rfl, rfl, rfl, regsAgreeRefl _ rs⟩
  | .PDisk _ => exact False.elim

theorem pnodeStepSim (m : SailM Unit) (rs rs' : RegFile) (ib : Ibch) (d : DevStates)
    (l : Wlabel) (m' : SailM Unit) (ors : Option RegFile)
    (fn' : Option (Bool × Bool × Bool × Bool)) (d' : DevStates) (oib : Option Ibch)
    (obar : Option barrier_kind) :
    nodeOk m → regsAgree AxRunClose.pinReg rs rs' →
    pnodeStep m rs' ib d l m' ors fn' d' oib obar →
    ∃ ors0, pnodeStep m rs ib d l m' ors0 fn' d' oib obar ∧
      regsAgree AxRunClose.pinReg (ors0.getD rs) (ors.getD rs') := by
  intro hok hag h
  match m, hok, h with
  | .pure _, hok, _ => exact hok.elim
  | .impure (.error _) _, _, h => exact h.elim
  | .impure (.ok o) k, hok, h =>
    cases o with
    | regRead r =>
      simp only [nodeOk] at hok
      simp only [pnodeStep] at h
      obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := h
      exact ⟨none, ⟨rfl, by rw [hag r hok], rfl, rfl, rfl, rfl, rfl⟩, hag⟩
    | regWrite r v =>
      simp only [pnodeStep] at h
      obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := h
      exact ⟨some (rs.set r v), ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
        regsAgreeSet _ _ _ _ _ hag⟩
    | memRead => exact hok.elim
    | memWrite => exact hok.elim
    | choose => exact hok.elim
    | _ =>
      first
        | exact (h : False).elim
        | (obtain ⟨h1, h2, rfl, h4⟩ := h
           exact ⟨none, ⟨h1, h2, rfl, h4⟩, hag⟩)

/-- (Lean-only) The simulation at `pstepNode` (parked fence or monad node). -/
theorem AxRunClose.pstepNodeSim (cpu : CPU) (m : SailM Unit) (rs rs' : RegFile)
    (fn : Option (Bool × Bool × Bool × Bool)) (ib : Ibch) (d : DevStates)
    (l : Wlabel) (m' : SailM Unit) (ors : Option RegFile)
    (fn' : Option (Bool × Bool × Bool × Bool)) (d' : DevStates) (oib : Option Ibch)
    (obar : Option barrier_kind) :
    nodeOk m → regsAgree AxRunClose.pinReg rs rs' →
    pstepNode cpu m rs' fn ib d l m' ors fn' d' oib obar →
    ∃ ors0, pstepNode cpu m rs fn ib d l m' ors0 fn' d' oib obar ∧
      regsAgree AxRunClose.pinReg (ors0.getD rs) (ors.getD rs') := by
  intro hok hag h
  cases fn with
  | some f =>
    obtain ⟨pr, pw, sr, sw⟩ := f
    have ho : ors = none := h.2.2.1
    subst ho
    exact ⟨none, h, hag⟩
  | none => exact pnodeStepSim m rs rs' ib d l m' ors fn' d' oib obar hok hag h

theorem pstepProgSim (p q : Pexv6) (d : Efab) (l : Wlabel) (q' : Pexv6) (d' : Efab) :
    pnodeOk p → peqv p q → pstepProg q d l q' d' →
    ∃ p', pstepProg p d l p' d' ∧ peqv p' q' := by
  intro hok heq hst
  match p, q, q', hok, heq, hst with
  | .PHart c m rs fn ib, .PHart c0 m0 rs0 fn0 ib0, .PHart c1 m1 rs1 fn1 ib1, hok, heq, hst =>
    obtain ⟨rfl, rfl, rfl, rfl, hag⟩ := heq
    obtain ⟨rfl, ors, oib, obar, rfl, rfl, hn, hd⟩ := hst
    obtain ⟨ors0, hn0, hag0⟩ :=
      AxRunClose.pstepNodeSim _ _ rs rs0 _ _ _ _ _ _ _ _ _ _ hok hag hn
    exact ⟨.PHart _ m1 (ors0.getD rs) fn1 (oib.getD _),
      ⟨rfl, ors0, oib, obar, rfl, rfl, hn0, hd⟩, rfl, rfl, rfl, rfl, hag0⟩
  | .PDisk _, _, _, hok, _, _ => exact (hok : False).elim
  | .PHart .., .PDisk _, _, _, heq, _ => exact (heq : False).elim
  | .PHart .., .PHart .., .PDisk _, _, _, hst => exact (hst : False).elim

/-- (2a) Any `astepProg` step of `t` is matched, SAME LABEL, from any `s` agreeing with `t` off
the pins, at an `anodeOk` node. -/
theorem astepProgSim (row : List Lbl) (s t : Athread) (l : Wlabel) (t' : Athread) :
    anodeOk s → aeqv s t → AxOpsem.astepProg row t l t' →
    ∃ s', AxOpsem.astepProg row s l s' ∧ aeqv s' t' := by
  obtain ⟨ps, ks⟩ := s
  intro hok ⟨hk, hp⟩ hst
  unfold anodeOk at hok
  simp only at hk hp hok
  subst hk
  cases hst with
  | AStepAdmin p k d l0 p' d' hadm hps =>
    obtain ⟨p0, hp0, heq⟩ := pstepProgSim _ _ _ _ _ _ hok hp hps
    exact ⟨⟨p0, _⟩, .AStepAdmin _ _ _ _ _ _ hadm hp0, rfl, heq⟩
  | AStepWrite p k d l0 lb p' d' hrow h1 h2 h3 hps =>
    obtain ⟨p0, hp0, heq⟩ := pstepProgSim _ _ _ _ _ _ hok hp hps
    exact ⟨⟨p0, _⟩, .AStepWrite _ _ _ _ _ _ _ hrow h1 h2 h3 hp0, rfl, heq⟩
  | AStepFence p k d l0 lb p' d' hrow h1 h2 hps =>
    obtain ⟨p0, hp0, heq⟩ := pstepProgSim _ _ _ _ _ _ hok hp hps
    exact ⟨⟨p0, _⟩, .AStepFence _ _ _ _ _ _ _ hrow h1 h2 hp0, rfl, heq⟩

/-- (Lean-only) The wire's register file agrees with the old one off the pins. -/
theorem AxRunClose.pinSetAgree (rs : RegFile) (mm b : Bool) :
    regsAgree AxRunClose.pinReg rs (pinSet rs mm b) := by
  unfold pinSet
  cases mm
  · exact regsAgreeSetExcluded _ _ _ _ (.inl rfl)
  · exact regsAgreeSetExcluded _ _ _ _ (.inr rfl)

/-- (2b) The PLIC wire moves a state only within its `aeqv` class. -/
theorem awireAeqv (s s' : Athread) : awire s s' → aeqv s' s := by
  rintro ⟨hk, d, d', hw⟩
  obtain ⟨-, cpu, m, rs, fn, ib, mm, b, k, hp, -, -, hp'⟩ := pstepWireInv _ _ _ _ _ hw
  refine ⟨hk, ?_⟩
  rw [hp, hp']
  exact ⟨rfl, rfl, rfl, rfl, regsAgreeSym _ _ _ (AxRunClose.pinSetAgree rs mm b)⟩

/-! # 3. The closure -/

/-- The guarded, `atK`-keeping, row-uniform program step. -/
def gstep (s1 s2 : Athread) : Prop :=
  anodeOk s1 ∧ s2.atK = s1.atK ∧ ∃ (row : List Lbl) (l : Wlabel), AxOpsem.astepProg row s1 l s2

def Pbefore (q s : Athread) : Prop := ∃ t, aeqv s t ∧ tc gstep t q

def Qat (q s : Athread) : Prop := aeqv s q

/-- `Hclos`, for any row. -/
theorem runCloseStep (q : Athread) (row : List Lbl) (s1 : Athread) (l : Wlabel) (s2 : Athread) :
    Pbefore q s1 → AxOpsem.astepProg row s1 l s2 →
    wlWdata l = none ∧ s2.atK = s1.atK ∧ (Pbefore q s2 ∨ Qat q s2) := by
  rintro ⟨t, heq, htc⟩ hst
  have hg : ∃ t', gstep t t' ∧ (t' = q ∨ tc gstep t' q) := by
    rcases AxWpdLift.tcInvL htc with h | ⟨y, h, h'⟩
    · exact ⟨q, h, .inl rfl⟩
    · exact ⟨y, h, .inr h'⟩
  obtain ⟨t', ⟨hok, hk', row', l', hst'⟩, hrest⟩ := hg
  obtain ⟨t2, hst2, heq2⟩ := astepProgSim row t s1 l s2 hok (aeqvSym _ _ heq) hst
  obtain ⟨rfl, rfl, hadm⟩ := astepProgAdmDet row' row t l' t' l t2 hok hst' hk' hst2
  refine ⟨AxRunClose.lbAdminWdata _ hadm, ?_, ?_⟩
  · have h1 := heq.1
    have h2 := heq2.1
    omega
  · rcases hrest with rfl | htc'
    · exact .inr (aeqvSym _ _ heq2)
    · exact .inl ⟨t2, aeqvSym _ _ heq2, htc'⟩

section runClose
variable (i : Agent) (q : Athread)

/-- EXACTLY `wpdOfClosedRunMaybe`'s `Hclos` at `P := Pbefore q`, `Q := Qat q`. -/
theorem runCloseHclos : ∀ GD s1 l s2, Pbefore q s1 →
    AxOpsem.astepProg (AxOpsem.grow GD i) s1 l s2 →
    wlWdata l = none ∧ s2.atK = s1.atK ∧ (Pbefore q s2 ∨ Qat q s2) :=
  fun GD s1 l s2 => runCloseStep q (AxOpsem.grow GD i) s1 l s2

/-- EXACTLY `Hwire`. -/
theorem runCloseHwire : ∀ s1 s2, Pbefore q s1 → awire s1 s2 → Pbefore q s2 ∨ Qat q s2 := by
  rintro s1 s2 ⟨t, heq, htc⟩ hw
  exact .inl ⟨t, aeqvTrans _ _ _ (awireAeqv _ _ hw) heq, htc⟩

/-- EXACTLY `Hnord`. -/
theorem runCloseHnord : ∀ GD s1 id K, Pbefore q s1 → ¬ areadStep (AxOpsem.grow GD i) s1 id K := by
  rintro GD s1 id K ⟨t, heq, htc⟩ ⟨lb, -, -, hrd, HK⟩
  obtain ⟨l, d, d', hl, -, hps, -⟩ :=
    HK (List.replicate (aidentN id) (0#8)) List.length_replicate
  have hg : ∃ t', gstep t t' := by
    rcases AxWpdLift.tcInvL htc with h | ⟨y, h, -⟩
    · exact ⟨q, h⟩
    · exact ⟨y, h⟩
  obtain ⟨t', hok, hk', row', l', hst'⟩ := hg
  have hadm := astepProgKeepAdmin _ _ _ _ hst' hk'
  obtain ⟨d1, d1', P1⟩ := astepProgPstep _ _ _ _ hst'
  obtain ⟨p2, P2, -⟩ := pstepProgSim _ _ _ _ _ _ hok (peqvSym _ _ heq.2) hps
  obtain ⟨rfl, -⟩ := pstepProgNd _ _ _ _ _ _ _ _ _ hok P1 P2
  rw [lbAdminRd _ hadm] at hl
  rw [← hl] at hrd
  simp at hrd

end runClose

/-- From the DELIVERED ∃-run: positions are monotone along a run. -/
theorem arunKLe (row : List Lbl) (s q : Athread) :
    rtc (fun t1 t2 => ∃ l, AxOpsem.astepProg row t1 l t2) s q → s.atK ≤ q.atK := by
  intro h
  induction h with
  | refl => exact Nat.le_refl _
  | tail _ hyz ih =>
    obtain ⟨l, hyz⟩ := hyz
    rcases astepProgK _ _ _ _ hyz with hy | ⟨hy, -⟩ <;> omega

/-- A `tc` run of `astepProg` (any row) that ends at the `atK` it started from, every state
strictly before `q` being `anodeOk`, is a `gstep` run. -/
theorem gstepRunOfRun (row : List Lbl) (s0 q : Athread) :
    tc (fun t1 t2 => ∃ l, AxOpsem.astepProg row t1 l t2) s0 q →
    q.atK = s0.atK →
    (∀ t, rtc (fun t1 t2 => ∃ l, AxOpsem.astepProg row t1 l t2) s0 t →
          tc (fun t1 t2 => ∃ l, AxOpsem.astepProg row t1 l t2) t q → anodeOk t) →
    tc gstep s0 q := by
  intro h
  induction h with
  | single hxy =>
    rename_i z
    intro hk hok
    obtain ⟨l, hxy⟩ := hxy
    exact tc_once ⟨hok s0 (rtc_refl _) (tc_once ⟨l, hxy⟩), hk, row, l, hxy⟩
  | tail hxy hyz ih =>
    rename_i y z
    intro hk hok
    obtain ⟨l, hyz'⟩ := hyz
    have hle := arunKLe row s0 y (tc_rtc hxy)
    have hky : z.atK = y.atK := by
      rcases astepProgK _ _ _ _ hyz' with h | ⟨h, -⟩ <;> omega
    refine tc_r (ih (by omega) ?_) ?_
    · intro t hst htc
      exact hok t hst (tc_r htc ⟨l, hyz'⟩)
    · exact ⟨hok y (tc_rtc hxy) (tc_once ⟨l, hyz'⟩), hky, row, l, hyz'⟩

/-! EVERYTHING PLUGGED IN: the generic segment lemma.  Only `Hend` (a row-length fact about
every `GD`) remains a premise. -/
section wpdRun
variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF] [Axpol]

theorem wpdOfRunMaybe (i : Agent) (q : Athread) (Φ : Athread → IProp GF) (s0 : Athread)
    (Hrun : tc gstep s0 q)
    (Hend : ∀ (GD : Gdexec) s1, Pbefore q s1 → s1.atK ≠ (AxOpsem.grow GD i).length) :
    ⊢ (∀ s2, ⌜Qat q s2⌝ -∗ wpd .MaybeStuck i s2 Φ) -∗ wpd .MaybeStuck i s0 Φ := by
  have hok : anodeOk s0 := by
    rcases AxWpdLift.tcInvL Hrun with h | ⟨_, h, -⟩
    · exact h.1
    · exact h.1
  exact wpdOfClosedRunMaybe i (Pbefore q) (Qat q) Φ s0 (runCloseHnord i q) (runCloseHclos i q)
    (runCloseHwire q) Hend ⟨s0, AxRunClose.aeqvReflOk s0 hok, Hrun⟩

end wpdRun

end Weak
