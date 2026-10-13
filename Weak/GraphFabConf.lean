/-
Weak: **W13 (W), increment 1 — the device-ACTIVE tagged conformance bundle `xv6ConfS` and the
discharge of `gfDevWIo`** (plan `notes/weak-allocproc-plan.md` rev 45, §C top THIRD LAUNCH SET
"W13 (W)", §A(†); review R41 [R41.4]/[R41.s6]; [R40.s2]/[R40.s6]).

Lean-only, no Rocq twin.

  §1  `GfexecT` (the fabric bundle over the TAGGED graph `GdexecT`) and `forgetF`.
  §2  **`xv6ConfS`** — the SHAPED, UNPINNED, FABRIC-ORDERED, TAGGED conformance text of §A(†):
      `gfexecConfIO`'s rows (per-row `hartConff` emission with two fabric endpoints and contact
      bits, membership by fabric CONTACT [OWN.43], fabric endpoints read off the global trace
      `fab`, the fetch-clause SLOT `emZifencei`) with the dependency clause TAGGED (every edge
      `rowDepsT` emits is in `gtDeps` with its tag — `gdexecQconfT`'s clause, `CatLinChain.lean`
      §3) and NO `emDevfree` (this is where W13 (F-dep)'s I/O-endpoint edges first have a
      consumer).  `xv6ConfSForget`: the projection to the untagged `gfexecConfIO` on
      `forgetF GT` (the `gdexecQconfTForget` pattern, over `hemitf`: `hemitfTagLbl`).
  §3  **`gfDevWIoOfXv6`** — the (R3′) named premise `gfDevWIo` (`WeakRvwmoLin2.lean` §8.3)
      DISCHARGED on an xv6 bundle: the HART half PROVED ([R40.s2]: admin labels are never `LDev`,
      a hart's non-`LDev` steps keep the fabric — `pdevEvOk` — and `LDev` projects to `LIo`:
      `GraphFabConf.hemitfHartIo`), the DISK half the NAMED hypothesis **`usedElemGateOk`**
      [R41.4].  `fconfTraceRealizeIOXv6`: `fconfTraceRealizeIO` with `gfDevWIo` replaced by
      the xv6 boot shape + `usedElemGateOk`.

**`usedElemGateOk` (device-model text, owner informed under the non-blocking rule [R41.4]).**
Stated at the bundle: every DISK-row fabric member is a RAM write or an I/O event.  On the disk
program's shape (`WeakEvInst.pdiskProg`, `VirtioProg.lean` node table) the only disk-row block
that is a member with a label that is neither (a `DFence`; a `DRead` never follows a fabric
step — [R40.1](c)) is the `DFence`'s block when the used-ELEMENT `DWriteDev` takes its OWN-GUARD
SKIP (`pdiskProg`'s SKIP arm: `g s = none ∨ ¬ ramBytes (pa s) …`, a silent `pdevEv`-true admin
step folded into the next row item's block) [R40.s6]; so on xv6 runs the hypothesis says "the
used-element gate `phase ∧ completeOk ∧ pushOk` holds and its target is RAM" — a RUN-LEVEL
virtio fact (the state `virtio_disk_rw`'s descriptor/avail discipline produces), NOT a
consequence of the program's shape, and not available in this item's consumer files.  It is
DISCHARGED by W14 (the device-active witness / the disk invariant), or stays a named premise.
Spec: RVWMO / riscv.cat / Sail / Zifencei / PMAs are SILENT on device programs; the hypothesis is
EQUAL to MachCSL's disk step on xv6 runs.  (The shape-to-gate equivalence is stated here in prose
only; proving it is W14's.)

**Deviations from the plan text.**  (1) `xv6ConfS` quantifies the fabric trace `fab`
EXISTENTIALLY (§A's statement passes no `fab`; `fab 0 = d0` is inside).  (2) The fetch clause is
the SLOT `emZifencei` with its current content (`emFetchImg`); W5d-G G1 changes its content in
`Fab` — ONE S rebase of nothing here (the slot's NAME is what `xv6ConfS` uses).  (3) The plan's
W13-wit (hart 0 to its first UART store, by kernel evaluation) and the Bool twin of `xv6ConfS` are
NOT in this increment (`PROGRESS-W13W.md`).

**Name map.**  Lean-only: `GfexecT`, `forgetF`, `gfexecConfIOT`, `xv6ConfS`, `xv6ConfSForget`,
`GraphFabConf.hemitfTagLbl`, `GraphFabConf.isHart`, `GraphFabConf.isLDev`,
`GraphFabConf.pstepEvHart`, `GraphFabConf.pdevEvHart`, `GraphFabConf.adminNotLDev`,
`GraphFabConf.admRunTHart`, `GraphFabConf.realizesLDevIo`, `GraphFabConf.hemitfHartIo`,
`GraphFabConf.xbootHart`, `usedElemGateOk`, `gfDevWIoOfXv6`, `fconfTraceRealizeIOXv6`.
-/
import Weak.WeakRvwmoKillIO
import Weak.WeakRvwmoCapstone

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Lbl

/-! # 1. The fabric bundle over the tagged graph -/

/-- The fabric bundle over a TAGGED graph (§A: `GT : GfexecT`, `GT.gfGd : GdexecT`). -/
structure GfexecT where
  GFExecT ::
  gfGd : GdexecT
  gfDev : List Geid

/-- The untagged fabric bundle the chain consumes (`forget` drops the tags and every edge whose
endpoints are not a RAM read and a RAM write). -/
def forgetF (GT : GfexecT) : Gfexec := ⟨forget GT.gfGd, GT.gfDev⟩

/-! # 2. `xv6ConfS` -/

/-- The device-ACTIVE fabric conformance over the tagged graph: `gfexecConfIO`'s clauses with the
dependency clause TAGGED (no `emDevfree`). -/
def gfexecConfIOT (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (GT : GfexecT) : Prop :=
  fab 0 = d0 ∧
  GT.gfDev.Nodup ∧
  (∀ (n i k : Nat), GT.gfDev[n]? = some (i, k) →
     ∃ row, GT.gfGd.gtG.gxProg[i]? = some row ∧ k < row.length) ∧
  (∀ (i : Nat) (row : List Lbl), GT.gfGd.gtG.gxProg[i]? = some row →
     ∃ (em : Hemission) (dvi dvo : Nat → Efab) (tq : Nat → Bool),
       hartConff i row (boot i) dvi dvo tq em ∧
       (∀ k : Nat, k < row.length →
          ((i, k) ∈ GT.gfDev ↔ (gisIo GT.gfGd.gtG (i, k) = true ∨ dvi k ≠ dvo k ∨ tq k = true))) ∧
       (∀ (k n : Nat), GT.gfDev[n]? = some (i, k) → dvi k = fab n ∧ dvo k = fab (n + 1)) ∧
       emZifencei GT.gfGd.gtG.gxImg em ∧
       (∀ e, e ∈ rowDepsT em.emItems → (((i, e.1.1), (i, e.1.2)), e.2) ∈ GT.gfGd.gtDeps))

/-- **`xv6ConfS`** (§A(†)): the booted image, at most `nh` rows, and a fabric trace along which
the tagged device-active conformance holds. -/
def xv6ConfS (boot : Nat → Pexv6) (d0 : Efab) (im : Image) (nh : Nat) (GT : GfexecT) : Prop :=
  GT.gfGd.gtG.gxImg = im ∧
  GT.gfGd.gtG.gxProg.length ≤ nh ∧
  ∃ fab : Nat → Efab, gfexecConfIOT boot d0 fab GT

/-- (Lean-only) `hemitTagLbl` for the two-endpoint emission: a tagged item `(l, some j)` sits at
row position `j` and agrees with the row event on read/write. -/
theorem GraphFabConf.hemitfTagLbl (dvi dvo : Nat → Efab) (tq : Nat → Bool) (k : Nat)
    (ws : Wstate) (row : List Lbl) (p : Pexv6) (es : List Eitem) (pfin : Pexv6) (it : Eitem)
    (j : Nat) :
    hemitf dvi dvo tq k ws row p es pfin → it ∈ es → it.2 = some j →
    ∃ lb, k ≤ j ∧ row[j - k]? = some lb ∧
      (elbIsR it.1 = true → lbIsR lb = true) ∧ (elbIsW it.1 = true → lbIsW lb = true) := by
  intro h
  induction h with
  | HFnil k ws p => intro hit; exact absurd hit List.not_mem_nil
  | HFone k ws lb row p ls pa da l p' es pfin b _ hre _ _ _ ih =>
    intro hit hj
    rcases List.mem_append.1 hit with hit | hit
    · simp only [eadm, List.mem_map] at hit
      obtain ⟨_, _, rfl⟩ := hit
      simp at hj
    rcases List.mem_cons.1 hit with rfl | hit
    · simp only [Option.some.injEq] at hj
      subst hj
      obtain ⟨hr, hw⟩ := hlblRealizesKind pa ws lb l hre
      exact ⟨lb, Nat.le_refl _, by simp, hr, hw⟩
    · obtain ⟨lb0, hle, hlk, hr, hw⟩ := ih hit hj
      refine ⟨lb0, by omega, ?_, hr, hw⟩
      rw [show j - k = (j - (k + 1)) + 1 by omega, List.getElem?_cons_succ]
      exact hlk
  | HFpair k ws lb row p ls1 pa da l1 pm dm ls2 pm2 dm2 l2 p' es pfin b1 b2 _ hre _ _ _ _ _ ih =>
    intro hit hj
    obtain ⟨aq, rl, base, tvs, data, asrc1, asrc2, vsrc2, rfl, rfl, _, _, hlb⟩ := hre
    rcases List.mem_append.1 hit with hit | hit
    · simp only [eadm, List.mem_map] at hit
      obtain ⟨_, _, rfl⟩ := hit
      simp at hj
    rcases List.mem_cons.1 hit with rfl | hit
    · simp only [Option.some.injEq] at hj
      subst hj
      exact ⟨lb, Nat.le_refl _, by simp, fun _ => by rw [hlb]; rfl, fun _ => by rw [hlb]; rfl⟩
    rcases List.mem_append.1 hit with hit | hit
    · simp only [eadm, List.mem_map] at hit
      obtain ⟨_, _, rfl⟩ := hit
      simp at hj
    rcases List.mem_cons.1 hit with rfl | hit
    · simp only [Option.some.injEq] at hj
      subst hj
      exact ⟨lb, Nat.le_refl _, by simp, fun _ => by rw [hlb]; rfl, fun _ => by rw [hlb]; rfl⟩
    · obtain ⟨lb0, hle, hlk, hr, hw⟩ := ih hit hj
      refine ⟨lb0, by omega, ?_, hr, hw⟩
      rw [show j - k = (j - (k + 1)) + 1 by omega, List.getElem?_cons_succ]
      exact hlk

/-- **The projection**: the tagged device-active bundle gives the untagged `gfexecConfIO` on
`forgetF GT` (every tree edge is a tagged edge, `rowDepsSubT`; its source is a RAM read and its
target a RAM write, so `forget` keeps it). -/
theorem xv6ConfSForget (boot : Nat → Pexv6) (d0 : Efab) (im : Image) (nh : Nat)
    (GT : GfexecT) :
    xv6ConfS boot d0 im nh GT →
    (forgetF GT).gfGd.gdG.gxImg = im ∧ (forgetF GT).gfGd.gdG.gxProg.length ≤ nh ∧
    ∃ fab, gfexecConfIO boot d0 fab (forgetF GT) := by
  rintro ⟨himg, hnh, fab, h0, hnd, hbnd, hrows⟩
  refine ⟨himg, hnh, fab, h0, hnd, hbnd, fun i row hrow => ?_⟩
  obtain ⟨em, dvi, dvo, tq, hem, hiff, hpin, hfi, hdeps⟩ := hrows i row hrow
  refine ⟨em, dvi, dvo, tq, hem, hiff, hpin, hfi, fun jk hjk => ?_⟩
  obtain ⟨tg, htg, -⟩ := rowDepsSubT em.emItems jk.1 jk.2 hjk
  have hem' : hemitf dvi dvo tq 0 wsInit row (boot i) em.emItems em.emFin := hem
  obtain ⟨it, hit, hpos, hr⟩ := rowDepsSrc _ _ hjk
  obtain ⟨lr, -, hlr, hrr, -⟩ := GraphFabConf.hemitfTagLbl _ _ _ _ _ _ _ _ _ it jk.1 hem' hit hpos
  obtain ⟨it', hit', hpos', hw⟩ := rowDepsTgt _ _ hjk
  obtain ⟨lw, -, hlw, -, hww⟩ :=
    GraphFabConf.hemitfTagLbl _ _ _ _ _ _ _ _ _ it' jk.2 hem' hit' hpos'
  rw [Nat.sub_zero] at hlr hlw
  have hrow' : GT.gfGd.gtG.gxProg[i]? = some row := hrow
  refine (elemOfForgetDeps GT.gfGd.gtG GT.gfGd.gtDeps (i, jk.1) (i, jk.2)).2
    ⟨tg, hdeps _ htg, ?_, ?_⟩
  · simp [gisRd, gxLbl, hrow', hlr, hrr hr]
  · simp [gisW, gxLbl, hrow', hlw, hww hw]

/-! # 3. `gfDevWIo` on an xv6 bundle: the hart half PROVED, the disk half NAMED -/

/-- (Lean-only) A hart process. -/
def GraphFabConf.isHart (p : Pexv6) : Bool :=
  match p with
  | .PHart .. => true
  | .PDisk _ => false

/-- (Lean-only) An `LDev` label. -/
def GraphFabConf.isLDev (l : Wlabel) : Bool :=
  match l with
  | .LDev .. => true
  | _ => false

/-- A hart steps to a hart (mismatched constructors are `False`, `pstepEv`). -/
theorem GraphFabConf.pstepEvHart (p : Pexv6) (d : Efab) (l : Wlabel) (p' : Pexv6) (d' : Efab) :
    pstepEv p d l p' d' → GraphFabConf.isHart p = true → GraphFabConf.isHart p' = true := by
  intro h hp
  cases p with
  | PDisk _ => simp [GraphFabConf.isHart] at hp
  | PHart cpu m rs fn ib =>
    cases p' with
    | PHart cpu' m' rs' fn' ib' => rfl
    | PDisk _ => simp [pstepEv] at h

/-- At a hart, the fabric marker is exactly "an `LDev` label" (the `.PDisk` match fails). -/
theorem GraphFabConf.pdevEvHart (p p' : Pexv6) (l : Wlabel) :
    GraphFabConf.isHart p = true → pdevEv p l p' = GraphFabConf.isLDev l := by
  intro hp
  cases p with
  | PDisk _ => simp [GraphFabConf.isHart] at hp
  | PHart cpu m rs fn ib => cases l <;> rfl

/-- Administrative labels are never `LDev` (`lbAdmin`, `WeakAxRealize.lean:140-144`). -/
theorem GraphFabConf.adminNotLDev (instr : Bool) (l : Wlabel) :
    lbAdmin instr l → GraphFabConf.isLDev l = false := by
  cases l <;> simp [lbAdmin, GraphFabConf.isLDev]

/-- A hart's administrative run is contact-free and fabric-preserving, and stays at a hart. -/
theorem GraphFabConf.admRunTHart (instr : Bool) (p : Pexv6) (d : Efab) (ls : List Wlabel)
    (p' : Pexv6) (d' : Efab) (b : Bool) :
    WeakRvwmoFab.admRunT instr p d ls p' d' b → GraphFabConf.isHart p = true →
    b = false ∧ d' = d ∧ GraphFabConf.isHart p' = true := by
  intro h
  induction h with
  | ATnil p d => intro hp; exact ⟨rfl, rfl, hp⟩
  | ATcons p d l p1 d1 ls p' d' b ha hs _ ih =>
    intro hp
    have hl : pdevEv p l p1 = false := by
      rw [GraphFabConf.pdevEvHart p p1 l hp, GraphFabConf.adminNotLDev instr l ha]
    obtain ⟨hd1, -⟩ := pdevEvOk p d l p1 d1 hs hl
    obtain ⟨hb, hd', hp'⟩ := ih (GraphFabConf.pstepEvHart p d l p1 d1 hs hp)
    exact ⟨by rw [hl, hb], by rw [hd', hd1], hp'⟩

/-- An `LDev` step realizes an I/O-class row event (`projLbl (.LDev …) = some (.LIo …)`,
`WeakPromiseBridge.lean:542`). -/
theorem GraphFabConf.realizesLDevIo (p : Pexv6) (ws : Wstate) (lb : Lbl) (l : Wlabel) :
    hlblRealizes p ws lb l → GraphFabConf.isLDev l = true → lbIsIo lb = true := by
  rintro ⟨_, _, _, hpr⟩ hl
  cases l <;> simp only [GraphFabConf.isLDev, reduceCtorEq] at hl
  simp only [projLbl, Option.some.injEq] at hpr
  subst hpr
  rfl

/-- **THE HART HALF** [R40.s2]: on a hart's emission, a block that moves the fabric or touches it
is an I/O-class row event. -/
theorem GraphFabConf.hemitfHartIo (dvi dvo : Nat → Efab) (tq : Nat → Bool) (k : Nat)
    (ws : Wstate) (row : List Lbl) (p : Pexv6) (es : List Eitem) (pfin : Pexv6) :
    hemitf dvi dvo tq k ws row p es pfin → GraphFabConf.isHart p = true →
    ∀ j, k ≤ j → j < k + row.length → (dvi j ≠ dvo j ∨ tq j = true) →
      ∃ lb, row[j - k]? = some lb ∧ lbIsIo lb = true := by
  intro h
  induction h with
  | HFnil k ws p =>
    intro _ j h1 h2
    simp at h2
    omega
  | HFone k ws lb row p ls pa da l p' es pfin b har hre hst htq _ ih =>
    intro hp j h1 h2 hj
    obtain ⟨hb, hda, hpa⟩ := GraphFabConf.admRunTHart true p (dvi k) ls pa da b har hp
    by_cases hjk : j = k
    · subst hjk
      refine ⟨lb, by simp, ?_⟩
      cases hl : GraphFabConf.isLDev l with
      | true => exact GraphFabConf.realizesLDevIo pa ws lb l hre hl
      | false =>
        exfalso
        have hpd : pdevEv pa l p' = false := by rw [GraphFabConf.pdevEvHart pa p' l hpa, hl]
        obtain ⟨hdo, -⟩ := pdevEvOk pa da l p' (dvo j) hst hpd
        rcases hj with hne | htqj
        · exact hne (by rw [hdo, hda])
        · rw [htq, hb, hpd] at htqj
          simp at htqj
    · have hp' := GraphFabConf.pstepEvHart pa da l p' (dvo k) hst hpa
      obtain ⟨lb0, hlk, hio⟩ := ih hp' j (by omega) (by simp at h2; omega) hj
      refine ⟨lb0, ?_, hio⟩
      rw [show j - k = (j - (k + 1)) + 1 by omega, List.getElem?_cons_succ]
      exact hlk
  | HFpair k ws lb row p ls1 pa da l1 pm dm ls2 pm2 dm2 l2 p' es pfin b1 b2 har1 hre hst1 har2
      hst2 htq _ ih =>
    intro hp j h1 h2 hj
    obtain ⟨aq, rl, base, tvs, data, asrc1, asrc2, vsrc2, rfl, rfl, -, -, -⟩ := hre
    obtain ⟨hb1, hda, hpa⟩ := GraphFabConf.admRunTHart true p (dvi k) ls1 pa da b1 har1 hp
    have hpd1 : pdevEv pa (Wlabel.LExLoad aq base tvs asrc1) pm = false := by
      rw [GraphFabConf.pdevEvHart _ _ _ hpa]; rfl
    obtain ⟨hdm, -⟩ := pdevEvOk _ _ _ _ _ hst1 hpd1
    have hpm := GraphFabConf.pstepEvHart _ _ _ _ _ hst1 hpa
    obtain ⟨hb2, hdm2, hpm2⟩ := GraphFabConf.admRunTHart false pm dm ls2 pm2 dm2 b2 har2 hpm
    have hpd2 : pdevEv pm2 (Wlabel.LExStore rl base data asrc2 vsrc2) p' = false := by
      rw [GraphFabConf.pdevEvHart _ _ _ hpm2]; rfl
    obtain ⟨hdo, -⟩ := pdevEvOk _ _ _ _ _ hst2 hpd2
    have hp' := GraphFabConf.pstepEvHart _ _ _ _ _ hst2 hpm2
    by_cases hjk : j = k
    · subst hjk
      exfalso
      rcases hj with hne | htqj
      · exact hne (by rw [hdo, hdm2, hdm, hda])
      · rw [htq, hb1, hpd1, hb2, hpd2] at htqj
        simp at htqj
    · obtain ⟨lb0, hlk, hio⟩ := ih hp' j (by omega) (by simp at h2; omega) hj
      refine ⟨lb0, ?_, hio⟩
      rw [show j - k = (j - (k + 1)) + 1 by omega, List.getElem?_cons_succ]
      exact hlk

/-- xv6's boot: rows `0 … NCPU - 1` are harts (`epsInit`, `xboot`). -/
theorem GraphFabConf.xbootHart (σ0 : WGState) (i : Nat) :
    i < NCPU → GraphFabConf.isHart (xboot σ0 i) = true := by
  intro hi
  unfold xboot epsInit
  rw [List.getElem?_append_left (by simp [cpus, hi]), List.getElem?_map]
  have hc : cpus[i]? = some ⟨i, hi⟩ := by simp [cpus, hi]
  rw [hc]
  rfl

/-- **THE DISK HALF, NAMED** [R41.4] (header): every disk-row fabric member is a RAM write or an
I/O event — on the disk program's shape, "no own-guard SKIP at the used-ELEMENT `DWriteDev`"
(its gate `phase ∧ completeOk ∧ pushOk` holds and its target is RAM).  Discharged by W14. -/
def usedElemGateOk (GF : Gfexec) : Prop :=
  ∀ k, (NCPU, k) ∈ GF.gfDev → gisWIo GF.gfGd.gdG (NCPU, k) = true

/-- **`gfDevWIoOfXv6`**: `gfDevWIo` from the conformance, the boot's hart rows and the named
disk-side hypothesis. -/
theorem gfDevWIoOfXv6 (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (GF : Gfexec) :
    gfexecConfIO boot d0 fab GF →
    (∀ i, i < NCPU → GraphFabConf.isHart (boot i) = true) →
    GF.gfGd.gdG.gxProg.length ≤ NCPU + 1 →
    usedElemGateOk GF → gfDevWIo GF := by
  rintro ⟨-, -, hbnd, hc⟩ hboot hlen hdisk ⟨i, k⟩ hmem
  by_cases hi : i = NCPU
  · subst hi
    exact hdisk k hmem
  obtain ⟨n, hn⟩ := List.mem_iff_getElem?.1 hmem
  obtain ⟨row, hrow, hlt⟩ := hbnd n i k hn
  have hiN : i < NCPU := by
    have := (List.getElem?_eq_some_iff.1 hrow).1
    omega
  obtain ⟨em, dvi, dvo, tq, hem, hiff, -, -, -⟩ := hc i row hrow
  have hem' : hemitf dvi dvo tq 0 wsInit row (boot i) em.emItems em.emFin := hem
  have hio : ∀ lb, row[k]? = some lb → lbIsIo lb = true → gisWIo GF.gfGd.gdG (i, k) = true := by
    intro lb hlk hlb
    have : gisIo GF.gfGd.gdG (i, k) = true := by
      unfold gisIo gxLbl
      rw [hrow]
      simp only [Option.bind_some, hlk]
      exact hlb
    simp [gisWIo, this]
  rcases (hiff k hlt).1 hmem with h | h | h
  · simp [gisWIo, h]
  · obtain ⟨lb, hlk, hlb⟩ := GraphFabConf.hemitfHartIo _ _ _ _ _ _ _ _ _ hem' (hboot i hiN) k
      (Nat.zero_le _) (by omega) (Or.inl h)
    rw [Nat.sub_zero] at hlk
    exact hio lb hlk hlb
  · obtain ⟨lb, hlk, hlb⟩ := GraphFabConf.hemitfHartIo _ _ _ _ _ _ _ _ _ hem' (hboot i hiN) k
      (Nat.zero_le _) (by omega) (Or.inr h)
    rw [Nat.sub_zero] at hlk
    exact hio lb hlk hlb

/-- **`fconfTraceRealizeIO` on an xv6 bundle**: its premise list with `gfDevWIo` DISCHARGED —
what remains is `gdiskRead14` (supplied by W13 (K)'s normalization), the trusted `ioResidueGmo`,
and the named `usedElemGateOk` (W14) [R41.4]. -/
theorem fconfTraceRealizeIOXv6 (σ0 : WGState) (fab : Nat → Efab) (GF : Gfexec) (N : Nat) :
    rvwmoMinusConsistent GF.gfGd.gdG → grule14 GF.gfGd.gdG → ioResidueGmo GF →
    gdiskRead14 GF.gfGd.gdG →
    gfexecConfIO (xboot σ0) (efInit σ0.wgdev) fab GF →
    GF.gfGd.gdG.gxProg.length ≤ NCPU + 1 →
    usedElemGateOk GF →
    GF.gfGd.gdG.gxProg.length ≤ N →
    srvwmoConsistent (linCandIO GF.gfGd.gdG) ∧
    (linCandIO GF.gfGd.gdG).cdImg = GF.gfGd.gdG.gxImg ∧
    trDevOrdered GF (linCandIO GF.gfGd.gdG) := by
  intro hc h14 hres hdr hconf hlen hgate hN
  have hwio := gfDevWIoOfXv6 _ _ fab GF hconf (GraphFabConf.xbootHart σ0) hlen hgate
  obtain ⟨hsr, himg, -, -, hord, -⟩ :=
    fconfTraceRealizeIO (xboot σ0) (efInit σ0.wgdev) fab GF N hc h14 hres hdr hconf hwio hN
  exact ⟨hsr, himg, hord⟩

end Weak
