/-
Weak: **THE BOUNDARY SEGMENT** (spike S3c): a `wpd` for the stretch from the instruction
boundary `riscvStep tick` up to the FETCH's `memRead` node, which contains the interrupt
check's `regRead sig_seip` — the one node `AxRunClose`'s bisimulation excludes.

Rocq: `iris/AxBoundaryWpd.v` @ xxvzwolszwmp.

## The Rocq header, in substance

THE SHAPE OF THE ARGUMENT ("finite product", made cheap by one observation): rv64d reads
`sig_seip` at exactly ONE site per instruction (`external_interrupts_pending`, through
`getPendingSet`).  So the segment splits at that node `n0`:
  - BEFORE `n0`: a `gstep` run (every node `anodeOk`); `AxRunClose`'s `Pbefore n0` is closed
    under steps and wire flips, exit `Qat n0`;
  - AT `n0` (up to `aeqv`): the read answers from the CURRENT register file; for EVERY answer
    `v` the continuation `k0 v` must have a `gstep` run to a fetch node;
  - AFTER `n0`: `Pbefore q` already quantifies over the representative, so ALL branches live in
    ONE invariant — no product construction.
`P := Pbefore n0 ∨ Qat n0 ∨ PbS Qs`, `Q := QaS Qs` (`Qs` a SET of fetch nodes).

§1 `wpdOfSeipSplit`: the generic lemma, via `wpdOfClosedRun` at `MaybeStuck`, row end
CALLER-SUPPLIED.  §2 `n0OkSeipRead`: the premise at the real node shape (`regRead sig_seip`).
§3 `gstepRd`/`gstepWr`/`gstepOfPnode` (one-node `gstep`s) and `erunGstepToMemread`: the
footprint evaluator `erun` (which observes register reads, unlike `execEff`) supplies
`anodeOk`.  §4 `erd` (`erun` that STOPS at the first RAM read — instruction-independent) and
its bridge `erdGstep`.  §5 `wpdBoundaryErd`: THE BOUNDARY WPd from two model-side facts (a
`gstep` run to `n0`, and an `erd` fact per answer).

NOT HERE (the spike's finding): those two model-side facts for `riscvStep tick` under the M-mode
tower (the "mirror gap" `AxCjrWpd` records).

## Deviations from Rocq

1. THE PIN SET (`AxRunClose` deviation 1).  `nodeOk` excludes `.regRead` of BOTH pins
   (`AxRunClose.pinReg r := r = sig_seip ∨ r = sig_meip`; Rocq `seip_reg`).  So `gstepRd`
   takes `¬ AxRunClose.pinReg r` (Rocq `¬ seip_reg r`), and `erunGstepToMemread`, `erdGstep`,
   `wpdBoundaryErd` take BOTH `Register.sig_seip ∉ Dr` and `Register.sig_meip ∉ Dr` (Rocq: only
   `sig_seip ∉ Dr`).  The split node `n0` stays the `sig_seip` read (`seipNode`).
2. lean-sail's `regRead` has no `direct` flag: `seipNode`, `n0OkSeipRead`, `gstepRd`,
   `gstepWr`, `wpdBoundaryErd` drop Rocq's `dir` argument.  `memRead` carries the VA width
   `va`: `erunGstepToMemread` and `ramRdNode` also exist it.
3. O2 STAGE C: no oracle parameters (`T`, `img`) — `pbSStep`/`pseipHclos` quantify the row and
   the label only, `n0Ok` speaks of `pstepProg` over an `Efab`.  `dev0_state` ↦
   `OpaxWit.wtD0` (an `Efab`; its `efDev` in `pnodeStep`).  `gstepOfPnode` also takes the
   barrier output `obar` of `pnodeStep` (AxRunClose deviation 4).
4. Vocabulary (as `WeakEvFunnel` deviation 1): `gset register` ↦ `List Register`, `M unit` ↦
   `SailM Unit`, `mstate` ↦ `ExecSt` (`sregs` ↦ `regs`), `register_lookup r rs` ↦ `rs r`,
   `register_set` ↦ `RegFile.set`, `oib32` ↦ `Ibch`, `ib_rd` ↦ `ibRd`, `dev_addr` ↦ `devAddr`,
   `default x o` ↦ `o.getD x`, `Arch.reg_type sig_seip` ↦ `RegisterType Register.sig_seip`.
   Rocq's `erd` arms are lean-sail's `Outcome` constructors listed exhaustively (as `erun`).
5. `pseipHnord`: the `axirisG Σ` section context is unused by the statement and dropped (as
   AxRunClose deviation 5).  `invGS_gen HasNoLc Σ` ↦ `[InvGS_gen hlc GF]` (any `hlc`);
   `A -∗ B` ↦ `⊢ A -∗ B`.

Q7 (owner ruling, `notes/weak-port-q7-sfence.md` route (a), Lean-only): the local evaluator `erd` returns `none` at an SFENCE.VMA announce (`erdGstep` reads the sfence-freedom off it); `erunGstepToMemread` (over `WeakEvFunnel.erun`, not local) takes `WeakEvLang.noSfAnn m t`.

**Rocq → Lean name map.**  `tc_of_step_rtc` `tcOfStepRtc`, `PbS` `PbS`, `QaS` `QaS`, `Pseip`
`Pseip`, `n0_ok` `n0Ok`, `pbS_step` `pbSStep`, `pseip_hclos` `pseipHclos`, `pbefore_wire`
`pbeforeWire`, `pseip_hwire` `pseipHwire`, `pseip_hnord` `pseipHnord`, `wpd_of_seip_split`
`wpdOfSeipSplit`, `seip_node` `seipNode`, `n0_ok_seip_read` `n0OkSeipRead`,
`erw_label_lb_admin'` `erwLabelLbAdmin'`, `gstep_rd` `gstepRd`, `gstep_wr` `gstepWr`,
`gstep_of_pnode` `gstepOfPnode`, `erun_gstep_to_memread` `erunGstepToMemread`, `erd` `erd`,
`ram_rd_node` `ramRdNode`, `erd_gstep` `erdGstep`, `erd_exit` `erdExit`, `wpd_boundary_erd`
`wpdBoundaryErd`.

**Dropped:** nothing (23 Rocq definitions/lemmas; Lean 23).  **Not ported:** the
`Print Assumptions` block (the lint's axiom check covers it).
-/
import Weak.AxRunClose
import Weak.WeakEvFunnel

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std Iris.Std.PartialMap MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D
open Wlabel

/-! # 0. A relation fact -/

theorem tcOfStepRtc {A : Type _} {R : A → A → Prop} {x y z : A} :
    R x y → rtc R y z → tc R x z :=
  fun h1 h2 => tc_rtc_r (tc_once h1) h2

/-! # 1. The generic split at the one wire-read node -/

/-- Before some exit node of the SET `Qs`. -/
def PbS (Qs : Athread → Prop) (s : Athread) : Prop := ∃ q, Qs q ∧ Pbefore q s

/-- At some exit node of `Qs` (up to `aeqv`). -/
def QaS (Qs : Athread → Prop) (s : Athread) : Prop := ∃ q, Qs q ∧ Qat q s

/-- The invariant: before `n0`, at `n0` (up to `aeqv`), or before a target. -/
def Pseip (n0 : Athread) (Qs : Athread → Prop) (s : Athread) : Prop :=
  Pbefore n0 s ∨ Qat n0 s ∨ PbS Qs s

/-- The premise at `n0`: every program step from any state `peqv` to `n0` is `LSilent` and
lands before or at a target (same row position). -/
def n0Ok (n0 : Athread) (Qs : Athread → Prop) : Prop :=
  ∀ (p : Pexv6) (d : Efab) (l : Wlabel) (p' : Pexv6) (d' : Efab),
    peqv p n0.atP → pstepProg p d l p' d' →
    l = LSilent ∧ (PbS Qs ⟨p', n0.atK⟩ ∨ QaS Qs ⟨p', n0.atK⟩)

theorem pbSStep (Qs : Athread → Prop) (row : List Lbl) (s1 : Athread) (l : Wlabel)
    (s2 : Athread) :
    PbS Qs s1 → AxOpsem.astepProg row s1 l s2 →
    wlWdata l = none ∧ s2.atK = s1.atK ∧ (PbS Qs s2 ∨ QaS Qs s2) := by
  rintro ⟨q, hq, H⟩ hst
  obtain ⟨hw, hk, H'⟩ := runCloseStep q row s1 l s2 H hst
  refine ⟨hw, hk, ?_⟩
  rcases H' with H' | H'
  · exact .inl ⟨q, hq, H'⟩
  · exact .inr ⟨q, hq, H'⟩

theorem pseipHclos (n0 : Athread) (Qs : Athread → Prop) (Hn0 : n0Ok n0 Qs) (row : List Lbl)
    (s1 : Athread) (l : Wlabel) (s2 : Athread) :
    Pseip n0 Qs s1 → AxOpsem.astepProg row s1 l s2 →
    wlWdata l = none ∧ s2.atK = s1.atK ∧ (Pseip n0 Qs s2 ∨ QaS Qs s2) := by
  intro H hst
  rcases H with H | H | H
  · obtain ⟨hw, hk, H'⟩ := runCloseStep n0 row s1 l s2 H hst
    refine ⟨hw, hk, ?_⟩
    rcases H' with H' | H'
    · exact .inl (.inl H')
    · exact .inl (.inr (.inl H'))
  · obtain ⟨hk0, hp0⟩ := H
    obtain ⟨d, d', hps⟩ := astepProgPstep row _ _ _ hst
    obtain ⟨rfl, HP⟩ := Hn0 _ _ _ _ _ hp0 hps
    have hk := astepProgAdminK' row _ _ _ hst trivial
    refine ⟨rfl, hk, ?_⟩
    obtain ⟨p2, k2⟩ := s2
    simp only at hk
    rw [hk, hk0]
    rcases HP with HP | HP
    · exact .inl (.inr (.inr HP))
    · exact .inr HP
  · obtain ⟨hw, hk, H'⟩ := pbSStep Qs row s1 l s2 H hst
    refine ⟨hw, hk, ?_⟩
    rcases H' with H' | H'
    · exact .inl (.inr (.inr H'))
    · exact .inr H'

theorem pbeforeWire (q s1 s2 : Athread) : Pbefore q s1 → awire s1 s2 → Pbefore q s2 := by
  rintro ⟨t, heq, htc⟩ hw
  exact ⟨t, aeqvTrans _ _ _ (awireAeqv _ _ hw) heq, htc⟩

theorem pseipHwire (n0 : Athread) (Qs : Athread → Prop) (s1 s2 : Athread) :
    Pseip n0 Qs s1 → awire s1 s2 → Pseip n0 Qs s2 ∨ QaS Qs s2 := by
  intro H hw
  refine .inl ?_
  rcases H with H | H | ⟨q, hq, H⟩
  · exact .inl (pbeforeWire _ _ _ H hw)
  · exact .inr (.inl (aeqvTrans _ _ _ (awireAeqv _ _ hw) H))
  · exact .inr (.inr ⟨q, hq, pbeforeWire _ _ _ H hw⟩)

theorem pseipHnord (i : Agent) (n0 : Athread) (Qs : Athread → Prop) (Hn0 : n0Ok n0 Qs)
    (GD : Gdexec) (s1 : Athread) (id : AidentT) (K : List (BitVec 8) → Athread) :
    Pseip n0 Qs s1 → ¬ areadStep (AxOpsem.grow GD i) s1 id K := by
  intro H
  rcases H with H | H | ⟨q, -, H⟩
  · exact runCloseHnord i n0 GD s1 id K H
  · rintro ⟨lb, -, -, hrd, HK⟩
    obtain ⟨l, d, d', hl, -, hps, -⟩ :=
      HK (List.replicate (aidentN id) (0#8)) List.length_replicate
    obtain ⟨rfl, -⟩ := Hn0 _ _ _ _ _ H.2 hps
    rw [← hl] at hrd
    simp [wlRd] at hrd
  · exact runCloseHnord i q GD s1 id K H

section wpdSplit
variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF] [Axpol]

/-- THE GENERIC BOUNDARY LEMMA.  `Hrun0`: the wire-free prefix to the read node `n0`.  `Hn0`:
every answer of the read lands before or at a target.  Row end: caller-supplied. -/
theorem wpdOfSeipSplit (i : Agent) (Φ : Athread → IProp GF) (s0 n0 : Athread)
    (Qs : Athread → Prop) (Hrun0 : tc gstep s0 n0) (Hn0 : n0Ok n0 Qs) :
    ⊢ ((∀ s2, ⌜QaS Qs s2⌝ -∗ wpd .MaybeStuck i s2 Φ) ∧
       (∀ (GD : Gdexec) s1, ⌜Pseip n0 Qs s1⌝ -∗ ⌜s1.atK = (AxOpsem.grow GD i).length⌝ -∗
          postLifting Φ i s1)) -∗
      wpd .MaybeStuck i s0 Φ := by
  have hok : anodeOk s0 := by
    rcases AxWpdLift.tcInvL Hrun0 with h | ⟨_, h, -⟩
    · exact h.1
    · exact h.1
  have HP : Pseip n0 Qs s0 := .inl ⟨s0, AxRunClose.aeqvReflOk s0 hok, Hrun0⟩
  iintro R
  iapply (wpdOfClosedRun .MaybeStuck i (Pseip n0 Qs) (QaS Qs) Φ
    (fun s1 _ => (progressOblMaybestuck (GF := GF) i s1).2)
    (fun GD s1 id K h => pseipHnord i n0 Qs Hn0 GD s1 id K h)
    (fun GD s1 l s2 h1 h2 => pseipHclos n0 Qs Hn0 _ s1 l s2 h1 h2)
    (pseipHwire n0 Qs)) $$ %s0 %HP R

end wpdSplit

/-! # 2. `n0Ok` at the real node shape

The read node itself: `regRead sig_seip` answers from the CURRENT register file, keeps the
registers, and records the register NAME (not the value) in the info bank — so the post-read
states of the different answers differ ONLY in the monad term `k0 v`. -/

def seipNode (cpu : CPU) (k0 : RegisterType Register.sig_seip → SailM Unit) (rs1 : RegFile)
    (ib1 : Ibch) (kk : Nat) : Athread :=
  ⟨.PHart cpu (.impure (.ok (.regRead Register.sig_seip)) k0) rs1 none ib1, kk⟩

theorem n0OkSeipRead (cpu : CPU) (k0 : RegisterType Register.sig_seip → SailM Unit)
    (rs1 : RegFile) (ib1 : Ibch) (kk : Nat) (Qs : Athread → Prop) :
    (∀ v, ∃ q, Qs q ∧
       rtc gstep ⟨.PHart cpu (k0 v) rs1 none (ibRd ib1 Register.sig_seip), kk⟩ q) →
    n0Ok (seipNode cpu k0 rs1 ib1 kk) Qs := by
  intro Hk p d l p' d' heq hst
  match p, p', heq, hst with
  | .PHart c m rs fn ib, .PHart c' m' rs' fn' ib', heq, hst =>
    obtain ⟨rfl, rfl, rfl, rfl, hag⟩ := heq
    obtain ⟨rfl, ors, oib, obar, rfl, rfl, hn, -⟩ := hst
    obtain ⟨rfl, rfl, rfl, rfl, -, rfl, -⟩ := hn
    refine ⟨rfl, ?_⟩
    obtain ⟨q, hq, hr⟩ := Hk (rs Register.sig_seip)
    rcases rtc_inv hr with rfl | ⟨y, hy, hr'⟩
    · exact .inr ⟨_, hq, rfl, rfl, rfl, rfl, rfl, hag⟩
    · exact .inl ⟨q, hq, ⟨.PHart _ (k0 (rs Register.sig_seip)) rs1 none (ibRd ib Register.sig_seip), kk⟩,
        ⟨rfl, rfl, rfl, rfl, rfl, hag⟩, tcOfStepRtc hy hr'⟩
  | .PDisk _, _, heq, _ => exact (heq : False).elim
  | .PHart .., .PDisk _, _, hst => exact (hst : False).elim

/-! # 3. Walking helpers -/

theorem erwLabelLbAdmin' (ek : ErwKind) : lbAdmin true (erwLabel ek) := by
  cases ek <;> trivial

/-- One admin step at a `nodeOk` node is a `gstep`. -/
theorem gstepOfPnode (cpu : CPU) (m : SailM Unit) (rs : RegFile) (ib : Ibch) (kk : Nat)
    (l : Wlabel) (m' : SailM Unit) (ors : Option RegFile) (oib : Option Ibch)
    (obar : Option barrier_kind) :
    pnodeStep m rs ib OpaxWit.wtD0.efDev l m' ors none OpaxWit.wtD0.efDev oib obar →
    nodeOk m → lbAdmin true l →
    gstep ⟨.PHart cpu m rs none ib, kk⟩ ⟨.PHart cpu m' (ors.getD rs) none (oib.getD ib), kk⟩ := by
  intro hn hok hadm
  exact ⟨hok, rfl, [], l,
    .AStepAdmin _ _ OpaxWit.wtD0 l _ OpaxWit.wtD0 hadm ⟨rfl, ors, oib, obar, rfl, rfl, hn, rfl⟩⟩

theorem gstepRd (cpu : CPU) (r : Register) (k : RegisterType r → SailM Unit) (rs : RegFile)
    (ib : Ibch) (kk : Nat) :
    ¬ AxRunClose.pinReg r →
    gstep ⟨.PHart cpu (.impure (.ok (.regRead r)) k) rs none ib, kk⟩
      ⟨.PHart cpu (k (rs r)) rs none (ibRd ib r), kk⟩ := by
  intro hr
  exact gstepOfPnode cpu _ rs ib kk LSilent _ none (some (ibRd ib r)) none
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ hr trivial

theorem gstepWr (cpu : CPU) (r : Register) (v : RegisterType r) (k : PUnit → SailM Unit)
    (rs : RegFile) (ib : Ibch) (kk : Nat) :
    gstep ⟨.PHart cpu (.impure (.ok (.regWrite r v)) k) rs none ib, kk⟩
      ⟨.PHart cpu (k PUnit.unit) (rs.set r v) none ib, kk⟩ :=
  gstepOfPnode cpu _ rs ib kk _ _ (some (rs.set r v)) none none
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ trivial (erwLabelLbAdmin' _)

/-- THE BRIDGE: the footprint evaluator `erun Dr Dw` (fails at any `regRead` outside `Dr`, at
MMIO, at `choose`/`memWrite`/`barrier`) with the pins `∉ Dr` yields a `gstep` run — every node
`anodeOk` — to the first RAM read. -/
theorem erunGstepToMemread (Dr Dw : List Register) (m : SailM Unit) :
    Register.sig_seip ∉ Dr → Register.sig_meip ∉ Dr →
    ∀ (t : ExecSt) (ib : Ibch) (ak : AkInfo) (pa : PAddr) (n : Nat) (t' : ExecSt)
      (es : List Weff),
      erun Dr Dw m t = some (PUnit.unit, t', .WEread ak pa n :: es) →
      WeakEvLang.noSfAnn m t →
    ∀ (cpu : CPU) (kk : Nat),
      ∃ (t2 : ExecSt) (ib2 : Ibch) (va : Nat)
        (req : Mem_read_request n va Arch.pa Arch.translation Arch.arch_ak)
        (KK : Result (BitVec (8 * n) × Option Bool) Arch.abort → SailM Unit),
        classify req.access_kind = ak ∧ req.pa = pa ∧ devAddr pa = false ∧ t2.mem = t.mem ∧
        erun Dr Dw (.impure (.ok (.memRead n va req)) KK) t2
          = some (PUnit.unit, t', .WEread ak pa n :: es) ∧
        rtc gstep ⟨.PHart cpu m t.regs none ib, kk⟩
          ⟨.PHart cpu (.impure (.ok (.memRead n va req)) KK) t2.regs none ib2, kk⟩ := by
  intro hs hm
  induction m with
  | pure x =>
    intro t ib ak pa n t' es hex
    simp [erun] at hex
  | impure call k ih =>
    intro t ib ak pa n t' es hex hsf cpu kk
    cases call with
    | error e => simp [erun] at hex
    | ok o =>
      cases o
      case regRead r =>
        by_cases hr : r ∈ Dr
        · simp only [erun, hr, ↓reduceIte] at hex
          simp only [WeakEvLang.noSfAnn] at hsf
          obtain ⟨t2, ib2, va, req, KK, h1, h2, h3, h4, h5, hrun⟩ :=
            ih _ t (ibRd ib r) _ _ _ _ _ hex hsf cpu kk
          refine ⟨t2, ib2, va, req, KK, h1, h2, h3, h4, h5, rtc_l ?_ hrun⟩
          refine gstepRd cpu r k t.regs ib kk ?_
          rintro (rfl | rfl)
          · exact hs hr
          · exact hm hr
        · simp [erun, hr] at hex
      case regWrite r v =>
        by_cases hr : r ∈ Dw
        · simp only [erun, hr, ↓reduceIte] at hex
          simp only [WeakEvLang.noSfAnn] at hsf
          obtain ⟨t2, ib2, va, req, KK, h1, h2, h3, h4, h5, hrun⟩ :=
            ih _ _ ib _ _ _ _ _ hex hsf cpu kk
          exact ⟨t2, ib2, va, req, KK, h1, h2, h3, h4, h5,
            rtc_l (gstepWr cpu r v k t.regs ib kk) hrun⟩
        · simp [erun, hr] at hex
      case memRead n' va req =>
        have hex0 := hex
        by_cases hd : devAddr req.pa = true
        · simp [erun, hd] at hex
        · cases hrb : bmRead t.mem req.pa n' with
          | none => simp [erun, hd, hrb] at hex
          | some w =>
            simp only [erun, hd, hrb, Bool.false_eq_true, ↓reduceIte] at hex
            obtain ⟨es0, -, heq⟩ := Weff.consEqSome.1 hex
            injection heq with heq1 _
            injection heq1 with hak hpa hn
            subst hak hpa hn
            exact ⟨t, ib, va, req, k, rfl, rfl, by simpa using hd, rfl, hex0, rtc_refl _⟩
      case instrAnnounce nw w =>
        simp only [erun] at hex
        simp only [WeakEvLang.noSfAnn] at hsf
        obtain ⟨hsw, hsf⟩ := hsf
        obtain ⟨t2, ib2, va, req, KK, h1, h2, h3, h4, h5, hrun⟩ :=
          ih _ t (ibAnn (ibOfBvn w)) _ _ _ _ _ hex hsf cpu kk
        exact ⟨t2, ib2, va, req, KK, h1, h2, h3, h4, h5,
          rtc_l (gstepOfPnode cpu _ t.regs ib kk _ _ none (some (ibAnn (ibOfBvn w))) none
            ⟨(annLabelNot hsw).symm, rfl, rfl, rfl, rfl, rfl, rfl⟩ trivial rfl) hrun⟩
      all_goals first
        | (simp [erun] at hex; done)
        | (simp only [erun] at hex
           simp only [WeakEvLang.noSfAnn] at hsf
           obtain ⟨t2, ib2, va, req, KK, h1, h2, h3, h4, h5, hrun⟩ :=
             ih _ t ib _ _ _ _ _ hex hsf cpu kk
           exact ⟨t2, ib2, va, req, KK, h1, h2, h3, h4, h5,
             rtc_l (gstepOfPnode cpu _ t.regs ib kk _ _ none none none
               ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ trivial trivial) hrun⟩)

/-! # 4. `erd`: the footprint evaluator UP TO THE FIRST RAM READ

`erun` runs to the END of the monad, so it covers decode + execute + tick of ONE instruction.
The boundary segment must be instruction-independent, so its model-side fact is stated with
`erd`: `erun`'s arms, except that a RAM `memRead` STOPS and returns the node itself. -/

def erd (Dr Dw : List Register) : SailM Unit → ExecSt → Option (SailM Unit × ExecSt)
  | .pure _, _ => none
  | .impure (.error _) _, _ => none
  | .impure (.ok o) k, s =>
    match o, k with
    | .regRead r, k => if r ∈ Dr then erd Dr Dw (k (s.regs r)) s else none
    | .regWrite r v, k => if r ∈ Dw then erd Dr Dw (k PUnit.unit) (s.setReg r v) else none
    | .memRead n va req, k =>
      if devAddr req.pa then none else some (.impure (.ok (.memRead n va req)) k, s)
    | .memWrite .., _ => none
    | .barrier _, _ => none
    | .cacheOp _, k => erd Dr Dw (k ()) s
    | .tlbi _, k => erd Dr Dw (k ()) s
    | .translationStart _, k => erd Dr Dw (k ()) s
    | .translationEnd _, k => erd Dr Dw (k ()) s
    | .takeException _, k => erd Dr Dw (k ()) s
    | .returnException _, k => erd Dr Dw (k ()) s
    | .cycleCount, k => erd Dr Dw (k ()) s
    | .getCycleCount, k => erd Dr Dw (k (0 : Nat)) s
    | .message _, k => erd Dr Dw (k ()) s
    -- Q7: an sfence.vma announce is the marker (a graph event): stop
    | .instrAnnounce n w, k => if sfAnnB n w then none else erd Dr Dw (k ()) s
    | .branchAnnounce _ _, k => erd Dr Dw (k ()) s
    | .choose _, _ => none
    | .readRam .., _ => none
    | .writeRam .., _ => none

/-- The RAM-read nodes (the fetch, when `erd` starts inside the boundary segment). -/
def ramRdNode (cpu : CPU) (kk : Nat) (q : Athread) : Prop :=
  ∃ (n va : Nat) (req : Mem_read_request n va Arch.pa Arch.translation Arch.arch_ak)
    (KK : Result (BitVec (8 * n) × Option Bool) Arch.abort → SailM Unit) (rs2 : RegFile)
    (ib2 : Ibch),
    q = ⟨.PHart cpu (.impure (.ok (.memRead n va req)) KK) rs2 none ib2, kk⟩ ∧
    devAddr req.pa = false

theorem erdGstep (Dr Dw : List Register) (m : SailM Unit) :
    Register.sig_seip ∉ Dr → Register.sig_meip ∉ Dr →
    ∀ (t : ExecSt) (ib : Ibch) (q : SailM Unit) (t2 : ExecSt),
      erd Dr Dw m t = some (q, t2) →
    ∀ (cpu : CPU) (kk : Nat), ∃ ib2,
      ramRdNode cpu kk ⟨.PHart cpu q t2.regs none ib2, kk⟩ ∧
      t2.mem = t.mem ∧
      rtc gstep ⟨.PHart cpu m t.regs none ib, kk⟩ ⟨.PHart cpu q t2.regs none ib2, kk⟩ := by
  intro hs hm
  induction m with
  | pure x =>
    intro t ib q t2 hex
    simp [erd] at hex
  | impure call k ih =>
    intro t ib q t2 hex cpu kk
    cases call with
    | error e => simp [erd] at hex
    | ok o =>
      cases o
      case regRead r =>
        by_cases hr : r ∈ Dr
        · simp only [erd, hr, ↓reduceIte] at hex
          obtain ⟨ib2, h1, h2, hrun⟩ := ih _ t (ibRd ib r) _ _ hex cpu kk
          refine ⟨ib2, h1, h2, rtc_l ?_ hrun⟩
          refine gstepRd cpu r k t.regs ib kk ?_
          rintro (rfl | rfl)
          · exact hs hr
          · exact hm hr
        · simp [erd, hr] at hex
      case regWrite r v =>
        by_cases hr : r ∈ Dw
        · simp only [erd, hr, ↓reduceIte] at hex
          obtain ⟨ib2, h1, h2, hrun⟩ := ih _ _ ib _ _ hex cpu kk
          exact ⟨ib2, h1, h2, rtc_l (gstepWr cpu r v k t.regs ib kk) hrun⟩
        · simp [erd, hr] at hex
      case memRead n va req =>
        by_cases hd : devAddr req.pa = true
        · simp [erd, hd] at hex
        · simp only [erd, hd, Bool.false_eq_true, ↓reduceIte, Option.some.injEq,
            Prod.mk.injEq] at hex
          obtain ⟨rfl, rfl⟩ := hex
          exact ⟨ib, ⟨n, va, req, k, _, ib, rfl, by simpa using hd⟩, rfl, rtc_refl _⟩
      case instrAnnounce nw w =>
        cases hsw : sfAnnB nw w <;>
          simp only [erd, hsw, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at hex
        obtain ⟨ib2, h1, h2, hrun⟩ := ih _ t (ibAnn (ibOfBvn w)) _ _ hex cpu kk
        exact ⟨ib2, h1, h2,
          rtc_l (gstepOfPnode cpu _ t.regs ib kk _ _ none (some (ibAnn (ibOfBvn w))) none
            ⟨(annLabelNot hsw).symm, rfl, rfl, rfl, rfl, rfl, rfl⟩ trivial rfl) hrun⟩
      all_goals first
        | (simp [erd] at hex; done)
        | (simp only [erd] at hex
           obtain ⟨ib2, h1, h2, hrun⟩ := ih _ t ib _ _ hex cpu kk
           exact ⟨ib2, h1, h2,
             rtc_l (gstepOfPnode cpu _ t.regs ib kk _ _ none none none
               ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ trivial trivial) hrun⟩)

/-! # 5. The boundary WPd from ONE `erd` fact per answer

The EXIT SET is `erdExit`: exactly the nodes `erd` RETURNS for some answer `v` (with the
`ramRdNode` shape facts kept as a conjunct), so the caller's continuation obligation is about
THOSE fetch nodes only. -/

def erdExit (Dr Dw : List Register) (cpu : CPU)
    (k0 : RegisterType Register.sig_seip → SailM Unit) (t1 : ExecSt) (kk : Nat)
    (q : Athread) : Prop :=
  ∃ v qm t2 ib2,
    erd Dr Dw (k0 v) t1 = some (qm, t2) ∧
    q = ⟨.PHart cpu qm t2.regs none ib2, kk⟩ ∧
    ramRdNode cpu kk q

section wpdBoundary
variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF] [Axpol]

theorem wpdBoundaryErd (i : Agent) (Φ : Athread → IProp GF) (s0 : Athread) (cpu : CPU)
    (k0 : RegisterType Register.sig_seip → SailM Unit) (t1 : ExecSt) (ib1 : Ibch) (kk : Nat)
    (Dr Dw : List Register)
    (Hseip : Register.sig_seip ∉ Dr) (Hmeip : Register.sig_meip ∉ Dr)
    (Hrun0 : tc gstep s0 (seipNode cpu k0 t1.regs ib1 kk))
    (Herd : ∀ v, ∃ q t2, erd Dr Dw (k0 v) t1 = some (q, t2)) :
    ⊢ ((∀ s2, ⌜QaS (erdExit Dr Dw cpu k0 t1 kk) s2⌝ -∗ wpd .MaybeStuck i s2 Φ) ∧
       (∀ (GD : Gdexec) s1,
          ⌜Pseip (seipNode cpu k0 t1.regs ib1 kk) (erdExit Dr Dw cpu k0 t1 kk) s1⌝ -∗
          ⌜s1.atK = (AxOpsem.grow GD i).length⌝ -∗ postLifting Φ i s1)) -∗
      wpd .MaybeStuck i s0 Φ := by
  refine wpdOfSeipSplit i Φ s0 _ _ Hrun0 (n0OkSeipRead cpu k0 t1.regs ib1 kk _ ?_)
  intro v
  obtain ⟨q, t2, he⟩ := Herd v
  obtain ⟨ib2, hq, -, hr⟩ :=
    erdGstep Dr Dw (k0 v) Hseip Hmeip t1 (ibRd ib1 Register.sig_seip) q t2 he cpu kk
  exact ⟨_, ⟨v, q, t2, ib2, he, rfl, hq⟩, hr⟩

end wpdBoundary

end Weak
