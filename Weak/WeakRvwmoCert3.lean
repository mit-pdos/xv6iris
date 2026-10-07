/-
Weak: **B2e-3b slice 3c(a) — the floor, discharged** (§1–§4; §5–§6 are `WeakRvwmoCert3b`).

Rocq: `iris/WeakRvwmoCert3.v` @ xxvzwolszwmp.

## The Rocq header, in substance

`WeakRvwmoCert2.certSegment` certifies a hart's segment against a policy whose read clause owes
`floorOk` (N-1).  `WeakRvwmoFloor.floorOfGraph` discharges it for a G-TRACE PREFIX; a certified
run is not one, because a WITNESS read carries the candidate log's latest bytes.  This file
states the CERTIFIED correspondence (`CtracePrefix`: G's label at a true position, a
`latestReadLbl` at a witness, a poisoned third arm), the witness step of the floor invariant
(`cinvStepWit`), the replay and the floor over a certified prefix (`cinvReplay`,
`floorOfCgraph`, `certFloorOk`, `certReadInLog'`, `cpolRead`), the context-carrying iteration
`certSegment'` (§3.4), and obligation (O-1), the fused exclusive pair (`cblkp`, `cpolp`,
`certRmwLatest`/`certRmwOk`: an RMW's G-source IS the log's latest, so the pair owes no floor;
`certBlockPair`).  The two side conditions a witness costs are (W-a) `WPolocClosed` and (W-b)
`witFenceUb` (fence-guarded); at a poisoned position both are `poisOkAt`/`poisOkHart`.
§5 (re-convergence at the instruction boundary), §5b (`certSegment''`) and §6 (non-vacuity) are
in `Weak/WeakRvwmoCert3b.lean` (the planned split).

## Deviations from Rocq

1. NAMES: the tree's camelCase (map below); `S k` ↦ `k + 1`; `l !! n` ↦ `l[n]?`;
   `cd_log c (length (cd_tr c))` ↦ `cdLog c c.cdTr.length`; `WeakAxiomatic.acc_addr` ↦ `accAddr`;
   `M unit` ↦ `SailM Unit`, `regstate` ↦ `RegFile`, `oib32` ↦ `Ibch`, `wreg` ↦ `Nat`,
   `register` ↦ `Register`, `dev_state` ↦ `Efab`, `agent` ↦ `Nat` (as `WeakRvwmoCert2`);
   `EStep x lb` ↦ `⟨x, lb⟩`; `Forall2` ↦ `List.Forall₂`.  Rocq's `Notation cinv := finv` is the
   abbreviation `cinv`; Rocq's `ofence` is the local notation `Ofence`.
2. Rocq's section-free hypotheses (`Hwf`/`Hppo`/`Hlv`, `r a Hrr Hra`) are explicit parameters,
   as in `WeakRvwmoFloor`; Rocq's `Section segment'` context (`x cpu d0 T Q Ctx Cls Hpres Hpol'
   Hpolp`) is `certSegment'`'s leading parameters, in Rocq's order.
3. `cblkp`'s read/write lists are written RIGHT-associated (`rdsA ++ (rdsB ++ (rdsC ++ rdsD))`),
   Rocq's `++` association (Lean's `++` is left-associative).
4. O2 / STAGE C — THE PINNED LTS (`WeakRvwmoCert2` deviation 4): every supply is at
   `pstepPin c.cdImg pstepEv`; Stage B's `lbFetchInert` conjunct of `Hpol'` is DELETED.
   - Lean-only `WeakRvwmoCert3.cblkpG A …` (Rocq's `cblkp` with the FIRST admin stretch's
     predicate abstracted; `cblkp := cblkpG (lbAdmin true)`, definitionally Rocq's body) and the
     pinned pair block `WeakRvwmoCert3.cblkpPin im := cblkpG (WeakRvwmoCert2.lbPin im)` (the
     second stretch is `lbAdmin false`, never a fetch: `WeakRvwmoCert3.lbAdminFalsePin`);
     `cblkpPinCblkp`, `cblkpIntroPin`, `cblkpElimPin`; transports `WeakRvwmoCert3.cblkpRelpG`,
     `certBlockPairMirrorG` (Rocq's `cblkpRelp` / `certBlockPairMirror` are their instances).
   - `certBlockSnocPair` / `certBlockPair`: pinned supply, `cblkpPin c.cdImg` block.
   - `cpolp` takes and returns `cblkpPin c0.cdImg` blocks; `polStore'` and `certSegment'`'s
     `Hpol'` take and return `WeakRvwmoCert2.cblkPin c0.cdImg` blocks; `certSegment'` takes
     `WeakRvwmoCert2.esPin c.cdImg es` (after `Ctx k0 c`).
5. `polStore'`'s `lblReidxW` is `lblReidxWOf` of `polStore`'s `lblReidx` (Rocq: `by left`).
6. §8's `Print Assumptions` audit is dropped (the lint's axiom/sorry ban is the audit); §7
   (what the slice leaves open) is a Rocq comment, not ported.

**Rocq → Lean name map.**  `cd_pre` `cdPre`, `cd_pre_img` `cdPreImg`,
`cd_pre_log` `cdPreLog`, `cpois_lbl` `cpoisLbl`, `cwit_step` `cwitStep`, `cpois_step`
`cpoisStep`, `cpois_lbl_notw` `cpoisLblNotw`, `lbl_touches` `lblTouches`, `ctrace_prefix`
`CtracePrefix` (fields `ctp_img`…`ctp_log` ↦ `ctpImg`…`ctpLog`), `ctrace_prefix_of_gtrace`
`ctracePrefixOfGtrace`, `gtrace_of_ctrace_prefix` `gtraceOfCtracePrefix`, `ctp_lbl` `ctpLbl`,
`ctp_lbl_w` `ctpLblW`, `ctp_wit` `ctpWit`, `ctp_ev_eq` `ctpEvEq`, `ctp_log_writes`
`ctpLogWrites`, `ctp_log_byte` `ctpLogByte`, `W_poloc_closed` `WPolocClosed`,
`witness_not_aq` `witnessNotAq`, `cinv` `cinv`, `wit_fence_ub` `witFenceUb`, `pois_ok_at`
`poisOkAt`, `pois_ok_hart` `poisOkHart`, `pois_ok_at_of_hart` `poisOkAtOfHart`,
`cinv_step_wit` `cinvStepWit`, `cinv_replay` `cinvReplay`, `floor_of_cgraph` `floorOfCgraph`,
`cert_floor_ok` `certFloorOk`, `cert_read_in_log'` `certReadInLog'`, `cpol_ctx` `cpolCtx`,
`cpol_read` `cpolRead`, `cblkp` `cblkp`, `cblkp_intro` `cblkpIntro`, `cblkp_elim` `cblkpElim`,
`cblkp_relp` `cblkpRelp`, `cert_block_snoc_pair` `certBlockSnocPair`, `cpolp` `cpolp`,
`cblkp_rmw` `cblkpRmw`, `cblkp_is_w` `cblkpIsW`, `cpolp_of_rmwfree` `cpolpOfRmwfree`,
`pol_store'` `polStore'`, `cert_segment'` `certSegment'`, `floor_ok_of_latest`
`floorOkOfLatest`, `cert_rmw_latest` `certRmwLatest`, `cert_rmw_ok` `certRmwOk`,
`cert_block_pair_mirror` `certBlockPairMirror`, `cert_block_pair` `certBlockPair`.

**File-qualified names:** none (no name of §1–§4 is in `notes/weak-port-dupnames.json`).

**Dropped:** none (§1–§4: Rocq 47 declarations incl. the `cinv` notation; Lean 47 + 8 Lean-only
helpers of deviation 4).
-/
import Weak.WeakRvwmoFloor
import Weak.WeakRvwmoCert2

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D

/-- The parked-fence field, abbreviated (as in `WeakRvwmoCert2`). -/
local notation "Ofence" => Option (Bool × Bool × Bool × Bool)

/-! # 1. The certified correspondence -/

/-! ## 1.1 The candidate's own prefix -/

def cdPre (c : Cand) (p : Nat) : Cand := ⟨c.cdImg, c.cdTr.take p⟩

theorem cdPreImg (c : Cand) (p : Nat) : (cdPre c p).cdImg = c.cdImg := rfl

theorem cdPreLog (c : Cand) (p : Nat) : cdLogEnd (cdPre c p) = cdLog c p := by
  show trMsgs ((c.cdTr.take p).take (c.cdTr.take p).length) = trMsgs (c.cdTr.take p)
  rw [take_ge (Nat.le_refl _)]

/-! ## 1.2 `CtracePrefix` -/

/-- THE POISONED POSITION's label: the candidate's own latest-source read at some footprint. -/
def cpoisLbl (c0 : Cand) (l : Lbl) : Prop :=
  ∃ (base : Int) (n : Nat), l = latestReadLbl c0 false base n

/-- THE WITNESS SHAPE: G's own footprint, read at the candidate's latest sources. -/
def cwitStep (G : Gexec) (c : Cand) (ev : Nat → Geid) (p : Nat) (s : Estep) : Prop :=
  ∃ (base : Int) (n : Nat) (ts0 : List Nat) (vs0 : List (BitVec 8)),
    gxLbl G (ev p) = some (Lbl.LLoad false base ts0 vs0) ∧
    ts0.length = n ∧
    s.esLb = latestReadLbl (cdPre c p) false base n

def cpoisStep (G : Gexec) (c : Cand) (ev : Nat → Geid) (p : Nat) (s : Estep) : Prop :=
  (∃ lb0 : Lbl, gxLbl G (ev p) = some lb0 ∧ lbIsW lb0 = false) ∧
  cpoisLbl (cdPre c p) s.esLb ∧
  gxLbl G (ev p) ≠ some s.esLb ∧
  ¬ cwitStep G c ev p s

theorem cpoisLblNotw (c0 : Cand) (l : Lbl) : cpoisLbl c0 l → lbIsW l = false := by
  rintro ⟨base, n, rfl⟩
  rfl

/-- WHICH BYTE A LABEL'S READ HALF TOUCHES. -/
def lblTouches (l : Lbl) (a : Int) : Prop :=
  ∃ (base : Int) (ts : List Nat) (vs : List (BitVec 8)),
    lbRd l = some (base, ts, vs) ∧
    ∃ (j : Nat) (t : Nat), ts[j]? = some t ∧ accAddr base j = a

structure CtracePrefix (G : Gexec) (c : Cand) (ev : Nat → Geid) (W : Geid → Prop) : Prop where
  ctpImg : c.cdImg = G.gxImg
  ctpAg : ∀ p s, c.cdTr[p]? = some s → (ev p).1 = s.esAg
  ctpPos : ∀ p s, c.cdTr[p]? = some s → (ev p).2 = gcnt s.esAg (c.cdTr.take p)
  ctpStep : ∀ p s, c.cdTr[p]? = some s →
    (¬ W (ev p) ∧ gxLbl G (ev p) = some s.esLb) ∨
    (W (ev p) ∧ cwitStep G c ev p s) ∨
    cpoisStep G c ev p s
  ctpWix : ∀ p s, c.cdTr[p]? = some s → lbIsW s.esLb = true →
    gwix G (ev p) = (cdLog c p).length + 1
  ctpLog : ∀ s : Nat, 0 < s → s ≤ (cdLog c c.cdTr.length).length →
    ∃ w, gwriteAt G s = some w ∧ (cdLog c c.cdTr.length)[s - 1]? = gwmsg G w

/-- A witness-free certified prefix IS a G-trace prefix, and conversely. -/
theorem ctracePrefixOfGtrace (G : Gexec) (c : Cand) (ev : Nat → Geid) :
    GtracePrefix G c ev → CtracePrefix G c ev (fun _ => False) :=
  fun h => ⟨h.gtpImg, h.gtpAg, h.gtpPos, fun p s hs => .inl ⟨id, h.gtpLbl p s hs⟩, h.gtpWix,
    h.gtpLog⟩

theorem gtraceOfCtracePrefix (G : Gexec) (c : Cand) (ev : Nat → Geid) (W : Geid → Prop) :
    CtracePrefix G c ev W → (∀ p, ¬ W (ev p)) →
    (∀ p s, c.cdTr[p]? = some s → ¬ cpoisStep G c ev p s) →
    GtracePrefix G c ev := by
  intro h hno hnp
  refine ⟨h.ctpImg, h.ctpAg, h.ctpPos, ?_, h.ctpWix, h.ctpLog⟩
  intro p s hs
  rcases h.ctpStep p s hs with ⟨_, hl⟩ | ⟨hW, _⟩ | hp
  · exact hl
  · exact (hno p hW).elim
  · exact (hnp p s hs hp).elim

theorem ctpLbl (G : Gexec) (c : Cand) (ev : Nat → Geid) (W : Geid → Prop) (p : Nat) (s : Estep) :
    CtracePrefix G c ev W → c.cdTr[p]? = some s → ¬ W (ev p) → ¬ cpoisStep G c ev p s →
    gxLbl G (ev p) = some s.esLb := by
  intro h hs hnW hnp
  rcases h.ctpStep p s hs with ⟨_, hl⟩ | ⟨hW, _⟩ | hp
  · exact hl
  · exact (hnW hW).elim
  · exact (hnp hp).elim

/-- An appended WRITE is neither a witness nor poisoned, so its label IS G's. -/
theorem ctpLblW (G : Gexec) (c : Cand) (ev : Nat → Geid) (W : Geid → Prop) (p : Nat)
    (s : Estep) :
    CtracePrefix G c ev W → c.cdTr[p]? = some s → lbIsW s.esLb = true →
    gxLbl G (ev p) = some s.esLb := by
  intro h hs hw
  rcases h.ctpStep p s hs with ⟨_, hl⟩ | ⟨_, _, _, _, _, _, _, hlb⟩ | ⟨_, hpl, _⟩
  · exact hl
  · rw [hlb] at hw
    simp [latestReadLbl, lbIsW] at hw
  · rw [cpoisLblNotw _ _ hpl] at hw
    cases hw

theorem ctpWit (G : Gexec) (c : Cand) (ev : Nat → Geid) (W : Geid → Prop) (p : Nat) (s : Estep) :
    CtracePrefix G c ev W → c.cdTr[p]? = some s → W (ev p) → ¬ cpoisStep G c ev p s →
    cwitStep G c ev p s := by
  intro h hs hW hnp
  rcases h.ctpStep p s hs with ⟨hnW, _⟩ | ⟨_, hw⟩ | hp
  · exact (hnW hW).elim
  · exact hw
  · exact (hnp hp).elim

theorem ctpEvEq (G : Gexec) (c : Cand) (ev : Nat → Geid) (W : Geid → Prop) (p : Nat) (s : Estep) :
    CtracePrefix G c ev W → c.cdTr[p]? = some s →
    ev p = (s.esAg, gcnt s.esAg (c.cdTr.take p)) :=
  fun h hs => Prod.ext (h.ctpAg p s hs) (h.ctpPos p s hs)

/-- THE LOG DICTIONARY, log → graph (verbatim from `WeakRvwmoFloor.gtpLogWrites`). -/
theorem ctpLogWrites (G : Gexec) (c : Cand) (ev : Nat → Geid) (W : Geid → Prop) :
    CtracePrefix G c ev W →
    ∀ (s : Nat) m, 0 < s → (cdLog c c.cdTr.length)[s - 1]? = some m →
      ∀ b, (msgByte m b).isSome →
        ∃ w v', gwriteAt G s = some w ∧ gwritesByte G w b v' := by
  intro hgt s m hs hm b hv
  obtain ⟨v, hv⟩ := someOfIsSome hv
  have hle : s ≤ (cdLog c c.cdTr.length).length := by have := lookup_lt_Some hm; omega
  obtain ⟨w, hw, heq⟩ := hgt.ctpLog s hs hle
  rw [hm] at heq
  cases hl : gxLbl G w with
  | none => simp [gwmsg, hl] at heq
  | some l =>
    cases hwr : lbWr l with
    | none => simp [gwmsg, hl, hwr] at heq
    | some p =>
      obtain ⟨base, vs⟩ := p
      simp only [gwmsg, hl, hwr, Option.some.injEq] at heq
      subst heq
      simp only [msgByte] at hv
      split at hv
      · refine ⟨w, v, hw, l, base, vs, (b - base).toNat, hl, hwr, hv, ?_⟩
        simp only [accAddr]; omega
      · cases hv

/-- THE LOG DICTIONARY, graph → log (verbatim from `WeakRvwmoFloor.gtpLogByte`). -/
theorem ctpLogByte (G : Gexec) (c : Cand) (ev : Nat → Geid) (W : Geid → Prop) :
    CtracePrefix G c ev W →
    ∀ (s : Nat) w b v, 0 < s → s ≤ (cdLog c c.cdTr.length).length →
      gwriteAt G s = some w → gwritesByte G w b v →
      logByte c.cdImg (cdLog c c.cdTr.length) s b = some v := by
  rintro hgt s w b v hs hle hw ⟨l, base, vs, j, hl, hwr, hj, hb⟩
  obtain ⟨w', hw', heq⟩ := hgt.ctpLog s hs hle
  rw [hw, Option.some.injEq] at hw'
  subst hw'
  simp only [gwmsg, hl, hwr] at heq
  obtain ⟨n, rfl⟩ : ∃ n, s = n + 1 := ⟨s - 1, by omega⟩
  rw [logByteS]
  simp only [Nat.add_sub_cancel] at heq
  rw [heq]
  subst hb
  simp only [Option.bind, msgByte, accAddr]
  rw [if_pos (by omega), show (base + (j : Int) - base).toNat = j by omega]
  exact hj

/-! ## 1.3 `WPolocClosed` -/

def WPolocClosed (G : Gexec) (W : Geid → Prop) : Prop :=
  ∀ e1 e2 a, W e1 → WeakRvwmoGraph.gpo G e1 e2 → gaccesses G e1 a → gaccesses G e2 a →
    glblIs G e2 lbIsR → W e2

/-! ## 1.4 `witnessNotAq` -/

theorem witnessNotAq (G : Gexec) (e z : Geid) :
    gppoGmo G → WeakRvwmoGraph.gpo G e z → gmem G z →
    glblIs G e lbIsR → glblIs G e lbAq → ¬ gmoLt G z e := by
  intro hppo hpo hmem hr haq hlt
  have hlt2 := gacqGmo G hppo e z hpo hr haq hmem
  obtain ⟨_, _, h1⟩ := hlt
  obtain ⟨_, _, h2⟩ := hlt2
  omega

/-! # 2. `cinv`: the floor invariant, tolerating witnesses -/

abbrev cinv (G : Gexec) (r : Geid) (a : Int) (k : Nat) (ws : Wstate) : Prop := finv G r a k ws

/-! ## 2.1 The side condition (W-b) -/

def witFenceUb (G : Gexec) (c : Cand) (ev : Nat → Geid) (W : Geid → Prop) (r : Geid) : Prop :=
  ∀ p s, c.cdTr[p]? = some s → W (ev p) → (ev p).1 = r.1 →
    fhook G r ((ev p).2 + 1) true → gvisUb G r (cdLog c p).length

/-! ## 2.1' The same two side conditions, at a POISONED position -/

def poisOkAt (G : Gexec) (c : Cand) (ev : Nat → Geid) (r : Geid) : Prop :=
  ∀ p s, c.cdTr[p]? = some s → cpoisStep G c ev p s → (ev p).1 = r.1 →
    (∀ a, gaccesses G r a → ¬ lblTouches s.esLb a) ∧
    (fhook G r ((ev p).2 + 1) true → gvisUb G r (cdLog c p).length)

def poisOkHart (G : Gexec) (c : Cand) (ev : Nat → Geid) (x : Nat) : Prop :=
  ∀ p s, c.cdTr[p]? = some s → cpoisStep G c ev p s → (ev p).1 = x →
    ∀ k, gcnt x c.cdTr ≤ k →
      (∀ a, gaccesses G (x, k) a → ¬ lblTouches s.esLb a) ∧
      (fhook G (x, k) ((ev p).2 + 1) true → gvisUb G (x, k) (cdLog c p).length)

theorem poisOkAtOfHart (G : Gexec) (c : Cand) (ev : Nat → Geid) (x : Nat) :
    poisOkHart G c ev x → poisOkAt G c ev (x, gcnt x c.cdTr) :=
  fun h p s hs hpo hag => h p s hs hpo hag _ (Nat.le_refl _)

/-! ## 2.2 THE WITNESS STEP -/

theorem cinvStepWit (G : Gexec) (_hwf : gwf G) (_hppo : gppoGmo G) (_hlv : gloadValue G)
    (r : Geid) (a : Int) (_hrr : glblIs G r lbIsR) (_hra : gaccesses G r a)
    (k : Nat) (ws : Wstate) (base : Int) (ts : List Nat) (vs : List (BitVec 8)) (tw : Nat) :
    (∀ (j : Nat) t, ts[j]? = some t → accAddr base j ≠ a) →
    (fhook G r (k + 1) true → ∀ (j : Nat) t, ts[j]? = some t → gvisUb G r t) →
    cinv G r a k ws →
    cinv G r a (k + 1) (WeakRvwmoFloor.lstep tw ws (.LLoad false base ts vs)) := by
  rintro hdisj hub ⟨hfw, hcoh, hrn, hrel, hro, hwo⟩
  have hcl : maxcl (gvisUb G r) := gvisUbMaxcl G r
  have hvpre : gvisUb G r (loadVpre ws false) := by
    unfold loadVpre
    apply maxclMax _ _ _ hcl hrn
    exact gvisUb0 G r
  simp only [cinv, finv, WeakRvwmoFloor.lstep]
  refine ⟨fwd0LoadPostRun _ _ _ _ hfw, ?_, ?_, ?_, ?_, ?_⟩
  · exact loadRunCoh _ ws false base ts a hcl hfw hcoh hvpre
      (fun j t hj hja => absurd hja (hdisj j t hj))
  · rw [loadRunVrNewPlain]; exact hrn
  · rw [loadRunVRel]; intro hah; exact hrel (ahookS G r k hah)
  · intro hfh
    exact loadRunVrOld _ ws false base ts hcl hfw (hro (fhookS G r k true hfh)) hvpre (hub hfh)
  · rw [loadRunVwOld]; intro hfh; exact hwo (fhookS G r k false hfh)

/-! ## 2.3 THE REPLAY -/

theorem cinvReplay (G : Gexec) (hwf : gwf G) (hppo : gppoGmo G) (hlv : gloadValue G)
    (r : Geid) (a : Int) (hrr : glblIs G r lbIsR) (hra : gaccesses G r a)
    (c : Cand) (ev : Nat → Geid) (W : Geid → Prop) (p : Nat) :
    CtracePrefix G c ev W →
    WPolocClosed G W →
    witFenceUb G c ev W r →
    poisOkAt G c ev r →
    ¬ W r →
    gcnt r.1 c.cdTr ≤ r.2 →
    p ≤ c.cdTr.length →
    cinv G r a (gcnt r.1 (c.cdTr.take p)) ((stt (candExec c) p).msWs r.1) := by
  intro hgt hpc hwub hpd hnW hcnt
  induction p with
  | zero =>
    intro _
    rw [candSttInit, List.take_zero]
    exact finvInit G r a
  | succ p ih =>
    intro hp
    obtain ⟨s, hs⟩ := someOfIsSome (lookup_lt_is_Some_2 (show p < c.cdTr.length by omega))
    have hlog : (stt (candExec c) p).msLog = cdLog c p := candElog c p (by omega)
    rw [candNext c p s hs]
    by_cases hag : s.esAg = r.1
    case neg =>
      rw [gcntStepNe r.1 c.cdTr p s hs hag,
        mnextWsNe _ s.esAg s.esLb r.1 (fun h => hag h.symm)]
      exact ih (by omega)
    rw [gcntStepEq r.1 c.cdTr p s hs hag, hag, mnextWsEq]
    have hev : ev p = (r.1, gcnt r.1 (c.cdTr.take p)) := by
      rw [ctpEvEq G c ev W p s hgt hs, hag]
    have hklt : gcnt r.1 (c.cdTr.take p) < r.2 := by
      have hle := gcntTakeLe r.1 c.cdTr (p + 1)
      rw [gcntStepEq r.1 c.cdTr p s hs hag] at hle
      omega
    have hIH := ih (by omega)
    rcases hgt.ctpStep p s hs with ⟨_, hlblp⟩ | ⟨hW, hwitp⟩ | hpois
    · -- A TRUE STEP
      apply finvStep G hwf hppo hlv r a hrr hra _ s.esLb _ _ hklt
      · rw [← hev]; exact hlblp
      · intro hw; rw [← hev, hlog]; exact hgt.ctpWix p s hs hw
      · exact hIH
    · -- A WITNESS
      obtain ⟨base, n, ts0, vs0, hlg, hn, hlb⟩ := hwitp
      have hlen0 : vs0.length = ts0.length := WeakRvwmoFloor.gshape G hwf _ _ hlg
      rw [hlb, latestReadLbl]
      apply cinvStepWit G hwf hppo hlv r a hrr hra _ _ base _ _ _ ?_ ?_ hIH
      · -- (W-a): the witness's footprint misses `a`
        intro j t hj heq
        obtain ⟨hjn, _⟩ := lrdTsLookup (cdPre c p) base n j t hj
        obtain ⟨t0, ht0⟩ := someOfIsSome (lookup_lt_is_Some_2 (show j < ts0.length by omega))
        obtain ⟨v0, hv0⟩ := someOfIsSome (lookup_lt_is_Some_2 (show j < vs0.length by omega))
        have hacc : gaccesses G (ev p) a :=
          .inr ⟨t0, v0, .LLoad false base ts0 vs0, base, ts0, vs0, j, hlg, rfl, ht0, hv0, heq⟩
        have hpo : WeakRvwmoGraph.gpo G (ev p) r := by
          refine ⟨by rw [hev], by rw [hev]; exact hklt, by rw [hlg]; rfl,
            WeakRvwmoFloor.hrsome G r hrr⟩
        exact hnW (hpc (ev p) r a hW hpo hacc hra hrr)
      · -- (W-b): the fence-guarded log bound
        intro hfh j t hj
        obtain ⟨_, rfl⟩ := lrdTsLookup (cdPre c p) base n j t hj
        rw [cdPreLog]
        apply gvisUbDown G r _ (cdLog c p).length (latestTsLe _ _)
        exact hwub p s hs hW (by rw [hev]) (by rw [hev]; exact hfh)
    · -- A POISONED STEP
      obtain ⟨hdisj, hub⟩ := hpd p s hs hpois (by rw [hev])
      obtain ⟨_, ⟨base, n, hlb⟩, _, _⟩ := hpois
      rw [hlb, latestReadLbl]
      apply cinvStepWit G hwf hppo hlv r a hrr hra _ _ base _ _ _ ?_ ?_ hIH
      · intro j t hj heq
        apply hdisj a hra
        exact ⟨base, lrdTs (cdPre c p) base n, lrdVs (cdPre c p) base n, by rw [hlb]; rfl,
          j, t, hj, heq⟩
      · intro hfh j t hj
        obtain ⟨_, rfl⟩ := lrdTsLookup (cdPre c p) base n j t hj
        rw [cdPreLog]
        apply gvisUbDown G r _ (cdLog c p).length (latestTsLe _ _)
        exact hub (by rw [hev]; exact hfh)

/-! ## 2.4 THE FLOOR, over a certified prefix -/

theorem floorOfCgraph (G : Gexec) (c : Cand) (ev : Nat → Geid) (W : Geid → Prop) (i : Nat)
    (r : Geid) (a : Int) (t : Nat) (v : BitVec 8) (aq : Bool) :
    rvwmoMinusConsistent G →
    CtracePrefix G c ev W →
    WPolocClosed G W →
    witFenceUb G c ev W r →
    poisOkAt G c ev r →
    ¬ W r →
    r = (i, gcnt i c.cdTr) →
    greadsByte G r a t v →
    (aq = true → glblIs G r lbAq) →
    ¬ writesIn (cdLog c c.cdTr.length) a t
      (max (loadVpre ((stt (candExec c) c.cdTr.length).msWs i) aq)
           (coh ((stt (candExec c) c.cdTr.length).msWs i) a)) := by
  rintro ⟨hwf, hppo, hlv, _⟩ hgt hpc hwub hpd hnW hr hrb haq
  have hrr : glblIs G r lbIsR := by
    obtain ⟨l, base, ts, vs, j, hl, hrd, _⟩ := hrb
    exact ⟨l, hl, lbRdIsR l _ hrd⟩
  have hra : gaccesses G r a := .inr ⟨t, v, hrb⟩
  subst hr
  have hcl : maxcl (gvisUb G (i, gcnt i c.cdTr)) := gvisUbMaxcl G _
  have hinv := cinvReplay G hwf hppo hlv _ a hrr hra c ev W c.cdTr.length hgt hpc hwub hpd hnW
    (Nat.le_refl _) (Nat.le_refl _)
  rw [take_ge (l := c.cdTr) (Nat.le_refl _)] at hinv
  obtain ⟨_, hcoh, hrn, hrel, _, _⟩ := hinv
  apply noWritesInOfUb G hwf hlv _ a t v _ _ hrb (ctpLogWrites G c ev W hgt)
  apply maxclMax _ _ _ hcl _ hcoh
  unfold loadVpre
  apply maxclMax _ _ _ hcl hrn
  cases aq with
  | false => exact gvisUb0 G _
  | true => exact hrel ⟨_, Nat.le_refl _, hrr, haq rfl, .inl rfl⟩

/-! # 3. `floorOk`, DISCHARGED — in `certSegment`'s vocabulary -/

/-! ## 3.1 The obligation itself -/

theorem certFloorOk (G : Gexec) (c : Cand) (ev : Nat → Geid) (W : Geid → Prop) (i : Nat)
    (aq : Bool) (base : Int) (ts : List Nat) (vs : List (BitVec 8)) :
    rvwmoMinusConsistent G →
    CtracePrefix G c ev W →
    WPolocClosed G W →
    witFenceUb G c ev W (i, gcnt i c.cdTr) →
    poisOkAt G c ev (i, gcnt i c.cdTr) →
    ¬ W (i, gcnt i c.cdTr) →
    gxLbl G (i, gcnt i c.cdTr) = some (.LLoad aq base ts vs) →
    floorOk c i aq base ts := by
  intro hcons hgt hpc hwub hpd hnW hl j t hj
  have hlen : vs.length = ts.length := WeakRvwmoFloor.gshape G hcons.1 _ _ hl
  obtain ⟨v, hv⟩ := someOfIsSome (lookup_lt_is_Some_2
    (show j < vs.length by rw [hlen]; exact lookup_lt_Some hj))
  exact floorOfCgraph G c ev W i _ (accAddr base j) t v aq hcons hgt hpc hwub hpd hnW rfl
    ⟨.LLoad aq base ts vs, base, ts, vs, j, hl, rfl, hj, hv, rfl⟩
    (fun h => by subst h; exact ⟨.LLoad true base ts vs, hl, rfl⟩)

/-! ## 3.2 `certReadInLog`, with `floorOk` GONE -/

theorem certReadInLog' (G : Gexec) (c : Cand) (ev : Nat → Geid) (W : Geid → Prop) (i : Nat)
    (aq : Bool) (base : Int) (ts : List Nat) (vs : List (BitVec 8)) :
    rvwmoMinusConsistent G →
    CtracePrefix G c ev W →
    WPolocClosed G W →
    witFenceUb G c ev W (i, gcnt i c.cdTr) →
    poisOkAt G c ev (i, gcnt i c.cdTr) →
    ¬ W (i, gcnt i c.cdTr) →
    gxLbl G (i, gcnt i c.cdTr) = some (.LLoad aq base ts vs) →
    srcInLog c base ts vs →
    mstepOk (candLastSt c) i (.LLoad aq base ts vs) :=
  fun hcons hgt hpc hwub hpd hnW hl hsrc =>
    certReadInLog c i aq base ts vs hsrc
      (certFloorOk G c ev W i aq base ts vs hcons hgt hpc hwub hpd hnW hl)

/-! ## 3.3 THE CERTIFICATION CONTEXT -/

def cpolCtx (G : Gexec) (W : Geid → Prop) (x : Nat) (c : Cand) : Prop :=
  ∃ ev, CtracePrefix G c ev W ∧ witFenceUb G c ev W (x, gcnt x c.cdTr) ∧ poisOkHart G c ev x

theorem cpolRead (G : Gexec) (W : Geid → Prop) (x : Nat) (c : Cand) (aq : Bool) (base : Int)
    (ts : List Nat) (vs : List (BitVec 8)) :
    rvwmoMinusConsistent G → WPolocClosed G W → cpolCtx G W x c →
    ¬ W (x, gcnt x c.cdTr) →
    gxLbl G (x, gcnt x c.cdTr) = some (.LLoad aq base ts vs) →
    srcInLog c base ts vs →
    mstepOk (candLastSt c) x (.LLoad aq base ts vs) := by
  rintro hcons hpc ⟨ev, hgt, hwub, hpd⟩ hnW hl hsrc
  exact certReadInLog' G c ev W x aq base ts vs hcons hgt hpc hwub (poisOkAtOfHart G c ev x hpd)
    hnW hl hsrc

/-! ## 3.3a `cblkp` — the `HEpair` block with its annotations exposed -/

/-- (Lean-only, deviation 4) Rocq's `cblkp` with the predicate on the FIRST admin stretch
abstracted to `A` (the second stretch is `lbAdmin false`, which never fetches). -/
def WeakRvwmoCert3.cblkpG (A : Wlabel → Prop) (cpu : CPU) (d0 : Efab) (ws : Wstate) (lb : Lbl) (l1 l2 : Wlabel) (rds : List Nat)
    (wrs : List Register) (m : SailM Unit) (rs : RegFile) (fn : Ofence) (ib : Ibch)
    (m' : SailM Unit) (rs' : RegFile) (fn' : Ofence) (ib' : Ibch) : Prop :=
  ∃ (ls1 : List Wlabel) (ma : SailM Unit) (rsa : RegFile) (fna : Ofence) (iba : Ibch) (da : Efab)
    (rdsA : List Nat) (wrsA : List Register) (annA : Bool)
    (mm : SailM Unit) (rsm : RegFile) (fnm : Ofence) (ibm : Ibch) (dm : Efab)
    (rdsB : List Nat) (wrsB : List Register) (annB : Bool)
    (ls2 : List Wlabel) (mm2 : SailM Unit) (rsm2 : RegFile) (fnm2 : Ofence) (ibm2 : Ibch)
    (dm2 : Efab) (rdsC : List Nat) (wrsC : List Register) (annC : Bool)
    (rdsD : List Nat) (wrsD : List Register) (annD : Bool),
    (∀ l0, l0 ∈ ls1 → A l0) ∧
    phrun cpu ls1 rdsA wrsA annA m rs fn ib d0 ma rsa fna iba da ∧
    hlblRealizesPair (.PHart cpu ma rsa fna iba) (.PHart cpu mm2 rsm2 fnm2 ibm2) ws lb l1 l2 ∧
    phrun cpu [l1] rdsB wrsB annB ma rsa fna iba da mm rsm fnm ibm dm ∧
    (∀ l0, l0 ∈ ls2 → lbAdmin false l0) ∧
    phrun cpu ls2 rdsC wrsC annC mm rsm fnm ibm dm mm2 rsm2 fnm2 ibm2 dm2 ∧
    phrun cpu [l2] rdsD wrsD annD mm2 rsm2 fnm2 ibm2 dm2 m' rs' fn' ib' d0 ∧
    rds = rdsA ++ (rdsB ++ (rdsC ++ rdsD)) ∧
    wrs = wrsA ++ (wrsB ++ (wrsC ++ wrsD))

/-- The four stretches' read/write lists are concatenated RIGHT-associated, as Rocq's `++`
(deviation 4: `cblkpG (lbAdmin true)`, definitionally Rocq's body). -/
def cblkp (cpu : CPU) (d0 : Efab) (ws : Wstate) (lb : Lbl) (l1 l2 : Wlabel) (rds : List Nat)
    (wrs : List Register) (m : SailM Unit) (rs : RegFile) (fn : Ofence) (ib : Ibch)
    (m' : SailM Unit) (rs' : RegFile) (fn' : Ofence) (ib' : Ibch) : Prop :=
  WeakRvwmoCert3.cblkpG (lbAdmin true) cpu d0 ws lb l1 l2 rds wrs m rs fn ib m' rs' fn' ib'


/-- (Lean-only, deviation 4) THE PINNED PAIR BLOCK. -/
def WeakRvwmoCert3.cblkpPin (im : Image) (cpu : CPU) (d0 : Efab) (ws : Wstate) (lb : Lbl)
    (l1 l2 : Wlabel) (rds : List Nat) (wrs : List Register) (m : SailM Unit) (rs : RegFile)
    (fn : Ofence) (ib : Ibch) (m' : SailM Unit) (rs' : RegFile) (fn' : Ofence) (ib' : Ibch) :
    Prop :=
  WeakRvwmoCert3.cblkpG (WeakRvwmoCert2.lbPin im) cpu d0 ws lb l1 l2 rds wrs m rs fn ib m' rs'
    fn' ib'

/-- (Lean-only, deviation 4) An `lbAdmin false` label is never a fetch. -/
theorem WeakRvwmoCert3.lbAdminFalsePin (im : Image) (l : Wlabel) :
    lbAdmin false l → WeakAxRealize.fetchPin im l := by
  cases l with
  | LIFetch base tvs => intro h; exact absurd h Bool.false_ne_true
  | _ => intro _; trivial

theorem cblkpIntro (cpu : CPU) (d0 : Efab) (ws : Wstate) (lb : Lbl) (l1 l2 : Wlabel)
    (ls1 : List Wlabel) (pa : Pexv6) (da : Efab) (pm : Pexv6) (dm : Efab) (ls2 : List Wlabel)
    (pm2 : Pexv6) (dm2 : Efab) (m : SailM Unit) (rs : RegFile) (fn : Ofence) (ib : Ibch)
    (m' : SailM Unit) (rs' : RegFile) (fn' : Ofence) (ib' : Ibch) :
    admRun true (.PHart cpu m rs fn ib) d0 ls1 pa da →
    hlblRealizesPair pa pm2 ws lb l1 l2 →
    pstepEv pa da l1 pm dm →
    admRun false pm dm ls2 pm2 dm2 →
    pstepEv pm2 dm2 l2 (.PHart cpu m' rs' fn' ib') d0 →
    ∃ rds wrs, cblkp cpu d0 ws lb l1 l2 rds wrs m rs fn ib m' rs' fn' ib' := by
  intro har1 hre hst1 har2 hst2
  obtain ⟨ma, rsa, fna, iba, rfl⟩ := admRunPhart true _ _ d0 ls1 da har1 cpu m rs fn ib rfl
  obtain ⟨mm, rsm, fnm, ibm, rfl⟩ := pstepEvPhart cpu ma rsa fna iba da l1 pm dm hst1
  obtain ⟨mm2, rsm2, fnm2, ibm2, rfl⟩ :=
    admRunPhart false _ _ dm ls2 dm2 har2 cpu mm rsm fnm ibm rfl
  obtain ⟨rdsA, wrsA, annA, hA⟩ := pevrunPhrun ls1 _ d0 _ da
    (admRunPevrun _ _ _ _ _ _ har1) cpu m rs fn ib ma rsa fna iba rfl rfl
  obtain ⟨rdsB, wrsB, annB, hB⟩ := pevrunPhrun [l1] _ da _ dm
    (pevrun.more hst1 (pevrun.nil _ _)) cpu ma rsa fna iba mm rsm fnm ibm rfl rfl
  obtain ⟨rdsC, wrsC, annC, hC⟩ := pevrunPhrun ls2 _ dm _ dm2
    (admRunPevrun _ _ _ _ _ _ har2) cpu mm rsm fnm ibm mm2 rsm2 fnm2 ibm2 rfl rfl
  obtain ⟨rdsD, wrsD, annD, hD⟩ := pevrunPhrun [l2] _ dm2 _ d0
    (pevrun.more hst2 (pevrun.nil _ _)) cpu mm2 rsm2 fnm2 ibm2 m' rs' fn' ib' rfl rfl
  exact ⟨_, _, ls1, ma, rsa, fna, iba, da, rdsA, wrsA, annA, mm, rsm, fnm, ibm, dm, rdsB, wrsB,
    annB, ls2, mm2, rsm2, fnm2, ibm2, dm2, rdsC, wrsC, annC, rdsD, wrsD, annD,
    admRunAdmin _ _ _ _ _ _ har1, hA, hre, hB, admRunAdmin _ _ _ _ _ _ har2, hC, hD, rfl, rfl⟩

theorem cblkpElim (cpu : CPU) (d0 : Efab) (ws : Wstate) (lb : Lbl) (l1 l2 : Wlabel)
    (rds : List Nat) (wrs : List Register) (m : SailM Unit) (rs : RegFile) (fn : Ofence)
    (ib : Ibch) (m' : SailM Unit) (rs' : RegFile) (fn' : Ofence) (ib' : Ibch) :
    cblkp cpu d0 ws lb l1 l2 rds wrs m rs fn ib m' rs' fn' ib' →
    ∃ ls1 pa da pm dm ls2 pm2 dm2,
      admRun true (.PHart cpu m rs fn ib) d0 ls1 pa da ∧
      hlblRealizesPair pa pm2 ws lb l1 l2 ∧
      pstepEv pa da l1 pm dm ∧
      admRun false pm dm ls2 pm2 dm2 ∧
      pstepEv pm2 dm2 l2 (.PHart cpu m' rs' fn' ib') d0 := by
  rintro ⟨ls1, ma, rsa, fna, iba, da, rdsA, wrsA, annA, mm, rsm, fnm, ibm, dm, rdsB, wrsB, annB,
    ls2, mm2, rsm2, fnm2, ibm2, dm2, rdsC, wrsC, annC, rdsD, wrsD, annD, had1, hA, hre, hB, had2,
    hC, hD, -, -⟩
  exact ⟨ls1, .PHart cpu ma rsa fna iba, da, .PHart cpu mm rsm fnm ibm, dm, ls2,
    .PHart cpu mm2 rsm2 fnm2 ibm2, dm2,
    pevrunAdmRun true _ d0 ls1 _ da (phrunPevrun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hA) had1, hre,
    pevrunSingleInv _ _ _ _ _ (phrunPevrun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hB),
    pevrunAdmRun false _ dm ls2 _ dm2 (phrunPevrun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hC) had2,
    pevrunSingleInv _ _ _ _ _ (phrunPevrun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hD)⟩

/-- (Lean-only, deviation 4) Forget the pins. -/
theorem WeakRvwmoCert3.cblkpPinCblkp (im : Image) (cpu : CPU) (d0 : Efab) (ws : Wstate)
    (lb : Lbl) (l1 l2 : Wlabel) (rds : List Nat) (wrs : List Register) (m : SailM Unit)
    (rs : RegFile) (fn : Ofence) (ib : Ibch) (m' : SailM Unit) (rs' : RegFile) (fn' : Ofence)
    (ib' : Ibch) :
    WeakRvwmoCert3.cblkpPin im cpu d0 ws lb l1 l2 rds wrs m rs fn ib m' rs' fn' ib' →
    cblkp cpu d0 ws lb l1 l2 rds wrs m rs fn ib m' rs' fn' ib' := by
  rintro ⟨ls1, ma, rsa, fna, iba, da, rdsA, wrsA, annA, mm, rsm, fnm, ibm, dm, rdsB, wrsB, annB,
    ls2, mm2, rsm2, fnm2, ibm2, dm2, rdsC, wrsC, annC, rdsD, wrsD, annD, had1, hA, hre, hB, had2,
    hC, hD, h1, h2⟩
  exact ⟨ls1, ma, rsa, fna, iba, da, rdsA, wrsA, annA, mm, rsm, fnm, ibm, dm, rdsB, wrsB, annB,
    ls2, mm2, rsm2, fnm2, ibm2, dm2, rdsC, wrsC, annC, rdsD, wrsD, annD,
    fun l0 h => (had1 l0 h).1, hA, hre, hB, had2, hC, hD, h1, h2⟩

/-- (Lean-only, deviation 4) `cblkpIntro` of a pair whose first admin stretch is pinned. -/
theorem WeakRvwmoCert3.cblkpIntroPin (im : Image) (cpu : CPU) (d0 : Efab) (ws : Wstate)
    (lb : Lbl) (l1 l2 : Wlabel) (ls1 : List Wlabel) (pa : Pexv6) (da : Efab) (pm : Pexv6)
    (dm : Efab) (ls2 : List Wlabel) (pm2 : Pexv6) (dm2 : Efab) (m : SailM Unit) (rs : RegFile)
    (fn : Ofence) (ib : Ibch) (m' : SailM Unit) (rs' : RegFile) (fn' : Ofence) (ib' : Ibch) :
    admRun true (.PHart cpu m rs fn ib) d0 ls1 pa da →
    (∀ l0, l0 ∈ ls1 → WeakAxRealize.fetchPin im l0) →
    hlblRealizesPair pa pm2 ws lb l1 l2 →
    pstepEv pa da l1 pm dm →
    admRun false pm dm ls2 pm2 dm2 →
    pstepEv pm2 dm2 l2 (.PHart cpu m' rs' fn' ib') d0 →
    ∃ rds wrs, WeakRvwmoCert3.cblkpPin im cpu d0 ws lb l1 l2 rds wrs m rs fn ib m' rs' fn' ib' := by
  intro har1 hpin hre hst1 har2 hst2
  obtain ⟨ma, rsa, fna, iba, rfl⟩ := admRunPhart true _ _ d0 ls1 da har1 cpu m rs fn ib rfl
  obtain ⟨mm, rsm, fnm, ibm, rfl⟩ := pstepEvPhart cpu ma rsa fna iba da l1 pm dm hst1
  obtain ⟨mm2, rsm2, fnm2, ibm2, rfl⟩ :=
    admRunPhart false _ _ dm ls2 dm2 har2 cpu mm rsm fnm ibm rfl
  obtain ⟨rdsA, wrsA, annA, hA⟩ := pevrunPhrun ls1 _ d0 _ da
    (admRunPevrun _ _ _ _ _ _ har1) cpu m rs fn ib ma rsa fna iba rfl rfl
  obtain ⟨rdsB, wrsB, annB, hB⟩ := pevrunPhrun [l1] _ da _ dm
    (pevrun.more hst1 (pevrun.nil _ _)) cpu ma rsa fna iba mm rsm fnm ibm rfl rfl
  obtain ⟨rdsC, wrsC, annC, hC⟩ := pevrunPhrun ls2 _ dm _ dm2
    (admRunPevrun _ _ _ _ _ _ har2) cpu mm rsm fnm ibm mm2 rsm2 fnm2 ibm2 rfl rfl
  obtain ⟨rdsD, wrsD, annD, hD⟩ := pevrunPhrun [l2] _ dm2 _ d0
    (pevrun.more hst2 (pevrun.nil _ _)) cpu mm2 rsm2 fnm2 ibm2 m' rs' fn' ib' rfl rfl
  exact ⟨_, _, ls1, ma, rsa, fna, iba, da, rdsA, wrsA, annA, mm, rsm, fnm, ibm, dm, rdsB, wrsB,
    annB, ls2, mm2, rsm2, fnm2, ibm2, dm2, rdsC, wrsC, annC, rdsD, wrsD, annD,
    fun l0 h => ⟨admRunAdmin _ _ _ _ _ _ har1 l0 h, hpin l0 h⟩, hA, hre, hB,
    admRunAdmin _ _ _ _ _ _ har2, hC, hD, rfl, rfl⟩

/-- (Lean-only, deviation 4) `cblkpElim`, keeping the pins of both admin stretches. -/
theorem WeakRvwmoCert3.cblkpElimPin (im : Image) (cpu : CPU) (d0 : Efab) (ws : Wstate)
    (lb : Lbl) (l1 l2 : Wlabel) (rds : List Nat) (wrs : List Register) (m : SailM Unit)
    (rs : RegFile) (fn : Ofence) (ib : Ibch) (m' : SailM Unit) (rs' : RegFile) (fn' : Ofence)
    (ib' : Ibch) :
    WeakRvwmoCert3.cblkpPin im cpu d0 ws lb l1 l2 rds wrs m rs fn ib m' rs' fn' ib' →
    ∃ ls1 pa da pm dm ls2 pm2 dm2,
      admRun true (.PHart cpu m rs fn ib) d0 ls1 pa da ∧
      (∀ l0, l0 ∈ ls1 → WeakAxRealize.fetchPin im l0) ∧
      hlblRealizesPair pa pm2 ws lb l1 l2 ∧
      pstepEv pa da l1 pm dm ∧
      admRun false pm dm ls2 pm2 dm2 ∧
      (∀ l0, l0 ∈ ls2 → WeakAxRealize.fetchPin im l0) ∧
      pstepEv pm2 dm2 l2 (.PHart cpu m' rs' fn' ib') d0 := by
  rintro ⟨ls1, ma, rsa, fna, iba, da, rdsA, wrsA, annA, mm, rsm, fnm, ibm, dm, rdsB, wrsB, annB,
    ls2, mm2, rsm2, fnm2, ibm2, dm2, rdsC, wrsC, annC, rdsD, wrsD, annD, had1, hA, hre, hB, had2,
    hC, hD, -, -⟩
  exact ⟨ls1, .PHart cpu ma rsa fna iba, da, .PHart cpu mm rsm fnm ibm, dm, ls2,
    .PHart cpu mm2 rsm2 fnm2 ibm2, dm2,
    pevrunAdmRun true _ d0 ls1 _ da (phrunPevrun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hA)
      (fun l0 h => (had1 l0 h).1), fun l0 h => (had1 l0 h).2, hre,
    pevrunSingleInv _ _ _ _ _ (phrunPevrun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hB),
    pevrunAdmRun false _ dm ls2 _ dm2 (phrunPevrun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hC) had2,
    fun l0 h => WeakRvwmoCert3.lbAdminFalsePin im l0 (had2 l0 h),
    pevrunSingleInv _ _ _ _ _ (phrunPevrun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hD)⟩



/-- (Lean-only, deviation 4) `cblkpRelp` at any admin predicate `A`. -/
theorem WeakRvwmoCert3.cblkpRelpG (A : Wlabel → Prop)
    (cpu : CPU) (d0 : Efab) (ws ws' : Wstate) (lb : Lbl) (l1 l2 : Wlabel)
    (rds : List Nat) (wrs : List Register) (m : SailM Unit) (rs : RegFile) (fn : Ofence)
    (ib : Ibch) (m' : SailM Unit) (rs' : RegFile) (fn' : Ofence) (ib' : Ibch) :
    ws'.wRelp = ws.wRelp →
    WeakRvwmoCert3.cblkpG A cpu d0 ws lb l1 l2 rds wrs m rs fn ib m' rs' fn' ib' →
    WeakRvwmoCert3.cblkpG A cpu d0 ws' lb l1 l2 rds wrs m rs fn ib m' rs' fn' ib' := by
  rintro hr ⟨ls1, ma, rsa, fna, iba, da, rdsA, wrsA, annA, mm, rsm, fnm, ibm, dm, rdsB, wrsB,
    annB, ls2, mm2, rsm2, fnm2, ibm2, dm2, rdsC, wrsC, annC, rdsD, wrsD, annD, had1, hA, hre, hB,
    had2, hC, hD, rfl, rfl⟩
  exact ⟨ls1, ma, rsa, fna, iba, da, rdsA, wrsA, annA, mm, rsm, fnm, ibm, dm, rdsB, wrsB, annB,
    ls2, mm2, rsm2, fnm2, ibm2, dm2, rdsC, wrsC, annC, rdsD, wrsD, annD, had1, hA,
    hlblRealizesPairRelp _ _ _ _ _ _ _ hr hre, hB, had2, hC, hD, rfl, rfl⟩

theorem cblkpRelp (cpu : CPU) (d0 : Efab) (ws ws' : Wstate) (lb : Lbl) (l1 l2 : Wlabel)
    (rds : List Nat) (wrs : List Register) (m : SailM Unit) (rs : RegFile) (fn : Ofence)
    (ib : Ibch) (m' : SailM Unit) (rs' : RegFile) (fn' : Ofence) (ib' : Ibch) :
    ws'.wRelp = ws.wRelp →
    cblkp cpu d0 ws lb l1 l2 rds wrs m rs fn ib m' rs' fn' ib' →
    cblkp cpu d0 ws' lb l1 l2 rds wrs m rs fn ib m' rs' fn' ib' :=
  WeakRvwmoCert3.cblkpRelpG (lbAdmin true) cpu d0 ws ws' lb l1 l2 rds wrs m rs fn ib m' rs' fn'
    ib'

/-! ## 3.3b The pair block, APPENDED (deviation 4: the pinned LTS, the pinned pair block) -/

theorem certBlockSnocPair (c : Cand) (x : Nat) (pst : Nat → List Pexv6) (dv : Nat → Efab)
    (cpu : CPU) (d0 : Efab) (lb : Lbl) (l1 l2 : Wlabel) (rds : List Nat) (wrs : List Register)
    (m : SailM Unit) (rs : RegFile) (fn : Ofence) (ib : Ibch) (m' : SailM Unit) (rs' : RegFile)
    (fn' : Ofence) (ib' : Ibch) :
    srvwmoConsistent c →
    execProgOk' (pstepPin c.cdImg pstepEv) pclsEv pst dv (candExec c) →
    (pst (cdEnd c))[x]? = some (.PHart cpu m rs fn ib) →
    dv (cdEnd c) = d0 →
    WeakRvwmoCert3.cblkpPin c.cdImg cpu d0 ((candLastSt c).msWs x) lb l1 l2 rds wrs m rs fn ib m'
      rs' fn' ib' →
    mstepOk (candLastSt c) x lb →
    srvwmoConsistent (candSnoc c ⟨x, lb⟩) ∧
    execProgOk' (pstepPin c.cdImg pstepEv) pclsEv (pstSnoc c pst x (.PHart cpu m' rs' fn' ib'))
      (dvSnoc c dv d0) (candExec (candSnoc c ⟨x, lb⟩)) := by
  intro hc hpo hp hdv hblk hok
  refine ⟨snocConsistent c ⟨x, lb⟩ hc hok, ?_⟩
  obtain ⟨ls1, pa, da, pm, dm, ls2, pm2, dm2, har1, hp1, hre, hs1, har2, hp2, hs2⟩ :=
    WeakRvwmoCert3.cblkpElimPin c.cdImg cpu d0 _ lb l1 l2 rds wrs m rs fn ib m' rs' fn' ib' hblk
  exact execProgOk'SnocPair c x _ pa da ls1 l1 l2 lb pm dm ls2 pm2 dm2 _ d0 pst dv hpo hp
    (by rw [hdv]; exact har1) hp1 hre hs1 har2 hp2 hs2

/-! ## 3.3c THE PAIR POLICY -/

/-- (Deviation 4: on pinned pair blocks.) -/
def cpolp (x : Nat) (cpu : CPU) (d0 : Efab) (T : List Nat) (Ctx : Nat → Cand → Prop)
    (Cls : Cand → Lbl → Prop) (Q : Nat → Lbl → Prop) : Prop :=
  ∀ (k : Nat) (c0 : Cand) (ws : Wstate) (lb : Lbl) (l1 l2 : Wlabel) (rds : List Nat)
    (wrs : List Register) (m : SailM Unit) (rs1 rs2 : RegFile) (fn : Ofence) (ib : Ibch)
    (m' : SailM Unit) (rs1' : RegFile) (fn' : Ofence) (ib' : Ibch),
    srvwmoConsistent c0 →
    Ctx k c0 →
    Q k lb →
    ((candLastSt c0).msWs x).wRelp = ws.wRelp →
    dregAgree (fun n => n ∉ T) rs1 rs2 →
    WeakRvwmoCert3.cblkpPin c0.cdImg cpu d0 ws lb l1 l2 rds wrs m rs1 fn ib m' rs1' fn' ib' →
    ∃ rs2',
      WeakRvwmoCert3.cblkpPin c0.cdImg cpu d0 ws lb l1 l2 rds wrs m rs2 fn ib m' rs2' fn' ib' ∧
      mstepOk (candLastSt c0) x lb ∧
      Cls c0 lb ∧
      dregAgree (fun n => n ∉ T) rs1' rs2'

/-- A `cblkp` block's label IS an RMW. -/
theorem cblkpRmw (cpu : CPU) (d0 : Efab) (ws : Wstate) (lb : Lbl) (l1 l2 : Wlabel)
    (rds : List Nat) (wrs : List Register) (m : SailM Unit) (rs : RegFile) (fn : Ofence)
    (ib : Ibch) (m' : SailM Unit) (rs' : RegFile) (fn' : Ofence) (ib' : Ibch) :
    cblkp cpu d0 ws lb l1 l2 rds wrs m rs fn ib m' rs' fn' ib' → ¬ lbRmwfree lb := by
  rintro ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    _, _, hre, _⟩
  obtain ⟨aq, rl, base, tvs, data, asrc1, asrc2, vsrc2, -, -, -, -, rfl⟩ := hre
  exact id

theorem cblkpIsW (cpu : CPU) (d0 : Efab) (ws : Wstate) (lb : Lbl) (l1 l2 : Wlabel)
    (rds : List Nat) (wrs : List Register) (m : SailM Unit) (rs : RegFile) (fn : Ofence)
    (ib : Ibch) (m' : SailM Unit) (rs' : RegFile) (fn' : Ofence) (ib' : Ibch) :
    cblkp cpu d0 ws lb l1 l2 rds wrs m rs fn ib m' rs' fn' ib' → lbIsW lb = true := by
  intro hblk
  have hr := cblkpRmw cpu d0 ws lb l1 l2 rds wrs m rs fn ib m' rs' fn' ib' hblk
  cases lb with
  | LLoad => exact (hr trivial).elim
  | LStore => rfl
  | LFence => exact (hr trivial).elim
  | LRmw => rfl

theorem cpolpOfRmwfree (x : Nat) (cpu : CPU) (d0 : Efab) (T : List Nat)
    (Ctx : Nat → Cand → Prop) (Cls : Cand → Lbl → Prop) (Q : Nat → Lbl → Prop) :
    (∀ k lb, Q k lb → lbRmwfree lb) → cpolp x cpu d0 T Ctx Cls Q := by
  intro hQ k c0 ws lb l1 l2 rds wrs m rs1 rs2 fn ib m' rs1' fn' ib' _ _ hq _ _ hblk
  exact (cblkpRmw _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (WeakRvwmoCert3.cblkpPinCblkp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hblk) (hQ k lb hq)).elim

/-- `WeakRvwmoCert2.polStore`, carrying the (trivial) classification, in `certSegment'`'s
policy shape (deviation 4: on pinned blocks). -/
theorem polStore' (x : Nat) (cpu : CPU) (d0 : Efab) :
    ∀ (c0 : Cand) (ws : Wstate) (lb : Lbl) (l : Wlabel) (rds : List Nat)
      (wrs : List Register) (m : SailM Unit) (rs1 rs2 : RegFile) (fn : Ofence) (ib : Ibch)
      (m' : SailM Unit) (rs1' : RegFile) (fn' : Ofence) (ib' : Ibch),
      srvwmoConsistent c0 →
      lbStoreNe lb →
      ((candLastSt c0).msWs x).wRelp = ws.wRelp →
      dregAgree (fun n => n ∉ ([] : List Nat)) rs1 rs2 →
      WeakRvwmoCert2.cblkPin c0.cdImg cpu d0 ws lb l rds wrs m rs1 fn ib m' rs1' fn' ib' →
      ∃ lb' l' rds' wrs' rs2',
        WeakRvwmoCert2.cblkPin c0.cdImg cpu d0 ws lb' l' rds' wrs' m rs2 fn ib m' rs2' fn' ib' ∧
        mstepOk (candLastSt c0) x lb' ∧
        lblReidxW lb lb' ∧
        True ∧
        dregAgree (fun n => n ∉ ([] : List Nat)) rs1' rs2' := by
  intro c0 ws lb l rds wrs m rs1 rs2 fn ib m' rs1' fn' ib' hc hlb hrelp hag hblk
  obtain ⟨lb', l', rds', wrs', rs2', h1, h2, h4, h5⟩ :=
    polStore x cpu d0 c0 ws lb l rds wrs m rs1 rs2 fn ib m' rs1' fn' ib' hc hlb hrelp hag hblk
  exact ⟨lb', l', rds', wrs', rs2', h1, h2, lblReidxWOf _ _ h4, trivial, h5⟩

/-! ## 3.4 `certSegment'` — the iteration with the read policy discharged

Rocq's `Section segment'` context is the leading parameters (deviation 2). -/

theorem certSegment' (x : Nat) (cpu : CPU) (d0 : Efab) (T : List Nat) (Q : Nat → Lbl → Prop)
    (Ctx : Nat → Cand → Prop) (Cls : Cand → Lbl → Prop)
    (Hpres : ∀ (k : Nat) (c0 : Cand) (lb lb' : Lbl),
      Ctx k c0 → srvwmoConsistent c0 → Q k lb → lblReidxW lb lb' →
      mstepOk (candLastSt c0) x lb' →
      Cls c0 lb' →
      Ctx (k + 1) (candSnoc c0 ⟨x, lb'⟩))
    (Hpol' : ∀ (k : Nat) (c0 : Cand) (ws : Wstate) (lb : Lbl) (l : Wlabel) (rds : List Nat)
      (wrs : List Register) (m : SailM Unit) (rs1 rs2 : RegFile) (fn : Ofence) (ib : Ibch)
      (m' : SailM Unit) (rs1' : RegFile) (fn' : Ofence) (ib' : Ibch),
      srvwmoConsistent c0 →
      Ctx k c0 →
      Q k lb →
      ((candLastSt c0).msWs x).wRelp = ws.wRelp →
      dregAgree (fun n => n ∉ T) rs1 rs2 →
      WeakRvwmoCert2.cblkPin c0.cdImg cpu d0 ws lb l rds wrs m rs1 fn ib m' rs1' fn' ib' →
      ∃ lb' l' rds' wrs' rs2',
        WeakRvwmoCert2.cblkPin c0.cdImg cpu d0 ws lb' l' rds' wrs' m rs2 fn ib m' rs2' fn' ib' ∧
        mstepOk (candLastSt c0) x lb' ∧
        lblReidxW lb lb' ∧
        Cls c0 lb' ∧
        dregAgree (fun n => n ∉ T) rs1' rs2')
    (Hpolp : cpolp x cpu d0 T Ctx Cls Q)
    (k0 : Nat) (ws0 : Wstate) (rowseg : List Lbl) (p : Pexv6) (es : List Eitem)
    (pfin : Pexv6) :
    hemit (fun _ => d0) k0 ws0 rowseg p es pfin →
    (∀ i lb, rowseg[i]? = some lb → Q (k0 + i) lb) →
    ∀ m0 rs10 fn0 ib0, p = .PHart cpu m0 rs10 fn0 ib0 →
    ∀ (c : Cand) (pst : Nat → List Pexv6) (dv : Nat → Efab) (rs20 : RegFile),
      srvwmoConsistent c →
      Ctx k0 c →
      WeakRvwmoCert2.esPin c.cdImg es →
      execProgOk' (pstepPin c.cdImg pstepEv) pclsEv pst dv (candExec c) →
      (pst (cdEnd c))[x]? = some (.PHart cpu m0 rs20 fn0 ib0) →
      dv (cdEnd c) = d0 →
      dregAgree (fun n => n ∉ T) rs10 rs20 →
      ((candLastSt c).msWs x).wRelp = ws0.wRelp →
      ∃ (c' : Cand) (pst' : Nat → List Pexv6) (dv' : Nat → Efab) (tradd : List Estep)
        (m1 : SailM Unit) (rs11 rs21 : RegFile) (fn1 : Ofence) (ib1 : Ibch),
        c'.cdTr = c.cdTr ++ tradd ∧
        (∀ s, s ∈ tradd → s.esAg = x) ∧
        List.Forall₂ lblReidxW rowseg (tradd.map (fun s => s.esLb)) ∧
        srvwmoConsistent c' ∧
        Ctx (k0 + rowseg.length) c' ∧
        execProgOk' (pstepPin c.cdImg pstepEv) pclsEv pst' dv' (candExec c') ∧
        (pst' (cdEnd c'))[x]? = some (.PHart cpu m1 rs21 fn1 ib1) ∧
        dv' (cdEnd c') = d0 ∧
        pfin = .PHart cpu m1 rs11 fn1 ib1 ∧
        dregAgree (fun n => n ∉ T) rs11 rs21 ∧
        ((candLastSt c').msWs x).wRelp = (rowWsAux k0 ws0 rowseg).wRelp ∧
        c'.cdImg = c.cdImg ∧
        pst' 0 = pst 0 ∧
        dv' 0 = dv 0 ∧
        (∀ y, y ≠ x → (pst' (cdEnd c'))[y]? = (pst (cdEnd c))[y]?) ∧
        (∀ y, y ≠ x → ((candLastSt c').msWs y).wRelp = ((candLastSt c).msWs y).wRelp) := by
  intro hem
  induction hem with
  | HEnil k ws p =>
    intro _ m0 rs10 fn0 ib0 hp0 c pst dv rs20 hc hctx _ hpo hp hdv hag hrelp
    exact ⟨c, pst, dv, [], m0, rs10, rs20, fn0, ib0, by simp,
      fun s hs => absurd hs List.not_mem_nil, .nil, hc, hctx, hpo, hp, hdv, hp0, hag, hrelp,
      rfl, rfl, rfl, fun _ _ => rfl, fun _ _ => rfl⟩
  | HEone k ws lb row p ls pa da l p' es pfin har hre hst _ ih =>
    intro hrf m0 rs10 fn0 ib0 hp0 c pst dv rs20 hc hctx hes hpo hp hdv hag hrelp
    subst hp0
    have hlb : Q k lb := hrf 0 lb rfl
    have hrf' : ∀ i lb0, row[i]? = some lb0 → Q (k + 1 + i) lb0 := by
      intro i lb0 hi
      have h0 := hrf (i + 1) lb0 hi
      rwa [show k + (i + 1) = k + 1 + i by omega] at h0
    obtain ⟨ma, rsa, fna, iba, rfl⟩ := admRunPhart true _ _ d0 ls da har cpu m0 rs10 fn0 ib0 rfl
    obtain ⟨m1, rs11, fn1, ib1, rfl⟩ := pstepEvPhart cpu ma rsa fna iba da l p' d0 hst
    obtain ⟨hpin, hes'⟩ := WeakRvwmoCert2.esPinBlock c.cdImg ls l k es hes
    obtain ⟨rds, wrs, hblk⟩ := WeakRvwmoCert2.cblkIntroPin c.cdImg cpu d0 ws lb l ls
      (.PHart cpu ma rsa fna iba) da m0 rs10 fn0 ib0 m1 rs11 fn1 ib1 har hpin hre hst
    obtain ⟨lb', l', rds', wrs', rs21, hblk2, hok, hri, hcl, hag2⟩ :=
      Hpol' k c ws lb l rds wrs m0 rs10 rs20 fn0 ib0 m1 rs11 fn1 ib1 hc hctx hlb hrelp hag hblk
    obtain ⟨hc2, hpo2⟩ := certBlockSnoc c x pst dv cpu d0 lb' l' rds' wrs' m0 rs20 fn0 ib0 m1 rs21
      fn1 ib1 hc hpo hp hdv
      (WeakRvwmoCert2.cblkRelpG _ cpu d0 ws ((candLastSt c).msWs x) lb' l' rds' wrs' m0 rs20 fn0
        ib0 m1 rs21 fn1 ib1 hrelp hblk2) hok
    have hctx2 : Ctx (k + 1) (candSnoc c ⟨x, lb'⟩) := Hpres k c lb lb' hctx hc hlb hri hok hcl
    have hend : cdEnd (candSnoc c ⟨x, lb'⟩) = cdEnd c + 1 := cdEndSnoc c _
    have hp2 : (pstSnoc c pst x (.PHart cpu m1 rs21 fn1 ib1) (cdEnd (candSnoc c ⟨x, lb'⟩)))[x]?
        = some (.PHart cpu m1 rs21 fn1 ib1) := by
      rw [hend, pstSnocGt c pst x _ (cdEnd c + 1) (by omega)]
      exact List.getElem?_set_self (lookup_lt_Some hp)
    have hdv2 : dvSnoc c dv d0 (cdEnd (candSnoc c ⟨x, lb'⟩)) = d0 := by
      rw [hend, dvSnocGt c dv d0 (cdEnd c + 1) (by omega)]
    have hrelp2 : ((candLastSt (candSnoc c ⟨x, lb'⟩)).msWs x).wRelp
        = (lblPost k ws lb).wRelp := by
      rw [candSnocRelp, hrelp, lblReidxWRelp _ lb lb' hri, lblPostRelp]
    obtain ⟨c', pst', dv', tradd, m2, rs12, rs22, fn2, ib2, htr, hag', hf2, hc', hctx', hpo',
      hp'', hdv', hfin, hagf, hrelpf, himg2, hpst02, hdv02, hfr2, hfrp2⟩ :=
      ih hrf' m1 rs11 fn1 ib1 rfl (candSnoc c ⟨x, lb'⟩)
        (pstSnoc c pst x (.PHart cpu m1 rs21 fn1 ib1)) (dvSnoc c dv d0) rs21 hc2 hctx2 hes' hpo2
        hp2 hdv2 hag2 hrelp2
    refine ⟨c', pst', dv', ⟨x, lb'⟩ :: tradd, m2, rs12, rs22, fn2, ib2, ?_, ?_,
      .cons hri hf2, hc', ?_, hpo', hp'', hdv', hfin, hagf, hrelpf, ?_, ?_, ?_, ?_, ?_⟩
    · rw [htr, candSnocTr, List.append_assoc]
      rfl
    · intro s hs
      rcases List.mem_cons.1 hs with rfl | hs
      · rfl
      · exact hag' s hs
    · rw [List.length_cons, show k + (row.length + 1) = k + 1 + row.length by omega]
      exact hctx'
    · rw [himg2]; rfl
    · rw [hpst02, pstSnocLe c pst x _ 0 (Nat.zero_le _)]
    · rw [hdv02, dvSnocLe c dv d0 0 (Nat.zero_le _)]
    · intro y hy
      rw [hfr2 y hy, hend, pstSnocGt c pst x _ (cdEnd c + 1) (by omega)]
      exact List.getElem?_set_ne (Ne.symm hy)
    · intro y hy
      rw [hfrp2 y hy, candSnocRelpNe c x y lb' hy]
  | HEpair k ws lb row p ls1 pa da l1 pm dm ls2 pm2 dm2 l2 p' es pfin har1 hre hst1 har2 hst2 _
      ih =>
    intro hrf m0 rs10 fn0 ib0 hp0 c pst dv rs20 hc hctx hes hpo hp hdv hag hrelp
    subst hp0
    have hlb : Q k lb := hrf 0 lb rfl
    have hrf' : ∀ i lb0, row[i]? = some lb0 → Q (k + 1 + i) lb0 := by
      intro i lb0 hi
      have h0 := hrf (i + 1) lb0 hi
      rwa [show k + (i + 1) = k + 1 + i by omega] at h0
    obtain ⟨ma, rsa, fna, iba, rfl⟩ :=
      admRunPhart true _ _ d0 ls1 da har1 cpu m0 rs10 fn0 ib0 rfl
    obtain ⟨mb, rsb, fnb, ibb, rfl⟩ := pstepEvPhart cpu ma rsa fna iba da l1 pm dm hst1
    obtain ⟨mc, rsc, fnc, ibc, rfl⟩ := admRunPhart false _ _ dm ls2 dm2 har2 cpu mb rsb fnb ibb rfl
    obtain ⟨m1, rs11, fn1, ib1, rfl⟩ := pstepEvPhart cpu mc rsc fnc ibc dm2 l2 p' d0 hst2
    obtain ⟨hpin1, hes1⟩ := WeakRvwmoCert2.esPinBlock c.cdImg ls1 l1 k _ hes
    obtain ⟨-, hes'⟩ := WeakRvwmoCert2.esPinBlock c.cdImg ls2 l2 k es hes1
    obtain ⟨rds, wrs, hblk⟩ := WeakRvwmoCert3.cblkpIntroPin c.cdImg cpu d0 ws lb l1 l2 ls1
      (.PHart cpu ma rsa fna iba) da (.PHart cpu mb rsb fnb ibb) dm ls2 (.PHart cpu mc rsc fnc ibc)
      dm2 m0 rs10 fn0 ib0 m1 rs11 fn1 ib1 har1 hpin1 hre hst1 har2 hst2
    obtain ⟨rs21, hblk2, hok, hcl, hag2⟩ :=
      Hpolp k c ws lb l1 l2 rds wrs m0 rs10 rs20 fn0 ib0 m1 rs11 fn1 ib1 hc hctx hlb hrelp hag hblk
    obtain ⟨hc2, hpo2⟩ := certBlockSnocPair c x pst dv cpu d0 lb l1 l2 rds wrs m0 rs20 fn0 ib0 m1
      rs21 fn1 ib1 hc hpo hp hdv
      (WeakRvwmoCert3.cblkpRelpG _ cpu d0 ws ((candLastSt c).msWs x) lb l1 l2 rds wrs m0 rs20 fn0
        ib0 m1 rs21 fn1 ib1 hrelp hblk2) hok
    have hctx2 : Ctx (k + 1) (candSnoc c ⟨x, lb⟩) :=
      Hpres k c lb lb hctx hc hlb (lblReidxWRefl lb) hok hcl
    have hend : cdEnd (candSnoc c ⟨x, lb⟩) = cdEnd c + 1 := cdEndSnoc c _
    have hp2 : (pstSnoc c pst x (.PHart cpu m1 rs21 fn1 ib1) (cdEnd (candSnoc c ⟨x, lb⟩)))[x]?
        = some (.PHart cpu m1 rs21 fn1 ib1) := by
      rw [hend, pstSnocGt c pst x _ (cdEnd c + 1) (by omega)]
      exact List.getElem?_set_self (lookup_lt_Some hp)
    have hdv2 : dvSnoc c dv d0 (cdEnd (candSnoc c ⟨x, lb⟩)) = d0 := by
      rw [hend, dvSnocGt c dv d0 (cdEnd c + 1) (by omega)]
    have hrelp2 : ((candLastSt (candSnoc c ⟨x, lb⟩)).msWs x).wRelp
        = (lblPost k ws lb).wRelp := by
      rw [candSnocRelp, hrelp, lblPostRelp]
    obtain ⟨c', pst', dv', tradd, m2, rs12, rs22, fn2, ib2, htr, hag', hf2, hc', hctx', hpo',
      hp'', hdv', hfin, hagf, hrelpf, himg2, hpst02, hdv02, hfr2, hfrp2⟩ :=
      ih hrf' m1 rs11 fn1 ib1 rfl (candSnoc c ⟨x, lb⟩)
        (pstSnoc c pst x (.PHart cpu m1 rs21 fn1 ib1)) (dvSnoc c dv d0) rs21 hc2 hctx2 hes' hpo2
        hp2 hdv2 hag2 hrelp2
    refine ⟨c', pst', dv', ⟨x, lb⟩ :: tradd, m2, rs12, rs22, fn2, ib2, ?_, ?_,
      .cons (lblReidxWRefl lb) hf2, hc', ?_, hpo', hp'', hdv', hfin, hagf, hrelpf, ?_, ?_, ?_,
      ?_, ?_⟩
    · rw [htr, candSnocTr, List.append_assoc]
      rfl
    · intro s hs
      rcases List.mem_cons.1 hs with rfl | hs
      · rfl
      · exact hag' s hs
    · rw [List.length_cons, show k + (row.length + 1) = k + 1 + row.length by omega]
      exact hctx'
    · rw [himg2]; rfl
    · rw [hpst02, pstSnocLe c pst x _ 0 (Nat.zero_le _)]
    · rw [hdv02, dvSnocLe c dv d0 0 (Nat.zero_le _)]
    · intro y hy
      rw [hfr2 y hy, hend, pstSnocGt c pst x _ (cdEnd c + 1) (by omega)]
      exact List.getElem?_set_ne (Ne.symm hy)
    · intro y hy
      rw [hfrp2 y hy, candSnocRelpNe c x y lb hy]

/-! # 4. OBLIGATION (O-1): THE FUSED EXCLUSIVE PAIR -/

/-! ## 4.1 A latest source needs no floor argument -/

theorem floorOkOfLatest (c : Cand) (i : Nat) (aq : Bool) (base : Int) (ts : List Nat) :
    srvwmoConsistent c →
    (∀ (j : Nat) t, ts[j]? = some t → latest c.cdImg (cdLogEnd c) (accAddr base j) t) →
    floorOk c i aq base ts := by
  intro hc hlat j t hj hw
  have hbi := candLastBounded c hc i
  rw [candLastLog] at hbi
  obtain ⟨_, htop⟩ := hlat j t hj
  apply htop
  apply writesInMonoHi _ _ _ _ _ ?_ hw
  have h1 := loadVpreBounded ((candLastSt c).msWs i) aq _ hbi
  have h2 := hbi.2.2.2.2.2.2.1 (accAddr base j)
  simp only [cdFloor]
  omega

/-! ## 4.2 THE BRIDGE: an RMW's G-source IS the candidate's latest -/

theorem certRmwLatest (G : Gexec) (c : Cand) (ev : Nat → Geid) (W : Geid → Prop) (e : Geid)
    (a : Int) (t : Nat) (v : BitVec 8) :
    rvwmoMinusConsistent G →
    CtracePrefix G c ev W →
    greadsByte G e a t v →
    glblIs G e lbIsW →
    gwix G e = (cdLogEnd c).length + 1 →
    t ≤ (cdLogEnd c).length →
    latest c.cdImg (cdLogEnd c) a t := by
  rintro ⟨hwf, _, hlv, hat⟩ hgt hrb hw hix hle
  refine ⟨?_, ?_⟩
  · have hval := (hlv _ _ _ _ hrb).1
    cases t with
    | zero =>
      have hval' : G.gxImg a = some v := hval
      rw [logByte0, hgt.ctpImg, hval']
      rfl
    | succ n =>
      obtain ⟨w, hw', hwb, _⟩ := hval
      show (logByte c.cdImg (cdLog c c.cdTr.length) (n + 1) a).isSome
      rw [ctpLogByte G c ev W hgt (n + 1) w a v (by omega) hle hw' hwb]
      rfl
  · rintro ⟨s, hlo, hhi, m, hm, hby⟩
    obtain ⟨w, v', hws, hwb⟩ := ctpLogWrites G c ev W hgt s m (by omega) hm a hby
    have hgwix : gwix G w = s := (gwriteAtInv G s w hwf.1 hws).2
    exact hat e a t v hrb hw w v' hwb ⟨by omega, by omega⟩

/-! ## 4.3 `mstepOk` at the RMW, with no floor obligation -/

theorem certRmwOk (G : Gexec) (c : Cand) (ev : Nat → Geid) (W : Geid → Prop) (x : Nat)
    (aq rl : Bool) (base : Int) (ts : List Nat) (rvs wvs : List (BitVec 8)) (kc : WmClass) :
    rvwmoMinusConsistent G →
    CtracePrefix G c ev W →
    srvwmoConsistent c →
    gxLbl G (x, gcnt x c.cdTr) = some (.LRmw aq rl base ts rvs wvs kc) →
    gwix G (x, gcnt x c.cdTr) = (cdLogEnd c).length + 1 →
    (∀ (j : Nat) t, ts[j]? = some t → t ≤ (cdLogEnd c).length) →
    srcInLog c base ts rvs →
    mstepOk (candLastSt c) x (.LRmw aq rl base ts rvs wvs kc) := by
  intro hcons hgt hc hl hix hbnd hsrc
  obtain ⟨hne, hlenw, hlenr⟩ := WeakRvwmoFloor.gshape G hcons.1 _ _ hl
  have hisw : glblIs G (x, gcnt x c.cdTr) lbIsW := ⟨_, hl, rfl⟩
  have hlat : ∀ (j : Nat) t, ts[j]? = some t →
      latest c.cdImg (cdLogEnd c) (accAddr base j) t := by
    intro j t hj
    obtain ⟨v, hv⟩ := someOfIsSome (lookup_lt_is_Some_2
      (show j < rvs.length by rw [hlenr]; exact lookup_lt_Some hj))
    exact certRmwLatest G c ev W _ _ t v hcons hgt
      ⟨_, base, ts, rvs, j, hl, rfl, hj, hv, rfl⟩ hisw hix (hbnd j t hj)
  refine ⟨hne, hlenw, snocRdOk c x aq base ts rvs
    (snocRdAdmOf c x aq base ts rvs hsrc (floorOkOfLatest c x aq base ts hc hlat)), ?_⟩
  show rmwLatest (candLastSt c).msImg (candLastSt c).msLog base ts
  rw [candLastImg, candLastLog]
  exact hlat

/-! ## 4.4 THE MIRROR, at the pair -/

/-- (Lean-only, deviation 4) `certBlockPairMirror` at any admin predicate `A`. -/
theorem WeakRvwmoCert3.certBlockPairMirrorG (A : Wlabel → Prop)
    (P : Nat → Prop) (cpu : CPU) (d0 : Efab) (ws : Wstate) (lb : Lbl)
    (l1 l2 : Wlabel) (rds : List Nat) (wrs : List Register) (m : SailM Unit) (rs1 : RegFile)
    (fn : Ofence) (ib : Ibch) (m' : SailM Unit) (rs1' : RegFile) (fn' : Ofence) (ib' : Ibch)
    (rs2 : RegFile) :
    WeakRvwmoCert3.cblkpG A cpu d0 ws lb l1 l2 rds wrs m rs1 fn ib m' rs1' fn' ib' →
    rdsOk P rds →
    dregAgree P rs1 rs2 →
    ∃ rs2', WeakRvwmoCert3.cblkpG A cpu d0 ws lb l1 l2 rds wrs m rs2 fn ib m' rs2' fn' ib' ∧
      dregAgree P rs1' rs2' := by
  rintro ⟨ls1, ma, rsa, fna, iba, da, rdsA, wrsA, annA, mm, rsm, fnm, ibm, dm, rdsB, wrsB, annB,
    ls2, mm2, rsm2, fnm2, ibm2, dm2, rdsC, wrsC, annC, rdsD, wrsD, annD, had1, hA, hre, hB, had2,
    hC, hD, rfl, rfl⟩ hrds hag
  obtain ⟨hrdsA, hrds⟩ := rdsOkApp P _ _ hrds
  obtain ⟨hrdsB, hrds⟩ := rdsOkApp P _ _ hrds
  obtain ⟨hrdsC, hrdsD⟩ := rdsOkApp P _ _ hrds
  obtain ⟨rsa2, hA2, haga⟩ := phrunDagree P cpu ls1 rdsA wrsA annA m rs1 fn ib d0 ma rsa fna iba
    da hA hrdsA rs2 hag
  obtain ⟨rsmb, hB2, hagb⟩ := phrunDagree P cpu [l1] rdsB wrsB annB ma rsa fna iba da mm rsm fnm
    ibm dm hB hrdsB rsa2 haga
  obtain ⟨rsm22, hC2, hagc⟩ := phrunDagree P cpu ls2 rdsC wrsC annC mm rsm fnm ibm dm mm2 rsm2
    fnm2 ibm2 dm2 hC hrdsC rsmb hagb
  obtain ⟨rs2', hD2, hagd⟩ := phrunDagree P cpu [l2] rdsD wrsD annD mm2 rsm2 fnm2 ibm2 dm2 m' rs1'
    fn' ib' d0 hD hrdsD rsm22 hagc
  exact ⟨rs2', ⟨ls1, ma, rsa2, fna, iba, da, rdsA, wrsA, annA, mm, rsmb, fnm, ibm, dm, rdsB, wrsB,
    annB, ls2, mm2, rsm22, fnm2, ibm2, dm2, rdsC, wrsC, annC, rdsD, wrsD, annD, had1, hA2,
    hlblRealizesPairRs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hre, hB2, had2, hC2, hD2, rfl, rfl⟩,
    hagd⟩

theorem certBlockPairMirror (P : Nat → Prop) (cpu : CPU) (d0 : Efab) (ws : Wstate) (lb : Lbl)
    (l1 l2 : Wlabel) (rds : List Nat) (wrs : List Register) (m : SailM Unit) (rs1 : RegFile)
    (fn : Ofence) (ib : Ibch) (m' : SailM Unit) (rs1' : RegFile) (fn' : Ofence) (ib' : Ibch)
    (rs2 : RegFile) :
    cblkp cpu d0 ws lb l1 l2 rds wrs m rs1 fn ib m' rs1' fn' ib' →
    rdsOk P rds →
    dregAgree P rs1 rs2 →
    ∃ rs2', cblkp cpu d0 ws lb l1 l2 rds wrs m rs2 fn ib m' rs2' fn' ib' ∧
      dregAgree P rs1' rs2' :=
  WeakRvwmoCert3.certBlockPairMirrorG (lbAdmin true) P cpu d0 ws lb l1 l2 rds wrs m rs1 fn ib m'
    rs1' fn' ib' rs2

/-! ## 4.5 THE PAIR, CERTIFIED -/

theorem certBlockPair (T : List Nat) (G : Gexec) (c : Cand) (ev : Nat → Geid) (W : Geid → Prop)
    (x : Nat) (pst : Nat → List Pexv6) (dv : Nat → Efab) (cpu : CPU) (d0 : Efab) (aq rl : Bool)
    (base : Int) (ts : List Nat) (rvs wvs : List (BitVec 8)) (kc : WmClass) (l1 l2 : Wlabel)
    (rds : List Nat) (wrs : List Register) (m : SailM Unit) (rs1 : RegFile) (fn : Ofence)
    (ib : Ibch) (m' : SailM Unit) (rs1' : RegFile) (fn' : Ofence) (ib' : Ibch) (rs2 : RegFile) :
    rvwmoMinusConsistent G →
    CtracePrefix G c ev W →
    srvwmoConsistent c →
    execProgOk' (pstepPin c.cdImg pstepEv) pclsEv pst dv (candExec c) →
    (pst (cdEnd c))[x]? = some (.PHart cpu m rs2 fn ib) →
    dv (cdEnd c) = d0 →
    WeakRvwmoCert3.cblkpPin c.cdImg cpu d0 ((candLastSt c).msWs x) (.LRmw aq rl base ts rvs wvs kc)
      l1 l2 rds wrs m rs1 fn ib m' rs1' fn' ib' →
    rdsOk (fun n => n ∉ T) rds →
    dregAgree (fun n => n ∉ T) rs1 rs2 →
    gxLbl G (x, gcnt x c.cdTr) = some (.LRmw aq rl base ts rvs wvs kc) →
    gwix G (x, gcnt x c.cdTr) = (cdLogEnd c).length + 1 →
    (∀ (j : Nat) t, ts[j]? = some t → t ≤ (cdLogEnd c).length) →
    srcInLog c base ts rvs →
    ∃ rs2',
      srvwmoConsistent (candSnoc c ⟨x, .LRmw aq rl base ts rvs wvs kc⟩) ∧
      execProgOk' (pstepPin c.cdImg pstepEv) pclsEv (pstSnoc c pst x (.PHart cpu m' rs2' fn' ib'))
        (dvSnoc c dv d0) (candExec (candSnoc c ⟨x, .LRmw aq rl base ts rvs wvs kc⟩)) ∧
      dregAgree (fun n => n ∉ T) rs1' rs2' := by
  intro hcons hgt hc hpo hp hdv hblk hrds hag hl hix hbnd hsrc
  obtain ⟨rs2', hblk2, hag2⟩ := WeakRvwmoCert3.certBlockPairMirrorG _ (fun n => n ∉ T) cpu d0 _ _
    l1 l2 rds wrs m rs1 fn ib m' rs1' fn' ib' rs2 hblk hrds hag
  obtain ⟨hc2, hpo2⟩ := certBlockSnocPair c x pst dv cpu d0 _ l1 l2 rds wrs m rs2 fn ib m' rs2'
    fn' ib' hc hpo hp hdv hblk2
    (certRmwOk G c ev W x aq rl base ts rvs wvs kc hcons hgt hc hl hix hbnd hsrc)
  exact ⟨rs2', hc2, hpo2, hag2⟩

end Weak
