/-
Weak: **the segment-composition kill** (route B, stage B2e-3c).

Rocq: `iris/WeakRvwmoKillArms.v` @ xxvzwolszwmp.

The Rocq header, in substance (design: `claude-notes/design/weak-memory-route-b.md`
§4d.2(3) and §4d.3′).

THE SETTING.  A graph `G` (`rvwmoMinusConsistent`) together with a LOG `log` that
is the gmo-ordered message list of a PREFIX of `G`'s writes.  §1 is the
DICTIONARY between the two vocabularies: log position `p` is graph write index
`p + 1` (`logOf`).

THE KILL.  An `R`-cycle is presented as a list of SEGMENTS (hart, entry event,
exit write) with a cross-hart edge (rf / co / fr) from each segment's
predecessor's exit to its entry, and a per-segment CERTIFICATE of one of three
kinds (§2): `Pinned` (`gmoLt G entry exit` outright), `CSchained`
(`gmoLt G prevExit exit` derived THROUGH the lock window, §4: `csChained`),
`Bad` (the hypothesis `False`; φ refutes the configuration, out of scope).
`cycleKillArms` chains the `gmoLt` steps around the cycle and closes on
`gmoLtIrrefl`.

§4: both window orders close.  WRITER-FIRST (`q < pA`): `wlpAltTwoAcq` puts a
release BY THE WRITER between the two acquires, and `wprotAt`'s no-release clause
forces it ABOVE the write, so `gwix w < gwix ACQ`, and ppo rule 5 carries `ACQ`
to the exit.  READER-FIRST is REFUTED: the same lemma puts a release BY THE
READER between them, `lockCs` identifies it at or above `REL`, and
`REL <co ACQ_w <co w`, `w <gmo entry`, `entry <gmo REL` is a gmo cycle.

THE ONE BRIDGE THAT IS A HYPOTHESIS: `lockWordByte` — a message whose byte `b`
is zero has the whole word zero (F3′'s fold tests the WORD, the graph kit tests
ONE BYTE).  Discharged on the witnesses.  The converse is free (`zero4Byte`).

THE KILL CONSUMES THE EXPORTS (`wlpAlt`, `wprotAt`, `logOf`) AND THE READER'S
OWN ROW (`acqRow`), NEVER THE GLOBAL `lockPattern`, which is false for xv6
(§6b's contended-lock witness `lkw2` refutes it: `lkw2NoPattern`).

§5–§6b — NON-VACUITY: the LB cycle is a two-segment cycle on which
`cycleKillArms` fires once both (false, `lbgPinnedAbsent`) `Pinned`
certificates are supplied; `lkw` (uncontended, 4-byte lock word) and `lkw2`
(one failed swap, `lockPattern` refuted) discharge every hypothesis of
`csChained` and DERIVE its conclusion.  (`WeakRvwmoLockWit.lkg` cannot serve:
its one-byte `WCrel` release makes F3′'s fold `none`.)

**Deviations from Rocq.**

1. NAMES: lowerCamelCase as `Weak/WeakMem.lean` deviation 1.  The names of this
   file in `notes/weak-port-dupnames.json` are file-qualified:
   `WeakRvwmoKillArms.gmsg`, `WeakRvwmoKillArms.gmsgByte`,
   `WeakRvwmoKillArms.chain`, `WeakRvwmoKillArms.lbgGrf01`,
   `WeakRvwmoKillArms.lbgGrf10`, `WeakRvwmoKillArms.imgw`,
   `WeakRvwmoKillArms.z4`, `WeakRvwmoKillArms.o4`.  The record `seg` (constructor
   `Seg`) is the structure `Seg` (constructor `Seg.mk`); the inductive `cert` is
   `Cert`, its constructors keep their spelling (`Pinned`, `CSchained`, `Bad`).
2. VOCABULARY: as `WeakRvwmoLock` deviation 2 (`Z` ↦ `Int`, `bv 8` ↦
   `BitVec 8`, `is_Some o` ↦ `o.isSome`, `l !! i` ↦ `l[i]?`, `S n` ↦ `n + 1`,
   `(a ≤ x < b)` ↦ `a ≤ x ∧ x < b`, `WMsg a d t k` ↦ `⟨a, d, t, k⟩`, `agent` ↦
   `Nat`); `grf` ↦ `WeakRvwmoAcyc.grf`, `Racy` ↦ `racy`, `gpo` ↦
   `WeakRvwmoGraph.gpo`, `lb_graph_consistent` ↦ `lbGraphConsistent`;
   `WeakLitmus.b0`/`b1`/`b0_ne_b1` ↦ `b0`/`b1`/`b0NeB1`.  The Rocq
   `Local Notation`s `ACQw` … `REL2` are Lean `local notation`s.
3. The closed `vm_compute` side conditions are `decide`.
4. Lean-only helpers (no Rocq twin): `gmsgInv` (the inversion of `gmsg` the
   three `gmsg_*` lemmas inline), `logOfIntro` (the pointwise shape both
   `lkw_log_of` proofs use), `lkwLbl` / `lkw2Lbl` (the labels of the two
   witnesses, the engine of every case split, as `WeakRvwmoLockWit.lkgLbl`).
5. §7 (`Print Assumptions`) is a command, not a declaration; the lint's
   sorry/axiom/native_decide checks stand in for it.

**Name map** (Rocq → Lean): `gmsg` ↦ `WeakRvwmoKillArms.gmsg`; `log_of` ↦
`logOf`; `gcls`; `gmsg_is_Some` ↦ `gmsgIsSome`; `gmsg_tid` ↦ `gmsgTid`;
`gmsg_cls` ↦ `gmsgCls`; `gmsg_byte` ↦ `WeakRvwmoKillArms.gmsgByte`;
`gmsg_byte_None` ↦ `gmsgByteNone`; `log_of_lookup` ↦ `logOfLookup`;
`log_of_write` ↦ `logOfWrite`; `gcross`; `gcross_gmo` ↦ `gcrossGmo`;
`gcross_Racy` ↦ `gcrossRacy`; `seg`/`Seg`/`sg_hart`/`sg_entry`/`sg_exit` ↦
`Seg`/`Seg.mk`/`sgHart`/`sgEntry`/`sgExit`; `cert` ↦ `Cert`; `cert_gmo` ↦
`certGmo`; `chain` ↦ `WeakRvwmoKillArms.chain`; `chain_gmo` ↦ `chainGmo`;
`cycle_kill_arms` ↦ `cycleKillArms`; `lock_word_byte` ↦ `lockWordByte`;
`zero4_byte` ↦ `zero4Byte`; `log_rel_graph` ↦ `logRelGraph`; `log_acq_graph` ↦
`logAcqGraph`; `holder_acq_graph` ↦ `holderAcqGraph`; `release_between_graph` ↦
`releaseBetweenGraph`; `acq_row` ↦ `acqRow`; `acq_row_is_r` ↦ `acqRowIsR`;
`acq_row_of_pattern` ↦ `acqRowOfPattern`; `acq_fold_free` ↦ `acqFoldFree`;
`cs_chained` ↦ `csChained`; `lbg_grf_01`/`_10` ↦
`WeakRvwmoKillArms.lbgGrf01`/`lbgGrf10`; `lb_segs` ↦ `lbSegs`;
`lbg_pinned_would_kill` ↦ `lbgPinnedWouldKill`; `lbg_pinned_absent` ↦
`lbgPinnedAbsent`; `imgw`/`z4`/`o4` ↦ `WeakRvwmoKillArms.imgw`/`.z4`/`.o4`;
`lkw`; `z4_lookup` ↦ `z4Lookup`; `gwrites_byte_of` ↦ `gwritesByteOf`; `imgw_in`
↦ `imgwIn`; `lkw_nodup` ↦ `lkwNodup`; `lkw_gpos_of` ↦ `lkwGposOf`;
`lkw_gwix_of` ↦ `lkwGwixOf`; `lkw_p0`…`lkw_p5` ↦ `lkwP0`…`lkwP5`;
`lkw_gwrites` ↦ `lkwGwrites`; `lkw_x1`…`lkw_x5` ↦ `lkwX1`…`lkwX5`;
`lkw_mem_inv` ↦ `lkwMemInv`; `lkw_gmo_mem` ↦ `lkwGmoMem`; `lkw_mo` ↦ `lkwMo`;
`lkw_gmo_po` ↦ `lkwGmoPo`; `lkw_wr` ↦ `lkwWr`; `lkw_rd` ↦ `lkwRd`;
`lkw_wr_lock` ↦ `lkwWrLock`; `lkw_wr_data` ↦ `lkwWrData`; `lkw_consistent` ↦
`lkwConsistent`; `lkw_pattern` ↦ `lkwPattern`; `lkw_acq_r` ↦ `lkwAcqR`;
`lkw_acq_row` ↦ `lkwAcqRow`; `lkw_rel_r` ↦ `lkwRelR`; `lkw_aq_r` ↦ `lkwAqR`;
`lkw_cs_r` ↦ `lkwCsR`; `lkw_fence_r` ↦ `lkwFenceR`; `lkw_grf` ↦ `lkwGrf`;
`lkw_wp_plain` ↦ `lkwWpPlain`; `lkw_wp_data` ↦ `lkwWpData`; `lkw_wp_no_lock` ↦
`lkwWpNoLock`; `lkw_log` ↦ `lkwLog`; `msg_byte_o4_0`/`z4_0`/`o4_8`/`z4_8`/`d_0`
↦ `msgByteO40`/`msgByteZ40`/`msgByteO48`/`msgByteZ48`/`msgByteD0`;
`lkw_log_of` ↦ `lkwLogOf`; `lkw_log_0`…`lkw_log_4`/`lkw_log_hi` ↦
`lkwLog0`…`lkwLog4`/`lkwLogHi`; `lkw_lwb` ↦ `lkwLwb`; `lkw_alt` ↦ `lkwAlt`;
`lkw_wprot` ↦ `lkwWprot`; `lkw_log_len` ↦ `lkwLogLen`; `lkw_cs_chained` ↦
`lkwCsChained`; `lkw_cert` ↦ `lkwCert`; `lkw2`; `o4_lookup` ↦ `o4Lookup`;
`imgw_in2` ↦ `imgwIn2`; and every `lkw2_*` ↦ `lkw2*` in the same way
(`lkw2_p0`…`p6`, `lkw2_x1`…`x6`, `lkw2_swp_wr` ↦ `lkw2SwpWr`, `lkw2_no_pattern`
↦ `lkw2NoPattern`, `lkw2_acq2` ↦ `lkw2Acq2`, `lkw2_acq_row` ↦ `lkw2AcqRow`,
`lkw2_rel2` ↦ `lkw2Rel2`, `lkw2_aq2` ↦ `lkw2Aq2`, `lkw2_log_0`…`5`/`_hi`, …).

**Not ported:** nothing.

**Statements checked** (by hand, against Rocq): all of them.
-/
import Weak.WeakMem
import Weak.WeakLitmus
import Weak.WeakAxiomatic
import Weak.WeakGhost
import Weak.WeakRvwmoGraph
import Weak.WeakRvwmoXchg
import Weak.WeakRvwmoAcyc
import Weak.WeakRvwmoLock

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Lbl

/-! # 1. The log dictionary

`gmsg` is `WeakRvwmoFloor.gwmsg` restated; `logOf` is the index convention of
`gtp_log`, read as an equivalence: LOG POSITION `p` IS GRAPH WRITE INDEX `p + 1`. -/

def WeakRvwmoKillArms.gmsg (G : Gexec) (w : Geid) : Option Wmsg :=
  match gxLbl G w with
  | some l =>
    match lbWr l with
    | some (base, vs) => some ⟨base, vs, some w.1, lbCls l⟩
    | none => none
  | none => none

/-- The log is the message list of a gmo-PREFIX of `G`'s writes. -/
def logOf (G : Gexec) (log : List Wmsg) : Prop :=
  ∀ (p : Nat) m, log[p]? = some m ↔
    ∃ w, gwriteAt G (p + 1) = some w ∧ WeakRvwmoKillArms.gmsg G w = some m

/-- The class a graph event's write half publishes. -/
def gcls (G : Gexec) (w : Geid) (k : WmClass) : Prop :=
  ∃ l, gxLbl G w = some l ∧ lbCls l = k

/-- Lean-only: the inversion of `gmsg`. -/
theorem gmsgInv (G : Gexec) (w : Geid) (m : Wmsg) :
    WeakRvwmoKillArms.gmsg G w = some m →
    ∃ l base vs, gxLbl G w = some l ∧ lbWr l = some (base, vs) ∧
      m = ⟨base, vs, some w.1, lbCls l⟩ := by
  intro h
  rcases hl : gxLbl G w with _ | l
  · simp [WeakRvwmoKillArms.gmsg, hl] at h
  · rcases hwr : lbWr l with _ | ⟨base, vs⟩
    · simp [WeakRvwmoKillArms.gmsg, hl, hwr] at h
    · simp only [WeakRvwmoKillArms.gmsg, hl, hwr, Option.some.injEq] at h
      exact ⟨l, base, vs, rfl, hwr, h.symm⟩

theorem gmsgIsSome (G : Gexec) (w : Geid) :
    gisW G w = true → (WeakRvwmoKillArms.gmsg G w).isSome := by
  intro hw
  unfold gisW at hw
  rcases hl : gxLbl G w with _ | l
  · rw [hl] at hw; cases hw
  · rw [hl] at hw
    obtain ⟨base, vs, hwr⟩ := lbIsWWr l hw
    simp [WeakRvwmoKillArms.gmsg, hl, hwr]

theorem gmsgTid (G : Gexec) (w : Geid) (m : Wmsg) :
    WeakRvwmoKillArms.gmsg G w = some m → m.wmTid = some w.1 := by
  intro h
  obtain ⟨l, base, vs, -, -, rfl⟩ := gmsgInv G w m h
  rfl

theorem gmsgCls (G : Gexec) (w : Geid) (m : Wmsg) (k : WmClass) :
    gcls G w k → WeakRvwmoKillArms.gmsg G w = some m → m.wmAk = k := by
  rintro ⟨l, hl, rfl⟩ h
  obtain ⟨l', base, vs, hl', -, rfl⟩ := gmsgInv G w m h
  rw [hl, Option.some.injEq] at hl'
  subst hl'
  rfl

/-- THE BYTE DICTIONARY: `msgByte` of the message IS `gwritesByte` of the event. -/
theorem WeakRvwmoKillArms.gmsgByte (G : Gexec) (w : Geid) (m : Wmsg) (a : Int) (v : BitVec 8) :
    WeakRvwmoKillArms.gmsg G w = some m → (msgByte m a = some v ↔ gwritesByte G w a v) := by
  intro h
  obtain ⟨l, base, vs, hl, hwr, rfl⟩ := gmsgInv G w m h
  constructor
  · intro hv
    unfold msgByte at hv
    dsimp only at hv
    by_cases hle : base ≤ a
    · rw [if_pos hle] at hv
      refine ⟨l, base, vs, (a - base).toNat, hl, hwr, hv, ?_⟩
      simp only [accAddr]
      rw [Int.toNat_of_nonneg (by omega)]
      omega
    · rw [if_neg hle] at hv
      cases hv
  · rintro ⟨l', base', vs', j, hl', hwr', hv, ha⟩
    rw [hl, Option.some.injEq] at hl'
    subst hl'
    rw [hwr, Option.some.injEq, Prod.mk.injEq] at hwr'
    obtain ⟨rfl, rfl⟩ := hwr'
    simp only [accAddr] at ha
    have hle : base ≤ a := by omega
    have hj : (a - base).toNat = j := by omega
    unfold msgByte
    dsimp only
    rw [if_pos hle, hj]
    exact hv

/-- … and its negative half. -/
theorem gmsgByteNone (G : Gexec) (w : Geid) (m : Wmsg) (a : Int) :
    WeakRvwmoKillArms.gmsg G w = some m → (∀ v, ¬ gwritesByte G w a v) → msgByte m a = none := by
  intro hm hno
  cases hb : msgByte m a with
  | none => rfl
  | some v => exact absurd ((WeakRvwmoKillArms.gmsgByte G w m a v hm).1 hb) (hno v)

/-- LOG → GRAPH. -/
theorem logOfLookup (G : Gexec) (log : List Wmsg) (p : Nat) (m : Wmsg) :
    gwf G → logOf G log → log[p]? = some m →
    ∃ w, gwriteAt G (p + 1) = some w ∧ WeakRvwmoKillArms.gmsg G w = some m ∧
      gwix G w = p + 1 ∧ w ∈ gwrites G := by
  intro hwf hlog hp
  obtain ⟨w, hw, hm⟩ := (hlog p m).1 hp
  obtain ⟨hmem, hix⟩ := gwriteAtInv G (p + 1) w hwf.1 hw
  exact ⟨w, hw, hm, hix, hmem⟩

/-- GRAPH → LOG. -/
theorem logOfWrite (G : Gexec) (log : List Wmsg) (w : Geid) :
    gwf G → logOf G log → w ∈ gwrites G → gwix G w ≤ log.length →
    ∃ m, log[gwix G w - 1]? = some m ∧ WeakRvwmoKillArms.gmsg G w = some m := by
  intro _ hlog hw hle
  obtain ⟨i, hi, hix⟩ := gwixLookup G w hw
  rw [hix] at hle ⊢
  rw [Nat.add_sub_cancel]
  obtain ⟨m, hm⟩ := Option.isSome_iff_exists.1 (lookup_lt_is_Some_2 (l := log) (i := i) (by omega))
  obtain ⟨w', hw', hm'⟩ := (hlog i m).1 hm
  have hw'' : (gwrites G)[i]? = some w' := hw'
  rw [hi, Option.some.injEq] at hw''
  subst hw''
  exact ⟨m, hm, hm'⟩

/-- Lean-only: the pointwise shape of a `logOf` proof on a concrete graph. -/
theorem logOfIntro (G : Gexec) (log : List Wmsg) :
    (∀ p : Nat, log[p]? = ((gwrites G)[p]?).bind (WeakRvwmoKillArms.gmsg G)) → logOf G log := by
  intro h p m
  rw [h p]
  constructor
  · intro hb
    obtain ⟨w, hw, hm⟩ := Option.bind_eq_some_iff.1 hb
    exact ⟨w, hw, hm⟩
  · rintro ⟨w, hw, hm⟩
    exact Option.bind_eq_some_iff.2 ⟨w, hw, hm⟩

/-! # 2. Segments, certificates, and the composition kill

`racy`'s CROSS-HART arms — rf, co, fr — join one segment's exit write to the next
segment's entry.  All three are gmo-forward from `rvwmoMinusConsistent` ALONE
(unlike `gpow`, which needs rule 14). -/

def gcross (G : Gexec) (x y : Geid) : Prop :=
  WeakRvwmoAcyc.grf G x y ∨ gco G x y ∨ gfr G x y

theorem gcrossGmo (G : Gexec) (x y : Geid) :
    rvwmoMinusConsistent G → gcross G x y → gmoLt G x y := by
  rintro hcons (h | h | h)
  · exact WeakRvwmoAcyc.grfGmo G x y hcons h
  · exact gcoGmo G x y hcons.1 h
  · exact gfrGmo G x y hcons h

theorem gcrossRacy (G : Gexec) (x y : Geid) : gcross G x y → racy G x y := by
  rintro (h | h | h)
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))

/-- ONE SEGMENT of the cycle: a hart, the event the cross edge lands on, and the
write the next cross edge leaves from.  (`sgHart` is carried because the design
states the segment that way; the arithmetic never reads it.) -/
structure Seg where
  sgHart : Nat
  sgEntry : Geid
  sgExit : Geid

/-- THE THREE ARMS, as one certificate relating the PREDECESSOR's exit to this
segment's exit. -/
inductive Cert (G : Gexec) (prev : Geid) (s : Seg) : Prop where
  | Pinned : gcross G prev s.sgEntry → gmoLt G s.sgEntry s.sgExit → Cert G prev s
  | CSchained : gmoLt G prev s.sgExit → Cert G prev s
  | Bad : False → Cert G prev s

theorem certGmo (G : Gexec) (prev : Geid) (s : Seg) :
    rvwmoMinusConsistent G → Cert G prev s → gmoLt G prev s.sgExit := by
  intro hcons hc
  cases hc with
  | Pinned hx hp => exact gmoLtTrans G _ _ _ (gcrossGmo G _ _ hcons hx) hp
  | CSchained hcs => exact hcs
  | Bad h => exact h.elim

/-- A CHAIN of certified segments, from `x` to `y`. -/
def WeakRvwmoKillArms.chain (G : Gexec) (x y : Geid) : List Seg → Prop
  | [] => x = y
  | s :: ss => Cert G x s ∧ WeakRvwmoKillArms.chain G s.sgExit y ss

theorem chainGmo (G : Gexec) (x y : Geid) (ss : List Seg) :
    rvwmoMinusConsistent G → ss ≠ [] → WeakRvwmoKillArms.chain G x y ss → gmoLt G x y := by
  intro hcons
  induction ss generalizing x with
  | nil => intro hne; exact absurd rfl hne
  | cons s ss ih =>
    intro _ hch
    simp only [WeakRvwmoKillArms.chain] at hch
    obtain ⟨hc, hch⟩ := hch
    cases ss with
    | nil =>
      simp only [WeakRvwmoKillArms.chain] at hch
      rw [← hch]
      exact certGmo G x s hcons hc
    | cons s' ss' =>
      exact gmoLtTrans G x s.sgExit y (certGmo G x s hcons hc) (ih s.sgExit (by simp) hch)

/-- THE THEOREM: a CYCLE of certified segments is inconsistent. -/
theorem cycleKillArms (G : Gexec) (x : Geid) (ss : List Seg) :
    rvwmoMinusConsistent G → ss ≠ [] → WeakRvwmoKillArms.chain G x x ss → False :=
  fun hcons hne hch => gmoLtIrrefl G x (chainGmo G x x ss hcons hne hch)

/-! # 3. The translation lemmas

F3′'s fold and F3″'s protection clause speak of MESSAGES and LOG POSITIONS;
`WeakRvwmoLock`'s kit speaks of EVENTS and WRITE INDICES.  What is left is the
one genuine mismatch — the fold tests the WORD, the kit tests the BYTE. -/

/-- THE BRIDGE, as a hypothesis: byte `b` WITNESSES the lock word. -/
def lockWordByte (log : List Wmsg) (b : Int) : Prop :=
  ∀ (p : Nat) m v, log[p]? = some m → msgByte m b = some v → v = lockFree →
    m.wmData = wlockZero4

/-- The converse direction is FREE. -/
theorem zero4Byte (m : Wmsg) (b : Int) (v : BitVec 8) :
    m.wmData = wlockZero4 → msgByte m b = some v → v = lockFree := by
  intro hd hb
  unfold msgByte at hb
  rw [hd] at hb
  split at hb
  · exact List.eq_of_mem_replicate (List.mem_of_getElem? hb)
  · cases hb

/-- A zero-word message on the lock byte IS a graph RELEASE. -/
theorem logRelGraph (G : Gexec) (log : List Wmsg) (b : Int) (p : Nat) (m : Wmsg) :
    gwf G → logOf G log → log[p]? = some m →
    (msgByte m b).isSome → m.wmData = wlockZero4 →
    ∃ R, gwriteAt G (p + 1) = some R ∧ lockRel G b R ∧ gwix G R = p + 1 ∧
      R ∈ gwrites G ∧ m.wmTid = some R.1 := by
  intro hwf hlog hp hs hz
  obtain ⟨v, hb⟩ := Option.isSome_iff_exists.1 hs
  obtain ⟨R, hat, hm, hix, hw⟩ := logOfLookup G log p m hwf hlog hp
  refine ⟨R, hat, ?_, hix, hw, gmsgTid G R m hm⟩
  have hv := zero4Byte m b v hz hb
  subst hv
  exact (WeakRvwmoKillArms.gmsgByte G R m b _ hm).1 hb

/-- A nonzero message on the lock byte IS a graph ACQUIRE. -/
theorem logAcqGraph (G : Gexec) (log : List Wmsg) (b : Int) (p : Nat) (m : Wmsg) :
    gwf G → logOf G log → lockWordByte log b →
    log[p]? = some m → (msgByte m b).isSome → m.wmData ≠ wlockZero4 →
    ∃ A, gwriteAt G (p + 1) = some A ∧ lockAcq G b A ∧ gwix G A = p + 1 ∧
      A ∈ gwrites G ∧ m.wmTid = some A.1 := by
  intro hwf hlog hlwb hp hs hnz
  obtain ⟨v, hb⟩ := Option.isSome_iff_exists.1 hs
  obtain ⟨A, hat, hm, hix, hw⟩ := logOfLookup G log p m hwf hlog hp
  exact ⟨A, hat, ⟨v, (WeakRvwmoKillArms.gmsgByte G A m b v hm).1 hb,
    fun hv => hnz (hlwb p m v hp hb hv)⟩, hix, hw, gmsgTid G A m hm⟩

/-- `holderAcqGraph` — F3″'s export, translated: a plain write of a protected
byte sits inside its author's critical section, whose ACQUIRE is handed back as a
log position AND as a graph `lockAcq` event at write index `q + 1`. -/
theorem holderAcqGraph (G : Gexec) (log : List Wmsg) (b a : Int) (n0 r0 : Nat) (w : Geid) :
    gwf G → logOf G log → lockWordByte log b →
    wprotAt log a b n0 r0 →
    w ∈ gwrites G → r0 < gwix G w → gwix G w ≤ log.length →
    (∃ v, gwritesByte G w a v) → gcls G w .WCplain →
    ∃ q mq, (n0 ≤ q ∧ q < gwix G w - 1) ∧ log[q]? = some mq ∧
      (msgByte mq b).isSome ∧ mq.wmData ≠ wlockZero4 ∧
      mq.wmTid = some w.1 ∧ wlpHolderAt log b n0 q = some none ∧
      (∀ r mr, (q < r ∧ r < gwix G w - 1) → log[r]? = some mr →
        (msgByte mr b).isSome → mr.wmData ≠ wlockZero4) ∧
      (∃ ACQw, gwriteAt G (q + 1) = some ACQw ∧ lockAcq G b ACQw ∧
        gwix G ACQw = q + 1 ∧ ACQw.1 = w.1) := by
  rintro hwf hlog hlwb hpr hw hr0 hle ⟨v, hwb⟩ hcl
  obtain ⟨mw, hmw, hgw⟩ := logOfWrite G log w hwf hlog hw hle
  have hbyte : (msgByte mw a).isSome := by
    rw [(WeakRvwmoKillArms.gmsgByte G w mw a v hgw).2 hwb]; rfl
  have hak : mw.wmAk = .WCplain := gmsgCls G w mw _ hcl hgw
  have htid := gmsgTid G w mw hgw
  obtain ⟨q, mq, hq, hlk, hs, hnz, ht, hfree, hno⟩ :=
    wprotWriterCs log a b n0 r0 (gwix G w - 1) mw w.1 hpr hmw (by omega) hbyte hak htid
  obtain ⟨ACQw, hat, hacq, hix, -, htq⟩ := logAcqGraph G log b q mq hwf hlog hlwb hlk hs hnz
  refine ⟨q, mq, hq, hlk, hs, hnz, ht, hfree, hno, ACQw, hat, hacq, hix, ?_⟩
  rw [ht, Option.some.injEq] at htq
  exact htq.symm

/-- `releaseBetweenGraph` — F3′'s `wlpAltTwoAcq`, translated: between a
successful acquire and a later FREE point sits its own author's RELEASE. -/
theorem releaseBetweenGraph (G : Gexec) (log : List Wmsg) (b : Int) (n0 p q : Nat) (mp : Wmsg)
    (i : Nat) :
    gwf G → logOf G log →
    n0 ≤ p → p < q → log[p]? = some mp →
    (msgByte mp b).isSome → mp.wmData ≠ wlockZero4 → mp.wmTid = some i →
    wlpHolderAt log b n0 p = some none →
    wlpHolderAt log b n0 q = some none →
    ∃ r R mr, (p < r ∧ r < q) ∧ log[r]? = some mr ∧
      (msgByte mr b).isSome ∧ mr.wmData = wlockZero4 ∧
      gwriteAt G (r + 1) = some R ∧ lockRel G b R ∧
      gwix G R = r + 1 ∧ R ∈ gwrites G ∧ R.1 = i := by
  intro hwf hlog hn0 hpq hp hs hnz hti hfp hfq
  obtain ⟨r, mr, hr, hlk, hsr, hzr, htr⟩ :=
    wlpAltTwoAcq log b n0 p q mp i hn0 hpq hp hs hnz hti hfp hfq
  obtain ⟨R, hat, hrel, hix, hw, htid⟩ := logRelGraph G log b r mr hwf hlog hlk hsr hzr
  refine ⟨r, R, mr, hr, hlk, hsr, hzr, hat, hrel, hix, hw, ?_⟩
  rw [htr, Option.some.injEq] at htid
  exact htid.symm

/-- THE ACQUIRE'S OWN ROW — WHAT REPLACES THE GLOBAL VALUE PATTERN: the
acquire's read entry at `b` names the free byte (route-b §4d.3′'s "a SUCCESSFUL
acquire is one whose READ ENTRY is zero, a ROW fact").  Per-site, and silent on
every other `b`-write (a failed swap, a memset, a fresh `initlock`). -/
def acqRow (G : Gexec) (b : Int) (A : Geid) : Prop :=
  ∃ t, greadsByte G A b t lockFree

/-- A row WITH a read entry IS a read. -/
theorem acqRowIsR (G : Gexec) (b : Int) (A : Geid) : acqRow G b A → glblIs G A lbIsR := by
  rintro ⟨t, l, base, ts, vs, j, hl, hrd, -⟩
  exact ⟨l, hl, lbRdIsR l _ hrd⟩

/-- … and where the pattern DOES hold it gives the row fact. -/
theorem acqRowOfPattern (G : Gexec) (b : Int) (A : Geid) :
    lockPattern G b → lockAcq G b A → acqRow G b A :=
  fun hpat hacq => (lockAcqRead G b A hpat hacq).2

/-- THE FOLD IS FREE AT AN ACQUIRE: the acquire's co-predecessor on `b` is a
release sitting immediately below it, so the fold is FREE just before it. -/
theorem acqFoldFree (G : Gexec) (log : List Wmsg) (b : Int) (n0 : Nat) (h : Option Nat)
    (ACQ : Geid) :
    rvwmoMinusConsistent G → logOf G log → lockWordByte log b →
    wlpAlt log b n0 h → acqRow G b ACQ → lockAcq G b ACQ →
    gwix G ACQ ≤ log.length →
    wlpHolderAt log b n0 (gwix G ACQ - 1) = some none := by
  intro hcons hlog hlwb halt hrow hacq hle
  have hwf := hcons.1
  have hAw := lockAcqGwrites G b ACQ hwf hacq
  have hpos := WeakRvwmoGraph.gwixPos G ACQ hAw
  obtain ⟨t, hrd⟩ := hrow
  have htlt := acqTsLt G b ACQ t hcons hacq hrd
  have hquiet : ∀ r mr, (t ≤ r ∧ r < gwix G ACQ - 1) → log[r]? = some mr →
      msgByte mr b = none := by
    intro r mr hr hmr
    cases hb : msgByte mr b with
    | none => rfl
    | some v =>
      exfalso
      obtain ⟨w', -, hm', hix', -⟩ := logOfLookup G log r mr hwf hlog hmr
      have hwb := (WeakRvwmoKillArms.gmsgByte G w' mr b v hm').1 hb
      rcases acqSrc G b ACQ t hcons hacq hrd w' v hwb with hlo | hhi <;> omega
  rw [wlpHolderQuiet log b n0 t (gwix G ACQ - 1) (by omega) hquiet]
  by_cases hn0 : t ≤ n0
  · exact wlpHolderSmall log b n0 t hn0
  obtain ⟨R, hR, hRw, hRix⟩ := acqSrcRel G b ACQ t hcons hrd (by omega)
  obtain ⟨m, hm, hgm⟩ := logOfWrite G log R hwf hlog hRw (by omega)
  rw [hRix] at hm
  have hbz := (WeakRvwmoKillArms.gmsgByte G R m b lockFree hgm).2 hR
  have hzero := hlwb (t - 1) m lockFree hm hbz rfl
  obtain ⟨hlen, hf⟩ := halt
  obtain ⟨h2, ht2⟩ := wlpHolderIsSome log b n0 t log.length h (by omega) hf
  obtain ⟨h1, ht1⟩ := wlpHolderIsSome log b n0 (t - 1) log.length h (by omega) hf
  rw [ht2]
  have hstep := wlpHolderStep log b n0 (t - 1) m (by omega) hm
  rw [ht1] at hstep
  have ht' : t - 1 + 1 = t := by omega
  rw [ht', ht2] at hstep
  dsimp only at hstep
  rw [(mwritesTrue b m).2 (by rw [hbz]; rfl)] at hstep
  simp only [↓reduceIte] at hstep
  rw [(altStepZero h1 m h2 hzero hstep.symm).1]

/-! # 4. The CS-chained arm

The segment's entry is a read inside its hart's critical section of the lock
byte `b`; the PREVIOUS segment's exit `w` is a plain write of a byte `a` that `b`
protects.  WRITER-FIRST is a derivation (the handoff); READER-FIRST is refuted by
a three-step gmo cycle through the reader's own release.  The two acquires cannot
be the SAME event: their authors differ (`ACQ.1 ≠ w.1`). -/

theorem csChained (G : Gexec) (log : List Wmsg) (b a : Int) (n0 r0 : Nat)
    (h : Option Nat) (w entry exit ACQ REL : Geid) :
    rvwmoMinusConsistent G →
    -- the log, the fold, and the byte/word bridge
    logOf G log → lockWordByte log b → wlpAlt log b n0 h →
    -- the reader's acquire is a SUCCESSFUL one (its ROW)
    acqRow G b ACQ →
    -- F3″ at the protected byte
    wprotAt log a b n0 r0 →
    -- the PREVIOUS EXIT `w`
    (∃ v, gwritesByte G w a v) → gcls G w .WCplain →
    r0 < gwix G w → gwix G w ≤ log.length →
    (∀ v, ¬ gwritesByte G w b v) →
    -- the READER's row: its acquire, its section, and the release fence
    lockAcq G b ACQ → glblIs G ACQ lbAq →
    n0 < gwix G ACQ → gwix G ACQ ≤ log.length →
    lockCs G b ACQ REL → WeakRvwmoGraph.gpo G ACQ entry → gfenceCovers G entry REL →
    -- the cross-hart edge into the entry, and the segment's exit
    gcross G w entry → WeakRvwmoGraph.gpo G ACQ exit → gmem G exit →
    ACQ.1 ≠ w.1 →
    gmoLt G w exit := by
  intro hcons hlog hlwb halt hrow hpr hwa hcl hr0 hlew hnob hacq haq hn0A hleA hcs _hpoe hfen
    hcross hpox hmx hhart
  obtain ⟨hwf, hppo, -, -⟩ := id hcons
  have hnd := hwf.1
  have hAw := lockAcqGwrites G b ACQ hwf hacq
  have hposA := WeakRvwmoGraph.gwixPos G ACQ hAw
  have hw : w ∈ gwrites G := by
    obtain ⟨v, hv⟩ := hwa
    exact gwritesByteGwrites G w a v hwf hv
  have hposw := WeakRvwmoGraph.gwixPos G w hw
  -- F3″: the writer's own acquire, at log position `q`
  obtain ⟨q, mq, hq, hlk, hs, hnz, ht, hfree, hno, -⟩ :=
    holderAcqGraph G log b a n0 r0 w hwf hlog hlwb hpr hw hr0 hlew hwa hcl
  -- F3′ locality: the fold is FREE just before the reader's acquire
  have hfreeA := acqFoldFree G log b n0 h ACQ hcons hlog hlwb halt hrow hacq hleA
  -- ppo rule 5: the reader's acquire is gmo-before its segment's exit
  have hrA := acqRowIsR G b ACQ hrow
  have hmoAx : gmoLt G ACQ exit := acqGmoAfter G ACQ exit hppo hpox hrA haq hmx
  obtain ⟨mw, hmw, hgw⟩ := logOfWrite G log w hwf hlog hw hlew
  -- the two acquires are distinct events
  by_cases heq : q = gwix G ACQ - 1
  · exfalso
    subst heq
    obtain ⟨A', -, hm', hix', hw'⟩ := logOfLookup G log (gwix G ACQ - 1) mq hwf hlog hlk
    have hA : A' = ACQ := gwixInj G A' ACQ hnd hw' hAw (by omega)
    rw [hA] at hm'
    apply hhart
    have htA := gmsgTid G ACQ mq hm'
    rw [ht, Option.some.injEq] at htA
    exact htA.symm
  by_cases hlt : q < gwix G ACQ - 1
  · -- ---- WRITER-FIRST: the handoff ----
    obtain ⟨r, R, mr, hr, hlkr, hsr, hzr, -, -, -, -, -⟩ :=
      releaseBetweenGraph G log b n0 q (gwix G ACQ - 1) mq w.1 hwf hlog hq.1 hlt hlk hs hnz ht
        hfree hfreeA
    -- the writer's release cannot sit BELOW its own protected write
    have hrp : gwix G w - 1 ≤ r := by
      by_cases hc : r < gwix G w - 1
      · exact absurd hzr (hno r mr ⟨hr.1, hc⟩ hlkr hsr)
      · omega
    -- … nor AT it: `w` does not touch the lock word
    have hrne : r ≠ gwix G w - 1 := by
      intro hre
      rw [hre, hmw, Option.some.injEq] at hlkr
      subst hlkr
      rw [gmsgByteNone G w mw b hgw hnob] at hsr
      simp at hsr
    exact gmoLtTrans G w ACQ exit (gwixLtGmo G w ACQ hwf hw hAw (by omega)) hmoAx
  · -- ---- READER-FIRST: refuted ----
    have hltA : gwix G ACQ - 1 < q := by omega
    obtain ⟨mA, hmA, hgA⟩ := logOfWrite G log ACQ hwf hlog hAw hleA
    obtain ⟨va, hva, hvane⟩ := id hacq
    have hbA := (WeakRvwmoKillArms.gmsgByte G ACQ mA b va hgA).2 hva
    have hnzA : mA.wmData ≠ wlockZero4 := fun hz => hvane (zero4Byte mA b va hz hbA)
    have htA := gmsgTid G ACQ mA hgA
    obtain ⟨r', R', mr', hr', -, -, -, -, hrelr', hixr', -, hhr'⟩ :=
      releaseBetweenGraph G log b n0 (gwix G ACQ - 1) q mA ACQ.1 hwf hlog (by omega) hltA hmA
        (by rw [hbA]; rfl) hnzA htA hfreeA hfree
    obtain ⟨-, hRel, -, -, hnoin⟩ := hcs
    have hRle : gwix G REL ≤ gwix G R' := by
      by_cases hc : gwix G R' < gwix G REL
      · exact absurd ⟨by omega, hc⟩ (hnoin R' lockFree hrelr' hhr')
      · omega
    have hmoRw : gmoLt G REL w :=
      gwixLtGmo G REL w hwf (lockRelGwrites G b REL hwf hRel) hw (by omega)
    have hmoWe := gcrossGmo G w entry hcons hcross
    have hmoeR := fenceGmoAfter G entry REL hppo hfen
    exact absurd (gmoLtTrans G w entry w hmoWe (gmoLtTrans G entry REL w hmoeR hmoRw))
      (gmoLtIrrefl G w)

/-! # 5. Non-vacuity (a): the LB cycle IS a two-segment cycle

`lbg`'s `racy` cycle in this file's segment vocabulary: two segments, two rf cross
edges, and the two `Pinned` certificates that would close it — both FALSE in
`lbg`, which is exactly why load buffering survives. -/

theorem WeakRvwmoKillArms.lbgGrf01 : WeakRvwmoAcyc.grf lbg (0, 1) (1, 0) :=
  ⟨8, 1, b1, ⟨LLoad false 8 [1] [b1], 8, [1], [b1], 0, rfl, rfl, rfl, rfl, by simp [accAddr]⟩,
    by decide⟩

theorem WeakRvwmoKillArms.lbgGrf10 : WeakRvwmoAcyc.grf lbg (1, 1) (0, 0) :=
  ⟨0, 2, b1, ⟨LLoad false 0 [2] [b1], 0, [2], [b1], 0, rfl, rfl, rfl, rfl, by simp [accAddr]⟩,
    by decide⟩

def lbSegs : List Seg :=
  [⟨1, (1, 0), (1, 1)⟩, ⟨0, (0, 0), (0, 1)⟩]

theorem lbgPinnedWouldKill :
    gmoLt lbg (1, 0) (1, 1) → gmoLt lbg (0, 0) (0, 1) → False := by
  intro h1 h0
  refine cycleKillArms lbg (0, 1) lbSegs lbGraphConsistent (by simp [lbSegs]) ?_
  simp only [lbSegs, WeakRvwmoKillArms.chain]
  exact ⟨.Pinned (Or.inl WeakRvwmoKillArms.lbgGrf01) h1,
    .Pinned (Or.inl WeakRvwmoKillArms.lbgGrf10) h0, trivial⟩

theorem lbgPinnedAbsent :
    ¬ gmoLt lbg (0, 0) (0, 1) ∧ ¬ gmoLt lbg (1, 0) (1, 1) := by
  refine ⟨fun ⟨_, _, hlt⟩ => ?_, fun ⟨_, _, hlt⟩ => ?_⟩ <;> revert hlt <;> decide

/-! # 6. Non-vacuity (b): the CS arm, instantiated

`lkw` is `WeakRvwmoLockWit.lkg` widened to a 4-byte lock word, with the two
harts' CS BODIES SWAPPED (hart 0 writes the payload byte, hart 1 reads it) — the
orientation the CS arm needs, and the WRITER-FIRST window order.

    hart 0 (the writer)                 hart 1 (the reader)
    (0,0) ACQ amoswap.aq 0:0->1 (img)   (1,0) ACQ amoswap.aq, reads (0,3)
    (0,1) STORE d := 1 (WCplain)        (1,1) LOAD  d, reads (0,1)
    (0,2) FENCE rw,rw                   (1,2) FENCE rw,rw
    (0,3) REL store 0 := 0              (1,3) REL store 0 := 0 -/

def WeakRvwmoKillArms.imgw : Image :=
  fun a => if (0 ≤ a ∧ a < 4) ∨ a = 8 then some b0 else none

def WeakRvwmoKillArms.z4 : List (BitVec 8) := [b0, b0, b0, b0]
def WeakRvwmoKillArms.o4 : List (BitVec 8) := [b1, b1, b1, b1]

def lkw : Gexec :=
  ⟨WeakRvwmoKillArms.imgw,
   [[LRmw true false 0 [0, 0, 0, 0] WeakRvwmoKillArms.z4 WeakRvwmoKillArms.o4 .WCexcl,
     LStore false 8 [b1] .WCplain,
     LFence true true true true,
     LStore true 0 WeakRvwmoKillArms.z4 .WCrel],
    [LRmw true false 0 [3, 3, 3, 3] WeakRvwmoKillArms.z4 WeakRvwmoKillArms.o4 .WCexcl,
     LLoad false 8 [2] [b1],
     LFence true true true true,
     LStore true 0 WeakRvwmoKillArms.z4 .WCrel]],
   [(0, 0), (0, 1), (0, 3), (1, 0), (1, 1), (1, 3)]⟩

local notation "ACQw" => ((0, 0) : Geid)
local notation "Wp" => ((0, 1) : Geid)
local notation "RELw" => ((0, 3) : Geid)
local notation "ACQr" => ((1, 0) : Geid)
local notation "ENT" => ((1, 1) : Geid)
local notation "RELr" => ((1, 3) : Geid)

/-- A byte of a uniform word. -/
theorem z4Lookup (a : Int) : (0 ≤ a ∧ a < 4) → WeakRvwmoKillArms.z4[a.toNat]? = some b0 := by
  intro ha
  have hk : a.toNat < 4 := by omega
  generalize a.toNat = k at hk ⊢
  rcases k with _ | _ | _ | _ | k <;> first | rfl | omega

theorem gwritesByteOf (G : Gexec) (e : Geid) (l : Lbl) (base : Int) (vs : List (BitVec 8))
    (a : Int) (v : BitVec 8) :
    gxLbl G e = some l → lbWr l = some (base, vs) → base ≤ a →
    vs[(a - base).toNat]? = some v → gwritesByte G e a v := by
  intro hl hwr hle hv
  refine ⟨l, base, vs, (a - base).toNat, hl, hwr, hv, ?_⟩
  simp only [accAddr]
  rw [Int.toNat_of_nonneg (by omega)]
  omega

theorem imgwIn (a : Int) : (0 ≤ a ∧ a < 4) → lkw.gxImg a = some b0 := by
  intro ha
  show (if (0 ≤ a ∧ a < 4) ∨ a = 8 then some b0 else none) = some b0
  rw [if_pos (Or.inl ha)]

/-! ## 6.1 Inversions and the position / index arithmetic -/

theorem lkwNodup : lkw.gxGmo.Nodup := by decide

theorem lkwGposOf (n : Nat) (e : Geid) : lkw.gxGmo[n]? = some e → gpos lkw e = n :=
  gposOfLookup lkw n e lkwNodup

theorem lkwGwixOf (n : Nat) (w : Geid) : (gwrites lkw)[n]? = some w → gwix lkw w = n + 1 :=
  gwixOfLookup lkw n w lkwNodup

theorem lkwP0 : gpos lkw ACQw = 0 := lkwGposOf _ _ (by decide)
theorem lkwP1 : gpos lkw Wp = 1 := lkwGposOf _ _ (by decide)
theorem lkwP2 : gpos lkw RELw = 2 := lkwGposOf _ _ (by decide)
theorem lkwP3 : gpos lkw ACQr = 3 := lkwGposOf _ _ (by decide)
theorem lkwP4 : gpos lkw ENT = 4 := lkwGposOf _ _ (by decide)
theorem lkwP5 : gpos lkw RELr = 5 := lkwGposOf _ _ (by decide)

theorem lkwGwrites : gwrites lkw = [ACQw, Wp, RELw, ACQr, RELr] := by decide

theorem lkwX1 : gwix lkw ACQw = 1 := lkwGwixOf 0 _ (by decide)
theorem lkwX2 : gwix lkw Wp = 2 := lkwGwixOf 1 _ (by decide)
theorem lkwX3 : gwix lkw RELw = 3 := lkwGwixOf 2 _ (by decide)
theorem lkwX4 : gwix lkw ACQr = 4 := lkwGwixOf 3 _ (by decide)
theorem lkwX5 : gwix lkw RELr = 5 := lkwGwixOf 4 _ (by decide)

/-- Lean-only: the eight labels of `lkw`. -/
theorem lkwLbl (e : Geid) (l : Lbl) : gxLbl lkw e = some l →
    (e = ACQw ∧ l = LRmw true false 0 [0, 0, 0, 0] WeakRvwmoKillArms.z4 WeakRvwmoKillArms.o4 .WCexcl) ∨
    (e = Wp ∧ l = LStore false 8 [b1] .WCplain) ∨
    (e = (0, 2) ∧ l = LFence true true true true) ∨
    (e = RELw ∧ l = LStore true 0 WeakRvwmoKillArms.z4 .WCrel) ∨
    (e = ACQr ∧ l = LRmw true false 0 [3, 3, 3, 3] WeakRvwmoKillArms.z4 WeakRvwmoKillArms.o4 .WCexcl) ∨
    (e = ENT ∧ l = LLoad false 8 [2] [b1]) ∨
    (e = (1, 2) ∧ l = LFence true true true true) ∨
    (e = RELr ∧ l = LStore true 0 WeakRvwmoKillArms.z4 .WCrel) := by
  obtain ⟨i, k⟩ := e
  intro hl
  rcases i with _ | _ | i <;> rcases k with _ | _ | _ | _ | k <;> simp [gxLbl, lkw] at hl <;>
    subst hl <;> simp

theorem lkwMemInv (e : Geid) :
    gmem lkw e →
    e = ACQw ∨ e = Wp ∨ e = RELw ∨ e = ACQr ∨ e = ENT ∨ e = RELr := by
  rintro ⟨l, hl, hm⟩
  rcases lkwLbl e l hl with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    first | decide | exact absurd hm (by decide)

theorem lkwGmoMem (e : Geid) : gmem lkw e → e ∈ lkw.gxGmo := by
  intro h
  rcases lkwMemInv e h with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem lkwMo (e1 e2 : Geid) :
    gmem lkw e1 → gmem lkw e2 → gpos lkw e1 < gpos lkw e2 → gmoLt lkw e1 e2 :=
  fun h1 h2 hlt => ⟨lkwGmoMem e1 h1, lkwGmoMem e2 h2, hlt⟩

/-- gmo IS per-hart program order, hart 0's section first. -/
theorem lkwGmoPo (e1 e2 : Geid) :
    gmem lkw e1 → gmem lkw e2 → e1.1 = e2.1 → e1.2 < e2.2 → gmoLt lkw e1 e2 := by
  intro hm1 hm2 hag hlt
  refine ⟨lkwGmoMem e1 hm1, lkwGmoMem e2 hm2, ?_⟩
  rcases lkwMemInv e1 hm1 with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases lkwMemInv e2 hm2 with rfl | rfl | rfl | rfl | rfl | rfl <;>
    revert hag hlt <;> decide

/-- The write footprints. -/
theorem lkwWr (e : Geid) (a : Int) (v : BitVec 8) :
    gwritesByte lkw e a v →
    (e = ACQw ∧ (0 ≤ a ∧ a < 4) ∧ v = b1) ∨
    (e = Wp ∧ a = 8 ∧ v = b1) ∨
    (e = RELw ∧ (0 ≤ a ∧ a < 4) ∧ v = b0) ∨
    (e = ACQr ∧ (0 ≤ a ∧ a < 4) ∧ v = b1) ∨
    (e = RELr ∧ (0 ≤ a ∧ a < 4) ∧ v = b0) := by
  rintro ⟨l, base, vs, j, hl, hwr, hv, ha⟩
  rcases lkwLbl e l hl with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    simp [lbWr] at hwr <;> obtain ⟨rfl, rfl⟩ := hwr <;>
    rcases j with _ | _ | _ | _ | j <;>
    simp [WeakRvwmoKillArms.z4, WeakRvwmoKillArms.o4] at hv <;>
    simp [accAddr] at ha <;> subst ha hv <;> simp

/-- The read footprints. -/
theorem lkwRd (e : Geid) (a : Int) (t : Nat) (v : BitVec 8) :
    greadsByte lkw e a t v →
    (e = ACQw ∧ (0 ≤ a ∧ a < 4) ∧ t = 0 ∧ v = b0) ∨
    (e = ACQr ∧ (0 ≤ a ∧ a < 4) ∧ t = 3 ∧ v = b0) ∨
    (e = ENT ∧ a = 8 ∧ t = 2 ∧ v = b1) := by
  rintro ⟨l, base, ts, vs, j, hl, hrd, ht, hv, ha⟩
  rcases lkwLbl e l hl with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    simp [lbRd] at hrd <;> obtain ⟨rfl, rfl, rfl⟩ := hrd <;>
    rcases j with _ | _ | _ | _ | j <;>
    simp [WeakRvwmoKillArms.z4] at ht hv <;>
    simp [accAddr] at ha <;> subst ha ht hv <;> simp

theorem lkwWrLock (w : Geid) (a : Int) (v : BitVec 8) :
    gwritesByte lkw w a v → (0 ≤ a ∧ a < 4) →
    (w = ACQw ∧ v = b1) ∨ (w = RELw ∧ v = b0) ∨
    (w = ACQr ∧ v = b1) ∨ (w = RELr ∧ v = b0) := by
  intro h ha
  rcases lkwWr w a v h with ⟨rfl, -, rfl⟩ | ⟨-, rfl, -⟩ | ⟨rfl, -, rfl⟩ | ⟨rfl, -, rfl⟩ |
      ⟨rfl, -, rfl⟩
  · exact Or.inl ⟨rfl, rfl⟩
  · exact absurd ha.2 (by decide)
  · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))

theorem lkwWrData (w : Geid) (v : BitVec 8) :
    gwritesByte lkw w 8 v → w = Wp ∧ v = b1 := by
  intro h
  rcases lkwWr w 8 v h with ⟨-, ha, -⟩ | ⟨rfl, -, rfl⟩ | ⟨-, ha, -⟩ | ⟨-, ha, -⟩ | ⟨-, ha, -⟩
  · exact absurd ha.2 (by decide)
  · exact ⟨rfl, rfl⟩
  · exact absurd ha.2 (by decide)
  · exact absurd ha.2 (by decide)
  · exact absurd ha.2 (by decide)

/-! ## 6.2 `lkw` is RVWMO⁻-consistent -/

theorem lkwConsistent : rvwmoMinusConsistent lkw := by
  refine ⟨⟨lkwNodup, ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro e
    constructor
    · intro he
      simp only [lkw, List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨_, rfl, rfl⟩
    · exact lkwGmoMem e
  · intro i p k l hp hk
    rcases i with _ | _ | i <;> simp [lkw] at hp <;> subst hp <;>
      rcases k with _ | _ | _ | _ | k <;> simp at hk <;> subst hk <;>
      simp [WeakRvwmoKillArms.z4, WeakRvwmoKillArms.o4]
  · -- ppo⁻ ⊆ gmo
    intro e1 e2 hppo
    obtain ⟨hm1, hm2⟩ := gppoGmem lkw e1 e2 hppo
    obtain ⟨hag, hlt⟩ := gppoPoLt lkw e1 e2 hppo
    exact lkwGmoPo e1 e2 hm1 hm2 hag hlt
  · -- load value
    intro e a t v hr
    rcases lkwRd e a t v hr with ⟨rfl, ha, rfl, rfl⟩ | ⟨rfl, ha, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
    · refine ⟨imgwIn a ha, ?_⟩
      intro w' v' _ hvis
      exfalso
      rcases hvis with ⟨_, _, hp⟩ | ⟨_, hoff, _⟩
      · rw [lkwP0] at hp
        omega
      · exact absurd hoff (Nat.not_lt_zero _)
    · refine ⟨?_, ?_⟩
      · show ∃ w, gwriteAt lkw 3 = some w ∧ gwritesByte lkw w a b0 ∧ gvisible lkw w ACQr
        refine ⟨RELw, by decide,
          gwritesByteOf lkw RELw (LStore true 0 WeakRvwmoKillArms.z4 .WCrel) 0
            WeakRvwmoKillArms.z4 a b0 rfl rfl ha.1 (by rw [Int.sub_zero]; exact z4Lookup a ha),
          Or.inl (lkwMo _ _ ⟨_, rfl, rfl⟩ ⟨_, rfl, rfl⟩ (by rw [lkwP2, lkwP3]; omega))⟩
      · intro w' v' hw' hvis
        rcases lkwWrLock w' a v' hw' ha with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;>
          first
          | decide
          | (exfalso
             rcases hvis with ⟨-, -, hp⟩ | ⟨-, hoff, -⟩
             · revert hp; decide
             · revert hoff; decide)
    · refine ⟨?_, ?_⟩
      · show ∃ w, gwriteAt lkw 2 = some w ∧ gwritesByte lkw w 8 b1 ∧ gvisible lkw w ENT
        refine ⟨Wp, by decide,
          ⟨LStore false 8 [b1] .WCplain, 8, [b1], 0, rfl, rfl, rfl, by simp [accAddr]⟩,
          Or.inl (lkwMo _ _ ⟨_, rfl, rfl⟩ ⟨_, rfl, rfl⟩ (by rw [lkwP1, lkwP4]; omega))⟩
      · intro w' v' hw' _
        obtain ⟨rfl, -⟩ := lkwWrData w' v' hw'
        decide
  · -- atomicity
    intro e a t v hr hw w' v' _ hbetw
    obtain ⟨hlo, hhi⟩ := hbetw
    rcases lkwRd e a t v hr with ⟨rfl, -, rfl, rfl⟩ | ⟨rfl, -, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
    · rw [lkwX1] at hhi
      omega
    · rw [lkwX4] at hhi
      omega
    · obtain ⟨l, hl, hlw⟩ := hw
      have h11 : gxLbl lkw ENT = some (LLoad false 8 [2] [b1]) := rfl
      rw [h11, Option.some.injEq] at hl
      subst hl
      exact absurd hlw (by decide)

/-! ## 6.3 The lock protocol and the reader's row -/

theorem lkwPattern : lockPattern lkw 0 := by
  refine ⟨fun v0 hv => ?_, fun w v hw => ?_⟩
  · rw [imgwIn 0 (by decide)] at hv
    exact (Option.some.inj hv).symm
  · rcases lkwWrLock w 0 v hw (by decide) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · left
      refine ⟨⟨_, rfl, rfl⟩, fun h => b0NeB1 h.symm, 0, ?_⟩
      exact ⟨LRmw true false 0 [0, 0, 0, 0] WeakRvwmoKillArms.z4 WeakRvwmoKillArms.o4 .WCexcl,
        0, [0, 0, 0, 0], WeakRvwmoKillArms.z4, 0, rfl, rfl, rfl, rfl, by simp [accAddr]⟩
    · right; rfl
    · left
      refine ⟨⟨_, rfl, rfl⟩, fun h => b0NeB1 h.symm, 3, ?_⟩
      exact ⟨LRmw true false 0 [3, 3, 3, 3] WeakRvwmoKillArms.z4 WeakRvwmoKillArms.o4 .WCexcl,
        0, [3, 3, 3, 3], WeakRvwmoKillArms.z4, 0, rfl, rfl, rfl, rfl, by simp [accAddr]⟩
    · right; rfl

theorem lkwAcqR : lockAcq lkw 0 ACQr :=
  ⟨b1, ⟨LRmw true false 0 [3, 3, 3, 3] WeakRvwmoKillArms.z4 WeakRvwmoKillArms.o4 .WCexcl,
    0, WeakRvwmoKillArms.o4, 0, rfl, rfl, rfl, by simp [accAddr]⟩, fun h => b0NeB1 h.symm⟩

/-- The reader's ROW fact.  On `lkw` the global pattern happens to hold too (the
lock is UNCONTENDED); §6b's contended witness is where they part. -/
theorem lkwAcqRow : acqRow lkw 0 ACQr := acqRowOfPattern lkw 0 ACQr lkwPattern lkwAcqR

theorem lkwRelR : lockRel lkw 0 RELr :=
  ⟨LStore true 0 WeakRvwmoKillArms.z4 .WCrel, 0, WeakRvwmoKillArms.z4, 0, rfl, rfl, rfl,
    by simp [accAddr]⟩

theorem lkwAqR : glblIs lkw ACQr lbAq :=
  ⟨LRmw true false 0 [3, 3, 3, 3] WeakRvwmoKillArms.z4 WeakRvwmoKillArms.o4 .WCexcl, rfl, rfl⟩

theorem lkwCsR : lockCs lkw 0 ACQr RELr := by
  apply lockCsIntro lkw 0 ACQr RELr lkwConsistent ⟨rfl, by decide, rfl, rfl⟩ lkwAcqR lkwRelR
  intro x v hx hag hlo hhi
  rcases lkwWrLock x 0 v hx (by decide) with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;>
    revert hag hlo hhi <;> decide

theorem lkwFenceR : gfenceCovers lkw ENT RELr :=
  ⟨true, true, true, true, ⟨rfl, by decide, 2, by decide, by decide, rfl⟩,
    Or.inl ⟨⟨LLoad false 8 [2] [b1], rfl, rfl⟩, rfl⟩,
    Or.inr ⟨⟨LStore true 0 WeakRvwmoKillArms.z4 .WCrel, rfl, rfl⟩, rfl⟩⟩

theorem lkwGrf : WeakRvwmoAcyc.grf lkw Wp ENT :=
  ⟨8, 2, b1, ⟨LLoad false 8 [2] [b1], 8, [2], [b1], 0, rfl, rfl, rfl, rfl, by simp [accAddr]⟩,
    by decide⟩

theorem lkwWpPlain : gcls lkw Wp .WCplain := ⟨LStore false 8 [b1] .WCplain, rfl, rfl⟩

theorem lkwWpData : ∃ v, gwritesByte lkw Wp 8 v :=
  ⟨b1, LStore false 8 [b1] .WCplain, 8, [b1], 0, rfl, rfl, rfl, by simp [accAddr]⟩

theorem lkwWpNoLock : ∀ v, ¬ gwritesByte lkw Wp 0 v := by
  intro v hv
  rcases lkwWrLock Wp 0 v hv (by decide) with ⟨hc, -⟩ | ⟨hc, -⟩ | ⟨hc, -⟩ | ⟨hc, -⟩ <;>
    exact absurd hc (by decide)

/-! ## 6.4 The log, and the three log-vocabulary exports -/

def lkwLog : List Wmsg :=
  [⟨0, WeakRvwmoKillArms.o4, some 0, .WCexcl⟩,
   ⟨8, [b1], some 0, .WCplain⟩,
   ⟨0, WeakRvwmoKillArms.z4, some 0, .WCrel⟩,
   ⟨0, WeakRvwmoKillArms.o4, some 1, .WCexcl⟩,
   ⟨0, WeakRvwmoKillArms.z4, some 1, .WCrel⟩]

theorem msgByteO40 (t : Option Nat) (k : WmClass) :
    msgByte ⟨0, WeakRvwmoKillArms.o4, t, k⟩ 0 = some b1 := rfl

theorem msgByteZ40 (t : Option Nat) (k : WmClass) :
    msgByte ⟨0, WeakRvwmoKillArms.z4, t, k⟩ 0 = some b0 := rfl

theorem msgByteO48 (t : Option Nat) (k : WmClass) :
    msgByte ⟨0, WeakRvwmoKillArms.o4, t, k⟩ 8 = none := rfl

theorem msgByteZ48 (t : Option Nat) (k : WmClass) :
    msgByte ⟨0, WeakRvwmoKillArms.z4, t, k⟩ 8 = none := rfl

theorem msgByteD0 (t : Option Nat) (k : WmClass) :
    msgByte ⟨8, [b1], t, k⟩ 0 = none := rfl

theorem lkwLogOf : logOf lkw lkwLog := by
  apply logOfIntro
  intro p
  rw [lkwGwrites]
  rcases p with _ | _ | _ | _ | _ | p
  all_goals rfl

theorem lkwLog0 : lkwLog[0]? = some ⟨0, WeakRvwmoKillArms.o4, some 0, .WCexcl⟩ := rfl
theorem lkwLog1 : lkwLog[1]? = some ⟨8, [b1], some 0, .WCplain⟩ := rfl
theorem lkwLog2 : lkwLog[2]? = some ⟨0, WeakRvwmoKillArms.z4, some 0, .WCrel⟩ := rfl
theorem lkwLog3 : lkwLog[3]? = some ⟨0, WeakRvwmoKillArms.o4, some 1, .WCexcl⟩ := rfl
theorem lkwLog4 : lkwLog[4]? = some ⟨0, WeakRvwmoKillArms.z4, some 1, .WCrel⟩ := rfl
theorem lkwLogHi (p : Nat) : lkwLog[p + 5]? = none := by simp [lkwLog]

theorem lkwLwb : lockWordByte lkwLog 0 := by
  intro p m v hp hb hv
  subst hv
  rcases p with _ | _ | _ | _ | _ | p <;> simp [lkwLog] at hp <;> subst hp <;>
    first | rfl | (exfalso; revert hb; decide)

theorem lkwAlt : wlpAlt lkwLog 0 0 none := ⟨by decide, by decide⟩

theorem lkwWprot : wprotAt lkwLog 8 0 0 0 := by
  refine ⟨Nat.le_refl _, ?_⟩
  intro p m hp _ hs hk
  rcases p with _ | _ | _ | _ | _ | p <;> simp [lkwLog] at hp <;> subst hp <;>
    revert hs hk <;> decide

/-! ## 6.5 THE INSTANTIATION

Every hypothesis of `csChained` is discharged on `lkw`/`lkwLog`, and its
conclusion is DERIVED (the WRITER-FIRST window order: hart 0's section closes,
`RELw` at write index 3, before hart 1's opens, `ACQr` at index 4). -/

theorem lkwLogLen : lkwLog.length = 5 := rfl

theorem lkwCsChained : gmoLt lkw Wp RELr :=
  csChained lkw lkwLog 0 8 0 0 none Wp ENT RELr ACQr RELr lkwConsistent lkwLogOf lkwLwb lkwAlt
    lkwAcqRow lkwWprot lkwWpData lkwWpPlain (by rw [lkwX2]; omega)
    (by rw [lkwX2, lkwLogLen]; omega) lkwWpNoLock lkwAcqR lkwAqR (by rw [lkwX4]; omega)
    (by rw [lkwX4, lkwLogLen]; omega) lkwCsR ⟨rfl, by decide, rfl, rfl⟩ lkwFenceR
    (Or.inl lkwGrf) ⟨rfl, by decide, rfl, rfl⟩ ⟨_, rfl, rfl⟩ (by decide)

/-- … and the certificate the composition consumes. -/
theorem lkwCert : Cert lkw Wp ⟨1, ENT, RELr⟩ := .CSchained lkwCsChained

/-! # 6b. Non-vacuity (c): THE CS ARM AT A *CONTENDED* LOCK

`lkw` is UNCONTENDED, so `lockPattern` happens to hold on it.  `lkw2` is `lkw`
with ONE extra event: hart 1 SPINS ONCE — a failed `amoswap.w.aq` that READS the
1 hart 0's acquire wrote and WRITES 1 again — before its successful acquire.
`lkw2NoPattern`: the OLD hypothesis is FALSE here; `lkw2CsChained`: every
hypothesis of `csChained` is discharged and its conclusion DERIVED.  Over a HELD
word an exclusive nonzero message leaves the holder unchanged (`altStepFail`), so
the fold walks past the failed swap.

    hart 0 (the writer)                 hart 1 (the reader)
    (0,0) ACQw amoswap.aq 0:0->1 (img)  (1,0) SWP2 amoswap.aq 0:1->1, reads (0,0)
    (0,1) Wp   STORE d := 1 (WCplain)   (1,1) ACQ2 amoswap.aq 0:0->1, reads (0,3)
    (0,2) FENCE rw,rw                   (1,2) ENT2 LOAD d, reads (0,1)
    (0,3) RELw store 0 := 0             (1,3) FENCE rw,rw
                                        (1,4) REL2 store 0 := 0

gmo — ACQw, SWP2, Wp, RELw, ACQ2, ENT2, REL2.  Write indices: ACQw 1, SWP2 2,
Wp 3, RELw 4, ACQ2 5, REL2 6. -/

def lkw2 : Gexec :=
  ⟨WeakRvwmoKillArms.imgw,
   [[LRmw true false 0 [0, 0, 0, 0] WeakRvwmoKillArms.z4 WeakRvwmoKillArms.o4 .WCexcl,
     LStore false 8 [b1] .WCplain,
     LFence true true true true,
     LStore true 0 WeakRvwmoKillArms.z4 .WCrel],
    [LRmw true false 0 [1, 1, 1, 1] WeakRvwmoKillArms.o4 WeakRvwmoKillArms.o4 .WCexcl,
     LRmw true false 0 [4, 4, 4, 4] WeakRvwmoKillArms.z4 WeakRvwmoKillArms.o4 .WCexcl,
     LLoad false 8 [3] [b1],
     LFence true true true true,
     LStore true 0 WeakRvwmoKillArms.z4 .WCrel]],
   [(0, 0), (1, 0), (0, 1), (0, 3), (1, 1), (1, 2), (1, 4)]⟩

local notation "SWP2" => ((1, 0) : Geid)
local notation "ACQ2" => ((1, 1) : Geid)
local notation "ENT2" => ((1, 2) : Geid)
local notation "REL2" => ((1, 4) : Geid)

theorem o4Lookup (a : Int) : (0 ≤ a ∧ a < 4) → WeakRvwmoKillArms.o4[a.toNat]? = some b1 := by
  intro ha
  have hk : a.toNat < 4 := by omega
  generalize a.toNat = k at hk ⊢
  rcases k with _ | _ | _ | _ | k <;> first | rfl | omega

theorem imgwIn2 (a : Int) : (0 ≤ a ∧ a < 4) → lkw2.gxImg a = some b0 := by
  intro ha
  show (if (0 ≤ a ∧ a < 4) ∨ a = 8 then some b0 else none) = some b0
  rw [if_pos (Or.inl ha)]

/-! ## 6b.1 Inversions and the position / index arithmetic -/

theorem lkw2Nodup : lkw2.gxGmo.Nodup := by decide

theorem lkw2GposOf (n : Nat) (e : Geid) : lkw2.gxGmo[n]? = some e → gpos lkw2 e = n :=
  gposOfLookup lkw2 n e lkw2Nodup

theorem lkw2GwixOf (n : Nat) (w : Geid) : (gwrites lkw2)[n]? = some w → gwix lkw2 w = n + 1 :=
  gwixOfLookup lkw2 n w lkw2Nodup

theorem lkw2P0 : gpos lkw2 ACQw = 0 := lkw2GposOf _ _ (by decide)
theorem lkw2P1 : gpos lkw2 SWP2 = 1 := lkw2GposOf _ _ (by decide)
theorem lkw2P2 : gpos lkw2 Wp = 2 := lkw2GposOf _ _ (by decide)
theorem lkw2P3 : gpos lkw2 RELw = 3 := lkw2GposOf _ _ (by decide)
theorem lkw2P4 : gpos lkw2 ACQ2 = 4 := lkw2GposOf _ _ (by decide)
theorem lkw2P5 : gpos lkw2 ENT2 = 5 := lkw2GposOf _ _ (by decide)
theorem lkw2P6 : gpos lkw2 REL2 = 6 := lkw2GposOf _ _ (by decide)

theorem lkw2Gwrites : gwrites lkw2 = [ACQw, SWP2, Wp, RELw, ACQ2, REL2] := by decide

theorem lkw2X1 : gwix lkw2 ACQw = 1 := lkw2GwixOf 0 _ (by decide)
theorem lkw2X2 : gwix lkw2 SWP2 = 2 := lkw2GwixOf 1 _ (by decide)
theorem lkw2X3 : gwix lkw2 Wp = 3 := lkw2GwixOf 2 _ (by decide)
theorem lkw2X4 : gwix lkw2 RELw = 4 := lkw2GwixOf 3 _ (by decide)
theorem lkw2X5 : gwix lkw2 ACQ2 = 5 := lkw2GwixOf 4 _ (by decide)
theorem lkw2X6 : gwix lkw2 REL2 = 6 := lkw2GwixOf 5 _ (by decide)

/-- Lean-only: the nine labels of `lkw2`. -/
theorem lkw2Lbl (e : Geid) (l : Lbl) : gxLbl lkw2 e = some l →
    (e = ACQw ∧ l = LRmw true false 0 [0, 0, 0, 0] WeakRvwmoKillArms.z4 WeakRvwmoKillArms.o4 .WCexcl) ∨
    (e = Wp ∧ l = LStore false 8 [b1] .WCplain) ∨
    (e = (0, 2) ∧ l = LFence true true true true) ∨
    (e = RELw ∧ l = LStore true 0 WeakRvwmoKillArms.z4 .WCrel) ∨
    (e = SWP2 ∧ l = LRmw true false 0 [1, 1, 1, 1] WeakRvwmoKillArms.o4 WeakRvwmoKillArms.o4 .WCexcl) ∨
    (e = ACQ2 ∧ l = LRmw true false 0 [4, 4, 4, 4] WeakRvwmoKillArms.z4 WeakRvwmoKillArms.o4 .WCexcl) ∨
    (e = ENT2 ∧ l = LLoad false 8 [3] [b1]) ∨
    (e = (1, 3) ∧ l = LFence true true true true) ∨
    (e = REL2 ∧ l = LStore true 0 WeakRvwmoKillArms.z4 .WCrel) := by
  obtain ⟨i, k⟩ := e
  intro hl
  rcases i with _ | _ | i <;> rcases k with _ | _ | _ | _ | _ | k <;> simp [gxLbl, lkw2] at hl <;>
    subst hl <;> simp

theorem lkw2MemInv (e : Geid) :
    gmem lkw2 e →
    e = ACQw ∨ e = Wp ∨ e = RELw ∨ e = SWP2 ∨ e = ACQ2 ∨ e = ENT2 ∨ e = REL2 := by
  rintro ⟨l, hl, hm⟩
  rcases lkw2Lbl e l hl with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    first | decide | exact absurd hm (by decide)

theorem lkw2GmoMem (e : Geid) : gmem lkw2 e → e ∈ lkw2.gxGmo := by
  intro h
  rcases lkw2MemInv e h with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem lkw2Mo (e1 e2 : Geid) :
    gmem lkw2 e1 → gmem lkw2 e2 → gpos lkw2 e1 < gpos lkw2 e2 → gmoLt lkw2 e1 e2 :=
  fun h1 h2 hlt => ⟨lkw2GmoMem e1 h1, lkw2GmoMem e2 h2, hlt⟩

/-- gmo IS per-hart program order here too. -/
theorem lkw2GmoPo (e1 e2 : Geid) :
    gmem lkw2 e1 → gmem lkw2 e2 → e1.1 = e2.1 → e1.2 < e2.2 → gmoLt lkw2 e1 e2 := by
  intro hm1 hm2 hag hlt
  refine ⟨lkw2GmoMem e1 hm1, lkw2GmoMem e2 hm2, ?_⟩
  rcases lkw2MemInv e1 hm1 with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases lkw2MemInv e2 hm2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    revert hag hlt <;> decide

/-- The write footprints. -/
theorem lkw2Wr (e : Geid) (a : Int) (v : BitVec 8) :
    gwritesByte lkw2 e a v →
    (e = ACQw ∧ (0 ≤ a ∧ a < 4) ∧ v = b1) ∨
    (e = Wp ∧ a = 8 ∧ v = b1) ∨
    (e = RELw ∧ (0 ≤ a ∧ a < 4) ∧ v = b0) ∨
    (e = SWP2 ∧ (0 ≤ a ∧ a < 4) ∧ v = b1) ∨
    (e = ACQ2 ∧ (0 ≤ a ∧ a < 4) ∧ v = b1) ∨
    (e = REL2 ∧ (0 ≤ a ∧ a < 4) ∧ v = b0) := by
  rintro ⟨l, base, vs, j, hl, hwr, hv, ha⟩
  rcases lkw2Lbl e l hl with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    simp [lbWr] at hwr <;> obtain ⟨rfl, rfl⟩ := hwr <;>
    rcases j with _ | _ | _ | _ | j <;>
    simp [WeakRvwmoKillArms.z4, WeakRvwmoKillArms.o4] at hv <;>
    simp [accAddr] at ha <;> subst ha hv <;> simp

/-- The read footprints.  THE HEART OF THE CONTENTION: `SWP2`'s read entry at
byte 0 names `b1`, NOT the free byte. -/
theorem lkw2Rd (e : Geid) (a : Int) (t : Nat) (v : BitVec 8) :
    greadsByte lkw2 e a t v →
    (e = ACQw ∧ (0 ≤ a ∧ a < 4) ∧ t = 0 ∧ v = b0) ∨
    (e = SWP2 ∧ (0 ≤ a ∧ a < 4) ∧ t = 1 ∧ v = b1) ∨
    (e = ACQ2 ∧ (0 ≤ a ∧ a < 4) ∧ t = 4 ∧ v = b0) ∨
    (e = ENT2 ∧ a = 8 ∧ t = 3 ∧ v = b1) := by
  rintro ⟨l, base, ts, vs, j, hl, hrd, ht, hv, ha⟩
  rcases lkw2Lbl e l hl with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    simp [lbRd] at hrd <;> obtain ⟨rfl, rfl, rfl⟩ := hrd <;>
    rcases j with _ | _ | _ | _ | j <;>
    simp [WeakRvwmoKillArms.z4, WeakRvwmoKillArms.o4] at ht hv <;>
    simp [accAddr] at ha <;> subst ha ht hv <;> simp

theorem lkw2WrLock (w : Geid) (a : Int) (v : BitVec 8) :
    gwritesByte lkw2 w a v → (0 ≤ a ∧ a < 4) →
    (w = ACQw ∧ v = b1) ∨ (w = SWP2 ∧ v = b1) ∨
    (w = RELw ∧ v = b0) ∨ (w = ACQ2 ∧ v = b1) ∨
    (w = REL2 ∧ v = b0) := by
  intro h ha
  rcases lkw2Wr w a v h with ⟨rfl, -, rfl⟩ | ⟨-, rfl, -⟩ | ⟨rfl, -, rfl⟩ | ⟨rfl, -, rfl⟩ |
      ⟨rfl, -, rfl⟩ | ⟨rfl, -, rfl⟩
  · exact Or.inl ⟨rfl, rfl⟩
  · exact absurd ha.2 (by decide)
  · exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))
  · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)))

theorem lkw2WrData (w : Geid) (v : BitVec 8) :
    gwritesByte lkw2 w 8 v → w = Wp ∧ v = b1 := by
  intro h
  rcases lkw2Wr w 8 v h with ⟨-, ha, -⟩ | ⟨rfl, -, rfl⟩ | ⟨-, ha, -⟩ | ⟨-, ha, -⟩ | ⟨-, ha, -⟩ |
      ⟨-, ha, -⟩
  · exact absurd ha.2 (by decide)
  · exact ⟨rfl, rfl⟩
  all_goals exact absurd ha.2 (by decide)

/-! ## 6b.2 `lkw2` is RVWMO⁻-consistent — a contended lock is a LEGITIMATE
execution -/

theorem lkw2Consistent : rvwmoMinusConsistent lkw2 := by
  refine ⟨⟨lkw2Nodup, ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro e
    constructor
    · intro he
      simp only [lkw2, List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨_, rfl, rfl⟩
    · exact lkw2GmoMem e
  · intro i p k l hp hk
    rcases i with _ | _ | i <;> simp [lkw2] at hp <;> subst hp <;>
      rcases k with _ | _ | _ | _ | _ | k <;> simp at hk <;> subst hk <;>
      simp [WeakRvwmoKillArms.z4, WeakRvwmoKillArms.o4]
  · -- ppo⁻ ⊆ gmo
    intro e1 e2 hppo
    obtain ⟨hm1, hm2⟩ := gppoGmem lkw2 e1 e2 hppo
    obtain ⟨hag, hlt⟩ := gppoPoLt lkw2 e1 e2 hppo
    exact lkw2GmoPo e1 e2 hm1 hm2 hag hlt
  · -- load value
    intro e a t v hr
    rcases lkw2Rd e a t v hr with ⟨rfl, ha, rfl, rfl⟩ | ⟨rfl, ha, rfl, rfl⟩ |
        ⟨rfl, ha, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
    · -- ACQw reads the image
      refine ⟨imgwIn2 a ha, ?_⟩
      intro w' v' _ hvis
      exfalso
      rcases hvis with ⟨_, _, hp⟩ | ⟨_, hoff, _⟩
      · rw [lkw2P0] at hp
        omega
      · exact absurd hoff (Nat.not_lt_zero _)
    · -- SWP2 — the FAILED swap — reads hart 0's acquire
      refine ⟨?_, ?_⟩
      · show ∃ w, gwriteAt lkw2 1 = some w ∧ gwritesByte lkw2 w a b1 ∧ gvisible lkw2 w SWP2
        refine ⟨ACQw, by decide,
          gwritesByteOf lkw2 ACQw
            (LRmw true false 0 [0, 0, 0, 0] WeakRvwmoKillArms.z4 WeakRvwmoKillArms.o4 .WCexcl) 0
            WeakRvwmoKillArms.o4 a b1 rfl rfl ha.1 (by rw [Int.sub_zero]; exact o4Lookup a ha),
          Or.inl (lkw2Mo _ _ ⟨_, rfl, rfl⟩ ⟨_, rfl, rfl⟩ (by rw [lkw2P0, lkw2P1]; omega))⟩
      · intro w' v' hw' hvis
        rcases lkw2WrLock w' a v' hw' ha with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ |
            ⟨rfl, -⟩ <;>
          first
          | decide
          | (exfalso
             rcases hvis with ⟨-, -, hp⟩ | ⟨-, hoff, -⟩
             · revert hp; decide
             · revert hoff; decide)
    · -- ACQ2 — the SUCCESSFUL acquire — reads hart 0's release
      refine ⟨?_, ?_⟩
      · show ∃ w, gwriteAt lkw2 4 = some w ∧ gwritesByte lkw2 w a b0 ∧ gvisible lkw2 w ACQ2
        refine ⟨RELw, by decide,
          gwritesByteOf lkw2 RELw (LStore true 0 WeakRvwmoKillArms.z4 .WCrel) 0
            WeakRvwmoKillArms.z4 a b0 rfl rfl ha.1 (by rw [Int.sub_zero]; exact z4Lookup a ha),
          Or.inl (lkw2Mo _ _ ⟨_, rfl, rfl⟩ ⟨_, rfl, rfl⟩ (by rw [lkw2P3, lkw2P4]; omega))⟩
      · intro w' v' hw' hvis
        rcases lkw2WrLock w' a v' hw' ha with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ |
            ⟨rfl, -⟩ <;>
          first
          | decide
          | (exfalso
             rcases hvis with ⟨-, -, hp⟩ | ⟨-, hoff, -⟩
             · revert hp; decide
             · revert hoff; decide)
    · -- ENT2 reads the payload
      refine ⟨?_, ?_⟩
      · show ∃ w, gwriteAt lkw2 3 = some w ∧ gwritesByte lkw2 w 8 b1 ∧ gvisible lkw2 w ENT2
        refine ⟨Wp, by decide,
          ⟨LStore false 8 [b1] .WCplain, 8, [b1], 0, rfl, rfl, rfl, by simp [accAddr]⟩,
          Or.inl (lkw2Mo _ _ ⟨_, rfl, rfl⟩ ⟨_, rfl, rfl⟩ (by rw [lkw2P2, lkw2P5]; omega))⟩
      · intro w' v' hw' _
        obtain ⟨rfl, -⟩ := lkw2WrData w' v' hw'
        decide
  · -- atomicity — each RMW's source is its immediate co-predecessor
    intro e a t v hr hw w' v' _ hbetw
    obtain ⟨hlo, hhi⟩ := hbetw
    rcases lkw2Rd e a t v hr with ⟨rfl, -, rfl, rfl⟩ | ⟨rfl, -, rfl, rfl⟩ |
        ⟨rfl, -, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
    · rw [lkw2X1] at hhi
      omega
    · rw [lkw2X2] at hhi
      omega
    · rw [lkw2X5] at hhi
      omega
    · obtain ⟨l, hl, hlw⟩ := hw
      have h12 : gxLbl lkw2 ENT2 = some (LLoad false 8 [3] [b1]) := rfl
      rw [h12, Option.some.injEq] at hl
      subst hl
      exact absurd hlw (by decide)

/-! ## 6b.3 THE OLD HYPOTHESIS IS FALSE HERE — F4(a), at this graph -/

theorem lkw2SwpWr : gwritesByte lkw2 SWP2 0 b1 :=
  ⟨LRmw true false 0 [1, 1, 1, 1] WeakRvwmoKillArms.o4 WeakRvwmoKillArms.o4 .WCexcl,
    0, WeakRvwmoKillArms.o4, 0, rfl, rfl, rfl, by simp [accAddr]⟩

theorem lkw2NoPattern : ¬ lockPattern lkw2 0 := by
  rintro ⟨-, hpat⟩
  rcases hpat SWP2 b1 lkw2SwpWr with ⟨-, -, t, hrd⟩ | hz
  · rcases lkw2Rd SWP2 0 t lockFree hrd with ⟨hc, -⟩ | ⟨-, -, -, hv⟩ | ⟨hc, -⟩ | ⟨hc, -⟩
    · exact absurd hc (by decide)
    · exact b0NeB1 hv
    · exact absurd hc (by decide)
    · exact absurd hc (by decide)
  · exact b0NeB1 hz.symm

/-! ## 6b.4 The reader's row, its section, and the payload -/

theorem lkw2Acq2 : lockAcq lkw2 0 ACQ2 :=
  ⟨b1, ⟨LRmw true false 0 [4, 4, 4, 4] WeakRvwmoKillArms.z4 WeakRvwmoKillArms.o4 .WCexcl,
    0, WeakRvwmoKillArms.o4, 0, rfl, rfl, rfl, by simp [accAddr]⟩, fun h => b0NeB1 h.symm⟩

/-- THE NEW HYPOTHESIS, at the same site the old one failed: the SUCCESSFUL
acquire's own read entry at byte 0 names the free byte. -/
theorem lkw2AcqRow : acqRow lkw2 0 ACQ2 :=
  ⟨4, LRmw true false 0 [4, 4, 4, 4] WeakRvwmoKillArms.z4 WeakRvwmoKillArms.o4 .WCexcl,
    0, [4, 4, 4, 4], WeakRvwmoKillArms.z4, 0, rfl, rfl, rfl, rfl, by simp [accAddr]⟩

theorem lkw2Rel2 : lockRel lkw2 0 REL2 :=
  ⟨LStore true 0 WeakRvwmoKillArms.z4 .WCrel, 0, WeakRvwmoKillArms.z4, 0, rfl, rfl, rfl,
    by simp [accAddr]⟩

theorem lkw2Aq2 : glblIs lkw2 ACQ2 lbAq :=
  ⟨LRmw true false 0 [4, 4, 4, 4] WeakRvwmoKillArms.z4 WeakRvwmoKillArms.o4 .WCexcl, rfl, rfl⟩

theorem lkw2CsR : lockCs lkw2 0 ACQ2 REL2 := by
  apply lockCsIntro lkw2 0 ACQ2 REL2 lkw2Consistent ⟨rfl, by decide, rfl, rfl⟩ lkw2Acq2 lkw2Rel2
  intro x v hx hag hlo hhi
  rcases lkw2WrLock x 0 v hx (by decide) with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ |
      ⟨rfl, -⟩ <;>
    revert hag hlo hhi <;> decide

theorem lkw2FenceR : gfenceCovers lkw2 ENT2 REL2 :=
  ⟨true, true, true, true, ⟨rfl, by decide, 3, by decide, by decide, rfl⟩,
    Or.inl ⟨⟨LLoad false 8 [3] [b1], rfl, rfl⟩, rfl⟩,
    Or.inr ⟨⟨LStore true 0 WeakRvwmoKillArms.z4 .WCrel, rfl, rfl⟩, rfl⟩⟩

theorem lkw2Grf : WeakRvwmoAcyc.grf lkw2 Wp ENT2 :=
  ⟨8, 3, b1, ⟨LLoad false 8 [3] [b1], 8, [3], [b1], 0, rfl, rfl, rfl, rfl, by simp [accAddr]⟩,
    by decide⟩

theorem lkw2WpPlain : gcls lkw2 Wp .WCplain := ⟨LStore false 8 [b1] .WCplain, rfl, rfl⟩

theorem lkw2WpData : ∃ v, gwritesByte lkw2 Wp 8 v :=
  ⟨b1, LStore false 8 [b1] .WCplain, 8, [b1], 0, rfl, rfl, rfl, by simp [accAddr]⟩

theorem lkw2WpNoLock : ∀ v, ¬ gwritesByte lkw2 Wp 0 v := by
  intro v hv
  rcases lkw2WrLock Wp 0 v hv (by decide) with ⟨hc, -⟩ | ⟨hc, -⟩ | ⟨hc, -⟩ | ⟨hc, -⟩ |
      ⟨hc, -⟩ <;>
    exact absurd hc (by decide)

/-! ## 6b.5 The log, and the three exported predicates on it

The log carries the failed swap as an ORDINARY `WCexcl` nonzero message at
position 1; `wlpAlt` folds straight past it (`altStepFail`), and `wprotAt` never
looks at it (it is not `WCplain`). -/

def lkw2Log : List Wmsg :=
  [⟨0, WeakRvwmoKillArms.o4, some 0, .WCexcl⟩,   -- ACQw
   ⟨0, WeakRvwmoKillArms.o4, some 1, .WCexcl⟩,   -- SWP2, the FAILED swap
   ⟨8, [b1], some 0, .WCplain⟩,                   -- Wp
   ⟨0, WeakRvwmoKillArms.z4, some 0, .WCrel⟩,    -- RELw
   ⟨0, WeakRvwmoKillArms.o4, some 1, .WCexcl⟩,   -- ACQ2
   ⟨0, WeakRvwmoKillArms.z4, some 1, .WCrel⟩]    -- REL2

theorem lkw2LogOf : logOf lkw2 lkw2Log := by
  apply logOfIntro
  intro p
  rw [lkw2Gwrites]
  rcases p with _ | _ | _ | _ | _ | _ | p
  all_goals rfl

theorem lkw2Log0 : lkw2Log[0]? = some ⟨0, WeakRvwmoKillArms.o4, some 0, .WCexcl⟩ := rfl
theorem lkw2Log1 : lkw2Log[1]? = some ⟨0, WeakRvwmoKillArms.o4, some 1, .WCexcl⟩ := rfl
theorem lkw2Log2 : lkw2Log[2]? = some ⟨8, [b1], some 0, .WCplain⟩ := rfl
theorem lkw2Log3 : lkw2Log[3]? = some ⟨0, WeakRvwmoKillArms.z4, some 0, .WCrel⟩ := rfl
theorem lkw2Log4 : lkw2Log[4]? = some ⟨0, WeakRvwmoKillArms.o4, some 1, .WCexcl⟩ := rfl
theorem lkw2Log5 : lkw2Log[5]? = some ⟨0, WeakRvwmoKillArms.z4, some 1, .WCrel⟩ := rfl
theorem lkw2LogHi (p : Nat) : lkw2Log[p + 6]? = none := by simp [lkw2Log]

theorem lkw2LogLen : lkw2Log.length = 6 := rfl

theorem lkw2Lwb : lockWordByte lkw2Log 0 := by
  intro p m v hp hb hv
  subst hv
  rcases p with _ | _ | _ | _ | _ | _ | p <;> simp [lkw2Log] at hp <;> subst hp <;>
    first | rfl | (exfalso; revert hb; decide)

/-- THE FOLD TOLERATES THE FAILED SWAP: positions 0…5 send the holder
`none → some 0 → some 0 (the failed swap) → some 0 → none → some 1 → none`. -/
theorem lkw2Alt : wlpAlt lkw2Log 0 0 none := ⟨by decide, by decide⟩

theorem lkw2Wprot : wprotAt lkw2Log 8 0 0 0 := by
  refine ⟨Nat.le_refl _, ?_⟩
  intro p m hp _ hs hk
  rcases p with _ | _ | _ | _ | _ | _ | p <;> simp [lkw2Log] at hp <;> subst hp <;>
    revert hs hk <;> decide

/-! ## 6b.6 THE INSTANTIATION AT THE CONTENDED LOCK

Every hypothesis of `csChained` discharged, its conclusion derived — on a graph
where `lockPattern` is refuted (`lkw2NoPattern`); hart 1's FAILED swap sits at log
position 1, inside hart 0's section, disturbing nothing. -/

theorem lkw2CsChained : gmoLt lkw2 Wp REL2 :=
  csChained lkw2 lkw2Log 0 8 0 0 none Wp ENT2 REL2 ACQ2 REL2 lkw2Consistent lkw2LogOf lkw2Lwb
    lkw2Alt lkw2AcqRow lkw2Wprot lkw2WpData lkw2WpPlain (by rw [lkw2X3]; omega)
    (by rw [lkw2X3, lkw2LogLen]; omega) lkw2WpNoLock lkw2Acq2 lkw2Aq2 (by rw [lkw2X5]; omega)
    (by rw [lkw2X5, lkw2LogLen]; omega) lkw2CsR ⟨rfl, by decide, rfl, rfl⟩ lkw2FenceR
    (Or.inl lkw2Grf) ⟨rfl, by decide, rfl, rfl⟩ ⟨_, rfl, rfl⟩ (by decide)

/-- … and the certificate the composition consumes. -/
theorem lkw2Cert : Cert lkw2 Wp ⟨1, ENT2, REL2⟩ := .CSchained lkw2CsChained

end Weak
