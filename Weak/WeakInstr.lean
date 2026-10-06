/-
Weak: **the weak instruction-leaf layer** (M3a): everything between
`WeakExec.wpWexecStep` (the raw lifting rule, stated over the ORACLE and
`wexec`) and a whole-instruction leaf rule stated over the memory resources of
`WeakVProp`/`WeakFence`.

Rocq: `iris/WeakInstr.v` @ xxvzwolszwmp (1cc222280).

The Rocq header, in substance (Rocq vocabulary).

THE THREE THINGS IN HERE.
(1) THE FLAT BRIDGE FOR RESOURCES (§1–§2).  `WeakBridge` transfers the
    exec-level library on the PINNED fragment, but it transfers a RUN; a leaf
    still has to say what the flat memory HOLDS at the bytes it owns.  That is
    `wlatFlatLookup`: an element of the latest-write map at byte `a` IS what
    `WeakLang.wflat` holds there -- for ANY timestamp, hence for an owned `↦w`
    and, as the special case that matters, for an era-image byte (`wptImg`,
    timestamp 0: all kernel text).  With it, the whole fetch/decode side of an
    instruction transfers as a statement about the flat projection, and
    `wkernelText` (§2) is the objective, freely shareable resource that
    carries it.
(2) THE PIN CERTIFICATE (§3).  `WeakBridge.wstepOk` is a structural peel of
    the WHOLE step (`riscvStep tick`).  Its per-access content is tiny (the
    text is unwritten, the data footprint is pinned or the access kind forces
    the latest read) but obtaining it requires walking the model -- a
    per-instruction obligation of the same nature as a decode fact.  It is
    therefore packaged AS one: `wstepCert cid pc P Q` is the pure,
    per-(pc, instruction) statement "given the text at `pc` is unwritten and
    `P` holds of the hart's weak state, the step's peel goes through, and every
    successor satisfies `Q`"; a leaf takes it as a premise exactly the way the
    SC leaves take `pmp_allows_all` and an `instr` fact.
(3) THE RULE (§4).  `wpWinstr` is the weak analogue of
    `InstrBytes.wp_exec_step_decode_execute_inv`'s altitude: the caller
    supplies the SAME `exec` facts it supplies today -- but over
    `WeakBridge.wflatSt σ` -- plus ONE certificate, and receives back a
    successor `σ'` described by `wstepPost`: registers/devices/flat-memory are
    the SC ones, the image is unchanged, the log only grew, and the hart's
    views only grew (what `WeakVProp.vwpHold_mono` consumes, so every resource
    a leaf did not touch crosses the step for free).

WHAT DID NOT HAVE TO MOVE: the config tower (register points-to, pure facts and
ghost state) is an `IProp` the weak side carries unchanged, and
`WeakGhost.wmstateInterp` contains `regInterp cpu σ.wmRegs` with
`σ.wmRegs = (wflatSt σ).regs`; only the lemmas consuming the SC `mstate_interp`
AS A BUNDLE do not carry over, and each is a mechanical restatement with the
memory hypothesis taken as the pure fact §1 produces.

**O2 (owner decision; `Weak/WeakBridge.lean` header).**  Under O2 a fetch is the
i-cache read, forced not by its kind but by THE FETCH PIN `fetchPinned σ a`
(`latestTs ≤ wmItv`).  So the certificate's text hypothesis and `wpWinstr`'s
text obligation carry BOTH pins per text byte (`pinnedRead ∧ fetchPinned`), see
deviation 4; kernel text (`latestTs = 0`) gives both for free
(`wkernelTextTextPinned`).

**Deviations from Rocq.**

1. NAMES: the tree's camelCase (map below); file-qualified per the
   duplicated-name rule: `WeakInstr.barrierPostRelp`,
   `WeakInstr.loadPostBytesRelp`, `WeakInstr.loadPostRunRelp`,
   `WeakInstr.wreadPostRelp`, `WeakInstr.wmClassOfRelp`.  Vocabulary as
   `Weak/WeakVProp.lean` deviation 6 / `Weak/WeakFence.lean` deviation 1
   (`⊑` ↦ `≤`, `S (length l)` ↦ `l.length + 1`, `pa_add a j` ↦
   `a + BitVec.ofNat 64 j`, `n : N` ↦ `n : Nat`, `nth_byte w j` ↦
   `nthByte (n := 4) w j` at `w : BitVec 32`).  Rocq's ambient `GenId`/`CpuId`
   are the explicit `gen`/`cpu` of `wpWexecStep` (WeakExec deviation 1); `WWP
   Loop` is `wwpTriv ⊤ (WExpr.loop gen cpu)`; `fin_to_nat cpu_id` is `cpu.val`;
   `register_lookup PC (wm_regs σ)` is `σ.wmRegs .PC`; `mstate`/`sregs`/`mdev`/
   `mem` are `ExecSt`/`.regs`/`.dev`/`.mem`.
2. THE FLAT MAP: Rocq `wflat (wm_img σ) (wm_log σ) !! a = Some v` is
   `wflatMem σ.wmImg σ.wmLog a = some v` (`WeakBridge.wflatMem`, definitionally
   `get? (wflat …) a`); `wstepPost`'s memory conjunct is
   `wflatMem σ'.wmImg σ'.wmLog = t.mem` (WeakBridge deviation 2).
3. STATEMENT SHAPES (WeakBridge deviation 8): Rocq `wlat_interp … -∗ X -∗ ⌜φ⌝`
   is `wlatInterp σ.wmImg σ.wmLog ⊢ X -∗ ⌜φ⌝`; Rocq `A -∗ B -∗ C -∗ D` is
   `A ⊢ B -∗ C -∗ D`; Rocq `P -∗ WWP Loop` is `P ⊢ WWP`.  `Example`s are
   `theorem`s.
4. O2, THE TEXT PIN: `wstepCert`'s and `wpWinstr`'s text hypothesis is
   `∀ j < 4, pinnedRead σ (accAddr pc j) ∧ fetchPinned σ (accAddr pc j)` (Rocq:
   `pinned_read` only, which under O2 no longer pins the i-cache fetch).  The
   Lean-only `wkernelTextTs` / `wkernelTextFetchPinned` /
   `wkernelTextTextPinned` discharge it from `wkernelText`;
   `wkernelTextPinned` is Rocq's statement.
5. `wkernel_text_pinned`'s `is_Some (bs !! pa_add a j)` is
   `∃ b, get? bs (a + BitVec.ofNat 64 j) = some b`; its width is `n : Nat`
   (Rocq `acc_wf a (N.of_nat n)`).
6. `wQ_store_w`/`wQ_amo_aq_w`: the stored value is `v : BitVec (8 * n)` (Rocq
   any width `{m : N} (v : bv m)`), because `WeakInterp.wwriteMsg` is stated at
   `8 * n` (WeakInterp deviation 7).  The width-4 instances take `v : BitVec 32`.
7. `load_post_fold_relp` is stated over `List.foldl` with the init first, as
   Lean's `foldl` takes it; `load_post_run_relp` additionally passes the Lean
   `loadPostRun`'s `ctrlPost` (`ctrlPostRelp`); `wread_post_relp`'s O2 arm is
   the i-cache identity (`wreadPost`'s `akIfetch` branch).
8. Lean-only helpers: `keepPure` (a pure consequence of `P ∗ Q` that keeps
   both, Rocq's non-consuming `iDestruct … as %`), `flatOfLatestVal`,
   `wpt4_at` (the definitional decode of a held `wpt4`), `wmstateInterpFacts`
   (the two pure conjuncts of `wmstateInterp` the rule reads), and the O2
   lemmas of deviation 4.

**Rocq → Lean name map.**  `wlat_flat_lookup` `wlatFlatLookup`,
`wlat_flat_lookup_e` `wlatFlatLookupE`, `wpt_own_h_flat_lookup`
`wptOwnHFlatLookup`, `wpt_flat_lookup` `wptFlatLookup`,
`wpt_img_flat_lookup_gen` `wptImgFlatLookupGen`, `wpt_img_flat_lookup`
`wptImgFlatLookup`, `wpt_byte_flat_pin` `wptByteFlatPin`,
`wpt_own_h_byte_flat_pin` `wptOwnHByteFlatPin`, `wlat_byte_flat_gen`
`wlatByteFlatGen`, `wpt4` `wpt4`, `wpt4_persistent` `wpt4_persistent`,
`wpt4_timeless` `wpt4_timeless`, `wpt4_facts` `wpt4Facts`, `wpt4_split`
`wpt4Split`, `wpt4_agree` `wpt4Agree`, `wpt4_flat_pin` `wpt4FlatPin`,
`wpt4_flat` `wpt4Flat`, `wpt4_pinned` `wpt4Pinned`, `wpt4_mono` `wpt4Mono`,
`wkernel_text` `wkernelText`, `wkernel_text_persistent`
`wkernelText_persistent`, `wkernel_text_v` `wkernelTextV`,
`wkernel_text_v_objective/persistent` `wkernelTextV_objective/persistent`,
`wkernel_text_at` `wkernelTextAt`, `wkernel_text_flat` `wkernelTextFlat`,
`wkernel_text_pinned` `wkernelTextPinned`, `wstep_cert` `wstepCert`,
`wstep_cert_mono` `wstepCertMono`, `wstep_post` `wstepPost`,
`wstep_post_ws_le` `wstepPostWsLe`, `wstep_post_log_le` `wstepPostLogLe`,
`wp_winstr` `wpWinstr`, `wP_load_w` `wPLoadW`, `wP_mem_w` `wPMemW`, `wP_none`
`wPNone`, `wV_fence` `wVFence`, `wV_store_w` `wVStoreW`, `wV_amo_aq_w`
`wVAmoAqW`, `wV_load_w` `wVLoadW`, `wQ_none` `wQNone`, `barrier_arms`
`barrierArms`, `barrier_post_relp` `WeakInstr.barrierPostRelp`, `wQ_fence`
`wQFence`, `wQ_load_w` `wQLoadW`, `load_post_fold_relp` `loadPostFoldRelp`,
`load_post_bytes_relp` `WeakInstr.loadPostBytesRelp`, `load_post_run_relp`
`WeakInstr.loadPostRunRelp`, `wread_post_relp` `WeakInstr.wreadPostRelp`,
`wm_class_of_relp` `WeakInstr.wmClassOfRelp`, `wQ_store_w` `wQStoreW`,
`wQ_amo_aq_w` `wQAmoAqW`, `wP_load` `wPLoad`, `wP_mem` `wPMem`, `wV_store`
`wVStore`, `wV_amo_aq` `wVAmoAq`, `wV_load` `wVLoad`, `wQ_load` `wQLoad`,
`wQ_store` `wQStore`, `wQ_amo_aq` `wQAmoAq`, `wQ_amo_aq_store`
`wQAmoAqStore`, `wQ_amo_aq_excl` `wQAmoAqExcl`, `wQ_store_wV` `wQStoreWV`,
`wQ_amo_aq_gain` `wQAmoAqGain`, `wwp_lw4` `wwpLw4`, `wwp_lw4_carry`
`wwpLw4Carry`, `wwp_release_deposit` `wwpReleaseDeposit`, `wwp_sw4_post`
`wwpSw4Post`, `wlat4` `wlat4`, `wlat4_objective` `wlat4_objective`,
`wwp_amoswap_w_aq_inv` `wwpAmoswapWAqInv`, `wwp_fence_deliver`
`wwpFenceDeliver`, `wwp_fence_scl_gen` `wwpFenceSclGen`, `wwp_fence_scl`
`wwpFenceScl`, `wwp_fence_scl_r` `wwpFenceSclR`, `wwp_fence_rw_w`
`wwpFenceRwW`, `wwp_smoke_sw_fence` `wwpSmokeSwFence`, `wwp_smoke_amo_lw`
`wwpSmokeAmoLw`.  The notation `a ↦w₄{dq} w` is kept.

**Not ported:** nothing -- every Rocq definition and lemma has a Lean twin.

**Statements checked** (by hand, against Rocq): all; the changed ones are listed
under the deviations.
-/
import Weak.WeakBridge
import Weak.WeakFence

namespace Weak

open Iris Iris.BI Iris.BI.MonPred Iris.ProofMode Iris.Std
open MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D LeanRV64D.Functions

/-! ## 0. Lean-only helpers -/

/-- A pure consequence of two resources, keeping both (Rocq's non-consuming
`iDestruct (lem with "H1 H2") as %h`). -/
theorem keepPure {PROP : Type _} [BI PROP] {P Q : PROP} {φ : Prop} (h : P ⊢ Q -∗ ⌜φ⌝) :
    P ⊢ Q -∗ ⌜φ⌝ ∗ P ∗ Q :=
  wand_intro ((and_intro (wand_elim h) .rfl).trans
    (persistent_and_affinely_sep_left_mp.trans (sep_mono_left affinely_elim)))

/-- The pure core of every §1 lemma: an element's latest-write fact pins the flat byte. -/
theorem flatOfLatestVal (img : Mem) (log : List Wmsg) (a : PAddr) (t : Nat) (v : BitVec 8) :
    wlogWf log → latestVal (imgZ img) log (paZ a) t v → wflatMem img log a = some v := by
  intro hwf hlat
  unfold wflatMem
  rw [wflatLatest img log a t hwf (latestValLatest _ _ _ _ _ hlat)]
  exact hlat.1

/-! ## 1. What the flat projection HOLDS at an owned byte

The `γlat` element for a byte says its LATEST write is `(t, v)`, and
`WeakLang.wflatLatest` says the flat projection holds exactly the latest write's
value.  So an element -- at ANY timestamp -- determines the flat byte, with no
hypothesis about the reader's views. -/

section flatBridge
variable {GF : BundledGFunctors} [WeakGS GF]

theorem wlatFlatLookup (σ : Wmstate) (a : PAddr) (dq : DFrac) (t : Nat) (v : BitVec 8) :
    wlogWf σ.wmLog →
    wlatInterp (GF := GF) σ.wmImg σ.wmLog ⊢
      wlatPointsto (paZ a) dq t v -∗ ⌜wflatMem σ.wmImg σ.wmLog a = some v⌝ := by
  intro hwf
  iintro Hi He
  ihave %hlat := wlatLookup σ.wmImg σ.wmLog (paZ a) dq t v $$ [Hi He]
  · iframe Hi He
  ipureintro
  exact flatOfLatestVal _ _ a t v hwf hlat

/-- The same over the BARE value element. -/
theorem wlatFlatLookupE (σ : Wmstate) (a : PAddr) (dq : DFrac) (t : Nat) (v : BitVec 8) :
    wlogWf σ.wmLog →
    wlatInterp (GF := GF) σ.wmImg σ.wmLog ⊢
      wlatElem (paZ a) dq t v -∗ ⌜wflatMem σ.wmImg σ.wmLog a = some v⌝ := by
  intro hwf
  iintro Hi He
  ihave %hlat := wlatLookupElem σ.wmImg σ.wmLog (paZ a) dq t v $$ [Hi He]
  · iframe Hi He
  ipureintro
  exact flatOfLatestVal _ _ a t v hwf hlat

theorem wptOwnHFlatLookup (c : CPU) (σ : Wmstate) (a : PAddr) (v : BitVec 8) :
    wlogWf σ.wmLog →
    wlatInterp (GF := GF) σ.wmImg σ.wmLog ⊢
      vwpHold (wptOwnH (GF := GF) c (paZ a) v) σ.wmWs -∗ ⌜wflatMem σ.wmImg σ.wmLog a = some v⌝ := by
  intro hwf
  iintro Hi Hpt
  icases (wptOwnH_at c (paZ a) v σ.wmWs).mp $$ Hpt with ⟨%t, He, -, -⟩
  iapply wlatFlatLookupE σ a (DFrac.own 1) t v hwf $$ Hi He

/-- The owned form (the receipt is not needed). -/
theorem wptFlatLookup (σ : Wmstate) (a : PAddr) (dq : DFrac) (v : BitVec 8) :
    wlogWf σ.wmLog →
    wlatInterp (GF := GF) σ.wmImg σ.wmLog ⊢
      vwpHold (paZ a ↦w{dq} v : VProp GF) σ.wmWs -∗ ⌜wflatMem σ.wmImg σ.wmLog a = some v⌝ := by
  intro hwf
  iintro Hi Hpt
  icases (wpt_at (paZ a) dq v σ.wmWs).mp $$ Hpt with ⟨%t, He, -⟩
  iapply wlatFlatLookup σ a dq t v hwf $$ Hi He

/-- The ERA-IMAGE form, at any timestamp: the flat byte AND `latestTs`. -/
theorem wptImgFlatLookupGen (σ : Wmstate) (a : PAddr) (dq : DFrac) (t : Nat) (v : BitVec 8) :
    wlogWf σ.wmLog →
    wlatInterp (GF := GF) σ.wmImg σ.wmLog ⊢
      wlatPointsto (paZ a) dq t v -∗
        ⌜wflatMem σ.wmImg σ.wmLog a = some v ∧ latestTs σ.wmLog (paZ a) = t⌝ := by
  intro hwf
  iintro Hi He
  ihave %hlat := wlatLookup σ.wmImg σ.wmLog (paZ a) dq t v $$ [Hi He]
  · iframe Hi He
  ipureintro
  exact ⟨flatOfLatestVal _ _ a t v hwf hlat, latestValTs _ _ _ _ _ hlat⟩

theorem wptImgFlatLookup (σ : Wmstate) (a : PAddr) (dq : DFrac) (v : BitVec 8) :
    wlogWf σ.wmLog →
    wlatInterp (GF := GF) σ.wmImg σ.wmLog ⊢
      wlatPointsto (paZ a) dq 0 v -∗
        ⌜wflatMem σ.wmImg σ.wmLog a = some v ∧ latestTs σ.wmLog (paZ a) = 0⌝ :=
  wptImgFlatLookupGen σ a dq 0 v

end flatBridge

/-! ## 1a'. The per-byte bridges, width-generic

Stated at the log's own key `WeakInterp.accAddr a j`, converted to the
`PAddr`-keyed flat map through `WeakBridge.accWfByte`. -/

section byteBridges
variable {GF : BundledGFunctors} [WeakGS GF]

/-- An OWNED byte of an access window: what the flat projection holds there, and
that it is pinned for this hart. -/
theorem wptByteFlatPin (σ : Wmstate) (a : PAddr) (n : Nat) (dq : DFrac) (b : BitVec 8) (j : Nat) :
    wlogWf σ.wmLog → accWf a n → j < n →
    wlatInterp (GF := GF) σ.wmImg σ.wmLog ⊢
      vwpHold (WeakInterp.accAddr a j ↦w{dq} b : VProp GF) σ.wmWs -∗
        ⌜wflatMem σ.wmImg σ.wmLog (a + BitVec.ofNat 64 j) = some b ∧
         pinnedRead σ (WeakInterp.accAddr a j)⌝ := by
  intro hwf hacc hj
  rw [← accWfByte a n j hacc hj]
  iintro Hi Hpt
  icases keepPure (wptPinnedRead σ _ dq b) $$ Hi Hpt with ⟨%hpin, Hi, Hpt⟩
  ihave %hfl := wptFlatLookup σ (a + BitVec.ofNat 64 j) dq b hwf $$ Hi Hpt
  ipureintro
  exact ⟨hfl, hpin⟩

/-- The OWNED (C-or-D) twin. -/
theorem wptOwnHByteFlatPin (c : CPU) (σ : Wmstate) (a : PAddr) (n : Nat) (b : BitVec 8) (j : Nat) :
    wlogWf σ.wmLog → accWf a n → j < n →
    wlatInterp (GF := GF) σ.wmImg σ.wmLog ⊢
      vwpHold (wptOwnH (GF := GF) c (WeakInterp.accAddr a j) b) σ.wmWs -∗
        ⌜wflatMem σ.wmImg σ.wmLog (a + BitVec.ofNat 64 j) = some b ∧
         pinnedRead σ (WeakInterp.accAddr a j)⌝ := by
  intro hwf hacc hj
  rw [← accWfByte a n j hacc hj]
  iintro Hi Hpt
  icases keepPure (wptOwnHPinnedRead c σ _ b) $$ Hi Hpt with ⟨%hpin, Hi, Hpt⟩
  ihave %hfl := wptOwnHFlatLookup c σ (a + BitVec.ofNat 64 j) b hwf $$ Hi Hpt
  ipureintro
  exact ⟨hfl, hpin⟩

/-- A BARE ELEMENT of an access window: the flat fact, plus the identification of
the element's timestamp with the byte's `latestTs`. -/
theorem wlatByteFlatGen (σ : Wmstate) (a : PAddr) (n : Nat) (dq : DFrac) (t : Nat) (b : BitVec 8)
    (j : Nat) :
    wlogWf σ.wmLog → accWf a n → j < n →
    wlatInterp (GF := GF) σ.wmImg σ.wmLog ⊢
      wlatPointsto (WeakInterp.accAddr a j) dq t b -∗
        ⌜wflatMem σ.wmImg σ.wmLog (a + BitVec.ofNat 64 j) = some b ∧
         latestTs σ.wmLog (WeakInterp.accAddr a j) = t⌝ := by
  intro hwf hacc hj
  rw [← accWfByte a n j hacc hj]
  exact wptImgFlatLookupGen σ (a + BitVec.ofNat 64 j) dq t b hwf

end byteBridges

/-! ## 1b. `↦w₄` -- the four-byte bundle

Four consecutive weak bytes plus 4-alignment (the model's access check) and
WRAP-FREEDOM of the window (`WeakBridge.accWf`). -/

section word4
variable {GF : BundledGFunctors} [WeakGS GF]

def wpt4 (a : PAddr) (dq : DFrac) (w : BitVec 32) : VProp GF :=
  iprop(⌜is_aligned_paddr (.Physaddr a) 4 = true⌝ ∗ ⌜accWf a 4⌝ ∗
    (WeakInterp.accAddr a 0 ↦w{dq} nthByte (n := 4) w 0) ∗
    (WeakInterp.accAddr a 1 ↦w{dq} nthByte (n := 4) w 1) ∗
    (WeakInterp.accAddr a 2 ↦w{dq} nthByte (n := 4) w 2) ∗
    (WeakInterp.accAddr a 3 ↦w{dq} nthByte (n := 4) w 3))

instance wpt4_persistent (a : PAddr) (w : BitVec 32) :
    Persistent (wpt4 (GF := GF) a DFrac.discard w) := by
  unfold wpt4; infer_instance

instance wpt4_timeless (a : PAddr) (q : Qp) (w : BitVec 32) :
    Timeless (wpt4 (GF := GF) a (DFrac.own q) w) := by
  unfold wpt4; infer_instance

/-- The definitional decode of a held bundle (Lean-only). -/
theorem wpt4_at (a : PAddr) (dq : DFrac) (w : BitVec 32) (ws : Wstate) :
    vwpHold (wpt4 (GF := GF) a dq w) ws ⊣⊢
      iprop(⌜is_aligned_paddr (.Physaddr a) 4 = true⌝ ∗ ⌜accWf a 4⌝ ∗
        vwpHold (WeakInterp.accAddr a 0 ↦w{dq} nthByte (n := 4) w 0 : VProp GF) ws ∗
        vwpHold (WeakInterp.accAddr a 1 ↦w{dq} nthByte (n := 4) w 1 : VProp GF) ws ∗
        vwpHold (WeakInterp.accAddr a 2 ↦w{dq} nthByte (n := 4) w 2 : VProp GF) ws ∗
        vwpHold (WeakInterp.accAddr a 3 ↦w{dq} nthByte (n := 4) w 3 : VProp GF) ws) := .rfl

theorem wpt4Facts (a : PAddr) (dq : DFrac) (w : BitVec 32) :
    wpt4 (GF := GF) a dq w ⊢ ⌜is_aligned_paddr (.Physaddr a) 4 = true ∧ accWf a 4⌝ := by
  unfold wpt4
  iintro ⟨%h1, %h2, -⟩
  ipureintro
  exact ⟨h1, h2⟩

/-- FRACTION SPLIT / JOIN, byte by byte from `wpt_split`. -/
theorem wpt4Split (a : PAddr) (q1 q2 : Qp) (w : BitVec 32) :
    wpt4 (GF := GF) a (DFrac.own (q1 + q2)) w ⊣⊢
      iprop(wpt4 (GF := GF) a (DFrac.own q1) w ∗ wpt4 (GF := GF) a (DFrac.own q2) w) := by
  unfold wpt4
  constructor
  · iintro ⟨%hal, %hacc, H0, H1, H2, H3⟩
    icases (wpt_split _ q1 q2 _).mp $$ H0 with ⟨A0, B0⟩
    icases (wpt_split _ q1 q2 _).mp $$ H1 with ⟨A1, B1⟩
    icases (wpt_split _ q1 q2 _).mp $$ H2 with ⟨A2, B2⟩
    icases (wpt_split _ q1 q2 _).mp $$ H3 with ⟨A3, B3⟩
    isplitl [A0 A1 A2 A3]
    · isplitr
      · ipureintro; exact hal
      isplitr
      · ipureintro; exact hacc
      iframe A0 A1 A2 A3
    · isplitr
      · ipureintro; exact hal
      isplitr
      · ipureintro; exact hacc
      iframe B0 B1 B2 B3
  · iintro ⟨⟨%hal, %hacc, A0, A1, A2, A3⟩, ⟨-, -, B0, B1, B2, B3⟩⟩
    isplitr
    · ipureintro; exact hal
    isplitr
    · ipureintro; exact hacc
    isplitl [A0 B0]
    · iapply (wpt_split _ q1 q2 _).mpr; iframe A0 B0
    isplitl [A1 B1]
    · iapply (wpt_split _ q1 q2 _).mpr; iframe A1 B1
    isplitl [A2 B2]
    · iapply (wpt_split _ q1 q2 _).mpr; iframe A2 B2
    · iapply (wpt_split _ q1 q2 _).mpr; iframe A3 B3

theorem wpt4Agree (a : PAddr) (dq1 : DFrac) (w1 : BitVec 32) (dq2 : DFrac) (w2 : BitVec 32) :
    iprop(wpt4 (GF := GF) a dq1 w1 ∗ wpt4 (GF := GF) a dq2 w2) ⊢ (⌜w1 = w2⌝ : VProp GF) := by
  unfold wpt4
  iintro ⟨⟨-, -, A0, A1, A2, A3⟩, ⟨-, -, B0, B1, B2, B3⟩⟩
  ihave %E0 := wpt_agree _ dq1 _ dq2 _ $$ [A0 B0]
  · iframe A0 B0
  ihave %E1 := wpt_agree _ dq1 _ dq2 _ $$ [A1 B1]
  · iframe A1 B1
  ihave %E2 := wpt_agree _ dq1 _ dq2 _ $$ [A2 B2]
  · iframe A2 B2
  ihave %E3 := wpt_agree _ dq1 _ dq2 _ $$ [A3 B3]
  · iframe A3 B3
  ipureintro
  apply bvEqOfBytes (n := 4) w1 w2
  intro j hj
  rcases j with _ | _ | _ | _ | j
  · exact E0
  · exact E1
  · exact E2
  · exact E3
  · omega

/-- THE FLAT + PINNED FACTS over the window, in one pass. -/
theorem wpt4FlatPin (σ : Wmstate) (a : PAddr) (dq : DFrac) (w : BitVec 32) :
    wlogWf σ.wmLog →
    wlatInterp (GF := GF) σ.wmImg σ.wmLog ⊢
      vwpHold (wpt4 (GF := GF) a dq w) σ.wmWs -∗
        ⌜accWf a 4 ∧
         ∀ j : Nat, j < 4 →
           wflatMem σ.wmImg σ.wmLog (a + BitVec.ofNat 64 j) = some (nthByte (n := 4) w j) ∧
           pinnedRead σ (WeakInterp.accAddr a j)⌝ := by
  intro hwf
  iintro Hi Hpt
  icases (wpt4_at a dq w σ.wmWs).mp $$ Hpt with ⟨%hal, %hacc, H0, H1, H2, H3⟩
  icases keepPure (wptByteFlatPin σ a 4 dq _ 0 hwf hacc (by omega)) $$ Hi H0 with ⟨%E0, Hi, -⟩
  icases keepPure (wptByteFlatPin σ a 4 dq _ 1 hwf hacc (by omega)) $$ Hi H1 with ⟨%E1, Hi, -⟩
  icases keepPure (wptByteFlatPin σ a 4 dq _ 2 hwf hacc (by omega)) $$ Hi H2 with ⟨%E2, Hi, -⟩
  ihave %E3 := wptByteFlatPin σ a 4 dq _ 3 hwf hacc (by omega) $$ Hi H3
  ipureintro
  refine ⟨hacc, ?_⟩
  intro j hj
  rcases j with _ | _ | _ | _ | j
  · exact E0
  · exact E1
  · exact E2
  · exact E3
  · omega

/-- WHAT THE FLAT PROJECTION HOLDS over the window. -/
theorem wpt4Flat (σ : Wmstate) (a : PAddr) (dq : DFrac) (w : BitVec 32) :
    wlogWf σ.wmLog →
    wlatInterp (GF := GF) σ.wmImg σ.wmLog ⊢
      vwpHold (wpt4 (GF := GF) a dq w) σ.wmWs -∗
        ⌜∀ j : Nat, j < 4 →
           wflatMem σ.wmImg σ.wmLog (a + BitVec.ofNat 64 j) = some (nthByte (n := 4) w j)⌝ := by
  intro hwf
  iintro Hi Hpt
  ihave %h := wpt4FlatPin σ a dq w hwf $$ Hi Hpt
  ipureintro
  intro j hj
  exact (h.2 j hj).1

/-- ... and that the window is PINNED for this hart (no `wlogWf` premise). -/
theorem wpt4Pinned (σ : Wmstate) (a : PAddr) (dq : DFrac) (w : BitVec 32) :
    wlatInterp (GF := GF) σ.wmImg σ.wmLog ⊢
      vwpHold (wpt4 (GF := GF) a dq w) σ.wmWs -∗
        ⌜∀ j : Nat, j < 4 → pinnedRead σ (WeakInterp.accAddr a j)⌝ := by
  iintro Hi Hpt
  icases (wpt4_at a dq w σ.wmWs).mp $$ Hpt with ⟨%hal, %hacc, H0, H1, H2, H3⟩
  icases keepPure (wptPinnedRead σ _ dq _) $$ Hi H0 with ⟨%E0, Hi, -⟩
  icases keepPure (wptPinnedRead σ _ dq _) $$ Hi H1 with ⟨%E1, Hi, -⟩
  icases keepPure (wptPinnedRead σ _ dq _) $$ Hi H2 with ⟨%E2, Hi, -⟩
  ihave %E3 := wptPinnedRead σ _ dq _ $$ Hi H3
  ipureintro
  intro j hj
  rcases j with _ | _ | _ | _ | j
  · exact E0
  · exact E1
  · exact E2
  · exact E3
  · omega

/-- MONOTONICITY across a step. -/
theorem wpt4Mono (a : PAddr) (dq : DFrac) (w : BitVec 32) (ws ws' : Wstate) :
    wsLe ws ws' → vwpHold (wpt4 (GF := GF) a dq w) ws ⊢ vwpHold (wpt4 (GF := GF) a dq w) ws' :=
  fun h => vwpHold_mono _ h

end word4

notation:50 a:50 " ↦w₄{" dq "} " w:50 => wpt4 a dq w

/-! ## 2. `wkernelText` -- the weak kernel-text resource

An era-image byte's element is `wlatPointsto a dq 0 v`, an ordinary `IProp`:
OBJECTIVE, PERSISTENT at `DFrac.discard`, and -- by §1 -- enough to pin the flat
byte AND to give `pinnedRead` (and, under O2, `fetchPinned`) for free. -/

section text
variable {GF : BundledGFunctors} [WeakGS GF]

def wkernelText (bs : GMapF PAddr (BitVec 8)) : IProp GF :=
  iprop([∗map] a ↦ b ∈ bs, wlatPointsto (GF := GF) (paZ a) DFrac.discard 0 b)

instance wkernelText_persistent (bs : GMapF PAddr (BitVec 8)) :
    Persistent (wkernelText (GF := GF) bs) := by
  unfold wkernelText; infer_instance

/-- The `VProp` reading: a big-op of `wptImg`s, hence objective. -/
def wkernelTextV (bs : GMapF PAddr (BitVec 8)) : VProp GF :=
  iprop([∗map] a ↦ b ∈ bs, wptImg (GF := GF) (paZ a) DFrac.discard b)

instance wkernelTextV_objective (bs : GMapF PAddr (BitVec 8)) :
    Objective (wkernelTextV (GF := GF) bs) := by
  unfold wkernelTextV; infer_instance

instance wkernelTextV_persistent (bs : GMapF PAddr (BitVec 8)) :
    Persistent (wkernelTextV (GF := GF) bs) := by
  unfold wkernelTextV; infer_instance

theorem wkernelTextAt (bs : GMapF PAddr (BitVec 8)) (ws : Wstate) :
    vwpHold (wkernelTextV (GF := GF) bs) ws ⊣⊢ wkernelText (GF := GF) bs := by
  unfold vwpHold wkernelTextV wkernelText
  exact monPred_at_big_sepM _ _ _

/-- THE TWO FACTS A FETCH NEEDS, off one text byte. -/
theorem wkernelTextFlat (σ : Wmstate) (bs : GMapF PAddr (BitVec 8)) (a : PAddr) (b : BitVec 8) :
    wlogWf σ.wmLog → get? bs a = some b →
    wlatInterp (GF := GF) σ.wmImg σ.wmLog ⊢
      wkernelText (GF := GF) bs -∗
        ⌜wflatMem σ.wmImg σ.wmLog a = some b ∧ latestTs σ.wmLog (paZ a) = 0⌝ := by
  intro hwf hlk
  unfold wkernelText
  iintro Hi Ht
  ihave He := BigSepM.bigSepM_lookup
    (Φ := fun a b => wlatPointsto (GF := GF) (paZ a) DFrac.discard 0 b) hlk $$ Ht
  iapply wptImgFlatLookup σ a DFrac.discard b hwf $$ Hi He

/-- Over a whole window: every text byte is unwritten this era (Lean-only, the
common core of the two pins). -/
theorem wkernelTextTs (σ : Wmstate) (bs : GMapF PAddr (BitVec 8)) (a : PAddr) (n : Nat) :
    accWf a n →
    (∀ j, j < n → ∃ b, get? bs (a + BitVec.ofNat 64 j) = some b) →
    wlogWf σ.wmLog →
    wlatInterp (GF := GF) σ.wmImg σ.wmLog ⊢
      wkernelText (GF := GF) bs -∗
        ⌜∀ j : Nat, j < n → latestTs σ.wmLog (WeakInterp.accAddr a j) = 0⌝ := by
  intro hacc hdom hwf
  apply wand_intro
  by_cases hall : ∀ j : Nat, j < n → latestTs σ.wmLog (WeakInterp.accAddr a j) = 0
  · exact pure_intro hall
  · have hex : ∃ j, j < n ∧ ¬ latestTs σ.wmLog (WeakInterp.accAddr a j) = 0 := by
      apply Classical.byContradiction
      intro hne
      exact hall fun j hj => Classical.byContradiction fun hp => hne ⟨j, hj, hp⟩
    obtain ⟨j, hj, hnp⟩ := hex
    obtain ⟨b, hb⟩ := hdom j hj
    refine (wand_elim (wkernelTextFlat σ bs _ b hwf hb)).trans (pure_mono fun h => ?_)
    exact absurd (by rw [← accWfByte a n j hacc hj]; exact h.2) hnp

/-- ... and the `pinnedRead` side, which makes the fetch footprint free of any view
hypothesis. -/
theorem wkernelTextPinned (σ : Wmstate) (bs : GMapF PAddr (BitVec 8)) (a : PAddr) (n : Nat) :
    accWf a n →
    (∀ j, j < n → ∃ b, get? bs (a + BitVec.ofNat 64 j) = some b) →
    wlogWf σ.wmLog →
    wlatInterp (GF := GF) σ.wmImg σ.wmLog ⊢
      wkernelText (GF := GF) bs -∗
        ⌜∀ j : Nat, j < n → pinnedRead σ (WeakInterp.accAddr a j)⌝ := by
  intro hacc hdom hwf
  iintro Hi Ht
  ihave %h := wkernelTextTs σ bs a n hacc hdom hwf $$ Hi Ht
  ipureintro
  exact fun j hj => pinnedReadUnwritten σ _ (h j hj)

/-- O2: the fetch pin, likewise free (Lean-only). -/
theorem wkernelTextFetchPinned (σ : Wmstate) (bs : GMapF PAddr (BitVec 8)) (a : PAddr) (n : Nat) :
    accWf a n →
    (∀ j, j < n → ∃ b, get? bs (a + BitVec.ofNat 64 j) = some b) →
    wlogWf σ.wmLog →
    wlatInterp (GF := GF) σ.wmImg σ.wmLog ⊢
      wkernelText (GF := GF) bs -∗
        ⌜∀ j : Nat, j < n → fetchPinned σ (WeakInterp.accAddr a j)⌝ := by
  intro hacc hdom hwf
  iintro Hi Ht
  ihave %h := wkernelTextTs σ bs a n hacc hdom hwf $$ Hi Ht
  ipureintro
  exact fun j hj => fetchPinnedUnwritten σ _ (h j hj)

/-- O2: both pins at once -- the text obligation of `wstepCert`/`wpWinstr` (Lean-only). -/
theorem wkernelTextTextPinned (σ : Wmstate) (bs : GMapF PAddr (BitVec 8)) (a : PAddr) (n : Nat) :
    accWf a n →
    (∀ j, j < n → ∃ b, get? bs (a + BitVec.ofNat 64 j) = some b) →
    wlogWf σ.wmLog →
    wlatInterp (GF := GF) σ.wmImg σ.wmLog ⊢
      wkernelText (GF := GF) bs -∗
        ⌜∀ j : Nat, j < n →
          pinnedRead σ (WeakInterp.accAddr a j) ∧ fetchPinned σ (WeakInterp.accAddr a j)⌝ := by
  intro hacc hdom hwf
  iintro Hi Ht
  ihave %h := wkernelTextTs σ bs a n hacc hdom hwf $$ Hi Ht
  ipureintro
  exact fun j hj => ⟨pinnedReadUnwritten σ _ (h j hj), fetchPinnedUnwritten σ _ (h j hj)⟩

end text

/-! ## 3. The pin certificate

`WeakBridge.wstepOk (some tid) (riscvStep tick) σ` is the ONE peel a leaf owes.
READ IT AS: "a step of the hart `cid` whose PC is `pc` touches the four text
bytes at `pc` (which are unwritten this era) and, beyond that, only what `P`
describes".  `P` is instantiated per leaf: a plain LOAD `wPLoad ea` (discharged
by `wpt4Pinned`); a plain STORE `wPMem ea` (a write has no read to pin);
`amoswap.w.aq` `wPMem ea` (the read half is `akLatest`, which forces the latest
read with no ownership and no view: THIS is why the invariant form of the
acquire is possible at all); `fence` `wPNone`.

AND WHAT THE CERTIFICATE ALSO CARRIES: the instruction's WEAK-MEMORY EFFECT `Q`,
a relation between the pre- and the successor STATE (M3b's correction, landed at
M3c): a store leaf has to say WHICH message the step appended, a statement about
`σ'.wmLog`.  The view-level predicates are `wV*`, the certificate-level ones the
`wQ*` built on them. -/

def wstepCert (cid : Nat) (pc : BitVec 64) (P : Wmstate → Prop) (Q : Wmstate → Wmstate → Prop) :
    Prop :=
  ∀ (σ : Wmstate) (tick : Bool),
    σ.wmRegs .PC = pc →
    accWf pc 4 →
    (∀ j : Nat, j < 4 →
      pinnedRead σ (WeakInterp.accAddr pc j) ∧ fetchPinned σ (WeakInterp.accAddr pc j)) →
    P σ →
    wstepOk (some cid) (riscvStep tick) σ ∧
    (∀ χ σ' χ', wexec (some cid) (riscvStep tick) χ σ = some ((), σ', χ') → Q σ σ')

/-- The certificate is contravariant in `P` and covariant in `Q`. -/
theorem wstepCertMono (cid : Nat) (pc : BitVec 64) (P P' : Wmstate → Prop)
    (Q Q' : Wmstate → Wmstate → Prop) :
    (∀ σ, P' σ → P σ) → (∀ σ σ', Q σ σ' → Q' σ σ') →
    wstepCert cid pc P Q → wstepCert cid pc P' Q' := by
  intro hP hQ hc σ tick hpc hwf htext hP'
  obtain ⟨hok, hq⟩ := hc σ tick hpc hwf htext (hP σ hP')
  exact ⟨hok, fun χ σ' χ' hex => hQ σ σ' (hq χ σ' χ' hex)⟩

/-! ## 4. THE RULE

`wstepPost` is the successor's contract: registers/devices/flat memory are the
SC ones, the image never moves, the log only grows, the hart's views only grow,
and the two machine invariants are re-established. -/

def wstepPost (σ σ' : Wmstate) (t : ExecSt) : Prop :=
  σ'.wmRegs = t.regs ∧
  σ'.wmDev = t.dev ∧
  wflatMem σ'.wmImg σ'.wmLog = t.mem ∧
  σ'.wmImg = σ.wmImg ∧
  (∃ l, σ'.wmLog = σ.wmLog ++ l) ∧
  wsLe σ.wmWs σ'.wmWs ∧
  wlogWf σ'.wmLog ∧
  wsBounded σ'.wmWs σ'.wmLog.length

theorem wstepPostWsLe (σ σ' : Wmstate) (t : ExecSt) : wstepPost σ σ' t → wsLe σ.wmWs σ'.wmWs :=
  fun h => h.2.2.2.2.2.1

theorem wstepPostLogLe (σ σ' : Wmstate) (t : ExecSt) :
    wstepPost σ σ' t → σ.wmLog.length ≤ σ'.wmLog.length := by
  intro h
  obtain ⟨l, hl⟩ := h.2.2.2.2.1
  rw [hl, List.length_append]
  omega

section rule
variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [WeakGS GF]

/-- The two pure conjuncts of the hart interpretation the rule reads, kept
(Lean-only). -/
theorem wmstateInterpFacts (cpu : CPU) (σ : Wmstate) :
    wmstateInterp (hlc := hlc) (GF := GF) cpu σ ⊢
      ⌜wsBounded σ.wmWs σ.wmLog.length ∧ wlogWf σ.wmLog⌝ ∗
        wmstateInterp (hlc := hlc) (GF := GF) cpu σ := by
  unfold wmstateInterp
  iintro ⟨%h1, %h2, %h3, H⟩
  isplitr
  · ipureintro; exact ⟨h1, h3⟩
  isplitr
  · ipureintro; exact h1
  isplitr
  · ipureintro; exact h2
  isplitr
  · ipureintro; exact h3
  iexact H

theorem wpWinstr (gen : Nat) (cpu : CPU) (pc : BitVec 64) (P : Wmstate → Prop)
    (Q : Wmstate → Wmstate → Prop) :
    gen = 0 →
    accWf pc 4 →
    wstepCert cpu.val pc P Q →
    (∀ σ : Wmstate, wmstateInterp (hlc := hlc) (GF := GF) cpu σ ={⊤,∅}=∗
      ⌜σ.wmRegs .PC = pc⌝ ∗
      ⌜∀ j : Nat, j < 4 →
        pinnedRead σ (WeakInterp.accAddr pc j) ∧ fetchPinned σ (WeakInterp.accAddr pc j)⌝ ∗
      ⌜P σ⌝ ∗
      ∃ t0 t1 : ExecSt,
        ⌜exec (riscvStep false) (wflatSt σ) = some ((), t0)⌝ ∗
        ⌜exec (riscvStep true) (wflatSt σ) = some ((), t1)⌝ ∗
        ▷ (∀ (tick : Bool) (σ' : Wmstate),
            ⌜wstepPost σ σ' (if tick then t1 else t0)⌝ -∗
            ⌜Q σ σ'⌝ ={∅,⊤}=∗
              wmstateInterp (hlc := hlc) (GF := GF) cpu σ' ∗
              wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu))) ⊢
    wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu) := by
  intro hgen haccpc hcert
  iintro H
  iapply wpWexecStep gen cpu hgen
  iintro %σ Hσ
  icases wmstateInterpFacts cpu σ $$ Hσ with ⟨%hfacts, Hσ⟩
  obtain ⟨hbnd, hwf⟩ := hfacts
  imod H $$ %σ Hσ with ⟨%hpc, %htext, %hP, %t0, %t1, %hex0, %hex1, Hk⟩
  have hc : ∀ tick : Bool,
      wstepOk (some cpu.val) (riscvStep tick) σ ∧
      (∀ χ σ' χ', wexec (some cpu.val) (riscvStep tick) χ σ = some ((), σ', χ') → Q σ σ') :=
    fun tick => hcert σ tick hpc haccpc htext hP
  obtain ⟨_, hred0, hag0⟩ := wexecLeafAgree _ _ σ () t0 (hc false).1 hwf hex0
  obtain ⟨_, _, hag1⟩ := wexecLeafAgree _ _ σ () t1 (hc true).1 hwf hex1
  imodintro
  isplitr
  · ipureintro
    intro tick
    exact wstepOkCovers _ _ _ (hc tick).1
  isplitr
  · ipureintro; exact hred0
  inext
  iintro %tick %χ %σ' %χ' %hex
  have hq := (hc tick).2 χ σ' χ' hex
  have hrun := wexecWrun _ _ χ σ () σ' χ' hex
  have hag : σ'.wmRegs = (if tick then t1 else t0).regs ∧
      σ'.wmDev = (if tick then t1 else t0).dev ∧
      wflatMem σ'.wmImg σ'.wmLog = (if tick then t1 else t0).mem ∧ wlogWf σ'.wmLog := by
    cases tick
    · obtain ⟨_, h1, h2, h3, h4⟩ := hag0 χ () σ' χ' hex
      exact ⟨h1, h2, h3, h4⟩
    · obtain ⟨_, h1, h2, h3, h4⟩ := hag1 χ () σ' χ' hex
      exact ⟨h1, h2, h3, h4⟩
  obtain ⟨hr, hd, hm, hw⟩ := hag
  have hpost : wstepPost σ σ' (if tick then t1 else t0) :=
    ⟨hr, hd, hm, wrunImg _ _ _ _ _ hrun, wrunLogApp _ _ _ _ _ hrun, wrunWsLe _ _ _ _ _ hrun, hw,
      wrunWsBounded _ _ _ _ _ hrun hbnd⟩
  iapply Hk $$ %tick %σ'
  · ipureintro; exact hpost
  · ipureintro; exact hq

end rule

/-! ## 5. THE FOUR LEAVES

One `P`/`Q` pair per instruction class, and the resource-side lemmas that
discharge `P` and consume `Q`.  The whole family is WIDTH-GENERIC (`*W`), the
width-4 names are its `n := 4` instances. -/

def wPLoadW (n : Nat) (ea : PAddr) : Wmstate → Prop :=
  fun σ => accWf ea n ∧ ∀ j : Nat, j < n → pinnedRead σ (WeakInterp.accAddr ea j)
def wPMemW (n : Nat) (ea : PAddr) : Wmstate → Prop := fun _ => accWf ea n
def wPNone : Wmstate → Prop := fun _ => True

/-! ### The VIEW-level effects (`wV*`) -/

def wVFence (b : barrier_kind) : Wmstate → Wstate → Prop :=
  fun σ ws' => wsLe (barrierPost σ.wmWs b) ws'
def wVStoreW (n : Nat) (ea : PAddr) : Wmstate → Wstate → Prop :=
  fun σ ws' => ∀ j : Nat, j < n →
    σ.wmLog.length + 1 ≤ flr (wsView ws') (WeakInterp.accAddr ea j)
def wVAmoAqW (n : Nat) (ea : PAddr) : Wmstate → Wstate → Prop :=
  fun σ ws' => ∀ j : Nat, j < n →
    viewScl (latestTs σ.wmLog (WeakInterp.accAddr ea j)) ≤ wsView ws'
def wVLoadW (n : Nat) (ea : PAddr) : Wmstate → Wstate → Prop :=
  fun σ ws' => ∀ j : Nat, j < n →
    viewByte (WeakInterp.accAddr ea j) (latestTs σ.wmLog (WeakInterp.accAddr ea j)) ≤ wsView ws'

/-! ### The CERTIFICATE-level effects (`wQ*`) -/

def wQNone : Wmstate → Wmstate → Prop := fun _ _ => True

/-- `wRelp` after a barrier: a `pw ∧ sw` fence ARMS the next store. -/
def barrierArms (b : barrier_kind) : Bool :=
  match b with
  | .Barrier_RISCV_rw_w | .Barrier_RISCV_w_w | .Barrier_RISCV_rw_rw
  | .Barrier_RISCV_w_rw | .Barrier_RISCV_tso => true
  | _ => false

theorem WeakInstr.barrierPostRelp (ws : Wstate) (b : barrier_kind) :
    barrierArms b = true → (barrierPost ws b).wRelp = true := by
  cases b <;> first | (intro _; rfl) | (intro h; exact absurd h (by decide))

def wQFence (b : barrier_kind) : Wmstate → Wmstate → Prop :=
  fun σ σ' => wVFence b σ σ'.wmWs ∧ (barrierArms b = true → σ'.wmWs.wRelp = true)

def wQLoadW (n : Nat) (ea : PAddr) : Wmstate → Wmstate → Prop :=
  fun σ σ' => σ'.wmImg = σ.wmImg ∧ σ'.wmLog = σ.wmLog ∧ wVLoadW n ea σ σ'.wmWs

/-- `wRelp` IS INERT UNDER READS (φ-upgrade §1). -/
theorem loadPostFoldRelp (aq : Bool) (vpre : Nat) (ats : List (Int × Nat)) (ws : Wstate) :
    (ats.foldl (fun w at_ => loadPostAt w aq vpre at_.1 at_.2) ws).wRelp = ws.wRelp := by
  induction ats generalizing ws with
  | nil => rfl
  | cons p l ih => exact ih _

theorem WeakInstr.loadPostBytesRelp (ws : Wstate) (aq : Bool) (ats : List (Int × Nat)) :
    (loadPostBytes ws aq ats).wRelp = ws.wRelp :=
  loadPostFoldRelp _ _ _ _

theorem WeakInstr.loadPostRunRelp (ws : Wstate) (aq : Bool) (base : Int) (ts : List Nat) :
    (loadPostRun ws aq base ts).wRelp = ws.wRelp := by
  unfold loadPostRun
  rw [ctrlPostRelp]
  exact WeakInstr.loadPostBytesRelp _ _ _

theorem WeakInstr.wreadPostRelp (s : Wmstate) (ak : AkInfo) (pa : PAddr) (ts : List Nat) :
    (wreadPost s ak pa ts).wmWs.wRelp = s.wmWs.wRelp := by
  unfold wreadPost
  split
  · rfl
  · exact WeakInstr.loadPostRunRelp _ _ _ _

/-- ... hence a class computed at a state whose `wRelp` is set is never `WCplain`. -/
theorem WeakInstr.wmClassOfRelp (ak : AkInfo) (ws : Wstate) :
    ws.wRelp = true → wmClassOf ak ws ≠ .WCplain := by
  intro hr
  unfold wmClassOf
  rw [hr]
  cases ak.akLatest <;> simp

/-- A width-`n` STORE of `v` to `ea`: ONE message at the log's fresh top (its class
existential), and the hart's own floor covers it afterwards. -/
def wQStoreW (n : Nat) (tid : Option Nat) (ea : PAddr) (v : BitVec (8 * n)) :
    Wmstate → Wmstate → Prop :=
  fun σ σ' =>
    σ'.wmImg = σ.wmImg ∧
    (∃ k, σ'.wmLog = σ.wmLog ++ [wwriteMsg tid k ea n v] ∧
      (σ.wmWs.wRelp = true → k ≠ .WCplain)) ∧
    wsLe σ.wmWs σ'.wmWs ∧
    wVStoreW n ea σ σ'.wmWs

/-- `amoswap` with `.aq` writing `v`: the store effect, PLUS the acquire's index
gain, PLUS the exclusive class of the write half. -/
def wQAmoAqW (n : Nat) (tid : Option Nat) (ea : PAddr) (v : BitVec (8 * n)) :
    Wmstate → Wmstate → Prop :=
  fun σ σ' => wQStoreW n tid ea v σ σ' ∧ wVAmoAqW n ea σ σ'.wmWs ∧
    σ'.wmLog = σ.wmLog ++ [wwriteMsg tid .WCexcl ea n v]

/-! ### The WIDTH-4 NAMES, as instances -/

def wPLoad (ea : PAddr) : Wmstate → Prop := wPLoadW 4 ea
def wPMem (ea : PAddr) : Wmstate → Prop := wPMemW 4 ea
def wVStore (ea : PAddr) : Wmstate → Wstate → Prop := wVStoreW 4 ea
def wVAmoAq (ea : PAddr) : Wmstate → Wstate → Prop := wVAmoAqW 4 ea
def wVLoad (ea : PAddr) : Wmstate → Wstate → Prop := wVLoadW 4 ea
def wQLoad (ea : PAddr) : Wmstate → Wmstate → Prop := wQLoadW 4 ea
def wQStore (tid : Option Nat) (ea : PAddr) (v : BitVec 32) : Wmstate → Wmstate → Prop :=
  wQStoreW 4 tid ea v
def wQAmoAq (tid : Option Nat) (ea : PAddr) (v : BitVec 32) : Wmstate → Wmstate → Prop :=
  wQAmoAqW 4 tid ea v

theorem wQAmoAqStore (tid : Option Nat) (ea : PAddr) (v : BitVec 32) (σ σ' : Wmstate) :
    wQAmoAq tid ea v σ σ' → wQStore tid ea v σ σ' :=
  fun h => h.1

theorem wQAmoAqExcl (tid : Option Nat) (ea : PAddr) (v : BitVec 32) (σ σ' : Wmstate) :
    wQAmoAq tid ea v σ σ' → σ'.wmLog = σ.wmLog ++ [wwriteMsg tid .WCexcl ea 4 v] :=
  fun h => h.2.2

theorem wQStoreWV (tid : Option Nat) (ea : PAddr) (v : BitVec 32) (σ σ' : Wmstate) :
    wQStore tid ea v σ σ' → wVStore ea σ σ'.wmWs :=
  fun h => h.2.2.2

theorem wQAmoAqGain (tid : Option Nat) (ea : PAddr) (v : BitVec 32) (σ σ' : Wmstate) :
    wQAmoAq tid ea v σ σ' → wVAmoAq ea σ σ'.wmWs :=
  fun h => h.2.1

section leaves
variable {GF : BundledGFunctors} [WeakGS GF]

/-! ### 5a. `lw` / `ld` -- the plain 4-byte LOAD, owned form -/

theorem wwpLw4 (σ : Wmstate) (ea : PAddr) (dq : DFrac) (w : BitVec 32) :
    wlogWf σ.wmLog →
    wlatInterp (GF := GF) σ.wmImg σ.wmLog ⊢
      vwpHold (wpt4 (GF := GF) ea dq w) σ.wmWs -∗
        ⌜wPLoad ea σ ∧
         ∀ j : Nat, j < 4 →
           wflatMem σ.wmImg σ.wmLog (ea + BitVec.ofNat 64 j) = some (nthByte (n := 4) w j)⌝ := by
  intro hwf
  iintro Hi Hpt
  ihave %h := wpt4FlatPin σ ea dq w hwf $$ Hi Hpt
  ipureintro
  obtain ⟨hacc, hall⟩ := h
  exact ⟨⟨hacc, fun j hj => (hall j hj).2⟩, fun j hj => (hall j hj).1⟩

/-- ... and the frame: the loaded word survives the step. -/
theorem wwpLw4Carry (σ σ' : Wmstate) (t : ExecSt) (ea : PAddr) (dq : DFrac) (w : BitVec 32) :
    wstepPost σ σ' t →
    vwpHold (wpt4 (GF := GF) ea dq w) σ.wmWs ⊢ vwpHold (wpt4 (GF := GF) ea dq w) σ'.wmWs :=
  fun hp => wpt4Mono ea dq w _ _ (wstepPostWsLe σ σ' t hp)

/-! ### 5b. `sw` / `sd` -- the 4-byte STORE, and the release deposit -/

theorem wwpReleaseDeposit (R : VProp GF) (σ : Wmstate) :
    wsBounded σ.wmWs σ.wmLog.length →
    vwpHold R σ.wmWs ⊢ R.monPred_at (viewScl (σ.wmLog.length + 1)) :=
  fun hb => release_deposit R σ.wmWs σ.wmLog hb

/-- The store's own post-view, in the form the next instruction consumes. -/
theorem wwpSw4Post (σ : Wmstate) (ws' : Wstate) (ea : PAddr) :
    wVStore ea σ ws' →
    ∀ j : Nat, j < 4 →
      viewByte (WeakInterp.accAddr ea j) (σ.wmLog.length + 1) ≤ wsView ws' :=
  fun hQ j hj => (viewByte_le _ _ _).mpr (hQ j hj)

/-! ### 5c. `amoswap.w.aq` -- THE ACQUIRE, invariant form

The read half of an AMO is `akLatest`, which forces the latest write: the read is
on the pinned fragment with NO ownership and NO hypothesis about the reader's
views.  So the resource this leaf fires off is a BARE LATEST-WRITE ELEMENT
BUNDLE, an `IProp`, hence OBJECTIVE, hence admissible inside an invariant. -/

def wlat4 (ea : PAddr) (dq : DFrac) (t : Nat) (w : BitVec 32) : IProp GF :=
  iprop(wlatPointsto (GF := GF) (WeakInterp.accAddr ea 0) dq t (nthByte (n := 4) w 0) ∗
    wlatPointsto (GF := GF) (WeakInterp.accAddr ea 1) dq t (nthByte (n := 4) w 1) ∗
    wlatPointsto (GF := GF) (WeakInterp.accAddr ea 2) dq t (nthByte (n := 4) w 2) ∗
    wlatPointsto (GF := GF) (WeakInterp.accAddr ea 3) dq t (nthByte (n := 4) w 3))

instance wlat4_objective (ea : PAddr) (dq : DFrac) (t : Nat) (w : BitVec 32) :
    Objective (iprop(⎡wlat4 (GF := GF) ea dq t w⎤) : VProp GF) := by
  infer_instance

theorem wwpAmoswapWAqInv (R : VProp GF) (σ : Wmstate) (ws' : Wstate) (ea : PAddr) (dq : DFrac)
    (t : Nat) (w : BitVec 32) :
    wlogWf σ.wmLog →
    accWf ea 4 →
    wVAmoAq ea σ ws' →
    wlatInterp (GF := GF) σ.wmImg σ.wmLog ⊢
      wlat4 (GF := GF) ea dq t w -∗
      R.monPred_at (viewScl t) -∗
        ⌜wPMem ea σ⌝ ∗
        ⌜∀ j : Nat, j < 4 →
           wflatMem σ.wmImg σ.wmLog (ea + BitVec.ofNat 64 j) = some (nthByte (n := 4) w j)⌝ ∗
        ⌜viewScl t ≤ wsView ws'⌝ ∗
        vwpHold R ws' := by
  intro hwf hacc hQ
  iintro Hi H HR
  unfold wlat4
  icases H with ⟨H0, H1, H2, H3⟩
  icases keepPure (wlatByteFlatGen σ ea 4 dq t _ 0 hwf hacc (by omega)) $$ Hi H0 with
    ⟨%E0, Hi, -⟩
  icases keepPure (wlatByteFlatGen σ ea 4 dq t _ 1 hwf hacc (by omega)) $$ Hi H1 with
    ⟨%E1, Hi, -⟩
  icases keepPure (wlatByteFlatGen σ ea 4 dq t _ 2 hwf hacc (by omega)) $$ Hi H2 with
    ⟨%E2, Hi, -⟩
  ihave %E3 := wlatByteFlatGen σ ea 4 dq t _ 3 hwf hacc (by omega) $$ Hi H3
  have hall : ∀ j : Nat, j < 4 →
      wflatMem σ.wmImg σ.wmLog (ea + BitVec.ofNat 64 j) = some (nthByte (n := 4) w j) ∧
      latestTs σ.wmLog (WeakInterp.accAddr ea j) = t := by
    intro j hj
    rcases j with _ | _ | _ | _ | j
    · exact E0
    · exact E1
    · exact E2
    · exact E3
    · omega
  have hscl : viewScl t ≤ wsView ws' := by
    have := hQ 0 (by omega)
    rw [(hall 0 (by omega)).2] at this
    exact this
  isplitr
  · ipureintro; exact hacc
  isplitr
  · ipureintro; exact fun j hj => (hall j hj).1
  isplitr
  · ipureintro; exact hscl
  iapply vwpHold_intro (viewScl t) R ws' hscl
  iexact HR

/-! ### 5d. `fence pred,succ` -/

theorem wwpFenceDeliver (R : VProp GF) (σ : Wmstate) (ws' : Wstate) :
    wVFence .Barrier_RISCV_rw_rw σ ws' →
    vwpAcq R σ.wmWs ⊢ vwpHold R ws' := by
  intro hQ
  unfold vwpAcq vwpHold
  apply R.monPred_mono
  rw [← wsView_barrier_rw_rw σ.wmWs]
  exact wsView_mono _ _ hQ

/-- `fence` with a pred-R set delivers everything deposited at a SCALAR view the
hart has already read. -/
theorem wwpFenceSclGen (R : VProp GF) (σ : Wmstate) (ws' : Wstate) (t : Nat) (b : barrier_kind) :
    acqPredR b →
    wVFence b σ ws' →
    t ≤ σ.wmWs.wVrOld →
    R.monPred_at (viewScl t) ⊢ vwpHold R ws' := by
  intro hb hQ ht
  unfold vwpHold
  apply R.monPred_mono
  exact Std.IsPreorder.le_trans _ _ _ (viewScl_acqPredR b σ.wmWs t hb ht) (wsView_mono _ _ hQ)

theorem wwpFenceScl (R : VProp GF) (σ : Wmstate) (ws' : Wstate) (t : Nat) :
    wVFence .Barrier_RISCV_rw_rw σ ws' →
    t ≤ σ.wmWs.wVrOld →
    R.monPred_at (viewScl t) ⊢ vwpHold R ws' :=
  wwpFenceSclGen R σ ws' t _ acqPredR_rw_rw

/-- THE ACQUIRE FENCE THE KERNEL ACTUALLY EXECUTES (`fence r,rw` after the
`started` load). -/
theorem wwpFenceSclR (R : VProp GF) (σ : Wmstate) (ws' : Wstate) (t : Nat) :
    wVFence .Barrier_RISCV_r_rw σ ws' →
    t ≤ σ.wmWs.wVrOld →
    R.monPred_at (viewScl t) ⊢ vwpHold R ws' :=
  wwpFenceSclGen R σ ws' t _ acqPredR_r_rw

/-- `fence rw,w` -- the RELEASE fence: no view content beyond `wsLe`. -/
theorem wwpFenceRwW (R : VProp GF) (σ : Wmstate) (ws' : Wstate) :
    wVFence .Barrier_RISCV_rw_w σ ws' →
    vwpHold R σ.wmWs ⊢ vwpHold R ws' :=
  fun hQ => vwpHold_mono R (wsLeTrans (barrierPostLe _ _) hQ)

end leaves

/-! ## 6. Smoke tests: two leaves in a row -/

section smoke
variable {GF : BundledGFunctors} [WeakGS GF]

/-- `sw` ; `fence rw,rw` -- the RELEASE/publication shape. -/
theorem wwpSmokeSwFence (R : VProp GF) (σ0 σ1 : Wmstate) (ws2 : Wstate) (t0 : ExecSt) :
    wsBounded σ0.wmWs σ0.wmLog.length →
    wstepPost σ0 σ1 t0 →
    σ0.wmLog.length + 1 ≤ σ1.wmWs.wVrOld →
    wVFence .Barrier_RISCV_rw_rw σ1 ws2 →
    vwpHold R σ0.wmWs ⊢ vwpHold R ws2 := by
  intro hb _ hrd hQ
  exact (wwpReleaseDeposit R σ0 hb).trans (wwpFenceScl R σ1 ws2 _ hQ hrd)

/-- `amoswap.w.aq` ; `lw` -- the ACQUIRE shape. -/
theorem wwpSmokeAmoLw (R : VProp GF) (σ0 σ1 σ2 : Wmstate) (t1 : ExecSt) (ea la : PAddr)
    (dq : DFrac) (t : Nat) (w lw : BitVec 32) :
    wlogWf σ0.wmLog →
    accWf ea 4 →
    wVAmoAq ea σ0 σ1.wmWs →
    wstepPost σ1 σ2 t1 →
    wlatInterp (GF := GF) σ0.wmImg σ0.wmLog ⊢
      wlat4 (GF := GF) ea dq t w -∗
      (iprop(R ∗ wpt4 (GF := GF) la (DFrac.own 1) lw) : VProp GF).monPred_at (viewScl t) -∗
        ⌜∀ j : Nat, j < 4 →
           wflatMem σ0.wmImg σ0.wmLog (ea + BitVec.ofNat 64 j) = some (nthByte (n := 4) w j)⌝ ∗
        vwpHold R σ2.wmWs ∗ vwpHold (wpt4 (GF := GF) la (DFrac.own 1) lw) σ2.wmWs := by
  intro hwf hacc hQ hp
  iintro Hi Hl HR
  icases wwpAmoswapWAqInv iprop(R ∗ wpt4 (GF := GF) la (DFrac.own 1) lw) σ0 σ1.wmWs ea dq t w
      hwf hacc hQ $$ Hi Hl HR with ⟨-, %hflat, -, Hpay⟩
  icases (vwpHold_sep R (wpt4 (GF := GF) la (DFrac.own 1) lw) σ1.wmWs).mp $$ Hpay with ⟨HR, Hpt⟩
  have hle := wstepPostWsLe σ1 σ2 t1 hp
  isplitr
  · ipureintro; exact hflat
  isplitl [HR]
  · iapply vwpHold_mono R hle; iexact HR
  · iapply vwpHold_mono _ hle; iexact Hpt

end smoke

end Weak
