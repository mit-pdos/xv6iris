/-
Weak: **the per-event lifting rules, BATCHED** (spike S4).

Rocq: `iris/WeakEvLift.v` @ xxvzwolszwmp (1cc222280).

## The Rocq header, in substance

Design: `claude-notes/design/weak-memory-event-granular.md` (the REVISED "expression-resident
monad" section and "reflective batching is MANDATORY"); worklist
`claude-notes/projects/weak-memory-event-lang.md` (deliverable S4).  `WeakExec.wpWrunStep` lifts
ONE INSTRUCTION of `WeakLang`; this file lifts ONE EVENT of `WeakEvLang`, and then provides the
BATCHED interface that is the actual leaf-facing one.  §2 is the SEMANTICS (the core lifting rule
and the arms with no memory content), §3 the REFLECTION (a computable silent stepper with a
once-proven soundness lemma), §4 the PROOF INTERFACE (the n-step batched rule), §5 the RAM
events, §6 the split exclusive pair, §7 the certification adapter (one combinator per event
kind; the residual monad is never named at a call site).

THE STRUCTURAL FINDINGS (S4):
(F1) THE HART HAS NO SPURIOUS ARM (interrupt delivery is the PLIC's wire write): every rule is an
     ordinary deterministic-arm lifting; only the conditional write's retry needs a Löb.
(F2) REDUCIBILITY IS THE ONE HONEST PARTIALITY: each rule SUPPLIES its arm's witness.
(F3) THE FROZEN LOG: (a) the racy load is stated at the READ EVENT's own state, so the
     instruction-atomic `wadm_down` transport (and its frozen-log hypothesis) is DELETED;
     (b) "a load leaves the log alone" holds of the load EVENT; (c) the release deposit is
     re-established at every event by `wsBounded`; (d) older-log facts use `wlogLb` snapshots.
(F4) INTERFERENCE STABILITY: every rule is stated at an ARBITRARY σ satisfying `weakStateInterp`
     and re-establishes it; the rules consume per-hart exclusive resources and the C/D/S
     fragments.  Fail criterion 1 is tested and NOT hit.
(F5) NO INVARIANT SPANS SEVERAL EVENTS: each RAM rule gives a mask-changing callback around ONE
     event.  Fail criterion 2 is NOT hit.
(F8) NO CALL SITE WRITES A RESIDUAL MONAD: the interface is over the cursor `ecur`, total resume
     functions, small projections (`enodeTag`, `ereadReqAt`, …) and once-proven inversions.
(F7, superseded by O2, see deviation 2) Rocq measured the model's fetch to be a PLAIN read and
     derived the fetch rule from the racy load plus never-written text.

## Deviations from Rocq

1. NAMES: the tree's camelCase (map below).  File-qualified: `WeakEvLift.cohLoadPostAtNe`
   (duplicated name, `notes/weak-port-dupnames.json`) and `WeakEvLift.weakStateInterpPin` (the
   unqualified name is `WeakExec`'s Lean-only helper of another statement).  Statement shapes as
   `WeakGhost` deviation 9 (`P -∗ Q -∗ R` ↦ `P ∗ Q ⊢ R`); `EWP e @ ⊤` is spelled
   `ewpTriv (hlc := hlc) (GF := GF) ⊤ e` (`WeakEvAdequacy` deviation 6).  Vocabulary: `M unit` ↦
   `SailM Unit`, `Interface.Next oc k` ↦ `.impure (.ok oc) k`, `Ret u` ↦ `FreeM.pure u`;
   `reg_interp_at (cpu_reg_name c)` ↦ `regInterp c`, `gregs_interp gr` ↦
   `[∗list] c ∈ cpus, regInterp c (gr c)`, `reg_pointsto_at c` ↦ `regPointsTo c`, `<[c := x]> f` ↦
   `updCpu f c x`, `fin_to_nat c` ↦ `c.val`, `N.to_nat n` ↦ `n : Nat`, `acc_addr` ↦
   `WeakInterp.accAddr`, `acc_wf` ↦ `WeakBridge.accWf`, `S (length l)` ↦ `l.length + 1`,
   `tvs.*1/.*2` ↦ `tvs.map Prod.fst/snd`, `DfracDiscarded` ↦ `DFrac.discard`.
2. O2 — THE FETCH (§5c, §7c; `notes/weak-port-o2-design.md` §1.5, owner decisions O2/D2/D3).  The
   Lean model tags fetches `AK_ifetch`, which the weak tier reads as the I-CACHE (WeakEvLang
   deviation 5): admissibility `ifetchOk … (σ.wgitv c) …` at the hart's instruction view (Stage
   B), post-state the IDENTITY.  So `ewpEvFetch`/`ewpEvSeqFetch` take
   `(classify req.access_kind).akIfetch = true` (Rocq: `ak_coh = false ∧ ak_latest = false`) and
   hand the continuation `hartWs c ws` UNCHANGED: Rocq's `efetch_ws`, `efetch_ws_le`,
   `efetch_ws_relp` are DROPPED (their downstream users `WeakEvStarted`, `WeakEvFunnel`,
   `WeakEvWire` read the fetch's view as `ws` itself).  Enabledness: the all-zero
   read is admissible at ANY instruction view, because the text byte is unwritten (`latestTs = 0`
   and `writesInClip`); uniqueness through `ifetchOkWbyteOk` + `etextBytePin`.  `ewpEvLoad`,
   `ewpEvExload`, `ewpEvSeqLoad`, `readOkWbyteOk`: Rocq's `ak_coh = false` is `akIfetch = false`.
   `etextBytePin` drops Rocq's two kind premises: it holds for EVERY access kind
   (`WeakBridge.wbyteOkPinned` with `readPinnedUnwritten`; its i-cache case is the fetch pin).
3. LATER CREDITS: `ewpEvExstore` is stated at `hlc := .hasLC` (`[MachGS .hasLC GF]`).  Its retry
   self-loop forces opening the caller's callback AFTER the step, where only the step's `£ 1` can
   strip the callback's `▷`; iris-lean's `lc_fupd_elim_later` needs `InvGS GF` (=
   `InvGS_gen .hasLC GF`; under `.hasNoLC`, `£ 1` is `True`).  Rocq Iris always has credits.  Every
   other rule (and `ewpEcycleLc`) is hlc-generic; the `WeakEvAdequacy` theorems are hlc-generic,
   so a leaf using `ewpEvExstore` is closed by instantiating them at `.hasLC`.
4. THE REGISTER FOOTPRINT: `D : gset register` ↦ `D : List Register` and `ereg_frame`'s `[∗ set]`
   ↦ `[∗list]` (so `eregFrame c (g.wgregs c) (D c)` IS the `WeakEvAdequacy` package's register
   conjunct).  No `Nodup` premise: a repeated register would be two full cells, refuted by
   `regPointsToNe`.  `eregFrame` is an `abbrev` (the proof mode destructs through it).
   `register_lookup r rs` ↦ `rs r`, `register_set r v rs` ↦ `rs.set r v`.
5. THE REFLECTIVE INTERFACE, at lean-sail's monad: one `esilNode` arm per `Outcome` constructor
   (a model `.error` node is not silent and has `enodeTag` 5; `getCycleCount` answers `(0 : Nat)`,
   as `WeakEvLang`).  `eread_resume (v : Z)` ↦ `ereadResume (v : Nat)` answering
   `BitVec.ofNat (8 * n) v` (Rocq `Z_to_bv`), inverted at `w.toNat` (Rocq `bv_unsigned w`).
   `ewriteResume` and the store rules' continuation answer `.Ok (some true)` (owner decision,
   WeakEvLang deviation 4; Rocq `inl None`).  `eread_req_at n`/`ewrite_req_at n` ↦
   `ereadReqAt n va`/`ewriteReqAt n va` (lean-sail requests are indexed by the VA width too).  The
   write value is `req.value : Option _`, so `ewpEvStore`/`ewpEvExstore`/`ewpEvSeqStore` take `v`
   with `req.value = some v`, and the message is `wwriteMsg (some c.val) … req.pa n v`
   (= WeakEvLang's literal, `wwriteMsgWbytes`).  `ecurLoop` is `noncomputable` (`riscvStep` is).
6. EXTENSIONALITY: Lean has `funext`, so Rocq's pointwise lemmas (`wws_interp_ext`,
   `gregs_interp_ext`, `weak_state_interp_reg_id`/`_ptwise`/`_store_id`) keep their statements and
   are proven through the Lean-only `weakStateInterpCongr` (the interpretation reads exactly seven
   fields: not `wgib`, nor the Lean-only `wgitv`/`wgrt`).  `weakStateInterpPtwise`'s state is
   `{ σ with wgregs := gr, wgws := f, wgib := ib }`.  The σ-effect of a silent node is closed by
   `esilSigmaShape` (Rocq: one `weak_state_interp_ptwise` per shape).
7. STAGE B BARRIER: `WeakEvLang`'s barrier arm writes `ewgBar` (data view AND instruction view).
   `ewpEvBarrier`'s statement is Rocq's (the hart's data view); the instruction view is invisible
   to the interpretation (`weakStateInterpBar`, `rfl`).
8. `ewp_ev_sil_rtc`'s induction from the first step is `rtc_ind_l` (`MachCSL.Rel` deviation 1).

**File-qualified names:** `WeakEvLift.cohLoadPostAtNe`, `WeakEvLift.weakStateInterpPin`.

Q7 (owner ruling, `notes/weak-port-q7-sfence.md` route (a), Lean-only): the announce node's σ-shape is `ewgIbws σ c v (annPost n w ws)` (`WeakEvLang`), so `esilSigma`'s announce disjunct quantifies the word: `∃ v n w, σ' = ewgIbws σ c v (annPost n w (σ.wgws c))`.

**Rocq → Lean name map.**  `store_fold_map` `storeFoldMap`, `coh_store_fold_nat`
`cohStoreFoldNat`, `coh_store_post_run_moved` `cohStorePostRunMoved`, `store_fold_d_map`
`storeFoldDMap`, `coh_store_post_d_ne` `cohStorePostDNe`, `coh_store_fold_d_nat`
`cohStoreFoldDNat`, `coh_store_post_run_d_moved` `cohStorePostRunDMoved`, `coh_load_post_at_ne`
`WeakEvLift.cohLoadPostAtNe`, `coh_load_fold_moved` `cohLoadFoldMoved`, `coh_load_post_run_moved`
`cohLoadPostRunMoved`, `load_post_fold_relp_ev` `loadPostFoldRelpEv`, `load_post_run_relp_ev`
`loadPostRunRelpEv`, `wws_interp_ext` `wwsInterpExt`, `wws_interp_acc_at` `wwsInterpAccAt`,
`gregs_interp_ext` `gregsInterpExt`, `weak_state_interp_reg_id` `weakStateInterpRegId`,
`weak_state_interp_pin` `WeakEvLift.weakStateInterpPin`, `weak_state_interp_regs`
`weakStateInterpRegs`, `weak_state_interp_mem` `weakStateInterpMem`, `weak_state_interp_ptwise`
`weakStateInterpPtwise`, `weak_state_interp_store_id` `weakStateInterpStoreId`,
`weak_state_interp_rmw` `weakStateInterpRmw`, `weak_state_interp_ib` `weakStateInterpIb`,
`weak_state_interp_ibws` `weakStateInterpIbws`, `ewp_ecycle` `ewpEcycle`, `ewp_ecycle_lc`
`ewpEcycleLc`, `ewp_eloop` `ewpEloop`, `ewp_ev_ret` `ewpEvRet`, `ewp_ev_fence_fire`
`ewpEvFenceFire`, `esil_node` `esilNode`, `erun_silent` `erunSilent`, `esilD` `esilD`,
`erun_silent_sound` `erunSilentSound`, `esil_sigma` `esilSigma`, `esil_node_ecycle`
`esilNodeEcycle`, `esil_node_ecycle_inv` `esilNodeEcycleInv`, `esil_sigma_depmove`
`esilSigmaDepmove`, `esil_sigma_log/img/regs` `esilSigmaLog/Img/Regs`, `ecur` `ecur`, `esil`
`esil`, `eread_resume` `ereadResume`, `ewrite_resume` `ewriteResume`, `ebar_resume`
`ebarResume`, `ecur_loop/read/write/bar` `ecurLoop/Read/Write/Bar`, `enode_tag` `enodeTag`,
`eread_req_at` `ereadReqAt`, `ewrite_req_at` `ewriteReqAt`, `ebar_at` `ebarAt`, `enode_tag_ret`
`enodeTagRet`, `eread_req_at_inv` `ereadReqAtInv`, `ewrite_req_at_inv` `ewriteReqAtInv`,
`ebar_at_inv` `ebarAtInv`, `ereg_frame` `eregFrame`, `reg_agree_on` `regAgreeOn`,
`ereg_frame_ext/agree/update` `eregFrameExt/Agree/Update`, `esil_node_agree` `esilNodeAgree`,
`ewp_ev_sil_node` `ewpEvSilNode`, `ewp_ev_sil_rtc` `ewpEvSilRtc`, `ewp_ev_batch` `ewpEvBatch`,
`read_ok_wbyte_ok` `readOkWbyteOk`, `ewp_ev_store` `ewpEvStore`, `ewp_ev_load` `ewpEvLoad`,
`etext` `etext`, `etext_persistent` `etext_persistent`, `etext_word` `etextWord`,
`etext_word_persistent` `etextWord_persistent`, `etext_byte_pin` `etextBytePin`, `ewp_ev_fetch`
`ewpEvFetch`, `eexl_ok` `eexlOk`, `eexl_ws` `eexlWs`, `ewp_ev_exload` `ewpEvExload`,
`ewp_ev_exstore` `ewpEvExstore`, `efence_apply_coh` `efenceApplyCoh`, `efence_apply_bounded`
`efenceApplyBounded`, `ewp_ev_barrier` `ewpEvBarrier`, `ewp_ev_seq_ret/barrier/store/load/fetch`
`ewpEvSeqRet/Barrier/Store/Load/Fetch`.
Lean-only: `updCpuSelf`, `weakStateInterpCongr`, `weakStateInterpBar`, `weakStateInterpWs`,
`nvHartOfCohEq`, `appNilOwn`, `memZipRunAddr`, `esilSigmaBounded`, `esilSigmaShape`,
`regPointsToNe`, `eregFrameNotMem`, `esilNodeRegs` (the register half Rocq inlines in
`ewp_ev_sil_node`), `storeMsgOwn`, `storeLogWf`, `storeNvHart`, `storeBounded` (the store
closing Rocq inlines twice), `etextWordLatest`, `ifetchOkWbyteOk`.

**Dropped:** `efetch_ws`, `efetch_ws_le`, `efetch_ws_relp` (deviation 2: under O2 the fetch moves
no view; uses: `WeakEvStarted`, `WeakEvFunnel`, `WeakEvWire`, which get `ws` itself).

**Statements checked** (by hand, against Rocq): all; the changed ones are the deviations above.
-/
import Weak.WeakEvAdequacy
import Weak.WeakBridge
import Iris.ProgramLogic.Lifting

namespace Weak

open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode Iris.Std
open MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D

/-! ## 0. Pure facts about the store and load folds

"The only coherence floors a store moves are the ones inside its window." -/

theorem storeFoldMap (rl : Bool) (t : Nat) (base : Int) (l : List Nat) (ws : Wstate) :
    (l.map (fun j : Nat => base + (j : Int))).foldl (fun w a0 => storePost w rl a0 t) ws =
      l.foldl (fun w j => storePost w rl (base + (j : Int)) t) ws := by
  induction l generalizing ws with
  | nil => rfl
  | cons j l ih => exact ih _

theorem cohStoreFoldNat (rl : Bool) (t : Nat) (base : Int) (l : List Nat) (ws : Wstate) (a : Int) :
    coh ws a < coh (l.foldl (fun w j => storePost w rl (base + (j : Int)) t) ws) a →
    ∃ j : Nat, j ∈ l ∧ a = base + (j : Int) := by
  induction l generalizing ws with
  | nil => intro h; exact (Nat.lt_irrefl _ h).elim
  | cons j l ih =>
    intro hc
    by_cases he : a = base + (j : Int)
    · exact ⟨j, List.mem_cons_self, he⟩
    · obtain ⟨j', hj', he'⟩ := ih _ (by rw [cohStorePostNe ws rl _ t a he]; exact hc)
      exact ⟨j', List.mem_cons_of_mem _ hj', he'⟩

theorem cohStorePostRunMoved (ws : Wstate) (rl : Bool) (base : Int) (cnt t : Nat) (a : Int) :
    coh ws a < coh (storePostRun ws rl base cnt t) a →
    ∃ j : Nat, j < cnt ∧ a = base + (j : Int) := by
  intro hc
  simp only [storePostRun, ctrlPostCoh, storePostBytes, storeFoldMap] at hc
  obtain ⟨j, hj, he⟩ := cohStoreFoldNat rl t base _ ws a hc
  exact ⟨j, by rw [List.mem_range'_1] at hj; omega, he⟩

/-- D3-2: THE COHERENCE FLOORS ARE DEPENDENCY-BLIND (the dependency-carrying twins). -/
theorem storeFoldDMap (rl : Bool) (vf t : Nat) (base : Int) (l : List Nat) (ws : Wstate) :
    (l.map (fun j : Nat => base + (j : Int))).foldl (fun w a0 => storePostD w rl vf a0 t) ws =
      l.foldl (fun w j => storePostD w rl vf (base + (j : Int)) t) ws := by
  induction l generalizing ws with
  | nil => rfl
  | cons j l ih => exact ih _

theorem cohStorePostDNe (ws : Wstate) (rl : Bool) (vf : Nat) (a' : Int) (t : Nat) (a : Int) :
    a ≠ a' → coh (storePostD ws rl vf a' t) a = coh ws a := by
  intro h; simp only [storePostD, coh, lookupInsertNe (Ne.symm h)]

theorem cohStoreFoldDNat (rl : Bool) (vf t : Nat) (base : Int) (l : List Nat) (ws : Wstate)
    (a : Int) :
    coh ws a < coh (l.foldl (fun w j => storePostD w rl vf (base + (j : Int)) t) ws) a →
    ∃ j : Nat, j ∈ l ∧ a = base + (j : Int) := by
  induction l generalizing ws with
  | nil => intro h; exact (Nat.lt_irrefl _ h).elim
  | cons j l ih =>
    intro hc
    by_cases he : a = base + (j : Int)
    · exact ⟨j, List.mem_cons_self, he⟩
    · obtain ⟨j', hj', he'⟩ := ih _ (by rw [cohStorePostDNe ws rl vf _ t a he]; exact hc)
      exact ⟨j', List.mem_cons_of_mem _ hj', he'⟩

theorem cohStorePostRunDMoved (ws : Wstate) (rl : Bool) (vaddr vdata : Nat) (base : Int)
    (cnt t : Nat) (a : Int) :
    coh ws a < coh (storePostRunD ws rl vaddr vdata base cnt t) a →
    ∃ j : Nat, j < cnt ∧ a = base + (j : Int) := by
  intro hc
  simp only [storePostRunD, ctrlPostCoh, storePostBytesD, storeRunAs, storeFoldDMap] at hc
  obtain ⟨j, hj, he⟩ := cohStoreFoldDNat rl (max vaddr vdata) t base _ ws a hc
  exact ⟨j, by rw [List.mem_range'_1] at hj; omega, he⟩

/-- ... and the LOAD twin: a load only moves the coherence floors of the bytes it read
(file-qualified: duplicated name, WeakMem/WeakCert). -/
theorem WeakEvLift.cohLoadPostAtNe (ws : Wstate) (aq : Bool) (vpre : Nat) (a' : Int) (t : Nat)
    (a : Int) : a ≠ a' → coh (loadPostAt ws aq vpre a' t) a = coh ws a :=
  fun h => Weak.cohLoadPostAtNe ws aq vpre a' t a h

theorem cohLoadFoldMoved (aq : Bool) (vpre : Nat) (ats : List (Int × Nat)) (ws : Wstate) (a : Int) :
    coh ws a < coh (ats.foldl (fun w at_ => loadPostAt w aq vpre at_.1 at_.2) ws) a →
    ∃ p, p ∈ ats ∧ a = p.1 := by
  induction ats generalizing ws with
  | nil => intro h; exact (Nat.lt_irrefl _ h).elim
  | cons p ats ih =>
    intro hc
    by_cases he : a = p.1
    · exact ⟨p, List.mem_cons_self, he⟩
    · obtain ⟨p', hp', he'⟩ :=
        ih _ (by rw [WeakEvLift.cohLoadPostAtNe ws aq vpre p.1 p.2 a he]; exact hc)
      exact ⟨p', List.mem_cons_of_mem _ hp', he'⟩

/-- The address of every entry of the zipped run (Lean-only helper). -/
theorem memZipRunAddr (base : Int) (ts : List Nat) :
    ∀ (k : Nat) (p : Int × Nat),
      p ∈ List.zipWith (fun (j : Nat) t => (base + (j : Int), t)) (List.range' k ts.length) ts →
      ∃ j : Nat, k ≤ j ∧ j < k + ts.length ∧ p.1 = base + (j : Int) := by
  induction ts with
  | nil => intro k p hp; simp at hp
  | cons t l ih =>
    intro k p hp
    rw [List.length_cons, List.range'_succ, List.zipWith_cons_cons, List.mem_cons] at hp
    rcases hp with rfl | hp
    · exact ⟨k, Nat.le_refl _, by simp, rfl⟩
    · obtain ⟨j, h1, h2, h3⟩ := ih (k + 1) p hp
      exact ⟨j, by omega, by simp only [List.length_cons]; omega, h3⟩

theorem cohLoadPostRunMoved (ws : Wstate) (aq : Bool) (base : Int) (ts : List Nat) (a : Int) :
    coh ws a < coh (loadPostRun ws aq base ts) a →
    ∃ j : Nat, j < ts.length ∧ a = base + (j : Int) := by
  intro hc
  simp only [loadPostRun, ctrlPostCoh, loadPostBytes] at hc
  obtain ⟨p, hp, he⟩ := cohLoadFoldMoved aq (loadVpre ws aq) _ ws a hc
  obtain ⟨j, -, hj, hpj⟩ := memZipRunAddr base ts 0 p hp
  exact ⟨j, by omega, he.trans hpj⟩

/-- ... and the `wRelp` flag a load leaves alone. -/
theorem loadPostFoldRelpEv (aq : Bool) (vpre : Nat) (ats : List (Int × Nat)) :
    ∀ ws : Wstate,
      (ats.foldl (fun w at_ => loadPostAt w aq vpre at_.1 at_.2) ws).wRelp = ws.wRelp := by
  induction ats with
  | nil => intro ws; rfl
  | cons p l ih => intro ws; simp only [List.foldl_cons]; rw [ih]; rfl

theorem loadPostRunRelpEv (ws : Wstate) (aq : Bool) (base : Int) (ts : List Nat) :
    (loadPostRun ws aq base ts).wRelp = ws.wRelp := by
  simp only [loadPostRun, ctrlPostRelp, loadPostBytes]
  exact loadPostFoldRelpEv aq _ _ ws

/-! ## 1. Opening `weakStateInterp` at one hart -/

/-- Updating a per-hart map at its own value is the identity (Lean-only helper). -/
theorem updCpuSelf {α : Type} (f : CPU → α) (c : CPU) : updCpu f c (f c) = f := by
  funext x
  by_cases h : x = c
  · subst h; simp [updCpu]
  · simp [updCpu, h]

section interp

variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [WeakGS GF]

theorem wwsInterpExt (f g : CPU → Wstate) :
    (∀ c, f c = g c) → wwsInterp (GF := GF) f ⊣⊢ wwsInterp g := by
  intro h
  have e : f = g := funext h
  subst e
  exact .rfl

/-- The view-cell twin of `regsInterpAcc` (it IS WeakGhost's `wwsInterpAcc`). -/
theorem wwsInterpAccAt (c : CPU) (f : CPU → Wstate) :
    wwsInterp (GF := GF) f ⊢
      wwsAuth c (f c) ∗ ∀ ws' : Wstate, wwsAuth c ws' -∗ wwsInterp (updCpu f c ws') :=
  wwsInterpAcc c f

theorem gregsInterpExt (gr gr' : CPU → RegFile) :
    (∀ c, gr c = gr' c) →
    iprop([∗list] c ∈ cpus, regInterp (hlc := hlc) (GF := GF) c (gr c)) ⊣⊢
      iprop([∗list] c ∈ cpus, regInterp (hlc := hlc) (GF := GF) c (gr' c)) := by
  intro h
  have e : gr = gr' := funext h
  subst e
  exact .rfl

/-- THE STATE-INTERPRETATION CONGRUENCE (Lean-only): `weakStateInterp` reads seven fields
and nothing else (not `wgib`, `wgitv`, `wgrt`). -/
theorem weakStateInterpCongr (σ σ' : WGState) (h1 : σ.wgregs = σ'.wgregs)
    (h2 : σ.wgimg = σ'.wgimg) (h3 : σ.wglog = σ'.wglog) (h4 : σ.wgws = σ'.wgws)
    (h5 : σ.wgdev = σ'.wgdev) (h6 : σ.wggen = σ'.wggen) (h7 : σ.wgpow = σ'.wgpow) :
    weakStateInterp (hlc := hlc) (GF := GF) σ = weakStateInterp (hlc := hlc) (GF := GF) σ' := by
  simp only [weakStateInterp, wgenPin, h1, h2, h3, h4, h5, h6, h7]

/-- A `regRead`-shaped register write-back is the identity. -/
theorem weakStateInterpRegId (σ : WGState) (c : CPU) :
    weakStateInterp (hlc := hlc) (GF := GF) (ewgReg σ c (σ.wgregs c)) ⊢
      weakStateInterp (hlc := hlc) (GF := GF) σ := by
  rw [weakStateInterpCongr (ewgReg σ c (σ.wgregs c)) σ (updCpuSelf _ _) rfl rfl rfl rfl rfl rfl]

theorem WeakEvLift.weakStateInterpPin (σ : WGState) :
    weakStateInterp (hlc := hlc) (GF := GF) σ ⊢ ⌜σ.wgpow = true ∧ σ.wggen = 0⌝ := by
  unfold weakStateInterp
  iintro ⟨%h, -⟩
  ipureintro
  exact h

/-- THE REGISTER CONJUNCT. -/
theorem weakStateInterpRegs (σ : WGState) (c : CPU) :
    weakStateInterp (hlc := hlc) (GF := GF) σ ⊢
      regInterp c (σ.wgregs c) ∗
        ∀ rs' : RegFile, regInterp c rs' -∗ weakStateInterp (hlc := hlc) (GF := GF) (ewgReg σ c rs') := by
  unfold weakStateInterp
  iintro ⟨%Hpin, %Hbnd, %Hnv, %Hwf, Hgr, Hdev, Hlog, Hlat, Hws⟩
  icases regsInterpAcc c σ.wgregs $$ Hgr with ⟨Hri, Hcl⟩
  iframe Hri
  iintro %rs' Hrs'
  dsimp only [ewgReg]
  isplitr
  · ipureintro; exact Hpin
  isplitr
  · ipureintro; exact Hbnd
  isplitr
  · ipureintro; exact Hnv
  isplitr
  · ipureintro; exact Hwf
  isplitl [Hcl Hrs']
  · iapply Hcl $$ %rs' Hrs'
  iframe Hdev Hlog Hlat Hws

/-- THE MEMORY CONJUNCTS: the log authority, the latest-write map and this hart's view cell, the
three machine invariants handed out and taken back at an `ewgStore` shape. -/
theorem weakStateInterpMem (σ : WGState) (c : CPU) :
    weakStateInterp (hlc := hlc) (GF := GF) σ ⊢
      ⌜∀ c' : CPU, wsBounded (σ.wgws c') σ.wglog.length⌝ ∗
      ⌜noViolation σ.wglog σ.wgws⌝ ∗ ⌜wlogWf σ.wglog⌝ ∗
      wlogAuth (GF := GF) σ.wglog ∗ wlatInterp (GF := GF) σ.wgimg σ.wglog ∗
      wwsAuth (GF := GF) c (σ.wgws c) ∗
      (∀ (ws' : Wstate) (lg' : List Wmsg),
        ⌜σ.wglog.length ≤ lg'.length⌝ -∗ ⌜wsBounded ws' lg'.length⌝ -∗ ⌜nvHart lg' c ws'⌝ -∗
        ⌜∃ ms, lg' = σ.wglog ++ ms ∧ ∀ m, m ∈ ms → m.wmTid = some c.val⌝ -∗
        ⌜wlogWf lg'⌝ -∗
        wlogAuth (GF := GF) lg' -∗ wlatInterp (GF := GF) σ.wgimg lg' -∗ wwsAuth (GF := GF) c ws' -∗
        weakStateInterp (hlc := hlc) (GF := GF) (ewgStore σ c ws' lg')) := by
  unfold weakStateInterp
  iintro ⟨%Hpin, %Hbnd, %Hnv, %Hwf, Hgr, Hdev, Hlog, Hlat, Hws⟩
  icases wwsInterpAcc c σ.wgws $$ Hws with ⟨Hwsc, Hwscl⟩
  isplitr
  · ipureintro; exact Hbnd
  isplitr
  · ipureintro; exact Hnv
  isplitr
  · ipureintro; exact Hwf
  iframe Hlog Hlat Hwsc
  iintro %ws' %lg' %Hlen %Hb' %Hnvh %Hown %Hwf' Hlog Hlat Hwsc
  dsimp only [ewgStore]
  isplitr
  · ipureintro; exact Hpin
  isplitr
  · ipureintro
    intro c0
    show wsBounded (updCpu σ.wgws c ws' c0) lg'.length
    by_cases hc : c0 = c
    · subst hc; rw [gwsInsertEq]; exact Hb'
    · rw [gwsInsertNe _ _ _ _ hc]; exact wsBoundedMono _ _ _ (Hbnd c0) Hlen
  isplitr
  · ipureintro
    obtain ⟨ms, hms, hown⟩ := Hown
    show noViolation lg' (updCpu σ.wgws c ws')
    rw [hms]
    apply noViolationStep σ.wglog ms σ.wgws _ c Hnv Hbnd hown
    · intro c0 hne; exact gwsInsertNe _ _ _ _ hne
    · rw [gwsInsertEq, ← hms]; exact Hnvh
  isplitr
  · ipureintro; exact Hwf'
  iframe Hgr Hdev Hlog Hlat
  iapply Hwscl $$ %ws' Hwsc

/-- D3-2: THE POINTWISE REBUILD.  A σ whose register/view maps agree pointwise and whose bits
differ arbitrarily carries the same interpretation. -/
theorem weakStateInterpPtwise (σ : WGState) (gr : CPU → RegFile) (f : CPU → Wstate)
    (ib : CPU → Ibch) :
    (∀ c, gr c = σ.wgregs c) → (∀ c, f c = σ.wgws c) →
    weakStateInterp (hlc := hlc) (GF := GF) σ ⊢
      weakStateInterp (hlc := hlc) (GF := GF) { σ with wgregs := gr, wgws := f, wgib := ib } := by
  intro hg hf
  rw [weakStateInterpCongr σ { σ with wgregs := gr, wgws := f, wgib := ib }
    (funext hg).symm rfl rfl (funext hf).symm rfl rfl rfl]

/-- THE IDENTITY RE-CLOSE. -/
theorem weakStateInterpStoreId (σ : WGState) (c : CPU) :
    weakStateInterp (hlc := hlc) (GF := GF) (ewgStore σ c (σ.wgws c) σ.wglog) ⊢
      weakStateInterp (hlc := hlc) (GF := GF) σ := by
  rw [weakStateInterpCongr (ewgStore σ c (σ.wgws c) σ.wglog) σ rfl rfl rfl (updCpuSelf _ _) rfl rfl
    rfl]

/-- The combined accessor: registers, views and the log together, closing at `ewgRegwslog`. -/
theorem weakStateInterpRmw (σ : WGState) (c : CPU) :
    weakStateInterp (hlc := hlc) (GF := GF) σ ⊢
      ⌜∀ c' : CPU, wsBounded (σ.wgws c') σ.wglog.length⌝ ∗
      ⌜noViolation σ.wglog σ.wgws⌝ ∗ ⌜wlogWf σ.wglog⌝ ∗
      regInterp c (σ.wgregs c) ∗
      wlogAuth (GF := GF) σ.wglog ∗ wlatInterp (GF := GF) σ.wgimg σ.wglog ∗
      wwsAuth (GF := GF) c (σ.wgws c) ∗
      (∀ (rs' : RegFile) (ws' : Wstate) (lg' : List Wmsg),
        ⌜σ.wglog.length ≤ lg'.length⌝ -∗ ⌜wsBounded ws' lg'.length⌝ -∗ ⌜nvHart lg' c ws'⌝ -∗
        ⌜∃ ms, lg' = σ.wglog ++ ms ∧ ∀ m, m ∈ ms → m.wmTid = some c.val⌝ -∗
        ⌜wlogWf lg'⌝ -∗
        regInterp c rs' -∗
        wlogAuth (GF := GF) lg' -∗ wlatInterp (GF := GF) σ.wgimg lg' -∗ wwsAuth (GF := GF) c ws' -∗
        weakStateInterp (hlc := hlc) (GF := GF) (ewgRegwslog σ c rs' ws' lg')) := by
  unfold weakStateInterp
  iintro ⟨%Hpin, %Hbnd, %Hnv, %Hwf, Hgr, Hdev, Hlog, Hlat, Hws⟩
  icases regsInterpAcc c σ.wgregs $$ Hgr with ⟨Hri, Hgrcl⟩
  icases wwsInterpAcc c σ.wgws $$ Hws with ⟨Hwsc, Hwscl⟩
  isplitr
  · ipureintro; exact Hbnd
  isplitr
  · ipureintro; exact Hnv
  isplitr
  · ipureintro; exact Hwf
  iframe Hri Hlog Hlat Hwsc
  iintro %rs' %ws' %lg' %Hlen %Hb' %Hnvh %Hown %Hwf' Hrs Hlog Hlat Hwsc
  dsimp only [ewgRegwslog]
  isplitr
  · ipureintro; exact Hpin
  isplitr
  · ipureintro
    intro c0
    show wsBounded (updCpu σ.wgws c ws' c0) lg'.length
    by_cases hc : c0 = c
    · subst hc; rw [gwsInsertEq]; exact Hb'
    · rw [gwsInsertNe _ _ _ _ hc]; exact wsBoundedMono _ _ _ (Hbnd c0) Hlen
  isplitr
  · ipureintro
    obtain ⟨ms, hms, hown⟩ := Hown
    show noViolation lg' (updCpu σ.wgws c ws')
    rw [hms]
    apply noViolationStep σ.wglog ms σ.wgws _ c Hnv Hbnd hown
    · intro c0 hne; exact gwsInsertNe _ _ _ _ hne
    · rw [gwsInsertEq, ← hms]; exact Hnvh
  isplitr
  · ipureintro; exact Hwf'
  isplitl [Hgrcl Hrs]
  · iapply Hgrcl $$ %rs' Hrs
  iframe Hdev Hlog Hlat
  iapply Hwscl $$ %ws' Hwsc

end interp

/-! ## 2. The core lifting rule, and the arms with no memory content -/

section core

variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [WeakGS GF]

/-- D3, THE INVISIBILITY LEMMA: `weakStateInterp` does not read the announced bits. -/
theorem weakStateInterpIb (σ : WGState) (c : CPU) (v : Ibch) :
    weakStateInterp (hlc := hlc) (GF := GF) (ewgIb σ c v) = weakStateInterp (hlc := hlc) (GF := GF) σ :=
  rfl

/-- ... and at the combined instruction-start shape only the VIEW half is visible. -/
theorem weakStateInterpIbws (σ : WGState) (c : CPU) (v : Ibch) (ws : Wstate) :
    weakStateInterp (hlc := hlc) (GF := GF) (ewgIbws σ c v ws) =
      weakStateInterp (hlc := hlc) (GF := GF) (ewgStore σ c ws σ.wglog) :=
  rfl

/-- O2 Stage B (Lean-only): the barrier shape's instruction view is invisible too. -/
theorem weakStateInterpBar (σ : WGState) (c : CPU) (ws : Wstate) (itv : Nat) :
    weakStateInterp (hlc := hlc) (GF := GF) (ewgBar σ c ws itv) =
      weakStateInterp (hlc := hlc) (GF := GF) (ewgStore σ c ws σ.wglog) :=
  rfl

/-- `ewgWs` is the log-preserving `ewgStore` (Lean-only). -/
theorem weakStateInterpWs (σ : WGState) (c : CPU) (ws : Wstate) :
    weakStateInterp (hlc := hlc) (GF := GF) (ewgWs σ c ws) =
      weakStateInterp (hlc := hlc) (GF := GF) (ewgStore σ c ws σ.wglog) :=
  rfl

/-- THE CORE LIFTING RULE for the cycle expression. -/
theorem ewpEcycle (gen : Nat) (c : CPU) (m : SailM Unit) (fn : Option (Bool × Bool × Bool × Bool)) :
    gen = 0 →
    (∀ σ : WGState, weakStateInterp (hlc := hlc) (GF := GF) σ ={⊤,∅}=∗
      ⌜∃ e' σ', ecycleStep gen σ c m fn e' σ'⌝ ∗
      ▷ (∀ e' σ', ⌜ecycleStep gen σ c m fn e' σ'⌝ ={∅,⊤}=∗
          weakStateInterp (hlc := hlc) (GF := GF) σ' ∗ ewpTriv (hlc := hlc) (GF := GF) ⊤ e')) ⊢
    ewpTriv (hlc := hlc) (GF := GF) ⊤ (ECycle gen c m fn) := by
  intro hgen
  iintro H
  unfold ewpTriv
  iapply wp_lift_step rfl
  iintro %σ %ns %obs %obs' %nt Hσ
  rw [weakStateInterpEq]
  icases weakStateInterpPin σ $$ Hσ with ⟨%Hpin, Hσ⟩
  have hlive : ethreadLive σ gen := ⟨Hpin.1, by rw [hgen]; exact Hpin.2⟩
  imod H $$ %σ Hσ with ⟨%Hred, Hk⟩
  imodintro
  isplitr
  · ipureintro
    obtain ⟨e', σ', hs⟩ := Hred
    exact ⟨[], e', σ', [], rfl, rfl, Or.inl ⟨hlive, hs⟩⟩
  inext
  iintro %e₂ %σ₂ %eₜ %Hstep _
  obtain ⟨_, rfl, harm⟩ := eprimStepCycleInv gen c m fn σ obs e₂ σ₂ eₜ Hstep
  rcases harm with ⟨_, hcy⟩ | ⟨hnl, _⟩
  case inr => exact absurd hlive hnl
  imod Hk $$ %e₂ %σ₂ %hcy with ⟨Hσ', HWP⟩
  imodintro
  rw [weakStateInterpEq]
  isplitl [Hσ']
  · iexact Hσ'
  isplitl [HWP]
  · iexact HWP
  · exact BigSepL.bigSepL_nil_intro

/-- THE SAME RULE, HANDING THE STEP'S LATER CREDIT TO THE CONTINUATION. -/
theorem ewpEcycleLc (gen : Nat) (c : CPU) (m : SailM Unit)
    (fn : Option (Bool × Bool × Bool × Bool)) :
    gen = 0 →
    (∀ σ : WGState, weakStateInterp (hlc := hlc) (GF := GF) σ ={⊤,∅}=∗
      ⌜∃ e' σ', ecycleStep gen σ c m fn e' σ'⌝ ∗
      ▷ (∀ e' σ', ⌜ecycleStep gen σ c m fn e' σ'⌝ -∗ £ 1 ={∅,⊤}=∗
          weakStateInterp (hlc := hlc) (GF := GF) σ' ∗ ewpTriv (hlc := hlc) (GF := GF) ⊤ e')) ⊢
    ewpTriv (hlc := hlc) (GF := GF) ⊤ (ECycle gen c m fn) := by
  intro hgen
  iintro H
  unfold ewpTriv
  iapply wp_lift_step rfl
  iintro %σ %ns %obs %obs' %nt Hσ
  rw [weakStateInterpEq]
  icases weakStateInterpPin σ $$ Hσ with ⟨%Hpin, Hσ⟩
  have hlive : ethreadLive σ gen := ⟨Hpin.1, by rw [hgen]; exact Hpin.2⟩
  imod H $$ %σ Hσ with ⟨%Hred, Hk⟩
  imodintro
  isplitr
  · ipureintro
    obtain ⟨e', σ', hs⟩ := Hred
    exact ⟨[], e', σ', [], rfl, rfl, Or.inl ⟨hlive, hs⟩⟩
  inext
  iintro %e₂ %σ₂ %eₜ %Hstep Hlc
  obtain ⟨_, rfl, harm⟩ := eprimStepCycleInv gen c m fn σ obs e₂ σ₂ eₜ Hstep
  rcases harm with ⟨_, hcy⟩ | ⟨hnl, _⟩
  case inr => exact absurd hlive hnl
  imod Hk $$ %e₂ %σ₂ %hcy Hlc with ⟨Hσ', HWP⟩
  imodintro
  rw [weakStateInterpEq]
  isplitl [Hσ']
  · iexact Hσ'
  isplitl [HWP]
  · iexact HWP
  · exact BigSepL.bigSepL_nil_intro

/-- No foreign message, no floor move: the closing obligations of a log-preserving step whose
view move leaves every `coh` alone (Lean-only helper). -/
theorem nvHartOfCohEq (log : List Wmsg) (c : CPU) (ws ws' : Wstate) :
    nvHart log c ws → (∀ a, coh ws' a = coh ws a) → nvHart log c ws' :=
  fun h hc => nvHartCohStep log c ws ws' h (fun a hlt => absurd hlt (by rw [hc a]; omega))

theorem appNilOwn (log : List Wmsg) (c : CPU) :
    ∃ ms, log = log ++ ms ∧ ∀ m, m ∈ ms → m.wmTid = some c.val :=
  ⟨[], (List.append_nil _).symm, fun _ hm => by simp at hm⟩

/-- THE BOUNDARY: `ELoop` fetches a fresh instruction, and it IS THE RESET POINT (`instrPost`). -/
theorem ewpEloop (gen : Nat) (c : CPU) (ws : Wstate) :
    gen = 0 →
    hartWs (GF := GF) c ws ∗
      ▷ (∀ tick : Bool, hartWs (GF := GF) c (instrPost ws) -∗
          ewpTriv (hlc := hlc) (GF := GF) ⊤ (ECycle gen c (riscvStep tick) none)) ⊢
    ewpTriv (hlc := hlc) (GF := GF) ⊤ (ELoop gen c) := by
  intro hgen
  iintro ⟨Hws, H⟩
  iapply ewpEcycle gen c (FreeM.pure ()) none hgen
  iintro %σ Hσ
  icases weakStateInterpMem σ c $$ Hσ with ⟨%Hbnd, %Hnv, %Hwf, Hlog, Hlat, Hwsa, Hcl⟩
  ihave ⟨%hws, Hwsa, Hws⟩ := persistent_entails_right (hartWsAgree c (σ.wgws c) ws) $$ [Hwsa Hws]
  · iframe Hwsa Hws
  subst hws
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro Hmask
  isplitr
  · ipureintro
    exact ⟨_, _, false, rfl, rfl⟩
  inext
  iintro %e' %σ' %hcy
  obtain ⟨tick, rfl, rfl⟩ := hcy
  imod Hmask
  imod hartWsUpdate c (σ.wgws c) (σ.wgws c) (instrPost (σ.wgws c)) $$ [$Hwsa $Hws] with ⟨Hwsa, Hws⟩
  imodintro
  isplitl [Hcl Hlog Hlat Hwsa]
  · rw [weakStateInterpIbws]
    iapply Hcl $$ %(instrPost (σ.wgws c)) %σ.wglog %(Nat.le_refl _)
      %(instrPostBounded _ _ (Hbnd c))
      %(nvHartOfCohEq _ c _ _ (noViolationHart _ _ c Hnv)
        (fun a => wsDepmoveCoh _ _ a (instrPostDepmove _)))
      %(appNilOwn σ.wglog c) %Hwf Hlog Hlat Hwsa
  · iapply H $$ %tick Hws

/-- THE INSTRUCTION END: `pure u` at `fn = none` IS the boundary value (no step, no `▷`). -/
theorem ewpEvRet (gen : Nat) (c : CPU) (u : Unit) :
    gen = 0 →
    ewpTriv (hlc := hlc) (GF := GF) ⊤ (ELoop gen c) ⊢
      ewpTriv (hlc := hlc) (GF := GF) ⊤ (ECycle gen c (FreeM.pure u) none) := by
  intro _
  cases u
  exact .rfl

/-- THE PARKED FENCE FIRING — the only arm enabled while `fn ≠ none` (D5). -/
theorem ewpEvFenceFire (gen : Nat) (c : CPU) (m : SailM Unit) (pr pw sr sw : Bool) (ws : Wstate) :
    gen = 0 →
    hartWs (GF := GF) c ws ∗
      ▷ (hartWs (GF := GF) c (Weak.fencePost ws pr pw sr sw) -∗
          ewpTriv (hlc := hlc) (GF := GF) ⊤ (ECycle gen c m none)) ⊢
    ewpTriv (hlc := hlc) (GF := GF) ⊤ (ECycle gen c m (some (pr, pw, sr, sw))) := by
  intro hgen
  iintro ⟨Hws, H⟩
  iapply ewpEcycle gen c m (some (pr, pw, sr, sw)) hgen
  iintro %σ Hσ
  icases weakStateInterpMem σ c $$ Hσ with ⟨%Hbnd, %Hnv, %Hwf, Hlog, Hlat, Hwsa, Hcl⟩
  ihave ⟨%hws, Hwsa, Hws⟩ := persistent_entails_right (hartWsAgree c (σ.wgws c) ws) $$ [Hwsa Hws]
  · iframe Hwsa Hws
  subst hws
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro Hmask
  isplitr
  · ipureintro
    exact ⟨_, _, rfl, rfl⟩
  inext
  iintro %e' %σ' %hcy
  obtain ⟨rfl, rfl⟩ := hcy
  imod Hmask
  imod hartWsUpdate c (σ.wgws c) (σ.wgws c) (Weak.fencePost (σ.wgws c) pr pw sr sw)
    $$ [$Hwsa $Hws] with ⟨Hwsa, Hws⟩
  imodintro
  isplitl [Hcl Hlog Hlat Hwsa]
  · rw [weakStateInterpWs]
    iapply Hcl $$ %(Weak.fencePost (σ.wgws c) pr pw sr sw) %σ.wglog %(Nat.le_refl _)
      %(fencePostBounded _ _ _ _ _ _ (Hbnd c))
      %(nvHartOfCohEq _ c _ _ (noViolationHart _ _ c Hnv) (fun a => rfl))
      %(appNilOwn σ.wglog c) %Hwf Hlog Hlat Hwsa
  · iapply H $$ Hws

end core

/-! ## 3. REFLECTION: the computable silent stepper

A COMPUTABLE function stepping through consecutive non-memory monad nodes, answering `regRead`
from the register file it threads and moving it at `regWrite`, with a ONCE-proven soundness
lemma.  `choose` is EXCLUDED (a functional stepper cannot follow it), and every register the
stretch touches must lie in the declared footprint `D`. -/

/-- One silent node (deviation 4: `D` is a `List Register`, `GetCycleCount` answers `0`). -/
def esilNode (D : List Register) (rs : RegFile) : SailM Unit → Option (RegFile × SailM Unit)
  | .pure _ => none
  | .impure (.error _) _ => none
  | .impure (.ok o) k =>
    match o, k with
    | .regRead r, k => if r ∈ D then some (rs, k (rs r)) else none
    | .regWrite r v, k => if r ∈ D then some (rs.set r v, k PUnit.unit) else none
    | .instrAnnounce _ _, k => some (rs, k ())
    | .branchAnnounce _ _, k => some (rs, k ())
    | .cacheOp _, k => some (rs, k ())
    | .tlbi _, k => some (rs, k ())
    | .takeException _, k => some (rs, k ())
    | .returnException _, k => some (rs, k ())
    | .translationStart _, k => some (rs, k ())
    | .translationEnd _, k => some (rs, k ())
    | .cycleCount, k => some (rs, k ())
    | .message _, k => some (rs, k ())
    | .getCycleCount, k => some (rs, k (0 : Nat))
    | _, _ => none

def erunSilent : Nat → List Register → RegFile → SailM Unit → RegFile × SailM Unit
  | 0, _, rs, m => (rs, m)
  | n + 1, D, rs, m =>
    match esilNode D rs m with
    | some (rs', m') => erunSilent n D rs' m'
    | none => (rs, m)

/-- The RELATIONAL silent step, at footprint `D`. -/
def esilD (D : List Register) (x y : SailM Unit × RegFile) : Prop :=
  esilNode D x.2 x.1 = some (y.2, y.1)

theorem erunSilentSound (n : Nat) (D : List Register) (rs : RegFile) (m : SailM Unit)
    (rs' : RegFile) (m' : SailM Unit) :
    erunSilent n D rs m = (rs', m') → rtc (esilD D) (m, rs) (m', rs') := by
  induction n generalizing rs m with
  | zero =>
    intro h
    simp only [erunSilent, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact rtc_refl _
  | succ n ih =>
    intro h
    simp only [erunSilent] at h
    split at h
    · rename_i rs1 m1 hnode
      exact rtc_l (y := (m1, rs1)) hnode (ih _ _ h)
    · simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact rtc_refl _

/-- D3: THE σ-EFFECT OF A SILENT NODE, a named four-way disjunction. -/
def esilSigma (σ : WGState) (c : CPU) (rs' : RegFile) (σ' : WGState) : Prop :=
  (∃ k : ErwKind, σ' = ewgRw σ c rs' k) ∨
  (rs' = σ.wgregs c ∧ ∃ (v : Ibch) (n : Nat) (w : BitVec n),
    σ' = ewgIbws σ c v (annPost n w (σ.wgws c))) ∨
  (rs' = σ.wgregs c ∧ ∃ v : Ibch, σ' = ewgIb σ c v) ∨
  (rs' = σ.wgregs c ∧ σ' = σ)

/-- THE SEMANTIC BRIDGE: a silent node IS an arm of `ecycleStep`. -/
theorem esilNodeEcycle (gen : Nat) (σ : WGState) (c : CPU) (D : List Register) (m m' : SailM Unit)
    (rs' : RegFile) :
    esilNode D (σ.wgregs c) m = some (rs', m') →
    ∃ σ' : WGState, ecycleStep gen σ c m none (ECycle gen c m' none) σ' ∧ esilSigma σ c rs' σ' := by
  intro h
  match m, h with
  | .pure _, h => simp [esilNode] at h
  | .impure (.error _) _, h => simp [esilNode] at h
  | .impure (.ok o) k, h =>
    cases o with
    | regRead r =>
      simp only [esilNode] at h
      split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨_, ⟨rfl, rfl⟩, Or.inr (Or.inr (Or.inl ⟨rfl, _, rfl⟩))⟩
      · simp at h
    | regWrite r v =>
      simp only [esilNode] at h
      split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨_, ⟨rfl, rfl⟩, Or.inl ⟨_, rfl⟩⟩
      · simp at h
    | instrAnnounce n w =>
      simp only [esilNode, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨_, ⟨rfl, rfl⟩, Or.inr (Or.inl ⟨rfl, _, n, w, rfl⟩)⟩
    | memRead => simp [esilNode] at h
    | memWrite => simp [esilNode] at h
    | readRam => simp [esilNode] at h
    | writeRam => simp [esilNode] at h
    | barrier => simp [esilNode] at h
    | choose => simp [esilNode] at h
    | getCycleCount =>
      simp only [esilNode, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨_, ⟨rfl, rfl⟩, Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))⟩
    | _ =>
      simp only [esilNode, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨_, ⟨rfl, rfl⟩, Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))⟩

theorem esilNodeEcycleInv (gen : Nat) (σ : WGState) (c : CPU) (D : List Register) (rs' : RegFile)
    (m' m : SailM Unit) (e' : EExpr) (σ' : WGState) :
    esilNode D (σ.wgregs c) m = some (rs', m') →
    ecycleStep gen σ c m none e' σ' →
    e' = ECycle gen c m' none ∧ esilSigma σ c rs' σ' := by
  intro h hcy
  match m, h, hcy with
  | .pure _, h, _ => simp [esilNode] at h
  | .impure (.error _) _, h, _ => simp [esilNode] at h
  | .impure (.ok o) k, h, hcy =>
    cases o with
    | regRead r =>
      simp only [esilNode] at h
      split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨rfl, rfl⟩ := hcy
        exact ⟨rfl, Or.inr (Or.inr (Or.inl ⟨rfl, _, rfl⟩))⟩
      · simp at h
    | regWrite r v =>
      simp only [esilNode] at h
      split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨rfl, rfl⟩ := hcy
        exact ⟨rfl, Or.inl ⟨_, rfl⟩⟩
      · simp at h
    | instrAnnounce n w =>
      simp only [esilNode, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨rfl, rfl⟩ := hcy
      exact ⟨rfl, Or.inr (Or.inl ⟨rfl, _, n, w, rfl⟩)⟩
    | memRead => simp [esilNode] at h
    | memWrite => simp [esilNode] at h
    | readRam => simp [esilNode] at h
    | writeRam => simp [esilNode] at h
    | barrier => simp [esilNode] at h
    | choose => simp [esilNode] at h
    | getCycleCount =>
      simp only [esilNode, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨rfl, rfl⟩ := hcy
      exact ⟨rfl, Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))⟩
    | _ =>
      simp only [esilNode, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨rfl, rfl⟩ := hcy
      exact ⟨rfl, Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))⟩

/-- THE VIEW MOVE OF A SILENT NODE is a `wsDepmove`. -/
theorem esilSigmaDepmove (σ : WGState) (c : CPU) (rs' : RegFile) (σ' : WGState) :
    esilSigma σ c rs' σ' → wsDepmove (σ.wgws c) (σ'.wgws c) := by
  rintro (⟨k, rfl⟩ | ⟨-, v, nn, ww, rfl⟩ | ⟨-, v, rfl⟩ | ⟨-, rfl⟩)
  · rw [ewgRwWs]; exact erwWsDepmove _ _
  · show wsDepmove (σ.wgws c) (updCpu σ.wgws c (annPost nn ww (σ.wgws c)) c)
    rw [gwsInsertEq]; exact annPostDepmove _ _ _
  · exact wsDepmoveRefl _
  · exact wsDepmoveRefl _

theorem esilSigmaLog (σ : WGState) (c : CPU) (rs' : RegFile) (σ' : WGState) :
    esilSigma σ c rs' σ' → σ'.wglog = σ.wglog := by
  rintro (⟨k, rfl⟩ | ⟨-, v, nn, ww, rfl⟩ | ⟨-, v, rfl⟩ | ⟨-, rfl⟩)
  · exact ewgRwLog _ _ _ _
  all_goals rfl

theorem esilSigmaImg (σ : WGState) (c : CPU) (rs' : RegFile) (σ' : WGState) :
    esilSigma σ c rs' σ' → σ'.wgimg = σ.wgimg := by
  rintro (⟨k, rfl⟩ | ⟨-, v, nn, ww, rfl⟩ | ⟨-, v, rfl⟩ | ⟨-, rfl⟩)
  · exact ewgRwImg _ _ _ _
  all_goals rfl

theorem esilSigmaRegs (σ : WGState) (c : CPU) (rs' : RegFile) (σ' : WGState) :
    esilSigma σ c rs' σ' → σ'.wgregs c = rs' := by
  rintro (⟨k, rfl⟩ | ⟨rfl, v, nn, ww, rfl⟩ | ⟨rfl, v, rfl⟩ | ⟨rfl, rfl⟩)
  · rw [ewgRwRegs]; exact gregInsertEq _ _ _
  all_goals rfl

/-- The bound half of every silent node's closing (Lean-only). -/
theorem esilSigmaBounded (σ : WGState) (c : CPU) (rs' : RegFile) (σ' : WGState) (n : Nat) :
    esilSigma σ c rs' σ' → wsBounded (σ.wgws c) n → wsBounded (σ'.wgws c) n := by
  rintro (⟨k, rfl⟩ | ⟨-, v, nn, ww, rfl⟩ | ⟨-, v, rfl⟩ | ⟨-, rfl⟩) hb
  · rw [ewgRwWs]
    cases k with
    | ERWnone => exact hb
    | ERWreg rd srcs => exact regwPostBounded _ _ _ _ hb (srcsViewBounded _ _ _ hb)
    | ERWctrl srcs => exact ctrlPostBounded _ _ _ hb (srcsViewBounded _ _ _ hb)
  · show wsBounded (updCpu σ.wgws c (annPost nn ww (σ.wgws c)) c) n
    rw [gwsInsertEq]; exact annPostBounded _ _ _ _ hb
  · exact hb
  · exact hb

/-- The whole σ-shape of a silent node, as the field equations `weakStateInterpCongr` reads
(Lean-only). -/
theorem esilSigmaShape (σ : WGState) (c : CPU) (rs' : RegFile) (σ' : WGState) :
    esilSigma σ c rs' σ' →
    (ewgRegwslog σ c rs' (σ'.wgws c) σ.wglog).wgregs = σ'.wgregs ∧
    (ewgRegwslog σ c rs' (σ'.wgws c) σ.wglog).wgws = σ'.wgws ∧
    σ'.wglog = σ.wglog ∧ σ'.wgimg = σ.wgimg ∧ σ'.wgdev = σ.wgdev ∧ σ'.wggen = σ.wggen ∧
    σ'.wgpow = σ.wgpow := by
  rintro (⟨k, rfl⟩ | ⟨rfl, v, nn, ww, rfl⟩ | ⟨rfl, v, rfl⟩ | ⟨rfl, rfl⟩)
  · refine ⟨(ewgRwRegs _ _ _ _).symm, ?_, ewgRwLog _ _ _ _, ewgRwImg _ _ _ _, ewgRwDev _ _ _ _,
      ewgRwGen _ _ _ _, ewgRwPow _ _ _ _⟩
    cases k with
    | ERWnone => exact updCpuSelf _ _
    | ERWreg rd srcs => show updCpu σ.wgws c _ = updCpu σ.wgws c _; rw [ewgRwWs]
    | ERWctrl srcs => show updCpu σ.wgws c _ = updCpu σ.wgws c _; rw [ewgRwWs]
  · refine ⟨updCpuSelf _ _, ?_, rfl, rfl, rfl, rfl, rfl⟩
    simp only [ewgIbws, ewgRegwslog, gwsInsertEq]
  · exact ⟨updCpuSelf _ _, updCpuSelf _ _, rfl, rfl, rfl, rfl, rfl⟩
  · exact ⟨updCpuSelf _ _, updCpuSelf _ _, rfl, rfl, rfl, rfl, rfl⟩

/-! ## 3b. THE REFLECTIVE INTERFACE: total projections and unevaluated compositions

The rule this section exists to enforce: **no call site ever writes a residual monad down.**  The
interface is restated over a CURSOR and TOTAL functions on it, small-output PROJECTIONS, and
ONCE-proven INVERSION lemmas. -/

/-- THE CURSOR: the machine's register file and its residual monad. -/
abbrev ecur : Type := RegFile × SailM Unit

/-- ONE SILENT STRETCH, as a total function of cursors. -/
def esil (n : Nat) (D : List Register) (x : ecur) : ecur := erunSilent n D x.1 x.2

/-- The read resume: answered by the VALUE READ, passed as a `Nat` (deviation 5). -/
def ereadResume (v : Nat) (m : SailM Unit) : SailM Unit :=
  match m with
  | .impure (.ok (.memRead n _ _)) k => k (.Ok (BitVec.ofNat (8 * n) v, none))
  | _ => m

/-- The write resume: MachCSL's write answer `.Ok (some true)` (deviation 5). -/
def ewriteResume (m : SailM Unit) : SailM Unit :=
  match m with
  | .impure (.ok (.memWrite _ _ _)) k => k (.Ok (some true))
  | _ => m

def ebarResume (m : SailM Unit) : SailM Unit :=
  match m with
  | .impure (.ok (.barrier _)) k => k ()
  | _ => m

/-- CROSSING AN INSTRUCTION BOUNDARY. -/
noncomputable def ecurLoop (tick : Bool) (x : ecur) : ecur := (x.1, riscvStep tick)

def ecurRead (v : Nat) (x : ecur) : ecur := (x.1, ereadResume v x.2)
def ecurWrite (x : ecur) : ecur := (x.1, ewriteResume x.2)
def ecurBar (x : ecur) : ecur := (x.1, ebarResume x.2)

/-- THE PROJECTIONS (a model `.error` node is tag 5, deviation 4). -/
def enodeTag (m : SailM Unit) : Nat :=
  match m with
  | .pure _ => 0
  | .impure (.ok (.memRead _ _ _)) _ => 1
  | .impure (.ok (.memWrite _ _ _)) _ => 2
  | .impure (.ok (.barrier _)) _ => 3
  | .impure (.ok (.choose _)) _ => 4
  | _ => 5

/-- The read request at the head (deviation 5: indexed by the width AND the VA width). -/
def ereadReqAt (n va : Nat) (m : SailM Unit) :
    Option (Mem_read_request n va Arch.pa Arch.translation Arch.arch_ak) :=
  match m with
  | .impure (.ok (.memRead n' va' req)) _ =>
    if h : n' = n ∧ va' = va then some (h.2 ▸ h.1 ▸ req) else none
  | _ => none

def ewriteReqAt (n va : Nat) (m : SailM Unit) :
    Option (Mem_write_request n va Arch.pa Arch.translation Arch.arch_ak) :=
  match m with
  | .impure (.ok (.memWrite n' va' req)) _ =>
    if h : n' = n ∧ va' = va then some (h.2 ▸ h.1 ▸ req) else none
  | _ => none

def ebarAt (m : SailM Unit) : Option barrier_kind :=
  match m with
  | .impure (.ok (.barrier b)) _ => some b
  | _ => none

/-! The four inversions, proven once. -/

theorem enodeTagRet (m : SailM Unit) : enodeTag m = 0 → ∃ u : Unit, m = FreeM.pure u := by
  intro h
  match m, h with
  | .pure u, _ => exact ⟨u, rfl⟩
  | .impure (.error _) _, h => simp [enodeTag] at h
  | .impure (.ok o) k, h => cases o <;> simp [enodeTag] at h

theorem ereadReqAtInv (n va : Nat) (m : SailM Unit)
    (req : Mem_read_request n va Arch.pa Arch.translation Arch.arch_ak) :
    ereadReqAt n va m = some req →
    ∃ K, m = .impure (.ok (.memRead n va req)) K ∧
      ∀ w : BitVec (8 * n), ereadResume w.toNat m = K (.Ok (w, none)) := by
  intro h
  match m, h with
  | .pure _, h => simp [ereadReqAt] at h
  | .impure (.error _) _, h => simp [ereadReqAt] at h
  | .impure (.ok o) k, h =>
    cases o with
    | memRead n' va' req' =>
      simp only [ereadReqAt] at h
      split at h
      · rename_i hc
        obtain ⟨rfl, rfl⟩ := hc
        simp only [Option.some.injEq] at h
        subst h
        refine ⟨k, rfl, fun w => ?_⟩
        simp only [ereadResume, BitVec.ofNat_toNat, BitVec.setWidth_eq]
      · simp at h
    | _ => simp [ereadReqAt] at h

theorem ewriteReqAtInv (n va : Nat) (m : SailM Unit)
    (req : Mem_write_request n va Arch.pa Arch.translation Arch.arch_ak) :
    ewriteReqAt n va m = some req →
    ∃ K, m = .impure (.ok (.memWrite n va req)) K ∧ ewriteResume m = K (.Ok (some true)) := by
  intro h
  match m, h with
  | .pure _, h => simp [ewriteReqAt] at h
  | .impure (.error _) _, h => simp [ewriteReqAt] at h
  | .impure (.ok o) k, h =>
    cases o with
    | memWrite n' va' req' =>
      simp only [ewriteReqAt] at h
      split at h
      · rename_i hc
        obtain ⟨rfl, rfl⟩ := hc
        simp only [Option.some.injEq] at h
        subst h
        exact ⟨k, rfl, rfl⟩
      · simp at h
    | _ => simp [ewriteReqAt] at h

theorem ebarAtInv (m : SailM Unit) (b : barrier_kind) :
    ebarAt m = some b → ∃ K, m = .impure (.ok (.barrier b)) K ∧ ebarResume m = K () := by
  intro h
  match m, h with
  | .pure _, h => simp [ebarAt] at h
  | .impure (.error _) _, h => simp [ebarAt] at h
  | .impure (.ok o) k, h =>
    cases o with
    | barrier b' =>
      simp only [ebarAt, Option.some.injEq] at h
      subst h
      exact ⟨k, rfl, rfl⟩
    | _ => simp [ebarAt] at h

/-! ## 4. THE PROOF INTERFACE: the n-step batched rule -/

/-- Two register files agree on the footprint. -/
def regAgreeOn (D : List Register) (rs rs' : RegFile) : Prop :=
  ∀ r : Register, r ∈ D → rs r = rs' r

/-- THE TRANSPORT the batching needs: the stretch the caller COMPUTED at its own register file is
the stretch the machine takes. -/
theorem esilNodeAgree (D : List Register) (rs1 rs2 : RegFile) (m m1 : SailM Unit) (rs1' : RegFile) :
    regAgreeOn D rs1 rs2 → esilNode D rs1 m = some (rs1', m1) →
    ∃ rs2', esilNode D rs2 m = some (rs2', m1) ∧ regAgreeOn D rs1' rs2' := by
  intro hag h
  match m, h with
  | .pure _, h => simp [esilNode] at h
  | .impure (.error _) _, h => simp [esilNode] at h
  | .impure (.ok o) k, h =>
    cases o with
    | regRead r =>
      simp only [esilNode] at h ⊢
      split at h
      · rename_i hr
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨rs2, ?_, hag⟩
        rw [if_pos hr, hag r hr]
      · simp at h
    | regWrite r v =>
      simp only [esilNode] at h ⊢
      split at h
      · rename_i hr
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨rs2.set r v, by rw [if_pos hr], fun r' hr' => ?_⟩
        by_cases he : r' = r
        · subst he; simp only [RegFile.set_same]
        · rw [RegFile.set_other _ _ _ _ he, RegFile.set_other _ _ _ _ he]; exact hag r' hr'
      · simp at h
    | memRead => simp [esilNode] at h
    | memWrite => simp [esilNode] at h
    | readRam => simp [esilNode] at h
    | writeRam => simp [esilNode] at h
    | barrier => simp [esilNode] at h
    | choose => simp [esilNode] at h
    | _ =>
      simp only [esilNode, Option.some.injEq, Prod.mk.injEq] at h ⊢
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨rs2, ⟨rfl, rfl⟩, hag⟩

section batch

variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [WeakGS GF]

/-- The register footprint `D` of the hart, at the values of `rs`. -/
abbrev eregFrame (c : CPU) (rs : RegFile) (D : List Register) : IProp GF :=
  iprop([∗list] r ∈ D, regPointsTo (hlc := hlc) (GF := GF) c r (DFrac.own 1) (rs r))

theorem eregFrameExt (c : CPU) (rs rs' : RegFile) (D : List Register) :
    regAgreeOn D rs rs' →
    eregFrame (hlc := hlc) (GF := GF) c rs D ⊣⊢ eregFrame (hlc := hlc) (GF := GF) c rs' D := by
  intro hag
  unfold eregFrame
  rw [BigSepL.bigSepL_eq (Φ := fun _ r => regPointsTo (hlc := hlc) (GF := GF) c r (DFrac.own 1) (rs r))
    (Ψ := fun _ r => regPointsTo (hlc := hlc) (GF := GF) c r (DFrac.own 1) (rs' r))
    (fun {_ x} hk => congrArg (regPointsTo (hlc := hlc) (GF := GF) c x (DFrac.own 1))
      (hag x (List.mem_of_getElem? hk)))]
  exact .rfl

/-- Two full cells name two different registers (Lean-only helper). -/
theorem regPointsToNe (c : CPU) (r r' : Register) (x : RegisterType r) (y : RegisterType r') :
    regPointsTo (hlc := hlc) (GF := GF) c r (DFrac.own 1) x ∗
      regPointsTo (hlc := hlc) (GF := GF) c r' (DFrac.own 1) y ⊢ ⌜r ≠ r'⌝ := by
  unfold regPointsTo regPointsToAt
  iintro ⟨H1, H2⟩
  ihave %h := ghost_map_elem_ne _ (regIdx r) (regIdx r') (DFrac.own 1) _ _ $$ H1 H2
  ipureintro
  intro he
  subst he
  exact h rfl

/-- ... so a full cell is not in a frame it is separate from (Lean-only helper). -/
theorem eregFrameNotMem (c : CPU) (rs : RegFile) (D : List Register) (r : Register)
    (x : RegisterType r) :
    regPointsTo (hlc := hlc) (GF := GF) c r (DFrac.own 1) x ∗ eregFrame (hlc := hlc) (GF := GF) c rs D ⊢
      ⌜r ∉ D⌝ := by
  unfold eregFrame
  induction D with
  | nil => iintro -; ipureintro; simp
  | cons r0 D ih =>
    iintro ⟨Hx, Hr0, Hrest⟩
    ihave ⟨%hne, Hx, Hr0⟩ := persistent_entails_right (regPointsToNe c r r0 x (rs r0)) $$ [Hx Hr0]
    · iframe Hx Hr0
    ihave %hnm := ih $$ [Hx Hrest]
    · iframe Hx Hrest
    ipureintro
    simp only [List.mem_cons, not_or]
    exact ⟨hne, hnm⟩

theorem eregFrameAgree (c : CPU) (rs : RegFile) (D : List Register) (rs0 : RegFile) :
    regInterp (hlc := hlc) (GF := GF) c rs0 ∗ eregFrame (hlc := hlc) (GF := GF) c rs D ⊢
      ⌜regAgreeOn D rs rs0⌝ := by
  unfold eregFrame
  induction D with
  | nil => iintro -; ipureintro; intro r hr; simp at hr
  | cons r0 D ih =>
    iintro ⟨Hi, Hr0, Hrest⟩
    ihave ⟨%h0, Hi, Hr0⟩ := persistent_entails_right (reg_valid c rs0 r0 (DFrac.own 1) (rs r0))
      $$ [Hi Hr0]
    · iframe Hi Hr0
    ihave %h1 := ih $$ [Hi Hrest]
    · iframe Hi Hrest
    ipureintro
    intro r hr
    rcases List.mem_cons.1 hr with rfl | hr
    · exact h0.symm
    · exact h1 r hr

theorem eregFrameUpdate (c : CPU) (rs : RegFile) (D : List Register) (r : Register)
    (v : RegisterType r) (rs0 : RegFile) :
    r ∈ D →
    regInterp (hlc := hlc) (GF := GF) c rs0 ∗ eregFrame (hlc := hlc) (GF := GF) c rs D ⊢
      |==> (regInterp (hlc := hlc) (GF := GF) c (rs0.set r v) ∗
        eregFrame (hlc := hlc) (GF := GF) c (rs.set r v) D) := by
  intro hrD
  induction D with
  | nil => simp at hrD
  | cons r0 D ih =>
    by_cases he : r0 = r
    · subst he
      iintro ⟨Hi, Hr, Hrest⟩
      ihave ⟨%hnm, Hr, Hrest⟩ := persistent_entails_right
        (eregFrameNotMem (hlc := hlc) (GF := GF) c rs D r0 (rs r0)) $$ [Hr Hrest]
      · iframe Hr Hrest
      imod reg_update c rs0 r0 (rs r0) v $$ [$Hi $Hr] with ⟨Hi, Hr⟩
      imodintro
      iframe Hi
      isplitl [Hr]
      · simp only [RegFile.set_same]
        iexact Hr
      · iapply (eregFrameExt (hlc := hlc) (GF := GF) c rs (rs.set r0 v) D
          (fun r' hr' => (RegFile.set_other rs r0 r' v (fun h : r' = r0 => hnm (h ▸ hr'))).symm)).1 $$ Hrest
    · have hD : r ∈ D := by
        rcases List.mem_cons.1 hrD with h | h
        · exact absurd h.symm he
        · exact h
      iintro ⟨Hi, Hr0, Hrest⟩
      imod (ih hD) $$ [$Hi $Hrest] with ⟨Hi, Hrest⟩
      imodintro
      iframe Hi
      isplitl [Hr0]
      · rw [RegFile.set_other _ _ _ _ he]
        iexact Hr0
      · iexact Hrest

/-- The register half of a silent node (Lean-only; Rocq inlines it in `ewp_ev_sil_node`). -/
theorem esilNodeRegs (c : CPU) (D : List Register) (rs rs0 rs1 rs2 : RegFile) (m m1 m2 : SailM Unit) :
    esilNode D rs m = some (rs1, m1) → esilNode D rs0 m = some (rs2, m2) →
    regInterp (hlc := hlc) (GF := GF) c rs0 ∗ eregFrame (hlc := hlc) (GF := GF) c rs D ⊢
      |==> (regInterp (hlc := hlc) (GF := GF) c rs2 ∗ eregFrame (hlc := hlc) (GF := GF) c rs1 D) := by
  intro h1 h2
  match m, h1, h2 with
  | .pure _, h1, _ => simp [esilNode] at h1
  | .impure (.error _) _, h1, _ => simp [esilNode] at h1
  | .impure (.ok o) k, h1, h2 =>
    cases o with
    | regWrite r v =>
      simp only [esilNode] at h1 h2
      split at h1
      · rename_i hr
        rw [if_pos hr] at h2
        simp only [Option.some.injEq, Prod.mk.injEq] at h1 h2
        obtain ⟨rfl, -⟩ := h1
        obtain ⟨rfl, -⟩ := h2
        exact eregFrameUpdate c rs D r v rs0 hr
      · simp at h1
    | regRead r =>
      simp only [esilNode] at h1 h2
      split at h1
      · rename_i hr
        rw [if_pos hr] at h2
        simp only [Option.some.injEq, Prod.mk.injEq] at h1 h2
        obtain ⟨rfl, -⟩ := h1
        obtain ⟨rfl, -⟩ := h2
        exact BIUpdate.intro
      · simp at h1
    | memRead => simp [esilNode] at h1
    | memWrite => simp [esilNode] at h1
    | readRam => simp [esilNode] at h1
    | writeRam => simp [esilNode] at h1
    | barrier => simp [esilNode] at h1
    | choose => simp [esilNode] at h1
    | _ =>
      simp only [esilNode, Option.some.injEq, Prod.mk.injEq] at h1 h2
      obtain ⟨rfl, -⟩ := h1
      obtain ⟨rfl, -⟩ := h2
      exact BIUpdate.intro

/-- D3-2, THE ONE PLACE THE DEPENDENCY VIEWS LEAK INTO THE WP TIER: one silent node, handing back
`wsDepmove` (callers use `ewpEvBatch`). -/
theorem ewpEvSilNode (gen : Nat) (c : CPU) (D : List Register) (rs : RegFile) (m m1 : SailM Unit)
    (rs1 : RegFile) (ws : Wstate) :
    gen = 0 → esilNode D rs m = some (rs1, m1) →
    hartWs (GF := GF) c ws ∗ eregFrame (hlc := hlc) (GF := GF) c rs D ∗
      ▷ (∀ ws' : Wstate, ⌜wsDepmove ws ws'⌝ -∗ hartWs (GF := GF) c ws' -∗
          eregFrame (hlc := hlc) (GF := GF) c rs1 D -∗
          ewpTriv (hlc := hlc) (GF := GF) ⊤ (ECycle gen c m1 none)) ⊢
    ewpTriv (hlc := hlc) (GF := GF) ⊤ (ECycle gen c m none) := by
  intro hgen hnode
  iintro ⟨Hws, Hrf, H⟩
  iapply ewpEcycle gen c m none hgen
  iintro %σ Hσ
  icases weakStateInterpRmw σ c $$ Hσ with ⟨%Hbnd, %Hnv, %Hwf, Hri, Hlog, Hlat, Hwsa, Hcl⟩
  ihave ⟨%hag, Hri, Hrf⟩ := persistent_entails_right
    (eregFrameAgree (hlc := hlc) (GF := GF) c rs D (σ.wgregs c)) $$ [Hri Hrf]
  · iframe Hri Hrf
  ihave ⟨%hws, Hwsa, Hws⟩ := persistent_entails_right (hartWsAgree c (σ.wgws c) ws) $$ [Hwsa Hws]
  · iframe Hwsa Hws
  subst hws
  obtain ⟨rs2, hnode2, -⟩ := esilNodeAgree D rs (σ.wgregs c) m m1 rs1 hag hnode
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro Hmask
  isplitr
  · ipureintro
    obtain ⟨σ1, hc, -⟩ := esilNodeEcycle gen σ c D m m1 rs2 hnode2
    exact ⟨_, _, hc⟩
  inext
  iintro %e' %σ' %hcy
  imod Hmask
  obtain ⟨rfl, hσ'⟩ := esilNodeEcycleInv gen σ c D rs2 m1 m e' σ' hnode2 hcy
  have hdm := esilSigmaDepmove σ c rs2 σ' hσ'
  obtain ⟨e1, e2, e3, e4, e5, e6, e7⟩ := esilSigmaShape σ c rs2 σ' hσ'
  have hEq := weakStateInterpCongr (hlc := hlc) (GF := GF)
    (ewgRegwslog σ c rs2 (σ'.wgws c) σ.wglog) σ' e1 e4.symm e3.symm e2 e5.symm e6.symm e7.symm
  imod esilNodeRegs c D rs (σ.wgregs c) rs1 rs2 m m1 m1 hnode hnode2 $$ [$Hri $Hrf] with ⟨Hri, Hrf⟩
  imod hartWsUpdate c (σ.wgws c) (σ.wgws c) (σ'.wgws c) $$ [$Hwsa $Hws] with ⟨Hwsa, Hws⟩
  imodintro
  isplitl [Hcl Hri Hlog Hlat Hwsa]
  · rw [← hEq]
    iapply Hcl $$ %rs2 %(σ'.wgws c) %σ.wglog %(Nat.le_refl _)
      %(esilSigmaBounded σ c rs2 σ' _ hσ' (Hbnd c))
      %(nvHartOfCohEq _ c _ _ (noViolationHart _ _ c Hnv) (fun a => wsDepmoveCoh _ _ a hdm))
      %(appNilOwn σ.wglog c) %Hwf Hri Hlog Hlat Hwsa
  · iapply H $$ %(σ'.wgws c) %hdm Hws Hrf

/-- THE BATCHED RULE.  The induction is HERE, not at the call site (`wsDepmove` is transitive). -/
theorem ewpEvSilRtc (gen : Nat) (c : CPU) (D : List Register) (x y : SailM Unit × RegFile)
    (ws : Wstate) :
    gen = 0 → rtc (esilD D) x y →
    hartWs (GF := GF) c ws ∗ eregFrame (hlc := hlc) (GF := GF) c x.2 D ∗
      (∀ ws' : Wstate, ⌜wsDepmove ws ws'⌝ -∗ hartWs (GF := GF) c ws' -∗
          eregFrame (hlc := hlc) (GF := GF) c y.2 D -∗
          ewpTriv (hlc := hlc) (GF := GF) ⊤ (ECycle gen c y.1 none)) ⊢
    ewpTriv (hlc := hlc) (GF := GF) ⊤ (ECycle gen c x.1 none) := by
  intro hgen hrtc
  revert ws
  refine rtc_ind_l (R := esilD D)
    (fun x => ∀ ws : Wstate,
      hartWs (GF := GF) c ws ∗ eregFrame (hlc := hlc) (GF := GF) c x.2 D ∗
        (∀ ws' : Wstate, ⌜wsDepmove ws ws'⌝ -∗ hartWs (GF := GF) c ws' -∗
          eregFrame (hlc := hlc) (GF := GF) c y.2 D -∗
          ewpTriv (hlc := hlc) (GF := GF) ⊤ (ECycle gen c y.1 none)) ⊢
      ewpTriv (hlc := hlc) (GF := GF) ⊤ (ECycle gen c x.1 none)) y ?_ ?_ x hrtc
  · intro ws
    iintro ⟨Hws, Hrf, H⟩
    iapply H $$ %ws %(wsDepmoveRefl ws) Hws Hrf
  · intro x0 y0 hxy _ ih ws
    iintro ⟨Hws, Hrf, H⟩
    iapply ewpEvSilNode gen c D x0.2 x0.1 y0.1 y0.2 ws hgen hxy
    iframe Hws Hrf
    inext
    iintro %ws1 %hd1 Hws Hrf
    iapply ih ws1
    iframe Hws Hrf
    iintro %ws2 %hd2 Hws Hrf
    iapply H $$ %ws2 %(wsDepmoveTrans hd1 hd2) Hws Hrf

/-- THE CALL-SITE FORM: a whole stretch of `EWP` out and NO EQUATION IN. -/
theorem ewpEvBatch (gen : Nat) (c : CPU) (D : List Register) (n : Nat) (x : ecur) (ws : Wstate) :
    gen = 0 →
    hartWs (GF := GF) c ws ∗ eregFrame (hlc := hlc) (GF := GF) c x.1 D ∗
      (∀ ws' : Wstate, ⌜wsDepmove ws ws'⌝ -∗ hartWs (GF := GF) c ws' -∗
          eregFrame (hlc := hlc) (GF := GF) c (esil n D x).1 D -∗
          ewpTriv (hlc := hlc) (GF := GF) ⊤ (ECycle gen c (esil n D x).2 none)) ⊢
    ewpTriv (hlc := hlc) (GF := GF) ⊤ (ECycle gen c x.2 none) := by
  intro hgen
  exact ewpEvSilRtc gen c D (x.2, x.1) ((esil n D x).2, (esil n D x).1) ws hgen
    (erunSilentSound n D x.1 x.2 (esil n D x).1 (esil n D x).2 rfl)

end batch

/-! ## 5. The RAM events

Both are stated at the EVENT's own state (finding F3) and give the caller a mask-changing
callback AROUND THE SINGLE EVENT (finding F5). -/

/-- `readOk` at a plain (non-i-cache, non-exclusive) access IS `wbyteOk` per byte, at the hart's
own projected `Wmstate`. -/
theorem readOkWbyteOk (σ : WGState) (c : CPU) (ak : AkInfo) (base : Int) (tvs : List (Nat × BitVec 8))
    (j t : Nat) (v : BitVec 8) :
    ak.akIfetch = false → ak.akLatest = false →
    readOk (imgZ σ.wgimg) σ.wglog (σ.wgws c) ak.akSync false base tvs →
    tvs[j]? = some (t, v) → wbyteOk (whartView σ c) ak (base + (j : Int)) t v := by
  intro hif hlat hrd hj
  obtain ⟨hb, hr, -⟩ := hrd j t v hj
  refine ⟨hb, ?_⟩
  rw [if_neg (by simp [hif])]
  refine ⟨by rw [← loadVpreD0]; exact hr, fun h => absurd h (by simp [hlat])⟩

/-- O2 (Lean-only): the i-cache twin — an admissible fetch byte IS `wbyteOk` at the hart's view. -/
theorem ifetchOkWbyteOk (σ : WGState) (c : CPU) (ak : AkInfo) (base : Int)
    (tvs : List (Nat × BitVec 8)) (j t : Nat) (v : BitVec 8) :
    ak.akIfetch = true → ifetchOk (imgZ σ.wgimg) σ.wglog (σ.wgitv c) base tvs →
    tvs[j]? = some (t, v) → wbyteOk (whartView σ c) ak (base + (j : Int)) t v :=
  fun hif hok hj => (wbyteOkIfetch _ ak _ t v hif).2 (hok j t v hj)

/-- THE PINNING LEMMA, proven once: at a never-written byte every admissible timestamp is 0 and
the value is the image's (deviation 6: for EVERY access kind). -/
theorem etextBytePin (σ : WGState) (c : CPU) (ak : AkInfo) (a : Int) (t : Nat) (v b : BitVec 8) :
    latestVal (imgZ σ.wgimg) σ.wglog a 0 b → wbyteOk (whartView σ c) ak a t v → t = 0 ∧ v = b := by
  intro hlv hok
  have hts : latestTs σ.wglog a = 0 := latestValTs _ _ _ _ _ hlv
  have ht : t = latestTs (whartView σ c).wmLog a :=
    wbyteOkPinned (whartView σ c) ak a t v (fun _ => readPinnedUnwritten _ ak a hts) hok
  rw [whartViewLog, hts] at ht
  subst ht
  refine ⟨rfl, ?_⟩
  exact Option.some.inj (hok.1.symm.trans hlv.1)

section ram

variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [WeakGS GF]

/-- The appended message is the author's own and well formed (Lean-only helper). -/
theorem storeMsgOwn (c : CPU) (k : WmClass) (pa : PAddr) (n : Nat) (v : BitVec (8 * n)) :
    ∀ m, m ∈ [wwriteMsg (some c.val) k pa n v] → m.wmTid = some c.val := by
  intro m hm
  simp only [List.mem_singleton] at hm
  subst hm
  rfl

theorem storeLogWf (log : List Wmsg) (c : CPU) (k : WmClass) (pa : PAddr) (n : Nat)
    (v : BitVec (8 * n)) :
    wlogWf log → accWf pa n → wlogWf (log ++ [wwriteMsg (some c.val) k pa n v]) := by
  intro hwf hacc m hm
  rcases List.mem_append.1 hm with h | h
  · exact hwf m h
  · simp only [List.mem_singleton] at h
    subst h
    exact accWfMsg _ _ _ _ _ hacc

/-- The φ obligation of a store's view move (Lean-only; Rocq inlines it twice). -/
theorem storeNvHart (log : List Wmsg) (c : CPU) (ws : Wstate) (k : WmClass) (pa : PAddr) (n : Nat)
    (v : BitVec (8 * n)) (rl : Bool) (va vd : Nat) :
    nvHart log c ws →
    (∀ j : Nat, j < n → nvOk log c (WeakInterp.accAddr pa j)) →
    nvHart (log ++ [wwriteMsg (some c.val) k pa n v]) c
      (storePostRunD ws rl va vd (paZ pa) n (log.length + 1)) := by
  intro hnv hok
  apply nvHartCohStep _ c ws
  · exact nvHartAppOwn _ _ c ws hnv (storeMsgOwn c k pa n v)
  · intro a hlt
    obtain ⟨j, hj, rfl⟩ := cohStorePostRunDMoved ws rl va vd (paZ pa) n (log.length + 1) a hlt
    exact nvByteAppOwn _ _ c _ _ (hok j hj _) (storeMsgOwn c k pa n v)

theorem storeBounded (log : List Wmsg) (c : CPU) (ws : Wstate) (k : WmClass) (pa : PAddr) (n : Nat)
    (v : BitVec (8 * n)) (rl : Bool) (va vd : Nat) :
    wsBounded ws log.length → va ≤ log.length → vd ≤ log.length →
    wsBounded (storePostRunD ws rl va vd (paZ pa) n (log.length + 1))
      (log ++ [wwriteMsg (some c.val) k pa n v]).length := by
  intro hb hva hvd
  rw [List.length_append, List.length_singleton]
  exact storePostRunDBounded _ _ _ _ _ _ _ log.length _ hb (Nat.le_refl _) (by omega) (by omega)
    (by omega)

/-- 5a. THE RAM STORE — the C/D/S owned-store protocol step at ONE event (deviation 5: the
written value `v` is a parameter, `req.value = some v`). -/
theorem ewpEvStore (gen : Nat) (c : CPU) (n va : Nat)
    (req : Mem_write_request n va Arch.pa Arch.translation Arch.arch_ak)
    (K : Result (Option Bool) Arch.abort → SailM Unit) (v : BitVec (8 * n)) (ws : Wstate) :
    gen = 0 → devAddr req.pa = false → n ≠ 0 → req.value = some v →
    (classify req.access_kind).akLatest = false → accWf req.pa n →
    hartWs (GF := GF) c ws ∗
      (∀ σ : WGState, ⌜σ.wgws c = ws⌝ -∗ ⌜wlogWf σ.wglog⌝ -∗ ⌜wsBounded ws σ.wglog.length⌝ -∗
        wlogLb (GF := GF) σ.wglog -∗ wlatInterp (GF := GF) σ.wgimg σ.wglog ={⊤,∅}=∗
        ▷ |={∅,⊤}=> iprop(
          ⌜∀ j : Nat, j < n → nvOk σ.wglog c (WeakInterp.accAddr req.pa j)⌝ ∗
           wlatInterp (GF := GF) σ.wgimg
             (σ.wglog ++ [wwriteMsg (some c.val) (wmClassOf (classify req.access_kind) ws) req.pa n v]) ∗
           (∀ (va' : Nat) (vd : Nat),
             hartWs (GF := GF) c (storePostRunD ws (classify req.access_kind).akSync va' vd
               (paZ req.pa) n (σ.wglog.length + 1)) -∗
             ewpTriv (hlc := hlc) (GF := GF) ⊤ (ECycle gen c (K (.Ok (some true))) none)))) ⊢
    ewpTriv (hlc := hlc) (GF := GF) ⊤ (ECycle gen c (.impure (.ok (.memWrite n va req)) K) none) := by
  intro hgen hdev hn hv hlat hacc
  iintro ⟨Hws, Hk⟩
  iapply ewpEcycle gen c _ none hgen
  iintro %σ Hσ
  icases weakStateInterpMem σ c $$ Hσ with ⟨%Hbnd, %Hnv, %Hwf, Hlog, Hlat0, Hwsa, Hcl⟩
  ihave ⟨%hws, Hwsa, Hws⟩ := persistent_entails_right (hartWsAgree c (σ.wgws c) ws) $$ [Hwsa Hws]
  · iframe Hwsa Hws
  subst hws
  icases wlogSnapshot σ.wglog $$ Hlog with ⟨Hlog, #Hlb⟩
  imod Hk $$ %σ %rfl %Hwf %(Hbnd c) Hlb Hlat0 with Hk
  imodintro
  isplitr
  · ipureintro
    refine ⟨ECycle gen c (K (.Ok (some true))) none,
      ewgStore σ c (storePostRunD (σ.wgws c) (classify req.access_kind).akSync
          (srcsView (σ.wgws c) (depsAsrc (edeps σ c))) (srcsView (σ.wgws c) (depsVsrc (edeps σ c)))
          (paZ req.pa) n (σ.wglog.length + 1))
        (σ.wglog ++ [⟨paZ req.pa, WeakInterpProj.wbytes n v, some c.val,
          wmClassOf (classify req.access_kind) (σ.wgws c)⟩]), ?_⟩
    dsimp only [ecycleStep, emonadStep]
    rw [if_neg (by simp [hdev]), hv]
    exact ⟨hn, Or.inl ⟨hlat, rfl, rfl⟩⟩
  inext
  iintro %e' %σ' %hcy
  simp only [ecycleStep, emonadStep, hdev, hv, Bool.false_eq_true, ↓reduceIte] at hcy
  rcases hcy.2 with ⟨-, rfl, rfl⟩ | ⟨hbad, -⟩
  rotate_left
  · simp [hlat] at hbad
  imod Hk with ⟨%Hnvok, Hlat, Hcont⟩
  imod wlogUpdate σ.wglog
    [wwriteMsg (some c.val) (wmClassOf (classify req.access_kind) (σ.wgws c)) req.pa n v] $$ Hlog
    with Hlog
  imod hartWsUpdate c (σ.wgws c) (σ.wgws c)
    (storePostRunD (σ.wgws c) (classify req.access_kind).akSync
      (srcsView (σ.wgws c) (depsAsrc (edeps σ c))) (srcsView (σ.wgws c) (depsVsrc (edeps σ c)))
      (paZ req.pa) n (σ.wglog.length + 1)) $$ [$Hwsa $Hws] with ⟨Hwsa, Hws⟩
  imodintro
  isplitl [Hcl Hlog Hlat Hwsa]
  · rw [← wwriteMsgWbytes]
    iapply Hcl $$ %_ %_ %(by simp) %(storeBounded _ c _ _ _ n v _ _ _ (Hbnd c)
        (srcsViewBounded _ _ _ (Hbnd c)) (srcsViewBounded _ _ _ (Hbnd c)))
      %(storeNvHart _ c _ _ _ n v _ _ _ (noViolationHart _ _ c Hnv) Hnvok)
      %⟨_, rfl, storeMsgOwn c _ req.pa n v⟩ %(storeLogWf _ c _ _ n v Hwf hacc) Hlog Hlat Hwsa
  · iapply Hcont $$ %_ %_ Hws

/-- 5b. THE RAM LOAD, RACY FORM — the continuation is quantified over EVERY read the machine
admits AT THE READ EVENT'S OWN STATE (finding F3(a)'s frozen-log assumption is deleted). -/
theorem ewpEvLoad (gen : Nat) (c : CPU) (n va : Nat)
    (req : Mem_read_request n va Arch.pa Arch.translation Arch.arch_ak)
    (K : Result (BitVec (8 * n) × Option Bool) Arch.abort → SailM Unit) (ws : Wstate) :
    gen = 0 → devAddr req.pa = false →
    (classify req.access_kind).akIfetch = false → (classify req.access_kind).akLatest = false →
    hartWs (GF := GF) c ws ∗
      (∀ σ : WGState, ⌜σ.wgws c = ws⌝ -∗ ⌜wlogWf σ.wglog⌝ -∗ ⌜wsBounded ws σ.wglog.length⌝ -∗
        wlogLb (GF := GF) σ.wglog -∗ wlatInterp (GF := GF) σ.wgimg σ.wglog ={⊤,∅}=∗
        ⌜∃ (w : BitVec (8 * n)) (tvs : List (Nat × BitVec 8)),
          tvs.length = n ∧ (∀ j : Nat, j < n → (tvs.map Prod.snd)[j]? = some (nthByte w j)) ∧
          readOk (imgZ σ.wgimg) σ.wglog ws (classify req.access_kind).akSync false (paZ req.pa) tvs⌝ ∗
        ▷ (∀ (w : BitVec (8 * n)) (tvs : List (Nat × BitVec 8)),
            ⌜tvs.length = n⌝ -∗
            ⌜∀ j : Nat, j < n → (tvs.map Prod.snd)[j]? = some (nthByte w j)⌝ -∗
            ⌜readOk (imgZ σ.wgimg) σ.wglog ws (classify req.access_kind).akSync false (paZ req.pa)
              tvs⌝ ={∅,⊤}=∗
            ⌜∀ a : Int, coh ws a <
                coh (loadPostRun ws (classify req.access_kind).akSync (paZ req.pa)
                  (tvs.map Prod.fst)) a →
              nvOk σ.wglog c a⌝ ∗
            wlatInterp (GF := GF) σ.wgimg σ.wglog ∗
            (hartWs (GF := GF) c (loadPostRun ws (classify req.access_kind).akSync (paZ req.pa)
                (tvs.map Prod.fst)) -∗
              ewpTriv (hlc := hlc) (GF := GF) ⊤ (ECycle gen c (K (.Ok (w, none))) none)))) ⊢
    ewpTriv (hlc := hlc) (GF := GF) ⊤ (ECycle gen c (.impure (.ok (.memRead n va req)) K) none) := by
  intro hgen hdev hif hlat
  iintro ⟨Hws, Hk⟩
  iapply ewpEcycle gen c _ none hgen
  iintro %σ Hσ
  icases weakStateInterpMem σ c $$ Hσ with ⟨%Hbnd, %Hnv, %Hwf, Hlog, Hlat0, Hwsa, Hcl⟩
  ihave ⟨%hws, Hwsa, Hws⟩ := persistent_entails_right (hartWsAgree c (σ.wgws c) ws) $$ [Hwsa Hws]
  · iframe Hwsa Hws
  subst hws
  icases wlogSnapshot σ.wglog $$ Hlog with ⟨Hlog, #Hlb⟩
  imod Hk $$ %σ %rfl %Hwf %(Hbnd c) Hlb Hlat0 with ⟨%Hen, Hk⟩
  imodintro
  isplitr
  · ipureintro
    obtain ⟨w, tvs, hlen, hbytes, hrd⟩ := Hen
    refine ⟨ECycle gen c (K (.Ok (w, none))) none,
      ewgWs σ c (loadPostRun (σ.wgws c) (classify req.access_kind).akSync (paZ req.pa)
        (tvs.map Prod.fst)), ?_⟩
    simp only [ecycleStep, emonadStep, hdev, Bool.false_eq_true, ↓reduceIte]
    exact Or.inr ⟨hif, Or.inl ⟨hlat, w, tvs, hlen, hbytes, hrd, rfl, rfl⟩⟩
  inext
  iintro %e' %σ' %hcy
  simp only [ecycleStep, emonadStep, hdev, Bool.false_eq_true, ↓reduceIte] at hcy
  rcases hcy with ⟨hbad, -⟩ | ⟨-, ⟨-, w, tvs, hlen, hbytes, hrd, rfl, rfl⟩ | ⟨hbad, -⟩⟩
  · simp [hif] at hbad
  rotate_left
  · simp [hlat] at hbad
  imod Hk $$ %w %tvs %hlen %hbytes %hrd with ⟨%Hnvok, Hlat0, Hcont⟩
  imod hartWsUpdate c (σ.wgws c) (σ.wgws c)
    (loadPostRun (σ.wgws c) (classify req.access_kind).akSync (paZ req.pa) (tvs.map Prod.fst))
    $$ [$Hwsa $Hws] with ⟨Hwsa, Hws⟩
  imodintro
  isplitl [Hcl Hlog Hlat0 Hwsa]
  · rw [weakStateInterpWs]
    iapply Hcl $$ %_ %σ.wglog %(Nat.le_refl _)
      %(loadPostRunBounded _ _ _ _ _ (Hbnd c) (readOkTsBounded _ _ _ _ _ _ _ hrd))
      %(nvHartCohStep _ c _ _ (noViolationHart _ _ c Hnv)
        (fun a hlt => nvByteOfOk _ _ _ _ (Hnvok a hlt)))
      %(appNilOwn σ.wglog c) %Hwf Hlog Hlat0 Hwsa
  · iapply Hcont $$ Hws

/-! ### 5c. THE FETCH — a DERIVED rule for reading NEVER-WRITTEN text (O2, the i-cache read)

Kernel text is immutable in the verified configuration: `etextWord` is a big-op of persistent
era-image elements ("the latest write to `a` is the boot image, at timestamp 0").  The rule
opens and closes the interpretation itself: NO caller callback, NO per-event read obligation,
NO φ payment, and — under O2 — NO view move: the continuation gets the hart's view back
UNCHANGED (Rocq's `efetch_ws` disappears, deviation 2). -/

def etext (a : Int) (b : BitVec 8) : IProp GF := wlatPointsto (GF := GF) a DFrac.discard 0 b

instance etext_persistent (a : Int) (b : BitVec 8) : Persistent (etext (GF := GF) a b) := by
  unfold etext; infer_instance

def etextWord (a : Int) (n : Nat) (w : BitVec (8 * n)) : IProp GF :=
  iprop([∗list] j ∈ List.range' 0 n, etext (GF := GF) (a + ((j : Nat) : Int)) (nthByte w j))

instance etextWord_persistent (a : Int) (n : Nat) (w : BitVec (8 * n)) :
    Persistent (etextWord (GF := GF) a n w) := by
  unfold etextWord; infer_instance

/-- The text's per-byte fact, off the persistent elements (Lean-only; Rocq inlines it). -/
theorem etextWordLatest (img : Mem) (log : List Wmsg) (a : Int) (n : Nat) (w : BitVec (8 * n)) :
    wlatInterp (GF := GF) img log ∗ etextWord (GF := GF) a n w ⊢
      ⌜∀ j : Nat, j < n → latestVal (imgZ img) log (a + (j : Int)) 0 (nthByte w j)⌝ := by
  by_cases hall : ∀ j : Nat, j < n → latestVal (imgZ img) log (a + (j : Int)) 0 (nthByte w j)
  · exact pure_intro hall
  · have hex : ∃ j, j < n ∧ ¬ latestVal (imgZ img) log (a + (j : Int)) 0 (nthByte w j) := by
      apply Classical.byContradiction
      intro hne
      exact hall fun j hj => Classical.byContradiction fun hp => hne ⟨j, hj, hp⟩
    obtain ⟨j, hj, hnp⟩ := hex
    have hlk : (List.range' 0 n)[j]? = some j := by simp [hj]
    unfold etextWord
    refine (sep_mono_right (BigSepL.bigSepL_lookup
      (Φ := fun _ (j : Nat) => etext (GF := GF) (a + ((j : Nat) : Int)) (nthByte w j)) hlk)).trans ?_
    exact (wlatLookup img log _ DFrac.discard 0 _).trans (pure_mono fun h => absurd h hnp)

theorem ewpEvFetch (gen : Nat) (c : CPU) (n va : Nat)
    (req : Mem_read_request n va Arch.pa Arch.translation Arch.arch_ak)
    (K : Result (BitVec (8 * n) × Option Bool) Arch.abort → SailM Unit) (w : BitVec (8 * n))
    (ws : Wstate) :
    gen = 0 → devAddr req.pa = false → (classify req.access_kind).akIfetch = true →
    etextWord (GF := GF) (paZ req.pa) n w ∗ hartWs (GF := GF) c ws ∗
      ▷ (hartWs (GF := GF) c ws -∗
          ewpTriv (hlc := hlc) (GF := GF) ⊤ (ECycle gen c (K (.Ok (w, none))) none)) ⊢
    ewpTriv (hlc := hlc) (GF := GF) ⊤ (ECycle gen c (.impure (.ok (.memRead n va req)) K) none) := by
  intro hgen hdev hif
  iintro ⟨#Ht, Hws, H⟩
  iapply ewpEcycle gen c _ none hgen
  iintro %σ Hσ
  icases weakStateInterpMem σ c $$ Hσ with ⟨%Hbnd, %Hnv, %Hwf, Hlog, Hlat0, Hwsa, Hcl⟩
  ihave ⟨%htext, Hlat0, -⟩ := persistent_entails_right
    (etextWordLatest σ.wgimg σ.wglog (paZ req.pa) n w) $$ [Hlat0]
  · isplitl [Hlat0]
    · iexact Hlat0
    · iexact Ht
  -- ENABLEDNESS: the all-zero read is admissible
  let tvs0 : List (Nat × BitVec 8) := (List.range' 0 n).map (fun j => (0, nthByte w j))
  have hlen0 : tvs0.length = n := by simp [tvs0]
  have hlk0 : ∀ j, j < n → tvs0[j]? = some (0, nthByte w j) := by
    intro j hj; simp [tvs0, hj]
  have hbytes0 : ∀ j, j < n → (tvs0.map Prod.snd)[j]? = some (nthByte w j) := by
    intro j hj; rw [List.getElem?_map, hlk0 j hj]; rfl
  have hok0 : ifetchOk (imgZ σ.wgimg) σ.wglog (σ.wgitv c) (paZ req.pa) tvs0 := by
    intro j t v hj
    have hjlt : j < n := by have := lookup_lt_Some hj; omega
    rw [hlk0 j hjlt] at hj
    simp only [Option.some.injEq, Prod.mk.injEq] at hj
    obtain ⟨rfl, rfl⟩ := hj
    obtain ⟨hv, hno⟩ := htext j hjlt
    refine ⟨hv, fun hw => hno ?_⟩
    exact writesInMonoHi _ _ _ _ _ (Nat.min_le_right _ _) (writesInClip _ _ _ _ hw)
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro Hmask
  isplitr
  · ipureintro
    refine ⟨ECycle gen c (K (.Ok (w, none))) none, σ, ?_⟩
    dsimp only [ecycleStep, emonadStep]
    rw [if_neg (by simp [hdev])]
    exact Or.inl ⟨hif, w, tvs0, hlen0, hbytes0, hok0, rfl, rfl⟩
  inext
  iintro %e' %σ' %hcy
  imod Hmask
  simp only [ecycleStep, emonadStep, hdev, Bool.false_eq_true, ↓reduceIte] at hcy
  rcases hcy with ⟨-, w', tvs, hlen, hbytes, hok, rfl, hσ'⟩ | ⟨hbad, -⟩
  rotate_left
  · simp [hif] at hbad
  -- UNIQUENESS: every admissible read is the certified word
  have hpin : ∀ (j t : Nat) (v : BitVec 8), tvs[j]? = some (t, v) → t = 0 ∧ v = nthByte w j := by
    intro j t v hj
    have hjlt : j < n := by have := lookup_lt_Some hj; omega
    exact etextBytePin σ c (classify req.access_kind) _ t v _ (htext j hjlt)
      (ifetchOkWbyteOk σ c _ _ tvs j t v hif hok hj)
  have hww : w' = w := by
    apply bvEqOfBytes
    intro j hj
    obtain ⟨⟨t, v⟩, hj2⟩ : ∃ p, tvs[j]? = some p :=
      ⟨tvs[j]'(by omega), List.getElem?_eq_getElem (by omega)⟩
    have h2 := hbytes j hj
    rw [List.getElem?_map, hj2] at h2
    simp only [Option.map_some, Option.some.injEq] at h2
    rw [← h2]
    exact (hpin j t v hj2).2
  subst hww
  subst σ'
  imodintro
  isplitl [Hcl Hlog Hlat0 Hwsa]
  · iapply weakStateInterpStoreId σ c
    iapply Hcl $$ %(σ.wgws c) %σ.wglog %(Nat.le_refl _) %(Hbnd c) %(noViolationHart _ _ c Hnv)
      %(appNilOwn σ.wglog c) %Hwf Hlog Hlat0 Hwsa
  · iapply H $$ Hws

end ram

/-! ## 6. THE SPLIT EXCLUSIVE PAIR — the lock acquire, at TWO events

`ewpEvExload` is `ewpEvLoad`'s rule at an EXCLUSIVE access kind (the post-state banks the
reservation); `ewpEvExstore` is `ewpEvStore`'s rule at an exclusive kind, PLUS the retry
self-loop absorbed by Löb, on `ewpEcycleLc` (deviation 3: at `hlc := .hasLC`). -/

def eexlOk (σ : WGState) (c : CPU) (n va : Nat)
    (req : Mem_read_request n va Arch.pa Arch.translation Arch.arch_ak) (w : BitVec (8 * n))
    (tvs : List (Nat × BitVec 8)) : Prop :=
  tvs.length = n ∧ (∀ j : Nat, j < n → (tvs.map Prod.snd)[j]? = some (nthByte w j)) ∧
  readOk (imgZ σ.wgimg) σ.wglog (σ.wgws c) (classify req.access_kind).akSync false (paZ req.pa) tvs

/-- The successor's view: the load's post-state PLUS the reservation. -/
def eexlWs (σ : WGState) (c : CPU) (n va : Nat)
    (req : Mem_read_request n va Arch.pa Arch.translation Arch.arch_ak)
    (tvs : List (Nat × BitVec 8)) : Wstate :=
  exloadPostRunD (σ.wgws c) (classify req.access_kind).akSync
    (srcsView (σ.wgws c) (depsAsrc (edeps σ c))) (paZ req.pa) (tvs.map Prod.fst)

section excl

variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [WeakGS GF]

/-- 6a. THE EXCLUSIVE READ. -/
theorem ewpEvExload (gen : Nat) (c : CPU) (n va : Nat)
    (req : Mem_read_request n va Arch.pa Arch.translation Arch.arch_ak)
    (K : Result (BitVec (8 * n) × Option Bool) Arch.abort → SailM Unit) (ws : Wstate) :
    gen = 0 → devAddr req.pa = false →
    (classify req.access_kind).akIfetch = false → (classify req.access_kind).akLatest = true →
    hartWs (GF := GF) c ws ∗
      (∀ σ : WGState, ⌜σ.wgws c = ws⌝ -∗ ⌜wlogWf σ.wglog⌝ -∗ ⌜wsBounded ws σ.wglog.length⌝ -∗
        wlogLb (GF := GF) σ.wglog -∗ wlatInterp (GF := GF) σ.wgimg σ.wglog ={⊤,∅}=∗
        ⌜∃ (w : BitVec (8 * n)) (tvs : List (Nat × BitVec 8)), eexlOk σ c n va req w tvs⌝ ∗
        ▷ (∀ (w : BitVec (8 * n)) (tvs : List (Nat × BitVec 8)),
            ⌜eexlOk σ c n va req w tvs⌝ ={∅,⊤}=∗
            ⌜∀ a : Int, coh ws a < coh (eexlWs σ c n va req tvs) a → nvOk σ.wglog c a⌝ ∗
            wlatInterp (GF := GF) σ.wgimg σ.wglog ∗
            (hartWs (GF := GF) c (eexlWs σ c n va req tvs) -∗
              ewpTriv (hlc := hlc) (GF := GF) ⊤ (ECycle gen c (K (.Ok (w, none))) none)))) ⊢
    ewpTriv (hlc := hlc) (GF := GF) ⊤ (ECycle gen c (.impure (.ok (.memRead n va req)) K) none) := by
  intro hgen hdev hif hlatest
  iintro ⟨Hws, Hk⟩
  iapply ewpEcycle gen c _ none hgen
  iintro %σ Hσ
  icases weakStateInterpMem σ c $$ Hσ with ⟨%Hbnd, %Hnv, %Hwf, Hlog, Hlat0, Hwsa, Hcl⟩
  ihave ⟨%hws, Hwsa, Hws⟩ := persistent_entails_right (hartWsAgree c (σ.wgws c) ws) $$ [Hwsa Hws]
  · iframe Hwsa Hws
  subst hws
  icases wlogSnapshot σ.wglog $$ Hlog with ⟨Hlog, #Hlb⟩
  imod Hk $$ %σ %rfl %Hwf %(Hbnd c) Hlb Hlat0 with ⟨%Hen, Hk⟩
  imodintro
  isplitr
  · ipureintro
    obtain ⟨w, tvs, hlen, hbytes, hrd⟩ := Hen
    refine ⟨ECycle gen c (K (.Ok (w, none))) none, ewgWs σ c (eexlWs σ c n va req tvs), ?_⟩
    simp only [ecycleStep, emonadStep, hdev, Bool.false_eq_true, ↓reduceIte]
    exact Or.inr ⟨hif, Or.inr ⟨hlatest, w, tvs, hlen, hbytes, hrd, rfl, rfl⟩⟩
  inext
  iintro %e' %σ' %hcy
  simp only [ecycleStep, emonadStep, hdev, Bool.false_eq_true, ↓reduceIte] at hcy
  rcases hcy with ⟨hbad, -⟩ | ⟨-, ⟨hbad, -⟩ | ⟨-, w, tvs, hlen, hbytes, hrd, rfl, rfl⟩⟩
  · simp [hif] at hbad
  · simp [hlatest] at hbad
  imod Hk $$ %w %tvs %⟨hlen, hbytes, hrd⟩ with ⟨%Hnvok, Hlat0, Hcont⟩
  imod hartWsUpdate c (σ.wgws c) (σ.wgws c) (eexlWs σ c n va req tvs) $$ [$Hwsa $Hws]
    with ⟨Hwsa, Hws⟩
  unfold eexlWs
  imodintro
  isplitl [Hcl Hlog Hlat0 Hwsa]
  · rw [weakStateInterpWs]
    iapply Hcl $$ %_ %σ.wglog %(Nat.le_refl _)
      %(exloadPostRunDBounded _ _ _ _ _ _ (Hbnd c) (srcsViewBounded _ _ _ (Hbnd c))
        (readOkTsBounded _ _ _ _ _ _ _ hrd))
      %(nvHartCohStep _ c _ _ (noViolationHart _ _ c Hnv)
        (fun a hlt => nvByteOfOk _ _ _ _ (Hnvok a hlt)))
      %(appNilOwn σ.wglog c) %Hwf Hlog Hlat0 Hwsa
  · iapply Hcont $$ Hws

end excl

section exstore

variable {GF : BundledGFunctors} [MachGS HasLC.hasLC GF] [WeakGS GF]

/-- 6b. THE CONDITIONAL WRITE, with the retry absorbed by Löb (deviations 3, 5). -/
theorem ewpEvExstore (gen : Nat) (c : CPU) (n va : Nat)
    (req : Mem_write_request n va Arch.pa Arch.translation Arch.arch_ak)
    (K : Result (Option Bool) Arch.abort → SailM Unit) (v : BitVec (8 * n)) (ws : Wstate) :
    gen = 0 → devAddr req.pa = false → n ≠ 0 → req.value = some v →
    (classify req.access_kind).akLatest = true → accWf req.pa n →
    hartWs (GF := GF) c ws ∗
      (∀ σ : WGState, ⌜σ.wgws c = ws⌝ -∗ ⌜wlogWf σ.wglog⌝ -∗ ⌜wsBounded ws σ.wglog.length⌝ -∗
        ⌜exwinOk σ.wglog c.val ws (paZ req.pa) n (σ.wglog.length + 1)⌝ -∗
        wlogLb (GF := GF) σ.wglog -∗ wlatInterp (GF := GF) σ.wgimg σ.wglog ={⊤,∅}=∗
        ▷ |={∅,⊤}=> iprop(
          ⌜∀ j : Nat, j < n → nvOk σ.wglog c (WeakInterp.accAddr req.pa j)⌝ ∗
           wlatInterp (GF := GF) σ.wgimg
             (σ.wglog ++ [wwriteMsg (some c.val) (wmClassOf (classify req.access_kind) ws) req.pa n v]) ∗
           (∀ (va' : Nat) (vd : Nat),
             hartWs (GF := GF) c (storePostRunD ws (classify req.access_kind).akSync va' vd
               (paZ req.pa) n (σ.wglog.length + 1)) -∗
             ewpTriv (hlc := .hasLC) (GF := GF) ⊤ (ECycle gen c (K (.Ok (some true))) none)))) ⊢
    ewpTriv (hlc := .hasLC) (GF := GF) ⊤
      (ECycle gen c (.impure (.ok (.memWrite n va req)) K) none) := by
  intro hgen hdev hn hv hlatest hacc
  iintro ⟨Hws, Hk⟩
  iloeb as IH
  iapply ewpEcycleLc gen c _ none hgen
  iintro %σ Hσ
  icases weakStateInterpMem σ c $$ Hσ with ⟨%Hbnd, %Hnv, %Hwf, Hlog, Hlat0, Hwsa, Hcl⟩
  ihave ⟨%hws, Hwsa, Hws⟩ := persistent_entails_right (hartWsAgree c (σ.wgws c) ws) $$ [Hwsa Hws]
  · iframe Hwsa Hws
  subst hws
  icases wlogSnapshot σ.wglog $$ Hlog with ⟨Hlog, #Hlb⟩
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro Hmask
  isplitr
  · -- REDUCIBILITY IS FREE: the self-loop is always available
    ipureintro
    refine ⟨ECycle gen c (.impure (.ok (.memWrite n va req)) K) none, σ, ?_⟩
    dsimp only [ecycleStep, emonadStep]
    rw [if_neg (by simp [hdev]), hv]
    exact ⟨hn, Or.inr ⟨hlatest, Or.inr ⟨rfl, rfl⟩⟩⟩
  inext
  iintro %e' %σ' %hcy Hlc
  simp only [ecycleStep, emonadStep, hdev, hv, Bool.false_eq_true, ↓reduceIte] at hcy
  rcases hcy.2 with ⟨hbad, -⟩ | ⟨-, ⟨hex, rfl, rfl⟩ | ⟨rfl, hσ'⟩⟩
  · simp [hlatest] at hbad
  · -- THE CONDITIONAL WRITE FIRED: the store's proof, the callback's `▷` paid by the credit
    imod Hmask
    imod Hk $$ %σ %rfl %Hwf %(Hbnd c) %hex Hlb Hlat0 with Hk
    imod (lc_fupd_elim_later (E := ∅)) $$ Hlc Hk with Hk
    imod Hk with ⟨%Hnvok, Hlat, Hcont⟩
    imod wlogUpdate σ.wglog
      [wwriteMsg (some c.val) (wmClassOf (classify req.access_kind) (σ.wgws c)) req.pa n v] $$ Hlog
      with Hlog
    imod hartWsUpdate c (σ.wgws c) (σ.wgws c)
      (storePostRunD (σ.wgws c) (classify req.access_kind).akSync
        (srcsView (σ.wgws c) (depsAsrc (edeps σ c))) (srcsView (σ.wgws c) (depsVsrc (edeps σ c)))
        (paZ req.pa) n (σ.wglog.length + 1)) $$ [$Hwsa $Hws] with ⟨Hwsa, Hws⟩
    imodintro
    isplitl [Hcl Hlog Hlat Hwsa]
    · rw [← wwriteMsgWbytes]
      iapply Hcl $$ %_ %_ %(by simp) %(storeBounded _ c _ _ _ n v _ _ _ (Hbnd c)
          (srcsViewBounded _ _ _ (Hbnd c)) (srcsViewBounded _ _ _ (Hbnd c)))
        %(storeNvHart _ c _ _ _ n v _ _ _ (noViolationHart _ _ c Hnv) Hnvok)
        %⟨_, rfl, storeMsgOwn c _ req.pa n v⟩ %(storeLogWf _ c _ _ n v Hwf hacc) Hlog Hlat Hwsa
    · iapply Hcont $$ %_ %_ Hws
  · -- THE RETRY SELF-LOOP: nothing was consumed, the Löb hypothesis closes it
    subst σ'
    imod Hmask
    imodintro
    isplitl [Hcl Hlog Hlat0 Hwsa]
    · iapply weakStateInterpStoreId σ c
      iapply Hcl $$ %(σ.wgws c) %σ.wglog %(Nat.le_refl _) %(Hbnd c) %(noViolationHart _ _ c Hnv)
        %(appNilOwn σ.wglog c) %Hwf Hlog Hlat0 Hwsa
    · iapply IH $$ Hws Hk

end exstore

/-! ## 7. THE CERTIFICATION ADAPTER

One combinator per event kind: ONE computed equation (a small projection) plus ONE memory-event
rule, the successor cursor handed on as the unevaluated composition. -/

theorem efenceApplyCoh (ws : Wstate) (o : Option (Bool × Bool × Bool × Bool)) (a : Int) :
    coh (efenceApply ws o) a = coh ws a := by
  match o with
  | some (_, _, _, _) => rfl
  | none => rfl

theorem efenceApplyBounded (ws : Wstate) (n : Nat) (o : Option (Bool × Bool × Bool × Bool)) :
    wsBounded ws n → wsBounded (efenceApply ws o) n := by
  intro hb
  match o with
  | some (pr, pw, sr, sw) => exact fencePostBounded _ _ _ _ _ _ hb
  | none => exact hb

section adapter

variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [WeakGS GF]

/-- 7a. The BARRIER event: no φ payment (a fence moves no coherence floor); Stage B's `fence.i`
instruction view is invisible to the interpretation (`weakStateInterpBar`). -/
theorem ewpEvBarrier (gen : Nat) (c : CPU) (b : barrier_kind) (K : Unit → SailM Unit) (ws : Wstate) :
    gen = 0 →
    hartWs (GF := GF) c ws ∗
      ▷ (hartWs (GF := GF) c (efenceApply ws (ebarNow b)) -∗
          ewpTriv (hlc := hlc) (GF := GF) ⊤ (ECycle gen c (K ()) (ebarPark b))) ⊢
    ewpTriv (hlc := hlc) (GF := GF) ⊤ (ECycle gen c (.impure (.ok (.barrier b)) K) none) := by
  intro hgen
  iintro ⟨Hws, H⟩
  iapply ewpEcycle gen c _ none hgen
  iintro %σ Hσ
  icases weakStateInterpMem σ c $$ Hσ with ⟨%Hbnd, %Hnv, %Hwf, Hlog, Hlat, Hwsa, Hcl⟩
  ihave ⟨%hws, Hwsa, Hws⟩ := persistent_entails_right (hartWsAgree c (σ.wgws c) ws) $$ [Hwsa Hws]
  · iframe Hwsa Hws
  subst hws
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro Hmask
  isplitr
  · ipureintro
    exact ⟨_, _, rfl, rfl⟩
  inext
  iintro %e' %σ' %hcy
  obtain ⟨rfl, rfl⟩ := hcy
  imod Hmask
  imod hartWsUpdate c (σ.wgws c) (σ.wgws c) (efenceApply (σ.wgws c) (ebarNow b))
    $$ [$Hwsa $Hws] with ⟨Hwsa, Hws⟩
  imodintro
  isplitl [Hcl Hlog Hlat Hwsa]
  · rw [weakStateInterpBar]
    iapply Hcl $$ %(efenceApply (σ.wgws c) (ebarNow b)) %σ.wglog %(Nat.le_refl _)
      %(efenceApplyBounded _ _ _ (Hbnd c))
      %(nvHartOfCohEq _ c _ _ (noViolationHart _ _ c Hnv) (fun a => efenceApplyCoh _ _ a))
      %(appNilOwn σ.wglog c) %Hwf Hlog Hlat Hwsa
  · iapply H $$ Hws

/-- 7b. The five chaining combinators. -/
theorem ewpEvSeqRet (gen : Nat) (c : CPU) (D : List Register) (nn : Nat) (x : ecur) (ws : Wstate) :
    gen = 0 → enodeTag (esil nn D x).2 = 0 →
    hartWs (GF := GF) c ws ∗ eregFrame (hlc := hlc) (GF := GF) c x.1 D ∗
      (∀ ws' : Wstate, ⌜wsDepmove ws ws'⌝ -∗ hartWs (GF := GF) c ws' -∗
          eregFrame (hlc := hlc) (GF := GF) c (esil nn D x).1 D -∗
          ewpTriv (hlc := hlc) (GF := GF) ⊤ (ELoop gen c)) ⊢
    ewpTriv (hlc := hlc) (GF := GF) ⊤ (ECycle gen c x.2 none) := by
  intro hgen htag
  obtain ⟨u, hu⟩ := enodeTagRet _ htag
  iintro ⟨Hws, Hrf, H⟩
  iapply ewpEvBatch gen c D nn x ws hgen
  iframe Hws Hrf
  iintro %ws' %hd Hws Hrf
  rw [hu]
  iapply ewpEvRet gen c u hgen
  iapply H $$ %ws' %hd Hws Hrf

theorem ewpEvSeqBarrier (gen : Nat) (c : CPU) (D : List Register) (nn : Nat) (x : ecur)
    (b : barrier_kind) (ws : Wstate) :
    gen = 0 → ebarAt (esil nn D x).2 = some b →
    hartWs (GF := GF) c ws ∗ eregFrame (hlc := hlc) (GF := GF) c x.1 D ∗
      ▷ (∀ ws0 : Wstate, ⌜wsDepmove ws ws0⌝ -∗
          hartWs (GF := GF) c (efenceApply ws0 (ebarNow b)) -∗
          eregFrame (hlc := hlc) (GF := GF) c (esil nn D x).1 D -∗
          ewpTriv (hlc := hlc) (GF := GF) ⊤ (ECycle gen c (ecurBar (esil nn D x)).2 (ebarPark b))) ⊢
    ewpTriv (hlc := hlc) (GF := GF) ⊤ (ECycle gen c x.2 none) := by
  intro hgen hbar
  obtain ⟨K, HK, Hres⟩ := ebarAtInv _ _ hbar
  iintro ⟨Hws, Hrf, H⟩
  iapply ewpEvBatch gen c D nn x ws hgen
  iframe Hws Hrf
  iintro %ws0 %hd Hws Hrf
  rw [HK]
  iapply ewpEvBarrier gen c b K ws0 hgen
  iframe Hws
  inext
  iintro Hws
  have Hres' : (ecurBar (esil nn D x)).2 = K () := Hres
  rw [← Hres']
  iapply H $$ %ws0 %hd Hws Hrf

theorem ewpEvSeqStore (gen : Nat) (c : CPU) (D : List Register) (nn : Nat) (x : ecur) (n va : Nat)
    (req : Mem_write_request n va Arch.pa Arch.translation Arch.arch_ak) (v : BitVec (8 * n))
    (ws : Wstate) :
    gen = 0 → ewriteReqAt n va (esil nn D x).2 = some req → devAddr req.pa = false → n ≠ 0 →
    req.value = some v → (classify req.access_kind).akLatest = false → accWf req.pa n →
    hartWs (GF := GF) c ws ∗ eregFrame (hlc := hlc) (GF := GF) c x.1 D ∗
      (∀ ws0 : Wstate, ⌜wsDepmove ws ws0⌝ -∗ ∀ σ : WGState,
        ⌜σ.wgws c = ws0⌝ -∗ ⌜wlogWf σ.wglog⌝ -∗ ⌜wsBounded ws0 σ.wglog.length⌝ -∗
        wlogLb (GF := GF) σ.wglog -∗ wlatInterp (GF := GF) σ.wgimg σ.wglog ={⊤,∅}=∗
        ▷ |={∅,⊤}=> iprop(
          ⌜∀ j : Nat, j < n → nvOk σ.wglog c (WeakInterp.accAddr req.pa j)⌝ ∗
          wlatInterp (GF := GF) σ.wgimg
            (σ.wglog ++ [wwriteMsg (some c.val) (wmClassOf (classify req.access_kind) ws0) req.pa n v]) ∗
          (∀ (va' : Nat) (vd : Nat),
            hartWs (GF := GF) c (storePostRunD ws0 (classify req.access_kind).akSync va' vd
              (paZ req.pa) n (σ.wglog.length + 1)) -∗
            eregFrame (hlc := hlc) (GF := GF) c (esil nn D x).1 D -∗
            ewpTriv (hlc := hlc) (GF := GF) ⊤ (ECycle gen c (ecurWrite (esil nn D x)).2 none)))) ⊢
    ewpTriv (hlc := hlc) (GF := GF) ⊤ (ECycle gen c x.2 none) := by
  intro hgen hnode hdev hn hv hlat hacc
  obtain ⟨K, HK, Hres⟩ := ewriteReqAtInv n va _ req hnode
  iintro ⟨Hws, Hrf, Hk⟩
  iapply ewpEvBatch gen c D nn x ws hgen
  iframe Hws Hrf
  iintro %ws0 %hd Hws Hrf
  rw [HK]
  iapply ewpEvStore gen c n va req K v ws0 hgen hdev hn hv hlat hacc
  iframe Hws
  iintro %σ %hws %hwf %hbnd #Hlb Hlat
  imod Hk $$ %ws0 %hd %σ %hws %hwf %hbnd Hlb Hlat with Hk
  imodintro
  inext
  imod Hk with ⟨%Hpay, Hlat, Hcont⟩
  imodintro
  iframe Hlat
  isplitr
  · ipureintro; exact Hpay
  iintro %va' %vd Hws
  have Hres' : (ecurWrite (esil nn D x)).2 = K (.Ok (some true)) := Hres
  rw [← Hres']
  iapply Hcont $$ %va' %vd Hws Hrf

theorem ewpEvSeqLoad (gen : Nat) (c : CPU) (D : List Register) (nn : Nat) (x : ecur) (n va : Nat)
    (req : Mem_read_request n va Arch.pa Arch.translation Arch.arch_ak) (ws : Wstate) :
    gen = 0 → ereadReqAt n va (esil nn D x).2 = some req → devAddr req.pa = false →
    (classify req.access_kind).akIfetch = false → (classify req.access_kind).akLatest = false →
    hartWs (GF := GF) c ws ∗ eregFrame (hlc := hlc) (GF := GF) c x.1 D ∗
      (∀ ws0 : Wstate, ⌜wsDepmove ws ws0⌝ -∗ ∀ σ : WGState,
        ⌜σ.wgws c = ws0⌝ -∗ ⌜wlogWf σ.wglog⌝ -∗ ⌜wsBounded ws0 σ.wglog.length⌝ -∗
        wlogLb (GF := GF) σ.wglog -∗ wlatInterp (GF := GF) σ.wgimg σ.wglog ={⊤,∅}=∗
        ⌜∃ (w : BitVec (8 * n)) (tvs : List (Nat × BitVec 8)),
          tvs.length = n ∧ (∀ j : Nat, j < n → (tvs.map Prod.snd)[j]? = some (nthByte w j)) ∧
          readOk (imgZ σ.wgimg) σ.wglog ws0 (classify req.access_kind).akSync false (paZ req.pa) tvs⌝ ∗
        ▷ (∀ (w : BitVec (8 * n)) (tvs : List (Nat × BitVec 8)),
            ⌜tvs.length = n⌝ -∗
            ⌜∀ j : Nat, j < n → (tvs.map Prod.snd)[j]? = some (nthByte w j)⌝ -∗
            ⌜readOk (imgZ σ.wgimg) σ.wglog ws0 (classify req.access_kind).akSync false (paZ req.pa)
              tvs⌝ ={∅,⊤}=∗
            ⌜∀ a : Int, coh ws0 a <
                coh (loadPostRun ws0 (classify req.access_kind).akSync (paZ req.pa)
                  (tvs.map Prod.fst)) a →
              nvOk σ.wglog c a⌝ ∗
            wlatInterp (GF := GF) σ.wgimg σ.wglog ∗
            (hartWs (GF := GF) c (loadPostRun ws0 (classify req.access_kind).akSync (paZ req.pa)
                (tvs.map Prod.fst)) -∗
              eregFrame (hlc := hlc) (GF := GF) c (esil nn D x).1 D -∗
              ewpTriv (hlc := hlc) (GF := GF) ⊤
                (ECycle gen c (ecurRead w.toNat (esil nn D x)).2 none)))) ⊢
    ewpTriv (hlc := hlc) (GF := GF) ⊤ (ECycle gen c x.2 none) := by
  intro hgen hnode hdev hif hlat
  obtain ⟨K, HK, Hres⟩ := ereadReqAtInv n va _ req hnode
  iintro ⟨Hws, Hrf, Hk⟩
  iapply ewpEvBatch gen c D nn x ws hgen
  iframe Hws Hrf
  iintro %ws0 %hd Hws Hrf
  rw [HK]
  iapply ewpEvLoad gen c n va req K ws0 hgen hdev hif hlat
  iframe Hws
  iintro %σ %hws %hwf %hbnd #Hlb Hlat0
  imod Hk $$ %ws0 %hd %σ %hws %hwf %hbnd Hlb Hlat0 with ⟨%Hen, Hk⟩
  imodintro
  isplitr
  · ipureintro; exact Hen
  inext
  iintro %w %tvs %H1 %H2 %H3
  imod Hk $$ %w %tvs %H1 %H2 %H3 with ⟨%Hpay, Hlat0, Hcont⟩
  imodintro
  iframe Hlat0
  isplitr
  · ipureintro; exact Hpay
  iintro Hws
  have Hres' : (ecurRead w.toNat (esil nn D x)).2 = K (.Ok (w, none)) := Hres w
  rw [← Hres']
  iapply Hcont $$ Hws Hrf

/-- 7c. THE FETCH COMBINATOR: the stretch, then §5c's derived rule — no callback, no read
obligation, no φ payment, and (O2) no view move. -/
theorem ewpEvSeqFetch (gen : Nat) (c : CPU) (D : List Register) (nn : Nat) (x : ecur) (n va : Nat)
    (req : Mem_read_request n va Arch.pa Arch.translation Arch.arch_ak) (w : BitVec (8 * n))
    (ws : Wstate) :
    gen = 0 → ereadReqAt n va (esil nn D x).2 = some req → devAddr req.pa = false →
    (classify req.access_kind).akIfetch = true →
    etextWord (GF := GF) (paZ req.pa) n w ∗ hartWs (GF := GF) c ws ∗
      eregFrame (hlc := hlc) (GF := GF) c x.1 D ∗
      ▷ (∀ ws0 : Wstate, ⌜wsDepmove ws ws0⌝ -∗ hartWs (GF := GF) c ws0 -∗
          eregFrame (hlc := hlc) (GF := GF) c (esil nn D x).1 D -∗
          ewpTriv (hlc := hlc) (GF := GF) ⊤ (ECycle gen c (ecurRead w.toNat (esil nn D x)).2 none)) ⊢
    ewpTriv (hlc := hlc) (GF := GF) ⊤ (ECycle gen c x.2 none) := by
  intro hgen hnode hdev hif
  obtain ⟨K, HK, Hres⟩ := ereadReqAtInv n va _ req hnode
  iintro ⟨#Ht, Hws, Hrf, H⟩
  iapply ewpEvBatch gen c D nn x ws hgen
  iframe Hws Hrf
  iintro %ws0 %hd Hws Hrf
  rw [HK]
  iapply ewpEvFetch gen c n va req K w ws0 hgen hdev hif
  iframe Ht Hws
  inext
  iintro Hws
  have Hres' : (ecurRead w.toNat (esil nn D x)).2 = K (.Ok (w, none)) := Hres w
  rw [← Hres']
  iapply H $$ %ws0 %hd Hws Hrf

end adapter

end Weak
