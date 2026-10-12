/-
Weak: **K1 GATE: the graph violation SUBSUMES the operational one** (the graph
restatement `AxViol.gviolationHart` is not WEAKER than
`WeakRobust.violationHart`).

Rocq: `iris/AxViolSubsume.v` @ xxvzwolszwmp.

The Rocq header, in substance (design: `weak-memory-lb-axsl.md` §0, K1).  PURE
(no Iris), a leaf.  Companion of `AxViol`; THIS file is the residual its header
names: on a graph REALIZED by a promise-free run,
`¬ gviolationHart nh G ⇒ ¬ violationHart c` for every realized configuration
`c` (`gviolationSubsumes`).

THE REALIZATION RELATION (the repo's, composed; nothing new): graph
`G = graphOfCand cd`; exec `E = candExec cd` with `execWf E` (from
`srvwmoRealizable` or `candReachable`); pf configuration `c` with
`cfgMatchd c (stt E n)` (same image, same log, per-agent `wsEqr`, hence the
same per-byte `coh` floor).  The proof goes through the AXIOMATIC machine's
exec; the pf run itself is not consulted.  The exec ↔ graph side is an explicit
interface record `ExecGraph E G eid`, PROVED for `graphOfCand`
(`candExecGraph`).

THE TWO RESIDUALS OF `AxViol`'s header, DISCHARGED HERE: (i) the `coh` floor
is also raised by a read's PRE-VIEW — `loadPostRunCohInv` + `readable` (the
message itself is a write of `a` in `(t, max vpre coh]`, so `p + 1 ≤ vpre`
forces `p + 1 ≤ t`); `cohTouched` is the CONVERSE of `touchesCoh`.  (ii) a
forwarded store's banked view is bounded by its timestamp (`storePost` banks
`(t, 0)`, D-7r): `AxViolSubsume.fwdLe` is a run invariant (`execFwdLe`) and
`fwdView ws aq a t ≤ t` (`fwdViewLe`).

FIELD MAPPING (`violationExecGraph`): message `p` (ts `p + 1`) ↦ the write
step `kw` with `evTs (ev_at kw) = p + 1` (`tsWriter`), event `eid kw`,
`gwix = p + 1` (`egWix`); `clsOf m = SCowned` ↦ `lbCls = WCplain`;
`p + 1 ≤ obsFlr c j a` ↦ `cohTouched` (a READ at `t ≥ p + 1`, or a WRITE at
`t = evTs ≠ p + 1`, strict by `evTsInj`); `¬ pubOf c (p + 1)` ↦
`¬ gpubBefore` (`gpubBeforePublished`); the read arm's forwarding clause
reduces to the same, since on `graphOfCand` a read's source is gmo-before the
read.

NON-VACUITY (`subsumeSat`): the 2-hart racy cand `wcd` is machine-reachable
(`wcdWf`); a matched configuration `wcfg` VIOLATES (`wcfgViolation`); the
theorem then yields `gdviolationHart 2 viol2` (`wcdGraphViol2`), the witness
`AxViol.gviolationSat` exhibits directly.

**Deviations from Rocq.**

1. NAMES: lowerCamelCase as `Weak/WeakMem.lean` deviation 1.  The duplicated
   Rocq names (`notes/weak-port-dupnames.json`) `coh_fence_post`, `fwd_le`,
   `load_fold_coh`, `store_fold_coh`, `wp` are FILE-QUALIFIED
   (`AxViolSubsume.cohFencePost`, …).  The Rocq record `exec_graph` is the
   structure `ExecGraph` with fields `egNodup` … `egWix`.
2. VOCABULARY: as `WeakRvwmoGraph` deviation 2 (`l !! i` ↦ `l[i]?`, `S n` ↦
   `n + 1`, `NoDup` ↦ `List.Nodup`, `is_Some o` ↦ `o.isSome`, `imap pair` ↦
   `mapIdx (fun i s => (i, s))`, `bool_decide` ↦ `decide`).
3. The generic list facts (`filterTakeLookup`, `filterTakeLt`,
   `filterFmapComm`, `filterFilterExt`) take a `Bool`-valued predicate (Lean's
   `List.filter`) in place of a decidable `Prop`; correspondingly `memp` and
   `AxViolSubsume.wp` are `Bool`-valued.
4. The Rocq `Section cand_graph` variable `E` is an explicit first argument of
   `cg`, `cf`, `L`, `ceid` and every lemma of §3.
5. `cohLoadPostAt` / `cohStorePost` state the case split with `if a' = a`
   (`decide`) in place of `bool_decide`.
6. ONE HELPER with no Rocq twin: `axViolSubsumeFoldrMaxLe` (an element is
   below `foldr max 0`), standing in for Rocq's `list_max_le`, since
   `graphOfCand` bounds its program rows by `foldr max 0` (`WeakRvwmoGraph`).
7. `msgByteAt` is proved by `WeakAxiomatic3.msgByteInRange` (the same
   statement).

**Name map** (Rocq → Lean): `filter_take_lookup` ↦ `filterTakeLookup`;
`filter_take_lt` ↦ `filterTakeLt`; `filter_fmap_comm` ↦ `filterFmapComm`;
`filter_filter_ext` ↦ `filterFilterExt`; `coh_load_post_at` ↦
`cohLoadPostAt`; `coh_store_post` ↦ `cohStorePost`; `coh_fence_post` ↦
`AxViolSubsume.cohFencePost`; `fwd_le` ↦ `AxViolSubsume.fwdLe`; `fwd_view_le` ↦
`fwdViewLe`; `store_fold_fwd_le` ↦ `storeFoldFwdLe`; `store_post_run_fwd_le` ↦
`storePostRunFwdLe`; `load_post_run_fwd_le` ↦ `loadPostRunFwdLe`;
`fence_post_fwd_le` ↦ `fencePostFwdLe`; `exec_fwd_le` ↦ `execFwdLe`;
`load_fold_coh` ↦ `AxViolSubsume.loadFoldCoh`; `load_post_run_coh_inv` ↦
`loadPostRunCohInv`; `store_fold_coh` ↦ `AxViolSubsume.storeFoldCoh`;
`store_post_run_coh_inv` ↦ `storePostRunCohInv`; `msg_byte_at` ↦ `msgByteAt`;
`coh_touched` ↦ `cohTouched`; `exec_graph` ↦ `ExecGraph` (fields `eg_*` ↦
`ExecGraph.eg*`); `lb_is_w_mem` ↦ `lbIsWMem`; `lb_is_r_mem` ↦ `lbIsRMem`;
`eg_lt_inv` ↦ `egLtInv`; `gpub_before_published` ↦ `gpubBeforePublished`;
`violation_exec_graph` ↦ `violationExecGraph`; `violation_exec_graph_matchd` ↦
`violationExecGraphMatchd`; `cg`; `cf`; `memp`; `wp` ↦ `AxViolSubsume.wp`; `L`;
`ceid`; `cg_gmo` ↦ `cgGmo`; `L_lookup` ↦ `LLookup`; `L_elem` ↦ `LElem`;
`ceid_cf` ↦ `ceidCf`; `cf_inj` ↦ `cfInj`; `L_nodup` ↦ `LNodup`; `cg_nodup` ↦
`cgNodup`; `cg_lbl` ↦ `cgLbl`; `cg_mem` ↦ `cgMem`; `cg_surj` ↦ `cgSurj`;
`cg_inj` ↦ `cgInj`; `cg_gpos` ↦ `cgGpos`; `cg_lt` ↦ `cgLt`; `cg_gwrites` ↦
`cgGwrites`; `elog_writes` ↦ `elogWrites`; `cg_wix` ↦ `cgWix`;
`cand_exec_graph` ↦ `candExecGraph`; `gviolation_subsumes` ↦
`gviolationSubsumes`; `gviolation_free_subsumes` ↦ `gviolationFreeSubsumes`;
`gviolation_subsumes_srvwmo` ↦ `gviolationSubsumesSrvwmo`; `wtr`; `wcd`;
`wcd_graph_viol2` ↦ `wcdGraphViol2`; `wcd_st1` ↦ `wcdSt1`; `wcd_wf` ↦ `wcdWf`;
`wcfg`; `wcfg_matchd` ↦ `wcfgMatchd`; `wcd_st2` ↦ `wcdSt2`; `wcfg_violation` ↦
`wcfgViolation`; `subsume_sat` ↦ `subsumeSat`.

**Not ported:** nothing.

**W13 (I) (plan `notes/weak-allocproc-plan.md` §C W13 (I); [OWN.27]).** the two `LIo` arms (formerly refuted by the retired `execStepNotIo`) use `WeakAxiomatic.execWsIo` (the inert step keeps every `Wstate`).
-/
import Weak.WeakRobustMain
import Weak.WeakAxiomatic3
import Weak.AxViol

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Lbl Ev

/-! # 0. Generic list facts -/

theorem filterTakeLookup {A : Type _} (p : A → Bool) (l : List A) (k : Nat) (x : A) :
    l[k]? = some x → p x = true →
    (l.filter p)[((l.take k).filter p).length]? = some x := by
  induction l generalizing k with
  | nil => intro h; simp at h
  | cons y l ih =>
    intro hk hx
    cases k with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hk
      subst hk
      simp [hx]
    | succ k =>
      simp only [List.getElem?_cons_succ] at hk
      have := ih k hk hx
      cases hy : p y <;> simp [List.take_succ_cons, hy, this]

theorem filterTakeLt {A : Type _} (p : A → Bool) (l : List A) (k1 k2 : Nat) (x : A) :
    l[k1]? = some x → p x = true → k1 < k2 →
    ((l.take k1).filter p).length < ((l.take k2).filter p).length := by
  induction l generalizing k1 k2 with
  | nil => intro h; simp at h
  | cons y l ih =>
    intro hk hx hlt
    obtain ⟨k2, rfl⟩ : ∃ k2', k2 = k2' + 1 := ⟨k2 - 1, by omega⟩
    cases k1 with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hk
      subst hk
      simp [List.take_succ_cons, hx]
    | succ k1 =>
      simp only [List.getElem?_cons_succ] at hk
      have := ih k1 k2 hk hx (by omega)
      cases hy : p y <;> simp [List.take_succ_cons, hy] <;> omega

theorem filterFmapComm {A B : Type _} (p : B → Bool) (f : A → B) (l : List A) :
    (l.map f).filter p = (l.filter (fun x => p (f x))).map f := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    cases h : p (f x) <;> simp [h, ih]

theorem filterFilterExt {A : Type _} (P Q R : A → Bool) (l : List A) :
    (∀ x, x ∈ l → (P x = true ∧ Q x = true ↔ R x = true)) →
    (l.filter Q).filter P = l.filter R := by
  induction l with
  | nil => intro _; rfl
  | cons x l ih =>
    intro hext
    have hx := hext x List.mem_cons_self
    have ih' := ih (fun y hy => hext y (List.mem_cons_of_mem _ hy))
    cases hq : Q x <;> cases hr : R x <;> cases hp : P x <;>
      simp_all

/-! # 1. The axiomatic machine: the floor is raised only by own accesses -/

/-- Per-byte `coh` of the step functions. -/
theorem cohLoadPostAt (ws : Wstate) (aq : Bool) (vpre : Nat) (a a' : Int) (t : Nat) :
    coh (loadPostAt ws aq vpre a t) a' =
      if a' = a then max (coh ws a) (max (max vpre (fwdView ws aq a t)) t)
      else coh ws a' := by
  by_cases h : a' = a
  · subst h; rw [if_pos rfl, cohLoadPostAtEq]
  · rw [if_neg h, cohLoadPostAtNe _ _ _ _ _ _ h]

theorem cohStorePost (ws : Wstate) (rl : Bool) (a a' : Int) (t : Nat) :
    coh (storePost ws rl a t) a' = if a' = a then max (coh ws a) t else coh ws a' := by
  by_cases h : a' = a
  · subst h; rw [if_pos rfl, cohStorePostEq]
  · rw [if_neg h, cohStorePostNe _ _ _ _ _ h]

theorem AxViolSubsume.cohFencePost (ws : Wstate) (pr pw sr sw : Bool) (a : Int) :
    coh (fencePost ws pr pw sr sw) a = coh ws a := rfl

/-- RESIDUAL (ii): the forward bank's view column is bounded by its timestamp
(it is `0` on this machine, D-7r). -/
def AxViolSubsume.fwdLe (ws : Wstate) : Prop :=
  ∀ a tf vf, get? ws.wFwd a = some (tf, vf) → vf ≤ tf

theorem fwdViewLe (ws : Wstate) (aq : Bool) (a : Int) (t : Nat) :
    AxViolSubsume.fwdLe ws → fwdView ws aq a t ≤ t := by
  intro hf
  cases aq with
  | true => exact Nat.le_refl _
  | false =>
    unfold fwdView
    simp only [Bool.false_eq_true, ↓reduceIte]
    cases h : get? ws.wFwd a with
    | none => exact Nat.le_refl _
    | some q =>
      obtain ⟨tf, vf⟩ := q
      show (if t = tf then vf else t) ≤ t
      by_cases ht : t = tf
      · rw [if_pos ht]; have := hf a tf vf h; omega
      · rw [if_neg ht]; exact Nat.le_refl _

theorem storeFoldFwdLe (rl : Bool) (t : Nat) (as_ : List Int) (ws : Wstate) :
    AxViolSubsume.fwdLe ws →
    AxViolSubsume.fwdLe (as_.foldl (fun w a => storePost w rl a t) ws) := by
  induction as_ generalizing ws with
  | nil => intro hf; exact hf
  | cons b l ih =>
    intro hf
    apply ih (storePost ws rl b t)
    intro a tf vf
    show get? (insert ws.wFwd b (t, 0)) a = some (tf, vf) → vf ≤ tf
    by_cases h : a = b
    · subst h; rw [lookupInsert]; intro he; cases he; omega
    · rw [lookupInsertNe (Ne.symm h)]; exact hf a tf vf

theorem storePostRunFwdLe (ws : Wstate) (rl : Bool) (base : Int) (n t : Nat) :
    AxViolSubsume.fwdLe ws → AxViolSubsume.fwdLe (storePostRun ws rl base n t) := by
  intro hf a tf vf h
  rw [storePostRun, ctrlPostFwd] at h
  exact storeFoldFwdLe rl t _ ws hf a tf vf h

theorem loadPostRunFwdLe (ws : Wstate) (aq : Bool) (base : Int) (ts : List Nat) :
    AxViolSubsume.fwdLe ws → AxViolSubsume.fwdLe (loadPostRun ws aq base ts) := by
  intro hf a tf vf h
  rw [loadPostRunFwd] at h
  exact hf a tf vf h

theorem fencePostFwdLe (ws : Wstate) (pr pw sr sw : Bool) :
    AxViolSubsume.fwdLe ws → AxViolSubsume.fwdLe (fencePost ws pr pw sr sw) := by
  intro hf a tf vf h
  rw [fencePostFwd] at h
  exact hf a tf vf h

theorem execFwdLe (E : Exec) (k i : Nat) :
    execWf E → k ≤ E.exTr.length → AxViolSubsume.fwdLe (ews E k i) := by
  intro hwf
  induction k with
  | zero =>
    intro _
    rw [execWsInit E i hwf]
    intro a tf vf h
    exact absurd h (by simp [wsInit, lookupEmpty])
  | succ k ih =>
    intro hk
    obtain ⟨s, hs⟩ := someOfIsSome (execTrLookup E k (by omega))
    have hstep := execStepAt E k s hwf hs
    have hf := ih (by omega)
    by_cases hi : i ≠ s.esAg
    · have heq : ews E (k + 1) i = ews E k i := mstepWsNe _ _ _ _ _ hstep hi
      rw [heq]; exact hf
    have hi := Decidable.of_not_not hi
    subst hi
    cases hl : s.esLb with
    | LLoad aq base ts vs =>
      rw [execWsLoad E k s aq base ts vs hwf hs hl]; exact loadPostRunFwdLe _ _ _ _ hf
    | LStore rl base vs kc =>
      rw [execWsStore E k s rl base vs kc hwf hs hl]; exact storePostRunFwdLe _ _ _ _ _ hf
    | LFence pr pw sr sw =>
      rw [execWsFence E k s pr pw sr sw hwf hs hl]; exact fencePostFwdLe _ _ _ _ _ hf
    | LRmw aq rl base ts rvs wvs kc =>
      rw [execWsRmw E k s aq rl base ts rvs wvs kc hwf hs hl]
      exact storePostRunFwdLe _ _ _ _ _ (loadPostRunFwdLe _ _ _ _ hf)
    | LIo kd0 b0 v0 => rw [WeakAxiomatic.execWsIo E k s kd0 b0 v0 _ hwf hs hl]; exact hf

/-- UPPER bounds for the floor after a step (the inverses of `loadPostRunCoh` /
`storePostRunCoh`). -/
theorem AxViolSubsume.loadFoldCoh (aq : Bool) (vpre : Nat) (ats : List (Int × Nat))
    (ws : Wstate) (a : Int) (n : Nat) :
    AxViolSubsume.fwdLe ws →
    n ≤ coh (ats.foldl (fun w at_ => loadPostAt w aq vpre at_.1 at_.2) ws) a →
    n ≤ coh ws a ∨ ∃ t, (a, t) ∈ ats ∧ n ≤ max vpre t := by
  induction ats generalizing ws with
  | nil => intro _ hn; exact .inl hn
  | cons q ats ih =>
    obtain ⟨a', t'⟩ := q
    intro hf hn
    have hf' : AxViolSubsume.fwdLe (loadPostAt ws aq vpre a' t') :=
      fun b tf vf h => hf b tf vf h
    rcases ih (loadPostAt ws aq vpre a' t') hf' hn with hle | ⟨t, hin, hle⟩
    · by_cases heq : a = a'
      · subst heq
        rw [cohLoadPostAtEq] at hle
        have := fwdViewLe ws aq a t' hf
        by_cases hc : n ≤ coh ws a
        · exact .inl hc
        · exact .inr ⟨t', List.mem_cons_self, by omega⟩
      · rw [cohLoadPostAtNe _ _ _ _ _ _ heq] at hle
        exact .inl hle
    · exact .inr ⟨t, List.mem_cons_of_mem _ hin, hle⟩

theorem loadPostRunCohInv (ws : Wstate) (aq : Bool) (base : Int) (ts : List Nat) (a : Int)
    (n : Nat) :
    AxViolSubsume.fwdLe ws →
    n ≤ coh (loadPostRun ws aq base ts) a →
    n ≤ coh ws a ∨
      ∃ (j : Nat) (t : Nat), ts[j]? = some t ∧ a = accAddr base j ∧
        n ≤ max (loadVpre ws aq) t := by
  intro hf hn
  rw [loadPostRun, ctrlPostCoh, loadPostBytes] at hn
  rcases AxViolSubsume.loadFoldCoh aq (loadVpre ws aq) _ ws a n hf hn with h | ⟨t, hin, hle⟩
  · exact .inl h
  · obtain ⟨j, hj, ha⟩ := elemOfZipSeq base ts (a, t) hin
    exact .inr ⟨j, t, hj, ha, hle⟩

theorem AxViolSubsume.storeFoldCoh (rl : Bool) (t : Nat) (as_ : List Int) (ws : Wstate)
    (a : Int) (n : Nat) :
    n ≤ coh (as_.foldl (fun w a => storePost w rl a t) ws) a →
    n ≤ coh ws a ∨ (a ∈ as_ ∧ n ≤ t) := by
  induction as_ generalizing ws with
  | nil => intro hn; exact .inl hn
  | cons b l ih =>
    intro hn
    rcases ih (storePost ws rl b t) hn with hle | ⟨hin, hle⟩
    · by_cases heq : a = b
      · subst heq
        rw [cohStorePostEq] at hle
        by_cases hc : n ≤ coh ws a
        · exact .inl hc
        · exact .inr ⟨List.mem_cons_self, by omega⟩
      · rw [cohStorePostNe _ _ _ _ _ heq] at hle
        exact .inl hle
    · exact .inr ⟨List.mem_cons_of_mem _ hin, hle⟩

theorem storePostRunCohInv (ws : Wstate) (rl : Bool) (base : Int) (cnt t : Nat) (a : Int)
    (n : Nat) :
    n ≤ coh (storePostRun ws rl base cnt t) a →
    n ≤ coh ws a ∨ ∃ j : Nat, j < cnt ∧ a = accAddr base j ∧ n ≤ t := by
  intro hn
  rw [storePostRun, ctrlPostCoh] at hn
  rcases AxViolSubsume.storeFoldCoh rl t _ ws a n hn with h | ⟨hin, hle⟩
  · exact .inl h
  · obtain ⟨j, hj, ha⟩ := elemOfMapSeq base cnt a hin
    exact .inr ⟨j, hj, ha, hle⟩

/-- A byte inside a write's range is a byte of its message. -/
theorem msgByteAt (base : Int) (vs : List (BitVec 8)) (tid : Option Nat) (k : WmClass)
    (j : Nat) :
    j < vs.length → (msgByte ⟨base, vs, tid, k⟩ (accAddr base j)).isSome :=
  msgByteInRange base vs tid k j

/-- THE CONVERSE OF `touchesCoh`.  If agent `j`'s floor for byte `a` has
reached a message `p` that writes `a`, then `j` itself touched `a` — read it
at, or wrote it with, a timestamp `≥ p + 1` — at some earlier step.  RESIDUAL
(i) is the `readable` case inside. -/
theorem cohTouched (E : Exec) (k j : Nat) (a : Int) (p : Nat) (m : Wmsg) :
    execWf E → k ≤ E.exTr.length →
    (elog E k)[p]? = some m → (msgByte m a).isSome →
    p + 1 ≤ coh (ews E k j) a →
    ∃ k0 s0 t, k0 < k ∧ E.exTr[k0]? = some s0 ∧ s0.esAg = j ∧
      touches E k0 a t ∧ p + 1 ≤ t := by
  intro hwf
  induction k with
  | zero =>
    intro _ _ _ hcoh
    rw [execWsInit E j hwf, cohInit] at hcoh
    omega
  | succ k ih =>
    intro hk hp hma hcoh
    obtain ⟨s, hs⟩ := someOfIsSome (execTrLookup E k (by omega))
    have hstep := execStepAt E k s hwf hs
    have hcohb : ∀ b, coh (ews E k j) b ≤ (elog E k).length :=
      (execWsBounded E k j hwf (by omega)).2.2.2.2.2.2.1
    -- the message is in the log at `k` as soon as `p` is below its length
    have hold : p < (elog E k).length → (elog E k)[p]? = some m := by
      intro hlt
      obtain ⟨l, hl⟩ := execLogPrefix E k (k + 1) hwf (by omega) hk
      rw [← hl, List.getElem?_append_left hlt] at hp
      exact hp
    have ihk : p + 1 ≤ coh (ews E k j) a →
        ∃ k0 s0 t, k0 < k + 1 ∧ E.exTr[k0]? = some s0 ∧ s0.esAg = j ∧
          touches E k0 a t ∧ p + 1 ≤ t := by
      intro hle
      have := hcohb a
      obtain ⟨k0, s0, t, h1, h2, h3, h4, h5⟩ := ih (by omega) (hold (by omega)) hma hle
      exact ⟨k0, s0, t, by omega, h2, h3, h4, h5⟩
    by_cases hj : j ≠ s.esAg
    · have heq : ews E (k + 1) j = ews E k j := mstepWsNe _ _ _ _ _ hstep hj
      rw [heq] at hcoh
      exact ihk hcoh
    have hj := Decidable.of_not_not hj
    subst hj
    -- the READ arm: byte `j'` of a read at `t` with `p + 1 ≤ max vpre t`
    have hread : ∀ (base : Int) (ts : List Nat) (vs : List (BitVec 8)) (j' t : Nat),
        lbRd s.esLb = some (base, ts, vs) → (elog E k)[p]? = some m →
        ts[j']? = some t → a = accAddr base j' →
        p + 1 ≤ max (loadVpre (ews E k s.esAg) (lbAq s.esLb)) t →
        ∃ k0 s0 t, k0 < k + 1 ∧ E.exTr[k0]? = some s0 ∧ s0.esAg = s.esAg ∧
          touches E k0 a t ∧ p + 1 ≤ t := by
      intro base ts vs j' t hrd hpk hj' ha hle
      obtain ⟨hlen, hall⟩ := execRdOk E k s base ts vs hwf hs hrd
      have hjv : j' < vs.length := by rw [hlen]; exact lookup_lt_Some hj'
      obtain ⟨_, _, hnw⟩ := hall j' t vs[j'] hj' (List.getElem?_eq_getElem hjv)
      by_cases hpt : p + 1 ≤ t
      · exact ⟨k, s, t, by omega, hs, rfl,
          .inl ⟨vs[j'], s, base, ts, vs, j', hs, hrd, hj', List.getElem?_eq_getElem hjv, ha⟩, hpt⟩
      · exfalso
        apply hnw
        refine ⟨p + 1, by omega, by omega, m, ?_, ?_⟩
        · simpa using hpk
        · rw [← ha]; exact hma
    cases hl : s.esLb with
    | LLoad aq base ts vs =>
      -- the log is unchanged
      have hpk : (elog E k)[p]? = some m := by
        have : elog E (k + 1) = elog E k := mstepLogNw _ _ _ _ hstep (by rw [hl]; rfl)
        rw [this] at hp; exact hp
      rw [execWsLoad E k s aq base ts vs hwf hs hl] at hcoh
      rcases loadPostRunCohInv _ _ _ _ _ _ (execFwdLe E k s.esAg hwf (by omega)) hcoh with
        hle | ⟨j', t, hj', ha, hle⟩
      · exact ihk hle
      · exact hread base ts vs j' t (by rw [hl]; rfl) hpk hj' ha (by rw [hl]; exact hle)
    | LStore rl base vs kc =>
      rw [execWsStore E k s rl base vs kc hwf hs hl] at hcoh
      rcases storePostRunCohInv _ _ _ _ _ _ _ hcoh with hle | ⟨j', hj', ha, hle⟩
      · exact ihk hle
      · refine ⟨k, s, evTs E (ev_at k), by omega, hs, rfl,
          .inr ⟨⟨s, hs, by rw [hl]; rfl⟩, ?_, rfl⟩, hle⟩
        refine (evWritesAt E k s base vs a hwf hs (by rw [hl]; rfl)).2 ?_
        rw [ha]; exact msgByteAt base vs _ _ j' hj'
    | LFence pr pw sr sw =>
      rw [execWsFence E k s pr pw sr sw hwf hs hl, AxViolSubsume.cohFencePost] at hcoh
      exact ihk hcoh
    | LIo kd0 b0 v0 =>
      rw [WeakAxiomatic.execWsIo E k s kd0 b0 v0 _ hwf hs hl] at hcoh
      exact ihk hcoh
    | LRmw aq rl base ts rvs wvs kc =>
      -- write half, then read half
      rw [execWsRmw E k s aq rl base ts rvs wvs kc hwf hs hl] at hcoh
      rcases storePostRunCohInv _ _ _ _ _ _ _ hcoh with hle | ⟨j', hj', ha, hle⟩
      rotate_left
      · refine ⟨k, s, evTs E (ev_at k), by omega, hs, rfl,
          .inr ⟨⟨s, hs, by rw [hl]; rfl⟩, ?_, rfl⟩, hle⟩
        refine (evWritesAt E k s base wvs a hwf hs (by rw [hl]; rfl)).2 ?_
        rw [ha]; exact msgByteAt base wvs _ _ j' hj'
      -- the message is old: the loaded floor is bounded by the old log
      have hrd := execRdOk E k s base ts rvs hwf hs (by rw [hl]; rfl)
      have hb := execWsBounded E k s.esAg hwf (by omega)
      have hb' := loadPostRunBounded _ aq base ts _ hb (rdOkTsBounded _ _ _ _ _ _ _ hrd)
      have := hb'.2.2.2.2.2.2.1 a
      have hpk := hold (by omega)
      rcases loadPostRunCohInv _ _ _ _ _ _ (execFwdLe E k s.esAg hwf (by omega)) hle with
        hle2 | ⟨j'', t, hj'', ha', hle2⟩
      · exact ihk hle2
      · exact hread base ts rvs j'' t (by rw [hl]; rfl) hpk hj'' ha' (by rw [hl]; exact hle2)

/-! # 2. The exec ↔ graph interface -/

/-- `eid k` is the graph event of trace position `k`.  Every clause is what
`graphOfCand` provides (`candExecGraph` below). -/
structure ExecGraph (E : Exec) (G : Gexec) (eid : Nat → Geid) : Prop where
  egNodup : G.gxGmo.Nodup
  egLbl : ∀ k s, E.exTr[k]? = some s →
    gxLbl G (eid k) = some s.esLb ∧ (eid k).1 = s.esAg
  egMem : ∀ k s, E.exTr[k]? = some s → lbIsMem s.esLb = true → eid k ∈ G.gxGmo
  egSurj : ∀ e, e ∈ G.gxGmo →
    ∃ k s, E.exTr[k]? = some s ∧ lbIsMem s.esLb = true ∧ e = eid k
  egInj : ∀ k1 k2 s1 s2, E.exTr[k1]? = some s1 → E.exTr[k2]? = some s2 →
    eid k1 = eid k2 → k1 = k2
  egLt : ∀ k1 k2 s1 s2, E.exTr[k1]? = some s1 → E.exTr[k2]? = some s2 →
    lbIsMem s1.esLb = true → lbIsMem s2.esLb = true →
    k1 < k2 → gmoLt G (eid k1) (eid k2)
  egWix : ∀ k s, E.exTr[k]? = some s → lbIsW s.esLb = true →
    gwix G (eid k) = evTs E (ev_at k)

theorem lbIsWMem (l : Lbl) : lbIsW l = true → lbIsMem l = true := by
  intro h; simp [lbIsMem, h]

theorem lbIsRMem (l : Lbl) : lbIsR l = true → lbIsMem l = true := by
  intro h; simp [lbIsMem, h]

theorem egLtInv (E : Exec) (G : Gexec) (eid : Nat → Geid) (k1 k2 : Nat) (s1 s2 : Estep) :
    ExecGraph E G eid →
    E.exTr[k1]? = some s1 → E.exTr[k2]? = some s2 →
    lbIsMem s1.esLb = true → lbIsMem s2.esLb = true →
    gmoLt G (eid k1) (eid k2) → k1 < k2 := by
  intro hG h1 h2 hm1 hm2 hlt
  rcases Nat.lt_or_ge k1 k2 with h | h
  · exact h
  · exfalso
    rcases Nat.eq_or_lt_of_le h with heq | hlt'
    · subst heq; exact gmoLtIrrefl G _ hlt
    · have := hG.egLt k2 k1 s2 s1 h2 h1 hm2 hm1 hlt'
      obtain ⟨_, _, h3⟩ := hlt
      obtain ⟨_, _, h4⟩ := this
      omega

/-- A publication in the graph IS a `WCrel` message of the same author, at or
after `w`'s position, in the log of every later point. -/
theorem gpubBeforePublished (E : Exec) (G : Gexec) (eid : Nat → Geid) (n kw : Nat)
    (sw : Estep) (ke : Nat) (se : Estep) :
    execWf E → ExecGraph E G eid → n ≤ E.exTr.length →
    E.exTr[kw]? = some sw → lbIsW sw.esLb = true →
    E.exTr[ke]? = some se → lbIsMem se.esLb = true → ke < n →
    gpubBefore G (eid kw) (eid ke) →
    wpublished (elog E n) (some sw.esAg) (elog E kw).length := by
  rintro hwf hG hn hkw hw hke hme hlt ⟨h, hh1, hrel, hwh, hhe⟩
  have hhin := hhe.1
  obtain ⟨kh, sh, hkh, hmh, rfl⟩ := hG.egSurj h hhin
  obtain ⟨hlh, hah⟩ := hG.egLbl kh sh hkh
  obtain ⟨_, haw⟩ := hG.egLbl kw sw hkw
  obtain ⟨l, hl, hrelw⟩ := hrel
  rw [hlh] at hl
  cases hl
  simp only [lbRelw, Bool.and_eq_true, decide_eq_true_eq] at hrelw
  obtain ⟨hwh', hcls⟩ := hrelw
  have hagh : sh.esAg = sw.esAg := by rw [← hah, ← haw]; exact hh1
  have hkhe : kh < ke := egLtInv E G eid kh ke sh se hG hkh hke hmh hme hhe
  have hkwh : kw ≤ kh := by
    rcases hwh with heq | hlt'
    · exact Nat.le_of_eq (hG.egInj kh kw sh sw hkh hkw heq).symm
    · exact Nat.le_of_lt (egLtInv E G eid kw kh sw sh hG hkw hkh (lbIsWMem _ hw) hmh hlt')
  obtain ⟨base, vs, hwr⟩ := lbIsWWr _ hwh'
  have hmsg := execMsgAt E kh sh base vs hwf hkh hwr
  have hnext := evTsNext E kh sh hwf hkh hwh'
  rw [evTsAt] at hnext
  have hlen := execLogLenLe E (kh + 1) n hwf (by omega) hn
  obtain ⟨l', hl'⟩ := exLogPrefix E n hwf hn
  rw [← hl', List.getElem?_append_left (by omega)] at hmsg
  have hkhl := lookup_lt_Some hkh
  refine ⟨(elog E kh).length, _, execLogLenLe E kw kh hwf hkwh (by omega), hmsg, ?_, hcls⟩
  show some sh.esAg = some sw.esAg
  rw [hagh]

/-- THE SUBSUMPTION over the axiomatic exec: a violation at any state
`σ = stt E n` whose log and floors `c` shares is a graph violation. -/
theorem violationExecGraph {P D : Type} (E : Exec) (G : Gexec) (eid : Nat → Geid)
    (n nh : Nat) (c : Wpcfg P D) :
    execWf E → n ≤ E.exTr.length → ExecGraph E G eid →
    c.pcLog = elog E n →
    (∀ j ag, c.pcAgs[j]? = some ag → ∀ a, coh ag.paWs a = coh (ews E n j) a) →
    violationHart clsOf pubOf nh c → gviolationHart nh G := by
  rintro hwf hn hG hlog hcohc ⟨p, m, i, j, a, hp, htid, hhi, hcls, hnpub, hji, hhj, hma, hflr⟩
  rw [hlog] at hp
  -- the observer's floor
  obtain ⟨ag, hag⟩ : ∃ ag, c.pcAgs[j]? = some ag := by
    cases h : c.pcAgs[j]? with
    | none => simp [obsFlr, h] at hflr
    | some ag => exact ⟨ag, rfl⟩
  have hflr' : p + 1 ≤ coh (ews E n j) a := by
    rw [← hcohc j ag hag a]; simpa [obsFlr, hag] using hflr
  obtain ⟨k0, s0, t, hk0, hs0, hag0, htch, hpt⟩ := cohTouched E n j a p m hwf hn hp hma hflr'
  -- the message's writer step
  have hplen := lookup_lt_Some hp
  obtain ⟨kw, sw, hkwn, hkw, hww, hts⟩ := tsWriter E n (p + 1) hwf hn (by omega) (by omega)
  rw [evTsAt] at hts
  obtain ⟨base, vs, hwr⟩ := lbIsWWr _ hww
  have hmsg := execMsgAt E kw sw base vs hwf hkw hwr
  obtain ⟨l', hl'⟩ := exLogPrefix E n hwf hn
  rw [← hl', List.getElem?_append_left (by omega)] at hmsg
  have hpe : p = (elog E kw).length := by omega
  have hmeq : m = ⟨base, vs, some sw.esAg, lbCls sw.esLb⟩ := by
    have hp' := hp
    rw [hpe, hmsg] at hp'
    exact (Option.some.inj hp').symm
  subst hmeq
  simp only [Option.some.injEq] at htid
  subst htid
  have hplain : lbCls sw.esLb = .WCplain := by
    revert hcls; unfold clsOf; cases lbCls sw.esLb <;> simp
  obtain ⟨jw, hjw, haw⟩ := msgByteIndex base vs (some sw.esAg) _ a hma
  obtain ⟨hlw, hagw⟩ := hG.egLbl kw sw hkw
  obtain ⟨hl0, hag0'⟩ := hG.egLbl k0 s0 hs0
  have hwix : gwix G (eid kw) = p + 1 := by rw [hG.egWix kw sw hkw hww, evTsAt]; omega
  -- the observation event is a memory event
  have hmem0 : lbIsMem s0.esLb = true := by
    rcases htch with ⟨v, s', _, _, _, _, hs', hrd, _⟩ | ⟨⟨s', hs', hw'⟩, _⟩
    · rw [hs0] at hs'; cases hs'; exact lbIsRMem _ (lbRdIsR _ _ hrd)
    · rw [hs0] at hs'; cases hs'; exact lbIsWMem _ hw'
  -- no publication before the observation
  have hnpb : ¬ gpubBefore G (eid kw) (eid k0) := by
    intro hpb
    apply hnpub
    refine ⟨p, ⟨base, vs, some sw.esAg, lbCls sw.esLb⟩, rfl, by rw [hlog]; exact hp, ?_⟩
    rw [hlog]
    show wpublished (elog E n) (some sw.esAg) p
    rw [hpe]
    exact gpubBeforePublished E G eid n kw sw k0 s0 hwf hG hn hkw hww hs0 hmem0 hk0 hpb
  refine ⟨eid kw, eid k0, a, vs[jw], hG.egMem kw sw hkw (lbIsWMem _ hww),
    ⟨sw.esLb, base, vs, jw, hlw, hwr, List.getElem?_eq_getElem hjw, haw.symm⟩,
    ⟨sw.esLb, hlw, by simp [lbPlain, hww, hplain]⟩, trivial,
    by rw [hagw]; exact hhi, by rw [hag0', hag0]; exact hhj,
    by rw [hag0', hagw, hag0]; exact hji, ?_⟩
  rcases htch with ⟨v, s', base', ts', vs', j', hs', hrd, hj', hv, ha'⟩ |
      ⟨⟨s', hs', hw'⟩, hwr0, ht⟩
  · -- a READ of `a` at `t ≥ p + 1`
    rw [hs0] at hs'; cases hs'
    refine .inr ⟨t, v, ⟨s0.esLb, base', ts', vs', j', hl0, hrd, hj', hv, ha'.symm⟩,
      by omega, hnpb, ?_⟩
    -- the read's source is gmo-before the read
    intro ws hws hpb
    apply hnpb
    obtain ⟨hwsin, hwsix⟩ := gwriteAtInv G t ws hG.egNodup hws
    obtain ⟨hwsin', hwsw⟩ := (gwritesElemOf G ws).1 hwsin
    obtain ⟨ks, ss, hks, _, rfl⟩ := hG.egSurj ws hwsin'
    obtain ⟨hls, _⟩ := hG.egLbl ks ss hks
    have hwss : lbIsW ss.esLb = true := by
      unfold gisW at hwsw; rw [hls] at hwsw; exact hwsw
    rw [hG.egWix ks ss hks hwss] at hwsix
    have hrat : readsAt E k0 (accAddr base' j') t v := ⟨s0, base', ts', vs', j', hs0, hrd, hj', hv, rfl⟩
    have htle := readsAtTsLe E k0 _ t v hwf hrat
    obtain ⟨kw', sw', hkw'0, hkw', hww', hts'⟩ :=
      tsWriter E k0 t hwf (by omega) (by omega) htle
    have heq : ev_at ks = ev_at kw' :=
      evTsInj E _ _ hwf ⟨ss, hks, hwss⟩ ⟨sw', hkw', hww'⟩ (by rw [hwsix, hts'])
    cases heq
    obtain ⟨h, hh1, hrel, hwh, hhe⟩ := hpb
    exact ⟨h, hh1, hrel, hwh,
      gmoLtTrans _ _ _ _ hhe (hG.egLt ks k0 ss s0 hks hs0 (lbIsWMem _ hwss) hmem0 hkw'0)⟩
  · -- a WRITE of `a` at `t = evTs (ev_at k0) > p + 1`
    rw [hs0] at hs'; cases hs'
    obtain ⟨base0, vs0, hwr0'⟩ := lbIsWWr _ hw'
    have hwr0b := (evWritesAt E k0 s0 base0 vs0 a hwf hs0 hwr0').1 hwr0
    obtain ⟨j0, hj0, ha0⟩ := msgByteIndex base0 vs0 (some s0.esAg) _ a hwr0b
    refine .inl ⟨vs0[j0], ⟨s0.esLb, base0, vs0, j0, hl0, hwr0', List.getElem?_eq_getElem hj0,
      ha0.symm⟩, ?_, hnpb⟩
    rw [hwix, hG.egWix k0 s0 hs0 hw', ← ht]
    by_cases hteq : t = p + 1
    · exfalso
      have hk : ev_at k0 = ev_at kw :=
        evTsInj E _ _ hwf ⟨s0, hs0, hw'⟩ ⟨sw, hkw, hww⟩ (by rw [← ht, evTsAt]; omega)
      cases hk
      rw [hs0] at hkw; cases hkw
      exact hji hag0.symm
    · omega

/-- … and with `cfgMatchd` (the realization bridge's conclusion). -/
theorem violationExecGraphMatchd {P D : Type} (E : Exec) (G : Gexec) (eid : Nat → Geid)
    (n nh : Nat) (c : Wpcfg P D) :
    execWf E → n ≤ E.exTr.length → ExecGraph E G eid →
    cfgMatchd c (stt E n) →
    violationHart clsOf pubOf nh c → gviolationHart nh G := by
  rintro hwf hn hG ⟨_, hlog, hws⟩
  apply violationExecGraph E G eid n nh c hwf hn hG hlog.symm
  intro j ag hag a
  exact (wsEqrCoh _ _ a (hws j ag hag)).symm

/-! # 3. `graphOfCand` realizes the interface -/

def cg (E : Exec) : Gexec := graphOfCand ⟨exImg E, E.exTr⟩

/-- The event of a trace pair, exactly as `graphOfCand` spells it. -/
def cf (E : Exec) (ks : Nat × Estep) : Geid :=
  (ks.2.esAg, ((E.exTr.take ks.1).filter (fun s => decide (s.esAg = ks.2.esAg))).length)

def memp (ks : Nat × Estep) : Bool := lbIsMem ks.2.esLb

def AxViolSubsume.wp (ks : Nat × Estep) : Bool := lbIsW ks.2.esLb

def L (E : Exec) : List (Nat × Estep) := E.exTr.mapIdx (fun i s => (i, s))

def ceid (E : Exec) (k : Nat) : Geid :=
  match E.exTr[k]? with
  | some s => cf E (k, s)
  | none => (0, 0)

theorem cgGmo (E : Exec) : (cg E).gxGmo = ((L E).filter memp).map (cf E) := rfl

theorem LLookup (E : Exec) (k : Nat) : (L E)[k]? = (E.exTr[k]?).map (Prod.mk k) := by
  unfold L; rw [list_lookup_imap]

theorem LElem (E : Exec) (k : Nat) (s : Estep) : (k, s) ∈ L E ↔ E.exTr[k]? = some s := by
  constructor
  · intro h
    obtain ⟨i, hi⟩ := elem_of_list_lookup_1 h
    rw [LLookup] at hi
    cases h' : E.exTr[i]? with
    | none => rw [h'] at hi; cases hi
    | some s' =>
      rw [h'] at hi
      cases hi
      exact h'
  · intro h
    apply elem_of_list_lookup_2 (i := k)
    rw [LLookup, h]; rfl

theorem ceidCf (E : Exec) (k : Nat) (s : Estep) : E.exTr[k]? = some s → ceid E k = cf E (k, s) := by
  intro h; unfold ceid; rw [h]

theorem cfInj (E : Exec) (k1 k2 : Nat) (s1 s2 : Estep) :
    E.exTr[k1]? = some s1 → E.exTr[k2]? = some s2 →
    cf E (k1, s1) = cf E (k2, s2) → k1 = k2 := by
  intro h1 h2 heq
  simp only [cf, Prod.mk.injEq] at heq
  obtain ⟨hag, hcnt⟩ := heq
  rcases Nat.lt_trichotomy k1 k2 with hlt | heq | hgt
  · have := filterTakeLt (fun s => decide (s.esAg = s1.esAg)) E.exTr k1 k2 s1 h1 (by simp) hlt
    rw [hag] at hcnt this
    omega
  · exact heq
  · have := filterTakeLt (fun s => decide (s.esAg = s2.esAg)) E.exTr k2 k1 s2 h2 (by simp) hgt
    rw [hag] at hcnt
    omega

theorem LNodup (E : Exec) : (L E).Nodup := by
  have key : ∀ (i : Nat) (x : Nat × Estep), (L E)[i]? = some x → x.1 = i := by
    intro i x h
    rw [LLookup] at h
    cases h' : E.exTr[i]? with
    | none => rw [h'] at h; cases h
    | some s => rw [h'] at h; cases h; rfl
  exact NoDup_alt.2 fun i j x hi hj => (key i x hi).symm.trans (key j x hj)

theorem cgNodup (E : Exec) : (cg E).gxGmo.Nodup := by
  rw [cgGmo]
  refine NoDup_fmap_2_strong ?_ (NoDup_filter (LNodup E))
  rintro ⟨k1, s1⟩ ⟨k2, s2⟩ hx hy heq
  have h1 := (LElem E k1 s1).1 (elem_of_list_filter.1 hx).2
  have h2 := (LElem E k2 s2).1 (elem_of_list_filter.1 hy).2
  have := cfInj E k1 k2 s1 s2 h1 h2 heq
  subst this
  obtain rfl : s1 = s2 := Option.some.inj (h1.symm.trans h2)
  rfl

/-- (No Rocq twin; header deviation 6.) -/
theorem axViolSubsumeFoldrMaxLe (l : List Nat) (x : Nat) : x ∈ l → x ≤ l.foldr max 0 := by
  induction l with
  | nil => intro h; cases h
  | cons y l ih =>
    intro h
    show x ≤ max y (l.foldr max 0)
    rcases List.mem_cons.1 h with rfl | h
    · omega
    · have := ih h; omega

theorem cgLbl (E : Exec) (k : Nat) (s : Estep) :
    E.exTr[k]? = some s → gxLbl (cg E) (ceid E k) = some s.esLb ∧ (ceid E k).1 = s.esAg := by
  intro hk
  rw [ceidCf E k s hk]
  refine ⟨?_, rfl⟩
  have hle : s.esAg ≤ (E.exTr.map Estep.esAg).foldr max 0 :=
    axViolSubsumeFoldrMaxLe _ _ (List.mem_map_of_mem (elem_of_list_lookup_2 hk))
  show (((List.range' 0 ((E.exTr.map Estep.esAg).foldr max 0 + 1)).map
      (fun i => (E.exTr.filter (fun s => decide (s.esAg = i))).map (fun s => s.esLb)))[s.esAg]?).bind
      (fun p => p[((E.exTr.take k).filter (fun s' => decide (s'.esAg = s.esAg))).length]?) =
    some s.esLb
  rw [List.getElem?_map, lookup_seq_lt (by omega), Nat.zero_add]
  show ((E.exTr.filter (fun s' => decide (s'.esAg = s.esAg))).map (fun s => s.esLb))[
      ((E.exTr.take k).filter (fun s' => decide (s'.esAg = s.esAg))).length]? = some s.esLb
  rw [List.getElem?_map, filterTakeLookup _ E.exTr k s hk (by simp)]
  rfl

theorem cgMem (E : Exec) (k : Nat) (s : Estep) :
    E.exTr[k]? = some s → lbIsMem s.esLb = true → ceid E k ∈ (cg E).gxGmo := by
  intro hk hm
  rw [cgGmo, ceidCf E k s hk]
  exact elem_of_list_fmap_1 (elem_of_list_filter.2 ⟨hm, (LElem E k s).2 hk⟩)

theorem cgSurj (E : Exec) (e : Geid) :
    e ∈ (cg E).gxGmo →
    ∃ k s, E.exTr[k]? = some s ∧ lbIsMem s.esLb = true ∧ e = ceid E k := by
  rw [cgGmo]
  intro he
  obtain ⟨⟨k, s⟩, rfl, hin⟩ := elem_of_list_fmap.1 he
  obtain ⟨hm, hk⟩ := elem_of_list_filter.1 hin
  have hk' := (LElem E k s).1 hk
  exact ⟨k, s, hk', hm, (ceidCf E k s hk').symm⟩

theorem cgInj (E : Exec) (k1 k2 : Nat) (s1 s2 : Estep) :
    E.exTr[k1]? = some s1 → E.exTr[k2]? = some s2 → ceid E k1 = ceid E k2 → k1 = k2 := by
  intro h1 h2
  rw [ceidCf E k1 s1 h1, ceidCf E k2 s2 h2]
  exact cfInj E k1 k2 s1 s2 h1 h2

/-- `gpos` of a memory event = the number of memory events before it. -/
theorem cgGpos (E : Exec) (k : Nat) (s : Estep) :
    E.exTr[k]? = some s → lbIsMem s.esLb = true →
    gpos (cg E) (ceid E k) = (((L E).take k).filter memp).length := by
  intro hk hm
  apply gposOfLookup _ _ _ (cgNodup E)
  rw [cgGmo, List.getElem?_map, ceidCf E k s hk,
    filterTakeLookup memp (L E) k (k, s) (by rw [LLookup, hk]; rfl) hm]
  rfl

theorem cgLt (E : Exec) (k1 k2 : Nat) (s1 s2 : Estep) :
    E.exTr[k1]? = some s1 → E.exTr[k2]? = some s2 →
    lbIsMem s1.esLb = true → lbIsMem s2.esLb = true →
    k1 < k2 → gmoLt (cg E) (ceid E k1) (ceid E k2) := by
  intro h1 h2 hm1 hm2 hlt
  refine ⟨cgMem E k1 s1 h1 hm1, cgMem E k2 s2 h2 hm2, ?_⟩
  rw [cgGpos E k1 s1 h1 hm1, cgGpos E k2 s2 h2 hm2]
  exact filterTakeLt memp (L E) k1 k2 (k1, s1) (by rw [LLookup, h1]; rfl) hm1 hlt

/-- The write sub-order is the trace's writes. -/
theorem cgGwrites (E : Exec) : gwrites (cg E) = ((L E).filter AxViolSubsume.wp).map (cf E) := by
  unfold gwrites
  rw [cgGmo, filterFmapComm]
  congr 1
  apply filterFilterExt
  rintro ⟨k, s⟩ hk
  have hk' := (LElem E k s).1 hk
  have hl := (cgLbl E k s hk').1
  rw [ceidCf E k s hk'] at hl
  show gisW (cg E) (cf E (k, s)) = true ∧ lbIsMem s.esLb = true ↔ lbIsW s.esLb = true
  unfold gisW
  rw [hl]
  exact ⟨fun h => h.1, fun h => ⟨h, lbIsWMem _ h⟩⟩

/-- The machine's log length counts the trace's writes. -/
theorem elogWrites (E : Exec) (k : Nat) :
    execWf E → k ≤ E.exTr.length →
    (elog E k).length = (((L E).take k).filter AxViolSubsume.wp).length := by
  intro hwf
  induction k with
  | zero => intro _; rw [execLogInit E hwf]; rfl
  | succ k ih =>
    intro hk
    obtain ⟨s, hs⟩ := someOfIsSome (execTrLookup E k (by omega))
    have hstep := execStepAt E k s hwf hs
    have hL : (L E)[k]? = some (k, s) := by rw [LLookup, hs]; rfl
    rw [take_S_r hL, List.filter_append, List.length_append, ← ih (by omega)]
    cases hw : lbIsW s.esLb
    · rw [show elog E (k + 1) = elog E k from mstepLogNw _ _ _ _ hstep hw]
      simp [AxViolSubsume.wp, hw]
    · rw [evTsNext E k s hwf hs hw, evTsAt]
      simp [AxViolSubsume.wp, hw]

theorem cgWix (E : Exec) (k : Nat) (s : Estep) :
    execWf E → E.exTr[k]? = some s → lbIsW s.esLb = true →
    gwix (cg E) (ceid E k) = evTs E (ev_at k) := by
  intro hwf hk hw
  have hlt := lookup_lt_Some hk
  rw [evTsAt, elogWrites E k hwf (by omega)]
  apply gwixOfLookup _ _ _ (cgNodup E)
  rw [cgGwrites, List.getElem?_map, ceidCf E k s hk,
    filterTakeLookup AxViolSubsume.wp (L E) k (k, s) (by rw [LLookup, hk]; rfl) hw]
  rfl

theorem candExecGraph (E : Exec) : execWf E → ExecGraph E (cg E) (ceid E) := fun hwf =>
  ⟨cgNodup E, cgLbl E, cgMem E, cgSurj E, cgInj E, cgLt E,
   fun k s hk hw => cgWix E k s hwf hk hw⟩

/-! # 4. THE K1 SUBSUMPTION COROLLARY -/

/-- On the repo's realization chain: `cd` a candidate whose replay is a machine
execution; `GT` the graph of `cd`; `c` any pf configuration matching the exec's
`n`-th state.  A violation at `c` is a graph violation on `GT`. -/
theorem gviolationSubsumes {P D : Type} (cd : Cand) (GT : Gdexec) (n nh : Nat) (c : Wpcfg P D) :
    execWf (candExec cd) →
    GT.gdG = graphOfCand cd →
    n ≤ cd.cdTr.length →
    cfgMatchd c (stt (candExec cd) n) →
    violationHart clsOf pubOf nh c → gdviolationHart nh GT := by
  intro hwf hGT hn hm hv
  unfold gdviolationHart
  rw [hGT]
  have hcg : graphOfCand cd = cg (candExec cd) := by
    show graphOfCand cd = graphOfCand ⟨exImg (candExec cd), cd.cdTr⟩
    rw [show exImg (candExec cd) = cd.cdImg from candEimg cd 0 (Nat.zero_le _)]
  rw [hcg]
  exact violationExecGraphMatchd (candExec cd) _ _ n nh c hwf hn (candExecGraph _ hwf) hm hv

/-- The contrapositive, as the design states it. -/
theorem gviolationFreeSubsumes {P D : Type} (cd : Cand) (GT : Gdexec) (n nh : Nat)
    (c : Wpcfg P D) :
    execWf (candExec cd) →
    GT.gdG = graphOfCand cd →
    n ≤ cd.cdTr.length →
    cfgMatchd c (stt (candExec cd) n) →
    ¬ gdviolationHart nh GT → ¬ violationHart clsOf pubOf nh c :=
  fun hwf hGT hn hm hng hv => hng (gviolationSubsumes cd GT n nh c hwf hGT hn hm hv)

/-- From sRVWMO consistency of the candidate (T1, `srvwmoRealizable`). -/
theorem gviolationSubsumesSrvwmo {P D : Type} (cd : Cand) (GT : Gdexec) (n nh : Nat)
    (c : Wpcfg P D) :
    srvwmoConsistent cd →
    GT.gdG = graphOfCand cd →
    n ≤ cd.cdTr.length →
    cfgMatchd c (stt (candExec cd) n) →
    violationHart clsOf pubOf nh c → gdviolationHart nh GT :=
  fun hcons => gviolationSubsumes cd GT n nh c (srvwmoRealizable cd hcons).1

/-! # 5. Non-vacuity: a racy 2-hart run whose matched configuration VIOLATES -/

/-- H0: plain store of `b1` to byte 0 (ts 1).  H1: plain load of byte 0 at
ts 1.  The very graph of `AxViol.viol2`. -/
def wtr : List Estep :=
  [⟨0, LStore false 0 [b1] .WCplain⟩, ⟨1, LLoad false 0 [1] [b1]⟩]

def wcd : Cand := ⟨vimg, wtr⟩

theorem wcdGraphViol2 : graphOfCand wcd = viol2.gdG := rfl

theorem wcdSt1 :
    stt (candExec wcd) 1 =
      ⟨vimg, [⟨0, [b1], some 0, .WCplain⟩],
       updWs (fun _ => wsInit) 0 (storePostRun wsInit false 0 1 1)⟩ := by
  rw [candNext wcd 0 ⟨0, LStore false 0 [b1] .WCplain⟩ rfl, candSttInit]
  rfl

theorem wcdWf : execWf (candExec wcd) := by
  refine (candReachable wcd ?_).1
  intro k s hs
  match k, hs with
  | 0, hs =>
    simp only [wcd, wtr, List.getElem?_cons_zero, Option.some.injEq] at hs
    subst hs
    exact List.cons_ne_nil _ _
  | 1, hs =>
    simp only [wcd, wtr, List.getElem?_cons_succ, List.getElem?_cons_zero,
      Option.some.injEq] at hs
    subst hs
    show rdOk (stt (candExec wcd) 1).msImg (stt (candExec wcd) 1).msLog
      ((stt (candExec wcd) 1).msWs 1) false 0 [1] [b1]
    rw [wcdSt1]
    refine ⟨rfl, ?_⟩
    intro j t v hj hv
    match j, hj, hv with
    | 0, hj, hv =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hj hv
      subst hj hv
      refine ⟨rfl, rfl, ?_⟩
      rintro ⟨t', h1, h2, _⟩
      have h2' : t' ≤ 0 := h2
      omega
    | j + 1, hj, _ => simp at hj
  | k + 2, hs => simp [wcd, wtr] at hs

/-- The matched configuration at the end of the run. -/
def wcfg : Wpcfg Unit Unit :=
  ⟨vimg, (stt (candExec wcd) 2).msLog, (),
   [⟨(), (stt (candExec wcd) 2).msWs 0, ∅⟩, ⟨(), (stt (candExec wcd) 2).msWs 1, ∅⟩]⟩

theorem wcfgMatchd : cfgMatchd wcfg (stt (candExec wcd) 2) := by
  refine ⟨candEimg wcd 2 (by decide), rfl, ?_⟩
  intro i ag hag
  match i, hag with
  | 0, hag =>
    simp only [wcfg, List.getElem?_cons_zero, Option.some.injEq] at hag
    subst hag; exact wsEqrRefl _
  | 1, hag =>
    simp only [wcfg, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hag
    subst hag; exact wsEqrRefl _
  | i + 2, hag => simp [wcfg] at hag

theorem wcdSt2 :
    (stt (candExec wcd) 2).msLog = [⟨0, [b1], some 0, .WCplain⟩] ∧
      1 ≤ coh ((stt (candExec wcd) 2).msWs 1) 0 := by
  rw [candNext wcd 1 ⟨1, LLoad false 0 [1] [b1]⟩ rfl, wcdSt1]
  refine ⟨rfl, ?_⟩
  show 1 ≤ coh (updWs (updWs (fun _ => wsInit) 0 (storePostRun wsInit false 0 1 1)) 1
    (loadPostRun (updWs (fun _ => wsInit) 0 (storePostRun wsInit false 0 1 1) 1) false 0 [1]) 1) 0
  rw [updWsEq]
  exact loadPostRunCoh _ false 0 [1] 0 1 rfl

theorem wcfgViolation : violationHart clsOf pubOf 2 wcfg := by
  obtain ⟨hlog, hcoh⟩ := wcdSt2
  refine ⟨0, ⟨0, [b1], some 0, .WCplain⟩, 0, 1, 0, ?_, rfl, ⟨0, rfl, by omega⟩, rfl, ?_,
    by omega, ⟨1, rfl, by omega⟩, rfl, hcoh⟩
  · show (stt (candExec wcd) 2).msLog[0]? = _
    rw [hlog]; rfl
  · rintro ⟨p, m, hp, hm, q, mq, _, hq, _, hak⟩
    have hq' : ([⟨0, [b1], some 0, .WCplain⟩] : List Wmsg)[q]? = some mq := by
      rw [← hlog]; exact hq
    cases q with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hq'
      subst hq'
      cases hak
    | succ q => simp at hq'

/-- THE SATISFIABILITY CERTIFICATE: every hypothesis of `gviolationSubsumes`
holds of `wcd`/`wcfg` AND its antecedent holds, so the corollary is not
vacuous; its conclusion is exactly `AxViol.gviolationSat`'s witness. -/
theorem subsumeSat : gdviolationHart 2 viol2 :=
  gviolationSubsumes wcd viol2 2 2 wcfg wcdWf wcdGraphViol2.symm (by decide) wcfgMatchd
    wcfgViolation

end Weak
