/-
Weak: **the floor discharge** (the core of T2-1c′).

Rocq: `iris/WeakRvwmoFloor.v` @ xxvzwolszwmp.

## The Rocq header, in substance

Design `claude-notes/design/weak-memory-route-b.md` §4d.4 and §4e (sub-slice 3a).
`WeakRvwmoCert.snocReadConsistent` appends a read to an sRVWMO-consistent candidate as soon
as the read's named source survives the agent's own COHERENCE FLOOR
`cdFloor c i aq a = max (loadVpre ws aq) (coh ws a)`.  `WeakRvwmoLin`'s rule-14
linearization discharges that obligation for ONE trace, declaratively; T2-1c′ must admit ANY
linear extension of po ∪ rf ∪ gmo|W, so this file discharges the floor OPERATIONALLY, by an
induction on the candidate that tracks what each of the agent's own view components can hold.

THE DECOMPOSITION: `loadVpre ws aq = wVrNew ⊔ (aq ? wVRel)`, `coh ws a` the per-byte floor;
the two OLD watermarks feed `wVrNew` only THROUGH A FENCE.  So the invariant `finv` is
conditional in exactly two places — `wVrOld`/`wVwOld` are bounded only when a fence still to
come will publish them (`fhook`), `wVRel` only when an acquire still to come will consume it
(`ahook`).  Each hook is one riscv.cat ppo⁻ arm: coh ← rules 1-3 (`gpolocGmo`), wVrNew ←
rule 5 (`gacqGmo`), wVrOld/wVwOld ← rule 4 (`gfenceGmo`), wVRel ← rule 7 (`grelacqGmo`).
The closing arithmetic: everything an ordered-before-`r` event can put into a view is a gmo
write index BELOW `r`, and `gloadValue`'s co-maximality half says every gmo-visible same-byte
write has index ≤ `t` — that is `gvisUb` (§1).

WHAT IS NOT NEEDED: `grule14`.  The floor follows from `rvwmoMinusConsistent` alone; rule 14
enters T2-1c′ only through the LOG-ORDER clause of a G-trace prefix (`gtpWix`/`gtpLog`).

§8 delivers the two induction steps of T2-1c′ (`gtraceSnocReadConsistent`,
`gtraceSnocWriteConsistent`, over `gtracePrefixSnoc`); §9 non-vacuity
(`gtraceSnocReadImage`).  Rocq §10 ("what remains of T2-1c′": obligations O1/O2/O6's
atomicity clause) is a comment only.  A LEAF: nothing imports this file.

## Deviations from Rocq

1. NAMES: the tree's camelCase (map below); `S k` ↦ `k + 1`; `l !! n` ↦ `l[n]?`;
   `is_Some o` ↦ `o.isSome`; `bool_decide (p < n)` ↦ `if p < n then …`; `agent` ↦ `Nat`;
   `Z` ↦ `Int`; `bv 8` ↦ `BitVec 8`; `EStep i l` ↦ `⟨i, l⟩`; `Cand img tr` ↦ `⟨img, tr⟩`;
   `filter (λ s, es_ag s = i)` ↦ `List.filter (fun s => decide (s.esAg = i))`;
   `WMsg base vs t k` ↦ the `Wmsg` literal.  Labels are `WeakAxiomatic.Lbl` (`.LLoad` …).
2. The Rocq `Section Graph` / `Section Floor` hypotheses become explicit parameters of each
   declaration, exactly those Rocq's section closing keeps, in section order
   (`gwf`/`gppoGmo`/`gloadValue`, then `r a`, then `glblIs G r lbIsR`/`gaccesses G r a`).
   The two `Local Lemma`s `Hrsome`/`Hrmem` become `WeakRvwmoFloor.hrsome`/`.hrmem` with
   those parameters explicit.
3. Duplicated Rocq names (protocol rule) are FILE-QUALIFIED: `WeakRvwmoFloor.loadFoldCoh'`,
   `WeakRvwmoFloor.loadFoldVrOld'`, `WeakRvwmoFloor.loadFoldVrNew'`,
   `WeakRvwmoFloor.storeFoldVRel`, `WeakRvwmoFloor.lstep`, `WeakRvwmoFloor.gshape`
   (the `WeakAxiomatic3` primed fold lemmas have a different hypothesis shape; this file's
   are Rocq's `fwd0` versions).
4. `gtracePrefixSnoc`'s and `gtraceSnocReadConsistent`'s log arguments are stated with
   `cdLogEnd c`, as Rocq; `GtracePrefix`'s own fields use `cdLog c c.cdTr.length` (Rocq's
   `cd_log c (length (cd_tr c))`), definitionally the same.
5. Inside `gtraceSnocReadConsistent`'s proof the byte value is taken from `vs[j]?` directly
   rather than Rocq's `default (bv_0 8) (vs !! j)` (proof-internal only).
6. O2/D1: no fetch-inertness premise is needed anywhere here — the file works in
   `WeakAxiomatic.Lbl` (no fetch constructor) and appends only plain `LLoad`/`LStore` steps
   through `WeakRvwmoCert.snocReadConsistent`/`snocWriteConsistent`, which carry none.
7. §11's `Print Assumptions` audit is dropped (the lint's axiom/sorry ban is the audit).

**Rocq → Lean name map.**  `gvis_ub` `gvisUb`, `gvis_ub_down` `gvisUbDown`, `gvis_ub_0`
`gvisUb0`, `gvis_ub_maxcl` `gvisUbMaxcl`, `gvis_ub_ev` `gvisUbEv`, `gvis_ub_of_write`
`gvisUbOfWrite`, `fwd0` `fwd0`, `fwd0_init` `fwd0Init`, `fwd0_ext` `fwd0Ext`, `fwd_view_P`
`fwdViewP`, `fwd0_store_post` `fwd0StorePost`, `fwd0_store_fold` `fwd0StoreFold`,
`fwd0_store_post_run` `fwd0StorePostRun`, `fwd0_load_post_run` `fwd0LoadPostRun`,
`fwd0_fence_post` `fwd0FencePost`, `load_fold_coh'` `WeakRvwmoFloor.loadFoldCoh'`,
`load_fold_vrOld'` `WeakRvwmoFloor.loadFoldVrOld'`, `load_fold_vrNew'`
`WeakRvwmoFloor.loadFoldVrNew'`, `store_fold_vRel` `WeakRvwmoFloor.storeFoldVRel`,
`elem_of_run_ats` `elemOfRunAts`, `elem_of_run_as` `elemOfRunAs`, `load_run_coh`
`loadRunCoh`, `load_run_vrOld` `loadRunVrOld`, `load_run_vrNew` `loadRunVrNew`,
`load_run_vrNew_plain` `loadRunVrNewPlain`, `load_run_vwOld` `loadRunVwOld`,
`load_run_vRel` `loadRunVRel`, `store_run_coh` `storeRunCoh`, `store_run_vwOld`
`storeRunVwOld`, `store_run_vRel` `storeRunVRel`, `store_run_vRel_norl` `storeRunVRelNorl`,
`store_run_vrOld` `storeRunVrOld`, `store_run_vrNew` `storeRunVrNew`, `lstep`
`WeakRvwmoFloor.lstep`, `mnext_ws_eq` `mnextWsEq`, `lstep_fwd0` `lstepFwd0`, `gshape`
`WeakRvwmoFloor.gshape`, `gpoloc_gmo` `gpolocGmo`, `gacq_gmo` `gacqGmo`, `grelacq_gmo`
`grelacqGmo`, `gfence_gmo` `gfenceGmo`, `gread_src_ub` `greadSrcUb`, `no_writes_in_of_ub`
`noWritesInOfUb`, `gcnt` `gcnt`, `gcnt_step_eq` `gcntStepEq`, `gcnt_step_ne` `gcntStepNe`,
`gcnt_take_le` `gcntTakeLe`, `gwmsg` `gwmsg`, `gtrace_prefix` `GtracePrefix` (fields
`gtp_img`…`gtp_log` ↦ `gtpImg`…`gtpLog`), `gtp_ev_eq` `gtpEvEq`, `gtp_log_writes`
`gtpLogWrites`, `gtp_log_byte` `gtpLogByte`, `Hrsome` `WeakRvwmoFloor.hrsome`, `Hrmem`
`WeakRvwmoFloor.hrmem`, `fhook` `fhook`, `ahook` `ahook`, `fhook_S` `fhookS`, `ahook_S`
`ahookS`, `finv` `finv`, `finv_init` `finvInit`, `finv_step` `finvStep`, `finv_replay`
`finvReplay`, `floor_of_graph_sec` `floorOfGraphSec`, `floor_of_graph` `floorOfGraph`,
`ev_snoc` `evSnoc`, `ev_snoc_lt` `evSnocLt`, `ev_snoc_end` `evSnocEnd`,
`gtrace_prefix_snoc` `gtracePrefixSnoc`, `gtrace_snoc_read_consistent`
`gtraceSnocReadConsistent`, `gtrace_snoc_write_consistent` `gtraceSnocWriteConsistent`,
`gtrace_prefix_empty` `gtracePrefixEmpty`, `gtrace_snoc_read_image` `gtraceSnocReadImage`.

**Dropped:** nothing (Rocq 72 declarations; Lean 72, no Lean-only helpers).
-/
import Weak.WeakRvwmoCert

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std

/-! # 1. `gvisUb`: "every write index below `n` is gmo-before `r`" -/

def gvisUb (G : Gexec) (r : Geid) (n : Nat) : Prop :=
  ∀ (s : Nat) w, gwriteAt G s = some w → s ≤ n → gmoLt G w r

theorem gvisUbDown (G : Gexec) (r : Geid) (m n : Nat) :
    m ≤ n → gvisUb G r n → gvisUb G r m :=
  fun hle h s w hw hs => h s w hw (by omega)

theorem gvisUb0 (G : Gexec) (r : Geid) : gvisUb G r 0 := by
  intro s w hw hs
  have : s = 0 := by omega
  subst this
  simp [gwriteAt] at hw

theorem gvisUbMaxcl (G : Gexec) (r : Geid) : maxcl (gvisUb G r) := by
  refine ⟨gvisUb0 G r, fun n1 n2 h1 h2 => ?_⟩
  rcases Nat.le_total n1 n2 with h | h
  · rw [Nat.max_eq_right h]; exact h2
  · rw [Nat.max_eq_left h]; exact h1

theorem gvisUbEv (G : Gexec) (r r' : Geid) (n : Nat) :
    gvisUb G r n → gmoLt G r r' → gvisUb G r' n :=
  fun h hlt s w hw hs => gmoLtTrans G _ _ _ (h s w hw hs) hlt

/-- THE INTRODUCTION RULE: a single gmo-before write bounds the whole prefix below it. -/
theorem gvisUbOfWrite (G : Gexec) (r : Geid) (t : Nat) (w : Geid) :
    gwf G → gwriteAt G t = some w → gmoLt G w r → gvisUb G r t := by
  intro hwf ht hlt s w' hs' hle
  have hnd := hwf.1
  obtain ⟨hw'g, hix'⟩ := gwriteAtInv G s w' hnd hs'
  obtain ⟨hwg, hix⟩ := gwriteAtInv G t w hnd ht
  by_cases hst : s = t
  · subst hst
    have : w' = w := gwixInj G w' w hnd hw'g hwg (by rw [hix', hix])
    subst this
    exact hlt
  · refine gmoLtTrans G _ _ _ ⟨((gwritesElemOf G w').1 hw'g).1, ((gwritesElemOf G w).1 hwg).1, ?_⟩ hlt
    exact (gwixGposLt G w' w hnd hw'g hwg).1 (by omega)

/-! # 2. The forward bank is view-free -/

def fwd0 (ws : Wstate) : Prop :=
  ∀ b tf vf, get? ws.wFwd b = some (tf, vf) → vf = 0

theorem fwd0Init : fwd0 wsInit := by
  intro b tf vf h
  have h0 : get? wsInit.wFwd b = none := lookupEmpty
  rw [h0] at h
  cases h

theorem fwd0Ext (ws ws' : Wstate) : ws'.wFwd = ws.wFwd → fwd0 ws → fwd0 ws' := by
  intro heq h b tf vf hb
  rw [heq] at hb
  exact h b tf vf hb

theorem fwdViewP (P : Nat → Prop) (ws : Wstate) (aq : Bool) (b : Int) (t : Nat) :
    maxcl P → fwd0 ws → P t → P (fwdView ws aq b t) := by
  intro hcl h0 ht
  cases aq with
  | true => rw [fwdViewAq]; exact ht
  | false =>
    cases hf : get? ws.wFwd b with
    | none => rw [fwdViewMiss ws false b t hf]; exact ht
    | some p =>
      obtain ⟨tf, vf⟩ := p
      by_cases htf : t = tf
      · rw [fwdViewHit ws b t tf vf hf htf, h0 b tf vf hf]; exact maxcl0 P hcl
      · have : fwdView ws false b t = t := by simp [fwdView, hf, htf]
        rw [this]; exact ht

theorem fwd0StorePost (ws : Wstate) (rl : Bool) (b : Int) (t : Nat) :
    fwd0 ws → fwd0 (storePost ws rl b t) := by
  intro h b' tf vf hb
  by_cases hbb : b' = b
  · subst hbb
    have : get? (storePost ws rl b' t).wFwd b' = some (t, 0) := lookupInsert
    rw [this] at hb
    simp only [Option.some.injEq, Prod.mk.injEq] at hb
    exact hb.2.symm
  · have : get? (storePost ws rl b t).wFwd b' = get? ws.wFwd b' := lookupInsertNe (Ne.symm hbb)
    rw [this] at hb
    exact h b' tf vf hb

theorem fwd0StoreFold (rl : Bool) (t : Nat) (as_ : List Int) (ws : Wstate) :
    fwd0 ws → fwd0 (as_.foldl (fun w b => storePost w rl b t) ws) := by
  induction as_ generalizing ws with
  | nil => intro h; exact h
  | cons b l ih => intro h; exact ih _ (fwd0StorePost ws rl b t h)

theorem fwd0StorePostRun (ws : Wstate) (rl : Bool) (base : Int) (n t : Nat) :
    fwd0 ws → fwd0 (storePostRun ws rl base n t) := by
  intro h
  exact fwd0Ext _ _ (ctrlPostFwd _ _) (fwd0StoreFold rl t _ ws h)

theorem fwd0LoadPostRun (ws : Wstate) (aq : Bool) (base : Int) (ts : List Nat) :
    fwd0 ws → fwd0 (loadPostRun ws aq base ts) :=
  fun h => fwd0Ext _ _ (loadPostRunFwd ws aq base ts) h

theorem fwd0FencePost (ws : Wstate) (pr pw sr sw : Bool) :
    fwd0 ws → fwd0 (fencePost ws pr pw sr sw) :=
  fun h => fwd0Ext _ _ (fencePostFwd ws pr pw sr sw) h

/-! # 3. The domination fold lemmas, at `fwd0` -/

theorem WeakRvwmoFloor.loadFoldCoh' (P : Nat → Prop) (aq : Bool) (vpre : Nat)
    (ats : List (Int × Nat)) (ws : Wstate) (a : Int) :
    maxcl P → fwd0 ws →
    P (coh ws a) → P vpre → (∀ p ∈ ats, p.1 = a → P p.2) →
    P (coh (ats.foldl (fun w at_ => loadPostAt w aq vpre at_.1 at_.2) ws) a) := by
  intro hcl
  induction ats generalizing ws with
  | nil => intro _ hc _ _; exact hc
  | cons p l ih =>
    intro hfw hc hv hts
    apply ih (loadPostAt ws aq vpre p.1 p.2) (fwd0Ext _ _ (loadPostAtFwd _ _ _ _ _) hfw) _ hv
      (fun q hq hqa => hts q (List.mem_cons_of_mem _ hq) hqa)
    by_cases heq : a = p.1
    · have hpa : P p.2 := hts p List.mem_cons_self heq.symm
      rw [heq, cohLoadPostAtEq]
      rw [heq] at hc
      exact maxclMax P _ _ hcl hc
        (maxclMax P _ _ hcl (maxclMax P _ _ hcl hv (fwdViewP P ws aq p.1 p.2 hcl hfw hpa)) hpa)
    · rw [cohLoadPostAtNe _ _ _ _ _ _ heq]; exact hc

theorem WeakRvwmoFloor.loadFoldVrOld' (P : Nat → Prop) (aq : Bool) (vpre : Nat)
    (ats : List (Int × Nat)) (ws : Wstate) :
    maxcl P → fwd0 ws →
    P ws.wVrOld → P vpre → (∀ p ∈ ats, P p.2) →
    P (ats.foldl (fun w at_ => loadPostAt w aq vpre at_.1 at_.2) ws).wVrOld := by
  intro hcl
  induction ats generalizing ws with
  | nil => intro _ hc _ _; exact hc
  | cons p l ih =>
    intro hfw hc hv hts
    apply ih (loadPostAt ws aq vpre p.1 p.2) (fwd0Ext _ _ (loadPostAtFwd _ _ _ _ _) hfw) _ hv
      (fun q hq => hts q (List.mem_cons_of_mem _ hq))
    show P (max ws.wVrOld (max vpre (fwdView ws aq p.1 p.2)))
    exact maxclMax P _ _ hcl hc
      (maxclMax P _ _ hcl hv (fwdViewP P ws aq p.1 p.2 hcl hfw (hts p List.mem_cons_self)))

theorem WeakRvwmoFloor.loadFoldVrNew' (P : Nat → Prop) (aq : Bool) (vpre : Nat)
    (ats : List (Int × Nat)) (ws : Wstate) :
    maxcl P → fwd0 ws →
    P ws.wVrNew → P vpre → (∀ p ∈ ats, P p.2) →
    P (ats.foldl (fun w at_ => loadPostAt w aq vpre at_.1 at_.2) ws).wVrNew := by
  intro hcl
  induction ats generalizing ws with
  | nil => intro _ hc _ _; exact hc
  | cons p l ih =>
    intro hfw hc hv hts
    apply ih (loadPostAt ws aq vpre p.1 p.2) (fwd0Ext _ _ (loadPostAtFwd _ _ _ _ _) hfw) _ hv
      (fun q hq => hts q (List.mem_cons_of_mem _ hq))
    cases aq with
    | false => exact hc
    | true =>
      show P (max ws.wVrNew (max vpre (fwdView ws true p.1 p.2)))
      exact maxclMax P _ _ hcl hc
        (maxclMax P _ _ hcl hv (fwdViewP P ws true p.1 p.2 hcl hfw (hts p List.mem_cons_self)))

theorem WeakRvwmoFloor.storeFoldVRel (P : Nat → Prop) (rl : Bool) (t : Nat) (as_ : List Int)
    (ws : Wstate) :
    maxcl P → P ws.wVRel → P t →
    P (as_.foldl (fun w b => storePost w rl b t) ws).wVRel := by
  intro hcl
  induction as_ generalizing ws with
  | nil => intro hc _; exact hc
  | cons b l ih =>
    intro hc ht
    apply ih _ _ ht
    cases rl with
    | false => exact hc
    | true => exact maxclMax P _ _ hcl hc ht

/-! ## 3.1 The two footprint-membership dictionaries -/

theorem elemOfRunAts (base : Int) (ts : List Nat) (p : Int × Nat) :
    p ∈ List.zipWith (fun (j : Nat) (t : Nat) => (base + (j : Int), t))
          (List.range' 0 ts.length) ts →
    ∃ j : Nat, j < ts.length ∧ ts[j]? = some p.2 ∧ p.1 = accAddr base j := by
  intro hp
  obtain ⟨j, hj, he⟩ := elemOfZipSeq base ts p hp
  exact ⟨j, lookup_lt_Some hj, hj, he⟩

theorem elemOfRunAs (base : Int) (n : Nat) (b : Int) :
    b ∈ (List.range' 0 n).map (fun j : Nat => base + (j : Int)) →
    ∃ j : Nat, j < n ∧ b = accAddr base j :=
  elemOfMapSeq base n b

/-! ## 3.2 The run level -/

theorem loadRunCoh (P : Nat → Prop) (ws : Wstate) (aq : Bool) (base : Int) (ts : List Nat)
    (a : Int) :
    maxcl P → fwd0 ws → P (coh ws a) → P (loadVpre ws aq) →
    (∀ (j : Nat) t, ts[j]? = some t → accAddr base j = a → P t) →
    P (coh (loadPostRun ws aq base ts) a) := by
  intro hcl hfw hc hv hts
  rw [loadPostRun, ctrlPostCoh]
  apply WeakRvwmoFloor.loadFoldCoh' P aq _ _ ws a hcl hfw hc hv
  intro p hp hpa
  obtain ⟨j, _, ht, he⟩ := elemOfRunAts base ts p hp
  exact hts j p.2 ht (by rw [← he]; exact hpa)

theorem loadRunVrOld (P : Nat → Prop) (ws : Wstate) (aq : Bool) (base : Int) (ts : List Nat) :
    maxcl P → fwd0 ws → P ws.wVrOld → P (loadVpre ws aq) →
    (∀ (j : Nat) t, ts[j]? = some t → P t) →
    P (loadPostRun ws aq base ts).wVrOld := by
  intro hcl hfw hc hv hts
  rw [loadPostRun, ctrlPostVrOld]
  apply WeakRvwmoFloor.loadFoldVrOld' P aq _ _ ws hcl hfw hc hv
  intro p hp
  obtain ⟨j, _, ht, _⟩ := elemOfRunAts base ts p hp
  exact hts j p.2 ht

theorem loadRunVrNew (P : Nat → Prop) (ws : Wstate) (aq : Bool) (base : Int) (ts : List Nat) :
    maxcl P → fwd0 ws → P ws.wVrNew → P (loadVpre ws aq) →
    (∀ (j : Nat) t, ts[j]? = some t → P t) →
    P (loadPostRun ws aq base ts).wVrNew := by
  intro hcl hfw hc hv hts
  rw [loadPostRun, ctrlPostVrNew]
  apply WeakRvwmoFloor.loadFoldVrNew' P aq _ _ ws hcl hfw hc hv
  intro p hp
  obtain ⟨j, _, ht, _⟩ := elemOfRunAts base ts p hp
  exact hts j p.2 ht

theorem loadRunVrNewPlain (ws : Wstate) (base : Int) (ts : List Nat) :
    (loadPostRun ws false base ts).wVrNew = ws.wVrNew := by
  rw [loadPostRun, ctrlPostVrNew]
  exact loadFoldVrNewPlain _ _ _

theorem loadRunVwOld (ws : Wstate) (aq : Bool) (base : Int) (ts : List Nat) :
    (loadPostRun ws aq base ts).wVwOld = ws.wVwOld := by
  rw [loadPostRun, ctrlPostVwOld]
  exact loadFoldVwOld _ _ _ _

theorem loadRunVRel (ws : Wstate) (aq : Bool) (base : Int) (ts : List Nat) :
    (loadPostRun ws aq base ts).wVRel = ws.wVRel := by
  rw [loadPostRun, ctrlPostVRel]
  exact loadFoldVRel _ _ _ _

theorem storeRunCoh (P : Nat → Prop) (ws : Wstate) (rl : Bool) (base : Int) (n t : Nat)
    (a : Int) :
    maxcl P → P (coh ws a) →
    ((∃ j : Nat, j < n ∧ accAddr base j = a) → P t) →
    P (coh (storePostRun ws rl base n t) a) := by
  intro hcl hc ht
  rw [storePostRun, ctrlPostCoh]
  apply storeFoldCoh P rl t _ ws a hcl hc
  intro hin
  obtain ⟨j, hj, he⟩ := elemOfRunAs base n a hin
  exact ht ⟨j, hj, he.symm⟩

theorem storeRunVwOld (P : Nat → Prop) (ws : Wstate) (rl : Bool) (base : Int) (n t : Nat) :
    maxcl P → P ws.wVwOld → P t →
    P (storePostRun ws rl base n t).wVwOld := by
  intro hcl hc ht
  rw [storePostRun, ctrlPostVwOld]
  exact storeFoldVwOld P rl t _ ws hcl hc ht

theorem storeRunVRel (P : Nat → Prop) (ws : Wstate) (rl : Bool) (base : Int) (n t : Nat) :
    maxcl P → P ws.wVRel → P t →
    P (storePostRun ws rl base n t).wVRel := by
  intro hcl hc ht
  rw [storePostRun, ctrlPostVRel]
  exact WeakRvwmoFloor.storeFoldVRel P rl t _ ws hcl hc ht

theorem storeRunVRelNorl (ws : Wstate) (base : Int) (n t : Nat) :
    (storePostRun ws false base n t).wVRel = ws.wVRel := by
  rw [storePostRun, ctrlPostVRel]
  exact storeFoldVRelNorl _ _ _

theorem storeRunVrOld (ws : Wstate) (rl : Bool) (base : Int) (n t : Nat) :
    (storePostRun ws rl base n t).wVrOld = ws.wVrOld := by
  rw [storePostRun, ctrlPostVrOld]
  exact storeFoldVrOld _ _ _ _

theorem storeRunVrNew (ws : Wstate) (rl : Bool) (base : Int) (n t : Nat) :
    (storePostRun ws rl base n t).wVrNew = ws.wVrNew := by
  rw [storePostRun, ctrlPostVrNew]
  exact storeFoldVrNew _ _ _ _

/-! ## 3.3 The one-step wstate of the acting agent -/

def WeakRvwmoFloor.lstep (tw : Nat) (ws : Wstate) (l : Lbl) : Wstate :=
  match l with
  | .LLoad aq base ts _ => loadPostRun ws aq base ts
  | .LStore rl base vs _ => storePostRun ws rl base vs.length tw
  | .LFence pr pw sr sw => fencePost ws pr pw sr sw
  | .LRmw aq rl base ts _ wvs _ =>
    storePostRun (loadPostRun ws aq base ts) rl base wvs.length tw

theorem mnextWsEq (σ : Mstate) (i : Nat) (l : Lbl) :
    (mnext σ i l).msWs i = WeakRvwmoFloor.lstep (σ.msLog.length + 1) (σ.msWs i) l := by
  cases l <;> exact updWsEq _ _ _

theorem lstepFwd0 (tw : Nat) (ws : Wstate) (l : Lbl) :
    fwd0 ws → fwd0 (WeakRvwmoFloor.lstep tw ws l) := by
  intro h
  cases l with
  | LLoad => exact fwd0LoadPostRun _ _ _ _ h
  | LStore => exact fwd0StorePostRun _ _ _ _ _ h
  | LFence => exact fwd0FencePost _ _ _ _ _ h
  | LRmw => exact fwd0StorePostRun _ _ _ _ _ (fwd0LoadPostRun _ _ _ _ h)

/-! # 4. The graph side: the four ppo⁻ arms as ordering facts -/

/-- `gwf`'s shape clause, read at a label. -/
theorem WeakRvwmoFloor.gshape (G : Gexec) (hwf : gwf G) (e : Geid) (l : Lbl) :
    gxLbl G e = some l →
    match l with
    | .LLoad _ _ ts vs => vs.length = ts.length
    | .LStore _ _ vs _ => vs ≠ []
    | .LFence _ _ _ _ => True
    | .LRmw _ _ _ ts rvs wvs _ =>
        wvs ≠ [] ∧ wvs.length = ts.length ∧ rvs.length = ts.length :=
  fun hl => gwfLblShape G e l hwf hl

/-! ## 4.1 The ordering arms -/

theorem gpolocGmo (G : Gexec) (hppo : gppoGmo G) (e1 e2 : Geid) (b : Int) :
    WeakRvwmoGraph.gpo G e1 e2 → gaccesses G e1 b → gaccesses G e2 b → gmoLt G e1 e2 :=
  fun h1 h2 h3 => hppo _ _ (.inl ⟨h1, b, h2, h3⟩)

theorem gacqGmo (G : Gexec) (hppo : gppoGmo G) (e1 e2 : Geid) :
    WeakRvwmoGraph.gpo G e1 e2 → glblIs G e1 lbIsR → glblIs G e1 lbAq → gmem G e2 →
    gmoLt G e1 e2 :=
  fun h1 h2 h3 h4 => hppo _ _ (.inr (.inr (.inl ⟨h1, h2, h3, h4⟩)))

theorem grelacqGmo (G : Gexec) (hppo : gppoGmo G) (e1 e2 : Geid) :
    WeakRvwmoGraph.gpo G e1 e2 → glblIs G e1 lbIsW → glblIs G e1 lbRl →
    glblIs G e2 lbIsR → glblIs G e2 lbAq → gmoLt G e1 e2 :=
  fun h1 h2 h3 h4 h5 => hppo _ _ (.inr (.inr (.inr ⟨h1, h2, h3, h4, h5⟩)))

theorem gfenceGmo (G : Gexec) (hppo : gppoGmo G) (e1 e2 : Geid) (kf : Nat) (pr pw sr sw : Bool) :
    e1.1 = e2.1 → e1.2 < kf → kf < e2.2 →
    gxLbl G (e1.1, kf) = some (.LFence pr pw sr sw) →
    ((glblIs G e1 lbIsR ∧ pr = true) ∨ (glblIs G e1 lbIsW ∧ pw = true)) →
    ((glblIs G e2 lbIsR ∧ sr = true) ∨ (glblIs G e2 lbIsW ∧ sw = true)) →
    gmoLt G e1 e2 :=
  fun hag h1 h2 hf hp hs =>
    hppo _ _ (.inr (.inl ⟨pr, pw, sr, sw, ⟨hag, by omega, kf, h1, h2, hf⟩, hp, hs⟩))

/-! ## 4.2 The source bound — `gloadValue`'s existence half -/

theorem greadSrcUb (G : Gexec) (hwf : gwf G) (hppo : gppoGmo G) (hlv : gloadValue G)
    (r e : Geid) (b : Int) (t : Nat) (v : BitVec 8) :
    greadsByte G e b t v → gmoLt G e r → gvisUb G r t := by
  intro hr hlt
  cases t with
  | zero => exact gvisUb0 G r
  | succ n =>
    obtain ⟨w, hw, hwb, hvis⟩ := (hlv e b (n + 1) v hr).1
    have hwe : gmoLt G w e := by
      rcases hvis with hv | hv
      · exact hv
      · exact gpolocGmo G hppo w e b hv (.inl ⟨v, hwb⟩) (.inr ⟨n + 1, v, hr⟩)
    exact gvisUbOfWrite G r (n + 1) w hwf hw (gmoLtTrans G _ _ _ hwe hlt)

/-! ## 4.3 The payoff shape — `gloadValue`'s co-maximality half -/

theorem noWritesInOfUb (G : Gexec) (hwf : gwf G) (hlv : gloadValue G)
    (r : Geid) (b : Int) (t : Nat) (v : BitVec 8) (log : List Wmsg) (n : Nat) :
    greadsByte G r b t v →
    (∀ (s : Nat) m, 0 < s → log[s - 1]? = some m →
       ∀ b', (msgByte m b').isSome →
         ∃ w v', gwriteAt G s = some w ∧ gwritesByte G w b' v') →
    gvisUb G r n → ¬ writesIn log b t n := by
  rintro hr hlog hub ⟨s, hlo, hhi, m, hm, hby⟩
  obtain ⟨w, v', hw, hwb⟩ := hlog s m (by omega) hm b hby
  have hgmo := hub s w hw hhi
  have hle := (hlv r b t v hr).2 w v' hwb (.inl hgmo)
  rw [(gwriteAtInv G s w hwf.1 hw).2] at hle
  omega

/-! # 5. G-trace prefixes -/

def gcnt (i : Nat) (tr : List Estep) : Nat :=
  (tr.filter (fun s => decide (s.esAg = i))).length

theorem gcntStepEq (i : Nat) (tr : List Estep) (k : Nat) (s : Estep) :
    tr[k]? = some s → s.esAg = i → gcnt i (tr.take (k + 1)) = gcnt i (tr.take k) + 1 := by
  intro hk hag
  simp [gcnt, List.take_add_one, hk, List.filter_append, hag]

theorem gcntStepNe (i : Nat) (tr : List Estep) (k : Nat) (s : Estep) :
    tr[k]? = some s → s.esAg ≠ i → gcnt i (tr.take (k + 1)) = gcnt i (tr.take k) := by
  intro hk hag
  simp [gcnt, List.take_add_one, hk, List.filter_append, hag]

theorem gcntTakeLe (i : Nat) (tr : List Estep) (k : Nat) : gcnt i (tr.take k) ≤ gcnt i tr :=
  ((List.take_sublist k tr).filter _).length_le

/-- The message a graph write contributes to the log. -/
def gwmsg (G : Gexec) (w : Geid) : Option Wmsg :=
  match gxLbl G w with
  | some l =>
    match lbWr l with
    | some (base, vs) => some ⟨base, vs, some w.1, lbCls l⟩
    | none => none
  | none => none

structure GtracePrefix (G : Gexec) (c : Cand) (ev : Nat → Geid) : Prop where
  gtpImg : c.cdImg = G.gxImg
  gtpAg : ∀ p s, c.cdTr[p]? = some s → (ev p).1 = s.esAg
  gtpPos : ∀ p s, c.cdTr[p]? = some s → (ev p).2 = gcnt s.esAg (c.cdTr.take p)
  gtpLbl : ∀ p s, c.cdTr[p]? = some s → gxLbl G (ev p) = some s.esLb
  gtpWix : ∀ p s, c.cdTr[p]? = some s → lbIsW s.esLb = true →
    gwix G (ev p) = (cdLog c p).length + 1
  gtpLog : ∀ s : Nat, 0 < s → s ≤ (cdLog c c.cdTr.length).length →
    ∃ w, gwriteAt G s = some w ∧ (cdLog c c.cdTr.length)[s - 1]? = gwmsg G w

theorem gtpEvEq (G : Gexec) (c : Cand) (ev : Nat → Geid) (p : Nat) (s : Estep) :
    GtracePrefix G c ev → c.cdTr[p]? = some s →
    ev p = (s.esAg, gcnt s.esAg (c.cdTr.take p)) :=
  fun hgt hs => Prod.ext (hgt.gtpAg p s hs) (hgt.gtpPos p s hs)

/-- THE LOG DICTIONARY, log → graph. -/
theorem gtpLogWrites (G : Gexec) (c : Cand) (ev : Nat → Geid) :
    GtracePrefix G c ev →
    ∀ (s : Nat) m, 0 < s → (cdLog c c.cdTr.length)[s - 1]? = some m →
      ∀ b, (msgByte m b).isSome →
        ∃ w v', gwriteAt G s = some w ∧ gwritesByte G w b v' := by
  intro hgt s m hs hm b hv
  obtain ⟨v, hv⟩ := someOfIsSome hv
  have hle : s ≤ (cdLog c c.cdTr.length).length := by have := lookup_lt_Some hm; omega
  obtain ⟨w, hw, heq⟩ := hgt.gtpLog s hs hle
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
      · rename_i hba
        refine ⟨w, v, hw, l, base, vs, (b - base).toNat, hl, hwr, hv, ?_⟩
        simp only [accAddr]; omega
      · cases hv

/-- THE LOG DICTIONARY, graph → log. -/
theorem gtpLogByte (G : Gexec) (c : Cand) (ev : Nat → Geid) :
    GtracePrefix G c ev →
    ∀ (s : Nat) w b v, 0 < s → s ≤ (cdLog c c.cdTr.length).length →
      gwriteAt G s = some w → gwritesByte G w b v →
      logByte c.cdImg (cdLog c c.cdTr.length) s b = some v := by
  rintro hgt s w b v hs hle hw ⟨l, base, vs, j, hl, hwr, hj, hb⟩
  obtain ⟨w', hw', heq⟩ := hgt.gtpLog s hs hle
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

/-! # 6. The invariant and its induction -/

theorem WeakRvwmoFloor.hrsome (G : Gexec) (r : Geid) (hrr : glblIs G r lbIsR) :
    (gxLbl G r).isSome := by
  obtain ⟨l, hl, _⟩ := hrr
  rw [hl]; rfl

theorem WeakRvwmoFloor.hrmem (G : Gexec) (r : Geid) (hrr : glblIs G r lbIsR) : gmem G r :=
  WeakRvwmoGraph.glblIsRGmem G r hrr

def fhook (G : Gexec) (r : Geid) (k : Nat) (pb : Bool) : Prop :=
  ∃ (kf : Nat) (pr pw sr sw : Bool), k ≤ kf ∧ kf < r.2 ∧
    gxLbl G (r.1, kf) = some (.LFence pr pw sr sw) ∧
    (if pb then pr else pw) = true ∧ sr = true

def ahook (G : Gexec) (r : Geid) (k : Nat) : Prop :=
  ∃ kf : Nat, k ≤ kf ∧
    glblIs G (r.1, kf) lbIsR ∧ glblIs G (r.1, kf) lbAq ∧
    ((r.1, kf) = r ∨ gmoLt G (r.1, kf) r)

theorem fhookS (G : Gexec) (r : Geid) (k : Nat) (pb : Bool) :
    fhook G r (k + 1) pb → fhook G r k pb := by
  rintro ⟨kf, pr, pw, sr, sw, h1, h2, h3, h4, h5⟩
  exact ⟨kf, pr, pw, sr, sw, by omega, h2, h3, h4, h5⟩

theorem ahookS (G : Gexec) (r : Geid) (k : Nat) : ahook G r (k + 1) → ahook G r k := by
  rintro ⟨kf, h1, h2, h3, h4⟩
  exact ⟨kf, by omega, h2, h3, h4⟩

def finv (G : Gexec) (r : Geid) (a : Int) (k : Nat) (ws : Wstate) : Prop :=
  fwd0 ws ∧
  gvisUb G r (coh ws a) ∧
  gvisUb G r ws.wVrNew ∧
  (ahook G r k → gvisUb G r ws.wVRel) ∧
  (fhook G r k true → gvisUb G r ws.wVrOld) ∧
  (fhook G r k false → gvisUb G r ws.wVwOld)

theorem finvInit (G : Gexec) (r : Geid) (a : Int) : finv G r a 0 wsInit := by
  refine ⟨fwd0Init, ?_, gvisUb0 G r, fun _ => gvisUb0 G r, fun _ => gvisUb0 G r,
    fun _ => gvisUb0 G r⟩
  rw [cohInit]; exact gvisUb0 G r

/-! ## 6.1 THE STEP -/

theorem finvStep (G : Gexec) (hwf : gwf G) (hppo : gppoGmo G) (hlv : gloadValue G)
    (r : Geid) (a : Int) (hrr : glblIs G r lbIsR) (hra : gaccesses G r a)
    (k : Nat) (l : Lbl) (ws : Wstate) (tw : Nat) :
    k < r.2 →
    gxLbl G (r.1, k) = some l →
    (lbIsW l = true → gwix G (r.1, k) = tw) →
    finv G r a k ws → finv G r a (k + 1) (WeakRvwmoFloor.lstep tw ws l) := by
  rintro hk hl htw ⟨hfw, hcoh, hrn, hrel, hro, hwo⟩
  have hcl : maxcl (gvisUb G r) := gvisUbMaxcl G r
  have hesome : (gxLbl G (r.1, k)).isSome := by rw [hl]; rfl
  have hpo : WeakRvwmoGraph.gpo G (r.1, k) r :=
    ⟨rfl, hk, hesome, WeakRvwmoFloor.hrsome G r hrr⟩
  -- the four ordering arms, as they apply to THIS event
  have hoacc : gaccesses G (r.1, k) a → gmoLt G (r.1, k) r :=
    fun hacc => gpolocGmo G hppo _ _ a hpo hacc hra
  have hoaq : glblIs G (r.1, k) lbIsR → glblIs G (r.1, k) lbAq → gmoLt G (r.1, k) r :=
    fun h1 h2 => gacqGmo G hppo _ _ hpo h1 h2 (WeakRvwmoFloor.hrmem G r hrr)
  have hof : ∀ pb, fhook G r (k + 1) pb →
      (if pb then glblIs G (r.1, k) lbIsR else glblIs G (r.1, k) lbIsW) →
      gmoLt G (r.1, k) r := by
    rintro pb ⟨kf, pr, pw, sr, sw, hk1, hk2, hf, hpb, hsr⟩ hcls
    apply gfenceGmo G hppo (r.1, k) r kf pr pw sr sw rfl (show k < kf by omega) hk2 hf
    · cases pb with
      | true => exact .inl ⟨hcls, hpb⟩
      | false => exact .inr ⟨hcls, hpb⟩
    · exact .inl ⟨hrr, hsr⟩
  have horl : ahook G r (k + 1) → glblIs G (r.1, k) lbIsW →
      glblIs G (r.1, k) lbRl → gmoLt G (r.1, k) r := by
    rintro ⟨kf, hk1, hr1, hr2, hle⟩ hw hrl
    have hpo2 : WeakRvwmoGraph.gpo G (r.1, k) (r.1, kf) := by
      obtain ⟨l', hl', _⟩ := hr1
      exact ⟨rfl, show k < kf by omega, hesome, by rw [hl']; rfl⟩
    have hlt := grelacqGmo G hppo _ _ hpo2 hw hrl hr1 hr2
    rcases hle with heq | hlt2
    · rw [heq] at hlt; exact hlt
    · exact gmoLtTrans G _ _ _ hlt hlt2
  -- the two byte dictionaries and the two index bounds
  have haccRd : ∀ base ts vs (j : Nat) t',
      lbRd l = some (base, ts, vs) → vs.length = ts.length →
      ts[j]? = some t' → gaccesses G (r.1, k) (accAddr base j) := by
    intro base ts vs j t' hrd hlen hj
    have hjlt : j < vs.length := by rw [hlen]; exact lookup_lt_Some hj
    obtain ⟨v', hv'⟩ := someOfIsSome (lookup_lt_is_Some_2 hjlt)
    exact .inr ⟨t', v', l, base, ts, vs, j, hl, hrd, hj, hv', rfl⟩
  have hsrc : ∀ base ts vs (j : Nat) t',
      lbRd l = some (base, ts, vs) → vs.length = ts.length →
      gmoLt G (r.1, k) r → ts[j]? = some t' → gvisUb G r t' := by
    intro base ts vs j t' hrd hlen hord hj
    have hjlt : j < vs.length := by rw [hlen]; exact lookup_lt_Some hj
    obtain ⟨v', hv'⟩ := someOfIsSome (lookup_lt_is_Some_2 hjlt)
    exact greadSrcUb G hwf hppo hlv r (r.1, k) (accAddr base j) t' v'
      ⟨l, base, ts, vs, j, hl, hrd, hj, hv', rfl⟩ hord
  have haccWr : ∀ base vs (j : Nat),
      lbWr l = some (base, vs) → j < vs.length →
      gaccesses G (r.1, k) (accAddr base j) := by
    intro base vs j hwr hj
    obtain ⟨v', hv'⟩ := someOfIsSome (lookup_lt_is_Some_2 hj)
    exact .inl ⟨v', l, base, vs, j, hl, hwr, hv', rfl⟩
  have hwix : lbIsW l = true → gmoLt G (r.1, k) r → gvisUb G r tw := by
    intro hw hord
    have hg : (r.1, k) ∈ gwrites G :=
      gisWGwrites G _ hwf hesome (by simp only [gisW, hl]; exact hw)
    apply gvisUbOfWrite G r tw (r.1, k) hwf _ hord
    rw [← htw hw]; exact gwriteAtGwix G _ hg
  cases l with
  | LLoad aq base ts vs =>
    -- ---------------- LLoad ----------------
    have hlen : vs.length = ts.length := WeakRvwmoFloor.gshape G hwf _ _ hl
    have hisr : glblIs G (r.1, k) lbIsR := ⟨_, hl, rfl⟩
    have hvpre : gvisUb G r (loadVpre ws aq) := by
      unfold loadVpre
      apply maxclMax _ _ _ hcl hrn
      cases aq with
      | false => exact gvisUb0 G r
      | true => exact hrel ⟨k, Nat.le_refl _, hisr, ⟨_, hl, rfl⟩, .inr (hoaq hisr ⟨_, hl, rfl⟩)⟩
    simp only [finv, WeakRvwmoFloor.lstep]
    refine ⟨fwd0LoadPostRun _ _ _ _ hfw, ?_, ?_, ?_, ?_, ?_⟩
    · apply loadRunCoh _ ws aq base ts a hcl hfw hcoh hvpre
      intro j t' hj hja
      have hord : gmoLt G (r.1, k) r := by
        apply hoacc; rw [← hja]; exact haccRd base ts vs j t' rfl hlen hj
      exact hsrc base ts vs j t' rfl hlen hord hj
    · cases aq with
      | true =>
        apply loadRunVrNew _ ws true base ts hcl hfw hrn hvpre
        intro j t' hj
        exact hsrc base ts vs j t' rfl hlen (hoaq hisr ⟨_, hl, rfl⟩) hj
      | false => rw [loadRunVrNewPlain]; exact hrn
    · rw [loadRunVRel]; intro hah; exact hrel (ahookS G r k hah)
    · intro hfh
      apply loadRunVrOld _ ws aq base ts hcl hfw (hro (fhookS G r k true hfh)) hvpre
      intro j t' hj
      exact hsrc base ts vs j t' rfl hlen (hof true hfh hisr) hj
    · rw [loadRunVwOld]; intro hfh; exact hwo (fhookS G r k false hfh)
  | LStore rl base vs kc =>
    -- ---------------- LStore ----------------
    have hisw : glblIs G (r.1, k) lbIsW := ⟨_, hl, rfl⟩
    simp only [finv, WeakRvwmoFloor.lstep]
    refine ⟨fwd0StorePostRun _ _ _ _ _ hfw, ?_, ?_, ?_, ?_, ?_⟩
    · apply storeRunCoh _ ws rl base vs.length tw a hcl hcoh
      rintro ⟨j, hj, hja⟩
      apply hwix rfl
      apply hoacc; rw [← hja]; exact haccWr base vs j rfl hj
    · rw [storeRunVrNew]; exact hrn
    · intro hah
      cases rl with
      | true =>
        exact storeRunVRel _ ws true base _ tw hcl (hrel (ahookS G r k hah))
          (hwix rfl (horl hah hisw ⟨_, hl, rfl⟩))
      | false => rw [storeRunVRelNorl]; exact hrel (ahookS G r k hah)
    · rw [storeRunVrOld]; intro hfh; exact hro (fhookS G r k true hfh)
    · intro hfh
      exact storeRunVwOld _ ws rl base _ tw hcl (hwo (fhookS G r k false hfh))
        (hwix rfl (hof false hfh hisw))
  | LFence pr pw sr sw =>
    -- ---------------- LFence ----------------
    simp only [finv, WeakRvwmoFloor.lstep]
    refine ⟨fwd0FencePost _ _ _ _ _ hfw, hcoh, ?_, ?_, ?_, ?_⟩
    · apply fencePostVrNewPred _ ws pr pw sr sw hcl hrn
      · intro hpr hsr; exact hro ⟨k, pr, pw, sr, sw, Nat.le_refl _, hk, hl, hpr, hsr⟩
      · intro hpw hsr; exact hwo ⟨k, pr, pw, sr, sw, Nat.le_refl _, hk, hl, hpw, hsr⟩
    · intro hah; exact hrel (ahookS G r k hah)
    · intro hfh; exact hro (fhookS G r k true hfh)
    · intro hfh; exact hwo (fhookS G r k false hfh)
  | LRmw aq rl base ts rvs wvs kc =>
    -- ---------------- LRmw ----------------
    obtain ⟨hne, hlenw, hlenr⟩ := WeakRvwmoFloor.gshape G hwf _ _ hl
    have hisr : glblIs G (r.1, k) lbIsR := ⟨_, hl, rfl⟩
    have hisw : glblIs G (r.1, k) lbIsW := ⟨_, hl, rfl⟩
    have hvpre : gvisUb G r (loadVpre ws aq) := by
      unfold loadVpre
      apply maxclMax _ _ _ hcl hrn
      cases aq with
      | false => exact gvisUb0 G r
      | true => exact hrel ⟨k, Nat.le_refl _, hisr, ⟨_, hl, rfl⟩, .inr (hoaq hisr ⟨_, hl, rfl⟩)⟩
    simp only [finv, WeakRvwmoFloor.lstep]
    refine ⟨fwd0StorePostRun _ _ _ _ _ (fwd0LoadPostRun _ _ _ _ hfw), ?_, ?_, ?_, ?_, ?_⟩
    · apply storeRunCoh _ _ rl base wvs.length tw a hcl
      · apply loadRunCoh _ ws aq base ts a hcl hfw hcoh hvpre
        intro j t' hj hja
        have hord : gmoLt G (r.1, k) r := by
          apply hoacc; rw [← hja]; exact haccRd base ts rvs j t' rfl hlenr hj
        exact hsrc base ts rvs j t' rfl hlenr hord hj
      · rintro ⟨j, hj, hja⟩
        apply hwix rfl
        apply hoacc; rw [← hja]; exact haccWr base wvs j rfl hj
    · rw [storeRunVrNew]
      cases aq with
      | true =>
        apply loadRunVrNew _ ws true base ts hcl hfw hrn hvpre
        intro j t' hj
        exact hsrc base ts rvs j t' rfl hlenr (hoaq hisr ⟨_, hl, rfl⟩) hj
      | false => rw [loadRunVrNewPlain]; exact hrn
    · intro hah
      cases rl with
      | true =>
        apply storeRunVRel _ _ true base _ tw hcl
        · rw [loadRunVRel]; exact hrel (ahookS G r k hah)
        · exact hwix rfl (horl hah hisw ⟨_, hl, rfl⟩)
      | false => rw [storeRunVRelNorl, loadRunVRel]; exact hrel (ahookS G r k hah)
    · rw [storeRunVrOld]
      intro hfh
      apply loadRunVrOld _ ws aq base ts hcl hfw (hro (fhookS G r k true hfh)) hvpre
      intro j t' hj
      exact hsrc base ts rvs j t' rfl hlenr (hof true hfh hisr) hj
    · intro hfh
      apply storeRunVwOld _ _ rl base _ tw hcl
      · rw [loadRunVwOld]; exact hwo (fhookS G r k false hfh)
      · exact hwix rfl (hof false hfh hisw)

/-! ## 6.2 THE INDUCTION over the candidate's trace -/

theorem finvReplay (G : Gexec) (hwf : gwf G) (hppo : gppoGmo G) (hlv : gloadValue G)
    (r : Geid) (a : Int) (hrr : glblIs G r lbIsR) (hra : gaccesses G r a)
    (c : Cand) (ev : Nat → Geid) (p : Nat) :
    GtracePrefix G c ev →
    gcnt r.1 c.cdTr ≤ r.2 →
    p ≤ c.cdTr.length →
    finv G r a (gcnt r.1 (c.cdTr.take p)) ((stt (candExec c) p).msWs r.1) := by
  intro hgt hcnt
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
    · rw [gcntStepEq r.1 c.cdTr p s hs hag, hag, mnextWsEq]
      have hev : ev p = (r.1, gcnt r.1 (c.cdTr.take p)) := by
        rw [gtpEvEq G c ev p s hgt hs, hag]
      apply finvStep G hwf hppo hlv r a hrr hra (gcnt r.1 (c.cdTr.take p)) s.esLb
      · have hle := gcntTakeLe r.1 c.cdTr (p + 1)
        rw [gcntStepEq r.1 c.cdTr p s hs hag] at hle
        omega
      · rw [← hev]; exact hgt.gtpLbl p s hs
      · intro hw; rw [← hev, hlog]; exact hgt.gtpWix p s hs hw
      · exact ih (by omega)
    · rw [gcntStepNe r.1 c.cdTr p s hs hag,
        mnextWsNe _ s.esAg s.esLb r.1 (fun h => hag h.symm)]
      exact ih (by omega)

/-! ## 6.3 THE FLOOR DISCHARGE -/

theorem floorOfGraphSec (G : Gexec) (hwf : gwf G) (hppo : gppoGmo G) (hlv : gloadValue G)
    (r : Geid) (a : Int) (hrr : glblIs G r lbIsR) (hra : gaccesses G r a)
    (c : Cand) (ev : Nat → Geid) (aq : Bool) (t : Nat) (v : BitVec 8) :
    GtracePrefix G c ev →
    r.2 = gcnt r.1 c.cdTr →
    greadsByte G r a t v →
    (aq = true → glblIs G r lbAq) →
    ¬ writesIn (cdLog c c.cdTr.length) a t
        (max (loadVpre ((stt (candExec c) c.cdTr.length).msWs r.1) aq)
             (coh ((stt (candExec c) c.cdTr.length).msWs r.1) a)) := by
  intro hgt hr2 hrb haq
  have hcl : maxcl (gvisUb G r) := gvisUbMaxcl G r
  have hinv := finvReplay G hwf hppo hlv r a hrr hra c ev c.cdTr.length hgt (by omega)
    (Nat.le_refl _)
  rw [take_ge (l := c.cdTr) (Nat.le_refl _), ← hr2] at hinv
  obtain ⟨_, hcoh, hrn, hrel, _, _⟩ := hinv
  apply noWritesInOfUb G hwf hlv r a t v _ _ hrb (gtpLogWrites G c ev hgt)
  apply maxclMax _ _ _ hcl _ hcoh
  unfold loadVpre
  apply maxclMax _ _ _ hcl hrn
  cases aq with
  | false => exact gvisUb0 G r
  | true => exact hrel ⟨r.2, Nat.le_refl _, hrr, haq rfl, .inl rfl⟩

/-! # 7. The floor discharge, packaged -/

theorem floorOfGraph (G : Gexec) (c : Cand) (ev : Nat → Geid) (i : Nat) (r : Geid) (a : Int)
    (t : Nat) (v : BitVec 8) (aq : Bool) :
    rvwmoMinusConsistent G →
    GtracePrefix G c ev →
    r = (i, gcnt i c.cdTr) →
    greadsByte G r a t v →
    (aq = true → glblIs G r lbAq) →
    ¬ writesIn (cdLog c c.cdTr.length) a t
      (max (loadVpre ((stt (candExec c) c.cdTr.length).msWs i) aq)
           (coh ((stt (candExec c) c.cdTr.length).msWs i) a)) := by
  rintro ⟨hwf, hppo, hlv, _⟩ hgt hr hrb haq
  have hrr : glblIs G r lbIsR := by
    obtain ⟨l, base, ts, vs, j, hl, hrd, _⟩ := hrb
    exact ⟨l, hl, lbRdIsR l _ hrd⟩
  have hra : gaccesses G r a := .inr ⟨t, v, hrb⟩
  subst hr
  exact floorOfGraphSec G hwf hppo hlv _ a hrr hra c ev aq t v hgt rfl hrb haq

/-! # 8. The two induction steps of T2-1c′ -/

/-- The event naming of a snoc: the old naming below the end, the appended event at it. -/
def evSnoc (c : Cand) (ev : Nat → Geid) (e : Geid) : Nat → Geid :=
  fun p => if p < c.cdTr.length then ev p else e

theorem evSnocLt (c : Cand) (ev : Nat → Geid) (e : Geid) (p : Nat) :
    p < c.cdTr.length → evSnoc c ev e p = ev p := by
  intro h; simp [evSnoc, h]

theorem evSnocEnd (c : Cand) (ev : Nat → Geid) (e : Geid) :
    evSnoc c ev e c.cdTr.length = e := by
  simp [evSnoc]

/-! ## 8.1 A G-trace prefix extends by one step -/

theorem gtracePrefixSnoc (G : Gexec) (c : Cand) (ev : Nat → Geid) (i : Nat) (l : Lbl) :
    gwf G →
    GtracePrefix G c ev →
    gxLbl G (i, gcnt i c.cdTr) = some l →
    (lbIsW l = true → gwix G (i, gcnt i c.cdTr) = (cdLogEnd c).length + 1) →
    GtracePrefix G (candSnoc c ⟨i, l⟩) (evSnoc c ev (i, gcnt i c.cdTr)) := by
  intro hwf hgt hl hix
  have hte : c.cdTr.take c.cdTr.length = c.cdTr := take_ge (Nat.le_refl _)
  obtain ⟨himg, hag, hpos, hlbl, hwix, hlog⟩ := hgt
  -- the three "below the end" transports, once
  have hlt : ∀ p s, (candSnoc c ⟨i, l⟩).cdTr[p]? = some s → p < c.cdTr.length →
      c.cdTr[p]? = some s ∧ evSnoc c ev (i, gcnt i c.cdTr) p = ev p ∧
      (candSnoc c ⟨i, l⟩).cdTr.take p = c.cdTr.take p ∧
      cdLog (candSnoc c ⟨i, l⟩) p = cdLog c p := by
    intro p s hs hp
    rw [candSnocTrLt c _ p hp] at hs
    exact ⟨hs, evSnocLt c ev _ p hp, take_app_le (Nat.le_of_lt hp),
      candSnocLog c _ p (Nat.le_of_lt hp)⟩
  have hend : ∀ p s, (candSnoc c ⟨i, l⟩).cdTr[p]? = some s → ¬ p < c.cdTr.length →
      p = c.cdTr.length ∧ s = ⟨i, l⟩ := by
    intro p s hs hp
    have hb := lookup_lt_Some hs
    simp only [candSnoc, List.length_append, List.length_singleton] at hb
    have hpe : p = c.cdTr.length := by omega
    subst hpe
    have he := candSnocTrEnd c ⟨i, l⟩
    unfold cdEnd at he
    rw [he] at hs
    exact ⟨rfl, (Option.some.inj hs).symm⟩
  refine ⟨himg, ?_, ?_, ?_, ?_, ?_⟩
  · intro p s hs
    by_cases hp : p < c.cdTr.length
    · obtain ⟨hs', hev, -, -⟩ := hlt p s hs hp
      rw [hev]; exact hag p s hs'
    · obtain ⟨rfl, rfl⟩ := hend p s hs hp
      rw [evSnocEnd]
  · intro p s hs
    by_cases hp : p < c.cdTr.length
    · obtain ⟨hs', hev, htk, -⟩ := hlt p s hs hp
      rw [hev, htk]; exact hpos p s hs'
    · obtain ⟨rfl, rfl⟩ := hend p s hs hp
      rw [evSnocEnd]
      show gcnt i c.cdTr = gcnt i ((c.cdTr ++ [(⟨i, l⟩ : Estep)]).take c.cdTr.length)
      rw [take_app_le (Nat.le_refl _), hte]
  · intro p s hs
    by_cases hp : p < c.cdTr.length
    · obtain ⟨hs', hev, -, -⟩ := hlt p s hs hp
      rw [hev]; exact hlbl p s hs'
    · obtain ⟨rfl, rfl⟩ := hend p s hs hp
      rw [evSnocEnd]; exact hl
  · intro p s hs hw
    by_cases hp : p < c.cdTr.length
    · obtain ⟨hs', hev, -, hlg⟩ := hlt p s hs hp
      rw [hev, hlg]; exact hwix p s hs' hw
    · obtain ⟨rfl, rfl⟩ := hend p s hs hp
      rw [evSnocEnd, candSnocLog c ⟨i, l⟩ c.cdTr.length (Nat.le_refl _)]
      exact hix hw
  · -- the log clause
    intro s hs hle
    have hlg : cdLog (candSnoc c ⟨i, l⟩) (candSnoc c ⟨i, l⟩).cdTr.length
        = cdLogEnd c ++ esMsg ⟨i, l⟩ := cdLogEndSnoc c ⟨i, l⟩
    rw [hlg] at hle ⊢
    by_cases hin : s ≤ (cdLogEnd c).length
    · obtain ⟨w, hw, heq⟩ := hlog s hs hin
      refine ⟨w, hw, ?_⟩
      have hsl : s - 1 < (cdLogEnd c).length := by omega
      rw [lookup_app_l hsl]
      exact heq
    · -- the appended message
      rw [List.length_append] at hle
      have hwl : lbIsW l = true := by
        cases hwr : lbWr l with
        | some p => exact lbWrIsW l p hwr
        | none =>
          exfalso
          simp only [esMsg, hwr, List.length_nil, Nat.add_zero] at hle
          omega
      obtain ⟨base, vs, hwr⟩ := lbIsWWr l hwl
      have hmsg : esMsg ⟨i, l⟩ = [⟨base, vs, some i, lbCls l⟩] := by simp only [esMsg, hwr]
      rw [hmsg] at hle ⊢
      simp only [List.length_singleton] at hle
      have hs' : s = (cdLogEnd c).length + 1 := by omega
      subst hs'
      have hgw : (i, gcnt i c.cdTr) ∈ gwrites G :=
        gisWGwrites G _ hwf (by rw [hl]; rfl) (by simp only [gisW, hl]; exact hwl)
      refine ⟨(i, gcnt i c.cdTr), ?_, ?_⟩
      · rw [← hix hwl]; exact gwriteAtGwix G _ hgw
      · rw [Nat.add_sub_cancel, lookup_app_r (Nat.le_refl _), Nat.sub_self]
        simp [gwmsg, hl, hwr]

/-! ## 8.2 The read step -/

theorem gtraceSnocReadConsistent (G : Gexec) (c : Cand) (ev : Nat → Geid) (i : Nat) (aq : Bool)
    (base : Int) (ts : List Nat) (vs : List (BitVec 8)) :
    rvwmoMinusConsistent G →
    srvwmoConsistent c →
    GtracePrefix G c ev →
    gxLbl G (i, gcnt i c.cdTr) = some (.LLoad aq base ts vs) →
    (∀ (j : Nat) t, ts[j]? = some t → t ≤ (cdLogEnd c).length) →
    srvwmoConsistent (candSnoc c ⟨i, .LLoad aq base ts vs⟩) ∧
    GtracePrefix G (candSnoc c ⟨i, .LLoad aq base ts vs⟩) (evSnoc c ev (i, gcnt i c.cdTr)) := by
  intro hcons hc hgt hl hsrc
  obtain ⟨hwf, hppo, hlv, hat⟩ := hcons
  have hlen : vs.length = ts.length := WeakRvwmoFloor.gshape G hwf _ _ hl
  have hrb : ∀ (j : Nat) t v, ts[j]? = some t → vs[j]? = some v →
      greadsByte G (i, gcnt i c.cdTr) (accAddr base j) t v :=
    fun j t v hj hv => ⟨_, base, ts, vs, j, hl, rfl, hj, hv, rfl⟩
  refine ⟨?_, gtracePrefixSnoc G c ev i _ hwf hgt hl (fun h => by simp [lbIsW] at h)⟩
  apply snocReadConsistent c i aq base ts vs hc
  refine ⟨hlen, ?_, ?_⟩
  · intro j t v hj hv
    have hval := (hlv _ _ _ _ (hrb j t v hj hv)).1
    cases t with
    | zero => rw [logByte0, hgt.gtpImg]; exact hval
    | succ n =>
      obtain ⟨w, hw, hwb, _⟩ := hval
      exact gtpLogByte G c ev hgt (n + 1) w (accAddr base j) v (by omega) (hsrc j (n + 1) hj)
        hw hwb
  · intro j t hj
    have hjlt : j < vs.length := by rw [hlen]; exact lookup_lt_Some hj
    obtain ⟨v, hv⟩ := someOfIsSome (lookup_lt_is_Some_2 hjlt)
    exact floorOfGraph G c ev i (i, gcnt i c.cdTr) (accAddr base j) t v aq
      ⟨hwf, hppo, hlv, hat⟩ hgt rfl (hrb j t v hj hv)
      (fun h => by subst h; exact ⟨_, hl, rfl⟩)

/-! ## 8.3 The write step -/

theorem gtraceSnocWriteConsistent (G : Gexec) (c : Cand) (ev : Nat → Geid) (i : Nat) (rl : Bool)
    (base : Int) (vs : List (BitVec 8)) (kc : WmClass) :
    gwf G →
    srvwmoConsistent c →
    GtracePrefix G c ev →
    gxLbl G (i, gcnt i c.cdTr) = some (.LStore rl base vs kc) →
    gwix G (i, gcnt i c.cdTr) = (cdLogEnd c).length + 1 →
    srvwmoConsistent (candSnoc c ⟨i, .LStore rl base vs kc⟩) ∧
    GtracePrefix G (candSnoc c ⟨i, .LStore rl base vs kc⟩) (evSnoc c ev (i, gcnt i c.cdTr)) := by
  intro hwf hc hgt hl hix
  have hne : vs ≠ [] := WeakRvwmoFloor.gshape G hwf _ _ hl
  exact ⟨snocWriteConsistent c i rl base vs kc hc hne,
    gtracePrefixSnoc G c ev i _ hwf hgt hl (fun _ => hix)⟩

/-! # 9. Non-vacuity -/

theorem gtracePrefixEmpty (G : Gexec) : GtracePrefix G ⟨G.gxImg, []⟩ (fun _ => (0, 0)) := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_⟩
  · intro p s hs; simp at hs
  · intro p s hs; simp at hs
  · intro p s hs; simp at hs
  · intro p s hs; simp at hs
  · intro s hs hle
    simp [cdLog, trMsgs] at hle
    omega

theorem gtraceSnocReadImage (G : Gexec) (i : Nat) (aq : Bool) (base : Int) (ts : List Nat)
    (vs : List (BitVec 8)) :
    rvwmoMinusConsistent G →
    gxLbl G (i, 0) = some (.LLoad aq base ts vs) →
    (∀ (j : Nat) t, ts[j]? = some t → t = 0) →
    srvwmoConsistent (candSnoc ⟨G.gxImg, []⟩ ⟨i, .LLoad aq base ts vs⟩) := by
  intro hcons hl hz
  exact (gtraceSnocReadConsistent G ⟨G.gxImg, []⟩ (fun _ => (0, 0)) i aq base ts vs hcons
    (srvwmoOfWf _ (candReachable _ (fun k s hs => by simp at hs)).1)
    (gtracePrefixEmpty G) hl (fun j t hj => by rw [hz j t hj]; omega)).1

end Weak
