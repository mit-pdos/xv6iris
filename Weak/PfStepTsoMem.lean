/-
Weak: **W2a — the MEMORY half of W2 proper** (allocproc plan `notes/weak-allocproc-plan.md`
§C "W2", §B(10) `R`; the spike `notes/W2-spike.md` §R and its (↓) table).

Lean-only (no Rocq source).  The relation `rmem` between a promise-free WeakMem configuration
(with its step list) and a TsoMem machine state is the MEMORY part of W2's `R`: the author log
(`R-log`), the boot image (`R-img`), the per-byte histories (`R-hist`, the log projection
`TsoOfPf.histOf`) and the reservations (`R-resv`: `none` unless the hart is mid-pair).  Every
TsoMem post-state is stated by FIELD EQUATIONS on `.mem`, `.log` and `.resv` only; the read side
(`R-view`, `tsoShadow`, the coherence floors) is W2b's and W5b′'s, not this file's.

Main results (all `Weak.PfStepTsoMem.*`):

* the history algebra: `histOfSnoc` (one appended message), `histOfWriteBytes` (`R-hist` is
  preserved by a TsoMem store and the matching pf message), `histOfFind` (TsoMem's reading
  `find? (HEnt.visible i tvn)` of the projected history is the single-copy-atomic source, entry
  form), `histOfTop` (the top of a history is the `latest` byte), `scaByteMono`;
* boot: `rmemBoot`;
* the exclusive-pair bookkeeping: `midPairOther`, `resvOthersNone`;
* the memory rows: `pfLoadRowMem` (hart plain load: TsoMem `readBytes` at any view `tvn ≤ tvn₀`
  under which the bytes stay visible), `pfStoreRowMem` (hart `LStore`/`LExStore`, ONE lemma, the
  exclusivity a parameter), `pfExLoadRowMem` (exclusive read: top bytes + reservation),
  `pfDReadRowMem` (disk `DRead` under `candDiskLat`'s `latest`), `pfDWriteRowMem` (a disk store),
  `pfFetchRowMemM1` (pristine fetch, any view), `pfFetchRowMemCut` (a fetch at a cut `q`, a memory
  helper only), `pfFrameRowMem` (every other label leaves the memory fields alone).
* W-DISK (plan §C "W-DISK"): the disk's writes are `DWriteDev`s, whose step moves the fabric too
  -- `pfDWriteDevRowMem` (the STORE: TsoMem's `storeDma` followed by the device's own `setDev`,
  `dmaWrite`'s moving guard) and `pfDSkipRowMem` (the SKIP / ABORT, label `LSilent`: `setDev`
  only); both are corollaries of `pfDWriteRowMem` / `pfFrameRowMem` (a device move touches no
  memory field).

Deviations from the brief's statement shapes (each an extra ADDRESS/LOG hypothesis without which
the statement is false):
* `histOfWriteBytes` takes `σ.log.length = log.length` (the store's timestamp `σ.log.length + 1`
  must be the appended message's position + 1; `rmem`'s `R-log` supplies it).
* `pfDReadRowMem` takes the no-wrap bound `pa.toNat + n ≤ 2 ^ 64` (the pf bytes are at the Int
  addresses `paZ pa + j`, TsoMem's at `pa + j`; `noWrapOfRam` derives it from `ramBytes`).
* The rows' "bytes match `w`" is `data.length = n ∧ ∀ j < n, data[j]? = some (nthByte w j)` for
  stores and `∀ j < n, (tvs[j]?).map Prod.snd = some (nthByte w j)` for reads.
-/
import Weak.TsoOfPf

namespace Weak.PfStepTsoMem

open MachCSL MachCSL.Stdpp

/-! ## 0. Definitions -/

/-- Agent `i` is MID-PAIR at the end of the step list `st`: an exclusive read of `i` at `v`
followed only by `i`'s administrative (`lbAdmin false`) steps. -/
def midPair (st : List (Nat × Wlabel)) (i : Nat) : Prop :=
  ∃ (v : Nat) (aq : Bool) (base : Int) (tvs : List (Nat × BitVec 8)) (asrc : List Dsrc),
    st[v]? = some (i, .LExLoad aq base tvs asrc) ∧
    ∀ w, v < w → w < st.length → ∃ l, st[w]? = some (i, l) ∧ lbAdmin false l

/-- The author `TsoOfPf.histOf` records for timestamp `t` (0 for the image). -/
def logAuthor (log : List Wmsg) : Nat → Nat
  | 0 => 0
  | p + 1 => (log[p]?.bind Wmsg.wmTid).getD 0

/-- `R-hist`: every RAM byte's history is the log projection, no history off RAM. -/
def rhist (m : FlatMem) (img : Image) (log : List Wmsg) : Prop :=
  (∀ pa, inRam pa 1 → m[pa]? = some (TsoOfPf.histOf img log (paZ pa))) ∧
  (∀ pa, ¬ inRam pa 1 → m[pa]? = none)

/-- **The memory half of W2's `R`**: `R-log`, `R-img`, `R-hist`, `R-resv`. -/
def rmem {P D : Type} (c : Wpcfg P D) (st : List (Nat × Wlabel)) (σ : MState) : Prop :=
  (c.pcLog.map Wmsg.wmTid = σ.log.map some ∧ ∀ a ∈ σ.log, a ≤ NCPU) ∧
  c.pcImg = imgZ bootImage ∧
  rhist σ.mem c.pcImg c.pcLog ∧
  (∀ cpu, σ.resv cpu = none ∨ midPair st (hartAgent cpu))

/-- A store label, the exclusivity a parameter (`true`: `LExStore`, `false`: `LStore`). -/
def stLbl (excl rl : Bool) (base : Int) (data : List (BitVec 8)) (asrc vsrc : List Dsrc) :
    Wlabel :=
  cond excl (.LExStore rl base data asrc vsrc) (.LStore rl base data asrc vsrc)

/-- The labels that touch no memory field: all but the stores and exclusive/RMW accesses. -/
def frameLbl : Wlabel → Prop
  | .LStore .. | .LExStore .. | .LExLoad .. | .LRmw .. => False
  | _ => True

/-! ## 1. Generic helpers -/

theorem filterMapCongr {α β : Type} (f g : α → Option β) :
    ∀ l : List α, (∀ x ∈ l, f x = g x) → l.filterMap f = l.filterMap g
  | [], _ => rfl
  | x :: l, h => by
    simp only [List.filterMap_cons]
    rw [h x (by simp), filterMapCongr f g l (fun y hy => h y (by simp [hy]))]

/-- Distinct harts are distinct agents. -/
theorem hartAgentNe (c c' : CPU) (h : c ≠ c') : hartAgent c ≠ hartAgent c' := by
  intro he; exact h (Fin.ext he)

/-! ## 2. The address seam (no wrap-around) -/

theorem toNatAdd (pa : PAddr) (j : Nat) (h : pa.toNat + j < 2 ^ 64) :
    (pa + BitVec.ofNat 64 j).toNat = pa.toNat + j := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := j) (by omega),
    Nat.mod_eq_of_lt h]

/-- A RAM footprint does not wrap: every byte sits below `ramEnd`. -/
theorem ramLt (pa : PAddr) (n : Nat) (h : ramBytes pa n) : ∀ j, j < n → pa.toNat + j < ramEnd := by
  intro j
  induction j with
  | zero =>
    intro hj
    have := h 0 hj
    simp only [inRam, BitVec.add_zero] at this
    omega
  | succ j ih =>
    intro hj
    have h1 := ih (by omega)
    have h2 := h (j + 1) hj
    simp only [inRam] at h2
    rw [toNatAdd pa (j + 1) (by simp only [ramEnd] at h1; omega)] at h2
    omega

/-- A RAM footprint satisfies the no-wrap bound. -/
theorem noWrapOfRam (pa : PAddr) (n : Nat) (h : ramBytes pa n) : pa.toNat + n ≤ 2 ^ 64 := by
  cases n with
  | zero => have := pa.isLt; omega
  | succ n => have := ramLt pa (n + 1) h n (by omega); simp only [ramEnd] at this; omega

theorem paZAddJ (pa : PAddr) (n j : Nat) (hnw : pa.toNat + n ≤ 2 ^ 64) (hj : j < n) :
    paZ (pa + BitVec.ofNat 64 j) = accAddr (paZ pa) j := by
  simp only [paZ, accAddr]
  rw [toNatAdd pa j (by omega)]
  omega

theorem fpInj (pa : PAddr) (n j j' : Nat) (hnw : pa.toNat + n ≤ 2 ^ 64) (hj : j < n)
    (hj' : j' < n) (h : pa + BitVec.ofNat 64 j = pa + BitVec.ofNat 64 j') : j = j' := by
  have h1 := congrArg BitVec.toNat h
  rw [toNatAdd pa j (by omega), toNatAdd pa j' (by omega)] at h1
  omega

/-- An address whose Int image lies in the footprint's range is a footprint byte. -/
theorem fpOf (pa a : PAddr) (n : Nat) (h1 : paZ pa ≤ paZ a) (h2 : paZ a < paZ pa + n) :
    ∃ j, j < n ∧ a = pa + BitVec.ofNat 64 (a.toNat - pa.toNat) := by
  simp only [paZ] at h1 h2
  refine ⟨a.toNat - pa.toNat, by omega, ?_⟩
  apply BitVec.eq_of_toNat_eq
  have := a.isLt
  rw [toNatAdd pa _ (by omega)]
  omega

/-- The store message's byte at a footprint byte. -/
theorem msgByteIn (pa : PAddr) (n j : Nat) (data : List (BitVec 8)) (tid : Option Nat)
    (k : WmClass) (hnw : pa.toNat + n ≤ 2 ^ 64) (hj : j < n) :
    msgByte ⟨paZ pa, data, tid, k⟩ (paZ (pa + BitVec.ofNat 64 j)) = data[j]? := by
  rw [paZAddJ pa n j hnw hj]
  simp only [msgByte, accAddr]
  rw [if_pos (by omega), show (paZ pa + (j : Int) - paZ pa).toNat = j by omega]

/-- The store message writes no byte off its footprint. -/
theorem msgByteOut (pa a : PAddr) (n : Nat) (data : List (BitVec 8)) (tid : Option Nat)
    (k : WmClass) (hd : data.length = n)
    (ha : ∀ j, j < n → a ≠ pa + BitVec.ofNat 64 j) :
    msgByte ⟨paZ pa, data, tid, k⟩ (paZ a) = none := by
  unfold msgByte
  split
  · rename_i hle
    simp only at hle ⊢
    apply List.getElem?_eq_none
    rw [hd]
    apply Nat.le_of_not_lt
    intro hlt
    obtain ⟨j, hj, he⟩ := fpOf pa a n hle (by omega)
    exact ha _ (by simp only [paZ] at hle hlt ⊢; omega) he
  · rfl

/-! ## 3. Footprint pushes -/

theorem foldPushOut (pa a : PAddr) (f : Nat → HEnt) :
    ∀ (l : List Nat), (∀ j ∈ l, a ≠ pa + BitVec.ofNat 64 j) → ∀ m : FlatMem,
      (l.foldl (fun (m : FlatMem) j => m.push (pa + BitVec.ofNat 64 j) (f j)) m)[a]? = m[a]?
  | [], _, _ => rfl
  | j :: l, hl, m => by
    simp only [List.foldl_cons]
    rw [foldPushOut pa a f l (fun j' hj' => hl j' (List.mem_cons_of_mem _ hj')),
      FlatMem.push_get?_ne _ _ _ _ (hl j List.mem_cons_self)]

theorem foldPushIn (m : FlatMem) (pa : PAddr) (f : Nat → HEnt) (n : Nat)
    (hnw : pa.toNat + n ≤ 2 ^ 64) : ∀ k, k ≤ n → ∀ j, j < k →
      ((List.range k).foldl (fun (m : FlatMem) j => m.push (pa + BitVec.ofNat 64 j) (f j))
        m)[pa + BitVec.ofNat 64 j]? = some (f j :: m.getD (pa + BitVec.ofNat 64 j) []) := by
  intro k
  induction k with
  | zero => intro _ j hj; omega
  | succ k ih =>
    intro hk j hj
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    by_cases hjk : j = k
    · subst hjk
      rw [FlatMem.push_get?_eq, Std.ExtTreeMap.getD_eq_getD_getElem?,
        Std.ExtTreeMap.getD_eq_getD_getElem?,
        foldPushOut pa _ f _ (fun j' hj' he =>
          by have := fpInj pa n j j' hnw (by omega) (by simp at hj'; omega) he
             simp at hj'; omega)]
    · rw [FlatMem.push_get?_ne _ _ _ _ (fun he =>
        hjk (fpInj pa n j k hnw (by omega) (by omega) he))]
      exact ih (by omega) j (by omega)

/-! ## 4. The history algebra -/

theorem histOfNil (img : Image) (a : Int) :
    TsoOfPf.histOf img [] a = ((img a).map (fun v => (⟨0, 0, v⟩ : HEnt))).toList := by
  simp [TsoOfPf.histOf]

/-- **(1)** One appended message. -/
theorem histOfSnoc (img : Image) (log : List Wmsg) (m : Wmsg) (a : Int) :
    TsoOfPf.histOf img (log ++ [m]) a =
      match msgByte m a with
      | some v => ⟨log.length + 1, m.wmTid.getD 0, v⟩ :: TsoOfPf.histOf img log a
      | none => TsoOfPf.histOf img log a := by
  unfold TsoOfPf.histOf
  rw [List.length_append, List.length_singleton, List.range_succ, List.filterMap_append]
  rw [filterMapCongr _ (fun i => (log[i]?.bind (fun m => msgByte m a)).map
      (fun v => (⟨i + 1, (log[i]?.bind Wmsg.wmTid).getD 0, v⟩ : HEnt))) _
    (fun i hi => by rw [List.getElem?_append_left (List.mem_range.1 hi)])]
  simp only [List.filterMap_cons, List.filterMap_nil, List.getElem?_concat_length,
    Option.bind_some]
  cases msgByte m a <;> simp

/-- A log none of whose messages writes `a` projects to the image byte alone. -/
theorem histOfPristine (img : Image) (a : Int) (log : List Wmsg)
    (h : ∀ m ∈ log, msgByte m a = none) :
    TsoOfPf.histOf img log a = ((img a).map (fun v => (⟨0, 0, v⟩ : HEnt))).toList := by
  induction log using Weak.snocInd with
  | h0 => exact histOfNil img a
  | hs l m ih =>
    rw [histOfSnoc, h m (by simp)]
    exact ih (fun m' hm' => h m' (by simp [hm']))

theorem scaVisApp (log l : List Wmsg) (i tvn t : Nat) (ht : t ≤ log.length) :
    scaVis (log ++ l) i tvn t ↔ scaVis log i tvn t := by
  unfold scaVis
  constructor
  · rintro (h | ⟨h0, m, hm, hid⟩)
    · exact Or.inl h
    · rw [List.getElem?_append_left (by omega)] at hm; exact Or.inr ⟨h0, m, hm, hid⟩
  · rintro (h | ⟨h0, m, hm, hid⟩)
    · exact Or.inl h
    · exact Or.inr ⟨h0, m, by rw [List.getElem?_append_left (by omega)]; exact hm, hid⟩

theorem logAuthorApp (log l : List Wmsg) (t : Nat) (ht : t ≤ log.length) :
    logAuthor (log ++ l) t = logAuthor log t := by
  cases t with
  | zero => rfl
  | succ p => simp only [logAuthor]; rw [List.getElem?_append_left (by omega)]

/-- **(3)** TsoMem's reading of the projected history at view `tvn` by agent `i` is the
single-copy-atomic source `t` (the ENTRY: timestamp, author, byte). -/
theorem histOfFind (img : Image) (log : List Wmsg) (i tvn : Nat) (a : Int) (t : Nat)
    (v : BitVec 8) (hsome : ∀ m ∈ log, m.wmTid.isSome) (hv : logByte img log t a = some v)
    (hs : scaByte img log i tvn a t) :
    (TsoOfPf.histOf img log a).find? (HEnt.visible i tvn) = some ⟨t, logAuthor log t, v⟩ := by
  induction log using Weak.snocInd generalizing t v with
  | h0 =>
    cases t with
    | zero =>
      rw [histOfNil]; rw [logByte0] at hv; rw [hv]
      simp [HEnt.visible, logAuthor]
    | succ p => simp [logByteS] at hv
  | hs log m ih =>
    have hsome' : ∀ m ∈ log, m.wmTid.isSome := fun m' hm' => hsome m' (by simp [hm'])
    have htN : t ≤ log.length + 1 := by
      have := logByteBounded img (log ++ [m]) t a (by rw [hv]; rfl)
      simpa using this
    obtain ⟨hsS, hsV, hsL⟩ := hs
    -- transport to `log` when `t ≤ |log|`
    have down : t ≤ log.length → (TsoOfPf.histOf img log a).find? (HEnt.visible i tvn) =
        some ⟨t, logAuthor (log ++ [m]) t, v⟩ := by
      intro htl
      rw [logAuthorApp log [m] t htl]
      refine ih t v hsome' (by rw [← logByteApp img log [m] t a htl]; exact hv) ⟨?_, ?_, ?_⟩
      · rw [← logByteApp img log [m] t a htl]; exact hsS
      · exact (scaVisApp log [m] i tvn t htl).1 hsV
      · intro t' htt' hs' hvis
        have ht'l := logByteBounded img log t' a hs'
        exact hsL t' htt' (by rw [logByteApp img log [m] t' a ht'l]; exact hs')
          ((scaVisApp log [m] i tvn t' ht'l).2 hvis)
    have hN : logByte img (log ++ [m]) (log.length + 1) a = msgByte m a := by
      simp [logByteS]
    rw [histOfSnoc]
    cases hm : msgByte m a with
    | none =>
      simp only
      apply down
      rcases Nat.lt_or_ge t (log.length + 1) with h | h
      · omega
      · have : t = log.length + 1 := by omega
        subst this; rw [hN, hm] at hv; cases hv
    | some u =>
      simp only
      obtain ⟨x, hx⟩ : ∃ x, m.wmTid = some x := Option.isSome_iff_exists.1 (hsome m (by simp))
      rcases Nat.lt_or_ge t (log.length + 1) with h | h
      · -- the new entry is a later write: invisible
        have hinv : ¬ scaVis (log ++ [m]) i tvn (log.length + 1) :=
          hsL _ h (by rw [hN, hm]; rfl)
        have hvis : HEnt.visible i tvn ⟨log.length + 1, m.wmTid.getD 0, u⟩ = false := by
          simp only [HEnt.visible, hx, Option.getD_some, Bool.or_eq_false_iff,
            decide_eq_false_iff_not]
          refine ⟨fun hle => hinv (Or.inl hle), fun hxi => hinv (Or.inr ⟨by omega, m, by simp, ?_⟩)⟩
          rw [hx, hxi]
        rw [List.find?_cons, hvis]
        exact down (by omega)
      · have : t = log.length + 1 := by omega
        subst this
        rw [hN, hm] at hv; cases hv
        have hvis : HEnt.visible i tvn ⟨log.length + 1, m.wmTid.getD 0, v⟩ = true := by
          rcases hsV with hle | ⟨_, m', hm', hid⟩
          · exact HEnt.visible_of_le _ _ _ hle
          · simp at hm'; subst hm'
            exact HEnt.visible_of_own _ _ _ (by simp [hid])
        rw [List.find?_cons, hvis]
        simp [logAuthor]

theorem writesInSnocNone (log : List Wmsg) (m : Wmsg) (a : Int) (lo : Nat)
    (hm : msgByte m a = none) :
    writesIn (log ++ [m]) a lo (log.length + 1) ↔ writesIn log a lo log.length := by
  constructor
  · rintro ⟨t, h1, h2, m', hm', hs⟩
    rcases Nat.lt_or_ge t (log.length + 1) with h | h
    · rw [List.getElem?_append_left (by omega)] at hm'
      exact ⟨t, h1, by omega, m', hm', hs⟩
    · have : t - 1 = log.length := by omega
      rw [this, List.getElem?_concat_length] at hm'
      cases hm'; rw [hm] at hs; cases hs
  · intro h
    exact writesInMonoHi _ _ _ _ _ (by omega) (writesInApp log [m] a lo _ h)

/-- **(4)** The top of the projected history is the `latest` byte. -/
theorem histOfTop (img : Image) (log : List Wmsg) (a : Int) (v : BitVec 8) :
    Hist.top (TsoOfPf.histOf img log a) = some v ↔
      ∃ t, latest img log a t ∧ logByte img log t a = some v := by
  induction log using Weak.snocInd with
  | h0 =>
    rw [histOfNil]
    constructor
    · intro h
      refine ⟨0, ⟨?_, fun ⟨t, h1, h2, _⟩ => by simp at h2; omega⟩, ?_⟩
      · cases ha : img a with
        | none => rw [ha] at h; simp [Hist.top] at h
        | some u => simp [logByte0, ha]
      · cases ha : img a with
        | none => rw [ha] at h; simp [Hist.top] at h
        | some u => rw [ha] at h; simp [Hist.top] at h; simp [logByte0, ha, h]
    · rintro ⟨t, -, hv⟩
      cases t with
      | zero => rw [logByte0] at hv; simp [Hist.top, hv]
      | succ p => simp [logByteS] at hv
  | hs log m ih =>
    have hN : logByte img (log ++ [m]) (log.length + 1) a = msgByte m a := by
      simp [logByteS]
    rw [histOfSnoc]
    cases hm : msgByte m a with
    | some u =>
      simp only [Hist.top, List.head?_cons, Option.map_some, Option.some.injEq]
      constructor
      · rintro rfl
        refine ⟨log.length + 1, ⟨by rw [hN, hm]; rfl, fun ⟨t, h1, h2, _⟩ => by simp at h2; omega⟩,
          by rw [hN, hm]⟩
      · rintro ⟨t, ⟨hs, hnw⟩, hv⟩
        have htN := logByteBounded img (log ++ [m]) t a hs
        simp only [List.length_append, List.length_singleton] at htN hnw
        rcases Nat.lt_or_ge t (log.length + 1) with h | h
        · exact absurd ((writesInLogByte img _ a t _).2 ⟨log.length + 1, h, by simp,
            by rw [hN, hm]; rfl⟩) hnw
        · have : t = log.length + 1 := by omega
          subst this; rw [hN, hm] at hv; exact Option.some.inj hv
    | none =>
      simp only
      rw [ih]
      constructor
      · rintro ⟨t, ⟨hs, hnw⟩, hv⟩
        have htl := logByteBounded img log t a hs
        refine ⟨t, ⟨by rw [logByteApp img log [m] t a htl]; exact hs, ?_⟩,
          by rw [logByteApp img log [m] t a htl]; exact hv⟩
        simp only [List.length_append, List.length_singleton]
        rw [writesInSnocNone log m a t hm]; exact hnw
      · rintro ⟨t, ⟨hs, hnw⟩, hv⟩
        have htN := logByteBounded img (log ++ [m]) t a hs
        simp only [List.length_append, List.length_singleton] at htN hnw
        have htl : t ≤ log.length := by
          rcases Nat.lt_or_ge t (log.length + 1) with h | h
          · omega
          · have : t = log.length + 1 := by omega
            subst this; rw [hN, hm] at hs; cases hs
        rw [logByteApp img log [m] t a htl] at hs hv
        exact ⟨t, ⟨hs, fun hw => hnw ((writesInSnocNone log m a t hm).2 hw)⟩, hv⟩

/-- **(5)** A single-copy-atomic source stays one at a smaller view where it is visible. -/
theorem scaByteMono (img : Image) (log : List Wmsg) (i tvn tvn₀ : Nat) (a : Int) (t : Nat)
    (hs : scaByte img log i tvn₀ a t) (hle : tvn ≤ tvn₀) (hvis : scaVis log i tvn t) :
    scaByte img log i tvn a t := by
  obtain ⟨h1, -, h3⟩ := hs
  refine ⟨h1, hvis, fun t' ht hs' hv' => h3 t' ht hs' ?_⟩
  rcases hv' with h | h
  · exact Or.inl (by omega)
  · exact Or.inr h

/-- **(2)** `R-hist` survives a TsoMem store of `w` and the matching pf message. -/
theorem histOfWriteBytes (σ : MState) (img : Image) (log : List Wmsg) (pa : PAddr) (n : Nat)
    (w : BitVec (8 * n)) (data : List (BitVec 8)) (h : Agent) (k : WmClass)
    (hH : rhist σ.mem img log) (hlen : σ.log.length = log.length) (hram : ramBytes pa n)
    (hd : data.length = n) (hb : ∀ j, j < n → data[j]? = some (nthByte w j)) :
    rhist (σ.mem.writeBytes pa n w (σ.log.length + 1) h) img
      (log ++ [⟨paZ pa, data, some h, k⟩]) := by
  have hnw := noWrapOfRam pa n hram
  refine ⟨fun a ha => ?_, fun a ha => ?_⟩
  · by_cases hfp : ∃ j, j < n ∧ a = pa + BitVec.ofNat 64 j
    · obtain ⟨j, hj, rfl⟩ := hfp
      unfold FlatMem.writeBytes
      rw [foldPushIn σ.mem pa (fun j => ⟨σ.log.length + 1, h, nthByte w j⟩) n hnw n
        (Nat.le_refl _) j hj, Std.ExtTreeMap.getD_eq_getD_getElem?, hH.1 _ ha, histOfSnoc,
        msgByteIn pa n j data (some h) k hnw hj, hb j hj]
      simp [hlen]
    · have hne : ∀ j, j < n → a ≠ pa + BitVec.ofNat 64 j := fun j hj he => hfp ⟨j, hj, he⟩
      rw [FlatMem.writeBytes_get?_notin _ _ _ _ _ _ hne, hH.1 _ ha, histOfSnoc,
        msgByteOut pa a n data (some h) k hd hne]
  · rw [FlatMem.writeBytes_get?_notin _ _ _ _ _ _
      (fun j hj he => ha (by rw [he]; exact hram j hj)), hH.2 _ ha]

/-! ## 5. Boot and the exclusive-pair bookkeeping -/

/-- **(6)** The booted machine is related to the initial configuration. -/
theorem rmemBoot {P D : Type} (d0 : D) (ps : List P) (σ : MState) (h : bootFacts σ) :
    rmem (wpInit (imgZ bootImage) d0 ps) [] σ := by
  obtain ⟨hmem, hlog, hcpu, -, -⟩ := h
  refine ⟨⟨by simp [wpInit, hlog], by simp [hlog]⟩, rfl, ⟨fun pa hpa => ?_, fun pa hpa => ?_⟩,
    fun cpu => Or.inl (hcpu cpu).2.2.2⟩
  · rw [hmem, imgFlat_get?, if_pos hpa]
    simp only [wpInit]
    rw [histOfNil, imgZLookup, bootImage_get?, if_pos hpa]
    simp
  · rw [hmem, imgFlat_get?, if_neg hpa]

/-- **(7)** Whatever step follows a mid-pair prefix is the pair's agent's, and administrative or
the pair's write. -/
theorem midPairOther (st rest : List (Nat × Wlabel)) (j i : Nat) (l : Wlabel)
    (hadj : pairAdjacent (st ++ (j, l) :: rest)) (hm : midPair st i) :
    j = i ∧ (lbAdmin false l ∨ ∃ rl b d asr vs, l = .LExStore rl b d asr vs) := by
  obtain ⟨v, aq, base, tvs, asrc, hv, hbt⟩ := hm
  have hvl : v < st.length := lookup_lt_Some hv
  obtain ⟨u, hvu, hbt2, rl, data, a2, v2, hu, -, -⟩ :=
    hadj.1 v i aq base tvs asrc (by rw [List.getElem?_append_left hvl]; exact hv)
  have hpos : (st ++ (j, l) :: rest)[st.length]? = some (j, l) := by simp
  rcases Nat.lt_trichotomy u st.length with hlt | heq | hgt
  · obtain ⟨l', hl', had⟩ := hbt u hvu hlt
    rw [List.getElem?_append_left hlt] at hu
    rw [hu] at hl'
    simp only [Option.some.injEq, Prod.mk.injEq, true_and] at hl'
    subst hl'
    simp [lbAdmin] at had
  · subst heq
    rw [hpos] at hu
    simp only [Option.some.injEq, Prod.mk.injEq] at hu
    obtain ⟨rfl, rfl⟩ := hu
    exact ⟨rfl, Or.inr ⟨_, _, _, _, _, rfl⟩⟩
  · obtain ⟨l', hl', had⟩ := hbt2 st.length hvl hgt
    rw [hpos] at hl'
    simp only [Option.some.injEq, Prod.mk.injEq] at hl'
    obtain ⟨rfl, rfl⟩ := hl'
    exact ⟨rfl, Or.inl had⟩

/-- **(8)** Under `rmem`, a hart other than the next step's agent holds no reservation. -/
theorem resvOthersNone {P D : Type} (c : Wpcfg P D) (st rest : List (Nat × Wlabel))
    (σ : MState) (j : Nat) (l : Wlabel) (hR : rmem c st σ)
    (hadj : pairAdjacent (st ++ (j, l) :: rest)) :
    ∀ cpu, hartAgent cpu ≠ j → σ.resv cpu = none := by
  intro cpu hne
  rcases hR.2.2.2 cpu with h | h
  · exact h
  · exact absurd (midPairOther st rest j _ l hadj h).1.symm hne

/-- A mid-pair prefix stays mid-pair past an administrative step of the pair's agent. -/
theorem midPairSnoc (st : List (Nat × Wlabel)) (i j : Nat) (l : Wlabel) (hm : midPair st i)
    (hj : j = i) (hl : lbAdmin false l) : midPair (st ++ [(j, l)]) i := by
  obtain ⟨v, aq, base, tvs, asrc, hv, hbt⟩ := hm
  have hvl : v < st.length := lookup_lt_Some hv
  refine ⟨v, aq, base, tvs, asrc, by rw [List.getElem?_append_left hvl]; exact hv,
    fun w h1 h2 => ?_⟩
  simp only [List.length_append, List.length_singleton] at h2
  rcases Nat.lt_or_ge w st.length with h | h
  · obtain ⟨l', hl', had⟩ := hbt w h1 h
    exact ⟨l', by rw [List.getElem?_append_left h]; exact hl', had⟩
  · have : w = st.length := by omega
    subst this hj
    exact ⟨l, by simp, hl⟩

/-- A step that appends a message at a RAM footprint keeps `rmem` once no hart reserves. -/
theorem rmemAppend {P D : Type} (c c' : Wpcfg P D) (st st' : List (Nat × Wlabel))
    (σ σ' : MState) (pa : PAddr) (n : Nat) (w : BitVec (8 * n)) (data : List (BitVec 8))
    (h : Agent) (k : WmClass) (hR : rmem c st σ) (himg : c'.pcImg = c.pcImg)
    (hlog : c'.pcLog = c.pcLog ++ [⟨paZ pa, data, some h, k⟩]) (hh : h ≤ NCPU)
    (hram : ramBytes pa n) (hd : data.length = n) (hb : ∀ j, j < n → data[j]? = some (nthByte w j))
    (hmem : σ'.mem = σ.mem.writeBytes pa n w (σ.top + 1) h) (hlg : σ'.log = σ.log ++ [h])
    (hres : ∀ cpu, σ'.resv cpu = none) : rmem c' st' σ' := by
  obtain ⟨⟨hl1, hl2⟩, hi, hH, -⟩ := hR
  have hlen : σ.log.length = c.pcLog.length := by
    have := congrArg List.length hl1; simpa using this.symm
  refine ⟨⟨?_, ?_⟩, by rw [himg]; exact hi, ?_, fun cpu => Or.inl (hres cpu)⟩
  · rw [hlog, hlg]; simp [hl1]
  · rw [hlg]; intro a ha
    simp only [List.mem_append, List.mem_singleton] at ha
    rcases ha with ha | rfl
    · exact hl2 a ha
    · exact hh
  · rw [hmem, himg, hlog]
    exact histOfWriteBytes σ c.pcImg c.pcLog pa n w data h k hH hlen hram hd hb

theorem allSome {P D : Type} (c : Wpcfg P D) (σ : MState)
    (hl : c.pcLog.map Wmsg.wmTid = σ.log.map some) :
    ∀ m ∈ c.pcLog, ∃ a, m.wmTid = some a ∧ a ∈ σ.log := by
  intro m hm
  have : m.wmTid ∈ σ.log.map some := by rw [← hl]; exact List.mem_map_of_mem hm
  obtain ⟨a, ha, he⟩ := List.mem_map.1 this
  exact ⟨a, he.symm, ha⟩

theorem allIsSome {P D : Type} (c : Wpcfg P D) (σ : MState)
    (hl : c.pcLog.map Wmsg.wmTid = σ.log.map some) : ∀ m ∈ c.pcLog, m.wmTid.isSome := by
  intro m hm
  obtain ⟨a, ha, -⟩ := allSome c σ hl m hm
  simp [ha]

/-! ## 6. The memory rows -/

/-- Byte `j` of a read whose answers match `w`. -/
theorem tvsAt (tvs : List (Nat × BitVec 8)) (n : Nat) (w : BitVec (8 * n))
    (hw : ∀ j, j < n → (tvs[j]?).map Prod.snd = some (nthByte w j)) (j : Nat) (hj : j < n) :
    ∃ t, tvs[j]? = some (t, nthByte w j) := by
  have := hw j hj
  cases htj : tvs[j]? with
  | none => rw [htj] at this; cases this
  | some p =>
    rw [htj] at this
    obtain ⟨t, v⟩ := p
    simp only [Option.map_some, Option.some.injEq] at this
    exact ⟨t, by rw [this]⟩

/-- **(9)** Hart plain load: TsoMem reads the pf bytes at any view `tvn ≤ tvn₀` at which every
source stays visible. -/
theorem pfLoadRowMem {P D : Type} (c : Wpcfg P D) (st : List (Nat × Wlabel)) (σ : MState)
    (cpu : CPU) (i : Nat) (pa : PAddr) (base : Int) (n : Nat) (tvs : List (Nat × BitVec 8))
    (tvn tvn₀ : Nat) (w : BitVec (8 * n)) (hR : rmem c st σ) (hi : i = hartAgent cpu)
    (hb : base = paZ pa) (hram : ramBytes pa n) (_hlen : tvs.length = n)
    (htvs : ∀ j t v, tvs[j]? = some (t, v) →
      logByte c.pcImg c.pcLog t (accAddr base j) = some v ∧
      scaByte c.pcImg c.pcLog i tvn₀ (accAddr base j) t ∧ scaVis c.pcLog i tvn t)
    (hle : tvn ≤ tvn₀) (hw : ∀ j, j < n → (tvs[j]?).map Prod.snd = some (nthByte w j)) :
    σ.mem.readBytes (hartAgent cpu) tvn pa n w := by
  subst hi hb
  intro j hj
  obtain ⟨t, htj⟩ := tvsAt tvs n w hw j hj
  obtain ⟨hlb, hsca, hvis⟩ := htvs j t _ htj
  unfold FlatMem.read
  rw [hR.2.2.1.1 _ (hram j hj), paZAddJ pa n j (noWrapOfRam pa n hram) hj]
  simp only [Option.bind_some, Hist.read]
  rw [histOfFind _ _ _ _ _ _ _ (allIsSome c σ hR.1.1) hlb
    (scaByteMono _ _ _ _ _ _ _ hsca hle hvis)]
  rfl

/-- A store step's configuration effect, the exclusivity a parameter. -/
theorem stStep {P D : Type} (pstep : P → D → Wlabel → P → D → Prop)
    (pcls : P → Wlabel → Wstate → WmClass) (i : Nat) (excl rl : Bool) (base : Int)
    (data : List (BitVec 8)) (asrc vsrc : List Dsrc) (c c' : Wpcfg P D)
    (h : wpPfStep pstep pcls i (stLbl excl rl base data asrc vsrc) c c') :
    c'.pcImg = c.pcImg ∧ ∃ k, c'.pcLog = c.pcLog ++ [⟨base, data, some i, k⟩] := by
  cases excl <;> simp only [stLbl, cond] at h <;> cases h <;> exact ⟨rfl, _, rfl⟩

/-- **(10)** Hart store (`LStore` and `LExStore`, ONE lemma): no other hart reserves the
footprint, and the TsoMem store (bytes appended at `top + 1` by the hart, author logged, own
reservation cleared) is related. -/
theorem pfStoreRowMem {P D : Type} (pstep : P → D → Wlabel → P → D → Prop)
    (pcls : P → Wlabel → Wstate → WmClass) (c c' : Wpcfg P D) (st rest : List (Nat × Wlabel))
    (σ : MState) (cpu : CPU) (i : Nat) (excl rl : Bool) (base : Int) (data : List (BitVec 8))
    (asrc vsrc : List Dsrc) (pa : PAddr) (n : Nat) (w : BitVec (8 * n)) (hR : rmem c st σ)
    (hstep : wpPfStep pstep pcls i (stLbl excl rl base data asrc vsrc) c c')
    (hadj : pairAdjacent (st ++ (i, stLbl excl rl base data asrc vsrc) :: rest))
    (hi : i = hartAgent cpu) (hb : base = paZ pa) (hram : ramBytes pa n) (hd : data.length = n)
    (hbytes : ∀ j, j < n → data[j]? = some (nthByte w j)) :
    ¬ othersReserve σ.resv cpu pa n ∧
      ∀ σ' : MState, σ'.mem = σ.mem.writeBytes pa n w (σ.top + 1) (hartAgent cpu) →
        σ'.log = σ.log ++ [hartAgent cpu] → σ'.resv = updCpu σ.resv cpu none →
        rmem c' (st ++ [(i, stLbl excl rl base data asrc vsrc)]) σ' := by
  have hoth : ∀ c0, c0 ≠ cpu → σ.resv c0 = none := fun c0 hne =>
    resvOthersNone c st rest σ i _ hR hadj c0 (by rw [hi]; exact hartAgentNe _ _ hne)
  refine ⟨?_, fun σ' hmem hlg hres => ?_⟩
  · rintro ⟨c0, hne, r, hr0, -⟩
    rw [hoth c0 hne] at hr0; cases hr0
  obtain ⟨himg, k, hlog⟩ := stStep pstep pcls i excl rl base data asrc vsrc c c' hstep
  subst hb hi
  refine rmemAppend c c' st _ σ σ' pa n w data (hartAgent cpu) k hR himg hlog
    (Nat.le_of_lt (hartAgent_lt cpu)) hram hd hbytes hmem hlg (fun c0 => ?_)
  rw [hres]
  by_cases h : c0 = cpu
  · simp [h]
  · simp only [updCpu, if_neg h]; exact hoth c0 h

/-- **(11)** Exclusive read: the pf bytes are TsoMem's TOP bytes, no other hart reserves the
footprint, and the reserving TsoMem state is related (the agent now mid-pair). -/
theorem pfExLoadRowMem {P D : Type} (pstep : P → D → Wlabel → P → D → Prop)
    (pcls : P → Wlabel → Wstate → WmClass) (c c' : Wpcfg P D) (st rest : List (Nat × Wlabel))
    (σ : MState) (cpu : CPU) (i : Nat) (aq : Bool) (base : Int) (tvs : List (Nat × BitVec 8))
    (asrc : List Dsrc) (pa : PAddr) (n : Nat) (w : BitVec (8 * n)) (hR : rmem c st σ)
    (hstep : wpPfStep pstep pcls i (.LExLoad aq base tvs asrc) c c') (hoc : ownCoh c)
    (hex : exclOkTs c.pcLog i base (tvs.map Prod.fst) (c.pcLog.length + 1))
    (hadj : pairAdjacent (st ++ (i, .LExLoad aq base tvs asrc) :: rest))
    (hi : i = hartAgent cpu) (hb : base = paZ pa) (hram : ramBytes pa n) (_hlen : tvs.length = n)
    (hw : ∀ j, j < n → (tvs[j]?).map Prod.snd = some (nthByte w j)) :
    σ.mem.topBytes pa n w ∧ ¬ othersReserve σ.resv cpu pa n ∧
      ∀ σ' : MState, σ'.mem = σ.mem → σ'.log = σ.log →
        σ'.resv = updCpu σ.resv cpu (some (snapOf pa n w)) →
        rmem c' (st ++ [(i, .LExLoad aq base tvs asrc)]) σ' := by
  have hoth : ∀ c0, c0 ≠ cpu → σ.resv c0 = none := fun c0 hne =>
    resvOthersNone c st rest σ i _ hR hadj c0 (by rw [hi]; exact hartAgentNe _ _ hne)
  cases hstep with
  | PFExLoad _ ag _ _ _ _ st' d' hag _ hrd =>
  refine ⟨fun j hj => ?_, ?_, fun σ' hmem hlg hres => ?_⟩
  · obtain ⟨t, htj⟩ := tvsAt tvs n w hw j hj
    obtain ⟨hlb, hrdb, -⟩ := hrd j t _ htj
    have hlat : latest c.pcImg c.pcLog (accAddr base j) t := by
      refine ⟨by rw [accAddr, hlb]; rfl, ?_⟩
      rintro ⟨t', h1, h2, m, hm, hs⟩
      by_cases hid : m.wmTid = some i
      · have hc : t' - 1 + 1 ≤ coh ag.paWs (base + (j : Int)) :=
          hoc (t' - 1) m i ag (accAddr base j) hm hid hag hs
        exact hrdb.2 ⟨t', h1, by omega, m, hm, hs⟩
      · exact hex j t (by simp [htj]) ⟨t', h1, by omega, m, hm, hs, hid⟩
    have htop := (histOfTop c.pcImg c.pcLog (accAddr base j) (nthByte w j)).2
      ⟨t, hlat, hlb⟩
    subst hb
    rw [hR.2.2.1.1 _ (hram j hj), paZAddJ pa n j (noWrapOfRam pa n hram) hj]
    exact htop
  · rintro ⟨c0, hne, r, hr0, -⟩
    rw [hoth c0 hne] at hr0; cases hr0
  · obtain ⟨⟨hl1, hl2⟩, himg, hH, -⟩ := hR
    refine ⟨⟨by rw [hlg]; exact hl1, by rw [hlg]; exact hl2⟩, himg, by rw [hmem]; exact hH,
      fun c0 => ?_⟩
    rw [hres]
    by_cases h : c0 = cpu
    · subst h hi
      refine Or.inr ⟨st.length, aq, base, tvs, asrc, by simp, fun w h1 h2 => ?_⟩
      simp at h2; omega
    · simp only [updCpu, if_neg h]; exact Or.inl (hoth c0 h)

/-- **(12)** Disk `DRead` under `candDiskLat`: the latest pf bytes are TsoMem's `dmaView`. -/
theorem pfDReadRowMem {P D : Type} (c : Wpcfg P D) (st : List (Nat × Wlabel)) (σ : MState)
    (pa : PAddr) (base : Int) (n : Nat) (tvs : List (Nat × BitVec 8)) (w : BitVec (8 * n))
    (hR : rmem c st σ)
    (htvs : ∀ j t v, tvs[j]? = some (t, v) →
      latest c.pcImg c.pcLog (accAddr base j) t ∧
      logByte c.pcImg c.pcLog t (accAddr base j) = some v)
    (hb : base = paZ pa) (hnw : pa.toNat + n ≤ 2 ^ 64)
    (hw : ∀ j, j < n → (tvs[j]?).map Prod.snd = some (nthByte w j)) :
    dmaView σ pa n w := by
  subst hb
  intro j hj b hbt
  by_cases hin : inRam (pa + BitVec.ofNat 64 j) 1
  · obtain ⟨t, htj⟩ := tvsAt tvs n w hw j hj
    obtain ⟨hlat, hlb⟩ := htvs j t _ htj
    have htop := (histOfTop c.pcImg c.pcLog (accAddr (paZ pa) j) (nthByte w j)).2
      ⟨t, hlat, hlb⟩
    rw [hR.2.2.1.1 _ hin, paZAddJ pa n j hnw hj] at hbt
    simp only [Option.bind_some] at hbt
    rw [htop] at hbt
    exact Option.some.inj hbt
  · rw [hR.2.2.1.2 _ hin] at hbt; cases hbt

/-- **(13)** Disk store (a `DWriteDev` STORE without its fabric move, see (13′)): no hart reserves the footprint, and the TsoMem DMA store is
related. -/
theorem pfDWriteRowMem {P D : Type} (pstep : P → D → Wlabel → P → D → Prop)
    (pcls : P → Wlabel → Wstate → WmClass) (c c' : Wpcfg P D) (st rest : List (Nat × Wlabel))
    (σ : MState) (rl : Bool) (base : Int) (data : List (BitVec 8)) (asrc vsrc : List Dsrc)
    (pa : PAddr) (n : Nat) (w : BitVec (8 * n)) (hR : rmem c st σ)
    (hstep : wpPfStep pstep pcls NCPU (.LStore rl base data asrc vsrc) c c')
    (hadj : pairAdjacent (st ++ (NCPU, .LStore rl base data asrc vsrc) :: rest))
    (hb : base = paZ pa) (hram : ramBytes pa n) (hd : data.length = n)
    (hbytes : ∀ j, j < n → data[j]? = some (nthByte w j)) :
    ¬ anyReserve σ.resv pa n ∧
      ∀ σ' : MState, σ'.mem = σ.mem.writeBytes pa n w (σ.top + 1) diskAgent →
        σ'.log = σ.log ++ [diskAgent] → σ'.resv = σ.resv →
        rmem c' (st ++ [(NCPU, .LStore rl base data asrc vsrc)]) σ' := by
  have hnone : ∀ c0, σ.resv c0 = none := fun c0 =>
    resvOthersNone c st rest σ NCPU _ hR hadj c0 (Nat.ne_of_lt (hartAgent_lt c0))
  refine ⟨?_, fun σ' hmem hlg hres => ?_⟩
  · rintro ⟨c0, r, hr0, -⟩
    rw [hnone c0] at hr0; cases hr0
  obtain ⟨himg, k, hlog⟩ := stStep pstep pcls NCPU false rl base data asrc vsrc c c' hstep
  subst hb
  exact rmemAppend c c' st _ σ σ' pa n w data diskAgent k hR himg hlog (Nat.le_refl _) hram hd
    hbytes hmem hlg (fun c0 => by rw [hres]; exact hnone c0)

/-- **(13′)** (W-DISK) Disk `DWriteDev` STORE: the TsoMem DMA store WITH the device's own move
(`(σ.storeDma pa n w).setDev d s'`, a nonzero width) is related. -/
theorem pfDWriteDevRowMem {P D : Type} (pstep : P → D → Wlabel → P → D → Prop)
    (pcls : P → Wlabel → Wstate → WmClass) (c c' : Wpcfg P D) (st rest : List (Nat × Wlabel))
    (σ : MState) (rl : Bool) (base : Int) (data : List (BitVec 8)) (asrc vsrc : List Dsrc)
    (pa : PAddr) (n : Nat) (w : BitVec (8 * n)) (d : DevId) (s' : DevSt d) (hR : rmem c st σ)
    (hstep : wpPfStep pstep pcls NCPU (.LStore rl base data asrc vsrc) c c')
    (hadj : pairAdjacent (st ++ (NCPU, .LStore rl base data asrc vsrc) :: rest))
    (hb : base = paZ pa) (hram : ramBytes pa n) (hd : data.length = n) (hn : n ≠ 0)
    (hbytes : ∀ j, j < n → data[j]? = some (nthByte w j)) :
    ¬ anyReserve σ.resv pa n ∧
      rmem c' (st ++ [(NCPU, .LStore rl base data asrc vsrc)]) ((σ.storeDma pa n w).setDev d s') := by
  obtain ⟨h1, h2⟩ := pfDWriteRowMem pstep pcls c c' st rest σ rl base data asrc vsrc pa n w hR hstep
    hadj hb hram hd hbytes
  refine ⟨h1, h2 _ (MState.storeDma_mem_of_ne σ pa n w hn) ?_ rfl⟩
  show (if n = 0 then σ.log else σ.log ++ [diskAgent]) = _
  rw [if_neg hn]

/-- **(14)** M1 fetch of PRISTINE bytes (no log message writes them, a hypothesis): the i-cache
agent reads the pf bytes at every view. -/
theorem pfFetchRowMemM1 {P D : Type} (c : Wpcfg P D) (st : List (Nat × Wlabel)) (σ : MState)
    (cpu : CPU) (pa : PAddr) (base : Int) (n : Nat) (tvs : List (Nat × BitVec 8))
    (w : BitVec (8 * n)) (hR : rmem c st σ) (hb : base = paZ pa) (hram : ramBytes pa n)
    (hpr : ∀ j, j < n → ∀ m ∈ c.pcLog, msgByte m (accAddr base j) = none)
    (hf : ifetchOk c.pcImg c.pcLog 0 base tvs)
    (hw : ∀ j, j < n → (tvs[j]?).map Prod.snd = some (nthByte w j)) :
    ∀ tvn, σ.mem.readBytes (ifetchAgent cpu) tvn pa n w := by
  intro tvn j hj
  obtain ⟨t, htj⟩ := tvsAt tvs n w hw j hj
  have hlb := (hf j t _ htj).1
  have himg : c.pcImg (accAddr base j) = some (nthByte w j) := by
    cases t with
    | zero => exact hlb
    | succ p =>
      rw [logByteS] at hlb
      cases hm : c.pcLog[p]? with
      | none => rw [hm] at hlb; cases hlb
      | some m =>
        rw [hm] at hlb
        simp only [Option.bind_some] at hlb
        rw [show msgByte m (base + (j : Int)) = none from hpr j hj m (List.mem_of_getElem? hm)]
          at hlb
        cases hlb
  subst hb
  unfold FlatMem.read
  rw [hR.2.2.1.1 _ (hram j hj), paZAddJ pa n j (noWrapOfRam pa n hram) hj,
    histOfPristine _ _ _ (hpr j hj), himg]
  simp [Hist.read, HEnt.visible]

/-- **(15)** A fetch at a cut `q` (a memory helper, not the M2 row): every source at or below
`q` makes the i-cache agent read the pf bytes at view `q`. -/
theorem pfFetchRowMemCut {P D : Type} (c : Wpcfg P D) (st : List (Nat × Wlabel)) (σ : MState)
    (cpu : CPU) (q : Nat) (pa : PAddr) (base : Int) (n : Nat) (tvs : List (Nat × BitVec 8))
    (w : BitVec (8 * n)) (hR : rmem c st σ) (hf : ifetchOk c.pcImg c.pcLog q base tvs)
    (hq : ∀ (j t : Nat) (v : BitVec 8), tvs[j]? = some (t, v) → t ≤ q) (hb : base = paZ pa) (hram : ramBytes pa n)
    (hw : ∀ j, j < n → (tvs[j]?).map Prod.snd = some (nthByte w j)) :
    σ.mem.readBytes (ifetchAgent cpu) q pa n w := by
  intro j hj
  obtain ⟨t, htj⟩ := tvsAt tvs n w hw j hj
  obtain ⟨hlb, hnw⟩ := hf j t _ htj
  have htq := hq j t _ htj
  rw [Nat.max_eq_right htq] at hnw
  have hsca : scaByte c.pcImg c.pcLog (ifetchAgent cpu) q (accAddr base j) t := by
    refine ⟨by rw [accAddr, hlb]; rfl, Or.inl htq, fun t' ht' hs' hv' => ?_⟩
    rcases hv' with hle | ⟨_, m, hm, hid⟩
    · exact hnw ((writesInLogByte c.pcImg c.pcLog _ t q).2 ⟨t', ht', hle, hs'⟩)
    · obtain ⟨a, ha, hal⟩ := allSome c σ hR.1.1 m (List.mem_of_getElem? hm)
      have h1 : a = ifetchAgent cpu := Option.some.inj (ha ▸ hid)
      have h2 := hR.1.2 a hal
      rw [h1] at h2
      simp only [ifetchAgent] at h2
      have h3 : (NCPU : Nat) + 1 + cpu.val ≤ (NCPU : Nat) := h2
      omega
  subst hb
  unfold FlatMem.read
  rw [hR.2.2.1.1 _ (hram j hj), paZAddJ pa n j (noWrapOfRam pa n hram) hj]
  simp only [Option.bind_some, Hist.read]
  rw [histOfFind c.pcImg c.pcLog _ _ (accAddr (paZ pa) j) t _ (allIsSome c σ hR.1.1) hlb hsca]
  rfl

/-- A frame step changes neither the log nor the image. -/
theorem frameStep {P D : Type} (pstep : P → D → Wlabel → P → D → Prop)
    (pcls : P → Wlabel → Wstate → WmClass) (i : Nat) (l : Wlabel) (c c' : Wpcfg P D)
    (h : wpPfStep pstep pcls i l c c') (hl : frameLbl l) :
    c'.pcLog = c.pcLog ∧ c'.pcImg = c.pcImg := by
  cases h <;> first | exact ⟨rfl, rfl⟩ | exact absurd hl (by simp [frameLbl])

/-- **(16)** Every other label: log and image unchanged, and the TsoMem state with the same
memory fields is related. -/
theorem pfFrameRowMem {P D : Type} (pstep : P → D → Wlabel → P → D → Prop)
    (pcls : P → Wlabel → Wstate → WmClass) (c c' : Wpcfg P D) (st rest : List (Nat × Wlabel))
    (σ : MState) (i : Nat) (l : Wlabel) (hR : rmem c st σ) (hstep : wpPfStep pstep pcls i l c c')
    (hl : frameLbl l) (hadj : pairAdjacent (st ++ (i, l) :: rest)) :
    c'.pcLog = c.pcLog ∧ c'.pcImg = c.pcImg ∧
      ∀ σ' : MState, σ'.mem = σ.mem → σ'.log = σ.log → σ'.resv = σ.resv →
        rmem c' (st ++ [(i, l)]) σ' := by
  obtain ⟨hlog, himg⟩ := frameStep pstep pcls i l c c' hstep hl
  refine ⟨hlog, himg, fun σ' hmem hlg hres => ?_⟩
  obtain ⟨⟨hl1, hl2⟩, hi, hH, hrs⟩ := hR
  refine ⟨⟨by rw [hlog, hlg]; exact hl1, by rw [hlg]; exact hl2⟩, by rw [himg]; exact hi,
    by rw [hmem, hlog, himg]; exact hH, fun cpu => ?_⟩
  rw [hres]
  rcases hrs cpu with h | h
  · exact Or.inl h
  · obtain ⟨hj, hadm | ⟨rl, b, d, asr, vs, rfl⟩⟩ := midPairOther st rest i _ l hadj h
    · exact Or.inr (midPairSnoc st _ i l h hj hadm)
    · exact absurd hl (by simp [frameLbl])

/-- **(16′)** (W-DISK) Disk `DWriteDev` SKIP / ABORT (label `LSilent`): the TsoMem state with the
device's own move only is related. -/
theorem pfDSkipRowMem {P D : Type} (pstep : P → D → Wlabel → P → D → Prop)
    (pcls : P → Wlabel → Wstate → WmClass) (c c' : Wpcfg P D) (st rest : List (Nat × Wlabel))
    (σ : MState) (i : Nat) (d : DevId) (s : DevSt d) (hR : rmem c st σ)
    (hstep : wpPfStep pstep pcls i .LSilent c c') (hadj : pairAdjacent (st ++ (i, .LSilent) :: rest)) :
    c'.pcLog = c.pcLog ∧ c'.pcImg = c.pcImg ∧ rmem c' (st ++ [(i, .LSilent)]) (σ.setDev d s) := by
  obtain ⟨h1, h2, h3⟩ := pfFrameRowMem pstep pcls c c' st rest σ i .LSilent hR hstep trivial hadj
  exact ⟨h1, h2, h3 _ rfl rfl rfl⟩

end Weak.PfStepTsoMem
