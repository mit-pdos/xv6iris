/-
Weak: **W10-2 [OWN.94] (N2′), increment 5 — THE MACHINE LABEL: every read takes the latest write,
and the per-step admissibility, single-copy atomicity, shadow and disk clauses hold for it**
(`PROGRESS-W10N2p.md`).  Lean-only, no Rocq twin.

The pinned walk re-indexes a read to its GRAPH source and owes the FLOOR (`CatFloor`,
`cpolReadCatAD`), which is stated for a candidate whose log is a GMO PREFIX of the graph
(`CtracePrefix`'s `ctpWix`, `WeakRvwmoCert4` §3.2).  N2′'s walk log is NOT a gmo prefix of `GF` (it
is the realized member's order, spike (1)), so the floor kit does not apply.  The walk instead
appends each hart's step with the MACHINE's answer: every read (plain load, RMW) reads the LATEST
write of each byte (`WeakRvwmoCert2.latestReadLbl`; an RMW must anyway, `certRmwLatestOk`).  This
file proves the per-step obligations of `CertZ2.stepOkZ` that do not depend on the hart:

  §1  THE SHADOW BOUND (`CertZ4.shadowRunBnd`): along any trace, the trace shadow's `tv`/`rv`/`coh`
      stay below the number of writes so far (`CertZ4.shadowAuthorsLen`: = the log length);
  §2  **`CertZ4.latestLoadFacts`** — a latest read is `scaOkT` at the trace shadow (view = the
      log's end) and `diskLatOk` (it IS the latest);
  §3  **`CertZ4.machLbl`** (the appended label for a row label: reads re-answered by the latest
      bytes, everything else verbatim) and **`CertZ4.machLblOk`** — it is admissible at the
      candidate's last state (`mstepOk`) and its load facts hold; `CertZ4.machLblReidx` — when the
      latest VALUES are the row's, it is `lblReidxW` of the row label (otherwise the read is
      re-valued: W10-3's taint / W10-4's poison, out of scope here).

Spec: the machine label is what the promise-free machine answers (a read of the latest write is
always admissible, `certReadWitness`); FAITHFUL, no trusted text.  Lean-only helpers
file-qualified (`CertZ4.*`).
-/
import Weak.CertZ3

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open TsoShadow

/-! # 1. The shadow bound -/

/-- Every view field of a shadow at or below `n`. -/
def CertZ4.shBnd (n : Nat) (sh : ShSt) : Prop :=
  sh.tv ≤ n ∧ sh.rv ≤ n ∧ ∀ a, sh.coh a ≤ n

theorem CertZ4.shBndMono (n m : Nat) (sh : ShSt) : n ≤ m → CertZ4.shBnd n sh → CertZ4.shBnd m sh :=
  fun h ⟨h1, h2, h3⟩ => ⟨by omega, by omega, fun a => by have := h3 a; omega⟩

theorem CertZ4.cohMaxLe (coh : Int → Nat) (base : Int) (n : Nat) :
    (∀ a, coh a ≤ n) → ∀ m, cohMax coh base m ≤ n := by
  intro h m
  induction m with
  | zero => exact Nat.zero_le _
  | succ m ih => simp only [cohMax]; have := h (accAddr base m); omega

theorem CertZ4.shSrcLe (au : List Nat) (t a t' : Nat) :
    shSrc au t = some (a, t') → t' ≤ au.length := by
  unfold shSrc
  split
  · intro h; simp only [Option.some.injEq, Prod.mk.injEq] at h; omega
  · rename_i ht
    intro h
    cases hl : au[t - 1]? with
    | none => rw [hl] at h; cases h
    | some b =>
      rw [hl] at h
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      have := lookup_lt_Some hl
      omega

/-- The sources of a load's footprint are bounded. -/
def CertZ4.srcsBnd (n : Nat) (srcs : List (Option (Nat × Nat))) : Prop :=
  ∀ x a t, x ∈ srcs → x = some (a, t) → t ≤ n

theorem CertZ4.shForeignLe (i n : Nat) :
    ∀ srcs, CertZ4.srcsBnd n srcs → shForeign i srcs ≤ n := by
  intro srcs
  induction srcs with
  | nil => intro _; exact Nat.zero_le _
  | cons x srcs ih =>
    intro h
    have ih' := ih (fun y a t hy he => h y a t (List.mem_cons_of_mem _ hy) he)
    cases x with
    | none => exact ih'
    | some p =>
      obtain ⟨a, t⟩ := p
      have ht := h _ a t (by simp) rfl
      simp only [shForeign]
      split <;> omega

theorem CertZ4.srcsBndMap (au : List Nat) (ts : List Nat) :
    CertZ4.srcsBnd au.length (ts.map (shSrc au)) := by
  intro x a t hx he
  obtain ⟨t0, -, rfl⟩ := List.mem_map.1 hx
  exact CertZ4.shSrcLe au t0 a t he

theorem CertZ4.loadBnd (i n : Nat) (sh : ShSt) (base : Int) (srcs : List (Option (Nat × Nat))) :
    CertZ4.shBnd n sh → CertZ4.srcsBnd n srcs → CertZ4.shBnd n (sh.load cohSrc i base srcs) := by
  intro ⟨htv, hrv, hcoh⟩ hs
  have hfl : shFloor sh base srcs.length ≤ n := by
    unfold shFloor; have := CertZ4.cohMaxLe sh.coh base n hcoh srcs.length; omega
  have hfo := CertZ4.shForeignLe i n srcs hs
  have htvn : shTvn i sh base srcs ≤ n := by unfold shTvn; omega
  refine ⟨htv, ?_, fun a => ?_⟩
  · show max sh.rv (shTvn i sh base srcs) ≤ n
    omega
  · show cohSrc.load i sh.coh base srcs (shTvn i sh base srcs) a ≤ n
    simp only [cohSrc]
    split
    · rename_i j _
      split
      · rename_i au t hj
        split
        · exact hcoh a
        · have := hs _ au t (List.mem_of_getElem? hj) rfl
          have := hcoh a
          omega
      · exact hcoh a
    · exact hcoh a

/-- The viewer's own step keeps the bound, the write count growing by the step's write. -/
theorem CertZ4.stepBnd (i : Nat) (au : List Nat) (sh : ShSt) (lb : Lbl) :
    CertZ4.shBnd au.length sh →
    CertZ4.shBnd (au.length + if lbIsW lb then 1 else 0) (shStepL cohSrc i au sh lb) := by
  intro hb
  obtain ⟨htv, hrv, hcoh⟩ := hb
  have hstore : ∀ (sh' : ShSt) (excl : Bool) (base : Int) (m : Nat), sh'.tv ≤ au.length + 1 →
      sh'.rv ≤ au.length + 1 → (∀ a, sh'.coh a ≤ au.length + 1) →
      CertZ4.shBnd (au.length + 1) (sh'.store cohSrc au.length excl base m) := by
    intro sh' excl base m h1 h2 h3
    refine ⟨?_, h2, fun a => ?_⟩
    · show (if excl && sh'.acq then au.length + 1 else sh'.tv) ≤ au.length + 1
      split <;> omega
    · show cohSrc.store sh'.coh base m a ≤ au.length + 1
      simp only [cohSrc]
      split
      · exact Nat.zero_le _
      · exact h3 a
  cases lb with
  | LLoad aq base ts vs =>
    simp only [lbIsW, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
    exact CertZ4.loadBnd i au.length sh base _ ⟨htv, hrv, hcoh⟩ (CertZ4.srcsBndMap au ts)
  | LStore rl base vs kc =>
    simp only [lbIsW, ↓reduceIte]
    exact hstore sh false base vs.length (by omega) (by omega) (fun a => by have := hcoh a; omega)
  | LFence pr pw sr sw =>
    simp only [lbIsW, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
    have hpub : MachCSL.ownPub i au ≤ au.length := by
      have := MachCSL.ownPubAux_le i au 0
      unfold MachCSL.ownPub; omega
    refine ⟨?_, hrv, hcoh⟩
    show MachCSL.fencePost (pw && sr) (pr && sr) sh.tv sh.rv (MachCSL.ownPub i au) ≤ au.length
    unfold MachCSL.fencePost
    split <;> split <;> omega
  | LRmw aq rl base ts rvs wvs kc =>
    simp only [lbIsW, ↓reduceIte]
    refine hstore _ true base wvs.length ?_ ?_ ?_
    · show (if aq then au.length else sh.tv) ≤ au.length + 1
      split <;> omega
    · show au.length ≤ au.length + 1
      omega
    · intro a; show sh.coh a ≤ au.length + 1; have := hcoh a; omega
  | LIo k base vs =>
    simp only [lbIsW, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
    exact ⟨htv, hrv, hcoh⟩

/-- **THE SHADOW BOUND**: along any trace, every view field of agent `i`'s trace shadow is at most
the number of writes so far. -/
theorem CertZ4.shadowRunBnd (i : Nat) (tr : List Estep) :
    CertZ4.shBnd (shadowRun cohSrc i tr).1.length (shadowRun cohSrc i tr).2 := by
  induction tr using snocInd with
  | h0 => exact ⟨Nat.zero_le _, Nat.zero_le _, fun _ => Nat.zero_le _⟩
  | hs tr s ih =>
    rw [shadowRunSnoc]
    generalize shadowRun cohSrc i tr = r at ih ⊢
    obtain ⟨au, sh⟩ := r
    dsimp only at ih
    simp only [shActL]
    by_cases hi : s.esAg = i
    · rw [if_pos hi]
      have := CertZ4.stepBnd i au sh s.esLb ih
      cases hw : lbIsW s.esLb
      · rw [hw] at this; simpa [hw] using this
      · rw [hw] at this; simpa [hw] using this
    · rw [if_neg hi]
      cases hw : lbIsW s.esLb
      · simpa [hw] using ih
      · simp only [↓reduceIte, List.length_append, List.length_singleton]
        exact CertZ4.shBndMono _ _ _ (by omega) ih

theorem CertZ4.esMsgLen (s : Estep) : (esMsg s).length = if lbIsW s.esLb then 1 else 0 := by
  unfold esMsg
  cases hw : lbIsW s.esLb
  · cases hwr : lbWr s.esLb with
    | none => rfl
    | some p => rw [lbWrIsW _ p hwr] at hw; cases hw
  · obtain ⟨base, vs, hwr⟩ := lbIsWWr _ hw
    rw [hwr]; rfl

/-- The shadow's author list is the log: one entry per write. -/
theorem CertZ4.shadowAuthorsLen (stamp : CohStamp) (i : Nat) (tr : List Estep) :
    (shadowRun stamp i tr).1.length = (trMsgs tr).length := by
  induction tr using snocInd with
  | h0 => rfl
  | hs tr s ih =>
    rw [shadowRunSnoc, trMsgsApp, List.length_append, ← ih]
    show (if lbIsW s.esLb then _ ++ [s.esAg] else _).length = _ + (esMsg s ++ []).length
    rw [List.append_nil, CertZ4.esMsgLen]
    split <;> simp

/-! # 2. The latest read's load facts -/

/-- **A LATEST READ IS SINGLE-COPY ATOMIC AT THE SHADOW AND READS THE DISK'S LATEST**: at the view
`|log|`, the shadow's floor is below it (§1) and every byte reads its latest write. -/
theorem CertZ4.latestLoadFacts (c : Cand) (x : Nat) (base : Int) (n : Nat) :
    latestBytesOk c base n →
    scaOkT (shadowOf cohSrc c.cdTr x) (candLastSt c).msImg (candLastSt c).msLog x base
        (lrdTs c base n) ∧
      diskLatOk (candLastSt c).msImg (candLastSt c).msLog x base (lrdTs c base n) := by
  intro hb
  rw [candLastImg, candLastLog]
  have hlat : ∀ j t, (lrdTs c base n)[j]? = some t →
      latest c.cdImg (cdLogEnd c) (accAddr base j) t := by
    intro j t hj
    obtain ⟨hjn, rfl⟩ := lrdTsLookup c base n j t hj
    exact latestTsLatest _ _ _ (hb j hjn)
  refine ⟨⟨(cdLogEnd c).length, Nat.le_refl _, ?_, fun j t hj => ?_⟩, fun _ j t hj => hlat j t hj⟩
  · have hbnd := CertZ4.shadowRunBnd x c.cdTr
    rw [CertZ4.shadowAuthorsLen, ← cdLogEndFull] at hbnd
    obtain ⟨htv, -, hcoh⟩ := hbnd
    unfold shFloor
    show max (shadowRun cohSrc x c.cdTr).2.tv
      (cohMax (shadowRun cohSrc x c.cdTr).2.coh base _) ≤ _
    have := CertZ4.cohMaxLe _ base _ hcoh (lrdTs c base n).length
    omega
  · obtain ⟨hs, hnw⟩ := hlat j t hj
    refine ⟨hs, .inl (logByteBounded _ _ _ _ hs), fun t' ht' hs' _ => hnw ?_⟩
    exact (writesInLogByte _ _ _ _ _).2 ⟨t', ht', logByteBounded _ _ _ _ hs', hs'⟩

/-! # 3. The machine label -/

/-- **THE MACHINE LABEL** for a row label at candidate `c`: a plain load and an RMW read the latest
bytes of their footprint; a store, a fence, an I/O event are appended verbatim. -/
def CertZ4.machLbl (c : Cand) (lb : Lbl) : Lbl :=
  match lb with
  | .LLoad aq base ts _ => .LLoad aq base (lrdTs c base ts.length) (lrdVs c base ts.length)
  | .LRmw aq rl base ts _ wvs kc =>
      .LRmw aq rl base (lrdTs c base ts.length) (lrdVs c base ts.length) wvs kc
  | l => l

/-- The footprint a row label READS (the latest bytes must exist there). -/
def CertZ4.readFoot (c : Cand) (lb : Lbl) : Prop :=
  match lb with
  | .LLoad _ base ts _ => latestBytesOk c base ts.length
  | .LRmw _ _ base ts _ _ _ => latestBytesOk c base ts.length
  | _ => True

/-- The label shapes `gwf` asks of a row label (`candShape`'s). -/
def CertZ4.lblShape (lb : Lbl) : Prop :=
  match lb with
  | .LLoad _ _ ts vs => vs.length = ts.length
  | .LStore _ _ vs _ => vs ≠ []
  | .LFence .. => True
  | .LRmw _ _ _ ts rvs wvs _ => wvs ≠ [] ∧ wvs.length = ts.length ∧ rvs.length = ts.length
  | .LIo .. => True

/-- **`CertZ4.machLblOk`**: the machine label is admissible at the candidate's last state, and its
load facts (`scaOkT` at the trace shadow, `diskLatOk`) hold. -/
theorem CertZ4.machLblOk (c : Cand) (x : Nat) (lb : Lbl) :
    srvwmoConsistent c → CertZ4.lblShape lb → CertZ4.readFoot c lb →
    mstepOk (candLastSt c) x (CertZ4.machLbl c lb) ∧
    (∀ (aq : Bool) (base : Int) (ts : List Nat) (vs : List (BitVec 8)),
      CertZ4.machLbl c lb = .LLoad aq base ts vs →
      scaOkT (shadowOf cohSrc c.cdTr x) (candLastSt c).msImg (candLastSt c).msLog x base ts ∧
        diskLatOk (candLastSt c).msImg (candLastSt c).msLog x base ts) := by
  intro hc hsh hft
  cases lb with
  | LLoad aq base ts vs =>
    refine ⟨certReadWitness c x aq base ts.length hc hft, ?_⟩
    intro aq' base' ts' vs' he
    simp only [CertZ4.machLbl, Lbl.LLoad.injEq] at he
    obtain ⟨-, rfl, rfl, -⟩ := he
    exact CertZ4.latestLoadFacts c x base ts.length hft
  | LStore rl base vs kc =>
    exact ⟨certWriteOk c x rl base vs kc hsh, fun _ _ _ _ he => by simp [CertZ4.machLbl] at he⟩
  | LFence pr pw sr sw =>
    exact ⟨certFenceOk c x pr pw sr sw, fun _ _ _ _ he => by simp [CertZ4.machLbl] at he⟩
  | LRmw aq rl base ts rvs wvs kc =>
    refine ⟨certRmwLatestOk c x aq rl base ts.length wvs kc hc hft hsh.1 hsh.2.1,
      fun _ _ _ _ he => by simp [CertZ4.machLbl] at he⟩
  | LIo k base vs =>
    exact ⟨trivial, fun _ _ _ _ he => by simp [CertZ4.machLbl] at he⟩

/-- **When the latest VALUES are the row's, the machine label is `lblReidxW` of the row label**
(re-timed only; a store, a fence, an I/O event are verbatim). -/
theorem CertZ4.machLblReidx (c : Cand) (lb : Lbl) :
    (∀ aq base ts vs, lb = .LLoad aq base ts vs → lrdVs c base ts.length = vs) →
    (∀ aq rl base ts rvs wvs kc, lb = .LRmw aq rl base ts rvs wvs kc →
      lrdVs c base ts.length = rvs) →
    lblReidxW lb (CertZ4.machLbl c lb) := by
  intro hl hr
  apply lblReidxWOf
  cases lb with
  | LLoad aq base ts vs =>
    show aq = aq ∧ base = base ∧ lrdVs c base ts.length = vs ∧
      (lrdTs c base ts.length).length = ts.length
    exact ⟨rfl, rfl, hl aq base ts vs rfl, by simp [lrdTs]⟩
  | LStore rl base vs kc => exact lblReidxRefl _
  | LFence pr pw sr sw => exact lblReidxRefl _
  | LRmw aq rl base ts rvs wvs kc =>
    show aq = aq ∧ rl = rl ∧ base = base ∧ lrdVs c base ts.length = rvs ∧ wvs = wvs ∧ kc = kc ∧
      (lrdTs c base ts.length).length = ts.length
    exact ⟨rfl, rfl, rfl, hr aq rl base ts rvs wvs kc rfl, rfl, rfl, by simp [lrdTs]⟩
  | LIo k base vs => exact lblReidxRefl _

end Weak
