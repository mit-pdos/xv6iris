/-
Weak: **spike S-R (route P, report-only) — realizing a read-gate-blocked plain load STALE at its GF
position** (`~/dev/weak-orch/weakmach/proposal-A5.md` §6 item S-R; `PROGRESS-SPSR.md`).  Lean-only, no
Rocq twin.  A leaf: nothing imports this file.

**Spec, stated first.**  riscv.cat's load value axiom lets a plain load return a write that is
co-before the latest one at its byte (a STALE read) whenever the load is gmo-before that later write
(from-reads); two plain loads of a hart to different bytes are unordered (no ppo rule), so a later load
may read below an earlier one.  The registered machine and `SbCand` both allow this (`byteRd`: any
timestamp `t` with no write to the byte in `(t, max vpre (coh a)]`); the gated walk (`SbOrd`) never
uses it: its read gate (`srcGate`/`valGate`) reads at the landed TOP, so a landing must wait for every
GF reader of the byte's current latest write (`readersDone`) — which is what makes reads WAITED ON,
row H3 (`SbOrd.HeadOrdRd`) and its named inputs (N3/N4/N10), and the three exempt pcs ([OWN.112],
[OWN.124]) necessary.

  §1  a boolean checker for `SbCand` runs whose loads read ANY readable timestamp (`SpikeSR.runOkBS`,
      sound: `SpikeSR.runOfBS` — every passing step list is an `SbCand.execWfP` run under every lawful
      landing policy).
  §2  **the two machine-checked "no member" litmus graphs of the current gate HAVE stale members**,
      with GF's labels VERBATIM (every timestamp = GF's write index), landing in GF's gmo|W order (S-P)
      and drained:
      * `SpikeSR.l8MemberSR` — `SbStuck.l8` (F-P-W3-3's witness that H3 does not follow from RVWMO +
        the text: `SbStuck.l8NoMember`); the stale read is `r1` (byte `C`, the image, after `C := 1`
        landed).  This is A5's MP-without-acquire shape.
      * `SpikeSR.l4MemberSR` — `SBAcqP.l4` WITHOUT the exemption (F-R45-1's witness for [OWN.112]:
        `SBAcqP.l4NoMemberP`); the stale read is `r_B` (byte `lk`, A's acquire, after `Y` and C's swap
        landed); `e_B` (`ilock+0xe`) reads GF's source `w` — no exemption, no re-sourcing.
  §3  **the soundness obligation, isolated** (`SpikeSR.staleStep`): at an S-P walk state (the landed
      write list a prefix of `gwrites G`, `SpikeSP.wrW`), a non-forwarded byte whose GF source has
      landed is an `SbCand` byte read AT GF's TIMESTAMP as soon as the hart's read view is DOMINATED
      (`SpikeSR.DomAt`: `max (loadVpre ws aq) (coh ws a) < gwix n` for every GF write `n` to the byte
      co-after the source).  `DomAt` is exactly `WeakAxiomatic3`'s view domination (`frdomB`),
      transported to the walk; its preservation along the walk is the redesign's cost item.
  §4  **why S-R presupposes S-P** (`SpikeSR.dm`, RVWMO-consistent `dmCat`): with `readersDone` gone,
      a per-byte landing order can STRAND a stale read (`dmStranded`: after `W_a` lands before `W_b`,
      C's fence lifts its view past `W_a` and `r2` reads the image at no timestamp), while GF's write
      order realizes it (`dmMemberSR`).

Spec: FAITHFUL (theorems about the existing model; stale reads are riscv.cat's load value axiom;
nothing assumed).  Lean-only helpers `SpikeSR.*`.
-/
import Weak.SpikeSP
import Weak.SbCandLit
import Weak.LitmusSbStuck2

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Lbl

namespace SpikeSR

/-! # 1. A checker for runs with STALE reads -/

/-- One byte of a load: forwarded (the youngest own entry), or ANY readable log timestamp. -/
def staleByteB (img : Image) (log : List Wmsg) (ws : Wstate) (aq : Bool) (sb : List SbEnt) (a : Int)
    (t : Nat) (v : BitVec 8) : Bool :=
  match SbCand.fwdByte sb a with
  | some v' => decide (v = v')
  | none => decide (logByte img log t a = some v) && readableb img log ws (loadVpre ws aq) a t

def staleRdB (img : Image) (log : List Wmsg) (ws : Wstate) (aq : Bool) (sb : List SbEnt) (base : Int)
    (ts : List Nat) (vs : List (BitVec 8)) : Bool :=
  decide (vs.length = ts.length) &&
  (List.range ts.length).all (fun j =>
    match ts[j]?, vs[j]? with
    | some t, some v => staleByteB img log ws aq sb (accAddr base j) t v
    | _, _ => true)

theorem staleRdBSound (img : Image) (log : List Wmsg) (ws : Wstate) (aq : Bool) (sb : List SbEnt)
    (base : Int) (ts : List Nat) (vs : List (BitVec 8)) :
    staleRdB img log ws aq sb base ts vs = true → SbCand.rdOkSb img log ws aq base ts vs sb := by
  intro h
  unfold staleRdB at h
  rw [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨hlen, hall⟩ := h
  refine ⟨hlen, fun j t v hj hv => ?_⟩
  have hc := hall j (List.mem_range.2 (lookup_lt_Some hj))
  simp only [hj, hv] at hc
  unfold staleByteB at hc
  cases hf : SbCand.fwdByte sb (accAddr base j) with
  | some v' =>
    simp only [hf, decide_eq_true_eq] at hc
    left; rw [hc]
  | none =>
    simp only [hf, Bool.and_eq_true, decide_eq_true_eq] at hc
    exact Or.inr ⟨rfl, hc.1, (readablebSpec _ _ _ _ _ _).1 hc.2⟩

/-- The event-step checker: STALE-capable plain loads, everything else as `SbCand.okEB`. -/
def okEBS (σ : SbCand.CandS) (i : Nat) (l : Lbl) : Bool :=
  match l with
  | LLoad aq base ts vs =>
    staleRdB σ.ms.msImg σ.ms.msLog (σ.ms.msWs i) aq (σ.sb i) base ts vs &&
      (!aq || SbCand.noRlB (σ.sb i))
  | l => SbCand.okEB σ i l

theorem okEBSSound (σ : SbCand.CandS) (i : Nat) (l : Lbl) :
    SbCand.Inv σ → okEBS σ i l = true → SbCand.stepE σ i l (SbCand.nextE σ i l) := by
  intro hI h
  cases l with
  | LLoad aq base ts vs =>
    simp only [okEBS, Bool.and_eq_true] at h
    exact SbCand.stepE.load aq base ts vs (staleRdBSound _ _ _ aq _ _ _ _ h.1)
      (SbCand.impB h.2 (SbCand.noRlBSound _))
  | LStore rl base vs k => exact SbCand.okEBSound σ i _ hI h
  | LFence pr pw sr sw => exact SbCand.okEBSound σ i _ hI h
  | LRmw aq rl base ts rvs wvs k => exact SbCand.okEBSound σ i _ hI h
  | LIo kd base vs => exact SbCand.okEBSound σ i _ hI h

def runOkBS (σ : SbCand.CandS) : List (Estep × List Nat) → Bool
  | [] => true
  | st :: rest => okEBS σ st.1.esAg st.1.esLb &&
      SbCand.landAllB (SbCand.nextE σ st.1.esAg st.1.esLb) st.2 &&
      runOkBS (SbCand.nextM σ st) rest

theorem runSoundS (pol : SbPol) : ∀ (steps : List (Estep × List Nat)) (σ : SbCand.CandS),
    SbCand.Inv σ → runOkBS σ steps = true →
    SbCand.Steps pol (SbCand.statesOf σ steps) (steps.map Prod.fst)
  | [], _, _, _ => ⟨rfl, fun _ _ _ _ hs => by simp at hs⟩
  | st :: rest, σ, hI, h => by
    simp only [runOkBS, Bool.and_eq_true] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    have he := okEBSSound σ st.1.esAg st.1.esLb hI h1
    obtain ⟨hl, hI'⟩ := SbCand.landAllSound pol st.2 _ (SbCand.invStepE _ _ _ _ hI he) h2
    exact SbCand.stepsCons pol σ (SbCand.nextM σ st) st.1 _ _
      (runSoundS pol rest _ hI' h3) (SbCand.statesOfHead _ _) ⟨_, he, hl⟩

/-- **THE STALE CHECKER IS SOUND**: a passing step list from an initial state is a buffered run under
EVERY lawful landing policy. -/
theorem runOfBS (pol : SbPol) (σ0 : SbCand.CandS) (steps : List (Estep × List Nat)) :
    SbCand.initS σ0 → runOkBS σ0 steps = true →
    SbCand.execWfP pol ⟨SbCand.statesOf σ0 steps, steps.map Prod.fst⟩ := fun hi h =>
  ⟨fun σ h0 => by
      rw [SbCand.statesOfHead, Option.some.injEq] at h0
      subst h0; exact hi,
    runSoundS pol steps σ0 (SbCand.invInit σ0 hi) h⟩

/-! # 2. The current gate's "no member" graphs have stale members -/

/-! ## 2.1 `SbStuck.l8` (F-P-W3-3) -/

/-- Hart 0: `C := 1`, lands; `fence rw,rw`; `amoswap.aq L`.  Hart 1: `r0 := L` (the swap, top),
`r1 := C` — STALE (the image, `C := 1` landed): hart 1's view is 0 (no fence, no acquire). -/
def o8 : List (Geid × List Geid) :=
  [((0, 0), [(0, 0)]), ((0, 1), []), ((0, 2), []), ((1, 0), []), ((1, 1), [])]

def steps8 : List (Estep × List Nat) := SbCandLit.toSteps SbStuck.l8.gdG o8

theorem l8RunB : runOkBS (SbCandLit.σ0 SbStuck.l8.gdG.gxImg) steps8 = true := by decide +kernel

/-- …and it is NOT a top-read run (the current read rule rejects `r1`). -/
theorem l8NotTop : SbCand.runOkB (SbCandLit.σ0 SbStuck.l8.gdG.gxImg) steps8 = false := by
  decide +kernel

/-- **`SbStuck.l8` IS AN `SbCand` RUN WITH GF's LABELS VERBATIM** (under every lawful policy). -/
theorem l8MemberSR (pol : SbPol) :
    SbCand.execWfP pol ⟨SbCand.statesOf (SbCandLit.σ0 SbStuck.l8.gdG.gxImg) steps8,
      steps8.map Prod.fst⟩ :=
  runOfBS pol _ _ (SbCandLit.σ0Init _) l8RunB

/-- Per-hart traces are GF's rows; the final log is GF's writes in gmo order (S-P); buffers drained. -/
theorem l8Facts :
    SbCandLit.traceOf steps8 0 = SbStuck.l8Prog[0]! ∧ SbCandLit.traceOf steps8 1 = SbStuck.l8Prog[1]! ∧
    (steps8.map Prod.fst).all (fun s => decide (s.esAg < 2)) = true ∧
    (SbCand.statesOf (SbCandLit.σ0 SbStuck.l8.gdG.gxImg) steps8).getLast?.map (·.ms.msLog) =
      some ((gwrites SbStuck.l8.gdG).filterMap (SbCandLit.msgOf SbStuck.l8.gdG)) ∧
    (SbCand.statesOf (SbCandLit.σ0 SbStuck.l8.gdG.gxImg) steps8).getLast?.map
      (fun σ => (σ.sb 0, σ.sb 1)) = some ([], []) := by
  decide +kernel

/-! ## 2.2 `SBAcqP.l4` (F-R45-1) WITHOUT the exemption -/

/-- A: `acquire(z)`, `fence rw,w`, `Y := 0` (lands); C: `e_C` (reads `Y`, top), the swap, `r_C` (the
image `ref`, top); A: `acquire(itable)`, the `ref` load, `w := ref − 1` (lands); B: `e_B` (`ilock+0xe`,
reads `w`, top — GF's source, NOT exempt), `r_B` — STALE (A's acquire write, after `Y` and C's swap
landed; hart B's read view is 0). -/
def o4 : List (Geid × List Geid) :=
  [((0, 0), []), ((0, 1), []), ((0, 2), [(0, 2)]), ((2, 0), []), ((2, 1), []), ((2, 2), []),
   ((0, 3), []), ((0, 4), []), ((0, 5), [(0, 5)]), ((1, 0), []), ((1, 1), [])]

def steps4 : List (Estep × List Nat) := SbCandLit.toSteps SBAcqP.l4.gdG o4

theorem l4RunB : runOkBS (SbCandLit.σ0 SBAcqP.l4.gdG.gxImg) steps4 = true := by decide +kernel

theorem l4NotTop : SbCand.runOkB (SbCandLit.σ0 SBAcqP.l4.gdG.gxImg) steps4 = false := by
  decide +kernel

/-- **F-R45-1's graph IS AN `SbCand` RUN WITH GF's LABELS VERBATIM, no exemption.** -/
theorem l4MemberSR (pol : SbPol) :
    SbCand.execWfP pol ⟨SbCand.statesOf (SbCandLit.σ0 SBAcqP.l4.gdG.gxImg) steps4,
      steps4.map Prod.fst⟩ :=
  runOfBS pol _ _ (SbCandLit.σ0Init _) l4RunB

theorem l4Facts :
    SbCandLit.traceOf steps4 0 = (SBAcqP.l4Prog 5 b1)[0]! ∧
    SbCandLit.traceOf steps4 1 = (SBAcqP.l4Prog 5 b1)[1]! ∧
    SbCandLit.traceOf steps4 2 = (SBAcqP.l4Prog 5 b1)[2]! ∧
    (steps4.map Prod.fst).all (fun s => decide (s.esAg < 3)) = true ∧
    (SbCand.statesOf (SbCandLit.σ0 SBAcqP.l4.gdG.gxImg) steps4).getLast?.map (·.ms.msLog) =
      some ((gwrites SBAcqP.l4.gdG).filterMap (SbCandLit.msgOf SBAcqP.l4.gdG)) ∧
    (SbCand.statesOf (SbCandLit.σ0 SBAcqP.l4.gdG.gxImg) steps4).getLast?.map
      (fun σ => (σ.sb 0, σ.sb 1, σ.sb 2)) = some ([], [], []) := by
  decide +kernel

/-! # 3. The soundness obligation, isolated: view domination -/

section Dom

open SbWalk SbAgree SbReplay SbOrd SpikeSP

/-- A member write message carries GF's footprint (`pfx`: write labels are GF's). -/
theorem msgOfRow (G : Gexec) (X : Geid → Prop) (w : WS) (hpf : pfx G X w) (e : Geid) (m : Wmsg) :
    wmsgOf w.rows e = some m → ∀ (a : Int) (u : BitVec 8),
      msgByte m a = some u ↔ gwritesByte G e a u := by
  intro hm a u
  unfold wmsgOf at hm
  cases hr : (w.rows e.1)[e.2]? with
  | none => rw [hr] at hm; cases hm
  | some l' =>
    rw [hr] at hm
    obtain ⟨l0, hl0, hrel⟩ := hpf.1 e.1 e.2 l' hr
    have hl0' : gxLbl G e = some l0 := hl0
    dsimp only at hm
    rw [relXWr _ _ _ hrel] at hm
    cases hw : lbWr l0 with
    | none => rw [hw] at hm; cases hm
    | some q =>
      obtain ⟨base, vs⟩ := q
      rw [hw] at hm
      simp only [Option.some.injEq] at hm
      subst hm
      constructor
      · intro h
        have hs : (msgByte ⟨base, vs, some e.1, lbCls l'⟩ a).isSome := by rw [h]; rfl
        obtain ⟨j, -, rfl⟩ := msgByteIndex base vs _ _ a hs
        rw [msgByteVal] at h
        exact ⟨l0, base, vs, j, hl0', hw, h, rfl⟩
      · rintro ⟨l1, base1, vs1, j, hl1, hw1, hv, ha⟩
        rw [hl0', Option.some.injEq] at hl1
        subst hl1
        rw [hw, Option.some.injEq, Prod.mk.injEq] at hw1
        obtain ⟨rfl, rfl⟩ := hw1
        rw [← ha, msgByteVal]; exact hv

/-- Every landed write of the member has a message. -/
theorem wrWMsg (w : WS) (e : Geid) : e ∈ wrW w → ∃ m, wmsgOf w.rows e = some m := by
  intro he
  have hb := (List.mem_filter.1 he).2
  unfold rwW at hb; unfold wmsgOf
  cases hl : (w.rows e.1)[e.2]? with
  | none => rw [hl] at hb; cases hb
  | some l =>
    rw [hl] at hb
    cases l <;> simp_all [lbIsW, lbWr]

theorem filterMapGet {α β : Type} (f : α → Option β) : ∀ (l : List α), (∀ x, x ∈ l → (f x).isSome) →
    ∀ i : Nat, (l.filterMap f)[i]? = (l[i]?).bind f
  | [], _, i => by simp
  | x :: l, h, i => by
    obtain ⟨y, hy⟩ := Option.isSome_iff_exists.1 (h x List.mem_cons_self)
    have ih := filterMapGet f l (fun z hz => h z (List.mem_cons_of_mem _ hz))
    cases i with
    | zero => simp [List.filterMap_cons, hy]
    | succ i => simp only [List.filterMap_cons, hy, List.getElem?_cons_succ]; exact ih i

theorem filterMapLen {α β : Type} (f : α → Option β) : ∀ (l : List α), (∀ x, x ∈ l → (f x).isSome) →
    (l.filterMap f).length = l.length
  | [], _ => rfl
  | x :: l, h => by
    obtain ⟨y, hy⟩ := Option.isSome_iff_exists.1 (h x List.mem_cons_self)
    simp only [List.filterMap_cons, hy, List.length_cons]
    rw [filterMapLen f l (fun z hz => h z (List.mem_cons_of_mem _ hz))]

/-- **THE S-P LOG, by index**: position `i` of the member's log is the message of GF's `i`-th write. -/
theorem logAt (img : Image) (G : Gexec) (w : WS) (hI : Inv img w) (hW : wrW w <+: gwrites G) :
    w.σ.ms.msLog.length = (wrW w).length ∧
    ∀ i, i < (wrW w).length → ∃ e m, (gwrites G)[i]? = some e ∧ wmsgOf w.rows e = some m ∧
      w.σ.ms.msLog[i]? = some m := by
  have hs : ∀ x, x ∈ wrW w → (wmsgOf w.rows x).isSome := by
    intro x hx; obtain ⟨m, hm⟩ := wrWMsg w x hx; rw [hm]; rfl
  rw [logOfWrW img w hI]
  refine ⟨filterMapLen _ _ hs, fun i hi => ?_⟩
  obtain ⟨e, he⟩ : ∃ e, (wrW w)[i]? = some e := ⟨_, List.getElem?_eq_getElem hi⟩
  obtain ⟨m, hm⟩ := wrWMsg w e (List.mem_of_getElem? he)
  obtain ⟨T, hT⟩ := hW
  refine ⟨e, m, ?_, hm, ?_⟩
  · rw [← hT, List.getElem?_append_left hi]; exact he
  · rw [filterMapGet _ _ hs, he]; exact hm

/-- **THE STALE BYTE READ AT GF's TIMESTAMP**: at an S-P state, a GF read of byte `a` at timestamp `t`
whose source has LANDED (`t ≤ |wrW|`) sees GF's value at log position `t`, and the log has no write to
`a` in `(t, V]` for any bound `V` below every GF write to `a` co-after the source. -/
theorem staleStep (img : Image) (G : Gexec) (X : Geid → Prop) (w : WS) (hI : Inv img w)
    (hpf : pfx G X w) (hW : wrW w <+: gwrites G) (hnd : G.gxGmo.Nodup) (hlv : gloadValue G)
    (himg : G.gxImg = img) (e : Geid) (a : Int) (t : Nat) (v : BitVec 8) (hrd : greadsByte G e a t v)
    (hland : t ≤ (wrW w).length) (V : Nat)
    (hdom : ∀ n u, gwritesByte G n a u → t < gwix G n → V < gwix G n) :
    logByte img w.σ.ms.msLog t a = some v ∧ ¬ writesIn w.σ.ms.msLog a t V := by
  obtain ⟨hlen, hat⟩ := logAt img G w hI hW
  refine ⟨?_, ?_⟩
  · have hv := (hlv e a t v hrd).1
    cases t with
    | zero => show img a = some v; rw [← himg]; exact hv
    | succ i =>
      obtain ⟨src, hsrc, hsw, -⟩ := hv
      obtain ⟨e', m, he', hm, hl⟩ := hat i (by omega)
      have : e' = src := by
        have h2 : (gwrites G)[i]? = some src := hsrc
        rw [he', Option.some.injEq] at h2; exact h2
      subst this
      rw [logByteS, hl]
      exact (msgOfRow G X w hpf _ m hm a v).2 hsw
  · rintro ⟨t', hlo, hhi, m, hm, hs⟩
    have hlt : t' - 1 < (wrW w).length := by rw [← hlen]; exact lookup_lt_Some hm
    obtain ⟨e', m', he', hm', hl⟩ := hat (t' - 1) hlt
    rw [hl, Option.some.injEq] at hm
    subst hm
    obtain ⟨u, hu⟩ := Option.isSome_iff_exists.1 hs
    have hwb := (msgOfRow G X w hpf e' m' hm' a u).1 hu
    have hix : gwix G e' = t' := by
      have := gwixOfLookup G (t' - 1) e' hnd he'
      omega
    have := hdom e' u hwb (by omega)
    omega

/-- **VIEW DOMINATION AT A BYTE** (the S-R invariant, `WeakAxiomatic3.frdomB` transported): agent `x`'s
read view at byte `a` is below every GF write to `a` co-after timestamp `t`. -/
def DomAt (G : Gexec) (w : WS) (x : Nat) (aq : Bool) (a : Int) (t : Nat) : Prop :=
  ∀ n u, gwritesByte G n a u → t < gwix G n →
    max (loadVpre (w.σ.ms.msWs x) aq) (coh (w.σ.ms.msWs x) a) < gwix G n

/-- **THE S-R LOAD ARM**: a GF plain-load label all of whose bytes are forwarded with GF's value or have
a LANDED GF source with a dominated view IS an `SbCand` load step WITH GF's LABEL VERBATIM (no
re-timing, no member-latest requirement). -/
theorem staleLoadArm (img : Image) (G : Gexec) (X : Geid → Prop) (w : WS) (hI : Inv img w)
    (hpf : pfx G X w) (hW : wrW w <+: gwrites G) (hwf : gwf G) (hlv : gloadValue G)
    (himg : G.gxImg = img) (x : Nat) (aq : Bool) (base : Int) (ts : List Nat) (vs : List (BitVec 8))
    (hl : gxLbl G (hd w x) = some (LLoad aq base ts vs))
    (hby : ∀ j t v, ts[j]? = some t → vs[j]? = some v →
      SbCand.fwdByte (w.σ.sb x) (accAddr base j) = some v ∨
      (SbCand.fwdByte (w.σ.sb x) (accAddr base j) = none ∧ t ≤ (wrW w).length ∧
        DomAt G w x aq (accAddr base j) t)) :
    SbCand.rdOkSb w.σ.ms.msImg w.σ.ms.msLog (w.σ.ms.msWs x) aq base ts vs (w.σ.sb x) := by
  refine ⟨lblShape G hwf _ _ hl, fun j t v htj hvj => ?_⟩
  rcases hby j t v htj hvj with h | ⟨hf, hland, hdom⟩
  · exact .inl h
  · refine .inr ⟨hf, ?_⟩
    have hrd : greadsByte G (hd w x) (accAddr base j) t v := ⟨_, base, ts, vs, j, hl, rfl, htj, hvj, rfl⟩
    obtain ⟨hv, hnw⟩ := staleStep img G X w hI hpf hW hwf.1 hlv himg _ _ t v hrd hland _ hdom
    rw [hI.img]
    exact ⟨hv, by rw [hv]; rfl, hnw⟩

end Dom

/-! # 4. Why S-R presupposes S-P: a per-byte landing order can strand a stale read

`dm`: A `sd a = 1`; B `sd b = 1`; C `r1 := b` (1), `fence r,r`, `r2 := a` (0, the image).  GF gmo
`W_b < r1 < r2 < W_a` (`r2` from-reads `W_a`).  Without `readersDone` a per-byte gate may land `W_a`
FIRST (different bytes); then `r1`'s source sits at member position 2, the fence lifts C's read view to
2, and `r2` can read the image at NO timestamp — the walk is stranded.  Landing in GF's write order
(S-P) the same stale read is readable. -/

def dmProg : List (List Lbl) :=
  [[LStore false 0 [b1] .WCplain], [LStore false 1 [b1] .WCplain],
   [LLoad false 1 [1] [b1], LFence true false true false, LLoad false 0 [0] [b0]]]

def dmGmo : List Geid := [(1, 0), (2, 0), (2, 2), (0, 0)]

def dm : Gdexec := AxLitmus.mkgd dmProg dmGmo []

theorem dmCat : rvwmoCatConsistent dm := catConsistentBSound _ (by decide +kernel)

/-- The S-P + S-R member: both stores land first (GF's write order), then C reads `r1` at the top and
`r2` STALE at the image. -/
def oDm : List (Geid × List Geid) :=
  [((1, 0), [(1, 0)]), ((0, 0), [(0, 0)]), ((2, 0), []), ((2, 1), []), ((2, 2), [])]

def stepsDm : List (Estep × List Nat) := SbCandLit.toSteps dm.gdG oDm

theorem dmRunB : runOkBS (SbCandLit.σ0 dm.gdG.gxImg) stepsDm = true := by decide +kernel

theorem dmMemberSR (pol : SbPol) :
    SbCand.execWfP pol ⟨SbCand.statesOf (SbCandLit.σ0 dm.gdG.gxImg) stepsDm, stepsDm.map Prod.fst⟩ :=
  runOfBS pol _ _ (SbCandLit.σ0Init _) dmRunB

/-- The per-byte order: `W_a` lands first, so `r1` reads `W_b` at member position 2. -/
def stepsDmBad : List (Estep × List Nat) :=
  [(⟨0, LStore false 0 [b1] .WCplain⟩, [0]), (⟨1, LStore false 1 [b1] .WCplain⟩, [1]),
   (⟨2, LLoad false 1 [2] [b1]⟩, []), (⟨2, LFence true false true false⟩, [])]

theorem dmBadRunB : runOkBS (SbCandLit.σ0 dm.gdG.gxImg) stepsDmBad = true := by decide +kernel

/-- **STRANDED**: at the end of the per-byte prefix, C's `r2` reads the image's `0` at no timestamp
(the only `0` at byte `a` is the image, timestamp 0, and C's view is 2). -/
theorem dmStranded :
    ((SbCand.statesOf (SbCandLit.σ0 dm.gdG.gxImg) stepsDmBad).getLast?.map (fun σ =>
      (List.range 3).all (fun t => !staleRdB σ.ms.msImg σ.ms.msLog (σ.ms.msWs 2) false (σ.sb 2) 0 [t]
        [b0]))) = some true := by
  decide +kernel

end SpikeSR

end Weak
