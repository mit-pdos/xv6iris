/-
**THE NI FILING LEDGER** (NI M2-W2c; design of record
`claude-notes/projects/noninterference.md`, "M2-W2 design (2026-10-02)" §1,
rulings O1/O2/O6): every user ENTER in the machine's history is FILED exactly
once, either as a ROUND (the exit it resumes, the cause, the trapped and the
resumed keys, lawful by `roundOkKeys`, same pid) or as an ORIGIN (an
incarnation's first key).

* §1 `tfGprs`, the trapframe's `x1..x31` in the order a boundary event names
  them (`MachCSL.gprList`, `x_k` at trapframe word `4 + k`), and the bridge
  `gprList_tfResumeGpr0`: the file userret rebuilds IS `tfGprs`.
* §2 `exitFits` / `enterFits`: an event read at a key; `niFit`, the meaning
  of an entry's evidence (`MachFixedGS.uFit`'s Xv6 reading, ruling O2).
* §3 `NiEntry`, `niOk h F` (every filing is valid in `h`, every enter in `h`
  is filed once), `niR h := ⌜∃ F, niOk h F⌝` (ruling O6), timeless; it steps
  blind on non-enter events (`niR_snoc`) and files an enter (`niR_enter`).
* §4 `NiFitIs`: the Prop class that tells the kernel's proofs (generic in the
  `MachGS` instance) that the record's `uFit` accepts `niFit`'s evidence.

**F3: `satp` is not an identity.**  A root is freed at exit / kill / a
successful exec and a later `kalloc` can hand the page to a new process, so
traces are NOT read per `satp`: they are read per FILING (O1: incarnations by
(era, pid), read off the filings by W4).

**F4: origins are free until W2d.**  `niFit none e` is "some key fits these
registers", which is always satisfiable: a run could file a round's resume as
a fresh origin and hide the round's law.  W2d's ledger-minted one-shot claims
close this; W4 may develop on this core but publishes after W2d (O4).

## Deviations from the design text

1. **`NiFitIs` is an implication, not an equation** (design O2: `eq :
   MachFixedGS.uFit = niFit`).  The kernel only ever PRODUCES `uFit` evidence
   from `niFit` evidence, so `fit : niFit ox e → uFit ox e` is all its proofs
   use; and the equation would force the system record (`xv6FixedGS`, named
   in `xv6PowerAdequacy`'s statement) to carry `niFit`, pulling this file and
   its closure (`UhistDefs`, `UexecRound`, ...) into that root's trusted base.
   The system theorems keep the blind record (`uFit := True`, instance by
   `trivial`); W4's theorem instantiates a record at `uFit := niFit` (instance
   by `id`).
2. `niOk`'s per-entry clause is the named `niEntryOk` rather than an inline
   `match` (same meaning; the lemmas case on it).

PURE but for `niR` (a pure proposition in `IProp`) and the class.
-/
import Xv6.UhistDefs

namespace Xv6

open Iris Iris.BI Iris.ProofMode Std MachCSL

/-! ## §1 The trapframe's GPRs -/

/-- **The trapframe's `x1..x31`** (words `5..35`), in the order a boundary
event names a register file (`MachCSL.gprList`): `x_k` is word `4 + k`. -/
def tfGprs (tf : List (BitVec 64)) : List (BitVec 64) := (List.range 31).map (fun k => tfW tf (5 + k))

/-- **The bridge**: the register file userret rebuilds (`tfResumeGpr0`, the
`sret`'s file off `x0`) reads, as an event's GPR list, the trapframe's
`tfGprs`. -/
theorem gprList_tfResumeGpr0 (ws : List (BitVec 64)) : gprList (tfResumeGpr0 ws) = tfGprs ws := by
  unfold gprList gprIdxs tfGprs tfResumeGpr0 tfResumeGpr
  simp [List.range_succ]

/-! ## §2 Events read at keys -/

/-- An exit event is the trap of key `W` at cause `sc`: the trapped pc and
registers are the key's trapframe's. -/
def exitFits (x : Obs) (sc : BitVec 64) (W : Uvis) : Prop :=
  ∃ (cpu : CPU) (s : BitVec 64), x = .uExit cpu s sc (tfW W.tf tfEpcIdx) (tfGprs W.tf)

/-- An enter event resumes key `W`: its registers are the key's trapframe's,
and it lands at the key's resume pc. -/
def enterFits (e : Obs) (W : Uvis) : Prop :=
  ∃ (cpu : CPU) (s ep : BitVec 64), e = .uEnter cpu s ep (tfGprs W.tf) ∧ retPc ep = tfResumePc W.tf

/-- **The evidence's meaning** (the Xv6 reading of `MachFixedGS.uFit`): an
origin is any key the enter fits (W2d tightens it, F4); a round cites the
exit it resumes, read at the trapped key `W`, and the resumed key `W'` is
lawful from it and keeps its pid. -/
def niFit : Option (Nat × Obs) → Obs → Prop
  | none, e => ∃ W0, enterFits e W0
  | some (_, x), e => ∃ (sc : BitVec 64) (W W' : Uvis),
      exitFits x sc W ∧ enterFits e W' ∧ roundOkKeys sc W W' ∧ W'.pid = W.pid

/-! ## §3 The filing -/

/-- One filing: an origin at position `j` with the incarnation's first key,
or a round from the exit at `i` to the enter at `j`. -/
inductive NiEntry where
  | origin (j : Nat) (W0 : Uvis)
  | round (i j : Nat) (sc : BitVec 64) (W W' : Uvis)

/-- The enter a filing files. -/
def NiEntry.j : NiEntry → Nat
  | .origin j _ => j
  | .round _ j _ _ _ => j

/-- One filing is valid in history `h`. -/
def niEntryOk (h : List Obs) : NiEntry → Prop
  | .origin j W0 => ∃ e, h[j]? = some e ∧ enterFits e W0
  | .round i j sc W W' => i < j ∧ (∃ x, h[i]? = some x ∧ exitFits x sc W) ∧
      (∃ e, h[j]? = some e ∧ enterFits e W') ∧ roundOkKeys sc W W' ∧ W'.pid = W.pid

/-- **THE LEDGER'S FACT**: every filing is valid, and every enter in `h` is
filed exactly once (`∃!`, spelled out). -/
def niOk (h : List Obs) (F : List NiEntry) : Prop :=
  (∀ f ∈ F, niEntryOk h f) ∧
  (∀ (j : Nat) (e : Obs), h[j]? = some e → isUEnter e = true →
    ∃ f, (f ∈ F ∧ f.j = j) ∧ ∀ f', f' ∈ F → f'.j = j → f' = f)

/-- **The ledger** (ruling O6: the filing is part of the run's witness). -/
def niR {GF : BundledGFunctors} (h : List Obs) : IProp GF := iprop(⌜∃ F, niOk h F⌝)

instance niR_timeless {GF : BundledGFunctors} (h : List Obs) : Timeless (niR (GF := GF) h) := by
  unfold niR; infer_instance

instance niR_persistent {GF : BundledGFunctors} (h : List Obs) : Persistent (niR (GF := GF) h) := by
  unfold niR; infer_instance

/-- A valid filing names a position of the history. -/
theorem niEntryOk_lt {h : List Obs} {f : NiEntry} (hf : niEntryOk h f) : f.j < h.length := by
  cases f with
  | origin j W0 =>
    obtain ⟨e, he, -⟩ := hf
    exact (List.getElem?_eq_some_iff.mp he).1
  | round i j sc W W' =>
    obtain ⟨-, -, ⟨e, he, -⟩, -⟩ := hf
    exact (List.getElem?_eq_some_iff.mp he).1

/-- A valid filing stays valid as the history grows. -/
theorem niEntryOk_snoc {h : List Obs} {f : NiEntry} (e : Obs) (hf : niEntryOk h f) :
    niEntryOk (h ++ [e]) f := by
  have hlt := niEntryOk_lt hf
  cases f with
  | origin j W0 =>
    have hlt' : j < h.length := hlt
    obtain ⟨e', he', hfit⟩ := hf
    exact ⟨e', by rw [List.getElem?_append_left hlt']; exact he', hfit⟩
  | round i j sc W W' =>
    obtain ⟨hij, ⟨x, hx, hxf⟩, ⟨e', he', hef⟩, hr, hp⟩ := hf
    have hlt' : j < h.length := hlt
    exact ⟨hij, ⟨x, by rw [List.getElem?_append_left (by omega)]; exact hx, hxf⟩,
      ⟨e', by rw [List.getElem?_append_left hlt']; exact he', hef⟩, hr, hp⟩

/-- The new last position reads the appended event. -/
theorem niLast {h : List Obs} {e e' : Obs} {j : Nat} (hj : (h ++ [e])[j]? = some e')
    (hle : h.length ≤ j) : j = h.length ∧ e' = e := by
  rw [List.getElem?_append_right hle] at hj
  have h1 := (List.getElem?_eq_some_iff.mp hj).1
  simp only [List.length_singleton] at h1
  have hj' : j = h.length := by omega
  subst hj'
  simp at hj
  exact ⟨rfl, hj.symm⟩

/-- The empty history, filed by nothing. -/
theorem niOk_nil : niOk [] [] :=
  ⟨fun _ hf => absurd hf List.not_mem_nil, fun j e hj _ => by simp at hj⟩

/-- **A non-enter event steps the ledger blind** (exits, power, UART). -/
theorem niOk_snoc {h : List Obs} {F : List NiEntry} {e : Obs} (he : isUEnter e = false)
    (hF : niOk h F) : niOk (h ++ [e]) F := by
  obtain ⟨hv, hc⟩ := hF
  refine ⟨fun f hf => niEntryOk_snoc e (hv f hf), fun j e' hj hu => ?_⟩
  by_cases hlt : j < h.length
  · rw [List.getElem?_append_left hlt] at hj
    exact hc j e' hj hu
  · obtain ⟨-, rfl⟩ := niLast hj (by omega)
    rw [he] at hu
    cases hu

/-- **An enter is filed** at its evidence: a round citing the exit at `i`
(which the history holds there), or an origin. -/
theorem niOk_enter {h : List Obs} {F : List NiEntry} {e : Obs} {ox : Option (Nat × Obs)}
    (_he : isUEnter e = true) (hfit : niFit ox e)
    (hrc : ∀ i x, ox = some (i, x) → i < h.length ∧ h[i]? = some x)
    (hF : niOk h F) : ∃ F', niOk (h ++ [e]) F' := by
  obtain ⟨hv, hc⟩ := hF
  -- the new filing, at position `h.length`
  obtain ⟨fn, hfnj, hfn⟩ : ∃ fn : NiEntry, fn.j = h.length ∧ niEntryOk (h ++ [e]) fn := by
    have hlast : (h ++ [e])[h.length]? = some e := by simp
    cases ox with
    | none =>
      obtain ⟨W0, hW0⟩ := hfit
      exact ⟨.origin h.length W0, rfl, e, hlast, hW0⟩
    | some ix =>
      obtain ⟨i, x⟩ := ix
      obtain ⟨sc, W, W', hx, hen, hr, hp⟩ := hfit
      obtain ⟨hi, hxi⟩ := hrc i x rfl
      exact ⟨.round i h.length sc W W', rfl, hi,
        ⟨x, by rw [List.getElem?_append_left hi]; exact hxi, hx⟩, ⟨e, hlast, hen⟩, hr, hp⟩
  refine ⟨F ++ [fn], fun f hf => ?_, fun j e' hj hu => ?_⟩
  · rcases List.mem_append.mp hf with hf | hf
    · exact niEntryOk_snoc e (hv f hf)
    · rw [List.mem_singleton.mp hf]; exact hfn
  · by_cases hlt : j < h.length
    · rw [List.getElem?_append_left hlt] at hj
      obtain ⟨f, ⟨hfF, hfj⟩, hu1⟩ := hc j e' hj hu
      refine ⟨f, ⟨List.mem_append_left _ hfF, hfj⟩, fun y hyF hyj => ?_⟩
      rcases List.mem_append.mp hyF with hyF | hyF
      · exact hu1 y hyF hyj
      · rw [List.mem_singleton.mp hyF] at hyj; omega
    · obtain ⟨rfl, -⟩ := niLast hj (by omega)
      refine ⟨fn, ⟨List.mem_append_right _ (List.mem_singleton.mpr rfl), hfnj⟩, fun y hyF hyj => ?_⟩
      rcases List.mem_append.mp hyF with hyF | hyF
      · have := niEntryOk_lt (hv y hyF); omega
      · exact List.mem_singleton.mp hyF

section
variable {GF : BundledGFunctors}

/-- The ledger at the empty history. -/
theorem niR_nil : ⊢@{IProp GF} niR [] := by
  unfold niR
  ipureintro
  exact ⟨[], niOk_nil⟩

/-- **`niR_snoc`**: exits, power and UART events step the ledger blind. -/
theorem niR_snoc (h : List Obs) (e : Obs) (he : isUEnter e = false) :
    niR (GF := GF) h ⊢ niR (h ++ [e]) := by
  unfold niR
  iintro %⟨F, hF⟩
  ipureintro
  exact ⟨F, niOk_snoc he hF⟩

/-- **`niR_enter`, THE FILING**: an enter with its evidence (`niFit`) and the
cited receipt's reading. -/
theorem niR_enter (h : List Obs) (e : Obs) (ox : Option (Nat × Obs)) (he : isUEnter e = true)
    (hfit : niFit ox e) (hrc : ∀ i x, ox = some (i, x) → i < h.length ∧ h[i]? = some x) :
    niR (GF := GF) h ⊢ niR (h ++ [e]) := by
  unfold niR
  iintro %⟨F, hF⟩
  ipureintro
  exact niOk_enter he hfit hrc hF

end

/-! ## §4 The kernel's carrier (ruling O2) -/

section
variable {hlc : HasLC}

/-- **The record accepts `niFit`'s evidence** (ruling O2's Prop class, as
`SchedCtx.ClaimIs`; deviation 1: an implication).  The boot instantiates it
beside `ClaimIs` (`SystemBootEra`); the closed trap loop's cone takes it. -/
class NiFitIs (GF : BundledGFunctors) [MachGS hlc GF] : Prop where
  fit : ∀ (ox : Option (Nat × Obs)) (e : Obs), niFit ox e → MachFixedGS.uFit (hlc := hlc) (GF := GF) ox e

theorem uFit_of_niFit {GF : BundledGFunctors} [MachGS hlc GF] [NiFitIs (hlc := hlc) GF]
    (ox : Option (Nat × Obs)) (e : Obs) (h : niFit ox e) : MachFixedGS.uFit (hlc := hlc) (GF := GF) ox e :=
  NiFitIs.fit ox e h

end

end Xv6
