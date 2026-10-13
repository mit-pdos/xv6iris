/-
Weak: **constraint A — computable checkers for the PTW model (H5') and the CONCRETE
WITNESSES** (AxSL tier).

Rocq: `iris/AxPtProt2.v` @ xxvzwolszwmp.

The Rocq header, in substance.  Over `AxPtProt`'s `Gptw`.  PURE.  Verdicts by
`decide +kernel` (Rocq: `vm_compute`).

§1  list-specified PTW graphs `mkptw GD fl sfl` (walker attribution `fl`, sfence markers
    `sfl`) and boolean checkers for `ptwWf` and the H5' clauses, SOUND against the Prop
    definitions, given the FULL cat model (`catConsistentB`) of the graph (used only for the
    ob ⊆ gmo step of the sfence check and for the explicit part).
§2  `GPad` — ONE hart: install store of an A/D-CLEAR leaf (xv6-faithful, no preset A/D),
    `sfence.vma`, walker leaf read, the Svadu A-bit write-back RMW (`update_PTE_Bits` of the
    REAL Sail model), and the data load at the translated address.  `gAdSound`: the whole
    model holds, the discipline holds BY THE ABSORPTION THEOREM (not by inspection), both
    walker reads are pinned to the class, the write-back is a variant, the translation is
    the install's page, and the agreement invariant holds at the load.
§3  `GPrace` — TWO harts: hart 1 remaps the leaf (canon-changing store, gmo-before hart 0's
    access), hart 0 has NO sfence and its walk reads the stale word.  The model (incl. H5')
    holds, and the agreement invariant FAILS (`raceBreaksAgree`).
§4  `GPsf` / `GPsfok` — H5' IS A NEW HARDWARE CLAUSE: hart 1 remaps then publishes a flag
    behind `fence w,w`; hart 0 reads the flag, executes `sfence.vma`, walks.  If the walk
    reads the STALE word the graph is riscv.cat-CONSISTENT (`gsfCat`: riscv.cat does not
    order PTW accesses) but VIOLATES H5'.2 (`gsfNotH5`); with the walk reading the new word
    (`GPsfok`) the full model holds and the agreement invariant holds (`gsfokSound`).

Stage C (D1 reversed: fetches are not graph events): graph-level; no access kinds, no
fetch events (every `LLoad` row item is a data or walker load; the sfence is the
`LFence false false false false` marker).  Nothing moves.

**Deviations from Rocq.**

1. NAMES: lowerCamelCase (map below).  Duplicated Rocq names (`w0`, `cover_b`,
   `notes/weak-port-dupnames.json`) are FILE-QUALIFIED: `AxPtProt2.w0`, `AxPtProt2.coverB`.
   `pa_of` is file-qualified too (`AxPtProt2.paOf`) because `MachCSL.paOf` exists (Lean-side
   clash under `open MachCSL`).
2. VOCABULARY: as `AxGraphDec` deviation 2 (`forallb`/`existsb` ↦ `List.all`/`List.any`,
   `bool_decide` ↦ `decide`, `Nat.leb`/`Nat.ltb` ↦ `decide (· ≤ ·)`/`decide (· < ·)`,
   `seq 0 8` ↦ `List.range' 0 8`); `mword_of_int (Z.lor (Z.shiftl p 10) f)` ↦
   `BitVec.ofNat 64 ((p <<< 10) ||| f)` (the values are non-negative); `Z_to_bv 8 k` ↦ the
   literal `k`; `Z.to_nat` ↦ `Int.toNat`; `List.repeat` ↦ `List.replicate`; `Load Data` ↦
   `.Load .Data`; `bv_unsigned` ↦ `BitVec.toNat` (cast to `Int` in `paOf`).
3. `vmr` (`vm_compute; reflexivity`) ↦ `decide +kernel` throughout.
4. Proof-only: the "walker read (0,2) writes no byte" case of `gAdSound` is closed by
   `gwrBytes … = []` (definitional) instead of Rocq's eight-way case split on `j`;
   `ptwModelBSound` reuses `ptwWfBSound` for its first conjunct (Rocq repeats the proof).
5. Lean-only helper (file-qualified): `AxPtProt2.inWinBAcc` (`inWinB pa (accAddr pa j)`
   for `j < 8`; Rocq inlines it in three proofs).  Closed `gwalk` goals are
   `unfold gwalk; decide +kernel` (`gwalk` is a `Prop` without a `Decidable` instance).
6. The `Print Assumptions` lines have no Lean twin (the lint's axiom check covers them).

**Rocq → Lean name map.**  `assoc`; `assoc_in` ↦ `assocIn`; `mkptw`; `sf_lbl_b` ↦
`sfLblB`; `sf_lbl_b_spec` ↦ `sfLblBSpec`; `ptw_wf_b` ↦ `ptwWfB`; `cover_b` ↦
`AxPtProt2.coverB`; `h5_sfence_b` ↦ `h5SfenceB`; `h5_ad_atomic_b` ↦ `h5AdAtomicB`;
`h5_ad_before_b` ↦ `h5AdBeforeB`; `h5_sfence_ad_b` ↦ `h5SfenceAdB`; `ptw_model_b` ↦
`ptwModelB`; `gwalk_mk` ↦ `gwalkMk`; `gsfence_mk` ↦ `gsfenceMk`; `ptw_model_b_sound` ↦
`ptwModelBSound`; `ptw_wf_b_sound` ↦ `ptwWfBSound`; `gwrites_word_b` ↦ `gwritesWordB`;
`gwrites_word_b_sound` ↦ `gwritesWordBSound`; `reads_word_after_b` ↦ `readsWordAfterB`;
`reads_word_after_b_sound` ↦ `readsWordAfterBSound`; `in_win_b` ↦ `inWinB`;
`no_kernel_writes_b` ↦ `noKernelWritesB`; `no_kernel_writes_b_sound` ↦
`noKernelWritesBSound`; `wb8`; `imgz`; `w0` ↦ `AxPtProt2.w0`; `w1`; `w1_update` ↦
`w1Update`; `w1_ne_w0` ↦ `w1NeW0`; `pa_of` ↦ `AxPtProt2.paOf`; `pa_of_w0` ↦ `paOfW0`;
`ts8`; `gad`; `GPad`; `gad_model` ↦ `gadModel`; `gad_cat` ↦ `gadCat`; `g_ad_sound` ↦
`gAdSound`; `no_walker_writes_b` ↦ `noWalkerWritesB`; `no_walker_writes_b_sound` ↦
`noWalkerWritesBSound`; `latest_b` ↦ `latestB`; `latest_b_sound` ↦ `latestBSound`;
`w_old` ↦ `wOld`; `w_new` ↦ `wNew`; `w_old_new_ppn` ↦ `wOldNewPpn`; `w_old_new_canon` ↦
`wOldNewCanon`; `pa_of_w_new` ↦ `paOfWNew`; `img_old` ↦ `imgOld`; `grace`; `GPrace`;
`race_breaks_agree` ↦ `raceBreaksAgree`; `B1`; `gsf_rows` ↦ `gsfRows`; `gsf`; `GPsf`;
`gsfok`; `GPsfok`; `gsf_cover` ↦ `gsfCover`; `gsf_cat` ↦ `gsfCat`; `gsf_not_h5` ↦
`gsfNotH5`; `gsf_explicit` ↦ `gsfExplicit`; `gsfok_sound` ↦ `gsfokSound`.

**Dropped:** nothing (the `Ltac`s `vmr`/`fa` are tactics, not declarations).
-/
import Weak.AxPtProt
import Weak.AxGraphDec

namespace Weak

open MachCSL MachCSL.Stdpp
open Lbl
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D LeanRV64D.Functions

/-! # 1. List-specified PTW graphs and checkers -/

def assoc : List (Geid × Geid) → Geid → Option Geid
  | [], _ => none
  | (x, e) :: l', u => if x = u then some e else assoc l' u

theorem assocIn (l : List (Geid × Geid)) (u e : Geid) : assoc l u = some e → (u, e) ∈ l := by
  induction l with
  | nil => intro h; cases h
  | cons p l ih =>
    obtain ⟨x, e'⟩ := p
    simp only [assoc]
    split
    · rename_i hx
      intro h
      cases h
      subst hx
      simp
    · intro h
      exact List.mem_cons_of_mem _ (ih h)

def mkptw (GD : Gdexec) (fl : List (Geid × Geid)) (sfl : List Geid) : Gptw :=
  ⟨GD, assoc fl, fun f => decide (f ∈ sfl)⟩

def sfLblB (G : Gexec) (f : Geid) : Bool :=
  match gxLbl G f with
  | some (LFence false false false false) => true
  | _ => false

theorem sfLblBSpec (G : Gexec) (f : Geid) :
    sfLblB G f = true → gxLbl G f = some (LFence false false false false) := by
  unfold sfLblB
  split
  · rename_i h
    exact fun _ => h
  · intro h
    cases h

section checkers

variable (GD : Gdexec) (fl : List (Geid × Geid)) (sfl : List Geid)

def ptwWfB : Bool :=
  fl.all (fun p => gpoB GD.gdG p.1 p.2 && !(isSomeB (assoc fl p.2))) &&
  fl.all (fun p => !(glblB GD.gdG p.1 lbIsW) || glblB GD.gdG p.1 lbIsR) &&
  sfl.all (fun f => sfLblB GD.gdG f)

def AxPtProt2.coverB (s f : Geid) : Bool :=
  gpoB GD.gdG s f || (gevents GD.gdG).any (fun e => gpoB GD.gdG e f && gmoLtB GD.gdG s e)

def h5SfenceB : Bool :=
  sfl.all (fun f =>
    fl.all (fun p =>
      (grdBytes GD.gdG p.1).all (fun x : (Int × Nat) × BitVec 8 =>
        (gevents GD.gdG).all (fun s =>
          (gwrBytes GD.gdG s).all (fun y : Int × BitVec 8 =>
            !(gpoB GD.gdG f p.1 && decide (y.1 = x.1.1) && AxPtProt2.coverB GD s f)
            || decide (gwix GD.gdG s ≤ x.1.2))))))

def h5AdAtomicB : Bool :=
  fl.all (fun p => !(glblB GD.gdG p.1 lbIsW) ||
    (grdBytes GD.gdG p.1).all (fun x : (Int × Nat) × BitVec 8 =>
      decide (x.1.2 < gwix GD.gdG p.1)))

def h5AdBeforeB : Bool :=
  fl.all (fun p => !(glblB GD.gdG p.1 lbIsW) || gmoLtB GD.gdG p.1 p.2)

def h5SfenceAdB : Bool :=
  sfl.all (fun f => fl.all (fun p => (gevents GD.gdG).all (fun s =>
    !(glblB GD.gdG p.1 lbIsW && gpoB GD.gdG p.1 f && gpoB GD.gdG f s &&
      !(isSomeB (assoc fl s)) && glblB GD.gdG s lbIsW)
    || gmoLtB GD.gdG p.1 s)))

def ptwModelB : Bool :=
  catConsistentB GD && ptwWfB GD fl sfl && h5SfenceB GD fl sfl && h5AdAtomicB GD fl &&
  h5AdBeforeB GD fl && h5SfenceAdB GD fl sfl

theorem gwalkMk (u : Geid) :
    gwalk (mkptw GD fl sfl) u → ∃ e, (u, e) ∈ fl ∧ assoc fl u = some e := by
  intro hu
  cases h : assoc fl u with
  | none =>
    have hu' : (assoc fl u).isSome = true := hu
    rw [h] at hu'
    cases hu'
  | some e => exact ⟨e, assocIn _ _ _ h, rfl⟩

theorem gsfenceMk (f : Geid) : gsfence (mkptw GD fl sfl) f → f ∈ sfl := by
  rintro ⟨h, _⟩
  have h' : decide (f ∈ sfl) = true := h
  exact of_decide_eq_true h'

theorem ptwWfBSound : ptwWfB GD fl sfl = true → ptwWf (mkptw GD fl sfl) := by
  intro hwf
  unfold ptwWfB at hwf
  rw [Bool.and_eq_true, Bool.and_eq_true] at hwf
  obtain ⟨⟨hw1, hw2⟩, hw3⟩ := hwf
  rw [forallbForallTrue] at hw1 hw2 hw3
  refine ⟨?_, ?_, ?_⟩
  · intro u e he
    have h := hw1 _ (assocIn _ _ _ he)
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
    obtain ⟨h1, h2⟩ := h
    refine ⟨(gpoBSpec _ _ _).1 h1, ?_⟩
    show assoc fl e = none
    cases hc : assoc fl e with
    | none => rfl
    | some _ =>
      rw [hc] at h2
      cases h2
  · intro u hu hwu
    obtain ⟨e, hin, _⟩ := gwalkMk GD fl sfl u hu
    have h := hw2 _ hin
    simp only [Bool.or_eq_true, Bool.not_eq_true'] at h
    have hw := (glblBSpec GD.gdG u lbIsW).2 hwu
    rcases h with h | h
    · rw [h] at hw
      cases hw
    · exact (glblBSpec _ _ _).1 h
  · intro f hf
    have hf' : decide (f ∈ sfl) = true := hf
    exact sfLblBSpec _ _ (hw3 f (of_decide_eq_true hf'))

theorem ptwModelBSound : ptwModelB GD fl sfl = true → ptwModel (mkptw GD fl sfl) := by
  intro h
  unfold ptwModelB at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨hcat, hwf⟩, hsf⟩, hat⟩, hbef⟩, hsfad⟩ := h
  have hc := catConsistentBSound GD hcat
  unfold h5SfenceB at hsf
  unfold h5AdAtomicB at hat
  unfold h5AdBeforeB at hbef
  unfold h5SfenceAdB at hsfad
  refine ⟨ptwWfBSound GD fl sfl hwf, ptwExplicitOfCat _ hc,
    h5WalkValueOfCat _ hc, ?_, ?_, ?_, ?_⟩
  · -- H5'.2
    intro f r a t v s v' hf hr hfr hrd hwr hcov
    have hfin := gsfenceMk GD fl sfl f hf
    obtain ⟨e, hin, _⟩ := gwalkMk GD fl sfl r hr
    have H := (forallbForallTrue _ _).1 hsf f hfin
    have H := (forallbForallTrue _ _).1 H _ hin
    have H := (forallbForallTrue _ _).1 H ((a, t), v) ((greadsByteBytes _ _ _ _ _).1 hrd)
    have H := (forallbForallTrue _ _).1 H s (gwritesByteGevents _ _ _ _ hwr)
    have H := (forallbForallTrue _ _).1 H (a, v') ((gwritesByteBytes _ _ _ _).1 hwr)
    simp only [Bool.or_eq_true, Bool.not_eq_true'] at H
    rcases H with H | H
    · exfalso
      have hc1 : gpoB GD.gdG f r = true := (gpoBSpec _ _ _).2 hfr
      have hc3 : AxPtProt2.coverB GD s f = true := by
        unfold AxPtProt2.coverB
        rw [Bool.or_eq_true]
        rcases hcov with hp | ⟨e', hp, hob⟩
        · exact Or.inl ((gpoBSpec _ _ _).2 hp)
        · refine Or.inr ((existsbExistsTrue _ _).2 ⟨e', (gpoGevents _ _ _ hp).1, ?_⟩)
          rw [Bool.and_eq_true]
          exact ⟨(gpoBSpec _ _ _).2 hp,
            (gmoLtBSpec _ _ _).2 (obCatSubGmo GD s e' hc (gobExplCat _ _ _ hob))⟩
      simp [hc1, hc3] at H
    · exact of_decide_eq_true H
  · -- H5'.3
    intro u a t v hu hwu hrd
    obtain ⟨e, hin, _⟩ := gwalkMk GD fl sfl u hu
    have H := (forallbForallTrue _ _).1 hat _ hin
    simp only [Bool.or_eq_true, Bool.not_eq_true'] at H
    rcases H with H | H
    · have hw := (glblBSpec GD.gdG u lbIsW).2 hwu
      rw [H] at hw
      cases hw
    · have H := (forallbForallTrue _ _).1 H ((a, t), v) ((greadsByteBytes _ _ _ _ _).1 hrd)
      exact of_decide_eq_true H
  · -- H5'.4
    intro u e he hwu
    have H := (forallbForallTrue _ _).1 hbef _ (assocIn _ _ _ he)
    simp only [Bool.or_eq_true, Bool.not_eq_true'] at H
    rcases H with H | H
    · have hw := (glblBSpec GD.gdG u lbIsW).2 hwu
      rw [H] at hw
      cases hw
    · exact (gmoLtBSpec _ _ _).1 H
  · -- H5'.5
    intro u f s hf hu hwu huf hfs hs hws
    have hfin := gsfenceMk GD fl sfl f hf
    obtain ⟨e, hin, _⟩ := gwalkMk GD fl sfl u hu
    have H := (forallbForallTrue _ _).1 hsfad f hfin
    have H := (forallbForallTrue _ _).1 H _ hin
    have H := (forallbForallTrue _ _).1 H s (gpoGevents _ _ _ hfs).2
    simp only [Bool.or_eq_true, Bool.not_eq_true'] at H
    rcases H with H | H
    · exfalso
      have h1 := (glblBSpec GD.gdG u lbIsW).2 hwu
      have h2 := (glblBSpec GD.gdG s lbIsW).2 hws
      have h3 := (gpoBSpec GD.gdG u f).2 huf
      have h4 := (gpoBSpec GD.gdG f s).2 hfs
      have h5 : assoc fl s = none := hs
      simp [h1, h2, h3, h4, h5, isSomeB] at H
    · exact (gmoLtBSpec _ _ _).1 H

end checkers

/-- Word-level checkers. -/
def gwritesWordB (G : Gexec) (e : Geid) (pa : Int) (x : BitVec 64) : Bool :=
  (List.range' 0 8).all (fun j => gwbB G e (accAddr pa j) (nthByte (n := 8) x j))

theorem gwritesWordBSound (G : Gexec) (e : Geid) (pa : Int) (x : BitVec 64) :
    gwritesWordB G e pa x = true → gwritesWord G e pa x := by
  intro H j hj
  exact (gwbBSpec _ _ _ _).1
    ((forallbForallTrue _ _).1 H j (List.mem_range'_1.2 ⟨Nat.zero_le _, by omega⟩))

def readsWordAfterB (G : Gexec) (e : Geid) (pa : Int) (x : BitVec 64) (T0 : Nat) : Bool :=
  (List.range' 0 8).all (fun j =>
    (grdBytes G e).all (fun y : (Int × Nat) × BitVec 8 =>
      !(decide (y.1.1 = accAddr pa j)) ||
      (decide (T0 ≤ y.1.2) && bvEqb y.2 (nthByte (n := 8) x j))) &&
    (grdBytes G e).any (fun y : (Int × Nat) × BitVec 8 => decide (y.1.1 = accAddr pa j)))

/-- Every byte of the window is read, with value `x`'s byte, at-or-after `T0`. -/
theorem readsWordAfterBSound (G : Gexec) (e : Geid) (pa : Int) (x : BitVec 64) (T0 : Nat) :
    readsWordAfterB G e pa x T0 = true →
    greadsWord G e pa x ∧ readsAfter G e pa T0 ∧
    (∀ x', greadsWord G e pa x' → x' = x) := by
  intro H
  unfold readsWordAfterB at H
  have hj : ∀ j, j < 8 →
      (∀ t v, greadsByte G e (accAddr pa j) t v → T0 ≤ t ∧ v = nthByte (n := 8) x j) ∧
      ∃ t v, greadsByte G e (accAddr pa j) t v := by
    intro j hj
    have H := (forallbForallTrue _ _).1 H j (List.mem_range'_1.2 ⟨Nat.zero_le _, by omega⟩)
    rw [Bool.and_eq_true] at H
    obtain ⟨H1, H2⟩ := H
    refine ⟨fun t v hr => ?_, ?_⟩
    · have H1 := (forallbForallTrue _ _).1 H1 _ ((greadsByteBytes _ _ _ _ _).1 hr)
      simp only [Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_true, decide_eq_true_iff,
        decide_eq_false_iff_not] at H1
      rcases H1 with H1 | H1
      · exact absurd trivial H1
      · exact ⟨H1.1, (bvEqbSpec _ _).1 H1.2⟩
    · obtain ⟨⟨⟨a, t⟩, v⟩, hin, ha⟩ := (existsbExistsTrue _ _).1 H2
      have ha' : a = accAddr pa j := of_decide_eq_true ha
      subst ha'
      exact ⟨t, v, (greadsByteBytes _ _ _ _ _).2 hin⟩
  refine ⟨fun j hjl => ?_, fun j t v hjl hr => ((hj j hjl).1 t v hr).1, fun x' hx' => ?_⟩
  · obtain ⟨t, v, hr⟩ := (hj j hjl).2
    obtain ⟨_, rfl⟩ := (hj j hjl).1 t v hr
    exact ⟨t, hr⟩
  · apply bv_eq_of_bytes (n := 8)
    intro j hjl
    obtain ⟨t, hr⟩ := hx' j hjl
    exact ((hj j hjl).1 t _ hr).2

/-- "no write of class `w` at the window with index above `n`" checker: discharges the
kernel premise of `ptDiscOfWriters` when the kernel does not store to an ACTIVE table. -/
def inWinB (pa a : Int) : Bool := (List.range' 0 8).any (fun j => decide (a = accAddr pa j))

def noKernelWritesB (GD : Gdexec) (fl : List (Geid × Geid)) (pa : Int) (n : Nat) : Bool :=
  (gevents GD.gdG).all (fun w => (gwrBytes GD.gdG w).all (fun y : Int × BitVec 8 =>
    !(!(isSomeB (assoc fl w)) && inWinB pa y.1 && decide (n < gwix GD.gdG w))))

theorem AxPtProt2.inWinBAcc (pa : Int) (j : Nat) (hj : j < 8) : inWinB pa (accAddr pa j) = true :=
  (existsbExistsTrue _ _).2 ⟨j, List.mem_range'_1.2 ⟨Nat.zero_le _, by omega⟩,
    decide_eq_true rfl⟩

theorem noKernelWritesBSound (GD : Gdexec) (fl : List (Geid × Geid)) (sfl : List Geid)
    (pa : Int) (n : Nat) (P : BitVec 64 → Prop) :
    noKernelWritesB GD fl pa n = true →
    ∀ w j v, j < 8 → (mkptw GD fl sfl).gpFor w = none →
      gwritesByte (gpG (mkptw GD fl sfl)) w (accAddr pa j) v →
      n < gwix (gpG (mkptw GD fl sfl)) w → AxPtProt.byteOk P j v := by
  intro H w j v hj hn hw hlt
  exfalso
  have H := (forallbForallTrue _ _).1 H w (gwritesByteGevents _ _ _ _ hw)
  have H := (forallbForallTrue _ _).1 H _ ((gwritesByteBytes _ _ _ _).1 hw)
  have hwin := AxPtProt2.inWinBAcc pa j hj
  have hn' : assoc fl w = none := hn
  have hlt' : n < gwix GD.gdG w := hlt
  simp [hn', hwin, hlt', isSomeB] at H

/-! # 2. `GPad`: install, sfence, walk, Svadu A write-back, load -/

def wb8 (x : BitVec 64) : List (BitVec 8) := (List.range' 0 8).map (fun j => nthByte (n := 8) x j)
def imgz : Image := fun _ => some 0

/-- xv6-faithful leaf: PPN 0x80001, flags V|R|W|X, A = D = 0 (NOT preset). -/
def AxPtProt2.w0 : BitVec 64 := BitVec.ofNat 64 ((0x80001 <<< 10) ||| 0x0F)

/-- the walker's write-back word: the REAL Sail `update_PTE_Bits` for a load. -/
def w1 : BitVec 64 :=
  match update_PTE_Bits AxPtProt2.w0 (.Load .Data) with
  | some x => x
  | none => AxPtProt2.w0

theorem w1Update : update_PTE_Bits AxPtProt2.w0 (.Load .Data) = some w1 := by decide +kernel

theorem w1NeW0 : w1.toNat ≠ AxPtProt2.w0.toNat := by decide +kernel

/-- the translated data address: the leaf's page + offset. -/
def AxPtProt2.paOf (x : BitVec 64) (off : Int) : Int := ((PPN_of_PTE x).toNat : Int) * 4096 + off

theorem paOfW0 : AxPtProt2.paOf AxPtProt2.w0 0x10 = 0x80001010 := by decide +kernel

def ts8 (t : Nat) : List Nat := List.replicate 8 t

/-- Hart 0, PTE at PA 0:
      (0,0) sd w0 → [0]           — mappages' install (explicit, owned)
      (0,1) sfence.vma            — no-op fence marker
      (0,2) walker read [0] = w0  — the walk of the load (0,4)
      (0,3) walker RMW [0]: w0 → w1   — Svadu A write-back (atomic)
      (0,4) ld [0x80001010]       — the data load at the translated PA -/
def gad : Gdexec :=
  ⟨⟨imgz,
    [[LStore false 0 (wb8 AxPtProt2.w0) .WCplain,
      LFence false false false false,
      LLoad false 0 (ts8 1) (wb8 AxPtProt2.w0),
      LRmw false false 0 (ts8 1) (wb8 AxPtProt2.w0) (wb8 w1) .WCplain,
      LLoad false 0x80001010 [0] [0]]],
    [(0, 0), (0, 2), (0, 3), (0, 4)]⟩, [], []⟩

def GPad : Gptw :=
  mkptw gad [((0, 2), (0, 4)), ((0, 3), (0, 4))] [(0, 1)]

theorem gadModel : ptwModel GPad := ptwModelBSound _ _ _ (by decide +kernel)

theorem gadCat : rvwmoCatConsistent gad := catConsistentBSound _ (by decide +kernel)

theorem gAdSound :
    ptwModel GPad ∧
    -- the discipline, derived by the ABSORPTION THEOREM
    ptDisc (gpG GPad) 0 (pteVar AxPtProt2.w0) 1 ∧
    -- the plain walker read and the RMW's read half: pinned to the class
    (∀ x, greadsWord (gpG GPad) (0, 2) 0 x →
      pteVar AxPtProt2.w0 x ∧ AxPtProt2.paOf x 0x10 = 0x80001010) ∧
    (∀ x, greadsWord (gpG GPad) (0, 3) 0 x → pteVar AxPtProt2.w0 x) ∧
    -- the write-back really changes memory, and stays in the class
    gwritesWord (gpG GPad) (0, 3) 0 w1 ∧ w1 ≠ AxPtProt2.w0 ∧ pteVar AxPtProt2.w0 w1 ∧
    -- the load is served by the walk and reads the translated PA
    GPad.gpFor (0, 2) = some (0, 4) ∧
    greadsByte (gpG GPad) (0, 4) (AxPtProt2.paOf AxPtProt2.w0 0x10) 0 0 ∧
    -- TLB-agrees-with-PT at the load (the current word is the WRITE-BACK)
    agreesAt GPad 0 (0, 2) (0, 4) := by
  obtain ⟨_, ⟨hwf, _, _, hat, _, _⟩, ⟨hwv, hsf, hada, _, _⟩⟩ := gadModel
  have hi : gwritesWord (gpG GPad) (0, 0) 0 AxPtProt2.w0 :=
    gwritesWordBSound _ _ _ _ (by decide +kernel)
  have hix : gwix (gpG GPad) (0, 0) = 1 := by decide +kernel
  have hw1 : gwritesWord (gpG GPad) (0, 3) 0 w1 := gwritesWordBSound _ _ _ _ (by decide +kernel)
  have hdisc : ptDisc (gpG GPad) 0 (pteVar AxPtProt2.w0) 1 := by
    rw [← hix]
    apply ptDiscOfWriters GPad 0 (pteVar AxPtProt2.w0) (0, 0) AxPtProt2.w0 hwf hwv hat hada
      (mixClosedVar AxPtProt2.w0) hi (pteVarRefl AxPtProt2.w0)
    · rw [hix]
      exact noKernelWritesBSound gad _ [(0, 1)] 0 1 _ (by decide +kernel)
    · intro u j v _ hu hwu
      obtain ⟨e, hin, _⟩ := gwalkMk gad _ [(0, 1)] u hu
      simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hin
      rcases hin with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exfalso
        have h := (gwritesByteBytes _ _ _ _).1 hwu
        have he : gwrBytes (gpG GPad) (0, 2) = [] := rfl
        rw [he] at h
        cases h
      · obtain ⟨hr, _, _⟩ :=
          readsWordAfterBSound (gpG GPad) (0, 3) 0 AxPtProt2.w0 1 (by decide +kernel)
        exact rmwClassOkUpdate _ _ 0 AxPtProt2.w0 AxPtProt2.w0 w1 (.Load .Data) hr hw1 w1Update
  have hpin : ∀ r x, gwalk GPad r → (r = (0, 2) ∨ r = (0, 3)) →
      greadsWord (gpG GPad) r 0 x → pteVar AxPtProt2.w0 x := by
    intro r x hr hrr hx
    have hcov : sfCovers GPad (0, 0) (0, 1) := Or.inl ((gpoBSpec _ _ _).1 (by decide +kernel))
    have hf : gsfence GPad (0, 1) := ⟨by decide +kernel, by decide +kernel⟩
    refine walkAfterSfence GPad (0, 1) r (0, 0) 0 AxPtProt2.w0 _ x hwf hwv hsf hf hr ?_ hi hcov
      (by rw [hix]; exact hdisc) (mixClosedVar AxPtProt2.w0) hx
    apply (gpoBSpec _ _ _).1
    rcases hrr with rfl | rfl <;> decide +kernel
  have hw1v : pteVar AxPtProt2.w0 w1 :=
    updatePTEBitsVariant AxPtProt2.w0 AxPtProt2.w0 w1 (.Load .Data) (pteVarRefl AxPtProt2.w0)
      w1Update
  refine ⟨gadModel, hdisc, fun x hx => ?_,
    fun x hx => hpin (0, 3) x (by unfold gwalk; decide +kernel) (Or.inr rfl) hx, hw1,
    fun h => w1NeW0 (by rw [h]), hw1v, by decide +kernel, ?_, ?_⟩
  · have V := hpin (0, 2) x (by unfold gwalk; decide +kernel) (Or.inl rfl) hx
    refine ⟨V, ?_⟩
    show ((PPN_of_PTE x).toNat : Int) * 4096 + 0x10 = 0x80001010
    rw [pteVarPpn _ _ V]
    exact paOfW0
  · rw [paOfW0]
    exact (grbBSpec _ _ _ _ _).1 (by decide +kernel)
  · refine agreesAtOfDisc GPad 0 AxPtProt2.w0 (0, 0) (0, 2) (0, 4) hwf hwv
      (by unfold gwalk; decide +kernel) hi
      ((gmoLtBSpec _ _ _).1 (by decide +kernel)) (by rw [hix]; exact hdisc) ?_
    rw [hix]
    exact (readsWordAfterBSound (gpG GPad) (0, 2) 0 AxPtProt2.w0 1 (by decide +kernel)).2.1

/-! # 3. Shared helpers for the multi-hart witnesses -/

def noWalkerWritesB (GD : Gdexec) (fl : List (Geid × Geid)) (pa : Int) : Bool :=
  fl.all (fun p => (gwrBytes GD.gdG p.1).all (fun y : Int × BitVec 8 => !(inWinB pa y.1)))

theorem noWalkerWritesBSound (GD : Gdexec) (fl : List (Geid × Geid)) (sfl : List Geid)
    (pa : Int) (P : BitVec 64 → Prop) :
    noWalkerWritesB GD fl pa = true →
    ∀ u j v, j < 8 → gwalk (mkptw GD fl sfl) u →
      gwritesByte (gpG (mkptw GD fl sfl)) u (accAddr pa j) v →
      rmwClassOk (gpG (mkptw GD fl sfl)) u pa P := by
  intro H u j v hj hu hw
  exfalso
  obtain ⟨e, hin, _⟩ := gwalkMk GD fl sfl u hu
  have H := (forallbForallTrue _ _).1 H _ hin
  have H := (forallbForallTrue _ _).1 H _ ((gwritesByteBytes _ _ _ _).1 hw)
  have hwin := AxPtProt2.inWinBAcc pa j hj
  simp [hwin] at H

/-- `w` is the co-latest window write gmo-before `e` (index `n`). -/
def latestB (G : Gexec) (pa : Int) (e : Geid) (n : Nat) : Bool :=
  (gevents G).all (fun w' => (gwrBytes G w').all (fun y : Int × BitVec 8 =>
    !(inWinB pa y.1 && gmoLtB G w' e) || decide (gwix G w' ≤ n)))

theorem latestBSound (G : Gexec) (pa : Int) (e : Geid) (n : Nat) :
    latestB G pa e n = true →
    ∀ w' j v, j < 8 → gwritesByte G w' (accAddr pa j) v → gmoLt G w' e →
      gwix G w' ≤ n := by
  intro H w' j v hj hw hlt
  have H := (forallbForallTrue _ _).1 H w' (gwritesByteGevents _ _ _ _ hw)
  have H := (forallbForallTrue _ _).1 H _ ((gwritesByteBytes _ _ _ _).1 hw)
  have hwin := AxPtProt2.inWinBAcc pa j hj
  have hlt' := (gmoLtBSpec _ _ _).2 hlt
  simpa [hwin, hlt'] using H

/-- Leaves with A already set (no write-back needed): old page 0x80001, new page 0x80002 —
a REMAP, i.e. a canon-changing PTE store. -/
def wOld : BitVec 64 := BitVec.ofNat 64 ((0x80001 <<< 10) ||| 0x4F)
def wNew : BitVec 64 := BitVec.ofNat 64 ((0x80002 <<< 10) ||| 0x4F)

theorem wOldNewPpn : PPN_of_PTE wOld ≠ PPN_of_PTE wNew := by decide +kernel

theorem wOldNewCanon : PtAdBits.pteCanon wOld ≠ PtAdBits.pteCanon wNew := by decide +kernel

theorem paOfWNew : AxPtProt2.paOf wNew 0x10 = 0x80002010 := by decide +kernel

/-- the image holds `wOld` at PA 0..7 (the installed-at-boot leaf). -/
def imgOld : Image := fun a =>
  if 0 ≤ a ∧ a < 8 then some (nthByte (n := 8) wOld a.toNat) else some 0

/-! # 4. `GPrace`: a remote remap WITHOUT sfence.vma breaks the agreement

hart 0: (0,0) walker read [0] = wOld (STALE: image, t = 0);
        (0,1) ld [0x80001010]  — translated by the stale word
hart 1: (1,0) sd wNew → [0]   — remap, gmo-before (0,1)
gmo = [(0,0); (1,0); (0,1)].  The graph is consistent even under the FULL cat model (walk
treated as explicit), and the full PTW model (incl. H5') holds — no sfence on hart 0. -/
def grace : Gdexec :=
  ⟨⟨imgOld,
    [[LLoad false 0 (ts8 0) (wb8 wOld),
      LLoad false 0x80001010 [0] [0]],
     [LStore false 0 (wb8 wNew) .WCplain]],
    [(0, 0), (1, 0), (0, 1)]⟩, [], []⟩

def GPrace : Gptw := mkptw grace [((0, 0), (0, 1))] []

theorem raceBreaksAgree :
    ptwModel GPrace ∧ rvwmoCatConsistent grace ∧
    GPrace.gpFor (0, 0) = some (0, 1) ∧
    gwritesWord (gpG GPrace) (1, 0) 0 wNew ∧
    gmoLt (gpG GPrace) (1, 0) (0, 1) ∧
    (∀ x, greadsWord (gpG GPrace) (0, 0) 0 x → x = wOld) ∧
    PPN_of_PTE wOld ≠ PPN_of_PTE wNew ∧
    ¬ agreesAt GPrace 0 (0, 0) (0, 1) := by
  obtain ⟨hr, _, huniq⟩ :=
    readsWordAfterBSound (gpG GPrace) (0, 0) 0 wOld 0 (by decide +kernel)
  have hw : gwritesWord (gpG GPrace) (1, 0) 0 wNew := gwritesWordBSound _ _ _ _ (by decide +kernel)
  have hlt : gmoLt (gpG GPrace) (1, 0) (0, 1) := (gmoLtBSpec _ _ _).1 (by decide +kernel)
  refine ⟨ptwModelBSound _ _ _ (by decide +kernel), catConsistentBSound _ (by decide +kernel),
    by decide +kernel, hw, hlt, huniq, wOldNewPpn, fun hag => ?_⟩
  apply wOldNewCanon
  exact hag wOld (1, 0) wNew hr hw hlt
    (latestBSound _ 0 (0, 1) (gwix (gpG GPrace) (1, 0)) (by decide +kernel))

/-! # 5. H5' is a GENUINELY NEW hardware clause: riscv.cat does not order the walk after
sfence.vma

hart 1: (1,0) sd wNew → [0]; (1,1) fence w,w; (1,2) sd 1 → [64] (flag)
hart 0: (0,0) ld [64] = 1; (0,1) sfence.vma; (0,2) walker read [0]; (0,3) ld (data)
The remap is ob-before the flag read (ppo fence; rfe), hence COVERED by the sfence
(H5'.2). -/
def B1 : BitVec 8 := 1

def gsfRows (wr : List Nat) (wv : BitVec 64) (dpa : Int) : List (List Lbl) :=
  [[LLoad false 64 [2] [B1],
    LFence false false false false,
    LLoad false 0 wr (wb8 wv),
    LLoad false dpa [0] [0]],
   [LStore false 0 (wb8 wNew) .WCplain,
    LFence false true false true,
    LStore false 64 [B1] .WCplain]]

/-- STALE: the walk reads the image (gmo-first).  riscv.cat allows it. -/
def gsf : Gdexec :=
  ⟨⟨imgOld, gsfRows (ts8 0) wOld 0x80001010,
    [(0, 2), (1, 0), (1, 2), (0, 0), (0, 3)]⟩, [], []⟩
def GPsf : Gptw := mkptw gsf [((0, 2), (0, 3))] [(0, 1)]

/-- FRESH: the walk reads the remap. -/
def gsfok : Gdexec :=
  ⟨⟨imgOld, gsfRows (ts8 1) wNew 0x80002010,
    [(1, 0), (1, 2), (0, 0), (0, 2), (0, 3)]⟩, [], []⟩
def GPsfok : Gptw := mkptw gsfok [((0, 2), (0, 3))] [(0, 1)]

theorem gsfCover (GD : Gdexec) (fl : List (Geid × Geid)) (sfl : List Geid) :
    GD.gdG = ⟨imgOld, GD.gdG.gxProg, GD.gdG.gxGmo⟩ →
    gppoCatB GD (1, 0) (1, 2) = true →
    grfeB GD.gdG (1, 2) (0, 0) = true →
    gpoB GD.gdG (0, 0) (0, 1) = true →
    assoc fl (1, 0) = none → assoc fl (1, 2) = none → assoc fl (0, 0) = none →
    sfCovers (mkptw GD fl sfl) (1, 0) (0, 1) := by
  intro _ hp hr hpo hn10 hn12 hn00
  refine Or.inr ⟨(0, 0), (gpoBSpec _ _ _).1 hpo, ?_⟩
  exact tc_l ⟨Or.inl ((gppoCatBSpec _ _ _).1 hp), hn10, hn12⟩
    (tc_once ⟨Or.inr (Or.inr (Or.inl ((grfeBSpec _ _ _).1 hr))), hn12, hn00⟩)

theorem gsfCat : rvwmoCatConsistent gsf := catConsistentBSound _ (by decide +kernel)

theorem gsfNotH5 : ¬ h5Sfence GPsf := by
  intro H
  have hcov : sfCovers GPsf (1, 0) (0, 1) :=
    gsfCover gsf _ _ rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have hle : gwix (gpG GPsf) (1, 0) ≤ 0 :=
    H (0, 1) (0, 2) 0 0 (nthByte (n := 8) wOld 0) (1, 0) (nthByte (n := 8) wNew 0)
      ⟨by decide +kernel, by decide +kernel⟩ (by unfold gwalk; decide +kernel)
      ((gpoBSpec _ _ _).1 (by decide +kernel))
      ((grbBSpec _ _ _ _ _).1 (by decide +kernel))
      ((gwbBSpec _ _ _ _).1 (by decide +kernel)) hcov
  have hix : gwix (gpG GPsf) (1, 0) = 1 := by decide +kernel
  omega

/-- ... while the explicit part of the model holds on `GPsf`: the ONLY obstruction is H5'. -/
theorem gsfExplicit : ptwWf GPsf ∧ ptwExplicitConsistent GPsf ∧ h5WalkValue GPsf :=
  ⟨ptwWfBSound _ _ _ (by decide +kernel), ptwExplicitOfCat _ gsfCat, h5WalkValueOfCat _ gsfCat⟩

theorem gsfokSound :
    ptwModel GPsfok ∧
    (∀ x, greadsWord (gpG GPsfok) (0, 2) 0 x →
      pteVar wNew x ∧ AxPtProt2.paOf x 0x10 = 0x80002010) ∧
    agreesAt GPsfok 0 (0, 2) (0, 3) := by
  have hm := ptwModelBSound gsfok [((0, 2), (0, 3))] [(0, 1)] (by decide +kernel)
  obtain ⟨_, ⟨hwf, _, _, hat, _, _⟩, ⟨hwv, hsf, hada, _, _⟩⟩ := hm
  have hi : gwritesWord (gpG GPsfok) (1, 0) 0 wNew := gwritesWordBSound _ _ _ _ (by decide +kernel)
  have hix : gwix (gpG GPsfok) (1, 0) = 1 := by decide +kernel
  have hdisc : ptDisc (gpG GPsfok) 0 (pteVar wNew) (gwix (gpG GPsfok) (1, 0)) := by
    apply ptDiscOfWriters GPsfok 0 (pteVar wNew) (1, 0) wNew hwf hwv hat hada
      (mixClosedVar wNew) hi (pteVarRefl wNew)
    · rw [hix]
      exact noKernelWritesBSound gsfok _ [(0, 1)] 0 1 _ (by decide +kernel)
    · exact noWalkerWritesBSound gsfok _ [(0, 1)] 0 _ (by decide +kernel)
  have hcov : sfCovers GPsfok (1, 0) (0, 1) :=
    gsfCover gsfok _ _ rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have hf : gsfence GPsfok (0, 1) := ⟨by decide +kernel, by decide +kernel⟩
  have hr : gwalk GPsfok (0, 2) := by unfold gwalk; decide +kernel
  have hfr : WeakRvwmoGraph.gpo (gpG GPsfok) (0, 1) (0, 2) :=
    (gpoBSpec _ _ _).1 (by decide +kernel)
  have hra := readsAfterOfSfence GPsfok _ _ _ 0 wNew hsf hf hr hfr hi hcov
  refine ⟨ptwModelBSound _ _ _ (by decide +kernel), fun x hx => ?_,
    agreesAtOfDisc GPsfok 0 wNew (1, 0) _ _ hwf hwv hr hi
      ((gmoLtBSpec _ _ _).1 (by decide +kernel)) hdisc hra⟩
  have V := walkAfterSfence GPsfok _ _ _ 0 wNew _ x hwf hwv hsf hf hr hfr hi hcov hdisc
    (mixClosedVar wNew) hx
  refine ⟨V, ?_⟩
  show ((PPN_of_PTE x).toNat : Int) * 4096 + 0x10 = 0x80002010
  rw [pteVarPpn _ _ V]
  exact paOfWNew

end Weak
