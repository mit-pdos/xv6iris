/-
Weak: **blocker (i) of the A2a walker bridge — the sfence.vma "marker" of the PTW model
(H5'), re-ported on the Q7 MARKER EVENT** (AxSL tier; owner ruling Q7, route (a) of
`notes/weak-port-q7-sfence.md`).

Rocq: `iris/AxSfence.v` @ xxvzwolszwmp.

The Rocq header, in substance.  Sail's `execute_SFENCE_VMA` emits no memory / barrier event
(it only flushes the `tlb` register), and AxOpsem cannot step past a row item without
emitting its label.  Rocq therefore used the sfence instruction's OWN FETCH as the H5'
sfence point (every H5' clause uses the sfence only for its program-order position).  PURE
(graph level).  Companion: AxSfence2 (the WPd leaf).

Q7 (Lean): fetches are not graph events (Stage C), so the sfence gets its own graph event:
the announce node of an SFENCE.VMA word (`WeakEvLang.sfAnnB`, the opcode test) carries the
label `LFence false false false false` (`WeakEvLang.annLabel`, emitted by
`WeakEvInst.pnodeStep`'s announce arm) instead of `LInstr`; it projects to the graph label
`Lbl.LFence false false false false`, AxPtProt's original marker.  This file is Rocq's with
the fetch replaced by that marker.

§1  THE DECODE PREDICATE.  `sfWord w`: the 32-bit word decodes, at every state with
    `misa = misaC` and `cfgOk`, to `SFENCE_VMA (rs1, rs2)`.  `sfBytes vs`: `vs` are the 4
    little-endian bytes of such a word.  xv6's word `WSfence = 0x12000073`
    (`sfence.vma zero,zero`): `sfWordXv6`; `AxSfence.sfAnnXv6` links it to `sfAnnB` (the
    announce of that word emits the marker).
§2  THE RESTATED MODEL.  `sfMark G f`: `f`'s label is the marker.  `gsfenceF GP f := gpSf f ∧
    sfMark`.  `sfCoversF GP s f`: `s` po-before `f`, or explicitly-ob-before an event
    po-AT-OR-before `f` (Rocq's shape).  `h5SfenceF` (H5'.2), `h5SfenceAdF` (H5'.5), `ptwWfF`,
    `ptwHwF`, `ptwModelF`, the row tag `gpSfRow`.  H5'.1/.3/.4 and the explicit part are
    unchanged.
§3  THE MARKER FORM IS AxPtProt's FORM: `gsfenceMIff`, `ptwWfFIff`, `h5SfenceAdIff` are
    `Iff.rfl`; `h5SfenceOfF`/`ptwModelOfF` (marker form ⇒ AxPtProt's, unconditionally) and
    `ptwModelMarkerIff` (⇔, given no explicit-ob edge INTO a tagged marker — the `e = f`
    disjunct of `sfCoversF` is then inert; decided by `AxSfence.noObInto`).
§4  CHECKERS for `ptwModelF` (`ptwModelFBSound`; everything but the marker-form H5'.2 is
    delegated to `AxPtProt2.ptwModelB`).
§5  THE WITNESSES re-derived with the sfence = the marker, where Rocq's rows had the fetch
    (so the rows are AxPtProt2's `gad`/`gsfRows`): `gAdSoundF`, `raceBreaksAgreeF`, `gsfCatF`
    + `gsfNotH5F` (H5'.2 is still a genuinely new clause), `gsfExplicitF`, `gsfokSoundF`,
    `gadmBoth` (non-vacuity of §3).
CONCERNS (Rocq header): (2) `sfCoversF` counts stores ob-before the sfence event itself (now
an empty set unless the graph has an ob edge into the marker); (3) `sfWord` is a ∀-state
decode fact (non-triviality in AxSfence2).  Rocq's concern (1) (the fetch treated as an
explicit read) is gone: the marker reads nothing.

**Deviations from Rocq.**

1. NAMES: lowerCamelCase (map below).  None of this file's names is in
   `notes/weak-port-dupnames.json`.
2. VOCABULARY: as `AxPtProt2` deviation 2.  `sf_word`'s state: Rocq `RiscvLang.mstate`,
   `register_lookup misa s.(sregs) = MISA_C`, `cfg_ok s`, `RiscvExec.exec` ↦ `Weak.ExecSt`,
   `s.regs .misa = misaC` (`ExecSC2`), `cfgOk s` (`WeakFunnel`, the literal restatement of
   Rocq's `cfg_ok`), `Weak.exec`; `mword_of_int W` ↦ `BitVec.ofInt 32 W`.  `wb32 W j`:
   `Z_to_bv 8 (Z.land (Z.shiftr W (8 * j)) 255)` ↦ `BitVec.ofInt 8 ((W >>> (8 * j)) % 256)`
   with `j : Nat` (Rocq `j : Z`; only `j = 0..3` are used); `nth_error` ↦ `l[n]?`;
   `S k` ↦ `k + 1`; `(Rocq) Section marker`'s `Context`/`Hypothesis` ↦ explicit
   arguments (each lemma takes exactly the hypotheses its Rocq proof uses).
3. `sfWordXv6`: Rocq `exact (kd_12000073 s Hm Hc)` (the generated KernelDecode20 catalogue,
   which Lean does not have, architecture C.5) ↦ a case split on `cfgOk` and
   `Weak.execOfRunRead` from the decoder's read-only walk, evaluated by `rfl` on the
   machine-mode reference map `MachCSL.drefM` and on the Lean-only supervisor-mode map
   `AxSfence.drefSf` (`drefS` without `mseccfg`, which `cfg_ok`'s supervisor branch does
   not pin and the walk does not read), with `hartSupports`, `currentlyEnabled` and
   `virtual_memory_supported` locally semireducible (the SFENCE_VMA decode clause asks
   `virtual_memory_supported ()`); `BitVec.ofInt 32 WSfence` is first rewritten to the
   literal `0x12000073#32`.
4. `vmr` ↦ `decide +kernel`; closed `gwalk` goals are `unfold gwalk; decide +kernel`.
5. Proof-only: in `gAdSoundF` the "walker read (0,2) writes no byte" case is closed by
   `gwrBytes … = []` (as `AxPtProt2.gAdSound`); `gsfExplicitF` takes `ptwExplicitConsistent`
   and `h5WalkValue` from `gsfCatF` directly.
6. The `Print Assumptions` lines have no Lean twin (the lint's axiom check covers them).
7. Q7 — THE MARKER REPLACES THE FETCH (owner ruling Q7; `notes/weak-port-q7-sfence.md`):
   - Rocq `sf_fetch G f` (a plain load of `sf_bytes`) ↦ `sfMark G f` (the label is
     `LFence false false false false`); `sf_fetch_some` ↦ `sfMarkSome`; `sf_fetch_b` /
     `sf_fetch_b_sound` ↦ `sfMarkB` (= `AxPtProt2.sfLblB`) / `sfMarkBSound`.  `gsfenceF`,
     `ptwWfF`'s third clause and `h5SfenceAdF` are therefore AxPtProt's `gsfence`/`ptwWf`/
     `h5SfenceAd` verbatim.
   - §3: Rocq relates a FETCH tag `sff` to a MARKER tag `sfm` one position later
     (`Hff`/`Hmk`/`Hcorr`).  The sfence now IS the marker, so `gsfenceMIff`,
     `h5SfenceAdIff` are `Iff.rfl` on one tagging, `coversIff`/`h5SfenceIff`/
     `ptwModelMarkerIff` take the inertness premise "no `gobExpl` edge into a tagged event"
     (Rocq's `e = f` disjunct was an ob edge into the FETCH, a real read; at the marker it is
     inert only without such edges — `gdDeps` is an arbitrary edge list), and the
     unconditional direction is `h5SfenceOfF`/`ptwModelOfF` (Lean-only).
     `AxSfence.noObInto` (Lean-only) decides the premise on a consistent graph.
   - §4: `ptwModelFB := ptwModelB GD fl sfl && h5SfenceFB GD fl sfl` (Rocq: `ptwModelB` at an
     EMPTY marker list plus the fetch-form checks).
   - §5: the rows put `LFence false false false false` where `LFetchSf` was, so `gadF`,
     `gsfRowsF`, `gsfF`, `gsfokF` ARE AxPtProt2's `gad`, `gsfRows`, `gsf`, `gsfok` (the
     marker is not in `gmo`; the image is `imgz` / `imgOld`, no text page).  `gadm` has two
     adjacent markers (the old fetch position and Rocq's marker); `gadmBoth` proves the
     second-tag model by AxPtProt2's checker and the first-tag `ptwModelF` through the §3
     iff.
   - DROPPED (no role without a fetch; no Lean importer): `PCsf`, `with_text`, `LFetchSf`.
     `writesNotLoad`/`iswNotLoad` are kept (generic graph facts, now unused here).

**Rocq → Lean name map.**  `sf_word` ↦ `sfWord`; `wb32`; `word_bytes` ↦ `wordBytes`;
`sf_bytes` ↦ `sfBytes`; `W_sfence` ↦ `WSfence`; `sf_word_xv6` ↦ `sfWordXv6`;
`sf_bytes_xv6` ↦ `sfBytesXv6`; `sf_fetch` ↦ `sfMark` (deviation 7); `gsfence_f` ↦ `gsfenceF`;
`sf_covers_f` ↦ `sfCoversF`; `h5_sfence_f` ↦ `h5SfenceF`; `h5_sfence_ad_f` ↦
`h5SfenceAdF`; `ptw_wf_f` ↦ `ptwWfF`; `ptw_hw_f` ↦ `ptwHwF`; `ptw_model_f` ↦ `ptwModelF`;
`gp_sf_row` ↦ `gpSfRow`; `gp_sf_row_spec` ↦ `gpSfRowSpec`; `walk_after_sfence_f` ↦
`walkAfterSfenceF`; `reads_after_of_sfence_f` ↦ `readsAfterOfSfenceF`;
`sf_covers_f_of_old` ↦ `sfCoversFOfOld`; `sf_fetch_some` ↦ `sfMarkSome`;
`gpo_into_next` ↦ `gpoIntoNext`; `gpo_next_from` ↦ `gpoNextFrom`; `gpo_next_to` ↦
`gpoNextTo`; `reads_not_fence` ↦ `readsNotFence`; `writes_not_load` ↦ `writesNotLoad`;
`isw_not_load` ↦ `iswNotLoad`; `isw_not_fence` ↦ `iswNotFence`; `gsfence_m_iff` ↦
`gsfenceMIff`; `covers_iff` ↦ `coversIff`; `h5_sfence_iff` ↦ `h5SfenceIff`;
`h5_sfence_ad_iff` ↦ `h5SfenceAdIff`; `ptw_model_marker_iff` ↦ `ptwModelMarkerIff`;
`sf_fetch_b` ↦ `sfMarkB`; `sf_fetch_b_sound` ↦ `sfMarkBSound`; `cover_f_b` ↦ `coverFB`;
`h5_sfence_f_b` ↦ `h5SfenceFB`; `ptw_model_f_b` ↦ `ptwModelFB`; `gsfence_f_mk` ↦
`gsfenceFMk`; `ptw_model_f_b_sound` ↦ `ptwModelFBSound`; `gad_f` ↦ `gadF`; `GPad_f` ↦
`GPadF`; `gad_f_model` ↦ `gadFModel`; `g_ad_sound_f` ↦ `gAdSoundF`; `race_breaks_agree_f` ↦
`raceBreaksAgreeF`; `gsf_rows_f` ↦ `gsfRowsF`; `gsf_f` ↦ `gsfF`; `GPsf_f` ↦ `GPsfF`;
`gsfok_f` ↦ `gsfokF`; `GPsfok_f` ↦ `GPsfokF`; `gsf_cover_f` ↦ `gsfCoverF`; `gsf_cat_f` ↦
`gsfCatF`; `gsf_not_h5_f` ↦ `gsfNotH5F`; `gsf_explicit_f` ↦ `gsfExplicitF`;
`gsfok_sound_f` ↦ `gsfokSoundF`; `gadm`; `fl_m` ↦ `flM`; `gadm_both` ↦ `gadmBoth`.
Lean-only: `AxSfence.drefSf` (deviation 3), `AxSfence.sfAnnXv6`, `AxSfence.noObInto`,
`ptwWfFIff`, `h5SfenceOfF`, `ptwModelOfF` (deviation 7).

**Dropped:** `PCsf`, `with_text`, `LFetchSf` (deviation 7).
-/
import Weak.AxPtProt2
import Weak.WeakFunnel
import Weak.WeakEvLang

namespace Weak

open MachCSL MachCSL.Stdpp
open Lbl
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D LeanRV64D.Functions

-- The decoder's walk reads the platform configuration (see `Xv6/CodeTactics.lean`).
attribute [local semireducible] LeanRV64D.Functions.hartSupports
  LeanRV64D.Functions.currentlyEnabled LeanRV64D.Functions.virtual_memory_supported

/-! # 1. The decode predicate -/

def sfWord (w : BitVec 32) : Prop :=
  ∃ rs1 rs2 : regidx, ∀ s : ExecSt,
    s.regs .misa = misaC → cfgOk s →
    exec (ext_decode w) s = some (.SFENCE_VMA (rs1, rs2), s)

def wb32 (W : Int) (j : Nat) : BitVec 8 := BitVec.ofInt 8 ((W >>> (8 * j)) % 256)
def wordBytes (W : Int) : List (BitVec 8) := [wb32 W 0, wb32 W 1, wb32 W 2, wb32 W 3]

def sfBytes (vs : List (BitVec 8)) : Prop :=
  ∃ W : Int, (0 ≤ W ∧ W < 2 ^ 32) ∧ vs = wordBytes W ∧ sfWord (BitVec.ofInt 32 W)

/-- xv6's `sfence.vma zero, zero` (kvminithart +0x8 / +0x20, trampoline). -/
def WSfence : Int := 0x12000073

/-- The supervisor-mode reference map without `mseccfg` (Lean-only; deviation 3). -/
def AxSfence.drefSf : (r : Register) → Option (RegisterType r)
  | .cur_privilege => some Privilege.Supervisor
  | .misa => some 0x800000000014112D#64
  | .menvcfg => some menvcfgS
  | _ => none

theorem sfWordXv6 : sfWord (BitVec.ofInt 32 WSfence) := by
  have hw : BitVec.ofInt 32 WSfence = 0x12000073#32 := by decide
  rw [hw]
  refine ⟨regidx.Regidx 0#5, regidx.Regidx 0#5, fun s hm hc => ?_⟩
  rcases hc with ⟨hp, hsec⟩ | ⟨hp, henv⟩
  · refine execOfRunRead drefM _ s _ true ?_ rfl
    intro r v hv
    unfold drefM at hv
    split at hv <;> simp only [Option.some.injEq, reduceCtorEq] at hv <;> subst hv
    · exact hp
    · exact hm
    · exact hsec
  · refine execOfRunRead AxSfence.drefSf _ s _ true ?_ rfl
    intro r v hv
    unfold AxSfence.drefSf at hv
    split at hv <;> simp only [Option.some.injEq, reduceCtorEq] at hv <;> subst hv
    · exact hp
    · exact hm
    · exact henv

theorem sfBytesXv6 : sfBytes (wordBytes WSfence) :=
  ⟨WSfence, ⟨by decide, by decide⟩, rfl, sfWordXv6⟩

/-- (Lean-only, Q7) THE LINK: the weak tier's SFENCE.VMA opcode test `sfAnnB` (the announce
that emits the marker) holds at xv6's word, which the Sail decoder decodes as `SFENCE_VMA`. -/
theorem AxSfence.sfAnnXv6 :
    sfAnnB 32 (BitVec.ofInt 32 WSfence) = true ∧ sfWord (BitVec.ofInt 32 WSfence) :=
  ⟨by decide, sfWordXv6⟩

/-! # 2. The restated model: the sfence is its own MARKER event (Q7) -/

/-- The sfence.vma marker (Q7): the graph event the announce of an SFENCE.VMA word emits
(`WeakEvLang.annLabel`). -/
def sfMark (G : Gexec) (f : Geid) : Prop :=
  gxLbl G f = some (LFence false false false false)

def gsfenceF (GP : Gptw) (f : Geid) : Prop :=
  GP.gpSf f = true ∧ sfMark (gpG GP) f

def sfCoversF (GP : Gptw) (s f : Geid) : Prop :=
  WeakRvwmoGraph.gpo (gpG GP) s f ∨
  ∃ e, (e = f ∨ WeakRvwmoGraph.gpo (gpG GP) e f) ∧ gobExpl GP s e

/-- H5'.2, marker form (Rocq's fetch-form statement shape). -/
def h5SfenceF (GP : Gptw) : Prop :=
  ∀ f r a t v s v', gsfenceF GP f → gwalk GP r → WeakRvwmoGraph.gpo (gpG GP) f r →
    greadsByte (gpG GP) r a t v → gwritesByte (gpG GP) s a v' →
    sfCoversF GP s f → gwix (gpG GP) s ≤ t

/-- H5'.5, marker form. -/
def h5SfenceAdF (GP : Gptw) : Prop :=
  ∀ u f s, gsfenceF GP f → gwalk GP u → glblIs (gpG GP) u lbIsW →
    WeakRvwmoGraph.gpo (gpG GP) u f → WeakRvwmoGraph.gpo (gpG GP) f s → GP.gpFor s = none →
    glblIs (gpG GP) s lbIsW → gmoLt (gpG GP) u s

def ptwWfF (GP : Gptw) : Prop :=
  (∀ u e, GP.gpFor u = some e → WeakRvwmoGraph.gpo (gpG GP) u e ∧ GP.gpFor e = none) ∧
  (∀ u, gwalk GP u → glblIs (gpG GP) u lbIsW → glblIs (gpG GP) u lbIsR) ∧
  (∀ f, GP.gpSf f = true → sfMark (gpG GP) f)

def ptwHwF (GP : Gptw) : Prop :=
  h5WalkValue GP ∧ h5SfenceF GP ∧ h5AdAtomic GP ∧ h5AdBefore GP ∧ h5SfenceAdF GP

def ptwModelF (GP : Gptw) : Prop :=
  ptwWfF GP ∧ ptwExplicitConsistent GP ∧ ptwHwF GP

/-- The row-level sfence tag: `ks` are the row positions of hart `i`'s sfence.vma MARKER
items (the row-level model is in AxSfence2). -/
def gpSfRow (i : Nat) (ks : List Nat) (e : Geid) : Bool :=
  decide (e.1 = i ∧ e.2 ∈ ks)

theorem gpSfRowSpec (i : Nat) (ks : List Nat) (e : Geid) :
    gpSfRow i ks e = true ↔ e.1 = i ∧ e.2 ∈ ks := by
  unfold gpSfRow
  exact decide_eq_true_iff

/-- The H5' consumers, marker form (twins of `walkAfterSfence` / `readsAfterOfSfence`). -/
theorem walkAfterSfenceF (GP : Gptw) (f r i : Geid) (pa : Int) (w0 : BitVec 64)
    (P : BitVec 64 → Prop) (x : BitVec 64) :
    gwf (gpG GP) → h5WalkValue GP → h5SfenceF GP →
    gsfenceF GP f → gwalk GP r → WeakRvwmoGraph.gpo (gpG GP) f r →
    gwritesWord (gpG GP) i pa w0 → sfCoversF GP i f →
    ptDisc (gpG GP) pa P (gwix (gpG GP) i) → mixClosed P →
    greadsWord (gpG GP) r pa x → P x := by
  intro hwf hwv hsf hf hr hfr hi hcov hd hmix hx
  refine walkReadClass GP pa P (gwix (gpG GP) i) r x hwf hwv hd hmix hr ?_
  intro j hj
  obtain ⟨t, ht⟩ := hx j hj
  exact ⟨t, ht, hsf f r _ t _ i _ hf hr hfr ht (hi j hj) hcov⟩

theorem readsAfterOfSfenceF (GP : Gptw) (f r i : Geid) (pa : Int) (w0 : BitVec 64) :
    h5SfenceF GP → gsfenceF GP f → gwalk GP r → WeakRvwmoGraph.gpo (gpG GP) f r →
    gwritesWord (gpG GP) i pa w0 → sfCoversF GP i f →
    readsAfter (gpG GP) r pa (gwix (gpG GP) i) := by
  intro hsf hf hr hfr hi hcov j t v hj hrt
  exact hsf f r _ t v i _ hf hr hfr hrt (hi j hj) hcov

theorem sfCoversFOfOld (GP : Gptw) (s f : Geid) : sfCovers GP s f → sfCoversF GP s f := by
  rintro (h | ⟨e, he, hob⟩)
  · exact Or.inl h
  · exact Or.inr ⟨e, Or.inr he, hob⟩

/-! # 3. The marker form IS AxPtProt's form

Q7: the sfence is the marker itself, so the tag, `gsfenceF`, `ptwWfF` and H5'.5 are AxPtProt's
verbatim; H5'.2 differs only by `sfCoversF`'s `e = f` disjunct (an explicit-ob edge INTO the
marker), which is inert whenever no such edge exists (`noObInto`). -/

theorem sfMarkSome (G : Gexec) (f : Geid) : sfMark G f → (gxLbl G f).isSome = true := by
  intro hl
  unfold sfMark at hl
  rw [hl]
  rfl

theorem gpoIntoNext (G : Gexec) (f x : Geid) :
    (gxLbl G f).isSome = true → (gxLbl G (f.1, f.2 + 1)).isSome = true →
    (WeakRvwmoGraph.gpo G x (f.1, f.2 + 1) ↔ WeakRvwmoGraph.gpo G x f ∨ x = f) := by
  obtain ⟨i, k⟩ := f
  obtain ⟨j, l⟩ := x
  intro hf hm
  simp only [WeakRvwmoGraph.gpo] at *
  constructor
  · rintro ⟨rfl, hlt, hx, _⟩
    by_cases hl : l = k
    · subst hl
      exact Or.inr rfl
    · exact Or.inl ⟨rfl, by omega, hx, hf⟩
  · rintro (⟨rfl, hlt, hx, _⟩ | h)
    · exact ⟨rfl, by omega, hx, hm⟩
    · cases h
      exact ⟨rfl, by omega, hf, hm⟩

theorem gpoNextFrom (G : Gexec) (f r : Geid) :
    (gxLbl G f).isSome = true → WeakRvwmoGraph.gpo G (f.1, f.2 + 1) r →
    WeakRvwmoGraph.gpo G f r := by
  obtain ⟨i, k⟩ := f
  obtain ⟨j, l⟩ := r
  rintro hf ⟨h1, hlt, _, hr⟩
  exact ⟨h1, by simp only at hlt ⊢; omega, hf, hr⟩

theorem gpoNextTo (G : Gexec) (f r : Geid) :
    (gxLbl G (f.1, f.2 + 1)).isSome = true → WeakRvwmoGraph.gpo G f r →
    r ≠ (f.1, f.2 + 1) → WeakRvwmoGraph.gpo G (f.1, f.2 + 1) r := by
  obtain ⟨i, k⟩ := f
  obtain ⟨j, l⟩ := r
  rintro hm ⟨h1, hlt, _, hr⟩ hne
  simp only at h1 hlt hm hne ⊢
  subst h1
  refine ⟨rfl, ?_, hm, hr⟩
  by_cases hl : l = k + 1
  · subst hl
    exact absurd rfl hne
  · omega

theorem readsNotFence (G : Gexec) (e : Geid) (a : Int) (t : Nat) (v : BitVec 8)
    (pr pw sr sw : Bool) :
    gxLbl G e = some (LFence pr pw sr sw) → ¬ greadsByte G e a t v := by
  rintro hl ⟨l, base, ts, vs, j, hl', hrd, _⟩
  rw [hl] at hl'
  cases hl'
  simp [lbRd] at hrd

theorem writesNotLoad (G : Gexec) (e : Geid) (a : Int) (v : BitVec 8) (aq : Bool) (base : Int)
    (ts : List Nat) (vs : List (BitVec 8)) :
    gxLbl G e = some (LLoad aq base ts vs) → ¬ gwritesByte G e a v := by
  rintro hl ⟨l, base', vs', j, hl', hwr, _⟩
  rw [hl] at hl'
  cases hl'
  simp [lbWr] at hwr

theorem iswNotLoad (G : Gexec) (e : Geid) (aq : Bool) (base : Int) (ts : List Nat)
    (vs : List (BitVec 8)) :
    gxLbl G e = some (LLoad aq base ts vs) → ¬ glblIs G e lbIsW := by
  rintro hl ⟨l, hl', hw⟩
  rw [hl] at hl'
  cases hl'
  simp [lbIsW] at hw

theorem iswNotFence (G : Gexec) (e : Geid) (pr pw sr sw : Bool) :
    gxLbl G e = some (LFence pr pw sr sw) → ¬ glblIs G e lbIsW := by
  rintro hl ⟨l, hl', hw⟩
  rw [hl] at hl'
  cases hl'
  simp [lbIsW] at hw

theorem gsfenceMIff (GP : Gptw) (m : Geid) : gsfence GP m ↔ gsfenceF GP m := Iff.rfl

theorem ptwWfFIff (GP : Gptw) : ptwWf GP ↔ ptwWfF GP := Iff.rfl

/-- At a marker with no explicit-ob edge into it, the two cover relations agree. -/
theorem coversIff (GP : Gptw) (s f : Geid) :
    ¬ gobExpl GP s f → (sfCovers GP s f ↔ sfCoversF GP s f) := by
  intro hin
  refine ⟨sfCoversFOfOld GP s f, ?_⟩
  rintro (hp | ⟨e, rfl | hp, hob⟩)
  · exact Or.inl hp
  · exact absurd hob hin
  · exact Or.inr ⟨e, hp, hob⟩

/-- The marker form implies AxPtProt's (unconditionally: `sfCoversF ⊇ sfCovers`). -/
theorem h5SfenceOfF (GP : Gptw) : h5SfenceF GP → h5Sfence GP :=
  fun H f r a t v s v' hf hr hfr hrd hwr hcov =>
    H f r a t v s v' hf hr hfr hrd hwr (sfCoversFOfOld GP s f hcov)

theorem h5SfenceIff (GP : Gptw) (Hin : ∀ s f, GP.gpSf f = true → ¬ gobExpl GP s f) :
    h5Sfence GP ↔ h5SfenceF GP := by
  refine ⟨fun H f r a t v s v' hf hr hfr hrd hwr hcov => ?_, h5SfenceOfF GP⟩
  exact H f r a t v s v' hf hr hfr hrd hwr ((coversIff GP s f (Hin s f hf.1)).2 hcov)

theorem h5SfenceAdIff (GP : Gptw) : h5SfenceAd GP ↔ h5SfenceAdF GP := Iff.rfl

theorem ptwModelOfF (GP : Gptw) : ptwModelF GP → ptwModel GP := by
  rintro ⟨W, E, V, S, A, B, D⟩
  exact ⟨W, E, V, h5SfenceOfF GP S, A, B, D⟩

/-- THE RELATION (Q7): the marker form is AxPtProt's form, given that no explicit-ob edge
enters a tagged marker. -/
theorem ptwModelMarkerIff (GP : Gptw) (Hin : ∀ s f, GP.gpSf f = true → ¬ gobExpl GP s f) :
    ptwModel GP ↔ ptwModelF GP := by
  unfold ptwModel ptwModelF ptwHw ptwHwF
  rw [h5SfenceIff GP Hin, h5SfenceAdIff GP]
  exact Iff.rfl

/-- (Lean-only) The inertness premise, decided: on a cat-consistent graph, no ob edge enters
`f` when no event has a `gobrCatB` edge into it. -/
theorem AxSfence.noObInto (GD : Gdexec) (fl : List (Geid × Geid)) (sfl : List Geid) (f : Geid) :
    rvwmoCatConsistent GD →
    (gevents GD.gdG).all (fun x => !(gobrCatB GD x f)) = true →
    ∀ s, ¬ gobExpl (mkptw GD fl sfl) s f := by
  intro hc hB s h
  have hstep : ∀ x, ¬ gobrCat GD x f := by
    intro x hx
    have hxe := (gobrCatGevents GD x f hc hx).1
    have H := (forallbForallTrue _ _).1 hB x hxe
    rw [(gobrCatBSpec GD x f).2 hx] at H
    cases H
  cases h with
  | single h => exact hstep _ h.1
  | tail _ h => exact hstep _ h.1

/-! # 4. Checkers for `ptwModelF` -/

/-- The marker test is AxPtProt2's `sfLblB`. -/
def sfMarkB (G : Gexec) (f : Geid) : Bool := sfLblB G f

theorem sfMarkBSound (G : Gexec) (f : Geid) : sfMarkB G f = true → sfMark G f :=
  sfLblBSpec G f

section checkersF

variable (GD : Gdexec) (fl : List (Geid × Geid)) (sfl : List Geid)

def coverFB (s f : Geid) : Bool :=
  gpoB GD.gdG s f ||
  (gevents GD.gdG).any (fun e => (decide (e = f) || gpoB GD.gdG e f) && gmoLtB GD.gdG s e)

def h5SfenceFB : Bool :=
  sfl.all (fun f =>
    fl.all (fun p =>
      (grdBytes GD.gdG p.1).all (fun x : (Int × Nat) × BitVec 8 =>
        (gevents GD.gdG).all (fun s =>
          (gwrBytes GD.gdG s).all (fun y : Int × BitVec 8 =>
            !(gpoB GD.gdG f p.1 && decide (y.1 = x.1.1) && coverFB GD s f)
            || decide (gwix GD.gdG s ≤ x.1.2))))))

/-- Q7: everything but the marker-form H5'.2 is AxPtProt2's checker (its `ptwWfB` checks the
marker labels, its `h5SfenceAdB` H5'.5). -/
def ptwModelFB : Bool :=
  ptwModelB GD fl sfl && h5SfenceFB GD fl sfl

theorem gsfenceFMk (f : Geid) : gsfenceF (mkptw GD fl sfl) f → f ∈ sfl := by
  rintro ⟨h, _⟩
  have h' : decide (f ∈ sfl) = true := h
  exact of_decide_eq_true h'

theorem ptwModelFBSound : ptwModelFB GD fl sfl = true → ptwModelF (mkptw GD fl sfl) := by
  intro H
  unfold ptwModelFB at H
  simp only [Bool.and_eq_true] at H
  obtain ⟨H0, Hsf⟩ := H
  have Hcat : catConsistentB GD = true := by
    have H0' := H0
    unfold ptwModelB at H0'
    simp only [Bool.and_eq_true] at H0'
    exact H0'.1.1.1.1.1
  have hc := catConsistentBSound GD Hcat
  obtain ⟨W, E, ⟨V, _, A, B, D⟩⟩ := ptwModelBSound GD fl sfl H0
  refine ⟨W, E, V, ?_, A, B, D⟩
  -- H5'.2, marker form
  intro f r a t v s v' hf hr hfr hrd hwr hcov
  have hfin := gsfenceFMk GD fl sfl f hf
  obtain ⟨e, hin, _⟩ := gwalkMk GD fl sfl r hr
  unfold h5SfenceFB at Hsf
  have H := (forallbForallTrue _ _).1 Hsf f hfin
  have H := (forallbForallTrue _ _).1 H _ hin
  have H := (forallbForallTrue _ _).1 H ((a, t), v) ((greadsByteBytes _ _ _ _ _).1 hrd)
  have H := (forallbForallTrue _ _).1 H s (gwritesByteGevents _ _ _ _ hwr)
  have H := (forallbForallTrue _ _).1 H (a, v') ((gwritesByteBytes _ _ _ _).1 hwr)
  simp only [Bool.or_eq_true, Bool.not_eq_true'] at H
  rcases H with H | H
  · exfalso
    have hc1 : gpoB GD.gdG f r = true := (gpoBSpec _ _ _).2 hfr
    have hc3 : coverFB GD s f = true := by
      unfold coverFB
      rw [Bool.or_eq_true]
      rcases hcov with hp | ⟨e', hp, hob⟩
      · exact Or.inl ((gpoBSpec _ _ _).2 hp)
      · refine Or.inr ((existsbExistsTrue _ _).2 ⟨e', ?_, ?_⟩)
        · rcases hp with rfl | hp
          · exact (geventsSpec _ _).2 (sfMarkSome _ _ hf.2)
          · exact (gpoGevents _ _ _ hp).1
        · rw [Bool.and_eq_true, Bool.or_eq_true]
          refine ⟨?_, (gmoLtBSpec _ _ _).2 (obCatSubGmo GD s e' hc (gobExplCat _ _ _ hob))⟩
          rcases hp with rfl | hp
          · exact Or.inl (decide_eq_true rfl)
          · exact Or.inr ((gpoBSpec _ _ _).2 hp)
    simp [hc1, hc3] at H
  · exact of_decide_eq_true H

end checkersF

/-! # 5. The witnesses, sfence = the MARKER (Q7: `LFence false false false false` where
`LFetchSf` was — AxPtProt2's `gad`/`gsf`/`gsfok` rows) -/

/-! ## 5.1 `GPadF`: install, sfence (marker), walk, Svadu A write-back, load -/

/-- = AxPtProt2's `gad`. -/
def gadF : Gdexec := gad

def GPadF : Gptw :=
  mkptw gadF [((0, 2), (0, 4)), ((0, 3), (0, 4))] [(0, 1)]

theorem gadFModel : ptwModelF GPadF := ptwModelFBSound _ _ _ (by decide +kernel)

theorem gAdSoundF :
    ptwModelF GPadF ∧
    gsfenceF GPadF (0, 1) ∧
    ptDisc (gpG GPadF) 0 (pteVar AxPtProt2.w0) 1 ∧
    (∀ x, greadsWord (gpG GPadF) (0, 2) 0 x →
      pteVar AxPtProt2.w0 x ∧ AxPtProt2.paOf x 0x10 = 0x80001010) ∧
    (∀ x, greadsWord (gpG GPadF) (0, 3) 0 x → pteVar AxPtProt2.w0 x) ∧
    gwritesWord (gpG GPadF) (0, 3) 0 w1 ∧ w1 ≠ AxPtProt2.w0 ∧ pteVar AxPtProt2.w0 w1 ∧
    GPadF.gpFor (0, 2) = some (0, 4) ∧
    greadsByte (gpG GPadF) (0, 4) (AxPtProt2.paOf AxPtProt2.w0 0x10) 0 0 ∧
    agreesAt GPadF 0 (0, 2) (0, 4) := by
  obtain ⟨_, ⟨hwf, _, _, hat, _, _⟩, ⟨hwv, hsf, hada, _, _⟩⟩ := gadFModel
  have hi : gwritesWord (gpG GPadF) (0, 0) 0 AxPtProt2.w0 :=
    gwritesWordBSound _ _ _ _ (by decide +kernel)
  have hix : gwix (gpG GPadF) (0, 0) = 1 := by decide +kernel
  have hw1 : gwritesWord (gpG GPadF) (0, 3) 0 w1 := gwritesWordBSound _ _ _ _ (by decide +kernel)
  have hf : gsfenceF GPadF (0, 1) := ⟨by decide +kernel, sfMarkBSound _ _ (by decide +kernel)⟩
  have hdisc : ptDisc (gpG GPadF) 0 (pteVar AxPtProt2.w0) 1 := by
    rw [← hix]
    apply ptDiscOfWriters GPadF 0 (pteVar AxPtProt2.w0) (0, 0) AxPtProt2.w0 hwf hwv hat hada
      (mixClosedVar AxPtProt2.w0) hi (pteVarRefl AxPtProt2.w0)
    · rw [hix]
      exact noKernelWritesBSound gadF _ [(0, 1)] 0 1 _ (by decide +kernel)
    · intro u j v _ hu hwu
      obtain ⟨e, hin, _⟩ := gwalkMk gadF _ [(0, 1)] u hu
      simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hin
      rcases hin with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exfalso
        have h := (gwritesByteBytes _ _ _ _).1 hwu
        have he : gwrBytes (gpG GPadF) (0, 2) = [] := rfl
        rw [he] at h
        cases h
      · obtain ⟨hr, _, _⟩ :=
          readsWordAfterBSound (gpG GPadF) (0, 3) 0 AxPtProt2.w0 1 (by decide +kernel)
        exact rmwClassOkUpdate _ _ 0 AxPtProt2.w0 AxPtProt2.w0 w1 (.Load .Data) hr hw1 w1Update
  have hpin : ∀ r x, gwalk GPadF r → (r = (0, 2) ∨ r = (0, 3)) →
      greadsWord (gpG GPadF) r 0 x → pteVar AxPtProt2.w0 x := by
    intro r x hr hrr hx
    have hcov : sfCoversF GPadF (0, 0) (0, 1) := Or.inl ((gpoBSpec _ _ _).1 (by decide +kernel))
    refine walkAfterSfenceF GPadF (0, 1) r (0, 0) 0 AxPtProt2.w0 _ x hwf hwv hsf hf hr ?_ hi hcov
      (by rw [hix]; exact hdisc) (mixClosedVar AxPtProt2.w0) hx
    apply (gpoBSpec _ _ _).1
    rcases hrr with rfl | rfl <;> decide +kernel
  have hw1v : pteVar AxPtProt2.w0 w1 :=
    updatePTEBitsVariant AxPtProt2.w0 AxPtProt2.w0 w1 (.Load .Data) (pteVarRefl AxPtProt2.w0)
      w1Update
  refine ⟨gadFModel, hf, hdisc, fun x hx => ?_,
    fun x hx => hpin (0, 3) x (by unfold gwalk; decide +kernel) (Or.inr rfl) hx, hw1,
    fun h => w1NeW0 (by rw [h]), hw1v, by decide +kernel, ?_, ?_⟩
  · have V := hpin (0, 2) x (by unfold gwalk; decide +kernel) (Or.inl rfl) hx
    refine ⟨V, ?_⟩
    show ((PPN_of_PTE x).toNat : Int) * 4096 + 0x10 = 0x80001010
    rw [pteVarPpn _ _ V]
    exact paOfW0
  · rw [paOfW0]
    exact (grbBSpec _ _ _ _ _).1 (by decide +kernel)
  · refine agreesAtOfDisc GPadF 0 AxPtProt2.w0 (0, 0) (0, 2) (0, 4) hwf hwv
      (by unfold gwalk; decide +kernel) hi
      ((gmoLtBSpec _ _ _).1 (by decide +kernel)) (by rw [hix]; exact hdisc) ?_
    rw [hix]
    exact (readsWordAfterBSound (gpG GPadF) (0, 2) 0 AxPtProt2.w0 1 (by decide +kernel)).2.1

/-! ## 5.2 The race (no sfence on hart 0): unchanged graph, new model -/

theorem raceBreaksAgreeF :
    ptwModelF GPrace ∧ rvwmoCatConsistent grace ∧
    GPrace.gpFor (0, 0) = some (0, 1) ∧
    gwritesWord (gpG GPrace) (1, 0) 0 wNew ∧
    gmoLt (gpG GPrace) (1, 0) (0, 1) ∧
    (∀ x, greadsWord (gpG GPrace) (0, 0) 0 x → x = wOld) ∧
    PPN_of_PTE wOld ≠ PPN_of_PTE wNew ∧
    ¬ agreesAt GPrace 0 (0, 0) (0, 1) :=
  ⟨ptwModelFBSound _ _ _ (by decide +kernel), raceBreaksAgree.2⟩

/-! ## 5.3 H5'.2 (marker form) is still a GENUINELY NEW hardware clause

hart 1: (1,0) sd wNew → [0]; (1,1) fence w,w; (1,2) sd 1 → [64] (flag)
hart 0: (0,0) ld [64] = 1; (0,1) sfence.vma MARKER; (0,2) walker read [0]; (0,3) ld (data) -/

/-- = AxPtProt2's `gsfRows`. -/
def gsfRowsF (wr : List Nat) (wv : BitVec 64) (dpa : Int) : List (List Lbl) :=
  gsfRows wr wv dpa

/-- STALE (= AxPtProt2's `gsf`). -/
def gsfF : Gdexec := gsf
def GPsfF : Gptw := mkptw gsfF [((0, 2), (0, 3))] [(0, 1)]

/-- FRESH (= AxPtProt2's `gsfok`). -/
def gsfokF : Gdexec := gsfok
def GPsfokF : Gptw := mkptw gsfokF [((0, 2), (0, 3))] [(0, 1)]

theorem gsfCoverF (GD : Gdexec) (fl : List (Geid × Geid)) (sfl : List Geid) :
    gppoCatB GD (1, 0) (1, 2) = true →
    grfeB GD.gdG (1, 2) (0, 0) = true →
    gpoB GD.gdG (0, 0) (0, 1) = true →
    assoc fl (1, 0) = none → assoc fl (1, 2) = none → assoc fl (0, 0) = none →
    sfCoversF (mkptw GD fl sfl) (1, 0) (0, 1) := by
  intro hp hr hpo hn10 hn12 hn00
  refine Or.inr ⟨(0, 0), Or.inr ((gpoBSpec _ _ _).1 hpo), ?_⟩
  exact tc_l ⟨Or.inl ((gppoCatBSpec _ _ _).1 hp), hn10, hn12⟩
    (tc_once ⟨Or.inr (Or.inr (Or.inl ((grfeBSpec _ _ _).1 hr))), hn12, hn00⟩)

theorem gsfCatF : rvwmoCatConsistent gsfF := catConsistentBSound _ (by decide +kernel)

theorem gsfNotH5F : ¬ h5SfenceF GPsfF := by
  intro H
  have hcov : sfCoversF GPsfF (1, 0) (0, 1) :=
    gsfCoverF gsfF _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have hle : gwix (gpG GPsfF) (1, 0) ≤ 0 :=
    H (0, 1) (0, 2) 0 0 (nthByte (n := 8) wOld 0) (1, 0) (nthByte (n := 8) wNew 0)
      ⟨by decide +kernel, sfMarkBSound _ _ (by decide +kernel)⟩
      (by unfold gwalk; decide +kernel)
      ((gpoBSpec _ _ _).1 (by decide +kernel))
      ((grbBSpec _ _ _ _ _).1 (by decide +kernel))
      ((gwbBSpec _ _ _ _).1 (by decide +kernel)) hcov
  have hix : gwix (gpG GPsfF) (1, 0) = 1 := by decide +kernel
  omega

/-- The ONLY obstruction is H5'.2: the rest of the marker-form model holds. -/
theorem gsfExplicitF :
    ptwWfF GPsfF ∧ ptwExplicitConsistent GPsfF ∧ h5WalkValue GPsfF ∧
    h5AdAtomic GPsfF ∧ h5AdBefore GPsfF ∧ h5SfenceAdF GPsfF := by
  have hc := gsfCatF
  -- the same graph with the sfence-dependent checker of H5'.2 dropped
  have H0 : ptwModelB gsfF [((0, 2), (0, 3))] [] = true := by decide +kernel
  obtain ⟨⟨W1, W2, _⟩, _, ⟨_, _, A, B, _⟩⟩ := ptwModelBSound _ _ _ H0
  refine ⟨⟨W1, W2, ?_⟩, ptwExplicitOfCat _ hc, h5WalkValueOfCat _ hc, A, B, ?_⟩
  · intro f hf
    have hf' : decide (f ∈ [((0 : Nat), (1 : Nat))]) = true := hf
    have hf'' := of_decide_eq_true hf'
    simp only [List.mem_singleton] at hf''
    subst hf''
    exact sfMarkBSound _ _ (by decide +kernel)
  · intro u f s _ hu hwu _ _ _ _
    exfalso
    obtain ⟨e, hin, _⟩ := gwalkMk gsfF _ [(0, 1)] u hu
    simp only [List.mem_singleton, Prod.mk.injEq] at hin
    obtain ⟨rfl, rfl⟩ := hin
    have h := (glblBSpec _ _ _).2 hwu
    revert h
    decide +kernel

theorem gsfokSoundF :
    ptwModelF GPsfokF ∧
    (∀ x, greadsWord (gpG GPsfokF) (0, 2) 0 x →
      pteVar wNew x ∧ AxPtProt2.paOf x 0x10 = 0x80002010) ∧
    agreesAt GPsfokF 0 (0, 2) (0, 3) := by
  have hm : ptwModelF GPsfokF := ptwModelFBSound _ _ _ (by decide +kernel)
  obtain ⟨_, ⟨hwf, _, _, hat, _, _⟩, ⟨hwv, hsf, hada, _, _⟩⟩ := hm
  have hi : gwritesWord (gpG GPsfokF) (1, 0) 0 wNew :=
    gwritesWordBSound _ _ _ _ (by decide +kernel)
  have hix : gwix (gpG GPsfokF) (1, 0) = 1 := by decide +kernel
  have hdisc : ptDisc (gpG GPsfokF) 0 (pteVar wNew) (gwix (gpG GPsfokF) (1, 0)) := by
    apply ptDiscOfWriters GPsfokF 0 (pteVar wNew) (1, 0) wNew hwf hwv hat hada
      (mixClosedVar wNew) hi (pteVarRefl wNew)
    · rw [hix]
      exact noKernelWritesBSound gsfokF _ [(0, 1)] 0 1 _ (by decide +kernel)
    · exact noWalkerWritesBSound gsfokF _ [(0, 1)] 0 _ (by decide +kernel)
  have hcov : sfCoversF GPsfokF (1, 0) (0, 1) :=
    gsfCoverF gsfokF _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have hf : gsfenceF GPsfokF (0, 1) :=
    ⟨by decide +kernel, sfMarkBSound _ _ (by decide +kernel)⟩
  have hr : gwalk GPsfokF (0, 2) := by unfold gwalk; decide +kernel
  have hfr : WeakRvwmoGraph.gpo (gpG GPsfokF) (0, 1) (0, 2) :=
    (gpoBSpec _ _ _).1 (by decide +kernel)
  have hra := readsAfterOfSfenceF GPsfokF _ _ _ 0 wNew hsf hf hr hfr hi hcov
  refine ⟨ptwModelFBSound _ _ _ (by decide +kernel), fun x hx => ?_,
    agreesAtOfDisc GPsfokF 0 wNew (1, 0) _ _ hwf hwv hr hi
      ((gmoLtBSpec _ _ _).1 (by decide +kernel)) hdisc hra⟩
  have V := walkAfterSfenceF GPsfokF _ _ _ 0 wNew _ x hwf hwv hsf hf hr hfr hi hcov hdisc
    (mixClosedVar wNew) hx
  refine ⟨V, ?_⟩
  show ((PPN_of_PTE x).toNat : Int) * 4096 + 0x10 = 0x80002010
  rw [pteVarPpn _ _ V]
  exact paOfWNew

/-! ## 5.4 NON-VACUITY of the §3 equivalence: `gad` with the marker where `LFetchSf` was AND
Rocq's marker right after it (two adjacent markers); AxPtProt2's checker proves `ptwModel` at
either tag, the §3 iff (its inertness premise decided by `AxSfence.noObInto`) yields
`ptwModelF` at the first. -/

def gadm : Gdexec :=
  ⟨⟨imgz,
    [[LStore false 0 (wb8 AxPtProt2.w0) .WCplain,
      LFence false false false false,
      LFence false false false false,
      LLoad false 0 (ts8 1) (wb8 AxPtProt2.w0),
      LRmw false false 0 (ts8 1) (wb8 AxPtProt2.w0) (wb8 w1) .WCplain,
      LLoad false 0x80001010 [0] [0]]],
    [(0, 0), (0, 3), (0, 4), (0, 5)]⟩, []⟩

def flM : List (Geid × Geid) := [((0, 3), (0, 5)), ((0, 4), (0, 5))]

theorem gadmBoth :
    ptwModel (mkptw gadm flM [(0, 2)]) ∧ ptwModelF (mkptw gadm flM [(0, 1)]) := by
  have hold : ptwModel (mkptw gadm flM [(0, 2)]) := ptwModelBSound _ _ _ (by decide +kernel)
  refine ⟨hold, ?_⟩
  have hc : rvwmoCatConsistent gadm := catConsistentBSound _ (by decide +kernel)
  refine (ptwModelMarkerIff (mkptw gadm flM [(0, 1)]) ?_).1
    (ptwModelBSound _ _ _ (by decide +kernel))
  intro s f hf
  have hf' : decide (f ∈ [((0 : Nat), (1 : Nat))]) = true := hf
  have hf'' := of_decide_eq_true hf'
  simp only [List.mem_singleton] at hf''
  subst hf''
  exact AxSfence.noObInto gadm flM [(0, 1)] (0, 1) hc (by decide +kernel) s

end Weak
