/-
Weak: **blocker (i) of the A2a walker bridge — the sfence.vma "marker" of the PTW model
(H5') is the sfence.vma instruction's OWN FETCH EVENT** (AxSL tier; owner-approved).

Rocq: `iris/AxSfence.v` @ xxvzwolszwmp.

The Rocq header, in substance.  Sail's `execute_SFENCE_VMA` emits no memory / barrier event
(it only flushes the `tlb` register), and AxOpsem cannot step past a row item without
emitting its label — a synthetic marker item makes the hart STUCK.  Every H5' clause uses
the sfence ONLY for its program-order position, and the instruction's fetch (a real row
item) has exactly that position.  PURE (graph level).  Companion: AxSfence2 (the WPd leaf).

§1  THE DECODE PREDICATE.  `sfWord w`: the 32-bit word decodes, at every state with
    `misa = misaC` and `cfgOk`, to `SFENCE_VMA (rs1, rs2)`.  `sfBytes vs`: `vs` are the 4
    little-endian bytes of such a word.  xv6's word `WSfence = 0x12000073`
    (`sfence.vma zero,zero`): `sfWordXv6`.  Non-triviality: AxSfence2's `sf_word_not_fence`.
§2  THE RESTATED MODEL.  `sfFetch G f`: `f`'s label is a plain load of `sfBytes`.
    `gsfenceF GP f := gpSf f ∧ sfFetch`.  `sfCoversF GP s f`: `s` po-before `f`, or
    explicitly-ob-before an event po-AT-OR-before `f`.  `h5SfenceF` (H5'.2), `h5SfenceAdF`
    (H5'.5), `ptwWfF`, `ptwHwF`, `ptwModelF`, the row tag `gpSfRow`.  H5'.1/.3/.4 and the
    explicit part are unchanged.
§3  EXACT EQUIVALENCE with the marker form on graphs where an explicit
    `LFence false false false false` marker sits RIGHT AFTER each tagged sfence fetch:
    `ptwModelMarkerIff`.  Non-vacuous (`gadmBoth`).
§4  CHECKERS for `ptwModelF` (`ptwModelFBSound`; the sfence-free clauses are delegated to
    `AxPtProt2.ptwModelB` at an EMPTY marker list).
§5  THE WITNESSES re-derived with the sfence = the fetch of xv6's sfence.vma word (text bytes
    in the image at `PCsf = 0x1000`, read at t = 0): `gAdSoundF`, `raceBreaksAgreeF`,
    `gsfCatF` + `gsfNotH5F` (H5'.2 is still a genuinely new clause in the fetch form),
    `gsfExplicitF`, `gsfokSoundF`, `gadmBoth`.
CONCERNS (Rocq header, unchanged): (1) the fetch is treated as an EXPLICIT read by
`ptwExplicitConsistent` (stronger than hardware, harmless for immutable kernel text);
(2) `sfCoversF` counts stores ob-before the fetch itself — exactly the old marker semantics
(§3); (3) `sfWord` is a ∀-state decode fact (non-triviality in AxSfence2).

O2 / D1 (as ported): fetches stay graph reads (`LLoad false …`) in the AxSL tier — exactly
this file's modelling; no access kinds appear.
STAGE C (D1 reversed, `notes/weak-port-o2-stageC.md` item 19) — HELD, rows UNCHANGED.  This
file's fetch literals (`LFetchSf` at row position 1 of `gadF`, `gsfRowsF`, `gadm`) are not
incidental: the sfence.vma's own fetch is the ONLY graph event the model gives the sfence
(`sfFetch`, `gsfenceF`, `ptwWfF`'s third clause, `sfFetchB`).  Removing them leaves no
event for `gpSf` to tag, so no re-index keeps the theorems' meaning (`gAdSoundF`,
`gsfNotH5F`, `gsfokSoundF`, `gadmBoth` would become vacuous or false).  Re-locating the
sfence (e.g. a row-position cut instead of an event) is a model change for the owner.

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

**Rocq → Lean name map.**  `sf_word` ↦ `sfWord`; `wb32`; `word_bytes` ↦ `wordBytes`;
`sf_bytes` ↦ `sfBytes`; `W_sfence` ↦ `WSfence`; `sf_word_xv6` ↦ `sfWordXv6`;
`sf_bytes_xv6` ↦ `sfBytesXv6`; `sf_fetch` ↦ `sfFetch`; `gsfence_f` ↦ `gsfenceF`;
`sf_covers_f` ↦ `sfCoversF`; `h5_sfence_f` ↦ `h5SfenceF`; `h5_sfence_ad_f` ↦
`h5SfenceAdF`; `ptw_wf_f` ↦ `ptwWfF`; `ptw_hw_f` ↦ `ptwHwF`; `ptw_model_f` ↦ `ptwModelF`;
`gp_sf_row` ↦ `gpSfRow`; `gp_sf_row_spec` ↦ `gpSfRowSpec`; `walk_after_sfence_f` ↦
`walkAfterSfenceF`; `reads_after_of_sfence_f` ↦ `readsAfterOfSfenceF`;
`sf_covers_f_of_old` ↦ `sfCoversFOfOld`; `sf_fetch_some` ↦ `sfFetchSome`;
`gpo_into_next` ↦ `gpoIntoNext`; `gpo_next_from` ↦ `gpoNextFrom`; `gpo_next_to` ↦
`gpoNextTo`; `reads_not_fence` ↦ `readsNotFence`; `writes_not_load` ↦ `writesNotLoad`;
`isw_not_load` ↦ `iswNotLoad`; `isw_not_fence` ↦ `iswNotFence`; `gsfence_m_iff` ↦
`gsfenceMIff`; `covers_iff` ↦ `coversIff`; `h5_sfence_iff` ↦ `h5SfenceIff`;
`h5_sfence_ad_iff` ↦ `h5SfenceAdIff`; `ptw_model_marker_iff` ↦ `ptwModelMarkerIff`;
`sf_fetch_b` ↦ `sfFetchB`; `sf_fetch_b_sound` ↦ `sfFetchBSound`; `cover_f_b` ↦ `coverFB`;
`h5_sfence_f_b` ↦ `h5SfenceFB`; `ptw_model_f_b` ↦ `ptwModelFB`; `gsfence_f_mk` ↦
`gsfenceFMk`; `ptw_model_f_b_sound` ↦ `ptwModelFBSound`; `PCsf`; `with_text` ↦ `withText`;
`LFetchSf`; `gad_f` ↦ `gadF`; `GPad_f` ↦ `GPadF`; `gad_f_model` ↦ `gadFModel`;
`g_ad_sound_f` ↦ `gAdSoundF`; `race_breaks_agree_f` ↦ `raceBreaksAgreeF`; `gsf_rows_f` ↦
`gsfRowsF`; `gsf_f` ↦ `gsfF`; `GPsf_f` ↦ `GPsfF`; `gsfok_f` ↦ `gsfokF`; `GPsfok_f` ↦
`GPsfokF`; `gsf_cover_f` ↦ `gsfCoverF`; `gsf_cat_f` ↦ `gsfCatF`; `gsf_not_h5_f` ↦
`gsfNotH5F`; `gsf_explicit_f` ↦ `gsfExplicitF`; `gsfok_sound_f` ↦ `gsfokSoundF`; `gadm`;
`fl_m` ↦ `flM`; `gadm_both` ↦ `gadmBoth`.
Lean-only (file-qualified): `AxSfence.drefSf` (deviation 3).

**Dropped:** nothing.
-/
import Weak.AxPtProt2
import Weak.WeakFunnel

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

/-! # 2. The restated model: the sfence is its own fetch event -/

def sfFetch (G : Gexec) (f : Geid) : Prop :=
  ∃ base ts vs, gxLbl G f = some (LLoad false base ts vs) ∧ sfBytes vs

def gsfenceF (GP : Gptw) (f : Geid) : Prop :=
  GP.gpSf f = true ∧ sfFetch (gpG GP) f

def sfCoversF (GP : Gptw) (s f : Geid) : Prop :=
  WeakRvwmoGraph.gpo (gpG GP) s f ∨
  ∃ e, (e = f ∨ WeakRvwmoGraph.gpo (gpG GP) e f) ∧ gobExpl GP s e

/-- H5'.2, fetch form. -/
def h5SfenceF (GP : Gptw) : Prop :=
  ∀ f r a t v s v', gsfenceF GP f → gwalk GP r → WeakRvwmoGraph.gpo (gpG GP) f r →
    greadsByte (gpG GP) r a t v → gwritesByte (gpG GP) s a v' →
    sfCoversF GP s f → gwix (gpG GP) s ≤ t

/-- H5'.5, fetch form. -/
def h5SfenceAdF (GP : Gptw) : Prop :=
  ∀ u f s, gsfenceF GP f → gwalk GP u → glblIs (gpG GP) u lbIsW →
    WeakRvwmoGraph.gpo (gpG GP) u f → WeakRvwmoGraph.gpo (gpG GP) f s → GP.gpFor s = none →
    glblIs (gpG GP) s lbIsW → gmoLt (gpG GP) u s

def ptwWfF (GP : Gptw) : Prop :=
  (∀ u e, GP.gpFor u = some e → WeakRvwmoGraph.gpo (gpG GP) u e ∧ GP.gpFor e = none) ∧
  (∀ u, gwalk GP u → glblIs (gpG GP) u lbIsW → glblIs (gpG GP) u lbIsR) ∧
  (∀ f, GP.gpSf f = true → sfFetch (gpG GP) f)

def ptwHwF (GP : Gptw) : Prop :=
  h5WalkValue GP ∧ h5SfenceF GP ∧ h5AdAtomic GP ∧ h5AdBefore GP ∧ h5SfenceAdF GP

def ptwModelF (GP : Gptw) : Prop :=
  ptwWfF GP ∧ ptwExplicitConsistent GP ∧ ptwHwF GP

/-- The row-level sfence tag: `ks` are the row positions of hart `i`'s sfence.vma FETCH
items (the row-level model is in AxSfence2). -/
def gpSfRow (i : Nat) (ks : List Nat) (e : Geid) : Bool :=
  decide (e.1 = i ∧ e.2 ∈ ks)

theorem gpSfRowSpec (i : Nat) (ks : List Nat) (e : Geid) :
    gpSfRow i ks e = true ↔ e.1 = i ∧ e.2 ∈ ks := by
  unfold gpSfRow
  exact decide_eq_true_iff

/-- The H5' consumers, fetch form (twins of `walkAfterSfence` / `readsAfterOfSfence`). -/
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

/-! # 3. Exact equivalence with the marker form -/

theorem sfFetchSome (G : Gexec) (f : Geid) : sfFetch G f → (gxLbl G f).isSome = true := by
  rintro ⟨_, _, _, hl, _⟩
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

/-! Section `marker` (Rocq): the sfence fetches are tagged (`sff`), each is followed by a
fence marker, and the marker tags (`sfm`) are exactly the successors of the fetch tags. -/

theorem gsfenceMIff (GD : Gdexec) (gf : Geid → Option Geid) (sff sfm : Geid → Bool)
    (Hff : ∀ f, sff f = true → sfFetch GD.gdG f)
    (Hmk : ∀ f, sff f = true → gxLbl GD.gdG (f.1, f.2 + 1) = some (LFence false false false false))
    (Hcorr : ∀ m, sfm m = true ↔ ∃ f, sff f = true ∧ m = (f.1, f.2 + 1)) (m : Geid) :
    gsfence ⟨GD, gf, sfm⟩ m ↔ ∃ f, gsfenceF ⟨GD, gf, sff⟩ f ∧ m = (f.1, f.2 + 1) := by
  constructor
  · rintro ⟨hm, _⟩
    obtain ⟨f, hf, rfl⟩ := (Hcorr m).1 hm
    exact ⟨f, ⟨hf, Hff f hf⟩, rfl⟩
  · rintro ⟨f, ⟨hf, _⟩, rfl⟩
    exact ⟨(Hcorr _).2 ⟨f, hf, rfl⟩, Hmk f hf⟩

theorem coversIff (GD : Gdexec) (gf : Geid → Option Geid) (sff sfm : Geid → Bool)
    (Hff : ∀ f, sff f = true → sfFetch GD.gdG f)
    (Hmk : ∀ f, sff f = true → gxLbl GD.gdG (f.1, f.2 + 1) = some (LFence false false false false))
    (s f : Geid) (a : Int) (v : BitVec 8) :
    sff f = true → gwritesByte GD.gdG s a v →
    (sfCovers ⟨GD, gf, sfm⟩ s (f.1, f.2 + 1) ↔ sfCoversF ⟨GD, gf, sff⟩ s f) := by
  intro hf hw
  have hlf := sfFetchSome _ _ (Hff f hf)
  have hlm : (gxLbl GD.gdG (f.1, f.2 + 1)).isSome = true := by rw [Hmk f hf]; rfl
  obtain ⟨base, ts, vs, hfl, _⟩ := Hff f hf
  have hI := fun x => gpoIntoNext GD.gdG f x hlf hlm
  constructor
  · rintro (hp | ⟨e, hp, hob⟩)
    · rcases (hI s).1 hp with hp | rfl
      · exact Or.inl hp
      · exact absurd hw (writesNotLoad _ _ _ _ _ _ _ _ hfl)
    · exact Or.inr ⟨e, ((hI e).1 hp).symm, hob⟩
  · rintro (hp | ⟨e, he, hob⟩)
    · exact Or.inl ((hI s).2 (Or.inl hp))
    · exact Or.inr ⟨e, (hI e).2 he.symm, hob⟩

theorem h5SfenceIff (GD : Gdexec) (gf : Geid → Option Geid) (sff sfm : Geid → Bool)
    (Hff : ∀ f, sff f = true → sfFetch GD.gdG f)
    (Hmk : ∀ f, sff f = true → gxLbl GD.gdG (f.1, f.2 + 1) = some (LFence false false false false))
    (Hcorr : ∀ m, sfm m = true ↔ ∃ f, sff f = true ∧ m = (f.1, f.2 + 1)) :
    h5Sfence ⟨GD, gf, sfm⟩ ↔ h5SfenceF ⟨GD, gf, sff⟩ := by
  constructor
  · intro H f r a t v s v' hf hr hfr hrd hwr hcov
    obtain ⟨hf1, hf2⟩ := hf
    have hlm : (gxLbl GD.gdG (f.1, f.2 + 1)).isSome = true := by rw [Hmk f hf1]; rfl
    refine H (f.1, f.2 + 1) r a t v s v' ?_ hr ?_ hrd hwr ?_
    · exact (gsfenceMIff GD gf sff sfm Hff Hmk Hcorr _).2 ⟨f, ⟨hf1, hf2⟩, rfl⟩
    · refine gpoNextTo _ f r hlm hfr ?_
      rintro rfl
      exact readsNotFence _ _ _ _ _ _ _ _ _ (Hmk f hf1) hrd
    · exact (coversIff GD gf sff sfm Hff Hmk s f _ _ hf1 hwr).2 hcov
  · intro H m r a t v s v' hm hr hmr hrd hwr hcov
    obtain ⟨f, hf, rfl⟩ := (gsfenceMIff GD gf sff sfm Hff Hmk Hcorr m).1 hm
    exact H f r a t v s v' hf hr (gpoNextFrom _ f r (sfFetchSome _ _ hf.2) hmr) hrd hwr
      ((coversIff GD gf sff sfm Hff Hmk s f _ _ hf.1 hwr).1 hcov)

theorem h5SfenceAdIff (GD : Gdexec) (gf : Geid → Option Geid) (sff sfm : Geid → Bool)
    (Hff : ∀ f, sff f = true → sfFetch GD.gdG f)
    (Hmk : ∀ f, sff f = true → gxLbl GD.gdG (f.1, f.2 + 1) = some (LFence false false false false))
    (Hcorr : ∀ m, sfm m = true ↔ ∃ f, sff f = true ∧ m = (f.1, f.2 + 1)) :
    h5SfenceAd ⟨GD, gf, sfm⟩ ↔ h5SfenceAdF ⟨GD, gf, sff⟩ := by
  constructor
  · intro H u f s hf hu hwu huf hfs hs hws
    obtain ⟨hf1, hf2⟩ := hf
    have hlf := sfFetchSome _ _ hf2
    have hlm : (gxLbl GD.gdG (f.1, f.2 + 1)).isSome = true := by rw [Hmk f hf1]; rfl
    refine H u (f.1, f.2 + 1) s ?_ hu hwu ?_ ?_ hs hws
    · exact (gsfenceMIff GD gf sff sfm Hff Hmk Hcorr _).2 ⟨f, ⟨hf1, hf2⟩, rfl⟩
    · exact (gpoIntoNext _ f u hlf hlm).2 (Or.inl huf)
    · refine gpoNextTo _ f s hlm hfs ?_
      rintro rfl
      exact iswNotFence _ _ _ _ _ _ (Hmk f hf1) hws
  · intro H u m s hm hu hwu hum hms hs hws
    obtain ⟨f, hf, rfl⟩ := (gsfenceMIff GD gf sff sfm Hff Hmk Hcorr m).1 hm
    have hlf := sfFetchSome _ _ hf.2
    have hlm : (gxLbl GD.gdG (f.1, f.2 + 1)).isSome = true := by rw [Hmk f hf.1]; rfl
    refine H u f s hf hu hwu ?_ (gpoNextFrom _ f s hlf hms) hs hws
    rcases (gpoIntoNext _ f u hlf hlm).1 hum with h | rfl
    · exact h
    · exfalso
      obtain ⟨_, _, _, hfl, _⟩ := hf.2
      exact iswNotLoad _ _ _ _ _ _ hfl hwu

/-- THE RELATION: exact equivalence. -/
theorem ptwModelMarkerIff (GD : Gdexec) (gf : Geid → Option Geid) (sff sfm : Geid → Bool)
    (Hff : ∀ f, sff f = true → sfFetch GD.gdG f)
    (Hmk : ∀ f, sff f = true → gxLbl GD.gdG (f.1, f.2 + 1) = some (LFence false false false false))
    (Hcorr : ∀ m, sfm m = true ↔ ∃ f, sff f = true ∧ m = (f.1, f.2 + 1)) :
    ptwModel ⟨GD, gf, sfm⟩ ↔ ptwModelF ⟨GD, gf, sff⟩ := by
  unfold ptwModel ptwModelF ptwHw ptwHwF
  rw [h5SfenceIff GD gf sff sfm Hff Hmk Hcorr, h5SfenceAdIff GD gf sff sfm Hff Hmk Hcorr]
  constructor
  · rintro ⟨⟨W1, W2, _⟩, E, HW⟩
    exact ⟨⟨W1, W2, Hff⟩, E, HW⟩
  · rintro ⟨⟨W1, W2, _⟩, E, HW⟩
    refine ⟨⟨W1, W2, ?_⟩, E, HW⟩
    intro m hm
    obtain ⟨f, hf, rfl⟩ := (Hcorr m).1 hm
    exact Hmk f hf

/-! # 4. Checkers for `ptwModelF` -/

def sfFetchB (G : Gexec) (f : Geid) : Bool :=
  match gxLbl G f with
  | some (LLoad false _ _ vs) => decide (vs = wordBytes WSfence)
  | _ => false

theorem sfFetchBSound (G : Gexec) (f : Geid) : sfFetchB G f = true → sfFetch G f := by
  intro h
  unfold sfFetchB at h
  cases hl : gxLbl G f with
  | none => simp [hl] at h
  | some l =>
    rw [hl] at h
    cases l with
    | LLoad aq base ts vs =>
      cases aq
      · have hv : vs = wordBytes WSfence := of_decide_eq_true h
        subst hv
        exact ⟨base, ts, _, hl, sfBytesXv6⟩
      · simp at h
    | LStore => simp at h
    | LFence => simp at h
    | LRmw => simp at h

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

/-- The sfence-free clauses are checked by AxPtProt2's checker at an EMPTY marker list;
H5'.5's checker `h5SfenceAdB` is label-agnostic in the sfence list and is reused as is. -/
def ptwModelFB : Bool :=
  ptwModelB GD fl [] && sfl.all (sfFetchB GD.gdG) && h5SfenceFB GD fl sfl &&
  h5SfenceAdB GD fl sfl

theorem gsfenceFMk (f : Geid) : gsfenceF (mkptw GD fl sfl) f → f ∈ sfl := by
  rintro ⟨h, _⟩
  have h' : decide (f ∈ sfl) = true := h
  exact of_decide_eq_true h'

theorem ptwModelFBSound : ptwModelFB GD fl sfl = true → ptwModelF (mkptw GD fl sfl) := by
  intro H
  unfold ptwModelFB at H
  simp only [Bool.and_eq_true] at H
  obtain ⟨⟨⟨H0, Hsfl⟩, Hsf⟩, Hsfad⟩ := H
  have Hcat : catConsistentB GD = true := by
    have H0' := H0
    unfold ptwModelB at H0'
    simp only [Bool.and_eq_true] at H0'
    exact H0'.1.1.1.1.1
  have hc := catConsistentBSound GD Hcat
  obtain ⟨⟨W1, W2, _⟩, E, ⟨V, _, A, B, _⟩⟩ := ptwModelBSound GD fl [] H0
  rw [forallbForallTrue] at Hsfl
  refine ⟨⟨W1, W2, ?_⟩, E, V, ?_, A, B, ?_⟩
  · intro f hf
    have hf' : decide (f ∈ sfl) = true := hf
    exact sfFetchBSound _ _ (Hsfl f (of_decide_eq_true hf'))
  · -- H5'.2, fetch form
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
            · exact (geventsSpec _ _).2 (sfFetchSome _ _ hf.2)
            · exact (gpoGevents _ _ _ hp).1
          · rw [Bool.and_eq_true, Bool.or_eq_true]
            refine ⟨?_, (gmoLtBSpec _ _ _).2 (obCatSubGmo GD s e' hc (gobExplCat _ _ _ hob))⟩
            rcases hp with rfl | hp
            · exact Or.inl (decide_eq_true rfl)
            · exact Or.inr ((gpoBSpec _ _ _).2 hp)
      simp [hc1, hc3] at H
    · exact of_decide_eq_true H
  · -- H5'.5, fetch form
    intro u f s hf hu hwu huf hfs hs hws
    have hfin := gsfenceFMk GD fl sfl f hf
    obtain ⟨e, hin, _⟩ := gwalkMk GD fl sfl u hu
    unfold h5SfenceAdB at Hsfad
    have H := (forallbForallTrue _ _).1 Hsfad f hfin
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

end checkersF

/-! # 5. The witnesses, sfence = the fetch of xv6's sfence.vma word -/

/-- The text page: xv6's sfence.vma bytes at `PCsf`. -/
def PCsf : Int := 0x1000

def withText (img : Image) : Image := fun a =>
  if decide (PCsf ≤ a) && decide (a < PCsf + 4) then (wordBytes WSfence)[(a - PCsf).toNat]?
  else img a

/-- The fetch event of the sfence.vma instruction. -/
def LFetchSf : Lbl := LLoad false PCsf [0, 0, 0, 0] (wordBytes WSfence)

/-! ## 5.1 `GPadF`: install, sfence (fetch), walk, Svadu A write-back, load — the positions
are those of `gad` with the marker REPLACED by the fetch. -/

def gadF : Gdexec :=
  ⟨⟨withText imgz,
    [[LStore false 0 (wb8 AxPtProt2.w0) .WCplain,
      LFetchSf,
      LLoad false 0 (ts8 1) (wb8 AxPtProt2.w0),
      LRmw false false 0 (ts8 1) (wb8 AxPtProt2.w0) (wb8 w1) .WCplain,
      LLoad false 0x80001010 [0] [0]]],
    [(0, 0), (0, 1), (0, 2), (0, 3), (0, 4)]⟩, []⟩

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
  have hf : gsfenceF GPadF (0, 1) := ⟨by decide +kernel, sfFetchBSound _ _ (by decide +kernel)⟩
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

/-! ## 5.3 H5'.2 (fetch form) is still a GENUINELY NEW hardware clause

hart 1: (1,0) sd wNew → [0]; (1,1) fence w,w; (1,2) sd 1 → [64] (flag)
hart 0: (0,0) ld [64] = 1; (0,1) FETCH of sfence.vma; (0,2) walker read [0]; (0,3) ld (data) -/

def gsfRowsF (wr : List Nat) (wv : BitVec 64) (dpa : Int) : List (List Lbl) :=
  [[LLoad false 64 [2] [B1],
    LFetchSf,
    LLoad false 0 wr (wb8 wv),
    LLoad false dpa [0] [0]],
   [LStore false 0 (wb8 wNew) .WCplain,
    LFence false true false true,
    LStore false 64 [B1] .WCplain]]

/-- STALE. -/
def gsfF : Gdexec :=
  ⟨⟨withText imgOld, gsfRowsF (ts8 0) wOld 0x80001010,
    [(0, 2), (1, 0), (1, 2), (0, 0), (0, 1), (0, 3)]⟩, []⟩
def GPsfF : Gptw := mkptw gsfF [((0, 2), (0, 3))] [(0, 1)]

/-- FRESH. -/
def gsfokF : Gdexec :=
  ⟨⟨withText imgOld, gsfRowsF (ts8 1) wNew 0x80002010,
    [(1, 0), (1, 2), (0, 0), (0, 1), (0, 2), (0, 3)]⟩, []⟩
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
      ⟨by decide +kernel, sfFetchBSound _ _ (by decide +kernel)⟩
      (by unfold gwalk; decide +kernel)
      ((gpoBSpec _ _ _).1 (by decide +kernel))
      ((grbBSpec _ _ _ _ _).1 (by decide +kernel))
      ((gwbBSpec _ _ _ _).1 (by decide +kernel)) hcov
  have hix : gwix (gpG GPsfF) (1, 0) = 1 := by decide +kernel
  omega

/-- The ONLY obstruction is H5'.2: the rest of the fetch-form model holds. -/
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
    exact sfFetchBSound _ _ (by decide +kernel)
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
  have hf : gsfenceF GPsfokF (0, 1) := ⟨by decide +kernel, sfFetchBSound _ _ (by decide +kernel)⟩
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

/-! ## 5.4 NON-VACUITY of the §3 equivalence: `gad` with the fetch AND a marker right after
it; the OLD checker proves `ptwModel` with the marker tagged, the iff yields `ptwModelF`
with the fetch tagged. -/

def gadm : Gdexec :=
  ⟨⟨withText imgz,
    [[LStore false 0 (wb8 AxPtProt2.w0) .WCplain,
      LFetchSf,
      LFence false false false false,
      LLoad false 0 (ts8 1) (wb8 AxPtProt2.w0),
      LRmw false false 0 (ts8 1) (wb8 AxPtProt2.w0) (wb8 w1) .WCplain,
      LLoad false 0x80001010 [0] [0]]],
    [(0, 0), (0, 1), (0, 3), (0, 4), (0, 5)]⟩, []⟩

def flM : List (Geid × Geid) := [((0, 3), (0, 5)), ((0, 4), (0, 5))]

theorem gadmBoth :
    ptwModel (mkptw gadm flM [(0, 2)]) ∧ ptwModelF (mkptw gadm flM [(0, 1)]) := by
  have hold : ptwModel (mkptw gadm flM [(0, 2)]) := ptwModelBSound _ _ _ (by decide +kernel)
  refine ⟨hold, ?_⟩
  refine (ptwModelMarkerIff gadm (assoc flM) (fun f => decide (f ∈ [((0 : Nat), (1 : Nat))]))
    (fun f => decide (f ∈ [((0 : Nat), (2 : Nat))])) ?_ ?_ ?_).1 hold
  · intro f hf
    have hf' := of_decide_eq_true hf
    simp only [List.mem_singleton] at hf'
    subst hf'
    exact sfFetchBSound _ _ (by decide +kernel)
  · intro f hf
    have hf' := of_decide_eq_true hf
    simp only [List.mem_singleton] at hf'
    subst hf'
    decide +kernel
  · intro m
    simp only [decide_eq_true_eq, List.mem_singleton]
    constructor
    · rintro rfl
      exact ⟨(0, 1), rfl, rfl⟩
    · rintro ⟨f, rfl, rfl⟩
      rfl

end Weak
