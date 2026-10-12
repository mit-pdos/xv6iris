/-
Weak: **`wpd` for one instruction FROM ITS FETCH NODE** (spike S3b): the fetch node, then the
post-fetch admin segment ending at the monad's `.pure ()` (the next boundary).

Rocq: `iris/AxCjrWpd.v` @ xxvzwolszwmp.

## The Rocq header, in substance

§1 (generic) `epureGstepRtc`: a successful `WeakEvExecEff.epure D` run whose footprint `D`
excludes the PLIC pins IS a `gstep` run (`AxRunClose`) to `.pure ()` — `epure` is stuck at every
memory / device / barrier / `choose` node and at every register outside `D`, so it is exactly
the "boolean checker" S3a asked for.  §2 (generic) `fetchNodePstep` (the program steps of a
non-exclusive RAM read node) and `wpdFetchStep`, the fetch node's `wpd`, by Löb over the
register file (the PLIC wire loops there).  §3 `wpdFetchThenRun`: §2 composed with
`AxWpdLift.wpdOfClosedRun` at `AxRunClose.Pbefore`/`Qat` (the row-end conjuncts are
caller-supplied `∧`-resources, per the S3a pitfall).  §4 `wpdCjrFromFetch`: §3 at the `c.jr`
geometry (a 2-byte fetch), the post-fetch segment given as an `epure` certificate — the one
premise Rocq leaves undischarged (`AxFetch.af_cjr_row_run` only has the `execEff` fact).

## Deviations from Rocq

1. O2 STAGE C + OWNER Q8 — THE FETCH IS A PINNED ADMIN STEP (`AxOpsem` deviation 2, `AxInstr`
   deviation 2, `AxWp2`'s step clause).  Rocq's fetch was a row `IRead` item, realised through
   clause (a) (graph value, `fetch_flow` deposit) and clause (b) (`AStepFetch`, image oracle),
   landing at `S k`.  In Lean the fetch node (`akIfetch = true`) has exactly one kind of program
   step, `AStepAdmin` at `LIFetch (paZ pa) tvs`, keeping `atK`, with `wlWdata = none`; there is
   no read step (`AxCjrWpd.fetchNoRead`).  The WP's step clause offers only steps whose label is
   PINNED to the graph's boot image (`WeakAxRealize.fetchPin GD.gdG.gxImg l`), so — as in Rocq —
   the continuation is owed for the IMAGE's bytes `vs` only (`AxCjrWpd.pinnedBytes`).  The
   statements are Rocq's, except:
   - `Hlat` ↦ `Hfe : akIfetch = true`; `Hflow` and `Hloc` are dropped (no row item, no deposit,
     no `k ↦ S k`); the post-fetch state is at `k` (Rocq `S k`).
   - `Hgd` states `AxCjrWpd.fetchImgOk GD i k base vs` (Lean-only) in place of `fetchGdOk`:
     Rocq's image conjunct verbatim, and of the row-item conjunct only `k < (grow GD i).length`
     (Rocq: the fetch's own `IRead` item sits at `k`; in Lean the item at `k` is the next row
     event) — it refutes clause (d) (row end) exactly as Rocq's item did.  The graph-value
     conjunct is gone (the fetch has no graph value).  `AxCjrWpd.fetchGdOkImg` gives
     `fetchGdOk → fetchImgOk`.
   - `fetchGdOk` and `fetchFlow` are ported verbatim (≈30 downstream Rocq files mention them)
     but are no longer premises of anything here.
   - `fetchNodePstep` (Rocq: plain `LLoad`) concludes `l = rdLabel akIfetch false akSync …`,
     i.e. it covers the fetch arm (`LIFetch`) too.
   (Before Q8 the step clause quantified fetches of ANY bytes, so these lemmas owed their
   continuation for every byte string and took an extra row-end `∧`-conjunct; both are gone.)
2. THE PINS (`AxRunClose` deviation 1): `regs_agree seip_reg` ↦ `regsAgree AxRunClose.pinReg`;
   `epureGstepRtc` and `wpdCjrFromFetch` take `Hse : sig_seip ∉ D` AND `Hme : sig_meip ∉ D`
   (`nodeOk` excludes reads of both pins).
3. TYPES: `RiscvLang.mstate` ↦ `ExecSt` (`sregs` ↦ `regs`), `gset register` ↦ `List Register`,
   `Interface.ReadReq.t n` ↦ `Mem_read_request n va …` (new bound `va`), `inl (w, None)` ↦
   `.Ok (w, none)`, `tvs.*2` ↦ `tvs.map Prod.snd`, `Interface.Ret tt` ↦ `.pure ()`; `WPd … @
   MaybeStuck; i {{ Φ }}` ↦ `wpd .MaybeStuck i s Φ`; `invGS_gen HasNoLc Σ` ↦
   `[InvGS_gen hlc GF]`; `A -∗ B` ↦ `⊢ A -∗ B`; Rocq's `{[e := R]} ∪ nu ∪ na` ↦
   `PartialMap.union (PartialMap.union {[e := R]} nu) na`.
4. Lean-only helpers (file-qualified): `AxCjrWpd.gstepNode` (one `gstep` at a monad node),
   `AxCjrWpd.fetchStepInv`, `AxCjrWpd.fetchAstepInv`, `AxCjrWpd.fetchNoRead` (the fetch node's
   steps), `AxCjrWpd.wpdOfRunFrom` (§3's closed-run tail), and (Q8) `AxCjrWpd.fetchImgOk`,
   `AxCjrWpd.fetchGdOkImg`, `AxCjrWpd.pinnedBytes` (a pinned fetch returns the image bytes).

Q7 (owner ruling, `notes/weak-port-q7-sfence.md` route (a), Lean-only): `epureGstepRtc`'s announce case reads `sfAnnB n w = false` off `WeakEvExecEff.epure` (which stops at an sfence announce) and steps with `LInstr`.

**Rocq → Lean name map.**  `erw_label_admin` `AxCjrWpd.erwLabelAdmin` (duplicated name),
`epure_gstep_rtc` `epureGstepRtc`, `bytes_word_eq` `bytesWordEq`, `fetch_node_pstep`
`fetchNodePstep`, `fetch_gd_ok` `fetchGdOk`, `fetch_flow` `fetchFlow`, `wpd_fetch_step`
`wpdFetchStep`, `wpd_fetch_then_run` `wpdFetchThenRun`, `wpd_cjr_from_fetch` `wpdCjrFromFetch`.

**Not ported:** the `Print Assumptions` block (the lint's axiom check covers it).
-/
import Weak.AxRunClose
import Weak.WeakEvExecEff

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std Iris.Std.PartialMap MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D
open Wlabel

/-! # 1. GENERIC: an `epure` run off the pins is a `gstep` run -/

theorem AxCjrWpd.erwLabelAdmin (ek : ErwKind) : AxOpsem.lbAdminAx true (erwLabel ek) := by
  cases ek <;> trivial

/-- (Lean-only) One `gstep` at an `nodeOk` monad node, from its `pnodeStep` at one fabric. -/
theorem AxCjrWpd.gstepNode (cpu : CPU) (m m' : SailM Unit) (rs : RegFile) (ib : Ibch) (k : Nat)
    (l : Wlabel) (ors : Option RegFile) (oib : Option Ibch) (obar : Option barrier_kind)
    (d : Efab) :
    nodeOk m → AxOpsem.lbAdminAx true l →
    pnodeStep m rs ib d.efDev l m' ors none d.efDev oib obar →
    gstep ⟨.PHart cpu m rs none ib, k⟩ ⟨.PHart cpu m' (ors.getD rs) none (oib.getD ib), k⟩ :=
  fun hok hadm h =>
    ⟨hok, rfl, [], l, .AStepAdmin _ k d l _ d hadm ⟨rfl, ors, oib, obar, rfl, rfl, h, rfl⟩⟩

theorem epureGstepRtc (D : List Register) (Hse : Register.sig_seip ∉ D)
    (Hme : Register.sig_meip ∉ D) (m : SailM Unit) :
    ∀ (t : ExecSt) (x : Unit) (t' : ExecSt), epure D m t = some (x, t') →
    ∀ (cpu : CPU) (ib : Ibch) (kpos : Nat), ∃ ib',
      rtc gstep (⟨.PHart cpu m t.regs none ib, kpos⟩ : Athread)
                ⟨.PHart cpu (.pure ()) t'.regs none ib', kpos⟩ := by
  induction m with
  | pure y =>
    intro t x t' h cpu ib kpos
    simp only [epure, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact ⟨ib, rtc_refl _⟩
  | impure call k ih =>
    intro t x t' h cpu ib kpos
    cases call with
    | error e => simp [epure] at h
    | ok o =>
      cases o
      case regRead r =>
        by_cases hr : r ∈ D
        · simp only [epure, hr, ↓reduceIte] at h
          obtain ⟨ib', hrun⟩ := ih _ _ _ _ h cpu (ibRd ib r) kpos
          refine ⟨ib', rtc_l ?_ hrun⟩
          refine AxCjrWpd.gstepNode cpu _ _ t.regs ib kpos .LSilent none (some (ibRd ib r)) none
            (efInit t.dev) ?_ trivial ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
          rintro (rfl | rfl)
          · exact Hse hr
          · exact Hme hr
        · simp [epure, hr] at h
      case regWrite r v =>
        by_cases hr : r ∈ D
        · simp only [epure, hr, ↓reduceIte] at h
          obtain ⟨ib', hrun⟩ := ih _ _ _ _ h cpu ib kpos
          refine ⟨ib', rtc_l ?_ hrun⟩
          exact AxCjrWpd.gstepNode cpu _ _ t.regs ib kpos _ (some (t.regs.set r v)) none none
            (efInit t.dev) trivial (AxCjrWpd.erwLabelAdmin _) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
        · simp [epure, hr] at h
      case instrAnnounce a w =>
        cases hsw : sfAnnB a w <;>
          simp only [epure, hsw, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at h
        obtain ⟨ib', hrun⟩ := ih _ _ _ _ h cpu (ibAnn (ibOfBvn w)) kpos
        refine ⟨ib', rtc_l ?_ hrun⟩
        exact AxCjrWpd.gstepNode cpu _ _ t.regs ib kpos .LInstr none (some (ibAnn (ibOfBvn w)))
          none (efInit t.dev) trivial rfl ⟨(annLabelNot hsw).symm, rfl, rfl, rfl, rfl, rfl, rfl⟩
      case getCycleCount =>
        simp only [epure] at h
        obtain ⟨ib', hrun⟩ := ih _ _ _ _ h cpu ib kpos
        refine ⟨ib', rtc_l ?_ hrun⟩
        exact AxCjrWpd.gstepNode cpu _ _ t.regs ib kpos .LSilent none none none
          (efInit t.dev) trivial trivial ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      all_goals first
        | (simp [epure] at h; done)
        | (simp only [epure] at h
           obtain ⟨ib', hrun⟩ := ih _ _ _ _ h cpu ib kpos
           refine ⟨ib', rtc_l ?_ hrun⟩
           exact AxCjrWpd.gstepNode cpu _ _ t.regs ib kpos .LSilent none none none
             (efInit t.dev) trivial trivial ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩)

/-! # 2. GENERIC: the fetch node -/

theorem bytesWordEq (n : Nat) (w : BitVec (8 * n)) (tvs : List (Nat × BitVec 8)) :
    tvs.length = n →
    (∀ j : Nat, j < n → (tvs.map Prod.snd)[j]? = some (nthByte w j)) →
    w = wordOfBytes n (tvs.map Prod.snd) := by
  intro hl hby
  rw [AxOpsem.sndEqWbytes n w tvs hl hby, wordOfBytesWbytes]

/-- Every program step of a RAM `memRead` node that is not exclusive: a load (a plain load, or
the fetch `LIFetch` at an `akIfetch` node) of SOME bytes, landing at the continuation on the
word of those bytes. -/
theorem fetchNodePstep (cpu : CPU) (n va : Nat)
    (req : Mem_read_request n va Arch.pa Arch.translation Arch.arch_ak)
    (KK : Result (BitVec (8 * n) × Option Bool) Arch.abort → SailM Unit) (rs : RegFile)
    (ib : Ibch) (d : Efab) (l : Wlabel) (p' : Pexv6) (d' : Efab) :
    devAddr req.pa = false → (classify req.access_kind).akLatest = false →
    pstepProg (.PHart cpu (.impure (.ok (.memRead n va req)) KK) rs none ib) d l p' d' →
    ∃ tvs : List (Nat × BitVec 8), tvs.length = n ∧
      l = rdLabel (classify req.access_kind).akIfetch false (classify req.access_kind).akSync
            (paZ req.pa) tvs [] ∧
      p' = .PHart cpu (KK (.Ok (wordOfBytes n (tvs.map Prod.snd), none))) rs none ib := by
  intro hdev hlat h
  cases p' with
  | PDisk _ => exact False.elim h
  | PHart c m' rs' fn' ib' =>
    obtain ⟨rfl, ors, oib, obar, rfl, rfl, hn, -⟩ := h
    simp only [pstepNode, pnodeStep, hdev, Bool.false_eq_true, ↓reduceIte] at hn
    rcases hn with ⟨hif, w, tvs, hlen, hby, rfl, rfl, rfl, rfl, -, rfl, -⟩ |
      ⟨hif, ⟨-, w, tvs, hlen, hby, rfl, rfl, rfl, rfl, -, rfl, -⟩ |
        ⟨hl', -⟩⟩
    · refine ⟨tvs, hlen, by simp only [rdLabel, hif, ↓reduceIte], ?_⟩
      rw [← bytesWordEq n w tvs hlen hby]
      rfl
    · refine ⟨tvs, hlen, by simp only [rdLabel, hif, Bool.false_eq_true, ↓reduceIte], ?_⟩
      rw [← bytesWordEq n w tvs hlen hby]
      rfl
    · rw [hlat] at hl'; exact absurd hl' Bool.false_ne_true

/-- (Lean-only) At an `akIfetch` RAM node the only program step is the fetch `LIFetch`. -/
theorem AxCjrWpd.fetchStepInv (cpu : CPU) (n va : Nat)
    (req : Mem_read_request n va Arch.pa Arch.translation Arch.arch_ak)
    (KK : Result (BitVec (8 * n) × Option Bool) Arch.abort → SailM Unit) (rs : RegFile)
    (ib : Ibch) (d : Efab) (l : Wlabel) (p' : Pexv6) (d' : Efab) :
    devAddr req.pa = false → (classify req.access_kind).akIfetch = true →
    pstepProg (.PHart cpu (.impure (.ok (.memRead n va req)) KK) rs none ib) d l p' d' →
    ∃ tvs : List (Nat × BitVec 8), tvs.length = n ∧ l = .LIFetch (paZ req.pa) tvs ∧
      p' = .PHart cpu (KK (.Ok (wordOfBytes n (tvs.map Prod.snd), none))) rs none ib := by
  intro hdev hfe h
  cases p' with
  | PDisk _ => exact False.elim h
  | PHart c m' rs' fn' ib' =>
    obtain ⟨rfl, ors, oib, obar, rfl, rfl, hn, -⟩ := h
    simp only [pstepNode, pnodeStep, hdev, Bool.false_eq_true, ↓reduceIte] at hn
    rcases hn with ⟨-, w, tvs, hlen, hby, rfl, rfl, rfl, rfl, -, rfl, -⟩ | ⟨hif, -⟩
    · refine ⟨tvs, hlen, rfl, ?_⟩
      rw [← bytesWordEq n w tvs hlen hby]
      rfl
    · rw [hfe] at hif; simp at hif

/-- (Lean-only) The fetch node's opax program steps: the admin fetch, position kept. -/
theorem AxCjrWpd.fetchAstepInv (row : List Lbl) (cpu : CPU) (n va : Nat)
    (req : Mem_read_request n va Arch.pa Arch.translation Arch.arch_ak)
    (KK : Result (BitVec (8 * n) × Option Bool) Arch.abort → SailM Unit) (rs : RegFile)
    (ib : Ibch) (k : Nat) (l : Wlabel) (s' : Athread) :
    devAddr req.pa = false → (classify req.access_kind).akIfetch = true →
    AxOpsem.astepProg row ⟨.PHart cpu (.impure (.ok (.memRead n va req)) KK) rs none ib, k⟩ l s' →
    ∃ tvs : List (Nat × BitVec 8), tvs.length = n ∧ l = .LIFetch (paZ req.pa) tvs ∧
      s' = ⟨.PHart cpu (KK (.Ok (wordOfBytes n (tvs.map Prod.snd), none))) rs none ib, k⟩ := by
  intro hdev hfe h
  obtain ⟨d, d', hps⟩ := astepProgPstep row _ _ _ h
  obtain ⟨tvs, hlen, hl, hp⟩ := AxCjrWpd.fetchStepInv cpu n va req KK rs ib d l _ d' hdev hfe hps
  have hk := astepProgAdminK' row _ _ _ h (by rw [hl]; rfl)
  refine ⟨tvs, hlen, hl, ?_⟩
  obtain ⟨p', k'⟩ := s'
  simp only at hp hk
  rw [hp, hk]

/-- (Lean-only) No read step from the fetch node: its only label has no read. -/
theorem AxCjrWpd.fetchNoRead (row : List Lbl) (cpu : CPU) (n va : Nat)
    (req : Mem_read_request n va Arch.pa Arch.translation Arch.arch_ak)
    (KK : Result (BitVec (8 * n) × Option Bool) Arch.abort → SailM Unit) (rs : RegFile)
    (ib : Ibch) (k : Nat) (id : AidentT) (K : List (BitVec 8) → Athread) :
    devAddr req.pa = false → (classify req.access_kind).akIfetch = true →
    ¬ areadStep row ⟨.PHart cpu (.impure (.ok (.memRead n va req)) KK) rs none ib, k⟩ id K := by
  rintro hdev hfe ⟨lb, -, -, hrd, HK⟩
  obtain ⟨l, d, d', hl, -, hps, -⟩ :=
    HK (List.replicate (aidentN id) (0#8)) List.length_replicate
  obtain ⟨tvs, -, rfl, -⟩ := AxCjrWpd.fetchStepInv cpu n va req KK rs ib d l _ d' hdev hfe hps
  rw [← hl] at hrd
  simp [wlRd] at hrd

/-- The pure graph facts Rocq's fetch needed (the fetch as a row read).  O2 Stage C: the fetch
is no row item, so this is no longer a premise of `wpdFetchStep` (kept for the downstream
ports that still state it; its Stage-C remainder is `AxCjrWpd.fetchImgOk`). -/
def fetchGdOk (GD : Gdexec) (i : Agent) (k : Nat) (base : Int) (vs : List (BitVec 8)) : Prop :=
  (∃ lb, (AxOpsem.grow GD i)[k]? = some lb ∧ aident lb = .IRead false base vs.length) ∧
  graphValue GD (i, k) = some vs ∧
  (∀ j : Nat, j < vs.length → GD.gdG.gxImg (base + j) = vs[j]?)

/-- (Lean-only, Q8) What survives of `fetchGdOk` under Stage C: the row has an item at the
fetch's position (Rocq: the fetch's own `IRead` item; Lean: the next row event, the fetch
having none) and the boot IMAGE holds the fetched bytes (verbatim). -/
def AxCjrWpd.fetchImgOk (GD : Gdexec) (i : Agent) (k : Nat) (base : Int) (vs : List (BitVec 8)) :
    Prop :=
  k < (AxOpsem.grow GD i).length ∧
  (∀ j : Nat, j < vs.length → GD.gdG.gxImg (base + j) = vs[j]?)

theorem AxCjrWpd.fetchGdOkImg (GD : Gdexec) (i : Agent) (k : Nat) (base : Int)
    (vs : List (BitVec 8)) :
    fetchGdOk GD i k base vs → AxCjrWpd.fetchImgOk GD i k base vs := by
  rintro ⟨⟨lb, hlb, -⟩, -, himg⟩
  exact ⟨lookup_lt_Some hlb, himg⟩

/-- (Lean-only, Q8) A PINNED fetch of the image's bytes returns exactly those bytes. -/
theorem AxCjrWpd.pinnedBytes (img : Image) (base : Int) (tvs : List (Nat × BitVec 8))
    (vs : List (BitVec 8)) (hlen : tvs.length = vs.length)
    (Himg : ∀ j : Nat, j < vs.length → img (base + j) = vs[j]?)
    (Hpin : WeakAxRealize.fetchPin img (.LIFetch base tvs)) :
    tvs.map Prod.snd = vs := by
  unfold WeakAxRealize.fetchPin at Hpin
  apply List.ext_getElem?
  intro j
  by_cases hj : j < vs.length
  · rw [← Hpin.2 j (by omega), Himg j hj]
  · rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]

section fetch
variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF] [Axpol]

/-- The fetch READ's annotation deposit (Rocq clause (a)).  O2 Stage C: no longer a premise of
`wpdFetchStep` (kept for the downstream ports that still state it). -/
def fetchFlow (GD : Gdexec) (i : Agent) (k : Nat) : IProp GF :=
  iprop(∀ na, naAtProgress GD i k na ∗ AxirisG.annotInterp na -∗ |==> ▷ |==>
    ∃ (R : IProp GF) (naUsed naUnused : Mea GF) (ls' : AxirisG.logTsT GF),
      naSplittingWf (Axpol.lobp GD (i, k)) na naUsed naUnused ∗
      flowEqDyn GD (i, k) (Axpol.sPol GD (i, k)) naUsed R ∗
      AxirisG.annotInterp (PartialMap.union (PartialMap.union {[(i, k) := R]} naUnused) na) ∗
      AxirisG.localInterp GD i (k + 1) ls')

/-- THE FETCH NODE'S `wpd`, by Löb over the register file (the PLIC wire loops there).  The
WP's step clause only offers fetches PINNED to the boot image (Q8), and `Hgd` puts the image
bytes `vs` there: the continuation is owed for `vs` only, at the SAME row position. -/
theorem wpdFetchStep (Φ : Athread → IProp GF) (i : Agent) (cpu : CPU) (n va : Nat)
    (req : Mem_read_request n va Arch.pa Arch.translation Arch.arch_ak)
    (KK : Result (BitVec (8 * n) × Option Bool) Arch.abort → SailM Unit) (ib : Ibch) (k : Nat)
    (vs : List (BitVec 8)) (rs0 : RegFile)
    (Hdev : devAddr req.pa = false) (Hfe : (classify req.access_kind).akIfetch = true)
    (Hlen : vs.length = n)
    (Hgd : ∀ GD, rvwmoCatConsistent GD →
      AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜AxCjrWpd.fetchImgOk GD i k (paZ req.pa) vs⌝) :
    ⊢ ∀ rs, ⌜regsAgree AxRunClose.pinReg rs0 rs⌝ -∗
      (∀ rs', ⌜regsAgree AxRunClose.pinReg rs0 rs'⌝ -∗
         wpd .MaybeStuck i ⟨.PHart cpu (KK (.Ok (wordOfBytes n vs, none))) rs' none ib, k⟩ Φ) -∗
      wpd .MaybeStuck i ⟨.PHart cpu (.impure (.ok (.memRead n va req)) KK) rs none ib, k⟩ Φ := by
  iloeb as IH
  iintro %rs %HP C
  iapply (AxWpD.wpdMUnfoldStep rvwmoCatConsistent .MaybeStuck i _ Φ).2
  isplit
  · iapply (progressOblMaybestuck (GF := GF) i _).2
    itrivial
  unfold wpdMPreStepDef
  iintro %GD %ls ⟨%Hc, #Hg, Hloc⟩
  ihave Hok := (Hgd GD Hc) $$ Hg
  icases Hok with %Hok
  isplit
  · iintro %id %K %Hst
    exact (AxCjrWpd.fetchNoRead _ cpu n va req KK rs ib k id K Hdev Hfe Hst).elim
  isplit
  · iintro %l %s' %Hst %Hpin
    obtain ⟨tvs, hlen, rfl, rfl⟩ := AxCjrWpd.fetchAstepInv _ cpu n va req KK rs ib k l s' Hdev Hfe Hst
    rw [AxCjrWpd.pinnedBytes _ _ tvs vs (by omega) Hok.2 Hpin]
    simp only [wlWdata]
    unfold wpSkipStep
    iintro %na Hna
    imodintro
    inext
    imodintro
    iexists ls
    iframe Hna Hloc
    iapply C $$ %rs %HP
  isplit
  · iintro %s' %Hw
    obtain ⟨hk, hp⟩ := awireAeqv _ _ Hw
    obtain ⟨p', k'⟩ := s'
    simp only at hk hp
    subst hk
    match p', hp with
    | .PHart c m' rs' fn' ib', hp =>
      obtain ⟨rfl, rfl, rfl, rfl, hag⟩ := hp
      unfold wpSkipStep
      iintro %na Hna
      imodintro
      inext
      imodintro
      iexists ls
      iframe Hna Hloc
      iapply IH $$ %rs' %(regsAgreeTrans _ _ _ _ HP (regsAgreeSym _ _ _ hag)) C
  · iintro %Heq
    have h1 := Hok.1
    simp only at Heq
    omega

/-! # 3. GENERIC: fetch, then a closed admin segment -/

/-- (Lean-only) A `gstep` run from `s0`, entered at any `s'` agreeing with `s0`: the
`wpdOfClosedRun` instance at `Pbefore q` / `Qat q` (inline in Rocq's `wpd_fetch_then_run`). -/
theorem AxCjrWpd.wpdOfRunFrom (i : Agent) (q s0 s' : Athread) (Φ : Athread → IProp GF)
    (Hrun : rtc gstep s0 q) (Heq : aeqv s' s0) :
    ⊢ ((∀ s2, ⌜Qat q s2⌝ -∗ wpd .MaybeStuck i s2 Φ) ∧
       (∀ (GD : Gdexec) s1, ⌜Pbefore q s1⌝ -∗ ⌜s1.atK = (AxOpsem.grow GD i).length⌝ -∗
          postLifting Φ i s1)) -∗
      wpd .MaybeStuck i s' Φ := by
  rcases rtc_inv Hrun with rfl | ⟨t, Ht, Htq⟩
  · iintro R
    icases R with ⟨R, -⟩
    iapply R $$ %s' %Heq
  · iintro R
    iapply (wpdOfClosedRun .MaybeStuck i (Pbefore q) (Qat q) Φ
      (fun s1 _ => (progressOblMaybestuck (GF := GF) i s1).2) (runCloseHnord i q)
      (runCloseHclos i q) (runCloseHwire q)) $$ %s' %⟨s0, Heq, tc_rtc_r (tc_once Ht) Htq⟩ R

theorem wpdFetchThenRun (Φ : Athread → IProp GF) (i : Agent) (cpu : CPU) (n va : Nat)
    (req : Mem_read_request n va Arch.pa Arch.translation Arch.arch_ak)
    (KK : Result (BitVec (8 * n) × Option Bool) Arch.abort → SailM Unit) (ib : Ibch) (k : Nat)
    (vs : List (BitVec 8)) (rs0 : RegFile) (q : Athread)
    (Hdev : devAddr req.pa = false) (Hfe : (classify req.access_kind).akIfetch = true)
    (Hlen : vs.length = n)
    (Hgd : ∀ GD, rvwmoCatConsistent GD →
      AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜AxCjrWpd.fetchImgOk GD i k (paZ req.pa) vs⌝)
    (Hrun : rtc gstep ⟨.PHart cpu (KK (.Ok (wordOfBytes n vs, none))) rs0 none ib, k⟩ q) :
    ⊢ ((∀ s2, ⌜Qat q s2⌝ -∗ wpd .MaybeStuck i s2 Φ) ∧
       (∀ (GD : Gdexec) s1, ⌜Pbefore q s1⌝ -∗ ⌜s1.atK = (AxOpsem.grow GD i).length⌝ -∗
          postLifting Φ i s1)) -∗
      wpd .MaybeStuck i ⟨.PHart cpu (.impure (.ok (.memRead n va req)) KK) rs0 none ib, k⟩ Φ := by
  iintro R
  iapply (wpdFetchStep Φ i cpu n va req KK ib k vs rs0 Hdev Hfe Hlen Hgd) $$ %rs0
    %(regsAgreeRefl _ rs0)
  iintro %rs' %hag
  iapply (AxCjrWpd.wpdOfRunFrom i q
    ⟨.PHart cpu (KK (.Ok (wordOfBytes n vs, none))) rs0 none ib, k⟩
    ⟨.PHart cpu (KK (.Ok (wordOfBytes n vs, none))) rs' none ib, k⟩ Φ Hrun
    ⟨rfl, rfl, rfl, rfl, rfl, regsAgreeSym _ _ _ hag⟩) $$ R

/-! # 4. c.jr: the 2-byte fetch of `h`, then the post-fetch segment as an `epure` certificate -/

theorem wpdCjrFromFetch (Φ : Athread → IProp GF) (i : Agent) (cpu : CPU) (va : Nat)
    (req : Mem_read_request 2 va Arch.pa Arch.translation Arch.arch_ak)
    (KK : Result (BitVec (8 * 2) × Option Bool) Arch.abort → SailM Unit) (ib : Ibch) (k : Nat)
    (h : BitVec 16) (s2 s3 : ExecSt) (D : List Register)
    (Hdev : devAddr req.pa = false) (Hfe : (classify req.access_kind).akIfetch = true)
    (Hgd : ∀ GD, rvwmoCatConsistent GD →
      AxirisG.gconstInterp (GF := GF) GD ⊢
        ⌜AxCjrWpd.fetchImgOk GD i k (paZ req.pa) (WeakInterpProj.wbytes 2 h)⌝)
    -- THE POST-FETCH CERTIFICATE (the undischarged c.jr residue), for the fetched halfword
    (Hseip : Register.sig_seip ∉ D) (Hmeip : Register.sig_meip ∉ D)
    (Hpost : epure D (KK (.Ok (wordOfBytes 2 (WeakInterpProj.wbytes 2 h), none))) s2 =
      some ((), s3)) :
    ⊢ ((∀ (ib' : Ibch) s', ⌜Qat ⟨.PHart cpu (.pure ()) s3.regs none ib', k⟩ s'⌝ -∗
          wpd .MaybeStuck i s' Φ) ∧
       (∀ (ib' : Ibch) (GD : Gdexec) s1,
          ⌜Pbefore ⟨.PHart cpu (.pure ()) s3.regs none ib', k⟩ s1⌝ -∗
          ⌜s1.atK = (AxOpsem.grow GD i).length⌝ -∗ postLifting Φ i s1)) -∗
      wpd .MaybeStuck i ⟨.PHart cpu (.impure (.ok (.memRead 2 va req)) KK) s2.regs none ib, k⟩
        Φ := by
  iintro R
  obtain ⟨ib', Hrun⟩ := epureGstepRtc D Hseip Hmeip _ _ _ _ Hpost cpu ib k
  iapply (wpdFetchThenRun Φ i cpu 2 va req KK ib k (WeakInterpProj.wbytes 2 h) s2.regs _
    Hdev Hfe (wbytesLength 2 h) Hgd Hrun)
  isplit
  · icases R with ⟨R, -⟩
    iapply R
  · icases R with ⟨-, R⟩
    iapply R

end fetch

end Weak
