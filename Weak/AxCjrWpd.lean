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

1. O2 STAGE C — THE FETCH IS AN ADMIN STEP WITH A DEMONIC VALUE (`AxOpsem` deviation 2,
   `AxInstr` deviation 2).  Rocq's fetch was a row `IRead` item, realised through clause (a)
   (graph value, `fetch_flow` deposit) and clause (b) (`AStepFetch`, image oracle), landing at
   `S k`.  In Lean the fetch node (`akIfetch = true`) has exactly one kind of program step,
   `AStepAdmin` at `LIFetch (paZ pa) tvs` for ANY bytes, keeping `atK`, with `wlWdata = none`;
   there is no read step (`AxCjrWpd.fetchNoRead`) and no oracle.  Consequently:
   - `wpdFetchStep`, `wpdFetchThenRun`, `wpdCjrFromFetch` drop the premises `Hlat`, `Hlen`,
     `Hgd` (`fetchGdOk`), `Hflow` (`fetchFlow`), `Hloc` and take `Hfe : akIfetch = true`; the
     post-fetch state is at `k` (Rocq `S k`) and the continuation is owed FOR EVERY fetched
     byte string `vs` of the width (Rocq: the image bytes `vs` only).  So `wpdFetchThenRun`'s run
     is a family `Hrun : ∀ vs, vs.length = n → rtc gstep … (q vs)` and its resources quantify
     `vs`; `wpdCjrFromFetch` drops `h : bv 16` and takes `Hpost` for every `vs` (with
     `s3 : List (BitVec 8) → ExecSt`), its resources quantify `vs` (and `ib'`, as Rocq).
   - Rocq's clause (d) (row end) was refuted by the fetch's own row item at `k`; Lean has none,
     so each of the three lemmas takes one more `∧`-conjunct: `postLifting` at the fetch node
     (any `rs'` agreeing off the pins) when `k` is the row length.
   - `fetchGdOk` and `fetchFlow` are ported verbatim (≈30 downstream Rocq files mention them)
     but are no longer premises of anything here.
   - `fetchNodePstep` (Rocq: plain `LLoad`) concludes `l = rdLabel akIfetch false akSync …`,
     i.e. it covers the fetch arm (`LIFetch`) too.
   FINDING (for the orchestrator): with the fetch value demonic, a `wpd` of a SPECIFIC
   instruction from its fetch node needs its post-fetch reasoning for all fetched bytes (§4's
   `Hpost` for every halfword is false for real code).  Downstream Rocq users of
   `wpd_fetch_step` (AxEpi*, AxLdspWpd, AxSmodeProbe, AxSymEngine) cannot be ported faithfully
   without an Ax-tier fetch pin (e.g. `WeakAxRealize.fetchPin GD.gdG.gxImg l` on `AStepAdmin`).
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
   steps), `AxCjrWpd.wpdOfRunFrom` (§3's closed-run tail, shared with §4).

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

theorem AxCjrWpd.erwLabelAdmin (ek : ErwKind) : lbAdmin true (erwLabel ek) := by
  cases ek <;> trivial

/-- (Lean-only) One `gstep` at an `nodeOk` monad node, from its `pnodeStep` at one fabric. -/
theorem AxCjrWpd.gstepNode (cpu : CPU) (m m' : SailM Unit) (rs : RegFile) (ib : Ibch) (k : Nat)
    (l : Wlabel) (ors : Option RegFile) (oib : Option Ibch) (obar : Option barrier_kind)
    (d : Efab) :
    nodeOk m → lbAdmin true l →
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
        simp only [epure] at h
        obtain ⟨ib', hrun⟩ := ih _ _ _ _ h cpu (ibAnn (ibOfBvn w)) kpos
        refine ⟨ib', rtc_l ?_ hrun⟩
        exact AxCjrWpd.gstepNode cpu _ _ t.regs ib kpos .LInstr none (some (ibAnn (ibOfBvn w)))
          none (efInit t.dev) trivial rfl ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
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
ports that still state it). -/
def fetchGdOk (GD : Gdexec) (i : Agent) (k : Nat) (base : Int) (vs : List (BitVec 8)) : Prop :=
  (∃ lb, (AxOpsem.grow GD i)[k]? = some lb ∧ aident lb = .IRead false base vs.length) ∧
  graphValue GD (i, k) = some vs ∧
  (∀ j : Nat, j < vs.length → GD.gdG.gxImg (base + j) = vs[j]?)

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
fetched bytes are DEMONIC (no graph value, no image oracle): the continuation is owed for every
byte string of the width, at the SAME row position. -/
theorem wpdFetchStep (Φ : Athread → IProp GF) (i : Agent) (cpu : CPU) (n va : Nat)
    (req : Mem_read_request n va Arch.pa Arch.translation Arch.arch_ak)
    (KK : Result (BitVec (8 * n) × Option Bool) Arch.abort → SailM Unit) (ib : Ibch) (k : Nat)
    (rs0 : RegFile)
    (Hdev : devAddr req.pa = false) (Hfe : (classify req.access_kind).akIfetch = true) :
    ⊢ ∀ rs, ⌜regsAgree AxRunClose.pinReg rs0 rs⌝ -∗
      ((∀ (vs : List (BitVec 8)) (rs' : RegFile), ⌜vs.length = n⌝ -∗
          ⌜regsAgree AxRunClose.pinReg rs0 rs'⌝ -∗
          wpd .MaybeStuck i ⟨.PHart cpu (KK (.Ok (wordOfBytes n vs, none))) rs' none ib, k⟩ Φ) ∧
       (∀ (GD : Gdexec) (rs' : RegFile), ⌜regsAgree AxRunClose.pinReg rs0 rs'⌝ -∗
          ⌜k = (AxOpsem.grow GD i).length⌝ -∗
          postLifting Φ i ⟨.PHart cpu (.impure (.ok (.memRead n va req)) KK) rs' none ib, k⟩)) -∗
      wpd .MaybeStuck i ⟨.PHart cpu (.impure (.ok (.memRead n va req)) KK) rs none ib, k⟩ Φ := by
  iloeb as IH
  iintro %rs %HP R
  iapply (AxWpD.wpdMUnfoldStep rvwmoCatConsistent .MaybeStuck i _ Φ).2
  isplit
  · iapply (progressOblMaybestuck (GF := GF) i _).2
    itrivial
  unfold wpdMPreStepDef
  iintro %GD %ls ⟨%Hc, #Hg, Hloc⟩
  isplit
  · iintro %id %K %Hst
    exact (AxCjrWpd.fetchNoRead _ cpu n va req KK rs ib k id K Hdev Hfe Hst).elim
  isplit
  · iintro %l %s' %Hst
    obtain ⟨tvs, hlen, rfl, rfl⟩ := AxCjrWpd.fetchAstepInv _ cpu n va req KK rs ib k l s' Hdev Hfe Hst
    simp only [wlWdata]
    unfold wpSkipStep
    iintro %na Hna
    imodintro
    inext
    imodintro
    iexists ls
    iframe Hna Hloc
    icases R with ⟨R, -⟩
    iapply R $$ %(tvs.map Prod.snd) %rs %(by simp [hlen]) %HP
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
      iapply IH $$ %rs' %(regsAgreeTrans _ _ _ _ HP (regsAgreeSym _ _ _ hag)) R
  · iintro %Heq
    icases R with ⟨-, R⟩
    iapply R $$ %GD %rs %HP %Heq

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
    (rs0 : RegFile) (q : List (BitVec 8) → Athread)
    (Hdev : devAddr req.pa = false) (Hfe : (classify req.access_kind).akIfetch = true)
    (Hrun : ∀ vs : List (BitVec 8), vs.length = n →
      rtc gstep ⟨.PHart cpu (KK (.Ok (wordOfBytes n vs, none))) rs0 none ib, k⟩ (q vs)) :
    ⊢ ((∀ (vs : List (BitVec 8)) s2, ⌜vs.length = n⌝ -∗ ⌜Qat (q vs) s2⌝ -∗
          wpd .MaybeStuck i s2 Φ) ∧
       (∀ (vs : List (BitVec 8)) (GD : Gdexec) s1, ⌜vs.length = n⌝ -∗ ⌜Pbefore (q vs) s1⌝ -∗
          ⌜s1.atK = (AxOpsem.grow GD i).length⌝ -∗ postLifting Φ i s1) ∧
       (∀ (GD : Gdexec) (rs' : RegFile), ⌜regsAgree AxRunClose.pinReg rs0 rs'⌝ -∗
          ⌜k = (AxOpsem.grow GD i).length⌝ -∗
          postLifting Φ i ⟨.PHart cpu (.impure (.ok (.memRead n va req)) KK) rs' none ib, k⟩)) -∗
      wpd .MaybeStuck i ⟨.PHart cpu (.impure (.ok (.memRead n va req)) KK) rs0 none ib, k⟩ Φ := by
  iintro R
  iapply (wpdFetchStep Φ i cpu n va req KK ib k rs0 Hdev Hfe) $$ %rs0 %(regsAgreeRefl _ rs0)
  isplit
  · iintro %vs %rs' %hl %hag
    iapply (AxCjrWpd.wpdOfRunFrom i (q vs)
      ⟨.PHart cpu (KK (.Ok (wordOfBytes n vs, none))) rs0 none ib, k⟩
      ⟨.PHart cpu (KK (.Ok (wordOfBytes n vs, none))) rs' none ib, k⟩ Φ (Hrun vs hl)
      ⟨rfl, rfl, rfl, rfl, rfl, regsAgreeSym _ _ _ hag⟩)
    isplit
    · icases R with ⟨R, -⟩
      iintro %s2 %HQ
      iapply R $$ %vs %s2 %hl %HQ
    · icases R with ⟨-, R, -⟩
      iintro %GD %s1 %HP %Heq
      iapply R $$ %vs %GD %s1 %hl %HP %Heq
  · icases R with ⟨-, -, R⟩
    iexact R

/-! # 4. c.jr: a 2-byte fetch, then the post-fetch segment as an `epure` certificate -/

theorem wpdCjrFromFetch (Φ : Athread → IProp GF) (i : Agent) (cpu : CPU) (va : Nat)
    (req : Mem_read_request 2 va Arch.pa Arch.translation Arch.arch_ak)
    (KK : Result (BitVec (8 * 2) × Option Bool) Arch.abort → SailM Unit) (ib : Ibch) (k : Nat)
    (s2 : ExecSt) (s3 : List (BitVec 8) → ExecSt) (D : List Register)
    (Hdev : devAddr req.pa = false) (Hfe : (classify req.access_kind).akIfetch = true)
    -- THE POST-FETCH CERTIFICATE, for every fetched halfword
    (Hseip : Register.sig_seip ∉ D) (Hmeip : Register.sig_meip ∉ D)
    (Hpost : ∀ vs : List (BitVec 8), vs.length = 2 →
      epure D (KK (.Ok (wordOfBytes 2 vs, none))) s2 = some ((), s3 vs)) :
    ⊢ ((∀ (vs : List (BitVec 8)) (ib' : Ibch) s', ⌜vs.length = 2⌝ -∗
          ⌜Qat ⟨.PHart cpu (.pure ()) (s3 vs).regs none ib', k⟩ s'⌝ -∗
          wpd .MaybeStuck i s' Φ) ∧
       (∀ (vs : List (BitVec 8)) (ib' : Ibch) (GD : Gdexec) s1, ⌜vs.length = 2⌝ -∗
          ⌜Pbefore ⟨.PHart cpu (.pure ()) (s3 vs).regs none ib', k⟩ s1⌝ -∗
          ⌜s1.atK = (AxOpsem.grow GD i).length⌝ -∗ postLifting Φ i s1) ∧
       (∀ (GD : Gdexec) (rs' : RegFile), ⌜regsAgree AxRunClose.pinReg s2.regs rs'⌝ -∗
          ⌜k = (AxOpsem.grow GD i).length⌝ -∗
          postLifting Φ i ⟨.PHart cpu (.impure (.ok (.memRead 2 va req)) KK) rs' none ib, k⟩)) -∗
      wpd .MaybeStuck i ⟨.PHart cpu (.impure (.ok (.memRead 2 va req)) KK) s2.regs none ib, k⟩
        Φ := by
  iintro R
  iapply (wpdFetchStep Φ i cpu 2 va req KK ib k s2.regs Hdev Hfe) $$ %s2.regs
    %(regsAgreeRefl _ s2.regs)
  isplit
  · iintro %vs %rs' %hl %hag
    obtain ⟨ib', Hrun⟩ := epureGstepRtc D Hseip Hmeip _ _ _ _ (Hpost vs hl) cpu ib k
    iapply (AxCjrWpd.wpdOfRunFrom i _
      ⟨.PHart cpu (KK (.Ok (wordOfBytes 2 vs, none))) s2.regs none ib, k⟩
      ⟨.PHart cpu (KK (.Ok (wordOfBytes 2 vs, none))) rs' none ib, k⟩ Φ Hrun
      ⟨rfl, rfl, rfl, rfl, rfl, regsAgreeSym _ _ _ hag⟩)
    isplit
    · icases R with ⟨R, -⟩
      iintro %s' %HQ
      iapply R $$ %vs %ib' %s' %hl %HQ
    · icases R with ⟨-, R, -⟩
      iintro %GD %s1 %HP %Heq
      iapply R $$ %vs %ib' %GD %s1 %hl %HP %Heq
  · icases R with ⟨-, -, R⟩
    iexact R

end fetch

end Weak
