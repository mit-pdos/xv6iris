/-
Weak: **FORWARD-PRECISE ROW-END OBLIGATIONS** (generic): the reach-strengthening of `wpdM`, a
region checker over the monad, a decidable "the monads differ" witness, and the
fetch-then-run region theorem.

Rocq: `iris/AxCjrReach.v` @ xxvzwolszwmp.

## The Rocq header, in substance

The ledger WPd lemmas hand out the row-end obligation `postLifting Φ` over BACKWARD closures
(`Pbefore q`); for a register-level post that is too strong.  This file makes the obligation
FORWARD-precise without touching those lemmas.
§1 `wpdReachM`: for ANY `R` closed under `rstep` (the three `wpdMPreStepDef` step clauses, reads
answered at the graph value, at every graph satisfying a `gconstInterp`-derivable `G`),
`R s ∧ WPd s {{ λ s', ⌜R s'⌝ -∗ Φ s' }} ⊢ WPd s {{ Φ }}`; the instance
`R := rtc (rstep G i) s0` is `wpdReachRtcM`.
§2 `chk`: a region checker — a structural walk of the monad answering register reads from the
file, BOTH answers of every PLIC-pin read, checking a node predicate `Q` at every node,
delegating the RAM read node to `ram` and the `.pure` node to `ret`.  `chkAgree`: insensitive to
the pins.  `chkPnode`: every program step of a `chk`-certified node stays certified (or is the
`.pure`/RAM exit).
§3 `diverge`: a decidable witness that two monads differ (`divergeSelf`, `divergeNe`).
§4 THE FETCH-THEN-RUN REGION TRIPLE: `chkPre` (boundary → the fetch of `vs` at `base`),
`chkPost` (post-fetch → `.pure`: each node `good` or provably not an instruction boundary),
`chkNext` (the next instruction's prefix, stuck at the row end: each node `good`).
`reachGood`: from a `chkPre`-certified boundary state, every FORWARD-reachable boundary-shaped
state at the row end is `good` (Lean: or still a `chkPre` boundary, deviation 1(c)).

## Deviations from Rocq

1. O2 STAGE C + OWNER Q8 (the fetch is a PINNED ADMIN step, no row item; cf. AxCjrWpd
   deviation 1).
   (a) `rstep`'s program arm carries the image pin `WeakAxRealize.fetchPin GD.gdG.gxImg l`
       (exactly what `wpdMPreStepDef`'s clause (b) offers, so `wpdReachM` is unchanged in
       shape and only gets stronger); the oracle parameter `AT` (Rocq `ax_text`) is deleted
       (AxOpsem Q-C2): `rstep G i`, `reachGood … i cpu …` (no `AT`).
   (b) GEOMETRY: Rocq's row had `S kf` items, the fetch being the last (`kf`), the post-fetch
       region at `S kf` = row end.  In Lean the fetch has no item: the row has `kf` items and
       the WHOLE region (pre-fetch, post-fetch, next prefix) sits at position `kf` = row end.
       `Gf kf base vs i GD` := Rocq's image conjunct of `fetchGdOk` (verbatim) ∧
       `(grow GD i).length = kf` (Rocq: `fetchGdOk GD i kf base vs ∧ length = S kf`; the
       row-item and graph-value conjuncts are gone with the fetch item).  `AxCjrReach.Inv` has
       Rocq's two disjuncts, both at `kf`.  `rowAtKf` becomes "no row item at `kf`" (Rocq: the
       fetch's `IRead` item sits at `kf`); `rowAtEnd` is stated at `kf` (Rocq `S kf`).
   (c) CONSEQUENCE for `InvGood`/`reachGood`: the position no longer separates the pre-fetch
       boundary (the start state itself, and its PLIC-wire variants) from the post-fetch
       boundaries, so the conclusion is `good rs' = true ∨ chkPre … (riscvStep tk) rs' = true`
       (Rocq: `good rs' = true`).  AxEpiRet does not use `reachGood`: it applies the reach at
       hart 0's start over its own staged region (AxEpiRet deviation 1).
   (d) A fetch is NOT stuck at the row end in Lean (it is an admin step), so Rocq's
       `ram := λ _ _, true` of `chkNext`/`chkPost` (any RAM read is a row-end exit) is unsound;
       they use `AxCjrReach.dataRead` (Lean-only: the node is a NON-fetch RAM read, which IS
       stuck at the row end).  A `chkNext` walk therefore cannot pass the next instruction's
       fetch.  Q11 (AxEpiRet port): `chk`'s `memWrite` arm now delegates to `ram` (with
       `!devAddr`, like `memRead`), `chkPnode` has a third (memWrite) disjunct, and `dataRead`
       also accepts a non-exclusive store (`!akLatest`: stuck at the row end) — the memWrite
       exit.  The existing `ram`s (`ramPre`) still reject stores.
   (e) `fetchSucc` takes `Hfe : akIfetch = true`, the pin and the image facts in place of Rocq's
       `Hvals : wlRvals l = vs` (a fetch label `LIFetch` has `wlRvals = []`; its bytes come
       from the pin, `AxCjrWpd.pinnedBytes`).
   (f) `chkPnode`'s RAM disjunct concludes `lbAdmin true l → akIfetch = true` (Rocq:
       `¬ lbAdmin true l`; the Lean fetch arm IS admin).
2. THE PINS (AxRunClose deviation 1): `regs_agree seip_reg` ↦ `regsAgree AxRunClose.pinReg`
   (the Lean wire writes `sig_seip` OR `sig_meip`).  `chk` answers a read of EITHER pin both
   ways, from `AxCjrReach.pinAns rs b` (Lean-only: both pins set to `b`; Rocq:
   `register_set sig_seip b rs`); `diverge` answers pin reads from `pinAns rs 0#1`.
   `lookupSetSeipAgree` is stated over `pinAns`.  `seipInsens` keeps its Rocq name.
3. Q7 (sfence marker): `chk`'s announce arm also checks `sfAnnB n w = false` (the sfence
   announce is a graph event, not an admin step), so `chkPnode` keeps Rocq's `lbAdmin true l`.
   Certificates over concrete monads are unaffected (no sfence in the walked regions).
4. TYPES: `M unit` ↦ `SailM Unit`, `regstate` ↦ `RegFile`, `Interface.Ret` ↦ `.pure`,
   `Interface.ReadReq.t n` ↦ `Mem_read_request n va …` (new bound `va`), `inl (w, None)` ↦
   `.Ok (w, none)`, `default rs ors` ↦ `ors.getD rs`, `bv 1` cases ↦ `0#1`/`1#1`; the Lean
   monad's `.error` node and the outcomes Rocq does not list (`memWrite`, `barrier`, `choose`,
   `readRam`, `writeRam`) make `chk` false; `mtag` tags the `.error` node `(100, none)`.
   `pnodeStep`/`pstepProgHart` carry the barrier output `obar`.  `invGS_gen HasNoLc Σ` ↦
   `[InvGS_gen hlc GF]`; `A -∗ B` ↦ `⊢ A -∗ B`; the Rocq section variable `Hgood` is an
   explicit argument (same position).  `QPost`, `chkPost`, `ramPre`, `chkPre` are
   `noncomputable` (`riscvStep` is).
5. `wpd_reach`/`wpd_reach_rtc` (Rocq `Definition`s at the cat instance) are theorems.

**Rocq → Lean name map.**  `rstep` `rstep`, `wpd_reachM` `wpdReachM`, `wpd_reach_rtcM`
`wpdReachRtcM`, `wpd_reach` `wpdReach`, `wpd_reach_rtc` `wpdReachRtc`, `chk` `chk`,
`seip_insens` `seipInsens`, `lookup_set_seip_agree` `lookupSetSeipAgree`, `chk_agree`
`chkAgree`, `chk_Q` `chkQ`, `chk_pnode` `chkPnode`, `mtag` `mtag`, `diverge` `diverge`,
`diverge_self` `divergeSelf`, `diverge_ne` `divergeNe`, `diverge_agree` `divergeAgree`,
`Q_post` `QPost`, `chk_next` `chkNext`, `chk_post` `chkPost`, `ram_pre` `ramPre`, `chk_pre`
`chkPre`, `Gf` `Gf`, `Inv` `AxCjrReach.Inv` (duplicated name), `chk_next_agree`
`chkNextAgree`, `Q_post_insens` `QPostInsens`, `chk_post_agree` `chkPostAgree`,
`ram_pre_insens` `ramPreInsens`, `chk_pre_agree` `chkPreAgree`, `pstep_prog_hart`
`pstepProgHart`, `row_at_kf` `rowAtKf`, `row_at_end` `rowAtEnd`, `fetch_succ` `fetchSucc`,
`Inv_step` `AxCjrReach.InvStep` (duplicated name), `Inv_good` `InvGood`, `rtc_Inv` `rtcInv`,
`reach_good` `reachGood`.  Lean-only (file-qualified): `AxCjrReach.pinAns`,
`AxCjrReach.pinAnsCases`, `AxCjrReach.dataRead`, `AxCjrReach.bv1Cases`.

**Not ported:** the `Print Assumptions` block (the lint's axiom check covers it).
-/
import Weak.AxCjrWpd

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std Iris.Std.PartialMap MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D
open Wlabel

/-! # 1. Forward reachability and the reach-strengthening lemma -/

/-- One step of the `wpdM` unfolding: a (pinned) program step, the PLIC wire, or a read answered
at the graph value — at any graph satisfying `G`. -/
def rstep (G : Gdexec → Prop) (i : Agent) (s s' : Athread) : Prop :=
  (∃ GD l, G GD ∧ AxOpsem.astepProg (AxOpsem.grow GD i) s l s' ∧
     WeakAxRealize.fetchPin GD.gdG.gxImg l) ∨
  awire s s' ∨
  (∃ GD id K v, G GD ∧ areadStep (AxOpsem.grow GD i) s id K ∧
     graphValue GD (i, s.atK) = some v ∧ v.length = aidentN id ∧ s' = K v)

section reach
variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF] [Axpol]
variable (M : Gdexec → Prop)

theorem wpdReachM (st : Stuckness) (i : Agent) (G : Gdexec → Prop) (R : Athread → Prop)
    (Φ : Athread → IProp GF)
    (HG : ∀ GD, M GD → AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜G GD⌝)
    (HR : ∀ s s', R s → rstep G i s s' → R s') :
    ⊢ ∀ s, ⌜R s⌝ -∗ wpdM M st i s (fun s' => iprop(⌜R s'⌝ -∗ Φ s')) -∗ wpdM M st i s Φ := by
  iloeb as IH
  iintro %s %HRs H
  rw [(AxWpD.wpdMUnfoldStep M st i s Φ).to_eq,
    (AxWpD.wpdMUnfoldStep M st i s (fun s' => iprop(⌜R s'⌝ -∗ Φ s'))).to_eq]
  isplit
  · icases H with ⟨H, -⟩
    iexact H
  icases H with ⟨-, H⟩
  unfold wpdMPreStepDef
  iintro %GD %ls ⟨%Hc, #Hg, Hloc⟩
  ihave Hok := (HG GD Hc) $$ Hg
  icases Hok with %HGD
  ihave H := H $$ %GD %ls [Hloc]
  · isplitr
    · ipureintro
      exact Hc
    isplitr
    · iexact Hg
    iexact Hloc
  isplit
  · icases H with ⟨H, -⟩
    iintro %id %K %Hst
    ihave H := H $$ %id %K %Hst
    by_cases hadv : aidentAdvRd id = 1
    · simp only [hadv, ↓reduceIte]
      iintro %v %Hv %Hl
      ihave H := H $$ %v %Hv %Hl
      have HR' := HR s (K v) HRs (.inr (.inr ⟨GD, id, K, v, HGD, Hst, Hv, Hl, rfl⟩))
      iapply wpEvStepMono $$ [] H
      inext
      iintro %_ H
      iapply IH $$ %(K v) %HR' H
    · simp only [hadv, ↓reduceIte]
      iintro %v %Hv %Hl
      ihave H := H $$ %v %Hv %Hl
      have HR' := HR s (K v) HRs (.inr (.inr ⟨GD, id, K, v, HGD, Hst, Hv, Hl, rfl⟩))
      iapply wpSkipStepMono $$ [] H
      inext
      iintro H
      iapply IH $$ %(K v) %HR' H
  isplit
  · icases H with ⟨-, H, -⟩
    iintro %l %s' %Hst %Hpin
    ihave H := H $$ %l %s' %Hst %Hpin
    have HR' := HR s s' HRs (.inl ⟨GD, l, HGD, Hst, Hpin⟩)
    cases wlWdata l with
    | some data =>
      iapply wpEvStepMono $$ [] H
      inext
      iintro %_ H
      iapply IH $$ %s' %HR' H
    | none =>
      iapply wpSkipStepMono $$ [] H
      inext
      iintro H
      iapply IH $$ %s' %HR' H
  isplit
  · icases H with ⟨-, -, H, -⟩
    iintro %s' %Hw
    ihave H := H $$ %s' %Hw
    have HR' := HR s s' HRs (.inr (.inl Hw))
    iapply wpSkipStepMono $$ [] H
    inext
    iintro H
    iapply IH $$ %s' %HR' H
  · icases H with ⟨-, -, -, H⟩
    iintro %Heq
    ihave H := H $$ %Heq
    unfold postLifting
    iintro %na Hna
    imod H $$ %na Hna with ⟨Hna, H⟩
    imodintro
    iframe Hna
    iintro Hb
    ihave H := H $$ Hb
    inext
    imod H
    imodintro
    iapply H
    ipureintro
    exact HRs

/-- The forward-reachable instance. -/
theorem wpdReachRtcM (st : Stuckness) (i : Agent) (G : Gdexec → Prop) (Φ : Athread → IProp GF)
    (s0 : Athread)
    (HG : ∀ GD, M GD → AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜G GD⌝) :
    ⊢ wpdM M st i s0 (fun s' => iprop(⌜rtc (rstep G i) s0 s'⌝ -∗ Φ s')) -∗
      wpdM M st i s0 Φ := by
  iintro H
  iapply (wpdReachM M st i G (rtc (rstep G i) s0) Φ HG
    (fun _ _ Hs Hst => rtc_r Hs Hst)) $$ %s0 %(rtc_refl _) H

end reach

/-! ## The riscv.cat instances under the old names -/

section reachCat
variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF] [Axpol]

theorem wpdReach (st : Stuckness) (i : Agent) (G : Gdexec → Prop) (R : Athread → Prop)
    (Φ : Athread → IProp GF)
    (HG : ∀ GD, rvwmoCatConsistent GD → AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜G GD⌝)
    (HR : ∀ s s', R s → rstep G i s s' → R s') :
    ⊢ ∀ s, ⌜R s⌝ -∗ wpd st i s (fun s' => iprop(⌜R s'⌝ -∗ Φ s')) -∗ wpd st i s Φ :=
  wpdReachM rvwmoCatConsistent st i G R Φ HG HR

theorem wpdReachRtc (st : Stuckness) (i : Agent) (G : Gdexec → Prop) (Φ : Athread → IProp GF)
    (s0 : Athread)
    (HG : ∀ GD, rvwmoCatConsistent GD → AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜G GD⌝) :
    ⊢ wpd st i s0 (fun s' => iprop(⌜rtc (rstep G i) s0 s'⌝ -∗ Φ s')) -∗ wpd st i s0 Φ :=
  wpdReachRtcM rvwmoCatConsistent st i G Φ s0 HG

end reachCat

/-! # 2. The region checker -/

/-- (Lean-only) The register file with BOTH PLIC pins set to `b` (the answers `chk` tries at a
pin read; Rocq `register_set sig_seip b rs`). -/
def AxCjrReach.pinAns (rs : RegFile) (b : BitVec 1) : RegFile :=
  (rs.set .sig_seip b).set .sig_meip b

def chk (Q ram : SailM Unit → RegFile → Bool) (ret : RegFile → Bool) :
    SailM Unit → RegFile → Bool
  | .pure y, rs => Q (.pure y) rs && ret rs
  | .impure (.error _) _, _ => false
  | .impure (.ok o) k, rs =>
    Q (.impure (.ok o) k) rs &&
    match o, k with
    | .regRead r, k =>
        if r = .sig_seip ∨ r = .sig_meip then
          chk Q ram ret (k (AxCjrReach.pinAns rs 0#1 r)) rs &&
            chk Q ram ret (k (AxCjrReach.pinAns rs 1#1 r)) rs
        else chk Q ram ret (k (rs r)) rs
    | .regWrite r v, k => chk Q ram ret (k PUnit.unit) (rs.set r v)
    | .memRead n va req, k => !devAddr req.pa && ram (.impure (.ok (.memRead n va req)) k) rs
    | .instrAnnounce n w, k => !sfAnnB n w && chk Q ram ret (k ()) rs
    | .branchAnnounce _ _, k => chk Q ram ret (k ()) rs
    | .cacheOp _, k => chk Q ram ret (k ()) rs
    | .tlbi _, k => chk Q ram ret (k ()) rs
    | .takeException _, k => chk Q ram ret (k ()) rs
    | .returnException _, k => chk Q ram ret (k ()) rs
    | .translationStart _, k => chk Q ram ret (k ()) rs
    | .translationEnd _, k => chk Q ram ret (k ()) rs
    | .cycleCount, k => chk Q ram ret (k ()) rs
    | .message _, k => chk Q ram ret (k ()) rs
    | .getCycleCount, k => chk Q ram ret (k (0 : Nat)) rs
    | .memWrite n va req, k => !devAddr req.pa && ram (.impure (.ok (.memWrite n va req)) k) rs
    | .barrier _, _ => false
    | .choose _, _ => false
    | .readRam .., _ => false
    | .writeRam .., _ => false

def seipInsens {A : Type} (f : A → RegFile → Bool) : Prop :=
  ∀ x rs rs', regsAgree AxRunClose.pinReg rs rs' → f x rs = f x rs'

theorem lookupSetSeipAgree (rs rs' : RegFile) (r : Register) (b : BitVec 1) :
    regsAgree AxRunClose.pinReg rs rs' →
    AxCjrReach.pinAns rs b r = AxCjrReach.pinAns rs' b r := by
  intro hag
  unfold AxCjrReach.pinAns
  by_cases hm : r = .sig_meip
  · subst hm
    rw [RegFile.set_same, RegFile.set_same]
  · rw [registerLookupSetNe _ _ _ _ hm, registerLookupSetNe _ _ _ _ hm]
    by_cases hs : r = .sig_seip
    · subst hs
      rw [RegFile.set_same, RegFile.set_same]
    · rw [registerLookupSetNe _ _ _ _ hs, registerLookupSetNe _ _ _ _ hs]
      exact hag r (by rintro (h | h) <;> contradiction)

/-- (Lean-only) The two values of a bit. -/
theorem AxCjrReach.bv1Cases (x : BitVec 1) : x = 0#1 ∨ x = 1#1 := by
  have : ∀ y : BitVec 1, y = 0#1 ∨ y = 1#1 := by decide
  exact this x

/-- (Lean-only) The actual value of a pin is one of `chk`'s two answers. -/
theorem AxCjrReach.pinAnsCases (rs : RegFile) (r : Register)
    (hp : r = .sig_seip ∨ r = .sig_meip) :
    AxCjrReach.pinAns rs 0#1 r = rs r ∨ AxCjrReach.pinAns rs 1#1 r = rs r := by
  rcases hp with rfl | rfl
  · have hne : (Register.sig_seip : Register) ≠ .sig_meip := by decide
    unfold AxCjrReach.pinAns
    rw [registerLookupSetNe _ _ _ _ hne, registerLookupSetNe _ _ _ _ hne, RegFile.set_same,
      RegFile.set_same]
    rcases AxCjrReach.bv1Cases (rs .sig_seip) with h | h
    · exact .inl h.symm
    · exact .inr h.symm
  · unfold AxCjrReach.pinAns
    rw [RegFile.set_same, RegFile.set_same]
    rcases AxCjrReach.bv1Cases (rs .sig_meip) with h | h
    · exact .inl h.symm
    · exact .inr h.symm

theorem chkAgree (Q ram : SailM Unit → RegFile → Bool) (ret : RegFile → Bool)
    (HQ : seipInsens Q) (Hram : seipInsens ram)
    (Hret : ∀ rs rs', regsAgree AxRunClose.pinReg rs rs' → ret rs = ret rs')
    (m : SailM Unit) :
    ∀ rs rs', regsAgree AxRunClose.pinReg rs rs' → chk Q ram ret m rs = chk Q ram ret m rs' := by
  induction m with
  | pure y =>
    intro rs rs' hag
    simp only [chk]
    rw [HQ _ _ _ hag, Hret _ _ hag]
  | impure call k ih =>
    intro rs rs' hag
    cases call with
    | error e => rfl
    | ok o =>
      cases o
      case regRead r =>
        simp only [chk]
        rw [HQ _ _ _ hag]
        congr 1
        by_cases hp : r = .sig_seip ∨ r = .sig_meip
        · simp only [if_pos hp]
          rw [lookupSetSeipAgree rs rs' r 0#1 hag, lookupSetSeipAgree rs rs' r 1#1 hag,
            ih _ _ _ hag, ih _ _ _ hag]
        · simp only [if_neg hp]
          rw [hag r hp]
          exact ih _ _ _ hag
      case regWrite r v =>
        simp only [chk]
        rw [HQ _ _ _ hag, ih _ _ _ (regsAgreeSet _ _ _ _ _ hag)]
      case memRead n va req =>
        simp only [chk]
        rw [HQ _ _ _ hag, Hram _ _ _ hag]
      case memWrite n va req =>
        simp only [chk]
        rw [HQ _ _ _ hag, Hram _ _ _ hag]
      all_goals first
        | (simp only [chk]; rw [HQ _ _ _ hag]; done)
        | (simp only [chk]; rw [HQ _ _ _ hag, ih _ _ _ hag])

theorem chkQ (Q ram : SailM Unit → RegFile → Bool) (ret : RegFile → Bool) (m : SailM Unit)
    (rs : RegFile) : chk Q ram ret m rs = true → Q m rs = true := by
  cases m with
  | pure y => simp only [chk, Bool.and_eq_true]; exact fun h => h.1
  | impure call k =>
    cases call with
    | error e => simp [chk]
    | ok o =>
      cases o <;>
        (intro h; simp only [chk] at h; exact (Bool.and_eq_true_iff.1 h).1)

/-- THE STEP LEMMA: a program step from a `chk`-certified node. -/
theorem chkPnode (Q ram : SailM Unit → RegFile → Bool) (ret : RegFile → Bool) (m : SailM Unit)
    (rs : RegFile) (ib : Ibch) (d : DevStates) (l : Wlabel) (m' : SailM Unit)
    (ors : Option RegFile) (fn' : Option (Bool × Bool × Bool × Bool)) (d' : DevStates)
    (oib : Option Ibch) (obar : Option barrier_kind) :
    chk Q ram ret m rs = true → pnodeStep m rs ib d l m' ors fn' d' oib obar →
    (lbAdmin true l ∧ fn' = none ∧
      (chk Q ram ret m' (ors.getD rs) = true ∨
       (∃ y, m = .pure y ∧ ret rs = true ∧ ors = none ∧ ∃ tk, m' = riscvStep tk))) ∨
    (∃ (n va : Nat) (req : Mem_read_request n va Arch.pa Arch.translation Arch.arch_ak)
       (KK : Result (BitVec (8 * n) × Option Bool) Arch.abort → SailM Unit),
       m = .impure (.ok (.memRead n va req)) KK ∧ devAddr req.pa = false ∧ ram m rs = true ∧
       (lbAdmin true l → (classify req.access_kind).akIfetch = true)) ∨
    (∃ (n va : Nat) (req : Mem_write_request n va Arch.pa Arch.translation Arch.arch_ak)
       (KK : Result (Option Bool) Arch.abort → SailM Unit),
       m = .impure (.ok (.memWrite n va req)) KK ∧ devAddr req.pa = false ∧ ram m rs = true ∧
       (lbAdmin true l → (classify req.access_kind).akLatest = true)) := by
  intro hc hs
  cases m with
  | pure y =>
    simp only [chk, Bool.and_eq_true] at hc
    obtain ⟨tk, rfl, rfl, rfl, rfl, -, -, -⟩ := hs
    exact .inl ⟨rfl, rfl, .inr ⟨y, rfl, hc.2, rfl, tk, rfl⟩⟩
  | impure call k =>
    cases call with
    | error e => simp [chk] at hc
    | ok o =>
      cases o
      case regRead r =>
        simp only [chk, Bool.and_eq_true] at hc
        obtain ⟨-, hc⟩ := hc
        obtain ⟨rfl, rfl, rfl, rfl, -, -, -⟩ := hs
        refine .inl ⟨trivial, rfl, .inl ?_⟩
        by_cases hp : r = .sig_seip ∨ r = .sig_meip
        · rw [if_pos hp, Bool.and_eq_true] at hc
          rcases AxCjrReach.pinAnsCases rs r hp with h | h
          · rw [← h]; exact hc.1
          · rw [← h]; exact hc.2
        · rw [if_neg hp] at hc
          exact hc
      case regWrite r v =>
        simp only [chk, Bool.and_eq_true] at hc
        obtain ⟨-, hc⟩ := hc
        obtain ⟨rfl, rfl, rfl, rfl, -, -, -⟩ := hs
        exact .inl ⟨AxCjrWpd.erwLabelAdmin _, rfl, .inl hc⟩
      case memRead n va req =>
        simp only [chk, Bool.and_eq_true, Bool.not_eq_true'] at hc
        obtain ⟨-, hd, hram⟩ := hc
        refine .inr (.inl ⟨n, va, req, k, rfl, hd, hram, ?_⟩)
        intro hadm
        simp only [pnodeStep, hd, Bool.false_eq_true, ↓reduceIte] at hs
        rcases hs with ⟨hif, -⟩ | ⟨-, ⟨-, w, tvs, -, -, rfl, -⟩ | ⟨-, w, tvs, -, -, rfl, -⟩⟩
        · exact hif
        · exact hadm.elim
        · exact hadm.elim
      case memWrite n va req =>
        simp only [chk, Bool.and_eq_true, Bool.not_eq_true'] at hc
        obtain ⟨-, hd, hram⟩ := hc
        refine .inr (.inr ⟨n, va, req, k, rfl, hd, hram, ?_⟩)
        intro hadm
        simp only [pnodeStep, hd, Bool.false_eq_true, ↓reduceIte] at hs
        cases hv : req.value with
        | none => rw [hv] at hs; exact hs.elim
        | some v =>
          rw [hv] at hs
          rcases hs with ⟨-, ⟨-, rfl, -⟩ | ⟨hl, -⟩⟩
          · exact hadm.elim
          · exact hl
      case instrAnnounce n w =>
        simp only [chk, Bool.and_eq_true, Bool.not_eq_true'] at hc
        obtain ⟨-, hsf, hc⟩ := hc
        obtain ⟨rfl, rfl, rfl, rfl, -, -, -⟩ := hs
        refine .inl ⟨?_, rfl, .inl hc⟩
        rw [annLabelNot hsf]
        trivial
      case getCycleCount =>
        simp only [chk, Bool.and_eq_true] at hc
        obtain ⟨-, hc⟩ := hc
        obtain ⟨rfl, rfl, rfl, rfl, -, -, -⟩ := hs
        exact .inl ⟨trivial, rfl, .inl hc⟩
      all_goals first
        | (simp [chk] at hc; done)
        | (simp only [chk, Bool.and_eq_true] at hc
           obtain ⟨-, hc⟩ := hc
           obtain ⟨rfl, rfl, rfl, rfl, -, -, -⟩ := hs
           exact .inl ⟨trivial, rfl, .inl hc⟩)

/-! # 3. A decidable "the monads differ" witness -/

def mtag (m : SailM Unit) : Option (Nat × Option Register) :=
  match m with
  | .pure _ => none
  | .impure (.error _) _ => some (100, none)
  | .impure (.ok o) _ =>
      some (match o with
            | .regRead r => (0, some r)
            | .regWrite r _ => (1, some r)
            | .memRead .. => (2, none)
            | .memWrite .. => (3, none)
            | .instrAnnounce .. => (4, none)
            | .branchAnnounce .. => (5, none)
            | .barrier _ => (6, none)
            | .cacheOp _ => (7, none)
            | .tlbi _ => (8, none)
            | .takeException _ => (9, none)
            | .returnException _ => (10, none)
            | .cycleCount => (11, none)
            | .getCycleCount => (12, none)
            | _ => (99, none))

/-- `diverge N m1 m2 rs = true` ⇒ `m1 ≠ m2`: walk both in lock-step (register reads answered
from `rs` with both pins `0`) and find differing head tags. -/
def diverge : Nat → SailM Unit → SailM Unit → RegFile → Bool
  | 0, _, _, _ => false
  | N + 1, m1, m2, rs =>
    if mtag m1 = mtag m2 then
      match m1, m2 with
      | .impure (.ok (.regRead r1)) k1, .impure (.ok (.regRead r2)) k2 =>
          diverge N (k1 (AxCjrReach.pinAns rs 0#1 r1)) (k2 (AxCjrReach.pinAns rs 0#1 r2)) rs
      | .impure (.ok (.regWrite r1 v1)) k1, .impure (.ok (.regWrite _ _)) k2 =>
          diverge N (k1 PUnit.unit) (k2 PUnit.unit) (rs.set r1 v1)
      | _, _ => false
    else true

theorem divergeSelf (N : Nat) : ∀ m rs, diverge N m m rs = false := by
  induction N with
  | zero => intro m rs; rfl
  | succ N ih =>
    intro m rs
    simp only [diverge, ↓reduceIte]
    cases m with
    | pure y => rfl
    | impure call k =>
      cases call with
      | error e => rfl
      | ok o => cases o <;> first | rfl | exact ih _ _

theorem divergeNe (N : Nat) (m1 m2 : SailM Unit) (rs : RegFile) :
    diverge N m1 m2 rs = true → m1 ≠ m2 := by
  intro h e
  subst e
  rw [divergeSelf] at h
  exact Bool.false_ne_true h

theorem divergeAgree (N : Nat) : ∀ m1 m2 rs rs', regsAgree AxRunClose.pinReg rs rs' →
    diverge N m1 m2 rs = diverge N m1 m2 rs' := by
  induction N with
  | zero => intro m1 m2 rs rs' _; rfl
  | succ N ih =>
    intro m1 m2 rs rs' hag
    simp only [diverge]
    split
    · cases m1 with
      | pure y1 => rfl
      | impure call1 k1 =>
        cases m2 with
        | pure y2 =>
          cases call1 with
          | error e1 => rfl
          | ok o1 => cases o1 <;> rfl
        | impure call2 k2 =>
          cases call1 with
          | error e1 => rfl
          | ok o1 =>
            cases call2 with
            | error e2 => cases o1 <;> rfl
            | ok o2 =>
              cases o1 <;> cases o2 <;> try rfl
              · simp only []
                rw [lookupSetSeipAgree rs rs' _ 0#1 hag, lookupSetSeipAgree rs rs' _ 0#1 hag]
                exact ih _ _ _ _ hag
              · exact ih _ _ _ _ (regsAgreeSet _ _ _ _ _ hag)
    · rfl

/-! # 4. The fetch-then-run region triple -/

section regions
variable (kf : Nat) (base : Int) (vs : List (BitVec 8)) (good : RegFile → Bool) (Nd : Nat)

noncomputable def QPost (m : SailM Unit) (rs : RegFile) : Bool :=
  good rs || (diverge Nd m (riscvStep false) rs && diverge Nd m (riscvStep true) rs)

/-- (Lean-only, deviation 1(d)) A RAM read node that is stuck at the row end: NOT a fetch. -/
def AxCjrReach.dataRead (m : SailM Unit) : Bool :=
  match m with
  | .impure (.ok (.memRead _ _ req)) _ => !(classify req.access_kind).akIfetch
  | .impure (.ok (.memWrite _ _ req)) _ => !(classify req.access_kind).akLatest
  | _ => false

def chkNext : SailM Unit → RegFile → Bool :=
  chk (fun _ rs => good rs) (fun m _ => AxCjrReach.dataRead m) (fun _ => false)

noncomputable def chkPost : SailM Unit → RegFile → Bool :=
  chk (QPost good Nd) (fun m _ => AxCjrReach.dataRead m)
    (fun rs => chkNext good (riscvStep false) rs && chkNext good (riscvStep true) rs)

noncomputable def ramPre (m : SailM Unit) (rs : RegFile) : Bool :=
  match m with
  | .impure (.ok (.memRead n _ req)) KK =>
      !(classify req.access_kind).akLatest && decide (paZ req.pa = base) &&
        decide (vs.length = n) && chkPost good Nd (KK (.Ok (wordOfBytes n vs, none))) rs
  | _ => false

noncomputable def chkPre : SailM Unit → RegFile → Bool :=
  chk (fun _ _ => true) (ramPre base vs good Nd) (fun _ => false)

/-- The graphs of the region: the image holds `vs` at `base`, and the row has `kf` items
(deviation 1(b): the fetch has no item; the whole region is at the row end). -/
def Gf (i : Agent) (GD : Gdexec) : Prop :=
  (∀ j : Nat, j < vs.length → GD.gdG.gxImg (base + j) = vs[j]?) ∧
  (AxOpsem.grow GD i).length = kf

def AxCjrReach.Inv (s : Athread) : Prop :=
  ∃ cpu m rs ib,
    (s = ⟨.PHart cpu m rs none ib, kf⟩ ∧ chkPre base vs good Nd m rs = true) ∨
    (s = ⟨.PHart cpu m rs none ib, kf⟩ ∧
       (chkPost good Nd m rs = true ∨ chkNext good m rs = true))

theorem chkNextAgree (Hgood : ∀ rs rs', regsAgree AxRunClose.pinReg rs rs' → good rs = good rs')
    (m : SailM Unit) (rs rs' : RegFile) :
    regsAgree AxRunClose.pinReg rs rs' → chkNext good m rs = chkNext good m rs' :=
  chkAgree _ _ _ (fun _ _ _ h => Hgood _ _ h) (fun _ _ _ _ => rfl) (fun _ _ _ => rfl) m rs rs'

theorem QPostInsens (Hgood : ∀ rs rs', regsAgree AxRunClose.pinReg rs rs' → good rs = good rs') :
    seipInsens (QPost good Nd) := by
  intro m rs rs' hag
  simp only [QPost]
  rw [Hgood _ _ hag, divergeAgree Nd m _ rs rs' hag, divergeAgree Nd m _ rs rs' hag]

theorem chkPostAgree (Hgood : ∀ rs rs', regsAgree AxRunClose.pinReg rs rs' → good rs = good rs')
    (m : SailM Unit) (rs rs' : RegFile) :
    regsAgree AxRunClose.pinReg rs rs' → chkPost good Nd m rs = chkPost good Nd m rs' :=
  chkAgree _ _ _ (QPostInsens good Nd Hgood) (fun _ _ _ _ => rfl)
    (fun r1 r2 hag => by
      simp only [chkNextAgree good Hgood _ r1 r2 hag]) m rs rs'

theorem ramPreInsens (Hgood : ∀ rs rs', regsAgree AxRunClose.pinReg rs rs' → good rs = good rs') :
    seipInsens (ramPre base vs good Nd) := by
  intro m rs rs' hag
  rcases m with y | ⟨call, KK⟩
  · rfl
  rcases call with e | o
  · rfl
  cases o <;> try rfl
  simp only [ramPre]
  rw [chkPostAgree good Nd Hgood _ _ _ hag]

theorem chkPreAgree (Hgood : ∀ rs rs', regsAgree AxRunClose.pinReg rs rs' → good rs = good rs')
    (m : SailM Unit) (rs rs' : RegFile) :
    regsAgree AxRunClose.pinReg rs rs' →
    chkPre base vs good Nd m rs = chkPre base vs good Nd m rs' :=
  chkAgree _ _ _ (fun _ _ _ _ => rfl) (ramPreInsens base vs good Nd Hgood) (fun _ _ _ => rfl)
    m rs rs'

/-- A hart program step, unfolded. -/
theorem pstepProgHart (cpu : CPU) (m : SailM Unit) (rs : RegFile) (ib : Ibch) (d : Efab)
    (l : Wlabel) (p' : Pexv6) (d' : Efab) :
    pstepProg (.PHart cpu m rs none ib) d l p' d' →
    ∃ m' ors fn' oib obar, p' = .PHart cpu m' (ors.getD rs) fn' (oib.getD ib) ∧
      pnodeStep m rs ib d.efDev l m' ors fn' d'.efDev oib obar := by
  intro h
  cases p' with
  | PDisk _ => exact False.elim h
  | PHart c' m' rs' fn' ib' =>
    obtain ⟨rfl, ors, oib, obar, rfl, rfl, hn, -⟩ := h
    exact ⟨m', ors, fn', oib, obar, rfl, hn⟩

/-- Region position `kf` has no row item (deviation 1(b); Rocq: the fetch's `IRead` item). -/
theorem rowAtKf (i : Agent) (GD : Gdexec) (lb : Lbl) :
    Gf kf base vs i GD → (AxOpsem.grow GD i)[kf]? = some lb → False := by
  rintro ⟨-, hlen⟩ hk
  rw [List.getElem?_eq_none (by omega)] at hk
  cases hk

theorem rowAtEnd (i : Agent) (GD : Gdexec) :
    Gf kf base vs i GD → (AxOpsem.grow GD i)[kf]? = none := by
  rintro ⟨-, hlen⟩
  exact List.getElem?_eq_none (by omega)

/-- The fetch node's successor: the pinned fetch returns the image's bytes `vs`. -/
theorem fetchSucc (cpu : CPU) (n va : Nat)
    (req : Mem_read_request n va Arch.pa Arch.translation Arch.arch_ak)
    (KK : Result (BitVec (8 * n) × Option Bool) Arch.abort → SailM Unit) (rs : RegFile)
    (ib : Ibch) (d : Efab) (l : Wlabel) (p' : Pexv6) (d' : Efab) (img : Image)
    (Hdev : devAddr req.pa = false)
    (Hram : ramPre base vs good Nd (.impure (.ok (.memRead n va req)) KK) rs = true)
    (Hfe : (classify req.access_kind).akIfetch = true)
    (Hps : pstepProg (.PHart cpu (.impure (.ok (.memRead n va req)) KK) rs none ib) d l p' d')
    (Himg : ∀ j : Nat, j < vs.length → img (base + j) = vs[j]?)
    (Hpin : WeakAxRealize.fetchPin img l) :
    p' = .PHart cpu (KK (.Ok (wordOfBytes n vs, none))) rs none ib ∧
    chkPost good Nd (KK (.Ok (wordOfBytes n vs, none))) rs = true := by
  simp only [ramPre, Bool.and_eq_true, decide_eq_true_eq] at Hram
  obtain ⟨⟨⟨-, hbase⟩, hlen⟩, hpost⟩ := Hram
  obtain ⟨tvs, htl, rfl, rfl⟩ := AxCjrWpd.fetchStepInv cpu n va req KK rs ib d _ _ d' Hdev Hfe Hps
  rw [hbase] at Hpin
  rw [AxCjrWpd.pinnedBytes img base tvs vs (by omega) Himg Hpin]
  exact ⟨rfl, hpost⟩

theorem AxCjrReach.InvStep
    (Hgood : ∀ rs rs', regsAgree AxRunClose.pinReg rs rs' → good rs = good rs')
    (i : Agent) (s s' : Athread) :
    AxCjrReach.Inv kf base vs good Nd s → rstep (Gf kf base vs i) i s s' →
    AxCjrReach.Inv kf base vs good Nd s' := by
  rintro ⟨cpu, m, rs, ib, HI⟩ Hst
  obtain ⟨rfl, Hc⟩ : s = ⟨.PHart cpu m rs none ib, kf⟩ ∧
      (chkPre base vs good Nd m rs = true ∨
        (chkPost good Nd m rs = true ∨ chkNext good m rs = true)) := by
    rcases HI with ⟨h, hc⟩ | ⟨h, hc⟩
    · exact ⟨h, .inl hc⟩
    · exact ⟨h, .inr hc⟩
  rcases Hst with ⟨GD, l, HG, Hst, Hpin⟩ | Hw | ⟨GD, id, K, v, HG, Hrd, -, -, -⟩
  · -- a program step
    have Hnone := rowAtEnd kf base vs i GD HG
    cases Hst with
    | AStepWrite _ _ _ _ lb _ _ hrow =>
      rw [Hnone] at hrow; cases hrow
    | AStepFence _ _ _ _ lb _ _ hrow =>
      rw [Hnone] at hrow; cases hrow
    | AStepAdmin _ _ d _ p' d' hadm hps =>
      obtain ⟨m', ors, fn', oib, obar, rfl, hn⟩ := pstepProgHart cpu m rs ib d l p' d' hps
      rcases Hc with Hc | Hc | Hc
      · rcases chkPnode _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hc hn with
          ⟨-, rfl, Hc' | ⟨y, -, hr, -⟩⟩ | ⟨n, va, req, KK, rfl, hdev, hram, hif⟩ |
          ⟨n, va, req, KK, rfl, -, hram, -⟩
        · exact ⟨cpu, m', ors.getD rs, oib.getD ib, .inl ⟨rfl, Hc'⟩⟩
        · exact (Bool.false_ne_true hr).elim
        · obtain ⟨hp, Hc'⟩ := fetchSucc base vs good Nd cpu n va req KK rs ib d l _ d' _ hdev hram
            (hif hadm) hps HG.1 Hpin
          rw [hp]
          exact ⟨cpu, _, rs, ib, .inr ⟨rfl, .inl Hc'⟩⟩
        · exact absurd hram (by simp [ramPre])
      · rcases chkPnode _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hc hn with
          ⟨-, rfl, Hc' | ⟨y, -, hr, rfl, tk, rfl⟩⟩ | ⟨n, va, req, KK, rfl, -, hram, hif⟩ |
          ⟨n, va, req, KK, rfl, -, hram, hif⟩
        · exact ⟨cpu, m', ors.getD rs, oib.getD ib, .inr ⟨rfl, .inl Hc'⟩⟩
        · simp only [Bool.and_eq_true] at hr
          refine ⟨cpu, riscvStep tk, rs, oib.getD ib, .inr ⟨rfl, .inr ?_⟩⟩
          cases tk
          · exact hr.1
          · exact hr.2
        · simp only [AxCjrReach.dataRead, Bool.not_eq_true'] at hram
          rw [hif hadm] at hram
          exact Bool.noConfusion hram
        · simp only [AxCjrReach.dataRead, Bool.not_eq_true'] at hram
          rw [hif hadm] at hram
          exact Bool.noConfusion hram
      · rcases chkPnode _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hc hn with
          ⟨-, rfl, Hc' | ⟨y, -, hr, -⟩⟩ | ⟨n, va, req, KK, rfl, -, hram, hif⟩ |
          ⟨n, va, req, KK, rfl, -, hram, hif⟩
        · exact ⟨cpu, m', ors.getD rs, oib.getD ib, .inr ⟨rfl, .inr Hc'⟩⟩
        · exact (Bool.false_ne_true hr).elim
        · simp only [AxCjrReach.dataRead, Bool.not_eq_true'] at hram
          rw [hif hadm] at hram
          exact Bool.noConfusion hram
        · simp only [AxCjrReach.dataRead, Bool.not_eq_true'] at hram
          rw [hif hadm] at hram
          exact Bool.noConfusion hram
  · -- the PLIC wire
    obtain ⟨hk, hp⟩ := awireAeqv _ _ Hw
    obtain ⟨p', k'⟩ := s'
    simp only at hk hp
    subst hk
    match p', hp with
    | .PHart c m' rs' fn' ib', hp =>
      obtain ⟨rfl, rfl, rfl, rfl, hag⟩ := hp
      refine ⟨c, m', rs', ib', ?_⟩
      rcases Hc with Hc | Hc | Hc
      · exact .inl ⟨rfl, by rw [chkPreAgree base vs good Nd Hgood _ _ _ hag]; exact Hc⟩
      · exact .inr ⟨rfl, .inl (by rw [chkPostAgree good Nd Hgood _ _ _ hag]; exact Hc)⟩
      · exact .inr ⟨rfl, .inr (by rw [chkNextAgree good Hgood _ _ _ hag]; exact Hc)⟩
  · -- the read: no row item at the row end
    obtain ⟨lb, hrow, -⟩ := Hrd
    exact (rowAtKf kf base vs i GD lb HG hrow).elim

/-- At a boundary-shaped state of the region: `good`, or still the pre-fetch boundary
(deviation 1(c)). -/
theorem InvGood (s : Athread) (c : CPU) (tk : Bool) (rs' : RegFile) (ib' : Ibch) :
    AxCjrReach.Inv kf base vs good Nd s →
    s = ⟨.PHart c (riscvStep tk) rs' none ib', kf⟩ → 0 < Nd →
    good rs' = true ∨ chkPre base vs good Nd (riscvStep tk) rs' = true := by
  rintro ⟨cpu, m, rs, ib, ⟨rfl, Hc⟩ | ⟨rfl, Hc⟩⟩ Heq HN
  · simp only [Athread.AThread.injEq, Pexv6.PHart.injEq] at Heq
    obtain ⟨⟨-, rfl, rfl, -, -⟩, -⟩ := Heq
    exact .inr Hc
  · simp only [Athread.AThread.injEq, Pexv6.PHart.injEq] at Heq
    obtain ⟨⟨-, rfl, rfl, -, -⟩, -⟩ := Heq
    refine .inl ?_
    rcases Hc with Hc | Hc
    · have Hq := chkQ _ _ _ _ _ Hc
      simp only [QPost, Bool.or_eq_true, Bool.and_eq_true] at Hq
      rcases Hq with Hq | ⟨H0, H1⟩
      · exact Hq
      · cases tk
        · rw [divergeSelf] at H0; exact (Bool.false_ne_true H0).elim
        · rw [divergeSelf] at H1; exact (Bool.false_ne_true H1).elim
    · exact chkQ _ _ _ _ _ Hc

theorem rtcInv (Hgood : ∀ rs rs', regsAgree AxRunClose.pinReg rs rs' → good rs = good rs')
    (i : Agent) (s0 s : Athread) :
    AxCjrReach.Inv kf base vs good Nd s0 → rtc (rstep (Gf kf base vs i) i) s0 s →
    AxCjrReach.Inv kf base vs good Nd s := by
  intro H0 Hr
  induction Hr with
  | refl => exact H0
  | tail _ hst ih => exact AxCjrReach.InvStep kf base vs good Nd Hgood i _ _ ih hst

/-- THE FORWARD REGION THEOREM. -/
theorem reachGood (Hgood : ∀ rs rs', regsAgree AxRunClose.pinReg rs rs' → good rs = good rs')
    (i : Agent) (cpu : CPU) (tick : Bool) (rs : RegFile) (ib : Ibch) (HN : 0 < Nd)
    (Hpre : chkPre base vs good Nd (riscvStep tick) rs = true) (s : Athread) :
    rtc (rstep (Gf kf base vs i) i) ⟨.PHart cpu (riscvStep tick) rs none ib, kf⟩ s →
    ∀ c tk rs' ib', s = ⟨.PHart c (riscvStep tk) rs' none ib', kf⟩ →
    good rs' = true ∨ chkPre base vs good Nd (riscvStep tk) rs' = true := by
  intro Hr c tk rs' ib' Heq
  have HI : AxCjrReach.Inv kf base vs good Nd s :=
    rtcInv kf base vs good Nd Hgood i _ _ ⟨cpu, riscvStep tick, rs, ib, .inl ⟨rfl, Hpre⟩⟩ Hr
  exact InvGood kf base vs good Nd s c tk rs' ib' HI Heq HN

end regions

end Weak
