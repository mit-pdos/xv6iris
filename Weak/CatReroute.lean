/-
Weak: **W11-A — the cycle RE-ROUTE lemma** (plan `notes/weak-allocproc-plan.md` rev 50, §C top
"W11 — LAUNCH PLAN" part A = W11 obligation (6) = W9a (B) (B2-exit); spike `notes/W9aB-spike.md`
§1.2–§1.3; rulings [OWN.60], [OWN.72]).  Lean-only, no Rocq twin.

**The gap.**  `CatLin.chainC` certifies each segment against its predecessor's exit
(`CertC.Pinned`: the cross edge into the entry, entry `<gmo` exit; `CertC.CSchained`: predecessor
`<gmo` exit).  A segment `(L, E)` whose exit `E` is a PRE-FENCE write — a trap-path store (frame
spill, cpu cell, lock AMO, `lk->cpu`, `p->state`, `ticks`, `swtch`'s context) or an own-stack
store of an `own = true` witness — is neither: RVWMO does not order `L` before `E` until the next
fence.  When the thread resumes on ANOTHER hart (a migration through `yield`/`swtch`), `E`'s
cross edge reaches a read `R` of that hart, and today's `chainC` has no arm for `(L, E)` (spike
§1.3: "not as-is").

**The re-route.**  The access discipline chains `R` from `E` through a release `REL` po-after `E`
(`fence rw,w; sw`) and an acquire `ACQ` po-before-or-at `R` (`amoswap.w.aq`).  Replace `E → R` by
`REL ⇝ ACQ`: the exiting segment becomes `(L, REL)` — `CertC.Pinned` by REL's fence (rule 4,
`gfenceCovers`; or, for an I/O entry, the trusted residue's (R2)) — and the next segment becomes
`(ACQ, E')` — pinned by `.aq` (rule 5) — so the re-routed chain is a `chainC` with every segment
certified, and the cycle dies by `cycleKillArmsX` unchanged.

  §1  The two certificates: `certRerouteExit` (the exiting segment) and `certRerouteIn` (the
      next one, `rrIn`: the hop `REL ⇝ ACQ` as one cross edge `X` — `Pinned` — or as any gmo
      path — `CSchained`; `ACQ` an aq read po-before-or-at the new exit); `RelAcqHops` /
      `relAcqHopsGmo` (a multi-hop lock hand-off — rfe into an aq read, aq read po-before the
      next release — is gmo-forward: rules 5 and rf only).
  §2  The plan's statement, ONE re-route: `chainCReroute` (`chainC x p pre`, the hole `(s, s')`,
      `chainC s'.exit y post` ⟹ `chainC x y (pre ++ (s.entry, REL) :: (ACQ, s'.exit) :: post)`),
      via `chainCAppend`.
  §3  ANY number of re-routes on a raw chain (overlapping ones included — a re-routed segment
      may itself be entered through a re-route): the annotated raw chain `rrRawChain` (each
      segment of `rawChainC` with an optional `Reroute` = `(REL, ACQ)`; per-segment obligations
      `rrInOk`/`rrOutOk`), its re-routed list `rrSegs`, **`chainCOfRrRaw`** (it IS a `chainC`
      from the re-routed start to the re-routed end), **`cycleKillReroute`** (a cyclic annotated
      raw chain is impossible), `rrRawChainRaw` (it annotates a `rawChainC`),
      `rrRawChainNone` (the un-re-routed case is today's classification `rawChainChainC`).
      Exit builders: `rrExitFence` (rule 4 from a `fence rw,w` between the exit and `REL`),
      `rrExitIo` (an I/O entry: (R2) of `ioResidueGmo`); entry builder: `rrInRun`.
  §4  NON-VACUITY, two computed riscv.cat-consistent (tagged) graphs:
      `rrMig*` — the spike's MIGRATION SPLIT (§1.3): hart 0 `L; E (spill); fence rw,w; REL`,
      hart 1 `ACQ (amoswap.aq); R (restore, reads E); E'`; the segment `(L, E)` has NO `CertC`
      at its predecessor (`rrMigNoCert`) yet the re-routed chain certifies (`rrMigChain`, via
      `rrExitFence` — rule 4); `rrIo*` — `kcatCex`-SHAPED (`WeakRvwmoKillIOC.lean` §2): the
      I/O segment `x →gpow w →rfi u →gpoloc v` whose step `u → v` is outside `ioStepCloses`
      (`rrIoNotCloses`, the twin of `kcatCexNotCloses`) and whose segment has NO `CertC` at
      `ioCross` (`rrIoNoCert`) is certified by the re-route (`rrIoChain`, via `rrExitIo` — (R2);
      residue `rrIoResidue`).

**Spec standing.**  FAITHFUL.  Every order used is riscv.cat's (rule 4 `fence rw,w`, rule 5
`.aq`, rf/rfe and load value, all through `CatLin.rvwmoCatAD`, implied by the published tagged
model) or the existing trusted residue `ioResidueGmo` (only in `rrExitIo`).  No trap-entry
ordering is assumed (option (D), "trap = fence", stays rejected as STRONGER than RVWMO).  The new
definitions are proof-device annotations, not trusted text.  Graph-level: the hop `REL ⇝ ACQ`
is a premise (one cross edge or a gmo fact); deriving it from `chainOkAt`'s `syncPath` through
the log identification `R` is W11's `chainHyps` work (parts C/D), as `csChainedC` does for one
lock.  A fence `rw,w` does NOT cover an I/O event (riscv.cat's fence bits are r/w only), so an
I/O entry is re-routed through (R2), not rule 4 (`rrExitIo`).

**Deviations from the plan text.**  (1) The exiting segment's certificate needs only
`entry <gmo REL`, so the annotation states that (`rrOutOk`) and two builders supply it (rule 4 /
(R2)); the plan names rule 4 only.  (2) The next segment is `Pinned` when the hop is one cross
edge (`REL →rfe ACQ`, the plan's case) and `CSchained` for a multi-hop hand-off or when
`ACQ` is itself the new exit; the plan names `Pinned` only.  (3) The cross edge `E → R` is NOT a
premise (the re-route discards it).  All three only widen the lemma.

**Name map (all new).**  `Reroute` (`rrRel`, `rrAcq`), `rrIn`, `certRerouteIn`,
`certRerouteExit`, `RelAcqHops`, `relAcqHopsGmo`, `chainCAppend`, `chainCReroute`, `rrPt`,
`rrAcqOr`, `rrSegs`, `rrInOk`, `rrOutOk`, `rrHop`, `rrRawChain`, `chainCOfRrRaw`,
`rrRawChainHop`, `cycleKillReroute`, `rrRawChainRaw`, `rrRawChainNone`, `rrExitFence`,
`rrExitIo`, `rrInRun`, `rrMigProg`, `rrMigGmo`, `rrMigT`, `rrMig`, `rrMigCatT`, `rrMigCatAD`,
`rrMigRaw`, `rrMigNoCert`, `rrMigAnn`, `rrMigChain`, `rrMigGmoLt`, `rrIoProg`, `rrIoGmo`,
`rrIoT`, `rrIo`, `rrIoCatT`, `rrIoCatAD`, `rrIoResidue`, `rrIoDiskRead14`, `rrIoNotCloses`, `rrIoRaw`,
`rrIoNoCert`, `rrIoAnn`, `rrIoChain`, `rrIoGmoLt`; Lean-only helpers `CatReroute.{runPo, poOrEq,
rrIoLbl}`.
-/
import Weak.WeakRvwmoKillIOC

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Lbl

namespace CatLin

/-! # 1. The two certificates -/

/-- The re-route data of a segment: its exit is re-routed to the release `rrRel`, and the next
segment's entry to the acquire `rrAcq`. -/
structure Reroute where
  rrRel : Geid
  rrAcq : Geid

/-- The IN side of a re-route: the hop `rel ⇝ acq` (one cross edge, or any gmo path), `acq` an
acquire read, po-before-or-at the new exit `out` (a memory event). -/
def rrIn (G : Gexec) (X : Geid → Geid → Prop) (rel acq out : Geid) : Prop :=
  (X rel acq ∨ gmoLt G rel acq) ∧ glblIs G acq lbIsR ∧ glblIs G acq lbAq ∧
    (acq = out ∨ (WeakRvwmoGraph.gpo G acq out ∧ gmem G out))

/-- The next segment, entered at the acquire: certified against the release by rule 5. -/
theorem certRerouteIn (G : Gexec) (X : Geid → Geid → Prop) (rel acq out : Geid) (h : Nat) :
    gppoCat6Gmo G → (∀ x y, X x y → gmoLt G x y) → rrIn G X rel acq out →
    CertC G X rel ⟨h, acq, out⟩ := by
  rintro h6 hX ⟨hhop, hr, haq, heq | ⟨hpo, hm⟩⟩
  · subst heq
    exact .CSchained (hhop.elim (hX _ _) id)
  · have hao : gmoLt G acq out := acqGmoAfterC G acq out h6 hpo hr haq hm
    rcases hhop with hx | hmo
    · exact .Pinned hx hao
    · exact .CSchained (gmoLtTrans G _ _ _ hmo hao)

/-- The exiting segment, re-routed to the release: `Pinned` by the cross edge into its entry. -/
theorem certRerouteExit (G : Gexec) (X : Geid → Geid → Prop) (prev rel : Geid) (s : Seg) :
    X prev s.sgEntry → gmoLt G s.sgEntry rel → CertC G X prev ⟨s.sgHart, s.sgEntry, rel⟩ :=
  fun hx hmo => .Pinned hx hmo

/-- A multi-hop lock hand-off at graph level: an rfe into an acquire read, which is po-before
the next hop's release (`gacqPo`, rule 5). -/
inductive RelAcqHops (G : Gexec) : Geid → Geid → Prop where
  | one (rel acq : Geid) : grfe G rel acq → RelAcqHops G rel acq
  | step (rel acq' rel' acq : Geid) :
      grfe G rel acq' → gacqPo G acq' rel' → RelAcqHops G rel' acq → RelAcqHops G rel acq

/-- …is gmo-forward: rf (load value) and rule 5 only. -/
theorem relAcqHopsGmo (G : Gexec) (rel acq : Geid) :
    gppoCat6Gmo G → gloadValue G → RelAcqHops G rel acq → gmoLt G rel acq := by
  intro h6 hlv h
  induction h with
  | one rel acq hrf => exact grfeGmo G rel acq hlv hrf
  | step rel acq' rel' acq hrf hap _ ih =>
    obtain ⟨hpo, hr, haq, hm⟩ := hap
    exact gmoLtTrans G _ _ _ (grfeGmo G rel acq' hlv hrf)
      (gmoLtTrans G _ _ _ (acqGmoAfterC G acq' rel' h6 hpo hr haq hm) ih)

/-! # 2. One re-route: the plan's statement -/

theorem chainCAppend (G : Gexec) (X : Geid → Geid → Prop) (x m y : Geid) (ss1 ss2 : List Seg) :
    chainC G X x m ss1 → chainC G X m y ss2 → chainC G X x y (ss1 ++ ss2) := by
  induction ss1 generalizing x with
  | nil =>
    intro h1 h2
    have h : x = m := h1
    subst h
    exact h2
  | cons s ss ih =>
    intro h1 h2
    exact ⟨h1.1, ih _ h1.2 h2⟩

/-- **THE RE-ROUTE (one hole).**  Before the hole the chain is certified up to `p`; the hole is
the segment `s` (entered from `p`, its exit NOT certified) and its successor `s'` (whatever its
certificate was); after it the chain is certified from `s'.exit`.  Re-routing `s`'s exit to
`rel` (entry `<gmo` rel) and `s'`'s entry to `acq` (`rrIn`) certifies the whole chain. -/
theorem chainCReroute (G : Gexec) (X : Geid → Geid → Prop) (x p y rel acq : Geid)
    (pre post : List Seg) (s s' : Seg) :
    gppoCat6Gmo G → (∀ a b, X a b → gmoLt G a b) →
    chainC G X x p pre → X p s.sgEntry → gmoLt G s.sgEntry rel →
    rrIn G X rel acq s'.sgExit → chainC G X s'.sgExit y post →
    chainC G X x y (pre ++ ⟨s.sgHart, s.sgEntry, rel⟩ :: ⟨s'.sgHart, acq, s'.sgExit⟩ :: post) :=
  fun h6 hX hpre hx hmo hin hpost =>
    chainCAppend G X x p y pre _ hpre
      ⟨certRerouteExit G X p rel s hx hmo, certRerouteIn G X rel acq s'.sgExit s'.sgHart h6 hX hin,
        hpost⟩

/-! # 3. Any number of re-routes on a raw chain -/

/-- The re-routed exit point: the release if re-routed. -/
def rrPt (p : Geid) : Option Reroute → Geid
  | none => p
  | some r => r.rrRel

/-- The re-routed entry point: the predecessor's acquire if it re-routed. -/
def rrAcqOr (e : Geid) : Option Reroute → Geid
  | none => e
  | some r => r.rrAcq

/-- The re-routed segment list (`ι`: the predecessor's annotation). -/
def rrSegs : Option Reroute → List (Seg × Option Reroute) → List Seg
  | _, [] => []
  | ι, (s, o) :: l => ⟨s.sgHart, rrAcqOr s.sgEntry ι, rrPt s.sgExit o⟩ :: rrSegs o l

/-- The IN obligation of an annotated segment `(s, o)` with raw predecessor exit `p` and
predecessor annotation `ι`: un-re-routed on both sides, today's certificate; entered through a
re-route, the predecessor's acquire is an aq read po-before-or-at the entry (and an un-re-routed
exit is a memory event). -/
def rrInOk (G : Gexec) (X : Geid → Geid → Prop) (p : Geid) :
    Option Reroute → Seg → Option Reroute → Prop
  | none, s, none => CertC G X p s
  | none, _, some _ => True
  | some r, s, o => glblIs G r.rrAcq lbIsR ∧ glblIs G r.rrAcq lbAq ∧
      (r.rrAcq = s.sgEntry ∨ WeakRvwmoGraph.gpo G r.rrAcq s.sgEntry) ∧
      (o = none → gmem G s.sgExit)

/-- The OUT obligation: a re-routed exit's release is po-after the exit, a memory event,
gmo-after the entry (rule 4 / (R2): `rrExitFence`, `rrExitIo`), and the hop reaches the
acquire. -/
def rrOutOk (G : Gexec) (X : Geid → Geid → Prop) (s : Seg) : Option Reroute → Prop
  | none => True
  | some r => WeakRvwmoGraph.gpo G s.sgExit r.rrRel ∧ gmem G r.rrRel ∧
      gmoLt G s.sgEntry r.rrRel ∧ (X r.rrRel r.rrAcq ∨ gmoLt G r.rrRel r.rrAcq)

/-- The hop of an annotation. -/
def rrHop (G : Gexec) (X : Geid → Geid → Prop) : Option Reroute → Prop
  | none => True
  | some r => X r.rrRel r.rrAcq ∨ gmoLt G r.rrRel r.rrAcq

/-- **THE ANNOTATED RAW CHAIN**: `rawChainC` (an `X`-edge into each entry, an `rsameC` run to its
exit) with each segment's annotation meeting `rrInOk`/`rrOutOk`; `ι`/`κ` the annotations
flowing in and out. -/
def rrRawChain (GD : Gdexec) (X : Geid → Geid → Prop) :
    Geid → Option Reroute → Geid → Option Reroute → List (Seg × Option Reroute) → Prop
  | p, ι, y, κ, [] => p = y ∧ ι = κ
  | p, ι, y, κ, (s, o) :: l =>
      X p s.sgEntry ∧ segRunC GD s ∧ rrInOk GD.gdG X p ι s o ∧ rrOutOk GD.gdG X s o ∧
        rrRawChain GD X s.sgExit o y κ l

/-- A run is program order (or empty). -/
theorem CatReroute.runPo (GD : Gdexec) (ad : List (Geid × Geid)) (e x : Geid) :
    rvwmoCatAD GD ad → rtc (rsameC GD) e x → e = x ∨ WeakRvwmoGraph.gpo GD.gdG e x := by
  intro hc h
  rcases rtc_tc.1 h with heq | ht
  · exact .inl heq
  · exact .inr (WeakRvwmoKillIO.tcGpo _ _ _ _
      (fun u v huv => WeakRvwmoKillIOC.rsameCGpo GD ad u v hc huv) ht)

theorem CatReroute.poOrEq (G : Gexec) (a e x : Geid) :
    (a = e ∨ WeakRvwmoGraph.gpo G a e) → (e = x ∨ WeakRvwmoGraph.gpo G e x) →
    a = x ∨ WeakRvwmoGraph.gpo G a x := by
  rintro (rfl | h1) (rfl | h2)
  · exact .inl rfl
  · exact .inr h2
  · exact .inr h1
  · exact .inr (gpoTrans G _ _ _ h1 h2)

/-- **THE RE-ROUTED CHAIN IS A `chainC`**, from the re-routed start to the re-routed end, every
segment certified. -/
theorem chainCOfRrRaw (GD : Gdexec) (ad : List (Geid × Geid)) (X : Geid → Geid → Prop) :
    rvwmoCatAD GD ad → (∀ a b, X a b → gmoLt GD.gdG a b) →
    ∀ (l : List (Seg × Option Reroute)) (p : Geid) (ι : Option Reroute) (y : Geid)
      (κ : Option Reroute),
      rrHop GD.gdG X ι → rrRawChain GD X p ι y κ l →
      chainC GD.gdG X (rrPt p ι) (rrPt y κ) (rrSegs ι l) := by
  intro hc hX l
  have h6 : gppoCat6Gmo GD.gdG := hc.2.1
  induction l with
  | nil =>
    intro p ι y κ _ h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  | cons so l ih =>
    obtain ⟨s, o⟩ := so
    intro p ι y κ hhop h
    obtain ⟨hx, hrun, hin, hout, hrest⟩ := h
    have hhop' : rrHop GD.gdG X o := by
      cases o with
      | none => trivial
      | some r => exact hout.2.2.2
    refine ⟨?_, ih s.sgExit o y κ hhop' hrest⟩
    cases ι with
    | none =>
      cases o with
      | none => exact hin
      | some r => exact certRerouteExit GD.gdG X p r.rrRel s hx hout.2.2.1
    | some r0 =>
      obtain ⟨hr, haq, hae, hm⟩ := hin
      have hae' := CatReroute.poOrEq GD.gdG _ _ _ hae (CatReroute.runPo GD ad _ _ hc hrun)
      refine certRerouteIn GD.gdG X r0.rrRel r0.rrAcq _ s.sgHart h6 hX ⟨hhop, hr, haq, ?_⟩
      cases o with
      | none =>
        rcases hae' with heq | hpo
        · exact .inl heq
        · exact .inr ⟨hpo, hm rfl⟩
      | some r =>
        obtain ⟨hpor, hmr, -, -⟩ := hout
        rcases hae' with heq | hpo
        · exact .inr ⟨heq ▸ hpor, hmr⟩
        · exact .inr ⟨gpoTrans GD.gdG _ _ _ hpo hpor, hmr⟩

/-- The out-flowing annotation's hop holds (from the last segment's `rrOutOk`). -/
theorem rrRawChainHop (GD : Gdexec) (X : Geid → Geid → Prop) :
    ∀ (l : List (Seg × Option Reroute)) (p : Geid) (ι : Option Reroute) (y : Geid)
      (κ : Option Reroute),
      rrHop GD.gdG X ι → rrRawChain GD X p ι y κ l → rrHop GD.gdG X κ := by
  intro l
  induction l with
  | nil =>
    intro p ι y κ hh h
    obtain ⟨-, rfl⟩ := h
    exact hh
  | cons so l ih =>
    obtain ⟨s, o⟩ := so
    intro p ι y κ _ h
    obtain ⟨-, -, -, hout, hrest⟩ := h
    refine ih s.sgExit o y κ ?_ hrest
    cases o with
    | none => trivial
    | some r => exact hout.2.2.2

/-- **THE KILL WITH RE-ROUTES**: a cyclic annotated raw chain is impossible. -/
theorem cycleKillReroute (GD : Gdexec) (ad : List (Geid × Geid)) (X : Geid → Geid → Prop)
    (z : Geid) (ι : Option Reroute) (l : List (Seg × Option Reroute)) :
    rvwmoCatAD GD ad → (∀ a b, X a b → gmoLt GD.gdG a b) →
    l ≠ [] → rrRawChain GD X z ι z ι l → False := by
  intro hc hX hne h
  have hhop : rrHop GD.gdG X ι := by
    cases l with
    | nil => exact absurd rfl hne
    | cons so l =>
      obtain ⟨s, o⟩ := so
      obtain ⟨-, -, -, hout, hrest⟩ := h
      refine rrRawChainHop GD X l s.sgExit o z ι ?_ hrest
      cases o with
      | none => trivial
      | some r => exact hout.2.2.2
  have hch := chainCOfRrRaw GD ad X hc hX l z ι z ι hhop h
  refine cycleKillArmsX GD.gdG X (rrPt z ι) (rrSegs ι l) hX ?_ hch
  cases l with
  | nil => exact absurd rfl hne
  | cons so l => obtain ⟨s, o⟩ := so; simp [rrSegs]

/-- The annotated raw chain annotates a raw chain. -/
theorem rrRawChainRaw (GD : Gdexec) (X : Geid → Geid → Prop) :
    ∀ (l : List (Seg × Option Reroute)) (p : Geid) (ι : Option Reroute) (y : Geid)
      (κ : Option Reroute),
      rrRawChain GD X p ι y κ l → rawChainC GD X p y (l.map Prod.fst) := by
  intro l
  induction l with
  | nil =>
    intro p ι y κ h
    exact h.1
  | cons so l ih =>
    obtain ⟨s, o⟩ := so
    intro p ι y κ h
    obtain ⟨hx, hrun, -, -, hrest⟩ := h
    exact ⟨hx, hrun, ih _ _ _ _ hrest⟩

/-- With NO re-route the annotated chain is today's classified raw chain (`rawChainChainC`'s
input): a raw chain whose every segment is certified. -/
theorem rrRawChainNone (GD : Gdexec) (X : Geid → Geid → Prop) (ss : List Seg) :
    (∀ prev s, s ∈ ss → X prev s.sgEntry → segRunC GD s → CertC GD.gdG X prev s) →
    ∀ (x y : Geid) (ss' : List Seg), ss' ⊆ ss → rawChainC GD X x y ss' →
      rrRawChain GD X x none y none (ss'.map fun s => (s, none)) := by
  intro hcl x y ss'
  induction ss' generalizing x with
  | nil =>
    intro _ h
    exact ⟨h, rfl⟩
  | cons s ss' ih =>
    intro hsub h
    obtain ⟨hx, hrun, hrest⟩ := h
    have hs : s ∈ ss := hsub (by simp)
    have hsub' : ss' ⊆ ss := fun t ht => hsub (List.mem_cons_of_mem s ht)
    exact ⟨hx, hrun, hcl x s hs hx hrun, trivial, ih _ hsub' hrest⟩

/-- **Exit builder, rule 4**: a `fence rw,w` between the exit and the release `rel` (a write)
orders the entry (a read or a write) before `rel`. -/
theorem rrExitFence (GD : Gdexec) (ad : List (Geid × Geid)) (s : Seg) (rel : Geid) (sr : Bool) :
    rvwmoCatAD GD ad → segRunC GD s →
    (glblIs GD.gdG s.sgEntry lbIsR ∨ glblIs GD.gdG s.sgEntry lbIsW) →
    gfenceBetween GD.gdG s.sgExit rel true true sr true → glblIs GD.gdG rel lbIsW →
    WeakRvwmoGraph.gpo GD.gdG s.sgExit rel ∧ gmem GD.gdG rel ∧ gmoLt GD.gdG s.sgEntry rel := by
  intro hc hrun hent hfb hrel
  obtain ⟨hag, hlt, kf, hk1, hk2, hkf⟩ := hfb
  have hrs : (gxLbl GD.gdG rel).isSome := by
    obtain ⟨l, hl, -⟩ := hrel
    simp [hl]
  have hes : (gxLbl GD.gdG s.sgEntry).isSome := by
    rcases hent with ⟨l, hl, -⟩ | ⟨l, hl, -⟩ <;> simp [hl]
  have hrun' := CatReroute.runPo GD ad _ _ hc hrun
  have hxs : (gxLbl GD.gdG s.sgExit).isSome := by
    rcases hrun' with heq | hpo
    · rw [← heq]; exact hes
    · exact hpo.2.2.2
  have hle : s.sgEntry.1 = s.sgExit.1 ∧ s.sgEntry.2 ≤ s.sgExit.2 := by
    rcases hrun' with heq | hpo
    · rw [heq]; exact ⟨rfl, Nat.le_refl _⟩
    · exact ⟨hpo.1, Nat.le_of_lt hpo.2.1⟩
  refine ⟨⟨hag, hlt, hxs, hrs⟩, WeakRvwmoGraph.glblIsWGmem _ _ hrel, ?_⟩
  have hfc : gfenceCovers GD.gdG s.sgEntry rel := by
    refine ⟨true, true, sr, true, ⟨hle.1.trans hag, by omega, kf, by omega, hk2, ?_⟩, ?_, ?_⟩
    · rw [hle.1]; exact hkf
    · rcases hent with h | h
      · exact .inl ⟨h, rfl⟩
      · exact .inr ⟨h, rfl⟩
    · exact .inr ⟨hrel, rfl⟩
  exact fenceGmoAfterC GD.gdG _ _ hc.2.1 hfc

/-- **Exit builder, (R2)**: an I/O entry is ordered before a po-later RAM write by the trusted
residue (`fence rw,w` does not cover I/O). -/
theorem rrExitIo (GF : Gfexec) (ad : List (Geid × Geid)) (s : Seg) (rel : Geid) :
    rvwmoCatAD GF.gfGd ad → ioResidueGmo GF → segRunC GF.gfGd s →
    gisIo GF.gfGd.gdG s.sgEntry = true → WeakRvwmoGraph.gpo GF.gfGd.gdG s.sgExit rel →
    gisW GF.gfGd.gdG rel = true →
    WeakRvwmoGraph.gpo GF.gfGd.gdG s.sgExit rel ∧ gmem GF.gfGd.gdG rel ∧
      gmoLt GF.gfGd.gdG s.sgEntry rel := by
  intro hc hres hrun hio hpo hw
  refine ⟨hpo, WeakRvwmoGraph.glblIsWGmem _ _ (WeakRvwmoKillIOC.gisWGlbl _ _ hw), ?_⟩
  have hper : WeakRvwmoGraph.gpo GF.gfGd.gdG s.sgEntry rel := by
    rcases CatReroute.runPo GF.gfGd ad _ _ hc hrun with heq | hp
    · rw [heq]; exact hpo
    · exact gpoTrans _ _ _ _ hp hpo
  exact hres _ _ (Or.inr (Or.inl ⟨hper, hio, hw⟩))

/-- **Entry builder**: an acquire po-before-or-at the raw entry `R` (the plan's `ACQ ≤po R`). -/
theorem rrInRun (G : Gexec) (s : Seg) (o : Option Reroute) (r : Reroute) (p : Geid)
    (X : Geid → Geid → Prop) :
    glblIs G r.rrAcq lbIsR → glblIs G r.rrAcq lbAq →
    (r.rrAcq = s.sgEntry ∨ WeakRvwmoGraph.gpo G r.rrAcq s.sgEntry) →
    (o = none → gmem G s.sgExit) → rrInOk G X p (some r) s o :=
  fun hr haq hae hm => ⟨hr, haq, hae, hm⟩

/-! # 4. Non-vacuity -/

/-! ## 4.1 The migration split (spike §1.3)

Hart 0 (A): `L = lb [0]` (reads hart 2's store — the cross edge into the segment), `E = sb [8] ← 1`
(the spill), `fence rw,w`, `REL = sb [4] ← 0` (the release).  Hart 1 (B): `ACQ = amoswap.aq [4]`
(reads `REL`), `R = lb [8]` (the restore, reads `E` — cross-hart), `E' = sb [9] ← 1`.  Hart 2:
`q = sb [0] ← 1`.  gmo = `[E; q; L; REL; ACQ; R; E']` — `E` before `L`: RVWMO does not order
`L` before the spill.  The raw chain `q →rfe (L ⇝ E) →rfe (R ⇝ E')`: the segment `(L, E)` has
no certificate; re-routed, `(L, REL)` is pinned by the fence and `(ACQ, E')` by `.aq`. -/

def rrMigProg : List (List Lbl) :=
  [[LLoad false 0 [2] [b1], LStore false 8 [b1] .WCplain, LFence true true false true,
    LStore false 4 [b0] .WCplain],
   [LRmw true false 4 [3] [b0] [b1] .WCplain, LLoad false 8 [1] [b1], LStore false 9 [b1] .WCplain],
   [LStore false 0 [b1] .WCplain]]

def rrMigGmo : List Geid := [(0, 1), (2, 0), (0, 0), (0, 3), (1, 0), (1, 1), (1, 2)]

/-- The graph, TAGGED (no dependencies). -/
def rrMigT : GdexecT := mkgt rrMigProg rrMigGmo []

def rrMig : Gdexec := forget rrMigT

/-- The published quantifier's model holds (computed). -/
theorem rrMigCatT : rvwmoCatConsistentT rrMigT :=
  catTConsistentBSound _ (by decide +kernel)

theorem rrMigCatAD : rvwmoCatAD rrMig (gtAd rrMigT.gtG rrMigT.gtDeps) :=
  catADOfCatT rrMigT rrMigCatT

/-- The raw chain `q →rfe (L ⇝ E) →rfe (R ⇝ E')`. -/
theorem rrMigRaw :
    rawChainC rrMig (gcrossE rrMig.gdG) (2, 0) (1, 2)
      [⟨0, (0, 0), (0, 1)⟩, ⟨1, (1, 1), (1, 2)⟩] :=
  ⟨.inl ((grfeBSpec _ _ _).1 (by decide +kernel)),
    rtc_once (Or.inl ⟨(gpoBSpec _ _ _).1 (by decide +kernel),
      ⟨LLoad false 0 [2] [b1], by decide +kernel, rfl⟩, by decide +kernel⟩),
    .inl ((grfeBSpec _ _ _).1 (by decide +kernel)),
    rtc_once (Or.inl ⟨(gpoBSpec _ _ _).1 (by decide +kernel),
      ⟨LLoad false 8 [1] [b1], by decide +kernel, rfl⟩, by decide +kernel⟩),
    rfl⟩

/-- **The segment `(L, E)` has NO certificate** at its predecessor `q`: `E <gmo L` and
`E <gmo q`. -/
theorem rrMigNoCert : ¬ CertC rrMig.gdG (gcrossE rrMig.gdG) (2, 0) ⟨0, (0, 0), (0, 1)⟩ := by
  rintro (⟨-, h⟩ | h | h)
  · exact absurd ((gmoLtBSpec _ _ _).2 h) (by decide +kernel)
  · exact absurd ((gmoLtBSpec _ _ _).2 h) (by decide +kernel)
  · exact h

/-- The annotation: `(L, E)` re-routed to `REL = (0,3)`, the next entry to `ACQ = (1,0)`. -/
theorem rrMigAnn :
    rrRawChain rrMig (gcrossE rrMig.gdG) (2, 0) none (1, 2) none
      [(⟨0, (0, 0), (0, 1)⟩, some ⟨(0, 3), (1, 0)⟩), (⟨1, (1, 1), (1, 2)⟩, none)] := by
  obtain ⟨hx0, hr0, hx1, hr1, -⟩ := rrMigRaw
  have hex := rrExitFence rrMig _ ⟨0, (0, 0), (0, 1)⟩ (0, 3) false rrMigCatAD hr0
    (.inl ((glblBSpec _ _ _).1 (by decide +kernel)))
    ⟨rfl, by decide, 2, by decide, by decide, by decide +kernel⟩
    ((glblBSpec _ _ _).1 (by decide +kernel))
  refine ⟨hx0, hr0, trivial, ⟨hex.1, hex.2.1, hex.2.2,
    .inl (.inl ((grfeBSpec _ _ _).1 (by decide +kernel)))⟩, hx1, hr1, ?_, trivial, rfl, rfl⟩
  exact rrInRun _ _ _ _ _ _ ((glblBSpec _ _ _).1 (by decide +kernel))
    ((glblBSpec _ _ _).1 (by decide +kernel)) (.inr ((gpoBSpec _ _ _).1 (by decide +kernel)))
    (fun _ => ⟨LStore false 9 [b1] .WCplain, by decide +kernel, rfl⟩)

/-- **…and the re-routed chain certifies**: `chainC` over `[(L, REL); (ACQ, E')]`. -/
theorem rrMigChain :
    chainC rrMig.gdG (gcrossE rrMig.gdG) (2, 0) (1, 2)
      [⟨0, (0, 0), (0, 3)⟩, ⟨1, (1, 0), (1, 2)⟩] :=
  chainCOfRrRaw rrMig _ (gcrossE rrMig.gdG) rrMigCatAD
    (fun a b => gcrossEGmo _ a b rrMigCatAD.1 rrMigCatAD.2.2.1) _ (2, 0) none (1, 2) none trivial
    rrMigAnn

theorem rrMigGmoLt : gmoLt rrMig.gdG (2, 0) (1, 2) :=
  chainCGmo _ _ _ _ _ (fun a b => gcrossEGmo _ a b rrMigCatAD.1 rrMigCatAD.2.2.1) (by simp)
    rrMigChain

/-! ## 4.2 The `kcatCex`-shaped I/O segment

Hart 0: `kcatCex`'s row 0 (`x` = UART store, `w = sb [1] ← 1`, `u = lh [0]` with byte 1 FORWARDED
from `w`, `v = lb [0]` — the same source as `u`'s byte 0), then `fence rw,w` and `REL = sb [4] ←
0`.  Hart 1: `ACQ = amoswap.aq [4]` (reads `REL`), `w2 = sb [0] ← 1`.  Hart 2: `z` = UART store.
gmo = `[u; v; z; x; w; REL; ACQ; w2]`.  The raw chain at `ioCross`: `z →gmo|IO (x ⇝ v) →fr (w2)`;
the step `u → v` is outside `ioStepCloses` and the segment `(x, v)` has no certificate;
re-routed, `(x, REL)` is pinned by (R2) and `(ACQ, w2)` by `.aq`. -/

def rrIoProg : List (List Lbl) :=
  [[LIo .wr 0x10000001 [0], LStore false 1 [b1] .WCplain, LLoad false 0 [0, 1] [b0, b1],
    LLoad false 0 [0] [b0], LFence true true false true, LStore false 4 [b0] .WCplain],
   [LRmw true false 4 [2] [b0] [b1] .WCplain, LStore false 0 [b1] .WCplain],
   [LIo .wr 0x10000001 [0]]]

def rrIoGmo : List Geid := [(0, 2), (0, 3), (2, 0), (0, 0), (0, 1), (0, 5), (1, 0), (1, 1)]

/-- The graph, TAGGED (no dependencies). -/
def rrIoT : GdexecT := mkgt rrIoProg rrIoGmo []

/-- The fabric bundle: EMPTY fabric list. -/
def rrIo : Gfexec := ⟨forget rrIoT, []⟩

/-- The published quantifier's model holds (computed). -/
theorem rrIoCatT : rvwmoCatConsistentT rrIoT :=
  catTConsistentBSound _ (by decide +kernel)

theorem rrIoCatAD : rvwmoCatAD rrIo.gfGd (gtAd rrIoT.gtG rrIoT.gtDeps) :=
  catADOfCatT rrIoT rrIoCatT

theorem CatReroute.rrIoLbl (e : Geid) :
    (gxLbl rrIo.gfGd.gdG e).isSome = true →
      e = (0, 0) ∨ e = (0, 1) ∨ e = (0, 2) ∨ e = (0, 3) ∨ e = (0, 4) ∨ e = (0, 5) ∨
      e = (1, 0) ∨ e = (1, 1) ∨ e = (2, 0) := by
  obtain ⟨i, k⟩ := e
  intro h
  rcases i with _ | _ | _ | i <;> rcases k with _ | _ | _ | _ | _ | _ | k <;>
    simp [gxLbl, rrIo, rrIoT, mkgt, forget, rrIoProg] at h ⊢

/-- The trusted residue holds. -/
theorem rrIoResidue : ioResidueGmo rrIo := by
  intro x y hr
  have hxy : (gxLbl rrIo.gfGd.gdG x).isSome = true ∧
      (gxLbl rrIo.gfGd.gdG y).isSome = true := by
    rcases hr with ⟨hp, -⟩ | ⟨hp, -⟩ | ⟨hp, -⟩ | ⟨hx, hy, -⟩ | ⟨hx, hy, -⟩
    · exact ⟨hp.2.2.1, hp.2.2.2⟩
    · exact ⟨hp.2.2.1, hp.2.2.2⟩
    · exact ⟨hp.2.2.1, hp.2.2.2⟩
    · exact ⟨GraphFabResidue.gisIoSome _ _ hx, GraphFabResidue.gisIoSome _ _ hy⟩
    · exact ⟨GraphFabResidue.gmemSome _ _ hx, GraphFabResidue.gmemSome _ _ hy⟩
  rcases CatReroute.rrIoLbl x hxy.1 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  rcases CatReroute.rrIoLbl y hxy.2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  first
  | (show gmoLt rrIo.gfGd.gdG _ _; exact (gmoLtBSpec _ _ _).1 (by decide +kernel))
  | (exfalso
     rcases hr with ⟨hp, hm, hx, hy⟩ | ⟨hp, hx, hy⟩ | ⟨hp, hx, hy, hn⟩ | ⟨hx, hy, hp⟩ |
       ⟨hx, hy, hb⟩
     all_goals first
       | exact absurd hp.2.1 (by decide)
       | exact absurd hp.1 (by decide)
       | exact absurd hx (by decide +kernel)
       | exact absurd hy (by decide +kernel)
       | exact absurd hn (by decide)
       | (obtain ⟨i, j, hi, -⟩ := hb; simp [rrIo] at hi))

/-- No disk row: the disk-read anchor pairs are vacuous (`ioCross ⊆ gmo` needs it). -/
theorem rrIoDiskRead14 : gdiskRead14 rrIo.gfGd.gdG := by
  intro e a hpo _ _ _ ha
  rcases CatReroute.rrIoLbl a hpo.2.2.2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact absurd ha (by decide)

/-- **The step `u → v` is OUTSIDE `ioStepCloses`** (for every rule-12 list) — `kcatCexNotCloses`
at this graph. -/
theorem rrIoNotCloses (ad : List (Geid × Geid)) :
    ¬ ioStepCloses rrIo ad (0, 0) (0, 2) (0, 3) := by
  rintro ((hw | hio | ⟨hux, -⟩ | ⟨-, pr, sr, sw, hfb, -⟩) |
    (hrf | ⟨w, a, t, val, hrdu, hat, -, -, t', val', hrdv⟩ | ⟨a, val, hwb, -⟩))
  · exact absurd hw (by decide +kernel)
  · exact absurd hio (by decide +kernel)
  · rcases hux with h | h
    · simp at h
    · exact absurd ((gmoLtBSpec _ _ _).2 h) (by decide +kernel)
  · obtain ⟨-, -, kf, h1, h2, -⟩ := hfb
    simp at h1 h2
    omega
  · obtain ⟨⟨a, t, vv, ⟨l, base, ts, vs, j, hl, hrd, hts, -⟩, hat⟩, -⟩ := hrf
    simp [gxLbl, rrIo, rrIoT, mkgt, forget, rrIoProg] at hl
    subst hl
    simp [lbRd] at hrd
    obtain ⟨-, rfl, -⟩ := hrd
    have ht : t = 0 := by
      rcases j with _ | j <;> simp at hts
      exact hts.symm
    subst ht
    simp [gwriteAt] at hat
  · obtain ⟨l, base, ts, vs, j, hl, hrd, hts, -, hacc⟩ := hrdv
    simp [gxLbl, rrIo, rrIoT, mkgt, forget, rrIoProg] at hl
    subst hl
    simp [lbRd] at hrd
    obtain ⟨rfl, rfl, rfl⟩ := hrd
    have hj : j = 0 := by
      rcases j with _ | j
      · rfl
      · simp at hts
    subst hj
    simp [accAddr] at hacc
    subst hacc
    obtain ⟨l', base', ts', vs', j', hl', hrd', hts', -, hacc'⟩ := hrdu
    simp [gxLbl, rrIo, rrIoT, mkgt, forget, rrIoProg] at hl'
    subst hl'
    simp [lbRd] at hrd'
    obtain ⟨rfl, rfl, rfl⟩ := hrd'
    have hj' : j' = 0 := by simp [accAddr] at hacc'; omega
    subst hj'
    simp at hts'
    subst hts'
    simp [gwriteAt] at hat
  · obtain ⟨l, base, vs, j, hl, hwr, -⟩ := hwb
    simp [gxLbl, rrIo, rrIoT, mkgt, forget, rrIoProg] at hl
    subst hl
    simp [lbWr] at hwr

/-- The raw chain at `ioCross`: `z →gmo|IO (x →gpow w →rfi u →gpoloc v) →fr (w2)`. -/
theorem rrIoRaw :
    rawChainC rrIo.gfGd (ioCross rrIo) (2, 0) (1, 1)
      [⟨0, (0, 0), (0, 3)⟩, ⟨1, (1, 1), (1, 1)⟩] := by
  have e1 : rsameC rrIo.gfGd (0, 0) (0, 1) :=
    Or.inl ⟨(gpoBSpec _ _ _).1 (by decide +kernel),
      GraphFabResidue.gisIoGmem _ _ (by decide +kernel), by decide +kernel⟩
  have e2 : rsameC rrIo.gfGd (0, 1) (0, 2) :=
    Or.inr (Or.inr (Or.inr ⟨(grfBSpec _ _ _).1 (by decide +kernel), rfl⟩))
  have e3 : rsameC rrIo.gfGd (0, 2) (0, 3) :=
    Or.inr (Or.inl (Or.inl ((gpolocBSpec _ _ _).1 (by decide +kernel))))
  exact ⟨.inr (.inr (.inl ⟨by decide +kernel, by decide +kernel,
      (gmoLtBSpec _ _ _).1 (by decide +kernel)⟩)),
    rtc_l e1 (rtc_l e2 (rtc_once e3)),
    .inl (.inr (.inr ((gfrBSpec _ _ _).1 (by decide +kernel)))),
    rtc_refl _, rfl⟩

/-- **The segment `(x, v)` has NO certificate** at `ioCross`: `v <gmo x` and `v <gmo z`. -/
theorem rrIoNoCert : ¬ CertC rrIo.gfGd.gdG (ioCross rrIo) (2, 0) ⟨0, (0, 0), (0, 3)⟩ := by
  rintro (⟨-, h⟩ | h | h)
  · exact absurd ((gmoLtBSpec _ _ _).2 h) (by decide +kernel)
  · exact absurd ((gmoLtBSpec _ _ _).2 h) (by decide +kernel)
  · exact h

/-- The annotation: `(x, v)` re-routed to `REL = (0,5)` ((R2)), the next entry to
`ACQ = (1,0)`. -/
theorem rrIoAnn :
    rrRawChain rrIo.gfGd (ioCross rrIo) (2, 0) none (1, 1) none
      [(⟨0, (0, 0), (0, 3)⟩, some ⟨(0, 5), (1, 0)⟩), (⟨1, (1, 1), (1, 1)⟩, none)] := by
  obtain ⟨hx0, hr0, hx1, hr1, -⟩ := rrIoRaw
  have hex := rrExitIo rrIo _ ⟨0, (0, 0), (0, 3)⟩ (0, 5) rrIoCatAD rrIoResidue hr0
    (by decide +kernel) ((gpoBSpec _ _ _).1 (by decide +kernel)) (by decide +kernel)
  refine ⟨hx0, hr0, trivial, ⟨hex.1, hex.2.1, hex.2.2,
    .inl (.inl (.inl ((grfeBSpec _ _ _).1 (by decide +kernel))))⟩, hx1, hr1, ?_, trivial, rfl,
    rfl⟩
  exact rrInRun _ _ _ _ _ _ ((glblBSpec _ _ _).1 (by decide +kernel))
    ((glblBSpec _ _ _).1 (by decide +kernel)) (.inr ((gpoBSpec _ _ _).1 (by decide +kernel)))
    (fun _ => ⟨LStore false 0 [b1] .WCplain, by decide +kernel, rfl⟩)

/-- **…and the re-routed chain certifies** at `ioCross`: `[(x, REL); (ACQ, w2)]`. -/
theorem rrIoChain :
    chainC rrIo.gfGd.gdG (ioCross rrIo) (2, 0) (1, 1)
      [⟨0, (0, 0), (0, 5)⟩, ⟨1, (1, 0), (1, 1)⟩] :=
  chainCOfRrRaw rrIo.gfGd _ (ioCross rrIo) rrIoCatAD (ioCrossGmo rrIo rrIoCatAD.1 rrIoCatAD.2.2.1 rrIoResidue rrIoDiskRead14) _
    (2, 0) none (1, 1) none trivial rrIoAnn

theorem rrIoGmoLt : gmoLt rrIo.gfGd.gdG (2, 0) (1, 1) :=
  chainCGmo _ _ _ _ _ (ioCrossGmo rrIo rrIoCatAD.1 rrIoCatAD.2.2.1 rrIoResidue rrIoDiskRead14) (by simp) rrIoChain

end CatLin

end Weak
