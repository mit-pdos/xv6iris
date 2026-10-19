/-
Weak: **W11-F row 6b′ [R43.1] (a) — THE RE-TAG INSIDE THE CLASSIFICATION.**  Lean-only, no Rocq twin.

`CapPcLog.readAtPrimedOf` gives W11-C's realized read with its release-site clause only at a PRIMED
twin `cf′` (`WbPrimed.cfgRel`: logs equal up to a positional re-tag `retagLog f`), because on W4's
registered machine the walker's A/D write-back after `fence rw,w` clears `wRelp` and the release `sw`
is `.WCplain` there [OWN.97].  The kill's graphs (and route P's member, whose labels are GF's) carry
the REGISTERED classes.  This file makes the two meet:

  §1  **the upgrade-only re-tag** `CapRetag.logUp L L′`: the logs agree on every byte, author and
      position, and a class changes only from `.WCplain` (registered) to `.WCrel` (primed)
      (`CapRetag.clsUp`); `.WCexcl` never moves.  `CapRetag.logUpRetag`: it IS a `retagLog`.
  §2  **the primed twin is an upgrade** (`CapRetag.chainOfContRUp`): along W4's record the primed
      run keeps every registered `wRelp` (`CapRetag.relpLe`: the walker's write-back is the only
      arm that differs, and there the registered flag is cleared), so every appended class is an
      upgrade (`CapRetag.pclsEvMono`: the class reads `wRelp` monotonically).  This is the precise
      content of "class-blind except at release sites, where the re-tag is exactly `.WCrel`" —
      NOTE (finding F-6b′-2, `PROGRESS-W11F-6i6m.md`): the upgraded positions are the first
      explicit store after ANY `pw ∧ sw` fence (`fence rw,w`, `fence rw,rw`, …) when a walker
      write-back intervened, not only the two `releasePcs`.
  §3  **ONE primed log for the whole run** (`CapRetag.readAtTwin`): the primed twin of the full
      record ends at `cN′` with `logUp cN.pcLog cN′.pcLog`; at EVERY record point the primed
      pre-configuration is related to the registered one, its log is a prefix of `cN′.pcLog`, and
      it carries `relSiteWCrel σ` from the export, (a2) and (a3) at that prefix.  So every realized
      read is a `readAt` over the SAME primed log `L′ := cN′.pcLog` (`CapRetag.readAtUp`) — what
      `segRealized GD L′` asks.
  §4  **the consumers**: W11-D's derivation `chainHypsOfSyncPath` at a PRIMED read and a
      REGISTERED graph (`CapRetag.chainHypsOfSyncPathUp`); the class-blind log facts (`latest`,
      `logByte`, `altFold`, `wlpHolderAt`, `wlpAlt`, `regZeroAt`, `rmwLatest`: equal; `wlpAt`,
      `wprotAt`, `protReg`, `protRegZ`, `wpublished`: upward; `acqAqLog`, `relCoversLog`,
      `badSeg`: downward); and THE CLAIM over the re-tag, `CapRetag.l2ClaimAtCDUp` (the bad arm
      read at the primed log) with its kill `CapRetag.cycleKillCDUp`.

Spec: FAITHFUL (proof organisation; RVWMO's rule 4 orders EXPLICIT later stores, Svadu's A/D update
is an implicit access — the primed reading is the faithful one [OWN.97]; nothing assumed).
Lean-only helpers `CapRetag.*`.
-/
import Weak.CapPcLog
import Weak.WbPrimedArm
import Weak.GraphFetchN2
import Weak.CertZ18

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Sail Sail.ConcurrencyInterfaceV1 LeanRV64D
open MachOfPf RelSiteProvPc PfStepTsoMem
open Wlabel

/-! # 1. The upgrade-only re-tag -/

/-- A class moves at most from `.WCplain` to `.WCrel`. -/
def CapRetag.clsUp (k k' : WmClass) : Prop := k' = k ∨ (k = .WCplain ∧ k' = .WCrel)

/-- Two messages agree but for an upgraded class. -/
def CapRetag.msgUp (m m' : Wmsg) : Prop :=
  m'.wmPa = m.wmPa ∧ m'.wmData = m.wmData ∧ m'.wmTid = m.wmTid ∧ CapRetag.clsUp m.wmAk m'.wmAk

/-- **THE UPGRADE-ONLY RE-TAG** of a log. -/
def CapRetag.logUp (L L' : List Wmsg) : Prop := List.Forall₂ CapRetag.msgUp L L'

theorem CapRetag.clsUpRefl (k : WmClass) : CapRetag.clsUp k k := .inl rfl

theorem CapRetag.msgUpRefl (m : Wmsg) : CapRetag.msgUp m m := ⟨rfl, rfl, rfl, .inl rfl⟩

theorem CapRetag.logUpRefl (L : List Wmsg) : CapRetag.logUp L L := by
  induction L with
  | nil => exact .nil
  | cons m L ih => exact .cons (CapRetag.msgUpRefl m) ih

theorem CapRetag.clsUpExcl {k k' : WmClass} (h : CapRetag.clsUp k k') :
    (k' = .WCexcl ↔ k = .WCexcl) := by
  rcases h with rfl | ⟨rfl, rfl⟩
  · exact Iff.rfl
  · exact ⟨fun h => (by cases h), fun h => (by cases h)⟩

theorem CapRetag.clsUpPlain {k k' : WmClass} (h : CapRetag.clsUp k k') :
    k' = .WCplain → k = .WCplain := by
  rcases h with rfl | ⟨rfl, -⟩
  · exact id
  · exact fun _ => rfl

theorem CapRetag.clsUpNonplain {k k' : WmClass} (h : CapRetag.clsUp k k') :
    k ≠ .WCplain → k' = k := by
  rcases h with h | ⟨h, -⟩
  · exact fun _ => h
  · exact fun hn => absurd h hn

theorem CapRetag.clsUpRel {k k' : WmClass} (h : CapRetag.clsUp k k') :
    k = .WCrel → k' = .WCrel := by
  rintro rfl
  rcases h with h | ⟨h, -⟩
  · exact h
  · cases h

theorem CapRetag.msgUpByte {m m' : Wmsg} (h : CapRetag.msgUp m m') (a : Int) :
    msgByte m' a = msgByte m a := by
  obtain ⟨hp, hd, -, -⟩ := h
  simp only [msgByte, hp, hd]

theorem CapRetag.logUpLength {L L' : List Wmsg} (h : CapRetag.logUp L L') : L'.length = L.length :=
  (List.Forall₂.length_eq h).symm

theorem CapRetag.logUpLookup {L L' : List Wmsg} (h : CapRetag.logUp L L') :
    ∀ (p : Nat) (m : Wmsg), L[p]? = some m → ∃ m', L'[p]? = some m' ∧ CapRetag.msgUp m m' := by
  induction h with
  | nil => intro p m hp; simp at hp
  | cons hxy _ ih =>
    intro p m hp
    cases p with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hp
      subst hp
      exact ⟨_, rfl, hxy⟩
    | succ p =>
      simp only [List.getElem?_cons_succ] at hp ⊢
      exact ih p m hp

theorem CapRetag.logUpLookupInv {L L' : List Wmsg} (h : CapRetag.logUp L L') :
    ∀ (p : Nat) (m' : Wmsg), L'[p]? = some m' → ∃ m, L[p]? = some m ∧ CapRetag.msgUp m m' :=
  WbPrimed.forall₂Lookup h

theorem CapRetag.logUpTake {L L' : List Wmsg} (h : CapRetag.logUp L L') (n : Nat) :
    CapRetag.logUp (L.take n) (L'.take n) :=
  WbPrimed.forall₂Take h n

theorem CapRetag.logUpDrop {L L' : List Wmsg} (h : CapRetag.logUp L L') :
    ∀ n : Nat, CapRetag.logUp (L.drop n) (L'.drop n) := by
  induction h with
  | nil => intro n; simp only [List.drop_nil]; exact .nil
  | cons hxy hr ih =>
    intro n
    cases n with
    | zero => exact .cons hxy hr
    | succ n => simp only [List.drop_succ_cons]; exact ih n

theorem CapRetag.logUpApp {L L' M M' : List Wmsg} (h : CapRetag.logUp L L') (hm : CapRetag.logUp M M') :
    CapRetag.logUp (L ++ M) (L' ++ M') := by
  induction h with
  | nil => exact hm
  | cons hxy _ ih => exact .cons hxy ih

/-- The positional class function of the primed log. -/
def CapRetag.fOf (L' : List Wmsg) (p : Nat) : WmClass := (L'[p]?).elim .WCplain Wmsg.wmAk

/-- **The upgrade IS a `retagLog`.** -/
theorem CapRetag.logUpRetag {L L' : List Wmsg} (h : CapRetag.logUp L L') :
    L' = retagLog (CapRetag.fOf L') L := by
  apply List.ext_getElem?
  intro p
  rw [retagLogLookup]
  cases hp : L[p]? with
  | none =>
    rw [Option.map_none, List.getElem?_eq_none_iff, CapRetag.logUpLength h]
    rw [List.getElem?_eq_none_iff] at hp
    exact hp
  | some m =>
    obtain ⟨m', hm', hpa, hd, ht, -⟩ := CapRetag.logUpLookup h p m hp
    rw [hm']
    simp only [Option.map_some, retagMsg, CapRetag.fOf, hm', Option.elim, Option.some.injEq]
    cases m'
    simp_all

theorem CapRetag.logUpPrefix {L L' M' : List Wmsg} (h : CapRetag.logUp L L') (hp : L' <+: M') :
    ∀ (q : Nat) (m' : Wmsg), L'[q]? = some m' → M'[q]? = some m' := by
  intro q m' hq
  obtain ⟨t, ht⟩ := hp
  rw [← ht]
  exact lookup_app_l_Some hq

/-! # 2. The primed twin of W4's record is an upgrade -/

/-- The release flag after a step, from the one before it: a store-like step clears it, a
`pw ∧ sw` fence sets it, everything else keeps it. -/
def CapRetag.relpAfter (l : Wlabel) (b : Bool) : Bool :=
  match l with
  | .LStore .. | .LRmw .. | .LExStore .. => false
  | .LFence _ pw _ sw => (pw && sw) || b
  | _ => b

theorem CapRetag.relpAfterMono (l : Wlabel) (b b' : Bool) (h : b = true → b' = true) :
    CapRetag.relpAfter l b = true → CapRetag.relpAfter l b' = true := by
  cases l <;> simp only [CapRetag.relpAfter] <;> try exact h
  · exact id
  · exact id
  · intro hh
    simp only [Bool.or_eq_true] at hh ⊢
    rcases hh with hh | hh
    · exact .inl hh
    · exact .inr (h hh)
  · exact id

/-- The message a step appends. -/
def CapRetag.appMsg (l : Wlabel) (i : Nat) (k : WmClass) : List Wmsg :=
  match l with
  | .LStore _ base data _ _ => [⟨base, data, some i, k⟩]
  | .LRmw _ _ base _ data _ _ => [⟨base, data, some i, k⟩]
  | .LExStore _ base data _ _ => [⟨base, data, some i, k⟩]
  | _ => []

theorem CapRetag.appMsgUp (l : Wlabel) (i : Nat) (k k' : WmClass) (h : CapRetag.clsUp k k') :
    CapRetag.logUp (CapRetag.appMsg l i k) (CapRetag.appMsg l i k') := by
  cases l <;> simp only [CapRetag.appMsg] <;>
    first | exact .nil | exact .cons ⟨rfl, rfl, rfl, h⟩ .nil

/-- The class function reads the release flag MONOTONICALLY. -/
def CapRetag.pclsMono {P : Type} (pcls : P → Wlabel → Wstate → WmClass) : Prop :=
  ∀ (p : P) (l : Wlabel) (ws ws' : Wstate), (ws.wRelp = true → ws'.wRelp = true) →
    CapRetag.clsUp (pcls p l ws) (pcls p l ws')

theorem CapRetag.wmClassOfUp (ak : AkInfo) (ws ws' : Wstate) (h : ws.wRelp = true → ws'.wRelp = true) :
    CapRetag.clsUp (wmClassOf ak ws) (wmClassOf ak ws') := by
  unfold wmClassOf
  cases hl : ak.akLatest
  · cases hs : ak.akSync <;> cases hr : ws.wRelp <;> cases hr' : ws'.wRelp <;>
      simp_all [CapRetag.clsUp]
  · exact .inl rfl

theorem CapRetag.pnodeWclassUp (m : SailM Unit) (ws ws' : Wstate)
    (h : ws.wRelp = true → ws'.wRelp = true) :
    CapRetag.clsUp (pnodeWclass m ws) (pnodeWclass m ws') := by
  rcases m with _ | ⟨e, K⟩
  · exact .inl rfl
  · rcases e with _ | o
    · exact .inl rfl
    · cases o <;> first | exact CapRetag.wmClassOfUp _ ws ws' h | exact .inl rfl

theorem CapRetag.pclsEvMono : CapRetag.pclsMono pclsEv := by
  intro p l ws ws' h
  cases l <;> simp only [pclsEv] <;> try exact .inl rfl
  · cases p with
    | PHart _ m _ _ _ => exact CapRetag.pnodeWclassUp m ws ws' h
    | PDisk _ => exact CapRetag.wmClassOfUp _ ws ws' h
  · cases p with
    | PHart _ m _ _ _ => exact CapRetag.pnodeWclassUp m ws ws' h
    | PDisk _ => exact CapRetag.wmClassOfUp _ ws ws' h

section shapes

variable {P D : Type}
variable (pstep : P → D → Wlabel → P → D → Prop)
variable (pcls : P → Wlabel → Wstate → WmClass)
variable (pwb : P → Bool)

/-- **The registered step's shape**: agent `i`'s new release flag is `relpAfter` of the old one, and
the step appends `appMsg` at the registered class. -/
theorem CapRetag.regShape (i : Nat) (l : Wlabel) (c c1 : Wpcfg P D) :
    wpPfStep pstep pcls i l c c1 →
    ∃ (ag : Wpagent P) (st' : P) (w : Wstate),
      c.pcAgs[i]? = some ag ∧ c1.pcAgs = c.pcAgs.set i ⟨st', w, ag.paProm⟩ ∧
      (w.wRelp = true → CapRetag.relpAfter l ag.paWs.wRelp = true) ∧
      c1.pcLog = c.pcLog ++ CapRetag.appMsg l i (pcls ag.paSt l ag.paWs) := by
  intro h
  cases h with
  | PFSilent _ ag st' d' hlk _ =>
    exact ⟨ag, st', _, hlk, rfl, id, by simp [CapRetag.appMsg]⟩
  | PFLoad _ ag aq lat base tvs asrc st' d' hlk _ _ =>
    refine ⟨ag, st', _, hlk, rfl, ?_, by simp [CapRetag.appMsg]⟩
    rw [loadPostRunDRelp]; exact id
  | PFStore _ ag rl base data asrc vsrc k st' d' hlk _ hnn hk =>
    refine ⟨ag, st', _, hlk, rfl, ?_, by simp [CapRetag.appMsg, hk]⟩
    rw [storePostRunDRelp _ _ _ _ _ _ _ (List.length_pos_iff.2 hnn)]
    intro hh; cases hh
  | PFRmw _ ag aq rl base tvs data asrc vsrc k st' d' hlk _ hnn _ _ _ hk =>
    refine ⟨ag, st', _, hlk, rfl, ?_, by simp [CapRetag.appMsg, hk]⟩
    rw [storePostRunDRelp _ _ _ _ _ _ _ (List.length_pos_iff.2 hnn)]
    intro hh; cases hh
  | PFFence _ ag pr pw sr sw st' d' hlk _ =>
    refine ⟨ag, st', _, hlk, rfl, ?_, by simp [CapRetag.appMsg]⟩
    simp only [fencePost, CapRetag.relpAfter]
    cases pw <;> cases sw <;> simp
  | PFDev _ ag st' d' hlk _ =>
    exact ⟨ag, st', _, hlk, rfl, id, by simp [CapRetag.appMsg]⟩
  | PFRegW _ ag rd srcs st' d' hlk _ =>
    exact ⟨ag, st', _, hlk, rfl, id, by simp [CapRetag.appMsg]⟩
  | PFCtrl _ ag srcs st' d' hlk _ =>
    exact ⟨ag, st', _, hlk, rfl, id, by simp [CapRetag.appMsg]⟩
  | PFInstr _ ag st' d' hlk _ =>
    exact ⟨ag, st', _, hlk, rfl, id, by simp [CapRetag.appMsg]⟩
  | PFExLoad _ ag aq base tvs asrc st' d' hlk _ _ =>
    refine ⟨ag, st', _, hlk, rfl, ?_, by simp [CapRetag.appMsg]⟩
    rw [exloadPostRunDRelp]; exact id
  | PFExStore _ ag rl base data asrc vsrc k R st' d' hlk _ hnn _ _ _ _ hk =>
    refine ⟨ag, st', _, hlk, rfl, ?_, by simp [CapRetag.appMsg, hk]⟩
    rw [storePostRunDRelp _ _ _ _ _ _ _ (List.length_pos_iff.2 hnn)]
    intro hh; cases hh
  | PFIFetch _ ag base tvs st' d' hlk _ _ =>
    exact ⟨ag, st', _, hlk, rfl, id, by simp [CapRetag.appMsg]⟩

/-- **The primed step's shape**: agent `i`'s new release flag is AT LEAST `relpAfter` of the old one
(the walker's write-back keeps it), and the step appends `appMsg` at the primed class. -/
theorem CapRetag.primShape (i : Nat) (l : Wlabel) (c c1 : Wpcfg P D) :
    WbPrimed.wpPfStepW pstep pcls pwb i l c c1 →
    ∃ (ag : Wpagent P) (st' : P) (w : Wstate),
      c.pcAgs[i]? = some ag ∧ c1.pcAgs = c.pcAgs.set i ⟨st', w, ag.paProm⟩ ∧
      (CapRetag.relpAfter l ag.paWs.wRelp = true → w.wRelp = true) ∧
      c1.pcLog = c.pcLog ++ CapRetag.appMsg l i (pcls ag.paSt l ag.paWs) := by
  intro h
  cases h with
  | PFSilent _ ag st' d' hlk _ =>
    exact ⟨ag, st', _, hlk, rfl, id, by simp [CapRetag.appMsg]⟩
  | PFLoad _ ag aq lat base tvs asrc st' d' hlk _ _ =>
    refine ⟨ag, st', _, hlk, rfl, ?_, by simp [CapRetag.appMsg]⟩
    rw [loadPostRunDRelp]; exact id
  | PFStore _ ag rl base data asrc vsrc k st' d' hlk _ hnn hk =>
    exact ⟨ag, st', _, hlk, rfl, (fun hh => by simp [CapRetag.relpAfter] at hh),
      by simp [CapRetag.appMsg, hk]⟩
  | PFRmw _ ag aq rl base tvs data asrc vsrc k st' d' hlk _ hnn _ _ _ hk =>
    exact ⟨ag, st', _, hlk, rfl, (fun hh => by simp [CapRetag.relpAfter] at hh),
      by simp [CapRetag.appMsg, hk]⟩
  | PFFence _ ag pr pw sr sw st' d' hlk _ =>
    refine ⟨ag, st', _, hlk, rfl, ?_, by simp [CapRetag.appMsg]⟩
    simp only [fencePost, CapRetag.relpAfter]
    cases pw <;> cases sw <;> simp
  | PFDev _ ag st' d' hlk _ =>
    exact ⟨ag, st', _, hlk, rfl, id, by simp [CapRetag.appMsg]⟩
  | PFRegW _ ag rd srcs st' d' hlk _ =>
    exact ⟨ag, st', _, hlk, rfl, id, by simp [CapRetag.appMsg]⟩
  | PFCtrl _ ag srcs st' d' hlk _ =>
    exact ⟨ag, st', _, hlk, rfl, id, by simp [CapRetag.appMsg]⟩
  | PFInstr _ ag st' d' hlk _ =>
    exact ⟨ag, st', _, hlk, rfl, id, by simp [CapRetag.appMsg]⟩
  | PFExLoad _ ag aq base tvs asrc st' d' hlk _ _ =>
    refine ⟨ag, st', _, hlk, rfl, ?_, by simp [CapRetag.appMsg]⟩
    rw [exloadPostRunDRelp]; exact id
  | PFExStore _ ag rl base data asrc vsrc k R st' d' hlk _ hnn _ _ _ _ hk =>
    exact ⟨ag, st', _, hlk, rfl, (fun hh => by simp [CapRetag.relpAfter] at hh),
      by simp [CapRetag.appMsg, hk]⟩
  | PFIFetch _ ag base tvs st' d' hlk _ _ =>
    exact ⟨ag, st', _, hlk, rfl, id, by simp [CapRetag.appMsg]⟩

end shapes

/-- Every registered release flag is set on the primed side too. -/
def CapRetag.relpLe {P D : Type} (c c' : Wpcfg P D) : Prop :=
  ∀ (i : Nat) (ag ag' : Wpagent P), c.pcAgs[i]? = some ag → c'.pcAgs[i]? = some ag' →
    ag.paWs.wRelp = true → ag'.paWs.wRelp = true

theorem CapRetag.relpLeRefl {P D : Type} (c : Wpcfg P D) : CapRetag.relpLe c c := by
  intro i ag ag' h h'
  rw [h, Option.some.injEq] at h'
  subst h'
  exact id

/-- **ONE STEP of the two machines at the same label keeps the upgrade.** -/
theorem CapRetag.stepUp {P D : Type} (pstep : P → D → Wlabel → P → D → Prop)
    (pcls : P → Wlabel → Wstate → WmClass) (pwb : P → Bool) (hm : CapRetag.pclsMono pcls)
    (i : Nat) (l : Wlabel) (c c1 c' c1' : Wpcfg P D) :
    wpPfStep pstep pcls i l c c1 → WbPrimed.wpPfStepW pstep pcls pwb i l c' c1' →
    WbPrimed.cfgRel c c' → CapRetag.relpLe c c' → CapRetag.logUp c.pcLog c'.pcLog →
    CapRetag.relpLe c1 c1' ∧ CapRetag.logUp c1.pcLog c1'.pcLog := by
  intro hs hs' hR hle hup
  obtain ⟨ag, st, w, hlk, hags, hw, hlog⟩ := CapRetag.regShape pstep pcls i l c c1 hs
  obtain ⟨ag', st', w', hlk', hags', hw', hlog'⟩ :=
    CapRetag.primShape pstep pcls pwb i l c' c1' hs'
  obtain ⟨ag'', hlk'', hst, -, -⟩ := hR.2.2.2.2 i ag hlk
  rw [hlk', Option.some.injEq] at hlk''
  subst hlk''
  have hrelp : ag.paWs.wRelp = true → ag'.paWs.wRelp = true := hle i ag ag' hlk hlk'
  refine ⟨?_, ?_⟩
  · intro j a a' hj hj'
    rw [hags] at hj
    rw [hags'] at hj'
    rcases lookupSetCases hj with ⟨rfl, rfl⟩ | ⟨hne, hj⟩
    · rcases lookupSetCases hj' with ⟨-, rfl⟩ | ⟨hne', -⟩
      · exact fun h => hw' (CapRetag.relpAfterMono l _ _ hrelp (hw h))
      · exact absurd rfl hne'
    · rcases lookupSetCases hj' with ⟨heq, -⟩ | ⟨-, hj'⟩
      · exact absurd heq hne
      · exact hle j a a' hj hj'
  · rw [hlog, hlog', hst]
    exact CapRetag.logUpApp hup (CapRetag.appMsgUp l i _ _ (hm _ l _ _ hrelp))

/-- A record entry and its primed twin, with the upgrade. -/
def CapRetag.recRelUp (x y : PfRec) : Prop :=
  WbPrimed.recRel x y ∧ CapRetag.relpLe x.pre y.pre ∧ CapRetag.logUp x.pre.pcLog y.pre.pcLog

theorem CapRetag.recRelOfUp {r r' : List PfRec} (h : List.Forall₂ CapRetag.recRelUp r r') :
    List.Forall₂ WbPrimed.recRel r r' :=
  List.Forall₂.imp (fun hxy => hxy.1) h

/-- **THE PRIMED RECORD IS AN UPGRADE** (`WbPrimed.chainOfContR` with the release flag order and the
upgrade-only log relation carried along). -/
theorem CapRetag.chainOfContRUp {fok : Image → List Wmsg → Nat → Int → List (Nat × BitVec 8) → Prop}
    {fcutT : Nat → Image → List Wmsg → Nat → Int → List (Nat × BitVec 8) → Prop}
    {c : Wpcfg Pexv6 Efab} {st : List (Nat × Wlabel)} {r : List PfRec} {cN : Wpcfg Pexv6 Efab}
    (h : contRC fok fcutT c st r cN) :
    ∀ c', WbPrimed.cfgRel c c' → CapRetag.relpLe c c' → CapRetag.logUp c.pcLog c'.pcLog →
      ∃ (r' : List PfRec) (cN' : Wpcfg Pexv6 Efab),
        WbPrimed.chainW c' r' cN' ∧ WbPrimed.cfgRel cN cN' ∧ CapRetag.relpLe cN cN' ∧
        CapRetag.logUp cN.pcLog cN'.pcLog ∧ List.Forall₂ CapRetag.recRelUp r r' := by
  induction h with
  | nil c st => intro c' hR hle hup; exact ⟨[], c', .nil c', hR, hle, hup, .nil⟩
  | cons c c1 st i l k r cN hs _ _ _ _ _ ih =>
    intro c' hR hle hup
    obtain ⟨c1', hs', hR1⟩ := WbPrimed.stepFwd pstepEv pclsEv WbPrimed.pwbEv i l c c1 c' hs hR
    obtain ⟨hle1, hup1⟩ := CapRetag.stepUp pstepEv pclsEv WbPrimed.pwbEv CapRetag.pclsEvMono
      i l c c1 c' c1' hs hs' hR hle hup
    obtain ⟨r', cN', hc, hRN, hleN, hupN, hF⟩ := ih c1' hR1 hle1 hup1
    exact ⟨⟨c', i, l, k⟩ :: r', cN', .cons c' c1' i l k r' cN' hs' hc, hRN, hleN, hupN,
      .cons ⟨⟨rfl, rfl, rfl, hR⟩, hle, hup⟩ hF⟩

/-! # 3. One primed log for the whole run -/

/-- A primed record, cut at one of its entries. -/
theorem CapRetag.chainTake {c : Wpcfg Pexv6 Efab} {r : List PfRec} {cN : Wpcfg Pexv6 Efab}
    (h : WbPrimed.chainW c r cN) :
    ∀ (n : Nat) (y : PfRec), r[n]? = some y →
      WbPrimed.chainW c (r.take n) y.pre ∧ y.pre.pcLog <+: cN.pcLog := by
  induction h with
  | nil => intro n y hy; simp at hy
  | cons c c' i l k r cN hs hr ih =>
    intro n y hy
    cases n with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hy
      subst hy
      exact ⟨.nil c, WbPrimed.chainPrefix (.cons c c' i l k r cN hs hr)⟩
    | succ n =>
      simp only [List.getElem?_cons_succ] at hy
      obtain ⟨h1, h2⟩ := ih n y hy
      exact ⟨by simpa only [List.take_succ_cons] using .cons c c' i l k _ _ hs h1, h2⟩

/-- (a3) for a prefix of the record. -/
theorem CapRetag.relArmedTake (r : List PfRec) (n : Nat) :
    WbPrimed.relArmed r → WbPrimed.relArmed (r.take n) := by
  intro ha n' x hx hst ag hag hpc
  rw [List.getElem?_take] at hx
  by_cases hlt : n' < n
  · rw [if_pos hlt] at hx
    rw [List.take_take, Nat.min_eq_left (Nat.le_of_lt hlt)]
    exact ha n' x hx hst ag hag hpc
  · rw [if_neg hlt] at hx; cases hx

/-- The release-site fact of the primed log at a record point, from the export, (a2) and (a3) at
the prefix. -/
theorem CapRetag.relSiteAt {c : Wpcfg Pexv6 Efab} {r r' : List PfRec} {cN' : Wpcfg Pexv6 Efab}
    (hc : WbPrimed.chainW c r' cN') (h0 : c.pcLog = [])
    (hF : List.Forall₂ WbPrimed.recRel r r') (n : Nat) (y : PfRec) (hy : r'[n]? = some y)
    (σ : MState) (hD : Xv6.AccessDiscipline.xv6AccessDisc σ)
    (ha2 : CapRelSite.pcLogAgree (r.take n) σ) (ha3 : WbPrimed.relArmed r) :
    relSiteWCrel σ y.pre.pcLog := by
  have hFn := WbPrimed.forall₂Take hF n
  obtain ⟨hcn, -⟩ := CapRetag.chainTake hc n y hy
  exact WbPrimed.relSiteWCrelPrimed σ (r.take n) (r'.take n) c y.pre hcn h0 hFn
    (CapRelSite.provAtRec (r.take n) σ hD ha2)
    (WbPrimed.relStepWCrelOfArmed hcn
      (WbPrimed.relArmedRel hFn (CapRetag.relArmedTake r n ha3)))

/-- **THE PRIMED TWIN OF THE WHOLE RUN** (one primed log `cN′.pcLog` for every realized read): the
primed record ends at `cN′`, an upgrade of the registered end; at every record point `n` the
primed pre-configuration `y.pre` is related to the registered `x.pre` (with the upgrade), its log
is a PREFIX of `cN′.pcLog`, and it carries `relSiteWCrel σ` given the export, (a2) at the prefix
and (a3); likewise at the end. -/
theorem CapRetag.readAtTwin {fok : Image → List Wmsg → Nat → Int → List (Nat × BitVec 8) → Prop}
    {fcutT : Nat → Image → List Wmsg → Nat → Int → List (Nat × BitVec 8) → Prop}
    {c : Wpcfg Pexv6 Efab} {st0 : List (Nat × Wlabel)} {r : List PfRec} {cN : Wpcfg Pexv6 Efab}
    (h : contRC fok fcutT c st0 r cN) (h0 : c.pcLog = []) :
    ∃ (r' : List PfRec) (cN' : Wpcfg Pexv6 Efab),
      WbPrimed.chainW c r' cN' ∧ WbPrimed.cfgRel cN cN' ∧ CapRetag.logUp cN.pcLog cN'.pcLog ∧
      List.Forall₂ CapRetag.recRelUp r r' ∧
      (∀ (n : Nat) (x y : PfRec), r[n]? = some x → r'[n]? = some y →
        WbPrimed.cfgRel x.pre y.pre ∧ CapRetag.logUp x.pre.pcLog y.pre.pcLog ∧
        y.pre.pcLog <+: cN'.pcLog ∧
        ∀ σ : MState, Xv6.AccessDiscipline.xv6AccessDisc σ → CapRelSite.pcLogAgree (r.take n) σ →
          WbPrimed.relArmed r → relSiteWCrel σ y.pre.pcLog) ∧
      (∀ σ : MState, Xv6.AccessDiscipline.xv6AccessDisc σ → CapRelSite.pcLogAgree r σ →
          WbPrimed.relArmed r → relSiteWCrel σ cN'.pcLog) := by
  obtain ⟨r', cN', hc, hRN, -, hupN, hF⟩ :=
    CapRetag.chainOfContRUp h c (WbPrimed.cfgRelRefl c) (CapRetag.relpLeRefl c)
      (CapRetag.logUpRefl _)
  have hF' := CapRetag.recRelOfUp hF
  refine ⟨r', cN', hc, hRN, hupN, hF, ?_, ?_⟩
  · intro n x y hx hy
    obtain ⟨x', hx', hxy⟩ := WbPrimed.forall₂Lookup hF n y hy
    rw [hx, Option.some.injEq] at hx'
    subst hx'
    exact ⟨hxy.1.2.2.2, hxy.2.2, (CapRetag.chainTake hc n y hy).2,
      fun σ hD ha2 ha3 => CapRetag.relSiteAt hc h0 hF' n y hy σ hD ha2 ha3⟩
  · intro σ hD ha2 ha3
    exact WbPrimed.relSiteWCrelPrimed σ r r' c cN' hc h0 hF' (CapRelSite.provAtRec r σ hD ha2)
      (WbPrimed.relStepWCrelOfArmed hc (WbPrimed.relArmedRel hF' ha3))

/-- **W11-C's realized read over the ONE primed log** `L′`: at a primed configuration `cf′` related
to a realized registered one `cf` (upgrade), carrying the release-site fact, whose log is a prefix
of `L′`, every registered read of message `m` is a `readAt L′` of an upgrade `m′` of it. -/
theorem CapRetag.readAtUp (L' : List Wmsg) (cf cf' : Wpcfg Pexv6 Efab) (st : List (Nat × Wlabel))
    (σ : MState) (j : CPU) (pa : PAddr) (p : Nat) (m : Wmsg)
    (hR : rmem cf st σ) (hrel : WbPrimed.cfgRel cf cf') (hup : CapRetag.logUp cf.pcLog cf'.pcLog)
    (hD : Xv6.AccessDiscipline.xv6AccessDisc σ) (hsite : relSiteWCrel σ cf'.pcLog)
    (hpre : cf'.pcLog <+: L') (hp : cf.pcLog[p]? = some m) (hv : (msgByte m (paZ pa)).isSome)
    (hram : inRam pa 1) (hcoh : (σ.hr j).coh pa = p + 1) :
    ∃ m', cf'.pcLog[p]? = some m' ∧ CapRetag.msgUp m m' ∧ readAt L' cf' st σ j pa p m' := by
  obtain ⟨m', hp', -, -, -, hrd⟩ :=
    WbPrimed.readAtPrimed L' cf cf' st σ j pa p m hR hrel hD hsite hpre hp hv hram hcoh
  obtain ⟨m'', hp'', hup'⟩ := CapRetag.logUpLookup hup p m hp
  rw [hp', Option.some.injEq] at hp''
  subst hp''
  exact ⟨m', hp', hup', hrd⟩

/-! # 4. The consumers -/

/-! ## 4.1 W11-D's derivation: a PRIMED realized read, a REGISTERED graph -/

/-- `RvwmoXv6Adequacy.entGraph` with the read's configuration under the PRIMED log `L′` and the graph's
log the REGISTERED `L` (`logUp L L′`). -/
theorem CapRetag.entGraphUp {c : Wpcfg Pexv6 Efab} {st : List (Nat × Wlabel)} {σ : MState}
    {L L' : List Wmsg} {G : Gexec} {b : PAddr} {H : Hist} {e : HEnt}
    (hR : rmem c st σ) (hpre : c.pcLog <+: L') (hwf : gwf G) (hlog : logOf G L)
    (hup : CapRetag.logUp L L') (hb : σ.mem[b]? = some H) (he : e ∈ H) (ht : e.t ≠ 0) :
    ∃ W, W ∈ gwrites G ∧ gwix G W = e.t ∧ W.1 = e.tid ∧ e.t ≤ c.pcLog.length := by
  have hr := hR.2.2.1
  rw [RvwmoXv6Adequacy.rhistGet hr hb] at he
  rcases RvwmoXv6Adequacy.histOfMemInv _ _ _ _ he with h0 | ⟨mq, hq, -, htq⟩
  · exact absurd h0 ht
  · have hlen := (List.getElem?_eq_some_iff.1 hq).1
    have hq' : L'[e.t - 1]? = some mq := by
      obtain ⟨rest, hrest⟩ := hpre
      rw [← hrest]; exact lookup_app_l_Some hq
    obtain ⟨m0, hm0, -, -, ht0, -⟩ := CapRetag.logUpLookupInv hup _ _ hq'
    obtain ⟨W, -, hm, hix, hmem⟩ := logOfLookup G L (e.t - 1) m0 hwf hlog hm0
    refine ⟨W, hmem, by rw [hix]; omega, ?_, by omega⟩
    rw [htq, ht0, gmsgTid G W m0 hm]
    rfl

/-- **THE DERIVATION AT THE RE-TAG** (`chainHypsOfSyncPath` with the realized read over the PRIMED log
`L′` and the graph's log the REGISTERED `L`): the sync arm reads no class, so the primed read and
the registered graph meet here. -/
theorem CapRetag.chainHypsOfSyncPathUp (GD : Gdexec) (L L' : List Wmsg) (c : Wpcfg Pexv6 Efab)
    (st : List (Nat × Wlabel)) (σ : MState) (j : CPU) (pa : PAddr) (p : Nat) (m : Wmsg)
    (i : Nat) (prev : Geid) (s : Seg)
    (hrd : readAt L' c st σ j pa p m) (hi : m.wmTid = some i) (hiN : i < NCPU)
    (hij : i ≠ hartAgent j) (hnb : ¬ benignAt σ pa (p + 1))
    (hwf : gwf GD.gdG) (hlog : logOf GD.gdG L) (hup : CapRetag.logUp L L')
    (hprev : gwriteAt GD.gdG (p + 1) = some prev)
    (hrun : s.sgEntry = s.sgExit ∨ WeakRvwmoGraph.gpo GD.gdG s.sgEntry s.sgExit)
    (hmx : gmem GD.gdG s.sgExit) (hre : syncRealized GD σ j s) :
    chainHyps GD prev s := by
  obtain ⟨hR, hD, -, hpre, hp, hv, hram, hcoh⟩ := hrd
  have hr := hR.2.2.1
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hv
  obtain ⟨hpw, hpix⟩ := gwriteAtInv GD.gdG (p + 1) prev hwf.1 hprev
  have hH := hr.1 pa hram
  have he : (⟨p + 1, i, v⟩ : HEnt) ∈ TsoOfPf.histOf c.pcImg c.pcLog (paZ pa) := by
    have := RvwmoXv6Adequacy.histOfMem c.pcImg c.pcLog (paZ pa) p m v hp hv
    rwa [hi] at this
  have h1 : ∀ b, Xv6.AccessDiscipline.custAt σ pa (p + 1) ≠ .lockw b :=
    fun b hb' => hnb (.inl ⟨b, hb'⟩)
  have h2 : ∀ w, Xv6.AccessDiscipline.custAt σ pa (p + 1) ≠ .pub w :=
    fun w hw => hnb (.inr (.inl ⟨w, hw⟩))
  have h3 : Xv6.AccessDiscipline.custAt σ pa (p + 1) ≠ .pte := fun h => hnb (.inr (.inr (.inl h)))
  rcases hD.1 j pa _ ⟨p + 1, i, v⟩ hH he (by simp) hcoh.symm hiN hij h1 h2 h3 with hs | hrc
  · rcases hs with ⟨a, ha, hc⟩ | ⟨f, w, r, v', H', hne, hpub, hf, hew, hrle, harm⟩
    · obtain ⟨⟨_, _, _, _, _, _, ht1, h1a⟩, b, C, r, hbl, hsh⟩ :=
        RvwmoXv6Adequacy.hopChainSpan hr hc
      simp only at ht1
      obtain ⟨Hb, va, hHb, hmemA⟩ := RvwmoXv6Adequacy.syncHopAcq hsh
      obtain ⟨W, hW, hix, hW1, -⟩ :=
        CapRetag.entGraphUp hR hpre hwf hlog hup hHb hmemA (by simp only; omega)
      simp only at hix hW1
      obtain ⟨hWR, hWaq, hWe⟩ := hre.1 W b C r hW hW1 (by rw [hix]; omega)
        (by rw [hix]; exact hbl) (by rw [hix]; exact hsh)
      refine ⟨W, W, hpw, hW, by rw [hix, hpix]; omega, .inl rfl, .inl ⟨hWR, hWaq, ?_⟩⟩
      rcases CatLin.CatReroute.poOrEq GD.gdG _ _ _ hWe hrun with heq | hpo
      · exact .inl heq
      · exact .inr ⟨hpo, hmx⟩
    · have hlt : p + 1 < r := by
        rcases harm with ⟨-, h⟩ | ⟨a, ha, hc⟩
        · exact h
        · obtain ⟨⟨_, _, _, _, _, _, ht1, h1a⟩, -⟩ :=
            RvwmoXv6Adequacy.hopChainSpan (m := σ.mem) hr hc
          simp only at ht1
          omega
      obtain ⟨W, Y, hW, hrW, hWY, hfc⟩ := hre.2 f w r v' H' hne hpub hf hew hrle
      exact ⟨W, Y, hpw, hW, by rw [hpix]; omega, hWY, .inr hfc⟩
  · exact absurd (.inr (.inr (.inr hrc))) hnb

/-! ## 4.2 The log facts: class-blind, upward or downward -/

section logs

variable {L L' : List Wmsg}

theorem CapRetag.logByteUp (h : CapRetag.logUp L L') (img : Image) (t : Nat) (a : Int) :
    logByte img L' t a = logByte img L t a := by
  rw [CapRetag.logUpRetag h, retagLogByte]

theorem CapRetag.latestUp (h : CapRetag.logUp L L') (img : Image) (a : Int) (t : Nat) :
    latest img L' a t ↔ latest img L a t := by
  rw [CapRetag.logUpRetag h, retagLatest]

theorem CapRetag.mwritesUp {m m' : Wmsg} (h : CapRetag.msgUp m m') (a : Int) :
    mwrites a m' = mwrites a m := by
  unfold mwrites; rw [CapRetag.msgUpByte h]

theorem CapRetag.altStepUp {m m' : Wmsg} (h : CapRetag.msgUp m m') (hh : Option Nat) :
    altStep hh m' = altStep hh m := by
  obtain ⟨hp, hd, ht, hk⟩ := h
  rcases hk with hk | ⟨hk1, hk2⟩
  · have e : m' = m := by
      cases m; cases m'; simp_all
    rw [e]
  · simp [altStep, hd, ht, hk1, hk2]

/-- **The alternation fold reads no upgraded class** (`.WCexcl` never moves). -/
theorem CapRetag.altFoldUp (a : Int) {ms ms' : List Wmsg} (h : CapRetag.logUp ms ms') :
    ∀ hh, altFold a hh ms' = altFold a hh ms := by
  induction h with
  | nil => intro hh; rfl
  | cons hxy _ ih =>
    intro hh
    simp only [altFold, CapRetag.mwritesUp hxy, CapRetag.altStepUp hxy, ih]

theorem CapRetag.wlpHolderAtUp (h : CapRetag.logUp L L') (a : Int) (n0 p : Nat) :
    wlpHolderAt L' a n0 p = wlpHolderAt L a n0 p := by
  unfold wlpHolderAt
  exact CapRetag.altFoldUp a (CapRetag.logUpDrop (CapRetag.logUpTake h p) n0) none

theorem CapRetag.wlpAltUp (h : CapRetag.logUp L L') (a : Int) (n0 : Nat) (hh : Option Nat) :
    wlpAlt L' a n0 hh ↔ wlpAlt L a n0 hh := by
  unfold wlpAlt
  rw [CapRetag.logUpLength h, CapRetag.wlpHolderAtUp h]

theorem CapRetag.regZeroAtUp (h : CapRetag.logUp L L') (img : Image) (b : Int) (n0 : Nat) :
    CertZ18.regZeroAt img L' b n0 ↔ CertZ18.regZeroAt img L b n0 := by
  have h' := CapRetag.logUpTake h n0
  unfold CertZ18.regZeroAt
  constructor
  · intro H t ht
    rw [← CapRetag.logByteUp h']
    exact H t ((CapRetag.latestUp h' img b t).2 ht)
  · intro H t ht
    rw [CapRetag.logByteUp h']
    exact H t ((CapRetag.latestUp h' img b t).1 ht)

theorem CapRetag.rmwLatestUp (h : CapRetag.logUp L L') (GR : Gexec) :
    CertZ18.rmwLatest GR L' ↔ CertZ18.rmwLatest GR L := by
  unfold CertZ18.rmwLatest
  constructor
  · intro H e a t v hW hr
    have h' := CapRetag.logUpTake h (gwix GR e - 1)
    obtain ⟨h1, h2⟩ := H e a t v hW hr
    exact ⟨(CapRetag.latestUp h' _ a t).1 h1, by rw [← CapRetag.logByteUp h']; exact h2⟩
  · intro H e a t v hW hr
    have h' := CapRetag.logUpTake h (gwix GR e - 1)
    obtain ⟨h1, h2⟩ := H e a t v hW hr
    exact ⟨(CapRetag.latestUp h' _ a t).2 h1, by rw [CapRetag.logByteUp h']; exact h2⟩

/-- The lock shape survives the upgrade (a non-plain class does not move). -/
theorem CapRetag.wlpAtUp (h : CapRetag.logUp L L') (a base : Int) (n0 : Nat) :
    wlpAt L a base n0 → wlpAt L' a base n0 := by
  rintro ⟨hab, H⟩
  refine ⟨hab, fun p m' hp hn hs => ?_⟩
  obtain ⟨m, hm, hup⟩ := CapRetag.logUpLookupInv h p m' hp
  obtain ⟨hb, hl, hnp, hx⟩ := H p m hm hn (by rw [← CapRetag.msgUpByte hup]; exact hs)
  obtain ⟨hpa, hd, -, hk⟩ := hup
  have hk' := CapRetag.clsUpNonplain hk hnp
  exact ⟨by rw [hpa, hb], by rw [hd]; exact hl, by rw [hk']; exact hnp,
    by rw [hk', hd]; exact hx⟩

/-- The protection clause survives the upgrade (a primed-plain message is registered-plain). -/
theorem CapRetag.wprotAtUp (h : CapRetag.logUp L L') (a base : Int) (n0 r0 : Nat) :
    wprotAt L a base n0 r0 → wprotAt L' a base n0 r0 := by
  rintro ⟨hle, H⟩
  refine ⟨hle, fun p m' hp hr hs hpl => ?_⟩
  obtain ⟨m, hm, hup⟩ := CapRetag.logUpLookupInv h p m' hp
  rw [CapRetag.wlpHolderAtUp h, hup.2.2.1]
  exact H p m hm hr (by rw [← CapRetag.msgUpByte hup]; exact hs)
    (CapRetag.clsUpPlain hup.2.2.2 hpl)

theorem CapRetag.protRegUp (h : CapRetag.logUp L L') (P : Int → Int → Prop) :
    protReg P L → protReg P L' := by
  intro H a base hP
  obtain ⟨n0, r0, hh, h1, h2, h3⟩ := H a base hP
  exact ⟨n0, r0, hh, CapRetag.wprotAtUp h a base n0 r0 h1, CapRetag.wlpAtUp h base base n0 h2,
    (CapRetag.wlpAltUp h base n0 hh).2 h3⟩

theorem CapRetag.protRegZUp (h : CapRetag.logUp L L') (P : Int → Int → Prop) (img : Image) :
    CertZ18.protRegZ P img L → CertZ18.protRegZ P img L' := by
  intro H a base hP
  obtain ⟨n0, r0, hh, h1, h2, h3, h4⟩ := H a base hP
  exact ⟨n0, r0, hh, CapRetag.wprotAtUp h a base n0 r0 h1, CapRetag.wlpAtUp h base base n0 h2,
    (CapRetag.wlpAltUp h base n0 hh).2 h3, (CapRetag.regZeroAtUp h img base n0).2 h4⟩

theorem CapRetag.inWinUp (h : CapRetag.logUp L L') (GR : Gexec) (n0 : Nat) (e : Geid) :
    CatLin.GraphFetchN2.inWin GR L' n0 e ↔ CatLin.GraphFetchN2.inWin GR L n0 e := by
  unfold CatLin.GraphFetchN2.inWin
  rw [CapRetag.logUpLength h]

/-- **`acqAq` over the primed re-tag gives the registered one.** -/
theorem CapRetag.acqAqLogDown (h : CapRetag.logUp L L') (G GR : Gexec) (P : Int → Int → Prop) :
    CatLin.acqAqLog G GR L' P → CatLin.acqAqLog G GR L P := by
  intro H a b n0 r0 hh hP h1 h2 h3 A hA hw
  exact H a b n0 r0 hh hP (CapRetag.wprotAtUp h a b n0 r0 h1) (CapRetag.wlpAtUp h b b n0 h2)
    ((CapRetag.wlpAltUp h b n0 hh).2 h3) A hA ((CapRetag.inWinUp h GR n0 A).2 hw)

/-- **`relCovers` over the primed re-tag gives the registered one.** -/
theorem CapRetag.relCoversLogDown (h : CapRetag.logUp L L') (G GR : Gexec) (P : Int → Int → Prop) :
    CatLin.relCoversLog G GR L' P → CatLin.relCoversLog G GR L P := by
  intro H a b n0 r0 hh hP h1 h2 h3 A R x hA hR hwA hwR
  exact H a b n0 r0 hh hP (CapRetag.wprotAtUp h a b n0 r0 h1) (CapRetag.wlpAtUp h b b n0 h2)
    ((CapRetag.wlpAltUp h b n0 hh).2 h3) A R x hA hR ((CapRetag.inWinUp h GR n0 A).2 hwA)
    ((CapRetag.inWinUp h GR n0 R).2 hwR)

/-- Publication survives the upgrade (a release message stays one). -/
theorem CapRetag.wpublishedUp (h : CapRetag.logUp L L') (tid : Option Nat) (p : Nat) :
    wpublished L tid p → wpublished L' tid p := by
  rintro ⟨q, mq, hle, hq, ht, hk⟩
  obtain ⟨mq', hq', hup⟩ := CapRetag.logUpLookup h q mq hq
  exact ⟨q, mq', hle, hq', by rw [hup.2.2.1, ht], CapRetag.clsUpRel hup.2.2.2 hk⟩

/-- **The primed bad arm is the registered one restricted** (so classifying at the re-tag is the
STRONGER claim). -/
theorem CapRetag.badSegDown (h : CapRetag.logUp L L') (GD : Gdexec) (prev : Geid) (s : Seg) :
    badSeg GD L' prev s → badSeg GD L prev s := by
  rintro ⟨p, m', i, a, v, hrd, hw, hp, hi, hiN, hs, hne, hcl, hnp⟩
  obtain ⟨m, hm, hup⟩ := CapRetag.logUpLookupInv h p m' hp
  exact ⟨p, m, i, a, v, hrd, hw, hm, by rw [← hup.2.2.1]; exact hi, hiN, hs, hne,
    CapRetag.clsUpPlain hup.2.2.2 hcl,
    fun hpub => hnp (by rw [hup.2.2.1]; exact CapRetag.wpublishedUp h m.wmTid p hpub)⟩

end logs

/-! ## 4.3 THE CLAIM over the re-tag and its kill -/

/-- **THE L2′ CLAIM WITH THE BAD ARM AT THE PRIMED RE-TAG** (`l2ClaimAtCD`'s text; `L` is the
graph's registered log, `L′` any upgrade of it — at the realized run the primed twin's log,
`CapRetag.readAtTwin` — and only the bad arm reads `L′`). -/
def CapRetag.l2ClaimAtCDUp (GD : Gdexec) (ad : List (Geid × Geid)) (P : Int → Int → Prop) : Prop :=
  ∀ (L L' : List Wmsg) (z : Geid) (ss : List Seg),
    CatLin.rvwmoCatAD GD ad →
    logOf GD.gdG L → CapRetag.logUp L L' →
    protReg P L →
    ss ≠ [] → CatLin.rawChainC GD (CatLin.gcrossE GD.gdG) z z ss →
    ∀ (prev : Geid) (s : Seg),
      s ∈ ss → CatLin.gcrossE GD.gdG prev s.sgEntry → CatLin.segRunC GD s →
      CatLin.segPinC GD ad s ∨ csHyps GD P L prev s ∨ chainHyps GD prev s ∨
        badSeg GD L' prev s

/-- The re-tagged claim is the stronger one: it gives `l2ClaimAtCD`. -/
theorem CapRetag.l2ClaimAtCDOfUp (GD : Gdexec) (ad : List (Geid × Geid)) (P : Int → Int → Prop) :
    CapRetag.l2ClaimAtCDUp GD ad P → l2ClaimAtCD GD ad P :=
  fun h log z ss hc hlog hpr hne hch =>
    h log log z ss hc hlog (CapRetag.logUpRefl log) hpr hne hch

/-- `rawChainChainCD` with the bad arm at the primed log. -/
theorem CapRetag.rawChainChainCDUp (GD : Gdexec) (ad : List (Geid × Geid)) (P : Int → Int → Prop)
    (L L' : List Wmsg) (ss : List Seg) :
    CatLin.rvwmoCatAD GD ad → logOf GD.gdG L → protReg P L →
    (∀ prev s, s ∈ ss → CatLin.gcrossE GD.gdG prev s.sgEntry → CatLin.segRunC GD s →
       CatLin.segPinC GD ad s ∨ csHyps GD P L prev s ∨ chainHyps GD prev s ∨
         badSeg GD L' prev s) →
    (∀ prev s, s ∈ ss → CatLin.gcrossE GD.gdG prev s.sgEntry → ¬ badSeg GD L' prev s) →
    ∀ (x y : Geid) (ss' : List Seg),
      ss' ⊆ ss → CatLin.rawChainC GD (CatLin.gcrossE GD.gdG) x y ss' →
      CatLin.chainC GD.gdG (CatLin.gcrossE GD.gdG) x y ss' := by
  intro hc hlog hpr hcl hnb x y ss'
  have hX : ∀ x y, CatLin.gcrossE GD.gdG x y → gmoLt GD.gdG x y :=
    fun x y => CatLin.gcrossEGmo GD.gdG x y hc.1 hc.2.2.1
  induction ss' generalizing x with
  | nil => intro _ hch; exact hch
  | cons s ss' ih =>
    intro hsub hch
    obtain ⟨hx, hrun, hrest⟩ := hch
    have hs : s ∈ ss := hsub (by simp)
    have hsub' : ss' ⊆ ss := fun t ht => hsub (List.mem_cons_of_mem s ht)
    show CatLin.CertC GD.gdG (CatLin.gcrossE GD.gdG) x s ∧
      CatLin.chainC GD.gdG (CatLin.gcrossE GD.gdG) s.sgExit y ss'
    refine ⟨?_, ih _ hsub' hrest⟩
    rcases hcl x s hs hx hrun with hp | hcs | hch | hb
    · exact CatLin.segPinCCert GD ad _ x s hc hx hp
    · exact CatLin.csHypsCertC GD ad _ P L x s hc hX hlog hpr hcs hx
    · exact chainHypsCertC GD ad _ x s hc hch
    · exact absurd hb (hnb x s hs hx)

/-- **THE KILL WITH THE BAD ARM REFUTED AT THE PRIMED RE-TAG** (`cycleKillCD`'s twin): the
refutation needs `¬ badSeg` only over `L′`, where W11-C's `readAt` (with its release-site clause)
lives (`CapRetag.readAtTwin`/`readAtUp`, `noBadSegOfRealized` at `L′`). -/
theorem CapRetag.cycleKillCDUp (GD : Gdexec) (ad : List (Geid × Geid)) (P : Int → Int → Prop)
    (L L' : List Wmsg) (z : Geid) (ss : List Seg) :
    CatLin.rvwmoCatAD GD ad → logOf GD.gdG L → CapRetag.logUp L L' → protReg P L →
    CapRetag.l2ClaimAtCDUp GD ad P → ss ≠ [] →
    CatLin.rawChainC GD (CatLin.gcrossE GD.gdG) z z ss →
    (∀ prev s, s ∈ ss → CatLin.gcrossE GD.gdG prev s.sgEntry → ¬ badSeg GD L' prev s) →
    False := by
  intro hc hlog hup hpr hcl hne hch hnb
  exact CatLin.cycleKillArmsC GD.gdG z ss hc.1 hc.2.2.1 hne
    (CapRetag.rawChainChainCDUp GD ad P L L' ss hc hlog hpr
      (hcl L L' z ss hc hlog hup hpr hne hch) hnb z z ss (fun _ h => h) hch)

end Weak
