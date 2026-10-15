/-
Weak: **W11-C2′ (a3) [OWN.82][OWN.97] — the release flag is SET at every release store of the
PRIMED run, from a Weak-free arming premise.**

On the primed machine (`Weak/WbPrimed.lean`) a hart's release-pending flag `wRelp` is
* SET by a fence ordering prior writes before later writes (`LFence _ true _ true`; `fencePost`),
* CLEARED only by a store run of the hart's own: `LStore`, `LRmw`, or `LExStore` OUTSIDE a
  write-back node (the walker's A/D write-back keeps it — the one primed difference),
* kept by every other label (loads, exclusive loads, register / control / instruction / i-fetch
  / device / silent steps) and by every step of another agent.

So the flag of agent `j` is the fold `WbPrimed.armFold j` of the per-step effect
`WbPrimed.armStep` over the record — which reads only agents, labels and the PROGRAM states'
write-back bit (`WbPrimed.pwbEv`), nothing of the weak-memory state.

* `WbPrimed.stepRelpW` / `WbPrimed.chainRelp`: the fold under-approximates the flag, step by step
  and along a primed record.
* `WbPrimed.pnodeStoreRel` / `WbPrimed.pstepEvStoreRel`: a hart's `LStore` comes from a
  NON-exclusive `memWrite` node, so with the flag set its class is `.WCrel`.
* **(a3) NAMED** `WbPrimed.relArmed r`: every recorded plain store at a release pc has its agent's
  fold set (the `fence rw,w` / `fence rw,rw` at `pc − 4` ran, and the hart issued no store run of
  its own since).  Weak-free: it is a statement about W4's REGISTERED record (agents, labels,
  program states), transferred to the primed record by `WbPrimed.relArmedRel`.
* `WbPrimed.relStepWCrelOfArmed`: (a3)'s step obligation on the primed record.
* `WbPrimed.relSiteWCrelArmed`: (a1) + (a3) ⇒ the primed twin of a W4 record has a final
  configuration whose log satisfies `relSiteWCrel σ`; `WbPrimed.ownedUnpubRefutedArmed`: W11-C's
  refutation there.

Lean-only (no Rocq counterpart); every name is file-qualified (`WbPrimed.*`).
-/
import Weak.WbPrimedRel

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Sail Sail.ConcurrencyInterfaceV1 LeanRV64D
open MachOfPf RelSiteProvPc PfStepTsoMem
open Wlabel

/-! ## 1. The flag's per-step effect (program-level) -/

/-- A label that ARMS the release flag: a fence ordering prior writes before later writes. -/
def WbPrimed.lbArms : Wlabel → Bool
  | .LFence _ pw _ sw => pw && sw
  | _ => false

/-- A label that CONSUMES the release flag on the primed machine (`wb`: the agent is at a
write-back node). -/
def WbPrimed.lbConsumes (wb : Bool) : Wlabel → Bool
  | .LStore .. | .LRmw .. => true
  | .LExStore .. => !wb
  | _ => false

/-- One step's effect on the tracked flag. -/
def WbPrimed.armStep (wb : Bool) (l : Wlabel) (b : Bool) : Bool :=
  if WbPrimed.lbArms l then true else if WbPrimed.lbConsumes wb l then false else b

/-- The tracked flag of agent `j` after agent `i` takes an `l` step from `c`. -/
def WbPrimed.armAt {P D : Type} (pwb : P → Bool) (c : Wpcfg P D) (i : Nat) (l : Wlabel) (j : Nat)
    (b : Bool) : Bool :=
  if i = j then (c.pcAgs[i]?).elim b (fun ag => WbPrimed.armStep (pwb ag.paSt) l b) else b

/-! ## 2. The fold under-approximates the flag -/

theorem WbPrimed.setRelp {P : Type} (as_ : List (Wpagent P)) (i j : Nat) (ag0 ag' : Wpagent P)
    (b bi : Bool) (hlk : as_[i]? = some ag0)
    (hb : b = true → ∀ ag, as_[j]? = some ag → ag.paWs.wRelp = true)
    (hpost : (b = true → ag0.paWs.wRelp = true) → bi = true → ag'.paWs.wRelp = true) :
    (if i = j then bi else b) = true → ∀ ag, (as_.set i ag')[j]? = some ag → ag.paWs.wRelp = true := by
  intro ha ag hag
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl] at ha
    have hlt : i < as_.length := by
      rcases Nat.lt_or_ge i as_.length with h | h
      · exact h
      · rw [List.getElem?_eq_none_iff.2 h] at hlk; cases hlk
    rw [List.getElem?_set_self hlt] at hag
    cases hag
    exact hpost (fun h => hb h ag0 hlk) ha
  · rw [if_neg hij] at ha
    rw [List.getElem?_set_ne hij] at hag
    exact hb ha ag hag

/-- **One primed step**: the tracked flag stays below the real one. -/
theorem WbPrimed.stepRelpW {P D : Type} (pstep : P → D → Wlabel → P → D → Prop)
    (pcls : P → Wlabel → Wstate → WmClass) (pwb : P → Bool) (i : Nat) (l : Wlabel)
    (c c' : Wpcfg P D) (h : WbPrimed.wpPfStepW pstep pcls pwb i l c c') (j : Nat) (b : Bool)
    (hb : b = true → ∀ ag, c.pcAgs[j]? = some ag → ag.paWs.wRelp = true) :
    WbPrimed.armAt pwb c i l j b = true → ∀ ag, c'.pcAgs[j]? = some ag → ag.paWs.wRelp = true := by
  intro ha
  unfold WbPrimed.armAt at ha
  cases h with
  | PFSilent _ ag st' d' hlk _ =>
    rw [hlk] at ha
    exact WbPrimed.setRelp _ i j ag _ b _ hlk hb (fun h0 h => h0 h) ha
  | PFLoad _ ag aq lat base tvs asrc st' d' hlk _ _ =>
    rw [hlk] at ha
    refine WbPrimed.setRelp _ i j ag _ b _ hlk hb (fun h0 h => ?_) ha
    show (loadPostRunD ag.paWs aq (srcsView ag.paWs asrc) base (tvs.map Prod.fst)).wRelp = true
    rw [loadPostRunDRelp]; exact h0 h
  | PFStore _ ag rl base data asrc vsrc k st' d' hlk _ _ _ =>
    rw [hlk] at ha
    refine WbPrimed.setRelp _ i j ag _ b _ hlk hb (fun _ h => ?_) ha
    simp [WbPrimed.armStep, WbPrimed.lbArms, WbPrimed.lbConsumes] at h
  | PFRmw _ ag aq rl base tvs data asrc vsrc k st' d' hlk _ _ _ _ _ _ =>
    rw [hlk] at ha
    refine WbPrimed.setRelp _ i j ag _ b _ hlk hb (fun _ h => ?_) ha
    simp [WbPrimed.armStep, WbPrimed.lbArms, WbPrimed.lbConsumes] at h
  | PFFence _ ag pr pw sr sw st' d' hlk _ =>
    rw [hlk] at ha
    refine WbPrimed.setRelp _ i j ag _ b _ hlk hb (fun h0 h => ?_) ha
    show (fencePost ag.paWs pr pw sr sw).wRelp = true
    cases hps : (pw && sw) with
    | true => simp [fencePost, hps]
    | false =>
      have hb' : b = true := by
        simpa [WbPrimed.armStep, WbPrimed.lbArms, WbPrimed.lbConsumes, hps] using h
      simp only [fencePost, hps]
      exact h0 hb'
  | PFDev _ ag st' d' hlk _ =>
    rw [hlk] at ha
    exact WbPrimed.setRelp _ i j ag _ b _ hlk hb (fun h0 h => h0 h) ha
  | PFRegW _ ag rd srcs st' d' hlk _ =>
    rw [hlk] at ha
    exact WbPrimed.setRelp _ i j ag _ b _ hlk hb (fun h0 h => h0 h) ha
  | PFCtrl _ ag srcs st' d' hlk _ =>
    rw [hlk] at ha
    exact WbPrimed.setRelp _ i j ag _ b _ hlk hb (fun h0 h => h0 h) ha
  | PFInstr _ ag st' d' hlk _ =>
    rw [hlk] at ha
    exact WbPrimed.setRelp _ i j ag _ b _ hlk hb (fun h0 h => h0 h) ha
  | PFExLoad _ ag aq base tvs asrc st' d' hlk _ _ =>
    rw [hlk] at ha
    refine WbPrimed.setRelp _ i j ag _ b _ hlk hb (fun h0 h => ?_) ha
    show (exloadPostRunD ag.paWs aq (srcsView ag.paWs asrc) base (tvs.map Prod.fst)).wRelp = true
    rw [exloadPostRunDRelp]; exact h0 h
  | PFExStore _ ag rl base data asrc vsrc k R st' d' hlk _ _ _ _ _ _ _ =>
    rw [hlk] at ha
    refine WbPrimed.setRelp _ i j ag _ b _ hlk hb (fun h0 h => ?_) ha
    show (WbPrimed.exPost (pwb ag.paSt) ag.paWs _).wRelp = true
    cases hw : pwb ag.paSt with
    | false => simp [WbPrimed.armStep, WbPrimed.lbArms, WbPrimed.lbConsumes, hw] at h
    | true =>
      have hb' : b = true := by
        simpa [WbPrimed.armStep, WbPrimed.lbArms, WbPrimed.lbConsumes, hw] using h
      exact h0 hb'
  | PFIFetch _ ag base tvs st' d' hlk _ _ =>
    rw [hlk] at ha
    exact WbPrimed.setRelp _ i j ag _ b _ hlk hb (fun h0 h => h0 h) ha

/-- **The tracked flag of agent `j` along a record** (agents, labels, program states only). -/
def WbPrimed.armFold (j : Nat) : List PfRec → Bool → Bool
  | [], b => b
  | x :: r, b => WbPrimed.armFold j r (WbPrimed.armAt WbPrimed.pwbEv x.pre x.ag x.lb j b)

/-- **Along a primed record**: where the fold of the steps before entry `n` is set, the agent's
flag is set at entry `n`'s pre-state. -/
theorem WbPrimed.chainRelp {c : Wpcfg Pexv6 Efab} {r : List PfRec} {cN : Wpcfg Pexv6 Efab}
    (h : WbPrimed.chainW c r cN) :
    ∀ (j : Nat) (b : Bool), (b = true → ∀ ag, c.pcAgs[j]? = some ag → ag.paWs.wRelp = true) →
      ∀ (n : Nat) (x : PfRec), r[n]? = some x → WbPrimed.armFold j (r.take n) b = true →
        ∀ ag, x.pre.pcAgs[j]? = some ag → ag.paWs.wRelp = true := by
  induction h with
  | nil => intro j b _ n x hx; simp at hx
  | cons c c' i l k r cN hs _ ih =>
    intro j b hb n x hx ha
    cases n with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hx
      subst hx
      exact hb ha
    | succ n =>
      simp only [List.getElem?_cons_succ] at hx
      simp only [List.take_succ_cons, WbPrimed.armFold] at ha
      exact ih j _ (WbPrimed.stepRelpW _ _ _ i l c c' hs j b hb) n x hx ha

/-- Every entry of a primed record is a primed step from its pre-state. -/
theorem WbPrimed.chainStepAt {c : Wpcfg Pexv6 Efab} {r : List PfRec} {cN : Wpcfg Pexv6 Efab}
    (h : WbPrimed.chainW c r cN) :
    ∀ (n : Nat) (x : PfRec), r[n]? = some x → ∃ c', WbPrimed.pfStepEvW x.ag x.lb x.pre c' := by
  induction h with
  | nil => intro n x hx; simp at hx
  | cons c c' i l k r cN hs _ ih =>
    intro n x hx
    cases n with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hx
      subst hx
      exact ⟨c', hs⟩
    | succ n =>
      simp only [List.getElem?_cons_succ] at hx
      exact ih n x hx

/-! ## 3. A hart's plain store is stamped `.WCrel` when the flag is set -/

/-- A hart's `LStore` comes from a NON-exclusive `memWrite` node. -/
theorem WbPrimed.pnodeStoreRel (m : SailM Unit) (rs : RegFile) (ib : Ibch) (d : DevStates)
    (rl : Bool) (base : Int) (data : List (BitVec 8)) (asrc vsrc : List Dsrc) (m' : SailM Unit)
    (ors : Option RegFile) (fn' : Option (Bool × Bool × Bool × Bool)) (d' : DevStates)
    (oib : Option Ibch) (obar : Option barrier_kind) (ws : Wstate) :
    pnodeStep m rs ib d (LStore rl base data asrc vsrc) m' ors fn' d' oib obar →
    ws.wRelp = true → pnodeWclass m ws = .WCrel := by
  intro h hr
  match m, h with
  | .pure _, h => obtain ⟨_, hl, _⟩ := h; cases hl
  | .impure (.error _) _, h => exact h.elim
  | .impure (.ok o) k, h =>
    cases o with
    | regRead r => obtain ⟨hl, _⟩ := h; cases hl
    | regWrite r v =>
      obtain ⟨hl, _⟩ := h
      revert hl
      generalize erwOf (depsOfIb ib.ibBits) ib.ibRds r = e
      intro hl
      cases e <;> cases hl
    | memRead n va req =>
      simp only [pnodeStep] at h
      split at h
      · obtain ⟨_, _, hl, _⟩ := h; cases hl
      · rcases h with ⟨_, _, _, _, _, hl, _⟩ | ⟨_, ⟨_, _, _, _, _, hl, _⟩ | ⟨_, _, _, _, _, hl, _⟩⟩
        · cases hl
        · cases hl
        · cases hl
    | memWrite n va req =>
      simp only [pnodeStep] at h
      split at h
      · split at h
        · obtain ⟨_, hl, _⟩ := h; cases hl
        · exact h.elim
      · split at h
        · rcases h with ⟨_, ⟨hlat, _, _⟩ | ⟨_, ⟨hl, _⟩ | ⟨hl, _⟩⟩⟩
          · simp [pnodeWclass, wmClassOf, hlat, hr]
          · cases hl
          · cases hl
        · exact h.elim
    | readRam => exact h.elim
    | writeRam => exact h.elim
    | barrier b =>
      obtain ⟨hl, _⟩ := h
      unfold ebarLabel at hl
      split at hl <;> cases hl
    | cacheOp => obtain ⟨hl, _⟩ := h; cases hl
    | tlbi => obtain ⟨hl, _⟩ := h; cases hl
    | translationStart => obtain ⟨hl, _⟩ := h; cases hl
    | translationEnd => obtain ⟨hl, _⟩ := h; cases hl
    | takeException => obtain ⟨hl, _⟩ := h; cases hl
    | returnException => obtain ⟨hl, _⟩ := h; cases hl
    | cycleCount => obtain ⟨hl, _⟩ := h; cases hl
    | getCycleCount => obtain ⟨hl, _⟩ := h; cases hl
    | message => obtain ⟨hl, _⟩ := h; cases hl
    | choose p => obtain ⟨_, hl, _⟩ := h; cases hl
    | instrAnnounce n w =>
      obtain ⟨hl, _⟩ := h
      unfold annLabel at hl
      split at hl <;> cases hl
    | branchAnnounce => obtain ⟨hl, _⟩ := h; cases hl

/-- **A hart's plain store, with the flag set, is release-class.** -/
theorem WbPrimed.pstepEvStoreRel (cpu : CPU) (m : SailM Unit) (rs : RegFile)
    (fn : Option (Bool × Bool × Bool × Bool)) (ib : Ibch) (d : Efab) (rl : Bool) (base : Int)
    (data : List (BitVec 8)) (asrc vsrc : List Dsrc) (p' : Pexv6) (d' : Efab) (ws : Wstate) :
    pstepEv (.PHart cpu m rs fn ib) d (LStore rl base data asrc vsrc) p' d' → ws.wRelp = true →
    pclsEv (.PHart cpu m rs fn ib) (LStore rl base data asrc vsrc) ws = .WCrel := by
  intro h hr
  show pnodeWclass m ws = .WCrel
  cases p' with
  | PDisk _ => exact h.elim
  | PHart cpu' m' rs' fn' ib' =>
    obtain ⟨-, ors, oib, obar, -, -, h⟩ := h
    rcases h with ⟨hn, -⟩ | ⟨_, _, _, _, hl, _⟩
    · cases fn with
      | some f =>
        obtain ⟨pr, pw, sr, sw⟩ := f
        obtain ⟨hl, _⟩ := hn
        cases hl
      | none => exact WbPrimed.pnodeStoreRel m rs ib _ rl base data asrc vsrc m' ors fn' _ oib obar ws hn hr
    · cases hl

/-- The same, for an agent at a release pc (the disk agent has none). -/
theorem WbPrimed.storeRelPc (p : Pexv6) (d : Efab) (rl : Bool) (base : Int)
    (data : List (BitVec 8)) (asrc vsrc : List Dsrc) (p' : Pexv6) (d' : Efab) (ws : Wstate) :
    pcOfSt p ∈ releasePcs → pstepEv p d (LStore rl base data asrc vsrc) p' d' →
    ws.wRelp = true → pclsEv p (LStore rl base data asrc vsrc) ws = .WCrel := by
  intro hpc hps hr
  cases p with
  | PDisk dp => exact absurd hpc negOneNotRelease
  | PHart cpu m rs fn ib => exact WbPrimed.pstepEvStoreRel cpu m rs fn ib d rl base data asrc vsrc p' d' ws hps hr

/-! ## 4. (a3) -/

/-- **(a3) NAMED — the arming fence ahead of every release store.**  Every recorded plain store
whose agent sits at a release pc has its agent's tracked flag set by the steps before it.  It reads
only agents, labels and program states (no weak-memory state), so it is a statement about W4's
REGISTERED record; for xv6 it is the per-hart stretch `fence rw,w` (`release+0x16`) /
`fence rw,rw` (`main+0xac`) … plain store at `pc` (`releaseSites`), with no own store run in
between (interrupts masked; no fault at the kernel-mapped `sw`; the walker's A/D write-back
keeps the flag on the primed machine). -/
def WbPrimed.relArmed (r : List PfRec) : Prop :=
  ∀ (n : Nat) (x : PfRec), r[n]? = some x → lbStore x.lb = true →
    ∀ ag, x.pre.pcAgs[x.ag]? = some ag → pcOfSt ag.paSt ∈ releasePcs →
      WbPrimed.armFold x.ag (r.take n) false = true

/-- **(a3)'s step obligation on a primed record.** -/
theorem WbPrimed.relStepWCrelOfArmed {c : Wpcfg Pexv6 Efab} {r : List PfRec}
    {cN : Wpcfg Pexv6 Efab} (h : WbPrimed.chainW c r cN) (ha : WbPrimed.relArmed r) :
    relStepWCrel r := by
  intro x hx hst ag hag hpc
  obtain ⟨n, hn⟩ := List.mem_iff_getElem?.1 hx
  have hrelp : ag.paWs.wRelp = true :=
    WbPrimed.chainRelp h x.ag false (fun h => by cases h) n x hn (ha n x hn hst ag hag hpc) ag hag
  obtain ⟨c', hs⟩ := WbPrimed.chainStepAt h n x hn
  revert hs hst hag
  generalize x.pre = p
  generalize x.ag = i
  generalize x.lb = l
  intro hst hag hs
  cases l with
  | LStore rl base data asrc vsrc =>
    cases hs with
    | PFStore _ ag0 _ _ _ _ _ k st' d' hlk hps _ _ =>
      have e : ag0 = ag := Option.some.inj (hlk.symm.trans hag)
      rw [e] at hps
      exact WbPrimed.storeRelPc ag.paSt _ rl base data asrc vsrc st' d' ag.paWs hpc hps hrelp
  | _ => cases hst

/-! ## 5. The registered premise transfers to the primed record -/

theorem WbPrimed.forall₂Lookup {α β : Type} {R : α → β → Prop} {l : List α} {l' : List β}
    (h : List.Forall₂ R l l') : ∀ (n : Nat) (y : β), l'[n]? = some y → ∃ x, l[n]? = some x ∧ R x y := by
  induction h with
  | nil => intro n y hy; simp at hy
  | cons hxy _ ih =>
    intro n y hy
    cases n with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hy
      subst hy
      exact ⟨_, rfl, hxy⟩
    | succ n =>
      simp only [List.getElem?_cons_succ] at hy ⊢
      exact ih n y hy

theorem WbPrimed.forall₂Take {α β : Type} {R : α → β → Prop} {l : List α} {l' : List β}
    (h : List.Forall₂ R l l') : ∀ n : Nat, List.Forall₂ R (l.take n) (l'.take n) := by
  induction h with
  | nil => intro n; simp
  | cons hxy _ ih =>
    intro n
    cases n with
    | zero => simp
    | succ n => simp only [List.take_succ_cons]; exact .cons hxy (ih n)

/-- Related configurations have the same program state at every agent. -/
theorem WbPrimed.cfgRelSt {c c' : Wpcfg Pexv6 Efab} (h : WbPrimed.cfgRel c c') (i : Nat) :
    (c'.pcAgs[i]?).map Wpagent.paSt = (c.pcAgs[i]?).map Wpagent.paSt := by
  cases hx : c.pcAgs[i]? with
  | none =>
    have : c'.pcAgs[i]? = none := by
      rw [List.getElem?_eq_none_iff] at hx ⊢
      have := h.2.2.2.1
      omega
    rw [this]
  | some ag =>
    obtain ⟨ag', h1, h2, -, -⟩ := h.2.2.2.2 i ag hx
    rw [h1]; simp [h2]

theorem WbPrimed.armAtRel (x y : PfRec) (h : WbPrimed.recRel x y) (j : Nat) (b : Bool) :
    WbPrimed.armAt WbPrimed.pwbEv y.pre y.ag y.lb j b
      = WbPrimed.armAt WbPrimed.pwbEv x.pre x.ag x.lb j b := by
  obtain ⟨hag, hlb, -, hR⟩ := h
  unfold WbPrimed.armAt
  rw [hag, hlb]
  have hs := WbPrimed.cfgRelSt hR x.ag
  cases hx : x.pre.pcAgs[x.ag]? with
  | none =>
    rw [hx] at hs
    cases hy : y.pre.pcAgs[x.ag]? with
    | none => rfl
    | some _ => rw [hy] at hs; cases hs
  | some ag =>
    rw [hx] at hs
    cases hy : y.pre.pcAgs[x.ag]? with
    | none => rw [hy] at hs; cases hs
    | some ag' =>
      rw [hy] at hs
      simp only [Option.map_some, Option.some.injEq] at hs
      simp only [Option.elim, hs]

theorem WbPrimed.armFoldRel {r r' : List PfRec} (h : List.Forall₂ WbPrimed.recRel r r') (j : Nat) :
    ∀ b : Bool, WbPrimed.armFold j r' b = WbPrimed.armFold j r b := by
  induction h with
  | nil => intro b; rfl
  | cons hxy _ ih =>
    intro b
    simp only [WbPrimed.armFold]
    rw [WbPrimed.armAtRel _ _ hxy, ih]

/-- **The registered premise gives the primed one.** -/
theorem WbPrimed.relArmedRel {r r' : List PfRec} (h : List.Forall₂ WbPrimed.recRel r r') :
    WbPrimed.relArmed r → WbPrimed.relArmed r' := by
  intro ha n y hy hst ag' hag' hpc
  obtain ⟨x, hx, hxy⟩ := WbPrimed.forall₂Lookup h n y hy
  have hxy' := hxy
  obtain ⟨hag, hlb, -, hR⟩ := hxy'
  have hs := WbPrimed.cfgRelSt hR x.ag
  rw [hag] at hag'
  rw [hag'] at hs
  cases hxa : x.pre.pcAgs[x.ag]? with
  | none => rw [hxa] at hs; cases hs
  | some ag =>
    rw [hxa] at hs
    simp only [Option.map_some, Option.some.injEq] at hs
    rw [WbPrimed.armFoldRel (WbPrimed.forall₂Take h n), hag]
    exact ha n x hx (hlb ▸ hst) ag hxa (hs ▸ hpc)

/-! ## 6. The composition -/

/-- **THE RELEASE-SITE FACT, from (a1) and (a3) on W4's registered record**: the primed twin of
the record ends at a configuration related to the registered one whose log satisfies
`relSiteWCrel σ`. -/
theorem WbPrimed.relSiteWCrelArmed {fok : Image → List Wmsg → Nat → Int → List (Nat × BitVec 8) → Prop}
    {fcutT : Nat → Image → List Wmsg → Nat → Int → List (Nat × BitVec 8) → Prop}
    {c : Wpcfg Pexv6 Efab} {st : List (Nat × Wlabel)} {r : List PfRec} {cN : Wpcfg Pexv6 Efab}
    (h : contRC fok fcutT c st r cN) (h0 : c.pcLog = []) (σ : MState)
    (ha1 : RelSiteProv.relProvExport σ (recPcLog r)) (ha3 : WbPrimed.relArmed r) :
    ∃ cN', WbPrimed.cfgRel cN cN' ∧ relSiteWCrel σ cN'.pcLog := by
  obtain ⟨r', cN', hc, hRN, hF⟩ := WbPrimed.chainOfContR h c (WbPrimed.cfgRelRefl c)
  exact ⟨cN', hRN, WbPrimed.relSiteWCrelPrimed σ r r' c cN' hc h0 hF ha1
    (WbPrimed.relStepWCrelOfArmed hc (WbPrimed.relArmedRel hF ha3))⟩

/-- **W11-C's refutation at the end of the primed twin** of a W4 record, from (a1) and (a3). -/
theorem WbPrimed.ownedUnpubRefutedArmed
    {fok : Image → List Wmsg → Nat → Int → List (Nat × BitVec 8) → Prop}
    {fcutT : Nat → Image → List Wmsg → Nat → Int → List (Nat × BitVec 8) → Prop}
    {c : Wpcfg Pexv6 Efab} {st0 : List (Nat × Wlabel)} {r : List PfRec} {cN : Wpcfg Pexv6 Efab}
    (h : contRC fok fcutT c st0 r cN) (h0 : c.pcLog = [])
    (st : List (Nat × Wlabel)) (σ : MState) (j : CPU) (pa : PAddr) (p : Nat) (m : Wmsg) (i : Nat)
    (ha1 : RelSiteProv.relProvExport σ (recPcLog r)) (ha3 : WbPrimed.relArmed r)
    (hR : rmem cN st σ) (hD : Xv6.AccessDiscipline.xv6AccessDisc σ) (hp : cN.pcLog[p]? = some m)
    (hv : (msgByte m (paZ pa)).isSome) (hram : inRam pa 1) (hcoh : (σ.hr j).coh pa = p + 1)
    (hi : m.wmTid = some i) (hiN : i < NCPU) (hij : i ≠ hartAgent j) :
    ∃ cN', WbPrimed.cfgRel cN cN' ∧ ∃ m', cN'.pcLog[p]? = some m' ∧ m'.wmTid = m.wmTid ∧
      (benignAt σ pa (p + 1) ∨ ¬ (m'.wmAk = .WCplain ∧ ¬ wpublished cN'.pcLog m'.wmTid p)) := by
  obtain ⟨cN', hRN, hsite⟩ := WbPrimed.relSiteWCrelArmed h h0 σ ha1 ha3
  exact ⟨cN', hRN, WbPrimed.ownedUnpubRefutedPrimed cN'.pcLog cN cN' st σ j pa p m i hR hRN hD hsite
    (List.prefix_refl _) hp hv hram hcoh hi hiN hij⟩

end Weak
