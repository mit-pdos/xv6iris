/-
Weak: **W11-C2′ (a3) relArmed — RUN SOUNDNESS of `amB`** (`PROGRESS-relArmed.md`).  Lean-only.

Along a hart-local trace (`htr`: the hart's own states and labels, each a `pstepEv` step at some
fabric states), from a tree satisfying `amB` at a matched state whose flag is below the trace's
fold (`armOk`):
* every 4-byte plain store (`LStore`, `lbSt4`) reached before the cycle's end and before a stop
  finds the hart-local fold `afold` (the primed machine's `WbPrimed.armStep`, write-back bit
  `WbPrimed.pwbEv` of each state) ARMED;
* at the cycle's end (`.pure`) the post holds with the flag below the fold.

Every helper is `Weak.PinRelArm.*`.
-/
import Weak.PinRelArmFetch

namespace Weak
open MachCSL Sail Sail.ConcurrencyInterfaceV1 LeanRV64D LeanRV64D.Functions
open Sail.ArchSem (FreeM)
open Wlabel

namespace PinRelArm
open SailCycleOrderK PinCycRun PinRelArmFp PinDataflow

/-! ## 1. Traces and the hart-local fold -/

/-- The hart-local release-flag fold along a trace of (pre-state, label) pairs. -/
def afold : List (Pexv6 × Wlabel) → Bool → Bool
  | [], b => b
  | (p, l) :: t, b => afold t (WbPrimed.armStep (WbPrimed.pwbEv p) l b)

theorem afoldApp : ∀ (t1 t2 : List (Pexv6 × Wlabel)) (b : Bool),
    afold (t1 ++ t2) b = afold t2 (afold t1 b) := by
  intro t1
  induction t1 with
  | nil => intro _ _; rfl
  | cons x t ih => intro t2 b; obtain ⟨p, l⟩ := x; exact ih t2 _

/-- The fold is monotone in its start. -/
theorem afoldMono : ∀ (t : List (Pexv6 × Wlabel)) (b b' : Bool), (b = true → b' = true) →
    afold t b = true → afold t b' = true := by
  intro t
  induction t with
  | nil => intro b b' h hb; exact h hb
  | cons x t ih =>
    intro b b' h hb
    obtain ⟨p, l⟩ := x
    refine ih _ _ ?_ hb
    intro h1
    unfold WbPrimed.armStep at h1 ⊢
    split
    · rfl
    · rename_i hn
      simp only [hn, Bool.false_eq_true, ↓reduceIte] at h1
      split
      · rename_i hc; simp only [hc, ↓reduceIte] at h1; exact h1
      · rename_i hc; simp only [hc, Bool.false_eq_true, ↓reduceIte] at h1; exact h h1

/-- A hart-local trace: each entry a step of the hart from its state, at some fabric states. -/
inductive htr : Pexv6 → List (Pexv6 × Wlabel) → Pexv6 → Prop where
  | nil (p : Pexv6) : htr p [] p
  | cons {p : Pexv6} {l : Wlabel} {p1 : Pexv6} {t : List (Pexv6 × Wlabel)} {p2 : Pexv6} :
      (∃ d d', pstepEv p d l p1 d') → htr p1 t p2 → htr p ((p, l) :: t) p2

theorem htrApp : ∀ (t1 t2 : List (Pexv6 × Wlabel)) (p p2 : Pexv6), htr p (t1 ++ t2) p2 →
    ∃ pm, htr p t1 pm ∧ htr pm t2 p2 := by
  intro t1
  induction t1 with
  | nil => intro t2 p p2 h; exact ⟨p, .nil p, h⟩
  | cons x t ih =>
    intro t2 p p2 h
    cases h with
    | cons hs hr =>
      obtain ⟨pm, h1, h2⟩ := ih t2 _ p2 hr
      exact ⟨pm, .cons hs h1, h2⟩

/-- The hart is at a cycle boundary. -/
def atPureS (p : Pexv6) : Prop :=
  ∃ (cpu : CPU) (rs : RegFile) (fn : Option (Bool × Bool × Bool × Bool)) (ib : Ibch),
    p = .PHart cpu (.pure ()) rs fn ib

/-- The hart is at a STOP: a write of a cause register. -/
def atStopC (p : Pexv6) : Prop :=
  ∃ (cpu : CPU) (r : Register) (v : RegisterType r) (k : Unit → SailM Unit) (rs : RegFile)
    (fn : Option (Bool × Bool × Bool × Bool)) (ib : Ibch),
    p = .PHart cpu (.impure (.ok (.regWrite r v)) k) rs fn ib ∧ cyS r = true

/-- The trace's states are inside one cycle, off its stops. -/
def inCyc (t : List (Pexv6 × Wlabel)) : Prop :=
  ∀ q, q ∈ t.map Prod.fst → ¬ atPureS q ∧ ¬ atStopC q

/-- A 4-byte plain store label. -/
def lbSt4 (l : Wlabel) : Prop :=
  ∃ (rl : Bool) (a : Int) (data : List (BitVec 8)) (asrc vsrc : List Dsrc),
    l = LStore rl a data asrc vsrc ∧ data.length = 4

/-- A parked fence that arms. -/
def parkArms (fn : Option (Bool × Bool × Bool × Bool)) : Prop :=
  ∃ pr pw sr sw, fn = some (pr, pw, sr, sw) ∧ (pw && sw) = true

/-- The tracked flag is below the fold `b`, up to a pending parked fence. -/
def armOk (a : Bool) (fn : Option (Bool × Bool × Bool × Bool)) (b : Bool) : Prop :=
  a = true → b = true ∨ parkArms fn

/-! ## 2. The flag's step facts -/

theorem armStepNeutral (wb : Bool) (l : Wlabel) (b : Bool) (h1 : WbPrimed.lbArms l = false)
    (h2 : WbPrimed.lbConsumes wb l = false) : WbPrimed.armStep wb l b = b := by
  unfold WbPrimed.armStep; rw [h1, h2]; rfl

theorem armStepFence (wb pr pw sr sw b : Bool) (h : b = true) :
    WbPrimed.armStep wb (LFence pr pw sr sw) b = true := by
  subst h; unfold WbPrimed.armStep; split <;> simp [WbPrimed.lbConsumes]

theorem armStepFenceArms (wb pr pw sr sw b : Bool) (h : (pw && sw) = true) :
    WbPrimed.armStep wb (LFence pr pw sr sw) b = true := by
  unfold WbPrimed.armStep; simp [WbPrimed.lbArms, h]

/-- The barrier's flag update is below the fold after its label, up to its parked fence. -/
theorem armBarOk (bk : barrier_kind) (a b wb : Bool) (h : a = true → b = true) :
    armOk (armBar bk a) (ebarPark bk) (WbPrimed.armStep wb (ebarLabel bk) b) := by
  intro ha
  cases a with
  | true =>
    left
    have hb := h rfl
    unfold ebarLabel
    split <;> exact armStepFence _ _ _ _ _ _ hb
  | false =>
    cases bk <;>
      simp_all [armBar, ebarPark, ebarLabel, ebarNow, WbPrimed.armStep, WbPrimed.lbArms,
        WbPrimed.lbConsumes, parkArms]

theorem erwNeutral (k : ErwKind) (wb : Bool) :
    WbPrimed.lbArms (erwLabel k) = false ∧ WbPrimed.lbConsumes wb (erwLabel k) = false ∧
      isFeLab (erwLabel k) = false := by
  cases k <;> exact ⟨rfl, rfl, rfl⟩

theorem annNeutral (n : Nat) (w : BitVec n) (wb b : Bool) :
    WbPrimed.armStep wb (annLabel n w) b = b ∧ isFeLab (annLabel n w) = false := by
  unfold annLabel
  split <;> simp [WbPrimed.armStep, WbPrimed.lbArms, WbPrimed.lbConsumes, isFeLab]

theorem ebarFe (bk : barrier_kind) : isFeLab (ebarLabel bk) = false := by
  unfold ebarLabel; split <;> rfl

theorem noSt4 (l : Wlabel) (b : Bool) (h : RelSiteProvPc.lbStore l = false) : lbSt4 l → b = true := by
  rintro ⟨rl, a, data, asrc, vsrc, rfl, -⟩; cases h

theorem erwSt (k : ErwKind) : RelSiteProvPc.lbStore (erwLabel k) = false := by cases k <;> rfl
theorem ebarSt (bk : barrier_kind) : RelSiteProvPc.lbStore (ebarLabel bk) = false := by
  unfold ebarLabel; split <;> rfl
theorem annSt (n : Nat) (w : BitVec n) : RelSiteProvPc.lbStore (annLabel n w) = false := by
  unfold annLabel; split <;> rfl

/-! ## 3. One step -/

/-- The register file agrees with every pin. -/
def cfgAg (rs : RegFile) : Prop := ∀ r v0, drefH r = some v0 → rs r = v0

theorem cfgAgSet (rs : RegFile) (r : Register) (v : RegisterType r) (h : cfgAg rs)
    (hn : drefH r = none) : cfgAg (rs.set r v) := by
  intro r' v0 h'
  have e : r' ≠ r := by rintro rfl; rw [hn] at h'; cases h'
  rw [RegFile.set_other _ _ _ _ e]; exact h r' v0 h'

/-- One step's conclusion: a state for the new tree, matched, the flag below the fold, the log
moved by the label, and a 4-byte plain store found the fold armed. -/
def amStepOk (A : Int → BitVec 8 → Prop) (Aa : Nat → Int → Prop) (P : Unit → AmSt → Prop)
    (st : AmSt) (b : Bool) (ib : Ibch) (l : Wlabel) (m' : SailM Unit) (ib' : Ibch) (rs' : RegFile)
    (fn' : Option (Bool × Bool × Bool × Bool)) : Prop :=
  ∃ st', amB A Aa P m' st' ∧ st'.amo = WbPrimed.ibAmo ib' ∧ RbootAll rs' ∧ cfgAg rs' ∧
    armOk st'.armed fn' (WbPrimed.armStep (!WbPrimed.ibAmo ib) l b) ∧ feStep st.fe st'.fe l ∧
    (lbSt4 l → b = true)

theorem amSilent (A : Int → BitVec 8 → Prop) (Aa : Nat → Int → Prop) (P : Unit → AmSt → Prop)
    (st : AmSt) (b : Bool) (ib : Ibch) (m' : SailM Unit) (rs : RegFile) (h : amB A Aa P m' st)
    (hamo : st.amo = WbPrimed.ibAmo ib) (hrb : RbootAll rs) (hcfg : cfgAg rs)
    (harm : st.armed = true → b = true) :
    amStepOk A Aa P st b ib LSilent m' ib rs none :=
  ⟨st, h, hamo, hrb, hcfg, fun ha => Or.inl (by rw [armStepNeutral _ _ _ rfl rfl]; exact harm ha),
    Or.inl ⟨rfl, rfl⟩, noSt4 _ _ rfl⟩

set_option maxHeartbeats 4000000 in
/-- **One Sail node** (header). -/
theorem amNodeStep (A : Int → BitVec 8 → Prop) (Aa : Nat → Int → Prop) (P : Unit → AmSt → Prop)
    (m : SailM Unit) (rs : RegFile) (ib : Ibch) (dd : DevStates) (l : Wlabel) (m' : SailM Unit)
    (ors : Option RegFile) (fn' : Option (Bool × Bool × Bool × Bool)) (dd' : DevStates)
    (oib : Option Ibch) (obar : Option barrier_kind) (st : AmSt) (b : Bool)
    (hstep : pnodeStep m rs ib dd l m' ors fn' dd' oib obar) (hpure : ∀ x, m ≠ .pure x)
    (hns : ∀ r v k, m = .impure (.ok (.regWrite r v)) k → cyS r = false)
    (hcy : amB A Aa P m st) (hamo : st.amo = WbPrimed.ibAmo ib) (hrb : RbootAll rs)
    (hcfg : cfgAg rs) (harm : st.armed = true → b = true) (hA : feAdm A Aa st.fe.length l) :
    amStepOk A Aa P st b ib l m' (oib.getD ib) (ors.getD rs) fn' := by
  match m, hstep with
  | .pure x, _ => exact absurd rfl (hpure x)
  | .impure (.error _) _, h => exact h.elim
  | .impure (.ok o) k, h =>
    cases o with
    | regRead r =>
      obtain ⟨rfl, rfl, rfl, rfl, -, rfl, -⟩ := h
      refine ⟨st, hcy (rs r) (hrb r) (fun v0 h => hcfg r v0 h), ?_, hrb, hcfg,
        fun ha => Or.inl (by rw [armStepNeutral _ _ _ rfl rfl]; exact harm ha),
        Or.inl ⟨rfl, rfl⟩, noSt4 _ _ rfl⟩
      show st.amo = WbPrimed.ibAmo (ibRd ib r)
      unfold WbPrimed.ibAmo; rw [ibRdBits]; exact hamo
    | regWrite r v =>
      obtain ⟨rfl, rfl, rfl, rfl, -, rfl, -⟩ := h
      have hcs := hns r v k rfl
      obtain ⟨hb, hdr, hk⟩ := hcy hcs
      obtain ⟨n1, n2, n3⟩ := erwNeutral (erwOf (depsOfIb ib.ibBits) ib.ibRds r) (!WbPrimed.ibAmo ib)
      refine ⟨st, hk (), hamo, rbootAllSet rs r v hrb hb, cfgAgSet rs r v hcfg hdr,
        fun ha => Or.inl (by rw [armStepNeutral _ _ _ n1 n2]; exact harm ha), Or.inl ⟨n3, rfl⟩, ?_⟩
      exact noSt4 _ _ (erwSt _)
    | memRead n va req =>
      simp only [pnodeStep] at h
      split at h
      · rename_i hdev
        obtain ⟨w, -, rfl, rfl, rfl, rfl, rfl, rfl⟩ := h
        refine ⟨st, hcy.2 (fun h' => absurd (hdev.symm.trans h') (by decide)) w, hamo, hrb, hcfg,
          fun ha => Or.inl (by rw [armStepNeutral _ _ _ rfl rfl]; exact harm ha),
          Or.inl ⟨rfl, rfl⟩, noSt4 _ _ rfl⟩
      · rename_i hdev
        have hdev' : devAddr req.pa = false := by simpa using hdev
        rcases h with ⟨hif, w, tvs, hlen, hb, rfl, rfl, rfl, rfl, -, rfl, rfl⟩ |
          ⟨hif, ⟨-, w, tvs, -, -, rfl, rfl, rfl, rfl, -, rfl, rfl⟩ |
            ⟨-, w, tvs, -, -, rfl, rfl, rfl, rfl, -, rfl, rfl⟩⟩
        · have hel : ∀ j (hj : j < tvs.length), (tvs[j]'hj).2 = nthByte w j := by
            intro j hj
            have h2 := hb j (by rw [← hlen]; exact hj)
            simp only [List.getElem?_map, List.getElem?_eq_getElem hj, Option.map_some,
              Option.some.injEq] at h2
            exact h2
          have hAw : ∀ j, j < n → A (paZ req.pa + (j : Int)) (nthByte w j) := by
            intro j hj
            have hj' : j < tvs.length := by rw [hlen]; exact hj
            rw [← hel j hj']; exact (hA _ tvs rfl).2 j hj'
          refine ⟨amFe st (paZ req.pa) n w, hcy.1 hdev' hif (hA _ tvs rfl).1 w hAw, hamo, hrb, hcfg,
            fun ha => Or.inl (by rw [armStepNeutral _ _ _ rfl rfl]; exact harm ha),
            Or.inr ⟨⟨paZ req.pa, n, w⟩, rfl, tvs, rfl, hlen, hb⟩,
            noSt4 _ _ rfl⟩
        · exact ⟨st, hcy.2 (fun _ => hif) w, hamo, hrb, hcfg,
            fun ha => Or.inl (by rw [armStepNeutral _ _ _ rfl rfl]; exact harm ha),
            Or.inl ⟨rfl, rfl⟩, noSt4 _ _ rfl⟩
        · exact ⟨st, hcy.2 (fun _ => hif) w, hamo, hrb, hcfg,
            fun ha => Or.inl (by rw [armStepNeutral _ _ _ rfl rfl]; exact harm ha),
            Or.inl ⟨rfl, rfl⟩, noSt4 _ _ rfl⟩
    | memWrite n va req =>
      simp only [pnodeStep] at h
      split at h
      · rename_i hdev
        split at h
        · obtain ⟨-, rfl, rfl, rfl, rfl, rfl, rfl⟩ := h
          exact ⟨st, hcy.1 hdev, hamo, hrb, hcfg,
            fun ha => Or.inl (by rw [armStepNeutral _ _ _ rfl rfl]; exact harm ha),
            Or.inl ⟨rfl, rfl⟩, noSt4 _ _ rfl⟩
        · exact h.elim
      · rename_i hdev
        have hdev' : devAddr req.pa = false := by simpa using hdev
        split at h
        · rename_i v _
          obtain ⟨-, ⟨hpl, rfl, rfl, rfl, rfl, -, rfl, rfl⟩ |
            ⟨hex, ⟨rfl, rfl, rfl, rfl, -, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, -, rfl, rfl⟩⟩⟩ := h
          · have hx : akExcl req.access_kind = false := by rw [← classifyAkLatest]; exact hpl
            obtain ⟨hob, hk⟩ := hcy.2.1 hdev' hx
            refine ⟨{ st with armed := false }, hk, hamo, hrb, hcfg, fun ha => absurd ha (by simp),
              Or.inl ⟨rfl, rfl⟩, ?_⟩
            rintro ⟨rl, a, data, asrc, vsrc, e, hl4⟩
            injection e with _ _ e3
            rw [← e3, wbytesLength] at hl4
            exact harm (hob hl4)
          · have hx : akExcl req.access_kind = true := by rw [← classifyAkLatest]; exact hex
            refine ⟨{ st with armed := st.armed && !st.amo }, hcy.2.2 hdev' hx, hamo, hrb, hcfg, ?_,
              Or.inl ⟨rfl, rfl⟩, noSt4 _ _ rfl⟩
            intro ha
            simp only [Bool.and_eq_true, Bool.not_eq_true'] at ha
            left
            have hb := harm ha.1
            unfold WbPrimed.armStep
            simp [WbPrimed.lbArms, WbPrimed.lbConsumes, ← hamo, ha.2, hb]
          · exact amSilent A Aa P st b ib _ rs hcy hamo hrb hcfg harm
        · exact h.elim
    | barrier bk =>
      obtain ⟨rfl, rfl, rfl, rfl, -, rfl, -⟩ := h
      exact ⟨{ st with armed := armBar bk st.armed }, hcy, hamo, hrb, hcfg,
        armBarOk bk st.armed b _ harm, Or.inl ⟨ebarFe bk, rfl⟩,
        noSt4 _ _ (ebarSt bk)⟩
    | instrAnnounce n w =>
      obtain ⟨rfl, rfl, rfl, rfl, -, rfl, -⟩ := h
      obtain ⟨n1, n2⟩ := annNeutral n w (!WbPrimed.ibAmo ib) b
      exact ⟨{ st with amo := WbPrimed.ibAmo (ibAnn (ibOfBvn w)) }, hcy (), rfl, hrb, hcfg,
        fun ha => Or.inl (by rw [n1]; exact harm ha), Or.inl ⟨n2, rfl⟩,
        noSt4 _ _ (annSt n w)⟩
    | getCycleCount =>
      obtain ⟨rfl, rfl, rfl, rfl, -, rfl, -⟩ := h
      exact amSilent A Aa P st b ib _ rs hcy hamo hrb hcfg harm
    | choose x =>
      obtain ⟨ch, rfl, rfl, rfl, rfl, -, rfl, -⟩ := h
      exact amSilent A Aa P st b ib _ rs (hcy ch) hamo hrb hcfg harm
    | readRam => exact h.elim
    | writeRam => exact h.elim
    | _ =>
      obtain ⟨rfl, rfl, rfl, rfl, -, rfl, -⟩ := h
      exact amSilent A Aa P st b ib _ rs (hcy _) hamo hrb hcfg harm

/-- **One step of the hart** (its own node, a parked fence, or a PLIC wire write). -/
theorem amHartStep (A : Int → BitVec 8 → Prop) (Aa : Nat → Int → Prop) (P : Unit → AmSt → Prop)
    (cpu : CPU) (m : SailM Unit) (rs : RegFile) (fn : Option (Bool × Bool × Bool × Bool))
    (ib : Ibch) (d : Efab) (l : Wlabel) (m' : SailM Unit) (ors : Option RegFile)
    (fn' : Option (Bool × Bool × Bool × Bool)) (d' : Efab) (oib : Option Ibch)
    (obar : Option barrier_kind) (st : AmSt) (b : Bool)
    (hstep : pstepHart cpu m rs fn ib d l m' ors fn' d' oib obar) (hpure : ∀ x, m ≠ .pure x)
    (hns : ∀ r v k, m = .impure (.ok (.regWrite r v)) k → cyS r = false)
    (hcy : amB A Aa P m st) (hamo : st.amo = WbPrimed.ibAmo ib) (hrb : RbootAll rs)
    (hcfg : cfgAg rs) (harm : armOk st.armed fn b) (hA : feAdm A Aa st.fe.length l) :
    amStepOk A Aa P st b ib l m' (oib.getD ib) (ors.getD rs) fn' := by
  rcases hstep with ⟨H, -⟩ | H
  · cases fn with
    | some f =>
      obtain ⟨pr, pw, sr, sw⟩ := f
      obtain ⟨rfl, rfl, rfl, rfl, -, rfl, -⟩ := H
      refine ⟨st, hcy, hamo, hrb, hcfg, fun ha => Or.inl ?_, Or.inl ⟨rfl, rfl⟩, noSt4 _ _ rfl⟩
      rcases harm ha with hb | ⟨pr', pw', sr', sw', e, hps⟩
      · exact armStepFence _ _ _ _ _ _ hb
      · simp only [Option.some.injEq, Prod.mk.injEq] at e
        obtain ⟨-, rfl, -, rfl⟩ := e
        exact armStepFenceArms _ _ _ _ _ _ hps
    | none =>
      have harm' : st.armed = true → b = true := by
        intro ha
        rcases harm ha with hb | ⟨_, _, _, _, e, _⟩
        · exact hb
        · cases e
      exact amNodeStep A Aa P m rs ib d.efDev l m' ors fn' d'.efDev oib obar st b H hpure hns hcy
        hamo hrb hcfg harm' hA
  · obtain ⟨mm, bb, k, -, rfl, rfl, rfl, -, rfl, -, rfl⟩ := H
    refine ⟨st, hcy, hamo, ?_, ?_, ?_, Or.inl ⟨rfl, rfl⟩, noSt4 _ _ rfl⟩
    · show RbootAll (pinSet rs mm bb)
      unfold pinSet
      split
      · exact rbootAllSet rs _ _ hrb trivial
      · exact rbootAllSet rs _ _ hrb trivial
    · show cfgAg (pinSet rs mm bb)
      unfold pinSet
      split
      · exact cfgAgSet rs _ _ hcfg rfl
      · exact cfgAgSet rs _ _ hcfg rfl
    · rw [armStepNeutral _ _ _ rfl rfl]; exact harm

/-! ## 4. The run -/

theorem inCycCons (q : Pexv6) (l : Wlabel) (t : List (Pexv6 × Wlabel)) (h1 : ¬ atPureS q)
    (h2 : ¬ atStopC q) (h : inCyc t) : inCyc ((q, l) :: t) := by
  intro x hx
  rcases List.mem_cons.1 hx with rfl | hx
  · exact ⟨h1, h2⟩
  · exact h x hx

theorem inCycHead {q : Pexv6} {l : Wlabel} {t : List (Pexv6 × Wlabel)} (h : inCyc ((q, l) :: t)) :
    ¬ atPureS q ∧ ¬ atStopC q := h q List.mem_cons_self

theorem inCycTail {x : Pexv6 × Wlabel} {t : List (Pexv6 × Wlabel)} (h : inCyc (x :: t)) :
    inCyc t := fun q hq => h q (List.mem_cons_of_mem _ hq)

theorem feStepLen (fe fe' : List FeEnt) (l : Wlabel) (h : feStep fe fe' l) :
    fe'.length = fe.length + (feLabs [l]).length := by
  rcases h with ⟨hl, e⟩ | ⟨e, e1, he⟩
  · rw [e]; simp [feLabs, hl]
  · obtain ⟨tvs, rfl, -⟩ := he
    rw [e1]; simp [feLabs, isFeLab]

set_option maxHeartbeats 4000000 in
/-- **THE RUN** (header). -/
theorem amRun (A : Int → BitVec 8 → Prop) (Aa : Nat → Int → Prop) (P : Unit → AmSt → Prop) :
    ∀ (p : Pexv6) (t : List (Pexv6 × Wlabel)) (p' : Pexv6), htr p t p' →
    ∀ (cpu : CPU) (m : SailM Unit) (rs : RegFile) (fn : Option (Bool × Bool × Bool × Bool))
      (ib : Ibch) (st : AmSt) (b : Bool), p = .PHart cpu m rs fn ib → amB A Aa P m st →
      st.amo = WbPrimed.ibAmo ib → RbootAll rs → cfgAg rs → armOk st.armed fn b →
      (∀ t1 pm l t2, t = t1 ++ (pm, l) :: t2 → inCyc t1 →
        feAdm A Aa (st.fe.length + (feLabs (t1.map Prod.snd)).length) l) →
      (∀ t1 pm l t2, t = t1 ++ (pm, l) :: t2 → inCyc (t1 ++ [(pm, l)]) → lbSt4 l →
        afold t1 b = true) ∧
      (∀ t1 pm l t2, t = t1 ++ (pm, l) :: t2 → inCyc t1 → atPureS pm →
        ∃ (st1 : AmSt) (fn1 : Option (Bool × Bool × Bool × Bool)), P () st1 ∧
          armOk st1.armed fn1 (afold t1 b) ∧
          ∃ (cpu1 : CPU) (rs1 : RegFile) (ib1 : Ibch), pm = .PHart cpu1 (.pure ()) rs1 fn1 ib1 ∧
            RbootAll rs1 ∧ cfgAg rs1) := by
  intro p t p' h
  induction h with
  | nil p =>
    intro cpu m rs fn ib st b hp hcy hamo hrb hcfg harm _
    exact ⟨fun t1 pm l t2 e => absurd e.symm (by simp), fun t1 pm l t2 e => absurd e.symm (by simp)⟩
  | @cons p l p1 t p2 hs hr ih =>
    intro cpu m rs fn ib st b hp hcy hamo hrb hcfg harm hA
    -- the head is the end of the cycle, or a stop: only the empty prefix matters
    by_cases hps : atPureS p ∨ atStopC p
    · refine ⟨fun t1 pm l' t2 e hin _ => ?_, fun t1 pm l' t2 e hin hpm => ?_⟩
      · cases t1 with
        | nil =>
          simp only [List.nil_append, List.cons.injEq] at e
          obtain ⟨⟨rfl, rfl⟩, -⟩ := e
          have := inCycHead hin
          rcases hps with h | h
          · exact absurd h this.1
          · exact absurd h this.2
        | cons x t1' =>
          simp only [List.cons_append, List.cons.injEq] at e
          obtain ⟨rfl, -⟩ := e
          have := inCycHead hin
          rcases hps with h | h
          · exact absurd h this.1
          · exact absurd h this.2
      · cases t1 with
        | nil =>
          simp only [List.nil_append, List.cons.injEq] at e
          obtain ⟨⟨rfl, rfl⟩, -⟩ := e
          obtain ⟨cpu1, rs1, fn1, ib1, e1⟩ := hpm
          rw [hp] at e1
          injection e1 with _ hm hrs hfn _
          subst hm hfn hrs
          exact ⟨st, fn, hcy, harm, cpu1, rs, ib1, by rw [hp]; congr, hrb, hcfg⟩
        | cons x t1' =>
          simp only [List.cons_append, List.cons.injEq] at e
          obtain ⟨rfl, -⟩ := e
          have := inCycHead hin
          rcases hps with h | h
          · exact absurd h this.1
          · exact absurd h this.2
    · have hnp : ¬ atPureS p := fun h => hps (Or.inl h)
      have hnc : ¬ atStopC p := fun h => hps (Or.inr h)
      have hpure : ∀ x, m ≠ .pure x := by
        intro x e; subst e; cases x; exact hnp ⟨cpu, rs, fn, ib, hp⟩
      have hns : ∀ r v k, m = .impure (.ok (.regWrite r v)) k → cyS r = false := by
        intro r v k e
        cases hc : cyS r with
        | false => rfl
        | true => exact absurd ⟨cpu, r, v, k, rs, fn, ib, by rw [hp, e], hc⟩ hnc
      obtain ⟨d, d', hst⟩ := hs
      subst hp
      cases p1 with
      | PDisk _ => exact (show False from hst).elim
      | PHart cpu1 m1 rs1 fn1 ib1 =>
      obtain ⟨rfl, ors, oib, obar, rfl, rfl, hh⟩ := hst
      have hA0 : feAdm A Aa st.fe.length l := by
        have := hA [] _ l t rfl (fun _ h => by simp at h)
        simpa [feLabs] using this
      obtain ⟨st', hcy', hamo', hrb', hcfg', harm', hfe, hst4⟩ :=
        amHartStep A Aa P cpu1 m rs fn ib d l m1 ors fn1 d' oib obar st b hh hpure hns hcy hamo hrb
          hcfg harm hA0
      have hlen := feStepLen st.fe st'.fe l hfe
      obtain ⟨ih1, ih2⟩ := ih cpu1 m1 (ors.getD rs) fn1 (oib.getD ib) st' _ rfl hcy' hamo' hrb'
        hcfg' harm' (fun t1 pm l' t2 e hin => by
          have := hA ((Pexv6.PHart cpu1 m rs fn ib, l) :: t1) pm l' t2 (by rw [e]; rfl)
            (inCycCons _ _ _ hnp hnc hin)
          rw [hlen, Nat.add_assoc]
          have e2 : (feLabs [l]).length + (feLabs (t1.map Prod.snd)).length =
              (feLabs (((Pexv6.PHart cpu1 m rs fn ib, l) :: t1).map Prod.snd)).length := by
            simp only [feLabs, List.map_cons, List.filter_cons, List.filter_nil]
            split <;> simp <;> omega
          rw [e2]; exact this)
      refine ⟨fun t1 pm l' t2 e hin h4 => ?_, fun t1 pm l' t2 e hin hpm => ?_⟩
      · cases t1 with
        | nil =>
          simp only [List.nil_append, List.cons.injEq] at e
          obtain ⟨⟨-, rfl⟩, -⟩ := e
          exact hst4 h4
        | cons x t1' =>
          simp only [List.cons_append, List.cons.injEq] at e
          obtain ⟨rfl, e⟩ := e
          exact ih1 t1' pm l' t2 e (inCycTail hin) h4
      · cases t1 with
        | nil =>
          simp only [List.nil_append, List.cons.injEq] at e
          obtain ⟨⟨rfl, -⟩, -⟩ := e
          exact absurd hpm hnp
        | cons x t1' =>
          simp only [List.cons_append, List.cons.injEq] at e
          obtain ⟨rfl, e⟩ := e
          exact ih2 t1' pm l' t2 e (inCycTail hin) hpm

end PinRelArm
end Weak
