/-
Weak: **the S-R `DomAt` lift, increment I-2 (1/2) — `SbOrdR`, THE S-R GATE and its WALK INVARIANT**
(ruling [OWN.150]; `PROGRESS-DomAt.md` §0.2; `PROGRESS-SPSR.md` §7 steps 1–2, 4).  Lean-only, no Rocq twin.
A leaf: nothing registered imports this file.

**Spec, stated first.**  RVWMO lets a plain load return any write co-between its view floor and the latest
one (load value + from-reads); stores land in ONE global write order (gmo|W).  The S-R gate walks GF's
writes IN GF's ORDER (S-P: a landing, and an AMO head whose write lands at its event, only as GF's NEXT
write) and realizes a plain load at its GF timestamp as soon as its source has LANDED (or the byte is
forwarded with GF's value) — the load's STALE read is admissible by view domination (`SbDom`).  So no
landing waits for a reader any more: `SbOrd.readersDone` is gone.

  §1  **THE S-R GATE** `SbOrdR.enbR`: `srGate` (forwarded with GF's value, or source landed; an `.aq`
      load's own source gmo-before it — finding F-DomAt-1), the exempt arm (`X`), stores / fences as
      `SbOrd.enbL`, the AMO arm (`amoOk`, the `.rl`/`.aq` buffer conditions, GF's next write), I/O; a
      landing `landR` (the policy and GF's next write).
  §2  the walk-state invariant **`SbOrdR.PInvR`**: `SbOrd.PInv` WITHOUT `rd` (an unrealized read is no
      longer at the member-latest) plus the S-P prefix `spw` (`wrW w <+: gwrites G`), VERBATIM labels off
      the exempt reads (`vb`), and VIEW DOMINATION at every hart (`dom`, `SbDom.DomInv`).
  §3  S-P gives the per-byte co prefix (`coPfx`), so `SbAgree.pfx` is kept.
  §4  **THE ITEMS KEEP `PInvR`**: `pinvLandR` (an enabled landing), `pinvEvR` (a head event with the arm's
      member label: GF's label off the exempt reads, an AMO GF's next write, a load's `SrBytes`).

Spec: FAITHFUL (proof organisation; the read rule is riscv.cat's load value).  Lean-only helpers `SbOrdR.*`.
-/
import Weak.SbDom

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Lbl

namespace SbOrdR

open SbWalk SbAgree SbReplay SbOrd SpikeSP SbDom

/-! # 1. The S-R gate -/

/-- **THE S-R READ GATE**: every byte forwarded with GF's value, or not forwarded with its GF source LANDED
(`t ≤ |wrW|`: at an S-P state the landed writes are GF's first ones); an `.aq` load's own source must be
gmo-before it (F-DomAt-1). -/
def srGate (G : Gexec) (w : WS) (x : Nat) (aq : Bool) (base : Int) (ts : List Nat) (vs : List (BitVec 8)) :
    Prop :=
  ∀ j t v, ts[j]? = some t → vs[j]? = some v →
    SbCand.fwdByte (w.σ.sb x) (accAddr base j) = some v ∨
    (SbCand.fwdByte (w.σ.sb x) (accAddr base j) = none ∧ t ≤ (wrW w).length ∧
      (aq = true → ∀ s, gwriteAt G t = some s → s.1 = x → gmoLt G s (hd w x)))

/-- **THE PER-LABEL S-R GATE** of row `e.1`'s next event `e` with GF label `l`. -/
def enbLR (G : Gexec) (X : Geid → Prop) (w : WS) (e : Geid) : Lbl → Prop
  | LLoad aq base ts vs =>
      X e ∨ (¬ X e ∧ (aq = true → SbCand.noRl (w.σ.sb e.1)) ∧ srGate G w e.1 aq base ts vs)
  | LStore rl _ _ _ => (rl = true → w.σ.sb e.1 = []) ∧ (NCPU ≤ e.1 → wrW w ++ [e] <+: gwrites G)
  | LFence _ pw sr _ => SbCand.drains pw sr = true → w.σ.sb e.1 = []
  | LRmw aq rl base ts _ _ _ =>
      SbCand.amoOk (w.σ.sb e.1) base ts.length ∧ (rl = true → w.σ.sb e.1 = []) ∧
      (aq = true → SbCand.noRl (w.σ.sb e.1)) ∧ wrW w ++ [e] <+: gwrites G
  | LIo .. => w.σ.sb e.1 = []

/-- **THE S-R LANDING GATE**: the policy, and the store is GF's NEXT write (S-P). -/
def landR (pol : SbPol) (G : Gexec) (w : WS) (i k : Nat) : Prop :=
  ∃ p, (w.pend i)[k]? = some p ∧ pol.landOk (w.σ.sb i) k ∧ wrW w ++ [(i, p.1)] <+: gwrites G

/-- **THE S-R GATE** (with `SbOrd.enb`'s [OWN.151] device unit: while a device store is pending only its
landing goes, `SbOrd.devQuiet`). -/
def enbR (pol : SbPol) (G : Gexec) (X : Geid → Prop) (dev : List Geid) (w : WS) : Tgt → Prop
  | .hd x => SbOrd.devQuiet w ∧ ∃ l, gxLbl G (hd w x) = some l ∧ fabOk dev w (hd w x) ∧ enbLR G X w (hd w x) l
  | .ld i k => (SbOrd.devQuiet w ∨ NCPU ≤ i) ∧ landR pol G w i k

/-- **THE S-R DEVICE UNIT** ([OWN.151], `SbOrd.devUnit` with the S-R landing gate): a device row with a
pending store holds exactly one, its landing is enabled, no other device row has one. -/
def devUnitR (G : Gexec) (w : WS) : Prop :=
  ∀ i, NCPU ≤ i → w.pend i ≠ [] →
    (w.pend i).length = 1 ∧ landR SbPol.epoch G w i 0 ∧ ∀ j, NCPU ≤ j → j ≠ i → w.pend j = []

/-! # 2. The walk-state invariant -/

/-- **THE S-R WALK-STATE INVARIANT**: `SbOrd.PInv` without `rd`, the S-P prefix, verbatim labels off the
exempt reads, view domination at every hart. -/
structure PInvR (N : Nat) (img : Image) (G : Gexec) (X : Geid → Prop) (dev : List Geid) (w : WS) :
    Prop where
  inv : Inv img w
  pf : pfx G X w
  ex : exOk X w
  len : ∀ x, (w.rows x).length ≤ (G.gxProg.getD x []).length
  ag : agOk N w
  dvP : ∀ d d', before dev d d' → realized w d' → realized w d
  ord : ∀ i, ((w.pend i).map Prod.fst).Pairwise (· < ·)
  fs0 : ∀ i p, p ∈ w.pend i → p.2.fs ≠ 0 → fenceSw G i p.1 (w.rows i).length
  fs2 : ∀ i p p', p ∈ w.pend i → p' ∈ w.pend i → p'.1 < p.1 → p'.2.fs ≠ p.2.fs → fenceSw G i p'.1 p.1
  nrl : ∀ i p, p ∈ w.pend i → p.2.rl = false
  spw : wrW w <+: gwrites G
  vb : ∀ (x n : Nat) (l' : Lbl), (w.rows x)[n]? = some l' → ¬ X (x, n) → gxLbl G (x, n) = some l'
  dom : ∀ x, DomInv G w x
  du : devUnitR G w

/-! # 3. S-P gives the per-byte co prefix -/

section Co

variable {img : Image} {G : Gexec} {X : Geid → Prop} {w : WS}

theorem rwrBG (hpf : pfx G X w) (hI : Inv img w) (b : Int) (e : Geid) : e ∈ w.gmo →
    rwrB w.rows b e = gwrB G b e := by
  intro he
  obtain ⟨l', hl', -⟩ := hI.gmoMem e he
  obtain ⟨l, hl, hrel⟩ := hpf.1 e.1 e.2 l' hl'
  unfold rwrB gwrB
  rw [hl', show gxLbl G e = some l from hl]
  exact wrsBEq _ l l' b hrel

theorem rwrBW (rows : Nat → List Lbl) (b : Int) (e : Geid) : rwrB rows b e = true → rwW rows e = true := by
  unfold rwrB rwW
  cases (rows e.1)[e.2]? with
  | none => simp
  | some l => exact wrsBOfWr l b

theorem gwrBW (b : Int) (e : Geid) : gwrB G b e = true → gisW G e = true := by
  unfold gwrB gisW
  cases gxLbl G e with
  | none => simp
  | some l => exact wrsBOfWr l b

theorem wrAtWOfWrW (hpf : pfx G X w) (hI : Inv img w) (b : Int) :
    wrAtW w b = (wrW w).filter (gwrB G b) := by
  unfold wrAtW wrW
  rw [List.filter_filter]
  apply List.filter_congr
  intro e he
  rw [rwrBG hpf hI b e he]
  cases h : gwrB G b e
  · simp
  · simp [rwrBW w.rows b e (by rw [rwrBG hpf hI b e he]; exact h)]

theorem wrAtGOfGw (b : Int) : wrAtG G b = (gwrites G).filter (gwrB G b) := by
  unfold wrAtG gwrites
  rw [List.filter_filter]
  apply List.filter_congr
  intro e _
  cases h : gwrB G b e
  · simp
  · simp [gwrBW b e h]

/-- **S-P GIVES THE PER-BYTE CO PREFIX**: GF's next write `s`, if it writes `b`, lands on top of `b`'s
GF co prefix. -/
theorem coPfx (hpf : pfx G X w) (hI : Inv img w) (s : Geid) (b : Int) :
    wrW w ++ [s] <+: gwrites G → gwrB G b s = true → wrAtW w b ++ [s] <+: wrAtG G b := by
  intro hS hb
  rw [wrAtWOfWrW hpf hI b, wrAtGOfGw b]
  have := hS.filter (gwrB G b)
  rw [List.filter_append] at this
  simpa [hb] using this

end Co

/-! # 4. The items keep `PInvR` -/

section Sound

variable {N : Nat} {img : Image} {G : Gexec} {X : Geid → Prop} {dev : List Geid} {w : WS}

theorem pendLblR (hP : PInvR N img G X dev w) (i : Nat) (p : Nat × SbEnt) : p ∈ w.pend i →
    ∃ rl base vs kc, gxLbl G (i, p.1) = some (LStore rl base vs kc) ∧
      (w.rows i)[p.1]? = some (LStore rl base vs kc) ∧ p.2.msg = ⟨base, vs, some i, kc⟩ :=
  pendLblI hP.inv hP.pf i p

theorem pendRealizedR (hP : PInvR N img G X dev w) (i : Nat) (p : Nat × SbEnt) : p ∈ w.pend i →
    realized w (i, p.1) := by
  intro hp
  obtain ⟨_, _, _, _, _, hrow, _⟩ := pendLblR hP i p hp
  exact lookup_lt_Some hrow

/-- **AN ENABLED S-R LANDING KEEPS THE WALK INVARIANT.** -/
theorem pinvLandR (hc : CatH G) (pol : SbPol) (hP : PInvR N img G X dev w) (i k : Nat)
    (hq : SbOrd.devQuiet w ∨ NCPU ≤ i) (hg : landR pol G w i k) : PInvR N img G X dev (nextI w (.land i k)) := by
  obtain ⟨p, hp, hok, hS⟩ := hg
  have hpm : p ∈ w.pend i := List.mem_of_getElem? hp
  obtain ⟨rl, base, vs, kc, hl, hrow, -⟩ := pendLblR hP i p hpm
  have hrows : (nextI w (.land i k)).rows = w.rows := by rw [landEq i k p hp]
  refine ⟨invLand img pol w i k hP.inv hok, ?_, exOkLand X w i k hP.ex, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    pfxWLand img G w i k p hP.inv hp hS, ?_, fun x => ?_, ?_⟩
  · refine pfxLand img pol G X w i k hP.inv hP.pf hok (fun p' hp' b hb => ?_)
    rw [hp, Option.some.injEq] at hp'
    subst hp'
    refine coPfx hP.pf hP.inv _ b hS ?_
    unfold rwrB at hb; rw [hrow] at hb
    unfold gwrB; rw [hl]; exact hb
  · intro x; rw [hrows]; exact hP.len x
  · intro x hx; rw [hrows] at hx; exact hP.ag x hx
  · intro d d' hb hd'
    rw [realizedLand i k p hp] at hd' ⊢
    exact hP.dvP d d' hb hd'
  · intro j; exact pendLandOrd i k p hp j (hP.ord j)
  · intro j q hq hfs
    rw [hrows]; exact hP.fs0 j q (pendLandMem i k p hp j q hq) hfs
  · intro j q q' hq hq' hlt hfs
    exact hP.fs2 j q q' (pendLandMem i k p hp j q hq) (pendLandMem i k p hp j q' hq') hlt hfs
  · intro j q hq; exact hP.nrl j q (pendLandMem i k p hp j q hq)
  · intro x n l' hl' hX; rw [hrows] at hl'; exact hP.vb x n l' hl' hX
  · exact domLand hc hP.inv hP.pf hP.spw i k p hp hS (fun h => by rw [hP.nrl i p hpm] at h; cases h)
      x (hP.dom x)
  · -- the device unit: a device landing empties its row; a hart landing happens at a quiet state
    intro j hj hne
    exfalso
    have hpe : ∀ j', (nextI w (.land i k)).pend j' = if j' = i then (w.pend i).eraseIdx k else w.pend j' := by
      intro j'; rw [landEq i k p hp]; show upd w.pend i _ j' = _
      by_cases h : j' = i
      · subst h; rw [updEq, if_pos rfl]
      · rw [updNe _ _ _ _ h, if_neg h]
    rw [hpe j] at hne
    rcases hq with hq | hq
    · by_cases hji : j = i
      · subst hji; rw [if_pos rfl, hq j hj] at hne; simp at hne
      · rw [if_neg hji, hq j hj] at hne; exact hne rfl
    · have hpi : w.pend i ≠ [] := fun h => by rw [h] at hp; simp at hp
      obtain ⟨h1, -, h3⟩ := hP.du i hq hpi
      by_cases hji : j = i
      · subst hji
        rw [if_pos rfl] at hne
        have hk0 : k = 0 := by have := lookup_lt_Some hp; omega
        subst hk0
        obtain ⟨q, hq'⟩ : ∃ q, w.pend j = [q] := by
          cases h : w.pend j with
          | nil => rw [h] at h1; simp at h1
          | cons q t => rw [h] at h1; simp at h1; subst h1; exact ⟨q, rfl⟩
        rw [hq'] at hne; simp at hne
      · rw [if_neg hji, h3 j hj hji] at hne; exact hne rfl

/-- A gmo event that writes is an AMO. -/
theorem gmoWRmw (l : Lbl) : (gmoEv l && lbIsW l) = true →
    ∃ aq rl base ts rvs wvs kc, l = LRmw aq rl base ts rvs wvs kc := by
  cases l <;> simp [gmoEv, isSt, lbIsW, lbIsMem, lbIsR, lbIsIo]

/-- **AN ENABLED S-R HEAD EVENT, WITH ITS ARM'S MEMBER LABEL, KEEPS THE WALK INVARIANT** — given the arm's
facts: the label related to GF's (and EQUAL to it off the exempt reads), the `SbCand` step, the fabric turn,
an AMO as GF's next write, a load's `SrBytes`, a store not `.rl`, an exempt read's exempt-value fact. -/
theorem pinvEvR (hc : CatH G) (hP : PInvR N img G X dev w) (x : Nat) (hx : x < N)
    (hcnt : (w.rows x).length < (G.gxProg.getD x []).length)
    (l lb' : Lbl) (hl : gxLbl G (hd w x) = some l) (hrel : lblRelX (X (hd w x)) l lb')
    (hst : SbCand.stepE w.σ x lb' (SbCand.nextE w.σ x lb'))
    (hfab : fabOk dev w (hd w x))
    (hvb : ¬ X (hd w x) → lb' = l)
    (hamo : ∀ aq rl base ts rvs wvs kc, l = LRmw aq rl base ts rvs wvs kc →
      lb' = l ∧ wrW w ++ [hd w x] <+: gwrites G)
    (hld : ∀ aq base ts vs ts' vs', l = LLoad aq base ts vs → lb' = LLoad aq base ts' vs' →
      SrBytes G w x aq base ts ts')
    (hnrl : ∀ rl base vs kc, lb' = LStore rl base vs kc → rl = false)
    (hex : X (hd w x) → exValL x lb') (hq : SbOrd.devQuiet w)
    (hdev : ∀ rl base vs kc, lb' = LStore rl base vs kc → NCPU ≤ x → wrW w ++ [hd w x] <+: gwrites G) :
    PInvR N img G X dev (nextI w (.ev ⟨x, lb'⟩)) := by
  have htag : ∀ q, q ∈ w.pend x → q.1 < (w.rows x).length := fun q hq => pendRealizedR hP x q hq
  have hamoW : (gmoEv lb' && lbIsW lb') = true → lb' = l ∧ wrW w ++ [hd w x] <+: gwrites G := by
    intro h
    obtain ⟨aq, rl, base, ts, rvs, wvs, kc, hlb⟩ := gmoWRmw lb' h
    subst hlb
    obtain ⟨ts0, hl0⟩ := relXRmw _ l aq rl base ts rvs wvs kc hrel
    exact hamo aq rl base ts0 rvs wvs kc hl0
  refine ⟨invEv img w ⟨x, lb'⟩ hP.inv hst, pfxEv img G X w ⟨x, lb'⟩ l hP.inv hP.pf hl hrel ?_,
    exOkEv X w ⟨x, lb'⟩ hP.ex hex, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    pfxWEv img G w ⟨x, lb'⟩ hP.inv hP.spw (fun h => (hamoW h).2), ?_, fun y => ?_, ?_⟩
  · -- the AMO's per-byte co prefix, from S-P
    intro hg b hb
    have hw : lbIsW lb' = true := wrsBOfWr lb' b hb
    obtain ⟨heq, hS⟩ := hamoW (by simp [hg, hw])
    refine coPfx hP.pf hP.inv _ b hS ?_
    show gwrB G b (hd w x) = true
    unfold gwrB; rw [hl]; rw [heq] at hb; exact hb
  · -- rows bounded
    intro j
    rw [rowsEvEq]
    by_cases hj : j = x
    · subst hj; rw [if_pos rfl, List.length_append, List.length_singleton]; exact hcnt
    · rw [if_neg hj]; exact hP.len j
  · -- agents
    intro j hj
    rw [rowsEvEq] at hj
    by_cases hjx : j = x
    · subst hjx; exact hx
    · rw [if_neg hjx] at hj; exact hP.ag j hj
  · -- fabric prefix
    intro d d' hb hd'
    rw [realizedEv] at hd' ⊢
    rcases hd' with h | h
    · exact .inl (hP.dvP d d' hb h)
    · have hin : d' ∈ dev := by obtain ⟨i, j, -, hj, -⟩ := hb; exact List.mem_of_getElem? hj
      rw [h] at hin hb
      exact .inl (hfab hin d hb)
  · -- tags in issue order
    intro j
    rw [pendEvEq]
    by_cases hj : j = x
    · subst hj
      rw [if_pos rfl]
      rcases pendECases w j lb' with ⟨rl, base, vs, k, -, hpe⟩ | ⟨pr, sr, -, hpe⟩ | hpe
      · rw [hpe, List.map_append, List.pairwise_append]
        refine ⟨hP.ord j, by simp, fun a ha b hb => ?_⟩
        simp only [List.map_cons, List.map_nil, List.mem_singleton] at hb
        obtain ⟨q, hq, rfl⟩ := List.mem_map.1 ha
        rw [hb]; exact htag q hq
      · rw [hpe, List.map_map]
        have : (Prod.fst ∘ fun p : Nat × SbEnt => (p.1, p.2.bump)) = Prod.fst := by funext p; rfl
        rw [this]; exact hP.ord j
      · rw [hpe]; exact hP.ord j
    · rw [if_neg hj]; exact hP.ord j
  · -- fs0
    intro j q hq hfs
    rw [pendEvEq] at hq
    rw [rowsEvEq]
    by_cases hj : j = x
    · subst hj
      rw [if_pos rfl] at hq
      rw [if_pos rfl, List.length_append, List.length_singleton]
      rcases pendECases w j lb' with ⟨rl, base, vs, k, -, hpe⟩ | ⟨pr, sr, hlb, hpe⟩ | hpe
      · rw [hpe] at hq
        rcases List.mem_append.1 hq with hq | hq
        · exact fenceSwMono G j _ _ _ (hP.fs0 j q hq hfs) (by omega)
        · simp only [List.mem_singleton] at hq
          subst hq; exact absurd rfl hfs
      · rw [hpe] at hq
        obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hq
        subst hlb
        refine ⟨(w.rows j).length, pr, sr, htag p hp, by omega, ?_⟩
        have := relXFence _ l pr true sr true hrel
        rw [← this]; exact hl
      · rw [hpe] at hq
        exact fenceSwMono G j _ _ _ (hP.fs0 j q hq hfs) (by omega)
    · rw [if_neg hj] at hq ⊢; exact hP.fs0 j q hq hfs
  · -- fs2
    intro j q q' hq hq' hlt hfs
    rw [pendEvEq] at hq hq'
    by_cases hj : j = x
    · subst hj
      rw [if_pos rfl] at hq hq'
      rcases pendECases w j lb' with ⟨rl, base, vs, k, -, hpe⟩ | ⟨pr, sr, -, hpe⟩ | hpe
      · rw [hpe] at hq hq'
        rcases List.mem_append.1 hq with hq | hq <;> rcases List.mem_append.1 hq' with hq' | hq'
        · exact hP.fs2 j q q' hq hq' hlt hfs
        · simp only [List.mem_singleton] at hq'; subst hq'
          have := htag q hq; simp only at hlt; omega
        · simp only [List.mem_singleton] at hq; subst hq
          have hfs' : q'.2.fs ≠ 0 := hfs
          exact hP.fs0 j q' hq' hfs'
        · simp only [List.mem_singleton] at hq hq'; subst hq hq'; exact absurd hlt (Nat.lt_irrefl _)
      · rw [hpe] at hq hq'
        obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hq
        obtain ⟨p', hp', rfl⟩ := List.mem_map.1 hq'
        exact hP.fs2 j p p' hp hp' hlt (fun h => hfs (by simp [SbEnt.bump, h]))
      · rw [hpe] at hq hq'; exact hP.fs2 j q q' hq hq' hlt hfs
    · rw [if_neg hj] at hq hq'; exact hP.fs2 j q q' hq hq' hlt hfs
  · -- no `.rl` entry
    intro j q hq
    rw [pendEvEq] at hq
    by_cases hj : j = x
    · subst hj
      rw [if_pos rfl] at hq
      rcases pendECases w j lb' with ⟨rl, base, vs, k, hlb, hpe⟩ | ⟨pr, sr, -, hpe⟩ | hpe
      · rw [hpe] at hq
        rcases List.mem_append.1 hq with hq | hq
        · exact hP.nrl j q hq
        · simp only [List.mem_singleton] at hq
          subst hq
          exact hnrl rl base vs k hlb
      · rw [hpe] at hq
        obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hq
        exact hP.nrl j p hp
      · rw [hpe] at hq; exact hP.nrl j q hq
    · rw [if_neg hj] at hq; exact hP.nrl j q hq
  · -- verbatim labels off the exempt reads
    intro j n l' hl' hX
    rcases rowsEvInv w ⟨x, lb'⟩ j n l' hl' with h | ⟨rfl, rfl, rfl⟩
    · exact hP.vb j n l' h hX
    · rw [hvb hX]; exact hl
  · exact domEv hc hP.inv hP.spw ⟨x, lb'⟩ l hl hrel hamo hld y (hP.dom y)
  · -- the device unit: only a device store's issue makes a device row non-empty (from a quiet state)
    intro j hj hne
    rw [pendEvEq] at hne
    have hothers : ∀ j', NCPU ≤ j' → j' ≠ x → (nextI w (.ev ⟨x, lb'⟩)).pend j' = [] := by
      intro j' hj' hne'; rw [pendEvEq, if_neg hne']; exact hq j' hj'
    by_cases hjx : j = x
    · subst hjx
      rw [if_pos rfl] at hne
      rcases pendECases w j lb' with ⟨rl, base, vs, kc, hlb, hpe⟩ | ⟨pr, sr, -, hpe⟩ | hpe
      · rw [hq j hj, List.nil_append] at hpe
        have hpe' : (nextI w (.ev ⟨j, lb'⟩)).pend j = [((w.rows j).length, SbCand.issueEnt w.σ j rl base vs kc)] := by
          rw [pendEvEq, if_pos rfl]; exact hpe
        have hst' : SbCand.stepE w.σ j lb' (SbCand.nextE w.σ j lb') := hst
        have hI' := invEv img w ⟨j, lb'⟩ hP.inv hst'
        refine ⟨by rw [hpe']; rfl, ⟨((w.rows j).length, SbCand.issueEnt w.σ j rl base vs kc), by rw [hpe']; rfl, ?_, ?_⟩, hothers⟩
        · rw [hI'.sb j, hpe']; exact SbPol.epoch.oldest _ []
        · rw [wrWEv hP.inv ⟨j, lb'⟩]
          subst hlb
          simp only [gmoEv, isSt, Bool.not_true, Bool.and_false, Bool.false_and, Bool.false_eq_true,
            if_false, List.append_nil]
          exact hdev rl base vs kc rfl hj
      · rw [hpe, hq j hj] at hne; exact absurd rfl hne
      · rw [hpe, hq j hj] at hne; exact absurd rfl hne
    · rw [if_neg hjx, hq j hj] at hne; exact absurd rfl hne

/-- The empty walk. -/
theorem pinvInitR (N : Nat) (img : Image) (G : Gexec) (hwf : gwf G) (X : Geid → Prop) (dev : List Geid) :
    PInvR N img G X dev (init img) where
  inv := invInit img
  pf := pfxInit G X img
  ex := exOkInit X img
  len _ := by simp [init]
  ag _ h := absurd rfl h
  dvP _ _ _ h := by simp [realized, init] at h
  ord _ := List.Pairwise.nil
  fs0 _ _ h := by simp [init] at h
  fs2 _ _ _ h := by simp [init] at h
  nrl _ _ h := by simp [init] at h
  spw := by simp [wrW, init]
  vb _ _ _ h := by simp [init] at h
  dom x := domInit G hwf img x
  du _ _ h := absurd rfl h

end Sound

end SbOrdR

end Weak
