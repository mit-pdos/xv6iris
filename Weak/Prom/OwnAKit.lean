/-
Weak/Prom: **track (a), the litmus kit over `wpA`** (stage S4a; plan rev 7 §3 "Invariants and points-to … opened per
hart step along the chosen schedule"; §2 "Leaf rules").

The same instruction-level rules as the core's kit (CoreKit.lean: memory entries `memEv`, `wrOk`, `ΨK`), proved from
the ONE lifting lemma `wpA_lift`, with what track (a) adds:
* every label step's continuation runs under `|={⊤}=>` with `£ 1` and the FRONTIER RULE of its pre-state (`frontA`),
  so the client may open invariants at the step (deposit slots, points-to transfers);
* a FULFIL must hand back `shot g ts` (the deposit is forced, OwnAWp.lean);
* every obligation may instead be discharged by doom (`dshot g`).
The kit resource `lhA g π w Q ws P ev` is `hartA` with some trace whose memory entries are `ev`, `wrOk`, and the
guarded `⟦V⟧⌜Q ev⌝` or doom.
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.OwnAAdeq

namespace Weak.Prom.OA

open MachCSL MachCSL.Stdpp Iris.Std
open Weak (Image Dsrc)
open Weak.Prom Weak.Prom.PF Weak.Prom.Mach Weak.Prom.Mach.Cert
open Weak.Prom.Ref (Instr Test two64 aluOp brEval amoOp sext byteList bytesVal)
open PLabel
open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode

instance : Inhabited LP := ⟨⟨[], 0, [], []⟩⟩

variable {V : Type} {hlc : HasLC} {GF : BundledGFunctors} [GhostVarG GF HSt] [GhostVarG GF Bool] [InvGS_gen hlc GF]

/-- The kit resource of track (a). -/
abbrev lhA (g : AGN) (π : Proto) (w : HW LP Unit V) (Q : Trace → Prop) (ws : PState) (pr : GSet Nat) (ev : Trace) :
    IProp GF :=
  iprop(∃ τ, hartA g w.h ws pr τ ∗ ⌜memEv τ = ev ∧ wrOk w.M τ⌝ ∗ (⌜∃ V, grd π w.img w.M V (Q ev)⌝ ∨ dshot g))

/-- The kit wp of track (a): `wpA` with the trace invariants `ΨK`. -/
abbrev wpKA (g : AGN) (π : Proto) (w : HW LP Unit V) (Qs : Nat → Trace → Prop) (s : LP) (Φ : V → IProp GF) :
    IProp GF :=
  wpA g π w (fun h => ΨK w.M (Qs h)) s Φ

variable {g : AGN} {π : Proto} {w : HW LP Unit V} {Qs : Nat → Trace → Prop} {Φ : V → IProp GF}

/-- From the adequacy premise's initial resources to the kit resource. -/
theorem lhA_start {P0 : GSet Nat} (hQ0 : Qs w.h []) :
    hartA (GF := GF) g w.h psInit P0 [] ⊢ lhA g π w (Qs w.h) psInit P0 [] := by
  iintro H
  unfold lhA
  iexists []
  iframe H
  isplitr
  · ipureintro; exact ⟨rfl, wrOk_nil _⟩
  · ileft; ipureintro; exact ⟨0, grd_intro hQ0⟩

/-- ANY STEP (no value): the lifting lemma without the value branch. -/
theorem wpA_any {s : LP} {ws : PState} {pr : GSet Nat} {τ : Trace} {Ψ : Nat → Trace → Prop}
    (hd : w.pdone s = none) :
    hartA g w.h ws pr τ ∗
    ▷ (∀ l ots s' ws' pr', ⌜anyFab w.pstep s () l s' ()⌝ -∗ ⌜memStep w.img w.M w.h pr ws l ots ws' pr'⌝ -∗
          frontA g π w.img w.M ws -∗ £ 1 -∗
          |={⊤}=> (⌜stepOk π w.img w.M (Ψ w.h) ws τ l ots⌝ ∨ dshot g) ∗ (∀ t, ⌜ots = some t⌝ → shot g t) ∗
            (hartA g w.h ws' pr' (τ ++ [(l, ots)]) -∗ wpA g π w Ψ s' Φ))
    ⊢ wpA g π w Ψ s Φ := by
  iintro ⟨Hst, Hk⟩
  iapply wpA_lift
  iframe Hst
  inext
  isplit
  · iintro %v %hv
    rw [hd] at hv; cases hv
  · iintro %l %ots %s' %ws' %pr' %hp %hm _ Hf Hc
    iapply Hk $$ %l %ots %s' %ws' %pr' %hp %hm Hf Hc

/-- ONE QUIET LABEL, with a fupd at the step (frontier of the pre-state, `£ 1`). -/
theorem wpKA_q1 {s k : LP} {ws ws1 : PState} {pr : GSet Nat} {ev : Trace} {l0 : PLabel} (hq : quietL l0 = true)
    (hd : w.pdone s = none) (hl : ∀ l s', anyFab w.pstep s () l s' () → l = l0 ∧ s' = k)
    (hpost : qPost ws l0 = ws1) :
    lhA g π w (Qs w.h) ws pr ev ∗
    ▷ (frontA g π w.img w.M ws -∗ £ 1 -∗ |={⊤}=> (lhA g π w (Qs w.h) ws1 pr ev -∗ wpKA g π w Qs k Φ))
    ⊢ wpKA g π w Qs s Φ := by
  subst hpost
  iintro ⟨⟨%τ, Hst, %hinv, Hq⟩, Hk⟩
  iapply wpA_any hd
  iframe Hst
  inext
  iintro %l %ots %s' %ws' %pr' %hp %hm Hf Hc
  obtain ⟨hl0, hk0⟩ := hl l s' hp
  subst hl0 hk0
  obtain ⟨rfl, rfl, rfl⟩ := quiet_inv hq hm
  obtain ⟨he, hw⟩ := hinv
  imod Hk $$ Hf Hc with Hk
  imodintro
  icases Hq with (%hQ | #Hd)
  · obtain ⟨V', hg⟩ := hQ
    isplitr
    · ileft; ipureintro
      refine ⟨⟨V', fun hv => ⟨by rw [memEv_quiet _ _ hq, he]; exact hg hv, wrOk_snoc_none hw⟩⟩, fun t ht => by cases ht⟩
    isplitr
    · iintro %t %ht; cases ht
    · iintro Hst
      iapply Hk
      unfold lhA
      iexists τ ++ [(l, none)]
      iframe Hst
      isplitr
      · ipureintro; exact ⟨by rw [memEv_quiet _ _ hq, he], wrOk_snoc_none hw⟩
      · ileft; ipureintro; exact ⟨V', hg⟩
  · isplitr
    · iright; iexact Hd
    isplitr
    · iintro %t %ht; cases ht
    · iintro Hst
      iapply Hk
      unfold lhA
      iexists τ ++ [(l, none)]
      iframe Hst
      isplitr
      · ipureintro; exact ⟨by rw [memEv_quiet _ _ hq, he], wrOk_snoc_none hw⟩
      · iright; iexact Hd

/-- A QUEUE OF QUIET LABELS, drained; the LAST one's step has the fupd (frontier of its pre-state, `£ 1`). -/
theorem wpKA_drain (hw : LitW w) {pr : GSet Nat} {ev : Trace} :
    ∀ (labs : List PLabel) (l0 : PLabel) (s k : LP) (ws : PState), (∀ l ∈ l0 :: labs, quietL l = true) →
      s.q = l0 :: labs → k = { s with q := [] } →
      lhA g π w (Qs w.h) ws pr ev ∗
      ▷ (frontA g π w.img w.M (qPosts ws (l0 :: labs).dropLast) -∗
          £ 1 -∗ |={⊤}=> (lhA g π w (Qs w.h) (qPosts ws (l0 :: labs)) pr ev -∗ wpKA g π w Qs k Φ))
      ⊢ wpKA g π w Qs s Φ := by
  intro labs
  induction labs with
  | nil =>
    intro l0 s k ws hql hs hk
    subst hk
    simp only [List.dropLast, qPosts]
    iintro ⟨Hl, Hk⟩
    iapply (wpKA_q1 (k := { s with q := [] }) (ws1 := qPost ws l0) (hql l0 (List.mem_cons_self ..))
      (hw.2 s (.inl (by rw [hs]; simp)))
      (fun l s' hp => litNext_q hs (((hw.1 s (by rw [hs]; simp)) l s').1 hp)) rfl)
    iframe Hl
    inext
    iintro Hf Hc
    imod Hk $$ Hf Hc with Hk
    imodintro
    iexact Hk
  | cons l1 r ih =>
    intro l0 s k ws hql hs hk
    iintro ⟨Hl, Hk⟩
    iapply (wpKA_q1 (k := { s with q := l1 :: r }) (ws1 := qPost ws l0) (hql l0 (List.mem_cons_self ..))
      (hw.2 s (.inl (by rw [hs]; simp)))
      (fun l s' hp => litNext_q hs (((hw.1 s (by rw [hs]; simp)) l s').1 hp)) rfl)
    iframe Hl
    inext
    iintro _ _
    imodintro
    iintro Hl
    iapply (ih l1 { s with q := l1 :: r } k (qPost ws l0) (fun l hl => hql l (List.mem_cons_of_mem _ hl)) rfl
      (by rw [hk]))
    iframe Hl
    inext
    have e1 : qPosts (qPost ws l0) (l1 :: r).dropLast = qPosts ws (l0 :: l1 :: r).dropLast := by
      simp [List.dropLast]
    have e2 : qPosts (qPost ws l0) (l1 :: r) = qPosts ws (l0 :: l1 :: r) := rfl
    rw [e1, e2]
    iexact Hk


/-- A non-empty queue of quiet labels, drained (`wpKA_drain` for any non-empty list). -/
theorem wpKA_drainA (hw : LitW w) {pr : GSet Nat} {ev : Trace} (labs : List PLabel) (s k : LP) (ws : PState)
    (hne : labs ≠ []) (hql : ∀ l ∈ labs, quietL l = true) (hs : s.q = labs) (hk : k = { s with q := [] }) :
    lhA g π w (Qs w.h) ws pr ev ∗
    ▷ (frontA g π w.img w.M (qPosts ws labs.dropLast) -∗ £ 1 -∗
        |={⊤}=> (lhA g π w (Qs w.h) (qPosts ws labs) pr ev -∗ wpKA g π w Qs k Φ))
    ⊢ wpKA g π w Qs s Φ := by
  cases labs with
  | nil => exact absurd rfl hne
  | cons l0 r => exact wpKA_drain hw r l0 s k ws hql hs hk

/-- ONE LOAD LABEL. -/
theorem wpKA_load1 {s : LP} {ws : PState} {pr : GSet Nat} {ev : Trace} {aq rl : Bool} {base : Int}
    {asrc : List Dsrc} {k : List (Nat × BitVec 8) → LP} {C : List (Nat × BitVec 8) → Prop} (hd : w.pdone s = none)
    (hl : ∀ l s', anyFab w.pstep s () l s' () → ∃ tvs, l = LLoad aq rl base tvs asrc ∧ s' = k tvs ∧ C tvs) :
    lhA g π w (Qs w.h) ws pr ev ∗
    ▷ (∀ tvs, ⌜C tvs⌝ -∗ ⌜loadOk w.img w.M ws (ldPre ws aq rl (srcsView ws asrc)) base tvs⌝ -∗
        frontA g π w.img w.M ws -∗ £ 1 -∗
        |={⊤}=> (⌜∃ V, grd π w.img w.M V (Qs w.h (ev ++ [(LLoad aq rl base tvs asrc, none)]))⌝ ∨ dshot g) ∗
          (lhA g π w (Qs w.h) (loadRun ws aq rl (srcsView ws asrc) base tvs) pr
              (ev ++ [(LLoad aq rl base tvs asrc, none)]) -∗ wpKA g π w Qs (k tvs) Φ))
    ⊢ wpKA g π w Qs s Φ := by
  iintro ⟨⟨%τ, Hst, %hinv, _⟩, Hk⟩
  obtain ⟨he, hw⟩ := hinv
  iapply wpA_any hd
  iframe Hst
  inext
  iintro %l %ots %s' %ws' %pr' %hp %hm Hf Hc
  obtain ⟨tvs, rfl, rfl, hC⟩ := hl l s' hp
  cases hm with
  | load _ _ _ _ _ hlo =>
    imod Hk $$ %tvs %hC %hlo Hf Hc with ⟨#Hr, Hk⟩
    imodintro
    isplitr
    · icases Hr with (%hQ | #Hd)
      · obtain ⟨V', hg⟩ := hQ
        ileft; ipureintro
        exact ⟨⟨V', fun hv => ⟨by rw [memEv_snoc _ _ rfl, he]; exact hg hv, wrOk_snoc_none hw⟩⟩,
          fun t ht => by cases ht⟩
      · iright; iexact Hd
    isplitr
    · iintro %t %ht; cases ht
    · iintro Hst
      iapply Hk
      unfold lhA
      iexists τ ++ [(LLoad aq rl base tvs asrc, none)]
      iframe Hst Hr
      ipureintro; exact ⟨by rw [memEv_snoc _ _ rfl, he], wrOk_snoc_none hw⟩

/-- ONE STORE LABEL (FULFIL): the client hands back `shot g ts`. -/
theorem wpKA_store1 {s k : LP} {ws : PState} {pr : GSet Nat} {ev : Trace} {aq rl : Bool} {base : Int}
    {data : List (BitVec 8)} {asrc vsrc : List Dsrc} (hd : w.pdone s = none)
    (hl : ∀ l s', anyFab w.pstep s () l s' () → l = LStore aq rl base data asrc vsrc ∧ s' = k) :
    lhA g π w (Qs w.h) ws pr ev ∗
    ▷ (∀ ts, ⌜ts ∈ pr⌝ -∗ ⌜w.M[ts - 1]? = some ⟨base, data, some w.h, stClass rl⟩⌝ -∗
        ⌜cohBelow ws base data.length ts⌝ -∗
        ⌜stPreA ws aq rl (srcsView ws asrc) (srcsView ws vsrc) < ts⌝ -∗ frontA g π w.img w.M ws -∗ £ 1 -∗
        |={⊤}=> (⌜(∃ V, grd π w.img w.M V (Qs w.h (ev ++ [(LStore aq rl base data asrc vsrc, some ts)]))) ∧
              grd π w.img w.M (stPreA ws aq rl (srcsView ws asrc) (srcsView ws vsrc))
                (π.okMsg ⟨base, data, some w.h, stClass rl⟩)⌝ ∨ dshot g) ∗ shot g ts ∗
          (lhA g π w (Qs w.h) (acqPost (storeRun ws rl (srcsView ws asrc) (max (srcsView ws asrc) (srcsView ws vsrc))
              base data.length ts) aq ts) (pr \ {ts}) (ev ++ [(LStore aq rl base data asrc vsrc, some ts)]) -∗
            wpKA g π w Qs k Φ))
    ⊢ wpKA g π w Qs s Φ := by
  iintro ⟨⟨%τ, Hst, %hinv, _⟩, Hk⟩
  obtain ⟨he, hw⟩ := hinv
  iapply wpA_any hd
  iframe Hst
  inext
  iintro %l %ots %s' %ws' %pr'' %hp %hm Hf Hc
  obtain ⟨rfl, rfl⟩ := hl l s' hp
  cases hm with
  | store _ _ _ _ _ _ ts hts hmsg hcoh hext =>
    imod Hk $$ %ts %hts %hmsg %hcoh %hext Hf Hc with ⟨#Hr, #Hsh, Hk⟩
    have hw' : wrOk w.M (τ ++ [(LStore aq rl base data asrc vsrc, some ts)]) :=
      wrOk_snoc_some hw hmsg (by omega) (by cases rl <;> rfl)
    imodintro
    isplitr
    · icases Hr with (%hQ | #Hd)
      · obtain ⟨⟨V', hg⟩, hpv⟩ := hQ
        ileft; ipureintro
        refine ⟨⟨V', fun hv => ⟨by rw [memEv_snoc _ _ rfl, he]; exact hg hv, hw'⟩⟩, fun t ht m hm => ?_⟩
        cases ht
        obtain ⟨k', rfl⟩ : ∃ k', ts = k' + 1 := ⟨ts - 1, by omega⟩
        simp only [msgAt] at hm
        simp only [Nat.add_sub_cancel] at hmsg
        rw [hmsg] at hm; cases hm
        exact hpv
      · iright; iexact Hd
    isplitr
    · iintro %t %ht; cases ht; iexact Hsh
    · iintro Hst
      iapply Hk
      unfold lhA
      iexists τ ++ [(LStore aq rl base data asrc vsrc, some ts)]
      iframe Hst
      isplitr
      · ipureintro; exact ⟨by rw [memEv_snoc _ _ rfl, he], hw'⟩
      · icases Hr with (%hQ | #Hd)
        · ileft; ipureintro; exact hQ.1
        · iright; iexact Hd

/-- **LOAD instruction** `l{b,h,w,d} rd, off(rs1)`: `LLoad`, then `LRegW rd [DLdRes]` (unless `rd = x0`),
`LInstr` (the last with a fupd at its pre-state's frontier). -/
theorem wpKA_ld (hw : LitW w) {s : LP} {sz rd rs1 off : Nat} {sgn : Bool} {base : Int} {ws : PState}
    {pr : GSet Nat} {ev : Trace} (hag : LitAg w s) (hq : s.q = []) (hp : s.prog[s.pc]? = some (.load sz sgn rd rs1 off))
    (ha : aligned ((s.rd rs1 + off) % two64) sz = true) (hb : (((s.rd rs1 + off) % two64 : Nat) : Int) = base) :
    lhA g π w (Qs w.h) ws pr ev ∗
    ▷ (∀ tvs, ⌜tvs.length = sz⌝ -∗ ⌜loadOk w.img w.M ws (ldPre ws false false (srcsView ws (srcR rs1))) base tvs⌝ -∗
        frontA g π w.img w.M ws -∗ £ 1 -∗
        |={⊤}=> (⌜∃ V, grd π w.img w.M V (Qs w.h (ev ++ [(LLoad false false base tvs (srcR rs1), none)]))⌝ ∨ dshot g) ∗
          (∀ s', ⌜LPstep s s' (s.pc + 1) rd (ldVal sgn sz tvs)⌝ -∗
            frontA g π w.img w.M (qPosts (loadRun ws false false (srcsView ws (srcR rs1)) base tvs)
              (regWL rd [.DLdRes] ++ [LInstr]).dropLast) -∗ £ 1 -∗
            |={⊤}=> (lhA g π w (Qs w.h) (qPosts (loadRun ws false false (srcsView ws (srcR rs1)) base tvs)
              (regWL rd [.DLdRes] ++ [LInstr])) pr (ev ++ [(LLoad false false base tvs (srcR rs1), none)]) -∗
              wpKA g π w Qs s' Φ)))
    ⊢ wpKA g π w Qs s Φ := by
  iintro ⟨Hl, Hk⟩
  iapply (wpKA_load1
    (k := fun tvs => { s with regs := s.wr rd (ldVal sgn sz tvs), pc := s.pc + 1, q := regWL rd [.DLdRes] ++ [LInstr] })
    (C := fun tvs => tvs.length = sz) (hw.2 s (.inr (pc_lt hp)))
    (fun l s' hs => by
      obtain ⟨tvs, h1, h2, h3⟩ := litNext_load hq hp ha ((hag l s').1 hs)
      exact ⟨tvs, by rw [h1, hb], by rw [h2]; rfl, h3⟩))
  iframe Hl
  inext
  iintro %tvs %hC %hlo Hf Hc
  imod Hk $$ %tvs %hC %hlo Hf Hc with ⟨Hr, Hk⟩
  imodintro
  iframe Hr
  iintro Hl
  iapply (wpKA_drainA hw (regWL rd [.DLdRes] ++ [LInstr]) _
    { s with regs := s.wr rd (ldVal sgn sz tvs), pc := s.pc + 1, q := [] } _ (by simp)
    (quiet_regWL rd _ (by simp [quietL])) rfl rfl)
  iframe Hl
  inext
  iintro Hf Hc
  iapply Hk $$ %_ %(LPstep_wr s rd _ _) Hf Hc

/-- **STORE instruction** `s{b,h,w,d} rs2, off(rs1)`: `LStore` (FULFIL; hand back `shot`), then `LInstr`. -/
theorem wpKA_sw (hw : LitW w) {s : LP} {sz rs2 rs1 off : Nat} {base : Int} {ws : PState} {pr : GSet Nat}
    {ev : Trace} (hag : LitAg w s) (hq : s.q = []) (hp : s.prog[s.pc]? = some (.store sz rs2 rs1 off))
    (ha : aligned ((s.rd rs1 + off) % two64) sz = true) (hb : (((s.rd rs1 + off) % two64 : Nat) : Int) = base) :
    lhA g π w (Qs w.h) ws pr ev ∗
    ▷ (∀ ts, ⌜ts ∈ pr⌝ -∗ ⌜w.M[ts - 1]? = some ⟨base, toBytes (s.rd rs2) sz, some w.h, .plain⟩⌝ -∗
        ⌜cohBelow ws base (toBytes (s.rd rs2) sz).length ts⌝ -∗
        ⌜stPreA ws false false (srcsView ws (srcR rs1)) (srcsView ws (srcR rs2)) < ts⌝ -∗
        frontA g π w.img w.M ws -∗ £ 1 -∗
        |={⊤}=> (⌜(∃ V, grd π w.img w.M V
            (Qs w.h (ev ++ [(LStore false false base (toBytes (s.rd rs2) sz) (srcR rs1) (srcR rs2), some ts)]))) ∧
          grd π w.img w.M (stPreA ws false false (srcsView ws (srcR rs1)) (srcsView ws (srcR rs2)))
            (π.okMsg ⟨base, toBytes (s.rd rs2) sz, some w.h, .plain⟩)⌝ ∨ dshot g) ∗ shot g ts ∗
          (∀ s', ⌜LPstep s s' (s.pc + 1) 0 0⌝ -∗
            frontA g π w.img w.M (acqPost (storeRun ws false (srcsView ws (srcR rs1))
                (max (srcsView ws (srcR rs1)) (srcsView ws (srcR rs2))) base (toBytes (s.rd rs2) sz).length ts) false ts) -∗
            £ 1 -∗
            |={⊤}=> (lhA g π w (Qs w.h) (instrR (acqPost (storeRun ws false (srcsView ws (srcR rs1))
                (max (srcsView ws (srcR rs1)) (srcsView ws (srcR rs2))) base (toBytes (s.rd rs2) sz).length ts) false ts))
              (pr \ {ts}) (ev ++ [(LStore false false base (toBytes (s.rd rs2) sz) (srcR rs1) (srcR rs2), some ts)]) -∗
            wpKA g π w Qs s' Φ)))
    ⊢ wpKA g π w Qs s Φ := by
  iintro ⟨Hl, Hk⟩
  iapply (wpKA_store1 (k := { s with pc := s.pc + 1, q := [LInstr] }) (hw.2 s (.inr (pc_lt hp)))
    (fun l s' hs => by
      obtain ⟨h1, h2⟩ := litNext_store hq hp ha ((hag l s').1 hs)
      exact ⟨by rw [h1, hb], h2⟩))
  iframe Hl
  inext
  iintro %ts %hts %hmsg %hcoh %hext Hf Hc
  imod Hk $$ %ts %hts %hmsg %hcoh %hext Hf Hc with ⟨Hr, Hsh, Hk⟩
  imodintro
  isplitl [Hr]
  · icases Hr with (%hr | #Hd)
    · ileft; ipureintro; exact hr
    · iright; iexact Hd
  iframe Hsh
  iintro Hl
  iapply (wpKA_drainA hw [LInstr] _ { s with pc := s.pc + 1, q := [] } _ (by simp) (by simp [quietL]) rfl rfl)
  iframe Hl
  inext
  simp only [List.dropLast, qPosts, qPost]
  iintro Hf Hc
  iapply Hk $$ %_ %(LPstep_same s _) Hf Hc

/-- **FENCE instruction** `fence pred, succ`: `LFence`, then `LInstr` (with a fupd at the POST-FENCE frontier). -/
theorem wpKA_fence (hw : LitW w) {s : LP} {f : Weak.Prom.Ref.FenceSet} {ws : PState} {pr : GSet Nat} {ev : Trace}
    (hag : LitAg w s) (hq : s.q = []) (hp : s.prog[s.pc]? = some (.fence f)) :
    lhA g π w (Qs w.h) ws pr ev ∗
    ▷ (∀ s', ⌜LPstep s s' (s.pc + 1) 0 0⌝ -∗ frontA g π w.img w.M (fencePost ws f.pr f.pw f.sr f.sw) -∗ £ 1 -∗
        |={⊤}=> (lhA g π w (Qs w.h) (instrR (fencePost ws f.pr f.pw f.sr f.sw)) pr ev -∗ wpKA g π w Qs s' Φ))
    ⊢ wpKA g π w Qs s Φ := by
  iintro ⟨Hl, Hk⟩
  iapply (wpKA_q1 (k := { s with regs := s.regs, pc := s.pc + 1, q := [LInstr] })
    (l0 := LFence f.pr f.pw f.sr f.sw) (ws1 := fencePost ws f.pr f.pw f.sr f.sw) rfl (hw.2 s (.inr (pc_lt hp)))
    (fun l s' hs => litNext_fence hq hp ((hag l s').1 hs)) rfl)
  iframe Hl
  inext
  iintro _ _
  imodintro
  iintro Hl
  iapply (wpKA_drainA hw [LInstr] _ { s with pc := s.pc + 1, q := [] } _ (by simp) (by simp [quietL]) rfl rfl)
  iframe Hl
  inext
  simp only [List.dropLast, qPosts, qPost]
  iintro Hf Hc
  iapply Hk $$ %_ %(LPstep_same s _) Hf Hc

/-- **THE END** of a litmus hart: nothing queued, no instruction left. -/
theorem wpKA_end {s : LP} {ws : PState} {pr : GSet Nat} {ev : Trace} {v : V} (hag : LitAg w s) (hq : s.q = [])
    (hpc : s.prog.length ≤ s.pc) (hdv : w.pdone s = some v) :
    lhA g π w (Qs w.h) ws pr ev ∗ (|={⊤}=> Φ v) ⊢ wpKA g π w Qs s Φ := by
  iintro ⟨⟨%τ, Hst, _, _⟩, Hk⟩
  iapply wpA_lift
  iframe Hst
  inext
  isplit
  · iintro %v' %hv _
    rw [hdv] at hv; cases hv
    iexact Hk
  · iintro %l %ots %s' %ws' %pr' %hp
    exfalso
    rw [hag l s', litNext_end hq (List.getElem?_eq_none hpc)] at hp; cases hp

end Weak.Prom.OA
