/-
Weak/Prom: **the leaf rules of the ownership-free core and their view facts** (stage S2; plan rev 7 §2 "Leaf
rules", (X4)–(X6), "Forwarded reads" `fwdMono`).

Every rule is an iProp lemma over the hart's EXACT state (`hartSt γ ws P τ`), proved from the one lifting lemma
`wpH_lift` (CoreWp.lean), and appends the step's entry to the trace τ.  A rule applies at a program state `s` whose
program half emits only labels of the rule's form: the premise `hl` says every step of `s` emits such a label and
moves to the continuation `k` (the abstract-`pstep` form of "the instruction is a load", plan §2: "At every step the
wp knows the label the step emits").  The client then proves, for every admissible answer / fulfil timestamp, the
step's guarded trace obligation `∃ V, ⟦V⟧⌜Ψ τ′⌝` and continues from the new `hartSt`.

* LOAD (`wpH_load`): every `tvs` with `loadOk … (ldPre …)` (v2's admissibility, M9's single read point); each byte
  comes with `memByte img M t_j a = some v_j` (the M-fact, or the image at `t_j = 0`) and its protocol fact
  `⟦t_j⟧ proto(M[t_j])` holds outright (`grd_self`).  View fact (X4): `loadRun_ldv` — the post-state's `wLdv` is at
  least every byte's forward view, which is `t_j` for a non-forwarded byte (`fwdView_of_not`).
* REGW (`wpH_regw`): (X5) `regv_regW` — `regv ws′ rd = srcsView ws srcs` (an assignment); INSTR (`wpH_instr`)
  keeps every register view (`regv_instr`).
* FULFIL (`wpH_store`): for every `t ∈ P` with `M[t] = (base, data, h, cls)`, COH and EXT, the client proves
  `⟦pv⟧ proto(data)` at `pv = stPreA ws aq rl va vd`, which records `protoOk t`.  (X6) `store_ext`: `vd ≤ pv < t`.
* CTRL, FENCE: `wpH_ctrl`, `wpH_fence`.  The other arms (RMW, LR, SC, AMO halves, FENCE.I, fetch, CMO, device)
  follow the same pattern; `wpH_any` is the general rule (the lifting lemma without the value branch), with
  `memStep` inversion done by the client.
* Termination: `wpH_done`.
* FORWARDED READS (plan §2 [R1.5]): `wpH_load_fwd` hands the client the forward-bank knowledge FK of the
  state interpretation (CoreFwd.lean); `fwdRead` extracts, for a byte forwarded from own store `t_f`, the knowledge
  recorded at that store's fulfil at its own index, `⟦pv_f⟧ proto(M[t_f])` with `pv_f < t_f` and
  `pv_f ≤ v_f ⊔ plainFloor` (plain and exclusive stores) — not at the smaller forward view.  `fwdMono_bound` and
  `fwdMono` (the plan's lemma, exact pre-view form; `floors_mono` in CoreFwd.lean) show `⟦pv_f⟧` is dischargeable at
  every later fulfil whose address or data view covers the forward view (label-level programs: no fetch view).
  Release/acquire stores (Zalasr, present in v2) are the stated exception: their pre-view also contains
  `vrOld ⊔ vwOld` / `vRel`, which a later plain store need not cover.
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.CoreWp

namespace Weak.Prom.PF

open MachCSL MachCSL.Stdpp Iris.Std
open Weak (Image Dsrc)
open Weak.Prom
open PLabel
open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode

variable {P D V : Type}

/-! ## 1. View facts (pure) -/

/-- The forward view of a non-forwarded answer is the answer's timestamp. -/
theorem fwdView_of_not {ws : PState} {aq : Bool} {a : Int} {t : Nat} (h : fwdHit ws a t = false) :
    fwdView ws aq a t = t := by
  unfold fwdView
  unfold fwdHit at h
  split
  · next tf vf he => rw [he] at h; simp only [beq_eq_false_iff_ne] at h; simp [h]
  · rfl

/-- With an empty forward bank no answer is forwarded. -/
theorem fwdHit_empty {ws : PState} {a : Int} {t : Nat} (h : get? ws.wFwd a = none) : fwdHit ws a t = false := by
  unfold fwdHit; rw [h]

theorem loadBytes_ldv' (aq : Bool) (vpre : Nat) : ∀ (ws : PState) (a : Int) (tvs : List (Nat × BitVec 8)),
    ws.wLdv ≤ (loadBytes aq vpre ws a tvs).wLdv ∧
      bytesAll (fun x u _ => fwdView ws aq x u ≤ (loadBytes aq vpre ws a tvs).wLdv) a tvs
  | _, _, [] => ⟨Nat.le_refl _, trivial⟩
  | ws, a, (t, _) :: r => by
    have ih := loadBytes_ldv' aq vpre (loadByte ws aq vpre a t) (a + 1) r
    have hf : (loadByte ws aq vpre a t).wFwd = ws.wFwd := rfl
    have e1 : (loadByte ws aq vpre a t).wLdv = max ws.wLdv (max vpre (fwdView ws aq a t)) := rfl
    have hfv : ∀ x u, fwdView (loadByte ws aq vpre a t) aq x u = fwdView ws aq x u := by
      intro x u; unfold fwdView; rw [hf]
    simp only [loadBytes]
    refine ⟨by omega, by omega, ?_⟩
    have := ih.2
    exact bytesAll_mono (fun x u v h => by rw [hfv] at h; exact h) _ _ this

/-- **(X4)** (plan §2 LOAD): after a load, `wLdv` is at least every byte's forward view; for a non-forwarded byte
that is its source timestamp. -/
theorem loadRun_ldv (ws : PState) (aq rl : Bool) (va : Nat) (base : Int) (tvs : List (Nat × BitVec 8)) :
    bytesAll (fun x u _ => fwdView ws aq x u ≤ (loadRun ws aq rl va base tvs).wLdv) base tvs :=
  (loadBytes_ldv' aq _ ws base tvs).2

/-- (X4) at byte 0, for a non-forwarded byte. -/
theorem loadRun_ldv0 {ws : PState} {aq rl : Bool} {va : Nat} {base : Int} {t : Nat} {v : BitVec 8}
    {r : List (Nat × BitVec 8)} (hnf : fwdHit ws base t = false) :
    t ≤ (loadRun ws aq rl va base ((t, v) :: r)).wLdv := by
  have h1 : fwdView ws aq base t ≤ (loadRun ws aq rl va base ((t, v) :: r)).wLdv :=
    (loadRun_ldv ws aq rl va base ((t, v) :: r)).1
  rwa [fwdView_of_not hnf] at h1

theorem loadBytes_regv (aq : Bool) (vpre : Nat) : ∀ (ws : PState) (a : Int) (tvs : List (Nat × BitVec 8)),
    (loadBytes aq vpre ws a tvs).wRegv = ws.wRegv
  | _, _, [] => rfl
  | ws, a, (t, _) :: r => by
    simp only [loadBytes]
    rw [loadBytes_regv aq vpre (loadByte ws aq vpre a t) (a + 1) r]
    rfl

/-- A load leaves the register views alone. -/
theorem loadRun_regv (ws : PState) (aq rl : Bool) (va : Nat) (base : Int) (tvs : List (Nat × BitVec 8)) (r : Nat) :
    regv (loadRun ws aq rl va base tvs) r = regv ws r := by
  unfold regv loadRun
  simp only
  rw [loadBytes_regv]

/-- **(X5)** (plan §2 REGW): a register write is an assignment of its sources' view. -/
theorem regv_regW (ws : PState) (rd : Nat) (x : Nat) : regv { ws with wRegv := insert ws.wRegv rd x } rd = x := by
  unfold regv; simp only; rw [lookupInsert]; rfl

theorem regv_regW_ne (ws : PState) {rd r : Nat} (x : Nat) (h : rd ≠ r) :
    regv { ws with wRegv := insert ws.wRegv rd x } r = regv ws r := by
  unfold regv; simp only; rw [lookupInsertNe h]

/-- (X5): `LInstr` keeps every register view (it resets `wLdv`, the AMO slot and the fetch view only). -/
theorem regv_instr (ws : PState) (r : Nat) : regv { ws with wLdv := 0, wRmw := none, wIfv := 0 } r = regv ws r := rfl

theorem srcsView_nil (ws : PState) : srcsView ws [] = 0 := rfl

theorem srcsView_cons (ws : PState) (d : Dsrc) (l : List Dsrc) :
    srcsView ws (d :: l) = max (dsrcView ws d) (srcsView ws l) := rfl

theorem srcsView_reg (ws : PState) (r : Nat) : srcsView ws [.DReg r] = regv ws r := by
  simp [srcsView, dsrcView]

theorem srcsView_ldres (ws : PState) : srcsView ws [.DLdRes] = ws.wLdv := by
  simp [srcsView, dsrcView]

/-- **(X6)** (plan §2 FULFIL): the data view is below the store's pre-view (EXT then gives `pv < t`). -/
theorem store_ext (ws : PState) (aq rl : Bool) (va vd : Nat) : max va vd ≤ stPreA ws aq rl va vd := by
  unfold stPreA stPre; omega

/-! ## 2. `fwdMono` (plan §2 "Forwarded reads") -/

/-- A plain store's pre-view, when the hart has no fetch view (label-level programs), is its forward view
`va ⊔ vd` joined with the floors. -/
theorem stPre_plain (ws : PState) (va vd : Nat) (hif : ws.wIfv = 0) :
    stPreA ws false false va vd = max (max va vd) (stFloor ws) := by
  unfold stPreA stPre stFloor; simp only [hif, Bool.false_eq_true, if_false]; omega

/-- **`fwdMono`** (plan §2 "Forwarded reads", S2 deliverable): a plain store at state `ws_f` (no fetch view) with
forward view `fv = va_f ⊔ vd_f`; at any later state `ws''` (floors at least `ws_f`'s, `floors_mono`), a fulfil whose
address or data view covers `fv` — "whose address or data sources include the forwarded register" — has a pre-view
at least the forwarding store's pre-view. -/
theorem fwdMono {wsf ws'' : PState} {vaf vdf va'' vd'' : Nat} (aq'' rl'' : Bool) (hif : wsf.wIfv = 0)
    (hfl : stFloor wsf ≤ stFloor ws'') (hcov : max vaf vdf ≤ max va'' vd'') :
    stPreA wsf false false vaf vdf ≤ stPreA ws'' aq'' rl'' va'' vd'' := by
  rw [stPre_plain wsf vaf vdf hif]
  unfold stFloor at hfl
  unfold stFloor stPreA stPre
  omega

/-- **THE FORWARDED-READ FACT** (plan §2 "Forwarded reads" [R1.5]): a byte forwarded from the hart's own store
`t` (`fwdHit`) comes with the knowledge recorded at that store's fulfil, at the store's own pre-view `pv`:
`⟦pv⟧ proto(M[t])`, with `pv < t`, and `pv` bounded by the forward view `vf` and the hart's floors (or the store was
a release/acquire store of the trace). -/
theorem fwdRead {π : Proto} {img : Image} {M : List PMsg} {ws : PState} {τ : Trace} {a : Int} {t : Nat}
    (hk : fwdKnow π img M ws τ) (hf : fwdHit ws a t = true) :
    ∃ vf pv, get? ws.wFwd a = some (t, vf) ∧ pv < t ∧ (∀ m, msgAt M t = some m → grd π img M pv (π.okMsg m)) ∧
      (pv ≤ max vf (plainFloor ws) ∨ ∃ e ∈ τ, e.2 = some t ∧ isRelAcq e.1 = true) := by
  unfold fwdHit at hf
  split at hf
  · next tf vf he =>
    simp only [beq_iff_eq] at hf
    subst hf
    obtain ⟨pv, h1, h2, h3⟩ := hk a t vf he
    exact ⟨vf, pv, he, h1, h2, h3⟩
  · cases hf

/-- **`fwdMono` for the recorded bound**: a forwarded store's knowledge index `pv ≤ vf ⊔ plainFloor ws_f` (FK, plain
case) is below the pre-view of every later fulfil whose address or data view covers the forward view `vf`, when the
hart has no fetch sources (label-level programs, `wIfr = 0`) — so `⟦pv⟧` is dischargeable where the forwarded value
feeds a write. -/
theorem fwdMono_bound {wsf ws'' : PState} {pv vf va'' vd'' : Nat} (aq'' rl'' : Bool)
    (hpv : pv ≤ max vf (plainFloor wsf)) (hfl : stFloor wsf ≤ stFloor ws'') (hifr : wsf.wIfr = 0)
    (hcov : vf ≤ max va'' vd'') : pv ≤ stPreA ws'' aq'' rl'' va'' vd'' := by
  unfold plainFloor at hpv
  unfold stFloor at hfl hpv
  unfold stPreA stPre
  omega

/-! ## 3. The leaf rules -/

section rules

variable {hlc : HasLC} {GF : BundledGFunctors} [GhostVarG GF HSt] [InvGS_gen hlc GF]
variable {γ : GName} {π : Proto} {w : HW P D V} {Ψ : Trace → Prop} {s : P} {Φ : V → IProp GF}
variable {ws : PState} {pr : GSet Nat} {τ : Trace}

/-- THE GENERAL RULE (the lifting lemma at a state that is not a value). -/
theorem wpH_any (hd : w.pdone s = none) :
    hartSt γ ws pr τ ∗
    ▷ (∀ l ots s' ws' pr', ⌜anyFab w.pstep s () l s' ()⌝ -∗ ⌜memStep w.img w.M w.h pr ws l ots ws' pr'⌝ -∗
          £ 1 -∗ |={⊤}=> ⌜stepOk π w.img w.M Ψ ws τ l ots⌝ ∗
            (hartSt γ ws' pr' (τ ++ [(l, ots)]) -∗ wpH γ π w Ψ s' Φ))
    ⊢ wpH γ π w Ψ s Φ := by
  iintro ⟨Hst, Hk⟩
  iapply wpH_lift
  iframe Hst
  inext
  isplit
  · iintro %v %hv
    rw [hd] at hv; cases hv
  · iexact Hk

/-- TERMINATION: a value state with no step proves the postcondition. -/
theorem wpH_done {v : V} (hdv : w.pdone s = some v) (hns : ∀ l s', ¬ anyFab w.pstep s () l s' ()) :
    hartSt γ ws pr τ ∗ (hartSt γ ws pr τ -∗ |={⊤}=> Φ v) ⊢ wpH γ π w Ψ s Φ := by
  iintro ⟨Hst, Hk⟩
  iapply wpH_lift
  iframe Hst
  inext
  isplit
  · iintro %v' %hv
    rw [hdv] at hv; cases hv
    iexact Hk
  · iintro %l %ots %s' %ws' %pr' %hp
    exact absurd hp (hns l s')

/-- **LOAD** (plan §2): every admissible answer `tvs` (`loadOk` at `ldPre`, v2's single read point); the
continuation `k tvs` with side condition `C tvs` (e.g. the width) from the program half. -/
theorem wpH_load {aq rl : Bool} {base : Int} {asrc : List Dsrc} {k : List (Nat × BitVec 8) → P}
    {C : List (Nat × BitVec 8) → Prop} (hd : w.pdone s = none)
    (hl : ∀ l s', anyFab w.pstep s () l s' () → ∃ tvs, l = LLoad aq rl base tvs asrc ∧ s' = k tvs ∧ C tvs)
    (hnoinv : ∀ t a, ¬ cmoAt w.M isInvalK t a := by assumption) :   -- MachFix-R-b5: `vi = 0`
    hartSt γ ws pr τ ∗
    ▷ (∀ tvs, ⌜C tvs⌝ -∗ ⌜loadOk w.img w.M ws (ldPre ws aq rl (srcsView ws asrc)) base tvs⌝ -∗ £ 1 -∗
        |={⊤}=> ⌜∃ V, grd π w.img w.M V (Ψ (τ ++ [(LLoad aq rl base tvs asrc, none)]))⌝ ∗
          (hartSt γ (loadRun ws aq rl (srcsView ws asrc) base tvs) pr (τ ++ [(LLoad aq rl base tvs asrc, none)]) -∗
            wpH γ π w Ψ (k tvs) Φ))
    ⊢ wpH γ π w Ψ s Φ := by
  iintro ⟨Hst, Hk⟩
  iapply wpH_any hd
  iframe Hst
  inext
  iintro %l %ots %s' %ws' %pr' %hp %hm Hc
  obtain ⟨tvs, rfl, rfl, hC⟩ := hl l s' hp
  cases hm with
  | load _ _ _ _ _ hlo vi hci =>
    obtain rfl := invalCite_vi0 hnoinv hci
    rw [loadRunV_zero]
    imod Hk $$ %tvs %hC %hlo Hc with ⟨%Hψ, Hk⟩
    imodintro
    isplitr
    · ipureintro; exact ⟨Hψ, fun t ht => by cases ht⟩
    · iexact Hk
/-- MachFix-R-b5: the general rule (every absorbed invalidate view `vi`, `invalCite`).  **LOAD** (plan §2): every admissible answer `tvs` (`loadOk` at `ldPre`, v2's single read point); the
continuation `k tvs` with side condition `C tvs` (e.g. the width) from the program half. -/
theorem wpH_loadV {aq rl : Bool} {base : Int} {asrc : List Dsrc} {k : List (Nat × BitVec 8) → P}
    {C : List (Nat × BitVec 8) → Prop} (hd : w.pdone s = none)
    (hl : ∀ l s', anyFab w.pstep s () l s' () → ∃ tvs, l = LLoad aq rl base tvs asrc ∧ s' = k tvs ∧ C tvs) :
    hartSt γ ws pr τ ∗
    ▷ (∀ tvs vi, ⌜C tvs⌝ -∗ ⌜loadOk w.img w.M ws (ldPre ws aq rl (srcsView ws asrc)) base tvs⌝ -∗
        ⌜invalCite w.M ws (ldPre ws aq rl (srcsView ws asrc)) vi base tvs⌝ -∗ £ 1 -∗
        |={⊤}=> ⌜∃ V, grd π w.img w.M V (Ψ (τ ++ [(LLoad aq rl base tvs asrc, none)]))⌝ ∗
          (hartSt γ (loadRunV ws aq rl (srcsView ws asrc) vi base tvs) pr (τ ++ [(LLoad aq rl base tvs asrc, none)]) -∗
            wpH γ π w Ψ (k tvs) Φ))
    ⊢ wpH γ π w Ψ s Φ := by
  iintro ⟨Hst, Hk⟩
  iapply wpH_any hd
  iframe Hst
  inext
  iintro %l %ots %s' %ws' %pr' %hp %hm Hc
  obtain ⟨tvs, rfl, rfl, hC⟩ := hl l s' hp
  cases hm with
  | load _ _ _ _ _ hlo vi hci =>
    imod Hk $$ %tvs %vi %hC %hlo %hci Hc with ⟨%Hψ, Hk⟩
    imodintro
    isplitr
    · ipureintro; exact ⟨Hψ, fun t ht => by cases ht⟩
    · iexact Hk

/-- **LOAD with the forwarded-read rule** (plan §2 "Forwarded reads"): as `wpH_load`, and the client is also handed
the forward-bank knowledge (FK) of the pre-state, so every forwarded byte comes with `⟦pv_f⟧ proto(M[t_f])`
(`fwdRead`). -/
theorem wpH_load_fwd {aq rl : Bool} {base : Int} {asrc : List Dsrc} {k : List (Nat × BitVec 8) → P}
    {C : List (Nat × BitVec 8) → Prop} (hd : w.pdone s = none)
    (hl : ∀ l s', anyFab w.pstep s () l s' () → ∃ tvs, l = LLoad aq rl base tvs asrc ∧ s' = k tvs ∧ C tvs)
    (hnoinv : ∀ t a, ¬ cmoAt w.M isInvalK t a := by assumption) :   -- MachFix-R-b5: `vi = 0`
    hartSt γ ws pr τ ∗
    ▷ (∀ tvs, ⌜C tvs⌝ -∗ ⌜loadOk w.img w.M ws (ldPre ws aq rl (srcsView ws asrc)) base tvs⌝ -∗
        ⌜fwdKnow π w.img w.M ws τ⌝ -∗ £ 1 -∗
        |={⊤}=> ⌜∃ V, grd π w.img w.M V (Ψ (τ ++ [(LLoad aq rl base tvs asrc, none)]))⌝ ∗
          (hartSt γ (loadRun ws aq rl (srcsView ws asrc) base tvs) pr (τ ++ [(LLoad aq rl base tvs asrc, none)]) -∗
            wpH γ π w Ψ (k tvs) Φ))
    ⊢ wpH γ π w Ψ s Φ := by
  iintro ⟨Hst, Hk⟩
  iapply wpH_liftF
  iframe Hst
  inext
  isplit
  · iintro %v %hv
    rw [hd] at hv; cases hv
  iintro %l %ots %s' %ws' %pr' %hp %hm %hf Hc
  obtain ⟨tvs, rfl, rfl, hC⟩ := hl l s' hp
  cases hm with
  | load _ _ _ _ _ hlo vi hci =>
    obtain rfl := invalCite_vi0 hnoinv hci
    rw [loadRunV_zero]
    imod Hk $$ %tvs %hC %hlo %hf.2.2.2 Hc with ⟨%Hψ, Hk⟩
    imodintro
    isplitr
    · ipureintro; exact ⟨Hψ, fun t ht => by cases ht⟩
    · iexact Hk
/-- MachFix-R-b5: the general rule (every absorbed invalidate view `vi`, `invalCite`).  **LOAD with the forwarded-read rule** (plan §2 "Forwarded reads"): as `wpH_load`, and the client is also handed
the forward-bank knowledge (FK) of the pre-state, so every forwarded byte comes with `⟦pv_f⟧ proto(M[t_f])`
(`fwdRead`). -/
theorem wpH_load_fwdV {aq rl : Bool} {base : Int} {asrc : List Dsrc} {k : List (Nat × BitVec 8) → P}
    {C : List (Nat × BitVec 8) → Prop} (hd : w.pdone s = none)
    (hl : ∀ l s', anyFab w.pstep s () l s' () → ∃ tvs, l = LLoad aq rl base tvs asrc ∧ s' = k tvs ∧ C tvs) :
    hartSt γ ws pr τ ∗
    ▷ (∀ tvs vi, ⌜C tvs⌝ -∗ ⌜loadOk w.img w.M ws (ldPre ws aq rl (srcsView ws asrc)) base tvs⌝ -∗
        ⌜invalCite w.M ws (ldPre ws aq rl (srcsView ws asrc)) vi base tvs⌝ -∗
        ⌜fwdKnow π w.img w.M ws τ⌝ -∗ £ 1 -∗
        |={⊤}=> ⌜∃ V, grd π w.img w.M V (Ψ (τ ++ [(LLoad aq rl base tvs asrc, none)]))⌝ ∗
          (hartSt γ (loadRunV ws aq rl (srcsView ws asrc) vi base tvs) pr (τ ++ [(LLoad aq rl base tvs asrc, none)]) -∗
            wpH γ π w Ψ (k tvs) Φ))
    ⊢ wpH γ π w Ψ s Φ := by
  iintro ⟨Hst, Hk⟩
  iapply wpH_liftF
  iframe Hst
  inext
  isplit
  · iintro %v %hv
    rw [hd] at hv; cases hv
  iintro %l %ots %s' %ws' %pr' %hp %hm %hf Hc
  obtain ⟨tvs, rfl, rfl, hC⟩ := hl l s' hp
  cases hm with
  | load _ _ _ _ _ hlo vi hci =>
    imod Hk $$ %tvs %vi %hC %hlo %hci %hf.2.2.2 Hc with ⟨%Hψ, Hk⟩
    imodintro
    isplitr
    · ipureintro; exact ⟨Hψ, fun t ht => by cases ht⟩
    · iexact Hk

/-- **REGW** (plan §2, (X5) `regv_regW`). -/
theorem wpH_regw {rd : Nat} {srcs : List Dsrc} {k : P} (hd : w.pdone s = none)
    (hl : ∀ l s', anyFab w.pstep s () l s' () → l = LRegW rd srcs ∧ s' = k) :
    hartSt γ ws pr τ ∗
    ▷ (£ 1 -∗ |={⊤}=> ⌜∃ V, grd π w.img w.M V (Ψ (τ ++ [(LRegW rd srcs, none)]))⌝ ∗
          (hartSt γ { ws with wRegv := insert ws.wRegv rd (srcsView ws srcs) } pr (τ ++ [(LRegW rd srcs, none)]) -∗
            wpH γ π w Ψ k Φ))
    ⊢ wpH γ π w Ψ s Φ := by
  iintro ⟨Hst, Hk⟩
  iapply wpH_any hd
  iframe Hst
  inext
  iintro %l %ots %s' %ws' %pr' %hp %hm Hc
  obtain ⟨rfl, rfl⟩ := hl l s' hp
  cases hm with
  | regW =>
    imod Hk $$ Hc with ⟨%Hψ, Hk⟩
    imodintro
    isplitr
    · ipureintro; exact ⟨Hψ, fun t ht => by cases ht⟩
    · iexact Hk

/-- **INSTR** (the instruction boundary; keeps every register view, `regv_instr`). -/
theorem wpH_instr {k : P} (hd : w.pdone s = none)
    (hl : ∀ l s', anyFab w.pstep s () l s' () → l = LInstr ∧ s' = k) :
    hartSt γ ws pr τ ∗
    ▷ (£ 1 -∗ |={⊤}=> ⌜∃ V, grd π w.img w.M V (Ψ (τ ++ [(LInstr, none)]))⌝ ∗
          (hartSt γ { ws with wLdv := 0, wRmw := none, wIfv := 0 } pr (τ ++ [(LInstr, none)]) -∗
            wpH γ π w Ψ k Φ))
    ⊢ wpH γ π w Ψ s Φ := by
  iintro ⟨Hst, Hk⟩
  iapply wpH_any hd
  iframe Hst
  inext
  iintro %l %ots %s' %ws' %pr' %hp %hm Hc
  obtain ⟨rfl, rfl⟩ := hl l s' hp
  cases hm with
  | instr =>
    imod Hk $$ Hc with ⟨%Hψ, Hk⟩
    imodintro
    isplitr
    · ipureintro; exact ⟨Hψ, fun t ht => by cases ht⟩
    · iexact Hk

/-- **CTRL** (rule 11: `vcap ⊔= view(srcs)`). -/
theorem wpH_ctrl {srcs : List Dsrc} {k : P} (hd : w.pdone s = none)
    (hl : ∀ l s', anyFab w.pstep s () l s' () → l = LCtrl srcs ∧ s' = k) :
    hartSt γ ws pr τ ∗
    ▷ (£ 1 -∗ |={⊤}=> ⌜∃ V, grd π w.img w.M V (Ψ (τ ++ [(LCtrl srcs, none)]))⌝ ∗
          (hartSt γ { ws with wVcap := max (srcsView ws srcs) ws.wVcap } pr (τ ++ [(LCtrl srcs, none)]) -∗
            wpH γ π w Ψ k Φ))
    ⊢ wpH γ π w Ψ s Φ := by
  iintro ⟨Hst, Hk⟩
  iapply wpH_any hd
  iframe Hst
  inext
  iintro %l %ots %s' %ws' %pr' %hp %hm Hc
  obtain ⟨rfl, rfl⟩ := hl l s' hp
  cases hm with
  | ctrl =>
    imod Hk $$ Hc with ⟨%Hψ, Hk⟩
    imodintro
    isplitr
    · ipureintro; exact ⟨Hψ, fun t ht => by cases ht⟩
    · iexact Hk

/-- **FENCE** (rule 4: `fencePost`). -/
theorem wpH_fence {pr' pw sr sw : Bool} {k : P} (hd : w.pdone s = none)
    (hl : ∀ l s', anyFab w.pstep s () l s' () → l = LFence pr' pw sr sw ∧ s' = k) :
    hartSt γ ws pr τ ∗
    ▷ (£ 1 -∗ |={⊤}=> ⌜∃ V, grd π w.img w.M V (Ψ (τ ++ [(LFence pr' pw sr sw, none)]))⌝ ∗
          (hartSt γ (fencePost ws pr' pw sr sw) pr (τ ++ [(LFence pr' pw sr sw, none)]) -∗ wpH γ π w Ψ k Φ))
    ⊢ wpH γ π w Ψ s Φ := by
  iintro ⟨Hst, Hk⟩
  iapply wpH_any hd
  iframe Hst
  inext
  iintro %l %ots %s' %ws' %pr'' %hp %hm Hc
  obtain ⟨rfl, rfl⟩ := hl l s' hp
  cases hm with
  | fence =>
    imod Hk $$ Hc with ⟨%Hψ, Hk⟩
    imodintro
    isplitr
    · ipureintro; exact ⟨Hψ, fun t ht => by cases ht⟩
    · iexact Hk

/-- **FULFIL** (plan §2): a plain/release/acquire store fulfils any own promise `t` whose message is the label's,
under COH and EXT; the client proves `⟦pv⟧ proto(M[t])` at the store's pre-view `pv`, which records `protoOk t`
(sound by EXT `pv < t`). -/
theorem wpH_store {aq rl : Bool} {base : Int} {data : List (BitVec 8)} {asrc vsrc : List Dsrc} {k : P}
    (hd : w.pdone s = none)
    (hl : ∀ l s', anyFab w.pstep s () l s' () → l = LStore aq rl base data asrc vsrc ∧ s' = k) :
    hartSt γ ws pr τ ∗
    ▷ (∀ ts, ⌜ts ∈ pr⌝ -∗ ⌜w.M[ts - 1]? = some ⟨base, data, some w.h, stClass rl⟩⌝ -∗
        ⌜cohBelow ws base data.length ts⌝ -∗
        ⌜stPreA ws aq rl (srcsView ws asrc) (srcsView ws vsrc) < ts⌝ -∗ £ 1 -∗
        |={⊤}=> ⌜∃ V, grd π w.img w.M V (Ψ (τ ++ [(LStore aq rl base data asrc vsrc, some ts)]))⌝ ∗
          ⌜grd π w.img w.M (stPreA ws aq rl (srcsView ws asrc) (srcsView ws vsrc))
            (π.okMsg ⟨base, data, some w.h, stClass rl⟩)⌝ ∗
          (hartSt γ (acqPost (storeRun ws rl (srcsView ws asrc) (max (srcsView ws asrc) (srcsView ws vsrc)) base
              data.length ts) aq ts) (pr \ {ts}) (τ ++ [(LStore aq rl base data asrc vsrc, some ts)]) -∗
            wpH γ π w Ψ k Φ))
    ⊢ wpH γ π w Ψ s Φ := by
  iintro ⟨Hst, Hk⟩
  iapply wpH_any hd
  iframe Hst
  inext
  iintro %l %ots %s' %ws' %pr'' %hp %hm Hc
  obtain ⟨rfl, rfl⟩ := hl l s' hp
  cases hm with
  | store _ _ _ _ _ _ ts hts hmsg hcoh hext =>
    imod Hk $$ %ts %hts %hmsg %hcoh %hext Hc with ⟨%Hψ, %Hp, Hk⟩
    imodintro
    isplitr
    · ipureintro
      refine ⟨Hψ, fun t ht m hm => ?_⟩
      cases ht
      obtain ⟨k', rfl⟩ : ∃ k', ts = k' + 1 := ⟨ts - 1, by omega⟩
      simp only [msgAt] at hm
      simp only [Nat.add_sub_cancel] at hmsg
      rw [hmsg] at hm; cases hm
      exact Hp
    · iexact Hk

/-- **LR** (plan §2 "RMW / LR / SC …: the same pattern over the v2 arms"; M16): every admissible answer; the
reservation records the LR's bytes and its post-view. -/
theorem wpH_lr {aq rl : Bool} {base : Int} {asrc : List Dsrc} {k : List (Nat × BitVec 8) → P}
    {C : List (Nat × BitVec 8) → Prop} (hd : w.pdone s = none)
    (hl : ∀ l s', anyFab w.pstep s () l s' () → ∃ tvs, l = LExLoad aq rl base tvs asrc ∧ s' = k tvs ∧ C tvs)
    (hnoinv : ∀ t a, ¬ cmoAt w.M isInvalK t a := by assumption) :   -- MachFix-R-b5: `vi = 0`
    hartSt γ ws pr τ ∗
    ▷ (∀ tvs, ⌜C tvs⌝ -∗ ⌜loadOk w.img w.M ws (ldPre ws aq rl (srcsView ws asrc)) base tvs⌝ -∗ £ 1 -∗
        |={⊤}=> ⌜∃ V, grd π w.img w.M V (Ψ (τ ++ [(LExLoad aq rl base tvs asrc, none)]))⌝ ∗
          (hartSt γ { loadRun ws aq rl (srcsView ws asrc) base tvs with
              wRes := some ⟨base, tvs.map Prod.fst, readView ws aq rl (srcsView ws asrc) base tvs⟩ }
            pr (τ ++ [(LExLoad aq rl base tvs asrc, none)]) -∗ wpH γ π w Ψ (k tvs) Φ))
    ⊢ wpH γ π w Ψ s Φ := by
  iintro ⟨Hst, Hk⟩
  iapply wpH_any hd
  iframe Hst
  inext
  iintro %l %ots %s' %ws' %pr' %hp %hm Hc
  obtain ⟨tvs, rfl, rfl, hC⟩ := hl l s' hp
  cases hm with
  | lr _ _ _ _ _ hlo vi hci =>
    obtain rfl := invalCite_vi0 hnoinv hci
    rw [loadRunV_zero, readViewV_zero]
    imod Hk $$ %tvs %hC %hlo Hc with ⟨%Hψ, Hk⟩
    imodintro
    isplitr
    · ipureintro; exact ⟨Hψ, fun t ht => by cases ht⟩
    · iexact Hk
/-- MachFix-R-b5: the general rule (every absorbed invalidate view `vi`, `invalCite`).  **LR** (plan §2 "RMW / LR / SC …: the same pattern over the v2 arms"; M16): every admissible answer; the
reservation records the LR's bytes and its post-view. -/
theorem wpH_lrV {aq rl : Bool} {base : Int} {asrc : List Dsrc} {k : List (Nat × BitVec 8) → P}
    {C : List (Nat × BitVec 8) → Prop} (hd : w.pdone s = none)
    (hl : ∀ l s', anyFab w.pstep s () l s' () → ∃ tvs, l = LExLoad aq rl base tvs asrc ∧ s' = k tvs ∧ C tvs) :
    hartSt γ ws pr τ ∗
    ▷ (∀ tvs vi, ⌜C tvs⌝ -∗ ⌜loadOk w.img w.M ws (ldPre ws aq rl (srcsView ws asrc)) base tvs⌝ -∗
        ⌜invalCite w.M ws (ldPre ws aq rl (srcsView ws asrc)) vi base tvs⌝ -∗ £ 1 -∗
        |={⊤}=> ⌜∃ V, grd π w.img w.M V (Ψ (τ ++ [(LExLoad aq rl base tvs asrc, none)]))⌝ ∗
          (hartSt γ { loadRunV ws aq rl (srcsView ws asrc) vi base tvs with
              wRes := some ⟨base, tvs.map Prod.fst, readViewV ws aq rl (srcsView ws asrc) vi base tvs⟩ }
            pr (τ ++ [(LExLoad aq rl base tvs asrc, none)]) -∗ wpH γ π w Ψ (k tvs) Φ))
    ⊢ wpH γ π w Ψ s Φ := by
  iintro ⟨Hst, Hk⟩
  iapply wpH_any hd
  iframe Hst
  inext
  iintro %l %ots %s' %ws' %pr' %hp %hm Hc
  obtain ⟨tvs, rfl, rfl, hC⟩ := hl l s' hp
  cases hm with
  | lr _ _ _ _ _ hlo vi hci =>
    imod Hk $$ %tvs %vi %hC %hlo %hci Hc with ⟨%Hψ, Hk⟩
    imodintro
    isplitr
    · ipureintro; exact ⟨Hψ, fun t ht => by cases ht⟩
    · iexact Hk

/-- **SC** (plan §2, M16): the program half may emit a successful `LExStore` (continuation `kS`) or the failure
`LExFail` (continuation `kF`); the client proves both branches.  On success it fulfils `t` under the reservation,
the atomicity window, COH and EXT (`max (stPreA …) rvView < t`) and proves `⟦pv⟧ proto(data)` at that pre-view. -/
theorem wpH_sc {aq rl : Bool} {base : Int} {data : List (BitVec 8)} {asrc vsrc : List Dsrc} {kS kF : P}
    (hd : w.pdone s = none)
    (hl : ∀ l s', anyFab w.pstep s () l s' () →
      (l = LExStore aq rl base data asrc vsrc ∧ s' = kS) ∨ (l = LExFail ∧ s' = kF)) :
    hartSt γ ws pr τ ∗
    ▷ ((∀ ts R, ⌜ws.wRes = some R⌝ -∗ ⌜ts ∈ pr⌝ -∗ ⌜w.M[ts - 1]? = some ⟨base, data, some w.h, .excl⟩⌝ -∗
          ⌜exclOk w.M w.h R.rvBase R.rvTs ts⌝ -∗ ⌜∀ t ∈ R.rvTs, t < ts⌝ -∗ ⌜cohBelow ws base data.length ts⌝ -∗
          ⌜max (stPreA ws aq rl (srcsView ws asrc) (srcsView ws vsrc)) R.rvView < ts⌝ -∗ £ 1 -∗
          |={⊤}=> ⌜∃ V, grd π w.img w.M V (Ψ (τ ++ [(LExStore aq rl base data asrc vsrc, some ts)]))⌝ ∗
            ⌜grd π w.img w.M (max (stPreA ws aq rl (srcsView ws asrc) (srcsView ws vsrc)) R.rvView)
              (π.okMsg ⟨base, data, some w.h, .excl⟩)⌝ ∗
            (hartSt γ { acqPost (storeRun ws rl (srcsView ws asrc) ts base data.length ts) aq ts with
                wLdv := max (storeRun ws rl (srcsView ws asrc) ts base data.length ts).wLdv ts
                wRes := none } (pr \ {ts}) (τ ++ [(LExStore aq rl base data asrc vsrc, some ts)]) -∗
              wpH γ π w Ψ kS Φ)) ∧
       (£ 1 -∗ |={⊤}=> ⌜∃ V, grd π w.img w.M V (Ψ (τ ++ [(LExFail, none)]))⌝ ∗
          (hartSt γ { ws with wRes := none } pr (τ ++ [(LExFail, none)]) -∗ wpH γ π w Ψ kF Φ)))
    ⊢ wpH γ π w Ψ s Φ := by
  iintro ⟨Hst, Hk⟩
  iapply wpH_any hd
  iframe Hst
  inext
  iintro %l %ots %s' %ws' %pr' %hp %hm Hc
  rcases hl l s' hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · cases hm with
    | sc _ _ _ _ _ _ ts R hR hts hmsg hex hlt hcoh hext =>
      icases Hk with ⟨Hk, -⟩
      imod Hk $$ %ts %R %hR %hts %hmsg %hex %hlt %hcoh %hext Hc with ⟨%Hψ, %Hp, Hk⟩
      imodintro
      isplitr
      · ipureintro
        refine ⟨Hψ, fun t ht m hm => ?_⟩
        cases ht
        obtain ⟨k', rfl⟩ : ∃ k', ts = k' + 1 := ⟨ts - 1, by omega⟩
        simp only [msgAt] at hm
        simp only [Nat.add_sub_cancel] at hmsg
        rw [hmsg] at hm; cases hm
        simp only [fulPv, hR]
        exact Hp
      · iexact Hk
  · cases hm with
    | scFail =>
      icases Hk with ⟨-, Hk⟩
      imod Hk $$ Hc with ⟨%Hψ, Hk⟩
      imodintro
      isplitr
      · ipureintro; exact ⟨Hψ, fun t ht => by cases ht⟩
      · iexact Hk

/-- **SC-FAIL** (`LExFail` alone: the end of an SC, M16 (c1)): clears the reservation. -/
theorem wpH_exfail {k : P} (hd : w.pdone s = none)
    (hl : ∀ l s', anyFab w.pstep s () l s' () → l = LExFail ∧ s' = k) :
    hartSt γ ws pr τ ∗
    ▷ (£ 1 -∗ |={⊤}=> ⌜∃ V, grd π w.img w.M V (Ψ (τ ++ [(LExFail, none)]))⌝ ∗
          (hartSt γ { ws with wRes := none } pr (τ ++ [(LExFail, none)]) -∗ wpH γ π w Ψ k Φ))
    ⊢ wpH γ π w Ψ s Φ := by
  iintro ⟨Hst, Hk⟩
  iapply wpH_any hd
  iframe Hst
  inext
  iintro %l %ots %s' %ws' %pr' %hp %hm Hc
  obtain ⟨rfl, rfl⟩ := hl l s' hp
  cases hm with
  | scFail =>
    imod Hk $$ Hc with ⟨%Hψ, Hk⟩
    imodintro
    isplitr
    · ipureintro; exact ⟨Hψ, fun t ht => by cases ht⟩
    · iexact Hk

end rules

end Weak.Prom.PF
