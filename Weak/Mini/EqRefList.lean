/-
Weak/Mini: **E1, the finite cut's memory side** (mini plan rev 4 §2 L1: "the same pair for the finite cut against
`partExec`").  `partExec` (PfxDefs.lean) checks Ref.lean's LIST-based `rvwmoRef` on `conc T trs ν g`; MiniRef's
finite cut uses the one axiom block over gmo = the order of a list.  The bridge, inside the full reference:
`rvwmo_cut_iff` — on F's kinds (no LR/SC/AMO) and without I/O, `rvwmoRef (conc T trs ν g)` is Ref.lean's gmo
well-formedness plus `rvwmoRefInf` (PfxDefs.lean, the relation form) of the CONSTANT execution `cutI T trs ν g`
(every hart's state is its cut state; gmo = `gB g`).  Rule by rule: `rfSrc` (the filter's last element) is `rfI`
(the gmo-latest candidate) because gmo lists every memory operation once.
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Mini.EqRef
import Weak.Prom.CmpRef

namespace Weak.Mini

open Weak.Prom.Ref
open Weak.Prom.Pfx
open Weak.Prom.Cmp (getLast?_filter_max getLast?_filter_mem gB_total pos_inj writesB_store)

/-- A finite execution as a (constant) possibly-infinite one. -/
def cutI (T : Test) (trs : List SSt) (ν : Val) (g : List EvId) : IExec :=
  { T := T, st := fun h _ => trs[h]?.getD default, ν := ν, gmo := fun a b => gB g a b = true }

section B2

variable {T : Test} {trs : List SSt} {ν : Val} {g : List EvId}

theorem cutI_has (hlen : trs.length = T.harts.length) (e : EvId) :
    (cutI T trs ν g).has e ↔ e ∈ sids trs := by
  unfold IExec.has sids
  rw [mem_idsOf]
  simp only [cutI, List.getElem?_map]
  constructor
  · rintro ⟨h1, _, h2⟩
    have h1' : e.1 < trs.length := by rw [hlen]; exact h1
    exact ⟨trs[e.1].evs, by simp [List.getElem?_eq_getElem h1'], by simpa [List.getElem?_eq_getElem h1'] using h2⟩
  · rintro ⟨l, hl, hi⟩
    cases h : trs[e.1]? with
    | none => rw [h] at hl; cases hl
    | some s =>
      rw [h] at hl; simp only [Option.map_some, Option.some.injEq] at hl; subst hl
      exact ⟨by rw [← hlen]; exact (List.getElem?_eq_some_iff.1 h).1, 0, by simp [hi]⟩

theorem cutI_sev (hlen : trs.length = T.harts.length) {e : EvId} (he : e ∈ sids trs) :
    (cutI T trs ν g).sev e = sevAt trs e := by
  unfold IExec.sev
  rw [dif_pos ((cutI_has hlen e).2 he)]
  obtain ⟨l, hl, hi⟩ := (mem_idsOf _ e).1 he
  simp only [List.getElem?_map] at hl
  cases h : trs[e.1]? with
  | none => rw [h] at hl; cases hl
  | some s =>
    rw [h] at hl; simp only [Option.map_some, Option.some.injEq] at hl; subst hl
    apply Option.some.inj
    rw [← List.getElem?_eq_getElem]
    simp only [cutI, sevAt, h, Option.getD_some, Option.bind_some, List.getElem?_eq_getElem hi]

theorem cutI_ev (hlen : trs.length = T.harts.length) {e : EvId} (he : e ∈ sids trs) :
    (cutI T trs ν g).ev e = (conc T trs ν g).ev e := by
  unfold IExec.ev; rw [cutI_sev hlen he, conc_ev _ _ _ _ _ he]; rfl

theorem cutI_sk (hlen : trs.length = T.harts.length) {e : EvId} (he : e ∈ sids trs) :
    (cutI T trs ν g).sk e = sskOf trs e := by
  unfold IExec.sk; rw [cutI_ev hlen he, ← conc_sk T trs ν g]; rfl

theorem isIoI_cut (hio : T.io = []) (e : EvId) : (cutI T trs ν g).isIoI e = false := by
  simp [IExec.isIoI, cutI, hio]

theorem isIo_cut (hio : T.io = []) (e : EvId) : isIo (conc T trs ν g) e = false := isIo_nil _ hio e

section hyp

variable (hlen : trs.length = T.harts.length) (hio : T.io = [])
  (hF : ∀ e ∈ sids trs, (sskOf trs e).kind.isLrSc = false ∧ (sskOf trs e).kind.isRmwW = false)
  (hg : gmoWf (conc T trs ν g))
include hlen hio hF hg

theorem memg (e : EvId) : e ∈ g ↔ e ∈ sids trs ∧ (sskOf trs e).kind.isMem = true := by
  have := hg.2
  simp only [conc_ids, conc_skf] at this
  exact ⟨fun h => this.1 e h, fun h => this.2 e h.1 h.2⟩

theorem isMem_cut (e : EvId) : (cutI T trs ν g).isMem e ↔ e ∈ g := by
  unfold IExec.isMem
  rw [memg hlen hio hF hg, cutI_has hlen]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, by rw [← cutI_sk hlen h1]; exact h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, by rw [cutI_sk hlen h1]; exact h2⟩

theorem po_cut {a b : EvId} (ha : a ∈ sids trs) (hb : b ∈ sids trs) :
    poS (cutI T trs ν g).sk a b = poX (conc T trs ν g) a b := by
  simp only [poS, poX, cutI_sk hlen ha, cutI_sk hlen hb, conc_sk]

theorem candI_cut {r : EvId} (hr : r ∈ sids trs) (x : Nat) (w : EvId) :
    (cutI T trs ν g).candI r x w ↔ w ∈ g ∧ Weak.Prom.Cmp.cand (conc T trs ν g) r x w = true := by
  unfold IExec.candI Weak.Prom.Cmp.cand
  simp only [Bool.and_eq_true, Bool.or_eq_true, gmoBefore, conc]
  constructor
  · rintro ⟨hw, h1, h2⟩
    have hw' := (cutI_has hlen w).1 hw
    rw [cutI_ev hlen hw'] at h1
    refine ⟨(memg hlen hio hF hg w).2 ⟨hw', ?_⟩, h1, ?_⟩
    · have := writesB_store h1; rw [← conc_sk T trs ν g]; exact Kind.isMem_of_isStore _ this
    · rcases h2 with h2 | h2
      · exact .inl h2
      · rw [po_cut hlen hio hF hg hw' hr] at h2; exact .inr h2
  · rintro ⟨hw, h1, h2⟩
    have hw' := ((memg hlen hio hF hg w).1 hw).1
    refine ⟨(cutI_has hlen w).2 hw', by rw [cutI_ev hlen hw']; exact h1, ?_⟩
    rcases h2 with h2 | h2
    · exact .inl h2
    · rw [po_cut hlen hio hF hg hw' hr]; exact .inr h2

theorem rfI_cut {r : EvId} (hr : r ∈ sids trs) (x : Nat) (o : Option EvId) :
    (cutI T trs ν g).rfI r x o ↔ rfSrc (conc T trs ν g) r x = o := by
  have hnd : g.Nodup := hg.1
  have hsrc : rfSrc (conc T trs ν g) r x = (g.filter (Weak.Prom.Cmp.cand (conc T trs ν g) r x)).getLast? := rfl
  rw [hsrc]
  cases o with
  | none =>
    simp only [IExec.rfI, candI_cut hlen hio hF hg hr]
    constructor
    · intro h
      cases hl : (g.filter (Weak.Prom.Cmp.cand (conc T trs ν g) r x)).getLast? with
      | none => rfl
      | some s => exact absurd (getLast?_filter_mem _ _ _ hl) (h s)
    · intro h w ⟨hw, hc⟩
      obtain ⟨s, hs, _⟩ := getLast?_filter_max _ g hnd w hw hc
      rw [h] at hs; cases hs
  | some w =>
    simp only [IExec.rfI, candI_cut hlen hio hF hg hr]
    show ((w ∈ g ∧ _) ∧ ∀ w', (w' ∈ g ∧ _) → w' = w ∨ gB g w' w = true) ↔ _
    constructor
    · rintro ⟨⟨hw, hc⟩, hmax⟩
      obtain ⟨s, hs, hsg, hsc, hws⟩ := getLast?_filter_max _ g hnd w hw hc
      rw [hs]
      rcases hmax s ⟨hsg, hsc⟩ with h | h
      · rw [h]
      · rcases hws with h' | h'
        · rw [h']
        · obtain ⟨_, _, h3⟩ := gB_mem g s w h; omega
    · intro hl
      obtain ⟨hw, hc⟩ := getLast?_filter_mem _ _ _ hl
      refine ⟨⟨hw, hc⟩, fun w' ⟨hw', hc'⟩ => ?_⟩
      obtain ⟨s, hs, _, _, hws⟩ := getLast?_filter_max _ g hnd w' hw' hc'
      rw [hl] at hs; cases hs
      rcases hws with h | h
      · exact .inl h
      · right; simp [gB, hw', hw, h]

theorem rfI_some_cut {r : EvId} (hr : r ∈ sids trs) (x : Nat) (w : EvId) :
    (cutI T trs ν g).rfI r x (some w) ↔ (rfSrc (conc T trs ν g) r x == some w) = true := by
  rw [rfI_cut hlen hio hF hg hr, beq_iff_eq]

theorem gmoOk_cut : (cutI T trs ν g).gmoOk := by
  refine ⟨fun a b h => ?_, fun a h => ?_, fun a b c h1 h2 => gB_trans g a b c h1 h2, fun a b ha hb hne => ?_⟩
  · obtain ⟨h1, h2, _⟩ := gB_mem g a b h
    exact ⟨(isMem_cut hlen hio hF hg a).2 h1, (isMem_cut hlen hio hF hg b).2 h2⟩
  · have : gB g a a = false := by simp [gB]
    exact absurd h (by simp [cutI, this])
  · rcases gB_total g a b ((isMem_cut hlen hio hF hg a).1 ha) ((isMem_cut hlen hio hF hg b).1 hb) with h | h | h
    · exact absurd h hne
    · exact .inl h
    · exact .inr h

theorem kind_cut {e : EvId} (he : e ∈ sids trs) : ((conc T trs ν g).sk e).kind = (sskOf trs e).kind := by
  rw [conc_sk]

theorem rule2_cut {a b : EvId} (ha : a ∈ sids trs) (hb : b ∈ sids trs) :
    rule2 (conc T trs ν g) a b = true ↔ (cutI T trs ν g).rule2I a b := by
  unfold rule2 IExec.rule2I
  rw [isIoI_cut hio, isIoI_cut hio, isIo_cut hio, isIo_cut hio]
  have hsa : (cutI T trs ν g).sk a = (conc T trs ν g).sk a := by rw [cutI_sk hlen ha, conc_sk]
  have hsb : (cutI T trs ν g).sk b = (conc T trs ν g).sk b := by rw [cutI_sk hlen hb, conc_sk]
  rw [hsa, hsb, cutI_ev hlen ha, cutI_ev hlen hb]
  simp only [Bool.and_eq_true, Bool.not_false, List.any_eq_true, List.mem_range, List.all_eq_true,
    Bool.not_eq_true', bne_iff_ne, ne_eq, and_true, true_and]
  constructor
  · rintro ⟨⟨hla, hlb⟩, k, hk, ⟨ht, hm⟩, hne⟩
    refine ⟨hla, hlb, k, hk, ht, fun m hm' h1 h2 => ?_, _, _, (rfI_cut hlen hio hF hg ha _ _).2 rfl,
      (rfI_cut hlen hio hF hg hb _ _).2 rfl, hne⟩
    have hm'' := (cutI_has hlen m).1 hm'
    rw [po_cut hlen hio hF hg ha hm''] at h1; rw [po_cut hlen hio hF hg hm'' hb] at h2
    have := hm m (by rw [conc_ids]; exact hm'')
    rw [cutI_ev hlen hm'']
    simp only [Bool.and_eq_false_iff, h1, h2] at this
    simpa using this
  · rintro ⟨hla, hlb, k, hk, ht, hm, oa, ob, h1, h2, hne⟩
    refine ⟨⟨hla, hlb⟩, k, hk, ⟨ht, fun m hm' => ?_⟩, ?_⟩
    · rw [conc_ids] at hm'
      cases h1' : poX (conc T trs ν g) a m <;> cases h2' : poX (conc T trs ν g) m b <;> simp only [Bool.false_and,
        Bool.and_false, Bool.true_and]
      have := hm m ((cutI_has hlen m).2 hm') (by rw [po_cut hlen hio hF hg ha hm']; exact h1')
        (by rw [po_cut hlen hio hF hg hm' hb]; exact h2')
      rw [cutI_ev hlen hm'] at this; exact this
    · rw [(rfI_cut hlen hio hF hg ha _ _).1 h1, (rfI_cut hlen hio hF hg hb _ _).1 h2]; exact hne

theorem rule4_cut {a b : EvId} (ha : a ∈ sids trs) (hb : b ∈ sids trs) :
    rule4 (conc T trs ν g).ids (conc T trs ν g).sk (isIo (conc T trs ν g)) a b = true ↔
      (cutI T trs ν g).rule4I a b := by
  unfold rule4 IExec.rule4I
  rw [List.any_eq_true, conc_ids]
  have hio1 : isIo (conc T trs ν g) = (cutI T trs ν g).isIoI := by
    funext e; rw [isIo_cut hio, isIoI_cut hio]
  have hpred : ∀ (f : FenceSet), inPred (conc T trs ν g).sk (isIo (conc T trs ν g)) f a =
      inPred (cutI T trs ν g).sk (cutI T trs ν g).isIoI f a := by
    intro f; simp only [inPred, hio1, cutI_sk hlen ha, conc_sk]
  have hsucc : ∀ (f : FenceSet), inSucc (conc T trs ν g).sk (isIo (conc T trs ν g)) f b =
      inSucc (cutI T trs ν g).sk (cutI T trs ν g).isIoI f b := by
    intro f; simp only [inSucc, hio1, cutI_sk hlen hb, conc_sk]
  constructor
  · rintro ⟨m, hm, h⟩
    rw [conc_sk] at h
    cases hk : (sskOf trs m).kind with
    | fence f =>
      rw [hk] at h
      simp only [Bool.and_eq_true] at h
      obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
      refine ⟨m, f, (cutI_has hlen m).2 hm, by rw [cutI_sk hlen hm, hk], ?_, ?_, ?_, ?_⟩
      · rw [po_cut hlen hio hF hg ha hm]; simpa [poX, conc_skf] using h1
      · rw [po_cut hlen hio hF hg hm hb]; simpa [poX, conc_skf] using h2
      · rw [← hpred]; simpa [conc_skf] using h3
      · rw [← hsucc]; simpa [conc_skf] using h4
    | _ => rw [hk] at h; cases h
  · rintro ⟨m, f, hm, hk, h1, h2, h3, h4⟩
    have hm' := (cutI_has hlen m).1 hm
    refine ⟨m, hm', ?_⟩
    rw [cutI_sk hlen hm'] at hk
    rw [conc_sk, hk]
    simp only [Bool.and_eq_true]
    rw [po_cut hlen hio hF hg ha hm'] at h1; rw [po_cut hlen hio hF hg hm' hb] at h2
    rw [← hpred] at h3; rw [← hsucc] at h4
    exact ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩

theorem rule12_cut {a b : EvId} (ha : a ∈ sids trs) (hb : b ∈ sids trs) :
    rule12 (conc T trs ν g) a b = true ↔ (cutI T trs ν g).rule12I a b := by
  unfold rule12 IExec.rule12I
  rw [isIoI_cut hio, isIo_cut hio]
  have hsb : (cutI T trs ν g).sk b = (conc T trs ν g).sk b := by rw [cutI_sk hlen hb, conc_sk]
  rw [hsb, cutI_ev hlen hb]
  simp only [Bool.and_eq_true, Bool.not_false, List.any_eq_true, List.mem_range, Bool.or_eq_true,
    List.contains_iff_mem, true_and, and_true]
  constructor
  · rintro ⟨hl, m, hm, ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, k, hk, h5⟩
    rw [conc_ids] at hm
    have hsm : (cutI T trs ν g).sk m = (conc T trs ν g).sk m := by rw [cutI_sk hlen hm, conc_sk]
    refine ⟨hl, m, (cutI_has hlen m).2 hm, by rw [po_cut hlen hio hF hg ha hm]; exact h1,
      by rw [po_cut hlen hio hF hg hm hb]; exact h2, by rw [hsm]; exact h3, ?_, k, hk, ?_⟩
    · rw [hsm]; simpa [List.contains_iff_mem] using h4
    · exact (rfI_some_cut hlen hio hF hg hb _ _).2 h5
  · rintro ⟨hl, m, hm, h1, h2, h3, h4, k, hk, h5⟩
    have hm' := (cutI_has hlen m).1 hm
    have hsm : (cutI T trs ν g).sk m = (conc T trs ν g).sk m := by rw [cutI_sk hlen hm', conc_sk]
    rw [po_cut hlen hio hF hg ha hm'] at h1; rw [po_cut hlen hio hF hg hm' hb] at h2
    rw [hsm] at h3 h4
    refine ⟨hl, m, by rw [conc_ids]; exact hm', ⟨⟨⟨h1, h2⟩, h3⟩, by simpa [List.contains_iff_mem] using h4⟩, k, hk,
      (rfI_some_cut hlen hio hF hg hb _ _).1 h5⟩

theorem rule13_cut {a b : EvId} (ha : a ∈ sids trs) (hb : b ∈ sids trs) :
    rule13 (conc T trs ν g).ids (conc T trs ν g).sk a b = true ↔ (cutI T trs ν g).rule13I a b := by
  unfold rule13 IExec.rule13I
  rw [conc_ids, cutI_sk hlen hb, ← conc_sk T trs ν g]
  simp only [Bool.and_eq_true, List.any_eq_true, List.contains_iff_mem]
  constructor
  · rintro ⟨hs, m, hm, ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩⟩
    refine ⟨hs, m, (cutI_has hlen m).2 hm, by rw [cutI_sk hlen hm, ← conc_sk T trs ν g]; exact h1,
      by rw [po_cut hlen hio hF hg ha hm]; exact h2, by rw [po_cut hlen hio hF hg hm hb]; exact h3,
      by rw [cutI_sk hlen hm, ← conc_sk T trs ν g]; exact h4⟩
  · rintro ⟨hs, m, hm, h1, h2, h3, h4⟩
    have hm' := (cutI_has hlen m).1 hm
    rw [cutI_sk hlen hm', ← conc_sk T trs ν g] at h1 h4
    rw [po_cut hlen hio hF hg ha hm'] at h2; rw [po_cut hlen hio hF hg hm' hb] at h3
    exact ⟨hs, m, hm', ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩⟩

theorem paired_cut_false {a b : EvId} (ha : a ∈ sids trs) : ¬ (cutI T trs ν g).pairedI a b := by
  rintro ⟨h, _⟩
  have := (hF a ha).1
  rw [cutI_sk hlen ha] at h; rw [h] at this; cases this

theorem pairedS_cut_false {a b : EvId} (ha : a ∈ sids trs) :
    pairedS (conc T trs ν g).ids (conc T trs ν g).sk a b = false := by
  have := (hF a ha).1
  unfold pairedS
  rw [conc_sk]
  cases hk : (sskOf trs a).kind <;> rw [hk] at this <;> simp_all [Kind.isLrSc]

theorem ppo_cut {a b : EvId} (ha : a ∈ sids trs) (hb : b ∈ sids trs) :
    ppoB (conc T trs ν g) a b = true ↔ (cutI T trs ν g).ppoI a b := by
  unfold ppoB IExec.ppoI IExec.staticI staticRules rule8
  have hma : (cutI T trs ν g).isMem a ↔ ((conc T trs ν g).sk a).kind.isMem = true := by
    rw [isMem_cut hlen hio hF hg, memg hlen hio hF hg, conc_sk]; exact ⟨fun h => h.2, fun h => ⟨ha, h⟩⟩
  have hmb : (cutI T trs ν g).isMem b ↔ ((conc T trs ν g).sk b).kind.isMem = true := by
    rw [isMem_cut hlen hio hF hg, memg hlen hio hF hg, conc_sk]; exact ⟨fun h => h.2, fun h => ⟨hb, h⟩⟩
  have hsa : (cutI T trs ν g).sk a = (conc T trs ν g).sk a := by rw [cutI_sk hlen ha, conc_sk]
  have hsb : (cutI T trs ν g).sk b = (conc T trs ν g).sk b := by rw [cutI_sk hlen hb, conc_sk]
  have hio1 : (cutI T trs ν g).isIoI = isIo (conc T trs ν g) := by
    funext e; rw [isIo_cut hio, isIoI_cut hio]
  have h1 : rule1 (conc T trs ν g) a b = true ↔ (cutI T trs ν g).rule1I a b := by
    unfold rule1 IExec.rule1I; rw [hsb, cutI_ev hlen ha, cutI_ev hlen hb]; simp [Exec.sk]
  have h3 : rule3 (conc T trs ν g) a b = false := by
    have := (hF a ha).2; unfold rule3; rw [conc_sk, this]; rfl
  have h3' : ¬ (cutI T trs ν g).rule3I a b := by
    rintro ⟨h, _⟩; rw [hsa, conc_sk, (hF a ha).2] at h; cases h
  have h5 : rule5 (cutI T trs ν g).sk (cutI T trs ν g).isIoI a b = rule5 (conc T trs ν g).sk (isIo (conc T trs ν g)) a b := by
    simp only [rule5, sameCls, hsa, hio1]
  have h6 : rule6 (cutI T trs ν g).sk (cutI T trs ν g).isIoI a b = rule6 (conc T trs ν g).sk (isIo (conc T trs ν g)) a b := by
    simp only [rule6, sameCls, hsb, hio1]
  have h7 : rule7 (cutI T trs ν g).sk (cutI T trs ν g).isIoI a b = rule7 (conc T trs ν g).sk (isIo (conc T trs ν g)) a b := by
    simp only [rule7, sameCls, hsa, hsb, hio1]
  have h9 : rule9 (cutI T trs ν g).sk a b = rule9 (conc T trs ν g).sk a b := by simp only [rule9, hsb]
  have h10 : rule10 (cutI T trs ν g).sk a b = rule10 (conc T trs ν g).sk a b := by simp only [rule10, hsb]
  have h11 : rule11 (cutI T trs ν g).sk a b = rule11 (conc T trs ν g).sk a b := by simp only [rule11, hsb]
  rw [h5, h6, h7, h9, h10, h11, po_cut hlen hio hF hg ha hb, pairedS_cut_false hlen hio hF hg ha]
  simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.or_false, h3, poX]
  rw [hma, hmb, h1, rule2_cut hlen hio hF hg ha hb, rule4_cut hlen hio hF hg ha hb, rule12_cut hlen hio hF hg ha hb,
    rule13_cut hlen hio hF hg ha hb]
  simp only [iff_false_intro h3', iff_false_intro (paired_cut_false hlen hio hF hg ha (b := b)), false_or,
    or_assoc, and_assoc]

/-- **The finite reference is the relation form of the constant execution** (F kinds, no I/O, gmo well formed). -/
theorem refCore_cut : rvwmoRef (conc T trs ν g) ↔ (cutI T trs ν g).rvwmoRefInf := by
  unfold rvwmoRef refCore IExec.rvwmoRefInf
  have hids : ∀ e, e ∈ (conc T trs ν g).ids ↔ (cutI T trs ν g).has e := by
    intro e; rw [conc_ids, cutI_has hlen]
  have hev : ∀ e, (cutI T trs ν g).has e → (cutI T trs ν g).ev e = (conc T trs ν g).ev e :=
    fun e he => cutI_ev hlen ((cutI_has hlen e).1 he)
  have hsk : ∀ e, (cutI T trs ν g).has e → (cutI T trs ν g).sk e = (conc T trs ν g).sk e :=
    fun e he => by unfold IExec.sk; rw [hev e he]; rfl
  have hev' : evWf (conc T trs ν g) ↔ (cutI T trs ν g).evWfI := by
    unfold evWf IExec.evWfI
    constructor
    · intro h e he; rw [hsk e he, hev e he]; exact h e ((hids e).2 he)
    · intro h e he; have := h e ((hids e).1 he); rwa [hsk e ((hids e).1 he), hev e ((hids e).1 he)] at this
  have hppo : ppoAx (conc T trs ν g) ↔ (cutI T trs ν g).ppoAxI := by
    unfold ppoAx IExec.ppoAxI
    have hioB : ∀ a b, ioOrdB (conc T trs ν g) a b = false := by
      intro a b; simp [ioOrdB, regionOf, conc, hio]
    have hioI : ∀ a b, ¬ (cutI T trs ν g).ioOrdI a b := by
      intro a b ⟨_, _, _, h⟩; simp [IExec.regionOfI, cutI, hio] at h
    constructor
    · intro h a b hab
      rcases hab with hab | hab
      · have ha := (cutI_has hlen a).1 hab.1.1
        have hb := (cutI_has hlen b).1 hab.2.1.1
        have := h a (by rw [conc_ids]; exact ha) b (by rw [conc_ids]; exact hb)
          (by simp [orderedB, (ppo_cut hlen hio hF hg ha hb).2 hab])
        exact this
      · exact absurd hab (hioI a b)
    · intro h a ha b hb hab
      rw [conc_ids] at ha hb
      simp only [orderedB, hioB, Bool.or_false] at hab
      exact h a b (.inl ((ppo_cut hlen hio hF hg ha hb).1 hab))
  have hlv : loadValueAx (conc T trs ν g) ↔ (cutI T trs ν g).loadValueAxI := by
    unfold loadValueAx IExec.loadValueAxI
    have hval : ∀ r x, r ∈ sids trs → (cutI T trs ν g).valI x (rfSrc (conc T trs ν g) r x) =
        lvVal (conc T trs ν g) r x := by
      intro r x hr
      unfold lvVal IExec.valI
      cases hs : rfSrc (conc T trs ν g) r x with
      | none => rfl
      | some w =>
        have hw := ((memg hlen hio hF hg w).1 (getLast?_filter_mem _ _ _ hs).1).1
        simp only; rw [cutI_ev hlen hw]
    constructor
    · intro h r hr hl hi k hk
      have hr' := (cutI_has hlen r).1 hr
      rw [hsk r hr] at hl hk; rw [hev r hr]
      exact ⟨_, (rfI_cut hlen hio hF hg hr' _ _).2 rfl, by
        rw [hval r _ hr']; exact h r (by rw [conc_ids]; exact hr') hl (isIo_cut hio r) k hk⟩
    · intro h r hr hl _ k hk
      rw [conc_ids] at hr
      have hr' := (cutI_has (ν := ν) (g := g) hlen r).2 hr
      obtain ⟨o, ho, hv⟩ := h r hr' (by rw [hsk r hr']; exact hl) (isIoI_cut hio r) k (by rw [hsk r hr']; exact hk)
      rw [hev r hr'] at ho hv
      rw [← (rfI_cut hlen hio hF hg hr _ _).1 ho, hval r _ hr] at hv
      exact hv
  have hat : atomicityAx (conc T trs ν g) ∧ (cutI T trs ν g).atomicityAxI := by
    refine ⟨fun r hr w _ hp => ?_, fun r w hr _ hp => ?_⟩
    · rw [conc_ids] at hr; rw [pairedS_cut_false hlen hio hF hg hr] at hp; cases hp
    · exact absurd hp (paired_cut_false hlen hio hF hg ((cutI_has hlen r).1 hr))
  have hsc : scAx (conc T trs ν g) ∧ (cutI T trs ν g).scAxI := by
    refine ⟨fun w hw hk => ?_, fun w hw hk => ?_⟩
    · rw [conc_ids] at hw
      have := (hF w hw).1; rw [conc_sk] at hk; rw [hk] at this; cases this
    · have hw' := (cutI_has hlen w).1 hw
      have := (hF w hw').1; rw [cutI_sk hlen hw'] at hk; rw [hk] at this; cases this
  have hpr : (cutI T trs ν g).progressAxI := by
    intro e he
    have := progressFin (conc T trs ν g) e ((isMem_cut hlen hio hF hg e).1 he)
    exact this
  constructor
  · rintro ⟨⟨_, h2, h3, h4, _, _⟩, _⟩
    exact ⟨gmoOk_cut hlen hio hF hg, hev'.1 h2, hppo.1 h3, hlv.1 h4, hat.2, hsc.2, hpr⟩
  · rintro ⟨_, h2, h3, h4, _, _, _⟩
    exact ⟨⟨hg, hev'.2 h2, hppo.2 h3, hlv.2 h4, hat.1, hsc.1⟩, progressFin _⟩

end hyp

end B2

end Weak.Mini
