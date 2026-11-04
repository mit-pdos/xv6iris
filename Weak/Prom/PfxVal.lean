/-
Weak/Prom: **S3d — the cut execution's gmo and load values** (plan rev 7 §6 S3d).
* `gC` — gmo restricted to the cut: the cut's memory operations in rank order (PfxRank.lean), so
  `gB gC a b ↔ E.gmo a b` (`gB_C`).
* `Y` — the cut with `E`'s own valuation: it has `E`'s events, so its `rfSrc` (Ref.lean, the load value axiom's
  store computed over the cut) is "the gmo-latest candidate OF THE CUT" (`rfSrcY_some`, `rfSrcY_none`), and it is
  `E`'s store whenever that store is in the cut (`rfSrcY_of_rfI`).
* `νC` — THE VALUES OF THE CUT: every load of the cut returns the bytes of its cut source (`nb`), computed by
  iterating `Fv` along gmo: a load's source's stored value only depends on loads EARLIER IN GMO (`dep_src`: rule 10,
  or rule 12 for a forwarded source, rvwmo.adoc:294, :298–300), so the iteration stabilises (`itV_stab`) at a fixed
  point (`νC_fix`).
* `νC_kv` — every load of the cut that is in `Gl` (the gmo-down-closure of the observations) keeps its value: its
  source is in the cut (gmo-below ⇒ an anchor store; po-below ⇒ in the cut) and its source's data dependencies are
  gmo-earlier loads of `Gl` (induction on the rank).  Hence `agreeG_νC`: `νC` agrees with `E.ν` on `Gl`, and every
  event of the cut keeps its address (PfxCut.lean `concC_pa`).
* `lva_XC` — the load value axiom of the cut execution `XC = conc T trsC νC gC`.
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.PfxCut

noncomputable section

namespace Weak.Prom.Pfx

open Classical
open Weak.Prom.Ref
open Weak.Prom.Cmp (depsOf getLast?_filter_max getLast?_filter_mem writesB_store)

namespace Cut

variable (E : IExec) (O : List EvId)

/-- The cut's memory operations. -/
def Dm : List EvId := (sids (trsC E O)).filter (fun e => (E.sk e).kind.isMem)

def Rm : Nat := (Dm E O).foldr (fun e m => max m (E.rk e)) 0

/-- gmo restricted to the cut, as a list. -/
def gC : List EvId :=
  (List.range (Rm E O + 1)).filterMap (fun n => (Dm E O).find? (fun e => decide (E.rk e = n)))

/-- The cut with `E`'s valuation. -/
def Y : Exec := conc E.T (trsC E O) E.ν (gC E O)

/-- The cut's loads. -/
def Dl : List EvId := (Dm E O).filter (fun e => (E.sk e).kind.isLoad)

/-- A load's bytes from its cut source under valuation `μ`. -/
def nb (μ : Val) (r : EvId) : List Nat :=
  (List.range (E.sk r).sz).map (fun k =>
    match rfSrc (Y E O) r ((E.ev r).pa + k) with
    | some w => ((concEv μ w.1 w.2 (E.sev w)).wdat[(E.ev r).pa + k - (E.ev w).pa]?).getD 0
    | none => E.T.imgF ((E.ev r).pa + k))

def Fv (μ : Val) : Val := fun r => if r ∈ Dl E O then nb E O μ r else E.ν r

def itV : Nat → Val
  | 0 => E.ν
  | n + 1 => Fv E O (itV n)

/-- **THE VALUES OF THE CUT.** -/
def νC : Val := itV E O (Rm E O + 1)

/-- **THE CUT EXECUTION.** -/
def XC : Exec := conc E.T (trsC E O) (νC E O) (gC E O)

end Cut

open Cut

theorem poS_congr {S S' : EvId → Skel} {a b : EvId} (ha : S a = S' a) (hb : S b = S' b) : poS S a b = poS S' a b := by
  unfold poS; rw [ha, hb]

/-- `rfSrc` only reads gmo, the gmo elements' writes and skeletons, and the load's skeleton. -/
theorem rfSrc_congr (X X' : Exec) (r : EvId) (x : Nat) (hg : X.gmo = X'.gmo)
    (hw : ∀ w ∈ X.gmo, writesB (X.ev w) x = writesB (X'.ev w) x ∧ X.sk w = X'.sk w) (hr : X.sk r = X'.sk r) :
    rfSrc X r x = rfSrc X' r x := by
  unfold rfSrc gmoBefore poX
  rw [← hg]
  congr 1
  apply List.filter_congr
  intro w hw'
  rw [(hw w hw').1, poS_congr (hw w hw').2 hr]

theorem pos_lt_iff (f : EvId → Nat) : ∀ (g : List EvId), g.Pairwise (fun x y => f x < f y) → ∀ {a b : EvId},
    a ∈ g → b ∈ g → (pos g a < pos g b ↔ f a < f b)
  | [], _, _, _, ha, _ => absurd ha List.not_mem_nil
  | x :: t, hp, a, b, ha, hb => by
    have hp' := List.pairwise_cons.1 hp
    unfold pos
    by_cases hxa : x = a
    · subst hxa
      by_cases hxb : x = b
      · subst hxb; simp
      · rw [if_pos rfl, if_neg hxb]
        have hbt : b ∈ t := by rcases List.mem_cons.1 hb with h | h; exact absurd h.symm hxb; exact h
        have := hp'.1 b hbt; constructor <;> intro <;> omega
    · rw [if_neg hxa]
      have hat : a ∈ t := by rcases List.mem_cons.1 ha with h | h; exact absurd h.symm hxa; exact h
      by_cases hxb : x = b
      · subst hxb
        rw [if_pos rfl]
        have := hp'.1 a hat; constructor <;> intro <;> omega
      · rw [if_neg hxb]
        have hbt : b ∈ t := by rcases List.mem_cons.1 hb with h | h; exact absurd h.symm hxb; exact h
        rw [← pos_lt_iff f t hp'.2 hat hbt]; omega

section lemmas

variable {E : IExec} {O : List EvId} (H : Hyp E O)
include H

theorem mem_Dm (e : EvId) : e ∈ Dm E O ↔ inD E O e ∧ (E.sk e).kind.isMem = true := by
  unfold Dm; rw [List.mem_filter, mem_sidsC H]

theorem Dm_mem {e : EvId} (he : e ∈ Dm E O) : E.isMem e :=
  ⟨inD_has H ((mem_Dm H e).1 he).1, ((mem_Dm H e).1 he).2⟩

theorem rk_le_Rm {e : EvId} (he : e ∈ Dm E O) : E.rk e ≤ Rm E O := by
  unfold Rm
  generalize Dm E O = L at he
  induction L with
  | nil => exact absurd he List.not_mem_nil
  | cons a t ih =>
    simp only [List.foldr_cons]
    rcases List.mem_cons.1 he with rfl | h
    · omega
    · have := ih h; omega

theorem mem_gC (e : EvId) : e ∈ gC E O ↔ e ∈ Dm E O := by
  unfold gC
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨n, _, hn⟩; exact List.mem_of_find?_eq_some hn
  · intro he
    refine ⟨E.rk e, List.mem_range.2 (by have := rk_le_Rm H he; omega), ?_⟩
    have hs : ((Dm E O).find? (fun x => decide (E.rk x = E.rk e))).isSome := List.find?_isSome.2 ⟨e, he, by simp⟩
    obtain ⟨e', he'⟩ := Option.isSome_iff_exists.1 hs
    rw [he']
    have h1 := List.find?_some he'
    have h2 := List.mem_of_find?_eq_some he'
    simp only [decide_eq_true_eq] at h1
    rw [IExec.rk_inj (H_gmo H) (H_prog H) (Dm_mem H h2) (Dm_mem H he) h1]

theorem gC_pairwise : (gC E O).Pairwise (fun x y => E.rk x < E.rk y) := by
  unfold gC
  apply List.Pairwise.filterMap _ _ List.pairwise_lt_range
  intro a a' haa b hb b' hb'
  have h1 := List.find?_some hb
  have h2 := List.find?_some hb'
  simp only [decide_eq_true_eq] at h1 h2
  omega

theorem gC_nodup : (gC E O).Nodup := (gC_pairwise H).imp (fun h => by intro he; subst he; omega)

theorem gB_C {a b : EvId} (ha : a ∈ Dm E O) (hb : b ∈ Dm E O) : gB (gC E O) a b = true ↔ E.gmo a b := by
  have ha' := (mem_gC H a).2 ha
  have hb' := (mem_gC H b).2 hb
  have c1 : (gC E O).contains a = true := List.contains_iff_mem.2 ha'
  have c2 : (gC E O).contains b = true := List.contains_iff_mem.2 hb'
  unfold gB
  rw [c1, c2, Bool.true_and, Bool.true_and, decide_eq_true_eq]
  rw [pos_lt_iff E.rk _ (gC_pairwise H) ha' hb', IExec.gmo_iff_rk (H_gmo H) (H_prog H) (Dm_mem H ha) (Dm_mem H hb)]

theorem gB_C_mem {a b : EvId} (h : gB (gC E O) a b = true) : a ∈ Dm E O ∧ b ∈ Dm E O := by
  simp only [gB, Bool.and_eq_true, List.contains_iff_mem] at h
  exact ⟨(mem_gC H a).1 h.1.1, (mem_gC H b).1 h.1.2⟩

theorem Y_ev {e : EvId} (he : inD E O e) : (Y E O).ev e = E.ev e := concC_ev H E.ν _ he

theorem Y_sk {e : EvId} (he : inD E O e) : (Y E O).sk e = E.sk e := concC_sk H E.ν _ he

theorem not_ld_st {e : EvId} (he : E.has e) (hl : (E.sk e).kind.isLoad = true) : (E.sk e).kind.isStore = false := by
  obtain ⟨h, i⟩ := e
  rcases fragEv H.conf H.frag he.1 he with hk | hk | ⟨f, hk, _⟩ <;>
    (change (E.sev (h, i)).sk.kind.isLoad = true at hl; change (E.sev (h, i)).sk.kind.isStore = false;
     rw [hk] at hl ⊢) <;> simp_all [Kind.isLoad, Kind.isStore]

theorem isIoI_f (e : EvId) : E.isIoI e = false := by simp [IExec.isIoI, H.io]

/-- The cut's candidates are `E`'s candidates. -/
theorem candY {r w : EvId} (hr : r ∈ Dm E O) (hw : w ∈ gC E O) (x : Nat) :
    (writesB ((Y E O).ev w) x && (gmoBefore (Y E O) w r || poX (Y E O) w r)) = true ↔ E.candI r x w := by
  have hwD := (mem_gC H w).1 hw
  have hwi := ((mem_Dm H w).1 hwD).1
  have hri := ((mem_Dm H r).1 hr).1
  unfold gmoBefore poX
  rw [Y_ev H hwi, poS_congr (Y_sk H hwi) (Y_sk H hri)]
  show (writesB (E.ev w) x && (gB (gC E O) w r || poS E.sk w r)) = true ↔ _
  rw [Bool.and_eq_true, Bool.or_eq_true, gB_C H hwD hr]
  unfold IExec.candI
  exact ⟨fun h => ⟨inD_has H hwi, h⟩, fun h => h.2⟩

theorem rfSrcY_some {r w : EvId} {x : Nat} (hr : r ∈ Dm E O) (h : rfSrc (Y E O) r x = some w) :
    w ∈ Dm E O ∧ E.candI r x w ∧ ∀ w', inD E O w' → E.candI r x w' → w' = w ∨ E.gmo w' w := by
  have hm := getLast?_filter_mem _ _ _ h
  have hwg : w ∈ gC E O := hm.1
  have hwD := (mem_gC H w).1 hwg
  refine ⟨hwD, (candY H hr hwg x).1 hm.2, fun w' hw' hc => ?_⟩
  have hw'm : (E.sk w').kind.isMem = true := Kind.isMem_of_isStore _ (writesB_store hc.2.1)
  have hw'g : w' ∈ gC E O := (mem_gC H w').2 ((mem_Dm H w').2 ⟨hw', hw'm⟩)
  obtain ⟨s, hs, _, _, hcs⟩ := getLast?_filter_max (fun w => writesB ((Y E O).ev w) x && (gmoBefore (Y E O) w r || poX (Y E O) w r)) _ (gC_nodup H) w' hw'g
    ((candY H hr hw'g x).2 hc)
  have hs' : rfSrc (Y E O) r x = some s := hs
  rw [h] at hs'; cases hs'
  rcases hcs with h1 | h1
  · exact Or.inl h1
  · right
    rw [← gB_C H ((mem_gC H w').1 hw'g) hwD]
    have c1 : (gC E O).contains w' = true := List.contains_iff_mem.2 hw'g
    have c2 : (gC E O).contains w = true := List.contains_iff_mem.2 hwg
    unfold gB
    rw [c1, c2, Bool.true_and, Bool.true_and, decide_eq_true_eq]
    exact h1

theorem rfSrcY_none {r : EvId} {x : Nat} (hr : r ∈ Dm E O) (h : rfSrc (Y E O) r x = none) :
    ∀ w', inD E O w' → ¬ E.candI r x w' := by
  intro w' hw' hc
  have hw'm : (E.sk w').kind.isMem = true := Kind.isMem_of_isStore _ (writesB_store hc.2.1)
  have hw'g : w' ∈ gC E O := (mem_gC H w').2 ((mem_Dm H w').2 ⟨hw', hw'm⟩)
  obtain ⟨s, hs, _⟩ := getLast?_filter_max (fun w => writesB ((Y E O).ev w) x && (gmoBefore (Y E O) w r || poX (Y E O) w r)) _ (gC_nodup H) w' hw'g
    ((candY H hr hw'g x).2 hc)
  have hs' : rfSrc (Y E O) r x = some s := hs
  rw [h] at hs'; cases hs'

/-- When `E`'s store is in the cut, the cut's source is `E`'s. -/
theorem rfSrcY_of_rfI {r : EvId} {x : Nat} {o : Option EvId} (hr : r ∈ Dm E O) (ho : E.rfI r x o)
    (hin : ∀ w, o = some w → inD E O w) : rfSrc (Y E O) r x = o := by
  cases hs : rfSrc (Y E O) r x with
  | none =>
    cases o with
    | none => rfl
    | some w => exact absurd ho.1 (rfSrcY_none H hr hs w (hin w rfl))
  | some s =>
    obtain ⟨hsD, hsc, hmax⟩ := rfSrcY_some H hr hs
    cases o with
    | none => exact absurd hsc (ho s)
    | some w =>
      rcases hmax w (hin w rfl) ho.1 with h1 | h1
      · rw [h1]
      · rcases ho.2 s hsc with h2 | h2
        · rw [h2]
        · exact absurd (IExec.gmo_trans (H_gmo H) h1 h2) (IExec.gmo_irrefl (H_gmo H) w)

theorem Dl_Dm {r : EvId} (hr : r ∈ Dl E O) : r ∈ Dm E O ∧ (E.sk r).kind.isLoad = true := by
  unfold Dl at hr; exact List.mem_filter.1 hr

/-- **A load's cut source depends only on gmo-earlier loads** (rule 10; rule 12 for a forwarded source). -/
theorem dep_src {r w : EvId} (hr : r ∈ Dl E O) {k : Nat} (hk : k < (E.sk r).sz)
    (hs : rfSrc (Y E O) r ((E.ev r).pa + k) = some w) :
    ∀ v ∈ (E.sev w).wval.vars, E.isMem v ∧ E.gmo v r ∧ inD E O v := by
  obtain ⟨hrD, hrl⟩ := Dl_Dm H hr
  obtain ⟨hwD, hwc, hmax⟩ := rfSrcY_some H hrD hs
  have hwi := ((mem_Dm H w).1 hwD).1
  have hwh := inD_has H hwi
  have hrm := Dm_mem H hrD
  have hwst : (E.sk w).kind.isStore = true := writesB_store hwc.2.1
  intro v hv
  obtain ⟨w1, w2⟩ := w
  obtain ⟨hv1, hv2⟩ := wval_vars H.conf H.frag hwi.1 hwh hv
  obtain ⟨hlt, hvm⟩ := deps_mem H.conf H.frag hwi.1 hwh (d := v.2) (Or.inr (Or.inl hv2))
  obtain ⟨v1, v2⟩ := v
  simp only at hv1 hv2 hlt hvm ⊢
  subst v1
  have hvi : inD E O (w1, v2) := inD_of_le H hwi (Nat.le_of_lt hlt)
  have hpo : poS E.sk (w1, v2) (w1, w2) = true := idx_po H.conf H.frag hwi.1 hwh hlt hvm.2
  have hvw : E.gmo (w1, v2) (w1, w2) := by
    apply H_ppo H
    refine ⟨hvm, ⟨hwh, Kind.isMem_of_isStore _ hwst⟩, hpo, Or.inr (Or.inr (Or.inr (Or.inl ?_)))⟩
    right; right; right; right; right; right; left
    simp only [rule10, hwst, beq_self_eq_true, Bool.true_and, Bool.and_true, List.contains_iff_mem]
    exact hv2
  refine ⟨hvm, ?_, hvi⟩
  rcases hwc.2.2 with hg | hp
  · exact IExec.gmo_trans (H_gmo H) hvw hg
  · -- a forwarded source: it is `E`'s source, and rule 12 orders the dependency before the load
    have hne : (w1, w2) ≠ r := by
      intro he; rw [← he] at hrl; have := not_ld_st H hwh hrl; rw [this] at hwst; cases hwst
    by_cases hg : E.gmo (w1, w2) r
    · exact IExec.gmo_trans (H_gmo H) hvw hg
    have hrw : E.gmo r (w1, w2) := by
      rcases IExec.gmo_total (H_gmo H) hrm ⟨hwh, Kind.isMem_of_isStore _ hwst⟩ (Ne.symm hne) with h1 | h1
      · exact h1
      · exact absurd h1 hg
    obtain ⟨o, ho, _⟩ := H.ref.2.2.2.1 r hrm.1 hrl (isIoI_f H r) k hk
    have hsrcE : E.rfI r ((E.ev r).pa + k) (some (w1, w2)) := by
      cases o with
      | none => exact absurd hwc (ho _)
      | some w' =>
        rcases ho.2 _ hwc with h1 | h1
        · rw [h1]; exact ho
        · exfalso
          rcases ho.1.2.2 with h2 | h2
          · exact IExec.gmo_asymm (H_gmo H) h2 (IExec.gmo_trans (H_gmo H) hrw h1)
          · have hw'i : inD E O w' := by
              have hri := ((mem_Dm H r).1 hrD).1
              have hw'h := ho.1.1
              obtain ⟨r1, r2⟩ := r
              obtain ⟨a1, a2⟩ := w'
              have hsame : a1 = r1 := by simp [poS] at h2; exact h2.1
              subst hsame
              have := po_idx H.conf H.frag hri.1 hw'h hrm.1 h2
              exact inD_of_le H hri (Nat.le_of_lt this)
            rcases hmax w' hw'i ho.1 with h3 | h3
            · rw [h3] at h1; exact IExec.gmo_irrefl (H_gmo H) _ h1
            · exact IExec.gmo_irrefl (H_gmo H) _ (IExec.gmo_trans (H_gmo H) h1 h3)
    apply H_ppo H
    have hrp : poS E.sk (w1, v2) r = true := by
      obtain ⟨r1, r2⟩ := r
      have hsame : w1 = r1 := by simp [poS] at hp; exact hp.1
      subst hsame
      have := po_idx H.conf H.frag hwi.1 hwh hrm.1 hp
      exact idx_po H.conf H.frag hwi.1 hrm.1 (by omega) hvm.2
    refine ⟨hvm, hrm, hrp, Or.inr (Or.inr (Or.inr (Or.inr ?_)))⟩
    refine ⟨hrl, isIoI_f H r, (w1, w2), hwh, hpo, hp, hwst, Or.inr (by simpa using hv2), k, hk, hsrcE⟩

theorem nb_congr {r : EvId} (hr : r ∈ Dl E O) {μ μ' : Val} (h : ∀ v, E.isMem v → E.gmo v r → μ v = μ' v) :
    nb E O μ r = nb E O μ' r := by
  unfold nb
  apply List.map_congr_left
  intro k hk
  have hk' : k < (E.sk r).sz := List.mem_range.1 hk
  cases hs : rfSrc (Y E O) r ((E.ev r).pa + k) with
  | none => rfl
  | some w =>
    simp only
    have hd := dep_src H hr hk' hs
    unfold concEv
    simp only
    rw [Ex.eval_congr μ μ' _ (fun v hv => h v (hd v hv).1 (hd v hv).2.1)]

theorem itV_out {v : EvId} (hv : v ∉ Dl E O) : ∀ n, itV E O n v = E.ν v
  | 0 => rfl
  | n + 1 => by show Fv E O (itV E O n) v = E.ν v; unfold Fv; rw [if_neg hv]

theorem itV_stab : ∀ n m, n ≤ m → ∀ v, (v ∉ Dl E O ∨ E.rk v < n) → itV E O m v = itV E O n v := by
  intro n
  induction n with
  | zero =>
    intro m _ v hv
    rcases hv with hv | hv
    · rw [itV_out H hv, itV_out H hv]
    · omega
  | succ n ih =>
    intro m hm v hv
    by_cases hvd : v ∈ Dl E O
    · have hrk : E.rk v < n + 1 := by rcases hv with hv | hv; exact absurd hvd hv; exact hv
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      show Fv E O (itV E O m') v = Fv E O (itV E O n) v
      unfold Fv; rw [if_pos hvd, if_pos hvd]
      apply nb_congr H hvd
      intro u hu hg
      apply ih m' (by omega) u
      by_cases hud : u ∈ Dl E O
      · right
        have := IExec.rk_lt (H_gmo H) (H_prog H) hg; omega
      · exact Or.inl hud
    · rw [itV_out H hvd, itV_out H hvd]

theorem νC_out {v : EvId} (hv : v ∉ Dl E O) : νC E O v = E.ν v := itV_out H hv _

/-- The fixed point: every load of the cut returns its cut source's bytes. -/
theorem νC_fix {r : EvId} (hr : r ∈ Dl E O) : νC E O r = nb E O (νC E O) r := by
  show Fv E O (itV E O (Rm E O)) r = nb E O (itV E O (Rm E O + 1)) r
  unfold Fv; rw [if_pos hr]
  apply nb_congr H hr
  intro u hu hg
  symm
  apply itV_stab H (Rm E O) (Rm E O + 1) (by omega) u
  by_cases hud : u ∈ Dl E O
  · right
    have h1 := IExec.rk_lt (H_gmo H) (H_prog H) hg
    have h2 := rk_le_Rm H (Dl_Dm H hr).1
    omega
  · exact Or.inl hud

/-- **THE LOADS OF `Gl` KEEP THEIR VALUES.** -/
theorem νC_kv : ∀ n, ∀ r, E.rk r = n → r ∈ Dl E O → r ∈ Gl E O → νC E O r = E.ν r := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
  intro r hn hr hrG
  obtain ⟨hrD, hrl⟩ := Dl_Dm H hr
  have hrm := Dm_mem H hrD
  have hri := ((mem_Dm H r).1 hrD).1
  rw [νC_fix H hr]
  have hlen : (E.ν r).length = (E.sk r).sz := by
    have := ((H.ref.2.1 r hrm.1).1 hrl)
    unfold IExec.ev concEv at this
    simp only at this
    change (if (E.sev r).sk.kind.isLoad = true then E.ν (r.1, r.2) else []).length = _ at this
    rw [if_pos (show (E.sev r).sk.kind.isLoad = true from hrl)] at this; exact this
  apply List.ext_getElem?
  intro k
  unfold nb
  rw [List.getElem?_map]
  by_cases hk : k < (E.sk r).sz
  · rw [List.getElem?_range hk]
    obtain ⟨o, ho, hval⟩ := H.ref.2.2.2.1 r hrm.1 hrl (isIoI_f H r) k hk
    have hrd : (E.ev r).rdat = E.ν r := by
      unfold IExec.ev concEv; simp only
      change (if (E.sev r).sk.kind.isLoad = true then E.ν (r.1, r.2) else []) = _
      rw [if_pos (show (E.sev r).sk.kind.isLoad = true from hrl)]
    rw [hrd] at hval
    rw [hval]
    have hin : ∀ w, o = some w → inD E O w := by
      intro w hw; subst hw
      rcases ho.1.2.2 with hg | hp
      · have hwG := Gl_down H hrG hg
        have hws := writesB_store ho.1.2.1
        exact Al_inD H (List.mem_append_right _ (List.mem_filter.2 ⟨hwG, hws⟩))
      · obtain ⟨r1, r2⟩ := r
        obtain ⟨a1, a2⟩ := w
        have hsame : a1 = r1 := by simp [poS] at hp; exact hp.1
        subst hsame
        exact inD_of_le H hri (Nat.le_of_lt (po_idx H.conf H.frag hri.1 ho.1.1 hrm.1 hp))
    simp only [Option.map_some]
    rw [rfSrcY_of_rfI H hrD ho hin]
    cases o with
    | none => rfl
    | some w =>
      simp only [Option.map_some, IExec.valI]
      have hs : rfSrc (Y E O) r ((E.ev r).pa + k) = some w := rfSrcY_of_rfI H hrD ho hin
      have hd := dep_src H hr hk hs
      have heq : (E.sev w).wval.eval (νC E O) = (E.sev w).wval.eval E.ν := by
        apply Ex.eval_congr
        intro v hv
        obtain ⟨hvm, hvg, hvi⟩ := hd v hv
        by_cases hvd : v ∈ Dl E O
        · exact ih (E.rk v) (by rw [← hn]; exact IExec.rk_lt (H_gmo H) (H_prog H) hvg) v rfl hvd
            (Gl_down H hrG hvg)
        · exact νC_out H hvd
      unfold wbyte IExec.ev concEv
      simp only
      rw [heq]
  · rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]
    rfl

theorem agreeG_νC : AgreeG E O (νC E O) := by
  intro x hx
  by_cases hd : x ∈ Dl E O
  · exact νC_kv H _ x rfl hd hx
  · exact νC_out H hd

theorem XC_ev {e : EvId} (he : inD E O e) : (XC E O).ev e = concEv (νC E O) e.1 e.2 (E.sev e) :=
  concC_ev H _ _ he

theorem XC_sk {e : EvId} (he : inD E O e) : (XC E O).sk e = E.sk e := concC_sk H _ _ he

theorem XC_pa {e : EvId} (he : inD E O e) : ((XC E O).ev e).pa = (E.ev e).pa :=
  concC_pa H (agreeG_νC H) _ he

theorem XC_writes {e : EvId} (he : inD E O e) (x : Nat) : writesB ((XC E O).ev e) x = writesB (E.ev e) x := by
  unfold writesB touches
  rw [XC_pa H he]
  have : ((XC E O).ev e).sk = (E.ev e).sk := XC_sk H he
  rw [this]

theorem XC_touches {e : EvId} (he : inD E O e) (x : Nat) : touches ((XC E O).ev e) x = touches (E.ev e) x := by
  unfold touches
  rw [XC_pa H he]
  have : ((XC E O).ev e).sk = (E.ev e).sk := XC_sk H he
  rw [this]

theorem XC_ids (e : EvId) : e ∈ (XC E O).ids ↔ inD E O e := by
  unfold XC; rw [conc_ids]; exact mem_sidsC H e

theorem rfSrc_XC (r : EvId) (hr : inD E O r) (x : Nat) : rfSrc (XC E O) r x = rfSrc (Y E O) r x := by
  apply rfSrc_congr (XC E O) (Y E O) r x rfl
  · intro w hw
    have hwi := ((mem_Dm H w).1 ((mem_gC H w).1 hw)).1
    refine ⟨by rw [XC_writes H hwi, ← Y_ev H hwi], by rw [XC_sk H hwi, Y_sk H hwi]⟩
  · rw [XC_sk H hr, Y_sk H hr]

/-- **THE LOAD VALUE AXIOM of the cut execution.** -/
theorem lva_XC : loadValueAx (XC E O) := by
  intro r hr hl _ k hk
  have hri := (XC_ids H r).1 hr
  rw [XC_sk H hri] at hl hk
  have hrD : r ∈ Dm E O := (mem_Dm H r).2 ⟨hri, Kind.isMem_of_isLoad _ hl⟩
  have hrl : r ∈ Dl E O := List.mem_filter.2 ⟨hrD, hl⟩
  have hl' : (E.sev r).sk.kind.isLoad = true := hl
  have hrd : ((XC E O).ev r).rdat = νC E O r := by
    rw [XC_ev H hri]; unfold concEv; simp only; rw [if_pos hl']
  rw [hrd, νC_fix H hrl]
  unfold nb lvVal
  rw [List.getElem?_map, List.getElem?_range hk]
  simp only [Option.map_some, Option.some.injEq]
  rw [rfSrc_XC H r hri, XC_pa H hri]
  cases hs : rfSrc (Y E O) r ((E.ev r).pa + k) with
  | none => rfl
  | some w =>
    simp only [Option.map_some]
    have hwi := ((mem_Dm H w).1 (rfSrcY_some H hrD hs).1).1
    unfold wbyte
    rw [XC_pa H hwi, XC_ev H hwi]

end lemmas

end Weak.Prom.Pfx

end
