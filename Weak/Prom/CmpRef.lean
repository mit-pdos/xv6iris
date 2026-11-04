/-
Weak/Prom: **completeness S3a — facts of a consistent reference execution** (plan rev 7 §6 "Each EXT and readable
check reduces to a ppo ⊆ gmo, a load-value fact or a `platformOrd` fact").

Over an execution `X` with `rvwmoRef X` (Weak/Prom/Ref.lean) and no I/O regions:
* gmo is duplicate-free and holds exactly the memory operations; `gB_of_ppo` (rvwmo.adoc:307–310 "a global memory
  order conforming to preserved program order");
* the load value axiom's store `rfSrc` (rvwmo.adoc:315–324): `rfSrc_spec` (it is a candidate), `rfSrc_max` (it is
  the gmo-latest candidate), `ldVal` (what a load returns);
* one constructor per ppo rule used by S3a (rules 1, 2, 4, 9, 10, 11, 12, 13; rvwmo.adoc:278–302);
* the two coherence lemmas the simulation needs: `corr` (two po-ordered loads of a byte return stores in coherence
  order, from rules 1 and 2 and the load value axiom) and `srcFwd` (a load whose store is not gmo-before it reads
  the po-latest own store, from rule 1 and the load value axiom);
* single-size consequences (`sameFp`).
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.CmpDefs

namespace Weak.Prom.Cmp

open MachCSL MachCSL.Stdpp Iris.Std
open Weak.Prom Weak.Prom.Ref

/-! ## 1. Lists -/

/-- The last element of a filter is the latest member satisfying the predicate. -/
theorem getLast?_filter_max (p : EvId → Bool) : ∀ (g : List EvId), g.Nodup → ∀ c, c ∈ g → p c = true →
    ∃ s, (g.filter p).getLast? = some s ∧ s ∈ g ∧ p s = true ∧ (c = s ∨ pos g c < pos g s)
  | [], _, _, hc, _ => absurd hc List.not_mem_nil
  | x :: t, hn, c, hc, hp => by
    have hnd := List.nodup_cons.1 hn
    by_cases hcx : x = c
    · subst hcx
      rw [List.filter_cons, if_pos hp]
      cases hft : t.filter p with
      | nil => exact ⟨x, rfl, List.mem_cons_self .., hp, .inl rfl⟩
      | cons y ys =>
        have hne : t.filter p ≠ [] := by rw [hft]; exact List.cons_ne_nil _ _
        obtain ⟨s, hs⟩ := List.getLast?_isSome.2 hne |> Option.isSome_iff_exists.1
        have hsm : s ∈ t.filter p := List.mem_of_getLast? hs
        have hst : s ∈ t := (List.mem_filter.1 hsm).1
        have hsx : x ≠ s := fun h => hnd.1 (h ▸ hst)
        refine ⟨s, ?_, List.mem_cons_of_mem _ hst, (List.mem_filter.1 hsm).2, .inr ?_⟩
        · rw [← hft, List.getLast?_cons, hs]; rfl
        · rw [pos_cons_self, pos_cons_ne _ _ _ hsx]; omega
    · have hct : c ∈ t := by
        rcases List.mem_cons.1 hc with h | h
        · exact absurd h.symm hcx
        · exact h
      obtain ⟨s, hs, hst, hps, hcs⟩ := getLast?_filter_max p t hnd.2 c hct hp
      have hsx : x ≠ s := fun h => hnd.1 (h ▸ hst)
      refine ⟨s, ?_, List.mem_cons_of_mem _ hst, hps, ?_⟩
      · rw [List.filter_cons]
        split
        · rw [List.getLast?_cons, hs]; rfl
        · exact hs
      · rw [pos_cons_ne _ _ _ hcx, pos_cons_ne _ _ _ hsx]
        rcases hcs with h | h
        · exact .inl h
        · exact .inr (by omega)

theorem getLast?_filter_mem (p : EvId → Bool) (g : List EvId) (s : EvId) (h : (g.filter p).getLast? = some s) :
    s ∈ g ∧ p s = true :=
  List.mem_filter.1 (List.mem_of_getLast? h)

/-! ## 2. The execution -/

section exec

variable {X : Exec} (hX : rvwmoRef X) (hio : X.io = [])

include hX in
theorem gmo_nodup : X.gmo.Nodup := hX.1.1.1

include hX in
theorem mem_gmo (e : EvId) : e ∈ X.gmo ↔ e ∈ X.ids ∧ (X.sk e).kind.isMem = true :=
  ⟨fun h => hX.1.1.2.1 e h, fun h => hX.1.1.2.2 e h.1 h.2⟩

include hio in
theorem isIo_f (e : EvId) : isIo X e = false := isIo_nil X hio e

include hX hio in
/-- PPO ⊆ GMO (rvwmo.adoc:307–310). -/
theorem gB_of_ppo {a b : EvId} (ha : a ∈ X.ids) (hb : b ∈ X.ids) (h : ppoB X a b = true) :
    gB X.gmo a b = true :=
  hX.1.2.2.1 a ha b hb (ppo_ordered X a b h)

theorem poX_trans {a b c : EvId} (h1 : poX X a b = true) (h2 : poX X b c = true) : poX X a c = true := by
  simp only [poX, poS, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at *
  exact ⟨h1.1.trans h2.1, by omega⟩

theorem poX_irrefl (a : EvId) : poX X a a = false := by
  simp [poX, poS]

theorem poX_asymm {a b : EvId} (h : poX X a b = true) : poX X b a = false := by
  simp only [poX, poS, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, Bool.and_eq_false_iff,
    decide_eq_false_iff_not] at *
  right; omega

theorem gB_irrefl (g : List EvId) (a : EvId) : gB g a a = false := by
  simp [gB]

theorem gB_asymm {g : List EvId} {a b : EvId} (h : gB g a b = true) : gB g b a = false := by
  obtain ⟨_, _, hp⟩ := gB_mem g a b h
  simp only [gB, Bool.and_eq_false_iff, decide_eq_false_iff_not]
  right; omega

theorem writesB_store {v : Ev} {x : Nat} (h : writesB v x = true) : v.sk.kind.isStore = true := by
  simp only [writesB, Bool.and_eq_true] at h; exact h.1

theorem writesB_touches {v : Ev} {x : Nat} (h : writesB v x = true) : touches v x = true := by
  simp only [writesB, Bool.and_eq_true] at h; exact h.2

/-! ### The load value axiom's store -/

/-- The candidates of the load value axiom for byte `x` of load `r`: "Stores that write that byte and that precede
i in the global memory order … Stores that write that byte and that precede i in program order". -/
def cand (X : Exec) (r : EvId) (x : Nat) (w : EvId) : Bool := writesB (X.ev w) x && (gmoBefore X w r || poX X w r)

theorem rfSrc_eq (r : EvId) (x : Nat) : rfSrc X r x = (X.gmo.filter (cand X r x)).getLast? := rfl

theorem rfSrc_spec {r : EvId} {x : Nat} {s : EvId} (h : rfSrc X r x = some s) :
    s ∈ X.gmo ∧ writesB (X.ev s) x = true ∧ (gB X.gmo s r = true ∨ poX X s r = true) := by
  obtain ⟨h1, h2⟩ := getLast?_filter_mem _ _ _ h
  simp only [cand, Bool.and_eq_true, Bool.or_eq_true] at h2
  exact ⟨h1, h2.1, h2.2⟩

include hX in
/-- THE LOAD VALUE AXIOM'S STORE IS THE gmo-LATEST CANDIDATE. -/
theorem rfSrc_max {r : EvId} {x : Nat} {c : EvId} (hc : c ∈ X.gmo) (hw : writesB (X.ev c) x = true)
    (ho : gB X.gmo c r = true ∨ poX X c r = true) :
    ∃ s, rfSrc X r x = some s ∧ (c = s ∨ gB X.gmo c s = true) := by
  have hp : cand X r x c = true := by
    simp only [cand, Bool.and_eq_true, Bool.or_eq_true]; exact ⟨hw, ho⟩
  obtain ⟨s, hs, hsm, _, hcs⟩ := getLast?_filter_max _ X.gmo (gmo_nodup hX) c hc hp
  refine ⟨s, hs, ?_⟩
  rcases hcs with h | h
  · exact .inl h
  · right; simp [gB, hc, hsm, h]

include hX hio in
/-- What a load returns (the load value axiom, RAM loads). -/
theorem ldVal {r : EvId} (hr : r ∈ X.ids) (hl : (X.sk r).kind.isLoad = true) {k : Nat} (hk : k < (X.sk r).sz) :
    (X.ev r).rdat[k]? = some (lvVal X r ((X.ev r).pa + k)) :=
  hX.1.2.2.2.1 r hr hl (isIo_f hio r) k hk

/-! ### ppo constructors (rvwmo.adoc:278–302) -/

theorem ppoB_mk {a b : EvId} (ha : (X.sk a).kind.isMem = true) (hb : (X.sk b).kind.isMem = true)
    (hpo : poX X a b = true)
    (hr : (rule1 X a b || rule2 X a b || rule3 X a b || staticRules X.ids X.sk (isIo X) a b ||
      rule12 X a b) = true) : ppoB X a b = true := ppoB_intro X a b ha hb hpo hr

/-- Rule 1: "b is a store, and a and b access overlapping memory addresses". -/
theorem ppo_r1 {a b : EvId} (ha : (X.sk a).kind.isMem = true) (hb : (X.sk b).kind.isStore = true)
    (hpo : poX X a b = true) (hov : overlapB (X.ev a) (X.ev b) = true) : ppoB X a b = true := by
  refine ppoB_mk ha (Kind.isMem_of_isStore _ hb) hpo ?_
  have : rule1 X a b = true := by
    unfold rule1; rw [hb, hov]; rfl
  simp [this]

theorem staticRules_ppo {a b : EvId} (ha : (X.sk a).kind.isMem = true) (hb : (X.sk b).kind.isMem = true)
    (hpo : poX X a b = true) (hs : staticRules X.ids X.sk (isIo X) a b = true) : ppoB X a b = true := by
  refine ppoB_mk ha hb hpo ?_
  simp [hs]

/-- Rule 4: "There is a FENCE instruction that orders a before b". -/
theorem ppo_r4 {a b m : EvId} {f : FenceSet} (ha : (X.sk a).kind.isMem = true) (hb : (X.sk b).kind.isMem = true)
    (hm : m ∈ X.ids) (hf : (X.sk m).kind = .fence f) (h1 : poX X a m = true) (h2 : poX X m b = true)
    (hp : inPred X.sk (isIo X) f a = true) (hs : inSucc X.sk (isIo X) f b = true) : ppoB X a b = true := by
  refine staticRules_ppo ha hb (poX_trans h1 h2) ?_
  have : rule4 X.ids X.sk (isIo X) a b = true := by
    unfold rule4
    refine List.any_eq_true.2 ⟨m, hm, ?_⟩
    rw [hf]
    simp only [poX] at h1 h2
    simp [h1, h2, hp, hs]
  simp [staticRules, this]

/-- Rule 9: "b has a syntactic address dependency on a". -/
theorem ppo_r9 {a b : EvId} (ha : (X.sk a).kind.isMem = true) (hb : (X.sk b).kind.isMem = true)
    (hpo : poX X a b = true) (hd : a.2 ∈ (X.sk b).adep) : ppoB X a b = true := by
  refine staticRules_ppo ha hb hpo ?_
  have h1 : a.1 = b.1 := by
    simp only [poX, poS, Bool.and_eq_true, beq_iff_eq] at hpo; exact hpo.1
  have : rule9 X.sk a b = true := by
    simp [rule9, h1, hd]
  simp [staticRules, this]

/-- Rule 10: "b has a syntactic data dependency on a". -/
theorem ppo_r10 {a b : EvId} (ha : (X.sk a).kind.isMem = true) (hb : (X.sk b).kind.isStore = true)
    (hpo : poX X a b = true) (hd : a.2 ∈ (X.sk b).ddep) : ppoB X a b = true := by
  refine staticRules_ppo ha (Kind.isMem_of_isStore _ hb) hpo ?_
  have h1 : a.1 = b.1 := by
    simp only [poX, poS, Bool.and_eq_true, beq_iff_eq] at hpo; exact hpo.1
  have : rule10 X.sk a b = true := by
    simp [rule10, h1, hd, hb]
  simp [staticRules, this]

/-- Rule 11: "b is a store, and b has a syntactic control dependency on a". -/
theorem ppo_r11 {a b : EvId} (ha : (X.sk a).kind.isMem = true) (hb : (X.sk b).kind.isStore = true)
    (hpo : poX X a b = true) (hd : a.2 ∈ (X.sk b).cdep) : ppoB X a b = true := by
  refine staticRules_ppo ha (Kind.isMem_of_isStore _ hb) hpo ?_
  have h1 : a.1 = b.1 := by
    simp only [poX, poS, Bool.and_eq_true, beq_iff_eq] at hpo; exact hpo.1
  have : rule11 X.sk a b = true := by
    simp [rule11, h1, hd, hb]
  simp [staticRules, this]

/-- Rule 13: "b is a store, and there exists some instruction m between a and b in program order such that m has
an address dependency on a" (m a memory operation, [OWN.P6]). -/
theorem ppo_r13 {a b m : EvId} (ha : (X.sk a).kind.isMem = true) (hb : (X.sk b).kind.isStore = true)
    (hm : m ∈ X.ids) (hmm : (X.sk m).kind.isMem = true) (h1 : poX X a m = true) (h2 : poX X m b = true)
    (hd : a.2 ∈ (X.sk m).adep) : ppoB X a b = true := by
  refine staticRules_ppo ha (Kind.isMem_of_isStore _ hb) (poX_trans h1 h2) ?_
  have : rule13 X.ids X.sk a b = true := by
    unfold rule13
    rw [hb, Bool.true_and]
    refine List.any_eq_true.2 ⟨m, hm, ?_⟩
    simp only [poX] at h1 h2
    simp [hmm, h1, h2, hd]
  simp [staticRules, this]

include hio in
/-- Rule 12: "b is a load, and there exists some store m between a and b in program order such that m has an
address or data dependency on a, and b returns a value written by m". -/
theorem ppo_r12 {a b m : EvId} (ha : (X.sk a).kind.isMem = true) (hb : (X.sk b).kind.isLoad = true)
    (hm : m ∈ X.ids) (hms : (X.sk m).kind.isStore = true) (h1 : poX X a m = true) (h2 : poX X m b = true)
    (hd : a.2 ∈ (X.sk m).adep ∨ a.2 ∈ (X.sk m).ddep) {k : Nat} (hk : k < (X.sk b).sz)
    (hrf : rfSrc X b ((X.ev b).pa + k) = some m) : ppoB X a b = true := by
  refine ppoB_mk ha (Kind.isMem_of_isLoad _ hb) (poX_trans h1 h2) ?_
  have : rule12 X a b = true := by
    unfold rule12
    rw [hb, isIo_f hio b]
    simp only [Bool.true_and, Bool.not_false]
    refine List.any_eq_true.2 ⟨m, hm, ?_⟩
    have hk' : (List.range (X.sk b).sz).any (fun k => rfSrc X b ((X.ev b).pa + k) == some m) = true :=
      List.any_eq_true.2 ⟨k, List.mem_range.2 hk, by simp [hrf]⟩
    rcases hd with hd | hd <;> simp [h1, h2, hms, hd, hk']
  simp [this]

include hio in
/-- Rule 2: "a and b are loads, x is a byte read by both a and b, there is no store to x between a and b in program
order, and a and b return values for x written by different memory operations". -/
theorem ppo_r2 {a b : EvId} (ha : (X.sk a).kind.isLoad = true) (hb : (X.sk b).kind.isLoad = true)
    (hpo : poX X a b = true) {k : Nat} (hk : k < (X.sk a).sz) (htb : touches (X.ev b) ((X.ev a).pa + k) = true)
    (hno : ∀ m ∈ X.ids, ¬ (poX X a m = true ∧ poX X m b = true ∧ writesB (X.ev m) ((X.ev a).pa + k) = true))
    (hne : rfSrc X a ((X.ev a).pa + k) ≠ rfSrc X b ((X.ev a).pa + k)) : ppoB X a b = true := by
  refine ppoB_mk (Kind.isMem_of_isLoad _ ha) (Kind.isMem_of_isLoad _ hb) hpo ?_
  have : rule2 X a b = true := by
    unfold rule2
    rw [ha, hb, isIo_f hio a, isIo_f hio b]
    simp only [Bool.true_and, Bool.not_false]
    refine List.any_eq_true.2 ⟨k, List.mem_range.2 hk, ?_⟩
    have hall : X.ids.all (fun m => !(poX X a m && poX X m b && writesB (X.ev m) ((X.ev a).pa + k))) = true := by
      refine List.all_eq_true.2 (fun m hm => ?_)
      have := hno m hm
      cases h1 : poX X a m <;> cases h2 : poX X m b <;> cases h3 : writesB (X.ev m) ((X.ev a).pa + k) <;>
        simp_all
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq]
    exact ⟨⟨htb, hall⟩, hne⟩
  simp [this]

/-! ### The key: the timestamp of the store a load reads -/

/-- The timestamp of an optional store (`0` = the initial value). -/
def kts (X : Exec) : Option EvId → Nat
  | none => 0
  | some s => vo X s

include hX in
/-- Every candidate's view is at most the timestamp of the load value axiom's store. -/
theorem kts_ge {r : EvId} {x : Nat} {c : EvId} (hc : c ∈ X.gmo) (hw : writesB (X.ev c) x = true)
    (ho : gB X.gmo c r = true ∨ poX X c r = true) : vo X c ≤ kts X (rfSrc X r x) := by
  obtain ⟨s, hs, hcs⟩ := rfSrc_max hX hc hw ho
  rw [hs]
  rcases hcs with h | h
  · subst h; exact Nat.le_refl _
  · exact (voG_mono X X.gmo c s h).1

/-- A memory operation's identifier in the execution, from gmo. -/
theorem ids_of_gmo {e : EvId} (he : e ∈ X.gmo) (hX : rvwmoRef X) : e ∈ X.ids :=
  ((mem_gmo hX e).1 he).1

theorem overlap_of_touch {u v : Ev} {x : Nat} (hu : touches u x = true) (hv : touches v x = true) :
    overlapB u v = true := by
  simp only [touches, decide_eq_true_eq] at hu hv
  simp only [overlapB, decide_eq_true_eq]
  omega

include hX hio in
/-- **CoRR / CoWR on loads** (rules 1, 2 + the load value axiom): two po-ordered loads of a byte `x` return
stores in coherence order. -/
theorem corr {r b : EvId} (hr : r ∈ X.ids) (hb : b ∈ X.ids) (hrl : (X.sk r).kind.isLoad = true)
    (hbl : (X.sk b).kind.isLoad = true) (hpo : poX X r b = true) {x : Nat} (htr : touches (X.ev r) x = true)
    (htb : touches (X.ev b) x = true) : kts X (rfSrc X r x) ≤ kts X (rfSrc X b x) := by
  cases hsr : rfSrc X r x with
  | none => exact Nat.zero_le _
  | some s0 =>
    obtain ⟨hs0g, hs0w, hs0o⟩ := rfSrc_spec hsr
    have hs0i := ids_of_gmo hs0g hX
    have hs0m : (X.sk s0).kind.isMem = true := Kind.isMem_of_isStore _ (writesB_store hs0w)
    -- a store between r and b in program order writing x
    by_cases hex : ∃ m ∈ X.ids, poX X r m = true ∧ poX X m b = true ∧ writesB (X.ev m) x = true
    · obtain ⟨m, hm, h1, h2, hmw⟩ := hex
      have hms := writesB_store hmw
      have hmg : m ∈ X.gmo := (mem_gmo hX m).2 ⟨hm, Kind.isMem_of_isStore _ hms⟩
      have hle := kts_ge hX hmg hmw (.inr h2)
      have hlt : gB X.gmo s0 m = true := by
        rcases hs0o with h | h
        · have hrm := gB_of_ppo hX hio hr hm (ppo_r1 (Kind.isMem_of_isLoad _ hrl) hms h1
            (overlap_of_touch htr (writesB_touches hmw)))
          exact gB_trans _ _ _ _ h hrm
        · exact gB_of_ppo hX hio hs0i hm (ppo_r1 hs0m hms (poX_trans h h1)
            (overlap_of_touch (writesB_touches hs0w) (writesB_touches hmw)))
      have := (voG_mono X X.gmo s0 m hlt).2 hms
      simp only [kts] at hle ⊢
      unfold vo at hle ⊢
      omega
    · have hno : ∀ m ∈ X.ids, ¬ (poX X r m = true ∧ poX X m b = true ∧
          writesB (X.ev m) ((X.ev r).pa + (x - (X.ev r).pa)) = true) := by
        have hx : (X.ev r).pa + (x - (X.ev r).pa) = x := by
          simp only [touches, decide_eq_true_eq] at htr; omega
        rw [hx]
        exact fun m hm h => hex ⟨m, hm, h⟩
      by_cases heq : rfSrc X r x = rfSrc X b x
      · rw [← heq, hsr]; exact Nat.le_refl _
      · have hk : x - (X.ev r).pa < (X.sk r).sz := by
          simp only [touches, decide_eq_true_eq] at htr; unfold Exec.sk; omega
        have hx : (X.ev r).pa + (x - (X.ev r).pa) = x := by
          simp only [touches, decide_eq_true_eq] at htr; omega
        have hrb : gB X.gmo r b = true := gB_of_ppo hX hio hr hb
          (ppo_r2 hio hrl hbl hpo hk (by rw [hx]; exact htb) hno (by rw [hx]; exact heq))
        have hc : gB X.gmo s0 b = true ∨ poX X s0 b = true := by
          rcases hs0o with h | h
          · exact .inl (gB_trans _ _ _ _ h hrb)
          · exact .inr (poX_trans h hpo)
        exact kts_ge hX hs0g hs0w hc

include hX hio in
/-- **A load whose store is not gmo-before it reads the po-latest own store** (rule 1 + the load value axiom):
no own store po-between the source and the load writes the byte. -/
theorem srcFwd {r s : EvId} {x : Nat} (hsr : rfSrc X r x = some s) (hng : gB X.gmo s r = false) :
    poX X s r = true ∧ ∀ w ∈ X.ids, poX X s w = true → poX X w r = true → writesB (X.ev w) x = false := by
  obtain ⟨hsg, hsw, hso⟩ := rfSrc_spec hsr
  have hpo : poX X s r = true := by
    rcases hso with h | h
    · rw [h] at hng; cases hng
    · exact h
  refine ⟨hpo, fun w hw h1 h2 => ?_⟩
  cases hww : writesB (X.ev w) x
  · rfl
  · exfalso
    have hws := writesB_store hww
    have hwg : w ∈ X.gmo := (mem_gmo hX w).2 ⟨hw, Kind.isMem_of_isStore _ hws⟩
    obtain ⟨s', hs', hws'⟩ := rfSrc_max hX hwg hww (.inr h2)
    rw [hsr] at hs'
    cases hs'
    have hsw' : gB X.gmo s w = true := gB_of_ppo hX hio (ids_of_gmo hsg hX) hw
      (ppo_r1 (Kind.isMem_of_isStore _ (writesB_store hsw)) hws h1
        (overlap_of_touch (writesB_touches hsw) (writesB_touches hww)))
    rcases hws' with h | h
    · subst h; rw [poX_irrefl] at h1; cases h1
    · rw [gB_asymm hsw'] at h; cases h

/-! ### Single size -/

/-- Same footprint. -/
def sameFp (u v : Ev) : Prop := u.pa = v.pa ∧ u.sk.sz = v.sk.sz

theorem touches_sameFp {u v : Ev} (h : sameFp u v) (x : Nat) : touches u x = touches v x := by
  simp [touches, h.1, h.2]

/-- NA-6: two memory operations touching a common byte have the same footprint. -/
theorem sameFp_of {a b : EvId} (hss : singleSize X) (ha : a ∈ X.ids) (hb : b ∈ X.ids)
    (ham : (X.sk a).kind.isMem = true) (hbm : (X.sk b).kind.isMem = true) {x : Nat}
    (hta : touches (X.ev a) x = true) (htb : touches (X.ev b) x = true) : sameFp (X.ev a) (X.ev b) :=
  hss a ha b hb ham hbm (overlap_of_touch hta htb)

include hX in
/-- Under NA-6 a load's candidates are the same for every byte it reads. -/
theorem rfSrc_bytes {r : EvId} (hss : singleSize X) (hr : r ∈ X.ids) (hrm : (X.sk r).kind.isMem = true)
    {x y : Nat} (hx : touches (X.ev r) x = true) (hy : touches (X.ev r) y = true) :
    rfSrc X r x = rfSrc X r y := by
  rw [rfSrc_eq, rfSrc_eq]
  congr 1
  apply List.filter_congr
  intro w hw
  have hwi := ids_of_gmo hw hX
  have hwm := ((mem_gmo hX w).1 hw).2
  unfold cand writesB
  cases hst : (X.ev w).sk.kind.isStore
  · rfl
  · simp only [Bool.true_and]
    have key : touches (X.ev w) x = touches (X.ev w) y := by
      cases htx : touches (X.ev w) x <;> cases hty : touches (X.ev w) y
      · rfl
      · have := sameFp_of hss hwi hr hwm hrm hty hy
        rw [touches_sameFp this] at htx; rw [htx] at hx; cases hx
      · have := sameFp_of hss hwi hr hwm hrm htx hx
        rw [touches_sameFp this] at hty; rw [hty] at hy; cases hy
      · rfl
    rw [key]

end exec

end Weak.Prom.Cmp
