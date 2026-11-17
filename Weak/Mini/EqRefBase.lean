/-
Weak/Mini: **E1, the memory side** (mini plan rev 4 §2 L1 E1): MiniRef's axiom block (Weak/Mini/Ref.lean `MEvs.ax`)
is the full reference's `rvwmoRefInf` (PfxDefs.lean) on any event set whose events are F's word events.

* `MEv.toEv` — a mini (word) event as a full (byte) event: the value becomes its `sz` little-endian bytes
  (`byteList`, RefProg.lean), a fence has size 0 (as `stepI`'s fence arm).
* `Corr A E` — the full execution `E` has exactly `A`'s events, as bytes, `A`'s gmo, no I/O, and an image whose bytes
  are those of `A`'s initial words; every access is aligned and every value fits in `sz` bytes.
* `corr_iff` — then `E.rvwmoRefInf ↔ A.ax ini`.  Rule by rule: on aligned single-size accesses a byte is read or
  written by an access iff the access has that address, so the per-byte candidate sets of the load value axiom are
  one per load (`candI_iff`, `rfI_iff`), and rules 1, 2, 12 collapse to their word forms; rules 3, 5–8, atomicity and
  §zalrsc are vacuous (no AMO/LR/SC kind, no annotation); I/O is vacuous (`io = []`).
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Mini.Ref
import Weak.Mini.EqProg
import Weak.Prom.PfxDefs

namespace Weak.Mini

open Weak.Prom.Ref
open Weak.Prom.Pfx

/-! ## 1. Mini events as full events -/

def MK.toKind : MK → Kind
  | .ld => .ld
  | .st => .st
  | .fence f => .fence f.toFenceSet

/-- The size of an event of kind `k` in a program of access size `sz` (fences: 0, as `stepI`). -/
def MK.szOf (sz : Nat) : MK → Nat
  | .fence _ => 0
  | _ => sz

/-- A word event as a byte event. -/
def MEv.toEv (sz : Nat) (m : MEv) : Ev :=
  { sk := { kind := m.kind.toKind, ii := m.ii, sz := m.kind.szOf sz, adep := m.adep, ddep := m.ddep, cdep := m.cdep }
    pa := m.pa
    rdat := if m.kind = .ld then byteList m.v sz else []
    wdat := if m.kind = .st then byteList m.v sz else [] }

/-! ## 2. Bytes -/

theorem byteList_length (v n : Nat) : (byteList v n).length = n := by simp [byteList]

theorem byteList_get (v n k : Nat) (hk : k < n) : (byteList v n)[k]? = some ((v >>> (8 * k)) % 256) := by
  simp [byteList, hk]

theorem byteList_succ (v n : Nat) : byteList v (n + 1) = v % 256 :: byteList (v / 256) n := by
  unfold byteList
  rw [List.range_succ_eq_map]
  simp only [List.map_cons, List.map_map, Nat.mul_zero, Nat.shiftRight_zero, List.cons.injEq, true_and]
  apply List.map_congr_left
  intro k _
  show (v >>> (8 * (k + 1))) % 256 = ((v / 256) >>> (8 * k)) % 256
  rw [Nat.mul_add, Nat.mul_one, Nat.add_comm, Nat.shiftRight_add, Nat.shiftRight_eq_div_pow v 8]

theorem bytesVal_cons (b : Nat) (bs : List Nat) : bytesVal (b :: bs) = b + 256 * bytesVal bs := rfl

theorem pow8_succ (n : Nat) : 2 ^ (8 * (n + 1)) = 256 * 2 ^ (8 * n) := by
  rw [Nat.mul_add, Nat.pow_add, Nat.mul_comm]

theorem bytesVal_byteList (v n : Nat) : bytesVal (byteList v n) = v % 2 ^ (8 * n) := by
  induction n generalizing v with
  | zero => simp [byteList, bytesVal, Nat.mod_one]
  | succ n ih => rw [byteList_succ, bytesVal_cons, ih, pow8_succ, Nat.mod_mul]

theorem byteList_mod (v n : Nat) : byteList (v % 2 ^ (8 * n)) n = byteList v n := by
  induction n generalizing v with
  | zero => rfl
  | succ n ih =>
    rw [byteList_succ, byteList_succ, pow8_succ, Nat.mod_mod_of_dvd _ (Nat.dvd_mul_right 256 _),
      Nat.mod_mul_right_div_self, ih]

theorem byteList_inj {a b n : Nat} (h : byteList a n = byteList b n) : a % 2 ^ (8 * n) = b % 2 ^ (8 * n) := by
  rw [← bytesVal_byteList, h, bytesVal_byteList]

theorem byteList_bytesVal : ∀ (bs : List Nat), (∀ b ∈ bs, b < 256) → byteList (bytesVal bs) bs.length = bs
  | [], _ => rfl
  | b :: bs, hb => by
    rw [List.length_cons, byteList_succ, bytesVal_cons]
    have h1 : b < 256 := hb b (List.mem_cons_self ..)
    have h2 := byteList_bytesVal bs (fun x hx => hb x (List.mem_cons_of_mem _ hx))
    have e1 : (b + 256 * bytesVal bs) % 256 = b := by omega
    have e2 : (b + 256 * bytesVal bs) / 256 = bytesVal bs := by omega
    rw [e1, e2, h2]

theorem byte_lt (v k : Nat) : (v >>> (8 * k)) % 256 < 256 := Nat.mod_lt _ (by decide)

theorem byteList_lt (v n : Nat) : ∀ b ∈ byteList v n, b < 256 := by
  intro b hb
  simp only [byteList, List.mem_map] at hb
  obtain ⟨k, _, rfl⟩ := hb
  exact byte_lt v k

/-- Two values with the same bytes below `sz` agree modulo `2^(8 sz)`. -/
theorem eq_of_bytes {a b n : Nat} (ha : a < 2 ^ (8 * n)) (hb : b < 2 ^ (8 * n))
    (h : ∀ k < n, (a >>> (8 * k)) % 256 = (b >>> (8 * k)) % 256) : a = b := by
  have : byteList a n = byteList b n := by
    apply List.ext_getElem?
    intro k
    by_cases hk : k < n
    · rw [byteList_get _ _ _ hk, byteList_get _ _ _ hk, h k hk]
    · rw [List.getElem?_eq_none (by rw [byteList_length]; omega),
        List.getElem?_eq_none (by rw [byteList_length]; omega)]
  have := byteList_inj this
  rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this

theorem byte_mod (v n k : Nat) (hk : k < n) : ((v % 2 ^ (8 * n)) >>> (8 * k)) % 256 = (v >>> (8 * k)) % 256 := by
  have := byteList_mod v n
  have h1 := byteList_get (v % 2 ^ (8 * n)) n k hk
  rw [this, byteList_get _ _ _ hk] at h1
  exact (Option.some.inj h1).symm

/-! ## 3. Alignment -/

theorem aligned_eq {n a b k : Nat} (ha : a % n = 0) (hb : b % n = 0) (h1 : a ≤ b + k) (h2 : b + k < a + n)
    (hk : k < n) : a = b := by
  have ea := Nat.div_add_mod a n
  have eb := Nat.div_add_mod b n
  rw [ha] at ea; rw [hb] at eb
  have hlt : a / n < b / n + 1 := by
    apply Nat.lt_of_not_le; intro hc
    have := Nat.mul_le_mul_left n hc
    rw [Nat.mul_add, Nat.mul_one] at this
    omega
  have hgt : b / n < a / n + 1 := by
    apply Nat.lt_of_not_le; intro hc
    have := Nat.mul_le_mul_left n hc
    rw [Nat.mul_add, Nat.mul_one] at this
    omega
  have : a / n = b / n := by omega
  rw [← ea, ← eb, this]

/-! ## 4. The image -/

theorem lookup_mapIdx (x : Nat) : ∀ (l : List Nat) (a : Nat),
    (l.mapIdx (fun j b => (a + j, b))).lookup x = if a ≤ x then l[x - a]? else none
  | [], a => by simp
  | b :: l, a => by
    rw [List.mapIdx_cons]
    have hf : (fun (i : Nat) (c : Nat) => (a + (i + 1), c)) = (fun (j : Nat) (c : Nat) => (a + 1 + j, c)) := by
      funext i c; rw [Nat.add_assoc, Nat.add_comm 1 i]
    simp only [List.lookup_cons, Nat.add_zero, hf, lookup_mapIdx x l (a + 1)]
    by_cases hx : x = a
    · subst hx; simp
    · have : (x == a) = false := by simpa using hx
      simp only [this]
      by_cases hax : a ≤ x
      · rw [if_pos (by omega : a + 1 ≤ x), if_pos hax, show x - a = (x - (a + 1)) + 1 by omega]
        simp
      · rw [if_neg (by omega), if_neg hax]

theorem lookup_img (sz : Nat) (a k : Nat) (ha : a % sz = 0) (hk : k < sz) : ∀ L : List (Nat × Nat),
    (∀ p ∈ L, p.1 % sz = 0) →
    ((L.flatMap (fun (a, v) => (byteList v sz).mapIdx (fun k b => (a + k, b)))).lookup (a + k)).getD 0 =
      (((L.lookup a).getD 0) >>> (8 * k)) % 256
  | [], _ => by simp
  | (a', v) :: L, himg => by
    have hp := himg (a', v) (List.mem_cons_self ..)
    have ih := lookup_img sz a k ha hk L (fun q hq => himg q (List.mem_cons_of_mem _ hq))
    rw [List.flatMap_cons, List.lookup_append, List.lookup_cons]
    simp only at hp ⊢
    rw [lookup_mapIdx]
    by_cases he : a' = a
    · subst he
      rw [if_pos (Nat.le_add_right _ _), Nat.add_sub_cancel_left, byteList_get _ _ _ hk]
      simp
    · have hne : (a == a') = false := by
        rw [beq_eq_false_iff_ne]; exact fun h => he h.symm
      rw [hne]
      have : (if a' ≤ a + k then (byteList v sz)[a + k - a']? else none) = none := by
        split
        · rename_i hle
          apply List.getElem?_eq_none
          rw [byteList_length]
          apply Nat.le_of_not_lt; intro hlt
          exact he (aligned_eq hp ha hle (by omega) hk)
        · rfl
      rw [this, Option.none_or]
      exact ih

/-- The full test's byte image at byte `k` of an aligned word `a` is byte `k` of the mini image's word. -/
theorem imgF_toTest (P : MProg) (cond : OC) (himg : ∀ p ∈ P.img, p.1 % P.sz = 0) (a k : Nat)
    (ha : a % P.sz = 0) (hk : k < P.sz) : (P.toTest cond).imgF (a + k) = (P.ini a >>> (8 * k)) % 256 := by
  unfold Test.imgF MProg.ini MProg.img0
  rw [byte_mod _ _ _ hk]
  exact lookup_img P.sz a k ha hk P.img himg

/-! ## 5. THE MEMORY-SIDE CORRESPONDENCE -/

/-- The full execution `E` is the mini event set `A` (access size `sz`, initial words `ini`), byte-wise. -/
structure Corr (sz : Nat) (ini : Nat → Nat) (A : MEvs) (E : IExec) : Prop where
  szpos : 0 < sz
  io : E.T.io = []
  has : ∀ e, E.has e ↔ A.has e
  ev : ∀ e, A.has e → E.ev e = (A.ev e).toEv sz
  gmo : E.gmo = A.gmo
  algn : A.aligned sz
  vlt : ∀ e, A.has e → A.isLd e ∨ A.isSt e → (A.ev e).v < 2 ^ (8 * sz)
  inilt : ∀ a, ini a < 2 ^ (8 * sz)
  img : ∀ a k, a % sz = 0 → k < sz → E.T.imgF (a + k) = (ini a >>> (8 * k)) % 256

section corr

variable {sz : Nat} {ini : Nat → Nat} {A : MEvs} {E : IExec} (H : Corr sz ini A E)
include H

theorem sk_eq {e : EvId} (he : A.has e) : E.sk e = ((A.ev e).toEv sz).sk := by
  unfold IExec.sk; rw [H.ev e he]

theorem kind_eq {e : EvId} (he : A.has e) : (E.sk e).kind = (A.ev e).kind.toKind := by
  rw [sk_eq H he]; rfl

theorem isLoad_iff {e : EvId} (he : A.has e) : (E.sk e).kind.isLoad = true ↔ A.isLd e := by
  rw [kind_eq H he]; unfold MEvs.isLd; cases (A.ev e).kind <;> simp [MK.toKind, Kind.isLoad]

theorem isStore_iff {e : EvId} (he : A.has e) : (E.sk e).kind.isStore = true ↔ A.isSt e := by
  rw [kind_eq H he]; unfold MEvs.isSt; cases (A.ev e).kind <;> simp [MK.toKind, Kind.isStore]

theorem isMemK_iff {e : EvId} (he : A.has e) : (E.sk e).kind.isMem = true ↔ A.isLd e ∨ A.isSt e := by
  rw [kind_eq H he]; unfold MEvs.isSt MEvs.isLd; cases (A.ev e).kind <;> simp [MK.toKind, Kind.isMem]

theorem isMem_iff (e : EvId) : E.isMem e ↔ A.isMem e := by
  unfold IExec.isMem MEvs.isMem
  constructor
  · rintro ⟨h1, h2⟩
    have h1' := (H.has e).1 h1
    exact ⟨h1', (isMemK_iff H h1').1 h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨(H.has e).2 h1, (isMemK_iff H h1).2 h2⟩

theorem sz_mem {e : EvId} (he : A.isMem e) : (E.sk e).sz = sz := by
  rw [sk_eq H he.1]
  rcases he.2 with h | h <;> (simp only [MEvs.isLd, MEvs.isSt] at h; simp [MEv.toEv, h, MK.szOf])

theorem pa_eq {e : EvId} (he : A.has e) : (E.ev e).pa = (A.ev e).pa := by rw [H.ev e he]; rfl

theorem po_iff {a b : EvId} (ha : A.has a) (hb : A.has b) : poS E.sk a b = true ↔ A.po a b := by
  unfold poS MEvs.po
  rw [sk_eq H ha, sk_eq H hb]
  simp [MEv.toEv]

theorem isIoI_f (e : EvId) : E.isIoI e = false := by simp [IExec.isIoI, H.io]

theorem regionOfI_none (e : EvId) : E.regionOfI e = none := by simp [IExec.regionOfI, H.io]

theorem not_isLd_isSt {e : EvId} (h1 : A.isLd e) (h2 : A.isSt e) : False := by
  unfold MEvs.isLd at h1; unfold MEvs.isSt at h2; rw [h1] at h2; cases h2

/-- A has-event writes byte `k` of `r`'s word iff it is a store to `r`'s address. -/
theorem writesB_iff {r w : EvId} (hr : A.isMem r) (hw : A.has w) {k : Nat} (hk : k < sz) :
    writesB (E.ev w) ((A.ev r).pa + k) = true ↔ A.isSt w ∧ (A.ev w).pa = (A.ev r).pa := by
  unfold writesB
  have hst := isStore_iff H hw
  unfold IExec.sk at hst
  rw [Bool.and_eq_true, hst]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    have hwm : A.isMem w := ⟨hw, .inr h1⟩
    have hsz := sz_mem H hwm
    unfold IExec.sk at hsz
    unfold touches at h2
    rw [hsz, pa_eq H hw] at h2
    simp only [decide_eq_true_eq] at h2
    exact aligned_eq (H.algn w hwm) (H.algn r hr) h2.1 h2.2 hk
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    have hsz := sz_mem H ⟨hw, .inr h1⟩
    unfold IExec.sk at hsz
    unfold touches
    rw [hsz, pa_eq H hw, h2]
    simp only [decide_eq_true_eq]; omega

theorem touches_iff {r b : EvId} (hr : A.isMem r) (hb : A.isMem b) {k : Nat} (hk : k < sz) :
    touches (E.ev b) ((A.ev r).pa + k) = true ↔ (A.ev b).pa = (A.ev r).pa := by
  have hsz := sz_mem H hb
  unfold IExec.sk at hsz
  unfold touches
  rw [hsz, pa_eq H hb.1]
  simp only [decide_eq_true_eq]
  constructor
  · intro h; exact aligned_eq (H.algn b hb) (H.algn r hr) h.1 h.2 hk
  · intro h; rw [h]; omega

theorem candI_iff {r : EvId} (hr : A.isMem r) {k : Nat} (hk : k < sz) (w : EvId) :
    E.candI r ((A.ev r).pa + k) w ↔ A.cand r w := by
  unfold IExec.candI MEvs.cand
  rw [H.has w, H.gmo]
  constructor
  · rintro ⟨hw, h1, h2⟩
    have := (writesB_iff H hr hw hk).1 h1
    exact ⟨hw, this.1, this.2, h2.imp id (fun h => (po_iff H hw hr.1).1 h)⟩
  · rintro ⟨hw, h1, h2, h3⟩
    exact ⟨hw, (writesB_iff H hr hw hk).2 ⟨h1, h2⟩, h3.imp id (fun h => (po_iff H hw hr.1).2 h)⟩

theorem rfI_iff {r : EvId} (hr : A.isMem r) {k : Nat} (hk : k < sz) (o : Option EvId) :
    E.rfI r ((A.ev r).pa + k) o ↔ A.rf r o := by
  cases o with
  | none => simp only [IExec.rfI, MEvs.rf, candI_iff H hr hk]
  | some w => simp only [IExec.rfI, MEvs.rf, candI_iff H hr hk, H.gmo]

/-- The value a source gives byte `k` of load `r`. -/
theorem valI_eq {r : EvId} (hr : A.isMem r) {k : Nat} (hk : k < sz) {o : Option EvId} (ho : A.rf r o) :
    E.valI ((A.ev r).pa + k) o = (A.valOf ini r o >>> (8 * k)) % 256 := by
  cases o with
  | none => exact H.img _ _ (H.algn r hr) hk
  | some w =>
    obtain ⟨⟨hw, hst, hpa, _⟩, _⟩ := ho
    show wbyte (E.ev w) _ = _
    unfold wbyte
    rw [H.ev w hw]
    simp only [MEvs.isSt] at hst
    simp only [MEv.toEv, hst, if_true, hpa, Nat.add_sub_cancel_left, byteList_get _ _ _ hk, Option.getD_some,
      MEvs.valOf]

theorem rf_unique (hg : A.gmoOk) {r : EvId} {o1 o2 : Option EvId} (h1 : A.rf r o1) (h2 : A.rf r o2) : o1 = o2 := by
  cases o1 with
  | none => cases o2 with
    | none => rfl
    | some w => exact absurd h2.1 (h1 w)
  | some w1 => cases o2 with
    | none => exact absurd h1.1 (h2 w1)
    | some w2 =>
      rcases h1.2 w2 h2.1 with e | e
      · rw [e]
      · rcases h2.2 w1 h1.1 with e' | e'
        · rw [e']
        · exact absurd (hg.2.2.1 _ _ _ e e') (hg.2.1 _)

theorem gmoOk_iff : E.gmoOk ↔ A.gmoOk := by
  unfold IExec.gmoOk MEvs.gmoOk
  simp only [isMem_iff H, H.gmo]

theorem progress_iff : E.progressAxI ↔ A.progressAx := by
  unfold IExec.progressAxI MEvs.progressAx
  simp only [isMem_iff H, H.gmo]

theorem evWfI_true : E.evWfI := by
  intro e he
  have he' := (H.has e).1 he
  unfold IExec.sk
  rw [H.ev e he']
  constructor
  · intro hl
    have : (A.ev e).kind = .ld := by
      revert hl; simp only [MEv.toEv]; cases (A.ev e).kind <;> simp [MK.toKind, Kind.isLoad]
    simp [MEv.toEv, this, byteList_length, MK.szOf]
  · intro hs
    have : (A.ev e).kind = .st := by
      revert hs; simp only [MEv.toEv]; cases (A.ev e).kind <;> simp [MK.toKind, Kind.isStore]
    simp [MEv.toEv, this, byteList_length, MK.szOf]

theorem pairedI_false (a b : EvId) (ha : A.has a) : ¬ E.pairedI a b := by
  rintro ⟨h, _⟩
  rw [kind_eq H ha] at h
  cases hk : (A.ev a).kind <;> rw [hk] at h <;> cases h

theorem atomicity_true : E.atomicityAxI := by
  intro r w hr _ hp
  exact absurd hp (pairedI_false H r w ((H.has r).1 hr))

theorem scAx_true : E.scAxI := by
  intro w hw hk
  have hw' := (H.has w).1 hw
  rw [kind_eq H hw'] at hk
  cases h : (A.ev w).kind <;> rw [h] at hk <;> cases hk

theorem loadValue_iff (hg : A.gmoOk) : E.loadValueAxI ↔ A.loadValueAx ini := by
  unfold IExec.loadValueAxI MEvs.loadValueAx
  constructor
  · intro hL r hr hl
    have hr' := (H.has r).2 hr
    have hrm : A.isMem r := ⟨hr, .inl hl⟩
    have hlf := (isLoad_iff H hr).2 hl
    have hsz := sz_mem H hrm
    have h0 := hL r hr' hlf (isIoI_f H r) 0 (by rw [hsz]; exact H.szpos)
    rw [pa_eq H hr] at h0
    obtain ⟨o, ho, _⟩ := h0
    have ho' := (rfI_iff H hrm H.szpos o).1 ho
    refine ⟨o, ho', ?_⟩
    have hvo : A.valOf ini r o < 2 ^ (8 * sz) := by
      cases o with
      | none => exact H.inilt _
      | some w => exact H.vlt w ho'.1.1 (.inr ho'.1.2.1)
    apply eq_of_bytes (H.vlt r hr (.inl hl)) hvo
    intro k hk
    obtain ⟨o', ho1, ho2⟩ := hL r hr' hlf (isIoI_f H r) k (by rw [hsz]; exact hk)
    rw [pa_eq H hr] at ho1 ho2
    have ho1' := (rfI_iff H hrm hk o').1 ho1
    have := rf_unique H hg ho1' ho'
    subst this
    rw [valI_eq H hrm hk ho1', H.ev r hr] at ho2
    unfold MEvs.isLd at hl
    simp only [MEv.toEv, hl, if_true, byteList_get _ _ _ hk] at ho2
    exact Option.some.inj ho2
  · intro hL r hr' hlf _ k hk
    have hr := (H.has r).1 hr'
    have hl := (isLoad_iff H hr).1 hlf
    have hrm : A.isMem r := ⟨hr, .inl hl⟩
    rw [sz_mem H hrm] at hk
    obtain ⟨o, ho, hv⟩ := hL r hr hl
    refine ⟨o, ?_, ?_⟩
    · rw [pa_eq H hr]; exact (rfI_iff H hrm hk o).2 ho
    · rw [pa_eq H hr, valI_eq H hrm hk ho, ← hv, H.ev r hr]
      unfold MEvs.isLd at hl
      simp only [MEv.toEv, hl, if_true, byteList_get _ _ _ hk]

theorem rule1_iff {a b : EvId} (ha : A.isMem a) (hb : A.isMem b) : E.rule1I a b ↔ A.rule1 a b := by
  unfold IExec.rule1I MEvs.rule1 overlapB
  rw [isStore_iff H hb.1, pa_eq H ha.1, pa_eq H hb.1]
  have h1 := sz_mem H ha; have h2 := sz_mem H hb
  unfold IExec.sk at h1 h2
  rw [h1, h2]
  simp only [decide_eq_true_eq]
  constructor
  · rintro ⟨hs, h3, h4⟩
    refine ⟨hs, ?_⟩
    rcases Nat.le_total (A.ev a).pa (A.ev b).pa with h | h
    · exact aligned_eq (H.algn a ha) (H.algn b hb) (k := 0) (by omega) (by omega) H.szpos
    · exact (aligned_eq (H.algn b hb) (H.algn a ha) (k := 0) (by omega) (by omega) H.szpos).symm
  · rintro ⟨hs, h3⟩
    refine ⟨hs, ?_, ?_⟩ <;> rw [h3] <;> have := H.szpos <;> omega

theorem rule2_iff {a b : EvId} (ha : A.isMem a) (hb : A.isMem b) : E.rule2I a b ↔ A.rule2 a b := by
  unfold IExec.rule2I MEvs.rule2
  rw [isLoad_iff H ha.1, isLoad_iff H hb.1, isIoI_f H a, isIoI_f H b, sz_mem H ha, pa_eq H ha.1]
  constructor
  · rintro ⟨hla, hlb, _, _, k, hk, ht, hm, oa, ob, h1, h2, hne⟩
    have hpa := (touches_iff H ha hb hk).1 ht
    refine ⟨hla, hlb, hpa.symm, fun m hm' h3 h4 hc => ?_, oa, ob, (rfI_iff H ha hk oa).1 h1, ?_, hne⟩
    · have := hm m ((H.has m).2 hm') ((po_iff H ha.1 hm').2 h3) ((po_iff H hm' hb.1).2 h4)
      rw [(writesB_iff H ha hm' hk).2 hc] at this; cases this
    · rw [← hpa] at h2; exact (rfI_iff H hb hk ob).1 h2
  · rintro ⟨hla, hlb, hpa, hm, oa, ob, h1, h2, hne⟩
    refine ⟨hla, hlb, rfl, rfl, 0, H.szpos, (touches_iff H ha hb H.szpos).2 hpa.symm, fun m hm' h3 h4 => ?_,
      oa, ob, (rfI_iff H ha H.szpos oa).2 h1, ?_, hne⟩
    · have hm'' := (H.has m).1 hm'
      cases hw : writesB (E.ev m) ((A.ev a).pa + 0)
      · rfl
      · exact absurd ((writesB_iff H ha hm'' H.szpos).1 hw) (hm m hm'' ((po_iff H ha.1 hm'').1 h3)
          ((po_iff H hm'' hb.1).1 h4))
    · rw [hpa]; exact (rfI_iff H hb H.szpos ob).2 h2

theorem rule3_false (a b : EvId) (ha : A.has a) : ¬ E.rule3I a b := by
  rintro ⟨h, _⟩
  rw [kind_eq H ha] at h
  cases hk : (A.ev a).kind <;> rw [hk] at h <;> cases h

theorem inPred_iff {f : MFence} {a : EvId} (ha : A.has a) :
    inPred E.sk E.isIoI f.toFenceSet a = true ↔ A.inPred f a := by
  unfold inPred MEvs.inPred
  rw [isIoI_f H a]
  have h1 := isLoad_iff H ha; have h2 := isStore_iff H ha
  cases hl : (E.sk a).kind.isLoad <;> cases hs : (E.sk a).kind.isStore <;>
    simp_all [MFence.toFenceSet] <;> (try exact not_isLd_isSt H h1 h2) <;> simp_all

theorem inSucc_iff {f : MFence} {a : EvId} (ha : A.has a) :
    inSucc E.sk E.isIoI f.toFenceSet a = true ↔ A.inSucc f a := by
  unfold inSucc MEvs.inSucc
  rw [isIoI_f H a]
  have h1 := isLoad_iff H ha; have h2 := isStore_iff H ha
  cases hl : (E.sk a).kind.isLoad <;> cases hs : (E.sk a).kind.isStore <;>
    simp_all [MFence.toFenceSet] <;> (try exact not_isLd_isSt H h1 h2) <;> simp_all

theorem rule4_iff {a b : EvId} (ha : A.has a) (hb : A.has b) : E.rule4I a b ↔ A.rule4 a b := by
  unfold IExec.rule4I MEvs.rule4
  constructor
  · rintro ⟨m, f, hm, hk, h1, h2, h3, h4⟩
    have hm' := (H.has m).1 hm
    rw [kind_eq H hm'] at hk
    cases hmk : (A.ev m).kind with
    | ld => rw [hmk] at hk; cases hk
    | st => rw [hmk] at hk; cases hk
    | fence g =>
      rw [hmk] at hk
      simp only [MK.toKind, Kind.fence.injEq] at hk
      subst hk
      exact ⟨m, g, hm', hmk, (po_iff H ha hm').1 h1, (po_iff H hm' hb).1 h2, (inPred_iff H ha).1 h3,
        (inSucc_iff H hb).1 h4⟩
  · rintro ⟨m, f, hm, hk, h1, h2, h3, h4⟩
    refine ⟨m, f.toFenceSet, (H.has m).2 hm, by rw [kind_eq H hm, hk]; rfl, (po_iff H ha hm).2 h1,
      (po_iff H hm hb).2 h2, (inPred_iff H ha).2 h3, (inSucc_iff H hb).2 h4⟩

theorem rule5_f {a b : EvId} (ha : A.has a) : rule5 E.sk E.isIoI a b = false := by
  simp [rule5, sk_eq H ha, MEv.toEv]

theorem rule6_f {a b : EvId} (hb : A.has b) : rule6 E.sk E.isIoI a b = false := by
  simp [rule6, sk_eq H hb, MEv.toEv]

theorem rule7_f {a b : EvId} (ha : A.has a) : rule7 E.sk E.isIoI a b = false := by
  simp [rule7, sk_eq H ha, MEv.toEv]

theorem rule9_iff {a b : EvId} (hb : A.has b) : rule9 E.sk a b = true ↔ A.rule9 a b := by
  simp [rule9, MEvs.rule9, sk_eq H hb, MEv.toEv]

theorem rule10_iff {a b : EvId} (hb : A.has b) : rule10 E.sk a b = true ↔ A.rule10 a b := by
  unfold rule10 MEvs.rule10
  have := isStore_iff H hb
  unfold IExec.sk at this
  simp only [Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem, IExec.sk, this]
  rw [H.ev b hb]; exact and_assoc

theorem rule11_iff {a b : EvId} (hb : A.has b) : rule11 E.sk a b = true ↔ A.rule11 a b := by
  unfold rule11 MEvs.rule11
  have := isStore_iff H hb
  unfold IExec.sk at this
  simp only [Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem, IExec.sk, this]
  rw [H.ev b hb]; exact and_assoc

theorem adep_eq {m : EvId} (hm : A.has m) : (E.sk m).adep = (A.ev m).adep := by rw [sk_eq H hm]; rfl

theorem ddep_eq {m : EvId} (hm : A.has m) : (E.sk m).ddep = (A.ev m).ddep := by rw [sk_eq H hm]; rfl

theorem rule12_iff {a b : EvId} (ha : A.has a) (hb : A.isMem b) : E.rule12I a b ↔ A.rule12 a b := by
  unfold IExec.rule12I MEvs.rule12
  rw [isLoad_iff H hb.1, isIoI_f H b, sz_mem H hb]
  constructor
  · rintro ⟨hl, _, m, hm, h1, h2, h3, h4, k, hk, h5⟩
    have hm' := (H.has m).1 hm
    refine ⟨hl, m, hm', (po_iff H ha hm').1 h1, (po_iff H hm' hb.1).1 h2, (isStore_iff H hm').1 h3, ?_, ?_⟩
    · rw [adep_eq H hm', ddep_eq H hm'] at h4; simpa [List.contains_iff_mem] using h4
    · rw [pa_eq H hb.1] at h5; exact (rfI_iff H hb hk _).1 h5
  · rintro ⟨hl, m, hm, h1, h2, h3, h4, h5⟩
    refine ⟨hl, rfl, m, (H.has m).2 hm, (po_iff H ha hm).2 h1, (po_iff H hm hb.1).2 h2, (isStore_iff H hm).2 h3,
      ?_, 0, H.szpos, ?_⟩
    · rw [adep_eq H hm, ddep_eq H hm]; simpa [List.contains_iff_mem] using h4
    · rw [pa_eq H hb.1]; exact (rfI_iff H hb H.szpos _).2 h5

theorem rule13_iff {a b : EvId} (ha : A.has a) (hb : A.has b) : E.rule13I a b ↔ A.rule13 a b := by
  unfold IExec.rule13I MEvs.rule13
  rw [isStore_iff H hb]
  constructor
  · rintro ⟨hs, m, hm, hk, h1, h2, h3⟩
    have hm' := (H.has m).1 hm
    refine ⟨hs, m, ⟨hm', (isMemK_iff H hm').1 hk⟩, (po_iff H ha hm').1 h1, (po_iff H hm' hb).1 h2, ?_⟩
    rw [adep_eq H hm'] at h3; simpa [List.contains_iff_mem] using h3
  · rintro ⟨hs, m, ⟨hm, hk⟩, h1, h2, h3⟩
    refine ⟨hs, m, (H.has m).2 hm, (isMemK_iff H hm).2 hk, (po_iff H ha hm).2 h1, (po_iff H hm hb).2 h2, ?_⟩
    rw [adep_eq H hm]; simpa [List.contains_iff_mem] using h3

theorem ppo_iff (a b : EvId) : E.ppoI a b ↔ A.ppo a b := by
  unfold IExec.ppoI MEvs.ppo
  rw [isMem_iff H a, isMem_iff H b]
  constructor
  · rintro ⟨ha, hb, hpo, hr⟩
    refine ⟨ha, hb, (po_iff H ha.1 hb.1).1 hpo, ?_⟩
    unfold IExec.staticI at hr
    rw [rule1_iff H ha hb, rule2_iff H ha hb, rule4_iff H ha.1 hb.1, rule5_f H ha.1, rule6_f H hb.1,
      rule7_f H ha.1, rule9_iff H hb.1, rule10_iff H hb.1, rule11_iff H hb.1, rule13_iff H ha.1 hb.1,
      rule12_iff H ha.1 hb] at hr
    rcases hr with h | h | h | h | h
    · exact .inl h
    · exact .inr (.inl h)
    · exact absurd h (rule3_false H a b ha.1)
    · rcases h with h | h | h | h | h | h | h | h | h
      · exact .inr (.inr (.inl h))
      · cases h
      · cases h
      · cases h
      · exact absurd h (pairedI_false H a b ha.1)
      · exact .inr (.inr (.inr (.inl h)))
      · exact .inr (.inr (.inr (.inr (.inl h))))
      · exact .inr (.inr (.inr (.inr (.inr (.inl h)))))
      · exact .inr (.inr (.inr (.inr (.inr (.inr (.inr h))))))
    · exact .inr (.inr (.inr (.inr (.inr (.inr (.inl h))))))
  · rintro ⟨ha, hb, hpo, hr⟩
    refine ⟨ha, hb, (po_iff H ha.1 hb.1).2 hpo, ?_⟩
    unfold IExec.staticI
    rw [rule1_iff H ha hb, rule2_iff H ha hb, rule4_iff H ha.1 hb.1, rule9_iff H hb.1, rule10_iff H hb.1,
      rule11_iff H hb.1, rule13_iff H ha.1 hb.1, rule12_iff H ha.1 hb]
    rcases hr with h | h | h | h | h | h | h | h
    · exact .inl h
    · exact .inr (.inl h)
    · exact .inr (.inr (.inr (.inl (.inl h))))
    · exact .inr (.inr (.inr (.inl (.inr (.inr (.inr (.inr (.inr (.inl h)))))))))
    · exact .inr (.inr (.inr (.inl (.inr (.inr (.inr (.inr (.inr (.inr (.inl h))))))))))
    · exact .inr (.inr (.inr (.inl (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl h)))))))))))
    · exact .inr (.inr (.inr (.inr h)))
    · exact .inr (.inr (.inr (.inl (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr h)))))))))))

theorem ppoAx_iff : E.ppoAxI ↔ A.ppoAx := by
  unfold IExec.ppoAxI MEvs.ppoAx
  have hio : ∀ a b, ¬ E.ioOrdI a b := by
    intro a b ⟨_, _, _, h⟩
    rw [regionOfI_none H a] at h; exact h
  rw [H.gmo]
  constructor
  · intro h a b hp; exact h a b (.inl ((ppo_iff H a b).2 hp))
  · intro h a b hp
    rcases hp with hp | hp
    · exact h a b ((ppo_iff H a b).1 hp)
    · exact absurd hp (hio a b)

/-- **THE MEMORY SIDE OF E1**: on F's word events, the full reference's axioms are MiniRef's axiom block. -/
theorem corr_iff : E.rvwmoRefInf ↔ A.ax ini := by
  unfold IExec.rvwmoRefInf MEvs.ax
  constructor
  · rintro ⟨hg, _, hp, hl, _, _, hpr⟩
    have hg' := (gmoOk_iff H).1 hg
    exact ⟨hg', (ppoAx_iff H).1 hp, (loadValue_iff H hg').1 hl, (progress_iff H).1 hpr⟩
  · rintro ⟨hg, hp, hl, hpr⟩
    exact ⟨(gmoOk_iff H).2 hg, evWfI_true H, (ppoAx_iff H).2 hp, (loadValue_iff H hg).2 hl, atomicity_true H,
      scAx_true H, (progress_iff H).2 hpr⟩

end corr

end Weak.Mini
