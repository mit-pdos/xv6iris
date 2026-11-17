/-
Weak/Mini: **E2 part 1 — words and bytes** (mini plan rev 4 §2 L2, E2; §5 Q1: "byte↔word cost paid once in E1/E2").

The embedding of MiniMach's words into machine v2's byte runs: `wordB P v` (the `sz` little-endian bytes of an
`sz`-byte word; an out-of-range value — never in a valid run — goes to a byte run of the WRONG length, so the
embedding is injective), messages `embMsg`, and the facts the simulation needs: round trips `toBytes`/`ofBytes`,
alignment, the image's bytes (`testImg_word`), a good message's bytes (`byteAt_emb`), and the byte-level
`memByte`/`writesIn` of an embedded log at a word.
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Mini.EqProg
import Weak.Mini.Mach

namespace MiniEq

open Weak.Prom Weak.Prom.Mach
open Weak.Prom.Ref (byteList bytesVal Test)
open Weak.Mini

/-! ## 1. Round trips -/

theorem tb_len (v n : Nat) : (toBytes v n).length = n := by simp [toBytes, byteList]

theorem byteList_succ (v n : Nat) : byteList v (n + 1) = v % 256 :: byteList (v / 256) n := by
  simp only [byteList, List.range_succ_eq_map, List.map_cons, List.map_map]
  rw [List.cons.injEq]
  refine ⟨by simp, ?_⟩
  · apply List.map_congr_left
    intro k _
    have h8 : 2 ^ (8 * (k + 1)) = 256 * 2 ^ (8 * k) := by
      rw [show 8 * (k + 1) = 8 + 8 * k by omega, Nat.pow_add]
    simp only [Function.comp, Nat.shiftRight_eq_div_pow, h8, Nat.div_div_eq_div_mul]

theorem tb_succ (v n : Nat) : toBytes v (n + 1) = bv8 (v % 256) :: toBytes (v / 256) n := by
  simp only [toBytes, byteList_succ, List.map_cons]

theorem bytesVal_byteList : ∀ (n v : Nat), bytesVal (byteList v n) = v % 2 ^ (8 * n)
  | 0, v => by simp [byteList, bytesVal, Nat.mod_one]
  | n + 1, v => by
    rw [byteList_succ]
    simp only [bytesVal, List.foldr_cons]
    have ih := bytesVal_byteList n (v / 256)
    simp only [bytesVal] at ih
    rw [ih, show 8 * (n + 1) = 8 + 8 * n by omega, Nat.pow_add, Nat.mod_mul]

theorem bv8_toNat (b : Nat) : (bv8 b).toNat = b % 256 := by simp [bv8]

theorem ofBytes_toBytes (v n : Nat) : ofBytes (toBytes v n) = v % 2 ^ (8 * n) := by
  have h : ((byteList v n).map bv8).map BitVec.toNat = byteList v n := by
    rw [List.map_map]
    conv => rhs; rw [← List.map_id (byteList v n)]
    apply List.map_congr_left
    intro b hb
    simp only [Function.comp, bv8_toNat, id]
    obtain ⟨k, _, rfl⟩ := List.mem_map.1 hb
    exact Nat.mod_mod _ _
  simp only [ofBytes, toBytes, h, bytesVal_byteList]

theorem ofBytes_cons (b : BitVec 8) (bs : List (BitVec 8)) : ofBytes (b :: bs) = b.toNat + 256 * ofBytes bs := by
  simp [ofBytes, bytesVal]

theorem toBytes_ofBytes : ∀ (bs : List (BitVec 8)), toBytes (ofBytes bs) bs.length = bs
  | [] => rfl
  | b :: bs => by
    rw [List.length_cons, tb_succ, ofBytes_cons]
    have hb := b.isLt
    have h1 : (b.toNat + 256 * ofBytes bs) % 256 = b.toNat := by omega
    have h2 : (b.toNat + 256 * ofBytes bs) / 256 = ofBytes bs := by omega
    rw [h1, h2, toBytes_ofBytes bs]
    congr 1
    apply BitVec.eq_of_toNat_eq
    simp only [bv8_toNat]; omega

theorem ofBytes_lt : ∀ (bs : List (BitVec 8)), ofBytes bs < 2 ^ (8 * bs.length)
  | [] => by simp [ofBytes, bytesVal]
  | b :: bs => by
    rw [ofBytes_cons, List.length_cons, show 8 * (bs.length + 1) = 8 + 8 * bs.length by omega, Nat.pow_add]
    have := ofBytes_lt bs
    have hb := b.isLt
    simp only [show (2 : Nat) ^ 8 = 256 from rfl]
    omega

theorem toBytes_mod (v n : Nat) : toBytes v n = toBytes (v % 2 ^ (8 * n)) n := by
  have h := toBytes_ofBytes (toBytes v n)
  rw [tb_len, ofBytes_toBytes] at h
  exact h.symm

theorem toBytes_inj {v w n : Nat} (hv : v < 2 ^ (8 * n)) (hw : w < 2 ^ (8 * n)) (h : toBytes v n = toBytes w n) :
    v = w := by
  have := congrArg ofBytes h
  rwa [ofBytes_toBytes, ofBytes_toBytes, Nat.mod_eq_of_lt hv, Nat.mod_eq_of_lt hw] at this

theorem toBytes_getElem? (v n k : Nat) (hk : k < n) : (toBytes v n)[k]? = some (bv8 ((v >>> (8 * k)) % 256)) := by
  simp [toBytes, byteList, hk]

/-! ## 2. Words as byte runs -/

/-- THE WORD EMBEDDING: an `sz`-byte word as its little-endian bytes; an out-of-range value (never in a valid run)
as a byte run of a different length, so that `wordB` is injective. -/
def wordB (P : MProg) (v : Nat) : List (BitVec 8) :=
  if v < Mach.wordW P then toBytes v P.sz else toBytes v (P.sz + 1 + v)

theorem wordB_lt {P : MProg} {v : Nat} (h : v < Mach.wordW P) : wordB P v = toBytes v P.sz := if_pos h

theorem wordB_len {P : MProg} {v : Nat} : (wordB P v).length = P.sz ↔ v < Mach.wordW P := by
  unfold wordB
  split
  · next h => simp [tb_len, h]
  · next h => simp [tb_len, h]; omega

theorem wordB_inj {P : MProg} {v w : Nat} (h : wordB P v = wordB P w) : v = w := by
  by_cases hv : v < Mach.wordW P <;> by_cases hw : w < Mach.wordW P
  · rw [wordB_lt hv, wordB_lt hw] at h; exact toBytes_inj hv hw h
  · have := congrArg List.length h; rw [wordB_len.2 hv] at this; exact absurd (wordB_len.1 this.symm) hw
  · have := congrArg List.length h; rw [wordB_len.2 hw] at this; exact absurd (wordB_len.1 this) hv
  · unfold wordB at h; rw [if_neg hv, if_neg hw] at h
    have := congrArg List.length h; simp only [tb_len] at this; omega

theorem ofBytes_wordB (P : MProg) (v : Nat) : ofBytes (wordB P v) = v := by
  unfold wordB
  split
  · next h => rw [ofBytes_toBytes]; exact Nat.mod_eq_of_lt h
  · rw [ofBytes_toBytes, Nat.mod_eq_of_lt]
    exact Nat.lt_of_lt_of_le Nat.lt_two_pow_self (Nat.pow_le_pow_right (by omega) (by omega))

theorem wordB_ne_nil {P : MProg} (hsz : 0 < P.sz) (v : Nat) : wordB P v ≠ [] := by
  intro h; have := congrArg List.length h; unfold wordB at this; split at this <;> simp [tb_len] at this <;> omega

/-- The full machine's bytes of a stored register value are the word's (`toBytes (rd rs2) sz`, MachCert.lean:74). -/
theorem wordW_pos (P : MProg) : 0 < Mach.wordW P := Nat.two_pow_pos _

theorem wordB_mod (P : MProg) (x : Nat) : wordB P (x % Mach.wordW P) = toBytes x P.sz := by
  rw [wordB_lt (Nat.mod_lt _ (wordW_pos P)), toBytes_mod x P.sz]; rfl

/-! ## 3. Alignment -/

theorem aligned_sep {n a b : Nat} (ha : a % n = 0) (hb : b % n = 0) (h : a < b) : a + n ≤ b := by
  have e1 := Nat.div_add_mod a n
  have e2 := Nat.div_add_mod b n
  rw [ha] at e1; rw [hb] at e2
  have : a / n < b / n := by
    rcases Nat.lt_or_ge (a / n) (b / n) with h' | h'
    · exact h'
    · have := Nat.mul_le_mul_left n h'; omega
  have := Nat.mul_le_mul_left n (Nat.succ_le_of_lt this)
  rw [Nat.mul_succ] at this
  omega

theorem aligned_eq {n a b k : Nat} (ha : a % n = 0) (hb : b % n = 0) (hk : k < n) (h1 : a ≤ b + k)
    (h2 : b + k < a + n) : a = b := by
  rcases Nat.lt_trichotomy a b with h | h | h
  · have := aligned_sep ha hb h; omega
  · exact h
  · have := aligned_sep hb ha h; omega

/-! ## 4. Messages -/

/-- A message as a machine v2 message (class `plain`, author `some tid`). -/
def embMsg (P : MProg) (m : Mach.MMsg) : PMsg := ⟨(m.pa : Int), wordB P m.v, some m.tid, .plain⟩

/-- A GOOD mini message: an aligned word. -/
def goodM (P : MProg) (m : Mach.MMsg) : Prop := m.pa % P.sz = 0 ∧ m.v < Mach.wordW P

/-- A GOOD full message: the embedding of a good mini message. -/
def good (P : MProg) (m : PMsg) : Prop := ∃ mm, m = embMsg P mm ∧ goodM P mm

theorem embMsg_inj {P : MProg} {m1 m2 : Mach.MMsg} (h : embMsg P m1 = embMsg P m2) : m1 = m2 := by
  simp only [embMsg, PMsg.mk.injEq, Int.ofNat_inj, Option.some.injEq] at h
  obtain ⟨h1, h2, h3, -⟩ := h
  cases m1; cases m2
  simp only at h1 h2 h3
  rw [h1, wordB_inj h2, h3]

theorem byteAt_emb {P : MProg} {m : Mach.MMsg} (hm : goodM P m) {a k : Nat} (ha : a % P.sz = 0) (hk : k < P.sz) :
    (embMsg P m).byteAt ((a + k : Nat) : Int) = if m.pa = a then (toBytes m.v P.sz)[k]? else none := by
  unfold PMsg.byteAt embMsg
  simp only [wordB_lt hm.2]
  by_cases hpa : m.pa = a
  · rw [if_pos hpa, if_pos (show ((m.pa : Nat) : Int) ≤ ((a + k : Nat) : Int) by omega)]
    congr 1; omega
  · rw [if_neg hpa]
    split
    · next hle =>
      have hle' : m.pa ≤ a + k := by omega
      have hlt : m.pa < a := by
        rcases Nat.lt_or_ge m.pa a with h | h
        · exact h
        · have h2 : a < m.pa := by omega
          have := aligned_sep ha hm.1 h2
          omega
      have := aligned_sep hm.1 ha hlt
      rw [List.getElem?_eq_none]
      rw [tb_len]; omega
    · rfl

theorem byteAt_emb_isSome {P : MProg} {m : Mach.MMsg} (hm : goodM P m) {a k : Nat} (ha : a % P.sz = 0)
    (hk : k < P.sz) : ((embMsg P m).byteAt ((a + k : Nat) : Int)).isSome = true ↔ m.pa = a := by
  rw [byteAt_emb hm ha hk]
  split
  · next h => simp [h, toBytes_getElem? _ _ _ hk]
  · next h => simp [h]

/-! ## 5. The image -/

theorem lookup_range (x a : Nat) (g : Nat → Nat) : ∀ n,
    ((List.range n).map (fun j => (a + j, g j))).lookup x = if a ≤ x ∧ x < a + n then some (g (x - a)) else none
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ, List.map_append, List.lookup_append, lookup_range x a g n]
    by_cases h : a ≤ x ∧ x < a + n
    · rw [if_pos h, if_pos (show a ≤ x ∧ x < a + (n + 1) by omega)]; rfl
    · rw [if_neg h]
      simp only [List.map_cons, List.map_nil, List.lookup_singleton, Option.none_or]
      by_cases hx : x = a + n
      · subst hx; simp
      · have h1 : ¬ (a ≤ x ∧ x < a + (n + 1)) := by omega
        have h2 : (x == a + n) = false := by simp [hx]
        simp [h1, h2]

theorem imgBytes_block (P : MProg) (a v : Nat) :
    (byteList v P.sz).mapIdx (fun k b => (a + k, b)) =
      (List.range P.sz).map (fun j => (a + j, (v >>> (8 * j)) % 256)) := by
  apply List.ext_getElem?
  intro j
  simp only [List.getElem?_mapIdx, List.getElem?_map, byteList]
  by_cases hj : j < P.sz <;> simp [hj]

theorem imgBytes_lookup (P : MProg) (hwf : Mach.progWf P) {a k : Nat} (ha : a % P.sz = 0) (hk : k < P.sz) :
    P.imgBytes.lookup (a + k) = (P.img.lookup a).map (fun v => (v >>> (8 * k)) % 256) := by
  unfold MProg.imgBytes
  have himg := hwf.2
  generalize P.img = img at himg ⊢
  induction img with
  | nil => rfl
  | cons p rest ih =>
    obtain ⟨a', v'⟩ := p
    rw [List.flatMap_cons]
    dsimp only
    rw [List.lookup_append, imgBytes_block, lookup_range,
      ih (fun q hq => himg q (List.mem_cons_of_mem _ hq))]
    have ha' : a' % P.sz = 0 := himg _ (List.mem_cons_self ..)
    by_cases he : a' = a
    · subst he
      rw [if_pos (show a' ≤ a' + k ∧ a' + k < a' + P.sz by omega)]
      simp [show a' + k - a' = k by omega, List.lookup]
    · rw [if_neg (fun h => he (aligned_eq ha' ha hk h.1 h.2))]
      have : (a == a') = false := by simp; omega
      simp only [Option.none_or, List.lookup, this]

/-- THE IMAGE AT A WORD: byte `k` of the aligned word `a` is byte `k` of `img0 a` (the word image, Prog.lean). -/
theorem testImg_word (P : MProg) (hwf : Mach.progWf P) (cond : Weak.Prom.Ref.OC) {a k : Nat} (ha : a % P.sz = 0)
    (hk : k < P.sz) : testImg (P.toTest cond) ((a + k : Nat) : Int) = (toBytes (P.img0 a % Mach.wordW P) P.sz)[k]? := by
  rw [show Mach.wordW P = 2 ^ (8 * P.sz) from rfl, ← toBytes_mod, toBytes_getElem? _ _ _ hk]
  simp only [testImg, Test.imgF, MProg.toTest, Int.toNat_natCast, imgBytes_lookup P hwf ha hk, MProg.img0]
  cases P.img.lookup a <;> simp

/-! ## 6. Embedded logs at a word -/

/-- The word answers of a mini load are bounded (image words mod `2^(8 sz)`, good messages). -/
theorem memv_lt {P : MProg} {log : List Mach.MMsg} (hg : ∀ m ∈ log, goodM P m) {t a w : Nat}
    (h : Mach.memv P log t a = some w) : w < Mach.wordW P := by
  cases t with
  | zero => simp only [Mach.memv, Option.some.injEq] at h; subst h
            exact Nat.mod_lt _ (wordW_pos P)
  | succ t =>
    simp only [Mach.memv] at h
    split at h
    · next m hm =>
      split at h
      · cases h; exact (hg m (List.mem_of_getElem? hm)).2
      · cases h
    · cases h

theorem memByte_word (P : MProg) (hwf : Mach.progWf P) (cond : Weak.Prom.Ref.OC) {log : List Mach.MMsg}
    (hg : ∀ m ∈ log, goodM P m) {a k : Nat} (ha : a % P.sz = 0) (hk : k < P.sz) (t : Nat) :
    memByte (testImg (P.toTest cond)) (log.map (embMsg P)) t ((a + k : Nat) : Int) =
      (Mach.memv P log t a).bind (fun w => (toBytes w P.sz)[k]?) := by
  cases t with
  | zero => simp only [memByte, testImg_word P hwf cond ha hk, Mach.memv, Option.bind_some]
  | succ t =>
    simp only [memByte, List.getElem?_map, Mach.memv]
    cases hm : log[t]? with
    | none => rfl
    | some m =>
      simp only [Option.map_some, Option.bind_some]
      rw [byteAt_emb (hg m (List.mem_of_getElem? hm)) ha hk]
      split <;> simp

theorem writesIn_word (P : MProg) {log : List Mach.MMsg} (hg : ∀ m ∈ log, goodM P m) {a k : Nat}
    (ha : a % P.sz = 0) (hk : k < P.sz) (lo hi : Nat) :
    Weak.Prom.writesIn (log.map (embMsg P)) ((a + k : Nat) : Int) lo hi ↔ Mach.writesIn log a lo hi := by
  unfold Weak.Prom.writesIn Mach.writesIn
  constructor
  · rintro ⟨t, h1, h2, m, hm, hs⟩
    rw [List.getElem?_map] at hm
    obtain ⟨mm, hmm, rfl⟩ := Option.map_eq_some_iff.1 hm
    exact ⟨t, h1, h2, mm, hmm, (byteAt_emb_isSome (hg mm (List.mem_of_getElem? hmm)) ha hk).1 hs⟩
  · rintro ⟨t, h1, h2, mm, hmm, hpa⟩
    refine ⟨t, h1, h2, embMsg P mm, by rw [List.getElem?_map, hmm]; rfl, ?_⟩
    exact (byteAt_emb_isSome (hg mm (List.mem_of_getElem? hmm)) ha hk).2 hpa

/-- An embedded log has no cache-block operation (every message is `plain`). -/
theorem noInval_emb (P : MProg) (log : List Mach.MMsg) : ∀ t a, ¬ cmoAt (log.map (embMsg P)) isInvalK t a := by
  rintro t a ⟨m, k, len, hm, hc, -⟩
  rw [List.getElem?_map] at hm
  obtain ⟨mm, -, rfl⟩ := Option.map_eq_some_iff.1 hm
  cases hc

end MiniEq
