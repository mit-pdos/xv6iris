/-
**The per-process key history's entries, and its ghost** (Rocq
`UhistDefs.v`; claude-notes/design/ni-uhist.md D1/D2).

A process's history is the list of its ROUNDS: the cause, the trapped key and
the resumed key (`Uround`).  The trap loop (`UserretClosedRound.urc_exit`)
appends one entry per round, and the invariant it keeps is that every entry
satisfies the kernel's round relation at the keys (`roundOkKeys`,
`uhistWf`).  The ghost (`uhistAuth` / `uhistLb` / `uhistOwn`, last section)
lives at the ENCODED ledger camera `Xv6G.mlUledG` (a mono-list of
`UartTrace.Uled`s), so that camera never names the U tier's key record.
The residue carries the history (`UsertrapRes.utOwn`'s last row,
`uhistRow`).

## Deviations from Rocq

1. **The encoding target is the tree `Uled`, not `positive`.**  Rocq derives
   `Countable uvis` (and for `uperm`, `offmode`, `pipe_names`, `fdtype`,
   `fdstate`) and stores `encode <$> h`.  Lean's key record holds functions
   (`Uvis.M : Nat → Option (BitVec 8)`, `Uvis.perm : Nat → Option UPerm`),
   so it is not countable; the carrier is `UartTrace.Uled` (numbers, pairs,
   and `Nat`-indexed families), and `UledEnc` is the injection (Rocq's
   `Countable` + `encode_inj`).  Prefix and comparability come back through
   injectivity exactly as Rocq's do (`uled_map_prefix`, Rocq
   `uhist_fmap_prefix`).
2. `Uround` is `BitVec 64 × Uvis × Uvis` (Lean's product nests to the right:
   Rocq's `e.1.1, e.1.2, e.2` are `e.1, e.2.1, e.2.2`); `uhistWf` is the
   membership form of Rocq's `Forall`.
3. `round_ok_keys_of_record` is stated at the record pair `(V, M)` the loop
   holds (UexecSlot deviation 1), `uvisOf`'s projections.
4. **The residue's row is `uhistRow := ∃ γ, uhistOwn γ`**: the history's
   name is existential beside its authority rather than Rocq's `un_uh N`
   field of the names record (UsertrapRes deviation 11).
5. `uhistAuth_alloc` (Rocq: `own_alloc (●ML [])` inline at the two park
   sites) is the one allocation the park sites call.
-/
import Xv6.UexecRound

namespace Xv6

open Iris Iris.BI Iris.ProofMode Std

/-! ## §1 The encoding (Rocq's `Countable` instances) -/

/-- **Rocq `Countable` + `encode_inj`**, into the encoded ledger's carrier. -/
class UledEnc (α : Type) where
  enc : α → Uled
  enc_inj : ∀ {a b : α}, enc a = enc b → a = b

namespace UledEnc

instance instNat : UledEnc Nat := ⟨.nat, fun h => Uled.nat.inj h⟩

instance instBool : UledEnc Bool where
  enc b := .nat (if b then 1 else 0)
  enc_inj {a b} h := by cases a <;> cases b <;> simp_all

instance instBitVec (w : Nat) : UledEnc (BitVec w) where
  enc x := .nat x.toNat
  enc_inj h := BitVec.eq_of_toNat_eq (Uled.nat.inj h)

instance instProd {α β : Type} [UledEnc α] [UledEnc β] : UledEnc (α × β) where
  enc p := .pair (enc p.1) (enc p.2)
  enc_inj {a b} h := by
    obtain ⟨h1, h2⟩ := Uled.pair.inj h
    exact Prod.ext (enc_inj h1) (enc_inj h2)

instance instOption {α : Type} [UledEnc α] : UledEnc (Option α) where
  enc o := match o with
    | none => .nat 0
    | some a => .pair (.nat 0) (enc a)
  enc_inj {a b} h := by
    cases a <;> cases b <;> simp only [Uled.pair.injEq, reduceCtorEq] at h
    · rfl
    · rw [enc_inj h.2]

/-- The list encoding (a right-nested chain of pairs ending in `nat 0`). -/
def encList {α : Type} [UledEnc α] : List α → Uled
  | [] => .nat 0
  | a :: l => .pair (enc a) (encList l)

theorem encList_inj {α : Type} [UledEnc α] : ∀ {l l' : List α}, encList l = encList l' → l = l'
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [encList] at h
  | _ :: _, [], h => by simp [encList] at h
  | a :: l, a' :: l', h => by
    obtain ⟨h1, h2⟩ := Uled.pair.inj h
    rw [enc_inj h1, encList_inj h2]

instance instList {α : Type} [UledEnc α] : UledEnc (List α) := ⟨encList, encList_inj⟩

/-- A `Nat`-indexed family, pointwise (Rocq has no counterpart: its key's
image and permission view are finite maps). -/
instance instFun {α : Type} [UledEnc α] : UledEnc (Nat → α) where
  enc f := .fn (fun n => enc (f n))
  enc_inj h := funext fun n => enc_inj (congrFun (Uled.fn.inj h) n)

/-- A set of names, by its membership test. -/
instance instExtTreeSet : UledEnc (ExtTreeSet GName compare) where
  enc s := .fn (fun n => enc (s.contains n))
  enc_inj h := ExtTreeSet.ext_contains fun n => enc_inj (congrFun (Uled.fn.inj h) n)

/-- Rocq `uperm_countable`. -/
instance instUPerm : UledEnc UPerm where
  enc u := enc (u.X, u.W)
  enc_inj {a b} h := by
    have := enc_inj h
    cases a; cases b; simp_all

/-- Rocq `offmode_countable`. -/
instance instOffMode : UledEnc OffMode where
  enc m := enc (match m with | .parked => true | .held => false)
  enc_inj {a b} h := by
    have := enc_inj h
    cases a <;> cases b <;> simp_all

/-- Rocq `pipe_names_countable`. -/
instance instPipeNames : UledEnc PipeNames where
  enc n := enc (n.pnRead, n.pnWrite, n.pnMread, n.pnMwrite, n.pnQueue)
  enc_inj {a b} h := by
    have := enc_inj h
    cases a; cases b; simp_all

/-- Rocq `fdtype_countable`. -/
instance instFdType : UledEnc FdType where
  enc t := match t with
    | .pipe γp => .pair (.nat 0) (enc γp)
    | .inode n g om => .pair (.nat 1) (enc (n, g, om))
    | .device mj => .pair (.nat 2) (enc mj)
  enc_inj {a b} h := by
    cases a <;> cases b <;> obtain ⟨h1, h2⟩ := Uled.pair.inj h <;> have h1 := Uled.nat.inj h1
    all_goals first | omega | (have := enc_inj h2; simp_all)

/-- Rocq `fdstate_countable`. -/
instance instFdState : UledEnc FdState where
  enc s := match s with
    | .closed => .nat 0
    | .open r w t => .pair (.nat 0) (enc (r, w, t))
  enc_inj {a b} h := by
    cases a <;> cases b
    · rfl
    · exact Uled.noConfusion h
    · exact Uled.noConfusion h
    · have := enc_inj (Uled.pair.inj h).2; simp_all

/-- Rocq `uvis_countable`: the eleven fields, in order. -/
instance instUvis : UledEnc Uvis where
  enc W := enc (W.tf, W.M, W.perm, W.sz, W.fd, W.cwd, W.gen, W.ch, W.pid, W.lazy, W.secc)
  enc_inj {a b} h := by
    have := enc_inj h
    cases a; cases b; simp_all

end UledEnc

open UledEnc in
/-- The encoding, mapped over a list, is injective. -/
theorem uled_map_inj {α : Type} [UledEnc α] : ∀ {l l' : List α}, l.map enc = l'.map enc → l = l'
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | a :: l, a' :: l', h => by
    simp only [List.map_cons, List.cons.injEq] at h
    rw [enc_inj h.1, uled_map_inj h.2]

open UledEnc in
/-- The encoding is injective on lists, so a prefix of encodings is a prefix
(Rocq `uhist_fmap_prefix`). -/
theorem uled_map_prefix {α : Type} [UledEnc α] {h h' : List α}
    (hp : h'.map enc <+: h.map enc) : h' <+: h := by
  obtain ⟨t, ht⟩ := hp
  obtain ⟨a, b, hab, ha, _⟩ := List.map_eq_append_iff.mp ht.symm
  refine ⟨b, ?_⟩
  rw [hab, uled_map_inj ha]

/-! ## §2 The entries (Rocq `uround`, `round_ok_keys`, `uhist_wf`) -/

/-- **Rocq `uround`**: one round -- the cause, the trapped key, the resumed
key. -/
abbrev Uround : Type := BitVec 64 × Uvis × Uvis

/-- **Rocq `round_ok_keys`**: the round relation at the two keys, spelled
exactly as `UexecApply.uexecRet_roundSlot_of`'s hypothesis is at
`g := tfResumeGpr0 W.tf`, `sep := tfW W.tf tfEpcIdx`. -/
def roundOkKeys (sc : BitVec 64) (W W' : Uvis) : Prop :=
  uroundOk sc (tfOf (tfResumeGpr0 W.tf) (retPc (tfW W.tf tfEpcIdx))) W.M W.perm W.sz W.cwd W.lazy W.secc
    W'.tf W'.M W'.perm W'.sz W'.cwd W'.lazy W'.secc

/-- **Rocq `uhist_wf`**: every recorded round is a lawful one. -/
def uhistWf (h : List Uround) : Prop := ∀ e ∈ h, roundOkKeys e.1 e.2.1 e.2.2

/-- Rocq `uhist_wf_nil`. -/
theorem uhistWf_nil : uhistWf [] := fun _ he => absurd he List.not_mem_nil

/-- **Rocq `uhist_wf_snoc`**. -/
theorem uhistWf_snoc {h : List Uround} {sc : BitVec 64} {W W' : Uvis} (hh : uhistWf h)
    (hr : roundOkKeys sc W W') : uhistWf (h ++ [(sc, W, W')]) := by
  intro e he
  rcases List.mem_append.mp he with he | he
  · exact hh e he
  · rw [List.mem_singleton.mp he]; exact hr

/-- **Rocq `round_ok_keys_of_record`** (deviation 3): the loop holds the
round relation at the record the round left; `uvisOf` projects exactly those
fields, so the same relation IS the relation at the resumed key. -/
theorem roundOkKeys_of_record (sc : BitVec 64) (W : Uvis) (V : ProcPriv) (M : Nat → List (BitVec 8))
    (sts : List FdState) (g : GName) (cs : ExtTreeSet GName compare) (pid : BitVec 32)
    (h : uroundOk sc (tfOf (tfResumeGpr0 W.tf) (retPc (tfW W.tf tfEpcIdx))) W.M W.perm W.sz W.cwd W.lazy
      W.secc V.tf (umemLazy V.upt V.sz.toNat M) (permOf V.upt.um V.sz.toNat) V.sz.toNat V.cwi V.pvLazy
      V.pvSecc) :
    roundOkKeys sc W (uvisOf V M sts g cs pid) := h

/-! ## §3 The ghost (Rocq `uhist_auth` / `uhist_lb` / `uhist_own`) -/

section Uhist
variable {GF : BundledGFunctors} [Xv6G GF]
open UledEnc

/-- **Rocq `uhist_auth`**: the authoritative history, its rounds encoded. -/
def uhistAuth (γ : GName) (h : List Uround) : IProp GF := γ ↪●ML (h.map enc)
/-- **Rocq `uhist_lb`**: a lower bound of the history. -/
def uhistLb (γ : GName) (h : List Uround) : IProp GF := γ ↪◯ML (h.map enc)

instance uhistLb_persistent (γ : GName) (h : List Uround) : Persistent (uhistLb (GF := GF) γ h) := by
  unfold uhistLb; infer_instance

instance uhistLb_timeless (γ : GName) (h : List Uround) : Timeless (uhistLb (GF := GF) γ h) := by
  unfold uhistLb; infer_instance

instance uhistAuth_timeless (γ : GName) (h : List Uround) : Timeless (uhistAuth (GF := GF) γ h) := by
  unfold uhistAuth; infer_instance

/-- **Rocq `uhist_auth_lb`**. -/
theorem uhistAuth_lb (γ : GName) (h : List Uround) :
    uhistAuth (GF := GF) γ h ⊢ uhistAuth γ h ∗ uhistLb γ h := by
  unfold uhistAuth uhistLb
  iintro Ha
  ihave #Hb := MonoList.lb_own_get γ _ (h.map enc) $$ Ha
  isplitl [Ha]
  · iexact Ha
  · iexact Hb

/-- **Rocq `uhist_lb_prefix`**: a lower bound is a prefix (through the
encoding's injectivity). -/
theorem uhistLb_prefix (γ : GName) (h h' : List Uround) :
    uhistAuth (GF := GF) γ h ⊢ uhistLb γ h' -∗ ⌜h' <+: h⌝ := by
  unfold uhistAuth uhistLb
  iintro Ha Hb
  ihave %hv := MonoList.auth_lb_own_valid γ _ (h.map enc) (h'.map enc) $$ Ha Hb
  ipureintro; exact uled_map_prefix hv.2

/-- **Rocq `uhist_lb_lb`**: two lower bounds of one history are comparable. -/
theorem uhistLb_lb (γ : GName) (h h' : List Uround) :
    uhistLb (GF := GF) γ h ⊢ uhistLb γ h' -∗ ⌜h <+: h' ∨ h' <+: h⌝ := by
  unfold uhistLb
  iintro Ha Hb
  ihave %hv := MonoList.lb_own_valid γ (h.map enc) (h'.map enc) $$ Ha Hb
  ipureintro; exact hv.imp uled_map_prefix uled_map_prefix

/-- **Rocq `uhist_grow`**. -/
theorem uhistAuth_grow (γ : GName) (h : List Uround) (e : Uround) :
    uhistAuth (GF := GF) γ h ⊢ |==> (uhistAuth γ (h ++ [e]) ∗ uhistLb γ (h ++ [e])) := by
  unfold uhistAuth uhistLb
  rw [List.map_append, List.map_singleton]
  iintro Ha
  iapply MonoList.auth_own_update_app γ [enc e] $$ Ha

/-- A fresh, empty history (deviation 5; Rocq: `own_alloc (●ML [])` at the
two park sites). -/
theorem uhistAuth_alloc : ⊢ |==> ∃ γ : GName, uhistAuth (GF := GF) γ [] := by
  unfold uhistAuth
  imod MonoList.own_alloc (GF := GF) (([] : List Uround).map enc) with ⟨%γ, Ha, -⟩
  imodintro
  iexists γ
  iexact Ha

/-- **Rocq `uhist_own`**: the history at some list, every round of it
lawful. -/
def uhistOwn (γ : GName) : IProp GF := iprop(∃ h : List Uround, uhistAuth γ h ∗ ⌜uhistWf h⌝)

/-- **Rocq `uhist_own_nil`**. -/
theorem uhistOwn_nil (γ : GName) : uhistAuth (GF := GF) γ [] ⊢ uhistOwn γ := by
  unfold uhistOwn
  iintro H
  iexists []
  iframe H
  ipureintro; exact uhistWf_nil

/-- **The residue's row** (deviation 4): the history at its own name,
existential beside it. -/
def uhistRow : IProp GF := iprop(∃ γ : GName, uhistOwn γ)

end Uhist

end Xv6
