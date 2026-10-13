/-
MachCSL: SYNC CHAINS -- the pure vocabulary of W8 (f2-ctx)'s chain
invariant (plan rev 37 §C-top "W8 (f2-ctx)", [OWN.37][OWN.38];
`notes/W8-Rctx.md` §1 F0; `PROGRESS-W8f2.md`).

The TSO proof's clean keys say "this entry is under the context's bound",
which is a VISIBILITY fact: TSO makes every entry under a hart's floor
visible to it, whoever wrote it and whether or not anything synchronised the
two harts.  RVWMO gives no such thing; what it gives is a SYNC CHAIN: the
author released after the entry, and a sequence of lock hand-offs ends in an
acquire by the observer.  This file states that chain as a pure fact of the
machine's byte histories (`FlatMem`), parametrised by the set of lock bytes
`isLk` (the registry: MachCSL cannot name xv6's locks; `Xv6/` instantiates
it), so that the state interpretation can carry it MachCSL-generically
([R26.s4]).

* **A hop** (`syncHop m b A r B a`): in the history of the lock byte `b`, the
  acquire entry `⟨a, B, va⟩` (`va ≠ 0`, the winning AMO's store) sits
  IMMEDIATELY above the release entry `⟨r, A, 0⟩` -- so the AMO read it: an
  exclusive read reads at the top of the order, and the region discipline
  lets only the lock rules write the byte -- or, for a dynamic lock, the word
  shape + the name window -- and the release entry sits above a NONZERO
  entry, so the lock was held when `A` wrote 0 (the region discipline: a 0
  from HELD only by the holder, `MachCSL.lkStepR`).  All three entries are
  WORD-sized (`wordEntAt`: each of the word's four bytes has an entry at that
  position by that agent -- every lock-protocol write is ONE 4-byte store,
  while `memset`'s junk is one byte per position) [R36.3].  An `initlock`
  zero (from FREE) is never a hop.
* **A chain** (`hopChain m isLk A t B a`): `t < r₀` (the entry precedes the
  author's release), the releaser of hop k+1 is the acquirer of hop k, which
  acquired before releasing (`a_k < r_{k+1}`), the last acquirer is `B`, at
  `a`; every hop's byte is a lock byte AT ITS ACQUIRE POSITION (`isLk b a_k`:
  the registry is TIME-INDEXED, [R35.1] -- a dynamic (pipe) lock is a hop
  byte exactly while it lives, `MachCSL.nameLockAt`).  Each author's chained entries form a PREFIX (`hopChain_prefix`):
  hence the per-author vector of [OWN.38].
* **A certificate** (`ChainCert`, `ChainCert.valid`): "the entries of `h` at
  or below `t` reach hart `j` before `τ`" -- `h = j` and `t < τ` (own
  entries), or a chain to `j` whose last acquire is below `τ`.  Timed, so a
  RELEASE can record what the releaser had reached BEFORE its release store
  (`ChainCert.valid_retime`) and the next acquirer can extend it by one hop
  (`ChainCert.valid_hop`).  A set of certificates is kept as the keys of a
  ghost map (`MachCSL.certsOk`, in `MachCSL.Resources`; `ChainCert.key` is
  injective, `chainPair`).

Everything here is STABLE under the machine's steps: a step only pushes
newer entries on top of histories (`memExt`), and a hop is about two
adjacent OLD entries (`ChainCert.valid_mono`).

Spec, for the record: RVWMO orders a release (`fence rw,w; sw` / `.rl`)
before every later access of the releasing hart's that it follows, and an
acquire (`amoswap.aq` / `fence r,rw`) after the read it ends; a chain of such
pairs through lock words is happens-before.  Which stores are releases is a
STATIC fact of the image (the release sites), carried by the consumer (W11),
not by this file.  Sail, Zifencei and the PMAs are silent on how a proof
represents it.  FAITHFUL.
-/
import MachCSL.Reserved

namespace MachCSL

/-! ## Memory extension -/

/-- `m'` extends `m`: every history only gained newer entries on top (what
every machine step does to the memory). -/
def memExt (m m' : FlatMem) : Prop :=
  ∀ (a : PAddr) (H : Hist), m[a]? = some H → ∃ N : Hist, m'[a]? = some (N ++ H)

theorem memExt_refl (m : FlatMem) : memExt m m :=
  fun _ H h => ⟨[], by simpa using h⟩

theorem memExt_trans {m m' m'' : FlatMem} (h1 : memExt m m') (h2 : memExt m' m'') : memExt m m'' := by
  intro a H h
  obtain ⟨N, hN⟩ := h1 a H h
  obtain ⟨N', hN'⟩ := h2 a _ hN
  exact ⟨N' ++ N, by rw [hN', List.append_assoc]⟩

theorem memExt_push (m : FlatMem) (a : PAddr) (e : HEnt) : memExt m (m.push a e) := by
  intro a' H h
  by_cases ha : a' = a
  · subst ha
    refine ⟨[e], ?_⟩
    rw [FlatMem.push_get?_eq, Std.ExtTreeMap.getD_eq_getD_getElem?, h]
    rfl
  · exact ⟨[], by rw [FlatMem.push_get?_ne _ _ _ _ ha, h]; rfl⟩

/-- A run of pushes of one store's bytes extends the memory. -/
theorem memExt_foldlPush {n : Nat} (pa : PAddr) (w : BitVec (8 * n)) (t : Nat) (h : Agent) :
    ∀ (l : List Nat) (m : FlatMem),
      memExt m (l.foldl (fun (m : FlatMem) j => m.push (pa + BitVec.ofNat 64 j) ⟨t, h, nthByte w j⟩) m)
  | [], m => memExt_refl m
  | j :: l, m => by
    simp only [List.foldl_cons]
    exact memExt_trans (memExt_push _ _ _) (memExt_foldlPush pa w t h l _)

theorem memExt_writeBytes {n : Nat} (m : FlatMem) (pa : PAddr) (w : BitVec (8 * n)) (t : Nat) (h : Agent) :
    memExt m (m.writeBytes pa n w t h) :=
  memExt_foldlPush pa w t h _ m

/-- A store's entry is in each footprint byte's history after it. -/
theorem ChainDefs.foldl_mem {n : Nat} (pa : PAddr) (w : BitVec (8 * n)) (t : Nat) (h : Agent) (j : Nat) :
    ∀ (l : List Nat) (m : FlatMem), j ∈ l →
      ∃ H, (l.foldl (fun (m : FlatMem) j => m.push (pa + BitVec.ofNat 64 j) ⟨t, h, nthByte w j⟩) m)[pa + BitVec.ofNat 64 j]? =
        some H ∧ (⟨t, h, nthByte w j⟩ : HEnt) ∈ H
  | [], _, hj => by simp at hj
  | j0 :: l, m, hj => by
    simp only [List.foldl_cons]
    by_cases hl : j ∈ l
    · exact ChainDefs.foldl_mem pa w t h j l _ hl
    · have hj0 : j = j0 := by
        rcases List.mem_cons.1 hj with h' | h'
        · exact h'
        · exact absurd h' hl
      subst hj0
      have h1 : (m.push (pa + BitVec.ofNat 64 j) ⟨t, h, nthByte w j⟩)[pa + BitVec.ofNat 64 j]? =
          some (⟨t, h, nthByte w j⟩ :: m.getD (pa + BitVec.ofNat 64 j) []) := FlatMem.push_get?_eq _ _ _
      obtain ⟨N, hN⟩ := memExt_foldlPush pa w t h l _ _ _ h1
      exact ⟨_, hN, List.mem_append_right _ List.mem_cons_self⟩

theorem ChainDefs.writeBytes_mem {n : Nat} (m : FlatMem) (pa : PAddr) (w : BitVec (8 * n)) (t : Nat) (h : Agent)
    {j : Nat} (hj : j < n) :
    ∃ H, (m.writeBytes pa n w t h)[pa + BitVec.ofNat 64 j]? = some H ∧ (⟨t, h, nthByte w j⟩ : HEnt) ∈ H :=
  ChainDefs.foldl_mem pa w t h j _ m (List.mem_range.2 hj)

/-! ## Growth above a position (the dynamic registry's stability) -/

theorem memGrow_refl (m : FlatMem) (t : Nat) : memGrow m t m :=
  fun _ H h => ⟨[], by simpa using h, fun _ he => by simp at he⟩

theorem memGrow_memExt {m m' : FlatMem} {t : Nat} (h : memGrow m t m') : memExt m m' :=
  fun a H hH => (h a H hH).imp fun _ hN => hN.1

theorem memGrow_push (m : FlatMem) (a : PAddr) (e : HEnt) (t : Nat) (ht : t < e.t) : memGrow m t (m.push a e) := by
  intro a' H h
  by_cases ha : a' = a
  · subst ha
    refine ⟨[e], ?_, fun x hx => by simp at hx; subst hx; exact ht⟩
    rw [FlatMem.push_get?_eq, Std.ExtTreeMap.getD_eq_getD_getElem?, h]
    rfl
  · exact ⟨[], by rw [FlatMem.push_get?_ne _ _ _ _ ha, h]; rfl, fun _ hx => by simp at hx⟩

theorem memGrow_trans {m m' m'' : FlatMem} {t : Nat} (h1 : memGrow m t m') (h2 : memGrow m' t m'') :
    memGrow m t m'' := by
  intro a H h
  obtain ⟨N, hN, hN'⟩ := h1 a H h
  obtain ⟨N', hN2, hN2'⟩ := h2 a _ hN
  refine ⟨N' ++ N, by rw [hN2, List.append_assoc], fun e he => ?_⟩
  rcases List.mem_append.1 he with he | he
  · exact hN2' e he
  · exact hN' e he

theorem memGrow_foldlPush {n : Nat} (pa : PAddr) (w : BitVec (8 * n)) (t0 t : Nat) (h : Agent) (ht : t0 < t) :
    ∀ (l : List Nat) (m : FlatMem),
      memGrow m t0 (l.foldl (fun (m : FlatMem) j => m.push (pa + BitVec.ofNat 64 j) ⟨t, h, nthByte w j⟩) m)
  | [], m => memGrow_refl m t0
  | j :: l, m => by
    simp only [List.foldl_cons]
    exact memGrow_trans (memGrow_push _ _ _ _ ht) (memGrow_foldlPush pa w t0 t h ht l _)

/-- A store at a position above `t0` grows the memory above `t0`. -/
theorem memGrow_writeBytes {n : Nat} (m : FlatMem) (pa : PAddr) (w : BitVec (8 * n)) (t0 t : Nat) (h : Agent)
    (ht : t0 < t) : memGrow m t0 (m.writeBytes pa n w t h) :=
  memGrow_foldlPush pa w t0 t h ht _ m

/-! ## Lock bytes of a region list -/

/-- `b` is the lock word (its low byte) of a reserved spinlock of `rs`. -/
def lockByteIn (rs : List RsvRegion) (b : PAddr) : Prop :=
  ∃ cb : BitVec 64, (⟨b, .lock cb⟩ : RsvRegion) ∈ rs

/-! ## Hops and chains -/

/-- **A word-sized entry** of the word at `b`: each of its four bytes has an
entry at position `t` by agent `g` (one 4-byte store) [R36.3]. -/
def wordEntAt (m : FlatMem) (b : PAddr) (t : Nat) (g : Agent) : Prop :=
  ∀ i, i < 4 → ∃ (H : Hist) (e : HEnt), m[b + BitVec.ofNat 64 i]? = some H ∧ e ∈ H ∧ e.t = t ∧ e.tid = g

theorem wordEntAt_mono {m m' : FlatMem} (hx : memExt m m') {b : PAddr} {t : Nat} {g : Agent}
    (h : wordEntAt m b t g) : wordEntAt m' b t g := by
  intro i hi
  obtain ⟨H, e, hH, he, het, heg⟩ := h i hi
  obtain ⟨N, hN⟩ := hx _ H hH
  exact ⟨N ++ H, e, hN, List.mem_append_right _ he, het, heg⟩

/-- **The dynamic hop registry** (W8 (f2-ctx), [OWN.49] (a′-r), the RULED
(a′) window [OWN.46] made provable by persistent entry receipts): at memory
`m` with top `top`, `b` is a hop byte for an acquire at `a ≤ top` when some
receipts `L` -- entries the memory holds -- satisfy the client's witness
`wit L b te` (xv6: a `struct file` slot's `f->pipe` word held `b`'s pipe at
`te`), `te ≤ a`, and every entry on `b`'s word after `te` up to `a` is
WORD-sized (no reclaim: `kfree`'s junk fill and `kalloc`'s are byte stores).
A pure fact of the memory, never falsified by a step (`dynLkAt_mono`). -/
def dynLkAt (wit : List (PAddr × HEnt) → PAddr → Nat → Prop) (m : FlatMem) (top : Nat) (b : PAddr)
    (a : Nat) : Prop :=
  a ≤ top ∧ ∃ (L : List (PAddr × HEnt)) (te : Nat), wit L b te ∧
    (∀ p ∈ L, ∃ H, m[p.1]? = some H ∧ p.2 ∈ H) ∧ te ≤ a ∧
    ∀ i, i < 4 → ∃ H, m[b + BitVec.ofNat 64 i]? = some H ∧ ∀ e ∈ H, te < e.t → e.t ≤ a →
      wordEntAt m b e.t e.tid

theorem dynLkAt_mono {wit : List (PAddr × HEnt) → PAddr → Nat → Prop} {m m' : FlatMem} {t t' : Nat}
    {b : PAddr} {a : Nat} (hg : memGrow m t m') (ht : t ≤ t') (h : dynLkAt wit m t b a) :
    dynLkAt wit m' t' b a := by
  obtain ⟨hat, L, te, hw, hL, hte, hwd⟩ := h
  have hx : memExt m m' := fun a H hH => by
    obtain ⟨N, hN, _⟩ := hg a H hH
    exact ⟨N, hN⟩
  refine ⟨Nat.le_trans hat ht, L, te, hw, fun p hp => ?_, hte, fun i hi => ?_⟩
  · obtain ⟨H, hH, hpe⟩ := hL p hp
    obtain ⟨N, hN, _⟩ := hg _ H hH
    exact ⟨N ++ H, hN, List.mem_append_right _ hpe⟩
  · obtain ⟨H0, hH0, hw0⟩ := hwd i hi
    obtain ⟨N, hN, hNt⟩ := hg _ H0 hH0
    refine ⟨N ++ H0, hN, fun e he hte' hea => ?_⟩
    rcases List.mem_append.1 he with he | he
    · have := hNt e he; omega
    · exact wordEntAt_mono hx (hw0 e he hte' hea)

/-- **A release → acquire hop** at the lock byte `b`: the acquire entry
`⟨a, B, va⟩` (nonzero) immediately above the release entry `⟨r, A, 0⟩`,
itself above a nonzero entry (the lock was held); all three WORD-sized
(`wordEntAt`, [R36.3]). -/
def syncHop (m : FlatMem) (b : PAddr) (A : CPU) (r : Nat) (B : CPU) (a : Nat) : Prop :=
  ∃ (H1 H2 : Hist) (e0 : HEnt) (va : BitVec 8),
    m[b]? = some (H1 ++ ⟨a, hartAgent B, va⟩ :: ⟨r, hartAgent A, 0⟩ :: e0 :: H2) ∧ va ≠ 0 ∧ e0.v ≠ 0 ∧
    wordEntAt m b a (hartAgent B) ∧ wordEntAt m b r (hartAgent A) ∧ wordEntAt m b e0.t e0.tid

/-- **A sync chain** from the entries of author `A` at or below `t` to hart
`B`, whose last acquire is at `a`. -/
inductive hopChain (m : FlatMem) (isLk : PAddr → Nat → Prop) : CPU → Nat → CPU → Nat → Prop
  /-- one hop: `A` released after its entry -/
  | base {A B : CPU} {t r a : Nat} (b : PAddr) :
      isLk b a → syncHop m b A r B a → t < r → hopChain m isLk A t B a
  /-- one more hop: the last acquirer `C` released after its acquire -/
  | step {A C B : CPU} {t a1 r a : Nat} (b : PAddr) :
      hopChain m isLk A t C a1 → isLk b a → syncHop m b C r B a → a1 < r → hopChain m isLk A t B a

theorem syncHop_mono {m m' : FlatMem} (hx : memExt m m') {b : PAddr} {A : CPU} {r : Nat} {B : CPU} {a : Nat}
    (h : syncHop m b A r B a) : syncHop m' b A r B a := by
  obtain ⟨H1, H2, e0, va, hb, hva, he0, hwa, hwr, hwe⟩ := h
  obtain ⟨N, hN⟩ := hx b _ hb
  exact ⟨N ++ H1, H2, e0, va, by rw [hN, List.append_assoc], hva, he0, wordEntAt_mono hx hwa,
    wordEntAt_mono hx hwr, wordEntAt_mono hx hwe⟩

theorem hopChain_mono {m m' : FlatMem} {isLk isLk' : PAddr → Nat → Prop} (hx : memExt m m')
    (hl : ∀ b r, isLk b r → isLk' b r) {A : CPU} {t : Nat} {B : CPU} {a : Nat}
    (h : hopChain m isLk A t B a) : hopChain m' isLk' A t B a := by
  induction h with
  | base b hb hh ht => exact .base b (hl b _ hb) (syncHop_mono hx hh) ht
  | step b _ hb hh ha ih => exact .step b ih (hl b _ hb) (syncHop_mono hx hh) ha

/-- Each author's chained entries form a prefix. -/
theorem hopChain_prefix {m : FlatMem} {isLk : PAddr → Nat → Prop} {A : CPU} {t : Nat} {B : CPU} {a : Nat}
    (h : hopChain m isLk A t B a) {t' : Nat} (ht : t' ≤ t) : hopChain m isLk A t' B a := by
  induction h with
  | base b hb hh hr => exact .base b hb hh (by omega)
  | step b _ hb hh ha ih => exact .step b (ih ht) hb hh ha

/-- A hop's acquire is an entry of the memory, authored by the acquirer. -/
theorem syncHop_acq_ent {m : FlatMem} {b : PAddr} {A : CPU} {r : Nat} {B : CPU} {a : Nat}
    (h : syncHop m b A r B a) : ∃ (H : Hist) (e : HEnt), m[b]? = some H ∧ e ∈ H ∧ e.t = a := by
  obtain ⟨H1, H2, e0, va, hb, _, _, _⟩ := h
  exact ⟨_, ⟨a, hartAgent B, va⟩, hb, List.mem_append_right _ List.mem_cons_self, rfl⟩

/-- A chain's last acquire is an entry of the memory. -/
theorem hopChain_acq_ent {m : FlatMem} {isLk : PAddr → Nat → Prop} {A : CPU} {t : Nat} {B : CPU} {a : Nat}
    (h : hopChain m isLk A t B a) : ∃ (b : PAddr) (H : Hist) (e : HEnt), m[b]? = some H ∧ e ∈ H ∧ e.t = a := by
  cases h with
  | base b _ hh _ => exact ⟨b, syncHop_acq_ent hh⟩
  | step b _ _ hh _ => exact ⟨b, syncHop_acq_ent hh⟩

/-- The hop a winning AMO makes: on top of a history headed by the release
entry `⟨r, A, 0⟩` over a nonzero entry, the acquire entry `⟨a, B, va⟩`; all
three word-sized. -/
theorem syncHop_of_head {m : FlatMem} {b : PAddr} {A : CPU} {r : Nat} {B : CPU} {a : Nat} {va : BitVec 8}
    {e0 : HEnt} {H2 : Hist} (hb : m[b]? = some (⟨a, hartAgent B, va⟩ :: ⟨r, hartAgent A, 0⟩ :: e0 :: H2))
    (hva : va ≠ 0) (he0 : e0.v ≠ 0) (hwa : wordEntAt m b a (hartAgent B)) (hwr : wordEntAt m b r (hartAgent A))
    (hwe : wordEntAt m b e0.t e0.tid) : syncHop m b A r B a :=
  ⟨[], H2, e0, va, by simpa using hb, hva, he0, hwa, hwr, hwe⟩

/-! ## The pairing (keys of the certificate map) -/

/-- The triangle numbers. -/
def ChainDefs.tri : Nat → Nat
  | 0 => 0
  | s + 1 => ChainDefs.tri s + s + 1

theorem ChainDefs.tri_lt {s u : Nat} (h : s < u) : ChainDefs.tri s + s < ChainDefs.tri u := by
  induction u with
  | zero => omega
  | succ u ih =>
    simp only [ChainDefs.tri]
    rcases Nat.lt_succ_iff_lt_or_eq.1 h with h | h
    · have := ih h
      omega
    · subst h
      omega

/-- Cantor's pairing. -/
def chainPair (a b : Nat) : Nat := ChainDefs.tri (a + b) + b

theorem chainPair_inj {a b c d : Nat} (h : chainPair a b = chainPair c d) : a = c ∧ b = d := by
  unfold chainPair at h
  rcases Nat.lt_trichotomy (a + b) (c + d) with hl | he | hg
  · have := ChainDefs.tri_lt hl
    omega
  · rw [he] at h
    omega
  · have := ChainDefs.tri_lt hg
    omega

/-! ## The environment certificates are checked against -/

/-- What a certificate is checked against: the byte histories, every hart's
coherence floors (`HRead.coh`), the lock bytes AT EACH POSITION (the hop
registry, time-indexed [R35.1]: `isLk b a` -- `b` is a hop byte for an
acquire at `a`), and the PUBLICATION bytes with their sole writer (the boot hop:
`started`, written once by hart 0 and read racily by the others). -/
structure ChainEnv where
  m : FlatMem
  coh : CPU → PAddr → Nat
  isLk : PAddr → Nat → Prop
  isPub : PAddr → CPU → Prop

/-- `Y` extends `X`: histories grew on top, the lock registry grew (a PAST
registration never changes: `isLk b r` stays true), the publication registry
is the same, and no hart's coherence floor at a publication byte of another
writer went down (a load only raises it; the region discipline keeps every
other hart's store off the byte). -/
def ChainEnv.ext (X Y : ChainEnv) : Prop :=
  memExt X.m Y.m ∧ (∀ b r, X.isLk b r → Y.isLk b r) ∧ (∀ f w, X.isPub f w ↔ Y.isPub f w) ∧
    (∀ (j : CPU) (f : PAddr) (w : CPU), X.isPub f w → j ≠ w → X.coh j f ≤ Y.coh j f)

theorem ChainEnv.ext_refl (X : ChainEnv) : X.ext X :=
  ⟨memExt_refl _, fun _ _ h => h, fun _ _ => Iff.rfl, fun _ _ _ _ _ => Nat.le_refl _⟩

theorem ChainEnv.ext_trans {X Y Z : ChainEnv} (h1 : X.ext Y) (h2 : Y.ext Z) : X.ext Z :=
  ⟨memExt_trans h1.1 h2.1, fun b r h => h2.2.1 b r (h1.2.1 b r h), fun f w => (h1.2.2.1 f w).trans (h2.2.2.1 f w),
    fun j f w hp hj => Nat.le_trans (h1.2.2.2 j f w hp hj) (h2.2.2.2 j f w ((h1.2.2.1 f w).1 hp) hj)⟩

/-- **The boot hop's cover** (W8 (f2-ctx), F-B adopted [R36.1]): hart `j`
has read (its coherence floor reached) a store at `r` of the publication
writer `w ≠ j` to its publication byte `f`, and the entries of `h` at or below
`t` precede that store -- `w`'s own entries (`h = w`, `t < r`), or entries
chained to `w` before it (`∃ a < r, hopChain … h t w a`: the boot hop composes
AFTER lock hops -- `h`'s release, the hops, `w`'s acquire at `a`, `w`'s
`fence rw,w; sw` at `r > a`, `rf`, `j`'s load and `fence r,rw`; PPO 4--7 and
`rf` in RVWMO's global memory order).  The guard is `j ≠ w`, the writer the
coherence clause of `ChainEnv.ext` is about. -/
def pubCover (X : ChainEnv) (h : CPU) (t : Nat) (j : CPU) : Prop :=
  ∃ (f : PAddr) (w : CPU) (r : Nat) (v : BitVec 8) (H : Hist),
    j ≠ w ∧ X.isPub f w ∧ X.m[f]? = some H ∧ ⟨r, hartAgent w, v⟩ ∈ H ∧ r ≤ X.coh j f ∧
    ((h = w ∧ t < r) ∨ ∃ a, a < r ∧ hopChain X.m X.isLk h t w a)

theorem pubCover_mono {X Y : ChainEnv} (hx : X.ext Y) {h : CPU} {t : Nat} {j : CPU}
    (hc : pubCover X h t j) : pubCover Y h t j := by
  obtain ⟨f, w, r, v, H, hne, hp, hf, he, hr, harm⟩ := hc
  obtain ⟨N, hN⟩ := hx.1 f H hf
  refine ⟨f, w, r, v, N ++ H, hne, (hx.2.2.1 f w).1 hp, hN, List.mem_append_right _ he,
    Nat.le_trans hr (hx.2.2.2 j f w hp hne), ?_⟩
  rcases harm with h1 | ⟨a, ha, hc⟩
  · exact .inl h1
  · exact .inr ⟨a, ha, hopChain_mono hx.1 hx.2.1 hc⟩

/-- **The gate**: hart `j` has read a post-power-on store of every
publication byte it does not write. -/
def gateOk (X : ChainEnv) (j : CPU) : Prop :=
  ∀ (f : PAddr) (w : CPU), X.isPub f w → j ≠ w →
    ∃ (r : Nat) (v : BitVec 8) (H : Hist), X.m[f]? = some H ∧ ⟨r, hartAgent w, v⟩ ∈ H ∧ 0 < r ∧ r ≤ X.coh j f

theorem gateOk_mono {X Y : ChainEnv} (hx : X.ext Y) {j : CPU} (hg : gateOk X j) : gateOk Y j := by
  intro f w hp hj
  obtain ⟨r, v, H, hf, he, hr0, hr⟩ := hg f w ((hx.2.2.1 f w).2 hp) hj
  obtain ⟨N, hN⟩ := hx.1 f H hf
  exact ⟨r, v, N ++ H, hN, List.mem_append_right _ he, hr0, Nat.le_trans hr (hx.2.2.2 j f w ((hx.2.2.1 f w).2 hp) hj)⟩

/-! ## Certificates -/

/-- **A chain certificate**: the entries of author `h` at or below `t` reach
hart `j` before `τ`. -/
structure ChainCert where
  h : CPU
  t : Nat
  j : CPU
  τ : Nat
  deriving DecidableEq

/-- The certificate's key in the ghost map (kind 0). -/
def ChainCert.key (c : ChainCert) : Nat :=
  chainPair 0 (chainPair (chainPair c.h.val c.t) (chainPair c.j.val c.τ))

/-- A gate's key in the ghost map (kind 1). -/
def gateKey (j : CPU) : Nat := chainPair 1 j.val

theorem ChainCert.key_inj {c c' : ChainCert} (h : c.key = c'.key) : c = c' := by
  obtain ⟨_, h0⟩ := chainPair_inj h
  obtain ⟨h1, h2⟩ := chainPair_inj h0
  obtain ⟨h3, h4⟩ := chainPair_inj h1
  obtain ⟨h5, h6⟩ := chainPair_inj h2
  cases c
  cases c'
  simp only at h3 h4 h5 h6
  subst h4 h6
  rw [Fin.ext h3, Fin.ext h5]

theorem gateKey_inj {j j' : CPU} (h : gateKey j = gateKey j') : j = j' :=
  Fin.ext (chainPair_inj h).2

theorem ChainCert.key_ne_gate (c : ChainCert) (j : CPU) : c.key ≠ gateKey j := by
  intro h
  have := (chainPair_inj h).1
  omega

/-- An ENTRY RECEIPT's key in the ghost map (kind 2; W8 (f2-ctx) [OWN.49]
(a′-r)): the history at `pa` holds `e` (histories only grow, so a receipt is a
past fact of the memory). -/
def entKey (pa : PAddr) (e : HEnt) : Nat :=
  chainPair 2 (chainPair pa.toNat (chainPair e.t (chainPair e.tid e.v.toNat)))

theorem entKey_inj {pa pa' : PAddr} {e e' : HEnt} (h : entKey pa e = entKey pa' e') : pa = pa' ∧ e = e' := by
  obtain ⟨_, h0⟩ := chainPair_inj h
  obtain ⟨h1, h2⟩ := chainPair_inj h0
  obtain ⟨h3, h4⟩ := chainPair_inj h2
  obtain ⟨h5, h6⟩ := chainPair_inj h4
  refine ⟨BitVec.eq_of_toNat_eq h1, ?_⟩
  cases e
  cases e'
  simp only at h3 h5 h6
  subst h3 h5
  rw [BitVec.eq_of_toNat_eq h6]

theorem entKey_ne_cert (pa : PAddr) (e : HEnt) (c : ChainCert) : entKey pa e ≠ c.key := by
  intro h
  have := (chainPair_inj h).1
  omega

theorem entKey_ne_gate (pa : PAddr) (e : HEnt) (j : CPU) : entKey pa e ≠ gateKey j := by
  intro h
  have := (chainPair_inj h).1
  omega

/-- What a certificate says: own entries before `τ`, or a chain whose last
acquire is below `τ`, or the boot hop. -/
def ChainCert.valid (X : ChainEnv) (c : ChainCert) : Prop :=
  (c.h = c.j ∧ c.t < c.τ) ∨ (∃ a, a < c.τ ∧ hopChain X.m X.isLk c.h c.t c.j a) ∨ pubCover X c.h c.t c.j

theorem ChainCert.valid_mono {X Y : ChainEnv} (hx : X.ext Y) {c : ChainCert} (h : c.valid X) : c.valid Y := by
  rcases h with h | ⟨a, ha, hc⟩ | hp
  · exact .inl h
  · exact .inr (.inl ⟨a, ha, hopChain_mono hx.1 hx.2.1 hc⟩)
  · exact .inr (.inr (pubCover_mono hx hp))

/-- A weaker certificate: fewer entries, a later deadline. -/
theorem ChainCert.valid_le {X : ChainEnv} {h j : CPU} {t t' τ τ' : Nat}
    (hv : ChainCert.valid X ⟨h, t, j, τ⟩) (ht : t' ≤ t) (hτ : τ ≤ τ') :
    ChainCert.valid X ⟨h, t', j, τ'⟩ := by
  rcases hv with ⟨h1, h2⟩ | ⟨a, ha, hc⟩ | ⟨f, w, r, v, H, hne, hp, hf, he, hr, harm⟩
  · exact .inl ⟨h1, by simp only at h2 ⊢; omega⟩
  · exact .inr (.inl ⟨a, by simp only at ha ⊢; omega, hopChain_prefix hc ht⟩)
  · refine .inr (.inr ⟨f, w, r, v, H, hne, hp, hf, he, hr, ?_⟩)
    rcases harm with ⟨h1, h2⟩ | ⟨a, ha, hc⟩
    · exact .inl ⟨h1, by simp only at h2 ⊢; omega⟩
    · exact .inr ⟨a, ha, hopChain_prefix hc ht⟩

/-- **The release's record**: a certificate to the releaser `j` is one before
the release store at `r`, when every entry of the memory is below `r` (the
store is at the top) and an own one is too. -/
theorem ChainCert.valid_retime {X : ChainEnv} {h j : CPU} {t τ r : Nat}
    (hv : ChainCert.valid X ⟨h, t, j, τ⟩)
    (hall : ∀ (b : PAddr) (H : Hist) (e : HEnt), X.m[b]? = some H → e ∈ H → e.t < r)
    (hown : h = j → t < r) : ChainCert.valid X ⟨h, t, j, r⟩ := by
  rcases hv with ⟨h1, _⟩ | ⟨a, _, hc⟩ | hp
  · exact .inl ⟨h1, hown h1⟩
  · obtain ⟨b, H, e, hb, he, het⟩ := hopChain_acq_ent hc
    exact .inr (.inl ⟨a, by rw [← het]; exact hall b H e hb he, hc⟩)
  · exact .inr (.inr hp)

/-- A publication byte is ONE-SHOT in `X`: all its post-power-on entries are
at one timestamp (the region discipline of `MachCSL.RsvKind.pub`). -/
def pubOneShot (X : ChainEnv) : Prop :=
  ∀ (f : PAddr) (w : CPU) (H : Hist) (e e' : HEnt), X.isPub f w → X.m[f]? = some H → e ∈ H → e' ∈ H →
    e.t ≠ 0 → e'.t ≠ 0 → e.t = e'.t

/-- **The acquire's extension**: a certificate to the releaser before its
release `r`, and the hop from that release to `B`'s acquire at `a`, give a
certificate to `B` past `a` -- by the chain, or (a boot-hop cover of the
releaser) by `B`'s own gate, the publication byte being one-shot. -/
theorem ChainCert.valid_hop {X : ChainEnv} {h A B : CPU} {t r a : Nat} {b : PAddr}
    (hv : ChainCert.valid X ⟨h, t, A, r⟩) (hb : X.isLk b a) (hh : syncHop X.m b A r B a)
    (hall : ∀ (b' : PAddr) (H : Hist) (e : HEnt), X.m[b']? = some H → e ∈ H → e.t ≤ a)
    (hone : pubOneShot X) (hgate : gateOk X B) : ChainCert.valid X ⟨h, t, B, a + 1⟩ := by
  rcases hv with ⟨h1, h2⟩ | ⟨a1, ha1, hc⟩ | ⟨f, w, r', v, H, hne, hp, hf, he, hr, harm⟩
  · simp only at h1 h2
    subst h1
    exact .inr (.inl ⟨a, Nat.lt_succ_self a, .base b hb hh h2⟩)
  · exact .inr (.inl ⟨a, Nat.lt_succ_self a, .step b hc hb hh ha1⟩)
  · simp only at hne hr harm
    have hle : r' ≤ a := hall f H _ hf he
    by_cases hBw : B = w
    · -- the writer itself acquires: its own entries, or the chain, before its store
      subst hBw
      rcases harm with ⟨h1, h2⟩ | ⟨a', ha', hc⟩
      · exact .inl ⟨h1, show t < a + 1 by omega⟩
      · exact .inr (.inl ⟨a', by simp only; omega, hc⟩)
    · obtain ⟨r2, v2, H2, hf2, he2, hr20, hr2⟩ := hgate f w hp hBw
      rw [hf] at hf2
      cases hf2
      have hr0 : r' ≠ 0 := by
        rcases harm with ⟨_, h2⟩ | ⟨a', ha', _⟩ <;> omega
      have heq : r' = r2 := hone f w H _ _ hp hf he he2 hr0 (show r2 ≠ 0 by omega)
      subst heq
      exact .inr (.inr ⟨f, w, r', v2, H, hBw, hp, hf, he2, hr2, harm⟩)


/-! ## The load-side invariant (W8 (f2-ctx) S3 -- STATED; wired by S3's load rules)

The MachCSL-generic form of `Xv6.AccessDiscipline`'s `chainOkAt` (plan §C W8
skeleton (iii+), [R26.s4]): what every load step must keep, and what the
export reads off the state interpretation.  Not yet a conjunct of
`MachCSL.certsOk`: S3 adds it there, with `memModel_load` taking the load's
certificates (established INSIDE the load's step [R35.s5]). -/

/-- `m'` adds to `m` only entries above `top`: every entry of `m'` at or
below `top` is an entry of `m` (what a machine step at top `top` does to the
memory: a store pushes entries at `top + 1`, a load pushes none). -/
def memAbove (m : FlatMem) (top : Nat) (m' : FlatMem) : Prop :=
  ∀ (a : PAddr) (H' : Hist), m'[a]? = some H' → ∀ e ∈ H', e.t ≤ top → ∃ H, m[a]? = some H ∧ e ∈ H

theorem memAbove_refl (m : FlatMem) (top : Nat) : memAbove m top m :=
  fun _ H' h e he _ => ⟨H', h, he⟩

theorem memAbove_trans {m m' m'' : FlatMem} {top : Nat} (h1 : memAbove m top m') (h2 : memAbove m' top m'') :
    memAbove m top m'' := by
  intro a H'' hH e he het
  obtain ⟨H', hH', he'⟩ := h2 a H'' hH e he het
  exact h1 a H' hH' e he' het

theorem memAbove_push (m : FlatMem) (a : PAddr) (e : HEnt) (top : Nat) (ht : top < e.t) :
    memAbove m top (m.push a e) := by
  intro a' H' hH x hx hxt
  by_cases ha : a' = a
  · subst ha
    rw [FlatMem.push_get?_eq] at hH
    cases hH
    rcases List.mem_cons.1 hx with hx | hx
    · subst hx; omega
    · rw [Std.ExtTreeMap.getD_eq_getD_getElem?] at hx
      cases hm : m[a']? with
      | none => rw [hm] at hx; simp at hx
      | some H => rw [hm] at hx; exact ⟨H, rfl, hx⟩
  · rw [FlatMem.push_get?_ne _ _ _ _ ha] at hH
    exact ⟨H', hH, hx⟩

theorem memAbove_foldlPush {n : Nat} (pa : PAddr) (w : BitVec (8 * n)) (top t : Nat) (h : Agent) (ht : top < t) :
    ∀ (l : List Nat) (m : FlatMem),
      memAbove m top (l.foldl (fun (m : FlatMem) j => m.push (pa + BitVec.ofNat 64 j) ⟨t, h, nthByte w j⟩) m)
  | [], m => memAbove_refl m top
  | j :: l, m => by
    simp only [List.foldl_cons]
    exact memAbove_trans (memAbove_push _ _ _ _ ht) (memAbove_foldlPush pa w top t h ht l _)

/-- A store above `top` adds entries above `top` only. -/
theorem memAbove_writeBytes {n : Nat} (m : FlatMem) (pa : PAddr) (w : BitVec (8 * n)) (top t : Nat) (h : Agent)
    (ht : top < t) : memAbove m top (m.writeBytes pa n w t h) :=
  memAbove_foldlPush pa w top t h ht _ m

/-- **Every observed foreign hart entry is chained** (W8 (f2-ctx) S3; plan
§C W8 (iii+)): hart `j`'s coherence floor at byte `a` is the timestamp of the
latest FOREIGN entry a load of `j` read there since `j` last stored to it
(`HRead.afterLoad`, `HRead.resetCoh`); when the entry at that timestamp is a
HART's (DMA authors are exempt: the device-key arm), not `j`'s own, and the
byte is not exempt as of the entry (`ex a t`: the client's registry -- the
lock layer's words, PTE bytes of both tables), some certificate of it to `j`
is VALID.  A pure fact of `X`. -/
def loadsChained (X : ChainEnv) (ex : PAddr → Nat → Prop) : Prop :=
  ∀ (j : CPU) (a : PAddr) (H : Hist) (e : HEnt), X.m[a]? = some H → e ∈ H → e.t ≠ 0 →
    e.t = X.coh j a → ∀ hA : e.tid < NCPU, e.tid ≠ hartAgent j → ¬ ex a e.t →
      ∃ τ, ChainCert.valid X ⟨⟨e.tid, hA⟩, e.t, j, τ⟩

/-- The power-on state: every coherence floor is 0. -/
theorem loadsChained_zero (X : ChainEnv) (ex : PAddr → Nat → Prop) (h0 : ∀ j a, X.coh j a = 0) :
    loadsChained X ex := by
  intro j a H e _ _ het hc
  rw [h0 j a] at hc
  exact absurd hc het

/-- **The invariant's step law**: a step at top `top` (every coherence floor
at or below it) that extends the environment, adds only entries above `top`,
and only GROWS the exemption (at the positions it already holds: an
exemption read off the memory AS OF a position, `MachCSL.chainExAt`, is fixed
only up to the top) keeps the invariant at every floor it leaves
alone or resets to 0; a floor it moves (a load's foreign source) needs the
step's own certificates (`hnew`). -/
theorem loadsChained_step {X Y : ChainEnv} {ex ex' : PAddr → Nat → Prop} {top : Nat}
    (hx : X.ext Y) (hm : memAbove X.m top Y.m) (hle : ∀ j a, X.coh j a ≤ top)
    (hex : ∀ a t, t ≤ top → ex a t → ex' a t)
    (hnew : ∀ (j : CPU) (a : PAddr), Y.coh j a ≠ X.coh j a → ∀ (H : Hist) (e : HEnt), Y.m[a]? = some H →
      e ∈ H → e.t ≠ 0 → e.t = Y.coh j a → ∀ hA : e.tid < NCPU, e.tid ≠ hartAgent j → ¬ ex' a e.t →
        ∃ τ, ChainCert.valid Y ⟨⟨e.tid, hA⟩, e.t, j, τ⟩)
    (h : loadsChained X ex) : loadsChained Y ex' := by
  intro j a H e hH he het hc hA hne hnex
  by_cases hcj : Y.coh j a = X.coh j a
  · have hle' : e.t ≤ top := by rw [hc, hcj]; exact hle j a
    obtain ⟨H0, hH0, he0⟩ := hm a H hH e he hle'
    obtain ⟨τ, hv⟩ := h j a H0 e hH0 he0 het (by rw [hc, hcj]) hA hne (fun hx' => hnex (hex a e.t hle' hx'))
    exact ⟨τ, ChainCert.valid_mono hx hv⟩
  · exact hnew j a hcj H e hH he het hc hA hne hnex

/-- A step that resets or keeps every floor (a store, a device step, an
exclusive access) keeps the invariant. -/
theorem loadsChained_keep {X Y : ChainEnv} {ex ex' : PAddr → Nat → Prop} {top : Nat}
    (hx : X.ext Y) (hm : memAbove X.m top Y.m) (hle : ∀ j a, X.coh j a ≤ top)
    (hex : ∀ a t, t ≤ top → ex a t → ex' a t) (hcoh : ∀ j a, Y.coh j a = X.coh j a ∨ Y.coh j a = 0)
    (h : loadsChained X ex) : loadsChained Y ex' := by
  refine loadsChained_step hx hm hle hex (fun j a hne' H e _ _ het hc => ?_) h
  rcases hcoh j a with h1 | h1
  · exact absurd h1 hne'
  · rw [h1] at hc
    exact absurd hc het

/-! ## The exemption (W8 (f2-ctx) S3; design (A′), `PROGRESS-W8f2.md`)

`loadsChained`'s exemption, read off the MEMORY and the registry -- not off a
ghost -- so that the pure export (`Xv6.AccessDiscipline.chainOkAt`'s
`custAt … = .lockw b` / `.pte` arms) can name the SAME predicate:

* the lock layer's bytes: the static spinlocks' two words and the
  publication words of the registry (`lockPubByteIn`), and a live dynamic
  lock's two words (`dynLkAt` at the entry's position);
* the PAGE-TABLE bytes of BOTH tables ([R25.1 (a)], [OWN.39]): the bytes of
  every page a Sv39 walk reaches, AS OF the entry's position, from a root
  word the registry names -- `ptByteLiveAt`.  From a PERMANENT root
  (`RsvKind.roots`: xv6's `kernel_pagetable`, never freed) the walk is
  unrestricted (`ptByteAt`); from a FREEABLE root (`RsvKind.uroots`: every
  `proc[i].pagetable`, built at run time by `uvmcreate`/`mappages`) every hop
  is restricted to pages NOT pushed onto the registered free list
  (`RsvKind.freeHead`: `kmem.freelist`) since the naming word's last write
  (W8 (pte-ghost), [OWN.57] scoped to the freeable tables [R42.1]): a freed
  page-table page stops being covered at its push, not when the stale
  pointer naming it is cleared;
* the bytes of an AUDITED RACY word whose value, AS OF the entry's position,
  lies in the registry's value set -- `racyValAt` (W8 (f3-racy) [OWN.63]; xv6:
  `ip->ref`, `[1, 2^31)`): a value fact, not a blanket exemption.

An exemption read AS OF a position is fixed once the position is below the
top (`ptByteLiveAt_grow`), which is all the step laws need. -/

/-- Byte `a`'s entry AS OF position `t`: the latest entry at or below `t`
(the value every agent's read at view `t` would return, ignoring its own
buffered stores above `t`). -/
def FlatMem.entAsOf (m : FlatMem) (a : PAddr) (t : Nat) : Option HEnt :=
  (m[a]?).bind (fun H => H.find? (fun e => decide (e.t ≤ t)))

/-- The doubleword at `a` holds `v` AS OF position `t`. -/
def wordAsOf (m : FlatMem) (a : PAddr) (t : Nat) (v : BitVec 64) : Prop :=
  ∀ j, j < 8 → (m.entAsOf (a + BitVec.ofNat 64 j) t).map HEnt.v = some (nthByte (n := 8) v j)

/-- A Sv39 POINTER entry (`V` set, `R`/`W`/`X` clear) naming the page at `c`
(its PPN, bits 53..10, shifted to a physical address). -/
def ptPtrTo (v : BitVec 64) (c : PAddr) : Prop :=
  v.getLsbD 0 = true ∧ v &&& 0xE#64 = 0#64 ∧ c = ((v >>> 10) <<< 12) &&& 0x00FFFFFFFFFFF000#64

/-- An entry of the page at `p` points, as of `t`, at the page `c`. -/
def ptChildAt (m : FlatMem) (t : Nat) (p c : PAddr) : Prop :=
  ∃ (i : Nat) (v : BitVec 64), i < 512 ∧ wordAsOf m (p + BitVec.ofNat 64 (8 * i)) t v ∧ ptPtrTo v c

/-- The page at `p` is one a Sv39 walk from the root page `r` visits, as of
`t`: the root, a level-1 page, or a level-0 page. -/
def ptPageAt (m : FlatMem) (t : Nat) (r p : PAddr) : Prop :=
  p = r ∨ ptChildAt m t r p ∨ ∃ q, ptChildAt m t r q ∧ ptChildAt m t q p

/-- As of `t`, a root word of `rs` holds the root page `r ≠ 0`. -/
def ptRootAt (rs : List RsvRegion) (m : FlatMem) (t : Nat) (r : PAddr) : Prop :=
  r ≠ 0 ∧ ∃ (base : PAddr) (cnt stride k : Nat), (⟨base, .roots cnt stride⟩ : RsvRegion) ∈ rs ∧ k < cnt ∧
    wordAsOf m (base + BitVec.ofNat 64 (stride * k)) t r

/-- **A page-table byte of a PERMANENT table as of `t`**: `a` lies in a page
a walk reaches, as of `t`, from a PERMANENT root word of `rs` (`RsvKind.roots`;
xv6: `kernel_pagetable`, never freed), unrestricted. -/
def ptByteAt (rs : List RsvRegion) (m : FlatMem) (t : Nat) (a : PAddr) : Prop :=
  ∃ r p : PAddr, ptRootAt rs m t r ∧ ptPageAt m t r p ∧ p.toNat ≤ a.toNat ∧ a.toNat < p.toNat + 4096

/-! ### The freeable tables (W8 (pte-ghost), [OWN.57] option (c) scoped to the
freeable tables [R42.1])

A table that is FREED at run time (xv6: a process's, `freewalk` /
`proc_freepagetable`) is walked HOP-RESTRICTED: a hop (a root word to its
root page, a pointer slot to its child page) is taken only if the named page
was NOT pushed onto a registered free list (`RsvKind.freeHead`; xv6:
`kmem.freelist`) after the naming word's last write.  Freed-ness is read off
the head word's history (positions are global, so the head's and the naming
word's positions compare); no ghost state. -/

/-- The POSITION of the doubleword at `a` as of `t`: the max over its 8 bytes
of the latest entry's position at or below `t` (0 for a byte without one) --
ENTRY-based [R42.s2]: a later write rewriting the same value moves it. -/
def wordPosAsOf (m : FlatMem) (a : PAddr) (t : Nat) : Nat :=
  (List.range 8).foldr
    (fun j acc => max (((m.entAsOf (a + BitVec.ofNat 64 j) t).map HEnt.t).getD 0) acc) 0

/-- **The page `p` was freed since `t0`** (as of `t`): a registered free-list
head word held `p`, as of some position in `(t0, t]`. -/
def ptFreedSince (rs : List RsvRegion) (m : FlatMem) (t0 t : Nat) (p : PAddr) : Prop :=
  ∃ (base : PAddr) (cnt stride k t' : Nat), (⟨base, .freeHead cnt stride⟩ : RsvRegion) ∈ rs ∧ k < cnt ∧
    t0 < t' ∧ t' ≤ t ∧ wordAsOf m (base + BitVec.ofNat 64 (stride * k)) t' p

/-- A LIVE hop: an entry of the page at `p` points, as of `t`, at the page
`c`, and `c` was not freed since that entry's word was last written. -/
def ptLiveChildAt (rs : List RsvRegion) (m : FlatMem) (t : Nat) (p c : PAddr) : Prop :=
  ∃ (i : Nat) (v : BitVec 64), i < 512 ∧ wordAsOf m (p + BitVec.ofNat 64 (8 * i)) t v ∧ ptPtrTo v c ∧
    ¬ ptFreedSince rs m (wordPosAsOf m (p + BitVec.ofNat 64 (8 * i)) t) t c

/-- The page at `p` is one a LIVE walk from the root page `r` visits, as of
`t`: the root, a live level-1 page, or a live level-0 page under one. -/
def ptLivePageAt (rs : List RsvRegion) (m : FlatMem) (t : Nat) (r p : PAddr) : Prop :=
  p = r ∨ ptLiveChildAt rs m t r p ∨ ∃ q, ptLiveChildAt rs m t r q ∧ ptLiveChildAt rs m t q p

/-- As of `t`, a FREEABLE root word of `rs` (`RsvKind.uroots`) holds the root
page `r ≠ 0`, not freed since the word's last write. -/
def ptURootAt (rs : List RsvRegion) (m : FlatMem) (t : Nat) (r : PAddr) : Prop :=
  r ≠ 0 ∧ ∃ (base : PAddr) (cnt stride k : Nat), (⟨base, .uroots cnt stride⟩ : RsvRegion) ∈ rs ∧ k < cnt ∧
    wordAsOf m (base + BitVec.ofNat 64 (stride * k)) t r ∧
    ¬ ptFreedSince rs m (wordPosAsOf m (base + BitVec.ofNat 64 (stride * k)) t) t r

/-- **A LIVE page-table byte as of `t`** (W8 (pte-ghost)): a byte of a page
the unrestricted walk from a PERMANENT root reaches (`ptByteAt`), or of a
page the hop-restricted walk from a FREEABLE root reaches -- so no page is
covered through a word that named it before it was pushed onto the free
list (the [R41.1] window is closed), and pointer-shaped words a later owner
writes into a freed page lead nowhere. -/
def ptByteLiveAt (rs : List RsvRegion) (m : FlatMem) (t : Nat) (a : PAddr) : Prop :=
  ptByteAt rs m t a ∨
    ∃ r p : PAddr, ptURootAt rs m t r ∧ ptLivePageAt rs m t r p ∧ p.toNat ≤ a.toNat ∧ a.toNat < p.toNat + 4096

/-- The doubleword whose byte `j` is `0x01` exactly when bit `j` of `mask` is
set and `0x00` otherwise: a byte-subset of `kfree`'s `0x01` junk fill
(`kalloc.c:55`) over an all-zero word. -/
def fill01Word (mask : Nat) : BitVec 64 :=
  BitVec.ofNat 64 ((List.range 8).foldr (fun j acc => (if mask.testBit j then 2 ^ (8 * j) else 0) + acc) 0)

/-- **No partial `0x01` fill is a pointer into RAM** [R42.s3]: for every
byte-subset of the fill over zero (256 masks), a Sv39 pointer entry it spells
names no page in `[0x80000000, 0x88000000)` (the PPN bits it can set are
`≡ 2 (mod 8)`, never bit 31).  So the fill `kfree` writes into an (all-zero,
`freewalk`) page-table page before its push makes no RAM page a page-table
page. -/
theorem ptPtrTo_fill01_notRam (mask : Nat) (hm : mask < 256) (c : PAddr) (hp : ptPtrTo (fill01Word mask) c) :
    ¬ (0x80000000 ≤ c.toNat ∧ c.toNat < 0x88000000) := by
  obtain ⟨_, _, rfl⟩ := hp
  revert mask
  decide +kernel

/-- A byte of a static spinlock's two words or of a publication word of `rs`. -/
def lockPubByteIn (rs : List RsvRegion) (a : PAddr) : Prop :=
  ∃ R ∈ rs, ((∃ cb, R.kind = .lock cb) ∨ (∃ w, R.kind = .pub w)) ∧ a ∈ R.bytes

/-- A byte of the two words (`lk->locked`, `lk->cpu`) of the spinlock at `b`. -/
def lockWordsByte (b a : PAddr) : Prop :=
  (∃ j, j < 4 ∧ a = b + BitVec.ofNat 64 j) ∨ (∃ j, j < 8 ∧ a = b + 16#64 + BitVec.ofNat 64 j)

/-- A byte of an audited racy word of `rs` (`RsvKind.racy`). -/
def racyByteIn (rs : List RsvRegion) (a : PAddr) : Prop :=
  ∃ (base : PAddr) (cnt stride n vlo vhi k j : Nat), (⟨base, .racy cnt stride n vlo vhi⟩ : RsvRegion) ∈ rs ∧
    k < cnt ∧ j < n ∧ a = base + BitVec.ofNat 64 (stride * k) + BitVec.ofNat 64 j

/-- The `n`-byte word at `w` holds, AS OF position `t` (`FlatMem.entAsOf`,
byte by byte), a value in `[vlo, vhi)` (unsigned, little-endian). -/
def racyWordOk (m : FlatMem) (w : PAddr) (n t vlo vhi : Nat) : Prop :=
  ∃ v : BitVec (8 * n), vlo ≤ v.toNat ∧ v.toNat < vhi ∧
    ∀ i, i < n → (m.entAsOf (w + BitVec.ofNat 64 i) t).map HEnt.v = some (nthByte v i)

/-- **A VALUE-QUALIFIED racy byte as of `t`** (W8 (f3-racy) [OWN.63]): `a` is
a byte of an audited racy word of `rs` whose value AS OF `t` lies in the
region's value set (xv6: `ip->ref`, the set `[1, 2^31)` -- the signed guard
`ip->ref < 1` of `ilock`/`iunlock` reads `≥ 1`). -/
def racyValAt (rs : List RsvRegion) (m : FlatMem) (t : Nat) (a : PAddr) : Prop :=
  ∃ (base : PAddr) (cnt stride n vlo vhi k j : Nat), (⟨base, .racy cnt stride n vlo vhi⟩ : RsvRegion) ∈ rs ∧
    k < cnt ∧ j < n ∧ a = base + BitVec.ofNat 64 (stride * k) + BitVec.ofNat 64 j ∧
    racyWordOk m (base + BitVec.ofNat 64 (stride * k)) n t vlo vhi

theorem racyByteIn_of_racyValAt {rs : List RsvRegion} {m : FlatMem} {t : Nat} {a : PAddr}
    (h : racyValAt rs m t a) : racyByteIn rs a :=
  let ⟨base, cnt, stride, n, vlo, vhi, k, j, hR, hk, hj, ha, _⟩ := h
  ⟨base, cnt, stride, n, vlo, vhi, k, j, hR, hk, hj, ha⟩

/-- **The exemption of the load-side invariant**, at memory `m` with top
`top`: byte `a` as of position `t` is a lock-layer byte (static, publication,
or a dynamic lock live at `t`), a LIVE page-table byte (`ptByteLiveAt`: the
permanent table's walk, or a freeable table's walk through pages not freed
since their naming words' writes -- W8 (pte-ghost), [OWN.57]), a byte of an
audited racy word whose value as of `t` is in the region's value set
(`racyValAt`, W8 (f3-racy) [OWN.63]: the exemption is VALUE-qualified, no
longer every byte at every position).  (W8 (f3-gate) [OWN.62] removed the
device-ring arm: the used ring's hart-authored entries -- hart 0's boot
zeroes -- are now CERTIFIED, `Xv6.DiskAcc.usedIdx_certs`.) -/
def chainExAt (rs : List RsvRegion) (wit : List (PAddr × HEnt) → PAddr → Nat → Prop) (m : FlatMem)
    (top : Nat) (a : PAddr) (t : Nat) : Prop :=
  lockPubByteIn rs a ∨ (∃ b, dynLkAt wit m top b t ∧ lockWordsByte b a) ∨ ptByteLiveAt rs m t a ∨
    racyValAt rs m t a

/-- Reading AS OF a position at or below the top is unchanged by a step that
adds entries above the top only. -/
theorem FlatMem.entAsOf_grow {m m' : FlatMem} {top t : Nat} (hg : memGrow m top m')
    (hm : memAbove m top m') (ht : t ≤ top) (a : PAddr) : m'.entAsOf a t = m.entAsOf a t := by
  unfold FlatMem.entAsOf
  cases hH : m[a]? with
  | some H =>
    obtain ⟨N, hN, hNt⟩ := hg a H hH
    rw [hN]
    simp only [Option.bind_some, List.find?_append]
    have : N.find? (fun e => decide (e.t ≤ t)) = none := by
      rw [List.find?_eq_none]
      intro e he
      have := hNt e he
      simp only [decide_eq_true_eq]
      omega
    rw [this, Option.none_or]
  | none =>
    cases hH' : m'[a]? with
    | none => rfl
    | some H' =>
      simp only [Option.bind_some, Option.bind_none]
      rw [List.find?_eq_none]
      intro e he hle
      simp only [decide_eq_true_eq] at hle
      obtain ⟨H, hH2, _⟩ := hm a H' hH' e he (Nat.le_trans hle ht)
      rw [hH] at hH2
      cases hH2

theorem wordAsOf_grow {m m' : FlatMem} {top t : Nat} (hg : memGrow m top m') (hm : memAbove m top m')
    (ht : t ≤ top) (a : PAddr) (v : BitVec 64) : wordAsOf m' a t v ↔ wordAsOf m a t v := by
  unfold wordAsOf
  simp only [FlatMem.entAsOf_grow hg hm ht]

/-- **A value-qualified racy byte stays one** (and a non-qualified one stays
non-qualified): as of a position at or below the top, under a step that adds
entries above the top only. -/
theorem racyValAt_grow {rs : List RsvRegion} {m m' : FlatMem} {top t : Nat} (hg : memGrow m top m')
    (hm : memAbove m top m') (ht : t ≤ top) (a : PAddr) : racyValAt rs m' t a ↔ racyValAt rs m t a := by
  simp only [racyValAt, racyWordOk, FlatMem.entAsOf_grow hg hm ht]

/-- **A page-table byte stays one**: as of a position at or below the top,
under a step that adds entries above the top only. -/
theorem ptByteAt_grow {rs : List RsvRegion} {m m' : FlatMem} {top t : Nat} (hg : memGrow m top m')
    (hm : memAbove m top m') (ht : t ≤ top) (a : PAddr) : ptByteAt rs m' t a ↔ ptByteAt rs m t a := by
  simp only [ptByteAt, ptRootAt, ptPageAt, ptChildAt, wordAsOf_grow hg hm ht]

theorem wordPosAsOf_grow {m m' : FlatMem} {top t : Nat} (hg : memGrow m top m') (hm : memAbove m top m')
    (ht : t ≤ top) (a : PAddr) : wordPosAsOf m' a t = wordPosAsOf m a t := by
  simp only [wordPosAsOf, FlatMem.entAsOf_grow hg hm ht]

theorem ptFreedSince_grow {rs : List RsvRegion} {m m' : FlatMem} {top t0 t : Nat} (hg : memGrow m top m')
    (hm : memAbove m top m') (ht : t ≤ top) (p : PAddr) :
    ptFreedSince rs m' t0 t p ↔ ptFreedSince rs m t0 t p := by
  unfold ptFreedSince
  constructor
  · rintro ⟨base, cnt, stride, k, t', hR, hk, h1, h2, hw⟩
    exact ⟨base, cnt, stride, k, t', hR, hk, h1, h2, (wordAsOf_grow hg hm (Nat.le_trans h2 ht) _ _).1 hw⟩
  · rintro ⟨base, cnt, stride, k, t', hR, hk, h1, h2, hw⟩
    exact ⟨base, cnt, stride, k, t', hR, hk, h1, h2, (wordAsOf_grow hg hm (Nat.le_trans h2 ht) _ _).2 hw⟩

/-- **A live page-table byte stays one** (and a non-live one stays non-live):
as of a position at or below the top, under a step that adds entries above
the top only. -/
theorem ptByteLiveAt_grow {rs : List RsvRegion} {m m' : FlatMem} {top t : Nat} (hg : memGrow m top m')
    (hm : memAbove m top m') (ht : t ≤ top) (a : PAddr) : ptByteLiveAt rs m' t a ↔ ptByteLiveAt rs m t a := by
  simp only [ptByteLiveAt, ptByteAt_grow hg hm ht, ptURootAt, ptLivePageAt, ptLiveChildAt,
    wordAsOf_grow hg hm ht, wordPosAsOf_grow hg hm ht, ptFreedSince_grow hg hm ht]

/-- A permanent-table byte is a live page-table byte (the kernel side: the
kernel table is never freed, so its walk needs no freed-check). -/
theorem ptByteLiveAt_of_ptByteAt {rs : List RsvRegion} {m : FlatMem} {t : Nat} {a : PAddr}
    (h : ptByteAt rs m t a) : ptByteLiveAt rs m t a := .inl h

/-- **A hop into a freed page is not live**: if the page `c` was pushed onto
the free list after EVERY entry of the page `p` naming it was last written,
the live walk does not go from `p` to `c`. -/
theorem ptLiveChildAt_freed {rs : List RsvRegion} {m : FlatMem} {t : Nat} {p c : PAddr}
    (h : ∀ (i : Nat) (v : BitVec 64), i < 512 → wordAsOf m (p + BitVec.ofNat 64 (8 * i)) t v → ptPtrTo v c →
      ptFreedSince rs m (wordPosAsOf m (p + BitVec.ofNat 64 (8 * i)) t) t c) :
    ¬ ptLiveChildAt rs m t p c := by
  rintro ⟨i, v, hi, hw, hp, hn⟩
  exact hn (h i v hi hw hp)

/-- **THE WINDOW IS CLOSED** (W8 (pte-ghost), [OWN.57]): a byte off the
permanent tables, every one of whose pages a freeable walk could reach was
pushed onto the free list after the word naming it was last written, is NOT
a live page-table byte.  Instances: `freewalk` `kfree`s each interior page
while its parent's slot still names it (`vm.c:273-274`), and `freeproc` frees
the root while `p->pagetable` still holds it (`proc.c:162-163`) -- from each
push on, the page's bytes are not exempt through the stale word. -/
theorem ptByteLiveAt_freed {rs : List RsvRegion} {m : FlatMem} {t : Nat} {a : PAddr}
    (hk : ¬ ptByteAt rs m t a)
    (hroot : ∀ (base : PAddr) (cnt stride k : Nat) (r : PAddr), (⟨base, .uroots cnt stride⟩ : RsvRegion) ∈ rs →
      k < cnt → wordAsOf m (base + BitVec.ofNat 64 (stride * k)) t r → r.toNat ≤ a.toNat →
      a.toNat < r.toNat + 4096 → ptFreedSince rs m (wordPosAsOf m (base + BitVec.ofNat 64 (stride * k)) t) t r)
    (hslot : ∀ (r q c : PAddr) (i : Nat) (v : BitVec 64), ptURootAt rs m t r → (q = r ∨ ptLiveChildAt rs m t r q) →
      i < 512 → wordAsOf m (q + BitVec.ofNat 64 (8 * i)) t v → ptPtrTo v c → c.toNat ≤ a.toNat →
      a.toNat < c.toNat + 4096 → ptFreedSince rs m (wordPosAsOf m (q + BitVec.ofNat 64 (8 * i)) t) t c) :
    ¬ ptByteLiveAt rs m t a := by
  rintro (h | ⟨r, p, hr, hp, h1, h2⟩)
  · exact hk h
  · have hr' := hr
    obtain ⟨_, base, cnt, stride, k, hR, hkc, hw, hn⟩ := hr'
    rcases hp with rfl | ⟨i, v, hi, hwv, hpt, hn'⟩ | ⟨q, hq, i, v, hi, hwv, hpt, hn'⟩
    · exact hn (hroot base cnt stride k _ hR hkc hw h1 h2)
    · exact hn' (hslot r r p i v hr (.inl rfl) hi hwv hpt h1 h2)
    · exact hn' (hslot r q p i v hr (.inr hq) hi hwv hpt h1 h2)

/-- **The exemption only grows** along a step that adds entries above the top
only (at the positions at or below the old top). -/
theorem chainExAt_grow {rs : List RsvRegion} {wit : List (PAddr × HEnt) → PAddr → Nat → Prop}
    {m m' : FlatMem} {top top' : Nat} (hg : memGrow m top m') (hm : memAbove m top m') (htop : top ≤ top')
    (a : PAddr) (t : Nat) (ht : t ≤ top) (h : chainExAt rs wit m top a t) : chainExAt rs wit m' top' a t := by
  rcases h with h | ⟨b, hb, hw⟩ | h | h
  · exact .inl h
  · exact .inr (.inl ⟨b, dynLkAt_mono hg htop hb, hw⟩)
  · exact .inr (.inr (.inl ((ptByteLiveAt_grow hg hm ht a).2 h)))
  · exact .inr (.inr (.inr ((racyValAt_grow hg hm ht a).2 h)))

/-- A step that leaves the memory alone keeps the exemption (any new top). -/
theorem chainExAt_top {rs : List RsvRegion} {wit : List (PAddr × HEnt) → PAddr → Nat → Prop}
    {m : FlatMem} {top top' : Nat} (htop : top ≤ top') (a : PAddr) (t : Nat)
    (h : chainExAt rs wit m top a t) : chainExAt rs wit m top' a t := by
  rcases h with h | ⟨b, hb, hw⟩ | h | h
  · exact .inl h
  · exact .inr (.inl ⟨b, dynLkAt_mono (memGrow_refl m top) htop hb, hw⟩)
  · exact .inr (.inr (.inl h))
  · exact .inr (.inr (.inr h))

end MachCSL
