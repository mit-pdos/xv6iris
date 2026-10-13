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
  lets only the lock rules write the byte -- and the release entry sits
  above a NONZERO entry, so the lock was held when `A` wrote 0 (the region
  discipline: a 0 from HELD only by the holder, `MachCSL.lkStepR`).  An
  `initlock` zero (from FREE) is never a hop.
* **A chain** (`hopChain m isLk A t B a`): `t < r₀` (the entry precedes the
  author's release), the releaser of hop k+1 is the acquirer of hop k, which
  acquired before releasing (`a_k < r_{k+1}`), the last acquirer is `B`, at
  `a`.  Each author's chained entries form a PREFIX (`hopChain_prefix`):
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

/-! ## Lock bytes of a region list -/

/-- `b` is the lock word (its low byte) of a reserved spinlock of `rs`. -/
def lockByteIn (rs : List RsvRegion) (b : PAddr) : Prop :=
  ∃ cb : BitVec 64, (⟨b, .lock cb⟩ : RsvRegion) ∈ rs

/-! ## Hops and chains -/

/-- **A release → acquire hop** at the lock byte `b`: the acquire entry
`⟨a, B, va⟩` (nonzero) immediately above the release entry `⟨r, A, 0⟩`,
itself above a nonzero entry (the lock was held). -/
def syncHop (m : FlatMem) (b : PAddr) (A : CPU) (r : Nat) (B : CPU) (a : Nat) : Prop :=
  ∃ (H1 H2 : Hist) (e0 : HEnt) (va : BitVec 8),
    m[b]? = some (H1 ++ ⟨a, hartAgent B, va⟩ :: ⟨r, hartAgent A, 0⟩ :: e0 :: H2) ∧ va ≠ 0 ∧ e0.v ≠ 0

/-- **A sync chain** from the entries of author `A` at or below `t` to hart
`B`, whose last acquire is at `a`. -/
inductive hopChain (m : FlatMem) (isLk : PAddr → Prop) : CPU → Nat → CPU → Nat → Prop
  /-- one hop: `A` released after its entry -/
  | base {A B : CPU} {t r a : Nat} (b : PAddr) :
      isLk b → syncHop m b A r B a → t < r → hopChain m isLk A t B a
  /-- one more hop: the last acquirer `C` released after its acquire -/
  | step {A C B : CPU} {t a1 r a : Nat} (b : PAddr) :
      hopChain m isLk A t C a1 → isLk b → syncHop m b C r B a → a1 < r → hopChain m isLk A t B a

theorem syncHop_mono {m m' : FlatMem} (hx : memExt m m') {b : PAddr} {A : CPU} {r : Nat} {B : CPU} {a : Nat}
    (h : syncHop m b A r B a) : syncHop m' b A r B a := by
  obtain ⟨H1, H2, e0, va, hb, hva, he0⟩ := h
  obtain ⟨N, hN⟩ := hx b _ hb
  exact ⟨N ++ H1, H2, e0, va, by rw [hN, List.append_assoc], hva, he0⟩

theorem hopChain_mono {m m' : FlatMem} {isLk isLk' : PAddr → Prop} (hx : memExt m m')
    (hl : ∀ b, isLk b → isLk' b) {A : CPU} {t : Nat} {B : CPU} {a : Nat}
    (h : hopChain m isLk A t B a) : hopChain m' isLk' A t B a := by
  induction h with
  | base b hb hh ht => exact .base b (hl b hb) (syncHop_mono hx hh) ht
  | step b _ hb hh ha ih => exact .step b ih (hl b hb) (syncHop_mono hx hh) ha

/-- Each author's chained entries form a prefix. -/
theorem hopChain_prefix {m : FlatMem} {isLk : PAddr → Prop} {A : CPU} {t : Nat} {B : CPU} {a : Nat}
    (h : hopChain m isLk A t B a) {t' : Nat} (ht : t' ≤ t) : hopChain m isLk A t' B a := by
  induction h with
  | base b hb hh hr => exact .base b hb hh (by omega)
  | step b _ hb hh ha ih => exact .step b (ih ht) hb hh ha

/-- A hop's acquire is an entry of the memory, authored by the acquirer. -/
theorem syncHop_acq_ent {m : FlatMem} {b : PAddr} {A : CPU} {r : Nat} {B : CPU} {a : Nat}
    (h : syncHop m b A r B a) : ∃ (H : Hist) (e : HEnt), m[b]? = some H ∧ e ∈ H ∧ e.t = a := by
  obtain ⟨H1, H2, e0, va, hb, _, _⟩ := h
  exact ⟨_, ⟨a, hartAgent B, va⟩, hb, List.mem_append_right _ List.mem_cons_self, rfl⟩

/-- A chain's last acquire is an entry of the memory. -/
theorem hopChain_acq_ent {m : FlatMem} {isLk : PAddr → Prop} {A : CPU} {t : Nat} {B : CPU} {a : Nat}
    (h : hopChain m isLk A t B a) : ∃ (b : PAddr) (H : Hist) (e : HEnt), m[b]? = some H ∧ e ∈ H ∧ e.t = a := by
  cases h with
  | base b _ hh _ => exact ⟨b, syncHop_acq_ent hh⟩
  | step b _ _ hh _ => exact ⟨b, syncHop_acq_ent hh⟩

/-- The hop a winning AMO makes: on top of a history headed by the release
entry `⟨r, A, 0⟩` over a nonzero entry, the acquire entry `⟨a, B, va⟩`. -/
theorem syncHop_of_head {m : FlatMem} {b : PAddr} {A : CPU} {r : Nat} {B : CPU} {a : Nat} {va : BitVec 8}
    {e0 : HEnt} {H2 : Hist} (hb : m[b]? = some (⟨a, hartAgent B, va⟩ :: ⟨r, hartAgent A, 0⟩ :: e0 :: H2))
    (hva : va ≠ 0) (he0 : e0.v ≠ 0) : syncHop m b A r B a :=
  ⟨[], H2, e0, va, by simpa using hb, hva, he0⟩

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
coherence floors (`HRead.coh`), the lock bytes (the hop registry), and the
PUBLICATION bytes with their sole writer (the boot hop: `started`, written
once by hart 0 and read racily by the others). -/
structure ChainEnv where
  m : FlatMem
  coh : CPU → PAddr → Nat
  isLk : PAddr → Prop
  isPub : PAddr → CPU → Prop

/-- `Y` extends `X`: histories grew on top, the lock registry grew, the
publication registry is the same, and no hart's coherence floor at a
publication byte of another writer went down (a load only raises it; the
region discipline keeps every other hart's store off the byte). -/
def ChainEnv.ext (X Y : ChainEnv) : Prop :=
  memExt X.m Y.m ∧ (∀ b, X.isLk b → Y.isLk b) ∧ (∀ f w, X.isPub f w ↔ Y.isPub f w) ∧
    (∀ (j : CPU) (f : PAddr) (w : CPU), X.isPub f w → j ≠ w → X.coh j f ≤ Y.coh j f)

theorem ChainEnv.ext_refl (X : ChainEnv) : X.ext X :=
  ⟨memExt_refl _, fun _ h => h, fun _ _ => Iff.rfl, fun _ _ _ _ _ => Nat.le_refl _⟩

theorem ChainEnv.ext_trans {X Y Z : ChainEnv} (h1 : X.ext Y) (h2 : Y.ext Z) : X.ext Z :=
  ⟨memExt_trans h1.1 h2.1, fun b h => h2.2.1 b (h1.2.1 b h), fun f w => (h1.2.2.1 f w).trans (h2.2.2.1 f w),
    fun j f w hp hj => Nat.le_trans (h1.2.2.2 j f w hp hj) (h2.2.2.2 j f w ((h1.2.2.1 f w).1 hp) hj)⟩

/-- **The boot hop's cover**: the entries of the publication writer `h` at or
below `t` precede one of its stores to a publication byte `f`, which hart
`j ≠ h` has read (its coherence floor at `f` reached it). -/
def pubCover (X : ChainEnv) (h : CPU) (t : Nat) (j : CPU) : Prop :=
  h ≠ j ∧ ∃ (f : PAddr) (r : Nat) (v : BitVec 8) (H : Hist),
    X.isPub f h ∧ X.m[f]? = some H ∧ ⟨r, hartAgent h, v⟩ ∈ H ∧ t < r ∧ r ≤ X.coh j f

theorem pubCover_mono {X Y : ChainEnv} (hx : X.ext Y) {h : CPU} {t : Nat} {j : CPU}
    (hc : pubCover X h t j) : pubCover Y h t j := by
  obtain ⟨hne, f, r, v, H, hp, hf, he, ht, hr⟩ := hc
  obtain ⟨N, hN⟩ := hx.1 f H hf
  exact ⟨hne, f, r, v, N ++ H, (hx.2.2.1 f h).1 hp, hN, List.mem_append_right _ he, ht,
    Nat.le_trans hr (hx.2.2.2 j f h hp (Ne.symm hne))⟩

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
  rcases hv with ⟨h1, h2⟩ | ⟨a, ha, hc⟩ | ⟨hne, f, r, v, H, hp, hf, he, htr, hr⟩
  · exact .inl ⟨h1, by simp only at h2 ⊢; omega⟩
  · exact .inr (.inl ⟨a, by simp only at ha ⊢; omega, hopChain_prefix hc ht⟩)
  · exact .inr (.inr ⟨hne, f, r, v, H, hp, hf, he, by simp only at htr ⊢; omega, hr⟩)

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
    (hv : ChainCert.valid X ⟨h, t, A, r⟩) (hb : X.isLk b) (hh : syncHop X.m b A r B a)
    (hall : ∀ (b' : PAddr) (H : Hist) (e : HEnt), X.m[b']? = some H → e ∈ H → e.t ≤ a)
    (hone : pubOneShot X) (hgate : gateOk X B) : ChainCert.valid X ⟨h, t, B, a + 1⟩ := by
  rcases hv with ⟨h1, h2⟩ | ⟨a1, ha1, hc⟩ | ⟨hne, f, r', v, H, hp, hf, he, htr, hr⟩
  · simp only at h1 h2
    subst h1
    exact .inr (.inl ⟨a, Nat.lt_succ_self a, .base b hb hh h2⟩)
  · exact .inr (.inl ⟨a, Nat.lt_succ_self a, .step b hc hb hh ha1⟩)
  · simp only at hne htr hr hp
    by_cases hBh : h = B
    · -- the writer itself: its own entries, all at or below the acquire
      subst hBh
      have hle : r' ≤ a := hall f H _ hf he
      exact .inl ⟨rfl, show t < a + 1 by omega⟩
    · obtain ⟨r2, v2, H2, hf2, he2, hr20, hr2⟩ := hgate f h hp (Ne.symm hBh)
      rw [hf] at hf2
      cases hf2
      have heq : r' = r2 := hone f h H _ _ hp hf he he2 (show r' ≠ 0 by omega) (show r2 ≠ 0 by omega)
      subst heq
      exact .inr (.inr ⟨hBh, f, r', v2, H, hp, hf, he2, htr, hr2⟩)

end MachCSL
