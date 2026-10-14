/-
MachCSL: THE RESERVED REGIONS (W8-β′, plan rev 30 §C top / §C W8 (3)).

A RESERVED REGION is a set of whole words whose every post-power-on entry
obeys a fixed discipline, a pure fact about the byte histories that the
state interpretation carries (`MachCSL.memModelAt`'s `rsvModelAt`
conjunct).  The interpretation holds HALF of every reserved byte's
points-to from the `PowerOn` mint on, so no generic rule -- every one of
which carries the whole (`own 1`) points-to of what it writes: the S-mode
store rules, the kernel-table A/D write-back, the disk's DMA lease -- can
write a reserved byte; the dedicated rules write through the other half
(`MachCSL.writeAURsv`), and re-establish the discipline themselves.

Two kinds (the client's static list, `KernelRsv.static`, the
`KernelMap.static` pattern):

* `cpu h` at `&cpus[h]`: the three cells `c->proc` (8 bytes at +0),
  `c->noff` (4 at +120), `c->intena` (4 at +124) -- every entry after
  power-on (`e.t ≠ 0`) is authored by hart `h` (`cpuRegionOk`);
* `lock cb` at `lk`: a spinlock's lock word (4 bytes at +0) and owner
  word (8 at +16) -- after power-on, the two histories are WHOLE-WORD
  histories `W`/`W'` over the image (`wordHistAt`, tails at timestamp 0),
  every lock-word entry a hart's 0 or 1, every owner-word entry a hart's,
  the holder fold `lkFold` legal (a 0 only by the holder or from free) and,
  for the state the fold names, the spinlock kit's `lockWordAt`/`lkCpuAt`
  (`lkCpuAtP (cpuPtrAt cb)`: the owner word's entries are 0 or the writer's own
  `&cpus[c]`; xv6's `cb` is `cpus`) -- `lockRegionOk`.

The definitions `lkOne`, `wordPin`, `lockWordAt`, `latestOwn` MOVED here
from `MachCSL.Lock` (pure; names unchanged) so that the discipline can be
stated below `MachCSL.Resources`.

The pure store lemmas: a store off every region keeps `rsvAllOk`
(`rsvAllOk_store_off`); a store into one word of region `R` keeps it if it
keeps `R`'s discipline (`rsvAllOk_store_in`, by the regions' byte
disjointness `rsvWf`); the boot image satisfies it (`rsvAllOk_boot`).
-/
import MachCSL.WordHistDefs
import MachCSL.Lang
import MachCSL.Pte

namespace MachCSL

/-! ## The spinlock kit's pure discipline (moved from `MachCSL.Lock`) -/

/-- The value a taken lock word holds. -/
def lkOne : BitVec 32 := 1#32

/-- Since the winning store at `B` (by hart `i`), every store wrote 1. -/
def wordPin (W : WordHist 4) (B : Nat) (i : CPU) : Prop :=
  ∃ W1 W2, W = W1 ++ ⟨B, hartAgent i, lkOne⟩ :: W2 ∧ ∀ e ∈ W1, e.v = lkOne

/-- The word's discipline at each state. -/
def lockWordAt : Option (CPU × Bool) → Nat → WordHist 4 → Prop
  | none, _, W => curVal W 0 = 0
  | some (i, _), B, W => wordPin W B i

/-- `e` is `h`'s latest own entry of `W`. -/
def latestOwn (W : WordHist 8) (h : Agent) (e : WEnt 8) : Prop :=
  ∃ W1 W2, W = W1 ++ e :: W2 ∧ e.tid = h ∧ ∀ x ∈ W1, x.tid ≠ h

/-- An entry of the owner word: 0, or the writer's own pointer `ptr c`. -/
def cpuEntOkP (ptr : CPU → BitVec 64) (e : WEnt 8) : Prop :=
  e.v = 0 ∨ ∃ c : CPU, e.tid = hartAgent c ∧ e.v = ptr c

/-- The owner word's discipline at each state (`MachCSL.lkCpuAt` at a
pointer function; `lkCpuAt = lkCpuAtP cpuAddr` by `rfl`). -/
def lkCpuAtP (ptr : CPU → BitVec 64) (st : Option (CPU × Bool)) (W : WordHist 8) : Prop :=
  (∀ e ∈ W, cpuEntOkP ptr e) ∧
  (∀ c : CPU, st ≠ some (c, true) → ∀ e, latestOwn W (hartAgent c) e → e.v = 0) ∧
  (∀ i : CPU, st = some (i, true) → ∃ e W2, W = e :: W2 ∧ e.tid = hartAgent i ∧ e.v = ptr i)

/-! ## The holder fold -/

/-- One step of the lock-word alternation, oldest entry first: from FREE a
zero write (`initlock`) keeps it free and a nonzero write by a hart (the
winning AMO) installs that hart; from HELD a zero write is legal only by the
holder (the release) and frees it, a nonzero one (a spinner's failed AMO,
`wordPin`) changes nothing.  `none`: illegal. -/
def lkStepR : Option CPU → WEnt 4 → Option (Option CPU)
  | none, e => if e.v = 0 then some none else if h : e.tid < NCPU then some (some ⟨e.tid, h⟩) else none
  | some c, e => if e.v = 0 then (if e.tid = hartAgent c then some none else none) else some (some c)

/-- The holder after the whole history (latest first, folded oldest first). -/
def lkFold : WordHist 4 → Option (Option CPU)
  | [] => some none
  | e :: W => (lkFold W).bind (fun s => lkStepR s e)

/-- The lock's two word histories, at a state `st` and acquire position `B`:
entries after power-on by harts, the lock word 0/1, the fold legal and naming
`st`'s holder, and the kit's per-state disciplines. -/
def lockDiscW (ptr : CPU → BitVec 64) (st : Option (CPU × Bool)) (B : Nat) (W : WordHist 4)
    (W' : WordHist 8) : Prop :=
  (∀ e ∈ W, e.t ≠ 0 ∧ e.tid < NCPU ∧ (e.v = 0 ∨ e.v = lkOne)) ∧
  (∀ e ∈ W', e.t ≠ 0 ∧ e.tid < NCPU) ∧
  lkFold W = some (st.map Prod.fst) ∧ lockWordAt st B W ∧ lkCpuAtP ptr st W'

/-- Tails headed at timestamp 0 (the image entry). -/
def tailAt0 (n : Nat) (Hold : Nat → Hist) : Prop :=
  ∀ j, j < n → ∃ e H, Hold j = e :: H ∧ e.t = 0

/-- The `n` byte histories at `pa` in `m` are the word history `W` over tails
headed at the image. -/
def wordHistAt (m : FlatMem) (pa : PAddr) (n : Nat) (W : WordHist n) (Hold : Nat → Hist) : Prop :=
  (∀ j, j < n → m[pa + BitVec.ofNat 64 j]? = some (W.hist Hold j)) ∧ tailAt0 n Hold

/-- **A spinlock's reserved discipline** at `lk` (lock word at `lk`, owner word
at `lk + 16`). -/
def lockRegionOk (ptr : CPU → BitVec 64) (m : FlatMem) (lk : PAddr) : Prop :=
  ∃ (W : WordHist 4) (W' : WordHist 8) (Hold Hold' : Nat → Hist) (st : Option (CPU × Bool)) (B : Nat),
    wordHistAt m lk 4 W Hold ∧ wordHistAt m (lk + 16#64) 8 W' Hold' ∧ lockDiscW ptr st B W W'

/-! ## A spinlock's discipline over a WINDOW (W8 (f3-pipelk) [OWN.65])

A DYNAMIC spinlock (xv6: a pipe's lock, in a page `kalloc` hands out and
`kfree` takes back) is not a region of the static list: its words carry
other data before its birth and after its reclaim.  Its discipline is stated
over a WINDOW `(p, a]` of positions: the entries of its two words' bytes at
positions in the window are WHOLE-WORD entries `W`/`W'` forming a lock history
from free (`lockDiscWin`: `lockDiscW` without the power-on clause -- the
window's entries are past `p`, so past 0).  As-of-`a` and never revoked:
entries above the top never enter a window ending at or below it
(`MachCSL.lockWinAt_grow`). -/

/-- **A lock history over a window**: `lockDiscW` without its power-on
clause -- the entries by harts, the lock word 0/1, the holder fold legal and
naming `st`'s holder, the kit's per-state disciplines. -/
def lockDiscWin (ptr : CPU → BitVec 64) (st : Option (CPU × Bool)) (B : Nat) (W : WordHist 4)
    (W' : WordHist 8) : Prop :=
  (∀ e ∈ W, e.tid < NCPU ∧ (e.v = 0 ∨ e.v = lkOne)) ∧ (∀ e ∈ W', e.tid < NCPU) ∧
  lkFold W = some (st.map Prod.fst) ∧ lockWordAt st B W ∧ lkCpuAtP ptr st W'

/-- An entry is in the window `(p, a]`. -/
def lkWinIn (p a : Nat) (e : HEnt) : Bool := decide (p < e.t) && decide (e.t ≤ a)

/-- **A spinlock's discipline over the window `(p, a]`** at `lk` (lock word at
`lk`, owner word at `lk + 16`): each byte's entries in the window are the
byte projections of the word histories `W`/`W'`, which form a lock history
from free (`lockDiscWin`). -/
def lockWinAt (ptr : CPU → BitVec 64) (m : FlatMem) (lk : PAddr) (p a : Nat) : Prop :=
  ∃ (W : WordHist 4) (W' : WordHist 8) (st : Option (CPU × Bool)) (B : Nat),
    (∀ j, j < 4 → ∃ H, m[lk + BitVec.ofNat 64 j]? = some H ∧ H.filter (lkWinIn p a) = W.map (WEnt.proj j)) ∧
    (∀ j, j < 8 → ∃ H, m[lk + 16#64 + BitVec.ofNat 64 j]? = some H ∧
      H.filter (lkWinIn p a) = W'.map (WEnt.proj j)) ∧
    lockDiscWin ptr st B W W'

/-! ## Regions -/

/-- The kinds of reserved region. -/
inductive RsvKind where
  /-- hart `h`'s `struct cpu` cells -/
  | cpu (h : CPU)
  /-- a spinlock's two words; `cb` is `&cpus[0]`: hart `c` stores `cb + 128 c` to `lk->cpu` -/
  | lock (cb : BitVec 64)
  /-- a ONE-SHOT PUBLICATION word written only by hart `w` (W8 (f2-ctx)'s boot
  hop: xv6's `started`): every post-power-on entry is `w`'s, all at one
  timestamp -/
  | pub (w : CPU)
  /-- the client's DYNAMIC-LOCK SLOTS (W8 (f2-ctx) [OWN.49] (a′-r)): `cnt`
  doubleword slots at `base + stride·k` whose stores NAME a live dynamic
  spinlock (xv6: the `struct file` table's `f->pipe` words, `slotWit`); a
  registry entry -- no footprint, no discipline, so the boot's pinning of
  the list pins the slots too -/
  | slots (cnt stride : Nat)
  /-- the client's PAGE-TABLE ROOT WORDS (W8 (f2-ctx) S3, the `.pte`
  exemption, design (A′) in `PROGRESS-W8f2.md`): `cnt` doubleword slots at
  `base + stride·k`, each holding (as of a position) the physical address of a
  Sv39 root page or 0 -- xv6: `kernel_pagetable` and every `proc[i].pagetable`.
  The page-table bytes of a position are the bytes of the pages a walk reaches
  from these words AS OF that position (`MachCSL.ptByteAt`); a registry entry
  -- no footprint, no discipline.  W8 (pte-ghost) [OWN.57] [R42.1]: the
  PERMANENT roots only (xv6: `kernel_pagetable`, never freed); the roots of
  tables that are freed at run time are `uroots` -/
  | roots (cnt stride : Nat)
  /-- the client's FREEABLE page-table root words (W8 (pte-ghost) [OWN.57],
  [R42.1]): `cnt` doubleword slots at `base + stride·k` holding the root of a
  table that is FREED at run time (xv6: every `proc[i].pagetable`, freed by
  `proc_freepagetable`/`freewalk`).  The walk from these words is
  hop-restricted: a page pushed onto a registered free list (`freeHead`) after
  its naming word's last write is not walked (`MachCSL.ptByteLiveAt`); a
  registry entry -- no footprint, no discipline -/
  | uroots (cnt stride : Nat)
  /-- the client's FREE-LIST HEAD words (W8 (pte-ghost) [OWN.57], [R42.1]):
  `cnt` doubleword slots at `base + stride·k` whose stores push and pop pages
  of a free list (xv6: `kmem.freelist`, `kfree`'s push `kmem.freelist = r`):
  a page the word held after a position was FREED since that position
  (`MachCSL.ptFreedSince`); a registry entry -- no footprint, no discipline -/
  | freeHead (cnt stride : Nat)
  /-- the client's AUDITED RACY words (W8 (f2-ctx) S3; VALUE-qualified by
  W8 (f3-racy) [OWN.63]): `cnt` words of `n` bytes at `base + stride·k` that
  the client reads WITHOUT synchronization (xv6: `itable.inode[k].ref`, read
  lock-free by `ilock`'s/`iunlock`'s guard `ip->ref < 1`), with the VALUE SET
  `[vlo, vhi)` (unsigned, of the little-endian word) every unchained entry's
  word lies in: a load of them need not be chained WHEN the word, as of the
  entry's position, is in the set (`MachCSL.racyValAt`; xv6: `[1, 2^31)`, i.e.
  the signed guard reads a value `≥ 1`); a registry entry -- no footprint, no
  discipline -/
  | racy (cnt stride n vlo vhi : Nat)
  deriving DecidableEq

/-- The kinds with a footprint (all but a `.slots` registry entry). -/
def RsvKind.hasFoot : RsvKind → Bool
  | .slots _ _ => false
  | .roots _ _ => false
  | .uroots _ _ => false
  | .freeHead _ _ => false
  | .racy _ _ _ _ _ => false
  | _ => true

/-- A reserved region: its base address and kind. -/
structure RsvRegion where
  base : PAddr
  kind : RsvKind
  deriving DecidableEq

/-- The pointer hart `c` stores to a lock's `lk->cpu`, `&cpus[c]` at `cpus` base `cb`. -/
def cpuPtrAt (cb : BitVec 64) (c : CPU) : BitVec 64 := cb + BitVec.ofNat 64 (128 * c.val)

/-- The region's words (address, width). -/
def RsvRegion.words (R : RsvRegion) : List (PAddr × Nat) :=
  match R.kind with
  | .cpu _ => [(R.base, 8), (R.base + 120#64, 4), (R.base + 124#64, 4)]
  | .lock _ => [(R.base, 4), (R.base + 16#64, 8)]
  | .pub _ => [(R.base, 4)]
  | .slots _ _ => []
  | .roots _ _ => []
  | .uroots _ _ => []
  | .freeHead _ _ => []
  | .racy _ _ _ _ _ => []

/-- The bytes of a word. -/
def wordBytes (w : PAddr × Nat) : List PAddr :=
  (List.range w.2).map (fun j => w.1 + BitVec.ofNat 64 j)

/-- The region's bytes. -/
def RsvRegion.bytes (R : RsvRegion) : List PAddr := R.words.flatMap wordBytes

/-- Every reserved byte. -/
def rsvBytes (rs : List RsvRegion) : List PAddr := rs.flatMap RsvRegion.bytes

/-- `cpus[h]`'s cells: written only by `h` after power-on. -/
def cpuRegionOk (h : CPU) (m : FlatMem) (R : RsvRegion) : Prop :=
  ∀ a ∈ R.bytes, ∀ H, m[a]? = some H → ∀ e ∈ H, e.t ≠ 0 → e.tid = hartAgent h

/-- A publication word's bytes were written at most once after power-on:
every post-power-on entry is at one timestamp. -/
def oneShotOk (m : FlatMem) (R : RsvRegion) : Prop :=
  ∀ a ∈ R.bytes, ∀ H, m[a]? = some H → ∀ e ∈ H, ∀ e' ∈ H, e.t ≠ 0 → e'.t ≠ 0 → e.t = e'.t

/-- A region's discipline. -/
def regionOk (m : FlatMem) (R : RsvRegion) : Prop :=
  match R.kind with
  | .cpu h => cpuRegionOk h m R
  | .lock cb => lockRegionOk (cpuPtrAt cb) m R.base
  | .pub w => cpuRegionOk w m R ∧ oneShotOk m R
  | .slots _ _ => True
  | .roots _ _ => True
  | .uroots _ _ => True
  | .freeHead _ _ => True
  | .racy _ _ _ _ _ => True

/-- Every region of the list keeps its discipline. -/
def rsvAllOk (rs : List RsvRegion) (m : FlatMem) : Prop :=
  ∀ (i : Nat) (R : RsvRegion), rs[i]? = some R → regionOk m R

/-- The list is well formed: its bytes are pairwise distinct and every one is
a RAM byte, hence an image byte (so the mint can split its points-to); and
its regions' bases are distinct. -/
def rsvWf (rs : List RsvRegion) : Prop :=
  (rsvBytes rs).Nodup ∧ (∀ a ∈ rsvBytes rs, inRam a 1) ∧ (rs.map (fun R => R.base.toNat)).Nodup

/-- A reserved byte has an image history. -/
theorem rsvWf_img {rs : List RsvRegion} (hwf : rsvWf rs) {a : PAddr} (ha : a ∈ rsvBytes rs) :
    ((imgFlat bootImage)[a]?).isSome := by
  have hr := hwf.2.1 a ha
  rw [imgFlat_get?, if_pos hr, bootImage_get?, if_pos hr]
  rfl

/-! ## Checking a list by evaluation (linear) -/

/-- Strictly increasing addresses. -/
def strictSorted : List PAddr → Bool
  | a :: b :: l => decide (a.toNat < b.toNat) && strictSorted (b :: l)
  | _ => true

theorem strictSorted_head : ∀ (a : PAddr) (l : List PAddr), strictSorted (a :: l) = true →
    ∀ b ∈ l, a.toNat < b.toNat
  | _, [], _, b, hb => by simp at hb
  | a, c :: l, h, b, hb => by
    simp only [strictSorted, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases List.mem_cons.1 hb with rfl | hb
    · exact h.1
    · exact Nat.lt_trans h.1 (strictSorted_head c l h.2 b hb)

theorem strictSorted_nodup : ∀ l : List PAddr, strictSorted l = true → l.Nodup
  | [], _ => List.nodup_nil
  | [a], _ => List.nodup_cons.2 ⟨by simp, List.nodup_nil⟩
  | a :: b :: l, h => by
    rw [List.nodup_cons]
    refine ⟨fun hm => ?_, strictSorted_nodup (b :: l) ?_⟩
    · have := strictSorted_head a (b :: l) h a hm
      omega
    · simp only [strictSorted, Bool.and_eq_true] at h
      exact h.2

/-- The list is well formed, by evaluation: sorted bytes, all in RAM, distinct
bases. -/
theorem rsvWf_of_check (rs : List RsvRegion) (h1 : strictSorted (rsvBytes rs) = true)
    (h2 : (rsvBytes rs).all (fun a => decide (inRam a 1)) = true)
    (h3 : (rs.map (fun R => R.base.toNat)).Nodup) : rsvWf rs :=
  ⟨strictSorted_nodup _ h1, fun a ha => by
    have := List.all_eq_true.1 h2 a ha
    simpa using this, h3⟩

/-- `m'` grows `m` above `t`: every history only gained entries newer than
`t`, on top (what a machine step at top `t` does to the memory). -/
def memGrow (m : FlatMem) (t : Nat) (m' : FlatMem) : Prop :=
  ∀ (a : PAddr) (H : Hist), m[a]? = some H → ∃ N : Hist, m'[a]? = some (N ++ H) ∧ ∀ e ∈ N, t < e.t

/-- A window ending at or below `t` is unchanged by entries above `t`. -/
theorem lockWinAt_grow {ptr : CPU → BitVec 64} {m m' : FlatMem} {t : Nat} (hg : memGrow m t m') {lk : PAddr}
    {p a : Nat} (hat : a ≤ t) (h : lockWinAt ptr m lk p a) : lockWinAt ptr m' lk p a := by
  have key : ∀ (b : PAddr) (H : Hist), m[b]? = some H →
      ∃ H', m'[b]? = some H' ∧ H'.filter (lkWinIn p a) = H.filter (lkWinIn p a) := by
    intro b H hH
    obtain ⟨N, hN, hNt⟩ := hg b H hH
    refine ⟨N ++ H, hN, ?_⟩
    rw [List.filter_append, List.filter_eq_nil_iff.2 (fun e he => ?_), List.nil_append]
    have := hNt e he
    simp only [lkWinIn, Bool.and_eq_true, decide_eq_true_eq, not_and, Nat.not_le]
    intro _
    omega
  obtain ⟨W, W', st, B, h1, h2, h3⟩ := h
  refine ⟨W, W', st, B, fun j hj => ?_, fun j hj => ?_, h3⟩
  · obtain ⟨H, hH, hf⟩ := h1 j hj
    obtain ⟨H', hH', hf'⟩ := key _ H hH
    exact ⟨H', hH', hf'.trans hf⟩
  · obtain ⟨H, hH, hf⟩ := h2 j hj
    obtain ⟨H', hH', hf'⟩ := key _ H hH
    exact ⟨H', hH', hf'.trans hf⟩

/-- **The slot witness of the dynamic hop registry** (W8 (f2-ctx) [OWN.49]
(a′-r), the RULED (a′) window [OWN.46]): `L` is the eight entries of ONE
doubleword store, by one agent at position `te`, of the value `b` into a
slot the list registers (`.slots`) -- xv6: `f->pipe = pi` into a `struct
file` slot.  The machine's registry (`MachCSL.dynLkAt`) closes the window at
the first non-word entry on `b`'s lock word (`kfree`'s junk fill). -/
def slotWit (rs : List RsvRegion) (L : List (PAddr × HEnt)) (b : PAddr) (te : Nat) : Prop :=
  ∃ (base : PAddr) (cnt stride k : Nat) (g : Agent), (⟨base, .slots cnt stride⟩ : RsvRegion) ∈ rs ∧ k < cnt ∧
    L = (List.range 8).map (fun j =>
      (base + BitVec.ofNat 64 (stride * k) + BitVec.ofNat 64 j, (⟨te, g, nthByte (n := 8) b j⟩ : HEnt)))

/-- **The client's static reserved regions** (the `KernelMap.static`
pattern): reserved at the `PowerOn` mint, from timestamp 0, never released
(W8 (f2-ctx) [OWN.49] (a′-r): with its dynamic-lock slots, `.slots`). -/
class KernelRsv where
  static : List RsvRegion
  wf : rsvWf static

/-! ## Membership facts -/

/-- Setting a list's entry to the value it holds. -/
theorem rsvSetSelf {α : Type _} {l : List α} {i : Nat} {x : α} (h : l[i]? = some x) : l.set i x = l := by
  obtain ⟨hlt, heq⟩ := List.getElem?_eq_some_iff.mp h
  subst heq
  exact List.set_getElem_self hlt

theorem mem_wordBytes {w : PAddr × Nat} {j : Nat} (hj : j < w.2) :
    w.1 + BitVec.ofNat 64 j ∈ wordBytes w :=
  List.mem_map.2 ⟨j, List.mem_range.2 hj, rfl⟩

theorem mem_regionBytes {R : RsvRegion} {w : PAddr × Nat} (hw : w ∈ R.words) {j : Nat} (hj : j < w.2) :
    w.1 + BitVec.ofNat 64 j ∈ R.bytes :=
  List.mem_flatMap.2 ⟨w, hw, mem_wordBytes hj⟩

theorem mem_rsvBytes {rs : List RsvRegion} {i : Nat} {R : RsvRegion} (hi : rs[i]? = some R) {a : PAddr}
    (ha : a ∈ R.bytes) : a ∈ rsvBytes rs :=
  List.mem_flatMap.2 ⟨R, List.mem_of_getElem? hi, ha⟩

/-- A region's base is one of its bytes (every kind with a footprint). -/
theorem RsvRegion.base_mem (R : RsvRegion) (hk : R.kind.hasFoot = true) : R.base ∈ R.bytes := by
  have hw : ∃ n, 0 < n ∧ (R.base, n) ∈ R.words := by
    unfold RsvRegion.words
    cases h : R.kind with
    | slots _ _ => rw [h] at hk; simp [RsvKind.hasFoot] at hk
    | roots _ _ => rw [h] at hk; simp [RsvKind.hasFoot] at hk
    | uroots _ _ => rw [h] at hk; simp [RsvKind.hasFoot] at hk
    | freeHead _ _ => rw [h] at hk; simp [RsvKind.hasFoot] at hk
    | racy _ _ _ _ _ => rw [h] at hk; simp [RsvKind.hasFoot] at hk
    | _ => exact ⟨_, by decide, List.mem_cons_self⟩
  obtain ⟨n, hn, hw⟩ := hw
  have := mem_regionBytes hw hn
  simpa using this

/-- Two regions at different indices of a byte-distinct list share no byte. -/
theorem rsvBytes_disjoint {rs : List RsvRegion} (hnd : (rsvBytes rs).Nodup) :
    ∀ {i i' : Nat} {R R' : RsvRegion}, rs[i]? = some R → rs[i']? = some R' → i ≠ i' →
      ∀ a, a ∈ R.bytes → a ∉ R'.bytes := by
  induction rs with
  | nil => intro i _ _ _ hi; simp at hi
  | cons R0 rs ih =>
    intro i i' R R' hi hi' hne a ha ha'
    unfold rsvBytes at hnd
    rw [List.flatMap_cons, List.nodup_append] at hnd
    obtain ⟨_, hnd2, hdis⟩ := hnd
    cases i with
    | zero =>
      cases i' with
      | zero => exact hne rfl
      | succ i' =>
        simp only [List.getElem?_cons_zero, Option.some.injEq, List.getElem?_cons_succ] at hi hi'
        subst hi
        exact hdis a ha a (List.mem_flatMap.2 ⟨R', List.mem_of_getElem? hi', ha'⟩) rfl
    | succ i =>
      cases i' with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq, List.getElem?_cons_succ] at hi hi'
        subst hi'
        exact hdis a ha' a (List.mem_flatMap.2 ⟨R, List.mem_of_getElem? hi, ha⟩) rfl
      | succ i' =>
        simp only [List.getElem?_cons_succ] at hi hi'
        exact ih hnd2 hi hi' (fun h => hne (by rw [h])) a ha ha'

/-! ## Stability -/

theorem wordHistAt_congr {m m' : FlatMem} {pa : PAddr} {n : Nat} {W : WordHist n} {Hold : Nat → Hist}
    (h : ∀ j, j < n → m'[pa + BitVec.ofNat 64 j]? = m[pa + BitVec.ofNat 64 j]?)
    (hw : wordHistAt m pa n W Hold) : wordHistAt m' pa n W Hold :=
  ⟨fun j hj => (h j hj).trans (hw.1 j hj), hw.2⟩

/-- A region's discipline reads only the region's bytes. -/
theorem regionOk_congr {m m' : FlatMem} {R : RsvRegion}
    (h : ∀ a ∈ R.bytes, m'[a]? = m[a]?) (hR : regionOk m R) : regionOk m' R := by
  unfold regionOk at hR ⊢
  cases hk : R.kind with
  | slots _ _ => trivial
  | roots _ _ => trivial
  | uroots _ _ => trivial
  | freeHead _ _ => trivial
  | racy _ _ _ _ _ => trivial
  | cpu c =>
    rw [hk] at hR
    intro a ha H hH
    exact hR a ha H ((h a ha).symm.trans hH)
  | lock cb =>
    rw [hk] at hR
    obtain ⟨W, W', Hold, Hold', st, B, h1, h2, h3⟩ := hR
    have hw : R.words = [(R.base, 4), (R.base + 16#64, 8)] := by unfold RsvRegion.words; rw [hk]
    refine ⟨W, W', Hold, Hold', st, B, wordHistAt_congr (fun j hj => h _ ?_) h1,
      wordHistAt_congr (fun j hj => h _ ?_) h2, h3⟩
    · exact mem_regionBytes (w := (R.base, 4)) (by rw [hw]; simp) hj
    · exact mem_regionBytes (w := (R.base + 16#64, 8)) (by rw [hw]; simp) hj
  | pub w =>
    rw [hk] at hR
    obtain ⟨h1, h2⟩ := hR
    exact ⟨fun a ha H hH => h1 a ha H ((h a ha).symm.trans hH),
      fun a ha H hH => h2 a ha H ((h a ha).symm.trans hH)⟩

/-- A store whose bytes lie off every region keeps every discipline. -/
theorem rsvAllOk_store_off {rs : List RsvRegion} {m : FlatMem} {pa : PAddr} {n : Nat}
    (w : BitVec (8 * n)) (t : Nat) (h : Agent)
    (hoff : ∀ j, j < n → pa + BitVec.ofNat 64 j ∉ rsvBytes rs) (hok : rsvAllOk rs m) :
    rsvAllOk rs (m.writeBytes pa n w t h) := by
  intro i R hi
  refine regionOk_congr (fun a ha => FlatMem.writeBytes_get?_notin _ _ _ _ _ _ ?_) (hok i R hi)
  intro j hj heq
  exact hoff j hj (heq ▸ mem_rsvBytes hi ha)

/-- A store into one word of region `R` (index `i`) keeps every discipline
if it keeps `R`'s. -/
theorem rsvAllOk_store_in {rs : List RsvRegion} {m : FlatMem} {pa : PAddr} {n : Nat}
    (w : BitVec (8 * n)) (t : Nat) (h : Agent) (hnd : (rsvBytes rs).Nodup)
    {i : Nat} {R : RsvRegion} (hi : rs[i]? = some R) (hw : (pa, n) ∈ R.words)
    (hR : regionOk m R → regionOk (m.writeBytes pa n w t h) R) (hok : rsvAllOk rs m) :
    rsvAllOk rs (m.writeBytes pa n w t h) := by
  intro i' R' hi'
  by_cases hii : i = i'
  · subst hii
    rw [hi] at hi'
    obtain rfl := Option.some.inj hi'
    exact hR (hok i R hi)
  · refine regionOk_congr (fun a ha => FlatMem.writeBytes_get?_notin _ _ _ _ _ _ ?_) (hok i' R' hi')
    intro j hj heq
    exact rsvBytes_disjoint hnd hi hi' hii _ (mem_regionBytes hw hj) (heq ▸ ha)


/-! ## Where a store's entries go -/

theorem rsvPushEntry (m : FlatMem) (b a : PAddr) (e0 e : HEnt) (H : Hist)
    (hH : (m.push b e0)[a]? = some H) (he : e ∈ H) : (∃ H0, m[a]? = some H0 ∧ e ∈ H0) ∨ e = e0 := by
  by_cases hab : a = b
  · subst hab
    rw [FlatMem.push_get?_eq] at hH
    obtain rfl := Option.some.inj hH
    rcases List.mem_cons.1 he with rfl | he
    · exact Or.inr rfl
    · left
      rw [Std.ExtTreeMap.getD_eq_getD_getElem?] at he
      cases hm : m[a]? with
      | none => rw [hm] at he; simp at he
      | some H0 => rw [hm] at he; exact ⟨H0, rfl, he⟩
  · rw [FlatMem.push_get?_ne _ _ _ _ hab] at hH
    exact Or.inl ⟨H, hH, he⟩

/-- Every entry after a store is an entry from before, or the store's. -/
theorem rsvWriteEntry {n : Nat} (pa : PAddr) (w : BitVec (8 * n)) (t : Nat) (h : Agent) (a : PAddr) (e : HEnt) :
    ∀ (l : List Nat) (m : FlatMem) (H : Hist),
      (l.foldl (fun (m : FlatMem) j => m.push (pa + BitVec.ofNat 64 j) ⟨t, h, nthByte w j⟩) m)[a]? = some H →
      e ∈ H → (∃ H0, m[a]? = some H0 ∧ e ∈ H0) ∨ (e.t = t ∧ e.tid = h)
  | [], m, H, hH, he => Or.inl ⟨H, hH, he⟩
  | j :: l, m, H, hH, he => by
    simp only [List.foldl_cons] at hH
    rcases rsvWriteEntry pa w t h a e l _ H hH he with ⟨H1, hH1, he1⟩ | h2
    · rcases rsvPushEntry m _ a _ e H1 hH1 he1 with h3 | rfl
      · exact Or.inl h3
      · exact Or.inr ⟨rfl, rfl⟩
    · exact Or.inr h2

/-- A store by `cpus[h]`'s own hart keeps its cells' discipline. -/
theorem cpuRegion_store {h : CPU} {R : RsvRegion} (hk : R.kind = .cpu h) (m : FlatMem) (pa : PAddr) (n : Nat)
    (w : BitVec (8 * n)) (t : Nat) (hR : regionOk m R) : regionOk (m.writeBytes pa n w t (hartAgent h)) R := by
  unfold regionOk at hR ⊢
  rw [hk] at hR ⊢
  intro a ha H hH e he het
  rcases rsvWriteEntry pa w t (hartAgent h) a e (List.range n) m H hH he with ⟨H0, hH0, he0⟩ | ⟨_, htid⟩
  · exact hR a ha H0 hH0 e he0 het
  · exact htid

/-- The boot image satisfies every discipline. -/
theorem rsvAllOk_boot {rs : List RsvRegion} (hwf : rsvWf rs) : rsvAllOk rs (imgFlat bootImage) := by
  intro i R hi
  have himg : ∀ a ∈ R.bytes, ∃ v, (imgFlat bootImage)[a]? = some [⟨0, 0, v⟩] := by
    intro a ha
    have hs := rsvWf_img hwf (mem_rsvBytes hi ha)
    rw [imgFlat_get?] at hs ⊢
    split at hs
    · rename_i hram
      cases hv : bootImage[a]? with
      | none => rw [hv] at hs; simp at hs
      | some v => exact ⟨v, by simp [hram]⟩
    · simp at hs
  unfold regionOk
  cases hk : R.kind with
  | slots _ _ => trivial
  | roots _ _ => trivial
  | uroots _ _ => trivial
  | freeHead _ _ => trivial
  | racy _ _ _ _ _ => trivial
  | cpu c =>
    intro a ha H hH e he het
    obtain ⟨v, hv⟩ := himg a ha
    rw [hv] at hH
    obtain rfl := Option.some.inj hH
    simp only [List.mem_singleton] at he
    subst he
    exact absurd rfl het
  | lock cb =>
    have hw : R.words = [(R.base, 4), (R.base + 16#64, 8)] := by unfold RsvRegion.words; rw [hk]
    have hb : ∀ (o : PAddr) (n j : Nat), (o, n) ∈ R.words → j < n →
        ∃ v, (imgFlat bootImage)[o + BitVec.ofNat 64 j]? = some [⟨0, 0, v⟩] :=
      fun o n j ho hj => himg _ (mem_regionBytes (w := (o, n)) ho hj)
    refine ⟨[], [], fun j => ((imgFlat bootImage)[R.base + BitVec.ofNat 64 j]?).getD [],
      fun j => ((imgFlat bootImage)[R.base + 16#64 + BitVec.ofNat 64 j]?).getD [], none, 0,
      ⟨fun j hj => ?_, fun j hj => ?_⟩, ⟨fun j hj => ?_, fun j hj => ?_⟩, ?_⟩
    · obtain ⟨v, hv⟩ := hb R.base 4 j (by rw [hw]; simp) hj
      simp [WordHist.hist, hv]
    · obtain ⟨v, hv⟩ := hb R.base 4 j (by rw [hw]; simp) hj
      exact ⟨⟨0, 0, v⟩, [], by simp [hv], rfl⟩
    · obtain ⟨v, hv⟩ := hb (R.base + 16#64) 8 j (by rw [hw]; simp) hj
      simp [WordHist.hist, hv]
    · obtain ⟨v, hv⟩ := hb (R.base + 16#64) 8 j (by rw [hw]; simp) hj
      exact ⟨⟨0, 0, v⟩, [], by simp [hv], rfl⟩
    · refine ⟨fun e he => by simp at he, fun e he => by simp at he, rfl, rfl, ?_⟩
      refine ⟨fun e he => by simp at he, fun c _ e hl => ?_, fun i hi => by simp at hi⟩
      obtain ⟨W1, W2, hW, _, _⟩ := hl
      cases W1 <;> cases hW
  | pub w =>
    refine ⟨fun a ha H hH e he het => ?_, fun a ha H hH e he e' _ het _ => ?_⟩
    · obtain ⟨v, hv⟩ := himg a ha
      rw [hv] at hH
      obtain rfl := Option.some.inj hH
      simp only [List.mem_singleton] at he
      subst he
      exact absurd rfl het
    · obtain ⟨v, hv⟩ := himg a ha
      rw [hv] at hH
      obtain rfl := Option.some.inj hH
      simp only [List.mem_singleton] at he
      subst he
      exact absurd rfl het


/-! ## The sealed kernel page table's slots (W8 (f3-ptek) [OWN.66])

After the kernel page table is SEALED (`MachCSL.kptOn_seal`) every slot of
it -- the root word and every entry of every page the table occupies -- is
registered with the state interpretation (`MachCSL.kptModelAt`): a FROZEN
slot (the root word, a pointer or an empty entry) is never written again (the
interpretation holds a discarded fragment of its bytes), a LEAF only by a
hart's whole-doubleword A/D write-back of a variant of its canonical value
(the interpretation holds half of its bytes, the table's invariant the other
half; `MachCSL.kpt_exclWriteAU` the only writer).  The discipline is stated
on the fragment's ghost histories (`kslotHistOk`), so no machine step but
the leaf's own write-back can disturb it.  Spec: the privileged spec's Svadu
A/D update is atomic per PTE; Sail performs it as
`read_pte_exclusive`/`write_pte_conditional` (`Vmem.lean:237`/`:228`) -- one
whole doubleword store of the same entry with A/D possibly set. -/

/-- The values an entry of canonical value `c` may hold: a leaf at any
A/D, anything else exactly. -/
def pteVariant (c v : BitVec 64) : Prop :=
  v = c ∨ ∃ (ppn : BitVec 44) (perm : KPerm) (a d a' d' : BitVec 1), c = kLeaf ppn perm a d ∧ v = kLeaf ppn perm a' d'

/-- A sealed slot: its (doubleword-aligned) address, its canonical value,
and whether it is frozen (the root word, a pointer, an empty entry) or a
leaf. -/
structure KSlot where
  addr : PAddr
  c : BitVec 64
  frozen : Bool
  deriving DecidableEq

/-- The eight histories `Hs` hold the doubleword `v` as of position `t`
(`MachCSL.wordAsOf` on histories). -/
def histWordAsOf (Hs : Nat → Hist) (t : Nat) (v : BitVec 64) : Prop :=
  ∀ j, j < 8 → ((Hs j).find? (fun e => decide (e.t ≤ t))).map HEnt.v = some (nthByte (n := 8) v j)

/-- **A sealed slot's discipline** on its eight histories, sealed at `S`: as
of `S` the slot holds its canonical value (a frozen slot) or a variant of it
(a leaf); every entry after `S` is a leaf's, by a hart, and one byte of a
WHOLE-doubleword store (same position, same author, every byte) of a variant
of the canonical value. -/
def kslotHistOk (S : Nat) (d : KSlot) (Hs : Nat → Hist) : Prop :=
  (∃ v : BitVec 64, histWordAsOf Hs S v ∧ (if d.frozen then v = d.c else pteVariant d.c v)) ∧
  ∀ j, j < 8 → ∀ e ∈ Hs j, S < e.t → d.frozen = false ∧ e.tid < NCPU ∧
    ∃ v : BitVec 64, pteVariant d.c v ∧ e.v = nthByte (n := 8) v j ∧
      ∀ j', j' < 8 → (⟨e.t, e.tid, nthByte (n := 8) v j'⟩ : HEnt) ∈ Hs j'

/-- The discipline reads only the eight histories. -/
theorem kslotHistOk_congr {S : Nat} {d : KSlot} {Hs Hs' : Nat → Hist} (h : ∀ j, j < 8 → Hs j = Hs' j)
    (hk : kslotHistOk S d Hs) : kslotHistOk S d Hs' := by
  obtain ⟨⟨v0, hv0, hc0⟩, hent⟩ := hk
  refine ⟨⟨v0, fun j hj => by rw [← h j hj]; exact hv0 j hj, hc0⟩, fun j hj e he het => ?_⟩
  rw [← h j hj] at he
  obtain ⟨h1, h2, w, hw, hwv, hall⟩ := hent j hj e he het
  exact ⟨h1, h2, w, hw, hwv, fun j' hj' => by rw [← h j' hj']; exact hall j' hj'⟩

/-- A whole-doubleword hart store of a variant at a position `t` past the
seal keeps a LEAF's discipline (the as-of-`S` value is unchanged). -/
theorem kslotHistOk_push {S : Nat} {d : KSlot} {Hs : Nat → Hist} (h : kslotHistOk S d Hs)
    (hleaf : d.frozen = false) (t : Nat) (hSt : S < t) (g : Agent) (hg : g < NCPU) (v : BitVec 64)
    (hv : pteVariant d.c v) :
    kslotHistOk S d (fun j => (⟨t, g, nthByte (n := 8) v j⟩ : HEnt) :: Hs j) := by
  obtain ⟨⟨v0, hv0, hc0⟩, hent⟩ := h
  refine ⟨⟨v0, fun j hj => ?_, hc0⟩, fun j hj e he het => ?_⟩
  · have hn : ¬ (t ≤ S) := by omega
    simp only [List.find?_cons, hn, decide_false]
    exact hv0 j hj
  · rcases List.mem_cons.1 he with rfl | he
    · exact ⟨hleaf, hg, v, hv, rfl, fun j' _ => List.mem_cons_self⟩
    · obtain ⟨h1, h2, w, hw, hwv, hall⟩ := hent j hj e he het
      exact ⟨h1, h2, w, hw, hwv, fun j' hj' => List.mem_cons_of_mem _ (hall j' hj')⟩


/-! ## Unwritten publication words (W8 (f3-ptek)) -/

/-- Every publication word of `rs` is never written since power-on at `m`
(before the kernel table's seal: `MachCSL.kptModelAt`). -/
def pubClean (rs : List RsvRegion) (m : FlatMem) : Prop :=
  ∀ (f : PAddr) (w : CPU), (⟨f, .pub w⟩ : RsvRegion) ∈ rs → ∀ a ∈ (⟨f, .pub w⟩ : RsvRegion).bytes,
    ∀ H, m[a]? = some H → ∀ e ∈ H, e.t = 0

/-- A store off every region keeps the publication words unwritten. -/
theorem pubClean_store_off {rs : List RsvRegion} {m : FlatMem} {pa : PAddr} {n : Nat}
    (w : BitVec (8 * n)) (t : Nat) (h : Agent)
    (hoff : ∀ j, j < n → pa + BitVec.ofNat 64 j ∉ rsvBytes rs) (hc : pubClean rs m) :
    pubClean rs (m.writeBytes pa n w t h) := by
  intro f w' hf a ha H hH
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hf
  rw [FlatMem.writeBytes_get?_notin _ _ _ _ _ _ (fun j hj heq => hoff j hj (heq ▸ mem_rsvBytes hi ha))] at hH
  exact hc f w' hf a ha H hH

/-- A store into a word of a region that is no publication word keeps the
publication words unwritten. -/
theorem pubClean_store_in {rs : List RsvRegion} {m : FlatMem} {pa : PAddr} {n : Nat}
    (w : BitVec (8 * n)) (t : Nat) (h : Agent) (hnd : (rsvBytes rs).Nodup)
    {i : Nat} {R : RsvRegion} (hi : rs[i]? = some R) (hw : (pa, n) ∈ R.words)
    (hnp : ∀ w', R.kind ≠ .pub w') (hc : pubClean rs m) :
    pubClean rs (m.writeBytes pa n w t h) := by
  intro f w' hf a ha H hH
  obtain ⟨i', hi'⟩ := List.mem_iff_getElem?.1 hf
  have hii : i ≠ i' := by
    intro he
    subst he
    rw [hi] at hi'
    obtain rfl := Option.some.inj hi'
    exact hnp w' rfl
  rw [FlatMem.writeBytes_get?_notin _ _ _ _ _ _
    (fun j hj heq => rsvBytes_disjoint hnd hi hi' hii _ (mem_regionBytes hw hj) (heq ▸ ha))] at hH
  exact hc f w' hf a ha H hH

/-- At power-on no publication word is written. -/
theorem pubClean_boot {rs : List RsvRegion} (hwf : rsvWf rs) : pubClean rs (imgFlat bootImage) := by
  intro f w hf a ha H hH e he
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hf
  have hs := rsvWf_img hwf (mem_rsvBytes hi ha)
  rw [imgFlat_get?] at hs hH
  split at hs
  · rename_i hram
    cases hv : bootImage[a]? with
    | none => rw [hv] at hs; simp at hs
    | some v =>
      simp [hram, hv] at hH
      subst hH
      simp only [List.mem_singleton] at he
      subst he
      rfl
  · simp at hs

end MachCSL
