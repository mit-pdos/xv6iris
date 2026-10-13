/-
Weak: **W4 F9 — the virtio half of the disk rows** (allocproc plan `notes/weak-allocproc-plan.md`
§C W4 F9, §C W-DISK "LANDED — the record"; [R18.3] [R19.1]–[R19.3] [R20.1] [R21.3]).
Lean-only (no Rocq source).  Everything here is about ONE device, the virtio disk, on both sides
of the simulation `Weak/MachOfPf.lean` proves: the pf disk agent's residual program (`DM Dres`,
`Weak/VirtioProg.lean`) and MachCSL's virtio threads (`Virtio.body` / `Virtio.serve`,
`MachCSL/Dev/Virtio.lean`).  `MachOfPf.lean` imports it and proves the rows.

*Spec, stated first* (plan §C W-DISK): virtio 1.x fixes what the device reads and writes, not
how its steps interleave; RVWMO / riscv.cat / Sail have NO device-internal events and Zifencei /
the PMAs are silent — every device-internal step below is MODEL text, the model of record is
MachCSL's.  Nothing here changes either model: it relates them.

## Contents

1. `DevStates` algebra (`dsExt`, `setSet`, `setComm`).
2. **`cacheWf`** — the cache's keys are distinct and every entry is at most one sector: an
   invariant of every state either side reaches (`cacheReq` adds entries by `alistSet`, a reset
   and the gate's `drainAll` empty it).  It is what lets MachCSL's root loop, draining ONE sector
   per iteration, reach pf's `drainAll` (`drainHead`, `cacheViewDrainHead`).  Deviation 1.
3. `pre₁` (`VirtioProg.preCaptureHead`) moves only `inflight` and `taken` (`pre1Eq`).
4. The hart's MMIO transactions commute with every move of `inflight` / `taken` / `cache`
   (`writeOther`, `writeNCases`, `readNIT`): the registers `write` / `read` touch are the
   configuration, `isr` and the capacity — the plan's "non-reset MMIO writes commute with
   `pre₁`, disjoint fields — verified once by the worker" [R20.1].  A RESET (STATUS := 0) is
   absorbed by `pre₁`'s in-flight pre-check.
5. **`R-dev`** = `VRel.holds` (the virtio clause: EQUAL, or `(pre₁ pf).1` on the OUT capture
   segment in its three task positions, zombie / free / held) and `devAgree` (every other device
   EQUAL), with its stability under every hart MMIO transaction (`devAgreeRead`,
   `devAgreeWrite`), the PLIC's sampling (`devAgreeLevel`) and the UART / PLIC programs
   (`devAgreeFdev`).
6. MachCSL's residual programs (`rootAG` … `idxR`, `svcR`) and their one-step SHAPES (`rfl`).
7. The pf ↔ MachCSL position relation: `FC` (the fetch), `PosRel` (every position of a burst).

## Deviations from the plan text

1. The plan's side invariant "`cache = []` outside a capture → gate window" [R19.1 (c)] is
   replaced by the weaker `cacheWf` (distinct keys, entries ≤ one sector), which holds at every
   state.  The plan uses the former to make `cacheReq` act on EQUAL states (it does here: the
   cache is equal on both sides by `R-dev`) and to let MachCSL's per-sector drains reach
   `drainAll`; `cacheWf` is exactly what the latter needs, and it survives a pre-check abort
   at the gate (where "`cache = []`" would need "a request no longer in flight was reset").
2. The task-bookkeeping (`devrt`) is not part of the relation: MachCSL's `fork` hands out
   `devrt.next` whatever it is, the forked task's thread is appended at the END of the pool
   (`poolOf`'s `vs ++ [task]`), and a finished or aborted task is never scheduled again
   (MachCSL imposes no fairness), so neither its `TaskId` nor `done` is ever read.  The thread
   map `13 + k` is the position of the task in `vs`.

All names are `Weak.MachOfPfDisk.*` (file-qualified).  Axioms: `propext`, `Classical.choice`,
`Quot.sound`.
-/
import Weak.WeakEvInst

namespace Weak

open MachCSL MachCSL.Virtio VirtioProg

namespace MachOfPfDisk

/-! ## (1) `DevStates` algebra -/

theorem dsExt {a b : DevStates} (h : ∀ d, a.st d = b.st d) : a = b := by
  cases a; cases b; congr; funext d; exact h d

theorem setSet (ds : DevStates) (d : DevId) (x y : DevSt d) :
    (ds.set d x).set d y = ds.set d y :=
  dsExt fun e => by
    by_cases h : e = d
    · subst h; simp
    · rw [DevStates.set_other _ _ _ _ h, DevStates.set_other _ _ _ _ h,
        DevStates.set_other _ _ _ _ h]

theorem setComm (ds : DevStates) (d d' : DevId) (x : DevSt d) (y : DevSt d') (h : d ≠ d') :
    (ds.set d x).set d' y = (ds.set d' y).set d x :=
  dsExt fun e => by
    by_cases h1 : e = d'
    · subst h1
      rw [DevStates.set_same, DevStates.set_other _ _ _ _ (Ne.symm h), DevStates.set_same]
    · by_cases h2 : e = d
      · subst h2
        rw [DevStates.set_other _ _ _ _ h1, DevStates.set_same, DevStates.set_same]
      · rw [DevStates.set_other _ _ _ _ h1, DevStates.set_other _ _ _ _ h2,
          DevStates.set_other _ _ _ _ h2, DevStates.set_other _ _ _ _ h1]

theorem dvirtioSet (ds : DevStates) (v : VirtioState) : dvirtio (setDvirtio ds v) = v :=
  DevStates.set_same ds .virtio v

theorem setDvirtioSt (ds : DevStates) (v : VirtioState) : (setDvirtio ds v).st .virtio = v :=
  DevStates.set_same ds .virtio v

theorem setDvirtioTwice (ds : DevStates) (a b : VirtioState) :
    setDvirtio (setDvirtio ds a) b = setDvirtio ds b :=
  setSet ds .virtio a b

theorem dvirtioSetOther (ds : DevStates) (d : DevId) (s : DevSt d) (hd : d ≠ .virtio) :
    dvirtio (ds.set d s) = dvirtio ds :=
  DevStates.set_other ds d .virtio s (Ne.symm hd)

/-! ## (2) The cache invariant and the drain -/

/-- The cache's keys are distinct and every entry is at most one sector (deviation 1). -/
def cacheWfL (l : List (Nat × List (BitVec 8))) : Prop :=
  (l.map Prod.fst).Nodup ∧ ∀ e ∈ l, e.2.length ≤ sectorSize

def cacheWf (v : VirtioState) : Prop := cacheWfL v.cache

theorem cacheWfNil : cacheWfL [] := ⟨List.nodup_nil, fun _ h => absurd h List.not_mem_nil⟩

theorem alistSetWf (l : List (Nat × List (BitVec 8))) (k : Nat) (x : List (BitVec 8))
    (hl : cacheWfL l) (hx : x.length ≤ sectorSize) : cacheWfL (alistSet l k x) := by
  obtain ⟨hn, hlen⟩ := hl
  refine ⟨?_, fun e he => ?_⟩
  · simp only [alistSet, List.map_cons]
    refine List.nodup_cons.2 ⟨?_, ?_⟩
    · intro hk
      obtain ⟨e, he, hek⟩ := List.mem_map.1 hk
      have := (List.mem_filter.1 he).2
      simp only [decide_eq_true_eq] at this
      exact this hek
    · exact (List.Sublist.map _ List.filter_sublist).nodup hn
  · simp only [alistSet, List.mem_cons] at he
    rcases he with rfl | he
    · exact hx
    · exact hlen e (List.mem_filter.1 he).1

theorem foldlAlistSetWf (r : VioReq) (bs : List (BitVec 8)) :
    ∀ (is : List Nat) (l : List (Nat × List (BitVec 8))), cacheWfL l →
      cacheWfL (is.foldl (fun cc i => alistSet cc (reqKey r i)
        ((bs.drop (sectorSize * i)).take (reqSectorLen r i))) l)
  | [], _, hl => hl
  | i :: is, l, hl => by
    simp only [List.foldl_cons]
    refine foldlAlistSetWf r bs is _ (alistSetWf _ _ _ hl ?_)
    simp only [List.length_take, reqSectorLen]
    omega

theorem cacheReqWf (v : VirtioState) (r : VioReq) (bs : List (BitVec 8)) (h : cacheWf v) :
    cacheWf (cacheReq v r bs) :=
  foldlAlistSetWf r bs _ _ h

theorem captureMoveWf (h : BitVec 16) (r : VioReq) (bs : List (BitVec 8)) (v : VirtioState)
    (hw : cacheWf v) : cacheWf (captureMove h r bs v) := by
  unfold captureMove
  show cacheWf (if reqOf v h = some r then cacheReq v r bs else v)
  split
  · exact cacheReqWf v r bs hw
  · exact hw

theorem drainAllWf (v : VirtioState) : cacheWf (drainAll v) := cacheWfNil

theorem diskWriteOff (dk : Nat → BitVec 8) (s a : Nat) (bs : List (BitVec 8))
    (hb : bs.length ≤ sectorSize) (ha : a / sectorSize ≠ s) :
    diskWrite dk (sectorSize * s) bs a = dk a := by
  unfold diskWrite
  split
  · next hle =>
    have hge : bs.length ≤ a - sectorSize * s := by
      simp only [sectorSize] at hb ha hle ⊢
      omega
    rw [List.getElem?_eq_none hge]
  · rfl

/-- MachCSL's root loop drains the HEAD entry: the entry leaves, its bytes reach the image. -/
theorem drainHead (v : VirtioState) (s : Nat) (bs : List (BitVec 8))
    (rest : List (Nat × List (BitVec 8))) (hc : v.cache = (s, bs) :: rest) (hw : cacheWf v) :
    drain v s = { v with disk := diskWrite v.disk (sectorSize * s) bs, cache := rest } := by
  have hnin : ∀ e ∈ rest, e.1 ≠ s := by
    intro e he hes
    have hn := hw.1
    rw [hc, List.map_cons, List.nodup_cons] at hn
    exact hn.1 (List.mem_map.2 ⟨e, he, hes⟩)
  unfold drain
  rw [show alistGet v.cache s = some bs by simp [alistGet, hc]]
  simp only
  congr 1
  rw [hc]
  simp only [alistDel, List.filter_cons, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true,
    if_false]
  exact List.filter_eq_self.2 (fun e he => by simpa using hnin e he)

theorem cacheViewDrainHead (v : VirtioState) (s : Nat) (bs : List (BitVec 8))
    (rest : List (Nat × List (BitVec 8))) (hc : v.cache = (s, bs) :: rest) (hw : cacheWf v) :
    cacheView { v with disk := diskWrite v.disk (sectorSize * s) bs, cache := rest } =
      cacheView v := by
  have hnin : ∀ e ∈ rest, e.1 ≠ s := by
    intro e he hes
    have hn := hw.1
    rw [hc, List.map_cons, List.nodup_cons] at hn
    exact hn.1 (List.mem_map.2 ⟨e, he, hes⟩)
  have hbs : bs.length ≤ sectorSize := hw.2 (s, bs) (by rw [hc]; exact List.mem_cons_self)
  funext a
  unfold cacheView
  simp only [hc]
  by_cases ha : a / sectorSize = s
  · have hrest : alistGet rest (a / sectorSize) = none := by
      simp only [alistGet, Option.map_eq_none_iff, List.find?_eq_none, decide_eq_true_eq]
      intro e he hea
      exact hnin e he (hea.trans ha)
    have hhead : alistGet ((s, bs) :: rest) (a / sectorSize) = some bs := by
      simp [alistGet, ha]
    rw [hrest, hhead]
    simp only
    unfold diskWrite
    have hle : sectorSize * s ≤ a := by
      simp only [sectorSize] at ha ⊢; omega
    have hmod : a - sectorSize * s = a % sectorSize := by
      simp only [sectorSize] at ha ⊢; omega
    rw [if_pos hle, hmod]
  · have hcons : alistGet ((s, bs) :: rest) (a / sectorSize) = alistGet rest (a / sectorSize) := by
      simp only [alistGet, List.find?_cons]
      have : (decide ((s, bs).1 = a / sectorSize)) = false := by
        simp only [decide_eq_false_iff_not]; exact fun h => ha h.symm
      rw [this]
    rw [hcons]
    cases hg : alistGet rest (a / sectorSize) with
    | none => exact diskWriteOff _ _ _ _ hbs ha
    | some x =>
      simp only
      split
      · rfl
      · exact diskWriteOff _ _ _ _ hbs ha

/-! ## (3) `pre₁` moves only `inflight` and `taken` -/

def p1I (h : BitVec 16) (r : VioReq) (inf : List (BitVec 16 × VPhase)) : List (BitVec 16 × VPhase) :=
  if (alistGet inf h).isSome then alistSet inf h (.fetched r) else inf

def p1T (h : BitVec 16) (inf : List (BitVec 16 × VPhase)) (tk : Option (BitVec 16)) :
    Option (BitVec 16) :=
  if (alistGet inf h).isSome = true ∧ tk = none then some h else tk

def p1B (h : BitVec 16) (inf : List (BitVec 16 × VPhase)) (tk : Option (BitVec 16)) : Bool :=
  (alistGet inf h).isSome && tk.isNone

theorem pre1Eq (h : BitVec 16) (r : VioReq) (v : VirtioState) :
    preCaptureHead h r v =
      ({ v with inflight := p1I h r v.inflight, taken := p1T h v.inflight v.taken },
       p1B h v.inflight v.taken) := by
  unfold preCaptureHead p1I p1T p1B Virtio.phase Virtio.setPhase
  by_cases hs : (alistGet v.inflight h).isSome = true
  · cases ht : v.taken <;> simp [hs]
  · simp [hs] <;> rfl

theorem p1Nil (h : BitVec 16) (r : VioReq) (tk : Option (BitVec 16)) :
    p1I h r [] = [] ∧ p1T h [] tk = tk ∧ p1B h [] tk = false := by
  simp [p1I, p1T, p1B, alistGet]

/-! ## (4) The hart's MMIO transactions commute with `inflight` / `taken` / `cache` -/

theorem writeReset (v : VirtioState) (off : Nat) (w : BitVec 32) (h : off = offStatus ∧ w = 0#32) :
    Virtio.write v off w = some (Virtio.reset v) := by
  obtain ⟨rfl, rfl⟩ := h
  simp [Virtio.write]

theorem resetIT (v : VirtioState) (a : List (BitVec 16 × VPhase)) (b : Option (BitVec 16))
    (cc : List (Nat × List (BitVec 8))) :
    Virtio.reset { v with inflight := a, taken := b, cache := cc } = Virtio.reset v := rfl

/-- Every non-reset register write moves only the configuration and `isr`. -/
theorem writeOther (v : VirtioState) (off : Nat) (w : BitVec 32) (a : List (BitVec 16 × VPhase))
    (b : Option (BitVec 16)) (cc : List (Nat × List (BitVec 8)))
    (hno : ¬ (off = offStatus ∧ w = 0#32)) :
    Virtio.write { v with inflight := a, taken := b, cache := cc } off w =
      (Virtio.write v off w).map (fun v' => { v' with inflight := a, taken := b, cache := cc }) := by
  unfold Virtio.write
  by_cases h1 : off = offStatus
  · have h2 : ¬ w = 0#32 := fun h2 => hno ⟨h1, h2⟩
    simp only [h1, if_true, h2, if_false, Option.map_some]
  · simp only [h1, if_false,
      apply_ite (Option.map (fun v' : VirtioState => { v' with inflight := a, taken := b, cache := cc })),
      Option.map_some, Option.map_none]

theorem readIT (v : VirtioState) (off : Nat) (a : List (BitVec 16 × VPhase))
    (b : Option (BitVec 16)) (cc : List (Nat × List (BitVec 8))) :
    Virtio.read { v with inflight := a, taken := b, cache := cc } off = Virtio.read v off := rfl

theorem readNIT (v : VirtioState) (off n : Nat) (a : List (BitVec 16 × VPhase))
    (b : Option (BitVec 16)) (cc : List (Nat × List (BitVec 8))) :
    readN { v with inflight := a, taken := b, cache := cc } off n =
      (readN v off n).map (fun p => (p.1, { v with inflight := a, taken := b, cache := cc })) := by
  unfold readN
  split
  · rw [readIT]
    cases Virtio.read v off <;> rfl
  · split <;> rfl

theorem readNSame (v : VirtioState) (off n : Nat) (x : BitVec (8 * n)) (v' : VirtioState)
    (h : readN v off n = some (x, v')) : v' = v := by
  unfold readN at h
  split at h
  · cases hr : Virtio.read v off with
    | none => rw [hr] at h; cases h
    | some y => rw [hr] at h; simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h; exact h.2.symm
  · split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h; exact h.2.symm
    · cases h

/-- **The MMIO write cases**: a reset (any state resets alike), or a move of the configuration /
`isr` alone that commutes with every move of `inflight`, `taken` and `cache`. -/
theorem writeNCases (v : VirtioState) (off n : Nat) (w : BitVec (8 * n)) (v' : VirtioState)
    (hw : writeN v off n w = some v') :
    (v' = Virtio.reset v ∧ ∀ u, writeN u off n w = some (Virtio.reset u)) ∨
    (v'.inflight = v.inflight ∧ v'.taken = v.taken ∧ v'.cache = v.cache ∧
      ∀ a b cc, writeN { v with inflight := a, taken := b, cache := cc } off n w =
        some { v' with inflight := a, taken := b, cache := cc }) := by
  unfold writeN at hw ⊢
  split at hw
  · next h4 =>
    by_cases hr : off = offStatus ∧ castW (by omega : 8 * n = 32) w = 0#32
    · left
      rw [writeReset _ _ _ hr] at hw
      cases hw
      refine ⟨rfl, fun u => ?_⟩
      rw [dif_pos h4, writeReset _ _ _ hr]
    · right
      have hself := writeOther v off (castW (by omega : 8 * n = 32) w) v.inflight v.taken v.cache hr
      rw [show ({ v with inflight := v.inflight, taken := v.taken, cache := v.cache } : VirtioState)
        = v from rfl, hw] at hself
      simp only [Option.map_some, Option.some.injEq] at hself
      refine ⟨by rw [hself], by rw [hself], by rw [hself], fun a b cc => ?_⟩
      rw [dif_pos h4, writeOther _ _ _ _ _ _ hr, hw]
      rfl
  · next h4 =>
    split at hw
    · next h12 =>
      simp only [Option.some.injEq] at hw
      subst hw
      exact Or.inr ⟨rfl, rfl, rfl, fun a b cc => by rw [dif_neg h4, if_pos h12]⟩
    · cases hw

theorem cacheWfWriteN (v : VirtioState) (off n : Nat) (w : BitVec (8 * n)) (v' : VirtioState)
    (hw : writeN v off n w = some v') (hc : cacheWf v) : cacheWf v' := by
  rcases writeNCases v off n w v' hw with ⟨rfl, -⟩ | ⟨-, -, hcc, -⟩
  · exact cacheWfNil
  · unfold cacheWf; rw [hcc]; exact hc

/-! ## (5) `R-dev`: the virtio clause and its stability -/

/-- The virtio clause of `R-dev` [R18.3 (b)][R19.1 (b)][R20.1]: EQUAL, or — on the OUT capture
segment of request `(h, r)` — MachCSL's state is `(pre₁ pf).1`, with the task ZOMBIE at `:526`
(`capZ`, the request no longer in flight), FREE past the capture read (`capF`) or HELD at the
latch (`capB`). -/
inductive VRel where
  | eq
  | capZ (h : BitVec 16)
  | capF (h : BitVec 16) (r : VioReq)
  | capB (h : BitVec 16) (r : VioReq)

def VRel.holds : VRel → VirtioState → VirtioState → Prop
  | .eq, vp, vm => vm = vp
  | .capZ h, vp, vm => vm = vp ∧ Virtio.phase vp h = none
  | .capF h r, vp, vm =>
      vm = (preCaptureHead h r vp).1 ∧
        ((preCaptureHead h r vp).2 = true ∨ Virtio.phase vp h = none)
  | .capB h r, vp, vm => vm = (preCaptureHead h r vp).1 ∧ (preCaptureHead h r vp).2 = false

/-- Both sides agree on everything but `inflight` and `taken`. -/
theorem holdsShape {κ : VRel} {vp vm : VirtioState} (h : κ.holds vp vm) :
    ∃ a b, vm = { vp with inflight := a, taken := b, cache := vp.cache } := by
  cases κ with
  | eq => exact ⟨vp.inflight, vp.taken, h⟩
  | capZ _ => exact ⟨vp.inflight, vp.taken, h.1⟩
  | capF h r => exact ⟨_, _, by rw [h.1, pre1Eq]⟩
  | capB h r => exact ⟨_, _, by rw [h.1, pre1Eq]⟩

theorem holdsIsr {κ : VRel} {vp vm : VirtioState} (h : κ.holds vp vm) : vm.isr = vp.isr := by
  obtain ⟨a, b, rfl⟩ := holdsShape h; rfl

theorem holdsReadN {κ : VRel} {vp vm : VirtioState} (h : κ.holds vp vm) (off n : Nat)
    (x : BitVec (8 * n)) (vp' : VirtioState) (hr : readN vp off n = some (x, vp')) :
    vp' = vp ∧ readN vm off n = some (x, vm) := by
  refine ⟨readNSame _ _ _ _ _ hr, ?_⟩
  obtain ⟨a, b, rfl⟩ := holdsShape h
  rw [readNIT, hr]
  rfl

/-- **`R-dev` survives every hart MMIO write** (incl. a RESET, absorbed by the pre-check). -/
theorem holdsWriteN {κ : VRel} {vp vm : VirtioState} (h : κ.holds vp vm) (off n : Nat)
    (w : BitVec (8 * n)) (vp' : VirtioState) (hw : writeN vp off n w = some vp') :
    ∃ vm', writeN vm off n w = some vm' ∧ κ.holds vp' vm' := by
  rcases writeNCases vp off n w vp' hw with ⟨rfl, hall⟩ | ⟨hi, ht, hc, hall⟩
  · -- the RESET: both sides reset alike, nothing in flight
    refine ⟨Virtio.reset vm, hall vm, ?_⟩
    obtain ⟨a, b, rfl⟩ := holdsShape h
    rw [resetIT]
    cases κ with
    | eq => rfl
    | capZ h0 => exact ⟨rfl, rfl⟩
    | capF h0 r0 =>
      obtain ⟨hI, hT, -⟩ := p1Nil h0 r0 none
      refine ⟨?_, Or.inr rfl⟩
      rw [pre1Eq]
      show Virtio.reset vp = { Virtio.reset vp with inflight := p1I h0 r0 [], taken := p1T h0 [] none }
      rw [hI, hT]
      rfl
    | capB h0 r0 =>
      obtain ⟨hI, hT, hB⟩ := p1Nil h0 r0 none
      refine ⟨?_, ?_⟩
      · rw [pre1Eq]
        show Virtio.reset vp = { Virtio.reset vp with inflight := p1I h0 r0 [], taken := p1T h0 [] none }
        rw [hI, hT]
        rfl
      · rw [pre1Eq]; exact hB
  · cases κ with
    | eq =>
      subst h
      exact ⟨vp', hw, rfl⟩
    | capZ h0 =>
      obtain ⟨rfl, hn⟩ := h
      refine ⟨vp', hw, rfl, ?_⟩
      unfold Virtio.phase at hn ⊢
      rw [hi]; exact hn
    | capF h0 r0 =>
      obtain ⟨rfl, hc0⟩ := h
      refine ⟨_, by rw [pre1Eq]; exact hall _ _ _, ?_, ?_⟩
      · rw [pre1Eq, hi, ht, hc]
      · rw [pre1Eq] at hc0 ⊢
        unfold Virtio.phase at hc0 ⊢
        rw [hi, ht]; exact hc0
    | capB h0 r0 =>
      obtain ⟨rfl, hc0⟩ := h
      refine ⟨_, by rw [pre1Eq]; exact hall _ _ _, ?_, ?_⟩
      · rw [pre1Eq, hi, ht, hc]
      · rw [pre1Eq] at hc0 ⊢
        rw [hi, ht]; exact hc0

/-- **`R-dev`** at the fabric level: every device but the disk EQUAL, the disk by `κ`, the pf
cache well-formed. -/
def devAgree (κ : VRel) (dsP dsM : DevStates) : Prop :=
  ∃ vm, dsM = setDvirtio dsP vm ∧ κ.holds (dvirtio dsP) vm ∧ cacheWf (dvirtio dsP)

theorem devAgreeEq (dsP : DevStates) (hc : cacheWf (dvirtio dsP)) : devAgree .eq dsP dsP :=
  ⟨dvirtio dsP, (setDvirtioSelf dsP).symm, rfl, hc⟩

theorem devAgreeOther {κ : VRel} {dsP dsM : DevStates} (h : devAgree κ dsP dsM) {d : DevId}
    (hd : d ≠ .virtio) : dsM.st d = dsP.st d := by
  obtain ⟨vm, rfl, -, -⟩ := h
  exact DevStates.set_other _ _ _ _ hd

theorem devAgreeSetOther {κ : VRel} {dsP dsM : DevStates} (h : devAgree κ dsP dsM) {d : DevId}
    (hd : d ≠ .virtio) (s : DevSt d) : devAgree κ (dsP.set d s) (dsM.set d s) := by
  obtain ⟨vm, rfl, hk, hc⟩ := h
  refine ⟨vm, ?_, by rw [dvirtioSetOther _ _ _ hd]; exact hk,
    by rw [dvirtioSetOther _ _ _ hd]; exact hc⟩
  exact setComm _ _ _ _ _ (Ne.symm hd)

theorem devAgreeLevel {κ : VRel} {dsP dsM : DevStates} (h : devAgree κ dsP dsM) (src : IrqSrc) :
    devLevel dsM src = devLevel dsP src := by
  unfold devLevel
  cases irqSrcOf src with
  | none => rfl
  | some d =>
    simp only
    by_cases hd : d = .virtio
    · subst hd
      obtain ⟨vm, rfl, hk, -⟩ := h
      show Virtio.irq (dvirtio (setDvirtio dsP vm)) = Virtio.irq (dvirtio dsP)
      rw [dvirtioSet]
      unfold Virtio.irq
      rw [holdsIsr hk]
    · rw [devAgreeOther h hd]

/-- `R-dev` survives a hart's MMIO READ (the value is the same on both sides). -/
theorem devAgreeRead {κ : VRel} {dsP dsM : DevStates} (h : devAgree κ dsP dsM) (pa : PAddr)
    (n : Nat) (x : BitVec (8 * n)) (dsP' : DevStates) (hr : devRead dsP pa n = some (x, dsP')) :
    ∃ dsM', devRead dsM pa n = some (x, dsM') ∧ devAgree κ dsP' dsM' := by
  unfold devRead at hr ⊢
  cases hdec : devDecode pa with
  | none => rw [hdec] at hr; cases hr
  | some p =>
    obtain ⟨d, off⟩ := p
    rw [hdec] at hr
    simp only at hr ⊢
    by_cases hd : d = .virtio
    · subst hd
      cases hrv : Virtio.readN (dvirtio dsP) off n with
      | none =>
        have : (devSig .virtio).read (dsP.st .virtio) off n = none := hrv
        rw [this] at hr; cases hr
      | some p =>
        obtain ⟨x', vp'⟩ := p
        have : (devSig .virtio).read (dsP.st .virtio) off n = some (x', vp') := hrv
        rw [this] at hr
        change some (x', dsP.set .virtio vp') = some (x, dsP') at hr
        simp only [Option.some.injEq, Prod.mk.injEq] at hr
        obtain ⟨rfl, rfl⟩ := hr
        obtain ⟨vm, rfl, hk, hc⟩ := h
        obtain ⟨hvp, hrm⟩ := holdsReadN hk off n x' vp' hrv
        subst hvp
        refine ⟨(setDvirtio dsP vm).set .virtio vm, ?_, ?_⟩
        · have : (devSig .virtio).read ((setDvirtio dsP vm).st .virtio) off n = some (x', vm) := by
            show Virtio.readN (dvirtio (setDvirtio dsP vm)) off n = _
            rw [dvirtioSet]; exact hrm
          rw [this]; rfl
        · refine ⟨vm, ?_, ?_, ?_⟩
          · show setDvirtio (setDvirtio dsP vm) vm = setDvirtio (setDvirtio dsP (dvirtio dsP)) vm
            rw [setDvirtioSelf, setDvirtioTwice]
          · show VRel.holds κ (dvirtio (setDvirtio dsP (dvirtio dsP))) vm
            rw [setDvirtioSelf]; exact hk
          · show cacheWf (dvirtio (setDvirtio dsP (dvirtio dsP)))
            rw [setDvirtioSelf]; exact hc
    · rw [devAgreeOther h hd]
      cases hrd : (devSig d).read (dsP.st d) off n with
      | none => rw [hrd] at hr; cases hr
      | some p =>
        obtain ⟨x', s'⟩ := p
        rw [hrd] at hr
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hr
        obtain ⟨rfl, rfl⟩ := hr
        exact ⟨dsM.set d s', rfl, devAgreeSetOther h hd s'⟩

/-- `R-dev` survives a hart's MMIO WRITE (a reset included). -/
theorem devAgreeWrite {κ : VRel} {dsP dsM : DevStates} (h : devAgree κ dsP dsM) (pa : PAddr)
    (n : Nat) (w : BitVec (8 * n)) (dsP' : DevStates) (hw : devWrite dsP pa n w = some dsP') :
    ∃ dsM', devWrite dsM pa n w = some dsM' ∧ devAgree κ dsP' dsM' := by
  unfold devWrite at hw ⊢
  cases hdec : devDecode pa with
  | none => rw [hdec] at hw; cases hw
  | some p =>
    obtain ⟨d, off⟩ := p
    rw [hdec] at hw
    simp only at hw ⊢
    by_cases hd : d = .virtio
    · subst hd
      cases hwv : Virtio.writeN (dvirtio dsP) off n w with
      | none =>
        have : (devSig .virtio).write (dsP.st .virtio) off n w = none := hwv
        rw [this] at hw; cases hw
      | some vp' =>
        have : (devSig .virtio).write (dsP.st .virtio) off n w = some vp' := hwv
        rw [this] at hw
        change some (dsP.set .virtio vp') = some dsP' at hw
        simp only [Option.some.injEq] at hw
        subst hw
        obtain ⟨vm, rfl, hk, hc⟩ := h
        obtain ⟨vm', hwm, hk'⟩ := holdsWriteN hk off n w vp' hwv
        refine ⟨(setDvirtio dsP vm).set .virtio vm', ?_, vm', ?_, ?_, ?_⟩
        · have : (devSig .virtio).write ((setDvirtio dsP vm).st .virtio) off n w = some vm' := by
            show Virtio.writeN (dvirtio (setDvirtio dsP vm)) off n w = _
            rw [dvirtioSet]; exact hwm
          rw [this]; rfl
        · show setDvirtio (setDvirtio dsP vm) vm' = setDvirtio (setDvirtio dsP vp') vm'
          rw [setDvirtioTwice, setDvirtioTwice]
        · show VRel.holds κ (dvirtio (setDvirtio dsP vp')) vm'
          rw [dvirtioSet]; exact hk'
        · show cacheWf (dvirtio (setDvirtio dsP vp'))
          rw [dvirtioSet]; exact cacheWfWriteN _ _ _ _ _ hwv hc
    · rw [devAgreeOther h hd]
      cases hwd : (devSig d).write (dsP.st d) off n w with
      | none => rw [hwd] at hw; cases hw
      | some s' =>
        rw [hwd] at hw
        simp only [Option.map_some, Option.some.injEq] at hw
        subst hw
        exact ⟨dsM.set d s', rfl, devAgreeSetOther h hd s'⟩

/-- `R-dev` survives a UART / PLIC program step (`fdevStep`, off the disk). -/
theorem devAgreeFdev {κ : VRel} {dsP dsM : DevStates} (h : devAgree κ dsP dsM) (dv : DevId)
    (hd : dv ≠ .virtio) (m m' : DevProg dv) (dsP' : DevStates) (hf : fdevStep dv m dsP m' dsP') :
    ∃ dsM', fdevStep dv m dsM m' dsM' ∧ devAgree κ dsP' dsM' := by
  have hst := devAgreeOther h hd
  cases m with
  | pure a =>
    obtain ⟨rfl, rfl⟩ := hf
    exact ⟨dsM, ⟨rfl, rfl⟩, h⟩
  | op o k =>
    cases o with
    | step f =>
      rcases hf with ⟨s', os, hfs, hok, rfl, rfl⟩ | ⟨hbl, rfl, rfl⟩
      · refine ⟨dsM.set dv s', Or.inl ⟨s', os, by rw [hst]; exact hfs, by rw [hst]; exact hok, rfl, rfl⟩,
          devAgreeSetOther h hd s'⟩
      · exact ⟨dsM, Or.inr ⟨by rw [hst]; exact hbl, rfl, rfl⟩, h⟩
    | get =>
      obtain ⟨rfl, rfl⟩ := hf
      exact ⟨dsM, ⟨by rw [hst], rfl⟩, h⟩
    | choose =>
      obtain ⟨n, rfl, rfl⟩ := hf
      exact ⟨dsM, ⟨n, rfl, rfl⟩, h⟩
    | sample src =>
      obtain ⟨rfl, rfl⟩ := hf
      exact ⟨dsM, ⟨by rw [devAgreeLevel h], rfl⟩, h⟩
    | dmaRead _ _ => exact hf.elim
    | dmaWrite _ _ _ _ => exact hf.elim
    | setPin _ _ _ => exact hf.elim
    | fork _ => exact hf.elim
    | join _ => exact hf.elim

/-! ## (6) MachCSL's residual programs and their one-step shapes

Each is the residual of `Virtio.body` / `Virtio.serve` at a point the simulation stops at, and
each shape lemma is `rfl` up to the binds the do-notation elaborates (checked by the kernel). -/

/-- The root loop after the ring read: `get :567`, the guard-pop `:576`, `fork :579`. -/
def rootRing (h : BitVec 16) : VM Unit := do
  let popped ← DevM.get
  if (phase popped h).isSome then pure ()
  else
    DevM.guard (fun v =>
      if (phase v h).isSome then none
      else some { setPhase v h .popped with seen := v.seen + 1#16 })
    let _ ← DevM.fork (.serve h)
    pure ()

/-- The root loop after the avail-index read. -/
def rootAI (v : VirtioState) (ai : BitVec 16) : VM Unit :=
  if v.seen ≠ ai then do
    let h ← dma16 (availRingAddr v.cfg v.seen)
    rootRing h
  else pure ()

/-- The root loop after `get :561` (snapshot `v`). -/
def rootAG (v : VirtioState) : VM Unit :=
  if live v.cfg then do
    let ai ← dma16 (availIdxAddr v.cfg)
    rootAI v ai
  else pure ()

/-- The root loop's drain branch after its `get :582`. -/
def drainG (v : VirtioState) : VM Unit :=
  if v.cache.isEmpty then pure ()
  else do
    let j ← DevM.chooseLt v.cache.length
    DevM.modify (fun v => drain v (v.cache.getD j (0, [])).1)

/-- The used-index write and the completion (`serve :552-554`). -/
def idxR (h : BitVec 16) (r : VioReq) (ui : BitVec 16) (c : VirtioCfg) : VM Unit :=
  DevM.dmaWriteStep (fun s =>
      if decide (reqOf s h = some r) && decide (s.usedIdx = ui) && decide (s.cfg = c) then
        some (complete s h) else none) (usedIdxAddr c) 2 (ui + 1#16)

/-- The used element (`:546-548`), then the index. -/
def usedR (h : BitVec 16) (r : VioReq) (ui : BitVec 16) (c : VirtioCfg) : VM Unit := do
  DevM.dmaWriteIf (fun s => decide (reqOf s h = some r) && decide (s.usedIdx = ui) &&
        decide (s.cfg = c)) (usedElemAddr c ui) 8
      (castW (by decide : 64 = 8 * 8) ((usedLen r) ++ (r.head.setWidth 32)))
  idxR h r ui c

/-- The completion gate `:539-541`, `get :542`, the used ring. -/
def gateR (h : BitVec 16) (r : VioReq) : VM Unit := do
  DevM.guard (fun v =>
      if (phase v h).isSome && completeOk v r h && pushOk v then some (setPhase v h (.pushed r))
      else none)
  let v ← DevM.get
  usedR h r v.usedIdx v.cfg

/-- `setPhase .status :537`, then the gate. -/
def statusR (h : BitVec 16) (r : VioReq) : VM Unit := do
  DevM.modify (fun v => setPhase v h (.status r))
  gateR h r

/-- The status byte `:536`, then the report. -/
def restR (h : BitVec 16) (r : VioReq) : VM Unit := do
  DevM.dmaWriteIf (fun v => decide (reqOf v h = some r)) r.status 1 (statusOf r)
  statusR h r

/-- `setPhase .served :534`, then the status byte. -/
def servedR (h : BitVec 16) (r : VioReq) : VM Unit := do
  DevM.modify (fun v => setPhase v h (.served r))
  restR h r

/-- The capture's move `:517-518` with the payload `w`, then the status byte. -/
def capR (h : BitVec 16) (r : VioReq) (w : BitVec (8 * r.len.toNat)) : VM Unit := do
  DevM.modify (fun v =>
    setPhase (if reqOf v h = some r then cacheReq v r (bytesOf w) else v) h (.served r))
  restR h r

/-- The capture latch `:529`, the capture, then the status byte. -/
def latchR (h : BitVec 16) (r : VioReq) : VM Unit := do
  DevM.guard (fun v => if v.taken = none then some { v with taken := some h } else none)
  capture h r
  restR h r

/-- `serve`'s `some r` arm: `setPhase .fetched :526`, the data phase, the report. -/
def svcR (h : BitVec 16) (r : VioReq) : VM Unit := do
    DevM.modify (fun v => setPhase v h (.fetched r))
    if r.type.toNat = blkTOut then
      DevM.guard (fun v => if v.taken = none then some { v with taken := some h } else none)
      capture h r
    else do
      if r.type.toNat = blkTIn then fill h r else pure ()
      DevM.modify (fun v => setPhase v h (.served r))
    DevM.dmaWriteIf (fun v => decide (reqOf v h = some r)) r.status 1 (statusOf r)
    DevM.modify (fun v => setPhase v h (.status r))
    DevM.guard (fun v =>
      if (phase v h).isSome && completeOk v r h && pushOk v then some (setPhase v h (.pushed r))
      else none)
    let v ← DevM.get
    let ui := v.usedIdx
    let c := v.cfg
    DevM.dmaWriteIf (fun s => decide (reqOf s h = some r) && decide (s.usedIdx = ui) &&
        decide (s.cfg = c)) (usedElemAddr c ui) 8
      (castW (by decide : 64 = 8 * 8) ((usedLen r) ++ (r.head.setWidth 32)))
    DevM.dmaWriteStep (fun s =>
      if decide (reqOf s h = some r) && decide (s.usedIdx = ui) && decide (s.cfg = c) then
        some (complete s h) else none) (usedIdxAddr c) 2 (ui + 1#16)

/-- `serve`'s match on the fetch's answer. -/
def serveMatch (h : BitVec 16) : Option VioReq → VM Unit
  | none => stall
  | some r => svcR h r

/-- The guard functions, named. -/
def latchG (h : BitVec 16) (v : VirtioState) : Option VirtioState :=
  if v.taken = none then some { v with taken := some h } else none

def gateG (h : BitVec 16) (r : VioReq) (v : VirtioState) : Option VirtioState :=
  if (phase v h).isSome && completeOk v r h && pushOk v then some (setPhase v h (.pushed r)) else none

def popG (h : BitVec 16) (v : VirtioState) : Option VirtioState :=
  if (phase v h).isSome then none else some (popState v h)

def usedG (h : BitVec 16) (r : VioReq) (ui : BitVec 16) (c : VirtioCfg) (s : VirtioState) :
    Option VirtioState :=
  if decide (reqOf s h = some r) && decide (s.usedIdx = ui) && decide (s.cfg = c) then some s
  else none

theorem bodyShape : ∃ kb, Virtio.body = .op .choose kb ∧ kb 0 = .op .get rootAG ∧
    kb 1 = .op .get drainG :=
  ⟨_, rfl, rfl, rfl⟩

theorem rootAGLive (v : VirtioState) (hl : live v.cfg = true) :
    ∃ k, rootAG v = .op (.dmaRead (availIdxAddr v.cfg) 2) k ∧
      ∀ w, k w = rootAI v (w.extractLsb' 0 16) := by
  unfold rootAG
  rw [if_pos hl]
  exact ⟨_, rfl, fun w => rfl⟩

theorem rootAGDead (v : VirtioState) (hl : ¬ live v.cfg = true) : rootAG v = .pure () := by
  unfold rootAG
  rw [if_neg hl]
  rfl

theorem rootAINe (v : VirtioState) (ai : BitVec 16) (h : v.seen ≠ ai) :
    ∃ k, rootAI v ai = .op (.dmaRead (availRingAddr v.cfg v.seen) 2) k ∧
      ∀ w, k w = rootRing (w.extractLsb' 0 16) := by
  unfold rootAI
  rw [if_pos h]
  exact ⟨_, rfl, fun w => rfl⟩

theorem rootAIEq (v : VirtioState) (ai : BitVec 16) (h : v.seen = ai) : rootAI v ai = .pure () := by
  unfold rootAI
  rw [if_neg (fun hn => hn h)]
  rfl

theorem rootRingShape (h : BitVec 16) :
    ∃ k, rootRing h = .op .get k ∧ (∀ v, (phase v h).isSome = true → k v = .pure ()) ∧
      ∀ v, (phase v h).isSome = false →
        ∃ f k2, k v = .op (.step f) k2 ∧ (∀ s, f s = (popG h s).map fun s' => (s', [])) ∧
          ∃ k3, k2 () = .op (.fork (.serve h)) k3 ∧ ∀ tid, k3 tid = .pure () := by
  refine ⟨_, rfl, fun v hv => ?_, fun v hv => ?_⟩
  · show (if (phase v h).isSome = true then _ else _) = _
    rw [if_pos hv]
    rfl
  · show ∃ f k2, (if (phase v h).isSome = true then _ else _) = _ ∧ _
    rw [if_neg (by simp [hv])]
    exact ⟨_, _, rfl, fun s => rfl, _, rfl, fun tid => rfl⟩

theorem drainGShape (v : VirtioState) (hne : v.cache ≠ []) :
    ∃ k, drainG v = .op .choose k ∧ ∃ f k2, k 0 = .op (.step f) k2 ∧
      (∀ s, f s = some (drain s (s.cache.getD (0 % v.cache.length) (0, [])).1, [])) ∧
      k2 () = .pure () := by
  unfold drainG
  rw [if_neg (by cases hc : v.cache with
    | nil => exact absurd hc hne
    | cons _ _ => simp)]
  exact ⟨_, rfl, _, _, rfl, fun s => rfl, rfl⟩

theorem serveShape (h : BitVec 16) :
    ∃ k, serve h = .op .get k ∧ ∀ v, k v = DevM.bind (fetch v.cfg h) (serveMatch h) :=
  ⟨_, rfl, fun v => by
    show DevM.bind (fetch v.cfg h) _ = _
    congr 1⟩

theorem svcShape (h : BitVec 16) (r : VioReq) :
    ∃ f k, svcR h r = .op (.step f) k ∧ (∀ s, f s = some (setPhase s h (.fetched r), [])) ∧
      (r.type.toNat = blkTOut → k () = latchR h r) ∧
      (¬ r.type.toNat = blkTOut → r.type.toNat = blkTIn →
        k () = DevM.bind (fill h r) (fun _ => servedR h r)) ∧
      (¬ r.type.toNat = blkTOut → ¬ r.type.toNat = blkTIn → k () = servedR h r) := by
  refine ⟨_, _, rfl, fun s => rfl, fun hout => ?_, fun hout hin => ?_, fun hout hin => ?_⟩
  · show (if r.type.toNat = blkTOut then _ else _) = _
    rw [if_pos hout]
    rfl
  · show (if r.type.toNat = blkTOut then _ else _) = _
    rw [if_neg hout]
    show (if r.type.toNat = blkTIn then _ else _) = _
    rw [if_pos hin]
    rfl
  · show (if r.type.toNat = blkTOut then _ else _) = _
    rw [if_neg hout]
    show (if r.type.toNat = blkTIn then _ else _) = _
    rw [if_neg hin]
    rfl

theorem latchShape (h : BitVec 16) (r : VioReq) :
    ∃ f k, latchR h r = .op (.step f) k ∧ (∀ s, f s = (latchG h s).map fun s' => (s', [])) ∧
      ∃ k2, k () = .op (.dmaRead r.buf r.len.toNat) k2 ∧ ∀ w, k2 w = capR h r w :=
  ⟨_, _, rfl, fun s => rfl, _, rfl, fun w => rfl⟩

theorem capShape (h : BitVec 16) (r : VioReq) (w : BitVec (8 * r.len.toNat)) :
    ∃ f k, capR h r w = .op (.step f) k ∧
      (∀ s, f s = some (setPhase (if reqOf s h = some r then cacheReq s r (bytesOf w) else s) h
        (.served r), [])) ∧ k () = restR h r :=
  ⟨_, _, rfl, fun s => rfl, rfl⟩

theorem fillShape (h : BitVec 16) (r : VioReq) :
    ∃ k, DevM.bind (fill h r) (fun _ => servedR h r) = .op .get k ∧
      ∀ v, ∃ G k2, k v = .op (.dmaWrite G r.buf r.len.toNat
          (bvOfBytes r.len.toNat (diskRead (cacheView v) (reqOff r) r.len.toNat))) k2 ∧
        (∀ s, G s = reqGuard h r s) ∧ k2 () = servedR h r :=
  ⟨_, rfl, fun v => ⟨_, _, rfl, fun s => rfl, rfl⟩⟩

theorem servedShape (h : BitVec 16) (r : VioReq) :
    ∃ f k, servedR h r = .op (.step f) k ∧ (∀ s, f s = some (setPhase s h (.served r), [])) ∧
      k () = restR h r :=
  ⟨_, _, rfl, fun s => rfl, rfl⟩

theorem restShape (h : BitVec 16) (r : VioReq) :
    ∃ G k, restR h r = .op (.dmaWrite G r.status 1 (statusOf r)) k ∧
      (∀ s, G s = reqGuard h r s) ∧ k () = statusR h r :=
  ⟨_, _, rfl, fun s => rfl, rfl⟩

theorem statusShape (h : BitVec 16) (r : VioReq) :
    ∃ f k, statusR h r = .op (.step f) k ∧ (∀ s, f s = some (setPhase s h (.status r), [])) ∧
      k () = gateR h r :=
  ⟨_, _, rfl, fun s => rfl, rfl⟩

theorem gateShape (h : BitVec 16) (r : VioReq) :
    ∃ f k, gateR h r = .op (.step f) k ∧ (∀ s, f s = (gateG h r s).map fun s' => (s', [])) ∧
      ∃ k2, k () = .op .get k2 ∧ ∀ v, k2 v = usedR h r v.usedIdx v.cfg :=
  ⟨_, _, rfl, fun s => rfl, _, rfl, fun v => rfl⟩

theorem usedShape (h : BitVec 16) (r : VioReq) (ui : BitVec 16) (c : VirtioCfg) :
    ∃ G k, usedR h r ui c = .op (.dmaWrite G (usedElemAddr c ui) 8 (usedElemWord r)) k ∧
      (∀ s, G s = usedG h r ui c s) ∧ k () = idxR h r ui c :=
  ⟨_, _, rfl, fun s => rfl, rfl⟩

theorem idxShape (h : BitVec 16) (r : VioReq) (ui : BitVec 16) (c : VirtioCfg) :
    ∃ G k, idxR h r ui c = .op (.dmaWrite G (usedIdxAddr c) 2 (ui + 1#16)) k ∧
      (∀ s, G s = idxGuard h r ui c s) ∧ k () = .pure () :=
  ⟨_, _, rfl, fun s => rfl, rfl⟩

theorem serveDone (h : BitVec 16) (r : VioReq) :
    DevM.bind (DevM.pure (some r)) (serveMatch h) = svcR h r := rfl

/-! ## (7) The pf side: the program's nodes, and the position relation -/

/-- The pf burst after the avail-index read (`virtioProg`'s inner continuation). -/
def kAi (v0 : VirtioState) (ai : BitVec 16) : DM Dres :=
  if v0.seen ≠ ai then dreadAvailRing v0.cfg v0.seen (fun h => DPop h (fun s => fetchProg s.cfg h))
  else DRet DIdle

theorem vpLive (v0 : VirtioState) (hl : live v0.cfg = true) :
    virtioProg v0 = DRead (availIdxAddr v0.cfg) 2 true
      (fun bs => kAi v0 ((bvOfBytes 2 bs).extractLsb' 0 16)) := by
  unfold virtioProg
  rw [if_pos hl]
  rfl

theorem vpDead (v0 : VirtioState) (hl : ¬ live v0.cfg = true) : virtioProg v0 = DRet DIdle := by
  unfold virtioProg
  rw [if_neg hl]

theorem kAiNe (v0 : VirtioState) (ai : BitVec 16) (h : v0.seen ≠ ai) :
    kAi v0 ai = DRead (availRingAddr v0.cfg v0.seen) 2 false
      (fun bs => DPop ((bvOfBytes 2 bs).extractLsb' 0 16)
        (fun s => fetchProg s.cfg ((bvOfBytes 2 bs).extractLsb' 0 16))) := by
  unfold kAi
  rw [if_pos h]
  rfl

theorem kAiEq (v0 : VirtioState) (ai : BitVec 16) (h : v0.seen = ai) : kAi v0 ai = DRet DIdle := by
  unfold kAi
  rw [if_neg (fun hn => hn h)]

/-- [OWN.40] An OUT capture buffer wrapping past `2^64` stalls the request. -/
theorem dcompleteWrap (h : BitVec 16) (r : VioReq) (hout : r.type.toNat = blkTOut)
    (hw : outWraps r = true) : dcomplete h r = DRet DStall := by
  unfold dcomplete
  rw [if_pos hout, if_pos hw]

/-- A zero-length buffer never wraps. -/
theorem outWraps0 (r : VioReq) (hn : r.len.toNat = 0) : outWraps r = false := by
  have := r.buf.isLt
  simp only [outWraps, hn, decide_eq_false_iff_not]
  omega

theorem dcompleteOut (h : BitVec 16) (r : VioReq) (hout : r.type.toNat = blkTOut)
    (hw : outWraps r = false) (hn : r.len.toNat ≠ 0) :
    dcomplete h r = DRead r.buf r.len.toNat false (fun bs => dtail h r (preCapture h r bs)) := by
  unfold dcomplete
  rw [if_pos hout, if_neg (by simp [hw])]
  unfold dreadData
  split
  · next h0 => exact absurd h0 hn
  · next n' hn' => rw [hn']

theorem dcompleteOut0 (h : BitVec 16) (r : VioReq) (hout : r.type.toNat = blkTOut)
    (hn : r.len.toNat = 0) : dcomplete h r = dtail h r (preCapture h r []) := by
  unfold dcomplete
  rw [if_pos hout, if_neg (by simp [outWraps0 r hn])]
  unfold dreadData
  split
  · rfl
  · next n' hn' => rw [hn] at hn'; cases hn'

theorem dcompleteIn (h : BitVec 16) (r : VioReq) (hout : ¬ r.type.toNat = blkTOut)
    (hin : r.type.toNat = blkTIn) (hn : r.len.toNat ≠ 0) : dcomplete h r = fillNode h r := by
  unfold dcomplete
  rw [if_neg hout, if_pos ⟨hin, hn⟩]

theorem dcompleteElse (h : BitVec 16) (r : VioReq) (hout : ¬ r.type.toNat = blkTOut)
    (hin : ¬ (r.type.toNat = blkTIn ∧ r.len.toNat ≠ 0)) :
    dcomplete h r = dtail h r (preNoData h r) := by
  unfold dcomplete
  rw [if_neg hout, if_neg hin]

/-- **The fetch correspondence**: the pf fetch program and MachCSL's `fetch` take the same reads
(one 16-byte descriptor read each, the header) and end alike — a stall on a malformed chain,
the decoded request otherwise. -/
inductive FC (h : BitVec 16) : DM Dres → VM (Option VioReq) → Prop where
  | stall : FC h (DRet DStall) (.pure none)
  | done (r : VioReq) : FC h (dcomplete h r) (.pure (some r))
  | read (pa : PAddr) (n : Nat) (kP : List (BitVec 8) → DM Dres)
      (kM : BitVec (8 * n) → VM (Option VioReq)) : n ≤ 16 →
      (∀ bs : List (BitVec 8), bs.length = n → FC h (kP bs) (kM (bvOfBytes n bs))) →
      FC h (DRead pa n false kP) (.op (.dmaRead pa n) kM)

theorem fcFetch (c : VirtioCfg) (h : BitVec 16) : FC h (fetchProg c h) (fetch c h) := by
  unfold fetchProg fetch
  dsimp only
  by_cases h1 : (!decide (h.toNat < c.qnum.toNat)) = true
  · rw [if_pos h1, if_pos h1]
    exact .stall
  rw [if_neg h1, if_neg h1]
  refine .read _ _ _ _ (by decide) (fun bs0 _ => ?_)
  show FC h (if _ then _ else _) (if _ then _ else _)
  generalize descOf (bvOfBytes 16 bs0) = d0
  by_cases h2 : (!d0.has descFNext || !decide (d0.next.toNat < c.qnum.toNat)) = true
  · rw [if_pos h2, if_pos h2]
    exact .stall
  rw [if_neg h2, if_neg h2]
  refine .read _ _ _ _ (by decide) (fun bs1 _ => ?_)
  show FC h (if _ then _ else _) (if _ then _ else _)
  generalize descOf (bvOfBytes 16 bs1) = d1
  by_cases h3 : (!d1.has descFNext || !decide (d1.next.toNat < c.qnum.toNat)) = true
  · rw [if_pos h3, if_pos h3]
    exact .stall
  rw [if_neg h3, if_neg h3]
  refine .read _ _ _ _ (by decide) (fun bs2 _ => ?_)
  show FC h (if _ then _ else _) (if _ then _ else _)
  generalize descOf (bvOfBytes 16 bs2) = d2
  by_cases h4 : d2.has descFNext = true
  · rw [if_pos h4, if_pos h4]
    exact .stall
  rw [if_neg h4, if_neg h4]
  refine .read _ _ _ _ (by decide) (fun bs3 _ => ?_)
  refine .read _ _ _ _ (by decide) (fun bs4 _ => ?_)
  exact .done _

/-- **The position relation**: where the pf disk program `dp` is, where MachCSL's virtio ROOT
thread (`mr`) and the LIVE serving task (`ot`, if one is needed) are, and which virtio clause
`κ` of `R-dev` holds.  One constructor per stopping point of a burst (plan §C W4 F9's
bookkeeping; the MachCSL counts are the rows of `MachOfPf.simDisk`). -/
inductive PosRel : Option (DM Dres) → VM Unit → Option (VM Unit) → VRel → Prop where
  /-- no burst; the root at its loop boundary -/
  | idle : PosRel none (.pure ()) none .eq
  /-- after START (`get :561`, snapshot `v0`) -/
  | start (v0 : VirtioState) : PosRel (some (virtioProg v0)) (rootAG v0) none .eq
  /-- after the avail-index read -/
  | ai (v0 : VirtioState) (ai : BitVec 16) : PosRel (some (kAi v0 ai)) (rootAI v0 ai) none .eq
  /-- after the ring read: at THE POP -/
  | ring (h : BitVec 16) :
      PosRel (some (DPop h (fun s => fetchProg s.cfg h))) (rootRing h) none .eq
  /-- the task in its fetch (incl. its stall and the decoded request at `:526`) -/
  | fetch (h : BitVec 16) (P : DM Dres) (M : VM (Option VioReq)) : FC h P M →
      PosRel (some P) (.pure ()) (some (DevM.bind M (serveMatch h))) .eq
  /-- the OUT capture segment, the request no longer in flight (the task a zombie at `:526`) -/
  | capZ (h : BitVec 16) (r : VioReq) (bs : List (BitVec 8)) : r.type.toNat = blkTOut →
      bs.length = r.len.toNat →
      PosRel (some (dtail h r (preCapture h r bs))) (.pure ()) (some (svcR h r)) (.capZ h)
  /-- the OUT capture segment, the latch FREE: the task past its capture read, at `:517` -/
  | capF (h : BitVec 16) (r : VioReq) (bs : List (BitVec 8)) : r.type.toNat = blkTOut →
      bs.length = r.len.toNat →
      PosRel (some (dtail h r (preCapture h r bs))) (.pure ())
        (some (capR h r (bvOfBytes r.len.toNat bs))) (.capF h r)
  /-- the OUT capture segment, the latch HELD: the task at its `taken` guard `:529` -/
  | capB (h : BitVec 16) (r : VioReq) (bs : List (BitVec 8)) : r.type.toNat = blkTOut →
      bs.length = r.len.toNat →
      PosRel (some (dtail h r (preCapture h r bs))) (.pure ()) (some (latchR h r)) (.capB h r)
  /-- after an IN fill: at the status byte, the task at `:534` -/
  | served (h : BitVec 16) (r : VioReq) :
      PosRel (some (dtail h r (preServed h r))) (.pure ()) (some (servedR h r)) .eq
  /-- after the status byte: at the used element, the task at `:537` -/
  | status (h : BitVec 16) (r : VioReq) :
      PosRel (some (dusedTail h r)) (.pure ()) (some (statusR h r)) .eq
  /-- after the used element: the pf-only `DFence`, the task at the index write -/
  | fence (h : BitVec 16) (r : VioReq) (ui : BitVec 16) (c : VirtioCfg) :
      PosRel (some (DFence (idxNode h r ui c))) (.pure ()) (some (idxR h r ui c)) .eq
  /-- at the used-index write -/
  | idx (h : BitVec 16) (r : VioReq) (ui : BitVec 16) (c : VirtioCfg) :
      PosRel (some (idxNode h r ui c)) (.pure ()) (some (idxR h r ui c)) .eq
  /-- the burst's end -/
  | fin : PosRel (some (DRet DIdle)) (.pure ()) none .eq
  /-- a request stalled by the pf program only (an OUT capture buffer wrapping past `2^64`,
  [OWN.40]): MachCSL's task is never scheduled again -/
  | stall : PosRel (some (DRet DStall)) (.pure ()) none .eq

/-! ### `pdiskProg` by the residual node -/

theorem pdpNone {d : DevStates} {l : Wlabel} {dp' : Option (DM Dres)} {d' : DevStates}
    (h : pdiskProg none d l dp' d') :
    l = .LDev .dev 0 [] [] [] ∧ dp' = some (virtioProg (dvirtio d)) ∧ d' = d := by
  rcases h with ⟨-, h1, h2, h3⟩ | ⟨_, _, _, _, _, h, _⟩ | ⟨_, h, _⟩ |
    ⟨_, _, _, _, _, _, _, h, _⟩ | ⟨_, _, _, _, _, _, h, _⟩ | ⟨_, _, _, _, _, _, h, _⟩ |
    ⟨_, _, h, _⟩ | ⟨_, _, h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩
  · exact ⟨h1, h2, h3⟩
  all_goals cases h

theorem pdpRead {pa : PAddr} {n : Nat} {aq : Bool} {k : List (BitVec 8) → DM Dres}
    {d : DevStates} {l : Wlabel} {dp' : Option (DM Dres)} {d' : DevStates}
    (h : pdiskProg (some (DRead pa n aq k)) d l dp' d') :
    ∃ tvs : List (Nat × BitVec 8), tvs.length = n ∧ l = .LLoad aq false (paZ pa) tvs [] ∧
      dp' = some (k (tvs.map Prod.snd)) ∧ d' = d := by
  rcases h with ⟨h, _⟩ | ⟨_, _, _, _, tvs, h, h1, h2, h3, h4⟩ | ⟨_, h, _⟩ |
    ⟨_, _, _, _, _, _, _, h, _⟩ | ⟨_, _, _, _, _, _, h, _⟩ | ⟨_, _, _, _, _, _, h, _⟩ |
    ⟨_, _, h, _⟩ | ⟨_, _, h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩
  all_goals (try cases h)
  exact ⟨tvs, h1, h2, h3, h4⟩

theorem pdpFence {k : DM Dres} {d : DevStates} {l : Wlabel} {dp' : Option (DM Dres)}
    {d' : DevStates} (h : pdiskProg (some (DFence k)) d l dp' d') :
    l = .LFence true true true true ∧ dp' = some k ∧ d' = d := by
  rcases h with ⟨h, _⟩ | ⟨_, _, _, _, _, h, _⟩ | ⟨_, h, h1, h2, h3⟩ |
    ⟨_, _, _, _, _, _, _, h, _⟩ | ⟨_, _, _, _, _, _, h, _⟩ | ⟨_, _, _, _, _, _, h, _⟩ |
    ⟨_, _, h, _⟩ | ⟨_, _, h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩
  all_goals (try cases h)
  exact ⟨h1, h2, h3⟩

theorem pdpWrite {pre : VirtioState → VirtioState × Bool} {g : VirtioState → Option VirtioState}
    {pa : VirtioState → PAddr} {bs : VirtioState → List (BitVec 8)} {k : VirtioState → DM Dres}
    {d : DevStates} {l : Wlabel} {dp' : Option (DM Dres)} {d' : DevStates}
    (h : pdiskProg (some (DWriteDev pre g pa bs k)) d l dp' d') :
    (∃ s s', pre (dvirtio d) = (s, true) ∧ g s = some s' ∧ ramBytes (pa s) (bs s).length ∧
      l = .LStore false (paZ (pa s)) (bs s) [] [] ∧ dp' = some (k s) ∧ d' = setDvirtio d s') ∨
    (∃ s, pre (dvirtio d) = (s, true) ∧ (g s = none ∨ ¬ ramBytes (pa s) (bs s).length) ∧
      l = .LSilent ∧ dp' = some (k s) ∧ d' = setDvirtio d s) ∨
    (∃ s, pre (dvirtio d) = (s, false) ∧ l = .LSilent ∧ dp' = none ∧ d' = setDvirtio d s) := by
  rcases h with ⟨h, _⟩ | ⟨_, _, _, _, _, h, _⟩ | ⟨_, h, _⟩ |
    ⟨_, _, _, _, _, s, s', h, h1, h2, h3, -, h4, h5, h6⟩ |
    ⟨_, _, _, _, _, s, h, h1, h2, h3, h4, h5⟩ | ⟨_, _, _, _, _, s, h, h1, h2, h3, h4⟩ |
    ⟨_, _, h, _⟩ | ⟨_, _, h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩
  all_goals (try cases h)
  · exact Or.inl ⟨s, s', h1, h2, h3, h4, h5, h6⟩
  · exact Or.inr (Or.inl ⟨s, h1, h2, h3, h4, h5⟩)
  · exact Or.inr (Or.inr ⟨s, h1, h2, h3, h4⟩)

theorem pdpPop {hh : BitVec 16} {k : VirtioState → DM Dres} {d : DevStates} {l : Wlabel}
    {dp' : Option (DM Dres)} {d' : DevStates} (h : pdiskProg (some (DPop hh k)) d l dp' d') :
    l = .LDev .dev 0 [] [] [] ∧
    (((Virtio.phase (dvirtio d) hh).isSome = true ∧ dp' = none ∧ d' = d) ∨
     ((Virtio.phase (dvirtio d) hh).isSome = false ∧ dp' = some (k (popState (dvirtio d) hh)) ∧
       d' = setDvirtio d (popState (dvirtio d) hh))) := by
  rcases h with ⟨h, _⟩ | ⟨_, _, _, _, _, h, _⟩ | ⟨_, h, _⟩ |
    ⟨_, _, _, _, _, _, _, h, _⟩ | ⟨_, _, _, _, _, _, h, _⟩ | ⟨_, _, _, _, _, _, h, _⟩ |
    ⟨_, _, h, h1, h2, h3, h4⟩ | ⟨_, _, h, h1, h2, h3, h4⟩ | ⟨h, _⟩ | ⟨h, _⟩
  all_goals (try cases h)
  · exact ⟨h2, Or.inl ⟨h1, h3, h4⟩⟩
  · exact ⟨h2, Or.inr ⟨h1, h3, h4⟩⟩

theorem pdpRet {a : Dres} {d : DevStates} {l : Wlabel} {dp' : Option (DM Dres)} {d' : DevStates}
    (h : pdiskProg (some (DRet a)) d l dp' d') :
    l = .LSilent ∧ d' = d ∧ ((a = DStall ∧ dp' = some (DRet DStall)) ∨ (a = DIdle ∧ dp' = none)) := by
  rcases h with ⟨h, _⟩ | ⟨_, _, _, _, _, h, _⟩ | ⟨_, h, _⟩ |
    ⟨_, _, _, _, _, _, _, h, _⟩ | ⟨_, _, _, _, _, _, h, _⟩ | ⟨_, _, _, _, _, _, h, _⟩ |
    ⟨_, _, h, _⟩ | ⟨_, _, h, _⟩ | ⟨h, h1, h2, h3⟩ | ⟨h, h1, h2, h3⟩
  all_goals (try cases h)
  · exact ⟨h1, h3, Or.inl ⟨rfl, h2⟩⟩
  · exact ⟨h1, h3, Or.inr ⟨rfl, h2⟩⟩

/-! ### The folded parts, inverted -/

theorem cacheWfOf {v v' : VirtioState} (h : v'.cache = v.cache) (hw : cacheWf v) : cacheWf v' := by
  unfold cacheWf; rw [h]; exact hw

theorem phaseSet (v : VirtioState) (h : BitVec 16) (p : VPhase) :
    Virtio.phase (setPhase v h p) h = some p := by
  simp [Virtio.phase, Virtio.setPhase, alistSet, alistGet]

theorem reqOfFetched (v : VirtioState) (h : BitVec 16) (r : VioReq) :
    reqOf (setPhase v h (.fetched r)) h = some r := by
  simp [reqOf, phaseSet, VPhase.req]

theorem reqGuardFetched (v : VirtioState) (h : BitVec 16) (r : VioReq) :
    reqGuard h r (setPhase v h (.fetched r)) = some (setPhase v h (.fetched r)) := by
  simp [reqGuard, reqOfFetched]

theorem pre1True (h : BitVec 16) (r : VioReq) (v : VirtioState)
    (ht : (preCaptureHead h r v).2 = true) :
    (Virtio.phase v h).isSome = true ∧ v.taken = none ∧
      (preCaptureHead h r v).1 = { setPhase v h (.fetched r) with taken := some h } := by
  unfold preCaptureHead at ht ⊢
  by_cases hs : (Virtio.phase v h).isSome = true
  · rw [if_pos hs] at ht ⊢
    simp only at ht ⊢
    by_cases hk : (setPhase v h (.fetched r)).taken = none
    · rw [if_pos hk]
      exact ⟨hs, hk, rfl⟩
    · rw [if_neg hk] at ht; cases ht
  · rw [if_neg hs] at ht; cases ht

theorem pre1False (h : BitVec 16) (r : VioReq) (v : VirtioState)
    (hf : (preCaptureHead h r v).2 = false) :
    (Virtio.phase v h = none ∧ (preCaptureHead h r v).1 = v) ∨
    ((Virtio.phase v h).isSome = true ∧ v.taken ≠ none ∧
      (preCaptureHead h r v).1 = setPhase v h (.fetched r)) := by
  unfold preCaptureHead at hf ⊢
  by_cases hs : (Virtio.phase v h).isSome = true
  · rw [if_pos hs] at hf ⊢
    simp only at hf ⊢
    by_cases hk : (setPhase v h (.fetched r)).taken = none
    · rw [if_pos hk] at hf; cases hf
    · rw [if_neg hk]
      exact Or.inr ⟨hs, hk, rfl⟩
  · rw [if_neg hs]
    exact Or.inl ⟨by simpa using hs, rfl⟩

theorem preCaptureInv (h : BitVec 16) (r : VioReq) (bs : List (BitVec 8)) (v s : VirtioState)
    (b : Bool) (hp : preCapture h r bs v = (s, b)) :
    (preCaptureHead h r v).2 = b ∧
      (b = true → s = captureMove h r bs (preCaptureHead h r v).1) ∧
      (b = false → s = (preCaptureHead h r v).1) := by
  unfold preCapture at hp
  simp only at hp
  cases hb : (preCaptureHead h r v).2
  · rw [if_neg (by simp [hb])] at hp
    simp only [Prod.mk.injEq] at hp
    exact ⟨hp.2, (fun hbt => by rw [← hp.2] at hbt; cases hbt), fun _ => hp.1.symm⟩
  · rw [if_pos hb] at hp
    simp only [Prod.mk.injEq] at hp
    exact ⟨hp.2, fun _ => hp.1.symm, (fun hbf => by rw [← hp.2] at hbf; cases hbf)⟩

/-- A folded part of the shape "pre-check, then a fixed move `f`". -/
theorem preSimpleInv {pre : VirtioState → VirtioState × Bool} {h : BitVec 16}
    {f : VirtioState → VirtioState}
    (hpre : ∀ v, pre v = if (Virtio.phase v h).isSome then (f v, true) else (v, false))
    (v s : VirtioState) (b : Bool) (hp : pre v = (s, b)) :
    (b = true ∧ (Virtio.phase v h).isSome = true ∧ s = f v) ∨
    (b = false ∧ Virtio.phase v h = none ∧ s = v) := by
  rw [hpre] at hp
  by_cases hs : (Virtio.phase v h).isSome = true
  · rw [if_pos hs] at hp
    simp only [Prod.mk.injEq] at hp
    exact Or.inl ⟨hp.2.symm, hs, hp.1.symm⟩
  · rw [if_neg hs] at hp
    simp only [Prod.mk.injEq] at hp
    exact Or.inr ⟨hp.2.symm, by simpa using hs, hp.1.symm⟩

theorem preFillEq (h : BitVec 16) (r : VioReq) (v : VirtioState) :
    preFill h r v = if (Virtio.phase v h).isSome then (setPhase v h (.fetched r), true) else (v, false) := rfl

theorem preServedEq (h : BitVec 16) (r : VioReq) (v : VirtioState) :
    preServed h r v = if (Virtio.phase v h).isSome then (setPhase v h (.served r), true) else (v, false) := rfl

theorem preNoDataEq (h : BitVec 16) (r : VioReq) (v : VirtioState) :
    preNoData h r v = if (Virtio.phase v h).isSome then
      (setPhase (setPhase v h (.fetched r)) h (.served r), true) else (v, false) := rfl

theorem preGateInv (h : BitVec 16) (r : VioReq) (v s : VirtioState) (b : Bool)
    (hp : preGate h r v = (s, b)) :
    (Virtio.phase v h = none ∧ b = false ∧ s = v) ∨
    ((Virtio.phase v h).isSome = true ∧
      gateG h r (drainAll (setPhase v h (.status r))) = (if b then some s else none) ∧
      (b = false → s = drainAll (setPhase v h (.status r)))) := by
  unfold preGate at hp
  by_cases hs : (Virtio.phase v h).isSome = true
  · rw [if_pos hs] at hp
    simp only at hp
    refine Or.inr ⟨hs, ?_⟩
    unfold gateG
    split
    · next hg =>
      rw [if_pos hg] at hp
      simp only [Prod.mk.injEq] at hp
      obtain ⟨rfl, rfl⟩ := hp
      exact ⟨rfl, fun h => by cases h⟩
    · next hg =>
      rw [if_neg hg] at hp
      simp only [Prod.mk.injEq] at hp
      obtain ⟨rfl, rfl⟩ := hp
      exact ⟨rfl, fun _ => rfl⟩
  · rw [if_neg hs] at hp
    simp only [Prod.mk.injEq] at hp
    exact Or.inl ⟨by simpa using hs, hp.2.symm, hp.1.symm⟩

theorem usedGSelf (h : BitVec 16) (r : VioReq) (s : VirtioState) :
    usedG h r s.usedIdx s.cfg s = reqGuard h r s := by
  simp [usedG, reqGuard]

theorem reqGuardSome {h : BitVec 16} {r : VioReq} {s s' : VirtioState}
    (hg : reqGuard h r s = some s') : s' = s := by
  unfold reqGuard at hg
  split at hg
  · exact (Option.some.inj hg).symm
  · cases hg

/-! ### `R-dev` after a disk step -/

theorem agSet (κ : VRel) (ds : DevStates) (s s' : VirtioState) (hk : κ.holds s s') (hc : cacheWf s) :
    devAgree κ (setDvirtio ds s) (setDvirtio ds s') :=
  ⟨s', (setDvirtioTwice ds s s').symm, by rw [dvirtioSet]; exact hk, by rw [dvirtioSet]; exact hc⟩

/-- The pf disk state moves to `s`, MachCSL's to `s'`, related by `κ`. -/
theorem agMove {κ0 : VRel} (κ : VRel) {dsP dsM : DevStates} (hag : devAgree κ0 dsP dsM)
    (s s' : VirtioState) (hk : κ.holds s s') (hc : cacheWf s) :
    devAgree κ (setDvirtio dsP s) (setDvirtio dsM s') := by
  obtain ⟨vm, rfl, -, -⟩ := hag
  rw [setDvirtioTwice]
  exact agSet κ dsP s s' hk hc

/-- The pf disk state stays, MachCSL's moves to `s'`. -/
theorem agMoveM {κ0 : VRel} (κ : VRel) {dsP dsM : DevStates} (hag : devAgree κ0 dsP dsM)
    (s' : VirtioState) (hk : κ.holds (dvirtio dsP) s') (hc : cacheWf (dvirtio dsP)) :
    devAgree κ dsP (setDvirtio dsM s') := by
  have := agMove κ hag (dvirtio dsP) s' hk hc
  rwa [setDvirtioSelf] at this

/-- Neither moves; the virtio clause is re-read. -/
theorem agRe {κ0 κ : VRel} {dsP dsM : DevStates} (hag : devAgree κ0 dsP dsM)
    (h : ∀ vm, κ0.holds (dvirtio dsP) vm → κ.holds (dvirtio dsP) vm) : devAgree κ dsP dsM := by
  obtain ⟨vm, h1, h2, h3⟩ := hag
  exact ⟨vm, h1, h vm h2, h3⟩

theorem agEqOf {dsP dsM : DevStates} (h : devAgree .eq dsP dsM) :
    dsM = dsP ∧ cacheWf (dvirtio dsP) := by
  obtain ⟨vm, rfl, hk, hc⟩ := h
  have : vm = dvirtio dsP := hk
  subst this
  exact ⟨setDvirtioSelf dsP, hc⟩

theorem agCache {κ : VRel} {dsP dsM : DevStates} (h : devAgree κ dsP dsM) : cacheWf (dvirtio dsP) := by
  obtain ⟨_, _, _, hc⟩ := h
  exact hc

theorem agSt {κ : VRel} {dsP dsM : DevStates} (h : devAgree κ dsP dsM) :
    dsM = setDvirtio dsP (dsM.st .virtio) ∧ κ.holds (dvirtio dsP) (dsM.st .virtio) := by
  obtain ⟨vm, rfl, hk, -⟩ := h
  rw [setDvirtioSt]
  exact ⟨rfl, hk⟩

theorem pre1Free (h : BitVec 16) (r : VioReq) (v : VirtioState)
    (hs : (Virtio.phase v h).isSome = true) (ht : v.taken = none) :
    preCaptureHead h r v = ({ setPhase v h (.fetched r) with taken := some h }, true) := by
  unfold preCaptureHead
  rw [if_pos hs]
  simp only
  rw [if_pos (show (setPhase v h (.fetched r)).taken = none from ht)]

theorem pre1Held (h : BitVec 16) (r : VioReq) (v : VirtioState)
    (hs : (Virtio.phase v h).isSome = true) (ht : ¬ v.taken = none) :
    preCaptureHead h r v = (setPhase v h (.fetched r), false) := by
  unfold preCaptureHead
  rw [if_pos hs]
  simp only
  rw [if_neg (show ¬ (setPhase v h (.fetched r)).taken = none from ht)]

theorem pre1Cache (h : BitVec 16) (r : VioReq) (v : VirtioState) :
    (preCaptureHead h r v).1.cache = v.cache := by
  rw [pre1Eq]

theorem idxGuardSome {h : BitVec 16} {r : VioReq} {ui : BitVec 16} {c : VirtioCfg}
    {s s' : VirtioState} (hg : idxGuard h r ui c s = some s') : s' = complete s h := by
  unfold idxGuard at hg
  split at hg
  · exact (Option.some.inj hg).symm
  · cases hg

theorem gateGSome {h : BitVec 16} {r : VioReq} {s s' : VirtioState} (hg : gateG h r s = some s') :
    s' = setPhase s h (.pushed r) := by
  unfold gateG at hg
  split at hg
  · exact (Option.some.inj hg).symm
  · cases hg

theorem diskReadLength (dk : Nat → BitVec 8) (off n : Nat) : (diskRead dk off n).length = n := by
  simp [diskRead]

end MachOfPfDisk

end Weak
