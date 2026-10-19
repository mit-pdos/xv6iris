/-
Weak: **allocproc route P — `SbOrd.DevStOrd` DISCHARGED** (PROGRESS-P.md §DEVSTORD; plan rev 55, the
named device-model fact of row H4).  Lean-only, no Rocq twin.  A PRIMED TWIN: nothing registered
imports this file.

**Spec, stated first.**  RVWMO / riscv.cat / Sail have no device events; Zifencei and the PMAs are
silent on DMA.  `DevStOrd` ("a non-I/O fabric member of a device row is gmo-before every po-later
memory event of its row") is therefore device-MODEL text, and this file shows it is NOT a new item:
it FOLLOWS from what the tree already carries —
* the device program's TEXT (`virtioProg`, `Weak/VirtioProg.lean`) through the disk agent's step
  (`WeakEvInst.pdiskProg`) and the row emission (`hemitf` in `GraphFabConf.gfexecConfZF`): after a
  fabric-moving `DWriteDev` store the residual program is READ-FREE (only `DWriteDev`, `DFence`,
  `DRet` until the burst ends; the next read follows the next START, an `LDev` = I/O row event) —
  `SbDevSt.goodProg`, `SbDevSt.rowStRd`; and every disk store block is a fabric CONTACT, so a fabric
  member (`SbDevSt.rowTq`);
* the trusted residue's (R1) (RAM access po-before I/O), (R2) (I/O po-before a RAM write), (R2′)
  (I/O po-before a DISK-row RAM read), (R3a) (same-row I/O) — (R2″) [OWN.116] only on a device row
  other than `NCPU` (none on xv6's bundle: `SbDevSt.xbootDisk` puts the one disk at row `NCPU`);
* the NAMED device-model facts already in the tree: `LockFacts3.diskFabPo` (a device row's fabric RAM
  stores are gmo-ordered along po — needed for store → store with no I/O between, e.g. the IN fill
  before its status byte, which RVWMO leaves unordered: different addresses, no fence) and
  `gfDevWIo` (= `usedElemGateOk` on the disk row, [OWN.93]: every fabric member is a RAM write or
  I/O — so the member is a STORE, not the `DFence` block of a skipped used element);
* the boot shape: every row `≥ NCPU` boots as the idle disk `PDisk none`.

  §1  read-freedom of the program text: `NoRd`, `Good`, `goodProg` (every `virtioProg v`).
  §2  the disk agent's step: `stepGood`, `stepQuiet`, `stepStore`, the admin runs, no pair block.
  §3  the row: `rowQuiet` (a read-free state reads only after an I/O event), `rowTq`, `rowStRd`.
  §4  **`SbDevSt.devStOrd`** (`DevStOrd` from the above) and the consumer forms: `walkHypCZD`
      (`SbKill.walkHypCZ` minus `DevStOrd`), `certSupplyOfWalkPD`, `cycleKillOfWalkPD`,
      `cycleKillAllPD`; `xbootDisk`, `diskFabPoCZ` (+ `diskFabPoCZOfLockDisc`).

Spec mark: FAITHFUL (proof organisation; no new trusted text, no new named item — `DevStOrd` is
replaced by the strictly narrower, already-named `diskFabPo`).  Names: Lean-only, `SbDevSt.*`.
-/
import Weak.SbKill

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open TsoShadow
open Lbl SbWalk SbAgree SbReplay SbOrd

/-! # 1. Read-freedom of the device program's text -/

/-- A READ-FREE residual program: only stores, fences and results until the burst ends. -/
inductive SbDevSt.NoRd : DM Dres → Prop where
  | ret (a : Dres) : SbDevSt.NoRd (DRet a)
  | fence (k : DM Dres) : SbDevSt.NoRd k → SbDevSt.NoRd (DFence k)
  | wr (pre : VirtioState → VirtioState × Bool) (g : VirtioState → Option VirtioState)
      (pa : VirtioState → PAddr) (bs : VirtioState → List (BitVec 8)) (k : VirtioState → DM Dres) :
      (∀ s, SbDevSt.NoRd (k s)) → SbDevSt.NoRd (DWriteDev pre g pa bs k)

/-- A residual program in which every `DWriteDev`'s continuation is read-free. -/
inductive SbDevSt.Good : DM Dres → Prop where
  | ret (a : Dres) : SbDevSt.Good (DRet a)
  | read (pa : PAddr) (n : Nat) (aq : Bool) (k : List (BitVec 8) → DM Dres) :
      (∀ bs, SbDevSt.Good (k bs)) → SbDevSt.Good (DRead pa n aq k)
  | fence (k : DM Dres) : SbDevSt.Good k → SbDevSt.Good (DFence k)
  | wr (pre : VirtioState → VirtioState × Bool) (g : VirtioState → Option VirtioState)
      (pa : VirtioState → PAddr) (bs : VirtioState → List (BitVec 8)) (k : VirtioState → DM Dres) :
      (∀ s, SbDevSt.NoRd (k s)) → SbDevSt.Good (DWriteDev pre g pa bs k)
  | pop (h : BitVec 16) (k : VirtioState → DM Dres) :
      (∀ s, SbDevSt.Good (k s)) → SbDevSt.Good (DPop h k)

theorem SbDevSt.goodOfNoRd (m : DM Dres) : SbDevSt.NoRd m → SbDevSt.Good m := by
  intro h
  induction h with
  | ret a => exact .ret a
  | fence k _ ih => exact .fence k ih
  | wr pre g pa bs k hk _ => exact .wr pre g pa bs k hk

theorem SbDevSt.noRdIdx (h : BitVec 16) (r : VioReq) (ui : BitVec 16) (c : VirtioCfg) :
    SbDevSt.NoRd (VirtioProg.idxNode h r ui c) :=
  .wr _ _ _ _ _ (fun _ => .ret _)

theorem SbDevSt.noRdUsed (h : BitVec 16) (r : VioReq) : SbDevSt.NoRd (dusedTail h r) :=
  .wr _ _ _ _ _ (fun _ => .fence _ (SbDevSt.noRdIdx _ _ _ _))

theorem SbDevSt.noRdTail (h : BitVec 16) (r : VioReq) (pre : VirtioState → VirtioState × Bool) :
    SbDevSt.NoRd (dtail h r pre) :=
  .wr _ _ _ _ _ (fun _ => SbDevSt.noRdUsed h r)

theorem SbDevSt.goodTail (h : BitVec 16) (r : VioReq) (pre : VirtioState → VirtioState × Bool) :
    SbDevSt.Good (dtail h r pre) :=
  SbDevSt.goodOfNoRd _ (SbDevSt.noRdTail h r pre)

theorem SbDevSt.goodFill (h : BitVec 16) (r : VioReq) : SbDevSt.Good (VirtioProg.fillNode h r) :=
  .wr _ _ _ _ _ (fun _ => SbDevSt.noRdTail _ _ _)

theorem SbDevSt.goodData (pa : PAddr) (n : Nat) (k : List (BitVec 8) → DM Dres) :
    (∀ bs, SbDevSt.Good (k bs)) → SbDevSt.Good (dreadData pa n k) := by
  intro hk
  cases n with
  | zero => exact hk []
  | succ n => exact .read _ _ _ _ hk

theorem SbDevSt.goodComplete (h : BitVec 16) (r : VioReq) : SbDevSt.Good (dcomplete h r) := by
  unfold dcomplete
  split
  · split
    · exact .ret _
    · exact SbDevSt.goodData _ _ _ (fun _ => SbDevSt.goodTail _ _ _)
  · split
    · exact SbDevSt.goodFill _ _
    · exact SbDevSt.goodTail _ _ _

theorem SbDevSt.goodFetch (c : VirtioCfg) (h : BitVec 16) :
    SbDevSt.Good (VirtioProg.fetchProg c h) := by
  dsimp only [VirtioProg.fetchProg, dreadDesc, dreadWord]
  split
  · exact .ret _
  refine .read _ _ _ _ (fun _ => ?_)
  split
  · exact .ret _
  refine .read _ _ _ _ (fun _ => ?_)
  split
  · exact .ret _
  refine .read _ _ _ _ (fun _ => ?_)
  split
  · exact .ret _
  refine .read _ _ _ _ (fun _ => ?_)
  refine .read _ _ _ _ (fun _ => ?_)
  exact SbDevSt.goodComplete _ _

/-- **THE PROGRAM TEXT**: every burst `virtioProg v` is `Good` — a read never follows a store inside
a burst. -/
theorem SbDevSt.goodProg (v : VirtioState) : SbDevSt.Good (virtioProg v) := by
  dsimp only [virtioProg, dreadAvailIdx, dreadAvailRing, dreadWord]
  split
  · refine .read _ _ _ _ (fun _ => ?_)
    split
    · exact .read _ _ _ _ (fun _ => .pop _ _ (fun s => SbDevSt.goodFetch _ _))
    · exact .ret _
  · exact .ret _

/-! # 2. The disk agent's step -/

/-- A disk agent whose residual program is `Good` (or idle). -/
def SbDevSt.dGood : Pexv6 → Prop
  | .PDisk none => True
  | .PDisk (some m) => SbDevSt.Good m
  | .PHart .. => False

/-- A disk agent whose residual program is read-free (or idle). -/
def SbDevSt.dQuiet : Pexv6 → Prop
  | .PDisk none => True
  | .PDisk (some m) => SbDevSt.NoRd m
  | .PHart .. => False

theorem SbDevSt.stepDisk (dp : Option (DM Dres)) (d : Efab) (l : Wlabel) (p' : Pexv6) (d' : Efab) :
    pstepEv (.PDisk dp) d l p' d' → ∃ dp', p' = .PDisk dp' ∧ pstepDisk dp d l dp' d' := by
  intro h
  cases p' with
  | PHart => simp [pstepEv] at h
  | PDisk dp' => exact ⟨dp', rfl, h⟩

theorem SbDevSt.dGoodDisk (p : Pexv6) : SbDevSt.dGood p → ∃ dp, p = .PDisk dp := by
  intro h
  cases p with
  | PHart => exact h.elim
  | PDisk dp => exact ⟨dp, rfl⟩

theorem SbDevSt.dQuietDisk (p : Pexv6) : SbDevSt.dQuiet p → ∃ dp, p = .PDisk dp := by
  intro h
  cases p with
  | PHart => exact h.elim
  | PDisk dp => exact ⟨dp, rfl⟩

theorem SbDevSt.dQuietGood (p : Pexv6) : SbDevSt.dQuiet p → SbDevSt.dGood p := by
  intro h
  cases p with
  | PHart => exact h.elim
  | PDisk dp =>
    cases dp with
    | none => trivial
    | some m => exact SbDevSt.goodOfNoRd m h

/-- `Good` is preserved by every disk step. -/
theorem SbDevSt.stepGood (p : Pexv6) (d : Efab) (l : Wlabel) (p' : Pexv6) (d' : Efab) :
    SbDevSt.dGood p → pstepEv p d l p' d' → SbDevSt.dGood p' := by
  intro hp hs
  obtain ⟨dp, rfl⟩ := SbDevSt.dGoodDisk p hp
  obtain ⟨dp', rfl, hs⟩ := SbDevSt.stepDisk dp d l p' d' hs
  rcases hs with ⟨hs, -⟩ | ⟨rfl, -⟩
  · rcases hs with ⟨-, -, rfl, -⟩ | ⟨_, _, _, k, _, rfl, -, -, rfl, -⟩ | ⟨k, rfl, -, rfl, -⟩ |
      ⟨_, _, _, _, k, s, _, rfl, -, -, -, -, -, rfl, -⟩ | ⟨_, _, _, _, k, s, rfl, -, -, -, rfl, -⟩ |
      ⟨_, _, _, _, _, _, rfl, -, -, rfl, -⟩ | ⟨_, _, rfl, -, -, rfl, -⟩ | ⟨_, k, rfl, -, -, rfl, -⟩ |
      ⟨rfl, -, rfl, -⟩ | ⟨rfl, -, rfl, -⟩
    · exact SbDevSt.goodProg _
    · cases hp with | read _ _ _ _ h => exact h _
    · cases hp with | fence _ h => exact h
    · cases hp with | wr _ _ _ _ _ h => exact SbDevSt.goodOfNoRd _ (h s)
    · cases hp with | wr _ _ _ _ _ h => exact SbDevSt.goodOfNoRd _ (h s)
    · trivial
    · trivial
    · cases hp with | pop _ _ h => exact h _
    · exact hp
    · trivial
  · exact hp

/-- A read-free disk step is an `LDev` step, or stays read-free and is no read. -/
theorem SbDevSt.stepQuiet (p : Pexv6) (d : Efab) (l : Wlabel) (p' : Pexv6) (d' : Efab) :
    SbDevSt.dQuiet p → pstepEv p d l p' d' →
    GraphFabConf.isLDev l = true ∨
      (SbDevSt.dQuiet p' ∧ ∀ c lb, projLbl c l = some lb → lbIsR lb = false) := by
  intro hp hs
  obtain ⟨dp, rfl⟩ := SbDevSt.dQuietDisk p hp
  obtain ⟨dp', rfl, hs⟩ := SbDevSt.stepDisk dp d l p' d' hs
  rcases hs with ⟨hs, -⟩ | ⟨-, rfl, -⟩
  · rcases hs with ⟨-, rfl, -⟩ | ⟨_, _, _, k, _, rfl, -, -, rfl, -⟩ | ⟨k, rfl, rfl, rfl, -⟩ |
      ⟨_, _, _, _, k, s, _, rfl, -, -, -, -, rfl, rfl, -⟩ | ⟨_, _, _, _, k, s, rfl, -, -, rfl, rfl, -⟩ |
      ⟨_, _, _, _, _, _, rfl, -, rfl, rfl, -⟩ | ⟨_, _, rfl, -, rfl, rfl, -⟩ |
      ⟨_, k, rfl, -, rfl, rfl, -⟩ | ⟨rfl, rfl, rfl, -⟩ | ⟨rfl, rfl, rfl, -⟩
    · exact .inl rfl
    · cases hp
    · cases hp with
      | fence _ h =>
        refine .inr ⟨h, fun c lb hl => ?_⟩
        simp only [projLbl, Option.some.injEq] at hl
        subst hl; rfl
    · cases hp with
      | wr _ _ _ _ _ h =>
        refine .inr ⟨h s, fun c lb hl => ?_⟩
        simp only [projLbl, Option.some.injEq] at hl
        subst hl; rfl
    · cases hp with
      | wr _ _ _ _ _ h =>
        exact .inr ⟨h s, fun c lb hl => by simp [projLbl] at hl⟩
    · exact .inr ⟨trivial, fun c lb hl => by simp [projLbl] at hl⟩
    · cases hp
    · cases hp
    · exact .inr ⟨hp, fun c lb hl => by simp [projLbl] at hl⟩
    · exact .inr ⟨trivial, fun c lb hl => by simp [projLbl] at hl⟩
  · exact .inl rfl

/-- A disk step whose label projects to a WRITE is a fabric-moving `DWriteDev` store: the residual
program is read-free and the step is a fabric contact. -/
theorem SbDevSt.stepStore (p : Pexv6) (d : Efab) (l : Wlabel) (p' : Pexv6) (d' : Efab)
    (c : WmClass) (lb : Lbl) :
    SbDevSt.dGood p → pstepEv p d l p' d' → projLbl c l = some lb → lbIsW lb = true →
    SbDevSt.dQuiet p' ∧ pdevEv p l p' = true := by
  intro hp hs hl hw
  obtain ⟨dp, rfl⟩ := SbDevSt.dGoodDisk p hp
  obtain ⟨dp', rfl, hs⟩ := SbDevSt.stepDisk dp d l p' d' hs
  rcases hs with ⟨hs, -⟩ | ⟨-, rfl, -⟩
  · rcases hs with ⟨-, rfl, -⟩ | ⟨_, _, _, k, _, rfl, -, rfl, rfl, -⟩ | ⟨k, rfl, rfl, rfl, -⟩ |
      ⟨_, _, _, _, k, s, _, rfl, -, -, -, -, rfl, rfl, -⟩ | ⟨_, _, _, _, k, s, rfl, -, -, rfl, rfl, -⟩ |
      ⟨_, _, _, _, _, _, rfl, -, rfl, rfl, -⟩ | ⟨_, _, rfl, -, rfl, rfl, -⟩ |
      ⟨_, k, rfl, -, rfl, rfl, -⟩ | ⟨rfl, rfl, rfl, -⟩ | ⟨rfl, rfl, rfl, -⟩ <;>
      simp only [projLbl, Option.some.injEq, reduceCtorEq] at hl
    · subst hl; simp [lbIsW] at hw
    · subst hl; simp [lbIsW] at hw
    · subst hl; simp [lbIsW] at hw
    · cases hp with
      | wr _ _ _ _ _ h => exact ⟨h s, by simp [pdevEv]⟩
    · subst hl; simp [lbIsW] at hw
    · subst hl; simp [lbIsW] at hw
  · simp only [projLbl, Option.some.injEq] at hl
    subst hl; simp [lbIsW] at hw

/-- The disk's label shapes (the program's five, the UART/PLIC moves' `LDev`). -/
theorem SbDevSt.stepLbl (dp : Option (DM Dres)) (d : Efab) (l : Wlabel) (p' : Pexv6) (d' : Efab) :
    pstepEv (.PDisk dp) d l p' d' →
    l = Wlabel.LDev .dev 0 [] [] [] ∨ (∃ aq base tvs, l = Wlabel.LLoad aq false base tvs []) ∨
    l = Wlabel.LFence true true true true ∨ (∃ base data, l = Wlabel.LStore false base data [] []) ∨
    l = Wlabel.LSilent := by
  intro hs
  obtain ⟨dp', -, hs⟩ := SbDevSt.stepDisk dp d l p' d' hs
  rcases hs with ⟨hs, -⟩ | ⟨-, rfl, -⟩
  · exact WeakEvInst.pdiskProgLabel _ _ _ _ _ hs
  · exact .inl rfl

/-- No disk block is a PAIR block (the pair's first step is an `LExLoad`). -/
theorem SbDevSt.noPair (dp : Option (DM Dres)) (d : Efab) (l1 : Wlabel) (pm : Pexv6) (dm : Efab)
    (pm2 : Pexv6) (ws : Wstate) (lb : Lbl) (l2 : Wlabel) :
    pstepEv (.PDisk dp) d l1 pm dm → ¬ hlblRealizesPair (.PDisk dp) pm2 ws lb l1 l2 := by
  intro hs ⟨_, _, _, _, _, _, _, _, h1, _⟩
  subst h1
  rcases SbDevSt.stepLbl dp d _ pm dm hs with h | ⟨_, _, _, h⟩ | h | ⟨_, _, h⟩ | h <;> cases h

theorem SbDevSt.admGood (instr : Bool) (p : Pexv6) (d : Efab) (ls : List Wlabel) (p' : Pexv6)
    (d' : Efab) (b : Bool) :
    WeakRvwmoFab.admRunT instr p d ls p' d' b → SbDevSt.dGood p → SbDevSt.dGood p' := by
  intro h
  induction h with
  | ATnil => exact id
  | ATcons p d l p1 d1 ls p' d' b _ hs _ ih =>
    exact fun hp => ih (SbDevSt.stepGood p d l p1 d1 hp hs)

theorem SbDevSt.admQuiet (instr : Bool) (p : Pexv6) (d : Efab) (ls : List Wlabel) (p' : Pexv6)
    (d' : Efab) (b : Bool) :
    WeakRvwmoFab.admRunT instr p d ls p' d' b → SbDevSt.dQuiet p → SbDevSt.dQuiet p' := by
  intro h
  induction h with
  | ATnil => exact id
  | ATcons p d l p1 d1 ls p' d' b ha hs _ ih =>
    intro hp
    rcases SbDevSt.stepQuiet p d l p1 d1 hp hs with hl | ⟨hq, -⟩
    · rw [GraphFabConf.adminNotLDev instr l ha] at hl; cases hl
    · exact ih hq

/-! # 3. The disk row -/

/-- **A read-free disk state reads only after an I/O row event.** -/
theorem SbDevSt.rowQuiet (dvi dvo : Nat → Efab) (tq : Nat → Bool) (k : Nat) (ws : Wstate)
    (row : List Lbl) (p : Pexv6) (es : List Eitem) (pfin : Pexv6) :
    hemitf dvi dvo tq k ws row p es pfin → SbDevSt.dQuiet p →
    ∀ (j : Nat) (lb : Lbl), row[j]? = some lb → lbIsR lb = true →
      ∃ (i : Nat) (lbi : Lbl), i ≤ j ∧ row[i]? = some lbi ∧ lbIsIo lbi = true := by
  intro h
  induction h with
  | HFnil => intro _ j lb hj; simp at hj
  | HFone k ws lb row p ls pa da l p' es pfin b har hre hst _ _ ih =>
    intro hq j lbj hj hr
    have hqa := SbDevSt.admQuiet _ _ _ _ _ _ _ har hq
    rcases SbDevSt.stepQuiet pa da l p' (dvo k) hqa hst with hdev | ⟨hq', hnr⟩
    · exact ⟨0, lb, Nat.zero_le _, rfl, GraphFabConf.realizesLDevIo pa ws lb l hre hdev⟩
    · cases j with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
        subst hj
        rw [hnr _ _ hre.2.2.2] at hr
        cases hr
      | succ j =>
        obtain ⟨i, lbi, hi, hri, hio⟩ := ih hq' j lbj hj hr
        exact ⟨i + 1, lbi, by omega, hri, hio⟩
  | HFpair k ws lb row p ls1 pa da l1 pm dm ls2 pm2 dm2 l2 p' es pfin b1 b2 har1 hre hst1 _ _ _ _ _ =>
    intro hq
    obtain ⟨dp, rfl⟩ := SbDevSt.dQuietDisk pa (SbDevSt.admQuiet _ _ _ _ _ _ _ har1 hq)
    exact absurd hre (SbDevSt.noPair dp da l1 pm dm pm2 ws lb l2 hst1)

/-- **Every disk-row write is a fabric contact** (its block's contact bit is set). -/
theorem SbDevSt.rowTq (dvi dvo : Nat → Efab) (tq : Nat → Bool) (k : Nat) (ws : Wstate)
    (row : List Lbl) (p : Pexv6) (es : List Eitem) (pfin : Pexv6) :
    hemitf dvi dvo tq k ws row p es pfin → SbDevSt.dGood p →
    ∀ (j : Nat) (lb : Lbl), row[j]? = some lb → lbIsW lb = true → tq (k + j) = true := by
  intro h
  induction h with
  | HFnil => intro _ j lb hj; simp at hj
  | HFone k ws lb row p ls pa da l p' es pfin b har hre hst htq _ ih =>
    intro hg j lbj hj hw
    have hga := SbDevSt.admGood _ _ _ _ _ _ _ har hg
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
      rw [← hj] at hw
      obtain ⟨-, hd⟩ := SbDevSt.stepStore pa da l p' (dvo k) _ lb hga hst hre.2.2.2 hw
      rw [Nat.add_zero, htq, hd, Bool.or_true]
    | succ j =>
      have := ih (SbDevSt.stepGood pa da l p' (dvo k) hga hst) j lbj hj hw
      rw [show k + (j + 1) = k + 1 + j by omega]
      exact this
  | HFpair k ws lb row p ls1 pa da l1 pm dm ls2 pm2 dm2 l2 p' es pfin b1 b2 har1 hre hst1 _ _ _ _ _ =>
    intro hg
    obtain ⟨dp, rfl⟩ := SbDevSt.dGoodDisk pa (SbDevSt.admGood _ _ _ _ _ _ _ har1 hg)
    exact absurd hre (SbDevSt.noPair dp da l1 pm dm pm2 ws lb l2 hst1)

/-- **A disk-row read po-after a disk-row write has an I/O row event between** (strictly after the
write, at or before the read). -/
theorem SbDevSt.rowStRd (dvi dvo : Nat → Efab) (tq : Nat → Bool) (k : Nat) (ws : Wstate)
    (row : List Lbl) (p : Pexv6) (es : List Eitem) (pfin : Pexv6) :
    hemitf dvi dvo tq k ws row p es pfin → SbDevSt.dGood p →
    ∀ (j j' : Nat) (lbj lbj' : Lbl), j < j' → row[j]? = some lbj → lbIsW lbj = true →
      row[j']? = some lbj' → lbIsR lbj' = true → ∃ (i : Nat) (lbi : Lbl), j < i ∧ i ≤ j' ∧ row[i]? = some lbi ∧ lbIsIo lbi = true := by
  intro h
  induction h with
  | HFnil => intro _ j j' lbj lbj' _ hj; simp at hj
  | HFone k ws lb row p ls pa da l p' es pfin b har hre hst _ htl ih =>
    intro hg j j' lbj lbj' hlt hj hw hj' hr
    have hga := SbDevSt.admGood _ _ _ _ _ _ _ har hg
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
      rw [← hj] at hw
      obtain ⟨hq, -⟩ := SbDevSt.stepStore pa da l p' (dvo k) _ lb hga hst hre.2.2.2 hw
      obtain ⟨j'', rfl⟩ : ∃ j'', j' = j'' + 1 := ⟨j' - 1, by omega⟩
      obtain ⟨i, lbi, hi, hri, hio⟩ :=
        SbDevSt.rowQuiet _ _ _ _ _ _ _ _ _ htl hq j'' lbj' hj' hr
      exact ⟨i + 1, lbi, by omega, by omega, hri, hio⟩
    | succ j =>
      obtain ⟨j'', rfl⟩ : ∃ j'', j' = j'' + 1 := ⟨j' - 1, by omega⟩
      obtain ⟨i, lbi, h1, h2, hri, hio⟩ :=
        ih (SbDevSt.stepGood pa da l p' (dvo k) hga hst) j j'' lbj lbj' (by omega) hj hw hj' hr
      exact ⟨i + 1, lbi, by omega, by omega, hri, hio⟩
  | HFpair k ws lb row p ls1 pa da l1 pm dm ls2 pm2 dm2 l2 p' es pfin b1 b2 har1 hre hst1 _ _ _ _ _ =>
    intro hg
    obtain ⟨dp, rfl⟩ := SbDevSt.dGoodDisk pa (SbDevSt.admGood _ _ _ _ _ _ _ har1 hg)
    exact absurd hre (SbDevSt.noPair dp da l1 pm dm pm2 ws lb l2 hst1)

/-! # 4. `DevStOrd` and the consumer forms -/

theorem SbDevSt.lblOf (G : Gexec) (e : Geid) (l : Lbl) :
    gxLbl G e = some l → ∃ row, G.gxProg[e.1]? = some row ∧ row[e.2]? = some l := by
  unfold gxLbl
  intro h
  rcases hr : G.gxProg[e.1]? with _ | row
  · rw [hr] at h; cases h
  · rw [hr] at h; exact ⟨row, rfl, h⟩

/-- **`DevStOrd` DISCHARGED**: on an xv6-shaped bundle (rows `≥ NCPU` boot as the idle disk), from the
trusted residue, `gfDevWIo` and the named `LockFacts3.diskFabPo`.  A device-row store `f` before a
po-later memory event `m` of its row: `m` I/O — (R1); `m` a write — a fabric member (`rowTq`), so
`diskFabPo`; `m` a read — an I/O event `s` lies between (`rowStRd`, the program text), (R1) then (R2′)
(or (R2″) on a row other than `NCPU`). -/
theorem SbDevSt.devStOrd (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (GF : Gfexec)
    (hconf : GraphFabConf.gfexecConfZF boot d0 fab GF)
    (hdb : ∀ i, NCPU ≤ i → boot i = .PDisk none)
    (hres : ioResidueGmo GF) (hwio : gfDevWIo GF) (hdf : LockFacts3.diskFabPo GF) :
    DevStOrd GF.gfGd.gdG GF.gfDev := by
  intro f m hf hfio hfN hpo hmm
  obtain ⟨hfm1, hfm2, -, -⟩ := hpo
  have hfw : gisW GF.gfGd.gdG f = true := by
    have h := hwio f hf
    unfold gisWIo at h
    rw [hfio, Bool.or_false] at h
    exact h
  obtain ⟨lf, hlf⟩ : ∃ lf, gxLbl GF.gfGd.gdG f = some lf ∧ lbIsW lf = true := by
    unfold gisW at hfw
    rcases h : gxLbl GF.gfGd.gdG f with _ | lf
    · rw [h] at hfw; cases hfw
    · rw [h] at hfw; exact ⟨lf, rfl, hfw⟩
  have hfmem : gmem GF.gfGd.gdG f := ⟨lf, hlf.1, by unfold lbIsMem; rw [hlf.2]; simp⟩
  obtain ⟨lm, hlm, hmem⟩ := hmm
  obtain ⟨row, hrow, hrf⟩ := SbDevSt.lblOf _ f lf hlf.1
  obtain ⟨row', hrow', hrm⟩ := SbDevSt.lblOf _ m lm hlm
  rw [← hfm1, hrow] at hrow'
  cases hrow'
  obtain ⟨em, dvi, dvo, tq, hem, hiff, -, -, -⟩ := hconf.2.2.2 f.1 row hrow
  have hem' : hemitf dvi dvo tq 0 wsInit row (.PDisk none) em.emItems em.emFin := by
    have h : hemitf dvi dvo tq 0 wsInit row (boot f.1) em.emItems em.emFin := hem
    rw [hdb f.1 hfN] at h
    exact h
  have hpo' : WeakRvwmoGraph.gpo GF.gfGd.gdG f m :=
    ⟨hfm1, hfm2, by rw [hlf.1]; rfl, by rw [hlm]; rfl⟩
  by_cases hio : lbIsIo lm = true
  · -- (R1)
    exact hres f m (.inl ⟨hpo', hfmem, hfio, by unfold gisIo; rw [hlm]; exact hio⟩)
  by_cases hw : lbIsW lm = true
  · -- a disk-row write: a fabric member (`rowTq`), ordered by `diskFabPo`
    have htq : tq m.2 = true := by
      have := SbDevSt.rowTq _ _ _ _ _ _ _ _ _ hem' trivial m.2 lm hrm hw
      rw [Nat.zero_add] at this
      exact this
    have hmlt : m.2 < row.length := (List.getElem?_eq_some_iff.1 hrm).1
    have hmd : m ∈ GF.gfDev := by
      have h := (hiff m.2 hmlt).2 (.inr (.inr htq))
      rw [hfm1] at h
      exact h
    have hmio : gisIo GF.gfGd.gdG m = false := by
      unfold gisIo; rw [hlm]; exact Bool.eq_false_iff.2 hio
    exact hdf f m ⟨hf, hfio⟩ ⟨hmd, hmio⟩ hpo'
  · -- a disk-row read: an I/O event between (the program text), (R1) then (R2′)/(R2″)
    have hr : lbIsR lm = true := by
      unfold lbIsMem at hmem
      simp only [Bool.or_eq_true] at hmem
      rcases hmem with (h | h) | h
      · exact h
      · exact absurd h hw
      · exact absurd h hio
    obtain ⟨i, lbi, h1, h2, hri, hiio⟩ :=
      SbDevSt.rowStRd _ _ _ _ _ _ _ _ _ hem' trivial f.2 m.2 lf lm hfm2 hrf hlf.2 hrm hr
    have hsl : gxLbl GF.gfGd.gdG (f.1, i) = some lbi := by
      unfold gxLbl; simp only [hrow, Option.bind_some]; exact hri
    have hsio : gisIo GF.gfGd.gdG (f.1, i) = true := by unfold gisIo; rw [hsl]; exact hiio
    have hfs : gmoLt GF.gfGd.gdG f (f.1, i) :=
      hres f (f.1, i) (.inl ⟨⟨rfl, h1, by rw [hlf.1]; rfl, by rw [hsl]; rfl⟩, hfmem, hfio, hsio⟩)
    by_cases him : i = m.2
    · have hm : (f.1, i) = m := by rw [him, hfm1]
      rw [hm] at hfs
      exact hfs
    have hsm : WeakRvwmoGraph.gpo GF.gfGd.gdG (f.1, i) m :=
      ⟨hfm1, by show i < m.2; omega, by rw [hsl]; rfl, by rw [hlm]; rfl⟩
    have hmr : gisR GF.gfGd.gdG m = true := by unfold gisR; rw [hlm]; exact hr
    refine gmoLtTrans _ _ _ _ hfs (hres _ m ?_)
    by_cases hN : m.1 = NCPU
    · exact .inr (.inr (.inl ⟨hsm, hsio, hmr, hN⟩))
    · exact .inr (.inr (.inr (.inr (.inr ⟨hsm, hsio, hmr⟩))))

/-- xv6's boot (`xboot`): every row `≥ NCPU` is the idle disk. -/
theorem SbDevSt.xbootDisk (σ0 : WGState) : ∀ i, NCPU ≤ i → xboot σ0 i = .PDisk none := by
  intro i hi
  unfold xboot epsInit
  rw [List.getElem?_append_right (by simp [cpus]; omega)]
  simp only [List.length_map, cpus, List.length_finRange]
  rcases Nat.eq_or_lt_of_le hi with h | h
  · subst h; simp
  · rw [List.getElem?_eq_none (by simp; omega)]
    rfl

/-- The class premise `diskFabPo` (NAMED device model, `LockFacts3`). -/
def SbDevSt.diskFabPoCZ (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (im : Image) : Prop :=
  ∀ (GF : Gfexec) (ad : List (Geid × Geid)),
    GF.gfGd.gdG.gxImg = im → CatLin.rvwmoCatAD GF.gfGd ad → GraphFabConf.gfexecConfZF boot d0 fab GF →
    LockFacts3.diskFabPo GF

/-- ... it is part of the existing class premise `CatLin.lockDiscGFCZ`. -/
theorem SbDevSt.diskFabPoCZOfLockDisc (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab)
    (im : Image) (P : Int → Int → Prop) :
    CatLin.lockDiscGFCZ boot d0 fab im P → SbDevSt.diskFabPoCZ boot d0 fab im :=
  fun h GF ad him hc hconf => (h GF ad him hc hconf).2.2.2.2

/-- **`SbKill.walkHypCZ` WITHOUT `DevStOrd`** (the image facts, exempt reads are plain loads, the image
defined at read bytes). -/
def SbDevSt.walkHypCZD (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (im : Image)
    (Xof : Gfexec → Geid → Prop) : Prop :=
  ∀ (GF : Gfexec) (ad : List (Geid × Geid)),
    GF.gfGd.gdG.gxImg = im → CatLin.rvwmoCatAD GF.gfGd ad → GraphFabConf.gfexecConfZF boot d0 fab GF →
    ImgFacts GF.gfGd.gdG ∧
    (∀ e l, Xof GF e → gxLbl GF.gfGd.gdG e = some l → ∃ base ts vs, l = LLoad false base ts vs) ∧
    (∀ e a t v, greadsByte GF.gfGd.gdG e a t v → (im a).isSome)

/-- `walkHypCZ`'s conjunction at every class graph that satisfies the trusted residue (the form the
walk consumes: `certSupplyOfWalkP` opens `walkHypCZ` only after `ioResidueGmo`). -/
theorem SbDevSt.walkHypAt (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (im : Image)
    (Xof : Gfexec → Geid → Prop) (hdb : ∀ i, NCPU ≤ i → boot i = .PDisk none)
    (hwio : CatLin.gfDevWIoCZ boot d0 fab im) (hdf : SbDevSt.diskFabPoCZ boot d0 fab im)
    (hW : SbDevSt.walkHypCZD boot d0 fab im Xof) :
    ∀ (GF : Gfexec) (ad : List (Geid × Geid)),
      GF.gfGd.gdG.gxImg = im → CatLin.rvwmoCatAD GF.gfGd ad →
      GraphFabConf.gfexecConfZF boot d0 fab GF → ioResidueGmo GF →
      ImgFacts GF.gfGd.gdG ∧ DevStOrd GF.gfGd.gdG GF.gfDev ∧
      (∀ e l, Xof GF e → gxLbl GF.gfGd.gdG e = some l → ∃ base ts vs, l = LLoad false base ts vs) ∧
      (∀ e a t v, greadsByte GF.gfGd.gdG e a t v → (im a).isSome) := by
  intro GF ad him hc hconf hres
  obtain ⟨hI, hex, hdef⟩ := hW GF ad him hc hconf
  exact ⟨hI, SbDevSt.devStOrd boot d0 fab GF hconf hdb hres (hwio GF ad him hc hconf)
    (hdf GF ad him hc hconf), hex, hdef⟩

/-- **THE SUPPLY FROM THE GATED WALK, `DevStOrd` discharged** (`SbKill.certSupplyOfWalkP` with
`walkHypCZD` + the disk boot shape + `diskFabPoCZ`). -/
theorem SbDevSt.certSupplyOfWalkPD (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (im : Image)
    (Xof : Gfexec → Geid → Prop)
    (hbt : ∀ i, i < NCPU → GraphFabConf.isHart (boot i) = true)
    (hdb : ∀ i, NCPU ≤ i → boot i = .PDisk none)
    (hwio : CatLin.gfDevWIoCZ boot d0 fab im) (hdf : SbDevSt.diskFabPoCZ boot d0 fab im)
    (hW : SbDevSt.walkHypCZD boot d0 fab im Xof) (hS : SbKill.stateIfcCZ boot d0 fab im Xof) :
    SbKill.certSupplyP boot d0 fab im Xof := by
  intro GF ad him hc hconf hres
  obtain ⟨hI, hDS, hex, hdef⟩ :=
    SbDevSt.walkHypAt boot d0 fab im Xof hdb hwio hdf hW GF ad him hc hconf hres
  have hWH : WalkHyp GF GF.gfGd.gdG.gxProg.length im (Xof GF) :=
    { cat := ⟨hc.1, hc.2.1, hc.2.2.1, hc.2.2.2.1⟩
      io := hres
      wio := hwio GF ad him hc hconf
      imgF := hI
      devSt := hDS
      hart := LockFacts3.hartDevIo boot d0 fab GF hconf hbt
      len := rfl
      imgEq := him
      ex := hex
      def' := hdef }
  obtain ⟨c, hcimg, hv, hdr, hgwf, hlog, hlat, hagX, -⟩ :=
    memberOfCat GF _ im (Xof GF) valGate hWH (fun c hv hg hci hP =>
      let h := hS GF ad him hc hconf hres c hv hg hci hP
      let h' := valIfc GF _ im (Xof GF) hWH c hv hP
      ⟨h.1, h.2, h'.1, h'.2⟩)
  exact ⟨c, hcimg.trans him.symm, hv, hdr, hgwf, hlog, hlat, hagX⟩

/-- **… the kill** (`SbKill.cycleKillOfWalkP` with `DevStOrd` discharged). -/
theorem SbDevSt.cycleKillOfWalkPD (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (im : Image)
    (Xof : Gfexec → Geid → Prop) (P : Int → Int → Prop) (Bad : Prop)
    (hbt : ∀ i, i < NCPU → GraphFabConf.isHart (boot i) = true)
    (hdb : ∀ i, NCPU ≤ i → boot i = .PDisk none)
    (hwio : CatLin.gfDevWIoCZ boot d0 fab im) (hdf : SbDevSt.diskFabPoCZ boot d0 fab im)
    (hW : SbDevSt.walkHypCZD boot d0 fab im Xof) (hS : SbKill.stateIfcCZ boot d0 fab im Xof)
    (hM : SbKill.memberRunCZ boot d0 fab im Xof P)
    (hl2 : SbKill.l2ClaimP boot d0 fab im Xof P Bad) (hnB : ¬ Bad) :
    CatLin.cycleKillCZT boot d0 fab im :=
  SbKill.cycleKillCoreP boot d0 fab im Xof P Bad
    (SbDevSt.certSupplyOfWalkPD boot d0 fab im Xof hbt hdb hwio hdf hW hS) hM hl2 hnB

/-- **THE SHAPE `CapFetchProv.t2linSupplyCZTtagged` CONSUMES**, `DevStOrd` discharged
(`SbKill.cycleKillAllP` with `walkHypCZD`, the disk boot shape and `diskFabPoCZ`). -/
theorem SbDevSt.cycleKillAllPD (boot : Nat → Pexv6) (d0 : Efab) (im : Image)
    (Xof : Gfexec → Geid → Prop) (P : Int → Int → Prop) (Bad : Prop)
    (hbt : ∀ i, i < NCPU → GraphFabConf.isHart (boot i) = true)
    (hdb : ∀ i, NCPU ≤ i → boot i = .PDisk none)
    (hwio : ∀ fab, CatLin.gfDevWIoCZ boot d0 fab im) (hdf : ∀ fab, SbDevSt.diskFabPoCZ boot d0 fab im)
    (hW : ∀ fab, SbDevSt.walkHypCZD boot d0 fab im Xof) (hS : ∀ fab, SbKill.stateIfcCZ boot d0 fab im Xof)
    (hM : ∀ fab, SbKill.memberRunCZ boot d0 fab im Xof P)
    (hl2 : ∀ fab, SbKill.l2ClaimP boot d0 fab im Xof P Bad) (hnB : ¬ Bad) :
    ∀ fab, CatLin.cycleKillCZT boot d0 fab im :=
  fun fab => SbDevSt.cycleKillOfWalkPD boot d0 fab im Xof P Bad hbt hdb (hwio fab) (hdf fab) (hW fab)
    (hS fab) (hM fab) (hl2 fab) hnB

end Weak
