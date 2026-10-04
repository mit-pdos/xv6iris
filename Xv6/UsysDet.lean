/-
**The functional rows** (NI M0 / M2-W3, grown by M2-G1d; design of record
`claude-notes/projects/noninterference.md` §2, §4 third bullet, §6 "M0",
"M2 as designed for the Lean tree" and "M2-G1 design (2026-10-03)" §3): the
kernel's round on a process's trap as a FUNCTION of the trapped key and the
event-history prefix the ledgers hand back, for the syscalls whose row CAN
be made one today.

* §1 `UIota`, one round's ι-prefix: the four ledgers' histories at the round
  (the allocator's `Kev` list, the pid ledger's `Pev` list, the zombie /
  FAMILY ledger's `Zev` list), the tick ledger's count and (G1d) the round's
  actor, the caller's slot address, with the readings the rows are
  functional in (`poolEmpty`, `nextOf`, `statusOf`/`zombiesOf`, the count,
  `zLowest` at the actor).  These are the ledgers' contents and the caller's
  own placement, never another process's outcome.
* §2 THE PRIVATE CLASS and `usysDet n W ι`: exit (no resume), getpid (the
  key's own pid), uptime (the tick count of `ι`) and (G1d) wait (the family
  ledger's lowest zombie child of the caller, `zLowest ι.zev ι.act`, through
  the key's STATUS WINDOW `uwaitWin`, NI M2-G1e).  The class is
  KEY-DEPENDENT at wait (`usysDetClassAt`, rulings G1-R4 and G1e-R1): a wait
  is in it at a NULL status pointer or with the key's LAZY BIT OFF
  (deviation 5).  Every other number stays
  RELATIONAL (`UsysMemOk.usysMemOk` and its siblings); §4 below says why
  each of §4's other candidates is out.
* §3 THE FUNCTIONAL ROW REFINES THE LANDED RELATION (`usysDet_mem` and
  `usysDet_rows`: nothing above changes meaning), and conversely the landed
  relation at a class number is ONLY the functional row (`usysDet_of_rows`):
  the arm's ∀ ranges over exactly `usysDet`'s image.
* §4 the rows found NOT functional, as a record (no definitions).

PURE.  The trap loop's discharge (`uexecRet_roundDet`) and the engine's arm
read as the policy (`uexecRetContF_det`) are in `UexecApply`.

## §4 The rows found NOT functional in (key, ι-prefix), and what they depend on

* **sbrk (12).**  (a) `SpecSysSbrk.sysSbrkOk`'s failure disjunct
  (`r = -1 ∧ V' = V ∧ M' = M`) is UNCONDITIONAL on every path: the spec
  licenses a spurious -1 even on the lazy grow and the shrink, whose real
  outcome is a function of the key alone (the lazy grow fails iff it
  overruns the user region; the shrink never fails).  Closing that is a
  `SpecSysSbrk` move.  (b) The EAGER grow runs `uvmalloc`'s loop of
  `kalloc`s -- one per data page AND one per missing page-table page, and
  which interior table pages are missing is a fact of the process's PAGE
  TABLE (what earlier, since-shrunk breaks left behind), which the key
  deliberately does not carry; the kallocs interleave with every other
  actor's under `kmem`, so no single ledger snapshot decides the outcome
  (it is a function of the positions of this round's `Kev`s in the whole
  history).  (c) The receipts are not there: L3b's call sites drop
  `kallocPostLed`'s receipt, and neither `growprocOk` nor `sysSbrkOk` carries
  one.
* **fork (1), the parent's answer.**  The pid allocproc picks is the first
  free pid at or after the `nextpid` cell; the pid ledger as landed ties
  only the LIVE SET (`PidLock.pidLedger`, ruling R2(a)): neither the counter
  tie (R2(b), `v = nextOf h`) nor first-ness (R2(c)) is stated, so the pid is
  not a function of the history -- only "the pid of this round's `PAlloc`"
  (G2).  The -1 arm depends on proc-SLOT exhaustion (G1 design §6, parked
  behind G3: allocproc's scan is a window, not a snapshot) and on the
  kallocs of allocproc (trapframe page, the table's pages) and uvmcopy (one
  per page plus the child's table pages; G3); and `SpecKfork`/`SpecSysFork`
  carry no receipt.
* **wait (3): RE-ADMITTED BY G1** (the family ledger, G1a-c).  W3 found the
  slot-placement channel: kwait reaps the zombie child in the LOWEST PROC
  SLOT.  G1 records the placement where the family sees it (kfork's parent
  store appends `ZFork act j pid g` under `wait_lock`), so the reap is
  `zLowest` of the family ledger at the caller's slot, and kwait's led
  answer carries that reading at the reap's receipt (G1c).  The row
  (`usysDetWait`): `zLowest ι.zev ι.act = some (j, pid, xs, γ)` reaps at a
  whole status window (`uwaitWin W.perm a0 = 4`: a null pointer, or the
  four status bytes writable in the key's `π`) -- the answer `pid`
  sign-extended, the status's bytes at the a0 pointer (none at null), `γ`
  out of the children set; at a window broken at byte `d < 4` (NI M2-G1e)
  it answers `-1` with the first `d` status bytes written and NOTHING reaped
  (xv6's copyout copies page by page, each after its `PTE_W` check);
  otherwise `-1` with nothing moved (no children: `¬ zHasKids` makes
  `zLowest` `none`; children of which none is a zombie: unreachable on a
  resumed round, kwait sleeps).  The kernel's led answer carries it (NI
  M2-G1e): kwait calls the reasoned `COPYOUT.wp_copyout`, its copyout
  reason carries the zombie found and the copied window, and at `lazy =
  false` the window IS the key's (`VmfaultQuiet.lazyFree_wmapped_iff`, G1c's
  F4; `SyscallArmsWait.syscArmWait_win`).  What stays NON-FUNCTIONAL in
  wait:
  - **the status copyout at a non-null pointer of a lazy process**
    (deviation 5): a lazily absent page faults through `vmfault → kalloc`
    (the allocator's position, G3's).
  - **the kill arm**: dead at the boundary (G1c's F3): usertrap's
    post-syscall `killed` read is the reading form, so a round whose `-1`
    came from `killShot` never resumes (`UsertrapParts.ut_kill_lend`,
    `usertrap_a6_after`); the pure row (`SyscRows.wait`) carries `-1`
    without its reason.
* **console write (16), the QUIET row.**  The trap contract has no write
  row at all (`usysMemOk`'s identity branch, `r` free); the kernel's answer
  lives in the armed post (`SpecFilewrite.writeConsArms`), and its short
  count is EXISTENTIAL (`SpecConsolewrite.writeConsShort`: SOME byte at or
  after the count, inside the 32-byte chunk the break fired in, is not
  read-mapped) and read off the PAGE TABLE `P`, not the key's `π` (a lazy
  page that was never touched is live in `π` and unmapped in `P`; copyin
  does not fault it in).  The fd's kind (inode / pipe / device) selects the
  arm too.  Making it functional needs `SpecConsolewrite` to pin the first
  unreadable byte and a lazy-free premise.

## Deviations from Rocq

1. **M0 as designed for Lean; Rocq never landed it** (NI-DET-ROWS stayed
   open on the `rocq` branch).  Nothing here is a port.
2. **The class is {exit, getpid, uptime, wait at a null status pointer or
   a lazy-free key}** (NI M2-G1e),
   not §4's whole list: §4 above.
3. **`round_det` concludes the KEY equality `ukeyEq`**, not `W' = usysDet …`
   on the nose: the round relation pins the resume trapframe through its
   restored file and pc only (`uroundBumpOk`), and the four kernel words
   differ -- `ukeyEq` is exactly what a slot sees (`UexecApply.UKeyCong`).
4. **ι for uptime is the receipt's COUNT, for wait the receipt's family
   history and the caller's slot** (`SyscRows.uptime` / `SyscRows.wait`);
   `SyscRows` is pure, so the receipts themselves (`tickLb n`,
   `zombReceipt h (ZReap act j rv)`) stop at the kernel's arms, and "∃ ι" is
   only as strong as `usysDet`'s dependence on ι (G1 design F6).  (NI M2-X2)
   The ι export now anchors it: the arms keep the receipts as the cited
   prefixes' lower bounds (`NiEvid.niIotaLbs`, `SpecSyscall.syscEvOut`),
   and the filing proves the row at the CITED ι (`usysIotaFits_of_ev`:
   the re-keyed `SyscallDefs.syscEvRow` IS the fit; `UserretClosedRows.
   urc_niDetRow`).  W4 reads both answers as READINGS (O5, G1-R5) until X4.
5. **The class at wait is `a0 = 0 ∨ lazy = false`** (G1-R4 as designed,
   narrowed by G1d to `a0 = 0` and re-admitted by NI M2-G1e, ruling
   G1e-R1): the class predicate takes the a0 WORD and the key's LAZY BIT
   (`usysDetClassAt n a0 lz`); the trace (`NiTrace.NiInClass`) reads the a0
   word off the exit's registers and the lazy bit off the step (a ghost-key
   reading the filing carries, as `secc`).  The design's first test ("a
   non-writable status word at `lazy = false` → -1, nothing moved") is not
   xv6's: with a zombie child the status is copied up to the first
   non-writable byte (`uwaitWin`, ruling G1e-R2) and the child is NOT
   reaped; `usysDetWait`'s middle arm.
-/
import Xv6.UexecRound

namespace Xv6

open Std Iris

/-! ## §1 The event history as the engine sees it -/

/-- **One round's ι-prefix**: what the four ledgers say at the round -- the
allocator's history, the pid ledger's, the family ledger's, and the tick
ledger's count -- and (G1d) the round's actor.  Public, actor-labelled, and
never another process's data. -/
structure UIota where
  /-- the allocator's ledger (`KallocDefs.ledLb`'s list) -/
  kev : List Kev
  /-- the pid ledger (`SlotGen.pidLedLb`'s list) -/
  pev : List Pev
  /-- the zombie / family ledger (`UserChildren.zombLedLb`'s list) -/
  zev : List Zev
  /-- the tick ledger's count (`WaitInv.tickLb`'s bound, at the read) -/
  ticks : Nat
  /-- the round's actor: the caller's slot address (`procAddr j`; NI G1d,
  the family ledger's readings are at it) -- the caller's own placement -/
  act : BitVec 64

/-- The empty prefix (the boot's). -/
def UIota.boot : UIota := ⟨[], [], [], 0, 0#64⟩

instance : Inhabited UIota := ⟨UIota.boot⟩

/-- The allocator's reading: the pool is empty after the prefix. -/
def UIota.poolEmpty (ι : UIota) : Prop := Xv6.poolEmpty ι.kev

/-- The pid ledger's reading: the counter the history computes. -/
def UIota.nextPid (ι : UIota) : Nat := nextOf PIDMAX ι.pev

/-- The zombie ledger's readings: the zombie set and the readable statuses. -/
def UIota.zombies (ι : UIota) : Int → Prop := zombiesOf ι.zev
def UIota.status (ι : UIota) : Int → Option Int := statusOf ι.zev

/-- **The family ledger's reading at the actor** (NI G1d): the lowest zombie
child of the caller's slot -- its slot, pid, status and generation. -/
def UIota.reap (ι : UIota) : Option (Nat × BitVec 32 × Int × GName) := zLowest ι.zev ι.act

/-- The empty family history names no zombie. -/
theorem zLowest_nil (a : BitVec 64) : zLowest [] a = none := by
  cases h : zLowest [] a with
  | none => rfl
  | some v =>
    obtain ⟨i, pid, xs, g⟩ := v
    have := ((zLowest_spec _ _ _ _ _ _).1 h).2.2.1
    simp [famOf_nil, ZSlot.empty] at this

/-! ## §2 The class and the function -/

/-- The members whose round moves NOTHING but `a0` (getpid, uptime). -/
def usysDetQuiet (n : Int) : Prop := n = USYS_getpid ∨ n = USYS_uptime

instance (n : Int) : Decidable (usysDetQuiet n) := by unfold usysDetQuiet; infer_instance

/-- The class members that RESUME (exit does not): the quiet two and (NI
G1d) wait. -/
def usysDetResumes (n : Int) : Prop := usysDetQuiet n ∨ n = USYS_wait

instance (n : Int) : Decidable (usysDetResumes n) := by unfold usysDetResumes; infer_instance

/-- **THE PRIVATE CLASS**, as numbers: the numbers whose round is a function
of `(key, ι)` at SOME key (wait's at a null status pointer or a lazy-free
process only: `usysDetClassAt`). -/
def usysDetClass (n : Int) : Prop := n = USYS_exit ∨ n = USYS_getpid ∨ n = USYS_uptime ∨ n = USYS_wait

instance (n : Int) : Decidable (usysDetClass n) := by unfold usysDetClass; infer_instance

/-- **THE PRIVATE CLASS AT A KEY** (NI G1d, ruling G1-R4: key-dependent at
wait; NI M2-G1e, ruling G1e-R1): the number is in the class and, at wait,
the status pointer -- the trapped key's argument word 0 -- is null, or the
key's lazy bit `lz` is off (no lazily absent page: the status copyout's
outcome is the key's `uwaitWin`). -/
def usysDetClassAt (n : Int) (a0 : BitVec 64) (lz : Bool) : Prop :=
  usysDetClass n ∧ (n = USYS_wait → a0 = 0#64 ∨ lz = false)

instance (n : Int) (a0 : BitVec 64) (lz : Bool) : Decidable (usysDetClassAt n a0 lz) := by
  unfold usysDetClassAt; infer_instance

theorem usysDetClass_resumes {n : Int} (h : usysDetClass n) (hx : n ≠ USYS_exit) : usysDetResumes n := by
  rcases h with h | h | h | h
  · exact absurd h hx
  · exact Or.inl (Or.inl h)
  · exact Or.inl (Or.inr h)
  · exact Or.inr h

theorem usysDetQuiet_resumes {n : Int} (h : usysDetQuiet n) : usysDetResumes n := Or.inl h

theorem usysDetQuiet_wait {n : Int} (h : usysDetQuiet n) : n ≠ USYS_wait := by
  rcases h with rfl | rfl <;> decide

/-- **Writable per the key's permission view** (NI M2-G1e): the page of
`va` is mapped in the key's `π` with `W`. -/
def πWritable (perm : Nat → Option UPerm) (va : Nat) : Prop :=
  ∃ q : UPerm, perm (va / 4096) = some q ∧ q.W = true

theorem πWritable_iff (perm : Nat → Option UPerm) (va : Nat) :
    πWritable perm va ↔ (perm (va / 4096)).any (fun q => q.W) = true := by
  unfold πWritable
  cases perm (va / 4096) <;> simp

instance (perm : Nat → Option UPerm) (va : Nat) : Decidable (πWritable perm va) :=
  decidable_of_iff _ (πWritable_iff perm va).symm

/-- **wait's STATUS WINDOW at the key** (NI M2-G1e, ruling G1e-R2): the
first offset `i < 4` whose byte `a0 + i` the key's `π` does not let the
process write, or `4` when all four are writable -- and `4` at a null
pointer (nothing to copy).  It is read off the caller's OWN mapping of its
own buffer: public to the process, like `secc` and `lazy`. -/
def uwaitWin (perm : Nat → Option UPerm) (a0 : BitVec 64) : Nat :=
  if a0 = 0#64 then 4
  else if ¬ πWritable perm (a0 + BitVec.ofNat 64 0).toNat then 0
  else if ¬ πWritable perm (a0 + BitVec.ofNat 64 1).toNat then 1
  else if ¬ πWritable perm (a0 + BitVec.ofNat 64 2).toNat then 2
  else if ¬ πWritable perm (a0 + BitVec.ofNat 64 3).toNat then 3
  else 4

/-- The window IS the first non-writable byte (or `4`). -/
theorem uwaitWin_eq {perm : Nat → Option UPerm} {a0 : BitVec 64} {d : Nat} (h0 : a0 ≠ 0#64)
    (hd : d ≤ 4) (hpre : ∀ i, i < d → πWritable perm (a0 + BitVec.ofNat 64 i).toNat)
    (hstop : d < 4 → ¬ πWritable perm (a0 + BitVec.ofNat 64 d).toNat) : uwaitWin perm a0 = d := by
  unfold uwaitWin
  rw [if_neg h0]
  have w : ∀ i, i < d → ¬ ¬ πWritable perm (a0 + BitVec.ofNat 64 i).toNat :=
    fun i hi h => h (hpre i hi)
  rcases (show d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 4 by omega) with rfl | rfl | rfl | rfl | rfl
  · rw [if_pos (hstop (by decide))]
  · rw [if_neg (w 0 (by decide)), if_pos (hstop (by decide))]
  · rw [if_neg (w 0 (by decide)), if_neg (w 1 (by decide)), if_pos (hstop (by decide))]
  · rw [if_neg (w 0 (by decide)), if_neg (w 1 (by decide)), if_neg (w 2 (by decide)),
      if_pos (hstop (by decide))]
  · rw [if_neg (w 0 (by decide)), if_neg (w 1 (by decide)), if_neg (w 2 (by decide)),
      if_neg (w 3 (by decide))]

theorem uwaitWin_null (perm : Nat → Option UPerm) : uwaitWin perm 0#64 = 4 := by
  unfold uwaitWin; rw [if_pos rfl]

/-- **wait's answer at a cited prefix and a window** (M2-X; NI M2-G1e,
ruling G1e-R2): the family ledger's lowest zombie child of the cited actor,
its pid sign-extended -- when the status window is whole (`4`) --, or `-1`:
no zombie child, or the status copyout stopped at byte `win < 4` (the child
is not reaped). -/
def usysWaitAns (ι : UIota) (win : Nat) : BitVec 64 :=
  match ι.reap with
  | some (_, pid, _, _) => if win = 4 then BitVec.signExtend 64 pid else -1#64
  | none => -1#64

/-- **The answer**: getpid the key's own pid (sign-extended, `c.lw`), uptime
the tick count of `ι` (`usysUptimeWord`), wait (NI G1d; NI M2-G1e) the
reaped child's pid sign-extended at a whole status window, or `-1`
(`usysWaitAns` at the key's window). -/
def usysDetRet (n : Int) (W : Uvis) (ι : UIota) : BitVec 64 :=
  if n = USYS_wait then usysWaitAns ι (uwaitWin W.perm (tfW W.tf (tfArgIdx 0)))
  else if n = USYS_uptime then usysUptimeWord ι.ticks else BitVec.signExtend 64 W.pid

/-- **wait's functional row** (NI G1d; G1 design §3; NI M2-G1e): at the
family ledger's lowest zombie child `(j, pid, xs, γ)` of the caller's slot,

  * at a whole status window (`uwaitWin W.perm a0 = 4`: a null pointer, or
    all four status bytes writable), the REAP -- the answer `pid`, the
    status's bytes at the a0 pointer (none at null), `γ` out of the
    children set;
  * at a window stopped at byte `d < 4` (xv6's copyout: each page copied
    only after its `PTE_W` check), `-1` with the first `d` status bytes
    written and NOTHING reaped (the child stays a zombie, `ch` kept);

with no zombie child, `-1` and nothing moved (the design's "no children"
arm: `¬ zHasKids` gives `none`; its "children, none a zombie" default is
the same key, never cited: kwait sleeps). -/
def usysDetWait (W : Uvis) (ι : UIota) : Uvis :=
  match ι.reap with
  | some (_, pid, xs, γ) =>
    if uwaitWin W.perm (tfW W.tf (tfArgIdx 0)) = 4 then
      bump W (BitVec.signExtend 64 pid)
        (usysWr W.M (tfW W.tf (tfArgIdx 0)) (usysWaitBytes (tfW W.tf (tfArgIdx 0)) xs)) W.perm W.sz W.fd
        W.cwd W.gen (W.ch \ {γ}) W.lazy W.secc
    else
      bump W (-1#64)
        (usysWr W.M (tfW W.tf (tfArgIdx 0))
          ((usysWaitBytes (tfW W.tf (tfArgIdx 0)) xs).take (uwaitWin W.perm (tfW W.tf (tfArgIdx 0)))))
        W.perm W.sz W.fd W.cwd W.gen W.ch W.lazy W.secc
  | none => bump W (-1#64) W.M W.perm W.sz W.fd W.cwd W.gen W.ch W.lazy W.secc

/-- **`usysDet n W ι`**: the key the round resumes the process at -- for the
quiet members the bumped key at `usysDetRet n W ι` with every other reading
kept, for wait `usysDetWait`; `W` itself elsewhere (exit never resumes,
`uroundOk_exit`; outside the class the value is unused). -/
def usysDet (n : Int) (W : Uvis) (ι : UIota) : Uvis :=
  if n = USYS_wait then usysDetWait W ι
  else if usysDetQuiet n then
    bump W (usysDetRet n W ι) W.M W.perm W.sz W.fd W.cwd W.gen W.ch W.lazy W.secc
  else W

theorem usysDet_quiet {n : Int} (W : Uvis) (ι : UIota) (h : usysDetQuiet n) :
    usysDet n W ι = bump W (usysDetRet n W ι) W.M W.perm W.sz W.fd W.cwd W.gen W.ch W.lazy W.secc := by
  unfold usysDet; rw [if_neg (usysDetQuiet_wait h), if_pos h]

theorem usysDet_wait (W : Uvis) (ι : UIota) : usysDet USYS_wait W ι = usysDetWait W ι := by
  unfold usysDet; rw [if_pos rfl]

theorem usysDetRet_getpid (W : Uvis) (ι : UIota) :
    usysDetRet USYS_getpid W ι = BitVec.signExtend 64 W.pid := by
  unfold usysDetRet; rw [if_neg (by decide), if_neg (by decide)]

theorem usysDetRet_uptime (W : Uvis) (ι : UIota) :
    usysDetRet USYS_uptime W ι = usysUptimeWord ι.ticks := by
  unfold usysDetRet; rw [if_neg (by decide), if_pos rfl]

/-- **wait's fit, at the key's readings** (NI G1d; NI M2-G1e): the answer
`r`, the children set `cs'` and the image `M'` are the ones the family
ledger's reading at `ι` names, at the key's permission view `perm`, status
pointer `a0`, children `ch` and image `M` -- the reap at a whole status
window, `-1` with the window's prefix written and nothing reaped at a
broken one, `-1` with nothing moved with no zombie child.  Stated on the
readings so the kernel's cited row (`SyscallDefs.syscEvRow`, at the
dispatch's record) and the key's (`usysWaitFits`) are one text. -/
def usysWaitFitsAt (perm : Nat → Option UPerm) (a0 : BitVec 64) (ch : Std.ExtTreeSet GName compare)
    (M : ElfMem) (ι : UIota) (r : BitVec 64) (cs' : Std.ExtTreeSet GName compare) (M' : ElfMem) : Prop :=
  match ι.reap with
  | some (_, pid, xs, γ) =>
    if uwaitWin perm a0 = 4 then
      r = BitVec.signExtend 64 pid ∧ cs' = ch \ {γ} ∧ M' = usysWr M a0 (usysWaitBytes a0 xs)
    else r = -1#64 ∧ cs' = ch ∧ M' = usysWr M a0 ((usysWaitBytes a0 xs).take (uwaitWin perm a0))
  | none => r = -1#64 ∧ cs' = ch ∧ M' = M

/-- **wait's fit** at the key `W`. -/
def usysWaitFits (W : Uvis) (ι : UIota) (r : BitVec 64) (cs' : Std.ExtTreeSet GName compare) (M' : ElfMem) :
    Prop :=
  usysWaitFitsAt W.perm (tfW W.tf (tfArgIdx 0)) W.ch W.M ι r cs' M'

/-- **The receipt-derived fact a round carries** (the ι-prefix fits the
answer): at uptime the answer is the count `ι` names; at wait (NI G1d; NI
M2-G1e) the answer, the children set and the image are the family ledger's
reading at `ι`'s actor through the key's status window; no other class
member reads `ι`. -/
def usysIotaFits (n : Int) (W : Uvis) (r : BitVec 64) (cs' : Std.ExtTreeSet GName compare) (M' : ElfMem)
    (ι : UIota) : Prop :=
  (n = USYS_uptime → r = usysUptimeWord ι.ticks) ∧ (n = USYS_wait → usysWaitFits W ι r cs' M')

/-- Every answer the rows allow at a number other than wait has a prefix it
fits: uptime's the row's count (NI M2-G1e: wait's fit pins the image, which
the relational row does not, so wait is not served here -- its prefix is the
CITED one, `usysIotaFits_of_ev`). -/
theorem usysIotaFits_exists {n : Int} {W : Uvis} {r : BitVec 64} {cs' : Std.ExtTreeSet GName compare}
    {M' : ElfMem} (hup : n = USYS_uptime → usysUptimeRet r) (hwt : n ≠ USYS_wait) :
    ∃ ι : UIota, usysIotaFits n W r cs' M' ι := by
  by_cases hu : n = USYS_uptime
  · obtain ⟨t, ht⟩ := hup hu
    exact ⟨{ UIota.boot with ticks := t }, fun _ => ht, fun h => absurd h hwt⟩
  · exact ⟨UIota.boot, fun h => absurd h hu, fun h => absurd h hwt⟩

/-- **The cited row IS the fit** (NI M2-X2; NI M2-G1e): what the kernel's
arm cited at `ι` (`SyscallDefs.syscEvRow`, read at the keys -- uptime's
answer the word of `ι`'s count; wait's, at a class key (a null status
pointer or a lazy-free process), `usysWaitFitsAt` at the key's readings) is
`usysIotaFits` at `ι`, at a class member at the key (`hcls`). -/
theorem usysIotaFits_of_ev {n : Int} {W : Uvis} {r : BitVec 64} {cs' : Std.ExtTreeSet GName compare}
    {M' : ElfMem} {ι : UIota} (hcls : n = USYS_wait → tfW W.tf (tfArgIdx 0) = 0#64 ∨ W.lazy = false)
    (hup : n = USYS_uptime → r = usysUptimeWord ι.ticks)
    (hw : n = USYS_wait → (tfW W.tf (tfArgIdx 0) = 0#64 ∨ W.lazy = false) → usysWaitFits W ι r cs' M') :
    usysIotaFits n W r cs' M' ι :=
  ⟨hup, fun hn => hw hn (hcls hn)⟩

/-! ## §3 The functional row refines the relation, and the relation at the
class IS the functional row -/

theorem usysDetQuiet_ne {n : Int} (h : usysDetQuiet n) :
    n ≠ USYS_exec ∧ n ≠ USYS_sbrk ∧ n ≠ USYS_wait ∧ n ≠ USYS_pipe ∧ n ≠ USYS_read ∧
      n ≠ USYS_fstat ∧ n ≠ USYS_fork ∧ n ≠ USYS_exit ∧ n ≠ USYS_close ∧ n ≠ USYS_dup ∧
      n ≠ USYS_open ∧ n ≠ USYS_chdir ∧ n ≠ USYS_seccomp := by
  rcases h with rfl | rfl <;> decide

theorem usysDetResumes_ne {n : Int} (h : usysDetResumes n) :
    n ≠ USYS_exec ∧ n ≠ USYS_sbrk ∧ n ≠ USYS_pipe ∧ n ≠ USYS_read ∧
      n ≠ USYS_fstat ∧ n ≠ USYS_fork ∧ n ≠ USYS_exit ∧ n ≠ USYS_close ∧ n ≠ USYS_dup ∧
      n ≠ USYS_open ∧ n ≠ USYS_chdir ∧ n ≠ USYS_seccomp := by
  rcases h with (rfl | rfl) | rfl <;> decide

/-- **`usysDet_mem`**: the functional row satisfies the landed image table
at its own answer -- `usysMemOk` at `usysDet`'s image, map, break and lazy
bit; at wait (NI G1d) given that the answer has wait's shape (`hwr`: a
history whose zombie pids are in range). -/
theorem usysDet_mem {n : Int} (W : Uvis) (ι : UIota) (h : usysDetResumes n)
    (hwr : n = USYS_wait → usysWaitRet (usysDetRet n W ι)) :
    usysMemOk n W.tf (usysDetRet n W ι) W.M W.perm W.sz W.lazy (usysDet n W ι).M (usysDet n W ι).perm
      (usysDet n W ι).sz (usysDet n W ι).lazy := by
  rcases h with hq | rfl
  · rw [usysDet_quiet W ι hq]
    obtain ⟨h7, h12, h3, h4, h5, h8, hf, -⟩ := usysDetQuiet_ne hq
    unfold usysMemOk
    rw [if_neg h7, if_neg h12, if_neg h3, if_neg h4, if_neg h5, if_neg h8, if_neg hf]
    rcases hq with rfl | rfl
    · rw [if_neg (by decide)]; exact ⟨rfl, rfl, rfl, rfl⟩
    · rw [if_pos rfl, usysDetRet_uptime]; exact ⟨⟨ι.ticks, rfl⟩, rfl, rfl, rfl, rfl⟩
  · have hw := hwr rfl
    rw [usysDet_wait]
    unfold usysMemOk
    rw [if_neg (by decide), if_neg (by decide), if_pos rfl]
    unfold usysDetWait
    cases hr : ι.reap with
    | none =>
      exact ⟨⟨[], by simp, fun _ => rfl, rfl⟩, rfl, rfl, rfl, hw⟩
    | some v =>
      obtain ⟨_, pid, xs, γ⟩ := v
      dsimp only
      by_cases hwin : uwaitWin W.perm (tfW W.tf (tfArgIdx 0)) = 4
      · rw [if_pos hwin]
        refine ⟨⟨usysWaitBytes (tfW W.tf (tfArgIdx 0)) xs, usysWaitBytes_length _ _, fun h0 => ?_, rfl⟩,
          rfl, rfl, rfl, hw⟩
        rw [show tfW W.tf (tfArgIdx 0) = 0#64 from BitVec.eq_of_toNat_eq (by simpa using h0)]
        exact usysWaitBytes_null xs
      · rw [if_neg hwin]
        refine ⟨⟨(usysWaitBytes (tfW W.tf (tfArgIdx 0)) xs).take (uwaitWin W.perm (tfW W.tf (tfArgIdx 0))),
          le_trans (List.length_take_le' _ _) (usysWaitBytes_length _ _), fun h0 => ?_, rfl⟩,
          rfl, rfl, rfl, hw⟩
        rw [show tfW W.tf (tfArgIdx 0) = 0#64 from BitVec.eq_of_toNat_eq (by simpa using h0),
          usysWaitBytes_null, List.take_nil]

/-- **The other rows, at the functional answer**: descriptors, pipe, cwd,
generation, pid, mask and (off wait) children all hold at `usysDet`, and the
answer (with the children set and the image) fits `ι` (the arm's remaining
premises; wait's children move is its own arm's, `uwaitAnsPid`). -/
theorem usysDet_rows {n : Int} (W : Uvis) (ι : UIota) (h : usysDetResumes n) :
    usysFdOk n W.tf (usysDetRet n W ι) W.fd (usysDet n W ι).fd ∧
    usysPipeOk n W.tf (usysDetRet n W ι) W.M (usysDet n W ι).M W.fd (usysDet n W ι).fd ∧
    usysCwdOk n (usysDetRet n W ι) W.cwd (usysDet n W ι).cwd ∧
    usysGenOk n W.gen (usysDet n W ι).gen ∧
    usysRetPid n (usysDetRet n W ι) W.pid ∧
    usysSeccOk n W.tf W.secc (usysDet n W ι).secc (usysDetRet n W ι) ∧
    (n ≠ USYS_wait → usysChOk n (usysDetRet n W ι) W.ch (usysDet n W ι).ch) ∧
    usysIotaFits n W (usysDetRet n W ι) (usysDet n W ι).ch (usysDet n W ι).M ι := by
  obtain ⟨-, -, h4, -, -, -, -, hcl, hdp, hop, hcd, h23⟩ := usysDetResumes_ne h
  have hfd : (usysDet n W ι).fd = W.fd := by
    unfold usysDet usysDetWait; split <;> (repeat' split) <;> rfl
  have hcw : (usysDet n W ι).cwd = W.cwd := by
    unfold usysDet usysDetWait; split <;> (repeat' split) <;> rfl
  have hgn : (usysDet n W ι).gen = W.gen := by
    unfold usysDet usysDetWait; split <;> (repeat' split) <;> rfl
  have hsc : (usysDet n W ι).secc = W.secc := by
    unfold usysDet usysDetWait; split <;> (repeat' split) <;> rfl
  rw [hfd, hcw, hgn, hsc]
  refine ⟨usysFdOk_refl_at n n _ _ _ rfl hcl hdp hop h4, usysPipeOk_quiet _ _ _ _ _ _ _ h4,
    usysCwdOk_refl_at n n _ _ rfl hcd, rfl, ?_, usysSeccOk_refl _ _ _ _ h23, ?_, ?_, ?_⟩
  · rcases h with (rfl | rfl) | rfl
    · exact usysRetPid_of _ _ _ (usysDetRet_getpid W ι)
    · exact usysRetPid_ne _ _ _ (by decide)
    · exact usysRetPid_ne _ _ _ (by decide)
  · intro hw
    rcases h with hq | hq
    · rw [usysDet_quiet W ι hq]; rfl
    · exact absurd hq hw
  · intro hu; subst hu; rw [usysDetRet_uptime]
  · intro hw; subst hw
    rw [usysDet_wait]
    unfold usysWaitFits usysWaitFitsAt usysDetWait usysDetRet usysWaitAns
    rw [if_pos rfl]
    cases ι.reap with
    | none => exact ⟨rfl, rfl, rfl⟩
    | some v =>
      obtain ⟨j, pid, xs, γ⟩ := v
      dsimp only
      by_cases hwin : uwaitWin W.perm (tfW W.tf (tfArgIdx 0)) = 4
      · simp only [hwin, ↓reduceIte] <;> trivial
      · simp only [hwin, ↓reduceIte] <;> trivial

/-- **THE CONVERSE, at the arm** (`round_det`'s pure core): at a resuming
class member, any `(r, M', …)` the landed rows allow, at a prefix the
answer (and at wait the children set and the image: NI M2-G1e) fits, IS
`usysDet`'s -- the bumped key equals the functional one ON THE NOSE.  (The
class condition at wait is the fit's to carry: `usysIotaFits_of_ev`.) -/
theorem usysDet_of_rows {n : Int} (W : Uvis) (ι : UIota) (h : usysDetResumes n) (r : BitVec 64)
    (M' : ElfMem) (π' : Nat → Option UPerm) (szv' : Nat) (fdv' : List FdState) (cw' : Nat)
    (g' : Iris.GName) (cs' : ExtTreeSet Iris.GName compare) (lz' : Bool) (secc' : BitVec 64)
    (hm : usysMemOk n W.tf r W.M W.perm W.sz W.lazy M' π' szv' lz')
    (hfd : usysFdOk n W.tf r W.fd fdv') (hc : usysCwdOk n r W.cwd cw') (hg : usysGenOk n W.gen g')
    (hpid : usysRetPid n r W.pid) (hs : usysSeccOk n W.tf W.secc secc' r) (hch : n ≠ USYS_wait → cs' = W.ch)
    (hfit : usysIotaFits n W r cs' M' ι) :
    r = usysDetRet n W ι ∧ bump W r M' π' szv' fdv' cw' g' cs' lz' secc' = usysDet n W ι := by
  obtain ⟨h7, h12, h4, h5, h8, hf, -, hcl, hdp, hop, hcd, h23⟩ := usysDetResumes_ne h
  have hlz := usysMemOk_lazy h12 hm
  have hfd' := usysFdOk_quiet hcl hdp hop h4 hfd
  have hc' := usysCwdOk_quiet hcd hc
  have hs' := usysSeccOk_quiet h23 hs
  have hg' : g' = W.gen := hg
  rcases h with hq | rfl
  · obtain ⟨-, -, h3, -⟩ := usysDetQuiet_ne hq
    obtain ⟨hM, hp, hsz⟩ := usysMemOk_quiet h7 h12 h3 h4 h5 h8 hm
    have hr : r = usysDetRet n W ι := by
      rcases hq with rfl | rfl
      · rw [usysDetRet_getpid]; exact usysRetPid_getpid hpid
      · rw [usysDetRet_uptime]; exact hfit.1 rfl
    refine ⟨hr, ?_⟩
    rw [usysDet_quiet W ι hq]
    have hch' := hch h3
    subst hM hp hsz hlz hfd' hc' hs' hg' hch' hr
    rfl
  · have hpw : π' = W.perm ∧ szv' = W.sz := by
      unfold usysMemOk at hm
      rw [if_neg (by decide), if_neg (by decide), if_pos rfl] at hm
      exact ⟨hm.2.1, hm.2.2.1⟩
    obtain ⟨hp, hsz⟩ := hpw
    have hf := hfit.2 rfl
    rw [usysDet_wait]
    unfold usysWaitFits usysWaitFitsAt at hf
    unfold usysDetWait usysDetRet usysWaitAns
    rw [if_pos rfl]
    subst hp hsz hlz hfd' hc' hs' hg'
    revert hf
    cases ι.reap with
    | none =>
      intro hf; obtain ⟨hrr, hcc, hM⟩ := hf; subst hrr hcc hM; exact ⟨rfl, rfl⟩
    | some v =>
      obtain ⟨j, pid, xs, γ⟩ := v
      dsimp only
      by_cases hwin : uwaitWin W.perm (tfW W.tf (tfArgIdx 0)) = 4
      · simp only [hwin, ↓reduceIte]
        intro hf; obtain ⟨hrr, hcc, hM⟩ := hf; subst hrr hcc hM; exact ⟨rfl, rfl⟩
      · simp only [hwin, ↓reduceIte]
        intro hf; obtain ⟨hrr, hcc, hM⟩ := hf; subst hrr hcc hM; exact ⟨rfl, rfl⟩

/-- **Exit never resumes**: the round relation has no ecall disjunct at
exit's effective number (the returning one excludes it, exec's is another
number). -/
theorem uroundOk_exit {tf : List (BitVec 64)} {M M' : ElfMem} {π π' : Nat → Option UPerm}
    {szv szv' cw cw' : Nat} {lz lz' : Bool} {secc secc' : BitVec 64} {tf' : List (BitVec 64)}
    (hx : usysEff secc tf = USYS_exit)
    (H : uroundOk uecallScause tf M π szv cw lz secc tf' M' π' szv' cw' lz' secc') : False := by
  rcases uroundOk_ecall H with ⟨he, -⟩ | ⟨hne, -⟩
  · rw [hx] at he; exact absurd he (by decide)
  · exact hne hx

end Xv6
