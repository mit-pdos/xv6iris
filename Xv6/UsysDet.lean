/-
**The functional rows** (NI M0 / M2-W3; design of record
`claude-notes/projects/noninterference.md` §2, §4 third bullet, §6 "M0" and
"M2 as designed for the Lean tree"): the kernel's round on a process's trap
as a FUNCTION of the trapped key and the event-history prefix the ledgers
hand back, for the syscalls whose row CAN be made one today.

* §1 `UIota`, one round's ι-prefix: the four ledgers' histories at the round
  (the allocator's `Kev` list, the pid ledger's `Pev` list, the zombie
  ledger's `Zev` list) and the tick ledger's count, with the readings the
  rows are functional in (`poolEmpty`, `nextOf`, `statusOf`/`zombiesOf`, the
  count).  These are the ledgers' contents, never a process's outcome.
* §2 THE PRIVATE CLASS and `usysDet n W ι`: exit (no resume), getpid (the
  key's own pid) and uptime (the tick count of `ι`).  Every other number
  stays RELATIONAL (`UsysMemOk.usysMemOk` and its siblings); §4 below says
  why each of §4's other candidates is out.
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
  not a function of the history -- only "the pid of this round's `PAlloc`".
  The -1 arm depends on proc-SLOT exhaustion (no ledger records slot
  occupancy) and on the kallocs of allocproc (trapframe page, the table's
  pages) and uvmcopy (one per page plus the child's table pages); and
  `SpecKfork`/`SpecSysFork` carry no receipt.
* **wait (3).**  kwait reaps the zombie child in the LOWEST PROC SLOT; a
  child's slot is allocproc's first UNUSED one, a fact of every process's
  slot usage that NO ledger records (the zombie ledger's D3: nothing under
  the wait lock knows the slots).  So with two zombie children, WHICH pid
  wait answers is a function of global slot placement -- A CHANNEL NOT YET
  NAMED (§2 of the design: proc-slot placement, observable through wait's
  choice).  Besides: the -1 arm also fires on `killed` (kkill, §3's kill
  channel) and on a failed status copyout (a lazy page faulted in by
  `vmfault` runs `kalloc`: the allocator's position), and `SpecKwait`/
  `SpecSysWait` carry no `zombReceipt`.
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
2. **The class is {exit, getpid, uptime}**, not §4's whole list: §4 above.
3. **`round_det` concludes the KEY equality `ukeyEq`**, not `W' = usysDet …`
   on the nose: the round relation pins the resume trapframe through its
   restored file and pc only (`uroundBumpOk`), and the four kernel words
   differ -- `ukeyEq` is exactly what a slot sees (`UexecApply.UKeyCong`).
4. **ι for uptime is the receipt's COUNT**; `SyscRows` is pure, so the
   receipt itself (`tickLb n`) stops at the kernel's arm, which records its
   `n` as the `uptime` row (`usysUptimeRet`).  W4 ties `ι.ticks` to the
   trace.
-/
import Xv6.UexecRound
import Xv6.KallocEv
import Xv6.PidEv
import Xv6.ZombEv

namespace Xv6

open Std

/-! ## §1 The event history as the engine sees it -/

/-- **One round's ι-prefix**: what the four ledgers say at the round -- the
allocator's history, the pid ledger's, the zombie ledger's, and the tick
ledger's count.  Public, actor-labelled, and never a process's data. -/
structure UIota where
  /-- the allocator's ledger (`KallocDefs.ledLb`'s list) -/
  kev : List Kev
  /-- the pid ledger (`SlotGen.pidLedLb`'s list) -/
  pev : List Pev
  /-- the zombie ledger (`UserChildren.zombLedLb`'s list) -/
  zev : List Zev
  /-- the tick ledger's count (`WaitInv.tickLb`'s bound, at the read) -/
  ticks : Nat

/-- The empty prefix (the boot's). -/
def UIota.boot : UIota := ⟨[], [], [], 0⟩

instance : Inhabited UIota := ⟨UIota.boot⟩

/-- The allocator's reading: the pool is empty after the prefix. -/
def UIota.poolEmpty (ι : UIota) : Prop := Xv6.poolEmpty ι.kev

/-- The pid ledger's reading: the counter the history computes. -/
def UIota.nextPid (ι : UIota) : Nat := nextOf PIDMAX ι.pev

/-- The zombie ledger's readings: the zombie set and the readable statuses. -/
def UIota.zombies (ι : UIota) : Int → Prop := zombiesOf ι.zev
def UIota.status (ι : UIota) : Int → Option Int := statusOf ι.zev

/-! ## §2 The class and the function -/

/-- **THE PRIVATE CLASS**: the numbers whose round is a function of
`(key, ι)` today. -/
def usysDetClass (n : Int) : Prop := n = USYS_exit ∨ n = USYS_getpid ∨ n = USYS_uptime

instance (n : Int) : Decidable (usysDetClass n) := by unfold usysDetClass; infer_instance

/-- The class members that RESUME (exit does not). -/
def usysDetResumes (n : Int) : Prop := n = USYS_getpid ∨ n = USYS_uptime

instance (n : Int) : Decidable (usysDetResumes n) := by unfold usysDetResumes; infer_instance

theorem usysDetClass_resumes {n : Int} (h : usysDetClass n) (hx : n ≠ USYS_exit) : usysDetResumes n := by
  rcases h with h | h | h
  · exact absurd h hx
  · exact Or.inl h
  · exact Or.inr h

/-- **The answer**: getpid the key's own pid (sign-extended, `c.lw`), uptime
the tick count of `ι` (`usysUptimeWord`). -/
def usysDetRet (n : Int) (W : Uvis) (ι : UIota) : BitVec 64 :=
  if n = USYS_uptime then usysUptimeWord ι.ticks else BitVec.signExtend 64 W.pid

/-- **`usysDet n W ι`**: the key the round resumes the process at -- the
bumped key at `usysDetRet n W ι` with every other reading kept, for the two
resuming members; `W` itself elsewhere (exit never resumes, `uroundOk_exit`;
outside the class the value is unused). -/
def usysDet (n : Int) (W : Uvis) (ι : UIota) : Uvis :=
  if usysDetResumes n then
    bump W (usysDetRet n W ι) W.M W.perm W.sz W.fd W.cwd W.gen W.ch W.lazy W.secc
  else W

theorem usysDet_resumes {n : Int} (W : Uvis) (ι : UIota) (h : usysDetResumes n) :
    usysDet n W ι = bump W (usysDetRet n W ι) W.M W.perm W.sz W.fd W.cwd W.gen W.ch W.lazy W.secc := by
  unfold usysDet; rw [if_pos h]

theorem usysDetRet_getpid (W : Uvis) (ι : UIota) :
    usysDetRet USYS_getpid W ι = BitVec.signExtend 64 W.pid := by
  unfold usysDetRet; rw [if_neg (by decide)]

theorem usysDetRet_uptime (W : Uvis) (ι : UIota) :
    usysDetRet USYS_uptime W ι = usysUptimeWord ι.ticks := by
  unfold usysDetRet; rw [if_pos rfl]

/-- **The receipt-derived fact a round carries** (the ι-prefix fits the
answer): at uptime the answer is the count `ι` names; no other class member
reads `ι`. -/
def usysIotaFits (n : Int) (r : BitVec 64) (ι : UIota) : Prop :=
  n = USYS_uptime → r = usysUptimeWord ι.ticks

/-- Every uptime answer the row allows has a prefix it fits (the row's count). -/
theorem usysIotaFits_exists {n : Int} {r : BitVec 64} (h : n = USYS_uptime → usysUptimeRet r) :
    ∃ ι : UIota, usysIotaFits n r ι := by
  by_cases hu : n = USYS_uptime
  · obtain ⟨t, ht⟩ := h hu
    exact ⟨{ UIota.boot with ticks := t }, fun _ => ht⟩
  · exact ⟨UIota.boot, fun h => absurd h hu⟩

/-! ## §3 The functional row refines the relation, and the relation at the
class IS the functional row -/

theorem usysDetResumes_ne {n : Int} (h : usysDetResumes n) :
    n ≠ USYS_exec ∧ n ≠ USYS_sbrk ∧ n ≠ USYS_wait ∧ n ≠ USYS_pipe ∧ n ≠ USYS_read ∧
      n ≠ USYS_fstat ∧ n ≠ USYS_fork ∧ n ≠ USYS_exit ∧ n ≠ USYS_close ∧ n ≠ USYS_dup ∧
      n ≠ USYS_open ∧ n ≠ USYS_chdir ∧ n ≠ USYS_seccomp := by
  rcases h with rfl | rfl <;> decide

/-- **`usysDet_mem`**: the functional row satisfies the landed image table
at its own answer -- `usysMemOk` at `usysDet`'s image, map, break and lazy
bit. -/
theorem usysDet_mem {n : Int} (W : Uvis) (ι : UIota) (h : usysDetResumes n) :
    usysMemOk n W.tf (usysDetRet n W ι) W.M W.perm W.sz W.lazy (usysDet n W ι).M (usysDet n W ι).perm
      (usysDet n W ι).sz (usysDet n W ι).lazy := by
  rw [usysDet_resumes W ι h]
  obtain ⟨h7, h12, h3, h4, h5, h8, hf, -⟩ := usysDetResumes_ne h
  unfold usysMemOk
  rw [if_neg h7, if_neg h12, if_neg h3, if_neg h4, if_neg h5, if_neg h8, if_neg hf]
  rcases h with rfl | rfl
  · rw [if_neg (by decide)]; exact ⟨rfl, rfl, rfl, rfl⟩
  · rw [if_pos rfl, usysDetRet_uptime]; exact ⟨⟨ι.ticks, rfl⟩, rfl, rfl, rfl, rfl⟩

/-- **The other rows, at the functional answer**: descriptors, pipe, cwd,
generation, pid, mask and children all hold at `usysDet` (the arm's
remaining premises). -/
theorem usysDet_rows {n : Int} (W : Uvis) (ι : UIota) (h : usysDetResumes n) :
    usysFdOk n W.tf (usysDetRet n W ι) W.fd (usysDet n W ι).fd ∧
    usysPipeOk n W.tf (usysDetRet n W ι) W.M (usysDet n W ι).M W.fd (usysDet n W ι).fd ∧
    usysCwdOk n (usysDetRet n W ι) W.cwd (usysDet n W ι).cwd ∧
    usysGenOk n W.gen (usysDet n W ι).gen ∧
    usysRetPid n (usysDetRet n W ι) W.pid ∧
    usysSeccOk n W.tf W.secc (usysDet n W ι).secc (usysDetRet n W ι) ∧
    usysChOk n (usysDetRet n W ι) W.ch (usysDet n W ι).ch ∧
    usysIotaFits n (usysDetRet n W ι) ι := by
  rw [usysDet_resumes W ι h]
  obtain ⟨-, -, -, h4, -, -, -, -, hcl, hdp, hop, hcd, h23⟩ := usysDetResumes_ne h
  refine ⟨usysFdOk_refl_at n n _ _ _ rfl hcl hdp hop h4, usysPipeOk_quiet _ _ _ _ _ _ _ h4,
    usysCwdOk_refl_at n n _ _ rfl hcd, rfl, ?_, usysSeccOk_refl _ _ _ _ h23, rfl, ?_⟩
  · rcases h with rfl | rfl
    · exact usysRetPid_of _ _ _ (usysDetRet_getpid W ι)
    · exact usysRetPid_ne _ _ _ (by decide)
  · intro hu; rw [hu, usysDetRet_uptime]

/-- **THE CONVERSE, at the arm** (`round_det`'s pure core): at a resuming
class member, any `(r, M', …)` the landed rows allow, at a prefix the answer
fits, IS `usysDet`'s -- the bumped key equals the functional one ON THE
NOSE. -/
theorem usysDet_of_rows {n : Int} (W : Uvis) (ι : UIota) (h : usysDetResumes n) (r : BitVec 64)
    (M' : ElfMem) (π' : Nat → Option UPerm) (szv' : Nat) (fdv' : List FdState) (cw' : Nat)
    (g' : Iris.GName) (cs' : ExtTreeSet Iris.GName compare) (lz' : Bool) (secc' : BitVec 64)
    (hm : usysMemOk n W.tf r W.M W.perm W.sz W.lazy M' π' szv' lz')
    (hfd : usysFdOk n W.tf r W.fd fdv') (hc : usysCwdOk n r W.cwd cw') (hg : usysGenOk n W.gen g')
    (hpid : usysRetPid n r W.pid) (hs : usysSeccOk n W.tf W.secc secc' r) (hch : cs' = W.ch)
    (hfit : usysIotaFits n r ι) :
    r = usysDetRet n W ι ∧ bump W r M' π' szv' fdv' cw' g' cs' lz' secc' = usysDet n W ι := by
  obtain ⟨h7, h12, h3, h4, h5, h8, hf, -, hcl, hdp, hop, hcd, h23⟩ := usysDetResumes_ne h
  obtain ⟨hM, hp, hsz⟩ := usysMemOk_quiet h7 h12 h3 h4 h5 h8 hm
  have hlz := usysMemOk_lazy h12 hm
  have hfd' := usysFdOk_quiet hcl hdp hop h4 hfd
  have hc' := usysCwdOk_quiet hcd hc
  have hs' := usysSeccOk_quiet h23 hs
  have hr : r = usysDetRet n W ι := by
    rcases h with rfl | rfl
    · rw [usysDetRet_getpid]; exact usysRetPid_getpid hpid
    · rw [usysDetRet_uptime]; exact hfit rfl
  refine ⟨hr, ?_⟩
  rw [usysDet_resumes W ι h]
  have hg' : g' = W.gen := hg
  subst hM hp hsz hlz hfd' hc' hs' hg' hch hr
  rfl

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
