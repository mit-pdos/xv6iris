/-
`pid_lock` (kernel/proc.c): protects the pid partition counters and the
pid cells `allocpid` (inlined into `allocproc`) writes.  NI M4 pids (the
`verified-quota` pid commit): pids are PARTITIONED BY THE PARENT'S SLOT --
slot `j` hands its children `j + NPROC`, `j + 2·NPROC`, ... from its own
counter `p->npid` (`ProcGeom.pNpid`, initialised to `j` by procinit), init
gets 1, and a slot whose share `PIDQ` is spent forks no more; `nextpid` and
the scan are gone.  The payload carries the 64 `npid` cells WHOLE and a
quarter of every `pid` word (the private block keeps a half, `p->lock` a
quarter), with the invariant that live pids are distinct.

THE PID LEDGER (NI-LEDGER-REST W2, Rocq 8043e4cdd; design
`claude-notes/design/ni-pid-ledger.md` D3): a fourth thing the lock
protects, riding beside the register it mirrors -- the authority of the
actor-labelled history of every allocation and release (`PidEv.Pev`, at the
canonical `WchG.wplName`), tied to the register by its live set alone
(`pidLedger R`: `liveOf h = PartialMap.dom R`).  allocproc appends
`PAlloc p pid` at its insert and freeproc `PFree p pid` at its delete, each
handing its caller a persistent receipt (`SlotGen.pidReceipt`).

THE PARTITION TIE (NI M4 pids P-0; design `noninterference.md` "M4 pids
design" F7, replacing NI M2-G2a's counter tie): the ledger also takes the
payload's counters `npids` and cells `pids`, and ties them to the history
(`pidTieS`): slot `j`'s counter IS `j + NPROC · ownAllocs (procAddr j) h`
(its own count, at most `PIDQ`), the cells' live set (`pidCells`) IS the
history's, and the history is well formed (`PidEv.pevWf`: every allocation
is the partition's at its prefix).  So the pid allocpid hands out is
`PidEv.pidPickS` of the opened history, FRESH by a pure lemma
(`pidPickS_fresh`), and the allocation hands back `pidAllocRcpt`: the
`PAlloc`'s prefix, and the pid the kernel was bound to give from it; the cap
arm hands back `pidCapRcpt`: a prefix at which the actor's share is spent.

## Deviations from Rocq (the ledger)

1. The tie is an equality of PREDICATES on `Int` (`PidEv` deviation 2):
   `liveOf h = PartialMap.dom R`, Rocq `live_of h = dom R` (a `gset Z`).
   `pidDom_empty/insert/delete` are the three `dom` rewrites the steps use
   (Rocq's `dom_empty_L`/`dom_insert_L`/`dom_delete_L`).
2. `pidLockResAt` changes IN PLACE, as Rocq's `nextpid_res_at` did: its
   statement and every statement naming it (`pidLockPay`, the
   `isLock … pidLockPay` of every client) are byte-identical; the body gains
   the conjunct `pidLedger R` right after `pidRegAuth R`.  No Timeless
   instance (the Lean payload has none to keep).
3. (G2a) The steps' cell updates are stated pointwise (`pids' n = pid`,
   `pids' i = pids i` elsewhere) rather than through `ProofAllocproc.apPidsSet`
   / `ProofFreeproc.pidsClear`, which live above this file.  `pidLedger_free`
   needs no `pid ≠ 0` (a cell holding 0 is in no `pidCells`).
4. (NI M4 pids) The tie also bounds each own count by `PIDQ` (the cap keeps
   it there): the counter's SIGNED compare against `PIDMAX - NPROC` is the
   quota test only below that bound.
-/
import Xv6.ProcDefs

namespace Xv6

open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode Std MachCSL

/-- `&initproc` (`&pid_lock` is `Xv6/SpecProcinit.lean`'s `pidLockAddr`;
NI M4 pids: `nextpid` is gone). -/
def initprocAddr : BitVec 64 := KA.«initproc»
-- `PIDMAX` is `Xv6/ProcGeom.lean`'s (Rocq `ProcGeom.PIDMAX`).

/-- The pids are distinct where nonzero, and in range. -/
def pidsOk (pids : Nat → BitVec 32) : Prop :=
  ∀ j1 j2, j1 < NPROC → j2 < NPROC → pids j1 ≠ 0#32 → pids j1 = pids j2 → j1 = j2

/-! ## The register's domain, step by step (deviation 1) -/

theorem pidDom_empty : PartialMap.dom (∅ : IntMapF GName) = fun _ => False := by
  funext k
  simp only [PartialMap.dom, get?_empty, Option.isSome_none, Bool.false_eq_true]

theorem pidDom_insert (R : IntMapF GName) (x : Int) (g : GName) :
    PartialMap.dom (PartialMap.insert R x g) = fun k => k = x ∨ PartialMap.dom R k := by
  funext k
  apply propext
  rw [Iris.Std.LawfulPartialMap.dom_insert_iff, eq_comm]

theorem pidDom_delete (R : IntMapF GName) (x : Int) :
    PartialMap.dom (PartialMap.delete R x) = fun k => PartialMap.dom R k ∧ k ≠ x := by
  funext k
  apply propext
  by_cases h : x = k
  · subst h
    simp only [PartialMap.dom, get?_delete_eq rfl, Option.isSome_none, Bool.false_eq_true,
      ne_eq, not_true_eq_false, and_false]
  · simp only [PartialMap.dom, get?_delete_ne h, ne_eq]
    exact ⟨fun h' => ⟨h', fun e => h e.symm⟩, fun h' => h'.1⟩

/-! ## The partition tie (NI M4 pids P-0) -/

/-- The nonzero pids the 64 cells hold. -/
def pidCells (pids : Nat → BitVec 32) (z : Nat) : Prop := z ≠ 0 ∧ ∃ j, j < NPROC ∧ (pids j).toNat = z

/-- The partition tie: slot `j`'s counter IS `j + NPROC` times its own
allocation count (at most `PIDQ`), and the cells' live set IS the history's. -/
def pidTieS (npids pids : Nat → BitVec 32) (h : List Pev) : Prop :=
  (∀ j, j < NPROC → (npids j).toNat = j + NPROC * ownAllocs (procAddr j) h ∧
    ownAllocs (procAddr j) h ≤ PIDQ) ∧
  ∀ z : Nat, liveOf h (z : Int) ↔ pidCells pids z

/-- The counters procinit leaves: slot `j`'s is `j`. -/
def npidsInit : Nat → BitVec 32 := fun j => BitVec.ofNat 32 j

/-- The counter's quota test (`npid > PIDMAX - NPROC`, signed): under the tie,
exactly the own count at `PIDQ`. -/
theorem pidTieS_cap {npids pids : Nat → BitVec 32} {h : List Pev} (ht : pidTieS npids pids h)
    {m : Nat} (hm : m < NPROC) :
    (2 ^ 31 - 65 < (npids m).toNat ↔ ownAllocs (procAddr m) h = PIDQ) := by
  obtain ⟨he, hle⟩ := ht.1 m hm
  rw [he]; unfold PIDQ at hle ⊢; unfold NPROC at hm ⊢
  omega

section
variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [WchG GF]

/-- THE PID LEDGER, as the lock's payload holds it (Rocq `pid_ledger`, design
ni-pid-ledger.md D3, ruling R2(a)): the history's authority, tied to the
register by its live set -- AND (NI M4 pids P-0) to the payload's counters
and cells (`pidTieS`), the history well formed (`pevWf`).  Context-free, so
the payload is still a `CtxMorph`. -/
def pidLedger (npids pids : Nat → BitVec 32) (R : IntMapF GName) : IProp GF := iprop%
  ∃ h : List Pev, pidLedAuth h ∗ ⌜liveOf h = PartialMap.dom R ∧ pidTieS npids pids h ∧ pevWf h⌝ ∗
    -- (NI M4 pids P-3) the payload's half of every slot's own-count agreement, at the history's
    ([∗list] j ∈ List.range NPROC, pownHalf (procAddr j) (ownAllocs (procAddr j) h))

/-- (NI M4 pids P-3) **THE OWN-COUNT LEND**: what allocproc takes from its
caller, keyed by the running proc word -- the slot's half of the own-count
agreement at the caller's record's count, or the fact that there is no actor
(the boot hart, `act = 0`). -/
def pownLend (act : BitVec 64) (c : Nat) : IProp GF := iprop(⌜act = 0#64⌝ ∨ pownHalf act c)

theorem pownLend_zero (c : Nat) : ⊢@{IProp GF} pownLend 0#64 c := by
  unfold pownLend; ileft; ipureintro; rfl

theorem pownLend_of_half (act : BitVec 64) (c : Nat) : pownHalf (GF := GF) act c ⊢ pownLend act c := by
  unfold pownLend; iintro H; iright; iexact H

theorem pownLend_back (act : BitVec 64) (c : Nat) (h : act ≠ 0#64) :
    pownLend (GF := GF) act c ⊢ pownHalf act c := by
  unfold pownLend; iintro (%hz | H)
  · exact absurd hz h
  · iexact H

/-- THE ALLOCATION RECEIPT: the `PAlloc`'s prefix, and the pid it was bound
to give (NI M4 pids: `PidEv.pidPickS` of the actor at that prefix) -- (P-3)
which is the partition's pick at the caller's own count `c` (`pidPickN`: the
lent half agreed with the ledger's own count of the actor). -/
def pidAllocRcpt (act : BitVec 64) (c : Nat) (pid : BitVec 32) : IProp GF := iprop%
  ∃ h : List Pev, pidReceipt h (.PAlloc act pid) ∗ ⌜pid.toNat = pidPickS act h ∧ pid.toNat = pidPickN act c⌝

instance pidAllocRcpt_persistent (act : BitVec 64) (c : Nat) (pid : BitVec 32) :
    Persistent (pidAllocRcpt (GF := GF) act c pid) := by
  unfold pidAllocRcpt; infer_instance

/-- (NI M4 pids P-3) The payload's halves, one slot's taken out; put back at a
history that moved no other slot's own count. -/
theorem pownHalves_acc (h : List Pev) (m : Nat) (hm : m < NPROC) :
    ([∗list] j ∈ List.range NPROC, pownHalf (GF := GF) (procAddr j) (ownAllocs (procAddr j) h)) ⊢
      pownHalf (procAddr m) (ownAllocs (procAddr m) h) ∗
      ∀ h' : List Pev, ⌜∀ j, j < NPROC → j ≠ m → ownAllocs (procAddr j) h' = ownAllocs (procAddr j) h⌝ -∗
        pownHalf (procAddr m) (ownAllocs (procAddr m) h') -∗
        [∗list] j ∈ List.range NPROC, pownHalf (procAddr j) (ownAllocs (procAddr j) h') := by
  have hl : (List.range NPROC)[m]? = some m := List.getElem?_range hm
  iintro H
  icases BigSepL.bigSepL_lookup_acc_impl hl $$ H with ⟨Hm, Hc⟩
  iframe Hm
  iintro %h' %ho Hm'
  ispecialize Hc $$ %(fun (_ : Nat) (y : Nat) => pownHalf (GF := GF) (procAddr y) (ownAllocs (procAddr y) h'))
  iapply Hc $$ [] Hm'
  imodintro
  iintro %k %y %hy %hk H
  have hkn : k < NPROC := by
    have := (List.getElem?_eq_some_iff.mp hy).1; simpa using this
  have hy' : y = k := by
    rw [List.getElem?_range hkn] at hy
    exact (Option.some.inj hy).symm
  subst hy'
  have e := ho y hkn hk
  iapply (show pownHalf (GF := GF) (procAddr y) (ownAllocs (procAddr y) h) ⊢
    pownHalf (procAddr y) (ownAllocs (procAddr y) h') from by rw [e]) $$ H

/-- (NI M4 pids P-3) The payload's halves at a history that moved no own count. -/
theorem pownHalves_congr (h h' : List Pev) (ho : ∀ j, j < NPROC → ownAllocs (procAddr j) h' = ownAllocs (procAddr j) h) :
    ([∗list] j ∈ List.range NPROC, pownHalf (GF := GF) (procAddr j) (ownAllocs (procAddr j) h)) ⊢
      [∗list] j ∈ List.range NPROC, pownHalf (procAddr j) (ownAllocs (procAddr j) h') := by
  apply BigSepL.bigSepL_mono
  intro k y hy
  have hyn : y < NPROC := List.mem_range.mp (List.mem_of_getElem? hy)
  rw [ho y hyn]

/-- THE CAP'S RECEIPT (NI M4 pids): a prefix of the ledger at which the
actor's share is spent (the own count is monotone and capped, so a lower
bound suffices). -/
def pidCapRcpt (act : BitVec 64) : IProp GF := iprop%
  ∃ h : List Pev, pidLedLb h ∗ ⌜ownAllocs act h = PIDQ⌝

instance pidCapRcpt_persistent (act : BitVec 64) : Persistent (pidCapRcpt (GF := GF) act) := by
  unfold pidCapRcpt; infer_instance

/-- The payload of `pid_lock` at context `ξ` (Rocq `PidLock.nextpid_res_at`):
(NI M4 pids) every slot's partition counter `npid` WHOLE, a quarter of every
slot's `pid` cell, THE PID REGISTER's authority (`SlotGen.pidRegAuth`, D8)
with its domain fact (`pidRegDom`: every registered pid is nonzero and held
by some slot), THE PID LEDGER beside the register (`pidLedger npids pids R`,
NI-LEDGER-REST, its partition tie NI M4 P-0) and THE BOOT ERA'S MARK -- no
slot holds pid 1 -- discharged for good by the one-shot `nextpidShot` (fired
by allocproc's init arm, NI M4 pids; the counter's mark went with
`nextpid`).  The distinctness conjunct `pidsOk` is Lean's (kept from the
pre-D8 payload). -/
def pidLockResAt [CurCtx] (ξ : CtxId) : IProp GF := iprop%
  ∃ (npids pids : Nat → BitVec 32), ⌜pidsOk pids⌝ ∗
    ([∗list] j ∈ List.range NPROC, wordAtN ξ (pNpid (procAddr j)) 4 (DFrac.own 1) (npids j)) ∗
    ([∗list] j ∈ List.range NPROC, wordAtN ξ (pPid (procAddr j)) 4 pidLockQ (pids j)) ∗
    ∃ R : IntMapF GName, ⌜pidRegDom R pids⌝ ∗ pidRegAuth R ∗ pidLedger npids pids R ∗
      (⌜∀ j, j < NPROC → (pids j).toNat ≠ 1⌝ ∨ nextpidShot)

/-- The payload as a function of the holder's context. -/
def pidLockPay [CurCtx] : CtxId → IProp GF := fun ξ => pidLockResAt ξ

/-- `pid_lock`'s payload transports between contexts, so `acquire` and
`release` apply to it (the register rows are ghost: constants). -/
instance instCtxMorphPidLockPay [CurCtx] : CtxMorph (GF := GF) pidLockPay := by
  unfold pidLockPay pidLockResAt
  exact @instCtxMorphExists hlc GF _ _ _ (fun npids => @instCtxMorphExists hlc GF _ _ _ (fun pids =>
    @instCtxMorphSep hlc GF _ _ _ (instCtxMorphConst _)
      (@instCtxMorphSep hlc GF _ _ _
        (ctxMorph_bigSepL (List.range NPROC)
          (fun _ y ξ => wordAtN ξ (pNpid (procAddr y)) 4 (DFrac.own 1) (npids y))
          (fun _ _ => instCtxMorphWordAtN _ _ _ _))
        (@instCtxMorphSep hlc GF _ _ _
          (ctxMorph_bigSepL (List.range NPROC)
            (fun _ y ξ => wordAtN ξ (pPid (procAddr y)) 4 pidLockQ (pids y))
            (fun _ _ => instCtxMorphWordAtN _ _ _ _))
          (instCtxMorphConst _)))))

/-! ## The ledger's ghost steps (design ni-pid-ledger.md §3 W2)

Each mirrors the register step it rides beside (`SlotGen.pidReg_insert` /
`pidReg_delete`) and hands back the receipt of the event it appended. -/

/-- The boot's: the empty history is the boot payload's ledger -- every
counter at its slot (procinit's), every cell 0, the empty register (Rocq
`pid_ledger_empty`). -/
theorem pidLedger_empty :
    pidLedAuth (GF := GF) [] ∗ ([∗list] j ∈ List.range NPROC, pownHalf (procAddr j) 0) ⊢
      pidLedger npidsInit (fun _ => 0#32) ∅ := by
  unfold pidLedger
  iintro ⟨Ha, Hh⟩
  iexists []
  iframe Ha
  isplitr [Hh]
  rotate_left
  · simp only [ownAllocs_nil]; iexact Hh
  ipureintro
  refine ⟨by rw [pidDom_empty]; rfl, ⟨fun j hj => ⟨?_, by simp [ownAllocs_nil]⟩, fun z => ?_⟩, pevWf_nil⟩
  · unfold npidsInit; rw [ownAllocs_nil, BitVec.toNat_ofNat]; unfold NPROC at hj ⊢; omega
  · simp only [liveOf, List.foldl_nil, pidCells, BitVec.toNat_ofNat, false_iff, not_and, not_exists]
    intro hz j _ h0
    exact hz (by rw [← h0])

/-- A lower bound of the ledger, read off its authority. -/
theorem pidLedAuth_lb (h : List Pev) : pidLedAuth (GF := GF) h ⊢ pidLedAuth h ∗ pidLedLb h := by
  unfold pidLedAuth pidLedLb
  iintro H
  ihave #Hl := MonoList.lb_own_get $$ H
  iframe H Hl

/-- Both readings at once, for every slot (what allocproc reads before its arms). -/
theorem pidLedger_facts (npids pids : Nat → BitVec 32) (R : IntMapF GName) :
    pidLedger (GF := GF) npids pids R ⊢ ⌜∀ m, m < NPROC → (npids m).toNat < 2 ^ 31 ∧
      ((npids m).toNat ≤ 2 ^ 31 - 65 → ∀ j, j < NPROC → (pids j).toNat ≠ (npids m).toNat + NPROC)⌝ := by
  unfold pidLedger
  iintro ⟨%h, -, %⟨-, ⟨hnp, hcells⟩, hw⟩, -⟩
  ipureintro
  intro m hm
  refine ⟨?_, fun _ j hj he => ?_⟩
  · obtain ⟨he, hle⟩ := hnp m hm
    rw [he]; unfold PIDQ at hle; unfold NPROC at hm ⊢
    omega
  · obtain ⟨hfr, -⟩ := pidPickS_fresh (act := procAddr m) hw hm rfl
    have hpk : pidPickS (procAddr m) h = (npids m).toNat + NPROC := by
      unfold pidPickS pidPickN
      rw [if_neg (procAddr_nonzero hm), slotOf_procAddr hm, (hnp m hm).1]
      unfold NPROC; omega
    apply hfr
    rw [hcells, hpk]
    exact ⟨by unfold NPROC; omega, j, hj, he⟩

/-- THE CAP'S STEP (NI M4 pids): at the counter's quota test, the actor's
share is spent at the opened history; the receipt is a lower bound of it. -/
theorem pidLedger_cap (npids pids : Nat → BitVec 32) (R : IntMapF GName) (m : Nat) (hm : m < NPROC)
    (hcap : 2 ^ 31 - 65 < (npids m).toNat) (c : Nat) :
    pidLedger (GF := GF) npids pids R ∗ pownHalf (procAddr m) c ⊢
      pidLedger npids pids R ∗ pownHalf (procAddr m) c ∗ pidCapRcpt (procAddr m) ∗ ⌜c = PIDQ⌝ := by
  unfold pidLedger pidCapRcpt
  iintro ⟨⟨%h, Ha, %⟨hl, ht, hw⟩, Hh⟩, Hc⟩
  icases pidLedAuth_lb h $$ Ha with ⟨Ha, #Hlb⟩
  icases pownHalves_acc h m hm $$ Hh with ⟨Hm, Hback⟩
  ihave %he := pownHalf_agree (procAddr m) _ c $$ [Hm Hc]
  · iframe Hm Hc
  have hq : ownAllocs (procAddr m) h = PIDQ := (pidTieS_cap ht hm).1 hcap
  isplitl [Ha Hm Hback]
  · iexists h
    iframe Ha
    isplitr
    · ipureintro; exact ⟨hl, ht, hw⟩
    iapply Hback $$ %h [] Hm
    ipureintro; intro _ _ _; rfl
  isplitl [Hc]
  · iexact Hc
  isplitl []
  · iexists h
    iframe Hlb
    ipureintro; exact hq
  · ipureintro; rw [← he, hq]

/-- allocproc's, at the register's insert (Rocq `pid_ledger_alloc`; NI M4
pids P-0): the store of `pid` into slot `n`'s empty cell -- and, on the
found arm, of `pid` into the actor's counter -- re-close the tie; the
appended `PAlloc act pid` keeps the history well formed, since `pid` IS the
partition's pick at the opened history; that is the receipt's fact.  Two
arms: INIT (`act = 0`, pid 1, the counters untouched) and FOUND (`act` slot
`m`'s address, under the cap, `pid` its counter plus `NPROC`). -/
theorem pidLedger_alloc (npids npids' pids pids' : Nat → BitVec 32) (n : Nat)
    (R : IntMapF GName) (act : BitVec 64) (pid : BitVec 32) (g : GName)
    (hn : n < NPROC) (hn0 : pids n = 0#32) (hset : pids' n = pid)
    (hother : ∀ i, i ≠ n → pids' i = pids i)
    (harm : (act = 0#64 ∧ pid = 1#32 ∧ npids' = npids) ∨
      (∃ m, m < NPROC ∧ act = procAddr m ∧ (npids m).toNat ≤ 2 ^ 31 - 65 ∧
        pid.toNat = (npids m).toNat + NPROC ∧ npids' m = pid ∧ ∀ i, i ≠ m → npids' i = npids i)) (c : Nat) :
    pidLedger (GF := GF) npids pids R ∗ pownLend act c ⊢
      |==> (pidLedger npids' pids' (PartialMap.insert R (pid.toNat : Int) g) ∗
        pownLend act (c + 1) ∗ pidAllocRcpt act c pid) := by
  unfold pidLedger pidAllocRcpt pidReceipt
  iintro ⟨⟨%h, Ha, %⟨hl, ⟨hnp, hcells⟩, hw⟩, Hh⟩, Hlend⟩
  -- the pick, read on the opened history
  have hpick : pid.toNat = pidPickS act h := by
    rcases harm with ⟨rfl, rfl, -⟩ | ⟨m, hm, rfl, -, hp, -, -⟩
    · unfold pidPickS pidPickN; rw [if_pos rfl]; rfl
    · unfold pidPickS pidPickN
      rw [if_neg (procAddr_nonzero hm), slotOf_procAddr hm, hp, (hnp m hm).1]
      unfold NPROC; omega
  have hact : pevActOk act := by
    rcases harm with ⟨rfl, -, -⟩ | ⟨m, hm, rfl, -⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨m, hm, rfl⟩
  -- (NI M4 pids P-3) the own counts after the append: the actor's moved by one, no other slot's
  have hoth : ∀ j, j < NPROC → procAddr j ≠ act →
      ownAllocs (procAddr j) (h ++ [.PAlloc act pid]) = ownAllocs (procAddr j) h :=
    fun j _ hne => ownAllocs_snoc_alloc_other _ _ h pid (fun e => hne e.symm)
  -- (NI M4 pids P-3) the halves: at the found arm the lend agrees with the payload's and both step
  ihave Hpo : iprop(|==> (([∗list] j ∈ List.range NPROC, pownHalf (GF := GF) (procAddr j)
      (ownAllocs (procAddr j) (h ++ [.PAlloc act pid]))) ∗ pownLend act (c + 1) ∗
      ⌜pid.toNat = pidPickN act c⌝)) $$ [Hh Hlend]
  · rcases harm with ⟨rfl, rfl, -⟩ | ⟨m, hm, rfl, -, hp, -, -⟩
    · iclear Hlend
      imodintro
      isplitl [Hh]
      · iapply pownHalves_congr h _ (fun j hj => hoth j hj (procAddr_nonzero hj)) $$ Hh
      isplitl []
      · iapply pownLend_zero
      · ipureintro; unfold pidPickN; rw [if_pos rfl]; rfl
    · ihave Hl := pownLend_back (procAddr m) c (procAddr_nonzero hm) $$ Hlend
      icases pownHalves_acc h m hm $$ Hh with ⟨Hm, Hback⟩
      ihave %he := pownHalf_agree (procAddr m) _ c $$ [Hm Hl]
      · iframe Hm Hl
      imod pownHalf_update (procAddr m) _ (c + 1) $$ [Hm Hl] with ⟨Hm, Hl⟩
      · rw [he]; iframe Hm Hl
      imodintro
      isplitl [Hm Hback]
      · iapply Hback $$ %(h ++ [.PAlloc (procAddr m) pid]) [] [Hm]
        · ipureintro
          intro j hj hjm
          exact hoth j hj (fun e => hjm (procAddr_inj hj hm e))
        · rw [ownAllocs_snoc_alloc_self, he]; iexact Hm
      isplitl [Hl]
      · iapply pownLend_of_half; iexact Hl
      · ipureintro
        rw [← he, hpick]; rfl
  imod Hpo with ⟨Hh, Hlend, %hpickN⟩
  imod pidLedAuth_grow h (.PAlloc act pid) $$ Ha with ⟨Ha, #Hb⟩
  imodintro
  iframe Hlend
  isplitl [Ha Hh]
  · iexists h ++ [.PAlloc act pid]
    iframe Ha Hh
    ipureintro
    refine ⟨by rw [liveOf_snoc_alloc_dom _ h act pid hl, pidDom_insert], ⟨fun j hj => ?_, fun z => ?_⟩,
      pevWf_snoc_alloc h act pid hw hpick hact⟩
    · rcases harm with ⟨rfl, -, rfl⟩ | ⟨m, hm, rfl, hcap, hp, hnm, hno⟩
      · rw [ownAllocs_snoc_alloc_other _ _ h pid (procAddr_nonzero hj).symm]
        exact hnp j hj
      · by_cases hjm : j = m
        · subst hjm
          have e := (hnp j hj).1
          rw [ownAllocs_snoc_alloc_self, hnm, hp]
          unfold NPROC PIDQ at *
          constructor <;> omega
        · rw [ownAllocs_snoc_alloc_other _ _ h pid
            (fun he => hjm (procAddr_inj hj hm he.symm)), hno j hjm]
          exact hnp j hj
    · rw [liveOf_snoc_alloc]
      simp only [Int.ofNat_inj, hcells, pidCells]
      constructor
      · rintro (rfl | ⟨hz, j, hj, hpj⟩)
        · refine ⟨?_, n, hn, by rw [hset]⟩
          rcases harm with ⟨-, rfl, -⟩ | ⟨m, -, -, -, hp, -⟩
          · decide
          · rw [hp]; unfold NPROC; omega
        · have hjn : j ≠ n := by rintro rfl; rw [hn0] at hpj; exact hz hpj.symm
          exact ⟨hz, j, hj, by rw [hother j hjn]; exact hpj⟩
      · rintro ⟨hz, j, hj, hpj⟩
        by_cases hjn : j = n
        · subst hjn; rw [hset] at hpj; exact Or.inl hpj.symm
        · rw [hother j hjn] at hpj; exact Or.inr ⟨hz, j, hj, hpj⟩
  · iexists h
    iframe Hb
    ipureintro
    exact ⟨hpick, hpickN⟩

/-- freeproc's, at the register's delete (Rocq `pid_ledger_free`; the tie NI
M2-G2a): slot `j`'s cell, the only one holding `pid` (`pidsOk`), is
cleared; the counters are untouched (`ownAllocs_snoc_free`). -/
theorem pidLedger_free (npids pids pids' : Nat → BitVec 32) (j : Nat)
    (R : IntMapF GName) (act : BitVec 64) (pid : BitVec 32)
    (hj : j < NPROC) (hpj : pids j = pid) (hok : pidsOk pids) (hclr : pids' j = 0#32)
    (hother : ∀ i, i ≠ j → pids' i = pids i) :
    pidLedger (GF := GF) npids pids R ⊢
      |==> (pidLedger npids pids' (PartialMap.delete R (pid.toNat : Int)) ∗
        ∃ h, pidReceipt h (.PFree act pid)) := by
  unfold pidLedger pidReceipt
  iintro ⟨%h, Ha, %⟨hl, ⟨hnp, hcells⟩, hw⟩, Hh⟩
  imod pidLedAuth_grow h (.PFree act pid) $$ Ha with ⟨Ha, #Hb⟩
  imodintro
  isplitl [Ha Hh]
  · iexists h ++ [.PFree act pid]
    iframe Ha
    isplitr [Hh]
    rotate_left
    · iapply pownHalves_congr h _ (fun j _ => ownAllocs_snoc_free _ _ h pid) $$ Hh
    ipureintro
    refine ⟨by rw [liveOf_snoc_free_dom _ h act pid hl, pidDom_delete],
      ⟨fun i hi => by rw [ownAllocs_snoc_free]; exact hnp i hi, fun z => ?_⟩, pevWf_snoc_free h act pid hw⟩
    · rw [liveOf_snoc_free]
      simp only [hcells, pidCells, ne_eq, Int.ofNat_inj]
      constructor
      · rintro ⟨⟨hz, i, hi, hpi⟩, hzp⟩
        have hij : i ≠ j := by rintro rfl; rw [hpj] at hpi; exact hzp hpi.symm
        exact ⟨hz, i, hi, by rw [hother i hij]; exact hpi⟩
      · rintro ⟨hz, i, hi, hpi⟩
        have hij : i ≠ j := by rintro rfl; rw [hclr] at hpi; exact hz hpi.symm
        rw [hother i hij] at hpi
        refine ⟨⟨hz, i, hi, hpi⟩, fun hzp => hij ?_⟩
        have hnz : pids i ≠ 0#32 := by
          intro h0; rw [h0] at hpi; exact hz hpi.symm
        exact hok i j hi hj hnz (by rw [hpj]; exact BitVec.eq_of_toNat_eq (hpi.trans hzp))
  · iexists h
    iexact Hb

end

end Xv6
