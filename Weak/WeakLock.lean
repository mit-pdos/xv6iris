/-
Weak: **the weak-memory spinlock** (M3b item 3) -- the view-tier lock rules: the lock
invariant (an `IProp`, hence objective), the client-facing `wisLock` / `wlocked`, allocation
and registration, the acquire core (`amoswap.w.aq`) and the release core (`sw` under
`fence rw,w`), and the PROTECTED lock (`wplockBody`: the payload's footprint, its registration,
the adequacy seams, the protected store, the read record, the two cores at a fixed
registration point).

Rocq: `iris/WeakLock.v` @ xxvzwolszwmp.

The Rocq header, in substance (Rocq vocabulary).

THE DESIGN'S CENTRAL CLAIM, ON REAL MACHINERY: a spinlock whose CLIENT-FACING interface is
today's -- `wis_lock γ lk R` persistent, `wlocked γ i` the exclusive holder token, `R` an
arbitrary `vProp` -- over a machine where a store is a message in a log and a load may read a
stale one.  What changes is only the two sync instructions' proofs.

WHY THE INVARIANT IS AN `iProp`.  Iris invariants may hold only OBJECTIVE assertions, and the
cleanest way to be objective is to be an `iProp`: the whole invariant lives at the BASE
altitude (the Cosmo pattern), and the `vProp` surface appears only in the payload, frozen at a
view:

  wlock_inv γ lk R := ∃ st t v, wlat4L lk t v (tid_of st) ∗ lock_auth γ st ∗
                        ( free: ⌜st = None⌝ ∗ ⌜v = 0⌝ ∗ frag ∗ monPred_at R (view_scl t)
                        | held: ⌜st ≠ None⌝ ∗ ⌜v ≠ 0⌝ )

Three landed facts make it work: the lock word's element bundle is an `iProp` (objective, no
receipt); `monPred_at R V` is objective for any `R`; and the timestamp `t` the elements carry IS
the timestamp the payload is frozen at -- the releaser deposits at the timestamp its own store
takes (`wwp_release_deposit`, resting on `ws_bounded`), and the acquirer's `amoswap.w.aq` reads
THAT timestamp and gains `view_scl t ⊑ ws_view`, so the payload thaws into the acquirer's own
index by `monPred_mono`, and no view ever crosses the invariant boundary.

KEPT: the lock WORD, the `excl_auth` ghost state and the holder token (`wlocked γ i` IS
`WpLock.locked γ i`), and the transfer of `R`.  DEFERRED (M4 bookkeeping): the `lk->cpu` and
`lock_name` fields (8-byte cells); the lock's state therefore only takes the values `None` and
`Some (i, true)` here, the intermediate state being passed through by composing `WpLock`'s two
transitions.

THE ALTITUDE OF THE TWO CORES: stated over the step's PRE- and POST-state with the
instruction's weak-memory effect (`wQ_amo_aq` / `wQ_store`) as a premise -- the altitude
`WeakInstr.wp_winstr` hands a leaf.  (The closing Rocq note, WHY `wstep_cert`'s `Q` IS OVER
THE SUCCESSOR *STATE*: the invariant owns the lock word's latest-write elements, and any step
that writes those bytes invalidates them; re-establishing the state interpretation after a
store requires RETARGETING the elements at the message the step appended, so the certificate
must say WHICH message that was -- a statement about `wm_log σ'`, which a `wstate` cannot
express.  Hence `Q : wmstate -> wmstate -> Prop`.)

The design records of §6 (the protected lock: WHY THE FRAGMENTS LIVE IN THE INVARIANT AND WHY
`n0` IS A PARAMETER; what the two cores do to the footprint window) are kept as the comments on
the corresponding Lean declarations below.

**Deviations from Rocq.**

1. NAMES: the tree's camelCase (map below).  `acc_addr_0` is FILE-QUALIFIED
   (`WeakLock.accAddr0`, `notes/weak-port-dupnames.json`).  Vocabulary as
   `Weak/WeakStore.lean` deviation 1 (`S (length l)` ↦ `l.length + 1`, `pa_z` ↦ `paZ`,
   `acc_addr` ↦ `WeakInterp.accAddr`, `pa_add a j` ↦ `a + BitVec.ofNat 64 j`, `fin_to_nat c` ↦
   `c.val`, `nth_byte w j` ↦ `nthByte (n := 4) w j`, `wflat … !! a = Some v` ↦
   `wflatMem … a = some v`, `DfracOwn 1` ↦ `DFrac.own 1`, `monPred_at R V` ↦
   `R.monPred_at V`, `view_scl` ↦ `viewScl`, `Arch.pa` ↦ `PAddr`, `bv n` ↦ `BitVec n`).
2. THE SC LOCK GHOST.  Rocq's `WpLock` `lockG`/`lock_auth`/`lock_frag`/`locked`/`lock_take`/
   `lock_setcpu`/`lock_clrcpu`/`lock_give`/`locked_state`/`locked_exclusive` have no Lean
   counterpart (`MachCSL.Lock` is the TSO kit, a different ghost): they are the new shim
   `MachCSL/WeakAuxWeakLock.lean` (`LockExG`, `lockAuth`, `lockFrag`, `lockedEx`, `lockTake`,
   `lockSetcpu`, `lockClrcpu`, `lockGive`, `lockedExState`, `lockedExExclusive`,
   `lockExAlloc`).  So Rocq's `locked γ i` is `lockedEx γ i` throughout.
3. `lock_zero`/`lock_one` (Rocq `mword_of_int 0/1 : mword 32`) are the literals `0#32`/`1#32`.
4. `wwrite_msg_data4` is stated at `v : BitVec 32` (Rocq any width `{w : N} (v : bv w)`):
   `WeakInterp.wwriteMsg` is stated at `8 * n` (WeakInterp deviation 7).
5. STATEMENT SHAPES (WeakStore deviation 3): Rocq `A -∗ B -∗ C` is `A ⊢ B -∗ C`, `A -∗ B ==∗ C`
   is `A ⊢ B -∗ |==> C`, `A -∗ B ={E}=∗ C` is `A ⊢ B -∗ |={E}=> C`; Rocq `P ⊢ Q` stays.
6. `Context {!riscvGS Σ, !weakGS Σ, !lockG Σ}` is `{hlc : HasLC} [MachGS hlc GF] [WeakGS GF]
   [LockExG GF]` (the SC instance supplies the invariant ghost state, WeakGhost deviation 10);
   `wprotG` is `[WprotG GF]`, from §6 on, as in Rocq.
7. `wlock_inv_regd`'s and the `wplock_inv_*regd` seams' `wlock_regd`/`wprot_regd`/
   `wprot_rd_regd` take `(hlc := hlc)` explicitly (they live in WeakGhost's `interp` section).
8. `wprot_win_free` is proved with `bigSepL_mono_of_forall` (Rocq `big_sepL_mono`, whose lookup
   premise is unused).  The `big_sepL_lookup_acc` of the two seams and of `wprot_store_core`
   is the Lean-only `bigSepLLookupAccSame` (iris-lean's `bigSepL_lookup_acc` restores at
   `l.set i y`, Rocq's at `l`).
9. `wprot_store_core` derives the holder fact inline (Rocq calls `wplock_holder` without
   consuming its three resources; the Lean `ihave` would consume them) -- same content, same
   statement.

**Rocq → Lean name map.**  `lock_zero` `lockZero`, `lock_one` `lockOne`, `lock_one_ne_zero`
`lockOneNeZero`, `wwrite_msg_data4` `wwriteMsgData4`, `lock_zero_data4` `lockZeroData4`,
`wlock_shaped_acq` `wlockShapedAcq`, `wlock_shaped_rel` `wlockShapedRel`,
`nth_byte_lock_one_0_ne` `nthByteLockOne0Ne`, `lock_one_data4_ne` `lockOneData4Ne`,
`alt_step_acq_msg` `altStepAcqMsg`, `alt_step_fail_msg` `altStepFailMsg`, `alt_step_rel_msg`
`altStepRelMsg`, `wlockN` `wlockN`, `tid_of` `tidOf`, `wlock_inv` `wlockInv`, `wis_lock`
`wisLock`, `wis_lock_persistent` `wisLock_persistent`, `wis_lock_objective`
`wisLock_objective`, `wlocked` `wlocked`, `wlocked_objective` `wlocked_objective`,
`wlocked_exclusive` `wlockedExclusive`, `wlock_alloc` `wlockAlloc`, `wlock_inv_regd`
`wlockInvRegd`, `wlat4_flat_gen` `wlat4FlatGen`, `wacquire_core` `wacquireCore`,
`wrelease_core` `wreleaseCore`, `acc_addr_0` `WeakLock.accAddr0`, `prot_dok` `protDok`,
`wprot_win` `wprotWin`, `wprot_win_timeless` `wprotWin_timeless`, `wprot_win_free`
`wprotWinFree`, `wplock_body` `wplockBody`, `wplock_body_inv` `wplockBodyInv`,
`wprot_register_list` `wprotRegisterList`, `wprot_deregister_list` `wprotDeregisterList`,
`wplock_alloc` `wplockAlloc`, `wplock_inv_regd` `wplockInvRegd`, `wplock_inv_rd_regd`
`wplockInvRdRegd`, `wplock_holder` `wplockHolder`, `wprot_store_core` `wprotStoreCore`,
`wprot_read_record` `wprotReadRecord`, `wprot_win_flip` `wprotWinFlip`, `wpacquire_core`
`wpacquireCore`, `wprelease_core` `wpreleaseCore`.  Lean-only: `bigSepLLookupAccSame`
(deviation 8).

**Not ported:** nothing -- every Rocq definition and lemma has a Lean twin.
-/
import Weak.WeakStore
import MachCSL.WeakAuxWeakLock
import MachCSL.MonPredExtra

namespace Weak

open Iris Iris.BI Iris.BI.MonPred Iris.ProofMode Iris.Std
open MachCSL MachCSL.Stdpp

/-- The two values the lock word takes (xv6's `locked` field is an `int`; `acquire` swaps in 1
and `release` stores 0). -/
def lockZero : BitVec 32 := 0#32
def lockOne : BitVec 32 := 1#32

theorem lockOneNeZero : lockOne ≠ lockZero := by decide

/-! ## T2-0: THE TWO MESSAGE SHAPES the lock word's value protocol admits
(`WeakGhost.wlockShaped`), as facts about the messages the two leaves actually append.  The
acquire's is `WCexcl` (pinned by `WeakInstr.wQAmoAqW`); the release's is whatever `wmClassOf`
computed, of which the leaf knows only `≠ WCplain` -- hence the protocol's release arm is keyed
on the VALUE (a zero word), which the leaf does pin. -/

theorem wwriteMsgData4 (tid : Option Nat) (k : WmClass) (a : PAddr) (v : BitVec 32) :
    (wwriteMsg tid k a 4 v).wmData =
      [nthByte (n := 4) v 0, nthByte (n := 4) v 1, nthByte (n := 4) v 2, nthByte (n := 4) v 3] :=
  rfl

theorem lockZeroData4 (tid : Option Nat) (k : WmClass) (a : PAddr) :
    (wwriteMsg tid k a 4 lockZero).wmData = wlockZero4 := by
  rw [wwriteMsgData4, wlockZero4Eq]
  decide

theorem wlockShapedAcq (tid : Option Nat) (a : PAddr) (v : BitVec 32) :
    wlockShaped (wwriteMsg tid .WCexcl a 4 v) :=
  ⟨wwriteMsgLength tid .WCexcl a 4 v, by simp [wwriteMsg], Or.inl rfl⟩

theorem wlockShapedRel (tid : Option Nat) (k : WmClass) (a : PAddr) :
    k ≠ .WCplain → wlockShaped (wwriteMsg tid k a 4 lockZero) :=
  fun hk => ⟨wwriteMsgLength tid k a 4 lockZero, hk, Or.inr (lockZeroData4 tid k a)⟩

/-- T2-0′ (F3′): the ALTERNATION side of the same two messages.  The acquire swaps in ONE,
which is not the zero word. -/
theorem nthByteLockOne0Ne : nthByte (n := 4) lockOne 0 ≠ 0#8 := by decide

theorem lockOneData4Ne (tid : Option Nat) (k : WmClass) (a : PAddr) :
    (wwriteMsg tid k a 4 lockOne).wmData ≠ wlockZero4 := by
  rw [wwriteMsgData4, wlockZero4Eq]
  intro h
  exact nthByteLockOne0Ne (List.cons.inj h).1

/-- The acquire's step: a successful swap on a FREE word installs its author. -/
theorem altStepAcqMsg (i : CPU) (a : PAddr) :
    altStep none (wwriteMsg (some i.val) .WCexcl a 4 lockOne) = some (some i.val) :=
  altStepAcq _ _ (lockOneData4Ne _ _ a) rfl rfl

/-- ... the FAILED swap's: the same message on a HELD word changes nothing. -/
theorem altStepFailMsg (tid : Option Nat) (a : PAddr) (t : Nat) :
    altStep (some t) (wwriteMsg tid .WCexcl a 4 lockOne) = some (some t) :=
  altStepFail _ _ (lockOneData4Ne _ _ a) rfl

/-- ... and the release's: the HOLDER's zero store frees it. -/
theorem altStepRelMsg (i : CPU) (k : WmClass) (a : PAddr) :
    altStep (some i.val) (wwriteMsg (some i.val) k a 4 lockZero) = some none :=
  altStepRel _ _ (lockZeroData4 _ _ a) rfl

/-- `[∗list]` lookup-and-restore at the SAME element (Lean-only, deviation 8). -/
theorem bigSepLLookupAccSame {PROP : Type _} [BI PROP] {A : Type _} {Φ : Nat → A → PROP}
    {l : List A} {i : Nat} {x : A} (h : l[i]? = some x) :
    ([∗list] k ↦ y ∈ l, Φ k y) ⊢ Φ i x ∗ (Φ i x -∗ [∗list] k ↦ y ∈ l, Φ k y) := by
  have hset : l.set i x = l := by
    apply List.ext_getElem?
    intro n
    rw [List.getElem?_set]
    by_cases hin : i = n
    · subst hin
      have hlt : i < l.length := (List.getElem?_eq_some_iff.mp h).1
      rw [if_pos rfl, if_pos hlt, h]
    · rw [if_neg hin]
  refine (BigSepL.bigSepL_lookup_acc h).mp.trans (sep_mono_right ?_)
  refine (forall_elim x).trans ?_
  rw [hset]

/-! ## 2. The lock -/

section weakLock

variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [WeakGS GF] [LockExG GF]

def wlockN : Namespace := ndot nroot "xv6weakspinlock"

/-- T2-0′ (F3′): THE TIE.  The lock's ghost state names the holder; so does the alternation
fold.  `wlockInv` IDENTIFIES the two, which is what makes the fold's step rules discharge
locally at the two leaves. -/
def tidOf (st : LockState) : Option Nat :=
  match st with
  | some (i, _) => some i.val
  | none => none

/-- THE INVARIANT -- an `IProp`, hence objective, hence admissible.  `t` is the timestamp of the
lock word's latest write AND the view the payload is frozen at.  T2-0 (S6 §4/§6b): THE BUNDLE IS
`wlat4L`, NOT `wlat4` -- the lock word's four bytes ride the C/D/S state `WLock`, which makes
the VALUE PROTOCOL an invariant of the state interpretation; the registration point is
EXISTENTIAL inside `wlat4L`. -/
def wlockInv (γ : GName) (lk : PAddr) (R : VProp GF) : IProp GF :=
  iprop(∃ (st : LockState) (t : Nat) (v : BitVec 32),
    wlat4L (GF := GF) lk t v (tidOf st) ∗ lockAuth (GF := GF) γ st ∗
    ((⌜st = none⌝ ∗ ⌜v = lockZero⌝ ∗ lockFrag (GF := GF) γ none ∗ R.monPred_at (viewScl t)) ∨
      (⌜st ≠ none⌝ ∗ ⌜v ≠ lockZero⌝)))

/-- ... so the lock predicate is the embedded invariant: PERSISTENT and OBJECTIVE. -/
def wisLock (γ : GName) (lk : PAddr) (R : VProp GF) : VProp GF :=
  iprop(⎡inv wlockN (wlockInv (GF := GF) γ lk R)⎤)

instance wisLock_persistent (γ : GName) (lk : PAddr) (R : VProp GF) :
    Persistent (wisLock (hlc := hlc) (GF := GF) γ lk R) := by
  unfold wisLock; infer_instance

instance wisLock_objective (γ : GName) (lk : PAddr) (R : VProp GF) :
    Objective (wisLock (hlc := hlc) (GF := GF) γ lk R) := by
  unfold wisLock; infer_instance

/-- THE HOLDER TOKEN IS TODAY'S, unchanged in statement and in algebra. -/
def wlocked (γ : GName) (i : CPU) : VProp GF := iprop(⎡lockedEx (GF := GF) γ i⎤)

instance wlocked_objective (γ : GName) (i : CPU) : Objective (wlocked (GF := GF) γ i) := by
  unfold wlocked; infer_instance

theorem wlockedExclusive (γ : GName) (i j : CPU) :
    wlocked (GF := GF) γ i ⊢ wlocked γ j -∗ False := by
  unfold wlocked
  apply wand_intro
  refine (embed_sep _ _).mpr.trans ?_
  refine (embed_mono (wand_elim (lockedExExclusive γ i j))).trans ?_
  exact (embed_pure False).mp

/-- ALLOCATION -- AND REGISTRATION (T2-0).  A free lock word plus the payload frozen at its
timestamp becomes a lock; the C→`WLock` ghost flip happens HERE, at the current log length. -/
theorem wlockAlloc (lk : PAddr) (R : VProp GF) (t : Nat) (img : GMapF PAddr (BitVec 8))
    (log : List Wmsg) (E : CoPset) :
    wlatInterp (GF := GF) img log ⊢
      wlat4 (GF := GF) lk (DFrac.own 1) t lockZero -∗
        R.monPred_at (viewScl t) -∗
          |={E}=> (wlatInterp (GF := GF) img log ∗
            ∃ γ : GName, inv wlockN (wlockInv (GF := GF) γ lk R)) := by
  iintro Hi Hw HR
  imod wlat4LMint img log lk t lockZero $$ Hi Hw with ⟨Hi, Hw⟩
  imod lockExAlloc (GF := GF) with ⟨%γ, Ha, Hf⟩
  imod inv_alloc wlockN E (wlockInv (GF := GF) γ lk R) $$ [Hw Ha Hf HR] with #Hinv
  · iapply later_intro
    unfold wlockInv
    iexists none, t, lockZero
    dsimp only [tidOf]
    iframe Hw Ha
    ileft
    iframe Hf HR
    ipureintro
    exact ⟨rfl, rfl⟩
  imodintro
  iframe Hi
  iexists γ
  iexact Hinv

/-- T2-0's REGISTRATION SEAM, instantiated: the lock invariant satisfies `wlockRegd` for each
of the word's four bytes. -/
theorem wlockInvRegd (γ : GName) (lk : PAddr) (R : VProp GF) (j : Nat) :
    j < 4 →
    inv wlockN (wlockInv (GF := GF) γ lk R) ⊢
      wlockRegd (hlc := hlc) (GF := GF) wlockN (WeakInterp.accAddr lk j) (paZ lk) := by
  intro hj
  iintro #Hinv
  unfold wlockRegd
  iexists wlockInv (GF := GF) γ lk R
  isplitr
  · iexact Hinv
  imodintro
  iintro Hbody
  unfold wlockInv wlat4L wlat4Lock wlockWin
  icases Hbody with ⟨%st, %t, %v, ⟨%n0, Hel, L0, L1, L2, L3⟩, Ha, Harm⟩
  iexists n0, tidOf st
  have hj' : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
  rcases hj' with rfl | rfl | rfl | rfl
  · iframe L0
    iintro L0
    iexists st, t, v
    iframe Ha Harm
    iexists n0
    iframe Hel L0 L1 L2 L3
  · iframe L1
    iintro L1
    iexists st, t, v
    iframe Ha Harm
    iexists n0
    iframe Hel L0 L1 L2 L3
  · iframe L2
    iintro L2
    iexists st, t, v
    iframe Ha Harm
    iexists n0
    iframe Hel L0 L1 L2 L3
  · iframe L3
    iintro L3
    iexists st, t, v
    iframe Ha Harm
    iexists n0
    iframe Hel L0 L1 L2 L3

/-! ## 3. Reading the lock word out of the invariant

The AMO's read half is `akLatest`, so the ELEMENT bundle alone determines both the value the
swap returns and the timestamp it reads; unlike `WeakInstr.wwpAmoswapWAqInv` this hands the
bundle BACK, because the acquire has to update it afterwards. -/

theorem wlat4FlatGen (σ : Wmstate) (a : PAddr) (dq : DFrac) (t : Nat) (w : BitVec 32) :
    wlogWf σ.wmLog → accWf a 4 →
    wlatInterp (GF := GF) σ.wmImg σ.wmLog ⊢
      wlat4 (GF := GF) a dq t w -∗
        ⌜(∀ j : Nat, j < 4 →
            wflatMem σ.wmImg σ.wmLog (a + BitVec.ofNat 64 j) = some (nthByte (n := 4) w j)) ∧
          (∀ j : Nat, j < 4 → latestTs σ.wmLog (WeakInterp.accAddr a j) = t)⌝ := by
  intro hwf hacc
  unfold wlat4
  iintro Hi ⟨H0, H1, H2, H3⟩
  icases keepPure (wlatByteFlatGen σ a 4 dq t _ 0 hwf hacc (by omega)) $$ Hi H0
    with ⟨%E0, Hi, -⟩
  icases keepPure (wlatByteFlatGen σ a 4 dq t _ 1 hwf hacc (by omega)) $$ Hi H1
    with ⟨%E1, Hi, -⟩
  icases keepPure (wlatByteFlatGen σ a 4 dq t _ 2 hwf hacc (by omega)) $$ Hi H2
    with ⟨%E2, Hi, -⟩
  ihave %E3 := wlatByteFlatGen σ a 4 dq t _ 3 hwf hacc (by omega) $$ Hi H3
  ipureintro
  constructor
  · intro j hj
    rcases j with _ | _ | _ | _ | j
    · exact E0.1
    · exact E1.1
    · exact E2.1
    · exact E3.1
    · omega
  · intro j hj
    rcases j with _ | _ | _ | _ | j
    · exact E0.2
    · exact E1.2
    · exact E2.2
    · exact E3.2
    · omega

/-! ## 4. THE ACQUIRE CORE -- one `amoswap.w.aq`

Open the invariant, hand the machinery the element bundle, and get back the flat lock word and
-- after the step -- the invariant restored at the new timestamp plus, IF the word read was 0,
the payload thawed at the acquirer's OWN index together with the holder token.  The contended
arm is not a no-op on the weak state: the AMO writes 1 back even when it read 1, so the
invariant's elements are retargeted at the new message in BOTH arms. -/

theorem wacquireCore (γ : GName) (lk : PAddr) (R : VProp GF) (i : CPU) (tid : Option Nat)
    (σ σ' : Wmstate) :
    wlogWf σ.wmLog → accWf lk 4 → wQAmoAq tid lk lockOne σ σ' →
    -- T2-0′ (F3′): THE AUTHOR TIE -- the message the step appends is THIS hart's.
    tid = some i.val →
    wlatInterp (GF := GF) σ.wmImg σ.wmLog ⊢
      wlockInv (GF := GF) γ lk R -∗
        ∃ v : BitVec 32,
          ⌜∀ j : Nat, j < 4 →
            wflatMem σ.wmImg σ.wmLog (lk + BitVec.ofNat 64 j) = some (nthByte (n := 4) v j)⌝ ∗
          |==> (wlatInterp (GF := GF) σ'.wmImg σ'.wmLog ∗ wlockInv (GF := GF) γ lk R ∗
            ((⌜v = lockZero⌝ ∗ vwpHold R σ'.wmWs ∗ lockedEx (GF := GF) γ i) ∨
              ⌜v ≠ lockZero⌝)) := by
  intro hwf hacc heff htid
  obtain ⟨⟨himg, -, -, -⟩, hgain, hexcl⟩ := heff
  subst htid
  iintro Hi Hinv
  unfold wlockInv
  icases Hinv with ⟨%st, %t, %v, Hw, Ha, Harm⟩
  icases keepPure (wlat4LFlatGen σ lk t v (tidOf st) hwf hacc) $$ Hi Hw with ⟨%hfl, Hi, Hw⟩
  obtain ⟨hflat, hts⟩ := hfl
  iexists v
  isplitr
  · ipureintro
    exact hflat
  icases Harm with (⟨%hst, %hv, Hfrag, HR⟩ | ⟨%hst, %hv⟩)
  · -- the lock was FREE: a SUCCESSFUL ACQUIRE -- take the lock and thaw the payload
    subst hst
    subst hv
    dsimp only [tidOf]
    imod wlat4LStoreGen (some i.val) .WCexcl σ σ' lk t lockZero lockOne none (some i.val)
        (wlockShapedAcq _ lk lockOne) (altStepAcqMsg i lk) himg hexcl $$ Hi Hw with ⟨Hi, Hw⟩
    imod lockTake γ i $$ Ha Hfrag with ⟨Ha, Hpre⟩
    imod lockSetcpu γ (some (i, false)) i $$ Ha Hpre with ⟨-, Ha, Htok⟩
    imodintro
    iframe Hi
    isplitl [Hw Ha]
    · iexists some (i, true), σ.wmLog.length + 1, lockOne
      dsimp only [tidOf]
      iframe Hw Ha
      iright
      ipureintro
      exact ⟨by simp, lockOneNeZero⟩
    · ileft
      iframe Htok
      -- THE THAW: the payload was frozen at `t`, the acquire's scalar floor now covers `t`
      have hg : viewScl t ≤ wsView σ'.wmWs := by
        have h0 := hgain 0 (by omega)
        rwa [hts 0 (by omega)] at h0
      isplitr
      · ipureintro; rfl
      · iapply vwpHold_intro (viewScl t) R σ'.wmWs hg
        iexact HR
  · -- the lock was HELD: a FAILED swap; the fold keeps the holder, only the timestamp moves
    rcases st with _ | ⟨j, b⟩
    · exact absurd rfl hst
    dsimp only [tidOf]
    imod wlat4LStoreGen (some i.val) .WCexcl σ σ' lk t v lockOne (some j.val) (some j.val)
        (wlockShapedAcq _ lk lockOne) (altStepFailMsg _ lk j.val) himg hexcl $$ Hi Hw
        with ⟨Hi, Hw⟩
    imodintro
    iframe Hi
    isplitl [Hw Ha]
    · iexists some (j, b), σ.wmLog.length + 1, lockOne
      dsimp only [tidOf]
      iframe Hw Ha
      iright
      ipureintro
      exact ⟨by simp, lockOneNeZero⟩
    · iright
      ipureintro
      exact hv

/-! ## 5. THE RELEASE CORE -- `fence rw,w` then `sw zero,0(s1)`

The holder deposits `R` at the timestamp its OWN store takes; sound at the `sw` step ALONE
(`WeakInstr.wwpReleaseDeposit` rests only on `wsBounded`), so the fence contributes NO view
content in this machine -- only the release-pending flag. -/

theorem wreleaseCore (γ : GName) (lk : PAddr) (R : VProp GF) (i : CPU) (tid : Option Nat)
    (σ σ' : Wmstate) :
    wQStore tid lk lockZero σ σ' →
    -- T2-0′ (F3′): THE AUTHOR TIE -- the releasing message is the holder's own.
    tid = some i.val →
    -- φ-upgrade §1: the RELEASE-PENDING flag makes this store's message release-class.
    σ.wmWs.wRelp = true →
    wsBounded σ.wmWs σ.wmLog.length →
    wlatInterp (GF := GF) σ.wmImg σ.wmLog ⊢
      wlockInv (GF := GF) γ lk R -∗
        lockedEx (GF := GF) γ i -∗
          vwpHold R σ.wmWs -∗
            |==> (wlatInterp (GF := GF) σ'.wmImg σ'.wmLog ∗ wlockInv (GF := GF) γ lk R) := by
  intro heff htid hrelp hbnd
  obtain ⟨himg, ⟨kc, hlog, hnp⟩, -, -⟩ := heff
  have hnp := hnp hrelp
  subst htid
  iintro Hi Hinv Htok HR
  unfold wlockInv
  icases Hinv with ⟨%st, %t, %v, Hw, Ha, -⟩
  -- the holder's token says the lock is held by `i` -- hence, by the tie, so does the fold
  icases keepPure (lockedExState γ st i) $$ Ha Htok with ⟨%hst, Ha, Htok⟩
  subst hst
  -- THE DEPOSIT
  ihave HR := wwpReleaseDeposit R σ hbnd $$ HR
  dsimp only [tidOf]
  imod wlat4LStoreGen (some i.val) kc σ σ' lk t v lockZero (some i.val) none
      (wlockShapedRel _ kc lk hnp) (altStepRelMsg i kc lk) himg hlog $$ Hi Hw with ⟨Hi, Hw⟩
  imod lockClrcpu γ (some (i, true)) i $$ Ha Htok with ⟨-, Ha, Hpre⟩
  imod lockGive γ (some (i, false)) i $$ Ha Hpre with ⟨-, Ha, Hfrag⟩
  imodintro
  iframe Hi
  iexists none, σ.wmLog.length + 1, lockZero
  dsimp only [tidOf]
  iframe Hw Ha
  ileft
  iframe Hfrag HR
  ipureintro
  exact ⟨rfl, rfl⟩

/-! ## 6. THE PROTECTED LOCK -- the payload's FOOTPRINT (T2-0′ / F3″, route-b §4d.3′)

`wlockInv` protects a payload `R` by an Iris invariant; NOTHING in it says what the payload's
BYTES are, and that is what route B's cycle kill needs.  `wplockBody` is `wlockInv` with the
payload's FOOTPRINT declared: a list `F` of byte addresses whose C/D/S state is `WProt`,
registered at the same point `n0` as the word itself.

WHY THE FRAGMENTS LIVE IN THE INVARIANT, AND WHY `n0` IS A PARAMETER.  `wprotAt`'s content is
a statement about the fold `wlpHolderAt log base n0 ·`: it is only as good as the registration
point it is stated at, and nothing relates two independently-quantified ones.  So the
footprint's `n0` and the word's must be THE SAME NUMBER -- a resource fact, persistent only by
living in one invariant. -/

variable [WprotG GF]

theorem WeakLock.accAddr0 (a : PAddr) : WeakInterp.accAddr a 0 = paZ a := by
  unfold WeakInterp.accAddr; omega

/-- The dirty author a footprint byte may carry, tied to the lock's state: only the CURRENT
holder may have an outstanding owned store on the payload. -/
def protDok (d : Option CPU) (st : LockState) : Prop :=
  match d with
  | none => True
  | some c => ∃ b : Bool, st = some (c, b)

def wprotWin (γ : GName) (base : Int) (n0 : Nat) (F : List Int) (st : LockState) : IProp GF :=
  iprop([∗list] a ∈ F, ∃ d : Option CPU, wprotSt (GF := GF) a γ base n0 n0 d ∗ ⌜protDok d st⌝)

instance wprotWin_timeless (γ : GName) (base : Int) (n0 : Nat) (F : List Int) (st : LockState) :
    Timeless (wprotWin (GF := GF) γ base n0 F st) := by
  unfold wprotWin; infer_instance

/-- A state change that only ever WIDENS what `protDok` allows -- the acquire's
`none → some (i, b)` -- leaves the window alone. -/
theorem wprotWinFree (γ : GName) (base : Int) (n0 : Nat) (F : List Int) (st : LockState) :
    wprotWin (GF := GF) γ base n0 F none ⊢ wprotWin γ base n0 F st := by
  unfold wprotWin
  refine BigSepL.bigSepL_mono_of_forall (@fun _ a => ?_)
  iintro ⟨%d, Hpr, %hd⟩
  rcases d with _ | c
  · iexists none
    iframe Hpr
    ipureintro
    trivial
  · obtain ⟨b, hb⟩ := hd
    cases hb

def wplockBody (γ γr : GName) (lk : PAddr) (R : VProp GF) (n0 : Nat) (F : List Int) :
    IProp GF :=
  iprop(∃ (st : LockState) (t : Nat) (v : BitVec 32) (L : List (Int × Nat)),
    wlat4Lock (GF := GF) lk n0 t v (tidOf st) ∗ lockAuth (GF := GF) γ st ∗
    wprotWin (GF := GF) γ (paZ lk) n0 F st ∗
    protRecs (GF := GF) γr L ∗ ⌜protRecsOk n0 L⌝ ∗
    ((⌜st = none⌝ ∗ ⌜v = lockZero⌝ ∗ lockFrag (GF := GF) γ none ∗ R.monPred_at (viewScl t)) ∨
      (⌜st ≠ none⌝ ∗ ⌜v ≠ lockZero⌝)))

/-- It IS a lock invariant -- the footprint and the records are extra. -/
theorem wplockBodyInv (γ γr : GName) (lk : PAddr) (R : VProp GF) (n0 : Nat) (F : List Int) :
    wplockBody (GF := GF) γ γr lk R n0 F ⊢ wlockInv γ lk R := by
  unfold wplockBody wlockInv
  iintro ⟨%st, %t, %v, %L, Hw, Ha, -, -, -, Harm⟩
  iexists st, t, v
  isplitl [Hw]
  · unfold wlat4L
    iexists n0
    iexact Hw
  · iframe Ha Harm

/-! ### 6a. REGISTRATION -/

/-- The whole footprint at once: full-fraction CLEAN fragments in, `WProt` fragments out, all
at the current log length -- where the protection clause is vacuous. -/
theorem wprotRegisterList (img : GMapF PAddr (BitVec 8)) (log : List Wmsg) (F : List Int)
    (γ : GName) (base : Int) :
    wlatInterp (GF := GF) img log ⊢
      ([∗list] a ∈ F, wclean (GF := GF) a (DFrac.own 1)) -∗
        |==> (wlatInterp (GF := GF) img log ∗ wprotWin (GF := GF) γ base log.length F none) := by
  induction F with
  | nil =>
    iintro Hi -
    imodintro
    iframe Hi
    unfold wprotWin
    iapply BigSepL.bigSepL_nil.mpr
    iempintro
  | cons a F ih =>
    unfold wprotWin at ih ⊢
    iintro Hi HF
    icases BigSepL.bigSepL_cons.mp $$ HF with ⟨Ha, HF⟩
    imod wprotRegister img log a γ base log.length (Nat.le_refl _) $$ [Hi Ha] with ⟨Hi, Hpr⟩
    · iframe Hi Ha
    imod ih $$ Hi HF with ⟨Hi, Htl⟩
    imodintro
    iframe Hi
    iapply BigSepL.bigSepL_cons.mpr
    iframe Htl
    iexists none
    iframe Hpr
    ipureintro
    trivial

/-- DEREGISTRATION, purely at the ghost level: with the lock free every byte's dirty author is
`none`, so the whole footprint comes back as ordinary clean fragments. -/
theorem wprotDeregisterList (img : GMapF PAddr (BitVec 8)) (log : List Wmsg) (F : List Int)
    (γ : GName) (base : Int) (n0 : Nat) :
    wlatInterp (GF := GF) img log ⊢
      wprotWin (GF := GF) γ base n0 F none -∗
        |==> (wlatInterp (GF := GF) img log ∗ [∗list] a ∈ F, wclean (GF := GF) a (DFrac.own 1)) := by
  induction F with
  | nil =>
    iintro Hi -
    imodintro
    iframe Hi
    iapply BigSepL.bigSepL_nil.mpr
    iempintro
  | cons a F ih =>
    unfold wprotWin at ih ⊢
    iintro Hi HF
    icases BigSepL.bigSepL_cons.mp $$ HF with ⟨Ha, HF⟩
    icases Ha with ⟨%d, Hpr, %hd⟩
    rcases d with _ | c
    · imod wprotDeregister img log a γ base n0 n0 $$ [Hi Hpr] with ⟨Hi, Hcl⟩
      · iframe Hi Hpr
      imod ih $$ Hi HF with ⟨Hi, Htl⟩
      imodintro
      iframe Hi
      iapply BigSepL.bigSepL_cons.mpr
      iframe Hcl Htl
    · obtain ⟨b, hb⟩ := hd
      cases hb

/-- THE ALLOCATION.  `wlockAlloc`'s protected twin: the lock word AND the declared footprint
are registered in the same instant, so they share the registration point. -/
theorem wplockAlloc (lk : PAddr) (R : VProp GF) (F : List Int) (t : Nat)
    (img : GMapF PAddr (BitVec 8)) (log : List Wmsg) (E : CoPset) :
    wlatInterp (GF := GF) img log ⊢
      wlat4 (GF := GF) lk (DFrac.own 1) t lockZero -∗
        ([∗list] a ∈ F, wclean (GF := GF) a (DFrac.own 1)) -∗
          R.monPred_at (viewScl t) -∗
            |={E}=> (wlatInterp (GF := GF) img log ∗
              ∃ γ γr : GName, inv wlockN (wplockBody (GF := GF) γ γr lk R log.length F)) := by
  iintro Hi Hw HF HR
  imod lockExAlloc (GF := GF) with ⟨%γ, Ha, Hf⟩
  imod protRecsAlloc (GF := GF) with ⟨%γr, Hrecs⟩
  imod wlat4LockMint img log lk t lockZero $$ Hi Hw with ⟨Hi, Hw⟩
  imod wprotRegisterList img log F γ (paZ lk) $$ Hi HF with ⟨Hi, Hwin⟩
  imod inv_alloc wlockN E (wplockBody (GF := GF) γ γr lk R log.length F)
      $$ [Hw Ha Hf HR Hwin Hrecs] with #Hinv
  · iapply later_intro
    unfold wplockBody
    iexists none, t, lockZero, []
    dsimp only [tidOf]
    iframe Hw Ha Hwin Hrecs
    isplitr
    · ipureintro
      intro ap hap
      cases hap
    · ileft
      iframe Hf HR
      ipureintro
      exact ⟨rfl, rfl⟩
  imodintro
  iframe Hi
  iexists γ, γr
  iexact Hinv

/-! ### 6b. THE ADEQUACY SEAMS

`wlockInvRegd`'s twins.  Both hand out the byte's `WProt` fragment TOGETHER WITH the lock
word's byte-0 `WLock` fragment at the same `n0`. -/

theorem wplockInvRegd (γ γr : GName) (lk : PAddr) (R : VProp GF) (n0 : Nat) (F : List Int)
    (a : Int) :
    a ∈ F →
    inv wlockN (wplockBody (GF := GF) γ γr lk R n0 F) ⊢
      wprotRegd (hlc := hlc) (GF := GF) wlockN a (paZ lk) := by
  intro hin
  obtain ⟨k, hk⟩ := List.getElem?_of_mem hin
  iintro #Hinv
  unfold wprotRegd
  iexists wplockBody (GF := GF) γ γr lk R n0 F
  isplitr
  · iexact Hinv
  imodintro
  iintro Hbody
  unfold wplockBody wlat4Lock wlockWin wprotWin
  icases Hbody with ⟨%st, %t, %v, %L, ⟨Hel, L0, L1, L2, L3⟩, Ha, Hwin, Hrec, %hok, Harm⟩
  icases bigSepLLookupAccSame hk $$ Hwin with ⟨Hb, Hwin⟩
  icases Hb with ⟨%d, Hpr, %hd⟩
  rw [WeakLock.accAddr0]
  iexists γ, n0, n0, d, tidOf st
  iframe Hpr L0
  iintro Hpr L0
  iexists st, t, v, L
  iframe Ha Hrec Harm Hel L0 L1 L2 L3
  isplitl [Hwin Hpr]
  · iapply Hwin
    iexists d
    iframe Hpr
    ipureintro
    exact hd
  · ipureintro
    exact hok

theorem wplockInvRdRegd (γ γr : GName) (lk : PAddr) (R : VProp GF) (n0 : Nat) (F : List Int)
    (a : Int) :
    a ∈ F →
    inv wlockN (wplockBody (GF := GF) γ γr lk R n0 F) ⊢
      wprotRdRegd (hlc := hlc) (GF := GF) wlockN γr a (paZ lk) := by
  intro hin
  obtain ⟨k, hk⟩ := List.getElem?_of_mem hin
  iintro #Hinv
  unfold wprotRdRegd
  iexists wplockBody (GF := GF) γ γr lk R n0 F
  isplitr
  · iexact Hinv
  imodintro
  iintro Hbody
  unfold wplockBody wlat4Lock wlockWin wprotWin
  icases Hbody with ⟨%st, %t, %v, %L, ⟨Hel, L0, L1, L2, L3⟩, Ha, Hwin, Hrec, %hok, Harm⟩
  icases bigSepLLookupAccSame hk $$ Hwin with ⟨Hb, Hwin⟩
  icases Hb with ⟨%d, Hpr, %hd⟩
  rw [WeakLock.accAddr0]
  iexists γ, n0, n0, d, tidOf st, L
  iframe Hpr L0 Hrec
  isplitr
  · ipureintro
    exact hok
  iintro Hpr L0 Hrec
  iexists st, t, v, L
  iframe Ha Hrec Harm Hel L0 L1 L2 L3
  isplitl [Hwin Hpr]
  · iapply Hwin
    iexists d
    iframe Hpr
    ipureintro
    exact hd
  · ipureintro
    exact hok

/-! ### 6c. THE PROTECTED STORE AND THE READ RECORD -/

/-- The holder fact, off the invariant and the token: the lock word's fold names THIS hart at
the log's top -- the premise of the pure protected-store rule. -/
theorem wplockHolder (γ γr : GName) (lk : PAddr) (R : VProp GF) (n0 : Nat) (F : List Int)
    (i : CPU) (img : GMapF PAddr (BitVec 8)) (log : List Wmsg) :
    wlatInterp (GF := GF) img log ⊢
      wplockBody (GF := GF) γ γr lk R n0 F -∗
        lockedEx (GF := GF) γ i -∗
          ⌜wlpHolderAt log (paZ lk) n0 log.length = some (some i.val)⌝ := by
  iintro Hi Hbody Htok
  unfold wplockBody wlat4Lock wlockWin
  icases Hbody with ⟨%st, %t, %v, %L, ⟨-, L0, -, -, -⟩, Ha, -, -, -, -⟩
  icases keepPure (lockedExState γ st i) $$ Ha Htok with ⟨%hst, -, -⟩
  subst hst
  ihave %hf := wlpAltOfLock img log _ _ n0 _ $$ [Hi L0]
  · iframe Hi L0
  ipureintro
  have h2 := hf.2
  rwa [WeakLock.accAddr0] at h2

/-- THE PROTECTED STORE, at the altitude the two lock cores are stated at: the message the step
appended is an OWNED store of this hart to a footprint byte, legal because the token says this
hart holds the lock. -/
theorem wprotStoreCore (γ γr : GName) (lk : PAddr) (R : VProp GF) (n0 : Nat) (F : List Int)
    (i : CPU) (a : Int) (m : Wmsg) (σ σ' : Wmstate) (t : Nat) (w b : BitVec 8) :
    a ∈ F →
    msgByte m a = some b → (∀ a', a' ≠ a → msgByte m a' = none) →
    m.wmAk = .WCplain → m.wmTid = some i.val →
    σ'.wmImg = σ.wmImg → σ'.wmLog = σ.wmLog ++ [m] →
    wlatInterp (GF := GF) σ.wmImg σ.wmLog ⊢
      wplockBody (GF := GF) γ γr lk R n0 F -∗
        lockedEx (GF := GF) γ i -∗
          wlatElem (GF := GF) a (DFrac.own 1) t w -∗
            |==> (wlatInterp (GF := GF) σ'.wmImg σ'.wmLog ∗
              wplockBody (GF := GF) γ γr lk R n0 F ∗ lockedEx (GF := GF) γ i ∗
              wlatElem (GF := GF) a (DFrac.own 1) (σ.wmLog.length + 1) b) := by
  intro hin hma hother hk htid himg hlog
  obtain ⟨j, hj⟩ := List.getElem?_of_mem hin
  iintro Hi Hbody Htok Hel
  unfold wplockBody wlat4Lock wlockWin wprotWin
  icases Hbody with ⟨%st, %t0, %v, %L, ⟨Hel4, L0, L1, L2, L3⟩, Ha, Hwin, Hrec, %hok, Harm⟩
  icases keepPure (lockedExState γ st i) $$ Ha Htok with ⟨%hst, Ha, Htok⟩
  subst hst
  -- the holder fact (`wplockHolder`'s content, deviation 9)
  icases keepPure (wand_intro (wlpAltOfLock σ.wmImg σ.wmLog _ _ n0 _)) $$ Hi L0
    with ⟨%halt, Hi, L0⟩
  have hhold : wlpHolderAt σ.wmLog (paZ lk) n0 σ.wmLog.length = some (some i.val) := by
    have h2 := halt.2
    rwa [WeakLock.accAddr0] at h2
  icases bigSepLLookupAccSame hj $$ Hwin with ⟨Hb, Hwin⟩
  icases Hb with ⟨%d, Hpr, %hd⟩
  have hdd : d = none ∨ d = some i := by
    rcases d with _ | c
    · exact Or.inl rfl
    · obtain ⟨bb, hbb⟩ := hd
      cases hbb
      exact Or.inr rfl
  imod wprotStore σ.wmImg σ.wmLog m a γ (paZ lk) n0 n0 d i t w b hk htid hdd hhold hma hother
      $$ [Hi Hel Hpr] with ⟨Hi, Hel, Hpr⟩
  · iframe Hi Hel Hpr
  imodintro
  rw [himg, hlog]
  iframe Hi Hel Htok
  iexists some (i, true), t0, v, L
  iframe Ha Hel4 L0 L1 L2 L3 Hrec Harm
  isplitl [Hwin Hpr]
  · iapply Hwin
    iexists some i
    iframe Hpr
    ipureintro
    exact ⟨true, rfl⟩
  · ipureintro
    exact hok

/-- THE READ RECORD: a persistent receipt that byte `a` of this lock's payload was read at log
position `p` (`n0 ≤ p`). -/
theorem wprotReadRecord (γ γr : GName) (lk : PAddr) (R : VProp GF) (n0 : Nat) (F : List Int)
    (a : Int) (p : Nat) :
    n0 ≤ p →
    wplockBody (GF := GF) γ γr lk R n0 F ⊢
      |==> (wplockBody (GF := GF) γ γr lk R n0 F ∗ protRead (GF := GF) γr a p) := by
  intro hp
  unfold wplockBody
  iintro ⟨%st, %t, %v, %L, Hw, Ha, Hwin, Hrec, %hok, Harm⟩
  imod protRecsAppend γr L a p $$ Hrec with ⟨Hrec, #Hrd⟩
  imodintro
  iframe Hrd
  iexists st, t, v, L ++ [(a, p)]
  iframe Hw Ha Hwin Hrec Harm
  ipureintro
  intro ap hap
  rcases List.mem_append.1 hap with hap | hap
  · exact hok ap hap
  · rw [List.mem_singleton] at hap
    subst hap
    exact hp

/-! ### 6d. THE TWO CORES, AT A FIXED REGISTRATION POINT

`wacquireCore` / `wreleaseCore` verbatim, over `wplockBody` instead of `wlockInv`.  The only
NEW content is what happens to the footprint window: the ACQUIRE takes the lock from FREE, where
every payload byte's dirty author is `none`, so the window survives by `wprotWinFree`; the
RELEASE hands it back, and its `WCrel` message publishes the holder's whole owned backlog -- so
every payload byte flips D→C (`wprotWinFlip`).  That is why this core needs the release
message's class PINNED at `WCrel`. -/

theorem wprotWinFlip (img : GMapF PAddr (BitVec 8)) (log : List Wmsg) (mrel : Wmsg)
    (γ : GName) (base : Int) (n0 : Nat) (F : List Int) (i : CPU) (bb : Bool) :
    mrel.wmTid = some i.val → mrel.wmAk = .WCrel →
    wlatInterp (GF := GF) img (log ++ [mrel]) ⊢
      wprotWin (GF := GF) γ base n0 F (some (i, bb)) -∗
        |==> (wlatInterp (GF := GF) img (log ++ [mrel]) ∗ wprotWin (GF := GF) γ base n0 F none) := by
  intro htid hk
  induction F with
  | nil =>
    iintro Hi -
    imodintro
    iframe Hi
    unfold wprotWin
    iapply BigSepL.bigSepL_nil.mpr
    iempintro
  | cons a F ih =>
    unfold wprotWin at ih ⊢
    iintro Hi HF
    icases BigSepL.bigSepL_cons.mp $$ HF with ⟨Ha, HF⟩
    icases Ha with ⟨%d, Hpr, %hd⟩
    imod ih $$ Hi HF with ⟨Hi, Htl⟩
    rcases d with _ | c
    · imodintro
      iframe Hi
      iapply BigSepL.bigSepL_cons.mpr
      iframe Htl
      iexists none
      iframe Hpr
      ipureintro
      trivial
    · obtain ⟨b0, hb0⟩ := hd
      cases hb0
      imod wprotFlip img log mrel i a γ base n0 n0 htid hk $$ [Hi Hpr] with ⟨Hi, Hpr⟩
      · iframe Hi Hpr
      imodintro
      iframe Hi
      iapply BigSepL.bigSepL_cons.mpr
      iframe Htl
      iexists none
      iframe Hpr
      ipureintro
      trivial

theorem wpacquireCore (γ γr : GName) (lk : PAddr) (R : VProp GF) (n0 : Nat) (F : List Int)
    (i : CPU) (tid : Option Nat) (σ σ' : Wmstate) :
    wlogWf σ.wmLog → accWf lk 4 → wQAmoAq tid lk lockOne σ σ' →
    tid = some i.val →
    wlatInterp (GF := GF) σ.wmImg σ.wmLog ⊢
      wplockBody (GF := GF) γ γr lk R n0 F -∗
        ∃ v : BitVec 32,
          ⌜∀ j : Nat, j < 4 →
            wflatMem σ.wmImg σ.wmLog (lk + BitVec.ofNat 64 j) = some (nthByte (n := 4) v j)⌝ ∗
          |==> (wlatInterp (GF := GF) σ'.wmImg σ'.wmLog ∗
            wplockBody (GF := GF) γ γr lk R n0 F ∗
            ((⌜v = lockZero⌝ ∗ vwpHold R σ'.wmWs ∗ lockedEx (GF := GF) γ i) ∨
              ⌜v ≠ lockZero⌝)) := by
  intro hwf hacc heff htid
  obtain ⟨⟨himg, -, -, -⟩, hgain, hexcl⟩ := heff
  subst htid
  iintro Hi Hbody
  unfold wplockBody
  icases Hbody with ⟨%st, %t, %v, %L, Hw, Ha, Hwin, Hrec, %hok, Harm⟩
  icases keepPure (wlat4LockFlatGen σ lk n0 t v (tidOf st) hwf hacc) $$ Hi Hw
    with ⟨%hfl, Hi, Hw⟩
  obtain ⟨hflat, hts⟩ := hfl
  iexists v
  isplitr
  · ipureintro
    exact hflat
  icases Harm with (⟨%hst, %hv, Hfrag, HR⟩ | ⟨%hst, %hv⟩)
  · -- FREE: a successful acquire, and the window widens for free
    subst hst
    subst hv
    dsimp only [tidOf]
    imod wlat4LockStoreGen (some i.val) .WCexcl σ σ' lk n0 t lockZero lockOne none (some i.val)
        (wlockShapedAcq _ lk lockOne) (altStepAcqMsg i lk) himg hexcl $$ Hi Hw with ⟨Hi, Hw⟩
    imod lockTake γ i $$ Ha Hfrag with ⟨Ha, Hpre⟩
    imod lockSetcpu γ (some (i, false)) i $$ Ha Hpre with ⟨-, Ha, Htok⟩
    ihave Hwin := wprotWinFree γ (paZ lk) n0 F (some (i, true)) $$ Hwin
    imodintro
    iframe Hi
    isplitl [Hw Ha Hwin Hrec]
    · iexists some (i, true), σ.wmLog.length + 1, lockOne, L
      dsimp only [tidOf]
      iframe Hw Ha Hwin Hrec
      isplitr
      · ipureintro
        exact hok
      · iright
        ipureintro
        exact ⟨by simp, lockOneNeZero⟩
    · ileft
      iframe Htok
      have hg : viewScl t ≤ wsView σ'.wmWs := by
        have h0 := hgain 0 (by omega)
        rwa [hts 0 (by omega)] at h0
      isplitr
      · ipureintro; rfl
      · iapply vwpHold_intro (viewScl t) R σ'.wmWs hg
        iexact HR
  · -- HELD: a failed swap; nothing about the footprint moves
    rcases st with _ | ⟨j, b⟩
    · exact absurd rfl hst
    dsimp only [tidOf]
    imod wlat4LockStoreGen (some i.val) .WCexcl σ σ' lk n0 t v lockOne (some j.val) (some j.val)
        (wlockShapedAcq _ lk lockOne) (altStepFailMsg _ lk j.val) himg hexcl $$ Hi Hw
        with ⟨Hi, Hw⟩
    imodintro
    iframe Hi
    isplitl [Hw Ha Hwin Hrec]
    · iexists some (j, b), σ.wmLog.length + 1, lockOne, L
      dsimp only [tidOf]
      iframe Hw Ha Hwin Hrec
      isplitr
      · ipureintro
        exact hok
      · iright
        ipureintro
        exact ⟨by simp, lockOneNeZero⟩
    · iright
      ipureintro
      exact hv

theorem wpreleaseCore (γ γr : GName) (lk : PAddr) (R : VProp GF) (n0 : Nat) (F : List Int)
    (i : CPU) (tid : Option Nat) (σ σ' : Wmstate) :
    wQStore tid lk lockZero σ σ' →
    tid = some i.val →
    -- the release's message is RELEASE-CLASS, not merely non-plain: it is what publishes the
    -- footprint's owned backlog
    σ'.wmLog = σ.wmLog ++ [wwriteMsg tid .WCrel lk 4 lockZero] →
    wsBounded σ.wmWs σ.wmLog.length →
    wlatInterp (GF := GF) σ.wmImg σ.wmLog ⊢
      wplockBody (GF := GF) γ γr lk R n0 F -∗
        lockedEx (GF := GF) γ i -∗
          vwpHold R σ.wmWs -∗
            |==> (wlatInterp (GF := GF) σ'.wmImg σ'.wmLog ∗
              wplockBody (GF := GF) γ γr lk R n0 F) := by
  intro heff htid hrel hbnd
  obtain ⟨himg, -, -, -⟩ := heff
  subst htid
  iintro Hi Hbody Htok HR
  unfold wplockBody
  icases Hbody with ⟨%st, %t, %v, %L, Hw, Ha, Hwin, Hrec, %hok, -⟩
  icases keepPure (lockedExState γ st i) $$ Ha Htok with ⟨%hst, Ha, Htok⟩
  subst hst
  ihave HR := wwpReleaseDeposit R σ hbnd $$ HR
  dsimp only [tidOf]
  imod wlat4LockStoreGen (some i.val) .WCrel σ σ' lk n0 t v lockZero (some i.val) none
      (wlockShapedRel _ .WCrel lk (by decide)) (altStepRelMsg i .WCrel lk) himg hrel $$ Hi Hw
      with ⟨Hi, Hw⟩
  imod lockClrcpu γ (some (i, true)) i $$ Ha Htok with ⟨-, Ha, Hpre⟩
  imod lockGive γ (some (i, false)) i $$ Ha Hpre with ⟨-, Ha, Hfrag⟩
  -- THE FOOTPRINT FLIP: the release message is the log's last and is `WCrel`
  rw [himg, hrel]
  imod wprotWinFlip σ.wmImg σ.wmLog (wwriteMsg (some i.val) .WCrel lk 4 lockZero) γ (paZ lk) n0 F
      i true rfl rfl $$ Hi Hwin with ⟨Hi, Hwin⟩
  imodintro
  iframe Hi
  iexists none, σ.wmLog.length + 1, lockZero, L
  dsimp only [tidOf]
  iframe Hw Ha Hwin Hrec
  isplitr
  · ipureintro
    exact hok
  · ileft
    iframe Hfrag HR
    ipureintro
    exact ⟨rfl, rfl⟩

end weakLock

end Weak
