(* TicksInv.v -- the tick counter [ticks] and the spinlock that owns it
   ([tickslock]), mirroring SleepLock.v one level down: a small definitional
   layer over WpLock.v that names

     a_ticks        -- &ticks       (the 4-byte global tick counter)
     a_tickslock    -- &tickslock   (the spinlock guarding it)
     tickslock_cpu  -- &tickslock->cpu, in acquire/release's [a_cpu] form
     ticks_res      -- the resource the lock protects
     is_tickslock   -- the lock itself (persistent)

   [ticks_res] is deliberately the WEAKEST useful invariant: ownership of the
   counter cell at an ARBITRARY value.  That is all sys_uptime needs (it hands
   the value it read straight back to the caller), and it is all clockintr can
   maintain without a ghost tick history.  When a client appears that must
   relate ticks to something else (sleep/wakeup on the tick channel), the
   resource -- not this file's interface -- is what changes: strengthen
   [ticks_res] and every lock user keeps compiling.

   The lock's name is the literal "time" that trapinit passes to initlock, so
   [is_tickslock] is exactly what a caller can seal from trapinit's
   postcondition ([new_tickslock] is that ghost step). *)
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import excl.
From iris.base_logic.lib Require Import invariants own.
Require Import SailStdpp.Base SailStdpp.Operators_mwords.
Require Import Riscv.rv64d.
Require Import RiscvPtsto.
Require Import WpLock.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.

Section TicksInv.
  Context `{!riscvGS Σ, !lockG Σ}.

  (* ---- geometry.  [tickslock_cpu] is spelled in acquire/release's [a_cpu]
     form (lk + sign_extend' 64 16) so the cell unifies with their specs
     without rewriting. *)
  Definition a_ticks : mword 64 := mword_of_int KernelSyms.ticks.
  Definition a_tickslock : mword 64 := mword_of_int KernelSyms.tickslock.
  Definition tickslock_cpu : mword 64 :=
    add_vec a_tickslock (sign_extend' 64 (mword_of_int 16 : mword 12)).

  (* the protected resource: the counter cell, contents existential. *)
  Definition ticks_res : iProp Σ := (∃ t : mword 32, a_ticks ↦₄ t)%I.

  Lemma ticks_res_intro (t : mword 32) : a_ticks ↦₄ t -∗ ticks_res.
  Proof. iIntros "H". iExists t. iFrame "H". Qed.

  Definition is_tickslock (γl : gname) : iProp Σ :=
    is_lock γl a_tickslock "time"%string ticks_res.

  Global Instance is_tickslock_persistent γl : Persistent (is_tickslock γl).
  Proof. apply _. Qed.

  Lemma is_tickslock_lock γl :
    is_tickslock γl -∗ is_lock γl a_tickslock "time"%string ticks_res.
  Proof. iIntros "$". Qed.

  (* ---- construction (the "newlock" ghost step): what a caller does with
     trapinit's postcondition -- the freshly zeroed lock word and its
     persistent name, plus the counter cell, become the tickslock. *)
  Lemma new_tickslock E (t : mword 32) :
    lock_name a_tickslock "time"%string -∗
    a_tickslock ↦₄ (mword_of_int 0 : mword 32) -∗
    a_ticks ↦₄ t ={E}=∗ ∃ γl : gname, is_tickslock γl.
  Proof.
    iIntros "#Hnm Hlkw Hticks".
    iMod (own_alloc (Excl () : exclR unitO)) as (γl) "Htok"; [done|].
    iMod (inv_alloc lockN E (lock_inv γl a_tickslock ticks_res)
            with "[Hlkw Htok Hticks]") as "#Hinv".
    { iNext. iExists (mword_of_int 0 : mword 32). rewrite /lock_word.
      iFrame "Hlkw". iLeft. iSplit; [done|]. iFrame "Htok".
      iApply (ticks_res_intro with "Hticks"). }
    iModIntro. iExists γl.
    iApply (is_lock_intro with "Hnm Hinv").
  Qed.

End TicksInv.
