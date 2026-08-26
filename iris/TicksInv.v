(* TicksInv.v -- the tick counter [ticks] and the spinlock that owns it
   ([tickslock]), mirroring SleepLock.v one level down: a small definitional
   layer over WpLock.v that names

     a_ticks        -- &ticks       (the 4-byte global tick counter)
     a_tickslock    -- &tickslock   (the spinlock guarding it)
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
Require Import TsoCtx.   (* the lock payload's context axis; [<{ }>] *)
From Kernel Require KernelSyms.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Local Open Scope Z_scope.

Section TicksInv.
  Context `{!riscvGS Σ, !xv6G Σ}.
  Context `{XI : CurCtx}.

  (* ---- geometry.  The lock's own two words ([locked] at +0, [cpu] at +16)
     belong to [lock_inv] (WpLock.v); nothing here names the cpu word. *)
  Definition a_ticks : mword 64 := mword_of_int KernelSyms.ticks.
  Definition a_tickslock : mword 64 := mword_of_int KernelSyms.tickslock.

  (* the protected resource: the counter cell, contents existential. *)
  Definition ticks_res : iProp Σ := (∃ t : mword 32, a_ticks ↦₄ t)%I.

  Lemma ticks_res_intro (t : mword 32) : a_ticks ↦₄ t -∗ ticks_res.
  Proof. iIntros "H". iExists t. iFrame "H". Qed.

  Definition is_tickslock (γl : gname) : iProp Σ :=
    is_lock γl a_tickslock "time"%string <{ ticks_res }>.

  Global Instance is_tickslock_persistent γl : Persistent (is_tickslock γl).
  Proof. apply _. Qed.

  Lemma is_tickslock_lock γl :
    is_tickslock γl -∗ is_lock γl a_tickslock "time"%string <{ ticks_res }>.
  Proof. iIntros "$". Qed.

  (* ---- construction (the "newlock" ghost step): what a caller does with
     trapinit's postcondition -- the freshly zeroed lock word and its
     persistent name, plus the counter cell, become the tickslock. *)
  Lemma new_tickslock E (t : mword 32) :
    lock_name a_tickslock "time"%string -∗
    a_tickslock ↦₄ (mword_of_int 0 : mword 32) -∗
    lock_cpu a_tickslock ↦₈ (zero_reg : mword 64) -∗
    a_ticks ↦₄ t ={E}=∗ ∃ γl : gname, is_tickslock γl.
  Proof.
    iIntros "#Hnm Hlkw Hcpu Hticks".
    iApply (newlock E a_tickslock "time"%string <{ ticks_res }>
              with "Hnm Hlkw Hcpu [Hticks]").
    iApply (ticks_res_intro with "Hticks").
  Qed.

End TicksInv.
