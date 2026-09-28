(* TicksInv.v -- the tick counter [ticks] and the spinlock that owns it
   ([tickslock]), mirroring SleepLock.v one level down: a small definitional
   layer over WpLock.v that names

     a_ticks        -- &ticks       (the 4-byte global tick counter)
     a_tickslock    -- &tickslock   (the spinlock guarding it)
     ticks_res      -- the resource the lock protects
     is_tickslock   -- the lock itself (persistent)

   HISTORY: [ticks_res] was first the WEAKEST useful invariant -- the cell at
   an ARBITRARY value -- with the note that a client relating ticks to
   something else would strengthen the resource, not this interface.  The
   noninterference campaign is that client (design ni-ticks-ledger.md): the
   payload now also holds the tick counter's MIRROR, [WaitInv.tick_cnt n]
   at the canonical name [Xv6Cameras.wtk_name] (D1), tied to the 32-bit
   cell modulo 2^32 ([ticks_tie], D2: [ticks++] wraps, the mirror does
   not).  The clock interrupt steps both; main raises the mirror to the
   cell's boot value before sealing; sys_uptime hands back a lower bound
   ([WaitInv.tick_lb]) as its receipt.  The price is one binder: the
   section now binds [!wchG Σ], the class that carries the name.

   The lock's name is the literal "time" that trapinit passes to initlock, so
   [is_tickslock] is exactly what a caller can seal from trapinit's
   postcondition ([new_tickslock] is that ghost step). *)
From Stdlib Require Import ZArith Znumtheory Lia.
From stdpp Require Import bitvector.definitions bitvector.tactics.
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
Require Import RiscvExtras.   (* [trunc32] and the unsigned readings *)
Require Import CtxMorphTac.
Require Import Xv6Cameras.    (* [wchG]: the class carrying [wtk_name] *)
Require Import WaitInv.       (* [tick_cnt]: the tick counter's mirror *)
Local Open Scope Z_scope.

Section TicksInv.
  Context `{!riscvGS Σ, !xv6G Σ}.
  Context `{!wchG Σ}.
  Context `{XI : CurCtx}.

  (* ---- geometry.  The lock's own two words ([locked] at +0, [cpu] at +16)
     belong to [lock_inv] (WpLock.v); nothing here names the cpu word. *)
  Definition a_ticks : mword 64 := mword_of_int KernelSyms.ticks.
  Definition a_tickslock : mword 64 := mword_of_int KernelSyms.tickslock.

  (* THE TIE (design ni-ticks-ledger.md D2, ruling R3): the 32-bit cell is
     the mirror's count modulo 2^32 -- [ticks] is a C [uint] and wraps, the
     count does not. *)
  Definition ticks_tie (t : mword 32) (n : nat) : Prop :=
    bv_unsigned t = (Z.of_nat n) `mod` (2 ^ 32).

  (* the protected resource: the counter cell and the mirror, tied. *)
  (* >>> A6.121 (the M3 λ-conversion, PILOT): the payload over an EXPLICIT
     context.  [ticks_res_at ξ] is what the lock surface takes as its
     [CtxId → iProp] -- so the invariant's free arm holds the cell at the
     PARKED record's context and acquire's absorb re-indexes it to the
     winner's, by a REAL transport proof ([CtxMorph], discharged here by the
     structural instances) instead of the constant embedding [<{ }>], which
     froze the payload at whichever context spelled it.  [ticks_res] stays
     as the ambient spelling every consumer already reads and writes. <<< *)
  Definition ticks_res_at (ξ : CtxId) : iProp Σ :=
    (∃ (t : mword 32) (n : nat),
       ctx_word4_pointsto ξ a_ticks (DfracOwn 1) t ∗ tick_cnt n ∗ ⌜ticks_tie t n⌝)%I.
  Definition ticks_res : iProp Σ := ticks_res_at cur_ctx.

  Global Instance ticks_res_at_morph : CtxMorph ticks_res_at.
  Proof using . rewrite /ticks_res_at. ctx_morph_solve. Qed.

  Lemma ticks_res_intro (t : mword 32) (n : nat) :
    ticks_tie t n -> a_ticks ↦₄ t -∗ tick_cnt n -∗ ticks_res.
  Proof using .
    iIntros (Htie) "H Hc". rewrite /ticks_res /ticks_res_at.
    iExists t, n. iFrame "H Hc". iPureIntro. exact Htie.
  Qed.

  (* the clock interrupt's increment, stated on EXACTLY the word its
     [c.sw] commits: [trunc32] of the [c.addiw a5,1] result over the
     sign-extended [c.lw] of [t] (ProofClockintr, hart 0's arm). *)
  Lemma ticks_tie_step (t : mword 32) (n : nat) :
    ticks_tie t n ->
    ticks_tie
      (trunc32 (sign_extend' 64 (subrange_vec_dec
         (add_vec (sign_extend' 64 t)
            (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6)))) 31 0)))
      (S n).
  Proof using .
    rewrite /ticks_tie. intros Htie.
    rewrite trunc32_sext64 subrange_31_0_unsigned add_vec64_unsigned.
    assert (H1 : bv_unsigned (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6)) : mword 64) = 1)
      by (vm_compute; reflexivity).
    assert (Ht : bv_unsigned t = bv_unsigned (sign_extend' 64 t : mword 64) mod 4294967296).
    { rewrite -{1}(trunc32_sext64 t). unfold trunc32. rewrite autocast_id.
      apply subrange_31_0_unsigned. }
    rewrite H1. unfold bv_wrap, bv_modulus.
    change (2 ^ Z.of_N 64) with (4294967296 * 4294967296).
    change (2 ^ 32) with 4294967296 in Htie |- *.
    rewrite -(Zmod_div_mod 4294967296 (4294967296 * 4294967296)); [| lia | lia | by exists 4294967296].
    rewrite -Zplus_mod_idemp_l -Ht Htie Zplus_mod_idemp_l. f_equal. lia.
  Qed.

  (* the bridge to uptime's receipt: at 32 bits [mword_of_int] truncates,
     so the tie IS the equation [t = mword_of_int n]. *)
  Lemma ticks_tie_of_int (t : mword 32) (n : nat) :
    ticks_tie t n -> t = (mword_of_int (Z.of_nat n) : mword 32).
  Proof using .
    rewrite /ticks_tie. intros Htie. apply bv_eq.
    rewrite moi32_unsigned Htie. reflexivity.
  Qed.

  Definition is_tickslock (γl : gname) : iProp Σ :=
    is_lock γl a_tickslock "time"%string ticks_res_at.

  Global Instance is_tickslock_persistent γl : Persistent (is_tickslock γl).
  Proof using . apply _. Qed.

  Lemma is_tickslock_lock γl :
    is_tickslock γl -∗ is_lock γl a_tickslock "time"%string ticks_res_at.
  Proof using . iIntros "$". Qed.

  (* ---- construction (the "newlock" ghost step): what a caller does with
     trapinit's postcondition -- the freshly zeroed lock word and its
     persistent name, plus the counter cell, become the tickslock. *)
  (* A6.67: the creator's honest deposit (A6.66) wants the running token;
     it is handed straight back, so a caller that has one loses nothing. *)
  (* the payload's mirror comes with the cell (design ni-ticks-ledger.md
     D2): a caller supplies the count the cell is tied to. *)
  Lemma new_tickslock `{CID : RiscvLang.CpuId} E (t : mword 32) (n : nat) :
    ticks_tie t n ->
    lock_name a_tickslock "time"%string -∗
    own_context cur_ctx -∗
    a_tickslock ↦₄ (mword_of_int 0 : mword 32) -∗
    WpLock.lk_cpu_ready a_tickslock -∗
    a_ticks ↦₄ t -∗ tick_cnt n ={E}=∗ own_context cur_ctx ∗ ∃ γl : gname, is_tickslock γl.
  Proof using .
    iIntros (Htie) "#Hnm Hrun Hlkw Hcpu Hticks Hc".
    iApply (newlock E a_tickslock "time"%string ticks_res_at
              with "Hnm Hrun Hlkw Hcpu [Hticks Hc]").
    iApply (ticks_res_intro t n Htie with "Hticks Hc").
  Qed.

End TicksInv.
