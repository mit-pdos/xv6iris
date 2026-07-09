(* WpWakeup.v -- the per-process spinlock invariant of xv6's [struct proc],
   the global [proc[NPROC]] lock invariant, and (later) a whole-function WP for
   wakeup().

   Layout of [struct proc] (kernel/proc.h), corroborated by the compiled
   wakeup disassembly (KernelInstrs.v):

       offset 0    struct spinlock lock;   (locked word at +0, cpu ptr at +16)
       offset 24   enum procstate state;   (4-byte int; SLEEPING=2, RUNNABLE=3)
       offset 32   void *chan;             (8-byte)
       ...
       offset 96   struct context context; (14 * 8 = 112 bytes: ra,sp,s0..s11)
       ...
       sizeof(struct proc) = 360,  NPROC = 64,  proc[] @ 0x80012778.

   [proc_lock_res γ p] is the resource protected by [p->lock]: it fully owns
   [p->state] and [p->chan], and -- WHENEVER the state is RUNNABLE or SLEEPING
   -- a [valid_context P (&p->context)] whose resumer-predicate P carries the
   lock's own [locked γ] token.  This encodes the sleep/wakeup handoff: to
   swtch INTO a runnable/sleeping proc you must hand it the lock (P delivers
   [locked γ]); when it wakes it is running holding its own lock.

   [procs_inv γs] is the global fact that every one of the NPROC procs has a
   spinlock guarding its own [proc_lock_res]. *)
From Stdlib Require Import ZArith List.
From stdpp Require Import gmap list.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.algebra Require Import excl ofe.
From iris.base_logic.lib Require Import invariants own ghost_var.
Require Import SailStdpp.Base SailStdpp.Operators_mwords SailStdpp.Values.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes RiscvPtsto RiscvLang.
Require Import SmodeCore.
Require Import InstrBytes MinstretInv RiscvFetchExec WpGpr WpEntryNew.
Require Import WpLock.
Require Import WpSwtchVc.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.

Section ProcInv.
  Context `{!riscvGS Σ, !lockG Σ, !sieG Σ}.
  Context `{CID : CpuId}.
  (* the ambient S-mode config a running/resumed kernel thread holds -- the same
     [sconf] (smode_config γc + the SIE ghost half + tlb_inv) that wp_swtch is
     now stated against, so a proc's saved context interoperates with swtch. *)
  Context (root_ppn : mword 44) (E : coPset) (Phi : mval -> iProp Σ).
  Context (γc : gname) (bsie : mword 1) (dq : dfrac).

  Local Notation VC :=
    (valid_context (sconf root_ppn γc bsie dq) E Phi).

  (* ---- struct proc geometry ---- *)
  Definition NPROC : nat := 64%nat.
  Definition proc_size : Z := 360.
  Definition proc_base : mword 64 := mword_of_int KernelSyms.proc.
  Definition proc_addr (i : nat) : mword 64 :=
    add_vec proc_base (mword_of_int (proc_size * Z.of_nat i)).

  Definition state_off : Z := 24.
  Definition chan_off : Z := 32.
  Definition context_off : Z := 96.

  Definition p_state (pa : mword 64) : mword 64 := add_vec pa (mword_of_int state_off).
  Definition p_chan (pa : mword 64) : mword 64 := add_vec pa (mword_of_int chan_off).
  Definition p_context (pa : mword 64) : mword 64 := add_vec pa (mword_of_int context_off).

  (* enum procstate codes (kernel/proc.h): UNUSED=0 USED=1 SLEEPING=2
     RUNNABLE=3 RUNNING=4 ZOMBIE=5. *)
  Definition SLEEPING : mword 32 := mword_of_int 2.
  Definition RUNNABLE : mword 32 := mword_of_int 3.

  (* A state that requires the [valid_context] obligation: the two "parked"
     states that own a saved context reachable by swtch. *)
  Definition needs_ctx (st : mword 32) : bool :=
    bool_decide (st = RUNNABLE) || bool_decide (st = SLEEPING).

  (* [P contains the lock token]: P is an accessor from which the exclusive
     [locked γ] can be borrowed and returned.  (An accessor, not plain
     ownership, so P can carry further per-proc coupling -- "more later".) *)
  Definition contains_lock (γ : gname) (P : mword 64 -d> iPropO Σ) : iProp Σ :=
    (□ ∀ c : mword 64, P c -∗ locked γ ∗ (locked γ -∗ P c))%I.

  Global Instance contains_lock_persistent γ P : Persistent (contains_lock γ P).
  Proof. apply _. Qed.

  (* the [valid_context] obligation attached to a parked proc: some resumer
     predicate P that hands over the lock token, plus a valid saved context at
     [&p->context]. *)
  Definition proc_ctx (γ : gname) (pa : mword 64) : iProp Σ :=
    (∃ P : mword 64 -d> iPropO Σ,
       contains_lock γ P ∗ VC P (p_context pa))%I.

  (* the resource protected by [p->lock]. *)
  Definition proc_lock_res (γ : gname) (pa : mword 64) : iProp Σ :=
    (∃ (st : mword 32) (ch : mword 64),
       p_state pa ↦₄ st ∗
       p_chan pa ↦₈ ch ∗
       (if needs_ctx st then proc_ctx γ pa else emp))%I.

  (* the global proc-array invariant: an [is_lock] over every proc's
     [proc_lock_res]. *)
  Definition procs_inv (γs : list gname) : iProp Σ :=
    (⌜length γs = NPROC⌝ ∗
     [∗ list] i ↦ γ ∈ γs, is_lock γ (proc_addr i) (proc_lock_res γ (proc_addr i)))%I.

  Global Instance procs_inv_persistent γs : Persistent (procs_inv γs).
  Proof. apply _. Qed.

  (* the per-proc [is_lock] extracted from the global invariant. *)
  Lemma procs_inv_lookup (γs : list gname) (i : nat) (γ : gname) :
    γs !! i = Some γ ->
    procs_inv γs -∗ is_lock γ (proc_addr i) (proc_lock_res γ (proc_addr i)).
  Proof.
    iIntros (Hi) "[_ Hbig]".
    by iDestruct (big_sepL_lookup with "Hbig") as "$".
  Qed.

  (* ===================================================================== *)
  (* Core preservation lemmas -- the separation-logic content of wakeup.    *)
  (* ===================================================================== *)

  (* the two parked states both demand the context obligation, so the obligation
     [proc_ctx] carries UNCHANGED across the SLEEPING -> RUNNABLE transition
     that wakeup performs. *)
  Lemma needs_ctx_SLEEPING : needs_ctx SLEEPING = true.
  Proof. rewrite /needs_ctx orb_true_r. done. Qed.

  Lemma needs_ctx_RUNNABLE : needs_ctx RUNNABLE = true.
  Proof.
    rewrite /needs_ctx. rewrite (bool_decide_eq_true_2 (RUNNABLE = RUNNABLE)); done.
  Qed.

  (* reassemble [proc_lock_res] from its parts -- what wakeup does at every
     [release]: whatever the (possibly updated) state, if it now demands a
     context we supply the (carried) [proc_ctx]. *)
  Lemma proc_lock_res_intro (γ : gname) (pa : mword 64) (st : mword 32) (ch : mword 64) :
    p_state pa ↦₄ st -∗
    p_chan pa ↦₈ ch -∗
    (if needs_ctx st then proc_ctx γ pa else emp) -∗
    proc_lock_res γ pa.
  Proof. iIntros "Hs Hc Hctx". iExists st, ch. iFrame. Qed.

  Lemma proc_lock_res_elim (γ : gname) (pa : mword 64) :
    proc_lock_res γ pa -∗
    ∃ (st : mword 32) (ch : mword 64),
      p_state pa ↦₄ st ∗ p_chan pa ↦₈ ch ∗
      (if needs_ctx st then proc_ctx γ pa else emp).
  Proof. iIntros "H". iExact "H". Qed.

  (* the wakeup transition: a proc found SLEEPING (hence carrying [proc_ctx]),
     with its state cell flipped to RUNNABLE, still satisfies [proc_lock_res].
     The saved context (with the lock token in its resumer predicate) survives
     the state change untouched. *)
  Lemma proc_lock_res_wakeup (γ : gname) (pa : mword 64) (ch : mword 64) :
    p_state pa ↦₄ RUNNABLE -∗
    p_chan pa ↦₈ ch -∗
    proc_ctx γ pa -∗
    proc_lock_res γ pa.
  Proof.
    iIntros "Hs Hc Hctx". iExists RUNNABLE, ch. iFrame "Hs Hc".
    destruct (needs_ctx RUNNABLE) eqn:Hn.
    - iExact "Hctx".
    - rewrite needs_ctx_RUNNABLE in Hn. discriminate.
  Qed.

End ProcInv.

(* ======================================================================= *)
(* myproc(), axiomatized.                                                    *)
(*                                                                           *)
(* wakeup only relies on ONE fact about myproc(): the pointer it returns (in *)
(* a0, used to skip the current process) is a genuine entry of the global    *)
(* proc[] table.  We assume a jal-callable whole-function WP that: returns   *)
(* a0 = proc_addr j for some j < NPROC; preserves the callee-saved registers *)
(* (sp, s0..s11); and preserves the ambient config [smode_config γc], its    *)
(* SIE ghost half, and [tlb_inv] -- exactly the resources acquire/release     *)
(* thread -- with myproc managing its own stack frame internally.  (For now,  *)
(* it just returns some proc.)                                                *)
(* ======================================================================= *)
Axiom wp_myproc :
  forall {Σ : gFunctors} {HR : riscvGS Σ} {HS : sieG Σ} {CID : CpuId}
    (root_ppn : mword 44) (E : coPset) (Phi : mval -> iProp Σ)
    (γc : gname) (bsie : mword 1)
    (m : gmap regidx (mword 64)),
    ↑minstretN ⊆ E ->
    let ret_tgt :=
      update_vec_dec (add_vec (m !!! Regidx (mword_of_int 1 : mword 5))
                        (sign_extend' 64 (zeros' 12))) 0 ('b"0") in
    eq_vec (access_vec_dec ret_tgt 0) ('b"0") = true ->
    smode_config γc (DfracOwn 1) -∗ ghost_var γc (1/2) bsie -∗ tlb_inv root_ppn -∗
    kernel_text -∗ pc_is (mword_of_int KernelSyms.myproc) -∗ gpr_file m -∗
    (∀ (j : nat) (mret : gmap regidx (mword 64)),
       ⌜(j < NPROC)%nat⌝ -∗
       ⌜mret !!! Regidx (mword_of_int 10 : mword 5) = proc_addr j⌝ -∗
       ⌜forall r : mword 5,
          r ∈ [mword_of_int 2; mword_of_int 8; mword_of_int 9;
               mword_of_int 18; mword_of_int 19; mword_of_int 20;
               mword_of_int 21; mword_of_int 22; mword_of_int 23;
               mword_of_int 24; mword_of_int 25; mword_of_int 26;
               mword_of_int 27] ->
          mret !!! Regidx r = m !!! Regidx r⌝ -∗
       smode_config γc (DfracOwn 1) -∗ ghost_var γc (1/2) bsie -∗ tlb_inv root_ppn -∗
       pc_is ret_tgt -∗ gpr_file mret -∗
       WP (Loop : expr riscv_lang) @ E {{ Phi }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Phi }}.
