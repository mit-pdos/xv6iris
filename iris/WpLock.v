(* WpLock.v -- the standard CSL/Iris spin-lock invariant for xv6's
   [struct spinlock], mirroring iris_heap_lang/lib/spin_lock.v but over the
   PHYSICAL fields of the Sail RISC-V machine: the 4-byte lock word
   ([lk->locked] @ +0) AND the 8-byte owner word ([lk->cpu] @ +16).

     lock_inv      -- ∃ v st, lock word ↦ v ∗ lk_cpu_res st lk ∗ ghost st
                        ∗ (st free ∗ v = 0 ∗ frag ∗ R  ∨  st held ∗ v ≠ 0)
     lk_cpu_res    -- the owner field, WHOLE at 0 while the lock is free or
                      in a one-store window, and HALF at [cpus_ptr i] plus
                      the held-lock-set fragment [lk_in i lk] while hart [i]
                      holds it (the other half is in that hart's
                      [LockSet.cpu_locks]).  See the block at its definition.
     is_lock       -- lock_name ∗ inv lockN lock_inv   (persistent)
     locked γ i    -- the lock-HOLDER token: hart [i] holds the lock and
                      [lk->cpu] holds [cpus_ptr i] = &cpus[i]

   BOTH physical fields belong to the invariant: no proof threads either of
   them, and there is no per-caller [lk->cpu] cell to pass around (the shape
   that made the cpu word look like private state -- unsound as soon as two
   harts race for the same lock).  What a holder carries instead is
   [locked γ i], and that token PINS [lk->cpu = cpus_ptr i]: the state ghost
   mirrors the field and the holder's fragment agrees with the invariant's
   authority.  So [holding()] provably returns 1 for the holder, which is all
   [release] needs.  A NON-holder learns nothing about the field -- so
   holding() may answer either way for it, and acquire's
   [if(holding(lk)) panic] arm is discharged by panic's contract rather than
   shown dead (SpecAcquire.v).

   [lock_state] mirrors both fields as one value, including the one-store
   window inside acquire (word already taken, [lk->cpu] not yet written):

     None            -- free:               word = 0, lk->cpu = 0
     Some (i, false) -- held by i, lk->cpu = 0 (acquire's window; release's
                        window between its cpu clear and its word clear)
     Some (i, true)  -- held by i, lk->cpu = cpus_ptr i                     *)
From stdpp Require Import bitvector.definitions.  (* [bv 8]: the M4 owner-cell kit is stated per byte *)
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import excl gmap auth ufrac.
From iris.algebra.lib Require Import excl_auth.
From iris.base_logic.lib Require Import invariants cancelable_invariants own.
Require Import SailStdpp.Base SailStdpp.Operators_mwords.
Require Import Riscv.rv64d.
Require Import Riscv.rv64d_types.  (* A6.84: the ledger word's carrier types *)
Require Import RiscvPtsto RiscvLang.
(* EXPORTED: [lock_cpu] (the +16 owner-field address) lives there, because the
   per-cpu held-lock set is stated over it, and the ~40 files that reach
   [lock_cpu] through this one keep working. *)
Require Export LockSet.
Require Import ProcGeom.
Require Import RiscvModelBytes.  (* [nth_byte] / [bv_eq_of_bytes]: the M4 owner-cell kit below is stated per BYTE *)
Require Import TsoMemPa.  (* [agent]: the racy owner-cell kit quantifies over the log's authors *)
Require Export Xv6Cameras.  (* the cameras this file states its theory over *)
(* the context axis (tso-port M3): the PAYLOAD of every lock is a function
   of the thread of control that holds its facts -- see the block above
   [lock_inv]. *)
Require Import Ktier KMap RiscvExtras.  (* A6.84: [ktier_pin] / [kmap_at] --
   a ledger cell carries no MAPPING, so [lk_addr_claim] states one here *)
Require Import TsoCtx.
Require Import TsoCtxPark.  (* A6.144: [ctx_parked_raise] -- the record's
   stamp rises at any log-length receipt, minting the floor a payload row
   needs (the [lock_pay_intro_llb] mint below) *)
(* [lock_name_intro] mints the deliberately-RAW name-field metadata
   (tso-port.md §0.8' ruling 2) out of a context-indexed store result, so it
   leaves the ledger through [TsoCtx.ctx_word_pointsto_forget] -- the named
   one-way projection (§6 amendment A6.8), where the SC-era file used the
   now-dead [TsoCtxShim.ctx_word_to_mem].  Sound and final: the field is
   discarded one line later, so nothing will ever load it again. *)
Local Open Scope Z_scope.


Section Lock.
  Context `{!riscvGS Σ, !lockG Σ}.
  (* the ambient context, used ONLY by the construction lemmas at the
     bottom (the creator deposits the payload at its own identity); a
     section variable, so nothing else picks it up. *)
  Context `{XI : CurCtx}.

  (* sibling of [minstretN]; the two are disjoint by construction, so a leaf
     can open [is_lock] INSIDE the step engine's [⊤ ∖ ↑minstretN] callback. *)
  Definition lockN : namespace := nroot .@ "xv6spinlock".

  (* ---- the ghost pieces ---------------------------------------------- *)

  (* the authority on the lock's state; lives in the invariant. *)
  (* A6.119: the position-exposing forms.  [lock_auth_at] is what the
     invariant holds beside the word's pin; [lock_frag_at] is what the holder
     token carries.  The agreement between them is the whole point. *)
  Definition lock_auth_at (γ : gname) (st : lock_state) (B : nat) : iProp Σ :=
    own γ ((●E (st : leibnizO lock_state), ●E (B : leibnizO nat)) : lockUR).
  Definition lock_frag_at (γ : gname) (st : lock_state) (B : nat) : iProp Σ :=
    own γ ((◯E (st : leibnizO lock_state), ◯E (B : leibnizO nat)) : lockUR).

  Definition lock_auth (γ : gname) (st : lock_state) : iProp Σ :=
    (∃ B : nat, lock_auth_at γ st B)%I.
  (* the state fragment; the free one lives in the invariant, a held one is
     the holder's token (see [locked] / [locked_pre]). *)
  Definition lock_frag (γ : gname) (st : lock_state) : iProp Σ :=
    (∃ B : nat, lock_frag_at γ st B)%I.

  Global Instance lock_auth_at_timeless γ st B : Timeless (lock_auth_at γ st B).
  Proof. apply _. Qed.
  Global Instance lock_frag_at_timeless γ st B : Timeless (lock_frag_at γ st B).
  Proof. apply _. Qed.

  (* THE AGREEMENT, and it is the tie the word's pin needs: the position the
     invariant minted at the AMO is the position the holder was handed. *)
  Lemma lock_pos_agree γ st st' B B' :
    lock_auth_at γ st B -∗ lock_frag_at γ st' B' -∗ ⌜st = st' /\ B = B'⌝.
  Proof.
    iIntros "Ha Hf".
    iDestruct (own_valid_2 with "Ha Hf") as %[Hv1 Hv2].
    iPureIntro. split.
    - exact (excl_auth_agree_L _ _ Hv1).
    - exact (excl_auth_agree_L _ _ Hv2).
  Qed.

  (* THE holder token: hart [i] holds the lock and [lk->cpu = cpus_ptr i]. *)
  (* >>> §0.34′ LANDS ON ITS SOUND AXIS (A6.119; §0.35′'s ξ-relativity, and
     A6.89's refutation SHARPENED rather than reversed).

     THE PRECISE BOUNDARY, because the earlier note read as a blanket warning
     and is not one:

       - A HART-INDEXED carrier is REFUTED.  The experiment was
         [locked `{CID : CpuId} γ i := lock_frag γ (Some (i,true)) ∗
         ⌜cpu_id = i⌝].  It dies at the first CONSUMER: every lock leaf hands
         the token THROUGH its instruction step, and the continuation's
         [locked γ i] is elaborated at the [CpuId] the [wp_next] lambda
         binds -- the RESUMING hart -- while the one in hand is at the entry
         hart.  The two print identically and do not unify (A6.63''/§0.20′'s
         re-park hazard, inside the token).

       - A ξ-INDEXED conjunct is LICENSED, and by the very fact that killed
         the other one: [CpuId] REBINDS at [wp_next]; [cur_ctx] DOES NOT.
         [SpecAcquire]'s own note says it -- "[cur_ctx] is bound OUTSIDE the
         [wp_next] binder, so the facts a thread wins are its own even if the
         prologue migrated".  So the token may carry ξ-indexed facts exactly
         where it may not carry hart-indexed ones.

     WHAT IT NOW CARRIES, and why: the ACQUIRE POSITION's floor.  The word's
     value-set pin (A6.119, §0.35′(iv) case 2) is minted at the AMO at that
     position, and [holding()]'s read needs [view_lb] at it -- a receipt only
     the acquirer ever had, at an instruction long past by the time the read
     runs.  The token is the one thing the holder holds across that gap.
     [lock_pos_agree] ties the token's [B] to the invariant's.

     ARITY UNCHANGED and ξ AMBIENT, so no consumer's spelling moves -- the
     same treatment [is_lock] took under §0.35′, and the 69 files that
     mention [locked] are the verification, not the cost. <<< *)
  Definition locked (γ : gname) (i : CPU) : iProp Σ :=
    (∃ B : nat, lock_frag_at γ (Some (i, true)) B ∗
       TsoCtx.ctx_floor cur_ctx B)%I.
  (* the same, in the window where [lk->cpu] is still 0 (internal to the
     acquire / release proofs; no caller ever sees it).  It carries the floor
     too: the pin exists from the WINNING amoswap, which is where this token
     is minted, so the two arms of the held interval agree. *)
  Definition locked_pre (γ : gname) (i : CPU) : iProp Σ :=
    (∃ B : nat, lock_frag_at γ (Some (i, false)) B ∗
       TsoCtx.ctx_floor cur_ctx B)%I.

  Global Instance locked_timeless γ i : Timeless (locked γ i).
  Proof. apply _. Qed.
  Global Instance locked_pre_timeless γ i : Timeless (locked_pre γ i).
  Proof. apply _. Qed.

  (* the value [lk->cpu] holds in each state: the OWNER word. *)
  Definition lk_cpu_val (st : lock_state) : mword 64 :=
    match st with
    | Some (i, true) => cpus_ptr i
    | _ => (zero_reg : mword 64)
    end.

  (* the one agent that may be missing an own-last record in each state:
     the HOLDER, and nobody else (see [lk_own_ok] below). *)
  Definition lk_ex (st : lock_state) : option CPU :=
    match st with Some (i, true) => Some i | _ => None end.

  (* >>> A6.89: THE WORD'S OWN-WRITE SELECTOR IS NOT THE CELL'S, and the
     difference is exactly one state.  [lk_ex] is about the OWNER CELL,
     whose author is the acquirer's [lk->cpu = mycpu()] store -- so the
     cell has an author only while HELD.  The lock WORD's author is the
     AMO, which fires one instruction EARLIER: from the amoswap until
     release's [sw x0] the word is the acquirer's own write, and that
     interval covers BOTH [Some (i,false)] windows (acquire's, before the
     cpu field is set, and release's, after it is cleared) as well as
     [Some (i,true)].
     Getting this wrong is not a soundness hole, it is an unprovable
     frame: the cpu-field stores do not touch the word, so the word's arm
     must be INVARIANT across them -- and with [lk_ex] it flips, which is
     where the store leaf's [iFrame] refuses. <<< *)
  Definition lk_wex (st : lock_state) : option CPU :=
    match st with Some (i, _) => Some i | None => None end.

  Lemma lk_wex_none : lk_wex None = None.
  Proof. reflexivity. Qed.
  Lemma lk_wex_some (i : CPU) (o : bool) : lk_wex (Some (i, o)) = Some i.
  Proof. reflexivity. Qed.

  Lemma lk_cpu_val_none : lk_cpu_val None = (zero_reg : mword 64).
  Proof. reflexivity. Qed.
  Lemma lk_cpu_val_win (i : CPU) : lk_cpu_val (Some (i, false)) = (zero_reg : mword 64).
  Proof. reflexivity. Qed.
  Lemma lk_cpu_val_held (i : CPU) : lk_cpu_val (Some (i, true)) = cpus_ptr i.
  Proof. reflexivity. Qed.


  Global Instance lock_auth_timeless γ st : Timeless (lock_auth γ st).
  Proof. apply _. Qed.
  Global Instance lock_frag_timeless γ st : Timeless (lock_frag γ st).
  Proof. apply _. Qed.

  (* ---- the ghost laws ------------------------------------------------ *)

  (* the fragment agrees with the authority: this is what pins [lk->cpu]. *)
  Lemma lock_frag_agree γ st st' :
    lock_auth γ st -∗ lock_frag γ st' -∗ ⌜st = st'⌝.
  Proof.
    iIntros "(%B & Ha) (%B' & Hf)".
    iDestruct (lock_pos_agree with "Ha Hf") as %[-> _]. done.
  Qed.
  (* the state fragment is exclusive: two of them cannot coexist, whatever
     states they claim -- so two holder tokens are impossible. *)
  Lemma lock_frag_exclusive γ st st' :
    lock_frag γ st -∗ lock_frag γ st' -∗ False.
  Proof.
    iIntros "(%B & H1) (%B' & H2)".
    iDestruct (own_valid_2 with "H1 H2") as %[Hv1 _].
    destruct (proj1 (excl_auth_frag_op_valid _ _) Hv1).
  Qed.


  Lemma lock_frag_at_exclusive γ st st' B B' :
    lock_frag_at γ st B -∗ lock_frag_at γ st' B' -∗ False.
  Proof.
    iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as %[Hv1 _].
    destruct (proj1 (excl_auth_frag_op_valid _ _) Hv1).
  Qed.
  Lemma locked_exclusive γ i j : locked γ i -∗ locked γ j -∗ False.
  Proof.
    iIntros "(%B & H1 & _) (%B' & H2 & _)".
    iApply (lock_frag_at_exclusive with "H1 H2").
  Qed.

  (* A bare exclusive token out of the same RA, for a client that needs an
     abstract "held" marker with no hart identity in it: the SLEEPlock's
     holder token (SleepLock.v).  A sleeplock is held by a PROCESS, not by a
     hart, and its gname carries nothing else -- no [lock_inv], no tickets. *)
  Definition lock_tok_excl (γ : gname) : iProp Σ := lock_frag γ None.
  Lemma lock_tok_excl_exclusive γ :
    lock_tok_excl γ -∗ lock_tok_excl γ -∗ False.
  Proof. apply lock_frag_exclusive. Qed.
  Global Instance lock_tok_excl_timeless γ : Timeless (lock_tok_excl γ).
  Proof. apply _. Qed.
  Lemma lock_tok_excl_alloc : ⊢ |==> ∃ γ : gname, lock_tok_excl γ.
  Proof.
    iMod (own_alloc (((◯E (None : leibnizO lock_state)),
                      (◯E (0%nat : leibnizO nat))) : lockUR)) as (γ) "H".
    { split; apply auth_frag_valid; done. }
    iModIntro. iExists γ. iExists 0%nat. iExact "H".
  Qed.

  (* THE holder law: the token pins the owner word to your own [struct cpu].
     A6.119: the token's own position comes back too -- it is what the word's
     pin is read against, and [lock_pos_agree] is what ties it to the one the
     invariant minted. *)
  Lemma locked_state_at γ st B i :
    lock_auth_at γ st B -∗ locked γ i -∗
    ⌜st = Some (i, true)⌝ ∗ TsoCtx.ctx_floor cur_ctx B.
  Proof.
    iIntros "Ha (%B' & Hf & #Hfl)".
    iDestruct (lock_pos_agree with "Ha Hf") as %[-> ->].
    iSplitR; [done|]. iExact "Hfl".
  Qed.

  Lemma locked_pre_state_at γ st B i :
    lock_auth_at γ st B -∗ locked_pre γ i -∗
    ⌜st = Some (i, false)⌝ ∗ TsoCtx.ctx_floor cur_ctx B.
  Proof.
    iIntros "Ha (%B' & Hf & #Hfl)".
    iDestruct (lock_pos_agree with "Ha Hf") as %[-> ->].
    iSplitR; [done|]. iExact "Hfl".
  Qed.

  Lemma locked_state γ st i :
    lock_auth γ st -∗ locked γ i -∗ ⌜st = Some (i, true)⌝.
  Proof.
    iIntros "(%B & Ha) Ht".
    iDestruct (locked_state_at with "Ha Ht") as "[$ _]".
  Qed.

  Lemma locked_pre_state γ st i :
    lock_auth γ st -∗ locked_pre γ i -∗ ⌜st = Some (i, false)⌝.
  Proof.
    iIntros "(%B & Ha) Ht".
    iDestruct (locked_pre_state_at with "Ha Ht") as "[$ _]".
  Qed.

  Lemma locked_cpu_eq γ st i :
    lock_auth γ st -∗ locked γ i -∗ ⌜lk_cpu_val st = cpus_ptr i⌝.
  Proof.
    iIntros "Hg Ht".
    iDestruct (locked_state with "Hg Ht") as %->. done.
  Qed.

  (* ---- the four state transitions (one per lock instruction) ---------
     A6.119: the POSITION rides with them.  [lock_take] is the AMO's step and
     is where it enters -- the floor is the acquire's own, minted at the same
     instruction; the two middle steps carry it; [lock_give] drops it as the
     lock goes free and the word's pin is retracted. *)
  Local Lemma lock_state_update_at γ st st' B B' :
    lock_auth_at γ st B -∗ lock_frag_at γ st B ==∗
    lock_auth_at γ st' B' ∗ lock_frag_at γ st' B'.
  Proof.
    iIntros "Ha Hf".
    rewrite /lock_auth_at /lock_frag_at -own_op.
    iApply (own_update_2 with "Ha Hf").
    apply prod_update; apply excl_auth_update.
  Qed.

  Local Lemma lock_state_update γ st st' :
    lock_auth γ st -∗ lock_frag γ st ==∗ lock_auth γ st' ∗ lock_frag γ st'.
  Proof.
    iIntros "(%B & Ha) (%B' & Hf)".
    iDestruct (lock_pos_agree with "Ha Hf") as %[_ ->].
    iMod (lock_state_update_at γ st st' B' B' with "Ha Hf") as "[Ha Hf]".
    iModIntro. iSplitL "Ha"; by iExists B'.
  Qed.

  (* acquire's amoswap: a free lock becomes "held by i, cpu not yet written",
     AT THE POSITION THE AMO JUST OCCUPIED. *)
  Lemma lock_take γ i (B : nat) :
    TsoCtx.ctx_floor cur_ctx B -∗
    lock_auth γ None -∗ lock_frag γ None ==∗
    lock_auth_at γ (Some (i, false)) B ∗ locked_pre γ i.
  Proof.
    iIntros "#Hfl (%B0 & Ha) (%B1 & Hf)".
    iDestruct (lock_pos_agree with "Ha Hf") as %[_ ->].
    iMod (lock_state_update_at γ None (Some (i, false)) B1 B with "Ha Hf")
      as "[Ha Hf]".
    iModIntro. iFrame "Ha". iExists B. iFrame "Hf Hfl".
  Qed.

  (* acquire's [lk->cpu = mycpu()]: the window closes, the holder gets THE
     token; the position is unmoved. *)
  Lemma lock_setcpu γ st B i :
    lock_auth_at γ st B -∗ locked_pre γ i ==∗
    ⌜st = Some (i, false)⌝ ∗ lock_auth_at γ (Some (i, true)) B ∗ locked γ i.
  Proof.
    iIntros "Ha (%B' & Hf & #Hfl)".
    iDestruct (lock_pos_agree with "Ha Hf") as %[-> ->].
    iMod (lock_state_update_at γ (Some (i, false)) (Some (i, true)) B' B' with "Ha Hf") as "[Ha Hf]".
    iModIntro. iSplitR; [done|]. iFrame "Ha". iExists B'. iFrame "Hf Hfl".
  Qed.

  (* release's [lk->cpu = 0]: back into the window, position unmoved. *)
  Lemma lock_clrcpu γ st B i :
    lock_auth_at γ st B -∗ locked γ i ==∗
    ⌜st = Some (i, true)⌝ ∗ lock_auth_at γ (Some (i, false)) B ∗ locked_pre γ i.
  Proof.
    iIntros "Ha (%B' & Hf & #Hfl)".
    iDestruct (lock_pos_agree with "Ha Hf") as %[-> ->].
    iMod (lock_state_update_at γ (Some (i, true)) (Some (i, false)) B' B' with "Ha Hf") as "[Ha Hf]".
    iModIntro. iSplitR; [done|]. iFrame "Ha". iExists B'. iFrame "Hf Hfl".
  Qed.

  (* release's word clear: the lock goes free again, and the position goes
     with it -- the pin it floored has just been retracted. *)
  Lemma lock_give γ st B i :
    lock_auth_at γ st B -∗ locked_pre γ i ==∗
    ⌜st = Some (i, false)⌝ ∗ lock_auth γ None ∗ lock_frag γ None.
  Proof.
    iIntros "Ha (%B' & Hf & _)".
    iDestruct (lock_pos_agree with "Ha Hf") as %[-> ->].
    iMod (lock_state_update_at γ (Some (i, false)) None B' B'
            with "Ha Hf") as "[Ha Hf]".
    iModIntro. iSplitR; [done|].
    iSplitL "Ha"; by iExists B'.
  Qed.

  (* ---- the physical fields ------------------------------------------- *)

  (* the physical 4-byte little-endian lock word at address [lk]: the 4-byte
     word points-to (which also bundles the 4-byte alignment of [lk]).

     ∃-CONTEXT, AND THAT IS A CORRECTNESS FIX, NOT A STYLE ONE
     (tso-port.md §0.19′'s ruling, replayed here at A6.72; main's [WpLock]
     at HEAD is the reference).  The cell is exactly [lk_cpu_res]'s owner
     word one field over and it takes the same shape for the same reason
     (§0.8′ ruling 2: lock metadata raw, lock-internal CELLS ∃-context):

     1. AN AMBIENT INDEX HERE DRAGS A CONTEXT INTO [is_lock].  This cell
        sits inside [lock_inv], hence inside the PERSISTENT HANDLE, and a
        boot-minted [is_lock] could then not be stated at another thread.
        §0.12′'s park record carries three lock handles (wait / ticks /
        nextpid) across a ∀-quantified resume context PRECISELY because
        [is_lock] is a CLOSED TERM; the ambient index falsified that
        outright, and no payload conversion could have repaired it.  The ∃
        closes the term again, and it is also the TRUE statement: the word
        belongs to whichever hart last stored it.
     2. RAW WAS CONSIDERED AND IS WRONG.  The lock word is only ever READ
        exclusively (acquire's [amoswap.w.aq] takes the machine's exclusive
        arm), so a raw cell would discharge every load -- but release's word
        clear is a STORE, and a store owes [Wobl_ram], whose γts update
        needs the cell's timestamp element.  A cell with no ledger residue
        cannot be stored to (A6.16).  So the residue stays.

     THE CLIENT-FACING SPELLINGS DO NOT MOVE: the creators still take, and
     the destroyers still hand back, [lk ↦₄ 0] at the caller's own context,
     and [lock_word_intro] is that bridge.

     >>> AND THE ELIMINATION DIRECTION IS NOT A LEMMA HERE.  Main states
     [lock_word_acc] as a [⊣⊢] and proves the ∃-elimination with
     [TsoCtxShim.ctx_word4_{to,of}_mem] -- sound at SC, where [ctx] is
     degenerate, and FALSE at this machine: a cell at an unknown ξ licenses
     no load at ours.  That direction is the M4 racy-owner-cell entry
     ([WpSconfLock]'s [wp_ld_lkcpu_lockopen_gen] is its twin one field
     over), and it is deliberately absent until the M4 memo lands. <<< *)
  (* >>> A6.84: THE ∃ IS GONE, AND WHAT REPLACED IT IS BETTER.  The ∃ξ
     closed [is_lock]'s term at the cost of an existential nothing could
     eliminate -- "a cell at an unknown ξ licenses no load at ours" -- so
     the two lock leaves that READ the word were unprovable.  At the
     LEDGER tier the cell has no ξ AT ALL: [phys_ledger_word4] is the
     eight-byte carrier's four-byte twin, ξ-free BY CONSTRUCTION, and the
     store gates over it are context-free ([ledger_store_win_at_ok]), so
     release's clear and the AMO's write need no [own_context] either.
     [is_lock] is a closed term for the reason §0.19′ wanted and with no
     residual existential.

     WHAT IT COSTS is the address's MAPPING, which a ledger cell does not
     carry: the invariant keeps the two [lk_addr_claim]s instead.  They
     are PERSISTENT and about the ADDRESS, not the value, so one peek
     serves every leaf ([WpSconfLock.lock_claims]).  <<< *)
  Definition lock_word (lk : mword 64) (v : mword 32) : iProp Σ :=
    TsoCtx.phys_ledger_word4 lk (DfracOwn 1) v.

  (* >>> A6.88: THE WORD'S HELD ARM CARRIES THE HOLDER'S OWN-WRITE RECEIPT,
     and it is [lk_cpu_cell_ex]'s shape one field over.  [holding()] reads
     BOTH lock fields and the holder's read of each must be EXACT; A6.78
     §(2) named the asymmetry for the owner CELL and A6.84 implemented it
     there, and the word wants it for the identical reason -- the invariant
     knows the CURRENT value, and under TSO a load may return an older one
     unless the reader can point at its own write.

     The state SELECTS the arm, exactly as [lk_cpu_cell_ex] does: a free
     lock's word is nobody's own write and carries no receipt; a held one
     is the holder's AMO and carries its message fragment. <<< *)
  (* >>> A6.119: THE WORD'S RACY KIT, AND IT IS THE PIN -- the fourth and, by
     measurement, final shape for this word.

     A6.92 refuted the AUTHORSHIP arm ([lock_word_ex] indexed by the holder):
     `amoswap` writes UNCONDITIONALLY, so a spinner that finds the lock held
     still stores, and after a failed acquire the word is the SPINNER's own
     write while the state still names the holder.  The plain word was then
     measured too weak at exactly one read -- [holding()]'s, which must
     conclude the word is nonzero and has nothing to conclude it from.  What
     is left is the VALUE-SET form, which is §0.35'(iv) case 2's own
     prescription: read the locked word against a value set on the racy kit.

     THE INSTRUMENT NOTE, since this word disambiguated the two racy kits:
     PIN for same-value-many-writers, TsWin for distinct-values-per-writer.
     [TsoCtx.ledger_read_pin_ok] concludes VALUE-SET MEMBERSHIP and its store
     gate's premise is "the stored value stays in the set" -- the spinner
     argument verbatim.  [ledger_read_racy_word_ok] concludes a NEGATIVE off
     per-agent-DISTINCT words: exactly the cpu cell's structure (each hart
     writes its own [cpus_ptr]) and exactly not this word's, where every
     agent writes the same 1 and the injectivity premise is unprovable.

     ARM-SHAPED BY THE STATE, [st = None] vs [st <> None]: the word is 1 from
     the WINNING amoswap until release's `sw x0`, spanning both
     [Some (i,false)] and [Some (i,true)] -- which is [lk_wex]'s domain used
     as the pure state function it was demoted to.  The free arm carries no
     pin: the free-path word read owns nothing and concludes nothing, and the
     only write to a free word is the winning AMO, which flips the state. <<< *)
  Definition lkw_one : mword 32 := mword_of_int 1.

  Definition lkw_set (j : nat) : TsoMemPa.byteset :=
    TsoMemPa.byteset_sing (nth_byte lkw_one j).

  Definition lock_word_pin (B : nat) (lk : mword 64) (v : mword 32) : iProp Σ :=
    (⌜is_aligned_paddr (Physaddr lk) 4 = true⌝ ∗
     [∗ list] j ∈ seq 0 4, ∃ t : nat,
       TsoCtx.phys_ledger_pin (pa_add lk j) (DfracOwn 1) (nth_byte v j) t B
         (lkw_set j))%I.

  Global Instance lock_word_pin_timeless B lk v :
    Timeless (lock_word_pin B lk v).
  Proof. apply _. Qed.

  (* the word conjunct of the invariant, at whichever arm the state selects *)
  Definition lock_word_at (st : lock_state) (B : nat) (lk : mword 64)
      (v : mword 32) : iProp Σ :=
    match st with
    | None   => lock_word lk v
    | Some _ => lock_word_pin B lk v
    end.

  Global Instance lock_word_at_timeless st B lk v :
    Timeless (lock_word_at st B lk v).
  Proof. destruct st; apply _. Qed.

  Definition lock_word_ex (ex : option CPU) (lk : mword 64) (v : mword 32)
      : iProp Σ :=
    match ex with
    | Some i => TsoCtx.phys_ledger_word4_vis (hart_agent i) 0 lk (DfracOwn 1) v
    | None   => lock_word lk v
    end.

  Global Instance lock_word_ex_timeless ex lk v : Timeless (lock_word_ex ex lk v).
  Proof. destruct ex; rewrite /lock_word_ex /lock_word; apply _. Qed.

  (* the held arm forgets its receipt: what release spends on the way out *)
  Lemma lock_word_ex_forget ex lk v : lock_word_ex ex lk v ⊢ lock_word lk v.
  Proof.
    destruct ex as [i|]; [| by iIntros "$"].
    rewrite /lock_word_ex /lock_word.
    iIntros "H". by iApply TsoCtx.phys_ledger_word4_vis_forget.
  Qed.

  Lemma lock_word_ex_free lk v : lock_word_ex None lk v ⊣⊢ lock_word lk v.
  Proof. reflexivity. Qed.

  Lemma lock_word_ex_aligned_p ex lk v :
    lock_word_ex ex lk v ⊢ ⌜is_aligned_paddr (Physaddr lk) 4 = true⌝.
  Proof.
    destruct ex as [i|].
    - iApply TsoCtx.phys_ledger_word4_vis_aligned_p.
    - iApply TsoCtx.phys_ledger_word4_aligned_p.
  Qed.

  (* the INTRODUCTION leg, which is all the creators need.  ONE-WAY, and
     deliberately: the lock's word never goes back to the ctx tower. *)
  Lemma lock_word_intro (lk : mword 64) (v : mword 32) :
    lk ↦₄ v ⊢ lock_word lk v.
  Proof. rewrite /lock_word. iIntros "H". by iApply TsoCtx.ctx_word4_ledger_kt0. Qed.

  (* ===================================================================
     THE OWNER FIELD, AND THE HELD-SET FRAGMENT BESIDE IT.

     [lk->cpu] ([LockSet.lock_cpu], the 8-byte word at +16) is owned WHOLE by
     the invariant in every state.  What varies is what sits beside it: while
     hart [i] holds the lock, the invariant also keeps the held-set fragment
     [lk_in i r] at this lock's NAME (its rank orders it, but the set holds
     the name -- see LockRank.v's [locks_below]).  So
     the two readings of "this lock is held by hart i" -- the C field and the
     ghost set -- are one resource, and neither can drift from the other:

       - RELEASE's [lk->cpu = 0] retires the fragment, which is exactly the
         licence to take the name out of the hart's set
         ([LockSet.cpu_locks_delete]).
       - ACQUIRE's [lk->cpu = mycpu()] mints it, which needs [r ∉ S] -- and
         that is supplied by the caller's ORDER PREMISE
         ([LockRank.locks_below S r]), not read off the machine.
       - a hart whose set omits [r] therefore CANNOT be the holder, so
         [holding(lk)] is provably 0 and acquire's [if(holding(lk)) panic()]
         arm is DEAD rather than discharged by a panic credential.

     WHAT THIS REPLACED, AND WHY THE SIMPLIFICATION IS THE ORDER'S DOING.
     Before the lock order existed, acquire had no premise to lean on, so
     [r ∉ S] had to be DERIVED: the hart co-owned HALF of every held lock's
     cpu cell (pinned at [cpus_ptr i]) and freshness fell out of the cell
     disagreeing at 0 in acquire's one-store window.  That forced a
     state-dependent sibling ([lk_cpu_half] / [lk_cpu_rest]), a fixed 1/2
     fraction the two READ leaves had to be blind to -- because
     [WpSconfMem.wp_load_s_sconf_au] fixes its [dqm] OUTSIDE the fupd that
     opens the invariant, where [st] is still existential -- and an EXCHANGE
     wand in each of the two cpu-word STORE leaves.  With the premise
     supplying freshness, all of it goes: the cell is [DfracOwn 1] in every
     state, the read leaves are state-blind for free, and the stores are
     ordinary stores. *)
  Definition lk_cpu_frag (st : lock_state) (r : string) : iProp Σ :=
    match st with
    | Some (i, true) => lk_in i r
    | _ => emp
    end%I.

  (* THE OWNER CELL'S CONTEXT IS ∃-QUANTIFIED, not ambient: [lk_cpu_res]
     sits inside [lock_inv] under the invariant, so an ambient index here
     would drag a context into [is_lock] -- the persistent HANDLE -- and a
     handle minted at boot could not be stated at another thread.  ∃ is
     also the true statement: the cell belongs to whichever hart last
     stored it.  The window lemmas below keep the ∃ ([lk_cpu_cell]); the
     SC-era trade for the acting hart's ambient form died with the shim,
     and recovering it is the M4 racy-kit entry spelled out there. *)
  (* THE ADDRESS CLAIM a ledger cell does not carry.  Character for
     character [MemClaim.mem_claim] under its alignment -- that file
     sits ABOVE this one, so the content is restated here and
     [WpSconfLock.lock_claims] is the one line that converts (they are
     convertible at [KT0], which is the only tier a lock lives at). *)
  (* THE ADDRESS CLAIM A LEDGER CELL DOES NOT CARRY.
     PER BYTE, not merely at the base (A6.86).  The base form is what the
     translation engines want ([MemClaim.mem_claim] under its alignment),
     but the PAGE that reclaims the cell wants one per byte -- a free page's
     bytes are [TsoCtx.mem_free], and [mem_free] is the kmap claim over the
     visibility-free byte.  Both readings are here because the producer has
     both for free: every creator pays this claim off a CTX WORD it still
     holds, and a ctx word is ctx BYTES, each carrying its own mapping.
     *That* is why the arithmetic never appears: the claim is read off the
     tower before the cell leaves it, not reconstructed after. *)
  Definition lk_addr_claim (a : Arch.pa) (width : Z) : iProp Σ :=
    (⌜is_aligned_paddr (Physaddr a) width = true⌝ ∗
     ∃ ppn : mword 44,
       kmap_at (svpn_of a) ppn KP_rw ∗
       ⌜(uint a < 274877906944)%Z⌝ ∗
       ⌜addr_is_ram (pa_of ppn a)⌝ ∗
       ⌜ktier_pin KT0 ppn a⌝ ∗
       ([∗ list] j ∈ seq 0 (Z.to_nat width),
          ∃ ppj : mword 44,
            kmap_at (svpn_of (pa_add a j)) ppj KP_rw ∗
            ⌜(uint (pa_add a j) < 274877906944)%Z⌝ ∗
            ⌜ktier_pin KT0 ppj (pa_add a j)⌝ ∗
            (* A6.87: RAM-ness PER BYTE.  [TsoCtxLedger.ledger_read_any_word_ok]
               -- the gate that makes the free-path word read own nothing --
               asks for it at every byte of the window, and the producer has
               it for free off the very ctx byte it is reading the mapping
               off.  Stated at [pa_add a j] rather than at [pa_of ppj _]
               because the tier pin identifies them (A6.84's [ktier_pin_id]). *)
            ⌜addr_is_ram (pa_add a j)⌝))%I.

  Global Instance lk_addr_claim_persistent a width :
    Persistent (lk_addr_claim a width).
  Proof. rewrite /lk_addr_claim. apply _. Qed.

  (* the per-byte half, which is what a free page's bytes are keyed by *)
  Lemma lk_addr_claim_bytes (a : Arch.pa) (width : Z) :
    lk_addr_claim a width ⊢
    [∗ list] j ∈ seq 0 (Z.to_nat width),
      ∃ ppj : mword 44,
        kmap_at (svpn_of (pa_add a j)) ppj KP_rw ∗
        ⌜(uint (pa_add a j) < 274877906944)%Z⌝ ∗
        ⌜ktier_pin KT0 ppj (pa_add a j)⌝ ∗
        ⌜addr_is_ram (pa_add a j)⌝.
  Proof. rewrite /lk_addr_claim. by iIntros "(_ & % & _ & _ & _ & _ & $)". Qed.

  (* the pure half, which is all [ledger_read_any_word_ok] wants *)
  Lemma lk_addr_claim_ram (a : Arch.pa) (width : Z) :
    lk_addr_claim a width ⊢
    ⌜forall j : nat, (j < Z.to_nat width)%nat -> addr_is_ram (pa_add a j)⌝.
  Proof.
    rewrite lk_addr_claim_bytes. iIntros "Hb". iIntros (j Hj).
    iDestruct (big_sepL_lookup _ _ j j with "Hb") as (ppj) "(_ & _ & _ & %Hr)".
    { rewrite lookup_seq_lt; [reflexivity | lia]. }
    by iPureIntro.
  Qed.

  (* the generic producer: a ctx WORD of any width carries its own claim --
     the base one off byte 0, the per-byte ones off each byte. *)
  Local Lemma lk_addr_claim_of_bytes (a : Arch.pa) (dq : dfrac) (w : Z)
      (f : nat -> bv 8) :
    (0 < w)%Z ->
    is_aligned_paddr (Physaddr a) w = true ->
    ([∗ list] j ∈ seq 0 (Z.to_nat w),
       ctx_pointsto (KTR := KT0) cur_ctx (pa_add a j) dq (f j))
    ⊢ lk_addr_claim a w.
  Proof.
    intros Hw Hal. iIntros "Hb".
    iAssert ([∗ list] j ∈ seq 0 (Z.to_nat w),
               ∃ ppj : mword 44,
                 kmap_at (svpn_of (pa_add a j)) ppj KP_rw ∗
                 ⌜(uint (pa_add a j) < 274877906944)%Z⌝ ∗
                 ⌜ktier_pin KT0 ppj (pa_add a j)⌝ ∗
                 ⌜addr_is_ram (pa_add a j)⌝)%I as "#Hbytes".
    { iApply (big_sepL_impl with "Hb"). iIntros "!>" (k j _) "H".
      iEval (rewrite (ctx_pointsto_phys (KTR := KT0))) in "H".
      iDestruct "H" as (ppj) "(#Hk & %Hc & %Hp & Hph)".
      iDestruct (ctx_phys_pointsto_ram with "Hph") as %Hr.
      rewrite (ktier_pin_id ppj (pa_add a j) Hp) in Hr.
      iExists ppj. iFrame "Hk". by iPureIntro. }
    iDestruct (big_sepL_lookup _ _ 0%nat 0%nat with "Hb") as "Hb0".
    { rewrite lookup_seq_lt; [reflexivity | lia]. }
    iEval (rewrite pa_add_0) in "Hb0".
    iEval (rewrite (ctx_pointsto_phys (KTR := KT0))) in "Hb0".
    iDestruct "Hb0" as (ppn) "(#Hk & %Hc & %Hp & Hph)".
    iDestruct (ctx_phys_pointsto_ram with "Hph") as %Hram.
    rewrite /lk_addr_claim.
    iSplitR; [done|]. iExists ppn. iFrame "Hk Hbytes". iPureIntro. split_and!; done.
  Qed.

  (* a ctx word carries its own claim, which is how the creators pay it *)
  Lemma lk_addr_claim_of4 (lk : mword 64) (dq : dfrac) (v : mword 32) :
    ctx_word4_pointsto (KTR := KT0) cur_ctx lk dq v ⊢ lk_addr_claim lk 4.
  Proof.
    rewrite ctx_word4_pointsto_unfold. iIntros "[%Hal Hb]".
    iApply (lk_addr_claim_of_bytes lk dq 4 (nth_byte v) ltac:(lia) Hal).
    iExact "Hb".
  Qed.

  (* ...and the EIGHT-byte one, which is how [initlock] pays for the owner
     cell's claim BEFORE the store that takes the cell out of the tower. *)
  Lemma lk_addr_claim_of8 (a : Arch.pa) (dq : dfrac) (v : mword 64) :
    ctx_word_pointsto (KTR := KT0) cur_ctx a dq v ⊢ lk_addr_claim a 8.
  Proof.
    rewrite ctx_word_pointsto_unfold. iIntros "[%Hal Hb]".
    iApply (lk_addr_claim_of_bytes a dq 8 (nth_byte v) ltac:(lia) Hal).
    iExact "Hb".
  Qed.


  (* ---- THE OWNER CELL AT THE LEDGER TIER, WITH THE RACY PAYLOAD ----

     [lk->cpu] is the one cell in the tree that is READ RACILY, by a hart
     that does not hold the lock, and what it must conclude is an
     EXCLUSION ("the recorded owner is not me").  That is a claim about
     the READER'S OWN WRITE HISTORY, so it rides in the ledger element's
     window payload (TsoMemPa §12c/§12d) and NOT in this invariant --
     tso-pin-memo.md §3's rule, and the reason the cell cannot stay in
     the ctx tower. *)
  (* >>> A6.84 (re-applied): THE RACY KIT MOVES UP.  [lk_cpu_pay]
     below is stated at [lkcpu_z] / [lkcpu_cp], so the kit that
     defines them has to precede it; nothing in the block depends on
     the physical fields, so this is a pure reordering. <<< *)

  (* ================================================================== *)
  (* THE RACY OWNER-CELL KIT AT THE LOCK'S OWN PARAMETERS                *)
  (* (tso-m4-memo.md §3/§8; tso-machine-flip.md A6.82).                   *)
  (*                                                                    *)
  (* This is what [holding()]'s [notheld] read cashes, and it is stated   *)
  (* here -- beside [lk_cpu_val] -- because its two side conditions are   *)
  (* facts about [cpus_ptr] and nothing else: the pointer is INJECTIVE    *)
  (* and never NULL.  The kit asks for them per BYTE, and the memo's      *)
  (* layout computation (§3) is why that is not the same request: for     *)
  (* harts 1..6 there is NO single byte offset separating them from every *)
  (* other hart, so a byte-keyed kit is defeated here and the WINDOW      *)
  (* form -- one timestamp resolving all eight bytes -- is what closes    *)
  (* the gap.  [nth_byte_ne] below is the whole bridge: two words that    *)
  (* differ differ AT SOME BYTE, which is all the window form needs.      *)
  (*                                                                    *)
  (* [agent] is [nat] and covers the DMA agents as well as the harts.     *)
  (* They never write a lock, and giving them [zero_reg] as their "own    *)
  (* word" is exactly what makes the per-agent distinguishing premise     *)
  (* true of them too -- by the same [cpus_ptr] nonzeroness a free lock   *)
  (* uses.                                                               *)
  (* ================================================================== *)

  (* two words that differ, differ at a byte *)
  Lemma nth_byte_ne (w1 w2 : mword 64) :
    w1 <> w2 -> exists k, (k < 8)%nat /\ nth_byte w1 k <> nth_byte w2 k.
  Proof.
    intros Hne.
    assert (H : forall l : list nat,
              (exists k, k ∈ l /\ nth_byte w1 k <> nth_byte w2 k)
              \/ (forall k, k ∈ l -> nth_byte w1 k = nth_byte w2 k)).
    { induction l as [|x xs IH].
      - right. intros k Hk. by apply elem_of_nil in Hk.
      - destruct (decide (nth_byte w1 x = nth_byte w2 x)) as [He|Hnee].
        + destruct IH as [(k & Hk & Hkk) | Hall].
          * left. exists k. split; [ by apply elem_of_cons; right | done ].
          * right. intros k Hk. apply elem_of_cons in Hk as [->|Hk];
              [ done | by apply Hall ].
        + left. exists x. split; [ by apply elem_of_cons; left | done ]. }
    destruct (H (seq 0 8)) as [(k & Hk & Hkk) | Hall].
    - exists k. apply elem_of_seq in Hk. split; [lia | done].
    - exfalso. apply Hne. apply (bv_eq_of_bytes (n := 8) w1 w2).
      intros j Hj. apply Hall, elem_of_seq. lia.
  Qed.

  (* a hart's [struct cpu] pointer is not the clear word *)
  Lemma cpus_ptr_ne_zero (i : CPU) : (zero_reg : mword 64) <> cpus_ptr i.
  Proof.
    intros Heq. pose proof (cpus_ptr_nonzero i) as Hne.
    rewrite -Heq in Hne.
    assert (Ht : eq_vec (zero_reg : mword 64) (zero_reg : mword 64) = true)
      by (apply eq_vec_true_iff; reflexivity).
    rewrite Ht in Hne. discriminate.
  Qed.

  (* the owner word of an arbitrary AGENT: a hart's [struct cpu] pointer,
     and the clear word for everything that is not a hart. *)
  Definition agent_cpus_ptr (h : agent) : mword 64 :=
    match decide (h < NCPU)%nat with
    | left Hh => cpus_ptr (nat_to_fin Hh)
    | right _ => (zero_reg : mword 64)
    end.

  Lemma agent_cpus_ptr_hart (c : CPU) : agent_cpus_ptr (hart_agent c) = cpus_ptr c.
  Proof.
    rewrite /agent_cpus_ptr. case_decide as Hh.
    - f_equal. apply fin_to_nat_inj. by rewrite fin_to_nat_to_fin.
    - exfalso. pose proof (fin_to_nat_lt c). rewrite /hart_agent in Hh. lia.
  Qed.

  Lemma agent_cpus_ptr_ne (h : agent) (c : CPU) :
    h <> hart_agent c -> agent_cpus_ptr h <> cpus_ptr c.
  Proof.
    intros Hne. rewrite /agent_cpus_ptr. case_decide as Hh.
    - intros Heq. apply cpus_ptr_inj in Heq. apply Hne.
      rewrite /hart_agent -Heq fin_to_nat_to_fin //.
    - exact (cpus_ptr_ne_zero c).
  Qed.

  (* THE TWO BYTE FUNCTIONS the owner cell's window payload is stated at:
     the CLEAR word a free lock holds, and each author's own word. *)
  Definition lkcpu_z : nat -> bv 8 := nth_byte (zero_reg : mword 64).
  Definition lkcpu_cp (h : agent) : nat -> bv 8 := nth_byte (agent_cpus_ptr h).

  (* THE [notheld] READ, DISCHARGED.  A hart whose own-last record for the
     window is [Some t] -- which every hart has from the mint until it
     acquires, and again from its own release -- and whose receipt has
     passed the floor, provably does not read its OWN [struct cpu] pointer
     out of [lk->cpu], AT EVERY view it can reach.  That is the whole
     content of [SpecAcquire]'s dead panic arm. *)
  Lemma lkcpu_read_not_mine `{CID : CpuId} (g : gstate) (lk : mword 64)
      (dq : dfrac) (f : nat -> bv 8)
      (own : agent -> option nat) (lo t K : nat) :
    own (hart_agent cpu_id) = Some t ->
    tso_interp_at riscv_eraGS g -∗
    TsoGhost.view_lb view_name loglen_name (hart_agent cpu_id) K -∗
    (* A6.111: the FLOOR, two-armed -- the reader either passed it or WROTE
       it.  A6.115: and the ANCHOR, off the cell's own invariant, which is
       what makes this work for every hart and not only the creator. *)
    TsoCtx.ledger_vis (hart_agent cpu_id) K lo -∗
    TsoCtx.ledger_vis (hart_agent cpu_id) lo t -∗
    (* A6.119: the ∃-form window -- [lk_cpu_pay]'s own shape, so the cell
       goes in without a bridge. *)
    ([∗ list] j ∈ seq 0 8, ∃ tj : nat,
       TsoCtx.phys_ledger_wpay (pa_add (lock_cpu lk) j) dq (f j) tj
         (TsoMemPa.TsWin (lock_cpu lk) 8 j lkcpu_z lkcpu_cp own lo)) -∗
    ⌜forall (tv : nat), (g.(gtv) cpu_id <= tv)%nat -> forall w : mword 64,
       tso_read_bytes g.(gimg) g.(glog) (hart_agent cpu_id) tv (lock_cpu lk)
         (N.of_nat 8) w -> w <> cpus_ptr cpu_id⌝.
  Proof.
    intros Hown.
    assert (Hcpw : forall k, (k < 8)%nat ->
              nth_byte (cpus_ptr cpu_id) k = lkcpu_cp (hart_agent cpu_id) k).
    { intros k Hk. by rewrite /lkcpu_cp agent_cpus_ptr_hart. }
    assert (Hzk : exists k, (k < 8)%nat /\
              lkcpu_z k <> lkcpu_cp (hart_agent cpu_id) k).
    { rewrite /lkcpu_z /lkcpu_cp agent_cpus_ptr_hart.
      apply nth_byte_ne. exact (cpus_ptr_ne_zero cpu_id). }
    assert (Hinj : forall h', h' <> hart_agent cpu_id ->
              exists k, (k < 8)%nat /\
                lkcpu_cp h' k <> lkcpu_cp (hart_agent cpu_id) k).
    { intros h' Hne. rewrite /lkcpu_cp (agent_cpus_ptr_hart cpu_id).
      apply nth_byte_ne. exact (agent_cpus_ptr_ne h' cpu_id Hne). }
    iIntros "Hint #HK #Hfv #Hav Hb".
    iApply (TsoCtx.ledger_read_racy_word_ok g (lock_cpu lk) 8%nat dq f
              lkcpu_z lkcpu_cp own lo t K (m := 64) (cpus_ptr cpu_id)
              ltac:(lia) Hown Hcpw Hzk Hinj with "Hint HK Hfv Hav Hb").
  Qed.

  (* [s] -- the lock's NAME -- rather than a bare rank: [is_lock] already
     carries it, so instantiating with [lock_rank s] leaves no second degree
     of freedom that could disagree with the name in [lock_name]. *)
  (* THE PAYLOAD IS A FUNCTION OF THE CONTEXT (tso-port M3).  A lock's
     facts belong, at any moment, to a THREAD OF CONTROL: the depositor's
     until release re-indexes them, the lock's own while parked here, the
     acquirer's after its AMO.  A fixed [iProp] payload cannot say that --
     whichever context its facts were elaborated at, every OTHER thread's
     acquire would receive them at the wrong index.  So [R : CtxId →
     iProp]; clients write payloads with the ambient spellings under
     [TsoCtx]'s [<{ P }>] wrapper and owe [CtxMorph R] at acquire/release
     (SpecAcquire.v / SpecRelease.v) -- a payload that fails it
     structurally is a real TSO bug found early.


     AT SC the parked payload is the ∃-closure below: the index is
     phantom under the seal, so "some context's facts" is as strong as
     anyone's, and the acquire-side re-indexing is a [CtxMorph] step
     against the shim's [ctx_dom_sc].  AT CUTOVER this free arm instead
     holds [R ξ_L] beside the lock's own internal context token
     ([TsoCtxTwin2]'s parked shape: release deposits by
     [ctx_dom_to_parked]-transport, acquire withdraws by
     [ctx_dom_of_parked] against its AMO-at-the-top evidence); the
     statement list above this definition is what stays. *)

  Definition lk_cpu_pay (lk : mword 64) (v : mword 64)
      (own : agent -> option nat) (lo : nat) : iProp Σ :=
    ([∗ list] j ∈ seq 0 8, ∃ t : nat,
       TsoCtx.phys_ledger_wpay (pa_add (lock_cpu lk) j) (DfracOwn 1)
         (nth_byte v j) t
         (TsoMemPa.TsWin (lock_cpu lk) 8 j lkcpu_z lkcpu_cp own lo))%I.

  (* the AUTHOR's form: the same window with the store's own message
     fragment beside every byte.  That is what makes the HOLDER's read of
     the cell IT wrote exact ([TsoCtxLedger.ledger_read_wpay_vis_ok]) -- and it
     is why the held arm carries more than the free one, which A6.78 §(2)
     named and nothing before it did. *)
  Definition lk_cpu_pay_vis (h : agent) (lk : mword 64) (v : mword 64)
      (own : agent -> option nat) (lo : nat) : iProp Σ :=
    ([∗ list] j ∈ seq 0 8, ∃ t : nat,
       TsoCtx.ledger_vis h 0 t ∗
       TsoCtx.phys_ledger_wpay (pa_add (lock_cpu lk) j) (DfracOwn 1)
         (nth_byte v j) t
         (TsoMemPa.TsWin (lock_cpu lk) 8 j lkcpu_z lkcpu_cp own lo))%I.

  Lemma lk_cpu_pay_vis_forget h lk v own lo :
    lk_cpu_pay_vis h lk v own lo ⊢ lk_cpu_pay lk v own lo.
  Proof.
    rewrite /lk_cpu_pay_vis /lk_cpu_pay.
    iIntros "H". iApply (big_sepL_impl with "H").
    iIntros "!>" (k j _) "(%t & _ & H)". by iExists t.
  Qed.

  Global Instance lk_cpu_pay_timeless lk v own lo :
    Timeless (lk_cpu_pay lk v own lo).
  Proof. rewrite /lk_cpu_pay. apply _. Qed.
  Global Instance lk_cpu_pay_vis_timeless h lk v own lo :
    Timeless (lk_cpu_pay_vis h lk v own lo).
  Proof. rewrite /lk_cpu_pay_vis. apply _. Qed.

  (* >>> THE OWN-INVARIANT, AND IT IS ONE SENTENCE: the ONLY agent that
     may be missing an own-last record is the HOLDER.  Acquire's store
     writes the author's own word and REVOKES its entry
     ([ledger_store_wpay_ok]'s second arm); release's writes the clear
     word and RESTORES it (the first).  Every other agent's entry frames.
     A [notheld] reader is a non-holder by definition, so this is exactly
     the premise [lkcpu_read_not_mine] consumes. <<< *)
  Definition lk_own_ok (ex : option CPU) (own : agent -> option nat) : Prop :=
    forall h : agent, own h = None -> exists i : CPU, ex = Some i /\ h = hart_agent i.

  (* >>> §0.35′(i): THE FLOOR IS PINNED, NOT EXISTENTIAL.  The window's mint
     position was ∃-bound here, which is exactly why A6.89 §(7)'s [notheld]
     read could not state its premise: [lo] was invisible outside the
     invariant, so no leaf could ask for [⌜lo ≤ K⌝] and no handle could carry
     it.  Pinning it as a PARAMETER is the surface half of the ruling; the
     handle then carries [TsoCtx.ctx_floor ξ lo] for THIS [lo] and the reads
     discharge against it ([TsoCtx.own_context_floor_view]).
     [own] stays existential: it is per-agent bookkeeping the reads consume
     through [lk_own_ok], not something a handle can name. <<< *)
  (* >>> A6.115 (approved on A6.114's pricing): THE CELL'S PER-AGENT ANCHOR.
     Every agent's own-last record is either the FLOOR itself or its OWN
     message -- which is [TsoCtx.ledger_vis h lo t] read at [(lo, t)], since
     [win_ok1] already gives [lo ≤ t] and so collapses that predicate's left
     arm to [t = lo].

     PRESERVED BY EVERY TRANSITION, and each discharge is one lemma: the mint
     sets [own = fun _ => Some lo] ([ledger_vis_below], free); acquire's store
     sets the writer's entry to [None] (nothing to prove); release's sets it
     to the store's own position ([ledger_vis_own] on the message fragment
     [WpSconfMem.word_wpay_frame_store_gen_c] now hands back, A6.114 §4).  Both
     store arms move only the writer's entry, so every other agent's clause
     rides across untouched.

     WHAT IT BUYS: the racy read's ANCHOR premise, for EVERY hart rather than
     only the lock's creator -- left arm and the anchor IS the floor, right arm
     and it is visible by authorship at any view.  A6.110 §5's two arguments
     collapse into one. <<< *)
  Definition lk_own_anchored (lo : nat) (own : agent -> option nat) : iProp Σ :=
    (∀ (h : agent) (t : nat),
       ⌜own h = Some t⌝ -∗ TsoCtx.ledger_vis h lo t)%I.

  Global Instance lk_own_anchored_persistent lo own :
    Persistent (lk_own_anchored lo own).
  Proof. apply _. Qed.

  Lemma lk_own_anchored_mint (lo : nat) :
    ⊢ lk_own_anchored lo (fun _ => Some lo).
  Proof.
    iIntros (h t) "%Heq". injection Heq as <-.
    iApply TsoCtx.ledger_vis_below. lia.
  Qed.

  Definition lk_cpu_cell_ex (lo : nat) (lk : mword 64) (v : mword 64)
      (ex : option CPU) : iProp Σ :=
    (∃ (own : agent -> option nat),
       ⌜lk_own_ok ex own⌝ ∗ lk_own_anchored lo own ∗
       match ex with
       | Some i => lk_cpu_pay_vis (hart_agent i) lk v own lo
       | None => lk_cpu_pay lk v own lo
       end)%I.

  Definition lk_cpu_cell (lo : nat) (lk : mword 64) (v : mword 64) : iProp Σ :=
    lk_cpu_cell_ex lo lk v None.

  (* A6.119: THE CELL AS A PLAIN WINDOW, AT EITHER ARM.  The racy read does
     not care who holds the lock -- it only needs the window, the per-agent
     record and the anchor -- so it takes this projection rather than
     case-splitting on [ex] at every site.  The held arm's author fragment is
     dropped ([lk_cpu_pay_vis_forget]); the free arm is already this shape. *)
  Lemma lk_cpu_cell_ex_pay (lo : nat) (lk : mword 64) (v : mword 64)
      (ex : option CPU) :
    lk_cpu_cell_ex lo lk v ex ⊢
    ∃ own : agent -> option nat,
      ⌜lk_own_ok ex own⌝ ∗ lk_own_anchored lo own ∗ lk_cpu_pay lk v own lo.
  Proof.
    iIntros "(%own & %Hok & #Han & Hb)". iExists own.
    iSplitR; [done|]. iFrame "Han".
    destruct ex as [i|]; [ by iApply lk_cpu_pay_vis_forget | iExact "Hb" ].
  Qed.

  (* the reader's own-last record, out of [lk_own_ok] at a state it does not
     hold: only the HOLDER may be missing one. *)
  Lemma lk_own_ok_some (ex : option CPU) (own : agent -> option nat)
      (i : CPU) :
    lk_own_ok ex own -> ex <> Some i ->
    exists t : nat, own (hart_agent i) = Some t.
  Proof.
    intros Hok Hne. destruct (own (hart_agent i)) as [t|] eqn:Heq.
    - by exists t.
    - destruct (Hok _ Heq) as (i' & -> & Hag).
      exfalso. apply Hne. f_equal. symmetry.
      apply fin_to_nat_inj. exact Hag.
  Qed.

  (* the held cell forgets its author fragment and becomes an ordinary
     one, at the cost of the exactness the holder had *)
  Lemma lk_cpu_cell_ex_forget lo lk v ex :
    lk_cpu_cell_ex lo lk v ex ⊢ lk_cpu_cell lo lk v ∨ ⌜is_Some ex⌝.
  Proof.
    iIntros "(%own & %Hok & #Han & Hb)". destruct ex as [i|].
    - iRight. iPureIntro. by eexists.
    - iLeft. iExists own. by iFrame "Han Hb".
  Qed.

  (* what [initlock]'s post hands over and every creator takes: the
     window payload at the CLEAR word, plus the address claim the ledger
     cells do not carry. *)
  (* >>> A6.105: THE CELL AT AN ARBITRARY VALUE, which is what [initlock]
     takes IN.  §0.35′'s floor-0 route needs the owner field's window minted
     BEFORE the `sd x0` (off the era image, at floor 0) and the store to FRAME
     that floor -- so [initlock]'s precondition is this at the cell's OLD
     value and its postcondition is [lk_cpu_fresh] = this at the clear word.
     Same proposition, one argument apart. <<< *)
  Definition lk_cpu_at (lo : nat) (lk : mword 64) (v : mword 64) : iProp Σ :=
    (lk_addr_claim (lock_cpu lk) 8 ∗ lk_cpu_cell lo lk v)%I.

  Definition lk_cpu_fresh (lo : nat) (lk : mword 64) : iProp Σ :=
    lk_cpu_at lo lk (zero_reg : mword 64).

  Lemma lk_cpu_fresh_at (lo : nat) (lk : mword 64) :
    lk_cpu_fresh lo lk ⊣⊢ lk_cpu_at lo lk (zero_reg : mword 64).
  Proof. reflexivity. Qed.

  (* >>> A6.105: THE FLOOR RIDES WITH THE CELL, and that is what keeps the
     whole creator sweep to a rename.  A creator needs two things to hand
     back a HANDLE -- the owner cell at some floor, and THIS context's claim
     to have passed that floor -- and no client ever names the floor itself.
     So they travel bundled, existentially, exactly as [lo] travels inside
     [is_lock]: every spec that said [lk_cpu_fresh lk] says [lk_cpu_ready lk]
     and keeps its arity, and [newlock] takes this in place of the cell plus
     a separate [ctx_floor] premise.
     A6.97's rule for the third time: a parameter no consumer NAMES does not
     belong in the arity. <<< *)
  (* >>> A6.105: THE FLOOR CERTIFICATE HAS TWO ARMS, and the second is the
     one a CREATOR can actually buy.

     Ruling §0.35'(i) puts [ctx_floor ξ lo] inside the handle so that every
     read can discharge its floor against [own_context].  That arm is free at
     [lo = 0] -- a boot lock's cell is an era-image cell -- but at a DYNAMIC
     lock it is unbuyable, and for the same reason A6.101 gave one level
     down: the creator's own [sd] is BUFFERED, so the store that made the
     floor never advances the storer's own view, and no fence or AMO stands
     between [initlock]'s store and the handle's construction.  Measured,
     not guessed: [ctx_bound_raise] wants [hart_view_lb lo] and the creator
     has no receipt at [lo].

     The right arm is what it DOES have: "[lo] is a real log position"
     ([TsoGhost.llb loglen_name lo], handed out by the store leaf beside the
     window).  Paired with an AMO's log-top view it yields the left arm on
     the spot -- [TsoCtxLedger.hart_view_lb_get] then [ctx_bound_raise] -- which is
     ruling §0.35'(iii)'s ABSORB, verbatim, at the first acquire.  So the
     floor is bought by the READER that needs it exact, not by the writer
     that cannot.

     The handle stays ξ-indexed (the left arm names [cur_ctx]), so §0.16''s
     crossing discipline is unchanged; what moves is WHERE the purchase
     happens. <<< *)
  (* >>> A6.120: THE RIGHT ARM IS THE OWN-WRITE WITNESS, not a bare log
     position.  §0.38′'s reading -- "you received this handle, or you wrote
     this lock" -- is now spelled with the ctx tower's own dirty witness
     ([TsoCtx.ctx_wrote]: the floor message is a dirty key of the creating
     context), which the read cashes against the running token on EITHER
     arm ([lk_floor_vis]).  A6.113 had measured that the bare [llb] cannot
     be cashed at a read at all (a view and a log position compare only at
     an AMO) -- which is what made the crossing upgrade look universal and
     left the creator's own first acquire (kinit's kfree, printfinit's
     printf) with no route.  The [llb] stays beside the witness: it is what
     [initlock] already exports, and the AMO-side upgrade
     ([TsoCtxLedger.hart_view_lb_get]) still reads it. <<< *)
  (* A6.123: the [llb] that used to ride beside the witness is gone -- no
     consumer read it (the read cashes the witness alone, [lk_floor_vis]),
     and a cell forgotten out of the tower has the witness but no
     log-length receipt ([TsoCtx.ctx_phys_pointsto_forget_floor]).  The
     arm is the witness, full stop. *)
  Definition lk_floor (ξ : TsoCtx.CtxId) (lo : nat) : iProp Σ :=
    (TsoCtx.ctx_floor ξ lo ∨ ∃ a : Arch.pa, TsoCtx.ctx_wrote ξ lo a)%I.

  Global Instance lk_floor_persistent ξ lo : Persistent (lk_floor ξ lo).
  Proof. apply _. Qed.

  Lemma lk_floor_0 ξ : ⊢ lk_floor ξ 0.
  Proof. iLeft. iApply TsoCtx.ctx_floor_0. Qed.

  Lemma lk_floor_of_ctx ξ lo : TsoCtx.ctx_floor ξ lo -∗ lk_floor ξ lo.
  Proof. iIntros "H". by iLeft. Qed.

  Lemma lk_floor_of_wrote ξ lo (a : Arch.pa) :
    TsoCtx.ctx_wrote ξ lo a -∗ lk_floor ξ lo.
  Proof. iIntros "#Hw". iRight. by iExists a. Qed.

  (* A6.123: the floor TRANSPORTS -- both arms land on the receiver's LEFT
     arm (A6.117's [ctx_floor_dom], A6.120's [ctx_dom_wrote_floor]), so a
     payload that carries a floor (a lease-held word's, a nested handle's)
     is [CtxMorph] with no absorb capability at all. *)
  Global Instance lk_floor_morph (lo : nat) : CtxMorph (λ ξ, lk_floor ξ lo).
  Proof.
    iIntros (ξ ξ') "Hd [#Hfl | (%a & #Hw)]".
    - iDestruct (TsoCtx.ctx_floor_dom with "Hd Hfl") as "[Hd #Hfl']".
      iModIntro. iFrame "Hd". by iLeft.
    - iDestruct (TsoCtx.ctx_dom_wrote_floor with "Hd Hw") as "[Hd #Hfl']".
      iModIntro. iFrame "Hd". by iLeft.
  Qed.

  (* A6.120: THE READ-SIDE CASH-IN, ON EITHER ARM.  The left arm is
     [TsoCtx.own_context_floor_view] (the bound has passed the floor, so
     the view has); the right is [TsoCtx.own_context_wrote_vis] (the floor
     message is a dirty key of my context: below my bound, or MINE).  Both
     land on [ledger_vis] at the token's own receipt, which is exactly the
     premise [lkcpu_read_not_mine] takes -- so the racy read needs no
     absorbed opener and [lock_openable_c] has no consumer left. *)
  Lemma lk_floor_vis `{CID : CpuId} (ξ : TsoCtx.CtxId) (lo : nat) :
    TsoCtx.own_context ξ -∗ lk_floor ξ lo -∗
    TsoCtx.own_context ξ ∗ ∃ K : nat,
      TsoGhost.view_lb view_name loglen_name (hart_agent cpu_id) K ∗
      TsoCtx.ledger_vis (hart_agent cpu_id) K lo.
  Proof.
    iIntros "Hrun #Hfl". iDestruct "Hfl" as "[#Hfl | (%a & #Hw)]".
    - iDestruct (TsoCtx.own_context_floor_view with "Hrun Hfl")
        as "[Hrun (%K & #HK & %HloK)]".
      iFrame "Hrun". iExists K. iFrame "HK". by iApply TsoCtx.ledger_vis_below.
    - iApply (TsoCtx.own_context_wrote_vis with "Hrun Hw").
  Qed.

  Definition lk_cpu_ready_at (lk : mword 64) (v : mword 64) : iProp Σ :=
    (∃ lo : nat, lk_cpu_at lo lk v ∗ lk_floor cur_ctx lo)%I.

  Definition lk_cpu_ready (lk : mword 64) : iProp Σ :=
    lk_cpu_ready_at lk (zero_reg : mword 64).

  (* >>> A6.89: THE WORD'S TWIN OF [lk_cpu_fresh], AND IT IS OWED FOR THE
     SAME REASON ONE FIELD OVER.  Release's [sw x0] leaves a LEDGER word
     behind ([lock_word] = [phys_ledger_word4]); the ctx tower cannot take
     it back (that needs a drain, A6.84 §(2)), so the FINISHER's word slot
     -- the thing release hands over at the instant the lock goes free --
     can no longer be the ctx word [lk ↦₄ 0] it was before the M4 flip.
     It is the ledger word plus the address claim a ledger cell does not
     carry: exactly [lk_cpu_fresh]'s shape.

     The CREATORS are untouched: [initlock] genuinely holds a ctx word and
     converts it once, one-way, with [lock_word_intro].  Only the exit
     moves. <<< *)
  Definition lock_word_fresh (lk : mword 64) : iProp Σ :=
    (lk_addr_claim lk 4 ∗ lock_word lk (mword_of_int 0 : mword 32))%I.

  (* the same reclamation [lk_cpu_fresh_free] does for the owner cell: a
     lock on a kalloc'd page must be able to die, and the word's four
     bytes go home to [kfree] at the visibility-free tier (§0.26′/§0.32′). *)
  Lemma lock_word_fresh_free (lk : mword 64) :
    lock_word_fresh lk ⊢
    [∗ list] j ∈ seq 0 4,
      TsoCtx.mem_free (KTR := KT0) (pa_add lk j) (DfracOwn 1).
  Proof.
    rewrite /lock_word_fresh /lock_word TsoCtx.phys_ledger_word4_unfold.
    iIntros "[#Hcl [_ Hp]]".
    iDestruct (lk_addr_claim_bytes with "Hcl") as "#Hb".
    change (Z.to_nat 4) with 4%nat.
    iApply (big_sepL_impl with "Hp"). iIntros "!>" (k j Hk) "Hw".
    iDestruct (big_sepL_lookup _ _ k j Hk with "Hb") as (ppj) "(#Hkj & %Hcj & %Hpj & _)".
    rewrite /TsoCtx.mem_free. iExists ppj. iFrame "Hkj".
    iSplitR; [done|]. iSplitR; [done|].
    rewrite (ktier_pin_id ppj (pa_add lk j) Hpj).
    by iApply TsoCtx.phys_ledger_free.
  Qed.

  (* THE RECLAMATION, AND IT IS THE WHOLE POINT (tso-port.md §0.26′).
     A lock on a kalloc'd page must be able to DIE.  Its owner word is a
     ledger cell and cannot re-enter the ctx tower -- that needs a drain
     (A6.84 §(2)) -- but it does not have to: [kfree] wants only the page's
     FUTURE, and a wpay cell has one.  The claim supplies the mapping the
     cell dropped; the payload supplies the fraction and the element. *)
  Lemma lk_cpu_fresh_free (lo : nat) (lk : mword 64) :
    lk_cpu_fresh lo lk ⊢
    [∗ list] j ∈ seq 0 8,
      TsoCtx.mem_free (KTR := KT0) (pa_add (lock_cpu lk) j) (DfracOwn 1).
  Proof.
    rewrite /lk_cpu_fresh /lk_cpu_at /lk_cpu_cell /lk_cpu_cell_ex /lk_cpu_pay.
    iIntros "[#Hcl (%own & _ & _ & Hp)]".
    iDestruct (lk_addr_claim_bytes with "Hcl") as "#Hb".
    change (Z.to_nat 8) with 8%nat.
    iApply (big_sepL_impl with "Hp"). iIntros "!>" (k j Hk) "(%t & Hw)".
    iDestruct (big_sepL_lookup _ _ k j Hk with "Hb") as (ppj) "(#Hkj & %Hcj & %Hpj & _)".
    rewrite /TsoCtx.mem_free. iExists ppj. iFrame "Hkj".
    iSplitR; [done|]. iSplitR; [done|].
    rewrite (ktier_pin_id ppj (pa_add (lock_cpu lk) j) Hpj).
    by iApply TsoCtx.phys_ledger_wpay_free.
  Qed.

  Definition lk_cpu_res (lo : nat) (st : lock_state) (lk : mword 64) (r : string) : iProp Σ :=
    (lk_cpu_cell_ex lo lk (lk_cpu_val st) (lk_ex st) ∗ lk_cpu_frag st r)%I.

  (* the leaves strip this under [>] inside the step engine's callback, and
     [st] is a VARIABLE there, so the match is stuck and the structural
     instances cannot see the two branches.  Stated once, here. *)
  Global Instance lk_cpu_frag_timeless st r : Timeless (lk_cpu_frag st r).
  Proof. destruct st as [[i []]|]; apply _. Qed.
  Global Instance lk_cpu_res_timeless lo st lk r : Timeless (lk_cpu_res lo st lk r).
  Proof. apply _. Qed.

  (* THE OWNER CELL, NAMED (§6 amendment A6.8).  The SC-era file stated the
     ∃-cell EQUAL to the acting hart's ambient form ([lk_cpu_cell_acc], via
     the shim) and phrased the three unfold lemmas at that ambient form.
     THE ELIMINATION DIRECTION IS FALSE AT TSO -- a ledger fact is pinned to
     its context, and the ∃ hides WHICH, so nothing can dominate it -- so the
     equation is gone and the unfold lemmas are stated at the cell itself.
     [lk_cpu_cell_intro] is the surviving (trivial) half.

     WHAT THE ELIMINATION NEEDS, so the M4 worklist entry is written down
     rather than implied: the invariant must hold the cell's context PARKED
     ([TsoCtx.ctx_parked ξ T]) beside the word, and the acquirer -- whose
     AMO puts its view at the log top -- mints [ctx_dom ξ cur_ctx] from it
     with [TsoCtxLedger.ctx_dom_of_parked] and moves the word with
     [ctx_morph_word].  That is the racy-kit design; it is the ONE reason
     [lk_cpu_res] may not simply go ambient (an ambient index in the payload
     would drag a context into the persistent [is_lock] handle).  The
     failures at the leaves that read and write this cell
     ([WpSconfLock]) are that entry. *)
  (* the free / window form: the whole cell at 0 and no fragment. *)
  Lemma lk_cpu_res_free (lo : nat) (lk : mword 64) (r : string) :
    lk_cpu_res lo None lk r ⊣⊢ lk_cpu_cell lo lk (zero_reg : mword 64).
  Proof. rewrite /lk_cpu_res /lk_cpu_cell /=. apply bi.sep_emp. Qed.
  Lemma lk_cpu_res_win (lo : nat) (i : CPU) (lk : mword 64) (r : string) :
    lk_cpu_res lo (Some (i, false)) lk r ⊣⊢ lk_cpu_cell lo lk (zero_reg : mword 64).
  Proof. rewrite /lk_cpu_res /lk_cpu_cell /=. apply bi.sep_emp. Qed.
  (* THE HELD FORM CARRIES MORE THAN THE OTHER TWO, and that is the
     author-fragment point (A6.78 §(2)): the holder's own read of the
     cell must be EXACT, so the held cell keeps the store's message
     fragment beside every byte. *)
  Lemma lk_cpu_res_held (lo : nat) (i : CPU) (lk : mword 64) (r : string) :
    lk_cpu_res lo (Some (i, true)) lk r ⊣⊢
    lk_cpu_cell_ex lo lk (cpus_ptr i) (Some i) ∗ lk_in i r.
  Proof. rewrite /lk_cpu_res /=. reflexivity. Qed.

  (* A6.66 THE PARKED-RECORD FREE ARM (tso-port.md §0.18′, ported from the
     main tree's landed shape).  The free arm holds the payload's facts
     BESIDE the record's own context token, so release deposits into a
     fresh record and acquire absorbs out of it -- and [ctx_dom] leaves
     the lock's transport path entirely.
     PER-PUBLICATION, not per-lock: §0.18′'s stamp analysis says the tie
     [T' ≤ t_release] is per-publication, so a record is minted at each
     release and abandoned by the winner that claims it.  Nothing needs to
     ratchet across generations and no token travels with the holder. *)
  Definition lock_pay (R : CtxId -> iProp Σ) : iProp Σ :=
    (∃ (ξ : CtxId) (T : nat), ctx_parked ξ T ∗ R ξ)%I.

  (* A6.120: THE WINNER'S FORM of the record -- the same record, plus the
     acquirer's floor AT THE RECORD'S STAMP.  The AMO leaf mints it: the
     stamp is a legal log position, hence below the AMO's own, and the leaf
     already exports [ctx_floor cur_ctx] at that position for the holder
     token.  This is the "stable pair" A6.116 §1 found the bare receipt
     lacked, in §0.38′'s one agreed spelling ([ctx_floor], re-cashed into
     [hart_view_lb K ∗ ⌜T ≤ K⌝] by [TsoCtx.own_context_floor_view]); with it
     [SpecAcquire]'s absorb is [TsoCtxAbsorbLb.ctx_absorb_lb] and the
     retired SC shim [ctx_dom_sc] has nothing left to conjure. *)
  Definition lock_pay_won (R : CtxId -> iProp Σ) : iProp Σ :=
    (∃ (ξ : CtxId) (T : nat),
       ctx_parked ξ T ∗ TsoCtx.ctx_floor cur_ctx T ∗ R ξ)%I.

  (* THE CREATOR'S MINT -- AND HERE IT IS HONEST, WHICH IT IS NOT ON MAIN.
     §0.18′ had to quarantine this at one site behind the shim's
     [ctx_dom_sc], because at SC there is no way to move a payload onto a
     fresh parked context.  THIS tree has the real [ctx_deposit], so the
     mint is a plain deposit into a freshly allocated record and there is
     NO quarantine anywhere on the lock's transport path.
     WHAT IT COSTS INSTEAD, and the trade is worth naming: [ctx_deposit]
     wants the creator's running token, so this lemma takes [own_context]
     and hands it straight back.  That is the 19-call-site creator cascade
     §0.18′ priced and deferred -- deferred there because the quarantine
     was cheaper, taken here because the honest proof exists.  Every
     newlock wrapper gains a token it already has in scope at its call
     sites. *)
  (* A6.64's lesson applies to the STATEMENT here: [own_context] is
     CpuId-indexed, and this section binds no [CpuId], so the creator's
     hart is a parameter -- the token the caller hands over is at ITS
     hart, not at some ambient one. *)
  Lemma lock_pay_intro `{CID : CpuId} (R : CtxId -> iProp Σ) `{!CtxMorph R} :
    own_context cur_ctx -∗ R cur_ctx ==∗ own_context cur_ctx ∗ lock_pay R.
  Proof.
    iIntros "Hrun HR".
    iMod ctx_parked_alloc as (ξc) "Hpk".
    iMod (ctx_deposit R cur_ctx ξc 0 with "Hrun Hpk HR")
      as "(Hrun & %T' & _ & Hpk & HR)".
    iModIntro. iFrame "Hrun". iExists ξc, T'. iFrame "Hpk HR".
  Qed.

  (* >>> A6.144: THE FLOORED MINT -- the release-side answer to the
     fresh-stores asymmetry (A6.113's, arriving at the PAYLOAD tier).  A
     releaser cannot floor a position covering its own buffered stores at
     its own context (its bound is capped by its view), so a payload row
     [λ ξ, ctx_floor ξ tl] with [tl] at or above those stores is
     unmintable through the plain deposit.  But the RECORD has no hart:
     [TsoCtxPark.ctx_parked_raise] lifts its stamp past ANY legal log
     position for free and hands back exactly the floor.  So the mint is:
     deposit as always, raise the record at the row's [llb], fold the
     floor in.  The acquire side is unchanged -- the row rides the
     ordinary payload transport ([TsoCtx.ctx_floor_dom]) and the winner
     cashes it against its own running token
     ([TsoCtx.own_context_floor_view]).

     THE TWO CLIENTS this was built for (both measured in the A6.141-43
     line): the itable's exact count read under itable.lock (the row
     floors the last count store's position, [llb] off the store leaf),
     and the CtxAnchor guard's slot mint (the row floors the anchor's
     raised stamp, [llb] off [CtxAnchor.anchor_deposit]). <<< *)
  Lemma lock_pay_intro_llb `{CID : CpuId} (R R' : CtxId -> iProp Σ)
      `{!CtxMorph R} (tl : nat) :
    (forall ξ : TsoCtx.CtxId, R ξ ∗ TsoCtx.ctx_floor ξ tl ⊢ R' ξ) ->
    TsoGhost.llb loglen_name tl -∗
    own_context cur_ctx -∗ R cur_ctx ==∗ own_context cur_ctx ∗ lock_pay R'.
  Proof.
    iIntros (Hfold) "#Hllb Hrun HR".
    iMod ctx_parked_alloc as (ξc) "Hpk".
    iMod (ctx_deposit R cur_ctx ξc 0 with "Hrun Hpk HR")
      as "(Hrun & %T' & _ & Hpk & HR)".
    iMod (TsoCtxPark.ctx_parked_raise ξc T' tl with "Hllb Hpk")
      as "[Hpk #Hfl]".
    iModIntro. iFrame "Hrun". iExists ξc, (Nat.max T' tl). iFrame "Hpk".
    iApply Hfold. iFrame "HR Hfl".
  Qed.

  (* THE TWO ADDRESS CLAIMS RIDE HERE, LAST, and outside the ∃: they are
     about the ADDRESSES, so no state mentions them, and they are
     persistent, so one peek serves every leaf.  They are what the ledger
     tier costs (a ledger cell carries no mapping) and they are cheaper
     than what they replaced -- [lock_claims] used to have to take the
     cell APART to read a claim off it, and that is where the last live
     [TsoCtxShim] use lived. *)
  (* A6.87: THE BODY IS NAMED.  Every leaf opens the invariant to work on
     the CELLS; the two address claims are persistent scenery that has to
     be put back untouched.  Naming the ∃-part keeps each leaf's
     [iDestruct] shape exactly what it was before the M4 flip -- the leaf
     peels the claims off once with [lock_inv_open] and hands them back
     with [lock_inv_close], and nothing else about it moves. *)
  (* §0.35′(i): the body is stated AT the lock's floor [lo]; the handle
     carries the matching [TsoCtx.ctx_floor ξ lo]. *)
  Definition lock_body (γ : gname) (lk : mword 64) (s : string)
      (R : CtxId → iProp Σ) (lo : nat) : iProp Σ :=
    (* >>> A6.119 (executing A6.92's own conclusion, and §0.35′(iv) case 2).
       THE WORD'S AUTHORSHIP ARM COMES OUT OF THE INVARIANT.  [lk_wex] indexed
       it by the state's [Some i], i.e. by the HOLDER -- and `amoswap` writes
       UNCONDITIONALLY, so a spinner that finds the lock held still stores the
       word.  After a failed acquire the word is the SPINNER's own write while
       the state, and hence [lk_wex], still names the holder: the invariant
       cannot be re-established, and no premise repairs it.  A6.92 refuted the
       held arm on exactly this ground and recorded that [lk_wex] should be
       withdrawn with it; this is that withdrawal, reaching the one site the
       file's red-upstream had hidden.

       WHY THE PLAIN WORD SUFFICES, measured rather than assumed: nothing
       outside this definition consumed the held arm.  [lock_word_ex] stays,
       and stays USED -- inside [WpSconfLock]'s AMO plumbing, where the
       acquiring hart really does own its write between its own mint and the
       close -- but it is no longer an INVARIANT INDEX.  §0.35′(iv) case 2
       reads the locked word on the racy kit against a value-set, not against
       an authorship arm, so the exact form was never what the reads wanted.
       [lk_wex] demotes to a pure state function. <<< *)
    (∃ (v : mword 32) (st : lock_state) (B : nat),
        (* A6.119: arm-shaped by the state, and the ACQUIRE POSITION [B] is
           exposed here beside the pin so [lock_auth_at] can tie it to the
           holder's half ([lock_pos_agree]).  That tie is what lets the
           holder's read name the pin's own [B] -- the one thing carrying the
           body whole across the atomic update could not supply, because it
           fixes witness identity and cannot manufacture evidence about the
           reader. *)
        lock_word_at st B lk v ∗
        lk_cpu_res lo st lk s ∗
        lock_auth_at γ st B ∗
        (⌜st = None⌝ ∗ ⌜v = (mword_of_int 0 : mword 32)⌝ ∗ lock_frag γ None ∗
           lock_pay R
         ∨ ⌜st ≠ None⌝ ∗ ⌜neq_vec (sign_extend' 64 v) zero_reg = true⌝))%I.

  Definition lock_inv (γ : gname) (lk : mword 64) (s : string)
      (R : CtxId → iProp Σ) (lo : nat) : iProp Σ :=
    (lock_body γ lk s R lo ∗
     lk_addr_claim lk 4 ∗ lk_addr_claim (lock_cpu lk) 8)%I.

  Lemma lock_inv_open γ lk s R lo :
    lock_inv γ lk s R lo ⊢
    lock_body γ lk s R lo ∗ lk_addr_claim lk 4 ∗ lk_addr_claim (lock_cpu lk) 8.
  Proof. by rewrite /lock_inv. Qed.

  Lemma lock_inv_close γ lk s R lo :
    lk_addr_claim lk 4 -∗ lk_addr_claim (lock_cpu lk) 8 -∗
    lock_body γ lk s R lo -∗ lock_inv γ lk s R lo.
  Proof. rewrite /lock_inv. iIntros "#H4 #H8 $". by iFrame "H4 H8". Qed.

  (* the lock's NAME: [lk->name] (the 8-byte pointer field at +8) holds the
     address of a NUL-terminated string [s].  initlock writes the field once
     and nothing ever writes it again, so both the field and the string it
     points at are held at [DfracDiscarded] -- [lock_name] is PERSISTENT, and
     therefore rides along inside the (persistent) lock predicate at no
     ownership cost: no proof has to thread the name field, and every holder
     of the lock knows which lock it is by name. *)
  Definition lock_name_field (lk : mword 64) : mword 64 :=
    add_vec lk (sign_extend' 64 (mword_of_int 8 : mword 12)).

  (* CONTEXT-FREE, deliberately, and in the two different ways the port has
     for it.  The name field is lock METADATA -- written once by initlock,
     discarded, read by nobody's data path -- and it rides inside [is_lock];
     were either half of it stated at an ambient ξ, that ξ would be in the
     HANDLE, and a handle minted at boot's context could not even be stated
     at another thread's (§0.8′ ruling 2, which the park rows depend on).

     - the FIELD is the RAW [word_pointsto] (the M1 flip's ruling; the intro
       below converts the minter's context-indexed store result through the
       shim);
     - the STRING is [TsoCtx.ctx_string_all], the ∀-context DERIVED form of
       [↦ₛ] (§0.21′).  [↦ₛ] itself is context-relative now -- it has to be,
       [p->name] is written at runtime -- so the handle takes the derived
       fact, which [KernelDataInv.kernel_data_string_all] mints for a rodata
       literal with no seam at all. *)
  Definition lock_name (lk : mword 64) (s : string) : iProp Σ :=
    (∃ p : mword 64,
       word_pointsto (lock_name_field lk) DfracDiscarded p ∗
       ctx_string_all p DfracDiscarded s)%I.

  Global Instance lock_name_persistent lk s : Persistent (lock_name lk s).
  Proof. apply _. Qed.

  (* Sealing the name field.  [initlock] hands the field back OWNED (it is
     inside the object's storage, and [kfree] memsets it, so a lock on a
     kalloc'd page cannot afford to have it discarded); a caller whose lock is
     static seals it here and forgets it.  A basic update, so this works in
     place inside a WP goal -- no [fupd_wp] needed. *)
  Lemma lock_name_intro (lk p : mword 64) (s : string) :
    ctx_string_all p DfracDiscarded s -∗
    lock_name_field lk ↦₈ p ==∗ lock_name lk s.
  Proof.
    iIntros "#Hs Hf".
    iDestruct (ctx_word_pointsto_forget with "Hf") as "Hf".
    iMod (word_pointsto_persist with "Hf") as "#Hfp".
    iModIntro. iExists p. by iFrame "Hfp Hs".
  Qed.

  (* >>> §0.35′(i): A LOCK HANDLE IS CONTEXT-RELATIVE.
     Still PERSISTENT, but ξ-indexed, and carrying INTERNALLY the fact that
     this context's bound has passed the lock's floor.  [lo] is existential,
     so it never appears in the exported type and NO MENTION SITE MOVES --
     measured (A6.96 §(2)), all 136 files that name [is_lock] already bind a
     [CurCtx], so the index is AMBIENT and the arity change is invisible.

     WHAT THE FLOOR BUYS is the premise four separate reads could not state
     (A6.89 §(7), A6.92 §(3), A6.95 §(3), §0.27′): a holder of the handle
     produces [view_lb … K ∗ ⌜lo ≤ K⌝] out of its own running token
     ([TsoCtx.own_context_floor_view]).  WHAT IT COSTS is that a handle can
     no longer be CONJURED: a core that merely discovers the address of a
     freshly kalloc'd pipe page has no floor for it and cannot acquire -- it
     must RECEIVE the handle through a real crossing (§0.16′), which is the
     ruling's own soundness argument. <<< *)
  Definition is_lock (γ : gname) (lk : mword 64) (s : string)
      (R : CtxId → iProp Σ) : iProp Σ :=
    (∃ lo : nat,
       lock_name lk s ∗ inv lockN (lock_inv γ lk s R lo) ∗
       lk_floor cur_ctx lo)%I.

  Global Instance is_lock_persistent γ lk s R :
    Persistent (is_lock γ lk s R).
  Proof. apply _. Qed.

  (* PERFORMANCE, and it is a big one: WITHOUT this seal, every [iIntros "#Hlk"]
     of an [is_lock] re-derives persistence by UNFOLDING the definition and
     descending through [lock_inv γ lk s R] into [R].  For a lock whose resource
     is large (the virtio disk lock's [disk_res], with its 4096-entry
     descriptor big-ops) that single [#]-intro measured **5.1 s** -- 22 % of
     [ProofEndOp]'s whole [typeclasses eauto] budget, at three sites.  With the
     constant sealed, resolution stops at [is_lock_persistent] above and the
     cost disappears (ProofEndOp 92.5 s -> 78 s from this line alone).
     Everything a consumer needs is lemma-driven ([is_lock_name] /
     [is_lock_inv] / [is_lock_intro] below), so nothing needs the unfolding. *)
  Global Typeclasses Opaque is_lock.


  (* the two projections + the introduction rule (the only interface the
     lock leaves and [newlock] need). *)
  (* these three are the ONLY places that may look inside [is_lock] -- the
     [Typeclasses Opaque] above means an [iDestruct]/[iFrame] elsewhere can no
     longer take it apart, which is the point: it must come through here. *)
  Lemma is_lock_name γ lk s R : is_lock γ lk s R -∗ lock_name lk s.
  Proof. rewrite /is_lock. iIntros "(% & $ & _)". Qed.
  (* the invariant projection EXHIBITS the floor: a leaf that opens the body
     needs the [lo] it was allocated at, and that same [lo] is what its read
     discharges against. *)
  Lemma is_lock_inv γ lk s R :
    is_lock γ lk s R -∗
    ∃ lo : nat, inv lockN (lock_inv γ lk s R lo) ∗ lk_floor cur_ctx lo.
  Proof.
    rewrite /is_lock. iIntros "(%lo & _ & #Hi & #Hf)".
    iExists lo. by iFrame "Hi Hf".
  Qed.
  Lemma is_lock_intro γ lk s R lo :
    lock_name lk s -∗ inv lockN (lock_inv γ lk s R lo) -∗
    lk_floor cur_ctx lo -∗ is_lock γ lk s R.
  Proof.
    rewrite /is_lock. iIntros "#Hn #Hi #Hf". iExists lo. by iFrame "Hn Hi Hf".
  Qed.

  (* ---- THE OPENING INTERFACE ------------------------------------------

     WpSconfLock.v is the only file in the tree that ever opens a lock, and
     all its leaves do the same three things: open [lock_inv], take one
     machine step, put it back.  [lock_openable] is that pattern named, with
     two parameters that decide WHOSE lock it is:

       T -- the OPENING CREDENTIAL.  Presented to open, handed straight back.
       D -- the DISPOSAL certificate.  Surrendering it destroys the invariant
            instead of closing it, and the opener keeps the contents.

     Two instances, and they are the whole point:

       inv lockN (lock_inv γ lk s R)              -- any T, D := False
            anyone may open, nobody may destroy: a static kernel lock, and
            exactly today's behaviour
       inv lockN (lock_inv γ lk s R ∨ D)          -- any T that REFUTES D
            the object may die: the invariant degenerates into a husk holding
            [D], and whoever can produce [D] puts it there and walks off with
            the memory.  [T] is whatever proves the object is not dead yet.

     A lock's storage is reclaimable exactly when the right to touch it is a
     resource rather than free knowledge -- which is the real xv6 rule for a
     kalloc'd object: you may take [pi->lock] only while you hold a reference
     to it, OR while you hold the lock.  Both are legitimate credentials, and
     BOTH are needed: the last holder to let go of a reference has already
     given it back by the time it calls release, and what licenses release's
     own three opens is the lock it is still holding.  That is why [T] is a
     parameter and not a fixed token -- see [lock_openable_holder].

     The mask is universally quantified so this file needs no [minstretN]; the
     leaves instantiate it at [⊤ ∖ ↑minstretN]. *)
  (* >>> §0.35′(i), AND THE ARITY DOES NOT MOVE (A6.97 §(2)).  The opener
     takes its context AMBIENT, exactly as [is_lock] does, and HANDS THE
     FLOOR OUT beside the body -- [lo] is the lock's, but it is existential
     at every consumer that does not discharge a read against it, and the
     two that do are being rewritten anyway.  Writing [lo] into the arity
     instead would have moved seventeen further green files for nothing. <<< *)
  Definition lock_openable (γ : gname) (lk : mword 64) (s : string)
      (R : CtxId → iProp Σ) (D : iProp Σ) : iProp Σ :=
    (* A6.109: THE FLOOR IS HOISTED OUT OF THE □∀, and it has to be.  With
       [∃ lo] inside the accessor, two opens of the SAME lock hand out two
       unrelated witnesses -- so a leaf that gives the owner cell to an
       atomic update and takes it back cannot close the invariant it opened
       ([lock_inv … lo] and [lock_inv … lo'] are different propositions).
       Outside, [lo] is fixed once per consumer, which is also what
       [is_lock] already does; the arity still does not move. *)
    (∃ lo : nat,
       lk_floor cur_ctx lo ∗
       □ ∀ (E : coPset) (T : iProp Σ),
           ⌜↑lockN ⊆ E⌝ -∗ (T -∗ D -∗ False) -∗ T ={E, E ∖ ↑lockN}=∗
           ▷ lock_inv γ lk s R lo ∗ T ∗
           ((▷ lock_inv γ lk s R lo ={E ∖ ↑lockN, E}=∗ True)   (* put it back *)
            ∧ (D ={E ∖ ↑lockN, E}=∗ True)))%I.               (* or destroy it *)

  (* >>> A6.112: THE OPENER WHOSE FLOOR IS ALREADY ABSORBED.

     [lock_openable] carries [lk_floor] -- the ratified disjunction (§0.38′),
     which is what makes a lock's CREATION provable.  A racy READ needs
     strictly more: [lkcpu_read_not_mine] wants the floor's visibility, and
     of [lk_floor]'s two arms only the LEFT one ([ctx_floor], against
     [own_context]) delivers it to a hart that did not write the floor.

     So the reads take this opener, whose floor conjunct is the left arm
     outright.  It is produced by the crossing upgrade (the AMO that carried
     the handle here), and free at [lo = 0] for every boot-static lock
     ([ctx_floor_0]).  [lock_openable_of_c] is the one-way weakening, so
     nothing that only OPENS a lock has to care which it holds. <<< *)
  (* A6.120: RETIRED IN PLACE -- no producer and no consumer.  The racy
     read cashes [lk_floor] on either arm now ([lk_floor_vis]), so the
     absorbed opener is never needed; kept because it is three lemmas and
     a grep landing here should read why. *)
  Definition lock_openable_c (γ : gname) (lk : mword 64) (s : string)
      (R : CtxId → iProp Σ) (D : iProp Σ) : iProp Σ :=
    (∃ lo : nat,
       TsoCtx.ctx_floor cur_ctx lo ∗
       □ ∀ (E : coPset) (T : iProp Σ),
           ⌜↑lockN ⊆ E⌝ -∗ (T -∗ D -∗ False) -∗ T ={E, E ∖ ↑lockN}=∗
           ▷ lock_inv γ lk s R lo ∗ T ∗
           ((▷ lock_inv γ lk s R lo ={E ∖ ↑lockN, E}=∗ True)
            ∧ (D ={E ∖ ↑lockN, E}=∗ True)))%I.

  Global Instance lock_openable_c_persistent γ lk s R D :
    Persistent (lock_openable_c γ lk s R D).
  Proof. apply _. Qed.

  Lemma lock_openable_of_c γ lk s R D :
    lock_openable_c γ lk s R D -∗ lock_openable γ lk s R D.
  Proof.
    iIntros "(%lo & #Hf & #Ho)". iExists lo. iFrame "Ho".
    by iApply lk_floor_of_ctx.
  Qed.

  Lemma lock_openable_c_parts γ lk s R D :
    lock_openable_c γ lk s R D -∗
    ∃ lo : nat,
      TsoCtx.ctx_floor cur_ctx lo ∗
      □ ∀ (E : coPset) (T : iProp Σ),
          ⌜↑lockN ⊆ E⌝ -∗ (T -∗ D -∗ False) -∗ T ={E, E ∖ ↑lockN}=∗
          ▷ lock_inv γ lk s R lo ∗ T ∗
          ((▷ lock_inv γ lk s R lo ={E ∖ ↑lockN, E}=∗ True)
           ∧ (D ={E ∖ ↑lockN, E}=∗ True)).
  Proof. by iIntros "$". Qed.

  (* the boot-static producer: floor 0 is free, so every lock whose owner
     cell is an era-image cell has this opener for nothing (A6.101). *)
  Lemma lock_openable_c_inv_0 γ lk s R :
    inv lockN (lock_inv γ lk s R 0) -∗ lock_openable_c γ lk s R False.
  Proof.
    iIntros "#Hi". iExists 0%nat. iSplitR; [ iApply TsoCtx.ctx_floor_0 | ].
    iIntros "!>" (E T HE) "_ HT".
    iMod (inv_acc E lockN with "Hi") as "[Hbody Hclose]"; [done|].
    iModIntro. iFrame "Hbody HT".
    iSplit; [iExact "Hclose" | iIntros "%Hf0"; destruct Hf0].
  Qed.

  (* A6.109: the projection every leaf uses -- [iDestruct (… with "Hlock")]
     leaves the intuitionistic handle in place, so a proof that both FORWARDS
     the opener and opens it itself keeps one name for each. *)
  Lemma lock_openable_parts γ lk s R D :
    lock_openable γ lk s R D -∗
    ∃ lo : nat,
      lk_floor cur_ctx lo ∗
      □ ∀ (E : coPset) (T : iProp Σ),
          ⌜↑lockN ⊆ E⌝ -∗ (T -∗ D -∗ False) -∗ T ={E, E ∖ ↑lockN}=∗
          ▷ lock_inv γ lk s R lo ∗ T ∗
          ((▷ lock_inv γ lk s R lo ={E ∖ ↑lockN, E}=∗ True)
           ∧ (D ={E ∖ ↑lockN, E}=∗ True)).
  Proof. by iIntros "$". Qed.

  Global Instance lock_openable_persistent γ lk s R D :
    Persistent (lock_openable γ lk s R D).
  Proof. apply _. Qed.

  (* a permanent [inv]: nothing has to be refuted, and no disposal is
     possible. *)
  Lemma lock_openable_inv γ lk s R lo :
    inv lockN (lock_inv γ lk s R lo) -∗ lk_floor cur_ctx lo -∗
    lock_openable γ lk s R False.
  Proof.
    iIntros "#Hi #Hf". iExists lo. iFrame "Hf". iIntros "!>" (E T HE) "_ HT".
    iMod (inv_acc E lockN with "Hi") as "[Hbody Hclose]"; [done|].
    iModIntro. iFrame "Hbody HT".
    iSplit; [iExact "Hclose" | iIntros "%Hf0"; destruct Hf0].
  Qed.

  (* the bridge every existing lock user rides: today's lock IS the permanent
     instance of the generic one. *)
  Lemma is_lock_openable γ lk s R :
    is_lock γ lk s R ⊢ lock_openable γ lk s R False.
  Proof.
    iIntros "H". iDestruct (is_lock_inv with "H") as (lo) "[#Hi #Hf]".
    iApply (lock_openable_inv with "Hi Hf").
  Qed.

  (* the refutation obligation is vacuous for a lock that cannot die. *)
  Lemma lock_refute_False (T : iProp Σ) : ⊢ T -∗ False -∗ False.
  Proof. iIntros "_ []". Qed.

  (* ---- the CANCELLABLE flavour ----------------------------------------

     One invariant with a dead branch, and any credential that refutes it.
     This is what a [cinv] would be if its accessor did not insist on a share
     of the very token that has to be WHOLE in order to cancel -- and that
     insistence is exactly what a multiply-owned object cannot satisfy: the
     last holder to let go of a reference has already given it back by the
     time it calls release, and what licenses release's own opens is the LOCK
     it is still holding, a different resource entirely.  Quantifying [T]
     inside the accessor is what lets the two coexist.

     [D] must be timeless: the dead branch is refuted UNDER a later, and there
     is no step to take there. *)
  Lemma lock_openable_of_dead γ lk s R D lo `{!Timeless D} :
    inv lockN (lock_inv γ lk s R lo ∨ D) -∗ lk_floor cur_ctx lo -∗
    lock_openable γ lk s R D.
  Proof.
    iIntros "#Hi #Hf". iExists lo. iFrame "Hf". iIntros "!>" (E T HE) "Hrefute HT".
    iMod (inv_acc E lockN with "Hi") as "[Hbody Hclose]"; [done|].
    rewrite bi.later_or. iDestruct "Hbody" as "[Hlive | >Hdead]".
    2:{ iExFalso. iApply ("Hrefute" with "HT Hdead"). }
    iModIntro. iFrame "Hlive HT".
    iSplit.
    - iIntros "Hb". iApply "Hclose". by iLeft.
    - iIntros "Hd". iApply "Hclose". iRight. by iApply bi.later_intro.
  Qed.

  (* ---- THE FINISHING INTERFACE ---------------------------------------

     The other half: what the CALLER of release's word clear supplies to
     decide the invariant's fate.  At that instant the store has happened and
     the state ghost is back at [None], so the two zeroed words, the ghost
     state and [R] are all in hand at once -- which is why the choice has to
     be made HERE and not one instruction later.  The finisher is handed the
     close-or-destroy choice at mask [E] and the contents in PIECES, and
     produces the leaf's output resource [Out].

     Pieces, not a reassembled [lock_inv]: a destroying caller needs the ghost
     state (that is what it turns into a certificate) and a closing one can
     rebuild the body from them.  The two canonical instances are below. *)
  (* §0.35′(i) / A6.97 §(2): the floor is ∀-QUANTIFIED INSIDE the wand, not
     added to the arity -- the finisher is handed whichever [lo] the leaf's
     open produced, and no consumer of [lock_finisher] names it. *)
  (* >>> A6.120: THE FINISHER IS TWO-PART -- a PRELUDE at release's entry
     and a BODY at the store -- because its two arms want the payload in two
     different shapes and only the entry has the running token:
       close   : the invariant's free arm is the parked record [lock_pay R],
                 so the payload must be DEPOSITED ([lock_pay_intro]), which
                 spends [own_context] -- borrowable from [sie_cap] at entry
                 (SieCapCtx) and NOT at the store, where the step engine
                 holds it inside its atomic update
                 ([WpSconfMem.wp_store_s_sconf_au_dat]'s obligation);
       destroy : the caller's completion wand speaks at [cur_ctx], and the
                 word clear is a plain [sw] after a fence -- no AMO, so no
                 log-top evidence could bring a record parked at entry back
                 (the retired SC shim [ctx_dom_sc] used to conjure exactly
                 that morph, at ProofRelease's cancel path).  The honest
                 form never parks it.
     So the finisher CHOOSES the shape [Pay]: the prelude turns [R cur_ctx]
     into it with the token in hand, the body consumes it at the store.
     [lock_finisher_body] is what the word-clear leaf takes; nothing outside
     this file looks inside [lock_finisher]. <<< *)
  Definition lock_finisher_body (γ : gname) (lk : mword 64) (s : string)
      (R : CtxId → iProp Σ) (D Out : iProp Σ)
      (E : coPset) (Pay : iProp Σ) : iProp Σ :=
    ( ∀ lo : nat,
      ((▷ lock_inv γ lk s R lo ={E ∖ ↑lockN, E}=∗ True)
       ∧ (D ={E ∖ ↑lockN, E}=∗ True)) -∗
      lock_auth γ None -∗ lock_frag γ None -∗
      (* A6.89: the LEDGER word plus its claim, not the ctx word.  See
         [lock_word_fresh]: release cannot hand back a ctx cell. *)
      lock_word_fresh lk -∗
      lk_cpu_fresh lo lk -∗
      (* the lock's floor, off the opener the leaf holds: a destroying
         finisher hands the owner cell back BUNDLED ([lk_cpu_ready], A6.105's
         shape) and needs it; a closing one ignores it. *)
      lk_floor cur_ctx lo -∗
      Pay -∗
      |={E ∖ ↑lockN, E}=> Out)%I.

  Definition lock_finisher `{CID : CpuId} (γ : gname) (lk : mword 64)
      (s : string) (R : CtxId → iProp Σ) (D Out : iProp Σ)
      (E : coPset) : iProp Σ :=
    (∃ Pay : iProp Σ,
       (own_context cur_ctx -∗ R cur_ctx ==∗ own_context cur_ctx ∗ Pay) ∗
       lock_finisher_body γ lk s R D Out E Pay)%I.

  (* put it back: today's release, and equally the release of an object that
     merely still has other holders -- [D] is not used, only not taken.
     The prelude is the deposit (A6.119 / §0.18′: the free arm is the parked
     record, minted honestly by [ctx_deposit]). *)
  Lemma lock_finisher_close `{CID : CpuId} γ lk s R `{!CtxMorph R} D E :
    ⊢ lock_finisher γ lk s R D emp E.
  Proof.
    iExists (lock_pay R). iSplitR.
    { iIntros "Hrun HR". iApply (lock_pay_intro with "Hrun HR"). }
    iIntros (lo) "[Hclose _] Hauth Hfrag [#Hc4 Hword] [#Hc8 Hcpu] _ HR".
    iDestruct "Hauth" as (B) "Hauth".
    iMod ("Hclose" with "[Hauth Hfrag Hword Hcpu HR]") as "_"; [| by iModIntro].
    iNext. rewrite /lock_inv /lock_body. iFrame "Hc4 Hc8".
    iExists (mword_of_int 0 : mword 32), None, B.
    rewrite lk_cpu_res_free. iFrame "Hword Hcpu Hauth".
    iLeft. by iFrame "Hfrag HR".
  Qed.
  (* destroy it and keep the storage.  The certificate [D] is assembled HERE,
     out of the ghost state the lock just gave up plus whatever the caller
     finds in [R] -- not brought along ready-made.  That generality is what a
     multiply-owned object needs: the last holder to let go has necessarily
     already surrendered its share of the certificate into [R], and [R] is
     only in hand at this instant (see PipeInv.pipe_res_dead).
     The prelude is the identity: the destroyer's payload stays at its own
     context, which is the context its completion wand speaks at. *)
  (* the destroy arm's [Out] cannot mention [lo] (it is chosen by the caller,
     before the open), so the owner cell leaves in A6.105's BUNDLED form
     [lk_cpu_ready] -- existentially floored, with the floor certificate
     beside it, which is what [SpecRelease]'s cancel post hands back and
     what [PipeInv.pipe_bytes_page_own] consumes. *)
  Lemma lock_finisher_destroy `{CID : CpuId} γ lk s R D Out E :
    (lock_frag γ None -∗ R cur_ctx ==∗ D ∗ Out) -∗
    lock_finisher γ lk s R D (lock_word_fresh lk ∗ lk_cpu_ready lk ∗ Out) E.
  Proof.
    iIntros "Hcomplete". iExists (R cur_ctx). iSplitR "Hcomplete".
    { iIntros "Hrun HR". iModIntro. iFrame "Hrun HR". }
    iIntros (lo) "[_ Hdispose] Hauth Hfrag Hword Hcpu #Hfl HR".
    iMod ("Hcomplete" with "Hfrag HR") as "[HD HOut]".
    iMod ("Hdispose" with "HD") as "_".
    iModIntro. iFrame "Hword HOut".
    rewrite /lk_cpu_ready /lk_cpu_ready_at. iExists lo.
    iSplitL "Hcpu"; [ iExact "Hcpu" | iExact "Hfl" ].
  Qed.
  (* [mem_pointsto]'s and [word4_pointsto]'s [Timeless] instances now live in
     RiscvPtsto.v, beside the definitions. *)
  Global Instance lock_word_timeless lk v : Timeless (lock_word lk v).
  Proof. rewrite /lock_word. apply _. Qed.

  (* ---- lock construction (the "newlock" ghost step) ------------------ *)


  (* THE lock body, built: a free physical lock (word 0, cpu word 0) plus the
     resource it protects.  Whether that body then goes into a permanent [inv]
     or a cancellable [cinv] is the caller's business -- this is the piece both
     constructions share, and a basic update, so it can be done before the
     invariant's namespace or gname exists (which is what an object whose
     resource mentions its OWN cancel gname needs; see [newlock_c_delayed]). *)
  (* A6.66: the free arm is now the parked record, so the creator DEPOSITS
     (honestly -- see [lock_pay_intro]) instead of wrapping the payload in a
     bare existential.  The token is taken and handed straight back. *)
  Lemma lock_inv_alloc `{CID : CpuId} (lo : nat) (lk : mword 64) (s : string)
      (R : CtxId → iProp Σ) `{!CtxMorph R} :
    own_context cur_ctx -∗
    lk ↦₄ (mword_of_int 0 : mword 32) -∗
    lk_cpu_fresh lo lk -∗
    R cur_ctx ==∗ own_context cur_ctx ∗ ∃ γ : gname, lock_inv γ lk s R lo.
  Proof.
    iIntros "Hrun Hword [#Hc8 Hcpu] HR".
    iDestruct (lk_addr_claim_of4 with "Hword") as "#Hc4".
    iMod (lock_pay_intro R with "Hrun HR") as "[Hrun HR]".
    iFrame "Hrun".
    iMod (own_alloc ((((●E (None : leibnizO lock_state)),
                       (●E (0%nat : leibnizO nat)))
                      ⋅ ((◯E (None : leibnizO lock_state)),
                         (◯E (0%nat : leibnizO nat)))) : lockUR)) as (γ) "H";
      [ split; apply excl_auth_valid | ].
    iDestruct (own_op with "H") as "[Ha Hf]".
    iModIntro. iExists γ. rewrite /lock_inv /lock_body. iFrame "Hc4 Hc8".
    iExists (mword_of_int 0 : mword 32), None, 0%nat.
    iDestruct (lock_word_intro with "Hword") as "Hword".
    rewrite lk_cpu_res_free. iFrame "Hword Hcpu Ha".
    iLeft. iSplitR; [done|]. iSplitR; [done|].
      iSplitL "Hf"; [ by iExists 0%nat | iExact "HR" ].
  Qed.

  (* a FREE physical lock plus its resource become a lock that can DIE: the
     body carries the dead branch from the start, and the ghost name of the
     lock state is chosen FIRST, so [R] and [D] may both mention it -- which
     they do for any object whose dead state parks the lock's own state
     fragment (PipeInv.pipe_dead). *)
  Lemma newlock_d `{CID : CpuId} E (lo : nat) (lk : mword 64) (s : string) :
    lk ↦₄ (mword_of_int 0 : mword 32) -∗
    lk_cpu_fresh lo lk ==∗
    ∃ γ : gname, ∀ (R : CtxId → iProp Σ) (D : iProp Σ),
      ⌜CtxMorph R⌝ -∗ own_context cur_ctx -∗
      R cur_ctx ={E}=∗ own_context cur_ctx ∗ inv lockN (lock_inv γ lk s R lo ∨ D).
  Proof.
    iIntros "Hword [#Hc8 Hcpu]".
    iDestruct (lk_addr_claim_of4 with "Hword") as "#Hc4".
    iMod (own_alloc ((((●E (None : leibnizO lock_state)),
                       (●E (0%nat : leibnizO nat)))
                      ⋅ ((◯E (None : leibnizO lock_state)),
                         (◯E (0%nat : leibnizO nat)))) : lockUR)) as (γ) "H";
      [ split; apply excl_auth_valid | ].
    iDestruct (own_op with "H") as "[Ha Hf]".
    iModIntro. iExists γ. iIntros (R D) "%HmR Hrun HR".
    iMod (lock_pay_intro (CtxMorph0 := HmR) R with "Hrun HR") as "[Hrun HR]".
    iFrame "Hrun".
    iApply (inv_alloc lockN E (lock_inv γ lk s R lo ∨ D)).
    iNext. iLeft. rewrite /lock_inv /lock_body. iFrame "Hc4 Hc8". iExists (mword_of_int 0 : mword 32), None, 0%nat.
    iDestruct (lock_word_intro with "Hword") as "Hword".
    rewrite lk_cpu_res_free. iFrame "Hword Hcpu Ha".
    iLeft. iSplitR; [done|]. iSplitR; [done|].
      iSplitL "Hf"; [ by iExists 0%nat | iExact "HR" ].
  Qed.

  (* a FREE physical lock plus the resource it protects and its name become a
     (permanent) lock. *)
  (* §0.35′(i)/(iii): a creator that hands back a HANDLE owes the floor, and
     it buys it with a receipt like everyone else ([TsoCtx.ctx_bound_raise] at
     the caller's next acquire).  A creator that hands back the bare INVARIANT
     ([lock_inv_alloc], [newlock_d]) owes nothing: the floor is a property of
     the handle, not of the lock. *)
  Lemma newlock `{CID : CpuId} E (lk : mword 64) (s : string)
      (R : CtxId → iProp Σ) `{!CtxMorph R} :
    lock_name lk s -∗
    own_context cur_ctx -∗
    lk ↦₄ (mword_of_int 0 : mword 32) -∗
    lk_cpu_ready lk -∗
    R cur_ctx ={E}=∗ own_context cur_ctx ∗ ∃ γ : gname, is_lock γ lk s R.
  Proof.
    iIntros "#Hnm Hrun Hword Hready HR".
    rewrite /lk_cpu_ready /lk_cpu_ready_at.
    iDestruct "Hready" as (lo) "[Hcpu #Hfl]".
    iMod (lock_inv_alloc lo lk s R with "Hrun Hword Hcpu HR") as "[Hrun Hbody]".
    iDestruct "Hbody" as (γ) "Hbody".
    iFrame "Hrun".
    iMod (inv_alloc lockN E (lock_inv γ lk s R lo) with "[Hbody]") as "#Hinv";
      [ by iNext | ].
    iModIntro. iExists γ.
    iApply (is_lock_intro with "Hnm Hinv Hfl").
  Qed.

  (* [newlock] with the two halves SEPARATED: the ghost name is chosen first
     and the resource is supplied afterwards, so [R] may mention the name -- or,
     which is what forced this lemma, the whole LIST of names an ARRAY of locks
     is being built with.  [SchedCtx.proc_lock_res] is indexed by the [γs] of
     all NPROC proc locks (through [p_sched]), so allocating the 64 locks with
     [newlock] is circular and [SpecProcinit.procs_inv_alloc] runs this instead:
     one pass to pick the 64 names, then one pass to pay each lock its
     resource.  [newlock_d] is the same trick for a lock whose resource
     mentions its own cancel gname; the difference is that this one lands on a
     plain [is_lock] rather than the [∨ D] body. *)
  Lemma newlock_delayed `{CID : CpuId} E (lk : mword 64) (s : string) :
    lock_name lk s -∗
    lk ↦₄ (mword_of_int 0 : mword 32) -∗
    lk_cpu_ready lk ==∗
    ∃ γ : gname, ∀ R : CtxId → iProp Σ,
      ⌜CtxMorph R⌝ -∗ own_context cur_ctx -∗
      R cur_ctx ={E}=∗ own_context cur_ctx ∗ is_lock γ lk s R.
  Proof.
    iIntros "#Hnm Hword Hready".
    rewrite /lk_cpu_ready /lk_cpu_ready_at.
    iDestruct "Hready" as (lo) "[[#Hc8 Hcpu] #Hfl]".
    iDestruct (lk_addr_claim_of4 with "Hword") as "#Hc4".
    iMod (own_alloc ((((●E (None : leibnizO lock_state)),
                       (●E (0%nat : leibnizO nat)))
                      ⋅ ((◯E (None : leibnizO lock_state)),
                         (◯E (0%nat : leibnizO nat)))) : lockUR)) as (γ) "H";
      [ split; apply excl_auth_valid | ].
    iDestruct (own_op with "H") as "[Ha Hf]".
    iModIntro. iExists γ. iIntros (R) "%HmR Hrun HR".
    iMod (lock_pay_intro (CtxMorph0 := HmR) R with "Hrun HR") as "[Hrun HR]".
    iFrame "Hrun".
    iMod (inv_alloc lockN E (lock_inv γ lk s R lo) with "[Hword Hcpu Ha Hf HR]") as "#Hinv".
    { iNext. rewrite /lock_inv /lock_body. iFrame "Hc4 Hc8". iExists (mword_of_int 0 : mword 32), None, 0%nat.
      iDestruct (lock_word_intro with "Hword") as "Hword".
    rewrite lk_cpu_res_free. iFrame "Hword Hcpu Ha".
      iLeft. iSplitR; [done|]. iSplitR; [done|].
      iSplitL "Hf"; [ by iExists 0%nat | iExact "HR" ]. }
    iModIntro. iApply (is_lock_intro with "Hnm Hinv Hfl").
  Qed.

  (* BOX v2 boot (endgame §3.6): the creator cannot floor its own deposit,
     so the lock is minted WITH the fold -- [lock_pay_intro_llb] in place
     of [lock_pay_intro]: the payload row [Rdep] at [cur_ctx] plus [llb tl]
     and the one-line entailment give the floored [R]. *)
  Lemma newlock_delayed_llb `{CID : CpuId} E (lk : mword 64) (s : string) :
    lock_name lk s -∗
    lk ↦₄ (mword_of_int 0 : mword 32) -∗
    lk_cpu_ready lk ==∗
    ∃ γ : gname, ∀ (R Rdep : CtxId → iProp Σ) (tl : nat),
      ⌜CtxMorph Rdep⌝ -∗
      ⌜forall ξ : CtxId, Rdep ξ ∗ TsoCtx.ctx_floor ξ tl ⊢ R ξ⌝ -∗
      TsoGhost.llb loglen_name tl -∗ own_context cur_ctx -∗
      Rdep cur_ctx ={E}=∗ own_context cur_ctx ∗ is_lock γ lk s R.
  Proof.
    iIntros "#Hnm Hword Hready".
    rewrite /lk_cpu_ready /lk_cpu_ready_at.
    iDestruct "Hready" as (lo) "[[#Hc8 Hcpu] #Hfl]".
    iDestruct (lk_addr_claim_of4 with "Hword") as "#Hc4".
    iMod (own_alloc ((((●E (None : leibnizO lock_state)),
                       (●E (0%nat : leibnizO nat)))
                      ⋅ ((◯E (None : leibnizO lock_state)),
                         (◯E (0%nat : leibnizO nat)))) : lockUR)) as (γ) "H";
      [ split; apply excl_auth_valid | ].
    iDestruct (own_op with "H") as "[Ha Hf]".
    iModIntro. iExists γ. iIntros (R Rdep tl) "%HmR %Hfold #Hllb Hrun HR".
    iMod (lock_pay_intro_llb (CtxMorph0 := HmR) Rdep R tl Hfold with "Hllb Hrun HR") as "[Hrun HR]".
    iFrame "Hrun".
    iMod (inv_alloc lockN E (lock_inv γ lk s R lo) with "[Hword Hcpu Ha Hf HR]") as "#Hinv".
    { iNext. rewrite /lock_inv /lock_body. iFrame "Hc4 Hc8". iExists (mword_of_int 0 : mword 32), None, 0%nat.
      iDestruct (lock_word_intro with "Hword") as "Hword".
    rewrite lk_cpu_res_free. iFrame "Hword Hcpu Ha".
      iLeft. iSplitR; [done|]. iSplitR; [done|].
      iSplitL "Hf"; [ by iExists 0%nat | iExact "HR" ]. }
    iModIntro. iApply (is_lock_intro with "Hnm Hinv Hfl").
  Qed.

End Lock.

(* ---------------------------------------------------------------------- *)
(* THE LOCK HANDLE AT ANOTHER CONTEXT, ONCE (the environment-row sweep,     *)
(* 2026-09-02).  A handle is [lock_name] (context-free) plus an [inv]       *)
(* (context-free) plus the FLOOR, and the floor is exactly what             *)
(* [lk_floor_morph] above transports -- so a handle crosses with no absorb  *)
(* capability and, since the M3 λ-conversion, WITHOUT its payload having to *)
(* move.  Three files had restated this locally ([ConsoleInv]'s copy stays, *)
(* it is [Local] and older); [SchedCtx.is_lock_morph] is the same law       *)
(* stated again for the scheduler's cone.                                   *)
(*                                                                          *)
(* BELOW THE SECTION, because it has to spell [is_lock (XI := ξ)]: inside   *)
(* [Section Lock] the ambient [XI] is a section variable and the constant   *)
(* has no argument to name yet.  (That is also why it is not literally      *)
(* beside [lk_floor_morph].)                                                *)
(* ---------------------------------------------------------------------- *)
Global Instance is_lock_handle_morph `{!riscvGS Σ, !lockG Σ}
    (γ : gname) (lk : mword 64) (s : string) (R : TsoCtx.CtxId → iProp Σ) :
  TsoCtx.CtxMorph (λ ξ : TsoCtx.CtxId, is_lock (XI := ξ) γ lk s R).
Proof.
  iIntros (ξ ξ') "Hd H". rewrite /is_lock.
  iDestruct "H" as (lo) "(#Hn & #Hi & Hf)".
  iMod (lk_floor_morph lo ξ ξ' with "Hd Hf") as "[Hd #Hf']".
  iModIntro. iFrame "Hd". iExists lo. by iFrame "Hn Hi Hf'".
Qed.
