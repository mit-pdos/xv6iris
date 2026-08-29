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
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import excl gmap auth ufrac.
From iris.algebra.lib Require Import excl_auth.
From iris.base_logic.lib Require Import invariants cancelable_invariants own.
Require Import SailStdpp.Base SailStdpp.Operators_mwords.
Require Import Riscv.rv64d.
Require Import RiscvPtsto RiscvLang.
(* EXPORTED: [lock_cpu] (the +16 owner-field address) lives there, because the
   per-cpu held-lock set is stated over it, and the ~40 files that reach
   [lock_cpu] through this one keep working. *)
Require Export LockSet.
Require Import ProcGeom.
Require Export Xv6Cameras.  (* the cameras this file states its theory over *)
(* SLICE 2 chunk 2: the lock kit's context laws, landed ADDITIVELY (§6(e) --
   laws first at a standalone green boundary, consumers after).  RiscvPtsto is
   re-imported after TsoCtx so this file's own notations stay raw until the M1
   flip. *)
Require Import TsoCtx TsoCtxShim.
Local Open Scope Z_scope.


Section Lock.
  Context `{!riscvGS Σ, !lockG Σ}.
  (* §0.35': the lock handle is CONTEXT-RELATIVE, so the context is ambient
     here exactly as on the T-leg (tso-flip WpLock.v:73).  §6(d)'s corollary:
     a fact ambient at every site belongs in a typeclass, not an argument --
     which is why [is_lock]'s ARITY does not move even though its meaning is
     now indexed.  Only the declarations that actually mention [cur_ctx]
     generalize over it. *)
  Context `{XI : TsoCtx.CurCtx}.

  (* sibling of [minstretN]; the two are disjoint by construction, so a leaf
     can open [is_lock] INSIDE the step engine's [⊤ ∖ ↑minstretN] callback. *)
  Definition lockN : namespace := nroot .@ "xv6spinlock".

  (* ---- the ghost pieces ---------------------------------------------- *)

  (* the authority on the lock's state; lives in the invariant. *)
  (* A6.119 (tso-flip WpLock.v:85): the position-exposing forms.  [lock_auth_at]
     is what the invariant holds beside the word; [lock_frag_at] is what the
     holder token carries.  The agreement between them is the whole point. *)
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
  (* THE AGREEMENT: the position the invariant minted at the AMO is the
     position the holder was handed. *)
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
  (* §0.34′ on its sound axis (A6.119, tso-flip WpLock.v:147): the token
     carries the ACQUIRE POSITION's floor -- a ξ-indexed conjunct is licensed
     where a hart-indexed one is not ([cur_ctx] does not rebind at [wp_next];
     [CpuId] does).  Arity unchanged and ξ ambient, so no consumer moves. *)
  Definition locked (γ : gname) (i : CPU) : iProp Σ :=
    (∃ B : nat, lock_frag_at γ (Some (i, true)) B ∗
       TsoCtx.ctx_floor TsoCtx.cur_ctx B)%I.
  (* the same, in the window where [lk->cpu] is still 0 (internal to the
     acquire / release proofs; no caller ever sees it). *)
  Definition locked_pre (γ : gname) (i : CPU) : iProp Σ :=
    (∃ B : nat, lock_frag_at γ (Some (i, false)) B ∗
       TsoCtx.ctx_floor TsoCtx.cur_ctx B)%I.
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
  (* the free fragment as an exclusive token of its own -- what a cancelled
     lock's [D] certificate is made of ([PipeInvDefs.pipe_dead]). *)
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
  (* THE holder laws: the token pins the owner word to your own [struct cpu],
     and its floor is at the invariant's position. *)
  Lemma locked_state_at γ st B i :
    lock_auth_at γ st B -∗ locked γ i -∗
    ⌜st = Some (i, true)⌝ ∗ TsoCtx.ctx_floor TsoCtx.cur_ctx B.
  Proof.
    iIntros "Ha (%B' & Hf & #Hfl)".
    iDestruct (lock_pos_agree with "Ha Hf") as %[-> ->].
    iSplitR; [done|]. iExact "Hfl".
  Qed.
  Lemma locked_pre_state_at γ st B i :
    lock_auth_at γ st B -∗ locked_pre γ i -∗
    ⌜st = Some (i, false)⌝ ∗ TsoCtx.ctx_floor TsoCtx.cur_ctx B.
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
  (* ---- the four state transitions (one per lock instruction) --------- *)
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
  (* the winning AMO: the invariant's position moves to [B], the acquirer's
     floor at it, and the holder token is born carrying that floor. *)
  Lemma lock_take γ i (B : nat) :
    TsoCtx.ctx_floor TsoCtx.cur_ctx B -∗
    lock_auth γ None -∗ lock_frag γ None ==∗
    lock_auth_at γ (Some (i, false)) B ∗ locked_pre γ i.
  Proof.
    iIntros "#Hfl (%B0 & Ha) (%B1 & Hf)".
    iDestruct (lock_pos_agree with "Ha Hf") as %[_ ->].
    iMod (lock_state_update_at γ None (Some (i, false)) B1 B with "Ha Hf")
      as "[Ha Hf]".
    iModIntro. iFrame "Ha". iExists B. iFrame "Hf Hfl".
  Qed.
  Lemma lock_setcpu γ st B i :
    lock_auth_at γ st B -∗ locked_pre γ i ==∗
    ⌜st = Some (i, false)⌝ ∗ lock_auth_at γ (Some (i, true)) B ∗ locked γ i.
  Proof.
    iIntros "Ha (%B' & Hf & #Hfl)".
    iDestruct (lock_pos_agree with "Ha Hf") as %[-> ->].
    iMod (lock_state_update_at γ (Some (i, false)) (Some (i, true)) B' B' with "Ha Hf") as "[Ha Hf]".
    iModIntro. iSplitR; [done|]. iFrame "Ha". iExists B'. iFrame "Hf Hfl".
  Qed.
  Lemma lock_clrcpu γ st B i :
    lock_auth_at γ st B -∗ locked γ i ==∗
    ⌜st = Some (i, true)⌝ ∗ lock_auth_at γ (Some (i, false)) B ∗ locked_pre γ i.
  Proof.
    iIntros "Ha (%B' & Hf & #Hfl)".
    iDestruct (lock_pos_agree with "Ha Hf") as %[-> ->].
    iMod (lock_state_update_at γ (Some (i, true)) (Some (i, false)) B' B' with "Ha Hf") as "[Ha Hf]".
    iModIntro. iSplitR; [done|]. iFrame "Ha". iExists B'. iFrame "Hf Hfl".
  Qed.
  (* the word clear: the token's floor is dropped with it -- the pin it
     floored has just been retracted. *)
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
  Definition lock_word (lk : mword 64) (v : mword 32) : iProp Σ :=
    (lk ↦₄ v)%I.

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

  Definition lk_cpu_res (st : lock_state) (lk : mword 64) (r : string) : iProp Σ :=
    (lock_cpu lk ↦₈ lk_cpu_val st ∗ lk_cpu_frag st r)%I.

  (* the leaves strip this under [>] inside the step engine's callback, and
     [st] is a VARIABLE there, so the match is stuck and the structural
     instances cannot see the two branches.  Stated once, here. *)
  Global Instance lk_cpu_frag_timeless st r : Timeless (lk_cpu_frag st r).
  Proof. destruct st as [[i []]|]; apply _. Qed.
  Global Instance lk_cpu_res_timeless st lk r : Timeless (lk_cpu_res st lk r).
  Proof. apply _. Qed.

  (* the free / window form: the whole cell at 0 and no fragment. *)
  Lemma lk_cpu_res_free (lk : mword 64) (r : string) :
    lk_cpu_res None lk r ⊣⊢ lock_cpu lk ↦₈ (zero_reg : mword 64).
  Proof. rewrite /lk_cpu_res /=. apply bi.sep_emp. Qed.
  Lemma lk_cpu_res_win (i : CPU) (lk : mword 64) (r : string) :
    lk_cpu_res (Some (i, false)) lk r ⊣⊢ lock_cpu lk ↦₈ (zero_reg : mword 64).
  Proof. rewrite /lk_cpu_res /=. apply bi.sep_emp. Qed.
  Lemma lk_cpu_res_held (i : CPU) (lk : mword 64) (r : string) :
    lk_cpu_res (Some (i, true)) lk r ⊣⊢
    lock_cpu lk ↦₈ cpus_ptr i ∗ lk_in i r.
  Proof. reflexivity. Qed.

  (* [s] -- the lock's NAME -- rather than a bare rank: [is_lock] already
     carries it, so instantiating with [lock_rank s] leaves no second degree
     of freedom that could disagree with the name in [lock_name]. *)
  (* ================================================================== *)
  (* SLICE 2 CHUNK 2 -- THE CONTEXT LAWS OF THE LOCK KIT.               *)
  (*                                                                    *)
  (* Additive: nothing above this point changed.  These are the objects  *)
  (* chunk 3 converts [lock_inv] / [is_lock] / acquire / release ONTO.    *)
  (*                                                                    *)
  (* EVERY STATEMENT HERE IS TAKEN FROM THE PROTOTYPE BRANCHES, NOT      *)
  (* DERIVED HERE.  The lock payload was engineered over days on `tso`   *)
  (* and `tso-flip` and it is subtle; this file copies, it does not      *)
  (* improve.  Provenance is recorded per definition.  If something      *)
  (* below looks like it wants a parameter or a companion law, the       *)
  (* answer is on those branches or it does not exist -- see the two     *)
  (* NEGATIVE RESULTS recorded at [lock_pay]. *)
  (* ================================================================== *)

  (* ------------------------------------------------------------------ *)
  (* §0.38': THE HANDLE'S FLOOR, TWO-ARMED.   [tso-flip WpLock.v:869]    *)
  (*                                                                    *)
  (* "You RECEIVED this handle, or you WROTE this lock."  The left arm is *)
  (* what every channel crossing delivers; the right arm's only resting   *)
  (* holder is the creator's own thread before its first AMO, whose reads *)
  (* are covered by store forwarding.  [ctx_pointsto]'s clean-vs-own-write*)
  (* disjunction surfacing one tier up, and what makes the creator        *)
  (* bootstrap STRUCTURAL rather than a second distribution (A6.100): two *)
  (* FLOOR SOURCES, not two channels.                                     *)
  (*                                                                    *)
  (* NOT ON THE M-LEG AT ALL -- `tso`'s [is_lock] is pre-§0.38' and has   *)
  (* no floor.  This is one of the corrected shapes §5.1(b) exists to     *)
  (* make main land directly.                                            *)
  (*                                                                    *)
  (* The T-leg's right arm is [TsoGhost.llb loglen_name lo], which is     *)
  (* BELOW the seal.  [TsoCtx.log_lb] is its above-seal name (§2's test:  *)
  (* the statement has an SC proof with a trivial body).  The name is     *)
  (* this tree's; the ARM is the ruling's. *)
  (* A6.120/A6.123 (tso-flip WpLock.v:1077): the right arm is the context's
     OWN DIRTY-WRITE WITNESS, not an install-receipt position.  §0.38′ reads
     the handle as "you received this handle, or you wrote this lock"; the
     receipt spelling ([log_lb lo]) said the floor was a log position and
     nothing about who wrote it, could not be cashed at a read, and did not
     transport (A6.113/A6.120).  The witness is ξ-indexed, hart-free, cashed
     against the running token in both arms ([lk_floor_vis]) and travels as
     the receiver's LEFT arm across a crossing ([lk_floor_morph]). *)
  Definition lk_floor (ξ : TsoCtx.CtxId) (lo : nat) : iProp Σ :=
    (TsoCtx.ctx_floor ξ lo ∨ ∃ a, TsoCtx.ctx_wrote ξ lo a)%I.
  Global Instance lk_floor_persistent ξ lo : Persistent (lk_floor ξ lo).
  Proof. apply _. Qed.
  Lemma lk_floor_0 ξ : ⊢ lk_floor ξ 0.
  Proof. iLeft. iApply TsoCtx.ctx_floor_0. Qed.
  Lemma lk_floor_of_ctx ξ lo : TsoCtx.ctx_floor ξ lo -∗ lk_floor ξ lo.
  Proof. iIntros "H". by iLeft. Qed.
  Lemma lk_floor_of_wrote ξ lo a :
    TsoCtx.ctx_wrote ξ lo a -∗ lk_floor ξ lo.
  Proof. iIntros "#Hw". iRight. by iExists a. Qed.
  (* A6.123: the floor TRANSPORTS -- both arms land on the receiver's LEFT
     arm, so a payload or handle that carries a floor is [CtxMorph] with no
     absorb capability at all. *)
  Global Instance lk_floor_morph (lo : nat) : CtxMorph (λ ξ, lk_floor ξ lo).
  Proof.
    iIntros (ξ ξ') "Hd [#Hfl | (%a & #Hw)]".
    - iDestruct (TsoCtx.ctx_floor_dom with "Hd Hfl") as "[Hd #Hfl']".
      iFrame "Hd". by iLeft.
    - iDestruct (TsoCtx.ctx_dom_wrote_floor with "Hd Hw") as "[Hd #Hfl']".
      iFrame "Hd". by iLeft.
  Qed.
  (* A6.120: THE READ-SIDE CASH-IN, ON EITHER ARM -- the left is
     [own_context_floor_view], the right [own_context_wrote_vis]; both land
     on [ctx_vis] at the token's own receipt, so the racy read needs no
     absorbed opener. *)
  Lemma lk_floor_vis `{CID : CpuId} (ξ : TsoCtx.CtxId) (lo : nat) :
    TsoCtx.own_context ξ -∗ lk_floor ξ lo -∗
    TsoCtx.own_context ξ ∗ ∃ K : nat, TsoCtx.hart_view_lb K ∗ TsoCtx.ctx_vis ξ K lo.
  Proof.
    iIntros "Hrun #Hfl". iDestruct "Hfl" as "[#Hfl | (%a & #Hw)]".
    - iDestruct (TsoCtx.own_context_floor_view with "Hrun Hfl")
        as "[Hrun (%K & #HK & %HloK)]".
      iFrame "Hrun". iExists K. iFrame "HK". by iApply TsoCtx.ctx_vis_below.
    - iApply (TsoCtx.own_context_wrote_vis with "Hrun Hw").
  Qed.

  (* ------------------------------------------------------------------ *)
  (* [tso-flip WpLock.v:884-889], SHAPE COPIED VERBATIM.                  *)
  (*                                                                    *)
  (* This is a PROPAGATED shape, not an internal one: it is what          *)
  (* [initlock]'s postcondition hands back, so it reaches every initlock   *)
  (* caller and every [newlock] site (~15 files on the T-leg).  Shapes     *)
  (* that travel get the T-leg's spelling first time, because changing one *)
  (* later is a tree-wide edit; only INTERNALS (the creator mints below,   *)
  (* acquire's proof) stay simplified on the SC shim.                     *)
  (*                                                                    *)
  (* The only substitution is below the seal: the T-leg's owner cell is    *)
  (* [lk_cpu_at lo lk v], its LEDGER cell, and main's is the ctx word.     *)
  (* The bundling -- floor travelling WITH the cell rather than as a       *)
  (* separate premise -- is what lets the T-leg say of initlock's post     *)
  (* that "every caller's premise is unchanged". *)
  Definition lk_cpu_ready_at (lk : mword 64) (v : mword 64) : iProp Σ :=
    (∃ lo : nat, lock_cpu lk ↦₈ v ∗ lk_floor TsoCtx.cur_ctx lo)%I.

  Definition lk_cpu_ready (lk : mword 64) : iProp Σ :=
    lk_cpu_ready_at lk (zero_reg : mword 64).

  (* the SC-ONLY producer -- an INTERNAL, and it burns with the shim.  At
     TSO the floor arrives off the store leaf that wrote the cell
     ([lk_floor]'s right arm); at SC a position is not evidence of anything,
     so it is minted.  Every use is a site whose own store must supply the
     receipt at cutover. *)
  Lemma lk_cpu_ready_at_intro (lk : mword 64) (v : mword 64) :
    lock_cpu lk ↦₈ v -∗ lk_cpu_ready_at lk v.
  Proof.
    iIntros "Hcpu". iExists 0%nat. iFrame "Hcpu".
    iApply lk_floor_0.
  Qed.

  Lemma lk_cpu_ready_intro (lk : mword 64) :
    lock_cpu lk ↦₈ (zero_reg : mword 64) -∗ lk_cpu_ready lk.
  Proof. iApply lk_cpu_ready_at_intro. Qed.

  (* ------------------------------------------------------------------ *)
  (* §0.18': THE PAYLOAD IS A PARKED RECORD.   [tso WpLock.v:388,        *)
  (*                                            tso-flip WpLock.v:1002]  *)
  (* BOTH branches, character-identical.                                  *)
  (*                                                                    *)
  (* This is what makes the lambda payload ONE invariant serving every    *)
  (* context, and the reason §5.1(a) forbids the constant embedding: [R]  *)
  (* is stored at an EXISTENTIAL context beside that context's own parked *)
  (* token, so the invariant body mentions no ambient at all.             *)
  (*                                                                    *)
  (* TWO NEGATIVE RESULTS, recorded so nobody re-adds them (I tried both  *)
  (* and the branches refute both):                                       *)
  (*                                                                    *)
  (* (1) THERE IS NO BOUND PARAMETER.  §0.27''s relational [U] belongs to *)
  (*     the PROCESS RECORD, not to the generic lock payload; neither     *)
  (*     branch's [lock_pay] takes one.  The absorb's [T <= K] premise is *)
  (*     discharged AT THE ACQUIRE SITE out of the AMO's own receipt --   *)
  (*     and at SC by the trivially valid pair ([K := T], reflexivity;    *)
  (*     `tso` ProofAcquire.v).  Adding [U] here would be a second, wrong *)
  (*     home for a fact that already has one.                            *)
  (*                                                                    *)
  (* (2) THERE IS NO ELIM LEMMA, on either branch, and that is by design. *)
  (*     The token DOES NOT SURVIVE THE HELD PHASE: a record is minted    *)
  (*     per PUBLICATION, at release, and abandoned by the winner that    *)
  (*     claims it.  [ctx_absorb] hands the token back, so keeping it     *)
  (*     would force release's [ctx_deposit] to run inside the word-clear *)
  (*     store's ATOMIC UPDATE, where no [own_context] is in scope        *)
  (*     (§0.17''s measured rule) -- or to ride inside [locked], a        *)
  (*     resource change under every lock client.  Neither is needed      *)
  (*     because the stamp tie is per-publication.  The elimination is    *)
  (*     [ctx_absorb] applied at the acquire proof, where the receipt is. *)
  Definition lock_pay (R : TsoCtx.CtxId -> iProp Σ) : iProp Σ :=
    (∃ (xi : TsoCtx.CtxId) (T : nat), TsoCtx.ctx_parked xi T ∗ R xi)%I.
  (* A6.120 (tso-flip WpLock.v:1256): THE WINNER'S FORM of the record -- the
     same record, plus the acquirer's floor AT THE RECORD'S STAMP.  The AMO
     leaf mints it (the stamp is a legal log position, hence below the AMO's
     own); with it [SpecAcquire]'s absorb is [TsoCtxAbsorbLb.ctx_absorb_lb]
     and the receipt it exports is the floor cashed by
     [TsoCtx.own_context_floor_view]. *)
  Definition lock_pay_won (R : TsoCtx.CtxId -> iProp Σ) : iProp Σ :=
    (∃ (xi : TsoCtx.CtxId) (T : nat),
       TsoCtx.ctx_parked xi T ∗ TsoCtx.ctx_floor TsoCtx.cur_ctx T ∗ R xi)%I.

  (* THE CREATOR'S MINT, AND THE ONE SHIM USE IT COSTS.  [tso WpLock.v:404] --
     the M-LEG's form, deliberately, not the T-leg's.

     The T-leg's is honest ([own_context cur_ctx -∗ R cur_ctx ==∗
     own_context cur_ctx ∗ lock_pay R], via the real [ctx_deposit]) and is
     where this ends up.  It is NOT where main is now.  The M-leg's history
     is the guide: its opening commit (cd7acf164) landed "the SC-DEGENERATE
     context surface" with no running token anywhere; the token was threaded
     beside [sie_cap_gpr] "until M2 folds it into the bundle" (847f7c9b8),
     and only reached [sie_cap] at the later M1+M2 consolidation
     (ddd8fc5b0).  Main is at the FIRST of those stages.

     Taking the T-leg's form here costs the 19-call-site creator cascade AND
     then a conjunct inside [sie_cap] -- a predicate 446 files mention -- to
     supply the token the creators would need.  That is a later stage's bill,
     paid to convert a lock.

     ON SC THE TRANSPORT IS FREE AND NEEDS NO TOKEN: [ctx_morph] plus the
     shim's [ctx_dom_sc] moves [R] from any context to any other, because on
     SC the contexts are degenerate.  So the mint quarantines ONE shim use
     here, exactly as the M-leg does, and every creator keeps its signature.
     When the shim burns at cutover this lemma is the single compile error
     that names the whole cascade -- which is the point of quarantining it in
     one place. *)
  Lemma lock_pay_intro_sc (R : TsoCtx.CtxId -> iProp Σ)
      `{CtxMorph0 : !TsoCtx.CtxMorph R} :
    R TsoCtx.cur_ctx ==∗ lock_pay R.
  Proof.
    iIntros "HR".
    iMod TsoCtx.ctx_parked_alloc as (xic) "Hpk".
    iPoseProof (TsoCtxShim.ctx_dom_sc TsoCtx.cur_ctx xic) as "Hdom".
    iDestruct (TsoCtx.ctx_morph TsoCtx.cur_ctx xic with "Hdom HR") as "[_ HR]".
    iModIntro. iExists xic, 0%nat. iFrame "Hpk HR".
  Qed.
  (* THE HONEST MINT (tso-flip WpLock.v:1277): a plain deposit into a freshly
     allocated record, against the depositor's running token, which it hands
     straight back.  [own_context] is CpuId-indexed and this section binds no
     [CpuId], so the depositor's hart is a parameter.  Used by the release
     finisher's prelude ([lock_finisher_close]); the creators still take
     [lock_pay_intro_sc] (the deferred creator cascade, Amendment 5.2). *)
  Lemma lock_pay_intro `{CID : CpuId} (R : TsoCtx.CtxId -> iProp Σ)
      `{!TsoCtx.CtxMorph R} :
    TsoCtx.own_context TsoCtx.cur_ctx -∗ R TsoCtx.cur_ctx ==∗
    TsoCtx.own_context TsoCtx.cur_ctx ∗ lock_pay R.
  Proof.
    iIntros "Hrun HR".
    iMod TsoCtx.ctx_parked_alloc as (ξc) "Hpk".
    iMod (TsoCtx.ctx_deposit R TsoCtx.cur_ctx ξc 0 with "Hrun Hpk HR")
      as "(Hrun & %T' & _ & Hpk & HR)".
    iModIntro. iFrame "Hrun". iExists ξc, T'. iFrame "Hpk HR".
  Qed.

  (* SLICE 2 CHUNK 3.  [tso WpLock.v:437 / tso-flip WpLock.v:1057].
     The payload is now a FUNCTION of the context and the free arm holds
     [lock_pay R] -- the parked record -- rather than [R] itself.  That is
     what makes ONE Iris invariant serve every context (§5.1(a)): the body
     mentions no ambient, because [R] sits at an EXISTENTIAL context beside
     that context's own parked token.
     [lo] is the T-leg's allocation floor.  Its body use is below the seal
     (there it floors the owner cell, [lk_cpu_res lo st lk s]); here it is
     carried but not yet threaded, which is the seal principle exactly --
     the STATEMENT is the T-leg's, the body is SC's.  Chunk 3 does not
     invent a use for it. *)
  Definition lock_inv (γ : gname) (lk : mword 64) (s : string)
      (R : TsoCtx.CtxId -> iProp Σ) (lo : nat) : iProp Σ :=
    (∃ (v : mword 32) (st : lock_state) (B : nat),
       lock_word lk v ∗
       lk_cpu_res st lk s ∗
       lock_auth_at γ st B ∗
       (⌜st = None⌝ ∗ ⌜v = (mword_of_int 0 : mword 32)⌝ ∗ lock_frag γ None ∗
          lock_pay R
        ∨ ⌜st ≠ None⌝ ∗ ⌜neq_vec (sign_extend' 64 v) zero_reg = true⌝))%I.

  (* the lock's NAME: [lk->name] (the 8-byte pointer field at +8) holds the
     address of a NUL-terminated string [s].  initlock writes the field once
     and nothing ever writes it again, so both the field and the string it
     points at are held at [DfracDiscarded] -- [lock_name] is PERSISTENT, and
     therefore rides along inside the (persistent) lock predicate at no
     ownership cost: no proof has to thread the name field, and every holder
     of the lock knows which lock it is by name. *)
  Definition lock_name_field (lk : mword 64) : mword 64 :=
    add_vec lk (sign_extend' 64 (mword_of_int 8 : mword 12)).

  (* [tso WpLock.v:472 / tso-flip WpLock.v:1314]: a CLOSED term -- the
     discarded name-field word is RAW (a discarded byte lives at every
     context) and the string is [ctx_string_all], the ∀-context form -- so
     the handle's only ambient dependence is the floor below. *)
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
    iDestruct (TsoCtxShim.ctx_word_to_mem with "Hf") as "Hf".
    iMod (word_pointsto_persist with "Hf") as "#Hfp".
    iModIntro. iExists p. by iFrame "Hfp Hs".
  Qed.

  (* a lock is its (immutable) name plus the invariant over its two words. *)
  (* §0.35' + §0.38'.  [tso-flip WpLock.v:1135] -- NOT on the M-leg, whose
     [is_lock] is pre-§0.38' and carries no floor at all.
     THE ARITY DOES NOT MOVE: the context is AMBIENT ([cur_ctx], §6(d)'s
     corollary) and [lo] is EXISTENTIAL INSIDE, never in the exported type.
     What the floor buys is the premise four separate reads could not state;
     what it costs is that a handle can no longer be CONJURED -- a core that
     merely discovers the address of a freshly kalloc'd pipe page has no
     floor for it and must RECEIVE the handle through a real crossing, which
     is §0.35''s own soundness argument. *)
  Definition is_lock (γ : gname) (lk : mword 64) (s : string)
      (R : TsoCtx.CtxId -> iProp Σ) : iProp Σ :=
    (∃ lo : nat,
       lock_name lk s ∗ inv lockN (lock_inv γ lk s R lo) ∗
       lk_floor TsoCtx.cur_ctx lo)%I.

  Global Instance is_lock_persistent γ lk s R : Persistent (is_lock γ lk s R).
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
    ∃ lo : nat, inv lockN (lock_inv γ lk s R lo) ∗ lk_floor TsoCtx.cur_ctx lo.
  Proof.
    rewrite /is_lock. iIntros "(%lo & _ & #Hi & #Hf)".
    iExists lo. by iFrame "Hi Hf".
  Qed.
  Lemma is_lock_intro γ lk s R lo :
    lock_name lk s -∗ inv lockN (lock_inv γ lk s R lo) -∗
    lk_floor TsoCtx.cur_ctx lo -∗ is_lock γ lk s R.
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
  (* A6.109: THE FLOOR IS HOISTED OUT OF THE [□∀], AND IT HAS TO BE.  With
     [∃ lo] inside the accessor, two opens of the SAME lock hand out two
     unrelated witnesses -- so a leaf that gives the owner cell to an atomic
     update and takes it back cannot close the invariant it opened
     ([lock_inv … lo] and [lock_inv … lo'] are different propositions; the
     bug showed as three [iExact] failures each one [lo] apart).  Outside,
     [lo] is fixed once per consumer, which is what [is_lock] already does,
     and the arity still does not move.  [tso-flip WpLock.v:1219]. *)
  Definition lock_openable (γ : gname) (lk : mword 64) (s : string)
      (R : TsoCtx.CtxId -> iProp Σ) (D : iProp Σ) : iProp Σ :=
    (∃ lo : nat,
       lk_floor TsoCtx.cur_ctx lo ∗
       □ ∀ (E : coPset) (T : iProp Σ),
           ⌜↑lockN ⊆ E⌝ -∗ (T -∗ D -∗ False) -∗ T ={E, E ∖ ↑lockN}=∗
           ▷ lock_inv γ lk s R lo ∗ T ∗
           ((▷ lock_inv γ lk s R lo ={E ∖ ↑lockN, E}=∗ True) (* put it back *)
            ∧ (D ={E ∖ ↑lockN, E}=∗ True)))%I.             (* or destroy it *)

  (* THE PROJECTION, and consumers must come through it rather than
     destructing the definition: [lock_openable] carries an existential now
     (§0.38'/A6.109's hoisted floor), and letting each proof take the raw
     shape apart leaks the representation into every leaf.  Same discipline
     as [is_lock]'s three projections.  [tso-flip WpLock.v:1513]. *)
  Lemma lock_openable_parts γ lk s R D :
    lock_openable γ lk s R D -∗
    ∃ lo : nat,
      lk_floor TsoCtx.cur_ctx lo ∗
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
  (* [tso-flip WpLock.v:1313] -- the floor is a premise now, and the [∃ lo]
     is discharged HERE rather than inside the accessor (A6.109). *)
  Lemma lock_openable_inv γ lk s R lo :
    inv lockN (lock_inv γ lk s R lo) -∗ lk_floor TsoCtx.cur_ctx lo -∗
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
    inv lockN (lock_inv γ lk s R lo ∨ D) -∗ lk_floor TsoCtx.cur_ctx lo -∗
    lock_openable γ lk s R D.
  Proof.
    iIntros "#Hi #Hf". iExists lo. iFrame "Hf".
    iIntros "!>" (E T HE) "Hrefute HT".
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
  (* [tso-flip WpLock.v:1378].  The [∀ lo] is the T-leg's: the finisher is
     supplied BEFORE the open, so it cannot mention the [lo] the invariant
     turns out to be at, and must work at whichever one it is handed.  The
     payload piece is now the parked record.
     Main's two zeroed words stay as they are: the T-leg's
     [lock_word_fresh]/[lk_cpu_fresh] are its A6.89 LEDGER spellings, which
     are below the seal and are not this project's to land. *)
  (* A6.120 (tso-flip WpLock.v:1683): THE FINISHER IS TWO-PART.  The prelude
     runs at release's ENTRY, where the payload's own obligations are paid
     against the running token (the deposit, for a closing release); the
     body runs at the store.  [lock_finisher_body] is what the word-clear
     leaf takes; nothing outside this file looks inside [lock_finisher].
     The [∀ lo] is the T-leg's: the finisher is supplied BEFORE the open and
     must work at whichever floor the invariant turns out to be at. *)
  Definition lock_finisher_body (γ : gname) (lk : mword 64) (s : string)
      (R : TsoCtx.CtxId -> iProp Σ) (D Out : iProp Σ)
      (E : coPset) (Pay : iProp Σ) : iProp Σ :=
    ( ∀ lo : nat,
      ((▷ lock_inv γ lk s R lo ={E ∖ ↑lockN, E}=∗ True)
       ∧ (D ={E ∖ ↑lockN, E}=∗ True)) -∗
      lock_auth γ None -∗ lock_frag γ None -∗
      lk ↦₄ (mword_of_int 0 : mword 32) -∗
      lock_cpu lk ↦₈ (zero_reg : mword 64) -∗
      (* the lock's floor, off the opener the leaf holds: a destroying
         finisher hands the owner cell back BUNDLED ([lk_cpu_ready]) and
         needs it; a closing one ignores it. *)
      lk_floor TsoCtx.cur_ctx lo -∗
      Pay -∗
      |={E ∖ ↑lockN, E}=> Out)%I.
  Definition lock_finisher `{CID : CpuId} (γ : gname) (lk : mword 64)
      (s : string) (R : TsoCtx.CtxId -> iProp Σ) (D Out : iProp Σ)
      (E : coPset) : iProp Σ :=
    (∃ Pay : iProp Σ,
       (TsoCtx.own_context TsoCtx.cur_ctx -∗ R TsoCtx.cur_ctx ==∗
          TsoCtx.own_context TsoCtx.cur_ctx ∗ Pay) ∗
       lock_finisher_body γ lk s R D Out E Pay)%I.
  (* put it back: today's release, and equally the release of an object that
     merely still has other holders -- [D] is not used, only not taken.  The
     prelude is the deposit (§0.18′: the free arm is the parked record,
     minted honestly by [ctx_deposit]). *)
  Lemma lock_finisher_close `{CID : CpuId} γ lk s R `{!TsoCtx.CtxMorph R} D E :
    ⊢ lock_finisher γ lk s R D emp E.
  Proof.
    iExists (lock_pay R). iSplitR.
    { iIntros "Hrun HR". iApply (lock_pay_intro with "Hrun HR"). }
    iIntros (lo) "[Hclose _] Hauth Hfrag Hword Hcpu _ HR".
    iDestruct "Hauth" as (B) "Hauth".
    iMod ("Hclose" with "[Hauth Hfrag Hword Hcpu HR]") as "_"; [| by iModIntro].
    iApply bi.later_intro. iExists (mword_of_int 0 : mword 32), None, B.
    rewrite /lock_word lk_cpu_res_free. iFrame "Hword Hcpu Hauth".
    iLeft. by iFrame "Hfrag HR".
  Qed.
  (* destroy it and keep the storage.  The certificate [D] is assembled HERE,
     out of the ghost state the lock just gave up plus whatever the caller
     finds in [R] -- not brought along ready-made.  That generality is what a
     multiply-owned object needs: the last holder to let go has necessarily
     already surrendered its share of the certificate into [R], and [R] is
     only in hand at this instant (see PipeInv.pipe_res_dead).
     The prelude is the identity: the destroyer's payload stays at its own
     context, which is the context its completion wand speaks at.  The
     destroy arm's [Out] cannot mention [lo] (chosen before the open), so the
     owner cell leaves BUNDLED as [lk_cpu_ready] -- existentially floored,
     with the floor certificate beside it -- which is what [SpecRelease]'s
     cancel post hands back and [PipeInv.pipe_bytes_page_own] consumes. *)
  Lemma lock_finisher_destroy `{CID : CpuId} γ lk s R D Out E :
    (lock_frag γ None -∗ R TsoCtx.cur_ctx ==∗ D ∗ Out) -∗
    lock_finisher γ lk s R D
      (lk ↦₄ (mword_of_int 0 : mword 32) ∗ lk_cpu_ready lk ∗ Out) E.
  Proof.
    iIntros "Hcomplete". iExists (R TsoCtx.cur_ctx). iSplitR "Hcomplete".
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
  Proof. rewrite /lock_word /word4_pointsto. apply _. Qed.

  (* ---- lock construction (the "newlock" ghost step) ------------------ *)


  (* THE lock body, built: a free physical lock (word 0, cpu word 0) plus the
     resource it protects.  Whether that body then goes into a permanent [inv]
     or a cancellable [cinv] is the caller's business -- this is the piece both
     constructions share, and a basic update, so it can be done before the
     invariant's namespace or gname exists (which is what an object whose
     resource mentions its OWN cancel gname needs; see [newlock_c_delayed]). *)
  (* A6.66 / [tso-flip WpLock.v:1441]: the free arm is now the parked record,
     so the creator DEPOSITS (honestly, via [lock_pay_intro]) rather than
     wrapping the payload bare.  The running token is taken and handed
     straight back -- this is the 19-call-site creator cascade §0.18' priced
     and deferred, paid here. *)
  Lemma lock_inv_alloc (lo : nat) (lk : mword 64) (s : string)
      (R : TsoCtx.CtxId -> iProp Σ) `{!TsoCtx.CtxMorph R} :
    lk ↦₄ (mword_of_int 0 : mword 32) -∗
    lock_cpu lk ↦₈ (zero_reg : mword 64) -∗
    R TsoCtx.cur_ctx ==∗ ∃ γ : gname, lock_inv γ lk s R lo.
  Proof.
    iIntros "Hword Hcpu HR".
    iMod (lock_pay_intro_sc R with "HR") as "HR".
    iMod (own_alloc (((●E (None : leibnizO lock_state), ●E (0%nat : leibnizO nat))
                      ⋅ (◯E (None : leibnizO lock_state), ◯E (0%nat : leibnizO nat)))
                     : lockUR)) as (γ) "H"; [ split; apply excl_auth_valid | ].
    iDestruct (own_op with "H") as "[Ha Hf]".
    iAssert (lock_frag γ None) with "[Hf]" as "Hf"; [ by iExists 0%nat | ].
    iModIntro. iExists γ.
    iExists (mword_of_int 0 : mword 32), None, 0%nat.
    rewrite /lock_word lk_cpu_res_free. iFrame "Hword Hcpu Ha".
    iLeft. iFrame "Hf HR". done.
  Qed.

  (* a FREE physical lock plus its resource become a lock that can DIE: the
     body carries the dead branch from the start, and the ghost name of the
     lock state is chosen FIRST, so [R] and [D] may both mention it -- which
     they do for any object whose dead state parks the lock's own state
     fragment (PipeInv.pipe_dead). *)
  Lemma newlock_d E (lo : nat) (lk : mword 64) (s : string) :
    lk ↦₄ (mword_of_int 0 : mword 32) -∗
    lock_cpu lk ↦₈ (zero_reg : mword 64) ==∗
    ∃ γ : gname, ∀ (R : TsoCtx.CtxId -> iProp Σ) (D : iProp Σ),
      ⌜TsoCtx.CtxMorph R⌝ -∗
      R TsoCtx.cur_ctx ={E}=∗ inv lockN (lock_inv γ lk s R lo ∨ D).
  Proof.
    iIntros "Hword Hcpu".
    iMod (own_alloc (((●E (None : leibnizO lock_state), ●E (0%nat : leibnizO nat))
                      ⋅ (◯E (None : leibnizO lock_state), ◯E (0%nat : leibnizO nat)))
                     : lockUR)) as (γ) "H"; [ split; apply excl_auth_valid | ].
    iDestruct (own_op with "H") as "[Ha Hf]".
    iAssert (lock_frag γ None) with "[Hf]" as "Hf"; [ by iExists 0%nat | ].
    iModIntro. iExists γ. iIntros (R D) "%HmR HR".
    iMod (lock_pay_intro_sc (CtxMorph0 := HmR) R with "HR") as "HR".
    iApply (inv_alloc lockN E (lock_inv γ lk s R lo ∨ D)).
    iApply bi.later_intro. iLeft. iExists (mword_of_int 0 : mword 32), None, 0%nat.
    rewrite /lock_word lk_cpu_res_free. iFrame "Hword Hcpu Ha".
    iLeft. iFrame "Hf HR". done.
  Qed.

  (* a FREE physical lock plus the resource it protects and its name become a
     (permanent) lock. *)
  (* §0.35'(i)/(iii) [tso-flip WpLock.v:1495]: a creator that hands back a
     HANDLE owes the floor, and buys it with a receipt like everyone else.  A
     creator that hands back the bare INVARIANT ([lock_inv_alloc],
     [newlock_d]) owes nothing -- the floor is a property of the handle, not
     of the lock. *)
  Lemma newlock E (lk : mword 64) (s : string)
      (R : TsoCtx.CtxId -> iProp Σ) `{!TsoCtx.CtxMorph R} :
    lock_name lk s -∗
    lk ↦₄ (mword_of_int 0 : mword 32) -∗
    lk_cpu_ready lk -∗
    R TsoCtx.cur_ctx ={E}=∗ ∃ γ : gname, is_lock γ lk s R.
  Proof.
    iIntros "#Hnm Hword Hready HR".
    rewrite /lk_cpu_ready /lk_cpu_ready_at.
    iDestruct "Hready" as (lo) "[Hcpu #Hfl]".
    iMod (lock_inv_alloc lo lk s R with "Hword Hcpu HR") as (γ) "Hbody".
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
  Lemma newlock_delayed E (lk : mword 64) (s : string) :
    lock_name lk s -∗
    lk ↦₄ (mword_of_int 0 : mword 32) -∗
    lk_cpu_ready lk ==∗
    ∃ γ : gname, ∀ R : TsoCtx.CtxId -> iProp Σ,
      ⌜TsoCtx.CtxMorph R⌝ -∗ R TsoCtx.cur_ctx ={E}=∗ is_lock γ lk s R.
  Proof.
    iIntros "#Hnm Hword Hready".
    rewrite /lk_cpu_ready /lk_cpu_ready_at.
    iDestruct "Hready" as (lo) "[Hcpu #Hfl]".
    iMod (own_alloc (((●E (None : leibnizO lock_state), ●E (0%nat : leibnizO nat))
                      ⋅ (◯E (None : leibnizO lock_state), ◯E (0%nat : leibnizO nat)))
                     : lockUR)) as (γ) "H"; [ split; apply excl_auth_valid | ].
    iDestruct (own_op with "H") as "[Ha Hf]".
    iAssert (lock_frag γ None) with "[Hf]" as "Hf"; [ by iExists 0%nat | ].
    iModIntro. iExists γ. iIntros (R) "%HmR HR".
    iMod (lock_pay_intro_sc (CtxMorph0 := HmR) R with "HR") as "HR".
    iMod (inv_alloc lockN E (lock_inv γ lk s R lo) with "[Hword Hcpu Ha Hf HR]") as "#Hinv".
    { iApply bi.later_intro. iExists (mword_of_int 0 : mword 32), None, 0%nat.
      rewrite /lock_word lk_cpu_res_free. iFrame "Hword Hcpu Ha".
      iLeft. iFrame "Hf HR". done. }
    iModIntro. iApply (is_lock_intro with "Hnm Hinv Hfl").
  Qed.

End Lock.

(* THE INVARIANT BODY AT ANOTHER CONTEXT -- main's pre-M4 shim (Amendment
   8, §5.2 deviation).  On the T-leg the lock's two words are LEDGER cells
   (A6.89) and the body is context-free, so the handle moves by its floor
   alone; on main the words are still context cells at the ambient context,
   so moving a handle re-indexes the body through the shim's cell laws.
   Dies with the M4 ledger flip; until then it is the body half of
   [is_lock_morph]. *)
Lemma lock_inv_reindex `{!riscvGS Σ, !lockG Σ} (xi xi' : TsoCtx.CtxId) γ lk s R lo :
  lock_inv (XI := xi) γ lk s R lo -∗ lock_inv (XI := xi') γ lk s R lo.
Proof.
  rewrite /lock_inv /lock_word /lk_cpu_res.
  iIntros "(%v & %st & %B & Hw & [Hc Hf] & Ha & Hrest)".
  iExists v, st, B. iFrame "Ha Hrest Hf".
  iSplitL "Hw". { iApply (TsoCtxShim.ctx_word4_reindex with "Hw"). }
  iDestruct (TsoCtxShim.ctx_word_to_mem with "Hc") as "Hc".
  iApply (TsoCtxShim.ctx_word_of_mem with "Hc").
Qed.
(* THE HANDLE TRANSPORTS (A6.123): the floor moves by [lk_floor_morph] (the
   honest half), the body by [lock_inv_reindex] (the shim half, above).
   Stated outside the section because the section's ambient [XI] is what
   this varies.  This is the law the console rows' morphs ride
   ([ConsoleInv]); the SC-only [is_lock_reindex] that re-minted the floor
   from the install receipt is gone with the receipt arm (Amendment 8,
   §5.2). *)
Global Instance is_lock_morph `{!riscvGS Σ, !lockG Σ} γ lk s (R : TsoCtx.CtxId -> iProp Σ) :
  TsoCtx.CtxMorph (λ ξ : TsoCtx.CtxId, is_lock (XI := ξ) γ lk s R).
Proof.
  iIntros (ξ ξ') "Hd #H".
  iDestruct (is_lock_name (XI := ξ) with "H") as "#Hn".
  iDestruct (is_lock_inv (XI := ξ) with "H") as (lo) "[#Hi #Hf]".
  iDestruct (lk_floor_morph lo ξ ξ' with "Hd Hf") as "[Hd #Hf']".
  iFrame "Hd". iApply (is_lock_intro (XI := ξ') γ lk s R lo with "Hn [] Hf'").
  iApply (inv_iff with "Hi"). iIntros "!> !>".
  iSplit; iIntros "Hl"; iApply (lock_inv_reindex with "Hl").
Qed.

(* THE PAYLOAD'S OWN REINDEX, for a [<{ P }>] whose [P] mentions the ambient
   context: [is_lock] is proper in its payload up to a persistent
   equivalence, because the payload only ever sits inside [lock_pay] under
   the invariant.  Not a shim -- an [inv_iff] -- but it is only ever needed
   together with [is_lock_morph] above, to restate a const-payload lock at
   another context (ConsoleInv.console_inv_morph). *)
Lemma is_lock_pay_iff `{!riscvGS Σ, !lockG Σ} `{XI : TsoCtx.CurCtx} γ lk s
    (R R' : TsoCtx.CtxId -> iProp Σ) :
  □ (∀ xi : TsoCtx.CtxId, R xi ∗-∗ R' xi) -∗ is_lock γ lk s R -∗ is_lock γ lk s R'.
Proof.
  iIntros "#HRR #H".
  iDestruct (is_lock_name with "H") as "#Hn".
  iDestruct (is_lock_inv with "H") as (lo) "[#Hi #Hf]".
  iApply (is_lock_intro γ lk s R' lo with "Hn [] Hf").
  iApply (inv_iff with "Hi"). iIntros "!> !>".
  rewrite /lock_inv /lock_pay.
  iSplit.
  - iIntros "(%v & %st & %B & Hw & Hc & Ha & Hrest)". iExists v, st, B. iFrame "Hw Hc Ha".
    iDestruct "Hrest" as "[(%Hst & %Hv & Hfr & (%xi & %T & Hpk & HR)) | Hr]";
      [| iRight; iExact "Hr"].
    iLeft. iSplit; [done|]. iSplit; [done|]. iFrame "Hfr". iExists xi, T. iFrame "Hpk".
    iDestruct ("HRR" $! xi) as "[H1 _]". iApply ("H1" with "HR").
  - iIntros "(%v & %st & %B & Hw & Hc & Ha & Hrest)". iExists v, st, B. iFrame "Hw Hc Ha".
    iDestruct "Hrest" as "[(%Hst & %Hv & Hfr & (%xi & %T & Hpk & HR)) | Hr]";
      [| iRight; iExact "Hr"].
    iLeft. iSplit; [done|]. iSplit; [done|]. iFrame "Hfr". iExists xi, T. iFrame "Hpk".
    iDestruct ("HRR" $! xi) as "[_ H2]". iApply ("H2" with "HR").
Qed.
