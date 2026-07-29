(* WpLock.v -- the standard CSL/Iris spin-lock invariant for xv6's
   [struct spinlock], mirroring iris_heap_lang/lib/spin_lock.v but over the
   PHYSICAL fields of the Sail RISC-V machine: the 4-byte lock word
   ([lk->locked] @ +0) AND the 8-byte owner word ([lk->cpu] @ +16).

     lock_inv      -- ∃ v st, lock word ↦ v ∗ lk->cpu ↦ (cpu of st) ∗ ghost st
                        ∗ (st free ∗ v = 0 ∗ frag ∗ R  ∨  st held ∗ v ≠ 0)
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
From iris.algebra Require Import excl gmap.
From iris.algebra.lib Require Import excl_auth.
From iris.base_logic.lib Require Import invariants cancelable_invariants own.
Require Import SailStdpp.Base SailStdpp.Operators_mwords.
Require Import Riscv.rv64d.
Require Import RiscvPtsto RiscvLang.
Require Import ProcGeom.
Local Open Scope Z_scope.

(* ===================================================================== *)
(* The lock's ghost state.                                               *)
(*                                                                       *)
(* An excl_auth over [lock_state]: the invariant keeps the authority, the *)
(* holder keeps the fragment -- so the holder's token pins the [cpu]      *)
(* field, and the fragment cannot be forged.                              *)
(* ===================================================================== *)
Definition lock_state : Type := option (CPU * bool).

Definition lockUR : ucmra := excl_authUR (leibnizO lock_state).

Class lockG (Σ : gFunctors) := LockG { lock_inG :: inG Σ lockUR }.
Definition lockΣ : gFunctors := #[GFunctor lockUR].
Global Instance subG_lockΣ {Σ} : subG lockΣ Σ -> lockG Σ.
Proof. solve_inG. Qed.

Section Lock.
  Context `{!riscvGS Σ, !lockG Σ}.

  (* sibling of [minstretN]; the two are disjoint by construction, so a leaf
     can open [is_lock] INSIDE the step engine's [⊤ ∖ ↑minstretN] callback. *)
  Definition lockN : namespace := nroot .@ "xv6spinlock".

  (* ---- the ghost pieces ---------------------------------------------- *)

  (* the authority on the lock's state; lives in the invariant. *)
  Definition lock_auth (γ : gname) (st : lock_state) : iProp Σ :=
    own γ ((●E (st : leibnizO lock_state)) : lockUR).
  (* the state fragment; the free one lives in the invariant, a held one is
     the holder's token (see [locked] / [locked_pre]). *)
  Definition lock_frag (γ : gname) (st : lock_state) : iProp Σ :=
    own γ ((◯E (st : leibnizO lock_state)) : lockUR).

  (* THE holder token: hart [i] holds the lock and [lk->cpu = cpus_ptr i]. *)
  Definition locked (γ : gname) (i : CPU) : iProp Σ :=
    lock_frag γ (Some (i, true)).
  (* the same, in the window where [lk->cpu] is still 0 (internal to the
     acquire / release proofs; no caller ever sees it). *)
  Definition locked_pre (γ : gname) (i : CPU) : iProp Σ :=
    lock_frag γ (Some (i, false)).

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
    iIntros "Ha Hf".
    iDestruct (own_valid_2 with "Ha Hf") as %Hv.
    iPureIntro. exact (excl_auth_agree_L _ _ Hv).
  Qed.


  (* the state fragment is exclusive: two of them cannot coexist, whatever
     states they claim -- so two holder tokens are impossible. *)
  Lemma lock_frag_exclusive γ st st' :
    lock_frag γ st -∗ lock_frag γ st' -∗ False.
  Proof.
    iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as %Hv.
    destruct (proj1 (excl_auth_frag_op_valid _ _) Hv).
  Qed.

  Lemma locked_exclusive γ i j : locked γ i -∗ locked γ j -∗ False.
  Proof. apply lock_frag_exclusive. Qed.

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
    iMod (own_alloc ((◯E (None : leibnizO lock_state)) : lockUR)) as (γ) "H".
    { apply auth_frag_valid. done. }
    iModIntro. iExists γ. iExact "H".
  Qed.

  (* THE holder law: the token pins the owner word to your own [struct cpu]. *)
  Lemma locked_state γ st i :
    lock_auth γ st -∗ locked γ i -∗ ⌜st = Some (i, true)⌝.
  Proof. apply lock_frag_agree. Qed.

  Lemma locked_cpu_eq γ st i :
    lock_auth γ st -∗ locked γ i -∗ ⌜lk_cpu_val st = cpus_ptr i⌝.
  Proof.
    iIntros "Hg Ht".
    iDestruct (locked_state with "Hg Ht") as %->. done.
  Qed.

  Lemma locked_pre_state γ st i :
    lock_auth γ st -∗ locked_pre γ i -∗ ⌜st = Some (i, false)⌝.
  Proof. apply lock_frag_agree. Qed.

  (* ---- the four state transitions (one per lock instruction) --------- *)

  Local Lemma lock_state_update γ st st' :
    lock_auth γ st -∗ lock_frag γ st ==∗ lock_auth γ st' ∗ lock_frag γ st'.
  Proof.
    iIntros "Ha Hf".
    rewrite -own_op.
    iApply (own_update_2 with "Ha Hf").
    apply excl_auth_update.
  Qed.

  (* acquire's amoswap: a free lock becomes "held by i, cpu not yet
     written". *)
  Lemma lock_take γ i :
    lock_auth γ None -∗ lock_frag γ None ==∗
    lock_auth γ (Some (i, false)) ∗ locked_pre γ i.
  Proof. apply lock_state_update. Qed.

  (* acquire's [lk->cpu = mycpu()]: the window closes, the holder gets THE
     token. *)
  Lemma lock_setcpu γ st i :
    lock_auth γ st -∗ locked_pre γ i ==∗
    ⌜st = Some (i, false)⌝ ∗ lock_auth γ (Some (i, true)) ∗ locked γ i.
  Proof.
    iIntros "Ha Hf".
    iDestruct (locked_pre_state with "Ha Hf") as %->.
    iMod (lock_state_update γ (Some (i, false)) (Some (i, true)) with "Ha Hf") as "[Ha Hf]".
    iModIntro. iSplitR; [done|]. iFrame "Ha Hf".
  Qed.

  (* release's [lk->cpu = 0]: back into the window. *)
  Lemma lock_clrcpu γ st i :
    lock_auth γ st -∗ locked γ i ==∗
    ⌜st = Some (i, true)⌝ ∗ lock_auth γ (Some (i, false)) ∗ locked_pre γ i.
  Proof.
    iIntros "Ha Hf".
    iDestruct (locked_state with "Ha Hf") as %->.
    iMod (lock_state_update γ (Some (i, true)) (Some (i, false)) with "Ha Hf") as "[Ha Hf]".
    iModIntro. iSplitR; [done|]. iFrame "Ha Hf".
  Qed.

  (* release's word clear: the lock goes free again. *)
  Lemma lock_give γ st i :
    lock_auth γ st -∗ locked_pre γ i ==∗
    ⌜st = Some (i, false)⌝ ∗ lock_auth γ None ∗ lock_frag γ None.
  Proof.
    iIntros "Ha Hf".
    iDestruct (locked_pre_state with "Ha Hf") as %->.
    iMod (lock_state_update γ (Some (i, false)) None with "Ha Hf") as "[Ha Hf]".
    iModIntro. iSplitR; [done|]. iFrame "Ha Hf".
  Qed.

  (* ---- the physical fields ------------------------------------------- *)

  (* the physical 4-byte little-endian lock word at address [lk]: the 4-byte
     word points-to [↦₄] (which also bundles the 4-byte alignment of [lk]). *)
  Definition lock_word (lk : mword 64) (v : mword 32) : iProp Σ :=
    (lk ↦₄ v)%I.

  (* [lk->cpu]: the 8-byte owner word at +16, in the address form the
     acquire / release / holding leaves see it ([add_vec lk (sext 16)]). *)
  Definition lock_cpu (lk : mword 64) : mword 64 :=
    add_vec lk (sign_extend' 64 (mword_of_int 16 : mword 12)).

  Definition lock_inv (γ : gname) (lk : mword 64) (R : iProp Σ) : iProp Σ :=
    (∃ (v : mword 32) (st : lock_state),
       lock_word lk v ∗
       lock_cpu lk ↦₈ lk_cpu_val st ∗
       lock_auth γ st ∗
       (⌜st = None⌝ ∗ ⌜v = (mword_of_int 0 : mword 32)⌝ ∗ lock_frag γ None ∗ R
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

  Definition lock_name (lk : mword 64) (s : string) : iProp Σ :=
    (∃ p : mword 64, lock_name_field lk ↦₈□ p ∗ p ↦ₛ□ s)%I.

  Global Instance lock_name_persistent lk s : Persistent (lock_name lk s).
  Proof. apply _. Qed.

  (* Sealing the name field.  [initlock] hands the field back OWNED (it is
     inside the object's storage, and [kfree] memsets it, so a lock on a
     kalloc'd page cannot afford to have it discarded); a caller whose lock is
     static seals it here and forgets it.  A basic update, so this works in
     place inside a WP goal -- no [fupd_wp] needed. *)
  Lemma lock_name_intro (lk p : mword 64) (s : string) :
    p ↦ₛ□ s -∗ lock_name_field lk ↦₈ p ==∗ lock_name lk s.
  Proof.
    iIntros "#Hs Hf".
    iMod (word_pointsto_persist with "Hf") as "#Hfp".
    iModIntro. iExists p. by iFrame "Hfp Hs".
  Qed.

  (* a lock is its (immutable) name plus the invariant over its two words. *)
  Definition is_lock (γ : gname) (lk : mword 64) (s : string) (R : iProp Σ) : iProp Σ :=
    (lock_name lk s ∗ inv lockN (lock_inv γ lk R))%I.

  Global Instance is_lock_persistent γ lk s R : Persistent (is_lock γ lk s R).
  Proof. apply _. Qed.

  (* the two projections + the introduction rule (the only interface the
     lock leaves and [newlock] need). *)
  Lemma is_lock_name γ lk s R : is_lock γ lk s R -∗ lock_name lk s.
  Proof. iIntros "[$ _]". Qed.
  Lemma is_lock_inv γ lk s R : is_lock γ lk s R -∗ inv lockN (lock_inv γ lk R).
  Proof. iIntros "[_ $]". Qed.
  Lemma is_lock_intro γ lk s R :
    lock_name lk s -∗ inv lockN (lock_inv γ lk R) -∗ is_lock γ lk s R.
  Proof. iIntros "#Hn #Hi". by iFrame "Hn Hi". Qed.

  (* ---- THE OPENING INTERFACE ------------------------------------------

     WpSconfLock.v is the only file in the tree that ever opens a lock, and
     all its leaves do the same three things: open [lock_inv], take one
     machine step, put it back.  [lock_openable] is that pattern named, with
     two parameters that decide WHOSE lock it is:

       T -- the OPENING CREDENTIAL.  Presented to open, handed straight back.
       D -- the DISPOSAL certificate.  Surrendering it destroys the invariant
            instead of closing it, and the opener keeps the contents.

     Two instances, and they are the whole point:

       inv lockN (lock_inv γ lk R)              -- any T, D := False
            anyone may open, nobody may destroy: a static kernel lock, and
            exactly today's behaviour
       inv lockN (lock_inv γ lk R ∨ D)          -- any T that REFUTES D
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
  Definition lock_openable (γ : gname) (lk : mword 64) (R D : iProp Σ) : iProp Σ :=
    (□ ∀ (E : coPset) (T : iProp Σ),
         ⌜↑lockN ⊆ E⌝ -∗ (T -∗ D -∗ False) -∗ T ={E, E ∖ ↑lockN}=∗
         ▷ lock_inv γ lk R ∗ T ∗
         ((▷ lock_inv γ lk R ={E ∖ ↑lockN, E}=∗ True)      (* put it back *)
          ∧ (D ={E ∖ ↑lockN, E}=∗ True)))%I.               (* or destroy it *)

  Global Instance lock_openable_persistent γ lk R D :
    Persistent (lock_openable γ lk R D).
  Proof. apply _. Qed.

  (* a permanent [inv]: nothing has to be refuted, and no disposal is
     possible. *)
  Lemma lock_openable_inv γ lk R :
    inv lockN (lock_inv γ lk R) ⊢ lock_openable γ lk R False.
  Proof.
    iIntros "#Hi !>" (E T HE) "_ HT".
    iMod (inv_acc E lockN with "Hi") as "[Hbody Hclose]"; [done|].
    iModIntro. iFrame "Hbody HT".
    iSplit; [iExact "Hclose" | iIntros "%Hf"; destruct Hf].
  Qed.

  (* the bridge every existing lock user rides: today's lock IS the permanent
     instance of the generic one. *)
  Lemma is_lock_openable γ lk s R : is_lock γ lk s R ⊢ lock_openable γ lk R False.
  Proof. iIntros "H". iApply lock_openable_inv. by iApply is_lock_inv. Qed.

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
  Lemma lock_openable_of_dead γ lk R D `{!Timeless D} :
    inv lockN (lock_inv γ lk R ∨ D) ⊢ lock_openable γ lk R D.
  Proof.
    iIntros "#Hi !>" (E T HE) "Hrefute HT".
    iMod (inv_acc E lockN with "Hi") as "[Hbody Hclose]"; [done|].
    rewrite bi.later_or. iDestruct "Hbody" as "[Hlive | >Hdead]".
    2:{ iExFalso. iApply ("Hrefute" with "HT Hdead"). }
    iModIntro. iFrame "Hlive HT".
    iSplit.
    - iIntros "Hb". iApply "Hclose". by iLeft.
    - iIntros "Hd". iApply "Hclose". iRight. by iNext.
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
  Definition lock_finisher (γ : gname) (lk : mword 64) (R D Out : iProp Σ)
      (E : coPset) : iProp Σ :=
    ( ((▷ lock_inv γ lk R ={E ∖ ↑lockN, E}=∗ True)
       ∧ (D ={E ∖ ↑lockN, E}=∗ True)) -∗
      lock_auth γ None -∗ lock_frag γ None -∗
      lk ↦₄ (mword_of_int 0 : mword 32) -∗
      lock_cpu lk ↦₈ (zero_reg : mword 64) -∗
      R -∗
      |={E ∖ ↑lockN, E}=> Out)%I.

  (* put it back: today's release, and equally the release of an object that
     merely still has other holders -- [D] is not used, only not taken. *)
  Lemma lock_finisher_close γ lk R D E : ⊢ lock_finisher γ lk R D emp E.
  Proof.
    iIntros "[Hclose _] Hauth Hfrag Hword Hcpu HR".
    iMod ("Hclose" with "[Hauth Hfrag Hword Hcpu HR]") as "_"; [| by iModIntro].
    iNext. iExists (mword_of_int 0 : mword 32), None.
    rewrite /lock_word. iFrame "Hword Hcpu Hauth".
    iLeft. by iFrame "Hfrag HR".
  Qed.

  (* destroy it and keep the storage.  The certificate [D] is assembled HERE,
     out of the ghost state the lock just gave up plus whatever the caller
     finds in [R] -- not brought along ready-made.  That generality is what a
     multiply-owned object needs: the last holder to let go has necessarily
     already surrendered its share of the certificate into [R], and [R] is
     only in hand at this instant (see PipeInv.pipe_res_dead). *)
  Lemma lock_finisher_destroy γ lk R D Out E :
    (lock_frag γ None -∗ R ==∗ D ∗ Out) -∗
    lock_finisher γ lk R D
      (lk ↦₄ (mword_of_int 0 : mword 32) ∗ lock_cpu lk ↦₈ (zero_reg : mword 64) ∗ Out) E.
  Proof.
    iIntros "Hcomplete [_ Hdispose] Hauth Hfrag Hword Hcpu HR".
    iMod ("Hcomplete" with "Hfrag HR") as "[HD HOut]".
    iMod ("Hdispose" with "HD") as "_".
    iModIntro. by iFrame "Hword Hcpu HOut".
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
  Lemma lock_inv_alloc (lk : mword 64) (R : iProp Σ) :
    lk ↦₄ (mword_of_int 0 : mword 32) -∗
    lock_cpu lk ↦₈ (zero_reg : mword 64) -∗
    R ==∗ ∃ γ : gname, lock_inv γ lk R.
  Proof.
    iIntros "Hword Hcpu HR".
    iMod (own_alloc ((●E (None : leibnizO lock_state) ⋅ ◯E (None : leibnizO lock_state))
                     : lockUR)) as (γ) "H"; [ apply excl_auth_valid | ].
    iDestruct (own_op with "H") as "[Ha Hf]".
    iModIntro. iExists γ.
    iExists (mword_of_int 0 : mword 32), None.
    rewrite /lock_word. iFrame "Hword Hcpu Ha".
    iLeft. iFrame "Hf HR". done.
  Qed.

  (* a FREE physical lock plus its resource become a lock that can DIE: the
     body carries the dead branch from the start, and the ghost name of the
     lock state is chosen FIRST, so [R] and [D] may both mention it -- which
     they do for any object whose dead state parks the lock's own state
     fragment (PipeInv.pipe_dead). *)
  Lemma newlock_d E (lk : mword 64) :
    lk ↦₄ (mword_of_int 0 : mword 32) -∗
    lock_cpu lk ↦₈ (zero_reg : mword 64) ==∗
    ∃ γ : gname, ∀ (R D : iProp Σ),
      R ={E}=∗ inv lockN (lock_inv γ lk R ∨ D).
  Proof.
    iIntros "Hword Hcpu".
    iMod (own_alloc ((●E (None : leibnizO lock_state) ⋅ ◯E (None : leibnizO lock_state))
                     : lockUR)) as (γ) "H"; [ apply excl_auth_valid | ].
    iDestruct (own_op with "H") as "[Ha Hf]".
    iModIntro. iExists γ. iIntros (R D) "HR".
    iApply (inv_alloc lockN E (lock_inv γ lk R ∨ D)).
    iNext. iLeft. iExists (mword_of_int 0 : mword 32), None.
    rewrite /lock_word. iFrame "Hword Hcpu Ha".
    iLeft. iFrame "Hf HR". done.
  Qed.

  (* a FREE physical lock plus the resource it protects and its name become a
     (permanent) lock. *)
  Lemma newlock E (lk : mword 64) (s : string) (R : iProp Σ) :
    lock_name lk s -∗
    lk ↦₄ (mword_of_int 0 : mword 32) -∗
    lock_cpu lk ↦₈ (zero_reg : mword 64) -∗
    R ={E}=∗ ∃ γ : gname, is_lock γ lk s R.
  Proof.
    iIntros "#Hnm Hword Hcpu HR".
    iMod (lock_inv_alloc lk R with "Hword Hcpu HR") as (γ) "Hbody".
    iMod (inv_alloc lockN E (lock_inv γ lk R) with "[Hbody]") as "#Hinv";
      [ by iNext | ].
    iModIntro. iExists γ.
    iApply (is_lock_intro with "Hnm Hinv").
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
    lock_cpu lk ↦₈ (zero_reg : mword 64) ==∗
    ∃ γ : gname, ∀ R : iProp Σ, R ={E}=∗ is_lock γ lk s R.
  Proof.
    iIntros "#Hnm Hword Hcpu".
    iMod (own_alloc ((●E (None : leibnizO lock_state) ⋅ ◯E (None : leibnizO lock_state))
                     : lockUR)) as (γ) "H"; [ apply excl_auth_valid | ].
    iDestruct (own_op with "H") as "[Ha Hf]".
    iModIntro. iExists γ. iIntros (R) "HR".
    iMod (inv_alloc lockN E (lock_inv γ lk R) with "[Hword Hcpu Ha Hf HR]") as "#Hinv".
    { iNext. iExists (mword_of_int 0 : mword 32), None.
      rewrite /lock_word. iFrame "Hword Hcpu Ha".
      iLeft. iFrame "Hf HR". done. }
    iModIntro. iApply (is_lock_intro with "Hnm Hinv").
  Qed.

End Lock.
