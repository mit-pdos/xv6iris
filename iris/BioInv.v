(* BioInv.v -- the bio.c ownership layer over the buffer cache: the
   reference-count algebra, the per-buffer content ESCROW, the bcache lock's
   resource, and the persistent [bio_ctx] every bio function shares.

   Design (claude-notes/projects/bio.md).  The two facts that force the shape:

   (1) A releasing holder's content must be reachable from the sleeplock side
       BY THE END of releasesleep -- a blocked waiter's acquiresleep can
       return (and its caller touch b->valid / b->data) before the releaser's
       refcnt-- runs.
   (2) bget's miss path rewrites dev/blockno/valid under ONLY bcache.lock
       (at refcnt==0), and its scan reads every buffer's dev/blockno there --
       so those cells can be fully inside neither the sleeplock chain nor
       the bcache resource.

   So the traveling content lives in a per-buffer ESCROW -- a namespace
   invariant, openable atomically at any instruction -- with two arms:

     A1 (parked):      valid (full) + dev (1/2) + buf_own (blockno 1/2,
                       disk pinned 0, the 1024 data bytes)
     A2 (checked out): the chain's own reference fragment with its
                       dev/blockno fraction q, plus the checkout token
                       [bown k]

   and the buffer's sleeplock protects EXACTLY [bown k].  A checkout
   (post-acquiresleep) refutes A2 with the bown in hand and swaps its ref +
   bown in for the parked bundle; a park (brelse's first instruction) refutes
   A1 with the full valid cell in hand (fraction 1+1 > 1) and swaps back.
   The miss path (refcnt==0, bcache.lock held) refutes A2 with the auth
   (M !! k = None vs the arm's fragment) and mutates the parked cells one
   atomic store at a time -- the bundle is parked at every instruction
   boundary, which is also what makes the recycler-vs-hit-thread race safe.

   The count algebra is FileInv's Arc algebra verbatim: auth (gmap nat
   (frac * positive)); M !! k = Some (q, n) means n outstanding references
   hold fraction q of buffer k's dev+blockno cells between them (the bundle
   holds 1/2 permanently; the bcache resource retains qr with q + qr = 1/2).
   Counts are bounded by the finite [bslot] supply (FdSlots.v's recipe): the
   caller of every increment supplies one unit, the resource stores n units
   per busy buffer, every decrement returns one -- that is what makes the
   unchecked refcnt++ provable and keeps the cell a faithful int. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import excl auth gmap frac numbers.
From iris.base_logic.lib Require Import gen_heap invariants own.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes.
Require Import RiscvPtsto.
Require Import InstrBytes.
Require Import WpLock.
Require Import SleepLock.
Require Import ArrCursor.
Require Import BufOwn.
Require Import BcacheInv.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Local Open Scope Z_scope.

(* ------------------------------------------------------------------ *)
(*  Geometry: the pa-tier node base and the refcnt cell                 *)
(* ------------------------------------------------------------------ *)

(* the [k]th buffer's base, at the tier BufOwn's field addresses use.
   [Arch.pa] and [mword 64] are convertible at rv64; the ascription keeps
   downstream elaboration at the reduced width (durable-notes). *)
Definition bpa (k : nat) : Arch.pa := bnode k.

Definition brefcnt (k : nat) : Arch.pa := pa_add (bpa k) 64.

(* ------------------------------------------------------------------ *)
(*  The reference-count algebra (FileInv's Arc algebra, verbatim)       *)
(* ------------------------------------------------------------------ *)

Definition bioUR : ucmra := authUR (gmapUR nat (prodR fracR positiveR)).

(* the finite reference-slot supply that bounds every count (FdSlots.v's
   conservation recipe, private to the bio layer).  1024 is comfortable --
   the honest bound is a handful of references per process plus the log's
   pinned blocks -- and far below 2^31. *)
Definition BSLOTS : nat := 1024%nat.
Definition bioslotUR : ucmra := authUR natUR.

Class bioG (Σ : gFunctors) := BioG {
  bio_inG :: inG Σ bioUR;
  bioslot_inG :: inG Σ bioslotUR;
}.
Definition bioΣ : gFunctors := #[GFunctor bioUR; GFunctor bioslotUR].
Global Instance subG_bioΣ {Σ} : subG bioΣ Σ -> bioG Σ.
Proof. solve_inG. Qed.

(* every ghost name of the layer, as one record (uart_names precedent):
   the bcache spinlock's gname, the count authority, the slot supply, and
   per buffer the inner-sleeplock pair (γl, γsl) and the checkout token's
   gname. *)
Record bio_names := MkBioNames {
  bn_lk   : gname;                (* the "bcache" spinlock               *)
  bn_auth : gname;                (* ● (gmap nat (frac * positive))      *)
  bn_slot : gname;                (* the bslot supply                    *)
  bn_slk  : nat -> gname * gname; (* buffer k's sleeplock (γl, γsl)      *)
  bn_own  : nat -> gname;         (* buffer k's checkout token           *)
}.

(* the count component's [⋅] IS [Pos.add] (FileInv.pos_op_add, restated so
   this file does not pull the whole file table in). *)
Local Lemma pos_op_add (a b : positive) : (a ⋅ b) = (a + b)%positive.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  The four count-authority updates, as pure algebra                    *)
(* ------------------------------------------------------------------ *)

(* Stated at [bioUR] and proved OUTSIDE the Iris section, so that every
   [own_update] below is handed a CLOSED update.  This is not cosmetic: an
   [iMod (own_update with "Ha") as "[Ha Hf]"] leaves the target as an evar,
   and [apply auth_update_alloc] against an evar-headed target does not come
   back (it looks exactly like a hang -- durable-notes' "a failing/searching
   tactic looks like a hang"). *)

(* refcnt==0 -> refcnt:=1: allocate the entry, minting the first reference
   at fraction qn (split off the resource's retained share). *)
Local Lemma bio_first_upd (M : gmap nat (Qp * positive)) (k : nat) (qn : Qp) :
  M !! k = None ->
  ✓ qn ->
  (● M : bioUR) ~~> ● (<[k := (qn, 1%positive)]> M) ⋅ ◯ {[ k := (qn, 1%positive) ]}.
Proof.
  intros HM Hq. apply auth_update_alloc.
  apply (alloc_singleton_local_update _ k (qn, 1%positive)); [done|].
  split; [exact Hq | done].
Qed.

(* refcnt++ on a busy buffer.  Unlike filedup nothing comes from a caller's
   fragment: the entry GROWS by exactly the minted [(qn,1)], so the update is
   an allocation keyed pointwise rather than a [singleton_local_update]. *)
Local Lemma bio_incr_lu (M : gmap nat (Qp * positive)) (k : nat)
    (qt qn : Qp) (n : positive) :
  M !! k = Some (qt, n) ->
  ✓ (qt + qn)%Qp ->
  @local_update _ (gmapUR nat (prodR fracR positiveR))
    (M, ∅) (<[k := ((qt + qn)%Qp, Pos.succ n)]> M, {[ k := (qn, 1%positive) ]}).
Proof.
  intros HM Hq.
  apply gmap_local_update. intros i.
  destruct (decide (i = k)) as [->|Hne]; last first.
  { rewrite lookup_insert_ne // lookup_singleton_ne //. }
  rewrite lookup_insert lookup_singleton lookup_empty HM.
  apply local_update_unital_discrete. intros z Hv Hz.
  rewrite left_id in Hz. rewrite -Hz.
  split.
  { apply Some_valid. split; cbn; [exact Hq | done]. }
  rewrite -Some_op -pair_op frac_op pos_op_add.
  by rewrite (Qp.add_comm qn qt) Pos.add_1_l.
Qed.

Local Lemma bio_incr_upd (M : gmap nat (Qp * positive)) (k : nat)
    (qt qn : Qp) (n : positive) :
  M !! k = Some (qt, n) ->
  ✓ (qt + qn)%Qp ->
  (● M : bioUR) ~~>
  ● (<[k := ((qt + qn)%Qp, Pos.succ n)]> M) ⋅ ◯ {[ k := (qn, 1%positive) ]}.
Proof. intros HM Hq. apply auth_update_alloc. by apply bio_incr_lu. Qed.

(* refcnt-- with survivors: the departing reference's fraction returns to the
   outstanding total (FileInv.file_close_step's algebra, verbatim). *)
Local Lemma bio_decr_upd (M : gmap nat (Qp * positive)) (k : nat)
    (q qt qr : Qp) (n : positive) :
  M !! k = Some (qt, Pos.succ n) ->
  (qt - q)%Qp = Some qr ->
  (● M : bioUR) ⋅ ◯ {[ k := (q, 1%positive) ]} ~~> ● (<[k := (qr, n)]> M).
Proof.
  intros HM Hsub.
  apply Qp.sub_Some in Hsub.       (* qt = q + qr *)
  apply auth_update_dealloc, gmap_local_update. intros i.
  destruct (decide (i = k)) as [->|Hne]; last first.
  { (* untouched slot: the fragment is absent on both sides *)
    assert (Hki : k <> i) by auto.
    pose proof (lookup_singleton_ne (M:=gmap nat) k i (q, 1%positive) Hki) as Hs.
    pose proof (lookup_insert_ne M k i (qr, n) Hki) as Hm.
    apply local_update_discrete. intros mz Hv Hz.
    rewrite Hs in Hz. rewrite Hm. split; [exact Hv | exact Hz]. }
  pose proof (lookup_singleton (M:=gmap nat) k (q, 1%positive)) as Hs.
  pose proof (lookup_insert M k (qr, n)) as Hm.
  apply local_update_discrete. intros mz Hv Hz.
  rewrite HM in Hz, Hv. rewrite Hs in Hz. rewrite Hm.
  (* the frame is an [option] of the ENTRY, so three shapes *)
  destruct mz as [[[qf nf]|]|]; simpl in Hz.
  - (* a real frame -- it is exactly what the entry shrinks to *)
    apply Some_equiv_inj in Hz. destruct Hz as [Hq Hn]; simpl in Hq, Hn.
    rewrite pos_op_add in Hn.
    assert (Hn' : Pos.succ n = (1 + nf)%positive) by exact Hn.
    assert (Hnf : nf = n) by lia.
    rewrite frac_op in Hq.
    assert (Hqf : qf = qr).
    { apply (inj (Qp.add q)). by rewrite -Hq -Hsub. }
    subst nf qf. split; last first.
    { by constructor. }
    destruct Hv as [Hvq _]; simpl in Hvq. apply frac_valid in Hvq.
    split; simpl; [|done].
    apply frac_valid. etrans; [|exact Hvq]. rewrite Hsub. apply Qp.le_add_r.
  - (* empty frame: the entry would have to BE (q,1), i.e. Pos.succ n = 1 *)
    exfalso. rewrite right_id in Hz. apply Some_equiv_inj in Hz.
    destruct Hz as [_ Hn]; simpl in Hn.
    assert (Hn' : Pos.succ n = 1%positive) by exact Hn. lia.
  - (* no frame: same contradiction *)
    exfalso. apply Some_equiv_inj in Hz.
    destruct Hz as [_ Hn]; simpl in Hn.
    assert (Hn' : Pos.succ n = 1%positive) by exact Hn. lia.
Qed.

(* the last refcnt--: [(q,1)] is not EXCLUSIVE (q may be a share), but it is
   cancelable and the entry is exactly the fragment -- a frame would push the
   COUNT past 1 -- so the whole entry goes away. *)
Local Lemma bio_last_upd (M : gmap nat (Qp * positive)) (k : nat) (q : Qp) :
  M !! k = Some (q, 1%positive) ->
  (● M : bioUR) ⋅ ◯ {[ k := (q, 1%positive) ]} ~~> ● (delete k M).
Proof.
  intros HM. apply auth_update_dealloc.
  apply delete_singleton_local_update_cancelable; [apply _ | by rewrite HM].
Qed.

Section BioInv.
  Context `{!riscvGS Σ, !lockG Σ, !bioG Σ}.

  (* full ownership of a 4-byte cell is exclusive: the escrow's park swap
     refutes the parked arm with the full valid cell in hand. *)
  Lemma word4_pointsto_excl (a : Arch.pa) (w1 w2 : bv 32) (dq : dfrac) :
    a ↦₄ w1 -∗ a ↦₄{dq} w2 -∗ False.
  Proof.
    iIntros "H1 H2".
    iDestruct (word4_pointsto_bytes with "H1") as "H1".
    iDestruct (word4_pointsto_bytes with "H2") as "H2".
    cbn [seq].
    iDestruct "H1" as "[Hb1 _]". iDestruct "H2" as "[Hb2 _]".
    iDestruct (mem_pointsto_ne with "Hb1 Hb2") as %Hne. done.
  Qed.

  (* ---- the slot supply ---- *)
  Definition bslots (bn : bio_names) (n : nat) : iProp Σ :=
    own (bn_slot bn) (◯ n).
  Definition bslot (bn : bio_names) : iProp Σ := bslots bn 1.
  Definition bslots_auth (bn : bio_names) : iProp Σ :=
    own (bn_slot bn) (● BSLOTS).

  Lemma bslots_op (bn : bio_names) a b :
    bslots bn (a + b) ⊣⊢ bslots bn a ∗ bslots bn b.
  Proof.
    rewrite /bslots.
    assert (Hop : (◯ (a + b)%nat : bioslotUR) = ◯ a ⋅ ◯ b)
      by (rewrite -auth_frag_op; reflexivity).
    rewrite Hop own_op. reflexivity.
  Qed.

  Lemma bslots_bound (bn : bio_names) n :
    bslots_auth bn -∗ bslots bn n -∗ ⌜(n <= BSLOTS)%nat⌝.
  Proof.
    rewrite /bslots_auth /bslots. iIntros "Ha Hf".
    iDestruct (own_valid_2 with "Ha Hf") as %[Hincl _]%auth_both_valid_discrete.
    iPureIntro. by apply nat_included in Hincl.
  Qed.

  (* the consequence every increment needs: a slot-backed count is far below
     what an int can hold (fd_slots_no_overflow's mirror). *)
  Lemma bslots_no_overflow (bn : bio_names) (n : positive) :
    bslots_auth bn -∗ bslots bn (Pos.to_nat n) -∗
    ⌜(Z.pos n < 2 ^ 31)%Z /\ (Z.pos (Pos.succ n) < 2 ^ 31)%Z⌝.
  Proof.
    iIntros "Ha Hf".
    iDestruct (bslots_bound with "Ha Hf") as %Hle.
    iPureIntro.
    assert (E31 : (2 ^ 31 = 2147483648)%Z) by (vm_compute; reflexivity).
    assert (EB : BSLOTS = 1024%nat) by (vm_compute; reflexivity).
    rewrite EB in Hle.
    assert (Hz : (Z.pos n <= 1024)%Z) by (rewrite -positive_nat_Z; lia).
    rewrite E31. lia.
  Qed.

  (* ---- one reference ----

     The unit of ownership for a buffer user: the count fragment plus a REAL
     fraction of the dev/blockno cells, so holders agree on the key with no
     extra ghost (FileInv's file_ref shape).  bpin's clients hold one; a
     bread..brelse chain's reference rides inside the escrow instead. *)
  Definition bref_tok (bn : bio_names) (k : nat) (q : Qp) : iProp Σ :=
    own (bn_auth bn) (◯ {[ k := (q, 1%positive) ]}).

  Definition bref (bn : bio_names) (k : nat) (q : Qp)
      (dev bno : mword 32) : iProp Σ :=
    (bref_tok bn k q ∗
     b_dev (bpa k) ↦₄{DfracOwn q} dev ∗
     b_blockno (bpa k) ↦₄{DfracOwn q} bno)%I.

  (* ---- the checkout token: the buffer sleeplock's WHOLE resource ---- *)
  Definition bown (bn : bio_names) (k : nat) : iProp Σ :=
    lock_tok_excl (bn_own bn k).

  Lemma bown_exclusive bn k : bown bn k -∗ bown bn k -∗ False.
  Proof. apply lock_tok_excl_exclusive. Qed.

  (* ------------------------------------------------------------------ *)
  (*  The escrow                                                          *)
  (* ------------------------------------------------------------------ *)

  Definition bioN : namespace := nroot .@ "xv6bio".

  (* A1: the buffer's traveling content, parked.  disk is pinned 0 -- only
     rw flips it, and always back before returning; the valid word is pinned
     to {0,1} -- the only writers are the miss path (0), bread's tail (1) and
     [bio_init] (0), and that pin is what turns bread's hit-path branch fact
     ("nonzero") into the [= 1] its postcondition states. *)
  Definition buf_parked (k : nat) : iProp Σ :=
    (∃ (vld dev bno : mword 32) (bs : list (bv 8)),
       ⌜vld = (mword_of_int 0 : mword 32) \/ vld = (mword_of_int 1 : mword 32)⌝ ∗
       b_valid (bpa k) ↦₄ vld ∗
       b_dev (bpa k) ↦₄{DfracOwn (1/2)} dev ∗
       buf_own (bpa k) bno (mword_of_int 0 : mword 32) bs)%I.

  (* A2: checked out by a sleeplock chain; the chain's own reference and the
     checkout token wait here until brelse brings the content back. *)
  Definition buf_chain (bn : bio_names) (k : nat) : iProp Σ :=
    (∃ (q : Qp) (dev bno : mword 32),
       bref_tok bn k q ∗
       b_dev (bpa k) ↦₄{DfracOwn q} dev ∗
       b_blockno (bpa k) ↦₄{DfracOwn q} bno ∗
       bown bn k)%I.

  Definition buf_escrow_body (bn : bio_names) (k : nat) : iProp Σ :=
    (buf_parked k ∨ buf_chain bn k)%I.

  Definition buf_escrow (bn : bio_names) (k : nat) : iProp Σ :=
    inv bioN (buf_escrow_body bn k).

  (* ---- the three swaps (used inside an [iInv] open of [buf_escrow]) ---- *)

  (* (a) checkout, post-acquiresleep: the opener's bown refutes A2; its
     reference's cell fractions AGREE with the parked bundle's, pinning the
     withdrawn dev/bno to the requested key. *)
  Lemma escrow_swap_checkout bn k q (dev bno : mword 32) :
    buf_escrow_body bn k -∗
    bown bn k -∗
    bref_tok bn k q -∗
    b_dev (bpa k) ↦₄{DfracOwn q} dev -∗
    b_blockno (bpa k) ↦₄{DfracOwn q} bno -∗
    buf_escrow_body bn k ∗
    (∃ (vld : mword 32) (bs : list (bv 8)),
       ⌜vld = (mword_of_int 0 : mword 32) \/ vld = (mword_of_int 1 : mword 32)⌝ ∗
       b_valid (bpa k) ↦₄ vld ∗
       b_dev (bpa k) ↦₄{DfracOwn (1/2)} dev ∗
       buf_own (bpa k) bno (mword_of_int 0 : mword 32) bs).
  Proof.
    iIntros "Hbody Hown Htok Hdev Hbno".
    iDestruct "Hbody" as "[Hparked | Hchain]"; last first.
    { iDestruct "Hchain" as (q' dev' bno') "(_ & _ & _ & Hown')".
      iExFalso. iApply (bown_exclusive with "Hown Hown'"). }
    iDestruct "Hparked" as (vld dev' bno' bs) "(%Hpin & Hvld & Hdev' & Hbuf)".
    iDestruct (word4_pointsto_agree with "Hdev Hdev'") as %Heqd. subst dev'.
    rewrite /buf_own.
    iDestruct "Hbuf" as "(Hbno' & Hdisk & %Hlen & Hdata)".
    iDestruct (word4_pointsto_agree with "Hbno Hbno'") as %Heqb. subst bno'.
    iSplitL "Htok Hdev Hbno Hown".
    { iRight. rewrite /buf_chain. iExists q, dev, bno. iFrame. }
    iExists vld, bs. iSplitR; [by iPureIntro|]. iFrame "Hvld Hdev'".
    rewrite /buf_own. iFrame "Hbno' Hdisk Hdata". done.
  Qed.

  (* (b) park, brelse's first instruction: the opener's full valid cell
     refutes A1 (fraction 1 + 1 is invalid); the chain's reference and bown
     come back out.  The withdrawn fractions agree with the deposited
     bundle's, so the recovered reference is at the SAME key. *)
  Lemma escrow_swap_park bn k (vld dev bno : mword 32) (bs : list (bv 8)) :
    vld = (mword_of_int 0 : mword 32) \/ vld = (mword_of_int 1 : mword 32) ->
    buf_escrow_body bn k -∗
    b_valid (bpa k) ↦₄ vld -∗
    b_dev (bpa k) ↦₄{DfracOwn (1/2)} dev -∗
    buf_own (bpa k) bno (mword_of_int 0 : mword 32) bs -∗
    buf_escrow_body bn k ∗
    (∃ q : Qp,
       bref_tok bn k q ∗
       b_dev (bpa k) ↦₄{DfracOwn q} dev ∗
       b_blockno (bpa k) ↦₄{DfracOwn q} bno ∗
       bown bn k).
  Proof.
    iIntros (Hpin) "Hbody Hvld Hdev Hbuf".
    iDestruct "Hbody" as "[Hparked | Hchain]".
    { iDestruct "Hparked" as (vld' dev' bno' bs') "(_ & Hvld' & _ & _)".
      iExFalso. iApply (word4_pointsto_excl with "Hvld Hvld'"). }
    iDestruct "Hchain" as (q dev' bno') "(Htok & Hdev' & Hbno' & Hown)".
    iDestruct (word4_pointsto_agree with "Hdev Hdev'") as %Heqd. subst dev'.
    rewrite /buf_own.
    iDestruct "Hbuf" as "(Hbno & Hdisk & %Hlen & Hdata)".
    iDestruct (word4_pointsto_agree with "Hbno' Hbno") as %Heqb. subst bno'.
    iSplitR "Htok Hdev' Hbno' Hown".
    { iLeft. rewrite /buf_parked. iExists vld, dev, bno, bs.
      iSplitR; [by iPureIntro|].
      iFrame "Hvld Hdev". rewrite /buf_own. iFrame "Hbno Hdisk Hdata". done. }
    iExists q. iFrame.
  Qed.

  (* (c) the miss path's view: with the authority showing no references,
     A2 is impossible, so the body IS the parked bundle. *)
  Lemma escrow_open_free bn k (M : gmap nat (Qp * positive)) :
    M !! k = None ->
    own (bn_auth bn) (● M) -∗
    buf_escrow_body bn k -∗
    own (bn_auth bn) (● M) ∗ buf_parked k ∗
    (buf_parked k -∗ buf_escrow_body bn k).
  Proof.
    iIntros (HM) "Ha Hbody".
    iDestruct "Hbody" as "[Hparked | Hchain]"; last first.
    { iDestruct "Hchain" as (q dev bno) "(Htok & _)".
      rewrite /bref_tok.
      iDestruct (own_valid_2 with "Ha Htok")
        as %[Hincl _]%auth_both_valid_discrete.
      iExFalso. iPureIntro.
      apply singleton_included_l in Hincl as [y [Hy _]].
      rewrite HM in Hy. inversion Hy. }
    iFrame "Ha Hparked". iIntros "Hp". by iLeft.
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  The count authority: lookups and the three ghost steps              *)
  (* ------------------------------------------------------------------ *)

  (* a reference against the authority (fref_tok_lookup's mirror): the entry
     exists, and the sole reference holds the whole outstanding fraction. *)
  Lemma bref_tok_lookup bn M k q :
    own (bn_auth bn) (● M) -∗ bref_tok bn k q -∗
    ⌜∃ qt n, M !! k = Some (qt, n) /\
       (n = 1%positive -> q = qt) /\ (q = qt -> n = 1%positive)⌝.
  Proof.
    rewrite /bref_tok. iIntros "Ha Hf".
    iDestruct (own_valid_2 with "Ha Hf") as %[Hincl _]%auth_both_valid_discrete.
    iPureIntro.
    apply singleton_included_l in Hincl as [y [Hy Hle]].
    apply leibniz_equiv in Hy. destruct y as [qt n]. exists qt, n.
    split; [exact Hy|].
    apply Some_included in Hle as [Heq | Hlt].
    - destruct Heq as [Hq Hn]; cbn in Hq, Hn.
      split; intros _; [exact Hq | by rewrite -Hn].
    - apply pair_included in Hlt as [Hq Hn]; cbn in Hq, Hn.
      apply frac_included in Hq. apply pos_included in Hn.
      split; intros Hc.
      + exfalso. rewrite Hc in Hn. lia.
      + exfalso. rewrite Hc in Hq. by apply (irreflexivity Qp.lt qt).
  Qed.

  (* refcnt==0 -> refcnt:=1: allocate the entry, minting the first reference
     with fraction qn split off the resource's retained share (the caller
     performs the physical cell split alongside). *)
  Lemma bio_first_ref_step bn M k (qn : Qp) :
    M !! k = None ->
    ✓ qn ->
    own (bn_auth bn) (● M) ==∗
    own (bn_auth bn) (● (<[k := (qn, 1%positive)]> M)) ∗ bref_tok bn k qn.
  Proof.
    iIntros (HM Hqn) "Ha". rewrite /bref_tok.
    iMod (own_update _ _ _ (bio_first_upd M k qn HM Hqn) with "Ha") as "[$ $]".
    done.
  Qed.

  (* refcnt++ on a busy buffer: mint a fresh reference at fraction qn taken
     from the RETAINED share (the incrementer -- bpin, or bget's hit path --
     may hold no reference of its own, so unlike filedup nothing comes from
     a caller's fragment: the entry grows by exactly the minted amount). *)
  Lemma bio_incr_step bn M k qt (n : positive) (qn : Qp) :
    M !! k = Some (qt, n) ->
    ✓ (qt + qn)%Qp ->
    own (bn_auth bn) (● M) ==∗
    own (bn_auth bn) (● (<[k := ((qt + qn)%Qp, Pos.succ n)]> M)) ∗
    bref_tok bn k qn.
  Proof.
    iIntros (HM Hq) "Ha". rewrite /bref_tok.
    iMod (own_update _ _ _ (bio_incr_upd M k qt qn n HM Hq) with "Ha")
      as "[$ $]".
    done.
  Qed.

  (* refcnt-- with survivors: the departing reference's fraction returns to
     the outstanding total (file_close_step's mirror). *)
  Lemma bio_decr_step bn M k q qt (n : positive) (qr : Qp) :
    M !! k = Some (qt, Pos.succ n) ->
    (qt - q)%Qp = Some qr ->
    own (bn_auth bn) (● M) -∗ bref_tok bn k q ==∗
    own (bn_auth bn) (● (<[k := (qr, n)]> M)).
  Proof.
    iIntros (HM Hsub) "Ha Hf". rewrite /bref_tok.
    iMod (own_update_2 _ _ _ _ (bio_decr_upd M k q qt qr n HM Hsub)
           with "Ha Hf") as "$".
    done.
  Qed.

  (* the last refcnt--: the entry disappears; the sole reference held the
     whole fraction (bref_tok_lookup), so the resource's retained share is
     whole again (file_close_last_step's mirror). *)
  Lemma bio_last_ref_step bn M k q :
    M !! k = Some (q, 1%positive) ->
    own (bn_auth bn) (● M) -∗ bref_tok bn k q ==∗
    own (bn_auth bn) (● (delete k M)).
  Proof.
    iIntros (HM) "Ha Hf". rewrite /bref_tok.
    iMod (own_update_2 _ _ _ _ (bio_last_upd M k q HM) with "Ha Hf") as "$".
    done.
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  The bcache lock's resource                                          *)
  (* ------------------------------------------------------------------ *)

  (* the refcnt word each state stores (0 on a free slot, the count else) *)
  Definition brc_word (o : option (Qp * positive)) : mword 32 :=
    match o with
    | None => (mword_of_int 0 : mword 32)
    | Some (_, n) => (mword_of_int (Z.pos n) : mword 32)
    end.

  (* one buffer's bcache-side state: the refcnt cell, and whatever fraction
     of dev/blockno has not been handed to references -- all of the bcache
     half (1/2) when free, the retainder qr (with q + qr = 1/2) when busy,
     plus one absorbed [bslot] per outstanding reference and the faithful-int
     bound the word ties need. *)
  Definition bio_slot_res (bn : bio_names) (M : gmap nat (Qp * positive))
      (k : nat) (dev bno : mword 32) : iProp Σ :=
    match M !! k with
    | None =>
        (brefcnt k ↦₄ (mword_of_int 0 : mword 32) ∗
         b_dev (bpa k) ↦₄{DfracOwn (1/2)} dev ∗
         b_blockno (bpa k) ↦₄{DfracOwn (1/2)} bno)%I
    | Some (q, n) =>
        (⌜(Z.pos n < 2 ^ 31)%Z⌝ ∗
         brefcnt k ↦₄ (mword_of_int (Z.pos n) : mword 32) ∗
         bslots bn (Pos.to_nat n) ∗
         ∃ qr : Qp, ⌜(q + qr)%Qp = (1/2)%Qp⌝ ∗
           b_dev (bpa k) ↦₄{DfracOwn qr} dev ∗
           b_blockno (bpa k) ↦₄{DfracOwn qr} bno)%I
    end.

  Definition bcache_res (bn : bio_names) : iProp Σ :=
    (∃ (M : gmap nat (Qp * positive)) (ord : list nat)
       (devs bnos : nat -> mword 32),
       own (bn_auth bn) (● M) ∗
       bslots_auth bn ∗
       ⌜∀ k, is_Some (M !! k) -> (k < NBUF)%nat⌝ ∗
       ⌜ord ≡ₚ seq 0 NBUF⌝ ∗
       bcache_lru bhead (map bnode ord) ∗
       [∗ list] k ∈ seq 0 NBUF, bio_slot_res bn M k (devs k) (bnos k))%I.

  (* borrow one buffer's slot out of the big-sep and put it back, possibly
     under a different authority map (ftable_slots_acc's mirror). *)
  Lemma bio_slots_acc (bn : bio_names) (M : gmap nat (Qp * positive))
      (devs bnos : nat -> mword 32) (i : nat) :
    (i < NBUF)%nat ->
    ([∗ list] k ∈ seq 0 NBUF, bio_slot_res bn M k (devs k) (bnos k)) -∗
    bio_slot_res bn M i (devs i) (bnos i) ∗
    (∀ (M' : gmap nat (Qp * positive)) (devs' bnos' : nat -> mword 32),
       ⌜∀ k, k ≠ i -> M' !! k = M !! k /\ devs' k = devs k /\
             bnos' k = bnos k⌝ -∗
       bio_slot_res bn M' i (devs' i) (bnos' i) -∗
       [∗ list] k ∈ seq 0 NBUF, bio_slot_res bn M' k (devs' k) (bnos' k)).
  Proof.
    iIntros (Hi) "H".
    assert (Hlk : seq 0 NBUF !! i = Some i) by (apply lookup_seq; lia).
    rewrite (big_sepL_delete
               (fun _ k => bio_slot_res bn M k (devs k) (bnos k))
               (seq 0 NBUF) i i Hlk).
    iDestruct "H" as "[$ Hrest]".
    iIntros (M' devs' bnos' HM') "Hi".
    rewrite (big_sepL_delete
               (fun _ k => bio_slot_res bn M' k (devs' k) (bnos' k))
               (seq 0 NBUF) i i Hlk).
    iFrame "Hi".
    iApply (big_sepL_mono with "Hrest").
    intros idx y Hy. destruct (decide (idx = i)) as [->|Hne]; [done|].
    apply lookup_seq in Hy as [-> _].
    destruct (HM' _ Hne) as (HMk & Hdk & Hbk).
    unfold bio_slot_res. rewrite HMk Hdk Hbk. done.
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  The persistent context and the caller-facing handle                 *)
  (* ------------------------------------------------------------------ *)

  Definition bio_ctx (bn : bio_names) : iProp Σ :=
    (is_lock (bn_lk bn) bcache_addr "bcache"%string (bcache_res bn) ∗
     [∗ list] k ∈ seq 0 NBUF,
       (is_sleeplock (fst (bn_slk bn k)) (snd (bn_slk bn k))
          (buf_lock (bnode k)) "buffer"%string (bown bn k) ∗
        buf_escrow bn k))%I.

  Global Instance bio_ctx_persistent bn : Persistent (bio_ctx bn).
  Proof. apply _. Qed.

  Lemma bio_ctx_lock bn :
    bio_ctx bn -∗ is_lock (bn_lk bn) bcache_addr "bcache"%string (bcache_res bn).
  Proof. iIntros "[$ _]". Qed.

  Lemma bio_ctx_buf bn k :
    (k < NBUF)%nat ->
    bio_ctx bn -∗
    is_sleeplock (fst (bn_slk bn k)) (snd (bn_slk bn k))
      (buf_lock (bnode k)) "buffer"%string (bown bn k) ∗
    buf_escrow bn k.
  Proof.
    iIntros (Hk) "[_ Hbufs]".
    assert (Hlk : seq 0 NBUF !! k = Some k) by (apply lookup_seq; lia).
    iDestruct (big_sepL_lookup with "Hbufs") as "[$ $]"; [exact Hlk].
  Qed.

  (* the locked-buffer handle bread returns and bwrite/brelse consume: the
     sleeplock holder's bundle plus the traveling content, at valid=1 and
     disk=0.  The chain's reference is NOT here -- it rides in the escrow. *)
  Definition bio_locked (bn : bio_names) (k : nat)
      (pidv dev bno : mword 32) (bs : list (bv 8)) : iProp Σ :=
    (⌜(k < NBUF)%nat⌝ ∗
     sleeplocked (snd (bn_slk bn k)) ∗
     sl_pid (buf_lock (bnode k)) ↦₄ pidv ∗
     b_valid (bpa k) ↦₄ (mword_of_int 1 : mword 32) ∗
     b_dev (bpa k) ↦₄{DfracOwn (1/2)} dev ∗
     buf_own (bpa k) bno (mword_of_int 0 : mword 32) bs)%I.

  (* ------------------------------------------------------------------ *)
  (*  Construction: binit's postcondition + the .bss-zeroed buffers       *)
  (* ------------------------------------------------------------------ *)

  Local Lemma bio_seq_cons (j n : nat) : seq j (S n) = j :: seq (S j) n.
  Proof. reflexivity. Qed.

  (* the split every buffer's dev/blockno cell undergoes exactly once: one
     half into the escrow's parked bundle, one half into the bcache
     resource, forever. *)
  Local Lemma word4_half_split (a : Arch.pa) (w : bv 32) :
    a ↦₄ w -∗ a ↦₄{DfracOwn (1/2)} w ∗ a ↦₄{DfracOwn (1/2)} w.
  Proof. iIntros "H". rewrite -word4_pointsto_frac_split Qp.div_2. iFrame. Qed.

  (* GNAMES BEFORE THE RECORD.  [bio_names] cannot be built until all of the
     per-buffer gnames exist, and [bown bn k] -- the resource the sleeplocks
     seal -- mentions [bn].  The way out: allocate the CHECKOUT TOKENS first
     (their gnames are just a [nat -> gname] function, no record needed), then
     the sleeplocks over [lock_tok_excl (f k)], collecting THEIR gname pairs
     into a second function; [bn] is assembled from the two functions at the
     end, and [bown bn k] is [lock_tok_excl (f k)] by construction.
     These two lemmas are the collectors. *)
  Local Lemma tok_fun_alloc (n j : nat) :
    ⊢ |==> ∃ f : nat -> gname, [∗ list] k ∈ seq j n, lock_tok_excl (f k).
  Proof.
    iInduction n as [|n IH] forall (j).
    { iModIntro. iExists (fun _ => inhabitant). cbn [seq]. done. }
    iMod lock_tok_excl_alloc as (γ) "Hg".
    iMod ("IH" $! (S j)) as (f) "Hf".
    iModIntro. iExists (fun k => if decide (k = j) then γ else f k).
    rewrite bio_seq_cons. iSplitL "Hg".
    { case_decide as Hd; [iExact "Hg" | congruence]. }
    iApply (big_sepL_mono with "Hf"). intros i k Hk.
    apply lookup_seq in Hk as [-> _].
    case_decide as Hd; [exfalso; lia | done].
  Qed.

  Local Lemma seq_fun_alloc {A : Type} `{Inhabited A} (E : coPset)
      (Q : nat -> A -> iProp Σ) (n j : nat) :
    ([∗ list] k ∈ seq j n, |={E}=> ∃ x : A, Q k x) ={E}=∗
    ∃ f : nat -> A, [∗ list] k ∈ seq j n, Q k (f k).
  Proof.
    iInduction n as [|n IH] forall (j).
    { iIntros "_". iModIntro. iExists (fun _ => inhabitant). cbn [seq]. done. }
    rewrite bio_seq_cons. iIntros "[Hh Ht]".
    iMod "Hh" as (x) "Hx". iMod ("IH" with "Ht") as (f) "Hf".
    iModIntro. iExists (fun k => if decide (k = j) then x else f k).
    iSplitL "Hx".
    { case_decide as Hd; [iExact "Hx" | congruence]. }
    iApply (big_sepL_mono with "Hf"). intros i k Hk.
    apply lookup_seq in Hk as [-> _].
    case_decide as Hd; [exfalso; lia | done].
  Qed.

  (* The caller-side ghost step over binit's postcondition (SpecBinit.v) plus
     the .bss-zeroed [struct buf] cells: seal the bcache spinlock over
     [bcache_res], seal every buffer's sleeplock over its checkout token,
     park every buffer's content in a fresh escrow, and hand the caller the
     whole [bslot] supply.  Everything starts at refcnt 0 / valid 0, so the
     authority map is empty and the LRU list is binit's [blist 0 NBUF]. *)
  Lemma bio_init E :
    bcache_addr ↦₄ (mword_of_int 0 : mword 32) -∗
    lock_name bcache_addr "bcache"%string -∗
    add_vec bcache_addr (sign_extend' 64 (mword_of_int 16 : mword 12)) ↦₈
      (zero_reg : mword 64) -∗
    ([∗ list] k ∈ seq 0 NBUF, sl_fresh (buf_lock (bnode k)) "buffer"%string) -∗
    ([∗ list] k ∈ seq 0 NBUF,
       b_valid (bpa k) ↦₄ (mword_of_int 0 : mword 32) ∗
       b_disk (bpa k) ↦₄ (mword_of_int 0 : mword 32) ∗
       b_dev (bpa k) ↦₄ (mword_of_int 0 : mword 32) ∗
       b_blockno (bpa k) ↦₄ (mword_of_int 0 : mword 32) ∗
       brefcnt k ↦₄ (mword_of_int 0 : mword 32) ∗
       (∃ bs : list (bv 8), ⌜length bs = 1024%nat⌝ ∗
          [∗ list] j ↦ byte ∈ bs, pa_add (b_data (bpa k)) j ↦ₘ byte)) -∗
    bcache_lru bhead (blist 0 NBUF) ={E}=∗
    ∃ bn : bio_names, bio_ctx bn ∗ bslots bn BSLOTS.
  Proof.
    iIntros "Hlkw #Hnm Hcpu Hfresh Hbufs Hlru".
    (* the NBUF checkout tokens, as a function *)
    iMod (tok_fun_alloc NBUF 0) as (fown) "Htoks".
    (* the count authority (no buffer has a reference) and the slot supply *)
    iMod (own_alloc (● (∅ : gmap nat (Qp * positive)) : bioUR)) as (γb) "Hauth".
    { apply auth_auth_valid. intros i. rewrite lookup_empty. done. }
    iMod (own_alloc ((● BSLOTS ⋅ ◯ BSLOTS) : bioslotUR)) as (γs) "[Hsa Hsf]".
    { apply auth_both_valid_discrete. split; [done | done]. }
    (* the bcache spinlock's gname, BEFORE its resource can be stated *)
    iMod (newlock_delayed E bcache_addr "bcache"%string with "Hnm Hlkw Hcpu")
      as (γlk) "Hmk".
    (* every buffer's sleeplock, sealing exactly its checkout token *)
    iDestruct (big_sepL_sep_2 with "Hfresh Htoks") as "Hsl".
    iAssert ([∗ list] k ∈ seq 0 NBUF, |={E}=> ∃ p : gname * gname,
               is_sleeplock (fst p) (snd p) (buf_lock (bnode k))
                 "buffer"%string (lock_tok_excl (fown k)))%I
      with "[Hsl]" as "Hsl".
    { iApply (big_sepL_mono with "Hsl"). intros i k Hk.
      iIntros "[Hf Ht]".
      iMod (sl_fresh_new E (buf_lock (bnode k)) "buffer"%string
              (lock_tok_excl (fown k)) with "Hf Ht") as (γl γsl) "Hlk".
      iModIntro. iExists (γl, γsl). iExact "Hlk". }
    iMod (seq_fun_alloc E
            (fun k p => is_sleeplock (fst p) (snd p) (buf_lock (bnode k))
                          "buffer"%string (lock_tok_excl (fown k)))
            NBUF 0 with "Hsl") as (fslk) "#Hsls".
    set (bn := MkBioNames γlk γb γs fslk fown).
    (* park every buffer's content in a fresh escrow, keeping the bcache half
       of dev/blockno and the refcnt cell for [bcache_res] *)
    iAssert (([∗ list] k ∈ seq 0 NBUF, |={E}=> buf_escrow bn k) ∗
             ([∗ list] k ∈ seq 0 NBUF,
                bio_slot_res bn ∅ k (mword_of_int 0 : mword 32)
                  (mword_of_int 0 : mword 32)))%I
      with "[Hbufs]" as "[Hesc Hslots]".
    { rewrite -big_sepL_sep. iApply (big_sepL_mono with "Hbufs").
      intros i k Hk. iIntros "(Hv & Hdk & Hdev & Hbno & Hrc & Hdata)".
      iDestruct (word4_half_split with "Hdev") as "[Hdev1 Hdev2]".
      iDestruct (word4_half_split with "Hbno") as "[Hbno1 Hbno2]".
      iDestruct "Hdata" as (bs) "[%Hlen Hdata]".
      iSplitR "Hrc Hdev2 Hbno2".
      - rewrite /buf_escrow.
        iApply (inv_alloc bioN E (buf_escrow_body bn k)).
        iNext. iLeft. rewrite /buf_parked.
        iExists (mword_of_int 0 : mword 32), (mword_of_int 0 : mword 32),
                (mword_of_int 0 : mword 32), bs.
        iSplitR; [by iPureIntro; left|].
        iFrame "Hv Hdev1". rewrite /buf_own. iFrame "Hbno1 Hdk Hdata". done.
      - rewrite /bio_slot_res lookup_empty. iFrame "Hrc Hdev2 Hbno2". }
    iMod (big_sepL_fupd with "Hesc") as "#Hescs".
    (* and seal the bcache lock over the assembled resource *)
    iMod ("Hmk" $! (bcache_res bn) with "[Hauth Hsa Hslots Hlru]") as "#Hlock".
    { rewrite /bcache_res.
      iExists ∅, (rev (seq 0 NBUF)),
        (fun _ => (mword_of_int 0 : mword 32)),
        (fun _ => (mword_of_int 0 : mword 32)).
      iFrame "Hauth Hsa".
      iSplitR.
      { iPureIntro. intros k [x Hx]. rewrite lookup_empty in Hx. done. }
      iSplitR.
      { iPureIntro. symmetry. apply Permutation_rev. }
      assert (Hml : map bnode (rev (seq 0 NBUF)) = blist 0 NBUF)
        by (rewrite /blist map_rev //).
      rewrite Hml. iFrame "Hlru Hslots". }
    iModIntro. iExists bn. iFrame "Hsf". rewrite /bio_ctx. iFrame "Hlock".
    rewrite big_sepL_sep. iFrame "Hsls Hescs".
  Qed.

End BioInv.
