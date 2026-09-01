(* BioInv.v -- the bio.c ownership layer over the buffer cache: the
   reference-count algebra, the per-buffer content ESCROW, the bcache lock's
   resource (with the UNCACHED POOL), and the persistent [bio_ctx] every bio
   function shares.

   Design (claude-notes/design/fs-log.md; the physical base is
   claude-notes/completed/bio.md).  The two facts that force the escrow:

   (1) A releasing holder's content must be reachable from the sleeplock side
       BY THE END of releasesleep -- a blocked waiter's acquiresleep can
       return (and its caller touch b->valid / b->data) before the releaser's
       refcnt-- runs.
   (2) bget's miss path rewrites dev/blockno/valid under ONLY bcache.lock
       (at refcnt==0), and its scan reads every buffer's dev/blockno there --
       so those cells can be fully inside neither the sleeplock chain nor
       the bcache resource.

   So the traveling content lives in a per-buffer ESCROW -- a namespace
   invariant, openable atomically at any instruction.  The layer is
   PARAMETRIC over a client view [bio_view]: the covered device+block range,
   and two opaque per-block payloads [bv_clean]/[bv_dirty] ("bs is the
   block's logical content", clean = the disk home cell agrees, dirty = the
   block is pinned by a log reference).  Bio only MOVES the payloads --
   pool -> escrow -> handle and back -- and never converts clean <-> dirty;
   holders do that with their own (log-layer) ghosts.  Three arms:

     A1 (parked):      valid cell (full, keyed by a bool v) + dev (1/2) +
                       buf_own (blockno 1/2, disk pinned 0, the 1024 data
                       bytes) + the payload [buf_pay] (v = true: the bytes
                       ARE the logical content and the disk cell is carried
                       alongside; v = false: the block's pool bundle rides
                       here so that WHOEVER wins the fill race finds it) +
                       the recycle token [bmid].
     A2 (checked out): the chain's own reference fragment with its
                       dev/blockno fraction q, the checkout token [bown k],
                       and the recycle token.
     A3 (mid-recycle): the recycler's window between the blockno store and
                       the valid store, where the blockno cell already names
                       the NEW block but the valid cell is stale: cells only,
                       decoupled from any payload, with the dev cell FULL
                       (the bcache-retained half joined in).  The recycle
                       token is OUT (in the recycler's hand): that is what
                       lets the recycler refute A1/A2 when it closes the
                       window, while every other opener refutes A3 by a dev
                       or valid cell fraction.

   The buffer's sleeplock protects EXACTLY [bown k].  A checkout
   (post-acquiresleep) refutes A2 with the bown in hand and A3 with its
   reference's dev fraction, and swaps its ref + bown in for the parked
   bundle; a park (brelse's first instruction) refutes A1 and A3 with the
   full valid cell in hand and swaps back.  The miss path (refcnt==0,
   bcache.lock held) refutes A2 with the auth (M !! k = None vs the arm's
   fragment) and A3 with the bcache-retained dev half, and mutates the
   parked cells one atomic store at a time.  The dirty payload holds a real
   [bref], so the recycler's auth ALSO refutes "dirty" at eviction: only
   clean, disk-agreeing content ever returns to the pool.

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
From iris.algebra Require Import excl auth gmap frac numbers agree gmultiset.
From stdpp Require Import gmultiset.
From iris.base_logic.lib Require Import ghost_var.
From iris.base_logic.lib Require Import gen_heap invariants own.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes.
Require Import RiscvPtsto.
Require Import WpLock.
Require Import TsoCtx.   (* the lock payload's context axis; [<{ }>] *)
Require Import TsoMemPa TsoGhost.
Require Import TsoCtxPark.
Require Import CtxAnchor.
Require Import SleepLock.
Require Import BufOwn.
Require Import DiskPtsto.
Require Import BcacheInv.
Require Export BioDefs.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SepThread.   (* A6.68: the token threaded through the NBUF *)
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
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

(* A6.148: the per-slot PRESENCE authority.  [● None] sits in the box's
   IDLE arm at refs = 0; [● Some n] in bcache.lock's payload at refs >= 1;
   every buffer reference carries a [◯ Some 1] fragment beside [bref_tok].
   The checkout's fragment against [● None] is the IDLE refutation that no
   count fragment could provide (fragments compose; authorities clash). *)
(* ENDGAME §3.2: the presence element carries the LAST BUMP's
   (generation, stamp) pair as an agree beside the count, so a reference's
   fragment IS its freshness witness for the bump case. *)
(* [presR]/[presG] and [btagR]/[btagG] live in [Xv6Cameras] (section 15),
   bundled into [xv6G] through [bioboxG]. *)

Section BioInv.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ}.
  Context `{XI : CurCtx}.

  (* full ownership of a 4-byte cell is exclusive: the escrow's park swap
     refutes the parked arm with the full valid cell in hand. *)
  Lemma word4_pointsto_excl (a : Arch.pa) (w1 w2 : bv 32) (dq : dfrac) :
    a ↦₄ w1 -∗ a ↦₄{dq} w2 -∗ False.
  Proof.
    iIntros "H1 H2".
    (* M1 stage 2: [↦₄] is the ctx tower, so the laws gain a leading ξ *)
    iDestruct (ctx_word4_pointsto_bytes with "H1") as "H1".
    iDestruct (ctx_word4_pointsto_bytes with "H2") as "H2".
    cbn [seq].
    iDestruct "H1" as "[Hb1 _]". iDestruct "H2" as "[Hb2 _]".
    iDestruct (ctx_pointsto_ne with "Hb1 Hb2") as %Hne. done.
  Qed.

  (* ---- the slot supply lives in [BioDefs] now, at the CANONICAL ghost
     name: it has to be nameable from [ProcDefs.proc_dormant], which is
     below the file system.  This file re-exports BioDefs, so [bslot],
     [bslots_auth], [bslots_op], [bslots_bound] and [bslots_no_overflow]
     are still in scope for every consumer, minus their [bn] argument. ---- *)

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
     (* ENDGAME §3.2: the presence fragment plus the persistent llb of the
        bump stamp -- the reference IS the bump-case freshness witness. *)
     (∃ rb : nat * nat,
        own (bn_pres bn k) (◯ Some (to_agree rb, 1%positive)) ∗
        llb loglen_name rb.2) ∗
     b_dev (bpa k) ↦₄{DfracOwn q} dev ∗
     b_blockno (bpa k) ↦₄{DfracOwn q} bno)%I.

  Definition pres_none (bn : bio_names) (k : nat) : iProp Σ :=
    own (bn_pres bn k) (● None).
  Definition pres_auth (bn : bio_names) (k : nat) (rb : nat * nat)
      (c : positive) : iProp Σ :=
    own (bn_pres bn k) (● Some (to_agree rb, c)).
  Definition pres_frag (bn : bio_names) (k : nat) (rb : nat * nat) : iProp Σ :=
    own (bn_pres bn k) (◯ Some (to_agree rb, 1%positive)).

  Lemma pres_frag_none_absurd bn k rb :
    pres_frag bn k rb -∗ pres_none bn k -∗ False.
  Proof.
    iIntros "Hf Ha".
    iDestruct (own_valid_2 with "Ha Hf") as %Hv.
    apply auth_both_valid_discrete in Hv as [Hincl _].
    apply option_included in Hincl as [Hc | (a & b & Ha & Hb & _)];
      [discriminate | discriminate].
  Qed.

  Lemma pres_auth_auth_absurd bn k on1 on2 :
    own (bn_pres bn k) (● on1) -∗ own (bn_pres bn k) (● on2) -∗ False.
  Proof.
    iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as %Hv.
    by apply auth_auth_op_valid in Hv.
  Qed.

  (* a fragment agrees with the authority on the bump pair *)
  Lemma pres_frag_agree bn k rb rb' c :
    pres_auth bn k rb c -∗ pres_frag bn k rb' -∗ ⌜rb' = rb⌝.
  Proof.
    iIntros "Ha Hf".
    iDestruct (own_valid_2 with "Ha Hf") as %Hv.
    iPureIntro.
    apply auth_both_valid_discrete in Hv as [Hincl Hval].
    apply Some_included in Hincl as [Heq | Hlt].
    - destruct Heq as [Ha _]; cbn in Ha.
      apply (inj to_agree) in Ha. by fold_leibniz.
    - apply pair_included in Hlt as [Ha _]; cbn in Ha.
      apply to_agree_included in Ha. by fold_leibniz.
  Qed.

  (* IDLE -> one reference: pick the new bump pair *)
  Lemma pres_none_take bn k (rb : nat * nat) :
    pres_none bn k ==∗ pres_auth bn k rb 1%positive ∗ pres_frag bn k rb.
  Proof.
    iIntros "Ha". rewrite -own_op.
    iApply (own_update with "Ha").
    apply auth_update_alloc.
    apply (alloc_option_local_update (to_agree rb, 1%positive)).
    split; [| done]. rewrite -(agree_idemp (to_agree rb)). by apply to_agree_op_valid.
  Qed.

  (* another reference at the SAME bump pair *)
  Lemma pres_take_another bn k rb c :
    pres_auth bn k rb c ==∗
    pres_auth bn k rb (c + 1)%positive ∗ pres_frag bn k rb.
  Proof.
    iIntros "Ha". rewrite -own_op.
    iApply (own_update with "Ha").
    apply auth_update_alloc.
    assert (Heq : (Some (to_agree rb, (c + 1)%positive) : optionUR (prodR (agreeR presPair) positiveR))
                  ≡ Some (to_agree rb, 1%positive) ⋅ Some (to_agree rb, c)).
    { rewrite -Some_op -pair_op agree_idemp. f_equiv. split; [done|]. cbn.
      by rewrite Pos.add_comm. }
    apply local_update_unital_discrete. intros z _ Hz.
    rewrite left_id in Hz. rewrite -Hz. split.
    - rewrite Some_valid pair_valid. split; [| done].
      rewrite -(agree_idemp (to_agree rb)). by apply to_agree_op_valid.
    - exact Heq.
  Qed.

  Local Lemma to_agree_valid' (x : presPair) : ✓ to_agree x.
  Proof. rewrite -(agree_idemp (to_agree x)). by apply to_agree_op_valid. Qed.

  (* a frame that composes with one reference to give the auth is either
     nothing (last reference) or the rest of the references *)
  Local Lemma pres_frame_inv (rb : presPair) (c : positive)
      (z : optionUR (prodR (agreeR presPair) positiveR)) :
    ✓ (Some (to_agree rb, c) : optionUR (prodR (agreeR presPair) positiveR)) ->
    (Some (to_agree rb, c) : optionUR (prodR (agreeR presPair) positiveR))
      ≡ Some (to_agree rb, 1%positive) ⋅ z ->
    (c = 1%positive /\ z = None)
    \/ (exists p, c = (1 + p)%positive /\ z ≡ Some (to_agree rb, p)).
  Proof.
    intros Hv Hz. destruct z as [[a p]|].
    - right. rewrite -Some_op -pair_op in Hz. apply (inj Some) in Hz.
      destruct Hz as [Ha Hp]. cbn in Ha, Hp. fold_leibniz.
      assert (Hva : ✓ (to_agree rb ⋅ a)) by (rewrite -Ha; apply to_agree_valid').
      apply agree_op_inv in Hva.
      exists p. split; [done|]. by rewrite -Hva.
    - left. rewrite right_id in Hz. apply (inj Some) in Hz.
      destruct Hz as [_ Hp]. cbn in Hp. fold_leibniz. done.
  Qed.

  (* one of several references retires *)
  Lemma pres_drop_one bn k rb c :
    pres_auth bn k rb (1 + c)%positive -∗ pres_frag bn k rb ==∗
    pres_auth bn k rb c.
  Proof.
    iIntros "Ha Hf". iCombine "Ha Hf" as "H".
    iApply (own_update with "H").
    apply auth_update_dealloc.
    apply local_update_unital_discrete. intros z Hv Hz.
    destruct (pres_frame_inv _ _ _ Hv Hz) as [[Hc _] | (p & Hc & Hzeq)].
    - exfalso. lia.
    - assert (p = c) as -> by lia.
      split; [| by rewrite Hzeq left_id].
      rewrite Some_valid pair_valid. split; [apply to_agree_valid' | done].
  Qed.

  (* the LAST reference retires *)
  Lemma pres_last_drop bn k rb :
    pres_auth bn k rb 1%positive -∗ pres_frag bn k rb ==∗ pres_none bn k.
  Proof.
    iIntros "Ha Hf". iCombine "Ha Hf" as "H".
    iApply (own_update with "H").
    apply auth_update_dealloc.
    apply local_update_unital_discrete. intros z Hv Hz.
    destruct (pres_frame_inv _ _ _ Hv Hz) as [[_ ->] | (p & Hc & _)].
    - split; [done | by rewrite left_id].
    - exfalso. lia.
  Qed.


  (* ---- the checkout token: the buffer sleeplock's WHOLE resource ---- *)
  Definition bown (bn : bio_names) (k : nat) : iProp Σ :=
    lock_tok_excl (bn_own bn k).

  Lemma bown_exclusive bn k : bown bn k -∗ bown bn k -∗ False.
  Proof. apply lock_tok_excl_exclusive. Qed.
  Global Instance bown_timeless bn k : Timeless (bown bn k).
  Proof. rewrite /bown. apply _. Qed.

  (* ------------------------------------------------------------------ *)
  (*  The escrow                                                          *)
  (* ------------------------------------------------------------------ *)

  Definition bioN : namespace := nroot .@ "xv6bio".

  (* the recycle token: parked in A1/A2, in the recycler's hand during the
     A3 window (which is what lets the recycler refute A1/A2 when it closes
     the window -- see the header). *)
  Definition bmid (bn : bio_names) (k : nat) : iProp Σ :=
    lock_tok_excl (bn_mid bn k).

  Lemma bmid_exclusive bn k : bmid bn k -∗ bmid bn k -∗ False.
  Proof. apply lock_tok_excl_exclusive. Qed.

  (* one uncached covered block's pool bundle: its disk cell and its clean
     payload at the SAME content -- uncached implies clean, because the
     dirty arm parks a real [bref] and a referenced buffer is never
     evicted. *)
  Definition pool_blk (V : bio_view Σ) (b : Z) : iProp Σ :=
    (∃ bs : list (bv 8), disk_block (bv_gd V) b bs ∗ bv_clean V b bs)%I.

  (* a HELD covered block's payload: the logical content [bsl] against the
     disk cell's value [bsd], keyed by the dirty flag.  Clean ties the disk
     to the logical content; dirty parks the pinning reference instead. *)
  Definition bio_pay (bn : bio_names) (V : bio_view Σ) (k : nat)
      (dev bno : mword 32) (bsl bsd : list (bv 8)) (d : bool) : iProp Σ :=
    (if d
     then bv_dirty V (uint bno) bsl ∗ ∃ q : Qp, bref bn k q dev bno
     else bv_clean V (uint bno) bsl ∗ ⌜bsd = bsl⌝)%I.

  (* the payload a PARKED buffer carries, keyed on its valid bit: a valid
     covered buffer's bytes ARE the logical content (with the block's disk
     cell alongside); an invalid covered buffer carries the block's pool
     bundle, so that WHOEVER wins the sleeplock race after a recycle finds
     the fragment the fill needs.  Uncovered blocknos (only block 0 in
     practice -- binit's zeroed cells) carry nothing. *)
  Definition buf_pay (bn : bio_names) (V : bio_view Σ) (k : nat)
      (v : bool) (dev bno : mword 32) (bs : list (bv 8)) : iProp Σ :=
    (if decide (uint bno ∈ bv_cov V) then
       ⌜dev = bv_dev V⌝ ∗
       (if v
        then ∃ (bsd : list (bv 8)) (d : bool),
               disk_block (bv_gd V) (uint bno) bsd ∗
               bio_pay bn V k dev bno bs bsd d
        else pool_blk V (uint bno))
     else emp)%I.

  (* A1: the buffer's traveling content, parked.  disk is pinned 0 -- only
     rw flips it, and always back before returning.  The valid cell is
     keyed by the bool [v], which is what couples it to the payload's
     form. *)
  Definition buf_parked (bn : bio_names) (V : bio_view Σ) (k : nat) : iProp Σ :=
    (∃ (v : bool) (dev bno : mword 32) (bs : list (bv 8)),
       b_valid (bpa k) ↦₄
         (if v then (mword_of_int 1 : mword 32) else (mword_of_int 0 : mword 32)) ∗
       b_dev (bpa k) ↦₄{DfracOwn (1/2)} dev ∗
       buf_own (bpa k) bno (mword_of_int 0 : mword 32) bs ∗
       buf_pay bn V k v dev bno bs ∗
       bmid bn k)%I.

  (* A2: checked out by a sleeplock chain; the chain's own reference, the
     checkout token and the recycle token wait here until brelse brings
     the content back. *)
  Definition buf_chain (bn : bio_names) (k : nat) : iProp Σ :=
    (∃ (q : Qp) (dev bno : mword 32),
       bref_tok bn k q ∗
       b_dev (bpa k) ↦₄{DfracOwn q} dev ∗
       b_blockno (bpa k) ↦₄{DfracOwn q} bno ∗
       bown bn k ∗
       bmid bn k)%I.

  (* A3: the recycler's window between its blockno store and its valid
     store, where the blockno cell already names the NEW block but the
     valid cell is stale: cells only, decoupled from any payload.  The dev
     cell is FULL (the recycler joins the bcache-retained half in), which
     is what every OTHER opener refutes this arm by; the recycle token is
     out, in the recycler's hand.  The dev cell's VALUE is pinned to the
     view's device: the only creator is the recycler, right after its dev
     store, and the recycler itself holds no fraction across the window,
     so an existential value here would be unrecoverable at the valid
     store (and the re-parked arm's dev pin unprovable). *)
  Definition buf_mid (V : bio_view Σ) (k : nat) : iProp Σ :=
    (∃ (vld bno : mword 32) (bs : list (bv 8)),
       ⌜vld = (mword_of_int 0 : mword 32) \/ vld = (mword_of_int 1 : mword 32)⌝ ∗
       b_valid (bpa k) ↦₄ vld ∗
       b_dev (bpa k) ↦₄ (bv_dev V) ∗
       buf_own (bpa k) bno (mword_of_int 0 : mword 32) bs)%I.

  Definition buf_escrow_body (bn : bio_names) (V : bio_view Σ) (k : nat) : iProp Σ :=
    (buf_parked bn V k ∨ buf_chain bn k ∨ buf_mid V k)%I.

  Definition buf_escrow (bn : bio_names) (V : bio_view Σ) (k : nat) : iProp Σ :=
    inv bioN (buf_escrow_body bn V k).

  (* the whole body is TIMELESS (the view's payload fields carry their own
     Timeless proofs), so every opener strips the ▷ up front with the usual
     [iInv … as ">Hbody"] -- exactly as the physical layer did. *)

  (* PEEL ONE CONNECTIVE PER STEP (optimization.md, "Prove a big
     Timeless/Persistent instance STRUCTURALLY").  A single [apply _] over
     these ∃/∗/∨ towers backtracks across the whole space even though every
     leaf instance already exists: [buf_parked] alone measured 19.7 s, and the
     four instances below were 31.5 s of a 41.5 s file.  The dispatch must be
     SYNTACTIC -- a [first [apply bi.exist_timeless; … | …]] spelling unifies
     up to delta and peels straight THROUGH a name that has its own instance,
     which is the regression the note warns about. *)
  Local Ltac tl_struct :=
    lazymatch goal with
    | |- Timeless (bi_exist _) => apply bi.exist_timeless; intro; tl_struct
    | |- Timeless (bi_sep _ _) => apply bi.sep_timeless; [tl_struct | tl_struct]
    | |- Timeless (bi_or _ _)  => apply bi.or_timeless;  [tl_struct | tl_struct]
    | |- _ => apply _
    end.

  Global Instance bio_pay_timeless bn V k dev bno bsl bsd d :
    Timeless (bio_pay bn V k dev bno bsl bsd d).
  Proof. rewrite /bio_pay. destruct d; tl_struct. Qed.

  Global Instance pool_blk_timeless V b : Timeless (pool_blk V b).
  Proof. rewrite /pool_blk. tl_struct. Qed.

  Global Instance buf_pay_timeless bn V k v dev bno bs :
    Timeless (buf_pay bn V k v dev bno bs).
  Proof. rewrite /buf_pay. case_decide; [destruct v|]; tl_struct. Qed.

  Global Instance buf_parked_timeless bn V k : Timeless (buf_parked bn V k).
  Proof. rewrite /buf_parked. tl_struct. Qed.

  Global Instance buf_chain_timeless bn k : Timeless (buf_chain bn k).
  Proof. rewrite /buf_chain. tl_struct. Qed.

  Global Instance buf_mid_timeless V k : Timeless (buf_mid V k).
  Proof. rewrite /buf_mid. tl_struct. Qed.

  Global Instance buf_escrow_body_timeless bn V k :
    Timeless (buf_escrow_body bn V k).
  Proof. rewrite /buf_escrow_body. tl_struct. Qed.

  (* a reference fragment against an authority showing NO references: the
     refutation the free-open and the eviction reading both turn on. *)
  Lemma bref_tok_free_absurd bn (M : gmap nat (Qp * positive)) k q :
    M !! k = None ->
    own (bn_auth bn) (● M) -∗ bref_tok bn k q -∗ False.
  Proof.
    iIntros (HM) "Ha Htok". rewrite /bref_tok.
    iDestruct (own_valid_2 with "Ha Htok")
      as %[Hincl _]%auth_both_valid_discrete.
    iPureIntro.
    apply singleton_included_l in Hincl as [y [Hy _]].
    rewrite HM in Hy. inversion Hy.
  Qed.

  (* ---- the swaps (used inside an [iInv] open of [buf_escrow]) ---- *)

  (* (a) checkout, post-acquiresleep: the opener's bown refutes A2 and its
     reference's dev fraction refutes A3 (whose dev cell is full); its
     reference's cell fractions AGREE with the parked bundle's, pinning the
     withdrawn dev/bno to the requested key.  The deposited A2 absorbs the
     parked arm's recycle token, so the handle needn't carry it. *)
  Lemma escrow_swap_checkout bn V k q (dev bno : mword 32) :
    buf_escrow_body bn V k -∗
    bown bn k -∗
    bref_tok bn k q -∗
    b_dev (bpa k) ↦₄{DfracOwn q} dev -∗
    b_blockno (bpa k) ↦₄{DfracOwn q} bno -∗
    buf_escrow_body bn V k ∗
    (∃ (v : bool) (bs : list (bv 8)),
       b_valid (bpa k) ↦₄
         (if v then (mword_of_int 1 : mword 32) else (mword_of_int 0 : mword 32)) ∗
       b_dev (bpa k) ↦₄{DfracOwn (1/2)} dev ∗
       buf_own (bpa k) bno (mword_of_int 0 : mword 32) bs ∗
       buf_pay bn V k v dev bno bs).
  Proof.
    iIntros "Hbody Hown Htok Hdev Hbno".
    iDestruct "Hbody" as "[Hparked | [Hchain | Hmid]]".
    - iDestruct "Hparked" as (v dev' bno' bs) "(Hvld & Hdev' & Hbuf & Hpay & Hbmid)".
      iDestruct (ctx_word4_pointsto_agree with "Hdev Hdev'") as %Heqd. subst dev'.
      rewrite /buf_own.
      iDestruct "Hbuf" as "(Hbno' & Hdisk & %Hlen & Hdata)".
      iDestruct (ctx_word4_pointsto_agree with "Hbno Hbno'") as %Heqb. subst bno'.
      iSplitL "Htok Hdev Hbno Hown Hbmid".
      { iRight; iLeft. rewrite /buf_chain. iExists q, dev, bno. iFrame. }
      iExists v, bs. iFrame "Hvld Hdev' Hpay".
      rewrite /buf_own. iFrame "Hbno' Hdisk Hdata". done.
    - iDestruct "Hchain" as (q' dev' bno') "(_ & _ & _ & Hown' & _)".
      iExFalso. iApply (bown_exclusive with "Hown Hown'").
    - iDestruct "Hmid" as (vld bno' bs) "(_ & _ & Hdev' & _)".
      iExFalso. iApply (word4_pointsto_excl with "Hdev' Hdev").
  Qed.

  (* (b) park, brelse's first instruction: the opener's full valid cell
     refutes A1 AND A3 (both hold the cell full); the chain's reference and
     bown come back out, and the deposited A1 re-absorbs the recycle token
     the chain arm was keeping.  The withdrawn fractions agree with the
     deposited bundle's, so the recovered reference is at the SAME key. *)
  Lemma escrow_swap_park bn V k (v : bool) (dev bno : mword 32) (bs : list (bv 8)) :
    buf_escrow_body bn V k -∗
    b_valid (bpa k) ↦₄
      (if v then (mword_of_int 1 : mword 32) else (mword_of_int 0 : mword 32)) -∗
    b_dev (bpa k) ↦₄{DfracOwn (1/2)} dev -∗
    buf_own (bpa k) bno (mword_of_int 0 : mword 32) bs -∗
    buf_pay bn V k v dev bno bs -∗
    buf_escrow_body bn V k ∗
    (∃ q : Qp,
       bref_tok bn k q ∗
       b_dev (bpa k) ↦₄{DfracOwn q} dev ∗
       b_blockno (bpa k) ↦₄{DfracOwn q} bno ∗
       bown bn k).
  Proof.
    iIntros "Hbody Hvld Hdev Hbuf Hpay".
    iDestruct "Hbody" as "[Hparked | [Hchain | Hmid]]".
    - iDestruct "Hparked" as (v' dev' bno' bs') "(Hvld' & _)".
      iExFalso. iApply (word4_pointsto_excl with "Hvld Hvld'").
    - iDestruct "Hchain" as (q dev' bno') "(Htok & Hdev' & Hbno' & Hown & Hbmid)".
      iDestruct (ctx_word4_pointsto_agree with "Hdev Hdev'") as %Heqd. subst dev'.
      rewrite /buf_own.
      iDestruct "Hbuf" as "(Hbno & Hdisk & %Hlen & Hdata)".
      iDestruct (ctx_word4_pointsto_agree with "Hbno' Hbno") as %Heqb. subst bno'.
      iSplitR "Htok Hdev' Hbno' Hown".
      { iLeft. rewrite /buf_parked. iExists v, dev, bno, bs.
        iFrame "Hvld Hdev Hpay Hbmid".
        rewrite /buf_own. iFrame "Hbno Hdisk Hdata". done. }
      iExists q. iFrame.
    - iDestruct "Hmid" as (vld bno' bs') "(_ & Hvld' & _)".
      iExFalso. iApply (word4_pointsto_excl with "Hvld' Hvld").
  Qed.

  (* THE SAME SWAP, with the withdrawn bundle already OUT from under the
     [▷] that [iInv] hands back.  brelse's park runs inside the +0x02
     store's atomic update and needs the reference NOW, so it must strip
     that later -- and the cost of doing so is proportional to the Iris
     CONTEXT it is done in, not to the bundle: the [iMod "Hpark"] at
     brelse's store measured 34 s, while the identical [Timeless] search on
     the identical bundle costs 0.4 s here, where the context is five
     hypotheses wide.  So the later comes off HERE and the caller writes one
     [iMod].  (Same family as optimization.md's [iNext] rule: never pay a
     context-proportional modality step inside a whole-function proof when a
     lemma can pay it once.) *)
  Lemma escrow_swap_park_now (E : coPset) bn V k (v : bool)
      (dev bno : mword 32) (bs : list (bv 8)) :
    ▷ buf_escrow_body bn V k -∗
    b_valid (bpa k) ↦₄
      (if v then (mword_of_int 1 : mword 32) else (mword_of_int 0 : mword 32)) -∗
    b_dev (bpa k) ↦₄{DfracOwn (1/2)} dev -∗
    buf_own (bpa k) bno (mword_of_int 0 : mword 32) bs -∗
    buf_pay bn V k v dev bno bs -∗
    |={E}=> ▷ buf_escrow_body bn V k ∗
            (∃ q : Qp,
               bref_tok bn k q ∗
               b_dev (bpa k) ↦₄{DfracOwn q} dev ∗
               b_blockno (bpa k) ↦₄{DfracOwn q} bno ∗
               bown bn k).
  Proof.
    iIntros "Hbody Hvld Hdev Hbuf Hpay".
    iAssert (▷ (buf_escrow_body bn V k ∗
                (∃ q : Qp,
                   bref_tok bn k q ∗
                   b_dev (bpa k) ↦₄{DfracOwn q} dev ∗
                   b_blockno (bpa k) ↦₄{DfracOwn q} bno ∗
                   bown bn k)))%I
      with "[Hbody Hvld Hdev Hbuf Hpay]" as "Hsw".
    { iNext. iApply (escrow_swap_park bn V k v dev bno bs
                       with "Hbody Hvld Hdev Hbuf Hpay"). }
    iDestruct "Hsw" as "[Hbody Hpark]". iMod "Hpark".
    iModIntro. iSplitL "Hbody"; [iExact "Hbody" | iExact "Hpark"].
  Qed.

  (* (c) the miss path's view: with the authority showing no references, A2
     is impossible, and the bcache-retained dev half refutes A3 (whose dev
     cell is full), so the body IS the parked bundle. *)
  Lemma escrow_open_free bn V k (M : gmap nat (Qp * positive)) (devr : mword 32) :
    M !! k = None ->
    own (bn_auth bn) (● M) -∗
    b_dev (bpa k) ↦₄{DfracOwn (1/2)} devr -∗
    buf_escrow_body bn V k -∗
    own (bn_auth bn) (● M) ∗
    b_dev (bpa k) ↦₄{DfracOwn (1/2)} devr ∗
    buf_parked bn V k ∗
    (buf_parked bn V k -∗ buf_escrow_body bn V k).
  Proof.
    iIntros (HM) "Ha Hdevr Hbody".
    iDestruct "Hbody" as "[Hparked | [Hchain | Hmid]]".
    - iFrame "Ha Hdevr Hparked". iIntros "Hp". by iLeft.
    - iDestruct "Hchain" as (q dev bno) "(Htok & _)".
      iExFalso. iApply (bref_tok_free_absurd bn M k q HM with "Ha Htok").
    - iDestruct "Hmid" as (vld bno bs) "(_ & _ & Hdev & _)".
      iExFalso. iApply (word4_pointsto_excl with "Hdev Hdevr").
  Qed.

  (* (d) the recycler's re-open at its valid store: its recycle token
     refutes BOTH normal arms, so the body is the mid window it parked; the
     reclose is at a normal parked arm, which re-absorbs the token. *)
  Lemma escrow_open_mid bn V k :
    bmid bn k -∗
    buf_escrow_body bn V k -∗
    bmid bn k ∗ buf_mid V k ∗
    (buf_parked bn V k -∗ buf_escrow_body bn V k).
  Proof.
    iIntros "Hbmid Hbody".
    iDestruct "Hbody" as "[Hparked | [Hchain | Hmid]]".
    - iDestruct "Hparked" as (v dev bno bs) "(_ & _ & _ & _ & Hbmid')".
      iExFalso. iApply (bmid_exclusive with "Hbmid Hbmid'").
    - iDestruct "Hchain" as (q dev bno) "(_ & _ & _ & _ & Hbmid')".
      iExFalso. iApply (bmid_exclusive with "Hbmid Hbmid'").
    - iFrame "Hbmid Hmid". iIntros "Hp". by iLeft.
  Qed.

  (* closing the window OPEN (at the blockno store): any mid bundle is a
     legal body. *)
  Lemma escrow_close_mid bn V k :
    buf_mid V k -∗ buf_escrow_body bn V k.
  Proof. iIntros "H". iRight; iRight. iExact "H". Qed.

  (* the eviction reading of a parked payload: with the authority showing
     no references the dirty arm (which parks a real bref) is impossible,
     so a covered payload yields exactly the block's pool bundle.  This is
     the "only clean content ever leaves the cache" fact. *)
  Lemma buf_pay_evict bn V k (M : gmap nat (Qp * positive))
      (v : bool) (dev bno : mword 32) (bs : list (bv 8)) :
    M !! k = None ->
    own (bn_auth bn) (● M) -∗
    buf_pay bn V k v dev bno bs -∗
    own (bn_auth bn) (● M) ∗
    (if decide (uint bno ∈ bv_cov V)
     then ⌜dev = bv_dev V⌝ ∗ pool_blk V (uint bno)
     else emp).
  Proof.
    iIntros (HM) "Ha Hpay". rewrite /buf_pay.
    case_decide as Hc; last by iFrame.
    iDestruct "Hpay" as "[%Hdev Hpay]".
    destruct v.
    - iDestruct "Hpay" as (bsd d) "[Hdb Hpay]".
      destruct d; rewrite /bio_pay.
      + iDestruct "Hpay" as "[_ Hq]". iDestruct "Hq" as (q) "(Htok & _ & _)".
        iExFalso. iApply (bref_tok_free_absurd bn M k q HM with "Ha Htok").
      + iDestruct "Hpay" as "[Hcl %Hbsd]". subst bsd.
        iFrame "Ha". iSplitR; [done|]. rewrite /pool_blk. iExists bs. iFrame.
    - iFrame "Ha". iSplitR; [done|]. iExact "Hpay".
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  The count authority: lookups and the three ghost steps              *)
  (* ------------------------------------------------------------------ *)

  (* a reference against the authority (fref_tok_lookup's mirror): the entry
     exists, and the sole reference holds the whole outstanding fraction.
     The THIRD conjunct is the same [singleton_included_l] reading one step
     further -- the STRICT order at a surviving entry, which is what
     [bio_decr_step]'s [(qt - q) = Some qr] premise needs (brelse and bunpin
     both take it on their non-last decrement). *)
  Lemma bref_tok_lookup bn M k q :
    own (bn_auth bn) (● M) -∗ bref_tok bn k q -∗
    ⌜∃ qt n, M !! k = Some (qt, n) /\
       (n = 1%positive -> q = qt) /\ (q = qt -> n = 1%positive) /\
       (n ≠ 1%positive -> (q < qt)%Qp)⌝.
  Proof.
    rewrite /bref_tok. iIntros "Ha Hf".
    iDestruct (own_valid_2 with "Ha Hf") as %[Hincl _]%auth_both_valid_discrete.
    iPureIntro.
    apply singleton_included_l in Hincl as [y [Hy Hle]].
    apply leibniz_equiv in Hy. destruct y as [qt n]. exists qt, n.
    split; [exact Hy|].
    apply Some_included in Hle as [Heq | Hlt].
    - destruct Heq as [Hq Hn]; cbn in Hq, Hn.
      split_and!.
      + intros _. exact Hq.
      + intros _. by rewrite -Hn.
      + intros Hne. exfalso. apply Hne. by rewrite -Hn.
    - apply pair_included in Hlt as [Hq Hn]; cbn in Hq, Hn.
      apply frac_included in Hq. apply pos_included in Hn.
      split_and!.
      + intros Hc. exfalso. rewrite Hc in Hn. lia.
      + intros Hc. exfalso. rewrite Hc in Hq. by apply (irreflexivity Qp.lt qt).
      + intros _. exact Hq.
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

  (* ---- the refcnt word's two VALUE TIES (FileInv's fref_word_zero /
     fref_word_nonzero at this cell) ----

     The [lw] of the refcnt sign-extends, and both the [beqz] of bread's
     backward scan and the [bnez] of brelse's/bunpin's decrement compare that
     against x0: so the word is zero exactly when the slot is free, and a
     slot-backed [positive] count (< 2^31, which is what the [bslot] supply
     buys) is never zero.  Stated in BOTH polarities because the two branch
     leaves take [eq_vec] (a [beqz]) and [neq_vec] (a [bnez]) respectively. *)
  Lemma brc_word_zero_eqv :
    eq_vec (sign_extend' 64 (mword_of_int 0 : mword 32)) (zero_reg : mword 64) = true.
  Proof. apply eq_vec_true_iff. apply bv_eq. vm_compute. reflexivity. Qed.

  Lemma brc_word_nonzero_eqv (pz : positive) :
    (Z.pos pz < 2 ^ 31)%Z ->
    eq_vec (sign_extend' 64 (mword_of_int (Z.pos pz) : mword 32)) (zero_reg : mword 64)
    = false.
  Proof.
    intro Hn.
    (* [lia] cannot evaluate [2^k]; name the three literals first. *)
    assert (E31 : (2 ^ 31 = 2147483648)%Z) by (vm_compute; reflexivity).
    assert (E32 : (2 ^ 32 = 4294967296)%Z) by (vm_compute; reflexivity).
    assert (E64 : (2 ^ 64 = 18446744073709551616)%Z) by (vm_compute; reflexivity).
    rewrite E31 in Hn.
    assert (Hu : bv_unsigned (mword_of_int (Z.pos pz) : mword 32) = Z.pos pz).
    { unfold mword_of_int, Values.mword_of_int, MachineWord.MachineWord.Z_to_word.
      rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
      change (Z.of_N 32) with 32. rewrite E32.
      rewrite Z.mod_small; [reflexivity | lia]. }
    assert (Hs : bv_signed (mword_of_int (Z.pos pz) : mword 32) = Z.pos pz).
    { unfold bv_signed. rewrite Hu. apply bv_swrap_small.
      unfold bv_half_modulus, bv_modulus. change (Z.of_N 32) with 32.
      assert (Ehalf : (2 ^ 32 / 2 = 2147483648)%Z) by (vm_compute; reflexivity).
      rewrite Ehalf. lia. }
    apply eq_vec_false_iff. intro Hc. apply (f_equal bv_unsigned) in Hc.
    assert (Hz : bv_unsigned (zero_reg : mword 64) = 0) by (vm_compute; reflexivity).
    rewrite Hz in Hc. revert Hc.
    cbv [sign_extend' Operators_mwords.sign_extend Operators_mwords.exts_vec
         to_word get_word MachineWord.MachineWord.sign_extend].
    rewrite bv_sign_extend_unsigned. rewrite Hs.
    unfold bv_wrap, bv_modulus. change (Z.of_N 64) with 64.
    rewrite E64. rewrite Z.mod_small; [lia|]. lia.
  Qed.

  Lemma brc_word_zero_neqv :
    neq_vec (sign_extend' 64 (mword_of_int 0 : mword 32)) (zero_reg : mword 64) = false.
  Proof. unfold neq_vec. by rewrite brc_word_zero_eqv. Qed.

  Lemma brc_word_nonzero_neqv (pz : positive) :
    (Z.pos pz < 2 ^ 31)%Z ->
    neq_vec (sign_extend' 64 (mword_of_int (Z.pos pz) : mword 32)) (zero_reg : mword 64)
    = true.
  Proof. intro Hn. unfold neq_vec. by rewrite (brc_word_nonzero_eqv pz Hn). Qed.

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
         bslots (Pos.to_nat n) ∗
         ∃ qr : Qp, ⌜(q + qr)%Qp = (1/2)%Qp⌝ ∗
           b_dev (bpa k) ↦₄{DfracOwn qr} dev ∗
           b_blockno (bpa k) ↦₄{DfracOwn qr} bno)%I
    end.

  (* ------------------------------------------------------------------ *)
  (*  The uncached pool                                                    *)
  (* ------------------------------------------------------------------ *)

  (* the blocknos currently claimed by SOME buffer slot, valid or not (an
     invalid slot's blockno still names the block whose fill is in flight;
     binit's slots all claim 0, which [bv_cov] excludes). *)
  Definition bcache_cached (bnos : nat -> mword 32) : gset Z :=
    list_to_set ((fun k => uint (bnos k)) <$> seq 0 NBUF).

  Lemma bcache_cached_spec (bnos : nat -> mword 32) (b : Z) :
    b ∈ bcache_cached bnos <-> exists j, (j < NBUF)%nat /\ b = uint (bnos j).
  Proof.
    rewrite /bcache_cached elem_of_list_to_set elem_of_list_fmap.
    split.
    - intros (j & -> & Hj). apply elem_of_seq in Hj. exists j.
      split; [lia | done].
    - intros (j & Hj & ->). exists j. split; [done|]. apply elem_of_seq. lia.
  Qed.

  (* every covered block no slot claims carries its pool bundle here: the
     cache overlay's "uncached => home disk content IS the logical
     content".  Rides inside the bcache lock's resource because every
     cached/uncached transition happens under bcache.lock. *)
  Definition bio_pool (V : bio_view Σ) (bnos : nat -> mword 32) : iProp Σ :=
    ([∗ set] b ∈ bv_cov V ∖ bcache_cached bnos, pool_blk V b)%I.

  (* the recycle's one-shot pool exchange, at the blockno store: slot k's
     claim moves old -> B, so B's bundle leaves the pool (into the
     recycler's hand, and from there into the escrow's invalid arm at the
     valid store) and old's bundle -- extracted from the evicted arm by
     [buf_pay_evict] -- comes back in, when old is covered at all. *)
  Lemma bio_pool_recycle (V : bio_view Σ) (bnos bnos' : nat -> mword 32)
      (k : nat) (old B : mword 32) :
    (k < NBUF)%nat ->
    bnos k = old ->
    bnos' k = B ->
    (forall j, j ≠ k -> bnos' j = bnos j) ->
    uint B ∈ bv_cov V ->
    (forall j, (j < NBUF)%nat -> uint (bnos j) ≠ uint B) ->
    (uint old ∈ bv_cov V ->
       forall j, (j < NBUF)%nat -> j ≠ k -> uint (bnos j) ≠ uint old) ->
    bio_pool V bnos -∗
    pool_blk V (uint B) ∗
    ((if decide (uint old ∈ bv_cov V) then pool_blk V (uint old) else emp) -∗
     bio_pool V bnos').
  Proof.
    iIntros (Hk Hbk Hbk' Hother HcovB HmissB Holdu) "Hpool".
    rewrite /bio_pool.
    assert (HBin : uint B ∈ bv_cov V ∖ bcache_cached bnos).
    { apply elem_of_difference. split; [exact HcovB|].
      intros Hc. apply bcache_cached_spec in Hc as (j & Hj & Heq).
      exact (HmissB j Hj (eq_sym Heq)). }
    rewrite (big_sepS_delete _ _ _ HBin).
    iDestruct "Hpool" as "[$ Hpool]".
    case_decide as Hcovold.
    - (* old covered: it joins the pool *)
      assert (Hset : bv_cov V ∖ bcache_cached bnos' =
                     {[uint old]} ∪ (bv_cov V ∖ bcache_cached bnos ∖ {[uint B]})).
      { apply set_eq. intros b.
        rewrite elem_of_union elem_of_singleton !elem_of_difference
                elem_of_singleton.
        split.
        - intros [Hbcov Hbnc].
          destruct (decide (b = uint old)) as [->|Hne]; [by left|].
          right. split; [split; [exact Hbcov|]|].
          + intros Hc. apply bcache_cached_spec in Hc as (j & Hj & ->).
            destruct (decide (j = k)) as [->|Hjk].
            * apply Hne. rewrite Hbk. done.
            * apply Hbnc. apply bcache_cached_spec. exists j.
              split; [done|]. rewrite (Hother j Hjk). done.
          + intros ->. apply Hbnc. apply bcache_cached_spec.
            exists k. split; [done|]. rewrite Hbk'. done.
        - intros [-> | [[Hbcov Hbnc] HneB]].
          + split; [exact Hcovold|].
            intros Hc. apply bcache_cached_spec in Hc as (j & Hj & Heq).
            destruct (decide (j = k)) as [->|Hjk].
            * rewrite Hbk' in Heq. apply (HmissB k Hk).
              rewrite Hbk -Heq. done.
            * rewrite (Hother j Hjk) in Heq.
              exact (Holdu Hcovold j Hj Hjk (eq_sym Heq)).
          + split; [exact Hbcov|].
            intros Hc. apply bcache_cached_spec in Hc as (j & Hj & Heq).
            destruct (decide (j = k)) as [->|Hjk].
            * apply HneB. rewrite Heq Hbk'. done.
            * apply Hbnc. apply bcache_cached_spec. exists j.
              split; [done|]. rewrite -(Hother j Hjk). done. }
      rewrite Hset big_sepS_union; last first.
      { apply disjoint_singleton_l. intros Hc.
        apply elem_of_difference in Hc as [Hc _].
        apply elem_of_difference in Hc as [_ Hnc].
        apply Hnc. apply bcache_cached_spec. exists k.
        split; [done|]. rewrite Hbk. done. }
      rewrite big_sepS_singleton.
      iIntros "Hold". iFrame.
    - (* old uncovered: the pool just shrinks by B *)
      assert (Hset : bv_cov V ∖ bcache_cached bnos' =
                     bv_cov V ∖ bcache_cached bnos ∖ {[uint B]}).
      { apply set_eq. intros b.
        rewrite !elem_of_difference elem_of_singleton.
        split.
        - intros [Hbcov Hbnc]. split; [split; [exact Hbcov|]|].
          + intros Hc. apply bcache_cached_spec in Hc as (j & Hj & ->).
            destruct (decide (j = k)) as [->|Hjk].
            * apply Hcovold. rewrite -Hbk. exact Hbcov.
            * apply Hbnc. apply bcache_cached_spec. exists j.
              split; [done|]. rewrite (Hother j Hjk). done.
          + intros ->. apply Hbnc. apply bcache_cached_spec.
            exists k. split; [done|]. rewrite Hbk'. done.
        - intros [[Hbcov Hbnc] HneB]. split; [exact Hbcov|].
          intros Hc. apply bcache_cached_spec in Hc as (j & Hj & Heq).
          destruct (decide (j = k)) as [->|Hjk].
          + apply HneB. rewrite Heq Hbk'. done.
          + apply Hbnc. apply bcache_cached_spec. exists j.
            split; [done|]. rewrite -(Hother j Hjk). done. }
      rewrite Hset. iIntros "_". iExact "Hpool".
  Qed.

  (* THE OPEN FORM: the whole resource with its four existentials NAMED.
     This is not cosmetic.  bread's forward scan establishes its exit fact by
     COMPARING the dev/blockno words it reads out of [bio_slot_res] against
     its arguments, i.e. what it leaves the loop with is [devs k = dev /\
     bnos k = bno] -- a statement about the FUNCTIONS the closed form hides.
     If a loop iteration re-packaged the closed form the tie would be lost the
     moment it was established, and the refcnt++ that follows could not hand
     back a [bref] at the REQUESTED key -- bread's postcondition would be
     unprovable.  (Same family as the virtio [vs_data] lesson in
     claude-notes/durable-notes.md: a resource that crosses a boundary must
     RECORD the value the other side needs to identify.)  So both scans carry
     the open form and only the release path closes it.

     NEW over the physical layer: the covered-blockno INJECTIVITY (two slots
     never claim the same covered block -- what makes the pool's set
     subtraction and the eviction deposit sound; the miss scan's exit ties
     re-establish it at the recycle) and the pool itself. *)
  Definition bcache_scan (bn : bio_names) (V : bio_view Σ)
      (M : gmap nat (Qp * positive))
      (ord : list nat) (devs bnos : nat -> mword 32) : iProp Σ :=
    (own (bn_auth bn) (● M) ∗
     bslots_auth ∗
     ⌜∀ k, is_Some (M !! k) -> (k < NBUF)%nat⌝ ∗
     ⌜ord ≡ₚ seq 0 NBUF⌝ ∗
     ⌜∀ k1 k2, (k1 < NBUF)%nat -> (k2 < NBUF)%nat ->
        uint (bnos k1) ∈ bv_cov V ->
        uint (bnos k1) = uint (bnos k2) -> k1 = k2⌝ ∗
     (* the DEV PIN: a slot claiming a covered blockno is on the view's
        device.  This is what upgrades the forward scan's per-slot exit tie
        (dev ≠ OR bno ≠, the negation of the code's && ) to the miss fact
        the pool exchange needs (∀ j, bnos j ≠ B): the payload's own dev
        pin is unreachable mid-scan (a checked-out arm carries no payload),
        so the fact must be RECORDED here -- the vs_data rule again. *)
     ⌜∀ k, (k < NBUF)%nat -> uint (bnos k) ∈ bv_cov V ->
        devs k = bv_dev V⌝ ∗
     bcache_lru bhead (map bnode ord) ∗
     bio_pool V bnos ∗
     [∗ list] k ∈ seq 0 NBUF, bio_slot_res bn M k (devs k) (bnos k))%I.

  (* ...and the CLOSED form the bcache spinlock is sealed over: its closure. *)
  Definition bcache_res (bn : bio_names) (V : bio_view Σ) : iProp Σ :=
    (∃ (M : gmap nat (Qp * positive)) (ord : list nat)
       (devs bnos : nat -> mword 32),
       bcache_scan bn V M ord devs bnos)%I.

  Lemma bcache_res_to_scan (bn : bio_names) (V : bio_view Σ) :
    bcache_res bn V -∗ ∃ M ord devs bnos, bcache_scan bn V M ord devs bnos.
  Proof. rewrite /bcache_res. iIntros "H". iExact "H". Qed.

  Lemma bcache_scan_to_res (bn : bio_names) (V : bio_view Σ) M ord devs bnos :
    bcache_scan bn V M ord devs bnos -∗ bcache_res bn V.
  Proof.
    rewrite /bcache_res. iIntros "H". iExists M, ord, devs, bnos. iExact "H".
  Qed.

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

  Definition bio_ctx_old (bn : bio_names) (V : bio_view Σ) : iProp Σ :=
    (is_lock (bn_lk bn) bcache_addr "bcache"%string <{ bcache_res bn V }> ∗
     [∗ list] k ∈ seq 0 NBUF,
       (is_sleeplock (fst (bn_slk bn k)) (snd (bn_slk bn k))
          (buf_lock (bnode k)) "buffer"%string (bown bn k) ∗
        buf_escrow bn V k))%I.

  Global Instance bio_ctx_old_persistent bn V : Persistent (bio_ctx_old bn V).
  Proof. apply _. Qed.

  Lemma bio_ctx_old_lock bn V :
    bio_ctx_old bn V -∗
    is_lock (bn_lk bn) bcache_addr "bcache"%string <{ bcache_res bn V }>.
  Proof. iIntros "[$ _]". Qed.

  Lemma bio_ctx_old_buf bn V k :
    (k < NBUF)%nat ->
    bio_ctx_old bn V -∗
    is_sleeplock (fst (bn_slk bn k)) (snd (bn_slk bn k))
      (buf_lock (bnode k)) "buffer"%string (bown bn k) ∗
    buf_escrow bn V k.
  Proof.
    iIntros (Hk) "[_ Hbufs]".
    assert (Hlk : seq 0 NBUF !! k = Some k) by (apply lookup_seq; lia).
    iDestruct (big_sepL_lookup with "Hbufs") as "[$ $]"; [exact Hlk].
  Qed.

  (* the held-buffer handle bread returns and bwrite/brelse (and the log
     layer's log_write) consume: the sleeplock holder's bundle, the
     traveling content at [bs], the block's disk cell at [bsd], and the
     payload at logical content [bsl] with dirty flag [d].  The chain's
     reference is NOT here (it rides in the escrow); the DIRTY payload's
     pinning reference is.

     [bio_held] leaves [bs] and [bsl] independent -- a holder who has
     edited the bytes has bs ≠ bsl until log_write re-indexes the payload
     -- and [bio_locked] (what bread returns and bwrite/brelse demand)
     ties them.  That tie IS the brelse obligation: modified bytes cannot
     be parked until the payload says they are the logical content. *)
  Definition bio_held (bn : bio_names) (V : bio_view Σ) (k : nat)
      (pidv dev bno : mword 32) (bs bsl bsd : list (bv 8)) (d : bool) : iProp Σ :=
    (⌜(k < NBUF)%nat⌝ ∗
     ⌜uint bno ∈ bv_cov V⌝ ∗
     ⌜dev = bv_dev V⌝ ∗
     (* the buffer's sleeplock, held -- its [pid] field is INSIDE the token
        now (SleepLock.v's [sleeplocked_q]), so [pidv] indexes the token
        rather than a row of its own. *)
     sleeplocked (snd (bn_slk bn k)) (buf_lock (bnode k)) pidv ∗
     b_valid (bpa k) ↦₄ (mword_of_int 1 : mword 32) ∗
     b_dev (bpa k) ↦₄{DfracOwn (1/2)} dev ∗
     buf_own (bpa k) bno (mword_of_int 0 : mword 32) bs ∗
     disk_block (bv_gd V) (uint bno) bsd ∗
     bio_pay bn V k dev bno bsl bsd d)%I.

  Definition bio_locked (bn : bio_names) (V : bio_view Σ) (k : nat)
      (pidv dev bno : mword 32) (bs bsd : list (bv 8)) (d : bool) : iProp Σ :=
    bio_held bn V k pidv dev bno bs bs bsd d.

  (* the handle MINUS its payload: what bwrite consumes.  A
     content-changing write (write_head rewriting the header) necessarily
     has logical ≠ disk on one side of the call WHATEVER the order of the
     ghost update and the write, so the clean payload's ⌜bsd = bsl⌝ tie
     cannot appear in bwrite's pre or post: the caller holds the payload
     aside across the call and re-pairs afterwards (bio_held_split). *)
  Definition bio_hold0 (bn : bio_names) (V : bio_view Σ) (k : nat)
      (pidv dev bno : mword 32) (bs bsd : list (bv 8)) : iProp Σ :=
    (⌜(k < NBUF)%nat⌝ ∗
     ⌜uint bno ∈ bv_cov V⌝ ∗
     ⌜dev = bv_dev V⌝ ∗
     (* the buffer's sleeplock, held -- its [pid] field is INSIDE the token
        now (SleepLock.v's [sleeplocked_q]), so [pidv] indexes the token
        rather than a row of its own. *)
     sleeplocked (snd (bn_slk bn k)) (buf_lock (bnode k)) pidv ∗
     b_valid (bpa k) ↦₄ (mword_of_int 1 : mword 32) ∗
     b_dev (bpa k) ↦₄{DfracOwn (1/2)} dev ∗
     buf_own (bpa k) bno (mword_of_int 0 : mword 32) bs ∗
     disk_block (bv_gd V) (uint bno) bsd)%I.

  Lemma bio_held_split bn V k pidv dev bno bs bsl bsd d :
    bio_held bn V k pidv dev bno bs bsl bsd d ⊣⊢
    bio_hold0 bn V k pidv dev bno bs bsd ∗
    bio_pay bn V k dev bno bsl bsd d.
  Proof.
    rewrite /bio_held /bio_hold0.
    iSplit.
    - iIntros "(%A & %B & %C & H1 & H2 & H3 & H4 & H5 & H6)".
      iSplitR "H6"; [|iExact "H6"].
      iSplitR; [done|]. iSplitR; [done|]. iSplitR; [done|]. iFrame.
    - iIntros "[(%A & %B & %C & H1 & H2 & H3 & H4 & H5) H6]".
      iSplitR; [done|]. iSplitR; [done|]. iSplitR; [done|]. iFrame.
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  Construction: binit's postcondition + the .bss-zeroed buffers       *)
  (* ------------------------------------------------------------------ *)

  Local Lemma bio_seq_cons (j n : nat) : seq j (S n) = j :: seq (S j) n.
  Proof. reflexivity. Qed.

  (* GNAMES BEFORE THE RECORD.  [bio_names] cannot be built until all of the
     per-buffer gnames exist, and [bown bn k] -- the resource the sleeplocks
     seal -- mentions [bn].  The way out: allocate the CHECKOUT TOKENS first
     (their gnames are just a [nat -> gname] function, no record needed), then
     the sleeplocks over [lock_tok_excl (f k)], collecting THEIR gname pairs
     into a second function; [bn] is assembled from the two functions at the
     end, and [bown bn k] is [lock_tok_excl (f k)] by construction.
     These two lemmas are the collectors. *)
  Lemma tok_fun_alloc (n j : nat) :
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

  Lemma seq_fun_alloc {A : Type} `{Inhabited A} (E : coPset)
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
     authority map is empty and the LRU list is binit's [blist 0 NBUF].

     NEW over the physical layer: the client supplies the whole covered
     range's pool bundles (its [disk_block]s paired with clean payloads --
     for the log layer, the mkfs image's content against the logged-view
     ghost), and 0 must be outside the covered range because every zeroed
     blockno cell claims it. *)
  (* A6.68: the honest creator deposit (A6.66) wants the running token, and
     this boot step builds NBUF+1 locks.  Borrowed once and handed straight
     back; the per-buffer loop threads it with
     [SepThread.big_sepL_fupd_thread], because [own_context] is EXCLUSIVE and
     the NBUF steps cannot run as independent fupds. *)
  Lemma bio_init_old `{CID : RiscvLang.CpuId} (V : bio_view Σ) E :
    (0 ∉ bv_cov V) ->
    own_context cur_ctx -∗
    bcache_addr ↦₄ (mword_of_int 0 : mword 32) -∗
    lock_name bcache_addr "bcache"%string -∗
    WpLock.lk_cpu_ready bcache_addr -∗
    ([∗ list] k ∈ seq 0 NBUF, sl_fresh (buf_lock (bnode k)) "buffer"%string) -∗
    ([∗ list] k ∈ seq 0 NBUF,
       b_valid (bpa k) ↦₄ (mword_of_int 0 : mword 32) ∗
       b_disk (bpa k) ↦₄ (mword_of_int 0 : mword 32) ∗
       b_dev (bpa k) ↦₄ (mword_of_int 0 : mword 32) ∗
       b_blockno (bpa k) ↦₄ (mword_of_int 0 : mword 32) ∗
       brefcnt k ↦₄ (mword_of_int 0 : mword 32) ∗
       (∃ bs : list (bv 8), ⌜length bs = 1024%nat⌝ ∗
          [∗ list] j ↦ byte ∈ bs, pa_add (b_data (bpa k)) j ↦ₘ byte)) -∗
    bcache_lru bhead (blist 0 NBUF) -∗
    ([∗ set] b ∈ bv_cov V, pool_blk V b) -∗
    (* THE SLOT SUPPLY IS NO LONGER MINTED HERE.  Its ghost name is
       canonical ([Xv6Cameras.bioslot_name]) and therefore fixed before this
       invariant exists, so [BioDefs.bslots_alloc] mints it at boot and this
       function takes the authority in and hands the fragments straight back
       out -- the same total, one step earlier. *)
    bslots_auth -∗ bslots BSLOTS_FS ={E}=∗
    own_context cur_ctx ∗
    ∃ bn : bio_names, bio_ctx_old bn V ∗ bslots BSLOTS_FS.
  Proof.
    iIntros (Hnc0) "Hrun Hlkw #Hnm Hcpu Hfresh Hbufs Hlru Hpool Hsa Hsf".
    assert (Hu0 : uint (mword_of_int 0 : mword 32) = 0)
      by (vm_compute; reflexivity).
    (* the NBUF checkout tokens and the NBUF recycle tokens, as functions *)
    iMod (tok_fun_alloc NBUF 0) as (fown) "Htoks".
    iMod (tok_fun_alloc NBUF 0) as (fmid) "Hmids".
    (* the count authority (no buffer has a reference) and the slot supply *)
    iMod (own_alloc (● (∅ : gmap nat (Qp * positive)) : bioUR)) as (γb) "Hauth".
    { apply auth_auth_valid. intros i. rewrite lookup_empty. done. }
    (* the bcache spinlock's gname, BEFORE its resource can be stated *)
    iMod (newlock_delayed E bcache_addr "bcache"%string with "Hnm Hlkw Hcpu")
      as (γlk) "Hmk".
    (* every buffer's sleeplock, sealing exactly its checkout token *)
    iDestruct (big_sepL_sep_2 with "Hfresh Htoks") as "Hsl".
    (* A6.68: SEQUENTIAL, not NBUF independent fupds -- each
       [sl_fresh_new] borrows the running token and returns it. *)
    iAssert ([∗ list] idx↦k ∈ seq 0 NBUF,
               own_context cur_ctx -∗
               (sl_fresh (buf_lock (bnode k)) "buffer"%string ∗
                lock_tok_excl (fown k))
               ={E}=∗ own_context cur_ctx ∗
               (∃ p : gname * gname,
                  is_sleeplock (fst p) (snd p) (buf_lock (bnode k))
                    "buffer"%string (lock_tok_excl (fown k))))%I
      as "Hstep".
    { iApply big_sepL_intro. iIntros "!>" (idx k _) "Hrun [Hf Ht]".
      iMod (sl_fresh_new E (buf_lock (bnode k)) "buffer"%string
              (lock_tok_excl (fown k)) with "Hf Hrun Ht") as "[Hrun Hlk]".
      iDestruct "Hlk" as (γl γsl) "Hlk".
      iModIntro. iFrame "Hrun". iExists (γl, γsl). iExact "Hlk". }
    iMod (big_sepL_fupd_thread E (own_context cur_ctx)
            with "Hrun Hstep Hsl") as "[Hrun Hsl]".
    (* re-wrap: [seq_fun_alloc] takes a list of fupds *)
    iAssert ([∗ list] k ∈ seq 0 NBUF, |={E}=> ∃ p : gname * gname,
               is_sleeplock (fst p) (snd p) (buf_lock (bnode k))
                 "buffer"%string (lock_tok_excl (fown k)))%I
      with "[Hsl]" as "Hsl".
    { iApply (big_sepL_mono with "Hsl"). intros i k Hk.
      iIntros "H". by iModIntro. }
    iMod (seq_fun_alloc E
            (fun k p => is_sleeplock (fst p) (snd p) (buf_lock (bnode k))
                          "buffer"%string (lock_tok_excl (fown k)))
            NBUF 0 with "Hsl") as (fslk) "#Hsls".
    set (bn := MkBioNames γlk γb fslk fown fmid fmid fmid fmid fmid fmid fmid).
    (* every initial payload is empty: blockno 0 is uncovered *)
    assert (Hpay0 : forall k bs,
        buf_pay bn V k false (mword_of_int 0 : mword 32)
          (mword_of_int 0 : mword 32) bs = emp%I).
    { intros k bs. rewrite /buf_pay. case_decide as Hd; [|reflexivity].
      exfalso. apply Hnc0. rewrite -Hu0. exact Hd. }
    (* park every buffer's content in a fresh escrow, keeping the bcache half
       of dev/blockno and the refcnt cell for [bcache_res] *)
    iDestruct (big_sepL_sep_2 with "Hbufs Hmids") as "Hbm".
    iAssert (([∗ list] k ∈ seq 0 NBUF, |={E}=> buf_escrow bn V k) ∗
             ([∗ list] k ∈ seq 0 NBUF,
                bio_slot_res bn ∅ k (mword_of_int 0 : mword 32)
                  (mword_of_int 0 : mword 32)))%I
      with "[Hbm]" as "[Hesc Hslots]".
    { rewrite -big_sepL_sep. iApply (big_sepL_mono with "Hbm").
      intros i k Hk. iIntros "[(Hv & Hdk & Hdev & Hbno & Hrc & Hdata) Hmid]".
      (* the split every buffer's dev/blockno cell undergoes exactly once:
         one half into the escrow's parked bundle, one half into the bcache
         resource, forever. *)
      iDestruct (ctx_word4_pointsto_half_split with "Hdev") as "[Hdev1 Hdev2]".
      iDestruct (ctx_word4_pointsto_half_split with "Hbno") as "[Hbno1 Hbno2]".
      iDestruct "Hdata" as (bs) "[%Hlen Hdata]".
      iSplitR "Hrc Hdev2 Hbno2".
      - rewrite /buf_escrow.
        iApply (inv_alloc bioN E (buf_escrow_body bn V k)).
        iNext. iLeft. rewrite /buf_parked.
        iExists false, (mword_of_int 0 : mword 32),
                (mword_of_int 0 : mword 32), bs.
        rewrite Hpay0. cbv iota.
        iFrame "Hv Hdev1 Hmid". rewrite /buf_own.
        iFrame "Hbno1 Hdk Hdata". done.
      - rewrite /bio_slot_res lookup_empty. iFrame "Hrc Hdev2 Hbno2". }
    iMod (big_sepL_fupd with "Hesc") as "#Hescs".
    (* the initial pool covers the whole range: the zeroed slots claim only
       the uncovered 0 *)
    iAssert (bio_pool V (fun _ => (mword_of_int 0 : mword 32)))
      with "[Hpool]" as "Hpool".
    { rewrite /bio_pool.
      assert (Hc0 : bv_cov V ∖
                    bcache_cached (fun _ => (mword_of_int 0 : mword 32))
                    = bv_cov V).
      { apply set_eq. intros b. rewrite elem_of_difference. split.
        - intros [Hb _]. exact Hb.
        - intros Hb. split; [exact Hb|]. intros Hc.
          apply bcache_cached_spec in Hc as (j & Hj & ->).
          apply Hnc0. rewrite -Hu0. exact Hb. }
      rewrite Hc0. iExact "Hpool". }
    (* and seal the bcache lock over the assembled resource *)
    iMod ("Hmk" $! (<{ bcache_res bn V }>) with "[%] Hrun [Hauth Hsa Hslots Hlru Hpool]")
      as "[Hrun #Hlock]".
    { apply _. }
    { rewrite /bcache_res /bcache_scan.
      iExists ∅, (rev (seq 0 NBUF)),
        (fun _ => (mword_of_int 0 : mword 32)),
        (fun _ => (mword_of_int 0 : mword 32)).
      iFrame "Hauth Hsa".
      iSplitR.
      { iPureIntro. intros k [x Hx]. rewrite lookup_empty in Hx. done. }
      iSplitR.
      { iPureIntro. symmetry. apply Permutation_rev. }
      iSplitR.
      { iPureIntro. intros k1 k2 Hk1 Hk2 Hcov _.
        exfalso. apply Hnc0. rewrite -Hu0. exact Hcov. }
      iSplitR.
      { iPureIntro. intros k1 Hk1 Hcov.
        exfalso. apply Hnc0. rewrite -Hu0. exact Hcov. }
      assert (Hml : map bnode (rev (seq 0 NBUF)) = blist 0 NBUF)
        by (rewrite /blist map_rev //).
      rewrite Hml. iFrame "Hlru Hslots Hpool". }
    (* Split STRUCTURALLY before framing.  A bare [iFrame "H"] against this
       goal has to search [bio_ctx]'s big-op (NBUF sleeplocks + escrows) for
       each named hypothesis: the two frames here were 25 s of the file's
       46 s (measured 2026-08-03).  [iSplitR]/[iExact] name both sides, so
       nothing is searched. *)
    iModIntro. iSplitL "Hrun"; [iExact "Hrun" |]. iExists bn. rewrite /bio_ctx_old.
    iSplitR "Hsf"; [| iExact "Hsf"].
    iSplitL "Hlock"; [iExact "Hlock" |].
    rewrite big_sepL_sep. iSplitL "Hsls"; [iExact "Hsls" | iExact "Hescs"].
  Qed.
End BioInv.

Section BioBox.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ}.

  (* ------------------------------------------------------------------ *)
  (*  The two box arms, as context-λs                                     *)
  (* ------------------------------------------------------------------ *)

  (* the travelling content: [BioInv.buf_parked] minus [bmid], stated at
     an explicit context.  (bmid dies with the recycle window: the
     recycler works entirely inside bcache.lock's payload now.) *)
  Definition buf_bundle (bn : bio_names) (V : bio_view Σ) (k : nat)
      (ξ : CtxId) : iProp Σ :=
    (∃ (v : bool) (dev bno : mword 32) (bs : list (bv 8)),
       ctx_word4_pointsto ξ (b_valid (bpa k)) (DfracOwn 1)
         (if v then (mword_of_int 1 : mword 32) else (mword_of_int 0 : mword 32)) ∗
       ctx_word4_pointsto ξ (b_dev (bpa k)) (DfracOwn (1/2)) dev ∗
       buf_own (XI := ξ) (bpa k) bno (mword_of_int 0 : mword 32) bs ∗
       buf_pay (XI := ξ) bn V k v dev bno bs)%I.

  (* the chain residue: GHOST-ONLY (A6.148 revision).  The checkout's
     dev/blockno fractions stay with the chain thread -- the C code uses
     them -- so the OUT arm is context-free: no anchor traffic to enter
     or leave it, and the park needs no freshness premise. *)
  Definition buf_chain_res (bn : bio_names) (k : nat) : iProp Σ :=
    (∃ q : Qp, bref_tok bn k q ∗ bown bn k)%I.

  (* both arms are timeless: the box opener strips the ▷ up front *)
  Global Instance buf_bundle_timeless bn V k ξ : Timeless (buf_bundle bn V k ξ).
  Proof.
    rewrite /buf_bundle.
    apply bi.exist_timeless; intro v. apply bi.exist_timeless; intro dev.
    apply bi.exist_timeless; intro bno. apply bi.exist_timeless; intro bs.
    apply bi.sep_timeless; [apply _|]. apply bi.sep_timeless; [apply _|].
    apply bi.sep_timeless; apply _.
  Qed.
  Global Instance buf_chain_res_timeless bn k : Timeless (buf_chain_res bn k).
  Proof.
    rewrite /buf_chain_res /bown.
    apply bi.exist_timeless; intro q. apply bi.sep_timeless; apply _.
  Qed.

  (* cross-context exclusivity of a FULL word cell: the bump/park refute
     the PARKED arm with the full valid cell in hand, and the arm's copy
     lives at the (different) box context. *)
  Lemma ctx_word4_excl_x (ξ1 ξ2 : CtxId) (a : Arch.pa) (dq : dfrac)
      (w1 w2 : bv 32) :
    ctx_word4_pointsto ξ1 a (DfracOwn 1) w1 -∗
    ctx_word4_pointsto ξ2 a dq w2 -∗ False.
  Proof.
    iIntros "H1 H2".
    iDestruct "H1" as "[%Hal1 H1]". iDestruct "H2" as "[%Hal2 H2]".
    cbn [seq]. rewrite !big_sepL_cons.
    iDestruct "H1" as "[Hb1 _]". iDestruct "H2" as "[Hb2 _]".
    iDestruct (TsoCtx.ctx_pointsto_ne with "Hb1 Hb2") as %Hne. done.
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  The box                                                             *)
  (* ------------------------------------------------------------------ *)

  Definition bioxN : namespace := nroot .@ "xv6biox".

  (* ---- ENDGAME §3.2: the registers, the tag multiset, the pile ------ *)
  Definition reg_park (bn : bio_names) (k : nat) (r : nat * nat) : iProp Σ :=
    ghost_var (bn_regp bn k) (1/2) r.
  Definition reg_drop (bn : bio_names) (k : nat) (r : nat * nat) : iProp Σ :=
    ghost_var (bn_regd bn k) (1/2) r.
  Definition reg_cnt (bn : bio_names) (k : nat) (c : nat) : iProp Σ :=
    ghost_var (bn_regc bn k) (1/2) c.
  Definition tag_auth (bn : bio_names) (k : nat) (S : gmultiset nat) : iProp Σ :=
    own (bn_pile bn k) (● S).
  Definition tag_claim (bn : bio_names) (k : nat) (n : nat) : iProp Σ :=
    own (bn_pile bn k) (◯ {[+ n +]}).
  (* the parked references' fragments, one per tag *)
  Definition pile (bn : bio_names) (k : nat) (rb : nat * nat)
      (S : gmultiset nat) : iProp Σ :=
    ([∗ mset] _ ∈ S, pres_frag bn k rb)%I.

  Lemma tag_claim_elem bn k S n :
    tag_auth bn k S -∗ tag_claim bn k n -∗ ⌜n ∈ S⌝.
  Proof.
    iIntros "Ha Hc".
    iDestruct (own_valid_2 with "Ha Hc") as %[Hincl _]%auth_both_valid_discrete.
    iPureIntro. apply gmultiset_included in Hincl.
    by apply gmultiset_singleton_subseteq_l.
  Qed.

  Lemma tag_take bn k S n :
    tag_auth bn k S ==∗ tag_auth bn k (S ⊎ {[+ n +]}) ∗ tag_claim bn k n.
  Proof.
    iIntros "Ha". rewrite /tag_auth /tag_claim -own_op.
    iApply (own_update with "Ha").
    apply auth_update_alloc.
    rewrite -{2}(gmultiset_disj_union_left_id {[+ n +]}).
    apply gmultiset_local_update_alloc.
  Qed.

  Lemma tag_return bn k S n :
    tag_auth bn k S -∗ tag_claim bn k n ==∗ tag_auth bn k (S ∖ {[+ n +]}).
  Proof.
    iIntros "Ha Hc". iCombine "Ha Hc" as "H".
    iApply (own_update with "H").
    apply auth_update_dealloc.
    assert (Hε : (ε : gmultiset nat) = {[+ n +]} ∖ {[+ n +]}).
    { by rewrite gmultiset_difference_diag. }
    rewrite Hε. by apply gmultiset_local_update_dealloc.
  Qed.

  (* THE BOX (endgame §2/§3.2).  Common prefix: the anchor's custody, the
     park register's own stamp witnesses (what a decrement copies into the
     L1 row when it syncs rd := rp), the three registers (γp/γd halves;
     ● S), row (r2).  IDLE: ● None, the count half at 0, S = ∅ (which
     forces (r2) into rp = rd).  IN/OUT: ● Some((n_b,T_b), c) with the bump
     pair's witnesses, the count half, the pile of parked fragments over
     S, the tie, the bump generation at or below the current one, (r3). *)
  Definition buf_box_body (bn : bio_names) (V : bio_view Σ) (k : nat) : iProp Σ :=
    (∃ (n T : nat) (ξb : CtxId) (rp rd : nat * nat) (S : gmultiset nat),
       anchor (bn_anc bn k) n ξb T ∗
       astamp (bn_anc bn k) n T ∗
       llb loglen_name T ∗
       astamp (bn_anc bn k) rp.1 rp.2 ∗ llb loglen_name rp.2 ∗
       reg_park bn k rp ∗ reg_drop bn k rd ∗
       tag_auth bn k S ∗
       ⌜rp ≠ rd → rp.1 ∈ S⌝ ∗
       ((pres_none bn k ∗ reg_cnt bn k 0 ∗ ⌜S = ∅⌝)
        ∨ (∃ (rb : nat * nat) (c : positive),
             pres_auth bn k rb c ∗
             astamp (bn_anc bn k) rb.1 rb.2 ∗ llb loglen_name rb.2 ∗
             reg_cnt bn k (Pos.to_nat c) ∗
             pile bn k rb S ∗
             ⌜(n, T) = rb ∨ (n, T) = rp⌝ ∗
             ⌜(rb.1 ≤ n)%nat⌝ ∗
             ⌜∀ m, m ∈ S → (rb.1 < m)%nat⌝ ∗
             (buf_bundle bn V k ξb ∨ buf_chain_res bn k))))%I.

  Definition buf_box (bn : bio_names) (V : bio_view Σ) (k : nat) : iProp Σ :=
    inv bioxN (buf_box_body bn V k).

  (* ------------------------------------------------------------------ *)
  (*  Morphability of the arms (what deposit/withdraw transport)          *)
  (* ------------------------------------------------------------------ *)

  Global Instance buf_bundle_morph bn V k : CtxMorph (buf_bundle bn V k).
  Proof.
    rewrite /buf_bundle. apply ctx_morph_exist => v.
    apply ctx_morph_exist => dev. apply ctx_morph_exist => bno.
    apply ctx_morph_exist => bs.
    apply ctx_morph_sep; [apply ctx_morph_word4|].
    apply ctx_morph_sep; [apply ctx_morph_word4|].
    apply ctx_morph_sep.
    - rewrite /buf_own.
      apply ctx_morph_sep; [apply ctx_morph_word4|].
      apply ctx_morph_sep; [apply ctx_morph_word4|].
      apply ctx_morph_sep; [apply ctx_morph_const|].
      apply ctx_morph_big_sepL. intros i x. apply ctx_morph_pointsto.
    - rewrite /buf_pay.
      case_decide; [|apply ctx_morph_const].
      apply ctx_morph_sep; [apply ctx_morph_const|].
      destruct v.
      + apply ctx_morph_exist => bsd. apply ctx_morph_exist => d.
        apply ctx_morph_sep; [apply ctx_morph_const|].
        rewrite /bio_pay. destruct d.
        * apply ctx_morph_sep; [apply ctx_morph_const|].
          apply ctx_morph_exist => q.
          rewrite /bref.
          apply ctx_morph_sep; [apply ctx_morph_const|].
          apply ctx_morph_sep; [apply ctx_morph_const|].
          apply ctx_morph_sep; apply ctx_morph_word4.
        * apply ctx_morph_const.
      + apply ctx_morph_const.
  Qed.

  (* ================================================================== *)
  (*  The transitions (endgame §3.3), as fupds over the box invariant.    *)
  (* ================================================================== *)

  Local Lemma pos_to_nat_pos (c : positive) : (1 ≤ Pos.to_nat c)%nat.
  Proof. pose proof (Pos2Nat.is_pos c). lia. Qed.

  (* two same-buffer reference tokens overflow a count of one *)
  Lemma bref_tok_two bn (M : gmap nat (Qp * positive)) k q q' :
    M !! k = Some (q, 1%positive) ->
    own (bn_auth bn) (● M) -∗ bref_tok bn k q -∗ bref_tok bn k q' -∗ False.
  Proof.
    iIntros (HMk) "Ha H1 H2". rewrite /bref_tok.
    iDestruct (own_valid_3 with "Ha H1 H2") as %Hv.
    rewrite -assoc -auth_frag_op singleton_op -pair_op in Hv.
    apply auth_both_valid_discrete in Hv as [Hincl _].
    iPureIntro.
    apply singleton_included_l in Hincl as [y [Hy Hle]].
    apply leibniz_equiv in Hy. rewrite HMk in Hy.
    destruct y as [qt nn]. injection Hy as <- <-.
    apply Some_included in Hle as [Heq | Hlt].
    - destruct Heq as [_ Hn]; cbn in Hn. discriminate.
    - apply pair_included in Hlt as [_ Hp].
      apply pos_included in Hp. lia.
  Qed.

  (* two fragments against a count of one *)
  Local Lemma two_frags_absurd bn k rb rb1 rb2 :
    pres_auth bn k rb 1%positive -∗ pres_frag bn k rb1 -∗ pres_frag bn k rb2 -∗ False.
  Proof.
    iIntros "Ha H1 H2".
    iDestruct (pres_frag_agree with "Ha H1") as %->.
    iDestruct (pres_frag_agree with "Ha H2") as %->.
    rewrite /pres_auth /pres_frag.
    iDestruct (own_valid_3 with "Ha H1 H2") as %Hv.
    rewrite -assoc -auth_frag_op -Some_op -pair_op agree_idemp in Hv.
    apply auth_both_valid_discrete in Hv as [Hincl _].
    iPureIntro.
    apply Some_included in Hincl as [Heq | Hlt].
    - destruct Heq as [_ Hn]; cbn in Hn. discriminate.
    - apply pair_included in Hlt as [_ Hp]. apply pos_included in Hp. lia.
  Qed.

  (* the body, opened with its prefix named *)
  Local Ltac box_open Hbox Hcl :=
    iInv Hbox as (n T ξb rp rd Sm)
      "(>Hanc & >#Hst & >#Hllb & >#Hstp & >#Hllbp & >Hrp & >Hrd & >Hta & >%Hr2 & Harm)" Hcl.

  (* BUMP: refs 0 -> 1 under bcache.lock.  Content leaves the payload for
     the box (a free deposit); the presence authority steps to the new
     bump pair; the count half rises. *)
  Lemma box_swap_bump `{CID : RiscvLang.CpuId} (bn : bio_names) (V : bio_view Σ)
      (k : nat) (ξ : CtxId) (E : coPset) :
    ↑bioxN ⊆ E ->
    buf_box bn V k -∗
    TsoCtx.own_context ξ -∗
    reg_cnt bn k 0 -∗
    buf_bundle bn V k ξ ={E}=∗
    TsoCtx.own_context ξ ∗ reg_cnt bn k 1 ∗
    (∃ rb : nat * nat, pres_frag bn k rb ∗ astamp (bn_anc bn k) rb.1 rb.2 ∗
       llb loglen_name rb.2).
  Proof.
    iIntros (HE) "#Hbox Hrun Hcnt Hbun".
    box_open "Hbox" "Hcl".
    iDestruct "Harm" as "[(>Hpn & >Hc & >%HS) | Hin]"; last first.
    { iDestruct "Hin" as (rb c) "(_ & _ & _ & >Hc & _)".
      iDestruct (ghost_var_agree with "Hc Hcnt") as %Hc.
      exfalso. pose proof (pos_to_nat_pos c). lia. }
    iMod (anchor_deposit (buf_bundle bn V k) _ n ξ ξb T with "Hrun Hanc Hbun")
      as "(Hrun & %T' & %HTT' & Hanc & Hbun & #Hst' & #Hllb')".
    iMod (pres_none_take bn k (S n, T') with "Hpn") as "[Hpa Hpf]".
    iMod (ghost_var_update_2 1%nat with "Hc Hcnt") as "[Hc Hcnt]"; [by rewrite Qp.half_half|].
    iMod ("Hcl" with "[Hanc Hrp Hrd Hta Hpa Hc Hbun]") as "_".
    { iNext. iExists (S n), T', ξb, rp, rd, Sm.
      iFrame "Hanc Hrp Hrd Hta".
      iSplitR; [iExact "Hst'"|]. iSplitR; [iExact "Hllb'"|].
      iSplitR; [iExact "Hstp"|]. iSplitR; [iExact "Hllbp"|]. iSplitR; [done|].
      iRight. iExists (S n, T'), 1%positive.
      iFrame "Hpa Hc". iSplitR; [iExact "Hst'"|]. iSplitR; [iExact "Hllb'"|].
      iSplitR; [rewrite /pile HS big_sepMS_empty; iEmpIntro|].
      iSplitR; [iPureIntro; by left|].
      iSplitR; [iPureIntro; cbn; lia|].
      iSplitR; [iPureIntro; intros m Hm; rewrite HS in Hm; by apply gmultiset_not_elem_of_empty in Hm|].
      iLeft. iExact "Hbun". }
    iModIntro. iFrame "Hrun Hcnt".
    iExists (S n, T'). iFrame "Hpf". iSplit; [iExact "Hst'" | iExact "Hllb'"].
  Qed.

  (* REFS++ at refs >= 1 under bcache.lock: another fragment at the same
     bump pair, its witnesses copied out of the box. *)
  Lemma box_ref_another (bn : bio_names) (V : bio_view Σ) (k : nat)
      (c : positive) (E : coPset) :
    ↑bioxN ⊆ E ->
    buf_box bn V k -∗
    reg_cnt bn k (Pos.to_nat c) ={E}=∗
    reg_cnt bn k (Pos.to_nat (c + 1)) ∗
    (∃ rb : nat * nat, pres_frag bn k rb ∗ astamp (bn_anc bn k) rb.1 rb.2 ∗
       llb loglen_name rb.2).
  Proof.
    iIntros (HE) "#Hbox Hcnt".
    box_open "Hbox" "Hcl".
    iDestruct "Harm" as "[(_ & >Hc & _) | Hin]".
    { iDestruct (ghost_var_agree with "Hc Hcnt") as %Hc.
      exfalso. pose proof (pos_to_nat_pos c). lia. }
    iDestruct "Hin" as (rb c') "(>Hpa & >#Hstb & >#Hllbb & >Hc & Hpile & >%Htie & >%Hbn & >%Hr3 & Harm)".
    iDestruct (ghost_var_agree with "Hc Hcnt") as %Hc.
    assert (c' = c) as -> by (apply Pos2Nat.inj; lia).
    iMod (pres_take_another with "Hpa") as "[Hpa Hpf]".
    iMod (ghost_var_update_2 (Pos.to_nat (c + 1)) with "Hc Hcnt") as "[Hc Hcnt]"; [by rewrite Qp.half_half|].
    iMod ("Hcl" with "[Hanc Hrp Hrd Hta Hpa Hc Hpile Harm]") as "_".
    { iNext. iExists n, T, ξb, rp, rd, Sm.
      iFrame "Hanc Hrp Hrd Hta".
      iSplitR; [iExact "Hst"|]. iSplitR; [iExact "Hllb"|].
      iSplitR; [iExact "Hstp"|]. iSplitR; [iExact "Hllbp"|]. iSplitR; [done|].
      iRight. iExists rb, (c + 1)%positive.
      iFrame "Hpa Hc Hpile Hstb Hllbb Harm". iPureIntro. auto. }
    iModIntro. iFrame "Hcnt". iExists rb. iFrame "Hpf". iSplit; [iExact "Hstb" | iExact "Hllbb"].
  Qed.

  (* REFS-- at refs >= 2 under bcache.lock, the fragment IN HAND (bunpin).
     Every decrement syncs reg_drop := reg_park, re-establishing (r2). *)
  Lemma box_ref_drop_hand (bn : bio_names) (V : bio_view Σ) (k : nat)
      (c : positive) (rb' rd0 : nat * nat) (E : coPset) :
    ↑bioxN ⊆ E ->
    buf_box bn V k -∗
    reg_cnt bn k (Pos.to_nat (c + 1)) -∗
    pres_frag bn k rb' -∗
    reg_drop bn k rd0 ={E}=∗
    reg_cnt bn k (Pos.to_nat c) ∗
    (∃ rp : nat * nat, reg_drop bn k rp ∗ astamp (bn_anc bn k) rp.1 rp.2 ∗
       llb loglen_name rp.2).
  Proof.
    iIntros (HE) "#Hbox Hcnt Hpf Hrd0".
    box_open "Hbox" "Hcl".
    iDestruct "Harm" as "[(_ & >Hc & _) | Hin]".
    { iDestruct (ghost_var_agree with "Hc Hcnt") as %Hc.
      exfalso. pose proof (pos_to_nat_pos (c + 1)). lia. }
    iDestruct "Hin" as (rb c') "(>Hpa & >#Hstb & >#Hllbb & >Hc & Hpile & >%Htie & >%Hbn & >%Hr3 & Harm)".
    iDestruct (ghost_var_agree with "Hc Hcnt") as %Hc.
    assert (c' = (1 + c)%positive) as ->.
    { apply Pos2Nat.inj. rewrite Pos2Nat.inj_add. rewrite Pos2Nat.inj_add in Hc. lia. }
    iDestruct (pres_frag_agree with "Hpa Hpf") as %->.
    iMod (pres_drop_one with "Hpa Hpf") as "Hpa".
    iMod (ghost_var_update_2 (Pos.to_nat c) with "Hc Hcnt") as "[Hc Hcnt]"; [by rewrite Qp.half_half|].
    iMod (ghost_var_update_2 rp with "Hrd Hrd0") as "[Hrd Hrd0]"; [by rewrite Qp.half_half|].
    iMod ("Hcl" with "[Hanc Hrp Hrd Hta Hpa Hc Hpile Harm]") as "_".
    { iNext. iExists n, T, ξb, rp, rp, Sm.
      iFrame "Hanc Hrp Hrd Hta".
      iSplitR; [iExact "Hst"|]. iSplitR; [iExact "Hllb"|].
      iSplitR; [iExact "Hstp"|]. iSplitR; [iExact "Hllbp"|].
      iSplitR; [iPureIntro; intros Hne; done|].
      iRight. iExists rb, c.
      iFrame "Hpa Hc Hpile Hstb Hllbb Harm". iPureIntro. auto. }
    iModIntro. iFrame "Hcnt". iExists rp. iFrame "Hrd0". iSplit; [iExact "Hstp" | iExact "Hllbp"].
  Qed.

  (* REFS-- at refs >= 2 under bcache.lock, the fragment IN THE PILE (an
     ex-parker's brelse): the claim selects it. *)
  Lemma box_ref_drop_pile (bn : bio_names) (V : bio_view Σ) (k : nat)
      (c : positive) (nP : nat) (rd0 : nat * nat) (E : coPset) :
    ↑bioxN ⊆ E ->
    buf_box bn V k -∗
    reg_cnt bn k (Pos.to_nat (c + 1)) -∗
    tag_claim bn k nP -∗
    reg_drop bn k rd0 ={E}=∗
    reg_cnt bn k (Pos.to_nat c) ∗
    (∃ rp : nat * nat, reg_drop bn k rp ∗ astamp (bn_anc bn k) rp.1 rp.2 ∗
       llb loglen_name rp.2).
  Proof.
    iIntros (HE) "#Hbox Hcnt Hclaim Hrd0".
    box_open "Hbox" "Hcl".
    iDestruct (tag_claim_elem with "Hta Hclaim") as %HnS.
    iDestruct "Harm" as "[(_ & >Hc & _) | Hin]".
    { iDestruct (ghost_var_agree with "Hc Hcnt") as %Hc.
      exfalso. pose proof (pos_to_nat_pos (c + 1)). lia. }
    iDestruct "Hin" as (rb c') "(>Hpa & >#Hstb & >#Hllbb & >Hc & Hpile & >%Htie & >%Hbn & >%Hr3 & Harm)".
    iDestruct (ghost_var_agree with "Hc Hcnt") as %Hc.
    assert (c' = (1 + c)%positive) as ->.
    { apply Pos2Nat.inj. rewrite Pos2Nat.inj_add. rewrite Pos2Nat.inj_add in Hc. lia. }
    rewrite /pile (big_sepMS_delete _ _ nP HnS).
    iDestruct "Hpile" as "[>Hpf Hpile]".
    iMod (pres_drop_one with "Hpa Hpf") as "Hpa".
    iMod (tag_return with "Hta Hclaim") as "Hta".
    iMod (ghost_var_update_2 (Pos.to_nat c) with "Hc Hcnt") as "[Hc Hcnt]"; [by rewrite Qp.half_half|].
    iMod (ghost_var_update_2 rp with "Hrd Hrd0") as "[Hrd Hrd0]"; [by rewrite Qp.half_half|].
    iMod ("Hcl" with "[Hanc Hrp Hrd Hta Hpa Hc Hpile Harm]") as "_".
    { iNext. iExists n, T, ξb, rp, rp, (Sm ∖ {[+ nP +]}).
      iFrame "Hanc Hrp Hrd Hta".
      iSplitR; [iExact "Hst"|]. iSplitR; [iExact "Hllb"|].
      iSplitR; [iExact "Hstp"|]. iSplitR; [iExact "Hllbp"|].
      iSplitR; [iPureIntro; intros Hne; done|].
      iRight. iExists rb, c.
      iFrame "Hpa Hc Hpile Hstb Hllbb Harm".
      iPureIntro. split_and!; [exact Htie | exact Hbn |].
      intros m Hm. apply Hr3. eapply gmultiset_elem_of_subseteq; [exact Hm|].
      intros x. rewrite multiplicity_difference. lia. }
    iModIntro. iFrame "Hcnt". iExists rp. iFrame "Hrd0". iSplit; [iExact "Hstp" | iExact "Hllbp"].
  Qed.

  (* CHECKOUT (IN -> OUT) under the sleeplock: the winner brings its
     fragment with the R1 pair for the bump stamp, and the payload's park
     half with the R2 floor for the park stamp; the tie picks. *)
  Lemma box_swap_checkout `{CID : RiscvLang.CpuId} (bn : bio_names)
      (V : bio_view Σ) (k : nat) (ξ : CtxId) (q : Qp) (rb' rp' : nat * nat)
      (K1 K2 : nat) (E : coPset) :
    ↑bioxN ⊆ E ->
    (rb'.2 <= K1)%nat -> (rp'.2 <= K2)%nat ->
    buf_box bn V k -∗
    TsoCtx.own_context ξ -∗
    TsoCtx.ctx_floor ξ K1 -∗
    TsoCtx.ctx_floor ξ K2 -∗
    pres_frag bn k rb' -∗
    reg_park bn k rp' -∗
    bown bn k -∗
    bref_tok bn k q ={E}=∗
    TsoCtx.own_context ξ ∗ pres_frag bn k rb' ∗ reg_park bn k rp' ∗
    buf_bundle bn V k ξ.
  Proof.
    iIntros (HE HK1 HK2) "#Hbox Hrun #Hfl1 #Hfl2 Hpf Hrp' Hbo Hbr".
    box_open "Hbox" "Hcl".
    iDestruct "Harm" as "[(>Hpn & _) | Hin]".
    { iDestruct (pres_frag_none_absurd with "Hpf Hpn") as %[]. }
    iDestruct "Hin" as (rb c) "(>Hpa & >#Hstb & >#Hllbb & >Hc & Hpile & >%Htie & >%Hbn & >%Hr3 & Harm)".
    iDestruct (pres_frag_agree with "Hpa Hpf") as %->.
    iDestruct (ghost_var_agree with "Hrp Hrp'") as %->.
    iAssert (aguard (bn_anc bn k) n ξ) as "#Hgrd".
    { destruct Htie as [Heq | Heq].
      - iApply (aguard_intro _ n T ξ K1 with "Hst Hfl1").
        rewrite -Heq in HK1. exact HK1.
      - iApply (aguard_intro _ n T ξ K2 with "Hst Hfl2").
        rewrite -Heq in HK2. exact HK2. }
    iDestruct "Harm" as "[>Hbun | >Hres]"; last first.
    { iDestruct "Hres" as (q') "[_ Hbo2]".
      iDestruct (bown_exclusive with "Hbo Hbo2") as %[]. }
    iMod (anchor_withdraw (buf_bundle bn V k) _ n ξ ξb T
            with "Hrun Hgrd Hanc Hbun") as "(Hrun & Hanc & Hbun)".
    iMod ("Hcl" with "[Hanc Hrp Hrd Hta Hpa Hc Hpile Hbo Hbr]") as "_".
    { iNext. iExists n, T, ξb, rp', rd, Sm.
      iFrame "Hanc Hrp Hrd Hta".
      iSplitR; [iExact "Hst"|]. iSplitR; [iExact "Hllb"|].
      iSplitR; [iExact "Hstp"|]. iSplitR; [iExact "Hllbp"|]. iSplitR; [done|].
      iRight. iExists rb, c. iFrame "Hpa Hc Hpile Hstb Hllbb".
      iSplitR; [done|]. iSplitR; [done|]. iSplitR; [done|].
      iRight. iExists q. iFrame "Hbr Hbo". }
    iModIntro. iFrame "Hrun Hpf Hrp' Hbun".
  Qed.

  (* PARK (OUT -> IN) under the sleeplock: a free deposit; the park register
     and its witnesses move to the new stamp, the parker's fragment joins
     the pile under a fresh tag, and the parker walks away with the claim
     and the payload residue. *)
  Lemma box_swap_park `{CID : RiscvLang.CpuId} (bn : bio_names)
      (V : bio_view Σ) (k : nat) (ξ : CtxId) (rb' rp' : nat * nat) (E : coPset) :
    ↑bioxN ⊆ E ->
    buf_box bn V k -∗
    TsoCtx.own_context ξ -∗
    buf_bundle bn V k ξ -∗
    pres_frag bn k rb' -∗
    reg_park bn k rp' ={E}=∗
    TsoCtx.own_context ξ ∗
    (∃ r : nat * nat, reg_park bn k r ∗ tag_claim bn k r.1 ∗
       astamp (bn_anc bn k) r.1 r.2 ∗ llb loglen_name r.2) ∗
    bown bn k ∗ (∃ q : Qp, bref_tok bn k q).
  Proof.
    iIntros (HE) "#Hbox Hrun Hbun Hpf Hrp'".
    box_open "Hbox" "Hcl".
    iDestruct "Harm" as "[(>Hpn & _) | Hin]".
    { iDestruct (pres_frag_none_absurd with "Hpf Hpn") as %[]. }
    iDestruct "Hin" as (rb c) "(>Hpa & >#Hstb & >#Hllbb & >Hc & Hpile & >%Htie & >%Hbn & >%Hr3 & Harm)".
    iDestruct (pres_frag_agree with "Hpa Hpf") as %->.
    iDestruct (ghost_var_agree with "Hrp Hrp'") as %->.
    iDestruct "Harm" as "[>Hbun2 | >Hres]".
    { iDestruct "Hbun" as (v1 d1 b1 bs1) "(Hv1 & _)".
      iDestruct "Hbun2" as (v2 d2 b2 bs2) "(Hv2 & _)".
      iDestruct (ctx_word4_excl_x ξ ξb (b_valid (bpa k)) (DfracOwn 1)
                   with "Hv1 Hv2") as %[]. }
    iDestruct "Hres" as (q') "[Hbr Hbo]".
    iMod (anchor_deposit (buf_bundle bn V k) _ n ξ ξb T with "Hrun Hanc Hbun")
      as "(Hrun & %T' & %HTT' & Hanc & Hbun & #Hst' & #Hllb')".
    iMod (ghost_var_update_2 (S n, T') with "Hrp Hrp'") as "[Hrp Hrp']"; [by rewrite Qp.half_half|].
    iMod (tag_take bn k Sm (S n) with "Hta") as "[Hta Hclaim]".
    iMod ("Hcl" with "[Hanc Hrp Hrd Hta Hpa Hc Hpile Hpf Hbun]") as "_".
    { iNext. iExists (S n), T', ξb, (S n, T'), rd, (Sm ⊎ {[+ S n +]}).
      iFrame "Hanc Hrp Hrd Hta".
      iSplitR; [iExact "Hst'"|]. iSplitR; [iExact "Hllb'"|].
      iSplitR; [iExact "Hst'"|]. iSplitR; [iExact "Hllb'"|].
      iSplitR.
      { iPureIntro. intros _. cbn. apply gmultiset_elem_of_disj_union. right.
        by apply gmultiset_elem_of_singleton. }
      iRight. iExists rb, c. iFrame "Hpa Hc Hstb Hllbb".
      rewrite /pile big_sepMS_disj_union big_sepMS_singleton. iFrame "Hpile Hpf".
      iSplitR; [iPureIntro; by right|].
      iSplitR; [iPureIntro; cbn; lia|].
      iSplitR.
      { iPureIntro. intros m Hm. apply gmultiset_elem_of_disj_union in Hm as [Hm | Hm].
        - by apply Hr3.
        - apply gmultiset_elem_of_singleton in Hm. subst m. lia. }
      iLeft. iExact "Hbun". }
    iModIntro. iFrame "Hrun Hbo".
    iSplitL "Hrp' Hclaim".
    { iExists (S n, T'). iFrame "Hrp' Hclaim". iSplit; [iExact "Hst'" | iExact "Hllb'"]. }
    iExists q'. iFrame "Hbr".
  Qed.

  (* DROP (IN -> IDLE), refs 1 -> 0 under bcache.lock, the fragment IN HAND
     (bunpin's last reference): the withdraw's floor is the bump pair's R1
     floor or the L1 row's for reg_drop -- the tie and (r2) decide. *)
  Lemma box_swap_drop_hand `{CID : RiscvLang.CpuId} (bn : bio_names)
      (V : bio_view Σ) (k : nat) (M : gmap nat (Qp * positive)) (q : Qp)
      (ξ : CtxId) (rb' rd0 : nat * nat) (Kb Kd : nat) (E : coPset) :
    ↑bioxN ⊆ E ->
    M !! k = Some (q, 1%positive) ->
    (rb'.2 <= Kb)%nat -> (rd0.2 <= Kd)%nat ->
    buf_box bn V k -∗
    TsoCtx.own_context ξ -∗
    TsoCtx.ctx_floor ξ Kb -∗
    TsoCtx.ctx_floor ξ Kd -∗
    own (bn_auth bn) (● M) -∗
    bref_tok bn k q -∗
    reg_cnt bn k 1 -∗
    pres_frag bn k rb' -∗
    reg_drop bn k rd0 ={E}=∗
    TsoCtx.own_context ξ ∗ own (bn_auth bn) (● M) ∗ bref_tok bn k q ∗
    reg_cnt bn k 0 ∗
    (∃ rp : nat * nat, reg_drop bn k rp ∗ astamp (bn_anc bn k) rp.1 rp.2 ∗
       llb loglen_name rp.2) ∗
    buf_bundle bn V k ξ.
  Proof.
    iIntros (HE HMk HKb HKd) "#Hbox Hrun #Hflb #Hfld Ha Hbr Hcnt Hpf Hrd0".
    box_open "Hbox" "Hcl".
    iDestruct "Harm" as "[(_ & >Hc & _) | Hin]".
    { iDestruct (ghost_var_agree with "Hc Hcnt") as %Hc. exfalso. lia. }
    iDestruct "Hin" as (rb c) "(>Hpa & >#Hstb & >#Hllbb & >Hc & Hpile & >%Htie & >%Hbn & >%Hr3 & Harm)".
    iDestruct (ghost_var_agree with "Hc Hcnt") as %Hc.
    assert (c = 1%positive) as -> by (apply Pos2Nat.inj; cbn; lia).
    iDestruct (pres_frag_agree with "Hpa Hpf") as %->.
    (* the pile is empty: a second fragment beside the one in hand *)
    destruct (decide (Sm = ∅)) as [-> | HSne]; last first.
    { apply gmultiset_choose in HSne as [x Hx].
      rewrite /pile (big_sepMS_delete _ _ x Hx).
      iDestruct "Hpile" as "[>Hpf2 _]".
      iDestruct (two_frags_absurd with "Hpa Hpf Hpf2") as %[]. }
    assert (rp = rd) as <-.
    { destruct (decide (rp = rd)) as [? | Hne]; [done|].
      specialize (Hr2 Hne). by apply gmultiset_not_elem_of_empty in Hr2. }
    iDestruct (ghost_var_agree with "Hrd Hrd0") as %->.
    iAssert (aguard (bn_anc bn k) n ξ) as "#Hgrd".
    { destruct Htie as [Heq | Heq].
      - iApply (aguard_intro _ n T ξ Kb with "Hst Hflb"). rewrite -Heq in HKb. exact HKb.
      - iApply (aguard_intro _ n T ξ Kd with "Hst Hfld"). rewrite -Heq in HKd. exact HKd. }
    iDestruct "Harm" as "[>Hbun | >Hres]"; last first.
    { iDestruct "Hres" as (q') "[Hbr2 _]".
      iDestruct (bref_tok_two bn M k q q' HMk with "Ha Hbr Hbr2") as %[]. }
    iMod (anchor_withdraw (buf_bundle bn V k) _ n ξ ξb T
            with "Hrun Hgrd Hanc Hbun") as "(Hrun & Hanc & Hbun)".
    iMod (pres_last_drop with "Hpa Hpf") as "Hpn".
    iMod (ghost_var_update_2 0%nat with "Hc Hcnt") as "[Hc Hcnt]"; [by rewrite Qp.half_half|].
    iMod ("Hcl" with "[Hanc Hrp Hrd Hta Hpn Hc]") as "_".
    { iNext. iExists n, T, ξb, rd0, rd0, ∅.
      iFrame "Hanc Hrp Hrd Hta".
      iSplitR; [iExact "Hst"|]. iSplitR; [iExact "Hllb"|].
      iSplitR; [iExact "Hstp"|]. iSplitR; [iExact "Hllbp"|].
      iSplitR; [iPureIntro; intros Hne; done|].
      iLeft. iFrame "Hpn Hc". done. }
    iModIntro. iFrame "Hrun Ha Hbr Hcnt Hbun".
    iExists rd0. iFrame "Hrd0". iSplit; [iExact "Hstp" | iExact "Hllbp"].
  Qed.

  (* DROP (IN -> IDLE), refs 1 -> 0 under bcache.lock, the fragment IN THE
     PILE (brelse: the dropper parked): the claim selects it; the bump case
     is refuted by (r3) + astamp_le; the park case is bounded by the
     dropper's own park stamp or by the L1 row. *)
  Lemma box_swap_drop_pile `{CID : RiscvLang.CpuId} (bn : bio_names)
      (V : bio_view Σ) (k : nat) (M : gmap nat (Qp * positive)) (q : Qp)
      (ξ : CtxId) (nm Tm : nat) (rd0 : nat * nat) (Km Kd : nat) (E : coPset) :
    ↑bioxN ⊆ E ->
    M !! k = Some (q, 1%positive) ->
    (Tm <= Km)%nat -> (rd0.2 <= Kd)%nat ->
    buf_box bn V k -∗
    TsoCtx.own_context ξ -∗
    TsoCtx.ctx_floor ξ Km -∗
    TsoCtx.ctx_floor ξ Kd -∗
    own (bn_auth bn) (● M) -∗
    bref_tok bn k q -∗
    reg_cnt bn k 1 -∗
    tag_claim bn k nm -∗
    astamp (bn_anc bn k) nm Tm -∗
    reg_drop bn k rd0 ={E}=∗
    TsoCtx.own_context ξ ∗ own (bn_auth bn) (● M) ∗ bref_tok bn k q ∗
    reg_cnt bn k 0 ∗
    (∃ rp : nat * nat, reg_drop bn k rp ∗ astamp (bn_anc bn k) rp.1 rp.2 ∗
       llb loglen_name rp.2) ∗
    buf_bundle bn V k ξ.
  Proof.
    iIntros (HE HMk HKm HKd) "#Hbox Hrun #Hflm #Hfld Ha Hbr Hcnt Hclaim #Hstm Hrd0".
    box_open "Hbox" "Hcl".
    iDestruct (tag_claim_elem with "Hta Hclaim") as %HnS.
    iDestruct "Harm" as "[(_ & >Hc & _) | Hin]".
    { iDestruct (ghost_var_agree with "Hc Hcnt") as %Hc. exfalso. lia. }
    iDestruct "Hin" as (rb c) "(>Hpa & >#Hstb & >#Hllbb & >Hc & Hpile & >%Htie & >%Hbn & >%Hr3 & Harm)".
    iDestruct (ghost_var_agree with "Hc Hcnt") as %Hc.
    assert (c = 1%positive) as -> by (apply Pos2Nat.inj; cbn; lia).
    (* the pile is exactly the dropper's fragment *)
    rewrite /pile (big_sepMS_delete _ _ nm HnS).
    iDestruct "Hpile" as "[>Hpf Hpile]".
    destruct (decide (Sm ∖ {[+ nm +]} = ∅)) as [HS1 | HSne]; last first.
    { apply gmultiset_choose in HSne as [x Hx].
      rewrite (big_sepMS_delete _ _ x Hx).
      iDestruct "Hpile" as "[>Hpf2 _]".
      iDestruct (two_frags_absurd with "Hpa Hpf Hpf2") as %[]. }
    iDestruct (astamp_le with "Hanc Hstm") as %Hnm_le.
    iAssert (aguard (bn_anc bn k) n ξ) as "#Hgrd".
    { destruct Htie as [Heq | Heq].
      - (* the bump case is refuted: the park generation exceeds the bump's *)
        exfalso. specialize (Hr3 nm HnS). rewrite -Heq in Hr3. cbn in Hr3. lia.
      - destruct (decide (rp = rd)) as [Hprd | Hne].
        + iDestruct (ghost_var_agree with "Hrd Hrd0") as %->.
          iApply (aguard_intro _ n T ξ Kd with "Hst Hfld").
          rewrite Hprd in Heq. rewrite -Heq in HKd. exact HKd.
        + specialize (Hr2 Hne).
          assert (rp.1 = nm) as Hrpn.
          { rewrite (gmultiset_disj_union_difference' _ _ HnS) HS1 in Hr2.
            apply gmultiset_elem_of_disj_union in Hr2 as [Hr2 | Hr2];
              [by apply gmultiset_elem_of_singleton in Hr2 |].
            by apply gmultiset_not_elem_of_empty in Hr2. }
          assert (n = nm) as -> by (rewrite -Heq in Hrpn; cbn in Hrpn; exact Hrpn).
          iDestruct (astamp_agree with "Hanc Hstm") as %HTm.
          iApply (aguard_intro _ nm T ξ Km with "Hst Hflm"). rewrite -HTm. exact HKm. }
    iDestruct "Harm" as "[>Hbun | >Hres]"; last first.
    { iDestruct "Hres" as (q') "[Hbr2 _]".
      iDestruct (bref_tok_two bn M k q q' HMk with "Ha Hbr Hbr2") as %[]. }
    iMod (anchor_withdraw (buf_bundle bn V k) _ n ξ ξb T
            with "Hrun Hgrd Hanc Hbun") as "(Hrun & Hanc & Hbun)".
    iMod (pres_last_drop with "Hpa Hpf") as "Hpn".
    iMod (tag_return with "Hta Hclaim") as "Hta".
    iMod (ghost_var_update_2 0%nat with "Hc Hcnt") as "[Hc Hcnt]"; [by rewrite Qp.half_half|].
    iMod (ghost_var_update_2 rp with "Hrd Hrd0") as "[Hrd Hrd0]"; [by rewrite Qp.half_half|].
    iMod ("Hcl" with "[Hanc Hrp Hrd Hta Hpn Hc]") as "_".
    { iNext. iExists n, T, ξb, rp, rp, (Sm ∖ {[+ nm +]}).
      iFrame "Hanc Hrp Hrd Hta".
      iSplitR; [iExact "Hst"|]. iSplitR; [iExact "Hllb"|].
      iSplitR; [iExact "Hstp"|]. iSplitR; [iExact "Hllbp"|].
      iSplitR; [iPureIntro; intros Hne; done|].
      iLeft. iFrame "Hpn Hc". done. }
    iModIntro. iFrame "Hrun Ha Hbr Hcnt Hbun".
    iExists rp. iFrame "Hrd0". iSplit; [iExact "Hstp" | iExact "Hllbp"].
  Qed.

  (* ================================================================== *)
  (*  The payload side (v2, A6.142): refs-0 custody in bcache.lock.       *)
  (*  Stated as context-λs -- the lock payload re-indexes at each acquire. *)
  (* ================================================================== *)

  (* the L1 row of endgame §3.2: the drop register's payload half with its
     stamp witnesses, bounded by the payload-level floor slot [tl] *)
  Definition bslot_regs (bn : bio_names) (k : nat) (tl : nat) : iProp Σ :=
    (∃ rd : nat * nat, reg_drop bn k rd ∗ astamp (bn_anc bn k) rd.1 rd.2 ∗
       llb loglen_name rd.2 ∗ ⌜(rd.2 ≤ tl)%nat⌝)%I.

  Definition bio_slot_res2 (bn : bio_names) (V : bio_view Σ)
      (M : gmap nat (Qp * positive)) (k : nat) (dev bno : mword 32)
      (tl : nat) (ξ : CtxId) : iProp Σ :=
    bslot_regs bn k tl ∗
    match M !! k with
    | None =>
        (ctx_word4_pointsto ξ (brefcnt k) (DfracOwn 1) (mword_of_int 0 : mword 32) ∗
         reg_cnt bn k 0 ∗
         (∃ (v : bool) (bs : list (bv 8)),
            ctx_word4_pointsto ξ (b_valid (bpa k)) (DfracOwn 1)
              (if v then (mword_of_int 1 : mword 32) else (mword_of_int 0 : mword 32)) ∗
            ctx_word4_pointsto ξ (b_dev (bpa k)) (DfracOwn 1) dev ∗
            buf_own (XI := ξ) (bpa k) bno (mword_of_int 0 : mword 32) bs ∗
            ctx_word4_pointsto ξ (b_blockno (bpa k)) (DfracOwn (1/2)) bno ∗
            buf_pay (XI := ξ) bn V k v dev bno bs))%I
    | Some (q, n) =>
        (⌜(Z.pos n < 2 ^ 31)%Z⌝ ∗
         ctx_word4_pointsto ξ (brefcnt k) (DfracOwn 1)
           (mword_of_int (Z.pos n) : mword 32) ∗
         bslots (Pos.to_nat n) ∗
         reg_cnt bn k (Pos.to_nat n) ∗
         ∃ qr : Qp, ⌜(q + qr)%Qp = (1/2)%Qp⌝ ∗
           ctx_word4_pointsto ξ (b_dev (bpa k)) (DfracOwn qr) dev ∗
           ctx_word4_pointsto ξ (b_blockno (bpa k)) (DfracOwn qr) bno)%I
    end.

  Definition bcache_scan2 (bn : bio_names) (V : bio_view Σ)
      (M : gmap nat (Qp * positive)) (ord : list nat)
      (devs bnos : nat -> mword 32) (tl : nat) (ξ : CtxId) : iProp Σ :=
    (own (bn_auth bn) (● M) ∗
     bslots_auth ∗
     ⌜∀ k, is_Some (M !! k) -> (k < NBUF)%nat⌝ ∗
     ⌜ord ≡ₚ seq 0 NBUF⌝ ∗
     ⌜∀ k1 k2, (k1 < NBUF)%nat -> (k2 < NBUF)%nat ->
        uint (bnos k1) ∈ bv_cov V ->
        uint (bnos k1) = uint (bnos k2) -> k1 = k2⌝ ∗
     ⌜∀ k, (k < NBUF)%nat -> uint (bnos k) ∈ bv_cov V ->
        devs k = bv_dev V⌝ ∗
     bcache_lru (XI := ξ) bhead (map bnode ord) ∗
     bio_pool V bnos ∗
     [∗ list] k ∈ seq 0 NBUF, bio_slot_res2 bn V M k (devs k) (bnos k) tl ξ)%I.

  (* the payload, with its floor slot: R2 folds the releaser's llb here
     ([lock_pay_intro_llb] with [bcache_scan2] as the unfloored body) *)
  Definition bcache_res2 (bn : bio_names) (V : bio_view Σ) (ξ : CtxId) : iProp Σ :=
    (∃ (M : gmap nat (Qp * positive)) (ord : list nat)
       (devs bnos : nat -> mword 32) (tl : nat),
       TsoCtx.ctx_floor ξ tl ∗ bcache_scan2 bn V M ord devs bnos tl ξ)%I.

  Lemma bcache_res2_fold bn V M ord devs bnos tl (ξ : CtxId) :
    bcache_scan2 bn V M ord devs bnos tl ξ ∗ TsoCtx.ctx_floor ξ tl ⊢ bcache_res2 bn V ξ.
  Proof. iIntros "[Hb #Hfl]". iExists M, ord, devs, bnos, tl. iFrame "Hfl Hb". Qed.

  (* ---- morphability ------------------------------------------------- *)

  Lemma bseg_morph (h : mword 64) :
    forall (l : list (mword 64)) (prev : mword 64),
      CtxMorph (fun ξ => bseg (XI := ξ) h prev l).
  Proof.
    induction l as [|a l' IH]; intros prev; cbn [bseg].
    - apply ctx_morph_const.
    - apply ctx_morph_sep; [apply ctx_morph_word|].
      apply ctx_morph_sep; [apply ctx_morph_word|].
      apply IH.
  Qed.

  Global Instance bcache_lru_morph h l :
    CtxMorph (fun ξ => bcache_lru (XI := ξ) h l).
  Proof.
    rewrite /bcache_lru.
    apply ctx_morph_sep; [apply ctx_morph_word|].
    apply ctx_morph_sep; [apply ctx_morph_word|].
    apply bseg_morph.
  Qed.

  Local Instance buf_pay_morph bn V k v dev bno bs :
    CtxMorph (fun ξ => buf_pay (XI := ξ) bn V k v dev bno bs).
  Proof.
    rewrite /buf_pay.
    case_decide; [|apply ctx_morph_const].
    apply ctx_morph_sep; [apply ctx_morph_const|].
    destruct v.
    - apply ctx_morph_exist => bsd. apply ctx_morph_exist => d.
      apply ctx_morph_sep; [apply ctx_morph_const|].
      rewrite /bio_pay. destruct d.
      + apply ctx_morph_sep; [apply ctx_morph_const|].
        apply ctx_morph_exist => q.
        rewrite /bref.
        apply ctx_morph_sep; [apply ctx_morph_const|].
        apply ctx_morph_sep; [apply ctx_morph_const|].
        apply ctx_morph_sep; apply ctx_morph_word4.
      + apply ctx_morph_const.
    - apply ctx_morph_const.
  Qed.

  Local Instance buf_own_morph b bno dsk bs :
    CtxMorph (fun ξ => buf_own (XI := ξ) b bno dsk bs).
  Proof.
    rewrite /buf_own.
    apply ctx_morph_sep; [apply ctx_morph_word4|].
    apply ctx_morph_sep; [apply ctx_morph_word4|].
    apply ctx_morph_sep; [apply ctx_morph_const|].
    apply ctx_morph_big_sepL. intros i x. apply ctx_morph_pointsto.
  Qed.

  Global Instance bio_slot_res2_morph bn V M k dev bno tl :
    CtxMorph (bio_slot_res2 bn V M k dev bno tl).
  Proof.
    rewrite /bio_slot_res2.
    apply ctx_morph_sep; [apply ctx_morph_const|].
    destruct (M !! k) as [[q n]|].
    - apply ctx_morph_sep; [apply ctx_morph_const|].
      apply ctx_morph_sep; [apply ctx_morph_word4|].
      apply ctx_morph_sep; [apply ctx_morph_const|].
      apply ctx_morph_sep; [apply ctx_morph_const|].
      apply ctx_morph_exist => qr.
      apply ctx_morph_sep; [apply ctx_morph_const|].
      apply ctx_morph_sep; apply ctx_morph_word4.
    - apply ctx_morph_sep; [apply ctx_morph_word4|].
      apply ctx_morph_sep; [apply ctx_morph_const|].
      apply ctx_morph_exist => v. apply ctx_morph_exist => bs.
      apply ctx_morph_sep; [apply ctx_morph_word4|].
      apply ctx_morph_sep; [apply ctx_morph_word4|].
      apply ctx_morph_sep; [apply buf_own_morph|].
      apply ctx_morph_sep; [apply ctx_morph_word4|].
      apply buf_pay_morph.
  Qed.

  Global Instance bcache_scan2_morph bn V M ord devs bnos tl :
    CtxMorph (bcache_scan2 bn V M ord devs bnos tl).
  Proof.
    rewrite /bcache_scan2.
    apply ctx_morph_sep; [apply ctx_morph_const|].
    apply ctx_morph_sep; [apply ctx_morph_const|].
    apply ctx_morph_sep; [apply ctx_morph_const|].
    apply ctx_morph_sep; [apply ctx_morph_const|].
    apply ctx_morph_sep; [apply ctx_morph_const|].
    apply ctx_morph_sep; [apply ctx_morph_const|].
    apply ctx_morph_sep; [apply bcache_lru_morph|].
    apply ctx_morph_sep; [apply ctx_morph_const|].
    apply ctx_morph_big_sepL. intros i x. apply bio_slot_res2_morph.
  Qed.

  Global Instance bcache_res2_morph bn V : CtxMorph (bcache_res2 bn V).
  Proof.
    rewrite /bcache_res2.
    apply ctx_morph_exist => M. apply ctx_morph_exist => ord.
    apply ctx_morph_exist => devs. apply ctx_morph_exist => bnos.
    apply ctx_morph_exist => tl.
    apply ctx_morph_sep; [apply _ | apply bcache_scan2_morph].
  Qed.

  (* ---- the sleeplock's client payload (endgame §3.2 / R1-pre): ξ-free,
     bound-indexed -- the checkout token plus the park register's payload
     half with its witnesses, bounded by the sleeplock's floor slot. ---- *)
  Definition bslp_raw (γo γp γa : gname) (ξ : CtxId) : iProp Σ :=
    (lock_tok_excl γo ∗
     ∃ rp : nat * nat, ghost_var γp (1/2) rp ∗ astamp γa rp.1 rp.2 ∗
       llb loglen_name rp.2 ∗ TsoCtx.ctx_floor ξ rp.2)%I.
  Definition bslp (bn : bio_names) (k : nat) : CtxId -> iProp Σ :=
    bslp_raw (bn_own bn k) (bn_regp bn k) (bn_anc bn k).
  (* the releaser's unfloored row (R2's [Rdep]), at a KNOWN park pair *)
  Definition bslp_dep (bn : bio_names) (k : nat) (rp : nat * nat) : iProp Σ :=
    (bown bn k ∗ reg_park bn k rp ∗ astamp (bn_anc bn k) rp.1 rp.2 ∗
     llb loglen_name rp.2)%I.
  Lemma bslp_fold bn k rp (ξ : CtxId) :
    bslp_dep bn k rp ∗ TsoCtx.ctx_floor ξ rp.2 ⊢ bslp bn k ξ.
  Proof.
    iIntros "[(Ho & Hrp & #Hst & #Hllb) #Hfl]". rewrite /bslp /bslp_raw /bown.
    iFrame "Ho". iExists rp. iFrame "Hrp Hst Hllb Hfl".
  Qed.
  Global Instance bslp_raw_morph γo γp γa : CtxMorph (bslp_raw γo γp γa).
  Proof.
    rewrite /bslp_raw. apply ctx_morph_sep; [apply ctx_morph_const|].
    apply ctx_morph_exist => rp.
    apply ctx_morph_sep; [apply ctx_morph_const|].
    apply ctx_morph_sep; [apply ctx_morph_const|].
    apply ctx_morph_sep; [apply ctx_morph_const| apply _].
  Qed.
  Global Instance bslp_morph bn k : CtxMorph (bslp bn k).
  Proof. rewrite /bslp. apply _. Qed.

  (* ================================================================== *)
  (*  The v2 context and its boot (bio_init's clone with the box).        *)
  (* ================================================================== *)

  (* ================================================================== *)
  (*  R2 (A): the v1 slot accessors restated over the v2 payload, at the  *)
  (*  ambient context (the payload has been morphed to cur_ctx by the     *)
  (*  acquire; every [↦₄] below is [ctx_word4_pointsto cur_ctx]).          *)
  (* ================================================================== *)

  Section BioSlots2.
  Context `{XI : CurCtx}.

  Lemma bcache_res2_to_scan (bn : bio_names) (V : bio_view Σ) :
    bcache_res2 bn V cur_ctx -∗
    ∃ M ord devs bnos tl,
      TsoCtx.ctx_floor cur_ctx tl ∗ bcache_scan2 bn V M ord devs bnos tl cur_ctx.
  Proof. rewrite /bcache_res2. iIntros "H". iExact "H". Qed.

  Lemma bio_slots_acc2 (bn : bio_names) (V : bio_view Σ)
      (M : gmap nat (Qp * positive)) (devs bnos : nat -> mword 32)
      (tl i : nat) :
    (i < NBUF)%nat ->
    ([∗ list] k ∈ seq 0 NBUF, bio_slot_res2 bn V M k (devs k) (bnos k) tl cur_ctx) -∗
    bio_slot_res2 bn V M i (devs i) (bnos i) tl cur_ctx ∗
    (∀ (M' : gmap nat (Qp * positive)) (devs' bnos' : nat -> mword 32),
       ⌜∀ k, k ≠ i -> M' !! k = M !! k /\ devs' k = devs k /\
             bnos' k = bnos k⌝ -∗
       bio_slot_res2 bn V M' i (devs' i) (bnos' i) tl cur_ctx -∗
       [∗ list] k ∈ seq 0 NBUF, bio_slot_res2 bn V M' k (devs' k) (bnos' k) tl cur_ctx).
  Proof.
    iIntros (Hi) "H".
    assert (Hlk : seq 0 NBUF !! i = Some i) by (apply lookup_seq; lia).
    rewrite (big_sepL_delete
               (fun _ k => bio_slot_res2 bn V M k (devs k) (bnos k) tl cur_ctx)
               (seq 0 NBUF) i i Hlk).
    iDestruct "H" as "[$ Hrest]".
    iIntros (M' devs' bnos' HM') "Hi".
    rewrite (big_sepL_delete
               (fun _ k => bio_slot_res2 bn V M' k (devs' k) (bnos' k) tl cur_ctx)
               (seq 0 NBUF) i i Hlk).
    iFrame "Hi".
    iApply (big_sepL_mono with "Hrest").
    intros idx y Hy. destruct (decide (idx = i)) as [->|Hne]; [done|].
    apply lookup_seq in Hy as [-> _].
    destruct (HM' _ Hne) as (HMk & Hdk & Hbk).
    unfold bio_slot_res2. rewrite HMk Hdk Hbk. done.
  Qed.

  (* the LRU scan's borrow of dev/blockno: SOME fraction of both cells *)
  Lemma bio_slot_devbno_acc2 (bn : bio_names) (V : bio_view Σ)
      (M : gmap nat (Qp * positive)) (k : nat) (dev bno : mword 32) (tl : nat) :
    bio_slot_res2 bn V M k dev bno tl cur_ctx -∗
    ∃ q : Qp,
      b_dev (bpa k) ↦₄{DfracOwn q} dev ∗
      b_blockno (bpa k) ↦₄{DfracOwn q} bno ∗
      (b_dev (bpa k) ↦₄{DfracOwn q} dev -∗
       b_blockno (bpa k) ↦₄{DfracOwn q} bno -∗
       bio_slot_res2 bn V M k dev bno tl cur_ctx).
  Proof.
    iIntros "[Hregs Hslot]". rewrite /bio_slot_res2.
    destruct (M !! k) as [[qt n]|] eqn:HMk.
    - iDestruct "Hslot" as "(%Hn & Hcell & Hsl & Hc & Hqr)".
      iDestruct "Hqr" as (qr) "(%Htie & Hdev & Hbno)".
      iExists qr. iFrame "Hdev Hbno". iIntros "Hdev Hbno".
      iFrame "Hregs". iSplitR; [by iPureIntro|]. iFrame "Hcell Hsl Hc".
      iExists qr. iSplitR; [by iPureIntro|]. iFrame "Hdev Hbno".
    - iDestruct "Hslot" as "(Hcell & Hc & Hcont)".
      iDestruct "Hcont" as (v bs) "(Hvld & Hdev & Hbuf & Hbno & Hpay)".
      iDestruct (ctx_word4_pointsto_half_split with "Hdev") as "[Hdev1 Hdev2]".
      iExists (1/2)%Qp. iFrame "Hdev1 Hbno". iIntros "Hdev1 Hbno".
      iDestruct (ctx_word4_pointsto_half_join with "Hdev1 Hdev2") as "Hdev".
      iFrame "Hregs Hcell Hc". iExists v, bs. iFrame "Hvld Hdev Hbuf Hbno Hpay".
  Qed.

  (* the backward scan's borrow of the refcnt word, with the [beqz] tie *)
  Lemma bio_slot_refcnt_acc2 (bn : bio_names) (V : bio_view Σ)
      (M : gmap nat (Qp * positive)) (k : nat) (dev bno : mword 32) (tl : nat) :
    bio_slot_res2 bn V M k dev bno tl cur_ctx -∗
    ∃ cw : mword 32,
      brefcnt k ↦₄ cw ∗
      ⌜(eq_vec (sign_extend' 64 cw) (zero_reg : mword 64) = true /\ M !! k = None)
       \/ (eq_vec (sign_extend' 64 cw) (zero_reg : mword 64) = false
           /\ is_Some (M !! k))⌝ ∗
      (brefcnt k ↦₄ cw -∗ bio_slot_res2 bn V M k dev bno tl cur_ctx).
  Proof.
    iIntros "[Hregs Hslot]". rewrite /bio_slot_res2.
    destruct (M !! k) as [[qt n]|] eqn:HMk.
    - iDestruct "Hslot" as "(%Hn & Hcell & Hsl & Hc & Hqr)".
      iExists (mword_of_int (Z.pos n) : mword 32). iFrame "Hcell".
      iSplitR.
      { iPureIntro. right. split; [exact (brc_word_nonzero_eqv n Hn) | by eexists]. }
      iIntros "Hcell". iFrame "Hregs". iSplitR; [by iPureIntro|]. iFrame "Hcell Hsl Hc Hqr".
    - iDestruct "Hslot" as "(Hcell & Hc & Hcont)".
      iExists (mword_of_int 0 : mword 32). iFrame "Hcell".
      iSplitR.
      { iPureIntro. left. split; [exact brc_word_zero_eqv | reflexivity]. }
      iIntros "Hcell". iFrame "Hregs Hcell Hc Hcont".
  Qed.

  End BioSlots2.

  Section BioBoot2.
  Context `{XI : CurCtx}.

  Definition bio_ctx (bn : bio_names) (V : bio_view Σ) : iProp Σ :=
    (WpLock.is_lock (bn_lk bn) bcache_addr "bcache"%string
       (fun ξ => bcache_res2 bn V ξ) ∗
     [∗ list] k ∈ seq 0 NBUF,
       (is_sleeplock_genl (fst (bn_slk bn k)) (snd (bn_slk bn k))
          (buf_lock (bnode k)) "buffer"%string (bslp bn k) sl_untracked ∗
        buf_box bn V k))%I.

  Global Instance bio_ctx_persistent bn V : Persistent (bio_ctx bn V).
  Proof. apply _. Qed.

  Lemma bio_ctx_lock bn V :
    bio_ctx bn V -∗
    WpLock.is_lock (bn_lk bn) bcache_addr "bcache"%string
      (fun ξ => bcache_res2 bn V ξ).
  Proof. iIntros "[$ _]". Qed.

  Lemma bio_ctx_buf bn V k :
    (k < NBUF)%nat ->
    bio_ctx bn V -∗
    is_sleeplock_genl (fst (bn_slk bn k)) (snd (bn_slk bn k))
      (buf_lock (bnode k)) "buffer"%string (bslp bn k) sl_untracked ∗
    buf_box bn V k.
  Proof.
    iIntros (Hk) "[_ Hbufs]".
    assert (Hlk : seq 0 NBUF !! k = Some k) by (apply lookup_seq; lia).
    iDestruct (big_sepL_lookup with "Hbufs") as "[$ $]"; [exact Hlk].
  Qed.

  Lemma bio_init `{CID : RiscvLang.CpuId} (V : bio_view Σ) E :
    (0 ∉ bv_cov V) ->
    own_context cur_ctx -∗
    bcache_addr ↦₄ (mword_of_int 0 : mword 32) -∗
    lock_name bcache_addr "bcache"%string -∗
    WpLock.lk_cpu_ready bcache_addr -∗
    ([∗ list] k ∈ seq 0 NBUF, sl_fresh (buf_lock (bnode k)) "buffer"%string) -∗
    ([∗ list] k ∈ seq 0 NBUF,
       b_valid (bpa k) ↦₄ (mword_of_int 0 : mword 32) ∗
       b_disk (bpa k) ↦₄ (mword_of_int 0 : mword 32) ∗
       b_dev (bpa k) ↦₄ (mword_of_int 0 : mword 32) ∗
       b_blockno (bpa k) ↦₄ (mword_of_int 0 : mword 32) ∗
       brefcnt k ↦₄ (mword_of_int 0 : mword 32) ∗
       (∃ bs : list (bv 8), ⌜length bs = 1024%nat⌝ ∗
          [∗ list] j ↦ byte ∈ bs, pa_add (b_data (bpa k)) j ↦ₘ byte)) -∗
    bcache_lru bhead (blist 0 NBUF) -∗
    ([∗ set] b ∈ bv_cov V, pool_blk V b) -∗
    bslots_auth -∗ bslots BSLOTS_FS ={E}=∗
    own_context cur_ctx ∗
    ∃ bn : bio_names, bio_ctx bn V ∗ bslots BSLOTS_FS.
  Proof.
    iIntros (Hnc0) "Hrun Hlkw #Hnm Hcpu Hfresh Hbufs Hlru Hpool Hsa Hsf".
    assert (Hu0 : uint (mword_of_int 0 : mword 32) = 0)
      by (vm_compute; reflexivity).
    iMod (tok_fun_alloc NBUF 0) as (fown) "Htoks".
    iMod (tok_fun_alloc NBUF 0) as (fmid) "Hmids".
    (* the NBUF anchors (BEFORE the sleeplocks: their boot rows need the
       generation-0 witness), presence authorities, registers, tag sets *)
    iAssert ([∗ list] k ∈ seq 0 NBUF, |={E}=> ∃ γ : gname,
               (∃ ξ0 : CtxId, anchor γ 0 ξ0 0) ∗ astamp γ 0 0)%I as "Hancs".
    { iApply big_sepL_intro. iIntros "!>" (i k _).
      iMod anchor_alloc as (γ ξ0) "[Ha Hs]".
      iModIntro. iExists γ. iFrame "Hs". iExists ξ0. iFrame "Ha". }
    iMod (seq_fun_alloc E
            (fun _ γ => (∃ ξ0 : CtxId, anchor γ 0 ξ0 0) ∗ astamp γ 0 0)%I
            NBUF 0 with "Hancs") as (fanc) "Hancs2".
    iEval (rewrite big_sepL_sep) in "Hancs2".
    iDestruct "Hancs2" as "[Hancs1 #Hsts]".
    iAssert ([∗ list] k ∈ seq 0 NBUF, |={E}=> ∃ γ : gname,
               own γ (● (None : optionUR (prodR (agreeR presPair) positiveR))))%I as "Hpres".
    { iApply big_sepL_intro. iIntros "!>" (i k _).
      iMod (own_alloc (● (None : optionUR (prodR (agreeR presPair) positiveR)))) as (γ) "H".
      { by apply auth_auth_valid. }
      iModIntro. iExists γ. iExact "H". }
    iMod (seq_fun_alloc E
            (fun _ γ => own γ (● (None : optionUR (prodR (agreeR presPair) positiveR))))
            NBUF 0 with "Hpres") as (fpres) "Hpres2".
    iAssert ([∗ list] k ∈ seq 0 NBUF, |={E}=> ∃ γ : gname,
               ghost_var γ (1/2) ((0%nat, 0%nat) : nat * nat) ∗ ghost_var γ (1/2) ((0%nat, 0%nat) : nat * nat))%I as "Hgp".
    { iApply big_sepL_intro. iIntros "!>" (i k _).
      iMod (ghost_var_alloc ((0%nat, 0%nat) : nat * nat)) as (γ) "H".
      iModIntro. iExists γ. iEval (rewrite -{1}Qp.half_half) in "H". iDestruct "H" as "[$ $]". }
    iMod (seq_fun_alloc E
            (fun _ γ => ghost_var γ (1/2) ((0%nat, 0%nat) : nat * nat) ∗ ghost_var γ (1/2) ((0%nat, 0%nat) : nat * nat))%I
            NBUF 0 with "Hgp") as (fregp) "Hregp".
    iAssert ([∗ list] k ∈ seq 0 NBUF, |={E}=> ∃ γ : gname,
               ghost_var γ (1/2) ((0%nat, 0%nat) : nat * nat) ∗ ghost_var γ (1/2) ((0%nat, 0%nat) : nat * nat))%I as "Hgd".
    { iApply big_sepL_intro. iIntros "!>" (i k _).
      iMod (ghost_var_alloc ((0%nat, 0%nat) : nat * nat)) as (γ) "H".
      iModIntro. iExists γ. iEval (rewrite -{1}Qp.half_half) in "H". iDestruct "H" as "[$ $]". }
    iMod (seq_fun_alloc E
            (fun _ γ => ghost_var γ (1/2) ((0%nat, 0%nat) : nat * nat) ∗ ghost_var γ (1/2) ((0%nat, 0%nat) : nat * nat))%I
            NBUF 0 with "Hgd") as (fregd) "Hregd".
    iAssert ([∗ list] k ∈ seq 0 NBUF, |={E}=> ∃ γ : gname,
               ghost_var γ (1/2) (0%nat : nat) ∗ ghost_var γ (1/2) (0%nat : nat))%I as "Hgc".
    { iApply big_sepL_intro. iIntros "!>" (i k _).
      iMod (ghost_var_alloc (0%nat : nat)) as (γ) "H".
      iModIntro. iExists γ. iEval (rewrite -{1}Qp.half_half) in "H". iDestruct "H" as "[$ $]". }
    iMod (seq_fun_alloc E
            (fun _ γ => ghost_var γ (1/2) (0%nat : nat) ∗ ghost_var γ (1/2) (0%nat : nat))%I
            NBUF 0 with "Hgc") as (fregc) "Hregc".
    iAssert ([∗ list] k ∈ seq 0 NBUF, |={E}=> ∃ γ : gname,
               own γ (● (∅ : gmultiset nat)))%I as "Hgt".
    { iApply big_sepL_intro. iIntros "!>" (i k _).
      iMod (own_alloc (● (∅ : gmultiset nat))) as (γ) "H".
      { by apply auth_auth_valid. }
      iModIntro. iExists γ. iExact "H". }
    iMod (seq_fun_alloc E
            (fun _ γ => own γ (● (∅ : gmultiset nat)))
            NBUF 0 with "Hgt") as (fpile) "Hpile".
    iMod (own_alloc (● (∅ : gmap nat (Qp * positive)) : bioUR)) as (γb) "Hauth".
    { apply auth_auth_valid. intros i. rewrite lookup_empty. done. }
    iMod (newlock_delayed E bcache_addr "bcache"%string with "Hnm Hlkw Hcpu")
      as (γlk) "Hmk".
    (* the sleeplocks, sealed over the bound-indexed client payload at
       bound 0: the checkout token and the park register's payload half at
       generation 0 *)
    iEval (rewrite big_sepL_sep) in "Hregp".
    iDestruct "Hregp" as "[Hregp1 Hregp2]".
    iDestruct (big_sepL_sep_2 with "Hfresh Htoks") as "Hsl".
    iDestruct (big_sepL_sep_2 with "Hsl Hregp1") as "Hsl".
    iAssert ([∗ list] idx↦k ∈ seq 0 NBUF,
               own_context cur_ctx -∗
               ((sl_fresh (buf_lock (bnode k)) "buffer"%string ∗
                 lock_tok_excl (fown k)) ∗
                ghost_var (fregp k) (1/2) ((0%nat, 0%nat) : nat * nat))
               ={E}=∗ own_context cur_ctx ∗
               (∃ p : gname * gname,
                  is_sleeplock_genl (fst p) (snd p) (buf_lock (bnode k))
                    "buffer"%string
                    (bslp_raw (fown k) (fregp k) (fanc k))
                    sl_untracked))%I
      as "Hstep".
    { iApply big_sepL_intro. iIntros "!>" (idx k Hk) "Hrun [[Hf Ht] Hrp]".
      iDestruct (big_sepL_lookup _ _ idx k Hk with "Hsts") as "#Hst0".
      iMod (sl_fresh_new_genl E (buf_lock (bnode k)) "buffer"%string
              (bslp_raw (fown k) (fregp k) (fanc k))
              (fun _ => sl_untracked) with "Hf Hrun [Ht Hrp]") as "[Hrun Hlk]".
      { rewrite /bslp_raw. iFrame "Ht". iExists (0%nat, 0%nat). iFrame "Hrp". iSplit; [iExact "Hst0"|].
        iSplit; [iApply TsoGhost.llb_0 | iApply TsoCtx.ctx_floor_0]. }
      iDestruct "Hlk" as (γl γsl) "[Hlk _]".
      iModIntro. iFrame "Hrun". iExists (γl, γsl). iExact "Hlk". }
    iMod (big_sepL_fupd_thread E (own_context cur_ctx)
            with "Hrun Hstep Hsl") as "[Hrun Hsl]".
    iAssert ([∗ list] k ∈ seq 0 NBUF, |={E}=> ∃ p : gname * gname,
               is_sleeplock_genl (fst p) (snd p) (buf_lock (bnode k))
                 "buffer"%string
                 (bslp_raw (fown k) (fregp k) (fanc k))
                 sl_untracked)%I
      with "[Hsl]" as "Hsl".
    { iApply (big_sepL_mono with "Hsl"). intros i k Hk.
      iIntros "H". by iModIntro. }
    iMod (seq_fun_alloc E
            (fun k p => is_sleeplock_genl (fst p) (snd p) (buf_lock (bnode k))
                          "buffer"%string
                          (bslp_raw (fown k) (fregp k) (fanc k))
                          sl_untracked)
            NBUF 0 with "Hsl") as (fslk) "#Hsls".
    set (bn := MkBioNames γlk γb fslk fown fmid fanc fpres fregp fregd fpile fregc).
    assert (Hpay0 : forall k bs,
        buf_pay (XI := cur_ctx) bn V k false (mword_of_int 0 : mword 32)
          (mword_of_int 0 : mword 32) bs = emp%I).
    { intros k bs. rewrite /buf_pay. case_decide as Hd; [|reflexivity].
      exfalso. apply Hnc0. rewrite -Hu0. exact Hd. }
    (* every buffer: the BOX starts IDLE at generation 0 (● None, the
       count half at 0, no tags); the payload's None arm takes the whole
       resting content plus the L1 register row at generation 0 *)
    iEval (rewrite big_sepL_sep) in "Hregd".
    iDestruct "Hregd" as "[Hregd1 Hregd2]".
    iEval (rewrite big_sepL_sep) in "Hregc".
    iDestruct "Hregc" as "[Hregc1 Hregc2]".
    iDestruct (big_sepL_sep_2 with "Hancs1 Hpres2") as "Hap".
    iDestruct (big_sepL_sep_2 with "Hap Hregp2") as "Hap".
    iDestruct (big_sepL_sep_2 with "Hap Hregd1") as "Hap".
    iDestruct (big_sepL_sep_2 with "Hap Hregc1") as "Hap".
    iDestruct (big_sepL_sep_2 with "Hap Hpile") as "Hap".
    iDestruct (big_sepL_sep_2 with "Hregd2 Hregc2") as "Hslr".
    iDestruct (big_sepL_sep_2 with "Hslr Hbufs") as "Hslr".
    iDestruct (big_sepL_sep_2 with "Hap Hslr") as "Hall".
    iAssert (([∗ list] k ∈ seq 0 NBUF, |={E}=> buf_box bn V k) ∗
             ([∗ list] k ∈ seq 0 NBUF,
                bio_slot_res2 bn V ∅ k (mword_of_int 0 : mword 32)
                  (mword_of_int 0 : mword 32) 0 cur_ctx))%I
      with "[Hall]" as "[Hbox Hslots]".
    { rewrite -big_sepL_sep. iApply (big_sepL_impl with "Hall").
      iIntros "!>" (i k Hk).
      iDestruct (big_sepL_lookup _ _ i k Hk with "Hsts") as "#Hst0".
      iIntros "[((((((%XI0 & Hanc) & Hpn) & Hrp) & Hrd) & Hc) & Hta) ((Hrd2 & Hc2) & (Hv & Hdk & Hdev & Hbno & Hrc & Hdata))]".
      iDestruct (ctx_word4_pointsto_half_split with "Hbno") as "[Hbno1 Hbno2]".
      iDestruct "Hdata" as (bs) "[%Hlen Hdata]".
      iSplitL "Hanc Hpn Hrp Hrd Hc Hta".
      - rewrite /buf_box.
        iApply (inv_alloc bioxN E (buf_box_body bn V k)).
        iNext. iExists 0%nat, 0%nat, XI0, (0%nat, 0%nat), (0%nat, 0%nat), ∅.
        iFrame "Hanc Hrp Hrd Hta". iSplitR; [iExact "Hst0"|].
        iSplitR; [iApply TsoGhost.llb_0|].
        iSplitR; [iExact "Hst0"|].
        iSplitR; [iApply TsoGhost.llb_0|].
        iSplitR; [iPureIntro; intros Hne; done|].
        iLeft. iFrame "Hpn Hc". done.
      - rewrite /bio_slot_res2 lookup_empty.
        iSplitL "Hrd2".
        { iExists (0%nat, 0%nat). iFrame "Hrd2". iSplit; [iExact "Hst0"|].
          iSplit; [iApply TsoGhost.llb_0 | done]. }
        iFrame "Hrc Hc2". iExists false, bs.
        rewrite Hpay0. cbv iota.
        iFrame "Hv Hdev Hbno2". rewrite /buf_own.
        iFrame "Hbno1 Hdk Hdata". done. }
    iMod (big_sepL_fupd with "Hbox") as "#Hboxs".
    iAssert (bio_pool V (fun _ => (mword_of_int 0 : mword 32)))
      with "[Hpool]" as "Hpool".
    { rewrite /bio_pool.
      assert (Hc0 : bv_cov V ∖
                    bcache_cached (fun _ => (mword_of_int 0 : mword 32))
                    = bv_cov V).
      { apply set_eq. intros b. rewrite elem_of_difference. split.
        - intros [Hb _]. exact Hb.
        - intros Hb. split; [exact Hb|]. intros Hc.
          apply bcache_cached_spec in Hc as (j & Hj & ->).
          apply Hnc0. rewrite -Hu0. exact Hb. }
      rewrite Hc0. iExact "Hpool". }
    iMod ("Hmk" $! (fun ξ => bcache_res2 bn V ξ)
            with "[%] Hrun [Hauth Hsa Hslots Hlru Hpool]")
      as "[Hrun #Hlock]".
    { apply _. }
    { rewrite /bcache_res2 /bcache_scan2.
      iExists ∅, (rev (seq 0 NBUF)),
        (fun _ => (mword_of_int 0 : mword 32)),
        (fun _ => (mword_of_int 0 : mword 32)), 0%nat.
      iSplitR; [iApply TsoCtx.ctx_floor_0|].
      iFrame "Hauth Hsa".
      iSplitR.
      { iPureIntro. intros k [x Hx]. rewrite lookup_empty in Hx. done. }
      iSplitR.
      { iPureIntro. symmetry. apply Permutation_rev. }
      iSplitR.
      { iPureIntro. intros k1 k2 Hk1 Hk2 Hcov _.
        exfalso. apply Hnc0. rewrite -Hu0. exact Hcov. }
      iSplitR.
      { iPureIntro. intros k1 Hk1 Hcov.
        exfalso. apply Hnc0. rewrite -Hu0. exact Hcov. }
      assert (Hml : map bnode (rev (seq 0 NBUF)) = blist 0 NBUF)
        by (rewrite /blist map_rev //).
      rewrite Hml. iFrame "Hlru Hslots Hpool". }
    iModIntro. iSplitL "Hrun"; [iExact "Hrun" |]. iExists bn. rewrite /bio_ctx.
    iSplitR "Hsf"; [| iExact "Hsf"].
    iSplitL "Hlock"; [iExact "Hlock" |].
    rewrite big_sepL_sep. iSplitL "Hsls"; [iExact "Hsls" | iExact "Hboxs"].
  Qed.

  End BioBoot2.
End BioBox.
