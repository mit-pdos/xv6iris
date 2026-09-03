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
From Stdlib Require Import ZArith Lia List QArith Qcanon.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import excl auth gmap frac numbers agree gmultiset ufrac.
From stdpp Require Import gmultiset.
From iris.base_logic.lib Require Import ghost_var.
From iris.base_logic.lib Require Import gen_heap invariants own.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes.
Require Import RiscvPtsto.
Require Import WpLock.
Require Import TsoCtx.   (* the lock payload's context axis; [<{ }>] *)
Require Import CtxMorphTac.   (* [bio_ctx_morph] (r25 pass 1) *)
Require Import TsoGhost.
Require Import CtxBox.   (* the generic transit box; bcache instantiates it below *)
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

(* ENDGAME A6.155 (vetted): the share component is [option Qp].  A
   fractioned reference (bpin's / the log layer's) carries [Some q] and the
   dev/bno fractions {q}; the chain's reference carries [None] and no
   fraction.  [None] is the unit of [optionUR fracR], so (None,1) ⋅ (Some q,1)
   = (Some q,2): the count component counts BOTH kinds.  The kit is written
   ONCE over the option share. *)
Local Lemma bio_first_upd (M : gmap nat (option Qp * positive)) (k : nat) (o : option Qp) :
  M !! k = None ->
  ✓ o ->
  (● M : bioUR) ~~> ● (<[k := (o, 1%positive)]> M) ⋅ ◯ {[ k := (o, 1%positive) ]}.
Proof.
  intros HM Ho. apply auth_update_alloc.
  apply (alloc_singleton_local_update _ k (o, 1%positive)); [done|].
  split; [exact Ho | done].
Qed.

Local Lemma bio_incr_lu (M : gmap nat (option Qp * positive)) (k : nat)
    (ot on : option Qp) (n : positive) :
  M !! k = Some (ot, n) ->
  ✓ (ot ⋅ on) ->
  @local_update _ (gmapUR nat (prodR (optionUR fracR) positiveR))
    (M, ∅) (<[k := (ot ⋅ on, Pos.succ n)]> M, {[ k := (on, 1%positive) ]}).
Proof.
  intros HM Hv.
  apply gmap_local_update. intros i.
  destruct (decide (i = k)) as [->|Hne]; last first.
  { rewrite lookup_insert_ne // lookup_singleton_ne //. }
  rewrite lookup_insert lookup_singleton lookup_empty HM.
  apply local_update_unital_discrete. intros z _ Hz.
  rewrite left_id in Hz. rewrite -Hz.
  split.
  { apply Some_valid. split; cbn; [exact Hv | done]. }
  rewrite -Some_op -pair_op pos_op_add.
  by rewrite (comm op on ot) Pos.add_1_l.
Qed.

Local Lemma bio_incr_upd (M : gmap nat (option Qp * positive)) (k : nat)
    (ot on : option Qp) (n : positive) :
  M !! k = Some (ot, n) ->
  ✓ (ot ⋅ on) ->
  (● M : bioUR) ~~>
  ● (<[k := (ot ⋅ on, Pos.succ n)]> M) ⋅ ◯ {[ k := (on, 1%positive) ]}.
Proof. intros HM Hv. apply auth_update_alloc. by apply bio_incr_lu. Qed.

(* refcnt-- with survivors: the departing reference's share leaves the
   entry ([o] is cancelable: [optionUR fracR] over an id-free, cancelable
   carrier). *)
Local Lemma bio_decr_upd (M : gmap nat (option Qp * positive)) (k : nat)
    (o ot orem : option Qp) (n : positive) :
  M !! k = Some (ot, Pos.succ n) ->
  ot = o ⋅ orem ->
  (● M : bioUR) ⋅ ◯ {[ k := (o, 1%positive) ]} ~~> ● (<[k := (orem, n)]> M).
Proof.
  intros HM Hsub.
  apply auth_update_dealloc, gmap_local_update. intros i.
  destruct (decide (i = k)) as [->|Hne]; last first.
  { assert (Hki : k <> i) by auto.
    pose proof (lookup_singleton_ne (M:=gmap nat) k i (o, 1%positive) Hki) as Hs.
    pose proof (lookup_insert_ne M k i (orem, n) Hki) as Hm.
    apply local_update_discrete. intros mz Hv Hz.
    rewrite Hs in Hz. rewrite Hm. split; [exact Hv | exact Hz]. }
  pose proof (lookup_singleton (M:=gmap nat) k (o, 1%positive)) as Hs.
  pose proof (lookup_insert M k (orem, n)) as Hm.
  apply local_update_discrete. intros mz Hv Hz.
  rewrite HM in Hz, Hv. rewrite Hs in Hz. rewrite Hm.
  destruct mz as [[[qf nf]|]|]; simpl in Hz.
  - apply (inj Some) in Hz. destruct Hz as [Hq Hn]; simpl in Hq, Hn.
    rewrite pos_op_add in Hn.
    assert (Hn' : Pos.succ n = (1 + nf)%positive) by exact Hn.
    assert (Hnf : nf = n) by lia.
    destruct Hv as [Hvq _]; simpl in Hvq.
    assert (Hqf : qf ≡ orem).
    { apply (cancelable o); [by rewrite -Hq |]. by rewrite -Hq -Hsub. }
    apply leibniz_equiv in Hqf. subst nf qf. split; last first.
    { by constructor. }
    split; simpl; [|done].
    rewrite Hsub in Hvq. exact (cmra_valid_op_r _ _ Hvq).
  - exfalso. rewrite right_id in Hz. apply (inj Some) in Hz.
    destruct Hz as [_ Hn]; simpl in Hn.
    assert (Hn' : Pos.succ n = 1%positive) by exact Hn. lia.
  - exfalso. apply (inj Some) in Hz.
    destruct Hz as [_ Hn]; simpl in Hn.
    assert (Hn' : Pos.succ n = 1%positive) by exact Hn. lia.
Qed.

(* the last refcnt--: [(o,1)] is cancelable and the entry is exactly the
   fragment -- a frame would push the COUNT past 1 -- so the entry goes. *)
Local Lemma bio_last_upd (M : gmap nat (option Qp * positive)) (k : nat) (o : option Qp) :
  M !! k = Some (o, 1%positive) ->
  (● M : bioUR) ⋅ ◯ {[ k := (o, 1%positive) ]} ~~> ● (delete k M).
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
  (* one reference's count fragment at share [o] (A6.155) *)
  Definition btok (bn : bio_names) (k : nat) (o : option Qp) : iProp Σ :=
    own (bn_auth bn) (◯ {[ k := (o, 1%positive) ]}).
  (* a FRACTIONED reference's fragment (bpin / the log layer) *)
  Definition bref_tok (bn : bio_names) (k : nat) (q : Qp) : iProp Σ :=
    btok bn k (Some q).
  (* the CHAIN's fragment (bread's reference): no share, no fraction *)
  Definition bref_tok0 (bn : bio_names) (k : nat) : iProp Σ :=
    btok bn k None.

  (* ================================================================== *)
  (*  THE STAMPED SHARES (box v2, endgame §3.2): stamp ↦ fraction.  [● m]  *)
  (*  sits in the box; a COUNTED reference owns ONE UNIT {[t := 1]} at    *)
  (*  the stamp of the last deposit it witnessed; Σ m (in Qc) is the      *)
  (*  count.  The kit: the sum, its steps, the two local updates.         *)
  (* ================================================================== *)
  (* THE BOX NAMES (CtxBox.v, endgame §3.2): stamps / cnt / slot_d / slot_p
     per buffer, drawn from the names record's fields *)
  Definition bn_box (bn : bio_names) (k : nat) : box_names :=
    BoxNames (bn_pres bn k) (bn_regc bn k) (bn_regd bn k) (bn_regp bn k).
  (* the count register's half at a RAW gname, at the box's own instance
     ([ghost_varG Σ nat] has several members in the bundle; the box's is
     kalloc's) -- what the boot mints before the names record exists *)
  Definition bcnt_var (γ : gname) (c : nat) : iProp Σ :=
    ghost_var (ghost_varG0 := kalloc_count_inG) γ (1/2) c.

  (* a COUNTED reference's stamps: one unit at the stamp of the last deposit
     it witnessed, with that stamp's llb (the R1 presentation at every
     acquire: [Tl := t]) *)
  Definition bref_ghost (bn : bio_names) (k : nat) (dev bno : mword 32) : iProp Σ :=
    (∃ t : nat, CtxBox.reference (X := bio_x) (bn_box bn k) (dev, bno) {[((dev, bno), t) := 1%Qp]})%I.

  (* a FRACTIONED reference (bpin's / the log layer's): the count fragment,
     the stamps unit at its identity, and the dev/bno fractions *)
  Definition bref (bn : bio_names) (k : nat) (q : Qp)
      (dev bno : mword 32) : iProp Σ :=
    (bref_tok bn k q ∗
     bref_ghost bn k dev bno ∗
     b_dev (bpa k) ↦₄{DfracOwn q} dev ∗
     b_blockno (bpa k) ↦₄{DfracOwn q} bno)%I.
  (* the CHAIN's reference (bread's), ghost-only: share None, no fraction;
     the identity rides the stamps key (F6) *)
  Definition bchain (bn : bio_names) (k : nat) (dev bno : mword 32) : iProp Σ :=
    (bref_tok0 bn k ∗ bref_ghost bn k dev bno)%I.

  Definition bown (bn : bio_names) (k : nat) : iProp Σ :=
    lock_tok_excl (bn_own bn k).

  Lemma bown_exclusive bn k : bown bn k -∗ bown bn k -∗ False.
  Proof. apply lock_tok_excl_exclusive. Qed.
  Global Instance bown_timeless bn k : Timeless (bown bn k).
  Proof. rewrite /bown. apply _. Qed.

  (* ------------------------------------------------------------------ *)
  (*  The uncached pool bundle and the payloads                           *)
  (* ------------------------------------------------------------------ *)

  (* one uncached covered block's pool bundle: its disk cell and its clean
     payload at the SAME content (uncached implies clean: the dirty arm
     parks a real [bref] and a referenced buffer is never evicted). *)
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

  Lemma btok_free_absurd bn (M : gmap nat (option Qp * positive)) k (o : option Qp) :
    M !! k = None ->
    own (bn_auth bn) (● M) -∗ btok bn k o -∗ False.
  Proof.
    iIntros (HM) "Ha Htok". rewrite /btok.
    iDestruct (own_valid_2 with "Ha Htok")
      as %[Hincl _]%auth_both_valid_discrete.
    iPureIntro.
    apply singleton_included_l in Hincl as [y [Hy _]].
    rewrite HM in Hy. inversion Hy.
  Qed.
  Lemma bref_tok_free_absurd bn (M : gmap nat (option Qp * positive)) k q :
    M !! k = None ->
    own (bn_auth bn) (● M) -∗ bref_tok bn k q -∗ False.
  Proof. apply btok_free_absurd. Qed.

  (* ---- the swaps (used inside an [iInv] open of [buf_escrow]) ---- *)

  (* (a) checkout, post-acquiresleep: the opener's bown refutes A2 and its
     reference's dev fraction refutes A3 (whose dev cell is full); its
     reference's cell fractions AGREE with the parked bundle's, pinning the
     withdrawn dev/bno to the requested key.  The deposited A2 absorbs the
     parked arm's recycle token, so the handle needn't carry it. *)
  Lemma buf_pay_evict bn V k (M : gmap nat (option Qp * positive))
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
  (* what a fragment says about the authority: the entry exists, the
     fragment's share is included, and a count of ONE means the entry IS
     the fragment. *)
  Lemma btok_lookup bn M k (o : option Qp) :
    own (bn_auth bn) (● M) -∗ btok bn k o -∗
    ⌜∃ ot n, M !! k = Some (ot, n) /\ o ≼ ot /\ (n = 1%positive -> ot = o)⌝.
  Proof.
    rewrite /btok. iIntros "Ha Hf".
    iDestruct (own_valid_2 with "Ha Hf") as %[Hincl _]%auth_both_valid_discrete.
    iPureIntro.
    apply singleton_included_l in Hincl as [y [Hy Hle]].
    apply leibniz_equiv in Hy. destruct y as [ot n]. exists ot, n.
    split; [exact Hy|].
    apply Some_included in Hle as [Heq | Hlt].
    - destruct Heq as [Ho Hn]; cbn in Ho, Hn. apply leibniz_equiv in Ho.
      split.
      + exists None. by rewrite right_id Ho.
      + intros _. by rewrite Ho.
    - apply pair_included in Hlt as [Ho Hn]; cbn in Ho, Hn.
      apply pos_included in Hn.
      split; [exact Ho|]. intros Hc. exfalso. rewrite Hc in Hn. lia.
  Qed.

  (* an entry's share is valid (the authority is) *)
  Lemma bio_auth_entry_valid bn M k (ot : option Qp) (n : positive) :
    M !! k = Some (ot, n) ->
    own (bn_auth bn) (● M) -∗ ⌜✓ ot⌝.
  Proof.
    iIntros (HM) "Ha". iDestruct (own_valid with "Ha") as %Hv.
    apply (proj1 (auth_auth_valid _)) in Hv.
    iPureIntro. specialize (Hv k). rewrite HM Some_valid in Hv.
    destruct Hv as [Hvo _]. exact Hvo.
  Qed.

  Lemma bio_first_ref_step bn M k (o : option Qp) :
    M !! k = None ->
    ✓ o ->
    own (bn_auth bn) (● M) ==∗
    own (bn_auth bn) (● (<[k := (o, 1%positive)]> M)) ∗ btok bn k o.
  Proof.
    iIntros (HM Ho) "Ha". rewrite /btok.
    iMod (own_update _ _ _ (bio_first_upd M k o HM Ho) with "Ha") as "[$ $]".
    done.
  Qed.

  Lemma bio_incr_step bn M k (ot : option Qp) (n : positive) (on : option Qp) :
    M !! k = Some (ot, n) ->
    ✓ (ot ⋅ on) ->
    own (bn_auth bn) (● M) ==∗
    own (bn_auth bn) (● (<[k := (ot ⋅ on, Pos.succ n)]> M)) ∗ btok bn k on.
  Proof.
    iIntros (HM Hv) "Ha". rewrite /btok.
    iMod (own_update _ _ _ (bio_incr_upd M k ot on n HM Hv) with "Ha") as "[$ $]".
    done.
  Qed.

  Lemma bio_decr_step bn M k (o ot orem : option Qp) (n : positive) :
    M !! k = Some (ot, Pos.succ n) ->
    ot = o ⋅ orem ->
    own (bn_auth bn) (● M) -∗ btok bn k o ==∗
    own (bn_auth bn) (● (<[k := (orem, n)]> M)).
  Proof.
    iIntros (HM Hsub) "Ha Hf". rewrite /btok.
    iMod (own_update_2 _ _ _ _ (bio_decr_upd M k o ot orem n HM Hsub)
           with "Ha Hf") as "$".
    done.
  Qed.

  Lemma bio_last_ref_step bn M k (o : option Qp) :
    M !! k = Some (o, 1%positive) ->
    own (bn_auth bn) (● M) -∗ btok bn k o ==∗
    own (bn_auth bn) (● (delete k M)).
  Proof.
    iIntros (HM) "Ha Hf". rewrite /btok.
    iMod (own_update_2 _ _ _ _ (bio_last_upd M k o HM) with "Ha Hf") as "$".
    done.
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  The bcache lock's resource                                          *)
  (* ------------------------------------------------------------------ *)

  (* the refcnt word each state stores (0 on a free slot, the count else) *)
  Definition brc_word (o : option (option Qp * positive)) : mword 32 :=
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
  (* F7 (vetted): the holder's token row -- the sleeplock token, the chain's
     count fragment, and the L2 register half naming the parked unit
     (keys AND mass: only the stamp is existential, R-1) *)
  Definition bstok (bn : bio_names) (k : nat) (pidv dev bno : mword 32) : iProp Σ :=
    (sleeplocked (snd (bn_slk bn k)) (buf_lock (bnode k)) pidv ∗
     (* the sleeplock's exclusivity token rides the handle: the box no
        longer takes it (endgame plan §6⁶(A)) *)
     bown bn k ∗
     bref_tok0 bn k ∗
     ∃ t : nat, CtxBox.l2_hold (X := bio_x) (bn_box bn k) (dev, bno) {[((dev, bno), t) := 1%Qp]})%I.

  Definition bio_held (bn : bio_names) (V : bio_view Σ) (k : nat)
      (pidv dev bno : mword 32) (bs bsl bsd : list (bv 8)) (d : bool) : iProp Σ :=
    (⌜(k < NBUF)%nat⌝ ∗
     ⌜uint bno ∈ bv_cov V⌝ ∗
     ⌜dev = bv_dev V⌝ ∗
     (* the buffer's sleeplock, held -- its [pid] field is INSIDE the token
        now (SleepLock.v's [sleeplocked_q]), so [pidv] indexes the token
        rather than a row of its own. *)
     bstok bn k pidv dev bno ∗
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
     bstok bn k pidv dev bno ∗
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
End BioInv.

Section BioBox.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ}.

  (* ================================================================== *)
  (*  THE BUNDLE, split P_hdr ∗ P_rest (endgame §2, F2): the header is   *)
  (*  what the L1-side code reads or writes (valid / dev / blockno and   *)
  (*  the identity-keyed payload); the rest is the disk cell + data.     *)
  (* ================================================================== *)
  Definition buf_hdr (bn : bio_names) (V : bio_view Σ) (k : nat) (ξ : CtxId)
      (v : bool) (dev bno : mword 32) (bs : list (bv 8)) : iProp Σ :=
    (ctx_word4_pointsto ξ (b_valid (bpa k)) (DfracOwn 1)
       (if v then (mword_of_int 1 : mword 32) else (mword_of_int 0 : mword 32)) ∗
     ctx_word4_pointsto ξ (b_dev (bpa k)) (DfracOwn (1/2)) dev ∗
     ctx_word4_pointsto ξ (b_blockno (bpa k)) (DfracOwn (1/2)) bno ∗
     buf_pay (XI := ξ) bn V k v dev bno bs)%I.
  Definition buf_rest (k : nat) (ξ : CtxId) (bs : list (bv 8)) : iProp Σ :=
    (ctx_word4_pointsto ξ (b_disk (bpa k)) (DfracOwn 1) (mword_of_int 0 : mword 32) ∗
     ⌜length bs = 1024%nat⌝ ∗
     [∗ list] j ↦ byte ∈ bs, ctx_pointsto ξ (pa_add (b_data (bpa k)) j) (DfracOwn 1) byte)%I.
  Definition buf_bundle (bn : bio_names) (V : bio_view Σ) (k : nat)
      (ξ : CtxId) : iProp Σ :=
    (∃ (v : bool) (dev bno : mword 32) (bs : list (bv 8)),
       buf_hdr bn V k ξ v dev bno bs ∗ buf_rest k ξ bs)%I.

  (* the regrouping (F2): the handle's [buf_own] spelling of the bundle *)
  Lemma buf_bundle_own bn V k ξ :
    buf_bundle bn V k ξ ⊣⊢
    (∃ (v : bool) (dev bno : mword 32) (bs : list (bv 8)),
       ctx_word4_pointsto ξ (b_valid (bpa k)) (DfracOwn 1)
         (if v then (mword_of_int 1 : mword 32) else (mword_of_int 0 : mword 32)) ∗
       ctx_word4_pointsto ξ (b_dev (bpa k)) (DfracOwn (1/2)) dev ∗
       buf_own (XI := ξ) (bpa k) bno (mword_of_int 0 : mword 32) bs ∗
       buf_pay (XI := ξ) bn V k v dev bno bs)%I.
  Proof.
    rewrite /buf_bundle /buf_hdr /buf_rest /buf_own. iSplit.
    - iIntros "(%v & %dev & %bno & %bs & (Hv & Hd & Hb & Hp) & (Hdk & %Hl & Hdata))".
      iExists v, dev, bno, bs. iFrame "Hv Hd Hp Hb Hdk Hdata". done.
    - iIntros "(%v & %dev & %bno & %bs & Hv & Hd & (Hb & Hdk & %Hl & Hdata) & Hp)".
      iExists v, dev, bno, bs. iFrame "Hv Hd Hb Hp Hdk Hdata". done.
  Qed.
  (* the invalid header does not mention the data *)
  Lemma buf_hdr_false_bs bn V k ξ dev bno bs bs' :
    buf_hdr bn V k ξ false dev bno bs -∗ buf_hdr bn V k ξ false dev bno bs'.
  Proof.
    rewrite /buf_hdr. iIntros "(Hv & Hd & Hb & Hp)". iFrame "Hv Hd Hb".
    rewrite /buf_pay. case_decide; [iExact "Hp" | iExact "Hp"].
  Qed.

  Global Instance buf_hdr_timeless bn V k ξ v dev bno bs : Timeless (buf_hdr bn V k ξ v dev bno bs).
  Proof.
    rewrite /buf_hdr. apply bi.sep_timeless; [apply _|]. apply bi.sep_timeless; [apply _|].
    apply bi.sep_timeless; apply _.
  Qed.
  Global Instance buf_rest_timeless k ξ bs : Timeless (buf_rest k ξ bs).
  Proof. rewrite /buf_rest. apply bi.sep_timeless; [apply _|]. apply bi.sep_timeless; apply _. Qed.
  Global Instance buf_bundle_timeless bn V k ξ : Timeless (buf_bundle bn V k ξ).
  Proof.
    rewrite /buf_bundle.
    apply bi.exist_timeless; intro v. apply bi.exist_timeless; intro dev.
    apply bi.exist_timeless; intro bno. apply bi.exist_timeless; intro bs.
    apply bi.sep_timeless; apply _.
  Qed.

  Local Instance buf_pay_morph' bn V k v dev bno bs :
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
  Global Instance buf_hdr_morph bn V k v dev bno bs :
    CtxMorph (fun ξ => buf_hdr bn V k ξ v dev bno bs).
  Proof.
    rewrite /buf_hdr.
    apply ctx_morph_sep; [apply ctx_morph_word4|].
    apply ctx_morph_sep; [apply ctx_morph_word4|].
    apply ctx_morph_sep; [apply ctx_morph_word4|].
    apply buf_pay_morph'.
  Qed.
  Global Instance buf_rest_morph k bs : CtxMorph (fun ξ => buf_rest k ξ bs).
  Proof.
    rewrite /buf_rest.
    apply ctx_morph_sep; [apply ctx_morph_word4|].
    apply ctx_morph_sep; [apply ctx_morph_const|].
    apply ctx_morph_big_sepL. intros i x. apply ctx_morph_pointsto.
  Qed.
  Global Instance buf_bundle_morph bn V k : CtxMorph (buf_bundle bn V k).
  Proof.
    rewrite /buf_bundle. apply ctx_morph_exist => v.
    apply ctx_morph_exist => dev. apply ctx_morph_exist => bno.
    apply ctx_morph_exist => bs.
    apply ctx_morph_sep; [apply buf_hdr_morph | apply buf_rest_morph].
  Qed.

  (* [ctx_word4_excl_x] is CtxBox's now (shared with the icache instance) *)

  (* ================================================================== *)
  (*  THE INSTANTIATION of CtxBox at bcache (endgame §4.1): id = dev ×     *)
  (*  blockno, X = the data bytes, P_hdr = the header at an identity (F2),  *)
  (*  P_rest = disk cell + data, tok = bown, Q = emp.                       *)
  (* ================================================================== *)
  Definition bhdr (bn : bio_names) (V : bio_view Σ) (k : nat)
      (i : bio_id) (x : bio_x) (ξ : CtxId) : iProp Σ :=
    (∃ v : bool, buf_hdr bn V k ξ v i.1 i.2 x)%I.
  Definition brest (k : nat) (x : bio_x) (ξ : CtxId) : iProp Σ := buf_rest k ξ x.

  Global Instance bhdr_morph bn V k i x : CtxMorph (bhdr bn V k i x).
  Proof. rewrite /bhdr. apply ctx_morph_exist => v. apply buf_hdr_morph. Qed.
  Global Instance brest_morph k x : CtxMorph (brest k x).
  Proof. rewrite /brest. apply buf_rest_morph. Qed.
  Global Instance bhdr_timeless bn V k i x ξ : Timeless (bhdr bn V k i x ξ).
  Proof. rewrite /bhdr. apply bi.exist_timeless; intro v. apply _. Qed.
  Global Instance brest_timeless k x ξ : Timeless (brest k x ξ).
  Proof. rewrite /brest. apply _. Qed.

  (* the client obligations: a FULL cell in each part (valid / disk) *)
  Lemma bhdr_excl bn V k : forall (i i' : bio_id) (x x' : bio_x) (ξ ξ' : CtxId),
    bhdr bn V k i x ξ -∗ bhdr bn V k i' x' ξ' -∗ False.
  Proof.
    iIntros (i i' x x' ξ ξ') "H1 H2".
    iDestruct "H1" as (v1) "(Hv1 & _)". iDestruct "H2" as (v2) "(Hv2 & _)".
    iDestruct (ctx_word4_excl_x ξ ξ' (b_valid (bpa k)) (DfracOwn 1) with "Hv1 Hv2") as %[].
  Qed.
  Lemma brest_excl k : forall (x x' : bio_x) (ξ ξ' : CtxId),
    brest k x ξ -∗ brest k x' ξ' -∗ False.
  Proof.
    iIntros (x x' ξ ξ') "(Hd1 & _) (Hd2 & _)".
    iDestruct (ctx_word4_excl_x ξ ξ' (b_disk (bpa k)) (DfracOwn 1) with "Hd1 Hd2") as %[].
  Qed.
  Lemma bown_excl bn k : bown bn k -∗ bown bn k -∗ False.
  Proof. apply bown_exclusive. Qed.

  (* the bundle at an identity: CtxBox's in_arm shape, and its [buf_own]
     regrouping (F2) for the handle *)
  Definition buf_bundle_at (bn : bio_names) (V : bio_view Σ) (k : nat)
      (ξ : CtxId) (dev bno : mword 32) : iProp Σ :=
    (∃ x : bio_x, bhdr bn V k (dev, bno) x ξ ∗ brest k x ξ)%I.
  Lemma buf_bundle_at_own bn V k ξ dev bno :
    buf_bundle_at bn V k ξ dev bno ⊣⊢
    (∃ (v : bool) (bs : list (bv 8)),
       ctx_word4_pointsto ξ (b_valid (bpa k)) (DfracOwn 1)
         (if v then (mword_of_int 1 : mword 32) else (mword_of_int 0 : mword 32)) ∗
       ctx_word4_pointsto ξ (b_dev (bpa k)) (DfracOwn (1/2)) dev ∗
       buf_own (XI := ξ) (bpa k) bno (mword_of_int 0 : mword 32) bs ∗
       buf_pay (XI := ξ) bn V k v dev bno bs)%I.
  Proof.
    rewrite /buf_bundle_at /bhdr /brest /buf_hdr /buf_rest /buf_own. iSplit.
    - iIntros "(%bs & (%v & (Hv & Hd & Hb & Hp)) & (Hdk & %Hl & Hdata))".
      iExists v, bs. cbn [fst snd]. iFrame "Hv Hd Hp Hb Hdk Hdata". done.
    - iIntros "(%v & %bs & Hv & Hd & (Hb & Hdk & %Hl & Hdata) & Hp)".
      iExists bs. iSplitL "Hv Hd Hb Hp".
      { iExists v. cbn [fst snd]. iFrame "Hv Hd Hb Hp". }
      iFrame "Hdk Hdata". done.
  Qed.
  Global Instance buf_bundle_at_timeless bn V k ξ dev bno : Timeless (buf_bundle_at bn V k ξ dev bno).
  Proof. rewrite /buf_bundle_at. apply bi.exist_timeless; intro x. apply _. Qed.

  (* ---- the registers, named per buffer ---- *)
  Definition reg_cnt (bn : bio_names) (k : nat) (c : nat) : iProp Σ :=
    cnt_half (X := bio_x) (bn_box bn k) c.
  Definition reg_drop (bn : bio_names) (k : nat) (r : slot_reg bio_id bio_x) : iProp Σ :=
    slotd_half (bn_box bn k) r.
  Definition reg_park (bn : bio_names) (k : nat) (s : l2_reg bio_id) : iProp Σ :=
    slotp_half (X := bio_x) (bn_box bn k) s.
  Definition bstm_frag (bn : bio_names) (k : nat) (m : gmap (bio_id * nat) ufrac) : iProp Σ :=
    stamps_frag (X := bio_x) (bn_box bn k) m.
  Definition bstm_auth (bn : bio_names) (k : nat) (m : gmap (bio_id * nat) ufrac) : iProp Σ :=
    stamps_auth (X := bio_x) (bn_box bn k) m.

  Definition bioxN : namespace := nroot .@ "xv6biox".

  (* THE BOX *)
  Definition buf_box (bn : bio_names) (V : bio_view Σ) (k : nat) : iProp Σ :=
    is_box (bhdr bn V k) (brest k) (λ _ : nat, emp%I) emp%I (bioxN .@ k) (bn_box bn k).
  Global Instance buf_box_persistent bn V k : Persistent (buf_box bn V k).
  Proof. rewrite /buf_box /is_box. apply _. Qed.

  (* ================================================================== *)
  (*  THE SIX LEMMAS at bcache (thin wrappers over CtxBox's; endgame      *)
  (*  §3.5).  The chain and the fractioned reference both carry ONE unit,  *)
  (*  so every fragment here is a unit singleton at the identity.         *)
  (* ================================================================== *)

  (* (a) at c = 0 (the recycle): the caller presents no units *)
  Lemma bbox_withdraw_L1 `{CID : RiscvLang.CpuId} (bn : bio_names) (V : bio_view Σ)
      (k : nat) (ξ : CtxId) (r : slot_reg bio_id bio_x) (Kd : nat) (E : coPset) :
    ↑bioxN ⊆ E ->
    sr_win r = false ->
    (sr_td r <= Kd)%nat ->
    buf_box bn V k -∗
    TsoCtx.own_context ξ -∗
    TsoCtx.ctx_floor ξ Kd -∗
    reg_drop bn k r -∗
    reg_cnt bn k 0 ={E}=∗
    TsoCtx.own_context ξ ∗ reg_cnt bn k 0 ∗
    ∃ (x0 : bio_x) (T0 : nat),
      ⌜(T0 <= Kd)%nat⌝ ∗
      reg_drop bn k (SlotReg (sr_td r) true (sr_ident r) (Some (x0, T0))) ∗
      bhdr bn V k (sr_ident r) x0 ξ.
  Proof.
    iIntros (HE Hw HKd) "#Hbox Hrun #Hfl Hrd Hc".
    assert (HEk : ↑(bioxN .@ k) ⊆ E) by (etrans; [apply nclose_subseteq | exact HE]).
    iMod (own_unit (authUR (gmapUR (bio_id * nat) ufracR)) (bx_stamps (bn_box bn k))) as "Hf0".
    assert (Hq0 : qsum (∅ : gmap (bio_id * nat) ufrac) = nat_Qc 0).
    { rewrite /qsum map_fold_empty /nat_Qc /=. symmetry. apply Z2Qc_inj_0. }
    assert (Hm0 : (max_stamp (∅ : gmap (bio_id * nat) ufrac) <= 0)%nat).
    { rewrite /max_stamp map_fold_empty. lia. }
    iMod (CtxBox.box_withdraw_L1 (bhdr bn V k) (brest k) (λ _ : nat, emp%I) emp%I
            (bioxN .@ k) (bn_box bn k) ξ r 0 ∅ Kd 0 E HEk Hw Hq0 HKd Hm0
            with "Hbox Hrun Hfl [] [] Hrd Hc [Hf0] []") as "(Hrun & Hc & Hout)".
    { iApply TsoCtx.ctx_floor_0. }
    { rewrite /max_stamp map_fold_empty. iApply TsoGhost.llb_0. }
    { rewrite /stamps_frag. iExact "Hf0". }
    { done. }
    iDestruct "Hout" as (x0 T0) "(%HT0 & Hrd & Hhdr)".
    iModIntro. iFrame "Hrun Hc". iExists x0, T0. iFrame "Hrd Hhdr". iPureIntro. lia.
  Qed.

  (* (b) at c = 0: the header comes back at the NEW identity; the chain's
     reference is minted at the deposit stamp *)
  Lemma bbox_deposit_L1 `{CID : RiscvLang.CpuId} (bn : bio_names) (V : bio_view Σ)
      (k : nat) (ξ : CtxId) (Td : nat) (i0 : bio_id) (x0 : bio_x) (T0 : nat)
      (dev bno : mword 32) (E : coPset) :
    ↑bioxN ⊆ E ->
    buf_box bn V k -∗
    TsoCtx.own_context ξ -∗
    reg_drop bn k (SlotReg Td true i0 (Some (x0, T0))) -∗
    reg_cnt bn k 0 -∗
    bhdr bn V k (dev, bno) x0 ξ ={E}=∗
    TsoCtx.own_context ξ ∗
    ∃ T' : nat, reg_drop bn k (SlotReg T' false (dev, bno) None) ∗ reg_cnt bn k 1 ∗
                bref_ghost bn k dev bno ∗ llb loglen_name T'.
  Proof.
    iIntros (HE) "#Hbox Hrun Hrd Hc Hhdr".
    assert (HEk : ↑(bioxN .@ k) ⊆ E) by (etrans; [apply nclose_subseteq | exact HE]).
    iMod (CtxBox.box_deposit_L1 (bhdr bn V k) (brest k) (λ _ : nat, emp%I) emp%I
            (bioxN .@ k) (bn_box bn k) ξ
            (SlotReg Td true i0 (Some (x0, T0))) 0 (dev, bno) x0 T0 E HEk eq_refl eq_refl
            with "Hbox Hrun Hrd Hc Hhdr") as "(Hrun & _ & %T' & Hrd & Hc & Href & #Hllb)".
    iModIntro. iFrame "Hrun". iExists T'. iFrame "Hrd Hllb".
    iSplitL "Hc"; [iExact "Hc"|].
    rewrite /bref_ghost. iExists T'.
    assert (unit_mass 0 = 1%Qp) as -> by reflexivity. iExact "Href".
  Qed.

  (* (c) refs++: the identity from the L1 row's register tie *)
  Lemma bbox_ref_incr (bn : bio_names) (V : bio_view Σ) (k : nat)
      (r : slot_reg bio_id bio_x) (c : nat) (dev bno : mword 32) (E : coPset) :
    ↑bioxN ⊆ E ->
    sr_win r = false ->
    sr_ident r = (dev, bno) ->
    buf_box bn V k -∗
    reg_drop bn k r -∗
    reg_cnt bn k c ={E}=∗
    reg_drop bn k r ∗ reg_cnt bn k (S c) ∗ bref_ghost bn k dev bno.
  Proof.
    iIntros (HE Hw Hid) "#Hbox Hrd Hc".
    assert (HEk : ↑(bioxN .@ k) ⊆ E) by (etrans; [apply nclose_subseteq | exact HE]).
    iMod (CtxBox.box_ref_incr (bhdr bn V k) (brest k) (λ _ : nat, emp%I) emp%I
            (bioxN .@ k) (bn_box bn k) r c E HEk Hw
            with "Hbox Hrd Hc") as "(Hrd & Hc & %T & Href)".
    iModIntro. iFrame "Hrd Hc". rewrite /bref_ghost. iExists T. rewrite Hid. iExact "Href".
  Qed.

  (* (d) refs--: the unit leaves; td := max td t; the row's llb joins the
     reference's *)
  Lemma bbox_ref_decr (bn : bio_names) (V : bio_view Σ) (k : nat)
      (r : slot_reg bio_id bio_x) (c : nat) (dev bno : mword 32) (E : coPset) :
    ↑bioxN ⊆ E ->
    sr_win r = false ->
    buf_box bn V k -∗
    reg_drop bn k r -∗
    llb loglen_name (sr_td r) -∗
    reg_cnt bn k (S c) -∗
    bref_ghost bn k dev bno ={E}=∗
    ∃ td' : nat, ⌜(sr_td r <= td')%nat⌝ ∗
      reg_drop bn k (SlotReg td' false (sr_ident r) (sr_x r)) ∗ reg_cnt bn k c ∗
      llb loglen_name td'.
  Proof.
    iIntros (HE Hw) "#Hbox Hrd #Hllb Hc Href". iDestruct "Href" as (t) "Href".
    assert (HEk : ↑(bioxN .@ k) ⊆ E) by (etrans; [apply nclose_subseteq | exact HE]).
    assert (Hq1 : qsum ({[((dev, bno), t) := 1%Qp]} : gmap (bio_id * nat) ufrac) = nat_Qc 1).
    { rewrite /qsum map_fold_singleton /qsum_step Qcplus_0_r Qp_to_Qc_1 /nat_Qc /=. symmetry. apply Z2Qc_inj_1. }
    iMod (CtxBox.box_ref_decr (bhdr bn V k) (brest k) (λ _ : nat, emp%I) emp%I
            (bioxN .@ k) (bn_box bn k) r c (dev, bno)
            {[((dev, bno), t) := 1%Qp]} E HEk Hw Hq1
            with "Hbox Hrd Hllb Hc Href") as "(Hrd & Hc & #Hllb')".
    iModIntro. iExists (Nat.max (sr_td r) (max_stamp {[((dev, bno), t) := 1%Qp]})).
    iSplitR; [iPureIntro; lia|]. iFrame "Hrd Hc Hllb'".
  Qed.

  (* (e) the checkout: the winner's unit at stamp t (R1 at Tl := t), the
     payload row's pieces (tok, the register half at rest, its floor) *)
  Lemma bbox_checkout `{CID : RiscvLang.CpuId} (bn : bio_names) (V : bio_view Σ)
      (k : nat) (ξ : CtxId) (dev bno : mword 32) (t : nat) (s0 : l2_reg bio_id)
      (Kt Kp : nat) (E : coPset) :
    ↑bioxN ⊆ E ->
    lr_hold s0 = None ->
    (t <= Kt)%nat ->
    (lr_tp s0 <= Kp)%nat ->
    buf_box bn V k -∗
    TsoCtx.own_context ξ -∗
    TsoCtx.ctx_floor ξ Kt -∗
    TsoCtx.ctx_floor ξ Kp -∗
    CtxBox.reference (X := bio_x) (bn_box bn k) (dev, bno) {[((dev, bno), t) := 1%Qp]} -∗
    reg_park bn k s0 ={E}=∗
    TsoCtx.own_context ξ ∗ buf_bundle_at bn V k ξ dev bno ∗
    CtxBox.l2_hold (X := bio_x) (bn_box bn k) (dev, bno) {[((dev, bno), t) := 1%Qp]}.
  Proof.
    iIntros (HE Hs0 HKt HKp) "#Hbox Hrun #Hflt #Hflp Href Hrp".
    assert (HEk : ↑(bioxN .@ k) ⊆ E) by (etrans; [apply nclose_subseteq | exact HE]).
    assert (Hmt : (max_stamp ({[((dev, bno), t) := 1%Qp]} : gmap (bio_id * nat) ufrac) <= Kt)%nat).
    { rewrite /max_stamp map_fold_singleton /max_step /=. lia. }
    iMod (CtxBox.box_checkout (bhdr bn V k) (brest k) (λ _ : nat, emp%I) emp%I
            (bioxN .@ k) (bn_box bn k) ξ (dev, bno)
            {[((dev, bno), t) := 1%Qp]} s0 Kt Kp E HEk Hs0 Hmt HKp
            with "Hbox Hrun Hflt Hflp Href [] Hrp") as "(Hrun & Hbun & Hhold)".
    { done. }
    iModIntro. iFrame "Hrun Hhold". iExact "Hbun".
  Qed.

  (* (f) the park: the bundle at the handle's identity and the handle's
     register half naming the parked unit; the unit moves to the park stamp *)
  Lemma bbox_park `{CID : RiscvLang.CpuId} (bn : bio_names) (V : bio_view Σ)
      (k : nat) (ξ : CtxId) (dev bno : mword 32) (t : nat) (E : coPset) :
    ↑bioxN ⊆ E ->
    buf_box bn V k -∗
    TsoCtx.own_context ξ -∗
    buf_bundle_at bn V k ξ dev bno -∗
    CtxBox.l2_hold (X := bio_x) (bn_box bn k) (dev, bno) {[((dev, bno), t) := 1%Qp]} ={E}=∗
    TsoCtx.own_context ξ ∗
    ∃ T' : nat, reg_park bn k (L2Reg T' None) ∗ bref_ghost bn k dev bno ∗ llb loglen_name T'.
  Proof.
    iIntros (HE) "#Hbox Hrun Hbun Hhold".
    assert (HEk : ↑(bioxN .@ k) ⊆ E) by (etrans; [apply nclose_subseteq | exact HE]).
    iMod (CtxBox.box_park (bhdr bn V k) (brest k) (λ _ : nat, emp%I) emp%I
            (bioxN .@ k) (bn_box bn k) ξ (dev, bno)
            {[((dev, bno), t) := 1%Qp]} E HEk
            with "Hbox Hrun Hbun Hhold") as "(Hrun & _ & %T' & %q & %Hq & Hrp & Href & #Hllb)".
    assert (q = 1%Qp) as ->.
    { apply Qp.to_Qc_inj_iff. rewrite Hq /qsum map_fold_singleton /qsum_step. by rewrite Qcplus_0_r. }
    iModIntro. iFrame "Hrun". iExists T'. iFrame "Hrp Hllb".
    rewrite /bref_ghost. iExists T'. iExact "Href".
  Qed.

  (* ================================================================== *)
  (*  The payload side (v2, A6.142): refs-0 custody in bcache.lock.       *)
  (*  Stated as context-λs -- the lock payload re-indexes at each acquire. *)
  (* ================================================================== *)

  (* the L1 row of endgame §3.2: the drop register's payload half with its
     stamp witnesses, bounded by the payload-level floor slot [tl] *)
  Definition bslot_regs (bn : bio_names) (k : nat) (tl : nat) (dev bno : mword 32) : iProp Σ :=
    (∃ r : slot_reg bio_id bio_x,
       reg_drop bn k r ∗ ⌜sr_win r = false⌝ ∗ ⌜sr_x r = None⌝ ∗ ⌜sr_ident r = (dev, bno)⌝ ∗
       llb loglen_name (sr_td r) ∗ ⌜(sr_td r ≤ tl)%nat⌝)%I.

  (* the L1 slot's tie on the bcache half (A6.155): [None] -- no fractioned
     reference outstanding, the slot keeps the whole half (the other half
     rides the bundle); [Some q] -- the fractioned references hold q of it. *)
  Definition btie (oq : option Qp) (qr : Qp) : Prop :=
    match oq with
    | None => qr = (1/2)%Qp
    | Some q => (q + qr)%Qp = (1/2)%Qp
    end.

  Definition bio_slot_res2 (bn : bio_names) (V : bio_view Σ)
      (M : gmap nat (option Qp * positive)) (k : nat) (dev bno : mword 32)
      (tl : nat) (ξ : CtxId) : iProp Σ :=
    bslot_regs bn k tl dev bno ∗
    match M !! k with
    | None =>
        (ctx_word4_pointsto ξ (brefcnt k) (DfracOwn 1) (mword_of_int 0 : mword 32) ∗
         reg_cnt bn k 0 ∗
         ctx_word4_pointsto ξ (b_dev (bpa k)) (DfracOwn (1/2)) dev ∗
         ctx_word4_pointsto ξ (b_blockno (bpa k)) (DfracOwn (1/2)) bno)%I
    | Some (oq, n) =>
        (⌜(Z.pos n < 2 ^ 31)%Z⌝ ∗
         ctx_word4_pointsto ξ (brefcnt k) (DfracOwn 1)
           (mword_of_int (Z.pos n) : mword 32) ∗
         bslots (Pos.to_nat n) ∗
         reg_cnt bn k (Pos.to_nat n) ∗
         ∃ qr : Qp, ⌜btie oq qr⌝ ∗
           ctx_word4_pointsto ξ (b_dev (bpa k)) (DfracOwn qr) dev ∗
           ctx_word4_pointsto ξ (b_blockno (bpa k)) (DfracOwn qr) bno)%I
    end.

  Definition bcache_scan2 (bn : bio_names) (V : bio_view Σ)
      (M : gmap nat (option Qp * positive)) (ord : list nat)
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

  (* the body ends in a [big_sepL] over the 30 buffer slots, and it sits BARE
     in every fold's goal -- so an unsealed name makes each [iFrame] candidate
     walk all 30 (claude-notes/optimization.md, "a big-op under a transparent
     name is an iFrame bomb").  [rewrite /bcache_scan2], which every fold site
     does on the next line, is unaffected by the seal. *)
  Global Typeclasses Opaque bcache_scan2.

  (* the payload, with its floor slot: R2 folds the releaser's llb here
     ([lock_pay_intro_llb] with [bcache_scan2] as the unfloored body) *)
  Definition bcache_res2 (bn : bio_names) (V : bio_view Σ) (ξ : CtxId) : iProp Σ :=
    (∃ (M : gmap nat (option Qp * positive)) (ord : list nat)
       (devs bnos : nat -> mword 32) (tl : nat),
       TsoCtx.ctx_floor ξ tl ∗ llb loglen_name tl ∗
       bcache_scan2 bn V M ord devs bnos tl ξ)%I.

  Lemma bcache_res2_fold bn V M ord devs bnos tl (ξ : CtxId) :
    bcache_scan2 bn V M ord devs bnos tl ξ ∗ TsoCtx.ctx_floor ξ tl ∗ llb loglen_name tl
    ⊢ bcache_res2 bn V ξ.
  Proof. iIntros "(Hb & #Hfl & #Hllb)". iExists M, ord, devs, bnos, tl. iFrame "Hfl Hllb Hb". Qed.

  (* the _in release's fold: the releaser presents [llb tl] (R2's
     [lock_pay_intro_llb] mints the floor) *)
  Lemma bcache_res2_fold_in bn V M ord devs bnos tl :
    forall ξ : CtxId,
      (llb loglen_name tl ∗ bcache_scan2 bn V M ord devs bnos tl ξ) ∗ TsoCtx.ctx_floor ξ tl
      ⊢ bcache_res2 bn V ξ.
  Proof.
    intros ξ. iIntros "[[#Hl Hs] #Hf]". iApply bcache_res2_fold. iFrame "Hs Hf Hl".
  Qed.

  (* the floor slot is a BOUND: every L1 row's stamp sits below it, so a
     larger slot (a decrement's synced stamp beyond the current slot) keeps
     every row.  The releaser re-floors at the larger slot through the _in
     release (llb of the max is one of the two llbs). *)
  Lemma bcache_scan2_floor_mono bn V M ord devs bnos tl tl' (ξ : CtxId) :
    (tl <= tl')%nat ->
    bcache_scan2 bn V M ord devs bnos tl ξ -∗ bcache_scan2 bn V M ord devs bnos tl' ξ.
  Proof.
    rewrite /bcache_scan2.
    iIntros (Hle) "(Hauth & Hsauth & %Hdom & %Hord & %Hinj & %Hdev & Hlru & Hpool & Hslots)".
    iFrame "Hauth Hsauth Hlru Hpool".
    iSplitR; [done|]. iSplitR; [done|]. iSplitR; [done|]. iSplitR; [done|].
    iApply (big_sepL_mono with "Hslots"). intros i k Hk.
    rewrite /bio_slot_res2. iIntros "[Hregs Hslot]". iFrame "Hslot".
    iDestruct "Hregs" as (r) "(Hrd & %Hw & %Hx & %Hid & #Hllb & %Hb)".
    iExists r. iFrame "Hrd Hllb". iPureIntro. split_and!; [done | done | done | lia].
  Qed.

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
      apply ctx_morph_sep; apply ctx_morph_word4.
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
    apply ctx_morph_sep; [apply _ |].
    apply ctx_morph_sep; [apply ctx_morph_const | apply bcache_scan2_morph].
  Qed.
  Global Instance bcache_scan2_llb_morph bn V M ord devs bnos tl :
    CtxMorph (fun ξ => llb loglen_name tl ∗ bcache_scan2 bn V M ord devs bnos tl ξ)%I.
  Proof. apply ctx_morph_sep; [apply ctx_morph_const | apply bcache_scan2_morph]. Qed.

  (* ---- the sleeplock's client payload (endgame §3.2 / R1-pre): ξ-free,
     bound-indexed -- the checkout token plus the park register's payload
     half with its witnesses, bounded by the sleeplock's floor slot. ---- *)
  Definition bslp_raw (γo γp : gname) (ξ : CtxId) : iProp Σ :=
    (lock_tok_excl γo ∗
     ∃ s : l2_reg bio_id, ghost_var γp (1/2) s ∗ ⌜lr_hold s = None⌝ ∗
       TsoCtx.ctx_floor ξ (lr_tp s))%I.
  Definition bslp (bn : bio_names) (k : nat) : CtxId -> iProp Σ :=
    bslp_raw (bn_own bn k) (bn_regp bn k).
  (* the releaser's unfloored row (R2's [Rdep]), at a KNOWN park stamp *)
  Definition bslp_dep (bn : bio_names) (k : nat) (T' : nat) : CtxId -> iProp Σ :=
    fun _ => (bown bn k ∗ reg_park bn k (L2Reg T' None))%I.
  Lemma bslp_fold bn k T' :
    forall ξ : CtxId, bslp_dep bn k T' ξ ∗ TsoCtx.ctx_floor ξ T' ⊢ bslp bn k ξ.
  Proof.
    intros ξ. iIntros "[(Ho & Hrp) #Hfl]". rewrite /bslp /bslp_raw /bown.
    iFrame "Ho". iExists (L2Reg T' None). rewrite /reg_park /slotp_half /bn_box /=.
    iFrame "Hrp". iSplitR; [done|]. iExact "Hfl".
  Qed.
  (* the checkout's pieces of the payload row *)
  Lemma bslp_unfold bn k (ξ : CtxId) :
    bslp bn k ξ ⊢ bown bn k ∗ ∃ s : l2_reg bio_id, reg_park bn k s ∗ ⌜lr_hold s = None⌝ ∗
                                                  TsoCtx.ctx_floor ξ (lr_tp s).
  Proof.
    iIntros "[Ho Hs]". rewrite /bown. iFrame "Ho". iDestruct "Hs" as (s) "(Hrp & %Hh & #Hfl)".
    iExists s. rewrite /reg_park /slotp_half /bn_box /=. iFrame "Hrp Hfl". done.
  Qed.
  Global Instance bslp_raw_morph γo γp : CtxMorph (bslp_raw γo γp).
  Proof.
    rewrite /bslp_raw. apply ctx_morph_sep; [apply ctx_morph_const|].
    apply ctx_morph_exist => s.
    apply ctx_morph_sep; [apply ctx_morph_const|].
    apply ctx_morph_sep; [apply ctx_morph_const| apply _].
  Qed.
  Global Instance bslp_morph bn k : CtxMorph (bslp bn k).
  Proof. rewrite /bslp. apply _. Qed.

  Section BioSlots2.
  Context `{XI : CurCtx}.

  Lemma bcache_res2_to_scan (bn : bio_names) (V : bio_view Σ) :
    bcache_res2 bn V cur_ctx -∗
    ∃ M ord devs bnos tl,
      TsoCtx.ctx_floor cur_ctx tl ∗ llb loglen_name tl ∗
      bcache_scan2 bn V M ord devs bnos tl cur_ctx.
  Proof. rewrite /bcache_res2. iIntros "H". iExact "H". Qed.

  (* a slot's row is a BOUND on its stamp: it survives a larger floor slot *)
  Lemma bio_slot_res2_floor_mono bn V M k dev bno tl tl' (ξ : CtxId) :
    (tl <= tl')%nat ->
    bio_slot_res2 bn V M k dev bno tl ξ -∗ bio_slot_res2 bn V M k dev bno tl' ξ.
  Proof.
    iIntros (Hle) "[Hregs Hslot]". rewrite /bio_slot_res2. iFrame "Hslot".
    iDestruct "Hregs" as (r) "(Hrd & %Hw & %Hx & %Hid & #Hllb & %Hb)".
    iExists r. iFrame "Hrd Hllb". iPureIntro. split_and!; [done | done | done | lia].
  Qed.

  Lemma bio_slots_acc2 (bn : bio_names) (V : bio_view Σ)
      (M : gmap nat (option Qp * positive)) (devs bnos : nat -> mword 32)
      (tl i : nat) :
    (i < NBUF)%nat ->
    ([∗ list] k ∈ seq 0 NBUF, bio_slot_res2 bn V M k (devs k) (bnos k) tl cur_ctx) -∗
    bio_slot_res2 bn V M i (devs i) (bnos i) tl cur_ctx ∗
    (∀ (M' : gmap nat (option Qp * positive)) (devs' bnos' : nat -> mword 32) (tl' : nat),
       ⌜∀ k, k ≠ i -> M' !! k = M !! k /\ devs' k = devs k /\
             bnos' k = bnos k⌝ -∗
       ⌜(tl <= tl')%nat⌝ -∗
       bio_slot_res2 bn V M' i (devs' i) (bnos' i) tl' cur_ctx -∗
       [∗ list] k ∈ seq 0 NBUF, bio_slot_res2 bn V M' k (devs' k) (bnos' k) tl' cur_ctx).
  Proof.
    iIntros (Hi) "H".
    assert (Hlk : seq 0 NBUF !! i = Some i) by (apply lookup_seq; lia).
    rewrite (big_sepL_delete
               (fun _ k => bio_slot_res2 bn V M k (devs k) (bnos k) tl cur_ctx)
               (seq 0 NBUF) i i Hlk).
    iDestruct "H" as "[$ Hrest]".
    iIntros (M' devs' bnos' tl' HM' Htl) "Hi".
    rewrite (big_sepL_delete
               (fun _ k => bio_slot_res2 bn V M' k (devs' k) (bnos' k) tl' cur_ctx)
               (seq 0 NBUF) i i Hlk).
    iFrame "Hi".
    iApply (big_sepL_impl with "Hrest").
    iIntros "!>" (idx y Hy) "Hs". destruct (decide (idx = i)) as [->|Hne]; [done|].
    apply lookup_seq in Hy as [-> _].
    destruct (HM' _ Hne) as (HMk & Hdk & Hbk).
    iApply (bio_slot_res2_floor_mono with "[Hs]"); [exact Htl|].
    unfold bio_slot_res2. rewrite HMk Hdk Hbk. iExact "Hs".
  Qed.

  (* the LRU scan's borrow of dev/blockno: SOME fraction of both cells *)
  Lemma bio_slot_devbno_acc2 (bn : bio_names) (V : bio_view Σ)
      (M : gmap nat (option Qp * positive)) (k : nat) (dev bno : mword 32) (tl : nat) :
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
    - iDestruct "Hslot" as "(Hcell & Hc & Hdev & Hbno)".
      iExists (1/2)%Qp. iFrame "Hdev Hbno". iIntros "Hdev Hbno".
      iFrame "Hregs Hcell Hc Hdev Hbno".
  Qed.

  (* the backward scan's borrow of the refcnt word, with the [beqz] tie *)
  Lemma bio_slot_refcnt_acc2 (bn : bio_names) (V : bio_view Σ)
      (M : gmap nat (option Qp * positive)) (k : nat) (dev bno : mword 32) (tl : nat) :
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
    - iDestruct "Hslot" as "(Hcell & Hc & Hdev & Hbno)".
      iExists (mword_of_int 0 : mword 32). iFrame "Hcell".
      iSplitR.
      { iPureIntro. left. split; [exact brc_word_zero_eqv | reflexivity]. }
      iIntros "Hcell". iFrame "Hregs Hcell Hc Hdev Hbno".
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
  (* structurally: one [apply _] over the [∗] and the 30-slot [big_sepL]
     backtracks through both lock abstractions' own instances *)
  Proof.
    rewrite /bio_ctx.
    apply bi.sep_persistent; [apply _|].
    apply big_sepL_persistent; intros ? ? ?.
    (* NAME the two leaves: neither [is_sleeplock_genl] nor [buf_box] is
       sealed, so a leaf [apply _] unfolds each into its own body and
       backtracks over it -- which was the whole residue after the peel. *)
    apply bi.sep_persistent;
      [apply is_sleeplock_genl_persistent | apply buf_box_persistent].
  Qed.

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

  (* [big_sepL_llb_max] moved to CtxBox.v (R3.3: the icache boot folds the same way) *)

  (* BOX CONSTRUCTION (box v2, endgame §3.6): the boot content is DEPOSITED
     into a fresh parked context (stamp T_boot); IN, m = ∅, slot_p =
     {| 0; None |}, slot_d = {| T_boot; false; (0,0); None |}.  The caller
     floors L1 at the maximum of the boot stamps through the lock's llb
     mint. *)
  Lemma buf_box_alloc `{CID : RiscvLang.CpuId} (E : coPset) (bn : bio_names)
      (V : bio_view Σ) (k : nat) :
    own_context cur_ctx -∗
    bstm_auth bn k ∅ -∗
    reg_cnt bn k 0 -∗
    reg_park bn k (L2Reg 0 None) -∗
    (∃ r0 : slot_reg bio_id bio_x, ghost_var (bn_regd bn k) 1 r0) -∗
    b_valid (bpa k) ↦₄ (mword_of_int 0 : mword 32) -∗
    b_dev (bpa k) ↦₄{DfracOwn (1/2)} (mword_of_int 0 : mword 32) -∗
    b_blockno (bpa k) ↦₄{DfracOwn (1/2)} (mword_of_int 0 : mword 32) -∗
    b_disk (bpa k) ↦₄ (mword_of_int 0 : mword 32) -∗
    (∃ bs : list (bv 8), ⌜length bs = 1024%nat⌝ ∗
       ([∗ list] j ↦ byte ∈ bs, pa_add (b_data (bpa k)) j ↦ₘ byte) ∗
       buf_pay bn V k false (mword_of_int 0 : mword 32) (mword_of_int 0 : mword 32) bs) ={E}=∗
    own_context cur_ctx ∗ buf_box bn V k ∗
    ∃ Td : nat,
      reg_drop bn k (SlotReg Td false (mword_of_int 0 : mword 32, mword_of_int 0 : mword 32) None) ∗
      llb loglen_name Td.
  Proof.
    iIntros "Hrun Hst Hc Hrp Hrd Hv Hdev Hbno Hdk Hdata".
    iDestruct "Hdata" as (bs) "(%Hlen & Hdata & Hpay)".
    iAssert (buf_bundle_at bn V k cur_ctx (mword_of_int 0 : mword 32) (mword_of_int 0 : mword 32))
      with "[Hv Hdev Hbno Hpay Hdk Hdata]" as "Hbun".
    { rewrite /buf_bundle_at /bhdr /brest /buf_hdr /buf_rest.
      iExists bs. iSplitL "Hv Hdev Hbno Hpay".
      { iExists false. cbn [fst snd]. cbv iota. iFrame "Hv Hdev Hbno Hpay". }
      iFrame "Hdk Hdata". done. }
    iMod (CtxBox.box_alloc_at_halves (bhdr bn V k) (brest k) (λ _ : nat, emp%I) emp%I
            (bioxN .@ k) (bn_box bn k) cur_ctx
            (mword_of_int 0 : mword 32, mword_of_int 0 : mword 32) E
            with "Hrun Hst Hc [Hrd] Hrp Hbun") as "(Hrun & %Tb & #Hbx & Hrd & #Hllb)".
    { rewrite /bn_box /=. iExact "Hrd". }
    iModIntro. iFrame "Hrun". iSplitR; [iExact "Hbx"|]. iExists Tb. iFrame "Hrd Hllb".
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
    (* the stamped-shares authorities, the two registers' halves, the count *)
    iAssert ([∗ list] k ∈ seq 0 NBUF, |={E}=> ∃ γ : gname,
               own γ (● (∅ : gmapUR (bio_id * nat) ufracR)))%I as "Hstm".
    { iApply big_sepL_intro. iIntros "!>" (i k _).
      iMod (own_alloc (● (∅ : gmapUR (bio_id * nat) ufracR))) as (γ) "H"; [by apply auth_auth_valid|].
      iModIntro. iExists γ. iExact "H". }
    iMod (seq_fun_alloc E (fun _ γ => own γ (● (∅ : gmapUR (bio_id * nat) ufracR))) NBUF 0 with "Hstm")
      as (fstm) "Hstm2".
    iAssert ([∗ list] k ∈ seq 0 NBUF, |={E}=> ∃ γ : gname,
               ghost_var γ (1/2) (L2Reg 0 None : l2_reg bio_id) ∗
               ghost_var γ (1/2) (L2Reg 0 None : l2_reg bio_id))%I as "Hgp".
    { iApply big_sepL_intro. iIntros "!>" (i k _).
      iMod (ghost_var_alloc (L2Reg 0 None : l2_reg bio_id)) as (γ) "H".
      iModIntro. iExists γ. iEval (rewrite -{1}Qp.half_half) in "H". iDestruct "H" as "[$ $]". }
    iMod (seq_fun_alloc E (fun _ γ => ghost_var γ (1/2) (L2Reg 0 None : l2_reg bio_id) ∗
                                      ghost_var γ (1/2) (L2Reg 0 None : l2_reg bio_id))%I
            NBUF 0 with "Hgp") as (fregp) "Hregp".
    iAssert ([∗ list] k ∈ seq 0 NBUF, |={E}=> ∃ γ : gname,
               ghost_var γ 1 (SlotReg 0 false (mword_of_int 0 : mword 32, mword_of_int 0 : mword 32) None
                                : slot_reg bio_id bio_x))%I as "Hgd".
    { iApply big_sepL_intro. iIntros "!>" (i k _).
      iMod (ghost_var_alloc (SlotReg 0 false (mword_of_int 0 : mword 32, mword_of_int 0 : mword 32) None
                               : slot_reg bio_id bio_x)) as (γ) "H".
      iModIntro. iExists γ. iExact "H". }
    iMod (seq_fun_alloc E
            (fun _ γ => ghost_var γ 1 (SlotReg 0 false (mword_of_int 0 : mword 32, mword_of_int 0 : mword 32) None
                                          : slot_reg bio_id bio_x)) NBUF 0 with "Hgd")
      as (fregd) "Hregd".
    iAssert ([∗ list] k ∈ seq 0 NBUF, |={E}=> ∃ γ : gname,
               bcnt_var γ 0 ∗ bcnt_var γ 0)%I as "Hgc".
    { iApply big_sepL_intro. iIntros "!>" (i k _).
      iMod (ghost_var_alloc (ghost_varG0 := kalloc_count_inG) 0%nat) as (γ) "H".
      iModIntro. iExists γ. rewrite /bcnt_var. iEval (rewrite -{1}Qp.half_half) in "H".
      iDestruct "H" as "[$ $]". }
    iMod (seq_fun_alloc E (fun _ γ => bcnt_var γ 0 ∗ bcnt_var γ 0)%I
            NBUF 0 with "Hgc") as (fregc) "Hregc".
    iMod (own_alloc (● (∅ : gmap nat (option Qp * positive)) : bioUR)) as (γb) "Hauth".
    { apply auth_auth_valid. intros i. rewrite lookup_empty. done. }
    iMod (newlock_delayed_llb E bcache_addr "bcache"%string with "Hnm Hlkw Hcpu")
      as (γlk) "Hmk".
    (* the sleeplocks, sealed over the λ payload at the park stamp 0 *)
    iEval (rewrite big_sepL_sep) in "Hregp".
    iDestruct "Hregp" as "[Hregp1 Hregp2]".
    iDestruct (big_sepL_sep_2 with "Hfresh Htoks") as "Hsl".
    iDestruct (big_sepL_sep_2 with "Hsl Hregp1") as "Hsl".
    iAssert ([∗ list] idx↦k ∈ seq 0 NBUF,
               own_context cur_ctx -∗
               ((sl_fresh (buf_lock (bnode k)) "buffer"%string ∗
                 lock_tok_excl (fown k)) ∗
                ghost_var (fregp k) (1/2) (L2Reg 0 None : l2_reg bio_id))
               ={E}=∗ own_context cur_ctx ∗
               (∃ p : gname * gname,
                  is_sleeplock_genl (fst p) (snd p) (buf_lock (bnode k))
                    "buffer"%string
                    (bslp_raw (fown k) (fregp k))
                    sl_untracked))%I
      as "Hstep".
    { iApply big_sepL_intro. iIntros "!>" (idx k Hk) "Hrun [[Hf Ht] Hrp]".
      iMod (sl_fresh_new_genl E (buf_lock (bnode k)) "buffer"%string
              (bslp_raw (fown k) (fregp k))
              (fun _ => sl_untracked) with "Hf Hrun [Ht Hrp]") as "[Hrun Hlk]".
      { rewrite /bslp_raw. iFrame "Ht". iExists (L2Reg 0 None). iFrame "Hrp".
        iSplitR; [done|]. simpl. iApply TsoCtx.ctx_floor_0. }
      iDestruct "Hlk" as (γl γsl) "[Hlk _]".
      iModIntro. iFrame "Hrun". iExists (γl, γsl). iExact "Hlk". }
    iMod (big_sepL_fupd_thread E (own_context cur_ctx)
            with "Hrun Hstep Hsl") as "[Hrun Hsl]".
    iAssert ([∗ list] k ∈ seq 0 NBUF, |={E}=> ∃ p : gname * gname,
               is_sleeplock_genl (fst p) (snd p) (buf_lock (bnode k))
                 "buffer"%string
                 (bslp_raw (fown k) (fregp k))
                 sl_untracked)%I
      with "[Hsl]" as "Hsl".
    { iApply (big_sepL_mono with "Hsl"). intros i k Hk.
      iIntros "H". by iModIntro. }
    iMod (seq_fun_alloc E
            (fun k p => is_sleeplock_genl (fst p) (snd p) (buf_lock (bnode k))
                          "buffer"%string
                          (bslp_raw (fown k) (fregp k))
                          sl_untracked)
            NBUF 0 with "Hsl") as (fslk) "#Hsls".
    (* the anchor / pile gname families are DEAD in box v2: any gname does *)
    set (bn := MkBioNames γlk γb fslk fown fmid fown fstm fregp fregd fown fregc).
    assert (Hpay0 : forall k bs,
        buf_pay (XI := cur_ctx) bn V k false (mword_of_int 0 : mword 32)
          (mword_of_int 0 : mword 32) bs = emp%I).
    { intros k bs. rewrite /buf_pay. case_decide as Hd; [|reflexivity].
      exfalso. apply Hnc0. rewrite -Hu0. exact Hd. }
    (* every buffer: the content is DEPOSITED into its box (IN at the boot
       stamp); the slot keeps the bcache half of dev/blockno and the count *)
    iEval (rewrite big_sepL_sep) in "Hregc".
    iDestruct "Hregc" as "[Hregc1 Hregc2]".
    iDestruct (big_sepL_sep_2 with "Hstm2 Hregp2") as "Hap".
    iDestruct (big_sepL_sep_2 with "Hap Hregd") as "Hap".
    iDestruct (big_sepL_sep_2 with "Hap Hregc1") as "Hap".
    iDestruct (big_sepL_sep_2 with "Hregc2 Hbufs") as "Hslr".
    iDestruct (big_sepL_sep_2 with "Hap Hslr") as "Hall".
    iAssert ([∗ list] i↦k ∈ seq 0 NBUF,
               own_context cur_ctx -∗ emp ={E}=∗
               own_context cur_ctx ∗
               (buf_box bn V k ∗
                ∃ Td : nat, llb loglen_name Td ∗
                  (reg_drop bn k (SlotReg Td false (mword_of_int 0 : mword 32, mword_of_int 0 : mword 32) None) ∗
                   (brefcnt k ↦₄ (mword_of_int 0 : mword 32) ∗
                    reg_cnt bn k 0 ∗
                    b_dev (bpa k) ↦₄{DfracOwn (1/2)} (mword_of_int 0 : mword 32) ∗
                    b_blockno (bpa k) ↦₄{DfracOwn (1/2)} (mword_of_int 0 : mword 32)))))%I
      with "[Hall]" as "Hstep2".
    { iApply (big_sepL_impl with "Hall").
      iIntros "!>" (i k Hk).
      iIntros "[(((Hst & Hrp) & Hrd) & Hc) [Hc2 (Hv & Hdk & Hdev & Hbno & Hrc & Hdata)]] Hrun _".
      iDestruct (ctx_word4_pointsto_half_split with "Hdev") as "[Hdev1 Hdev2]".
      iDestruct (ctx_word4_pointsto_half_split with "Hbno") as "[Hbno1 Hbno2]".
      iMod (buf_box_alloc E bn V k with "Hrun Hst Hc Hrp [Hrd] Hv Hdev1 Hbno1 Hdk [Hdata]")
        as "(Hrun & #Hbx & Hreg)".
      { iExists _. iExact "Hrd". }
      { iDestruct "Hdata" as (bs) "[%Hlen Hdata]". iExists bs. iFrame "Hdata".
        iSplitR; [done|]. rewrite Hpay0. done. }
      iModIntro. iFrame "Hrun". iSplitR; [iExact "Hbx"|].
      iDestruct "Hreg" as (Td) "[Hrd0 #Hllb]". iExists Td. iFrame "Hllb Hrd0".
      iFrame "Hrc Hc2 Hdev2 Hbno2". }
    iAssert ([∗ list] i↦k ∈ seq 0 NBUF, emp)%I as "Hemp".
    { rewrite big_sepL_emp. iEmpIntro. }
    iMod (big_sepL_fupd_thread E (own_context cur_ctx) (fun _ _ => emp%I)
            with "Hrun Hstep2 Hemp") as "[Hrun Hboth]".
    iEval (rewrite big_sepL_sep) in "Hboth".
    iDestruct "Hboth" as "[#Hboxs Hslots0]".
    iDestruct (big_sepL_llb_max (seq 0 NBUF)
                 (fun k Td => reg_drop bn k (SlotReg Td false (mword_of_int 0 : mword 32, mword_of_int 0 : mword 32) None) ∗
                              (brefcnt k ↦₄ (mword_of_int 0 : mword 32) ∗
                               reg_cnt bn k 0 ∗
                               b_dev (bpa k) ↦₄{DfracOwn (1/2)} (mword_of_int 0 : mword 32) ∗
                               b_blockno (bpa k) ↦₄{DfracOwn (1/2)} (mword_of_int 0 : mword 32)))%I
                 with "Hslots0") as (tl) "[#Hllbtl Hslots0]".
    iAssert ([∗ list] k ∈ seq 0 NBUF,
               bio_slot_res2 bn V ∅ k (mword_of_int 0 : mword 32)
                 (mword_of_int 0 : mword 32) tl cur_ctx)%I
      with "[Hslots0]" as "Hslots".
    { iApply (big_sepL_mono with "Hslots0"). intros i k _.
      iIntros "(%Td & %Hb & #Hl & Hrd & Hslot)".
      rewrite /bio_slot_res2 lookup_empty.
      iSplitL "Hrd".
      { iExists (SlotReg Td false (mword_of_int 0 : mword 32, mword_of_int 0 : mword 32) None).
        iFrame "Hrd Hl". iPureIntro. cbn. split_and!; [done | done | done | exact Hb]. }
      iExact "Hslot". }
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
    (* L1, minted WITH the fold at the boot floor slot *)
    iMod ("Hmk" $! (fun ξ => bcache_res2 bn V ξ)
            (fun ξ => llb loglen_name tl ∗
                      bcache_scan2 bn V ∅ (rev (seq 0 NBUF))
                        (fun _ => (mword_of_int 0 : mword 32))
                        (fun _ => (mword_of_int 0 : mword 32)) tl ξ)%I tl
            with "[%] [%] Hllbtl Hrun [Hauth Hsa Hslots Hlru Hpool]")
      as "[Hrun #Hlock]".
    { apply _. }
    { apply bcache_res2_fold_in. }
    { iFrame "Hllbtl". rewrite /bcache_scan2.
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

(* A BIG-OP UNDER A TRANSPARENT NAME IS AN [iFrame] BOMB (optimization.md).
   This is [is_lock] plus a [big_sepL] over NBUF, and it is a conjunct of
   [FsReady.fs_ready_pre], so every frame in the FS cone unfolded it and
   tried each candidate hypothesis against all thirty elements.  Measured
   2026-08-27 by sealing it and nothing else: [ProofWritei] 84.3 s ->
   75.0 s.  ([disk_res], sealed the same way, is worth only 1.0 s there --
   size of the body is not what predicts this, being a big-op is.) *)
Global Typeclasses Opaque bio_ctx.
(* AT THE END OF THE FILE: this file's own lemmas take [bio_ctx] apart, and
   they are the accessors every consumer should use instead of unfolding it. *)

(* ===================================================================== *)
(*  [bio_ctx]'s context instance -- HOME (moved from EnvMorph.v, which is  *)
(*  registered after FsReady and invisible to fs_ready_morph; r25 pass 1) *)
(* ===================================================================== *)
Section BioCtxMorph.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ}.

  (* the bcache: the "bcache" spinlock's HANDLE (its payload is already the
     λ [bcache_res2]) plus one sleeplock handle and one box handle per
     buffer.  The sleeplock's own payload λ is [bslp bn k], covered by
     [BioInv.bslp_morph]; [buf_box] is a box handle and so ξ-free. *)
  Global Instance bio_ctx_morph (bn : bio_names) (V : bio_view Σ) :
    CtxMorph (λ ξ : CtxId, (bio_ctx (XI := ξ) bn V : iProp Σ)).
  Proof. rewrite /bio_ctx. ctx_morph_solve. Qed.
End BioCtxMorph.
