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
From iris.algebra Require Import excl auth gmap frac numbers.
From iris.base_logic.lib Require Import gen_heap invariants own.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes.
Require Import RiscvPtsto.
Require Import WpLock.
Require Import SleepLock.
Require Import BufOwn.
Require Import DiskPtsto.
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
   per buffer the inner-sleeplock pair (γl, γsl), the checkout token's
   gname and the recycle token's gname. *)
Record bio_names := MkBioNames {
  bn_lk   : gname;                (* the "bcache" spinlock               *)
  bn_auth : gname;                (* ● (gmap nat (frac * positive))      *)
  bn_slot : gname;                (* the bslot supply                    *)
  bn_slk  : nat -> gname * gname; (* buffer k's sleeplock (γl, γsl)      *)
  bn_own  : nat -> gname;         (* buffer k's checkout token           *)
  bn_mid  : nat -> gname;         (* buffer k's recycle token            *)
}.

(* THE CLIENT VIEW the whole layer is parametric over: the disk ghost the
   covered blocks' [disk_block] fragments live at, the ONE covered device,
   the covered block-number range, and the two opaque content payloads.
   The log layer instantiates the payloads with its logged-view ghost
   halves (claude-notes/design/fs-log.md); bio itself never opens them.
   [bv_cov] must not contain 0 (binit leaves every buffer's blockno cell
   at 0) -- [bio_init] takes that as a premise. *)
Record bio_view (Σ : gFunctors) := MkBioView {
  bv_gd    : disk_names;
  bv_dev   : SailStdpp.Values.mword 32;
  bv_cov   : gset Z;
  bv_clean : Z -> list (bv 8) -> iProp Σ;
  bv_dirty : Z -> list (bv 8) -> iProp Σ;
  (* the payloads must be TIMELESS: they ride the escrow, whose every open
     happens inside a store's atomic update with no step left to absorb a
     ▷ (the disk_inv precedent -- projects/crash.md M5b).  No real client
     payload is hurt: "bs is the logical content" is ghost state. *)
  bv_clean_tl : forall b bs, Timeless (bv_clean b bs);
  bv_dirty_tl : forall b bs, Timeless (bv_dirty b bs);
}.
Arguments bv_gd {Σ} _.
Arguments bv_dev {Σ} _.
Arguments bv_cov {Σ} _.
Arguments bv_clean {Σ} _.
Arguments bv_dirty {Σ} _.
Arguments bv_clean_tl {Σ} _ _ _.
Arguments bv_dirty_tl {Σ} _ _ _.
Arguments MkBioView {Σ} _ _ _ _ _ _ _.

Global Instance bio_view_clean_timeless {Σ} (V : bio_view Σ) b bs :
  Timeless (bv_clean V b bs) := bv_clean_tl V b bs.
Global Instance bio_view_dirty_timeless {Σ} (V : bio_view Σ) b bs :
  Timeless (bv_dirty V b bs) := bv_dirty_tl V b bs.

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
  Context `{!riscvGS Σ, !lockG Σ, !bioG Σ, !diskGhostG Σ}.

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
  Global Instance bio_pay_timeless bn V k dev bno bsl bsd d :
    Timeless (bio_pay bn V k dev bno bsl bsd d).
  Proof. rewrite /bio_pay. destruct d; apply _. Qed.

  Global Instance pool_blk_timeless V b : Timeless (pool_blk V b).
  Proof. apply _. Qed.

  Global Instance buf_pay_timeless bn V k v dev bno bs :
    Timeless (buf_pay bn V k v dev bno bs).
  Proof. rewrite /buf_pay. case_decide; [destruct v|]; apply _. Qed.

  Global Instance buf_parked_timeless bn V k : Timeless (buf_parked bn V k).
  Proof. apply _. Qed.

  Global Instance buf_chain_timeless bn k : Timeless (buf_chain bn k).
  Proof. apply _. Qed.

  Global Instance buf_mid_timeless V k : Timeless (buf_mid V k).
  Proof. apply _. Qed.

  Global Instance buf_escrow_body_timeless bn V k :
    Timeless (buf_escrow_body bn V k).
  Proof. apply _. Qed.

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
      iDestruct (word4_pointsto_agree with "Hdev Hdev'") as %Heqd. subst dev'.
      rewrite /buf_own.
      iDestruct "Hbuf" as "(Hbno' & Hdisk & %Hlen & Hdata)".
      iDestruct (word4_pointsto_agree with "Hbno Hbno'") as %Heqb. subst bno'.
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
      iDestruct (word4_pointsto_agree with "Hdev Hdev'") as %Heqd. subst dev'.
      rewrite /buf_own.
      iDestruct "Hbuf" as "(Hbno & Hdisk & %Hlen & Hdata)".
      iDestruct (word4_pointsto_agree with "Hbno' Hbno") as %Heqb. subst bno'.
      iSplitR "Htok Hdev' Hbno' Hown".
      { iLeft. rewrite /buf_parked. iExists v, dev, bno, bs.
        iFrame "Hvld Hdev Hpay Hbmid".
        rewrite /buf_own. iFrame "Hbno Hdisk Hdata". done. }
      iExists q. iFrame.
    - iDestruct "Hmid" as (vld bno' bs') "(_ & Hvld' & _)".
      iExFalso. iApply (word4_pointsto_excl with "Hvld' Hvld").
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
         bslots bn (Pos.to_nat n) ∗
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
     bslots_auth bn ∗
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

  Definition bio_ctx (bn : bio_names) (V : bio_view Σ) : iProp Σ :=
    (is_lock (bn_lk bn) bcache_addr "bcache"%string (bcache_res bn V) ∗
     [∗ list] k ∈ seq 0 NBUF,
       (is_sleeplock (fst (bn_slk bn k)) (snd (bn_slk bn k))
          (buf_lock (bnode k)) "buffer"%string (bown bn k) ∗
        buf_escrow bn V k))%I.

  Global Instance bio_ctx_persistent bn V : Persistent (bio_ctx bn V).
  Proof. apply _. Qed.

  Lemma bio_ctx_lock bn V :
    bio_ctx bn V -∗
    is_lock (bn_lk bn) bcache_addr "bcache"%string (bcache_res bn V).
  Proof. iIntros "[$ _]". Qed.

  Lemma bio_ctx_buf bn V k :
    (k < NBUF)%nat ->
    bio_ctx bn V -∗
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
     sleeplocked (snd (bn_slk bn k)) ∗
     sl_pid (buf_lock (bnode k)) ↦₄ pidv ∗
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
     sleeplocked (snd (bn_slk bn k)) ∗
     sl_pid (buf_lock (bnode k)) ↦₄ pidv ∗
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
    - iIntros "(%A & %B & %C & H1 & H2 & H3 & H4 & H5 & H6 & H7)".
      iSplitR "H7"; [|iExact "H7"].
      iSplitR; [done|]. iSplitR; [done|]. iSplitR; [done|]. iFrame.
    - iIntros "[(%A & %B & %C & H1 & H2 & H3 & H4 & H5 & H6) H7]".
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
     authority map is empty and the LRU list is binit's [blist 0 NBUF].

     NEW over the physical layer: the client supplies the whole covered
     range's pool bundles (its [disk_block]s paired with clean payloads --
     for the log layer, the mkfs image's content against the logged-view
     ghost), and 0 must be outside the covered range because every zeroed
     blockno cell claims it. *)
  Lemma bio_init (V : bio_view Σ) E :
    (0 ∉ bv_cov V) ->
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
    bcache_lru bhead (blist 0 NBUF) -∗
    ([∗ set] b ∈ bv_cov V, pool_blk V b) ={E}=∗
    ∃ bn : bio_names, bio_ctx bn V ∗ bslots bn BSLOTS.
  Proof.
    iIntros (Hnc0) "Hlkw #Hnm Hcpu Hfresh Hbufs Hlru Hpool".
    assert (Hu0 : uint (mword_of_int 0 : mword 32) = 0)
      by (vm_compute; reflexivity).
    (* the NBUF checkout tokens and the NBUF recycle tokens, as functions *)
    iMod (tok_fun_alloc NBUF 0) as (fown) "Htoks".
    iMod (tok_fun_alloc NBUF 0) as (fmid) "Hmids".
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
    set (bn := MkBioNames γlk γb γs fslk fown fmid).
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
      iDestruct (word4_pointsto_half_split with "Hdev") as "[Hdev1 Hdev2]".
      iDestruct (word4_pointsto_half_split with "Hbno") as "[Hbno1 Hbno2]".
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
    iMod ("Hmk" $! (bcache_res bn V) with "[Hauth Hsa Hslots Hlru Hpool]")
      as "#Hlock".
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
    iModIntro. iExists bn. rewrite /bio_ctx.
    iSplitR "Hsf"; [| iExact "Hsf"].
    iSplitL "Hlock"; [iExact "Hlock" |].
    rewrite big_sepL_sep. iSplitL "Hsls"; [iExact "Hsls" | iExact "Hescs"].
  Qed.

End BioInv.
