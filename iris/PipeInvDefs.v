(* PipeInvDefs.v -- [struct pipe] (kernel/pipe.c): its geometry, the two-ended
   reference algebra, the resource [pi->lock] protects, and the well-formedness
   predicate [is_pipe].

     #define PIPESIZE 512
     struct pipe { struct spinlock lock; char data[PIPESIZE];
                   uint nread; uint nwrite; int readopen; int writeopen; };

   A pipe is one kalloc'd page holding a single self-contained object, so --
   unlike the ftable, whose slots live in a global array under one global lock
   -- EVERYTHING about it is protected by its OWN lock, and there is no
   lock-free immutable part at all: no field of a [struct pipe] is ever read
   without holding [pi->lock].  So the predicate is exactly what the shape of
   the C code says it should be:

     is_pipe γl γp pi  :=  ⌜page_valid pi⌝ ∗
                           inv lockN (lock_inv γl pi "pipe" (pipe_res γp pi)
                                      ∨ pipe_dead γl γp)

   persistent, and [pipe_res] owns every remaining byte of the page -- the
   lock's own name field included, since kfree memsets all 4096.  The lock's
   invariant has a DEAD arm because a pipe's page goes back to kfree: once
   both ends are home the invariant degenerates into [pipe_dead], a husk
   nobody can open again, and the right to touch [pi->lock] at all is a
   resource -- a reference to the pipe, or the lock itself (see below).

   ---- the reference count ----

   xv6 does not give a pipe an int refcount; it gives it TWO int flags,
   [readopen] and [writeopen], one per end, and pipeclose(pi, writable) clears
   the one its argument selects and frees the page when both have reached 0.
   The count of outstanding references IS [readopen + writeopen], so the ghost
   mirrors the ends rather than a single number: per end, a FRACTION ghost

     pipe_ref γp w q  :=  own (pn_end γp w) q
                       -- q of the [w] end of pi ([w] = the struct file's
                          [writable] flag, i.e. pipeclose's second argument)

   with the invariant holding, per end ([pipe_endstate]), either "the flag is
   nonzero" or "the flag is zero AND the whole fraction has come home".  Three
   things fall out, and they are the whole reason for the shape:

   * a holder of ANY positive fraction of an end proves that end's flag is
     nonzero -- otherwise the invariant would hold fraction 1 of it as well;
   * only a holder of the FULL fraction of an end can close it, so an end
     cannot be closed twice, and a file that was [dup]ed cannot close the pipe
     out from under its twin;
   * the closer of the second end recovers fraction 1 of BOTH ends, which is
     the licence to reclaim the page.

   A single counter would not do any of this: it could not tell pipeclose(pi,1)
   twice apart from one close of each end.

   ---- the dead arm, and who may open the lock ----

   The licence to open [pi->lock] is deliberately NOT one resource but two:

     a REFERENCE  refutes [pipe_dead], so acquire may take the lock;
     the LOCK     refutes [pipe_dead], so release may put it down.

   [pipe_dead γl γp] parks BOTH ends at fraction 1 (so any [pipe_ref] is
   inconsistent with it) together with the lock's own state fragment
   [lock_frag γl None] (so any [locked]/[locked_pre] token is too).  The second
   credential is not redundant: by the time the closer of an end calls
   release, its reference has already gone home into [pipe_res], which release
   must be handed INTACT -- so release opens the lock on the strength of the
   lock token it is already carrying.  WpLock's [lock_openable] quantifies the
   credential inside the accessor precisely so the two can coexist
   ([is_pipe_openable] below, via [lock_openable_of_dead]).

   A CANCELLABLE invariant ([cinv]) with its token split across the references
   was the first design and cannot work: [cinv_acc] demands a share of the very
   token that must be WHOLE to cancel, and the first end to close has
   surrendered its share before its own release call, which opens the lock
   four times.  The fraction arithmetic has no solution -- the derivation is in
   claude-notes/design/pipe.md, "Killing the pipe: why not cinv".

   ---- the receipt ----

   [pipe_res] hides its flag words behind existentials, so inside release's
   finisher the last closer cannot re-read them to show both ends are home.
   It carries witnesses instead: [pipe_endstate]'s open side holds an
   exclusive per-end marker ([pipe_openmark], a [DfracOwn 1]), and closing an
   end DISCARDS it, yielding the persistent [pipe_shut].  So an end can never
   re-open (which is what makes [pipe_dead] stable), and the closed side keeps
   a copy of [pipe_shut] that the OTHER closer picks up when it reads that
   flag as 0.  [pipe_res_dead] is the whole argument in one lemma: two receipts
   plus the spent [lock_frag γl None] turn [pipe_res] into
   [pipe_dead ∗ pipe_bytes] -- exactly the wand RELEASE_CANCEL asks for.

   ---- the page, and reclaiming it ----

   [pipe_res] holds the data buffer, the four counter/flag words, AND every
   byte of the page that [struct pipe] does not name (the 4 padding bytes
   inside [struct spinlock], and everything past its 552-byte extent) -- see
   [pipe_slack].  Nothing ever reads those; they are held only so that the
   page can be handed back to kfree, which memsets all 4096 bytes.

   The lock's NAME field is [pipe_res]'s too, held raw rather than sealed into
   a persistent [lock_name]: it is 8 bytes inside the page, and kfree memsets
   all of them.  Nothing reads it, so nothing loses by that.

   ---- why this is its own file ----

   This is the slice of PipeInv.v every HOLDER of a pipe reference needs
   ([FileInv]'s [file_payload], and every whole-function proof that only
   reads/writes through an existing pipe): the geometry, the reference
   algebra, and [is_pipe]/[pipe_held].  PipeInv.v itself keeps the page-carving
   and construction lemmas ([pipe_raw], [page_own_pipe_raw], [new_pipe], ...),
   needed only by pipealloc/pipeclose/piperead/pipewrite's own proofs -- not by
   anything that merely requires a pipe to already exist and be well-formed.
   Splitting them out lets that construction machinery compile IN PARALLEL
   with FileInv/ProcInv/SchedCtx/SpecPiperead/ProofPiperead instead of sitting
   as a serial prerequisite of all of them (it was ~99s on the critical path
   for content none of those five files touch).  See claude-notes/optimization.md.

   Design: claude-notes/design/pipe.md. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import list bitvector.definitions.
From iris.algebra Require Import frac dfrac.
From iris.bi.lib Require Import fractional.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap invariants own.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes.
Require Import RiscvPtsto.
Require Import KallocInv.
Require Import WpLock.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Export Xv6Cameras.  (* the cameras this file states its theory over *)
Local Open Scope Z_scope.


(* ------------------------------------------------------------------ *)
(*  Geometry                                                           *)
(* ------------------------------------------------------------------ *)

Definition PIPESIZE : nat := 512.
Definition pipe_data_off : nat := 24.       (* sizeof(struct spinlock) *)
Definition pipe_sizeof : nat := 552.        (* 24 + 512 + 4*4 *)
Definition pipe_pgbytes : nat := 4096.

(* the field addresses, in the EXACT [add_vec base (sign_extend' 64 imm)] form
   the sw/lw instructions compute (all four offsets fit the 12-bit immediate),
   so a load/store address unifies with the cell without rewriting. *)
Definition poff_of (a : mword 64) (i : Z) : mword 64 :=
  add_vec a (sign_extend' 64 (mword_of_int i : mword 12)).

Definition a_pnread  (pi : mword 64) : mword 64 := poff_of pi 536.
Definition a_pnwrite (pi : mword 64) : mword 64 := poff_of pi 540.

(* the open flag of ONE end, selected by the [writable] bit -- the same bool
   that indexes [pipe_ref] and that pipeclose receives as its argument.  One
   indexed field, not two, so every law below is stated once. *)
Definition a_popen (pi : mword 64) (w : bool) : mword 64 :=
  poff_of pi (if w then 548 else 544).      (* writeopen / readopen *)

(* the lock is the FIRST member, so &pi->lock = pi -- which is exactly the a0
   pipealloc passes to initlock. *)

(* the two flag values, in the form the c.beqz / c.bnez tests consume. *)
Definition pflag_open (v : mword 32) : Prop :=
  neq_vec (sign_extend' 64 v) zero_reg = true.

Lemma pflag_one_open : pflag_open (mword_of_int 1 : mword 32).
Proof. reflexivity. Qed.

Lemma pflag_zero_not_open : ~ pflag_open (mword_of_int 0 : mword 32).
Proof. unfold pflag_open. cbn. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  The queue coupling                                                 *)
(* ------------------------------------------------------------------ *)
(* nread/nwrite are FREE-RUNNING uint32 counters: the live bytes are the
   indices [nread, nwrite) taken in Z/2^32, and there are never more than
   PIPESIZE of them.  This is the well-formedness the read/write proofs
   maintain -- pipewrite's increment is guarded by the failed
   [nwrite == nread + PIPESIZE] test and piperead's by the failed
   [nread == nwrite] test -- and nothing else touches the counters.
   (The CONTENTS of the live window stay existential: copyin/copyout are
   contents-existential, so no observable contract could consume more.) *)
Definition pipe_count (nr nw : mword 32) : Z :=
  ((bv_unsigned nw - bv_unsigned nr) mod 2 ^ 32)%Z.

Definition pipe_count_ok (nr nw : mword 32) : Prop :=
  (pipe_count nr nw <= Z.of_nat PIPESIZE)%Z.

Lemma pipe_count_ok_00 :
  pipe_count_ok (mword_of_int 0 : mword 32) (mword_of_int 0 : mword 32).
Proof. unfold pipe_count_ok, pipe_count. vm_compute. discriminate. Qed.

(* the [mword 32] faces of the RiscvExtras width-64 identities (same
   unfold-to-[bv_add] proof; the width is opaque to it). *)
Local Lemma add_vec32_unsigned (x y : mword 32) :
  bv_unsigned (add_vec x y) = bv_wrap 32 (bv_unsigned x + bv_unsigned y).
Proof.
  unfold add_vec, Operators_mwords.word_binop, Operators_mwords.with_word',
    SailStdpp.Values.with_word, to_word, get_word, MachineWord.MachineWord.add.
  rewrite bv_add_unsigned. reflexivity.
Qed.

Local Lemma wrap32_mod (z : Z) : bv_wrap 32 z = (z mod 2 ^ 32)%Z.
Proof.
  unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 32)%Z with (2 ^ 32)%Z. reflexivity.
Qed.

Local Lemma u32_range (x : mword 32) : (0 <= bv_unsigned x < 2 ^ 32)%Z.
Proof.
  pose proof (bv_unsigned_in_range _ x) as Hr.
  unfold bv_modulus in Hr.
  change (2 ^ Z.of_N 32)%Z with (2 ^ 32)%Z in Hr.
  exact Hr.
Qed.

(* the arithmetic, packaged over plain Z so [lia] never sees a bitvector
   (the zify-hook recipe in durable-notes.md).  a/b are the raw uint32
   values of nread/nwrite. *)
Local Lemma pipe_count_arith_incr (a b : Z) :
  (0 <= a < 2 ^ 32)%Z -> (0 <= b < 2 ^ 32)%Z ->
  ((b - a) mod 2 ^ 32 <= 512)%Z ->
  ((b - a) mod 2 ^ 32 <> 512)%Z ->
  (((b + 1) mod 2 ^ 32 - a) mod 2 ^ 32 <= 512)%Z.
Proof.
  intros Ha Hb Hle Hne.
  rewrite Zminus_mod_idemp_l.
  replace (b + 1 - a)%Z with ((b - a) + 1)%Z by lia.
  rewrite <- (Zplus_mod_idemp_l (b - a) 1).
  assert (H0 : (0 <= (b - a) mod 2 ^ 32 < 2 ^ 32)%Z)
    by (apply Z.mod_pos_bound; vm_compute; reflexivity).
  rewrite Z.mod_small; lia.
Qed.

Local Lemma pipe_count_arith_decr (a b : Z) :
  (0 <= a < 2 ^ 32)%Z -> (0 <= b < 2 ^ 32)%Z ->
  ((b - a) mod 2 ^ 32 <= 512)%Z ->
  a <> b ->
  ((b - (a + 1) mod 2 ^ 32) mod 2 ^ 32 <= 512)%Z.
Proof.
  intros Ha Hb Hle Hne.
  rewrite Zminus_mod_idemp_r.
  replace (b - (a + 1))%Z with ((b - a) - 1)%Z by lia.
  rewrite <- (Zminus_mod_idemp_l (b - a) 1).
  assert (H0 : (0 <= (b - a) mod 2 ^ 32 < 2 ^ 32)%Z)
    by (apply Z.mod_pos_bound; vm_compute; reflexivity).
  assert (Hnz : ((b - a) mod 2 ^ 32 <> 0)%Z).
  { intro Hz. apply Z.mod_divide in Hz; [|vm_compute; discriminate].
    destruct Hz as [k Hk]. assert (k = 0)%Z by nia. lia. }
  rewrite Z.mod_small; lia.
Qed.

(* pipewrite's increment, licensed by the failed full test: if the count is
   in range and [nwrite] is NOT [nread + PIPESIZE], the count after
   [nwrite++] still is. *)
Lemma pipe_count_incr_w (nr nw : mword 32) :
  pipe_count_ok nr nw ->
  nw <> add_vec nr (mword_of_int 512 : mword 32) ->
  pipe_count_ok nr (add_vec nw (mword_of_int 1 : mword 32)).
Proof.
  unfold pipe_count_ok, pipe_count. intros Hok Hne.
  pose proof (u32_range nr) as Hnr. pose proof (u32_range nw) as Hnw.
  rewrite add_vec32_unsigned wrap32_mod.
  assert (H1 : bv_unsigned (mword_of_int 1 : mword 32) = 1%Z) by (vm_compute; reflexivity).
  rewrite H1.
  apply pipe_count_arith_incr; [lia|lia|exact Hok|].
  intro Heq. apply Hne. apply bv_eq.
  rewrite add_vec32_unsigned wrap32_mod.
  assert (H512 : bv_unsigned (mword_of_int 512 : mword 32) = 512%Z) by (vm_compute; reflexivity).
  rewrite H512.
  (* from (nw - nr) mod 2^32 = 512: nw = (nr + 512) mod 2^32 *)
  assert (Hw : ((bv_unsigned nw - bv_unsigned nr) = 512
                \/ (bv_unsigned nw - bv_unsigned nr) = 512 - 2 ^ 32)%Z).
  { assert (Hr : (- 2 ^ 32 < bv_unsigned nw - bv_unsigned nr < 2 ^ 32)%Z) by lia.
    destruct (Z.le_gt_cases 0 (bv_unsigned nw - bv_unsigned nr)) as [Hge | Hlt].
    - left. rewrite Z.mod_small in Heq; lia.
    - right.
      assert (Hshift : ((bv_unsigned nw - bv_unsigned nr) mod 2 ^ 32
                        = (bv_unsigned nw - bv_unsigned nr) + 2 ^ 32)%Z).
      { rewrite <- (Z.mod_small ((bv_unsigned nw - bv_unsigned nr) + 2 ^ 32) (2 ^ 32)); [|lia].
        rewrite <- Zplus_mod_idemp_r. rewrite Z_mod_same_full.
        f_equal. lia. }
      lia. }
  destruct Hw as [Hw | Hw]; [rewrite Z.mod_small; lia|].
  rewrite <- (Z.mod_small (bv_unsigned nw) (2 ^ 32)); [|lia].
  replace (bv_unsigned nw)%Z with ((bv_unsigned nr + 512) + (- 1) * 2 ^ 32)%Z by lia.
  rewrite Z_mod_plus_full. reflexivity.
Qed.

(* piperead's decrement, licensed by the failed empty test: nr ≠ nw means
   the count is nonzero, so [nread++] keeps it in range. *)
Lemma pipe_count_decr_r (nr nw : mword 32) :
  pipe_count_ok nr nw ->
  nr <> nw ->
  pipe_count_ok (add_vec nr (mword_of_int 1 : mword 32)) nw.
Proof.
  unfold pipe_count_ok, pipe_count. intros Hok Hne.
  pose proof (u32_range nr) as Hnr. pose proof (u32_range nw) as Hnw.
  rewrite add_vec32_unsigned wrap32_mod.
  assert (H1 : bv_unsigned (mword_of_int 1 : mword 32) = 1%Z) by (vm_compute; reflexivity).
  rewrite H1.
  apply pipe_count_arith_decr; [lia|lia|exact Hok|].
  intro Heq. apply Hne. by apply bv_eq.
Qed.

(* the return-value range piperead and pipewrite share: -1, or a count
   between 0 and n (n itself clamped at 0 -- a non-positive request writes
   or reads nothing and returns 0). *)
Definition pipe_rw_ret (n : Z) (r : mword 64) : Prop :=
  r = (mword_of_int (-1) : mword 64)
  \/ exists i : Z, r = (mword_of_int i : mword 64) /\ (0 <= i <= Z.max 0 n)%Z.

(* ------------------------------------------------------------------ *)
(*  The reference algebra: one fraction ghost per end                   *)
(* ------------------------------------------------------------------ *)

(* [pipeG] is defined in Xv6Cameras.v.  The NAMES record and its
   accessors stay here. *)

(* a pipe's ghost identity: per end, the reference fraction and the
   "still open" marker. *)
Record pipe_names := MkPipeNames
  { pn_read : gname; pn_write : gname;
    pn_mread : gname; pn_mwrite : gname }.

Definition pn_end (γp : pipe_names) (w : bool) : gname :=
  if w then pn_write γp else pn_read γp.
Definition pn_mark (γp : pipe_names) (w : bool) : gname :=
  if w then pn_mwrite γp else pn_mread γp.

Section PipeInv.
  Context `{!riscvGS Σ, !lockG Σ, !pipeG Σ}.

  (* ---- THE reference: a share of one END of the pipe ----

     Held by whoever holds the [struct file] for that end (FileInv's
     [file_payload]); split by filedup along with the file's own content
     fraction, and recombined by the last fileclose, which then hands the full
     [pipe_ref γp w 1] to pipeclose.  q = 1 is "I am the only holder of this
     end", which is precisely the right to close it.

     A reference is ALSO the licence to touch [pi->lock] at all: acquire opens
     the lock against it (WpLock's [lock_openable]), so a hart with no
     reference to a pipe cannot even take its lock -- which is what makes the
     page reclaimable.  See [pipe_dead]. *)
  Definition pipe_ref (γp : pipe_names) (w : bool) (q : Qp) : iProp Σ :=
    own (pn_end γp w) q.

  (* the same at q = 1, under the name the INVARIANT holds it by once that end
     has been closed and its reference has come home. *)
  Definition pipe_end_full (γp : pipe_names) (w : bool) : iProp Σ :=
    pipe_ref γp w 1%Qp.

  Global Instance pipe_ref_timeless γp w q : Timeless (pipe_ref γp w q).
  Proof. apply _. Qed.
  Global Instance pipe_end_full_timeless γp w : Timeless (pipe_end_full γp w).
  Proof. apply _. Qed.

  Global Instance pipe_ref_fractional γp w :
    Fractional (fun q => pipe_ref γp w q).
  Proof. intros q1 q2. by rewrite /pipe_ref -own_op frac_op. Qed.

  Lemma pipe_ref_split γp w q1 q2 :
    pipe_ref γp w (q1 + q2) ⊣⊢ pipe_ref γp w q1 ∗ pipe_ref γp w q2.
  Proof. by rewrite /pipe_ref -own_op frac_op. Qed.

  Lemma pipe_ref_valid γp w q : pipe_ref γp w q -∗ ⌜(q ≤ 1)%Qp⌝.
  Proof. iIntros "H". by iDestruct (own_valid with "H") as %?%frac_valid. Qed.

  (* the whole point of the [q = 1] state: nobody else holds any of this end. *)
  Lemma pipe_end_full_excl γp w q :
    pipe_end_full γp w -∗ pipe_ref γp w q -∗ False.
  Proof.
    iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as %Hv.
    rewrite frac_op in Hv. apply frac_valid in Hv.
    iPureIntro. exact (Qp.not_add_le_l 1 q Hv).
  Qed.

  Lemma pipe_ref_full_excl γp w q :
    pipe_ref γp w 1 -∗ pipe_ref γp w q -∗ False.
  Proof. apply pipe_end_full_excl. Qed.

  (* ---- the per-end coupling between the flag and the ghost ----

     The OPEN side carries a MARKER, exclusive and created with the pipe.
     Closing an end spends it -- irreversibly, by discarding the fraction --
     and what comes back is [pipe_shut], persistent evidence that this end is
     shut for good.  Two things need it, and neither could be done without:

     - an end can never re-open, which is what makes [pipe_dead] stable;
     - the last closer must be able to say, INSIDE release's finisher and with
       nothing but [pipe_res] in hand, that both ends are home -- and
       [pipe_res] hides its flag words behind existentials.  [pipe_shut] is
       persistent, so a closer keeps a copy and the invariant keeps one too:
       reading the other end's flag as 0 is what hands over that copy. *)
  Definition pipe_openmark (γp : pipe_names) (w : bool) : iProp Σ :=
    own (pn_mark γp w) (DfracOwn 1).
  Definition pipe_shut (γp : pipe_names) (w : bool) : iProp Σ :=
    own (pn_mark γp w) DfracDiscarded.

  Global Instance pipe_openmark_timeless γp w : Timeless (pipe_openmark γp w).
  Proof. apply _. Qed.
  Global Instance pipe_shut_persistent γp w : Persistent (pipe_shut γp w).
  Proof. apply _. Qed.
  Global Instance pipe_shut_timeless γp w : Timeless (pipe_shut γp w).
  Proof. apply _. Qed.

  Lemma pipe_shut_openmark γp w :
    pipe_shut γp w -∗ pipe_openmark γp w -∗ False.
  Proof.
    iIntros "H1 H2".
    by iDestruct (own_valid_2 with "H1 H2") as %?.
  Qed.

  Lemma pipe_openmark_shut γp w : pipe_openmark γp w ==∗ pipe_shut γp w.
  Proof. iIntros "H". iApply (own_update with "H"). apply dfrac_discard_update. Qed.

  Definition pipe_endstate (γp : pipe_names) (w : bool) (v : mword 32) : iProp Σ :=
    (⌜pflag_open v⌝ ∗ pipe_openmark γp w          (* the end is still open *)
     ∨ ⌜v = (mword_of_int 0 : mword 32)⌝ ∗ pipe_end_full γp w ∗ pipe_shut γp w)%I.
                                            (* closed: the reference came home *)

  Global Instance pipe_endstate_timeless γp w v : Timeless (pipe_endstate γp w v).
  Proof. apply _. Qed.

  Lemma pipe_endstate_open_intro γp w v :
    pflag_open v -> pipe_openmark γp w -∗ pipe_endstate γp w v.
  Proof. iIntros (H) "Hm". iLeft. by iFrame "Hm". Qed.

  (* holding ANY share of an end proves its flag is nonzero.  The conclusion is
     pure, so [iDestruct ... as %H] keeps both inputs. *)
  Lemma pipe_endstate_holder γp w v q :
    pipe_endstate γp w v -∗ pipe_ref γp w q -∗ ⌜pflag_open v⌝.
  Proof.
    iIntros "Hst Hq".
    iDestruct "Hst" as "[[%Hop _]|(-> & Hfull & _)]"; [done|].
    iExFalso. iApply (pipe_end_full_excl with "Hfull Hq").
  Qed.

  (* pipeclose closing its own end, at the [pi->{read,write}open = 0] store:
     the reference goes home, the marker is spent, and the receipt comes out. *)
  Lemma pipe_endstate_shut γp w v :
    pipe_endstate γp w v -∗ pipe_ref γp w 1 ==∗
    pipe_endstate γp w (mword_of_int 0 : mword 32) ∗ pipe_shut γp w.
  Proof.
    iIntros "Hst Hfull".
    iDestruct "Hst" as "[[_ Hmark]|(_ & Hhome & _)]".
    2:{ iExFalso. iApply (pipe_end_full_excl with "Hhome Hfull"). }
    iMod (pipe_openmark_shut with "Hmark") as "#Hshut".
    iModIntro. iSplitL "Hfull"; [| iExact "Hshut" ].
    iRight. iFrame "Hfull". iSplit; [done | iExact "Hshut"].
  Qed.

  (* THE receipt in action: it says its end is shut, and hands over that end's
     reference -- without disturbing the invariant, since it is persistent. *)
  Lemma pipe_endstate_shut_elim γp w v :
    pipe_shut γp w -∗ pipe_endstate γp w v -∗
    ⌜v = (mword_of_int 0 : mword 32)⌝ ∗ pipe_end_full γp w.
  Proof.
    iIntros "Hs [[_ Hm]|($ & $ & _)]".
    iExFalso. iApply (pipe_shut_openmark with "Hs Hm").
  Qed.

  (* pipeclose reading the OTHER end's flag and finding it shut: the receipt
     is persistent, so the invariant keeps its copy and the closer walks away
     with one, leaving the endstate exactly as it found it. *)
  Lemma pipe_endstate_closed γp w v :
    ~ pflag_open v ->
    pipe_endstate γp w v -∗ pipe_endstate γp w v ∗ pipe_shut γp w.
  Proof.
    intro Hclosed.
    iIntros "[[%Hop _]|(-> & Hfull & #Hs)]"; [ done | ].
    iSplitL "Hfull"; [| iExact "Hs" ].
    iRight. iFrame "Hfull". iSplit; [done | iExact "Hs"].
  Qed.

  (* the two receipts, in the order [pipe_res_dead] wants them. *)
  Lemma pipe_shut_both γp w :
    pipe_shut γp w -∗ pipe_shut γp (negb w) -∗
    pipe_shut γp false ∗ pipe_shut γp true.
  Proof. destruct w; iIntros "H1 H2"; iFrame. Qed.

  (* ---- the page bytes ---- *)

  (* pi->data[0..PIPESIZE), contents tracked: piperead/pipewrite will need to
     say WHICH bytes are in the pipe, and the byte window is the only place
     that can be said.  (The queue coupling -- the live bytes being those at
     indices [nread, nwrite) mod PIPESIZE -- is not imposed here; it belongs
     with the read/write specs, and lands as an extra conjunct of
     [pipe_res].) *)
  Definition pipe_data (pi : mword 64) (bs : list (bv 8)) : iProp Σ :=
    ([∗ list] j ↦ b ∈ bs, pa_add pi (pipe_data_off + j) ↦ₘ b)%I.

  (* the bytes of the page that [struct pipe] does not name: the 4 padding
     bytes between [lock.locked] and [lock.name], and everything past
     sizeof(struct pipe).  No code touches them; they are held so that the
     page can go back to kfree, which memsets the lot. *)
  Definition pipe_slack (pi : mword 64) : iProp Σ :=
    (([∗ list] j ∈ seq 4 4, byte_any (pa_add pi j)) ∗
     ([∗ list] j ∈ seq pipe_sizeof (pipe_pgbytes - pipe_sizeof),
        byte_any (pa_add pi j)))%I.

  Typeclasses Opaque pipe_data pipe_slack.

  (* ---- the resource pi->lock protects: every byte of the page except the
     lock's own two WORDS (which belong to [lock_inv]).  The lock's NAME field
     is here: nothing reads it, and kfree memsets it, so holding it raw is
     what keeps the page reassemblable. ---- *)
  Definition pipe_res (γp : pipe_names) (pi : mword 64) : iProp Σ :=
    (∃ (nr nw ro wo : mword 32) (vname : mword 64) (bs : list (bv 8)),
       lock_name_field pi ↦₈ vname ∗
       a_pnread pi      ↦₄ nr ∗
       a_pnwrite pi     ↦₄ nw ∗
       a_popen pi false ↦₄ ro ∗
       a_popen pi true  ↦₄ wo ∗
       pipe_endstate γp false ro ∗
       pipe_endstate γp true wo ∗
       ⌜pipe_count_ok nr nw⌝ ∗
       ⌜length bs = PIPESIZE⌝ ∗ pipe_data pi bs ∗
       pipe_slack pi)%I.

  (* every byte of the page except the lock's two WORDS, which release hands
     back separately: what [pipe_res] is once its ghosts are spent, and what
     pipeclose reassembles into [page_own] for kfree. *)
  Definition pipe_bytes (pi : mword 64) : iProp Σ :=
    (∃ (vname : mword 64) (nr nw ro wo : mword 32) (bs : list (bv 8)),
       lock_name_field pi ↦₈ vname ∗
       a_pnread pi      ↦₄ nr ∗
       a_pnwrite pi     ↦₄ nw ∗
       a_popen pi false ↦₄ ro ∗
       a_popen pi true  ↦₄ wo ∗
       ⌜length bs = PIPESIZE⌝ ∗ pipe_data pi bs ∗
       pipe_slack pi)%I.

  (* ---- THE DEAD STATE, and reclamation ----

     A pipe dies exactly when both its ends have come home.  [pipe_dead] is
     what the lock invariant degenerates into: the two end references, parked
     in a husk nobody can ever open again, plus the lock's own state fragment
     -- which is what a HOLDER of the lock refutes it with.  Those two
     refutations are the whole access-control story:

       a REFERENCE  refutes it, so acquire may take the lock;
       the LOCK     refutes it, so release may put it down.

     and the second is not redundant: by the time release runs, the closer's
     reference has already gone home into [pipe_res]. *)
  Definition pipe_dead (γl : gname) (γp : pipe_names) : iProp Σ :=
    (lock_frag γl None ∗ pipe_end_full γp false ∗ pipe_end_full γp true)%I.

  Global Instance pipe_dead_timeless γl γp : Timeless (pipe_dead γl γp).
  Proof. rewrite /pipe_dead /pipe_end_full /pipe_ref /lock_frag. apply _. Qed.

  Lemma pipe_ref_dead γl γp w q :
    pipe_ref γp w q -∗ pipe_dead γl γp -∗ False.
  Proof.
    iIntros "Hq (_ & H0 & H1)". destruct w.
    - iApply (pipe_end_full_excl with "H1 Hq").
    - iApply (pipe_end_full_excl with "H0 Hq").
  Qed.

  Lemma lock_frag_dead γl γp st :
    lock_frag γl st -∗ pipe_dead γl γp -∗ False.
  Proof. iIntros "Hf (Hf' & _ & _)". iApply (lock_frag_exclusive with "Hf Hf'"). Qed.

  Lemma locked_dead γl γp i : ⊢ locked γl i -∗ pipe_dead γl γp -∗ False.
  Proof. iApply lock_frag_dead. Qed.
  Lemma locked_pre_dead γl γp i : ⊢ locked_pre γl i -∗ pipe_dead γl γp -∗ False.
  Proof. iApply lock_frag_dead. Qed.

  (* THE reclamation step, and the reason the whole construction hangs
     together.  The last closer arrives inside release's finisher with a
     receipt for each end -- its own, and the other's, which it got by reading
     that flag as 0 -- and with the state fragment the lock has just given up.
     The receipts say both flags are 0, so both references are inside
     [pipe_res]; out come the dead state and every byte of the object.  This
     is precisely the wand RELEASE_CANCEL asks for. *)
  Lemma pipe_res_dead γl γp pi :
    pipe_shut γp false -∗ pipe_shut γp true -∗
    lock_frag γl None -∗ pipe_res γp pi -∗
    pipe_dead γl γp ∗ pipe_bytes pi.
  Proof.
    iIntros "#Hs0 #Hs1 Hfrag Hres".
    iDestruct "Hres" as (nr nw ro wo vname bs)
      "(Hnm & Hnr & Hnw & Hro & Hwo & Hst0 & Hst1 & %Hcnt & %Hlen & Hdat & Hslack)".
    iDestruct (pipe_endstate_shut_elim with "Hs0 Hst0") as "[-> H0]".
    iDestruct (pipe_endstate_shut_elim with "Hs1 Hst1") as "[-> H1]".
    iSplitL "Hfrag H0 H1"; [ by iFrame "Hfrag H0 H1" | ].
    iExists vname, nr, nw, (mword_of_int 0 : mword 32), (mword_of_int 0 : mword 32), bs.
    by iFrame.
  Qed.

  (* ---- THE predicate: a well-formed [struct pipe] ----

     Persistent, so every holder of either end shares it.  [page_valid] is
     kalloc's guarantee travelling with the object: it is what makes the page
     re-freeable, so it has to survive to pipeclose. *)
  Definition is_pipe (γl : gname) (γp : pipe_names) (pi : mword 64) : iProp Σ :=
    (⌜page_valid pi⌝ ∗
     inv lockN (lock_inv γl pi "pipe" (pipe_res γp pi) ∨ pipe_dead γl γp))%I.

  Global Instance is_pipe_persistent γl γp pi : Persistent (is_pipe γl γp pi).
  Proof. apply _. Qed.

  (* PERFORMANCE: seal it, for the same reason [WpLock.is_lock] is sealed --
     without this, every [iIntros "#Hpipe"] re-derives persistence by unfolding
     into [lock_inv γl pi "pipe" (pipe_res γp pi)] and descending through [pipe_res]
     instead of stopping at the instance above.  Worth 6.5 % of [ProofPiperead]
     on its own (104 s -> 97 s).  The three lemmas below are the interface. *)
  Global Typeclasses Opaque is_pipe.

  Lemma is_pipe_valid γl γp pi : is_pipe γl γp pi -∗ ⌜page_valid pi⌝.
  Proof. rewrite /is_pipe. by iIntros "[$ _]". Qed.
  Lemma is_pipe_inv γl γp pi :
    is_pipe γl γp pi -∗ inv lockN (lock_inv γl pi "pipe" (pipe_res γp pi) ∨ pipe_dead γl γp).
  Proof. rewrite /is_pipe. by iIntros "[_ $]". Qed.

  (* what acquire / holding / release take.  The credential is left to the
     caller: a reference for acquire, the holder token for release. *)
  Lemma is_pipe_openable γl γp pi :
    is_pipe γl γp pi -∗
    lock_openable γl pi "pipe" (pipe_res γp pi) (pipe_dead γl γp).
  Proof. iIntros "H". iApply lock_openable_of_dead. by iApply is_pipe_inv. Qed.

  (* ---- what a [struct file] of type FD_PIPE carries, ADDRESS-KEYED ----

     The pipe itself (persistent) plus the share of the end that the file's
     [writable] flag selects, with the ghost names quantified away -- keyed by
     the pipe's ADDRESS, since that is all [fcontent] records.

     THIS IS NOT WHAT [FileInv.file_payload] USES, and the reason is the
     caveat this comment used to record as future work: two shares of one
     address cannot be RECOMBINED without knowing they name the same [γp], and
     recombining them is exactly what the last fileclose does when it takes
     [file_rest]'s parked fraction back.  FileInv pins the identity instead --
     a per-slot frac-times-agree names field, split by the same fractions as
     the content cells -- and [file_payload] is stated at the NAMED [γp].
     [pipe_held] is kept as the address-keyed form for anything that only ever
     needs to SPLIT (nothing does today). *)
  Definition pipe_held (pi : mword 64) (w : bool) (q : Qp) : iProp Σ :=
    (∃ (γl : gname) (γp : pipe_names), is_pipe γl γp pi ∗ pipe_ref γp w q)%I.
End PipeInv.
