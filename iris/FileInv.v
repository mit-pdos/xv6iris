(* FileInv.v -- the open-file table: [struct file]'s geometry, the
   reference-count algebra, the "holding a reference on a struct file"
   predicate, and the resource [ftable.lock] protects.  Kept apart from any
   whole-function proof so filealloc / filedup / fileclose / sys_open share it.

   The design (and the reasoning behind the algebra) is written up in
   claude-notes/design/file-table.md; the short version:

     struct file { int type; int ref; char readable; char writable;
                   struct pipe *pipe; struct inode *ip; uint off; short major; }
     struct { struct spinlock lock; struct file file[NFILE]; } ftable;

   Three different disciplines govern the fields, and the model keeps them
   apart:

   * [ref] is protected by ftable.lock -- filealloc's scan reads the [ref]
     field of EVERY entry, so all NFILE of those cells live in the lock's
     resource and none of them ever travels with a reference.
   * the other fields are immutable while [ref > 0] and are read with no lock
     at all, so a reference has to carry a real points-to FRACTION of them.
   * [off] is mutable under ip->lock; see the "off" note at the bottom.

   The two halves are tied together by one authoritative ghost map, keyed by
   slot index: [M !! k = Some (q,n)] says slot k has n outstanding references
   holding fraction q of the content between them, and [k ∉ dom M] says the
   slot is free.  Because [fracR] has no unit and [positiveR] no zero, a
   fragment [(q,1)] included in [(qt,n)] forces [n = 1 -> q = qt]: THE HOLDER
   OF THE ONLY REFERENCE HOLDS THE FULL FRACTION, hence write access.  That is
   what licenses sys_open's unlocked initialization of a fresh file and
   fileclose's [f->type = FD_NONE] at ref 0.

   ---- the PAYLOAD ----

   A [struct file] is a reference TO something: a pipe end (FD_PIPE) or an
   inode (FD_INODE / FD_DEVICE).  That resource rides INSIDE [file_ref], at
   the reference's own fraction, and is a FUNCTION of the file's content
   ([file_payload]) -- which is what lets the exclusive holder publish a
   payload by storing to [f->type] and [f->pipe] with no lock held and no
   ghost step, exactly as pipealloc and sys_open do.  The one thing memory
   does not record is the payload's ghost identity, so that is a per-slot
   ghost FIELD ([fpay_tok]) beside the content cells, split by the same
   fractions and agreeing between holders; see the note above [fpnames] for
   why it cannot live on the authority.

   Two fraction laws are the whole of fileclose: [file_rest_absorb] (a
   departing reference's share goes back to the invariant) and
   [file_rest_join] (the last one takes the invariant's leftover, and so
   holds a WHOLE pipe end to hand to pipeclose). *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.algebra Require Import auth gmap frac numbers.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap invariants own cancelable_invariants.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvPtsto RiscvExtras.
Require Import ArrCursor.
Require Export FdSlots.
Require Import WpLock.
Require Import PipeInv.
Require Import IcacheRef.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Local Open Scope Z_scope.

(* ------------------------------------------------------------------ *)
(*  Geometry                                                           *)
(* ------------------------------------------------------------------ *)

(* struct ftable { struct spinlock lock; struct file file[NFILE]; }, so the
   lock is the first member and &ftable.lock = &ftable (SpecFileinit.v). *)
Definition ftable_addr : mword 64 := mword_of_int KernelSyms.ftable.

(* [NFILE] moved to [FdSlots.v] to break the IrefSlots -> FileInv cycle;
   it is still in scope here through this file's own [Require Import
   FdSlots], and [Require Export] keeps it visible to FileInv's importers. *)
Definition file_stride : Z := 40.               (* the loop's [addi s1,s1,40] *)
Definition file_base : Z := KernelSyms.ftable + 24.

(* the [k]th entry, &ftable.file[k].  [fnode NFILE] is one past the last entry
   -- which is where the next global (<disk>) starts, and is the literal end
   pointer filealloc's scan compares its cursor against. *)
Definition fnode (k : nat) : mword 64 := acur file_base file_stride k.

(* the field addresses, in the EXACT [add_vec base (sign_extend' 64 imm)] form
   the instructions compute, so a load/store address unifies with the cell
   without rewriting. *)
Definition foff_of (a : mword 64) (i : Z) : mword 64 :=
  add_vec a (sign_extend' 64 (mword_of_int i : mword 12)).

Definition a_ftype     (k : nat) : mword 64 := fnode k.
Definition a_fref      (k : nat) : mword 64 := foff_of (fnode k) 4.
Definition a_freadable (k : nat) : mword 64 := foff_of (fnode k) 8.
Definition a_fwritable (k : nat) : mword 64 := foff_of (fnode k) 9.
Definition a_fpipe     (k : nat) : mword 64 := foff_of (fnode k) 16.
Definition a_fip       (k : nat) : mword 64 := foff_of (fnode k) 24.
Definition a_foff      (k : nat) : mword 64 := foff_of (fnode k) 32.
Definition a_fmajor    (k : nat) : mword 64 := foff_of (fnode k) 36.

(* the side conditions [ArrCursor]'s cursor lemmas take, discharged once. *)
Lemma file_base_nonneg : 0 <= file_base.
Proof. unfold file_base, KernelSyms.ftable. lia. Qed.
Lemma file_stride_pos : 0 < file_stride.
Proof. unfold file_stride. lia. Qed.
Lemma file_end_fits : file_base + file_stride * Z.of_nat NFILE < 2 ^ 64.
Proof.
  unfold file_base, file_stride, NFILE, KernelSyms.ftable.
  assert (H : (2 ^ 64 = 18446744073709551616)%Z) by (vm_compute; reflexivity).
  rewrite H. lia.
Qed.

(* A FILE SLOT'S ADDRESS IS NEVER NULL.  The geometry alone says so
   ([file_base] is 0x80022478), and several proofs need it: it is what kills
   pipealloc's two dead "*f0 == 0" arms, and what tells sys_pipe that
   installing a file pointer in a descriptor really does fill it. *)
Lemma fnode_nonzero (k : nat) :
  (k < NFILE)%nat -> eq_vec (fnode k : mword 64) (zero_reg : mword 64) = false.
Proof.
  intro Hk. apply eq_vec_false_iff. intro Hc.
  apply (f_equal bv_unsigned) in Hc.
  rewrite (acur_unsigned file_base file_stride k NFILE
             file_base_nonneg file_stride_pos file_end_fits ltac:(lia)) in Hc.
  assert (Hz : bv_unsigned (zero_reg : mword 64) = 0) by reflexivity.
  rewrite Hz in Hc.
  unfold file_base, file_stride, KernelSyms.ftable in Hc.
  lia.
Qed.

(* the same, as a plain disequality -- what a caller reasoning about the
   VALUE stored in a descriptor wants. *)
Lemma fnode_ne_zero (k : nat) :
  (k < NFILE)%nat -> (fnode k : mword 64) <> (zero_reg : mword 64).
Proof.
  intros Hk Hc.
  pose proof (fnode_nonzero k Hk) as Hf.
  apply eq_vec_false_iff in Hf. exact (Hf Hc).
Qed.

(* the four [type] codes (file.h's anonymous enum). *)
Definition FD_NONE   : mword 32 := mword_of_int 0.
Definition FD_PIPE   : mword 32 := mword_of_int 1.
Definition FD_INODE  : mword 32 := mword_of_int 2.
Definition FD_DEVICE : mword 32 := mword_of_int 3.

(* ------------------------------------------------------------------ *)
(*  The reference-count algebra                                        *)
(* ------------------------------------------------------------------ *)

Definition frefUR : ucmra := authUR (gmapUR nat (prodR fracR positiveR)).

(* ------------------------------------------------------------------ *)
(*  The payload's ghost identity, and why it is a SEPARATE COMPONENT    *)
(* ------------------------------------------------------------------ *)

(* A [struct file] of type FD_PIPE owns a share of one END of a pipe
   (PipeInv.v).  [fcontent] records the pipe's ADDRESS -- that is all the
   memory says -- and a pipe's reference is indexed by its ghost names, so a
   payload share has to carry them.  Recording them under an existential
   ([PipeInv.pipe_held]) is not enough: two shares of one slot's payload would
   then not be recombinable, and recombining them is exactly what the last
   [fileclose] does when it takes [file_rest]'s leftover fraction back.

   So the names are a per-slot GHOST FIELD, fractional and agreeing, living
   beside the content cells and split by exactly the same fractions.  What
   fixes its shape is WHERE it has to be written:

   * pipealloc sets [f->type = FD_PIPE] and [f->pipe = pi] holding NO lock --
     it is the exclusive holder (ref == 1), and that is the whole licence.
     So installing the names must need no authority either, which rules out
     an [agree] component on the [frefUR] entry: a fragment of an [auth]
     cannot be updated without the authoritative element, and the authority
     is inside ftable.lock.
   * the fraction still has to agree between holders, and to come home to
     [file_rest] when a reference departs.

   A frac-times-agree gmap with NO authority does both: the exclusive holder
   ([q = 1]) can update the value by a frame-preserving update on its own
   fragment (nothing else can hold a share), and any two shares agree.  It is
   a second COMPONENT of the table's one ghost rather than a second ghost
   name, so that nothing above the file layer -- and no boot wiring -- learns
   that the payload has an identity at all.  The supply is minted with the
   authority ([ftable_ghosts_alloc]), every slot present; a free slot's entry
   is held by the invariant, exactly like its content cells.

   [fp_icv] is the FD_INODE arm's, and is a CANCELLABLE INVARIANT'S name
   rather than the inode's: see [inode_pay] for why a share of an inode
   reference cannot be the reference itself.

   [fp_iq] IS NOT A GHOST NAME, and it is the one field here that is a plain
   number: it is THE FRACTION OF THE INODE'S IDENTITY-AND-LIVENESS SLICE that
   this slot's FD_INODE / FD_DEVICE payload lends its holders, fixed when the
   file is published and unchanged for the file's life.  A holder of file
   fraction [q] carries [q * fp_iq] of it; the parked reference inside the
   cinv is SHORT by exactly [fp_iq], and the last closer's gather adds the two
   back up (see [inode_pay]).

   WHY IT HAS TO BE A CONSTANT RATHER THAN AN EXISTENTIAL.  An existential
   "some share" splits and rejoins freely, which would make
   [file_payload_split] fall out for nothing -- and would make the inode
   UNFREEABLE.  [IcacheRef.inode_held_gather] re-forms the canonical reference
   only from the EXACT fraction that was carved (canonical pairing, design
   §14.6/§14.7), and [IcacheInv.iref_close_last_step] then requires the final
   closer to hold the whole outstanding slice; so every sliver handed out has
   to come back, and an existential fraction lets a holder split and drop
   half.  With a constant, [file_payload_split] is distributivity,
   [(q1 + q2) * Q = q1 * Q + q2 * Q].

   It lives HERE, in the per-slot names, because that is what this record is
   for: per-slot constants agreed across every holder by [fpay_tok]. *)
Record fpnames := MkFPNames
  { fp_lock : gname; fp_pipe : pipe_names; fp_icv : gname; fp_iq : Qp }.

Global Instance fpnames_inhabited : Inhabited fpnames :=
  populate (MkFPNames 1%positive
              (MkPipeNames 1%positive 1%positive 1%positive 1%positive)
              1%positive 1%Qp).

Definition fpayUR : ucmra :=
  gmapUR nat (prodR fracR (agreeR (leibnizO fpnames))).

(* ------------------------------------------------------------------ *)
(*  The off-borrow LIVENESS COUNTER (third component)                   *)
(* ------------------------------------------------------------------ *)

(* [off] lives in a per-slot borrow invariant ([FileOff.v]) whose checked-out
   disjunct parks a token.  The EXCLUSIVE holder of a slot ([q = 1]) has to be
   able to refute a STALE checked-out state -- fileclose and sys_open reach
   [f->off] holding no inode lock at all, so they have nothing to contradict
   the borrower's marker with.  What contradicts it is a COUNT: one fungible
   unit per outstanding reference, with the authority riding beside the
   reference-count authority inside ftable.lock.  At the last reference the
   authority records ONE, so a second unit -- the parked one -- is impossible,
   and the cell must be resident.

   The unit is [◯ {[k := 1%positive]}], a CLOSED element: that is what makes it
   FUNGIBLE, i.e. what lets a borrower prove that the token it takes back on
   return is the token it parked.  A slice of the borrower's own fraction is
   not fungible (the invariant hands it back existentially quantified) which is
   exactly why the marker cannot be one.

   [positiveR], not [natR], for the same reason the reference count uses it: a
   unit-free count has no zero fragment, so the entry can be DELETED when the
   last reference goes.  With [natR] a stale [◯ {[k := 0]}] is a legal frame
   and blocks the deallocating local update. *)
Definition fliveUR : ucmra := authUR (gmapUR nat positiveR).

(* the table's ONE ghost: the reference-count authority, the payload names and
   the off-borrow liveness counter, under a single [γ] -- the [γf] every
   consumer already threads. *)
Definition fileUR : ucmra := prodUR frefUR (prodUR fpayUR fliveUR).

(* the liveness authority's map is the reference-count map's COUNT column: one
   unit per outstanding reference, by construction. *)
Definition Mcount (M : gmap nat (Qp * positive)) : gmap nat positive := snd <$> M.

Lemma Mcount_lookup M k : Mcount M !! k = snd <$> (M !! k).
Proof. rewrite /Mcount lookup_fmap. reflexivity. Qed.
Lemma Mcount_insert M k e : Mcount (<[k := e]> M) = <[k := e.2]> (Mcount M).
Proof. rewrite /Mcount fmap_insert. reflexivity. Qed.
Lemma Mcount_delete M k : Mcount (delete k M) = delete k (Mcount M).
Proof. rewrite /Mcount fmap_delete. reflexivity. Qed.

(* [pipeG] is a SUPERCLASS rather than a sibling context assumption, so that
   the ~100 files that merely mention [proc_priv] do not have to name the
   pipe layer's ghosts.  A file that needs both must take [fileG] alone and
   project: two instance paths to [inG Σ fracR] print identically and do not
   unify.

   [icacheG] and [icfg] are superclasses for the SAME reason, and the rule
   is the same: a file that needs both the file table and the inode cache
   takes [fileG] alone (SpecFileread.v is the one such file today).  They
   are here because an FD_INODE file's payload IS an inode reference --
   [IcacheRef.inode_held] -- so the predicate cannot be stated without the
   cache's algebra and its three constants.  [cinvG] is the cancellable
   invariant the payload's fraction law needs; see [inode_pay]. *)
Class fileG (Σ : gFunctors) := FileG {
  file_inG :: inG Σ fileUR;
  file_pipeG :: pipeG Σ;
  file_icacheG :: icacheG Σ;
  file_cinvG :: cinvG Σ;
  file_icfg :: icfg;
}.
Definition fileΣ : gFunctors := #[GFunctor fileUR; pipeΣ; icacheΣ; cinvΣ].
Global Instance subG_fileΣ {Σ} `{ICFG : icfg} : subG fileΣ Σ -> fileG Σ.
Proof. solve_inG. Qed.

(* The immutable-while-referenced content of a [struct file]: every field but
   [ref] AND [off].

   [off] is deliberately NOT here.  It is neither ftable-protected nor
   immutable-while-referenced: it is mutable under ip->lock, by a holder of an
   arbitrarily SMALL fraction of the reference (fileread does [f->off += r]
   holding whatever share its descriptor has).  A fractional content field
   cannot express that, so [off] lives in its own per-slot borrow invariant --
   [FileOff.v] -- and the only thing FileInv keeps of it is the CELL ADDRESS
   [a_foff] and the liveness counter the borrow protocol needs.  See the "off"
   note at the bottom of this file and design/file-table.md. *)
Record fcontent := MkFContent {
  fc_type     : mword 32;
  fc_readable : bv 8;
  fc_writable : bv 8;
  fc_pipe     : mword 64;
  fc_ip       : mword 64;
  fc_major    : bv 16;
}.

(* ------------------------------------------------------------------ *)
(*  The [ref] word: zero exactly on a free slot                         *)
(* ------------------------------------------------------------------ *)

(* filealloc's scan tests [f->ref] with a sign-extending 4-byte load and a
   [c.beqz], so what the branch consumes is the 64-bit sign extension of the
   stored word.  These two lemmas are the whole content of "the physical test
   and the ghost state agree": a slot outside the authority reads zero, a slot
   inside it reads its (positive, in-range) count and so reads nonzero. *)
Lemma fref_word_zero :
  eq_vec (sign_extend' 64 (mword_of_int 0 : mword 32)) (zero_reg : mword 64) = true.
Proof. apply eq_vec_true_iff. apply bv_eq. vm_compute. reflexivity. Qed.

Lemma fref_word_nonzero (n : positive) :
  Z.pos n < 2 ^ 31 ->
  eq_vec (sign_extend' 64 (mword_of_int (Z.pos n) : mword 32)) (zero_reg : mword 64) = false.
Proof.
  intro Hn.
  (* [lia] cannot evaluate [2^k]; name the three literals first. *)
  assert (E31 : (2 ^ 31 = 2147483648)%Z) by (vm_compute; reflexivity).
  assert (E32 : (2 ^ 32 = 4294967296)%Z) by (vm_compute; reflexivity).
  assert (E64 : (2 ^ 64 = 18446744073709551616)%Z) by (vm_compute; reflexivity).
  rewrite E31 in Hn.
  assert (Hlt32 : (Z.pos n < 2 ^ 32)%Z) by (rewrite E32; lia).
  (* the stored word's unsigned value is [n] itself (no wrap) ... *)
  assert (Hu : bv_unsigned (mword_of_int (Z.pos n) : mword 32) = Z.pos n).
  { unfold mword_of_int, Values.mword_of_int, MachineWord.MachineWord.Z_to_word.
    rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
    change (Z.of_N 32) with 32. rewrite E32.
    rewrite Z.mod_small; [reflexivity | lia]. }
  (* ... and it is below the half modulus, so the sign extension is the
     identity on the value. *)
  assert (Hs : bv_signed (mword_of_int (Z.pos n) : mword 32) = Z.pos n).
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

(* the signed [f->ref < 1] test: a positive in-range count is signed-positive,
   so [bge x0,a5] falls through.  This is what makes filedup's and
   fileclose's panic arms dead for a caller that holds a reference. *)
Lemma fref_word_spos (n : positive) :
  Z.pos n < 2 ^ 31 ->
  zopz0zKzJ_s (zero_reg : mword 64)
              (sign_extend' 64 (mword_of_int (Z.pos n) : mword 32)) = false.
Proof.
  intro Hn.
  unfold zopz0zKzJ_s.
  rewrite Z.geb_leb. apply Z.leb_gt.
  assert (Hz0 : sint (zero_reg : mword 64) = 0%Z) by reflexivity. rewrite Hz0.
  rewrite sint64_moi32; lia.
Qed.

(* the count component's [⋅] IS [Pos.add]; naming it lets [lia] see the
   arithmetic in the local-update side conditions. *)
Lemma pos_op_add (a b : positive) : (a ⋅ b) = (a + b)%positive.
Proof. reflexivity. Qed.
Lemma pos_succ_1_add (b : positive) : Pos.succ (1 + b) = (2 + b)%positive.
Proof. lia. Qed.

Section FileInv.
  Context `{!riscvGS Σ, !lockG Σ, !fileG Σ, !fdslotG Σ}.

  (* ---- the content cells, at an arbitrary fraction ----

     SIX fields: [off] is gone (it is FileOff.v's), and [ref] was never here.

     [a_fip] is held at HALF the nominal fraction, and that is the one piece of
     asymmetry in this predicate.  The other half is held, PERMANENTLY, by the
     off-borrow invariant -- which is how that invariant knows WHICH INODE
     governs this slot's offset.  It has to know: [off] is protected by
     [ip->lock], so the mutual exclusion between two borrowers of slot [k] is
     the exclusivity of one inode's lock, and an invariant that cannot name the
     inode cannot appeal to it.  Points-to agreement then hands a reference
     holder "the invariant's inode is MY inode" for nothing, with no ghost and
     no redundant copy of the pointer.  See FileOff.v.

     A [Qp] rather than a [dfrac]: every use is [DfracOwn], the half above is
     not definable on a discarded share, and the whole design turns on
     fractions adding back up to one. *)
  Definition file_fields (k : nat) (q : Qp) (C : fcontent) : iProp Σ :=
    (a_ftype k     ↦₄{DfracOwn q} fc_type C ∗
     a_freadable k ↦ₘ{DfracOwn q} fc_readable C ∗
     a_fwritable k ↦ₘ{DfracOwn q} fc_writable C ∗
     a_fpipe k     ↦₈{DfracOwn q} fc_pipe C ∗
     a_fip k       ↦₈{DfracOwn (q/2)} fc_ip C ∗
     a_fmajor k    ↦₂{DfracOwn q} fc_major C)%I.

  (* ---- the two components of the table's ghost ----

     [fref_own] is "own this much of the reference-count component and none of
     the payload one"; every existing law about the count is stated over it,
     so the product is invisible below. *)
  Definition fref_own (γ : gname) (a : frefUR) : iProp Σ :=
    own γ ((a, ε) : fileUR).

  Lemma fref_own_op γ a b : fref_own γ (a ⋅ b) ⊣⊢ fref_own γ a ∗ fref_own γ b.
  Proof.
    rewrite /fref_own -own_op.
    assert (H : (((a, ε) : fileUR) ⋅ (b, ε)) ≡ ((a ⋅ b, ε) : fileUR)).
    { rewrite -pair_op left_id. reflexivity. }
    by rewrite H.
  Qed.

  Lemma fref_own_update γ a b : (a ~~> b) -> fref_own γ a ==∗ fref_own γ b.
  Proof.
    intros Hup. rewrite /fref_own. iApply own_update.
    apply prod_update; [exact Hup | done].
  Qed.

  Lemma fref_own_update_2' γ a b c :
    (a ⋅ b ~~> c) -> fref_own γ a -∗ fref_own γ b ==∗ fref_own γ c.
  Proof.
    intros Hup. iIntros "Ha Hb".
    iDestruct (fref_own_op γ a b with "[$Ha $Hb]") as "H".
    by iApply (fref_own_update with "H").
  Qed.

  Lemma fref_own_update_2 γ a b a' b' :
    (a ⋅ b ~~> a' ⋅ b') ->
    fref_own γ a -∗ fref_own γ b ==∗ fref_own γ a' ∗ fref_own γ b'.
  Proof.
    intros Hup. iIntros "Ha Hb".
    iDestruct (fref_own_op γ a b with "[$Ha $Hb]") as "H".
    iMod (fref_own_update _ _ (a' ⋅ b') Hup with "H") as "H".
    by iApply fref_own_op.
  Qed.

  Lemma fref_own_valid_2 γ a b :
    fref_own γ a -∗ fref_own γ b -∗ ⌜✓ (a ⋅ b)⌝.
  Proof.
    rewrite /fref_own. iIntros "Ha Hb".
    iDestruct (own_valid_2 with "Ha Hb") as %[Hv _]. done.
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  The off-borrow liveness counter                                    *)
  (* ------------------------------------------------------------------ *)

  (* "own this much of the liveness component and none of the other two" --
     the same shape as [fref_own], so the counter's laws are stated without
     the product ever showing. *)
  Definition flive_own (γ : gname) (a : fliveUR) : iProp Σ :=
    own γ ((ε, (ε, a)) : fileUR).

  Lemma flive_own_op γ a b : flive_own γ (a ⋅ b) ⊣⊢ flive_own γ a ∗ flive_own γ b.
  Proof.
    rewrite /flive_own -own_op.
    assert (H : (((ε, (ε, a)) : fileUR) ⋅ (ε, (ε, b)))
                ≡ ((ε, (ε, a ⋅ b)) : fileUR)).
    { rewrite -!pair_op !left_id. reflexivity. }
    by rewrite H.
  Qed.

  Lemma flive_own_update γ a b : (a ~~> b) -> flive_own γ a ==∗ flive_own γ b.
  Proof.
    intros Hup. rewrite /flive_own. iApply own_update.
    apply prod_update; [done|]. cbn [fst snd].
    apply prod_update; [done | exact Hup].
  Qed.

  Lemma flive_own_update_2 γ a b a' b' :
    (a ⋅ b ~~> a' ⋅ b') ->
    flive_own γ a -∗ flive_own γ b ==∗ flive_own γ a' ∗ flive_own γ b'.
  Proof.
    intros Hup. iIntros "Ha Hb".
    iDestruct (flive_own_op γ a b with "[$Ha $Hb]") as "H".
    iMod (flive_own_update _ _ (a' ⋅ b') Hup with "H") as "H".
    by iApply flive_own_op.
  Qed.

  Lemma flive_own_update_2' γ a b c :
    (a ⋅ b ~~> c) -> flive_own γ a -∗ flive_own γ b ==∗ flive_own γ c.
  Proof.
    intros Hup. iIntros "Ha Hb".
    iDestruct (flive_own_op γ a b with "[$Ha $Hb]") as "H".
    by iApply (flive_own_update with "H").
  Qed.

  Lemma flive_own_valid_2 γ a b :
    flive_own γ a -∗ flive_own γ b -∗ ⌜✓ (a ⋅ b)⌝.
  Proof.
    rewrite /flive_own. iIntros "Ha Hb".
    iDestruct (own_valid_2 with "Ha Hb") as %[_ [_ Hv]]. done.
  Qed.

  (* ONE unit of "there is an outstanding reference on slot k".  A closed
     element, hence fungible: what comes back out of the borrow invariant is
     provably what went in. *)
  Definition flive_tok (γ : gname) (k : nat) : iProp Σ :=
    flive_own γ (◯ {[ k := 1%positive ]}).

  (* the authoritative element, held by [ftable_res] inside ftable.lock.  It is
     BOTH authorities -- the reference-count one and the off-borrow liveness
     one, whose map is the count column of the same [M].  Bundling them here
     rather than adding a conjunct to [ftable_res] keeps every ghost step's
     statement, and hence every caller, unchanged. *)
  Definition ftable_auth (γ : gname) (M : gmap nat (Qp * positive)) : iProp Σ :=
    (fref_own γ (● M) ∗ flive_own γ (● Mcount M))%I.

  (* ---- one reference's ghost fragment ---- *)
  Definition fref_tok (γ : gname) (k : nat) (q : Qp) : iProp Σ :=
    fref_own γ (◯ {[ k := (q, 1%positive) ]}).


  (* ------------------------------------------------------------------ *)
  (*  The payload: the thing a [struct file] is a reference TO            *)
  (* ------------------------------------------------------------------ *)

  (* ---- AN FD_INODE FILE'S PAYLOAD: A SHARE OF ONE INODE REFERENCE ----

     The predicate this file carried as [emp] until C6b.  What replaced it
     is NOT [IcacheRef.inode_held] at fraction [q], and the reason is the
     whole content of the definition:

     an icache reference is [iref_tok γ k q ∗ inode_ident k q dev inum],
     and its ghost fragment [◯ {[k := (q, 1%positive)]}] carries a COUNT of
     one.  Two of them compose to a count of TWO -- a second reference,
     which the itable would have to have handed out.  So [inode_held] does
     not split fractionally, at any fraction, and [file_payload_split] --
     which is a genuine ⊣⊢, used leftwards by filedup and rightwards by
     fileclose -- cannot be satisfied by any function of [q] that mentions
     the token directly.  Recombining a resource that is not itself
     fractional out of fractional shares is exactly what a CANCELLABLE
     INVARIANT is for, and it is what [PipeInv] already does one layer down
     ([pipe_ref] carries [cinv_own (pn_cancel γp) (q/2)] beside its own
     fraction).  So: the reference goes into a [cinv], the persistent half
     rides every share, and the FRACTION is the cancel token.  The last
     closer -- and only it -- holds [cinv_own γx 1], cancels, and walks
     away with a WHOLE [inode_held] to give to iput.

     THE THIRD CONJUNCT, AND WHY THE PARKED REFERENCE IS SHORT (design §14.6's
     "share beside the cinv").  A cancel token alone says nothing ABOUT the
     inode: it cannot be read through, and it cannot discharge a contract that
     wants to know the entry is live -- which is exactly what a reader needs
     ([SpecFileread]'s [frn_s], and [SpecIlock] v3 behind it, both take an
     [IcacheRef.inode_shr]).  So a real slice travels beside the token.

     IT CANNOT BE CARVED OUT OF THE PARKED REFERENCE ON DEMAND, because the
     cinv's content is not accessible without cancelling it.  It is carved
     ONCE, when the payload is published ([inode_pay_alloc]), and what goes
     into the cinv is therefore the parent SHORT by the whole outstanding
     slice: [IcacheRef.inode_held_short v (fp_iq pn)].  That is not a breach of
     canonical pairing -- [inode_ref_short] IS the design's name for a parent
     with a share out, and the pairing is restored by the gather, which is the
     last closer's move ([inode_pay_cancel]) and happens before iput ever sees
     the reference.  Nothing can spend the parked reference in the meantime:
     the cinv is the only holder and cancelling it is what the closer does.

     The travelling slice is PROPORTIONAL, [q * fp_iq pn], so that the split
     law is distributivity and the closer at [q = 1] holds exactly the
     [fp_iq pn] the cinv is short by.  See the header above [fpnames] for why
     the constant cannot be an existential.

     [v] is the pointer, not the slot: [ientry_inj] makes them the same
     thing, and the file table has no vocabulary for a slot -- which is why
     both [inode_held_short] and [inode_shr_held] are stated at the pointer. *)
  Definition fileipN : namespace := nroot .@ "fileip".

  Definition inode_pay (γx : gname) (Q : Qp) (v : mword 64) (q : Qp) : iProp Σ :=
    (cinv fileipN γx (inode_held_short v Q) ∗ cinv_own γx q ∗
     inode_shr_held v (q * Q)%Qp)%I.

  Lemma inode_pay_split γx Q v q1 q2 :
    inode_pay γx Q v (q1 + q2) ⊣⊢ inode_pay γx Q v q1 ∗ inode_pay γx Q v q2.
  Proof.
    rewrite /inode_pay cinv_own_fractional Qp.mul_add_distr_r
            inode_shr_held_split.
    iSplit.
    - iIntros "(#Hi & [H1 H2] & [S1 S2])". iFrame "Hi H1 H2 S1 S2".
    - iIntros "[(#Hi & H1 & S1) (_ & H2 & S2)]". iFrame "Hi H1 H2 S1 S2".
  Qed.

  (* THE LAST CLOSER'S MOVE, packaged: fraction one is the whole reference.
     A fupd, and the only one the file layer performs.  The gather is what
     makes it a WHOLE one -- the cinv gives back the parent short by [Q] and
     the closer's own arm is [1 * Q], the exact complement. *)
  Lemma inode_pay_cancel (E : coPset) (γx : gname) (Q : Qp) (v : mword 64) :
    ↑fileipN ⊆ E -> inode_pay γx Q v 1 ={E}=∗ inode_held v.
  Proof.
    iIntros (HE) "(#Hi & Hown & Hs)".
    iMod (cinv_cancel with "Hi Hown") as "H"; [exact HE|].
    iMod "H". iModIntro. rewrite Qp.mul_1_l.
    iApply (inode_held_gather with "H Hs").
  Qed.

  (* ...and its inverse, for whoever PUBLISHES an FD_INODE file (sys_open):
     an inode reference becomes a payload at fraction one.  The constant is
     the publisher's to choose -- it comes OUT of the carve here, and the
     [fpnames] it installs in the same breath is where it is recorded. *)
  Lemma inode_pay_alloc (E : coPset) (v : mword 64) :
    inode_held v ={E}=∗ ∃ (γx : gname) (Q : Qp), inode_pay γx Q v 1.
  Proof.
    iIntros "H".
    iDestruct (inode_held_shed with "H") as (Q) "[Hsh Hs]".
    iMod (cinv_alloc E fileipN (inode_held_short v Q) with "[Hsh]")
      as (γx) "[#Hi Hown]".
    { by iNext. }
    iModIntro. iExists γx, Q. rewrite /inode_pay Qp.mul_1_l.
    by iFrame "Hi Hown Hs".
  Qed.

  (* the per-slot payload-names ghost: fractional, agreeing, and updatable
     by whoever holds the whole of it.  See the header above [fpnames]. *)
  Definition fpay_tok (γ : gname) (k : nat) (q : Qp) (pn : fpnames) : iProp Σ :=
    own γ ((ε, ({[ k := (q, to_agree (pn : leibnizO fpnames)) ]}, ε)) : fileUR).

  Lemma fpay_tok_split γ k q1 q2 pn :
    fpay_tok γ k (q1 + q2) pn ⊣⊢ fpay_tok γ k q1 pn ∗ fpay_tok γ k q2 pn.
  Proof.
    rewrite /fpay_tok -own_op.
    assert (H : (((ε, ({[ k := (q1, to_agree (pn : leibnizO fpnames)) ]}, ε)) : fileUR)
                 ⋅ (ε, ({[ k := (q2, to_agree (pn : leibnizO fpnames)) ]}, ε)))
                ≡ ((ε, ({[ k := ((q1 + q2)%Qp, to_agree (pn : leibnizO fpnames)) ]}, ε))
                   : fileUR)).
    { rewrite -!pair_op !left_id singleton_op -pair_op frac_op agree_idemp.
      reflexivity. }
    by rewrite H.
  Qed.

  Lemma fpay_tok_agree γ k q1 pn1 q2 pn2 :
    fpay_tok γ k q1 pn1 -∗ fpay_tok γ k q2 pn2 -∗ ⌜pn1 = pn2⌝.
  Proof.
    rewrite /fpay_tok. iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as %[_ [Hv _]]. iPureIntro.
    simpl in Hv. rewrite singleton_op in Hv. apply singleton_valid in Hv.
    destruct Hv as [_ Hv]; simpl in Hv.
    by apply to_agree_op_valid_L in Hv.
  Qed.

  (* THE reason the names are not on the ftable authority: the exclusive
     holder installs them with no lock in hand.  This is pipealloc's ghost
     step, and it happens at the [sd] that writes [f->pipe]. *)
  Lemma fpay_tok_update γ k pn pn' :
    fpay_tok γ k 1 pn ==∗ fpay_tok γ k 1 pn'.
  Proof.
    rewrite /fpay_tok. iIntros "H". iApply (own_update with "H").
    apply prod_update; [done|]. cbn [fst snd].
    apply prod_update; [|done]. cbn [fst snd].
    apply singleton_update, cmra_update_exclusive. done.
  Qed.

  (* [f->writable] as the BOOL that indexes the pipe's two ends -- the same
     bool pipeclose takes as its second argument, and the truth value of the
     byte fileclose loads with [lbu]. *)
  Definition fc_wbool (C : fcontent) : bool :=
    negb (eq_vec (fc_writable C : mword 8) (mword_of_int 0 : mword 8)).

  (* WHAT THE FILE OWNS, as a function of its CONTENT and its payload names.
     A function of [C] alone (given the names) is what lets the exclusive
     holder publish a payload by STORING to [f->type] and [f->pipe]: there is
     no ghost step to perform and no lock to hold, which is precisely the
     situation pipealloc and sys_open are in.

     The free state pins [fc_type = FD_NONE], so a free slot carries no
     payload -- which is the real xv6 invariant: fileclose writes FD_NONE
     before releasing, and the BSS starts zeroed. *)
  Definition file_payload (q : Qp) (pn : fpnames) (C : fcontent) : iProp Σ :=
    (if bool_decide (fc_type C = FD_PIPE)
     then is_pipe (fp_lock pn) (fp_pipe pn) (fc_pipe C) ∗
          pipe_ref (fp_pipe pn) (fc_wbool C) q
     else if bool_decide (fc_type C = FD_INODE) || bool_decide (fc_type C = FD_DEVICE)
     then inode_pay (fp_icv pn) (fp_iq pn) (fc_ip C) q
     else emp)%I.

  Lemma file_payload_split q1 q2 pn C :
    file_payload (q1 + q2) pn C ⊣⊢ file_payload q1 pn C ∗ file_payload q2 pn C.
  Proof.
    rewrite /file_payload.
    case_bool_decide as Hp; [|case_match].
    - rewrite pipe_ref_split. iSplit.
      + iIntros "(#Hi & H1 & H2)". iSplitL "H1"; (iSplitR; [iExact "Hi"|iFrame]).
      + iIntros "[[#Hi H1] [_ H2]]". iSplitR; [iExact "Hi"|]. iFrame.
    - apply inode_pay_split.
    - by rewrite left_id.
  Qed.

  (* the payload with its names quantified -- the form a reference carries,
     since nothing outside the file layer names a pipe's ghosts.  It still
     JOINS, because the names ghost makes the two shares agree. *)
  Definition file_pay (γ : gname) (k : nat) (q : Qp) (C : fcontent) : iProp Σ :=
    (∃ pn, fpay_tok γ k q pn ∗ file_payload q pn C)%I.

  Lemma file_pay_split γ k q1 q2 C :
    file_pay γ k (q1 + q2) C ⊣⊢ file_pay γ k q1 C ∗ file_pay γ k q2 C.
  Proof.
    rewrite /file_pay. iSplit.
    - iIntros "(%pn & Hn & Hp)".
      rewrite fpay_tok_split file_payload_split.
      iDestruct "Hn" as "[Hn1 Hn2]". iDestruct "Hp" as "[Hp1 Hp2]".
      iSplitL "Hn1 Hp1"; by iExists pn; iFrame.
    - iIntros "[(%pn1 & Hn1 & Hp1) (%pn2 & Hn2 & Hp2)]".
      iDestruct (fpay_tok_agree with "Hn1 Hn2") as %<-.
      iExists pn1. rewrite fpay_tok_split file_payload_split. iFrame.
  Qed.

  (* ---- THE predicate: holding one reference on file slot [k] ----

     The unit of ownership everywhere a [struct file *] is held: a process's
     p->ofile[fd], a syscall's local [struct file *f], pipealloc's two
     half-built files.  It is NOT persistent and NOT duplicable -- duplicating
     it is filedup, which must run under ftable.lock and bump the physical
     count.  [file_ref γ k 1 C] is the exclusive (writable) state. *)
  Definition file_ref (γ : gname) (k : nat) (q : Qp) (C : fcontent) : iProp Σ :=
    (fref_tok γ k q ∗ file_fields k q C ∗ file_pay γ k q C ∗ flive_tok γ k)%I.

  (* ---- the ftable lock's resource ----

     The invariant holds every slot's [ref] cell (filealloc scans them all),
     and, per slot, whatever content fraction has NOT been handed out: all of
     it when the slot is free, [1-q] when q is out, nothing at all when q = 1.
     Note what is NOT here: the content of a referenced file.  That is exactly
     why fileread can read f->type / f->ip holding no lock. *)
  Definition file_rest (γ : gname) (k : nat) (q : Qp) : iProp Σ :=
    match (1 - q)%Qp with
    | Some q' => (∃ C, file_fields k q' C ∗ file_pay γ k q' C)%I
    | None    => emp%I
    end.

  (* q = 1 -- every share is out, so the invariant keeps nothing. *)
  Lemma file_rest_full (γ : gname) (k : nat) : file_rest γ k 1 ⊣⊢ emp.
  Proof.
    rewrite /file_rest.
    assert (Hs : (1 - 1)%Qp = None) by (apply Qp.sub_None; done).
    rewrite Hs. reflexivity.
  Qed.

  (* A referenced slot holds ONE fd slot per outstanding reference: every
     holder of a reference is a file descriptor, and a descriptor that names
     a file has given its [fd_slot] away (FdSlots.v).  That is what bounds
     the count, and hence what makes [f->ref++] safe.

     The [< 2^31] conjunct is the LOCAL PROJECTION of that bound -- it is
     what a consumer walking the table actually needs, and reaching for the
     authority at every slot would infect every consumer.  It is not an
     independent assumption: every operation that changes a count re-derives
     it from [fd_slots_no_overflow]. *)
  Definition fslot (γ : gname) (M : gmap nat (Qp * positive)) (k : nat) : iProp Σ :=
    match M !! k with
    | None =>
        (a_fref k ↦₄ (mword_of_int 0 : mword 32) ∗
         ∃ C, ⌜fc_type C = FD_NONE⌝ ∗ file_fields k 1 C ∗
              file_pay γ k 1 C)%I
    | Some (q, n) =>
        (⌜Z.pos n < 2 ^ 31⌝ ∗
         a_fref k ↦₄ (mword_of_int (Z.pos n) : mword 32) ∗
         file_rest γ k q ∗
         fd_slots (Pos.to_nat n))%I
    end.

  Definition ftable_res (γ : gname) : iProp Σ :=
    (∃ M : gmap nat (Qp * positive),
       ftable_auth γ M ∗
       (* the fd-slot supply: the table is where the conservation law is
          checked, because the table is what holds one unit per reference. *)
       fd_slots_auth ∗
       ⌜∀ k, is_Some (M !! k) -> (k < NFILE)%nat⌝ ∗
       [∗ list] k ∈ seq 0 NFILE, fslot γ M k)%I.

  (* the whole table: the spinlock named "ftable" over that resource.
     Persistent, so every core shares it. *)
  Definition is_ftable (γl γ : gname) : iProp Σ :=
    is_lock γl ftable_addr "ftable"%string (ftable_res γ).

  Global Instance is_ftable_persistent γl γ : Persistent (is_ftable γl γ).
  Proof. apply _. Qed.

  (* ------------------------------------------------------------------ *)
  (*  Content: agreement and the fractional split                         *)
  (* ------------------------------------------------------------------ *)

  (* Two fds onto the same file agree on its content -- for free, because a
     reference carries genuine points-to fractions.  No [agree] ghost. *)
  Lemma file_fields_agree k q1 C1 q2 C2 :
    file_fields k q1 C1 -∗ file_fields k q2 C2 -∗ ⌜C1 = C2⌝.
  Proof.
    rewrite /file_fields.
    iIntros "(Ht1 & Hr1 & Hw1 & Hp1 & Hi1 & Hm1)".
    iIntros "(Ht2 & Hr2 & Hw2 & Hp2 & Hi2 & Hm2)".
    iDestruct (word4_pointsto_agree with "Ht1 Ht2") as %E1.
    iDestruct (mem_pointsto_agree with "Hr1 Hr2") as %E2.
    iDestruct (mem_pointsto_agree with "Hw1 Hw2") as %E3.
    iDestruct (word_pointsto_agree with "Hp1 Hp2") as %E4.
    iDestruct (word_pointsto_agree with "Hi1 Hi2") as %E5.
    iDestruct (word2_pointsto_agree with "Hm1 Hm2") as %E7.
    iPureIntro. destruct C1, C2; cbn in *. congruence.
  Qed.

  (* THE FILE'S INODE, read out of a reference at ANY fraction.  This is the
     bridge the off-borrow invariant is opened with: the invariant holds the
     OTHER half of the same cell, so agreement identifies the two. *)
  Lemma file_fields_ip k q C :
    file_fields k q C -∗ a_fip k ↦₈{DfracOwn (q/2)} fc_ip C.
  Proof. iIntros "(_ & _ & _ & _ & $ & _)". Qed.

  Lemma file_ref_agree γ k q1 C1 q2 C2 :
    file_ref γ k q1 C1 -∗ file_ref γ k q2 C2 -∗ ⌜C1 = C2⌝.
  Proof.
    iIntros "(_ & H1 & _) (_ & H2 & _)".
    by iApply (file_fields_agree with "H1 H2").
  Qed.

  (* the split filedup performs and fileclose undoes. *)
  Lemma file_fields_frac_split k q1 q2 C :
    file_fields k (q1 + q2) C ⊣⊢ file_fields k q1 C ∗ file_fields k q2 C.
  Proof.
    rewrite /file_fields.
    rewrite (word4_pointsto_frac_split (a_ftype k)).
    rewrite (mem_pointsto_frac_split (a_freadable k)).
    rewrite (mem_pointsto_frac_split (a_fwritable k)).
    rewrite (word_pointsto_frac_split (a_fpipe k)).
    rewrite (word2_pointsto_frac_split (a_fmajor k)).
    (* the ip cell is at HALF, and halving distributes over the sum *)
    rewrite Qp.div_add_distr (word_pointsto_frac_split (a_fip k)).
    iSplit.
    - iIntros "([A1 B1] & [A2 B2] & [A3 B3] & [A4 B4] & [A5 B5] & [A6 B6])".
      iFrame.
    - iIntros "[(A1 & A2 & A3 & A4 & A5 & A6) (B1 & B2 & B3 & B4 & B5 & B6)]".
      iFrame.
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  Reaching into the table                                             *)
  (* ------------------------------------------------------------------ *)

  (* Borrow one slot out of the NFILE-way big-sep and put it back, possibly
     under a DIFFERENT authority map -- which is what filealloc needs: its
     scan borrows slot after slot unchanged (M' := M), and the slot it takes
     is given back at [<[i := (1,1)]> M].  Since [fslot γ M k] reads only
     [M !! k], every other slot is untouched by the update. *)
  Lemma ftable_slots_acc (γ : gname) (M : gmap nat (Qp * positive)) (i : nat) :
    (i < NFILE)%nat ->
    ([∗ list] k ∈ seq 0 NFILE, fslot γ M k) -∗
    fslot γ M i ∗
    (∀ M' : gmap nat (Qp * positive),
       ⌜∀ k, k ≠ i -> M' !! k = M !! k⌝ -∗ fslot γ M' i -∗
       [∗ list] k ∈ seq 0 NFILE, fslot γ M' k).
  Proof.
    iIntros (Hi) "H".
    assert (Hlk : seq 0 NFILE !! i = Some i).
    { apply lookup_seq. lia. }
    rewrite (big_sepL_delete (fun _ k => fslot γ M k) (seq 0 NFILE) i i Hlk).
    iDestruct "H" as "[$ Hrest]".
    iIntros (M' HM') "Hi".
    rewrite (big_sepL_delete (fun _ k => fslot γ M' k) (seq 0 NFILE) i i Hlk).
    iFrame "Hi".
    iApply (big_sepL_mono with "Hrest").
    intros idx y Hy. destruct (decide (idx = i)) as [->|Hne]; [done|].
    (* in [seq 0 NFILE] the element IS the index, so [y <> i] *)
    apply lookup_seq in Hy as [-> _].
    unfold fslot. rewrite (HM' _ Hne). done.
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  The algebra's two load-bearing validity facts                       *)
  (* ------------------------------------------------------------------ *)

  (* A reference's fragment against the authority.  The second conjunct is
     THE fact the whole design turns on: the holder of the ONLY reference
     holds the FULL fraction, hence write access -- which is what licenses
     sys_open's unlocked initialization and fileclose's [type = FD_NONE]. *)
  Lemma fref_tok_lookup γ M k q :
    ftable_auth γ M -∗ fref_tok γ k q -∗
    ⌜∃ qt n, M !! k = Some (qt, n) /\ (qt ≤ 1)%Qp /\
       (n = 1%positive -> q = qt) /\ (q = qt -> n = 1%positive) /\
       (n <> 1%positive -> (q < qt)%Qp)⌝.
  Proof.
    rewrite /ftable_auth /fref_tok. iIntros "[Ha _] Hf".
    iDestruct (fref_own_valid_2 with "Ha Hf")
      as %[Hincl Hval]%auth_both_valid_discrete.
    iPureIntro.
    apply singleton_included_l in Hincl as [y [Hy Hle]].
    apply leibniz_equiv in Hy. destruct y as [qt n]. exists qt, n.
    split; [exact Hy|].
    (* the authority's own validity bounds the OUTSTANDING total, which is
       what the [n >= 2] close needs before it may subtract from it. *)
    split.
    { specialize (Hval k). rewrite Hy in Hval.
      destruct Hval as [Hvq _]; simpl in Hvq. by apply frac_valid in Hvq. }
    apply Some_included in Hle as [Heq | Hlt].
    - (* the fragment IS the whole entry: same fraction, count 1 *)
      destruct Heq as [Hq Hn]; cbn in Hq, Hn.
      split; [by intros _|]. split; [by intros _; rewrite -Hn|].
      intros Hne. exfalso. apply Hne. by rewrite -Hn.
    - (* strictly included, so BOTH components strictly grow -- and the
         fraction one is what the [n >= 2] close needs to SUBTRACT. *)
      apply pair_included in Hlt as [Hq Hn]; cbn in Hq, Hn.
      apply frac_included in Hq. apply pos_included in Hn.
      split; [|split].
      + intros Hc. exfalso. rewrite Hc in Hn. lia.
      + intros Hc. exfalso. rewrite Hc in Hq. by apply (irreflexivity Qp.lt qt).
      + by intros _.
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  The liveness counter's four steps                                   *)
  (* ------------------------------------------------------------------ *)

  (* They mirror the reference count exactly -- the counter IS the count
     column of [M] -- so each one is the corresponding [file_*_step]'s local
     update with the fraction component dropped.  They are separate lemmas
     rather than inlined so that the reason the counter exists (the borrow
     protocol, FileOff.v) stays legible here. *)

  Lemma flive_alloc γ (m : gmap nat positive) k :
    m !! k = None ->
    flive_own γ (● m) ==∗
    flive_own γ (● (<[k := 1%positive]> m)) ∗ flive_tok γ k.
  Proof.
    intros Hm. iIntros "Ha". rewrite /flive_tok.
    iMod (flive_own_update _ _
            (● (<[k := 1%positive]> m) ⋅ ◯ {[k := 1%positive]}) with "Ha") as "H".
    { apply auth_update_alloc.
      apply (alloc_singleton_local_update _ k 1%positive); done. }
    rewrite flive_own_op. by iDestruct "H" as "[$ $]".
  Qed.

  Lemma flive_dup γ (m : gmap nat positive) k (n : positive) :
    m !! k = Some n ->
    flive_own γ (● m) -∗ flive_tok γ k ==∗
    flive_own γ (● (<[k := Pos.succ n]> m)) ∗ flive_tok γ k ∗ flive_tok γ k.
  Proof.
    intros Hm. iIntros "Ha Hf". rewrite /flive_tok.
    iMod (flive_own_update_2 _ _ _ (● (<[k := Pos.succ n]> m))
            (◯ {[k := 2%positive]}) with "Ha Hf") as "[$ Hfrag]".
    { apply auth_update.
      apply (singleton_local_update _ k n 1%positive (Pos.succ n) 2%positive Hm).
      apply local_update_discrete. intros mz Hv Hz.
      split; [done|].
      destruct mz as [nf|]; simpl in Hz |- *.
      - rewrite pos_op_add in Hz. rewrite pos_op_add. rewrite Hz.
        apply pos_succ_1_add.
      - by rewrite Hz. }
    assert (Hsp : ({[k := 2%positive]} : gmap nat positive)
                  = {[k := 1%positive]} ⋅ {[k := 1%positive]}).
    { rewrite singleton_op. reflexivity. }
    rewrite Hsp auth_frag_op flive_own_op.
    by iDestruct "Hfrag" as "[$ $]".
  Qed.

  Lemma flive_close γ (m : gmap nat positive) k (n : positive) :
    m !! k = Some (Pos.succ n) ->
    flive_own γ (● m) -∗ flive_tok γ k ==∗ flive_own γ (● (<[k := n]> m)).
  Proof.
    intros Hm. iIntros "Ha Hf". rewrite /flive_tok.
    iMod (flive_own_update_2' γ (● m) (◯ {[k := 1%positive]})
            (● (<[k := n]> m)) with "Ha Hf") as "$"; [|done].
    apply auth_update_dealloc, gmap_local_update. intros i.
    destruct (decide (i = k)) as [->|Hne]; last first.
    { assert (Hki : k <> i) by auto.
      pose proof (lookup_singleton_ne (M:=gmap nat) k i 1%positive Hki) as Hs.
      pose proof (lookup_insert_ne m k i n Hki) as Hmi.
      apply local_update_discrete. intros mz Hv Hz.
      rewrite Hs in Hz. rewrite Hmi. split; [exact Hv | exact Hz]. }
    pose proof (lookup_singleton (M:=gmap nat) k 1%positive) as Hs.
    pose proof (lookup_insert m k n) as Hmi.
    apply local_update_discrete. intros mz Hv Hz.
    rewrite Hm in Hz, Hv. rewrite Hs in Hz. rewrite Hmi.
    destruct mz as [[nf|]|]; simpl in Hz.
    - apply Some_equiv_inj in Hz. rewrite pos_op_add in Hz.
      assert (Hn' : Pos.succ n = (1 + nf)%positive) by exact Hz.
      assert (Hnf : nf = n) by lia. subst nf.
      split; [done | reflexivity].
    - exfalso. rewrite right_id in Hz. apply Some_equiv_inj in Hz.
      assert (Hn' : Pos.succ n = 1%positive) by exact Hz. lia.
    - exfalso. apply Some_equiv_inj in Hz.
      assert (Hn' : Pos.succ n = 1%positive) by exact Hz. lia.
  Qed.

  Lemma flive_close_last γ (m : gmap nat positive) k :
    m !! k = Some 1%positive ->
    flive_own γ (● m) -∗ flive_tok γ k ==∗ flive_own γ (● (delete k m)).
  Proof.
    intros Hm. iIntros "Ha Hf". rewrite /flive_tok.
    iMod (flive_own_update_2' γ (● m) (◯ {[k := 1%positive]})
            (● (delete k m)) with "Ha Hf") as "$"; [|done].
    apply auth_update_dealloc, gmap_local_update. intros i.
    destruct (decide (i = k)) as [->|Hne]; last first.
    { assert (Hki : k <> i) by auto.
      pose proof (lookup_singleton_ne (M:=gmap nat) k i 1%positive Hki) as Hs.
      pose proof (lookup_delete_ne m k i Hki) as Hmi.
      apply local_update_discrete. intros mz Hv Hz.
      rewrite Hs in Hz. rewrite Hmi. split; [exact Hv | exact Hz]. }
    pose proof (lookup_singleton (M:=gmap nat) k 1%positive) as Hs.
    pose proof (lookup_delete m k) as Hmi.
    apply local_update_discrete. intros mz Hv Hz.
    rewrite Hm in Hz. rewrite Hs in Hz. rewrite Hmi.
    destruct mz as [[nf|]|]; simpl in Hz.
    - exfalso. apply Some_equiv_inj in Hz. rewrite pos_op_add in Hz.
      assert (Hn' : 1%positive = (1 + nf)%positive) by exact Hz. lia.
    - split; done.
    - split; done.
  Qed.

  (* OBLIGATION (b), the ghost half: at the LAST reference the authority
     records ONE unit, so a second one -- the one a stale checked-out state
     would be parking -- cannot exist.  This is what lets the exclusive holder
     of a slot reclaim [f->off] holding NO inode lock. *)
  Lemma flive_excl_last γ (m : gmap nat positive) k :
    m !! k = Some 1%positive ->
    flive_own γ (● m) -∗ flive_tok γ k -∗ flive_tok γ k -∗ False.
  Proof.
    intros Hm. iIntros "Ha H1 H2". rewrite /flive_tok.
    iDestruct (flive_own_valid_2 γ (● m)
                 (◯ {[k := 1%positive]} ⋅ ◯ {[k := 1%positive]})
                 with "Ha [H1 H2]") as %Hv.
    { iApply flive_own_op. iFrame. }
    iPureIntro.
    rewrite -auth_frag_op singleton_op pos_op_add in Hv.
    apply auth_both_valid_discrete in Hv as [Hincl _].
    apply singleton_included_l in Hincl as [y [Hy Hle]].
    rewrite Hm in Hy. apply Some_equiv_inj in Hy.
    assert (Hy' : 1%positive = y) by exact Hy. subst y.
    apply Some_included in Hle as [Heq | Hlt].
    - assert (Hc : (1 + 1)%positive = 1%positive) by exact Heq. lia.
    - apply pos_included in Hlt. lia.
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  The three ghost steps, all performed under ftable.lock              *)
  (* ------------------------------------------------------------------ *)

  (* filealloc: [ref = 0] -> [ref = 1].  Allocate the authority entry at
     (1,1) and hand the invariant's WHOLE content fraction out as the
     exclusive reference. *)
  Lemma file_alloc_step γ M k C :
    M !! k = None ->
    ftable_auth γ M -∗ file_fields k 1 C -∗ file_pay γ k 1 C ==∗
    ftable_auth γ (<[k := (1%Qp, 1%positive)]> M) ∗ file_ref γ k 1 C.
  Proof.
    iIntros (HM) "[Ha Hl] Hf Hp".
    rewrite /ftable_auth /fref_tok.
    assert (Hml : Mcount M !! k = None)
      by (rewrite Mcount_lookup HM; reflexivity).
    iMod (flive_alloc γ (Mcount M) k Hml with "Hl") as "[Hl Hlv]".
    iMod (fref_own_update _ _
            (● (<[k := (1%Qp, 1%positive)]> M) ⋅ ◯ {[k := (1%Qp, 1%positive)]})
            with "Ha") as "H".
    { apply auth_update_alloc.
      apply (alloc_singleton_local_update _ k (1%Qp, 1%positive)); [done|].
      split; done. }
    rewrite fref_own_op. iDestruct "H" as "[Ha Hfrag]".
    rewrite Mcount_insert. cbn [snd].
    iModIntro. iFrame "Ha Hl". rewrite /file_ref /fref_tok. iFrame.
  Qed.

  (* filedup: [ref++].  The new reference's fraction comes out of the
     CALLER's -- nothing is conjured, which is exactly why the invariant's
     leftover [file_rest γ k qt] is untouched. *)
  Lemma file_dup_step γ M k q C qt (n : positive) :
    M !! k = Some (qt, n) ->
    ftable_auth γ M -∗ file_ref γ k q C ==∗
    ftable_auth γ (<[k := (qt, Pos.succ n)]> M) ∗
    file_ref γ k (q/2)%Qp C ∗ file_ref γ k (q/2)%Qp C.
  Proof.
    iIntros (HM) "[Ha Hl] (Hf & Hc & Hp & Hlv)".
    rewrite /ftable_auth /fref_tok.
    assert (Hml : Mcount M !! k = Some n)
      by (rewrite Mcount_lookup HM; reflexivity).
    iMod (flive_dup γ (Mcount M) k n Hml with "Hl Hlv") as "(Hl & Hlv1 & Hlv2)".
    rewrite Mcount_insert. cbn [snd].
    iMod (fref_own_update_2 _ _ _ (● (<[k := (qt, Pos.succ n)]> M))
            (◯ {[k := (q, 2%positive)]}) with "Ha Hf") as "[Ha Hfrag]".
    { apply auth_update.
      apply (singleton_local_update _ k (qt, n) (q, 1%positive)
                                      (qt, Pos.succ n) (q, 2%positive) HM).
      apply local_update_discrete. intros mz Hv Hz.
      destruct Hv as [Hvq Hvn]. split; [by split|].
      destruct mz as [[qf nf]|]; destruct Hz as [Hq Hn]; simpl in Hq, Hn.
      - split; simpl; [exact Hq|]. rewrite Hn !pos_op_add. apply pos_succ_1_add.
      - split; simpl; [exact Hq|]. by rewrite Hn. }
    iModIntro. iFrame "Ha Hl".
    (* split the fragment: (q/2,1) ⋅ (q/2,1) = (q,2) *)
    rewrite /file_ref /fref_tok.
    assert (Hsp : ({[k := (q, 2%positive)]} : gmap nat (Qp * positive))
                  = {[k := ((q/2)%Qp, 1%positive)]} ⋅ {[k := ((q/2)%Qp, 1%positive)]}).
    { rewrite singleton_op. f_equal. rewrite -pair_op.
      by rewrite frac_op Qp.div_2. }
    rewrite Hsp auth_frag_op fref_own_op.
    iDestruct "Hfrag" as "[Hfa Hfb]".
    (* and the content fraction, and the payload, likewise *)
    iEval (rewrite -{1}(Qp.div_2 q) file_fields_frac_split) in "Hc".
    iEval (rewrite -{1}(Qp.div_2 q) file_pay_split) in "Hp".
    iDestruct "Hc" as "[Hca Hcb]". iDestruct "Hp" as "[Hpa Hpb]".
    iFrame.
  Qed.

  (* fileclose, [--ref > 0]: the departing reference's fraction has to go
     SOMEWHERE, and it goes back into the authority's outstanding total (and,
     on the points-to side, into [file_rest]).  That is why the frac component
     tracks outstanding fraction rather than being pinned at 1. *)
  Lemma file_close_step γ M k q C qt (n : positive) (qr : Qp) :
    M !! k = Some (qt, Pos.succ n) ->
    (qt - q)%Qp = Some qr ->
    ftable_auth γ M -∗ file_ref γ k q C ==∗
    ftable_auth γ (<[k := (qr, n)]> M) ∗ file_fields k q C ∗
    file_pay γ k q C.
  Proof.
    iIntros (HM Hsub) "[Ha Hl] (Hf & Hc & Hp & Hlv)".
    rewrite /ftable_auth /fref_tok.
    assert (Hml : Mcount M !! k = Some (Pos.succ n))
      by (rewrite Mcount_lookup HM; reflexivity).
    iMod (flive_close γ (Mcount M) k n Hml with "Hl Hlv") as "Hl".
    rewrite Mcount_insert. cbn [snd].
    apply Qp.sub_Some in Hsub.       (* qt = q + qr *)
    iMod (fref_own_update_2' γ (● M) (◯ {[k := (q, 1%positive)]})
            (● (<[k := (qr, n)]> M)) with "Ha Hf") as "Ha"; last first.
    { iModIntro. iFrame. }
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
      (* qr ≤ qt ≤ 1 *)
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

  (* fileclose, [--ref == 0]: [fref_tok_lookup] forced [q = qt], so the closer
     holds every share that was ever handed out, and the slot leaves the
     authority.  The OUTSTANDING total [qt] is not 1 in general -- every
     earlier close returned its fraction to [file_rest] and shrank it -- so
     what the closer walks away with is [qt], and the rest of the slot is
     still in the invariant.  [file_rest_join] below is where they meet.

     Note the entry can be deleted at any [qt]: it is the COUNT component
     that is exclusive here, since [positiveR] has no unit, so no frame can
     sit beside a fragment recording the last reference. *)
  Lemma file_close_last_step γ M k C (qt : Qp) :
    M !! k = Some (qt, 1%positive) ->
    ftable_auth γ M -∗ file_ref γ k qt C ==∗
    ftable_auth γ (delete k M) ∗ file_fields k qt C ∗
    file_pay γ k qt C.
  Proof.
    iIntros (HM) "[Ha Hl] (Hf & Hc & Hp & Hlv)".
    rewrite /ftable_auth /fref_tok.
    assert (Hml : Mcount M !! k = Some 1%positive)
      by (rewrite Mcount_lookup HM; reflexivity).
    iMod (flive_close_last γ (Mcount M) k Hml with "Hl Hlv") as "Hl".
    rewrite Mcount_delete.
    iMod (fref_own_update_2' γ (● M) (◯ {[k := (qt, 1%positive)]})
            (● (delete k M)) with "Ha Hf") as "Ha"; last first.
    { iModIntro. iFrame. }
    apply auth_update_dealloc, gmap_local_update. intros i.
    destruct (decide (i = k)) as [->|Hne]; last first.
    { (* untouched slot: the fragment is absent on both sides *)
      assert (Hki : k <> i) by auto.
      pose proof (lookup_singleton_ne (M:=gmap nat) k i (qt, 1%positive) Hki) as Hs.
      pose proof (lookup_delete_ne M k i Hki) as Hm.
      apply local_update_discrete. intros mz Hv Hz.
      rewrite Hs in Hz. rewrite Hm. split; [exact Hv | exact Hz]. }
    pose proof (lookup_singleton (M:=gmap nat) k (qt, 1%positive)) as Hs.
    pose proof (lookup_delete M k) as Hm.
    apply local_update_discrete. intros mz Hv Hz.
    rewrite HM in Hz. rewrite Hs in Hz. rewrite Hm.
    destruct mz as [[[qf nf]|]|]; simpl in Hz.
    - (* a frame at this key would make the count 1 + nf, and it is 1 *)
      exfalso. apply Some_equiv_inj in Hz. destruct Hz as [_ Hn]; simpl in Hn.
      rewrite pos_op_add in Hn.
      assert (Hn' : 1%positive = (1 + nf)%positive) by exact Hn. lia.
    - split; done.
    - split; done.
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  [file_rest]: the fraction the invariant still holds                 *)
  (* ------------------------------------------------------------------ *)

  (* THE LAST CLOSER'S JOIN.  Its own share plus whatever the invariant kept
     is the whole slot -- content cells, payload names and payload alike.
     This is what puts a WHOLE pipe end in fileclose's hands, and hence what
     licenses [pipeclose(ff.pipe, ff.writable)]. *)
  Lemma file_rest_join γ k (qt : Qp) C :
    (qt ≤ 1)%Qp ->
    file_fields k qt C -∗ file_pay γ k qt C -∗ file_rest γ k qt -∗
    file_fields k 1 C ∗ file_pay γ k 1 C.
  Proof.
    intros Hle. rewrite /file_rest.
    destruct (1 - qt)%Qp as [q'|] eqn:Et.
    - apply Qp.sub_Some in Et.        (* 1 = qt + q' *)
      iIntros "Hf Hp (%C' & Hf' & Hp')".
      iDestruct (file_fields_agree with "Hf Hf'") as %<-.
      rewrite Et file_fields_frac_split file_pay_split. iFrame.
    - (* nothing left over: [qt] is already the whole of it *)
      apply Qp.sub_None in Et.
      assert (qt = 1%Qp) as -> by (apply (anti_symm (⊑@{Qp})); done).
      iIntros "$ $ _". done.
  Qed.

  (* ... and the DEPARTING reference's, when it is not the last: its fraction
     goes back into the leftover, which is why [fileUR]'s frac component
     tracks OUTSTANDING fraction rather than being pinned at 1. *)
  Lemma file_rest_absorb γ k (qt q qr : Qp) C :
    (qt - q)%Qp = Some qr -> (qt ≤ 1)%Qp ->
    file_rest γ k qt -∗ file_fields k q C -∗ file_pay γ k q C -∗
    file_rest γ k qr.
  Proof.
    intros Hsub Hle. apply Qp.sub_Some in Hsub.   (* qt = q + qr *)
    rewrite /file_rest.
    destruct (1 - qt)%Qp as [s|] eqn:Et.
    - apply Qp.sub_Some in Et.                     (* 1 = qt + s *)
      assert (Hr : (1 - qr)%Qp = Some (q + s)%Qp).
      { apply Qp.sub_Some. rewrite Et Hsub.
        by rewrite (Qp.add_comm q qr) -Qp.add_assoc. }
      rewrite Hr.
      iIntros "(%C' & Hf' & Hp') Hf Hp".
      iDestruct (file_fields_agree with "Hf Hf'") as %<-.
      iExists C. rewrite file_fields_frac_split file_pay_split. iFrame.
    - apply Qp.sub_None in Et.
      assert (qt = 1%Qp) as Hqt by (apply (anti_symm (⊑@{Qp})); done).
      assert (Hr : (1 - qr)%Qp = Some q).
      { apply Qp.sub_Some. rewrite -Hqt Hsub. apply Qp.add_comm. }
      rewrite Hr. iIntros "_ Hf Hp". iExists C. iFrame.
  Qed.

End FileInv.

(* ------------------------------------------------------------------ *)
(*  Boot: minting the table's ghost                                     *)
(* ------------------------------------------------------------------ *)

(* The authority starts empty -- every slot free -- and every slot's names
   ghost exists from the start, held at fraction 1 by the free-slot arm of
   [fslot] exactly as its content cells are.  Nothing is ever allocated or
   freed per slot afterwards: a slot's names are simply OVERWRITTEN by
   whoever holds it exclusively ([fpay_tok_update]), which is what lets
   pipealloc publish a payload with no lock in hand.

   Nothing calls this yet -- the ftable lock is not wired at boot (fileinit
   is proven, but [ftable_res] is still a premise everywhere).  It is here
   because a resource nobody can MINT is a design hole that only surfaces
   when the wiring is written. *)
Definition fpay_v0 : prodR fracR (agreeR (leibnizO fpnames)) :=
  (1%Qp, to_agree (inhabitant : leibnizO fpnames)).

Fixpoint fpay_map0 (n : nat) : fpayUR :=
  match n with
  | O => ∅
  | S k => <[k := fpay_v0]> (fpay_map0 k)
  end.

Lemma fpay_map0_none (n i : nat) : (n <= i)%nat -> fpay_map0 n !! i = None.
Proof.
  revert i. induction n as [|n IH]; intros i Hi; [done|].
  cbn [fpay_map0]. rewrite lookup_insert_ne; [apply IH; lia | lia].
Qed.

Lemma fpay_map0_valid (n : nat) : ✓ (fpay_map0 n).
Proof.
  induction n as [|n IH];
    [cbn [fpay_map0]; intros i; rewrite lookup_empty; done|].
  cbn [fpay_map0]. apply insert_valid; [|exact IH].
  split; done.
Qed.

Section FileGhostAlloc.
  Context `{!riscvGS Σ, !lockG Σ, !fileG Σ, !fdslotG Σ}.

  Lemma fpay_map0_split (γ : gname) (n : nat) :
    own γ ((ε, (fpay_map0 n, ε)) : fileUR) ⊢
    [∗ list] k ∈ seq 0 n, own γ ((ε, ({[ k := fpay_v0 ]}, ε)) : fileUR).
  Proof.
    induction n as [|n IH]; [by iIntros "_"|].
    rewrite seq_S big_sepL_app. iIntros "H". cbn [fpay_map0].
    rewrite (insert_singleton_op (fpay_map0 n) n fpay_v0);
      [|apply fpay_map0_none; lia].
    assert (Hsp : ((ε, ({[n := fpay_v0]} ⋅ fpay_map0 n, ε)) : fileUR)
                  ≡ ((ε, ({[n := fpay_v0]}, ε)) : fileUR)
                    ⋅ ((ε, (fpay_map0 n, ε)) : fileUR)).
    { rewrite -!pair_op !left_id. reflexivity. }
    rewrite Hsp own_op. iDestruct "H" as "[Hk Hm]".
    iSplitL "Hm"; [by iApply IH | by iFrame].
  Qed.

  Lemma ftable_ghosts_alloc :
    ⊢ |==> ∃ γ, ftable_auth γ ∅ ∗
                [∗ list] k ∈ seq 0 NFILE, ∃ pn, fpay_tok γ k 1 pn.
  Proof.
    iMod (own_alloc (((● (∅ : gmap nat (Qp * positive))),
                      (fpay_map0 NFILE, ● (∅ : gmap nat positive)))
                     : fileUR)) as (γ) "H".
    { split; cbn [fst snd].
      - apply auth_auth_valid. intros i. rewrite lookup_empty. done.
      - split; cbn [fst snd].
        + apply fpay_map0_valid.
        + apply auth_auth_valid. intros i. rewrite lookup_empty. done. }
    iModIntro. iExists γ.
    assert (Hsp : ((● (∅ : gmap nat (Qp * positive)),
                    (fpay_map0 NFILE, ● (∅ : gmap nat positive))) : fileUR)
                  ≡ ((● (∅ : gmap nat (Qp * positive)),
                      (ε, ● (∅ : gmap nat positive))) : fileUR)
                    ⋅ ((ε, (fpay_map0 NFILE, ε)) : fileUR)).
    { rewrite -!pair_op !right_id !left_id. reflexivity. }
    rewrite Hsp own_op. iDestruct "H" as "[Ha Hm]".
    iSplitL "Ha".
    { rewrite /ftable_auth /fref_own /flive_own /Mcount fmap_empty.
      rewrite -own_op.
      assert (He : (((● (∅ : gmap nat (Qp * positive)), ε) : fileUR)
                    ⋅ (ε, (ε, ● (∅ : gmap nat positive))))
                   ≡ ((● (∅ : gmap nat (Qp * positive)),
                       (ε, ● (∅ : gmap nat positive))) : fileUR)).
      { rewrite -!pair_op !left_id !right_id. reflexivity. }
      rewrite He. iExact "Ha". }
    iDestruct (fpay_map0_split with "Hm") as "Hm".
    iApply (big_sepL_mono with "Hm"). intros ? k ?. iIntros "H".
    iExists inhabitant. iExact "H".
  Qed.

End FileGhostAlloc.
