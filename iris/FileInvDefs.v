(* FileInvDefs.v -- the open-file table's geometry, the reference-count
   algebra, and [file_ref]/[fslot]: what every consumer that merely HOLDS or
   LOOKS UP a file reference needs (starting with [ProcInv]'s [proc_priv],
   which threads a slot index through [p->ofile]).

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
   * [off] is mutable under ip->lock; see the "off" note at the bottom of
     FileInv.v.

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
   holds a WHOLE pipe end to hand to pipeclose) -- both in FileInv.v.

   ---- why this is its own file ----

   FileInv.v keeps [ftable_res]/[is_ftable] and the ~500 lines of ref-counting
   ghost-step lemmas ([file_alloc_step], [flive_*], [file_close_step], ...)
   that only filealloc/filedup/fileclose/sys_open/sys_pipe/sys_fork/kexit need
   to CHANGE a reference count.  [ProcInv] and everything downstream of it on
   the pipe-read critical path ([SchedCtx], [SpecPiperead], [ProofPiperead])
   only ever HOLD a [file_ref]/[fslot] -- they never allocate or close one --
   so splitting this slice out lets FileInv.v's heavier tail compile IN
   PARALLEL with [ProcInv]/[SchedCtx]/[SpecPiperead]/[ProofPiperead] instead
   of sitting as a serial prerequisite of all of them.  `Require Import
   FileInv` still gets everything (FileInv.v `Require Export`s this file);
   switch to `Require Import FileInvDefs` wherever only this slice is needed.
   See claude-notes/optimization.md. *)
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
Require Import PipeInvDefs.
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
End FileInv.
