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
(* for [T_DIR_z] alone -- [inode_pay]'s witness says "not a directory", and
   the number is stated once, where [IcacheEscrow.ic_loaded]'s [dir_ok]
   states it (design fs-icache.md §17.6 (5)). *)
Require Import DirView.
(* for [MAXFILE] and [BSIZE] alone -- [off_wf], the bound the off cell carries,
   is stated over the inode layer's two constants, and the cell now lives here
   (R-open-1b).  Neither file mentions the file table, so this closes no cycle. *)
Require Import InodeInv.
Require Import FsCrash.
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
   for: per-slot constants agreed across every holder by [fpay_tok].

   [fp_ig] IS THE INODE SLOT'S LIVENESS GENERATION (design fs-icache.md
   §17.6 (5), ratified §17.7), and it is [fp_iq]'s exact status: a per-slot
   CONSTANT fixed when the file is published.  It is what the fd's type
   witness is keyed on -- [inode_pay] carries [IcacheRef.ity_shot fp_ig ty]
   with "[ty] is not a directory if this fd is writable", and filewrite joins
   it to ilock's copy with [IcacheRef.ity_shot_agree].  It can be a constant
   because a live reference PINS the generation: a bump needs the slot's
   whole liveness unit, which does not exist while any share is outstanding
   ([IcacheInv.live_slot_alloc] at the recycle, [IcacheInv.live_slot_regen]
   at iput's REF-1 free window -- and this fd's share refutes both).

   [fp_ocv] IS THE OFF-BORROW CINV'S NAME, and it is [fp_icv]'s exact status
   one field over (R-open-1b).  [off] is not a content field -- it is mutable
   under ip->lock by a holder of an arbitrarily small fraction -- so its cell
   lives in a per-slot invariant that is BORROWED across the instructions that
   use it ([FileOff.v]).  That invariant cannot be permanent: sys_open is the
   table's first WRITER of [f->ip] and [f->off], and an exclusive holder
   outside ftable.lock has no credential that refutes a stale checked-out
   state.  So it is CANCELLABLE, minted by whoever publishes a payload
   (sys_open, pipealloc) and cancelled by whoever retires one (fileclose's
   last-reference arm), and it exists exactly while the slot is TYPED -- the
   same lifetime [inode_pay]'s cinv already has.  A borrower opens it with
   [cinv_own] at its own fraction, which is why the token rides [file_payload]
   proportionally ([off_hold]).  See [off_hold] for why it is UNARMED until
   the slot is typed. *)
Record fpnames := MkFPNames
  { fp_lock : gname; fp_pipe : pipe_names; fp_icv : gname; fp_iq : Qp;
    fp_ig : gname; fp_ocv : gname }.

Global Instance fpnames_inhabited : Inhabited fpnames :=
  populate (MkFPNames 1%positive
              (MkPipeNames 1%positive 1%positive 1%positive 1%positive)
              1%positive 1%Qp 1%positive 1%positive).

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

(* ------------------------------------------------------------------ *)
(*  [off]: the namespace and the value bound                           *)
(* ------------------------------------------------------------------ *)

(* one namespace, one cancellable invariant per slot *)
Definition offN : namespace := nroot .@ "fileoff".

(* THE VALUE BOUND.  An offset never exceeds MAXFILE*BSIZE, and this is not
   decoration: readi's contract demands [off + n < 2^31] and NOTHING IN MEMORY
   bounds a freshly loaded [off], so without a bound in the invariant fileread
   cannot call readi at all.  The bound is inductive: the BSS starts zeroed,
   sys_open writes 0, and every advance is [off + r] with [r] clamped by
   readi/writei to the file's size, which is itself bounded by MAXFILE*BSIZE.
   A pipe or device file never writes the cell. *)
Definition off_wf (v : mword 32) : Prop :=
  bv_unsigned v <= Z.of_nat MAXFILE * Z.of_nat BSIZE.

Lemma off_wf_zero : off_wf (mword_of_int 0 : mword 32).
Proof.
  rewrite /off_wf.
  assert (Hz : bv_unsigned (mword_of_int 0 : mword 32) = 0) by reflexivity.
  rewrite Hz. unfold MAXFILE, BSIZE. lia.
Qed.

(* an offset in range is BELOW int range, which is what makes the [lw] that
   loads it read the literal (and readi's [off + n < 2^31] premise
   dischargeable from a bound on [n] alone). *)
Lemma off_wf_lt31 (v : mword 32) : off_wf v -> bv_unsigned v < 2 ^ 31.
Proof.
  rewrite /off_wf. unfold MAXFILE, BSIZE. intro H.
  assert (E : (2 ^ 31 = 2147483648)%Z) by (vm_compute; reflexivity).
  rewrite E. lia.
Qed.

(* Timelessness of the word points-to the off invariant puts in its body --
   typeclass search does not unfold a [Definition] on its own, exactly as
   [RiscvPtsto.word4_pointsto_timeless]'s comment says. *)
Global Instance word_pointsto_timeless' `{!riscvGS Σ} (ktr : CurKtier) (a : Arch.pa) (dq : dfrac)
    (w : bv 64) : Timeless (word_pointsto (KTR := ktr) a dq w).
Proof. rewrite /word_pointsto. apply _. Qed.

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

  (* THE FOURTH CONJUNCT: THE FD'S TYPE WITNESS (design fs-icache.md §17.6
     (5), ratified §17.7).  filewrite's FD_INODE arm must rebuild
     [IcacheEscrow.ic_loaded], whose [DirView.dir_ok] constrains a
     DIRECTORY's data bytes -- and an arbitrary user write into a directory
     breaks it.  The real xv6 invariant is five frames up: sys_open refuses
     writable directory fds.  This is where it crosses.

     The travelling share is therefore GENERATION-NAMED, and the witness is
     that generation's one-shot: ilock's postcondition hands filewrite
     [ity_shot g (di_type dn)] at the caller's [g], this payload holds
     [ity_shot g ty] with [ty <> T_DIR], [IcacheRef.ity_shot_agree] joins
     them, and [DirView.dir_ok_not_dir] finishes.  A generation sees at most
     one fill (§17.6), which is what makes the agreement mean something.

     CONDITIONAL ON [wr], NOT UNCONDITIONAL: an O_RDONLY directory fd is
     legal and fileread never needs the fact.  [wr] is [fc_wbool C] at the
     call site in [file_payload], and FD_DEVICE selects this payload too but
     never reaches writei.

     Everything here is PERSISTENT except the cinv token and the share, so
     [inode_pay_split]'s distributivity is untouched. *)
  Definition inode_pay (γx : gname) (Q : Qp) (g : gname) (v : mword 64)
      (wr : bool) (q : Qp) : iProp Σ :=
    (cinv fileipN γx (inode_held_short v Q) ∗ cinv_own γx q ∗
     inode_shr_held_gen v (q * Q)%Qp g ∗
     ∃ ty : bv 16, ity_shot g ty ∗ ⌜wr = true -> bv_unsigned ty <> T_DIR_z⌝)%I.

  Lemma inode_pay_split γx Q g v wr q1 q2 :
    inode_pay γx Q g v wr (q1 + q2) ⊣⊢
    inode_pay γx Q g v wr q1 ∗ inode_pay γx Q g v wr q2.
  Proof.
    rewrite /inode_pay cinv_own_fractional Qp.mul_add_distr_r
            inode_shr_held_gen_split.
    iSplit.
    - iIntros "(#Hi & [H1 H2] & [S1 S2] & #Hw)". iFrame "Hi H1 H2 S1 S2 Hw".
    - iIntros "[(#Hi & H1 & S1 & #Hw) (_ & H2 & S2 & _)]".
      iFrame "Hi H1 H2 S1 S2 Hw".
  Qed.

  (* THE LAST CLOSER'S MOVE, packaged: fraction one is the whole reference.
     A fupd, and the only one the file layer performs.  The gather is what
     makes it a WHOLE one -- the cinv gives back the parent short by [Q] and
     the closer's own arm is [1 * Q], the exact complement. *)
  Lemma inode_pay_cancel (E : coPset) (γx : gname) (Q : Qp) (g : gname)
      (v : mword 64) (wr : bool) :
    ↑fileipN ⊆ E -> inode_pay γx Q g v wr 1 ={E}=∗ inode_held v.
  Proof.
    iIntros (HE) "(#Hi & Hown & Hs & _)".
    iMod (cinv_cancel with "Hi Hown") as "H"; [exact HE|].
    iMod "H". iModIntro. rewrite Qp.mul_1_l.
    iDestruct (inode_shr_held_gen_forget with "Hs") as "Hs".
    iApply (inode_held_gather with "H Hs").
  Qed.

  (* the travelling share names SOME generation -- the one every slice of
     this slot names, since [iliveUR]'s agree is per-KEY ([IcacheRef.
     live_gen_agree]).  A publisher learns it by shedding, which is why
     [inode_pay_alloc] below takes the pieces rather than the whole
     reference: the type witness sys_open must supply is keyed on a gname it
     cannot name until the shed has happened. *)
  Local Lemma inode_shr_held_gen_intro (v : mword 64) (s : Qp) :
    inode_shr_held v s -∗ ∃ g : gname, inode_shr_held_gen v s g.
  Proof.
    rewrite /inode_shr_held /inode_shr_held_gen.
    iIntros "(%k & %inum & %Hv & %Hk & %Hb & Hs)".
    rewrite inode_shr_gen_intro. iDestruct "Hs" as (g) "Hs".
    iExists g, k, inum. by iFrame.
  Qed.

  Lemma inode_held_shed_gen (v : mword 64) :
    inode_held v -∗ ∃ (s : Qp) (g : gname),
      inode_held_short v s ∗ inode_shr_held_gen v s g.
  Proof.
    iIntros "H".
    iDestruct (inode_held_shed with "H") as (s) "[Hsh Hs]".
    iDestruct (inode_shr_held_gen_intro with "Hs") as (g) "Hs".
    iExists s, g. iFrame.
  Qed.

  (* ...and the inverse of the cancel, for whoever PUBLISHES an FD_INODE file
     (sys_open): a shed inode reference plus a TYPE WITNESS becomes a payload
     at fraction one.  The [Q] and the [g] the caller ends up recording in
     [fpnames] are the shed's outputs, which is why they are parameters here
     rather than existentials: sys_open runs [inode_held_shed_gen] first,
     reads [g] off it, discharges the witness against ilock's postcondition
     (T_FILE by construction on the O_CREATE path; O_RDONLY forced on a
     T_DIR inode on the open-existing one), and only then installs the
     names. *)
  Lemma inode_pay_alloc (E : coPset) (v : mword 64) (Q : Qp) (g : gname)
      (wr : bool) (ty : bv 16) :
    (wr = true -> bv_unsigned ty <> T_DIR_z) ->
    inode_held_short v Q -∗ inode_shr_held_gen v Q g -∗ ity_shot g ty
    ={E}=∗ ∃ γx : gname, inode_pay γx Q g v wr 1.
  Proof.
    iIntros (Hwr) "Hsh Hs #Hty".
    iMod (cinv_alloc E fileipN (inode_held_short v Q) with "[Hsh]")
      as (γx) "[#Hi Hown]".
    { by iNext. }
    iModIntro. iExists γx. rewrite /inode_pay Qp.mul_1_l.
    iFrame "Hi Hown Hs". iExists ty. iFrame "Hty". iPureIntro. exact Hwr.
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

  (* ------------------------------------------------------------------ *)
  (*  [off]: the per-slot CANCELLABLE borrow invariant                    *)
  (* ------------------------------------------------------------------ *)

  (* ---- full ownership of a word is EXCLUSIVE ----
     [mem_pointsto_ne] at one address is a contradiction; that is all this
     is, and it is what refutes a stale marker / a stale resident cell. *)
  Lemma word4_pointsto_excl (a : Arch.pa) (dq : dfrac) (w1 w2 : bv 32) :
    a ↦₄ w1 -∗ a ↦₄{dq} w2 -∗ False.
  Proof.
    iIntros "H1 H2".
    rewrite !word4_pointsto_unfold.
    iDestruct "H1" as "[_ H1]". iDestruct "H2" as "[_ H2]".
    change (seq 0 4) with ([0; 1; 2; 3]%nat).
    iDestruct "H1" as "[Hb1 _]". iDestruct "H2" as "[Hb2 _]".
    iDestruct (mem_pointsto_ne with "Hb1 Hb2") as %Hne.
    iPureIntro. exact (Hne eq_refl).
  Qed.

  Definition off_resident (k : nat) : iProp Σ :=
    (∃ v : mword 32, a_foff k ↦₄ v ∗ ⌜off_wf v⌝)%I.

  (* the borrower's marker: the inode's [valid] flag, which ilock hands out
     at 1 and which no fs.c callee below ilock touches.  It is EXCLUSIVE, it
     is keyed by the INODE'S ADDRESS (unlike a ghost-named token, which a
     second borrower has no way to match) and it is CLOSED -- the value is
     pinned at 1 -- so what a borrower takes back on return is provably what
     it parked.  See FileOff.v's header for the full argument. *)
  Definition off_mark (ip : mword 64) : iProp Σ :=
    (i_valid ip ↦₄ (mword_of_int 1 : mword 32))%I.

  (* THE BODY.  It holds, for the life of the invariant, HALF OF THE [f->ip]
     CELL -- which is how it knows WHICH INODE governs this slot's offset, and
     hence how two borrowers of one slot exclude each other (both would have
     to hold that inode's lock).  [file_fields] holds the other half, at half
     the nominal fraction, for exactly this reason. *)
  Definition off_body (γ : gname) (k : nat) : iProp Σ :=
    (∃ ip : mword 64,
       a_fip k ↦₈{DfracOwn (1/2)%Qp} ip ∗
       (off_resident k ∨ (off_mark ip ∗ flive_tok γ k)))%I.

  (* Proven STRUCTURALLY, one connective at a time, not by a single
     [apply _] over the whole unfolded body.  The monolithic search
     backtracks across the ∃/∗/∨ tower and the two points-to abstractions
     underneath it: 12.7 s for a fact whose every leaf instance already
     exists.  (The general rule is in claude-notes/optimization.md.) *)
  Global Instance off_body_timeless γ k : Timeless (off_body γ k).
  Proof.
    rewrite /off_body /off_resident /off_mark.
    apply bi.exist_timeless; intro ip.
    apply bi.sep_timeless; [apply _ |].
    apply bi.or_timeless.
    - apply bi.exist_timeless; intro v.
      apply bi.sep_timeless; [apply _ | apply _].
    - apply bi.sep_timeless; [apply _ | apply _].
  Qed.

  (* THE TWO CELLS, PLAIN -- what the publisher writes and what the last
     closer puts back.  [off_body]'s resident disjunct IS this. *)
  Definition off_raw (k : nat) : iProp Σ :=
    (∃ (ip : mword 64) (v : mword 32),
       a_fip k ↦₈{DfracOwn (1/2)%Qp} ip ∗ a_foff k ↦₄ v ∗ ⌜off_wf v⌝)%I.

  Lemma off_raw_body (γ : gname) (k : nat) : off_raw k -∗ off_body γ k.
  Proof.
    iIntros "(%ip & %v & Hip & Hc & %Hwf)".
    iExists ip. iFrame "Hip". iLeft. iExists v. iFrame. done.
  Qed.

  Global Instance off_raw_timeless k : Timeless (off_raw k).
  Proof.
    rewrite /off_raw.
    apply bi.exist_timeless; intro ip.
    apply bi.exist_timeless; intro v.
    apply bi.sep_timeless; [apply _ |].
    apply bi.sep_timeless; [apply _ | apply _].
  Qed.

  (* ---- ARMED AND UNARMED, AND WHY BOTH ----

     The cells cannot ride a reference as points-to fractions (they do not
     split, and [file_payload_split] is a ⊣⊢ at every arm), and they cannot
     live in a PERMANENT invariant either: sys_open is the table's first
     WRITER of [f->ip] and [f->off], it holds the exclusive reference with
     ftable.lock RELEASED, and nothing it can hold refutes a stale
     checked-out disjunct ([flive_tok] is fraction-free but composes; any
     fractional witness comes back existentially quantified, which is not
     what its depositor needs -- the thirteenth stop, fs-sysfile.md).

     A CANCELLABLE invariant answers both, exactly as [inode_pay]'s does one
     field over -- the assertion is persistent so it rides every share, and
     the FRACTION is the cancel.  What makes the publisher's write work is
     that the invariant is UNARMED while the slot is untyped: its body is
     then the two cells with NO disjunction, so [cinv_cancel] at fraction one
     hands them over outright and there is nothing to refute.  The publisher
     writes them, mints an ARMED one -- whose body carries the borrow
     protocol's resident/checked-out disjunction -- and records its name in
     [fpnames] with the SAME [fpay_tok_update] that installs the payload's.
     [fileclose]'s last-reference arm cancels whichever it finds (with the
     authority, inside the lock, which is what refutes the checked-out arm)
     and mints an unarmed one for the free slot it puts back.

     So a slot carries an off-cinv for its whole referenced life, ARMED
     exactly while it is typed -- and neither [FileInvDefs.fslot],
     [SpecFilealloc]'s post nor [SpecFileclose]'s environment moves.  The
     name is per-slot and changes on every publication, which is why no fixed
     persistent FAMILY of off-invariants can exist and no environment carries
     one. *)
  Definition off_content (γ : gname) (k : nat) (armed : bool) : iProp Σ :=
    (if armed then off_body γ k else off_raw k)%I.

  Global Instance off_content_timeless γ k armed : Timeless (off_content γ k armed).
  Proof. rewrite /off_content. destruct armed; apply _. Qed.

  Definition off_hold (γ : gname) (k : nat) (γx : gname) (armed : bool)
      (q : Qp) : iProp Σ :=
    (cinv (offN .@ k) γx (off_content γ k armed) ∗ cinv_own γx q)%I.

  Lemma off_hold_split γ k γx armed q1 q2 :
    off_hold γ k γx armed (q1 + q2) ⊣⊢
    off_hold γ k γx armed q1 ∗ off_hold γ k γx armed q2.
  Proof.
    rewrite /off_hold cinv_own_fractional. iSplit.
    - iIntros "(#Hi & H1 & H2)". iFrame "Hi H1 H2".
    - iIntros "[(#Hi & H1) (_ & H2)]". iFrame "Hi H1 H2".
  Qed.

  (* THE MINT, one lemma for both arms: an armed body's resident disjunct is
     the raw cells ([off_raw_body]). *)
  Lemma off_hold_alloc (E : coPset) (γ : gname) (k : nat) (armed : bool) :
    off_raw k ={E}=∗ ∃ γx : gname, off_hold γ k γx armed 1.
  Proof.
    iIntros "Hraw". rewrite /off_hold.
    iMod (cinv_alloc E (offN .@ k) (off_content γ k armed) with "[Hraw]")
      as (γx) "[#Hi Hown]".
    { iNext. rewrite /off_content. destruct armed; [| iExact "Hraw"].
      by iApply off_raw_body. }
    iModIntro. iExists γx. iFrame "Hi Hown".
  Qed.

  (* THE UNARMED CANCEL: no disjunction, hence no credential beyond the
     token.  THIS IS WHAT LETS sys_open AND pipealloc WRITE [f->ip] AND
     [f->off] WITH NO LOCK HELD -- blocker 1's whole answer. *)
  Lemma off_hold_cancel_raw (E : coPset) (γ : gname) (k : nat) (γx : gname) :
    ↑(offN .@ k) ⊆ E -> off_hold γ k γx false 1 ={E}=∗ ▷ off_raw k.
  Proof.
    iIntros (HE) "[#Hi Hown]".
    iMod (cinv_cancel with "Hi Hown") as "H"; [exact HE|].
    iModIntro. iExact "H".
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
     before releasing, and the BSS starts zeroed.

     THE OFF-BORROW CINV RIDES THE TYPED ARMS (R-open-1b).  A slot with no
     payload has no off-borrow invariant either: the two are created and
     cancelled by the same parties at the same moments, so the cinv exists
     exactly while the slot is typed, and a FREE slot's two cells live in
     [fslot]'s free arm instead.  That is also why the assertion cannot sit
     beside the payload rather than inside it -- [file_payload_split] is a
     ⊣⊢ at every arm and two full points-tos do not split, while
     [cinv]/[cinv_own] do. *)
  Definition file_core (q : Qp) (pn : fpnames) (C : fcontent) : iProp Σ :=
    (if bool_decide (fc_type C = FD_PIPE)
     then is_pipe (fp_lock pn) (fp_pipe pn) (fc_pipe C) ∗
          pipe_ref (fp_pipe pn) (fc_wbool C) q
     else if bool_decide (fc_type C = FD_INODE) || bool_decide (fc_type C = FD_DEVICE)
     then inode_pay (fp_icv pn) (fp_iq pn) (fp_ig pn) (fc_ip C) (fc_wbool C) q
     else emp)%I.

  Lemma file_core_split q1 q2 pn C :
    file_core (q1 + q2) pn C ⊣⊢ file_core q1 pn C ∗ file_core q2 pn C.
  Proof.
    rewrite /file_core.
    case_bool_decide as Hp; [|case_match].
    - rewrite pipe_ref_split. iSplit.
      + iIntros "(#Hi & H1 & H2)". iSplitL "H1"; (iSplitR; [iExact "Hi"|iFrame]).
      + iIntros "[[#Hi H1] [_ H2]]". iSplitR; [iExact "Hi"|]. iFrame.
    - apply inode_pay_split.
    - by rewrite left_id.
  Qed.

  (* THE CINV IS ARMED EXACTLY ON THE TWO TYPES THAT BORROW [off].  Only
     fileread's and filewrite's FD_INODE / FD_DEVICE arms ever touch the
     cell; a pipe's [off] is dead memory, so an FD_PIPE file keeps the
     UNARMED cinv it was allocated with and pipealloc has no ghost step to
     perform.  One predicate rather than a case analysis, because fileclose's
     last-reference arm has to retire the cinv long before the type is
     tested. *)
  Definition file_armed (C : fcontent) : bool :=
    (bool_decide (fc_type C = FD_INODE) || bool_decide (fc_type C = FD_DEVICE))%bool.

  Lemma file_armed_none C : fc_type C = FD_NONE -> file_armed C = false.
  Proof. intro Ht. rewrite /file_armed Ht. by vm_compute. Qed.

  Lemma file_armed_pipe C : fc_type C = FD_PIPE -> file_armed C = false.
  Proof. intro Ht. rewrite /file_armed Ht. by vm_compute. Qed.

  Definition file_payload (γ : gname) (k : nat) (q : Qp) (pn : fpnames)
      (C : fcontent) : iProp Σ :=
    (file_core q pn C ∗ off_hold γ k (fp_ocv pn) (file_armed C) q)%I.

  Lemma file_payload_split γ k q1 q2 pn C :
    file_payload γ k (q1 + q2) pn C ⊣⊢
    file_payload γ k q1 pn C ∗ file_payload γ k q2 pn C.
  Proof.
    rewrite /file_payload file_core_split off_hold_split. iSplit.
    - iIntros "[[H1 H2] [O1 O2]]". iFrame.
    - iIntros "[[H1 O1] [H2 O2]]". iFrame.
  Qed.

  (* the payload with its names quantified -- the form a reference carries,
     since nothing outside the file layer names a pipe's ghosts.  It still
     JOINS, because the names ghost makes the two shares agree. *)
  Definition file_pay (γ : gname) (k : nat) (q : Qp) (C : fcontent) : iProp Σ :=
    (∃ pn, fpay_tok γ k q pn ∗ file_payload γ k q pn C)%I.

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
