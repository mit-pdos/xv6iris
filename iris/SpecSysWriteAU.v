(* SpecSysWriteAU.v -- sys_write's ATOMIC-UPDATE contract, stated over the
   campaign's abstract state.  A STATEMENT FILE: definitions, structural
   lemmas, and a [Module Type] seal -- no walk, no proof against the
   machine.

   Design of record: claude-notes/design/fs-syscall-specs.md sections 0-5
   (v3; the sys_write paragraph of section 4 is this file's brief) and
   section 7's write row; lane W of
   claude-notes/projects/fs-syscall-specs.md.  The abstract vocabulary is
   FsAbs.v (lane A, landed); the mold is SpecSysMknodAU.v (lane W's first
   contract) -- same two-phase commit shape, same mask floor, same seal.

   ==== WHAT THIS CONTRACT IS ==========================================

   A PARALLEL FORM beside [SpecSysWrite.wp_sys_write_sconf] (R10: the
   landed contract does not move).  Same calling convention, same ambient
   premises, same threaded resources; what is NEW is that the caller hands
   in a BUNDLE of commit steps -- one per possible chunk -- fired at the
   syscall's linearization instantS against the ONE abstract state, and
   the postcondition ties the returned a0 to which chunks fired.

   ==== THE HONESTY CENTERPIECE: PER-CHUNK, NOT PER-CALL ===============

   sys_write is honestly NON-atomic in memory, and ONLY in memory (doc
   section 4).  filewrite splits a large write into MULTIPLE log
   transactions -- the few-blocks-per-tx loop, [SpecFilewrite]'s listing:
   each iteration is begin_op / ilock / writei / iunlock / end_op, at most
   [FW_MAX] = 3072 bytes -- and the inode is UNLOCKED between chunks, so a
   concurrent reader may observe any chunk boundary.  The AU form is
   therefore PER-CHUNK: a sequence of [delta_write] deltas, each with its
   own instant, each observed and witnessed by its own commit fire.  The
   friendly single-delta reading is the STABLE corollary at the bottom of
   the file, with its own honesty caveat.

   THE CHUNK DECOMPOSITION IS EXISTENTIAL.  The kernel picks the chunk
   boundaries by transaction budget, and writei may stop short inside a
   chunk; the spec must not fix either.  The arms quantify a list [bss]
   of per-chunk byte runs and state ONLY (i) each fired chunk was a real
   [delta_write] at SOME offset, and (ii) the totals: [length (concat
   bss)] equals the count on the full arm and falls short of it on the
   partial arm.  The ONE place the 3072 constant shows is [wchunks]: an
   upper bound on the NUMBER OF INSTANTS, which is what sizes the commit
   bundle the caller hands in.  A bound on the count is not a fixing of
   the boundaries; it is what makes the bundle finite (the alternative --
   a self-returning stream commit -- is a recursive iProp this layer does
   not buy; recorded as open question 1).

   OFFSETS ARE PER-CHUNK EXISTENTIAL, DELIBERATELY.  [f->off] is read and
   advanced OUTSIDE any lock (filewrite updates it after iunlock), and
   the struct file is SHARED (dup, fork), so "chunk k+1 starts where
   chunk k ended" is not a truth of the concurrent kernel -- another
   process writing through the same struct file moves the offset between
   our chunks.  Each receipt carries the offset its chunk actually fired
   at, and no chaining is claimed.  Chaining is exactly the STABLE
   corollary's content.  There is also NO client-facing offset carrier to
   pin it to: the offset lives in [fcontent] behind [file_ref] (lane A
   item (iv), the offset seam, still owed); when that seam lands, a
   refined parallel form can pin the start offset.

   THE BYTES' SOURCE IS NAMED SINCE RULING A (2026-08-31, the content
   seam).  This paragraph used to say it was not: the written bytes come
   from USER memory (a1, fetched per-chunk by either_copyin) and the
   kernel contracts said nothing about which bytes arrive.  They do now --
   either_copyin's success arm relays [SpecCopyin.copyin_got], writei
   relays it to its written range, and filewrite's loop appends the chunks
   -- so the arms below carry [SpecCopyin.ubytes_at (us_M U) v1 (concat
   bss)]: the DECOMPOSITION [bss] is still existential (the kernel picks
   the boundaries), but the BYTES are the caller's own run at syscall
   argument 1, in the image it lent.  On the CONCATENATION, not per chunk:
   the per-chunk file offsets stay existential for the concurrency reason
   above, while the SOURCE offsets chain by construction.

   ==== WHAT IT DELIBERATELY DOES NOT SAY ==============================

   NOTHING ABOUT DURABILITY.  No durable clause of any kind appears below
   (doc section 5): write's crash story is an INSTANCE of SNAPSHOT --
   each chunk boundary WAS a current state, so "recovery = some past
   current state" already says a chunk prefix (batch-aligned) may
   survive.  That sentence is deliberately not written here, or anywhere.

   NOTHING ABOUT DEVICE OR PIPE DESCRIPTORS.  The [fd_st] premise pins
   the descriptor to [FdInode], so the console and pipe arms of filewrite
   are out of this contract's domain BY PREMISE.  They are separate
   contracts when someone needs them -- a console write is not an fs
   delta, and a pipe write is a pipe-buffer story, not an [aview] one.

   NOTHING BETWEEN THE ARMS.  The return value is filewrite's: the count
   [n] when every chunk landed, MINUS ONE otherwise ([SpecFilewrite]
   decode fact 3: the inode arm answers n or -1 and nothing between --
   note this corrects the doc's section-7 sketch of "partial ret": xv6's
   filewrite does NOT return the partial count; the fired prefix's
   receipts are how the caller learns what happened).  Which failure
   produced a -1 is not distinguishable from the value, matching the
   landed contract's stance.

   ==== THE FD SIDE ====================================================

   The descriptor premise is the LANDED fd-state vocabulary, nothing
   minted (worklist note of 2026-08-27): the caller holds the per-process
   fragment [FdSlots.fd_st (pv_fdg (us_V U)) fd (FdOpen rb true (FdInode i))] --
   open, WRITABLE, an inode descriptor naming inum [i] (the inum rides
   the constructor since d1411776) -- plus the pure premise
   [arg_fd v (pv_ofile (us_V U)) = Some (fd, fv)] tying syscall argument 0 to
   that slot of the caller's own private block.  The fragment is returned
   UNCHANGED in the continuation: a write moves the offset and the file
   bytes, never the descriptor's state.  Two consequences:

   - argfd cannot fail (the premise names the slot and its non-zero
     cell), and filewrite's [f->writable == 0] arm cannot fire (the
     fragment says writable, [FileInvDefs.fdstate_ok] ties it to the
     cell the [lbu] reads).  So the arms below are TWO, not the landed
     contract's blanket: full ([r = n], all bytes) and fail ([r = -1],
     a fired PREFIX of chunks -- possibly empty, e.g. the [n < 0] guard
     or a first-chunk writei failure).
   - the receipts speak about THE CALLER'S file: every fired chunk's
     delta is at the [i] the caller's own descriptor names.

   The OFFSET is not part of the premise or the postcondition's fd side
   -- see above; "the offset advances by the bytes written" is true of
   the machine and currently unstatable as a client-facing resource fact
   (lane A (iv)).

   ==== THE COMMIT SHAPE, AND WHERE THE MASK SITS ======================

   [awrite_commit] is [SpecSysMknodAU.acre_commit]'s two-phase HOCAP mold
   at the write delta, shaped for [FsAbs.ftop_astate_acc]: the prover
   opens [ftopN] inside writei's transaction at the retag point, borrows
   [astate], fires phase 1 (the caller OBSERVES the pre-state -- the
   file's row is an [AFile]; agreement against caller-held [nview]
   shares happens here), performs the row's [ghost_map_update], fires
   phase 2 (the caller WITNESSES the post-state authority at the delta),
   pays the give-back's [inode_local] row obligation, closes [ftopN].
   One critical section, so the pair is ONE instant per chunk.

   THE MASK IS THE FLOOR [∅], mknod's ruling inherited verbatim: a
   mask-∅ fupd can be fired under whatever invariants are open at the
   retag point, and it suffices for ghost receipts and agreement.  A
   client that must open its OWN invariant at an instant asks for a
   masked variant later (a new parallel form; R10).

   THE BUNDLE.  The caller hands [awrite_commits] -- [wchunks n] copies
   of the commit, indexed by chunk -- and every arm returns the UNFIRED
   suffix.  [wchunks_covers] is the sanity fact that the bundle is big
   enough for the count; [awrite_commit_unit]/[awrite_commits_unit] are
   the satisfiability receipts (the seal cannot be vacuously blocked on
   the caller side); [awrite_commit_pinned] is the agreement seed that
   turns an observation into "YOUR value" for a caller-held share.

   ==== THE STABLE COROLLARY, AND ITS HONESTY CAVEAT ===================

   [wp_sys_write_au_stable] is the single-delta reading's STATEMENT: the
   client presents the file's own [nview] share at [MkAnode (AFile bs0)
   nl] for the duration, and the ok arm offers the CHAINED form -- the
   observed pre-rows walk [wri_row] (each chunk's pre-row is the splice
   of the chunks before it), the offsets walk [woff], and by
   [delta_write_chain] the whole call reads as ONE [delta_write] of
   [concat bss] at [off0].  TWO honesty points, sharper than mknod's:

   - THE SHARE IS ON THE WRITTEN ROW, which is exactly the shape
     SpecSysMknodAU's header REFUSES for the parent: a held [nview]
     share pins its row against every mover ([ireg_top_retag] needs the
     whole element), so it blocks THIS CALL'S OWN chunk retags.  Today
     the payload arms hold the element whole ([FsAbsSeam]'s finding 3),
     so a client share against a live inum is refuted outright and the
     form is VACUOUS.  It is the FUTURE-facing statement: the tree
     layer's cross-syscall EXCLUSIVITY fact (doc section 2 -- not a
     fraction) is the intended premise, and when it exists this
     statement is re-cut at it (a new parallel form; R10).
   - THE CHAINED ARM CARRIES AN UN-KEYED ESCAPE.  mknod's stable arms
     split on an OBSERVABLE (the fetched path vs the client's); write
     has no observable to key on, so the ok arm is "chained receipts OR
     plain receipts".  Without the escape the seal would be underivable
     from the AU form (the derivation cannot manufacture chaining that
     the per-chunk instants do not promise); with it, the derivation
     lands in the escape arm today.  The chained disjunct is the
     documented intent, not yet a deliverable.  Open question 2.

   ==== WHAT THE PROVER OWES ===========================================

   1. The fire points: [awrite_commit]'s two phases around the written
      row's [ghost_map_update], inside EACH chunk's transaction at
      writei's retag, via [ftop_astate_acc] + the [inode_local]
      give-back -- once per chunk, at the chunk's own index.
   2. The reading bridge at the update: the writei-updated record reads
      as the splice -- [fn_file_bytes n' = blk_splice off bs
      (fn_file_bytes n)] from [SpecWritei]'s record/data clauses through
      [abs_of_file], plus [SpecSysMknodAU.abs_view_insert] (reusable
      verbatim) to push the raw-map insert through [abs_view].
   3. The fd bridge: [fd_st] agreement through [ProcInv.ofile_slot] /
      [FileInvDefs.fdstate_ok] to (i) argfd's success at [(fd, fv)],
      (ii) the writable bit, (iii) the borrowed reference's state being
      [FdOpen rb true (FdInode i)] with the reference's inum equal to
      [i] ([SpecFileread.fileread_pay_carve]'s outputs).
   4. The instant count: fired chunks ≤ [wchunks n] (the loop's budget
      arithmetic; [SpecFilewrite.fw_chunk_joint] / [fw_off_advance] are
      the landed halves) and the totals per arm.
   5. [wri_pre]'s side conditions at each instant, from writei's own
      guards: the row is an [AFile] (the type witness -- fs-icache
      section 17's [ity_shot] chain, already carried by the landed
      filewrite proof), [off <= length bs0] (writei refuses past-size
      starts), the [MAXFILE*BSIZE] cap (writei's range guard), and
      [0 < length bs] (a chunk that wrote nothing fires no delta).
   6. The stable corollary, derived from the AU form + the agreement
      seed ([awrite_commit_pinned]); the escape arm is available.

   ==== OPEN QUESTIONS FOR THE OWNER ===================================

   1. The bundle is sized by [wchunks n], exposing FW_MAX as an
      instant-count bound.  Acceptable, or is a count-free shape (a
      recursive stream commit, or a commit under a persistence modality
      with caller-side receipt accounting) worth its machinery?
   2. The stable form's un-keyed escape arm (see above): keep the sealed
      statement now, or drop the stable Parameter entirely and let the
      pure chain lemmas ([blk_splice_splice], [delta_write_chain]) stand
      as the corollary until the tree layer's exclusivity fact exists?
   3. On the fail arm the value -1 hides WHERE the loop died; the fired
      prefix's receipts are the only signal.  Is a sharper pure tie
      (e.g. "the prefix total is a multiple of FW_MAX unless writei
      stopped short") wanted by any consumer, or is the honest silence
      right (it matches the landed [DETERMINISM: none] stance)?
   4. Lane A (iv), the offset seam: this contract is the first consumer
      that would use it (pin [off0], return the advanced offset).
      Schedule it, or wait for a second consumer?

   BINDERS: one instance path per scope -- [fileG] is bound and
   [icacheG]/[icfg] resolve only through its fields (SpecFilewrite's
   duplicate-instance note, inherited); the FsAbs carriers resolve their
   [fsTopG]/[fsLinkG] through [xv6G]'s fields.  The live Γ is
   [FsBytesGamma.fs_gamma_L fsc_fs]; its gname tie to [ftop_body]'s
   authority is definitional ([FsAbs.ftop_gamma_top], by reflexivity). *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list functions bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import auth gmap frac dfrac.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap ghost_map.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import InstrBytes.
Require Import RegFile.
Require Import RiscvExtras.
Require Import CalleeSaved KernelText KernelDataInv.
Require Import IntrDefs.
Require Import WpNext.
Require Import SpecPanic.
Require Import FdSlots.
Require Import ProcGeom.
Require Export SwtchCtx.
Require Import CpuOwn.
Require Import SchedCtx.
Require Import IrefSlots.
Require Import UserPtTree.
Require Import KvmSpec.
Require Import ProcPtOwn.
Require Import ProcInv.
Require Import FileInvDefs.
Require Import SpecArgfd.      (* [arg_fd]                                  *)
Require Import SpecSysRead.    (* [sys_rw_count]                            *)
Require Import ConsoleInv.
Require Import FsBlocks.       (* [blk_splice]: the landed byte splice --
                                  the delta REUSES it rather than minting a
                                  second take/drop sandwich               *)
Require Import InodeInv.       (* [MAXFILE]                                 *)
Require Import SpecFilewrite.  (* [FW_MAX], [fwrite_names], the env bundles *)
Require Import SpecCopyin.     (* [ubytes_at]: the content seam (RULING A)  *)
Require Import SpecSysWrite.   (* the landed contract this file states a
                                  parallel form beside; [sys_write_stack]  *)
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import ProcAvail.
Require Import FsAbs.          (* the abstract state (lane A, landed)       *)
Require Import FsBytesGamma.   (* [fs_gamma_L]: the live Γ                  *)
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Require Import FsCfg.  (* [fscfg]: the fs configuration is AMBIENT *)
Import Defs.
Require Import TsoCtx.

Local Open Scope Z_scope.

(* ===================================================================== *)
(*  1.  THE DELTA AND ITS ALGEBRA (PURE)                                  *)
(* ===================================================================== *)

(* THE SPLICE IS [FsBlocks.blk_splice], REUSED: [blk_splice off sub bs] is
   [take off bs ++ sub ++ drop (off + length sub) bs], which is the doc's
   "AFile (splice off bs)" already -- and it MAY GROW: past the end the
   [drop] is empty and the result's length is [off + length sub].
   [blk_splice_length_grow] is the "size = max" reading; FsBlocks's own
   [blk_splice_length] is the in-bounds special case. *)

Lemma blk_splice_nil (off : nat) (bs : list (bv 8)) :
  blk_splice off [] bs = bs.
Proof. rewrite /blk_splice /= Nat.add_0_r take_drop //. Qed.

Lemma blk_splice_length_grow (off : nat) (sub bs : list (bv 8)) :
  (off <= length bs)%nat ->
  length (blk_splice off sub bs) = Nat.max (off + length sub) (length bs).
Proof.
  intros Hle.
  rewrite /blk_splice !length_app length_take_le // length_drop. lia.
Qed.

(* THE COMPOSITION: two splices at adjacent offsets ARE one splice of the
   concatenation.  This is what makes the per-chunk deltas COMPOSE, and it
   is the pure heart of the stable corollary. *)
Lemma blk_splice_splice (off : nat) (bs1 bs2 bs0 : list (bv 8)) :
  (off <= length bs0)%nat ->
  blk_splice (off + length bs1)%nat bs2 (blk_splice off bs1 bs0)
  = blk_splice off (bs1 ++ bs2) bs0.
Proof.
  intros Hle. rewrite {1 2}/blk_splice.
  assert (HA : off = length (take off bs0))
    by (rewrite length_take_le //).
  rewrite (take_app_add' _ _ _ _ HA) take_app_length.
  rewrite -Nat.add_assoc (drop_app_add' _ _ _ _ HA) drop_app_add drop_drop.
  rewrite /blk_splice length_app Nat.add_assoc -!app_assoc //.
Qed.

(* THE DELTA (doc section 4's [δ_write]): splice [new] into the file's
   bytes at [off]; nlink untouched.  Total on purpose -- applied where the
   row is not an [AFile] it is the identity; the side conditions live in
   [wri_pre], not in the function (the mknod mold's rule). *)
Definition delta_write (i : Z) (off : nat) (new : list (bv 8))
    (av : aview) : aview :=
  match av !! i with
  | Some a =>
      match an_node a with
      | AFile bs =>
          <[i := MkAnode (AFile (blk_splice off new bs)) (an_nlink a)]> av
      | _ => av
      end
  | None => av
  end.

(* THE SIDE CONDITIONS a fired chunk's caller may assume at its instant,
   each realized by a writei guard (header, prover item 5): the row is a
   file, the chunk wrote something, the start is inside the current bytes
   (writei refuses past-size starts, so the splice never leaves a hole),
   and the end is inside the file-size cap. *)
Definition wri_pre (av : aview) (i : Z) (off : nat)
    (bs bs0 : list (bv 8)) (nl : nat) : Prop :=
  av !! i = Some (MkAnode (AFile bs0) nl)
  /\ (0 < length bs)%nat
  /\ (off <= length bs0)%nat
  /\ (off + length bs <= MAXFILE * BSIZE)%nat.

(* the delta's row algebra *)
Lemma delta_write_file (av : aview) (i : Z) (off : nat)
    (new bs0 : list (bv 8)) (nl : nat) :
  av !! i = Some (MkAnode (AFile bs0) nl) ->
  delta_write i off new av
  = <[i := MkAnode (AFile (blk_splice off new bs0)) nl]> av.
Proof. intros Hi. rewrite /delta_write Hi //=. Qed.

Lemma delta_write_lookup (av : aview) (i : Z) (off : nat)
    (new bs0 : list (bv 8)) (nl : nat) :
  av !! i = Some (MkAnode (AFile bs0) nl) ->
  delta_write i off new av !! i
  = Some (MkAnode (AFile (blk_splice off new bs0)) nl).
Proof.
  intros Hi. rewrite (delta_write_file _ _ _ _ _ _ Hi) lookup_insert //.
Qed.

Lemma delta_write_other (av : aview) (i : Z) (off : nat)
    (new : list (bv 8)) (j : Z) :
  j <> i -> delta_write i off new av !! j = av !! j.
Proof.
  intros Hj. rewrite /delta_write.
  destruct (av !! i) as [a |]; [| done].
  destruct (an_node a) as [bs | ents | ma mi]; [| done | done].
  rewrite lookup_insert_ne //.
Qed.

(* a zero-byte chunk is the identity -- which is why [wri_pre] may demand
   [0 < length bs] with nothing lost *)
Lemma delta_write_nil (av : aview) (i : Z) (off : nat)
    (bs0 : list (bv 8)) (nl : nat) :
  av !! i = Some (MkAnode (AFile bs0) nl) ->
  delta_write i off [] av = av.
Proof.
  intros Hi.
  rewrite (delta_write_file _ _ _ _ _ _ Hi) blk_splice_nil insert_id //.
Qed.

(* ---------------------------------------------------------------------
   1a.  THE CHAINED READING (what the stable corollary is made of)

   [woff off0 bss k] is where chunk [k] fires WHEN the chunks chain from
   [off0]; [wri_row bs0 off0 bss] is the file's bytes after a chained run
   of all of [bss].  [delta_write_chain] is the induction step: firing
   chunk [k] on the [take k]-folded state lands on the [take (S k)]-folded
   state -- so a chained run of the whole list IS the single delta
   [delta_write i off0 (concat bss)], which is the doc's friendly form.
   --------------------------------------------------------------------- *)

Definition woff (off0 : nat) (bss : list (list (bv 8))) (k : nat) : nat :=
  (off0 + length (concat (take k bss)))%nat.

Definition wri_row (bs0 : list (bv 8)) (off0 : nat)
    (bss : list (list (bv 8))) : list (bv 8) :=
  blk_splice off0 (concat bss) bs0.

Lemma wri_row_0 (bs0 : list (bv 8)) (off0 : nat)
    (bss : list (list (bv 8))) :
  wri_row bs0 off0 (take 0 bss) = bs0.
Proof. rewrite /wri_row take_0 /=. apply blk_splice_nil. Qed.

Lemma wri_row_snoc (bs0 : list (bv 8)) (off0 : nat)
    (bss : list (list (bv 8))) (k : nat) (bs : list (bv 8)) :
  (off0 <= length bs0)%nat ->
  bss !! k = Some bs ->
  blk_splice (woff off0 bss k) bs (wri_row bs0 off0 (take k bss))
  = wri_row bs0 off0 (take (S k) bss).
Proof.
  intros Hle Hk. rewrite /woff /wri_row.
  rewrite (take_S_r _ _ _ Hk) concat_app /= app_nil_r.
  apply blk_splice_splice, Hle.
Qed.

Lemma delta_write_chain (av : aview) (i : Z) (off0 : nat)
    (bs0 : list (bv 8)) (nl : nat) (bss : list (list (bv 8)))
    (k : nat) (bs : list (bv 8)) :
  av !! i = Some (MkAnode (AFile bs0) nl) ->
  (off0 <= length bs0)%nat ->
  bss !! k = Some bs ->
  delta_write i (woff off0 bss k) bs
    (delta_write i off0 (concat (take k bss)) av)
  = delta_write i off0 (concat (take (S k) bss)) av.
Proof.
  intros Hi Hle Hk.
  rewrite (delta_write_file av i off0 (concat (take k bss)) bs0 nl Hi).
  rewrite (delta_write_file _ i (woff off0 bss k) bs
             (blk_splice off0 (concat (take k bss)) bs0) nl);
    [| by rewrite lookup_insert].
  rewrite insert_insert.
  rewrite (delta_write_file av i off0 (concat (take (S k) bss)) bs0 nl Hi).
  do 3 f_equal.
  exact (wri_row_snoc bs0 off0 bss k bs Hle Hk).
Qed.

(* ---------------------------------------------------------------------
   1b.  THE INSTANT-COUNT BOUND

   Every chunk that CONTINUES the loop wrote exactly
   [min (n - i) FW_MAX] bytes, so at most [⌈n / FW_MAX⌉] instants fire
   (the last possibly short).  [wchunks] is that ceiling; it sizes the
   commit bundle.  [wchunks_covers] is the non-vacuity fact -- the bundle
   is big enough for the count -- and [wchunks_nonpos] the degenerate
   arms' (nothing to hand in when the count is not positive).
   --------------------------------------------------------------------- *)

Definition wchunks (n : Z) : nat := Z.to_nat ((n + FW_MAX - 1) / FW_MAX).

Lemma wchunks_covers (n : Z) :
  0 <= n -> n <= FW_MAX * Z.of_nat (wchunks n).
Proof.
  intros Hn. rewrite /wchunks Z2Nat.id.
  - assert (Hdm := Z.div_mod (n + FW_MAX - 1) FW_MAX).
    assert (Hmb := Z.mod_pos_bound (n + FW_MAX - 1) FW_MAX).
    rewrite /FW_MAX in Hdm Hmb *.
    specialize (Hdm ltac:(lia)). specialize (Hmb ltac:(lia)). lia.
  - apply Z.div_pos; rewrite /FW_MAX; lia.
Qed.

Lemma wchunks_nonpos (n : Z) : n <= 0 -> wchunks n = 0%nat.
Proof.
  intros Hn. rewrite /wchunks.
  assert (Hlt : (n + FW_MAX - 1) / FW_MAX < 1).
  { apply Z.div_lt_upper_bound; rewrite /FW_MAX; lia. }
  apply Z2Nat.nonpos. lia.
Qed.

(* ===================================================================== *)
(*  2.  THE COMMITS, THE RECEIPTS, AND THE ARMS                           *)
(* ===================================================================== *)

Section SysWriteAU.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ}.
  Implicit Types Γ : fs_view_names Σ.

  (* ------------------------------------------------------------------ *)
  (*  2a.  One chunk's commit, and the bundle                             *)
  (* ------------------------------------------------------------------ *)

  (* THE CHUNK COMMIT, two-phase (see the header: shaped for
     [ftop_astate_acc], fired inside the chunk's own transaction).  Phase
     1 lends the pre-state at the instant -- agreement against caller-held
     [nview] shares happens here; phase 2 lends the post-state authority,
     so the caller WITNESSES that the chunk's delta was applied.  [k] is
     the chunk index; the receipt family [Φ] is indexed by it.  Both
     phases at mask [E]; the machine contract instantiates the floor [∅]. *)
  Definition awrite_commit Γ (E : coPset) (i : Z) (k : nat)
      (Φ : nat -> aview -> nat -> list (bv 8) -> iProp Σ) : iProp Σ :=
    (∀ (av : aview) (off : nat) (bs bs0 : list (bv 8)) (nl : nat),
       ⌜wri_pre av i off bs bs0 nl⌝ -∗
       astate Γ av ={E}=∗
       astate Γ av ∗
         (astate Γ (delta_write i off bs av) ={E}=∗
          astate Γ (delta_write i off bs av) ∗ Φ k av off bs))%I.

  (* THE BUNDLE: [cnt] consecutive chunk commits from index [lo].  The
     caller hands [awrite_commits Γ ∅ i Φ 0 (wchunks n)]; the arms return
     the unfired suffix [awrite_commits Γ ∅ i Φ p (wchunks n - p)]. *)
  Definition awrite_commits Γ (E : coPset) (i : Z)
      (Φ : nat -> aview -> nat -> list (bv 8) -> iProp Σ)
      (lo cnt : nat) : iProp Σ :=
    ([∗ list] k ∈ seq lo cnt, awrite_commit Γ E i k Φ)%I.

  (* sanity: the commits are satisfiable with the trivial receipt (the
     module type below cannot be vacuously blocked on the caller side) *)
  Lemma awrite_commit_unit Γ E i k :
    ⊢ awrite_commit Γ E i k (fun _ _ _ _ => True%I).
  Proof.
    rewrite /awrite_commit. iIntros (av off bs bs0 nl) "%Hpre Hst".
    iModIntro. iFrame "Hst". iIntros "Hst'". iModIntro. by iFrame "Hst'".
  Qed.

  Lemma awrite_commits_unit Γ E i lo cnt :
    ⊢ awrite_commits Γ E i (fun _ _ _ _ => True%I) lo cnt.
  Proof.
    rewrite /awrite_commits. iApply big_sepL_intro.
    iIntros "!>" (j k Hk). iApply awrite_commit_unit.
  Qed.

  (* THE STABLE SEED: a caller-held [nview] share turns the phase-1
     observation's "some state" into "a state whose row at MY inum is MY
     value" -- the agreement corollary at the instant, discharged once so
     the stable form's derivation is assembly.  Note the pin at [jpin = i]
     is the DEGENERATE case the header describes: it blocks this call's
     own retags, so it is useful today only for OTHER rows (a caller
     watching a directory while writing a file, say). *)
  Lemma awrite_commit_pinned Γ E (i : Z) (k : nat) (q : Qp) (jpin : Z)
      (a : anode) (Φ : nat -> aview -> nat -> list (bv 8) -> iProp Σ) :
    nview Γ q jpin a -∗
    (∀ (av : aview) (off : nat) (bs : list (bv 8)),
       ⌜av !! jpin = Some a⌝ -∗ nview Γ q jpin a -∗ Φ k av off bs) -∗
    awrite_commit Γ E i k Φ.
  Proof.
    iIntros "Hn HΦ". rewrite /awrite_commit.
    iIntros (av off bs bs0 nl) "%Hpre Hst".
    iDestruct (astate_nview with "Hst Hn") as %Hav.
    iModIntro. iFrame "Hst". iIntros "Hst'". iModIntro. iFrame "Hst'".
    iApply ("HΦ" $! av off bs with "[%] Hn"). done.
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  2b.  The receipts                                                   *)
  (* ------------------------------------------------------------------ *)

  (* THE AU RECEIPTS: one per fired chunk, each restating its instant's
     [wri_pre] purely beside the caller's own [Φ].  The offset and the
     pre-bytes are EXISTENTIAL PER CHUNK -- the header's concurrency
     honesty: nothing ties chunk k+1's offset to chunk k's. *)
  Definition wri_receipts (i : Z)
      (Φ : nat -> aview -> nat -> list (bv 8) -> iProp Σ)
      (bss : list (list (bv 8))) : iProp Σ :=
    ([∗ list] k ↦ bs ∈ bss,
       ∃ (av : aview) (off : nat) (bs0 : list (bv 8)) (nl : nat),
         ⌜wri_pre av i off bs bs0 nl⌝ ∗ Φ k av off bs)%I.

  (* THE CHAINED RECEIPTS (the stable corollary's ok arm): the pre-rows
     walk [wri_row] and the offsets walk [woff], so by [delta_write_chain]
     the run reads as ONE delta of [concat bss] at [off0]. *)
  Definition wri_receipts_chained (i : Z) (bs0 : list (bv 8)) (nl : nat)
      (off0 : nat)
      (Φ : nat -> aview -> nat -> list (bv 8) -> iProp Σ)
      (bss : list (list (bv 8))) : iProp Σ :=
    ([∗ list] k ↦ bs ∈ bss,
       ∃ av : aview,
         ⌜av !! i = Some (MkAnode (AFile (wri_row bs0 off0 (take k bss)))
                                  nl)⌝ ∗
         Φ k av (woff off0 bss k) bs)%I.

  (* ------------------------------------------------------------------ *)
  (*  2c.  The arms                                                       *)
  (* ------------------------------------------------------------------ *)

  (* ret n (with 0 <= n): every byte landed -- the fired chunks
     concatenate to the whole count; the unfired tail of the bundle (the
     kernel may have used fewer, larger chunks than the bound) refunds. *)
  Definition write_post_ok Γ (i : Z) (n : Z)
      (M : gmap Z (bv 8)) (ua : mword 64)
      (Φ : nat -> aview -> nat -> list (bv 8) -> iProp Σ) : iProp Σ :=
    (∃ bss : list (list (bv 8)),
       ⌜Z.of_nat (length (concat bss)) = n⌝ ∗
       ⌜(length bss <= wchunks n)%nat⌝ ∗
       (* the content seam, RULING A -- see [SpecSysWriteAUEra]'s copy of
          this arm for the long note.  The DECOMPOSITION stays existential;
          the BYTES are the caller's own run at [ua]. *)
       ⌜ubytes_at M ua (concat bss)⌝ ∗
       wri_receipts i Φ bss ∗
       awrite_commits Γ ∅ i Φ (length bss)
         (wchunks n - length bss)%nat)%I.

  (* ret -1: filewrite's honest partial arm.  A PREFIX of chunks fired --
     possibly empty ([n < 0]'s guard, or the first chunk's writei failing)
     -- their deltas are REAL and their receipts are delivered; the total
     falls short of the count, the rest of the bundle refunds, and the
     value does not say where the loop died (DETERMINISM: none). *)
  Definition write_post_fail Γ (i : Z) (n : Z)
      (M : gmap Z (bv 8)) (ua : mword 64)
      (Φ : nat -> aview -> nat -> list (bv 8) -> iProp Σ) : iProp Σ :=
    (∃ bss : list (list (bv 8)),
       ⌜Z.of_nat (length (concat bss)) < n \/ (n < 0 /\ bss = [])⌝ ∗
       ⌜(length bss <= wchunks n)%nat⌝ ∗
       ⌜ubytes_at M ua (concat bss)⌝ ∗
       wri_receipts i Φ bss ∗
       awrite_commits Γ ∅ i Φ (length bss)
         (wchunks n - length bss)%nat)%I.

  (* the armed disjunction the continuation receives, keyed on a0.  TWO
     arms only: the fd premises refute argfd's and the writable test's
     failures (header, THE FD SIDE), and the inode arm answers [n] or
     [-1] and nothing between (SpecFilewrite decode fact 3). *)
  Definition write_arms Γ (i : Z) (n : Z)
      (M : gmap Z (bv 8)) (ua : mword 64)
      (Φ : nat -> aview -> nat -> list (bv 8) -> iProp Σ)
      (r : mword 64) : iProp Σ :=
    ((⌜r = (mword_of_int n : mword 64) /\ 0 <= n⌝
      ∗ write_post_ok Γ i n M ua Φ)
     ∨ (⌜r = (mword_of_int (-1) : mword 64)⌝
        ∗ write_post_fail Γ i n M ua Φ))%I.

  (* ------------------------------------------------------------------ *)
  (*  2d.  The stable corollary's arms (statement; header's caveats)      *)
  (* ------------------------------------------------------------------ *)

  (* the client's share comes back on every arm; the ok arm's chained
     disjunct is the single-delta reading, its escape disjunct the
     un-keyed honesty valve the header explains *)
  Definition write_stable_arms Γ (i : Z) (n : Z) (q : Qp)
      (bs0 : list (bv 8)) (nl : nat)
      (M : gmap Z (bv 8)) (ua : mword 64)
      (Φ : nat -> aview -> nat -> list (bv 8) -> iProp Σ)
      (r : mword 64) : iProp Σ :=
    (nview Γ q i (MkAnode (AFile bs0) nl) ∗
     ((⌜r = (mword_of_int n : mword 64) /\ 0 <= n⌝ ∗
         ∃ (off0 : nat) (bss : list (list (bv 8))),
           ⌜(off0 <= length bs0)%nat⌝ ∗
           ⌜Z.of_nat (length (concat bss)) = n⌝ ∗
           ⌜(length bss <= wchunks n)%nat⌝ ∗
           ⌜ubytes_at M ua (concat bss)⌝ ∗
           (wri_receipts_chained i bs0 nl off0 Φ bss
            ∨ wri_receipts i Φ bss) ∗
           awrite_commits Γ ∅ i Φ (length bss)
             (wchunks n - length bss)%nat)
      ∨ (⌜r = (mword_of_int (-1) : mword 64)⌝
         ∗ write_post_fail Γ i n M ua Φ)))%I.

End SysWriteAU.

(* big-op bodies behind definitions: seal them, or an [iFrame] near a
   consumer resolves instances through the whole family (durable-notes;
   optimization.md, "a big-op body is the predictor").  [awrite_commit]
   is a match-free single wand and stays transparent, as mknod's do. *)
Global Typeclasses Opaque awrite_commits wri_receipts wri_receipts_chained
  write_post_ok write_post_fail write_arms write_stable_arms.

(* ===================================================================== *)
(*  3.  THE MACHINE CONTRACT: SpecSysWrite's frame + the AU               *)
(* ===================================================================== *)

(* THE SHARED FRAME: [SpecSysWrite.wp_sys_write_sconf_body]'s premises and
   threaded resources VERBATIM (R10 -- the landed contract's calling
   convention, not a new one), plus the FD SIDE (the [arg_fd] premise and
   the caller's [fd_st] fragment, threaded in and RETURNED UNCHANGED),
   abstracted over the AU-side extras: the caller's bundle [EXTRA] and the
   armed post [ARMS] on the returned a0 (which REPLACES the landed
   ⌜sys_write_ret⌝ -- each arm pins a0 and the [arg_fd] premise supplies
   the landed disjunction's witness, so the blanket is implied).  Both
   strengths below are this frame at their own bundle and arms. *)
Definition wp_sys_write_au_frame
    `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
      !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
    (γf : gname)                    (* kalloc, the file table  *)
    (γs : list gname) (j : nat) (γlp : gname)    (* the running process    *)
    (fn : fwrite_names)                          (* the fs ghosts          *)
    (pidv : mword 32) (U : ustate)
    (v v1 v2 : mword 64)                         (* syscall args 0, 1, 2   *)
    (m : regfile) (K : nat) (eb : bool) (b : bool) (lks : gset string)
    (fd : nat) (fv : mword 64)                   (* the descriptor's slot  *)
    (rb : bool) (i : Z)                          (* its mode bit and inum  *)
    (EXTRA : iProp Σ) (ARMS : mword 64 -> iProp Σ) :=
  let pcE : mword 64 := mword_of_int KernelSyms.sys_write in
  let pj := proc_addr j in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  (sys_write_stack <= K)%nat ->
  (j < NPROC)%nat ->
  γs !! j = Some γlp ->
  length γs = NPROC ->
  fwn_j fn = j ->
  fwn_procs fn = γs ->
  pv_tf (us_V U) !! tf_arg_idx 0 = Some v ->
  (* NAMED, not existential, since RULING A: the arms speak about the bytes
     at THIS address. *)
  pv_tf (us_V U) !! tf_arg_idx 1 = Some v1 ->
  pv_tf (us_V U) !! tf_arg_idx 2 = Some v2 ->
  fwn_wp fn = ConsoleInv.devsw_write_val ->
  fwn_dqv fn = (fun _ => DfracDiscarded) ->
  eb = true ->
  (* THE FD SIDE's pure half: argument 0 names slot [fd] of the caller's
     own table, and the cell holds [fv] (non-zero by [arg_fd]'s shape) *)
  arg_fd v (pv_ofile (us_V U)) = Some (fd, fv) ->
  sie_cap_gpr KT1 m K b pj -∗
  cpu_own 0%nat eb pj b lks -∗
  kernel_text -∗ kernel_data -∗ pc_is pcE -∗
  panic_env -∗
  proc_priv γf pj pidv U -∗
  kalloc_env fsc_kalloc None -∗
  procs_inv γs -∗
  filewrite_fs_env γf fn -∗
  filewrite_dev_caps fn -∗
  ConsoleInv.devsw_table -∗
  (* THE FD SIDE's resource half: the caller's own fragment -- open,
     WRITABLE, an inode descriptor at inum [i] *)
  fd_st (pv_fdg (us_V U)) fd (FdOpen rb true (FdInode i)) -∗
  (* ---- THE AU SIDE (the one addition to the landed premise list) ---- *)
  EXTRA -∗
  wp_next true pj (fun (CID : CpuId) =>
    ∀ (mf : regfile) (r : mword 64) (P' : uptd),
      ⌜callee_saved m mf⌝ -∗
      ⌜uptd_ext_sz (pv_sz (us_V U)) (pv_upt (us_V U)) P'⌝ -∗
      ⌜mf !!! Regidx (mword_of_int 10 : mword 5) = r⌝ -∗
      sie_cap_gpr KT1 mf K b pj -∗
      cpu_own 0%nat eb pj b lks -∗
      pc_is ret_tgt -∗
      proc_priv γf pj pidv (us_upt U P') -∗
      kalloc_env fsc_kalloc None -∗
      filewrite_fs_out fn -∗
      (* the descriptor's state does not move: a write advances the
         offset and the bytes, never the fd table *)
      fd_st (pv_fdg (us_V U)) fd (FdOpen rb true (FdInode i)) -∗
      (* the armed post on the returned a0 (implies [sys_write_ret]) *)
      ARMS r -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

(* THE AU FORM.  The abstract state is read at the LIVE Γ,
   [fs_gamma_L fsc_fs] -- the gname tie to [ftop_body]'s authority is
   definitional ([FsAbs.ftop_gamma_top]).  The count is the syscall's own
   argument reading ([sys_rw_count v2] -- the whole int range; the code's
   [n < 0] guard is what the fail arm's second disjunct answers), so the
   caller's receipts speak about the count IT passed. *)
Definition wp_sys_write_au_body
    `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
      !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
    (γf : gname)
    (γs : list gname) (j : nat) (γlp : gname)
    (fn : fwrite_names)
    (pidv : mword 32) (U : ustate)
    (v v1 v2 : mword 64)
    (m : regfile) (K : nat) (eb : bool) (b : bool) (lks : gset string)
    (fd : nat) (fv : mword 64) (rb : bool) (i : Z)
    (Φw : nat -> aview -> nat -> list (bv 8) -> iProp Σ) :=
  let Γfs := fs_gamma_L fsc_fs in
  let n := sys_rw_count v2 in
  wp_sys_write_au_frame γf γs j γlp fn pidv U v v1 v2 m K eb b lks
    fd fv rb i
    (awrite_commits Γfs ∅ i Φw 0%nat (wchunks n))
    (write_arms Γfs i n (us_M U) v1 Φw).

(* THE STABLE COROLLARY'S STATEMENT (header: THE STABLE COROLLARY, AND ITS
   HONESTY CAVEAT; its derivation is the sealer's, expected from the AU
   form + the agreement seed, never as a second walk).  The client
   presents the FILE'S OWN [nview] share at its expected value for the
   duration; the ok arm offers the chained single-delta reading beside
   the un-keyed escape.  Deliberately limited, and the limits are the
   header's: the share is on the written row, so the form is VACUOUS
   until the tree layer's exclusivity fact replaces the fraction premise
   (the mknod parent-pin argument, here aimed at this call's own
   chunks). *)
Definition wp_sys_write_au_stable_body
    `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
      !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
    (γf : gname)
    (γs : list gname) (j : nat) (γlp : gname)
    (fn : fwrite_names)
    (pidv : mword 32) (U : ustate)
    (v v1 v2 : mword 64)
    (m : regfile) (K : nat) (eb : bool) (b : bool) (lks : gset string)
    (fd : nat) (fv : mword 64) (rb : bool) (i : Z)
    (q : Qp) (bs0 : list (bv 8)) (nl : nat)
    (Φw : nat -> aview -> nat -> list (bv 8) -> iProp Σ) :=
  let Γfs := fs_gamma_L fsc_fs in
  let n := sys_rw_count v2 in
  wp_sys_write_au_frame γf γs j γlp fn pidv U v v1 v2 m K eb b lks
    fd fv rb i
    (nview Γfs q i (MkAnode (AFile bs0) nl)
     ∗ awrite_commits Γfs ∅ i Φw 0%nat (wchunks n))%I
    (write_stable_arms Γfs i n q bs0 nl (us_M U) v1 Φw).

(* ===================================================================== *)
(*  4.  THE SEAL                                                          *)
(* ===================================================================== *)

Module Type SYSWRITE_AU.
  Parameter wp_sys_write_au :
    forall `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
             !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
      (γf : gname)
      (γs : list gname) (j : nat) (γlp : gname)
      (fn : fwrite_names)
      (pidv : mword 32) (U : ustate)
      (v v1 v2 : mword 64)
      (m : regfile) (K : nat) (eb : bool) (b : bool) (lks : gset string)
      (fd : nat) (fv : mword 64) (rb : bool) (i : Z)
      (Φw : nat -> aview -> nat -> list (bv 8) -> iProp Σ),
      wp_sys_write_au_body γf γs j γlp fn pidv U v v1 v2 m K eb b lks
        fd fv rb i Φw.

  (* owed as a DERIVATION from [wp_sys_write_au] + the agreement seed
     ([awrite_commit_pinned]), never as a second walk; the escape arm of
     [write_stable_arms] is what makes the derivation land (header) *)
  Parameter wp_sys_write_au_stable :
    forall `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
             !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
      (γf : gname)
      (γs : list gname) (j : nat) (γlp : gname)
      (fn : fwrite_names)
      (pidv : mword 32) (U : ustate)
      (v v1 v2 : mword 64)
      (m : regfile) (K : nat) (eb : bool) (b : bool) (lks : gset string)
      (fd : nat) (fv : mword 64) (rb : bool) (i : Z)
      (q : Qp) (bs0 : list (bv 8)) (nl : nat)
      (Φw : nat -> aview -> nat -> list (bv 8) -> iProp Σ),
      wp_sys_write_au_stable_body γf γs j γlp fn pidv U v v1 v2 m K eb b
        lks fd fv rb i q bs0 nl Φw.
End SYSWRITE_AU.
