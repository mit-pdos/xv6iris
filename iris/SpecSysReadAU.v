(* SpecSysReadAU.v -- sys_read's ATOMIC-UPDATE contract, stated over the
   campaign's abstract state.  A STATEMENT FILE: definitions, structural
   lemmas, and a [Module Type] seal -- no walk, no proof against the
   machine.

   Design of record: claude-notes/design/fs-syscall-specs.md sections 0-5
   (v3; section 7's read row -- CORRECTED by this file, see THE ONE
   INSTANT below) and lane W of claude-notes/projects/fs-syscall-specs.md.
   The abstract vocabulary is FsAbs.v (lane A, landed); the molds are
   SpecSysMknodAU.v (the family conventions; [dlookup_commit] is this
   commit's single-phase shape) and SpecSysWriteAU.v (the fd threading,
   the offset honesty, the exclusion-by-premise pattern).

   ==== WHAT THIS CONTRACT IS ==========================================

   A PARALLEL FORM beside [SpecSysRead.wp_sys_read_sconf] (R10: the landed
   contract does not move).  Same calling convention, same ambient
   premises, same threaded resources; what is NEW is that the caller hands
   in ONE read-only commit step fired at the syscall's single linearization
   instant against the ONE abstract state, and the postcondition ties the
   returned a0 to the value OBSERVED at that instant.

   ==== THE ONE INSTANT (this corrects doc section 7's read row) ========

   fileread's inode arm is

       ilock(f->ip);
       if ((r = readi(f->ip, 1, addr, f->off, n)) > 0) f->off += r;
       iunlock(f->ip);

   -- ONE lock hold, the WHOLE transfer inside it, no per-chunk unlocking
   (verified against the object code: the only calls between the arm's
   ilock and its iunlock are readi's own; contrast filewrite's
   begin_op/ilock/writei/iunlock/end_op LOOP, which is what forced
   SpecSysWriteAU's chunk bundle).  The doc's section-7 row said
   "per-chunk AU (readi)" -- PESSIMISTIC relative to the code: readi's
   interior bread/brelse per block are invisible to any concurrent
   fs-state observer because the INODE stays locked and the state never
   moves.  So this AU is SINGLE-INSTANT: one observation, no bundle, no
   concatenation algebra.  The doc table now carries the as-verified note
   (same precedent as the write lane's partial-return correction).

   ==== READ-ONLY: THE STATE NEVER MOVES ================================

   There is no delta.  The commit is [SpecSysMknodAU.dlookup_commit]'s
   single-phase read-only mold, shaped for [FsAbs.ftop_astate_ro]: the
   prover opens [ftopN] inside the lock window, borrows [astate], fires
   the caller's fupd ONCE (agreement against caller-held [nview] shares
   happens here), and hands the SAME authority back -- no row obligation,
   no ghost update, nothing for any other party to observe.  THE MASK IS
   THE FLOOR [∅], mknod's ruling inherited verbatim; the definition takes
   [E] for reuse and the machine contract instantiates [∅].

   ==== THE RETURN TIE, AND THE SLICE VOCABULARY ========================

   On a FILE row the tie is an EQUALITY, inherited from readi's own
   exactness (SpecReadi: two arms, "a caller learns that a returning
   readi read everything there was to read"):

       r  =  ard_count (Z.to_nat n) off (length bs)
          =  min n (length bs - off)        (0 once off >= length bs)

   and the delivered bytes are the SLICE [take r (drop off bs)] --
   spelled with stdpp's take/drop directly (no landed slice function
   exists to reuse; [FsBlocks.blk_splice] is the WRITE-side sandwich, and
   this file deliberately mints no dual).  [file_bytes_slice] below is
   the pure half of the readi byte bridge: the slice of the flat byte
   view IS [file_byte data <$> seq off r], which is [rd_delivered]'s
   per-index clause ([rd_delivered_file]) summed into a list.

   WHAT "DELIVERED" DOES NOT MEAN: the contract says NOTHING about the
   USER buffer's contents.  readi's user arm -- the one fileread takes --
   promises only [uptd_ext] about the destination (SpecReadi's header;
   SpecFileread inherits the silence), so the slice is VOCABULARY tying
   the return count to the observed value, not a memory postcondition.
   A kernel-arm reader (kexec, dirlookup) that wants the bytes has
   readi's own contract.

   ==== ...BUT THE LENGTH IS SAID, AND IT IS THE ANSWER =================

   [SpecSysRead] / [SpecFileread] carry the exact-count conjunct

       r = mword_of_int (Z.of_nat d)  \/  r = mword_of_int (-1)

   and this frame RELAYS IT beside the window it is about.  So the caller
   learns what "delivered" means for the DESTINATION after all, at the
   only granularity the kernel proves: HOW MANY bytes moved, never which.
   Joined with the arms it is [ard_ret_tie_pos] (the -1 disjunct is
   refuted on an ok arm, so the window's length IS the answer, on every
   row) and [ard_ret_tie_exact_file] (on a file row the length is the
   ABSTRACT count -- the bytes the observed state had to give are exactly
   the bytes that landed).  The -1 arm keeps only the bound [d <= max 0 n]
   and that is the CODE's doing: readi overwrites its running [tot] with
   -1 when a copyout faults, discarding blocks it has already delivered,
   so a read really can return -1 with bytes in the buffer.  On that arm
   [read_post_fail]'s right disjunct is what still reports the
   observation.

   ==== THE DIRECTORY ARM (deviation from the lane W brief) =============

   A readable FD_INODE descriptor may name a DIRECTORY: xv6's open()
   maps T_DEVICE inodes to FD_DEVICE but keeps T_DIR under FD_INODE
   (ls reads directories through read()).  The landed [fd_st] fragment
   carries only the inum, so file-ness is NOT excludable by premise --
   unlike write, where the writable bit's [ity_shot] side condition
   ("a writable fd is not a directory", [fileread_pay_carve]'s clause)
   does exactly that.  The commit therefore observes the WHOLE [anode]
   and the return tie is a match:

   - [AFile bs]  -> the exact count equation above (the whole slice
                    algebra applies);
   - [ADir _]    -> BOUNDS ONLY ([0 <= r <= n]) AS AGAINST THE ABSTRACT
                    SIZE: readi still answers exactly
                    [rd_clamp (dir's size)], but a directory's BYTE size
                    (nrec * 16) is not recoverable from its [aview]
                    reading (the first-match entry map forgets the dirent
                    encoding, deliberately -- doc section 1), so an exact
                    tie to the STATE is unstatable at this abstraction.
                    It is NOT bounds-only about the DELIVERY: the
                    exact-count conjunct relayed below pins [r] to the
                    window's length on this arm too, and
                    [ard_ret_tie_pos] is where the bound's existential
                    witness becomes [Z.of_nat d];
   - [ADev _ _]  -> folded into the bounds arm rather than REFUTED.  An
                    FD_INODE descriptor never names a device row, but
                    the client-visible tie "FdInode => the row reads
                    AFile or ADir" is a custody fact no landed lemma
                    exports; refuting ADev would charge the seal for it.
                    Open question 2.

   ==== THE FD SIDE =====================================================

   The landed fd-state vocabulary, nothing minted (the write mold's
   pattern): the caller holds [FdSlots.fd_st (pv_fdg (us_V U)) fd
   (FdOpen true wb (FdInode i))] -- open, READABLE, an inode descriptor
   naming inum [i] -- plus the pure premise [arg_fd v (pv_ofile (us_V U)) =
   Some (fd, fv)].  The fragment is returned UNCHANGED: a read moves the
   offset, never the descriptor's state.  Consequences: argfd cannot
   fail, fileread's [f->readable == 0] arm cannot fire, and the pipe /
   device / panic arms are out of this contract's domain BY PREMISE
   (they are separate contracts when someone needs them -- the write
   mold's stance, verbatim).

   THE OFFSET IS PER-INSTANT EXISTENTIAL (the family ruling).  [f->off]
   lives in [fcontent] behind [file_ref] with no client-facing carrier
   (lane A item (iv), the offset seam, still owed) -- so the receipt
   carries the offset the call actually used and nothing pins it.  Note
   the honesty here is CHEAPER than write's: the offset is read AND
   advanced ([f->off += r] on [r > 0]; unmoved otherwise) inside the ONE
   lock hold, so within a call there is nothing to chain -- the
   existential is one, not a family.  When the offset seam lands, a
   refined parallel form can pin the start offset and return the
   advance; this contract is that seam's SECOND consumer.

   ==== THE FAILURE ARMS, AS THIS FORK'S CODE HAS THEM ==================

   - [n < 0]: THIS FORK'S fileread has a sign guard the stock C does not
     -- [srliw a5,a2,0x1f ; c.bnez a5] at +0x1a (XV6_REV 31f115a),
     branching to the -1 block BEFORE the type dispatch, hence before
     ilock.  Nothing fs-visible happens; the commit comes back unspent.
   - readi's COPYOUT FAULT: the one way the inode arm's transfer stops
     short.  Verified against SpecReadi (its header and post): under
     [bm_covers] the "bmap returned 0" break is dead, either_copyout
     answers 0 unconditionally on the kernel arm, so the fault arm is
     [a0 = -1 /\ user = true] -- readi sets [tot = -1] and breaks;
     fileread's [r > 0] test then fails, THE OFFSET IS NOT ADVANCED, and
     -1 is returned.  The observation still FIRED (the lock window
     happened; the receipt reports the value the transfer was serving
     from); how much of the slice reached user memory before the fault
     is unstated, exactly as the success arm's buffer contents are.
   - [f->readable == 0] and argfd's -1: refuted by the premises.
   The value -1 does not say which of the two live arms produced it
   (DETERMINISM: none, the landed stance); the ⌜n < 0⌝ / ⌜0 <= n⌝ keys
   inside [read_post_fail] separate them for a caller that knows its
   count's sign -- which every caller does, [n] being its own argument.

   ==== WHAT IT DELIBERATELY DOES NOT SAY ==============================

   NOTHING ABOUT DURABILITY -- and for the first time in the family the
   omission is TRIVIALLY EXACT rather than a discipline: there is no
   delta, so doc section 5's "zero per-syscall durable clauses" holds
   with nothing to even defer to SNAPSHOT.  NOTHING about the user
   buffer or the offset cell (above).  ATOMICITY, by contrast, IS
   claimed, for the WHOLE transfer: one lock hold means every concurrent
   fs-state observer sees the read as one instant -- this is strictly
   stronger than the write contract could honestly say, and it is the
   lock hold, not a spec choice, that pays for it.

   ==== THE STABLE COROLLARY, AND WHY IT NEEDS NO ESCAPE ===============

   [wp_sys_read_au_stable] is the "YOUR bytes" reading: the client
   presents the file's own [nview] share at [MkAnode (AFile bs0) nl] and
   every arm's receipt lands at that value -- [r] is the exact count
   over [bs0], or -1 with the receipt still fired.  TWO points:

   - NO ESCAPE ARM, unlike write.  One instant + agreement collapse the
     derivation completely ([aread_commit_pinned_self] below); write's
     un-keyed escape existed because chaining across instants could not
     be manufactured, and there is nothing to chain here.  One premise
     is the price: [0 <= sys_rw_count v2].  Without it the [n < 0] arm
     refunds the commit UNFIRED, and the wrapped share would be
     stranded inside the closure; with it every arm fires and the share
     returns through the receipt.  The premise costs a caller nothing:
     the count is its own trapframe argument.
   - THE USUAL VACUITY CAVEAT, with a sharper edge than write's.  Today
     the payload arms hold the element WHOLE ([FsAbsSeam]'s finding 3),
     so a client [nview] share against a live inum is refuted and the
     form is vacuous until the tree layer's cross-syscall EXCLUSIVITY
     fact (or an era-fragment-style lend) exists.  BUT -- unlike write,
     where a share on the written row would block that call's own
     retags -- a read fires NO retag, so the statement needs no re-cut
     when the custody seam moves: the same sealed form becomes
     non-vacuous as-is.

   ==== WHAT THE PROVER OWES ===========================================

   1. THE SINGLE FIRE: inside the FD_INODE arm's lock window (any
      instruction boundary between ilock's return and iunlock), open
      [ftopN], take [ftop_astate_ro], identify the authority's row at
      [i] with the loaded payload's node ([FsAbs.abs_view_lookup] + the
      [abs_of] readings over [fileread_pay_carve]'s outputs), and fire
      the commit at the checked-out offset.  [ard_pre]'s caps come from
      [FileInvDefs.off_wf] (the offset) and the region's size invariant
      (the bytes; readi's own [di_size <= MAXFILE*BSIZE] premise is
      discharged from the same source).
   2. THE COUNT BRIDGE on the file arm: readi's arm 2 gives
      [tot = rd_clamp (di_size dn) off n']; [rd_clamp_ard] +
      [length_fn_file_bytes] + [FsAbs.abs_of_file] turn that into the
      [ard_count] tie over the OBSERVED [bs]; the argument ties are
      [SpecReadi.rd_arg32_small] at [n' = Z.to_nat n] (0 <= n < 2^31
      past the guard, [SpecSysRead.sys_rw_count_lt]) and the checked-out
      offset word.
   3. THE FD BOOKKEEPING: [fd_st] agreement through [ProcInv.ofile_slot]
      / [FileInvDefs.fdstate_ok] to argfd's success at [(fd, fv)], the
      readable bit, and the borrowed reference's payload naming inum
      [i]; the fragment handed back unchanged.
   4. THE GUARD ARM: +0x1a/+0x1e to the -1 block with the bundle
      untouched (ProofFileread already walks it).
   5. THE FAULT ARM: readi's [-1 /\ user = true] disjunct into
      [read_post_fail]'s fired arm (the fire from item 1 has already
      happened by the time readi returns).
   6. THE DIR/OTHER BOUNDS: fileread's own [fileread_ret] bounds into
      [ard_ret_tie]'s wildcard arm.
   7. THE STABLE COROLLARY, derived from the AU form + the agreement
      seed ([aread_commit_pinned_self]), never as a second walk; the
      [0 <= n] premise is what makes every arm's receipt fire.

   ==== OPEN QUESTIONS FOR THE OWNER ===================================

   1. DIRECTORY READS are bounds-only here (the dirent byte encoding is
      beneath [aview], deliberately).  If a verified ls-style consumer
      ever needs the delivered dirent bytes, that is a NEW parallel form
      stated at the raw [fs_node] reading, not a strengthening of this
      one -- schedule then, or never?
   2. THE [ADev] FOLD: refuting the device row on an FD_INODE descriptor
      needs a client-visible "FdInode => AFile or ADir" custody tie that
      no landed lemma exports.  Worth landing (a one-conjunct sharpening
      of [ard_ret_tie]'s wildcard to [ADir] only, R10-clean since the
      arm only ever weakens toward the caller), or is the fold fine?
   3. The commit mask floor [∅]: inherited from mknod's ruling; confirm
      no first consumer needs its own invariant open at the instant.
   4. Lane A (iv), the offset seam, now has a SECOND consumer (write was
      the first): pin the start offset, return the [r > 0] advance.
      Schedule it?

   BINDERS: one instance path per scope -- [fileG] is bound and
   [icacheG]/[icfg] resolve only through its fields (SpecFileread's
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
Require Import ConsoleInv.
Require Import FsTree.         (* [file_bytes]: the landed flat byte-list
                                  reading the slice vocabulary is cut from  *)
Require Import PipeInvDefs.    (* [pipe_rw_ret], the landed blanket the
                                  sanity lemma folds the arms back into    *)
Require Import InodeInv.       (* [MAXFILE]; exports InodeDefs' [file_byte] *)
Require Import SpecReadi.      (* [rd_clamp], [rd_delivered]: what readi
                                  actually answers -- the tie is to THESE  *)
Require Import SpecFileread.   (* [fread_names], the env bundles,
                                  [fileread_ret]                           *)
Require Import SpecSysRead.    (* the landed contract this file states a
                                  parallel form beside; [sys_rw_count]     *)
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
(*  1.  THE COUNT, THE SLICE, AND THE READI BRIDGE (PURE)                 *)
(* ===================================================================== *)

(* THE COUNT a full transfer answers: [n] clamped to the file's end --
   0 once [off] is at or past the end (nat subtraction), which is the
   EOF-returns-0 arm folded into the same equation, readi's own collapse
   ("the up-front bounds failure is NOT a third arm"). *)
Definition ard_count (n off len : nat) : nat := Nat.min n (len - off)%nat.

Lemma ard_count_le (n off len : nat) : (ard_count n off len <= n)%nat.
Proof. apply Nat.le_min_l. Qed.

Lemma ard_count_sub (n off len : nat) :
  (ard_count n off len <= len - off)%nat.
Proof. apply Nat.le_min_r. Qed.

Lemma ard_count_eof (n off len : nat) :
  (len <= off)%nat -> ard_count n off len = 0%nat.
Proof. rewrite /ard_count. lia. Qed.

Lemma ard_count_full (n off len : nat) :
  (off + n <= len)%nat -> ard_count n off len = n.
Proof. rewrite /ard_count. lia. Qed.

(* r = 0 is EXACTLY "nothing was asked or nothing is there" *)
Lemma ard_count_0 (n off len : nat) :
  ard_count n off len = 0%nat <-> n = 0%nat \/ (len <= off)%nat.
Proof. rewrite /ard_count. lia. Qed.

(* THE BRIDGE TO READI'S OWN CLAMP: [rd_clamp] over the size word IS
   [ard_count] over the byte count -- the prover's item 2 rewrites
   readi's arm 2 through this. *)
Lemma rd_clamp_ard (szw : bv 32) (off n : nat) :
  rd_clamp szw off n = ard_count n off (Z.to_nat (bv_unsigned szw)).
Proof.
  rewrite /rd_clamp /ard_count.
  destruct (decide (Z.to_nat (bv_unsigned szw) < off + n)%nat); lia.
Qed.

(* the flat byte-list reading has the length its name says -- which is
   what ties [length bs] to the size word the clamp is stated over *)
Lemma length_file_bytes (data : nat -> list (bv 8)) (len : nat) :
  length (file_bytes data len) = len.
Proof. rewrite /file_bytes length_fmap length_seq //. Qed.

Lemma length_fn_file_bytes (n : fs_node) :
  length (fn_file_bytes n) = Z.to_nat (fn_size n).
Proof. rewrite /fn_file_bytes length_file_bytes //. Qed.

(* THE SLICE IS EXACT ON BOTH ENDS: [take r (drop off bs)] has length
   exactly [r] whenever [r] fits, and the count always fits *)
Lemma ard_slice_length (off r : nat) (bs : list (bv 8)) :
  (r <= length bs - off)%nat ->
  length (take r (drop off bs)) = r.
Proof.
  intros Hr. rewrite length_take_le; [done | rewrite length_drop; lia].
Qed.

Lemma ard_slice_count (n off : nat) (bs : list (bv 8)) :
  length (take (ard_count n off (length bs)) (drop off bs))
  = ard_count n off (length bs).
Proof. apply ard_slice_length, Nat.le_min_r. Qed.

(* THE READI BYTE BRIDGE'S PURE HALF: the slice of the flat view is the
   per-index [file_byte] family readi's kernel arm delivers, summed into
   a list -- what turns [rd_delivered]'s pointwise clause into "the
   destination holds the slice" for a kernel-arm reader, and what makes
   the slice the honest VOCABULARY for the user arm (header). *)
Lemma file_bytes_slice (data : nat -> list (bv 8)) (len off r : nat) :
  (r <= len - off)%nat ->
  take r (drop off (file_bytes data len)) = file_byte data <$> seq off r.
Proof.
  intros Hr. rewrite /file_bytes -fmap_drop -fmap_take.
  rewrite drop_seq take_seq Nat.add_0_l Nat.min_l //.
Qed.

(* ...and [rd_delivered] below the count IS that family, index by index *)
Lemma rd_delivered_file (data : nat -> list (bv 8)) (dst_olds : nat -> bv 8)
    (off tot i : nat) :
  (i < tot)%nat ->
  rd_delivered data dst_olds off tot i = file_byte data (off + i)%nat.
Proof. intros Hi. rewrite /rd_delivered decide_True //. Qed.

(* --------------------------------------------------------------------- *)
(*  1a.  The observation's side conditions, and the return tie            *)
(* --------------------------------------------------------------------- *)

(* the one row-shaped cap the machine realizes: a FILE's bytes fit the
   size cap (the region invariant readi itself trusts); the other kinds
   carry nothing *)
Definition anode_size_ok (a : anode) : Prop :=
  match an_node a with
  | AFile bs => (length bs <= MAXFILE * BSIZE)%nat
  | _ => True
  end.

(* WHAT A FIRED OBSERVATION MAY ASSUME AT ITS INSTANT, each conjunct
   realized by the machine (header, prover items 1): the row IS the
   authority's at [i]; the offset the call used respects [off_wf]; the
   row's bytes respect the size cap. *)
Definition ard_pre (av : aview) (i : Z) (off : nat) (a : anode) : Prop :=
  av !! i = Some a
  /\ (off <= MAXFILE * BSIZE)%nat
  /\ anode_size_ok a.

(* THE RETURN TIE, keyed on what the observed row IS (header: THE
   DIRECTORY ARM).  A file answers the exact count; a directory (or the
   never-realized device fold -- open question 2) answers within the
   landed blanket's bounds. *)
Definition ard_ret_tie (n : Z) (a : anode) (off : nat) (r : mword 64)
    : Prop :=
  match an_node a with
  | AFile bs =>
      r = (mword_of_int
             (Z.of_nat (ard_count (Z.to_nat n) off (length bs)))
           : mword 64)
  | _ => exists rv : Z, r = (mword_of_int rv : mword 64) /\ 0 <= rv <= n
  end.

(* SANITY: every ok-arm value sits inside the landed blanket
   [fileread_ret] -- the AU arms IMPLY [SpecSysRead.sys_read_ret]'s
   Some-side disjunct (the [arg_fd] premise supplies the witness), so
   the parallel form never contradicts the landed contract. *)
Lemma ard_ret_tie_ret (n : Z) (a : anode) (off : nat) (r : mword 64) :
  0 <= n -> ard_ret_tie n a off r -> fileread_ret n r.
Proof.
  rewrite /ard_ret_tie /fileread_ret /pipe_rw_ret.
  destruct (an_node a) as [bs | ents | ma mi].
  - intros Hn ->. right.
    exists (Z.of_nat (ard_count (Z.to_nat n) off (length bs))).
    split; [reflexivity |].
    assert (Hk : (ard_count (Z.to_nat n) off (length bs) <= Z.to_nat n)%nat)
      by apply Nat.le_min_l.
    assert (HkZ : Z.of_nat (ard_count (Z.to_nat n) off (length bs))
                  <= Z.of_nat (Z.to_nat n))
      by (apply Nat2Z.inj_le; exact Hk).
    rewrite (Z2Nat.id n Hn) in HkZ. lia.
  - intros Hn (rv & -> & Hrv). right. exists rv.
    split; [reflexivity | lia].
  - intros Hn (rv & -> & Hrv). right. exists rv.
    split; [reflexivity | lia].
Qed.

(* --------------------------------------------------------------------- *)
(*  1b.  THE EXACT-COUNT JOIN: the return tie meets the window's length   *)
(* --------------------------------------------------------------------- *)

(* [SpecFilereadAU] / [SpecSysReadAUAt] relay the kernel contracts' output
   conjunct -- a non-negative answer IS the number of bytes written,

       r = mword_of_int (Z.of_nat d)  \/  r = mword_of_int (-1)

   -- and THIS is where it meets [ard_ret_tie].  Every ok-arm value is a
   non-negative count below [n < 2^31], so the -1 disjunct is REFUTED
   ([ard_ret_tie_pos]) and the window's length is the answer on EVERY row.

   WHAT THAT BUYS THE DIRECTORY ARM, and it is more than the header's
   "BOUNDS ONLY" suggests: on a non-file row [ard_ret_tie] says only
   [∃ rv, r = mword_of_int rv /\ 0 <= rv <= n], and [ard_ret_tie_pos]
   supplies the witness -- [rv] IS [Z.of_nat d].  So the DELIVERY is exact
   on a directory read too; what remains bounds-only is the relation of
   that count to the row's abstract SIZE, and that is [aview]'s deliberate
   forgetting of the dirent encoding (open question 1), not a weakness of
   the count.  On a file row the two facts compose all the way to the
   abstract state ([ard_ret_tie_exact_file]). *)

Local Lemma moi64_lit_inj (x y : Z) :
  0 <= x < 18446744073709551616 -> 0 <= y < 18446744073709551616 ->
  (mword_of_int x : mword 64) = (mword_of_int y : mword 64) -> x = y.
Proof.
  intros Hx Hy Heq.
  assert (Hx' : bv_wrap 64 x = x)
    by (apply bvw64_small; change (2 ^ 64)%Z with 18446744073709551616%Z; lia).
  assert (Hy' : bv_wrap 64 y = y)
    by (apply bvw64_small; change (2 ^ 64)%Z with 18446744073709551616%Z; lia).
  apply (f_equal bv_unsigned) in Heq.
  rewrite !moi64_unsigned Hx' Hy' in Heq. exact Heq.
Qed.

Local Lemma moi64_lit_ne_m1 (x : Z) :
  0 <= x < 18446744073709551615 ->
  (mword_of_int x : mword 64) <> (mword_of_int (-1) : mword 64).
Proof.
  intros Hx Heq.
  assert (Hx' : bv_wrap 64 x = x)
    by (apply bvw64_small; change (2 ^ 64)%Z with 18446744073709551616%Z; lia).
  assert (Hm1 : bv_wrap 64 (-1) = 18446744073709551615%Z)
    by (vm_compute; reflexivity).
  apply (f_equal bv_unsigned) in Heq.
  rewrite !moi64_unsigned Hx' Hm1 in Heq. lia.
Qed.

(* the ok arm's value is never the -1 literal, so the relayed disjunction
   collapses: THE ANSWER IS THE WINDOW'S LENGTH, on every row *)
Lemma ard_ret_tie_pos (n : Z) (a : anode) (off d : nat) (r : mword 64) :
  0 <= n < 2 ^ 31 ->
  ard_ret_tie n a off r ->
  (r = (mword_of_int (Z.of_nat d) : mword 64)
   \/ r = (mword_of_int (-1) : mword 64)) ->
  r = (mword_of_int (Z.of_nat d) : mword 64).
Proof.
  intros Hn Htie [Hd | Hm1]; [exact Hd |].
  exfalso. change (2 ^ 31)%Z with 2147483648%Z in Hn.
  rewrite /ard_ret_tie in Htie. revert Htie.
  destruct (an_node a) as [bs | ents | ma mi]; intros Htie.
  - rewrite Htie in Hm1.
    assert (Hk : (ard_count (Z.to_nat n) off (length bs) <= Z.to_nat n)%nat)
      by apply ard_count_le.
    apply Nat2Z.inj_le in Hk. rewrite Z2Nat.id in Hk; [| lia].
    assert (Hrg : 0 <= Z.of_nat (ard_count (Z.to_nat n) off (length bs))
                  < 18446744073709551615) by lia.
    exact (moi64_lit_ne_m1 _ Hrg Hm1).
  - destruct Htie as (rv & Hrv & Hb). rewrite Hrv in Hm1.
    assert (Hrg : 0 <= rv < 18446744073709551615) by lia.
    exact (moi64_lit_ne_m1 _ Hrg Hm1).
  - destruct Htie as (rv & Hrv & Hb). rewrite Hrv in Hm1.
    assert (Hrg : 0 <= rv < 18446744073709551615) by lia.
    exact (moi64_lit_ne_m1 _ Hrg Hm1).
Qed.

(* ...and on a FILE row the length is the ABSTRACT count: the bytes the
   observed state had to give are exactly the bytes that landed *)
Lemma ard_ret_tie_exact_file (n : Z) (bs : list (bv 8)) (a : anode)
    (off d : nat) (r : mword 64) :
  0 <= n < 2 ^ 31 ->
  (Z.of_nat d <= Z.max 0 n)%Z ->
  an_node a = AFile bs ->
  ard_ret_tie n a off r ->
  (r = (mword_of_int (Z.of_nat d) : mword 64)
   \/ r = (mword_of_int (-1) : mword 64)) ->
  d = ard_count (Z.to_nat n) off (length bs).
Proof.
  intros Hn Hdle Hfile Htie Hor.
  pose proof (ard_ret_tie_pos n a off d r Hn Htie Hor) as Hpos.
  change (2 ^ 31)%Z with 2147483648%Z in Hn.
  rewrite Z.max_r in Hdle; [| lia].
  rewrite /ard_ret_tie Hfile in Htie.
  rewrite Htie in Hpos.
  assert (Hk : (ard_count (Z.to_nat n) off (length bs) <= Z.to_nat n)%nat)
    by apply ard_count_le.
  apply Nat2Z.inj_le in Hk. rewrite Z2Nat.id in Hk; [| lia].
  assert (Hrg1 : 0 <= Z.of_nat (ard_count (Z.to_nat n) off (length bs))
                 < 18446744073709551616) by lia.
  assert (Hrg2 : 0 <= Z.of_nat d < 18446744073709551616) by lia.
  apply (moi64_lit_inj _ _ Hrg1 Hrg2) in Hpos.
  lia.
Qed.

(* ===================================================================== *)
(*  2.  THE COMMIT, THE SEEDS, AND THE ARMS                               *)
(* ===================================================================== *)

Section SysReadAU.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ}.
  Implicit Types Γ : fs_view_names Σ.

  (* ------------------------------------------------------------------ *)
  (*  2a.  The observation commit                                         *)
  (* ------------------------------------------------------------------ *)

  (* SINGLE-PHASE AND READ-ONLY, [dlookup_commit]'s mold at the whole
     [anode]: the state does not move, the caller hands the SAME
     authority back ([ftop_astate_ro]'s shape), and no row obligation
     arises.  Fired ONCE, inside fileread's lock window; agreement
     against caller-held [nview] shares happens here.  [E] for reuse;
     the machine contract instantiates the floor [∅]. *)
  Definition aread_commit Γ (E : coPset) (i : Z)
      (Φ : aview -> nat -> anode -> iProp Σ) : iProp Σ :=
    (∀ (av : aview) (off : nat) (a : anode),
       ⌜ard_pre av i off a⌝ -∗
       astate Γ av ={E}=∗ astate Γ av ∗ Φ av off a)%I.

  (* sanity: satisfiable with the trivial receipt (the module type below
     cannot be vacuously blocked on the caller side) *)
  Lemma aread_commit_unit Γ E i :
    ⊢ aread_commit Γ E i (fun _ _ _ => True%I).
  Proof.
    rewrite /aread_commit. iIntros (av off a) "%Hpre Hst".
    iModIntro. by iFrame "Hst".
  Qed.

  (* THE STABLE SEEDS.  The general one watches ANY row (a caller
     watching a directory while reading a file, say); the SELF one is
     read's own collapse -- the pin is on the READ row and agreement
     forces the observed node to be the client's, with no cost to any
     arm (a read fires no retag, so a held share blocks nothing this
     call does; the vacuity is the custody seam alone -- header). *)
  Lemma aread_commit_pinned Γ E (i : Z) (q : Qp) (jpin : Z) (b : anode)
      (Φ : aview -> nat -> anode -> iProp Σ) :
    nview Γ q jpin b -∗
    (∀ (av : aview) (off : nat) (a : anode),
       ⌜av !! jpin = Some b⌝ -∗ nview Γ q jpin b -∗ Φ av off a) -∗
    aread_commit Γ E i Φ.
  Proof.
    iIntros "Hn HΦ". rewrite /aread_commit.
    iIntros (av off a) "%Hpre Hst".
    iDestruct (astate_nview with "Hst Hn") as %Hav.
    iModIntro. iFrame "Hst".
    iApply ("HΦ" $! av off a with "[%] Hn"). done.
  Qed.

  Lemma aread_commit_pinned_self Γ E (i : Z) (q : Qp) (b : anode)
      (Φ : aview -> nat -> anode -> iProp Σ) :
    nview Γ q i b -∗
    (∀ (av : aview) (off : nat),
       ⌜av !! i = Some b⌝ -∗ nview Γ q i b -∗ Φ av off b) -∗
    aread_commit Γ E i Φ.
  Proof.
    iIntros "Hn HΦ". rewrite /aread_commit.
    iIntros (av off a) "%Hpre Hst".
    iDestruct (astate_nview with "Hst Hn") as %Hav.
    destruct Hpre as (Hrow & _ & _).
    assert (a = b) as -> by congruence.
    iModIntro. iFrame "Hst".
    iApply ("HΦ" $! av off with "[%] Hn"). done.
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  2b.  The arms                                                       *)
  (* ------------------------------------------------------------------ *)

  (* ret >= 0: the observation fired and the value IS the tie's -- keyed
     by the equation itself rather than by a constant (the count depends
     on the instant's offset and the observed bytes; readi's exactness
     is what makes it an equality and not a bound on the file arm).
     [0 <= n] rides because this arm is only reachable past the fork's
     sign guard. *)
  Definition read_post_ok Γ (i : Z) (n : Z)
      (Φ : aview -> nat -> anode -> iProp Σ) (r : mword 64) : iProp Σ :=
    (∃ (av : aview) (off : nat) (a : anode),
       ⌜ard_pre av i off a⌝ ∗ ⌜0 <= n⌝ ∗ ⌜ard_ret_tie n a off r⌝ ∗
       Φ av off a)%I.

  (* ret -1: the fork's two live failure arms, keyed by the sign the
     caller already knows (header: THE FAILURE ARMS).  The guard arm
     ([n < 0], pre-lock) refunds the commit unspent; the copyout-fault
     arm delivers the FIRED receipt -- the transfer's source value was
     observed even though the copy died -- with no count tie (readi
     answers -1, the offset does not move, the user bytes are unstated). *)
  Definition read_post_fail Γ (i : Z) (n : Z)
      (Φ : aview -> nat -> anode -> iProp Σ) : iProp Σ :=
    ((⌜n < 0⌝ ∗ aread_commit Γ ∅ i Φ)
     ∨ (⌜0 <= n⌝
        ∗ ∃ (av : aview) (off : nat) (a : anode),
            ⌜ard_pre av i off a⌝ ∗ Φ av off a))%I.

  (* the armed disjunction the continuation receives, keyed on a0 *)
  Definition read_arms Γ (i : Z) (n : Z)
      (Φ : aview -> nat -> anode -> iProp Σ) (r : mword 64) : iProp Σ :=
    (read_post_ok Γ i n Φ r
     ∨ (⌜r = (mword_of_int (-1) : mword 64)⌝
        ∗ read_post_fail Γ i n Φ))%I.

  (* ------------------------------------------------------------------ *)
  (*  2c.  The stable corollary's arms (statement; header's caveats)      *)
  (* ------------------------------------------------------------------ *)

  (* the client's share comes back on every arm, and every arm's receipt
     is at the client's OWN value: [r] is the exact count over [bs0] at
     the instant's offset, or -1 (the fault) with the receipt still
     fired.  No escape arm, no unfired residue -- the [0 <= n] premise
     of the stable body is what removes the refund arm (header). *)
  Definition read_stable_arms Γ (i : Z) (n : Z) (q : Qp)
      (bs0 : list (bv 8)) (nl : nat)
      (Φ : aview -> nat -> anode -> iProp Σ) (r : mword 64) : iProp Σ :=
    (nview Γ q i (MkAnode (AFile bs0) nl) ∗
     (∃ (av : aview) (off : nat),
        ⌜av !! i = Some (MkAnode (AFile bs0) nl)⌝ ∗
        ⌜(off <= MAXFILE * BSIZE)%nat⌝ ∗
        ⌜(length bs0 <= MAXFILE * BSIZE)%nat⌝ ∗
        ⌜r = (mword_of_int
                (Z.of_nat (ard_count (Z.to_nat n) off (length bs0)))
              : mword 64)
         \/ r = (mword_of_int (-1) : mword 64)⌝ ∗
        Φ av off (MkAnode (AFile bs0) nl)))%I.

End SysReadAU.

(* Sealed for family uniformity with the two siblings' arm families --
   none of these carries a big-op today (the read AU has no bundle), so
   this is convention, not the optimization.md necessity it is for the
   molds.  [aread_commit] is a match-free single wand and stays
   transparent, as the siblings' commits do. *)
Global Typeclasses Opaque read_post_ok read_post_fail read_arms
  read_stable_arms.

(* ===================================================================== *)
(*  3.  THE MACHINE CONTRACT: SpecSysRead's frame + the AU                *)
(* ===================================================================== *)

(* THE SHARED FRAME: [SpecSysRead.wp_sys_read_sconf_body]'s premises and
   threaded resources VERBATIM (R10 -- the landed contract's calling
   convention, not a new one), plus the FD SIDE (the [arg_fd] premise and
   the caller's [fd_st] fragment, threaded in and RETURNED UNCHANGED),
   abstracted over the AU-side extras: the caller's commit [EXTRA] and
   the armed post [ARMS] on the returned a0 (which REPLACES the landed
   ⌜sys_read_ret⌝ -- the arms imply [fileread_ret] ([ard_ret_tie_ret] /
   the -1 literal) and the [arg_fd] premise supplies the landed
   disjunction's witness, so the blanket is implied).  Both strengths
   below are this frame at their own bundle and arms. *)
Definition wp_sys_read_au_frame
    `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
      !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
    (γf : gname)                    (* kalloc, the file table  *)
    (γs : list gname) (j : nat) (γlp : gname)    (* the running process    *)
    (fn : fread_names)                           (* the fs ghosts          *)
    (pidv : mword 32) (U : ustate)
    (v v1 v2 : mword 64)                         (* syscall args 0, 1, 2   *)
    (m : regfile) (K : nat) (eb : bool) (b : bool) (lks : gset string)
    (fd : nat) (fv : mword 64)                   (* the descriptor's slot  *)
    (wb : bool) (i : Z)                          (* its mode bit and inum  *)
    (EXTRA : iProp Σ) (ARMS : mword 64 -> iProp Σ) :=
  let pcE : mword 64 := mword_of_int KernelSyms.sys_read in
  let pj := proc_addr j in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  (sys_read_stack <= K)%nat ->
  (j < NPROC)%nat ->
  γs !! j = Some γlp ->
  length γs = NPROC ->
  pv_tf (us_V U) !! tf_arg_idx 0 = Some v ->
  (* ARGUMENT 1 IS NAMED, NOT EXISTENTIAL (the landed contract's own
     spelling, restored): the destination address is what the window in the
     post is stated at, and the window is what carries the exact count. *)
  pv_tf (us_V U) !! tf_arg_idx 1 = Some v1 ->
  pv_tf (us_V U) !! tf_arg_idx 2 = Some v2 ->
  frn_rp fn = ConsoleInv.devsw_read_val ->
  frn_dqv fn = (fun _ => DfracDiscarded) ->
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
  fileread_fs_env γf fn -∗
  ConsoleInv.console_inv (frn_cons fn) -∗
  (* THE FD SIDE's resource half: the caller's own fragment -- open,
     READABLE, an inode descriptor at inum [i] *)
  fd_st (pv_fdg (us_V U)) fd (FdOpen true wb (FdInode i)) -∗
  (* ---- THE AU SIDE (the one addition to the landed premise list) ---- *)
  EXTRA -∗
  wp_next true pj (fun (CID : CpuId) =>
    (* THE IMAGE MOVES, AND THE MOVE IS A WINDOW AT ARGUMENT 1 -- the landed
       contract's own post, restored.  The frame used to state the image
       existentially ([M' : gmap Z (bv 8)]) on the grounds that a
       receipt-carrying caller has no use for the destination BYTES.  That
       is still true of the bytes and is why [bs] stays a bare function;
       it is NOT true of the LENGTH, which the kernel contracts now pin to
       the answer, so the window comes back and brings the exact count with
       it. *)
    ∀ (mf : regfile) (r : mword 64) (P' : uptd) (d : nat) (bs : nat -> bv 8),
      ⌜callee_saved m mf⌝ -∗
      ⌜uptd_ext_sz (pv_sz (us_V U)) (pv_upt (us_V U)) P'⌝ -∗
      ⌜(Z.of_nat d <= Z.max 0 (sys_rw_count v2))%Z⌝ -∗
      (* ...AND A NON-NEGATIVE ANSWER IS EXACTLY THE COUNT WRITTEN
         ([SpecSysRead]'s conjunct, relayed).  Joined with [ARMS] at
         [read_arms] this is [ard_ret_tie_pos] / [ard_ret_tie_exact_file]:
         the window's length is the count the OBSERVED abstract row had to
         give.  The -1 answer keeps only the bound, because readi discards
         its running count when a copyout faults after earlier blocks
         landed -- and on that arm [read_post_fail]'s right disjunct is
         what still reports the observation. *)
      ⌜r = (mword_of_int (Z.of_nat d) : mword 64)
       \/ r = (mword_of_int (-1) : mword 64)⌝ -∗
      ⌜mf !!! Regidx (mword_of_int 10 : mword 5) = r⌝ -∗
      sie_cap_gpr KT1 mf K b pj -∗
      cpu_own 0%nat eb pj b lks -∗
      pc_is ret_tgt -∗
      proc_priv γf pj pidv
        (upd_usM (us_upt U P') (umem_wr (us_M U) v1 d bs)) -∗
      kalloc_env fsc_kalloc None -∗
      fileread_fs_out fn -∗
      (* the descriptor's state does not move: a read advances the
         offset, never the fd table *)
      fd_st (pv_fdg (us_V U)) fd (FdOpen true wb (FdInode i)) -∗
      (* the armed post on the returned a0 (implies [sys_read_ret]) *)
      ARMS r -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

(* THE AU FORM.  The abstract state is read at the LIVE Γ,
   [fs_gamma_L fsc_fs] -- the gname tie to [ftop_body]'s authority is
   definitional ([FsAbs.ftop_gamma_top]).  The count is the syscall's own
   argument reading ([sys_rw_count v2] -- the whole int range; the fork's
   sign guard is what the fail arm's first disjunct answers), so the
   caller's receipts speak about the count IT passed. *)
Definition wp_sys_read_au_body
    `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
      !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
    (γf : gname)
    (γs : list gname) (j : nat) (γlp : gname)
    (fn : fread_names)
    (pidv : mword 32) (U : ustate)
    (v v1 v2 : mword 64)
    (m : regfile) (K : nat) (eb : bool) (b : bool) (lks : gset string)
    (fd : nat) (fv : mword 64) (wb : bool) (i : Z)
    (Φr : aview -> nat -> anode -> iProp Σ) :=
  let Γfs := fs_gamma_L fsc_fs in
  let n := sys_rw_count v2 in
  wp_sys_read_au_frame γf γs j γlp fn pidv U v v1 v2 m K eb b lks
    fd fv wb i
    (aread_commit Γfs ∅ i Φr)
    (read_arms Γfs i n Φr).

(* THE STABLE COROLLARY'S STATEMENT (header: THE STABLE COROLLARY; its
   derivation is the sealer's, expected from the AU form + the agreement
   seed [aread_commit_pinned_self], never as a second walk).  The client
   presents the file's own [nview] share at its expected value for the
   duration and a NON-NEGATIVE count -- its own argument, so the premise
   is free -- and every arm answers at that value with the receipt
   fired.  Deliberately limited, and the limit is the header's: the
   share is refuted against today's whole-element payload custody, so
   the form is vacuous until the tree layer's exclusivity fact (or an
   era-fragment-style lend) exists -- but unlike write's it needs no
   re-cut then: a read retags nothing, so the same statement becomes
   non-vacuous as-is. *)
Definition wp_sys_read_au_stable_body
    `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
      !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
    (γf : gname)
    (γs : list gname) (j : nat) (γlp : gname)
    (fn : fread_names)
    (pidv : mword 32) (U : ustate)
    (v v1 v2 : mword 64)
    (m : regfile) (K : nat) (eb : bool) (b : bool) (lks : gset string)
    (fd : nat) (fv : mword 64) (wb : bool) (i : Z)
    (q : Qp) (bs0 : list (bv 8)) (nl : nat)
    (Φr : aview -> nat -> anode -> iProp Σ) :=
  let Γfs := fs_gamma_L fsc_fs in
  let n := sys_rw_count v2 in
  0 <= sys_rw_count v2 ->
  wp_sys_read_au_frame γf γs j γlp fn pidv U v v1 v2 m K eb b lks
    fd fv wb i
    (nview Γfs q i (MkAnode (AFile bs0) nl)
     ∗ aread_commit Γfs ∅ i Φr)%I
    (read_stable_arms Γfs i n q bs0 nl Φr).

(* ===================================================================== *)
(*  4.  THE SEAL                                                          *)
(* ===================================================================== *)

Module Type SYSREAD_AU.
  Parameter wp_sys_read_au :
    forall `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
             !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
      (γf : gname)
      (γs : list gname) (j : nat) (γlp : gname)
      (fn : fread_names)
      (pidv : mword 32) (U : ustate)
      (v v1 v2 : mword 64)
      (m : regfile) (K : nat) (eb : bool) (b : bool) (lks : gset string)
      (fd : nat) (fv : mword 64) (wb : bool) (i : Z)
      (Φr : aview -> nat -> anode -> iProp Σ),
      wp_sys_read_au_body γf γs j γlp fn pidv U v v1 v2 m K eb b lks
        fd fv wb i Φr.

  (* owed as a DERIVATION from [wp_sys_read_au] + the agreement seed
     ([aread_commit_pinned_self]), never as a second walk; the stable
     body's [0 <= n] premise is what makes every arm's receipt fire
     (header: no escape arm, and why) *)
  Parameter wp_sys_read_au_stable :
    forall `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
             !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
      (γf : gname)
      (γs : list gname) (j : nat) (γlp : gname)
      (fn : fread_names)
      (pidv : mword 32) (U : ustate)
      (v v1 v2 : mword 64)
      (m : regfile) (K : nat) (eb : bool) (b : bool) (lks : gset string)
      (fd : nat) (fv : mword 64) (wb : bool) (i : Z)
      (q : Qp) (bs0 : list (bv 8)) (nl : nat)
      (Φr : aview -> nat -> anode -> iProp Σ),
      wp_sys_read_au_stable_body γf γs j γlp fn pidv U v v1 v2 m K eb b
        lks fd fv wb i q bs0 nl Φr.
End SYSREAD_AU.
