(* SpecSysReadAU.v -- THE READ OBSERVATION'S PURE VOCABULARY: the count a
   transfer answers, the slice it delivers, the readi bridges, and the
   observation's side conditions and return tie.  A LEAF: pure Coq, no
   [iProp], no [Module Type], no contract.

   WHY THE READ'S VOCABULARY LIVES IN A LEAF OF ITS OWN.  Both the
   INVARIANT layer ([FsAbsReadFire.v], the commit and its fire point) and
   the CONTRACT ([SpecFileread.v]) need [ard_count], [ard_pre] and
   [ard_ret_tie], and a spec file may not own a definition the invariant
   layer needs (design/code-organization.md), so they sit here, below both.
   [SpecSysWriteAU.v] is the write side's twin.

   sys_read has ONE contract, [SpecSysRead.SYSREAD], whose caller input and
   armed output are keyed on the descriptor's state; the observation commit
   it is stated over is [FsAbsReadFire.aread_commit_at], at the gtop
   AUTHORITY (an [FsAbs.astate]-shaped commit is not dischargeable -- that
   file's header is the argument).

   Design of record: claude-notes/design/fs-syscall-specs.md sections 0-4
   (the read row of section 4, and its "ONE CONTRACT PER SYSCALL"
   paragraph).

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

   WHAT "DELIVERED" DOES NOT MEAN: the read contract says NOTHING about
   the USER buffer's contents.  readi's user arm -- the one fileread takes
   -- promises only [uptd_ext] about the destination (SpecReadi's header;
   SpecFileread inherits the silence), so the slice is VOCABULARY tying
   the return count to the observed value, not a memory postcondition.
   A kernel-arm reader (kexec, dirlookup) that wants the bytes has
   readi's own contract.

   ==== ...BUT THE LENGTH IS SAID, AND IT IS THE ANSWER =================

   [SpecFileread] / [SpecSysRead] carry the exact-count conjunct

       r = mword_of_int (Z.of_nat d)  \/  r = mword_of_int (-1)

   beside the user-memory window it is about.  So the caller learns what
   "delivered" means for the DESTINATION, at the only granularity the
   kernel proves: HOW MANY bytes moved, never which.  Joined with the
   inode arm's receipt it is [ard_ret_tie_pos] (the -1 disjunct is refuted
   on an ok arm, so the window's length IS the answer, on every row) and
   [ard_ret_tie_exact_file] (on a file row the length is the ABSTRACT
   count -- the bytes the observed state had to give are exactly the bytes
   that landed).  The -1 arm keeps only the bound [d <= max 0 n] and that
   is the CODE's doing: readi overwrites its running [tot] with -1 when a
   copyout faults, discarding blocks it has already delivered, so a read
   really can return -1 with bytes in the buffer.

   ==== THE DIRECTORY ARM ===============================================

   A readable FD_INODE descriptor may name a DIRECTORY: xv6's open()
   maps T_DEVICE inodes to FD_DEVICE but keeps T_DIR under FD_INODE
   (ls reads directories through read()).  The landed fd-state fragment
   carries only the inum, so file-ness is NOT excludable by premise --
   unlike write, where the writable bit's [ity_shot] side condition
   ("a writable fd is not a directory", [SpecFileread.fileread_pay_carve]'s
   clause) does exactly that.  The observation therefore takes the WHOLE
   [anode] and the return tie is a match:

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
                    exact-count conjunct relayed by the contract pins [r]
                    to the window's length on this arm too, and
                    [ard_ret_tie_pos] is where the bound's existential
                    witness becomes [Z.of_nat d];
   - [ADev _ _]  -> folded into the bounds arm rather than REFUTED.  An
                    FD_INODE descriptor never names a device row, but
                    the client-visible tie "FdInode => the row reads
                    AFile or ADir" is a custody fact no landed lemma
                    exports; refuting ADev would charge the seal for it.

   The blanket the tie folds back into is [PipeInvDefs.pipe_rw_ret], which
   is what [SpecFileread.fileread_ret] is defined as -- named here rather
   than through the contract, because the contract sits ABOVE this leaf. *)
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
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import ProcAvail.
Require Import AppInv.          (* [appN]/[appE]: the application's namespace, the commit mask (app-instances.md round A) *)
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
   realized by the machine (header, prover items 1): the row is the
   authority's at [i] -- stated on the COUNT ([FsAbsDefs.arow_at], E2-V2):
   the fd's inode may have been unlinked while open, and then the view has
   no row for it and [a] is what the record reads as; the offset the call
   used respects [off_wf]; the row's bytes respect the size cap. *)
Definition ard_pre (av : aview) (i : Z) (off : nat) (a : anode) : Prop :=
  arow_at av i a
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
   ([SpecFileread.fileread_ret] IS [pipe_rw_ret]), so the inode arm's
   receipt refines the unified contract's unconditional return clause. *)
Lemma ard_ret_tie_ret (n : Z) (a : anode) (off : nat) (r : mword 64) :
  0 <= n -> ard_ret_tie n a off r -> pipe_rw_ret n r.
Proof.
  rewrite /ard_ret_tie /pipe_rw_ret.
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

(* [SpecFileread] / [SpecSysRead] carry the output conjunct -- a
   non-negative answer IS the number of bytes written,

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
