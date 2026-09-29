(* SysWriteDefs.v -- THE WRITE DELTA'S PURE VOCABULARY: the chunk
   constant, the per-chunk side conditions, the chained reading and the
   instant-count bound.  A LEAF: pure Coq, no [iProp], no [Module Type],
   no contract.

   WHY THE WRITE'S CONSTANTS LIVE IN A LEAF OF THEIR OWN.  Both the
   INVARIANT layer ([FsAbsWriteFire.v], the fire point) and the CONTRACT
   ([SpecFilewrite.v]) need [FW_MAX] and [wchunks], and a spec file may not
   own a definition the invariant layer needs
   (design/code-organization.md), so they sit here, below both.  [FW_MAX]'s
   derivation from the log's budget stays in [SpecFilewrite.fw_max_value],
   where [MAXOPBLOCKS] is in scope.

   sys_write itself has ONE contract, [SpecSysWrite.SYSWRITE], whose arms
   are keyed on the descriptor's state; the abstract commits it is stated
   over are [FsAbsWriteFire]'s, at the γtop AUTHORITY (an [FsAbs.astate]-
   shaped commit is not dischargeable in either phase -- that file's header
   is the argument).

   Design of record: claude-notes/design/fs-syscall-specs.md sections 0-4
   (the sys_write paragraph of section 4). *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list functions bitvector.definitions.
(* the proofmode, for ssreflect's [rewrite /x] -- the pure proofs below are
   written in it, and it is not transitive *)
From iris.proofmode Require Import proofmode.
From xv6iris Require Import StepIndex.
Require Import SailStdpp.Base SailStdpp.Values SailStdpp.MachineWord.
Require Import BioDefs.        (* [BSIZE]                                   *)
Require Import InodeInv.       (* [MAXFILE]                                 *)
Require Import FsAbsDefs.          (* the abstract state (lane A, landed)       *)
Require Import UserPtTree.         (* [uptd] / [uva_rmapped]: the write's
                                      failure reason, below                   *)
Require Import ProcPtOwn.          (* [uptd_ext_sz]: the round's table grew    *)

Local Open Scope Z_scope.

(* ===================================================================== *)
(*  0.  THE CHUNK SIZE                                                    *)
(* ===================================================================== *)

(* THE CHUNK SIZE, as the two [lui]/[addi] pairs at filewrite+0x42..+0x4e
   materialise it: ((MAXOPBLOCKS-1-1-2)/2)*BSIZE with MAXOPBLOCKS = 10 and
   BSIZE = 1024.  The equation with the log's budget is
   [SpecFilewrite.fw_max_value]; this file only needs the value. *)
Definition FW_MAX : Z := 3072.

(* ===================================================================== *)
(*  1.  THE DELTA AND ITS ALGEBRA (PURE)                                  *)
(* ===================================================================== *)

Require Export FsAbsDelta.   (* the splice algebra, [delta_write] + its row algebra (hoisted 2026-09-04) *)

(* THE SIDE CONDITIONS a fired chunk's caller may assume at its instant,
   each realized by a writei guard (header, prover item 5): the row is a
   file, the chunk wrote something, the start is inside the current bytes
   (writei refuses past-size starts, so the splice never leaves a hole),
   and the end is inside the file-size cap. *)
Definition wri_pre (av : aview) (i : Z) (off : nat)
    (bs bs0 : list (bv 8)) (nl : nat) : Prop :=
  (* on the COUNT ([FsAbsDefs.arow_at], E2-V2): a write through the fd of
     an unlinked file finds no row, and moves none *)
  arow_at av i (MkAnode (AFile bs0) nl)
  /\ (0 < length bs)%nat
  /\ (off <= length bs0)%nat
  /\ (off + length bs <= MAXFILE * BSIZE)%nat.

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

(* ---------------------------------------------------------------------
   1c.  THE CHUNK AT ONE NODE -- RELAY 3 (lane WRITE-RELAY)

   [wchunks n] says HOW MANY instants can fire; [wchunk_at n k] says how
   BIG the one at node [k] is.  filewrite's loop computes it in two
   instructions ([subw a5,s5,s4] then the [FW_MAX] cap), and every chunk
   that reaches node [k] was FULL -- a short one breaks the loop -- so the
   loop's running offset at node [k] is [FW_MAX * k] and the count it
   passes writei is [min (n - FW_MAX*k) FW_MAX].

   WHY THE NODE NEEDS IT.  [SpecCopyin.ubytes_at M ua bs] is a [∀] over
   [bs]'s OWN indices and is therefore PREFIX-CLOSED: it says "these bytes
   are a run of the caller's image at this base", never "this is the whole
   chunk".  So a client that knows which bytes it asked to have written
   cannot identify the fire's [bs] with them from the content tie alone --
   it needs the LENGTH, and the length is the one thing the kernel holds
   for free at the fire (it is the number it passed writei).  With the two
   together the identification is [ubytes_at_inj]'s one line.  (F-WRITE
   finding 2; design/app-file.md section 3, RELAY 3.) *)
Definition wchunk_at (n : Z) (k : nat) : Z :=
  Z.min (n - FW_MAX * Z.of_nat k) FW_MAX.

(* THE LOOP'S OWN CHUNK IS THIS ONE.  [ProofFilewrite.fw_test] hands the
   body [0 < c <= FW_MAX], [c <= n - t] and -- the clause lane E2-W added
   for exactly this kind of reasoning -- [c = n - t \/ c = FW_MAX].  With
   the loop's tie [t = FW_MAX * k] that pins [c] outright. *)
Lemma wchunk_at_pick (n c t : Z) (k : nat) :
  0 <= t -> t < n -> t = FW_MAX * Z.of_nat k ->
  0 < c -> c <= FW_MAX -> c <= n - t ->
  (c = n - t \/ c = FW_MAX) ->
  c = wchunk_at n k.
Proof.
  intros Ht Htn Htie Hc0 Hcm Hcr Hpick.
  rewrite /wchunk_at -Htie. destruct Hpick as [-> | ->]; lia.
Qed.

Lemma wchunk_at_pos (n : Z) (k : nat) :
  FW_MAX * Z.of_nat k < n -> 0 < wchunk_at n k.
Proof. intro H. rewrite /wchunk_at /FW_MAX in H |- *. lia. Qed.

Lemma wchunk_at_le (n : Z) (k : nat) : wchunk_at n k <= FW_MAX.
Proof. rewrite /wchunk_at. lia. Qed.

(* ONE WRITE OF AT MOST [FW_MAX] BYTES IS ONE NODE (lane SKELETON, finding
   5).  echo's four chunks are bytes long and each goes out in a [write] of
   its own, so its chain is exactly one node -- a full arm beside a partial
   arm -- and that node's chunk IS the whole request. *)
Lemma wchunks_one (n : Z) : 0 < n -> n <= FW_MAX -> wchunks n = 1%nat.
Proof.
  intros H1 H2. rewrite /wchunks /FW_MAX in H2 |- *.
  assert (Hd : (n + 3072 - 1) / 3072 = 1).
  { assert (Hlo : 1 <= (n + 3072 - 1) / 3072)
      by (apply Z.div_le_lower_bound; lia).
    assert (Hhi : (n + 3072 - 1) / 3072 < 2)
      by (apply Z.div_lt_upper_bound; lia).
    lia. }
  rewrite Hd. reflexivity.
Qed.

Lemma wchunk_at_0 (n : Z) : n <= FW_MAX -> wchunk_at n 0 = n.
Proof. intro H. rewrite /wchunk_at /=. lia. Qed.

(* ===================================================================== *)
(*  1d.  WHY A WRITE LEAVES BYTES NOBODY NAMED -- THE COPYIN'S REASON     *)
(*       (lane WRITE-RELAY-2; RELAY 4's carrying half)                    *)
(* ===================================================================== *)

(* writei's DISTURBED TAIL exists for exactly one reason: [either_copyin]
   gave up part-way on the USER arm, having already written a prefix of the
   chunk into the block it had [bread] (kernel defect D1's fix commits that
   block rather than stranding it).  copyin's only failing test is
   walkaddr's, taken again after vmfault declined, so the byte it died on is
   an address of the SOURCE run the process's page table does not map for
   READING -- [uva_rmapped] (present and V&U) and NOT [uva_wmapped]: there
   is no PTE_R re-walk on this side ([SpecCopyin.copyin_read]'s -1 arm
   states it, and [SpecEitherCopyin.either_copyin_post] relays it).

   THE EXACT TWIN of [SysReadDefs.rd_fail_why], one test weaker, and it is
   read the same way: STATED AT THE ENTRY DESCRIPTOR [P], which is the
   WEAKER and therefore usable form -- the round's table only GREW
   ([uptd_ext_sz]) and a byte the entry table can read the grown one can
   read too ([UserPtTree.uva_rmapped_mono]), so [wr_nrmapped_entry] below is
   how a proof brings the round's verdict back to the entry.

   WHICH byte is EXISTENTIAL and the bound is the REQUEST: copyin walks
   whole pages, so the failing round may have copied a prefix of its own
   chunk first, and all the caller is promised is that the bad byte is
   inside the run it asked for.  That is enough: a caller whose whole source
   run is readable-mapped refutes the arm outright ([wr_fail_why_refute]),
   which is what [UkRunSys.usrc_ok]'s second conjunct buys the U tier.

   KEYED BY THE 64-BIT VA, like every image equation in the tower, so this
   promises nothing about [src + n] not wrapping. *)
Definition wr_fail_why (P : uptd) (src : mword 64) (n : nat) : Prop :=
  exists d : nat, (d < n)%nat
    /\ ~ uva_rmapped P (uint (add_vec_int src (Z.of_nat d))).

(* the round's verdict, brought back to the ENTRY table *)
Lemma wr_nrmapped_entry (szv : mword 64) (P Pc : uptd) (va : Z) :
  uptd_ext_sz szv P Pc -> ~ uva_rmapped Pc va -> ~ uva_rmapped P va.
Proof.
  intros Hext Hn Hc. apply Hn.
  destruct (uptd_ext_sz_ext szv P Pc Hext) as (_ & _ & Hsub).
  exact (uva_rmapped_mono P Pc va Hsub Hc).
Qed.

(* ...and the same for the whole reason, at a request the round's count sits
   inside *)
Lemma wr_fail_why_entry (szv : mword 64) (P Pc : uptd) (src : mword 64)
    (n : nat) :
  uptd_ext_sz szv P Pc -> wr_fail_why Pc src n -> wr_fail_why P src n.
Proof.
  intros Hext (d & Hd & Hn). exists d. split; [exact Hd |].
  exact (wr_nrmapped_entry szv P Pc _ Hext Hn).
Qed.

(* the reason survives a WIDER request: a caller that asked for more still
   has the bad byte inside its run *)
Lemma wr_fail_why_mono (P : uptd) (src : mword 64) (n n' : nat) :
  (n <= n')%nat -> wr_fail_why P src n -> wr_fail_why P src n'.
Proof. intros Hle (d & Hd & Hn). exists d. split; [lia | exact Hn]. Qed.

(* THE REASON, MOVED TO THE WHOLE RUN'S BASE: a chunk's failing byte is a
   byte of the request the chunk sits inside.  This is what filewrite's fold
   does with what writei answered -- the chunk's base is [ua + FW_MAX*k] and
   the node states the reason at [ua].  No no-wrap side condition, because
   [add_vec_int] composes modulo 2^64
   ([UserPtTree.add_vec_int_nat_assoc]). *)
Lemma wr_fail_why_shift (P : uptd) (src : mword 64) (b c n : nat) :
  (b + c <= n)%nat ->
  wr_fail_why P (add_vec_int src (Z.of_nat b)) c -> wr_fail_why P src n.
Proof.
  intros Hle (d & Hd & Hn). exists (b + d)%nat. split; [lia |].
  rewrite -add_vec_int_nat_assoc. exact Hn.
Qed.

(* THE REFUTATION, and it is one line: a caller whose whole source run is
   readable-mapped in the table the reason is stated at has no copyin fault
   to answer for.  The write's twin of [SysReadDefs.rd_fail_why_refute]. *)
Lemma wr_fail_why_refute (P : uptd) (src : mword 64) (k n : nat) :
  (n <= k)%nat ->
  (forall j : nat, (j < k)%nat ->
     uva_rmapped P (uint (add_vec_int src (Z.of_nat j)))) ->
  wr_fail_why P src n -> False.
Proof.
  intros Hnk Hmap (d & Hd & Hn). exact (Hn (Hmap d ltac:(lia))).
Qed.
