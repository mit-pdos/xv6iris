(* ProofFilewrite.v -- filewrite's own control flow and ghost steps.
   ============================= WIP, S3n ==============================

   STATUS: THE ARITHMETIC PREAMBLE ONLY.  [wp_filewrite_sconf] and the
   [FilewriteProof] functor are NOT WRITTEN, so [LinkFilewrite.v] does not
   exist and file.c stays 6/7.  Everything below compiles and is what the
   walk consumes at its call sites; S3o resumes at "THE RESUME POINT".

   Why the split: the whole-function walk is ~2500 lines of instruction-wise
   Iris in [ProofFileread.v]'s style (that file's single lemma is 2139 lines
   for FOUR arms and NO loop; filewrite adds a bottom-tested loop with a
   nine-component invariant).  The pure [nat]/[Z]/[Qp] obligations it needs
   are separable, and they are separated here for the same reason
   [ProofFileread.v] hoists its own [fr_av_*] / [fr_ret_*] block above the
   module: a [lia] cannot run at a call site, where the context holds a
   register file (durable-notes, "an [mword] merely in CONTEXT").

   S3n VERIFIED, BEFORE ANY OF THE WALK -- the five things that could have
   made this stage a sixth blocker, and did not:

   1. THE STACK CONSTANTS CLOSE, and [filewrite_stack] is EXACTLY TIGHT on
      writei.  [filewrite_stack = 12 + K_writei = 82], every call is made
      after the 12-slot push, so each callee needs [<= K - 12 = 70]:
      writei 70 (equality), pipewrite 64, consolewrite 62, end_op 58,
      ilock 44, begin_op 26, iunlock 26.  [SpecFilewrite]'s header claim
      ("its deepest callee is writei, the others are smaller") HOLDS, and
      the [fw_av_*] block below is the machine-checked form of it.
   2. THE BUDGET PREMISE IS UNIFORM IN [off].  S3m's headline number is
      [wi_cost_bmonly 1023 FW_MAX = 10]; what the loop actually needs is
      that bound at EVERY offset, since [f->off] is not block-aligned.
      [WriteiBudget.wi_cost_bmonly_fits] is already stated that way -- its
      only hypothesis is [n <= FW_MAX], with [off] universally quantified,
      because [wi_blocks_le4] bounds [off `mod` BSIZE] rather than [off].
      So every chunk filewrite can ask for is payable.  ([fw_budget_ok].)
   3. THE SHARE ALGEBRA COMPOSES.  SpecIlock v5 consumes
      [inode_shr_gen k s dev inum g] and returns [ic_deposit cn k
      (DepShr s dev inum g)]; SpecIunlock takes that deposit back and
      returns the arity-preserving [inode_shr k s dev inum].  Lending
      [s/2] therefore leaves [inode_shr_gen k (s/2) .. g] in hand and gets
      [inode_shr k (s/2) ..] back, which is exactly [fw_shr_regen]'s two
      arguments, and [Qp.div_2] rejoins them at [s].  ([fw_qp_halves].)
   4. writei's TWO UNOBVIOUS RESOURCE PREMISES ARE BOTH AVAILABLE.
      [p_pid pj] is not in [filewrite_fs_env] and does not need to be --
      filewrite writes from USER memory ([c.li s8,1] at +0x50), so it holds
      [proc_priv] and [ProcInv.proc_priv_pid] splits the pid quarter out,
      exactly as SpecWritei's own comment at the premise says.
      [dinode_at gi inum dn0] is not in the environment either; it arrives
      inside ilock's [ic_loaded] payload (fileread destructs it as "Hdnat"
      at ProofFileread.v:1741).
   5. end_op ACCEPTS A PARTIALLY SPENT RESERVATION.  [SpecEndOp] takes
      [log_op g u] for ANY [u] (its header says so at :30 and the premise is
      at :142), so the loop never has to prove that a chunk spent its whole
      begin_op grant -- writei promises spend-AT-MOST and the remainder is
      simply carried into end_op.

   S3n SURPRISE, and the one thing that will bite the walk mechanically:
   THERE ARE TWO CONSTANTS NAMED [FW_MAX] AND THIS FILE MUST IMPORT BOTH.
   [SpecFilewrite.FW_MAX : Z] (the chunk size as the [lui]/[addi] pairs
   materialise it) and [WriteiBudget.FW_MAX : nat] (the same 3072 as the
   budget lemmas' hypothesis) are DIFFERENT CONSTANTS AT DIFFERENT TYPES,
   and whichever file is [Require Import]ed second shadows the other.  Every
   occurrence below is written QUALIFIED for that reason, and [fw_max_bridge]
   is the one place the two are related.  An unqualified [FW_MAX] in the walk
   will typecheck in some goals and fail in others with a [nat]-vs-[Z]
   mismatch that reads like a coercion problem.

   THE RESUME POINT (S3o): the walk itself, in [ProofFileread.v]'s shape --
   dispatch (!writable pre-prologue -> -1; FD_PIPE; FD_DEVICE via [fw_devidx]
   and the assumed contract at the [c.jalr]; the +0x11e ELSE = [fw_panic]),
   then the FD_INODE loop.  Per iteration: begin_op -> ilock at [s/2] ->
   re-park ([ity_shot_agree] pins the type, [dir_ok_not_dir] makes dir_ok
   vacuous, S3i's two preservations close [inode_ok] 5/7) -> the COUNTED
   [wp_writei_sconf] at [ncount := MAXOPBLOCKS] with [fw_budget_ok] as the
   premise -> the [f->off] update ([off_checkout]/[off_checkin], fileread's
   choreography) -> iunlock -> [fw_shr_regen] -> end_op -> break/continue.
   The three join paths are one shape and are already [fw_tail]; the hoisted
   zero-trip test at +0x32 skips the loop AND the five spills, which is why
   [fw_epi] takes those slots as arbitrary words. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list functions bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.Values.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvLang RiscvPtsto RiscvExtras.
Require Import FsCrash.
Require Import InodeInv.
Require Import LogInv.
Require Import PipeInvDefs.
Require Import SpecBeginOp SpecEndOp.
Require Import SpecIlock SpecIunlock.
Require Import SpecWritei.
Require Import WriteiBudget.
Require Import SpecPipewrite.
Require Import SpecConsolewrite.
Require Import SpecFilewrite.
From Kernel Require KernelSyms.

Local Open Scope Z_scope.

(* ---------------------------------------------------------------------- *)
(*  THE STACK BOUNDS, one per callee.                                      *)
(*                                                                         *)
(*  All seven calls are made INSIDE the frame, i.e. with [K - 12] slots     *)
(*  left, and [filewrite_stack = 12 + K_writei] is what the contract        *)
(*  demands of its caller.  Kept [mword]-free over [nat]: the [lia] that    *)
(*  discharges them cannot run at the call site (fileread's [fr_av_*]).     *)
(*  The writei line is an EQUALITY, not slack -- see the header's point 1.  *)
(* ---------------------------------------------------------------------- *)

Lemma fw_K12 (K : nat) : (filewrite_stack <= K)%nat -> (12 <= K)%nat.
Proof. unfold filewrite_stack, K_writei. lia. Qed.

Lemma fw_av_writei (K : nat) :
  (filewrite_stack <= K)%nat -> (K_writei <= K - 12)%nat.
Proof. unfold filewrite_stack. lia. Qed.

Lemma fw_av_pipe (K : nat) :
  (filewrite_stack <= K)%nat -> (pipewrite_stack <= K - 12)%nat.
Proof. unfold filewrite_stack, K_writei, pipewrite_stack. lia. Qed.

Lemma fw_av_cons (K : nat) :
  (filewrite_stack <= K)%nat -> (consolewrite_stack <= K - 12)%nat.
Proof. unfold filewrite_stack, K_writei, consolewrite_stack. lia. Qed.

Lemma fw_av_ilock (K : nat) :
  (filewrite_stack <= K)%nat -> (K_ilock <= K - 12)%nat.
Proof. unfold filewrite_stack, K_writei, K_ilock. lia. Qed.

Lemma fw_av_iunlock (K : nat) :
  (filewrite_stack <= K)%nat -> (K_iunlock <= K - 12)%nat.
Proof. unfold filewrite_stack, K_writei, K_iunlock. lia. Qed.

Lemma fw_av_begin_op (K : nat) :
  (filewrite_stack <= K)%nat -> (K_begin_op <= K - 12)%nat.
Proof. unfold filewrite_stack, K_writei, K_begin_op. lia. Qed.

Lemma fw_av_end_op (K : nat) :
  (filewrite_stack <= K)%nat -> (K_end_op <= K - 12)%nat.
Proof. unfold filewrite_stack, K_writei, K_end_op. lia. Qed.

(* The frame trade-back, at the arity the epilogue wants. *)
Lemma fw_K_back (K : nat) :
  (filewrite_stack <= K)%nat -> ((K - 12) + 12)%nat = K.
Proof. unfold filewrite_stack, K_writei. lia. Qed.

(* ---------------------------------------------------------------------- *)
(*  THE BUDGET.                                                            *)
(*                                                                         *)
(*  [begin_op] mints [log_op g MAXOPBLOCKS] and the chunk's premise is      *)
(*  [wi_cost_bmonly off n1 <= ncount] at [ncount := MAXOPBLOCKS].  This is  *)
(*  the whole of S3j/S3l/S3m's ruling, applied: it holds for EVERY offset,  *)
(*  not just the aligned ones (header point 2).                            *)
(* ---------------------------------------------------------------------- *)

(* The two [FW_MAX]s, related once.  See the header's SURPRISE. *)
Lemma fw_max_bridge : Z.of_nat WriteiBudget.FW_MAX = SpecFilewrite.FW_MAX.
Proof. vm_compute. reflexivity. Qed.

(* ...and the chunk bound in the shape the WALK has it: the code compares
   [n - i] against the 3072 in s7 with a [bge], so what is in hand at the
   call is a [Z] fact about the register, while the budget lemma wants a
   [nat] one about writei's argument. *)
Lemma fw_budget_ok (off n1 : nat) :
  (Z.of_nat n1 <= SpecFilewrite.FW_MAX) ->
  (wi_cost_bmonly off n1 <= MAXOPBLOCKS)%nat.
Proof.
  intro Hn. apply WriteiBudget.wi_cost_bmonly_fits.
  rewrite <- fw_max_bridge in Hn. lia.
Qed.

(* The empty-range arm is NOT waved through: S3m's trap check says
   [wi_cost_bmonly 0 0 = 2 > wi_cost 0 0 = 1], so the premise is strictly
   harder there.  It still fits, with eight to spare. *)
Lemma fw_budget_ok_empty (off : nat) :
  (wi_cost_bmonly off 0 <= MAXOPBLOCKS)%nat.
Proof.
  apply fw_budget_ok. unfold SpecFilewrite.FW_MAX. cbn. lia.
Qed.

(* ---------------------------------------------------------------------- *)
(*  THE CHUNK, as the loop test at +0xcc..+0xd8 computes it.               *)
(*                                                                         *)
(*  [subw a5,s5,s4] gives [n - i]; [bge s7,a5] falls to the body when       *)
(*  [3072 >= n - i] and otherwise [c.mv s3,s9] caps it at 3072.  So the     *)
(*  chunk is [min (n - i) FW_MAX], and BOTH arms need it positive (the      *)
(*  loop is entered only from a state with [i < n]) and at most FW_MAX      *)
(*  (writei's budget premise).                                             *)
(* ---------------------------------------------------------------------- *)

(* the [bge] falls: the chunk is the whole remainder *)
Lemma fw_chunk_rem (n i : Z) :
  (0 <= i < n) -> (n - i <= SpecFilewrite.FW_MAX) ->
  (0 < n - i <= SpecFilewrite.FW_MAX).
Proof. lia. Qed.

(* the [bge] is taken: the chunk is the cap itself *)
Lemma fw_chunk_cap (n i : Z) :
  (0 <= i < n) -> (SpecFilewrite.FW_MAX < n - i) ->
  (0 < SpecFilewrite.FW_MAX <= SpecFilewrite.FW_MAX).
Proof. unfold SpecFilewrite.FW_MAX. lia. Qed.

(* ...and either way the chunk is in int range, which is what the
   [sext.w s3,s3] at +0x82 needs ([fw_sextw_moi]'s hypothesis). *)
Lemma fw_chunk_lt31 (c : Z) :
  (0 < c <= SpecFilewrite.FW_MAX) -> (0 <= c < 2 ^ 31).
Proof. unfold SpecFilewrite.FW_MAX. lia. Qed.

(* THE DECREASE.  [addw s4,s4,s1] at +0xc4 advances [i] by the count writei
   returned, and the loop is left when [i >= n].  The fuel is [n - i] and
   this is its step: a continuing iteration returned the FULL chunk (the
   [bne s3,s1] at +0xc0 breaks otherwise), and a full chunk is positive. *)
Lemma fw_i_advance (n i c : Z) :
  (0 <= i < n) -> (0 < c <= n - i) -> (0 <= i + c <= n) /\ (n - (i + c) < n - i).
Proof. lia. Qed.

(* the loop-carried [i] stays an int, so [fw_bge_moi] / [fw_neq_moi] apply *)
Lemma fw_i_lt31 (n i : Z) : (0 <= i <= n) -> (0 <= n < 2 ^ 31) -> (0 <= i < 2 ^ 31).
Proof. lia. Qed.

(* ---------------------------------------------------------------------- *)
(*  THE OFFSET.                                                            *)
(*                                                                         *)
(*  [f->off] is read at +0x92 and written back at +0xb0 with [c.addw].      *)
(*  [SpecFilewrite.fw_off_advance] is the [off_wf] step and                 *)
(*  [SpecFilewrite.fw_chunk_joint] is writei's joint premise; both are      *)
(*  CLOSED FACTS there.  What the walk additionally needs is the [Z] form   *)
(*  of the joint premise, since the register holds [off] as an int.        *)
(* ---------------------------------------------------------------------- *)

Lemma fw_off_lt31 (off : nat) :
  (Z.of_nat off <= Z.of_nat MAXFILE * Z.of_nat BSIZE) -> (0 <= Z.of_nat off < 2 ^ 31).
Proof. unfold MAXFILE, BSIZE, NDIRECT. cbn. lia. Qed.

(* ---------------------------------------------------------------------- *)
(*  THE SHARE.                                                             *)
(*                                                                         *)
(*  [fw_shr_gen_halve] lends ilock [s/2] and keeps [s/2]; [fw_shr_regen]    *)
(*  rejoins the kept half with the [inode_shr] iunlock returns, at the      *)
(*  KEPT half's generation.  This is the [Qp] step that closes the loop     *)
(*  invariant back at [fwn_s fn] (header point 3).                         *)
(* ---------------------------------------------------------------------- *)

Lemma fw_qp_halves (s : Qp) : (s / 2 + s / 2)%Qp = s.
Proof. apply Qp.div_2. Qed.

(* ---------------------------------------------------------------------- *)
(*  THE RETURN VALUE.                                                      *)
(*                                                                         *)
(*  [fw_tail]'s postcondition is a DISJUNCTION -- [-1], or [i = n] and the  *)
(*  value is [n] -- and the contract wants [filewrite_ret n r].  The pipe   *)
(*  and device arms produce [filewrite_ret] verbatim (it IS               *)
(*  [pipe_rw_ret]); this is the inode arm's join.                          *)
(* ---------------------------------------------------------------------- *)

Lemma fw_ret_of_tail (n nz iz : Z) (rv : mword 64) :
  (0 <= n) -> nz = n ->
  (rv = (mword_of_int (-1) : mword 64)
   \/ (iz = nz /\ rv = (mword_of_int nz : mword 64))) ->
  filewrite_ret n rv.
Proof.
  intros Hn Hnz [Hm1 | [_ Hall]]; subst.
  - apply filewrite_ret_m1.
  - apply filewrite_ret_all. exact Hn.
Qed.

(* the device arm's callee promises [-1 <= r <= n] (SpecConsolewrite's
   deliberately weak bound); that is inside [filewrite_ret]. *)
Lemma fw_ret_of_dev (n r : Z) (rv : mword 64) :
  (0 <= n) -> (-1 <= r <= n) -> rv = (mword_of_int r : mword 64) ->
  filewrite_ret n rv.
Proof.
  intros Hn Hr Hrv. subst rv.
  destruct (Z.eq_dec r (-1)) as [He | Hne].
  - subst r. apply filewrite_ret_m1.
  - right. exists r. split; [reflexivity | lia].
Qed.

(* THE ZERO-TRIP EXIT.  [bge x0,a2] at +0x32 is taken when [n <= 0]; with
   the contract's [0 <= n] that forces [n = 0], and the tail then joins at
   [i = 0 = n] and returns 0.  The five spills never happened, which is
   what [fw_epi]'s arbitrary slots are for. *)
Lemma fw_zero_trip (n : Z) : (0 <= n) -> (n <= 0) -> n = 0.
Proof. lia. Qed.
