(* ProofFilewrite.v -- filewrite's own control flow and ghost steps.
   ============================= WIP, S3p ==============================

   STATUS: THE ARITHMETIC PREAMBLE ONLY.  [wp_filewrite_sconf] and the
   [FilewriteProof] functor are NOT WRITTEN, so [LinkFilewrite.v] does not
   exist and file.c stays 6/7.  Everything below compiles and is what the
   walk consumes at its call sites.

   =====================================================================
   S3p: BLOCKER SIX IS REPAIRED.  THE WALK HAS NOTHING OWED IN FRONT OF IT.
   =====================================================================

   S3o stopped at ONE premise of ONE call -- writei's, at +0xa0 -- and S3p
   fixed the contract.  [SpecWritei.v] now carries [SpecReadi.v]'s shape
   verbatim: the pid fraction is the KERNEL arm's and rides INSIDE the
   [if user] bracket, in the precondition and the postcondition of both
   [wp_writei_sconf_body] and [wp_writei_gen_body].  So the walk, standing
   at +0xa0 holding [proc_priv γf pj pidv V] and nothing else, satisfies the
   source premise EXACTLY -- see [fw_writei_src] below, which is that
   discharge, machine-checked, at the [user = true] the decode forces.
   Inside writei the quarter is borrowed out of [proc_priv] by
   [ProofWritei.wi_src_pid] and closed again around each of bmap / bread /
   brelse / iupdate; [either_copyin] always sees the block whole.  Nothing
   above writei moved -- the new premise is strictly weaker -- so the
   [Print Assumptions] cones of Writei and Dirlink are unchanged.

   WHAT THE STOP WAS, kept because the lesson is the durable part.  S3n
   cleared this call by reading SpecWritei's premise COMMENT ("on the user
   arm this is proc_priv's own quarter"), which was the stale sentence
   [SpecReadi.v]:255-263 had already refuted in terms.  The accessor's TYPE
   refutes it in one line: [ProcInv.proc_priv_pid] is a BORROW
   ([proc_priv -∗ p_pid ↦₄{1/4} ∗ (p_pid ↦₄{1/4} -∗ proc_priv)],
   ProcInv.v:892), so it consumes the block; and the cell totals one, with
   [ProcInv.proc_priv_core] holding a half and [SchedCtx.proc_pub] the
   other behind [p->lock], so there was no third fragment to find.  A
   premise justified by a comment is not cleared.  Clear it against a
   signature, a lemma, or a [vm_compute].

   WHAT IS *NOT* BLOCKED.  S3o re-checked every other premise of every other
   call by hand against what the walk holds at each instruction, and the pid
   pair was the ONLY unsatisfiable one.  The four other loop callees are
   clear because none of them wants [proc_priv] at all -- [SpecBeginOp],
   [SpecIlock], [SpecIunlock] and [SpecEndOp] each take the bare
   [p_pid pj ↦₄{dq} pidv] at a universally quantified [dq], which the
   accessor supplies (lend before the [jal], close the wand the instant it
   returns -- fileread's discipline at ProofFileread.v:1685/1712).  In
   particular:

     - writei's eighteen numeric/pure premises all close: (2) by
       [fw_budget_ok], (13) by [SpecFilewrite.fw_chunk_joint], (14) by
       [fw_size_lt31], (8)(9)(10)(11)(12) are conjuncts 3,4,1,6,2 of the
       [InodeLock.inode_ok] ilock hands out inside [ic_loaded], and
       (3)-(7),(15),(16) are [filewrite_fs_env]'s own pure fields;
     - every writei RESOURCE other than the pid pair is in hand:
       [i_dev]/[i_inum] at [1/2] and [inode_meta]/[inode_map]/
       [inode_blocks]/[dinode_at] come out of ilock's [ic_loaded]
       ([dn0 := dn]), the three superblock cells + [bitmap_res] +
       [ireg_inv] + [bslots _ 3] out of the environment, and
       [log_op γ MAXOPBLOCKS] out of begin_op;
     - THE RE-PARK CLOSES.  [fw_inode_ok_rebuild] below assembles
       [inode_ok] from writei's post verbatim -- conjuncts 5 and 7 are
       S3i's two preservations, whose antecedents are the SAME conjuncts of
       the [inode_ok] that came in -- and [fw_dir_ok_wi] makes [dir_ok]
       vacuous from [ity_shot_agree] plus [fw_wbool_of_fall];
     - iunlock's [ity_shot g (di_type dn')] is ilock's own witness
       unchanged, because [fw_wi_type] says writei never moves [di_type];
     - the share algebra, the stack constants, the offset choreography and
       the two [FW_MAX]s are S3n's five clearances and stand.

   THE REPAIR, AS LANDED (S3p).  [SpecReadi.v]:244-267 was the template and
   it transferred without surprise: the pid fraction moved into the KERNEL
   arm of the [if user], in the precondition AND the postcondition, of BOTH
   [wp_writei_sconf_body] and [wp_writei_gen_body].  Inside [ProofWritei.v]
   the borrow is ONE lemma over a [user]-indexed dfrac,

       Definition wi_q (user : bool) (dq : dfrac) : dfrac :=
         if user then DfracOwn (1/4) else dq.
       Lemma wi_src_pid … : <the bracket> -∗
         p_pid (proc_addr j) ↦₄{wi_q user dq} pidv ∗
         (p_pid (proc_addr j) ↦₄{wi_q user dq} pidv -∗ <the bracket>).

   -- which is cheaper than the sized version of this note predicted, because
   every fraction-taking callee quantifies its [dq], so ONE accessor serves
   both arms and NO call site case-splits on [user].  It is opened just
   before each of bmap / bread / the two brelses / iupdate and closed the
   instant each returns; [either_copyin] therefore always sees the bracket
   whole, and the two [iAssert]s that split the source around the copy grew
   the fraction into their kernel arm rather than case-splitting.
   Downstream, ONE consumer moved -- [ProofDirlink.v]:2042 is [user = false]
   and just [iCombine]s its two arguments across the call.  Nothing above
   writei changed, because the new premise is strictly WEAKER, and the
   [Print Assumptions] cones of Writei and Dirlink are byte-identical.
   file-table.md's OWED note is now DONE.

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
   4. **HALF OF THIS WAS REFUTED AT S3o AND REPAIRED AT S3p.**  The half
      that always HELD: [dinode_at gi inum dn0] is not in the environment
      and does not need to be; it arrives inside ilock's [ic_loaded] payload
      (fileread destructs it as "Hdnat" at ProofFileread.v:1741), at
      [dn0 := dn].  The half that was WRONG: [p_pid pj] canNOT be split out
      of [proc_priv] alongside it, because [ProcInv.proc_priv_pid] is a
      BORROW.  S3p made that a non-question by moving the fraction into the
      kernel arm of writei's bracket, so the walk never asks for it -- it
      hands over [proc_priv] and writei does its own borrowing.  See the
      banner and [fw_writei_src].
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

   THE RESUME POINT (S3p's repair IS IN; what is left is only the walk):
   the walk itself, in [ProofFileread.v]'s shape --
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
   [fw_epi] takes those slots as arbitrary words.

   S3o's LEAF TABLE, checked instruction by instruction against
   [CodeFilewrite.v]'s 118 AST lemmas and against the [wp_*_s_sconf] family
   as it actually exists.  Every branch displacement below was evaluated,
   not copied from the S3g graph; three of them are compressed-vs-full traps
   of the kind S3g's own trap 4 records, and one ([+0xd8]) is a NEGATIVE
   21-bit field that reads positive if the sign extension is skipped.

     +0x00 [wp_lbu_s_sconf]        a5 := zext (fc_writable Cf)
     +0x04 [wp_beqz_x0_{taken,fall}_s_sconf]   BTYPE(286, zreg, a5, BEQ)
             taken -> +0x122; the FALL is [fw_wbool_of_fall]
     +0x08..+0x14  [fw_pro]
     +0x16/+0x18/+0x1a  [wp_cmv_s_sconf]  s2:=a0, s6:=a1, s5:=a2
     +0x1c [wp_clw_s_sconf]        a5 := sext (fc_type Cf)   (a_ftype k)
     +0x1e [wp_cli_s_sconf] a4:=1 ; +0x20 [wp_beq_*] disp 52 -> +0x54
     +0x24 [wp_cli_s_sconf] a4:=3 ; +0x26 [wp_beq_*] disp 54 -> +0x5c
     +0x2a [wp_cli_s_sconf] a4:=2 ; +0x2c [wp_bne_*] disp 222 -> +0x10a
     --- FD_PIPE ---
     +0x54 [wp_cld_s_sconf] a0 := f->pipe ; +0x56 [wp_jal_s_sconf] disp 516
     +0x5a [wp_cj_s_sconf]  sext21 (2 * 81) = +0xa2 -> +0xfc   [fw_epi]
     --- FD_DEVICE ---
     +0x5c [wp_lh_s_sconf] (NOT compressed, and it does NOT live in the
             [WpSconf*] four: it is in [WpSmodeHalf.v], which
             [ProofFilewriteParts.v] does not import -- the walk must
             [Require Import WpSmodeHalf] itself, as [ProofFileread.v] does)
     +0x60 [wp_slli_s_sconf] 48
     +0x64 [wp_csrli_s_sconf] 48 ; +0x66 [wp_cli_s_sconf] a4:=9
     +0x68 [wp_bltu_*] disp 190 -> +0x126   ([fw_bltu9_{true,false}])
     +0x6c..+0x78 [fw_devidx] (lands at +0x7a; the field is at OFFSET 8)
     +0x7a [wp_cbeqz_*] sext13 (2 * 88) = 0xb0 -> +0x12a
     +0x7c [wp_cli_s_sconf] a0:=1 ; +0x7e [wp_cjalr_s_sconf] ([fw_ret_pc_cons])
     +0x80 [wp_cj_s_sconf]  sext21 (2 * 62) = 0x7c -> +0xfc
     +0x126 / +0x12a : [fw_m1j]      -> +0xfc
     --- FD_INODE ---
     +0x30 [wp_csdsp_s_sconf] s4 -> slot 6
     +0x32 [wp_bge_x0_{taken,fall}_s_sconf]  BTYPE(180, a2, zreg, BGE)
             taken (n <= 0, so n = 0 by [fw_zero_trip]) -> +0xe6
     +0x36..+0x3e  five [wp_csdsp_s_sconf] -> slots 3, 5, 9, 10, 11
     +0x40 [wp_cli_s_sconf] s4:=0 ([fw_li0])
     +0x42 [wp_clui_s_sconf] ([fw_lui1]) ; +0x44 [wp_addi4_s_sconf]
             ([fw_addi_m1024])                         -- s7 := 3072
     +0x48 [wp_clui_s_sconf] ; +0x4a [wp_addiw_s_sconf] ([fw_addiw_m1024])
     +0x4e [wp_cmv_s_sconf] s9 := a5                   -- s9 := 3072
     +0x50 [wp_cli_s_sconf] s8:=1 ([ProofFilereadParts.fr_li1])
     +0x52 [wp_cj_s_sconf]  sext21 (2 * 61) = 0x7a -> +0xcc  (BOTTOM-TESTED)
     LOOP TEST @ +0xcc
     +0xcc [wp_subw_s_sconf] a5 := n - i   (rs1 = s5, rs2 = s4; [fw_subw_moi])
     +0xd0 [wp_cmv_s_sconf] s3 := a5
     +0xd2 [wp_bge_*] rs1 = s7, rs2 = a5, disp 8112 = -80 -> +0x82
             TAKEN when 3072 >= n - i (chunk = the remainder, [fw_chunk_rem]);
             FALL is the capped chunk ([fw_chunk_cap])
     +0xd6 [wp_cmv_s_sconf] s3 := s9 ; +0xd8 [wp_cj_s_sconf]
             sext21 (2 * 2005 = 4010, bit 11 SET) = -86 -> +0x82
     LOOP BODY @ +0x82
     +0x82 [wp_caddiw_s_sconf] (COMPRESSED ADDIW; [fw_sextw_moi])
     +0x84 [wp_jal_s_sconf] disp 2095378 -> begin_op
     +0x88 [wp_ld_s_sconf] (NOT compressed) a0 := f->ip
     +0x8c [wp_jal_s_sconf] disp 2092792 -> ilock
     +0x90 [wp_cmv_s_sconf] a4 := s3 (= n1)
     +0x92 [wp_lw_s_sconf]  (NOT compressed) a3 := f->off   -- THE BORROWED CELL
     +0x96 [wp_add_s_sconf] (NOT compressed) a2 := i + addr
     +0x9a [wp_cmv_s_sconf] a1 := s8 (= 1: THE USER-SOURCE FLAG)
     +0x9c [wp_ld_s_sconf]  a0 := f->ip
     +0xa0 [wp_jal_s_sconf] disp 2093928 -> writei     <-- S3o'S STOP
     +0xa4 [wp_cmv_s_sconf] s1 := a0 (= r)
     +0xa6 [wp_bge_x0_*] disp 14 -> +0xb4  (skip the off update when r <= 0)
     +0xaa [wp_lw_s_sconf] ; +0xae [wp_addw_s_sconf] (COMPRESSED, c-regs
             a5/a0 = Cregidx 7 / Cregidx 2) ; +0xb0 [wp_sw_s_sconf]
             ([ProofFilereadParts.fr_addw_store] is the store value)
     +0xb4 [wp_ld_s_sconf] ; +0xb8 [wp_jal_s_sconf] disp 2092922 -> iunlock
     +0xbc [wp_jal_s_sconf] disp 2095434 -> end_op
     +0xc0 [wp_bne_*] rs1 = s3, rs2 = s1, disp 42 -> +0xea   (SHORT WRITE)
     +0xc4 [wp_addw4_s_sconf] (NOT compressed) s4 := i + r ([fw_addw_moi])
     +0xc8 [wp_bge_*] rs1 = s4, rs2 = s5, disp 18 -> +0xda   (i >= n)
             the FALL is the back edge to +0xcc, and [fw_i_advance] is its
             decrease
     --- the joins ---
     +0xda..+0xe4 : [fw_rest5] at (0xda,0xdc,0xde,0xe0,0xe2,0xe4), then
             [wp_cj_s_sconf] sext21 (2 * 8) = 0x10 -> +0xf4
     +0xe6 [wp_cli_s_sconf] s4:=0 ; +0xe8 [wp_cj_s_sconf] 2 * 6 = 0xc -> +0xf4
     +0xea..+0xf2 : [fw_rest5] at (0xea,0xec,0xee,0xf0,0xf2,0xf4) -- its LAST
             pc parameter IS +0xf4, so this join needs no jump of its own
     +0xf4 : [fw_tail], which owns everything from there to the [c.jr ra]

   THE LOOP LEMMA'S SHAPE, settled: [ProofWritei.wi_loop]'s, i.e. a
   [Local Lemma] with a [wi_cont]-style packaged continuation, [revert
   CID0; induction W as [| W IH]] over a FUEL, and the fuel is [n - i]
   (S3g's ledger; the chunk count would need [fw_chunk_cap]'s division and
   buys nothing).  NOT ireclaim's hart-closed wand: the back edge at +0xc8
   re-enters at +0xcc with a DIFFERENT [i], so the invariant has to be
   universally quantified over the loop-carried values, which is exactly
   what the [∀]-fuel shape gives and what a [□]-tail does not.  [fw_tail]
   is the [□]-tail, and it is already proved. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list functions bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre lifting.
(* The Sail side, in [ProofFileread.v]'s exact spelling.  It is NOT
   decoration: the Sail [uint] the [bltu] range facts below are stated over
   lives in [SailStdpp.Operators_mwords], and neither [SailStdpp.Values]
   alone, nor [Require Import Riscv.riscv_extras], nor [Import Defs] puts it
   in scope -- all three were tried, in that order. *)
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import RiscvLang RiscvPtsto RiscvExtras.
(* [pa_add] -- the buffer in writei's kernel arm is indexed with it *)
Require Import RiscvModelBytes.
Require Import FsCrash.
Require Import DinodeEnc.
Require Import InodeInv.
Require Import InodeLock.
Require Import DirView.
Require Import LogInv.
Require Import BioInv.
Require Import FdSlots FileInvDefs.
(* [ProcGeom] for [proc_addr] / [p_pid]: [ProcInv] Requires but does not
   Export it, so [proc_priv] is in scope here without them. *)
Require Import ProcGeom.
Require Import ProcPtOwn ProcInv.
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

(* ---------------------------------------------------------------------- *)
(*  S3o's ADDITIONS.  Everything the walk needs that is NOT arithmetic     *)
(*  about the loop: the dispatch's two range facts, the writability        *)
(*  bridge, the re-park's two assemblies, and the one slot-count split.    *)
(*                                                                        *)
(*  All of it is INDEPENDENT of the writei premise S3o stopped on, and     *)
(*  all of it is what S3q would otherwise have had to discover at a call   *)
(*  site with a register file in context (the [lia] rule from             *)
(*  durable-notes, and fileread's own [fr_*] block above its module).      *)
(* ---------------------------------------------------------------------- *)

(* MAXFILE*BSIZE as a Z LITERAL, never as a [nat] equality: a nat equality
   whose RHS is 274432 materialises a unary successor chain that blows the
   stack (durable-notes).  fileread's [fr_maxfile_bsize], restated here
   because that lemma lives in ProofFileread.v's own preamble and
   [Require Import] does not re-export. *)
Lemma fw_maxfile_bsize : (Z.of_nat MAXFILE * Z.of_nat BSIZE = 274432)%Z.
Proof. vm_compute. reflexivity. Qed.

(* the count, in the shape pipewrite and consolewrite both ask for.  Note
   what is NOT needed: fileread's [MAXFILE*BSIZE + n < 2^31] premise has no
   counterpart here, because the chunking makes writei's joint premise a
   closed fact ([SpecFilewrite.fw_chunk_joint]). *)
Lemma fw_n_range (n : Z) : (0 <= n < 2 ^ 31)%Z -> (- 2 ^ 31 <= n < 2 ^ 31)%Z.
Proof. change (2 ^ 31)%Z with 2147483648%Z. lia. Qed.

(* the file's recorded size is an [off_wf]-sized number, hence an int:
   writei's premise (14), read off [InodeLock.inode_ok]'s conjunct 5. *)
Lemma fw_size_lt31 (z : Z) :
  (0 <= z)%Z -> (z <= Z.of_nat MAXFILE * Z.of_nat BSIZE)%Z -> (z < 2 ^ 31)%Z.
Proof.
  rewrite fw_maxfile_bsize. change (2 ^ 31)%Z with 2147483648%Z. lia.
Qed.

(* ---- the FD_DEVICE dispatch's two range facts (fileread's, restated) ---- *)

Lemma fw_uint_moi (z : Z) : (0 <= z < 2 ^ 64)%Z ->
  uint (mword_of_int z : mword 64) = z.
Proof. intro H. rewrite uint_unsigned moi64_unsigned. by apply bvw64_small. Qed.

(* a [short] field's unsigned value is below 2^16 -- the range the major's
   zero extension and the [devsw] index arithmetic both need. *)
Lemma fw_major_range (w : mword 16) : (0 <= bv_unsigned w < 65536)%Z.
Proof.
  pose proof (bv_unsigned_in_range _ w) as H. unfold bv_modulus in H.
  change (2 ^ Z.of_N (MachineWord.MachineWord.Z_idx 16))%Z with 65536%Z in H.
  exact H.
Qed.

(* [bltu a4,a3] at +0x68 with a4 = 9: the NDEV bounds test, on the
   ZERO-extended major.  In range is exactly [major <= 9]. *)
Lemma fw_bltu9_false (mj : Z) : (0 <= mj)%Z -> (mj <= 9)%Z ->
  zopz0zI_u (mword_of_int 9 : mword 64) (mword_of_int mj : mword 64) = false.
Proof.
  intros H0 H9. unfold zopz0zI_u. apply Z.ltb_ge.
  rewrite (fw_uint_moi 9 ltac:(change (2^64)%Z with 18446744073709551616%Z; lia)).
  rewrite (fw_uint_moi mj ltac:(change (2^64)%Z with 18446744073709551616%Z; lia)).
  lia.
Qed.

Lemma fw_bltu9_true (mj : Z) : (9 < mj)%Z -> (mj < 65536)%Z ->
  zopz0zI_u (mword_of_int 9 : mword 64) (mword_of_int mj : mword 64) = true.
Proof.
  intros H9 Hb. unfold zopz0zI_u. apply Z.ltb_lt.
  rewrite (fw_uint_moi 9 ltac:(change (2^64)%Z with 18446744073709551616%Z; lia)).
  rewrite (fw_uint_moi mj ltac:(change (2^64)%Z with 18446744073709551616%Z; lia)).
  lia.
Qed.

(* consolewrite's entry address is even, so the [c.jalr a5] at +0x7e lands
   on it rather than on it-minus-its-low-bit. *)
Lemma fw_ret_pc_cons :
  ret_pc (mword_of_int KernelSyms.consolewrite : mword 64)
  = (mword_of_int KernelSyms.consolewrite : mword 64).
Proof. apply bv_eq; vm_compute; reflexivity. Qed.

(* the record-eta step: the two paths that return WITHOUT calling anything
   -- the pre-prologue [f->writable == 0] exit at +0x122 and the
   out-of-range / null-slot device exits -- leave the page table alone. *)
Lemma fw_upd_upt_id (V : pprivate) : upd_upt V (pv_upt V) = V.
Proof. destruct V; reflexivity. Qed.

(* three of the four arms produce [pipe_rw_ret] verbatim, and that IS
   [filewrite_ret]; named so the walk does not have to unfold a Definition
   at a call site. *)
Lemma fw_ret_of_pipe (n : Z) (r : mword 64) :
  pipe_rw_ret n r -> filewrite_ret n r.
Proof. exact (fun H => H). Qed.

(* ---- THE WRITABILITY BRIDGE ------------------------------------------
   [lbu a5,9(a0)] at +0x00 loads [fc_writable Cf] zero-extended and the
   [beq a5,x0] at +0x04 tests it.  On the FALL -- the only path that
   reaches the prologue at all -- the byte is nonzero, which is exactly
   [FileInvDefs.fc_wbool Cf = true].  That boolean is the antecedent of
   [filewrite_fs_env]'s last pure field, so this lemma is what turns "the
   fd is writable" into "the inode is not a directory", five frames down
   from sys_open.  ---------------------------------------------------- *)
Lemma fw_zext8_zero :
  eq_vec (zero_extend' 64 (mword_of_int 0 : mword 8) : mword 64)
         (zero_reg : mword 64) = true.
Proof. apply eq_vec_true_iff. apply bv_eq; vm_compute; reflexivity. Qed.

Lemma fw_wbool_of_fall (C : fcontent) :
  eq_vec (zero_extend' 64 (fc_writable C : mword 8) : mword 64)
         (zero_reg : mword 64) = false ->
  fc_wbool C = true.
Proof.
  intro Hne. rewrite /fc_wbool.
  destruct (eq_vec (fc_writable C : mword 8) (mword_of_int 0 : mword 8)) eqn:Hz;
    [| reflexivity].
  exfalso. apply eq_vec_true_iff in Hz. rewrite Hz in Hne.
  rewrite fw_zext8_zero in Hne. discriminate.
Qed.

(* the early return needs no converse: the [f->writable == 0] arm at +0x122
   returns -1 before the type is ever read, so it never looks at
   [fc_wbool].  Only the FALL direction is load-bearing. *)

(* ---- THE RE-PARK, in two assemblies ----------------------------------
   ilock hands [InodeLock.inode_ok] out inside [IcacheEscrow.ic_loaded] and
   iunlock demands it back at the NEW record.  writei's postcondition
   supplies all seven conjuncts -- five outright and two (the size cap and
   [InodeInv.inode_sized]) as S3i's PRESERVATIONS, whose antecedents are
   the very conjuncts that came in.  Assembling them in one named lemma is
   what keeps the walk's re-park to a single [iPureIntro].  ------------- *)
Lemma fw_inode_ok_rebuild (cov : gset Z) (logstart : Z) (dn' : dinode)
    (bm' : blkmap) (data' : nat -> list (bv 8)) :
  blkmap_wf cov logstart bm' ->
  bm_covers bm' (bv_unsigned (di_size dn')) ->
  di_addrs dn' = bm_cells bm' ->
  bv_unsigned (di_type dn') <> 0 ->
  (bv_unsigned (di_size dn') <= Z.of_nat MAXFILE * Z.of_nat BSIZE)%Z ->
  blk_holes_zero bm' data' ->
  inode_sized data' ->
  inode_ok cov logstart dn' bm' data'.
Proof.
  intros H1 H2 H3 H4 H5 H6 H7.
  rewrite /inode_ok. split_and!; assumption.
Qed.

(* writei NEVER MOVES [di_type] -- definitionally, [SpecWritei.wi_dinode]
   copies it through.  Three separate obligations ride on this one line:
   [inode_ok]'s conjunct 4 at the new record, [DirView.dir_ok]'s vacuity
   below, and iunlock's [ity_shot g (di_type dn')] being ilock's own
   witness unchanged. *)
Lemma fw_wi_type (dn : dinode) (bm' : blkmap) (off tot : nat) :
  di_type (wi_dinode dn bm' off tot) = di_type dn.
Proof. reflexivity. Qed.

(* THE DIRECTORY DISCHARGE.  [ity_shot_agree] pins ilock's [di_type dn] to
   the fd's own [fwn_ty], [filewrite_fs_env]'s last field says a WRITABLE
   fd's type is not [T_DIR], and [DirView.dir_ok] is then vacuous at the
   record writei produced -- which has the same type by [fw_wi_type]. *)
Lemma fw_dir_ok_wi (nib : nat) (dn : dinode) (bm' : blkmap) (off tot : nat)
    (data' : nat -> list (bv 8)) :
  bv_unsigned (di_type dn) <> T_DIR_z ->
  dir_ok nib (wi_dinode dn bm' off tot) data'.
Proof.
  intro Hnd. apply dir_ok_not_dir. rewrite fw_wi_type. exact Hnd.
Qed.

(* ...and the shape the -1 arm needs, where writei returns the caller's own
   record untouched ([dn' = dn]). *)
Lemma fw_dir_ok_same (nib : nat) (dn : dinode) (data' : nat -> list (bv 8)) :
  bv_unsigned (di_type dn) <> T_DIR_z -> dir_ok nib dn data'.
Proof. apply dir_ok_not_dir. Qed.

(* ---- THE SLOT SPLIT --------------------------------------------------
   [filewrite_fs_env] carries writei's peak of THREE bio slot units;
   ilock's own bread wants ONE and gives it back before writei is called.
   One [bslots_op] rewrite, named so the walk does not re-derive [3 = 1+2]
   inside a proofmode goal.  --------------------------------------------- *)
Section FwSlots.
  Context `{!riscvGS Σ, !bioG Σ}.

  Lemma fw_bslots3 (bn : bio_names) :
    bslots bn 3 ⊣⊢ bslot bn ∗ bslots bn 2.
  Proof.
    rewrite /bslot. change 3%nat with (1 + 2)%nat. apply bslots_op.
  Qed.
End FwSlots.

(* ---- BLOCKER SIX, DISCHARGED -----------------------------------------
   The premise S3o stopped on, at the [user] the decode forces, proved from
   what the walk actually holds at +0xa0.

   [c.li s8,1] at +0x50 and [c.mv a1,s8] at +0x9a put 1 in a1, so writei's
   [eq_vec (m !!! Ra1) zero_reg = negb user] forces [user = true]; on that
   arm SpecWritei's source premise is now [proc_priv] AND NOTHING ELSE,
   which is exactly what [wp_filewrite_sconf_body] hands the walk.  Before
   S3p the same call also demanded [p_pid pj ↦₄{dq} pidv] alongside, and
   that conjunction was FALSE for any holder of [proc_priv] (the accessor is
   a borrow and the cell totals one) -- the walk could not be started.

   Stated with the [if] unreduced, and at a universally quantified [dq] and
   buffer, so that it is a discharge of the premise AS WRITTEN rather than
   of a hand-reduced paraphrase of it: if SpecWritei's bracket ever changes
   shape again, this stops compiling.  ------------------------------------- *)
Section FwWriteiSrc.
  (* exactly [ProcInv]'s own context for [proc_priv].  [lockG] IS QUALIFIED
     ON PURPOSE: this file does not [Require Import WpLock], so the plain
     spelling does not fail -- Rocq's backtick binders generalize, and it
     INVENTS a section variable [lockG] that [proc_priv]'s real instance can
     never match (durable-notes, "a class that is not IMPORTED becomes a
     fresh VARIABLE, silently").  The error is then eleven UNDEFINED EVARS
     over riscvGS / fileG / fdslotG / mem_pointsto / big_opL, none of which
     names [lockG]; the tell is [lockG] AND [lockG0] both in the printed
     context.  Qualifying rather than importing, because a new import here
     would also re-resolve every other unqualified name in the file -- see
     the header's [FW_MAX] warning. *)
  Context `{!riscvGS Σ, !WpLock.lockG Σ, !fileG Σ, !fdslotG Σ, !irefslotG Σ}.

  (* A BI-ENTAILMENT, so it covers both ends of the call at once: read left
     to right it is what the walk must SUPPLY at +0xa0, right to left what
     it GETS BACK at +0xa4 (instantiate [V := upd_upt V P']), which is what
     lets the loop re-park [proc_priv] and carry it into the next iteration
     without ever holding [p_pid] itself. *)
  Lemma fw_writei_src (γf : gname) (j : nat) (pidv : mword 32) (V : pprivate)
      (dq : dfrac) (src : mword 64) (n : nat) (src_bytes : nat -> bv 8) :
    (if true
     then proc_priv γf (proc_addr j) pidv V
     else ([∗ list] i ∈ seq 0 n, pa_add src i ↦ₘ src_bytes i) ∗
          p_pid (proc_addr j) ↦₄{dq} pidv)
    ⊣⊢ proc_priv γf (proc_addr j) pidv V.
  Proof. reflexivity. Qed.
End FwWriteiSrc.
