(* ProofFilewrite.v -- filewrite's own control flow and ghost steps.
   ============================= WIP, S3r ==============================

   STATUS (S3r): THE LOOP LEMMA IS LANDED AND THE WALK IS PARKED INSIDE
   THE BODY, at +0x84.  [FilewriteProof] exists at the bottom of this file
   and [wp_filewrite_sconf] is proved for EVERY path except the STRAIGHT
   LINE from the [jal begin_op] at +0x84 to the back edge at +0xc8, under
   ONE banered [Axiom cheat_] whose single occurrence is inside
   [fw_loop].  Proved outright, instruction by instruction:

     * +0x00/+0x04, the pre-prologue [f->writable] test, and its -1 return
       at +0x122 with sp and the whole frame untouched;
     * the prologue ([fw_pro]) and the three-way type dispatch at
       +0x16..+0x2c;
     * FD_PIPE in full: [c.ld a0,16(a0)], the [jal pipewrite], the [c.j] to
       [fw_epi];
     * FD_DEVICE in full, all four of its paths: the out-of-range major
       (+0x126), the null [devsw] slot (+0x12a), the [c.jalr] into
       consolewrite, and the [c.j] to [fw_epi];
     * the ELSE arm ([fw_panic]);
     * FD_INODE's entry: the s4 spill at +0x30, the HOISTED [n <= 0] test at
       +0x32, the whole ZERO-TRIP path (+0xe6 -> +0xf4 -> [fw_tail] ->
       [fw_epi]), and, on the other side of that test, the five late spills
       at +0x36..+0x3e, both [lui]/[addi] pairs for 3072, [i := 0],
       [user := 1], and the [c.j] to the bottom test;
     * S3r: THE LOOP ITSELF, as far as its body's first instruction --
       [fw_loop], the [forall]-fuel induction at [n - i], applied at +0xcc
       against the real state the walk holds there, and [fw_test], the
       +0xcc..+0xd8 chunk computation in BOTH of its arms, plus the
       [sext.w s3,s3] at +0x82 that normalises the chunk.

   WHAT S3r ACTUALLY BOUGHT, since it is one instruction of code and two
   lemmas: the loop lemma's STATEMENT is now machine-checked against the
   proof state at +0xcc rather than sketched in a note.  Three things are
   loop-carried ([i], the page-table descriptor, the bitmap's marked set)
   and -- the discovery -- almost nothing else is.  The inode is PARKED in
   the escrow at the head of every iteration, so no [dinode], no [blkmap]
   and no [data] appears in the invariant; ilock mints them inside the
   iteration and iunlock parks them again.  [f->off] is likewise RESIDENT
   in [off_inv] at the head, borrowed and returned within one iteration.
   The environment splits cleanly: fourteen PERSISTENT invariants (all
   fourteen verified persistent -- they are introduced with [#]) plus the
   ten pure fields, threaded free, and an exclusive half that is exactly
   [filewrite_fs_out fn Cf SI], i.e. the six resources the contract
   itself returns.  That is why the exit needs no re-assembly.

   WHAT IS LEFT is the straight line +0x84 .. +0xc8 and its three joins --
   see the FRONTIER banner inside [fw_loop] for the exact state it is
   handed and the exact order it must run.  [LinkFilewrite.v] is
   DELIBERATELY ABSENT: nothing outside this file may consume a parked
   walk, so file.c stays 6/7 until the frontier closes.

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

   THE RESUME POINT AS OF S3p (kept because the S3q walk below follows it
   line for line, and the loop half of it is still the frontier):
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

(* ====================================================================== *)
(*  THE WALK'S OWN IMPORTS.                                               *)
(*                                                                        *)
(*  Placed HERE, after the whole preamble, and not at the head of the     *)
(*  file: the header's [FW_MAX] surprise is the general rule -- a         *)
(*  [Require Import] re-resolves every unqualified name BELOW it, so the  *)
(*  seventeen lemmas above are compiled under the scope they were written *)
(*  in and only the walk sees the wider one.  In particular [WpLock] is   *)
(*  imported only from here down, which is why [fw_writei_src]'s context  *)
(*  above says [WpLock.lockG] and the functor's says [lockG].             *)
(*  [WpSmodeHalf] is the [lh] at +0x5c: it is NOT one of the four         *)
(*  [WpSconf*] files (S3o's leaf table), and ProofFilewriteParts does not *)
(*  import it.                                                            *)
(* ====================================================================== *)
From Stdlib Require Import Eqdep_dec.
From stdpp Require Import list_monad bitvector.tactics.
From iris.algebra Require Import excl auth gmap frac numbers.
From iris.base_logic.lib Require Import ghost_var gen_heap invariants ghost_map.
Require Import RegFile.
Require Import HartTp WpNext.
Require Import WpMmodeLeafBase.
Require Import SmodeCore.
Require Import StackOwn.
Require Import CalleeSaved KernelText.
Require Import KernelRvcDecode.
Require Import WpSconfAlu WpSconfMem WpSconfBtype WpSconfCtl.
Require Import WpSmodeIntr WpSmodeHalf.
Require Import IntrDefs.
Require Import CpuOwn.
Require Import UserPtTree.
Require Import KallocInv.
Require Import SchedCtx.
Require Import WpLock.
Require Import SpecPanic.
Require Import FileInv FileOff.
(* THE FOUR CLASSES THAT ARE NOT WHERE THEY LOOK.  [diskGhostG],
   [uartGhostG], [fsLogG] and [iregG] live in [DiskPtsto], [WpUart],
   [FsBlocks] and [InodeRegion], and NONE of them is re-exported by the
   [Require Import]s of the preamble above -- so without these four lines
   the functor's [Context] invents four FRESH variables of those names and
   the body fails with "Could not find an instance for ?diskGhostG0" and
   three more, none of which names the missing file.  Same tell as the
   [lockG]/[lockG0] one in [fw_writei_src]'s comment, one tier up. *)
Require Import WpUart DiskPtsto BioInv FsBlocks LogInv FsCrash.
Require Import DinodeEnc InodeInv InodeLock.
Require Import InodeRegion.
Require Import IrefSlots.
Require Import IcacheEscrow.
(* RE-IMPORT, fileread's line for line: [IcacheInv.islot] shadows
   [DinodeEnc.islot] and [IcacheRef.inode_ref] shadows [FileInv]'s
   placeholder; neither icache name is meant here except through the two
   contracts. *)
Require Import DinodeEnc.
(* [dev_major] and [NDEV_max] are SpecFileread's -- [SpecFilewrite] states
   [filewrite_dev_env]'s guard with them but does not re-export them, so the
   device arm's four [Local Lemma]s cannot even be TYPED without this line. *)
Require Import SpecFileread.
Require Import CodeFilewrite ProofFilereadParts ProofFilewriteParts.

Set Printing Depth 40.

(* ====================================================================== *)
(*  ############   PARKED, S3q -- ONE BOUNDED ASSUMPTION   ############   *)
(*                                                                        *)
(*  [cheat_] IS THE FRONTIER AND NOTHING ELSE DEPENDS ON IT.  It stands   *)
(*  for the part of [wp_filewrite_sconf] this stage did not reach; every  *)
(*  occurrence is marked [FRONTIER] in the walk below and each one names  *)
(*  the offset it parks at.  The file compiles, [LinkFilewrite.v] is      *)
(*  DELIBERATELY ABSENT (nothing outside this file may consume a parked   *)
(*  walk), and [tools/lemma_diff.py] should report exactly this one       *)
(*  Axiom.  The N4c namex parks are the precedent for the shape.          *)
(*                                                                        *)
(*  Unlike [Admitted] this still runs [Qed], so the surrounding walk is   *)
(*  really typechecked rather than merely parsed.                         *)
(* ====================================================================== *)
Axiom cheat_ : forall (A : Type), A.

Module FilewriteProof (Pipewrite : PIPEWRITE) (Ilock : ILOCK) (Writei : WRITEI)
                      (Iunlock : IUNLOCK) (BeginOp : BEGIN_OP) (EndOp : END_OP)
                      (Consolewrite : CONSOLEWRITE) : FILEWRITE.

Section ProofFilewrite.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !kallocG Σ,
            !bioG Σ, !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ,
            !fsCrashG Σ, !icacheG Σ, !irefslotG Σ, !iregG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Notation Rra := (mword_of_int 1 : mword 5).
  Notation Rs0 := (mword_of_int 8 : mword 5).
  Notation Rs1 := (mword_of_int 9 : mword 5).
  Notation Ra0 := (mword_of_int 10 : mword 5).
  Notation Ra1 := (mword_of_int 11 : mword 5).
  Notation Ra2 := (mword_of_int 12 : mword 5).
  Notation Ra3 := (mword_of_int 13 : mword 5).
  Notation Ra4 := (mword_of_int 14 : mword 5).
  Notation Ra5 := (mword_of_int 15 : mword 5).
  Notation Rs2 := (mword_of_int 18 : mword 5).
  Notation Rs3 := (mword_of_int 19 : mword 5).
  Notation Rs4 := (mword_of_int 20 : mword 5).
  Notation Rs5 := (mword_of_int 21 : mword 5).
  Notation Rs6 := (mword_of_int 22 : mword 5).
  Notation Rs7 := (mword_of_int 23 : mword 5).
  Notation Rs8 := (mword_of_int 24 : mword 5).
  Notation Rs9 := (mword_of_int 25 : mword 5).

  Local Ltac regne := reg_ne_side.

  (* ---- the type-indexed environment, opened at the type the code read.
     fileread's [fr_env_*] block, one arm at a time; the [used'] parameter is
     the only difference, and on the device arm it is the set nothing
     touched. ---------------------------------------------------------- *)
  Local Lemma fw_env_dev (γa' γf' : gname) (k' : nat)
      (fn' : fwrite_names) (Cf' : fcontent) :
    fc_type Cf' = FD_DEVICE ->
    filewrite_env γa' γf' k' fn' Cf' -∗ filewrite_dev_env fn' Cf'.
  Proof.
    intro Ht. rewrite /filewrite_env Ht.
    rewrite bool_decide_eq_false_2; [| by vm_compute].
    rewrite bool_decide_eq_true_2; [| reflexivity].
    by iIntros "$".
  Qed.

  Local Lemma fw_env_out_dev (fn' : fwrite_names) (Cf' : fcontent)
      (used' : gset Z) :
    fc_type Cf' = FD_DEVICE ->
    filewrite_dev_env fn' Cf' -∗ filewrite_env_out fn' Cf' used'.
  Proof.
    intro Ht. rewrite /filewrite_env_out /filewrite_dev_out Ht.
    rewrite bool_decide_eq_false_2; [| by vm_compute].
    rewrite bool_decide_eq_true_2; [| reflexivity].
    by iIntros "$".
  Qed.

  Local Lemma fw_dev_in (fn' : fwrite_names) (Cf' : fcontent) :
    (dev_major Cf' <= NDEV_max)%Z ->
    filewrite_dev_env fn' Cf' -∗
    ⌜fwn_wp fn' = (zero_reg : mword 64)
      \/ fwn_wp fn' = (mword_of_int KernelSyms.consolewrite : mword 64)⌝ ∗
    a_devsw_write (dev_major Cf') ↦₈{fwn_dqv fn'} fwn_wp fn'.
  Proof.
    intro H. rewrite /filewrite_dev_env.
    case_decide as H'; [by iIntros "$" | contradiction].
  Qed.

  Local Lemma fw_dev_in_back (fn' : fwrite_names) (Cf' : fcontent) :
    (dev_major Cf' <= NDEV_max)%Z ->
    ⌜fwn_wp fn' = (zero_reg : mword 64)
      \/ fwn_wp fn' = (mword_of_int KernelSyms.consolewrite : mword 64)⌝ -∗
    a_devsw_write (dev_major Cf') ↦₈{fwn_dqv fn'} fwn_wp fn' -∗
    filewrite_dev_env fn' Cf'.
  Proof.
    intro H. rewrite /filewrite_dev_env. case_decide as H'; [| contradiction].
    iIntros "%Hd Hc". iSplitR; [iPureIntro; exact Hd | iExact "Hc"].
  Qed.

  (* ---- the FD_INODE arm's environment, opened and closed --------------
     [fw_env_fs] is [fw_env_dev]'s twin at the third arm; [fw_env_out_fs]
     is the exit, and it is stated at an ARBITRARY [used'] because the
     bitmap only grows.  Neither does anything but reduce three
     [bool_decide]s, and they exist so that no [vm_compute] on an
     [fcontent] runs at a call site. ------------------------------------ *)
  Local Lemma fw_env_fs (ga' gf' : gname) (k' : nat)
      (fn' : fwrite_names) (Cf' : fcontent) :
    fc_type Cf' = FD_INODE ->
    filewrite_env ga' gf' k' fn' Cf' -∗ filewrite_fs_env ga' gf' k' fn' Cf'.
  Proof.
    intro Ht. rewrite /filewrite_env Ht.
    rewrite bool_decide_eq_false_2; [| by vm_compute].
    rewrite bool_decide_eq_false_2; [| by vm_compute].
    rewrite bool_decide_eq_true_2; [| reflexivity].
    by iIntros "$".
  Qed.

  Local Lemma fw_env_out_fs (fn' : fwrite_names) (Cf' : fcontent)
      (used' : gset Z) :
    fc_type Cf' = FD_INODE ->
    filewrite_fs_out fn' Cf' used' -∗ filewrite_env_out fn' Cf' used'.
  Proof.
    intro Ht. rewrite /filewrite_env_out Ht.
    rewrite bool_decide_eq_false_2; [| by vm_compute].
    rewrite bool_decide_eq_false_2; [| by vm_compute].
    rewrite bool_decide_eq_true_2; [| reflexivity].
    by iIntros "$".
  Qed.

  (* =================================================================== *)
  (*  THE LOOP TEST, +0xcc .. +0xd8 -- and the ONE reason it is a lemma   *)
  (*  of its own.                                                        *)
  (*                                                                     *)
  (*  [subw a5,s5,s4] computes [n - i]; [c.mv s3,a5] parks it; [bge      *)
  (*  s7,a5] is TAKEN to the body when the remainder fits in a chunk and *)
  (*  otherwise [c.mv s3,s9 ; c.j] caps it at FW_MAX.  BOTH arms land at *)
  (*  +0x82 -- and a Rocq proof cannot JOIN two arms.  So the block is   *)
  (*  lifted out and its continuation is quantified over the chunk [c]   *)
  (*  and the register map [P], which is the only thing the two arms     *)
  (*  disagree about.  Without this the whole loop body (begin_op ..     *)
  (*  end_op) would have to be written TWICE.                            *)
  (*                                                                     *)
  (*  The continuation is handed the state at +0x82 rather than at       *)
  (*  +0x84: the [sext.w s3,s3] there is straight-line, so it costs the  *)
  (*  caller one step and costs this lemma nothing.                      *)
  (*                                                                     *)
  (*  Note what is NOT a premise: [i < n] is, but nothing about the      *)
  (*  resources -- the block touches only a5 and s3 and reads four       *)
  (*  callee-saved registers, so it needs [sie_cap_gpr] and the text and *)
  (*  nothing else.                                                      *)
  (* =================================================================== *)
  Local Lemma fw_test `{CID0 : CpuId}
      (M : regfile) (Kn : nat) (nz iz : Z) (p : mword 64) (b : bool) :
    (0 <= iz < nz)%Z -> (nz < 2 ^ 31)%Z ->
    M !!! Regidx Rs4 = (mword_of_int iz : mword 64) ->
    M !!! Regidx Rs5 = (mword_of_int nz : mword 64) ->
    M !!! Regidx Rs7 = (mword_of_int SpecFilewrite.FW_MAX : mword 64) ->
    M !!! Regidx Rs9 = (mword_of_int SpecFilewrite.FW_MAX : mword 64) ->
    sie_cap_gpr M Kn b p -∗
    kernel_text -∗
    InstrBytes.pc_is (mword_of_int (FW + 0xcc) : mword 64) -∗
    wp_next b p (fun (CID : CpuId) =>
      ∀ (c : Z) (P : regfile),
        ⌜(0 < c <= SpecFilewrite.FW_MAX)%Z /\ (c <= nz - iz)%Z
          /\ P !!! Regidx Rs3 = (mword_of_int c : mword 64)
          /\ (forall r : mword 5, is_cs_idx r = true -> r <> Rs3 ->
                P !!! Regidx r = M !!! Regidx r)⌝ -∗
        sie_cap_gpr P Kn b p -∗
        InstrBytes.pc_is (mword_of_int (FW + 0x82) : mword 64) -∗
        WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hiz Hnz HMs4 HMs5 HMs7 HMs9.
    iIntros "Hcg #Htext Hpc Hcont".
    iPoseProof (fwri_0cc with "Htext") as "Hicc".
    iPoseProof (fwri_0d0 with "Htext") as "Hid0".
    iPoseProof (fwri_0d2 with "Htext") as "Hid2".
    iPoseProof (fwri_0d6 with "Htext") as "Hid6".
    iPoseProof (fwri_0d8 with "Htext") as "Hid8".
    (* ---- +0xcc subw a5,s5,s4 : a5 := n - i ---- *)
    iApply (wp_subw_s_sconf (mword_of_int (FW + 0xcc)) Ra5 Rs5 Rs4 M Kn b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hicc [-]").
    iIntros (CID1 Hq1) "Hcg Hpc". iEval (rgne) in "Hcg".
    set (T1 := <[Regidx Ra5 := regval_into_reg
                  (sign_extend' 64 (sub_vec
                     (subrange_vec_dec (M !!! Regidx Rs5) 31 0 : mword 32)
                     (subrange_vec_dec (M !!! Regidx Rs4) 31 0 : mword 32)))]> M).
    assert (HT1a5 : T1 !!! Regidx Ra5 = (mword_of_int (nz - iz) : mword 64)).
    { rewrite /T1 upd_eq. unfold regval_into_reg.
      rewrite HMs5 HMs4. apply fw_subw_moi; lia. }
    assert (Hppd0 : add_vec_int (mword_of_int (FW + 0xcc) : mword 64) 4
                    = mword_of_int (FW + 0xd0))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hppd0) in "Hpc".
    (* ---- +0xd0 c.mv s3,a5 ---- *)
    iApply (wp_cmv_s_sconf (mword_of_int (FW + 0xd0)) Rs3 Ra5 T1 Kn b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hid0 [-]").
    iIntros (CID2 Hq2) "Hcg Hpc". iEval (rgne) in "Hcg".
    set (T2 := <[Regidx Rs3 := regval_into_reg
                  (add_vec zero_reg (T1 !!! Regidx Ra5))]> T1).
    assert (HT2s3 : T2 !!! Regidx Rs3 = (mword_of_int (nz - iz) : mword 64)).
    { rewrite /T2 upd_eq. unfold regval_into_reg.
      rewrite add_vec_zero_l. exact HT1a5. }
    assert (HT2a5 : T2 !!! Regidx Ra5 = (mword_of_int (nz - iz) : mword 64))
      by (rewrite /T2 upd_ne; [exact HT1a5 | vm_compute; discriminate]).
    assert (HT2s7 : T2 !!! Regidx Rs7
                    = (mword_of_int SpecFilewrite.FW_MAX : mword 64)).
    { rewrite /T2 upd_ne; [| vm_compute; discriminate].
      rewrite /T1 upd_ne; [exact HMs7 | vm_compute; discriminate]. }
    assert (HT2s9 : T2 !!! Regidx Rs9
                    = (mword_of_int SpecFilewrite.FW_MAX : mword 64)).
    { rewrite /T2 upd_ne; [| vm_compute; discriminate].
      rewrite /T1 upd_ne; [exact HMs9 | vm_compute; discriminate]. }
    assert (HT2thr : forall r : mword 5, is_cs_idx r = true -> r <> Rs3 ->
              T2 !!! Regidx r = M !!! Regidx r).
    { intros r Hr N3. rewrite /T2 upd_ne; [| regne].
      rewrite /T1 upd_ne; [reflexivity | regne]. }
    assert (Hppd2 : add_vec_int (mword_of_int (FW + 0xd0) : mword 64) 2
                    = mword_of_int (FW + 0xd2))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hppd2) in "Hpc".
    (* ---- +0xd2 bge s7,a5 : is 3072 >= n - i ? ---- *)
    assert (Hcmp : zopz0zKzJ_s (rget T2 Rs7) (rget T2 Ra5)
                   = Z.geb SpecFilewrite.FW_MAX (nz - iz)).
    { rewrite (rget_ne T2 Rs7 ltac:(vm_compute; discriminate)).
      rewrite (rget_ne T2 Ra5 ltac:(vm_compute; discriminate)).
      rewrite HT2s7 HT2a5.
      apply fw_bge_moi; unfold SpecFilewrite.FW_MAX;
        change (2 ^ 31)%Z with 2147483648%Z; lia. }
    assert (Htgt82 : add_vec (mword_of_int (FW + 0xd2) : mword 64)
              (sign_extend' 64 (mword_of_int 8112 : mword 13))
              = mword_of_int (FW + 0x82))
      by (apply bv_eq; vm_compute; reflexivity).
    destruct (Z.geb SpecFilewrite.FW_MAX (nz - iz)) eqn:Hge.
    - (* ---- TAKEN: the chunk is the whole remainder ([fw_chunk_rem]) ---- *)
      assert (Hrem : (0 < nz - iz <= SpecFilewrite.FW_MAX)%Z).
      { apply fw_chunk_rem; [lia | apply Z.geb_le; exact Hge]. }
      iApply (wp_bge_taken_s_sconf (mword_of_int (FW + 0xd2))
                (mword_of_int 8112 : mword 13) Ra5 Rs7 T2 Kn b
                ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                ltac:(exact Hcmp)
                ltac:(rewrite Htgt82; vm_compute; reflexivity)
                with "Hcg Hpc Hid2 [-]").
      iNext. iIntros (CID3 Hq3) "Hcg Hpc".
      iEval (rewrite Htgt82) in "Hpc".
      iSpecialize ("Hcont" $! CID3 with "[]"); [iPureIntro; wp_next_chain|].
      iApply ("Hcont" $! (nz - iz)%Z T2 with "[%] Hcg Hpc").
      split_and!; [lia | lia | lia | exact HT2s3 | exact HT2thr].
    - (* ---- FALL: the chunk is the CAP ([fw_chunk_cap]).  [Z.geb_le] is
             the only direction that exists; the strict one is derived by
             cases, NOT by a [Z.geb_gt] (there is no such lemma). ---- *)
      assert (Hgt : (SpecFilewrite.FW_MAX < nz - iz)%Z).
      { destruct (Z.le_gt_cases (nz - iz) SpecFilewrite.FW_MAX) as [Hle | Hgt']; [| lia].
        exfalso.
        rewrite (proj2 (Z.geb_le SpecFilewrite.FW_MAX (nz - iz)) Hle) in Hge.
        discriminate. }
      assert (Hcap : (0 < SpecFilewrite.FW_MAX <= SpecFilewrite.FW_MAX)%Z)
        by (apply (fw_chunk_cap nz iz); [lia | exact Hgt]).
      iApply (wp_bge_fall_s_sconf (mword_of_int (FW + 0xd2))
                (mword_of_int 8112 : mword 13) Ra5 Rs7 T2 Kn b
                ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                ltac:(exact Hcmp)
                with "Hcg Hpc Hid2 [-]").
      iIntros (CID3 Hq3) "Hcg Hpc".
      assert (Hppd6 : add_vec_int (mword_of_int (FW + 0xd2) : mword 64) 4
                      = mword_of_int (FW + 0xd6))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hppd6) in "Hpc".
      (* ---- +0xd6 c.mv s3,s9 : n1 := FW_MAX ---- *)
      iApply (wp_cmv_s_sconf (mword_of_int (FW + 0xd6)) Rs3 Rs9 T2 Kn b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hid6 [-]").
      iIntros (CID4 Hq4) "Hcg Hpc". iEval (rgne) in "Hcg".
      set (T3 := <[Regidx Rs3 := regval_into_reg
                    (add_vec zero_reg (T2 !!! Regidx Rs9))]> T2).
      assert (HT3s3 : T3 !!! Regidx Rs3
                      = (mword_of_int SpecFilewrite.FW_MAX : mword 64)).
      { rewrite /T3 upd_eq. unfold regval_into_reg.
        rewrite add_vec_zero_l. exact HT2s9. }
      assert (HT3thr : forall r : mword 5, is_cs_idx r = true -> r <> Rs3 ->
                T3 !!! Regidx r = M !!! Regidx r).
      { intros r Hr N3. rewrite /T3 upd_ne; [| regne]. exact (HT2thr r Hr N3). }
      assert (Hppd8 : add_vec_int (mword_of_int (FW + 0xd6) : mword 64) 2
                      = mword_of_int (FW + 0xd8))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hppd8) in "Hpc".
      (* ---- +0xd8 c.j -> +0x82.  THE NEGATIVE 21-BIT FIELD (S3o's leaf
             table): 2 * 2005 has bit 11 SET, so the displacement is -86
             and NOT +4010. ---- *)
      assert (Htgt82b : add_vec (mword_of_int (FW + 0xd8) : mword 64)
                (sign_extend' 64 (sign_extend' 21
                   (concat_vec (mword_of_int 2005 : mword 11) ('b"0"))))
                = mword_of_int (FW + 0x82))
        by (apply bv_eq; vm_compute; reflexivity).
      iApply (wp_cj_s_sconf (mword_of_int (FW + 0xd8))
                (sign_extend' 21 (concat_vec (mword_of_int 2005 : mword 11) ('b"0")))
                T3 Kn b
                ltac:(rewrite Htgt82b; vm_compute; reflexivity)
                with "Hcg Hpc Hid8 [-]").
      iIntros (CID5 Hq5). iNext. iIntros "Hcg Hpc".
      iEval (rewrite Htgt82b) in "Hpc".
      iSpecialize ("Hcont" $! CID5 with "[]"); [iPureIntro; wp_next_chain|].
      iApply ("Hcont" $! SpecFilewrite.FW_MAX T3 with "[%] Hcg Hpc").
      split_and!; [lia | lia | lia | exact HT3s3 | exact HT3thr].
  Qed.

  (* =================================================================== *)
  (*  THE FD_INODE LOOP.                                                 *)
  (*                                                                     *)
  (*  Entry is the BOTTOM TEST at +0xcc, which is where the [c.j] at     *)
  (*  +0x52 sends the first iteration and where the back edge at +0xc8   *)
  (*  returns.  The shape is [ProofWritei.wi_loop]'s -- a [forall]-fuel  *)
  (*  induction with every loop-carried value re-quantified UNDER the    *)
  (*  fuel -- and NOT [ProofIreclaim.irc_loop]'s hart-closed wand: the   *)
  (*  back edge re-enters with a DIFFERENT [i], so the invariant must be *)
  (*  universally quantified over it, which is exactly what a [box]-tail *)
  (*  does not give.  The fuel is [n - i] (S3g's ledger); the chunk      *)
  (*  count would need [fw_chunk_cap]'s division and buys nothing.       *)
  (*                                                                     *)
  (*  WHAT IS LOOP-CARRIED, and it is remarkably little: the counter     *)
  (*  [iz], the page-table descriptor [PI] (which writei's user arm      *)
  (*  advances), and the bitmap's marked set [SI] (which balloc grows).  *)
  (*  THE INODE IS NOT: at the head of every iteration it is PARKED in   *)
  (*  the escrow, so its record, block map and data are inside           *)
  (*  [ic_escrow] and ilock mints fresh ones -- which is why the         *)
  (*  invariant names no [dinode] and no [blkmap] at all.  Likewise      *)
  (*  [f->off] is RESIDENT in [off_inv] at the head and is borrowed and  *)
  (*  returned inside a single iteration, so it too is absent here.      *)
  (*                                                                     *)
  (*  WHAT IS THREADED but not carried: the whole persistent half of     *)
  (*  [filewrite_fs_env] (fourteen invariants and contexts) is passed as *)
  (*  separate arguments rather than as the packed environment, because  *)
  (*  the packed form is indexed by [fwn_used fn] and the loop's bitmap  *)
  (*  set moves.  The EXCLUSIVE half is exactly [filewrite_fs_out fn Cf  *)
  (*  SI] -- the same six resources the contract returns -- which is why *)
  (*  the exit needs no re-assembly beyond [fw_env_out_fs].              *)
  (* =================================================================== *)
  Local Lemma fw_loop `{CID0 : CpuId}
      (ga gf : gname) (gs : list gname) (jx : nat) (glp : gname)
      (kx : nat) (qx : Qp) (Cf : fcontent) (fn : fwrite_names)
      (pidv : mword 32) (V : pprivate)
      (m : regfile) (K : nat) (eb : bool) (C : iProp Σ) (n : Z) (b : bool)
      (sp0 w12 pj : mword 64) :
    (* ---- the contract's own premises, unchanged ---- *)
    (filewrite_stack <= K)%nat ->
    (kx < NFILE)%nat ->
    (jx < NPROC)%nat ->
    gs !! jx = Some glp ->
    length gs = NPROC ->
    fwn_j fn = jx ->
    fwn_procs fn = gs ->
    (0 <= n < 2 ^ 31)%Z ->
    eb = true ->
    fc_type Cf = FD_INODE ->
    fc_wbool Cf = true ->
    m !!! Regidx csp_rs1 = sp0 ->
    pj = proc_addr jx ->
    (* ---- [filewrite_fs_env]'s ten PURE fields.  Pure, hence free: they
       are Coq hypotheses and cost the induction nothing. ---- *)
    log_geom_ok (fwn_cov fn) (fwn_logstart fn) ->
    (0 <= fwn_inodestart fn)%Z ->
    IBLOCK (fwn_inum fn) (fwn_inodestart fn) ∈ fwn_cov fn ->
    IBLOCK (fwn_inum fn) (fwn_inodestart fn)
      ∉ log_region_set (fwn_logstart fn) ->
    (bv_unsigned (fwn_inum fn) < 16 * Z.of_nat (fwn_nib fn))%Z ->
    BitmapInv.bitmap_geom_ok (fwn_cov fn) (fwn_logstart fn)
      (fwn_bmapstart fn) (fwn_size fn) ->
    SpecPrintkGen.printk_gen_contract (fwn_pr fn) (fwn_uart fn) (fwn_disk fn) ->
    fc_ip Cf = ientry (fwn_ik fn) ->
    (fwn_ik fn < NINODE)%nat ->
    (fc_wbool Cf = true -> bv_unsigned (fwn_ty fn) <> T_DIR_z) ->
    (* ---- THE FUEL, and everything the loop carries under it ---- *)
    forall (W : nat) (iz : Z) (PI : uptd) (SI : gset Z) (M : regfile),
    (n - iz <= Z.of_nat W)%Z ->
    (0 <= iz < n)%Z ->
    uptd_ext (pv_upt V) PI ->
    M !!! Regidx csp_rs1 = pa_stk sp0 12 ->
    M !!! Regidx Rs2 = fnode kx ->
    M !!! Regidx Rs4 = (mword_of_int iz : mword 64) ->
    M !!! Regidx Rs5 = (mword_of_int n : mword 64) ->
    M !!! Regidx Rs6 = m !!! Regidx Ra1 ->
    M !!! Regidx Rs7 = (mword_of_int SpecFilewrite.FW_MAX : mword 64) ->
    M !!! Regidx Rs8 = (mword_of_int 1 : mword 64) ->
    M !!! Regidx Rs9 = (mword_of_int SpecFilewrite.FW_MAX : mword 64) ->
    (* s1 and s3 are the loop's own scratch and are EXCLUDED here as well
       as the eight the entry set: [fw_rest5] puts the caller's values
       back out of slots 3 and 5 before [fw_tail] ever looks. *)
    (forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 -> r <> Rs0 ->
       r <> Rs1 -> r <> Rs2 -> r <> Rs3 -> r <> Rs4 -> r <> Rs5 ->
       r <> Rs6 -> r <> Rs7 -> r <> Rs8 -> r <> Rs9 ->
       M !!! Regidx r = m !!! Regidx r) ->
    sie_cap_gpr M (K - 12)%nat b pj -∗
    cpu_own 0%nat eb pj C b -∗
    kernel_text -∗
    InstrBytes.pc_is (mword_of_int (FW + 0xcc) : mword 64) -∗
    panic_wp_any -∗
    procs_inv gs -∗
    (* the twelve frame slots, none of which the body touches *)
    word_pointsto (pa_stk sp0 1) (DfracOwn 1) (m !!! Regidx Rra) -∗
    word_pointsto (pa_stk sp0 2) (DfracOwn 1) (m !!! Regidx Rs0) -∗
    word_pointsto (pa_stk sp0 3) (DfracOwn 1) (m !!! Regidx Rs1) -∗
    word_pointsto (pa_stk sp0 4) (DfracOwn 1) (m !!! Regidx Rs2) -∗
    word_pointsto (pa_stk sp0 5) (DfracOwn 1) (m !!! Regidx Rs3) -∗
    word_pointsto (pa_stk sp0 6) (DfracOwn 1) (m !!! Regidx Rs4) -∗
    word_pointsto (pa_stk sp0 7) (DfracOwn 1) (m !!! Regidx Rs5) -∗
    word_pointsto (pa_stk sp0 8) (DfracOwn 1) (m !!! Regidx Rs6) -∗
    word_pointsto (pa_stk sp0 9) (DfracOwn 1) (m !!! Regidx Rs7) -∗
    word_pointsto (pa_stk sp0 10) (DfracOwn 1) (m !!! Regidx Rs8) -∗
    word_pointsto (pa_stk sp0 11) (DfracOwn 1) (m !!! Regidx Rs9) -∗
    word_pointsto (pa_stk sp0 12) (DfracOwn 1) w12 -∗
    file_ref gf kx qx Cf -∗
    proc_priv gf pj pidv (upd_upt V PI) -∗
    KvmSpec.kalloc_env ga None -∗
    (* ---- the PERSISTENT half of [filewrite_fs_env] ---- *)
    off_inv gf kx -∗
    bio_ctx (fwn_bio fn)
      (fs_view (fwn_fs fn) (fwn_disk fn) (fwn_dev fn) (fwn_cov fn)) -∗
    log_ctx (fwn_log fn) (fwn_bio fn) (fwn_fs fn) (fwn_cov fn)
      (fwn_logstart fn) (fwn_dev fn) -∗
    fs_crash_seam (fwn_cov fn) (fwn_logstart fn) -∗
    gen_cert -∗
    KernelDataInv.kernel_data -∗
    SpecPrintkGen.printk_env (fwn_pr fn) (fwn_uart fn) (fwn_disk fn) -∗
    IcacheInv.itable_inv -∗
    ic_escrow (fwn_ic fn) (fwn_fs fn) (fwn_ireg fn) (fwn_cov fn)
      (fwn_logstart fn) (fwn_ik fn) -∗
    ireg_inv (fwn_ireg fn) (fwn_fs fn) (fwn_inodestart fn) (fwn_nib fn) -∗
    SleepLock.is_sleeplock (fwn_ilk fn) (fwn_islk fn) (i_lock (fc_ip Cf))
      "inode"%string (ic_tok (fwn_ic fn) (fwn_ik fn)) -∗
    ity_shot (fwn_g fn) (fwn_ty fn) -∗
    dev_inv (fwn_uart fn) (fwn_disk fn) -∗
    DiskInv.disk_geom (fwn_disk fn) (fwn_pd fn) (fwn_pav fn) (fwn_pu fn) -∗
    is_lock (fwn_dlock fn) DiskInv.d_lock "virtio_disk"%string
      (DiskInv.disk_res (fwn_disk fn) (fwn_pd fn) (fwn_pav fn) (fwn_pu fn)) -∗
    (* ---- the EXCLUSIVE half, at the set the loop has reached ---- *)
    filewrite_fs_out fn Cf SI -∗
    (* ---- and the contract's own continuation ---- *)
    wp_next b pj (fun (CID : CpuId) =>
      ∀ (mf : regfile) (r : mword 64) (P' : uptd) (used' : gset Z),
        ⌜callee_saved m mf⌝ -∗
        ⌜uptd_ext (pv_upt V) P'⌝ -∗
        ⌜filewrite_ret n r⌝ -∗
        ⌜mf !!! Regidx Ra0 = r⌝ -∗
        sie_cap_gpr mf K b pj -∗
        cpu_own 0%nat eb pj C b -∗
        InstrBytes.pc_is (ret_pc (m !!! Regidx Rra)) -∗
        file_ref gf kx qx Cf -∗
        proc_priv gf pj pidv (upd_upt V P') -∗
        filewrite_env_out fn Cf used' -∗
        WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HK Hkf Hjp Hgsj Hlens Hfnj Hfnps Hn Heb Htyi Hwb Hspm Hpjeq.
    intros P1 P2 P3 P4 P5 P6 P7 P8 P9 P10.
    intro W. revert CID0.
    induction W as [| W IH];
      intros CID0 iz PI SI M Hfuel Hiz Hext
             HMsp HMs2 HMs4 HMs5 HMs6 HMs7 HMs8 HMs9 HMthr.
    { (* NO FUEL.  The loop is entered only at [i < n], so [n - i] is at
         least one and the zero case is vacuous. *)
      exfalso. lia. }
    iIntros "Hcg Hcnt #Htext Hpc #Hpanic #Hprocs
             Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hb7 Hb8 Hb9 Hb10 Hb11 Hb12
             Href Hpriv Hkenv
             #Hoff #Hbio #Hlog #Hcrash #Hgc #Hkd #Hpk #Hit #Hesc #Hireg
             #Hslk #Hty #Hdev #Hgeo #Hdlk Hout Hcont".
    (* =================================================================
       +0xcc .. +0xd8 -- THE TEST, and the chunk it settles.
       ================================================================= *)
    iApply (fw_test (CID0 := CID0) M (K - 12)%nat n iz pj b
              Hiz (proj2 Hn) HMs4 HMs5 HMs7 HMs9
              with "Hcg Htext Hpc [-]").
    iIntros (CIDt Hst c P) "%Hc Hcg Hpc".
    destruct Hc as (Hcrange & Hcrem & HPs3 & HPthr).
    (* the register facts travel through the test untouched *)
    assert (HPsp : P !!! Regidx csp_rs1 = pa_stk sp0 12)
      by (rewrite (HPthr csp_rs1 ltac:(vm_compute; reflexivity)
                     ltac:(vm_compute; discriminate)); exact HMsp).
    assert (HPs2 : P !!! Regidx Rs2 = fnode kx)
      by (rewrite (HPthr Rs2 ltac:(vm_compute; reflexivity)
                     ltac:(vm_compute; discriminate)); exact HMs2).
    assert (HPs4 : P !!! Regidx Rs4 = (mword_of_int iz : mword 64))
      by (rewrite (HPthr Rs4 ltac:(vm_compute; reflexivity)
                     ltac:(vm_compute; discriminate)); exact HMs4).
    assert (HPs5 : P !!! Regidx Rs5 = (mword_of_int n : mword 64))
      by (rewrite (HPthr Rs5 ltac:(vm_compute; reflexivity)
                     ltac:(vm_compute; discriminate)); exact HMs5).
    assert (HPs6 : P !!! Regidx Rs6 = m !!! Regidx Ra1)
      by (rewrite (HPthr Rs6 ltac:(vm_compute; reflexivity)
                     ltac:(vm_compute; discriminate)); exact HMs6).
    assert (HPs7 : P !!! Regidx Rs7
                   = (mword_of_int SpecFilewrite.FW_MAX : mword 64))
      by (rewrite (HPthr Rs7 ltac:(vm_compute; reflexivity)
                     ltac:(vm_compute; discriminate)); exact HMs7).
    assert (HPs8 : P !!! Regidx Rs8 = (mword_of_int 1 : mword 64))
      by (rewrite (HPthr Rs8 ltac:(vm_compute; reflexivity)
                     ltac:(vm_compute; discriminate)); exact HMs8).
    assert (HPs9 : P !!! Regidx Rs9
                   = (mword_of_int SpecFilewrite.FW_MAX : mword 64))
      by (rewrite (HPthr Rs9 ltac:(vm_compute; reflexivity)
                     ltac:(vm_compute; discriminate)); exact HMs9).
    assert (HPthr' : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
              r <> Rs0 -> r <> Rs1 -> r <> Rs2 -> r <> Rs3 -> r <> Rs4 ->
              r <> Rs5 -> r <> Rs6 -> r <> Rs7 -> r <> Rs8 -> r <> Rs9 ->
              P !!! Regidx r = m !!! Regidx r).
    { intros r Hr Nsp Ns0 Ns1 Ns2 Ns3 Ns4 Ns5 Ns6 Ns7 Ns8 Ns9.
      rewrite (HPthr r Hr Ns3).
      exact (HMthr r Hr Nsp Ns0 Ns1 Ns2 Ns3 Ns4 Ns5 Ns6 Ns7 Ns8 Ns9). }
    (* =================================================================
       +0x82 sext.w s3,s3 -- gcc's normalisation of [n1].  The chunk is
       already a small non-negative literal, so this is the identity
       ([fw_sextw_moi] at [fw_chunk_lt31]'s range).
       ================================================================= *)
    iPoseProof (fwri_082 with "Htext") as "Hi82".
    iApply (wp_caddiw_s_sconf (mword_of_int (FW + 0x82)) Rs3
              (mword_of_int 0 : mword 6) P (K - 12)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi82 [-]").
    iIntros (CIDa Hsa) "Hcg Hpc". iEval (rgne) in "Hcg".
    set (B0 := <[Regidx Rs3 := regval_into_reg
                  (sign_extend' 64 (subrange_vec_dec
                     (add_vec (P !!! Regidx Rs3)
                        (sign_extend' 64 (sign_extend' 12
                           (mword_of_int 0 : mword 6)))) 31 0))]> P).
    assert (HB0s3 : B0 !!! Regidx Rs3 = (mword_of_int c : mword 64)).
    { rewrite /B0 upd_eq. unfold regval_into_reg. rewrite HPs3.
      apply fw_sextw_moi. exact (fw_chunk_lt31 c Hcrange). }
    assert (HB0thr : forall r : mword 5, is_cs_idx r = true -> r <> Rs3 ->
              B0 !!! Regidx r = P !!! Regidx r).
    { intros r Hr N3. rewrite /B0 upd_ne; [reflexivity | regne]. }
    assert (Hpp84 : add_vec_int (mword_of_int (FW + 0x82) : mword 64) 2
                    = mword_of_int (FW + 0x84))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp84) in "Hpc".
    (* ############### FRONTIER (S3r) ###############
       PARKED AT +0x84, THE [jal begin_op], and everything from the
       function's entry down to here is proved: the whole dispatch, the
       three light arms, FD_INODE's entry and zero-trip, the loop TEST in
       both its arms ([fw_test], which is what keeps the body from being
       written twice), and the [sext.w] that normalises the chunk.

       WHAT THIS STAGE LANDED, and why the statement above is the
       expensive part: the loop lemma is now MACHINE-CHECKED against the
       real state at +0xcc -- the [forall]-fuel shape, the three things
       that are loop-carried ([iz], [PI], [SI]) and, more importantly,
       the many that turned out NOT to be (the inode is parked, [f->off]
       is resident, and every content variable is minted fresh by ilock
       inside the iteration).  That is the design S3g/S3o could only
       sketch, and it is now a typechecked signature rather than a note.

       WHAT IS LEFT is the STRAIGHT-LINE body from +0x84 to +0xc8, in the
       order S3o's leaf table gives:
         +0x84 begin_op            (SpecBeginOp; [fw_av_begin_op]; the pid
                                    quarter is BORROWED out of [Hpriv] by
                                    [ProcInv.proc_priv_pid] and closed the
                                    instant the call returns -- fileread's
                                    discipline at ProofFileread.v:1685)
         +0x88 ld a0,24(s2)        (f->ip, out of "Hcip" at [q/2])
         +0x8c ilock               (SpecIlock v5, at [s/2] via
                                    [fw_shr_gen_halve]; keeps the other
                                    half so [fw_shr_regen] can pin the
                                    generation on the way out)
         +0x90..+0x9c              (a4 := n1, a3 := f->off via
                                    [off_checkout], a2 := i + addr,
                                    a1 := 1, a0 := f->ip)
         +0xa0 writei              ([fw_writei_src] both directions;
                                    [fw_budget_ok] + [fw_max_bridge] for
                                    the cost premise; the re-park is
                                    [fw_inode_ok_rebuild] + [fw_dir_ok_wi]
                                    + [ity_shot_agree])
         +0xa4..+0xb0              (s1 := r; the [r <= 0] skip; the
                                    f->off advance and [off_checkin])
         +0xb4..+0xbc              (iunlock via [fw_shr_regen], end_op at
                                    a PARTIALLY SPENT reservation)
         +0xc0 bne s3,s1           (the SHORT WRITE break -> +0xea)
         +0xc4..+0xc8              (i += r; [bge s4,s5] -> +0xda, and the
                                    FALL is the back edge, where [IH] is
                                    instantiated at [fw_i_advance]'s
                                    decrease)
       and the three joins, which are [fw_rest5] into [fw_tail] and are
       already proved.  Every premise of every one of those calls was
       cleared by hand in S3o and the last of them discharged as
       [fw_writei_src] in S3p, so nothing below is BLOCKED -- only
       unwritten.  [IH] is in context and unused for exactly that reason. *)
    exact (cheat_ _).
  Qed.

  Lemma wp_filewrite_sconf
      (γa γf : gname) (γs : list gname) (j : nat) (γlp : gname)
      (k : nat) (q : Qp) (Cf : fcontent) (fn : fwrite_names)
      (pidv : mword 32) (V : pprivate)
      (m : regfile) (K : nat) (eb : bool) (C : iProp Σ) (n : Z) (b : bool)
    : wp_filewrite_sconf_body γa γf γs j γlp k q Cf fn pidv V m K eb C n b.
  Proof.
    cbv beta delta [wp_filewrite_sconf_body].
    intros pcE pj ret_tgt HK Hk Hj Hgs Hlens Hfnj Hfnps Ha0 Ha2 Hn Heb.
    pose (sp0 := (m !!! Regidx csp_rs1 : mword 64)).
    iIntros "Hcg Hcnt #Htext Hpc #Hpanic Href Hpriv Hkenv #Hprocs Henv Hcont".
    assert (Hspm : m !!! Regidx csp_rs1 = sp0) by reflexivity.
    (* the reference, taken apart exactly as fileread does it: the dispatch
       reads f->writable and f->type out of the reference's OWN content
       fraction, so the loaded words ARE [fc_writable Cf] / [fc_type Cf]. *)
    iDestruct "Href" as "(Hrtok & Hrfields & Hrpay & Hrlv)".
    iEval (rewrite /file_fields) in "Hrfields".
    iDestruct "Hrfields" as "(Hcty & Hcrd & Hcwr & Hcpp & Hcip & Hcmaj)".
    iPoseProof (fwri_000 with "Htext") as "Hi00".
    iPoseProof (fwri_004 with "Htext") as "Hi04".
    (* =================================================================
       +0x00 lbu a5,9(a0) -- f->writable, BEFORE THE PROLOGUE (S3a's
       decode note 1: the -1 return at +0x122 runs with sp untouched).
       ================================================================= *)
    assert (Hpwr : add_vec (rget m Ra0) (sign_extend' 64 (mword_of_int 9 : mword 12))
                   = a_fwritable k).
    { rewrite (rget_ne m Ra0 ltac:(vm_compute; discriminate)) Ha0. reflexivity. }
    iEval (rewrite -Hpwr) in "Hcwr".
    iApply (wp_lbu_s_sconf pcE Ra5 Ra0 (mword_of_int 9 : mword 12) m K
              (fc_writable Cf : mword 8) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi00 Hcwr [-]").
    iIntros (CID1 Hs1) "Hcg Hpc Hcwr". iEval (rewrite Hpwr) in "Hcwr".
    set (R1 := <[Regidx Ra5 := regval_into_reg
                  (zero_extend' 64 (fc_writable Cf : mword 8))]> m).
    assert (HR1a5 : rget R1 Ra5 = zero_extend' 64 (fc_writable Cf : mword 8)).
    { rewrite (rget_ne R1 Ra5 ltac:(vm_compute; discriminate)).
      rewrite /R1; apply upd_eq. }
    assert (HR1sp : R1 !!! Regidx csp_rs1 = sp0)
      by (rewrite /R1 upd_ne; [exact Hspm | vm_compute; discriminate]).
    assert (HR1a0 : R1 !!! Regidx Ra0 = fnode k)
      by (rewrite /R1 upd_ne; [exact Ha0 | vm_compute; discriminate]).
    assert (HR1a1 : R1 !!! Regidx Ra1 = m !!! Regidx Ra1)
      by (rewrite /R1 upd_ne; [reflexivity | vm_compute; discriminate]).
    assert (HR1a2 : R1 !!! Regidx Ra2 = (mword_of_int n : mword 64))
      by (rewrite /R1 upd_ne; [exact Ha2 | vm_compute; discriminate]).
    assert (HR1thr : forall c : mword 5, c <> Ra5 -> R1 !!! Regidx c = m !!! Regidx c).
    { intros c N15. rewrite /R1 upd_ne; [reflexivity | regne]. }
    assert (Hpp04 : add_vec_int (pcE : mword 64) 4 = mword_of_int (FW + 0x04))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp04) in "Hpc".
    destruct (eq_vec (zero_extend' 64 (fc_writable Cf : mword 8) : mword 64)
                     (zero_reg : mword 64)) eqn:Hwrz.
    - (* ===============================================================
         NOT WRITABLE: [beq a5,x0] is taken to +0x122, and the two
         instructions there are the whole exit -- [c.li a0,-1; c.jr ra],
         with sp, the frame and every callee-saved register untouched.
         =============================================================== *)
      iPoseProof (fwri_122 with "Htext") as "Hi122".
      iPoseProof (fwri_124 with "Htext") as "Hi124".
      assert (Htgt122 : add_vec (mword_of_int (FW + 0x04) : mword 64)
                (sign_extend' 64 (mword_of_int 286 : mword 13))
                = mword_of_int (FW + 0x122))
        by (apply bv_eq; vm_compute; reflexivity).
      iApply (wp_beqz_x0_taken_s_sconf (mword_of_int (FW + 0x04))
                (mword_of_int 286 : mword 13) Ra5 R1 K b
                ltac:(vm_compute; discriminate)
                ltac:(rewrite HR1a5; exact Hwrz)
                ltac:(rewrite Htgt122; vm_compute; reflexivity)
                with "Hcg Hpc Hi04 [-]").
      iNext. iIntros (CID2 Hs2) "Hcg Hpc".
      iEval (rewrite Htgt122) in "Hpc".
      (* ---- +0x122 c.li a0,-1 ---- *)
      iApply (wp_cli_s_sconf (mword_of_int (FW + 0x122)) Ra0
                (mword_of_int 63 : mword 6) (mword_of_int (-1) : mword 64)
                R1 K b
                ltac:(vm_compute; discriminate) ltac:(rdok) fr_lim1
                with "Hcg Hpc Hi122 [-]").
      iIntros (CID3 Hs3) "Hcg Hpc".
      set (A1 := <[Regidx Ra0 := regval_into_reg (mword_of_int (-1) : mword 64)]> R1).
      assert (HA1a0 : A1 !!! Regidx Ra0 = (mword_of_int (-1) : mword 64))
        by (rewrite /A1; apply upd_eq).
      assert (HA1ra : rget A1 Rra = m !!! Regidx Rra).
      { rewrite (rget_ne A1 Rra ltac:(vm_compute; discriminate)).
        rewrite /A1 upd_ne; [| vm_compute; discriminate].
        rewrite /R1 upd_ne; [reflexivity | vm_compute; discriminate]. }
      assert (Hcs1 : callee_saved m A1).
      { rewrite /callee_saved. split_and!;
          (rewrite /A1 upd_ne; [| vm_compute; discriminate]);
          (rewrite /R1 upd_ne; [reflexivity | vm_compute; discriminate]). }
      assert (Hpp124 : add_vec_int (mword_of_int (FW + 0x122) : mword 64) 2
                       = mword_of_int (FW + 0x124)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp124) in "Hpc".
      (* ---- +0x124 c.jr ra ---- *)
      iApply (wp_cret_s_sconf (mword_of_int (FW + 0x124)) Rra A1 K b
                ltac:(vm_compute; discriminate) with "Hcg Hpc Hi124 [-]").
      iIntros (CID4 Hs4) "Hcg Hpc".
      iEval (rewrite HA1ra) in "Hpc".
      iDestruct (cpu_own_transport CID CID4 0%nat eb pj C b ltac:(wp_next_chain)
                   with "Hcnt") as "Hcnt".
      iSpecialize ("Hcont" $! CID4 with "[]"); [iPureIntro; wp_next_chain|].
      assert (HVid : upd_upt V (pv_upt V) = V) by apply fw_upd_upt_id.
      iApply ("Hcont" $! A1 (mword_of_int (-1)) (pv_upt V) (fwn_used fn)
                with "[%] [%] [%] [%] Hcg Hcnt [Hpc]
                      [Hrtok Hcty Hcrd Hcwr Hcpp Hcip Hcmaj Hrpay Hrlv]
                      [Hpriv] [Henv]").
      { exact Hcs1. }
      { apply uptd_ext_refl. }
      { apply filewrite_ret_m1. }
      { exact HA1a0. }
      { iEval (rewrite /ret_tgt). iExact "Hpc". }
      { rewrite /file_ref /file_fields.
        iFrame "Hrtok Hcty Hcrd Hcwr Hcpp Hcip Hcmaj Hrpay Hrlv". }
      { rewrite HVid. iExact "Hpriv". }
      { by iApply filewrite_env_out_of_env. }
    - (* ===============================================================
         WRITABLE.  [fw_wbool_of_fall] turns the FALL into the boolean
         [filewrite_fs_env]'s last pure field is conditioned on -- the
         resource form of "sys_open refuses writable directory fds".
         =============================================================== *)
      assert (Hwb : fc_wbool Cf = true) by (apply fw_wbool_of_fall; exact Hwrz).
      iApply (wp_beqz_x0_fall_s_sconf (mword_of_int (FW + 0x04))
                (mword_of_int 286 : mword 13) Ra5 R1 K b
                ltac:(vm_compute; discriminate)
                ltac:(rewrite HR1a5; exact Hwrz)
                with "Hcg Hpc Hi04 [-]").
      iIntros (CID2 Hs2) "Hcg Hpc".
      assert (Hpp08 : add_vec_int (mword_of_int (FW + 0x04) : mword 64) 4
                      = mword_of_int (FW + 0x08)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp08) in "Hpc".
      (* ---- +0x08 .. +0x14 : the whole prologue, [fw_pro] ---- *)
      iApply (fw_pro (CID0 := CID2) R1 K sp0 pj b (fw_K12 K HK) HR1sp
                with "Hcg Htext Hpc [-]").
      iIntros (CID3 Hs3 Mr w3 w5 w6 w9 w10 w11 w12)
        "%Hmr Hcg Hpc Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hb7 Hb8 Hb9 Hb10 Hb11 Hb12".
      destruct Hmr as (HMsp & HMs0 & HMthr).
      (* the five spilled words are the CALLER's, because [R1] differs from
         [m] only at a5 *)
      iEval (rewrite (HR1thr Rra ltac:(vm_compute; discriminate))) in "Hb1".
      iEval (rewrite (HR1thr Rs0 ltac:(vm_compute; discriminate))) in "Hb2".
      iEval (rewrite (HR1thr Rs2 ltac:(vm_compute; discriminate))) in "Hb4".
      iEval (rewrite (HR1thr Rs5 ltac:(vm_compute; discriminate))) in "Hb7".
      iEval (rewrite (HR1thr Rs6 ltac:(vm_compute; discriminate))) in "Hb8".
      assert (HMa0 : Mr !!! Regidx Ra0 = fnode k).
      { rewrite (HMthr Ra0 ltac:(vm_compute; discriminate)
                  ltac:(vm_compute; discriminate)). exact HR1a0. }
      assert (HMa1 : Mr !!! Regidx Ra1 = m !!! Regidx Ra1).
      { rewrite (HMthr Ra1 ltac:(vm_compute; discriminate)
                  ltac:(vm_compute; discriminate)). exact HR1a1. }
      assert (HMa2 : Mr !!! Regidx Ra2 = (mword_of_int n : mword 64)).
      { rewrite (HMthr Ra2 ltac:(vm_compute; discriminate)
                  ltac:(vm_compute; discriminate)). exact HR1a2. }
      assert (HMthrm : forall c : mword 5, is_cs_idx c = true -> c <> csp_rs1 ->
                c <> Rs0 -> Mr !!! Regidx c = m !!! Regidx c).
      { intros c Hcs N2 N8.
        rewrite (HMthr c N2 N8).
        destruct (decide (c = Ra5)) as [-> | N15]; [by vm_compute in Hcs|].
        exact (HR1thr c N15). }
      iPoseProof (fwri_016 with "Htext") as "Hi16".
      iPoseProof (fwri_018 with "Htext") as "Hi18".
      iPoseProof (fwri_01a with "Htext") as "Hi1a".
      iPoseProof (fwri_01c with "Htext") as "Hi1c".
      iPoseProof (fwri_01e with "Htext") as "Hi1e".
      iPoseProof (fwri_020 with "Htext") as "Hi20".
      iPoseProof (fwri_024 with "Htext") as "Hi24".
      iPoseProof (fwri_026 with "Htext") as "Hi26".
      iPoseProof (fwri_02a with "Htext") as "Hi2a".
      iPoseProof (fwri_02c with "Htext") as "Hi2c".
      (* ---- +0x16 c.mv s2,a0 ; +0x18 c.mv s6,a1 ; +0x1a c.mv s5,a2 ---- *)
      iApply (wp_cmv_s_sconf (mword_of_int (FW + 0x16)) Rs2 Ra0 Mr (K - 12)%nat b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi16 [-]").
      iIntros (CID4 Hs4) "Hcg Hpc". iEval (rgne) in "Hcg".
      set (G1 := <[Regidx Rs2 := regval_into_reg
                    (add_vec zero_reg (Mr !!! Regidx Ra0))]> Mr).
      assert (Hpp18 : add_vec_int (mword_of_int (FW + 0x16) : mword 64) 2
                      = mword_of_int (FW + 0x18)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp18) in "Hpc".
      iApply (wp_cmv_s_sconf (mword_of_int (FW + 0x18)) Rs6 Ra1 G1 (K - 12)%nat b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi18 [-]").
      iIntros (CID5 Hs5) "Hcg Hpc". iEval (rgne) in "Hcg".
      set (G2 := <[Regidx Rs6 := regval_into_reg
                    (add_vec zero_reg (G1 !!! Regidx Ra1))]> G1).
      assert (Hpp1a : add_vec_int (mword_of_int (FW + 0x18) : mword 64) 2
                      = mword_of_int (FW + 0x1a)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp1a) in "Hpc".
      iApply (wp_cmv_s_sconf (mword_of_int (FW + 0x1a)) Rs5 Ra2 G2 (K - 12)%nat b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi1a [-]").
      iIntros (CID6 Hs6) "Hcg Hpc". iEval (rgne) in "Hcg".
      set (G3 := <[Regidx Rs5 := regval_into_reg
                    (add_vec zero_reg (G2 !!! Regidx Ra2))]> G2).
      assert (HG3s2 : G3 !!! Regidx Rs2 = fnode k).
      { rewrite /G3 upd_ne; [| vm_compute; discriminate].
        rewrite /G2 upd_ne; [| vm_compute; discriminate].
        rewrite /G1 upd_eq. unfold regval_into_reg.
        rewrite HMa0. apply add_vec_zero_l. }
      assert (HG3s6 : G3 !!! Regidx Rs6 = m !!! Regidx Ra1).
      { rewrite /G3 upd_ne; [| vm_compute; discriminate].
        rewrite /G2 upd_eq. unfold regval_into_reg.
        rewrite /G1 upd_ne; [| vm_compute; discriminate].
        rewrite HMa1. apply add_vec_zero_l. }
      assert (HG3s5 : G3 !!! Regidx Rs5 = (mword_of_int n : mword 64)).
      { rewrite /G3 upd_eq. unfold regval_into_reg.
        rewrite /G2 upd_ne; [| vm_compute; discriminate].
        rewrite /G1 upd_ne; [| vm_compute; discriminate].
        rewrite HMa2. apply add_vec_zero_l. }
      assert (HG3a0 : G3 !!! Regidx Ra0 = fnode k).
      { rewrite /G3 upd_ne; [| vm_compute; discriminate].
        rewrite /G2 upd_ne; [| vm_compute; discriminate].
        rewrite /G1 upd_ne; [exact HMa0 | vm_compute; discriminate]. }
      assert (HG3sp : G3 !!! Regidx csp_rs1 = pa_stk sp0 12).
      { rewrite /G3 upd_ne; [| vm_compute; discriminate].
        rewrite /G2 upd_ne; [| vm_compute; discriminate].
        rewrite /G1 upd_ne; [exact HMsp | vm_compute; discriminate]. }
      assert (HG3thr : forall c : mword 5, is_cs_idx c = true -> c <> csp_rs1 ->
                c <> Rs0 -> c <> Rs2 -> c <> Rs5 -> c <> Rs6 ->
                G3 !!! Regidx c = m !!! Regidx c).
      { intros c Hcs N2 N8 N18 N21 N22.
        rewrite /G3 upd_ne; [| regne].
        rewrite /G2 upd_ne; [| regne].
        rewrite /G1 upd_ne; [| regne].
        exact (HMthrm c Hcs N2 N8). }
      assert (Hpp1c : add_vec_int (mword_of_int (FW + 0x1a) : mword 64) 2
                      = mword_of_int (FW + 0x1c)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp1c) in "Hpc".
      (* ---- +0x1c c.lw a5,0(a0) : THE TYPE ---- *)
      assert (Hpty : add_vec (rget G3 Ra0) (sign_extend' 64 (mword_of_int 0 : mword 12))
                     = a_ftype k).
      { rewrite (rget_ne G3 Ra0 ltac:(vm_compute; discriminate)) HG3a0.
        rewrite /a_ftype. apply addv_sext0. }
      iEval (rewrite -Hpty) in "Hcty".
      iApply (wp_clw_s_sconf (mword_of_int (FW + 0x1c)) Ra5 Ra0
                (mword_of_int 0 : mword 12) G3 (K - 12)%nat (fc_type Cf) b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi1c Hcty [-]").
      iIntros (CID7 Hs7) "Hcg Hpc Hcty". iEval (rewrite Hpty) in "Hcty".
      set (G4 := <[Regidx Ra5 := regval_into_reg (sign_extend' 64 (fc_type Cf))]> G3).
      assert (HG4a5 : G4 !!! Regidx Ra5 = sign_extend' 64 (fc_type Cf))
        by (rewrite /G4; apply upd_eq).
      assert (Hpp1e : add_vec_int (mword_of_int (FW + 0x1c) : mword 64) 2
                      = mword_of_int (FW + 0x1e)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp1e) in "Hpc".
      (* ---- +0x1e c.li a4,1 ; +0x20 beq a5,a4 -> +0x54 (FD_PIPE) ---- *)
      iApply (wp_cli_s_sconf (mword_of_int (FW + 0x1e)) Ra4
                (mword_of_int 1 : mword 6) (mword_of_int 1 : mword 64)
                G4 (K - 12)%nat b
                ltac:(vm_compute; discriminate) ltac:(rdok) fr_li1
                with "Hcg Hpc Hi1e [-]").
      iIntros (CID8 Hs8) "Hcg Hpc".
      set (G5 := <[Regidx Ra4 := regval_into_reg (mword_of_int 1 : mword 64)]> G4).
      assert (HG5a5 : rget G5 Ra5 = sign_extend' 64 (fc_type Cf)).
      { rewrite (rget_ne G5 Ra5 ltac:(vm_compute; discriminate)).
        rewrite /G5 upd_ne; [exact HG4a5 | vm_compute; discriminate]. }
      assert (HG5a4 : rget G5 Ra4 = (mword_of_int 1 : mword 64)).
      { rewrite (rget_ne G5 Ra4 ltac:(vm_compute; discriminate)).
        rewrite /G5; apply upd_eq. }
      assert (Hcmp1 : eq_vec (rget G5 Ra5) (rget G5 Ra4)
                      = eq_vec (fc_type Cf) (mword_of_int 1 : mword 32)).
      { rewrite HG5a5 HG5a4. apply fr_ty_eqz.
        change (2^31)%Z with 2147483648%Z. lia. }
      assert (HG5a0 : G5 !!! Regidx Ra0 = fnode k).
      { rewrite /G5 upd_ne; [| vm_compute; discriminate].
        rewrite /G4 upd_ne; [exact HG3a0 | vm_compute; discriminate]. }
      assert (HG5s2 : G5 !!! Regidx Rs2 = fnode k).
      { rewrite /G5 upd_ne; [| vm_compute; discriminate].
        rewrite /G4 upd_ne; [exact HG3s2 | vm_compute; discriminate]. }
      assert (HG5s5 : G5 !!! Regidx Rs5 = (mword_of_int n : mword 64)).
      { rewrite /G5 upd_ne; [| vm_compute; discriminate].
        rewrite /G4 upd_ne; [exact HG3s5 | vm_compute; discriminate]. }
      assert (HG5s6 : G5 !!! Regidx Rs6 = m !!! Regidx Ra1).
      { rewrite /G5 upd_ne; [| vm_compute; discriminate].
        rewrite /G4 upd_ne; [exact HG3s6 | vm_compute; discriminate]. }
      assert (HG5sp : G5 !!! Regidx csp_rs1 = pa_stk sp0 12).
      { rewrite /G5 upd_ne; [| vm_compute; discriminate].
        rewrite /G4 upd_ne; [exact HG3sp | vm_compute; discriminate]. }
      assert (HG5thr : forall c : mword 5, is_cs_idx c = true -> c <> csp_rs1 ->
                c <> Rs0 -> c <> Rs2 -> c <> Rs5 -> c <> Rs6 ->
                G5 !!! Regidx c = m !!! Regidx c).
      { intros c Hcs N2 N8 N18 N21 N22.
        rewrite /G5 upd_ne; [| regne].
        rewrite /G4 upd_ne; [| regne].
        exact (HG3thr c Hcs N2 N8 N18 N21 N22). }
      assert (Hpp20 : add_vec_int (mword_of_int (FW + 0x1e) : mword 64) 2
                      = mword_of_int (FW + 0x20)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp20) in "Hpc".
      destruct (eq_vec (fc_type Cf) (mword_of_int 1 : mword 32)) eqn:Hp1.
      + (* ======================== FD_PIPE ==========================
           [c.ld a0,16(a0)] then [jal pipewrite]; the value it leaves in
           a0 is the return, and [c.j +0xa2] goes straight to [fw_epi]. *)
        assert (Htyp : fc_type Cf = FD_PIPE)
          by (apply eq_vec_true_iff; exact Hp1).
        iDestruct "Hrpay" as (pn) "[Hpn Hpl]".
        iEval (rewrite /file_payload Htyp bool_decide_eq_true_2; [| reflexivity])
          in "Hpl".
        iDestruct "Hpl" as "[#Hpipe Hpref]".
        assert (Htgt54 : add_vec (mword_of_int (FW + 0x20) : mword 64)
                  (sign_extend' 64 (mword_of_int 52 : mword 13))
                  = mword_of_int (FW + 0x54))
          by (apply bv_eq; vm_compute; reflexivity).
        iApply (wp_beq_taken_s_sconf (mword_of_int (FW + 0x20))
                  (mword_of_int 52 : mword 13) Ra4 Ra5 G5 (K - 12)%nat b
                  ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                  ltac:(rewrite Hcmp1; first [exact Hp1 | reflexivity])
                  ltac:(rewrite Htgt54; vm_compute; reflexivity)
                  with "Hcg Hpc Hi20 [-]").
        iNext. iIntros (CID9 Hs9) "Hcg Hpc".
        iEval (rewrite Htgt54) in "Hpc".
        iPoseProof (fwri_054 with "Htext") as "Hi54".
        iPoseProof (fwri_056 with "Htext") as "Hi56".
        iPoseProof (fwri_05a with "Htext") as "Hi5a".
        (* ---- +0x54 c.ld a0,16(a0) : a0 := f->pipe ---- *)
        assert (Hppi : add_vec (rget G5 Ra0) (sign_extend' 64 (mword_of_int 16 : mword 12))
                       = a_fpipe k).
        { rewrite (rget_ne G5 Ra0 ltac:(vm_compute; discriminate)) HG5a0. reflexivity. }
        iEval (rewrite -Hppi) in "Hcpp".
        iApply (wp_cld_s_sconf (mword_of_int (FW + 0x54)) Ra0 Ra0
                  (mword_of_int 16 : mword 12) G5 (K - 12)%nat (fc_pipe Cf) b
                  ltac:(vm_compute; discriminate) ltac:(rdok)
                  with "Hcg Hpc Hi54 Hcpp [-]").
        iIntros (CID10 Hs10) "Hcg Hpc Hcpp". iEval (rewrite Hppi) in "Hcpp".
        set (P1 := <[Regidx Ra0 := regval_into_reg (fc_pipe Cf)]> G5).
        assert (Hpp56 : add_vec_int (mword_of_int (FW + 0x54) : mword 64) 2
                        = mword_of_int (FW + 0x56)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hpp56) in "Hpc".
        (* ---- +0x56 jal ra,pipewrite ---- *)
        iApply (wp_jal_s_sconf (mword_of_int (FW + 0x56)) Rra
                  (mword_of_int 516 : mword 21) P1 (K - 12)%nat b
                  ltac:(vm_compute; discriminate) ltac:(rdok)
                  ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi56 [-]").
        iIntros (CID11 Hs11) "Hcg Hpc".
        set (P2 := <[Regidx Rra := regval_into_reg
                      (add_vec_int (mword_of_int (FW + 0x56) : mword 64) 4)]> P1).
        assert (Htgtpw : add_vec (mword_of_int (FW + 0x56) : mword 64)
                  (sign_extend' 64 (mword_of_int 516 : mword 21))
                  = mword_of_int KernelSyms.pipewrite)
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Htgtpw) in "Hpc".
        assert (HP2a0 : P2 !!! Regidx Ra0 = fc_pipe Cf).
        { rewrite /P2 upd_ne; [| vm_compute; discriminate].
          rewrite /P1; apply upd_eq. }
        assert (HP2a2 : P2 !!! Regidx Ra2 = (mword_of_int n : mword 64)).
        { rewrite /P2 upd_ne; [| vm_compute; discriminate].
          rewrite /P1 upd_ne; [| vm_compute; discriminate].
          rewrite /G5 upd_ne; [| vm_compute; discriminate].
          rewrite /G4 upd_ne; [| vm_compute; discriminate].
          rewrite /G3 upd_ne; [| vm_compute; discriminate].
          rewrite /G2 upd_ne; [| vm_compute; discriminate].
          rewrite /G1 upd_ne; [exact HMa2 | vm_compute; discriminate]. }
        assert (HP2ra : P2 !!! Regidx Rra
                        = add_vec_int (mword_of_int (FW + 0x56) : mword 64) 4)
          by (rewrite /P2; apply upd_eq).
        assert (HP2sp : P2 !!! Regidx csp_rs1 = pa_stk sp0 12).
        { rewrite /P2 upd_ne; [| vm_compute; discriminate].
          rewrite /P1 upd_ne; [exact HG5sp | vm_compute; discriminate]. }
        assert (HP2thr : forall c : mword 5, is_cs_idx c = true -> c <> csp_rs1 ->
                  c <> Rs0 -> c <> Rs2 -> c <> Rs5 -> c <> Rs6 ->
                  P2 !!! Regidx c = m !!! Regidx c).
        { intros c Hcs N2 N8 N18 N21 N22.
          rewrite /P2 upd_ne; [| regne].
          rewrite /P1 upd_ne; [| regne].
          exact (HG5thr c Hcs N2 N8 N18 N21 N22). }
        iDestruct (cpu_own_transport CID CID11 0%nat eb pj C b ltac:(wp_next_chain)
                     with "Hcnt") as "Hcnt".
        iApply (Pipewrite.wp_pipewrite_sconf γa γf γs j γlp (fp_lock pn) (fp_pipe pn)
                  (fc_wbool Cf) q P2 (K - 12)%nat eb C pidv V n b
                  Hj Hgs Hlens HP2a2 (fw_n_range n Hn) (fw_av_pipe K HK) Heb
                  with "Hcg Hcnt Htext Hpc [] Hpref Hpriv Hkenv Hprocs Hpanic [-]").
        { iEval (rewrite HP2a0). iExact "Hpipe". }
        iIntros (CIDpw Hspw mf P') "%Hcspw %Hupt %Hretpw Hcg Hcnt Hpc Hpref Hpriv".
        assert (Hpc5a : ret_pc (P2 !!! Regidx Rra) = mword_of_int (FW + 0x5a)).
        { rewrite HP2ra. apply bv_eq; vm_compute; reflexivity. }
        iEval (rewrite Hpc5a) in "Hpc".
        pose proof Hcspw as Hcspw_cs.
        assert (Hmfsp : mf !!! Regidx csp_rs1 = pa_stk sp0 12).
        { rewrite (callee_saved_lookup Hcspw_cs csp_rs1 ltac:(vm_compute; reflexivity)).
          exact HP2sp. }
        assert (Hmfthr : forall c : mword 5, is_cs_idx c = true -> c <> csp_rs1 ->
                  c <> Rs0 -> c <> Rs2 -> c <> Rs5 -> c <> Rs6 ->
                  mf !!! Regidx c = m !!! Regidx c).
        { intros c Hcs N2 N8 N18 N21 N22.
          rewrite (callee_saved_lookup Hcspw_cs c Hcs).
          exact (HP2thr c Hcs N2 N8 N18 N21 N22). }
        (* ---- +0x5a c.j -> +0xfc ---- *)
        assert (Htgtfc : add_vec (mword_of_int (FW + 0x5a) : mword 64)
                  (sign_extend' 64 (sign_extend' 21
                     (concat_vec (mword_of_int 81 : mword 11) ('b"0"))))
                  = mword_of_int (FW + 0xfc))
          by (apply bv_eq; vm_compute; reflexivity).
        iApply (wp_cj_s_sconf (mword_of_int (FW + 0x5a))
                  (sign_extend' 21 (concat_vec (mword_of_int 81 : mword 11) ('b"0")))
                  mf (K - 12)%nat b
                  ltac:(rewrite Htgtfc; vm_compute; reflexivity)
                  with "Hcg Hpc Hi5a [-]").
        iIntros (CID12 Hs12). iNext. iIntros "Hcg Hpc".
        iEval (rewrite Htgtfc) in "Hpc".
        iApply (fw_epi (CID0 := CID12) m mf K sp0 (m !!! Regidx Rra)
                  (m !!! Regidx Rs0) (m !!! Regidx Rs2) (m !!! Regidx Rs5)
                  (m !!! Regidx Rs6) (mf !!! Regidx Ra0)
                  w3 w5 w6 w9 w10 w11 w12 pj b
                  (fw_K12 K HK) Hspm eq_refl eq_refl eq_refl eq_refl eq_refl
                  Hmfsp eq_refl Hmfthr
                  with "Hcg Htext Hpc Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hb7 Hb8 Hb9 Hb10
                        Hb11 Hb12 [-]").
        iIntros (CIDe Hse mfin) "%Hcsr Hcg Hpc".
        destruct Hcsr as [Hcsf Hrv].
        iDestruct (cpu_own_transport CIDpw CIDe 0%nat eb pj C b ltac:(wp_next_chain)
                     with "Hcnt") as "Hcnt".
        iSpecialize ("Hcont" $! CIDe with "[]"); [iPureIntro; wp_next_chain|].
        iApply ("Hcont" $! mfin (mf !!! Regidx Ra0) P' (fwn_used fn)
                  with "[%] [%] [%] [%] Hcg Hcnt [Hpc]
                        [Hrtok Hcty Hcrd Hcwr Hcpp Hcip Hcmaj Hpn Hpref Hrlv]
                        Hpriv [Henv]").
        { exact Hcsf. }
        { exact Hupt. }
        { by apply fw_ret_of_pipe. }
        { exact Hrv. }
        { iEval (rewrite /ret_tgt). iExact "Hpc". }
        { rewrite /file_ref /file_fields /file_pay.
          iFrame "Hrtok Hcty Hcrd Hcwr Hcpp Hcip Hcmaj Hrlv".
          iExists pn. iFrame "Hpn".
          rewrite /file_payload Htyp bool_decide_eq_true_2; [| reflexivity].
          iFrame "Hpipe Hpref". }
        { by iApply filewrite_env_out_of_env. }
      + (* ---- +0x24 c.li a4,3 ; +0x26 beq a5,a4 -> +0x5c (FD_DEVICE) ---- *)
        iApply (wp_beq_fall_s_sconf (mword_of_int (FW + 0x20))
                  (mword_of_int 52 : mword 13) Ra4 Ra5 G5 (K - 12)%nat b
                  ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                  ltac:(rewrite Hcmp1; first [exact Hp1 | reflexivity])
                  with "Hcg Hpc Hi20 [-]").
        iIntros (CID9 Hs9) "Hcg Hpc".
        assert (Hpp24 : add_vec_int (mword_of_int (FW + 0x20) : mword 64) 4
                        = mword_of_int (FW + 0x24)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hpp24) in "Hpc".
        iApply (wp_cli_s_sconf (mword_of_int (FW + 0x24)) Ra4
                  (mword_of_int 3 : mword 6) (mword_of_int 3 : mword 64)
                  G5 (K - 12)%nat b
                  ltac:(vm_compute; discriminate) ltac:(rdok) fr_li3
                  with "Hcg Hpc Hi24 [-]").
        iIntros (CID10 Hs10) "Hcg Hpc".
        set (G6 := <[Regidx Ra4 := regval_into_reg (mword_of_int 3 : mword 64)]> G5).
        assert (HG6a5 : rget G6 Ra5 = sign_extend' 64 (fc_type Cf)).
        { rewrite (rget_ne G6 Ra5 ltac:(vm_compute; discriminate)).
          rewrite /G6 upd_ne; [| vm_compute; discriminate].
          rewrite /G5 upd_ne; [exact HG4a5 | vm_compute; discriminate]. }
        assert (HG6a4 : rget G6 Ra4 = (mword_of_int 3 : mword 64)).
        { rewrite (rget_ne G6 Ra4 ltac:(vm_compute; discriminate)).
          rewrite /G6; apply upd_eq. }
        assert (Hcmp3 : eq_vec (rget G6 Ra5) (rget G6 Ra4)
                        = eq_vec (fc_type Cf) (mword_of_int 3 : mword 32)).
        { rewrite HG6a5 HG6a4. apply fr_ty_eqz.
          change (2^31)%Z with 2147483648%Z. lia. }
        assert (HG6a0 : G6 !!! Regidx Ra0 = fnode k).
        { rewrite /G6 upd_ne; [exact HG5a0 | vm_compute; discriminate]. }
        assert (HG6sp : G6 !!! Regidx csp_rs1 = pa_stk sp0 12).
        { rewrite /G6 upd_ne; [exact HG5sp | vm_compute; discriminate]. }
        assert (HG6s2 : G6 !!! Regidx Rs2 = fnode k).
        { rewrite /G6 upd_ne; [exact HG5s2 | vm_compute; discriminate]. }
        assert (HG6s5 : G6 !!! Regidx Rs5 = (mword_of_int n : mword 64)).
        { rewrite /G6 upd_ne; [exact HG5s5 | vm_compute; discriminate]. }
        assert (HG6s6 : G6 !!! Regidx Rs6 = m !!! Regidx Ra1).
        { rewrite /G6 upd_ne; [exact HG5s6 | vm_compute; discriminate]. }
        assert (HG6thr : forall c : mword 5, is_cs_idx c = true -> c <> csp_rs1 ->
                  c <> Rs0 -> c <> Rs2 -> c <> Rs5 -> c <> Rs6 ->
                  G6 !!! Regidx c = m !!! Regidx c).
        { intros c Hcs N2 N8 N18 N21 N22.
          rewrite /G6 upd_ne; [| regne].
          exact (HG5thr c Hcs N2 N8 N18 N21 N22). }
        assert (Hpp26 : add_vec_int (mword_of_int (FW + 0x24) : mword 64) 2
                        = mword_of_int (FW + 0x26)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hpp26) in "Hpc".
        destruct (eq_vec (fc_type Cf) (mword_of_int 3 : mword 32)) eqn:Hp3.
        * (* ========================= FD_DEVICE =======================
             [f->major] is a SIGNED halfword load and the [slli 48 ; srli 48]
             pair is gcc's zero extension of it, so the value the [bltu]
             tests is [dev_major Cf].  Past that test the table is indexed --
             at OFFSET 8, S3a's decode note 2, which is [fw_devidx]'s whole
             reason to exist -- and the slot is either null (-1) or
             consolewrite, whose contract is the functor's parameter. *)
          assert (Htyd : fc_type Cf = FD_DEVICE)
            by (apply eq_vec_true_iff; exact Hp3).
          iDestruct (fw_env_dev γa γf k fn Cf Htyd with "Henv") as "Henv".
          pose proof (fw_major_range (fc_major Cf : mword 16)) as Hmjr.
          iPoseProof (fwri_05c with "Htext") as "Hi5c".
          iPoseProof (fwri_060 with "Htext") as "Hi60".
          iPoseProof (fwri_064 with "Htext") as "Hi64".
          iPoseProof (fwri_066 with "Htext") as "Hi66".
          iPoseProof (fwri_068 with "Htext") as "Hi68".
          assert (Htgt5c : add_vec (mword_of_int (FW + 0x26) : mword 64)
                    (sign_extend' 64 (mword_of_int 54 : mword 13))
                    = mword_of_int (FW + 0x5c))
            by (apply bv_eq; vm_compute; reflexivity).
          iApply (wp_beq_taken_s_sconf (mword_of_int (FW + 0x26))
                    (mword_of_int 54 : mword 13) Ra4 Ra5 G6 (K - 12)%nat b
                    ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                    ltac:(rewrite Hcmp3; first [exact Hp3 | reflexivity])
                    ltac:(rewrite Htgt5c; vm_compute; reflexivity)
                    with "Hcg Hpc Hi26 [-]").
          iNext. iIntros (CID11 Hs11) "Hcg Hpc".
          iEval (rewrite Htgt5c) in "Hpc".
          (* ---- +0x5c lh a5,36(a0) : f->major, SIGN-extended ---- *)
          assert (Hpmj : add_vec (rget G6 Ra0) (sign_extend' 64 (mword_of_int 36 : mword 12))
                         = a_fmajor k).
          { rewrite (rget_ne G6 Ra0 ltac:(vm_compute; discriminate)) HG6a0. reflexivity. }
          iEval (rewrite -Hpmj) in "Hcmaj".
          iApply (wp_lh_s_sconf (mword_of_int (FW + 0x5c)) Ra5 Ra0
                    (mword_of_int 36 : mword 12) G6 (K - 12)%nat (fc_major Cf : mword 16) b
                    ltac:(vm_compute; discriminate) ltac:(rdok)
                    with "Hcg Hpc Hi5c Hcmaj [-]").
          iIntros (CID12 Hs12) "Hcg Hpc Hcmaj". iEval (rewrite Hpmj) in "Hcmaj".
          set (D1 := <[Regidx Ra5 := regval_into_reg
                        (sign_extend' 64 (fc_major Cf : mword 16))]> G6).
          assert (HD1a5 : D1 !!! Regidx Ra5 = sign_extend' 64 (fc_major Cf : mword 16))
            by (rewrite /D1; apply upd_eq).
          assert (Hpp60 : add_vec_int (mword_of_int (FW + 0x5c) : mword 64) 4
                          = mword_of_int (FW + 0x60)) by (apply bv_eq; vm_compute; reflexivity).
          iEval (rewrite Hpp60) in "Hpc".
          (* ---- +0x60 slli a3,a5,48 ---- *)
          assert (Hsl48 : shift_bits_left (rget D1 Ra5)
                            (subrange_vec_dec (mword_of_int 48 : mword 6) (Z.sub log2_xlen 1) 0)
                          = shift_bits_left (sign_extend' 64 (fc_major Cf : mword 16) : mword 64)
                            (subrange_vec_dec (mword_of_int 48 : mword 6) (Z.sub log2_xlen 1) 0)).
          { rewrite (rget_ne D1 Ra5 ltac:(vm_compute; discriminate)) HD1a5. reflexivity. }
          iApply (wp_slli_s_sconf (mword_of_int (FW + 0x60)) Ra3 Ra5
                    (mword_of_int 48 : mword 6)
                    (shift_bits_left (sign_extend' 64 (fc_major Cf : mword 16) : mword 64)
                       (subrange_vec_dec (mword_of_int 48 : mword 6) (Z.sub log2_xlen 1) 0))
                    D1 (K - 12)%nat b
                    ltac:(vm_compute; discriminate) ltac:(rdok) Hsl48
                    with "Hcg Hpc Hi60 [-]").
          iIntros (CID13 Hs13) "Hcg Hpc".
          set (D2 := <[Regidx Ra3 := regval_into_reg
                        (shift_bits_left (sign_extend' 64 (fc_major Cf : mword 16) : mword 64)
                           (subrange_vec_dec (mword_of_int 48 : mword 6)
                              (Z.sub log2_xlen 1) 0))]> D1).
          assert (Hpp64 : add_vec_int (mword_of_int (FW + 0x60) : mword 64) 4
                          = mword_of_int (FW + 0x64)) by (apply bv_eq; vm_compute; reflexivity).
          iEval (rewrite Hpp64) in "Hpc".
          (* ---- +0x64 c.srli a3,a3,48 : the zero extension ---- *)
          assert (Hc5 : creg2reg_idx (Cregidx (mword_of_int 5)) = Regidx Ra3)
            by (vm_compute; reflexivity).
          iEval (rewrite Hc5) in "Hi64".
          iApply (wp_csrli_s_sconf (mword_of_int (FW + 0x64)) (Cregidx (mword_of_int 5))
                    Ra3 (mword_of_int 48 : mword 6) D2 (K - 12)%nat b
                    Hc5 ltac:(vm_compute; discriminate) ltac:(rdok)
                    with "Hcg Hpc Hi64 [-]").
          iIntros (CID14 Hs14) "Hcg Hpc".
          set (D3 := <[Regidx Ra3 := regval_into_reg
                        (shift_bits_right (rget D2 Ra3)
                           (subrange_vec_dec (mword_of_int 48 : mword 6)
                              (Z.sub log2_xlen 1) 0))]> D2).
          assert (HD3a3 : D3 !!! Regidx Ra3
                          = (mword_of_int (bv_unsigned (fc_major Cf)) : mword 64)).
          { rewrite /D3 upd_eq. unfold regval_into_reg. rgne.
            rewrite /D2 upd_eq. unfold regval_into_reg. apply fr_zext16. }
          assert (HD3a5 : D3 !!! Regidx Ra5 = sign_extend' 64 (fc_major Cf : mword 16)).
          { rewrite /D3 upd_ne; [| vm_compute; discriminate].
            rewrite /D2 upd_ne; [exact HD1a5 | vm_compute; discriminate]. }
          assert (Hpp66 : add_vec_int (mword_of_int (FW + 0x64) : mword 64) 2
                          = mword_of_int (FW + 0x66)) by (apply bv_eq; vm_compute; reflexivity).
          iEval (rewrite Hpp66) in "Hpc".
          (* ---- +0x66 c.li a4,9 ---- *)
          iApply (wp_cli_s_sconf (mword_of_int (FW + 0x66)) Ra4
                    (mword_of_int 9 : mword 6) (mword_of_int 9 : mword 64)
                    D3 (K - 12)%nat b
                    ltac:(vm_compute; discriminate) ltac:(rdok) fr_li9
                    with "Hcg Hpc Hi66 [-]").
          iIntros (CID15 Hs15) "Hcg Hpc".
          set (D4 := <[Regidx Ra4 := regval_into_reg (mword_of_int 9 : mword 64)]> D3).
          assert (HD4a4 : rget D4 Ra4 = (mword_of_int 9 : mword 64)).
          { rewrite (rget_ne D4 Ra4 ltac:(vm_compute; discriminate)).
            rewrite /D4; apply upd_eq. }
          assert (HD4a3 : rget D4 Ra3
                          = (mword_of_int (bv_unsigned (fc_major Cf)) : mword 64)).
          { rewrite (rget_ne D4 Ra3 ltac:(vm_compute; discriminate)).
            rewrite /D4 upd_ne; [exact HD3a3 | vm_compute; discriminate]. }
          assert (HD4a5 : D4 !!! Regidx Ra5 = sign_extend' 64 (fc_major Cf : mword 16))
            by (rewrite /D4 upd_ne; [exact HD3a5 | vm_compute; discriminate]).
          assert (HD4sp : D4 !!! Regidx csp_rs1 = pa_stk sp0 12).
          { rewrite /D4 upd_ne; [| vm_compute; discriminate].
            rewrite /D3 upd_ne; [| vm_compute; discriminate].
            rewrite /D2 upd_ne; [| vm_compute; discriminate].
            rewrite /D1 upd_ne; [exact HG6sp | vm_compute; discriminate]. }
          assert (HD4thr : forall c : mword 5, is_cs_idx c = true -> c <> csp_rs1 ->
                    c <> Rs0 -> c <> Rs2 -> c <> Rs5 -> c <> Rs6 ->
                    D4 !!! Regidx c = m !!! Regidx c).
          { intros c Hcs N2 N8 N18 N21 N22.
            rewrite /D4 upd_ne; [| regne].
            rewrite /D3 upd_ne; [| regne].
            rewrite /D2 upd_ne; [| regne].
            rewrite /D1 upd_ne; [| regne].
            exact (HG6thr c Hcs N2 N8 N18 N21 N22). }
          assert (Hpp68 : add_vec_int (mword_of_int (FW + 0x66) : mword 64) 2
                          = mword_of_int (FW + 0x68)) by (apply bv_eq; vm_compute; reflexivity).
          iEval (rewrite Hpp68) in "Hpc".
          destruct (decide (dev_major Cf <= NDEV_max)%Z) as [Hin | Hout].
          ++ (* ---------- the major is IN RANGE: index the table ---------- *)
             unfold dev_major, NDEV_max in Hin.
             assert (Hmj0 : (0 <= bv_unsigned (fc_major Cf))%Z) by exact (proj1 Hmjr).
             assert (Hmj16 : (bv_unsigned (fc_major Cf) < 16)%Z)
               by exact (Z.le_lt_trans (bv_unsigned (fc_major Cf)) 9 16 Hin
                           ltac:(reflexivity)).
             assert (Hmj15 : (bv_unsigned (fc_major Cf) < 2 ^ 15)%Z).
             { change (2 ^ 15)%Z with 32768%Z.
               exact (Z.le_lt_trans (bv_unsigned (fc_major Cf)) 9 32768 Hin
                        ltac:(reflexivity)). }
             iDestruct (fw_dev_in fn Cf Hin with "Henv") as "[%Hwp Hslot]".
             iPoseProof (fwri_07a with "Htext") as "Hi7a".
             iApply (wp_bltu_fall_s_sconf (mword_of_int (FW + 0x68))
                       (mword_of_int 190 : mword 13) Ra3 Ra4 D4 (K - 12)%nat b
                       ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                       ltac:(rewrite HD4a4 HD4a3; exact (fw_bltu9_false _ Hmj0 Hin))
                       with "Hcg Hpc Hi68 [-]").
             iIntros (CID16 Hs16) "Hcg Hpc".
             assert (Hpp6c : add_vec_int (mword_of_int (FW + 0x68) : mword 64) 4
                             = mword_of_int (FW + 0x6c)) by (apply bv_eq; vm_compute; reflexivity).
             iEval (rewrite Hpp6c) in "Hpc".
             (* ---- +0x6c .. +0x78 : &devsw[major].write, and its value ---- *)
             assert (HD4a5m : D4 !!! Regidx Ra5
                              = (mword_of_int (bv_unsigned (fc_major Cf)) : mword 64)).
             { rewrite HD4a5. apply fr_sext16_small. exact Hmj15. }
             iEval (rewrite /a_devsw_write /dev_major) in "Hslot".
             iApply (fw_devidx (CID0 := CID16) D4 (K - 12)%nat
                       (bv_unsigned (fc_major Cf)) (fwn_wp fn) (fwn_dqv fn) pj b
                       (conj Hmj0 Hmj16) HD4a5m
                       with "Hcg Htext Hpc Hslot [-]").
             iIntros (CID17 Hs17 Dr) "%Hdr Hcg Hpc Hslot".
             destruct Hdr as (HDra5 & HDrthr).
             iEval (rewrite -(_ : a_devsw_write (dev_major Cf)
                                  = mword_of_int (KernelSyms.devsw
                                       + 16 * bv_unsigned (fc_major Cf) + 8));
                    [| reflexivity]) in "Hslot".
             assert (HDrsp : Dr !!! Regidx csp_rs1 = pa_stk sp0 12).
             { rewrite (HDrthr csp_rs1 ltac:(vm_compute; discriminate)
                         ltac:(vm_compute; discriminate)). exact HD4sp. }
             assert (HDrthrm : forall c : mword 5, is_cs_idx c = true -> c <> csp_rs1 ->
                       c <> Rs0 -> c <> Rs2 -> c <> Rs5 -> c <> Rs6 ->
                       Dr !!! Regidx c = m !!! Regidx c).
             { intros c Hcs N2 N8 N18 N21 N22.
               destruct (decide (c = Ra4)) as [-> | N14]; [by vm_compute in Hcs|].
               destruct (decide (c = Ra5)) as [-> | N15]; [by vm_compute in Hcs|].
               rewrite (HDrthr c N14 N15).
               exact (HD4thr c Hcs N2 N8 N18 N21 N22). }
             assert (Hc7 : creg2reg_idx (Cregidx (mword_of_int 7)) = Regidx Ra5)
               by (vm_compute; reflexivity).
             destruct Hwp as [Hwp0 | Hwpc].
             ** (* ---- the slot is NULL: +0x7a taken -> +0x12a, return -1 ---- *)
                iPoseProof (fwri_12a with "Htext") as "Hi12a".
                iPoseProof (fwri_12c with "Htext") as "Hi12c".
                assert (Htgt12a : add_vec (mword_of_int (FW + 0x7a) : mword 64)
                          (sign_extend' 64 (sign_extend' 13
                             (concat_vec (mword_of_int 88 : mword 8) ('b"0"))))
                          = mword_of_int (FW + 0x12a))
                  by (apply bv_eq; vm_compute; reflexivity).
                iApply (wp_cbeqz_taken_s_sconf (mword_of_int (FW + 0x7a))
                          (mword_of_int 88 : mword 8) (Cregidx (mword_of_int 7)) Ra5
                          Dr (K - 12)%nat b Hc7 ltac:(vm_compute; discriminate)
                          ltac:(rewrite (rget_ne Dr Ra5 ltac:(vm_compute; discriminate))
                                  HDra5 Hwp0; apply eq_vec_true_iff; reflexivity)
                          ltac:(rewrite Htgt12a; vm_compute; reflexivity)
                          with "Hcg Hpc Hi7a [-]").
                iNext. iIntros (CID18 Hs18) "Hcg Hpc".
                iEval (rewrite Htgt12a) in "Hpc".
                iApply (fw_m1j (CID0 := CID18) Dr (K - 12)%nat
                          (FW + 0x12a) (FW + 0x12c)
                          (sign_extend' 21 (concat_vec (mword_of_int 2024 : mword 11) ('b"0")))
                          pj b
                          ltac:(apply bv_eq; vm_compute; reflexivity)
                          ltac:(apply bv_eq; vm_compute; reflexivity)
                          with "Hcg Hpc Hi12a Hi12c [-]").
                iIntros (CID19 Hs19 Er) "%Her Hcg Hpc".
                destruct Her as (HEra0 & HErthr).
                assert (HErsp : Er !!! Regidx csp_rs1 = pa_stk sp0 12).
                { rewrite (HErthr csp_rs1 ltac:(vm_compute; reflexivity)). exact HDrsp. }
                assert (HErthr2 : forall c : mword 5, is_cs_idx c = true -> c <> csp_rs1 ->
                          c <> Rs0 -> c <> Rs2 -> c <> Rs5 -> c <> Rs6 ->
                          Er !!! Regidx c = m !!! Regidx c).
                { intros c Hcs N2 N8 N18 N21 N22.
                  rewrite (HErthr c Hcs).
                  exact (HDrthrm c Hcs N2 N8 N18 N21 N22). }
                iApply (fw_epi (CID0 := CID19) m Er K sp0 (m !!! Regidx Rra)
                          (m !!! Regidx Rs0) (m !!! Regidx Rs2) (m !!! Regidx Rs5)
                          (m !!! Regidx Rs6) (mword_of_int (-1))
                          w3 w5 w6 w9 w10 w11 w12 pj b
                          (fw_K12 K HK) Hspm eq_refl eq_refl eq_refl eq_refl eq_refl
                          HErsp HEra0 HErthr2
                          with "Hcg Htext Hpc Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hb7 Hb8 Hb9 Hb10
                                Hb11 Hb12 [-]").
                iIntros (CIDe Hse mfin) "%Hcsr Hcg Hpc".
                destruct Hcsr as [Hcsf Hrv].
                iDestruct (cpu_own_transport CID CIDe 0%nat eb pj C b ltac:(wp_next_chain)
                             with "Hcnt") as "Hcnt".
                iSpecialize ("Hcont" $! CIDe with "[]"); [iPureIntro; wp_next_chain|].
                assert (HVid : upd_upt V (pv_upt V) = V) by apply fw_upd_upt_id.
                iApply ("Hcont" $! mfin (mword_of_int (-1)) (pv_upt V) (fwn_used fn)
                          with "[%] [%] [%] [%] Hcg Hcnt [Hpc]
                                [Hrtok Hcty Hcrd Hcwr Hcpp Hcip Hcmaj Hrpay Hrlv]
                                [Hpriv] [Hslot]").
                { exact Hcsf. }
                { apply uptd_ext_refl. }
                { apply filewrite_ret_m1. }
                { exact Hrv. }
                { iEval (rewrite /ret_tgt). iExact "Hpc". }
                { rewrite /file_ref /file_fields.
                  iFrame "Hrtok Hcty Hcrd Hcwr Hcpp Hcip Hcmaj Hrpay Hrlv". }
                { rewrite HVid. iExact "Hpriv". }
                { iApply (fw_env_out_dev fn Cf (fwn_used fn) Htyd).
                  iApply (fw_dev_in_back fn Cf Hin with "[%] Hslot").
                  by left. }
             ** (* ---- consolewrite: the INDIRECT CALL at +0x7e ---- *)
                iPoseProof (fwri_07c with "Htext") as "Hi7c".
                iPoseProof (fwri_07e with "Htext") as "Hi7e".
                iPoseProof (fwri_080 with "Htext") as "Hi80".
                iApply (wp_cbeqz_fall_s_sconf (mword_of_int (FW + 0x7a))
                          (mword_of_int 88 : mword 8) (Cregidx (mword_of_int 7)) Ra5
                          Dr (K - 12)%nat b Hc7 ltac:(vm_compute; discriminate)
                          ltac:(rewrite (rget_ne Dr Ra5 ltac:(vm_compute; discriminate))
                                  HDra5 Hwpc; apply eq_vec_false_iff;
                                intro Hc; apply (f_equal (@bv_unsigned _)) in Hc;
                                vm_compute in Hc; discriminate)
                          with "Hcg Hpc Hi7a [-]").
                iIntros (CID18 Hs18) "Hcg Hpc".
                assert (Hpp7c : add_vec_int (mword_of_int (FW + 0x7a) : mword 64) 2
                                = mword_of_int (FW + 0x7c)) by (apply bv_eq; vm_compute; reflexivity).
                iEval (rewrite Hpp7c) in "Hpc".
                (* +0x7c c.li a0,1 : the source is a USER address *)
                iApply (wp_cli_s_sconf (mword_of_int (FW + 0x7c)) Ra0
                          (mword_of_int 1 : mword 6) (mword_of_int 1 : mword 64)
                          Dr (K - 12)%nat b
                          ltac:(vm_compute; discriminate) ltac:(rdok) fr_li1
                          with "Hcg Hpc Hi7c [-]").
                iIntros (CID19 Hs19) "Hcg Hpc".
                set (E1 := <[Regidx Ra0 := regval_into_reg (mword_of_int 1 : mword 64)]> Dr).
                assert (HE1a5 : E1 !!! Regidx Ra5
                                = (mword_of_int KernelSyms.consolewrite : mword 64)).
                { rewrite /E1 upd_ne; [| vm_compute; discriminate].
                  rewrite HDra5. exact Hwpc. }
                assert (Hpp7e : add_vec_int (mword_of_int (FW + 0x7c) : mword 64) 2
                                = mword_of_int (FW + 0x7e)) by (apply bv_eq; vm_compute; reflexivity).
                iEval (rewrite Hpp7e) in "Hpc".
                (* +0x7e c.jalr a5 -- the indirect call *)
                iApply (wp_cjalr_s_sconf (mword_of_int (FW + 0x7e)) Ra5 Rra
                          E1 (K - 12)%nat b
                          ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                          ltac:(rdok) with "Hcg Hpc Hi7e [-]").
                iIntros (CID20 Hs20) "Hcg Hpc".
                set (E2 := <[Regidx Rra := regval_into_reg
                              (add_vec_int (mword_of_int (FW + 0x7e) : mword 64) 2)]> E1).
                (* [rgne] FIRST, so the [rget]'s hart instance is fixed by
                   unification rather than by whichever [CpuId] is ambient. *)
                iEval (rgne) in "Hpc".
                iEval (rewrite HE1a5 fw_ret_pc_cons) in "Hpc".
                assert (HE2a0 : E2 !!! Regidx Ra0 = (mword_of_int 1 : mword 64)).
                { rewrite /E2 upd_ne; [| vm_compute; discriminate].
                  rewrite /E1; apply upd_eq. }
                assert (HE2a2 : E2 !!! Regidx Ra2 = (mword_of_int n : mword 64)).
                { rewrite /E2 upd_ne; [| vm_compute; discriminate].
                  rewrite /E1 upd_ne; [| vm_compute; discriminate].
                  rewrite (HDrthr Ra2 ltac:(vm_compute; discriminate)
                            ltac:(vm_compute; discriminate)).
                  rewrite /D4 upd_ne; [| vm_compute; discriminate].
                  rewrite /D3 upd_ne; [| vm_compute; discriminate].
                  rewrite /D2 upd_ne; [| vm_compute; discriminate].
                  rewrite /D1 upd_ne; [| vm_compute; discriminate].
                  rewrite /G6 upd_ne; [| vm_compute; discriminate].
                  rewrite /G5 upd_ne; [| vm_compute; discriminate].
                  rewrite /G4 upd_ne; [| vm_compute; discriminate].
                  rewrite /G3 upd_ne; [| vm_compute; discriminate].
                  rewrite /G2 upd_ne; [| vm_compute; discriminate].
                  rewrite /G1 upd_ne; [exact HMa2 | vm_compute; discriminate]. }
                assert (HE2ra : E2 !!! Regidx Rra
                                = add_vec_int (mword_of_int (FW + 0x7e) : mword 64) 2)
                  by (rewrite /E2; apply upd_eq).
                assert (HE2sp : E2 !!! Regidx csp_rs1 = pa_stk sp0 12).
                { rewrite /E2 upd_ne; [| vm_compute; discriminate].
                  rewrite /E1 upd_ne; [exact HDrsp | vm_compute; discriminate]. }
                assert (HE2thr : forall c : mword 5, is_cs_idx c = true -> c <> csp_rs1 ->
                          c <> Rs0 -> c <> Rs2 -> c <> Rs5 -> c <> Rs6 ->
                          E2 !!! Regidx c = m !!! Regidx c).
                { intros c Hcs N2 N8 N18 N21 N22.
                  rewrite /E2 upd_ne; [| regne].
                  rewrite /E1 upd_ne; [| regne].
                  exact (HDrthrm c Hcs N2 N8 N18 N21 N22). }
                iDestruct (cpu_own_transport CID CID20 0%nat eb pj C b ltac:(wp_next_chain)
                             with "Hcnt") as "Hcnt".
                iApply (Consolewrite.wp_consolewrite_sconf γa γf γs j γlp
                          E2 (K - 12)%nat eb C pidv V n b
                          Hj Hgs Hlens HE2a0 HE2a2 (fw_n_range n Hn)
                          (fw_av_cons K HK) Heb
                          with "Hcg Hcnt Htext Hpc Hpriv Hkenv Hprocs Hpanic [-]").
                iIntros (CIDcw Hscw mf r P') "%Hcscw %Hupt %Hrr %Hra0 Hcg Hcnt Hpc Hpriv".
                assert (Hpc80 : ret_pc (E2 !!! Regidx Rra) = mword_of_int (FW + 0x80)).
                { rewrite HE2ra. apply bv_eq; vm_compute; reflexivity. }
                iEval (rewrite Hpc80) in "Hpc".
                pose proof Hcscw as Hcscw_cs.
                assert (Hmfsp : mf !!! Regidx csp_rs1 = pa_stk sp0 12).
                { rewrite (callee_saved_lookup Hcscw_cs csp_rs1 ltac:(vm_compute; reflexivity)).
                  exact HE2sp. }
                assert (Hmfthr : forall c : mword 5, is_cs_idx c = true -> c <> csp_rs1 ->
                          c <> Rs0 -> c <> Rs2 -> c <> Rs5 -> c <> Rs6 ->
                          mf !!! Regidx c = m !!! Regidx c).
                { intros c Hcs N2 N8 N18 N21 N22.
                  rewrite (callee_saved_lookup Hcscw_cs c Hcs).
                  exact (HE2thr c Hcs N2 N8 N18 N21 N22). }
                (* ---- +0x80 c.j -> +0xfc ---- *)
                assert (Htgtfcd : add_vec (mword_of_int (FW + 0x80) : mword 64)
                          (sign_extend' 64 (sign_extend' 21
                             (concat_vec (mword_of_int 62 : mword 11) ('b"0"))))
                          = mword_of_int (FW + 0xfc))
                  by (apply bv_eq; vm_compute; reflexivity).
                iApply (wp_cj_s_sconf (mword_of_int (FW + 0x80))
                          (sign_extend' 21 (concat_vec (mword_of_int 62 : mword 11) ('b"0")))
                          mf (K - 12)%nat b
                          ltac:(rewrite Htgtfcd; vm_compute; reflexivity)
                          with "Hcg Hpc Hi80 [-]").
                iIntros (CID21 Hs21). iNext. iIntros "Hcg Hpc".
                iEval (rewrite Htgtfcd) in "Hpc".
                iApply (fw_epi (CID0 := CID21) m mf K sp0 (m !!! Regidx Rra)
                          (m !!! Regidx Rs0) (m !!! Regidx Rs2) (m !!! Regidx Rs5)
                          (m !!! Regidx Rs6) (mword_of_int r)
                          w3 w5 w6 w9 w10 w11 w12 pj b
                          (fw_K12 K HK) Hspm eq_refl eq_refl eq_refl eq_refl eq_refl
                          Hmfsp Hra0 Hmfthr
                          with "Hcg Htext Hpc Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hb7 Hb8 Hb9 Hb10
                                Hb11 Hb12 [-]").
                iIntros (CIDe Hse mfin) "%Hcsr Hcg Hpc".
                destruct Hcsr as [Hcsf Hrv].
                iDestruct (cpu_own_transport CIDcw CIDe 0%nat eb pj C b ltac:(wp_next_chain)
                             with "Hcnt") as "Hcnt".
                iSpecialize ("Hcont" $! CIDe with "[]"); [iPureIntro; wp_next_chain|].
                iApply ("Hcont" $! mfin (mword_of_int r) P' (fwn_used fn)
                          with "[%] [%] [%] [%] Hcg Hcnt [Hpc]
                                [Hrtok Hcty Hcrd Hcwr Hcpp Hcip Hcmaj Hrpay Hrlv]
                                Hpriv [Hslot]").
                { exact Hcsf. }
                { exact Hupt. }
                { exact (fw_ret_of_dev n r (mword_of_int r) (proj1 Hn) Hrr eq_refl). }
                { exact Hrv. }
                { iEval (rewrite /ret_tgt). iExact "Hpc". }
                { rewrite /file_ref /file_fields.
                  iFrame "Hrtok Hcty Hcrd Hcwr Hcpp Hcip Hcmaj Hrpay Hrlv". }
                { iApply (fw_env_out_dev fn Cf (fwn_used fn) Htyd).
                  iApply (fw_dev_in_back fn Cf Hin with "[%] Hslot").
                  by right. }
          ++ (* ---------- OUT OF RANGE: the [bltu] is taken to +0x126 ------- *)
             assert (Hmjgt : (9 < bv_unsigned (fc_major Cf))%Z)
               by (unfold dev_major, NDEV_max in Hout; lia).
             iPoseProof (fwri_126 with "Htext") as "Hi126".
             iPoseProof (fwri_128 with "Htext") as "Hi128".
             assert (Htgt126 : add_vec (mword_of_int (FW + 0x68) : mword 64)
                       (sign_extend' 64 (mword_of_int 190 : mword 13))
                       = mword_of_int (FW + 0x126))
               by (apply bv_eq; vm_compute; reflexivity).
             iApply (wp_bltu_taken_s_sconf (mword_of_int (FW + 0x68))
                       (mword_of_int 190 : mword 13) Ra3 Ra4 D4 (K - 12)%nat b
                       ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                       ltac:(rewrite HD4a4 HD4a3;
                             exact (fw_bltu9_true _ Hmjgt (proj2 Hmjr)))
                       ltac:(rewrite Htgt126; vm_compute; reflexivity)
                       with "Hcg Hpc Hi68 [-]").
             iNext. iIntros (CID16 Hs16) "Hcg Hpc".
             iEval (rewrite Htgt126) in "Hpc".
             iApply (fw_m1j (CID0 := CID16) D4 (K - 12)%nat
                       (FW + 0x126) (FW + 0x128)
                       (sign_extend' 21 (concat_vec (mword_of_int 2026 : mword 11) ('b"0")))
                       pj b
                       ltac:(apply bv_eq; vm_compute; reflexivity)
                       ltac:(apply bv_eq; vm_compute; reflexivity)
                       with "Hcg Hpc Hi126 Hi128 [-]").
             iIntros (CID17 Hs17 Er) "%Her Hcg Hpc".
             destruct Her as (HEra0 & HErthr).
             assert (HErsp : Er !!! Regidx csp_rs1 = pa_stk sp0 12).
             { rewrite (HErthr csp_rs1 ltac:(vm_compute; reflexivity)). exact HD4sp. }
             assert (HErthr2 : forall c : mword 5, is_cs_idx c = true -> c <> csp_rs1 ->
                       c <> Rs0 -> c <> Rs2 -> c <> Rs5 -> c <> Rs6 ->
                       Er !!! Regidx c = m !!! Regidx c).
             { intros c Hcs N2 N8 N18 N21 N22.
               rewrite (HErthr c Hcs). exact (HD4thr c Hcs N2 N8 N18 N21 N22). }
             iApply (fw_epi (CID0 := CID17) m Er K sp0 (m !!! Regidx Rra)
                       (m !!! Regidx Rs0) (m !!! Regidx Rs2) (m !!! Regidx Rs5)
                       (m !!! Regidx Rs6) (mword_of_int (-1))
                       w3 w5 w6 w9 w10 w11 w12 pj b
                       (fw_K12 K HK) Hspm eq_refl eq_refl eq_refl eq_refl eq_refl
                       HErsp HEra0 HErthr2
                       with "Hcg Htext Hpc Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hb7 Hb8 Hb9 Hb10
                             Hb11 Hb12 [-]").
             iIntros (CIDe Hse mfin) "%Hcsr Hcg Hpc".
             destruct Hcsr as [Hcsf Hrv].
             iDestruct (cpu_own_transport CID CIDe 0%nat eb pj C b ltac:(wp_next_chain)
                          with "Hcnt") as "Hcnt".
             iSpecialize ("Hcont" $! CIDe with "[]"); [iPureIntro; wp_next_chain|].
             assert (HVid : upd_upt V (pv_upt V) = V) by apply fw_upd_upt_id.
             iApply ("Hcont" $! mfin (mword_of_int (-1)) (pv_upt V) (fwn_used fn)
                       with "[%] [%] [%] [%] Hcg Hcnt [Hpc]
                             [Hrtok Hcty Hcrd Hcwr Hcpp Hcip Hcmaj Hrpay Hrlv]
                             [Hpriv] [Henv]").
             { exact Hcsf. }
             { apply uptd_ext_refl. }
             { apply filewrite_ret_m1. }
             { exact Hrv. }
             { iEval (rewrite /ret_tgt). iExact "Hpc". }
             { rewrite /file_ref /file_fields.
               iFrame "Hrtok Hcty Hcrd Hcwr Hcpp Hcip Hcmaj Hrpay Hrlv". }
             { rewrite HVid. iExact "Hpriv". }
             { by iApply (fw_env_out_dev fn Cf (fwn_used fn) Htyd). }
        * (* ---- +0x2a c.li a4,2 ; +0x2c bne a5,a4 -> +0x10a (panic) ---- *)
          iApply (wp_beq_fall_s_sconf (mword_of_int (FW + 0x26))
                    (mword_of_int 54 : mword 13) Ra4 Ra5 G6 (K - 12)%nat b
                    ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                    ltac:(rewrite Hcmp3; first [exact Hp3 | reflexivity])
                    with "Hcg Hpc Hi26 [-]").
          iIntros (CID11 Hs11) "Hcg Hpc".
          assert (Hpp2a : add_vec_int (mword_of_int (FW + 0x26) : mword 64) 4
                          = mword_of_int (FW + 0x2a)) by (apply bv_eq; vm_compute; reflexivity).
          iEval (rewrite Hpp2a) in "Hpc".
          iApply (wp_cli_s_sconf (mword_of_int (FW + 0x2a)) Ra4
                    (mword_of_int 2 : mword 6) (mword_of_int 2 : mword 64)
                    G6 (K - 12)%nat b
                    ltac:(vm_compute; discriminate) ltac:(rdok) fr_li2
                    with "Hcg Hpc Hi2a [-]").
          iIntros (CID12 Hs12) "Hcg Hpc".
          set (G7 := <[Regidx Ra4 := regval_into_reg (mword_of_int 2 : mword 64)]> G6).
          assert (HG7a5 : rget G7 Ra5 = sign_extend' 64 (fc_type Cf)).
          { rewrite (rget_ne G7 Ra5 ltac:(vm_compute; discriminate)).
            rewrite /G7 upd_ne; [| vm_compute; discriminate].
            rewrite /G6 upd_ne; [| vm_compute; discriminate].
            rewrite /G5 upd_ne; [exact HG4a5 | vm_compute; discriminate]. }
          assert (HG7a4 : rget G7 Ra4 = (mword_of_int 2 : mword 64)).
          { rewrite (rget_ne G7 Ra4 ltac:(vm_compute; discriminate)).
            rewrite /G7; apply upd_eq. }
          (* BOTH forms, because the branch at +0x2c is a BNE and its two
             leaves state their premise over [neq_vec] -- whose ARGUMENTS are
             the two mwords, not an [eq_vec], so a [rewrite] of the [eq_vec]
             equation has nothing to match until [neq_vec] is unfolded.  This
             is fileread's [fr_ty_neqz] pair, and the reason it exists. *)
          assert (Hcmp2 : eq_vec (rget G7 Ra5) (rget G7 Ra4)
                          = eq_vec (fc_type Cf) (mword_of_int 2 : mword 32)).
          { rewrite HG7a5 HG7a4. apply fr_ty_eqz.
            change (2^31)%Z with 2147483648%Z. lia. }
          assert (Hncmp2 : neq_vec (rget G7 Ra5) (rget G7 Ra4)
                           = neq_vec (fc_type Cf) (mword_of_int 2 : mword 32)).
          { rewrite HG7a5 HG7a4. apply fr_ty_neqz.
            change (2^31)%Z with 2147483648%Z. lia. }
          assert (HG7sp : G7 !!! Regidx csp_rs1 = pa_stk sp0 12).
          { rewrite /G7 upd_ne; [exact HG6sp | vm_compute; discriminate]. }
          assert (HG7s2 : G7 !!! Regidx Rs2 = fnode k).
          { rewrite /G7 upd_ne; [exact HG6s2 | vm_compute; discriminate]. }
          assert (HG7s5 : G7 !!! Regidx Rs5 = (mword_of_int n : mword 64)).
          { rewrite /G7 upd_ne; [exact HG6s5 | vm_compute; discriminate]. }
          assert (HG7s6 : G7 !!! Regidx Rs6 = m !!! Regidx Ra1).
          { rewrite /G7 upd_ne; [exact HG6s6 | vm_compute; discriminate]. }
          assert (HG7thr : forall c : mword 5, is_cs_idx c = true -> c <> csp_rs1 ->
                    c <> Rs0 -> c <> Rs2 -> c <> Rs5 -> c <> Rs6 ->
                    G7 !!! Regidx c = m !!! Regidx c).
          { intros c Hcs N2 N8 N18 N21 N22.
            rewrite /G7 upd_ne; [| regne].
            exact (HG6thr c Hcs N2 N8 N18 N21 N22). }
          assert (Hpp2c : add_vec_int (mword_of_int (FW + 0x2a) : mword 64) 2
                          = mword_of_int (FW + 0x2c)) by (apply bv_eq; vm_compute; reflexivity).
          iEval (rewrite Hpp2c) in "Hpc".
          destruct (eq_vec (fc_type Cf) (mword_of_int 2 : mword 32)) eqn:Hp2.
          -- (* ======================= FD_INODE =======================
                s4 (the running [i]) is spilled at +0x30 and the [n <= 0]
                test at +0x32 is HOISTED above the other five spills, so the
                zero-trip path never writes slots 3/5/9/10/11 -- Parts'
                header fact 3, and the reason [fw_tail] takes them as
                arbitrary words. *)
             assert (Htyi : fc_type Cf = FD_INODE)
               by (apply eq_vec_true_iff; exact Hp2).
             iPoseProof (fwri_030 with "Htext") as "Hi30".
             iPoseProof (fwri_032 with "Htext") as "Hi32".
             (* the BNE FALLS exactly when the two are equal *)
             iApply (wp_bne_fall_s_sconf (mword_of_int (FW + 0x2c))
                       (mword_of_int 222 : mword 13) Ra4 Ra5 G7 (K - 12)%nat b
                       ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                       ltac:(rewrite Hncmp2; unfold neq_vec;
                             first [rewrite Hp2 | idtac]; reflexivity)
                       with "Hcg Hpc Hi2c [-]").
             { iIntros (CID13 Hs13) "Hcg Hpc".
               assert (Hpp30 : add_vec_int (mword_of_int (FW + 0x2c) : mword 64) 4
                               = mword_of_int (FW + 0x30))
                 by (apply bv_eq; vm_compute; reflexivity).
               iEval (rewrite Hpp30) in "Hpc".
               (* ---- +0x30 c.sdsp s4,48(sp) : the running [i]'s slot ---- *)
               assert (Hf6 : add_vec (G7 !!! Regidx csp_rs1)
                               (zero_extend' 64 (concat_vec (mword_of_int 6 : mword 6) ('b"000")))
                             = pa_stk sp0 6) by (rewrite HG7sp; apply fw_frm6).
               iEval (rewrite -Hf6) in "Hb6".
               iApply (wp_csdsp_s_sconf (mword_of_int (FW + 0x30))
                         (mword_of_int 6 : mword 6) Rs4 G7 (K - 12)%nat w6 b
                         with "Hcg Hpc Hi30 Hb6 [-]").
               iIntros (CID14 Hs14) "Hcg Hpc Hb6". iEval (rgne) in "Hb6".
               iEval (rewrite Hf6) in "Hb6".
               iEval (rewrite (HG7thr Rs4 ltac:(vm_compute; reflexivity)
                                ltac:(vm_compute; discriminate)
                                ltac:(vm_compute; discriminate)
                                ltac:(vm_compute; discriminate)
                                ltac:(vm_compute; discriminate)
                                ltac:(vm_compute; discriminate))) in "Hb6".
               assert (Hpp32 : add_vec_int (mword_of_int (FW + 0x30) : mword 64) 2
                               = mword_of_int (FW + 0x32))
                 by (apply bv_eq; vm_compute; reflexivity).
               iEval (rewrite Hpp32) in "Hpc".
               (* ---- +0x32 bge x0,a2 : the HOISTED zero-trip test ---- *)
               assert (HG7a2 : rget G7 Ra2 = (mword_of_int n : mword 64)).
               { rewrite (rget_ne G7 Ra2 ltac:(vm_compute; discriminate)).
                 rewrite /G7 upd_ne; [| vm_compute; discriminate].
                 rewrite /G6 upd_ne; [| vm_compute; discriminate].
                 rewrite /G5 upd_ne; [| vm_compute; discriminate].
                 rewrite /G4 upd_ne; [| vm_compute; discriminate].
                 rewrite /G3 upd_ne; [| vm_compute; discriminate].
                 rewrite /G2 upd_ne; [| vm_compute; discriminate].
                 rewrite /G1 upd_ne; [exact HMa2 | vm_compute; discriminate]. }
               assert (Hbge0 : zopz0zKzJ_s (zero_reg : mword 64) (rget G7 Ra2)
                               = Z.geb 0 n)
                 by (rewrite HG7a2; exact (fw_bge0_moi n Hn)).
               destruct (Z.geb 0 n) eqn:Hz0.
               - (* ---- n <= 0, so n = 0: the loop is never entered ---- *)
                 assert (Hnz0 : n = 0)
                   by (apply (fw_zero_trip n (proj1 Hn)); apply Z.geb_le; exact Hz0).
                 iPoseProof (fwri_0e6 with "Htext") as "Hie6".
                 iPoseProof (fwri_0e8 with "Htext") as "Hie8".
                 assert (Htgte6 : add_vec (mword_of_int (FW + 0x32) : mword 64)
                           (sign_extend' 64 (mword_of_int 180 : mword 13))
                           = mword_of_int (FW + 0xe6))
                   by (apply bv_eq; vm_compute; reflexivity).
                 iApply (wp_bge_x0_taken_s_sconf (mword_of_int (FW + 0x32))
                           (mword_of_int 180 : mword 13) Ra2 G7 (K - 12)%nat b
                           ltac:(vm_compute; discriminate)
                           (* [destruct ... eqn:Hz0] rewrote [Hbge0]'s RHS
                              along with the goal, so [Hbge0] IS the premise
                              already -- a [rewrite Hbge0; exact Hz0] would
                              leave [true = true] and then fail on the type. *)
                           ltac:(first [exact Hbge0 | rewrite Hbge0; exact Hz0])
                           ltac:(rewrite Htgte6; vm_compute; reflexivity)
                           with "Hcg Hpc Hi32 [-]").
                 iNext. iIntros (CID15 Hs15) "Hcg Hpc".
                 iEval (rewrite Htgte6) in "Hpc".
                 (* ---- +0xe6 c.li s4,0 ---- *)
                 iApply (wp_cli_s_sconf (mword_of_int (FW + 0xe6)) Rs4
                           (mword_of_int 0 : mword 6) (mword_of_int 0 : mword 64)
                           G7 (K - 12)%nat b
                           ltac:(vm_compute; discriminate) ltac:(rdok) fw_li0
                           with "Hcg Hpc Hie6 [-]").
                 iIntros (CID16 Hs16) "Hcg Hpc".
                 set (Z1 := <[Regidx Rs4 := regval_into_reg
                               (mword_of_int 0 : mword 64)]> G7).
                 assert (HZ1s4 : Z1 !!! Regidx Rs4 = (mword_of_int 0 : mword 64))
                   by (rewrite /Z1; apply upd_eq).
                 assert (HZ1s5 : Z1 !!! Regidx Rs5 = (mword_of_int n : mword 64))
                   by (rewrite /Z1 upd_ne; [exact HG7s5 | vm_compute; discriminate]).
                 assert (HZ1sp : Z1 !!! Regidx csp_rs1 = pa_stk sp0 12)
                   by (rewrite /Z1 upd_ne; [exact HG7sp | vm_compute; discriminate]).
                 assert (HZ1thr : forall c : mword 5, is_cs_idx c = true -> c <> csp_rs1 ->
                           c <> Rs0 -> c <> Rs2 -> c <> Rs4 -> c <> Rs5 -> c <> Rs6 ->
                           Z1 !!! Regidx c = m !!! Regidx c).
                 { intros c Hcs N2 N8 N18 N20 N21 N22.
                   rewrite /Z1 upd_ne; [| regne].
                   exact (HG7thr c Hcs N2 N8 N18 N21 N22). }
                 assert (Hppe8 : add_vec_int (mword_of_int (FW + 0xe6) : mword 64) 2
                                 = mword_of_int (FW + 0xe8))
                   by (apply bv_eq; vm_compute; reflexivity).
                 iEval (rewrite Hppe8) in "Hpc".
                 (* ---- +0xe8 c.j -> +0xf4 ---- *)
                 assert (Htgtf4 : add_vec (mword_of_int (FW + 0xe8) : mword 64)
                           (sign_extend' 64 (sign_extend' 21
                              (concat_vec (mword_of_int 6 : mword 11) ('b"0"))))
                           = mword_of_int (FW + 0xf4))
                   by (apply bv_eq; vm_compute; reflexivity).
                 iApply (wp_cj_s_sconf (mword_of_int (FW + 0xe8))
                           (sign_extend' 21 (concat_vec (mword_of_int 6 : mword 11) ('b"0")))
                           Z1 (K - 12)%nat b
                           ltac:(rewrite Htgtf4; vm_compute; reflexivity)
                           with "Hcg Hpc Hie8 [-]").
                 iIntros (CID17 Hs17). iNext. iIntros "Hcg Hpc".
                 iEval (rewrite Htgtf4) in "Hpc".
                 (* ---- +0xf4 .. : [fw_tail], at [i = 0] and [n = 0] ---- *)
                 iApply (fw_tail (CID0 := CID17) m Z1 K sp0 (m !!! Regidx Rra)
                           (m !!! Regidx Rs0) (m !!! Regidx Rs2) (m !!! Regidx Rs4)
                           (m !!! Regidx Rs5) (m !!! Regidx Rs6) n 0
                           w3 w5 w9 w10 w11 w12 pj b
                           (fw_K12 K HK) Hn ltac:(lia) Hspm eq_refl eq_refl eq_refl
                           eq_refl eq_refl eq_refl HZ1sp HZ1s5 HZ1s4 HZ1thr
                           with "Hcg Htext Hpc Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hb7 Hb8 Hb9
                                 Hb10 Hb11 Hb12 [-]").
                 iIntros (CIDe Hse mfin rv) "%Hcsr Hcg Hpc".
                 destruct Hcsr as (Hcsf & Hrv & Hdisj).
                 iDestruct (cpu_own_transport CID CIDe 0%nat eb pj C b
                              ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
                 iSpecialize ("Hcont" $! CIDe with "[]"); [iPureIntro; wp_next_chain|].
                 assert (HVid : upd_upt V (pv_upt V) = V) by apply fw_upd_upt_id.
                 iApply ("Hcont" $! mfin rv (pv_upt V) (fwn_used fn)
                           with "[%] [%] [%] [%] Hcg Hcnt [Hpc]
                                 [Hrtok Hcty Hcrd Hcwr Hcpp Hcip Hcmaj Hrpay Hrlv]
                                 [Hpriv] [Henv]").
                 { exact Hcsf. }
                 { apply uptd_ext_refl. }
                 { exact (fw_ret_of_tail n n 0 rv (proj1 Hn) eq_refl Hdisj). }
                 { exact Hrv. }
                 { iEval (rewrite /ret_tgt). iExact "Hpc". }
                 { rewrite /file_ref /file_fields.
                   iFrame "Hrtok Hcty Hcrd Hcwr Hcpp Hcip Hcmaj Hrpay Hrlv". }
                 { rewrite HVid. iExact "Hpriv". }
                 { by iApply filewrite_env_out_of_env. }
               - (* ---- 0 < n: the five late spills, the two 3072s, and
                      the jump to the BOTTOM test at +0xcc ---- *)
                 (* [0 < n] here, from [Hz0 : (0 >=? n) = false]; the loop
                    lemma is the first thing that needs it, so it is left to
                    be derived there rather than asserted into a context that
                    is already full of [mword]s. *)
                 iPoseProof (fwri_036 with "Htext") as "Hi36".
                 iPoseProof (fwri_038 with "Htext") as "Hi38".
                 iPoseProof (fwri_03a with "Htext") as "Hi3a".
                 iPoseProof (fwri_03c with "Htext") as "Hi3c".
                 iPoseProof (fwri_03e with "Htext") as "Hi3e".
                 iPoseProof (fwri_040 with "Htext") as "Hi40".
                 iPoseProof (fwri_042 with "Htext") as "Hi42".
                 iPoseProof (fwri_044 with "Htext") as "Hi44".
                 iPoseProof (fwri_048 with "Htext") as "Hi48".
                 iPoseProof (fwri_04a with "Htext") as "Hi4a".
                 iPoseProof (fwri_04e with "Htext") as "Hi4e".
                 iPoseProof (fwri_050 with "Htext") as "Hi50".
                 iPoseProof (fwri_052 with "Htext") as "Hi52".
                 iApply (wp_bge_x0_fall_s_sconf (mword_of_int (FW + 0x32))
                           (mword_of_int 180 : mword 13) Ra2 G7 (K - 12)%nat b
                           ltac:(vm_compute; discriminate)
                           ltac:(first [exact Hbge0 | rewrite Hbge0; exact Hz0])
                           with "Hcg Hpc Hi32 [-]").
                 iIntros (CID15 Hs15) "Hcg Hpc".
                 assert (Hpp36 : add_vec_int (mword_of_int (FW + 0x32) : mword 64) 4
                                 = mword_of_int (FW + 0x36))
                   by (apply bv_eq; vm_compute; reflexivity).
                 iEval (rewrite Hpp36) in "Hpc".
                 (* the five [c.sdsp]s of Parts' header fact 3.  None of them
                    touches a register, so the map stays [G7] throughout. *)
                 assert (Hf3 : add_vec (G7 !!! Regidx csp_rs1)
                                 (zero_extend' 64 (concat_vec (mword_of_int 9 : mword 6) ('b"000")))
                               = pa_stk sp0 3) by (rewrite HG7sp; apply fw_frm3).
                 assert (Hf5 : add_vec (G7 !!! Regidx csp_rs1)
                                 (zero_extend' 64 (concat_vec (mword_of_int 7 : mword 6) ('b"000")))
                               = pa_stk sp0 5) by (rewrite HG7sp; apply fw_frm5).
                 assert (Hf9 : add_vec (G7 !!! Regidx csp_rs1)
                                 (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000")))
                               = pa_stk sp0 9) by (rewrite HG7sp; apply fw_frm9).
                 assert (Hf10 : add_vec (G7 !!! Regidx csp_rs1)
                                  (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000")))
                                = pa_stk sp0 10) by (rewrite HG7sp; apply fw_frm10).
                 assert (Hf11 : add_vec (G7 !!! Regidx csp_rs1)
                                  (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000")))
                                = pa_stk sp0 11) by (rewrite HG7sp; apply fw_frm11).
                 iEval (rewrite -Hf3) in "Hb3".
                 iApply (wp_csdsp_s_sconf (mword_of_int (FW + 0x36))
                           (mword_of_int 9 : mword 6) Rs1 G7 (K - 12)%nat w3 b
                           with "Hcg Hpc Hi36 Hb3 [-]").
                 iIntros (CID16 Hs16) "Hcg Hpc Hb3". iEval (rgne) in "Hb3".
                 iEval (rewrite Hf3) in "Hb3".
                 iEval (rewrite (HG7thr Rs1 ltac:(vm_compute; reflexivity)
                                  ltac:(vm_compute; discriminate)
                                  ltac:(vm_compute; discriminate)
                                  ltac:(vm_compute; discriminate)
                                  ltac:(vm_compute; discriminate)
                                  ltac:(vm_compute; discriminate))) in "Hb3".
                 assert (Hpp38 : add_vec_int (mword_of_int (FW + 0x36) : mword 64) 2
                                 = mword_of_int (FW + 0x38))
                   by (apply bv_eq; vm_compute; reflexivity).
                 iEval (rewrite Hpp38) in "Hpc".
                 iEval (rewrite -Hf5) in "Hb5".
                 iApply (wp_csdsp_s_sconf (mword_of_int (FW + 0x38))
                           (mword_of_int 7 : mword 6) Rs3 G7 (K - 12)%nat w5 b
                           with "Hcg Hpc Hi38 Hb5 [-]").
                 iIntros (CID17 Hs17) "Hcg Hpc Hb5". iEval (rgne) in "Hb5".
                 iEval (rewrite Hf5) in "Hb5".
                 iEval (rewrite (HG7thr Rs3 ltac:(vm_compute; reflexivity)
                                  ltac:(vm_compute; discriminate)
                                  ltac:(vm_compute; discriminate)
                                  ltac:(vm_compute; discriminate)
                                  ltac:(vm_compute; discriminate)
                                  ltac:(vm_compute; discriminate))) in "Hb5".
                 assert (Hpp3a : add_vec_int (mword_of_int (FW + 0x38) : mword 64) 2
                                 = mword_of_int (FW + 0x3a))
                   by (apply bv_eq; vm_compute; reflexivity).
                 iEval (rewrite Hpp3a) in "Hpc".
                 iEval (rewrite -Hf9) in "Hb9".
                 iApply (wp_csdsp_s_sconf (mword_of_int (FW + 0x3a))
                           (mword_of_int 3 : mword 6) Rs7 G7 (K - 12)%nat w9 b
                           with "Hcg Hpc Hi3a Hb9 [-]").
                 iIntros (CID18 Hs18) "Hcg Hpc Hb9". iEval (rgne) in "Hb9".
                 iEval (rewrite Hf9) in "Hb9".
                 iEval (rewrite (HG7thr Rs7 ltac:(vm_compute; reflexivity)
                                  ltac:(vm_compute; discriminate)
                                  ltac:(vm_compute; discriminate)
                                  ltac:(vm_compute; discriminate)
                                  ltac:(vm_compute; discriminate)
                                  ltac:(vm_compute; discriminate))) in "Hb9".
                 assert (Hpp3c : add_vec_int (mword_of_int (FW + 0x3a) : mword 64) 2
                                 = mword_of_int (FW + 0x3c))
                   by (apply bv_eq; vm_compute; reflexivity).
                 iEval (rewrite Hpp3c) in "Hpc".
                 iEval (rewrite -Hf10) in "Hb10".
                 iApply (wp_csdsp_s_sconf (mword_of_int (FW + 0x3c))
                           (mword_of_int 2 : mword 6) Rs8 G7 (K - 12)%nat w10 b
                           with "Hcg Hpc Hi3c Hb10 [-]").
                 iIntros (CID19 Hs19) "Hcg Hpc Hb10". iEval (rgne) in "Hb10".
                 iEval (rewrite Hf10) in "Hb10".
                 iEval (rewrite (HG7thr Rs8 ltac:(vm_compute; reflexivity)
                                  ltac:(vm_compute; discriminate)
                                  ltac:(vm_compute; discriminate)
                                  ltac:(vm_compute; discriminate)
                                  ltac:(vm_compute; discriminate)
                                  ltac:(vm_compute; discriminate))) in "Hb10".
                 assert (Hpp3e : add_vec_int (mword_of_int (FW + 0x3c) : mword 64) 2
                                 = mword_of_int (FW + 0x3e))
                   by (apply bv_eq; vm_compute; reflexivity).
                 iEval (rewrite Hpp3e) in "Hpc".
                 iEval (rewrite -Hf11) in "Hb11".
                 iApply (wp_csdsp_s_sconf (mword_of_int (FW + 0x3e))
                           (mword_of_int 1 : mword 6) Rs9 G7 (K - 12)%nat w11 b
                           with "Hcg Hpc Hi3e Hb11 [-]").
                 iIntros (CID20 Hs20) "Hcg Hpc Hb11". iEval (rgne) in "Hb11".
                 iEval (rewrite Hf11) in "Hb11".
                 iEval (rewrite (HG7thr Rs9 ltac:(vm_compute; reflexivity)
                                  ltac:(vm_compute; discriminate)
                                  ltac:(vm_compute; discriminate)
                                  ltac:(vm_compute; discriminate)
                                  ltac:(vm_compute; discriminate)
                                  ltac:(vm_compute; discriminate))) in "Hb11".
                 assert (Hpp40 : add_vec_int (mword_of_int (FW + 0x3e) : mword 64) 2
                                 = mword_of_int (FW + 0x40))
                   by (apply bv_eq; vm_compute; reflexivity).
                 iEval (rewrite Hpp40) in "Hpc".
                 (* ---- +0x40 c.li s4,0 : [i := 0] ---- *)
                 iApply (wp_cli_s_sconf (mword_of_int (FW + 0x40)) Rs4
                           (mword_of_int 0 : mword 6) (mword_of_int 0 : mword 64)
                           G7 (K - 12)%nat b
                           ltac:(vm_compute; discriminate) ltac:(rdok) fw_li0
                           with "Hcg Hpc Hi40 [-]").
                 iIntros (CID21 Hs21) "Hcg Hpc".
                 set (L1 := <[Regidx Rs4 := regval_into_reg
                               (mword_of_int 0 : mword 64)]> G7).
                 assert (Hpp42 : add_vec_int (mword_of_int (FW + 0x40) : mword 64) 2
                                 = mword_of_int (FW + 0x42))
                   by (apply bv_eq; vm_compute; reflexivity).
                 iEval (rewrite Hpp42) in "Hpc".
                 (* ---- +0x42 c.lui s7,0x1 ; +0x44 addi s7,s7,-1024 : 3072 ---- *)
                 iApply (wp_clui_s_sconf (mword_of_int (FW + 0x42)) Rs7
                           (sign_extend' 20 (mword_of_int 1 : mword 6))
                           (mword_of_int 4096 : mword 64) L1 (K - 12)%nat b
                           ltac:(vm_compute; discriminate) ltac:(rdok) fw_lui1
                           with "Hcg Hpc Hi42 [-]").
                 iIntros (CID22 Hs22) "Hcg Hpc".
                 set (L2 := <[Regidx Rs7 := regval_into_reg
                               (mword_of_int 4096 : mword 64)]> L1).
                 assert (Hpp44 : add_vec_int (mword_of_int (FW + 0x42) : mword 64) 2
                                 = mword_of_int (FW + 0x44))
                   by (apply bv_eq; vm_compute; reflexivity).
                 iEval (rewrite Hpp44) in "Hpc".
                 iApply (wp_addi4_s_sconf (mword_of_int (FW + 0x44)) Rs7 Rs7
                           (mword_of_int 3072 : mword 12) L2 (K - 12)%nat b
                           ltac:(vm_compute; discriminate) ltac:(rdok)
                           with "Hcg Hpc Hi44 [-]").
                 iIntros (CID23 Hs23) "Hcg Hpc". iEval (rgne) in "Hcg".
                 set (L3 := <[Regidx Rs7 := regval_into_reg
                               (add_vec (L2 !!! Regidx Rs7)
                                  (sign_extend' 64 (mword_of_int 3072 : mword 12)))]> L2).
                 assert (HL3s7 : L3 !!! Regidx Rs7
                                 = (mword_of_int SpecFilewrite.FW_MAX : mword 64)).
                 { rewrite /L3 upd_eq. unfold regval_into_reg.
                   rewrite /L2 upd_eq. exact fw_addi_m1024. }
                 assert (Hpp48 : add_vec_int (mword_of_int (FW + 0x44) : mword 64) 4
                                 = mword_of_int (FW + 0x48))
                   by (apply bv_eq; vm_compute; reflexivity).
                 iEval (rewrite Hpp48) in "Hpc".
                 (* ---- +0x48 c.lui a5,0x1 ; +0x4a addiw a5,a5,-1024 : again ---- *)
                 iApply (wp_clui_s_sconf (mword_of_int (FW + 0x48)) Ra5
                           (sign_extend' 20 (mword_of_int 1 : mword 6))
                           (mword_of_int 4096 : mword 64) L3 (K - 12)%nat b
                           ltac:(vm_compute; discriminate) ltac:(rdok) fw_lui1
                           with "Hcg Hpc Hi48 [-]").
                 iIntros (CID24 Hs24) "Hcg Hpc".
                 set (L4 := <[Regidx Ra5 := regval_into_reg
                               (mword_of_int 4096 : mword 64)]> L3).
                 assert (Hpp4a : add_vec_int (mword_of_int (FW + 0x48) : mword 64) 2
                                 = mword_of_int (FW + 0x4a))
                   by (apply bv_eq; vm_compute; reflexivity).
                 iEval (rewrite Hpp4a) in "Hpc".
                 iApply (wp_addiw_s_sconf (mword_of_int (FW + 0x4a)) Ra5 Ra5
                           (mword_of_int 3072 : mword 12) L4 (K - 12)%nat b
                           ltac:(vm_compute; discriminate) ltac:(rdok)
                           with "Hcg Hpc Hi4a [-]").
                 iIntros (CID25 Hs25) "Hcg Hpc". iEval (rgne) in "Hcg".
                 set (L5 := <[Regidx Ra5 := regval_into_reg
                               (sign_extend' 64 (subrange_vec_dec
                                  (add_vec (L4 !!! Regidx Ra5)
                                     (sign_extend' 64 (mword_of_int 3072 : mword 12)))
                                  31 0))]> L4).
                 assert (HL5a5 : L5 !!! Regidx Ra5
                                 = (mword_of_int SpecFilewrite.FW_MAX : mword 64)).
                 { rewrite /L5 upd_eq. unfold regval_into_reg.
                   rewrite /L4 upd_eq. exact fw_addiw_m1024. }
                 assert (Hpp4e : add_vec_int (mword_of_int (FW + 0x4a) : mword 64) 4
                                 = mword_of_int (FW + 0x4e))
                   by (apply bv_eq; vm_compute; reflexivity).
                 iEval (rewrite Hpp4e) in "Hpc".
                 (* ---- +0x4e c.mv s9,a5 ; +0x50 c.li s8,1 ---- *)
                 iApply (wp_cmv_s_sconf (mword_of_int (FW + 0x4e)) Rs9 Ra5
                           L5 (K - 12)%nat b
                           ltac:(vm_compute; discriminate) ltac:(rdok)
                           with "Hcg Hpc Hi4e [-]").
                 iIntros (CID26 Hs26) "Hcg Hpc". iEval (rgne) in "Hcg".
                 set (L6 := <[Regidx Rs9 := regval_into_reg
                               (add_vec zero_reg (L5 !!! Regidx Ra5))]> L5).
                 assert (HL6s9 : L6 !!! Regidx Rs9
                                 = (mword_of_int SpecFilewrite.FW_MAX : mword 64)).
                 { rewrite /L6 upd_eq. unfold regval_into_reg.
                   rewrite add_vec_zero_l. exact HL5a5. }
                 assert (Hpp50 : add_vec_int (mword_of_int (FW + 0x4e) : mword 64) 2
                                 = mword_of_int (FW + 0x50))
                   by (apply bv_eq; vm_compute; reflexivity).
                 iEval (rewrite Hpp50) in "Hpc".
                 iApply (wp_cli_s_sconf (mword_of_int (FW + 0x50)) Rs8
                           (mword_of_int 1 : mword 6) (mword_of_int 1 : mword 64)
                           L6 (K - 12)%nat b
                           ltac:(vm_compute; discriminate) ltac:(rdok) fr_li1
                           with "Hcg Hpc Hi50 [-]").
                 iIntros (CID27 Hs27) "Hcg Hpc".
                 set (L7 := <[Regidx Rs8 := regval_into_reg
                               (mword_of_int 1 : mword 64)]> L6).
                 assert (HL7s8 : L7 !!! Regidx Rs8 = (mword_of_int 1 : mword 64))
                   by (rewrite /L7; apply upd_eq).
                 assert (HL7s9 : L7 !!! Regidx Rs9
                                 = (mword_of_int SpecFilewrite.FW_MAX : mword 64))
                   by (rewrite /L7 upd_ne; [exact HL6s9 | vm_compute; discriminate]).
                 assert (HL7s7 : L7 !!! Regidx Rs7
                                 = (mword_of_int SpecFilewrite.FW_MAX : mword 64)).
                 { rewrite /L7 upd_ne; [| vm_compute; discriminate].
                   rewrite /L6 upd_ne; [| vm_compute; discriminate].
                   rewrite /L5 upd_ne; [| vm_compute; discriminate].
                   rewrite /L4 upd_ne; [exact HL3s7 | vm_compute; discriminate]. }
                 assert (HL7s4 : L7 !!! Regidx Rs4 = (mword_of_int 0 : mword 64)).
                 { rewrite /L7 upd_ne; [| vm_compute; discriminate].
                   rewrite /L6 upd_ne; [| vm_compute; discriminate].
                   rewrite /L5 upd_ne; [| vm_compute; discriminate].
                   rewrite /L4 upd_ne; [| vm_compute; discriminate].
                   rewrite /L3 upd_ne; [| vm_compute; discriminate].
                   rewrite /L2 upd_ne; [| vm_compute; discriminate].
                   rewrite /L1; apply upd_eq. }
                 assert (HL7s5 : L7 !!! Regidx Rs5 = (mword_of_int n : mword 64)).
                 { rewrite /L7 upd_ne; [| vm_compute; discriminate].
                   rewrite /L6 upd_ne; [| vm_compute; discriminate].
                   rewrite /L5 upd_ne; [| vm_compute; discriminate].
                   rewrite /L4 upd_ne; [| vm_compute; discriminate].
                   rewrite /L3 upd_ne; [| vm_compute; discriminate].
                   rewrite /L2 upd_ne; [| vm_compute; discriminate].
                   rewrite /L1 upd_ne; [exact HG7s5 | vm_compute; discriminate]. }
                 assert (HL7s2 : L7 !!! Regidx Rs2 = fnode k).
                 { rewrite /L7 upd_ne; [| vm_compute; discriminate].
                   rewrite /L6 upd_ne; [| vm_compute; discriminate].
                   rewrite /L5 upd_ne; [| vm_compute; discriminate].
                   rewrite /L4 upd_ne; [| vm_compute; discriminate].
                   rewrite /L3 upd_ne; [| vm_compute; discriminate].
                   rewrite /L2 upd_ne; [| vm_compute; discriminate].
                   rewrite /L1 upd_ne; [exact HG7s2 | vm_compute; discriminate]. }
                 assert (HL7s6 : L7 !!! Regidx Rs6 = m !!! Regidx Ra1).
                 { rewrite /L7 upd_ne; [| vm_compute; discriminate].
                   rewrite /L6 upd_ne; [| vm_compute; discriminate].
                   rewrite /L5 upd_ne; [| vm_compute; discriminate].
                   rewrite /L4 upd_ne; [| vm_compute; discriminate].
                   rewrite /L3 upd_ne; [| vm_compute; discriminate].
                   rewrite /L2 upd_ne; [| vm_compute; discriminate].
                   rewrite /L1 upd_ne; [exact HG7s6 | vm_compute; discriminate]. }
                 assert (HL7sp : L7 !!! Regidx csp_rs1 = pa_stk sp0 12).
                 { rewrite /L7 upd_ne; [| vm_compute; discriminate].
                   rewrite /L6 upd_ne; [| vm_compute; discriminate].
                   rewrite /L5 upd_ne; [| vm_compute; discriminate].
                   rewrite /L4 upd_ne; [| vm_compute; discriminate].
                   rewrite /L3 upd_ne; [| vm_compute; discriminate].
                   rewrite /L2 upd_ne; [| vm_compute; discriminate].
                   rewrite /L1 upd_ne; [exact HG7sp | vm_compute; discriminate]. }
                 assert (HL7thr : forall c : mword 5, is_cs_idx c = true -> c <> csp_rs1 ->
                           c <> Rs0 -> c <> Rs2 -> c <> Rs4 -> c <> Rs5 -> c <> Rs6 ->
                           c <> Rs7 -> c <> Rs8 -> c <> Rs9 ->
                           L7 !!! Regidx c = m !!! Regidx c).
                 { intros c Hcs N2 N8 N18 N20 N21 N22 N23 N24 N25.
                   rewrite /L7 upd_ne; [| regne].
                   rewrite /L6 upd_ne; [| regne].
                   rewrite /L5 upd_ne; [| regne].
                   rewrite /L4 upd_ne; [| regne].
                   rewrite /L3 upd_ne; [| regne].
                   rewrite /L2 upd_ne; [| regne].
                   rewrite /L1 upd_ne; [| regne].
                   exact (HG7thr c Hcs N2 N8 N18 N21 N22). }
                 assert (Hpp52 : add_vec_int (mword_of_int (FW + 0x50) : mword 64) 2
                                 = mword_of_int (FW + 0x52))
                   by (apply bv_eq; vm_compute; reflexivity).
                 iEval (rewrite Hpp52) in "Hpc".
                 (* ---- +0x52 c.j -> +0xcc : the loop is BOTTOM-TESTED ---- *)
                 assert (Htgtcc : add_vec (mword_of_int (FW + 0x52) : mword 64)
                           (sign_extend' 64 (sign_extend' 21
                              (concat_vec (mword_of_int 61 : mword 11) ('b"0"))))
                           = mword_of_int (FW + 0xcc))
                   by (apply bv_eq; vm_compute; reflexivity).
                 iApply (wp_cj_s_sconf (mword_of_int (FW + 0x52))
                           (sign_extend' 21 (concat_vec (mword_of_int 61 : mword 11) ('b"0")))
                           L7 (K - 12)%nat b
                           ltac:(rewrite Htgtcc; vm_compute; reflexivity)
                           with "Hcg Hpc Hi52 [-]").
                 iIntros (CID28 Hs28). iNext. iIntros "Hcg Hpc".
                 iEval (rewrite Htgtcc) in "Hpc".
                 (* ############### FRONTIER (S3q) ###############
                    PARKED AT +0xcc, THE LOOP TEST, and nothing before it is
                    parked: the whole of filewrite except the loop BODY is
                    proved above.  What is left is exactly the [∀]-fuel loop
                    lemma at [n - i] (ProofWritei's [wi_loop] shape, one level
                    up), whose iteration is
                      begin_op -> ilock at [s/2] ([fw_shr_gen_halve]) ->
                      the re-park ([fw_inode_ok_rebuild] + [fw_dir_ok_wi] +
                      [ity_shot_agree]) -> writei ([fw_writei_src] both
                      directions, [fw_budget_ok] + [fw_max_bridge] for the
                      cost premise) -> the f->off update ([off_checkout] /
                      [off_checkin]) -> iunlock ([fw_shr_regen]) -> end_op ->
                      break/continue, joining through [fw_rest5] into
                      [fw_tail].
                    The state it must be given: [L7] with s4 = 0, s5 = n,
                    s7 = s9 = FW_MAX, s8 = 1, s2 = f, s6 = addr, sp pushed;
                    the twelve frame slots; and the FD_INODE environment,
                    still packed in "Henv" at [Htyi].
                    Every premise of every call in that body was cleared by
                    hand in S3o and the last of them discharged as
                    [fw_writei_src] in S3p, so nothing below is BLOCKED --
                    only unwritten. *)
                 (* ---- THE FD_INODE LOOP.  [Hz0] left exactly one thing
                    undone on this path: [0 < n].  [Z.geb_le] is the only
                    direction that exists (there is no [Z.geb_gt]), so the
                    strict form is derived by cases. ---- *)
                 assert (Hpos : (0 < n)%Z).
                 { destruct (Z.le_gt_cases n 0) as [Hle | Hgt]; [| exact Hgt].
                   exfalso. rewrite (proj2 (Z.geb_le 0 n) Hle) in Hz0. discriminate. }
                 iPoseProof (fw_env_fs _ _ _ _ _ Htyi with "Henv") as "Henv".
                 iEval (rewrite /filewrite_fs_env) in "Henv".
                 iDestruct "Henv" as "(%E1 & %E2 & %E3 & %E4 & %E5 & %E6 & %E7 & %E8 & %E9 & #E10 & #E11 & #E12 & #E13 & #E14 & #E15 & #E16 & #E17 & #E18 & #E19 & #E20 & E21 & #E22 & %E23 & E24 & E25 & E26 & E27 & #E28 & #E29 & #E30 & E31)".
                 assert (HVid : upd_upt V (pv_upt V) = V) by apply fw_upd_upt_id.
                 (* [cpu_own] IS HART-INDEXED and the loop lemma states it at
                    ITS OWN [CID0]; the walk still holds the ENTRY hart's copy.
                    One transport, exactly as the -1 exit does before [Hcont]. *)
                 iDestruct (cpu_own_transport CID CID28 0%nat eb pj C b
                              ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
                 iApply (fw_loop (CID0 := CID28) γa γf γs j γlp k q Cf fn pidv V
                           m K eb C n b sp0 w12 pj
                           HK Hk Hj Hgs Hlens Hfnj Hfnps Hn Heb Htyi Hwb Hspm
                           ltac:(reflexivity)
                           E1 E2 E3 E4 E5 E6 E7 E8 E9 E23
                           (Z.to_nat n) 0%Z (pv_upt V) (fwn_used fn) L7
                           ltac:(rewrite (Z2Nat.id n (proj1 Hn)); lia)
                           ltac:(lia)
                           ltac:(apply uptd_ext_refl)
                           HL7sp HL7s2 HL7s4 HL7s5 HL7s6 HL7s7 HL7s8 HL7s9
                           ltac:(intros r Hr A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11;
                                 exact (HL7thr r Hr A1 A2 A4 A6 A7 A8 A9 A10 A11))
                           with "Hcg Hcnt Htext Hpc Hpanic Hprocs
                                 Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hb7 Hb8 Hb9 Hb10 Hb11 Hb12
                                 [Hrtok Hcty Hcrd Hcwr Hcpp Hcip Hcmaj Hrpay Hrlv]
                                 [Hpriv] Hkenv
                                 E10 E11 E12 E13 E14 E15 E16 E17 E18 E19 E20 E22
                                 E28 E29 E30 [E21 E24 E25 E26 E27 E31] [-]").
                 { rewrite /file_ref /file_fields.
                   iFrame "Hrtok Hcty Hcrd Hcwr Hcpp Hcip Hcmaj Hrpay Hrlv". }
                 { rewrite HVid. iExact "Hpriv". }
                 { rewrite /filewrite_fs_out.
                   iSplitR; [iPureIntro; reflexivity|].
                   iFrame "E21 E24 E25 E26 E27 E31". }
                 iIntros (CIDx Hsx mf rv P' used')
                   "%Hcs %Hup %Hret %Hra Hcg Hcnt Hpc Href Hpriv Henvo".
                 iSpecialize ("Hcont" $! CIDx with "[]"); [iPureIntro; wp_next_chain|].
                 iApply ("Hcont" $! mf rv P' used'
                           with "[%] [%] [%] [%] Hcg Hcnt Hpc Href Hpriv Henvo").
                 { exact Hcs. }
                 { exact Hup. }
                 { exact Hret. }
                 { exact Hra. } }
          -- (* ==================== THE ELSE ARM ======================
                Neither pipe, nor device, nor inode: [panic("filewrite")]
                at +0x11e, and [fw_panic] is the whole block from +0x10a. *)
             assert (Htgt10a : add_vec (mword_of_int (FW + 0x2c) : mword 64)
                       (sign_extend' 64 (mword_of_int 222 : mword 13))
                       = mword_of_int (FW + 0x10a))
               by (apply bv_eq; vm_compute; reflexivity).
             iApply (wp_bne_taken_s_sconf (mword_of_int (FW + 0x2c))
                       (mword_of_int 222 : mword 13) Ra4 Ra5 G7 (K - 12)%nat b
                       ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                       ltac:(rewrite Hncmp2; unfold neq_vec;
                             first [rewrite Hp2 | idtac]; reflexivity)
                       ltac:(rewrite Htgt10a; vm_compute; reflexivity)
                       with "Hcg Hpc Hi2c [-]").
             iNext. iIntros (CID13 Hs13) "Hcg Hpc".
             iEval (rewrite Htgt10a) in "Hpc".
             iApply (fw_panic (CID0 := CID13) G7 (K - 12)%nat sp0
                       w3 w5 w6 w9 w10 w11 pj b HG7sp
                       with "Hcg Htext Hpc Hpanic Hb3 Hb5 Hb6 Hb9 Hb10 Hb11").
  Qed.

End ProofFilewrite.
End FilewriteProof.
