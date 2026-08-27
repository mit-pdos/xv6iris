(* ProofFilewrite.v -- filewrite's own control flow and ghost steps.
   ========================== COMPLETE, S3t ============================

   STATUS (S3t): PROVEN, WITH NO AXIOM OF ITS OWN.  [FilewriteProof] is at
   the bottom of this file, [wp_filewrite_sconf] is proved for every path,
   and [LinkFilewrite.v] instantiates it.  Instruction by instruction:

     * +0x00/+0x04, the pre-prologue [f->writable] test, and its -1 return
       at +0x10c with sp and the whole frame untouched;
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
     * THE LOOP: [fw_loop], the [forall]-fuel induction at [n - i]; [fw_test],
       the +0xcc..+0xd8 chunk computation in BOTH arms; the [sext.w] at
       +0x82; and (S3t) the BODY -- begin_op, [ld a0,24(s2)], ilock at
       [s/2], the four argument moves and the [f->off] checkout, writei at
       [user = true], [fw_offupd] (the +0xa6 skip in both arms), the
       check-in and the re-park, iunlock, end_op, the short-write break at
       +0xc0, [i += r] at +0xc4 and the exhaustion test at +0xc8 whose fall
       IS the back edge.

   THE TWO STRUCTURAL DEVICES, and they are the whole reason this file is
   ~2900 lines and not ~4500.  A ROCQ PROOF CANNOT JOIN TWO ARMS, so a
   diamond in the control-flow graph doubles everything after it unless it
   is lifted into a lemma whose continuation is quantified over exactly
   what the two arms disagree about.  There are two such diamonds:

     * [fw_test] (+0xcc..+0xd8), which disagrees about the chunk [c] and
       the register file;
     * [fw_offupd] (+0xa6..+0xb0), which disagrees about the register file
       and the word [f->off] ends up holding.

   A THIRD diamond -- writei's own return disjunction -- is collapsed not
   by a lemma but by ONE [assert] ([Hjoin]): both arms produce a count
   [rz] in [-1 .. c], the two PURE re-park facts ([InodeLock.inode_ok] and
   [DirView.dir_ok] at the record writei returned) and [dn0' = dn'], and
   nothing below the [assert] mentions the arms again.

   WHAT THE INVARIANT TURNED OUT TO BE.  Three things are loop-carried
   ([i] and the page-table descriptor -- the bitmap's marked set is NOT,
   since the bitmap now lives in a persistent invariant) and almost
   nothing else is.  The inode is PARKED in the escrow at the head of every
   iteration, so no [dinode], no [blkmap] and no [data] appears in the
   invariant; ilock mints them inside the iteration and iunlock parks them
   again.  [f->off] is likewise RESIDENT in [off_inv] at the head, borrowed
   and returned within one iteration.  The environment splits cleanly:
   fifteen PERSISTENT invariants (the bitmap's among them) plus the ten
   pure fields, threaded free, and an exclusive half that is exactly
   [filewrite_fs_out fn], i.e. the four resources the contract itself
   returns.  That is why the exit needs no re-assembly.

   THE CROSSING CONVENTION (S3t).  [SpecFilewrite]'s and
   [SpecConsolewrite]'s crossings are the literal [true], not [b]: every
   arm of filewrite parks, and the porting guide's rule is that a PARKING
   function's [wp_next] index is [true] unconditionally.  With the
   contract's [eb = true] and [CpuOwn.cpu_own_eb_agree] at level 0 the two
   spellings coincide at every constructible instance, so this is not a
   change of strength -- but [cpu_own_transport] is asked at [b], and from
   a [true]-indexed chain fact the [b]-indexed guard is UNDERIVABLE.  So
   [b = true] is pinned once per lemma as [Hb] and rewritten into the
   TRANSPORTS ONLY, never into [sie_cap_gpr] or [cpu_own], whose spelling
   has to keep matching the callee contracts.

   =====================================================================
   S3p: BLOCKER SIX IS REPAIRED.  THE WALK HAS NOTHING OWED IN FRONT OF IT.
   =====================================================================

   S3o stopped at ONE premise of ONE call -- writei's, at +0xa0 -- and S3p
   fixed the contract.  [SpecWritei.v] now carries [SpecReadi.v]'s shape
   verbatim: the pid fraction is the KERNEL arm's and rides INSIDE the
   [if user] bracket, in the precondition and the postcondition of both
   [wp_writei_sconf_body] and [wp_writei_gen_body].  So the walk, standing
   at +0xa0 holding [proc_priv_core pj pidv V] and nothing else, satisfies the
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
       ([dn0 := dn]), the three superblock cells + [bitmap_inv] +
       [ireg_inv] + [bslots 3] out of the environment, and
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
      [inode_shr_gen k s dev inum g] and returns the checkout descriptor;
      SpecIunlock takes that deposit back and
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
             taken -> +0x10c; the FALL is [fw_wbool_of_fall]
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
     +0x5c [wp_lh_s_sconf (kt := KT1) (ktd := KT0)] (NOT compressed, and it does NOT live in the
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
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
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
Require Import DinodeEnc.
Require Import InodeInv.
Require Import InodeLock.
Require Import DirView.
(* THE PAYLOAD'S OWN VOCABULARY (durable-disk 2b-inode-3): [top_frag],
   [fs_gamma_L], [era_node] / [inode_rec_local].  IMPORTED BEFORE
   [FsBlocks] on purpose -- the [FsState*] stack exports [fs_view] and
   [byte_range], both of which have live twins below, and the LAST import
   wins (durable-notes, "AND WHERE THAT IMPORT COLLIDES, PUT IT EARLY"). *)
Require Import FsStateInode.
Require Import FsStateEra.
Require Import LogInv.
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
Require Import ConsoleInv.  (* [NDEV_max], [a_devsw_write] *)
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
Proof. lia. Qed.

Lemma fw_av_writei (K : nat) :
  (filewrite_stack <= K)%nat -> (K_writei <= K - 12)%nat.
Proof. lia. Qed.

Lemma fw_av_pipe (K : nat) :
  (filewrite_stack <= K)%nat -> (pipewrite_stack <= K - 12)%nat.
Proof. lia. Qed.

Lemma fw_av_cons (K : nat) :
  (filewrite_stack <= K)%nat -> (consolewrite_stack <= K - 12)%nat.
Proof. lia. Qed.

Lemma fw_av_ilock (K : nat) :
  (filewrite_stack <= K)%nat -> (K_ilock <= K - 12)%nat.
Proof. lia. Qed.

Lemma fw_av_iunlock (K : nat) :
  (filewrite_stack <= K)%nat -> (K_iunlock <= K - 12)%nat.
Proof. lia. Qed.

Lemma fw_av_begin_op (K : nat) :
  (filewrite_stack <= K)%nat -> (K_begin_op <= K - 12)%nat.
Proof. lia. Qed.

Lemma fw_av_end_op (K : nat) :
  (filewrite_stack <= K)%nat -> (K_end_op <= K - 12)%nat.
Proof. lia. Qed.

(* The frame trade-back, at the arity the epilogue wants. *)
Lemma fw_K_back (K : nat) :
  (filewrite_stack <= K)%nat -> ((K - 12) + 12)%nat = K.
Proof. lia. Qed.

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
   -- the pre-prologue [f->writable == 0] exit at +0x10c and the
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

(* the early return needs no converse: the [f->writable == 0] arm at +0x10c
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
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, FSC : fscfg}.

  Lemma fw_bslots3 :
    bslots 3 ⊣⊢ bslot ∗ bslots 2.
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
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fileG Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ}.
  (* ...and [GenId], which [ProcInv.proc_priv_core] acquired with
     [FirstTok.first_tok].  [RiscvLang] IS imported (line ~339), so unlike
     [pavG] above this one binds the real class. *)
  Context `{GEN : GenId}.

  (* A BI-ENTAILMENT, so it covers both ends of the call at once: read left
     to right it is what the walk must SUPPLY at +0xa0, right to left what
     it GETS BACK at +0xa4 (instantiate [V := upd_upt V P']), which is what
     lets the loop re-park [proc_priv] and carry it into the next iteration
     without ever holding [p_pid] itself. *)
  Lemma fw_writei_src (γf : gname) (j : nat) (pidv : mword 32) (V : pprivate)
      (dq : dfrac) (src : mword 64) (n : nat) (src_bytes : nat -> bv 8) :
    (if true
     then proc_priv_core (proc_addr j) pidv V
     else ([∗ list] i ∈ seq 0 n, pa_add src i ↦ₘ src_bytes i) ∗
          p_pid (proc_addr j) ↦₄{dq} pidv)
    ⊣⊢ proc_priv_core (proc_addr j) pidv V.
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
(*  above says [WpLock.lockG] and the functor's says [lockG].  (Both are  *)
(*  now [Xv6Cameras.lockG]; the scoping point above still stands.)        *)
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
Require Import StackOwn.
Require Import CalleeSaved KernelText.
Require Import WpSconfAlu WpSconfMem WpSconfBtype WpSconfCtl.
Require Import WpSmodeIntr WpSmodeHalf.
Require Import IntrDefs.
Require Import CpuOwn.
Require Import UserPtTree.
Require Import SchedCtx.
Require Import WpLock.
Require Import SpecPanic.
Require Import FileOff.
(* [diskGhostG], [uartGhostG], [fsLogG] and [iregG] USED TO live unexported in
   [DiskPtsto], [WpUart], [FsBlocks] and [InodeRegion], and this block
   re-imported those four so the functor's [Context] would not invent four
   FRESH variables of the names ("Could not find an instance for ?diskGhostG0",
   naming no file).  6864d420 moved all four down to [Xv6Cameras], which this
   file already reaches, so that reason is gone: the re-imports it justified
   were dead weight and are removed.  What is left on these lines is here for
   what those modules define themselves. *)
Require Import WpUart BioInv FsBlocks FsCrash.
Require Import UartTxInv.
Require Import InodeRegion.
Require Import IrefSlots.
Require Import FsTree.
Require Import IcacheEscrow.
(* [dev_major] and [NDEV_max] are SpecFileread's -- [SpecFilewrite] states
   [filewrite_dev_env]'s guard with them but does not re-export them, so the
   device arm's four [Local Lemma]s cannot even be TYPED without this line. *)
Require Import SpecFileread.
Require Import CodeFilewrite ProofFilereadParts ProofFilewriteParts.
Require Import ProcAvail.
Require Import FsCfg.   (* [fscfg]: the fs configuration is AMBIENT *)

Set Printing Depth 40.

(* ---------------------------------------------------------------------- *)
(*  SEVEN FACTS THE LOOP BODY NEEDS AND THE PREAMBLE ABOVE COULD NOT STATE.*)
(*                                                                        *)
(*  Four are restatements: [ProofFileread.v] and [ProofPipewrite.v] each   *)
(*  keep a preamble above their own module and this tree does not          *)
(*  [Require Import] a proof file, so the facts the body borrows from      *)
(*  those preambles are re-proved here.  They live BELOW the walk's import *)
(*  block because [off_wf], [pprivate] and [uptd] are not in scope above   *)
(*  it.                                                                   *)
(*                                                                        *)
(*  The last two are new, and they are what writei's RETURN RANGE costs:   *)
(*  [fw_neq_moi] is stated for two NON-NEGATIVE literals and writei's      *)
(*  failure arm answers [-1], so the [bne s3,s1] at +0xc0 needs the        *)
(*  compare over [-1 <= r].  Splitting the walk on writei's arm instead    *)
(*  would duplicate iunlock, end_op, both exits and the back edge.        *)
(* ---------------------------------------------------------------------- *)

Lemma fw_off_wf_new (u t : Z) : (0 <= u)%Z -> (0 <= t)%Z ->
  (u + t <= Z.of_nat MAXFILE * Z.of_nat BSIZE)%Z ->
  off_wf (mword_of_int (u + t) : mword 32).
Proof.
  rewrite /off_wf fw_maxfile_bsize. intros H0 H1 H2.
  rewrite moi32_small; [lia | change (2 ^ 32)%Z with 4294967296%Z; lia].
Qed.

Lemma fw_r_lt63 (o t : Z) : (0 <= o)%Z ->
  (o + t <= Z.of_nat MAXFILE * Z.of_nat BSIZE)%Z -> (t < 2 ^ 63)%Z.
Proof.
  rewrite fw_maxfile_bsize. change (2 ^ 63)%Z with 9223372036854775808%Z. lia.
Qed.

Lemma fw_pv_upt_upd (V : pprivate) (P : uptd) : pv_upt (upd_upt V P) = P.
Proof. destruct V; reflexivity. Qed.

Lemma fw_upd_upt_upd (V : pprivate) (P Q : uptd) :
  upd_upt (upd_upt V P) Q = upd_upt V Q.
Proof. destruct V; reflexivity. Qed.

(* THE OFFSET STAYS [off_wf] ACROSS A CHUNK, and the reason is the record
   writei RETURNS rather than any premise it was given: [wi_dinode]'s size
   is [max (di_size dn) (off + tot)], and the size cap is one of the seven
   [InodeLock.inode_ok] conjuncts the re-park has to re-establish anyway.
   So [off + tot] is under the cap because the NEW SIZE is -- which is why
   [SpecFilewrite.fw_off_advance]'s "writei refuses rather than overruns"
   never has to be invoked on the success arm. *)
Lemma fw_off_tot_bound (dn : dinode) (bm' : blkmap) (off tot : nat) :
  (bv_unsigned (di_size dn) <= Z.of_nat MAXFILE * Z.of_nat BSIZE)%Z ->
  (Z.of_nat off + Z.of_nat tot < 2 ^ 32)%Z ->
  (bv_unsigned (di_size (wi_dinode dn bm' off tot))
     <= Z.of_nat MAXFILE * Z.of_nat BSIZE)%Z ->
  (Z.of_nat off + Z.of_nat tot <= Z.of_nat MAXFILE * Z.of_nat BSIZE)%Z.
Proof.
  intros Hsz Hlt Hsz'.
  (* [<] IS NOT [Z.lt] BY DEFAULT HERE.  [nat_scope] is open, so the
     [decide] this destructs has to be spelled [%Z] or Rocq elaborates it
     at [nat] and reports "bv_unsigned (di_size dn) has type Z while it is
     expected to have type nat" -- an error about the SUBTERM, not about
     the scope that caused it. *)
  assert (Hsum : Z.of_nat (off + tot) = (Z.of_nat off + Z.of_nat tot)%Z)
    by (rewrite Nat2Z.inj_add; reflexivity).
  unfold wi_dinode in Hsz'. cbn [di_size] in Hsz'.
  destruct (decide ((bv_unsigned (di_size dn) < Z.of_nat (off + tot))%Z))
    as [Hlt' | Hge].
  - assert (Hb : bv_unsigned (mword_of_int (Z.of_nat (off + tot)) : mword 32)
                 = Z.of_nat (off + tot))
      by (apply moi32_small; lia).
    rewrite Hb in Hsz'. lia.
  - lia.
Qed.

Lemma fw_neq_m1 (a : Z) : (0 <= a < 2 ^ 31)%Z ->
  neq_vec (mword_of_int a : mword 64) (mword_of_int (-1) : mword 64) = true.
Proof.
  intro Ha. change (2 ^ 31)%Z with 2147483648%Z in Ha.
  unfold neq_vec.
  rewrite (_ : eq_vec (mword_of_int a : mword 64) (mword_of_int (-1) : mword 64)
               = false); [reflexivity |].
  apply eq_vec_false_iff. intro Hce.
  apply (f_equal (@bv_unsigned 64)) in Hce.
  rewrite !moi64_unsigned in Hce.
  rewrite (bvw64_small a ltac:(change (2^64)%Z with 18446744073709551616%Z; lia))
    in Hce.
  assert (Hm : bv_wrap 64 (-1) = 18446744073709551615%Z)
    by (vm_compute; reflexivity).
  rewrite Hm in Hce. lia.
Qed.

Lemma fw_neq_r (a rz : Z) : (0 <= a < 2 ^ 31)%Z -> (-1 <= rz < 2 ^ 31)%Z ->
  neq_vec (mword_of_int a : mword 64) (mword_of_int rz : mword 64)
  = negb (Z.eqb a rz).
Proof.
  intros Ha Hr.
  (* [Z.eq_dec] declares no argument scopes, so a bare [-1] here is read in
     [nat_scope] and fails with "Cannot interpret this number as a value of
     type nat" -- pointing at the numeral and not at the constant that let
     it default.  Both occurrences are ascribed. *)
  destruct (Z.eq_dec rz (-1)%Z) as [Hm1 | Hne].
  - subst rz. rewrite (fw_neq_m1 a Ha).
    replace (Z.eqb a (-1)%Z) with false by (symmetry; apply Z.eqb_neq; lia).
    reflexivity.
  - apply fw_neq_moi; [exact Ha | lia].
Qed.

(* filewrite's ELSE arm reaches [panic("filewrite")] with the frame already
   pushed 12 slots deep; [ProofFilewriteParts.fw_panic] is the whole block. *)
Lemma fw_panic_K (K : nat) :
  (filewrite_stack <= K)%nat -> (panic_stack <= K - 12)%nat.
Proof. lia. Qed.

Module FilewriteProof (Pipewrite : PIPEWRITE) (Ilock : ILOCK) (Writei : WRITEI)
                      (Iunlock : IUNLOCK) (BeginOp : BEGIN_OP) (EndOp : END_OP)
                      (Consolewrite : CONSOLEWRITE) (PN : PANIC) : FILEWRITE.

Section ProofFilewrite.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ, !irefslotG Σ, !pavG Σ}.
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
     fileread's [fr_env_*] block, one arm at a time.  Nothing about the
     bitmap crosses either way: it is a persistent invariant.
     ------------------------------------------------------------------ *)
  Local Lemma fw_env_dev (γf' : gname)
      (fn' : fwrite_names) (Cf' : fcontent) :
    fc_type Cf' = FD_DEVICE ->
    filewrite_env γf' fn' Cf' -∗ filewrite_dev_env fn' Cf'.
  Proof.
    intro Ht. rewrite /filewrite_env Ht.
    rewrite bool_decide_eq_false_2; [| by vm_compute].
    rewrite bool_decide_eq_true_2; [| reflexivity].
    by iIntros "$".
  Qed.

  Local Lemma fw_env_out_dev (fn' : fwrite_names) (Cf' : fcontent) :
    fc_type Cf' = FD_DEVICE ->
    filewrite_dev_env fn' Cf' -∗ filewrite_env_out fn' Cf'.
  Proof.
    intro Ht. rewrite /filewrite_env_out /filewrite_dev_out Ht.
    rewrite bool_decide_eq_false_2; [| by vm_compute].
    rewrite bool_decide_eq_true_2; [| reflexivity].
    by iIntros "$".
  Qed.

  Local Lemma fw_dev_in (fn' : fwrite_names) (Cf' : fcontent) :
    (dev_major Cf' <= NDEV_max)%Z ->
    filewrite_dev_env fn' Cf' -∗
    ⌜fwn_wp fn' (dev_major Cf') = (zero_reg : mword 64)
      \/ fwn_wp fn' (dev_major Cf')
          = (mword_of_int KernelSyms.consolewrite : mword 64)⌝ ∗
    a_devsw_write (dev_major Cf') ↦₈{fwn_dqv fn' (dev_major Cf')}
      fwn_wp fn' (dev_major Cf') ∗
    dev_inv (fwn_uart fn') (fwn_disk fn') ∗
    is_txlock (fwn_txlock fn') (fwn_uart fn').
  Proof.
    intro H. rewrite /filewrite_dev_env /filewrite_dev_caps.
    case_decide as H'; [by iIntros "$" | contradiction].
  Qed.

  Local Lemma fw_dev_in_back (fn' : fwrite_names) (Cf' : fcontent) :
    (dev_major Cf' <= NDEV_max)%Z ->
    ⌜fwn_wp fn' (dev_major Cf') = (zero_reg : mword 64)
      \/ fwn_wp fn' (dev_major Cf')
          = (mword_of_int KernelSyms.consolewrite : mword 64)⌝ -∗
    a_devsw_write (dev_major Cf') ↦₈{fwn_dqv fn' (dev_major Cf')}
      fwn_wp fn' (dev_major Cf') -∗
    dev_inv (fwn_uart fn') (fwn_disk fn') -∗
    is_txlock (fwn_txlock fn') (fwn_uart fn') -∗
    filewrite_dev_env fn' Cf'.
  Proof.
    intro H. rewrite /filewrite_dev_env /filewrite_dev_caps.
    case_decide as H'; [| contradiction].
    iIntros "%Hd Hc #Hdi #Htx".
    iSplitR; [iPureIntro; exact Hd |]. iFrame "Hc Hdi Htx".
  Qed.

  (* ---- the FD_INODE arm's environment, opened and closed --------------
     [fw_env_fs] is [fw_env_dev]'s twin at the third arm; [fw_env_out_fs]
     is the exit.  Neither does anything but reduce three
     [bool_decide]s, and they exist so that no [vm_compute] on an
     [fcontent] runs at a call site. ------------------------------------ *)
  Local Lemma fw_env_fs (gf' : gname)
      (fn' : fwrite_names) (Cf' : fcontent) :
    fc_type Cf' = FD_INODE ->
    filewrite_env gf' fn' Cf' -∗ filewrite_fs_env gf' fn'.
  Proof.
    intro Ht. rewrite /filewrite_env Ht.
    rewrite bool_decide_eq_false_2; [| by vm_compute].
    rewrite bool_decide_eq_false_2; [| by vm_compute].
    rewrite bool_decide_eq_true_2; [| reflexivity].
    by iIntros "$".
  Qed.

  Local Lemma fw_env_out_fs (fn' : fwrite_names) (Cf' : fcontent) :
    fc_type Cf' = FD_INODE ->
    filewrite_fs_out fn' -∗ filewrite_env_out fn' Cf'.
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
    sie_cap_gpr KT1 M Kn b p -∗
    kernel_text -∗
    InstrBytes.pc_is (mword_of_int (FW + 0xd4) : mword 64) -∗
    wp_next b p (fun (CID : CpuId) =>
      ∀ (c : Z) (P : regfile),
        ⌜(0 < c <= SpecFilewrite.FW_MAX)%Z /\ (c <= nz - iz)%Z
          /\ P !!! Regidx Rs3 = (mword_of_int c : mword 64)
          /\ (forall r : mword 5, is_cs_idx r = true -> r <> Rs3 ->
                P !!! Regidx r = M !!! Regidx r)⌝ -∗
        sie_cap_gpr KT1 P Kn b p -∗
        InstrBytes.pc_is (mword_of_int (FW + 0x8a) : mword 64) -∗
        WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hiz Hnz HMs4 HMs5 HMs7 HMs9.
    iIntros "Hcg #Htext Hpc Hcont".
    (* ---- +0xcc subw a5,s5,s4 : a5 := n - i ---- *)
    iApply (wp_subw_s_sconf (mword_of_int (FW + 0xd4)) Ra5 Rs5 Rs4 M Kn b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (fwri_0d4 with "Htext"). }
    iIntros (CID1 Hq1) "Hcg Hpc". iEval (rgne) in "Hcg".
    set (T1 := <[Regidx Ra5 := regval_into_reg
                  (sign_extend' 64 (sub_vec
                     (subrange_vec_dec (M !!! Regidx Rs5) 31 0 : mword 32)
                     (subrange_vec_dec (M !!! Regidx Rs4) 31 0 : mword 32)))]> M).
    assert (HT1a5 : T1 !!! Regidx Ra5 = (mword_of_int (nz - iz) : mword 64)).
    { rewrite /T1 upd_eq. unfold regval_into_reg.
      rewrite HMs5 HMs4. apply fw_subw_moi; lia. }
    assert (Hppd8 : add_vec_int (mword_of_int (FW + 0xd4) : mword 64) 4
                    = mword_of_int (FW + 0xd8))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hppd8) in "Hpc".
    (* ---- +0xd0 c.mv s3,a5 ---- *)
    iApply (wp_cmv_s_sconf (mword_of_int (FW + 0xd8)) Rs3 Ra5 T1 Kn b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (fwri_0d8 with "Htext"). }
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
    assert (Hppda : add_vec_int (mword_of_int (FW + 0xd8) : mword 64) 2
                    = mword_of_int (FW + 0xda))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hppda) in "Hpc".
    (* ---- +0xd2 bge s7,a5 : is 3072 >= n - i ? ---- *)
    assert (Hcmp : zopz0zKzJ_s (rget T2 Rs7) (rget T2 Ra5)
                   = Z.geb SpecFilewrite.FW_MAX (nz - iz)).
    { rewrite (rget_ne T2 Rs7 ltac:(vm_compute; discriminate)).
      rewrite (rget_ne T2 Ra5 ltac:(vm_compute; discriminate)).
      rewrite HT2s7 HT2a5.
      apply fw_bge_moi; unfold SpecFilewrite.FW_MAX;
        change (2 ^ 31)%Z with 2147483648%Z; lia. }
    assert (Htgt82 : add_vec (mword_of_int (FW + 0xda) : mword 64)
              (sign_extend' 64 (mword_of_int 8112 : mword 13))
              = mword_of_int (FW + 0x8a))
      by (apply bv_eq; vm_compute; reflexivity).
    destruct (Z.geb SpecFilewrite.FW_MAX (nz - iz)) eqn:Hge.
    - (* ---- TAKEN: the chunk is the whole remainder ([fw_chunk_rem]) ---- *)
      assert (Hrem : (0 < nz - iz <= SpecFilewrite.FW_MAX)%Z).
      { apply fw_chunk_rem; [lia | apply Z.geb_le; exact Hge]. }
      iApply (wp_bge_taken_s_sconf (mword_of_int (FW + 0xda))
                (mword_of_int 8112 : mword 13) Ra5 Rs7 T2 Kn b
                ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                ltac:(exact Hcmp)
                ltac:(rewrite Htgt82; vm_compute; reflexivity)
                with "Hcg Hpc []").
      { iApply (fwri_0da with "Htext"). }
      iApply bi.later_intro. iIntros (CID3 Hq3) "Hcg Hpc".
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
      iApply (wp_bge_fall_s_sconf (mword_of_int (FW + 0xda))
                (mword_of_int 8112 : mword 13) Ra5 Rs7 T2 Kn b
                ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                ltac:(exact Hcmp)
                with "Hcg Hpc []").
      { iApply (fwri_0da with "Htext"). }
      iIntros (CID3 Hq3) "Hcg Hpc".
      assert (Hppde : add_vec_int (mword_of_int (FW + 0xda) : mword 64) 4
                      = mword_of_int (FW + 0xde))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hppde) in "Hpc".
      (* ---- +0xd6 c.mv s3,s9 : n1 := FW_MAX ---- *)
      iApply (wp_cmv_s_sconf (mword_of_int (FW + 0xde)) Rs3 Rs9 T2 Kn b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc []").
      { iApply (fwri_0de with "Htext"). }
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
      assert (Hppe0 : add_vec_int (mword_of_int (FW + 0xde) : mword 64) 2
                      = mword_of_int (FW + 0xe0))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hppe0) in "Hpc".
      (* ---- +0xd8 c.j -> +0x82.  THE NEGATIVE 21-BIT FIELD (S3o's leaf
             table): 2 * 2005 has bit 11 SET, so the displacement is -86
             and NOT +4010. ---- *)
      assert (Htgt82b : add_vec (mword_of_int (FW + 0xe0) : mword 64)
                (sign_extend' 64 (sign_extend' 21
                   (concat_vec (mword_of_int 2005 : mword 11) ('b"0"))))
                = mword_of_int (FW + 0x8a))
        by (apply bv_eq; vm_compute; reflexivity).
      iApply (wp_cj_s_sconf (mword_of_int (FW + 0xe0))
                (sign_extend' 21 (concat_vec (mword_of_int 2005 : mword 11) ('b"0")))
                T3 Kn b
                ltac:(rewrite Htgt82b; vm_compute; reflexivity)
                with "Hcg Hpc []").
      { iApply (fwri_0e0 with "Htext"). }
      iIntros (CID5 Hq5). iApply bi.later_intro. iIntros "Hcg Hpc".
      iEval (rewrite Htgt82b) in "Hpc".
      iSpecialize ("Hcont" $! CID5 with "[]"); [iPureIntro; wp_next_chain|].
      iApply ("Hcont" $! SpecFilewrite.FW_MAX T3 with "[%] Hcg Hpc").
      split_and!; [lia | lia | lia | exact HT3s3 | exact HT3thr].
  Qed.

  (* =================================================================== *)
  (*  +0xa6 .. +0xb0 -- THE [r <= 0] SKIP OF THE [f->off] ADVANCE, IN     *)
  (*  BOTH ARMS.                                                         *)
  (*                                                                     *)
  (*  [bge x0,a0] at +0xa6 jumps to +0xb4 when writei answered -1 or 0,   *)
  (*  and the fall runs [lw a5,32(s2) ; c.addw a5,a0 ; sw a5,32(s2)].     *)
  (*  BOTH arms land on +0xb4, and A ROCQ PROOF CANNOT JOIN TWO ARMS --   *)
  (*  so this is [fw_test]'s device a second time: lift the diamond into  *)
  (*  a lemma whose continuation is quantified over exactly what the two  *)
  (*  arms disagree about, which here is the register file (a5 is         *)
  (*  clobbered on one side) and the word the cell ends up holding.       *)
  (*  Everything after it -- the check-in, iunlock, end_op, the break     *)
  (*  test, both exits and the back edge -- is then written ONCE.  Inline *)
  (*  it would be written twice, which is what [ProofFileread.v]:1984 and *)
  (*  :2143 actually are.                                                *)
  (*                                                                     *)
  (*  The continuation learns only [off_wf v'] about the new word, and    *)
  (*  that is all any caller can use: the cell goes straight back into    *)
  (*  [off_inv] and the next iteration re-reads it.                       *)
  (* =================================================================== *)
  Local Lemma fw_offupd `{CID0 : CpuId}
      (Mt : regfile) (Kn : nat) (kx : nat) (v : mword 32) (rz : Z)
      (p : mword 64) (b : bool) :
    Mt !!! Regidx Ra0 = (mword_of_int rz : mword 64) ->
    Mt !!! Regidx Rs2 = fnode kx ->
    (-1 <= rz)%Z ->
    off_wf v ->
    (bv_unsigned v + rz <= Z.of_nat MAXFILE * Z.of_nat BSIZE)%Z ->
    sie_cap_gpr KT1 Mt Kn b p -∗
    kernel_text -∗
    InstrBytes.pc_is (mword_of_int (FW + 0xae) : mword 64) -∗
    a_foff kx ↦₄ v -∗
    wp_next b p (fun (CID : CpuId) =>
      ∀ (P : regfile) (v' : mword 32),
        ⌜off_wf v'
          /\ (forall r : mword 5, is_cs_idx r = true ->
                P !!! Regidx r = Mt !!! Regidx r)⌝ -∗
        sie_cap_gpr KT1 P Kn b p -∗
        InstrBytes.pc_is (mword_of_int (FW + 0xbc) : mword 64) -∗
        a_foff kx ↦₄ v' -∗
        WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Ha0 Hs2 Hrz Hwf Hadv.
    iIntros "Hcg #Htext Hpc Hcell Hcont".
    pose proof (bv_unsigned_in_range _ v) as Hvr.
    assert (Htgtb4 : add_vec (mword_of_int (FW + 0xae) : mword 64)
              (sign_extend' 64 (mword_of_int 14 : mword 13))
              = mword_of_int (FW + 0xbc))
      by (apply bv_eq; vm_compute; reflexivity).
    destruct (Z.le_gt_cases rz 0) as [Hle | Hgt].
    - (* ---- TAKEN: nothing was written and the cell goes back as it came.
           [-1 <= r <= 0] leaves exactly the two literals the two [blez]
           lemmas are stated at. ---- *)
      assert (Htk : zopz0zKzJ_s (zero_reg : mword 64)
                      (mword_of_int rz : mword 64) = true).
      { assert (Hz : rz = (-1)%Z \/ rz = 0%Z) by lia.
        destruct Hz as [-> | ->]; [exact fr_blez_m1 | exact fr_blez_zero]. }
      iApply (wp_bge_x0_taken_s_sconf (mword_of_int (FW + 0xae))
                (mword_of_int 14 : mword 13) Ra0 Mt Kn b
                ltac:(vm_compute; discriminate)
                ltac:(rgne; rewrite Ha0; exact Htk)
                ltac:(rewrite Htgtb4; vm_compute; reflexivity)
                with "Hcg Hpc []").
      { iApply (fwri_0ae with "Htext"). }
      iApply bi.later_intro. iIntros (CID1 Hq1) "Hcg Hpc".
      iEval (rewrite Htgtb4) in "Hpc".
      iSpecialize ("Hcont" $! CID1 with "[]"); [iPureIntro; wp_next_chain|].
      iApply ("Hcont" $! Mt v with "[%] Hcg Hpc Hcell").
      split; [exact Hwf | intros r _; reflexivity].
    - (* ---- FALL: [f->off += r], at a strictly positive count ---- *)
      assert (Hrb : (1 <= rz < 2 ^ 63)%Z).
      { split; [lia | exact (fw_r_lt63 (bv_unsigned v) rz (proj1 Hvr) Hadv)]. }
      iApply (wp_bge_x0_fall_s_sconf (mword_of_int (FW + 0xae))
                (mword_of_int 14 : mword 13) Ra0 Mt Kn b
                ltac:(vm_compute; discriminate)
                ltac:(rgne; rewrite Ha0; exact (fr_blez_pos rz Hrb))
                with "Hcg Hpc []").
      { iApply (fwri_0ae with "Htext"). }
      iIntros (CID1 Hq1) "Hcg Hpc".
      assert (Hppb2 : add_vec_int (mword_of_int (FW + 0xae) : mword 64) 4
                      = mword_of_int (FW + 0xb2))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hppb2) in "Hpc".
      (* ---- +0xaa lw a5,32(s2) : the cell, still borrowed ---- *)
      assert (Hpoff : add_vec (rget Mt Rs2)
                        (sign_extend' 64 (mword_of_int 32 : mword 12))
                      = a_foff kx).
      { rewrite (rget_ne Mt Rs2 ltac:(vm_compute; discriminate)) Hs2.
        reflexivity. }
      iEval (rewrite -Hpoff) in "Hcell".
      iApply (wp_lw_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (FW + 0xb2)) Ra5 Rs2
                (mword_of_int 32 : mword 12) Mt Kn v b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc [] Hcell").
      { iApply (fwri_0b2 with "Htext"). }
      iIntros (CID2 Hq2) "Hcg Hpc Hcell". iEval (rewrite Hpoff) in "Hcell".
      set (U1 := <[Regidx Ra5 := regval_into_reg (sign_extend' 64 v)]> Mt).
      assert (HU1a5 : U1 !!! Regidx Ra5 = sign_extend' 64 v)
        by (rewrite /U1; apply upd_eq).
      assert (HU1a0 : U1 !!! Regidx Ra0 = (mword_of_int rz : mword 64))
        by (rewrite /U1 upd_ne; [exact Ha0 | vm_compute; discriminate]).
      assert (HU1s2 : U1 !!! Regidx Rs2 = fnode kx)
        by (rewrite /U1 upd_ne; [exact Hs2 | vm_compute; discriminate]).
      assert (Hppb6 : add_vec_int (mword_of_int (FW + 0xb2) : mword 64) 4
                      = mword_of_int (FW + 0xb6))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hppb6) in "Hpc".
      (* ---- +0xae c.addw a5,a0.  The AST names COMPRESSED register
             indices and the leaf lemma is stated at full ones. ---- *)
      assert (Hc2 : creg2reg_idx (Cregidx (mword_of_int 2)) = Regidx Ra0)
        by (vm_compute; reflexivity).
      assert (Hc7 : creg2reg_idx (Cregidx (mword_of_int 7)) = Regidx Ra5)
        by (vm_compute; reflexivity).
      iApply (wp_addw_s_sconf (mword_of_int (FW + 0xb6)) Ra5 Ra0 U1 Kn b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc []").
      { iEval (rewrite -Hc2 -Hc7). iApply (fwri_0b6 with "Htext"). }
      iIntros (CID3 Hq3) "Hcg Hpc". iEval (rgne; rgne) in "Hcg".
      set (U2 := <[Regidx Ra5 := regval_into_reg
                    (sign_extend' 64 (add_vec
                       (subrange_vec_dec (U1 !!! Regidx Ra5) 31 0 : mword 32)
                       (subrange_vec_dec (U1 !!! Regidx Ra0) 31 0 : mword 32)))]> U1).
      assert (HU2s2 : U2 !!! Regidx Rs2 = fnode kx)
        by (rewrite /U2 upd_ne; [exact HU1s2 | vm_compute; discriminate]).
      assert (Hstv : trunc32 (rget U2 Ra5)
                     = (mword_of_int (bv_unsigned v + rz) : mword 32)).
      { rgne. rewrite /U2 upd_eq. unfold regval_into_reg.
        rewrite HU1a5 HU1a0. apply fr_addw_store. }
      assert (Hppb8 : add_vec_int (mword_of_int (FW + 0xb6) : mword 64) 2
                      = mword_of_int (FW + 0xb8))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hppb8) in "Hpc".
      (* ---- +0xb0 sw a5,32(s2) ---- *)
      assert (Hpoff2 : add_vec (rget U2 Rs2)
                         (sign_extend' 64 (mword_of_int 32 : mword 12))
                       = a_foff kx).
      { rewrite (rget_ne U2 Rs2 ltac:(vm_compute; discriminate)) HU2s2.
        reflexivity. }
      iEval (rewrite -Hpoff2) in "Hcell".
      iApply (wp_sw_s_sconf (mword_of_int (FW + 0xb8)) Ra5 Rs2
                (mword_of_int 32 : mword 12) U2 Kn v b
                with "Hcg Hpc [] Hcell").
      { iApply (fwri_0b8 with "Htext"). }
      iIntros (CID4 Hq4) "Hcg Hpc Hcell".
      iEval (rewrite Hpoff2) in "Hcell". iEval (rewrite Hstv) in "Hcell".
      assert (Hppbc : add_vec_int (mword_of_int (FW + 0xb8) : mword 64) 4
                      = mword_of_int (FW + 0xbc))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hppbc) in "Hpc".
      iSpecialize ("Hcont" $! CID4 with "[]"); [iPureIntro; wp_next_chain|].
      iApply ("Hcont" $! U2 (mword_of_int (bv_unsigned v + rz) : mword 32)
                with "[%] Hcg Hpc Hcell").
      split.
      + apply fw_off_wf_new; [exact (proj1 Hvr) | lia | exact Hadv].
      + intros r Hr. rewrite /U2 upd_ne; [| regne].
        rewrite /U1 upd_ne; [reflexivity | regne].
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
  (*  [iz] and the page-table descriptor [PI] (which writei's user arm   *)
  (*  advances).  THE BITMAP IS NOT CARRIED: [BitmapInv.bitmap_inv] is   *)
  (*  persistent, so balloc's marking is invisible to this loop.         *)
  (*  THE INODE IS NOT: at the head of every iteration it is PARKED in   *)
  (*  the escrow, so its record, block map and data are inside           *)
  (*  [ic_escrow] and ilock mints fresh ones -- which is why the         *)
  (*  invariant names no [dinode] and no [blkmap] at all.  Likewise      *)
  (*  [f->off] is RESIDENT in [off_inv] at the head and is borrowed and  *)
  (*  returned inside a single iteration, so it too is absent here.      *)
  (*                                                                     *)
  (*  WHAT IS THREADED but not carried: the whole persistent half of     *)
  (*  [filewrite_fs_env] (fifteen invariants and contexts) is passed as *)
  (*  separate arguments rather than as the packed environment, since    *)
  (*  the induction has to name them one at a time anyway.  The          *)
  (*  EXCLUSIVE half is exactly [filewrite_fs_out fn] -- the same four   *)
  (*  resources the contract returns -- which is why the exit needs no   *)
  (*  re-assembly beyond [fw_env_out_fs].                                *)
  (* =================================================================== *)
  Local Lemma fw_loop `{CID0 : CpuId}
      (ga gf : gname) (gs : list gname) (jx : nat) (glp : gname)
      (kx : nat) (qx : Qp) (Cf : fcontent) (fn : fwrite_names)
      (pidv : mword 32) (V : pprivate)
      (m : regfile) (K : nat) (eb : bool) (n : Z) (b : bool)
      (sp0 w12 pj : mword 64) (lks : gset string) :
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
    log_geom_ok fsc_cov fsc_logst ->
    (0 <= fwn_inodestart fn)%Z ->
    (* the REGION-WIDE geometry, quantified: the inum is existential in the
       reference and only the carve names it (fs-sysfile S4c) *)
    (forall inum : mword 32,
       (bv_unsigned inum < 16 * Z.of_nat icfg_nib)%Z ->
       IBLOCK inum (fwn_inodestart fn) ∈ fsc_cov) ->
    (forall inum : mword 32,
       (bv_unsigned inum < 16 * Z.of_nat icfg_nib)%Z ->
       IBLOCK inum (fwn_inodestart fn)
         ∉ log_region_set fsc_logst) ->
    BitmapInv.bitmap_geom_ok fsc_cov fsc_logst
      (fwn_bmapstart fn) (fwn_size fn) ->
    SpecPrintk.printk_gen_contract (kt := KT1) (fwn_pr fn) (fwn_uart fn) (fwn_disk fn) ->
    (* the ambient log, named -- the escrow's write arm parks at [icfg_log]
       (durable-disk B''-tx) *)
    fwn_log fn = icfg_log ->
    (* ---- THE FUEL, and everything the loop carries under it ---- *)
    forall (W : nat) (iz : Z) (PI : uptd) (M : regfile),
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
    (* the loop body's cone: begin_op/end_op ("log", 3), ilock ("bcache",
       4), iunlock ("sleep lock", 6) -- "log" is the lowest, on this
       recursion's own binder list so the back-edge re-proves it. *)
    locks_below lks "log" ->
    sie_cap_gpr KT1 M (K - 12)%nat b pj -∗
    cpu_own 0%nat eb pj b lks -∗
    kernel_text -∗
    InstrBytes.pc_is (mword_of_int (FW + 0xd4) : mword 64) -∗
    procs_inv gs -∗
    (* the twelve frame slots, none of which the body touches *)
    word_pointsto (KTR := KT1) (pa_stk sp0 1) (DfracOwn 1) (m !!! Regidx Rra) -∗
    word_pointsto (KTR := KT1) (pa_stk sp0 2) (DfracOwn 1) (m !!! Regidx Rs0) -∗
    word_pointsto (KTR := KT1) (pa_stk sp0 3) (DfracOwn 1) (m !!! Regidx Rs1) -∗
    word_pointsto (KTR := KT1) (pa_stk sp0 4) (DfracOwn 1) (m !!! Regidx Rs2) -∗
    word_pointsto (KTR := KT1) (pa_stk sp0 5) (DfracOwn 1) (m !!! Regidx Rs3) -∗
    word_pointsto (KTR := KT1) (pa_stk sp0 6) (DfracOwn 1) (m !!! Regidx Rs4) -∗
    word_pointsto (KTR := KT1) (pa_stk sp0 7) (DfracOwn 1) (m !!! Regidx Rs5) -∗
    word_pointsto (KTR := KT1) (pa_stk sp0 8) (DfracOwn 1) (m !!! Regidx Rs6) -∗
    word_pointsto (KTR := KT1) (pa_stk sp0 9) (DfracOwn 1) (m !!! Regidx Rs7) -∗
    word_pointsto (KTR := KT1) (pa_stk sp0 10) (DfracOwn 1) (m !!! Regidx Rs8) -∗
    word_pointsto (KTR := KT1) (pa_stk sp0 11) (DfracOwn 1) (m !!! Regidx Rs9) -∗
    word_pointsto (KTR := KT1) (pa_stk sp0 12) (DfracOwn 1) w12 -∗
    file_ref gf kx qx Cf -∗
    proc_priv_core pj pidv (upd_upt V PI) -∗
    KvmSpec.kalloc_env ga None -∗
    (* ---- the PERSISTENT half of [filewrite_fs_env] ---- *)
    bio_ctx (fwn_bio fn)
      (fs_view fsc_fs (fwn_disk fn) icfg_dev fsc_cov) -∗
    log_ctx (fwn_log fn) (fwn_bio fn) fsc_fs fsc_cov
      fsc_logst icfg_dev -∗
    fs_crash_seam fsc_cov fsc_logst -∗
    gen_cert -∗
    KernelDataInv.kernel_data -∗
    SpecPrintk.printk_env (fwn_pr fn) (fwn_uart fn) (fwn_disk fn) -∗
    IcacheInv.itable_inv -∗
    (* the FAMILIES, since the slot is the carve's output and not the
       caller's to name *)
    ic_escrows fsc_ic fsc_fs fsc_ireg fsc_cov
      fsc_logst -∗
    ireg_inv fsc_ireg fsc_fs (fwn_inodestart fn) icfg_nib -∗
    ic_sleeplocks fsc_ic -∗
    dev_inv (fwn_uart fn) (fwn_disk fn) -∗
    DiskInv.disk_geom (fwn_disk fn) (fwn_pd fn) (fwn_pav fn) (fwn_pu fn) -∗
    is_lock (fwn_dlock fn) DiskAddrs.d_lock "virtio_disk"%string
      (DiskInv.disk_res (fwn_disk fn) (fwn_pd fn) (fwn_pav fn) (fwn_pu fn)) -∗
    (* THE BITMAP'S INVARIANT -- persistent, so it rides with the rest of
       the persistent half rather than being loop-carried. *)
    BitmapInv.bitmap_inv fsc_fs (fwn_bmapstart fn) fsc_cov
      fsc_logst (fwn_size fn) -∗
    (* ---- the EXCLUSIVE half ---- *)
    filewrite_fs_out fn -∗
    (* ---- and the contract's own continuation ---- *)
    (* [true], verbatim from [SpecFilewrite]: this IS the contract's crossing,
       forwarded, so the two must be spelled the same or [iExact] fails. *)
    wp_next true pj (fun (CID : CpuId) =>
      ∀ (mf : regfile) (r : mword 64) (P' : uptd),
        ⌜callee_saved m mf⌝ -∗
        ⌜uptd_ext (pv_upt V) P'⌝ -∗
        ⌜filewrite_ret n r⌝ -∗
        ⌜mf !!! Regidx Ra0 = r⌝ -∗
        sie_cap_gpr KT1 mf K b pj -∗
        cpu_own 0%nat eb pj b lks -∗
        InstrBytes.pc_is (ret_pc (m !!! Regidx Rra)) -∗
        file_ref gf kx qx Cf -∗
        proc_priv_core pj pidv (upd_upt V P') -∗
        filewrite_env_out fn Cf -∗
        WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HK Hkf Hjp Hgsj Hlens Hfnj Hfnps Hn Heb Htyi Hwb Hspm Hpjeq.
    intros P1 P2 P3q P4q P6 P7 Hclog.
    (* [pj] is the CALLER's let-bound local and every callee contract below
       states its resources at [proc_addr jx]; the two are the same word and
       the equation is eliminated once here rather than rewritten at each of
       the five calls. *)
    subst pj.
    intro W. revert CID0.
    induction W as [| W IH];
      intros CID0 iz PI M Hfuel Hiz Hext
             HMsp HMs2 HMs4 HMs5 HMs6 HMs7 HMs8 HMs9 HMthr Hbelow.
    { (* NO FUEL.  The loop is entered only at [i < n], so [n - i] is at
         least one and the zero case is vacuous. *)
      exfalso. lia. }
    iIntros "Hcg Hcnt #Htext Hpc #Hprocs
             Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hb7 Hb8 Hb9 Hb10 Hb11 Hb12
             Href Hpriv #Hkenv
             #Hbio #Hlog #Hcrash #Hgc #Hkd #Hpk #Hit #Hescs #Hireg
             #Hslks #Hdev #Hgeo #Hdlk #Hbm Hout Hcont".
    iPoseProof (SpecPrintk.printk_env_panic with "Hpk") as "#Hpenv".
    (* PIN THE INDEX.  Same one-liner as the contract's own proof below, and
       needed for the same reason: the body calls THREE [true]-crossing
       parking contracts (ilock, writei, end_op), whose chain facts are
       [true]-indexed, while [cpu_own_transport] is asked at [b].  From a
       [true]-indexed guard the [b]-indexed one is underivable, so [b] is
       pinned once here and rewritten into the TRANSPORTS ONLY -- never into
       [sie_cap_gpr] or [cpu_own], whose spelling must keep matching the
       callee contracts. *)
    iDestruct (cpu_own_eb_agree with "Hcg Hcnt") as %Hbm.
    assert (Hb : b = true) by (rewrite -Hbm; exact Heb).
    clear Hbm.
    (* =================================================================
       +0xcc .. +0xd8 -- THE TEST, and the chunk it settles.
       ================================================================= *)
    iApply (fw_test (CID0 := CID0) M (K - 12)%nat n iz (proc_addr jx) b
              Hiz (proj2 Hn) HMs4 HMs5 HMs7 HMs9
              with "Hcg Htext Hpc").
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
    iApply (wp_caddiw_s_sconf (mword_of_int (FW + 0x8a)) Rs3
              (mword_of_int 0 : mword 6) P (K - 12)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (fwri_08a with "Htext"). }
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
    assert (Hpp8c : add_vec_int (mword_of_int (FW + 0x8a) : mword 64) 2
                    = mword_of_int (FW + 0x8c))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp8c) in "Hpc".
    (* =================================================================
       +0x84 .. +0xc8 -- THE LOOP BODY.  The state at entry is [B0] with
       s3 = c (the chunk), s4 = i, s5 = n, s2 = f, s6 = addr, s7 = s9 =
       FW_MAX, s8 = 1, sp pushed; the twelve frame slots; the persistent
       half of the environment; [filewrite_fs_out fn]; and the
       contract's continuation.

       WHAT TRAVELS AND WHAT DOES NOT.  Only [is_cs_idx] registers are
       tracked, and only against [B0]: every callee is [callee_saved] and
       every straight-line instruction between the calls writes ra or an
       a-register, so ONE "agrees with [B0] on the callee-saved set" fact
       per step replaces the nine per-register ones.  The two exceptions
       are the [c.mv s1,a0] at +0xa4 and the [addw s4,s1,s4] at +0xc4,
       which really do move a tracked register and are stated in full.
       ================================================================= *)
    assert (HB0sp : B0 !!! Regidx csp_rs1 = pa_stk sp0 12)
      by (rewrite (HB0thr csp_rs1 ltac:(vm_compute; reflexivity)
                     ltac:(vm_compute; discriminate)); exact HPsp).
    assert (HB0s2 : B0 !!! Regidx Rs2 = fnode kx)
      by (rewrite (HB0thr Rs2 ltac:(vm_compute; reflexivity)
                     ltac:(vm_compute; discriminate)); exact HPs2).
    assert (HB0s4 : B0 !!! Regidx Rs4 = (mword_of_int iz : mword 64))
      by (rewrite (HB0thr Rs4 ltac:(vm_compute; reflexivity)
                     ltac:(vm_compute; discriminate)); exact HPs4).
    assert (HB0s5 : B0 !!! Regidx Rs5 = (mword_of_int n : mword 64))
      by (rewrite (HB0thr Rs5 ltac:(vm_compute; reflexivity)
                     ltac:(vm_compute; discriminate)); exact HPs5).
    assert (HB0s6 : B0 !!! Regidx Rs6 = m !!! Regidx Ra1)
      by (rewrite (HB0thr Rs6 ltac:(vm_compute; reflexivity)
                     ltac:(vm_compute; discriminate)); exact HPs6).
    assert (HB0s7 : B0 !!! Regidx Rs7
                    = (mword_of_int SpecFilewrite.FW_MAX : mword 64))
      by (rewrite (HB0thr Rs7 ltac:(vm_compute; reflexivity)
                     ltac:(vm_compute; discriminate)); exact HPs7).
    assert (HB0s8 : B0 !!! Regidx Rs8 = (mword_of_int 1 : mword 64))
      by (rewrite (HB0thr Rs8 ltac:(vm_compute; reflexivity)
                     ltac:(vm_compute; discriminate)); exact HPs8).
    assert (HB0s9 : B0 !!! Regidx Rs9
                    = (mword_of_int SpecFilewrite.FW_MAX : mword 64))
      by (rewrite (HB0thr Rs9 ltac:(vm_compute; reflexivity)
                     ltac:(vm_compute; discriminate)); exact HPs9).
    assert (HB0thr2 : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
              r <> Rs0 -> r <> Rs1 -> r <> Rs2 -> r <> Rs3 -> r <> Rs4 ->
              r <> Rs5 -> r <> Rs6 -> r <> Rs7 -> r <> Rs8 -> r <> Rs9 ->
              B0 !!! Regidx r = m !!! Regidx r).
    { intros r Hr Nsp N0 N1 N2 N3 N4 N5 N6 N7 N8 N9.
      rewrite (HB0thr r Hr N3).
      exact (HPthr' r Hr Nsp N0 N1 N2 N3 N4 N5 N6 N7 N8 N9). }
    (* the chunk's two [Z] shapes, and the [nat] the callee takes it at *)
    assert (Hcz : Z.of_nat (Z.to_nat c) = c) by (apply Z2Nat.id; lia).
    assert (Hcb : (Z.of_nat (Z.to_nat c) <= SpecFilewrite.FW_MAX)%Z)
      by (rewrite Hcz; lia).
    assert (Hclt31 : (0 <= c < 2 ^ 31)%Z) by (apply fw_chunk_lt31; lia).
    assert (Hizlt31 : (0 <= iz < 2 ^ 31)%Z) by (apply (fw_i_lt31 n iz); lia).
    (* ---- the iteration's own resources ---- *)
    iDestruct "Hout" as "(Hsbi & Hsbsz & Hsbb & Hbsl)".
    iDestruct "Href" as "(Hrtok & Hrfields & Hrpay & Hrlv)".
    iEval (rewrite /file_fields) in "Hrfields".
    iDestruct "Hrfields" as "(Hcty & Hcrd & Hcwr & Hcpp & Hcip & Hcmaj)".
    (* ---- THE CARVE (fs-sysfile S4', blocker 2's ratified alternative;
       ProofFilestat is the landed instance and ProofFileread the sibling).
       The slot, the inum, the device, the region bound, the SHARE, the
       GENERATION and the fd's recorded TYPE are not the caller's to supply
       -- they come out of the reference's own FD_INODE payload.  It is done
       once per ITERATION because the loop threads the reference whole; the
       names below are local to the iteration and everything derived from
       them is re-derived on the next one. ---- *)
    iDestruct (fileread_pay_carve gf kx qx Cf (or_introl Htyi) with "Hrpay")
      as (ik inum sh g ty γox)
         "(%P8 & %P9 & %P5 & %P10 & #Hty & Hshr & Hoh & Hpayback)".
    assert (P3 : IBLOCK inum (fwn_inodestart fn) ∈ fsc_cov)
      by (apply P3q; exact P5).
    assert (P4 : IBLOCK inum (fwn_inodestart fn)
                   ∉ log_region_set fsc_logst)
      by (apply P4q; exact P5).
    iDestruct (ic_escrows_acc2
                 ik P9 with "Hescs") as "#Hesc".
    iDestruct (ic_sleeplocks_lookup fsc_ic ik P9 with "Hslks")
      as (gil gisl) "#Hslk2".
    (* =================================================================
       +0x84 jal ra,begin_op -- THE TRANSACTION OPENS.  The pid quarter is
       BORROWED out of [proc_priv] for the length of the call and the wand
       is closed the instant it returns (fileread's discipline).
       ================================================================= *)
    iApply (wp_jal_s_sconf (mword_of_int (FW + 0x8c)) Rra
              (mword_of_int 2095300 : mword 21) B0 (K - 12)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(vm_compute; reflexivity) with "Hcg Hpc []").
    { iApply (fwri_08c with "Htext"). }
    iIntros (CIDa1 Hsa1) "Hcg Hpc".
    set (D1 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (FW + 0x8c) : mword 64) 4)]> B0).
    assert (Htgtbo : add_vec (mword_of_int (FW + 0x8c) : mword 64)
              (sign_extend' 64 (mword_of_int 2095300 : mword 21))
              = mword_of_int KernelSyms.begin_op)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtbo) in "Hpc".
    assert (HD1ra : D1 !!! Regidx Rra
                    = add_vec_int (mword_of_int (FW + 0x8c) : mword 64) 4)
      by (rewrite /D1; apply upd_eq).
    assert (HD1cs : forall r : mword 5, is_cs_idx r = true ->
              D1 !!! Regidx r = B0 !!! Regidx r).
    { intros r Hr. rewrite /D1 upd_ne; [reflexivity | regne]. }
    iDestruct (proc_priv_core_bare_acc (proc_addr jx) pidv (upd_upt V PI) with "Hpriv")
      as "[Hppid Hpbk1]".
   iDestruct (cpu_own_transport CID0 CIDa1 0%nat eb (proc_addr jx) b 
                 ltac:(rewrite Hb; wp_next_chain) with "Hcnt") as "Hcnt".
    iApply (BeginOp.wp_begin_op_sconf gs jx glp (fwn_bio fn) (fwn_log fn)
              fsc_fs fsc_cov fsc_logst icfg_dev
              pidv (DfracOwn (1/4)) D1 (K - 12)%nat eb b
              _ (upd_upt V PI) (fw_av_begin_op K HK) Hjp Hgsj
              Hbelow
              with "Hcg Hcnt [] [] Htext Hpc Hlog Hppid Hprocs").
    all: try lkbelow.
    { rewrite Heb /trap_csrs_ext. done. }
    { rewrite Heb /cpu_claim_ext. done. }
    iIntros (CIDbo Hsbo mbo) "%Hcsbo Hcg Hcnt _ _ Hpc Hppid Hlogop".
    (* ---- THE WRITE ARM (durable-fs-plan.md section 3, [ilock];
       durable-disk B''-tx).  The transaction token goes INTO [ilock], which
       parks half of it in the escrow's checked-out arm for the whole locked
       window; what crosses the window is the BUDGET half, which is the only
       token [log_write] ever wanted -- so [writei] is called at its
       [log_opS] GEN form here, exactly as B''-arm measured. *)
    iDestruct (log_op_openS with "Hlogop") as (SbF) "[HlogS Htx]".
    iEval (rewrite Hclog) in "Htx".
    iDestruct ("Hpbk1" with "Hppid") as "Hpriv".
    assert (Hpc88 : ret_pc (D1 !!! Regidx Rra) = mword_of_int (FW + 0x90)).
    { rewrite HD1ra. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hpc88) in "Hpc".
    pose proof Hcsbo as Hcsbo_cs.
    assert (Hbocs : forall r : mword 5, is_cs_idx r = true ->
              mbo !!! Regidx r = B0 !!! Regidx r).
    { intros r Hr. rewrite (callee_saved_lookup Hcsbo_cs r Hr).
      exact (HD1cs r Hr). }
    assert (Hbos2 : mbo !!! Regidx Rs2 = fnode kx)
      by (rewrite (Hbocs Rs2 ltac:(vm_compute; reflexivity)); exact HB0s2).
    (* ---- +0x88 ld a0,24(s2) : a0 := f->ip ---- *)
    assert (Hpip : add_vec (rget mbo Rs2)
                     (sign_extend' 64 (mword_of_int 24 : mword 12)) = a_fip kx).
    { rewrite (rget_ne mbo Rs2 ltac:(vm_compute; discriminate)) Hbos2.
      reflexivity. }
    iEval (rewrite -Hpip) in "Hcip".
    iApply (wp_ld_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (FW + 0x90)) Ra0 Rs2
              (mword_of_int 24 : mword 12) mbo (K - 12)%nat (fc_ip Cf) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] Hcip").
    { iApply (fwri_090 with "Htext"). }
    iIntros (CIDa2 Hsa2) "Hcg Hpc Hcip". iEval (rewrite Hpip) in "Hcip".
    set (D2 := <[Regidx Ra0 := regval_into_reg (fc_ip Cf)]> mbo).
    assert (Hpp94 : add_vec_int (mword_of_int (FW + 0x90) : mword 64) 4
                    = mword_of_int (FW + 0x94))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp94) in "Hpc".
    (* ---- +0x8c jal ra,ilock ---- *)
    iApply (wp_jal_s_sconf (mword_of_int (FW + 0x94)) Rra
              (mword_of_int 2092626 : mword 21) D2 (K - 12)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(vm_compute; reflexivity) with "Hcg Hpc []").
    { iApply (fwri_094 with "Htext"). }
    iIntros (CIDa3 Hsa3) "Hcg Hpc".
    set (D3 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (FW + 0x94) : mword 64) 4)]> D2).
    assert (Htgtil : add_vec (mword_of_int (FW + 0x94) : mword 64)
              (sign_extend' 64 (mword_of_int 2092626 : mword 21))
              = mword_of_int KernelSyms.ilock)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtil) in "Hpc".
    assert (HD3a0 : D3 !!! Regidx Ra0 = fc_ip Cf).
    { rewrite /D3 upd_ne; [| vm_compute; discriminate].
      rewrite /D2; apply upd_eq. }
    assert (HD3ra : D3 !!! Regidx Rra
                    = add_vec_int (mword_of_int (FW + 0x94) : mword 64) 4)
      by (rewrite /D3; apply upd_eq).
    assert (HD3cs : forall r : mword 5, is_cs_idx r = true ->
              D3 !!! Regidx r = B0 !!! Regidx r).
    { intros r Hr. rewrite /D3 upd_ne; [| regne].
      rewrite /D2 upd_ne; [| regne]. exact (Hbocs r Hr). }
    (* THE SHARE, HALVED (fs-icache 17.3): ilock is lent [s/2] and the
       retained half's [live_gen] is what pins the generation of the share
       iunlock hands back ([fw_shr_regen] on the way out). *)
    iEval (rewrite fw_shr_gen_halve) in "Hshr".
    iDestruct "Hshr" as "[Hshrk Hshrl]".
    iEval (rewrite fw_bslots3) in "Hbsl".
    iDestruct "Hbsl" as "[Hbsl1 Hbsl2]".
    iDestruct (proc_priv_core_bare_acc (proc_addr jx) pidv (upd_upt V PI) with "Hpriv")
      as "[Hppid Hpbk2]".
    iDestruct (cpu_own_transport CIDbo CIDa3 0%nat eb (proc_addr jx) b
                 ltac:(rewrite Hb; wp_next_chain) with "Hcnt") as "Hcnt".
    iApply (Ilock.wp_ilock_tx_sconf gs jx glp (fwn_uart fn) (fwn_disk fn)
              (fwn_dlock fn) (fwn_pd fn) (fwn_pav fn) (fwn_pu fn)
              (fwn_bio fn)
              gil gisl
              (fwn_inodestart fn)
              icfg_nib ik (sh / 2)%Qp g (ShotK ty)
              icfg_dev inum
              pidv (DfracOwn (1/4)) (fwn_dqs fn)
              D3 (K - 12)%nat eb b lks (upd_upt V PI)
              (fw_av_ilock K HK) P9 P1 P2 P3 P5 Hjp Hgsj
              ltac:(rewrite HD3a0; exact P8)
              (* ilock's bound is "bcache"(4); fw_loop's own is "log"(3),
                 and [locks_below_mono] weakens it. *)
              ltac:(lkbelow)
              with "Hcg Hcnt [] [] Htext Hkd Hpc Hpenv Hbio Hit Hesc Hireg
                    Hslk2 Hshrl Hty Hsbi Hppid Hprocs
                    Hdev Hgeo Hdlk Hbsl1 Htx").
    all: try lkbelow.
    { rewrite Heb /trap_csrs_ext. done. }
    { rewrite Heb /cpu_claim_ext. done. }
    iIntros (CIDil Hsil mil dnl bml fl_)
      "%Hcsil Hcg Hcnt _ _ Hpc Hppid Hsbi Hbsl1 Hheld Hdep
       Hidev Hinum Hvalid Hlk #Hshot Hfrz %Hfr_ _ %Hilkp".
    iDestruct ("Hpbk2" with "Hppid") as "Hpriv".
    assert (Hpc90 : ret_pc (D3 !!! Regidx Rra) = mword_of_int (FW + 0x98)).
    { rewrite HD3ra. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hpc90) in "Hpc".
    pose proof Hcsil as Hcsil_cs.
    assert (Hilcs : forall r : mword 5, is_cs_idx r = true ->
              mil !!! Regidx r = B0 !!! Regidx r).
    { intros r Hr. rewrite (callee_saved_lookup Hcsil_cs r Hr).
      exact (HD3cs r Hr). }
    assert (Hils2 : mil !!! Regidx Rs2 = fnode kx)
      by (rewrite (Hilcs Rs2 ltac:(vm_compute; reflexivity)); exact HB0s2).
    assert (Hils3 : mil !!! Regidx Rs3 = (mword_of_int c : mword 64))
      by (rewrite (Hilcs Rs3 ltac:(vm_compute; reflexivity)); exact HB0s3).
    assert (Hils8 : mil !!! Regidx Rs8 = (mword_of_int 1 : mword 64))
      by (rewrite (Hilcs Rs8 ltac:(vm_compute; reflexivity)); exact HB0s8).
    (* THE FD'S TYPE, PINNED.  ilock's witness and the fd's own witness name
       ONE generation, so [ity_shot_agree] joins them and the environment's
       last pure field turns "the fd is writable" into "not a directory". *)
    (* THE FD'S TYPE, PINNED.  ilock's witness and the fd's own witness (out
       of the CARVE now, not out of a caller-supplied field) name ONE
       generation, so [ity_shot_agree] joins them. *)
    iDestruct (ity_shot_agree with "Hshot Hty") as %Htyeq.
    assert (Hnodir : bv_unsigned (di_type dnl) <> T_DIR_z)
      by (rewrite Htyeq; exact (P10 Hwb)).
    (* ---- PEEL the checked-out bundle.  The valid cell is beside the
           content (SpecIlock v2) and it IS [FileOff.off_mark]. ---- *)
    rewrite /ic_loaded.
    iDestruct (ic_loaded_open with "Hlk") as (datal)"(%Hiok & %Hrl_datal & %Hdok & %Hddix & %Hdoc & %Hduq & Hdlnk & Hdnat & Hmeta & Haddrs & Hindres & Hblocks & Hdview & Hfview)".
    destruct Hiok as (Hbmwf & Hbmcov & Hdaddr & Hdty & Hszb & Hholes & Hsized).
    iAssert (inode_map fsc_fs (ientry ik) bml)
      with "[Haddrs Hindres]" as "Hmap".
    { rewrite /inode_map. iFrame. }
    (* ---- CHECK OUT the offset cell ---- *)
    iAssert (off_mark (fc_ip Cf)) with "[Hvalid]" as "Hmark".
    { rewrite /off_mark P8. iExact "Hvalid". }
    iApply fupd_wp.
    iMod (off_checkout gf γox kx qx (DfracOwn (qx/2)) (fc_ip Cf) ⊤
            ltac:(solve_ndisj) with "Hoh Hcip Hmark Hrlv")
      as "(Hoh & Hcip & Hoffc)".
    iModIntro.
    iDestruct "Hoffc" as (v) "[Hcell %Hwf]".
    pose proof (bv_unsigned_in_range _ v) as Hvr.
    assert (Hoffz : Z.of_nat (Z.to_nat (bv_unsigned v)) = bv_unsigned v)
      by (apply Z2Nat.id; exact (proj1 Hvr)).
    assert (Hoffb : (Z.of_nat (Z.to_nat (bv_unsigned v))
                     <= Z.of_nat MAXFILE * Z.of_nat BSIZE)%Z)
      by (rewrite Hoffz; exact Hwf).
    (* ---- +0x90 c.mv a4,s3 : a4 := n1 ---- *)
    iApply (wp_cmv_s_sconf (mword_of_int (FW + 0x98)) Ra4 Rs3 mil (K - 12)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (fwri_098 with "Htext"). }
    iIntros (CIDa4 Hsa4) "Hcg Hpc". iEval (rgne) in "Hcg".
    set (Q1 := <[Regidx Ra4 := regval_into_reg
                  (add_vec zero_reg (mil !!! Regidx Rs3))]> mil).
    assert (HQ1a4 : Q1 !!! Regidx Ra4 = (mword_of_int c : mword 64)).
    { rewrite /Q1 upd_eq. unfold regval_into_reg.
      rewrite add_vec_zero_l. exact Hils3. }
    assert (HQ1s2 : Q1 !!! Regidx Rs2 = fnode kx)
      by (rewrite /Q1 upd_ne; [exact Hils2 | vm_compute; discriminate]).
    assert (Hpp9a : add_vec_int (mword_of_int (FW + 0x98) : mword 64) 2
                    = mword_of_int (FW + 0x9a))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp9a) in "Hpc".
    (* ---- +0x92 lw a3,32(s2) : THE BORROWED CELL ---- *)
    assert (Hpoff : add_vec (rget Q1 Rs2)
                      (sign_extend' 64 (mword_of_int 32 : mword 12))
                    = a_foff kx).
    { rewrite (rget_ne Q1 Rs2 ltac:(vm_compute; discriminate)) HQ1s2.
      reflexivity. }
    iEval (rewrite -Hpoff) in "Hcell".
    iApply (wp_lw_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (FW + 0x9a)) Ra3 Rs2
              (mword_of_int 32 : mword 12) Q1 (K - 12)%nat v b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] Hcell").
    { iApply (fwri_09a with "Htext"). }
    iIntros (CIDa5 Hsa5) "Hcg Hpc Hcell". iEval (rewrite Hpoff) in "Hcell".
    set (Q2 := <[Regidx Ra3 := regval_into_reg (sign_extend' 64 v)]> Q1).
    assert (Hpp9e : add_vec_int (mword_of_int (FW + 0x9a) : mword 64) 4
                    = mword_of_int (FW + 0x9e))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp9e) in "Hpc".
    (* ---- +0x96 add a2,s4,s6 : the user source is [addr + i].  Its VALUE
           is never constrained -- writei's user arm reads the address out
           of [proc_priv] and the contract's [src] is a let. ---- *)
    iApply (wp_add_s_sconf (mword_of_int (FW + 0x9e)) Ra2 Rs4 Rs6
              (add_vec (rget Q2 Rs4) (rget Q2 Rs6)) Q2 (K - 12)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok) eq_refl
              with "Hcg Hpc []").
    { iApply (fwri_09e with "Htext"). }
    iIntros (CIDa6 Hsa6) "Hcg Hpc".
    set (Q3 := <[Regidx Ra2 := regval_into_reg
                  (add_vec (rget Q2 Rs4) (rget Q2 Rs6))]> Q2).
    assert (Hppa2 : add_vec_int (mword_of_int (FW + 0x9e) : mword 64) 4
                    = mword_of_int (FW + 0xa2))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hppa2) in "Hpc".
    (* ---- +0x9a c.mv a1,s8 : THE USER-SOURCE FLAG, the literal 1 ---- *)
    iApply (wp_cmv_s_sconf (mword_of_int (FW + 0xa2)) Ra1 Rs8 Q3 (K - 12)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (fwri_0a2 with "Htext"). }
    iIntros (CIDa7 Hsa7) "Hcg Hpc". iEval (rgne) in "Hcg".
    set (Q4 := <[Regidx Ra1 := regval_into_reg
                  (add_vec zero_reg (Q3 !!! Regidx Rs8))]> Q3).
    assert (HQ3s8 : Q3 !!! Regidx Rs8 = (mword_of_int 1 : mword 64)).
    { rewrite /Q3 upd_ne; [| vm_compute; discriminate].
      rewrite /Q2 upd_ne; [| vm_compute; discriminate].
      rewrite /Q1 upd_ne; [exact Hils8 | vm_compute; discriminate]. }
    assert (HQ4a1 : Q4 !!! Regidx Ra1 = (mword_of_int 1 : mword 64)).
    { rewrite /Q4 upd_eq. unfold regval_into_reg.
      rewrite add_vec_zero_l. exact HQ3s8. }
    assert (HQ4s2 : Q4 !!! Regidx Rs2 = fnode kx).
    { rewrite /Q4 upd_ne; [| vm_compute; discriminate].
      rewrite /Q3 upd_ne; [| vm_compute; discriminate].
      rewrite /Q2 upd_ne; [exact HQ1s2 | vm_compute; discriminate]. }
    assert (Hppa4 : add_vec_int (mword_of_int (FW + 0xa2) : mword 64) 2
                    = mword_of_int (FW + 0xa4))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hppa4) in "Hpc".
    (* ---- +0x9c ld a0,24(s2) : a0 := f->ip, again ---- *)
    assert (Hpip2 : add_vec (rget Q4 Rs2)
                      (sign_extend' 64 (mword_of_int 24 : mword 12)) = a_fip kx).
    { rewrite (rget_ne Q4 Rs2 ltac:(vm_compute; discriminate)) HQ4s2.
      reflexivity. }
    iEval (rewrite -Hpip2) in "Hcip".
    iApply (wp_ld_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (FW + 0xa4)) Ra0 Rs2
              (mword_of_int 24 : mword 12) Q4 (K - 12)%nat (fc_ip Cf) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] Hcip").
    { iApply (fwri_0a4 with "Htext"). }
    iIntros (CIDa8 Hsa8) "Hcg Hpc Hcip". iEval (rewrite Hpip2) in "Hcip".
    set (Q5 := <[Regidx Ra0 := regval_into_reg (fc_ip Cf)]> Q4).
    assert (Hppa8 : add_vec_int (mword_of_int (FW + 0xa4) : mword 64) 4
                    = mword_of_int (FW + 0xa8))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hppa8) in "Hpc".
    (* ---- +0xa0 jal ra,writei ---- *)
    iApply (wp_jal_s_sconf (mword_of_int (FW + 0xa8)) Rra
              (mword_of_int 2093834 : mword 21) Q5 (K - 12)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(vm_compute; reflexivity) with "Hcg Hpc []").
    { iApply (fwri_0a8 with "Htext"). }
    iIntros (CIDa9 Hsa9) "Hcg Hpc".
    set (Q6 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (FW + 0xa8) : mword 64) 4)]> Q5).
    assert (Htgtwi : add_vec (mword_of_int (FW + 0xa8) : mword 64)
              (sign_extend' 64 (mword_of_int 2093834 : mword 21))
              = mword_of_int KernelSyms.writei)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtwi) in "Hpc".
    assert (HQ6ra : Q6 !!! Regidx Rra
                    = add_vec_int (mword_of_int (FW + 0xa8) : mword 64) 4)
      by (rewrite /Q6; apply upd_eq).
    assert (HQ6a0 : Q6 !!! Regidx Ra0 = fc_ip Cf).
    { rewrite /Q6 upd_ne; [| vm_compute; discriminate].
      rewrite /Q5; apply upd_eq. }
    assert (HQ6a1 : Q6 !!! Regidx Ra1 = (mword_of_int 1 : mword 64)).
    { rewrite /Q6 upd_ne; [| vm_compute; discriminate].
      rewrite /Q5 upd_ne; [exact HQ4a1 | vm_compute; discriminate]. }
    assert (HQ6a3 : Q6 !!! Regidx Ra3
                    = (mword_of_int (Z.of_nat (Z.to_nat (bv_unsigned v)))
                       : mword 64)).
    { rewrite Hoffz.
      rewrite /Q6 upd_ne; [| vm_compute; discriminate].
      rewrite /Q5 upd_ne; [| vm_compute; discriminate].
      rewrite /Q4 upd_ne; [| vm_compute; discriminate].
      rewrite /Q3 upd_ne; [| vm_compute; discriminate].
      rewrite /Q2 upd_eq. unfold regval_into_reg.
      exact (fr_off_reg v (off_wf_lt31 v Hwf)). }
    assert (HQ6a4 : Q6 !!! Regidx Ra4
                    = (mword_of_int (Z.of_nat (Z.to_nat c)) : mword 64)).
    { rewrite Hcz.
      rewrite /Q6 upd_ne; [| vm_compute; discriminate].
      rewrite /Q5 upd_ne; [| vm_compute; discriminate].
      rewrite /Q4 upd_ne; [| vm_compute; discriminate].
      rewrite /Q3 upd_ne; [| vm_compute; discriminate].
      rewrite /Q2 upd_ne; [exact HQ1a4 | vm_compute; discriminate]. }
    assert (HQ6cs : forall r : mword 5, is_cs_idx r = true ->
              Q6 !!! Regidx r = B0 !!! Regidx r).
    { intros r Hr.
      rewrite /Q6 upd_ne; [| regne]. rewrite /Q5 upd_ne; [| regne].
      rewrite /Q4 upd_ne; [| regne]. rewrite /Q3 upd_ne; [| regne].
      rewrite /Q2 upd_ne; [| regne]. rewrite /Q1 upd_ne; [| regne].
      exact (Hilcs r Hr). }
    iAssert (bslots 3) with "[Hbsl1 Hbsl2]" as "Hbsl".
    { rewrite fw_bslots3. iFrame "Hbsl1 Hbsl2". }
    iDestruct (cpu_own_transport CIDil CIDa9 0%nat eb (proc_addr jx) b
                 ltac:(rewrite Hb; wp_next_chain) with "Hcnt") as "Hcnt".
    iApply (Writei.wp_writei_gen KT0 gs jx glp (fwn_uart fn) (fwn_disk fn)
              (fwn_dlock fn) (fwn_pd fn) (fwn_pav fn) (fwn_pu fn)
              (fwn_bio fn) (fwn_log fn) ga gf
              (fwn_inodestart fn) icfg_nib
              (fwn_bmapstart fn) (fwn_size fn) icfg_dev
              (fwn_pr fn)
              (ientry ik) inum
              bml datal dnl dnl
              true (Z.to_nat (bv_unsigned v)) (Z.to_nat c)
              (fun _ => (mword_of_int 0 : mword 8))
              (upd_upt V PI) MAXOPBLOCKS SbF
              pidv (DfracOwn 1) (DfracOwn (1/2)) (DfracOwn (1/2))
              (fwn_dqs fn) (fwn_dqb fn) (fwn_dqbs fn)
              Q6 (K - 12)%nat eb b lks
              (fw_av_writei K HK)
              (fw_budget_ok (Z.to_nat (bv_unsigned v)) (Z.to_nat c) Hcb)
              P1 P2 P3 P4 P5 Hdaddr Hdty
              (* §19.6 Part 1: filewrite hands writei ONE record for both
                 the in-memory and the region slot ([dnl dnl]), so writei's
                 type-stability premise is reflexivity. *)
              (InodeRegion.di_type_stable_refl dnl)
              (* §20's (L3), vacuous here: [inode_ok]'s own nonzero type. *)
              (InodeRegion.di_nlink_stable_refl dnl Hdty)
              Hbmwf Hholes Hbmcov
              (SpecFilewrite.fw_chunk_joint (Z.to_nat (bv_unsigned v))
                 (Z.to_nat c) Hoffb Hcb)
              (fw_size_lt31 (bv_unsigned (di_size dnl)) (proj1 (bv_unsigned_in_range _ _)) Hszb)
              P6 P7 Hjp Hgsj
              ltac:(rewrite HQ6a0; exact P8)
              ltac:(rewrite HQ6a1; vm_compute; reflexivity)
              HQ6a3 HQ6a4
              with "Hcg Hcnt [] [] Htext Hpc Hkd Hpk Hbio Hlog Hkenv
                    Hidev Hinum Hmeta Hmap Hblocks Hsbi Hsbsz Hsbb Hbm
                    Hireg Hdnat [Hpriv] Hprocs Hdev Hgeo Hdlk Hbsl HlogS").
    all: try lkbelow.
    { rewrite Heb /trap_csrs_ext. done. }
    { rewrite Heb /cpu_claim_ext. done. }
    (* [fw_writei_src] is NOT applied here and does not need to be: the
       [if user] bracket is at the literal [true] the decode forces, and the
       proofmode iota-reduces it before the goal is ever shown.  Rewriting
       with the bi-entailment fails outright ("all matches of the LHS are
       equal to the RHS"), which is the tell that the discharge is free.
       The lemma stays as the machine-checked statement that the premise
       AS WRITTEN is what the walk holds -- it is what stops compiling if
       SpecWritei's bracket changes shape again. *)
    { iExact "Hpriv". }
    iIntros (CIDwi Hswi mwi tot bm' data' dn' dn0' n' wrote dist dstb P' Sb')
      "%Hcswi %Hbmwf2 %Hholes2 %Hdaddr2 %Hsz2 %Hbmcov2 %Hcap2 %Hsized2
       %Hdist %Hdistn %Hdistk %Hrange %Hkbytes %Harms %Hbud
       %HSbsub %Hwi16p %Hwi16sp %Hwi16at %Hupt
       Hcg Hcnt _ _ Hpc Hidev Hinum Hmeta Hmap Hblocks Hsbi Hsbsz Hsbb
       Hdnat Hpriv Hbsl HlogS".
    assert (Hpca4 : ret_pc (Q6 !!! Regidx Rra) = mword_of_int (FW + 0xac)).
    { rewrite HQ6ra. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hpca4) in "Hpc".
    pose proof Hcswi as Hcswi_cs.
    assert (Hwics : forall r : mword 5, is_cs_idx r = true ->
              mwi !!! Regidx r = B0 !!! Regidx r).
    { intros r Hr. rewrite (callee_saved_lookup Hcswi_cs r Hr).
      exact (HQ6cs r Hr). }
    (* =================================================================
       WHAT WRITEI ANSWERED, in the ONE shape the rest of the body uses.
       This [assert] is the only place the two arms of writei's return
       disjunction are separated: everything below -- the offset update,
       the re-park, iunlock, end_op, the break test, both exits and the
       back edge -- is written once, against [rz] and against the two
       PURE re-park facts.  [dn0' = dn'] in both arms, which is what lets
       [ic_loaded] be rebuilt without a case split.
       ================================================================= *)
    assert (Hjoin : exists rz : Z,
              mwi !!! Regidx Ra0 = (mword_of_int rz : mword 64)
              /\ (-1 <= rz <= c)%Z
              /\ (bv_unsigned v + rz <= Z.of_nat MAXFILE * Z.of_nat BSIZE)%Z
              /\ inode_ok fsc_cov fsc_logst dn' bm' data'
              /\ dir_ok icfg_nib dn' data'
              /\ di_type dn' = di_type dnl
              /\ di_nlink dn' = di_nlink dnl
              /\ dn0' = dn').
    { destruct Harms as
        [(Hm1 & _ & Htot0 & _ & Hbmq & Hdataq & Hdnq & Hdn0q & _)
        | (Hcnt2 & Htotle & Hdnq & Hdn0q)].
      - exists (-1)%Z. subst bm' data' dn' dn0'. split_and!.
        (* EIGHT branches, not seven: [split_and!] splits the chained
           [-1 <= rz <= c] into TWO goals (the recorded trap). *)
        + exact Hm1.
        + lia.
        + lia.
        + rewrite /off_wf in Hwf. lia.
        + exact (fw_inode_ok_rebuild _ _ _ _ _ Hbmwf Hbmcov Hdaddr Hdty Hszb
                   Hholes Hsized).
        + exact (fw_dir_ok_same icfg_nib dnl datal Hnodir).
        + reflexivity.
        + reflexivity.
        + reflexivity.
      - exists (Z.of_nat tot). subst dn' dn0'.
        assert (Htotc : (Z.of_nat tot <= c)%Z)
          by (rewrite -Hcz; apply Nat2Z.inj_le; exact Htotle).
        assert (Hadv : (Z.of_nat (Z.to_nat (bv_unsigned v)) + Z.of_nat tot
                        <= Z.of_nat MAXFILE * Z.of_nat BSIZE)%Z).
        { apply (fw_off_tot_bound dnl bm' (Z.to_nat (bv_unsigned v)) tot Hszb).
          - (* [off_wf] is a Definition, so [fw_maxfile_bsize]'s LHS is not a
               subterm of [Hwf] until it is unfolded -- take the bound from
               [FileOff.off_wf_lt31] instead, which is already in [Z]. *)
            rewrite Hoffz.
            pose proof (off_wf_lt31 v Hwf) as Hw31.
            unfold SpecFilewrite.FW_MAX in Hcrange.
            change (2 ^ 31)%Z with 2147483648%Z in Hw31.
            change (2 ^ 32)%Z with 4294967296%Z. lia.
          - apply Hcap2. exact Hszb. }
        split_and!.
        + exact Hcnt2.
        + lia.
        + exact Htotc.
        + rewrite -Hoffz. exact Hadv.
        + apply fw_inode_ok_rebuild;
            [ exact Hbmwf2 | exact Hbmcov2 | exact Hdaddr2
            | rewrite fw_wi_type; exact Hdty
            | exact (Hcap2 Hszb) | exact Hholes2 | exact (Hsized2 Hsized) ].
        + exact (fw_dir_ok_wi icfg_nib dnl bm' (Z.to_nat (bv_unsigned v)) tot
                   data' Hnodir).
        + apply fw_wi_type.
        + reflexivity.
        + reflexivity. }
    destruct Hjoin as (rz & Hrza0 & Hrzr & Hrzadv & Hiok2 & Hdok2 & Htyq & Hnlq
                       & Hdn0q).
    (* the RESOURCE twin of [Hdok2] (design §20.3).  filewrite cannot reach a
       T_DIR inode -- sys_open refuses writable directories, which is what
       [Hnodir] records -- so the twin is [emp] at the record writei
       returned, exactly as [fw_dir_ok_wi] makes [dir_ok] vacuous there.  The
       incoming [Hdlnk] was [emp] for the same reason and is dropped. *)
    assert (Hnodir' : bv_unsigned (di_type dn') <> T_DIR_z)
      by (rewrite Htyq; exact Hnodir).
    (* the three record-only facts at writei's output (durable-disk
       2b-inode-3): the type and the count ride, and the directory clause is
       vacuous at a record filewrite has already refuted as a directory. *)
    assert (Hrl2 : inode_rec_local dn').
    { apply (inode_rec_local_same_type dnl dn' Hrl_datal Htyq).
      - rewrite Hnlq. exact (proj1 (proj2 Hrl_datal)).
      - intros Hd. exfalso. exact (Hnodir' Hd). }
    (* ---- +0xa4 c.mv s1,a0 : park the count ---- *)
    iApply (wp_cmv_s_sconf (mword_of_int (FW + 0xac)) Rs1 Ra0 mwi (K - 12)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (fwri_0ac with "Htext"). }
    iIntros (CIDb1 Hsb1) "Hcg Hpc". iEval (rgne) in "Hcg".
    set (W1 := <[Regidx Rs1 := regval_into_reg
                  (add_vec zero_reg (mwi !!! Regidx Ra0))]> mwi).
    assert (HW1s1 : W1 !!! Regidx Rs1 = (mword_of_int rz : mword 64)).
    { rewrite /W1 upd_eq. unfold regval_into_reg.
      rewrite add_vec_zero_l. exact Hrza0. }
    assert (HW1a0 : W1 !!! Regidx Ra0 = (mword_of_int rz : mword 64))
      by (rewrite /W1 upd_ne; [exact Hrza0 | vm_compute; discriminate]).
    assert (HW1cs : forall r : mword 5, is_cs_idx r = true -> r <> Rs1 ->
              W1 !!! Regidx r = B0 !!! Regidx r).
    { intros r Hr N1. rewrite /W1 upd_ne; [| regne]. exact (Hwics r Hr). }
    assert (HW1s2 : W1 !!! Regidx Rs2 = fnode kx)
      by (rewrite (HW1cs Rs2 ltac:(vm_compute; reflexivity)
                     ltac:(vm_compute; discriminate)); exact HB0s2).
    assert (Hppae : add_vec_int (mword_of_int (FW + 0xac) : mword 64) 2
                    = mword_of_int (FW + 0xae))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hppae) in "Hpc".
    (* ---- +0xa6 .. +0xb0 : the skip and the advance, BOTH ARMS ---- *)
    iApply (fw_offupd (CID0 := CIDb1) W1 (K - 12)%nat kx v rz (proc_addr jx) b
              HW1a0 HW1s2 ltac:(lia) Hwf Hrzadv
              with "Hcg Htext Hpc Hcell").
    iIntros (CIDb2 Hsb2 X0 v2) "%Hx Hcg Hpc Hcell".
    destruct Hx as [Hwf2 Hxcs].
    assert (HX0s1 : X0 !!! Regidx Rs1 = (mword_of_int rz : mword 64))
      by (rewrite (Hxcs Rs1 ltac:(vm_compute; reflexivity)); exact HW1s1).
    assert (HX0s2 : X0 !!! Regidx Rs2 = fnode kx)
      by (rewrite (Hxcs Rs2 ltac:(vm_compute; reflexivity)); exact HW1s2).
    assert (HX0cs : forall r : mword 5, is_cs_idx r = true -> r <> Rs1 ->
              X0 !!! Regidx r = B0 !!! Regidx r).
    { intros r Hr N1. rewrite (Hxcs r Hr). exact (HW1cs r Hr N1). }
    (* ---- CHECK IN the cell and REBUILD the checked-out bundle ---- *)
    iApply fupd_wp.
    iMod (off_checkin gf γox kx qx (DfracOwn (qx/2)) (fc_ip Cf) v2 ⊤
            ltac:(solve_ndisj) Hwf2 with "Hoh Hcip Hcell")
      as "(Hoh & Hcip & Hmark & Hrlv)".
    (* THE MOVER (namei-pinned-lookup.md §9 W3, the file-write row): writei
       moved this inode's bytes, so the hold moves with them.  The value is
       determined garbage -- the fd is provably not a directory here -- and
       the fragment is WHOLE, so the move is one free own-update and no delta
       is proved. *)
    (* the payload's last name carries [fv_ride * top_frag]; writei MOVED
       the record and the blocks, so the ride is set and the era's abstract
       value is RETAGGED at the new node (durable-disk 2b-inode-3). *)
    iDestruct "Hfview" as "[Hfview Htop]".
    iMod (dvw_set_rt ⊤ fsc_ireg fsc_fs (fwn_inodestart fn) icfg_nib
            (bv_unsigned inum) (dv_of dnl datal) (dv_of dn' data')
            (fv_of dnl datal) (fv_of dn' data')
            ltac:(solve_ndisj) with "Hireg Hdview Hfview")
      as "[Hdview Hfview]".
    (* THE RETAG OWES THE ROW (durable-disk lane A).  A write leaves the
       inode well-formed -- writei grows the size only after the block it
       needs is in the map -- and these are the four facts the re-pack
       below proves anyway; the fd is provably not a directory here, so the
       two dot clauses are vacuous. *)
    assert (Hlocw : inode_local (bv_unsigned inum) (era_node dn' bm' data')).
    { apply (inode_local_of_ok_rec (bv_unsigned inum) fsc_cov
               fsc_logst dn' bm' data' Hiok2 Hrl2).
      - exact (dir_uniq_not_dir dn' data' Hnodir').
      - exact (dir_dots_ix_not_dir (bv_unsigned inum) dn' data' Hnodir'). }
    iMod (ireg_top_retag ⊤ fsc_fs (bv_unsigned inum)
            (era_node dnl bml datal) (era_node dn' bm' data')
            ltac:(solve_ndisj) Hlocw with "[] Htop") as "Htop";
      [iApply (ireg_inv_ftop with "Hireg") |].
    iModIntro.
    iAssert (i_valid (ientry ik) ↦₄ valid_word true)%I
      with "[Hmark]" as "Hvalid".
    { rewrite -P8. iExact "Hmark". }
    iAssert (ic_loaded fsc_fs fsc_ireg fsc_cov
               fsc_logst ik inum dn' bm')
      with "[Hdnat Hmeta Hmap Hblocks Hdview Hfview Htop]" as "Hlk".
    { iApply ic_loaded_flat; rewrite /ic_loaded_flat_body /inode_map. iExists data'.
      iSplitR; [iPureIntro; exact Hiok2 |].
      iSplitR; [iPureIntro; exact Hrl2 |].
      iSplitR; [iPureIntro; exact Hdok2 |].
      iSplitR; [iPureIntro;
                exact (dir_dots_ix_not_dir (bv_unsigned inum) dn' data' Hnodir') |].
      iSplitR; [iPureIntro;
                exact (dir_orphan_clean_not_dir dn' data' Hnodir') |].
      iSplitR; [iPureIntro; exact (dir_uniq_not_dir dn' data' Hnodir') |].
      iSplitR; [iApply (dlinks_not_dir fsc_fs (bv_unsigned inum) dn' bm' data'
                          Hnodir') |].
      iDestruct "Hmap" as "[Haddrs Hindres]".
      rewrite Hdn0q.
      iFrame "Hdnat Hmeta Haddrs Hindres Hblocks Hdview Hfview Htop". }
    (* ---- +0xb4 ld a0,24(s2) ; +0xb8 jal ra,iunlock ---- *)
    assert (Hpip3 : add_vec (rget X0 Rs2)
                      (sign_extend' 64 (mword_of_int 24 : mword 12)) = a_fip kx).
    { rewrite (rget_ne X0 Rs2 ltac:(vm_compute; discriminate)) HX0s2.
      reflexivity. }
    iEval (rewrite -Hpip3) in "Hcip".
    iApply (wp_ld_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (FW + 0xbc)) Ra0 Rs2
              (mword_of_int 24 : mword 12) X0 (K - 12)%nat (fc_ip Cf) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] Hcip").
    { iApply (fwri_0bc with "Htext"). }
    iIntros (CIDb3 Hsb3) "Hcg Hpc Hcip". iEval (rewrite Hpip3) in "Hcip".
    set (X1 := <[Regidx Ra0 := regval_into_reg (fc_ip Cf)]> X0).
    assert (Hppc0 : add_vec_int (mword_of_int (FW + 0xbc) : mword 64) 4
                    = mword_of_int (FW + 0xc0))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hppc0) in "Hpc".
    iApply (wp_jal_s_sconf (mword_of_int (FW + 0xc0)) Rra
              (mword_of_int 2092756 : mword 21) X1 (K - 12)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(vm_compute; reflexivity) with "Hcg Hpc []").
    { iApply (fwri_0c0 with "Htext"). }
    iIntros (CIDb4 Hsb4) "Hcg Hpc".
    set (X2 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (FW + 0xc0) : mword 64) 4)]> X1).
    assert (Htgtiu : add_vec (mword_of_int (FW + 0xc0) : mword 64)
              (sign_extend' 64 (mword_of_int 2092756 : mword 21))
              = mword_of_int KernelSyms.iunlock)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtiu) in "Hpc".
    assert (HX2a0 : X2 !!! Regidx Ra0 = fc_ip Cf).
    { rewrite /X2 upd_ne; [| vm_compute; discriminate].
      rewrite /X1; apply upd_eq. }
    assert (HX2ra : X2 !!! Regidx Rra
                    = add_vec_int (mword_of_int (FW + 0xc0) : mword 64) 4)
      by (rewrite /X2; apply upd_eq).
    assert (HX2cs : forall r : mword 5, is_cs_idx r = true -> r <> Rs1 ->
              X2 !!! Regidx r = B0 !!! Regidx r).
    { intros r Hr N1. rewrite /X2 upd_ne; [| regne].
      rewrite /X1 upd_ne; [| regne]. exact (HX0cs r Hr N1). }
    assert (HX2s1 : X2 !!! Regidx Rs1 = (mword_of_int rz : mword 64)).
    { rewrite /X2 upd_ne; [| vm_compute; discriminate].
      rewrite /X1 upd_ne; [exact HX0s1 | vm_compute; discriminate]. }
    iDestruct (proc_priv_core_bare_acc (proc_addr jx) pidv
                 (upd_upt (upd_upt V PI) P') with "Hpriv") as "[Hppid Hpbk3]".
    iDestruct (cpu_own_transport CIDwi CIDb4 0%nat eb (proc_addr jx) b
                 ltac:(rewrite Hb; wp_next_chain) with "Hcnt") as "Hcnt".
    iApply (Iunlock.wp_iunlock_tx_sconf gs
              gil gisl
              ik (sh / 2)%Qp g icfg_dev
              inum dn' bm'
              pidv (DfracOwn (1/4)) X2 (K - 12)%nat eb (proc_addr jx) b lks
              (upd_upt (upd_upt V PI) P') (fw_av_iunlock K HK) P9 ltac:(rewrite HX2a0; exact P8)
              (* iunlock's bound is "sleep lock"(6); fw_loop's own is
                 "log"(3), and [locks_below_mono] weakens it. *)
              ltac:(lkbelow)
              with "Hcg Hcnt Htext Hpc Hit Hesc Hslk2
                    Hheld Hppid Hprocs
                    Hdep Hidev Hinum Hvalid Hlk [Hshot] Hfrz").
    all: try lkbelow.
    { rewrite Htyq. iExact "Hshot". }
    iIntros (CIDiu Hsiu miu) "%Hcsiu Hcg Hcnt Hpc Hppid Hshrb Htx".
    (* ...AND THE WRITE ARM COMES HOME inside [iunlock] (B''-tx): the
       descriptor named the share, so the token is whole again and [end_op]
       gets its [log_op] back. *)
    iEval (rewrite -Hclog) in "Htx".
    iDestruct (log_opS_op with "HlogS Htx") as "Hlogop".
    iDestruct (inode_shr_gen_forget with "Hshrb") as "Hshrb".
    iDestruct ("Hpbk3" with "Hppid") as "Hpriv".
    assert (Hpcbc : ret_pc (X2 !!! Regidx Rra) = mword_of_int (FW + 0xc4)).
    { rewrite HX2ra. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hpcbc) in "Hpc".
    pose proof Hcsiu as Hcsiu_cs.
    assert (Hiucs : forall r : mword 5, is_cs_idx r = true -> r <> Rs1 ->
              miu !!! Regidx r = B0 !!! Regidx r).
    { intros r Hr N1. rewrite (callee_saved_lookup Hcsiu_cs r Hr).
      exact (HX2cs r Hr N1). }
    assert (Hius1 : miu !!! Regidx Rs1 = (mword_of_int rz : mword 64)).
    { rewrite (callee_saved_lookup Hcsiu_cs Rs1 ltac:(vm_compute; reflexivity)).
      exact HX2s1. }
    (* THE SHARE, WHOLE AGAIN, at the generation the retained half names *)
    iDestruct (fw_shr_regen ik (sh / 2)%Qp (sh / 2)%Qp
                 icfg_dev inum g with "Hshrk Hshrb") as "Hshr".
    iEval (rewrite fw_qp_halves) in "Hshr".
    (* ...and back into the payload it came from.  From here the reference is
       intact again and the postcondition carries no share at all. *)
    iDestruct ("Hpayback" with "Hshr Hoh") as "Hrpay".
    (* ---- +0xbc jal ra,end_op : the transaction closes at whatever the
           chunk left of its reservation ([SpecEndOp] takes any [u]) ---- *)
    iApply (wp_jal_s_sconf (mword_of_int (FW + 0xc4)) Rra
              (mword_of_int 2095384 : mword 21) miu (K - 12)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(vm_compute; reflexivity) with "Hcg Hpc []").
    { iApply (fwri_0c4 with "Htext"). }
    iIntros (CIDb5 Hsb5) "Hcg Hpc".
    set (X3 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (FW + 0xc4) : mword 64) 4)]> miu).
    assert (Htgteo : add_vec (mword_of_int (FW + 0xc4) : mword 64)
              (sign_extend' 64 (mword_of_int 2095384 : mword 21))
              = mword_of_int KernelSyms.end_op)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgteo) in "Hpc".
    assert (HX3ra : X3 !!! Regidx Rra
                    = add_vec_int (mword_of_int (FW + 0xc4) : mword 64) 4)
      by (rewrite /X3; apply upd_eq).
    assert (HX3cs : forall r : mword 5, is_cs_idx r = true -> r <> Rs1 ->
              X3 !!! Regidx r = B0 !!! Regidx r).
    { intros r Hr N1. rewrite /X3 upd_ne; [| regne]. exact (Hiucs r Hr N1). }
    assert (HX3s1 : X3 !!! Regidx Rs1 = (mword_of_int rz : mword 64))
      by (rewrite /X3 upd_ne; [exact Hius1 | vm_compute; discriminate]).
    iDestruct (proc_priv_core_bare_acc (proc_addr jx) pidv
                 (upd_upt (upd_upt V PI) P') with "Hpriv") as "[Hppid Hpbk4]".
    iDestruct (cpu_own_transport CIDiu CIDb5 0%nat eb (proc_addr jx) b
                 ltac:(rewrite Hb; wp_next_chain) with "Hcnt") as "Hcnt".
    iApply (EndOp.wp_end_op_sconf gs jx glp (fwn_uart fn) (fwn_disk fn)
              (fwn_dlock fn) (fwn_pd fn) (fwn_pav fn) (fwn_pu fn)
              (fwn_bio fn) (fwn_log fn) fsc_fs
              fsc_cov fsc_logst icfg_dev n'
              pidv (DfracOwn (1/4)) X3 (K - 12)%nat eb b lks (upd_upt (upd_upt V PI) P')
              (fw_av_end_op K HK) P1 Hjp Hgsj
              Hbelow
              with "Hcg Hcnt [] [] Htext Hkd Hpc Hpenv Hbio Hlog Hcrash Hgc
                    Hppid Hprocs Hdev Hgeo Hdlk Hlogop").
    all: try lkbelow.
    { rewrite Heb /trap_csrs_ext. done. }
    { rewrite Heb /cpu_claim_ext. done. }
    iIntros (CIDeo Hseo meo) "%Hcseo Hcg Hcnt _ _ Hpc Hppid".
    iDestruct ("Hpbk4" with "Hppid") as "Hpriv".
    assert (Hpcc0 : ret_pc (X3 !!! Regidx Rra) = mword_of_int (FW + 0xc8)).
    { rewrite HX3ra. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hpcc0) in "Hpc".
    pose proof Hcseo as Hcseo_cs.
    assert (Heocs : forall r : mword 5, is_cs_idx r = true -> r <> Rs1 ->
              meo !!! Regidx r = B0 !!! Regidx r).
    { intros r Hr N1. rewrite (callee_saved_lookup Hcseo_cs r Hr).
      exact (HX3cs r Hr N1). }
    assert (Heos1 : meo !!! Regidx Rs1 = (mword_of_int rz : mword 64)).
    { rewrite (callee_saved_lookup Hcseo_cs Rs1 ltac:(vm_compute; reflexivity)).
      exact HX3s1. }
    assert (Heos3 : meo !!! Regidx Rs3 = (mword_of_int c : mword 64))
      by (rewrite (Heocs Rs3 ltac:(vm_compute; reflexivity)
                     ltac:(vm_compute; discriminate)); exact HB0s3).
    assert (Heos4 : meo !!! Regidx Rs4 = (mword_of_int iz : mword 64))
      by (rewrite (Heocs Rs4 ltac:(vm_compute; reflexivity)
                     ltac:(vm_compute; discriminate)); exact HB0s4).
    assert (Heos5 : meo !!! Regidx Rs5 = (mword_of_int n : mword 64))
      by (rewrite (Heocs Rs5 ltac:(vm_compute; reflexivity)
                     ltac:(vm_compute; discriminate)); exact HB0s5).
    assert (Heosp : meo !!! Regidx csp_rs1 = pa_stk sp0 12)
      by (rewrite (Heocs csp_rs1 ltac:(vm_compute; reflexivity)
                     ltac:(vm_compute; discriminate)); exact HB0sp).
    (* THE REFERENCE, back whole -- nothing below this point touches it *)
    iAssert (file_ref gf kx qx Cf)
      with "[Hrtok Hcty Hcrd Hcwr Hcpp Hcip Hcmaj Hrpay Hrlv]" as "Href".
    { rewrite /file_ref /file_fields.
      iFrame "Hrtok Hcty Hcrd Hcwr Hcpp Hcip Hcmaj Hrpay Hrlv". }
    (* THE EXCLUSIVE HALF, back at the set the chunk reached *)
    iAssert (filewrite_fs_out fn)
      with "[Hsbi Hsbsz Hsbb Hbsl]" as "Hout".
    { rewrite /filewrite_fs_out.
      iFrame "Hsbi Hsbsz Hsbb Hbsl". }
    (* the page-table descriptor, re-based on the contract's own [V] *)
    iEval (rewrite (fw_upd_upt_upd V PI P')) in "Hpriv".
    assert (Hupt2 : uptd_ext (pv_upt V) P').
    { apply (uptd_ext_trans (pv_upt V) PI P'); [exact Hext |].
      rewrite -(fw_pv_upt_upd V PI). exact Hupt. }
    (* =================================================================
       +0xc0 bne s3,s1 -- THE SHORT-WRITE BREAK.  Taken when the count is
       not the whole chunk, which is where writei's [-1] also goes.
       ================================================================= *)
    assert (Hcmpc0 : neq_vec (rget meo Rs3) (rget meo Rs1)
                     = negb (Z.eqb c rz)).
    { rewrite (rget_ne meo Rs3 ltac:(vm_compute; discriminate)).
      rewrite (rget_ne meo Rs1 ltac:(vm_compute; discriminate)).
      rewrite Heos3 Heos1. apply fw_neq_r; [exact Hclt31 | lia]. }
    assert (Htgtea : add_vec (mword_of_int (FW + 0xc8) : mword 64)
              (sign_extend' 64 (mword_of_int 26 : mword 13))
              = mword_of_int (FW + 0xe2))
      by (apply bv_eq; vm_compute; reflexivity).
    destruct (Z.eqb c rz) eqn:Hce.
    - (* ============ THE FULL CHUNK: fall to +0xc4 ============ *)
      assert (Hcrz : rz = c) by (symmetry; apply Z.eqb_eq; exact Hce).
      iApply (wp_bne_fall_s_sconf (mword_of_int (FW + 0xc8))
                (mword_of_int 26 : mword 13) Rs1 Rs3 meo (K - 12)%nat b
                ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                ltac:(rewrite Hcmpc0; reflexivity)
                with "Hcg Hpc []").
      { iApply (fwri_0c8 with "Htext"). }
      iIntros (CIDc1 Hsc1) "Hcg Hpc".
      assert (Hppcc : add_vec_int (mword_of_int (FW + 0xc8) : mword 64) 4
                      = mword_of_int (FW + 0xcc))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hppcc) in "Hpc".
      (* ---- +0xc4 addw s4,s1,s4 : i += r ---- *)
      iApply (wp_addw4_s_sconf (mword_of_int (FW + 0xcc)) Rs4 Rs1 Rs4
                meo (K - 12)%nat b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc []").
      { iApply (fwri_0cc with "Htext"). }
      iIntros (CIDc2 Hsc2) "Hcg Hpc". iEval (rgne; rgne) in "Hcg".
      set (Y1 := <[Regidx Rs4 := regval_into_reg
                    (sign_extend' 64 (add_vec
                       (subrange_vec_dec (meo !!! Regidx Rs1) 31 0 : mword 32)
                       (subrange_vec_dec (meo !!! Regidx Rs4) 31 0 : mword 32)))]> meo).
      assert (Hstep : (0 <= iz + c <= n)%Z /\ (n - (iz + c) < n - iz)%Z)
        by (apply fw_i_advance; lia).
      assert (HY1s4 : Y1 !!! Regidx Rs4 = (mword_of_int (iz + c) : mword 64)).
      { rewrite /Y1 upd_eq. unfold regval_into_reg.
        rewrite Heos1 Heos4 Hcrz.
        rewrite (fw_addw_moi iz c ltac:(lia) ltac:(lia) ltac:(lia)).
        f_equal. lia. }
      assert (HY1s5 : Y1 !!! Regidx Rs5 = (mword_of_int n : mword 64))
        by (rewrite /Y1 upd_ne; [exact Heos5 | vm_compute; discriminate]).
      assert (HY1sp : Y1 !!! Regidx csp_rs1 = pa_stk sp0 12)
        by (rewrite /Y1 upd_ne; [exact Heosp | vm_compute; discriminate]).
      assert (HY1cs : forall r : mword 5, is_cs_idx r = true ->
                r <> Rs1 -> r <> Rs4 -> Y1 !!! Regidx r = B0 !!! Regidx r).
      { intros r Hr N1 N4. rewrite /Y1 upd_ne; [| regne].
        exact (Heocs r Hr N1). }
      (* ---- +0xc8 bge s4,s5 : the exhaustion test ---- *)
      assert (Hcmpc8 : zopz0zKzJ_s (rget Y1 Rs4) (rget Y1 Rs5)
                       = Z.geb (iz + c) n).
      { rewrite (rget_ne Y1 Rs4 ltac:(vm_compute; discriminate)).
        rewrite (rget_ne Y1 Rs5 ltac:(vm_compute; discriminate)).
        rewrite HY1s4 HY1s5. apply fw_bge_moi; lia. }
      assert (Htgtda : add_vec (mword_of_int (FW + 0xd0) : mword 64)
                (sign_extend' 64 (mword_of_int 18 : mword 13))
                = mword_of_int (FW + 0xe2))
        by (apply bv_eq; vm_compute; reflexivity).
      destruct (Z.geb (iz + c) n) eqn:Hex.
      + (* ---- EXHAUSTED: i = n, the write completed ---- *)
        assert (Hizn : (iz + c = n)%Z)
          by (pose proof (proj1 (Z.geb_le _ _) Hex); lia).
        (* NO RESTORES HERE any more: 31f115a's gcc lets the exhaustion
           test branch straight into the tail, which owns the six. *)
        iApply (wp_bge_taken_s_sconf (mword_of_int (FW + 0xd0))
                  (mword_of_int 18 : mword 13) Rs5 Rs4 Y1 (K - 12)%nat b
                  ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                  ltac:(exact Hcmpc8)
                  ltac:(rewrite Htgtda; vm_compute; reflexivity)
                  with "Hcg Hpc []").
        { iApply (fwri_0d0 with "Htext"). }
        iApply bi.later_intro. iIntros (CIDc3 Hsc3) "Hcg Hpc".
        iEval (rewrite Htgtda) in "Hpc".
        assert (HY1thr2 : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
                  r <> Rs0 -> r <> Rs1 -> r <> Rs2 -> r <> Rs3 -> r <> Rs4 ->
                  r <> Rs5 -> r <> Rs6 -> r <> Rs7 -> r <> Rs8 -> r <> Rs9 ->
                  Y1 !!! Regidx r = m !!! Regidx r).
        { intros r Hr Nsp N0 N1 N2 N3 N4 N5 N6 N7 N8 N9.
          rewrite (HY1cs r Hr N1 N4).
          exact (HB0thr2 r Hr Nsp N0 N1 N2 N3 N4 N5 N6 N7 N8 N9). }
        iApply (fw_tail (CID0 := CIDc3) m Y1 K sp0 (m !!! Regidx Rra)
                  (m !!! Regidx Rs0) (m !!! Regidx Rs2) (m !!! Regidx Rs4)
                  (m !!! Regidx Rs5) (m !!! Regidx Rs6)
                  (m !!! Regidx Rs1) (m !!! Regidx Rs3) (m !!! Regidx Rs7)
                  (m !!! Regidx Rs8) (m !!! Regidx Rs9)
                  n (iz + c)%Z w12 (proc_addr jx) b
                  (fw_K12 K HK) Hn ltac:(lia) Hspm eq_refl eq_refl eq_refl
                  eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
                  eq_refl HY1sp HY1s5 HY1s4 HY1thr2
                  with "Hcg Htext Hpc Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hb7 Hb8 Hb9
                        Hb10 Hb11 Hb12").
        iIntros (CIDe Hse mfin rv) "%Hcsr Hcg Hpc".
        destruct Hcsr as (Hcsf & Hrv & Hdisj).
        iDestruct (cpu_own_transport CIDeo CIDe 0%nat eb (proc_addr jx) b
                     ltac:(rewrite Hb; wp_next_chain) with "Hcnt") as "Hcnt".
        iSpecialize ("Hcont" $! CIDe with "[]"); [iPureIntro; wp_next_chain|].
        iApply ("Hcont" $! mfin rv P'
                  with "[%] [%] [%] [%] Hcg Hcnt Hpc Href Hpriv [Hout]").
        { exact Hcsf. }
        { exact Hupt2. }
        { exact (fw_ret_of_tail n n (iz + c)%Z rv (proj1 Hn) eq_refl Hdisj). }
        { exact Hrv. }
        { iApply (fw_env_out_fs fn Cf Htyi). iExact "Hout". }
      + (* ---- NOT EXHAUSTED: the FALL is the back edge to +0xcc ---- *)
        assert (Hlt : (iz + c < n)%Z).
        { destruct (Z.le_gt_cases n (iz + c)) as [Hle | Hgt]; [| lia].
          exfalso. rewrite (proj2 (Z.geb_le (iz + c)%Z n) Hle) in Hex.
          discriminate. }
        iApply (wp_bge_fall_s_sconf (mword_of_int (FW + 0xd0))
                  (mword_of_int 18 : mword 13) Rs5 Rs4 Y1 (K - 12)%nat b
                  ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                  ltac:(exact Hcmpc8)
                  with "Hcg Hpc []").
        { iApply (fwri_0d0 with "Htext"). }
        iIntros (CIDc3 Hsc3) "Hcg Hpc".
        assert (Htgtcc2 : add_vec_int (mword_of_int (FW + 0xd0) : mword 64) 4
                          = mword_of_int (FW + 0xd4))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Htgtcc2) in "Hpc".
        (* THE BACK EDGE.  [IH] at the fuel [fw_i_advance] decreases and at
           the two carried components: [iz + c] and [P']. *)
        iDestruct (cpu_own_transport CIDeo CIDc3 0%nat eb (proc_addr jx) b
                     ltac:(rewrite Hb; wp_next_chain) with "Hcnt") as "Hcnt".
        (* [wp_next] IS HART-INDEXED TOO, and the back edge re-anchors the
           induction at [CIDc3].  The contract's crossing is held at the
           hart this iteration STARTED on; [IH] demands it at the one it is
           being re-entered on.  Same shape as [cpu_own_transport] and the
           same tell: the two printed types are identical and [iSpecialize]
           still refuses. *)
        iDestruct (wp_next_retarget CID0 CIDc3 true (proc_addr jx) _
                     ltac:(wp_next_chain) with "Hcont") as "Hcont".
        iApply (IH CIDc3 (iz + c)%Z P' Y1
                  ltac:(lia) ltac:(lia) Hupt2
                  HY1sp
                  ltac:(rewrite (HY1cs Rs2 ltac:(vm_compute; reflexivity)
                                  ltac:(vm_compute; discriminate)
                                  ltac:(vm_compute; discriminate)); exact HB0s2)
                  HY1s4 HY1s5
                  ltac:(rewrite (HY1cs Rs6 ltac:(vm_compute; reflexivity)
                                  ltac:(vm_compute; discriminate)
                                  ltac:(vm_compute; discriminate)); exact HB0s6)
                  ltac:(rewrite (HY1cs Rs7 ltac:(vm_compute; reflexivity)
                                  ltac:(vm_compute; discriminate)
                                  ltac:(vm_compute; discriminate)); exact HB0s7)
                  ltac:(rewrite (HY1cs Rs8 ltac:(vm_compute; reflexivity)
                                  ltac:(vm_compute; discriminate)
                                  ltac:(vm_compute; discriminate)); exact HB0s8)
                  ltac:(rewrite (HY1cs Rs9 ltac:(vm_compute; reflexivity)
                                  ltac:(vm_compute; discriminate)
                                  ltac:(vm_compute; discriminate)); exact HB0s9)
                  ltac:(intros r Hr Nsp N0 N1 N2 N3 N4 N5 N6 N7 N8 N9;
                        rewrite (HY1cs r Hr N1 N4);
                        exact (HB0thr2 r Hr Nsp N0 N1 N2 N3 N4 N5 N6 N7 N8 N9))
                  Hbelow
                  with "Hcg Hcnt Htext Hpc Hprocs
                        Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hb7 Hb8 Hb9 Hb10 Hb11 Hb12
                        Href Hpriv Hkenv
                        Hbio Hlog Hcrash Hgc Hkd Hpk Hit Hescs Hireg
                        Hslks Hdev Hgeo Hdlk Hbm Hout Hcont").
    - (* ====== THE SHORT WRITE (and writei's -1): straight to +0xe2 ======
         Before 31f115a this arm ran its own five restores at +0xea first;
         gcc now sends both loop exits into the tail, which owns them. *)
      iApply (wp_bne_taken_s_sconf (mword_of_int (FW + 0xc8))
                (mword_of_int 26 : mword 13) Rs1 Rs3 meo (K - 12)%nat b
                ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                ltac:(rewrite Hcmpc0; reflexivity)
                ltac:(rewrite Htgtea; vm_compute; reflexivity)
                with "Hcg Hpc []").
      { iApply (fwri_0c8 with "Htext"). }
      iNext. iIntros (CIDc2 Hsc2) "Hcg Hpc".
      iEval (rewrite Htgtea) in "Hpc".
      assert (Heothr2 : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
                r <> Rs0 -> r <> Rs1 -> r <> Rs2 -> r <> Rs3 -> r <> Rs4 ->
                r <> Rs5 -> r <> Rs6 -> r <> Rs7 -> r <> Rs8 -> r <> Rs9 ->
                meo !!! Regidx r = m !!! Regidx r).
      { intros r Hr Nsp N0 N1 N2 N3 N4 N5 N6 N7 N8 N9.
        rewrite (Heocs r Hr N1).
        exact (HB0thr2 r Hr Nsp N0 N1 N2 N3 N4 N5 N6 N7 N8 N9). }
      iApply (fw_tail (CID0 := CIDc2) m meo K sp0 (m !!! Regidx Rra)
                (m !!! Regidx Rs0) (m !!! Regidx Rs2) (m !!! Regidx Rs4)
                (m !!! Regidx Rs5) (m !!! Regidx Rs6)
                (m !!! Regidx Rs1) (m !!! Regidx Rs3) (m !!! Regidx Rs7)
                (m !!! Regidx Rs8) (m !!! Regidx Rs9)
                n iz w12 (proc_addr jx) b
                (fw_K12 K HK) Hn Hizlt31 Hspm eq_refl eq_refl eq_refl
                eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
                eq_refl Heosp Heos5 Heos4 Heothr2
                with "Hcg Htext Hpc Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hb7 Hb8 Hb9
                      Hb10 Hb11 Hb12").
      iIntros (CIDe Hse mfin rv) "%Hcsr Hcg Hpc".
      destruct Hcsr as (Hcsf & Hrv & Hdisj).
      iDestruct (cpu_own_transport CIDeo CIDe 0%nat eb (proc_addr jx) b
                   ltac:(rewrite Hb; wp_next_chain) with "Hcnt") as "Hcnt".
      iSpecialize ("Hcont" $! CIDe with "[]"); [iPureIntro; wp_next_chain|].
      iApply ("Hcont" $! mfin rv P'
                with "[%] [%] [%] [%] Hcg Hcnt Hpc Href Hpriv [Hout]").
      { exact Hcsf. }
      { exact Hupt2. }
      { exact (fw_ret_of_tail n n iz rv (proj1 Hn) eq_refl Hdisj). }
      { exact Hrv. }
      { iApply (fw_env_out_fs fn Cf Htyi). iExact "Hout". }
  Qed.

  Lemma wp_filewrite_sconf
      (γa γf : gname) (γs : list gname) (j : nat) (γlp : gname)
      (k : nat) (q : Qp) (Cf : fcontent) (fn : fwrite_names)
      (pidv : mword 32) (V : pprivate)
      (m : regfile) (K : nat) (eb : bool) (n : Z) (b : bool)
      (lks : gset string)
    : wp_filewrite_sconf_body γa γf γs j γlp k q Cf fn pidv V m K eb n b lks.
  Proof.
    cbv beta delta [wp_filewrite_sconf_body].
    intros pcE pj ret_tgt HK Hk Hj Hgs Hlens Hfnj Hfnps Ha0 Ha2 Hn Heb Hclog
           Hbelow.
    pose (sp0 := (m !!! Regidx csp_rs1 : mword 64)).
    iIntros "Hcg Hcnt #Htext #Hkd Hpc #Hpenv Href Hpriv Hkenv #Hprocs Henv Hcont".
    (* PIN THE INDEX.  This contract carries [eb = true ->] and [cpu_own] at
       level 0, so [cpu_own_eb_agree] forces [b] to be the literal [true].
       That is what reconciles the [true]-spelled crossings (this contract's
       own, consolewrite's, and the three parking contracts the loop body
       calls) with the [b]-spelled [cpu_own_transport]: from a [true]-indexed
       guard the [b]-indexed transport is underivable, so [Hb] is derived once
       and rewritten into the TRANSPORTS ONLY.  Goes when filewrite is
       eb-generalized.  ([ProofFilestat]'s recipe, verbatim.) *)
    iDestruct (cpu_own_eb_agree with "Hcg Hcnt") as %Hbm.
    assert (Hb : b = true) by (rewrite -Hbm; exact Heb).
    clear Hbm.
    assert (Hspm : m !!! Regidx csp_rs1 = sp0) by reflexivity.
    (* the reference, taken apart exactly as fileread does it: the dispatch
       reads f->writable and f->type out of the reference's OWN content
       fraction, so the loaded words ARE [fc_writable Cf] / [fc_type Cf]. *)
    iDestruct "Href" as "(Hrtok & Hrfields & Hrpay & Hrlv)".
    iEval (rewrite /file_fields) in "Hrfields".
    iDestruct "Hrfields" as "(Hcty & Hcrd & Hcwr & Hcpp & Hcip & Hcmaj)".
    (* =================================================================
       +0x00 lbu a5,9(a0) -- f->writable, BEFORE THE PROLOGUE (S3a's
       decode note 1: the -1 return at +0x10c runs with sp untouched).
       ================================================================= *)
    assert (Hpwr : add_vec (rget m Ra0) (sign_extend' 64 (mword_of_int 9 : mword 12))
                   = a_fwritable k).
    { rewrite (rget_ne m Ra0 ltac:(vm_compute; discriminate)) Ha0. reflexivity. }
    iEval (rewrite -Hpwr) in "Hcwr".
    iApply (wp_lbu_s_sconf (kt := KT1) (ktd := KT0) pcE Ra5 Ra0 (mword_of_int 9 : mword 12) m K
              (fc_writable Cf : mword 8) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] Hcwr").
    { iApply (fwri_000 with "Htext"). }
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
         NOT WRITABLE: [beq a5,x0] is taken to +0x10c, and the two
         instructions there are the whole exit -- [c.li a0,-1; c.jr ra],
         with sp, the frame and every callee-saved register untouched.
         =============================================================== *)
      assert (Htgt122 : add_vec (mword_of_int (FW + 0x04) : mword 64)
                (sign_extend' 64 (mword_of_int 310 : mword 13))
                = mword_of_int (FW + 0x13a))
        by (apply bv_eq; vm_compute; reflexivity).
      iApply (wp_beqz_x0_taken_s_sconf (mword_of_int (FW + 0x04))
                (mword_of_int 310 : mword 13) Ra5 R1 K b
                ltac:(vm_compute; discriminate)
                ltac:(rewrite HR1a5; exact Hwrz)
                ltac:(rewrite Htgt122; vm_compute; reflexivity)
                with "Hcg Hpc []").
      { iApply (fwri_004 with "Htext"). }
      iApply bi.later_intro. iIntros (CID2 Hs2) "Hcg Hpc".
      iEval (rewrite Htgt122) in "Hpc".
      (* ---- +0x10c c.li a0,-1 ---- *)
      iApply (wp_cli_s_sconf (mword_of_int (FW + 0x13a)) Ra0
                (mword_of_int 63 : mword 6) (mword_of_int (-1) : mword 64)
                R1 K b
                ltac:(vm_compute; discriminate) ltac:(rdok) fr_lim1
                with "Hcg Hpc []").
      { iApply (fwri_13a with "Htext"). }
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
      assert (Hpp13c : add_vec_int (mword_of_int (FW + 0x13a) : mword 64) 2
                       = mword_of_int (FW + 0x13c)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp13c) in "Hpc".
      (* ---- +0x124 c.jr ra ---- *)
      iApply (wp_cret_s_sconf (mword_of_int (FW + 0x13c)) Rra A1 K b
                ltac:(vm_compute; discriminate) with "Hcg Hpc []").
      { iApply (fwri_13c with "Htext"). }
      iIntros (CID4 Hs4) "Hcg Hpc".
      iEval (rewrite HA1ra) in "Hpc".
      iDestruct (cpu_own_transport CID CID4 0%nat eb pj b ltac:(rewrite Hb; wp_next_chain)
                   with "Hcnt") as "Hcnt".
      iSpecialize ("Hcont" $! CID4 with "[]"); [iPureIntro; wp_next_chain|].
      assert (HVid : upd_upt V (pv_upt V) = V) by apply fw_upd_upt_id.
      iApply ("Hcont" $! A1 (mword_of_int (-1)) (pv_upt V)
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
                (mword_of_int 310 : mword 13) Ra5 R1 K b
                ltac:(vm_compute; discriminate)
                ltac:(rewrite HR1a5; exact Hwrz)
                with "Hcg Hpc []").
      { iApply (fwri_004 with "Htext"). }
      iIntros (CID2 Hs2) "Hcg Hpc".
      assert (Hpp08 : add_vec_int (mword_of_int (FW + 0x04) : mword 64) 4
                      = mword_of_int (FW + 0x08)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp08) in "Hpc".
      (* ---- +0x08 .. +0x14 : the whole prologue, [fw_pro] ---- *)
      iApply (fw_pro (CID0 := CID2) R1 K sp0 pj b (fw_K12 K HK) HR1sp
                with "Hcg Htext Hpc").
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
      (* ---- +0x16 c.mv s2,a0 ; +0x18 c.mv s6,a1 ; +0x1a c.mv s5,a2 ---- *)
      iApply (wp_cmv_s_sconf (mword_of_int (FW + 0x16)) Rs2 Ra0 Mr (K - 12)%nat b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc []").
      { iApply (fwri_016 with "Htext"). }
      iIntros (CID4 Hs4) "Hcg Hpc". iEval (rgne) in "Hcg".
      set (G1 := <[Regidx Rs2 := regval_into_reg
                    (add_vec zero_reg (Mr !!! Regidx Ra0))]> Mr).
      assert (Hpp18 : add_vec_int (mword_of_int (FW + 0x16) : mword 64) 2
                      = mword_of_int (FW + 0x18)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp18) in "Hpc".
      iApply (wp_cmv_s_sconf (mword_of_int (FW + 0x18)) Rs6 Ra1 G1 (K - 12)%nat b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc []").
      { iApply (fwri_018 with "Htext"). }
      iIntros (CID5 Hs5) "Hcg Hpc". iEval (rgne) in "Hcg".
      set (G2 := <[Regidx Rs6 := regval_into_reg
                    (add_vec zero_reg (G1 !!! Regidx Ra1))]> G1).
      assert (Hpp1a : add_vec_int (mword_of_int (FW + 0x18) : mword 64) 2
                      = mword_of_int (FW + 0x1a)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp1a) in "Hpc".
      iApply (wp_cmv_s_sconf (mword_of_int (FW + 0x1a)) Rs5 Ra2 G2 (K - 12)%nat b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc []").
      { iApply (fwri_01a with "Htext"). }
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
      assert (HG3a2 : G3 !!! Regidx Ra2 = (mword_of_int n : mword 64)).
      { rewrite /G3 upd_ne; [| vm_compute; discriminate].
        rewrite /G2 upd_ne; [| vm_compute; discriminate].
        rewrite /G1 upd_ne; [exact HMa2 | vm_compute; discriminate]. }
      assert (HG3thr : forall c : mword 5, is_cs_idx c = true -> c <> csp_rs1 ->
                c <> Rs0 -> c <> Rs2 -> c <> Rs5 -> c <> Rs6 ->
                G3 !!! Regidx c = m !!! Regidx c).
      { intros c Hcs N2 N8 N18 N21 N22.
        rewrite /G3 upd_ne; [| regne].
        rewrite /G2 upd_ne; [| regne].
        rewrite /G1 upd_ne; [| regne].
        exact (HMthrm c Hcs N2 N8). }
      (* =============================================================
         +0x1c / +0x20 -- THE SIGN TEST (XV6_REV 31f115a).

         [srliw a5,a2,0x1f] lifts the count's sign bit and [bnez a5] is
         [if (n < 0) return -1].  This is what lets the CONTRACT take [n] at
         the whole [int] range: sys_write reads the count out of a trapframe
         word the user wrote, and no caller can promise anything about it.
         Past the fall-through [0 <= n] is a fact of the code, and the rest
         of this proof reads as it did before the guard existed.
         ============================================================= *)
      assert (Hpp1c : add_vec_int (mword_of_int (FW + 0x1a) : mword 64) 2
                      = mword_of_int (FW + 0x1c)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp1c) in "Hpc".
      assert (Hsrl : sign_extend' 64
                       (shift_bits_right
                          (subrange_vec_dec (rget G3 Ra2) 31 0 : mword 32)
                          (mword_of_int 31 : mword 5))
                     = (mword_of_int (if Z_lt_dec n 0 then 1 else 0) : mword 64)).
      { rewrite (rget_ne G3 Ra2 ltac:(vm_compute; discriminate)) HG3a2.
        apply fr_srliw31. exact Hn. }
      iApply (wp_srliw_s_sconf (mword_of_int (FW + 0x1c)) Ra5 Ra2
                (mword_of_int 31 : mword 5)
                (mword_of_int (if Z_lt_dec n 0 then 1 else 0) : mword 64)
                G3 (K - 12)%nat b ltac:(vm_compute; discriminate) ltac:(rdok) Hsrl
                with "Hcg Hpc []").
      { iApply (fwri_01c with "Htext"). }
      iIntros (CIDg1 Hsg1) "Hcg Hpc".
      set (G3g := <[Regidx Ra5 := regval_into_reg
                     (mword_of_int (if Z_lt_dec n 0 then 1 else 0) : mword 64)]> G3).
      assert (HG3ga5 : G3g !!! Regidx Ra5
                       = (mword_of_int (if Z_lt_dec n 0 then 1 else 0) : mword 64))
        by (rewrite /G3g; apply upd_eq).
      assert (HG3ga0 : G3g !!! Regidx Ra0 = fnode k)
        by (rewrite /G3g upd_ne; [exact HG3a0 | vm_compute; discriminate]).
      assert (HG3ga2 : G3g !!! Regidx Ra2 = (mword_of_int n : mword 64))
        by (rewrite /G3g upd_ne; [exact HG3a2 | vm_compute; discriminate]).
      assert (HG3gsp : G3g !!! Regidx csp_rs1 = pa_stk sp0 12)
        by (rewrite /G3g upd_ne; [exact HG3sp | vm_compute; discriminate]).
      assert (HG3gthr : forall c : mword 5, is_cs_idx c = true -> c <> csp_rs1 ->
                c <> Rs0 -> c <> Rs2 -> c <> Rs5 -> c <> Rs6 ->
                G3g !!! Regidx c = m !!! Regidx c).
      { intros c Hcs N2 N8 N18 N21 N22.
        rewrite /G3g upd_ne; [| regne]. exact (HG3thr c Hcs N2 N8 N18 N21 N22). }
      assert (Hpp20 : add_vec_int (mword_of_int (FW + 0x1c) : mword 64) 4
                      = mword_of_int (FW + 0x20)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp20) in "Hpc".
      destruct (Z_lt_dec n 0) as [Hneg | Hnn].
      { (* ---- n < 0 : the guard FIRES, and +0x11a is [fw_m1j] ---- *)
        assert (Htgt11a : add_vec (mword_of_int (FW + 0x20) : mword 64)
                  (sign_extend' 64 (mword_of_int 250 : mword 13))
                  = mword_of_int (FW + 0x11a))
          by (apply bv_eq; vm_compute; reflexivity).
        iApply (wp_bnez_x0_taken_s_sconf (mword_of_int (FW + 0x20))
                  (mword_of_int 250 : mword 13) Ra5 G3g (K - 12)%nat b
                  ltac:(vm_compute; discriminate)
                  ltac:(rewrite (rget_ne G3g Ra5 ltac:(vm_compute; discriminate)) HG3ga5;
                        exact fr_neq1_true)
                  ltac:(rewrite Htgt11a; vm_compute; reflexivity)
                  with "Hcg Hpc []").
        { iApply (fwri_020 with "Htext"). }
        iApply bi.later_intro. iIntros (CIDg2 Hsg2) "Hcg Hpc".
        iEval (rewrite Htgt11a) in "Hpc".
        iApply (fw_m1j (CID0 := CIDg2) G3g (K - 12)%nat
                  (FW + 0x11a) (FW + 0x11c)
                  (sign_extend' 21 (concat_vec (mword_of_int 2028 : mword 11) ('b"0")))
                  pj b
                  ltac:(apply bv_eq; vm_compute; reflexivity)
                  ltac:(apply bv_eq; vm_compute; reflexivity)
                  with "Hcg Hpc [] []").
        { iApply (fwri_11a with "Htext"). }
        { iApply (fwri_11c with "Htext"). }
        iIntros (CIDg3 Hsg3 Mg) "%Hmg Hcg Hpc".
        destruct Hmg as (Hmga0 & Hmgthr).
        assert (HMgsp : Mg !!! Regidx csp_rs1 = pa_stk sp0 12).
        { rewrite (Hmgthr csp_rs1 ltac:(vm_compute; reflexivity)). exact HG3gsp. }
        assert (HMgthr : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
                  r <> Rs0 -> r <> Rs2 -> r <> Rs5 -> r <> Rs6 ->
                  Mg !!! Regidx r = m !!! Regidx r).
        { intros r Hr Nsp N0 N2 N5 N6.
          rewrite (Hmgthr r Hr). exact (HG3gthr r Hr Nsp N0 N2 N5 N6). }
        iApply (fw_epi (CID0 := CIDg3) m Mg K sp0 (m !!! Regidx Rra)
                  (m !!! Regidx Rs0) (m !!! Regidx Rs2)
                  (m !!! Regidx Rs5) (m !!! Regidx Rs6)
                  (mword_of_int (-1)) w3 w5 w6 w9 w10 w11 w12 pj b
                  (fw_K12 K HK) Hspm eq_refl eq_refl eq_refl eq_refl eq_refl
                  HMgsp Hmga0 HMgthr
                  with "Hcg Htext Hpc Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hb7 Hb8 Hb9
                        Hb10 Hb11 Hb12").
        iIntros (CIDe Hse mfin) "%Hcsr Hcg Hpc".
        destruct Hcsr as [Hcsf Hrv].
        iDestruct (cpu_own_transport CID CIDe 0%nat eb pj b
                     ltac:(rewrite Hb; wp_next_chain) with "Hcnt") as "Hcnt".
        iSpecialize ("Hcont" $! CIDe with "[]"); [iPureIntro; wp_next_chain|].
        assert (HVid : upd_upt V (pv_upt V) = V) by apply fw_upd_upt_id.
        iApply ("Hcont" $! mfin (mword_of_int (-1)) (pv_upt V)
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
        { by iApply filewrite_env_out_of_env. } }
      (* ---- 0 <= n : [Hn0] is now a fact of the code, not a premise ---- *)
      assert (Hn0 : (0 <= n)%Z) by lia.
      assert (Hn01 : (0 <= n < 2 ^ 31)%Z) by lia.
      iApply (wp_bnez_x0_fall_s_sconf (mword_of_int (FW + 0x20))
                (mword_of_int 250 : mword 13) Ra5 G3g (K - 12)%nat b
                ltac:(vm_compute; discriminate)
                ltac:(rewrite (rget_ne G3g Ra5 ltac:(vm_compute; discriminate)) HG3ga5;
                      exact fr_neq0_false)
                with "Hcg Hpc []").
      { iApply (fwri_020 with "Htext"). }
      iIntros (CIDg2 Hsg2) "Hcg Hpc".
      assert (Hpp24 : add_vec_int (mword_of_int (FW + 0x20) : mword 64) 4
                      = mword_of_int (FW + 0x24)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp24) in "Hpc".
      (* ---- +0x24 c.lw a5,0(a0) : THE TYPE ---- *)
      assert (Hpty : add_vec (rget G3g Ra0) (sign_extend' 64 (mword_of_int 0 : mword 12))
                     = a_ftype k).
      { rewrite (rget_ne G3g Ra0 ltac:(vm_compute; discriminate)) HG3ga0.
        rewrite /a_ftype. apply addv_sext0. }
      iEval (rewrite -Hpty) in "Hcty".
      iApply (wp_clw_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (FW + 0x24)) Ra5 Ra0
                (mword_of_int 0 : mword 12) G3g (K - 12)%nat (fc_type Cf) b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc [] Hcty").
      { iApply (fwri_024 with "Htext"). }
      iIntros (CID7 Hs7) "Hcg Hpc Hcty". iEval (rewrite Hpty) in "Hcty".
      set (G4 := <[Regidx Ra5 := regval_into_reg (sign_extend' 64 (fc_type Cf))]> G3g).
      assert (HG4a5 : G4 !!! Regidx Ra5 = sign_extend' 64 (fc_type Cf))
        by (rewrite /G4; apply upd_eq).
      assert (Hpp26 : add_vec_int (mword_of_int (FW + 0x24) : mword 64) 2
                      = mword_of_int (FW + 0x26)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp26) in "Hpc".
      (* ---- +0x1e c.li a4,1 ; +0x20 beq a5,a4 -> +0x54 (FD_PIPE) ---- *)
      iApply (wp_cli_s_sconf (mword_of_int (FW + 0x26)) Ra4
                (mword_of_int 1 : mword 6) (mword_of_int 1 : mword 64)
                G4 (K - 12)%nat b
                ltac:(vm_compute; discriminate) ltac:(rdok) fr_li1
                with "Hcg Hpc []").
      { iApply (fwri_026 with "Htext"). }
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
        rewrite /G4 upd_ne; [exact HG3ga0 | vm_compute; discriminate]. }
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
        rewrite /G4 upd_ne; [exact HG3gsp | vm_compute; discriminate]. }
      assert (HG5thr : forall c : mword 5, is_cs_idx c = true -> c <> csp_rs1 ->
                c <> Rs0 -> c <> Rs2 -> c <> Rs5 -> c <> Rs6 ->
                G5 !!! Regidx c = m !!! Regidx c).
      { intros c Hcs N2 N8 N18 N21 N22.
        rewrite /G5 upd_ne; [| regne].
        rewrite /G4 upd_ne; [| regne].
        exact (HG3gthr c Hcs N2 N8 N18 N21 N22). }
      assert (Hpp28 : add_vec_int (mword_of_int (FW + 0x26) : mword 64) 2
                      = mword_of_int (FW + 0x28)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp28) in "Hpc".
      destruct (eq_vec (fc_type Cf) (mword_of_int 1 : mword 32)) eqn:Hp1.
      + (* ======================== FD_PIPE ==========================
           [c.ld a0,16(a0)] then [jal pipewrite]; the value it leaves in
           a0 is the return, and [c.j +0xa2] goes straight to [fw_epi]. *)
        assert (Htyp : fc_type Cf = FD_PIPE)
          by (apply eq_vec_true_iff; exact Hp1).
        iDestruct "Hrpay" as (pn) "[Hpn Hpl]".
        iEval (rewrite /file_payload /file_core Htyp bool_decide_eq_true_2;
               [| reflexivity]) in "Hpl".
        (* the entry's iref unit rides the pipe arm now ([file_core]); it is
           not piperead's business, so it stays here and goes back below. *)
        iDestruct "Hpl" as "[(#Hpipe & Hpref & Hiru) Hoh]".
        assert (Htgt54 : add_vec (mword_of_int (FW + 0x28) : mword 64)
                  (sign_extend' 64 (mword_of_int 52 : mword 13))
                  = mword_of_int (FW + 0x5c))
          by (apply bv_eq; vm_compute; reflexivity).
        iApply (wp_beq_taken_s_sconf (mword_of_int (FW + 0x28))
                  (mword_of_int 52 : mword 13) Ra4 Ra5 G5 (K - 12)%nat b
                  ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                  ltac:(rewrite Hcmp1; first [exact Hp1 | reflexivity])
                  ltac:(rewrite Htgt54; vm_compute; reflexivity)
                  with "Hcg Hpc []").
        { iApply (fwri_028 with "Htext"). }
        iApply bi.later_intro. iIntros (CID9 Hs9) "Hcg Hpc".
        iEval (rewrite Htgt54) in "Hpc".
        (* ---- +0x54 c.ld a0,16(a0) : a0 := f->pipe ---- *)
        assert (Hppi : add_vec (rget G5 Ra0) (sign_extend' 64 (mword_of_int 16 : mword 12))
                       = a_fpipe k).
        { rewrite (rget_ne G5 Ra0 ltac:(vm_compute; discriminate)) HG5a0. reflexivity. }
        iEval (rewrite -Hppi) in "Hcpp".
        iApply (wp_cld_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (FW + 0x5c)) Ra0 Ra0
                  (mword_of_int 16 : mword 12) G5 (K - 12)%nat (fc_pipe Cf) b
                  ltac:(vm_compute; discriminate) ltac:(rdok)
                  with "Hcg Hpc [] Hcpp").
        { iApply (fwri_05c with "Htext"). }
        iIntros (CID10 Hs10) "Hcg Hpc Hcpp". iEval (rewrite Hppi) in "Hcpp".
        set (P1 := <[Regidx Ra0 := regval_into_reg (fc_pipe Cf)]> G5).
        assert (Hpp5e : add_vec_int (mword_of_int (FW + 0x5c) : mword 64) 2
                        = mword_of_int (FW + 0x5e)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hpp5e) in "Hpc".
        (* ---- +0x56 jal ra,pipewrite ---- *)
        iApply (wp_jal_s_sconf (mword_of_int (FW + 0x5e)) Rra
                  (mword_of_int 518 : mword 21) P1 (K - 12)%nat b
                  ltac:(vm_compute; discriminate) ltac:(rdok)
                  ltac:(vm_compute; reflexivity) with "Hcg Hpc []").
        { iApply (fwri_05e with "Htext"). }
        iIntros (CID11 Hs11) "Hcg Hpc".
        set (P2 := <[Regidx Rra := regval_into_reg
                      (add_vec_int (mword_of_int (FW + 0x5e) : mword 64) 4)]> P1).
        assert (Htgtpw : add_vec (mword_of_int (FW + 0x5e) : mword 64)
                  (sign_extend' 64 (mword_of_int 518 : mword 21))
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
          rewrite /G3g upd_ne; [| vm_compute; discriminate].
          rewrite /G2 upd_ne; [| vm_compute; discriminate].
          rewrite /G1 upd_ne; [exact HMa2 | vm_compute; discriminate]. }
        assert (HP2ra : P2 !!! Regidx Rra
                        = add_vec_int (mword_of_int (FW + 0x5e) : mword 64) 4)
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
        iDestruct (cpu_own_transport CID CID11 0%nat eb pj b ltac:(rewrite Hb; wp_next_chain)
                     with "Hcnt") as "Hcnt".
        iApply (Pipewrite.wp_pipewrite_sconf γa γf γs j γlp (fp_lock pn) (fp_pipe pn)
                  (fc_wbool Cf) q P2 (K - 12)%nat eb pidv V n b lks
                  Hj Hgs Hlens HP2a2 (fw_n_range n Hn01) (fw_av_pipe K HK) Heb
                  with "Hcg Hcnt Htext Hpc [] Hpref Hpriv Hkenv Hprocs").
        all: try lkbelow.
        { iEval (rewrite HP2a0). iExact "Hpipe". }
        iIntros (CIDpw Hspw mf P') "%Hcspw %Hupt %Hretpw Hcg Hcnt Hpc Hpref Hpriv".
        assert (Hpc5a : ret_pc (P2 !!! Regidx Rra) = mword_of_int (FW + 0x62)).
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
        assert (Htgtfc : add_vec (mword_of_int (FW + 0x62) : mword 64)
                  (sign_extend' 64 (sign_extend' 21
                     (concat_vec (mword_of_int 73 : mword 11) ('b"0"))))
                  = mword_of_int (FW + 0xf4))
          by (apply bv_eq; vm_compute; reflexivity).
        iApply (wp_cj_s_sconf (mword_of_int (FW + 0x62))
                  (sign_extend' 21 (concat_vec (mword_of_int 73 : mword 11) ('b"0")))
                  mf (K - 12)%nat b
                  ltac:(rewrite Htgtfc; vm_compute; reflexivity)
                  with "Hcg Hpc []").
        { iApply (fwri_062 with "Htext"). }
        iIntros (CID12 Hs12). iApply bi.later_intro. iIntros "Hcg Hpc".
        iEval (rewrite Htgtfc) in "Hpc".
        iApply (fw_epi (CID0 := CID12) m mf K sp0 (m !!! Regidx Rra)
                  (m !!! Regidx Rs0) (m !!! Regidx Rs2) (m !!! Regidx Rs5)
                  (m !!! Regidx Rs6) (mf !!! Regidx Ra0)
                  w3 w5 w6 w9 w10 w11 w12 pj b
                  (fw_K12 K HK) Hspm eq_refl eq_refl eq_refl eq_refl eq_refl
                  Hmfsp eq_refl Hmfthr
                  with "Hcg Htext Hpc Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hb7 Hb8 Hb9 Hb10
                        Hb11 Hb12").
        iIntros (CIDe Hse mfin) "%Hcsr Hcg Hpc".
        destruct Hcsr as [Hcsf Hrv].
        iDestruct (cpu_own_transport CIDpw CIDe 0%nat eb pj b ltac:(rewrite Hb; wp_next_chain)
                     with "Hcnt") as "Hcnt".
        iSpecialize ("Hcont" $! CIDe with "[]"); [iPureIntro; wp_next_chain|].
        iApply ("Hcont" $! mfin (mf !!! Regidx Ra0) P'
                  with "[%] [%] [%] [%] Hcg Hcnt [Hpc]
                        [Hrtok Hcty Hcrd Hcwr Hcpp Hcip Hcmaj Hpn Hpref Hiru Hoh Hrlv]
                        Hpriv [Henv]").
        { exact Hcsf. }
        { exact Hupt. }
        { by apply fw_ret_of_pipe. }
        { exact Hrv. }
        { iEval (rewrite /ret_tgt). iExact "Hpc". }
        { rewrite /file_ref /file_fields /file_pay.
          iFrame "Hrtok Hcty Hcrd Hcwr Hcpp Hcip Hcmaj Hrlv".
          iExists pn. iFrame "Hpn".
          rewrite /file_payload /file_core Htyp bool_decide_eq_true_2;
            [| reflexivity].
          iFrame "Hpipe Hpref Hiru Hoh". }
        { by iApply filewrite_env_out_of_env. }
      + (* ---- +0x24 c.li a4,3 ; +0x26 beq a5,a4 -> +0x5c (FD_DEVICE) ---- *)
        iApply (wp_beq_fall_s_sconf (mword_of_int (FW + 0x28))
                  (mword_of_int 52 : mword 13) Ra4 Ra5 G5 (K - 12)%nat b
                  ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                  ltac:(rewrite Hcmp1; first [exact Hp1 | reflexivity])
                  with "Hcg Hpc []").
        { iApply (fwri_028 with "Htext"). }
        iIntros (CID9 Hs9) "Hcg Hpc".
        assert (Hpp2c : add_vec_int (mword_of_int (FW + 0x28) : mword 64) 4
                        = mword_of_int (FW + 0x2c)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hpp2c) in "Hpc".
        iApply (wp_cli_s_sconf (mword_of_int (FW + 0x2c)) Ra4
                  (mword_of_int 3 : mword 6) (mword_of_int 3 : mword 64)
                  G5 (K - 12)%nat b
                  ltac:(vm_compute; discriminate) ltac:(rdok) fr_li3
                  with "Hcg Hpc []").
        { iApply (fwri_02c with "Htext"). }
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
        assert (Hpp2e : add_vec_int (mword_of_int (FW + 0x2c) : mword 64) 2
                        = mword_of_int (FW + 0x2e)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hpp2e) in "Hpc".
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
          iDestruct (fw_env_dev γf fn Cf Htyd with "Henv") as "Henv".
          pose proof (fw_major_range (fc_major Cf : mword 16)) as Hmjr.
          assert (Htgt5c : add_vec (mword_of_int (FW + 0x2e) : mword 64)
                    (sign_extend' 64 (mword_of_int 54 : mword 13))
                    = mword_of_int (FW + 0x64))
            by (apply bv_eq; vm_compute; reflexivity).
          iApply (wp_beq_taken_s_sconf (mword_of_int (FW + 0x2e))
                    (mword_of_int 54 : mword 13) Ra4 Ra5 G6 (K - 12)%nat b
                    ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                    ltac:(rewrite Hcmp3; first [exact Hp3 | reflexivity])
                    ltac:(rewrite Htgt5c; vm_compute; reflexivity)
                    with "Hcg Hpc []").
          { iApply (fwri_02e with "Htext"). }
          iApply bi.later_intro. iIntros (CID11 Hs11) "Hcg Hpc".
          iEval (rewrite Htgt5c) in "Hpc".
          (* ---- +0x5c lh a5,36(a0) : f->major, SIGN-extended ---- *)
          assert (Hpmj : add_vec (rget G6 Ra0) (sign_extend' 64 (mword_of_int 36 : mword 12))
                         = a_fmajor k).
          { rewrite (rget_ne G6 Ra0 ltac:(vm_compute; discriminate)) HG6a0. reflexivity. }
          iEval (rewrite -Hpmj) in "Hcmaj".
          iApply (wp_lh_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (FW + 0x64)) Ra5 Ra0
                    (mword_of_int 36 : mword 12) G6 (K - 12)%nat (fc_major Cf : mword 16) b
                    ltac:(vm_compute; discriminate) ltac:(rdok)
                    with "Hcg Hpc [] Hcmaj").
          { iApply (fwri_064 with "Htext"). }
          iIntros (CID12 Hs12) "Hcg Hpc Hcmaj". iEval (rewrite Hpmj) in "Hcmaj".
          set (D1 := <[Regidx Ra5 := regval_into_reg
                        (sign_extend' 64 (fc_major Cf : mword 16))]> G6).
          assert (HD1a5 : D1 !!! Regidx Ra5 = sign_extend' 64 (fc_major Cf : mword 16))
            by (rewrite /D1; apply upd_eq).
          assert (Hpp68 : add_vec_int (mword_of_int (FW + 0x64) : mword 64) 4
                          = mword_of_int (FW + 0x68)) by (apply bv_eq; vm_compute; reflexivity).
          iEval (rewrite Hpp68) in "Hpc".
          (* ---- +0x60 slli a3,a5,48 ---- *)
          assert (Hsl48 : shift_bits_left (rget D1 Ra5)
                            (subrange_vec_dec (mword_of_int 48 : mword 6) (Z.sub log2_xlen 1) 0)
                          = shift_bits_left (sign_extend' 64 (fc_major Cf : mword 16) : mword 64)
                            (subrange_vec_dec (mword_of_int 48 : mword 6) (Z.sub log2_xlen 1) 0)).
          { rewrite (rget_ne D1 Ra5 ltac:(vm_compute; discriminate)) HD1a5. reflexivity. }
          iApply (wp_slli_s_sconf (mword_of_int (FW + 0x68)) Ra3 Ra5
                    (mword_of_int 48 : mword 6)
                    (shift_bits_left (sign_extend' 64 (fc_major Cf : mword 16) : mword 64)
                       (subrange_vec_dec (mword_of_int 48 : mword 6) (Z.sub log2_xlen 1) 0))
                    D1 (K - 12)%nat b
                    ltac:(vm_compute; discriminate) ltac:(rdok) Hsl48
                    with "Hcg Hpc []").
          { iApply (fwri_068 with "Htext"). }
          iIntros (CID13 Hs13) "Hcg Hpc".
          set (D2 := <[Regidx Ra3 := regval_into_reg
                        (shift_bits_left (sign_extend' 64 (fc_major Cf : mword 16) : mword 64)
                           (subrange_vec_dec (mword_of_int 48 : mword 6)
                              (Z.sub log2_xlen 1) 0))]> D1).
          assert (Hpp6c : add_vec_int (mword_of_int (FW + 0x68) : mword 64) 4
                          = mword_of_int (FW + 0x6c)) by (apply bv_eq; vm_compute; reflexivity).
          iEval (rewrite Hpp6c) in "Hpc".
          (* ---- +0x64 c.srli a3,a3,48 : the zero extension ---- *)
          assert (Hc5 : creg2reg_idx (Cregidx (mword_of_int 5)) = Regidx Ra3)
            by (vm_compute; reflexivity).
          iApply (wp_csrli_s_sconf (mword_of_int (FW + 0x6c)) (Cregidx (mword_of_int 5))
                    Ra3 (mword_of_int 48 : mword 6) D2 (K - 12)%nat b
                    Hc5 ltac:(vm_compute; discriminate) ltac:(rdok)
                    with "Hcg Hpc []").
          { iEval (rewrite -Hc5). iApply (fwri_06c with "Htext"). }
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
          assert (Hpp6e : add_vec_int (mword_of_int (FW + 0x6c) : mword 64) 2
                          = mword_of_int (FW + 0x6e)) by (apply bv_eq; vm_compute; reflexivity).
          iEval (rewrite Hpp6e) in "Hpc".
          (* ---- +0x66 c.li a4,9 ---- *)
          iApply (wp_cli_s_sconf (mword_of_int (FW + 0x6e)) Ra4
                    (mword_of_int 9 : mword 6) (mword_of_int 9 : mword 64)
                    D3 (K - 12)%nat b
                    ltac:(vm_compute; discriminate) ltac:(rdok) fr_li9
                    with "Hcg Hpc []").
          { iApply (fwri_06e with "Htext"). }
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
          assert (Hpp70 : add_vec_int (mword_of_int (FW + 0x6e) : mword 64) 2
                          = mword_of_int (FW + 0x70)) by (apply bv_eq; vm_compute; reflexivity).
          iEval (rewrite Hpp70) in "Hpc".
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
             iDestruct (fw_dev_in fn Cf Hin with "Henv")
               as "(%Hwp & Hslot & #Hdevinv & #Htxlk)".
             iApply (wp_bltu_fall_s_sconf (mword_of_int (FW + 0x70))
                       (mword_of_int 174 : mword 13) Ra3 Ra4 D4 (K - 12)%nat b
                       ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                       ltac:(rewrite HD4a4 HD4a3; exact (fw_bltu9_false _ Hmj0 Hin))
                       with "Hcg Hpc []").
             { iApply (fwri_070 with "Htext"). }
             iIntros (CID16 Hs16) "Hcg Hpc".
             assert (Hpp74 : add_vec_int (mword_of_int (FW + 0x70) : mword 64) 4
                             = mword_of_int (FW + 0x74)) by (apply bv_eq; vm_compute; reflexivity).
             iEval (rewrite Hpp74) in "Hpc".
             (* ---- +0x6c .. +0x78 : &devsw[major].write, and its value ---- *)
             assert (HD4a5m : D4 !!! Regidx Ra5
                              = (mword_of_int (bv_unsigned (fc_major Cf)) : mword 64)).
             { rewrite HD4a5. apply fr_sext16_small. exact Hmj15. }
             iEval (rewrite /a_devsw_write /dev_major) in "Hslot".
             iApply (fw_devidx (CID0 := CID16) D4 (K - 12)%nat
                       (bv_unsigned (fc_major Cf)) (fwn_wp fn (dev_major Cf)) (fwn_dqv fn (dev_major Cf)) pj b
                       (conj Hmj0 Hmj16) HD4a5m
                       with "Hcg Htext Hpc Hslot").
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
                assert (Htgt12a : add_vec (mword_of_int (FW + 0x82) : mword 64)
                          (sign_extend' 64 (sign_extend' 13
                             (concat_vec (mword_of_int 80 : mword 8) ('b"0"))))
                          = mword_of_int (FW + 0x122))
                  by (apply bv_eq; vm_compute; reflexivity).
                iApply (wp_cbeqz_taken_s_sconf (mword_of_int (FW + 0x82))
                          (mword_of_int 80 : mword 8) (Cregidx (mword_of_int 7)) Ra5
                          Dr (K - 12)%nat b Hc7 ltac:(vm_compute; discriminate)
                          ltac:(rewrite (rget_ne Dr Ra5 ltac:(vm_compute; discriminate))
                                  HDra5 Hwp0; apply eq_vec_true_iff; reflexivity)
                          ltac:(rewrite Htgt12a; vm_compute; reflexivity)
                          with "Hcg Hpc []").
                { iApply (fwri_082 with "Htext"). }
                iApply bi.later_intro. iIntros (CID18 Hs18) "Hcg Hpc".
                iEval (rewrite Htgt12a) in "Hpc".
                iApply (fw_m1j (CID0 := CID18) Dr (K - 12)%nat
                          (FW + 0x122) (FW + 0x124)
                          (sign_extend' 21 (concat_vec (mword_of_int 2024 : mword 11) ('b"0")))
                          pj b
                          ltac:(apply bv_eq; vm_compute; reflexivity)
                          ltac:(apply bv_eq; vm_compute; reflexivity)
                          with "Hcg Hpc [] []").
                { iApply (fwri_122 with "Htext"). }
                { iApply (fwri_124 with "Htext"). }
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
                                Hb11 Hb12").
                iIntros (CIDe Hse mfin) "%Hcsr Hcg Hpc".
                destruct Hcsr as [Hcsf Hrv].
                iDestruct (cpu_own_transport CID CIDe 0%nat eb pj b ltac:(rewrite Hb; wp_next_chain)
                             with "Hcnt") as "Hcnt".
                iSpecialize ("Hcont" $! CIDe with "[]"); [iPureIntro; wp_next_chain|].
                assert (HVid : upd_upt V (pv_upt V) = V) by apply fw_upd_upt_id.
                iApply ("Hcont" $! mfin (mword_of_int (-1)) (pv_upt V)
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
                { iApply (fw_env_out_dev fn Cf Htyd).
                  iApply (fw_dev_in_back fn Cf Hin with "[%] Hslot Hdevinv Htxlk").
                  by left. }
             ** (* ---- consolewrite: the INDIRECT CALL at +0x7e ---- *)
                iApply (wp_cbeqz_fall_s_sconf (mword_of_int (FW + 0x82))
                          (mword_of_int 80 : mword 8) (Cregidx (mword_of_int 7)) Ra5
                          Dr (K - 12)%nat b Hc7 ltac:(vm_compute; discriminate)
                          ltac:(rewrite (rget_ne Dr Ra5 ltac:(vm_compute; discriminate))
                                  HDra5 Hwpc; apply eq_vec_false_iff;
                                intro Hc; apply (f_equal (@bv_unsigned _)) in Hc;
                                vm_compute in Hc; discriminate)
                          with "Hcg Hpc []").
                { iApply (fwri_082 with "Htext"). }
                iIntros (CID18 Hs18) "Hcg Hpc".
                assert (Hpp84 : add_vec_int (mword_of_int (FW + 0x82) : mword 64) 2
                                = mword_of_int (FW + 0x84)) by (apply bv_eq; vm_compute; reflexivity).
                iEval (rewrite Hpp84) in "Hpc".
                (* +0x7c c.li a0,1 : the source is a USER address *)
                iApply (wp_cli_s_sconf (mword_of_int (FW + 0x84)) Ra0
                          (mword_of_int 1 : mword 6) (mword_of_int 1 : mword 64)
                          Dr (K - 12)%nat b
                          ltac:(vm_compute; discriminate) ltac:(rdok) fr_li1
                          with "Hcg Hpc []").
                { iApply (fwri_084 with "Htext"). }
                iIntros (CID19 Hs19) "Hcg Hpc".
                set (E1 := <[Regidx Ra0 := regval_into_reg (mword_of_int 1 : mword 64)]> Dr).
                assert (HE1a5 : E1 !!! Regidx Ra5
                                = (mword_of_int KernelSyms.consolewrite : mword 64)).
                { rewrite /E1 upd_ne; [| vm_compute; discriminate].
                  rewrite HDra5. exact Hwpc. }
                assert (Hpp86 : add_vec_int (mword_of_int (FW + 0x84) : mword 64) 2
                                = mword_of_int (FW + 0x86)) by (apply bv_eq; vm_compute; reflexivity).
                iEval (rewrite Hpp86) in "Hpc".
                (* +0x7e c.jalr a5 -- the indirect call *)
                iApply (wp_cjalr_s_sconf (mword_of_int (FW + 0x86)) Ra5 Rra
                          E1 (K - 12)%nat b
                          ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                          ltac:(rdok) with "Hcg Hpc []").
                { iApply (fwri_086 with "Htext"). }
                iIntros (CID20 Hs20) "Hcg Hpc".
                set (E2 := <[Regidx Rra := regval_into_reg
                              (add_vec_int (mword_of_int (FW + 0x86) : mword 64) 2)]> E1).
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
                  rewrite /G3g upd_ne; [| vm_compute; discriminate].
                  rewrite /G2 upd_ne; [| vm_compute; discriminate].
                  rewrite /G1 upd_ne; [exact HMa2 | vm_compute; discriminate]. }
                assert (HE2ra : E2 !!! Regidx Rra
                                = add_vec_int (mword_of_int (FW + 0x86) : mword 64) 2)
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
                iDestruct (cpu_own_transport CID CID20 0%nat eb pj b ltac:(rewrite Hb; wp_next_chain)
                             with "Hcnt") as "Hcnt".
                iApply (Consolewrite.wp_consolewrite_sconf γa γf γs j γlp
                          (fwn_uart fn) (fwn_disk fn) (fwn_txlock fn)
                          E2 (K - 12)%nat eb pidv V n b lks
                          Hj Hgs Hlens HE2a0 HE2a2 (fw_n_range n Hn01)
                          (fw_av_cons K HK) Heb
                          with "Hcg Hcnt Htext Hpc Hpriv Hkenv Hdevinv Htxlk
                                Hprocs").
                all: try lkbelow.
                iIntros (CIDcw Hscw mf r P') "%Hcscw %Hupt %Hrr %Hra0 Hcg Hcnt Hpc Hpriv".
                assert (Hpc80 : ret_pc (E2 !!! Regidx Rra) = mword_of_int (FW + 0x88)).
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
                assert (Htgtfcd : add_vec (mword_of_int (FW + 0x88) : mword 64)
                          (sign_extend' 64 (sign_extend' 21
                             (concat_vec (mword_of_int 54 : mword 11) ('b"0"))))
                          = mword_of_int (FW + 0xf4))
                  by (apply bv_eq; vm_compute; reflexivity).
                iApply (wp_cj_s_sconf (mword_of_int (FW + 0x88))
                          (sign_extend' 21 (concat_vec (mword_of_int 54 : mword 11) ('b"0")))
                          mf (K - 12)%nat b
                          ltac:(rewrite Htgtfcd; vm_compute; reflexivity)
                          with "Hcg Hpc []").
                { iApply (fwri_088 with "Htext"). }
                iIntros (CID21 Hs21). iApply bi.later_intro. iIntros "Hcg Hpc".
                iEval (rewrite Htgtfcd) in "Hpc".
                iApply (fw_epi (CID0 := CID21) m mf K sp0 (m !!! Regidx Rra)
                          (m !!! Regidx Rs0) (m !!! Regidx Rs2) (m !!! Regidx Rs5)
                          (m !!! Regidx Rs6) (mword_of_int r)
                          w3 w5 w6 w9 w10 w11 w12 pj b
                          (fw_K12 K HK) Hspm eq_refl eq_refl eq_refl eq_refl eq_refl
                          Hmfsp Hra0 Hmfthr
                          with "Hcg Htext Hpc Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hb7 Hb8 Hb9 Hb10
                                Hb11 Hb12").
                iIntros (CIDe Hse mfin) "%Hcsr Hcg Hpc".
                destruct Hcsr as [Hcsf Hrv].
                iDestruct (cpu_own_transport CIDcw CIDe 0%nat eb pj b ltac:(rewrite Hb; wp_next_chain)
                             with "Hcnt") as "Hcnt".
                iSpecialize ("Hcont" $! CIDe with "[]"); [iPureIntro; wp_next_chain|].
                iApply ("Hcont" $! mfin (mword_of_int r) P'
                          with "[%] [%] [%] [%] Hcg Hcnt [Hpc]
                                [Hrtok Hcty Hcrd Hcwr Hcpp Hcip Hcmaj Hrpay Hrlv]
                                Hpriv [Hslot]").
                { exact Hcsf. }
                { exact Hupt. }
                { apply (fw_ret_of_dev n r (mword_of_int r) Hn0);
                    [pose proof Hn0; lia | reflexivity]. }
                { exact Hrv. }
                { iEval (rewrite /ret_tgt). iExact "Hpc". }
                { rewrite /file_ref /file_fields.
                  iFrame "Hrtok Hcty Hcrd Hcwr Hcpp Hcip Hcmaj Hrpay Hrlv". }
                { iApply (fw_env_out_dev fn Cf Htyd).
                  iApply (fw_dev_in_back fn Cf Hin with "[%] Hslot Hdevinv Htxlk").
                  by right. }
          ++ (* ---------- OUT OF RANGE: the [bltu] is taken to +0x126 ------- *)
             assert (Hmjgt : (9 < bv_unsigned (fc_major Cf))%Z)
               by (unfold dev_major, NDEV_max in Hout; lia).
             assert (Htgt126 : add_vec (mword_of_int (FW + 0x70) : mword 64)
                       (sign_extend' 64 (mword_of_int 174 : mword 13))
                       = mword_of_int (FW + 0x11e))
               by (apply bv_eq; vm_compute; reflexivity).
             iApply (wp_bltu_taken_s_sconf (mword_of_int (FW + 0x70))
                       (mword_of_int 174 : mword 13) Ra3 Ra4 D4 (K - 12)%nat b
                       ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                       ltac:(rewrite HD4a4 HD4a3;
                             exact (fw_bltu9_true _ Hmjgt (proj2 Hmjr)))
                       ltac:(rewrite Htgt126; vm_compute; reflexivity)
                       with "Hcg Hpc []").
             { iApply (fwri_070 with "Htext"). }
             iApply bi.later_intro. iIntros (CID16 Hs16) "Hcg Hpc".
             iEval (rewrite Htgt126) in "Hpc".
             iApply (fw_m1j (CID0 := CID16) D4 (K - 12)%nat
                       (FW + 0x11e) (FW + 0x120)
                       (sign_extend' 21 (concat_vec (mword_of_int 2026 : mword 11) ('b"0")))
                       pj b
                       ltac:(apply bv_eq; vm_compute; reflexivity)
                       ltac:(apply bv_eq; vm_compute; reflexivity)
                       with "Hcg Hpc [] []").
             { iApply (fwri_11e with "Htext"). }
             { iApply (fwri_120 with "Htext"). }
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
                             Hb11 Hb12").
             iIntros (CIDe Hse mfin) "%Hcsr Hcg Hpc".
             destruct Hcsr as [Hcsf Hrv].
             iDestruct (cpu_own_transport CID CIDe 0%nat eb pj b ltac:(rewrite Hb; wp_next_chain)
                          with "Hcnt") as "Hcnt".
             iSpecialize ("Hcont" $! CIDe with "[]"); [iPureIntro; wp_next_chain|].
             assert (HVid : upd_upt V (pv_upt V) = V) by apply fw_upd_upt_id.
             iApply ("Hcont" $! mfin (mword_of_int (-1)) (pv_upt V)
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
             { by iApply (fw_env_out_dev fn Cf Htyd). }
        * (* ---- +0x2a c.li a4,2 ; +0x2c bne a5,a4 -> +0x10a (panic) ---- *)
          iApply (wp_beq_fall_s_sconf (mword_of_int (FW + 0x2e))
                    (mword_of_int 54 : mword 13) Ra4 Ra5 G6 (K - 12)%nat b
                    ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                    ltac:(rewrite Hcmp3; first [exact Hp3 | reflexivity])
                    with "Hcg Hpc []").
          { iApply (fwri_02e with "Htext"). }
          iIntros (CID11 Hs11) "Hcg Hpc".
          assert (Hpp32 : add_vec_int (mword_of_int (FW + 0x2e) : mword 64) 4
                          = mword_of_int (FW + 0x32)) by (apply bv_eq; vm_compute; reflexivity).
          iEval (rewrite Hpp32) in "Hpc".
          iApply (wp_cli_s_sconf (mword_of_int (FW + 0x32)) Ra4
                    (mword_of_int 2 : mword 6) (mword_of_int 2 : mword 64)
                    G6 (K - 12)%nat b
                    ltac:(vm_compute; discriminate) ltac:(rdok) fr_li2
                    with "Hcg Hpc []").
          { iApply (fwri_032 with "Htext"). }
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
          assert (Hpp34 : add_vec_int (mword_of_int (FW + 0x32) : mword 64) 2
                          = mword_of_int (FW + 0x34)) by (apply bv_eq; vm_compute; reflexivity).
          iEval (rewrite Hpp34) in "Hpc".
          destruct (eq_vec (fc_type Cf) (mword_of_int 2 : mword 32)) eqn:Hp2.
          -- (* ======================= FD_INODE =======================
                s4 (the running [i]) is spilled at +0x30 and the [n <= 0]
                test at +0x32 is HOISTED above the other five spills, so the
                zero-trip path never writes slots 3/5/9/10/11 -- Parts'
                header fact 3, and the reason [fw_tail] takes them as
                arbitrary words. *)
             assert (Htyi : fc_type Cf = FD_INODE)
               by (apply eq_vec_true_iff; exact Hp2).
             (* the BNE FALLS exactly when the two are equal *)
             iApply (wp_bne_fall_s_sconf (mword_of_int (FW + 0x34))
                       (mword_of_int 206 : mword 13) Ra4 Ra5 G7 (K - 12)%nat b
                       ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                       ltac:(rewrite Hncmp2; unfold neq_vec;
                             first [rewrite Hp2 | idtac]; reflexivity)
                       with "Hcg Hpc []").
             { iApply (fwri_034 with "Htext"). }
             { iIntros (CID13 Hs13) "Hcg Hpc".
               (* 31f115a: the [sd s4,48(sp)] that used to sit HERE moved
                  below the zero-trip test, into the six-spill run. *)
               assert (Hpp38 : add_vec_int (mword_of_int (FW + 0x34) : mword 64) 4
                               = mword_of_int (FW + 0x38))
                 by (apply bv_eq; vm_compute; reflexivity).
               iEval (rewrite Hpp38) in "Hpc".
               (* ---- +0x38 bge x0,a2 : the zero-trip test, now BEFORE
                      every one of the six late spills ---- *)
               assert (HG7a2 : rget G7 Ra2 = (mword_of_int n : mword 64)).
               { rewrite (rget_ne G7 Ra2 ltac:(vm_compute; discriminate)).
                 rewrite /G7 upd_ne; [| vm_compute; discriminate].
                 rewrite /G6 upd_ne; [| vm_compute; discriminate].
                 rewrite /G5 upd_ne; [| vm_compute; discriminate].
                 rewrite /G4 upd_ne; [| vm_compute; discriminate].
                 rewrite /G3g upd_ne; [| vm_compute; discriminate].
                 rewrite /G2 upd_ne; [| vm_compute; discriminate].
                 rewrite /G1 upd_ne; [exact HMa2 | vm_compute; discriminate]. }
               assert (Hbge0 : zopz0zKzJ_s (zero_reg : mword 64) (rget G7 Ra2)
                               = Z.geb 0 n)
                 by (rewrite HG7a2; exact (fw_bge0_moi n Hn01)).
               destruct (Z.geb 0 n) eqn:Hz0.
               - (* ---- n <= 0, so n = 0: the loop is never entered ---- *)
                 assert (Hnz0 : n = 0)
                   by (apply (fw_zero_trip n Hn0); apply Z.geb_le; exact Hz0).
                 (* ---- +0x38 bge x0,a2 TAKEN -> +0x126, THE ZERO TRIP ----
                    31f115a moved the six late spills BELOW this test, so on
                    this path they never happen: s1/s3/s4/s7/s8/s9 still hold
                    the caller's values and their slots are untouched.  The
                    arm is [c.mv a0,a2 ; c.j] straight into the epilogue and
                    does NOT go through [fw_tail] at all -- which is why it
                    is now a dozen lines rather than a join. *)
                 assert (Htgt126 : add_vec (mword_of_int (FW + 0x38) : mword 64)
                           (sign_extend' 64 (mword_of_int 238 : mword 13))
                           = mword_of_int (FW + 0x126))
                   by (apply bv_eq; vm_compute; reflexivity).
                 iApply (wp_bge_x0_taken_s_sconf (mword_of_int (FW + 0x38))
                           (mword_of_int 238 : mword 13) Ra2 G7 (K - 12)%nat b
                           ltac:(vm_compute; discriminate)
                           ltac:(first [exact Hbge0 | rewrite Hbge0; exact Hz0])
                           ltac:(rewrite Htgt126; vm_compute; reflexivity)
                           with "Hcg Hpc []").
                 { iApply (fwri_038 with "Htext"). }
                 iApply bi.later_intro. iIntros (CID15 Hs15) "Hcg Hpc".
                 iEval (rewrite Htgt126) in "Hpc".
                 (* ---- +0x126 c.mv a0,a2 : the answer is [n] itself ---- *)
                 iApply (wp_cmv_s_sconf (mword_of_int (FW + 0x126)) Ra0 Ra2
                           G7 (K - 12)%nat b
                           ltac:(vm_compute; discriminate) ltac:(rdok)
                           with "Hcg Hpc []").
                 { iApply (fwri_126 with "Htext"). }
                 iIntros (CID16 Hs16) "Hcg Hpc". iEval (rgne) in "Hcg".
                 set (Z1 := <[Regidx Ra0 := regval_into_reg
                               (add_vec zero_reg (G7 !!! Regidx Ra2))]> G7).
                 assert (HZ1a0 : Z1 !!! Regidx Ra0 = (mword_of_int n : mword 64)).
                 { rewrite /Z1 upd_eq. unfold regval_into_reg.
                   rewrite add_vec_zero_l. exact HG7a2. }
                 assert (HZ1sp : Z1 !!! Regidx csp_rs1 = pa_stk sp0 12)
                   by (rewrite /Z1 upd_ne; [exact HG7sp | vm_compute; discriminate]).
                 assert (HZ1thr : forall r : mword 5, is_cs_idx r = true ->
                           r <> csp_rs1 -> r <> Rs0 -> r <> Rs2 -> r <> Rs5 ->
                           r <> Rs6 -> Z1 !!! Regidx r = m !!! Regidx r).
                 { intros r Hr Nsp N0 N2 N5 N6.
                   rewrite /Z1 upd_ne; [| regne].
                   exact (HG7thr r Hr Nsp N0 N2 N5 N6). }
                 assert (Hpp128 : add_vec_int (mword_of_int (FW + 0x126) : mword 64) 2
                                  = mword_of_int (FW + 0x128))
                   by (apply bv_eq; vm_compute; reflexivity).
                 iEval (rewrite Hpp128) in "Hpc".
                 (* ---- +0x128 c.j -> +0xf4, the epilogue ---- *)
                 assert (Htgtf4 : add_vec (mword_of_int (FW + 0x128) : mword 64)
                           (sign_extend' 64 (sign_extend' 21
                              (concat_vec (mword_of_int 2022 : mword 11) ('b"0"))))
                           = mword_of_int (FW + 0xf4))
                   by (apply bv_eq; vm_compute; reflexivity).
                 iApply (wp_cj_s_sconf (mword_of_int (FW + 0x128))
                           (sign_extend' 21 (concat_vec (mword_of_int 2022 : mword 11) ('b"0")))
                           Z1 (K - 12)%nat b
                           ltac:(rewrite Htgtf4; vm_compute; reflexivity)
                           with "Hcg Hpc []").
                 { iApply (fwri_128 with "Htext"). }
                 iIntros (CID17 Hs17). iApply bi.later_intro. iIntros "Hcg Hpc".
                 iEval (rewrite Htgtf4) in "Hpc".
                 iApply (fw_epi (CID0 := CID17) m Z1 K sp0 (m !!! Regidx Rra)
                           (m !!! Regidx Rs0) (m !!! Regidx Rs2)
                           (m !!! Regidx Rs5) (m !!! Regidx Rs6)
                           (mword_of_int n) w3 w5 w6 w9 w10 w11 w12 pj b
                           (fw_K12 K HK) Hspm eq_refl eq_refl eq_refl eq_refl
                           eq_refl HZ1sp HZ1a0 HZ1thr
                           with "Hcg Htext Hpc Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hb7 Hb8 Hb9
                                 Hb10 Hb11 Hb12").
                 iIntros (CIDe Hse mfin) "%Hcsr Hcg Hpc".
                 destruct Hcsr as [Hcsf Hrv].
                 iDestruct (cpu_own_transport CID CIDe 0%nat eb pj b
                              ltac:(rewrite Hb; wp_next_chain) with "Hcnt") as "Hcnt".
                 iSpecialize ("Hcont" $! CIDe with "[]"); [iPureIntro; wp_next_chain|].
                 assert (HVid : upd_upt V (pv_upt V) = V) by apply fw_upd_upt_id.
                 iApply ("Hcont" $! mfin (mword_of_int n) (pv_upt V)
                           with "[%] [%] [%] [%] Hcg Hcnt [Hpc]
                                 [Hrtok Hcty Hcrd Hcwr Hcpp Hcip Hcmaj Hrpay Hrlv]
                                 [Hpriv] [Henv]").
                 { exact Hcsf. }
                 { apply uptd_ext_refl. }
                 { apply filewrite_ret_all. exact Hn0. }
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
                 iApply (wp_bge_x0_fall_s_sconf (mword_of_int (FW + 0x38))
                           (mword_of_int 238 : mword 13) Ra2 G7 (K - 12)%nat b
                           ltac:(vm_compute; discriminate)
                           ltac:(first [exact Hbge0 | rewrite Hbge0; exact Hz0])
                           with "Hcg Hpc []").
                 { iApply (fwri_038 with "Htext"). }
                 iIntros (CID15 Hs15) "Hcg Hpc".
                 assert (Hpp3c : add_vec_int (mword_of_int (FW + 0x38) : mword 64) 4
                                 = mword_of_int (FW + 0x3c))
                   by (apply bv_eq; vm_compute; reflexivity).
                 iEval (rewrite Hpp3c) in "Hpc".
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
                 iApply (wp_csdsp_s_sconf (mword_of_int (FW + 0x3c))
                           (mword_of_int 9 : mword 6) Rs1 G7 (K - 12)%nat w3 b
                           with "Hcg Hpc [] Hb3").
                 { iApply (fwri_03c with "Htext"). }
                 iIntros (CID16 Hs16) "Hcg Hpc Hb3". iEval (rgne) in "Hb3".
                 iEval (rewrite Hf3) in "Hb3".
                 iEval (rewrite (HG7thr Rs1 ltac:(vm_compute; reflexivity)
                                  ltac:(vm_compute; discriminate)
                                  ltac:(vm_compute; discriminate)
                                  ltac:(vm_compute; discriminate)
                                  ltac:(vm_compute; discriminate)
                                  ltac:(vm_compute; discriminate))) in "Hb3".
                 assert (Hpp3e : add_vec_int (mword_of_int (FW + 0x3c) : mword 64) 2
                                 = mword_of_int (FW + 0x3e))
                   by (apply bv_eq; vm_compute; reflexivity).
                 iEval (rewrite Hpp3e) in "Hpc".
                 iEval (rewrite -Hf5) in "Hb5".
                 iApply (wp_csdsp_s_sconf (mword_of_int (FW + 0x3e))
                           (mword_of_int 7 : mword 6) Rs3 G7 (K - 12)%nat w5 b
                           with "Hcg Hpc [] Hb5").
                 { iApply (fwri_03e with "Htext"). }
                 iIntros (CID17 Hs17) "Hcg Hpc Hb5". iEval (rgne) in "Hb5".
                 iEval (rewrite Hf5) in "Hb5".
                 iEval (rewrite (HG7thr Rs3 ltac:(vm_compute; reflexivity)
                                  ltac:(vm_compute; discriminate)
                                  ltac:(vm_compute; discriminate)
                                  ltac:(vm_compute; discriminate)
                                  ltac:(vm_compute; discriminate)
                                  ltac:(vm_compute; discriminate))) in "Hb5".
                 assert (Hpp40 : add_vec_int (mword_of_int (FW + 0x3e) : mword 64) 2
                                 = mword_of_int (FW + 0x40))
                   by (apply bv_eq; vm_compute; reflexivity).
                 iEval (rewrite Hpp40) in "Hpc".
                 (* ---- +0x40 c.sdsp s4,48(sp) : the running [i]'s slot ---- *)
                 assert (Hf6 : add_vec (G7 !!! Regidx csp_rs1)
                                 (zero_extend' 64 (concat_vec (mword_of_int 6 : mword 6) ('b"000")))
                               = pa_stk sp0 6) by (rewrite HG7sp; apply fw_frm6).
                 iEval (rewrite -Hf6) in "Hb6".
                 iApply (wp_csdsp_s_sconf (mword_of_int (FW + 0x40))
                           (mword_of_int 6 : mword 6) Rs4 G7 (K - 12)%nat w6 b
                           with "Hcg Hpc [] Hb6").
                 { iApply (fwri_040 with "Htext"). }
                 iIntros (CID16b Hs16b) "Hcg Hpc Hb6". iEval (rgne) in "Hb6".
                 iEval (rewrite Hf6) in "Hb6".
                 iEval (rewrite (HG7thr Rs4 ltac:(vm_compute; reflexivity)
                                  ltac:(vm_compute; discriminate)
                                  ltac:(vm_compute; discriminate)
                                  ltac:(vm_compute; discriminate)
                                  ltac:(vm_compute; discriminate)
                                  ltac:(vm_compute; discriminate))) in "Hb6".
                 assert (Hpp42 : add_vec_int (mword_of_int (FW + 0x40) : mword 64) 2
                                 = mword_of_int (FW + 0x42))
                   by (apply bv_eq; vm_compute; reflexivity).
                 iEval (rewrite Hpp42) in "Hpc".
                 iEval (rewrite -Hf9) in "Hb9".
                 iApply (wp_csdsp_s_sconf (mword_of_int (FW + 0x42))
                           (mword_of_int 3 : mword 6) Rs7 G7 (K - 12)%nat w9 b
                           with "Hcg Hpc [] Hb9").
                 { iApply (fwri_042 with "Htext"). }
                 iIntros (CID18 Hs18) "Hcg Hpc Hb9". iEval (rgne) in "Hb9".
                 iEval (rewrite Hf9) in "Hb9".
                 iEval (rewrite (HG7thr Rs7 ltac:(vm_compute; reflexivity)
                                  ltac:(vm_compute; discriminate)
                                  ltac:(vm_compute; discriminate)
                                  ltac:(vm_compute; discriminate)
                                  ltac:(vm_compute; discriminate)
                                  ltac:(vm_compute; discriminate))) in "Hb9".
                 assert (Hpp44 : add_vec_int (mword_of_int (FW + 0x42) : mword 64) 2
                                 = mword_of_int (FW + 0x44))
                   by (apply bv_eq; vm_compute; reflexivity).
                 iEval (rewrite Hpp44) in "Hpc".
                 iEval (rewrite -Hf10) in "Hb10".
                 iApply (wp_csdsp_s_sconf (mword_of_int (FW + 0x44))
                           (mword_of_int 2 : mword 6) Rs8 G7 (K - 12)%nat w10 b
                           with "Hcg Hpc [] Hb10").
                 { iApply (fwri_044 with "Htext"). }
                 iIntros (CID19 Hs19) "Hcg Hpc Hb10". iEval (rgne) in "Hb10".
                 iEval (rewrite Hf10) in "Hb10".
                 iEval (rewrite (HG7thr Rs8 ltac:(vm_compute; reflexivity)
                                  ltac:(vm_compute; discriminate)
                                  ltac:(vm_compute; discriminate)
                                  ltac:(vm_compute; discriminate)
                                  ltac:(vm_compute; discriminate)
                                  ltac:(vm_compute; discriminate))) in "Hb10".
                 assert (Hpp46 : add_vec_int (mword_of_int (FW + 0x44) : mword 64) 2
                                 = mword_of_int (FW + 0x46))
                   by (apply bv_eq; vm_compute; reflexivity).
                 iEval (rewrite Hpp46) in "Hpc".
                 iEval (rewrite -Hf11) in "Hb11".
                 iApply (wp_csdsp_s_sconf (mword_of_int (FW + 0x46))
                           (mword_of_int 1 : mword 6) Rs9 G7 (K - 12)%nat w11 b
                           with "Hcg Hpc [] Hb11").
                 { iApply (fwri_046 with "Htext"). }
                 iIntros (CID20 Hs20) "Hcg Hpc Hb11". iEval (rgne) in "Hb11".
                 iEval (rewrite Hf11) in "Hb11".
                 iEval (rewrite (HG7thr Rs9 ltac:(vm_compute; reflexivity)
                                  ltac:(vm_compute; discriminate)
                                  ltac:(vm_compute; discriminate)
                                  ltac:(vm_compute; discriminate)
                                  ltac:(vm_compute; discriminate)
                                  ltac:(vm_compute; discriminate))) in "Hb11".
                 assert (Hpp48 : add_vec_int (mword_of_int (FW + 0x46) : mword 64) 2
                                 = mword_of_int (FW + 0x48))
                   by (apply bv_eq; vm_compute; reflexivity).
                 iEval (rewrite Hpp48) in "Hpc".
                 (* ---- +0x40 c.li s4,0 : [i := 0] ---- *)
                 iApply (wp_cli_s_sconf (mword_of_int (FW + 0x48)) Rs4
                           (mword_of_int 0 : mword 6) (mword_of_int 0 : mword 64)
                           G7 (K - 12)%nat b
                           ltac:(vm_compute; discriminate) ltac:(rdok) fw_li0
                           with "Hcg Hpc []").
                 { iApply (fwri_048 with "Htext"). }
                 iIntros (CID21 Hs21) "Hcg Hpc".
                 set (L1 := <[Regidx Rs4 := regval_into_reg
                               (mword_of_int 0 : mword 64)]> G7).
                 assert (Hpp4a : add_vec_int (mword_of_int (FW + 0x48) : mword 64) 2
                                 = mword_of_int (FW + 0x4a))
                   by (apply bv_eq; vm_compute; reflexivity).
                 iEval (rewrite Hpp4a) in "Hpc".
                 (* ---- +0x42 c.lui s7,0x1 ; +0x44 addi s7,s7,-1024 : 3072 ---- *)
                 iApply (wp_clui_s_sconf (mword_of_int (FW + 0x4a)) Rs7
                           (sign_extend' 20 (mword_of_int 1 : mword 6))
                           (mword_of_int 4096 : mword 64) L1 (K - 12)%nat b
                           ltac:(vm_compute; discriminate) ltac:(rdok) fw_lui1
                           with "Hcg Hpc []").
                 { iApply (fwri_04a with "Htext"). }
                 iIntros (CID22 Hs22) "Hcg Hpc".
                 set (L2 := <[Regidx Rs7 := regval_into_reg
                               (mword_of_int 4096 : mword 64)]> L1).
                 assert (Hpp4c : add_vec_int (mword_of_int (FW + 0x4a) : mword 64) 2
                                 = mword_of_int (FW + 0x4c))
                   by (apply bv_eq; vm_compute; reflexivity).
                 iEval (rewrite Hpp4c) in "Hpc".
                 iApply (wp_addi4_s_sconf (mword_of_int (FW + 0x4c)) Rs7 Rs7
                           (mword_of_int 3072 : mword 12) L2 (K - 12)%nat b
                           ltac:(vm_compute; discriminate) ltac:(rdok)
                           with "Hcg Hpc []").
                 { iApply (fwri_04c with "Htext"). }
                 iIntros (CID23 Hs23) "Hcg Hpc". iEval (rgne) in "Hcg".
                 set (L3 := <[Regidx Rs7 := regval_into_reg
                               (add_vec (L2 !!! Regidx Rs7)
                                  (sign_extend' 64 (mword_of_int 3072 : mword 12)))]> L2).
                 assert (HL3s7 : L3 !!! Regidx Rs7
                                 = (mword_of_int SpecFilewrite.FW_MAX : mword 64)).
                 { rewrite /L3 upd_eq. unfold regval_into_reg.
                   rewrite /L2 upd_eq. exact fw_addi_m1024. }
                 assert (Hpp50 : add_vec_int (mword_of_int (FW + 0x4c) : mword 64) 4
                                 = mword_of_int (FW + 0x50))
                   by (apply bv_eq; vm_compute; reflexivity).
                 iEval (rewrite Hpp50) in "Hpc".
                 (* ---- +0x48 c.lui a5,0x1 ; +0x4a addiw a5,a5,-1024 : again ---- *)
                 iApply (wp_clui_s_sconf (mword_of_int (FW + 0x50)) Ra5
                           (sign_extend' 20 (mword_of_int 1 : mword 6))
                           (mword_of_int 4096 : mword 64) L3 (K - 12)%nat b
                           ltac:(vm_compute; discriminate) ltac:(rdok) fw_lui1
                           with "Hcg Hpc []").
                 { iApply (fwri_050 with "Htext"). }
                 iIntros (CID24 Hs24) "Hcg Hpc".
                 set (L4 := <[Regidx Ra5 := regval_into_reg
                               (mword_of_int 4096 : mword 64)]> L3).
                 assert (Hpp52 : add_vec_int (mword_of_int (FW + 0x50) : mword 64) 2
                                 = mword_of_int (FW + 0x52))
                   by (apply bv_eq; vm_compute; reflexivity).
                 iEval (rewrite Hpp52) in "Hpc".
                 iApply (wp_addiw_s_sconf (mword_of_int (FW + 0x52)) Ra5 Ra5
                           (mword_of_int 3072 : mword 12) L4 (K - 12)%nat b
                           ltac:(vm_compute; discriminate) ltac:(rdok)
                           with "Hcg Hpc []").
                 { iApply (fwri_052 with "Htext"). }
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
                 assert (Hpp56 : add_vec_int (mword_of_int (FW + 0x52) : mword 64) 4
                                 = mword_of_int (FW + 0x56))
                   by (apply bv_eq; vm_compute; reflexivity).
                 iEval (rewrite Hpp56) in "Hpc".
                 (* ---- +0x4e c.mv s9,a5 ; +0x50 c.li s8,1 ---- *)
                 iApply (wp_cmv_s_sconf (mword_of_int (FW + 0x56)) Rs9 Ra5
                           L5 (K - 12)%nat b
                           ltac:(vm_compute; discriminate) ltac:(rdok)
                           with "Hcg Hpc []").
                 { iApply (fwri_056 with "Htext"). }
                 iIntros (CID26 Hs26) "Hcg Hpc". iEval (rgne) in "Hcg".
                 set (L6 := <[Regidx Rs9 := regval_into_reg
                               (add_vec zero_reg (L5 !!! Regidx Ra5))]> L5).
                 assert (HL6s9 : L6 !!! Regidx Rs9
                                 = (mword_of_int SpecFilewrite.FW_MAX : mword 64)).
                 { rewrite /L6 upd_eq. unfold regval_into_reg.
                   rewrite add_vec_zero_l. exact HL5a5. }
                 assert (Hpp58 : add_vec_int (mword_of_int (FW + 0x56) : mword 64) 2
                                 = mword_of_int (FW + 0x58))
                   by (apply bv_eq; vm_compute; reflexivity).
                 iEval (rewrite Hpp58) in "Hpc".
                 iApply (wp_cli_s_sconf (mword_of_int (FW + 0x58)) Rs8
                           (mword_of_int 1 : mword 6) (mword_of_int 1 : mword 64)
                           L6 (K - 12)%nat b
                           ltac:(vm_compute; discriminate) ltac:(rdok) fr_li1
                           with "Hcg Hpc []").
                 { iApply (fwri_058 with "Htext"). }
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
                 assert (Hpp5a : add_vec_int (mword_of_int (FW + 0x58) : mword 64) 2
                                 = mword_of_int (FW + 0x5a))
                   by (apply bv_eq; vm_compute; reflexivity).
                 iEval (rewrite Hpp5a) in "Hpc".
                 (* ---- +0x52 c.j -> +0xcc : the loop is BOTTOM-TESTED ---- *)
                 assert (Htgtcc : add_vec (mword_of_int (FW + 0x5a) : mword 64)
                           (sign_extend' 64 (sign_extend' 21
                              (concat_vec (mword_of_int 61 : mword 11) ('b"0"))))
                           = mword_of_int (FW + 0xd4))
                   by (apply bv_eq; vm_compute; reflexivity).
                 iApply (wp_cj_s_sconf (mword_of_int (FW + 0x5a))
                           (sign_extend' 21 (concat_vec (mword_of_int 61 : mword 11) ('b"0")))
                           L7 (K - 12)%nat b
                           ltac:(rewrite Htgtcc; vm_compute; reflexivity)
                           with "Hcg Hpc []").
                 { iApply (fwri_05a with "Htext"). }
                 iIntros (CID28 Hs28). iApply bi.later_intro. iIntros "Hcg Hpc".
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
                 iPoseProof (fw_env_fs _ _ _ Htyi with "Henv") as "Henv".
                 iEval (rewrite /filewrite_fs_env) in "Henv".
                 (* 25 conjuncts, not 31: the six per-inode fields (the two
                    slot facts, the two point geometry facts, the share and
                    its [ity_shot] with the [fc_wbool] side condition) are
                    gone, replaced by the two QUANTIFIED geometry facts and
                    the two FAMILIES -- fs-sysfile S4c. *)
                 (* R-open-1b deleted the off-borrow FAMILY from this
                    environment (the cinv is minted per publication, so no
                    fixed persistent family can exist); the names below keep
                    their meanings and the seventh slot is simply gone. *)
                 iDestruct "Henv" as "(%E1 & %E2 & %E3 & %E4 & %E5 & %E6 & #E8 & #E9 & #E10 & #E11 & #E12 & #E13 & #E14 & #E15 & #E16 & #E17 & E18 & E19 & E20 & #E21 & #E22 & #E23 & #E24 & E25)".
                 (* the loop still takes the ONE slot's off-borrow invariant;
                    the environment now carries the family, so it is selected
                    here rather than by the caller. *)
                 assert (HVid : upd_upt V (pv_upt V) = V) by apply fw_upd_upt_id.
                 (* [cpu_own] IS HART-INDEXED and the loop lemma states it at
                    ITS OWN [CID0]; the walk still holds the ENTRY hart's copy.
                    One transport, exactly as the -1 exit does before [Hcont]. *)
                 iDestruct (cpu_own_transport CID CID28 0%nat eb pj b
                              ltac:(rewrite Hb; wp_next_chain) with "Hcnt") as "Hcnt".
                 iApply (fw_loop (CID0 := CID28) γa γf γs j γlp k q Cf fn pidv V
                           m K eb n b sp0 w12 pj lks
                           HK Hk Hj Hgs Hlens Hfnj Hfnps Hn01 Heb Htyi Hwb Hspm
                           ltac:(reflexivity)
                           E1 E2 E3 E4 E5 E6 Hclog
                           (Z.to_nat n) 0%Z (pv_upt V) L7
                           ltac:(rewrite (Z2Nat.id n Hn0); lia)
                           ltac:(lia)
                           ltac:(apply uptd_ext_refl)
                           HL7sp HL7s2 HL7s4 HL7s5 HL7s6 HL7s7 HL7s8 HL7s9
                           ltac:(intros r Hr A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11;
                                 exact (HL7thr r Hr A1 A2 A4 A6 A7 A8 A9 A10 A11))
                           Hbelow
                           with "Hcg Hcnt Htext Hpc Hprocs
                                 Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hb7 Hb8 Hb9 Hb10 Hb11 Hb12
                                 [Hrtok Hcty Hcrd Hcwr Hcpp Hcip Hcmaj Hrpay Hrlv]
                                 [Hpriv] Hkenv
                                 E8 E9 E10 E11 E12 E13 E14 E15 E16 E17
                                 E22 E23 E24 E21 [E18 E19 E20 E25]").
                 { rewrite /file_ref /file_fields.
                   iFrame "Hrtok Hcty Hcrd Hcwr Hcpp Hcip Hcmaj Hrpay Hrlv". }
                 { rewrite HVid. iExact "Hpriv". }
                 { rewrite /filewrite_fs_out.
                   iFrame "E18 E19 E20 E25". }
                 iIntros (CIDx Hsx mf rv P')
                   "%Hcs %Hup %Hret %Hra Hcg Hcnt Hpc Href Hpriv Henvo".
                 iSpecialize ("Hcont" $! CIDx with "[]"); [iPureIntro; wp_next_chain|].
                 iApply ("Hcont" $! mf rv P'
                           with "[%] [%] [%] [%] Hcg Hcnt Hpc Href Hpriv Henvo").
                 { exact Hcs. }
                 { exact Hup. }
                 { exact Hret. }
                 { exact Hra. } }
          -- (* ==================== THE ELSE ARM ======================
                Neither pipe, nor device, nor inode: [panic("filewrite")]
                at +0x11e, and [fw_panic] is the whole block from +0x10a. *)
             assert (Htgt10a : add_vec (mword_of_int (FW + 0x34) : mword 64)
                       (sign_extend' 64 (mword_of_int 206 : mword 13))
                       = mword_of_int (FW + 0x102))
               by (apply bv_eq; vm_compute; reflexivity).
             iApply (wp_bne_taken_s_sconf (mword_of_int (FW + 0x34))
                       (mword_of_int 206 : mword 13) Ra4 Ra5 G7 (K - 12)%nat b
                       ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                       ltac:(rewrite Hncmp2; unfold neq_vec;
                             first [rewrite Hp2 | idtac]; reflexivity)
                       ltac:(rewrite Htgt10a; vm_compute; reflexivity)
                       with "Hcg Hpc []").
             { iApply (fwri_034 with "Htext"). }
             iApply bi.later_intro. iIntros (CID13 Hs13) "Hcg Hpc".
             iEval (rewrite Htgt10a) in "Hpc".
             (* [cpu_own] IS HART-INDEXED: the block states it at its own
                [CID0], and the walk still holds the ENTRY hart's copy. *)
             iDestruct (cpu_own_transport CID CID13 0%nat eb pj b
                          ltac:(rewrite Hb; wp_next_chain) with "Hcnt") as "Hcnt".
             iApply (fw_panic (fun (h : CpuId) => PN.wp_panic_sconf KT1 (CID := h)) (CID0 := CID13) G7 (K - 12)%nat sp0
                       w3 w5 w6 w9 w10 w11 pj eb b lks HG7sp
                       (fw_panic_K K HK) Hbelow
                       with "Hcg Hcnt Htext Hkd Hpc Hpenv Hb3 Hb5 Hb6 Hb9 Hb10 Hb11").
  Qed.

End ProofFilewrite.
End FilewriteProof.
