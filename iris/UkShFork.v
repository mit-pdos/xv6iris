(* ===================================================================== *)
(* UkShFork.v -- sh's FORK ARM: the four instructions of main's body that  *)
(* start a command, and the payload that crosses the fork with it.        *)
(*                                                                        *)
(*   0x908  jal  ra,fork1                                                 *)
(*   0x90c  c.beqz a0,0x99c        the CHILD -- parse and exec            *)
(*   0x90e  c.li a0,0                                                     *)
(*   0x910  jal  ra,wait           the PARENT -- reap, and round again    *)
(*          ...falls into 0x914, the loop head                            *)
(*                                                                        *)
(* FOUR INSTRUCTIONS AND TWO PROCESSES.  [UkShDiag.wp_kshr_fork1_final]    *)
(* already carries fork1's own [-1 -> panic -> exit] arm, so what is left  *)
(* is a pair of continuations: the parent's, which reaps and goes back to  *)
(* the command loop, and the child's, which is                            *)
(* [UkShMain.wp_kshm_child_alloc] -- the parse, the runner, and [exec].    *)
(*                                                                        *)
(* WHAT CROSSES, AND WHY IT IS SHAPED THIS WAY.  [Forkable P] hands the    *)
(* PARENT [P] back and mints the CHILD's copy at FRESH ghost names, which  *)
(* is exactly the address-space copy fork performs.  So the payload is     *)
(* everything the child's walk reads out of memory:                        *)
(*                                                                        *)
(*   the text and its jump table  (persistent, and the same proposition    *)
(*                                 as the parser's [shp_code]/[shp_rodata])*)
(*   the two static lexer tables at 0x2000 / 0x2008                        *)
(*   the allocator's untouched first-call state ([freep] = 0, [base])      *)
(*   the whole line buffer                                                 *)
(*                                                                        *)
(* THE BREAK IS NOT IN IT.  [usz] is a ghost var, not bytes, so it cannot  *)
(* be [Forkable]; [wp_kshr_fork1_final] hands [usz gs szv] to the child     *)
(* itself.  The child assembles [UkShMalloc.ushm_fresh] out of that and    *)
(* the payload's two data cells.                                           *)
(*                                                                        *)
(* AND FIRST-CALL-ONLY MALLOC IS ENOUGH FOREVER, which is worth saying     *)
(* out loud because it looks like a gap and is not: the PARENT never calls *)
(* [malloc].  Only the forked child does, exactly once, in a fresh copy of *)
(* the address space.  So the parent carrying an untouched [ushf_dat]      *)
(* round the loop is the actual control flow and not a weakening.          *)
(*                                                                        *)
(* AND IT JOINS [UkSh.ush_rest] (SS5).  The re-cut landed: the loop head    *)
(* carries an opaque [R] and hands its walk [16 + (UkSh.ush_Dbody + n)],   *)
(* which at [R := UkShLoop.ushl_R] is exactly the tables, the allocator's  *)
(* first-call state, [usz] and the [16 + (ush_Dbody + n)] it needs.  So    *)
(* [ushf_rest_of_body] discharges [ush_rest] -- from ONE premise, and it   *)
(* is not about fork at all: the child's walk needs the line to be one the *)
(* LEXER ACCEPTS ([ushp_no_symbols], fewer than MAXARGS tokens), and the   *)
(* command loop cannot promise that about a line the user typed.  That is  *)
(* [ushf_lexable], stage 5's [ush_simple] scope -- the REDIRECT and PIPE   *)
(* arms -- and it is a premise here for the same reason [UkShCd] takes     *)
(* "this line begins cd " as one.  Everything else the loop knew already:  *)
(* where the line ends comes off its own scan, via [ushf_first_nul].       *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_map ghost_var invariants.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExtras RiscvModelBytes.
Require Import RegFile.
Require Import WpUmodeBranch.
Require Import UmodeArith UmodeAbi.
Require Import ProcGeom.     (* [PIDMAX] -- the fork answer's pid range *)
Require Import UserPerm.
From Stdlib Require Import FunctionalExtensionality.
Require Import UserHeap UkRun UkRunLeaf.
Require Import UkFork.
Require Import FdSlots UserFd.
Require Import UCodeShK UCodeShP.
Require Import FileDisc.  (* [uline] -- the line the loop read, typed *)
Require Import UkSh.
Require Import UkShParse.
Require Import UkShRun.
Require Import UkShDiag.
Require Import UkShMalloc.
Require Import UkShLoop.
Require Import UkShCd.   (* [ushc_bytes_sub] / [ushc_ustr_of_bytes]: the line cut out *)
Require Import CtxIdDefs.
Require User.ShSyms User.ShInstrs.
Require Import ChildTok.  (* [genF] -- the capacity the slot's fork arms name; [child_tok] / [exit_tok] / [gen_pay_timeless] *)
Require Import UexecRet.  (* [uwait_ans_pid] / [sext_neg1_64]: the wait's answer at sh's own pid *)
Require Import LineWords.  (* [wl_line] / [last_ws]: the line the child runs *)
Require Import EchoDisc.  (* [line_ok]: the disciplined line's first byte *)
Local Open Scope Z_scope.
Import Defs.

Require Import UexecSG.   (* [uexecSG] / [uprogSG]: the ARM deposit class *)
Require Import UserCwd.  (* [ucwd] / [ucwd_any] -- the process's own view of its working directory *)
Require Import UserChildren.  (* [uch_any] -- the process's own half of its children set *)

Require Import Xv6Cameras.   (* [uartGhostG] -- the console ring's cameras *)
(* A PID IN [1, PIDMAX] DOES NOT SIGN-EXTEND TO -1 (lane RESIDUALS, (A)):
   the fork answer's pid arm carries the range, and the shell's fork-failed
   branch (fork1's [-1] test) refutes that arm with it.  Pure, on [Z], at
   the top level so [lia] sees no machine word. *)
Lemma ushf_pid_lt_Z31 (z : Z) : 1 <= z <= PIDMAX -> z < Z31.
Proof. unfold PIDMAX, Z31. lia. Qed.

Lemma ushf_pid_Z64 (z : Z) : 1 <= z <= PIDMAX -> 0 <= z < Z64.
Proof. unfold PIDMAX, Z64. lia. Qed.

Lemma ushf_pid_ne_m1 (z : Z) : 1 <= z <= PIDMAX -> z <> 18446744073709551615.
Proof. unfold PIDMAX. lia. Qed.

Lemma ushf_pid_sext_ne_m1 (pidv : mword 32) :
  1 <= bv_unsigned pidv <= PIDMAX ->
  (sign_extend' 64 pidv : mword 64) <> (mword_of_int (-1) : mword 64).
Proof.
  intros Hrng Heq.
  rewrite (sext32_small pidv (ushf_pid_lt_Z31 _ Hrng)) in Heq.
  pose proof (f_equal uint Heq) as Hu.
  rewrite (uint_moi (bv_unsigned pidv) (ushf_pid_Z64 _ Hrng)) in Hu.
  assert (Hm1 : uint (mword_of_int (-1) : mword 64) = 18446744073709551615)
    by (vm_compute; reflexivity).
  rewrite Hm1 in Hu.
  exact (ushf_pid_ne_m1 _ Hrng Hu).
Qed.

Section UkShFork.
  Context `{!riscvGS Σ}.
  Context `{!ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  (* ...and the children set's ([Xv6Cameras.uchG]), which [UkRun.urun]
     carries beside the cwd's *)
  Context `{!ghost_varG Σ (gset gname)}.
  Context (N : uk_names Σ).
  (* THIS PROGRAM'S EXIT OWES ITS PARENT NOTHING at this lane, as a
     CLASS so that it reaches the exit ecall without an argument at every
     call site ([UkRun.ukn_const]). *)
  Context `{Hpay : !ukn_const N}.
  (* [Xv6Cameras.uartGhostG] and the POSITION's ghost name, which
     [UkSh.ush_pstate] carries as its fourth conjunct (app-echo.md,
     "SH-LINE RULING"): this walk never reads the number, but the resource
     travels through every lemma that carries the process state. *)
  Context `{!uartGhostG Σ}.
  Context (γp : gname).
  (* ...AND THE APPLICATION'S TAINT, which the line fact's second arm is
     (lane SH-LINE 2b, L3).  A PARAMETER, for [UkSh.v]'s reason: the
     program tier names no application.  Persistent, which is what lets
     the arm be read without threading a resource. *)
  Context (T : iProp Σ).
  Context `{HT : !Persistent T}.
  (* ...and the era's write credential the loop carries beside its cursor
     (lane IO-LEAF, M6a(3)), opaque here for the same reason *)
  Context (Wc : list (bv 8) -> nat -> iProp Σ).
  (* ...the banner-owed credential and the lease's pieces beside it (step
     3), opaque here for the same reason *)
  Context (Wb : list (bv 8) -> iProp Σ).
  Context (Pm : list (bv 8) -> iProp Σ).
  (* the fields, under the names the engine has always used *)
  Local Notation γt := (ukn_t N).
  Local Notation γd := (ukn_d N).
  Local Notation γs := (ukn_s N).
  Local Notation γfd := (ukn_fd N).
  Local Notation γcwd := (ukn_cwd N).
  Local Notation γch := (ukn_ch N).
  (* [ChildTok.ctokG]: the slot's fork arms name the generation's pieces,
     and this file binds no whole-system bundle. *)
  Context `{!ctokG Σ}.
  Context {SG : uexecSG Σ}.
  Context `{PS : uprogSG Σ}.
  (* THE NUMBERS THIS PROGRAM ADMITS ([UexecSG.uprogSG]'s [psok]).  A SECTION
     hypothesis, so no lemma statement in this file names it and the ~570
     [urun] sites did not move; the program's kernel-side constructor
     discharges it.
     AT THE FREE NUMBERS AND NO MORE (lane SUPPLY-SPLIT).  It used to read
     "every number but exec", which at the generic instance is true and at
     a VERIFIED program's instance is not: a program whose supplier is the
     application's ([AppInv.app_sup] -- for the echo application, the
     TAINT) could only ever be entered tainted.  What a verified program
     admits is [UexecSG.free_num] -- every number whose bundle is [emp],
     plus chdir, whose branch is a closed fact -- and at
     [UexecExecInst.uprogSG_free] this hypothesis is the identity.  A call
     at a number OUTSIDE that set takes its own deposit as a premise
     ([UkRun.udepw_law]) and is named at its site. *)
  Hypothesis Hpsok_free : forall k : Z, free_num k -> psok k.

  Local Notation ra_idx := (mword_of_int 1 : mword 5).
  Local Notation s1_idx := (mword_of_int 9 : mword 5).
  Local Notation a5_idx := (mword_of_int 15 : mword 5).
  Local Notation a0_idx := (mword_of_int 10 : mword 5).
  Local Notation a7_idx := (mword_of_int 17 : mword 5).
  Local Notation s2_idx := (mword_of_int 18 : mword 5).
  Local Notation s3_idx := (mword_of_int 19 : mword 5).
  Local Notation s4_idx := (mword_of_int 20 : mword 5).
  Local Notation s5_idx := (mword_of_int 21 : mword 5).
  Local Notation s6_idx := (mword_of_int 22 : mword 5).

  Local Notation ush_std := (UkSh.ush_std N T).
  Local Notation ush_pstate := (UkSh.ush_pstate N γp T Wc Wb Pm).
  Local Notation ushl_dat := (UkShLoop.ushl_dat γd).
  Local Notation ushl_head := (UkShLoop.ushl_head N γp T Wc Wb Pm).

  (* ===================================================================== *)
  (* §1 THE TWO CATALOG BRIDGES THE CHILD NEEDS.                            *)
  (*                                                                        *)
  (* The payload carries the KERNEL-lane catalog's names because that is    *)
  (* what fork1 hands over; the child's walk asks for the PARSER lane's.    *)
  (* They are the same propositions -- [shp_code] and [shk_code] are both   *)
  (* [utext_img g ShInstrs.sh_bytes], and [shp_ro] and [shk_ro] are the     *)
  (* same filter of [ShData.sh_data] -- so each bridge is one line.         *)
  (* ===================================================================== *)
  Lemma ushf_code_shp (g : gname) : shk_code g -∗ shp_code g.
  Proof using . rewrite /shk_code /shp_code. iIntros "#H". iExact "H". Qed.

  Lemma ushf_rodata_shp (g : gname) : shk_rodata g -∗ shp_rodata g.
  Proof using .
    rewrite /shk_rodata /shp_rodata /shk_ro /shp_ro.
    iIntros "#H". iExact "H".
  Qed.

  (* ===================================================================== *)
  (* §2 THE PAYLOAD.                                                        *)
  (*                                                                        *)
  (* Everything the child's walk reads out of memory: the text and its jump *)
  (* table, and the DATA half a turn of the loop carries                    *)
  (* ([UkShLoop.ushl_dat] -- the two lexer tables and the allocator's       *)
  (* first-call state) plus the line buffer itself.                        *)
  (* ===================================================================== *)
  Definition ushf_pay (f : nat -> bv 8)
      : gname -> gname -> gname -> iProp Σ :=
    fun gt gd _ =>
      (shk_code gt ∗ shk_rodata gt ∗ ush_jtab gt ∗
       UkShLoop.ushl_dat gd ∗ ubytes gd sh_buf sh_nbuf f)%I.

  Global Instance forkable_ushf_pay (f : nat -> bv 8) :
    Forkable (ushf_pay f).
  Proof using .
    rewrite /ushf_pay /UkShLoop.ushl_dat.
    apply forkable_sep; [ apply forkable_shk_code | ].
    apply forkable_sep; [ apply forkable_shk_rodata | ].
    apply forkable_sep; [ apply forkable_ush_jtab | ].
    apply forkable_sep; [ | apply forkable_ubytes ].
    apply forkable_sep; [ apply forkable_ustr_disc | ].
    apply forkable_sep; [ apply forkable_ustr_disc | ].
    apply forkable_sep; [ apply forkable_uword | ].
    apply forkable_exist. intros fb. apply forkable_ubytes.
  Qed.

  (* what a nonzero pid does to the [c.beqz] at 0x90c *)
  Lemma ushf_eqv_false (x : mword 64) :
    x <> (mword_of_int 0 : mword 64) -> eq_vec x zero_reg = false.
  Proof using .
    intros H. apply (proj2 (eq_vec_false_iff x zero_reg)).
    rewrite zero_reg_moi. exact H.
  Qed.

  (* ===================================================================== *)
  (* §3 THE ARM.                                                            *)
  (* ===================================================================== *)

  (* THE PROCESS STATE.  [UkSh.ush_pstate]'s working directory is the ROOT
     (step 4; SH-LINE R3(2)): the disciplined shell's one line is never
     [cd], and its forked child execs /echo on a PIN, which resolves a
     path from the directory the process is in.  [ushf_pstate_at] and
     [wp_kshf_fork_any] -- the cwd-indexed state and the index-free arm --
     are gone with the index. *)
  Local Notation γpid := (ukn_pid N).
  Local Notation ush_pid := (UkSh.ush_pid N).
  Local Notation ush_bstate := (UkSh.ush_bstate N γp T Wc Wb Pm).

  (* THE CREDENTIAL FAMILY IS TIMELESS, as the era's is
     ([EchoLinksLine.ewc_lcred_timeless]): the parent redeems its child's
     payload out of an escrow that costs a later ([ChildTok.gen_pay]), and
     a timeless payload costs it nothing ([gen_pay_timeless]).  A NAMED
     instance binder, for the proofs' [H0]. *)
  Context `{HWct : forall (I : list (bv 8)) (p : nat), Timeless (Wc I p)}.

  (* ===================================================================== *)
  (* §3 THE LEND AND THE PAYLOAD (lane IO-LEAF, step 4, M3b core).          *)
  (*                                                                        *)
  (* WHAT THE PARENT LENDS ITS CHILD is the credential at the body's slot:  *)
  (* the line's block owed at the boundary after the line ([Wc np 3]),      *)
  (* which is exactly what echo's paid entry wants at its first byte        *)
  (* ([UEchoOut.echo_uexec_slot_at], through [EchoLinksLine.               *)
  (* ewc_lcred_blk_lend]).  WHAT THE CHILD HANDS BACK through its exit is   *)
  (* the credential AFTER the block -- the shell's next prompt is paid from *)
  (* it -- and nothing else: every way a child ends prints first (the       *)
  (* program, a failed exec's diagnostic, and since upstream d66e41c the    *)
  (* parse's out-of-memory panic), so no child hands the lend back          *)
  (* untouched (sync design section 2).  A KILLED child pays [ushf_wq]      *)
  (* with the taint through [ushf_kill_law] (the taint inhabits every       *)
  (* shape).  Both are opaque here for [Wc]'s reason and are discharged at  *)
  (* the top.                                                               *)
  (* ===================================================================== *)
  Definition ushf_wq (I : list (bv 8)) : iProp Σ := Wc I 0%nat.

  Global Instance ushf_wq_timeless I : Timeless (ushf_wq I).
  Proof. rewrite /ushf_wq. apply _. Qed.

  Definition ushf_kill_law : iProp Σ :=
    (□ (∀ I : list (bv 8), app_taint -∗ Wc I 0%nat))%I.

  Global Instance ushf_kill_law_persistent : Persistent ushf_kill_law.
  Proof using . rewrite /ushf_kill_law. apply _. Qed.

  (* THE CHILD'S WALK AT THE PAID PAYLOAD, as a law the body takes: from
     0x99c (the [c.beqz] at 0x90c taken, the line cut out of the child's own
     copy of the buffer, the allocator's first-call state assembled) to
     the child's exit, at a record whose payload is [ushf_wq I], holding
     the lent block credential and the ledger's three console rows.  It is
     stated over the line the discipline admitted ([UkSh.ush_line_is] at
     the word list [ws]), because that is the line the paid entry is proved
     at ([UkShEcho.wp_kshm_child_echo_at]); the discharge is E4's dispatch
     on the paid supply, one file above this one.

     [ws] IS THE LAST LINE OF THE BOUNDARY IT WAS LENT AT (project
     echo-any-line), and that equation is a PREMISE: the credential
     [Wc I 3] says which block of the transcript the child's output must
     fill, and only the line that closed [I] fills it.  The fork arm
     supplies it out of [UkSh.ush_posw]. *)
  (* THE LINE SHAPE IS A PARAMETER (lane SH-CHILD).  The law was stated at
     [UkSh.ush_line_is] -- echo's line -- and the file application's sh
     forks a child on a REDIRECT line too, which
     [UkShRedirLine.ushs_line_is_nosym] proves no [ush_line_is] line can
     be.  Everything else about the law is indifferent to which line it
     is, so the line fact is [Lp] and [ushf_child_law] is this at
     [Lp := UkSh.ush_line_is]. *)
  (* ...AND THE ROOM IT ASKS FOR IS A PARAMETER TOO (lane SH-CHILD-2):
     the redirect line's parse is eight words deeper than the symbol-free
     one, and the fork hands whatever [UkSh.ush_Dbody] leaves -- [68 + (8 +
     (ush_Dg + n))] -- so a law at [Dc <= 68] is that run at a bigger [n].
     echo's is [Dc := 60], the landed number. *)
  Definition ushf_child_law_at
      (Lp : list (list (bv 8)) -> (nat -> bv 8) -> nat -> nat -> Prop)
      (Dc : nat)
      : iProp Σ :=
    (□ (∀ (N' : uk_names Σ) (h : CpuId) (m : regfile) (dw dv : dfrac)
          (s0 : Z) (len : nat) (ws : list (list (bv 8))) (g : nat -> bv 8)
          (sz : Z) (ld : list fdstate) (n : nat) (I : list (bv 8)),
          ⌜ ukn_pay N' = (fun _ : Z => ushf_wq I) ⌝ -∗
          (* ...AND THE CHILD HOLDS NO OFFSET HALF (lane OFF-HAND-4, S2):
             the child execs /echo, whose entry is minted at
             [ukn_held = empty] and now reads the key's all-parked row off
             the exec'ing process's own run ([UkShEcho.sh_exec_sup_echo]).
             The fork arm supplies it: the child's held set is the one sh
             chose ([UkFork.wp_uk_ecall_fork]'s [hs]), and sh's own is
             empty ([UkSh.ush_gen_slot]'s row). *)
          ⌜ m !!! Regidx s1_idx = (mword_of_int s0 : mword 64) ⌝ -∗
          ⌜ Lp ws g 0%nat len ⌝ -∗
          ⌜ ws = last_ws I ⌝ -∗
          (* ...AND THE ERA'S OWN LINE AT THAT INPUT (the PROGRAM STREAM):
             the input's last body PARSES.  [ws = last_ws I] gives the
             child its words; it does not say which CONSTRUCTOR the era
             filed, and an era with more than one line shape needs that to
             open its lend ([FileDisc.fbody_ok_echo] turns this plus
             [EchoDisc.line_ok ws] into it).  The slot the loop left
             carries it ([UkSh.ush_posw]); the echo era ignores it. *)
          ⌜ FileDisc.fline_ok (UkSh.ush_lastbody I) ⌝ -∗
          ⌜ 0 < s0 ⌝ -∗ ⌜ s0 + Z.of_nat len + 1 < Z64 ⌝ -∗
          ⌜ s0 + Z.of_nat len < 2 ^ 38 ⌝ -∗
          ⌜ 8344 <= sz ⌝ -∗ ⌜ UserPtTree.pgroundup sz = sz ⌝ -∗
          ⌜ usz_ok (sz + 65536) ⌝ -∗
          ⌜ UkSh.ush_fd0c ld /\ UkSh.ush_fd1p ld /\ UkSh.ush_fd2p ld ⌝ -∗
          (* NO FREE WRITE LAW (M4b(2)): the paid child's walk spends it
             nowhere -- its one diagnostic goes through the links *)
          shk_code (ukn_t N') -∗
          shp_code (ukn_t N') -∗ shp_rodata (ukn_t N') -∗ ush_jtab (ukn_t N') -∗
          ustr (ukn_d N') (DfracOwn 1) s0 len g -∗
          ustr (ukn_d N') dw ushp_whitespace 5 ushp_ws_f -∗
          ustr (ukn_d N') dv ushp_symbols 7 ushp_sym_f -∗
          (* ...AT THE PARENT'S OK VIEW (seccomp S4): the child's table is
             sh's, every row closed or the console *)
          UkSh.ush_std N' T ld -∗
          UserCwd.ucwd (ukn_cwd N') FsImg.ROOTINO -∗
          (* ...AND ITS CHILDREN SET IS EMPTY, ON THE NOSE (design
             app-pipe SS4.3w, purchase 2), where the law used to take
             [UserChildren.uch_any].  The fork arm HAS the stronger row --
             [UkShRun.wp_kshr_fork1]'s child arm is at [∅] and was
             weakening it here -- and a child that cannot say its own set
             is empty cannot tell its own two forks apart later: the
             pipeline round needs [Sc = ∅] at the runcmd child, which IS
             this law's [N'] ([UShPipeRound.sh_pipe_child_law] is this
             statement at [ushq_lp]). *)
          UserChildren.uch (ukn_ch N') ∅ -∗
          (* ...AND ITS OWN PID, NOT <init>'s (purchase 1's relay, spent
             here).  A premise on a [□ ∀] law is FREE for its provers --
             the echo and file eras introduce it and drop it -- and owed
             by its ONE consumer, [wp_kshf_fork_core]'s child arm below,
             which now has it.  What it buys is the pid-carrying wait
             ([UkShRun.wp_kshr_wait_pid]): a process holding it can refute
             [UserChildren.wait_ans]'s [pidv = 1] disjunct and so say
             WHICH of its children a reap reaped. *)
          UkSh.ush_pid N' -∗
          UkShMalloc.ushm_fresh N' sz -∗
          Wc I 3%nat -∗
          urun N' h m (mword_of_int 0x99c)
            (Dc + (8 + (UkShDiag.ush_Dg + n))) -∗
          mWP (Loop : expr riscv_lang)))%I.

  Definition ushf_child_law : iProp Σ :=
    ushf_child_law_at UkSh.ush_line_is 60.

  (* NOT [apply _]: the line predicate is a VARIABLE, so the search walks
     the whole body (durable-notes, the fourth silent hang). *)
  Global Instance ushf_child_law_at_persistent Lp Dc :
    Persistent (ushf_child_law_at Lp Dc).
  Proof using .
    rewrite /ushf_child_law_at. apply bi.intuitionistically_persistent.
  Qed.
  Global Instance ushf_child_law_persistent : Persistent ushf_child_law.
  Proof using . rewrite /ushf_child_law. apply _. Qed.

  (* WHAT THE FORK LEFT IN THE PARENT'S HAND, beside the children set it
     grew to: the token of the child it forked, at the payload it chose.
     The row's other arm -- the lend back whole, at a [-1] -- is refuted in
     [wp_kshf_fork_core]: fork1 panics at [-1], and its returning arm says
     the answer is not [-1]. *)
  Definition ushf_fans (Sc : gset gname) (Q : Z -> iProp Σ)
      (Sw : gset gname) : iProp Σ :=
    (∃ (γ : gname) (pidc : mword 32),
       ⌜Sw = Sc ∪ {[γ]}⌝ ∗ child_tok γ pidc Q)%I.

  (* THE SET AFTER THE WAIT IS EMPTY AGAIN (lane EXEC-SEAM).  sh enters
     with no children ([UkSh.ush_pstate]'s [uch γch ∅]), a turn forks at
     most one, and its wait -- at a pid that is not <init>'s -- either
     fails with the set empty ([UkRunSys.wp_uk_ecall_wait_null_pid]'s row)
     or reaps out of sh's OWN set ([UserChildren.wait_ans]'s [γ' ∈ cs ∨
     pidv = 1], the right disjunct refuted), and the only generation in
     that set is the one the fork put there.  Pure, so the caller reads
     it with an [iAssert ... as %] and keeps both answers. *)
  Lemma ushf_wait_empty (Q : Z -> iProp Σ)
      (Sw Sw' : gset gname) (ret : mword 64) (pidv : mword 32) :
    pidv <> (mword_of_int 1 : mword 32) ->
    (ret = (mword_of_int (-1) : mword 64) -> Sw' = (∅ : gset gname)) ->
    ushf_fans ∅ Q Sw -∗ uwait_ans_pid ret Sw Sw' pidv -∗
    ⌜Sw' = (∅ : gset gname)⌝.
  Proof using .
    intros Hne Hm1. iIntros "Hfans Hans".
    rewrite /uwait_ans_pid /uwait_ans_at.
    iDestruct "Hans" as (gn b rv xs) "[%Hr Hwa]".
    rewrite /UserChildren.wait_ans.
    iDestruct "Hwa" as "[[%Hf _] | Hreap]".
    { iPureIntro. apply Hm1. rewrite Hr (proj1 Hf). exact UexecRet.sext_neg1_64. }
    iDestruct "Hreap" as (γ') "(%Hrng & %Hoci & _ & _)".
    destruct Hoci as [Hin | Heq]; [ | exfalso; exact (Hne Heq) ].
    destruct Hrng as [HSw' _].
    rewrite /ushf_fans. iDestruct "Hfans" as (γ pidc) "[%HSw _]". iPureIntro.
    rewrite HSw in Hin. rewrite HSw' HSw.
    assert (Hg : γ' = γ) by set_solver. subst γ'. set_solver.
  Qed.

  (* sh's pid handle, as the wait row reads it: a [Z] other than 1 is a
     word other than <init>'s *)
  Lemma ushf_pid_ne_1 (pidv : mword 32) (p : Z) :
    bv_unsigned pidv = p -> p <> 1 -> pidv <> (mword_of_int 1 : mword 32).
  Proof using .
    intros Hp Hne Heq. apply Hne. rewrite <- Hp, Heq. vm_compute. reflexivity.
  Qed.

  (* ===================================================================== *)
  (* §3b THE ARM, ONCE, AT AN ABSTRACT LEND (step 4).                       *)
  (*                                                                        *)
  (* fork1, the [c.beqz] both processes run, the child's line cut and       *)
  (* allocator state, the parent's [wait] at its OWN pid, and the head --   *)
  (* with the payload, the lend, the child's continuation at 0x99c and the *)
  (* parent's RE-ENTRY (what the fork's answer and the wait's leave, into   *)
  (* the head's credential slot) all parameters.  [wp_kshf_fork] below     *)
  (* applies it once per arm of the body's slot.                            *)
  (* ===================================================================== *)
  Local Lemma wp_kshf_fork_core
      (h : CpuId) (m : regfile) (f : nat -> bv 8) (k len : nat)
      (sz : Z) (l : list fdstate) (n : nat)
      (Q : Z -> iProp Σ) (Rc : iProp Σ)
      (* ...and what fork1's panic spends (M4b(2)) *)
      (Pex : iProp Σ) :
    (forall x y : Z, Q x = Q y) ->
    UkSh.ush_regs m ->
    m !!! Regidx s1_idx = mword_of_int (sh_buf + Z.of_nat k) ->
    (forall j : nat, (j < len)%nat -> f (k + j)%nat <> ubyte0) ->
    f (k + len)%nat = ubyte0 ->
    (k + len < sh_nbuf)%nat ->
    ushl_head l sz -∗
    shk_code γt -∗ shk_rodata γt -∗ ush_jtab γt -∗
    ⌜ UkSh.ush_fd0p l ⌝ -∗
    ush_std l -∗ UserCwd.ucwd γcwd FsImg.ROOTINO -∗
    (* the loop's two identity fragments (lane EXEC-SEAM): no children at
       the head, and a pid that is not <init>'s *)
    UserChildren.uch γch ∅ -∗ ush_pid -∗
    (* what the parent lends, how a killer pays for it, and what fork1's
       panic spends -- borrowed, and back on the returning arm *)
    Rc -∗
    □ (app_taint -∗ Q (-1)) -∗
    Pex -∗
    (* THE PANIC: fork failed, and sh is at [panic]'s entry with "fork" in
       a0, its ledger, fork's answer and what it borrowed -- see
       [UkShRun.wp_kshr_fork1].  The children set was opened at some [Sc]
       for the fork, so the arm is over it. *)
    (∀ (Sc : gset gname) (h' : CpuId) (m' : regfile) (r : mword 64),
       ⌜ uint (m' !!! Regidx a0_idx) = 0x1288 ⌝ -∗
       ⌜ r = (mword_of_int (-1) : mword 64) ⌝ -∗
       ((⌜r = (mword_of_int (-1) : mword 64)⌝ ∗
           UserChildren.uch γch Sc ∗ Rc)
        ∨ ∃ (γ : gname) (pidv : mword 32),
            ⌜r = (sign_extend' 64 pidv : mword 64)⌝ ∗
            ⌜(1 <= bv_unsigned pidv <= PIDMAX)%Z⌝ ∗
            child_tok γ pidv Q ∗
            UserChildren.uch γch (Sc ∪ {[γ]})) -∗
       UserFd.ustd γfd l -∗
       Pex -∗
       urun N h' m' (mword_of_int ShSyms.panic)
         (UkShDiag.ush_Dg + (74 + (UkSh.ush_Dpipe + n))) -∗
       mWP (Loop : expr riscv_lang)) -∗
    (* THE CHILD, at 0x99c *)
    (∀ (N' : uk_names Σ) (hB : CpuId) (mA : regfile) (γ' : gname),
       ⌜ ukn_pay N' = Q ⌝ -∗
       (* ...and its held set is the FORKING SHELL'S (lane OFF-HAND-4,
          S1/S2): [UkShRun.wp_kshr_fork1]'s row, relayed.  The step to
          [ushf_child_law]'s [empty] is sh's own slot
          ([UkSh.ush_gen_slot_held]), which this core lemma does not
          hold and its callers do. *)
       ⌜ mA !!! Regidx s1_idx
         = (mword_of_int (sh_buf + Z.of_nat k) : mword 64) ⌝ -∗
       my_pay γ' Q -∗ Rc -∗
       shk_code (ukn_t N') -∗ shk_rodata (ukn_t N') -∗ ush_jtab (ukn_t N') -∗
       ustr (ukn_d N') (DfracOwn 1) (sh_buf + Z.of_nat k) len
         (fun j : nat => f (k + j)%nat) -∗
       ustr (ukn_d N') DfracDiscarded ushp_whitespace 5 ushp_ws_f -∗
       ustr (ukn_d N') DfracDiscarded ushp_symbols 7 ushp_sym_f -∗
       (* ...AT THE PARENT'S OK VIEW (seccomp S4) *)
       UkSh.ush_std N' T l -∗
       UserCwd.ucwd (ukn_cwd N') FsImg.ROOTINO -∗
       UserChildren.uch (ukn_ch N') ∅ -∗
       (* ...and its own pid, not <init>'s (design app-pipe SS4.3w,
          purchase 1's relay): [UkShRun.wp_kshr_fork1]'s row, in the shape
          [UkSh.ush_pid] names it *)
       UkSh.ush_pid N' -∗
       UkShMalloc.ushm_fresh N' sz -∗
       urun N' hB mA (mword_of_int 0x99c)
         (68 + (8 + (UkShDiag.ush_Dg + (UkSh.ush_Dpipe + n)))) -∗
       mWP (Loop : expr riscv_lang)) -∗
    (* THE PARENT'S RE-ENTRY: the head's slot out of what the fork and the
       wait left, and what fork1 borrowed back.  The fork went out at the
       EMPTY set and the wait's row is at sh's own pid, which is not
       <init>'s (lane EXEC-SEAM) -- so the arm can identify the reaped
       generation. *)
    (∀ (Sw Sw' : gset gname) (ret : mword 64) (pidv : mword 32),
       ⌜ pidv <> (mword_of_int 1 : mword 32) ⌝ -∗
       ⌜ ret = (mword_of_int (-1) : mword 64) -> Sw' = (∅ : gset gname) ⌝ -∗
       ushf_fans ∅ Q Sw -∗
       uwait_ans_pid ret Sw Sw' pidv -∗
       Pex -∗
       ◇ UkSh.ush_posb N γp T Wc Wb Pm l 0%nat) -∗
    ushl_dat -∗ usz γs sz -∗
    ubytes γd sh_buf sh_nbuf f -∗
    urun N h m (mword_of_int 0x908) (16 + (UkSh.ush_Dbody + n)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using HT Hpay Hpsok_free.
    intros HQc Hregs Hs1 Hnn Hnul Hkl.
    iIntros "Hhead #Hcode #Hro #Hjt %Hfd0 Hustd Hcwd Hch Hpid HRc #Hkw
             Hlease Hpanic Hchild Hre Hdat Hsz Hbuf Hrun".
    destruct Hregs as (Hs2 & Hs3 & Hs4 & Hs5 & Hs6).
    assert (Hlen31 : Z.of_nat len < 2 ^ 31)
      by (unfold sh_nbuf in Hkl; lia).
    (* ---- 0x908  jal ra,fork1 ---- *)
    iApply (wp_uk_jal N h m (mword_of_int 0x908)
              (mword_of_int 2094944 : mword 21) ra_idx
              (mword_of_int ShSyms.fork1) (mword_of_int 0x90c)
              (16 + (UkSh.ush_Dbody + n))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_908 with "Hcode"). }
    iIntros (h1) "Hrun".
    set (m1 := <[Regidx ra_idx
                 := regval_into_reg (mword_of_int 0x90c : mword 64)]> m).
    assert (Hra_1 : m1 !!! Regidx ra_idx = (mword_of_int 0x90c : mword 64))
      by exact (upd_eq m (Regidx ra_idx) _).
    assert (Hm1 : forall q : mword 5, Regidx q <> Regidx ra_idx ->
                    m1 !!! Regidx q = m !!! Regidx q)
      by (intros q Hq; exact (upd_ne m (Regidx ra_idx) (Regidx q) _ Hq)).
    (* ---- fork1() ---- *)
    replace (16 + (UkSh.ush_Dbody + n))%nat
      with (2 + (UkShDiag.ush_Dg + (74 + (UkSh.ush_Dpipe + n))))%nat
      by (unfold UkShDiag.ush_Dg, UkSh.ush_Dbody, UkSh.ush_Dpipe; lia).
    (* THE CHILDREN SET IS OPENED FOR THE FORK-WAIT WINDOW (lane IO-LEAF,
       M3a) and closed again at the loop head: the fork MINTS the token at
       the generation that joined it, and the wait REPORTS what the reap
       left.  THE PAYLOAD AND THE LEND ARE THE CALLER'S (step 4). *)
    iDestruct "Hustd" as (vw) "[#Hvok Hustd]".
    iApply (UkShDiag.wp_kshr_fork1_final_at N (ushf_pay f)
              sz l vw ∅ h1 m1 (74 + (UkSh.ush_Dpipe + n)) FsImg.ROOTINO ∅ Q Rc Pex HQc
              with "Hcode Hro [Hdat Hbuf] Hsz Hustd Hcwd Hch [] HRc Hkw
                    Hlease Hrun").
    { rewrite /ushf_pay.
      iSplitR; [ iExact "Hcode" | ].
      iSplitR; [ iExact "Hro" | ].
      iSplitR; [ iExact "Hjt" | ].
      iFrame "Hdat Hbuf". }
    { rewrite big_sepM_empty. done. }
    rewrite Hra_1.
    assert (Eret : ret_pc (mword_of_int 0x90c : mword 64)
                   = mword_of_int 0x90c)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Eret.
    iSplitL "Hpanic".
    { (* ================= THE PANIC: fork failed ======================= *)
      iIntros (hA mA rA) "%Hmsg %HrA Hans Hustd Hpex Hrun".
      (* design app-pipe SS4.3y: [UkShRun.wp_kshr_fork1]'s panic arm now
         carries the forked generation's FRESHNESS.  This law is the echo
         and file eras' as well and reads no such row, so the conjunct is
         dropped here -- one weakening, statement byte-identical. *)
      iAssert ((⌜rA = (mword_of_int (-1) : mword 64)⌝
                  ∗ UserChildren.uch γch ∅ ∗ Rc)
               ∨ ∃ (γ : gname) (pidv : mword 32),
                   ⌜rA = (sign_extend' 64 pidv : mword 64)⌝ ∗
                   ⌜(1 <= bv_unsigned pidv <= PIDMAX)%Z⌝ ∗
                   child_tok γ pidv Q ∗
                   UserChildren.uch γch (∅ ∪ {[γ]}))%I
        with "[Hans]" as "Hans".
      { iDestruct "Hans" as "[Hf | Hpid]"; [ by iLeft | ].
        iDestruct "Hpid" as (γx pidx) "(%Hr & %Hrng & _ & Htok & Hf)".
        iRight. iExists γx, pidx. iFrame "Htok Hf".
        iSplitR; [ iPureIntro; exact Hr | iPureIntro; exact Hrng ]. }
      iApply ("Hpanic" $! ∅ hA mA rA with "[%] [%] Hans [Hustd] Hpex Hrun");
        [ exact Hmsg | exact HrA | by iApply ustd_at_ustd ]. }
    iSplitL "Hhead Hpid Hre".
    - (* ================= THE PARENT: reap, and round again ============= *)
      iIntros (hA mA rA) "%HrA %Hrm1 %HcsA %Ha0A Hans Hpay Hsz Hustd Hcwd _
                          Hlease Hrun".
      iDestruct "Hpay" as "(_ & _ & _ & Hdat & Hbuf)".
      (* WHAT THE FORK LEFT IN sh's HAND, at the set it grew to.  The row's
         whole-lend arm is at [-1], and fork1's returning arm is not: the
         lend never comes back to the parent *)
      iAssert (∃ Sw : gset gname,
                 UserChildren.uch (ukn_ch N) Sw ∗ ushf_fans ∅ Q Sw)%I
        with "[Hans]" as "Hchx".
      { rewrite /ushf_fans.
        iDestruct "Hans" as "[(%Hr & _ & _) | Hpid']".
        - exfalso. exact (Hrm1 Hr).
        (* one slot more since design app-pipe SS4.3y: the answer's pid
           arm carries the generation's freshness, which this era's
           [ushf_fans] does not record. *)
        - iDestruct "Hpid'" as (γ pidv) "(_ & _ & _ & Htok & Hf)".
          iExists (∅ ∪ {[γ]}). iFrame "Hf".
          iExists γ, pidv. iFrame "Htok". by iPureIntro. }
      iDestruct "Hchx" as (Sw) "[Hch Hfans]".
      (* ---- 0x90c  c.beqz a0,0x99c -- NOT taken: this is the parent ---- *)
      iApply (wp_uk_cbeqz N hA mA (mword_of_int 0x90c)
                (mword_of_int 72 : mword 8) (mword_of_int 2 : mword 3) a0_idx
                false (mword_of_int 0x99c)
                (2 + (UkShDiag.ush_Dg + (74 + (UkSh.ush_Dpipe + n))))
                ltac:(vm_compute; reflexivity)
                ltac:(rewrite Ha0A; symmetry; exact (ushf_eqv_false rA HrA))
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(discriminate)
                with "[] Hrun").
      { iApply (uis_shk_90c with "Hcode"). }
      assert (E930 : add_vec_int (mword_of_int 0x90c : mword 64) 2
                     = mword_of_int 0x90e)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite E930. iIntros (hB) "Hrun".
      (* ---- 0x90e  c.li a0,0 ---- *)
      iApply (wp_uk_cli N hB mA (mword_of_int 0x90e)
                (mword_of_int 0 : mword 6) a0_idx
                (2 + (UkShDiag.ush_Dg + (74 + (UkSh.ush_Dpipe + n))))
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate) with "[] Hrun").
      { iApply (uis_shk_90e with "Hcode"). }
      assert (Em0 : <[Regidx a0_idx
                      := regval_into_reg (sign_extend' 64
                           (mword_of_int 0 : mword 6) : mword 64)]> mA
                    = <[Regidx a0_idx
                        := regval_into_reg (mword_of_int 0 : mword 64)]> mA)
        by (f_equal; apply bv_eq; vm_compute; reflexivity).
      assert (E932 : add_vec_int (mword_of_int 0x90e : mword 64) 2
                     = mword_of_int 0x910)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite E932 Em0. iIntros (hC) "Hrun".
      set (mB := <[Regidx a0_idx
                   := regval_into_reg (mword_of_int 0 : mword 64)]> mA).
      (* ---- 0x910  jal ra,wait ---- *)
      iApply (wp_uk_jal N hC mB (mword_of_int 0x910)
                (mword_of_int 858 : mword 21) ra_idx
                (mword_of_int ShSyms.wait) (mword_of_int 0x914)
                (2 + (UkShDiag.ush_Dg + (74 + (UkSh.ush_Dpipe + n))))
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity)
                with "[] Hrun").
      { iApply (uis_shk_910 with "Hcode"). }
      iIntros (hD) "Hrun".
      set (mC := <[Regidx ra_idx
                   := regval_into_reg (mword_of_int 0x914 : mword 64)]> mB).
      assert (Ha0_C : uint (mC !!! Regidx a0_idx) = 0).
      { rewrite /mC (upd_ne mB (Regidx ra_idx) (Regidx a0_idx) _
                       ltac:(vm_compute; discriminate)).
        rewrite /mB (upd_eq mA (Regidx a0_idx) _).
        exact (uint_moi 0 ltac:(unfold Z64; lia)). }
      assert (Hra_C : mC !!! Regidx ra_idx = (mword_of_int 0x914 : mword 64))
        by exact (upd_eq mB (Regidx ra_idx) _).
      (* ---- wait((int * )0), AT sh's OWN PID (step 4) ---- *)
      iDestruct "Hpid" as (pid) "[%Hpid1 Hpid]".
      iApply (UkShRun.wp_kshr_wait_pid Hpsok_free N hD mC
                (2 + (UkShDiag.ush_Dg + (74 + (UkSh.ush_Dpipe + n)))) Sw pid Ha0_C
                with "Hcode Hrun Hch Hpid").
      iIntros (hE ret Sw' pidv) "%Hpv Hpid %Hneg1 Hans Hrun Hch".
      (* THE SET IS EMPTY AGAIN (lane EXEC-SEAM): the wait reaped the one
         generation the fork put in, or failed with the set empty *)
      assert (Hpv1 : pidv <> (mword_of_int 1 : mword 32))
        by exact (ushf_pid_ne_1 pidv pid Hpv Hpid1).
      iAssert (⌜Sw' = (∅ : gset gname)⌝)%I as %HSw'.
      { iApply (ushf_wait_empty Q Sw Sw' ret pidv Hpv1 Hneg1
                  with "Hfans Hans"). }
      iEval (rewrite HSw') in "Hch".
      iAssert ush_pid with "[Hpid]" as "Hpid";
        [ iExists pid; iSplitR; [ iPureIntro; exact Hpid1 | iExact "Hpid" ] | ].
      rewrite Hra_C.
      assert (Eret2 : ret_pc (mword_of_int 0x914 : mword 64)
                      = mword_of_int 0x914)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite Eret2.
      set (mD := <[Regidx a0_idx := ret]>
                   (<[Regidx a7_idx := (mword_of_int 3 : mword 64)]> mC)).
      (* the five constants are still where main put them *)
      assert (HkeepD : forall q : mword 5,
                ucallee_saved_idx q = true ->
                mD !!! Regidx q = m !!! Regidx q).
      { intros q Hq.
        assert (Hne : forall rq : mword 5, ucallee_saved_idx rq = false ->
                        Regidx q <> Regidx rq).
        { intros rq Hr He. injection He as He. subst q.
          rewrite Hr in Hq. discriminate Hq. }
        assert (Fra : ucallee_saved_idx ra_idx = false)
          by (vm_compute; reflexivity).
        assert (Fa0 : ucallee_saved_idx a0_idx = false)
          by (vm_compute; reflexivity).
        assert (Fa7 : ucallee_saved_idx a7_idx = false)
          by (vm_compute; reflexivity).
        rewrite /mD (upd_ne _ (Regidx a0_idx) (Regidx q) _ (Hne a0_idx Fa0)).
        rewrite (upd_ne mC (Regidx a7_idx) (Regidx q) _ (Hne a7_idx Fa7)).
        rewrite /mC (upd_ne mB (Regidx ra_idx) (Regidx q) _ (Hne ra_idx Fra)).
        rewrite /mB (upd_ne mA (Regidx a0_idx) (Regidx q) _ (Hne a0_idx Fa0)).
        rewrite (HcsA q Hq).
        exact (Hm1 q (Hne ra_idx Fra)). }
      assert (HregsD : UkSh.ush_regs mD).
      { rewrite /UkSh.ush_regs. split_and!.
        - rewrite (HkeepD s2_idx ltac:(vm_compute; reflexivity)). exact Hs2.
        - rewrite (HkeepD s3_idx ltac:(vm_compute; reflexivity)). exact Hs3.
        - rewrite (HkeepD s4_idx ltac:(vm_compute; reflexivity)). exact Hs4.
        - rewrite (HkeepD s5_idx ltac:(vm_compute; reflexivity)). exact Hs5.
        - rewrite (HkeepD s6_idx ltac:(vm_compute; reflexivity)). exact Hs6. }
      replace (2 + (UkShDiag.ush_Dg + (74 + (UkSh.ush_Dpipe + n))))%nat
        with (16 + (UkSh.ush_Dbody + n))%nat
        by (unfold UkShDiag.ush_Dg, UkSh.ush_Dbody, UkSh.ush_Dpipe; lia).
      (* THE RE-ENTRY: the head's slot out of what the fork and the wait
         left (the caller's law), and the head *)
      iMod ("Hre" $! Sw Sw' ret pidv with "[%] [%] Hfans Hans Hlease") as "Hpos";
        [ exact Hpv1 | exact Hneg1 | ].
      iApply ("Hhead" $! hE mD f n
                with "[%] [%] [Hustd Hcwd Hch Hpid Hpos] Hdat Hsz Hbuf Hrun").
      + exact HregsD.
      + exact Hfd0.
      + rewrite /UkSh.ush_pstate /UkSh.ush_std /ustd_ok. iFrame "Hcwd Hch Hpid Hpos".
        iExists vw. by iFrame "Hvok Hustd".
    - (* ================= THE CHILD: parse, run, exec =================== *)
      iIntros (N' hA mA γ') "%Hpeq' %HcsA %Ha0A Hmy HRc #Hcode' Hpay Hsz Hustd Hcwd
                             Hch Hpid' _ Hrun".
      iDestruct "Hpay" as "(_ & #Hro' & #Hjt' & Hdat & Hbuf)".
      (* ---- 0x90c  c.beqz a0,0x99c -- TAKEN: this is the child ---- *)
      iApply (wp_uk_cbeqz N' hA mA (mword_of_int 0x90c)
                (mword_of_int 72 : mword 8) (mword_of_int 2 : mword 3) a0_idx
                true (mword_of_int 0x99c)
                (2 + (UkShDiag.ush_Dg + (74 + (UkSh.ush_Dpipe + n))))
                ltac:(vm_compute; reflexivity)
                ltac:(rewrite Ha0A; symmetry;
                      rewrite (moi_eq_zero 0 ltac:(unfold Z64; lia));
                      reflexivity)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(intros _; vm_compute; reflexivity)
                with "[] Hrun").
      { iApply (uis_shk_90c with "Hcode'"). }
      iIntros (hB) "Hrun".
      (* the line, cut out of the child's own copy of the buffer *)
      iDestruct (UkShCd.ushc_bytes_sub N' sh_buf sh_nbuf f k (S len)
                   ltac:(lia) with "Hbuf") as "[Hsub _]".
      iDestruct (UkShCd.ushc_ustr_of_bytes N' (sh_buf + Z.of_nat k) len
                   (fun j : nat => f (k + j)%nat) Hnn Hlen31 Hnul
                   with "Hsub") as "Hline".
      iDestruct (UkShLoop.ushl_fresh_of_dat N' sz with "Hdat Hsz")
        as "(Hfresh & Hws & Hsy)".
      assert (Hs1_A : mA !!! Regidx s1_idx
                      = (mword_of_int (sh_buf + Z.of_nat k) : mword 64)).
      { rewrite (HcsA s1_idx ltac:(vm_compute; reflexivity)).
        rewrite (Hm1 s1_idx ltac:(vm_compute; discriminate)). exact Hs1. }
      replace (2 + (UkShDiag.ush_Dg + (74 + (UkSh.ush_Dpipe + n))))%nat
        with (68 + (8 + (UkShDiag.ush_Dg + (UkSh.ush_Dpipe + n))))%nat
        by (unfold UkShDiag.ush_Dg, UkSh.ush_Dbody, UkSh.ush_Dpipe; lia).
      iApply ("Hchild" $! N' hB mA γ' with "[%] [%] Hmy HRc Hcode' Hro' Hjt'
                Hline Hws Hsy [Hustd] Hcwd Hch Hpid' Hfresh Hrun");
        [ exact Hpeq' | exact Hs1_A | rewrite /UkSh.ush_std /ustd_ok; iExists vw; by iFrame "Hvok Hustd" ].
  Qed.

  (* ===================================================================== *)
  (* §3c THE ARM, at the body's slot: three cases, one lemma each way.      *)
  (*                                                                        *)
  (* On the CONSOLE arm the fork LENDS the block credential and the child   *)
  (* runs echo on the paid entry ([ushf_child_law]); its exit hands back    *)
  (* [ushf_wq np], and the parent's [wait] -- at its own pid, with the      *)
  (* kernel's row that a -1 leaves no children -- REFUTES the failing arm   *)
  (* against the live token and REDEEMS the payload when the reaped         *)
  (* generation is the one it forked.  When it is not -- the reaped         *)
  (* generation is another child of sh's, or sh reaped an orphan as <init> *)
  (* would -- the loop re-enters on the slot's affine arm: the shell's      *)
  (* children set and pid are unconstrained at its entry                    *)
  (* ([SpecKexec.exec_slot_pre] carries neither row), so neither case can   *)
  (* be refuted here.  THIS IS THE ONE PRODUCER of that arm in this file.   *)
  (* On the AFFINE arm and under the TAINT the child runs the generic walk  *)
  (* at the trivial payload, as before.                                     *)
  (* ===================================================================== *)
  (* THE LEXER PREMISES ARE GONE (lane SH-CHILD).  [ushp_no_symbols],
     [ushp_tokens] and the token count were premises of this lemma and of
     [wp_kshm_body], and NEITHER PROOF READ THEM: the parse happens in the
     CHILD, whose law re-derives it from the line fact
     ([UkShEcho.ush_line_toks_holds] inside [wp_kshm_child_echo_holds]).
     They could not survive the redirect line anyway -- it HAS a symbol
     byte -- so what is left is the line fact, abstract. *)
  Lemma wp_kshf_fork_at
      (Lp : list (list (bv 8)) -> (nat -> bv 8) -> nat -> nat -> Prop)
      (Dc : nat)
      (h : CpuId) (m : regfile) (f : nat -> bv 8) (k len : nat)
      (ws : list (list (bv 8)))
      (sz : Z) (l : list fdstate) (n : nat) :
    (Dc <= 68 + UkSh.ush_Dpipe)%nat ->
    UkSh.ush_regs m ->
    m !!! Regidx s1_idx = mword_of_int (sh_buf + Z.of_nat k) ->
    (forall j : nat, (j < len)%nat -> f (k + j)%nat <> ubyte0) ->
    f (k + len)%nat = ubyte0 ->
    (k + len < sh_nbuf)%nat ->
    (* ...and it is a line the discipline admits (step 4): what the paid
       child law is stated at, at the word list the loop found *)
    Lp ws (fun j : nat => f (k + j)%nat) 0%nat len ->
    (* the break, as [exec] leaves it *)
    8344 <= sz ->
    UserPtTree.pgroundup sz = sz ->
    usz_ok (sz + 65536) ->
    (* the lease's two laws the fork arm spends (lane IO-LEAF, step 3):
       premises of the obligation, see [UkSh.ush_rest_l] *)
    (forall n' : nat,
       ⊢ UkSh.ush_at N γp n' -∗
         ∃ I : list (bv 8), ⌜length I = n'⌝ ∗ UkSh.ush_lease N γp T Pm I) ->
    (* ...and the payload's OWN assembler (M4b(2)): what the fork panic
       leaves is the banner-owed credential, and the exit is paid from it *)
    (forall I : list (bv 8),
       ⊢ Pm I -∗ Wb I -∗ UkSh.ush_at N γp (length I)) ->
    (* THE TAINT'S CONTINUATION (lane R3), in place of the free write law
       and the exec supply: a tainted process does not run sh's code, so
       the arm hands its run to the generic slot right here rather than
       forking a generic child.  [UkRun.uxsup] has no producer anywhere in
       the tree, which is why that arm could never be paid from the top. *)
    UkSh.ush_gen_slot N T -∗
    ushl_head l sz -∗
    shk_code γt -∗
    shk_rodata γt -∗ ush_jtab γt -∗
    (* the two laws of the paid child (step 4) *)
    ushf_kill_law -∗
    ushf_child_law_at Lp Dc -∗
    (* ...and the law of sh's own panic (M4b(2)) *)
    UkShDiag.ush_panic_law Wc Wb -∗
    (* the row the console preamble established (lane SH-OPEN): the PARENT
       keeps its ledger across fork1 -- a REDIR runs in the child -- so the
       row goes straight back into the head *)
    ⌜ UkSh.ush_fd0p l ⌝ -∗
    ush_bstate l ws -∗
    ushl_dat -∗ usz γs sz -∗
    ubytes γd sh_buf sh_nbuf f -∗
    urun N h m (mword_of_int 0x908) (16 + (UkSh.ush_Dbody + n)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using HT HWct Hpay Hpsok_free.
    intros HDc Hregs Hs1 Hnn Hnul Hkl Hline Hszlo Hszal Hszok
           Hpm1 Hpmwb.
    iIntros "#Hgen Hhead #Hcode #Hro #Hjt #Hkl #Hchl #Hplaw %Hfd0 Hstd
             Hdat Hsz Hbuf Hrun".
    iDestruct "Hstd" as "(Hustd & Hcwd & Hch & Hpid & Hpos)".
    (* THE CONSOLE ARM APART FROM THE REST.  The boundary the slot names
       comes out with the EQUATION that the line the loop read is its last
       ([UkSh.ush_posw]) -- which is what the child's law is applied at. *)
    iAssert ((∃ I : list (bv 8),
                ⌜rest_of I = [] /\ last_ws I = ws
                 /\ FileDisc.fline_ok (UkSh.ush_lastbody I)⌝ ∗ Pm I
                ∗ ⌜UkSh.ush_fd0c l /\ UkSh.ush_fd1p l /\ UkSh.ush_fd2p l⌝
                ∗ Wc I 3%nat)
             ∨ (T ∗ UkSh.ush_pos N γp))%I
      with "[Hpos]" as "[Hcon | [#HT Hpos]]".
    { rewrite /UkSh.ush_posw. iDestruct "Hpos" as "[Hb | Ht]"; last first.
      { iRight. iExact "Ht". }
      iDestruct "Hb" as (np) "(%Hbl & Hpm & Hwc)".
      rewrite /UkSh.ush_wcp. iDestruct "Hwc" as "[[%Hrow Hc] | [%Hcl _]]".
      - iLeft. iExists np. iFrame "Hpm Hc". iPureIntro.
        split; [ exact Hbl | exact Hrow ].
      - (* the closed arm never reaches the body ([p < 3] at [p = 3]) *)
        exfalso. destruct Hcl as [_ Hlt]. lia. }
    - (* ================= THE CONSOLE ARM: lend, and redeem ============= *)
      iDestruct "Hcon" as (np) "([%Hbnd [%Hlast %Hfbk]] & Hpm & %Hrow & Hc)".
      (* WHAT FORK1 BORROWS IS THE LEASE'S PIECES (M4b(2)): a failed fork
         pays "fork\n" from the lend and its exit from the pieces and the
         banner-owed credential the message leaves; a fork that returned
         hands the pieces back to the re-entry. *)
      iAssert (□ (app_taint -∗ ushf_wq np))%I as "#Hkw".
      { iIntros "!> Hk". rewrite /ushf_wq. iApply ("Hkl" $! np with "Hk"). }
      iApply (wp_kshf_fork_core h m f k len sz l n (fun _ : Z => ushf_wq np)
                (Wc np 3%nat) (Pm np) ltac:(intros x y; reflexivity)
                Hregs Hs1 Hnn Hnul Hkl
                with "Hhead Hcode Hro Hjt [%] Hustd Hcwd Hch Hpid Hc Hkw
                      Hpm [] [] [] Hdat Hsz Hbuf Hrun");
        [ exact Hfd0 | | | ].
      + (* THE PANIC, PAID (M4b(2)): fork failed and the lend came back
           whole -- the row's [-1] arm -- so the five bytes go out on the
           block credential and the exit is paid from the pieces and the
           banner-owed credential they leave ([ush_at_of_pm_wb]). *)
        iIntros (Sc h' m' r) "%Hmsg %Hr1 Hans Hustd' Hpm' Hrun'".
        iDestruct "Hans" as "[(_ & _ & HRc) | Hpid']".
        * iApply (UkShDiag.wp_kshd_panic_paid N Wc Wb l h' m' (74 + (UkSh.ush_Dpipe + n)) np
                    (proj2 (proj2 Hrow)) Hmsg
                    with "Hplaw Hcode Hro Hustd' HRc [Hpm'] Hrun'").
          iIntros "_ Hwb".
          iDestruct (Hpmwb np with "Hpm' Hwb") as "Hat".
          iEval (rewrite /UkSh.ush_at) in "Hat".
          iDestruct "Hat" as "[_ Hpay]". iExact "Hpay".
        * (* THE ROW'S PID ARM AT -1 IS REFUTED (lane RESIDUALS, (A)): the
             leaf's pid arm carries the pid's range ([UexecRet.ufork_ans],
             off [SpecKfork.kfork_post]), and a pid in [1, PIDMAX]
             sign-extends to a small positive, never to -1. *)
          iDestruct "Hpid'" as (γ pidv) "(%Hpv & %Hrng & _ & _)".
          exfalso.
          exact (ushf_pid_sext_ne_m1 pidv Hrng (eq_trans (eq_sym Hpv) Hr1)).
      + (* the child, on the paid entry *)
        iIntros (N' hB mA γ') "%Hpeq' %Hs1A Hmy HRc #Hcode' #Hro' #Hjt'
                               Hline' Hws Hsy Hustd' Hcwd' Hch' Hpid' Hfresh
                               Hrun'".
        (* THE CHILD'S ROOM, AS ITS OWN LAW ASKS FOR IT (lane SH-CHILD-2):
           the core hands [68 + (8 + (ush_Dg + n))] -- the body's
           [ush_Dbody] less its own frames -- and a law that spends [Dc] of
           it is that same run at [68 - Dc + n]. *)
        iRevert "Hrun'".
        replace (68 + (8 + (UkShDiag.ush_Dg + (UkSh.ush_Dpipe + n))))%nat
          with (Dc + (8 + (UkShDiag.ush_Dg + (68 + UkSh.ush_Dpipe - Dc + n))))%nat by lia.
        iIntros "Hrun'".
        iApply ("Hchl" $! N' hB mA DfracDiscarded DfracDiscarded
                  (sh_buf + Z.of_nat k) len ws (fun j : nat => f (k + j)%nat)
                  sz l (68 + UkSh.ush_Dpipe - Dc + n)%nat np
                  with "[%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%]
                        Hcode' [] []
                        Hjt' Hline' Hws Hsy Hustd' Hcwd' Hch' Hpid' Hfresh HRc
                        Hrun'").
        * exact Hpeq'.
        * exact Hs1A.
        * exact Hline.
        * symmetry. exact Hlast.
        * exact Hfbk.
        * unfold sh_buf. lia.
        * unfold sh_buf, sh_nbuf, Z64 in *. lia.
        * unfold sh_buf, sh_nbuf in *. lia.
        * exact Hszlo.
        * exact Hszal.
        * exact Hszok.
        * exact Hrow.
        * iApply (ushf_code_shp with "Hcode'").
        * iApply (ushf_rodata_shp with "Hro'").
      + (* the re-entry, with the pieces back in hand *)
        iIntros (Sw Sw' ret pidv) "%Hpv1 %Hm1 Hfans Hans Hpm".
        rewrite /ushf_fans. iDestruct "Hfans" as (γ pidc) "[%HSw Htok]". subst Sw.
        rewrite /uwait_ans_pid /uwait_ans_at.
        iDestruct "Hans" as (gn b rv xs) "[%Hr Hwa]".
        rewrite /UserChildren.wait_ans.
        iDestruct "Hwa" as "[[%Hneg _] | Hreap]".
        { (* -1: "my own child set is empty" -- against the live token *)
          exfalso. destruct Hneg as [Hrv Hcs].
          assert (Hret1 : ret = (mword_of_int (-1) : mword 64))
            by (rewrite Hr Hrv; exact UexecRet.sext_neg1_64).
          specialize (Hm1 Hret1). rewrite Hm1 in Hcs. set_solver. }
        iDestruct "Hreap" as (γ') "(%Hrng & %Hin & Hesc & #Huniq)".
        (* THE REAPED GENERATION IS THE CHILD SH FORKED (lane EXEC-SEAM):
           the set the wait read held that one generation alone -- sh
           entered with none -- and sh is not <init>, so the row's
           orphan disjunct is refuted and the membership names it. *)
        destruct Hin as [Hin | Heq]; [ | exfalso; exact (Hpv1 Heq) ].
        assert (Hgg : γ' = γ) by set_solver. subst γ'.
        (* THE REDEMPTION: its escrow carries the payload sh chose *)
        iDestruct (exit_tok_pid with "Hesc") as "#Hgp".
        iDestruct (child_tok_pid with "Htok Hgp") as %<-.
        iMod (gen_pay_timeless γ pidc (fun _ : Z => ushf_wq np) xs
                with "Htok Hesc") as "HQ".
        iModIntro.
        iApply (UkSh.ush_posb_of_wc N γp T Wc Wb Pm l 0%nat np Hbnd
                  with "Hpm [HQ]").
        rewrite /UkSh.ush_wcp. iLeft. iSplitR; [ by iPureIntro | ].
        rewrite /ushf_wq. iExact "HQ".
    - (* ============ THE TAINT: sh's code is left HERE (lane R3).  A
         tainted process may run anything, so the arm hands its run to the
         GENERIC SLOT at 0x908 rather than walking fork1/runcmd on the free
         write law and an exec supply nobody can produce.  Everything the
         old arm carried -- the cursor, the lease, the ledger, the buffer
         -- is dropped: the taint claims nothing. ====== *)
      assert (Halo : is_aligned_vaddr
                       (Virtaddr (mword_of_int 0x908 : mword 64)) 2 = true)
        by (vm_compute; reflexivity).
      iApply (UkSh.ush_gen_run N T h m (mword_of_int 0x908)
                (16 + (UkSh.ush_Dbody + n)) Halo with "Hgen HT Hrun").
  Qed.

  (* ===================================================================== *)
  (* §4 MAIN'S BODY, WHOLE -- 0x956 and 0x908..0x914.                       *)
  (*                                                                        *)
  (* THE THREE BYTE TESTS ARE THE DISPATCH, and the disciplined line        *)
  (* decides it at the first: [echo hello world] begins with 'e', so the    *)
  (* [bne a5,s5] at 0x956 is TAKEN and control goes to the fork.  The [cd]  *)
  (* arm -- all three tests falling through -- is REFUTED here (step 4,     *)
  (* M4b(2)'s "cannot cd"), and [UkShCd.wp_kshc_cd] is gone with it.        *)
  (* ===================================================================== *)
  (* AT ANY LINE SHAPE WHOSE FIRST BYTE IS 'e' (lane SH-CHILD).  The walk
     reads the line ONCE, at 0x956, and only to see that it is not a [cd]:
     everything else it does with the line is to hand it to the child's
     law.  So the shape is [Lp] and the one reading is [Hlp0] -- which
     holds of echo's line and of the redirect line alike, both carrying
     [EchoDisc.line_ok] and hence [line_ok_head_byte0]. *)
  Lemma wp_kshm_body_at
      (Lp : list (list (bv 8)) -> (nat -> bv 8) -> nat -> nat -> Prop)
      (Dc : nat)
      (h : CpuId) (m : regfile) (f : nat -> bv 8) (k len : nat)
      (ws : list (list (bv 8)))
      (sz : Z) (l : list fdstate) (n : nat) :
    (Dc <= 68 + UkSh.ush_Dpipe)%nat ->
    (forall (ws' : list (list (bv 8))) (g : nat -> bv 8) (k' len' : nat),
       Lp ws' g k' len' -> bv_unsigned (g k') = 101%Z) ->
    UkSh.ush_regs m ->
    m !!! Regidx s1_idx = mword_of_int (sh_buf + Z.of_nat k) ->
    m !!! Regidx a5_idx = mword_of_int (bv_unsigned (f k)) ->
    (* the line at [k] *)
    (forall j : nat, (j < len)%nat -> f (k + j)%nat <> ubyte0) ->
    f (k + len)%nat = ubyte0 ->
    (k + len < sh_nbuf)%nat ->
    (* ...and it is a line the discipline admits (step 4) *)
    Lp ws (fun j : nat => f (k + j)%nat) 0%nat len ->
    (* the break, as [exec] leaves it *)
    8344 <= sz ->
    UserPtTree.pgroundup sz = sz ->
    usz_ok (sz + 65536) ->
    (* the lease's two laws the fork arm spends (lane IO-LEAF, step 3):
       premises of the obligation, see [UkSh.ush_rest_l] *)
    (forall n' : nat,
       ⊢ UkSh.ush_at N γp n' -∗
         ∃ I : list (bv 8), ⌜length I = n'⌝ ∗ UkSh.ush_lease N γp T Pm I) ->
    (forall I : list (bv 8),
       ⊢ Pm I -∗ Wb I -∗ UkSh.ush_at N γp (length I)) ->
    (* the taint's continuation, in place of the free write law and the
       exec supply (lane R3) -- see [wp_kshf_fork] *)
    UkSh.ush_gen_slot N T -∗
    ushl_head l sz -∗
    shk_code γt -∗
    shk_rodata γt -∗ shp_code γt -∗ ush_jtab γt -∗
    ushf_kill_law -∗
    ushf_child_law_at Lp Dc -∗
    UkShDiag.ush_panic_law Wc Wb -∗
    ⌜ UkSh.ush_fd0p l ⌝ -∗
    ush_bstate l ws -∗
    ushl_dat -∗ usz γs sz -∗
    ubytes γd sh_buf sh_nbuf f -∗
    urun N h m (mword_of_int 0x956) (16 + (UkSh.ush_Dbody + n)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using HT HWct Hpay Hpsok_free.
    intros HDc Hlp0 Hregs Hs1 Ha5 Hnn Hnul Hkl Hline Hszlo Hszal Hszok
           Hpm1 Hpmwb.
    iIntros "#Hgen Hhead #Hcode #Hro #Hpcode #Hjt #Hkl #Hchl #Hplaw %Hfd0
             Hstd Hdat Hsz Hbuf Hrun".
    assert (Hbr : forall j : nat, 0 <= bv_unsigned (f j) < Z64).
    { intros j. pose proof (bv_unsigned_in_range 8 (f j)) as H0.
      assert (Em8 : bv_modulus 8 = 256) by (vm_compute; reflexivity).
      rewrite Em8 in H0. unfold Z64. lia. }
    (* THE FIRST BYTE IS 'e', so the line is not a [cd] command -- at any
       admissible line, because the command it runs IS /echo
       ([EchoDisc.line_ok_head_byte0]) *)
    assert (Hnck : bv_unsigned (f k) <> 99).
    { pose proof (Hlp0 ws (fun j : nat => f (k + j)%nat) 0%nat len Hline)
        as H0. cbn beta in H0. rewrite Nat.add_0_r in H0. lia. }
    pose proof Hregs as Hregs'.
    destruct Hregs' as (Hs2 & Hs3 & Hs4 & Hs5 & Hs6).
    (* ---- 0x956  bne a5,s5 -- TAKEN ---- *)
    assert (Htk7a : true = uv_btaken BNE (m !!! Regidx a5_idx)
                             (m !!! Regidx s5_idx)).
    { cbn [uv_btaken]. rewrite Ha5 Hs5.
      rewrite (moi_neq_vec (bv_unsigned (f k)) 99 (Hbr k)
                 ltac:(unfold Z64; lia)).
      symmetry. apply negb_true_iff. apply Z.eqb_neq. exact Hnck. }
    iApply (wp_uk_btype N h m (mword_of_int 0x956)
              (mword_of_int 8114 : mword 13) s5_idx a5_idx BNE true
              (mword_of_int 0x908) (16 + (UkSh.ush_Dbody + n))
              Htk7a
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(intros _; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_956 with "Hcode"). }
    iIntros (h1) "Hrun".
    iApply (wp_kshf_fork_at Lp Dc h1 m f k len ws sz l n
              HDc Hregs Hs1 Hnn Hnul Hkl Hline
              Hszlo Hszal Hszok Hpm1 Hpmwb
              with "Hgen Hhead Hcode Hro Hjt Hkl Hchl Hplaw [%] Hstd Hdat
                    Hsz Hbuf Hrun").
    exact Hfd0.
  Qed.

  (* ===================================================================== *)
  (* §5 THE JOIN: main's body IS [UkSh.ush_rest], modulo LEXABILITY.        *)
  (*                                                                        *)
  (* [wp_kshm_body] is stated at 0x956 with the line spelled out -- where   *)
  (* it ends, that the lexer accepts it, and how it tokenises.  [ush_rest]  *)
  (* is stated with almost none of that: the command loop knows only that   *)
  (* SOME byte at or after [k] is NUL, because that is what its own scan    *)
  (* established.  Two of the three gaps close on the spot; the third does  *)
  (* not, and is the whole of what is left.                                 *)
  (*                                                                        *)
  (*   WHERE THE LINE ENDS is derivable: [ushf_first_nul] walks from [k] to *)
  (*     the witness and returns the FIRST NUL, which is exactly the        *)
  (*     [len] the body asks for, with [k + len <= i2 < sh_nbuf].           *)
  (*   THE RESOURCES are the re-cut's [R], instantiated at                  *)
  (*     [UkShLoop.ushl_R]; [ushl_head_of_R] uncurries it into the head the *)
  (*     body wants.                                                        *)
  (*   THAT THE LEXER ACCEPTS THE LINE is NOT derivable and never will be   *)
  (*     from inside the loop -- the user may type a symbol byte or eleven  *)
  (*     words.  It is [ushf_lexable] below, and closing it is stage 5's    *)
  (*     [ush_simple] work: a line with a symbol byte does not reach        *)
  (*     [wp_kshp_parser] at all, and [runcmd]'s REDIRECT and PIPE arms --  *)
  (*     the two that MOVE THE DESCRIPTOR TABLE -- are what a real          *)
  (*     [ush_simple] has to refute.                                        *)
  (* ===================================================================== *)

  (* the FIRST NUL at or after [k], out of any NUL at or after [k] *)
  Local Lemma ushf_first_nul_aux (f : nat -> bv 8) (d : nat) :
    forall k : nat, f (k + d)%nat = ubyte0 ->
      exists len : nat, (len <= d)%nat /\
        (forall j : nat, (j < len)%nat -> f (k + j)%nat <> ubyte0) /\
        f (k + len)%nat = ubyte0.
  Proof using .
    induction d as [| d IH]; intros k Hd.
    - exists 0%nat. split; [ lia | ].
      split; [ intros j Hj; lia | exact Hd ].
    - destruct (decide (f k = ubyte0)) as [H0 | H0].
      + exists 0%nat. split; [ lia | ].
        split; [ intros j Hj; lia | ].
        rewrite Nat.add_0_r. exact H0.
      + destruct (IH (S k)) as (len & Hle & Hnn & Hnul).
        { replace (S k + d)%nat with (k + S d)%nat by lia. exact Hd. }
        exists (S len). split; [ lia | ]. split.
        * intros j Hj. destruct j as [| j'].
          { rewrite Nat.add_0_r. exact H0. }
          { replace (k + S j')%nat with (S k + j')%nat by lia.
            apply Hnn. lia. }
        * replace (k + S len)%nat with (S k + len)%nat by lia. exact Hnul.
  Qed.

  Lemma ushf_first_nul (f : nat -> bv 8) (k i2 : nat) :
    (k <= i2)%nat -> f i2 = ubyte0 ->
    exists len : nat, (k + len <= i2)%nat /\
      (forall j : nat, (j < len)%nat -> f (k + j)%nat <> ubyte0) /\
      f (k + len)%nat = ubyte0.
  Proof using .
    intros Hk Hi2.
    destruct (ushf_first_nul_aux f (i2 - k)%nat k
                ltac:(replace (k + (i2 - k))%nat with i2 by lia; exact Hi2))
      as (len & Hle & Hnn & Hnul).
    exists len. split; [ lia | exact (conj Hnn Hnul) ].
  Qed.

  (* [ushf_lexable] IS GONE (lane SH-LINE 2b, L3).  It said "every line the
     user could type lexes", quantified over an arbitrary [f] and [k]
     because that is how the loop hands the buffer over -- and it is FALSE:
     the user may type a symbol byte or eleven words.  What stands in its
     place is two things that are both true.  The LINE FACT
     ([UkSh.ush_rest_line], a premise of [UkSh.ush_rest_l] below) says the
     line the read's receipt delivered is [wl_line ws] for an ADMISSIBLE
     word list, or else the application is tainted; and
     [UkShLoop.ush_line_lexable] -- owed by E4 at every admissible line --
     says such a line lexes into fewer than ten tokens with no symbol
     byte.  Under the taint the walk does not continue in sh's code at all
     ([UkSh.ush_gen_run]). *)

  (* ===================================================================== *)
  (* THE BODY, AS A LAW OVER THE LINES AN ERA ADMITS (lane SH-CHILD).       *)
  (*                                                                        *)
  (* [wp_kshm_body_at] is one line shape; an ERA reads several              *)
  (* ([FileDisc.uline] has three constructors and the file application's sh *)
  (* sees all three), and they do NOT share a walk: [echo ... ] and         *)
  (* [echo ... > f] do -- both begin with 'e', so both take the [bne] at    *)
  (* 0x956 -- while [cat f] begins with 'c' and falls into the three-byte   *)
  (* [cd] test instead.  So what [ushf_rest_of_body_at] takes is the walk   *)
  (* PER ADMITTED CONSTRUCTOR, as one law, and each era assembles it out of *)
  (* the walks its lines need.                                              *)
  (* ===================================================================== *)
  Definition ushf_body_law (D : FileDisc.uline -> Prop) (sz : Z) : iProp Σ :=
    (□ (∀ (lu : FileDisc.uline) (h : CpuId) (m : regfile) (f : nat -> bv 8)
          (k len : nat) (l : list fdstate) (n : nat),
          ⌜ D lu ⌝ -∗
          ⌜ UkSh.ush_line_at lu f k len ⌝ -∗
          ⌜ UkSh.ush_regs m ⌝ -∗
          ⌜ m !!! Regidx s1_idx = mword_of_int (sh_buf + Z.of_nat k) ⌝ -∗
          ⌜ m !!! Regidx a5_idx = mword_of_int (bv_unsigned (f k)) ⌝ -∗
          ⌜ forall j : nat, (j < len)%nat -> f (k + j)%nat <> ubyte0 ⌝ -∗
          ⌜ f (k + len)%nat = ubyte0 ⌝ -∗
          ⌜ (k + len < sh_nbuf)%nat ⌝ -∗
          ⌜ forall n' : nat,
              ⊢ UkSh.ush_at N γp n' -∗
                ∃ I : list (bv 8),
                  ⌜length I = n'⌝ ∗ UkSh.ush_lease N γp T Pm I ⌝ -∗
          ⌜ forall I : list (bv 8),
              ⊢ Pm I -∗ Wb I -∗ UkSh.ush_at N γp (length I) ⌝ -∗
          ⌜ UkSh.ush_fd0p l ⌝ -∗
          UkSh.ush_gen_slot N T -∗
          shk_code γt -∗
          ush_jtab γt -∗
          ushl_head l sz -∗
          ush_bstate l (FileDisc.uline_ws lu) -∗
          ushl_dat -∗ usz γs sz -∗
          ubytes γd sh_buf sh_nbuf f -∗
          urun N h m (mword_of_int 0x956) (16 + (UkSh.ush_Dbody + n)) -∗
          mWP (Loop : expr riscv_lang)))%I.

  Global Instance ushf_body_law_persistent D sz :
    Persistent (ushf_body_law D sz).
  Proof using .
    rewrite /ushf_body_law. apply bi.intuitionistically_persistent.
  Qed.

  (* the reading of the line every body walk makes, at echo's shape *)
  Lemma ushf_lp0_echo (ws : list (list (bv 8))) (g : nat -> bv 8)
      (k len : nat) :
    UkSh.ush_line_is ws g k len -> bv_unsigned (g k) = 101%Z.
  Proof using .
    intros (Hok & Hlen & Hby).
    pose proof (wl_line_pos ws) as HL.
    pose proof (Hby 0%nat ltac:(lia)) as H0.
    rewrite Nat.add_0_r in H0. rewrite H0.
    exact (line_ok_head_byte0 ws Hok).
  Qed.

  (* ...AND THE ECHO ERA'S LAW: one constructor, one walk.  This is what
     [UShRest] hands the discharger, and it is where [ushf_child_law] --
     the ECHO child -- is spent. *)
  Lemma ushf_body_law_echo (sz : Z) :
    8344 <= sz ->
    UserPtTree.pgroundup sz = sz ->
    usz_ok (sz + 65536) ->
    ushf_kill_law -∗
    ushf_child_law -∗
    UkShDiag.ush_panic_law Wc Wb -∗
    ushf_body_law UkSh.ush_line_echo sz.
  Proof using HT HWct Hpay Hpsok_free.
    intros Hszlo Hszal Hszok.
    iIntros "#Hkl #Hchl #Hplaw !>" (lu h m f k len l n)
      "%Hd %Hlat %Hregs %Hs1 %Ha5 %Hnn %Hnul %Hkl2 %Hpm1 %Hpmwb %Hfd0
       #Hgen #Hcode #Hjt Hhead Hstd Hdat Hsz Hbuf Hrun".
    destruct Hd as [ ws -> ].
    iDestruct (ush_jtab_ro γt with "Hjt") as "#Hro".
    iApply (wp_kshm_body_at UkSh.ush_line_is 60 h m f k len ws sz l n
              ltac:(lia) ushf_lp0_echo Hregs Hs1 Ha5 Hnn Hnul Hkl2 Hlat
              Hszlo Hszal Hszok Hpm1 Hpmwb
              with "Hgen Hhead Hcode Hro [] Hjt Hkl Hchl Hplaw [%] Hstd
                    Hdat Hsz Hbuf Hrun").
    - iApply (ushf_code_shp with "Hcode").
    - exact Hfd0.
  Qed.

  Lemma ushf_rest_of_body_at
      (D : FileDisc.uline -> Prop) (sz : Z) :
    (* the break, as [exec] leaves it *)
    8344 <= sz ->
    UserPtTree.pgroundup sz = sz ->
    usz_ok (sz + 65536) ->
    (* THE PAYLOAD'S OWN ASSEMBLER AND THE TAINT'S CONTINUATION ARE NOT
       PREMISES HERE ANY MORE (lane R3): both are facts about the RECORD
       the kernel minted -- the assembler is guarded by [ukn_pay N], the
       generic slot IS [ukn_pay N] at an arbitrary key -- so they come out
       of the obligation's own box below, exactly as sh's text, its jump
       table and the constancy of its payload do.  THE FREE WRITE LAW AND
       THE EXEC SUPPLY ARE GONE with the fork's taint arm. *)
    (* ...AND THE BODY, PER LINE THE ERA ADMITS (lane SH-CHILD).  The two
       child laws and sh's panic are inside it now -- which is what lets
       one era spend [ushf_child_law] and another spend that AND the
       redirect child's AND cat's. *)
    ushf_body_law D sz -∗
    UkSh.ush_rest_l_at N γp T Wc Wb Pm D (UkShLoop.ushl_R N sz).
  Proof using HT HWct Hpay Hpsok_free.
    intros Hszlo Hszal Hszok.
    iIntros "#Hbody".
    (* THE RECORD'S OWN THREE COME OUT OF THE OBLIGATION now (lane SH-LINE
       2b, (b)): sh's text, its jump table and the constancy of its exit
       payload are facts about the record the KERNEL minted, so the entry
       pays them and the discharger no longer takes them as premises --
       which is what makes [UInitSh.sh_pay_rest], a [∀] over every record,
       provable at all.  [.rodata] rides in with the table. *)
    iModIntro. iIntros (l) "%Hc %Hpm1 %Hpmwb #Hcode #Hjt #Hgen Hhead".
    iDestruct (ush_jtab_ro γt with "Hjt") as "#Hro".
    iIntros (h m f k i2 n ws)
      "%Hregs %Hs1 %Ha5 %Hi2 %Hfd0 Hline Hstd [Hdat Hsz] Hbuf Hrun".
    destruct Hi2 as [[Hki2 Hi2n] Hnul2].
    destruct (ushf_first_nul f k i2 Hki2 Hnul2) as (len & Hle & Hnn & Hnul).
    (* THE LINE, OR THE TAINT *)
    iEval (rewrite /UkSh.ush_rest_line_at) in "Hline".
    iDestruct "Hline" as "[Hl | HT]"; last first.
    { assert (Halo : is_aligned_vaddr
                       (Virtaddr (mword_of_int 0x956 : mword 64)) 2 = true)
        by (vm_compute; reflexivity).
      iApply (UkSh.ush_gen_run N T h m (mword_of_int 0x956)
                (16 + (UkSh.ush_Dbody + n)) Halo with "Hgen HT Hrun"). }
    iDestruct ("Hl" $! len with "[%] [%]") as %Hline;
      [ exact Hnn | exact Hnul | ].
    destruct Hline as (lu & Hd & Hws & Hlat). subst ws.
    iApply ("Hbody" $! lu h m f k len l n with
              "[%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] Hgen Hcode Hjt
               [Hhead] Hstd Hdat Hsz Hbuf Hrun");
      [ exact Hd | exact Hlat | exact Hregs | exact Hs1 | exact Ha5
      | exact Hnn | exact Hnul | lia | exact Hpm1 | exact Hpmwb
      | exact Hfd0 | ].
    iApply (UkShLoop.ushl_head_of_R N γp with "Hhead").
  Qed.

  (* ...AND THE LANDED DISCHARGER: the echo era's, at its one constructor.
     [UkShLoop.ush_line_lexable] is NOT a premise any more -- see
     [wp_kshf_fork_at]'s header: nothing on this walk ever read it. *)
  Lemma ushf_rest_of_body
      (sz : Z) :
    8344 <= sz ->
    UserPtTree.pgroundup sz = sz ->
    usz_ok (sz + 65536) ->
    ushf_kill_law -∗
    ushf_child_law -∗
    UkShDiag.ush_panic_law Wc Wb -∗
    UkSh.ush_rest_l N γp T Wc Wb Pm (UkShLoop.ushl_R N sz).
  Proof using HT HWct Hpay Hpsok_free.
    intros Hszlo Hszal Hszok.
    iIntros "#Hkl #Hchl #Hplaw".
    rewrite /UkSh.ush_rest_l.
    iApply (ushf_rest_of_body_at UkSh.ush_line_echo sz
              Hszlo Hszal Hszok).
    iApply (ushf_body_law_echo sz Hszlo Hszal Hszok
              with "Hkl Hchl Hplaw").
  Qed.

End UkShFork.
