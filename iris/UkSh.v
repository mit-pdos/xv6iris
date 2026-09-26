(* ===================================================================== *)
(* UkSh.v -- the `sh` user program on the urun engine, SH LANE STAGES 1-2: *)
(* the ELF entry, main's prologue, main's CONSOLE PREAMBLE, and the        *)
(* COMMAND LOOP down to the blank-line test -- getcmd, memset, gets, the   *)
(* read window, and the leading-blank scan.                                *)
(*                                                                        *)
(* Ten functions' worth of pcs: start, main, getcmd, memset, gets, and the *)
(* five syscall stubs those issue (open, close, exit, write, read).  The   *)
(* catalog is UCodeShK.v -- one of three over the same dump, emitted at    *)
(* [--prog shk] so that it, UCodeShM.v ([--prog shm]) and UCodeShP.v       *)
(* ([--prog shp]) define disjoint names.  tools/ucode_shk.txt is its pc    *)
(* set; `make gen-ucode` regenerates it.                                   *)
(*                                                                        *)
(* WHAT THE TWO STAGES ESTABLISH.                                          *)
(*                                                                        *)
(* (1) THE QUIET ROW, ONCE.  open (15), close (21), exit (2) and write     *)
(* (16) are all outside the eight numbers [UsysMemOk.usys_mem_ok] gives a  *)
(* window to, so the kernel writes no user byte and the heap crosses the   *)
(* trap untouched.  [wp_ksh_qstub] is that fact once, for the whole        *)
(* two-instruction-and-a-return stub shape of usys.S; open, close and      *)
(* write are instances, and stage 5's chdir and dup will be two more.      *)
(*                                                                        *)
(* (2) THE WINDOW ROW, ONCE, AND AS A HYPOTHESIS.  [read] (5) IS in the    *)
(* window table, and the consumer leaf for the general window --           *)
(* [UkRunSys.wp_uk_ecall_window] -- has since landed; this file still takes *)
(* the row as a Hypothesis, because read is a CLAIM number (its console arm *)
(* spends the supply) and what a verified sh may take is a DEPOSIT, not the *)
(* program-generic supplier.  Its                                          *)
(* statement is the file's one Hypothesis, [ush_read_leaf], spelled at the *)
(* idiom of the landed [UkRunSys.wp_uk_ecall_wait_null].  Every lemma that *)
(* depends on it SAYS SO in its own header and carries it as an explicit   *)
(* argument once the section closes: [wp_ksh_read], [wp_ksh_gets],         *)
(* [wp_ksh_getcmd], [wp_ksh_cmd_head], [wp_ksh_console], [wp_ksh_main],    *)
(* [wp_ksh_start].  Everything else here -- the byte-run algebra, the      *)
(* quiet stubs, exit, memset, and the blank scan -- is unconditional.      *)
(*                                                                        *)
(* (3) TWO UNBOUNDED LOOPS, WITH VERY DIFFERENT INVARIANTS.  The console   *)
(* preamble                                                                *)
(*                                                                        *)
(*   while ((fd = open("console", O_RDWR)) >= 0)                           *)
(*     if (fd >= 3) { close(fd); break; }                                  *)
(*                                                                        *)
(* carries NOTHING round its cycle: its branch conditions are case split   *)
(* on the abstract [uv_btaken …] boolean, so the walk never learns what fd *)
(* the kernel returned and never needs to.  90 lines.  The COMMAND loop    *)
(* carries the buffer -- [ubytes γd sh_buf 100 f] at an existential [f] -- *)
(* and five register constants, [ush_regs].  Both close through            *)
(* [UkRunLeaf.wp_uk_btype_later], which init's loops needed too and which  *)
(* upstream landed beside [wp_uk_btype]; UkRunBr.v is now down to the ONE  *)
(* leaf UkRunLeaf still has no twin for, the x0 branch [wp_uk_btype0].     *)
(*                                                                        *)
(* (4) ONE FACT ABOUT MEMORY DECIDES CONTROL FLOW, and only one.  main's   *)
(* leading-blank scan has no bound in the code; what bounds it is gets'    *)
(* postcondition -- a NUL below the buffer's size -- because 0 is neither  *)
(* a space nor a tab.  Everything else that branches is either computed    *)
(* from a register the walk set itself or case split abstractly.           *)
(*                                                                        *)
(* (5) THE STANDARD-STREAM LEDGER IS A PARAMETER: sh is verified at ANY   *)
(* ledger and assumes nothing about which of its three streams are open.   *)
(* [ush_std] is the ledger of the low NSTD slots at an arbitrary state      *)
(* vector, and it travels inside [ush_pstate] -- sh's process state, the    *)
(* ledger together with its working directory and its children set -- from  *)
(* [wp_ksh_start] through main, the console preamble and the command loop,  *)
(* and out through [ush_rest_l] to where runcmd's REDIR and PIPE arms close   *)
(* and reopen standard streams, the [cd] builtin spends the cwd and fork1   *)
(* moves the children set.  See [ush_std]'s own header for what the ledger  *)
(* buys, and [ush_pstate]'s for why the three travel as one resource.       *)
(*                                                                        *)
(* WHERE THE STAGE STOPS.  0x97a, the first instruction of main's body     *)
(* past the blank-line test, is [ush_rest_l]: an abstract continuation that  *)
(* TAKES THE LOOP HEAD as its own premise, because the rest of main's body *)
(* (the cd builtin at 0x98e, fork1/parsecmd/runcmd at 0x92c) ends by       *)
(* falling back into 0x938.  The two are mutually recursive and the honest *)
(* cut is a premise that says so; stages 4-5 discharge it.                 *)
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
Require Import WpMmodeLeafBase.
Require Import UserBits.
Require Import WpUmodeBranch.
Require Import UmodeArith UmodeAbi.
Require Import UsysMemOk.
Require Import UkStep.
Require Import UserHeap UkRun UkRunLeaf UkRunMem UkRunSys UkRunBr.
Require Import UCodeShK.
Require Import CtxIdDefs.
Require User.ShSyms User.ShInstrs.
Require Import ChildTok.  (* [genF] -- the capacity the slot's fork arms name *)
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* THE LINE BUFFER.  [buf.0] is 100 bytes of .bss at 0x2020 -- the ONE     *)
(* object the command loop owns, and the only thing its invariant carries  *)
(* besides the free stack.  main loads its address with the [auipc s2,0x1  *)
(* ; addi s2,s2,1800] pair at 0x918, and hands it to [getcmd] with the     *)
(* size in a1.                                                            *)
(* ===================================================================== *)
Definition sh_buf : Z := 0x2020.
Definition sh_nbuf : nat := 100.

(* one index of a byte-run's contents overwritten -- what a [sb] does to
   the function a [ubytes] is indexed by *)
Definition ush_set (f : nat -> bv 8) (j : nat) (b : bv 8) : nat -> bv 8 :=
  fun i => if Nat.eqb i j then b else f i.

Lemma ush_set_lt (f : nat -> bv 8) (i j : nat) (b : bv 8) :
  (j < i)%nat -> ush_set f i b j = f j.
Proof.
  intro H. unfold ush_set.
  destruct (Nat.eqb_spec j i) as [-> | Hne]; [ exfalso; lia | reflexivity ].
Qed.

Lemma ush_set_at (f : nat -> bv 8) (i : nat) (b : bv 8) :
  ush_set f i b i = b.
Proof. unfold ush_set. rewrite Nat.eqb_refl. reflexivity. Qed.

Require Import VcGen.
Require Import RiscvExtras.
Require Import FdSlots.   (* [fdstate] -- what a handle names *)
Require Import UserFd.   (* [ufd_auth] -- the PROGRAM's own view of
                            its descriptor table, the authority for
                            which rides inside [urun] *)
Require Import ProcGeom.  (* [NOFILE] -- how many slots a table has *)
Require Import UserCwd.  (* [ucwd_any] -- sh's own working directory, which
                            its [cd] builtin spends *)
Require Import UserChildren.  (* [uch_any] -- sh's own half of its children
                                 set, which its fork1 spends *)
Require Import UexecSG.   (* [uexecSG] / [uprogSG]: the ARM deposit class *)
Require Import Xv6Cameras.   (* [uartGhostG] -- the console ring's cameras,
                                at the narrow class a program binds *)
Require Import ConsoleInv.   (* [CONSOLE] -- the major fd 0's arm is keyed by *)
Require Import LineWords.    (* [wl_line] / [wl_words] / the cut: a line IS a
                                list of words, and an input parses into the
                                lines it closed and the one it is in *)
Require Import EchoDisc.     (* [line_ok] / [disc_input] / [disc] -- WHICH
                                lines the discipline admits, and the
                                discipline the input tag is read as (lane
                                SH-LINE 2b).
                                A PURE file: no ghost class comes with it. *)
Require Import FileDisc.     (* [uline] -- the line the loop read, TYPED: the
                                three constructors of the file discipline,
                                of which the echo era admits one (lane
                                SH-CHILD).  PURE, like [EchoDisc]. *)
Require Import UserConsole.  (* [upos] -- sh's half of the console position
                                pair (app-echo.md, "SH-LINE RULING") *)
Require Import ObsTrace.     (* [mobs] -- what a tag's history is made of, and
                                what the read's receipt hands back per byte *)
(* lane SH-OPEN: the console preamble's PINNED open.  [uvis] / [uslot] are
   what the TAINT arm of the preamble hands the run to
   ([UkRun.urun_gen]); [FsImg.ROOTINO] is the directory the pin resolves
   "console" from, which is sh's own working directory at its entry. *)
Require Import UexecSlot UexecRet.
Require Import UserPerm.    (* [perm_of] / [lazy_free] -- the text row's reading *)
Require Import ProcPtOwn.   (* [proc_pt_wf] *)
Require Import UserPtTree.  (* [uva_rmapped] -- what refutes the short write *)
Require FsImg.

(* ===================================================================== *)
(* THE ROW SH'S ENTRY IS TOLD, AS A PURE PROPOSITION (lane SH-OPEN).      *)
(*                                                                        *)
(* [ush_fd0] below is this or the taint.  It is spelled out here, OUTSIDE *)
(* the section and free of the taint, because it is what the COMMAND LOOP *)
(* carries: a program that has learned the taint does not run its own     *)
(* code any more ([ush_gen_slot]), so nothing below the preamble needs a  *)
(* taint arm on this row -- and a pure row keeps [ush_loop_head] and      *)
(* [ush_rest_l] at the arity every file that discharges them already uses.  *)
(* ===================================================================== *)
(* THE BASE OF SH'S OWN "console" LITERAL, NAMED ONCE (lane SH-OPEN, ruling
   (D)).  0x8f8's [auipc s2,0x1] and 0x8fc's [addi s2,s2,-1392] compute it
   into s2, 0x902's [c.mv a0,s2] passes it, and the eight bytes there are
   "console\0" ([user-rocq/ShData.v], .rodata 0x1288..0x13e9, inside
   [UCodeShK.shk_ro] since 0x1388 < 0x2000).  /init's twin is 0x980. *)
Definition sh_cons_pv : Z := 0x1388.

Definition ush_fd0p (l : list fdstate) : Prop :=
  (exists wr : bool, l !! 0%nat = Some (FdOpen true wr (FdDevice CONSOLE)))
  \/ l !! 0%nat = Some FdClosed.

(* ...AND THE TWO ARMS APART (lane IO-LEAF, M5(3)).  A read's answer says
   WHICH of them it was answered at -- a delivered window is the console
   arm's and a [-1] is the shut arm's ([ush_read_ans] below) -- and that is
   what lets [gets] know that a line it has begun cannot stop in the
   middle: the [-1] that would stop it is the shut fd's, and a shut fd
   delivers no first byte. *)
Definition ush_fd0c (l : list fdstate) : Prop :=
  exists wr : bool, l !! 0%nat = Some (FdOpen true wr (FdDevice CONSOLE)).

Lemma ush_fd0c_not_closed (l : list fdstate) :
  ush_fd0c l -> l !! 0%nat = Some FdClosed -> False.
Proof.
  intros [wr Hc] Hcl. rewrite Hc in Hcl. discriminate Hcl.
Qed.

(* ...and the console preamble's opens preserve it, at either of the two
   ways an open can land: on slot 0 itself, where what it installs IS the
   console device, or anywhere else, where the row is untouched
   ([ush_fd2p_cons] is the twin). *)
Lemma ush_fd0c_cons (l : list fdstate) (k : nat) :
  length l = NSTD ->
  ush_fd0c l ->
  ush_fd0c (<[k := FdOpen true true (FdDevice CONSOLE)]> l).
Proof.
  intros Hlen [wr Hc].
  destruct (decide (k = 0%nat)) as [-> | Hne].
  - exists true.
    rewrite list_lookup_insert;
      [ reflexivity | rewrite Hlen; unfold NSTD; lia ].
  - exists wr. rewrite list_lookup_insert_ne; [ exact Hc | exact Hne ].
Qed.

(* THE SCAN LANDS ON SLOT 0 EXACTLY WHEN SLOT 0 IS CLOSED, so the row is a
   LOOP INVARIANT of sh's console preamble: every open the preamble makes
   lands at [fd_lowest_closed] of the ledger it was called at
   ([UserFd.ualloc_at]), and what the pinned open installs there is the
   console device. *)
Lemma ush_fd0p_scan (l : list fdstate) (k : nat) :
  l !! 0%nat = Some FdClosed -> fd_lowest_closed l = Some k -> k = 0%nat.
Proof.
  intros H0 Hk.
  destruct k as [| k']; [ reflexivity | exfalso ].
  exact (fd_lowest_closed_below l (S k') Hk 0%nat ltac:(lia) H0).
Qed.

Lemma ush_fd0p_cons (l : list fdstate) (k : nat) :
  length l = NSTD ->
  fd_lowest_closed l = Some k ->
  ush_fd0p l ->
  ush_fd0p (<[k := FdOpen true true (FdDevice CONSOLE)]> l).
Proof.
  intros Hlen Hk [[wr Hc] | Hcl].
  - (* slot 0 is the console already, so it is not the slot the scan found *)
    left. exists wr.
    assert (Hne : k <> 0%nat).
    { intro Hz. subst k.
      rewrite (fd_lowest_closed_is_closed l 0%nat Hk) in Hc. discriminate Hc. }
    rewrite list_lookup_insert_ne; [ exact Hc | exact Hne ].
  - (* slot 0 is closed, so it IS the slot the scan found *)
    rewrite (ush_fd0p_scan l k Hcl Hk).
    left. exists true.
    rewrite list_lookup_insert;
      [ reflexivity | rewrite Hlen; unfold NSTD; lia ].
Qed.

(* ===================================================================== *)
(* THE PROMPT'S SOURCE RUN AND THE ROW ITS PAYMENT ASKS FOR               *)
(* (lane IO-LEAF, M4a).                                                   *)
(*                                                                        *)
(* getcmd's [write(2, "$ ", 2)] at 0x10..0x1c takes its buffer out of sh's *)
(* OWN .rodata: 0x12's [auipc a1,0x1] and 0x16's [addi a1,a1,638] compute  *)
(* 0x1290, and the two bytes there are "$ " ([UCodeShK.shk_ro]).  The      *)
(* address is named here because the walk needs it in a REGISTER fact and  *)
(* the payment ([UShOut.ksh_w_of_link_prompt]) needs it in a statement.    *)
(* ===================================================================== *)
Definition sh_prompt_pv : Z := 0x1290.

(* ...AND THE ROW: sh's fd 2 IS the console.  PURE, for [ush_fd0p]'s       *)
(* reason -- it is what the command loop carries -- and preserved by the   *)
(* console preamble's own opens ([ush_fd2p_cons]), which is what lets the  *)
(* prompt's payment enter at sh's ENTRY ledger and still be spendable at   *)
(* the ledger the preamble left.                                          *)
Definition ush_fd2p (l : list fdstate) : Prop :=
  exists rb : bool, l !! 2%nat = Some (FdOpen rb true (FdDevice CONSOLE)).

(* THE PREAMBLE PRESERVES IT, at either of the two ways an open can land:
   on slot 2 itself, where what it installs IS the console device, or
   anywhere else, where the row is untouched.  (Unlike [ush_fd0p_cons]
   this needs nothing about the scan: both cases go through.) *)
Lemma ush_fd2p_cons (l : list fdstate) (k : nat) :
  length l = NSTD ->
  ush_fd2p l ->
  ush_fd2p (<[k := FdOpen true true (FdDevice CONSOLE)]> l).
Proof.
  intros Hlen [rb Hc].
  destruct (decide (k = 2%nat)) as [-> | Hne].
  - exists true.
    rewrite list_lookup_insert;
      [ reflexivity | rewrite Hlen; unfold NSTD; lia ].
  - exists rb. rewrite list_lookup_insert_ne; [ exact Hc | exact Hne ].
Qed.

(* ...AND SH'S fd 1 IS THE CONSOLE, WRITABLE (lane IO-LEAF, step 4): the
   row the FORKED CHILD's echo writes on ([UEchoOut.echo_uexec_slot_at]
   asks it of the child's table, which is its parent's).  Carried in the
   credential slot's console arm beside fd 0's and fd 2's rows, from
   /init's pinned table, and preserved by the preamble's opens. *)
Definition ush_fd1p (l : list fdstate) : Prop :=
  exists rb : bool, l !! 1%nat = Some (FdOpen rb true (FdDevice CONSOLE)).

Lemma ush_fd1p_cons (l : list fdstate) (k : nat) :
  length l = NSTD ->
  ush_fd1p l ->
  ush_fd1p (<[k := FdOpen true true (FdDevice CONSOLE)]> l).
Proof.
  intros Hlen [rb Hc].
  destruct (decide (k = 1%nat)) as [-> | Hne].
  - exists true.
    rewrite list_lookup_insert;
      [ reflexivity | rewrite Hlen; unfold NSTD; lia ].
  - exists rb. rewrite list_lookup_insert_ne; [ exact Hc | exact Hne ].
Qed.

(* THE LEDGER A SHELL WITH A CLOSED fd 2 IS AT (lane IO-LEAF, step 4):
   /init's all-closed table with the console preamble's first [j] opens
   landed -- slots below [j] are the console, slots from [j] on are
   closed.  The credential slot's closed arm carries this shape rather
   than the bare "slot 2 is closed", because the preamble's open onto
   slot 2 turns the banner-owed credential into the prompt's ([ush_wb_wc])
   and the console arm it lands on needs all three rows. *)
Definition ush_lcl (l : list fdstate) (j : nat) : Prop :=
  (forall i : nat, (i < j)%nat ->
     l !! i = Some (FdOpen true true (FdDevice CONSOLE)))
  /\ (forall i : nat, (j <= i < NSTD)%nat -> l !! i = Some FdClosed).

Lemma ush_lcl_2 (l : list fdstate) (j : nat) :
  (j <= 2)%nat -> ush_lcl l j -> l !! 2%nat = Some FdClosed.
Proof. intros Hj [_ Hcl]. apply Hcl. unfold NSTD. lia. Qed.

(* the preamble's open lands at the lowest closed slot, which is [j] *)
Lemma ush_lcl_lowest (l : list fdstate) (j k : nat) :
  (j < NSTD)%nat -> ush_lcl l j -> fd_lowest_closed l = Some k -> k = j.
Proof.
  intros Hj [Hop Hcl] Hk.
  pose proof (fd_lowest_closed_is_closed l k Hk) as Hkc.
  pose proof (fd_lowest_closed_below l k Hk) as Hbel.
  destruct (Nat.lt_trichotomy k j) as [Hlt | [Heq | Hgt]].
  - exfalso. rewrite (Hop k Hlt) in Hkc. discriminate Hkc.
  - exact Heq.
  - exfalso. exact (Hbel j Hgt (Hcl j ltac:(lia))).
Qed.

Lemma ush_lcl_cons (l : list fdstate) (j : nat) :
  length l = NSTD ->
  (j < NSTD)%nat ->
  ush_lcl l j ->
  ush_lcl (<[j := FdOpen true true (FdDevice CONSOLE)]> l) (S j).
Proof.
  intros Hlen Hj [Hop Hcl]. split.
  - intros i Hi. destruct (decide (i = j)) as [-> | Hne].
    + rewrite list_lookup_insert; [ reflexivity | rewrite Hlen; exact Hj ].
    + rewrite list_lookup_insert_ne; [ apply Hop; lia | intro H; apply Hne; symmetry; exact H ].
  - intros i Hi. rewrite list_lookup_insert_ne; [ apply Hcl; lia | lia ].
Qed.

(* ...and once the third open has landed, every standard stream is the
   console, writable *)
Lemma ush_lcl_rows (l : list fdstate) :
  ush_lcl l 3%nat -> ush_fd0c l /\ ush_fd1p l /\ ush_fd2p l.
Proof.
  intros [Hop _]. split_and!.
  - exists true. apply Hop. lia.
  - exists true. apply Hop. lia.
  - exists true. apply Hop. lia.
Qed.

(* ===================================================================== *)
(* WHAT SH'S LINE IS, AS A PURE PROPOSITION (lane SH-LINE 2b, L3).        *)
(*                                                                        *)
(* [UkShFork.ushf_lexable] was "every line the user could type lexes",     *)
(* which is false and was the last thing sh rested on.  What replaces it   *)
(* is this, applied to the ONE line the read's receipt says sh read: the   *)
(* [len] bytes at [k] in the line buffer are those of [wl_line ws] for an  *)
(* ADMISSIBLE word list [ws] ([EchoDisc.line_ok]), in order, and there are *)
(* exactly [length (wl_line ws)] of them.                                  *)
(*                                                                        *)
(* IT CARRIES ITS WORD LIST (project echo-any-line): the line is a line    *)
(* per round now, so "which line" is data the fork's child law, the        *)
(* lexer's tokens and echo's argv all read off this proposition -- and     *)
(* [wl_line_inj] makes it unique, so no two readings of one buffer can     *)
(* disagree about the words.                                               *)
(*                                                                        *)
(* PURE AND OUTSIDE THE SECTION for [ush_fd0p]'s reason: the command loop  *)
(* carries it, no resource does, and the file that turns it into           *)
(* "the lexer accepts this line" ([UkShLoop.ush_line_lexable]) is above    *)
(* this one.                                                              *)
(* ===================================================================== *)
Definition ush_line_is (ws : list (list (bv 8))) (f : nat -> bv 8)
    (k len : nat) : Prop :=
  line_ok ws
  /\ len = length (wl_line ws)
  /\ forall j : nat, (j < len)%nat -> f (k + j)%nat = wl_line ws !!! j.

(* THE TWO CONSTANTS MEET HERE: the buffer [getcmd] reads into is exactly
   as long as the longest line the discipline admits, which is what makes
   "the line fits the buffer" a fact about [EchoDisc.line_max] and not a
   side condition on this walk. *)
Lemma sh_nbuf_line_max : sh_nbuf = EchoDisc.line_max.
Proof. reflexivity. Qed.

(* THE BYTES A LINE CANNOT CARRY, at any line (lane IO-LEAF, M5(3)).
   [gets] breaks on '\n' and on '\r', main's scan stops at the NUL [gets]
   plants past the line, and the console's erase and end-of-file bytes have
   to be refuted wherever a receipt delivers one.  All of them come off
   [LineWords.wl_line_byte_val] by [lia]; a literal line used to answer
   each by case analysis over seventeen bytes.

   [EchoDisc.line_ok_head_byte0] is NOT one of them and stays: it is the
   COMMAND NAME's first byte, which is 'e' whatever the arguments are,
   because the line the discipline admits runs /echo. *)
Lemma ush_line_byte_val (ws : list (list (bv 8))) (j : nat) :
  wl_wf ws -> (j < length (wl_line ws))%nat ->
  bv_unsigned (wl_line ws !!! j) = 10%Z
  \/ bv_unsigned (wl_line ws !!! j) = 32%Z
  \/ (48 <= bv_unsigned (wl_line ws !!! j) <= 57)%Z
  \/ (65 <= bv_unsigned (wl_line ws !!! j) <= 90)%Z
  \/ (97 <= bv_unsigned (wl_line ws !!! j) <= 122)%Z.
Proof.
  intros Hwf Hj. apply (wl_line_byte_val ws _ Hwf).
  destruct (lookup_lt_is_Some_2 (wl_line ws) j Hj) as [b Hb].
  rewrite list_lookup_total_alt Hb. cbn [default from_option].
  exact (elem_of_list_lookup_2 (wl_line ws) j b Hb).
Qed.

(* ...and no byte of the line is the NUL [gets] plants past it, which is
   what turns "the first NUL at or after 0" into "the line's length" *)
Lemma ush_line_no_nul (ws : list (list (bv 8))) (j : nat) :
  fn_wf ws -> (j < length (wl_line ws))%nat -> wl_line ws !!! j <> ubyte0.
Proof.
  intros Hwf Hj Hc.
  assert (Hv : bv_unsigned (wl_line ws !!! j) = 10%Z \/ bv_unsigned (wl_line ws !!! j) = 32%Z
               \/ bv_unsigned (wl_line ws !!! j) = 46%Z
               \/ (48 <= bv_unsigned (wl_line ws !!! j) <= 57)%Z
               \/ (65 <= bv_unsigned (wl_line ws !!! j) <= 90)%Z
               \/ (97 <= bv_unsigned (wl_line ws !!! j) <= 122)%Z).
  { apply (wl_line_byte_val_fn ws _ Hwf).
    destruct (lookup_lt_is_Some_2 (wl_line ws) j Hj) as [b Hb].
    rewrite list_lookup_total_alt Hb. cbn [default from_option].
    exact (elem_of_list_lookup_2 (wl_line ws) j b Hb). }
  rewrite Hc in Hv.
  rewrite (_ : bv_unsigned ubyte0 = 0%Z) in Hv; [ lia | by vm_compute ].
Qed.

(* ...AND THE LINE IS TYPED (lane SH-CHILD).  The shape the buffer holds
   used to be [ush_line_is ws] -- echo's line and nothing else -- and the
   FILE application's sh reads two more: [echo a b > f] and [cat f].  All
   three are lines of ONE discipline ([FileDisc.uline]), so what the loop
   carries is "the buffer at [k] holds the bytes of an admissible line
   whose words are [ws]", and WHICH constructors an era admits is the
   parameter [D].  [ush_line_is ws] IS this at [l := LEcho ws]
   ([ush_line_at_echo], by conversion), so the echo era's instance
   ([ush_line_echo]) says exactly what the landed premise said. *)
Definition ush_line_at (l : FileDisc.uline) (f : nat -> bv 8)
    (k len : nat) : Prop :=
  FileDisc.uline_ok l
  /\ len = length (FileDisc.line_bytes l)
  /\ (forall j : nat, (j < len)%nat ->
        f (k + j)%nat = FileDisc.line_bytes l !!! j).

Lemma ush_line_at_echo (ws : list (list (bv 8))) (f : nat -> bv 8)
    (k len : nat) :
  ush_line_at (FileDisc.LEcho ws) f k len <-> ush_line_is ws f k len.
Proof using . split; intro H; exact H. Qed.

(* the echo era's shapes: its discipline admits [LEcho] lines alone
   ([EchoDisc.disc]), which is why widening the payload costs the echo
   tier nothing -- its producer supplies this constructor and its
   consumer case-splits on a one-armed case. *)
Definition ush_line_echo (l : FileDisc.uline) : Prop :=
  exists ws : list (list (bv 8)), l = FileDisc.LEcho ws.

(* ===================================================================== *)
(*  WHAT THE LOOP READS OF A LINE, AT ANY CONSTRUCTOR (lane LINK-GEN-6).  *)
(*                                                                       *)
(*  [wp_ksh_loop] makes exactly three readings of the line it just read,  *)
(*  and all three used to go through [EchoDisc.line_ok] -- which demands  *)
(*  [ws !! 0 = Some cmd_echo] and is therefore FALSE at a [cat f] line.   *)
(*  They are facts about [FileDisc.uline_ok] instead, proved here once    *)
(*  for all three constructors, so the loop's line predicate can widen    *)
(*  without the loop gaining a single era-specific premise.               *)
(* ===================================================================== *)

(* (1) a line is never empty: it ends in the newline [gets] stopped at *)
Lemma ush_uline_bytes_pos (lu : FileDisc.uline) :
  (0 < length (FileDisc.line_bytes lu))%nat.
Proof.
  rewrite FileDisc.line_bytes_body length_app. cbn [length]. lia.
Qed.

(* the body's own bytes, at each constructor: the two echo shapes carry
   [EchoDisc.line_ok]'s word list, the cat line is a literal, and the pipe
   line adds the BAR (lane ULINE-LPIPE).  The bar is the one value this
   conclusion gained; the only consumer is [ush_uline_no_nul] just below,
   which reads the disjunction through [lia] and does not move. *)
Lemma ush_uline_body_val (lu : FileDisc.uline) (j : nat) :
  FileDisc.uline_ok lu -> (j < length (FileDisc.line_bytes lu))%nat ->
  bv_unsigned (FileDisc.line_bytes lu !!! j) = 10%Z
  \/ bv_unsigned (FileDisc.line_bytes lu !!! j) = 32%Z
  \/ bv_unsigned (FileDisc.line_bytes lu !!! j) = 62%Z
  \/ bv_unsigned (FileDisc.line_bytes lu !!! j) = 124%Z
  \/ bv_unsigned (FileDisc.line_bytes lu !!! j) = 46%Z
  \/ (48 <= bv_unsigned (FileDisc.line_bytes lu !!! j) <= 57)%Z
  \/ (65 <= bv_unsigned (FileDisc.line_bytes lu !!! j) <= 90)%Z
  \/ (97 <= bv_unsigned (FileDisc.line_bytes lu !!! j) <= 122)%Z.
Proof.
  intros Hok Hj.
  assert (Hin : FileDisc.line_bytes lu !!! j ∈ FileDisc.line_bytes lu).
  { destruct (lookup_lt_is_Some_2 (FileDisc.line_bytes lu) j Hj) as [b Hb].
    rewrite list_lookup_total_alt Hb. cbn [default from_option].
    exact (elem_of_list_lookup_2 _ j b Hb). }
  set (b := FileDisc.line_bytes lu !!! j) in *.
  (* the four-constructor enumeration is [FileDisc.line_bytes_bytes]'s now:
     the twelve lines it replaces were this same case split done here *)
  assert (Hb : FileDisc.fbody_byte b \/ b = FileDisc.fd_bar \/ b = wl_nl).
  { apply elem_of_list_lookup in Hin as [q Hq].
    exact (proj1 (Forall_lookup _ _)
             (FileDisc.line_bytes_bytes lu Hok) q b Hq). }
  destruct Hb as [Hfb | [-> | ->]].
  - destruct Hfb as [[Ha | ->] | [-> | ->]].
    + destruct Ha as [H | [H | H]];
        [ right; right; right; right; right; by left
        | right; right; right; right; right; right; by left
        | right; right; right; right; right; right; by right ].
    + right. left. exact wl_sp_val.
    + right. right. left. by vm_compute.
    + right. right. right. right. left. exact fn_dot_val.
  - right. right. right. left. by vm_compute.
  - left. exact wl_nl_val.
Qed.

(* (2) no byte of a line is the NUL [gets] plants past it *)
Lemma ush_uline_no_nul (lu : FileDisc.uline) (j : nat) :
  FileDisc.uline_ok lu -> (j < length (FileDisc.line_bytes lu))%nat ->
  FileDisc.line_bytes lu !!! j <> ubyte0.
Proof.
  intros Hok Hj Hc.
  pose proof (ush_uline_body_val lu j Hok Hj) as Hv. rewrite Hc in Hv.
  rewrite (_ : bv_unsigned ubyte0 = 0%Z) in Hv; [ lia | by vm_compute ].
Qed.

(* (3) ...AND ITS FIRST BYTE IS NOT A BLANK, which is what refutes the two
   leading-blank arms of the scan.  It is 'e' at either echo shape and 'c'
   at the cat line; what the walk needs is only that it is neither a space
   nor a tab, and THAT is the reading that travels. *)
(* the echo shapes' body is non-empty: it begins with the command name,
   and a body of no bytes would make the line's first byte the newline *)
Lemma ush_wl_body_pos (ws : list (list (bv 8))) :
  line_ok ws -> (0 < length (wl_body ws))%nat.
Proof.
  intro Hok.
  destruct (Nat.eq_dec (length (wl_body ws)) 0%nat) as [Hz | Hn]; [| lia].
  exfalso.
  assert (Hnil : wl_body ws = []) by (apply nil_length_inv; exact Hz).
  pose proof (line_ok_head_byte0 ws Hok) as Hb.
  rewrite /wl_line Hnil in Hb. cbn [app] in Hb.
  rewrite (_ : ([wl_nl] : list (bv 8)) !!! 0%nat = wl_nl) in Hb;
    [| reflexivity ].
  rewrite wl_nl_val in Hb. lia.
Qed.

Lemma ush_uline_head_nonblank (lu : FileDisc.uline) :
  FileDisc.uline_ok lu ->
  bv_unsigned (FileDisc.line_bytes lu !!! 0%nat) <> 9%Z
  /\ bv_unsigned (FileDisc.line_bytes lu !!! 0%nat) <> 32%Z.
Proof.
  intro Hok.
  assert (Hval : bv_unsigned (FileDisc.line_bytes lu !!! 0%nat) = 101%Z
                 \/ bv_unsigned (FileDisc.line_bytes lu !!! 0%nat) = 99%Z
                 \/ bv_unsigned (FileDisc.line_bytes lu !!! 0%nat) = 115%Z).
  { destruct lu as [ws | ws Nf | Nf | ws npc | ws]; cbn [FileDisc.uline_ok] in Hok.
    5: { (* the seccomp line: its head is [seccomp]'s *)
         right; right. rewrite FileDisc.line_bytes_body. cbn [FileDisc.line_body].
         rewrite wl_body_cons. rewrite -!app_assoc.
         rewrite (wl_lta_app_l FileDisc.cmd_seccomp _ 0%nat ltac:(vm_compute; lia)).
         by vm_compute. }
    - left. rewrite FileDisc.line_bytes_echo.
      exact (line_ok_head_byte0 ws Hok).
    - left.
      pose proof (ush_wl_body_pos ws (proj1 Hok)) as Hwb.
      rewrite FileDisc.line_bytes_body. cbn [FileDisc.line_body].
      rewrite (wl_lta_app_l (wl_body ws ++ FileDisc.suf_gt Nf) [wl_nl] 0%nat
                 ltac:(rewrite length_app; lia)).
      rewrite (wl_lta_app_l (wl_body ws) (FileDisc.suf_gt Nf) 0%nat Hwb).
      pose proof (line_ok_head_byte0 ws (proj1 Hok)) as Hh.
      rewrite /wl_line (wl_lta_app_l (wl_body ws) [wl_nl] 0%nat Hwb) in Hh.
      exact Hh.
    - right; left.
      rewrite FileDisc.line_bytes_body. cbn [FileDisc.line_body].
      rewrite (wl_lta_app_l (FileDisc.cmd_cat Nf) [wl_nl] 0%nat
                 ltac:(rewrite FileDisc.cmd_cat_len; lia)).
      rewrite (_ : FileDisc.cmd_cat Nf = FileDisc.fd_w_cat ++ wl_tail [Nf]); [| reflexivity].
      rewrite (wl_lta_app_l FileDisc.fd_w_cat _ 0%nat ltac:(vm_compute; lia)).
      by vm_compute.
    - (* the pipe line: its head is its producer's, one suffix over --
         the echo line's, or [cat]'s *)
      destruct ws as [ws | fn].
      + left.
        pose proof (ush_wl_body_pos ws (proj1 Hok)) as Hwb.
        rewrite FileDisc.line_bytes_body.
        cbn [FileDisc.line_body FileDisc.prod_body FileDisc.prod_words].
        rewrite (wl_lta_app_l (wl_body ws ++ FileDisc.suf_filts npc) [wl_nl] 0%nat
                   ltac:(rewrite length_app; lia)).
        rewrite (wl_lta_app_l (wl_body ws) (FileDisc.suf_filts npc) 0%nat Hwb).
        pose proof (line_ok_head_byte0 ws (proj1 Hok)) as Hh.
        rewrite /wl_line (wl_lta_app_l (wl_body ws) [wl_nl] 0%nat Hwb) in Hh.
        exact Hh.
      + right; left. rewrite FileDisc.line_bytes_body. cbn [FileDisc.line_body].
        rewrite (_ : FileDisc.prod_body (FileDisc.PrCatF fn)
                     = FileDisc.fd_w_cat ++ wl_tail [fn]); [| reflexivity].
        rewrite -!app_assoc.
        rewrite (wl_lta_app_l FileDisc.fd_w_cat _ 0%nat ltac:(vm_compute; lia)).
        by vm_compute. }
  lia.
Qed.

(* ---- the two readings of ONE received byte the walk spends ------------ *)
(* A byte a disciplined input ends in is a body byte or the newline, which
   is the numeric reading every branch of [gets] is decided by: 10 is the
   line's end, 13 cannot happen, 0 cannot happen, and 4 cannot happen. *)
Lemma ush_disc_snoc_val (I : list (bv 8)) (b : bv 8) :
  disc_input (I ++ [b]) ->
  bv_unsigned b = 10%Z \/ bv_unsigned b = 32%Z
  \/ (48 <= bv_unsigned b <= 57)%Z
  \/ (65 <= bv_unsigned b <= 90)%Z
  \/ (97 <= bv_unsigned b <= 122)%Z.
Proof.
  intro Hd. apply (disc_input_byte_val (I ++ [b]) b Hd).
  apply elem_of_app. right. by apply elem_of_list_singleton.
Qed.

(* ...AND THE ONE CONSEQUENCE THE WALK ACTUALLY SPENDS (lane LINK-GEN-5):
   the byte is not a carriage return.  The walk's only use of the value is
   to refute the '\r' branch, so this -- and not the alphanumeric range --
   is what a second era's discipline has to give. *)
Lemma ush_disc_snoc_ncr (I : list (bv 8)) (b : bv 8) :
  disc_input (I ++ [b]) -> bv_unsigned b <> 13%Z.
Proof. intro Hd. pose proof (ush_disc_snoc_val I b Hd). lia. Qed.

(* ...and the two spellings of the newline the branches go between: [gets]
   tests the VALUE and the parser names the BYTE. *)
Lemma ush_nl_of_val (b : bv 8) : bv_unsigned b = 10%Z -> b = wl_nl.
Proof. intro H. apply bv_eq. rewrite wl_nl_val. exact H. Qed.

Lemma ush_nl_ne_of_val (b : bv 8) : bv_unsigned b <> 10%Z -> b <> wl_nl.
Proof. intros H Heq. apply H. rewrite Heq. exact wl_nl_val. Qed.

(* ===================================================================== *)
(*  S4b  THE ^D REFUTATION (lane SH-LINE 2b, L2).                         *)
(*                                                                        *)
(*  [ConsoleInv.cons_swallow]'s [d + 1] arm, once the copy-out fault is    *)
(*  eliminated ([UkRunSys.uk_read_nofault] under the lazy flag), says the  *)
(*  swallowed byte was [C('D')] -- [cons_xlate b] is 4 -- and hands over   *)
(*  its history's input TAG.  [UkSh.ush_tag_law] reads that tag as         *)
(*  [⌜disc h⌝ ∨ T], and this is why the first disjunct is impossible: the  *)
(*  discipline's content half says every byte of the cycle's input is a    *)
(*  body byte or a newline ([EchoDisc.disc_input_byte_val]), and 0x04 is   *)
(*  neither.  So [r = 0] on a read that swallowed a byte is the TAINT, and *)
(*  [gets] takes its taint branch.                                        *)
(* ===================================================================== *)

(* THE CYCLE THE LAST INPUT BYTE IS IN.  [cycles_of] folds the history
   into its power cycles, the open one last; an [ObsUartIn Uart0] event extends
   the most recent cycle (or starts one), so the byte's own cycle is a
   segment whose input ENDS with it.  No [trace_shape] premise: the fold
   does this whether or not the power is on. *)
Lemma ush_elem_of_rev_head {A} (x : A) (l : list A) : x ∈ rev (x :: l).
Proof.
  cbn. apply elem_of_app. right. by apply elem_of_list_singleton.
Qed.

Lemma ush_cycles_snoc_in (h : list mobs) (b : bv 8) :
  exists s0 : list mobs,
    (s0 ++ [ObsUartIn Uart0 b])%list ∈ cycles_of (h ++ [ObsUartIn Uart0 b])%list.
Proof.
  rewrite /cycles_of cycles_rev_app.
  destruct (cycles_rev h) as [| c cs] eqn:Hc.
  - exists []. exact (ush_elem_of_rev_head ([] ++ [ObsUartIn Uart0 b])%list []).
  - exists c. exact (ush_elem_of_rev_head (c ++ [ObsUartIn Uart0 b])%list cs).
Qed.

(* THE REFUTATION ITSELF, at the shape [cons_swallow]'s arm hands it: the
   byte the history ends in translates to 0x04. *)
Lemma disc_no_ctrl_d (h : list mobs) (b : bv 8) :
  obs_ends_in Uart0 h b -> bv_unsigned (cons_xlate b) = 4 -> disc h -> False.
Proof.
  intros [h0 ->] Hx Hd.
  (* 0x04 is not '\r', so [cons_xlate] is the identity on it *)
  assert (Hb : bv_unsigned b = 4).
  { destruct (decide (b = (mword_of_int 13 : mword 8))) as [-> | Hne].
    - rewrite cons_xlate_cr in Hx. vm_compute in Hx. discriminate Hx.
    - rewrite (cons_xlate_other b Hne) in Hx. exact Hx. }
  destruct (ush_cycles_snoc_in h0 b) as (s0 & Hin).
  apply elem_of_list_lookup in Hin as [i Hi].
  pose proof (disc_seg'_proj _ (Forall_lookup_1 _ _ _ _ Hd Hi)) as Hseg.
  rewrite /disc_seg ins_app ins_in in Hseg.
  pose proof (ush_disc_snoc_val (ins s0) b Hseg) as Hv. lia.
Qed.


(* THE JUMP TABLE at 0x13a8 (.rodata), read as six SIGNED 32-bit
   displacements from the table's own base.  The six values are the dump's
   ([user-rocq/ShData.v], 0x13a8..0x13bf); the arm each one names is
   [ush_jarm] below and every one of those is checked by [vm_compute]
   against the pc the walk actually continues at. *)
Definition SH_JTAB : Z := 0x13a8.

Definition ush_jent (k : Z) : mword 32 :=
  mword_of_int
    (if Z.eqb k 1 then 0xffffed26
     else if Z.eqb k 2 then 0xffffed4e
     else if Z.eqb k 3 then 0xffffed94
     else if Z.eqb k 4 then 0xffffed7c
     else if Z.eqb k 5 then 0xffffee1c
     else 0xffffed1a).

(* ...AND THE TABLE'S TWENTY BYTES ARE IN SH'S OWN .rodata, which is what
   lets the ENTRY pay [ush_jtab] instead of a caller carrying it (lane
   SH-LINE 2b, (b)).  0x13a8 is below 0x2000, so it is inside
   [UCodeShK.shk_ro]; the check is one [vm_compute] on the dump, in the
   [forallb]-over-[seq] shape [UShConsK.sh_cons_ro_bytes_bool] uses for
   sh's "console" literal. *)
Definition ush_jrow_bytes_ok (k : Z) : bool :=
  forallb (fun j : nat =>
      bool_decide (UCodeShK.shk_ro !! (SH_JTAB + 4 * k + Z.of_nat j)
                   = Some (nth_byte (ush_jent k) j)))
    (seq 0 4).

Lemma ush_jrow_bytes_all :
  forallb ush_jrow_bytes_ok [1; 2; 3; 4; 5]%Z = true.
Proof. vm_compute. reflexivity. Qed.

Lemma ush_jrow_bytes (k : Z) (j : nat) :
  In k [1; 2; 3; 4; 5]%Z -> (j < 4)%nat ->
  UCodeShK.shk_ro !! (SH_JTAB + 4 * k + Z.of_nat j)
  = Some (nth_byte (ush_jent k) j).
Proof.
  intros Hk Hj.
  pose proof (proj1 (forallb_forall _ _) ush_jrow_bytes_all k Hk) as H.
  unfold ush_jrow_bytes_ok in H.
  pose proof (proj1 (forallb_forall _ _) H j ltac:(apply in_seq; lia)) as H2.
  exact (bool_decide_eq_true_1 _ H2).
Qed.


(* ===================================================================== *)
(* THE SHELL'S TABLE VIEW (seccomp S4).  sh's own table never moves in the  *)
(* parent past its console preamble -- a redirect or a pipe moves a CHILD's *)
(* table -- and every row it ever holds is closed or the console device.   *)
(* That is the fact the seccomp child needs of its WHOLE table             *)
(* ([UexecSecc.secc_rows]), and the ledger carries it at a view            *)
(* ([UserFd.ustd_at]) that satisfies this.                                 *)
(* ===================================================================== *)
Definition ush_view_ok (v : list fdstate) : Prop :=
  Forall (fun st => st = FdClosed \/ exists r w : bool, st = FdOpen r w (FdDevice CONSOLE)) v.

(* a table under an ok view is ok: a slot the view shows may have closed *)
Lemma ush_view_ok_tab (sts v : list fdstate) :
  ush_view_ok v -> tab_le sts v -> ush_view_ok sts.
Proof.
  intros Hv [_ Hle]. apply Forall_lookup. intros k st Hk.
  destruct (Hle k st Hk) as [Hv' | [-> _]]; [| by left].
  exact (proj1 (Forall_lookup _ _) Hv k st Hv').
Qed.

(* ...and the console preamble's open keeps it: the new view is the old
   table with the console installed *)
Lemma ush_view_ok_open (fdv v : list fdstate) (fd : nat) (r w : bool) :
  ush_view_ok v -> tab_le fdv v ->
  ush_view_ok (<[fd := FdOpen r w (FdDevice CONSOLE)]> fdv).
Proof.
  intros Hv Hle. pose proof (ush_view_ok_tab fdv v Hv Hle) as Hf.
  apply Forall_insert; [exact Hf | right; by exists r, w].
Qed.

Section UkSh.
  Context `{!riscvGS Σ}.
  Context `{!ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  (* ...and the children set's ([Xv6Cameras.uchG]), which [UkRun.urun]
     carries beside the cwd's *)
  Context `{!ghost_varG Σ (gset gname)}.
  Context (N : uk_names Σ).
  (* THE PROGRAM'S PAYLOAD, as a section hypothesis: this program's exit
     owes its parent nothing at this lane, and the entry constructor is
     what fixes it ([UkRun.uslot_of_urun*] mint the record at the payload
     the kernel handed them).  A SECTION hypothesis rather than a premise
     on the exit stub, so that every lemma between the entry and the ecall
     is generalized over it automatically and no intermediate statement has
     to carry it by hand. *)
  Context `{Hpay : !ukn_const N}.
  (* [Xv6Cameras.uartGhostG]: the console ring's own cameras, which is the
     class [UserConsole.upos] is stated over -- a program binds the narrow
     classes and never [Xv6G.xv6G] ([UserConsole.v]'s header). *)
  Context `{!uartGhostG Σ}.
  (* THE PROGRAM'S HALF OF THE CONSOLE POSITION PAIR, as a section variable
     for [Hpay]'s reason: it travels in [ush_pstate] from sh's entry to its
     read and back, and no lemma between the two says anything about it. *)
  Context (γp : gname).
  (* ...AND THE APPLICATION'S TAINT, which sh's entry ledger's third arm is.
     A PARAMETER: the program tier names no application
     ([UserConsole.ucons_pay]'s note).  Persistent, which is what lets the
     arm be a side fact rather than a resource the walk has to thread. *)
  Context (T : iProp Σ).
  Context `{HT : !Persistent T}.
  (* the fields, under the names the engine has always used *)
  Local Notation γt := (ukn_t N).
  Local Notation γd := (ukn_d N).
  Local Notation γs := (ukn_s N).
  Local Notation γfd := (ukn_fd N).
  Local Notation γcwd := (ukn_cwd N).
  Local Notation γch := (ukn_ch N).
  Local Notation γpid := (ukn_pid N).

  (* THE LEDGER sh CARRIES (seccomp S4): the standard streams at a table
     view whose rows are closed or the console ([ush_view_ok]).  Every step
     of the loop keeps the view; the console preamble's open re-sets it to
     the new table, which is still ok ([ush_view_ok_open]). *)
  Definition ush_std (l : list fdstate) : iProp Σ :=
    (∃ v : list fdstate, ⌜ush_view_ok v⌝ ∗ ustd_at γfd l v)%I.

  Global Instance ush_std_timeless l : Timeless (ush_std l).
  Proof using . rewrite /ush_std. apply _. Qed.

  Lemma ush_std_ustd (l : list fdstate) : ush_std l -∗ ustd γfd l.
  Proof using . iIntros "[%v [_ H]]". iApply (ustd_at_ustd with "H"). Qed.

  Lemma ush_std_len (l : list fdstate) : ush_std l -∗ ⌜length l = NSTD⌝.
  Proof using .
    iIntros "H". iDestruct (ush_std_ustd with "H") as "H". iApply (ustd_len with "H").
  Qed.
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

  (* ===================================================================== *)
  (* THE DEPOSITS SH OWES (lane SUPPLY-SPLIT, P4): ONE, and the bundle is   *)
  (* kept as a bundle only so that no call site moved when the other two    *)
  (* left it.                                                               *)
  (*                                                                        *)
  (*   write(16) the prompt and every diagnostic.  E5's output lane.        *)
  (*                                                                        *)
  (*   NOT read(5) ANY MORE (lane SH-LINE 2b, R1').  read's console arm     *)
  (*             spends the EXCLUSIVE reader token, and a [□]-shaped        *)
  (*             key-free law cannot hold one: sh pays its read out of the  *)
  (*             LEASE inside its own exit payload                          *)
  (*             ([UserConsole.ucons_pay], through                          *)
  (*             [UkRun.udepwf_std] and [UkRunSys.wp_uk_ecall_read_recv]).  *)
  (*             The law was still in this bundle after the route changed   *)
  (*             and nothing used it, so the top theorem was carrying a     *)
  (*             premise no walk could spend -- dropped, and                *)
  (*             [UInitBootAdequacy]'s [Hsh_owed] is that much weaker.      *)
  (*   NOT open(15).  sh's [open("console", O_RDWR)] loop at its start    *)
  (*             goes through a PINNED open (lane SH-OPEN), exactly as      *)
  (*             UInitConsK landed /init's ([UkRun.udepwf_at]): the leaf    *)
  (*             bodies [ush_open_console_leaf] / [ush_open_absent_leaf]    *)
  (*             below carry their own supplier, and at the TAINT the       *)
  (*             preamble does not call at all -- it hands the run to the   *)
  (*             generic slot ([ush_gen_slot]).  So no deposit at 15.       *)
  (*                                                                        *)
  (* WHAT IS NOT HERE: [UkRun.udep] at the generic supplier.  sh's own      *)
  (* free numbers -- close(21) here, chdir(9), sbrk(12), wait(3) in the     *)
  (* sibling files -- go through the minting law at [psok := free_num] and  *)
  (* cost nothing, which is what [Hpsok_free] above says.                   *)
  (* ===================================================================== *)
  Definition sh_deps : iProp Σ := udepw_law 16.

  Global Instance sh_deps_persistent : Persistent sh_deps.
  Proof using . rewrite /sh_deps. apply _. Qed.

  Local Notation ra_idx := (mword_of_int 1 : mword 5).
  Local Notation s0_idx := (mword_of_int 8 : mword 5).
  Local Notation s1_idx := (mword_of_int 9 : mword 5).
  Local Notation a0_idx := (mword_of_int 10 : mword 5).
  Local Notation a1_idx := (mword_of_int 11 : mword 5).
  Local Notation a7_idx := (mword_of_int 17 : mword 5).
  Local Notation s2_idx := (mword_of_int 18 : mword 5).
  Local Notation s3_idx := (mword_of_int 19 : mword 5).
  Local Notation s4_idx := (mword_of_int 20 : mword 5).
  Local Notation s5_idx := (mword_of_int 21 : mword 5).
  Local Notation s6_idx := (mword_of_int 22 : mword 5).
  Local Notation a2_idx := (mword_of_int 12 : mword 5).
  Local Notation a3_idx := (mword_of_int 13 : mword 5).
  Local Notation a4_idx := (mword_of_int 14 : mword 5).
  Local Notation a5_idx := (mword_of_int 15 : mword 5).
  Local Notation s7_idx := (mword_of_int 23 : mword 5).
  Local Notation s8_idx := (mword_of_int 24 : mword 5).
  Local Notation x0_idx := (mword_of_int 0 : mword 5).

  (* ===================================================================== *)
  (* THE SYMBOL PINS, ONE NAME EACH.  [shk_syms_pins] is a conjunction that *)
  (* grows a clause per stage, so a positional destruct at every use site   *)
  (* breaks whenever the catalog does.  Destructed ONCE, here.              *)
  (* ===================================================================== *)
  Local Lemma shp_start  : ShSyms.start  = 0x9d0.
  Proof using . destruct shk_syms_pins as (H&_&_&_&_&_&_&_&_&_). exact H. Qed.
  Local Lemma shp_main   : ShSyms.main   = 0x8e2.
  Proof using . destruct shk_syms_pins as (_&H&_&_&_&_&_&_&_&_). exact H. Qed.
  Local Lemma shp_getcmd : ShSyms.getcmd = 0x0.
  Proof using . destruct shk_syms_pins as (_&_&H&_&_&_&_&_&_&_). exact H. Qed.
  Local Lemma shp_memset : ShSyms.memset = 0xa5c.
  Proof using . destruct shk_syms_pins as (_&_&_&H&_&_&_&_&_&_). exact H. Qed.
  Local Lemma shp_gets   : ShSyms.gets   = 0xaaa.
  Proof using . destruct shk_syms_pins as (_&_&_&_&H&_&_&_&_&_). exact H. Qed.
  Local Lemma shp_open   : ShSyms.open   = 0xcc6.
  Proof using . destruct shk_syms_pins as (_&_&_&_&_&H&_&_&_&_). exact H. Qed.
  Local Lemma shp_close  : ShSyms.close  = 0xcae.
  Proof using . destruct shk_syms_pins as (_&_&_&_&_&_&H&_&_&_). exact H. Qed.
  Local Lemma shp_exit   : ShSyms.exit   = 0xc86.
  Proof using . destruct shk_syms_pins as (_&_&_&_&_&_&_&H&_&_). exact H. Qed.
  Local Lemma shp_write  : ShSyms.write  = 0xca6.
  Proof using . destruct shk_syms_pins as (_&_&_&_&_&_&_&_&H&_). exact H. Qed.
  Local Lemma shp_read   : ShSyms.read   = 0xc9e.
  Proof using . destruct shk_syms_pins as (_&_&_&_&_&_&_&_&_&H&_). exact H. Qed.


  (* ===================================================================== *)
  (* STAGE 2, §A -- THE BYTE-RUN ALGEBRA THE LINE BUFFER NEEDS.             *)
  (*                                                                       *)
  (* Stage 1 owned nothing but the free stack: its loop invariant was empty *)
  (* and no leaf it used touched a data byte.  Stage 2's whole subject is a *)
  (* BUFFER -- [buf.0], 100 bytes of .bss at 0x2020 -- written by memset,   *)
  (* by gets, and by the KERNEL through read's window row, then read back   *)
  (* by main's blank-line scan.  So the first thing the stage needs is to   *)
  (* take ONE byte out of a run, put a DIFFERENT byte back, and still have  *)
  (* the run.  [UserHeap.ustr_byte] does the unchanged case for strings;    *)
  (* this is the changing case, for [ubytes].                               *)
  (* ===================================================================== *)

  (* one byte of a run, out and back UNCHANGED *)
  Local Lemma ush_bytes_at (dq : dfrac) (a : Z) (k j : nat) (f : nat -> bv 8) :
    (j < k)%nat ->
    ubytesq γd dq a k f -∗
      ubyteq γd dq (a + Z.of_nat j) (f j) ∗
      (ubyteq γd dq (a + Z.of_nat j) (f j) -∗ ubytesq γd dq a k f).
  Proof using .
    intros Hj. rewrite /ubytesq. iIntros "H".
    iDestruct (big_sepL_lookup_acc _ _ j j with "H") as "[Hb Hcl]";
      [ apply lookup_seq; split; [ lia | exact Hj ] | ].
    iSplitL "Hb"; [ iExact "Hb" | iExact "Hcl" ].
  Qed.

  (* a run only cares about its function BELOW the length *)
  Local Lemma ush_bytes_ext (dq : dfrac) (a : Z) (k : nat) (f g : nat -> bv 8) :
    (forall i : nat, (i < k)%nat -> f i = g i) ->
    ubytesq γd dq a k f -∗ ubytesq γd dq a k g.
  Proof using .
    intros Hfg. rewrite /ubytesq. iIntros "H".
    iApply (big_sepL_mono with "H").
    intros i y Hy.
    apply lookup_seq in Hy. destruct Hy as [Hy Hlt]. subst y.
    rewrite (Hfg (0 + i)%nat Hlt). reflexivity.
  Qed.

  (* a ONE-byte run is a byte *)
  Local Lemma ush_bytes_one (b : Z) (g : nat -> bv 8) (v : bv 8) :
    g 0%nat = v -> ubytes γd b 1 g ⊣⊢ ubyte γd b v.
  Proof using .
    intro Hv. rewrite /ubytes /ubytesq /ubyte /= Z.add_0_r right_id Hv.
    reflexivity.
  Qed.

  (* THE ACCESSOR THE WHOLE STAGE RUNS ON: one byte out, ANY byte back. *)
  Local Lemma ush_bytes_upd (a : Z) (k j : nat) (f : nat -> bv 8) :
    (j < k)%nat ->
    ubytes γd a k f -∗
      ubyte γd (a + Z.of_nat j) (f j) ∗
      (∀ b : bv 8, ubyte γd (a + Z.of_nat j) b -∗ ubytes γd a k (ush_set f j b)).
  Proof using .
    intros Hj.
    remember (k - j - 1)%nat as q eqn:Hq.
    assert (Hk : k = (j + (1 + q))%nat) by lia.
    clear Hq. subst k.
    iIntros "H".
    rewrite (ubytes_app γd a j (1 + q) f).
    iDestruct "H" as "[Hlo Hhi]".
    rewrite (ubytes_app γd (a + Z.of_nat j) 1 q (fun i => f (j + i)%nat)).
    iDestruct "Hhi" as "[Hb Hrest]".
    rewrite (ush_bytes_one (a + Z.of_nat j) (fun i => f (j + i)%nat) (f j)
               ltac:(cbn; f_equal; lia)).
    iSplitL "Hb"; [ iExact "Hb" | ].
    iIntros (b) "Hb".
    rewrite (ubytes_app γd a j (1 + q) (ush_set f j b)).
    iSplitL "Hlo".
    { iApply (ush_bytes_ext (DfracOwn 1) a j f (ush_set f j b) with "Hlo").
      intros i Hi. unfold ush_set.
      rewrite (proj2 (Nat.eqb_neq i j) ltac:(lia)). reflexivity. }
    rewrite (ubytes_app γd (a + Z.of_nat j) 1 q
               (fun i => ush_set f j b (j + i)%nat)).
    iSplitL "Hb".
    { rewrite (ush_bytes_one (a + Z.of_nat j)
                 (fun i => ush_set f j b (j + i)%nat) b
                 ltac:(cbn; unfold ush_set;
                       rewrite (proj2 (Nat.eqb_eq (j + 0)%nat j) ltac:(lia));
                       reflexivity)).
      iExact "Hb". }
    iApply (ush_bytes_ext (DfracOwn 1) (a + Z.of_nat j + Z.of_nat 1) q
              (fun i => f (j + (1 + i))%nat)
              (fun i => ush_set f j b (j + (1 + i))%nat) with "Hrest").
    intros i Hi. unfold ush_set.
    rewrite (proj2 (Nat.eqb_neq (j + (1 + i))%nat j) ltac:(lia)). reflexivity.
  Qed.

  (* ADDRESS BOUNDS OFF THE RESOURCE -- UkEcho.v's [urun_ustr_bnd] at a
     plain run.  A byte the program owns is a byte the image maps, and the
     heap invariant bounds every mapped address by MAXVA, so no caller ever
     has to say where its buffer lives. *)
  Local Lemma urun_ubyte_bnd (h : CpuId) (m : regfile) (pc : mword 64)
      (avail : nat) (dq : dfrac) (a : Z) (b : bv 8) :
    urun N h m pc avail -∗ ubyteq γd dq a b -∗ ⌜ 0 <= a < 2 ^ 38 ⌝.
  Proof using .
    iIntros "Hrun Hb".
    iDestruct "Hrun" as (xi C pt Rfd Rut sz M pm fdv cw gn cs pidv) "(_ & _ & _ & _ & Hh & _ & _ & _ & _)".
    iDestruct (uheap_ubyte with "Hh Hb") as %(_ & _ & Hbnd).
    iPureIntro. exact Hbnd.
  Qed.

  Local Lemma urun_ubytes_bnd (h : CpuId) (m : regfile) (pc : mword 64)
      (avail : nat) (dq : dfrac) (a : Z) (k : nat) (f : nat -> bv 8) :
    (0 < k)%nat ->
    urun N h m pc avail -∗ ubytesq γd dq a k f -∗
    ⌜ 0 <= a /\ a + Z.of_nat k <= 2 ^ 38 ⌝.
  Proof using .
    intros Hk. iIntros "Hrun Hbs".
    iDestruct (ush_bytes_at dq a k 0%nat f ltac:(lia) with "Hbs") as "[Hb0 Hcl]".
    iDestruct (urun_ubyte_bnd with "Hrun Hb0") as %Hlo.
    iDestruct ("Hcl" with "Hb0") as "Hbs".
    iDestruct (ush_bytes_at dq a k (k - 1)%nat f ltac:(lia) with "Hbs")
      as "[Hbk _]".
    iDestruct (urun_ubyte_bnd with "Hrun Hbk") as %Hhi.
    iPureIntro. rewrite Z.add_0_r in Hlo. lia.
  Qed.

  (* [m] says nothing about x0, but the BUNDLE inside [urun] does -- and     *)
  (* gets ends on [sb zero,0(s8)], whose stored byte IS the value of x0.     *)
  (* Without this the NUL that terminates main's scan could not be named.    *)
  (* ([UkRunBr.wp_uk_btype0] exists for the same reason on the branch side;  *)
  (* this is the read of x0 as a VALUE.)                                     *)
  Local Lemma urun_x0 (h : CpuId) (m : regfile) (pc : mword 64) (avail : nat) :
    urun N h m pc avail -∗
    ⌜ m !!! Regidx x0_idx = zero_reg ⌝ ∗ urun N h m pc avail.
  Proof using .
    iIntros "Hrun".
    iDestruct "Hrun" as (xi C pt Rfd Rut sz M pm fdv cw gn cs pidv) "(%Hlo & %Hpm & %Hlzf & %HRut & Hheap & Hstk & Hufd & Hcwda & Hcha & #Hmy & #Hdep & #Hnpx & Hb)".
    iDestruct (uvb_x0 with "Hb") as "[%Hx0 Hb]".
    iSplitR; [ iPureIntro; exact Hx0 | ].
    iExists xi, C, pt, Rfd, Rut, sz, M, pm, fdv, cw, gn, cs, pidv.
    iFrame "Hheap Hstk Hufd Hcwda Hcha Hmy Hdep Hnpx Hb".
    iPureIntro. split_and!; [ exact Hlo | exact Hpm | exact Hlzf | exact HRut ].
  Qed.

  Local Lemma ush_nth_byte0_zero : nth_byte (zero_reg : mword 64) 0 = ubyte0.
  Proof using . vm_compute. reflexivity. Qed.

  (* ...and the byte a [lbu]/[sb] pair puts back (lane IO-LEAF, M5(3)):
     what gets stores at buf[i] is the byte the read delivered. *)
  Local Lemma ush_nth_byte0_moi (b : bv 8) :
    nth_byte (mword_of_int (bv_unsigned b) : mword 64) 0%nat = b.
  Proof using .
    pose proof (bv_unsigned_in_range 8 b) as Hr.
    assert (Em : bv_modulus 8 = 256) by (vm_compute; reflexivity).
    rewrite Em in Hr.
    apply bv_eq. rewrite nth_byte_unsigned.
    replace (Z.of_N (8 * N.of_nat 0)) with 0 by (vm_compute; reflexivity).
    rewrite Z.shiftr_0_r moi_unsigned.
    rewrite (Z.mod_small (bv_unsigned b) Z64 ltac:(unfold Z64; lia)).
    change (2 ^ 8) with 256. apply Z.mod_small. lia.
  Qed.

  (* the [blez] the walk runs on a read's answer, as a NUMBER *)
  Local Lemma ush_blez_taken (v : mword 64) :
    uv_btaken BGE (zero_reg : mword 64) v = Z.geb 0 (bv_signed v).
  Proof using .
    cbn [uv_btaken]. unfold zopz0zKzJ_s.
    assert (Hz : sint (zero_reg : mword 64) = 0)
      by (vm_compute; reflexivity).
    rewrite Hz. reflexivity.
  Qed.

  (* [x - d] tested against zero, at values that cannot wrap: every "is this
     byte a blank / a newline / a return" test in main and in gets. *)
  Local Lemma ush_eqz_sub (x d : Z) :
    0 <= x < Z64 -> 0 <= d < Z64 ->
    eq_vec (mword_of_int (x - d) : mword 64) zero_reg = Z.eqb x d.
  Proof using .
    intros Hx Hd.
    assert (E : (mword_of_int (x - d) : mword 64)
                = mword_of_int ((x - d) mod Z64)).
    { apply bv_eq. rewrite !moi_unsigned Zmod_mod. reflexivity. }
    rewrite E.
    rewrite (moi_eq_zero ((x - d) mod Z64)
               ltac:(apply Z.mod_pos_bound; unfold Z64; lia)).
    destruct (Z.eqb_spec x d) as [-> | Hne].
    - replace (d - d) with 0 by lia. reflexivity.
    - apply Z.eqb_neq. intro H0.
      apply Hne. apply Z.mod_divide in H0; [ | unfold Z64; lia ].
      destruct H0 as [qq Hqq]. unfold Z64 in *. lia.
  Qed.

  Local Lemma ush_neqz_sub (x d : Z) :
    0 <= x < Z64 -> 0 <= d < Z64 ->
    neq_vec (mword_of_int (x - d) : mword 64) zero_reg = negb (Z.eqb x d).
  Proof using .
    intros Hx Hd. unfold neq_vec. rewrite (ush_eqz_sub x d Hx Hd). reflexivity.
  Qed.

  (* the [addi rd,rs,-d] this file does on a loaded byte, as a NUMBER *)
  Local Lemma ush_addi_sub (x d : Z) (imm : mword 12) :
    0 <= x < Z64 -> uoff_i12 imm = - d ->
    (mword_of_int (x - d) : mword 64)
    = add_vec (mword_of_int x : mword 64) (sign_extend' 64 imm).
  Proof using .
    intros Hx Hd. apply (umoi_add_i12 (mword_of_int x) imm (x - d)).
    rewrite (uint_moi x Hx) Hd. lia.
  Qed.


  (* ===================================================================== *)
  (* THE SYSCALL STUB SHAPE.  usys.S emits every stub as                    *)
  (*   c.li a7,<n> ; ecall ; c.jr ra                                        *)
  (* so ONE lemma covers every quiet-row syscall sh issues; the caller      *)
  (* supplies the three [uinstr_is] resources and the number.  The          *)
  (* [n <> USYS_*] premises are the program paying, one by one, for not     *)
  (* being in any of the rows that write user memory, move a descriptor,    *)
  (* or move the working directory.                                         *)
  (* ===================================================================== *)
  Local Lemma wp_ksh_qstub (h : CpuId) (m : regfile) (pc0 pc1 pc2 : Z)
      (imm : mword 6) (n : Z) (avail : nat) :
    (sign_extend' 64 imm : mword 64) = mword_of_int n ->
    usysno (<[Regidx a7_idx := (mword_of_int n : mword 64)]> m) = n ->
    n <> USYS_exit -> n <> USYS_fork ->
    n <> USYS_exec -> n <> USYS_sbrk ->
    n <> USYS_wait -> n <> USYS_pipe -> n <> USYS_read -> n <> USYS_fstat ->
    (* ...and the three that move the descriptor table: this stub re-closes
       the run at the view it opened at, so it is for calls that leave
       [p->ofile[]] alone.  open / close / dup have their own leaves. *)
    n <> USYS_close -> n <> USYS_dup -> n <> USYS_open ->
    (* ...and chdir, the one row that moves the working directory, which
       [urun] carries the process's own authority over *)
    n <> USYS_chdir ->
    (* ...and a number the full mask passes, not seccomp's
       ([UkRunSys.wp_uk_ecall_quiet]'s two new rows) *)
    (0 <= n < 64)%Z -> n <> USYS_seccomp ->
    add_vec_int (mword_of_int pc0 : mword 64) 2 = mword_of_int pc1 ->
    add_vec_int (mword_of_int pc1 : mword 64) 4 = mword_of_int pc2 ->
    is_aligned_vaddr (Virtaddr (mword_of_int pc2 : mword 64)) 2 = true ->
    (* THE DEPOSIT AT THIS STUB'S OWN NUMBER (lane SUPPLY-SPLIT, P4).  The
       twelve exclusions above still leave 16 / 17 / 18 / 19 / 20, every one
       a CLAIM number, so this stub may not route through [UkRun.udep]'s
       law; it takes the deposit for the number it is instantiated at.  Its
       one caller is [wp_ksh_write] at 16, which pays it out of
       [sh_deps]. *)
    udepw_law n -∗
    uinstr_is γt (mword_of_int pc0) true (C_LI (imm, Regidx a7_idx)) -∗
    uinstr_is γt (mword_of_int pc1) false (ECALL tt) -∗
    uinstr_is γt (mword_of_int pc2) true (C_JR (Regidx ra_idx)) -∗
    urun N h m (mword_of_int pc0) avail -∗
    (∀ (h' : CpuId) (ret : mword 64),
       urun N h'
         (<[Regidx a0_idx := ret]>
            (<[Regidx a7_idx := (mword_of_int n : mword 64)]> m))
         (ret_pc (m !!! Regidx ra_idx)) avail -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Himm Hno He Hf Hx Hs Hw Hp Hr Hst Hcl Hdp Hop Hcd Hrng Hn23 E01 E12 Hal2.
    iIntros "#Hdp #Ci0 #Ci1 #Ci2 Hrun Hcont".
    (* ---- pc0  c.li a7,n ---- *)
    iApply (wp_uk_cli N h m (mword_of_int pc0) imm a7_idx avail
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) with "Ci0 Hrun").
    assert (Em : <[Regidx a7_idx := regval_into_reg (sign_extend' 64 imm : mword 64)]> m
                 = <[Regidx a7_idx := (mword_of_int n : mword 64)]> m)
      by (f_equal; exact Himm).
    rewrite E01 Em.
    iIntros (h1) "Hrun".
    set (m1 := <[Regidx a7_idx := (mword_of_int n : mword 64)]> m).
    (* ---- pc1  ecall -- the QUIET row ---- *)
    iApply (wp_uk_ecall_quiet N h1 m1 (mword_of_int pc1) n avail
              Hno He Hf Hx Hs Hw Hp Hr Hst Hcl Hdp Hop Hcd Hrng Hn23
              ltac:(rewrite E12; exact Hal2)
              with "Ci1 Hrun []").
    (* THE FLAGGED DEPOSIT, at this stub's own number: its one caller is
       [wp_ksh_write] at 16 (P4) *)
    { iApply (udepw_of_law N m1 (mword_of_int pc1) n with "Hdp"). }
    rewrite E12.
    iIntros (h2 ret) "Hrun".
    set (m2 := <[Regidx a0_idx := ret]> m1).
    (* ---- pc2  c.jr ra ---- *)
    assert (Hra : m2 !!! Regidx ra_idx = m !!! Regidx ra_idx).
    { unfold m2, m1.
      exact (eq_trans
               (upd_ne m1 (Regidx a0_idx) (Regidx ra_idx) ret
                  ltac:(vm_compute; discriminate))
               (upd_ne m (Regidx a7_idx) (Regidx ra_idx)
                  (mword_of_int n : mword 64)
                  ltac:(vm_compute; discriminate))). }
    iApply (wp_uk_cjr N h2 m2 (mword_of_int pc2) ra_idx
              (ret_pc (m !!! Regidx ra_idx)) avail
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hra; reflexivity)
              with "Ci2 Hrun").
    iIntros (h3) "Hrun".
    iApply ("Hcont" $! h3 ret with "Hrun").
  Qed.

  (* ...and the twin at CLOSE.  Same three instructions; the middle one is
     the close leaf, which SPENDS the caller's handle for the descriptor a0
     names.  sh's handles come from its own entry precondition (fds 0 and 1,
     which init opened and dup'd before exec'ing it) and from [pipe]. *)
  Local Lemma wp_ksh_cstub (h : CpuId) (m : regfile) (pc0 pc1 pc2 : Z)
      (imm : mword 6) (fd : nat) (st : fdstate) (avail : nat) :
    bv_signed (trunc32 (m !!! Regidx a0_idx)) = Z.of_nat fd ->
    (* ...AND THE DESCRIPTOR IS NOT A PIPE END (design/pipe.md, "The byte
       queue").  close(2) is no longer a free number: at a pipe descriptor
       its deposit steps the pipe's exact ghost state, and sh closes only
       descriptors whose type it knows ([wp_ksh_close]'s one call site is
       the console). *)
    (forall (rb wb : bool) (gp : PipeNames.pipe_names),
       st <> FdOpen rb wb (FdPipe gp)) ->
    (sign_extend' 64 imm : mword 64) = mword_of_int USYS_close ->
    usysno (<[Regidx a7_idx := (mword_of_int USYS_close : mword 64)]> m) = USYS_close ->
        (* the three exclusions are NOT here: this stub IS the open one. *)
    add_vec_int (mword_of_int pc0 : mword 64) 2 = mword_of_int pc1 ->
    add_vec_int (mword_of_int pc1 : mword 64) 4 = mword_of_int pc2 ->
    is_aligned_vaddr (Virtaddr (mword_of_int pc2 : mword 64)) 2 = true ->
    uinstr_is γt (mword_of_int pc0) true (C_LI (imm, Regidx a7_idx)) -∗
    uinstr_is γt (mword_of_int pc1) false (ECALL tt) -∗
    uinstr_is γt (mword_of_int pc2) true (C_JR (Regidx ra_idx)) -∗
    urun N h m (mword_of_int pc0) avail -∗
    ufd γfd fd st -∗
    (∀ (h' : CpuId) (ret : mword 64),
       urun N h'
         (<[Regidx a0_idx := ret]>
            (<[Regidx a7_idx := (mword_of_int USYS_close : mword 64)]> m))
         (ret_pc (m !!! Regidx ra_idx)) avail -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Harg Hnp Himm Hno E01 E12 Hal2.
    iIntros "#Ci0 #Ci1 #Ci2 Hrun Hfdh Hcont".
    (* ---- pc0  c.li a7,USYS_close ---- *)
    iApply (wp_uk_cli N h m (mword_of_int pc0) imm a7_idx avail
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) with "Ci0 Hrun").
    assert (Em : <[Regidx a7_idx := regval_into_reg (sign_extend' 64 imm : mword 64)]> m
                 = <[Regidx a7_idx := (mword_of_int USYS_close : mword 64)]> m)
      by (f_equal; exact Himm).
    rewrite E01 Em.
    iIntros (h1) "Hrun".
    set (m1 := <[Regidx a7_idx := (mword_of_int USYS_close : mword 64)]> m).
    (* ---- pc1  ecall -- CLOSE, spending the handle ---- *)
    iApply (wp_uk_ecall_close N h1 m1 (mword_of_int pc1) fd st avail
              Hno
              ltac:(unfold m1;
                    rewrite (upd_ne m (Regidx a7_idx) (Regidx a0_idx)
                               (mword_of_int USYS_close : mword 64)
                               ltac:(vm_compute; discriminate));
                    exact Harg)
              ltac:(rewrite E12; exact Hal2)
              with "Ci1 Hrun [] Hfdh").
    { iApply (udepw_cl_nonpipe N m1 (mword_of_int pc1) st Hnp). }
    rewrite E12.
    (* close of an OPEN descriptor returns 0; sh does not read it *)
    iIntros (h2 ret) "_ Hrun".
    set (m2 := <[Regidx a0_idx := ret]> m1).
    (* ---- pc2  c.jr ra ---- *)
    assert (Hra : m2 !!! Regidx ra_idx = m !!! Regidx ra_idx).
    { unfold m2, m1.
      exact (eq_trans
               (upd_ne m1 (Regidx a0_idx) (Regidx ra_idx) ret
                  ltac:(vm_compute; discriminate))
               (upd_ne m (Regidx a7_idx) (Regidx ra_idx)
                  (mword_of_int USYS_close : mword 64)
                  ltac:(vm_compute; discriminate))). }
    iApply (wp_uk_cjr N h2 m2 (mword_of_int pc2) ra_idx
              (ret_pc (m !!! Regidx ra_idx)) avail
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hra; reflexivity)
              with "Ci2 Hrun").
    iIntros (h3) "Hrun".
    iApply ("Hcont" $! h3 ret with "Hrun").
  Qed.

  (* ---- close @0xcae, SYS_close = 21 ----------------------------------- *)
  (* close SPENDS the handle for the descriptor a0 names.  sh's handles come
     from its entry precondition (fds 0 and 1) and from [pipe]. *)
  Lemma wp_ksh_close (h : CpuId) (m : regfile) (fd : nat) (st : fdstate)
      (avail : nat) :
    bv_signed (trunc32 (m !!! Regidx a0_idx)) = Z.of_nat fd ->
    (* ...and the descriptor is not a pipe end -- see [wp_ksh_cstub] *)
    (forall (rb wb : bool) (gp : PipeNames.pipe_names),
       st <> FdOpen rb wb (FdPipe gp)) ->
    shk_code γt -∗
    urun N h m (mword_of_int ShSyms.close) avail -∗
    ufd γfd fd st -∗
    (∀ (h' : CpuId) (ret : mword 64),
       urun N h'
         (<[Regidx a0_idx := ret]>
            (<[Regidx a7_idx := (mword_of_int 21 : mword 64)]> m))
         (ret_pc (m !!! Regidx ra_idx)) avail -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Harg Hnp. iIntros "#Hcode Hrun Hfdh Hcont".
    rewrite shp_close.
    iApply (wp_ksh_cstub h m 0xcae 0xcb0 0xcb4
              (mword_of_int 21 : mword 6) fd st avail
              Harg Hnp
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(unfold usysno;
                    rewrite (upd_eq m (Regidx a7_idx) (mword_of_int 21 : mword 64));
                    vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "[] [] [] Hrun Hfdh Hcont").
    { iApply (uis_shk_cae with "Hcode"). }
    { iApply (uis_shk_cb0 with "Hcode"). }
    { iApply (uis_shk_cb4 with "Hcode"). }
  Qed.

  (* ---- exit @0xc86, the arm with no continuation ---------------------- *)
  (* THE PAYMENT COMES OUT OF THE PROGRAM'S OWN HAND (lane KILL-PAY,
     K4(a)).  exit's leaf is a PAYMENT: the program owes what its record
     says its exit owes.  It used to take it out of [UkRun.urun]'s payload
     row, and cannot any more -- that row is a WAND from the kill
     credential, because a process that is torn down behind its back
     should not have to fund the payload at all.  So the payload is a
     PREMISE here: [True] at [UkRun.ukn_triv] and free, and at sh's own
     record the console lease it carries beside its position
     ([UkSh.ush_at]).  ONE conjunct, since P6b: the exit leaf owes the
     payload at the status it exits with and nothing else. *)
  Lemma wp_ksh_exit (h : CpuId) (m : regfile) (avail : nat) :
    shk_code γt -∗
    ukn_pay N (-1) -∗
    urun N h m (mword_of_int ShSyms.exit) avail -∗
    mWP (Loop : expr riscv_lang).
  Proof using Hpay.
    iIntros "#Hcode Hpay Hrun".
    rewrite shp_exit.
    (* ---- 0xc86  c.li a7,2 ---- *)
    iApply (wp_uk_cli N h m (mword_of_int 0xc86)
              (mword_of_int 2 : mword 6) a7_idx avail
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) with "[] Hrun").
    { iApply (uis_shk_c86 with "Hcode"). }
    assert (Ec86 : add_vec_int (mword_of_int 0xc86 : mword 64) 2
                   = mword_of_int 0xc88)
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Em : <[Regidx a7_idx
                   := regval_into_reg (sign_extend' 64 (mword_of_int 2 : mword 6)
                                       : mword 64)]> m
                 = <[Regidx a7_idx := (mword_of_int 2 : mword 64)]> m)
      by (f_equal; apply bv_eq; vm_compute; reflexivity).
    rewrite Ec86 Em.
    iIntros (h1) "Hrun".
    set (m1 := <[Regidx a7_idx := (mword_of_int 2 : mword 64)]> m).
    (* ---- 0xc88  ecall -- SYS_exit ---- *)
    iApply (wp_uk_ecall_exit N h1 m1 (mword_of_int 0xc88) avail
              ltac:(unfold m1, usysno;
                    rewrite (upd_eq m (Regidx a7_idx) (mword_of_int 2 : mword 64));
                    vm_compute; reflexivity)
              with "[] [Hpay] Hrun").
    { iApply (uis_shk_c88 with "Hcode"). }
    (* AT A PAYLOAD THAT DOES NOT READ THE STATUS the one copy the program
       holds is the one the leaf owes ([UkRun.ukn_const]): sh's exit owes
       its parent the console reader token ([UserConsole.ucons_pay]). *)
    { rewrite (ukn_const_eq (N := N) (uexitst m1) (-1)). iExact "Hpay". }
  Qed.


  (* ---- write @0xca6, SYS_write = 16 -- quiet, the third stub instance -- *)
  Lemma wp_ksh_write (h : CpuId) (m : regfile) (avail : nat) :
    sh_deps -∗
    shk_code γt -∗
    urun N h m (mword_of_int ShSyms.write) avail -∗
    (∀ (h' : CpuId) (ret : mword 64),
       urun N h'
         (<[Regidx a0_idx := ret]>
            (<[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m))
         (ret_pc (m !!! Regidx ra_idx)) avail -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    iIntros "#Hdp #Hcode Hrun Hcont".
    rewrite shp_write.
    iApply (wp_ksh_qstub h m 0xca6 0xca8 0xcac
              (mword_of_int 16 : mword 6) 16 avail
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(unfold usysno;
                    rewrite (upd_eq m (Regidx a7_idx) (mword_of_int 16 : mword 64));
                    vm_compute; reflexivity)
              ltac:(discriminate) ltac:(discriminate)
              ltac:(discriminate) ltac:(discriminate)
              ltac:(discriminate) ltac:(discriminate)
              ltac:(discriminate) ltac:(discriminate)
              (* ...and the three descriptor-moving numbers, and chdir *)
              ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)
              ltac:(discriminate)
              ltac:(lia) ltac:(discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "[Hdp] [] [] [] Hrun Hcont").
    { iExact "Hdp". }
    { iApply (uis_shk_ca6 with "Hcode"). }
    { iApply (uis_shk_ca8 with "Hcode"). }
    { iApply (uis_shk_cac with "Hcode"). }
  Qed.
  (* ...AND THE SAME STUB WITH THE OUTPUT CHAIN AND THE POST                *)
  (* (app-echo.md, lane IO-LEAF, first half; the leaf is                    *)
  (* [UkRunSys.wp_uk_ecall_write_chain]).                                   *)
  (*                                                                       *)
  (* [wp_ksh_write] above pays row 16 out of [sh_deps] -- the flagged       *)
  (* deposit at 16, which is the whole of what [UkShKernel]'s entry still   *)
  (* owes -- and throws the post away.  This is the same three              *)
  (* instructions with the deposit taken at sh's OWN cursor family and the  *)
  (* post handed back, so that the prompt, "fork\n" and the child's         *)
  (* diagnostic can justify their own bytes.  It does NOT replace           *)
  (* [wp_ksh_write]: the two live side by side, and IO-LEAF's second half   *)
  (* swaps the call at each write site that has a claim to make.            *)
  (*                                                                       *)
  (* [sh_deps] is not a premise here: a named deposit and a flagged one are *)
  (* alternatives, not a pair, and this leaf takes the named one.           *)
  Lemma wp_ksh_write_chain (h : CpuId) (m : regfile) (avail : nat)
      (fdep : sfam) (l : list fdstate) :
    shk_code γt -∗
    urun N h m (mword_of_int ShSyms.write) avail -∗
    udepwf_std N (<[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m)
      (add_vec_int (mword_of_int ShSyms.write : mword 64) 2) 16 fdep l -∗
    UserFd.ustd γfd l -∗
    (∀ (h' : CpuId) (ret : mword 64) (W : uvis) (cw' : Z) (cs' : gset gname),
       ⌜tf_w (uvis_tf W) (tf_arg_idx 0) = m !!! Regidx a0_idx⌝ -∗
       ⌜tf_w (uvis_tf W) (tf_arg_idx 1) = m !!! Regidx a1_idx⌝ -∗
       ⌜tf_w (uvis_tf W) (tf_arg_idx 2) = m !!! Regidx a2_idx⌝ -∗
       ⌜take NSTD (uvis_fd W) = l⌝ -∗
       UserFd.ustd γfd l -∗
       spost_at uslot 16 fdep W ret (uvis_M W) (uvis_fd W) cw' cs' -∗
       urun N h'
         (<[Regidx a0_idx := ret]>
            (<[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m))
         (ret_pc (m !!! Regidx ra_idx)) avail -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    iIntros "#Hcode Hrun Hsb Hstd Hcont".
    rewrite shp_write.
    (* ---- 0xca6  c.li a7,16 ---- *)
    iApply (wp_uk_cli N h m (mword_of_int 0xca6)
              (mword_of_int 16 : mword 6) a7_idx avail
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) with "[] Hrun").
    { iApply (uis_shk_ca6 with "Hcode"). }
    assert (Eca6 : add_vec_int (mword_of_int 0xca6 : mword 64) 2
                   = mword_of_int 0xca8)
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Em : <[Regidx a7_idx
                   := regval_into_reg (sign_extend' 64 (mword_of_int 16 : mword 6)
                                       : mword 64)]> m
                 = <[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m)
      by (f_equal; apply bv_eq; vm_compute; reflexivity).
    rewrite Eca6 Em.
    iIntros (h1) "Hrun".
    set (m1 := <[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m).
    (* ---- 0xca8  ecall -- THE CHAIN-PAYING WRITE ---- *)
    iApply (wp_uk_ecall_write_chain N h1 m1 (mword_of_int 0xca8) avail fdep l
              ltac:(unfold m1, usysno;
                    rewrite (upd_eq m (Regidx a7_idx)
                               (mword_of_int 16 : mword 64));
                    vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "[] Hrun Hsb Hstd").
    { iApply (uis_shk_ca8 with "Hcode"). }
    assert (Eca8 : add_vec_int (mword_of_int 0xca8 : mword 64) 4
                   = mword_of_int 0xcac)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Eca8.
    iIntros (h2 ret W cw' cs') "%Ha0 %Ha1 %Ha2 %Htk Hstd Hpost Hrun".
    set (m2 := <[Regidx a0_idx := ret]> m1).
    (* ---- 0xcac  c.jr ra ---- *)
    assert (Hra : m2 !!! Regidx ra_idx = m !!! Regidx ra_idx).
    { unfold m2, m1.
      exact (eq_trans
               (upd_ne m1 (Regidx a0_idx) (Regidx ra_idx) ret
                  ltac:(vm_compute; discriminate))
               (upd_ne m (Regidx a7_idx) (Regidx ra_idx)
                  (mword_of_int 16 : mword 64)
                  ltac:(vm_compute; discriminate))). }
    iApply (wp_uk_cjr N h2 m2 (mword_of_int 0xcac) ra_idx
              (ret_pc (m !!! Regidx ra_idx)) avail
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hra; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_cac with "Hcode"). }
    iIntros (h3) "Hrun".
    (* the three argument words are the CALLER's: the stub writes a7 and
       then a0, and neither is a0/a1/a2 before the bump *)
    iApply ("Hcont" $! h3 ret W cw' cs' with "[%] [%] [%] [%] Hstd Hpost Hrun").
    { rewrite Ha0 /m1.
      exact (upd_ne m (Regidx a7_idx) (Regidx a0_idx)
               (mword_of_int 16 : mword 64) ltac:(vm_compute; discriminate)). }
    { rewrite Ha1 /m1.
      exact (upd_ne m (Regidx a7_idx) (Regidx a1_idx)
               (mword_of_int 16 : mword 64) ltac:(vm_compute; discriminate)). }
    { rewrite Ha2 /m1.
      exact (upd_ne m (Regidx a7_idx) (Regidx a2_idx)
               (mword_of_int 16 : mword 64) ltac:(vm_compute; discriminate)). }
    { exact Htk. }
  Qed.

  (* ...AT A NAMED TABLE VIEW (seccomp S4): the view rides through *)
  Lemma wp_ksh_write_chain_at (h : CpuId) (m : regfile) (avail : nat)
      (fdep : sfam) (l v : list fdstate) :
    shk_code γt -∗
    urun N h m (mword_of_int ShSyms.write) avail -∗
    udepwf_std N (<[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m)
      (add_vec_int (mword_of_int ShSyms.write : mword 64) 2) 16 fdep l -∗
    UserFd.ustd_at γfd l v -∗
    (∀ (h' : CpuId) (ret : mword 64) (W : uvis) (cw' : Z) (cs' : gset gname),
       ⌜tf_w (uvis_tf W) (tf_arg_idx 0) = m !!! Regidx a0_idx⌝ -∗
       ⌜tf_w (uvis_tf W) (tf_arg_idx 1) = m !!! Regidx a1_idx⌝ -∗
       ⌜tf_w (uvis_tf W) (tf_arg_idx 2) = m !!! Regidx a2_idx⌝ -∗
       ⌜take NSTD (uvis_fd W) = l⌝ -∗
       UserFd.ustd_at γfd l v -∗
       spost_at uslot 16 fdep W ret (uvis_M W) (uvis_fd W) cw' cs' -∗
       urun N h'
         (<[Regidx a0_idx := ret]>
            (<[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m))
         (ret_pc (m !!! Regidx ra_idx)) avail -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    iIntros "#Hcode Hrun Hsb Hstd Hcont".
    rewrite shp_write.
    (* ---- 0xca6  c.li a7,16 ---- *)
    iApply (wp_uk_cli N h m (mword_of_int 0xca6)
              (mword_of_int 16 : mword 6) a7_idx avail
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) with "[] Hrun").
    { iApply (uis_shk_ca6 with "Hcode"). }
    assert (Eca6 : add_vec_int (mword_of_int 0xca6 : mword 64) 2
                   = mword_of_int 0xca8)
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Em : <[Regidx a7_idx
                   := regval_into_reg (sign_extend' 64 (mword_of_int 16 : mword 6)
                                       : mword 64)]> m
                 = <[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m)
      by (f_equal; apply bv_eq; vm_compute; reflexivity).
    rewrite Eca6 Em.
    iIntros (h1) "Hrun".
    set (m1 := <[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m).
    (* ---- 0xca8  ecall -- THE CHAIN-PAYING WRITE ---- *)
    iApply (wp_uk_ecall_write_chain_at N h1 m1 (mword_of_int 0xca8) avail fdep l v
              ltac:(unfold m1, usysno;
                    rewrite (upd_eq m (Regidx a7_idx)
                               (mword_of_int 16 : mword 64));
                    vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "[] Hrun Hsb Hstd").
    { iApply (uis_shk_ca8 with "Hcode"). }
    assert (Eca8 : add_vec_int (mword_of_int 0xca8 : mword 64) 4
                   = mword_of_int 0xcac)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Eca8.
    iIntros (h2 ret W cw' cs') "%Ha0 %Ha1 %Ha2 %Htk Hstd Hpost Hrun".
    set (m2 := <[Regidx a0_idx := ret]> m1).
    (* ---- 0xcac  c.jr ra ---- *)
    assert (Hra : m2 !!! Regidx ra_idx = m !!! Regidx ra_idx).
    { unfold m2, m1.
      exact (eq_trans
               (upd_ne m1 (Regidx a0_idx) (Regidx ra_idx) ret
                  ltac:(vm_compute; discriminate))
               (upd_ne m (Regidx a7_idx) (Regidx ra_idx)
                  (mword_of_int 16 : mword 64)
                  ltac:(vm_compute; discriminate))). }
    iApply (wp_uk_cjr N h2 m2 (mword_of_int 0xcac) ra_idx
              (ret_pc (m !!! Regidx ra_idx)) avail
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hra; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_cac with "Hcode"). }
    iIntros (h3) "Hrun".
    (* the three argument words are the CALLER's: the stub writes a7 and
       then a0, and neither is a0/a1/a2 before the bump *)
    iApply ("Hcont" $! h3 ret W cw' cs' with "[%] [%] [%] [%] Hstd Hpost Hrun").
    { rewrite Ha0 /m1.
      exact (upd_ne m (Regidx a7_idx) (Regidx a0_idx)
               (mword_of_int 16 : mword 64) ltac:(vm_compute; discriminate)). }
    { rewrite Ha1 /m1.
      exact (upd_ne m (Regidx a7_idx) (Regidx a1_idx)
               (mword_of_int 16 : mword 64) ltac:(vm_compute; discriminate)). }
    { rewrite Ha2 /m1.
      exact (upd_ne m (Regidx a7_idx) (Regidx a2_idx)
               (mword_of_int 16 : mword 64) ltac:(vm_compute; discriminate)). }
    { exact Htk. }
  Qed.

  (* ...AND THE SAME STUB WITH THE SOURCE RUN IN THE TEXT HALF (lane
     TXT-ROW's leaf, at sh; [UkEcho.wp_kecho_write_chain_txt] is the twin).

     EVERY LITERAL SH WRITES IS .rodata: the prompt "$ " at 0x1348, the
     three panic strings, the two "%s" formats.  A .rodata run is filed
     under [UkRun.ukn_t] and its pages are X-and-NOT-W, so
     [UserHeap.uheap_ubytes_w] -- which is what [wp_ksh_write_chain] hands
     the leaf -- says nothing about it and the post's SHORT arm cannot be
     refuted.  [UkRunSys.wp_uk_ecall_write_chain_txt] reads the run off
     [UserHeap.uheap_text] instead, one test weaker and true of exactly
     the pages a literal lives on, and hands back the two facts
     [UkWriteLeaf.uwrite_no_short] wants.

     BOTH STUBS STAND, as [wp_ksh_write] and [wp_ksh_write_chain] do: a
     write whose buffer is the LINE BUFFER (the child's diagnostic prints
     a heap string) takes the data-half leaf, and a write whose buffer is
     a literal takes this one. *)
  Lemma wp_ksh_write_chain_txt (h : CpuId) (m : regfile) (avail : nat)
      (fdep : sfam) (l : list fdstate) (nb : nat) (fb : nat -> bv 8) :
    shk_code γt -∗
    urun N h m (mword_of_int ShSyms.write) avail -∗
    udepwf_std N (<[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m)
      (add_vec_int (mword_of_int ShSyms.write : mword 64) 2) 16 fdep l -∗
    UserFd.ustd γfd l -∗
    ([∗ list] j ∈ seq 0 nb,
       utext γt (uint (m !!! Regidx a1_idx) + Z.of_nat j)%Z (fb j)) -∗
    (∀ (h' : CpuId) (ret : mword 64) (W : uvis) (cw' : Z) (cs' : gset gname),
       ⌜tf_w (uvis_tf W) (tf_arg_idx 0) = m !!! Regidx a0_idx⌝ -∗
       ⌜tf_w (uvis_tf W) (tf_arg_idx 1) = m !!! Regidx a1_idx⌝ -∗
       ⌜tf_w (uvis_tf W) (tf_arg_idx 2) = m !!! Regidx a2_idx⌝ -∗
       ⌜take NSTD (uvis_fd W) = l⌝ -∗
       ⌜uvis_lazy W = false⌝ -∗
       ⌜ forall (P : uptd) (j : nat),
           ProcPtOwn.proc_pt_wf P ->
           perm_of (ud_um P) (uvis_sz W) = uvis_perm W ->
           lazy_free (ud_um P) (uvis_sz W) ->
           (j < nb)%nat ->
           UserPtTree.uva_rmapped P
             (uint (add_vec_int (m !!! Regidx a1_idx) (Z.of_nat j))) ⌝ -∗
       UserFd.ustd γfd l -∗
       spost_at uslot 16 fdep W ret (uvis_M W) (uvis_fd W) cw' cs' -∗
       urun N h'
         (<[Regidx a0_idx := ret]>
            (<[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m))
         (ret_pc (m !!! Regidx ra_idx)) avail -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    iIntros "#Hcode Hrun Hsb Hstd #Hbs Hcont".
    rewrite shp_write.
    (* ---- 0xca6  c.li a7,16 ---- *)
    iApply (wp_uk_cli N h m (mword_of_int 0xca6)
              (mword_of_int 16 : mword 6) a7_idx avail
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) with "[] Hrun").
    { iApply (uis_shk_ca6 with "Hcode"). }
    assert (Eca6 : add_vec_int (mword_of_int 0xca6 : mword 64) 2
                   = mword_of_int 0xca8)
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Em : <[Regidx a7_idx
                   := regval_into_reg (sign_extend' 64 (mword_of_int 16 : mword 6)
                                       : mword 64)]> m
                 = <[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m)
      by (f_equal; apply bv_eq; vm_compute; reflexivity).
    rewrite Eca6 Em.
    iIntros (h1) "Hrun".
    set (m1 := <[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m).
    (* ---- 0xca8  ecall -- THE CHAIN-PAYING WRITE, AT THE TEXT ROW ---- *)
    assert (Ha1m1 : m1 !!! Regidx a1_idx = m !!! Regidx a1_idx)
      by exact (upd_ne m (Regidx a7_idx) (Regidx a1_idx)
                  (mword_of_int 16 : mword 64) ltac:(vm_compute; discriminate)).
    rewrite <- Ha1m1.
    iApply (wp_uk_ecall_write_chain_txt N h1 m1 (mword_of_int 0xca8) avail
              fdep l nb fb
              ltac:(unfold m1, usysno;
                    rewrite (upd_eq m (Regidx a7_idx)
                               (mword_of_int 16 : mword 64));
                    vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "[] Hrun Hsb Hstd Hbs").
    { iApply (uis_shk_ca8 with "Hcode"). }
    assert (Eca8 : add_vec_int (mword_of_int 0xca8 : mword 64) 4
                   = mword_of_int 0xcac)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Eca8.
    iIntros (h2 ret W cw' cs')
      "%Ha0 %Ha1 %Ha2 %Htk %Hlz %Hnf Hstd _ Hpost Hrun".
    rewrite Ha1m1.
    set (m2 := <[Regidx a0_idx := ret]> m1).
    (* ---- 0xcac  c.jr ra ---- *)
    assert (Hra : m2 !!! Regidx ra_idx = m !!! Regidx ra_idx).
    { unfold m2, m1.
      exact (eq_trans
               (upd_ne m1 (Regidx a0_idx) (Regidx ra_idx) ret
                  ltac:(vm_compute; discriminate))
               (upd_ne m (Regidx a7_idx) (Regidx ra_idx)
                  (mword_of_int 16 : mword 64)
                  ltac:(vm_compute; discriminate))). }
    iApply (wp_uk_cjr N h2 m2 (mword_of_int 0xcac) ra_idx
              (ret_pc (m !!! Regidx ra_idx)) avail
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hra; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_cac with "Hcode"). }
    iIntros (h3) "Hrun".
    iApply ("Hcont" $! h3 ret W cw' cs'
              with "[%] [%] [%] [%] [%] [%] Hstd Hpost Hrun").
    { rewrite Ha0 /m1.
      exact (upd_ne m (Regidx a7_idx) (Regidx a0_idx)
               (mword_of_int 16 : mword 64) ltac:(vm_compute; discriminate)). }
    { rewrite Ha1 /m1.
      exact (upd_ne m (Regidx a7_idx) (Regidx a1_idx)
               (mword_of_int 16 : mword 64) ltac:(vm_compute; discriminate)). }
    { rewrite Ha2 /m1.
      exact (upd_ne m (Regidx a7_idx) (Regidx a2_idx)
               (mword_of_int 16 : mword 64) ltac:(vm_compute; discriminate)). }
    { exact Htk. }
    { exact Hlz. }
    { rewrite <- Ha1m1. exact Hnf. }
  Qed.

  (* ...AT A NAMED TABLE VIEW (seccomp S4): the view rides through *)
  Lemma wp_ksh_write_chain_txt_at (h : CpuId) (m : regfile) (avail : nat)
      (fdep : sfam) (l v : list fdstate) (nb : nat) (fb : nat -> bv 8) :
    shk_code γt -∗
    urun N h m (mword_of_int ShSyms.write) avail -∗
    udepwf_std N (<[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m)
      (add_vec_int (mword_of_int ShSyms.write : mword 64) 2) 16 fdep l -∗
    UserFd.ustd_at γfd l v -∗
    ([∗ list] j ∈ seq 0 nb,
       utext γt (uint (m !!! Regidx a1_idx) + Z.of_nat j)%Z (fb j)) -∗
    (∀ (h' : CpuId) (ret : mword 64) (W : uvis) (cw' : Z) (cs' : gset gname),
       ⌜tf_w (uvis_tf W) (tf_arg_idx 0) = m !!! Regidx a0_idx⌝ -∗
       ⌜tf_w (uvis_tf W) (tf_arg_idx 1) = m !!! Regidx a1_idx⌝ -∗
       ⌜tf_w (uvis_tf W) (tf_arg_idx 2) = m !!! Regidx a2_idx⌝ -∗
       ⌜take NSTD (uvis_fd W) = l⌝ -∗
       ⌜uvis_lazy W = false⌝ -∗
       ⌜ forall (P : uptd) (j : nat),
           ProcPtOwn.proc_pt_wf P ->
           perm_of (ud_um P) (uvis_sz W) = uvis_perm W ->
           lazy_free (ud_um P) (uvis_sz W) ->
           (j < nb)%nat ->
           UserPtTree.uva_rmapped P
             (uint (add_vec_int (m !!! Regidx a1_idx) (Z.of_nat j))) ⌝ -∗
       UserFd.ustd_at γfd l v -∗
       spost_at uslot 16 fdep W ret (uvis_M W) (uvis_fd W) cw' cs' -∗
       urun N h'
         (<[Regidx a0_idx := ret]>
            (<[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m))
         (ret_pc (m !!! Regidx ra_idx)) avail -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    iIntros "#Hcode Hrun Hsb Hstd #Hbs Hcont".
    rewrite shp_write.
    (* ---- 0xca6  c.li a7,16 ---- *)
    iApply (wp_uk_cli N h m (mword_of_int 0xca6)
              (mword_of_int 16 : mword 6) a7_idx avail
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) with "[] Hrun").
    { iApply (uis_shk_ca6 with "Hcode"). }
    assert (Eca6 : add_vec_int (mword_of_int 0xca6 : mword 64) 2
                   = mword_of_int 0xca8)
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Em : <[Regidx a7_idx
                   := regval_into_reg (sign_extend' 64 (mword_of_int 16 : mword 6)
                                       : mword 64)]> m
                 = <[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m)
      by (f_equal; apply bv_eq; vm_compute; reflexivity).
    rewrite Eca6 Em.
    iIntros (h1) "Hrun".
    set (m1 := <[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m).
    (* ---- 0xca8  ecall -- THE CHAIN-PAYING WRITE, AT THE TEXT ROW ---- *)
    assert (Ha1m1 : m1 !!! Regidx a1_idx = m !!! Regidx a1_idx)
      by exact (upd_ne m (Regidx a7_idx) (Regidx a1_idx)
                  (mword_of_int 16 : mword 64) ltac:(vm_compute; discriminate)).
    rewrite <- Ha1m1.
    iApply (wp_uk_ecall_write_chain_txt_at N h1 m1 (mword_of_int 0xca8) avail
              fdep l v nb fb
              ltac:(unfold m1, usysno;
                    rewrite (upd_eq m (Regidx a7_idx)
                               (mword_of_int 16 : mword 64));
                    vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "[] Hrun Hsb Hstd Hbs").
    { iApply (uis_shk_ca8 with "Hcode"). }
    assert (Eca8 : add_vec_int (mword_of_int 0xca8 : mword 64) 4
                   = mword_of_int 0xcac)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Eca8.
    iIntros (h2 ret W cw' cs')
      "%Ha0 %Ha1 %Ha2 %Htk %Hlz %Hnf Hstd _ Hpost Hrun".
    rewrite Ha1m1.
    set (m2 := <[Regidx a0_idx := ret]> m1).
    (* ---- 0xcac  c.jr ra ---- *)
    assert (Hra : m2 !!! Regidx ra_idx = m !!! Regidx ra_idx).
    { unfold m2, m1.
      exact (eq_trans
               (upd_ne m1 (Regidx a0_idx) (Regidx ra_idx) ret
                  ltac:(vm_compute; discriminate))
               (upd_ne m (Regidx a7_idx) (Regidx ra_idx)
                  (mword_of_int 16 : mword 64)
                  ltac:(vm_compute; discriminate))). }
    iApply (wp_uk_cjr N h2 m2 (mword_of_int 0xcac) ra_idx
              (ret_pc (m !!! Regidx ra_idx)) avail
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hra; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_cac with "Hcode"). }
    iIntros (h3) "Hrun".
    iApply ("Hcont" $! h3 ret W cw' cs'
              with "[%] [%] [%] [%] [%] [%] Hstd Hpost Hrun").
    { rewrite Ha0 /m1.
      exact (upd_ne m (Regidx a7_idx) (Regidx a0_idx)
               (mword_of_int 16 : mword 64) ltac:(vm_compute; discriminate)). }
    { rewrite Ha1 /m1.
      exact (upd_ne m (Regidx a7_idx) (Regidx a1_idx)
               (mword_of_int 16 : mword 64) ltac:(vm_compute; discriminate)). }
    { rewrite Ha2 /m1.
      exact (upd_ne m (Regidx a7_idx) (Regidx a2_idx)
               (mword_of_int 16 : mword 64) ltac:(vm_compute; discriminate)). }
    { exact Htk. }
    { exact Hlz. }
    { rewrite <- Ha1m1. exact Hnf. }
  Qed.

  (* ===================================================================== *)
  (* WHAT THE WALK SPENDS PER WRITE (lane IO-LEAF, M4a).                    *)
  (*                                                                       *)
  (* [UkEcho.kecho_w]'s twin at sh, and it is per CALL and not per byte for *)
  (* the same reason: sh's prompt is [write(2, "$ ", 2)] and the child's    *)
  (* diagnostic is an [fprintf] whose putc writes one byte at a time, so    *)
  (* the obligation has to be statable at any count.  THE DESCRIPTOR IS A   *)
  (* PARAMETER, which /init's and echo's are not: sh writes its prompt to   *)
  (* fd 2 and its diagnostics to fd 2, while echo writes to fd 1, and which *)
  (* arm of [SpecFilewrite.filewrite_in] row 16 asks for is decided by      *)
  (* argument 0's ledger row.                                              *)
  (*                                                                       *)
  (* It names nothing but the program tier's own vocabulary -- the three    *)
  (* argument registers, the run, [Ci], [Co] -- and that is forced: sh sits *)
  (* BELOW the file system and cannot name row 16's reading at all          *)
  (* ([UkWriteLeaf]'s header).  The CONCRETE discharge -- the console       *)
  (* chain, the era's write link, the short arm's refutation -- is proved   *)
  (* above [UkWriteLeaf] and reaches this walk as a premise, exactly as     *)
  (* /init's banner reaches [UkInitMain] from [UInitBanner].                *)
  (* ===================================================================== *)
  Definition ksh_w (fdw ua : mword 64) (nb : nat) (Ci Co : iProp Σ) : iProp Σ :=
    (∀ (h : CpuId) (m : regfile) (avail : nat),
       ⌜m !!! Regidx a0_idx = fdw⌝ -∗
       ⌜m !!! Regidx a1_idx = ua⌝ -∗
       ⌜m !!! Regidx a2_idx = (mword_of_int (Z.of_nat nb) : mword 64)⌝ -∗
       shk_code γt -∗
       Ci -∗
       urun N h m (mword_of_int ShSyms.write) avail -∗
       (∀ (h' : CpuId) (ret : mword 64),
          Co -∗
          urun N h'
            (<[Regidx a0_idx := ret]>
               (<[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m))
            (ret_pc (m !!! Regidx ra_idx)) avail -∗
          mWP (Loop : expr riscv_lang)) -∗
       mWP (Loop : expr riscv_lang))%I.

  (* ...AND THE TRIVIAL ONE: the flagged deposit pays row 16 and the post
     is thrown away, which is what every write of sh's does today.  This is
     what keeps the two stubs side by side ([wp_ksh_write] beside
     [wp_ksh_write_chain]) while the swap happens one site at a time. *)
  Lemma ksh_w_of_law (fdw ua : mword 64) (nb : nat) (Ci Co : iProp Σ) :
    (Ci ⊢ Co) -> sh_deps -∗ ksh_w fdw ua nb Ci Co.
  Proof using .
    intros Hm. iIntros "#Hdp" (h m avail) "_ _ _ #Hcode HCi Hrun Hcont".
    iApply (wp_ksh_write h m avail with "Hdp Hcode Hrun").
    iIntros (h' ret) "Hrun".
    iApply ("Hcont" $! h' ret with "[HCi] Hrun"). by iApply Hm.
  Qed.

  (* ...and the output side is MONOTONE, which is what lets the LAST write
     of a run hand its cursor straight on ([UkEcho.kecho_w_mono]'s twin). *)
  Lemma ksh_w_mono (fdw ua : mword 64) (nb : nat) (Ci Co Co' : iProp Σ) :
    (Co -∗ Co') -∗ ksh_w fdw ua nb Ci Co -∗ ksh_w fdw ua nb Ci Co'.
  Proof using .
    iIntros "Hm Hw" (h m avail) "%Ha0 %Ha1 %Ha2 #Hcode HCi Hrun Hcont".
    iApply ("Hw" $! h m avail with "[%] [%] [%] Hcode HCi Hrun");
      [ exact Ha0 | exact Ha1 | exact Ha2 | ].
    iIntros (h' ret) "HCo Hrun".
    iApply ("Hcont" $! h' ret with "[Hm HCo] Hrun").
    iApply ("Hm" with "HCo").
  Qed.

  (* ...AND IT FRAMES: a caller that HOLDS the input half a payment asks
     for hands it over once and is left with the obligation at the rest.
     This is how the prompt's payment reaches the walk -- the credential
     is linear and the conversion is not, so the two travel separately and
     meet here. *)
  Lemma ksh_w_frame (fdw ua : mword 64) (nb : nat) (Ci Co C : iProp Σ) :
    C -∗ ksh_w fdw ua nb (Ci ∗ C) Co -∗ ksh_w fdw ua nb Ci Co.
  Proof using .
    iIntros "HC Hw" (h m avail) "%Ha0 %Ha1 %Ha2 #Hcode HCi Hrun Hcont".
    iApply ("Hw" $! h m avail with "[%] [%] [%] Hcode [$HCi $HC] Hrun Hcont");
      [ exact Ha0 | exact Ha1 | exact Ha2 ].
  Qed.

  (* ===================================================================== *)
  (* THE CREDENTIAL AT EVERY LINE BOUNDARY (lane IO-LEAF, M6a(3); the      *)
  (* entry unbundled at its step 3).                                       *)
  (*                                                                       *)
  (* sh's "$ " is the byte that RESOLVES a round of the application's      *)
  (* transcript, so it is paid for by the era's own write link and not by  *)
  (* the flagged deposit -- but this file sits below the file system and   *)
  (* below the application, and can say neither.  What the command loop    *)
  (* carries is a FAMILY [Wc I p], the era's write credential at boundary  *)
  (* [I] with [p] of the prompt's two bytes out, which this file cannot    *)
  (* read (it names no era) and carries opaquely beside its cursor,        *)
  (* exactly as it carries [Pm].  Two laws are all the loop needs of it:   *)
  (* the prompt's call takes [0] to [2] ([ush_prompt_law], quantified over *)
  (* the ledger because the preamble may move it; [UShOut.               *)
  (* ksh_w_of_link_cred] is the one discharge), and the read of a line     *)
  (* takes [2] at [I] to [3] at [I ++ line] on the pieces the read leaves  *)
  (* ([ush_wc_read], below, with [Pm]).                                    *)
  (*                                                                       *)
  (* THE BOUNDARY IS THE ERA'S INPUT, not a count of it (project           *)
  (* echo-any-line): a round reads a line of its own, so "which boundary"  *)
  (* is the bytes typed so far and the round the transcript is at is the   *)
  (* number of newlines in them ([LineWords.nlines]).  This file reads     *)
  (* neither; it carries the list where it carried the number.             *)
  (* ===================================================================== *)
  Context (Wc : list (bv 8) -> nat -> iProp Σ).

  (* ...AND THE BANNER-OWED CREDENTIAL AT A BOUNDARY (step 3): what a
     shell holds when its fd 2 is CLOSED.  /init's banner went to a closed
     descriptor and printed nothing, so the era still owes the round's
     banner; [Wb I] is the credential for it, and sh carries it UNCHANGED
     through its prompt -- the prompt writes nothing on a closed
     descriptor either -- to the exit, where it goes into the payload
     ([ush_at_of_pm_wb] below).  Opaque here for [Wc]'s reason. *)
  Context (Wb : list (bv 8) -> iProp Σ).

  (* ...AND THE TWO CONVERSIONS THE SLOT NEEDS OF THE FAMILIES (step 4),
     Coq-level for [ush_wc_read]'s reason.  The banner-owed credential IS a
     prompt credential once the console reaches fd 2: /init's banner went
     nowhere, so the round's prologue is the bare prompt
     ([EchoLinksBan.ewc_ban_line] is the one discharge).  And a block owed
     with nothing chosen ([Wc I 3], what a line's read leaves and the fork
     lends) is a boundary credential at the same input -- the '$' is the
     block's first byte ([EchoLinksLine.ewc_lcred_blk_line]). *)
  Hypothesis ush_wb_wc : forall I : list (bv 8), ⊢ Wb I -∗ Wc I 0%nat.
  Hypothesis ush_wc_blk_line :
    forall I : list (bv 8), ⊢ Wc I 3%nat -∗ Wc I 0%nat.

  (* THE PROMPT'S LAW, at the two ledgers a prompt can be printed on: fd 2
     is the console, where the call moves the credential from [0] to [2];
     or fd 2 is CLOSED, where the call writes nothing and needs nothing
     ([UkWriteClosed.ksh_w_of_closed] is that arm's discharge -- it sits
     ABOVE this file, which is why the arm is a law here and not a
     lemma). *)
  Definition ush_prompt_law : iProp Σ :=
    (□ ((∀ (I : list (bv 8)) (l : list fdstate),
           ⌜ ush_fd2p l ⌝ -∗
           ksh_w (mword_of_int 2) (mword_of_int sh_prompt_pv) 2%nat
             (ush_std l ∗ Wc I 0%nat) (ush_std l ∗ Wc I 2%nat))
        ∗ (∀ l : list fdstate,
             ⌜ l !! 2%nat = Some FdClosed ⌝ -∗
             ksh_w (mword_of_int 2) (mword_of_int sh_prompt_pv) 2%nat
               (ush_std l) (ush_std l))))%I.

  Global Instance ush_prompt_law_persistent : Persistent ush_prompt_law.
  Proof using . rewrite /ush_prompt_law. apply _. Qed.

  (* ...AS THE LOOP CARRIES IT, at three arms.  The BOTH-CONSOLE arm: fd 0,
     fd 1 and fd 2 are the console (init's pinned table, preserved by the
     preamble's opens) and the era's credential is here; [p] is the
     prompt bytes out, and [3] the line's BLOCK OWED with nothing chosen
     (the body's index, what a line's read leaves and the fork lends).
     The CLOSED arm: the ledger is /init's all-closed one with the
     preamble's first opens landed ([ush_lcl]) -- so fd 2 is still closed
     -- and the banner-owed credential rides unchanged; it never reaches
     the body ([p < 3]: a line read on it is the taint,
     [ush_gets_done_line]).  NO AFFINE ARM (lane EXEC-SEAM, (C)): its two
     producers are gone -- /init's lend names the taint on its third arm
     and the entry runs a tainted shell on the generic slot, and the wait
     re-entry identifies the reaped child as the one forked (the entry's
     key pins sh's children set and pid).  A tainted turn is [ush_posb]'s
     right arm, never a slot.  Indexed by the ledger because the console
     preamble may move it ([ush_wcp_cons]). *)
  Definition ush_wcp (l : list fdstate) (I : list (bv 8)) (p : nat)
      : iProp Σ :=
    ((⌜ ush_fd0c l /\ ush_fd1p l /\ ush_fd2p l ⌝ ∗ Wc I p)
     ∨ (⌜ (exists j : nat, (j <= 2)%nat /\ ush_lcl l j) /\ (p < 3)%nat ⌝ ∗ Wb I))%I.

  (* the preamble installs the console at the lowest closed slot [k]: the
     console arm's rows survive it; the closed arm's ledger gains one open
     -- and when that open is the THIRD, every standard stream is the
     console and the banner-owed credential is the prompt's
     ([ush_wb_wc]) *)
  Lemma ush_wcp_cons (l : list fdstate) (k : nat) (I : list (bv 8)) :
    length l = NSTD ->
    fd_lowest_closed l = Some k ->
    ush_wcp l I 0%nat -∗
    ush_wcp (<[k := FdOpen true true (FdDevice CONSOLE)]> l) I 0%nat.
  Proof using ush_wb_wc.
    intros Hlen Hk. rewrite /ush_wcp.
    iIntros "[[%Hrow Hc] | [%Hcl Hb]]"; last first.
    { destruct Hcl as [[j [Hj2 Hlcl]] _].
      assert (Hj3 : (j < NSTD)%nat) by (unfold NSTD; lia).
      assert (Hkj : k = j) by exact (ush_lcl_lowest l j k Hj3 Hlcl Hk).
      subst k.
      pose proof (ush_lcl_cons l j Hlen Hj3 Hlcl) as Hlcl'.
      destruct (decide (j = 2%nat)) as [-> | Hne].
      - iLeft. iSplitR; [ iPureIntro; exact (ush_lcl_rows _ Hlcl') | ].
        iApply (ush_wb_wc I with "Hb").
      - iRight. iFrame "Hb". iPureIntro. split; [ | lia ].
        exists (S j). split; [ lia | exact Hlcl' ]. }
    destruct Hrow as (Hfd0c & Hfd1 & Hfd2).
    iLeft. iFrame "Hc". iPureIntro.
    split_and!; [ exact (ush_fd0c_cons l k Hlen Hfd0c)
                | exact (ush_fd1p_cons l k Hlen Hfd1)
                | exact (ush_fd2p_cons l k Hlen Hfd2) ].
  Qed.

  (* THE PROMPT'S CALL, AT WHICHEVER ARM THE WALK IS ON: the loop's
     credential through the law's console arm, or the banner-owed
     credential framed past the law's closed arm.  No free law any more
     (lane EXEC-SEAM, (C)): the slot has no affine arm to print on.  What
     comes back is the loop's slot two bytes on. *)
  Lemma ksh_w_of_wcp (l : list fdstate) (I : list (bv 8)) :
    ush_prompt_law -∗
    ush_wcp l I 0%nat -∗
    ksh_w (mword_of_int 2) (mword_of_int sh_prompt_pv) 2%nat
      (ush_std l) (ush_std l ∗ ush_wcp l I 2%nat).
  Proof using .
    iIntros "#Hlaw Hwc". rewrite /ush_prompt_law.
    iDestruct "Hlaw" as "[#Hplaw #Hclaw]".
    iDestruct "Hwc" as "[[%Hrow Hc] | [%Hcl Hb]]"; last first.
    { destruct Hcl as [[j [Hj2 Hlcl]] _].
      iDestruct ("Hclaw" $! l with "[%]") as "Hw"; [ exact (ush_lcl_2 l j Hj2 Hlcl) | ].
      iApply (ksh_w_mono _ _ _ (ush_std l) (ush_std l) with "[Hb] [Hw]").
      - iIntros "$". rewrite /ush_wcp. iRight. iFrame "Hb".
        iPureIntro. split; [ exists j; split; [ exact Hj2 | exact Hlcl ] | lia ].
      - iExact "Hw". }
    destruct Hrow as (Hfd0c & Hfd1 & Hfd2).
    iDestruct ("Hplaw" $! I l with "[%]") as "Hw"; [ exact Hfd2 | ].
    iApply (ksh_w_mono _ _ _ (ush_std l) (ush_std l ∗ Wc I 2%nat)
              with "[] [Hc Hw]").
    - iIntros "[$ Hc]". rewrite /ush_wcp. iLeft. iFrame "Hc".
      iPureIntro. split_and!; [ exact Hfd0c | exact Hfd1 | exact Hfd2 ].
    - iApply (ksh_w_frame with "Hc Hw").
  Qed.


  (* ===================================================================== *)
  (* THE TAG'S READING, AS A PERSISTENT LAW SH'S ENTRY TAKES                *)
  (* (lane SH-LINE 2b, L4; app-echo.md, "SH-LINE PHASE 1 LANDED",           *)
  (* ruling (3)).                                                          *)
  (*                                                                       *)
  (* [RiscvPtsto.riscv_rx_tag] is a field of the machine's FIXED ghost      *)
  (* state, tied to the application's own tag ([App.app_tag]) only by an    *)
  (* equation in the top theorem's [boot_fixedGS] -- nothing below reads    *)
  (* it.  So the reading is a PREMISE, threaded from [SystemAdequacy]'s     *)
  (* [Hinit_boot] through init's pinned builder to sh's entry, exactly as   *)
  (* [UInitSh.init_sh_slot] takes its claim law.                           *)
  (*                                                                       *)
  (* PERSISTENT, which it must be: sh's entry is built inside init's fork   *)
  (* child, inside an [iLob] the parent re-enters.                         *)
  (*                                                                       *)
  (* STATED HERE rather than in [UConsLine.v] because [ush_rest_l] below    *)
  (* consumes what it produces and this file is under that one.            *)
  (* ===================================================================== *)
  (* THE DISCIPLINE IS A PARAMETER (lane LINK-GEN, item 21).  The tag's
     reading was [⌜EchoDisc.disc h⌝ ∨ T] -- the ECHO discipline -- and the
     FILE era cannot supply it: [FileOut.ftag]'s second conjunct is
     [⌜FileDisc.disc_f h⌝ ∨ file_taint], and [disc_f h] does NOT imply
     [disc h] (lane STAGE's ruling: a [cat] line is not an echo line).  So
     the reading takes the discipline as a parameter [D]. *)
  Definition ush_tag_law_at (D : list mobs -> Prop) : iProp Σ :=
    (□ (∀ h : list mobs, riscv_rx_tag h -∗ ⌜D h⌝ ∨ T))%I.

  (* ...AND WHAT EVERYTHING BELOW ACTUALLY DRAWS FROM IT is ONE
     consequence: a tag on a history whose last console byte is C('D') is
     the taint ([ush_swallow_taint] is its only consumer, and the ^D
     refutation is the only use the discipline was ever put to here).  So
     THAT is what travels -- [UInitSh.sh_pay]'s third conjunct,
     [UConsLine]'s payload, [UShKernel]'s three entries -- and a
     discipline appears only where an era PRODUCES it.  A [D]-era
     converts with [ush_tag_law_of_at] once it has shown that no
     [D]-history ends in a C('D'); echo's is [disc_no_ctrl_d]. *)
  Definition ush_tag_law : iProp Σ :=
    (□ (∀ (h : list mobs) (b : bv 8),
          ⌜obs_ends_in Uart0 h b⌝ -∗
          ⌜bv_unsigned (cons_xlate b) = 4⌝ -∗
          riscv_rx_tag h -∗ T))%I.

  Global Instance ush_tag_law_at_persistent D : Persistent (ush_tag_law_at D).
  Proof using . rewrite /ush_tag_law_at. apply _. Qed.
  Global Instance ush_tag_law_persistent : Persistent ush_tag_law.
  Proof using . rewrite /ush_tag_law. apply _. Qed.

  Lemma ush_tag_law_of_at (D : list mobs -> Prop) :
    (forall (h : list mobs) (b : bv 8),
       obs_ends_in Uart0 h b -> bv_unsigned (cons_xlate b) = 4 ->
       D h -> False) ->
    ush_tag_law_at D -∗ ush_tag_law.
  Proof using .
    intro HD. iIntros "#Hl !>" (h b) "%Hen %Hx Htg".
    iDestruct ("Hl" $! h with "Htg") as "[%Hd | HT]"; [ | iExact "HT" ].
    exfalso. exact (HD h b Hen Hx Hd).
  Qed.

  (* the echo era's instance: [D := EchoDisc.disc] *)
  Lemma ush_tag_law_echo : ush_tag_law_at disc -∗ ush_tag_law.
  Proof using . exact (ush_tag_law_of_at disc disc_no_ctrl_d). Qed.

  (* ===================================================================== *)
  (* THE ONE HYPOTHESIS OF STAGE 2: SH'S CONSOLE READ, WITH THE RECEIPT     *)
  (* KEPT (lane SH-LINE 2b, R1').                                           *)
  (*                                                                       *)
  (* [read] is syscall 5, and 5 is one of the eight numbers                 *)
  (* [UsysMemOk.usys_mem_ok] gives a WINDOW to.  The GENERAL window leaf    *)
  (* ([UkRunSys.wp_uk_ecall_window]) is not what sh runs on any more: it    *)
  (* binds the process's [spost_at] as [_], so the kernel's receipt reaches *)
  (* the round and is dropped there, and a shell that has thrown its        *)
  (* receipt away can never say WHICH bytes are in its line.  This is the   *)
  (* same call with the post KEPT -- [UkRunSys.wp_uk_ecall_read_recv]'s     *)
  (* deliverable -- and it costs the caller exactly two things the window   *)
  (* leaf did not ask for:                                                  *)
  (*                                                                       *)
  (*   ITS LEDGER, because the arm the kernel's row takes is selected by    *)
  (*   the KEY's descriptor table and a program holds only its own record   *)
  (*   of the low [NSTD] slots.  The pure row beside it is [ush_fd0p] --    *)
  (*   the very row the console preamble establishes and the command loop   *)
  (*   carries -- so the leaf answers on BOTH of its arms and sh's [gets]   *)
  (*   does not case split: fd 0 is the console (the receipt), or fd 0 is   *)
  (*   closed and [read] returns -1 (lane CLOSED-READ), which is the same   *)
  (*   arm of the answer as a killed process's.                             *)
  (*                                                                       *)
  (*   ITS POSITION ([UserConsole.upos]), because a receipt is only a       *)
  (*   receipt AT A CURSOR: what the shell needs to know is that the byte   *)
  (*   it was just handed is the one after the byte it was handed last.     *)
  (*                                                                       *)
  (* THE COUNT AND THE BUFFER ARE TWO NUMBERS, [cap] and [k], and [cap <=   *)
  (* k] is all that relates them (lane CONS-ROWS): the slack byte the       *)
  (* copy-out reason used to need is gone, because at [dd = cap] the        *)
  (* cursor's first control-flow row says the call popped exactly what it   *)
  (* delivered, so there is no fault left to refute.  [gets] asks for one   *)
  (* byte into a one-byte window, i.e. [cap = k = 1].                       *)
  (*                                                                       *)
  (* EVERY LEMMA BELOW THAT DEPENDS ON IT SAYS SO IN ITS HEADER:            *)
  (* [wp_ksh_read], [wp_ksh_gets], [wp_ksh_getcmd], [wp_ksh_cmd_head],      *)
  (* [wp_ksh_console], [wp_ksh_main] and [wp_ksh_start].  Everything else   *)
  (* in this file -- the byte-run algebra, the quiet stubs, exit, memset,   *)
  (* and main's blank-line scan -- is unconditional.                        *)
  (* ===================================================================== *)

  (* ...AND THE PROGRAM'S HALF OF THE CONSOLE POSITION PAIR
     ([UserConsole.upos]).  EXISTENTIAL here and named inside [gets]: a
     turn of the command loop begins wherever the previous line ended, no
     lemma between the loop head and the read needs the number, and the
     read is what moves it.  STATED HERE, above the read, because the
     read's own answer is what hands it back. *)
  (* ...AND THE LEASE TRAVELS WITH IT (lane KILL-PAY, K4(a)).  sh used to
     be lent the console reader token INSIDE its exit payload, which lived
     in [UkRun.urun]'s own row: the run carried [ukn_pay N (-1)] and the
     read's deposit was a wand from it (SH-LINE R1).  That row is GONE
     (lane SELF-KILL, P6) -- a killed process pays nothing it cannot pay,
     and the price of a kill is the KILLER's -- so the payload has nowhere
     to ride, and the lease moves into the program's OWN hand, beside the
     half of the position pair it already held.  The two positions agree
     ([UserConsole.upos_agree]): the payload's is existential and the
     program's is named, which is what makes a read's receipt a receipt at
     sh's own cursor.  sh spends the lease at its read (and gets it back)
     and at its own exit, where it is what init reaps.

     [upos_a] IS NOT REDUNDANT WITH THE LEASE even though both halves are
     now in one hand: the payload sh HANDS BACK at exit is
     [UserConsole.ucons_pay], whose left arm is the pair, and init reads
     the position off it without knowing sh's [n].  Merging them is a
     separate question and not this lane's. *)
  (* AT THE RECORD'S OWN PAYLOAD, not at [UserConsole.ucons_pay]: this
     file names no application and no console era, and the equation
     [ukn_pay N = ucons_pay fsc_cons γp T] is [UInitSh]'s to choose.  The
     read leaf's ONE discharge ([UShLine.ush_read_recv_leaf_holds]) is
     guarded by it and unfolds the lease there; sh's exit stub needs only
     [ukn_pay N (-1)] and takes it as it stands. *)
  Definition ush_at (n : nat) : iProp Σ :=
    (upos γp n ∗ ukn_pay N (-1))%I.

  Definition ush_pos : iProp Σ := (∃ n : nat, ush_at n)%I.

  (* ...and the ONE thing the exit stub wants off it *)
  Lemma ush_pos_pay : ush_pos -∗ ukn_pay N (-1).
  Proof using . rewrite /ush_pos /ush_at. iIntros "H". by iDestruct "H" as (n) "[_ $]". Qed.

  (* ===================================================================== *)
  (*  THE LEASE, UNBUNDLED (lane IO-LEAF, M5(3); D3's unbundling, whole   *)
  (*  at step 3).                                                          *)
  (*                                                                       *)
  (*  [ush_at] is the cursor AND sh's exit payload, and the payload is      *)
  (*  where the era's read credential rides (M5b).  The command loop does  *)
  (*  NOT hold it: between its entry and its exit sh holds the PIECES of   *)
  (*  the lease -- both halves of the position pair, the ring's reader     *)
  (*  token and the era's read half -- and [Pm n] is their name here, at   *)
  (*  count [n].  The payload is assembled only where sh actually leaves   *)
  (*  (the shut-fd-0 exit) or where the fork arm re-enters, and the three  *)
  (*  assemblers below are all this file knows about it: at a boundary     *)
  (*  with the banner-owed credential ([ush_at_of_pm_wb], the payload's    *)
  (*  own arm), at a boundary without it ([ush_at_of_pm], the affine arm   *)
  (*  step 4 kills), and under the taint anywhere.  A payload comes apart  *)
  (*  into the pieces ([ush_pm_of_at]).                                    *)
  (*                                                                       *)
  (*  A PARAMETER for [cn]'s reason: this file names no console era, and   *)
  (*  [UShLine.ush_mid] is the one instance.                               *)
  (* ===================================================================== *)
  Context (Pm : list (bv 8) -> iProp Σ).

  (* ...AND WHAT A READ IS ACTUALLY RUN ON: the pieces, or the taint.  A
     tainted turn holds no credential and no token, and the ring's own
     payment is free there ([ConsoleInv.cons_dirty_cred]) -- so the read
     still goes through, and its answer can only be the taint again. *)
  Definition ush_lease (I : list (bv 8)) : iProp Σ :=
    (Pm I ∨ (T ∗ ush_pos))%I.

  (* THE PAYLOAD KNOWS THE POSITION AND THE PIECES KNOW THE BYTES (project
     echo-any-line): [ush_at] is the console cursor, a NUMBER, because that
     is what the ring's own pair holds; the pieces are at the input whose
     length that number is.  Taking the input apart is what the one
     discharge ([UShLine]) does with its lower bound of the era's echoed
     list. *)
  Hypothesis ush_pm_of_at :
    forall n : nat,
      ⊢ ush_at n -∗ ∃ I : list (bv 8), ⌜length I = n⌝ ∗ ush_lease I.

  (* NO CREDENTIAL-LESS ASSEMBLER (lane EXEC-SEAM, (C)): a payload is
     assembled at a boundary WITH the banner-owed credential
     ([ush_at_of_pm_wb]) or under the taint, and nowhere else. *)

  (* ...AND UNDER THE TAINT THEY GO BACK TOGETHER ANYWHERE, because a
     tainted payload is free ([UserConsole.ucons_pay]'s right arm) and the
     count no longer says anything. *)
  Hypothesis ush_at_of_pm_taint :
    forall I : list (bv 8), ⊢ T -∗ Pm I -∗ ush_at (length I).

  (* ...AND WITH THE BANNER-OWED CREDENTIAL (step 3): the payload's own
     arm, which is what the shut-fd-0 exit hands /init when sh's fd 2 was
     closed.  [UShLine.ush_at_of_mid_wb] is the one discharge.  NO
     BOUNDARY PREMISE any more: "the input closed its last line" is what
     [Wb I] itself says now. *)
  Hypothesis ush_at_of_pm_wb :
    forall I : list (bv 8), ⊢ Pm I -∗ Wb I -∗ ush_at (length I).

  (* ...AND A LINE READ AT AN UNWRITTEN PROMPT IS THE TAINT (step 4): with
     fd 2 closed the prompt went nowhere, so the era still owes the round's
     banner ([Wb I]) -- while the pieces a whole line's read leaves carry
     the reader's receipt of that line, which says the writer's cursor is
     past the block the line closed.  The two contradict
     ([EchoLinks.wr_owed_read_refute]), so a walk that reads a line on the
     closed arm is on a tainted era.  [UShLine.ush_wb_read_holds] is the
     one discharge; the pieces come back for the taint arm's payload.

     THE LINE IS THE ONE THE LOOP READ, as its raw bytes [l] and the
     newline that closed it -- never a length. *)
  Hypothesis ush_wb_read :
    forall (I l : list (bv 8)),
      wl_nl ∉ l ->
      ⊢ Pm (I ++ l ++ [wl_nl]) -∗ Wb I -∗ Pm (I ++ l ++ [wl_nl]) ∗ T.

  (* ...AND WHAT A LINE'S READ DOES TO THE WRITE CREDENTIAL (lane IO-LEAF,
     M6a(3)): the one the prompt left at boundary [I] is the block-owed
     credential at [I ++ l ++ "\n"] once the line is read, on the pieces the
     read leaves -- and the pieces come back untouched.
     [UShLine.ush_mid_wc_read] is the one discharge.
     ...AND IT IS A FANCY UPDATE AT [top] (design claude-notes/design/
     app-pipe.md SS4.3k, lane SH-PIPE-ROUND-5 part 3).  Every era but one
     discharges it as the landed ENTAILMENT under [iModIntro]; the
     PIPELINE era's terminal arm cannot, and the reason is not a missing
     lemma: what it has to refute is `a line was delivered AFTER a
     fork-failure round', which is the input discipline's D4 -- a fact
     about the era's CLAIM, reachable only by opening the console
     invariant (and the round's own).  Both live at [top], which is why
     the mask is [top] and not a parameter: the step is taken at the
     read's return, a WP point, where [top] is the ambient mask
     ([RiscvPtsto]'s [mWP e := wp_triv top e]).  The ONE consumer inside
     this file is [ush_gets_done_line_at], which carries the update out
     to [wp_ksh_gets_loop]. *)
  Hypothesis ush_wc_read :
    forall (I l : list (bv 8)),
      wl_nl ∉ l ->
      ⊢ Pm (I ++ l ++ [wl_nl]) -∗ Wc I 2%nat ={⊤}=∗
        Pm (I ++ l ++ [wl_nl]) ∗ Wc (I ++ l ++ [wl_nl]) 3%nat.

  Lemma ush_pos_of_pm (I : list (bv 8)) : T -∗ Pm I -∗ ush_pos.
  Proof using HT ush_at_of_pm_taint.
    iIntros "#HT H". rewrite /ush_pos. iExists (length I).
    iApply (ush_at_of_pm_taint I with "HT H").
  Qed.

  Lemma ush_pos_of_lease_taint (I : list (bv 8)) :
    T -∗ ush_lease I -∗ ush_pos.
  Proof using HT ush_at_of_pm_taint.
    iIntros "#HT [H | [_ $]]". iApply (ush_pos_of_pm I with "HT H").
  Qed.

  (* ===================================================================== *)
  (*  SH'S CURSOR AT A LINE BOUNDARY (lane IO-LEAF, M5(3)).                 *)
  (*                                                                       *)
  (*  A turn of the command loop begins where the previous line ENDED, and  *)
  (*  "ended" is a fact about the INPUT: the bytes the era has echoed so    *)
  (*  far parse into the lines they closed and the one the user is in the   *)
  (*  middle of ([LineWords.wl_cut]), and a turn begins where that          *)
  (*  remainder is EMPTY ([rest_of I = []]).  There is no arithmetic in it  *)
  (*  any more: with a line per round a count says nothing about where a    *)
  (*  line starts, and the cut says everything.                            *)
  (*                                                                       *)
  (*  OR THE TAINT, for [ush_fd0]'s reason: under the taint sh proves       *)
  (*  nothing about its input and the boundary says nothing.                *)
  (* ===================================================================== *)
  (* ...AND THE ERA'S WRITE CREDENTIAL AT THAT BOUNDARY BESIDE IT (lane
     IO-LEAF, M6a(3)), at the SAME input: the prompt this turn prints is
     paid at the boundary the cursor stands on, and nothing else ties the
     two together.  [p] is how many prompt bytes are out -- the
     process state carries [0]; the read is entered at [2]. *)
  (* IN PIECES (step 3): what the loop holds at the boundary is [Pm I] and
     the credential slot, and no payload rides round the loop any more --
     it is assembled where sh leaves. *)
  Definition ush_posb (l : list fdstate) (p : nat) : iProp Σ :=
    ((∃ I : list (bv 8), ⌜rest_of I = []⌝ ∗ Pm I ∗ ush_wcp l I p)
     ∨ (T ∗ ush_pos))%I.

  Lemma ush_posb_of_wc (l : list fdstate) (p : nat) (I : list (bv 8)) :
    rest_of I = [] -> Pm I -∗ ush_wcp l I p -∗ ush_posb l p.
  Proof using .
    intro Hn. iIntros "H Hc". rewrite /ush_posb. iLeft. iExists I.
    iSplitR; [ by iPureIntro | ]. iFrame "H Hc".
  Qed.

  (* ...AND THE BODY'S SLOT, WITH THE LINE IT JUST READ PINNED TO IT
     (project echo-any-line).  What the fork lends its child is the block
     credential at the boundary the line closed, and the child runs the
     WORDS of that line: so the two have to be one resource, or the arm
     that applies the child's law holds a credential at [I] and a line
     [ws] with nothing saying [ws] is [I]'s last line.  [last_ws I = ws] is
     that equation, and the gets exit is the only producer of it
     ([ush_gets_done_line]).  The taint arm is the same as [ush_posb]'s and
     says nothing about either. *)
  (* THE INPUT'S LAST BODY, which is the one the slot's equation is about
     ([last_ws I] is its words). *)
  Definition ush_lastbody (I : list (bv 8)) : list (bv 8) :=
    bodies_of I !!! (nlines I - 1)%nat.

  (* ...AND THE THIRD CONJUNCT (the PROGRAM STREAM): that body IS SOME
     ADMISSIBLE LINE'S BODY.  [last_ws I = ws] says the slot's words are
     the input's last line's, and that is NOT enough to say which LINE the
     era filed -- a body with a trailing blank has the same words as the
     body without it, and only one of the two is a line's body.  An era
     with more than one line shape has to know which constructor its own
     input carries, and [FileDisc.fline_ok_echo] turns this conjunct plus
     [EchoDisc.line_ok] of the words into exactly that.  The echo era never
     reads it.
     THIS IS [fline_ok] AND NOT [fbody_ok] (lane ULINE-LPIPE): "in
     [FileDisc.parse_line]'s range" is the FILE era's reading of the same
     conjunct and is unsatisfiable for an era whose lines the file parser
     refuses -- the pipeline application's, whose body carries a bar.  Every
     consumer only ever spent it through [fbody_ok_echo], which holds at
     the weaker reading. *)
  Definition ush_posw (l : list fdstate) (ws : list (list (bv 8)))
      : iProp Σ :=
    ((∃ I : list (bv 8),
        ⌜rest_of I = [] /\ last_ws I = ws
         /\ FileDisc.fline_ok (ush_lastbody I)⌝
        ∗ Pm I ∗ ush_wcp l I 3%nat)
     ∨ (T ∗ ush_pos))%I.

  Lemma ush_posb_of_posw (l : list fdstate) (ws : list (list (bv 8))) :
    ush_posw l ws -∗ ush_posb l 3%nat.
  Proof using .
    rewrite /ush_posw /ush_posb. iIntros "[H | H]"; [ | iRight; iExact "H" ].
    iLeft. iDestruct "H" as (I) "([%Hr [%Hw %Hfb]] & H & Hc)". iExists I.
    iSplitR; [ by iPureIntro | ]. iFrame "H Hc".
  Qed.

  Lemma ush_posw_taint (l : list fdstate) (ws : list (list (bv 8))) :
    T -∗ ush_pos -∗ ush_posw l ws.
  Proof using HT. iIntros "#HT H". rewrite /ush_posw. iRight. iFrame "HT H". Qed.

  (* ...and it rides the console preamble's back edge, for the slot's own
     reason ([ush_wcp_cons]) *)
  Lemma ush_posb_cons (l : list fdstate) (k : nat) :
    length l = NSTD ->
    fd_lowest_closed l = Some k ->
    ush_posb l 0%nat -∗
    ush_posb (<[k := FdOpen true true (FdDevice CONSOLE)]> l) 0%nat.
  Proof using ush_wb_wc.
    intros Hlen Hk. rewrite /ush_posb. iIntros "[H | H]"; [ | iRight; iExact "H" ].
    iLeft. iDestruct "H" as (I) "(%Hn & H & Hc)". iExists I.
    iSplitR; [ by iPureIntro | ]. iFrame "H".
    iApply (ush_wcp_cons l k I Hlen Hk with "Hc").
  Qed.

  Lemma ush_posb_taint (l : list fdstate) (p : nat) :
    T -∗ ush_pos -∗ ush_posb l p.
  Proof using HT. iIntros "#HT H". rewrite /ush_posb. iRight. iFrame "HT H". Qed.

  (* the body's slot back at the head's index (step 4): a block owed with
     nothing chosen is a boundary credential ([ush_wc_blk_line]) -- the
     [cd] arm's back edge and a fork that failed re-enter through it; the
     closed arm does not reach the body ([p < 3]); the rest is as it was *)
  Lemma ush_posb_blk_line (l : list fdstate) :
    ush_posb l 3%nat -∗ ush_posb l 0%nat.
  Proof using ush_wc_blk_line.
    rewrite /ush_posb. iIntros "[H | H]"; [ | iRight; iExact "H" ].
    iLeft. iDestruct "H" as (I) "(%Hn & H & Hc)". iExists I.
    iSplitR; [ by iPureIntro | ]. iFrame "H".
    rewrite /ush_wcp.
    iDestruct "Hc" as "[[%Hrow Hc] | [%Hcl Hb]]".
    - iLeft. iSplitR; [ by iPureIntro | ].
      iApply (ush_wc_blk_line I with "Hc").
    - exfalso. destruct Hcl as [_ Hp]. lia.
  Qed.

  (* WHAT A READ ANSWERS, at three arms and not one (lane SH-LINE 2b).
     Which arm the caller gets is not its choice.

       THE WINDOW.  The [dd] bytes the call delivered are the ring's
       committed sequence at [n .. n+dd), in order ([cons_window] over
       [cons_chain]'s bound), each with the application's tag on the
       history it arrived at; and the position comes back at [n + dc],
       where the extra step is ACCOUNTED FOR rather than merely bounded
       ([UserConsole.ucons_swallow] at [False] -- the copy-out fault is
       eliminated inside the discharge, so what is left is [C('D')] with
       nothing delivered).  THE TWO CONTROL-FLOW ROWS (lane CONS-ROWS,
       B1/B4) are what a ONE-BYTE reader spends: at [dd = cap] the cursor
       moved by exactly [dd], so nothing is missing behind the call; at
       [dd = 0] against a positive request the byte WAS popped, which
       refutes [ucons_swallow]'s left arm and sends the caller to the
       reason on the right.  [Z.of_nat dd = bv_unsigned r] is what turns
       the [blez] the caller ran into either of those two cases.

       THE MINUS ONE.  consoleread answers -1 only when the process was
       killed, and a shut fd 0 answers -1 without reaching consoleread at
       all ([SpecFileread.fileread_extra_core]'s [FdClosed] arm, lane
       CLOSED-READ).  Neither pays a window; the token comes back
       somewhere.  It is not a placeholder: [gets] breaks on [cc < 1].

       THE TAINT.  A read taken WITHOUT the reader token moved the ring's
       committed count without moving the cursor, and the kernel cannot
       keep such a reader out ([ConsoleInv]'s "CONS-CURSOR RULING (7)").
       What it leaves is the dirty credential, which for a constraining
       application IS [T], and sh's continuation goes generic. *)
  (* THE INPUT'S DISCIPLINE IS A PARAMETER (lane LINK-GEN-4), on
     [ush_tag_law_at]'s and [ush_rest_line_at]'s pattern.  The shell knows
     nothing about WHICH discipline its era enforces -- it spends exactly
     three readings of it, all in [wp_kshg_loop] (the byte's value, the
     line a newline closes, the remainder's length) -- and the ECHO
     discipline is [EchoDisc.disc_input] while the file's is
     [FileDisc.disc_input_f].  Every landed name below is this at
     [disc_input], by definition, so no consumer moves. *)
  Definition ush_read_ans_at (Dsc : list (bv 8) -> Prop)
      (cnm : cons_names) (l : list fdstate) (r : mword 64)
      (cap : nat) (I : list (bv 8)) (g : nat -> bv 8) : iProp Σ :=
    ((∃ (dd dc : nat) (hs : list (list mobs))
        (sl : list (list mobs * bv 8)) (J : list (bv 8)),
        ⌜ Z.of_nat dd = bv_unsigned r ⌝ ∗
        ⌜ (dd <= cap)%nat ⌝ ∗
        ⌜ dd = cap -> dc = dd ⌝ ∗
        ⌜ dd = 0%nat -> (0 < cap)%nat -> dc = (dd + 1)%nat ⌝ ∗
        ⌜ cons_chain sl ⌝ ∗
        ucons_stored_lb cnm sl ∗
        ([∗ list] hh ∈ hs, riscv_rx_tag hh) ∗
        ⌜ cons_window sl (length I) dd g hs ⌝ ∗
        ucons_swallow cnm False sl dd dc ∗
        (* ...AND THE ERA'S OWN READING OF THE BYTES (lane IO-LEAF, M5(3);
           project echo-any-line).  The call moved the era's input on by
           the [dc] bytes [J], the byte it DELIVERED is the first of them,
           and the input so far is DISCIPLINED -- which is all the shell
           ever knew about what it reads and all it needs: the byte's value
           comes off [EchoDisc.disc_input_byte_val] and the line it closes
           off [EchoDisc.disc_input_snoc_nl]. *)
        ⌜ length J = dc ⌝ ∗
        ⌜ Dsc (I ++ J) ⌝ ∗
        ⌜ (0 < dd)%nat -> g 0%nat = J !!! 0%nat ⌝ ∗
        (* ...AND WHICH ARM OF [ush_fd0p] ANSWERED: a window is the
           CONSOLE's.  What it buys is the other arm's refutation below. *)
        ⌜ ush_fd0c l ⌝ ∗
        (* THE PIECES AND NOT THE PAYLOAD: mid-line the era's credential is
           at no boundary, so what comes back is [Pm] ([ush_at_of_pm_wb] puts
           it back together where the line ends). *)
        Pm (I ++ J))
     ∨ (⌜ r = (mword_of_int (-1) : mword 64) ⌝ ∗
        (* ...AND A [-1] IS THE SHUT ARM'S.  At an open readable console
           descriptor the answer is never [-1] (lane TRAP-ROWS, T2), which
           is what the leaf's console branch refutes it with; so this arm
           carries the row it was answered at, and a [gets] that has
           already taken a byte knows it cannot be here. *)
        ⌜ l !! 0%nat = Some FdClosed ⌝ ∗
        (* ...AND THE MINUS-ONE ARM SAYS NOTHING ABOUT WHY (lane SELF-KILL,
           §4b'; the owner's ruling of 2026-09-13).  read(0) answers -1 on
           exactly two grounds -- fd 0 is SHUT, or the process was KILLED
           -- and this arm USED to name both, carrying the application's
           kill credential from [SchedCtx.proc_pub]'s killed row through
           consoleread's post ([SpecFileread.console_receipt], KILL-PAY
           K4(b)).  That relay is WITHDRAWN: the killed row is
           per-incarnation and LINEAR now -- it holds the payment for THIS
           incarnation's death -- so a reader can neither copy it out nor
           relay it and [killed()] reports the flag alone.  NOTHING SPENT
           THE RELAY: this arm's only consumer is [ush_read_ans_pm], which
           takes the position, so what goes is a row nobody read. *)
        (* THE PIECES COME BACK UNMOVED: a shut fd 0 never reaches
           consoleread, so the lease is handed straight back at the input
           it went in at. *)
        Pm I)
     ∨ (T ∗ ush_pos))%I.

  Definition ush_read_ans (cnm : cons_names) (l : list fdstate) (r : mword 64)
      (cap : nat) (I : list (bv 8)) (g : nat -> bv 8) : iProp Σ :=
    ush_read_ans_at disc_input cnm l r cap I g.

  (* ...and the answer, weakened to the ONE thing the walk cannot do
     without: the position comes back.  This is what stands between R1'
     (the leaf sh runs on) and R2 (the line fact the loop accumulates). *)
  (* IN PIECES NOW (lane IO-LEAF, M5(3)): the walk between a line's first
     byte and its '\n' holds no payload, so what a receipt hands back is
     [Pm] at SOME input, or the taint. *)
  Lemma ush_read_ans_pm_at (Dsc : list (bv 8) -> Prop)
      (cnm : cons_names) (l : list fdstate) (r : mword 64)
      (cap : nat) (I : list (bv 8)) (g : nat -> bv 8) :
    ush_read_ans_at Dsc cnm l r cap I g -∗
    (∃ I' : list (bv 8), Pm I') ∨ (T ∗ ush_pos).
  Proof using HT.
    rewrite /ush_read_ans_at.
    iIntros "[Hw | [(_ & _ & Hp) | [#HT Hp]]]".
    - iDestruct "Hw" as (dd dc hs sl J)
        "(_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hp)".
      iLeft. iExists (I ++ J). iExact "Hp".
    - iLeft. iExists I. iExact "Hp".
    - iRight. iFrame "HT Hp".
  Qed.

  Definition ush_read_ans_pm (cnm : cons_names) (l : list fdstate)
      (r : mword 64) (cap : nat) (I : list (bv 8)) (g : nat -> bv 8) :
    ush_read_ans cnm l r cap I g -∗
    (∃ I' : list (bv 8), Pm I') ∨ (T ∗ ush_pos)
    := ush_read_ans_pm_at disc_input cnm l r cap I g.

  (* =================================================================== *)
  (*  THE [r = 0] ROUND'S REFUTATION, IN ONE STEP (lane SH-LINE 2b, L2).   *)
  (*                                                                      *)
  (*  [gets] breaks on [cc < 1], and what it has to know there is whether  *)
  (*  the ring's cursor moved anyway -- because if it did, the byte the    *)
  (*  NEXT read delivers is not the one after the last one delivered, and  *)
  (*  the line has a hole in it.  The cursor moves past an empty delivery  *)
  (*  only on the swallowing arm, whose reason at [fault := False] is      *)
  (*  [C('D')] -- and THAT is refuted into the taint: the swallowed byte's *)
  (*  history carries the input tag, the tag law reads it as the           *)
  (*  discipline or the taint, and every byte of a disciplined input is a  *)
  (*  body byte or a newline, never 0x04 ([disc_no_ctrl_d]).               *)
  (*                                                                      *)
  (*  So there is no third thing for sh to walk: either nothing was        *)
  (*  swallowed and the position is exactly where the loop left it, or the *)
  (*  application is tainted and sh's continuation is the generic one.     *)
  (*                                                                      *)
  (*  IT IS AN IMPLICATION AND NOT A DISJUNCTION NOW (lane CONS-ROWS, B4   *)
  (*  spent).  The old shape had to leave "nothing was swallowed" open,    *)
  (*  because nothing in the landed contract said what a zero-length read  *)
  (*  did to the cursor.  B4 does: at [dd = 0] against a POSITIVE request  *)
  (*  the byte WAS popped, so the caller arrives here already knowing      *)
  (*  [dc <> 0] -- and then the only arm left is [C('D')], and the only    *)
  (*  reading of it is the taint.  A zero-length read at a positive        *)
  (*  request IS the ^D-with-nothing-delivered arm.                        *)
  (* =================================================================== *)
  Lemma ush_swallow_taint (cnm : cons_names)
      (sl : list (list mobs * bv 8)) (dc : nat) :
    dc <> 0%nat ->
    ush_tag_law -∗ ucons_swallow cnm False sl 0%nat dc -∗ T.
  Proof using .
    intro Hdc. iIntros "#Hlaw Hsw". rewrite /ucons_swallow.
    iDestruct "Hsw" as "[%He | [%He H]]"; [ exfalso; exact (Hdc He) | ].
    iDestruct "H" as (h b) "(%Hen & _ & _ & Htg & Hwhy)".
    iDestruct "Hwhy" as "[%Hd | %Hf]"; [ | exfalso; exact Hf ].
    iApply ("Hlaw" $! h b with "[%] [%] Htg");
      [ exact Hen | exact (proj2 Hd) ].
  Qed.


  (* =================================================================== *)
  (*  §3  THE [gets] LOOP'S LINE INVARIANT                                *)
  (*                                                                      *)
  (*  [UkSh.wp_ksh_gets_loop] reads ONE byte per [read()] into the frame   *)
  (*  slot at s0-81 and copies it to buf[i], so after [i] turns the buffer *)
  (*  holds the [i] bytes the era has echoed since the boundary and the    *)
  (*  position stands at the end of them.  THOSE BYTES ARE A LIST [J]      *)
  (*  (project echo-any-line): the loop is assembling a line nobody knows  *)
  (*  in advance, so what it carries is the line so far and not an index   *)
  (*  into a constant.                                                    *)
  (*                                                                      *)
  (*  [dc = d] ON EVERY TURN THE LOOP CONTINUES ON, which is why the       *)
  (*  input is [I0 ++ J] and not [I0 ++ J ++ something].  The two rounds:   *)
  (*                                                                       *)
  (*   [r = 1] -- gets stored a byte and goes round again.  Then [d = 1],   *)
  (*     and the swallowing arm needs [d = 0] once the copy-out fault is    *)
  (*     eliminated, so [dc = 1] ([UserConsole.ucons_swallow_nofault_1]):   *)
  (*     the window grows by exactly one byte, with its tag.                *)
  (*                                                                       *)
  (*   [r = 0] -- gets breaks on [r < 1].  Then [d = 0], and the cursor     *)
  (*     may have moved by one: the byte the call swallowed is [C('D')].    *)
  (*     [ush_swallow_taint] below is the whole refutation -- the byte's    *)
  (*     tag reads as the discipline or the taint ([UkSh.ush_tag_law]),     *)
  (*     and a history whose input ends in 0x04 is not disciplined          *)
  (*     ([disc_no_ctrl_d]) -- so that round leaves the TAINT, and the      *)
  (*     line stops being the shell's business.                             *)
  (*                                                                       *)
  (*  [r < 0] is not observable at the U tier: consoleread answers -1 only  *)
  (*  when the process was killed, and a killed process is never resumed.   *)
  (*                                                                      *)
  (*  THE TAINT BRANCH IS ONE DISJUNCT AND CARRIES NO BYTES: after it the  *)
  (*  line is [∃ bytes] and sh's continuation is the generic one           *)
  (*  ([UkShFork.ushf_rest_of_body]'s taint case).                         *)
  (* =================================================================== *)
  (* IT IS THE LINE SO FAR (lane IO-LEAF, M5(3)), and not the ring window
     it used to be: what the walk above the loop wants is the BYTES, and
     the era's own reading of the receipt ([ush_read_ans]'s rows) gives
     them directly.  Five pure rows and the unbundled lease:

       -- [I0] IS A LINE BOUNDARY -- its cut leaves no remainder -- without
          which the bytes read since are not a line's bytes at all;
       -- [J] CARRIES NO NEWLINE, which the loop keeps because it BREAKS on
          one: a turn that went round again went round on a body byte;
       -- [J] STILL FITS THE BUFFER with its newline to come
          ([EchoDisc.line_max] is [sh_nbuf]), which is what refutes the
          buffer-full exit;
       -- fd 0 is the CONSOLE once a byte has been taken, which is what
          refutes the [-1] arm in the middle of a line;
       -- the bytes so far ARE [J], in order.

     ...and the DISCIPLINE of what has been typed, which rides the read
     receipts rather than the loop's own entry: the empty [J] asks for
     nothing (the boundary's own discipline is not in the loop's hand), and
     every byte after the first arrives with [disc_input] of the input it
     extends. *)
  Definition ush_gline_p_at (Dsc : list (bv 8) -> Prop)
      (l : list fdstate) (I0 J : list (bv 8))
      (f : nat -> bv 8) : Prop :=
    rest_of I0 = []
    /\ wl_nl ∉ J
    /\ (S (length J) < line_max)%nat
    /\ ((0 < length J)%nat -> ush_fd0c l)
    /\ (forall j : nat, (j < length J)%nat -> f j = J !!! j)
    /\ (J <> [] -> Dsc (I0 ++ J)).

  Definition ush_gline_p (l : list fdstate) (I0 J : list (bv 8))
      (f : nat -> bv 8) : Prop := ush_gline_p_at disc_input l I0 J f.

  Definition ush_gets_line_at (Dsc : list (bv 8) -> Prop)
      (l : list fdstate) (I0 J : list (bv 8))
      (f : nat -> bv 8) : iProp Σ :=
    ((⌜ush_gline_p_at Dsc l I0 J f⌝ ∗ Pm (I0 ++ J)) ∨ (T ∗ ush_pos))%I.

  Definition ush_gets_line (l : list fdstate) (I0 J : list (bv 8))
      (f : nat -> bv 8) : iProp Σ := ush_gets_line_at disc_input l I0 J f.

  (* THE ROWS ARE PURE, SO THEY COME OFF THE DISJUNCTION: what the walk
     carries past the read is the lease (linear) and "the rows, or the
     taint" (persistent, because both sides are).  That is what keeps the
     walk between the read and the '\n' test UNDUPLICATED. *)
  Lemma ush_gets_line_split_at (Dsc : list (bv 8) -> Prop)
      (l : list fdstate) (I0 J : list (bv 8))
      (f : nat -> bv 8) :
    ush_gets_line_at Dsc l I0 J f -∗
    ush_lease (I0 ++ J) ∗ (⌜ush_gline_p_at Dsc l I0 J f⌝ ∨ T).
  Proof.
    rewrite /ush_gets_line_at /ush_lease.
    iIntros "[[%Hp H] | [#HT H]]".
    - iSplitL "H"; [ by iLeft | iLeft; by iPureIntro ].
    - iSplitL "H"; [ iRight; iFrame "HT H" | iRight; iExact "HT" ].
  Qed.

  Definition ush_gets_line_split (l : list fdstate) (I0 J : list (bv 8))
      (f : nat -> bv 8) :
    ush_gets_line l I0 J f -∗
    ush_lease (I0 ++ J) ∗ (⌜ush_gline_p l I0 J f⌝ ∨ T)
    := ush_gets_line_split_at disc_input l I0 J f.

  (* the loop ENTERS at the empty line, which costs nothing but the
     boundary the command loop was already standing on *)
  Lemma ush_gets_line_0_at (Dsc : list (bv 8) -> Prop)
      (l : list fdstate) (I0 : list (bv 8))
      (f : nat -> bv 8) :
    rest_of I0 = [] ->
    Pm I0 -∗ ush_gets_line_at Dsc l I0 [] f.
  Proof using .
    intro Hr0. iIntros "Hp". rewrite /ush_gets_line_at. iLeft.
    iSplitR.
    { iPureIntro. rewrite /ush_gline_p_at. split_and!.
      - exact Hr0.
      - apply not_elem_of_nil.
      - cbn [length]. unfold line_max. lia.
      - cbn [length]. intro Hc. exfalso. lia.
      - cbn [length]. intros j Hj. exfalso. lia.
      - intro Hne. exfalso. exact (Hne eq_refl). }
    rewrite app_nil_r. iExact "Hp".
  Qed.

  Definition ush_gets_line_0 (l : list fdstate) (I0 : list (bv 8))
      (f : nat -> bv 8) :
    rest_of I0 = [] -> Pm I0 -∗ ush_gets_line l I0 [] f
    := ush_gets_line_0_at disc_input l I0 f.

  (* ...and the entry from a command-loop turn, which is where the
     boundary comes from *)
  (* ...ENTERED AT THE PROMPT'S END (lane IO-LEAF, M6a(3)): the credential
     the prompt left rides beside the line, untouched, to the exit that
     spends it ([ush_gets_done_line]). *)
  (* ...or the taint, at no slot at all: a tainted turn holds no credential
     and [gets]'s exits do not read one *)
  Lemma ush_gets_line_of_posb_at (Dsc : list (bv 8) -> Prop)
      (l : list fdstate) (f : nat -> bv 8) :
    ush_posb l 2%nat -∗
    ∃ I0 : list (bv 8),
      ush_gets_line_at Dsc l I0 [] f ∗ (ush_wcp l I0 2%nat ∨ T).
  Proof.
    iIntros "H". rewrite /ush_posb.
    iDestruct "H" as "[H | [#HT H]]"; last first.
    { iExists []. rewrite /ush_gets_line_at.
      iSplitL; [ iRight; iFrame "HT H" | iRight; iExact "HT" ]. }
    iDestruct "H" as (I) "(%Hn & H & Hc)".
    iExists I. iSplitL "H"; [ iApply (ush_gets_line_0_at Dsc l I f Hn with "H") | ].
    iLeft. iExact "Hc".
  Qed.

  Definition ush_gets_line_of_posb (l : list fdstate) (f : nat -> bv 8) :
    ush_posb l 2%nat -∗
    ∃ I0 : list (bv 8),
      ush_gets_line l I0 [] f ∗ (ush_wcp l I0 2%nat ∨ T)
    := ush_gets_line_of_posb_at disc_input l f.

  (* ...AND WHAT THE LOOP LEAVES: nothing read at all, or exactly one
     line -- WHICH one being what the word list says.  There is no third
     outcome on the untainted arm: the walk stops on '\n' (the line's last
     byte), on a shut fd 0 (which delivers no first byte either), or on the
     taint.  The slot it leaves carries the line's own words
     ([ush_posw]), which is the fork's whole claim on what its child runs. *)
  (* AT THE LINE THE ERA ADMITS (lane LINK-GEN-6), and not at a word list
     with [EchoDisc.body_ok]'s [cmd_echo] inside it.  The middle arm is
     what [UkSh.ush_rest_line_at] asks for verbatim -- a constructor the
     discipline admits, its words, and its bytes in the buffer -- so the
     loop hands the body law exactly its premise and the LINE predicate
     [Dl] is the only thing that widens. *)
  Definition ush_gets_done_at (Dl : FileDisc.uline -> Prop)
      (l : list fdstate) (i : nat) (f : nat -> bv 8) : iProp Σ :=
    ((⌜i = 0%nat⌝ ∗ ush_pos)
     ∨ (∃ lu : FileDisc.uline,
          ⌜Dl lu /\ i = length (FileDisc.line_bytes lu)
           /\ ush_line_at lu f 0%nat i⌝
          ∗ ush_posw l (FileDisc.uline_ws lu))
     ∨ (T ∗ ush_pos))%I.

  Definition ush_gets_done (l : list fdstate) (i : nat) (f : nat -> bv 8)
      : iProp Σ := ush_gets_done_at ush_line_echo l i f.

  (* the three ways out of the loop, as one constructor each *)
  (* NOTHING READ: the arm getcmd answers [-1] on, and sh exits with the
     lease -- this is the shut fd 0's exit, and what the loop's slot holds
     decides the payload.  The console arm is REFUTED (fd 0 is the console
     there); the closed arm's banner-owed credential goes into the payload
     ([ush_at_of_pm_wb]). *)
  Lemma ush_gets_done_0_at (Dl : FileDisc.uline -> Prop)
      (l : list fdstate) (I0 : list (bv 8))
      (f : nat -> bv 8) :
    l !! 0%nat = Some FdClosed ->
    Pm I0 -∗ ush_wcp l I0 2%nat -∗ ush_gets_done_at Dl l 0%nat f.
  Proof using ush_at_of_pm_wb.
    intro Hcl. iIntros "H Hwc". rewrite /ush_gets_done_at. iLeft.
    iSplitR; [ by iPureIntro | ].
    rewrite /ush_pos. iExists (length I0).
    rewrite /ush_wcp.
    iDestruct "Hwc" as "[[%Hrow _] | [_ Hb]]".
    - exfalso. exact (ush_fd0c_not_closed l (proj1 Hrow) Hcl).
    - iApply (ush_at_of_pm_wb I0 with "H Hb").
  Qed.

  Definition ush_gets_done_0 (l : list fdstate) (I0 : list (bv 8))
      (f : nat -> bv 8) :
    l !! 0%nat = Some FdClosed ->
    Pm I0 -∗ ush_wcp l I0 2%nat -∗ ush_gets_done l 0%nat f
    := ush_gets_done_0_at ush_line_echo l I0 f.

  (* ONE LINE READ: the credential the prompt left becomes the NEXT
     boundary's BLOCK-OWED one, on the pieces the read leaves
     ([ush_wc_read]) -- which is what the body's fork lends (step 4).  On
     the closed arm a line was read at an unwritten prompt: the taint
     ([ush_wb_read]).
     THE LINE IS THE BODY THE LOOP READ: [J] is an admissible body
     ([EchoDisc.body_ok], off the newline's own receipt), its words are
     [ws], and the buffer holds [wl_line ws] -- [J] and then the '\n' the
     loop stored.  The boundary after it is [I0 ++ J ++ "\n"], whose last
     line IS [ws] ([LineWords.last_ws_snoc_nl]), which is the equation the
     child's law is applied at. *)
  (* THE INPUT'S DISCIPLINE IS A PARAMETER HERE AND THE BODY'S IS NOT
     (lane LINK-GEN-4).  [body_ok J] is spent on BOTH its conjuncts -- the
     join's round trip and [line_ok (wl_words J)], the latter through
     [ush_line_is] inside [ush_gets_done] -- so the LINE predicate is a
     second axis, and it is the one [UkSh.ush_rest_line_at]'s [D] and
     [UkShFork.ushf_child_law_at]'s [Lp] already own (lane SH-CHILD). *)
  Lemma ush_gets_done_line_at (Dsc : list (bv 8) -> Prop)
      (Dl : FileDisc.uline -> Prop)
      (l : list fdstate) (I0 J : list (bv 8))
      (lu : FileDisc.uline) (f : nat -> bv 8) :
    ush_gline_p_at Dsc l I0 J f ->
    (* THE LINE THE NEWLINE CLOSED, as the era's discipline names it
       (lane LINK-GEN-6): a constructor it admits, whose words are the
       body's parse and whose bytes are the ones in the buffer.  This is
       [EchoDisc.body_ok J] one level up, and it is the reading a second
       era can supply -- [FileDisc.fbody_ok_line] gives it for all three
       constructors while [body_ok] gives it for one. *)
    Dl lu ->
    FileDisc.uline_ws lu = wl_words J ->
    length (FileDisc.line_bytes lu) = S (length J) ->
    ush_line_at lu f 0%nat (S (length J)) ->
    f (length J) = wl_nl ->
    ush_wcp l I0 2%nat -∗
    Pm (I0 ++ J ++ [wl_nl]) ={⊤}=∗
    ush_gets_done_at Dl l (S (length J)) f.
  Proof using HT ush_at_of_pm_taint ush_wb_read ush_wc_read.
    intros (Hr0 & Hnl & Hlt & Hfdc & Hby & _) HD Hws Hlen Hli Hfnl.
    (* the boundary the line closed, and its last line *)
    assert (Hrest : rest_of (I0 ++ J) = J).
    { rewrite /rest_of (wl_cut_app_nonl I0 J Hnl). cbn [snd].
      rewrite Hr0. reflexivity. }
    assert (Hlast : last_ws (I0 ++ J ++ [wl_nl]) = FileDisc.uline_ws lu).
    { rewrite app_assoc last_ws_snoc_nl Hrest Hws. reflexivity. }
    assert (Hrnl : rest_of (I0 ++ J ++ [wl_nl]) = []).
    { rewrite app_assoc. exact (rest_of_snoc_nl (I0 ++ J)). }
    (* ...AND THE BODY IT CLOSED PARSES (the PROGRAM STREAM): the buffer
       holds [J] and it holds [line_bytes lu], so [J] IS [lu]'s body, and
       a constructor's own body parses back to it
       ([FileDisc.parse_line_body]).  This is the conjunct
       [ush_posw] carries for an era with more than one line shape. *)
    assert (Hlb : ush_lastbody (I0 ++ J ++ [wl_nl]) = J).
    { rewrite /ush_lastbody app_assoc lastbody_snoc_nl. exact Hrest. }
    assert (Hlbl : length (FileDisc.line_body lu) = length J).
    { pose proof Hlen as HL.
      rewrite FileDisc.line_bytes_body length_app in HL.
      cbn [length] in HL. lia. }
    assert (Hbody : FileDisc.line_body lu = J).
    { apply list_eq. intro i.
      destruct (decide (i < length J)%nat) as [Hi | Hi].
      - rewrite (list_lookup_lookup_total_lt (FileDisc.line_body lu) i
                   ltac:(lia)).
        rewrite (list_lookup_lookup_total_lt J i Hi).
        f_equal.
        destruct Hli as (_ & _ & Hbytes).
        pose proof (Hbytes i ltac:(lia)) as Hfi.
        rewrite Nat.add_0_l in Hfi.
        pose proof (Hby i Hi) as Hji.
        assert (Hbl : FileDisc.line_bytes lu !!! i
                      = FileDisc.line_body lu !!! i).
        { rewrite FileDisc.line_bytes_body.
          rewrite (lookup_total_app_l (FileDisc.line_body lu) [wl_nl] i
                     ltac:(lia)).
          reflexivity. }
        rewrite <- Hbl. rewrite <- Hfi. exact Hji.
      - rewrite (lookup_ge_None_2 (FileDisc.line_body lu) i ltac:(lia)).
        rewrite (lookup_ge_None_2 J i ltac:(lia)). reflexivity. }
    assert (Hfbk : FileDisc.fline_ok (ush_lastbody (I0 ++ J ++ [wl_nl]))).
    { rewrite Hlb. rewrite <- Hbody.
      exact (FileDisc.fline_ok_of lu (proj1 Hli)). }
    rewrite /ush_gets_done_at.
    iIntros "Hwc H".
    iDestruct "Hwc" as "[[%Hrow Hc] | [%Hcl Hb]]".
    - iMod (ush_wc_read I0 J Hnl with "H Hc") as "[H Hc]".
      iModIntro. iRight. iLeft. iExists lu.
      iSplitR;
        [ iPureIntro; split; [ exact HD | split; [ by rewrite Hlen | exact Hli ] ] | ].
      rewrite /ush_posw. iLeft. iExists (I0 ++ J ++ [wl_nl]).
      iSplitR;
        [ iPureIntro; split;
          [ exact Hrnl | split; [ exact Hlast | exact Hfbk ] ] | ].
      iFrame "H". rewrite /ush_wcp. iLeft. iFrame "Hc". by iPureIntro.
    - iDestruct (ush_wb_read I0 J Hnl with "H Hb") as "[H #HT]".
      iModIntro. iRight. iRight. iFrame "HT".
      iApply (ush_pos_of_pm (I0 ++ J ++ [wl_nl]) with "HT H").
  Qed.

  (* ...AND THE ECHO ERA'S WITNESS, which is [EchoDisc.disc_input_snoc_nl]
     read as a line: [body_ok J] gives the constructor [LEcho (wl_words J)]
     and every row above. *)
  Lemma ush_line_echo_of_body (J : list (bv 8)) (f : nat -> bv 8) :
    body_ok J ->
    (forall j : nat, (j < length J)%nat -> f j = J !!! j) ->
    f (length J) = wl_nl ->
    ush_line_echo (FileDisc.LEcho (wl_words J))
    /\ FileDisc.uline_ws (FileDisc.LEcho (wl_words J)) = wl_words J
    /\ length (FileDisc.line_bytes (FileDisc.LEcho (wl_words J)))
       = S (length J)
    /\ ush_line_at (FileDisc.LEcho (wl_words J)) f 0%nat (S (length J)).
  Proof using .
    intros Hbody Hby Hfnl.
    assert (Hline : wl_line (wl_words J) = J ++ [wl_nl]).
    { rewrite /wl_line (proj1 Hbody). reflexivity. }
    assert (Hlen : length (wl_line (wl_words J)) = S (length J))
      by (rewrite Hline length_app; cbn [length]; lia).
    split; [ by exists (wl_words J) | ].
    split; [ reflexivity | ].
    split; [ rewrite FileDisc.line_bytes_echo; exact Hlen | ].
    rewrite /ush_line_at FileDisc.line_bytes_echo. split_and!.
    - exact (proj2 Hbody).
    - by rewrite Hlen.
    - intros j Hj. rewrite Nat.add_0_l.
      assert (Hnlat : (J ++ [wl_nl]) !!! length J = wl_nl).
      { pose proof (wl_lta_app_r J [wl_nl] 0%nat) as Hr.
        rewrite Nat.add_0_r in Hr. exact Hr. }
      destruct (Nat.eq_dec j (length J)) as [-> | Hne].
      + rewrite Hfnl Hline Hnlat. reflexivity.
      + rewrite (Hby j ltac:(lia)) Hline.
        symmetry. exact (wl_lta_app_l J [wl_nl] j ltac:(lia)).
  Qed.

  (* ...AND THE ECHO ERA'S [Hdsc_line], in one line: its discipline's
     newline closes an [EchoDisc.body_ok] body ([disc_input_snoc_nl]) and
     that body IS the constructor [LEcho] at its own parse. *)
  Lemma ush_disc_line_echo (I : list (bv 8)) (f : nat -> bv 8) :
    disc_input (I ++ [wl_nl]) ->
    (forall j : nat, (j < length (rest_of I))%nat -> f j = rest_of I !!! j) ->
    f (length (rest_of I)) = wl_nl ->
    exists lu : FileDisc.uline,
      ush_line_echo lu
      /\ FileDisc.uline_ws lu = wl_words (rest_of I)
      /\ length (FileDisc.line_bytes lu) = S (length (rest_of I))
      /\ ush_line_at lu f 0%nat (S (length (rest_of I))).
  Proof using .
    intros Hd Hby Hfnl.
    exists (FileDisc.LEcho (wl_words (rest_of I))).
    exact (ush_line_echo_of_body (rest_of I) f
             (disc_input_snoc_nl I Hd) Hby Hfnl).
  Qed.

  (* ...and the same exit on a tainted turn, at no slot *)
  Lemma ush_gets_done_line_t_at (Dl : FileDisc.uline -> Prop)
      (l : list fdstate) (I : list (bv 8)) (i : nat) (f : nat -> bv 8) :
    T -∗ Pm I -∗ ush_gets_done_at Dl l i f.
  Proof using HT ush_at_of_pm_taint.
    iIntros "#HT H". rewrite /ush_gets_done_at. iRight. iRight. iFrame "HT".
    iApply (ush_pos_of_pm I with "HT H").
  Qed.

  Lemma ush_gets_done_taint_at (Dl : FileDisc.uline -> Prop)
      (l : list fdstate) (i : nat) (f : nat -> bv 8) :
    T -∗ ush_pos -∗ ush_gets_done_at Dl l i f.
  Proof using HT.
    iIntros "#HT H". rewrite /ush_gets_done_at. iRight. iRight.
    iFrame "HT H".
  Qed.

  Definition ush_gets_done_line_t (l : list fdstate) (I : list (bv 8))
      (i : nat) (f : nat -> bv 8) :
    T -∗ Pm I -∗ ush_gets_done l i f
    := ush_gets_done_line_t_at ush_line_echo l I i f.

  Definition ush_gets_done_taint (l : list fdstate) (i : nat)
      (f : nat -> bv 8) :
    T -∗ ush_pos -∗ ush_gets_done l i f
    := ush_gets_done_taint_at ush_line_echo l i f.


  (* ...and the NUL [gets] plants past the line does not disturb it: the
     line's own bytes are all BELOW the index it is planted at. *)
  Lemma ush_gets_done_set_at (Dl : FileDisc.uline -> Prop)
      (l : list fdstate) (i : nat) (f : nat -> bv 8)
      (b : bv 8) :
    ush_gets_done_at Dl l i f -∗ ush_gets_done_at Dl l i (ush_set f i b).
  Proof.
    rewrite /ush_gets_done_at. iIntros "[[#Hi H] | [Hl | [#HT H]]]";
      [ iLeft; iFrame "Hi H" | | iRight; iRight; iFrame "HT H" ].
    iDestruct "Hl" as (lu) "[#Hl H]".
    iRight. iLeft. iExists lu. iFrame "H".
    iDestruct "Hl" as %[HD [Hi17 [Hok [Hlen Hby]]]]. iPureIntro.
    split; [ exact HD | ]. split; [ exact Hi17 | ].
    split; [ exact Hok | ]. split; [ exact Hlen | ].
    intros j Hj. rewrite (ush_set_lt f i (0 + j)%nat b ltac:(lia)).
    exact (Hby j Hj).
  Qed.

  Definition ush_gets_done_set (l : list fdstate) (i : nat) (f : nat -> bv 8)
      (b : bv 8) :
    ush_gets_done l i f -∗ ush_gets_done l i (ush_set f i b)
    := ush_gets_done_set_at ush_line_echo l i f b.

  (* =================================================================== *)
  (*  THE RECEIPT AT [cap = 1], READ INTO THE THREE OUTCOMES [gets] HAS   *)
  (*  (lane IO-LEAF, M5(3)).                                              *)
  (*                                                                     *)
  (*  A ONE-BYTE reader spends both control-flow rows: at [dd = cap] the  *)
  (*  cursor moved by exactly [dd], so the byte it took is the line's     *)
  (*  next one and the count is one further on; at [dd = 0] against a     *)
  (*  positive request the byte WAS popped, which is the ^D swallow and   *)
  (*  the tag's reading turns it into the taint.  So the answer to a      *)
  (*  one-byte read is: the next byte, a shut fd 0, or the taint.         *)
  (* =================================================================== *)
  Lemma ush_read_ans_1_at (Dsc : list (bv 8) -> Prop)
      (cnm : cons_names) (l : list fdstate) (r : mword 64)
      (I : list (bv 8)) (g : nat -> bv 8) :
    ush_tag_law -∗
    ush_read_ans_at Dsc cnm l r 1%nat I g -∗
    ((⌜ (0 < bv_signed r)%Z ⌝
      ∗ ⌜ Dsc (I ++ [g 0%nat]) ⌝
      ∗ ⌜ ush_fd0c l ⌝ ∗ Pm (I ++ [g 0%nat]))
     ∨ (⌜ (bv_signed r <= 0)%Z ⌝ ∗ ⌜ l !! 0%nat = Some FdClosed ⌝ ∗ Pm I)
     ∨ (T ∗ ush_pos)).
  Proof using HT ush_at_of_pm_taint.
    iIntros "#Hlaw [Hw | [(%Hm1 & %Hcl & Hp) | [#HT Hp]]]"; last first.
    { iRight. iRight. iFrame "HT Hp". }
    { iRight. iLeft.
      assert (Hs : bv_signed (mword_of_int (-1) : mword 64) = -1)
        by (vm_compute; reflexivity).
      iSplitR; [ iPureIntro; rewrite Hm1 Hs; lia | ].
      iSplitR; [ by iPureIntro | ]. iExact "Hp". }
    iDestruct "Hw" as (dd dc hs sl J)
      "(%Hdr & %Hdmax & %Hb1 & %Hb4 & %Hch & #Hlb & #Htags & %Hwin & Hsw
        & %HJl & %Hdisc & %Hbyte & %Hfdc & Hp)".
    destruct (Nat.eq_dec dd 0%nat) as [Hd0 | Hdn].
    - (* nothing delivered against a positive request: the ^D swallow *)
      subst dd.
      pose proof (Hb4 eq_refl ltac:(lia)) as Hdc1.
      iAssert T as "#HT";
        [ iApply (ush_swallow_taint cnm sl dc ltac:(lia) with "Hlaw Hsw") | ].
      iRight. iRight. iFrame "HT".
      iApply (ush_pos_of_pm (I ++ J) with "HT Hp").
    - assert (Hd1 : dd = 1%nat) by lia. subst dd.
      assert (Hdc1 : dc = 1%nat) by (apply Hb1; reflexivity).
      assert (HJ1 : length J = 1%nat) by (rewrite HJl; exact Hdc1).
      subst dc.
      (* ONE BYTE DELIVERED IS ONE BYTE MOVED: the era's input grew by the
         single byte the call copied out, so the list the receipt names IS
         the singleton of what the buffer now holds. *)
      assert (HJ : J = [g 0%nat]).
      { pose proof (Hbyte ltac:(lia)) as Hb0.
        revert HJ1 Hb0. destruct J as [| b [| b' J']]; intros HL Hb0';
          [ cbn in HL; discriminate HL | | cbn in HL; discriminate HL ].
        cbn in Hb0'. by rewrite Hb0'. }
      rewrite HJ in Hdisc. rewrite HJ.
      replace (Z.of_nat 1) with 1 in Hdr by lia.
      assert (Hre : (mword_of_int 1 : mword 64) = r)
        by (rewrite Hdr; apply moi_of_unsigned).
      iLeft.
      iSplitR.
      { iPureIntro.
        assert (Hs1 : bv_signed (mword_of_int 1 : mword 64) = 1)
          by (vm_compute; reflexivity).
        rewrite <- Hre, Hs1. lia. }
      iSplitR; [ by iPureIntro | ].
      iSplitR; [ by iPureIntro | ]. iExact "Hp".
  Qed.

  Definition ush_read_ans_1 (cnm : cons_names) (l : list fdstate)
      (r : mword 64) (I : list (bv 8)) (g : nat -> bv 8) :
    ush_tag_law -∗
    ush_read_ans cnm l r 1%nat I g -∗
    ((⌜ (0 < bv_signed r)%Z ⌝
      ∗ ⌜ disc_input (I ++ [g 0%nat]) ⌝
      ∗ ⌜ ush_fd0c l ⌝ ∗ Pm (I ++ [g 0%nat]))
     ∨ (⌜ (bv_signed r <= 0)%Z ⌝ ∗ ⌜ l !! 0%nat = Some FdClosed ⌝ ∗ Pm I)
     ∨ (T ∗ ush_pos))
    := ush_read_ans_1_at disc_input cnm l r I g.


  Definition ush_read_recv_leaf_at (Dsc : list (bv 8) -> Prop)
      (cnm : cons_names) (l : list fdstate)
      : iProp Σ :=
    (∀ (h : CpuId) (m : regfile) (pc : mword 64) (a : Z) (k cap : nat)
       (I : list (bv 8)) (f : nat -> bv 8) (avail : nat),
       ⌜ usysno m = USYS_read ⌝ -∗
       (* the descriptor is fd 0, which the row below says is the console
          or is shut *)
       ⌜ bv_signed (trunc32 (m !!! Regidx a0_idx)) = 0 ⌝ -∗
       ⌜ uint (m !!! Regidx a1_idx) = a ⌝ -∗
       ⌜ uint (m !!! Regidx a2_idx) = Z.of_nat cap ⌝ -∗
       ⌜ (cap <= k)%nat ⌝ -∗
       (* the kernel answers the SIGNED 32-bit count, so the request the
          caller made is the request file.c read only below the sign
          boundary ([UShLine.ush_count_is_cap] is the bridge) *)
       ⌜ (Z.of_nat cap < 2 ^ 31)%Z ⌝ -∗
       ⌜ ush_fd0p l ⌝ -∗
       ⌜ is_aligned_vaddr (Virtaddr (add_vec_int pc 4)) 2 = true ⌝ -∗
       uinstr_is γt pc false (ECALL tt) -∗
       ubytes γd a k f -∗
       ush_std l -∗
       (* THE LEASE AND THE POSITION, IN THE PROGRAM'S HAND (lane KILL-PAY,
          K4(a)): read's deposit is a plain one now, so what pays the
          console arm is what sh carries. *)
       ush_lease I -∗
       urun N h m pc avail -∗
       (∀ (h' : CpuId) (r : mword 64) (d : nat) (g : nat -> bv 8),
          ⌜ (d <= cap)%nat ⌝ -∗
          ⌜ forall j : nat, (d <= j < k)%nat -> g j = f j ⌝ -∗
          ush_std l -∗
          ush_read_ans_at Dsc cnm l r cap I g -∗
          ubytes γd a k g -∗
          urun N h' (<[Regidx a0_idx := r]> m)
            (add_vec_int pc 4) avail -∗
          mWP (Loop : expr riscv_lang)) -∗
       mWP (Loop : expr riscv_lang))%I.

  Definition ush_read_recv_leaf (cnm : cons_names) (l : list fdstate)
      : iProp Σ := ush_read_recv_leaf_at disc_input cnm l.

  (* THE RING'S NAMES, as a section variable: the program tier names no
     application and no era, and the ONE discharge of the Hypothesis below
     ([UShLine.ush_read_recv_leaf_holds]) is at [FsCfg.fsc_cons]. *)
  Context (cn : cons_names).

  (* ...AND THE INPUT'S DISCIPLINE, from here on (lane LINK-GEN-5).  The
     statements above take it as a parameter; the WALK spends it, and it
     spends exactly three readings of it -- no more.  They are named here
     so that a second era supplies three lemmas and nothing else.

      - [Hdsc_ncr] is the whole of what the byte's VALUE is read for: the
        walk's only use is to refute the carriage-return branch (it never
        needs the alphanumeric range), so the law is one negation and it
        is true of any discipline whose bytes are body bytes.
      - [Hdsc_nl] is the LINE the newline closed.  It is [body_ok]-valued
        because that is what [ush_gets_done_line] spends on BOTH its
        conjuncts; see the lane's findings -- this is the one of the three
        that a wider era cannot supply, and the reason is the LINE axis
        ([ush_line_is] inside [ush_gets_done]) and not the discipline.
      - [Hdsc_short] is the remainder's length, which is what refutes the
        buffer-full exit. *)
  Context (Dsc : list (bv 8) -> Prop).

  Hypothesis Hdsc_ncr : forall (I : list (bv 8)) (b : bv 8),
    Dsc (I ++ [b]) -> bv_unsigned b <> 13%Z.
  Hypothesis Hdsc_short : forall I : list (bv 8),
    Dsc I -> (S (length (rest_of I)) < line_max)%nat.

  (* ...AND THE LINE THE NEWLINE CLOSES (lane LINK-GEN-6).  This is what
     [Hdsc_nl] was, read one level up: [EchoDisc.body_ok (rest_of I)] is
     the ECHO era's witness and it carries [line_ok]'s [cmd_echo], which a
     [cat f] line does not.  The reading that travels is "the era admits
     some LINE whose words are the body's parse and whose bytes are the
     ones the buffer holds" -- echo supplies it from
     [EchoDisc.disc_input_snoc_nl] through [ush_line_echo_of_body], the
     file from [FileDisc.fbody_ok_line]. *)
  Context (Dl : FileDisc.uline -> Prop).

  Hypothesis Hdsc_line : forall (I : list (bv 8)) (f : nat -> bv 8),
    Dsc (I ++ [wl_nl]) ->
    (forall j : nat, (j < length (rest_of I))%nat -> f j = rest_of I !!! j) ->
    f (length (rest_of I)) = wl_nl ->
    exists lu : FileDisc.uline,
      Dl lu
      /\ FileDisc.uline_ws lu = wl_words (rest_of I)
      /\ length (FileDisc.line_bytes lu) = S (length (rest_of I))
      /\ ush_line_at lu f 0%nat (S (length (rest_of I))).

  Hypothesis ush_read_leaf :
    forall l : list fdstate, ⊢ ush_read_recv_leaf_at Dsc cn l.

  (* ---- read @0xc9e, SYS_read = 5 -- the WINDOW row's stub -------------- *)
  (* DEPENDS ON [ush_read_leaf].                                            *)
  Lemma wp_ksh_read (h : CpuId) (m : regfile) (a : Z) (k cap : nat)
      (I : list (bv 8)) (f : nat -> bv 8) (l : list fdstate) (avail : nat) :
    bv_signed (trunc32 (m !!! Regidx a0_idx)) = 0 ->
    uint (m !!! Regidx a1_idx) = a ->
    uint (m !!! Regidx a2_idx) = Z.of_nat cap ->
    (cap <= k)%nat ->
    (Z.of_nat cap < 2 ^ 31)%Z ->
    ush_fd0p l ->
    shk_code γt -∗
    ubytes γd a k f -∗
    ush_std l -∗
    ush_lease I -∗
    urun N h m (mword_of_int ShSyms.read) avail -∗
    (∀ (h' : CpuId) (ret : mword 64) (d : nat) (g : nat -> bv 8),
       ⌜ (d <= cap)%nat ⌝ -∗
       ⌜ forall j : nat, (d <= j < k)%nat -> g j = f j ⌝ -∗
       ush_std l -∗
       ush_read_ans_at Dsc cn l ret cap I g -∗
       ubytes γd a k g -∗
       urun N h'
         (<[Regidx a0_idx := ret]>
            (<[Regidx a7_idx := (mword_of_int 5 : mword 64)]> m))
         (ret_pc (m !!! Regidx ra_idx)) avail -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using Hdsc_ncr Hdsc_line Hdsc_short ush_read_leaf.
    intros Ha0 Ha1 Ha2 Hck Hc31 Hfd0.
    iIntros "#Hcode Hbs Hstd Hpos Hrun Hcont".
    rewrite shp_read.
    (* ---- 0xc9e  c.li a7,5 ---- *)
    iApply (wp_uk_cli N h m (mword_of_int 0xc9e)
              (mword_of_int 5 : mword 6) a7_idx avail
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) with "[] Hrun").
    { iApply (uis_shk_c9e with "Hcode"). }
    assert (Ec9e : add_vec_int (mword_of_int 0xc9e : mword 64) 2
                   = mword_of_int 0xca0)
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Em : <[Regidx a7_idx
                   := regval_into_reg (sign_extend' 64 (mword_of_int 5 : mword 6)
                                       : mword 64)]> m
                 = <[Regidx a7_idx := (mword_of_int 5 : mword 64)]> m)
      by (f_equal; apply bv_eq; vm_compute; reflexivity).
    rewrite Ec9e Em.
    iIntros (h1) "Hrun".
    set (m1 := <[Regidx a7_idx := (mword_of_int 5 : mword 64)]> m).
    assert (Ha1_1 : uint (m1 !!! Regidx a1_idx) = a).
    { rewrite /m1 (upd_ne m (Regidx a7_idx) (Regidx a1_idx)
                     (mword_of_int 5 : mword 64)
                     ltac:(vm_compute; discriminate)). exact Ha1. }
    assert (Ha2_1 : uint (m1 !!! Regidx a2_idx) = Z.of_nat cap).
    { rewrite /m1 (upd_ne m (Regidx a7_idx) (Regidx a2_idx)
                     (mword_of_int 5 : mword 64)
                     ltac:(vm_compute; discriminate)). exact Ha2. }
    assert (Ha0_1 : bv_signed (trunc32 (m1 !!! Regidx a0_idx)) = 0).
    { rewrite /m1 (upd_ne m (Regidx a7_idx) (Regidx a0_idx)
                     (mword_of_int 5 : mword 64)
                     ltac:(vm_compute; discriminate)). exact Ha0. }
    (* ---- 0xca0  ecall -- THE RECEIPT-KEEPING READ ---- *)
    iPoseProof (ush_read_leaf l) as "Hrl".
    rewrite /ush_read_recv_leaf.
    iApply ("Hrl" $! h1 m1 (mword_of_int 0xca0) a k cap I f avail
              with "[%] [%] [%] [%] [%] [%] [%] [%] [] Hbs Hstd Hpos Hrun").
    { unfold m1, usysno.
      rewrite (upd_eq m (Regidx a7_idx) (mword_of_int 5 : mword 64)).
      vm_compute; reflexivity. }
    { exact Ha0_1. }
    { exact Ha1_1. }
    { exact Ha2_1. }
    { exact Hck. }
    { exact Hc31. }
    { exact Hfd0. }
    { vm_compute; reflexivity. }
    { iApply (uis_shk_ca0 with "Hcode"). }
    assert (Eca0 : add_vec_int (mword_of_int 0xca0 : mword 64) 4
                   = mword_of_int 0xca4)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Eca0.
    iIntros (h2 ret d g) "%Hd %Hg Hstd Hans Hbs Hrun".
    set (m2 := <[Regidx a0_idx := ret]> m1).
    (* ---- 0xca4  c.jr ra ---- *)
    assert (Hra : m2 !!! Regidx ra_idx = m !!! Regidx ra_idx).
    { rewrite /m2 /m1.
      exact (eq_trans
               (upd_ne m1 (Regidx a0_idx) (Regidx ra_idx) ret
                  ltac:(vm_compute; discriminate))
               (upd_ne m (Regidx a7_idx) (Regidx ra_idx)
                  (mword_of_int 5 : mword 64)
                  ltac:(vm_compute; discriminate))). }
    iApply (wp_uk_cjr N h2 m2 (mword_of_int 0xca4) ra_idx
              (ret_pc (m !!! Regidx ra_idx)) avail
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hra; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_ca4 with "Hcode"). }
    iIntros (h3) "Hrun".
    iApply ("Hcont" $! h3 ret d g with "[%] [%] Hstd Hans Hbs Hrun");
      [ exact Hd | exact Hg ].
  Qed.


  (* ===================================================================== *)
  (* memset @0xa5c -- 16 instructions, one byte loop.  UNCONDITIONAL.       *)
  (*                                                                       *)
  (* The contract deliberately FORGETS what was written: getcmd calls it as *)
  (* [memset(buf, 0, 100)] only to clear the line, and what the command     *)
  (* loop needs afterwards is that it still OWNS the buffer, not what is in *)
  (* it -- gets overwrites a prefix and plants the NUL that main's scan     *)
  (* stops on.  Dropping the contents halves the loop invariant: it carries *)
  (* the two addresses and nothing about the bytes.                         *)
  (* ===================================================================== *)

  (* a callee-saved register is none of the ones a caller may clobber *)
  Local Lemma ucs_ne (r q : mword 5) :
    ucallee_saved_idx r = true -> ucallee_saved_idx q = false ->
    Regidx r <> Regidx q.
  Proof using .
    intros Hr Hq He.
    assert (Hrr : r = q) by (injection He; trivial).
    rewrite Hrr Hq in Hr. discriminate.
  Qed.

  (* the byte loop, 0xa70..0xa76:
       sb a1,0(a5) ; c.addi a5,a5,1 ; bne a5,a4,0xa70
     [k] is the number of bytes still to come AFTER this one, so the
     measure is the loop's own trip count and the [bne] decides it. *)
  (* THE LOOP CARRIES THE BYTE IT IS WRITING.  [memset] does not merely
     leave SOME contents behind, it leaves [c] at every index -- and the
     [NULL] cap at an [execcmd] node's argv is exactly that fact, so the
     postcondition names the byte rather than existentially quantifying it.
     The invariant is the prefix already written ([Hpre]); the constant is
     stable across iterations because the loop writes only a5. *)
  Local Lemma wp_ksh_memset_loop (a : Z) (Nb : nat) (c : bv 8) :
    forall (k j : nat) (h : CpuId) (mc : regfile) (f : nat -> bv 8) (nn : nat),
    (Nb = j + 1 + k)%nat ->
    0 <= a -> a + Z.of_nat Nb < Z64 ->
    nth_byte (mc !!! Regidx a1_idx) 0 = c ->
    (forall i : nat, (i < j)%nat -> f i = c) ->
    mc !!! Regidx a5_idx = mword_of_int (a + Z.of_nat j) ->
    mc !!! Regidx a4_idx = mword_of_int (a + Z.of_nat Nb) ->
    shk_code γt -∗
    ubytes γd a Nb f -∗
    urun N h mc (mword_of_int 0xa70) nn -∗
    (ubytes γd a Nb (fun _ => c) -∗
       ∀ (h' : CpuId) (mc' : regfile),
         ⌜ forall r : mword 5, Regidx r <> Regidx a5_idx ->
             mc' !!! Regidx r = mc !!! Regidx r ⌝ -∗
         urun N h' mc' (mword_of_int 0xa7a) nn -∗
         mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros k. induction k as [| k IH ];
      intros j h mc f nn HN Ha0 Ha64 Hc Hpre Ha5 Ha4;
      iIntros "#Hcode Hbs Hrun Hcont".
    - (* the LAST byte: after it a5 = a4 and the branch falls through *)
      iDestruct (ush_bytes_upd a Nb j f ltac:(lia) with "Hbs") as "[Hb Hcl]".
      iApply (wp_uk_sb N h mc (mword_of_int 0xa70)
                (mword_of_int 0 : mword 12) a5_idx a1_idx
                (a + Z.of_nat j) (f j) nn
                ltac:(rewrite Ha5 (uint_moi (a + Z.of_nat j) ltac:(unfold Z64 in *; lia));
                      vm_compute uoff_i12; lia)
                with "[] Hb Hrun").
      { iApply (uis_shk_a70 with "Hcode"). }
      iIntros "Hb".
      iDestruct ("Hcl" $! (nth_byte (mc !!! Regidx a1_idx) 0) with "Hb") as "Hbs".
      assert (Ea70 : add_vec_int (mword_of_int 0xa70 : mword 64) 4
                     = mword_of_int 0xa74)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite Ea70. iIntros (h1) "Hrun".
      (* ---- 0xa74  c.addi a5,a5,1 ---- *)
      assert (E1 : (sign_extend' 64 (mword_of_int 1 : mword 6) : mword 64)
                   = mword_of_int 1)
        by (apply bv_eq; vm_compute; reflexivity).
      iApply (wp_uk_caddi N h1 mc (mword_of_int 0xa74)
                (mword_of_int 1 : mword 6) a5_idx
                (mword_of_int (a + Z.of_nat j + 1)) nn
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite Ha5 E1 moi_add; reflexivity)
                with "[] Hrun").
      { iApply (uis_shk_a74 with "Hcode"). }
      assert (Ea74 : add_vec_int (mword_of_int 0xa74 : mword 64) 2
                     = mword_of_int 0xa76)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite Ea74. iIntros (h2) "Hrun".
      set (m1 := <[Regidx a5_idx
                   := regval_into_reg (mword_of_int (a + Z.of_nat j + 1)
                                       : mword 64)]> mc).
      assert (Hpres : forall r : mword 5, Regidx r <> Regidx a5_idx ->
                        m1 !!! Regidx r = mc !!! Regidx r)
        by (intros r Hr; exact (upd_ne mc (Regidx a5_idx) (Regidx r) _ Hr)).
      assert (Ha5_1 : m1 !!! Regidx a5_idx
                      = mword_of_int (a + Z.of_nat j + 1))
        by exact (upd_eq mc (Regidx a5_idx)
                    (regval_into_reg (mword_of_int (a + Z.of_nat j + 1)
                                      : mword 64))).
      assert (Ha4_1 : m1 !!! Regidx a4_idx = mword_of_int (a + Z.of_nat Nb))
        by (rewrite (Hpres a4_idx ltac:(vm_compute; discriminate)); exact Ha4).
      (* ---- 0xa76  bne a5,a4 -- NOT taken: this was the last byte ---- *)
      assert (Htk : false = uv_btaken BNE (m1 !!! Regidx a5_idx)
                              (m1 !!! Regidx a4_idx)).
      { cbn [uv_btaken]. rewrite Ha5_1 Ha4_1.
        rewrite (moi_neq_vec (a + Z.of_nat j + 1) (a + Z.of_nat Nb)
                   ltac:(unfold Z64 in *; lia) ltac:(unfold Z64 in *; lia)).
        symmetry. apply negb_false_iff. apply Z.eqb_eq. lia. }
      iApply (wp_uk_btype N h2 m1 (mword_of_int 0xa76)
                (mword_of_int 8186 : mword 13) a4_idx a5_idx BNE false
                (mword_of_int 0xa70) nn
                Htk
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(discriminate)
                with "[] Hrun").
      { iApply (uis_shk_a76 with "Hcode"). }
      assert (Ea76 : add_vec_int (mword_of_int 0xa76 : mword 64) 4
                     = mword_of_int 0xa7a)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite Ea76. iIntros (h3) "Hrun".
      iApply ("Hcont" with "[Hbs] [] Hrun").
      { iApply (ush_bytes_ext (DfracOwn 1) a Nb
                  (ush_set f j (nth_byte (mc !!! Regidx a1_idx) 0))
                  (fun _ => c) with "Hbs").
        intros i Hi. unfold ush_set.
        destruct (Nat.eqb_spec i j) as [-> | Hne];
          [ exact Hc | apply Hpre; lia ]. }
      { iPureIntro. exact Hpres. }
    - (* a body byte: a5 moves on and the branch goes back to 0xa70 *)
      iDestruct (ush_bytes_upd a Nb j f ltac:(lia) with "Hbs") as "[Hb Hcl]".
      iApply (wp_uk_sb N h mc (mword_of_int 0xa70)
                (mword_of_int 0 : mword 12) a5_idx a1_idx
                (a + Z.of_nat j) (f j) nn
                ltac:(rewrite Ha5 (uint_moi (a + Z.of_nat j) ltac:(unfold Z64 in *; lia));
                      vm_compute uoff_i12; lia)
                with "[] Hb Hrun").
      { iApply (uis_shk_a70 with "Hcode"). }
      iIntros "Hb".
      iDestruct ("Hcl" $! (nth_byte (mc !!! Regidx a1_idx) 0) with "Hb") as "Hbs".
      assert (Ea70 : add_vec_int (mword_of_int 0xa70 : mword 64) 4
                     = mword_of_int 0xa74)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite Ea70. iIntros (h1) "Hrun".
      assert (E1 : (sign_extend' 64 (mword_of_int 1 : mword 6) : mword 64)
                   = mword_of_int 1)
        by (apply bv_eq; vm_compute; reflexivity).
      iApply (wp_uk_caddi N h1 mc (mword_of_int 0xa74)
                (mword_of_int 1 : mword 6) a5_idx
                (mword_of_int (a + Z.of_nat j + 1)) nn
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite Ha5 E1 moi_add; reflexivity)
                with "[] Hrun").
      { iApply (uis_shk_a74 with "Hcode"). }
      assert (Ea74 : add_vec_int (mword_of_int 0xa74 : mword 64) 2
                     = mword_of_int 0xa76)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite Ea74. iIntros (h2) "Hrun".
      set (m1 := <[Regidx a5_idx
                   := regval_into_reg (mword_of_int (a + Z.of_nat j + 1)
                                       : mword 64)]> mc).
      assert (Hpres : forall r : mword 5, Regidx r <> Regidx a5_idx ->
                        m1 !!! Regidx r = mc !!! Regidx r)
        by (intros r Hr; exact (upd_ne mc (Regidx a5_idx) (Regidx r) _ Hr)).
      assert (Ha5_1 : m1 !!! Regidx a5_idx
                      = mword_of_int (a + Z.of_nat (j + 1))).
      { replace (a + Z.of_nat (j + 1)) with (a + Z.of_nat j + 1) by lia.
        exact (upd_eq mc (Regidx a5_idx)
                 (regval_into_reg (mword_of_int (a + Z.of_nat j + 1)
                                   : mword 64))). }
      assert (Ha4_1 : m1 !!! Regidx a4_idx = mword_of_int (a + Z.of_nat Nb))
        by (rewrite (Hpres a4_idx ltac:(vm_compute; discriminate)); exact Ha4).
      assert (Htk : true = uv_btaken BNE (m1 !!! Regidx a5_idx)
                             (m1 !!! Regidx a4_idx)).
      { cbn [uv_btaken]. rewrite Ha5_1 Ha4_1.
        rewrite (moi_neq_vec (a + Z.of_nat (j + 1)) (a + Z.of_nat Nb)
                   ltac:(unfold Z64 in *; lia) ltac:(unfold Z64 in *; lia)).
        symmetry. apply negb_true_iff. apply Z.eqb_neq. lia. }
      iApply (wp_uk_btype N h2 m1 (mword_of_int 0xa76)
                (mword_of_int 8186 : mword 13) a4_idx a5_idx BNE true
                (mword_of_int 0xa70) nn
                Htk
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(intros _; vm_compute; reflexivity)
                with "[] Hrun").
      { iApply (uis_shk_a76 with "Hcode"). }
      iIntros (h3) "Hrun".
      iApply (IH (j + 1)%nat h3 m1
                (ush_set f j (nth_byte (mc !!! Regidx a1_idx) 0)) nn
                ltac:(lia) Ha0 Ha64
                ltac:(rewrite (Hpres a1_idx ltac:(vm_compute; discriminate));
                      exact Hc)
                ltac:(intros i Hi; unfold ush_set;
                      destruct (Nat.eqb_spec i j) as [-> | Hne];
                        [ exact Hc | apply Hpre; lia ])
                Ha5_1 Ha4_1
                with "Hcode Hbs Hrun").
      iIntros "Hbs" (h4 mc') "%Hpres' Hrun".
      iApply ("Hcont" with "Hbs [] Hrun").
      iPureIntro. intros r Hr. rewrite (Hpres' r Hr). exact (Hpres r Hr).
  Qed.


  (* two register indices are equal when their numbers are *)
  Local Lemma ush_ridx_eq (r q : mword 5) : uint r = uint q -> Regidx r = Regidx q.
  Proof using .
    intro H. f_equal. apply bv_eq. rewrite <- !(uint_unsigned_n 5). exact H.
  Qed.

  Local Lemma ush_ridx_ne (r q : mword 5) : uint r <> uint q -> Regidx r <> Regidx q.
  Proof using .
    intros H He. apply H.
    assert (Hrq : r = q) by (injection He; trivial). rewrite Hrq. reflexivity.
  Qed.

  (* ===================================================================== *)
  (* memset AT A POINTER THE PROCESS CANNOT WRITE (lane SELF-KILL, step 5). *)
  (*                                                                       *)
  (* [wp_ksh_memset] above owns the buffer.  This one owns a TEXT byte at   *)
  (* the same address instead, which is the opposite fact: the page is      *)
  (* mapped X-and-not-W, so the loop's FIRST store (0xa70, [sb a1,0(a5)])   *)
  (* takes a store page fault and the kernel kills the process.  The walk   *)
  (* is memset's prologue verbatim -- the sixteen bytes of frame are        *)
  (* pushed and never popped -- and then it stops.                          *)
  (*                                                                       *)
  (* THE CALLER IS sh's FORKED CHILD after [malloc] returned NULL:          *)
  (* [execcmd] does not test the result and goes straight into             *)
  (* [memset(cmd, 0, 168)] at [cmd = 0], and VA 0 is sh's own first text    *)
  (* byte ([ShSyms.getcmd = 0]).  The price is the child's exit payload at  *)
  (* the kill status, free at its trivial record                            *)
  (* ([UkRun.ukn_pay_free_of_triv]).                                        *)
  (* ===================================================================== *)
  Lemma wp_ksh_memset_null (h : CpuId) (m : regfile) (a : Z) (Nb : nat)
      (b0 : bv 8) (nn : nat) :
    0 <= a -> a + Z.of_nat Nb < 2 ^ 38 ->
    m !!! Regidx a0_idx = mword_of_int a ->
    m !!! Regidx a2_idx = mword_of_int (Z.of_nat Nb) ->
    (0 < Nb)%nat -> Z.of_nat Nb < Z31 ->
    shk_code γt -∗
    utext γt a b0 -∗
    (* THE EXIT PAYLOAD, AS A RESOURCE (lane IO-LEAF, M3c).  It was the
       Coq-level [(⊢ ukn_pay N (-1))] -- "the payload is free at this
       record" -- which is exactly what a child that dies at a LINEAR
       payload cannot say.  The engine leaf below took the same step
       (TRAP-ROWS M2 part 2, [UkRunMem.wp_uk_sb_denied]); this is the same
       premise one level up, and a caller that still has the free payload
       is one [iPoseProof] away from it. *)
    ukn_pay N (-1) -∗
    urun N h m (mword_of_int ShSyms.memset) (2 + nn) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Halo Hahi0 Ha0 Ha2 HN0 HN31. iIntros "#Hcode #Ht0 Hpay Hrun".
    rewrite shp_memset.
    iDestruct (urun_stack with "Hrun") as %[Hal8 Hroom].
    assert (Hahi : a + Z.of_nat Nb < 274877906944)
      by (change (2 ^ 38) with 274877906944 in Hahi0; lia).
    remember (m !!! Regidx csp_rs1) as sp0 eqn:Hsp0.
    assert (Hsp : m !!! Regidx csp_rs1 = sp0) by (symmetry; exact Hsp0).
    clear Hsp0.
    assert (Hlo : 16 <= uint sp0) by lia.
    set (vra := m !!! Regidx ra_idx).
    set (vs0 := m !!! Regidx s0_idx).
    assert (Hbsp1 : bv_unsigned (add_vec_int sp0 (- (8 * Z.of_nat 2)))
                    = bv_unsigned sp0 - 16).
    { replace (- (8 * Z.of_nat 2)) with (-16) by lia.
      exact (uv_avi_neg sp0 16 ltac:(lia) ltac:(rewrite <- uint_unsigned; lia)). }
    assert (Hsp16 : uint (add_vec_int sp0 (- (8 * Z.of_nat 2))) = uint sp0 - 16)
      by (rewrite !uint_unsigned; exact Hbsp1).
    assert (Ho8 : uoff_sdsp (mword_of_int 1 : mword 6) = 8)
      by (vm_compute; reflexivity).
    assert (Ho0 : uoff_sdsp (mword_of_int 0 : mword 6) = 0)
      by (vm_compute; reflexivity).
    (* ---- 0xa5c  c.addi sp,sp,-16 -- THE PUSH ---- *)
    iApply (wp_uk_caddi_sp_dn N h m (mword_of_int 0xa5c)
              (mword_of_int 48 : mword 6) 2 nn
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_a5c with "Hcode"). }
    assert (Ea5c : add_vec_int (mword_of_int 0xa5c : mword 64) 2
                   = mword_of_int 0xa5e)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Hsp ustack_2 Ea5c.
    iIntros "(_ & [%v8 Hw8] & [%v0 Hw0])".
    iIntros (h1) "Hrun".
    set (m1 := <[Regidx csp_rs1
                 := regval_into_reg (add_vec_int sp0 (- (8 * Z.of_nat 2)))]> m).
    assert (Hsp1 : m1 !!! Regidx csp_rs1 = add_vec_int sp0 (- (8 * Z.of_nat 2)))
      by exact (upd_eq m (Regidx csp_rs1)
                  (regval_into_reg (add_vec_int sp0 (- (8 * Z.of_nat 2))))).
    assert (Hm1 : forall r : mword 5, Regidx r <> Regidx csp_rs1 ->
                    m1 !!! Regidx r = m !!! Regidx r)
      by (intros r Hr; exact (upd_ne m (Regidx csp_rs1) (Regidx r) _ Hr)).
    (* ---- 0xa5e  c.sdsp ra,8(sp) ---- *)
    iApply (wp_uk_csdsp N h1 m1 (mword_of_int 0xa5e)
              (mword_of_int 1 : mword 6) ra_idx (uint sp0 - 8) v8 nn
              ltac:(rewrite Hsp1 Hsp16 Ho8; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              with "[] Hw8 Hrun").
    { iApply (uis_shk_a5e with "Hcode"). }
    iIntros "Hw8".
    rewrite (Hm1 ra_idx ltac:(vm_compute; discriminate)).
    assert (Ea5e : add_vec_int (mword_of_int 0xa5e : mword 64) 2
                   = mword_of_int 0xa60)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Ea5e. iIntros (h2) "Hrun".
    (* ---- 0xa60  c.sdsp s0,0(sp) ---- *)
    iApply (wp_uk_csdsp N h2 m1 (mword_of_int 0xa60)
              (mword_of_int 0 : mword 6) s0_idx (uint sp0 - 16) v0 nn
              ltac:(rewrite Hsp1 Hsp16 Ho0; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              with "[] Hw0 Hrun").
    { iApply (uis_shk_a60 with "Hcode"). }
    iIntros "Hw0".
    rewrite (Hm1 s0_idx ltac:(vm_compute; discriminate)).
    assert (Ea60 : add_vec_int (mword_of_int 0xa60 : mword 64) 2
                   = mword_of_int 0xa62)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Ea60. iIntros (h3) "Hrun".
    (* ---- 0xa62  c.addi4spn s0,sp,16 (s0 is dead until the epilogue) ---- *)
    iApply (wp_uk_caddi4spn N h3 m1 (mword_of_int 0xa62)
              (mword_of_int 0 : mword 3) (mword_of_int 4 : mword 8) s0_idx
              (add_vec (m1 !!! Regidx csp_rs1)
                 (sign_extend' 64 (caddi4spn_imm (mword_of_int 4 : mword 8)))) nn
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
              eq_refl
              with "[] Hrun").
    { iApply (uis_shk_a62 with "Hcode"). }
    assert (Ea62 : add_vec_int (mword_of_int 0xa62 : mword 64) 2
                   = mword_of_int 0xa64)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Ea62. iIntros (h4) "Hrun".
    set (m2 := <[Regidx s0_idx
                 := regval_into_reg
                      (add_vec (m1 !!! Regidx csp_rs1)
                         (sign_extend' 64
                            (caddi4spn_imm (mword_of_int 4 : mword 8))))]> m1).
    assert (Hm2 : forall r : mword 5, Regidx r <> Regidx s0_idx ->
                    m2 !!! Regidx r = m1 !!! Regidx r)
      by (intros r Hr; exact (upd_ne m1 (Regidx s0_idx) (Regidx r) _ Hr)).
    assert (Hsp2 : m2 !!! Regidx csp_rs1 = add_vec_int sp0 (- (8 * Z.of_nat 2)))
      by (rewrite (Hm2 csp_rs1 ltac:(vm_compute; discriminate)); exact Hsp1).
    assert (Ha2_2 : m2 !!! Regidx a2_idx = mword_of_int (Z.of_nat Nb)).
    { rewrite (Hm2 a2_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm1 a2_idx ltac:(vm_compute; discriminate)). exact Ha2. }
    assert (Ha0_2 : m2 !!! Regidx a0_idx = mword_of_int a).
    { rewrite (Hm2 a0_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm1 a0_idx ltac:(vm_compute; discriminate)). exact Ha0. }
    (* ---- 0xa64  c.beqz a2 -- the count is nonzero, so NOT taken ---- *)
    assert (Htk64 : false = eq_vec (m2 !!! Regidx a2_idx) zero_reg).
    { rewrite Ha2_2.
      rewrite (moi_eq_zero (Z.of_nat Nb) ltac:(unfold Z31, Z64 in *; lia)).
      symmetry. apply Z.eqb_neq. lia. }
    iApply (wp_uk_cbeqz N h4 m2 (mword_of_int 0xa64)
              (mword_of_int 11 : mword 8) (mword_of_int 4 : mword 3) a2_idx
              false (mword_of_int 0xa7a) nn
              ltac:(vm_compute; reflexivity) Htk64
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(discriminate)
              with "[] Hrun").
    { iApply (uis_shk_a64 with "Hcode"). }
    assert (Ea64 : add_vec_int (mword_of_int 0xa64 : mword 64) 2
                   = mword_of_int 0xa66)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Ea64. iIntros (h5) "Hrun".
    (* ---- 0xa66  c.mv a5,a0 ---- *)
    iApply (wp_uk_cmv N h5 m2 (mword_of_int 0xa66) a5_idx a0_idx
              (mword_of_int a) nn
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha0_2 moi_add_zero_l; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_a66 with "Hcode"). }
    assert (Ea66 : add_vec_int (mword_of_int 0xa66 : mword 64) 2
                   = mword_of_int 0xa68)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Ea66. iIntros (h6) "Hrun".
    set (m3 := <[Regidx a5_idx
                 := regval_into_reg (mword_of_int a : mword 64)]> m2).
    assert (Hm3 : forall r : mword 5, Regidx r <> Regidx a5_idx ->
                    m3 !!! Regidx r = m2 !!! Regidx r)
      by (intros r Hr; exact (upd_ne m2 (Regidx a5_idx) (Regidx r) _ Hr)).
    assert (Ha2_3 : m3 !!! Regidx a2_idx = mword_of_int (Z.of_nat Nb))
      by (rewrite (Hm3 a2_idx ltac:(vm_compute; discriminate)); exact Ha2_2).
    (* ---- 0xa68  c.slli a2,a2,0x20 ---- *)
    iApply (wp_uk_cslli N h6 m3 (mword_of_int 0xa68)
              (mword_of_int 32 : mword 6) a2_idx
              (mword_of_int (Z.of_nat Nb * 2 ^ 32)) nn
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha2_3; symmetry;
                    exact (moi_shl (Z.of_nat Nb) 32 ltac:(lia)))
              with "[] Hrun").
    { iApply (uis_shk_a68 with "Hcode"). }
    assert (Ea68 : add_vec_int (mword_of_int 0xa68 : mword 64) 2
                   = mword_of_int 0xa6a)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Ea68. iIntros (h7) "Hrun".
    set (m4 := <[Regidx a2_idx
                 := regval_into_reg (mword_of_int (Z.of_nat Nb * 2 ^ 32)
                                     : mword 64)]> m3).
    assert (Hm4 : forall r : mword 5, Regidx r <> Regidx a2_idx ->
                    m4 !!! Regidx r = m3 !!! Regidx r)
      by (intros r Hr; exact (upd_ne m3 (Regidx a2_idx) (Regidx r) _ Hr)).
    assert (Ha2_4 : m4 !!! Regidx a2_idx
                    = mword_of_int (Z.of_nat Nb * 2 ^ 32))
      by exact (upd_eq m3 (Regidx a2_idx)
                  (regval_into_reg (mword_of_int (Z.of_nat Nb * 2 ^ 32)
                                    : mword 64))).
    (* ---- 0xa6a  c.srli a2,a2,0x20 -- the pair is a 32-bit zero-extend -- *)
    iApply (wp_uk_csrli N h7 m4 (mword_of_int 0xa6a)
              (mword_of_int 32 : mword 6) (mword_of_int 4 : mword 3) a2_idx
              (mword_of_int (Z.of_nat Nb)) nn
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha2_4;
                    rewrite (moi_shr (Z.of_nat Nb * 2 ^ 32) 32 ltac:(lia)
                               ltac:(change (2 ^ 32) with 4294967296;
                                     unfold Z31, Z64 in *; lia));
                    rewrite Z.div_mul; [ reflexivity | vm_compute; discriminate ])
              with "[] Hrun").
    { iApply (uis_shk_a6a with "Hcode"). }
    assert (Ea6a : add_vec_int (mword_of_int 0xa6a : mword 64) 2
                   = mword_of_int 0xa6c)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Ea6a. iIntros (h8) "Hrun".
    set (m5 := <[Regidx a2_idx
                 := regval_into_reg (mword_of_int (Z.of_nat Nb) : mword 64)]> m4).
    assert (Hm5 : forall r : mword 5, Regidx r <> Regidx a2_idx ->
                    m5 !!! Regidx r = m4 !!! Regidx r)
      by (intros r Hr; exact (upd_ne m4 (Regidx a2_idx) (Regidx r) _ Hr)).
    assert (Ha2_5 : m5 !!! Regidx a2_idx = mword_of_int (Z.of_nat Nb))
      by exact (upd_eq m4 (Regidx a2_idx)
                  (regval_into_reg (mword_of_int (Z.of_nat Nb) : mword 64))).
    assert (Ha0_5 : m5 !!! Regidx a0_idx = mword_of_int a).
    { rewrite (Hm5 a0_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm4 a0_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm3 a0_idx ltac:(vm_compute; discriminate)). exact Ha0_2. }
    (* ---- 0xa6c  add a4,a2,a0 -- the end address ---- *)
    iApply (wp_uk_add N h8 m5 (mword_of_int 0xa6c)
              a2_idx a0_idx a4_idx (mword_of_int (a + Z.of_nat Nb)) nn
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha2_5 Ha0_5 moi_add;
                    replace (a + Z.of_nat Nb) with (Z.of_nat Nb + a) by lia;
                    reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_a6c with "Hcode"). }
    assert (Ea6c : add_vec_int (mword_of_int 0xa6c : mword 64) 4
                   = mword_of_int 0xa70)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Ea6c. iIntros (h9) "Hrun".
    set (m6 := <[Regidx a4_idx
                 := regval_into_reg (mword_of_int (a + Z.of_nat Nb)
                                     : mword 64)]> m5).
    assert (Hm6 : forall r : mword 5, Regidx r <> Regidx a4_idx ->
                    m6 !!! Regidx r = m5 !!! Regidx r)
      by (intros r Hr; exact (upd_ne m5 (Regidx a4_idx) (Regidx r) _ Hr)).
    assert (Ha4_6 : m6 !!! Regidx a4_idx = mword_of_int (a + Z.of_nat Nb))
      by exact (upd_eq m5 (Regidx a4_idx)
                  (regval_into_reg (mword_of_int (a + Z.of_nat Nb) : mword 64))).
    assert (Ha5_6 : m6 !!! Regidx a5_idx = mword_of_int (a + Z.of_nat 0)).
    { replace (a + Z.of_nat 0) with a by lia.
      rewrite (Hm6 a5_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm5 a5_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm4 a5_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq m2 (Regidx a5_idx)
               (regval_into_reg (mword_of_int a : mword 64))). }
    (* ---- 0xa70..0xa76  the byte loop ---- *)
    (* ---- 0xa70  sb a1,0(a5) -- AND THIS IS WHERE THE PROCESS DIES ---- *)
    (* the deposit is a RESOURCE at the leaf (TRAP-ROWS M2 part 2) and a
       resource here too (lane IO-LEAF, M3c): it was carried down the
       parser's walk from the fork that lent it. *)
    iApply (wp_uk_sb_denied N h9 m6 (mword_of_int 0xa70)
              (mword_of_int 0 : mword 12) a5_idx a1_idx a b0 nn
              ltac:(rewrite Ha5_6; replace (a + Z.of_nat 0) with a by lia;
                    rewrite (uint_moi a ltac:(unfold Z64; lia));
                    vm_compute uoff_i12; lia)
              with "[] Ht0 Hrun Hpay").
    iApply (uis_shk_a70 with "Hcode").
  Qed.

  (* ...AND THE PROCESS'S FIRST TEXT BYTE, which is what a store to the NULL
     pointer needs ([wp_ksh_memset_null] below): VA 0 is [getcmd]'s first
     byte ([ShSyms.getcmd = 0]), so it is in the dumped image, hence in the
     TEXT half of [UserHeap.uheap] -- and a text page is X-and-not-W. *)
  Lemma ush_text0 (g : gname) : shk_code g -∗ ∃ b : bv 8, utext g 0 b.
  Proof using .
    iIntros "#Ht".
    iDestruct (shk_code_img with "Ht") as "Himg". rewrite /utext_img.
    destruct (ShInstrs.sh_bytes !! 0%Z) as [b0 |] eqn:Hb0.
    - iExists b0. iApply (big_sepM_lookup with "Himg"). exact Hb0.
    - exfalso. vm_compute in Hb0. discriminate Hb0.
  Qed.

  (* ---- memset, the whole function ------------------------------------- *)
  Lemma wp_ksh_memset (h : CpuId) (m : regfile) (a : Z) (Nb : nat)
      (f : nat -> bv 8) (nn : nat) :
    m !!! Regidx a0_idx = mword_of_int a ->
    m !!! Regidx a2_idx = mword_of_int (Z.of_nat Nb) ->
    (0 < Nb)%nat -> Z.of_nat Nb < Z31 ->
    shk_code γt -∗
    ubytes γd a Nb f -∗
    urun N h m (mword_of_int ShSyms.memset) (2 + nn) -∗
    (ubytes γd a Nb (fun _ => nth_byte (m !!! Regidx a1_idx) 0) -∗
       ∀ (h' : CpuId) (m' : regfile),
         ⌜ ucallee_saved m m' ⌝ -∗
         urun N h' m' (ret_pc (m !!! Regidx ra_idx)) (2 + nn) -∗
         mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Ha0 Ha2 HN0 HN31. iIntros "#Hcode Hbs Hrun Hcont".
    rewrite shp_memset.
    iDestruct (urun_stack with "Hrun") as %[Hal8 Hroom].
    iDestruct (urun_ubytes_bnd h m _ (2 + nn) (DfracOwn 1) a Nb f ltac:(lia)
                 with "Hrun Hbs") as %[Halo Hahi].
    change (2 ^ 38) with 274877906944 in Hahi.
    remember (m !!! Regidx csp_rs1) as sp0 eqn:Hsp0.
    assert (Hsp : m !!! Regidx csp_rs1 = sp0) by (symmetry; exact Hsp0).
    clear Hsp0.
    assert (Hlo : 16 <= uint sp0) by lia.
    set (vra := m !!! Regidx ra_idx).
    set (vs0 := m !!! Regidx s0_idx).
    assert (Hbsp1 : bv_unsigned (add_vec_int sp0 (- (8 * Z.of_nat 2)))
                    = bv_unsigned sp0 - 16).
    { replace (- (8 * Z.of_nat 2)) with (-16) by lia.
      exact (uv_avi_neg sp0 16 ltac:(lia) ltac:(rewrite <- uint_unsigned; lia)). }
    assert (Hsp16 : uint (add_vec_int sp0 (- (8 * Z.of_nat 2))) = uint sp0 - 16)
      by (rewrite !uint_unsigned; exact Hbsp1).
    assert (Ho8 : uoff_sdsp (mword_of_int 1 : mword 6) = 8)
      by (vm_compute; reflexivity).
    assert (Ho0 : uoff_sdsp (mword_of_int 0 : mword 6) = 0)
      by (vm_compute; reflexivity).
    (* ---- 0xa5c  c.addi sp,sp,-16 -- THE PUSH ---- *)
    iApply (wp_uk_caddi_sp_dn N h m (mword_of_int 0xa5c)
              (mword_of_int 48 : mword 6) 2 nn
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_a5c with "Hcode"). }
    assert (Ea5c : add_vec_int (mword_of_int 0xa5c : mword 64) 2
                   = mword_of_int 0xa5e)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Hsp ustack_2 Ea5c.
    iIntros "(_ & [%v8 Hw8] & [%v0 Hw0])".
    iIntros (h1) "Hrun".
    set (m1 := <[Regidx csp_rs1
                 := regval_into_reg (add_vec_int sp0 (- (8 * Z.of_nat 2)))]> m).
    assert (Hsp1 : m1 !!! Regidx csp_rs1 = add_vec_int sp0 (- (8 * Z.of_nat 2)))
      by exact (upd_eq m (Regidx csp_rs1)
                  (regval_into_reg (add_vec_int sp0 (- (8 * Z.of_nat 2))))).
    assert (Hm1 : forall r : mword 5, Regidx r <> Regidx csp_rs1 ->
                    m1 !!! Regidx r = m !!! Regidx r)
      by (intros r Hr; exact (upd_ne m (Regidx csp_rs1) (Regidx r) _ Hr)).
    (* ---- 0xa5e  c.sdsp ra,8(sp) ---- *)
    iApply (wp_uk_csdsp N h1 m1 (mword_of_int 0xa5e)
              (mword_of_int 1 : mword 6) ra_idx (uint sp0 - 8) v8 nn
              ltac:(rewrite Hsp1 Hsp16 Ho8; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              with "[] Hw8 Hrun").
    { iApply (uis_shk_a5e with "Hcode"). }
    iIntros "Hw8".
    rewrite (Hm1 ra_idx ltac:(vm_compute; discriminate)).
    assert (Ea5e : add_vec_int (mword_of_int 0xa5e : mword 64) 2
                   = mword_of_int 0xa60)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Ea5e. iIntros (h2) "Hrun".
    (* ---- 0xa60  c.sdsp s0,0(sp) ---- *)
    iApply (wp_uk_csdsp N h2 m1 (mword_of_int 0xa60)
              (mword_of_int 0 : mword 6) s0_idx (uint sp0 - 16) v0 nn
              ltac:(rewrite Hsp1 Hsp16 Ho0; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              with "[] Hw0 Hrun").
    { iApply (uis_shk_a60 with "Hcode"). }
    iIntros "Hw0".
    rewrite (Hm1 s0_idx ltac:(vm_compute; discriminate)).
    assert (Ea60 : add_vec_int (mword_of_int 0xa60 : mword 64) 2
                   = mword_of_int 0xa62)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Ea60. iIntros (h3) "Hrun".
    (* ---- 0xa62  c.addi4spn s0,sp,16 (s0 is dead until the epilogue) ---- *)
    iApply (wp_uk_caddi4spn N h3 m1 (mword_of_int 0xa62)
              (mword_of_int 0 : mword 3) (mword_of_int 4 : mword 8) s0_idx
              (add_vec (m1 !!! Regidx csp_rs1)
                 (sign_extend' 64 (caddi4spn_imm (mword_of_int 4 : mword 8)))) nn
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
              eq_refl
              with "[] Hrun").
    { iApply (uis_shk_a62 with "Hcode"). }
    assert (Ea62 : add_vec_int (mword_of_int 0xa62 : mword 64) 2
                   = mword_of_int 0xa64)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Ea62. iIntros (h4) "Hrun".
    set (m2 := <[Regidx s0_idx
                 := regval_into_reg
                      (add_vec (m1 !!! Regidx csp_rs1)
                         (sign_extend' 64
                            (caddi4spn_imm (mword_of_int 4 : mword 8))))]> m1).
    assert (Hm2 : forall r : mword 5, Regidx r <> Regidx s0_idx ->
                    m2 !!! Regidx r = m1 !!! Regidx r)
      by (intros r Hr; exact (upd_ne m1 (Regidx s0_idx) (Regidx r) _ Hr)).
    assert (Hsp2 : m2 !!! Regidx csp_rs1 = add_vec_int sp0 (- (8 * Z.of_nat 2)))
      by (rewrite (Hm2 csp_rs1 ltac:(vm_compute; discriminate)); exact Hsp1).
    assert (Ha2_2 : m2 !!! Regidx a2_idx = mword_of_int (Z.of_nat Nb)).
    { rewrite (Hm2 a2_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm1 a2_idx ltac:(vm_compute; discriminate)). exact Ha2. }
    assert (Ha0_2 : m2 !!! Regidx a0_idx = mword_of_int a).
    { rewrite (Hm2 a0_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm1 a0_idx ltac:(vm_compute; discriminate)). exact Ha0. }
    (* ---- 0xa64  c.beqz a2 -- the count is nonzero, so NOT taken ---- *)
    assert (Htk64 : false = eq_vec (m2 !!! Regidx a2_idx) zero_reg).
    { rewrite Ha2_2.
      rewrite (moi_eq_zero (Z.of_nat Nb) ltac:(unfold Z31, Z64 in *; lia)).
      symmetry. apply Z.eqb_neq. lia. }
    iApply (wp_uk_cbeqz N h4 m2 (mword_of_int 0xa64)
              (mword_of_int 11 : mword 8) (mword_of_int 4 : mword 3) a2_idx
              false (mword_of_int 0xa7a) nn
              ltac:(vm_compute; reflexivity) Htk64
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(discriminate)
              with "[] Hrun").
    { iApply (uis_shk_a64 with "Hcode"). }
    assert (Ea64 : add_vec_int (mword_of_int 0xa64 : mword 64) 2
                   = mword_of_int 0xa66)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Ea64. iIntros (h5) "Hrun".
    (* ---- 0xa66  c.mv a5,a0 ---- *)
    iApply (wp_uk_cmv N h5 m2 (mword_of_int 0xa66) a5_idx a0_idx
              (mword_of_int a) nn
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha0_2 moi_add_zero_l; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_a66 with "Hcode"). }
    assert (Ea66 : add_vec_int (mword_of_int 0xa66 : mword 64) 2
                   = mword_of_int 0xa68)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Ea66. iIntros (h6) "Hrun".
    set (m3 := <[Regidx a5_idx
                 := regval_into_reg (mword_of_int a : mword 64)]> m2).
    assert (Hm3 : forall r : mword 5, Regidx r <> Regidx a5_idx ->
                    m3 !!! Regidx r = m2 !!! Regidx r)
      by (intros r Hr; exact (upd_ne m2 (Regidx a5_idx) (Regidx r) _ Hr)).
    assert (Ha2_3 : m3 !!! Regidx a2_idx = mword_of_int (Z.of_nat Nb))
      by (rewrite (Hm3 a2_idx ltac:(vm_compute; discriminate)); exact Ha2_2).
    (* ---- 0xa68  c.slli a2,a2,0x20 ---- *)
    iApply (wp_uk_cslli N h6 m3 (mword_of_int 0xa68)
              (mword_of_int 32 : mword 6) a2_idx
              (mword_of_int (Z.of_nat Nb * 2 ^ 32)) nn
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha2_3; symmetry;
                    exact (moi_shl (Z.of_nat Nb) 32 ltac:(lia)))
              with "[] Hrun").
    { iApply (uis_shk_a68 with "Hcode"). }
    assert (Ea68 : add_vec_int (mword_of_int 0xa68 : mword 64) 2
                   = mword_of_int 0xa6a)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Ea68. iIntros (h7) "Hrun".
    set (m4 := <[Regidx a2_idx
                 := regval_into_reg (mword_of_int (Z.of_nat Nb * 2 ^ 32)
                                     : mword 64)]> m3).
    assert (Hm4 : forall r : mword 5, Regidx r <> Regidx a2_idx ->
                    m4 !!! Regidx r = m3 !!! Regidx r)
      by (intros r Hr; exact (upd_ne m3 (Regidx a2_idx) (Regidx r) _ Hr)).
    assert (Ha2_4 : m4 !!! Regidx a2_idx
                    = mword_of_int (Z.of_nat Nb * 2 ^ 32))
      by exact (upd_eq m3 (Regidx a2_idx)
                  (regval_into_reg (mword_of_int (Z.of_nat Nb * 2 ^ 32)
                                    : mword 64))).
    (* ---- 0xa6a  c.srli a2,a2,0x20 -- the pair is a 32-bit zero-extend -- *)
    iApply (wp_uk_csrli N h7 m4 (mword_of_int 0xa6a)
              (mword_of_int 32 : mword 6) (mword_of_int 4 : mword 3) a2_idx
              (mword_of_int (Z.of_nat Nb)) nn
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha2_4;
                    rewrite (moi_shr (Z.of_nat Nb * 2 ^ 32) 32 ltac:(lia)
                               ltac:(change (2 ^ 32) with 4294967296;
                                     unfold Z31, Z64 in *; lia));
                    rewrite Z.div_mul; [ reflexivity | vm_compute; discriminate ])
              with "[] Hrun").
    { iApply (uis_shk_a6a with "Hcode"). }
    assert (Ea6a : add_vec_int (mword_of_int 0xa6a : mword 64) 2
                   = mword_of_int 0xa6c)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Ea6a. iIntros (h8) "Hrun".
    set (m5 := <[Regidx a2_idx
                 := regval_into_reg (mword_of_int (Z.of_nat Nb) : mword 64)]> m4).
    assert (Hm5 : forall r : mword 5, Regidx r <> Regidx a2_idx ->
                    m5 !!! Regidx r = m4 !!! Regidx r)
      by (intros r Hr; exact (upd_ne m4 (Regidx a2_idx) (Regidx r) _ Hr)).
    assert (Ha2_5 : m5 !!! Regidx a2_idx = mword_of_int (Z.of_nat Nb))
      by exact (upd_eq m4 (Regidx a2_idx)
                  (regval_into_reg (mword_of_int (Z.of_nat Nb) : mword 64))).
    assert (Ha0_5 : m5 !!! Regidx a0_idx = mword_of_int a).
    { rewrite (Hm5 a0_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm4 a0_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm3 a0_idx ltac:(vm_compute; discriminate)). exact Ha0_2. }
    (* ---- 0xa6c  add a4,a2,a0 -- the end address ---- *)
    iApply (wp_uk_add N h8 m5 (mword_of_int 0xa6c)
              a2_idx a0_idx a4_idx (mword_of_int (a + Z.of_nat Nb)) nn
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha2_5 Ha0_5 moi_add;
                    replace (a + Z.of_nat Nb) with (Z.of_nat Nb + a) by lia;
                    reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_a6c with "Hcode"). }
    assert (Ea6c : add_vec_int (mword_of_int 0xa6c : mword 64) 4
                   = mword_of_int 0xa70)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Ea6c. iIntros (h9) "Hrun".
    set (m6 := <[Regidx a4_idx
                 := regval_into_reg (mword_of_int (a + Z.of_nat Nb)
                                     : mword 64)]> m5).
    assert (Hm6 : forall r : mword 5, Regidx r <> Regidx a4_idx ->
                    m6 !!! Regidx r = m5 !!! Regidx r)
      by (intros r Hr; exact (upd_ne m5 (Regidx a4_idx) (Regidx r) _ Hr)).
    assert (Ha4_6 : m6 !!! Regidx a4_idx = mword_of_int (a + Z.of_nat Nb))
      by exact (upd_eq m5 (Regidx a4_idx)
                  (regval_into_reg (mword_of_int (a + Z.of_nat Nb) : mword 64))).
    assert (Ha5_6 : m6 !!! Regidx a5_idx = mword_of_int (a + Z.of_nat 0)).
    { replace (a + Z.of_nat 0) with a by lia.
      rewrite (Hm6 a5_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm5 a5_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm4 a5_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq m2 (Regidx a5_idx)
               (regval_into_reg (mword_of_int a : mword 64))). }
    (* ---- 0xa70..0xa76  the byte loop ---- *)
    assert (Ha1_6 : m6 !!! Regidx a1_idx = m !!! Regidx a1_idx).
    { rewrite (Hm6 a1_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm5 a1_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm4 a1_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm3 a1_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm2 a1_idx ltac:(vm_compute; discriminate)).
      exact (Hm1 a1_idx ltac:(vm_compute; discriminate)). }
    iApply (wp_ksh_memset_loop a Nb (nth_byte (m !!! Regidx a1_idx) 0)
              (Nb - 1)%nat 0%nat h9 m6 f nn
              ltac:(lia) Halo ltac:(unfold Z64; lia)
              ltac:(rewrite Ha1_6; reflexivity)
              ltac:(intros i Hi; lia)
              Ha5_6 Ha4_6
              with "Hcode Hbs Hrun").
    iIntros "Hbs" (h10 mc) "%Hmc Hrun".
    assert (Hspc : mc !!! Regidx csp_rs1 = add_vec_int sp0 (- (8 * Z.of_nat 2))).
    { rewrite (Hmc csp_rs1 ltac:(vm_compute; discriminate)).
      rewrite (Hm6 csp_rs1 ltac:(vm_compute; discriminate)).
      rewrite (Hm5 csp_rs1 ltac:(vm_compute; discriminate)).
      rewrite (Hm4 csp_rs1 ltac:(vm_compute; discriminate)).
      rewrite (Hm3 csp_rs1 ltac:(vm_compute; discriminate)). exact Hsp2. }
    (* ---- 0xa7a  c.ldsp ra,8(sp) ---- *)
    iApply (wp_uk_cldsp N h10 mc (mword_of_int 0xa7a)
              (mword_of_int 1 : mword 6) ra_idx (uint sp0 - 8) vra nn
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(rewrite Hspc Hsp16 Ho8; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              ltac:(vm_compute; discriminate)
              with "[] Hw8 Hrun").
    { iApply (uis_shk_a7a with "Hcode"). }
    iIntros "Hw8".
    assert (Ea7a : add_vec_int (mword_of_int 0xa7a : mword 64) 2
                   = mword_of_int 0xa7c)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Ea7a. iIntros (h11) "Hrun".
    set (e1 := <[Regidx ra_idx := regval_into_reg vra]> mc).
    assert (Hspe1 : e1 !!! Regidx csp_rs1
                    = add_vec_int sp0 (- (8 * Z.of_nat 2))).
    { rewrite (upd_ne mc (Regidx ra_idx) (Regidx csp_rs1) _
                 ltac:(vm_compute; discriminate)). exact Hspc. }
    (* ---- 0xa7c  c.ldsp s0,0(sp) ---- *)
    iApply (wp_uk_cldsp N h11 e1 (mword_of_int 0xa7c)
              (mword_of_int 0 : mword 6) s0_idx (uint sp0 - 16) vs0 nn
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(rewrite Hspe1 Hsp16 Ho0; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              ltac:(vm_compute; discriminate)
              with "[] Hw0 Hrun").
    { iApply (uis_shk_a7c with "Hcode"). }
    iIntros "Hw0".
    assert (Ea7c : add_vec_int (mword_of_int 0xa7c : mword 64) 2
                   = mword_of_int 0xa7e)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Ea7c. iIntros (h12) "Hrun".
    set (e2 := <[Regidx s0_idx := regval_into_reg vs0]> e1).
    assert (Hspe2 : e2 !!! Regidx csp_rs1
                    = add_vec_int sp0 (- (8 * Z.of_nat 2))).
    { rewrite (upd_ne e1 (Regidx s0_idx) (Regidx csp_rs1) _
                 ltac:(vm_compute; discriminate)). exact Hspe1. }
    (* ---- 0xa7e  c.addi sp,sp,16 -- THE POP ---- *)
    assert (HR : 0 <= bv_unsigned sp0 < 18446744073709551616).
    { pose proof (bv_unsigned_in_range 64 sp0) as H0.
      assert (Em : bv_modulus 64 = 18446744073709551616)
        by (vm_compute; reflexivity).
      rewrite Em in H0. exact H0. }
    assert (Hlt2 : bv_unsigned (add_vec_int sp0 (- (8 * Z.of_nat 2)))
                   + 8 * Z.of_nat 2 < Z64)
      by (rewrite Hbsp1; unfold Z64; lia).
    assert (Hup : add_vec_int (add_vec_int sp0 (- (8 * Z.of_nat 2)))
                    (8 * Z.of_nat 2) = sp0).
    { apply bv_eq.
      rewrite (uv_avi_pos (add_vec_int sp0 (- (8 * Z.of_nat 2)))
                 (8 * Z.of_nat 2) ltac:(lia) Hlt2).
      rewrite Hbsp1. lia. }
    iApply (wp_uk_caddi_sp_up N h12 e2 (mword_of_int 0xa7e)
              (mword_of_int 16 : mword 6) 2 nn
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "[] [Hw8 Hw0] Hrun").
    { iApply (uis_shk_a7e with "Hcode"). }
    { rewrite Hspe2 Hup ustack_2.
      iSplit; [ iPureIntro; exact Hal8 | ].
      iSplitL "Hw8"; [ iExists vra; iFrame | iExists vs0; iFrame ]. }
    assert (Ea7e : add_vec_int (mword_of_int 0xa7e : mword 64) 2
                   = mword_of_int 0xa80)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Hspe2 Hup Ea7e.
    iIntros (h13) "Hrun".
    set (e3 := <[Regidx csp_rs1 := regval_into_reg sp0]> e2).
    assert (Hra3 : e3 !!! Regidx ra_idx = vra).
    { rewrite (upd_ne e2 (Regidx csp_rs1) (Regidx ra_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne e1 (Regidx s0_idx) (Regidx ra_idx) _
                 ltac:(vm_compute; discriminate)).
      exact (upd_eq mc (Regidx ra_idx) (regval_into_reg vra)). }
    (* ---- 0xa80  c.jr ra ---- *)
    iApply (wp_uk_cjr N h13 e3 (mword_of_int 0xa80) ra_idx
              (ret_pc vra) (2 + nn)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hra3; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_a80 with "Hcode"). }
    iIntros (h14) "Hrun".
    iApply ("Hcont" with "Hbs [] Hrun").
    iPureIntro. intros r Hr.
    assert (Hcsp2 : uint csp_rs1 = 2) by (vm_compute; reflexivity).
    assert (Hs08 : uint s0_idx = 8) by (vm_compute; reflexivity).
    destruct (Z.eq_dec (uint r) 2) as [Er | Er].
    { rewrite (ush_ridx_eq r csp_rs1 ltac:(rewrite Er; vm_compute; reflexivity)).
      rewrite Hsp.
      exact (upd_eq e2 (Regidx csp_rs1) (regval_into_reg sp0)). }
    destruct (Z.eq_dec (uint r) 8) as [E8 | E8].
    { rewrite (ush_ridx_eq r s0_idx ltac:(rewrite E8; vm_compute; reflexivity)).
      rewrite (upd_ne e2 (Regidx csp_rs1) (Regidx s0_idx) _
                 ltac:(vm_compute; discriminate)).
      exact (upd_eq e1 (Regidx s0_idx) (regval_into_reg vs0)). }
    assert (Hrsp : Regidx r <> Regidx csp_rs1)
      by (apply ush_ridx_ne; rewrite Hcsp2; exact Er).
    assert (Hrs0 : Regidx r <> Regidx s0_idx)
      by (apply ush_ridx_ne; rewrite Hs08; exact E8).
    rewrite /e3 (upd_ne e2 (Regidx csp_rs1) (Regidx r) _ Hrsp).
    rewrite /e2 (upd_ne e1 (Regidx s0_idx) (Regidx r) _ Hrs0).
    rewrite /e1 (upd_ne mc (Regidx ra_idx) (Regidx r) _
                   (ucs_ne r ra_idx Hr ltac:(vm_compute; reflexivity))).
    rewrite (Hmc r (ucs_ne r a5_idx Hr ltac:(vm_compute; reflexivity))).
    rewrite (Hm6 r (ucs_ne r a4_idx Hr ltac:(vm_compute; reflexivity))).
    rewrite (Hm5 r (ucs_ne r a2_idx Hr ltac:(vm_compute; reflexivity))).
    rewrite (Hm4 r (ucs_ne r a2_idx Hr ltac:(vm_compute; reflexivity))).
    rewrite (Hm3 r (ucs_ne r a5_idx Hr ltac:(vm_compute; reflexivity))).
    rewrite (Hm2 r Hrs0). exact (Hm1 r Hrsp).
  Qed.


  (* ===================================================================== *)
  (* gets @0xaaa -- 50 instructions, a 96-byte frame, and the READ.         *)
  (* DEPENDS ON [ush_read_leaf] (through [wp_ksh_read]).                    *)
  (*                                                                       *)
  (*   for(i = 0; i+1 < max; ){                                            *)
  (*     cc = read(0, &c, 1);                                              *)
  (*     if(cc < 1) break;                                                 *)
  (*     buf[i++] = c;                                                     *)
  (*     if(c == '\n' || c == '\r') break;                                 *)
  (*   }                                                                   *)
  (*   buf[i] = '\0';                                                      *)
  (*                                                                       *)
  (* WHAT THE CONTRACT PROMISES is exactly what main's scan needs and no    *)
  (* more: the buffer comes back OWNED, with a NUL at some index below      *)
  (* [max].  It says nothing about which bytes were read -- it cannot, and  *)
  (* it does not have to.  The kernel's window row does not tie the         *)
  (* returned count to the number of bytes it wrote, and gets stores        *)
  (* whatever is in its one-byte window either way; the walk is correct at  *)
  (* every [d <= 1] the row permits.                                       *)
  (*                                                                       *)
  (* THE NUL IS WHY [urun_x0] EXISTS.  [buf[i] = '\0'] is [sb zero,0(s8)],  *)
  (* whose stored byte is the VALUE of x0 -- about which the register file  *)
  (* alone says nothing.                                                   *)
  (*                                                                       *)
  (* c LIVES IN THE FRAME, at [s0-81] = one byte inside the word at         *)
  (* [sp0-88] -- the only slot of the twelve that is a local rather than a  *)
  (* spill.  The loop therefore carries ONE byte, not the frame: the ten    *)
  (* spilled words and the other seven bytes of that word are never touched *)
  (* by it and stay in the caller's context.                                *)
  (* ===================================================================== *)

  (* the registers gets' loop body does NOT write: sp, s0, s4..s7.  Its
     [read] call clobbers ra and a0/a1/a2/a7 as well as the loop's own
     s1/s2/s3/s8/a4/a5, so the caller reads back only these six. *)
  Definition ush_gets_keep (r : mword 5) : bool :=
    let z := uint r in
    Z.eqb z 2 || Z.eqb z 3 || Z.eqb z 4 || Z.eqb z 8 ||
    ((20 <=? z) && (z <=? 23)) || ((25 <=? z) && (z <=? 27)).

  Local Lemma ush_keep_ne (r q : mword 5) :
    ush_gets_keep r = true -> ush_gets_keep q = false -> Regidx r <> Regidx q.
  Proof using .
    intros Hr Hq He.
    assert (Hrr : r = q) by (injection He; trivial).
    rewrite Hrr Hq in Hr. discriminate.
  Qed.

  Local Lemma wp_ksh_gets_loop (a : Z) (Nb : nat) (spz : Z)
      (l : list fdstate) (I0 : list (bv 8)) (Hfd0 : ush_fd0p l) :
    forall (k i : nat) (J : list (bv 8)) (h : CpuId) (mc : regfile)
           (f : nat -> bv 8) (bc : bv 8) (nn : nat),
    (Nb = i + k)%nat -> (i < Nb)%nat ->
    (* THE INDEX IS THE LENGTH OF WHAT HAS BEEN READ (project
       echo-any-line): the loop's [i] is a register, and the bytes behind
       it are the line so far. *)
    (i = length J)%nat ->
    (* ROOM FOR A WHOLE LINE (lane IO-LEAF, M5(3)): the buffer-full exit is
       what would leave the walk in the MIDDLE of a line, and the buffer IS
       as long as the longest line the discipline admits
       ([sh_nbuf_line_max]), so a line that is still growing still fits. *)
    Nb = sh_nbuf ->
    0 <= a -> a + Z.of_nat Nb < Z64 -> Z.of_nat Nb < Z31 ->
    96 <= spz -> spz < Z64 ->
    mc !!! Regidx s0_idx = mword_of_int spz ->
    mc !!! Regidx s1_idx = mword_of_int (Z.of_nat i) ->
    mc !!! Regidx s2_idx = mword_of_int (a + Z.of_nat i) ->
    mc !!! Regidx s4_idx = mword_of_int (Z.of_nat Nb) ->
    mc !!! Regidx s5_idx = mword_of_int 1 ->
    mc !!! Regidx s6_idx = mword_of_int (spz - 81) ->
    (* the tag's reading, which is what the ^D swallow is refuted with *)
    ush_tag_law -∗
    shk_code γt -∗
    ubytes γd a Nb f -∗
    ubyte γd (spz - 81) bc -∗
    ush_std l -∗
    ush_gets_line_at Dsc l I0 J f -∗
    (* ...and the credential the prompt left, riding beside the line
       untouched to the exit that spends it (lane IO-LEAF, M6a(3)) -- or
       the taint, on a turn that holds none (step 4) *)
    (ush_wcp l I0 2%nat ∨ T) -∗
    urun N h mc (mword_of_int 0xad0) nn -∗
    (∀ (h' : CpuId) (mc' : regfile) (i2 : nat) (g : nat -> bv 8) (bc' : bv 8),
       ⌜ (i2 < Nb)%nat ⌝ -∗
       ⌜ mc' !!! Regidx s8_idx = mword_of_int (Z.of_nat i2) ⌝ -∗
       ⌜ forall r : mword 5, ush_gets_keep r = true ->
           mc' !!! Regidx r = mc !!! Regidx r ⌝ -∗
       ubytes γd a Nb g -∗
       ubyte γd (spz - 81) bc' -∗
       ush_std l -∗
       ush_gets_done_at Dl l i2 g -∗
       urun N h' mc' (mword_of_int 0xb00) nn -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using Hdsc_ncr Hdsc_line Hdsc_short HT ush_at_of_pm_taint ush_at_of_pm_wb ush_read_leaf ush_wb_read ush_wc_read.
    intros k. induction k as [| k IH ];
      intros i J h mc f bc nn HN Hi Hij HNb Ha0 Ha64 HN31 Hsz0 Hsz1
             Hs0 Hs1 Hs2 Hs4 Hs5 Hs6.
    { assert (HF : False) by lia. destruct HF. }
    iIntros "#Hlaw #Hcode Hbs Hb Hstd Hpos Hwc Hrun Hcont".
    (* ---- 0xad0  c.mv s8,s1 ---- *)
    iApply (wp_uk_cmv N h mc (mword_of_int 0xad0) s8_idx s1_idx
              (mword_of_int (Z.of_nat i)) nn
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs1 moi_add_zero_l; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_ad0 with "Hcode"). }
    assert (Ead0 : add_vec_int (mword_of_int 0xad0 : mword 64) 2
                   = mword_of_int 0xad2)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Ead0. iIntros (h1) "Hrun".
    set (m1 := <[Regidx s8_idx
                 := regval_into_reg (mword_of_int (Z.of_nat i) : mword 64)]> mc).
    assert (P1 : forall r : mword 5, ush_gets_keep r = true ->
                   m1 !!! Regidx r = mc !!! Regidx r)
      by (intros r Hr; exact (upd_ne mc (Regidx s8_idx) (Regidx r) _
                                (ush_keep_ne r s8_idx Hr
                                   ltac:(vm_compute; reflexivity)))).
    assert (Hs1_1 : m1 !!! Regidx s1_idx = mword_of_int (Z.of_nat i)).
    { rewrite (upd_ne mc (Regidx s8_idx) (Regidx s1_idx) _
                 ltac:(vm_compute; discriminate)). exact Hs1. }
    assert (Hs8_1 : m1 !!! Regidx s8_idx = mword_of_int (Z.of_nat i))
      by exact (upd_eq mc (Regidx s8_idx)
                  (regval_into_reg (mword_of_int (Z.of_nat i) : mword 64))).
    (* ---- 0xad2  addiw s3,s1,1 ---- *)
    assert (Ei1 : (sign_extend' 64 (mword_of_int 1 : mword 12) : mword 64)
                  = mword_of_int 1)
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uk_addiw N h1 m1 (mword_of_int 0xad2)
              (mword_of_int 1 : mword 12) s1_idx s3_idx
              (mword_of_int (Z.of_nat i + 1)) nn
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs1_1 Ei1; symmetry;
                    exact (moi_addw (Z.of_nat i) 1 ltac:(unfold Z31 in *; lia)))
              with "[] Hrun").
    { iApply (uis_shk_ad2 with "Hcode"). }
    assert (Ead2 : add_vec_int (mword_of_int 0xad2 : mword 64) 4
                   = mword_of_int 0xad6)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Ead2. iIntros (h2) "Hrun".
    set (m2 := <[Regidx s3_idx
                 := regval_into_reg (mword_of_int (Z.of_nat i + 1)
                                     : mword 64)]> m1).
    assert (P2 : forall r : mword 5, ush_gets_keep r = true ->
                   m2 !!! Regidx r = m1 !!! Regidx r)
      by (intros r Hr; exact (upd_ne m1 (Regidx s3_idx) (Regidx r) _
                                (ush_keep_ne r s3_idx Hr
                                   ltac:(vm_compute; reflexivity)))).
    assert (Hs3_2 : m2 !!! Regidx s3_idx = mword_of_int (Z.of_nat i + 1))
      by exact (upd_eq m1 (Regidx s3_idx)
                  (regval_into_reg (mword_of_int (Z.of_nat i + 1) : mword 64))).
    (* ---- 0xad6  c.mv s1,s3 ---- *)
    iApply (wp_uk_cmv N h2 m2 (mword_of_int 0xad6) s1_idx s3_idx
              (mword_of_int (Z.of_nat i + 1)) nn
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs3_2 moi_add_zero_l; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_ad6 with "Hcode"). }
    assert (Ead6 : add_vec_int (mword_of_int 0xad6 : mword 64) 2
                   = mword_of_int 0xad8)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Ead6. iIntros (h3) "Hrun".
    set (m3 := <[Regidx s1_idx
                 := regval_into_reg (mword_of_int (Z.of_nat i + 1)
                                     : mword 64)]> m2).
    assert (P3 : forall r : mword 5, ush_gets_keep r = true ->
                   m3 !!! Regidx r = m2 !!! Regidx r)
      by (intros r Hr; exact (upd_ne m2 (Regidx s1_idx) (Regidx r) _
                                (ush_keep_ne r s1_idx Hr
                                   ltac:(vm_compute; reflexivity)))).
    assert (P13 : forall r : mword 5, ush_gets_keep r = true ->
                    m3 !!! Regidx r = mc !!! Regidx r)
      by (intros r Hr; rewrite (P3 r Hr) (P2 r Hr); exact (P1 r Hr)).
    assert (Hs3_3 : m3 !!! Regidx s3_idx = mword_of_int (Z.of_nat i + 1)).
    { rewrite (upd_ne m2 (Regidx s1_idx) (Regidx s3_idx) _
                 ltac:(vm_compute; discriminate)). exact Hs3_2. }
    assert (Hs4_3 : m3 !!! Regidx s4_idx = mword_of_int (Z.of_nat Nb))
      by (rewrite (P13 s4_idx ltac:(vm_compute; reflexivity)); exact Hs4).
    assert (Hs8_3 : m3 !!! Regidx s8_idx = mword_of_int (Z.of_nat i)).
    { rewrite (upd_ne m2 (Regidx s1_idx) (Regidx s8_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne m1 (Regidx s3_idx) (Regidx s8_idx) _
                 ltac:(vm_compute; discriminate)). exact Hs8_1. }
    (* ---- 0xad8  bge s3,s4,0xb00 -- the ONE computed branch of the loop  *)
    assert (Htk8 : Z.geb (Z.of_nat i + 1) (Z.of_nat Nb)
                   = uv_btaken BGE (m3 !!! Regidx s3_idx)
                       (m3 !!! Regidx s4_idx)).
    { cbn [uv_btaken]. rewrite Hs3_3 Hs4_3.
      symmetry.
      exact (moi_ge_s (Z.of_nat i + 1) (Z.of_nat Nb)
               ltac:(unfold Z31, Z63 in *; lia)
               ltac:(unfold Z31, Z63 in *; lia)). }
    iApply (wp_uk_btype N h3 m3 (mword_of_int 0xad8)
              (mword_of_int 40 : mword 13) s4_idx s3_idx BGE
              (Z.geb (Z.of_nat i + 1) (Z.of_nat Nb)) (mword_of_int 0xb00) nn
              Htk8
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(intros _; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_ad8 with "Hcode"). }
    destruct (Z.geb_spec (Z.of_nat i + 1) (Z.of_nat Nb)) as [Hge | Hlt].
    { (* the buffer is full -- WHICH CANNOT HAPPEN INSIDE A LINE: the
         invariant keeps [i] below the line's length and the buffer is
         longer than that.  Under the taint there is nothing to keep. *)
      iIntros (h4) "Hrun".
      iApply ("Hcont" $! h4 m3 i f bc
                with "[%] [%] [%] Hbs Hb Hstd [Hpos] Hrun");
        [ lia | exact Hs8_3 | exact P13 | ].
      rewrite /ush_gets_line_at.
      iDestruct "Hpos" as "[[%Hp Hpm] | [#HT Hp]]"; last first.
      { iApply (ush_gets_done_taint_at Dl l i f with "HT Hp"). }
      (* THE BUFFER CANNOT FILL INSIDE A LINE: the invariant keeps the line
         so far one byte short of [line_max], and the buffer IS
         [line_max] ([sh_nbuf_line_max]). *)
      destruct Hp as (_ & _ & Hlt & _ & _ & _). exfalso.
      assert (Hnbm : Nb = line_max)
        by (rewrite HNb; exact sh_nbuf_line_max).
      lia. }
    assert (Ead8 : add_vec_int (mword_of_int 0xad8 : mword 64) 4
                   = mword_of_int 0xadc)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Ead8. iIntros (h4) "Hrun".
    (* room for one more byte *)
    assert (Hik : (i + 1 < Nb)%nat) by lia.
    (* ---- 0xadc  c.mv a2,s5 ---- *)
    assert (Hs5_3 : m3 !!! Regidx s5_idx = mword_of_int 1)
      by (rewrite (P13 s5_idx ltac:(vm_compute; reflexivity)); exact Hs5).
    iApply (wp_uk_cmv N h4 m3 (mword_of_int 0xadc) a2_idx s5_idx
              (mword_of_int 1) nn
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs5_3 moi_add_zero_l; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_adc with "Hcode"). }
    assert (Eadc : add_vec_int (mword_of_int 0xadc : mword 64) 2
                   = mword_of_int 0xade)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Eadc. iIntros (h5) "Hrun".
    set (m4 := <[Regidx a2_idx
                 := regval_into_reg (mword_of_int 1 : mword 64)]> m3).
    assert (P4 : forall r : mword 5, ush_gets_keep r = true ->
                   m4 !!! Regidx r = m3 !!! Regidx r)
      by (intros r Hr; exact (upd_ne m3 (Regidx a2_idx) (Regidx r) _
                                (ush_keep_ne r a2_idx Hr
                                   ltac:(vm_compute; reflexivity)))).
    (* ---- 0xade  c.mv a1,s6 ---- *)
    assert (Hs6_4 : m4 !!! Regidx s6_idx = mword_of_int (spz - 81)).
    { rewrite (P4 s6_idx ltac:(vm_compute; reflexivity)).
      rewrite (P13 s6_idx ltac:(vm_compute; reflexivity)). exact Hs6. }
    iApply (wp_uk_cmv N h5 m4 (mword_of_int 0xade) a1_idx s6_idx
              (mword_of_int (spz - 81)) nn
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs6_4 moi_add_zero_l; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_ade with "Hcode"). }
    assert (Eade : add_vec_int (mword_of_int 0xade : mword 64) 2
                   = mword_of_int 0xae0)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Eade. iIntros (h6) "Hrun".
    set (m5 := <[Regidx a1_idx
                 := regval_into_reg (mword_of_int (spz - 81) : mword 64)]> m4).
    assert (P5 : forall r : mword 5, ush_gets_keep r = true ->
                   m5 !!! Regidx r = m4 !!! Regidx r)
      by (intros r Hr; exact (upd_ne m4 (Regidx a1_idx) (Regidx r) _
                                (ush_keep_ne r a1_idx Hr
                                   ltac:(vm_compute; reflexivity)))).
    (* ---- 0xae0  c.li a0,0 ---- *)
    iApply (wp_uk_cli N h6 m5 (mword_of_int 0xae0)
              (mword_of_int 0 : mword 6) a0_idx nn
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) with "[] Hrun").
    { iApply (uis_shk_ae0 with "Hcode"). }
    assert (Eae0 : add_vec_int (mword_of_int 0xae0 : mword 64) 2
                   = mword_of_int 0xae2)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Eae0. iIntros (h7) "Hrun".
    set (m6 := <[Regidx a0_idx
                 := regval_into_reg (sign_extend' 64 (mword_of_int 0 : mword 6)
                                     : mword 64)]> m5).
    assert (P6 : forall r : mword 5, ush_gets_keep r = true ->
                   m6 !!! Regidx r = m5 !!! Regidx r)
      by (intros r Hr; exact (upd_ne m5 (Regidx a0_idx) (Regidx r) _
                                (ush_keep_ne r a0_idx Hr
                                   ltac:(vm_compute; reflexivity)))).
    (* ---- 0xae2  jal ra,0xc9e <read> ---- *)
    iApply (wp_uk_jal N h7 m6 (mword_of_int 0xae2)
              (mword_of_int 444 : mword 21) ra_idx
              (mword_of_int ShSyms.read) (mword_of_int 0xae6) nn
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite shp_read; apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(rewrite shp_read; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_ae2 with "Hcode"). }
    iIntros (h8) "Hrun".
    set (m7 := <[Regidx ra_idx
                 := regval_into_reg (mword_of_int 0xae6 : mword 64)]> m6).
    assert (P7 : forall r : mword 5, ush_gets_keep r = true ->
                   m7 !!! Regidx r = m6 !!! Regidx r)
      by (intros r Hr; exact (upd_ne m6 (Regidx ra_idx) (Regidx r) _
                                (ush_keep_ne r ra_idx Hr
                                   ltac:(vm_compute; reflexivity)))).
    assert (Hra7 : m7 !!! Regidx ra_idx = mword_of_int 0xae6)
      by exact (upd_eq m6 (Regidx ra_idx)
                  (regval_into_reg (mword_of_int 0xae6 : mword 64))).
    assert (Ha1_7 : uint (m7 !!! Regidx a1_idx) = spz - 81).
    { rewrite (upd_ne m6 (Regidx ra_idx) (Regidx a1_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne m5 (Regidx a0_idx) (Regidx a1_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_eq m4 (Regidx a1_idx)
                 (regval_into_reg (mword_of_int (spz - 81) : mword 64))).
      apply uint_moi. unfold Z64 in *. lia. }
    assert (Ha2_7 : uint (m7 !!! Regidx a2_idx) = Z.of_nat 1).
    { rewrite (upd_ne m6 (Regidx ra_idx) (Regidx a2_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne m5 (Regidx a0_idx) (Regidx a2_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne m4 (Regidx a1_idx) (Regidx a2_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_eq m3 (Regidx a2_idx)
                 (regval_into_reg (mword_of_int 1 : mword 64))).
      vm_compute. reflexivity. }
    (* the one-byte window, as a run *)
    iDestruct (ush_bytes_one (spz - 81) (fun _ => bc) bc eq_refl) as "Hcv".
    iAssert (ubytes γd (spz - 81) 1 (fun _ => bc)) with "[Hb]" as "Hbw".
    { iApply "Hcv". iExact "Hb". }
    assert (Ha0_7 : bv_signed (trunc32 (m7 !!! Regidx a0_idx)) = 0).
    { rewrite (upd_ne m6 (Regidx ra_idx) (Regidx a0_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_eq m5 (Regidx a0_idx)
                 (regval_into_reg (sign_extend' 64 (mword_of_int 0 : mword 6)
                                   : mword 64))).
      vm_compute. reflexivity. }
    (* THE LEASE GOES IN AND THE RECEIPT COMES BACK (lane IO-LEAF, M5(3)).
       The loop's four rows are PURE, so they come off the invariant's
       disjunction and ride the rest of the walk persistently while the
       lease itself is spent -- which is what keeps the walk between the
       read and the '\n' test UNDUPLICATED. *)
    iDestruct (ush_gets_line_split_at Dsc l I0 J f with "Hpos") as "[Hlease #Hrows]".
    iApply (wp_ksh_read h8 m7 (spz - 81) 1%nat 1%nat (I0 ++ J)
              (fun _ => bc) l nn
              Ha0_7 Ha1_7 Ha2_7 ltac:(lia) ltac:(vm_compute; reflexivity)
              Hfd0
              with "Hcode Hbw Hstd Hlease Hrun").
    iIntros (h9 ret d g1) "%Hd %Hg1 Hstd Hans Hbw Hrun".
    (* R2: the receipt, read into the three outcomes a one-byte read has *)
    iDestruct (ush_read_ans_1_at Dsc cn l ret (I0 ++ J) g1 with "Hlaw Hans")
      as "Hans".
    rewrite Hra7.
    assert (Eret : ret_pc (mword_of_int 0xae6 : mword 64) = mword_of_int 0xae6)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Eret.
    set (m8 := <[Regidx a0_idx := ret]>
                 (<[Regidx a7_idx := (mword_of_int 5 : mword 64)]> m7)).
    assert (P8 : forall r : mword 5, ush_gets_keep r = true ->
                   m8 !!! Regidx r = m7 !!! Regidx r).
    { intros r Hr.
      rewrite (upd_ne _ (Regidx a0_idx) (Regidx r) _
                 (ush_keep_ne r a0_idx Hr ltac:(vm_compute; reflexivity))).
      exact (upd_ne m7 (Regidx a7_idx) (Regidx r) _
               (ush_keep_ne r a7_idx Hr ltac:(vm_compute; reflexivity))). }
    assert (P18 : forall r : mword 5, ush_gets_keep r = true ->
                    m8 !!! Regidx r = mc !!! Regidx r).
    { intros r Hr.
      rewrite (P8 r Hr) (P7 r Hr) (P6 r Hr) (P5 r Hr) (P4 r Hr).
      exact (P13 r Hr). }
    assert (Hs8_8 : m8 !!! Regidx s8_idx = mword_of_int (Z.of_nat i)).
    { rewrite (upd_ne _ (Regidx a0_idx) (Regidx s8_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne m7 (Regidx a7_idx) (Regidx s8_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne m6 (Regidx ra_idx) (Regidx s8_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne m5 (Regidx a0_idx) (Regidx s8_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne m4 (Regidx a1_idx) (Regidx s8_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne m3 (Regidx a2_idx) (Regidx s8_idx) _
                 ltac:(vm_compute; discriminate)). exact Hs8_3. }
    (* ---- 0xae6  blez a0,0xb00 -- THE COMPUTED split (lane IO-LEAF,
       M5(3)): which arm it is IS the receipt's, so the walk reads the
       branch off the answer rather than leaving it abstract. *)
    iDestruct (urun_x0 h9 m8 (mword_of_int 0xae6) nn with "Hrun")
      as "[%Hx0_8 Hrun]".
    assert (Ha0_8r : m8 !!! Regidx a0_idx = ret)
      by exact (upd_eq _ (Regidx a0_idx) ret).
    remember (uv_btaken BGE (m8 !!! Regidx x0_idx) (m8 !!! Regidx a0_idx))
      as tk6 eqn:Htk6.
    assert (Htk6v : tk6 = Z.geb 0 (bv_signed ret)).
    { rewrite Htk6 Hx0_8 Ha0_8r. exact (ush_blez_taken ret). }
    iApply (wp_uk_btype N h9 m8 (mword_of_int 0xae6)
              (mword_of_int 26 : mword 13) a0_idx x0_idx BGE tk6
              (mword_of_int 0xb00) nn
              Htk6
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(intros _; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_ae6 with "Hcode"). }
    iDestruct (ush_bytes_one (spz - 81) g1 (g1 0%nat) eq_refl) as "Hcw".
    iAssert (ubyte γd (spz - 81) (g1 0%nat)) with "[Hbw]" as "Hb".
    { iApply "Hcw". iExact "Hbw". }
    destruct tk6.
    { (* the read gave nothing: leave with s8 = i.  On the untainted arm
         that can only be the SHUT fd 0 -- the ^D swallow is the taint and
         a delivered byte is not this arm -- and a shut fd 0 delivered no
         first byte either, so the line the walk leaves is EMPTY. *)
      assert (Hret0 : (bv_signed ret <= 0)%Z)
        by (symmetry in Htk6v; apply Z.geb_le in Htk6v; lia).
      iIntros (h10) "Hrun".
      iApply ("Hcont" $! h10 m8 i f (g1 0%nat)
                with "[%] [%] [%] Hbs Hb Hstd [Hans Hwc] Hrun");
        [ lia | exact Hs8_8 | exact P18 | ].
      iDestruct "Hans" as "[(%Hgt & _ & _ & _) | [(_ & %Hcl & Hpm) | [#HT Hp]]]".
      { exfalso. lia. }
      { iDestruct "Hrows" as "[%Hp | #HT]"; last first.
        { iApply (ush_gets_done_taint_at Dl l i f with "HT [Hpm]").
          iApply (ush_pos_of_pm (I0 ++ J) with "HT Hpm"). }
        destruct Hp as (Hr0 & _ & _ & Hfdc & _ & _).
        (* NOTHING WAS READ: fd 0 is shut, and a shut fd 0 never delivered
           a first byte either, so the line so far is EMPTY. *)
        assert (Hi0 : i = 0%nat).
        { destruct i as [| i']; [ reflexivity | exfalso ].
          exact (ush_fd0c_not_closed l (Hfdc ltac:(lia)) Hcl). }
        assert (HJ0 : J = []) by (apply nil_length_inv; lia).
        subst i. rewrite HJ0 (app_nil_r I0).
        iDestruct "Hwc" as "[Hwc | #HT']".
        { iApply (ush_gets_done_0_at Dl l I0 f Hcl with "Hpm Hwc"). }
        iApply (ush_gets_done_taint_at Dl l 0%nat f with "HT' [Hpm]").
        iApply (ush_pos_of_pm I0 with "HT' Hpm"). }
      { iApply (ush_gets_done_taint_at Dl l i f with "HT Hp"). } }
    assert (Eae6 : add_vec_int (mword_of_int 0xae6 : mword 64) 4
                   = mword_of_int 0xaea)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Eae6. iIntros (h10) "Hrun".
    (* THE READ DELIVERED A BYTE, so the answer is the WINDOW arm or the
       taint: a shut fd 0 answers [-1], which this branch is not at. *)
    assert (Hretp : (0 < bv_signed ret)%Z).
    { destruct (Z.le_gt_cases (bv_signed ret) 0) as [Hle | Hgt]; [ | lia ].
      exfalso.
      assert (Hg : Z.geb 0 (bv_signed ret) = true) by (apply Z.geb_le; lia).
      rewrite Hg in Htk6v. discriminate Htk6v. }
    (* THE BYTE IT DELIVERED, AS THE DISCIPLINE READS IT: the input grew
       by that one byte and is disciplined still, which is what decides
       every branch below -- '\n' closes an admissible line, '\r' cannot
       happen, and anything else is a body byte the line grows by. *)
    iAssert ((⌜Dsc ((I0 ++ J) ++ [g1 0%nat])⌝
              ∗ ⌜ush_fd0c l⌝ ∗ Pm ((I0 ++ J) ++ [g1 0%nat]))
             ∨ (T ∗ ush_pos))%I with "[Hans]" as "Hans".
    { iDestruct "Hans"
        as "[(_ & %Hb & %Hfdc & Hpm) | [(%Hle & _ & _) | [#HT Hp]]]".
      - iLeft. iSplitR; [ by iPureIntro | ].
        iSplitR; [ by iPureIntro | ]. iExact "Hpm".
      - exfalso. lia.
      - iRight. iFrame "HT Hp". }
    (* ---- 0xaea  lbu a5,-81(s0) -- read the byte back out of the frame -- *)
    set (bz := bv_unsigned (g1 0%nat)).
    assert (Hbzr : 0 <= bz < 256).
    { unfold bz. pose proof (bv_unsigned_in_range 8 (g1 0%nat)) as Hr.
      assert (Em8 : bv_modulus 8 = 256) by (vm_compute; reflexivity).
      rewrite Em8 in Hr. exact Hr. }
    assert (Hs0_8 : m8 !!! Regidx s0_idx = mword_of_int spz)
      by (rewrite (P18 s0_idx ltac:(vm_compute; reflexivity)); exact Hs0).
    iApply (wp_uk_lbu N h10 m8 (mword_of_int 0xaea)
              (mword_of_int 4015 : mword 12) s0_idx a5_idx (DfracOwn 1)
              (spz - 81) (g1 0%nat) nn
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(rewrite Hs0_8 (uint_moi spz ltac:(unfold Z64 in *; lia));
                    vm_compute uoff_i12; lia)
              ltac:(vm_compute; discriminate)
              with "[] Hb Hrun").
    { iApply (uis_shk_aea with "Hcode"). }
    iIntros "Hb".
    assert (Eaea : add_vec_int (mword_of_int 0xaea : mword 64) 4
                   = mword_of_int 0xaee)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Eaea. iIntros (h11) "Hrun".
    set (m9 := <[Regidx a5_idx
                 := regval_into_reg (zero_extend' 64 (g1 0%nat : mword 8)
                                     : mword 64)]> m8).
    assert (P9 : forall r : mword 5, ush_gets_keep r = true ->
                   m9 !!! Regidx r = m8 !!! Regidx r)
      by (intros r Hr; exact (upd_ne m8 (Regidx a5_idx) (Regidx r) _
                                (ush_keep_ne r a5_idx Hr
                                   ltac:(vm_compute; reflexivity)))).
    assert (Ha5_9 : m9 !!! Regidx a5_idx = mword_of_int bz).
    { rewrite (upd_eq m8 (Regidx a5_idx)
                 (regval_into_reg (zero_extend' 64 (g1 0%nat : mword 8)
                                   : mword 64))).
      exact (zext8_moi (g1 0%nat)). }
    (* ---- 0xaee  sb a5,0(s2) -- buf[i] := c ---- *)
    assert (Hs2_9 : m9 !!! Regidx s2_idx = mword_of_int (a + Z.of_nat i)).
    { rewrite (upd_ne m8 (Regidx a5_idx) (Regidx s2_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne _ (Regidx a0_idx) (Regidx s2_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne m7 (Regidx a7_idx) (Regidx s2_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne m6 (Regidx ra_idx) (Regidx s2_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne m5 (Regidx a0_idx) (Regidx s2_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne m4 (Regidx a1_idx) (Regidx s2_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne m3 (Regidx a2_idx) (Regidx s2_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne m2 (Regidx s1_idx) (Regidx s2_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne m1 (Regidx s3_idx) (Regidx s2_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne mc (Regidx s8_idx) (Regidx s2_idx) _
                 ltac:(vm_compute; discriminate)). exact Hs2. }
    iDestruct (ush_bytes_upd a Nb i f ltac:(lia) with "Hbs") as "[Hbi Hcl]".
    iApply (wp_uk_sb N h11 m9 (mword_of_int 0xaee)
              (mword_of_int 0 : mword 12) s2_idx a5_idx
              (a + Z.of_nat i) (f i) nn
              ltac:(rewrite Hs2_9 (uint_moi (a + Z.of_nat i)
                                     ltac:(unfold Z64 in *; lia));
                    vm_compute uoff_i12; lia)
              with "[] Hbi Hrun").
    { iApply (uis_shk_aee with "Hcode"). }
    iIntros "Hbi".
    iDestruct ("Hcl" $! (nth_byte (m9 !!! Regidx a5_idx) 0) with "Hbi")
      as "Hbs".
    assert (Eaee : add_vec_int (mword_of_int 0xaee : mword 64) 4
                   = mword_of_int 0xaf2)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Eaee. iIntros (h12) "Hrun".
    (* ---- 0xaf2  c.addi s2,s2,1 ---- *)
    assert (E1c : (sign_extend' 64 (mword_of_int 1 : mword 6) : mword 64)
                  = mword_of_int 1)
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uk_caddi N h12 m9 (mword_of_int 0xaf2)
              (mword_of_int 1 : mword 6) s2_idx
              (mword_of_int (a + Z.of_nat (i + 1))) nn
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs2_9 E1c moi_add;
                    replace (a + Z.of_nat (i + 1)) with (a + Z.of_nat i + 1)
                      by lia; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_af2 with "Hcode"). }
    assert (Eaf2 : add_vec_int (mword_of_int 0xaf2 : mword 64) 2
                   = mword_of_int 0xaf4)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Eaf2. iIntros (h13) "Hrun".
    set (mA := <[Regidx s2_idx
                 := regval_into_reg (mword_of_int (a + Z.of_nat (i + 1))
                                     : mword 64)]> m9).
    assert (PA : forall r : mword 5, ush_gets_keep r = true ->
                   mA !!! Regidx r = m9 !!! Regidx r)
      by (intros r Hr; exact (upd_ne m9 (Regidx s2_idx) (Regidx r) _
                                (ush_keep_ne r s2_idx Hr
                                   ltac:(vm_compute; reflexivity)))).
    assert (Ha5_A : mA !!! Regidx a5_idx = mword_of_int bz).
    { rewrite (upd_ne m9 (Regidx s2_idx) (Regidx a5_idx) _
                 ltac:(vm_compute; discriminate)). exact Ha5_9. }
    assert (Hs2_A : mA !!! Regidx s2_idx
                    = mword_of_int (a + Z.of_nat (i + 1)))
      by exact (upd_eq m9 (Regidx s2_idx)
                  (regval_into_reg (mword_of_int (a + Z.of_nat (i + 1))
                                    : mword 64))).
    (* ---- 0xaf4  addi a4,a5,-10 ---- *)
    iApply (wp_uk_addi N h13 mA (mword_of_int 0xaf4)
              (mword_of_int 4086 : mword 12) a5_idx a4_idx
              (mword_of_int (bz - 10)) nn
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha5_A;
                    exact (ush_addi_sub bz 10 (mword_of_int 4086 : mword 12)
                             ltac:(unfold Z64; lia)
                             ltac:(vm_compute; reflexivity)))
              with "[] Hrun").
    { iApply (uis_shk_af4 with "Hcode"). }
    assert (Eaf4 : add_vec_int (mword_of_int 0xaf4 : mword 64) 4
                   = mword_of_int 0xaf8)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Eaf4. iIntros (h14) "Hrun".
    set (mB := <[Regidx a4_idx
                 := regval_into_reg (mword_of_int (bz - 10) : mword 64)]> mA).
    assert (PB : forall r : mword 5, ush_gets_keep r = true ->
                   mB !!! Regidx r = mA !!! Regidx r)
      by (intros r Hr; exact (upd_ne mA (Regidx a4_idx) (Regidx r) _
                                (ush_keep_ne r a4_idx Hr
                                   ltac:(vm_compute; reflexivity)))).
    assert (Hs3_B : mB !!! Regidx s3_idx = mword_of_int (Z.of_nat i + 1)).
    { rewrite (upd_ne mA (Regidx a4_idx) (Regidx s3_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne m9 (Regidx s2_idx) (Regidx s3_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne m8 (Regidx a5_idx) (Regidx s3_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne _ (Regidx a0_idx) (Regidx s3_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne m7 (Regidx a7_idx) (Regidx s3_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne m6 (Regidx ra_idx) (Regidx s3_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne m5 (Regidx a0_idx) (Regidx s3_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne m4 (Regidx a1_idx) (Regidx s3_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne m3 (Regidx a2_idx) (Regidx s3_idx) _
                 ltac:(vm_compute; discriminate)). exact Hs3_3. }
    (* ---- 0xaf8  c.beqz a4,0xafe -- '\n' ends the line, AS A NUMBER
       (lane IO-LEAF, M5(3)): which arm this is decides whether the line
       the walk is assembling is finished. *)
    assert (Ha4_B : mB !!! Regidx a4_idx = mword_of_int (bz - 10))
      by exact (upd_eq mA (Regidx a4_idx)
                  (regval_into_reg (mword_of_int (bz - 10) : mword 64))).
    remember (eq_vec (mB !!! Regidx a4_idx) zero_reg) as tk8 eqn:Htk8e.
    assert (Htk8v : tk8 = Z.eqb bz 10).
    { rewrite Htk8e Ha4_B.
      exact (ush_eqz_sub bz 10 ltac:(unfold Z64; lia)
               ltac:(unfold Z64; lia)). }
    iApply (wp_uk_cbeqz N h14 mB (mword_of_int 0xaf8)
              (mword_of_int 3 : mword 8) (mword_of_int 6 : mword 3) a4_idx
              tk8 (mword_of_int 0xafe) nn
              ltac:(vm_compute; reflexivity) Htk8e
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(intros _; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_af8 with "Hcode"). }
    (* the two arms differ only in whether 0xafa/0xafc run first; both end
       at 0xafe with s8 := s3 = i+1, or go round again *)
    destruct tk8.
    { (* '\n': straight to 0xafe *)
      iIntros (h15) "Hrun".
      iApply (wp_uk_cmv N h15 mB (mword_of_int 0xafe) s8_idx s3_idx
                (mword_of_int (Z.of_nat i + 1)) nn
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite Hs3_B moi_add_zero_l; reflexivity)
                with "[] Hrun").
      { iApply (uis_shk_afe with "Hcode"). }
      assert (Eafe : add_vec_int (mword_of_int 0xafe : mword 64) 2
                     = mword_of_int 0xb00)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite Eafe. iIntros (h16) "Hrun".
      iApply ("Hcont" $! h16 _ (i + 1)%nat
                (ush_set f i (nth_byte (m9 !!! Regidx a5_idx) 0))
                (g1 0%nat) with "[] [] [] Hbs Hb Hstd [>Hans Hwc] Hrun").
      { iPureIntro. lia. }
      { iPureIntro.
        replace (Z.of_nat (i + 1)) with (Z.of_nat i + 1) by lia.
        exact (upd_eq mB (Regidx s8_idx)
                 (regval_into_reg (mword_of_int (Z.of_nat i + 1)
                                   : mword 64))). }
      { iPureIntro. intros r Hr.
        rewrite (upd_ne mB (Regidx s8_idx) (Regidx r) _
                   (ush_keep_ne r s8_idx Hr ltac:(vm_compute; reflexivity))).
        rewrite (PB r Hr) (PA r Hr) (P9 r Hr). exact (P18 r Hr). }
      (* THE LINE IS COMPLETE: the byte just stored was '\n', so the bytes
         before it are the BODY the era just closed -- and the newline's own
         receipt says that body is an admissible line
         ([EchoDisc.disc_input_snoc_nl]).  Which line it is is [wl_words J],
         and the buffer holds [wl_line] of it. *)
      assert (Hnb : nth_byte (m9 !!! Regidx a5_idx) 0%nat = g1 0%nat)
        by (rewrite Ha5_9; exact (ush_nth_byte0_moi (g1 0%nat))).
      rewrite Hnb.
      assert (Hb10 : bz = 10)
        by (symmetry in Htk8v; apply Z.eqb_eq in Htk8v; exact Htk8v).
      assert (Hnlb : g1 0%nat = wl_nl) by (apply ush_nl_of_val; exact Hb10).
      iDestruct "Hans" as "[(%Hdisc & %Hfdc & Hpm) | [#HT Hp]]"; last first.
      { iModIntro. iApply (ush_gets_done_taint_at Dl l (i + 1)%nat _ with "HT Hp"). }
      iDestruct "Hrows" as "[%Hp | #HT]"; last first.
      { iModIntro.
        iApply (ush_gets_done_taint_at Dl l (i + 1)%nat _ with "HT [Hpm]").
        iApply (ush_pos_of_pm ((I0 ++ J) ++ [g1 0%nat]) with "HT Hpm"). }
      destruct Hp as (Hr0 & Hnlj & Hltj & Hfdc' & Hbytes & Hdj).
      rewrite Hnlb in Hdisc.
      iEval (rewrite Hnlb) in "Hpm".
      iEval (rewrite -(app_assoc I0 J [wl_nl])) in "Hpm".
      assert (Hrest : rest_of (I0 ++ J) = J).
      { rewrite /rest_of (wl_cut_app_nonl I0 J Hnlj). cbn [snd].
        rewrite Hr0. reflexivity. }
      assert (Hfnl : ush_set f i (g1 0%nat) (length J) = wl_nl).
      { rewrite <- Hij, ush_set_at. exact Hnlb. }
      assert (Hbys : forall j : nat, (j < length J)%nat ->
                       ush_set f i (g1 0%nat) j = J !!! j).
      { intros j Hj. rewrite (ush_set_lt f i j (g1 0%nat) ltac:(lia)).
        exact (Hbytes j Hj). }
      (* THE LINE THE NEWLINE CLOSED, at the era's own constructor *)
      destruct (Hdsc_line (I0 ++ J) (ush_set f i (g1 0%nat)) Hdisc
                  ltac:(rewrite Hrest; exact Hbys)
                  ltac:(rewrite Hrest; exact Hfnl))
        as (lu & HDlu & Hwslu & Hlenlu & Hlilu).
      rewrite Hrest in Hwslu, Hlenlu, Hlilu.
      assert (Hp' : ush_gline_p_at Dsc l I0 J (ush_set f i (g1 0%nat))).
      { rewrite /ush_gline_p_at. split_and!;
          [ exact Hr0 | exact Hnlj | exact Hltj | exact Hfdc' | exact Hbys
          | exact Hdj ]. }
      replace (i + 1)%nat with (S (length J)) by lia.
      iDestruct "Hwc" as "[Hwc | #HT']".
      { iApply (ush_gets_done_line_at Dsc Dl l I0 J lu
                  (ush_set f i (g1 0%nat)) Hp' HDlu Hwslu Hlenlu Hlilu Hfnl
                  with "Hwc Hpm"). }
      iModIntro.
      iApply (ush_gets_done_line_t_at Dl l (I0 ++ J ++ [wl_nl]) _
                (ush_set f i (g1 0%nat)) with "HT' Hpm"). }
    assert (Eaf8 : add_vec_int (mword_of_int 0xaf8 : mword 64) 2
                   = mword_of_int 0xafa)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Eaf8. iIntros (h15) "Hrun".
    (* ---- 0xafa  c.addi a5,a5,-13 ---- *)
    assert (E13 : (sign_extend' 64 (mword_of_int 51 : mword 6) : mword 64)
                  = mword_of_int (-13))
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uk_caddi N h15 mB (mword_of_int 0xafa)
              (mword_of_int 51 : mword 6) a5_idx
              (mword_of_int (bz - 13)) nn
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(assert (Ha5B : mB !!! Regidx a5_idx = mword_of_int bz)
                      by (rewrite (upd_ne mA (Regidx a4_idx) (Regidx a5_idx) _
                                     ltac:(vm_compute; discriminate));
                          exact Ha5_A);
                    rewrite Ha5B E13 moi_add;
                    replace (bz - 13) with (bz + -13) by lia; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_afa with "Hcode"). }
    assert (Eafa : add_vec_int (mword_of_int 0xafa : mword 64) 2
                   = mword_of_int 0xafc)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Eafa. iIntros (h16) "Hrun".
    set (mC := <[Regidx a5_idx
                 := regval_into_reg (mword_of_int (bz - 13) : mword 64)]> mB).
    assert (PC : forall r : mword 5, ush_gets_keep r = true ->
                   mC !!! Regidx r = mB !!! Regidx r)
      by (intros r Hr; exact (upd_ne mB (Regidx a5_idx) (Regidx r) _
                                (ush_keep_ne r a5_idx Hr
                                   ltac:(vm_compute; reflexivity)))).
    assert (Hs3_C : mC !!! Regidx s3_idx = mword_of_int (Z.of_nat i + 1)).
    { rewrite (upd_ne mB (Regidx a5_idx) (Regidx s3_idx) _
                 ltac:(vm_compute; discriminate)). exact Hs3_B. }
    (* ---- 0xafc  c.bnez a5,0xad0 -- '\r' ends the line too, AS A NUMBER
       (lane IO-LEAF, M5(3)): the era's line has no '\r' in it, so on the
       untainted arm this branch is never the one that falls through. *)
    assert (Ha5_C : mC !!! Regidx a5_idx = mword_of_int (bz - 13))
      by exact (upd_eq mB (Regidx a5_idx)
                  (regval_into_reg (mword_of_int (bz - 13) : mword 64))).
    remember (neq_vec (mC !!! Regidx a5_idx) zero_reg) as tkc eqn:Htkc.
    assert (Htkcv : tkc = negb (Z.eqb bz 13)).
    { rewrite Htkc Ha5_C.
      exact (ush_neqz_sub bz 13 ltac:(unfold Z64; lia)
               ltac:(unfold Z64; lia)). }
    iApply (wp_uk_cbnez N h16 mC (mword_of_int 0xafc)
              (mword_of_int 234 : mword 8) (mword_of_int 7 : mword 3) a5_idx
              tkc (mword_of_int 0xad0) nn
              ltac:(vm_compute; reflexivity) Htkc
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(intros _; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_afc with "Hcode"). }
    assert (PCall : forall r : mword 5, ush_gets_keep r = true ->
                      mC !!! Regidx r = mc !!! Regidx r).
    { intros r Hr.
      rewrite (PC r Hr) (PB r Hr) (PA r Hr) (P9 r Hr). exact (P18 r Hr). }
    destruct tkc.
    { (* not a '\r': go round again at i+1 *)
      iIntros (h17) "Hrun".
      iApply (IH (i + 1)%nat (J ++ [g1 0%nat]) h17 mC
                (ush_set f i (nth_byte (m9 !!! Regidx a5_idx) 0)) (g1 0%nat) nn
                ltac:(lia) ltac:(lia)
                ltac:(rewrite length_app; cbn [length]; lia)
                HNb Ha0 Ha64 HN31 Hsz0 Hsz1
                ltac:(rewrite (PCall s0_idx ltac:(vm_compute; reflexivity));
                      exact Hs0)
                ltac:(rewrite (upd_ne mB (Regidx a5_idx) (Regidx s1_idx) _
                                 ltac:(vm_compute; discriminate));
                      rewrite (upd_ne mA (Regidx a4_idx) (Regidx s1_idx) _
                                 ltac:(vm_compute; discriminate));
                      rewrite (upd_ne m9 (Regidx s2_idx) (Regidx s1_idx) _
                                 ltac:(vm_compute; discriminate));
                      rewrite (upd_ne m8 (Regidx a5_idx) (Regidx s1_idx) _
                                 ltac:(vm_compute; discriminate));
                      rewrite (upd_ne _ (Regidx a0_idx) (Regidx s1_idx) _
                                 ltac:(vm_compute; discriminate));
                      rewrite (upd_ne m7 (Regidx a7_idx) (Regidx s1_idx) _
                                 ltac:(vm_compute; discriminate));
                      rewrite (upd_ne m6 (Regidx ra_idx) (Regidx s1_idx) _
                                 ltac:(vm_compute; discriminate));
                      rewrite (upd_ne m5 (Regidx a0_idx) (Regidx s1_idx) _
                                 ltac:(vm_compute; discriminate));
                      rewrite (upd_ne m4 (Regidx a1_idx) (Regidx s1_idx) _
                                 ltac:(vm_compute; discriminate));
                      rewrite (upd_ne m3 (Regidx a2_idx) (Regidx s1_idx) _
                                 ltac:(vm_compute; discriminate));
                      replace (Z.of_nat (i + 1)) with (Z.of_nat i + 1) by lia;
                      exact (upd_eq m2 (Regidx s1_idx)
                               (regval_into_reg
                                  (mword_of_int (Z.of_nat i + 1) : mword 64))))
                ltac:(rewrite (upd_ne mB (Regidx a5_idx) (Regidx s2_idx) _
                                 ltac:(vm_compute; discriminate));
                      rewrite (upd_ne mA (Regidx a4_idx) (Regidx s2_idx) _
                                 ltac:(vm_compute; discriminate));
                      exact Hs2_A)
                ltac:(rewrite (PCall s4_idx ltac:(vm_compute; reflexivity));
                      exact Hs4)
                ltac:(rewrite (PCall s5_idx ltac:(vm_compute; reflexivity));
                      exact Hs5)
                ltac:(rewrite (PCall s6_idx ltac:(vm_compute; reflexivity));
                      exact Hs6)
                with "Hlaw Hcode Hbs Hb Hstd [Hans] Hwc Hrun").
      { (* ROUND AGAIN: the byte was neither '\n' nor '\r', so it was a
           BODY byte and the line grows by it.  That it still fits the
           buffer is the receipt's own reading of the input
           ([EchoDisc.disc_input_rest_short] at the remainder the cut
           leaves), which is where the loop's bound comes from now. *)
        assert (Hnb : nth_byte (m9 !!! Regidx a5_idx) 0%nat = g1 0%nat)
          by (rewrite Ha5_9; exact (ush_nth_byte0_moi (g1 0%nat))).
        rewrite Hnb. rewrite /ush_gets_line_at.
        iDestruct "Hans" as "[(%Hdisc & %Hfdc & Hpm) | [#HT Hp]]"; last first.
        { iRight. iFrame "HT Hp". }
        iDestruct "Hrows" as "[%Hp | #HT]"; last first.
        { iRight. iFrame "HT".
          iApply (ush_pos_of_pm ((I0 ++ J) ++ [g1 0%nat]) with "HT Hpm"). }
        destruct Hp as (Hr0 & Hnlj & Hltj & Hfdc' & Hbytes & _).
        assert (Hb10 : bz <> 10)
          by (symmetry in Htk8v; apply Z.eqb_neq in Htk8v; exact Htk8v).
        assert (Hbne : g1 0%nat <> wl_nl)
          by (apply ush_nl_ne_of_val; exact Hb10).
        (* the cut of the input after this byte: the boundary's remainder is
           empty, so the remainder IS the line so far and one more byte *)
        assert (Hrest : rest_of ((I0 ++ J) ++ [g1 0%nat]) = J ++ [g1 0%nat]).
        { rewrite (rest_of_snoc_other (I0 ++ J) (g1 0%nat) Hbne).
          rewrite /rest_of (wl_cut_app_nonl I0 J Hnlj). cbn [snd].
          rewrite Hr0. reflexivity. }
        pose proof (Hdsc_short _ Hdisc) as Hshort.
        rewrite Hrest length_app in Hshort. cbn [length] in Hshort.
        iLeft. iSplitR.
        { iPureIntro. rewrite /ush_gline_p_at. split_and!.
          - exact Hr0.
          - exact (wl_nonl_app J [g1 0%nat] Hnlj
                     (wl_nonl_cons_2 (g1 0%nat) [] Hbne (not_elem_of_nil _))).
          - rewrite length_app. cbn [length]. lia.
          - intros _. exact Hfdc.
          - intros j Hj. rewrite length_app in Hj. cbn [length] in Hj.
            destruct (Nat.eq_dec j i) as [-> | Hne].
            + rewrite ush_set_at Hij.
              pose proof (wl_lta_app_r J [g1 0%nat] 0%nat) as Hr.
              rewrite Nat.add_0_r in Hr. by rewrite Hr.
            + rewrite (ush_set_lt f i j (g1 0%nat) ltac:(lia)).
              rewrite (wl_lta_app_l J [g1 0%nat] j ltac:(lia)).
              apply Hbytes. lia.
          - intros _. rewrite (app_assoc I0 J [g1 0%nat]). exact Hdisc. }
        rewrite (app_assoc I0 J [g1 0%nat]). iExact "Hpm". }
      iIntros (h18 mc'' i2 g2 bc2) "%Hi2 %Hs8'' %Hp'' Hbs Hb Hstd Hpos Hrun".
      iApply ("Hcont" $! h18 mc'' i2 g2 bc2
                with "[%] [%] [%] Hbs Hb Hstd Hpos Hrun");
        [ exact Hi2 | exact Hs8'' | ].
      intros r Hr. rewrite (Hp'' r Hr). exact (PCall r Hr). }
    (* a '\r': fall into 0xafe *)
    assert (Eafc : add_vec_int (mword_of_int 0xafc : mword 64) 2
                   = mword_of_int 0xafe)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Eafc. iIntros (h17) "Hrun".
    iApply (wp_uk_cmv N h17 mC (mword_of_int 0xafe) s8_idx s3_idx
              (mword_of_int (Z.of_nat i + 1)) nn
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs3_C moi_add_zero_l; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_afe with "Hcode"). }
    assert (Eafe : add_vec_int (mword_of_int 0xafe : mword 64) 2
                   = mword_of_int 0xb00)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Eafe. iIntros (h18) "Hrun".
    iApply ("Hcont" $! h18 _ (i + 1)%nat
              (ush_set f i (nth_byte (m9 !!! Regidx a5_idx) 0))
              (g1 0%nat) with "[] [] [] Hbs Hb Hstd [Hans] Hrun").
    { iPureIntro. lia. }
    { iPureIntro.
      replace (Z.of_nat (i + 1)) with (Z.of_nat i + 1) by lia.
      exact (upd_eq mC (Regidx s8_idx)
               (regval_into_reg (mword_of_int (Z.of_nat i + 1) : mword 64))). }
    { iPureIntro. intros r Hr.
      rewrite (upd_ne mC (Regidx s8_idx) (Regidx r) _
                 (ush_keep_ne r s8_idx Hr ltac:(vm_compute; reflexivity))).
      exact (PCall r Hr). }
    (* A '\r' ENDS THE LINE TOO -- and no disciplined input carries one, at
       any line ([EchoDisc.disc_input_byte_val] on the byte just received),
       so on the untainted arm this arm is empty. *)
    assert (Hb13 : bz = 13).
    { symmetry in Htkcv. apply negb_false_iff in Htkcv.
      apply Z.eqb_eq in Htkcv. exact Htkcv. }
    iDestruct "Hans" as "[(%Hdisc & _ & Hpm) | [#HT Hp]]"; last first.
    { iApply (ush_gets_done_taint_at Dl l (i + 1)%nat _ with "HT Hp"). }
    exfalso.
    pose proof (Hdsc_ncr (I0 ++ J) (g1 0%nat) Hdisc) as Hv.
    unfold bz in Hb13. lia.
  Qed.


  (* the twelve-word frame, opened and closed DIRECTIONALLY.  A [⊣⊢] split
     used under [rewrite] inside a proofmode goal fires on the whole
     [envs_entails], context included; UserHeap.v's own header records what
     that cost at four words.  Here the goal is two lines long. *)
  Local Lemma ush_stack_12_open (sp : mword 64) :
    ustack γd sp 12 -∗
      ⌜ uint sp mod 8 = 0 ⌝ ∗
      (∃ w : mword 64, uword γd (uint sp - 8) w) ∗
      (∃ w : mword 64, uword γd (uint sp - 16) w) ∗
      (∃ w : mword 64, uword γd (uint sp - 24) w) ∗
      (∃ w : mword 64, uword γd (uint sp - 32) w) ∗
      (∃ w : mword 64, uword γd (uint sp - 40) w) ∗
      (∃ w : mword 64, uword γd (uint sp - 48) w) ∗
      (∃ w : mword 64, uword γd (uint sp - 56) w) ∗
      (∃ w : mword 64, uword γd (uint sp - 64) w) ∗
      (∃ w : mword 64, uword γd (uint sp - 72) w) ∗
      (∃ w : mword 64, uword γd (uint sp - 80) w) ∗
      (∃ w : mword 64, uword γd (uint sp - 88) w) ∗
      (∃ w : mword 64, uword γd (uint sp - 96) w).
  Proof using . rewrite ustack_12. iIntros "$". Qed.

  Local Lemma ush_stack_12_close (sp : mword 64) :
    ⌜ uint sp mod 8 = 0 ⌝ -∗
    (∃ w : mword 64, uword γd (uint sp - 8) w) -∗
    (∃ w : mword 64, uword γd (uint sp - 16) w) -∗
    (∃ w : mword 64, uword γd (uint sp - 24) w) -∗
    (∃ w : mword 64, uword γd (uint sp - 32) w) -∗
    (∃ w : mword 64, uword γd (uint sp - 40) w) -∗
    (∃ w : mword 64, uword γd (uint sp - 48) w) -∗
    (∃ w : mword 64, uword γd (uint sp - 56) w) -∗
    (∃ w : mword 64, uword γd (uint sp - 64) w) -∗
    (∃ w : mword 64, uword γd (uint sp - 72) w) -∗
    (∃ w : mword 64, uword γd (uint sp - 80) w) -∗
    (∃ w : mword 64, uword γd (uint sp - 88) w) -∗
    (∃ w : mword 64, uword γd (uint sp - 96) w) -∗
    ustack γd sp 12.
  Proof using .
    rewrite ustack_12.
    iIntros "%H H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12".
    iSplit; [ iPureIntro; exact H | ].
    (* BUILT, not framed: a bare [iFrame] over twelve [∃]-wrapped cells is
       twelve goal walks (claude-notes/optimization.md, "a rebuild is a
       construction, so build it"). *)
    iSplitL "H1"; [iExact "H1"|].
    iSplitL "H2"; [iExact "H2"|].
    iSplitL "H3"; [iExact "H3"|].
    iSplitL "H4"; [iExact "H4"|].
    iSplitL "H5"; [iExact "H5"|].
    iSplitL "H6"; [iExact "H6"|].
    iSplitL "H7"; [iExact "H7"|].
    iSplitL "H8"; [iExact "H8"|].
    iSplitL "H9"; [iExact "H9"|].
    iSplitL "H10"; [iExact "H10"|].
    iSplitL "H11"; [iExact "H11"|].
    iExact "H12".
  Qed.

  (* the callee-saved set, as an arithmetic disjunction *)
  Local Lemma ucs_cases (r : mword 5) :
    ucallee_saved_idx r = true ->
    uint r = 2 \/ uint r = 3 \/ uint r = 4 \/ uint r = 8 \/ uint r = 9 \/
    (18 <= uint r <= 27).
  Proof using .
    unfold ucallee_saved_idx. intro H.
    repeat (apply orb_prop in H as [H | H]).
    all: try (apply Z.eqb_eq in H; lia).
    apply andb_prop in H as [H1 H2].
    apply Z.leb_le in H1. apply Z.leb_le in H2. lia.
  Qed.

  Local Lemma ush_r_ne (r : mword 5) (z : Z) (q : mword 5) :
    uint q = z -> uint r <> z -> Regidx r <> Regidx q.
  Proof using . intros Hq Hr. apply ush_ridx_ne. rewrite Hq. exact Hr. Qed.

  (* ---- gets, the whole function --------------------------------------- *)
  (* DEPENDS ON [ush_read_leaf].                                            *)
  Lemma wp_ksh_gets (h : CpuId) (m : regfile) (a : Z) (Nb : nat)
      (f : nat -> bv 8) (l : list fdstate) (nn : nat) :
    m !!! Regidx a0_idx = mword_of_int a ->
    m !!! Regidx a1_idx = mword_of_int (Z.of_nat Nb) ->
    (* ROOM FOR A WHOLE LINE, which is what makes the walk's only exits
       "nothing read" and "one line read" (lane IO-LEAF, M5(3)): the buffer
       IS as long as the longest admissible line ([sh_nbuf_line_max]) *)
    Nb = sh_nbuf -> Z.of_nat Nb < Z31 ->
    ush_fd0p l ->
    ush_tag_law -∗
    shk_code γt -∗
    ubytes γd a Nb f -∗
    ush_std l -∗
    (* AT THE PROMPT'S END (lane IO-LEAF, M6a(3)): the credential the
       prompt left rides in, and comes out at the next boundary *)
    ush_posb l 2%nat -∗
    urun N h m (mword_of_int ShSyms.gets) (12 + nn) -∗
    ((∃ (g : nat -> bv 8) (i2 : nat),
        ⌜ (i2 < Nb)%nat /\ g i2 = ubyte0 ⌝ ∗ ubytes γd a Nb g ∗
        ush_std l ∗ ush_gets_done_at Dl l i2 g) -∗
       ∀ (h' : CpuId) (m' : regfile),
         ⌜ ucallee_saved m m' ⌝ -∗
         urun N h' m' (ret_pc (m !!! Regidx ra_idx)) (12 + nn) -∗
         mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using Hdsc_ncr Hdsc_line Hdsc_short HT ush_at_of_pm_taint ush_at_of_pm_wb ush_read_leaf ush_wb_read ush_wc_read.
    intros Ha0 Ha1 HNle HN31 Hfd0.
    assert (HN0 : (0 < Nb)%nat)
      by (rewrite HNle; unfold sh_nbuf; lia).
    iIntros "#Hlaw #Hcode Hbs Hstd Hpos Hrun Hcont".
    rewrite shp_gets.
    iDestruct (urun_stack with "Hrun") as %[Hal8 Hroom].
    iDestruct (urun_ubytes_bnd h m _ (12 + nn) (DfracOwn 1) a Nb f ltac:(lia)
                 with "Hrun Hbs") as %[Halo Hahi].
    change (2 ^ 38) with 274877906944 in Hahi.
    remember (m !!! Regidx csp_rs1) as sp0 eqn:Hsp0.
    assert (Hsp : m !!! Regidx csp_rs1 = sp0) by (symmetry; exact Hsp0).
    clear Hsp0.
    set (spz := uint sp0).
    assert (Hspm : (mword_of_int spz : mword 64) = sp0)
      by (unfold spz; rewrite uint_unsigned; exact (moi_of_unsigned sp0)).
    assert (Hlo : 96 <= spz) by (unfold spz; lia).
    assert (Hhi : spz < Z64).
    { unfold spz. rewrite uint_unsigned.
      pose proof (bv_unsigned_in_range 64 sp0) as Hr. rewrite Zmod64 in Hr.
      destruct Hr as [_ Hr2]. exact Hr2. }
    assert (Hbsp : bv_unsigned (add_vec_int sp0 (- (8 * Z.of_nat 12)))
                   = bv_unsigned sp0 - 96).
    { replace (- (8 * Z.of_nat 12)) with (-96) by lia.
      exact (uv_avi_neg sp0 96 ltac:(lia) ltac:(rewrite <- uint_unsigned; lia)). }
    assert (Hsp96 : uint (add_vec_int sp0 (- (8 * Z.of_nat 12))) = spz - 96)
      by (unfold spz; rewrite !uint_unsigned; exact Hbsp).
    assert (Ho2 : uoff_sdsp (mword_of_int 2 : mword 6) = 16)
      by (vm_compute; reflexivity).
    assert (Ho3 : uoff_sdsp (mword_of_int 3 : mword 6) = 24)
      by (vm_compute; reflexivity).
    assert (Ho4 : uoff_sdsp (mword_of_int 4 : mword 6) = 32)
      by (vm_compute; reflexivity).
    assert (Ho5 : uoff_sdsp (mword_of_int 5 : mword 6) = 40)
      by (vm_compute; reflexivity).
    assert (Ho6 : uoff_sdsp (mword_of_int 6 : mword 6) = 48)
      by (vm_compute; reflexivity).
    assert (Ho7 : uoff_sdsp (mword_of_int 7 : mword 6) = 56)
      by (vm_compute; reflexivity).
    assert (Ho8 : uoff_sdsp (mword_of_int 8 : mword 6) = 64)
      by (vm_compute; reflexivity).
    assert (Ho9 : uoff_sdsp (mword_of_int 9 : mword 6) = 72)
      by (vm_compute; reflexivity).
    assert (Ho10 : uoff_sdsp (mword_of_int 10 : mword 6) = 80)
      by (vm_compute; reflexivity).
    assert (Ho11 : uoff_sdsp (mword_of_int 11 : mword 6) = 88)
      by (vm_compute; reflexivity).
    (* ---- 0xaaa  c.addi16sp sp,sp,-96 -- THE PUSH ---- *)
    iApply (wp_uk_caddi16sp_dn N h m (mword_of_int 0xaaa)
              (mword_of_int 58 : mword 6) 12 nn
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_aaa with "Hcode"). }
    assert (Eaaa : add_vec_int (mword_of_int 0xaaa : mword 64) 2
                   = mword_of_int 0xaac)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Hsp Eaaa.
    iIntros "Hfr" (h1) "Hrun".
    iDestruct (ush_stack_12_open with "Hfr")
      as "(_ & [%v1 Hw1] & [%v2 Hw2] & [%v3 Hw3] & [%v4 Hw4] & [%v5 Hw5]
           & [%v6 Hw6] & [%v7 Hw7] & [%v8 Hw8] & [%v9 Hw9] & [%v10 Hw10]
           & [%v11 Hw11] & [%v12 Hw12])".
    set (m1 := <[Regidx csp_rs1
                 := regval_into_reg (add_vec_int sp0 (- (8 * Z.of_nat 12)))]> m).
    assert (Hsp1 : m1 !!! Regidx csp_rs1
                   = add_vec_int sp0 (- (8 * Z.of_nat 12)))
      by exact (upd_eq m (Regidx csp_rs1)
                  (regval_into_reg (add_vec_int sp0 (- (8 * Z.of_nat 12))))).
    assert (Hm1 : forall r : mword 5, Regidx r <> Regidx csp_rs1 ->
                    m1 !!! Regidx r = m !!! Regidx r)
      by (intros r Hr; exact (upd_ne m (Regidx csp_rs1) (Regidx r) _ Hr)).
    (* ---- 0xaac..0xabe  the ten spills ---- *)
    iApply (wp_uk_csdsp N h1 m1 (mword_of_int 0xaac)
              (mword_of_int 11 : mword 6) ra_idx (spz - 8) v1 nn
              ltac:(rewrite Hsp1 Hsp96 Ho11; lia)
              ltac:(unfold spz; rewrite Zminus_mod Hal8; reflexivity)
              with "[] Hw1 Hrun").
    { iApply (uis_shk_aac with "Hcode"). }
    iIntros "Hw1". rewrite (Hm1 ra_idx ltac:(vm_compute; discriminate)).
    assert (Eg1 : add_vec_int (mword_of_int 0xaac : mword 64) 2
                 = mword_of_int 0xaae) by (apply bv_eq; vm_compute; reflexivity).
    rewrite Eg1. clear Eg1.
    iIntros (h2) "Hrun".
    iApply (wp_uk_csdsp N h2 m1 (mword_of_int 0xaae)
              (mword_of_int 10 : mword 6) s0_idx (spz - 16) v2 nn
              ltac:(rewrite Hsp1 Hsp96 Ho10; lia)
              ltac:(unfold spz; rewrite Zminus_mod Hal8; reflexivity)
              with "[] Hw2 Hrun").
    { iApply (uis_shk_aae with "Hcode"). }
    iIntros "Hw2". rewrite (Hm1 s0_idx ltac:(vm_compute; discriminate)).
    assert (Eg2 : add_vec_int (mword_of_int 0xaae : mword 64) 2
                 = mword_of_int 0xab0) by (apply bv_eq; vm_compute; reflexivity).
    rewrite Eg2. clear Eg2.
    iIntros (h3) "Hrun".
    iApply (wp_uk_csdsp N h3 m1 (mword_of_int 0xab0)
              (mword_of_int 9 : mword 6) s1_idx (spz - 24) v3 nn
              ltac:(rewrite Hsp1 Hsp96 Ho9; lia)
              ltac:(unfold spz; rewrite Zminus_mod Hal8; reflexivity)
              with "[] Hw3 Hrun").
    { iApply (uis_shk_ab0 with "Hcode"). }
    iIntros "Hw3". rewrite (Hm1 s1_idx ltac:(vm_compute; discriminate)).
    assert (Eg3 : add_vec_int (mword_of_int 0xab0 : mword 64) 2
                 = mword_of_int 0xab2) by (apply bv_eq; vm_compute; reflexivity).
    rewrite Eg3. clear Eg3.
    iIntros (h4) "Hrun".
    iApply (wp_uk_csdsp N h4 m1 (mword_of_int 0xab2)
              (mword_of_int 8 : mword 6) s2_idx (spz - 32) v4 nn
              ltac:(rewrite Hsp1 Hsp96 Ho8; lia)
              ltac:(unfold spz; rewrite Zminus_mod Hal8; reflexivity)
              with "[] Hw4 Hrun").
    { iApply (uis_shk_ab2 with "Hcode"). }
    iIntros "Hw4". rewrite (Hm1 s2_idx ltac:(vm_compute; discriminate)).
    assert (Eg4 : add_vec_int (mword_of_int 0xab2 : mword 64) 2
                 = mword_of_int 0xab4) by (apply bv_eq; vm_compute; reflexivity).
    rewrite Eg4. clear Eg4.
    iIntros (h5) "Hrun".
    iApply (wp_uk_csdsp N h5 m1 (mword_of_int 0xab4)
              (mword_of_int 7 : mword 6) s3_idx (spz - 40) v5 nn
              ltac:(rewrite Hsp1 Hsp96 Ho7; lia)
              ltac:(unfold spz; rewrite Zminus_mod Hal8; reflexivity)
              with "[] Hw5 Hrun").
    { iApply (uis_shk_ab4 with "Hcode"). }
    iIntros "Hw5". rewrite (Hm1 s3_idx ltac:(vm_compute; discriminate)).
    assert (Eg5 : add_vec_int (mword_of_int 0xab4 : mword 64) 2
                 = mword_of_int 0xab6) by (apply bv_eq; vm_compute; reflexivity).
    rewrite Eg5. clear Eg5.
    iIntros (h6) "Hrun".
    iApply (wp_uk_csdsp N h6 m1 (mword_of_int 0xab6)
              (mword_of_int 6 : mword 6) s4_idx (spz - 48) v6 nn
              ltac:(rewrite Hsp1 Hsp96 Ho6; lia)
              ltac:(unfold spz; rewrite Zminus_mod Hal8; reflexivity)
              with "[] Hw6 Hrun").
    { iApply (uis_shk_ab6 with "Hcode"). }
    iIntros "Hw6". rewrite (Hm1 s4_idx ltac:(vm_compute; discriminate)).
    assert (Eg6 : add_vec_int (mword_of_int 0xab6 : mword 64) 2
                 = mword_of_int 0xab8) by (apply bv_eq; vm_compute; reflexivity).
    rewrite Eg6. clear Eg6.
    iIntros (h7) "Hrun".
    iApply (wp_uk_csdsp N h7 m1 (mword_of_int 0xab8)
              (mword_of_int 5 : mword 6) s5_idx (spz - 56) v7 nn
              ltac:(rewrite Hsp1 Hsp96 Ho5; lia)
              ltac:(unfold spz; rewrite Zminus_mod Hal8; reflexivity)
              with "[] Hw7 Hrun").
    { iApply (uis_shk_ab8 with "Hcode"). }
    iIntros "Hw7". rewrite (Hm1 s5_idx ltac:(vm_compute; discriminate)).
    assert (Eg7 : add_vec_int (mword_of_int 0xab8 : mword 64) 2
                 = mword_of_int 0xaba) by (apply bv_eq; vm_compute; reflexivity).
    rewrite Eg7. clear Eg7.
    iIntros (h8) "Hrun".
    iApply (wp_uk_csdsp N h8 m1 (mword_of_int 0xaba)
              (mword_of_int 4 : mword 6) s6_idx (spz - 64) v8 nn
              ltac:(rewrite Hsp1 Hsp96 Ho4; lia)
              ltac:(unfold spz; rewrite Zminus_mod Hal8; reflexivity)
              with "[] Hw8 Hrun").
    { iApply (uis_shk_aba with "Hcode"). }
    iIntros "Hw8". rewrite (Hm1 s6_idx ltac:(vm_compute; discriminate)).
    assert (Eg8 : add_vec_int (mword_of_int 0xaba : mword 64) 2
                 = mword_of_int 0xabc) by (apply bv_eq; vm_compute; reflexivity).
    rewrite Eg8. clear Eg8.
    iIntros (h9) "Hrun".
    iApply (wp_uk_csdsp N h9 m1 (mword_of_int 0xabc)
              (mword_of_int 3 : mword 6) s7_idx (spz - 72) v9 nn
              ltac:(rewrite Hsp1 Hsp96 Ho3; lia)
              ltac:(unfold spz; rewrite Zminus_mod Hal8; reflexivity)
              with "[] Hw9 Hrun").
    { iApply (uis_shk_abc with "Hcode"). }
    iIntros "Hw9". rewrite (Hm1 s7_idx ltac:(vm_compute; discriminate)).
    assert (Eg9 : add_vec_int (mword_of_int 0xabc : mword 64) 2
                 = mword_of_int 0xabe) by (apply bv_eq; vm_compute; reflexivity).
    rewrite Eg9. clear Eg9.
    iIntros (h10) "Hrun".
    iApply (wp_uk_csdsp N h10 m1 (mword_of_int 0xabe)
              (mword_of_int 2 : mword 6) s8_idx (spz - 80) v10 nn
              ltac:(rewrite Hsp1 Hsp96 Ho2; lia)
              ltac:(unfold spz; rewrite Zminus_mod Hal8; reflexivity)
              with "[] Hw10 Hrun").
    { iApply (uis_shk_abe with "Hcode"). }
    iIntros "Hw10". rewrite (Hm1 s8_idx ltac:(vm_compute; discriminate)).
    assert (Eg10 : add_vec_int (mword_of_int 0xabe : mword 64) 2
                 = mword_of_int 0xac0) by (apply bv_eq; vm_compute; reflexivity).
    rewrite Eg10. clear Eg10.
    iIntros (h11) "Hrun".
    (* ---- 0xac0  c.addi4spn s0,sp,96 -- the frame pointer IS sp0 ---- *)
    assert (Hci : (sign_extend' 64 (caddi4spn_imm (mword_of_int 24 : mword 8))
                   : mword 64) = mword_of_int (8 * Z.of_nat 12))
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Hbu : bv_unsigned sp0 = spz)
      by (unfold spz; rewrite uint_unsigned; reflexivity).
    assert (Hlt12 : bv_unsigned (add_vec_int sp0 (- (8 * Z.of_nat 12)))
                    + 8 * Z.of_nat 12 < Z64)
      by (rewrite Hbsp Hbu; lia).
    assert (Hup : add_vec_int (add_vec_int sp0 (- (8 * Z.of_nat 12)))
                    (8 * Z.of_nat 12) = sp0).
    { apply bv_eq.
      rewrite (uv_avi_pos (add_vec_int sp0 (- (8 * Z.of_nat 12)))
                 (8 * Z.of_nat 12) ltac:(lia) Hlt12).
      rewrite Hbsp. lia. }
    iApply (wp_uk_caddi4spn N h11 m1 (mword_of_int 0xac0)
              (mword_of_int 0 : mword 3) (mword_of_int 24 : mword 8) s0_idx
              sp0 nn
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
              ltac:(rewrite Hsp1 Hci; unfold add_vec_int in Hup; exact (eq_sym Hup))
              with "[] Hrun").
    { iApply (uis_shk_ac0 with "Hcode"). }
    assert (Eg11 : add_vec_int (mword_of_int 0xac0 : mword 64) 2
                 = mword_of_int 0xac2) by (apply bv_eq; vm_compute; reflexivity).
    rewrite Eg11. clear Eg11.
    iIntros (h12) "Hrun".
    set (m2 := <[Regidx s0_idx := regval_into_reg sp0]> m1).
    assert (Ha0_2 : m2 !!! Regidx a0_idx = mword_of_int a).
    { rewrite (upd_ne m1 (Regidx s0_idx) (Regidx a0_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (Hm1 a0_idx ltac:(vm_compute; discriminate)). exact Ha0. }
    assert (Ha1_2 : m2 !!! Regidx a1_idx = mword_of_int (Z.of_nat Nb)).
    { rewrite (upd_ne m1 (Regidx s0_idx) (Regidx a1_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (Hm1 a1_idx ltac:(vm_compute; discriminate)). exact Ha1. }
    (* ---- 0xac2  c.mv s7,a0 ---- *)
    iApply (wp_uk_cmv N h12 m2 (mword_of_int 0xac2) s7_idx a0_idx
              (mword_of_int a) nn
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha0_2 moi_add_zero_l; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_ac2 with "Hcode"). }
    assert (Eg12 : add_vec_int (mword_of_int 0xac2 : mword 64) 2
                 = mword_of_int 0xac4) by (apply bv_eq; vm_compute; reflexivity).
    rewrite Eg12. clear Eg12.
    iIntros (h13) "Hrun".
    set (m3 := <[Regidx s7_idx
                 := regval_into_reg (mword_of_int a : mword 64)]> m2).
    assert (Ha1_3 : m3 !!! Regidx a1_idx = mword_of_int (Z.of_nat Nb)).
    { rewrite (upd_ne m2 (Regidx s7_idx) (Regidx a1_idx) _
                 ltac:(vm_compute; discriminate)). exact Ha1_2. }
    (* ---- 0xac4  c.mv s4,a1 ---- *)
    iApply (wp_uk_cmv N h13 m3 (mword_of_int 0xac4) s4_idx a1_idx
              (mword_of_int (Z.of_nat Nb)) nn
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha1_3 moi_add_zero_l; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_ac4 with "Hcode"). }
    assert (Eg13 : add_vec_int (mword_of_int 0xac4 : mword 64) 2
                 = mword_of_int 0xac6) by (apply bv_eq; vm_compute; reflexivity).
    rewrite Eg13. clear Eg13.
    iIntros (h14) "Hrun".
    set (m4 := <[Regidx s4_idx
                 := regval_into_reg (mword_of_int (Z.of_nat Nb)
                                     : mword 64)]> m3).
    assert (Ha0_4 : m4 !!! Regidx a0_idx = mword_of_int a).
    { rewrite (upd_ne m3 (Regidx s4_idx) (Regidx a0_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne m2 (Regidx s7_idx) (Regidx a0_idx) _
                 ltac:(vm_compute; discriminate)). exact Ha0_2. }
    (* ---- 0xac6  c.mv s2,a0 ---- *)
    iApply (wp_uk_cmv N h14 m4 (mword_of_int 0xac6) s2_idx a0_idx
              (mword_of_int a) nn
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha0_4 moi_add_zero_l; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_ac6 with "Hcode"). }
    assert (Eg14 : add_vec_int (mword_of_int 0xac6 : mword 64) 2
                 = mword_of_int 0xac8) by (apply bv_eq; vm_compute; reflexivity).
    rewrite Eg14. clear Eg14.
    iIntros (h15) "Hrun".
    set (m5 := <[Regidx s2_idx
                 := regval_into_reg (mword_of_int a : mword 64)]> m4).
    (* ---- 0xac8  c.li s1,0 ---- *)
    iApply (wp_uk_cli N h15 m5 (mword_of_int 0xac8)
              (mword_of_int 0 : mword 6) s1_idx nn
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) with "[] Hrun").
    { iApply (uis_shk_ac8 with "Hcode"). }
    assert (Eg15 : <[Regidx s1_idx
                   := regval_into_reg (sign_extend' 64 (mword_of_int 0 : mword 6)
                                       : mword 64)]> m5
                 = <[Regidx s1_idx := regval_into_reg
                                        (mword_of_int 0 : mword 64)]> m5) by (f_equal; apply bv_eq; vm_compute; reflexivity).
    rewrite Eg15. clear Eg15.
    assert (Eg16 : add_vec_int (mword_of_int 0xac8 : mword 64) 2
                 = mword_of_int 0xaca) by (apply bv_eq; vm_compute; reflexivity).
    rewrite Eg16. clear Eg16.
    iIntros (h16) "Hrun".
    set (m6 := <[Regidx s1_idx
                 := regval_into_reg (mword_of_int 0 : mword 64)]> m5).
    assert (Hs0_6 : m6 !!! Regidx s0_idx = mword_of_int spz).
    { rewrite Hspm.
      rewrite (upd_ne m5 (Regidx s1_idx) (Regidx s0_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne m4 (Regidx s2_idx) (Regidx s0_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne m3 (Regidx s4_idx) (Regidx s0_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne m2 (Regidx s7_idx) (Regidx s0_idx) _
                 ltac:(vm_compute; discriminate)).
      exact (upd_eq m1 (Regidx s0_idx) (regval_into_reg sp0)). }
    (* ---- 0xaca  addi s6,s0,-81 -- &c, one byte inside the frame ---- *)
    assert (Hoff81 : uoff_i12 (mword_of_int 4015 : mword 12) = -81)
      by (vm_compute; reflexivity).
    iApply (wp_uk_addi N h16 m6 (mword_of_int 0xaca)
              (mword_of_int 4015 : mword 12) s0_idx s6_idx
              (mword_of_int (spz - 81)) nn
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs0_6;
                    exact (umoi_add_i12 (mword_of_int spz)
                             (mword_of_int 4015 : mword 12) (spz - 81)
                             ltac:(rewrite (uint_moi spz ltac:(lia)) Hoff81;
                                   lia)))
              with "[] Hrun").
    { iApply (uis_shk_aca with "Hcode"). }
    assert (Eg17 : add_vec_int (mword_of_int 0xaca : mword 64) 4
                 = mword_of_int 0xace) by (apply bv_eq; vm_compute; reflexivity).
    rewrite Eg17. clear Eg17.
    iIntros (h17) "Hrun".
    set (m7 := <[Regidx s6_idx
                 := regval_into_reg (mword_of_int (spz - 81)
                                     : mword 64)]> m6).
    (* ---- 0xace  c.li s5,1 ---- *)
    iApply (wp_uk_cli N h17 m7 (mword_of_int 0xace)
              (mword_of_int 1 : mword 6) s5_idx nn
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) with "[] Hrun").
    { iApply (uis_shk_ace with "Hcode"). }
    assert (Eg18 : <[Regidx s5_idx
                   := regval_into_reg (sign_extend' 64 (mword_of_int 1 : mword 6)
                                       : mword 64)]> m7
                 = <[Regidx s5_idx := regval_into_reg
                                        (mword_of_int 1 : mword 64)]> m7) by (f_equal; apply bv_eq; vm_compute; reflexivity).
    rewrite Eg18. clear Eg18.
    assert (Eg19 : add_vec_int (mword_of_int 0xace : mword 64) 2
                 = mword_of_int 0xad0) by (apply bv_eq; vm_compute; reflexivity).
    rewrite Eg19. clear Eg19.
    iIntros (h18) "Hrun".
    set (m8 := <[Regidx s5_idx
                 := regval_into_reg (mword_of_int 1 : mword 64)]> m7).
    (* ---- the one byte of the frame the loop actually uses ---- *)
    iDestruct (ush_bytes_upd (spz - 88) 8 7 (nth_byte v11) ltac:(lia)
                 with "Hw11") as "[Hbc Hclc]".
    assert (Eg20 : spz - 88 + Z.of_nat 7 = spz - 81) by lia.
    rewrite Eg20. clear Eg20.
    (* ---- 0xad0..0xafe  the loop ---- *)
    (* THE LINE BEGINS AT A BOUNDARY, which is what the command loop
       carries round its cycle ([ush_posb]) and what makes the byte the
       first read delivers the line's FIRST byte (lane IO-LEAF, M5(3)). *)
    iDestruct (ush_gets_line_of_posb_at Dsc l f with "Hpos") as (I0) "[Hpos Hwc]".
    iApply (wp_ksh_gets_loop a Nb spz l I0 Hfd0 Nb 0%nat [] h18 m8 f
              (nth_byte v11 7) nn
              ltac:(lia) ltac:(lia) ltac:(reflexivity) HNle
              Halo ltac:(unfold Z64; lia) HN31
              ltac:(lia) Hhi
              ltac:(rewrite (upd_ne m7 (Regidx s5_idx) (Regidx s0_idx) _
                               ltac:(vm_compute; discriminate));
                    rewrite (upd_ne m6 (Regidx s6_idx) (Regidx s0_idx) _
                               ltac:(vm_compute; discriminate));
                    exact Hs0_6)
              ltac:(replace (Z.of_nat 0) with 0 by lia;
                    rewrite (upd_ne m7 (Regidx s5_idx) (Regidx s1_idx) _
                               ltac:(vm_compute; discriminate));
                    rewrite (upd_ne m6 (Regidx s6_idx) (Regidx s1_idx) _
                               ltac:(vm_compute; discriminate));
                    exact (upd_eq m5 (Regidx s1_idx)
                             (regval_into_reg (mword_of_int 0 : mword 64))))
              ltac:(replace (a + Z.of_nat 0) with a by lia;
                    rewrite (upd_ne m7 (Regidx s5_idx) (Regidx s2_idx) _
                               ltac:(vm_compute; discriminate));
                    rewrite (upd_ne m6 (Regidx s6_idx) (Regidx s2_idx) _
                               ltac:(vm_compute; discriminate));
                    rewrite (upd_ne m5 (Regidx s1_idx) (Regidx s2_idx) _
                               ltac:(vm_compute; discriminate));
                    exact (upd_eq m4 (Regidx s2_idx)
                             (regval_into_reg (mword_of_int a : mword 64))))
              ltac:(rewrite (upd_ne m7 (Regidx s5_idx) (Regidx s4_idx) _
                               ltac:(vm_compute; discriminate));
                    rewrite (upd_ne m6 (Regidx s6_idx) (Regidx s4_idx) _
                               ltac:(vm_compute; discriminate));
                    rewrite (upd_ne m5 (Regidx s1_idx) (Regidx s4_idx) _
                               ltac:(vm_compute; discriminate));
                    rewrite (upd_ne m4 (Regidx s2_idx) (Regidx s4_idx) _
                               ltac:(vm_compute; discriminate));
                    exact (upd_eq m3 (Regidx s4_idx)
                             (regval_into_reg (mword_of_int (Z.of_nat Nb)
                                               : mword 64))))
              ltac:(exact (upd_eq m7 (Regidx s5_idx)
                             (regval_into_reg (mword_of_int 1 : mword 64))))
              ltac:(rewrite (upd_ne m7 (Regidx s5_idx) (Regidx s6_idx) _
                               ltac:(vm_compute; discriminate));
                    exact (upd_eq m6 (Regidx s6_idx)
                             (regval_into_reg (mword_of_int (spz - 81)
                                               : mword 64))))
              with "Hlaw Hcode Hbs Hbc Hstd Hpos Hwc Hrun").
    iIntros (h19 mc i2 g bc2) "%Hi2 %Hs8c %Hpk Hbs Hbc Hstd Hpos Hrun".
    iDestruct ("Hclc" $! bc2 with "Hbc") as "Hw11".
    (* ---- 0xb00  c.add s8,s8,s7 ---- *)
    assert (Hs7c : mc !!! Regidx s7_idx = mword_of_int a).
    { rewrite (Hpk s7_idx ltac:(vm_compute; reflexivity)).
      rewrite (upd_ne m7 (Regidx s5_idx) (Regidx s7_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne m6 (Regidx s6_idx) (Regidx s7_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne m5 (Regidx s1_idx) (Regidx s7_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne m4 (Regidx s2_idx) (Regidx s7_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne m3 (Regidx s4_idx) (Regidx s7_idx) _
                 ltac:(vm_compute; discriminate)).
      exact (upd_eq m2 (Regidx s7_idx)
               (regval_into_reg (mword_of_int a : mword 64))). }
    assert (Hspc : mc !!! Regidx csp_rs1
                   = add_vec_int sp0 (- (8 * Z.of_nat 12))).
    { rewrite (Hpk csp_rs1 ltac:(vm_compute; reflexivity)).
      rewrite (upd_ne m7 (Regidx s5_idx) (Regidx csp_rs1) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne m6 (Regidx s6_idx) (Regidx csp_rs1) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne m5 (Regidx s1_idx) (Regidx csp_rs1) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne m4 (Regidx s2_idx) (Regidx csp_rs1) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne m3 (Regidx s4_idx) (Regidx csp_rs1) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne m2 (Regidx s7_idx) (Regidx csp_rs1) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne m1 (Regidx s0_idx) (Regidx csp_rs1) _
                 ltac:(vm_compute; discriminate)). exact Hsp1. }
    iApply (wp_uk_cadd N h19 mc (mword_of_int 0xb00) s8_idx s7_idx
              (mword_of_int (a + Z.of_nat i2)) nn
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs8c Hs7c moi_add;
                    replace (a + Z.of_nat i2) with (Z.of_nat i2 + a) by lia;
                    reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_b00 with "Hcode"). }
    assert (Eg21 : add_vec_int (mword_of_int 0xb00 : mword 64) 2
                 = mword_of_int 0xb02) by (apply bv_eq; vm_compute; reflexivity).
    rewrite Eg21. clear Eg21.
    iIntros (h20) "Hrun".
    set (q0 := <[Regidx s8_idx
                 := regval_into_reg (mword_of_int (a + Z.of_nat i2)
                                     : mword 64)]> mc).
    (* ---- 0xb02  sb zero,0(s8) -- THE NUL ---- *)
    iDestruct (urun_x0 with "Hrun") as "[%Hx0 Hrun]".
    assert (Hs8q : q0 !!! Regidx s8_idx = mword_of_int (a + Z.of_nat i2))
      by exact (upd_eq mc (Regidx s8_idx)
                  (regval_into_reg (mword_of_int (a + Z.of_nat i2)
                                    : mword 64))).
    iDestruct (ush_bytes_upd a Nb i2 g ltac:(lia) with "Hbs") as "[Hbi Hcl]".
    iApply (wp_uk_sb N h20 q0 (mword_of_int 0xb02)
              (mword_of_int 0 : mword 12) s8_idx x0_idx
              (a + Z.of_nat i2) (g i2) nn
              ltac:(rewrite Hs8q (uint_moi (a + Z.of_nat i2)
                                    ltac:(unfold Z64 in *; lia));
                    vm_compute uoff_i12; lia)
              with "[] Hbi Hrun").
    { iApply (uis_shk_b02 with "Hcode"). }
    iIntros "Hbi".
    iDestruct ("Hcl" $! (nth_byte (q0 !!! Regidx x0_idx) 0) with "Hbi")
      as "Hbs".
    assert (Hnul : ush_set g i2 (nth_byte (q0 !!! Regidx x0_idx) 0) i2
                   = ubyte0).
    { unfold ush_set. rewrite Nat.eqb_refl.
      assert (Ex0q : q0 !!! Regidx x0_idx = zero_reg)
        by (rewrite (upd_ne mc (Regidx s8_idx) (Regidx x0_idx) _
                       ltac:(vm_compute; discriminate)); exact Hx0).
      rewrite Ex0q. exact ush_nth_byte0_zero. }
    assert (Eb02 : add_vec_int (mword_of_int 0xb02 : mword 64) 4
                   = mword_of_int 0xb06)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Eb02. clear Eb02.
    iIntros (h21) "Hrun".
    (* ---- 0xb06  c.mv a0,s7 ---- *)
    assert (Hs7q : q0 !!! Regidx s7_idx = mword_of_int a).
    { rewrite (upd_ne mc (Regidx s8_idx) (Regidx s7_idx) _
                 ltac:(vm_compute; discriminate)). exact Hs7c. }
    iApply (wp_uk_cmv N h21 q0 (mword_of_int 0xb06) a0_idx s7_idx
              (mword_of_int a) nn
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs7q moi_add_zero_l; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_b06 with "Hcode"). }
    assert (Eg23 : add_vec_int (mword_of_int 0xb06 : mword 64) 2
                 = mword_of_int 0xb08) by (apply bv_eq; vm_compute; reflexivity).
    rewrite Eg23. clear Eg23.
    iIntros (h22) "Hrun".
    set (q1 := <[Regidx a0_idx
                 := regval_into_reg (mword_of_int a : mword 64)]> q0).
    assert (Hspq1 : q1 !!! Regidx csp_rs1
                    = add_vec_int sp0 (- (8 * Z.of_nat 12))).
    { rewrite (upd_ne q0 (Regidx a0_idx) (Regidx csp_rs1) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne mc (Regidx s8_idx) (Regidx csp_rs1) _
                 ltac:(vm_compute; discriminate)). exact Hspc. }
    (* ---- 0xb08  c.ldsp ra ---- *)
    iApply (wp_uk_cldsp N h22 q1 (mword_of_int 0xb08)
              (mword_of_int 11 : mword 6) ra_idx (spz - 8)
              (m !!! Regidx ra_idx) nn
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(rewrite Hspq1 Hsp96 Ho11; lia)
              ltac:(unfold spz; rewrite Zminus_mod Hal8; reflexivity)
              ltac:(vm_compute; discriminate)
              with "[] Hw1 Hrun").
    { iApply (uis_shk_b08 with "Hcode"). }
    iIntros "Hw1".
    assert (Eg24 : add_vec_int (mword_of_int 0xb08 : mword 64) 2
                 = mword_of_int 0xb0a) by (apply bv_eq; vm_compute; reflexivity).
    rewrite Eg24. clear Eg24.
    iIntros (h23) "Hrun".
    set (r1 := <[Regidx ra_idx
                 := regval_into_reg (m !!! Regidx ra_idx)]> q1).
    assert (Hspr1 : r1 !!! Regidx csp_rs1
                   = add_vec_int sp0 (- (8 * Z.of_nat 12))).
    { rewrite (upd_ne q1 (Regidx ra_idx) (Regidx csp_rs1) _
                 ltac:(vm_compute; discriminate)). exact Hspq1. }
    (* ---- 0xb0a  c.ldsp s0 ---- *)
    iApply (wp_uk_cldsp N h23 r1 (mword_of_int 0xb0a)
              (mword_of_int 10 : mword 6) s0_idx (spz - 16)
              (m !!! Regidx s0_idx) nn
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(rewrite Hspr1 Hsp96 Ho10; lia)
              ltac:(unfold spz; rewrite Zminus_mod Hal8; reflexivity)
              ltac:(vm_compute; discriminate)
              with "[] Hw2 Hrun").
    { iApply (uis_shk_b0a with "Hcode"). }
    iIntros "Hw2".
    assert (Eg25 : add_vec_int (mword_of_int 0xb0a : mword 64) 2
                 = mword_of_int 0xb0c) by (apply bv_eq; vm_compute; reflexivity).
    rewrite Eg25. clear Eg25.
    iIntros (h24) "Hrun".
    set (r2 := <[Regidx s0_idx
                 := regval_into_reg (m !!! Regidx s0_idx)]> r1).
    assert (Hspr2 : r2 !!! Regidx csp_rs1
                   = add_vec_int sp0 (- (8 * Z.of_nat 12))).
    { rewrite (upd_ne r1 (Regidx s0_idx) (Regidx csp_rs1) _
                 ltac:(vm_compute; discriminate)). exact Hspr1. }
    (* ---- 0xb0c  c.ldsp s1 ---- *)
    iApply (wp_uk_cldsp N h24 r2 (mword_of_int 0xb0c)
              (mword_of_int 9 : mword 6) s1_idx (spz - 24)
              (m !!! Regidx s1_idx) nn
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(rewrite Hspr2 Hsp96 Ho9; lia)
              ltac:(unfold spz; rewrite Zminus_mod Hal8; reflexivity)
              ltac:(vm_compute; discriminate)
              with "[] Hw3 Hrun").
    { iApply (uis_shk_b0c with "Hcode"). }
    iIntros "Hw3".
    assert (Eg26 : add_vec_int (mword_of_int 0xb0c : mword 64) 2
                 = mword_of_int 0xb0e) by (apply bv_eq; vm_compute; reflexivity).
    rewrite Eg26. clear Eg26.
    iIntros (h25) "Hrun".
    set (r3 := <[Regidx s1_idx
                 := regval_into_reg (m !!! Regidx s1_idx)]> r2).
    assert (Hspr3 : r3 !!! Regidx csp_rs1
                   = add_vec_int sp0 (- (8 * Z.of_nat 12))).
    { rewrite (upd_ne r2 (Regidx s1_idx) (Regidx csp_rs1) _
                 ltac:(vm_compute; discriminate)). exact Hspr2. }
    (* ---- 0xb0e  c.ldsp s2 ---- *)
    iApply (wp_uk_cldsp N h25 r3 (mword_of_int 0xb0e)
              (mword_of_int 8 : mword 6) s2_idx (spz - 32)
              (m !!! Regidx s2_idx) nn
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(rewrite Hspr3 Hsp96 Ho8; lia)
              ltac:(unfold spz; rewrite Zminus_mod Hal8; reflexivity)
              ltac:(vm_compute; discriminate)
              with "[] Hw4 Hrun").
    { iApply (uis_shk_b0e with "Hcode"). }
    iIntros "Hw4".
    assert (Eg27 : add_vec_int (mword_of_int 0xb0e : mword 64) 2
                 = mword_of_int 0xb10) by (apply bv_eq; vm_compute; reflexivity).
    rewrite Eg27. clear Eg27.
    iIntros (h26) "Hrun".
    set (r4 := <[Regidx s2_idx
                 := regval_into_reg (m !!! Regidx s2_idx)]> r3).
    assert (Hspr4 : r4 !!! Regidx csp_rs1
                   = add_vec_int sp0 (- (8 * Z.of_nat 12))).
    { rewrite (upd_ne r3 (Regidx s2_idx) (Regidx csp_rs1) _
                 ltac:(vm_compute; discriminate)). exact Hspr3. }
    (* ---- 0xb10  c.ldsp s3 ---- *)
    iApply (wp_uk_cldsp N h26 r4 (mword_of_int 0xb10)
              (mword_of_int 7 : mword 6) s3_idx (spz - 40)
              (m !!! Regidx s3_idx) nn
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(rewrite Hspr4 Hsp96 Ho7; lia)
              ltac:(unfold spz; rewrite Zminus_mod Hal8; reflexivity)
              ltac:(vm_compute; discriminate)
              with "[] Hw5 Hrun").
    { iApply (uis_shk_b10 with "Hcode"). }
    iIntros "Hw5".
    assert (Eg28 : add_vec_int (mword_of_int 0xb10 : mword 64) 2
                 = mword_of_int 0xb12) by (apply bv_eq; vm_compute; reflexivity).
    rewrite Eg28. clear Eg28.
    iIntros (h27) "Hrun".
    set (r5 := <[Regidx s3_idx
                 := regval_into_reg (m !!! Regidx s3_idx)]> r4).
    assert (Hspr5 : r5 !!! Regidx csp_rs1
                   = add_vec_int sp0 (- (8 * Z.of_nat 12))).
    { rewrite (upd_ne r4 (Regidx s3_idx) (Regidx csp_rs1) _
                 ltac:(vm_compute; discriminate)). exact Hspr4. }
    (* ---- 0xb12  c.ldsp s4 ---- *)
    iApply (wp_uk_cldsp N h27 r5 (mword_of_int 0xb12)
              (mword_of_int 6 : mword 6) s4_idx (spz - 48)
              (m !!! Regidx s4_idx) nn
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(rewrite Hspr5 Hsp96 Ho6; lia)
              ltac:(unfold spz; rewrite Zminus_mod Hal8; reflexivity)
              ltac:(vm_compute; discriminate)
              with "[] Hw6 Hrun").
    { iApply (uis_shk_b12 with "Hcode"). }
    iIntros "Hw6".
    assert (Eg29 : add_vec_int (mword_of_int 0xb12 : mword 64) 2
                 = mword_of_int 0xb14) by (apply bv_eq; vm_compute; reflexivity).
    rewrite Eg29. clear Eg29.
    iIntros (h28) "Hrun".
    set (r6 := <[Regidx s4_idx
                 := regval_into_reg (m !!! Regidx s4_idx)]> r5).
    assert (Hspr6 : r6 !!! Regidx csp_rs1
                   = add_vec_int sp0 (- (8 * Z.of_nat 12))).
    { rewrite (upd_ne r5 (Regidx s4_idx) (Regidx csp_rs1) _
                 ltac:(vm_compute; discriminate)). exact Hspr5. }
    (* ---- 0xb14  c.ldsp s5 ---- *)
    iApply (wp_uk_cldsp N h28 r6 (mword_of_int 0xb14)
              (mword_of_int 5 : mword 6) s5_idx (spz - 56)
              (m !!! Regidx s5_idx) nn
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(rewrite Hspr6 Hsp96 Ho5; lia)
              ltac:(unfold spz; rewrite Zminus_mod Hal8; reflexivity)
              ltac:(vm_compute; discriminate)
              with "[] Hw7 Hrun").
    { iApply (uis_shk_b14 with "Hcode"). }
    iIntros "Hw7".
    assert (Eg30 : add_vec_int (mword_of_int 0xb14 : mword 64) 2
                 = mword_of_int 0xb16) by (apply bv_eq; vm_compute; reflexivity).
    rewrite Eg30. clear Eg30.
    iIntros (h29) "Hrun".
    set (r7 := <[Regidx s5_idx
                 := regval_into_reg (m !!! Regidx s5_idx)]> r6).
    assert (Hspr7 : r7 !!! Regidx csp_rs1
                   = add_vec_int sp0 (- (8 * Z.of_nat 12))).
    { rewrite (upd_ne r6 (Regidx s5_idx) (Regidx csp_rs1) _
                 ltac:(vm_compute; discriminate)). exact Hspr6. }
    (* ---- 0xb16  c.ldsp s6 ---- *)
    iApply (wp_uk_cldsp N h29 r7 (mword_of_int 0xb16)
              (mword_of_int 4 : mword 6) s6_idx (spz - 64)
              (m !!! Regidx s6_idx) nn
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(rewrite Hspr7 Hsp96 Ho4; lia)
              ltac:(unfold spz; rewrite Zminus_mod Hal8; reflexivity)
              ltac:(vm_compute; discriminate)
              with "[] Hw8 Hrun").
    { iApply (uis_shk_b16 with "Hcode"). }
    iIntros "Hw8".
    assert (Eg31 : add_vec_int (mword_of_int 0xb16 : mword 64) 2
                 = mword_of_int 0xb18) by (apply bv_eq; vm_compute; reflexivity).
    rewrite Eg31. clear Eg31.
    iIntros (h30) "Hrun".
    set (r8 := <[Regidx s6_idx
                 := regval_into_reg (m !!! Regidx s6_idx)]> r7).
    assert (Hspr8 : r8 !!! Regidx csp_rs1
                   = add_vec_int sp0 (- (8 * Z.of_nat 12))).
    { rewrite (upd_ne r7 (Regidx s6_idx) (Regidx csp_rs1) _
                 ltac:(vm_compute; discriminate)). exact Hspr7. }
    (* ---- 0xb18  c.ldsp s7 ---- *)
    iApply (wp_uk_cldsp N h30 r8 (mword_of_int 0xb18)
              (mword_of_int 3 : mword 6) s7_idx (spz - 72)
              (m !!! Regidx s7_idx) nn
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(rewrite Hspr8 Hsp96 Ho3; lia)
              ltac:(unfold spz; rewrite Zminus_mod Hal8; reflexivity)
              ltac:(vm_compute; discriminate)
              with "[] Hw9 Hrun").
    { iApply (uis_shk_b18 with "Hcode"). }
    iIntros "Hw9".
    assert (Eg32 : add_vec_int (mword_of_int 0xb18 : mword 64) 2
                 = mword_of_int 0xb1a) by (apply bv_eq; vm_compute; reflexivity).
    rewrite Eg32. clear Eg32.
    iIntros (h31) "Hrun".
    set (r9 := <[Regidx s7_idx
                 := regval_into_reg (m !!! Regidx s7_idx)]> r8).
    assert (Hspr9 : r9 !!! Regidx csp_rs1
                   = add_vec_int sp0 (- (8 * Z.of_nat 12))).
    { rewrite (upd_ne r8 (Regidx s7_idx) (Regidx csp_rs1) _
                 ltac:(vm_compute; discriminate)). exact Hspr8. }
    (* ---- 0xb1a  c.ldsp s8 ---- *)
    iApply (wp_uk_cldsp N h31 r9 (mword_of_int 0xb1a)
              (mword_of_int 2 : mword 6) s8_idx (spz - 80)
              (m !!! Regidx s8_idx) nn
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(rewrite Hspr9 Hsp96 Ho2; lia)
              ltac:(unfold spz; rewrite Zminus_mod Hal8; reflexivity)
              ltac:(vm_compute; discriminate)
              with "[] Hw10 Hrun").
    { iApply (uis_shk_b1a with "Hcode"). }
    iIntros "Hw10".
    assert (Eg33 : add_vec_int (mword_of_int 0xb1a : mword 64) 2
                 = mword_of_int 0xb1c) by (apply bv_eq; vm_compute; reflexivity).
    rewrite Eg33. clear Eg33.
    iIntros (h32) "Hrun".
    set (r10 := <[Regidx s8_idx
                 := regval_into_reg (m !!! Regidx s8_idx)]> r9).
    assert (Hspr10 : r10 !!! Regidx csp_rs1
                   = add_vec_int sp0 (- (8 * Z.of_nat 12))).
    { rewrite (upd_ne r9 (Regidx s8_idx) (Regidx csp_rs1) _
                 ltac:(vm_compute; discriminate)). exact Hspr9. }
    (* ---- 0xb1c  c.addi16sp sp,sp,96 -- THE POP ---- *)
    iApply (wp_uk_caddi16sp_up N h32 r10 (mword_of_int 0xb1c)
              (mword_of_int 6 : mword 6) 12 nn
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "[] [Hw1 Hw2 Hw3 Hw4 Hw5 Hw6 Hw7 Hw8 Hw9 Hw10 Hw11 Hw12] Hrun").
    { iApply (uis_shk_b1c with "Hcode"). }
    { rewrite Hspr10 Hup.
      iApply (ush_stack_12_close sp0 with
                "[] [Hw1] [Hw2] [Hw3] [Hw4] [Hw5] [Hw6] [Hw7] [Hw8] [Hw9]
                 [Hw10] [Hw11] [Hw12]");
        [ iPureIntro; exact Hal8
        | iExists _; iExact "Hw1" | iExists _; iExact "Hw2"
        | iExists _; iExact "Hw3" | iExists _; iExact "Hw4"
        | iExists _; iExact "Hw5" | iExists _; iExact "Hw6"
        | iExists _; iExact "Hw7" | iExists _; iExact "Hw8"
        | iExists _; iExact "Hw9" | iExists _; iExact "Hw10"
        | iApply (uword_of_ubytes γd (spz - 88) _ with "Hw11")
        | iExists _; iExact "Hw12" ]. }
    rewrite Hspr10 Hup.
    assert (Eg34 : add_vec_int (mword_of_int 0xb1c : mword 64) 2
                 = mword_of_int 0xb1e) by (apply bv_eq; vm_compute; reflexivity).
    rewrite Eg34. clear Eg34.
    iIntros (h33) "Hrun".
    set (r11 := <[Regidx csp_rs1 := regval_into_reg sp0]> r10).
    assert (Hrar11 : r11 !!! Regidx ra_idx = m !!! Regidx ra_idx).
    { rewrite (upd_ne r10 (Regidx csp_rs1) (Regidx ra_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne r9 (Regidx s8_idx) (Regidx ra_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne r8 (Regidx s7_idx) (Regidx ra_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne r7 (Regidx s6_idx) (Regidx ra_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne r6 (Regidx s5_idx) (Regidx ra_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne r5 (Regidx s4_idx) (Regidx ra_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne r4 (Regidx s3_idx) (Regidx ra_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne r3 (Regidx s2_idx) (Regidx ra_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne r2 (Regidx s1_idx) (Regidx ra_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne r1 (Regidx s0_idx) (Regidx ra_idx) _
                 ltac:(vm_compute; discriminate)).
      exact (upd_eq q1 (Regidx ra_idx)
               (regval_into_reg (m !!! Regidx ra_idx))). }
    (* ---- 0xb1e  c.jr ra ---- *)
    iApply (wp_uk_cjr N h33 r11 (mword_of_int 0xb1e) ra_idx
              (ret_pc (m !!! Regidx ra_idx)) (12 + nn)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hrar11; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_b1e with "Hcode"). }
    iIntros (h34) "Hrun".
    iApply ("Hcont" with "[Hbs Hstd Hpos] [] Hrun").
    { iExists (ush_set g i2 (nth_byte (q0 !!! Regidx x0_idx) 0)), i2.
      iSplitR; [ iPureIntro; split; [ lia | exact Hnul ] | ].
      iFrame "Hbs Hstd".
      iApply (ush_gets_done_set_at Dl l i2 g (nth_byte (q0 !!! Regidx x0_idx) 0)
                with "Hpos"). }
    iPureIntro. intros r Hr.
    destruct (Z.eq_dec (uint r) 2) as [Eq1 | Eq1].
    { rewrite (ush_ridx_eq r csp_rs1
                 ltac:(rewrite Eq1; vm_compute; reflexivity)).
      rewrite Hsp.
      exact (upd_eq r10 (Regidx csp_rs1) (regval_into_reg sp0)). }
    destruct (Z.eq_dec (uint r) 8) as [Eq2 | Eq2].
    { rewrite (ush_ridx_eq r s0_idx
                 ltac:(rewrite Eq2; vm_compute; reflexivity)).
      rewrite (upd_ne r10 (Regidx csp_rs1) (Regidx s0_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne r9 (Regidx s8_idx) (Regidx s0_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne r8 (Regidx s7_idx) (Regidx s0_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne r7 (Regidx s6_idx) (Regidx s0_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne r6 (Regidx s5_idx) (Regidx s0_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne r5 (Regidx s4_idx) (Regidx s0_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne r4 (Regidx s3_idx) (Regidx s0_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne r3 (Regidx s2_idx) (Regidx s0_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne r2 (Regidx s1_idx) (Regidx s0_idx) _
                 ltac:(vm_compute; discriminate)).
      exact (upd_eq r1 (Regidx s0_idx) (regval_into_reg (m !!! Regidx s0_idx))). }
    destruct (Z.eq_dec (uint r) 9) as [Eq3 | Eq3].
    { rewrite (ush_ridx_eq r s1_idx
                 ltac:(rewrite Eq3; vm_compute; reflexivity)).
      rewrite (upd_ne r10 (Regidx csp_rs1) (Regidx s1_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne r9 (Regidx s8_idx) (Regidx s1_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne r8 (Regidx s7_idx) (Regidx s1_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne r7 (Regidx s6_idx) (Regidx s1_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne r6 (Regidx s5_idx) (Regidx s1_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne r5 (Regidx s4_idx) (Regidx s1_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne r4 (Regidx s3_idx) (Regidx s1_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne r3 (Regidx s2_idx) (Regidx s1_idx) _
                 ltac:(vm_compute; discriminate)).
      exact (upd_eq r2 (Regidx s1_idx) (regval_into_reg (m !!! Regidx s1_idx))). }
    destruct (Z.eq_dec (uint r) 18) as [Eq4 | Eq4].
    { rewrite (ush_ridx_eq r s2_idx
                 ltac:(rewrite Eq4; vm_compute; reflexivity)).
      rewrite (upd_ne r10 (Regidx csp_rs1) (Regidx s2_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne r9 (Regidx s8_idx) (Regidx s2_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne r8 (Regidx s7_idx) (Regidx s2_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne r7 (Regidx s6_idx) (Regidx s2_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne r6 (Regidx s5_idx) (Regidx s2_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne r5 (Regidx s4_idx) (Regidx s2_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne r4 (Regidx s3_idx) (Regidx s2_idx) _
                 ltac:(vm_compute; discriminate)).
      exact (upd_eq r3 (Regidx s2_idx) (regval_into_reg (m !!! Regidx s2_idx))). }
    destruct (Z.eq_dec (uint r) 19) as [Eq5 | Eq5].
    { rewrite (ush_ridx_eq r s3_idx
                 ltac:(rewrite Eq5; vm_compute; reflexivity)).
      rewrite (upd_ne r10 (Regidx csp_rs1) (Regidx s3_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne r9 (Regidx s8_idx) (Regidx s3_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne r8 (Regidx s7_idx) (Regidx s3_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne r7 (Regidx s6_idx) (Regidx s3_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne r6 (Regidx s5_idx) (Regidx s3_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne r5 (Regidx s4_idx) (Regidx s3_idx) _
                 ltac:(vm_compute; discriminate)).
      exact (upd_eq r4 (Regidx s3_idx) (regval_into_reg (m !!! Regidx s3_idx))). }
    destruct (Z.eq_dec (uint r) 20) as [Eq6 | Eq6].
    { rewrite (ush_ridx_eq r s4_idx
                 ltac:(rewrite Eq6; vm_compute; reflexivity)).
      rewrite (upd_ne r10 (Regidx csp_rs1) (Regidx s4_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne r9 (Regidx s8_idx) (Regidx s4_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne r8 (Regidx s7_idx) (Regidx s4_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne r7 (Regidx s6_idx) (Regidx s4_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne r6 (Regidx s5_idx) (Regidx s4_idx) _
                 ltac:(vm_compute; discriminate)).
      exact (upd_eq r5 (Regidx s4_idx) (regval_into_reg (m !!! Regidx s4_idx))). }
    destruct (Z.eq_dec (uint r) 21) as [Eq7 | Eq7].
    { rewrite (ush_ridx_eq r s5_idx
                 ltac:(rewrite Eq7; vm_compute; reflexivity)).
      rewrite (upd_ne r10 (Regidx csp_rs1) (Regidx s5_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne r9 (Regidx s8_idx) (Regidx s5_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne r8 (Regidx s7_idx) (Regidx s5_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne r7 (Regidx s6_idx) (Regidx s5_idx) _
                 ltac:(vm_compute; discriminate)).
      exact (upd_eq r6 (Regidx s5_idx) (regval_into_reg (m !!! Regidx s5_idx))). }
    destruct (Z.eq_dec (uint r) 22) as [Eq8 | Eq8].
    { rewrite (ush_ridx_eq r s6_idx
                 ltac:(rewrite Eq8; vm_compute; reflexivity)).
      rewrite (upd_ne r10 (Regidx csp_rs1) (Regidx s6_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne r9 (Regidx s8_idx) (Regidx s6_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne r8 (Regidx s7_idx) (Regidx s6_idx) _
                 ltac:(vm_compute; discriminate)).
      exact (upd_eq r7 (Regidx s6_idx) (regval_into_reg (m !!! Regidx s6_idx))). }
    destruct (Z.eq_dec (uint r) 23) as [Eq9 | Eq9].
    { rewrite (ush_ridx_eq r s7_idx
                 ltac:(rewrite Eq9; vm_compute; reflexivity)).
      rewrite (upd_ne r10 (Regidx csp_rs1) (Regidx s7_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne r9 (Regidx s8_idx) (Regidx s7_idx) _
                 ltac:(vm_compute; discriminate)).
      exact (upd_eq r8 (Regidx s7_idx) (regval_into_reg (m !!! Regidx s7_idx))). }
    destruct (Z.eq_dec (uint r) 24) as [Eq10 | Eq10].
    { rewrite (ush_ridx_eq r s8_idx
                 ltac:(rewrite Eq10; vm_compute; reflexivity)).
      rewrite (upd_ne r10 (Regidx csp_rs1) (Regidx s8_idx) _
                 ltac:(vm_compute; discriminate)).
      exact (upd_eq r9 (Regidx s8_idx) (regval_into_reg (m !!! Regidx s8_idx))). }
    assert (Hu : uint r = 3 \/ uint r = 4 \/ uint r = 25 \/
                 uint r = 26 \/ uint r = 27).
    { pose proof (ucs_cases r Hr) as Hc. lia. }
    assert (Hkeep : ush_gets_keep r = true).
    { unfold ush_gets_keep.
      destruct Hu as [E|[E|[E|[E|E]]]]; rewrite E; vm_compute; reflexivity. }
    rewrite (upd_ne r10 (Regidx csp_rs1) (Regidx r) _
               (ush_r_ne r 2 csp_rs1 ltac:(vm_compute; reflexivity)
                  ltac:(lia))).
    rewrite (upd_ne r9 (Regidx s8_idx) (Regidx r) _
               (ush_r_ne r 24 s8_idx ltac:(vm_compute; reflexivity)
                  ltac:(lia))).
    rewrite (upd_ne r8 (Regidx s7_idx) (Regidx r) _
               (ush_r_ne r 23 s7_idx ltac:(vm_compute; reflexivity)
                  ltac:(lia))).
    rewrite (upd_ne r7 (Regidx s6_idx) (Regidx r) _
               (ush_r_ne r 22 s6_idx ltac:(vm_compute; reflexivity)
                  ltac:(lia))).
    rewrite (upd_ne r6 (Regidx s5_idx) (Regidx r) _
               (ush_r_ne r 21 s5_idx ltac:(vm_compute; reflexivity)
                  ltac:(lia))).
    rewrite (upd_ne r5 (Regidx s4_idx) (Regidx r) _
               (ush_r_ne r 20 s4_idx ltac:(vm_compute; reflexivity)
                  ltac:(lia))).
    rewrite (upd_ne r4 (Regidx s3_idx) (Regidx r) _
               (ush_r_ne r 19 s3_idx ltac:(vm_compute; reflexivity)
                  ltac:(lia))).
    rewrite (upd_ne r3 (Regidx s2_idx) (Regidx r) _
               (ush_r_ne r 18 s2_idx ltac:(vm_compute; reflexivity)
                  ltac:(lia))).
    rewrite (upd_ne r2 (Regidx s1_idx) (Regidx r) _
               (ush_r_ne r 9 s1_idx ltac:(vm_compute; reflexivity)
                  ltac:(lia))).
    rewrite (upd_ne r1 (Regidx s0_idx) (Regidx r) _
               (ush_r_ne r 8 s0_idx ltac:(vm_compute; reflexivity)
                  ltac:(lia))).
    rewrite (upd_ne q1 (Regidx ra_idx) (Regidx r) _
               (ush_r_ne r 1 ra_idx ltac:(vm_compute; reflexivity)
                  ltac:(lia))).
    rewrite (upd_ne q0 (Regidx a0_idx) (Regidx r) _
               (ush_r_ne r 10 a0_idx ltac:(vm_compute; reflexivity)
                  ltac:(lia))).
    rewrite (upd_ne mc (Regidx s8_idx) (Regidx r) _
               (ush_r_ne r 24 s8_idx ltac:(vm_compute; reflexivity)
                  ltac:(lia))).
    rewrite (Hpk r Hkeep).
    rewrite (upd_ne m7 (Regidx s5_idx) (Regidx r) _
               (ush_r_ne r 21 s5_idx ltac:(vm_compute; reflexivity)
                  ltac:(lia))).
    rewrite (upd_ne m6 (Regidx s6_idx) (Regidx r) _
               (ush_r_ne r 22 s6_idx ltac:(vm_compute; reflexivity)
                  ltac:(lia))).
    rewrite (upd_ne m5 (Regidx s1_idx) (Regidx r) _
               (ush_r_ne r 9 s1_idx ltac:(vm_compute; reflexivity)
                  ltac:(lia))).
    rewrite (upd_ne m4 (Regidx s2_idx) (Regidx r) _
               (ush_r_ne r 18 s2_idx ltac:(vm_compute; reflexivity)
                  ltac:(lia))).
    rewrite (upd_ne m3 (Regidx s4_idx) (Regidx r) _
               (ush_r_ne r 20 s4_idx ltac:(vm_compute; reflexivity)
                  ltac:(lia))).
    rewrite (upd_ne m2 (Regidx s7_idx) (Regidx r) _
               (ush_r_ne r 23 s7_idx ltac:(vm_compute; reflexivity)
                  ltac:(lia))).
    rewrite (upd_ne m1 (Regidx s0_idx) (Regidx r) _
               (ush_r_ne r 8 s0_idx ltac:(vm_compute; reflexivity)
                  ltac:(lia))).
    rewrite (upd_ne m (Regidx csp_rs1) (Regidx r) _
               (ush_r_ne r 2 csp_rs1 ltac:(vm_compute; reflexivity)
                  ltac:(lia))).
    reflexivity.
  Qed.


  (* ===================================================================== *)
  (* getcmd @0x0 -- 29 instructions, a 32-byte frame, three calls.          *)
  (* DEPENDS ON [ush_read_leaf] (through [wp_ksh_gets]).                    *)
  (*                                                                       *)
  (*   write(2, "$ ", 2);  memset(buf, 0, nbuf);  gets(buf, nbuf);          *)
  (*   return buf[0] == 0 ? -1 : 0;                                         *)
  (*                                                                       *)
  (* The stack budget is the call chain spelled out: getcmd's own four      *)
  (* words on top of gets' twelve, which is the deepest callee.  memset     *)
  (* borrows two of the same twelve and write borrows none.                 *)
  (*                                                                       *)
  (* THE RETURN VALUE IS NOT COMPUTED.  [seqz]/[negw] turn [buf[0]] into    *)
  (* 0 or -1 and main branches on it at 0x940, but the walk never needs to  *)
  (* know which: both arms of that branch are proved, so the two            *)
  (* instructions go through with their values left as they are.            *)
  (* ===================================================================== *)
  (* THE WRITE DEPOSIT UNDER THE TAINT (lane EXEC-SEAM, (D)): the only
     turn that prints on the free law is a tainted one, and the law is
     owed there and nowhere else. *)
  Lemma wp_ksh_getcmd (h : CpuId) (m : regfile) (a : Z) (Nb : nat)
      (f : nat -> bv 8) (l : list fdstate) (nn : nat) :
    m !!! Regidx a0_idx = mword_of_int a ->
    m !!! Regidx a1_idx = mword_of_int (Z.of_nat Nb) ->
    Nb = sh_nbuf -> Z.of_nat Nb < Z31 ->
    ush_fd0p l ->
    □ (T -∗ sh_deps) -∗
    ush_tag_law -∗
    (* ...and the prompt's law at every line boundary (lane IO-LEAF,
       M6a(3)) *)
    ush_prompt_law -∗
    shk_code γt -∗
    ubytes γd a Nb f -∗
    ush_std l -∗
    (* THE LOOP'S CURSOR AND CREDENTIAL, at the boundary the cursor stands
       on (lane IO-LEAF, M6a(3)); the read moves both to the next one *)
    ush_posb l 0%nat -∗
    urun N h m (mword_of_int ShSyms.getcmd) (4 + (12 + nn)) -∗
    (* ONE ∀ AND NOT AN ∃ UNDER A ∀ (lane IO-LEAF, M5(3)): the return
       value is a fact ABOUT THE LINE, so the line and the registers have
       to be bound together. *)
    (∀ (h' : CpuId) (m' : regfile) (g : nat -> bv 8) (i2 : nat),
       ⌜ (i2 < Nb)%nat /\ g i2 = ubyte0 ⌝ -∗
       ⌜ ucallee_saved m m' ⌝ -∗
       (* ...AND THE RETURN VALUE AT THE ONE INPUT IT HAS: getcmd answers
          -1 exactly when the line is empty, which is what keeps the
          command loop's body off the arm where there is no line to
          lex. *)
       (* ...TOTALLY (lane EXEC-SEAM, (C)): [seqz]/[negw] of the first
          byte is -1 on a NUL and 0 on anything else, which is what lets
          the command loop's exit say that a line it read was not the turn
          it left on. *)
       ⌜ (g 0%nat = ubyte0 ->
          m' !!! Regidx a0_idx = (mword_of_int (-1) : mword 64))
         /\ (g 0%nat <> ubyte0 ->
             m' !!! Regidx a0_idx = (mword_of_int 0 : mword 64)) ⌝ -∗
       ubytes γd a Nb g -∗
       ush_std l -∗
       ush_gets_done_at Dl l i2 g -∗
       urun N h' m' (ret_pc (m !!! Regidx ra_idx)) (4 + (12 + nn)) -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using Hdsc_ncr Hdsc_line Hdsc_short HT ush_at_of_pm_taint ush_at_of_pm_wb ush_read_leaf ush_wb_read ush_wc_read.
    intros Ha0 Ha1 HNle HN31 Hfd0.
    assert (HN0 : (0 < Nb)%nat) by (rewrite HNle; unfold sh_nbuf; lia).
    iIntros "#Hdp #Hlaw #Hplaw #Hcode Hbs Hstd Hpos Hrun Hcont".
    (* THE ONE BRANCH: which of the payments answers the prompt is decided
       here, once, and the walk below spends the obligation every arm
       produces ([ksh_w_of_wcp]); what the call hands back beside the
       ledger is the boundary at the prompt's end, which is what [gets] is
       entered with. *)
    iAssert (ksh_w (mword_of_int 2) (mword_of_int sh_prompt_pv) 2%nat
               (ush_std l) (ush_std l ∗ ush_posb l 2%nat))%I
      with "[Hpos]" as "Hw".
    { rewrite /ush_posb. iDestruct "Hpos" as "[Hb | [#HT Hp]]"; last first.
      { iApply (ksh_w_mono _ _ _ (ush_std l) (ush_std l) with "[Hp] []").
        - iIntros "$". iRight. iFrame "HT Hp".
        - iDestruct ("Hdp" with "HT") as "#Hdp16".
          iApply (ksh_w_of_law (mword_of_int 2) (mword_of_int sh_prompt_pv)
                    2%nat (ush_std l) (ush_std l) ltac:(reflexivity)
                    with "Hdp16"). }
      iDestruct "Hb" as (I) "(%Hbnd & Hpm & Hwc)".
      iApply (ksh_w_mono _ _ _ (ush_std l) (ush_std l ∗ ush_wcp l I 2%nat)
                with "[Hpm] [Hwc]").
      - iIntros "[$ Hwc]". iLeft. iExists I. iFrame "Hpm Hwc". by iPureIntro.
      - iApply (ksh_w_of_wcp l I with "Hplaw Hwc"). }
    rewrite shp_getcmd.
    iDestruct (urun_stack with "Hrun") as %[Hal8 Hroom].
    iDestruct (urun_ubytes_bnd h m _ (4 + (12 + nn)) (DfracOwn 1) a Nb f
                 ltac:(lia) with "Hrun Hbs") as %[Halo Hahi].
    change (2 ^ 38) with 274877906944 in Hahi.
    remember (m !!! Regidx csp_rs1) as sp0 eqn:Hsp0.
    assert (Hsp : m !!! Regidx csp_rs1 = sp0) by (symmetry; exact Hsp0).
    clear Hsp0.
    assert (Hlo : 32 <= uint sp0) by lia.
    assert (Hbsp : bv_unsigned (add_vec_int sp0 (- (8 * Z.of_nat 4)))
                   = bv_unsigned sp0 - 32).
    { replace (- (8 * Z.of_nat 4)) with (-32) by lia.
      exact (uv_avi_neg sp0 32 ltac:(lia) ltac:(rewrite <- uint_unsigned; lia)). }
    assert (Hsp32 : uint (add_vec_int sp0 (- (8 * Z.of_nat 4)))
                    = uint sp0 - 32)
      by (rewrite !uint_unsigned; exact Hbsp).
    assert (Go0 : uoff_sdsp (mword_of_int 0 : mword 6) = 0)
      by (vm_compute; reflexivity).
    assert (Go1 : uoff_sdsp (mword_of_int 1 : mword 6) = 8)
      by (vm_compute; reflexivity).
    assert (Go2 : uoff_sdsp (mword_of_int 2 : mword 6) = 16)
      by (vm_compute; reflexivity).
    assert (Go3 : uoff_sdsp (mword_of_int 3 : mword 6) = 24)
      by (vm_compute; reflexivity).
    (* ---- 0x0  c.addi sp,sp,-32 -- THE PUSH ---- *)
    iApply (wp_uk_caddi_sp_dn N h m (mword_of_int 0x0)
              (mword_of_int 32 : mword 6) 4 (12 + nn)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_00 with "Hcode"). }
    assert (E00 : add_vec_int (mword_of_int 0x0 : mword 64) 2
                  = mword_of_int 0x2)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Hsp ustack_4 E00.
    iIntros "(_ & [%v1 Hw1] & [%v2 Hw2] & [%v3 Hw3] & [%v4 Hw4])".
    iIntros (h1) "Hrun".
    set (n1 := <[Regidx csp_rs1
                 := regval_into_reg (add_vec_int sp0 (- (8 * Z.of_nat 4)))]> m).
    assert (Hsp1 : n1 !!! Regidx csp_rs1 = add_vec_int sp0 (- (8 * Z.of_nat 4)))
      by exact (upd_eq m (Regidx csp_rs1)
                  (regval_into_reg (add_vec_int sp0 (- (8 * Z.of_nat 4))))).
    assert (Hn1 : forall r : mword 5, Regidx r <> Regidx csp_rs1 ->
                    n1 !!! Regidx r = m !!! Regidx r)
      by (intros r Hr; exact (upd_ne m (Regidx csp_rs1) (Regidx r) _ Hr)).
    (* ---- 0x2..0x8  the four spills ---- *)
    iApply (wp_uk_csdsp N h1 n1 (mword_of_int 0x2)
              (mword_of_int 3 : mword 6) ra_idx (uint sp0 - 8) v1 (12 + nn)
              ltac:(rewrite Hsp1 Hsp32 Go3; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              with "[] Hw1 Hrun").
    { iApply (uis_shk_02 with "Hcode"). }
    iIntros "Hw1". rewrite (Hn1 ra_idx ltac:(vm_compute; discriminate)).
    assert (E02 : add_vec_int (mword_of_int 0x2 : mword 64) 2
                  = mword_of_int 0x4)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E02. iIntros (h2) "Hrun".
    iApply (wp_uk_csdsp N h2 n1 (mword_of_int 0x4)
              (mword_of_int 2 : mword 6) s0_idx (uint sp0 - 16) v2 (12 + nn)
              ltac:(rewrite Hsp1 Hsp32 Go2; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              with "[] Hw2 Hrun").
    { iApply (uis_shk_04 with "Hcode"). }
    iIntros "Hw2". rewrite (Hn1 s0_idx ltac:(vm_compute; discriminate)).
    assert (E04 : add_vec_int (mword_of_int 0x4 : mword 64) 2
                  = mword_of_int 0x6)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E04. iIntros (h3) "Hrun".
    iApply (wp_uk_csdsp N h3 n1 (mword_of_int 0x6)
              (mword_of_int 1 : mword 6) s1_idx (uint sp0 - 24) v3 (12 + nn)
              ltac:(rewrite Hsp1 Hsp32 Go1; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              with "[] Hw3 Hrun").
    { iApply (uis_shk_06 with "Hcode"). }
    iIntros "Hw3". rewrite (Hn1 s1_idx ltac:(vm_compute; discriminate)).
    assert (E06 : add_vec_int (mword_of_int 0x6 : mword 64) 2
                  = mword_of_int 0x8)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E06. iIntros (h4) "Hrun".
    iApply (wp_uk_csdsp N h4 n1 (mword_of_int 0x8)
              (mword_of_int 0 : mword 6) s2_idx (uint sp0 - 32) v4 (12 + nn)
              ltac:(rewrite Hsp1 Hsp32 Go0; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              with "[] Hw4 Hrun").
    { iApply (uis_shk_08 with "Hcode"). }
    iIntros "Hw4". rewrite (Hn1 s2_idx ltac:(vm_compute; discriminate)).
    assert (E08 : add_vec_int (mword_of_int 0x8 : mword 64) 2
                  = mword_of_int 0xa)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E08. iIntros (h5) "Hrun".
    (* ---- 0xa  c.addi4spn s0,sp,32 (s0 is dead until the epilogue) ---- *)
    iApply (wp_uk_caddi4spn N h5 n1 (mword_of_int 0xa)
              (mword_of_int 0 : mword 3) (mword_of_int 8 : mword 8) s0_idx
              (add_vec (n1 !!! Regidx csp_rs1)
                 (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8))))
              (12 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
              eq_refl
              with "[] Hrun").
    { iApply (uis_shk_0a with "Hcode"). }
    assert (E0a : add_vec_int (mword_of_int 0xa : mword 64) 2
                  = mword_of_int 0xc)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E0a. iIntros (h6) "Hrun".
    set (n2 := <[Regidx s0_idx
                 := regval_into_reg
                      (add_vec (n1 !!! Regidx csp_rs1)
                         (sign_extend' 64
                            (caddi4spn_imm (mword_of_int 8 : mword 8))))]> n1).
    assert (Hn2 : forall r : mword 5, Regidx r <> Regidx s0_idx ->
                    n2 !!! Regidx r = n1 !!! Regidx r)
      by (intros r Hr; exact (upd_ne n1 (Regidx s0_idx) (Regidx r) _ Hr)).
    assert (Ha0_2 : n2 !!! Regidx a0_idx = mword_of_int a).
    { rewrite (Hn2 a0_idx ltac:(vm_compute; discriminate)).
      rewrite (Hn1 a0_idx ltac:(vm_compute; discriminate)). exact Ha0. }
    (* ---- 0xc  c.mv s1,a0 ---- *)
    iApply (wp_uk_cmv N h6 n2 (mword_of_int 0xc) s1_idx a0_idx
              (mword_of_int a) (12 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha0_2 moi_add_zero_l; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_0c with "Hcode"). }
    assert (E0c : add_vec_int (mword_of_int 0xc : mword 64) 2
                  = mword_of_int 0xe)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E0c. iIntros (h7) "Hrun".
    set (n3 := <[Regidx s1_idx
                 := regval_into_reg (mword_of_int a : mword 64)]> n2).
    assert (Hn3 : forall r : mword 5, Regidx r <> Regidx s1_idx ->
                    n3 !!! Regidx r = n2 !!! Regidx r)
      by (intros r Hr; exact (upd_ne n2 (Regidx s1_idx) (Regidx r) _ Hr)).
    assert (Ha1_3 : n3 !!! Regidx a1_idx = mword_of_int (Z.of_nat Nb)).
    { rewrite (Hn3 a1_idx ltac:(vm_compute; discriminate)).
      rewrite (Hn2 a1_idx ltac:(vm_compute; discriminate)).
      rewrite (Hn1 a1_idx ltac:(vm_compute; discriminate)). exact Ha1. }
    (* ---- 0xe  c.mv s2,a1 ---- *)
    iApply (wp_uk_cmv N h7 n3 (mword_of_int 0xe) s2_idx a1_idx
              (mword_of_int (Z.of_nat Nb)) (12 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha1_3 moi_add_zero_l; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_0e with "Hcode"). }
    assert (E0e : add_vec_int (mword_of_int 0xe : mword 64) 2
                  = mword_of_int 0x10)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E0e. iIntros (h8) "Hrun".
    set (n4 := <[Regidx s2_idx
                 := regval_into_reg (mword_of_int (Z.of_nat Nb)
                                     : mword 64)]> n3).
    assert (Hn4 : forall r : mword 5, Regidx r <> Regidx s2_idx ->
                    n4 !!! Regidx r = n3 !!! Regidx r)
      by (intros r Hr; exact (upd_ne n3 (Regidx s2_idx) (Regidx r) _ Hr)).
    assert (Hs1_4 : n4 !!! Regidx s1_idx = mword_of_int a).
    { rewrite (Hn4 s1_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq n2 (Regidx s1_idx)
               (regval_into_reg (mword_of_int a : mword 64))). }
    assert (Hs2_4 : n4 !!! Regidx s2_idx = mword_of_int (Z.of_nat Nb))
      by exact (upd_eq n3 (Regidx s2_idx)
                  (regval_into_reg (mword_of_int (Z.of_nat Nb) : mword 64))).
    (* ---- 0x10..0x1c  the prompt: write(2, "$ ", 2) ---- *)
    iApply (wp_uk_cli N h8 n4 (mword_of_int 0x10)
              (mword_of_int 2 : mword 6) a2_idx (12 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) with "[] Hrun").
    { iApply (uis_shk_10 with "Hcode"). }
    assert (Em10 : <[Regidx a2_idx
                     := regval_into_reg (sign_extend' 64
                                           (mword_of_int 2 : mword 6)
                                         : mword 64)]> n4
                   = <[Regidx a2_idx
                       := regval_into_reg (mword_of_int 2 : mword 64)]> n4)
      by (f_equal; apply bv_eq; vm_compute; reflexivity).
    assert (E10 : add_vec_int (mword_of_int 0x10 : mword 64) 2
                  = mword_of_int 0x12)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Em10 E10. iIntros (h9) "Hrun".
    set (n5 := <[Regidx a2_idx
                 := regval_into_reg (mword_of_int 2 : mword 64)]> n4).
    assert (Hn5 : forall r : mword 5, Regidx r <> Regidx a2_idx ->
                    n5 !!! Regidx r = n4 !!! Regidx r)
      by (intros r Hr; exact (upd_ne n4 (Regidx a2_idx) (Regidx r) _ Hr)).
    iApply (wp_uk_auipc N h9 n5 (mword_of_int 0x12)
              (mword_of_int 1 : mword 20) a1_idx
              (add_vec (mword_of_int 0x12 : mword 64)
                 (auipc_off (mword_of_int 1 : mword 20))) (12 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) eq_refl
              with "[] Hrun").
    { iApply (uis_shk_12 with "Hcode"). }
    assert (E12 : add_vec_int (mword_of_int 0x12 : mword 64) 4
                  = mword_of_int 0x16)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E12. iIntros (h10) "Hrun".
    set (n6 := <[Regidx a1_idx
                 := regval_into_reg
                      (add_vec (mword_of_int 0x12 : mword 64)
                         (auipc_off (mword_of_int 1 : mword 20)))]> n5).
    assert (Hn6 : forall r : mword 5, Regidx r <> Regidx a1_idx ->
                    n6 !!! Regidx r = n5 !!! Regidx r)
      by (intros r Hr; exact (upd_ne n5 (Regidx a1_idx) (Regidx r) _ Hr)).
    iApply (wp_uk_addi N h10 n6 (mword_of_int 0x16)
              (mword_of_int 638 : mword 12) a1_idx a1_idx
              (add_vec (n6 !!! Regidx a1_idx)
                 (sign_extend' 64 (mword_of_int 638 : mword 12))) (12 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) eq_refl
              with "[] Hrun").
    { iApply (uis_shk_16 with "Hcode"). }
    assert (E16 : add_vec_int (mword_of_int 0x16 : mword 64) 4
                  = mword_of_int 0x1a)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E16. iIntros (h11) "Hrun".
    set (n7 := <[Regidx a1_idx
                 := regval_into_reg
                      (add_vec (n6 !!! Regidx a1_idx)
                         (sign_extend' 64
                            (mword_of_int 638 : mword 12)))]> n6).
    assert (Hn7 : forall r : mword 5, Regidx r <> Regidx a1_idx ->
                    n7 !!! Regidx r = n6 !!! Regidx r)
      by (intros r Hr; exact (upd_ne n6 (Regidx a1_idx) (Regidx r) _ Hr)).
    iApply (wp_uk_cmv N h11 n7 (mword_of_int 0x1a) a0_idx a2_idx
              (add_vec zero_reg (n7 !!! Regidx a2_idx)) (12 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) eq_refl
              with "[] Hrun").
    { iApply (uis_shk_1a with "Hcode"). }
    assert (E1a : add_vec_int (mword_of_int 0x1a : mword 64) 2
                  = mword_of_int 0x1c)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E1a. iIntros (h12) "Hrun".
    set (n8 := <[Regidx a0_idx
                 := regval_into_reg
                      (add_vec zero_reg (n7 !!! Regidx a2_idx))]> n7).
    assert (Hn8 : forall r : mword 5, Regidx r <> Regidx a0_idx ->
                    n8 !!! Regidx r = n7 !!! Regidx r)
      by (intros r Hr; exact (upd_ne n7 (Regidx a0_idx) (Regidx r) _ Hr)).
    (* ---- 0x1c  jal ra,0xca6 <write> ---- *)
    iApply (wp_uk_jal N h12 n8 (mword_of_int 0x1c)
              (mword_of_int 3210 : mword 21) ra_idx
              (mword_of_int ShSyms.write) (mword_of_int 0x20) (12 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite shp_write; apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(rewrite shp_write; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_1c with "Hcode"). }
    iIntros (h13) "Hrun".
    set (n9 := <[Regidx ra_idx
                 := regval_into_reg (mword_of_int 0x20 : mword 64)]> n8).
    assert (Hn9 : forall r : mword 5, Regidx r <> Regidx ra_idx ->
                    n9 !!! Regidx r = n8 !!! Regidx r)
      by (intros r Hr; exact (upd_ne n8 (Regidx ra_idx) (Regidx r) _ Hr)).
    assert (Hra9 : n9 !!! Regidx ra_idx = mword_of_int 0x20)
      by exact (upd_eq n8 (Regidx ra_idx)
                  (regval_into_reg (mword_of_int 0x20 : mword 64))).
    (* ---- THE PROMPT'S THREE ARGUMENTS, as the payment asks for them:
           fd 2, sh's own .rodata literal, two bytes.  a2 was set at 0x10
           and survives; a1 is the auipc/addi pair at 0x12/0x16; a0 is
           a2's copy at 0x1a. ---- *)
    assert (Ha2_7 : n7 !!! Regidx a2_idx = (mword_of_int 2 : mword 64)).
    { rewrite (Hn7 a2_idx ltac:(vm_compute; discriminate)).
      rewrite (Hn6 a2_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq n4 (Regidx a2_idx)
               (regval_into_reg (mword_of_int 2 : mword 64))). }
    assert (Ha1_6 : n6 !!! Regidx a1_idx
                    = add_vec (mword_of_int 0x12 : mword 64)
                        (auipc_off (mword_of_int 1 : mword 20)))
      by exact (upd_eq n5 (Regidx a1_idx)
                  (regval_into_reg
                     (add_vec (mword_of_int 0x12 : mword 64)
                        (auipc_off (mword_of_int 1 : mword 20))))).
    assert (Ha2_9 : n9 !!! Regidx a2_idx
                    = (mword_of_int (Z.of_nat 2%nat) : mword 64)).
    { rewrite (Hn9 a2_idx ltac:(vm_compute; discriminate)).
      rewrite (Hn8 a2_idx ltac:(vm_compute; discriminate)).
      exact Ha2_7. }
    assert (Ha0_9 : n9 !!! Regidx a0_idx = (mword_of_int 2 : mword 64)).
    { rewrite (Hn9 a0_idx ltac:(vm_compute; discriminate)).
      etransitivity;
        [ exact (upd_eq n7 (Regidx a0_idx)
                   (regval_into_reg
                      (add_vec zero_reg (n7 !!! Regidx a2_idx)))) | ].
      rewrite Ha2_7. exact (moi_add_zero_l 2). }
    assert (Ha1_9 : n9 !!! Regidx a1_idx
                    = (mword_of_int sh_prompt_pv : mword 64)).
    { rewrite (Hn9 a1_idx ltac:(vm_compute; discriminate)).
      rewrite (Hn8 a1_idx ltac:(vm_compute; discriminate)).
      etransitivity;
        [ exact (upd_eq n6 (Regidx a1_idx)
                   (regval_into_reg
                      (add_vec (n6 !!! Regidx a1_idx)
                         (sign_extend' 64 (mword_of_int 638 : mword 12))))) | ].
      rewrite Ha1_6. apply bv_eq; vm_compute; reflexivity. }
    iApply ("Hw" $! h13 n9 (12 + nn)%nat with "[%] [%] [%] Hcode Hstd Hrun").
    { exact Ha0_9. }
    { exact Ha1_9. }
    { exact Ha2_9. }
    iIntros (h14 rw) "[Hstd Hpos] Hrun". rewrite Hra9.
    assert (Er20 : ret_pc (mword_of_int 0x20 : mword 64) = mword_of_int 0x20)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Er20.
    set (nA := <[Regidx a0_idx := rw]>
                 (<[Regidx a7_idx := (mword_of_int 16 : mword 64)]> n9)).
    assert (HnA : forall r : mword 5, Regidx r <> Regidx a0_idx ->
                    Regidx r <> Regidx a7_idx ->
                    nA !!! Regidx r = n9 !!! Regidx r).
    { intros r Hr0 Hr7.
      rewrite (upd_ne _ (Regidx a0_idx) (Regidx r) _ Hr0).
      exact (upd_ne n9 (Regidx a7_idx) (Regidx r) _ Hr7). }
    assert (Hs1_A : nA !!! Regidx s1_idx = mword_of_int a).
    { rewrite (HnA s1_idx ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate)).
      rewrite (Hn9 s1_idx ltac:(vm_compute; discriminate)).
      rewrite (Hn8 s1_idx ltac:(vm_compute; discriminate)).
      rewrite (Hn7 s1_idx ltac:(vm_compute; discriminate)).
      rewrite (Hn6 s1_idx ltac:(vm_compute; discriminate)).
      rewrite (Hn5 s1_idx ltac:(vm_compute; discriminate)). exact Hs1_4. }
    assert (Hs2_A : nA !!! Regidx s2_idx = mword_of_int (Z.of_nat Nb)).
    { rewrite (HnA s2_idx ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate)).
      rewrite (Hn9 s2_idx ltac:(vm_compute; discriminate)).
      rewrite (Hn8 s2_idx ltac:(vm_compute; discriminate)).
      rewrite (Hn7 s2_idx ltac:(vm_compute; discriminate)).
      rewrite (Hn6 s2_idx ltac:(vm_compute; discriminate)).
      rewrite (Hn5 s2_idx ltac:(vm_compute; discriminate)). exact Hs2_4. }
    (* ---- 0x20..0x26  memset(buf, 0, nbuf) ---- *)
    iApply (wp_uk_cmv N h14 nA (mword_of_int 0x20) a2_idx s2_idx
              (mword_of_int (Z.of_nat Nb)) (12 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs2_A moi_add_zero_l; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_20 with "Hcode"). }
    assert (E20 : add_vec_int (mword_of_int 0x20 : mword 64) 2
                  = mword_of_int 0x22)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E20. iIntros (h15) "Hrun".
    set (nB := <[Regidx a2_idx
                 := regval_into_reg (mword_of_int (Z.of_nat Nb)
                                     : mword 64)]> nA).
    assert (HnB : forall r : mword 5, Regidx r <> Regidx a2_idx ->
                    nB !!! Regidx r = nA !!! Regidx r)
      by (intros r Hr; exact (upd_ne nA (Regidx a2_idx) (Regidx r) _ Hr)).
    iApply (wp_uk_cli N h15 nB (mword_of_int 0x22)
              (mword_of_int 0 : mword 6) a1_idx (12 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) with "[] Hrun").
    { iApply (uis_shk_22 with "Hcode"). }
    assert (E22 : add_vec_int (mword_of_int 0x22 : mword 64) 2
                  = mword_of_int 0x24)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E22. iIntros (h16) "Hrun".
    set (nC := <[Regidx a1_idx
                 := regval_into_reg (sign_extend' 64
                                       (mword_of_int 0 : mword 6)
                                     : mword 64)]> nB).
    assert (HnC : forall r : mword 5, Regidx r <> Regidx a1_idx ->
                    nC !!! Regidx r = nB !!! Regidx r)
      by (intros r Hr; exact (upd_ne nB (Regidx a1_idx) (Regidx r) _ Hr)).
    assert (Hs1_C : nC !!! Regidx s1_idx = mword_of_int a).
    { rewrite (HnC s1_idx ltac:(vm_compute; discriminate)).
      rewrite (HnB s1_idx ltac:(vm_compute; discriminate)). exact Hs1_A. }
    iApply (wp_uk_cmv N h16 nC (mword_of_int 0x24) a0_idx s1_idx
              (mword_of_int a) (12 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs1_C moi_add_zero_l; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_24 with "Hcode"). }
    assert (E24 : add_vec_int (mword_of_int 0x24 : mword 64) 2
                  = mword_of_int 0x26)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E24. iIntros (h17) "Hrun".
    set (nD := <[Regidx a0_idx
                 := regval_into_reg (mword_of_int a : mword 64)]> nC).
    assert (HnD : forall r : mword 5, Regidx r <> Regidx a0_idx ->
                    nD !!! Regidx r = nC !!! Regidx r)
      by (intros r Hr; exact (upd_ne nC (Regidx a0_idx) (Regidx r) _ Hr)).
    iApply (wp_uk_jal N h17 nD (mword_of_int 0x26)
              (mword_of_int 2614 : mword 21) ra_idx
              (mword_of_int ShSyms.memset) (mword_of_int 0x2a) (12 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite shp_memset; apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(rewrite shp_memset; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_26 with "Hcode"). }
    iIntros (h18) "Hrun".
    set (nE := <[Regidx ra_idx
                 := regval_into_reg (mword_of_int 0x2a : mword 64)]> nD).
    assert (HnE : forall r : mword 5, Regidx r <> Regidx ra_idx ->
                    nE !!! Regidx r = nD !!! Regidx r)
      by (intros r Hr; exact (upd_ne nD (Regidx ra_idx) (Regidx r) _ Hr)).
    assert (HraE : nE !!! Regidx ra_idx = mword_of_int 0x2a)
      by exact (upd_eq nD (Regidx ra_idx)
                  (regval_into_reg (mword_of_int 0x2a : mword 64))).
    assert (Ha0_E : nE !!! Regidx a0_idx = mword_of_int a).
    { rewrite (HnE a0_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq nC (Regidx a0_idx)
               (regval_into_reg (mword_of_int a : mword 64))). }
    assert (Ha2_E : nE !!! Regidx a2_idx = mword_of_int (Z.of_nat Nb)).
    { rewrite (HnE a2_idx ltac:(vm_compute; discriminate)).
      rewrite (HnD a2_idx ltac:(vm_compute; discriminate)).
      rewrite (HnC a2_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq nA (Regidx a2_idx)
               (regval_into_reg (mword_of_int (Z.of_nat Nb) : mword 64))). }
    replace (12 + nn)%nat with (2 + (10 + nn))%nat by lia.
    iApply (wp_ksh_memset h18 nE a Nb f (10 + nn) Ha0_E Ha2_E HN0 HN31
              with "Hcode Hbs Hrun").
    iIntros "Hbs" (h19 mM) "%HcsM Hrun". rewrite HraE.
    assert (Er2a : ret_pc (mword_of_int 0x2a : mword 64) = mword_of_int 0x2a)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Er2a.
    replace (2 + (10 + nn))%nat with (12 + nn)%nat by lia.
    iAssert (∃ g : nat -> bv 8, ubytes γd a Nb g)%I with "[Hbs]" as "Hbs".
    { iExists _. iExact "Hbs". }
    iDestruct "Hbs" as (fm) "Hbs".
    (* ---- 0x2a..0x2e  gets(buf, nbuf) ---- *)
    assert (Hs2_M : mM !!! Regidx s2_idx = mword_of_int (Z.of_nat Nb)).
    { rewrite (HcsM s2_idx ltac:(vm_compute; reflexivity)).
      rewrite (HnE s2_idx ltac:(vm_compute; discriminate)).
      rewrite (HnD s2_idx ltac:(vm_compute; discriminate)).
      rewrite (HnC s2_idx ltac:(vm_compute; discriminate)).
      rewrite (HnB s2_idx ltac:(vm_compute; discriminate)). exact Hs2_A. }
    assert (Hs1_M : mM !!! Regidx s1_idx = mword_of_int a).
    { rewrite (HcsM s1_idx ltac:(vm_compute; reflexivity)).
      rewrite (HnE s1_idx ltac:(vm_compute; discriminate)).
      rewrite (HnD s1_idx ltac:(vm_compute; discriminate)). exact Hs1_C. }
    iApply (wp_uk_cmv N h19 mM (mword_of_int 0x2a) a1_idx s2_idx
              (mword_of_int (Z.of_nat Nb)) (12 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs2_M moi_add_zero_l; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_2a with "Hcode"). }
    assert (E2a : add_vec_int (mword_of_int 0x2a : mword 64) 2
                  = mword_of_int 0x2c)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E2a. iIntros (h20) "Hrun".
    set (nF := <[Regidx a1_idx
                 := regval_into_reg (mword_of_int (Z.of_nat Nb)
                                     : mword 64)]> mM).
    assert (HnF : forall r : mword 5, Regidx r <> Regidx a1_idx ->
                    nF !!! Regidx r = mM !!! Regidx r)
      by (intros r Hr; exact (upd_ne mM (Regidx a1_idx) (Regidx r) _ Hr)).
    assert (Hs1_F : nF !!! Regidx s1_idx = mword_of_int a)
      by (rewrite (HnF s1_idx ltac:(vm_compute; discriminate)); exact Hs1_M).
    iApply (wp_uk_cmv N h20 nF (mword_of_int 0x2c) a0_idx s1_idx
              (mword_of_int a) (12 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs1_F moi_add_zero_l; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_2c with "Hcode"). }
    assert (E2c : add_vec_int (mword_of_int 0x2c : mword 64) 2
                  = mword_of_int 0x2e)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E2c. iIntros (h21) "Hrun".
    set (nG := <[Regidx a0_idx
                 := regval_into_reg (mword_of_int a : mword 64)]> nF).
    assert (HnG : forall r : mword 5, Regidx r <> Regidx a0_idx ->
                    nG !!! Regidx r = nF !!! Regidx r)
      by (intros r Hr; exact (upd_ne nF (Regidx a0_idx) (Regidx r) _ Hr)).
    iApply (wp_uk_jal N h21 nG (mword_of_int 0x2e)
              (mword_of_int 2684 : mword 21) ra_idx
              (mword_of_int ShSyms.gets) (mword_of_int 0x32) (12 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite shp_gets; apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(rewrite shp_gets; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_2e with "Hcode"). }
    iIntros (h22) "Hrun".
    set (nH := <[Regidx ra_idx
                 := regval_into_reg (mword_of_int 0x32 : mword 64)]> nG).
    assert (HnH : forall r : mword 5, Regidx r <> Regidx ra_idx ->
                    nH !!! Regidx r = nG !!! Regidx r)
      by (intros r Hr; exact (upd_ne nG (Regidx ra_idx) (Regidx r) _ Hr)).
    assert (HraH : nH !!! Regidx ra_idx = mword_of_int 0x32)
      by exact (upd_eq nG (Regidx ra_idx)
                  (regval_into_reg (mword_of_int 0x32 : mword 64))).
    assert (Ha0_H : nH !!! Regidx a0_idx = mword_of_int a).
    { rewrite (HnH a0_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq nF (Regidx a0_idx)
               (regval_into_reg (mword_of_int a : mword 64))). }
    assert (Ha1_H : nH !!! Regidx a1_idx = mword_of_int (Z.of_nat Nb)).
    { rewrite (HnH a1_idx ltac:(vm_compute; discriminate)).
      rewrite (HnG a1_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq mM (Regidx a1_idx)
               (regval_into_reg (mword_of_int (Z.of_nat Nb) : mword 64))). }
    iApply (wp_ksh_gets h22 nH a Nb fm l nn Ha0_H Ha1_H HNle HN31 Hfd0
              with "Hlaw Hcode Hbs Hstd Hpos Hrun").
    iIntros "Hbs" (h23 mG) "%HcsG Hrun". rewrite HraH.
    assert (Er32 : ret_pc (mword_of_int 0x32 : mword 64) = mword_of_int 0x32)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Er32.
    iDestruct "Hbs" as (gg i2) "(%Hgi & Hbs & Hstd & Hpos)".
    (* ---- 0x32  lbu a0,0(s1) -- the return value's only input ---- *)
    assert (Hs1_G : mG !!! Regidx s1_idx = mword_of_int a).
    { rewrite (HcsG s1_idx ltac:(vm_compute; reflexivity)).
      rewrite (HnH s1_idx ltac:(vm_compute; discriminate)).
      rewrite (HnG s1_idx ltac:(vm_compute; discriminate)). exact Hs1_F. }
    iDestruct (ush_bytes_at (DfracOwn 1) a Nb 0%nat gg ltac:(lia) with "Hbs")
      as "[Hb0 Hcl0]".
    rewrite Z.add_0_r.
    iApply (wp_uk_lbu N h23 mG (mword_of_int 0x32)
              (mword_of_int 0 : mword 12) s1_idx a0_idx (DfracOwn 1)
              a (gg 0%nat) (12 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(rewrite Hs1_G (uint_moi a ltac:(unfold Z64 in *; lia));
                    vm_compute uoff_i12; lia)
              ltac:(vm_compute; discriminate)
              with "[] Hb0 Hrun").
    { iApply (uis_shk_32 with "Hcode"). }
    iIntros "Hb0".
    iDestruct ("Hcl0" with "Hb0") as "Hbs".
    rewrite <- (Z.add_0_r a).
    assert (E32 : add_vec_int (mword_of_int 0x32 : mword 64) 4
                  = mword_of_int 0x36)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E32. iIntros (h24) "Hrun".
    set (nI := <[Regidx a0_idx
                 := regval_into_reg (zero_extend' 64 (gg 0%nat : mword 8)
                                     : mword 64)]> mG).
    assert (HnI : forall r : mword 5, Regidx r <> Regidx a0_idx ->
                    nI !!! Regidx r = mG !!! Regidx r)
      by (intros r Hr; exact (upd_ne mG (Regidx a0_idx) (Regidx r) _ Hr)).
    (* ---- 0x36  seqz a0,a0 ; 0x3a  negw a0,a0 -- values not needed ---- *)
    iApply (wp_uk_sltiu N h24 nI (mword_of_int 0x36)
              (mword_of_int 1 : mword 12) a0_idx a0_idx
              (zero_extend' 64
                 (bool_to_bit (zopz0zI_u (nI !!! Regidx a0_idx)
                                 (sign_extend' 64
                                    (mword_of_int 1 : mword 12)))))
              (12 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) eq_refl
              with "[] Hrun").
    { iApply (uis_shk_36 with "Hcode"). }
    assert (E36 : add_vec_int (mword_of_int 0x36 : mword 64) 4
                  = mword_of_int 0x3a)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E36. iIntros (h25) "Hrun".
    set (nJ := <[Regidx a0_idx
                 := regval_into_reg
                      (zero_extend' 64
                         (bool_to_bit (zopz0zI_u (nI !!! Regidx a0_idx)
                                         (sign_extend' 64
                                            (mword_of_int 1 : mword 12)))))]> nI).
    assert (HnJ : forall r : mword 5, Regidx r <> Regidx a0_idx ->
                    nJ !!! Regidx r = nI !!! Regidx r)
      by (intros r Hr; exact (upd_ne nI (Regidx a0_idx) (Regidx r) _ Hr)).
    iDestruct (urun_x0 h25 nJ (mword_of_int 0x3a) (12 + nn) with "Hrun")
      as "[%Hx0J Hrun]".
    iApply (wp_uk_subw N h25 nJ (mword_of_int 0x3a)
              x0_idx a0_idx a0_idx
              (sign_extend' 64
                 (sub_vec (subrange_vec_dec (nJ !!! Regidx x0_idx) 31 0
                           : mword 32)
                    (subrange_vec_dec (nJ !!! Regidx a0_idx) 31 0 : mword 32)))
              (12 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) eq_refl
              with "[] Hrun").
    { iApply (uis_shk_3a with "Hcode"). }
    assert (E3a : add_vec_int (mword_of_int 0x3a : mword 64) 4
                  = mword_of_int 0x3e)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E3a. iIntros (h26) "Hrun".
    set (nK := <[Regidx a0_idx
                 := regval_into_reg
                      (sign_extend' 64
                         (sub_vec (subrange_vec_dec (nJ !!! Regidx x0_idx) 31 0
                                   : mword 32)
                            (subrange_vec_dec (nJ !!! Regidx a0_idx) 31 0
                             : mword 32)))]> nJ).
    assert (HnK : forall r : mword 5, Regidx r <> Regidx a0_idx ->
                    nK !!! Regidx r = nJ !!! Regidx r)
      by (intros r Hr; exact (upd_ne nJ (Regidx a0_idx) (Regidx r) _ Hr)).
    (* THE RETURN VALUE, COMPUTED AT THE ONE INPUT IT HAS (lane IO-LEAF,
       M5(3)): [seqz]/[negw] on a NUL first byte is -1, and that is the
       arm on which the command loop leaves. *)
    assert (Hret : gg 0%nat = ubyte0 ->
                   nK !!! Regidx a0_idx = (mword_of_int (-1) : mword 64)).
    { intro Hg0.
      assert (Ha0I : nI !!! Regidx a0_idx = (zero_reg : mword 64)).
      { rewrite /nI (upd_eq mG (Regidx a0_idx)
                       (regval_into_reg
                          (zero_extend' 64 (gg 0%nat : mword 8) : mword 64))).
        rewrite Hg0. apply bv_eq; vm_compute; reflexivity. }
      assert (Ha0J : nJ !!! Regidx a0_idx = (mword_of_int 1 : mword 64)).
      { rewrite /nJ (upd_eq nI (Regidx a0_idx) _). rewrite Ha0I.
        apply bv_eq; vm_compute; reflexivity. }
      rewrite /nK (upd_eq nJ (Regidx a0_idx) _). rewrite Hx0J Ha0J.
      apply bv_eq; vm_compute; reflexivity. }
    (* ...and 0 on any other first byte: [sltiu a0,a0,1] is false at a
       nonzero unsigned byte, and [negw] of 0 is 0 *)
    assert (Hret0 : gg 0%nat <> ubyte0 ->
                    nK !!! Regidx a0_idx = (mword_of_int 0 : mword 64)).
    { intro Hg0.
      assert (Hlt : zopz0zI_u (nI !!! Regidx a0_idx)
                      (sign_extend' 64 (mword_of_int 1 : mword 12)) = false).
      { rewrite /nI (upd_eq mG (Regidx a0_idx)
                       (regval_into_reg
                          (zero_extend' 64 (gg 0%nat : mword 8) : mword 64))).
        unfold zopz0zI_u, regval_into_reg. apply Z.ltb_ge.
        rewrite !RiscvExtras.uint_unsigned UmodeArith.zext8_unsigned.
        assert (H1 : bv_unsigned (sign_extend' 64 (mword_of_int 1 : mword 12)
                                  : mword 64) = 1)
          by (vm_compute; reflexivity).
        rewrite H1.
        pose proof (bv_unsigned_in_range _ (gg 0%nat)) as [Hg0lo _].
        assert (Hg0nz : bv_unsigned (gg 0%nat) <> 0).
        { intro Hz0. apply Hg0. apply bv_eq. rewrite Hz0.
          vm_compute. reflexivity. }
        (* stated at the byte's own type and closed by [exact]: the goal
           reads the byte through [mword 8], which [lia] does not identify
           with [bv 8] *)
        assert (Hg1 : (1 <= bv_unsigned (gg 0%nat))%Z) by lia.
        exact Hg1. }
      rewrite /nK (upd_eq nJ (Regidx a0_idx) _). rewrite Hx0J.
      rewrite /nJ (upd_eq nI (Regidx a0_idx) _). rewrite Hlt.
      apply bv_eq; vm_compute; reflexivity. }
    (* the sp the epilogue reloads from: it survived all three calls *)
    assert (HspK : nK !!! Regidx csp_rs1
                   = add_vec_int sp0 (- (8 * Z.of_nat 4))).
    { rewrite (HnK csp_rs1 ltac:(vm_compute; discriminate)).
      rewrite (HnJ csp_rs1 ltac:(vm_compute; discriminate)).
      rewrite (HnI csp_rs1 ltac:(vm_compute; discriminate)).
      rewrite (HcsG csp_rs1 ltac:(vm_compute; reflexivity)).
      rewrite (HnH csp_rs1 ltac:(vm_compute; discriminate)).
      rewrite (HnG csp_rs1 ltac:(vm_compute; discriminate)).
      rewrite (HnF csp_rs1 ltac:(vm_compute; discriminate)).
      rewrite (HcsM csp_rs1 ltac:(vm_compute; reflexivity)).
      rewrite (HnE csp_rs1 ltac:(vm_compute; discriminate)).
      rewrite (HnD csp_rs1 ltac:(vm_compute; discriminate)).
      rewrite (HnC csp_rs1 ltac:(vm_compute; discriminate)).
      rewrite (HnB csp_rs1 ltac:(vm_compute; discriminate)).
      rewrite (HnA csp_rs1 ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate)).
      rewrite (Hn9 csp_rs1 ltac:(vm_compute; discriminate)).
      rewrite (Hn8 csp_rs1 ltac:(vm_compute; discriminate)).
      rewrite (Hn7 csp_rs1 ltac:(vm_compute; discriminate)).
      rewrite (Hn6 csp_rs1 ltac:(vm_compute; discriminate)).
      rewrite (Hn5 csp_rs1 ltac:(vm_compute; discriminate)).
      rewrite (Hn4 csp_rs1 ltac:(vm_compute; discriminate)).
      rewrite (Hn3 csp_rs1 ltac:(vm_compute; discriminate)).
      rewrite (Hn2 csp_rs1 ltac:(vm_compute; discriminate)). exact Hsp1. }
    (* ---- 0x3e..0x44  the four reloads ---- *)
    iApply (wp_uk_cldsp N h26 nK (mword_of_int 0x3e)
              (mword_of_int 3 : mword 6) ra_idx (uint sp0 - 8)
              (m !!! Regidx ra_idx) (12 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(rewrite HspK Hsp32 Go3; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              ltac:(vm_compute; discriminate)
              with "[] Hw1 Hrun").
    { iApply (uis_shk_3e with "Hcode"). }
    iIntros "Hw1".
    assert (E3e : add_vec_int (mword_of_int 0x3e : mword 64) 2
                  = mword_of_int 0x40)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E3e. iIntros (h27) "Hrun".
    set (p1 := <[Regidx ra_idx
                 := regval_into_reg (m !!! Regidx ra_idx)]> nK).
    assert (Hsp_p1 : p1 !!! Regidx csp_rs1
                     = add_vec_int sp0 (- (8 * Z.of_nat 4))).
    { rewrite (upd_ne nK (Regidx ra_idx) (Regidx csp_rs1) _
                 ltac:(vm_compute; discriminate)). exact HspK. }
    iApply (wp_uk_cldsp N h27 p1 (mword_of_int 0x40)
              (mword_of_int 2 : mword 6) s0_idx (uint sp0 - 16)
              (m !!! Regidx s0_idx) (12 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(rewrite Hsp_p1 Hsp32 Go2; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              ltac:(vm_compute; discriminate)
              with "[] Hw2 Hrun").
    { iApply (uis_shk_40 with "Hcode"). }
    iIntros "Hw2".
    assert (E40 : add_vec_int (mword_of_int 0x40 : mword 64) 2
                  = mword_of_int 0x42)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E40. iIntros (h28) "Hrun".
    set (p2 := <[Regidx s0_idx
                 := regval_into_reg (m !!! Regidx s0_idx)]> p1).
    assert (Hsp_p2 : p2 !!! Regidx csp_rs1
                     = add_vec_int sp0 (- (8 * Z.of_nat 4))).
    { rewrite (upd_ne p1 (Regidx s0_idx) (Regidx csp_rs1) _
                 ltac:(vm_compute; discriminate)). exact Hsp_p1. }
    iApply (wp_uk_cldsp N h28 p2 (mword_of_int 0x42)
              (mword_of_int 1 : mword 6) s1_idx (uint sp0 - 24)
              (m !!! Regidx s1_idx) (12 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(rewrite Hsp_p2 Hsp32 Go1; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              ltac:(vm_compute; discriminate)
              with "[] Hw3 Hrun").
    { iApply (uis_shk_42 with "Hcode"). }
    iIntros "Hw3".
    assert (E42 : add_vec_int (mword_of_int 0x42 : mword 64) 2
                  = mword_of_int 0x44)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E42. iIntros (h29) "Hrun".
    set (p3 := <[Regidx s1_idx
                 := regval_into_reg (m !!! Regidx s1_idx)]> p2).
    assert (Hsp_p3 : p3 !!! Regidx csp_rs1
                     = add_vec_int sp0 (- (8 * Z.of_nat 4))).
    { rewrite (upd_ne p2 (Regidx s1_idx) (Regidx csp_rs1) _
                 ltac:(vm_compute; discriminate)). exact Hsp_p2. }
    iApply (wp_uk_cldsp N h29 p3 (mword_of_int 0x44)
              (mword_of_int 0 : mword 6) s2_idx (uint sp0 - 32)
              (m !!! Regidx s2_idx) (12 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(rewrite Hsp_p3 Hsp32 Go0; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              ltac:(vm_compute; discriminate)
              with "[] Hw4 Hrun").
    { iApply (uis_shk_44 with "Hcode"). }
    iIntros "Hw4".
    assert (E44 : add_vec_int (mword_of_int 0x44 : mword 64) 2
                  = mword_of_int 0x46)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E44. iIntros (h30) "Hrun".
    set (p4 := <[Regidx s2_idx
                 := regval_into_reg (m !!! Regidx s2_idx)]> p3).
    assert (Hsp_p4 : p4 !!! Regidx csp_rs1
                     = add_vec_int sp0 (- (8 * Z.of_nat 4))).
    { rewrite (upd_ne p3 (Regidx s2_idx) (Regidx csp_rs1) _
                 ltac:(vm_compute; discriminate)). exact Hsp_p3. }
    (* ---- 0x46  c.addi16sp sp,sp,32 -- THE POP ---- *)
    assert (HR4 : 0 <= bv_unsigned sp0 < 18446744073709551616).
    { pose proof (bv_unsigned_in_range 64 sp0) as H0.
      assert (Em : bv_modulus 64 = 18446744073709551616)
        by (vm_compute; reflexivity).
      rewrite Em in H0. exact H0. }
    assert (Hlt4 : bv_unsigned (add_vec_int sp0 (- (8 * Z.of_nat 4)))
                   + 8 * Z.of_nat 4 < Z64)
      by (rewrite Hbsp; unfold Z64; lia).
    assert (Hup4 : add_vec_int (add_vec_int sp0 (- (8 * Z.of_nat 4)))
                     (8 * Z.of_nat 4) = sp0).
    { apply bv_eq.
      rewrite (uv_avi_pos (add_vec_int sp0 (- (8 * Z.of_nat 4)))
                 (8 * Z.of_nat 4) ltac:(lia) Hlt4).
      rewrite Hbsp. lia. }
    iApply (wp_uk_caddi16sp_up N h30 p4 (mword_of_int 0x46)
              (mword_of_int 2 : mword 6) 4 (12 + nn)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "[] [Hw1 Hw2 Hw3 Hw4] Hrun").
    { iApply (uis_shk_46 with "Hcode"). }
    { rewrite Hsp_p4 Hup4 ustack_4.
      iSplit; [ iPureIntro; exact Hal8 | ].
      iSplitL "Hw1"; [ iExists _; iFrame | ].
      iSplitL "Hw2"; [ iExists _; iFrame | ].
      iSplitL "Hw3"; [ iExists _; iFrame | iExists _; iFrame ]. }
    assert (E46 : add_vec_int (mword_of_int 0x46 : mword 64) 2
                  = mword_of_int 0x48)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Hsp_p4 Hup4 E46. iIntros (h31) "Hrun".
    set (p5 := <[Regidx csp_rs1 := regval_into_reg sp0]> p4).
    assert (Hra_p5 : p5 !!! Regidx ra_idx = m !!! Regidx ra_idx).
    { rewrite (upd_ne p4 (Regidx csp_rs1) (Regidx ra_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne p3 (Regidx s2_idx) (Regidx ra_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne p2 (Regidx s1_idx) (Regidx ra_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne p1 (Regidx s0_idx) (Regidx ra_idx) _
                 ltac:(vm_compute; discriminate)).
      exact (upd_eq nK (Regidx ra_idx)
               (regval_into_reg (m !!! Regidx ra_idx))). }
    (* ---- 0x48  c.jr ra ---- *)
    iApply (wp_uk_cjr N h31 p5 (mword_of_int 0x48) ra_idx
              (ret_pc (m !!! Regidx ra_idx)) (4 + (12 + nn))
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hra_p5; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_48 with "Hcode"). }
    iIntros (h32) "Hrun".
    iApply ("Hcont" $! h32 p5 gg i2 with "[] [] [] Hbs Hstd Hpos Hrun").
    { iPureIntro. exact Hgi. }
    2: { iPureIntro.
         (* a0 reaches the caller untouched by the epilogue: both halves of
            the return row are [Hret] / [Hret0] under the same five
            reloads *)
         assert (Ha0p5 : p5 !!! Regidx a0_idx = nK !!! Regidx a0_idx).
         { rewrite (upd_ne p4 (Regidx csp_rs1) (Regidx a0_idx) _
                      ltac:(vm_compute; discriminate)).
           rewrite (upd_ne p3 (Regidx s2_idx) (Regidx a0_idx) _
                      ltac:(vm_compute; discriminate)).
           rewrite (upd_ne p2 (Regidx s1_idx) (Regidx a0_idx) _
                      ltac:(vm_compute; discriminate)).
           rewrite (upd_ne p1 (Regidx s0_idx) (Regidx a0_idx) _
                      ltac:(vm_compute; discriminate)).
           exact (upd_ne nK (Regidx ra_idx) (Regidx a0_idx) _
                    ltac:(vm_compute; discriminate)). }
         rewrite Ha0p5.
         split; intro Hg0; [ exact (Hret Hg0) | exact (Hret0 Hg0) ]. }
    iPureIntro. intros r Hr.
    assert (Hcsp2 : uint csp_rs1 = 2) by (vm_compute; reflexivity).
    destruct (Z.eq_dec (uint r) 2) as [Eq1 | Eq1].
    { rewrite (ush_ridx_eq r csp_rs1 ltac:(rewrite Eq1; exact Hcsp2)).
      rewrite Hsp. exact (upd_eq p4 (Regidx csp_rs1) (regval_into_reg sp0)). }
    destruct (Z.eq_dec (uint r) 8) as [Eq2 | Eq2].
    { rewrite (ush_ridx_eq r s0_idx ltac:(rewrite Eq2; vm_compute; reflexivity)).
      rewrite (upd_ne p4 (Regidx csp_rs1) (Regidx s0_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne p3 (Regidx s2_idx) (Regidx s0_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne p2 (Regidx s1_idx) (Regidx s0_idx) _
                 ltac:(vm_compute; discriminate)).
      exact (upd_eq p1 (Regidx s0_idx)
               (regval_into_reg (m !!! Regidx s0_idx))). }
    destruct (Z.eq_dec (uint r) 9) as [Eq3 | Eq3].
    { rewrite (ush_ridx_eq r s1_idx ltac:(rewrite Eq3; vm_compute; reflexivity)).
      rewrite (upd_ne p4 (Regidx csp_rs1) (Regidx s1_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne p3 (Regidx s2_idx) (Regidx s1_idx) _
                 ltac:(vm_compute; discriminate)).
      exact (upd_eq p2 (Regidx s1_idx)
               (regval_into_reg (m !!! Regidx s1_idx))). }
    destruct (Z.eq_dec (uint r) 18) as [Eq4 | Eq4].
    { rewrite (ush_ridx_eq r s2_idx ltac:(rewrite Eq4; vm_compute; reflexivity)).
      rewrite (upd_ne p4 (Regidx csp_rs1) (Regidx s2_idx) _
                 ltac:(vm_compute; discriminate)).
      exact (upd_eq p3 (Regidx s2_idx)
               (regval_into_reg (m !!! Regidx s2_idx))). }
    (* everything else callee-saved is untouched from end to end *)
    assert (Hu : uint r = 3 \/ uint r = 4 \/ (19 <= uint r <= 27)).
    { pose proof (ucs_cases r Hr) as Hc. lia. }
    rewrite (upd_ne p4 (Regidx csp_rs1) (Regidx r) _
               (ush_r_ne r 2 csp_rs1 ltac:(vm_compute; reflexivity)
                  ltac:(lia))).
    rewrite (upd_ne p3 (Regidx s2_idx) (Regidx r) _
               (ush_r_ne r 18 s2_idx ltac:(vm_compute; reflexivity)
                  ltac:(lia))).
    rewrite (upd_ne p2 (Regidx s1_idx) (Regidx r) _
               (ush_r_ne r 9 s1_idx ltac:(vm_compute; reflexivity)
                  ltac:(lia))).
    rewrite (upd_ne p1 (Regidx s0_idx) (Regidx r) _
               (ush_r_ne r 8 s0_idx ltac:(vm_compute; reflexivity)
                  ltac:(lia))).
    rewrite (upd_ne nK (Regidx ra_idx) (Regidx r) _
               (ush_r_ne r 1 ra_idx ltac:(vm_compute; reflexivity)
                  ltac:(lia))).
    rewrite (HnK r (ush_r_ne r 10 a0_idx ltac:(vm_compute; reflexivity)
                      ltac:(lia))).
    rewrite (HnJ r (ush_r_ne r 10 a0_idx ltac:(vm_compute; reflexivity)
                      ltac:(lia))).
    rewrite (HnI r (ush_r_ne r 10 a0_idx ltac:(vm_compute; reflexivity)
                      ltac:(lia))).
    rewrite (HcsG r Hr).
    rewrite (HnH r (ush_r_ne r 1 ra_idx ltac:(vm_compute; reflexivity)
                      ltac:(lia))).
    rewrite (HnG r (ush_r_ne r 10 a0_idx ltac:(vm_compute; reflexivity)
                      ltac:(lia))).
    rewrite (HnF r (ush_r_ne r 11 a1_idx ltac:(vm_compute; reflexivity)
                      ltac:(lia))).
    rewrite (HcsM r Hr).
    rewrite (HnE r (ush_r_ne r 1 ra_idx ltac:(vm_compute; reflexivity)
                      ltac:(lia))).
    rewrite (HnD r (ush_r_ne r 10 a0_idx ltac:(vm_compute; reflexivity)
                      ltac:(lia))).
    rewrite (HnC r (ush_r_ne r 11 a1_idx ltac:(vm_compute; reflexivity)
                      ltac:(lia))).
    rewrite (HnB r (ush_r_ne r 12 a2_idx ltac:(vm_compute; reflexivity)
                      ltac:(lia))).
    rewrite (HnA r (ush_r_ne r 10 a0_idx ltac:(vm_compute; reflexivity)
                      ltac:(lia))
               (ush_r_ne r 17 a7_idx ltac:(vm_compute; reflexivity)
                  ltac:(lia))).
    rewrite (Hn9 r (ush_r_ne r 1 ra_idx ltac:(vm_compute; reflexivity)
                      ltac:(lia))).
    rewrite (Hn8 r (ush_r_ne r 10 a0_idx ltac:(vm_compute; reflexivity)
                      ltac:(lia))).
    rewrite (Hn7 r (ush_r_ne r 11 a1_idx ltac:(vm_compute; reflexivity)
                      ltac:(lia))).
    rewrite (Hn6 r (ush_r_ne r 11 a1_idx ltac:(vm_compute; reflexivity)
                      ltac:(lia))).
    rewrite (Hn5 r (ush_r_ne r 12 a2_idx ltac:(vm_compute; reflexivity)
                      ltac:(lia))).
    rewrite (Hn4 r (ush_r_ne r 18 s2_idx ltac:(vm_compute; reflexivity)
                      ltac:(lia))).
    rewrite (Hn3 r (ush_r_ne r 9 s1_idx ltac:(vm_compute; reflexivity)
                      ltac:(lia))).
    rewrite (Hn2 r (ush_r_ne r 8 s0_idx ltac:(vm_compute; reflexivity)
                      ltac:(lia))).
    exact (Hn1 r (ush_r_ne r 2 csp_rs1 ltac:(vm_compute; reflexivity)
                    ltac:(lia))).
  Qed.


  (* ===================================================================== *)
  (* THE COMMAND LOOP -- what stage 1 left as the Prop [ush_cmd_head].      *)
  (* DEPENDS ON [ush_read_leaf] (through getcmd).                           *)
  (*                                                                       *)
  (*   for(;;){                                                            *)
  (*     if(getcmd(buf, sizeof(buf)) < 0) break;          <- exit(0)        *)
  (*     while ( *cmd == ' ' || *cmd == '\t') cmd++;                          *)
  (*     if ( *cmd == '\n') continue;                       <- BLANK LINE     *)
  (*     ... the cd builtin, fork1/parsecmd/runcmd ...  <- [ush_rest_l]   *)
  (*   }                                                                   *)
  (*                                                                       *)
  (* THE INVARIANT IS NO LONGER EMPTY.  Stage 1's console loop carried      *)
  (* nothing round its cycle but the free stack; this one carries the       *)
  (* BUFFER -- [ubytes gd sh_buf 100 f] at an existentially quantified [f]  *)
  (* -- and five register values, [ush_regs], which are the constants       *)
  (* 0x914..0x926 loads once and the loop never rewrites.  That is the      *)
  (* whole invariant: the CONTENTS of the buffer are never carried round,   *)
  (* because getcmd re-establishes from scratch what the next turn needs    *)
  (* (a NUL below 100).                                                     *)
  (*                                                                       *)
  (* THE SCAN TERMINATES ON THE NUL, and that is the one place in the stage *)
  (* where a fact about MEMORY decides control flow.  [while ( *cmd==' ' ||   *)
  (* *cmd=='\t') cmd++] has no bound in the code; what bounds it is gets'   *)
  (* postcondition -- [f i2 = 0] for some [i2 < 100] -- because 0 is        *)
  (* neither a space nor a tab.  The measure is [i2 - k], so the scan is a  *)
  (* bounded Rocq induction (echo's strlen mold) inside an [iLöb].          *)
  (*                                                                       *)
  (* WHERE THE STAGE STOPS.  0x97a hands over to [ush_rest_l], an abstract    *)
  (* continuation THAT TAKES THE LOOP HEAD as its own premise: the rest of  *)
  (* main's body ends by falling back into 0x938 (fork1's parent arm does,  *)
  (* and so does the cd builtin), so the two are mutually recursive and the *)
  (* honest cut is a premise that says so.  Stage 4/5 discharge it; nothing *)
  (* here assumes anything about it.                                        *)
  (* ===================================================================== *)

  (* the five constants 0x914..0x926 loads and the loop preserves *)
  Definition ush_regs (m : regfile) : Prop :=
    m !!! Regidx s2_idx = mword_of_int sh_buf /\
    m !!! Regidx s3_idx = mword_of_int 100 /\
    m !!! Regidx s4_idx = mword_of_int 10 /\
    m !!! Regidx s5_idx = mword_of_int 99 /\
    m !!! Regidx s6_idx = mword_of_int 32.

  (* a register OUTSIDE s2..s6 -- which is every one the loop body writes *)
  Definition ush_reg_free (r : mword 5) : bool :=
    let z := uint r in negb ((18 <=? z) && (z <=? 22)).

  Local Lemma ush_regs_upd (m : regfile) (r : mword 5) (v : mword 64) :
    ush_regs m -> ush_reg_free r = true -> ush_regs (<[Regidx r := v]> m).
  Proof using .
    intros (H2 & H3 & H4 & H5 & H6) Hf.
    unfold ush_reg_free in Hf. apply negb_true_iff in Hf.
    assert (Hne : forall (q : mword 5) (z : Z), uint q = z -> 18 <= z <= 22 ->
                    Regidx q <> Regidx r).
    { intros q z Hq Hz. apply ush_ridx_ne. rewrite Hq. intro He.
      apply andb_false_iff in Hf. destruct Hf as [Hf | Hf];
        apply Z.leb_gt in Hf; lia. }
    split_and!.
    - rewrite (upd_ne m (Regidx r) (Regidx s2_idx) v
                 (Hne s2_idx 18 ltac:(vm_compute; reflexivity) ltac:(lia))).
      exact H2.
    - rewrite (upd_ne m (Regidx r) (Regidx s3_idx) v
                 (Hne s3_idx 19 ltac:(vm_compute; reflexivity) ltac:(lia))).
      exact H3.
    - rewrite (upd_ne m (Regidx r) (Regidx s4_idx) v
                 (Hne s4_idx 20 ltac:(vm_compute; reflexivity) ltac:(lia))).
      exact H4.
    - rewrite (upd_ne m (Regidx r) (Regidx s5_idx) v
                 (Hne s5_idx 21 ltac:(vm_compute; reflexivity) ltac:(lia))).
      exact H5.
    - rewrite (upd_ne m (Regidx r) (Regidx s6_idx) v
                 (Hne s6_idx 22 ltac:(vm_compute; reflexivity) ltac:(lia))).
      exact H6.
  Qed.

  Local Lemma ush_regs_cs (m m' : regfile) :
    ush_regs m -> ucallee_saved m m' -> ush_regs m'.
  Proof using .
    intros (H2 & H3 & H4 & H5 & H6) Hcs. split_and!.
    - rewrite (Hcs s2_idx ltac:(vm_compute; reflexivity)). exact H2.
    - rewrite (Hcs s3_idx ltac:(vm_compute; reflexivity)). exact H3.
    - rewrite (Hcs s4_idx ltac:(vm_compute; reflexivity)). exact H4.
    - rewrite (Hcs s5_idx ltac:(vm_compute; reflexivity)). exact H5.
    - rewrite (Hcs s6_idx ltac:(vm_compute; reflexivity)). exact H6.
  Qed.

  (* ===================================================================== *)
  (* THE STANDARD-STREAM LEDGER -- WHAT SH CARRIES, AND WHAT IT DOES NOT    *)
  (* ASSUME.                                                               *)
  (*                                                                       *)
  (* sh opens no standard stream of its own.  It INHERITS fds 0, 1 and 2,   *)
  (* and everything it does with them -- the write() in its prompt, the     *)
  (* read() in gets, and (in runcmd) the close-and-reopen a REDIR performs  *)
  (* and the three closes each half of a PIPE performs -- is done to        *)
  (* descriptors it was handed rather than ones it allocated.               *)
  (*                                                                       *)
  (* WHAT THE LEDGER BUYS IS TWO THINGS, AND NEITHER IS "THEY ARE OPEN".    *)
  (* First, it says WHERE AN OPEN LANDS: fdalloc scans from 0, so the       *)
  (* caller's own record of the low slots computes the descriptor           *)
  (* ([UserFd.ualloc_at] -- the lowest closed slot if there is one, and a   *)
  (* fresh handle above them otherwise).  Second, it is the right to CLOSE  *)
  (* a standard stream: a closed slot is ABSENT from [UserFd.ufd_map], so   *)
  (* close is a DELETE, and the ledger is what says slot 0 or 1 is there    *)
  (* to delete.  A process with no ledger cannot close fd 0 at all, no      *)
  (* matter what the kernel would do, because it has nothing to spend.      *)
  (*                                                                       *)
  (* THE WALK ASSUMES NOTHING ABOUT WHICH OF THE THREE ARE OPEN, and that  *)
  (* is what makes sh's entry cost THREE ARMS rather than one.  init can    *)
  (* hand over a console on fd 0, or an all-closed table (its second open   *)
  (* failed at allocation, so the two dups failed too -- app-echo.md,       *)
  (* "OPEN-PIN PHASE 1 LANDED", finding (a)), or nothing at all beyond the  *)
  (* taint; [ush_fd0] below is that disjunction and [wp_ksh_start] is where *)
  (* it enters.  NO LEMMA BELOW READS IT: sh's walk is the same on all      *)
  (* three arms -- a closed fd 0 makes its first read return -1, [gets]     *)
  (* break at once, [getcmd] return -1 and main exit, and that arm is       *)
  (* already inside the abstract walk -- which is exactly why the CLOSED    *)
  (* arm costs no second proof.  What reads the arm is the DISCIPLINED      *)
  (* LINE (app-echo.md, SH-LINE S4), and that is the console arm's job.     *)
  (*                                                                       *)
  (* xv6's sh reopens "console" until the descriptor comes back at 3 or     *)
  (* above, and that preamble ([wp_ksh_console]) is the ONE program point   *)
  (* in the whole of sh that looks at the ledger's shape.                   *)
  (*                                                                       *)
  (* THE STATES ARE PARAMETERS, not existentials, and nothing here says     *)
  (* what they are.  sh reads from 0 and writes to 1, but the walk never    *)
  (* needs to know they are readable/writable consoles -- the syscall rows  *)
  (* it goes through do not look at [fdstate] -- so pinning them would be   *)
  (* a promise no caller could use and every caller would have to make.     *)
  (* ===================================================================== *)
  (* [ush_std] is stated at the top of the section (seccomp S4): the ledger
     at a table view whose rows are closed or the console. *)

  (* ...AND THE ONE ROW SH'S ENTRY IS TOLD ABOUT, at three arms (header).
     PERSISTENT, which is what makes it a side fact: it is delivered once,
     at the entry, and no resource has to carry it.  The CLOSED arm names
     only slot 0 -- that is all the arm is for, and it is what init's
     all-closed head ([UInitFd.ufd_l0]) weakens to. *)
  Definition ush_fd0 (l : list fdstate) : iProp Σ :=
    (⌜ush_fd0p l⌝ ∨ T)%I.

  Global Instance ush_fd0_persistent l : Persistent (ush_fd0 l).
  Proof. rewrite /ush_fd0. apply _. Qed.

  (* ===================================================================== *)
  (* THE ROW IS A LOOP INVARIANT OF THE CONSOLE PREAMBLE (lane SH-OPEN).    *)
  (*                                                                        *)
  (* sh's preamble reopens "console" until the descriptor comes back at 3   *)
  (* or above, and every open it makes lands at [fd_lowest_closed] of the   *)
  (* ledger it was called at ([UserFd.ualloc_at]).  So the row survives     *)
  (* both ways: if slot 0 is ALREADY the console it is not closed, the      *)
  (* scan lands somewhere else and slot 0 does not move; if slot 0 is       *)
  (* CLOSED it is the LOWEST closed slot, the scan lands exactly there, and *)
  (* what it installs is the console device (the pinned open's receipt      *)
  (* names the type).  That is why the preamble's post is [ush_fd0] again,  *)
  (* at the ledger the loop LEFT -- and why "init's open failed" is not     *)
  (* what the CLOSED arm means any more: it means every open sh itself made *)
  (* failed too.                                                            *)
  (* ===================================================================== *)
  (* ===================================================================== *)
  (* THE TAINT'S GENERIC CONTINUATION, as a premise of the preamble.        *)
  (*                                                                       *)
  (* [UConsLine.ush_gen_slot]'s definition, moved DOWN to the program tier  *)
  (* because the preamble is the first walk that needs it: sh's console     *)
  (* open is PINNED, and at the taint there is no pin -- so the preamble    *)
  (* does not make the call at all, it hands the run to the generic slot    *)
  (* ([UkRun.urun_gen]).  That is also why no [udepw_law 15] remains in     *)
  (* this file: nothing here ever routes open through the key-free law.     *)
  (* ===================================================================== *)
  (* ...AND IT CARRIES THE RECORD'S PARK BIT (lane OFF-HAND-3, R1).  The
     family the taint runs on is narrowed to ALL-PARKED KEYS
     ([ExecEntry.image_entry_taint]), and the key a running process is at
     is bound by [UkRun.urun]'s own existential -- so the only thing that
     can pay that row at [ush_gen_run] is the run's own, which is guarded
     by [UkRun.ukn_held].  THE SET RIDES HERE, IN THE SLOT, and not as a
     section hypothesis: a section hypothesis would have to be named in the
     [Proof using] of every lemma on sh's walk between the entry and the
     taint, and none of them says anything about it.  The slot is already
     threaded to exactly those lemmas, it is already persistent, and its
     producer ([UShKernel.sh_uexec_slot]) holds the equation the entry
     constructor handed over. *)
  Definition ush_gen_slot : iProp Σ :=
    (□ (∀ W : uvis,
          T -∗ my_pay (uvis_gen W) (ukn_pay N) -∗ uslot W))%I.

  Global Instance ush_gen_slot_persistent : Persistent ush_gen_slot.
  Proof using . rewrite /ush_gen_slot. apply _. Qed.

  (* [ush_gen_slot_held] IS DELETED with [UkRun.ukn_held] (lane OFF-LINK-2,
     L6): the slot carried "sh's record holds no offset half", which is the
     fact design/app-file.md SS3.5's principle retires. *)

  Lemma ush_gen_run (h : CpuId) (m : regfile) (pc : mword 64) (avail : nat) :
    is_aligned_vaddr (Virtaddr pc) 2 = true ->
    ush_gen_slot -∗ T -∗ urun N h m pc avail -∗ mWP (Loop : expr riscv_lang).
  Proof using .
    intro Hal. rewrite /ush_gen_slot. iIntros "#Hg HT Hrun".
    iApply (urun_gen N T h m pc avail Hal with "Hg HT Hrun").
  Qed.

  (* THE TAG'S READING ([ush_tag_law]) IS STATED ABOVE THE READ LEAF now
     (lane SH-LINE 2b, R2): it is spent INSIDE [gets], on the byte the
     read swallowed, so it has to be in scope there. *)

  (* ===================================================================== *)
  (* SH'S CONSOLE OPEN, AS TWO LEAF BODIES (lane SH-OPEN, H2).              *)
  (*                                                                       *)
  (* [UkInit.uki_open_console_leaf] / [uki_open_absent_leaf] are the mould, *)
  (* one syscall stub over: the program tier names no application           *)
  (* ([UConsLine.v:202]), so the two calls are stated HERE as leaf BODIES   *)
  (* over the abstract pieces and DISCHARGED at the era, where the pin      *)
  (* lives.  The difference from /init's is only in the ADDRESSES: sh's     *)
  (* stub is at [ShSyms.open] (0xcc6) and its "console" literal is the      *)
  (* eight bytes at 0x1388 in its own .rodata ([UCodeShK.shk_ro]), which    *)
  (* 0x8f8/0x8fc compute into s2 and 0x902 moves into a0.                   *)
  (*                                                                       *)
  (*   [T]  THE TAINT, exactly [ush_fd0]'s third arm.                       *)
  (*   [K]  THE ABSENCE CREDENTIAL.  What makes the FIRST open's SUCCESS    *)
  (*        arm REFUTABLE at a view with no console node, rather than an    *)
  (*        arm sh has to carry.  It is a PARAMETER here for [T]'s reason;  *)
  (*        which resource the era supplies is the application's business   *)
  (*        (app-echo.md, SH-OPEN H3).                                      *)
  (*                                                                       *)
  (* THE WORKING DIRECTORY IS NAMED, and that is new for sh: a pinned open  *)
  (* is about a PATH, "console" names a file only relative to the directory *)
  (* it is resolved from, and the pin resolves it from the ROOT             *)
  (* ([UkRun.udepwf_at] fixes the cwd for exactly this reason).  sh does    *)
  (* not chdir before the preamble, so the row is its entry's -- and after  *)
  (* the preamble it is weakened to [UserCwd.ucwd_any] again, which is all  *)
  (* the command loop's [cd] needs.                                         *)
  (* ===================================================================== *)

  (* THE OPEN AT THE RESOLVING PIN: three arms.  The descriptor the ledger
     decided, open at the console DEVICE and readable and writable (O_RDWR
     is [om_readable]/[om_writable] both true); or the call failed at
     allocation ([filealloc] / [fdalloc], about which sh proves NOTHING,
     exactly as /init proves nothing -- app-echo.md, "OPEN-PIN FINDINGS",
     FACT 3) and the ledger did not move; or the taint.  The TYPE is what
     the pin buys; the NUMBER is the caller's own ledger's answer. *)
  (* the allocation's ledger at an ok view (seccomp S4) *)
  Definition ush_ualloc (l : list fdstate) (fd : nat) (st : fdstate) : iProp Σ :=
    (∃ w : list fdstate, ⌜ush_view_ok w⌝ ∗ ualloc_v γfd l fd st w)%I.

  Lemma ush_ualloc_std (l : list fdstate) (fd k : nat) (st : fdstate) :
    fd_lowest_closed l = Some k ->
    ush_ualloc l fd st -∗ ⌜fd = k⌝ ∗ ush_std (<[k := st]> l).
  Proof using .
    intros Hk. iIntros "[%w [%Hok Hl]]".
    iDestruct (ualloc_v_std with "Hl") as "[$ Hl]"; [exact Hk |].
    iExists w. by iFrame "Hl".
  Qed.

  Lemma ush_ualloc_hi (l : list fdstate) (fd : nat) (st : fdstate) :
    fd_lowest_closed l = None ->
    ush_ualloc l fd st -∗ ⌜(NSTD <= fd)%nat⌝ ∗ ush_std l ∗ ufd γfd fd st.
  Proof using .
    intros Hk. iIntros "[%w [%Hok Hl]]".
    iDestruct (ualloc_v_hi with "Hl") as "($ & Hl & $)"; [exact Hk |].
    iExists w. by iFrame "Hl".
  Qed.

  Definition ush_open_console_leaf : iProp Σ :=
    (∀ (h : CpuId) (m : regfile) (l v : list fdstate) (avail : nat),
       shk_code γt -∗
       (* the read-only image and the two argument words: a0 = "console" at
          0x1388, a1 = O_RDWR.  The preamble holds both at 0x904
          ([wp_ksh_console]'s walk from 0x900). *)
       shk_rodata γt -∗
       ⌜ m !!! Regidx a0_idx = (mword_of_int sh_cons_pv : mword 64)
         /\ m !!! Regidx a1_idx = (mword_of_int 2 : mword 64) ⌝ -∗
       urun N h m (mword_of_int ShSyms.open) avail -∗
       UserCwd.ucwd γcwd FsImg.ROOTINO -∗
       (* THE LEDGER AT A NAMED VIEW (seccomp S4): an allocation re-sets
          the view to the new table, the old table under the old view *)
       ustd_at γfd l v -∗
       (∀ (h' : CpuId) (ret : mword 64),
          ((∃ fd : nat,
              ⌜ret = (mword_of_int (Z.of_nat fd) : mword 64)
               /\ (fd < NOFILE)%nat⌝ ∗
              ∃ fdv : list fdstate, ⌜tab_le fdv v⌝ ∗
                ualloc_v γfd l fd (FdOpen true true (FdDevice CONSOLE))
                  (<[fd := FdOpen true true (FdDevice CONSOLE)]> fdv))
           ∨ (⌜ret = (mword_of_int (-1) : mword 64)⌝ ∗ ustd_at γfd l v)
           ∨ T) -∗
          UserCwd.ucwd γcwd FsImg.ROOTINO -∗
          urun N h'
            (<[Regidx a0_idx := ret]>
               (<[Regidx a7_idx := (mword_of_int 15 : mword 64)]> m))
            (ret_pc (m !!! Regidx ra_idx)) avail -∗
          mWP (Loop : expr riscv_lang)) -∗
       mWP (Loop : expr riscv_lang))%I.

  (* THE OPEN AT THE PIN THAT MISSES: TWO arms, and there is no third.  At
     a view the credential holds of, the walk dies at hop 0
     ([PinnedObs.pobs_walk_dead]), so the success arm is REFUTED rather
     than carried -- which is what makes the [bltz a0] at 0x908 provably
     leave the loop, at the ledger sh came in with.  The credential goes in
     and comes back, as /init's does. *)
  Definition ush_open_absent_leaf (K : iProp Σ) : iProp Σ :=
    (∀ (h : CpuId) (m : regfile) (l v : list fdstate) (avail : nat),
       shk_code γt -∗
       shk_rodata γt -∗
       ⌜ m !!! Regidx a0_idx = (mword_of_int sh_cons_pv : mword 64)
         /\ m !!! Regidx a1_idx = (mword_of_int 2 : mword 64) ⌝ -∗
       urun N h m (mword_of_int ShSyms.open) avail -∗
       UserCwd.ucwd γcwd FsImg.ROOTINO -∗
       ustd_at γfd l v -∗
       K -∗
       (∀ (h' : CpuId) (ret : mword 64),
          ((⌜ret = (mword_of_int (-1) : mword 64)⌝ ∗ ustd_at γfd l v ∗ K)
           ∨ T) -∗
          UserCwd.ucwd γcwd FsImg.ROOTINO -∗
          urun N h'
            (<[Regidx a0_idx := ret]>
               (<[Regidx a7_idx := (mword_of_int 15 : mword 64)]> m))
            (ret_pc (m !!! Regidx ra_idx)) avail -∗
          mWP (Loop : expr riscv_lang)) -∗
       mWP (Loop : expr riscv_lang))%I.

  (* ...AND WHAT SH'S ENTRY IS TOLD ABOUT THE CONSOLE NODE, as ONE
     resource: the node is THERE (and then every open sh makes either
     installs the console device at the lowest closed standard stream or
     fails at allocation), or it is NOT (and then every open returns [-1]
     and nothing moves), or the application is tainted and sh's walk stops
     being sh's ([ush_gen_slot]).

     THE PRESENT ARM IS PERSISTENT and the ABSENT one is not: "the console
     resolves to inode i" is a consequence of a persistent flag
     ([AppEcho.cons_made]), while "the console is absent" is the refutation
     of the claim's own PRESENT arms and needs a CREDENTIAL
     ([UInitCons.init_cons_abs_law]'s [K]).  That asymmetry is the lane's
     one open design question -- app-echo.md, SH-OPEN H3. *)
  Definition ush_cons_in (K : iProp Σ) : iProp Σ :=
    (□ ush_open_console_leaf ∨ (□ ush_open_absent_leaf K ∗ K) ∨ T)%I.

  (* ...AND THE ONE CALL THE PREAMBLE MAKES, whichever state the node is
     in.  This is what makes the preamble's loop ONE walk rather than three:
     the state goes in, the ledger's own answer and THE STATE AGAIN come
     back, so [ush_cons_in] rides the loop's back edge.  The two ways the
     walk can stop being sh's are absorbed here -- the taint at the entry
     (the call is not made at all) and the taint out of either leaf -- and
     both go to [ush_gen_slot].

     THE ABSENT ARM NEVER REACHES THE BACK EDGE, and nothing here says so:
     it hands back [-1], the [bltz] at 0x908 is taken, and the loop is left
     at the ledger sh came in with.  The credential is simply carried in
     the rebuilt [ush_cons_in]. *)
  Lemma ush_cons_open (K : iProp Σ) (h : CpuId) (m : regfile)
      (l : list fdstate) (avail : nat) :
    m !!! Regidx a0_idx = (mword_of_int sh_cons_pv : mword 64) ->
    m !!! Regidx a1_idx = (mword_of_int 2 : mword 64) ->
    is_aligned_vaddr (Virtaddr (ret_pc (m !!! Regidx ra_idx))) 2 = true ->
    shk_code γt -∗
    shk_rodata γt -∗
    ush_gen_slot -∗
    urun N h m (mword_of_int ShSyms.open) avail -∗
    UserCwd.ucwd γcwd FsImg.ROOTINO -∗
    ush_std l -∗
    ush_cons_in K -∗
    (∀ (h' : CpuId) (ret : mword 64),
       ((∃ fd : nat,
           ⌜ret = (mword_of_int (Z.of_nat fd) : mword 64)
            /\ (fd < NOFILE)%nat⌝ ∗
           ush_ualloc l fd (FdOpen true true (FdDevice CONSOLE)))
        ∨ (⌜ret = (mword_of_int (-1) : mword 64)⌝ ∗ ush_std l)) -∗
       ush_cons_in K -∗
       UserCwd.ucwd γcwd FsImg.ROOTINO -∗
       urun N h'
         (<[Regidx a0_idx := ret]>
            (<[Regidx a7_idx := (mword_of_int 15 : mword 64)]> m))
         (ret_pc (m !!! Regidx ra_idx)) avail -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using HT.
    intros Ha0 Ha1 Hal.
    iIntros "#Hcode #Hro #Hgen Hrun Hcwd Hstd Hin Hcont".
    iDestruct "Hstd" as (v) "[%Hok Hstd]".
    iDestruct "Hin" as "[#Hlf | [[#Hlf HK] | #HT]]".
    - (* THE NODE IS THERE: the pinned open resolves *)
      iApply ("Hlf" $! h m l v avail with "Hcode Hro [%] Hrun Hcwd Hstd").
      { split; [ exact Ha0 | exact Ha1 ]. }
      iIntros (h' ret) "[Hal | [Hm1 | #HT]] Hcwd Hrun".
      + iApply ("Hcont" $! h' ret with "[Hal] [] Hcwd Hrun");
          [ iLeft | iLeft; iExact "Hlf" ].
        iDestruct "Hal" as (fd) "[%Hr Hal]". iDestruct "Hal" as (fdv) "[%Hle Hal]".
        iExists fd. iSplitR; [ by iPureIntro |]. rewrite /ush_ualloc.
        iExists _. iFrame "Hal". iPureIntro. exact (ush_view_ok_open fdv v fd true true Hok Hle).
      + iApply ("Hcont" $! h' ret with "[Hm1] [] Hcwd Hrun");
          [ iRight | iLeft; iExact "Hlf" ].
        iDestruct "Hm1" as "[$ Hstd]". iExists v. by iFrame "Hstd".
      + iApply (ush_gen_run h' _ _ avail Hal with "Hgen HT Hrun").
    - (* THE NODE IS NOT THERE: the pinned open MISSES, provably *)
      iApply ("Hlf" $! h m l v avail with "Hcode Hro [%] Hrun Hcwd Hstd HK").
      { split; [ exact Ha0 | exact Ha1 ]. }
      iIntros (h' ret) "[(%Hrm & Hstd & HK) | #HT] Hcwd Hrun".
      + iApply ("Hcont" $! h' ret with "[Hstd] [HK] Hcwd Hrun").
        * iRight. iSplitR; [ by iPureIntro |]. iExists v. by iFrame "Hstd".
        * iRight. iLeft. iFrame "Hlf HK".
      + iApply (ush_gen_run h' _ _ avail Hal with "Hgen HT Hrun").
    - (* THE TAINT: sh's walk stops being sh's before the call *)
      assert (Halo : is_aligned_vaddr
                       (Virtaddr (mword_of_int ShSyms.open : mword 64)) 2
                     = true)
        by (rewrite shp_open; vm_compute; reflexivity).
      iApply (ush_gen_run h m _ avail Halo with "Hgen HT Hrun").
  Qed.

  (* ...AND THE PROGRAM'S HALF OF THE CONSOLE POSITION PAIR
     ([UserConsole.upos]) IS [ush_pos], STATED ABOVE THE READ (lane
     SH-LINE 2b, R1'): the read's own answer is what hands it back, so its
     definition has to be in scope where the read leaf is stated. *)

  (* ===================================================================== *)
  (* ...AND THE OTHER GHOST A TURN CANNOT ESCAPE CARRYING: THE CWD.        *)
  (*                                                                       *)
  (* [UkRun.urun] holds the process's authority over its working directory *)
  (* ([UserCwd.ucwd_auth], pinned to the inum the trap key is at), and an  *)
  (* authority does not move without the fragment -- so sh's [cd] builtin, *)
  (* which issues chdir, must hold one, exactly as its REDIR must hold the *)
  (* descriptor ledger.  The cwd, unlike the ledger, is never READ by the  *)
  (* walk -- sh never asks which directory it is in -- so it travels       *)
  (* index-free ([UserCwd.ucwd_any]).                                      *)
  (*                                                                       *)
  (* ...AND THE THIRD: THE CHILDREN SET.  [UkRun.urun] holds the other     *)
  (* half of it too, and fork MOVES the set -- an update takes both halves *)
  (* -- so sh's [fork1] cannot call fork without one, exactly as its [cd]  *)
  (* cannot call chdir without the cwd.  sh never asks WHICH children it   *)
  (* has (its wait() reads a pid off a0 and nothing else), so this travels *)
  (* index-free too ([UserChildren.uch_any]) and its fork site drops the   *)
  (* token the kernel mints ([UkFork.wp_uk_ecall_fork_any]).               *)
  (*                                                                       *)
  (* THE THREE TRAVEL AS ONE RESOURCE, which is why this definition exists *)
  (* rather than three premises beside [ush_std] at thirteen sites:        *)
  (* every lemma between the loop head and the syscall that spends one is  *)
  (* then unchanged by the others' arrival.  [UserFd.ufd_state] is the     *)
  (* same move one tier down.                                             *)
  (* ===================================================================== *)
  (* ...AND THE FOURTH, WHICH GOES LAST (durable-notes, "Shaping a change
     so the sweep is small"): the console POSITION.  sh was lent the
     console reader token inside its exit payload ([UserConsole.ucons_pay],
     which is linear in [UkRun.urun] and abstract to the program), and the
     half of the position pair it holds in its hand is what turns a read's
     receipt into a receipt AT ITS OWN CURSOR.  It travels with the other
     three for their reason: fork does not move it, the read does. *)
  (* ...AT A LINE BOUNDARY (lane IO-LEAF, M5(3)).  A turn of the command
     loop begins where the previous line ENDED, and that is a fact about
     the NUMBER the cursor stands at -- without it the byte the next read
     delivers is not the next LINE's first byte.  So the fourth conjunct
     is [ush_posb] and not the bare position; the read moves it from one
     boundary to the next and nothing else in a turn touches it. *)
  (* ...AND SH'S OWN PID, AS A HANDLE (step 4): the row the wait's reaping
     arm is read against ([UkRunSys.wp_uk_ecall_wait_null_pid]), at the
     record's own ghost name, index-free like the children set.  The entry
     hands it over ([UkRun.uslot_of_urun]'s row) and nothing in a turn
     moves it. *)
  (* ...AND THE WORKING DIRECTORY IS THE ROOT (step 4; SH-LINE R3(2)): the
     disciplined shell's one line is [echo hello world], never [cd], and its
     forked child execs /echo on a PIN, which resolves a path from the
     directory the process is in.  It enters at the root
     ([UShKernel.sh_uexec_slot]'s [uvis_cwd W = ROOTINO]) and nothing in a
     turn moves it -- the [cd] arm is refuted at the body's dispatch
     ([UkShFork.wp_kshm_body]). *)
  (* ...AND BOTH ARE PINNED NOW (lane EXEC-SEAM): the children set is
     EMPTY -- a fresh sh has forked nobody, and every turn's fork is
     redeemed by the wait that follows it ([UkShFork.ushf_wait_empty]) --
     and the pid is NOT <init>'s, which is what makes the wait's reaping
     arm speak of sh's OWN set ([UserChildren.wait_ans]'s [γ' ∈ cs ∨ pidv
     = 1], the right disjunct refuted).  Both come off the exec'd key
     ([UShKernel.sh_uexec_slot], from [SpecKexec.exec_slot_pre]'s two
     identity rows).  ONE conjunct each, so the positional readers of this
     state did not move. *)
  Definition ush_pid : iProp Σ :=
    (∃ p : Z, ⌜p <> 1⌝ ∗ UserChildren.upid γpid p)%I.

  Global Instance ush_pid_timeless : Timeless ush_pid.
  Proof using . rewrite /ush_pid. apply _. Qed.

  Definition ush_pstate (l : list fdstate) : iProp Σ :=
    (ush_std l ∗ UserCwd.ucwd γcwd FsImg.ROOTINO ∗ UserChildren.uch γch ∅
     ∗ ush_pid ∗ ush_posb l 0%nat)%I.

  (* ...AND THE BODY'S STATE (step 4): the same, with the slot at the
     BLOCK-OWED index the line's read left ([ush_gets_done_line]).  This
     is what main's body is handed and what its fork lends from; the [cd]
     arm and a failed fork go back to the head through
     [ush_posb_blk_line].
     INDEXED BY THE LINE THE TURN READ (project echo-any-line), because
     that is what the slot is FOR: the fork lends the block credential at
     the boundary the line closed and its child runs that line's words, and
     [ush_posw]'s equation is the only thing tying the two together. *)
  Definition ush_bstate (l : list fdstate) (ws : list (list (bv 8)))
      : iProp Σ :=
    (ush_std l ∗ UserCwd.ucwd γcwd FsImg.ROOTINO ∗ UserChildren.uch γch ∅
     ∗ ush_pid ∗ ush_posw l ws)%I.

  (* ...and back to the head's, where nothing was written: a blank line's
     back edge, the [cd] arm's, and a fork that failed *)
  Lemma ush_pstate_of_bstate (l : list fdstate) (ws : list (list (bv 8))) :
    ush_bstate l ws -∗ ush_pstate l.
  Proof using ush_wc_blk_line.
    rewrite /ush_bstate /ush_pstate.
    iIntros "(Hstd & Hcwd & Hch & Hpid & Hpos)". iFrame "Hstd Hcwd Hch Hpid".
    iApply (ush_posb_blk_line l with "[Hpos]").
    iApply (ush_posb_of_posw l ws with "Hpos").
  Qed.

  (* the loop head, and the abstract rest of main's body ------------------ *)
  (* Both are indexed by the two states, because both are re-entered: the
     head is sh's command loop and the rest hands back into it.  sh's parent
     never closes either descriptor -- a REDIR runs in the forked CHILD,
     which gets its own descriptor authority at the fork arm -- so the two
     states that come round the loop are the two that went in. *)
  (* THE BODY'S FRAME, as the sum it is.  main's body reaches [fork1] (2
     words), the diagnostic subtree under it (28 -- [UkShDiag.ush_Dg]),
     the parser (60) and the runner (8); the [cd] arm's own 26 (fprintf's
     frame) fits inside the same total.  It is a NUMBER here and a sum in
     the files that spend it, because this file walks none of them. *)
  (* EIGHT MORE THAN ECHO'S (the program stream, SH-CHILD-2's "one
     number").  The body's room has to cover the DEEPEST child it forks,
     and the file application's sh forks a redirect child whose parse is
     eight words deeper than the symbol-free one
     ([UkShRedirPc.wp_kshp_parsecmd_gt] asks [68 + nn] where
     [UkShParseCmd.wp_kshp_parser] asks [60 + nn]).  The echo tier carries
     the eight unspent: a child law is [∀ n], so more room is the same law
     at a bigger [n] and no landed walk moved. *)
  (* ...AND THE PIPELINE'S ROOM (cut C8): a pipeline's right spine nests
     one [runcmd] frame (6 words) per stage in the forked child, and the
     longest line the buffer holds carries 15 bare cats, so the child's
     room is 60 words more than the redirect's.  The body's frame is the
     same 88; [ush_Dpipe] is carried beside it, and a child law may spend
     up to [68 + ush_Dpipe] of what the fork hands it. *)
  Definition ush_Dpipe : nat := 60%nat.
  Definition ush_Dbody : nat := 148%nat.

  Lemma ush_Dbody_split : ush_Dbody = (88 + ush_Dpipe)%nat.
  Proof using. reflexivity. Qed.

  (* [R] IS WHAT A TURN CARRIES AND DOES NOT CREATE, and it is abstract
     here on purpose.  Stages 1-2 carried the five constants, the
     descriptor promise and the line buffer; main's body also needs the two
     static lexer tables, the allocator's first-call state and the break --
     and naming any of those would drag the parser's and the allocator's
     files into this one.  So the loop carries an OPAQUE [R] round its
     cycle, and iris/UkShLoop.v is where it is said what [R] is. *)
  (* ...AND THE ROW THE PREAMBLE ESTABLISHED (lane SH-OPEN).  It enters the
     command loop HERE, at the ledger the preamble's opens LEFT -- which is
     the whole point of pinning them: [wp_ksh_start] used to be handed
     [ush_fd0] at its ENTRY ledger and the preamble then moved that ledger,
     so the row the read of fd 0 needs (SH-LINE 2b) was about a list no
     lemma below could name.  It is a PREMISE of the head rather than a
     conjunct of [ush_pstate] because it is NOT preserved by everything a
     turn does: a REDIR reopens fd 0 onto a file, and it does so in the
     forked CHILD, which takes [ush_pstate] and not this. *)
  (* ...AND WHAT PAYS FOR THE PROMPT IS INSIDE THE PROCESS STATE (lane
     IO-LEAF, M6a(3), step 3): the era's credential rides [ush_posb]'s
     slot beside the cursor, at every turn, and the entry supplies it
     through the lend ([UShLine.ush_posb_of_lend]). *)
  Definition ush_loop_head (R : iProp Σ) (l : list fdstate) : iProp Σ :=
    (∀ (h : CpuId) (m : regfile) (f : nat -> bv 8) (n : nat),
       ⌜ ush_regs m ⌝ -∗
       ⌜ ush_fd0p l ⌝ -∗
       ush_pstate l -∗
       R -∗
       ubytes γd sh_buf sh_nbuf f -∗
       urun N h m (mword_of_int 0x938) (16 + (ush_Dbody + n)) -∗
       mWP (Loop : expr riscv_lang))%I.

  (* ===================================================================== *)
  (* WHAT REPLACES [UkShFork.ushf_lexable] (lane SH-LINE 2b, L3).            *)
  (*                                                                        *)
  (* [ushf_lexable] quantified over EVERY line the user could type, which   *)
  (* is why it is false.  What the command loop hands its body instead is   *)
  (* this, about the ONE line the read's receipt says sh read: either the   *)
  (* FIRST NUL at or after [k] ends a line whose words are [ws]             *)
  (* ([ush_line_is], hence [UkShLoop.ush_line_lexable]), or the TAINT --    *)
  (* and on the taint the body's continuation is the generic one            *)
  (* ([ush_gen_run] above).                                                 *)
  (*                                                                        *)
  (* THE WORD LIST IS A PARAMETER and not an existential, because the same  *)
  (* [ws] indexes the body's slot ([ush_bstate]): the fork lends a          *)
  (* credential at the boundary this line closed, so the line fact and the  *)
  (* credential have to name ONE line.                                      *)
  (*                                                                        *)
  (* STATED OVER THE FIRST NUL rather than over a given [len] because that  *)
  (* is what [UkShFork.ushf_first_nul] produces: the body derives its own   *)
  (* [len] from the loop's "some byte at or after [k] is NUL", and the line *)
  (* fact has to hold at the [len] it derived.                              *)
  (* ===================================================================== *)
  Definition ush_rest_line_at (D : FileDisc.uline -> Prop)
      (ws : list (list (bv 8))) (f : nat -> bv 8) (k : nat) : iProp Σ :=
    ((∀ len : nat,
        ⌜forall j : nat, (j < len)%nat -> f (k + j)%nat <> ubyte0⌝ -∗
        ⌜f (k + len)%nat = ubyte0⌝ -∗
        ⌜exists l : FileDisc.uline,
           D l /\ FileDisc.uline_ws l = ws /\ ush_line_at l f k len⌝)
     ∨ T)%I.

  Definition ush_rest_line (ws : list (list (bv 8))) (f : nat -> bv 8)
      (k : nat) : iProp Σ := ush_rest_line_at ush_line_echo ws f k.

  Global Instance ush_rest_line_at_persistent D ws f k :
    Persistent (ush_rest_line_at D ws f k).
  Proof using HT.
    rewrite /ush_rest_line_at. apply bi.or_persistent; apply _.
  Qed.
  Global Instance ush_rest_line_persistent ws f k :
    Persistent (ush_rest_line ws f k).
  Proof using HT. rewrite /ush_rest_line. apply _. Qed.

  (* ...AND THE ARM A TAINTED TURN IS AT, as a constructor, so a walk that
     has learned the taint does not have to spell the disjunction. *)
  Lemma ush_rest_line_at_taint (D : FileDisc.uline -> Prop)
      (ws : list (list (bv 8))) (f : nat -> bv 8) (k : nat) :
    T -∗ ush_rest_line_at D ws f k.
  Proof using . iIntros "HT". rewrite /ush_rest_line_at. by iRight. Qed.

  Lemma ush_rest_line_taint (ws : list (list (bv 8))) (f : nat -> bv 8)
      (k : nat) :
    T -∗ ush_rest_line ws f k.
  Proof using . exact (ush_rest_line_at_taint ush_line_echo ws f k). Qed.

  (* ...and the ECHO era's producer, in one line: the constructor its
     discipline admits, at the line the read delivered. *)
  Lemma ush_line_echo_of_is (ws : list (list (bv 8))) (f : nat -> bv 8)
      (k len : nat) :
    ush_line_is ws f k len ->
    exists l : FileDisc.uline,
      ush_line_echo l /\ FileDisc.uline_ws l = ws /\ ush_line_at l f k len.
  Proof using .
    intro Hl. exists (FileDisc.LEcho ws).
    split; [ by exists ws | ]. split; [ reflexivity | exact Hl ].
  Qed.

  (* ===================================================================== *)
  (* §2b THE JUMP TABLE, as a resource: five rows of four TEXT bytes.  Only *)
  (* the five rows a well-formed node can select are here; row 0 is the     *)
  (* default arm's, and the node predicate makes it unreachable.            *)
  (* ===================================================================== *)
  Definition ush_jrow (g : gname) (k : Z) : iProp Σ :=
    ([∗ list] j ∈ seq 0 4,
       utext g (SH_JTAB + 4 * k + Z.of_nat j) (nth_byte (ush_jent k) j))%I.

  (* ...AND SH'S READ-ONLY IMAGE BESIDE THEM.  The jump table IS .rodata
     (0x13a8 is inside [ShData.sh_data]), so the two belong together, and
     what makes it worth saying is the DIAGNOSTIC CUT below: every site that
     reaches sh's printer needs the three format strings, which are .rodata
     too, and every one of those sites already carries [ush_jtab] -- through
     the recursion, through each arm, and across every fork, since the whole
     thing is [Forkable].  Carrying the image here rather than as a sixth
     premise is what keeps [wp_kshr_runcmd]'s statement, all four fork
     payloads and every budget exactly where stage 5 left them. *)
  Definition ush_jtab (g : gname) : iProp Σ :=
    (ush_jrow g 1 ∗ ush_jrow g 2 ∗ ush_jrow g 3 ∗
     ush_jrow g 4 ∗ ush_jrow g 5 ∗ shk_rodata g)%I.

  Global Instance ush_jrow_persistent g k : Persistent (ush_jrow g k).
  Proof using . apply _. Qed.
  Global Instance ush_jtab_persistent g : Persistent (ush_jtab g).
  Proof using . apply _. Qed.

  (* ...and the image it carries *)
  Lemma ush_jtab_ro (g : gname) : ush_jtab g -∗ shk_rodata g.
  Proof using . iIntros "(_ & _ & _ & _ & _ & #H)". iExact "H". Qed.

  (* ...AND WHERE IT COMES FROM: the .rodata image itself (lane SH-LINE 2b,
     (b)).  The table IS .rodata, so a process that holds sh's read-only
     image holds the table -- twenty [utext] points-tos out of one
     [UserHeap.utext_img], each looked up by [ush_jrow_bytes].  This is
     what lets [UShKernel.sh_uexec_slot] pay [ush_jtab] off the key's own
     text, beside [shk_code] and [shk_rodata], instead of a caller of
     [UInitSh.sh_pay_rest] carrying it -- which no caller could. *)
  Lemma ush_jtab_of_rodata (g : gname) : shk_rodata g -∗ ush_jtab g.
  Proof using .
    iIntros "#Hro".
    iAssert (∀ k : Z, ⌜In k [1; 2; 3; 4; 5]%Z⌝ -∗ ush_jrow g k)%I as "#Hrow".
    { iIntros (k) "%Hk". rewrite /ush_jrow.
      iApply (utext_img_run g shk_ro (SH_JTAB + 4 * k) 4 (ush_jent k)
                ltac:(intros j Hj; exact (ush_jrow_bytes k j Hk Hj))
                with "[Hro]").
      rewrite /shk_rodata. iExact "Hro". }
    rewrite /ush_jtab.
    iSplitR; [ iApply ("Hrow" $! 1 with "[%]"); cbn; tauto | ].
    iSplitR; [ iApply ("Hrow" $! 2 with "[%]"); cbn; tauto | ].
    iSplitR; [ iApply ("Hrow" $! 3 with "[%]"); cbn; tauto | ].
    iSplitR; [ iApply ("Hrow" $! 4 with "[%]"); cbn; tauto | ].
    iSplitR; [ iApply ("Hrow" $! 5 with "[%]"); cbn; tauto | ].
    iExact "Hro".
  Qed.

  (* WHAT THE ENTRY PAYS AND THE BODY MAY THEREFORE ASK FOR (lane
     SH-LINE 2b, (b)).  Three things sh's body needs that its own
     [urun] does not carry, and all three are facts about THE RECORD the
     kernel minted for it, so only the ENTRY can produce them and no
     caller of [UInitSh.sh_pay_rest] ever could:

       [⌜ukn_const N⌝]   sh's exit stub answers [ukn_pay N xs ∧
                         ukn_pay N (-1)] out of ONE resource, which it
                         can only do at a payload that does not read the
                         status ([UserConsole.ucons_pay_const] is the
                         witness the entry supplies).
       [shk_code γt]     sh's text, off the key's own image
                         ([UCodeShK.shk_code_of_text]).
       [ush_jtab γt]     runcmd's jump table and the .rodata it carries,
                         off the same image.

     Before this they were premises of the DISCHARGER
     ([UkShFork.ushf_rest_of_body]), which made [sh_pay_rest] -- a [∀]
     over every [uk_names] record -- unprovable by construction.  They are
     premises of the OBLIGATION now, [wp_ksh_loop] below pays them (it
     already holds the first two and the third is threaded beside the
     code), and [UShKernel.sh_uexec_slot] pays them at the entry. *)
  (* ...WITH THE LINE FACT IN IT (lane SH-LINE 2b, L3; the weaker
     obligation of the two is the ONLY one now -- lane IO-LEAF, M5(3)).
     The body is where the buffer is LEXED, so that is where "this line's
     words are [ws], or the taint" has to arrive: it rides beside
     [ush_fd0p] and before the process state, so the rows the walk reads
     stay together.

     STATED OVER THE FIRST NUL rather than over a given [len] because that
     is what [UkShFork.ushf_first_nul] produces.  The SIBLING obligation
     [ush_rest] -- the same thing without the line fact -- is gone with
     M5(3): [wp_ksh_getcmd] produces the fact now, so the loop takes this
     one and nothing is left that could take the other. *)
  Definition ush_rest_l_at (D : FileDisc.uline -> Prop) (R : iProp Σ)
      : iProp Σ :=
    (□ (∀ (l : list fdstate),
        ⌜ ukn_const N ⌝ -∗
        (* ...AND THE LEASE'S TWO LAWS THE BODY'S FORK ARM SPENDS (lane
           IO-LEAF, step 3): the loop holds the PIECES ([Pm]) and the fork
           arm assembles the payload from them at a boundary
           ([ush_at_of_pm_wb]) and takes it apart again on the returning arm
           ([ush_pm_of_at]).  Premises of the OBLIGATION for the same
           reason as the three above: the laws are this section's
           hypotheses, so [wp_ksh_loop] pays them, and no caller of
           [UInitSh.sh_pay_rest] -- a [∀] over every [Pm] -- could. *)
        ⌜ forall n : nat,
            ⊢ ush_at n -∗ ∃ I : list (bv 8), ⌜length I = n⌝ ∗ ush_lease I ⌝ -∗
        (* ...AND THE PAYLOAD'S OWN ASSEMBLER, at a boundary and with the
           banner-owed credential ([ush_at_of_pm_wb]): what the fork
           panic's exit is paid from.  A premise of the OBLIGATION for the
           same reason (lane R3): it is this section's hypothesis, so
           [wp_ksh_loop] pays it and no discharger stated over an
           arbitrary [Pm]/[Wb] pair could. *)
        ⌜ forall I : list (bv 8), ⊢ Pm I -∗ Wb I -∗ ush_at (length I) ⌝ -∗
        shk_code γt -∗
        ush_jtab γt -∗
        (* ...AND THE TAINT'S GENERIC CONTINUATION (lane R3).  The body's
           line fact has the taint as its second arm and a tainted process
           stops running sh's code ([ush_gen_run]); the slot is a fact
           about the RECORD the kernel minted ([ukn_pay N] is the console
           lease's pair), so the entry produces it and the discharger
           cannot.  Same rule as the three above. *)
        ush_gen_slot -∗
        ush_loop_head R l -∗
        ∀ (h : CpuId) (m : regfile) (f : nat -> bv 8) (k i2 : nat) (n : nat)
          (ws : list (list (bv 8))),
          ⌜ ush_regs m ⌝ -∗
          ⌜ m !!! Regidx s1_idx = mword_of_int (sh_buf + Z.of_nat k) ⌝ -∗
          ⌜ m !!! Regidx a5_idx = mword_of_int (bv_unsigned (f k)) ⌝ -∗
          ⌜ (k <= i2 < sh_nbuf)%nat /\ f i2 = ubyte0 ⌝ -∗
          ⌜ ush_fd0p l ⌝ -∗
          ush_rest_line_at D ws f k -∗
          ush_bstate l ws -∗
          R -∗
          ubytes γd sh_buf sh_nbuf f -∗
          urun N h m (mword_of_int 0x97a) (16 + (ush_Dbody + n)) -∗
          mWP (Loop : expr riscv_lang)))%I.

  (* the ECHO era's obligation, and the landed name: every file that
     threads it ([UShKernel], [UInitSh], [UShRest]) is stated at this one
     and does not move.  A widened era passes its own [D]. *)
  Definition ush_rest_l (R : iProp Σ) : iProp Σ :=
    ush_rest_l_at ush_line_echo R.

  (* NOT [apply _]: with the obligation transparent the search walks its
     whole body.  Name the instance the box deserves. *)
  Global Instance ush_rest_l_at_persistent D R : Persistent (ush_rest_l_at D R).
  Proof using .
    rewrite /ush_rest_l_at. apply bi.intuitionistically_persistent.
  Qed.
  Global Instance ush_rest_l_persistent R : Persistent (ush_rest_l R).
  Proof using . rewrite /ush_rest_l. apply _. Qed.

  (* ---- ONE TURN of the leading-blank scan, 0x964..0x974 ---------------- *)
  (*   c.addi s1,1 ; lbu a5,0(s1) ; addi a4,a5,-32 ; c.beqz a4,0x964        *)
  (*   addi a4,a5,-9 ; c.beqz a4,0x964                                      *)
  (* s1 points AT the byte just tested on entry and one past it on exit;    *)
  (* the byte decides where control goes, and the caller says which target  *)
  (* it expects.  (UkEcho.v's [wp_kecho_strlen_step] is the mold.)          *)
  Local Lemma wp_ksh_scan_step (h : CpuId) (mc : regfile) (k : nat)
      (b : mword 8) (bz : Z) (tgt : mword 64) (n : nat) :
    bv_unsigned b = bz ->
    ush_regs mc ->
    mc !!! Regidx s1_idx = mword_of_int (sh_buf + Z.of_nat k) ->
    0 <= sh_buf + Z.of_nat (k + 1) < Z64 ->
    tgt = (if (bz =? 32) || (bz =? 9)
           then mword_of_int 0x964 else mword_of_int 0x976) ->
    shk_code γt -∗
    ubyteq γd (DfracOwn 1) (sh_buf + Z.of_nat (k + 1)) b -∗
    urun N h mc (mword_of_int 0x964) (16 + n) -∗
    (ubyteq γd (DfracOwn 1) (sh_buf + Z.of_nat (k + 1)) b -∗
       ∀ (h' : CpuId) (mc' : regfile),
         ⌜ ush_regs mc' ⌝ -∗
         ⌜ mc' !!! Regidx s1_idx
             = mword_of_int (sh_buf + Z.of_nat (k + 1)) ⌝ -∗
         ⌜ mc' !!! Regidx a5_idx = mword_of_int bz ⌝ -∗
         urun N h' mc' tgt (16 + n) -∗
         mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Hbz Hregs Hs1 Hrng Htgt. iIntros "#Hcode Hb Hrun Hcont".
    assert (Hbzr : 0 <= bz < 256).
    { rewrite <- Hbz. pose proof (bv_unsigned_in_range 8 b) as Hr8.
      assert (Em8 : bv_modulus 8 = 256) by (vm_compute; reflexivity).
      rewrite Em8 in Hr8. exact Hr8. }
    (* ---- 0x964  c.addi s1,s1,1 ---- *)
    assert (E1 : (sign_extend' 64 (mword_of_int 1 : mword 6) : mword 64)
                 = mword_of_int 1)
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uk_caddi N h mc (mword_of_int 0x964)
              (mword_of_int 1 : mword 6) s1_idx
              (mword_of_int (sh_buf + Z.of_nat (k + 1))) (16 + n)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs1 E1 moi_add;
                    replace (sh_buf + Z.of_nat (k + 1))
                      with (sh_buf + Z.of_nat k + 1) by lia; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_964 with "Hcode"). }
    assert (E964 : add_vec_int (mword_of_int 0x964 : mword 64) 2
                   = mword_of_int 0x966)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E964. iIntros (h1) "Hrun".
    set (m1 := <[Regidx s1_idx
                 := regval_into_reg (mword_of_int (sh_buf + Z.of_nat (k + 1))
                                     : mword 64)]> mc).
    assert (Hs1_1 : m1 !!! Regidx s1_idx
                    = mword_of_int (sh_buf + Z.of_nat (k + 1)))
      by exact (upd_eq mc (Regidx s1_idx)
                  (regval_into_reg (mword_of_int (sh_buf + Z.of_nat (k + 1))
                                    : mword 64))).
    assert (Hreg1 : ush_regs m1)
      by exact (ush_regs_upd mc s1_idx _ Hregs ltac:(vm_compute; reflexivity)).
    (* ---- 0x966  lbu a5,0(s1) ---- *)
    iApply (wp_uk_lbu N h1 m1 (mword_of_int 0x966)
              (mword_of_int 0 : mword 12) s1_idx a5_idx (DfracOwn 1)
              (sh_buf + Z.of_nat (k + 1)) b (16 + n)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(rewrite Hs1_1
                      (uint_moi (sh_buf + Z.of_nat (k + 1)) Hrng);
                    vm_compute uoff_i12; lia)
              ltac:(vm_compute; discriminate)
              with "[] Hb Hrun").
    { iApply (uis_shk_966 with "Hcode"). }
    iIntros "Hb".
    assert (E966 : add_vec_int (mword_of_int 0x966 : mword 64) 4
                   = mword_of_int 0x96a)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E966. iIntros (h2) "Hrun".
    set (m2 := <[Regidx a5_idx
                 := regval_into_reg (zero_extend' 64 b : mword 64)]> m1).
    assert (Ha5_2 : m2 !!! Regidx a5_idx = mword_of_int bz).
    { rewrite (upd_eq m1 (Regidx a5_idx)
                 (regval_into_reg (zero_extend' 64 b : mword 64))).
      rewrite <- Hbz. exact (zext8_moi b). }
    assert (Hreg2 : ush_regs m2)
      by exact (ush_regs_upd m1 a5_idx _ Hreg1 ltac:(vm_compute; reflexivity)).
    assert (Hs1_2 : m2 !!! Regidx s1_idx
                    = mword_of_int (sh_buf + Z.of_nat (k + 1))).
    { rewrite (upd_ne m1 (Regidx a5_idx) (Regidx s1_idx) _
                 ltac:(vm_compute; discriminate)). exact Hs1_1. }
    (* ---- 0x96a  addi a4,a5,-32 ---- *)
    iApply (wp_uk_addi N h2 m2 (mword_of_int 0x96a)
              (mword_of_int 4064 : mword 12) a5_idx a4_idx
              (mword_of_int (bz - 32)) (16 + n)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha5_2;
                    exact (ush_addi_sub bz 32 (mword_of_int 4064 : mword 12)
                             ltac:(unfold Z64; lia)
                             ltac:(vm_compute; reflexivity)))
              with "[] Hrun").
    { iApply (uis_shk_96a with "Hcode"). }
    assert (E96a : add_vec_int (mword_of_int 0x96a : mword 64) 4
                   = mword_of_int 0x96e)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E96a. iIntros (h3) "Hrun".
    set (m3 := <[Regidx a4_idx
                 := regval_into_reg (mword_of_int (bz - 32) : mword 64)]> m2).
    assert (Ha4_3 : m3 !!! Regidx a4_idx = mword_of_int (bz - 32))
      by exact (upd_eq m2 (Regidx a4_idx)
                  (regval_into_reg (mword_of_int (bz - 32) : mword 64))).
    assert (Hreg3 : ush_regs m3)
      by exact (ush_regs_upd m2 a4_idx _ Hreg2 ltac:(vm_compute; reflexivity)).
    assert (Hs1_3 : m3 !!! Regidx s1_idx
                    = mword_of_int (sh_buf + Z.of_nat (k + 1))).
    { rewrite (upd_ne m2 (Regidx a4_idx) (Regidx s1_idx) _
                 ltac:(vm_compute; discriminate)). exact Hs1_2. }
    assert (Ha5_3 : m3 !!! Regidx a5_idx = mword_of_int bz).
    { rewrite (upd_ne m2 (Regidx a4_idx) (Regidx a5_idx) _
                 ltac:(vm_compute; discriminate)). exact Ha5_2. }
    (* ---- 0x96e  c.beqz a4,0x964 -- a SPACE goes round ---- *)
    assert (Htk32 : Z.eqb bz 32 = eq_vec (m3 !!! Regidx a4_idx) zero_reg).
    { rewrite Ha4_3. symmetry.
      exact (ush_eqz_sub bz 32 ltac:(unfold Z64; lia) ltac:(unfold Z64; lia)). }
    iApply (wp_uk_cbeqz N h3 m3 (mword_of_int 0x96e)
              (mword_of_int 251 : mword 8) (mword_of_int 6 : mword 3)
              a4_idx (Z.eqb bz 32) (mword_of_int 0x964) (16 + n)
              ltac:(vm_compute; reflexivity) Htk32
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(intros _; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_96e with "Hcode"). }
    destruct (Z.eqb_spec bz 32) as [Hb32 | Hb32].
    { iIntros (h4) "Hrun".
      assert (Htg32 : tgt = mword_of_int 0x964).
      { rewrite Htgt; try (rewrite Hb32); try (rewrite Hb9);
          vm_compute; reflexivity. }
      iSpecialize ("Hcont" with "Hb").
      iApply ("Hcont" $! h4 m3 with "[] [] [] [Hrun]").
      - iPureIntro. exact Hreg3.
      - iPureIntro. exact Hs1_3.
      - iPureIntro. exact Ha5_3.
      - rewrite Htg32. iExact "Hrun". }
    assert (E96e : add_vec_int (mword_of_int 0x96e : mword 64) 2
                   = mword_of_int 0x970)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E96e. iIntros (h4) "Hrun".
    (* ---- 0x970  addi a4,a5,-9 ---- *)
    iApply (wp_uk_addi N h4 m3 (mword_of_int 0x970)
              (mword_of_int 4087 : mword 12) a5_idx a4_idx
              (mword_of_int (bz - 9)) (16 + n)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha5_3;
                    exact (ush_addi_sub bz 9 (mword_of_int 4087 : mword 12)
                             ltac:(unfold Z64; lia)
                             ltac:(vm_compute; reflexivity)))
              with "[] Hrun").
    { iApply (uis_shk_970 with "Hcode"). }
    assert (E970 : add_vec_int (mword_of_int 0x970 : mword 64) 4
                   = mword_of_int 0x974)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E970. iIntros (h5) "Hrun".
    set (m4 := <[Regidx a4_idx
                 := regval_into_reg (mword_of_int (bz - 9) : mword 64)]> m3).
    assert (Ha4_4 : m4 !!! Regidx a4_idx = mword_of_int (bz - 9))
      by exact (upd_eq m3 (Regidx a4_idx)
                  (regval_into_reg (mword_of_int (bz - 9) : mword 64))).
    assert (Hreg4 : ush_regs m4)
      by exact (ush_regs_upd m3 a4_idx _ Hreg3 ltac:(vm_compute; reflexivity)).
    assert (Hs1_4 : m4 !!! Regidx s1_idx
                    = mword_of_int (sh_buf + Z.of_nat (k + 1))).
    { rewrite (upd_ne m3 (Regidx a4_idx) (Regidx s1_idx) _
                 ltac:(vm_compute; discriminate)). exact Hs1_3. }
    assert (Ha5_4 : m4 !!! Regidx a5_idx = mword_of_int bz).
    { rewrite (upd_ne m3 (Regidx a4_idx) (Regidx a5_idx) _
                 ltac:(vm_compute; discriminate)). exact Ha5_3. }
    assert (Htk9 : Z.eqb bz 9 = eq_vec (m4 !!! Regidx a4_idx) zero_reg).
    { rewrite Ha4_4. symmetry.
      exact (ush_eqz_sub bz 9 ltac:(unfold Z64; lia) ltac:(unfold Z64; lia)). }
    iApply (wp_uk_cbeqz N h5 m4 (mword_of_int 0x974)
              (mword_of_int 248 : mword 8) (mword_of_int 6 : mword 3)
              a4_idx (Z.eqb bz 9) (mword_of_int 0x964) (16 + n)
              ltac:(vm_compute; reflexivity) Htk9
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(intros _; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_974 with "Hcode"). }
    assert (E974 : add_vec_int (mword_of_int 0x974 : mword 64) 2
                   = mword_of_int 0x976)
      by (apply bv_eq; vm_compute; reflexivity).
    destruct (Z.eqb_spec bz 9) as [Hb9 | Hb9].
    { iIntros (h6) "Hrun".
      assert (Htg9 : tgt = mword_of_int 0x964).
      { rewrite Htgt; try (rewrite Hb32); try (rewrite Hb9);
          vm_compute; reflexivity. }
      iSpecialize ("Hcont" with "Hb").
      iApply ("Hcont" $! h6 m4 with "[] [] [] [Hrun]").
      - iPureIntro. exact Hreg4.
      - iPureIntro. exact Hs1_4.
      - iPureIntro. exact Ha5_4.
      - rewrite Htg9. iExact "Hrun". }
    iIntros (h6) "Hrun".
    assert (Htg0 : tgt = mword_of_int 0x976).
    { rewrite Htgt; try (rewrite Hb32); try (rewrite Hb9);
        vm_compute; reflexivity. }
    iSpecialize ("Hcont" with "Hb").
    iApply ("Hcont" $! h6 m4 with "[] [] [] [Hrun]").
    - iPureIntro. exact Hreg4.
    - iPureIntro. exact Hs1_4.
    - iPureIntro. exact Ha5_4.
    - rewrite E974 Htg0. iExact "Hrun".
  Qed.


  (* ---- the scan as a whole, 0x964..0x974 under the NUL's measure ------- *)
  Local Lemma wp_ksh_scan (f : nat -> bv 8) (i2 : nat) :
    forall (d k : nat) (h : CpuId) (mc : regfile) (n : nat),
    (i2 = k + 1 + d)%nat -> (i2 < sh_nbuf)%nat -> f i2 = ubyte0 ->
    ush_regs mc ->
    mc !!! Regidx s1_idx = mword_of_int (sh_buf + Z.of_nat k) ->
    shk_code γt -∗
    ubytes γd sh_buf sh_nbuf f -∗
    urun N h mc (mword_of_int 0x964) (16 + n) -∗
    (∀ (h' : CpuId) (mc' : regfile) (k' : nat),
       ⌜ (k' <= i2)%nat ⌝ -∗
       ⌜ ush_regs mc' ⌝ -∗
       ⌜ mc' !!! Regidx s1_idx = mword_of_int (sh_buf + Z.of_nat k') ⌝ -∗
       ⌜ mc' !!! Regidx a5_idx = mword_of_int (bv_unsigned (f k')) ⌝ -∗
       ubytes γd sh_buf sh_nbuf f -∗
       urun N h' mc' (mword_of_int 0x976) (16 + n) -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    assert (Hbf : sh_buf = 8224) by (vm_compute; reflexivity).
    assert (Hnb : sh_nbuf = 100%nat) by (vm_compute; reflexivity).
    intros d. induction d as [| d IH ];
      intros k h mc n Hi2 Hlt Hnul Hregs Hs1;
      iIntros "#Hcode Hbs Hrun Hcont";
      assert (Hk1lt : (k + 1 < sh_nbuf)%nat) by lia;
      assert (Hrng : 0 <= sh_buf + Z.of_nat (k + 1) < Z64)
        by (rewrite Hbf; rewrite Hnb in Hk1lt; unfold Z64; lia);
      iDestruct (ush_bytes_at (DfracOwn 1) sh_buf sh_nbuf (k + 1)%nat f Hk1lt
                   with "Hbs") as "[Hb Hcl]".
    - (* the byte AT k+1 IS the NUL: neither test fires, the scan ends *)
      assert (Hbz0 : bv_unsigned (f (k + 1)%nat) = 0)
        by (replace (k + 1)%nat with i2 by lia; rewrite Hnul;
            vm_compute; reflexivity).
      iApply (wp_ksh_scan_step h mc k (f (k + 1)%nat) 0
                (mword_of_int 0x976) n Hbz0 Hregs Hs1 Hrng
                ltac:(vm_compute; reflexivity)
                with "Hcode Hb Hrun").
      iIntros "Hb" (h1 mc') "%Hr %Hs %Ha Hrun".
      iDestruct ("Hcl" with "Hb") as "Hbs".
      iApply ("Hcont" $! h1 mc' (k + 1)%nat with "[] [] [] [] Hbs Hrun");
        iPureIntro; [ lia | exact Hr | exact Hs | rewrite Hbz0; exact Ha ].
    - remember ((bv_unsigned (f (k + 1)%nat) =? 32)
                || (bv_unsigned (f (k + 1)%nat) =? 9))%bool as blank eqn:Hbl.
      destruct blank.
      + (* a blank: round again at k+1, one closer to the NUL *)
        iApply (wp_ksh_scan_step h mc k (f (k + 1)%nat)
                  (bv_unsigned (f (k + 1)%nat)) (mword_of_int 0x964) n
                  eq_refl Hregs Hs1 Hrng
                  ltac:(rewrite <- Hbl; reflexivity)
                  with "Hcode Hb Hrun").
        iIntros "Hb" (h1 mc') "%Hr %Hs %Ha Hrun".
        iDestruct ("Hcl" with "Hb") as "Hbs".
        iApply (IH (k + 1)%nat h1 mc' n ltac:(lia) Hlt Hnul Hr Hs
                  with "Hcode Hbs Hrun").
        iIntros (h2 mc'' k') "%Hk' %Hr' %Hs' %Ha' Hbs Hrun".
        iApply ("Hcont" $! h2 mc'' k' with "[] [] [] [] Hbs Hrun");
          iPureIntro; [ exact Hk' | exact Hr' | exact Hs' | exact Ha' ].
      + (* not a blank: the scan ends here *)
        iApply (wp_ksh_scan_step h mc k (f (k + 1)%nat)
                  (bv_unsigned (f (k + 1)%nat)) (mword_of_int 0x976) n
                  eq_refl Hregs Hs1 Hrng
                  ltac:(rewrite <- Hbl; reflexivity)
                  with "Hcode Hb Hrun").
        iIntros "Hb" (h1 mc') "%Hr %Hs %Ha Hrun".
        iDestruct ("Hcl" with "Hb") as "Hbs".
        iApply ("Hcont" $! h1 mc' (k + 1)%nat with "[] [] [] [] Hbs Hrun");
          iPureIntro; [ lia | exact Hr | exact Hs | exact Ha ].
  Qed.

  (* ---- 0x9ca  the loop's only exit: exit(0) --------------------------- *)
  Local Lemma wp_ksh_die (h : CpuId) (mc : regfile) (n : nat) :
    shk_code γt -∗
    (* the loop's exit is sh's OWN exit, so the payload is sh's own lease
       (lane KILL-PAY, K4(a)) *)
    ukn_pay N (-1) -∗
    urun N h mc (mword_of_int 0x9ca) n -∗
    mWP (Loop : expr riscv_lang).
  Proof using Hpay.
    iIntros "#Hcode Hpay Hrun".
    iApply (wp_uk_cli N h mc (mword_of_int 0x9ca)
              (mword_of_int 0 : mword 6) a0_idx n
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) with "[] Hrun").
    { iApply (uis_shk_9ca with "Hcode"). }
    assert (E9ca : add_vec_int (mword_of_int 0x9ca : mword 64) 2
                   = mword_of_int 0x9cc)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E9ca. iIntros (h1) "Hrun".
    set (q := <[Regidx a0_idx
                := regval_into_reg (sign_extend' 64 (mword_of_int 0 : mword 6)
                                    : mword 64)]> mc).
    iApply (wp_uk_jal N h1 q (mword_of_int 0x9cc)
              (mword_of_int 698 : mword 21) ra_idx
              (mword_of_int ShSyms.exit) (mword_of_int 0x9d0) n
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite shp_exit; apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(rewrite shp_exit; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_9cc with "Hcode"). }
    iIntros (h2) "Hrun".
    iApply (wp_ksh_exit h2 _ n with "Hcode Hpay Hrun").
  Qed.


  (* ---- 0x95c/0x960  both ways into the scan land s1 on the buffer ----- *)
  (* ...AND IT RUNS UNDER THE TAINT ONLY (lane IO-LEAF, M5(3)): the era's
     line begins with 'e', so a LEADING BLANK is something only a tainted
     turn can see -- which is what lets this arm hand the tail the line
     fact it owes ([ush_rest_line_taint]) without knowing where the scan
     will stop. *)
  Local Lemma wp_ksh_blank_entry (h : CpuId) (mc : regfile) (g : nat -> bv 8)
      (ws : list (list (bv 8))) (i2 n : nat) :
    ush_regs mc -> (0 < i2)%nat -> (i2 < sh_nbuf)%nat -> g i2 = ubyte0 ->
    shk_code γt -∗
    T -∗
    (∀ (hh : CpuId) (mm : regfile) (kk : nat),
       ⌜ ush_regs mm ⌝ -∗ ⌜ (kk <= i2)%nat ⌝ -∗
       ⌜ mm !!! Regidx s1_idx = mword_of_int (sh_buf + Z.of_nat kk) ⌝ -∗
       ⌜ mm !!! Regidx a5_idx = mword_of_int (bv_unsigned (g kk)) ⌝ -∗
       ush_rest_line_at Dl ws g kk -∗
       ubytes γd sh_buf sh_nbuf g -∗
       urun N hh mm (mword_of_int 0x976) (16 + n) -∗
       mWP (Loop : expr riscv_lang)) -∗
    ubytes γd sh_buf sh_nbuf g -∗
    urun N h mc (mword_of_int 0x95c) (16 + n) -∗
    mWP (Loop : expr riscv_lang).
  Proof.
    intros Hregs Hi20 Hi2lt Hnul. iIntros "#Hcode #HTb Htail Hbs Hrun".
    iApply (wp_uk_auipc N h mc (mword_of_int 0x95c)
              (mword_of_int 1 : mword 20) s1_idx
              (add_vec (mword_of_int 0x95c : mword 64)
                 (auipc_off (mword_of_int 1 : mword 20))) (16 + n)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) eq_refl
              with "[] Hrun").
    { iApply (uis_shk_95c with "Hcode"). }
    assert (E95c : add_vec_int (mword_of_int 0x95c : mword 64) 4
                   = mword_of_int 0x960)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E95c. iIntros (h1) "Hrun".
    set (q1 := <[Regidx s1_idx
                 := regval_into_reg
                      (add_vec (mword_of_int 0x95c : mword 64)
                         (auipc_off (mword_of_int 1 : mword 20)))]> mc).
    assert (Hq1 : ush_regs q1)
      by exact (ush_regs_upd mc s1_idx _ Hregs ltac:(vm_compute; reflexivity)).
    iApply (wp_uk_addi N h1 q1 (mword_of_int 0x960)
              (mword_of_int 1732 : mword 12) s1_idx s1_idx
              (mword_of_int sh_buf) (16 + n)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (upd_eq mc (Regidx s1_idx)
                               (regval_into_reg
                                  (add_vec (mword_of_int 0x95c : mword 64)
                                     (auipc_off (mword_of_int 1 : mword 20)))));
                    apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_960 with "Hcode"). }
    assert (E960 : add_vec_int (mword_of_int 0x960 : mword 64) 4
                   = mword_of_int 0x964)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E960. iIntros (h2) "Hrun".
    set (q2 := <[Regidx s1_idx
                 := regval_into_reg (mword_of_int sh_buf : mword 64)]> q1).
    assert (Hq2 : ush_regs q2)
      by exact (ush_regs_upd q1 s1_idx _ Hq1 ltac:(vm_compute; reflexivity)).
    assert (Hs1_2 : q2 !!! Regidx s1_idx
                    = mword_of_int (sh_buf + Z.of_nat 0)).
    { replace (sh_buf + Z.of_nat 0) with sh_buf by lia.
      exact (upd_eq q1 (Regidx s1_idx)
               (regval_into_reg (mword_of_int sh_buf : mword 64))). }
    iApply (wp_ksh_scan g i2 (i2 - 1)%nat 0%nat h2 q2 n ltac:(lia) Hi2lt Hnul
              Hq2 Hs1_2 with "Hcode Hbs Hrun").
    iIntros (h3 mc' k') "%Hk' %Hr' %Hs' %Ha' Hbs Hrun".
    iApply ("Htail" $! h3 mc' k' with "[] [] [] [] [] Hbs Hrun");
      [ iPureIntro; exact Hr' | iPureIntro; exact Hk'
      | iPureIntro; exact Hs' | iPureIntro; exact Ha'
      | iApply (ush_rest_line_at_taint Dl ws g k' with "HTb") ].
  Qed.

  (* ---- the loop itself: 0x938..0x976, under one iLöb ------------------ *)
  (* DEPENDS ON [ush_read_leaf] (through getcmd).                          *)
  Local Lemma wp_ksh_loop (R : iProp Σ) (l : list fdstate) :
    □ (T -∗ sh_deps) -∗
    ush_tag_law -∗
    ush_prompt_law -∗
    ush_rest_l_at Dl R -∗ shk_code γt -∗ ush_jtab γt -∗ ush_gen_slot -∗
    ush_loop_head R l.
  Proof using Hdsc_ncr Hdsc_line Hdsc_short HT Hpay ush_at_of_pm_taint ush_at_of_pm_wb ush_pm_of_at ush_read_leaf ush_wb_read ush_wc_blk_line ush_wc_read.
    assert (Hbf : sh_buf = 8224) by (vm_compute; reflexivity).
    assert (Hnb : sh_nbuf = 100%nat) by (vm_compute; reflexivity).
    assert (Hnbz : Z.of_nat sh_nbuf = 100) by (vm_compute; reflexivity).
    (* THE LINE FITS sh's BUFFER, and it is no longer a side condition on
       the line: [getcmd] reads at most [sh_nbuf - 1] bytes, and
       [EchoDisc.line_ok] admits exactly the lines shorter than
       [line_max], which IS [sh_nbuf] ([sh_nbuf_line_max]). *)
    assert (Hnble : sh_nbuf = sh_nbuf) by reflexivity.
    iIntros "#Hdp #Hlaw #Hplaw #Hrest #Hcode #Hjt #Hgen".
    iLöb as "IH".
    iIntros (h m f n0) "%Hregs %Hfd0 Hstd HR Hbs Hrun".
    set (n := (ush_Dbody + n0)%nat).
    pose proof Hregs as (Hs2 & Hs3 & Hs4 & Hs5 & Hs6).
    (* ---- 0x938  c.mv a1,s3 ---- *)
    iApply (wp_uk_cmv N h m (mword_of_int 0x938) a1_idx s3_idx
              (mword_of_int 100) (16 + n)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs3 moi_add_zero_l; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_938 with "Hcode"). }
    assert (E938 : add_vec_int (mword_of_int 0x938 : mword 64) 2
                   = mword_of_int 0x93a)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E938. iIntros (h1) "Hrun".
    set (m1 := <[Regidx a1_idx
                 := regval_into_reg (mword_of_int 100 : mword 64)]> m).
    assert (Hr1 : ush_regs m1)
      by exact (ush_regs_upd m a1_idx _ Hregs ltac:(vm_compute; reflexivity)).
    assert (Ha1_1 : m1 !!! Regidx a1_idx = mword_of_int 100)
      by exact (upd_eq m (Regidx a1_idx)
                  (regval_into_reg (mword_of_int 100 : mword 64))).
    pose proof Hr1 as (Hs2_1 & _ & _ & _ & _).
    (* ---- 0x93a  c.mv a0,s2 ---- *)
    iApply (wp_uk_cmv N h1 m1 (mword_of_int 0x93a) a0_idx s2_idx
              (mword_of_int sh_buf) (16 + n)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs2_1 moi_add_zero_l; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_93a with "Hcode"). }
    assert (E93a : add_vec_int (mword_of_int 0x93a : mword 64) 2
                   = mword_of_int 0x93c)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E93a. iIntros (h2) "Hrun".
    set (m2 := <[Regidx a0_idx
                 := regval_into_reg (mword_of_int sh_buf : mword 64)]> m1).
    assert (Hr2 : ush_regs m2)
      by exact (ush_regs_upd m1 a0_idx _ Hr1 ltac:(vm_compute; reflexivity)).
    assert (Ha0_2 : m2 !!! Regidx a0_idx = mword_of_int sh_buf)
      by exact (upd_eq m1 (Regidx a0_idx)
                  (regval_into_reg (mword_of_int sh_buf : mword 64))).
    assert (Ha1_2 : m2 !!! Regidx a1_idx = mword_of_int 100).
    { rewrite (upd_ne m1 (Regidx a0_idx) (Regidx a1_idx) _
                 ltac:(vm_compute; discriminate)). exact Ha1_1. }
    (* ---- 0x93c  jal ra,0x0 <getcmd> ---- *)
    iApply (wp_uk_jal N h2 m2 (mword_of_int 0x93c)
              (mword_of_int 2094788 : mword 21) ra_idx
              (mword_of_int ShSyms.getcmd) (mword_of_int 0x940) (16 + n)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite shp_getcmd; apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(rewrite shp_getcmd; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_93c with "Hcode"). }
    iIntros (h3) "Hrun".
    set (m3 := <[Regidx ra_idx
                 := regval_into_reg (mword_of_int 0x940 : mword 64)]> m2).
    assert (Hr3 : ush_regs m3)
      by exact (ush_regs_upd m2 ra_idx _ Hr2 ltac:(vm_compute; reflexivity)).
    assert (Hra3 : m3 !!! Regidx ra_idx = mword_of_int 0x940)
      by exact (upd_eq m2 (Regidx ra_idx)
                  (regval_into_reg (mword_of_int 0x940 : mword 64))).
    assert (Ha0_3 : m3 !!! Regidx a0_idx = mword_of_int sh_buf).
    { rewrite (upd_ne m2 (Regidx ra_idx) (Regidx a0_idx) _
                 ltac:(vm_compute; discriminate)). exact Ha0_2. }
    assert (Ha1_3 : m3 !!! Regidx a1_idx = mword_of_int (Z.of_nat sh_nbuf)).
    { rewrite Hnbz.
      rewrite (upd_ne m2 (Regidx ra_idx) (Regidx a1_idx) _
                 ltac:(vm_compute; discriminate)). exact Ha1_2. }
    replace (16 + n)%nat with (4 + (12 + n))%nat by lia.
    (* THE LEDGER AND THE POSITION GO INTO getcmd, because the READ inside
       it is what spends them (lane SH-LINE 2b, R1'); the working
       directory and the children set stay here. *)
    iDestruct "Hstd" as "(Hustd & Hcwd & Hch & Hpid & Hpos)".
    iApply (wp_ksh_getcmd h3 m3 sh_buf sh_nbuf f l n Ha0_3 Ha1_3
              Hnble ltac:(rewrite Hnbz; unfold Z31; lia)
              Hfd0
              with "Hdp Hlaw Hplaw Hcode Hbs Hustd Hpos Hrun").
    iIntros (h4 mR g i2) "%Hgi %HcsR %Ha0m Hbs Hustd Hpos Hrun".
    replace (4 + (12 + n))%nat with (16 + n)%nat by lia.
    rewrite Hra3.
    assert (Er940 : ret_pc (mword_of_int 0x940 : mword 64) = mword_of_int 0x940)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Er940.
    destruct Hgi as [Hi2lt Hnul].
    assert (HrR : ush_regs mR) by exact (ush_regs_cs m3 mR Hr3 HcsR).
    pose proof HrR as (Hs2_R & Hs3_R & Hs4_R & Hs5_R & Hs6_R).
    (* ---- 0x940  bltz a0,0x9ca -- an ABSTRACT split ---- *)
    remember (uv_btaken BLT (mR !!! Regidx a0_idx) zero_reg) as tk40 eqn:Htk40.
    iApply (wp_uk_btype0 N h4 mR (mword_of_int 0x940)
              (mword_of_int 138 : mword 13) a0_idx BLT tk40
              (mword_of_int 0x9ca) (16 + n)
              Htk40
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(intros _; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_940 with "Hcode"). }
    destruct tk40.
    (* sh's OWN exit: the payload it owes its parent is the lease it has
       been carrying since its entry (lane KILL-PAY, K4(a)) *)
    { iIntros (h5) "Hrun".
      (* THE PAYLOAD, off whichever arm left: nothing read, or the taint.
         A LINE READ is refuted here (lane EXEC-SEAM, (C)): its first byte
         is 'e', so getcmd answered 0 and this branch was not taken. *)
      iAssert ush_pos with "[Hpos]" as "Hpos".
      { rewrite /ush_gets_done_at.
        iDestruct "Hpos" as "[[_ $] | [Hl | [_ $]]]".
        iDestruct "Hl" as (lu) "[%Hl _]".
        exfalso. destruct Hl as [_ [_ Hli]].
        assert (Hg0 : g 0%nat <> ubyte0).
        { pose proof (proj2 (proj2 Hli) 0%nat
                        ltac:(rewrite (proj1 (proj2 Hli));
                              exact (ush_uline_bytes_pos lu))) as Hb0.
          rewrite Nat.add_0_r in Hb0. rewrite Hb0.
          exact (ush_uline_no_nul lu 0%nat (proj1 Hli)
                   (ush_uline_bytes_pos lu)). }
        assert (Hz : uv_btaken BLT (mword_of_int 0 : mword 64)
                       (zero_reg : mword 64) = false)
          by (vm_compute; reflexivity).
        rewrite (proj2 Ha0m Hg0) Hz in Htk40. discriminate Htk40. }
      iDestruct (ush_pos_pay with "Hpos") as "Hpay".
      iApply (wp_ksh_die h5 mR (16 + n) with "Hcode Hpay Hrun"). }
    assert (E940 : add_vec_int (mword_of_int 0x940 : mword 64) 4
                   = mword_of_int 0x944)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E940. iIntros (h5) "Hrun".
    (* THE LINE, OFF THE RECEIPT (lane IO-LEAF, M5(3)).  [gets] leaves
       either nothing read or exactly one line, and "nothing read" is
       precisely the arm getcmd answers [-1] on -- which this branch is
       NOT at.  So what is left is the line itself, or the taint; the line
       fact is PURE, so it rides the rest of the turn persistently while
       the cursor goes back into the process state. *)
    iAssert (∃ lu : FileDisc.uline,
               ((⌜Dl lu /\ i2 = length (FileDisc.line_bytes lu)
                  /\ ush_line_at lu g 0%nat i2⌝ ∨ T)
                ∗ ush_posw l (FileDisc.uline_ws lu)))%I
      with "[Hpos]" as (lu) "[#Hline Hpos]".
    { rewrite /ush_gets_done_at.
      iDestruct "Hpos" as "[[%H0 Hp] | [Hl | [#HT Hp]]]"; last first.
      - iExists (FileDisc.LEcho []). iSplitR; [ iRight; iExact "HT" | ].
        iApply (ush_posw_taint l _ with "HT Hp").
      - iDestruct "Hl" as (lu) "[%Hl Hp]".
        iExists lu. iFrame "Hp". iLeft. iPureIntro. exact Hl.
      - (* nothing was read: then buf[0] is the NUL and getcmd answered -1,
           so this branch is the exit's and not this one *)
        exfalso.
        assert (Hg0 : g 0%nat = ubyte0) by (rewrite <- H0; exact Hnul).
        assert (Hm1 : uv_btaken BLT (mword_of_int (-1) : mword 64)
                        (zero_reg : mword 64) = true)
          by (vm_compute; reflexivity).
        rewrite (proj1 Ha0m Hg0) Hm1 in Htk40. discriminate Htk40. }
    set (ws := FileDisc.uline_ws lu).
    iAssert (ush_bstate l ws) with "[Hustd Hcwd Hch Hpid Hpos]" as "Hstd".
    { rewrite /ush_bstate. iFrame "Hustd Hcwd Hch Hpid Hpos". }
    (* ---- 0x944  lbu a5,0(s2) -- the FIRST byte of the line ---- *)
    set (bz0 := bv_unsigned (g 0%nat)).
    assert (Hbz0r : 0 <= bz0 < 256).
    { unfold bz0. pose proof (bv_unsigned_in_range 8 (g 0%nat)) as Hr8.
      assert (Em8 : bv_modulus 8 = 256) by (vm_compute; reflexivity).
      rewrite Em8 in Hr8. exact Hr8. }
    iDestruct (ush_bytes_at (DfracOwn 1) sh_buf sh_nbuf 0%nat g
                 ltac:(rewrite Hnb; lia) with "Hbs") as "[Hb Hcl]".
    rewrite Z.add_0_r.
    iApply (wp_uk_lbu N h5 mR (mword_of_int 0x944)
              (mword_of_int 0 : mword 12) s2_idx a5_idx (DfracOwn 1)
              sh_buf (g 0%nat) (16 + n)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(rewrite Hs2_R (uint_moi sh_buf
                                     ltac:(rewrite Hbf; unfold Z64; lia));
                    vm_compute uoff_i12; lia)
              ltac:(vm_compute; discriminate)
              with "[] Hb Hrun").
    { iApply (uis_shk_944 with "Hcode"). }
    iIntros "Hb". iDestruct ("Hcl" with "Hb") as "Hbs".
    assert (E944 : add_vec_int (mword_of_int 0x944 : mword 64) 4
                   = mword_of_int 0x948)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E944. iIntros (h6) "Hrun".
    set (m4 := <[Regidx a5_idx
                 := regval_into_reg (zero_extend' 64 (g 0%nat : mword 8)
                                     : mword 64)]> mR).
    assert (Hr4 : ush_regs m4)
      by exact (ush_regs_upd mR a5_idx _ HrR ltac:(vm_compute; reflexivity)).
    assert (Ha5_4 : m4 !!! Regidx a5_idx = mword_of_int bz0).
    { rewrite (upd_eq mR (Regidx a5_idx)
                 (regval_into_reg (zero_extend' 64 (g 0%nat : mword 8)
                                   : mword 64))).
      exact (zext8_moi (g 0%nat)). }
    (* ---- 0x948  addi a4,a5,-32 ---- *)
    iApply (wp_uk_addi N h6 m4 (mword_of_int 0x948)
              (mword_of_int 4064 : mword 12) a5_idx a4_idx
              (mword_of_int (bz0 - 32)) (16 + n)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha5_4;
                    exact (ush_addi_sub bz0 32 (mword_of_int 4064 : mword 12)
                             ltac:(unfold Z64; lia)
                             ltac:(vm_compute; reflexivity)))
              with "[] Hrun").
    { iApply (uis_shk_948 with "Hcode"). }
    assert (E948 : add_vec_int (mword_of_int 0x948 : mword 64) 4
                   = mword_of_int 0x94c)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E948. iIntros (h7) "Hrun".
    set (m5 := <[Regidx a4_idx
                 := regval_into_reg (mword_of_int (bz0 - 32) : mword 64)]> m4).
    assert (Hr5 : ush_regs m5)
      by exact (ush_regs_upd m4 a4_idx _ Hr4 ltac:(vm_compute; reflexivity)).
    assert (Ha4_5 : m5 !!! Regidx a4_idx = mword_of_int (bz0 - 32))
      by exact (upd_eq m4 (Regidx a4_idx)
                  (regval_into_reg (mword_of_int (bz0 - 32) : mword 64))).
    assert (Ha5_5 : m5 !!! Regidx a5_idx = mword_of_int bz0).
    { rewrite (upd_ne m4 (Regidx a4_idx) (Regidx a5_idx) _
                 ltac:(vm_compute; discriminate)). exact Ha5_4. }
    (* ---- 0x94c  c.beqz a4,0x95c -- a leading SPACE ---- *)
    assert (Htk4c : Z.eqb bz0 32 = eq_vec (m5 !!! Regidx a4_idx) zero_reg).
    { rewrite Ha4_5. symmetry.
      exact (ush_eqz_sub bz0 32 ltac:(unfold Z64; lia)
               ltac:(unfold Z64; lia)). }
    iApply (wp_uk_cbeqz N h7 m5 (mword_of_int 0x94c)
              (mword_of_int 8 : mword 8) (mword_of_int 6 : mword 3) a4_idx
              (Z.eqb bz0 32) (mword_of_int 0x95c) (16 + n)
              ltac:(vm_compute; reflexivity) Htk4c
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(intros _; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_94c with "Hcode"). }
    (* the two ways into the scan and the one way past it all reconverge on
       a shared tail, so state it once *)
    (* SPATIAL, NOT [□], and that is forced.  The tail rounds the command
       loop on the blank-line arm, which needs the two inherited descriptor
       handles -- and a [□] assertion is proved with the spatial context
       CLEARED, so a persistent tail could never hold them.  The three uses
       below sit in mutually exclusive branches, so one copy is all any run
       of sh can need. *)
    iAssert (∀ (hh : CpuId) (mm : regfile) (kk : nat),
                  ⌜ ush_regs mm ⌝ -∗
                  ⌜ (kk <= i2)%nat ⌝ -∗
                  ⌜ mm !!! Regidx s1_idx
                      = mword_of_int (sh_buf + Z.of_nat kk) ⌝ -∗
                  ⌜ mm !!! Regidx a5_idx
                      = mword_of_int (bv_unsigned (g kk)) ⌝ -∗
                  ush_rest_line_at Dl ws g kk -∗
                  ubytes γd sh_buf sh_nbuf g -∗
                  urun N hh mm (mword_of_int 0x976) (16 + n) -∗
                  mWP (Loop : expr riscv_lang))%I with "[Hstd HR]" as "Htail".
    { iIntros (hh mm kk) "%Hrm %Hkk %Hsm %Ham #Hrl Hbs Hrun".
      pose proof Hrm as (_ & _ & Hs4m & _ & _).
      remember (uv_btaken BEQ (mm !!! Regidx a5_idx) (mm !!! Regidx s4_idx))
        as tk76 eqn:Htk76.
      iApply (UkRunLeaf.wp_uk_btype_later N hh mm (mword_of_int 0x976)
                (mword_of_int 8130 : mword 13) s4_idx a5_idx BEQ tk76
                (mword_of_int 0x938) (16 + n)
                Htk76
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(intros _; vm_compute; reflexivity)
                with "[] Hrun").
      { iApply (uis_shk_976 with "Hcode"). }
      destruct tk76.
      { (* a blank line: round the command loop again *)
        iNext. iIntros (hh1) "Hrun".
        iApply ("IH" $! hh1 mm g n0 with "[%] [%] [Hstd] HR Hbs Hrun");
          [ exact Hrm | exact Hfd0
          | iApply (ush_pstate_of_bstate l ws with "Hstd") ]. }
      iNext.
      assert (E976 : add_vec_int (mword_of_int 0x976 : mword 64) 4
                     = mword_of_int 0x97a)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite E976. iIntros (hh1) "Hrun".
      iDestruct ("Hrest" $! l with "[%] [%] [%] Hcode Hjt Hgen IH") as "Hbody";
        [ exact Hpay | exact ush_pm_of_at | exact ush_at_of_pm_wb | ].
      iApply ("Hbody" $! hh1 mm g kk i2 n0 ws
                with "[] [] [] [] [] Hrl Hstd HR Hbs Hrun");
        iPureIntro; [ exact Hrm | exact Hsm | exact Ham
                    | split; [ lia | exact Hnul ] | exact Hfd0 ]. }
    (* the two auipc/addi pairs that both land s1 on the buffer *)
    destruct (Z.eqb_spec bz0 32) as [Hb32 | Hb32].
    { (* leading space: straight to 0x95c *)
      iIntros (h8) "Hrun".
      assert (Hi20 : (0 < i2)%nat).
      { destruct (Nat.eq_dec i2 0) as [Hz | Hne]; [ | lia ].
        exfalso. unfold bz0 in Hb32. rewrite Hz in Hnul.
        rewrite Hnul in Hb32. vm_compute in Hb32. discriminate Hb32. }
      (* A LEADING BLANK IS THE TAINT'S, at any line: an admissible line
         runs /echo, so its first byte is 'e'
         ([EchoDisc.line_ok_head_byte0]). *)
      iAssert T as "#HTb".
      { iDestruct "Hline" as "[%Hl | $]".
        exfalso. destruct Hl as [_ [_ Hli]].
        pose proof (proj2 (proj2 Hli) 0%nat
                      ltac:(rewrite (proj1 (proj2 Hli));
                            exact (ush_uline_bytes_pos lu))) as Hg0.
        rewrite Nat.add_0_r in Hg0.
        pose proof (ush_uline_head_nonblank lu (proj1 Hli)) as Hhnb.
        rewrite <- Hg0 in Hhnb. unfold bz0 in *. lia. }
      iApply (wp_ksh_blank_entry h8 m5 g ws i2 n Hr5 Hi20 Hi2lt Hnul
                with "Hcode HTb Htail Hbs Hrun"). }
    assert (E94c : add_vec_int (mword_of_int 0x94c : mword 64) 2
                   = mword_of_int 0x94e)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E94c. iIntros (h8) "Hrun".
    (* ---- 0x94e  addi a4,a5,-9 ---- *)
    iApply (wp_uk_addi N h8 m5 (mword_of_int 0x94e)
              (mword_of_int 4087 : mword 12) a5_idx a4_idx
              (mword_of_int (bz0 - 9)) (16 + n)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha5_5;
                    exact (ush_addi_sub bz0 9 (mword_of_int 4087 : mword 12)
                             ltac:(unfold Z64; lia)
                             ltac:(vm_compute; reflexivity)))
              with "[] Hrun").
    { iApply (uis_shk_94e with "Hcode"). }
    assert (E94e : add_vec_int (mword_of_int 0x94e : mword 64) 4
                   = mword_of_int 0x952)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E94e. iIntros (h9) "Hrun".
    set (m6 := <[Regidx a4_idx
                 := regval_into_reg (mword_of_int (bz0 - 9) : mword 64)]> m5).
    assert (Hr6 : ush_regs m6)
      by exact (ush_regs_upd m5 a4_idx _ Hr5 ltac:(vm_compute; reflexivity)).
    assert (Ha5_6 : m6 !!! Regidx a5_idx = mword_of_int bz0).
    { rewrite (upd_ne m5 (Regidx a4_idx) (Regidx a5_idx) _
                 ltac:(vm_compute; discriminate)). exact Ha5_5. }
    assert (Ha4_6 : m6 !!! Regidx a4_idx = mword_of_int (bz0 - 9))
      by exact (upd_eq m5 (Regidx a4_idx)
                  (regval_into_reg (mword_of_int (bz0 - 9) : mword 64))).
    (* ---- 0x952/0x956  auipc+addi: s1 := buf ---- *)
    iApply (wp_uk_auipc N h9 m6 (mword_of_int 0x952)
              (mword_of_int 1 : mword 20) s1_idx
              (add_vec (mword_of_int 0x952 : mword 64)
                 (auipc_off (mword_of_int 1 : mword 20))) (16 + n)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) eq_refl
              with "[] Hrun").
    { iApply (uis_shk_952 with "Hcode"). }
    assert (E952 : add_vec_int (mword_of_int 0x952 : mword 64) 4
                   = mword_of_int 0x956)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E952. iIntros (h10) "Hrun".
    set (m7 := <[Regidx s1_idx
                 := regval_into_reg
                      (add_vec (mword_of_int 0x952 : mword 64)
                         (auipc_off (mword_of_int 1 : mword 20)))]> m6).
    assert (Hr7 : ush_regs m7)
      by exact (ush_regs_upd m6 s1_idx _ Hr6 ltac:(vm_compute; reflexivity)).
    assert (Ha4_7 : m7 !!! Regidx a4_idx = mword_of_int (bz0 - 9)).
    { rewrite (upd_ne m6 (Regidx s1_idx) (Regidx a4_idx) _
                 ltac:(vm_compute; discriminate)). exact Ha4_6. }
    assert (Ha5_7 : m7 !!! Regidx a5_idx = mword_of_int bz0).
    { rewrite (upd_ne m6 (Regidx s1_idx) (Regidx a5_idx) _
                 ltac:(vm_compute; discriminate)). exact Ha5_6. }
    iApply (wp_uk_addi N h10 m7 (mword_of_int 0x956)
              (mword_of_int 1742 : mword 12) s1_idx s1_idx
              (mword_of_int sh_buf) (16 + n)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (upd_eq m6 (Regidx s1_idx)
                               (regval_into_reg
                                  (add_vec (mword_of_int 0x952 : mword 64)
                                     (auipc_off (mword_of_int 1 : mword 20)))));
                    apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_956 with "Hcode"). }
    assert (E956 : add_vec_int (mword_of_int 0x956 : mword 64) 4
                   = mword_of_int 0x95a)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E956. iIntros (h11) "Hrun".
    set (m8 := <[Regidx s1_idx
                 := regval_into_reg (mword_of_int sh_buf : mword 64)]> m7).
    assert (Hr8 : ush_regs m8)
      by exact (ush_regs_upd m7 s1_idx _ Hr7 ltac:(vm_compute; reflexivity)).
    assert (Hs1_8 : m8 !!! Regidx s1_idx = mword_of_int (sh_buf + Z.of_nat 0)).
    { replace (sh_buf + Z.of_nat 0) with sh_buf by lia.
      exact (upd_eq m7 (Regidx s1_idx)
               (regval_into_reg (mword_of_int sh_buf : mword 64))). }
    assert (Ha4_8 : m8 !!! Regidx a4_idx = mword_of_int (bz0 - 9)).
    { rewrite (upd_ne m7 (Regidx s1_idx) (Regidx a4_idx) _
                 ltac:(vm_compute; discriminate)). exact Ha4_7. }
    assert (Ha5_8 : m8 !!! Regidx a5_idx = mword_of_int bz0).
    { rewrite (upd_ne m7 (Regidx s1_idx) (Regidx a5_idx) _
                 ltac:(vm_compute; discriminate)). exact Ha5_7. }
    (* ---- 0x95a  c.bnez a4,0x976 -- not a TAB either: done scanning ---- *)
    assert (Htk5a : negb (Z.eqb bz0 9)
                    = neq_vec (m8 !!! Regidx a4_idx) zero_reg).
    { rewrite Ha4_8. symmetry.
      exact (ush_neqz_sub bz0 9 ltac:(unfold Z64; lia)
               ltac:(unfold Z64; lia)). }
    iApply (wp_uk_cbnez N h11 m8 (mword_of_int 0x95a)
              (mword_of_int 14 : mword 8) (mword_of_int 6 : mword 3) a4_idx
              (negb (Z.eqb bz0 9)) (mword_of_int 0x976) (16 + n)
              ltac:(vm_compute; reflexivity) Htk5a
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(intros _; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_95a with "Hcode"). }
    destruct (Z.eqb_spec bz0 9) as [Hb9 | Hb9].
    { (* a leading tab: fall into 0x95c and scan *)
      cbn [negb]. iIntros (h12) "Hrun".
      assert (E95a : add_vec_int (mword_of_int 0x95a : mword 64) 2
                     = mword_of_int 0x95c)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite E95a.
      assert (Hi20 : (0 < i2)%nat).
      { destruct (Nat.eq_dec i2 0) as [Hz | Hne]; [ | lia ].
        exfalso. unfold bz0 in Hb9. rewrite Hz in Hnul.
        rewrite Hnul in Hb9. vm_compute in Hb9. discriminate Hb9. }
      (* A LEADING BLANK IS THE TAINT'S, at any line: an admissible line
         runs /echo, so its first byte is 'e'
         ([EchoDisc.line_ok_head_byte0]). *)
      iAssert T as "#HTb".
      { iDestruct "Hline" as "[%Hl | $]".
        exfalso. destruct Hl as [_ [_ Hli]].
        pose proof (proj2 (proj2 Hli) 0%nat
                      ltac:(rewrite (proj1 (proj2 Hli));
                            exact (ush_uline_bytes_pos lu))) as Hg0.
        rewrite Nat.add_0_r in Hg0.
        pose proof (ush_uline_head_nonblank lu (proj1 Hli)) as Hhnb.
        rewrite <- Hg0 in Hhnb. unfold bz0 in *. lia. }
      iApply (wp_ksh_blank_entry h12 m8 g ws i2 n Hr8 Hi20 Hi2lt Hnul
                with "Hcode HTb Htail Hbs Hrun"). }
    cbn [negb]. iIntros (h12) "Hrun".
    iApply ("Htail" $! h12 m8 0%nat with "[] [] [] [] [] Hbs Hrun");
      [ iPureIntro; exact Hr8 | iPureIntro; lia | iPureIntro; exact Hs1_8
      | iPureIntro; rewrite Ha5_8; reflexivity | ].
    (* THE LINE STARTS AT 0 on this arm: the first byte is neither a space
       nor a tab, so the blank scan never ran. *)
    rewrite /ush_rest_line_at.
    iDestruct "Hline" as "[%Hl | #HT]"; [ | iRight; iExact "HT" ].
    iLeft. iIntros (len) "%Hne %Hnl". iPureIntro.
    (* THE CONSTRUCTOR THE ECHO ERA ADMITS (lane SH-CHILD): the payload is
       "some admissible line of the discipline", and this era's is
       [LEcho ws] -- [ush_line_echo_of_is] is the whole of the widening's
       cost on this side. *)
    (* THE CONSTRUCTOR THE ERA ADMITS is the one the loop already carries
       (lane LINK-GEN-6): the payload names it, so the widening costs the
       producer a [exists lu] and nothing else. *)
    exists lu.
    destruct Hl as [HD [Hi17 [Hok [_ Hby]]]].
    split; [ exact HD | ]. split; [ reflexivity | ].
    (* THE NUL THE SCAN FOUND IS THE LINE'S END: no byte of a line is a NUL
       ([ush_uline_no_nul]), and the one [gets] planted sits just past it. *)
    assert (Hle : (len = i2)%nat).
    { destruct (Nat.lt_trichotomy len i2) as [Hlt | [He | Hgt]];
        [ | exact He | ].
      - exfalso. rewrite Nat.add_0_l in Hnl. rewrite (Hby len Hlt) in Hnl.
        exact (ush_uline_no_nul lu len Hok
                 ltac:(rewrite <- Hi17; exact Hlt) Hnl).
      - exfalso. apply (Hne i2 ltac:(lia)).
        rewrite Nat.add_0_l. exact Hnul. }
    rewrite /ush_line_at. split; [ exact Hok | ].
    split; [ rewrite Hle; exact Hi17 | ].
    intros j Hj. apply Hby. lia.
  Qed.

  (* ===================================================================== *)
  (* 0x914..0x92a -- THE LOOP'S SETUP, and what stage 1 left open.          *)
  (*                                                                       *)
  (* Six instructions load the five constants the loop runs on: the buffer  *)
  (* address (an auipc/addi pair), its size, and the three character        *)
  (* literals for newline, 'c' and space.  main's frame is dead from here   *)
  (* on -- main does not return (0x9cc is a [jal exit]), so the eight words *)
  (* its prologue spilled are never reloaded -- which is why nothing about  *)
  (* the entry register file survives into the loop and the invariant is    *)
  (* exactly [ush_regs] plus the buffer.                                    *)
  (*                                                                       *)
  (* DEPENDS ON [ush_read_leaf] (through the loop).                         *)
  (* ===================================================================== *)
  Lemma wp_ksh_cmd_head (R : iProp Σ) (h : CpuId) (m : regfile)
      (f : nat -> bv 8) (n0 : nat) (l : list fdstate) :
    □ (T -∗ sh_deps) -∗
    ush_tag_law -∗
    ush_prompt_law -∗
    ush_rest_l_at Dl R -∗
    shk_code γt -∗
    ush_jtab γt -∗
    ush_gen_slot -∗
    ⌜ ush_fd0p l ⌝ -∗
    ush_pstate l -∗
    R -∗
    ubytes γd sh_buf sh_nbuf f -∗
    urun N h m (mword_of_int 0x914) (16 + (ush_Dbody + n0)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using Hdsc_ncr Hdsc_line Hdsc_short HT Hpay ush_at_of_pm_taint ush_at_of_pm_wb ush_pm_of_at ush_read_leaf ush_wb_read ush_wc_blk_line ush_wc_read.
    iIntros "#Hdp #Hlaw #Hplaw #Hrest #Hcode #Hjt #Hgen %Hfd0 Hstd HR Hbs Hrun".
    set (n := (ush_Dbody + n0)%nat).
    (* ---- 0x914  li s3,100 ---- *)
    iApply (wp_uk_li N h m (mword_of_int 0x914)
              (mword_of_int 100 : mword 12) s3_idx (mword_of_int 100) (16 + n)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(assert (E : (sign_extend' 64 (mword_of_int 100 : mword 12)
                                 : mword 64) = mword_of_int 100)
                      by (apply bv_eq; vm_compute; reflexivity);
                    rewrite E moi_add_zero_l; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_914 with "Hcode"). }
    assert (E914 : add_vec_int (mword_of_int 0x914 : mword 64) 4
                   = mword_of_int 0x918)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E914. iIntros (h1) "Hrun".
    set (m1 := <[Regidx s3_idx
                 := regval_into_reg (mword_of_int 100 : mword 64)]> m).
    (* ---- 0x918/0x91c  auipc+addi: s2 := the buffer's address ---- *)
    iApply (wp_uk_auipc N h1 m1 (mword_of_int 0x918)
              (mword_of_int 1 : mword 20) s2_idx
              (add_vec (mword_of_int 0x918 : mword 64)
                 (auipc_off (mword_of_int 1 : mword 20))) (16 + n)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) eq_refl
              with "[] Hrun").
    { iApply (uis_shk_918 with "Hcode"). }
    assert (E918 : add_vec_int (mword_of_int 0x918 : mword 64) 4
                   = mword_of_int 0x91c)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E918. iIntros (h2) "Hrun".
    set (m2 := <[Regidx s2_idx
                 := regval_into_reg
                      (add_vec (mword_of_int 0x918 : mword 64)
                         (auipc_off (mword_of_int 1 : mword 20)))]> m1).
    iApply (wp_uk_addi N h2 m2 (mword_of_int 0x91c)
              (mword_of_int 1800 : mword 12) s2_idx s2_idx
              (mword_of_int sh_buf) (16 + n)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (upd_eq m1 (Regidx s2_idx)
                               (regval_into_reg
                                  (add_vec (mword_of_int 0x918 : mword 64)
                                     (auipc_off (mword_of_int 1 : mword 20)))));
                    apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_91c with "Hcode"). }
    assert (E91c : add_vec_int (mword_of_int 0x91c : mword 64) 4
                   = mword_of_int 0x920)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E91c. iIntros (h3) "Hrun".
    set (m3 := <[Regidx s2_idx
                 := regval_into_reg (mword_of_int sh_buf : mword 64)]> m2).
    (* ---- 0x920  c.li s4,10 ---- *)
    iApply (wp_uk_cli N h3 m3 (mword_of_int 0x920)
              (mword_of_int 10 : mword 6) s4_idx (16 + n)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) with "[] Hrun").
    { iApply (uis_shk_920 with "Hcode"). }
    assert (Em920 : <[Regidx s4_idx
                      := regval_into_reg (sign_extend' 64
                                            (mword_of_int 10 : mword 6)
                                          : mword 64)]> m3
                    = <[Regidx s4_idx
                        := regval_into_reg (mword_of_int 10 : mword 64)]> m3)
      by (f_equal; apply bv_eq; vm_compute; reflexivity).
    assert (E920 : add_vec_int (mword_of_int 0x920 : mword 64) 2
                   = mword_of_int 0x922)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Em920 E920. iIntros (h4) "Hrun".
    set (m4 := <[Regidx s4_idx
                 := regval_into_reg (mword_of_int 10 : mword 64)]> m3).
    (* ---- 0x922  li s5,99 ---- *)
    iApply (wp_uk_li N h4 m4 (mword_of_int 0x922)
              (mword_of_int 99 : mword 12) s5_idx (mword_of_int 99) (16 + n)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(assert (E : (sign_extend' 64 (mword_of_int 99 : mword 12)
                                 : mword 64) = mword_of_int 99)
                      by (apply bv_eq; vm_compute; reflexivity);
                    rewrite E moi_add_zero_l; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_922 with "Hcode"). }
    assert (E922 : add_vec_int (mword_of_int 0x922 : mword 64) 4
                   = mword_of_int 0x926)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E922. iIntros (h5) "Hrun".
    set (m5 := <[Regidx s5_idx
                 := regval_into_reg (mword_of_int 99 : mword 64)]> m4).
    (* ---- 0x926  li s6,32 ---- *)
    iApply (wp_uk_li N h5 m5 (mword_of_int 0x926)
              (mword_of_int 32 : mword 12) s6_idx (mword_of_int 32) (16 + n)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(assert (E : (sign_extend' 64 (mword_of_int 32 : mword 12)
                                 : mword 64) = mword_of_int 32)
                      by (apply bv_eq; vm_compute; reflexivity);
                    rewrite E moi_add_zero_l; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_926 with "Hcode"). }
    assert (E926 : add_vec_int (mword_of_int 0x926 : mword 64) 4
                   = mword_of_int 0x92a)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E926. iIntros (h6) "Hrun".
    set (m6 := <[Regidx s6_idx
                 := regval_into_reg (mword_of_int 32 : mword 64)]> m5).
    (* ---- 0x92a  c.j 0x938 ---- *)
    iApply (wp_uk_cj N h6 m6 (mword_of_int 0x92a)
              (mword_of_int 7 : mword 11) (mword_of_int 0x938) (16 + n)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_92a with "Hcode"). }
    iIntros (h7) "Hrun".
    assert (Hregs : ush_regs m6).
    { split_and!.
      - rewrite (upd_ne m5 (Regidx s6_idx) (Regidx s2_idx) _
                   ltac:(vm_compute; discriminate)).
        rewrite (upd_ne m4 (Regidx s5_idx) (Regidx s2_idx) _
                   ltac:(vm_compute; discriminate)).
        rewrite (upd_ne m3 (Regidx s4_idx) (Regidx s2_idx) _
                   ltac:(vm_compute; discriminate)).
        exact (upd_eq m2 (Regidx s2_idx)
                 (regval_into_reg (mword_of_int sh_buf : mword 64))).
      - rewrite (upd_ne m5 (Regidx s6_idx) (Regidx s3_idx) _
                   ltac:(vm_compute; discriminate)).
        rewrite (upd_ne m4 (Regidx s5_idx) (Regidx s3_idx) _
                   ltac:(vm_compute; discriminate)).
        rewrite (upd_ne m3 (Regidx s4_idx) (Regidx s3_idx) _
                   ltac:(vm_compute; discriminate)).
        rewrite (upd_ne m2 (Regidx s2_idx) (Regidx s3_idx) _
                   ltac:(vm_compute; discriminate)).
        rewrite (upd_ne m1 (Regidx s2_idx) (Regidx s3_idx) _
                   ltac:(vm_compute; discriminate)).
        exact (upd_eq m (Regidx s3_idx)
                 (regval_into_reg (mword_of_int 100 : mword 64))).
      - rewrite (upd_ne m5 (Regidx s6_idx) (Regidx s4_idx) _
                   ltac:(vm_compute; discriminate)).
        rewrite (upd_ne m4 (Regidx s5_idx) (Regidx s4_idx) _
                   ltac:(vm_compute; discriminate)).
        exact (upd_eq m3 (Regidx s4_idx)
                 (regval_into_reg (mword_of_int 10 : mword 64))).
      - rewrite (upd_ne m5 (Regidx s6_idx) (Regidx s5_idx) _
                   ltac:(vm_compute; discriminate)).
        exact (upd_eq m4 (Regidx s5_idx)
                 (regval_into_reg (mword_of_int 99 : mword 64))).
      - exact (upd_eq m5 (Regidx s6_idx)
                 (regval_into_reg (mword_of_int 32 : mword 64))). }
    iDestruct (wp_ksh_loop R l with "Hdp Hlaw Hplaw Hrest Hcode Hjt Hgen")
      as "Hhead".
    iApply ("Hhead" $! h7 m6 f n0 with "[%] [%] Hstd HR Hbs Hrun");
      [ exact Hregs | exact Hfd0 ].
  Qed.

  (* THE BRANCH THAT SAYS THE DESCRIPTOR IS NOT A STANDARD STREAM.  s1
     holds O_RDWR = 2 across the console preamble, so [bge s1,a0] is taken
     exactly when what open returned is at most 2 -- which is every
     descriptor the ledger itself can name, the ledger being NSTD long. *)
  Local Lemma ush_bge_std (k : nat) :
    (k < NSTD)%nat ->
    uv_btaken BGE (mword_of_int 2 : mword 64)
      (mword_of_int (Z.of_nat k) : mword 64) = true.
  Proof using .
    intro Hk. unfold NSTD in Hk. cbn [uv_btaken].
    rewrite (moi_ge_s 2 (Z.of_nat k) ltac:(unfold Z63; lia)
               ltac:(unfold Z63; lia)).
    apply Z.geb_le. lia.
  Qed.

  (* ===================================================================== *)
  (* THE CONSOLE PREAMBLE, 0x900..0x910 -- the loop, under iLöb.            *)
  (*                                                                       *)
  (*   0x900  c.mv a1,s1        ; a1 := O_RDWR                             *)
  (*   0x902  c.mv a0,s2        ; a0 := &"console"                         *)
  (*   0x904  jal ra,0xcc6      ; open                                     *)
  (*   0x908  bltz a0,0x914     ; open failed: leave the loop              *)
  (*   0x90c  bge s1,a0,0x900   ; fd <= 2: go round again  <-- BACK EDGE   *)
  (*   0x910  jal ra,0xcae      ; close(fd), then fall into 0x914          *)
  (*                                                                       *)
  (* THIS IS THE ONE PLACE IN SH THAT LOOKS AT THE SHAPE OF THE LEDGER,     *)
  (* and what it is doing is xv6's own repair of a closed standard stream.  *)
  (* So the induction generalises over the LEDGER as well as the register   *)
  (* file, and the command loop is entered at whatever the last open left.  *)
  (*                                                                       *)
  (* THE TWO BRANCHES STAY ABSTRACT, and what closes the walk is that the   *)
  (* fall-through of BOTH of them wants a HANDLE for the descriptor in a0.  *)
  (* Three things can have come back and only the third reaches 0x910:      *)
  (* open failed (a0 = -1, so the [bltz] at 0x908 was taken); the           *)
  (* descriptor landed on a closed standard stream, so a0 <= 2 and the      *)
  (* [bge] against s1 at 0x90c was taken; or it landed above them, which    *)
  (* is [UserFd.ualloc_at]'s [None] arm and hands over exactly the handle   *)
  (* the close spends.  The first two are arithmetic on a0, which is why    *)
  (* s1's value is a premise here: the walk decides the branch rather than  *)
  (* carrying a resource for every way it could go.                         *)
  (* ===================================================================== *)
  (* THE STATE OF THE CONSOLE NODE RIDES THE BACK EDGE, and the row the
     entry was told rides it beside: [ush_fd0] is a LOOP INVARIANT here
     ([ush_fd0_cons]), which is what lets the command loop be entered with
     the row at the ledger the preamble LEFT rather than at the one it
     started from. *)
  Local Lemma wp_ksh_console (R K : iProp Σ) (h : CpuId) (m : regfile)
      (f : nat -> bv 8) (n0 : nat) (l : list fdstate) :
    □ (T -∗ sh_deps) -∗
    ush_tag_law -∗
    ush_prompt_law -∗
    ush_rest_l_at Dl R -∗
    shk_code γt -∗
    ush_jtab γt -∗
    shk_rodata γt -∗
    ush_gen_slot -∗
    ⌜m !!! Regidx s1_idx = (mword_of_int 2 : mword 64)⌝ -∗
    ⌜m !!! Regidx s2_idx = (mword_of_int sh_cons_pv : mword 64)⌝ -∗
    ⌜ ush_fd0p l ⌝ -∗
    ush_cons_in K -∗
    ush_std l -∗
    UserCwd.ucwd γcwd FsImg.ROOTINO -∗
    UserChildren.uch γch ∅ -∗
    ush_pid -∗
    ush_posb l 0%nat -∗
    R -∗
    ubytes γd sh_buf sh_nbuf f -∗
    urun N h m (mword_of_int 0x900) (16 + (ush_Dbody + n0)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using Hdsc_ncr Hdsc_line Hdsc_short HT Hpay ush_at_of_pm_taint ush_at_of_pm_wb ush_pm_of_at ush_read_leaf ush_wb_read ush_wb_wc ush_wc_blk_line ush_wc_read.
    iIntros "#Hdp #Hlaw #Hplaw #Hrest #Hcode #Hjt #Hro #Hgen".
    set (n := (16 + (ush_Dbody + n0))%nat).
    iLöb as "IH" forall (h m l).
    iIntros "%Hs1 %Hs2 %Hfd0 Hin Hstd Hcwd Hch Hpid Hpos HR Hbs Hrun".
    (* ---- 0x900  c.mv a1,s1 ---- *)
    iApply (wp_uk_cmv N h m (mword_of_int 0x900) a1_idx s1_idx
              (add_vec zero_reg (m !!! Regidx s1_idx)) n
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) eq_refl
              with "[] Hrun").
    { iApply (uis_shk_900 with "Hcode"). }
    assert (E900 : add_vec_int (mword_of_int 0x900 : mword 64) 2
                   = mword_of_int 0x902)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E900. iIntros (h1) "Hrun".
    set (mA := <[Regidx a1_idx
                 := regval_into_reg (add_vec zero_reg (m !!! Regidx s1_idx))]> m).
    (* ---- 0x902  c.mv a0,s2 ---- *)
    iApply (wp_uk_cmv N h1 mA (mword_of_int 0x902) a0_idx s2_idx
              (add_vec zero_reg (mA !!! Regidx s2_idx)) n
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) eq_refl
              with "[] Hrun").
    { iApply (uis_shk_902 with "Hcode"). }
    assert (E902 : add_vec_int (mword_of_int 0x902 : mword 64) 2
                   = mword_of_int 0x904)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E902. iIntros (h2) "Hrun".
    set (mB := <[Regidx a0_idx
                 := regval_into_reg (add_vec zero_reg (mA !!! Regidx s2_idx))]> mA).
    (* ---- 0x904  jal ra,0xcc6 <open> ---- *)
    iApply (wp_uk_jal N h2 mB (mword_of_int 0x904)
              (mword_of_int 962 : mword 21) ra_idx
              (mword_of_int ShSyms.open) (mword_of_int 0x908) n
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite shp_open; apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(rewrite shp_open; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_904 with "Hcode"). }
    iIntros (h3) "Hrun".
    set (mC := <[Regidx ra_idx
                 := regval_into_reg (mword_of_int 0x908 : mword 64)]> mB).
    assert (HraC : mC !!! Regidx ra_idx = mword_of_int 0x908)
      by exact (upd_eq mB (Regidx ra_idx) (mword_of_int 0x908 : mword 64)).
    (* THE TWO ARGUMENT WORDS THE PINNED OPEN IS ABOUT: a0 is the address
       of sh's own "console" literal (0x1388, [UCodeShK.shk_ro]) and a1 is
       O_RDWR.  Both are read off the two [c.mv]s just walked. *)
    assert (Hs2A : mA !!! Regidx s2_idx = (mword_of_int sh_cons_pv : mword 64)).
    { rewrite /mA (upd_ne m (Regidx a1_idx) (Regidx s2_idx) _
                     ltac:(vm_compute; discriminate)). exact Hs2. }
    assert (Ha0C : mC !!! Regidx a0_idx = (mword_of_int sh_cons_pv : mword 64)).
    { rewrite /mC (upd_ne mB (Regidx ra_idx) (Regidx a0_idx) _
                     ltac:(vm_compute; discriminate)).
      rewrite /mB (upd_eq mA (Regidx a0_idx) _) Hs2A.
      apply bv_eq; vm_compute; reflexivity. }
    assert (Ha1C : mC !!! Regidx a1_idx = (mword_of_int 2 : mword 64)).
    { rewrite /mC (upd_ne mB (Regidx ra_idx) (Regidx a1_idx) _
                     ltac:(vm_compute; discriminate)).
      rewrite /mB (upd_ne mA (Regidx a0_idx) (Regidx a1_idx) _
                     ltac:(vm_compute; discriminate)).
      rewrite /mA (upd_eq m (Regidx a1_idx) _) Hs1.
      apply bv_eq; vm_compute; reflexivity. }
    assert (HalC : is_aligned_vaddr
                     (Virtaddr (ret_pc (mC !!! Regidx ra_idx))) 2 = true)
      by (rewrite HraC; vm_compute; reflexivity).
    iApply (ush_cons_open K h3 mC l n Ha0C Ha1C HalC
              with "Hcode Hro Hgen Hrun Hcwd Hstd Hin").
    (* WHAT CAME BACK, PUT IN THE FORM THE TWO BRANCHES CONSUME: the ledger
       the open left -- AND THE ROW, which is the pin's work: an allocation
       lands at [fd_lowest_closed], so a closed slot 0 IS where it lands and
       what it installs is the console device ([ush_fd0_cons]).  Then either
       the handle (the descriptor landed above the standard streams,
       [UserFd.ualloc_at]'s [None] arm) or a pure fact about a0 that refutes
       the fall-through of one of the two branches. *)
    iIntros (h4 ret) "Hal Hin Hcwd Hrun".
    iAssert (∃ l' : list fdstate,
               ush_std l' ∗ ⌜ush_fd0p l'⌝ ∗
               ush_posb l' 0%nat ∗
               ((∃ fd : nat,
                   ⌜ret = (mword_of_int (Z.of_nat fd) : mword 64)
                    /\ (fd < NOFILE)%nat⌝ ∗
                   ufd γfd fd (FdOpen true true (FdDevice CONSOLE)))
                ∨ ⌜ret = (mword_of_int (-1) : mword 64)
                   \/ (exists k : nat,
                         ret = (mword_of_int (Z.of_nat k) : mword 64)
                         /\ (k < NSTD)%nat)⌝))%I
      with "[Hal Hpos]" as "(%l' & Hstd & %Hfd0' & Hpos & Hfdh)".
    { iDestruct "Hal" as "[Hal | [%Hrm Hstd]]".
      - iDestruct "Hal" as (fd) "[%Hr Hal]".
        destruct (fd_lowest_closed l) as [k |] eqn:Hk.
        + iDestruct (ush_ualloc_std l fd k
                       (FdOpen true true (FdDevice CONSOLE)) Hk with "Hal")
            as "[%Hfk Hstd]".
          iDestruct (ush_std_len with "Hstd") as %Hlen.
          rewrite length_insert in Hlen.
          iExists (<[k := FdOpen true true (FdDevice CONSOLE)]> l).
          iFrame "Hstd".
          iSplitR; [ iPureIntro; exact (ush_fd0p_cons l k Hlen Hk Hfd0) | ].
          iSplitL "Hpos";
            [ iApply (ush_posb_cons l k Hlen Hk with "Hpos") | ].
          iRight. iPureIntro. right. exists k.
          split; [ rewrite <- Hfk; exact (proj1 Hr) | ].
          rewrite <- Hlen. exact (fd_lowest_closed_bound l k Hk).
        + iDestruct (ush_ualloc_hi l fd
                       (FdOpen true true (FdDevice CONSOLE)) Hk with "Hal")
            as "(_ & Hstd & Hh)".
          iExists l. iFrame "Hstd".
          iSplitR; [ by iPureIntro | ].
          iFrame "Hpos".
          iLeft. iExists fd. iFrame "Hh". iPureIntro. exact Hr.
      - iExists l. iFrame "Hstd". iSplitR; [ by iPureIntro | ].
        iFrame "Hpos".
        iRight. iPureIntro. left. exact Hrm. }
    rewrite HraC.
    assert (Eret : ret_pc (mword_of_int 0x908 : mword 64) = mword_of_int 0x908)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Eret.
    set (mD := <[Regidx a0_idx := ret]>
                 (<[Regidx a7_idx := (mword_of_int 15 : mword 64)]> mC)).
    (* s1 and s2 survive the round: the preamble writes a1, a0, ra and a7
       and nothing else, so O_RDWR is still there at the 0x90c test and the
       literal's address is still there at 0x902 on the next turn. *)
    assert (Hs1D : mD !!! Regidx s1_idx = (mword_of_int 2 : mword 64)).
    { rewrite /mD (upd_ne (<[Regidx a7_idx := (mword_of_int 15 : mword 64)]> mC)
                     (Regidx a0_idx) (Regidx s1_idx) _
                     ltac:(vm_compute; discriminate)).
      rewrite (upd_ne mC (Regidx a7_idx) (Regidx s1_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite /mC (upd_ne mB (Regidx ra_idx) (Regidx s1_idx) _
                     ltac:(vm_compute; discriminate)).
      rewrite /mB (upd_ne mA (Regidx a0_idx) (Regidx s1_idx) _
                     ltac:(vm_compute; discriminate)).
      rewrite /mA (upd_ne m (Regidx a1_idx) (Regidx s1_idx) _
                     ltac:(vm_compute; discriminate)).
      exact Hs1. }
    assert (Hs2D : mD !!! Regidx s2_idx = (mword_of_int sh_cons_pv : mword 64)).
    { rewrite /mD (upd_ne (<[Regidx a7_idx := (mword_of_int 15 : mword 64)]> mC)
                     (Regidx a0_idx) (Regidx s2_idx) _
                     ltac:(vm_compute; discriminate)).
      rewrite (upd_ne mC (Regidx a7_idx) (Regidx s2_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite /mC (upd_ne mB (Regidx ra_idx) (Regidx s2_idx) _
                     ltac:(vm_compute; discriminate)).
      rewrite /mB (upd_ne mA (Regidx a0_idx) (Regidx s2_idx) _
                     ltac:(vm_compute; discriminate)).
      exact Hs2A. }
    (* ---- 0x908  bltz a0,0x914 ---- *)
    remember (uv_btaken BLT (mD !!! Regidx a0_idx) zero_reg) as t1 eqn:Ht1.
    iApply (wp_uk_btype0 N h4 mD (mword_of_int 0x908)
              (mword_of_int 12 : mword 13) a0_idx BLT t1 (mword_of_int 0x914) n
              Ht1
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(intros _; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_908 with "Hcode"). }
    destruct t1.
    { (* the loop is left, at whatever ledger the open left behind -- and at
         the row that ledger satisfies *)
      iIntros (h5) "Hrun".
      iApply (wp_ksh_cmd_head R h5 mD f n0 l'
                with "Hdp Hlaw Hplaw Hrest Hcode Hjt Hgen [%]
                      [Hstd Hcwd Hch Hpid Hpos] HR Hbs Hrun");
        [ exact Hfd0' | ].
      rewrite /ush_pstate. iFrame "Hstd Hcwd Hch Hpid Hpos". }
    assert (E908 : add_vec_int (mword_of_int 0x908 : mword 64) 4
                   = mword_of_int 0x90c)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E908. iIntros (h5) "Hrun".
    (* ---- 0x90c  bge s1,a0,0x900 -- THE BACK EDGE ---- *)
    remember (uv_btaken BGE (mD !!! Regidx s1_idx) (mD !!! Regidx a0_idx))
      as t2 eqn:Ht2.
    iApply (UkRunLeaf.wp_uk_btype_later N h5 mD (mword_of_int 0x90c)
              (mword_of_int 8180 : mword 13) a0_idx s1_idx BGE t2
              (mword_of_int 0x900) n
              Ht2
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(intros _; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_90c with "Hcode"). }
    destruct t2.
    { (* fd <= 2 -- round again, on the Löb hypothesis, at the new ledger,
         the new row and the console state that came back *)
      iNext. iIntros (h6) "Hrun".
      iApply ("IH" $! h6 mD l' with "[%] [%] [%] Hin Hstd Hcwd Hch Hpid Hpos
                                      HR Hbs Hrun");
        [ exact Hs1D | exact Hs2D | exact Hfd0' ]. }
    iNext.
    assert (E90c : add_vec_int (mword_of_int 0x90c : mword 64) 4
                   = mword_of_int 0x910)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E90c. iIntros (h6) "Hrun".
    (* ---- 0x910  jal ra,0xcae <close> ---- *)
    iApply (wp_uk_jal N h6 mD (mword_of_int 0x910)
              (mword_of_int 926 : mword 21) ra_idx
              (mword_of_int ShSyms.close) (mword_of_int 0x914) n
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite shp_close; apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(rewrite shp_close; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_910 with "Hcode"). }
    iIntros (h7) "Hrun".
    set (mE := <[Regidx ra_idx
                 := regval_into_reg (mword_of_int 0x914 : mword 64)]> mD).
    assert (HraE : mE !!! Regidx ra_idx = mword_of_int 0x914)
      by exact (upd_eq mD (Regidx ra_idx) (mword_of_int 0x914 : mword 64)).
    (* SH REACHES THIS CLOSE ONLY HOLDING A HANDLE.  Both branches fell
       through, and each refutes one of the two ways the open could have
       come back without one: [-1] would have taken the [bltz] at 0x908,
       and a descriptor at or below 2 would have taken the [bge] against
       s1 = O_RDWR at 0x90c.  What is left is the descriptor that landed
       above the standard streams, and a0 still holds it ([ra] is the only
       register written since). *)
    assert (Ha0D : mD !!! Regidx a0_idx = ret)
      by exact (upd_eq _ (Regidx a0_idx) ret).
    iDestruct "Hfdh" as "[(%fd & [%Hretfd %Hfdlt] & Hh) | %Hbad]";
      [ | exfalso; destruct Hbad as [Hretm1 | (k & Hretk & Hklt)];
          [ rewrite Ha0D Hretm1 in Ht1; vm_compute in Ht1; discriminate Ht1
          | rewrite Hs1D Ha0D Hretk (ush_bge_std k Hklt) in Ht2;
            discriminate Ht2 ] ].
    assert (Ha0E : bv_signed (trunc32 (mE !!! Regidx a0_idx)) = Z.of_nat fd).
    { rewrite /mE (upd_ne mD (Regidx ra_idx) (Regidx a0_idx) _
                     ltac:(vm_compute; discriminate)) Ha0D Hretfd
              trunc32_mword_of_int.
      assert (Hbw : bv_wrap 32 (Z.of_nat fd) = Z.of_nat fd)
        by (apply bvw32_small; unfold NOFILE in Hfdlt; lia).
      unfold bv_signed. rewrite moi32_unsigned Hbw.
      apply bv_swrap_small.
      assert (Hh32 : bv_half_modulus 32 = 2147483648%Z)
        by (vm_compute; reflexivity).
      rewrite Hh32. unfold NOFILE in Hfdlt. lia. }
    iApply (wp_ksh_close h7 mE fd (FdOpen true true (FdDevice CONSOLE)) n Ha0E
              ltac:(intros ? ? ?; discriminate)
              with "Hcode Hrun Hh").
    iIntros (h8 ret2) "Hrun".
    rewrite HraE.
    assert (Eret2 : ret_pc (mword_of_int 0x914 : mword 64) = mword_of_int 0x914)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Eret2.
    iApply (wp_ksh_cmd_head R h8 _ f n0 l'
              with "Hdp Hlaw Hplaw Hrest Hcode Hjt Hgen [%]
                    [Hstd Hcwd Hch Hpid Hpos] HR Hbs Hrun");
      [ exact Hfd0' | ].
    rewrite /ush_pstate. iFrame "Hstd Hcwd Hch Hpid Hpos".
  Qed.


  (* ===================================================================== *)
  (* main -- the prologue and the preamble's setup.                         *)
  (*                                                                       *)
  (* Eight words of frame (ra and s0..s6), spilled and never reloaded:      *)
  (* main never returns.  0x8f6..0x8fc load O_RDWR and the address of the   *)
  (* "console" literal, and 0x900 is the loop above.                        *)
  (* ===================================================================== *)
  Lemma wp_ksh_main (R K : iProp Σ) (h : CpuId) (m : regfile)
      (f : nat -> bv 8) (n0 : nat) (l : list fdstate) :
    □ (T -∗ sh_deps) -∗
    ush_tag_law -∗
    ush_prompt_law -∗
    ush_rest_l_at Dl R -∗
    shk_code γt -∗
    ush_jtab γt -∗
    shk_rodata γt -∗
    ush_gen_slot -∗
    ⌜ ush_fd0p l ⌝ -∗
    ush_cons_in K -∗
    (* THE PROCESS STATE, SPLIT: the console preamble is the one walk in sh
       that needs the WORKING DIRECTORY AT A NAMED INUM (a pin is about a
       path), so the cwd comes in at [FsImg.ROOTINO] here and is weakened to
       [UserCwd.ucwd_any] at the command loop, which is all [cd] needs. *)
    ush_std l -∗
    UserCwd.ucwd γcwd FsImg.ROOTINO -∗
    UserChildren.uch γch ∅ -∗
    ush_pid -∗
    ush_posb l 0%nat -∗
    R -∗
    ubytes γd sh_buf sh_nbuf f -∗
    urun N h m (mword_of_int ShSyms.main)
      (8 + (16 + (ush_Dbody + n0))) -∗
    mWP (Loop : expr riscv_lang).
  Proof using Hdsc_ncr Hdsc_line Hdsc_short HT Hpay ush_at_of_pm_taint ush_at_of_pm_wb ush_pm_of_at ush_read_leaf ush_wb_read ush_wb_wc ush_wc_blk_line ush_wc_read.
    iIntros "#Hdp #Hlaw #Hplaw #Hrest #Hcode #Hjt #Hro #Hgen %Hfd0 Hin Hstd Hcwd Hch Hpid Hpos
             HR Hbs Hrun".
    set (n := (16 + (ush_Dbody + n0))%nat).
    rewrite shp_main.
    iDestruct (urun_stack with "Hrun") as %[Hal8' Hroom].
    remember (m !!! Regidx csp_rs1) as sp0 eqn:Hsp0.
    assert (Hsp : m !!! Regidx csp_rs1 = sp0) by (symmetry; exact Hsp0).
    clear Hsp0.
    assert (Hal8 : uint sp0 mod 8 = 0) by exact Hal8'.
    assert (Hlo : 64 <= uint sp0) by lia.
    assert (Hbsp : bv_unsigned (add_vec_int sp0 (- (8 * Z.of_nat 8)))
                   = bv_unsigned sp0 - 64).
    { replace (- (8 * Z.of_nat 8)) with (-64) by lia.
      exact (uv_avi_neg sp0 64 ltac:(lia) ltac:(rewrite <- uint_unsigned; lia)). }
    assert (Hsp64 : uint (add_vec_int sp0 (- (8 * Z.of_nat 8)))
                    = uint sp0 - 64)
      by (rewrite !uint_unsigned; exact Hbsp).
    assert (Ho0 : uoff_sdsp (mword_of_int 0 : mword 6) = 0)
      by (vm_compute; reflexivity).
    assert (Ho1 : uoff_sdsp (mword_of_int 1 : mword 6) = 8)
      by (vm_compute; reflexivity).
    assert (Ho2 : uoff_sdsp (mword_of_int 2 : mword 6) = 16)
      by (vm_compute; reflexivity).
    assert (Ho3 : uoff_sdsp (mword_of_int 3 : mword 6) = 24)
      by (vm_compute; reflexivity).
    assert (Ho4 : uoff_sdsp (mword_of_int 4 : mword 6) = 32)
      by (vm_compute; reflexivity).
    assert (Ho5 : uoff_sdsp (mword_of_int 5 : mword 6) = 40)
      by (vm_compute; reflexivity).
    assert (Ho6 : uoff_sdsp (mword_of_int 6 : mword 6) = 48)
      by (vm_compute; reflexivity).
    assert (Ho7 : uoff_sdsp (mword_of_int 7 : mword 6) = 56)
      by (vm_compute; reflexivity).
    (* ---- 0x8e2  c.addi16sp sp,sp,-64 -- THE PUSH ---- *)
    iApply (wp_uk_caddi16sp_dn N h m (mword_of_int 0x8e2)
              (mword_of_int 60 : mword 6) 8 n
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_8e2 with "Hcode"). }
    assert (E8e2 : add_vec_int (mword_of_int 0x8e2 : mword 64) 2
                   = mword_of_int 0x8e4)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Hsp ustack_8 E8e2.
    iIntros "(_ & [%v1 Hw1] & [%v2 Hw2] & [%v3 Hw3] & [%v4 Hw4]
              & [%v5 Hw5] & [%v6 Hw6] & [%v7 Hw7] & [%v8 Hw8])".
    iIntros (hs0) "Hrun".
    set (mA := <[Regidx csp_rs1
                 := regval_into_reg (add_vec_int sp0 (- (8 * Z.of_nat 8)))]> m).
    assert (HspA : mA !!! Regidx csp_rs1
                   = add_vec_int sp0 (- (8 * Z.of_nat 8)))
      by exact (upd_eq m (Regidx csp_rs1)
                  (regval_into_reg (add_vec_int sp0 (- (8 * Z.of_nat 8))))).
    (* ---- 0x8e4  c.sdsp ra,56(sp) ---- *)
    iApply (wp_uk_csdsp N hs0 mA (mword_of_int 0x8e4)
              (mword_of_int 7 : mword 6) ra_idx (uint sp0 - 8) v1 n
              ltac:(rewrite HspA Hsp64 Ho7; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              with "[] Hw1 Hrun").
    { iApply (uis_shk_8e4 with "Hcode"). }
    iIntros "Hw1".
    assert (Es0 : add_vec_int (mword_of_int 0x8e4 : mword 64) 2
                  = mword_of_int 0x8e6)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Es0. iIntros (hs1) "Hrun".
    (* ---- 0x8e6  c.sdsp s0,48(sp) ---- *)
    iApply (wp_uk_csdsp N hs1 mA (mword_of_int 0x8e6)
              (mword_of_int 6 : mword 6) s0_idx (uint sp0 - 16) v2 n
              ltac:(rewrite HspA Hsp64 Ho6; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              with "[] Hw2 Hrun").
    { iApply (uis_shk_8e6 with "Hcode"). }
    iIntros "Hw2".
    assert (Es1 : add_vec_int (mword_of_int 0x8e6 : mword 64) 2
                  = mword_of_int 0x8e8)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Es1. iIntros (hs2) "Hrun".
    (* ---- 0x8e8  c.sdsp s1,40(sp) ---- *)
    iApply (wp_uk_csdsp N hs2 mA (mword_of_int 0x8e8)
              (mword_of_int 5 : mword 6) s1_idx (uint sp0 - 24) v3 n
              ltac:(rewrite HspA Hsp64 Ho5; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              with "[] Hw3 Hrun").
    { iApply (uis_shk_8e8 with "Hcode"). }
    iIntros "Hw3".
    assert (Es2 : add_vec_int (mword_of_int 0x8e8 : mword 64) 2
                  = mword_of_int 0x8ea)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Es2. iIntros (hs3) "Hrun".
    (* ---- 0x8ea  c.sdsp s2,32(sp) ---- *)
    iApply (wp_uk_csdsp N hs3 mA (mword_of_int 0x8ea)
              (mword_of_int 4 : mword 6) s2_idx (uint sp0 - 32) v4 n
              ltac:(rewrite HspA Hsp64 Ho4; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              with "[] Hw4 Hrun").
    { iApply (uis_shk_8ea with "Hcode"). }
    iIntros "Hw4".
    assert (Es3 : add_vec_int (mword_of_int 0x8ea : mword 64) 2
                  = mword_of_int 0x8ec)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Es3. iIntros (hs4) "Hrun".
    (* ---- 0x8ec  c.sdsp s3,24(sp) ---- *)
    iApply (wp_uk_csdsp N hs4 mA (mword_of_int 0x8ec)
              (mword_of_int 3 : mword 6) s3_idx (uint sp0 - 40) v5 n
              ltac:(rewrite HspA Hsp64 Ho3; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              with "[] Hw5 Hrun").
    { iApply (uis_shk_8ec with "Hcode"). }
    iIntros "Hw5".
    assert (Es4 : add_vec_int (mword_of_int 0x8ec : mword 64) 2
                  = mword_of_int 0x8ee)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Es4. iIntros (hs5) "Hrun".
    (* ---- 0x8ee  c.sdsp s4,16(sp) ---- *)
    iApply (wp_uk_csdsp N hs5 mA (mword_of_int 0x8ee)
              (mword_of_int 2 : mword 6) s4_idx (uint sp0 - 48) v6 n
              ltac:(rewrite HspA Hsp64 Ho2; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              with "[] Hw6 Hrun").
    { iApply (uis_shk_8ee with "Hcode"). }
    iIntros "Hw6".
    assert (Es5 : add_vec_int (mword_of_int 0x8ee : mword 64) 2
                  = mword_of_int 0x8f0)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Es5. iIntros (hs6) "Hrun".
    (* ---- 0x8f0  c.sdsp s5,8(sp) ---- *)
    iApply (wp_uk_csdsp N hs6 mA (mword_of_int 0x8f0)
              (mword_of_int 1 : mword 6) s5_idx (uint sp0 - 56) v7 n
              ltac:(rewrite HspA Hsp64 Ho1; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              with "[] Hw7 Hrun").
    { iApply (uis_shk_8f0 with "Hcode"). }
    iIntros "Hw7".
    assert (Es6 : add_vec_int (mword_of_int 0x8f0 : mword 64) 2
                  = mword_of_int 0x8f2)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Es6. iIntros (hs7) "Hrun".
    (* ---- 0x8f2  c.sdsp s6,0(sp) ---- *)
    iApply (wp_uk_csdsp N hs7 mA (mword_of_int 0x8f2)
              (mword_of_int 0 : mword 6) s6_idx (uint sp0 - 64) v8 n
              ltac:(rewrite HspA Hsp64 Ho0; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              with "[] Hw8 Hrun").
    { iApply (uis_shk_8f2 with "Hcode"). }
    iIntros "Hw8".
    assert (Es7 : add_vec_int (mword_of_int 0x8f2 : mword 64) 2
                  = mword_of_int 0x8f4)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Es7. iIntros (hs8) "Hrun".
    (* ---- 0x8f4  c.addi4spn s0,sp,64 (s0 is dead: main never returns) ---- *)
    iApply (wp_uk_caddi4spn N hs8 mA (mword_of_int 0x8f4)
              (mword_of_int 0 : mword 3) (mword_of_int 16 : mword 8) s0_idx
              (add_vec (mA !!! Regidx csp_rs1)
                 (sign_extend' 64
                    (caddi4spn_imm (mword_of_int 16 : mword 8)))) n
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
              eq_refl
              with "[] Hrun").
    { iApply (uis_shk_8f4 with "Hcode"). }
    assert (E8f4 : add_vec_int (mword_of_int 0x8f4 : mword 64) 2
                   = mword_of_int 0x8f6)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E8f4. iIntros (hb) "Hrun".
    set (mB := <[Regidx s0_idx
                 := regval_into_reg
                      (add_vec (mA !!! Regidx csp_rs1)
                         (sign_extend' 64
                            (caddi4spn_imm (mword_of_int 16 : mword 8))))]> mA).
    (* ---- 0x8f6  c.li s1,2  (O_RDWR) ---- *)
    iApply (wp_uk_cli N hb mB (mword_of_int 0x8f6)
              (mword_of_int 2 : mword 6) s1_idx n
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) with "[] Hrun").
    { iApply (uis_shk_8f6 with "Hcode"). }
    assert (E8f6 : add_vec_int (mword_of_int 0x8f6 : mword 64) 2
                   = mword_of_int 0x8f8)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E8f6. iIntros (hc) "Hrun".
    set (mC := <[Regidx s1_idx
                 := regval_into_reg (sign_extend' 64 (mword_of_int 2 : mword 6)
                                     : mword 64)]> mB).
    (* ---- 0x8f8  auipc s2,0x1 ---- *)
    iApply (wp_uk_auipc N hc mC (mword_of_int 0x8f8)
              (mword_of_int 1 : mword 20) s2_idx
              (add_vec (mword_of_int 0x8f8 : mword 64)
                 (auipc_off (mword_of_int 1 : mword 20))) n
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) eq_refl
              with "[] Hrun").
    { iApply (uis_shk_8f8 with "Hcode"). }
    assert (E8f8 : add_vec_int (mword_of_int 0x8f8 : mword 64) 4
                   = mword_of_int 0x8fc)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E8f8. iIntros (hd) "Hrun".
    set (mD := <[Regidx s2_idx
                 := regval_into_reg
                      (add_vec (mword_of_int 0x8f8 : mword 64)
                         (auipc_off (mword_of_int 1 : mword 20)))]> mC).
    (* ---- 0x8fc  addi s2,s2,-1392  (&"console") ---- *)
    iApply (wp_uk_addi N hd mD (mword_of_int 0x8fc)
              (mword_of_int 2704 : mword 12) s2_idx s2_idx
              (add_vec (mD !!! Regidx s2_idx)
                 (sign_extend' 64 (mword_of_int 2704 : mword 12))) n
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) eq_refl
              with "[] Hrun").
    { iApply (uis_shk_8fc with "Hcode"). }
    assert (E8fc : add_vec_int (mword_of_int 0x8fc : mword 64) 4
                   = mword_of_int 0x900)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E8fc. iIntros (he) "Hrun".
    (* ---- 0x900  the console loop ---- *)
    (* s1 is O_RDWR from the [c.li] at 0x8f6, and the loop needs it: the
       [bge s1,a0] at 0x90c is what tells a descriptor above the standard
       streams from one that landed on a closed standard stream. *)
    iApply (wp_ksh_console R K he _ f n0 l
              with "Hdp Hlaw Hplaw Hrest Hcode Hjt Hro Hgen [] [] [%] Hin Hstd Hcwd Hch
                    Hpid Hpos HR Hbs Hrun");
      [ | | exact Hfd0 ].
    - (* s1 is O_RDWR, off the [c.li] at 0x8f6 *)
      iPureIntro.
      rewrite (upd_ne mD (Regidx s2_idx) (Regidx s1_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite /mD (upd_ne mC (Regidx s2_idx) (Regidx s1_idx) _
                     ltac:(vm_compute; discriminate)).
      rewrite /mC (upd_eq mB (Regidx s1_idx) _).
      apply bv_eq; vm_compute; reflexivity.
    - (* ...and s2 is the address of sh's own "console" literal, off the
         auipc/addi pair at 0x8f8/0x8fc: 0x8f8 + 0x1000 - 1392 = 0x1388
         ([ShData.sh_data] has "console\0" there, inside [UCodeShK.shk_ro]
         since 0x1388 < 0x2000). *)
      iPureIntro.
      rewrite (upd_eq mD (Regidx s2_idx) _).
      rewrite /mD (upd_eq mC (Regidx s2_idx) _).
      apply bv_eq; vm_compute; reflexivity.
  Qed.


  (* ===================================================================== *)
  (* start -- the ELF entry.  usys.S's crt: a two-word frame, then          *)
  (* main(), then exit() if it ever came back.  It does not: main's own     *)
  (* contract has no continuation, so 0x9dc is unreachable and never        *)
  (* appears here.  The [avail] arithmetic is the call chain spelled out:   *)
  (* start's two words and main's eight.                                    *)
  (* ===================================================================== *)
  Lemma wp_ksh_start (R K : iProp Σ) (h : CpuId) (m : regfile)
      (f : nat -> bv 8) (n0 : nat) (l : list fdstate) :
    □ (T -∗ sh_deps) -∗
    ush_tag_law -∗
    (* ...and the prompt's law at every line boundary (lane IO-LEAF,
       M6a(3)), from the entry ([UShKernel.sh_prompt_law]) *)
    ush_prompt_law -∗
    ush_rest_l_at Dl R -∗
    shk_code γt -∗
    (* runcmd's jump table, which the BODY needs and only the entry can
       produce ([ush_rest_l]'s header) *)
    ush_jtab γt -∗
    (* sh's own READ-ONLY IMAGE, which the pinned open needs: the path is a
       string in it ([UCodeShK.shk_ro] at 0x1388). *)
    shk_rodata γt -∗
    (* ...AND THE TAINT'S CONTINUATION.  sh's console open is PINNED, so at
       the taint there is no bundle to pay it with -- the preamble does not
       make the call, it hands the run to the generic slot. *)
    ush_gen_slot -∗
    (* THE ONE ROW THE ENTRY IS TOLD ABOUT, at its three arms ([ush_fd0]'s
       header).  It enters HERE, and the preamble PRESERVES it
       ([ush_fd0_cons]) so that the command loop is entered with the row at
       the ledger the preamble's own opens left.  Under the CONSOLE arm fd 0
       is the console device whether init's open succeeded or sh's did. *)
    ush_fd0 l -∗
    (* ...AND THE STATE OF THE CONSOLE NODE, which is what decides which of
       the two pinned opens the preamble makes (lane SH-OPEN, H1/H3). *)
    ush_cons_in K -∗
    ush_std l -∗
    UserCwd.ucwd γcwd FsImg.ROOTINO -∗
    UserChildren.uch γch ∅ -∗
    ush_pid -∗
    (* ...AND THE CURSOR WITH THE ERA'S CREDENTIAL BESIDE IT (step 3): this
       is where the era's credential enters sh -- /init lends the pieces
       and the credential at the fork, the child carries them across the
       exec ([PinnedExec]'s [Pay]) and the entry law
       ([UShLine.ush_posb_of_lend]) puts them into the loop's slot. *)
    ush_posb l 0%nat -∗
    R -∗
    ubytes γd sh_buf sh_nbuf f -∗
    urun N h m (mword_of_int ShSyms.start)
      (2 + (8 + (16 + (ush_Dbody + n0)))) -∗
    mWP (Loop : expr riscv_lang).
  Proof using Hdsc_ncr Hdsc_line Hdsc_short HT Hpay ush_at_of_pm_taint ush_at_of_pm_wb ush_pm_of_at ush_read_leaf ush_wb_read ush_wb_wc ush_wc_blk_line ush_wc_read.
    iIntros "#Hdp #Hlaw #Hplaw #Hrest #Hcode #Hjt #Hro #Hgen #Hfd0 Hin Hstd Hcwd Hch Hpid Hpos
             HR Hbs Hrun".
    (* THE TAINT ARM GOES GENERIC AT ONCE, and this is the ONE place it can:
       every walk below is sh's own code, and sh's console open is PINNED --
       under the taint there is no pin and no bundle to pay row 15 with.  So
       the row the command loop carries is the PURE one ([ush_fd0p]) and no
       statement below this line names the application at all. *)
    iDestruct "Hfd0" as "[%Hfd0 | #HT]"; last first.
    { assert (Halo : is_aligned_vaddr
                       (Virtaddr (mword_of_int ShSyms.start : mword 64)) 2
                     = true)
        by (rewrite shp_start; vm_compute; reflexivity).
      iApply (ush_gen_run h m (mword_of_int ShSyms.start)
                (2 + (8 + (16 + (ush_Dbody + n0)))) Halo
                with "Hgen HT Hrun"). }
    set (n := (16 + (ush_Dbody + n0))%nat).
    rewrite shp_start.
    iDestruct (urun_stack with "Hrun") as %[Hal8' Hroom].
    remember (m !!! Regidx csp_rs1) as sp0 eqn:Hsp0.
    assert (Hsp : m !!! Regidx csp_rs1 = sp0) by (symmetry; exact Hsp0).
    clear Hsp0.
    assert (Hal8 : uint sp0 mod 8 = 0) by exact Hal8'.
    assert (Hlo : 16 <= uint sp0) by lia.
    assert (Hbsp : bv_unsigned (add_vec_int sp0 (- (8 * Z.of_nat 2)))
                   = bv_unsigned sp0 - 16).
    { replace (- (8 * Z.of_nat 2)) with (-16) by lia.
      exact (uv_avi_neg sp0 16 ltac:(lia) ltac:(rewrite <- uint_unsigned; lia)). }
    assert (Hsp16 : uint (add_vec_int sp0 (- (8 * Z.of_nat 2)))
                    = uint sp0 - 16)
      by (rewrite !uint_unsigned; exact Hbsp).
    assert (Ho8 : uoff_sdsp (mword_of_int 1 : mword 6) = 8)
      by (vm_compute; reflexivity).
    assert (Ho0 : uoff_sdsp (mword_of_int 0 : mword 6) = 0)
      by (vm_compute; reflexivity).
    (* ---- 0x9d0  c.addi sp,sp,-16 ---- *)
    iApply (wp_uk_caddi_sp_dn N h m (mword_of_int 0x9d0)
              (mword_of_int 48 : mword 6) 2 (8 + n)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_9d0 with "Hcode"). }
    assert (E9d0 : add_vec_int (mword_of_int 0x9d0 : mword 64) 2
                   = mword_of_int 0x9d2)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Hsp ustack_2 E9d0.
    iIntros "(_ & [%v8 Hw8] & [%v0 Hw0])".
    iIntros (h1) "Hrun".
    set (m1 := <[Regidx csp_rs1
                 := regval_into_reg (add_vec_int sp0 (- (8 * Z.of_nat 2)))]> m).
    assert (Hsp1 : m1 !!! Regidx csp_rs1
                   = add_vec_int sp0 (- (8 * Z.of_nat 2)))
      by exact (upd_eq m (Regidx csp_rs1)
                  (regval_into_reg (add_vec_int sp0 (- (8 * Z.of_nat 2))))).
    (* ---- 0x9d2  c.sdsp ra,8(sp) ---- *)
    iApply (wp_uk_csdsp N h1 m1 (mword_of_int 0x9d2)
              (mword_of_int 1 : mword 6) ra_idx (uint sp0 - 8) v8 (8 + n)
              ltac:(rewrite Hsp1 Hsp16 Ho8; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              with "[] Hw8 Hrun").
    { iApply (uis_shk_9d2 with "Hcode"). }
    iIntros "Hw8".
    assert (E9d2 : add_vec_int (mword_of_int 0x9d2 : mword 64) 2
                   = mword_of_int 0x9d4)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E9d2. iIntros (h2) "Hrun".
    (* ---- 0x9d4  c.sdsp s0,0(sp) ---- *)
    iApply (wp_uk_csdsp N h2 m1 (mword_of_int 0x9d4)
              (mword_of_int 0 : mword 6) s0_idx (uint sp0 - 16) v0 (8 + n)
              ltac:(rewrite Hsp1 Hsp16 Ho0; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              with "[] Hw0 Hrun").
    { iApply (uis_shk_9d4 with "Hcode"). }
    iIntros "Hw0".
    assert (E9d4 : add_vec_int (mword_of_int 0x9d4 : mword 64) 2
                   = mword_of_int 0x9d6)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E9d4. iIntros (h3) "Hrun".
    (* ---- 0x9d6  c.addi4spn s0,sp,16 ---- *)
    iApply (wp_uk_caddi4spn N h3 m1 (mword_of_int 0x9d6)
              (mword_of_int 0 : mword 3) (mword_of_int 4 : mword 8) s0_idx
              (add_vec (m1 !!! Regidx csp_rs1)
                 (sign_extend' 64
                    (caddi4spn_imm (mword_of_int 4 : mword 8)))) (8 + n)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
              eq_refl
              with "[] Hrun").
    { iApply (uis_shk_9d6 with "Hcode"). }
    assert (E9d6 : add_vec_int (mword_of_int 0x9d6 : mword 64) 2
                   = mword_of_int 0x9d8)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E9d6. iIntros (h4) "Hrun".
    set (m2 := <[Regidx s0_idx
                 := regval_into_reg
                      (add_vec (m1 !!! Regidx csp_rs1)
                         (sign_extend' 64
                            (caddi4spn_imm (mword_of_int 4 : mword 8))))]> m1).
    (* ---- 0x9d8  jal ra,0x8e2 <main> ---- *)
    iApply (wp_uk_jal N h4 m2 (mword_of_int 0x9d8)
              (mword_of_int 2096906 : mword 21) ra_idx
              (mword_of_int ShSyms.main) (mword_of_int 0x9dc) (8 + n)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite shp_main; apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(rewrite shp_main; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_9d8 with "Hcode"). }
    iIntros (h5) "Hrun".
    (* ---- main(), which never returns ---- *)
    (* [ShSyms.main] is what the jal's target already is, so this only ever
       had work to do while the wide catalog destruct was dumping unused
       [uinstr_is] hypotheses holding the literal into the context. *)
    rewrite <- ?shp_main.
    iApply (wp_ksh_main R K h5 _ f n0 l
              with "Hdp Hlaw Hplaw Hrest Hcode Hjt Hro Hgen [%] Hin Hstd Hcwd Hch Hpid Hpos
                    HR Hbs Hrun").
    exact Hfd0.
  Qed.

End UkSh.

(* ===================================================================== *)
(* THE NARROWED COUNT, kept: the Hypothesis above takes a2 as the          *)
(* unsigned word equal to the buffer's size and every read leaf takes it   *)
(* as the C [int] the kernel narrows it to, so a discharge needs ONE bound *)
(* -- [Z.to_nat] of the narrowed count never exceeds the unsigned word --  *)
(* and it needs NO side condition on [k]: a negative narrow floors at zero *)
(* under [Z.to_nat], and a non-negative one IS the unsigned low half,      *)
(* which [mod] bounds by the whole word.                                   *)
(*                                                                        *)
(* THE DISCHARGE ITSELF IS NOT HERE ANY MORE (lane SH-LINE 2b phase 2,     *)
(* R1).  There were two copies of it -- this file's [ush_read_leaf_holds]  *)
(* and [UShKernel.ush_read_leaf_of_win], the same walk through             *)
(* [UkRunSys.wp_uk_ecall_read_win] at two spellings of the count -- and    *)
(* only the second was ever applied ([UShKernel.sh_uexec_slot]).  The one  *)
(* that survives the lane is neither: sh's read is a CONSOLE read, its     *)
(* deposit carries the reader token out of the exit payload rather than    *)
(* [sh_deps]' [UkRun.udepw_law 5], and the discharge of the                *)
(* receipt-keeping leaf is [UShLine.ush_read_recv_leaf_holds], which needs *)
(* the CONCRETE deposit bundle and so cannot live in this file at all.     *)
(* ===================================================================== *)

Lemma ush_narrow_count_le (w : mword 64) (k : nat) :
  uint w = Z.of_nat k ->
  (Z.to_nat (bv_signed (subrange_vec_dec w 31 0 : mword 32)) <= k)%nat.
Proof.
  intros Hu. rewrite uint_unsigned in Hu.
  pose proof (subrange_31_0_unsigned w) as Hlo.
  (* the signed reading, as the unsigned one shifted into the signed
     window -- convertibility does the modulus arithmetic *)
  assert (Hs : bv_signed (subrange_vec_dec w 31 0 : mword 32)
               = (bv_unsigned (subrange_vec_dec w 31 0 : mword 32)
                  + 2147483648) mod 4294967296 - 2147483648)
    by reflexivity.
  rewrite Hs Hlo.
  set (u := bv_unsigned w mod 4294967296).
  assert (Hub : 0 <= u < 4294967296)
    by (apply Z.mod_pos_bound; lia).
  assert (Hule : u <= bv_unsigned w)
    by (apply Z.mod_le; [ lia | lia ]).
  pose proof (Z.div_mod (u + 2147483648) 4294967296 ltac:(lia)) as Hdm.
  pose proof (Z.mod_pos_bound (u + 2147483648) 4294967296 ltac:(lia)) as Hmb.
  lia.
Qed.

