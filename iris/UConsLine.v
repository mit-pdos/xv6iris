(* ===================================================================== *)
(* UConsLine.v -- SH-LINE'S STATEMENTS: what the shell's line IS.          *)
(*                                                                        *)
(* The lane SH-LINE (app-echo.md, "SH-LINE RULING") makes sh's line buffer *)
(* carry "these are the consecutive next input bytes, at my position, each *)
(* tagged", and discharges [UkShFork.ushf_lexable] from it.  This file is  *)
(* PHASE 1 of that lane: every shape the rewiring has to hit, STATED and   *)
(* typechecked, and nothing rewired yet -- so a reviewer sees the target   *)
(* before the sweep, and the sweep has something to unify against.         *)
(*                                                                        *)
(*   §1  the ledger that knows fd 0 is the console          (design S4)    *)
(*   §2  sh's read leaf, with the receipt kept              (design S5)    *)
(*   §3  the [gets] loop's line invariant                   (design S5)    *)
(*   §4  the two PURE facts that discharge lexability       (design S6)    *)
(*   §5  init's LINEAR exec supply for the child it lends   (design S3)    *)
(*                                                                        *)
(* WHAT PHASE 1 FOUND, and why the rewiring is not in this file:           *)
(*                                                                        *)
(*  (a) THE EXIT PAYLOAD CROSSES exec (lane EXEC-PAY, landed).  A run's    *)
(*      payload [UkRun.ukn_pay N (-1)] lives INSIDE [UkRun.urun] and the   *)
(*      exec'd image's own run needs it ([UkRun.uslot_of_urun_all] takes   *)
(*      [Q (-1)] linearly), so no program can hand it over: it is the      *)
(*      KERNEL that carries it.  [SpecKexec.exec_slot_pre]'s two wands     *)
(*      take [Q (-1)] beside the pay fact, [SpecSyscall.sysc_exec_out]'s   *)
(*      success arm is a wand from [sexit_pay f (-1)] -- the payment the   *)
(*      dispatcher holds across the trap ([SpecSyscall.sysc_pay_in],       *)
(*      returned as [sysc_pay_out]) -- and the trap loop feeds that one    *)
(*      resource to whichever continuation it takes                        *)
(*      ([UexecApply.uexec_ret_round_slot]'s exec arm).  §5's supply       *)
(*      therefore names the POSITION only; the payload arrives at the      *)
(*      constructor wand ([PinnedExec.pex_slot]) from the seam.            *)
(*                                                                        *)
(*  (b) FD 0 IS NOT KNOWN TO BE THE CONSOLE from the leaves init has.      *)
(*      [UkRunSys.wp_uk_ecall_open]'s post existentially quantifies the    *)
(*      descriptor's TYPE ([SpecSysOpen.v:403] says why: it is [FdDevice]  *)
(*      exactly when the path walk observed a T_DEVICE inode), and that    *)
(*      leaf discards the process's post ([UkRunSys.v:785] binds           *)
(*      [spost_at] as [_]).  Switching init's two [dup]s to the tracked    *)
(*      leaf does not fix it: a dup copies whatever state the ledger       *)
(*      already records.  §1's ledger is therefore stated, and what it     *)
(*      needs is a PINNED OPEN bundle at "/console" -- [xv6_sbundle]'s     *)
(*      row 15 and [xv6_spost]'s row 15 already carry an observation       *)
(*      family and a receipt, so the shape exists; the builder and the     *)
(*      pin do not.                                                       *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_map ghost_var invariants.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExtras RiscvModelBytes ObsTrace.
Require Import RegFile.
Require Import UmodeArith.
Require Import UmodeAbi.       (* [ubyte0] -- the NUL [gets] plants *)
Require Import UsysMemOk.
Require Import UserHeap UkRun UkRunSys.
(* the address-space vocabulary the swallowed byte's FAULT arm is refuted
   in ([ush_swallow_nofault]): the permission projection and the lazy
   flag's claim, the page table the read ran at, and the writable-leaf
   predicate a copy-out needs. *)
Require Import UserPerm.       (* [perm_of] / [uperm] / [lazy_free] *)
Require Import ProcPtOwn.      (* [uptd] / [ud_um] / [proc_pt_wf] *)
Require Import UserPtTree.     (* [uva_wmapped] *)
(* THE GHOST-CLASS BINDERS' DEFINING MODULES, each IMPORTED and not merely
   reached transitively: a class named without its module in scope is a
   fresh [gFunctors -> Type] variable and the section's binders then
   resolve nothing (durable-notes, "Typeclasses and ghost-class bundling"). *)
Require Import Xv6Cameras.     (* [uartGhostG]: the console ring's cameras *)
Require Import ChildTok.       (* [ctokG]: the slot's fork arms' capacity *)
Require Import VcGen.          (* [trunc32]: how [argfd] reads a descriptor *)
Require Import FdSlots UserFd ProcGeom.
Require Import UInitFd.      (* [ufd_l0] -- the all-closed low ledger the
                               CLOSED arm of sh's entry is at *)
Require Import UserCwd UserChildren.  (* [ucwd_any] / [uch_any] -- the two
                               ghosts [UkSh.ush_pstate] carries beside the
                               ledger *)
Require Import UexecSlot UexecRet.  (* [uvis] / [uslot] -- the taint's
                               generic slot, [UkRun.urun_gen]'s premise *)
Require Import ConsoleInv.     (* [cons_window] / [cons_chain] / [CONSOLE] *)
Require Import UserConsole.    (* [upos] / [ucons_stored_lb] / [ucons_pay] *)
Require Import UCodeInit UkInit.  (* init's catalogs and its exec supply's shape *)
Require Import UkSh.           (* [sh_buf] / [sh_nbuf] *)
Require Import UkShParse.      (* [ushp_no_symbols] / [ushp_tokens] *)
Require Import UkShLoop.       (* [ush_line_lexable] -- the lowest file that
                                  sees both the LINE and the LEXER *)
Require Import AppEcho.        (* [echo_line] / [star_prefix] / [disc_seg] *)
Require Import UexecSG.
Require FsImg.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(*  §4  THE TWO PURE FACTS THAT DISCHARGE LEXABILITY                      *)
(*                                                                        *)
(*  [UkShFork.ushf_lexable] is "every line the user could type lexes",     *)
(*  which is false and is the last thing sh rests on.  What replaces it is *)
(*  these two, applied to the line the RECEIPT says sh read.               *)
(* ===================================================================== *)

(* (1) THE LINE IS A PREFIX OF [echo_line].  Under the discipline the input
   of one power cycle is a prefix of [echo_line]*; a window that begins at
   a LINE BOUNDARY -- which is where sh's previous [gets] stopped, because
   it stopped at a '\n' -- is therefore a prefix of one [echo_line].

   STATED OVER [ins] ALONE, at [EchoDisc.disc_seg] -- the CONTENT half D3
   of the discipline, which is all this lane needs (S6).  The discipline
   itself is stronger since DISC-RATE ([EchoDisc.disc_seg'] adds the owner's
   rate bound D0/D1/D2, which is what excludes the ring overflow), and a
   supplier reaches D3 from it in one step ([EchoDisc.disc_seg'_proj], or
   [disc_proj] to the whole-history [disc_old]).  These statements say
   nothing about which stored bytes were dropped, and do not have to --
   contiguity of the STORED sequence is what [ConsoleInv.cons_window] /
   [cons_chain] carry, and contiguity of the INPUT sequence is E5's
   overflow argument, not this lane's. *)
Definition ush_disc_line : Prop :=
  forall (q : nat) (bs : list (bv 8)),
    star_prefix echo_line (concat (replicate q echo_line) ++ bs) ->
    bs = take (length bs) echo_line.

(* ...and the same at the shape the call site has it in: the cycle's
   discipline, at a history whose input ends with the window. *)
Definition ush_disc_line_seg : Prop :=
  forall (h : list mobs) (q : nat) (bs : list (bv 8)),
    disc_seg h ->
    ins h = concat (replicate q echo_line) ++ bs ->
    bs = take (length bs) echo_line.

(* (2) A PREFIX OF [echo_line] THAT ENDS IN '\n' IS [echo_line].  '\n' is
   [echo_line]'s last byte and occurs nowhere else in it, and '\n' is
   exactly what [gets] stops at -- so the two together say the line sh has
   in its buffer IS "echo hello world\n". *)
Definition ush_line_full : Prop :=
  forall bs0 : list (bv 8),
    let bs := bs0 ++ [Z_to_bv 8 10] in
    bs = take (length bs) echo_line ->
    bs = echo_line.

(* (3) ...AND THAT LINE LEXES, concretely.  [ushp_no_symbols] keeps
   [gettoken] in its default arm and [ushp_tokens] names the three tokens
   of "echo hello world"; both are decidable at the literal, so the proof
   is [vm_compute]/[reflexivity] and no assumption about user input
   survives.  The length is [length echo_line] = 17 -- the '\n' is
   whitespace, not a terminator, and [gets] plants the NUL past it. *)
Definition ush_echo_tokens : Prop :=
  ushp_no_symbols (length echo_line) (fun j : nat => echo_line !!! j)
  /\ ushp_tokens (length echo_line) (fun j : nat => echo_line !!! j) 0%nat
       [(0, 4); (5, 10); (11, 16)]%nat
  /\ (length [(0, 4); (5, 10); (11, 16)]%nat < 10)%nat.

(* (4) ...AND THE SHAPE THE BUFFER'S LINE IS IN WHEN IT IS DISCIPLINED is
   [UkSh.ush_line_is] -- MOVED DOWN to the program tier (lane SH-LINE 2b,
   L3), because [UkSh.ush_rest_l] is what carries it and that file is below
   this one. *)

(* ...AND THE DISCHARGE ITSELF is [UkShLoop.ush_line_lexable]: it
   quantifies over the ONE line the receipt says sh read, and
   [ush_echo_tokens] above is the closed computation that answers it.
   What stands between the two is that [ushp_no_symbols] and [ushp_tokens]
   read their bytes through a function, so the instance at
   [fun j => f (k + j)] is the instance at [fun j => echo_line !!! j] under
   [UkSh.ush_line_is]'s pointwise equality (E4's
   [UkShEcho.ush_line_toks_holds] is that transport, with the token list
   named).  BOTH NAMES ARE KEPT HERE as abbreviations, so that the
   consumers above this file are unaffected by the move down. *)
Notation ush_line_is := UkSh.ush_line_is.
Notation ush_line_lexable := UkShLoop.ush_line_lexable.

(* ===================================================================== *)
(*  §4b  THE ^D REFUTATION (lane SH-LINE 2b, L2).                         *)
(*                                                                        *)
(*  [ConsoleInv.cons_swallow]'s [d + 1] arm, once the copy-out fault is    *)
(*  eliminated ([UkRunSys.uk_read_nofault] under the lazy flag), says the  *)
(*  swallowed byte was [C('D')] -- [cons_xlate b] is 4 -- and hands over   *)
(*  its history's input TAG.  [UkSh.ush_tag_law] reads that tag as         *)
(*  [⌜disc h⌝ ∨ T], and this is why the first disjunct is impossible: the  *)
(*  discipline's content half says the cycle's input is a prefix of        *)
(*  [echo_line]*, every byte of such a prefix is a byte OF [echo_line],    *)
(*  and 0x04 is not one of the seventeen.  So [r = 0] on a read that       *)
(*  swallowed a byte is the TAINT, and [gets] takes its taint branch.      *)
(* ===================================================================== *)

(* every byte of a [star_prefix] of [pat] is a byte of [pat] *)
Lemma ush_elem_concat_replicate (pat : list (bv 8)) (n : nat) (x : bv 8) :
  x ∈ concat (replicate n pat) -> x ∈ pat.
Proof.
  induction n as [| n IH]; cbn.
  - intro H. by apply elem_of_nil in H.
  - intro H. apply elem_of_app in H as [H | H]; [ exact H | exact (IH H) ].
Qed.

Lemma ush_star_prefix_elem (pat l : list (bv 8)) (x : bv 8) :
  star_prefix pat l -> x ∈ l -> x ∈ pat.
Proof.
  rewrite /star_prefix. intros Hsp Hx. rewrite Hsp in Hx.
  apply (ush_elem_concat_replicate pat (length l) x).
  rewrite <- (take_drop (length l) (concat (replicate (length l) pat))).
  apply elem_of_app. by left.
Qed.

(* ...and 0x04 is not one of [echo_line]'s seventeen *)
Lemma ush_echo_line_no_ctrl_d (x : bv 8) :
  x ∈ echo_line -> bv_unsigned x <> 4.
Proof.
  rewrite /echo_line. intros Hx Hv.
  apply elem_of_list_fmap in Hx as (z & -> & Hz).
  repeat (apply elem_of_cons in Hz as [-> | Hz];
          [ vm_compute in Hv; discriminate Hv | ]).
  by apply elem_of_nil in Hz.
Qed.

(* THE CYCLE THE LAST INPUT BYTE IS IN.  [cycles_of] folds the history
   into its power cycles, the open one last; an [ObsUartIn] event extends
   the most recent cycle (or starts one), so the byte's own cycle is a
   segment whose input ENDS with it.  No [trace_shape] premise: the fold
   does this whether or not the power is on. *)
Lemma ush_elem_of_rev_head {A} (x : A) (l : list A) : x ∈ rev (x :: l).
Proof.
  cbn. apply elem_of_app. right. by apply elem_of_list_singleton.
Qed.

Lemma ush_cycles_snoc_in (h : list mobs) (b : bv 8) :
  exists s0 : list mobs,
    (s0 ++ [ObsUartIn b])%list ∈ cycles_of (h ++ [ObsUartIn b])%list.
Proof.
  rewrite /cycles_of cycles_rev_app.
  destruct (cycles_rev h) as [| c cs] eqn:Hc.
  - exists []. exact (ush_elem_of_rev_head ([] ++ [ObsUartIn b])%list []).
  - exists c. exact (ush_elem_of_rev_head (c ++ [ObsUartIn b])%list cs).
Qed.

(* THE REFUTATION ITSELF, at the shape [cons_swallow]'s arm hands it: the
   byte the history ends in translates to 0x04. *)
Lemma disc_no_ctrl_d (h : list mobs) (b : bv 8) :
  obs_ends_in h b -> bv_unsigned (cons_xlate b) = 4 -> disc h -> False.
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
  apply (ush_echo_line_no_ctrl_d b); [| exact Hb].
  apply (ush_star_prefix_elem echo_line (ins s0 ++ [b]) b Hseg).
  apply elem_of_app. right. by apply elem_of_list_singleton.
Qed.

Section UConsLine.
  Context `{!riscvGS Σ}.
  Context `{!ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  Context `{!ghost_varG Σ (gset gname)}.
  (* the console ring's two cameras, at the narrow class a program binds
     ([UserConsole.v]'s header) *)
  Context `{!uartGhostG Σ}.
  Context `{!ctokG Σ}.
  Context {SG : uexecSG Σ}.
  Context `{PS : uprogSG Σ}.

  Local Notation a0_idx := (mword_of_int 10 : mword 5).
  Local Notation a1_idx := (mword_of_int 11 : mword 5).
  Local Notation a2_idx := (mword_of_int 12 : mword 5).

  (* =================================================================== *)
  (*  §1  THE LEDGER THAT KNOWS ITS FD 0                                  *)
  (*                                                                      *)
  (*  [UkSh.ush_std] is the bare ledger and says nothing about which of    *)
  (*  the three standard streams are open ([UkSh.v:4121-4133]).  What      *)
  (*  sh's read needs is one row: fd 0 is an OPEN, READABLE CONSOLE        *)
  (*  DEVICE, because that row is what selects [SpecFileread.              *)
  (*  fileread_in]'s console arm at [SpecArgfd.fd_st_of_key (xk_a W 0)]    *)
  (*  -- and the console arm is the only one that pays a receipt about     *)
  (*  input bytes.                                                        *)
  (*                                                                      *)
  (*  THE MAJOR IS [ConsoleInv.CONSOLE], not "some device": the arm is     *)
  (*  keyed by a [decide] on the major ([SpecFileread.fileread_extra]'s    *)
  (*  note), and a different major reads a different device.              *)
  (* =================================================================== *)
  Definition ush_std_cons (γfd : gname) (l : list fdstate) : iProp Σ :=
    (ustd γfd l ∗
     ⌜exists wr : bool, l !! 0%nat = Some (FdOpen true wr (FdDevice CONSOLE))⌝)%I.

  (* the bare ledger is what the rest of sh reads: the row is a pure side
     fact, so no lemma between here and the read has to carry it, and
     [UkSh.ush_std] is this one weakened. *)
  Lemma ush_std_cons_ledger (γfd : gname) (l : list fdstate) :
    ush_std_cons γfd l -∗ ustd γfd l.
  Proof. iIntros "[$ _]". Qed.

  (* =================================================================== *)
  (*  §2  SH'S READ LEAF, WITH THE RECEIPT KEPT                           *)
  (*                                                                      *)
  (*  [UkSh.ush_read_leaf] (a Hypothesis of UkSh's section, discharged     *)
  (*  today by [UShKernel.ush_read_leaf_of_win] out of                     *)
  (*  [UkRunSys.wp_uk_ecall_read_win]) throws the process's post away.     *)
  (*  This is the same leaf with the post KEPT, which is what              *)
  (*  [UkRunSys.wp_uk_ecall_read_recv] exists to deliver.             *)
  (*                                                                      *)
  (*  WHAT IT COSTS THE CALLER: its POSITION ([UserConsole.upos] at the    *)
  (*  cursor it believes the token stands at).  What it hands back is one  *)
  (*  of two things, and which one is not the caller's choice:             *)
  (*                                                                      *)
  (*   THE WINDOW.  The [d] bytes the call delivered are the ring's       *)
  (*   committed sequence at [n .. n+d), in order ([cons_chain]), each     *)
  (*   with the application's tag on the history it arrived at; and the    *)
  (*   position comes back at [n + dc], where the extra step is ACCOUNTED  *)
  (*   FOR rather than merely bounded ([UserConsole.ucons_swallow], lane   *)
  (*   CONS-SWALLOW): at [dc = d + 1] the call popped a byte it did not    *)
  (*   deliver, and the arm NAMES that byte -- its history, its tag and    *)
  (*   the reason.  THE REASON HAS ONE ARM HERE AND NOT TWO: the copy-out  *)
  (*   fault is ELIMINATED inside the leaf's own discharge                 *)
  (*   ([ush_swallow_nofault] below, out of row 5's [∃ P] and the buffer   *)
  (*   the caller owns, under the lazy flag at [false]), so the [fault]    *)
  (*   parameter is instantiated at [False] and what is left is [C('D')]   *)
  (*   with nothing delivered.  That is what lets a reader taking one byte *)
  (*   at a time tell a delivered line from a line with a hole in it.      *)
  (*                                                                      *)
  (*   THE TAINT.  A read taken WITHOUT the token -- by a process this     *)
  (*   application says nothing about -- moved the ring's committed count  *)
  (*   without moving the cursor, and the kernel cannot keep one out       *)
  (*   ([ConsoleInv]'s "CONS-CURSOR RULING (7)").  What it leaves is the   *)
  (*   credential, which for a constraining application IS the taint       *)
  (*   ([AppEcho.echo_sup_of_taint] read backwards), and sh's              *)
  (*   continuation goes generic.  The position comes back at SOME value:  *)
  (*   the pair is still the pair, but its number means nothing any more.  *)
  (*                                                                      *)
  (*  [T] IS A PARAMETER for [UserConsole.ucons_pay]'s reason: the program *)
  (*  tier names no application.                                          *)
  (*                                                                      *)
  (*  STATED AS A BODY, not as a [Lemma]: the discharge is this lane's     *)
  (*  phase 2, and it has to happen where the kernel's own instance of     *)
  (*  [UexecSG.uexecSG] is in scope (that is where [spost_at] at 5 unfolds *)
  (*  to [SpecFileread.fileread_extra]), which is [UInitSh.v]'s altitude   *)
  (*  and not [UShKernel.v]'s.                                            *)
  (* =================================================================== *)
  Definition ush_read_recv_leaf (N : uk_names Σ) (cn : cons_names)
      (γp : gname) (T : iProp Σ) (l : list fdstate) : iProp Σ :=
    (∀ (h : CpuId) (m : regfile) (pc : mword 64) (a : Z) (k n : nat)
       (f : nat -> bv 8) (avail : nat),
       ⌜usysno m = USYS_read⌝ -∗
       (* the descriptor is fd 0, which §1's ledger says is the console *)
       ⌜bv_signed (trunc32 (m !!! Regidx a0_idx)) = 0⌝ -∗
       ⌜uint (m !!! Regidx a1_idx) = a⌝ -∗
       ⌜uint (m !!! Regidx a2_idx) = Z.of_nat k⌝ -∗
       ⌜is_aligned_vaddr (Virtaddr (add_vec_int pc 4)) 2 = true⌝ -∗
       uinstr_is (ukn_t N) pc false (ECALL tt) -∗
       ubytes (ukn_d N) a k f -∗
       (* THE LEDGER, which is what SELECTS the console arm: row 5's
          bundle is [SpecFileread.fileread_in] at [SpecArgfd.fd_st_of_key]
          of the key's own table, and this is the caller's claim on it
          ([UkRunSys.wp_uk_ecall_read_recv] hands back the agreement
          [take NSTD (uvis_fd W) = l]).  read moves no descriptor, so it
          comes straight back. *)
       ush_std_cons (ukn_fd N) l -∗
       (* THE CALLER'S POSITION, which is what makes the window its own *)
       upos γp n -∗
       urun N h m pc avail -∗
       (∀ (h' : CpuId) (r : mword 64) (d : nat) (g : nat -> bv 8),
          ⌜(d <= k)%nat⌝ -∗
          ⌜forall j : nat, (d <= j < k)%nat -> g j = f j⌝ -∗
          ush_std_cons (ukn_fd N) l -∗
          ((∃ (dc : nat) (hs : list (list mobs))
              (sl : list (list mobs * bv 8)),
              ⌜cons_window sl n d g hs⌝ ∗ ⌜cons_chain sl⌝ ∗
              ucons_swallow cn False sl d dc ∗
              ucons_stored_lb cn sl ∗
              ([∗ list] hh ∈ hs, riscv_rx_tag hh) ∗
              upos γp (n + dc)%nat)
           ∨ (T ∗ ∃ n' : nat, upos γp n')) -∗
          ubytes (ukn_d N) a k g -∗
          urun N h' (<[Regidx a0_idx := r]> m) (add_vec_int pc 4) avail -∗
          WP (Loop : expr riscv_lang)) -∗
       WP (Loop : expr riscv_lang))%I.

  (* =================================================================== *)
  (*  §3  THE [gets] LOOP'S LINE INVARIANT                                *)
  (*                                                                      *)
  (*  [UkSh.wp_ksh_gets_loop] reads ONE byte per [read()] into the frame   *)
  (*  slot at s0-81 and copies it to buf[i], so after [i] turns the buffer *)
  (*  holds the ring's stored bytes at [n0 .. n0+i) and the position       *)
  (*  stands at [n0 + i].  That is this predicate, and it is the whole of  *)
  (*  what the loop gains.                                                *)
  (*                                                                      *)
  (*  [dc = d] ON EVERY TURN THE LOOP CONTINUES ON, which is why the       *)
  (*  position is [n0 + i] and not [n0 + i + something].  The two rounds:   *)
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
  Definition ush_gets_line (cn : cons_names) (γp : gname) (T : iProp Σ)
      (n0 i : nat) (g : nat -> bv 8) : iProp Σ :=
    ((∃ (hs : list (list mobs)) (sl : list (list mobs * bv 8)),
        ⌜cons_window sl n0 i g hs⌝ ∗ ⌜cons_chain sl⌝ ∗
        ucons_stored_lb cn sl ∗
        ([∗ list] hh ∈ hs, riscv_rx_tag hh) ∗
        upos γp (n0 + i)%nat)
     ∨ (T ∗ ∃ n' : nat, upos γp n'))%I.

  (* the loop ENTERS at the empty window, which costs nothing but the
     position: [cons_window sl n0 0 g []] holds of any bound whose length
     is [n0] ([ConsoleInv.cons_window_0]) *)
  Lemma ush_gets_line_0 (cn : cons_names) (γp : gname) (T : iProp Σ)
      (n0 : nat) (g : nat -> bv 8) (sl : list (list mobs * bv 8)) :
    length sl = n0 ->
    cons_chain sl ->
    ucons_stored_lb cn sl -∗ upos γp n0 -∗ ush_gets_line cn γp T n0 0%nat g.
  Proof.
    intros Hlen Hch. iIntros "#Hlb Hp". rewrite /ush_gets_line. iLeft.
    iExists [], sl.
    iSplitR; [ iPureIntro; exact (cons_window_0 sl n0 g Hlen) | ].
    iSplitR; [ by iPureIntro | ].
    iSplitR; [ iExact "Hlb" | ].
    iSplitR; [ done | ].
    rewrite Nat.add_0_r. iExact "Hp".
  Qed.

  (* =================================================================== *)
  (*  §3b  THE TWO ROUNDS' READINGS OF THE SWALLOWED BYTE                 *)
  (* =================================================================== *)

  (* THE COPY-OUT FAULT, ELIMINATED (lane SH-LINE 2b, L1; lane LAZY-FLAG's
     deliverable).  [ConsoleInv.cons_swallow]'s reason is "[C('D')] with
     nothing delivered, OR the copy-out faulted at this destination", and
     the second is a statement about the READER's own address space.  A
     verified program refutes it from what it already owns: [ubytes] puts
     the destination in the permission map's writable set, and the lazy
     flag at [false] turns a writable page of the PROJECTION into a real
     user leaf with V, U and W ([UkRunSys.uk_read_nofault]).  What is left
     is the [False]-instantiated arm the leaf above is stated at.

     THE THREE PURE PREMISES ARE ROW 5's THREE CONJUNCTS
     ([UexecExecInst]'s read row, with [UkRunSys.wp_uk_ecall_read_recv]'s
     [⌜uvis_lazy W = false⌝] turning the row's implication into
     [lazy_free]), so the discharge applies this with the [∃ P] in hand. *)
  Lemma ush_swallow_nofault (N : uk_names Σ) (cn : cons_names)
      (M : gmap Z (bv 8)) (pmv : gmap (mword 27) uperm) (sz : Z)
      (dst : mword 64) (k d : nat) (f : nat -> bv 8) (P : uptd)
      (sl : list (list mobs * bv 8)) (dc : nat) :
    (d < k)%nat ->
    ProcPtOwn.proc_pt_wf P ->
    perm_of (ud_um P) sz = pmv ->
    lazy_free (ud_um P) sz ->
    uheap (ukn_t N) (ukn_d N) (ukn_s N) M pmv sz -∗
    ubytes (ukn_d N) (uint dst) k f -∗
    ucons_swallow cn
      (~ UserPtTree.uva_wmapped P (uint (add_vec_int dst (Z.of_nat d))))
      sl d dc -∗
    ucons_swallow cn False sl d dc.
  Proof.
    intros Hdk Hwf Hpm Hlf. iIntros "Hheap Hbs Hsw".
    iDestruct (uk_read_nofault (ukn_t N) (ukn_d N) (ukn_s N) M pmv sz
                 (DfracOwn 1) dst k d f P Hdk Hwf Hpm Hlf
                 with "Hheap Hbs") as %Hmap.
    iApply (ucons_swallow_mono cn _ False sl d dc with "Hsw").
    intro Hno. exact (Hno Hmap).
  Qed.

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
  (*  discipline or the taint, and a disciplined cycle's input is a prefix *)
  (*  of [echo_line]*, in which 0x04 does not occur ([disc_no_ctrl_d]).    *)
  (*                                                                      *)
  (*  So there is no third thing for sh to walk: either nothing was        *)
  (*  swallowed and the position is exactly where the loop left it, or the *)
  (*  application is tainted and sh's continuation is the generic one.     *)
  (* =================================================================== *)
  Lemma ush_swallow_taint (cn : cons_names) (T : iProp Σ)
      (sl : list (list mobs * bv 8)) (dc : nat) :
    ush_tag_law T -∗ ucons_swallow cn False sl 0%nat dc -∗
    ⌜dc = 0%nat⌝ ∨ T.
  Proof.
    iIntros "#Hlaw Hsw". rewrite /ucons_swallow.
    iDestruct "Hsw" as "[%He | [%He H]]"; [ iLeft; by iPureIntro | ].
    iDestruct "H" as (h b) "(%Hen & _ & _ & Htg & Hwhy)".
    iDestruct "Hwhy" as "[%Hd | %Hf]"; [ | exfalso; exact Hf ].
    iDestruct ("Hlaw" $! h with "Htg") as "[%Hdisc | HT]"; [ | by iRight ].
    exfalso. exact (disc_no_ctrl_d h b Hen (proj2 Hd) Hdisc).
  Qed.

  (* =================================================================== *)
  (*  §6  THE THREE-ARM LEDGER SH'S ENTRY TAKES -- COLLAPSED (lane          *)
  (*      SH-LINE 2b, L4).                                                  *)
  (*                                                                        *)
  (*  It is [UkSh.ush_std l] beside [UkSh.ush_fd0 T l] now, and the three    *)
  (*  arms are [UkSh.ush_fd0p]'s two plus the taint.  The pure row moved     *)
  (*  DOWN for SH-OPEN's reason: sh's console PREAMBLE reopens a closed      *)
  (*  fd 0, so the row its read runs on is the one the preamble LEFT, and    *)
  (*  the loop head ([UkSh.ush_loop_head]) has to carry it -- which it       *)
  (*  cannot do from a file above [UkSh.v].  §1's [ush_std_cons] is the      *)
  (*  CONSOLE arm, which is what the read leaf above takes.                  *)
  (* =================================================================== *)

  (* =================================================================== *)
  (*  §7  SH'S PER-TURN STATE, WITH THE POSITION -- LANDED.                 *)
  (*                                                                        *)
  (*  [UkSh.ush_pstate] carries it: the ledger, the cwd, the children set    *)
  (*  and -- LAST -- [UkSh.ush_pos], the program's half of the console       *)
  (*  position pair (SH-LINE phase 2a).  Nothing is left here.               *)
  (* =================================================================== *)

  (* =================================================================== *)
  (*  §8  THE TAG'S READING -- MOVED DOWN (lane SH-LINE 2b, L4).            *)
  (*                                                                        *)
  (*  It is [UkSh.ush_tag_law T] now, for §10's reason: [UkSh.ush_rest_l]    *)
  (*  is what consumes what the law produces, and that file is below this    *)
  (*  one.  §11's [Pay] below is what carries it across the exec.            *)
  (* =================================================================== *)

  (* =================================================================== *)
  (*  §9  THE TAINT'S GENERIC CONTINUATION -- MOVED DOWN (lane SH-OPEN).   *)
  (*                                                                      *)
  (*  It is [UkSh.ush_gen_slot] / [UkSh.ush_gen_run] now, because the      *)
  (*  first walk that needs it is sh's CONSOLE PREAMBLE, which is below    *)
  (*  this file: sh's open of "console" is PINNED, so under the taint      *)
  (*  there is no bundle for row 15 and the preamble must be able to stop  *)
  (*  walking sh's code.  The two statements were textually identical;     *)
  (*  this file's copies are gone and its own statements take UkSh's.      *)
  (* =================================================================== *)

  (* =================================================================== *)
  (*  §10  WHAT REPLACES [UkShFork.ushf_lexable]                          *)
  (*                                                                      *)
  (*  [ushf_lexable] is "every line the user could type lexes", which is   *)
  (*  false.  What the command loop hands its body instead is this: for    *)
  (*  the line in the buffer at [k], either the FIRST NUL at or after [k]  *)
  (*  ends a line that is exactly [echo_line] ([ush_line_is], hence        *)
  (*  [ush_line_lexable]), or the taint -- and on the taint the body's     *)
  (*  continuation is §9's.                                               *)
  (*                                                                      *)
  (*  STATED OVER THE FIRST NUL rather than over a given [len] because     *)
  (*  that is what [UkShFork.ushf_first_nul] produces: the body derives    *)
  (*  its own [len] from the loop's "some byte at or after [k] is NUL",    *)
  (*  and the line fact has to hold at the [len] it derived.               *)
  (* =================================================================== *)
  (*  IT IS [UkSh.ush_rest_line T f k] NOW, and it rides as a premise of    *)
  (*  [UkSh.ush_rest_l] -- the obligation [UkShFork.ushf_rest_of_body]       *)
  (*  proves.  Moved DOWN because its consumer is the command loop's body.   *)

  (* =================================================================== *)
  (*  §11  THE LINEAR [Pay] THAT CROSSES THE EXEC                         *)
  (*                                                                      *)
  (*  [PinnedExec.pinned_exec_bundle]'s [Pay] is the ONE linear resource   *)
  (*  an exec'ing process can put in the exec'd image's slot, and this is  *)
  (*  what init puts there for sh: sh's own entry payload                  *)
  (*  ([UInitSh.sh_pay], persistent), the tag's reading (§8, persistent)   *)
  (*  and the POSITION (linear, minted fresh per child just before the     *)
  (*  fork).  The exit payload is NOT here -- it arrives at the            *)
  (*  constructor wand from the kernel's own payment (EXEC-PAY; §5's       *)
  (*  note).                                                              *)
  (*                                                                      *)
  (*  [Pay] is a parameter because [UInitSh.sh_pay] is stated above this   *)
  (*  file's altitude; what this names is the SHAPE the two extra          *)
  (*  conjuncts ride in.                                                   *)
  (* =================================================================== *)
  Definition ush_exec_pay (Pay : iProp Σ) (T : iProp Σ) (γp : gname)
      (n : nat) : iProp Σ :=
    (Pay ∗ ush_tag_law T ∗ upos γp n)%I.


End UConsLine.
