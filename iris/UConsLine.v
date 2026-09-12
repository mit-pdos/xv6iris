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

(* (4) ...AND THE SHAPE THE BUFFER'S LINE IS IN WHEN IT IS DISCIPLINED.
   (1)-(3) above are about the ring's stored sequence and about
   [echo_line]; this is the same fact at the shape sh's command loop hands
   its body: the [len] bytes at [k] in the LINE BUFFER are [echo_line]'s,
   in order, and there are exactly [length echo_line] of them.  It is the
   whole of what [UkShFork.ushf_lexable] is replaced by (S5). *)
Definition ush_line_is (f : nat -> bv 8) (k len : nat) : Prop :=
  len = length echo_line
  /\ forall j : nat, (j < len)%nat -> f (k + j)%nat = echo_line !!! j.

(* ...AND THE DISCHARGE ITSELF.  [ushf_lexable] quantifies over EVERY line
   the user could type, which is why it is false; this quantifies over the
   ONE line the receipt says sh read, and [ush_echo_tokens] above is the
   closed computation that answers it.  What stands between the two is that
   [ushp_no_symbols] and [ushp_tokens] read their bytes through a function,
   so the instance at [fun j => f (k + j)] is the instance at
   [fun j => echo_line !!! j] under [ush_line_is]'s pointwise equality. *)
Definition ush_line_lexable : Prop :=
  forall (f : nat -> bv 8) (k len : nat),
    ush_line_is f k len ->
    ushp_no_symbols len (fun j : nat => f (k + j)%nat)
    /\ exists toks : list (nat * nat),
         ushp_tokens len (fun j : nat => f (k + j)%nat) 0 toks
         /\ (length toks < 10)%nat.

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
  (*   THE WINDOW.  The [d] bytes the call delivered are the ring's        *)
  (*   committed sequence at [n .. n+d), in order ([cons_chain]), each     *)
  (*   with the application's tag on the history it arrived at; and the    *)
  (*   position comes back at [n + dc], where [dc] is [d] or one more      *)
  (*   (two of consoleread's exits pop a byte they do not deliver).        *)
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
              ⌜(d <= dc <= d + 1)%nat⌝ ∗
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
  (*  [dc = d] ON EVERY TURN, which is why the position is [n0 + i] and    *)
  (*  not [n0 + i + something]: the two consoleread exits that pop a byte  *)
  (*  they do not deliver are the C('D') arm with nothing delivered yet    *)
  (*  ([d = 0], and gets breaks on [r < 1]) and the copyout failure, which *)
  (*  is a failure on sh's OWN one-byte frame slot.  Phase 2 proves that   *)
  (*  from [d = r = 1] on the arm gets continues on; if a swallowed byte   *)
  (*  can occur with [r = 1] the loop takes the TAINT branch instead.      *)
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
  (*  §6  THE THREE-ARM LEDGER SH'S ENTRY TAKES                           *)
  (*                                                                      *)
  (*  §1 above is the arm sh's read RUNS ON.  What init can actually       *)
  (*  hand over is one of three, and which one is not init's choice        *)
  (*  (app-echo.md, "OPEN-PIN PHASE 1 LANDED", finding (a); the head is    *)
  (*  [UInitFd.ufd_head] at the fork):                                     *)
  (*                                                                      *)
  (*   CONSOLE -- init's repair worked and fd 0 is the console device.     *)
  (*     This is the arm the line is disciplined on.                       *)
  (*                                                                      *)
  (*   CLOSED -- init's second open failed at allocation, so the two dups  *)
  (*     failed too and fds 0-2 are all closed ([UInitFd.ufd_l0]).  sh     *)
  (*     runs: its first [read(0, ..)] returns -1, [gets] breaks on        *)
  (*     [r < 1], [getcmd] returns -1 and sh exits.  Nothing reaches the   *)
  (*     console, and the arm is a SHORT walk rather than a missing one.   *)
  (*                                                                      *)
  (*   THE TAINT -- the claim's pins may be broken, and the continuation   *)
  (*     is the generic one (§9).                                          *)
  (*                                                                      *)
  (*  ONE PREDICATE at three arms rather than three premises, so that      *)
  (*  every lemma between sh's entry and its read is unchanged by which    *)
  (*  arm it is at: [UkSh.ush_std] is this one with the disjunction        *)
  (*  dropped.                                                             *)
  (* =================================================================== *)
  Definition ush_std3 (γfd : gname) (T : iProp Σ) (l : list fdstate)
    : iProp Σ :=
    (ustd γfd l ∗
     (⌜exists wr : bool, l !! 0%nat = Some (FdOpen true wr (FdDevice CONSOLE))⌝
      ∨ ⌜l = ufd_l0⌝
      ∨ T))%I.

  (* the bare ledger, which is what every lemma that does not read the arm
     wants -- [ush_std_cons_ledger]'s twin *)
  Lemma ush_std3_ledger (γfd : gname) (T : iProp Σ) (l : list fdstate) :
    ush_std3 γfd T l -∗ ustd γfd l.
  Proof. iIntros "[$ _]". Qed.

  (* the three constructors, one per arm *)
  Lemma ush_std3_cons (γfd : gname) (T : iProp Σ) (l : list fdstate) :
    ush_std_cons γfd l -∗ ush_std3 γfd T l.
  Proof.
    iIntros "[Hl %Hrow]". rewrite /ush_std3. iFrame "Hl".
    iLeft. by iPureIntro.
  Qed.

  Lemma ush_std3_closed (γfd : gname) (T : iProp Σ) :
    ustd γfd ufd_l0 -∗ ush_std3 γfd T ufd_l0.
  Proof.
    iIntros "Hl". rewrite /ush_std3. iFrame "Hl". iRight. iLeft.
    by iPureIntro.
  Qed.

  Lemma ush_std3_taint (γfd : gname) (T : iProp Σ) (l : list fdstate) :
    T -∗ ustd γfd l -∗ ush_std3 γfd T l.
  Proof.
    iIntros "HT Hl". rewrite /ush_std3. iFrame "Hl". iRight. iRight.
    iExact "HT".
  Qed.

  (* =================================================================== *)
  (*  §7  SH'S PER-TURN STATE, WITH THE POSITION                          *)
  (*                                                                      *)
  (*  [UkSh.ush_pstate] is the three ghosts a turn of sh's command loop    *)
  (*  cannot escape carrying (the ledger, the cwd, the children set).      *)
  (*  SH-LINE adds a FOURTH -- the program's half of the console position  *)
  (*  pair ([UserConsole.upos]) -- and it goes LAST, so every existing     *)
  (*  destructuring pattern keeps working (durable-notes, "Shaping a       *)
  (*  change so the sweep is small").                                      *)
  (*                                                                      *)
  (*  THE POSITION IS EXISTENTIAL HERE AND NAMED INSIDE [gets].  A turn of *)
  (*  the loop begins wherever the previous line ended, and no lemma       *)
  (*  between the loop head and the read needs the number; [gets] opens    *)
  (*  the existential once, calls it [n0], and its own invariant           *)
  (*  ([ush_gets_line]) is what carries it byte by byte.                   *)
  (*                                                                      *)
  (*  IT IS HELD ON BOTH ARMS, tainted or not: the pair is still the pair  *)
  (*  after a tokenless reader has moved the ring, only its number no      *)
  (*  longer means anything ([ush_read_recv_leaf]'s taint disjunct hands   *)
  (*  it back at SOME value).                                              *)
  (* =================================================================== *)
  Definition ush_pos (γp : gname) : iProp Σ := (∃ n : nat, upos γp n)%I.

  Definition ush_pstate_line (γfd γcwd γch γp : gname) (T : iProp Σ)
      (l : list fdstate) : iProp Σ :=
    (ush_std3 γfd T l ∗ UserCwd.ucwd_any γcwd ∗ UserChildren.uch_any γch
     ∗ ush_pos γp)%I.

  (* =================================================================== *)
  (*  §8  THE TAG'S READING, AS A PERSISTENT LAW SH'S ENTRY TAKES         *)
  (*                                                                      *)
  (*  [RiscvPtsto.riscv_rx_tag] is a field of the machine's fixed ghost    *)
  (*  state, tied to the application's own tag ([App.app_tag]) only by an  *)
  (*  equation in the top theorem's [boot_fixedGS] -- nothing below reads  *)
  (*  it (app-echo.md, "SH-LINE PHASE 1 LANDED", ruling (3)).  So the      *)
  (*  reading is a PREMISE, threaded from [SystemAdequacy]'s [Hinit_boot]  *)
  (*  through init's pinned builder to sh's entry, exactly as              *)
  (*  [UInitSh.init_sh_slot] takes its claim law.                          *)
  (*                                                                      *)
  (*  Persistent, which it must be: sh's entry is built inside init's      *)
  (*  fork child, inside an [iLob] the parent re-enters.                   *)
  (* =================================================================== *)
  Definition ush_tag_law (T : iProp Σ) : iProp Σ :=
    (□ (∀ h : list mobs, riscv_rx_tag h -∗ ⌜disc h⌝ ∨ T))%I.

  Global Instance ush_tag_law_persistent T : Persistent (ush_tag_law T).
  Proof. rewrite /ush_tag_law. apply _. Qed.

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
  Definition ush_rest_line (T : iProp Σ) (f : nat -> bv 8) (k : nat)
    : iProp Σ :=
    ((∀ len : nat,
        ⌜forall j : nat, (j < len)%nat -> f (k + j)%nat <> ubyte0⌝ -∗
        ⌜f (k + len)%nat = ubyte0⌝ -∗ ⌜ush_line_is f k len⌝)
     ∨ T)%I.

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
