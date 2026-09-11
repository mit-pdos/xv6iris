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

   STATED OVER [ins] ALONE, which is all [AppEcho.disc] gives (S6): it says
   nothing about which stored bytes were dropped, and it does not have to
   -- contiguity of the STORED sequence is what [ConsoleInv.cons_window] /
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
  (*  [UkRunSys.wp_uk_ecall_read_recv_body] exists to deliver.             *)
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
      (γp : gname) (T : iProp Σ) : iProp Σ :=
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
       (* THE CALLER'S POSITION, which is what makes the window its own *)
       upos γp n -∗
       urun N h m pc avail -∗
       (∀ (h' : CpuId) (r : mword 64) (d : nat) (g : nat -> bv 8),
          ⌜(d <= k)%nat⌝ -∗
          ⌜forall j : nat, (d <= j < k)%nat -> g j = f j⌝ -∗
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
  (*  §5  INIT'S LINEAR EXEC SUPPLY                                       *)
  (*                                                                      *)
  (*  [UkInit.init_exec_sup] is persistent and stated at the TRIVIAL       *)
  (*  payload ([UkInit.v:518]).  The child init lends the console to execs *)
  (*  ONCE, at a payload that is not trivial, and carries a LINEAR         *)
  (*  resource across that exec ([PinnedExec.pinned_exec_bundle]'s [Pay]   *)
  (*  is linear, and [PinnedExec.pex_slot]'s [∧] is what lets the same     *)
  (*  payload answer the slot arm and the refund) -- so the supply the     *)
  (*  child holds is this one: no [□], the payload named, and the          *)
  (*  POSITION handed over with it.                                       *)
  (*                                                                      *)
  (*  THE EXIT PAYLOAD IS NOT A PREMISE: IT ARRIVES THROUGH THE SEAM.      *)
  (*  [SpecKexec.exec_slot_pre]'s two wands take [Q (-1)] beside the pay   *)
  (*  fact, the dispatcher feeds it from the payment it holds across the   *)
  (*  exec trap ([SpecSyscall.sysc_exec_out]'s success arm), and           *)
  (*  [PinnedExec.pex_slot]'s constructor wand relays it -- so the party   *)
  (*  that builds sh's entry is handed the payload at the key it is        *)
  (*  building for, and this supply neither holds nor asks for it.  What   *)
  (*  it still names is the POSITION, which is sh's own and crosses in     *)
  (*  the slot piece's linear [Pay].                                       *)
  (* =================================================================== *)
  Definition init_exec_sup_lin (cn : cons_names) (γp : gname) (T : iProp Σ)
      (n : nat) : iProp Σ :=
    (∀ (N' : uk_names Σ) (m : regfile) (pc : mword 64),
       (* THE CHILD'S RECORD IS AT THE CONSOLE PAYLOAD, not at the trivial
          one: exec keeps the generation, so the exec'd image's payload IS
          the exec'ing process's ([ChildTok.my_pay] pins it). *)
       ⌜ukn_pay N' = ucons_pay cn γp T⌝ -∗
       ⌜m !!! Regidx a0_idx = (mword_of_int 0x9a8 : mword 64)⌝ -∗
       ⌜m !!! Regidx a1_idx = (mword_of_int 0x1000 : mword 64)⌝ -∗
       init_rodata (ukn_t N') -∗
       init_argv (ukn_d N') -∗
       ustd_any (ukn_fd N') -∗
       (* the position, which sh holds across [gets] *)
       upos γp n -∗
       udepw_at N' m pc USYS_exec FsImg.ROOTINO)%I.

End UConsLine.
