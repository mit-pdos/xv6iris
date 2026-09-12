(* ===================================================================== *)
(* UserConsole.v -- THE PROGRAM SIDE OF THE CONSOLE READER'S CURSOR.      *)
(*                                                                        *)
(* The console ring's consumption cursor is a [ghost_var] in two halves:   *)
(* the ring keeps one ([ConsoleInv.cons_cursor], inside [cons_res]) and    *)
(* the other IS THE READER TOKEN ([ConsoleInv.cons_reader]) -- the         *)
(* exclusive right to consume the console's input.  A verified reader has  *)
(* to do two things with that token which no single half can do at once:   *)
(*                                                                        *)
(*   PAY IT BACK WHEN IT IS KILLED.  Only [UkRun.ukn_pay N (-1)] survives  *)
(*   a kill (app-echo.md, "SH-LINE RULING"), so the token has to sit       *)
(*   inside the exit payload -- which is LINEAR IN [urun] and ABSTRACT to  *)
(*   the program: a program cannot look at it between traps.               *)
(*                                                                        *)
(*   NAME ITS OWN POSITION BETWEEN READS.  [gets] reads one byte per       *)
(*   [read()] and has to know the next byte it gets is the one after the   *)
(*   last -- which needs the cursor's VALUE as a resource the program      *)
(*   holds in its hand, not one buried in a payload.                       *)
(*                                                                        *)
(* THE POSITION PAIR IS WHAT RESOLVES THAT.  A SECOND ghost_var pair       *)
(* [upos]/[upos_a], minted fresh per child at the token's current          *)
(* position: the PROGRAM's half [upos] travels beside the run (through     *)
(* the fork's child arm and across the exec in                             *)
(* [PinnedExec.pinned_exec_bundle]'s linear [Pay]), while the other half   *)
(* [upos_a] rides INSIDE the payload beside the token.  Neither half moves *)
(* alone, so "the payload's token stands at the position I hold" is an     *)
(* agreement ([upos_agree]) and a read advances both together              *)
(* ([upos_update]).  Two copies of ONE half would be [False]; this is the  *)
(* only shape that gives the program a NAMED position without giving it a  *)
(* second copy of the token.                                               *)
(*                                                                        *)
(* [UserChildren.v] is the mold: one ghost variable, split in half, one    *)
(* agreement lemma and one update lemma, and nothing else.                 *)
(*                                                                        *)
(* WHY THE READER TOKEN IS SPELLED AGAIN HERE.  [ConsoleInv.cons_reader]   *)
(* is discharged over the whole-system bundle [Xv6G.xv6G], and a user      *)
(* program file binds the narrow classes instead ([UkRun.v] binds          *)
(* [ChildTok.ctokG] and not the bundle, deliberately) -- so a program      *)
(* statement cannot name [cons_reader] at all.  [ucons_reader] is THE SAME *)
(* PROPOSITION at the narrow class, exactly as [ConsoleInv.cons_hi] is     *)
(* [WpUart.uart_rx_hi] spelled one file down, and §3 below proves the two  *)
(* equal by [reflexivity] wherever the bundle IS in scope.                 *)
(* ===================================================================== *)
From Stdlib Require Import ZArith List.
From stdpp Require Import list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_var own.
From iris.algebra.lib Require Import mono_list.
Require Import SailStdpp.Base SailStdpp.Values.
Require Import RiscvLang ObsTrace.   (* [mobs] -- what a tag's history is made of *)
Require Import RiscvPtsto.           (* [riscv_rx_tag] -- the application's tag on
                                        the history an input byte arrived at *)
Require Import Xv6Cameras.           (* [uartGhostG]: the ring's two cameras *)
Require Import Xv6G.                 (* [xv6G] -- §3's bridge only *)
Require Export UartNames.            (* [cons_names] / [cn_rd] / [cn_log] *)
Require Import ConsoleInv.           (* the ring's own spelling, for §3's bridge *)
Local Open Scope Z_scope.

(* ===================================================================== *)
(*  1.  THE POSITION PAIR, AND THE TOKEN AT THE NARROW CLASS              *)
(* ===================================================================== *)
Section UserConsole.
  (* [Xv6Cameras.uartGhostG] and NOT [Xv6G.xv6G]: this file is meant to be
     named from the user-program tier, which binds the narrow classes
     ([UkRun.v]'s note).  [cons_ghost_rdG] and [cons_ghost_logG] are its
     two members the console's cursor and stored sequence are built on. *)
  Context `{!uartGhostG Σ}.
  (* ...and the machine's fixed ghost state, for [RiscvPtsto.riscv_rx_tag]
     alone: [ucons_swallow] below is the only definition here that names a
     tag, and the rest of the section does not see this binder. *)
  Context `{!riscvGS Σ}.

  (* ---- the pair ---- *)
  (* the PROGRAM's half: a separable resource sh carries round [gets],
     frames across unrelated calls, and hands to the read that moves it *)
  Definition upos (γ : gname) (n : nat) : iProp Σ :=
    ghost_var γ (1/2) n.

  (* ...and the half that RIDES IN THE PAYLOAD, beside the token.  It is
     what makes the payload's existential position the program's own: the
     program agrees the two and neither can move without the other. *)
  Definition upos_a (γ : gname) (n : nat) : iProp Σ :=
    ghost_var γ (1/2) n.

  Global Instance upos_timeless γ n : Timeless (upos γ n).
  Proof. rewrite /upos. apply _. Qed.
  Global Instance upos_a_timeless γ n : Timeless (upos_a γ n).
  Proof. rewrite /upos_a. apply _. Qed.

  (* THE MINT, at the position the token currently stands at.  init calls
     it once per child, immediately before the fork that lends that child
     the token: the payload it pays takes [upos_a] and the child's own
     continuation takes [upos]. *)
  Lemma upos_alloc (n : nat) :
    ⊢ |==> ∃ γ : gname, upos γ n ∗ upos_a γ n.
  Proof.
    iMod (ghost_var_alloc n) as (γ) "Hg".
    iEval (rewrite -Qp.half_half) in "Hg".
    iDestruct (ghost_var_split with "Hg") as "[H1 H2]".
    iModIntro. iExists γ. iFrame "H1 H2".
  Qed.

  (* the whole point of the pair: the payload's position IS the one the
     program holds, so a read's receipt at [cur = n] is a receipt at the
     reader's own cursor *)
  Lemma upos_agree (γ : gname) (n n' : nat) :
    upos γ n -∗ upos_a γ n' -∗ ⌜n = n'⌝.
  Proof.
    iIntros "H1 H2". by iDestruct (ghost_var_agree with "H1 H2") as %->.
  Qed.

  (* ...and BOTH halves move it, which is what a read spends *)
  Lemma upos_update (γ : gname) (n n' : nat) :
    upos γ n -∗ upos_a γ n ==∗ upos γ n' ∗ upos_a γ n'.
  Proof. iIntros "H1 H2". iApply (ghost_var_update_halves with "H1 H2"). Qed.

  (* ---- the ring's two resources, at the narrow class ---- *)
  (* THE READER TOKEN.  [ConsoleInv.cons_reader] spelled at [uartGhostG];
     §3 proves them equal. *)
  Definition ucons_reader (cn : cons_names) (n : nat) : iProp Σ :=
    ghost_var cn.(cn_rd) (1/2) n.

  (* ...AND THE BOUND ON THE STORED SEQUENCE a receipt hands out
     ([ConsoleInv.cons_stored_lb]): persistent, and any two of them agree
     on every index both have, which is what makes two successive reads'
     windows parts of ONE sequence. *)
  Definition ucons_stored_lb (cn : cons_names)
      (st : list (list mobs * bv 8)) : iProp Σ :=
    own cn.(cn_log) (◯ML (st : list (leibnizO (list mobs * bv 8)))).

  Global Instance ucons_reader_timeless cn n : Timeless (ucons_reader cn n).
  Proof. rewrite /ucons_reader. apply _. Qed.
  Global Instance ucons_stored_lb_persistent cn st :
    Persistent (ucons_stored_lb cn st).
  Proof. rewrite /ucons_stored_lb. apply _. Qed.
  Global Instance ucons_stored_lb_timeless cn st :
    Timeless (ucons_stored_lb cn st).
  Proof. rewrite /ucons_stored_lb. apply _. Qed.

  (* ...AND THE SWALLOWED BYTE, at the narrow class too
     ([ConsoleInv.cons_swallow]).  consoleread's cursor moves by [d] or by
     [d + 1], and at [d + 1] the call popped a byte it did not deliver;
     the arm NAMES that byte, so a program reading one byte at a time can
     tell a delivered line from a line with a hole in it.  Spelled here
     for [ucons_reader]'s reason -- the ring's own copy is discharged over
     [Xv6G.xv6G], which a program file must not bind -- and section 3
     proves the two equal.

     [fault] IS A PARAMETER, as it is in the ring's copy: it is a statement
     about the READER's own address space, and a verified program
     ELIMINATES it ([UkRunSys.uk_read_nofault] under the lazy flag), so the
     program-tier leaf is stated at [False] and the discharge weakens the
     kernel's arm to it ([cons_swallow_mono]). *)
  Definition ucons_swallow (cn : cons_names) (fault : Prop)
      (sl : list (list mobs * bv 8)) (d dc : nat) : iProp Σ :=
    (⌜dc = d⌝
     ∨ ⌜dc = (d + 1)%nat⌝ ∗
       ∃ (h : list mobs) (b : bv 8),
         ⌜obs_ends_in Uart0 h b⌝ ∗
         ucons_stored_lb cn (sl ++ [(h, b)])%list ∗
         ⌜cons_chain (sl ++ [(h, b)])%list⌝ ∗
         riscv_rx_tag h ∗
         (⌜d = 0%nat /\ bv_unsigned (cons_xlate b) = 4⌝ ∨ ⌜fault⌝))%I.

  Global Instance ucons_swallow_persistent cn fault sl d dc :
    Persistent (ucons_swallow cn fault sl d dc).
  Proof. rewrite /ucons_swallow. apply _. Qed.

  (* THE REASON WEAKENS ([ConsoleInv.cons_swallow_mono]'s twin).  [fault]
     is a statement about the reader's own address space, and the verified
     reader's use of it is the DEGENERATE weakening: it proves the fault
     impossible and moves the arm to [False]. *)
  Lemma ucons_swallow_mono (cn : cons_names) (f1 f2 : Prop)
      (sl : list (list mobs * bv 8)) (d dc : nat) :
    (f1 -> f2) ->
    ucons_swallow cn f1 sl d dc -∗ ucons_swallow cn f2 sl d dc.
  Proof.
    intros Himp. rewrite /ucons_swallow.
    iIntros "[%He | [%He H]]"; [ iLeft; by iPureIntro | ].
    iRight. iSplitR; [ by iPureIntro | ].
    iDestruct "H" as (h b) "(%Hen & #Hlb & %Hch & #Htg & Hwhy)".
    iExists h, b. iFrame "Hlb Htg".
    iSplitR; [ by iPureIntro | ]. iSplitR; [ by iPureIntro | ].
    iDestruct "Hwhy" as "[%Hd | %Hf]";
      [ iLeft; by iPureIntro | iRight; iPureIntro; exact (Himp Hf) ].
  Qed.

  (* the arm every exit but the two takes: the cursor moved by exactly the
     run ([ConsoleInv.cons_swallow_eq]'s twin) *)
  Lemma ucons_swallow_refl (cn : cons_names) (fault : Prop)
      (sl : list (list mobs * bv 8)) (d : nat) :
    ⊢ ucons_swallow cn fault sl d d.
  Proof. rewrite /ucons_swallow. iLeft. by iPureIntro. Qed.

  (* ...and the bound it carries, which is what the landed callers read *)
  Lemma ucons_swallow_range (cn : cons_names) (fault : Prop)
      (sl : list (list mobs * bv 8)) (d dc : nat) :
    ucons_swallow cn fault sl d dc -∗ ⌜(d <= dc <= d + 1)%nat⌝.
  Proof.
    rewrite /ucons_swallow. iIntros "[%He | [%He _]]"; iPureIntro; lia.
  Qed.

  (* THE ONE ARM A ONE-BYTE READ THAT RETURNED A BYTE CAN BE AT.  [gets]
     asks for one byte and continues only on [r = 1], so [d = 1] there --
     and the swallowing arm needs [d = 0] once the fault is eliminated.
     So at [d = 1] and [fault := False] the cursor moved by exactly one. *)
  Lemma ucons_swallow_nofault_1 (cn : cons_names)
      (sl : list (list mobs * bv 8)) (dc : nat) :
    ucons_swallow cn False sl 1%nat dc -∗ ⌜dc = 1%nat⌝.
  Proof.
    rewrite /ucons_swallow. iIntros "[%He | [%He H]]"; [ by iPureIntro | ].
    iDestruct "H" as (h b) "(_ & _ & _ & _ & [%Hd | %Hf])";
      [ iPureIntro; lia | done ].
  Qed.

  (* =================================================================== *)
  (*  2.  THE PAYLOAD THE SHELL'S EXIT OWES ITS PARENT                    *)
  (* =================================================================== *)
  (* [UkRun.ukn_pay] at sh: what init gets back when the shell exits OR IS
     KILLED.  Either the token at SOME position with the payload's half of
     the pair beside it, or the application's TAINT -- which is what a
     process whose console input broke the discipline pays with, and which
     is persistent, so that arm costs nothing to produce twice.

     CONSTANT IN THE STATUS ([ucons_pay_const]), which is the whole of what
     sh's exit stub needs: the leaf's premise is
     [ukn_pay N (-1) -∗ ukn_pay N xs ∧ ukn_pay N (-1)], and at a payload
     that does not read the status one resource answers both conjuncts.

     [T] IS A PARAMETER and not [AppEcho.echo_taint]: the program tier
     names no application.  The application instantiates it at the entry
     constructor, exactly as [UInitSh.init_sh_slot] takes its taint. *)
  Definition ucons_pay (cn : cons_names) (γ : gname) (T : iProp Σ)
    : Z -> iProp Σ :=
    fun _ => ((∃ n : nat, ucons_reader cn n ∗ upos_a γ n) ∨ T)%I.

  Global Instance ucons_pay_timeless cn γ T `{!Timeless T} (xs : Z) :
    Timeless (ucons_pay cn γ T xs).
  Proof. rewrite /ucons_pay. apply _. Qed.

  (* the payload does not read the status -- [UkRun.ukn_const]'s witness *)
  Lemma ucons_pay_const (cn : cons_names) (γ : gname) (T : iProp Σ)
      (x y : Z) :
    ucons_pay cn γ T x = ucons_pay cn γ T y.
  Proof. reflexivity. Qed.

  (* ...AND THE SAME FACT IN THE FORM THE GENERIC SLOT IS STATED AT: the
     payload IS the constant function at the resource it names, so a lemma
     indexed by [fun _ => R] applies here at [R] read off the kill status
     ([UexecExecMint.uslot_mint_pay], [UexecRet.uexec_wp_uslot]). *)
  Lemma ucons_pay_eta (cn : cons_names) (γ : gname) (T : iProp Σ) :
    (fun _ : Z => ucons_pay cn γ T (-1)) = ucons_pay cn γ T.
  Proof. reflexivity. Qed.

  (* the two constructors: the lender's, at the position it minted the
     pair at, and the tainted one's *)
  Lemma ucons_pay_tok (cn : cons_names) (γ : gname) (T : iProp Σ)
      (n : nat) (xs : Z) :
    ucons_reader cn n -∗ upos_a γ n -∗ ucons_pay cn γ T xs.
  Proof.
    iIntros "Hr Hp". rewrite /ucons_pay. iLeft. iExists n. iFrame "Hr Hp".
  Qed.

  Lemma ucons_pay_taint (cn : cons_names) (γ : gname) (T : iProp Σ)
      (xs : Z) :
    T -∗ ucons_pay cn γ T xs.
  Proof. iIntros "HT". rewrite /ucons_pay. by iRight. Qed.

  (* ...and what init reads off it at the reap: the token at a position it
     does not know, or the taint.  The payload's half of the pair is
     DROPPED -- the child that held the other half is gone, so nothing
     will ever agree against it again. *)
  Lemma ucons_pay_redeem (cn : cons_names) (γ : gname) (T : iProp Σ)
      (xs : Z) :
    ucons_pay cn γ T xs -∗ (∃ n : nat, ucons_reader cn n) ∨ T.
  Proof.
    rewrite /ucons_pay. iIntros "[Hl | HT]"; [| by iRight ].
    iDestruct "Hl" as (n) "[Hr _]". iLeft. iExists n. iExact "Hr".
  Qed.

  (* =================================================================== *)
  (*  §12  INIT'S ROUND: THE MINT BEFORE THE FORK, THE REDEEM AT WAIT     *)
  (*                                                                      *)
  (*  What init holds between two shells is the TOKEN or the taint --      *)
  (*  [ucons_pay]'s own body with the payload half of the position pair    *)
  (*  dropped, which is what [UserConsole.ucons_pay_redeem] hands back at  *)
  (*  the reap.  The restart head of init's loop carries exactly this, and *)
  (*  it is what makes the loop close: the shell that died gave it back.   *)
  (*                                                                      *)
  (*  THE PAIR IS MINTED PER CHILD.  Two shells must not share a [γ] --    *)
  (*  the dead one's half would still agree against the live one's -- so   *)
  (*  init allocates a fresh pair at the token's CURRENT position          *)
  (*  immediately before each fork ([UserConsole.upos_alloc]), pays        *)
  (*  [ucons_pay cn γ T (-1)] into [UkFork.wp_uk_ecall_fork]'s [Q (-1)]    *)
  (*  and lends [upos γ n] through its [Rc].                               *)
  (*                                                                      *)
  (*  THE TAINT ARM MINTS A PAIR TOO, at 0 and meaning nothing: sh's       *)
  (*  entry takes a position unconditionally ([ush_pstate_line]'s fourth   *)
  (*  conjunct), and a pair whose token is gone is exactly what a tainted  *)
  (*  process holds -- the number is still there and no longer says        *)
  (*  anything ([ush_read_recv_leaf]'s taint disjunct).                     *)
  (* =================================================================== *)
  Definition uinit_tok (cn : cons_names) (T : iProp Σ) : iProp Σ :=
    ((∃ n : nat, ucons_reader cn n) ∨ T)%I.

  (* the boot's own shape: init's entry is handed the token at position 0
     ([InitBoot.init_boot_bundle]'s input, threaded to init's run through
     [PinnedExec.pinned_exec_bundle]'s linear [Pay]) *)
  Lemma uinit_tok_0 (cn : cons_names) (T : iProp Σ) :
    ucons_reader cn 0%nat -∗ uinit_tok cn T.
  Proof.
    iIntros "Hr". rewrite /uinit_tok. iLeft. iExists 0%nat. iExact "Hr".
  Qed.

  (* THE MINT, once per round, immediately before the fork *)
  Lemma uinit_lend (cn : cons_names) (T : iProp Σ) (xs : Z) :
    uinit_tok cn T ==∗
    ∃ (γ : gname) (n : nat), ucons_pay cn γ T xs ∗ upos γ n.
  Proof.
    rewrite /uinit_tok. iIntros "[Hl | HT]".
    - iDestruct "Hl" as (n) "Hr".
      iMod (upos_alloc n) as (γ) "[Hp Hpa]".
      iModIntro. iExists γ, n. iFrame "Hp".
      iApply (ucons_pay_tok cn γ T n xs with "Hr Hpa").
    - iMod (upos_alloc 0%nat) as (γ) "[Hp _]".
      iModIntro. iExists γ, 0%nat. iFrame "Hp".
      iApply (ucons_pay_taint cn γ T xs with "HT").
  Qed.

  (* ...AND THE REDEEM, at the wait that reaps the shell: the escrow's
     payload comes back at the status the child exited with
     ([ChildTok.gen_pay]), and what init reads off it is the token again --
     at a position it does not know, which is why the next round's mint
     takes one from the token itself. *)
  Lemma uinit_redeem (cn : cons_names) (γ : gname) (T : iProp Σ) (xs : Z) :
    ucons_pay cn γ T xs -∗ uinit_tok cn T.
  Proof. rewrite /uinit_tok. iApply (ucons_pay_redeem cn γ T xs). Qed.

End UserConsole.

(* ===================================================================== *)
(*  3.  THE BRIDGE: the two spellings are ONE PROPOSITION                 *)
(*                                                                        *)
(*  Where the whole-system bundle is in scope -- the application's entry   *)
(*  constructors, and the discharge of sh's read leaf -- the program's     *)
(*  spelling and the ring's are convertible, because [Xv6G.xv6_uart] is    *)
(*  the one path from the bundle to [uartGhostG].  Stated (rather than     *)
(*  left to [rewrite]) so that a consumer names the fact instead of        *)
(*  unfolding two definitions, and so that a future divergence is a build  *)
(*  failure here and not a mismatch between two propositions that print    *)
(*  identically.                                                          *)
(* ===================================================================== *)
Section UserConsoleBridge.
  Context `{!riscvGS Σ, !xv6G Σ}.

  Lemma ucons_reader_eq (cn : cons_names) (n : nat) :
    ucons_reader cn n = ConsoleInv.cons_reader cn n.
  Proof. reflexivity. Qed.

  Lemma ucons_stored_lb_eq (cn : cons_names)
      (st : list (list mobs * bv 8)) :
    ucons_stored_lb cn st = ConsoleInv.cons_stored_lb cn st.
  Proof. reflexivity. Qed.

  Lemma ucons_swallow_eq (cn : cons_names) (fault : Prop)
      (sl : list (list mobs * bv 8)) (d dc : nat) :
    ucons_swallow cn fault sl d dc = ConsoleInv.cons_swallow cn fault sl d dc.
  Proof. reflexivity. Qed.
End UserConsoleBridge.
