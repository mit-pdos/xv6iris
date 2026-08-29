(* SpecSysWriteConsAU.v -- sys_write's CONSOLE contract: the device arm
   that SpecSysWriteAU.v excluded by premise ("a console write is not an
   fs delta").  A STATEMENT FILE: definitions, structural lemmas, and a
   [Module Type] seal -- no walk, no proof against the machine.

   Design of record: the observation work of 2026-08-27 (commit 746c265c,
   RiscvLang.v section 3b', claude-notes/design/device.md and
   adequacy.md's trace paragraph) plus the UART ghost story
   (claude-notes/design/device.md, "the device-ghost design"; WpUart.v /
   UartTxInv.v).  The mold is SpecSysWriteAU.v -- same frame discipline
   (R10: a PARALLEL FORM beside [SpecSysWrite.wp_sys_write_sconf], the
   landed contract does not move), same seal -- with the AU side replaced
   by what the console's observable honestly is (below: THE OBSERVABLE,
   AND WHY THERE IS NO COMMIT BUNDLE).

   The driving consumer is init.c's printf -- the user library pushes ONE
   CHARACTER PER write() CALL -- and after it every verified user
   program's output; the receipt algebra below ([uart_sent_from_chain])
   is shaped for exactly that per-character composition.

   ==== THE OBSERVABLE: WHAT A CONSOLE WRITE CAN HONESTLY PROMISE ======

   The path is sys_write -> filewrite's FD_DEVICE arm ->
   devsw[CONSOLE].write = consolewrite -> either_copyin (32-byte bounce
   chunks) -> uartwrite -> one THR store per byte.  Three candidate
   observables, strongest first:

   (a) THE WIRE: the bytes appear in the machine's OBSERVATION TRACE
       ([RiscvLang.mobs]; [ObsUartOut b] is emitted on [uart_step]'s
       drain arm exactly when the byte reaches SOUT, and the cumulative
       ObsUartOut trace IS [u_wire] -- [uart_step_wire]).  NOT STATABLE
       HERE, twice over.  (i) It is FALSE AT RETURN: a THR store only
       QUEUES ([uart_write_thr] grows [u_tx]); the wire event is the
       DEVICE THREAD's own later drain step, and the semantics does not
       schedule that thread fairly -- at the syscall's return the bytes
       may sit in the tx FIFO, and a pointwise safety statement cannot
       promise the drain ever happens (that is a LIVENESS/fairness
       statement, out of wp_strong_adequacy's reach; adequacy.md item
       (d)/(b)).  (ii) It is UNSTATABLE IN-LOGIC today: the events are
       in the semantics, but [state_interp] IGNORES its observation
       argument, so no WP postcondition and no invariant can constrain
       the trace (adequacy.md: a trace-aware phi needs a
       kappa-consuming [state_interp] and every lifting rule
       rethreaded, or a Trillium-style refit).  No landed spec speaks
       the observation vocabulary; RiscvLang.v is its only occupant.

   (b) ACCEPTANCE: the bytes were accepted by the UART transmitter, in
       order.  THIS IS THE CHOSEN OBSERVABLE, and the landed ghost
       machinery carries it with no new ghost state: [uart_acc] (=
       [u_out ++ u_tx], every byte the UART has ACCEPTED -- invariant
       under the device's drain, grown only by a CPU THR push) has a
       [mono_list] history ghost [un_acc] inside [dev_inv], whose
       persistent lower bound [WpUart.uart_sent] / sublist form
       [UartTxInv.uart_sent_sub] is exactly what [SpecUartwrite]'s
       landed postcondition already delivers per uartwrite call.  This
       file states it at sys_write altitude in LOCATED form
       ([uart_sent_from] below): the caller seeds the call with any
       trace bound it holds ([uart_sent fsc_uart tr0] -- free at [tr0
       = []], [uart_sent_nil]) and the receipt places the accepted
       bytes AFTER that seed, which is what makes receipts from
       successive write() calls COMPOSE in order
       ([uart_sent_from_chain]) -- the printf consumer's whole need.

   (c) THE RETURN VALUE ONLY -- what the landed [SpecSysWrite] already
       gives ([filewrite_ret]'s blanket).  The fallback; strictly weaker.

   THE UPGRADE GAPS, precisely:

   * (b) -> (a) as a WHOLE-SYSTEM statement needs, in this order: (1)
     nothing for the ghost-physical tie -- [un_acc]'s authority sits in
     [dev_inv] over the physical [uart_acc], and at adequacy level
     [power_interp_era]/[dev_interp_at] already export the fabric, so a
     pointwise phi "every [uart_sent] bound is a prefix of
     [uart_acc (duart g2)]" is a two-line agreement TODAY; (2) the pure
     bridge is landed: [uart_step_wire] says the cumulative ObsUartOut
     trace IS [u_wire], and at any state with [u_tx = []] and MCR.LOOP
     off, accepted = transmitted = on the wire; (3) what is genuinely
     missing is the DRAIN -- "u_tx empties" is liveness (device-thread
     fairness), which no pointwise phi can supply -- and, if one wants
     the statement over the observation TRACE rather than the state,
     the kappa plumbing of adequacy.md.  So the honest whole-system
     corollary available after this contract is: at every reachable
     state, the receipt's bytes are a sublist of the accepted stream,
     and of the wire stream up to the (at most 16 + 1) bytes still in
     the tx path at that state.

   * (b) -> "the bytes are MY buffer's": blocked at copyin, not here.
     The written bytes come from USER memory and
     [SpecEitherCopyin.either_copyin_post]'s user arm returns the
     destination at an EXISTENTIAL content (a faulting copy has still
     written a prefix), so no kernel contract can name which bytes
     arrived (SpecConsolewrite's header records this; SpecSysWriteAU's
     "THE BYTES' SOURCE IS NOT NAMED" is the same stance on the inode
     arm).  Hence the receipts below are EXISTENTIAL byte strings of
     the right LENGTH, in order.  When copyin's spec can name a stable
     user page's content, a content-pinned parallel form (R10) can say
     WHICH bytes; nothing in this file's shape has to change for it --
     the receipt gains an equation, not a new resource.

   ==== WHY THERE IS NO COMMIT BUNDLE (contrast with SpecSysWriteAU) ===

   The mknod/write AU mold hands the prover a two-phase HOCAP commit per
   linearization instant because the caller must OBSERVE a borrowed
   authority it can also hold fractions of ([astate]/[nview] agreement).
   The console has no such abstract state: the observable is a
   PERSISTENT, MONOTONE history bound ([uart_sent] is a mono_list lower
   bound -- Persistent and Timeless, WpUart.v), the transmitter token
   [uart_tx_own] lives under the tx lock and is not caller-holdable
   across the call, and the bytes are existential (above), so an
   instant-level observation could tell the caller nothing a persistent
   receipt does not.  The receipt IS the agreement corollary: its
   located form pins the only thing an instant could pin -- WHERE in the
   accepted stream the bytes landed (after the caller's seed).  The
   per-byte instants (each THR store) therefore stay the prover's
   private business, and the arms deliver receipts directly.

   ==== THE ARMS =======================================================

   Under this contract's premises the landed blanket sharpens to THREE
   arms ([write_cons_arms]; [write_cons_arms_ret] recovers the blanket):

   * OK: [r = n] with [0 <= n] -- every requested byte was accepted, in
     order ([wcons_ok]: a receipt for a byte string of length [n]).
   * SHORT: [r] is the accepted COUNT, [0 <= r < n] -- either_copyin
     faulted mid-loop; the [r] bytes already pushed are real and
     receipted ([wcons_short]).  Note the DEVICE arm returns the partial
     COUNT where the inode arm returns -1: consolewrite has NO failing
     exit (SpecConsolewrite: a faulting copy BREAKS and the count
     already pushed is the answer), and a chunk is counted only after
     uartwrite pushed all of it, so the count IS the accepted length.
   * NEG: [r = -1] exactly when [n < 0] -- filewrite's own sign guard
     (XV6_REV 31f115a, the [srliw a5,a2,0x1f; c.bnez] at +0x1c,
     SpecFilewrite's decode notes), taken BEFORE the type dispatch;
     consolewrite never runs and nothing is promised about the trace.
     Every other -1 of the landed disjunction is REFUTED by the
     premises: argfd's by the [arg_fd] premise + the caller's [fd_st]
     fragment, the writable test's by the fragment's [true],
     filewrite's major-range/null-slot test's by [ma = CONSOLE] (in
     range, and [ConsoleInv.devsw_write_val_console] says the cell
     holds consolewrite).

   All three arms are PERSISTENT (receipts are history), so the caller
   keeps them forever -- unlike the inode AU's arms, which return live
   resources.

   WHAT THE ARMS DELIBERATELY DO NOT SAY: nothing about SYNCHRONOUS
   TRANSMISSION (gap (a): at return the bytes may sit in the tx FIFO --
   this file promises acceptance, never the wire); nothing about WHICH
   bytes (the copyin gap); nothing about CONTIGUITY (a sublist, not a
   segment: uartwrite takes and releases the tx lock around EACH byte
   and sleeps between bytes, so another hart's printk or another
   process's console write may interleave -- in the trace AND on the
   screen; that is what the real machine does); and no "and no more than
   [r] of your bytes" -- a negative trace claim is not in the
   lower-bound vocabulary (and with existential bytes it would say
   nothing).

   ==== WHAT THE PROVER OWES ===========================================

   1. The dispatch: argfd's success at [(fd, fv)] from the [arg_fd]
      premise + [fd_st] agreement (ProcInv.ofile_slot /
      FileInvDefs.fdstate_ok; [SpecFileread.fileread_pay_carve]'s
      outputs at [FdDevice]), the writable bit from the fragment, the
      recorded major = [ma] = CONSOLE, and the devsw cell at
      [a_devsw_write CONSOLE] holding consolewrite
      ([filewrite_devsw_of_console] + [filewrite_devsw_acc] +
      [ConsoleInv.devsw_write_val_console], as the landed ProofSysWrite
      already routes them).
   2. The NEG arm from filewrite's sign guard (decode: +0x1c), and that
      no other -1 path is reachable under the premises.
   3. A LOCATED parallel form of SpecUartwrite (R10 -- a new statement
      beside it, never an edit): premise [uart_sent gu tr0], post
      [uart_sent_from gu tr0 (f <$> seq 0 n)] in place of the landed
      [uart_sent_sub gu (f <$> seq 0 n)].  Provable from the landed
      walk's own ghost steps: the first acquire's token pins the entry
      trace [l0] with [tr0 `prefix_of` l0]
      ([UartTxInv.uart_tx_own_sent_prefix]), and every THR push appends
      strictly beyond it; the byte positions only grow across the
      release/sleep/reacquire cycles.  THIS IS THE ONE PLACE the
      black-box composition of landed specs falls short: two landed
      [uart_sent_sub] receipts do NOT concatenate (nothing orders one
      call's trace witness against another's), so with strictly landed
      callee posts the strongest sys-level statement would be a bag of
      per-32-byte-chunk sublist receipts -- weaker, and it would expose
      consolewrite's bounce-buffer size for no consumer's benefit.
   4. A located parallel form of SpecConsolewrite threading the seed
      through the chunk loop ([uart_sent_from_chain] is the glue; the
      count bookkeeping [i += nn] only after a full chunk push gives
      the arms' length equations).
   5. The frame plumbing exactly as the landed ProofSysWrite: the
      [P']/[M'] staging from either_copyin's user arm, [callee_saved],
      the a0 decode, [filewrite_fs_out] via [write_env_frame].

   ==== OPEN QUESTIONS FOR THE OWNER ===================================

   1. The SEED: the caller-supplied [uart_sent fsc_uart tr0] premise is
      free ([uart_sent_nil] at [[]]) and buys cross-call composition.
      Acceptable as the one console form, or is an unseeded sibling
      (post = plain [uart_sent_sub]) wanted for callers that will never
      chain?  (It is one [uart_sent_from_sub] away, so this file says
      no.)
   2. The content gap: schedule the copyin content seam (the
      SpecConsolewrite header's condition) so a content-pinned parallel
      form can name the bytes -- printf's theorem is "length and order"
      until then.  Same seam as SpecSysWriteAU's bss (its header's "THE
      BYTES' SOURCE IS NOT NAMED"), so one ruling covers both.
   3. The wire: is a whole-system console-output corollary (the
      pointwise phi of gap (a), with the drain caveat) worth a campaign
      now, or does it wait for the kappa plumbing so it can be said
      over the observation trace proper?
   4. The NEG arm states the sharp tie [r = -1 <-> n < 0] (given the
      premises).  Keep, or weaken to the landed blanket to keep the
      dispatcher's obligations one lemma smaller?

   BINDERS: one instance path per scope -- [fileG] is bound and the
   ambient [fscfg] (hence [fsc_uart]) resolves only through its fields
   (SpecFilewrite's duplicate-instance note, inherited).  Context binder
   lists are verbatim from the nearest landed sections:
   SpecSysWriteAU's for the frame, UartTxInv's for the receipt layer. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list functions bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import auth gmap frac dfrac.
From iris.algebra.lib Require Import mono_list.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap ghost_map own.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import InstrBytes.
Require Import RegFile.
Require Import RiscvExtras.
Require Import CalleeSaved KernelText KernelDataInv.
Require Import IntrDefs.
Require Import WpNext.
Require Import SpecPanic.
Require Import FdSlots.
Require Import ProcGeom.
Require Export SwtchCtx.
Require Import CpuOwn.
Require Import SchedCtx.
Require Import IrefSlots.
Require Import UserPtTree.
Require Import KvmSpec.
Require Import ProcPtOwn.
Require Import ProcInv.
Require Import FileInvDefs.
Require Import SpecArgfd.      (* [arg_fd]                                  *)
Require Import SpecSysRead.    (* [sys_rw_count]                            *)
Require Import ConsoleInv.     (* [CONSOLE], [devsw_table]                  *)
Require Import WpUart.  (* [uart_names], [uart_sent]              *)
Require Import Xv6Cameras.
Require Import UartTxInv.      (* [uart_sent_sub] -- the landed sublist
                                  receipt this file's located form refines *)
Require Import PipeInvDefs.    (* [pipe_rw_ret], under [filewrite_ret]      *)
Require Import SpecFilewrite.  (* [fwrite_names], [filewrite_ret], the env
                                  bundles                                  *)
Require Import SpecSysWrite.   (* the landed contract this file states a
                                  parallel form beside; [sys_write_stack]  *)
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import ProcAvail.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Require Import FsCfg.  (* [fscfg]: the fs configuration is AMBIENT --
                          [fsc_uart] is the console's ghost bundle        *)
Import Defs.

Local Open Scope Z_scope.

(* ===================================================================== *)
(*  1.  THE LOCATED-RECEIPT ALGEBRA (PURE CORE)                           *)
(* ===================================================================== *)

(* THE COMPOSITION FACT the whole file is shaped around: a sublist of one
   trace extension followed by a sublist of the next IS a sublist of the
   joint extension.  This is what per-call receipts compose by -- printf's
   one character per write() call concatenates to the whole message. *)
Lemma sublist_drop_chain {A : Type} (tr0 tr1 tr2 bs1 bs2 : list A) :
  tr0 `prefix_of` tr1 -> tr1 `prefix_of` tr2 ->
  bs1 `sublist_of` drop (length tr0) tr1 ->
  bs2 `sublist_of` drop (length tr1) tr2 ->
  ((bs1 ++ bs2)%list) `sublist_of` drop (length tr0) tr2.
Proof.
  intros H01 H12 Hb1 Hb2.
  destruct H12 as [ext ->].
  rewrite drop_app_le; last by apply stdpp.list_relations.prefix_length.
  rewrite drop_app_length in Hb2.
  by apply stdpp.list_relations.sublist_app.
Qed.

(* ===================================================================== *)
(*  2.  THE RECEIPT: ACCEPTED, IN ORDER, AFTER THE SEED                   *)
(* ===================================================================== *)

Section ConsReceipt.
  Context `{!riscvGS Σ, !xv6G Σ}.

  (* [uart_sent_from γu tr0 bs]: the bytes [bs] were accepted by the UART,
     in order, STRICTLY AFTER the accepted trace had [tr0] as a prefix --
     [UartTxInv.uart_sent_sub] refined by a LOCATION.  Persistent: it is a
     statement about history and survives everything.  The location is
     what makes receipts chain ([uart_sent_from_chain]); the plain sublist
     form is one projection away ([uart_sent_from_sub]). *)
  Definition uart_sent_from (γu : uart_names) (tr0 bs : list (bv 8))
      : iProp Σ :=
    (∃ tr : list (bv 8),
       uart_sent γu tr ∗ ⌜tr0 `prefix_of` tr⌝ ∗
       ⌜bs `sublist_of` drop (length tr0) tr⌝)%I.

  Global Instance uart_sent_from_persistent γu tr0 bs :
    Persistent (uart_sent_from γu tr0 bs).
  Proof. apply _. Qed.

  (* the reflexive receipt: nothing was accepted after a seed one holds *)
  Lemma uart_sent_from_refl (γu : uart_names) (tr0 : list (bv 8)) :
    uart_sent γu tr0 -∗ uart_sent_from γu tr0 [].
  Proof.
    iIntros "H". iExists tr0. iFrame "H". iPureIntro. split.
    - by exists []; rewrite app_nil_r.
    - apply stdpp.list_relations.sublist_nil_l.
  Qed.

  (* the projection to the landed vocabulary: located implies sublist *)
  Lemma uart_sent_from_sub (γu : uart_names) (tr0 bs : list (bv 8)) :
    uart_sent_from γu tr0 bs -∗ uart_sent_sub γu bs.
  Proof.
    iIntros "H". iDestruct "H" as (tr) "(Htr & %Hp & %Hs)".
    iExists tr. iFrame "Htr". iPureIntro.
    apply (transitivity Hs). apply stdpp.list_relations.sublist_drop.
  Qed.

  (* THE CHAIN: a caller who destructed call k's receipt -- learning its
     trace witness [tr1] (kept: [uart_sent] is persistent) and the two
     pure facts -- and seeded call k+1 with [tr1], concatenates.  This is
     the printf composition (header): per-character receipts fold into
     one in-order receipt for the whole message. *)
  Lemma uart_sent_from_chain (γu : uart_names)
      (tr0 tr1 bs1 bs2 : list (bv 8)) :
    tr0 `prefix_of` tr1 ->
    bs1 `sublist_of` drop (length tr0) tr1 ->
    uart_sent_from γu tr1 bs2 -∗
    uart_sent_from γu tr0 ((bs1 ++ bs2)%list).
  Proof.
    iIntros (Hp Hb) "H". iDestruct "H" as (tr2) "(Htr & %Hp2 & %Hs2)".
    iExists tr2. iFrame "Htr". iPureIntro. split.
    - by etrans.
    - by eapply sublist_drop_chain.
  Qed.

  (* THE SEED IS FREE: [◯ML []] is the unit of the mono-list algebra, so a
     caller with no trace bound in hand mints the empty one from nothing
     ([UartTxInv.uart_sent_sub_nil_free]'s move, delivering [uart_sent]
     itself so it can SEED the contract, not only conclude from it). *)
  Lemma uart_sent_nil (γu : uart_names) : ⊢ |==> uart_sent γu [].
  Proof.
    iMod (own_unit (mono_listUR (leibnizO (bv 8))) γu.(un_acc)) as "H".
    iModIntro.
    rewrite /uart_sent -(mono_list_lb_nil_is_unit (leibnizO (bv 8))).
    done.
  Qed.

End ConsReceipt.

(* ===================================================================== *)
(*  3.  THE ARMS                                                          *)
(* ===================================================================== *)

Section SysWriteConsAU.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ}.

  (* OK: every requested byte accepted, in order, after the seed.  The
     byte STRING is existential (header: the copyin gap); its LENGTH is
     the count. *)
  Definition wcons_ok (γu : uart_names) (tr0 : list (bv 8)) (n : Z)
      : iProp Σ :=
    (∃ bs : list (bv 8),
       ⌜Z.of_nat (length bs) = n⌝ ∗ uart_sent_from γu tr0 bs)%I.

  (* SHORT: either_copyin faulted mid-loop; the count already pushed is
     the answer AND the receipt's length.  [0 <= count] is the coercion's;
     [count < n] forces [0 < n], so no separate sign clause is needed. *)
  Definition wcons_short (γu : uart_names) (tr0 : list (bv 8)) (n : Z)
      (r : mword 64) : iProp Σ :=
    (∃ bs : list (bv 8),
       ⌜r = (mword_of_int (Z.of_nat (length bs)) : mword 64)⌝ ∗
       ⌜Z.of_nat (length bs) < n⌝ ∗
       uart_sent_from γu tr0 bs)%I.

  (* the armed disjunction the continuation receives, keyed on a0.  THREE
     arms (header: THE ARMS); the NEG arm is filewrite's own sign guard,
     the only -1 the premises leave reachable. *)
  Definition write_cons_arms (γu : uart_names) (tr0 : list (bv 8))
      (n : Z) (r : mword 64) : iProp Σ :=
    ((⌜r = (mword_of_int n : mword 64) /\ 0 <= n⌝ ∗ wcons_ok γu tr0 n)
     ∨ wcons_short γu tr0 n r
     ∨ ⌜r = (mword_of_int (-1) : mword 64) /\ n < 0⌝)%I.

  Global Instance wcons_ok_persistent γu tr0 n :
    Persistent (wcons_ok γu tr0 n).
  Proof. apply _. Qed.

  Global Instance wcons_short_persistent γu tr0 n r :
    Persistent (wcons_short γu tr0 n r).
  Proof. apply _. Qed.

  (* the receipts are HISTORY: the caller keeps the whole disjunction *)
  Global Instance write_cons_arms_persistent γu tr0 n r :
    Persistent (write_cons_arms γu tr0 n r).
  Proof. apply _. Qed.

  (* ------------------------------------------------------------------ *)
  (*  3a.  Sanity                                                         *)
  (* ------------------------------------------------------------------ *)

  (* the arms refine the landed blanket: [sys_write_ret]'s device-side
     disjunct is [filewrite_ret], and every arm lands inside it -- the
     dispatcher's bridge back to the landed calling convention *)
  Lemma write_cons_arms_ret γu tr0 n r :
    write_cons_arms γu tr0 n r -∗ ⌜filewrite_ret n r⌝.
  Proof.
    iIntros "[[%Hr _] | [H | %Hr]]".
    - iPureIntro. destruct Hr as [-> Hn]. by apply filewrite_ret_all.
    - iDestruct "H" as (bs) "(%Hr & %Hlt & _)". iPureIntro.
      rewrite /filewrite_ret /pipe_rw_ret. right.
      exists (Z.of_nat (length bs)). split; [exact Hr | lia].
    - iPureIntro. destruct Hr as [-> _]. apply filewrite_ret_m1.
  Qed.

  (* satisfiability at the degenerate count: the [n = 0] instance is
     constructible outright from a seed, so the seal cannot be vacuously
     strong at the trivial call *)
  Lemma wcons_ok_zero γu tr0 :
    uart_sent γu tr0 -∗ wcons_ok γu tr0 0.
  Proof.
    iIntros "H". iExists []. iSplitR; [done|].
    by iApply uart_sent_from_refl.
  Qed.

  Lemma write_cons_arms_zero γu tr0 :
    uart_sent γu tr0 -∗
    write_cons_arms γu tr0 0 (mword_of_int 0 : mword 64).
  Proof.
    iIntros "H". iLeft. iSplitR; [iPureIntro; split; [done | lia]|].
    by iApply wcons_ok_zero.
  Qed.

End SysWriteConsAU.

(* no [Typeclasses Opaque] here, deliberately: nothing above hides a
   big-op (optimization.md, "a big-op body is the predictor"), and the
   receipt is a match-free small existential -- the same ruling that
   keeps [SpecSysWriteAU.awrite_commit] transparent. *)

(* ===================================================================== *)
(*  4.  THE MACHINE CONTRACT: SpecSysWrite's frame + the receipt arms     *)
(* ===================================================================== *)

(* THE SHARED FRAME: [SpecSysWrite.wp_sys_write_sconf_body]'s premises and
   threaded resources VERBATIM (R10 -- the landed calling convention, not
   a new one; [SpecSysWriteAU.wp_sys_write_au_frame] is the same frame at
   the inode-descriptor premise), with the FD SIDE at the DEVICE
   constructor: the caller's fragment pins [FdOpen rb true (FdDevice ma)]
   -- open, WRITABLE, a device descriptor at major [ma] -- and the pure
   tie [ma = CONSOLE] selects the one entry consoleinit fills.  The
   fragment is returned UNCHANGED (a console write moves no fd state --
   not even an offset: the device arm never touches [f->off]).  The
   continuation carries the landed contract's [P']/[M'] staging verbatim
   (the copy leaf may fault a page in), and [ARMS] on the returned a0
   REPLACES the landed ⌜sys_write_ret⌝ -- each arm pins a0, and the
   [arg_fd] premise supplies the landed disjunction's witness
   ([write_cons_arms_ret]), so the blanket is implied. *)
Definition wp_sys_write_cons_frame
    `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
      !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId}
    (γf : gname)                    (* kalloc, the file table  *)
    (γs : list gname) (j : nat) (γlp : gname)    (* the running process    *)
    (fn : fwrite_names)                          (* the fs ghosts          *)
    (pidv : mword 32) (U : ustate)
    (v v2 : mword 64)                            (* syscall args 0, 2      *)
    (m : regfile) (K : nat) (eb : bool) (b : bool) (lks : gset string)
    (fd : nat) (fv : mword 64)                   (* the descriptor's slot  *)
    (rb : bool) (ma : Z)                         (* its mode bit and major *)
    (EXTRA : iProp Σ) (ARMS : mword 64 -> iProp Σ) :=
  let pcE : mword 64 := mword_of_int KernelSyms.sys_write in
  let pj := proc_addr j in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  (sys_write_stack <= K)%nat ->
  (j < NPROC)%nat ->
  γs !! j = Some γlp ->
  length γs = NPROC ->
  fwn_j fn = j ->
  fwn_procs fn = γs ->
  pv_tf (us_V U) !! tf_arg_idx 0 = Some v ->
  (exists v1 : mword 64, pv_tf (us_V U) !! tf_arg_idx 1 = Some v1) ->
  pv_tf (us_V U) !! tf_arg_idx 2 = Some v2 ->
  fwn_wp fn = ConsoleInv.devsw_write_val ->
  fwn_dqv fn = (fun _ => DfracDiscarded) ->
  eb = true ->
  (* THE FD SIDE's pure half: argument 0 names slot [fd] of the caller's
     own table, and the cell holds [fv] (non-zero by [arg_fd]'s shape) *)
  arg_fd v (pv_ofile (us_V U)) = Some (fd, fv) ->
  (* THE CONSOLE TIE: the descriptor's major is the one entry consoleinit
     fills -- what routes the dispatch to consolewrite and refutes the
     major-range / null-slot -1 *)
  ma = ConsoleInv.CONSOLE ->
  sie_cap_gpr KT1 m K b pj -∗
  cpu_own 0%nat eb pj b lks -∗
  kernel_text -∗ kernel_data -∗ pc_is pcE -∗
  panic_env -∗
  proc_priv γf pj pidv U -∗
  kalloc_env fsc_kalloc None -∗
  procs_inv γs -∗
  filewrite_fs_env γf fn -∗
  filewrite_dev_caps fn -∗
  ConsoleInv.devsw_table -∗
  (* THE FD SIDE's resource half: the caller's own fragment -- open,
     WRITABLE, a device descriptor at major [ma] *)
  fd_st (pv_fdg (us_V U)) fd (FdOpen rb true (FdDevice ma)) -∗
  (* ---- THE RECEIPT SIDE (the one addition to the landed premises) ---- *)
  EXTRA -∗
  wp_next true pj (fun (CID : CpuId) =>
    ∀ (mf : regfile) (r : mword 64) (P' : uptd) (M' : gmap Z (bv 8)),
      ⌜callee_saved m mf⌝ -∗
      ⌜uptd_ext (pv_upt (us_V U)) P'⌝ -∗
      ⌜mf !!! Regidx (mword_of_int 10 : mword 5) = r⌝ -∗
      sie_cap_gpr KT1 mf K b pj -∗
      cpu_own 0%nat eb pj b lks -∗
      pc_is ret_tgt -∗
      proc_priv γf pj pidv (upd_usM (us_upt U P') M') -∗
      kalloc_env fsc_kalloc None -∗
      filewrite_fs_out fn -∗
      (* the descriptor's state does not move: a console write touches
         neither the fd table nor an offset *)
      fd_st (pv_fdg (us_V U)) fd (FdOpen rb true (FdDevice ma)) -∗
      (* the armed post on the returned a0 (implies [sys_write_ret]) *)
      ARMS r -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

(* THE CONSOLE FORM.  The UART bundle is the AMBIENT [fsc_uart] -- the
   same one [filewrite_dev_caps]'s [dev_inv] speaks, so the receipts and
   the credential name one transmitter.  The count is the syscall's own
   argument reading ([sys_rw_count v2] -- the whole int range; the NEG
   arm answers the sign), and the seed [tr0] is whatever trace bound the
   caller holds ([[]] is free, [uart_sent_nil]). *)
Definition wp_sys_write_cons_au_body
    `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
      !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId}
    (γf : gname)
    (γs : list gname) (j : nat) (γlp : gname)
    (fn : fwrite_names)
    (pidv : mword 32) (U : ustate)
    (v v2 : mword 64)
    (m : regfile) (K : nat) (eb : bool) (b : bool) (lks : gset string)
    (fd : nat) (fv : mword 64) (rb : bool) (ma : Z)
    (tr0 : list (bv 8)) :=
  let n := sys_rw_count v2 in
  wp_sys_write_cons_frame γf γs j γlp fn pidv U v v2 m K eb b lks
    fd fv rb ma
    (uart_sent fsc_uart tr0)
    (write_cons_arms fsc_uart tr0 n).

(* ===================================================================== *)
(*  5.  THE SEAL                                                          *)
(* ===================================================================== *)

Module Type SYSWRITE_CONS_AU.
  Parameter wp_sys_write_cons_au :
    forall `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
             !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId}
      (γf : gname)
      (γs : list gname) (j : nat) (γlp : gname)
      (fn : fwrite_names)
      (pidv : mword 32) (U : ustate)
      (v v2 : mword 64)
      (m : regfile) (K : nat) (eb : bool) (b : bool) (lks : gset string)
      (fd : nat) (fv : mword 64) (rb : bool) (ma : Z)
      (tr0 : list (bv 8)),
      wp_sys_write_cons_au_body γf γs j γlp fn pidv U v v2 m K eb b lks
        fd fv rb ma tr0.
End SYSWRITE_CONS_AU.
