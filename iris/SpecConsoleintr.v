(* SpecConsoleintr.v -- the public interface of consoleintr, stated
   independently of its proof.

     void consoleintr(int c);

   consoleintr is xv6's console line-discipline: it takes cons.lock, edits the
   input line (kill-line, backspace, echo through consputc), stores the byte
   in cons.buf, wakes a blocked consoleread() when a whole line has arrived,
   and releases cons.lock.  @ KernelSyms.consoleintr = 0x800002bc.

   ---- THE CREDENTIAL, AND WHY IT IS ONE EXISTENTIAL BUNDLE -------------

   This contract used to be ASSUMED, and what the assumption hid was the
   ECHO: [consputc] reaches [uartputc_sync], which really does take tx_lock
   and write the THR, so a contract silent about the transmitter was
   asserting something false about the device.  A proof cannot be silent
   about it, so consoleintr asks for exactly what its four callees ask for:

     acquire / release   [ConsoleInv.is_conslock]
     consputc            [WpUart.dev_inv] ∗ [UartTxInv.is_txlock] ∗ the
                         ECHO'S JUSTIFICATION [cons_echo_shift] ∗
                         [SpecUartPutc.uart_base_word Uart0]
     wakeup              [procs_inv]

   ALL OF THEM ARE PERSISTENT, which is what makes the ripple cheap: the two
   lock credentials and the trace baseline are bundled here as
   [console_caps], with the two ghost NAMES existentially quantified, so a
   caller threading it gains a conjunct and NO new parameter.  uartintr's
   contract gains [console_caps], [SpecDevintr.devintr_caps] gains it, and
   every file that merely passes that bundle along changes by one name.

   [SpecUartPutc.uarts_words] rides in the bundle for the same reason the
   lock handles do.  Since XV6_REV 163d39b the driver reaches a port through
   `&uarts[uid]` and LOADS both of that element's immutable fields out of
   `.data` instead of spelling them as constants: consputc's callee needs the
   base, and uartintr's receive drain needs the hook word -- it is what
   decides the `if (u->rx)` guard STATICALLY.  All four words are persistent
   and depend on no ghost name, and putting them here means the call sites
   project what they need from a bundle consoleintr already has rather than
   threading new premises up through uartintr and devintr.  They are VA-tier
   points-to, so only the boot chain can mint them
   ([KMap.kmap_static_claims]) -- a driver cannot cross from the physical
   [UartsFields.uarts_pinned] form.

   AND IT IS BOTH PORTS' WORDS, not the console's alone, because this bundle
   is the interrupt path's ONE context-relative carrier: devintr calls the
   same uartintr at [Uart1], whose credential ([SpecDevintr.uart1_caps]) is
   rebuilt at a foreign context by a proof holding no domination and must
   therefore stay ξ-free.  See [SpecUartPutc.uarts_words].

   THE ECHO'S JUSTIFICATION RIDES THE BUNDLE (lane OUT-FUPD, F3), where the
   trace baseline [UartTxInv]'s retired sublist claim used to.  consputc now asks its
   caller for a CHAIN of view shifts over the bytes it will push
   ([WpUart.out_chain Uart0 (SpecConsputc.consputc_cs a0) Φ]), and
   consoleintr is called from the interrupt path with nothing of its own to
   pay it with: the echo is the APPLICATION's claim about its own input, so
   the justification is the application's, MINTED AT BOOT into the console
   environment and persistent so that every byte's echo re-uses it.  That
   is [cons_echo_shift] below.  consoleintr's arity does not move: the
   bundle keeps its shape and one conjunct is replaced.

   ---- THE ECHO'S BYTES ARE REPORTED (app-echo.md, E5/O4) ----------------

   The bare "∃ cs, these bytes went out" would be VACUOUS -- [cs = []] is a
   free witness -- so the claim is
   keyed on the HIGH-WATER MARK, which this contract already reports and
   which decides the arm: the incoming mark is strictly before [hb] (the
   premise [ohist_ext hh hb]), so [hh' = Some hb] holds exactly on the arm
   that FILED the byte, and that arm echoed [echo_of cb] and nothing else.
   The other arms leave the mark alone, and what they echo is [cons_echo]'s
   shape -- nothing, or a run of erase triples.  WHO pushed a byte is NOT
   invariant data: attribution is the application's private knowledge,
   established inside the view shift every UART output takes (lane
   OUT-FUPD).

   PINNING THE BYTES COST [SpecConsputc]'s POST ITS EXISTENTIAL: it now
   names which bytes each of its two arms pushes, which is what lets this
   one say [echo_of cb] rather than "something".  printk's own post is
   unaffected -- its format recursion drops the conjunct.

   [dev_inv] stays OUTSIDE the bundle: uartintr already holds it (its rx poll
   reads the device), so folding it in would make the caller's own hypothesis
   unreachable behind an existential pair of ghost names it does not know.

   WHERE IT COMES FROM: [ProofMain.mn_grp_printk], right after the
   consoleinit call that initializes both locks.  Both halves are
   [WpLock.newlock]s -- [is_txlock] over [UartTxInv.tx_res] (out of
   consoleinit's [lk_fresh] for tx_lock plus the transmitter token, both of
   which that block already held) and [is_conslock] over
   [ConsoleInv.cons_res] (out of consoleinit's own postcondition plus the
   ring's .bss cells, now a conjunct of [SpecMain.main_globals_raw]).  It
   then rides the [started] deposit to the secondaries.  Nothing is assumed;
   see claude-notes/projects/console.md.

   ---- WHAT THE CONTRACT NO LONGER ASKS ---------------------------------

   Two premises of the ASSUMED shape were vacuous and are gone: the register
   file's totality ([RegFile.rf_to_gmap_dom] proves it for every [m], with no
   hypothesis) and the non-null [mycpu_ret] of the entry [tp] -- nothing
   below consoleintr reads either.  Both were supplied at uartintr's call
   site by an [ltac:] that named the lemma; that is the tell. *)
From Stdlib Require Import ZArith List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre lifting.
From iris.base_logic.lib Require Import invariants ghost_var.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Operators_mwords SailStdpp.Values SailStdpp.MachineWord.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvPtsto RiscvLang ObsTrace.
Require Import ConsLog.   (* [echo_of], [cons_erase], [cons_echo]: the
   boundary's pure vocabulary, MOVED here from this file (lane CONS-IO). *)
Require Import RegFile.
Require Import RiscvExtras.
Require Import FdSlots.
Require Import ProcGeom.
Require Import InstrBytes KernelText.
Require Import LockRank.
Require Import CalleeSaved.
Require Import IntrDefs.
Require Import WpNext.
Require Import CpuOwn.
Require Import SchedCtx.
Require Import DiskPtsto WpUart.
Require Import UartTxInv.
Require Import SpecUartPutc.   (* [uart_base_word]: the .data word the
   console driver LOADS its MMIO base from, since XV6_REV 163d39b.
   Required explicitly -- SpecConsputc requires it, but Import is not
   transitive. *)
Require Import ConsoleInv.
From Kernel Require KernelSyms.
Require Import ProcAvail.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Require Import TsoCtx CtxMorphTac.

(* consoleintr's own frame (48 bytes = 6 slots) plus its deepest callee
   (wakeup, 18) is 24; this is that with slack.  consputc (16) and the two
   lock calls (10) are all shallower than wakeup. *)
Notation consoleintr_stack := (32%nat) (only parsing).
(* THE ECHOED BYTES, per arm (console.c:150-183).
   [echo_of], [cons_erase] and [cons_echo] MOVED to ConsLog.v (lane CONS-IO,
   ruling on F10), together with [SpecConsputc.consputc_bs]: they are the
   PURE vocabulary of the console UART's input log, which the boundary's
   contract is stated over and which sits below every Iris file that
   mentions this one.  Nothing about them changed.  What was here:
     [echo_of c]      -- the byte the default arm echoes ('\r' as '\n');
     [cons_erase c]   -- ^U, ^H and DEL, the three bytes the erase arms take;
     [cons_echo c cs] -- the SHAPE of one call's echo, per arm, with the
                         erase disjunct GUARDED by an erase byte. *)

Section EchoShift.
  (* ONLY [riscvGS], and deliberately: this is the obligation the
     APPLICATION discharges at the boot record ([App.xv6_app]'s
     [Happ_echo]), and App.v holds no [xv6G]/[bioslotG].  It sits in its own
     section so the statement can be made where the application record is.
     The [CurCtx] binder is kept and UNUSED -- nothing in the body is
     context-relative -- so that [console_caps]'s [CtxMorph] proof keeps
     seeing a ξ-indexed conjunct and not a constant.

     SINCE lane CONS-IO milestone C IT ALSO CARRIES [GenId]: the shift is
     paid at the ERA'S index [S gen_id] and takes the era STAMP on the
     byte's history as a premise, so the section needs the ambient
     generation.  App.v quantifies over it beside [CurCtx] ([Happ_echo]),
     which is exactly "the application pays for every era". *)
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId}.

  (* THE ECHO'S JUSTIFICATION, FIXED AT BOOT (lane OUT-FUPD, F3).
     What the application must supply once, at the console environment's
     mint, so that consoleintr can pay consputc's chain for EVERY byte it
     ever echoes.

     WHY IT TAKES THE BYTE'S TAG AND ITS HISTORY, and not just the bytes.
     The echo answers an input byte; whether echoing it keeps the
     application's output claim true depends on WHICH byte arrived and on
     what the application knows about the input so far -- and the only
     handles on that are the byte's own arrival history [h] (with
     [RiscvPtsto.obs_hist_lb h], the monotone witness that lets the shift
     place [h] against the claim's own witness) and the application's
     persistent claim about it, [RiscvPtsto.riscv_rx_tag h].  consoleintr
     already holds all three, so nothing new is threaded to it.

     WHY IT IS QUANTIFIED OVER THE PAYLOAD [Φ].  The ^U arm calls consputc
     once per erased glyph and the number is the ring's content, which this
     contract cannot name; a □-quantified builder pays each call.

     [cons_echo c cs] is the ARM's shape, and it is GUARDED BY THE BYTE (see
     below): an application that claims a transcript must be able to refute
     the erase arm from its own discipline, which it can only do if the
     kernel says the erase arm needs an erase byte. *)
  (* SINCE lane CONS-IO IT PAYS BOTH RESOURCES AT ONCE.  The output side is
     unchanged -- one link per echoed byte -- but the SAME shift now also
     files the accepted byte in the console UART's INPUT LOG, which is what
     makes the log say what the reader did NOT get.  [WpUart.cons_run] is the
     two together: the bytes first, the log entry last, and STOPPABLE at
     every prefix, because the kill-line arm's glyph count is the ring's
     content and the shift is fired before the loop runs.  [cs] is then an
     UPPER BOUND on what the arm will emit, and the arm closes the log at
     exactly what it did emit.

     EVERY ARM FIRES IT, including the two that echo nothing (a NUL byte, a
     full ring): a dropped byte is an accepted byte and the log records it
     at [cs = []], which is the disjunct a read's gap clause spends. *)
  (* THE ERA STAMP (lane CONS-IO milestone C).  Beside the tag premise the
     kernel hands the shift [⌜obs_boots h = S gen_id⌝]: the byte arrived in
     THIS era, and the era's number is readable from its own history.  It
     comes from the receive column, which files it beside the byte's tag at
     the rx push ([WpUart.uart_col]) and relays it through uartgetc and
     uartintr.  WHAT IT BUYS the application: every same-era fact it needs
     is PURE from the stamp -- a comparison of the byte's history against
     the ledger's own is unprovable inside a link, because the observation
     authority lives in the state interpretation and no link holds it. *)
  (* NO WINDOW TOKEN (redesign R2, option A).  The shift used to take a
     per-era exclusive the kernel lent the application, because the run was
     SPLIT -- the bytes went out through one claim and the log entry was
     filed later through another -- and nothing the application owned
     crossed the two fupds, so it could not refute interleavings cons.lock
     forbids (a second echo of one byte, an echo after the append, two
     appends).  The port now carries ONE claim over ONE console history
     whose [ch_arm] field IS the open arm, and every event steps it with
     the port invariant open: a second open, a byte after the close, a
     second close are refuted by [ConsLog.cons_ev_ok] on the kernel's side
     and by the history's own shape on the application's.  The exclusion
     cons.lock provides is thereby stated in the ghost state itself
     ([WpUart.uart_arm]), and no token has to stand in for it.

     THE ERA'S INDEX is still [S gen_id], for the reason the claim's is. *)
  Definition cons_echo_shift `{XI : CurCtx} : iProp Σ :=
    (□ ∀ (h : list mobs) (c : bv 8) (cs : list (bv 8)) (Φ : iProp Σ),
        ⌜obs_ends_in Uart0 h c⌝ -∗ ⌜obs_boots h = S gen_id⌝ -∗
        ⌜cons_echo c cs⌝ -∗
        riscv_rx_tag h -∗ obs_hist_lb h -∗
        Φ -∗ cons_link Uart0 (S gen_id) (ConsLog.EvOpen h c cs)
                       (cons_run (S gen_id) cs Φ))%I.

  Global Instance cons_echo_shift_persistent `{XI : CurCtx} :
    Persistent (cons_echo_shift (XI := XI)).
  Proof using . rewrite /cons_echo_shift. apply _. Qed.

  (* THE TRIVIAL APPLICATION'S DISCHARGE.  When the machine's console claim
     is [RiscvPtsto.cons_res_triv] every link is free, so the echo justifies
     itself. *)
  Lemma cons_echo_shift_triv `{XI : CurCtx} :
    riscv_cons_res = cons_res_triv -> ⊢ cons_echo_shift (XI := XI).
  Proof using .
    intros Hc. iIntros "!>" (h c cs Φ) "_ _ _ _ _ HΦ".
    iAssert cons_licence as "#Hlic"; [by iApply cons_licence_triv|].
    iApply (cons_link_of_licence with "Hlic").
    by iApply (cons_run_of_licence with "Hlic HΦ").
  Qed.

End EchoShift.

Section ConsoleCaps.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ}.
  (* the era's generation: [cons_echo_shift] is era-indexed (milestone C) *)
  Context `{GEN : GenId}.

  (* The two locks the console's interrupt path takes, plus the trace
     baseline its echo extends.  The ghost NAMES are existential: nothing
     above consoleintr names either lock, so binding them here keeps the
     bundle parameter-free in [γu] alone. *)
  (* [uart_inited γu] rides along, and it is the only row that is not a lock:
     it is the witness that the boot chain has parked the receive token in
     the PLIC invariant, which plicinithart needs before it may enable the
     UART's interrupt source and which every reader of a tagged byte needs
     to know the token exists at all.  It is persistent and context-free, so
     it costs the bundle one conjunct and the morphism nothing.
     [uart_dlab_off γu] is already here, inside [is_txlock] (UartTxInv.v) --
     which is where uartintr's RHR pop reads it from.  [uarts_words] REPLACES
     the bare [uart_base_word Uart0] in the last row, so the bundle keeps its
     arity and every destructuring pattern keeps its shape. *)
  (* THE CONS LOCK'S HANDLE AND NOT [ConsoleInv.is_conslock]: since the
     credential escrow moved into [is_conslock] (ConsoleInv.v, the
     timelessness split), that constant carries the application's [Wd], and
     consoleintr has nothing to do with it -- it STORES bytes, it does not
     read them, so the only thing it needs about the console is the ring's
     lock.  Naming the handle directly keeps the interrupt path free of the
     application parameter. *)
  Definition console_caps `{XI : CurCtx} (γu : uart_names) : iProp Σ :=
    (∃ (γtx γc : gname) (cn : cons_names),
       is_txlock γtx γu ∗
       WpLock.is_lock γc a_cons "cons"%string (cons_res_at cn) ∗
       ⌜cn_uart cn = γu⌝ ∗
       (* ...AND THE RING IS THIS ERA'S (lane seccomp S2k, the follow-up):
          what lets the store arm keep [ConsoleInv.cons_res]'s era clause
          with the byte's own stamp [obs_boots hb = S gen_id]. *)
       ⌜cn_era cn = S gen_id⌝ ∗
       cons_echo_shift ∗ uart_inited γu ∗
       uarts_words)%I.

  Global Instance console_caps_persistent `{XI : CurCtx} γu : Persistent (console_caps γu).
  Proof using . rewrite /console_caps. apply _. Qed.

  (* the capabilities are two lock handles, so they ride any domination *)
  Global Instance console_caps_morph γu :
    CtxMorph (λ ξ, console_caps (XI := ξ) γu).
  Proof using .
    rewrite /console_caps /UartTxInv.is_txlock /SpecUartPutc.uarts_words
            /cons_echo_shift.
    ctx_morph_solve.
  Qed.

End ConsoleCaps.

Definition wp_consoleintr_sconf_body `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ, !wchG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
     (γu : uart_names) (γv : disk_names) (m : regfile) (γs : list gname)
    (pme : mword 64) (lvl K : nat) (eb : bool) (b : bool) (lks : gset string)
    (* THE BYTE, ITS HISTORY AND THE RING'S HIGH-WATER MARK, as PARAMETERS
       and no longer under an existential: the post has to name the byte's
       own history ([hb]) to say where the mark ended up, and an existential
       premise cannot be named by a postcondition. *)
    (hb : list mobs) (cb : bv 8) (hh hg : option (list mobs)) :=
  let rettgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  (consoleintr_stack <= K)%nat ->
  (* a0 carries the byte the environment pushed into the UART *)
  m !!! Regidx (mword_of_int 10 : mword 5)
    = (extend_value (n := 8) true (cb : mword 8) : mword 64) ->
  (* ...at the history [hb], which ends with exactly that arrival *)
  obs_ends_in Uart0 hb cb ->
  (* ...IN THIS ERA (lane CONS-IO milestone C): the stamp the receive column
     filed beside the byte's tag, relayed by uartgetc and uartintr.  It is
     what lets the arms pay [cons_echo_shift], which is era-indexed. *)
  obs_boots hb = S gen_id ->
  (* ...and which is strictly newer than everything the ring holds *)
  ohist_ext hh hb ->
  (* ...and strictly newer than everything the kernel has LOGGED *)
  ohist_ext hg hb ->
  (* ...AND IT IS THE VERY NEXT INPUT AFTER THE ONE THE LOG'S MARK NAMES
     (relax-d2, lane K1).  The receive FIFO is drained in arrival order and
     one byte's arm closes before the next byte is popped, so the kernel
     knows WHICH keystroke it is handling: [hg]'s input number plus one.
     uartintr supplies it out of the pop's two numbers and the payload's
     own clause ([WpUart.uart_log_at] at the console port identifies the
     log's mark with the popper's anchor); the arms spend it at the log's
     OPEN and CLOSE, where it becomes [ConsLog]'s K1 clause -- "the log
     holds every earlier input of this era". *)
  trace_shape hb true ->
  WpUart.k1_next hg hb ->
  length γs = NPROC ->
  (* cons.lock's and wakeup's transient noff increments stay in int range *)
  (Z.of_nat lvl + 2 < 2 ^ 31)%Z ->
  (* acquire's order premise: every lock this hart already holds ranks below
     "cons"'s -- consoleintr acquires and releases cons.lock in the same
     call (BALANCED), so this contract is threaded on [lks] unchanged end to
     end.  "cons" (5) is also the LOWEST rank this call tree touches while
     the lock is held: [wakeup] (-> "proc", 11) surfaces its own
     [locks_below] premise, which the proof discharges from this one via
     [locks_below_mono]/[locks_below_union_singleton].  [consputc]'s public
     contract (SpecConsputc.v) does not surface an order premise at all --
     see the proof file's report for why that is not this function's
     obligation to supply. *)
  locks_below lks "cons" ->
  sie_cap_gpr KT1 m K b pme -∗
  cpu_own lvl eb pme b lks -∗
  kernel_text -∗ pc_is (mword_of_int KernelSyms.consoleintr) -∗
 procs_inv γs -∗
  dev_inv γu γv -∗
  console_caps γu -∗
  (* THE BYTE'S TAG (app-echo.md lane L5).  a0 carries a byte the environment
     pushed into the UART, and this is the history it arrived at together
     with the application's persistent claim about that history.  consoleintr
     FILES IT: the arm that appends the byte to the ring writes [Some h] into
     the tag column at the slot the byte lands in ([ConsoleInv.cons_row] is
     the coupling, [cons_tags] the column), which is how consoleread can hand
     each delivered byte's tag to its caller.  The three arms that do not
     append -- a NUL byte, a full ring, backspace/kill-line -- drop it, and
     a tag is persistent, so dropping costs nothing. *)
  riscv_rx_tag hb -∗
  (* ...AND THE LOWER BOUND ON THE RUN'S HISTORY AT IT.  Persistent, and what
     travels on into the ring's own column: a reader further down the line
     compares two of these to line two windows up. *)
  obs_hist_lb hb -∗
  (* ...AND THE WIRE AS IT STOOD WHEN THE BYTE ARRIVED (app-echo.md, lane
     CONS-IO, the coordinator's second C2 amendment).  A persistent bound on
     the transmitted prefix at THIS byte's own history, minted in the device
     thread's rx arm -- the one place where the trace coupling is in hand --
     and carried here in the receive column beside the tag.  The echo's link
     asks for it because the application has to place the transcript the
     discipline pins BELOW the wire inside the bytes the UART has ACCEPTED,
     and at a CPU MMIO step there is no trace authority to derive it from.
     Persistent, so relaying it costs the caller nothing. *)
  uart_out_lb γu (obs_wire Uart0 (open_seg hb)) -∗
  (* THE RING'S HIGH-WATER HALF, IN AND OUT (app-echo.md, lane CONS-CURSOR,
     C2).  [hh] is the newest history the ring already holds, and the premise
     [ohist_ext hh hb] -- supplied by the caller out of the pop's own two
     facts, the token's anchor being at or after the mark and strictly before
     this byte -- is what licenses the store to extend the ring's chain.  The
     mark comes back at [hb] if the byte was filed and unmoved if it was
     dropped, which is exactly [ohist_le hh' (Some hb)]; that is what
     re-establishes the PLIC payload's own clause at the new anchor.

     IT IS A RESOURCE AND NOT A PURE PREMISE because nothing else can say
     which of two histories came first: both are prefixes of one run, so two
     persistent bounds on them are comparable and no more, and the ring's own
     picture can be arbitrarily stale.  The exclusive pair decides it. *)
  uart_rx_hi γu (1/2) hh -∗
  (* THE LOG'S HIGH-WATER HALF, IN AND OUT (app-echo.md, lane CONS-IO).
     [hg] is the newest history the kernel has already LOGGED -- every
     accepted byte, not only the ones the ring filed -- and the premise
     [ohist_ext hg hb] below is what licenses this call's ONE append: with
     it, the log's own chain puts every logged history strictly before
     [hb], so the byte is logged once and the log stays in arrival order.
     It comes back at [Some hb] UNCONDITIONALLY, because every arm of the
     switch logs: a NUL byte and a full ring are accepted-and-dropped, the
     erase arms are accepted-and-edited, and the log records the choice.
     Like the ring's mark, it is a RESOURCE and not a pure premise: nothing
     else can say which of two histories came first. *)
  uart_log_hi γu (1/2) hg -∗
  (* THE ARM'S OWN HALF, AT [None] (redesign R2), the fourth thing the PLIC
     payload carries: no arm is open.  It is what the application's per-era
     window token used to stand for, except that it is the KERNEL's ghost
     and it says WHICH arm is open -- cons.lock's exclusion, in the ghost
     state.  It comes IN with the byte and goes OUT unconditionally, on
     every arm, because every arm opens and closes exactly one arm, so
     uartintr re-assembles the payload with it and the next byte's call has
     it again. *)
  uart_arm γu (1/2) None -∗
  wp_next b pme (fun (CID : CpuId) =>
  ∀ Mf : regfile,
      ⌜ callee_saved m Mf /\ (forall r : regidx, r ∈ dom (rf_to_gmap Mf)) ⌝ -∗
      sie_cap_gpr KT1 Mf K b pme -∗
      cpu_own lvl eb pme b lks -∗
      kernel_text -∗ pc_is rettgt -∗
      (* THE MARK AND THE ECHO, in one existential because the mark is what
         makes the echo's claim say anything: [hh' = Some hb] holds exactly
         on the arm that FILED the byte, and that arm echoed [echo_of cb]
         and nothing else.  Every other arm leaves the mark where it was
         and the echo claim is then only [cons_echo]'s shape. *)
      (* THE MARK.  The ECHO'S RECEIPT IS GONE (lane OUT-FUPD): what one
         call put on the wire is no longer reported here, because the
         application already justified it -- the bytes were paid for at the
         store, out of [console_caps]'s [cons_echo_shift], and the
         consequence lives in the console UART's invariant rather than in a
         receipt this contract hands back.  [hh' = Some hb] still marks the
         arm that FILED the byte, which is what the ring's order needs. *)
      (∃ hh' : option (list mobs),
         uart_rx_hi γu (1/2) hh' ∗ ⌜ohist_le hh' (Some hb)⌝) -∗
      (* ...AND THE LOG'S MARK, AT THIS BYTE.  No existential and no
         disjunction: the byte was logged, on every arm. *)
      uart_log_hi γu (1/2) (Some hb) -∗
      (* ...AND THE ARM'S HALF, BACK AT [None] (redesign R2): the close that
         ended this byte's log entry returned it. *)
      uart_arm γu (1/2) None -∗
      mWP (Loop : expr riscv_lang)) -∗
  mWP (Loop : expr riscv_lang).

Module Type CONSOLEINTR.
  Parameter wp_consoleintr_sconf :
    forall `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ, !wchG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
       (γu : uart_names) (γv : disk_names) (m : regfile) (γs : list gname)
      (pme : mword 64) (lvl K : nat) (eb : bool) (b : bool) (lks : gset string)
      (hb : list mobs) (cb : bv 8) (hh hg : option (list mobs)),
      wp_consoleintr_sconf_body γu γv m γs pme lvl K eb b lks hb cb hh hg.
End CONSOLEINTR.
