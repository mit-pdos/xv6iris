(* ======================================================================= *)
(*  UartNames.v -- the UART's four ghost names, and nothing else.          *)
(*                                                                        *)
(*  Split out of WpUart.v on 2026-09-03 FOR THE BUILD DAG.  [FsCfg]'s      *)
(*  config record has one [fsc_uart : uart_names] field and needs no other *)
(*  thing WpUart defines; the profiler flags the edge as                   *)
(*  "weak -- 1.1% (1/94); symbols: uart_names".  A record of four [gname]s *)
(*  depends on nothing, so it does not belong behind a file that sits on   *)
(*  the device model.                                                      *)
(*                                                                        *)
(*  WpUart.v [Require Export]s this, so every consumer that reached        *)
(*  [uart_names] through it still does.                                    *)
(* ======================================================================= *)

From iris.base_logic.lib Require Import own.

(*  The UART's ghost names travel together in ONE record, so [dev_inv] and
    every client-facing resource take a single [γ : uart_names] rather than a
    fistful of gnames:

      un_acc   mono_list over [uart_acc]  -- the persistent accepted-byte
               history.  Grows only on a THR push; a lower bound
               [uart_sent γ l] is a permanent record that [l] was accepted.
      un_out   mono_list over [u_out]     -- the transmitted prefix.  Its
               lower bound is what carries a THRE observation forward across
               later device steps (see [uart_tx_still_empty], DevModel.v).
      un_tx    ghost_var halves over the accepted trace -- EXCLUSIVE
               ownership of the transmitter (see [uart_tx_own] in WpUart.v).
      un_dlab  dfrac_agree over DLAB -- freezable to a persistent fact.
      un_rxpush  mono_nat over the number of bytes the environment has ever
               pushed into the receive FIFO.  Its lower bound
               [uart_rx_pushed_lb] is what carries a "the FIFO was
               non-empty" observation from the LSR poll to the RHR pop.
      un_rxpop  ghost_var halves over the number of bytes ever REMOVED from
               the receive FIFO -- popped by an RHR read or flushed by an
               FCR write -- TOGETHER WITH THE LAST REMOVED BYTE'S HISTORY
               (the ANCHOR, [None] before the first pop).  The client's half
               is [uart_rx_tok], the receive token: exactly one hart holds
               it, so exactly one hart can shorten the FIFO.  The anchor is
               here rather than in the column because the queued histories'
               strict-prefix chain has to survive an EMPTY queue, and the
               token is the one thing that does.
      un_rxhi  ghost_var halves over the history of the last byte the
               CONSOLE RING stored ([WpUart.uart_rx_hi]).  One half rides in
               the PLIC payload beside the token, the other in
               [ConsoleInv.cons_res]; the pure clause between them is
               "everything the ring holds is at or before the last pop",
               which is what lets consoleintr's store know the byte it is
               filing is newer than every byte already in the ring.
      un_init  the one-shot that says uartinit's FCR flush has run.  Its
               exclusive half [uart_preinit] is what the PLIC invariant
               holds before the boot chain deposits the token; the
               persistent [uart_inited] is what plicinithart needs before it
               may enable the UART's interrupt source.                       *)
Record uart_names := UartNames {
  un_acc    : gname;
  un_out    : gname;
  un_tx     : gname;
  un_dlab   : gname;
  un_rxpush : gname;
  un_rxpop  : gname;
  un_rxhi   : gname;
  un_init   : gname;
  (* ---- THE INPUT LOG'S THREE (app-echo.md, lane CONS-IO), appended LAST
         so every literal construction site is an append.

     un_loghi  ghost_var halves over the history of the last input the
               kernel LOGGED -- every accepted byte, not only the ones the
               ring filed.  The exact twin of [un_rxhi]: one half rides
               [WpUart.uart_rx_writer] in the PLIC payload, one sits in the
               port invariant's input claim, and the pair is what makes
               "a byte is logged once, and the log is in arrival order" a
               theorem rather than a hope.
     un_log    mono_list mirror of the log itself, so that the console ring
               can keep a PERSISTENT lower bound on it beside its own
               entries and state the read contract's gap fact against it.
     un_deliv  ghost_var halves over the inputs the read path has CONSUMED.
               One half is in the port invariant beside the input claim,
               the other in [ConsoleInv.cons_res]: that pair is what ties
               the boundary's [dl] to the ring's consumed count, without
               which a read cannot say where its window begins.           *)
  un_loghi  : gname;
  un_log    : gname;
  un_deliv  : gname;
  (* un_logm   THE EXACT MIRROR of the log (lane CONS-IO, milestone B, the
               coordinator's ruling on F4).  A [ghost_var] PAIR, not a
               bound: one half sits in the port invariant's input claim
               beside [un_log]'s authority, the other in
               [ConsoleInv.cons_res].  A lower bound is not enough, because
               the ring's gap accumulator quantifies over the log's entries
               ABOVE the ring's top -- exactly the ones a bound cannot
               exclude -- so the ring must be able to say [L = pops] and
               not merely [L prefix_of pops].  Only consoleintr moves it,
               and it holds cons.lock and the port invariant together when
               it does.  APPENDED LAST. *)
  un_logm   : gname;
  (* un_arm    THE CONSOLEINTR ARM IN PROGRESS (redesign R2): a ghost_var
               PAIR, one half in the port invariant and one riding
               [WpUart.uart_rx_writer] in the PLIC payload.  Opening an arm
               agrees the two and advances both; a second arm before the
               first is closed is refuted by the agreement, which is the
               kernel stating the exclusion cons.lock already provides. *)
  un_arm    : gname;
  (* un_dlcnt  THE DELIVERED COUNT, AS A NUMBER THE RING CAN SEE (relax-d2,
               lane K2).  [un_deliv] carries the delivered LIST, and its
               kernel half travels with the reader's LEASE, not with the
               ring -- so the ring cannot bound the boundary's [dl] from
               above, which is exactly what a full-ring drop has to say.
               This [ghost_var nat] pair is that bound: one half sits in
               the Uart0 port invariant at [length (ch_dl H)], the other in
               [ConsoleInv.cons_res] under [n <= cur].  It moves at ONE
               site, consoleread's final release
               ([WpUart.uart_inv_cons_read]), where both halves are in
               hand.  APPENDED LAST. *)
  un_dlcnt  : gname;
}.

(* THE CONSOLE RING'S GHOST NAMES, here and not in [ConsoleInv.v] for the
   reason [uart_names] is here: [FsCfg]'s config record has to carry them,
   and it must not pull the console's own theory (hence the device model) in
   front of every file-system file.

     cn_uart  the receive side's names.  The ring's HIGH-WATER MARK is one
              of them ([un_rxhi] above): its partner half sits in the PLIC
              payload beside the receive token, which is where the popper
              is, and that pairing is what lets the ring order a byte it is
              handed against the bytes it already holds.
     cn_log   the APPEND-ONLY sequence of (history, byte) pairs the ring has
              committed -- what consoleread consumes, and what a read's
              receipt hands out a lower bound of.
     cn_rd    the CONSUMPTION CURSOR, a [ghost_var] over the number of bytes
              consumed.  One half is in the ring's resource; the other IS
              the console-reader token.
     cn_dirty the ONE-SHOT MARKER that says "a read without the token has
              moved the ring's consumed count past the token holder's
              cursor".  A [mono_nat]: the authority at 0 is the CLEAN token
              (exclusive, minted at boot beside the ring), the lower bound
              at 1 is the persistent, TIMELESS marker the ring's resource
              carries ([ConsoleInv.cons_dirty_lb]).  The marker and not the
              credential itself is what rides in [ConsoleInv.cons_res],
              because the credential is an arbitrary application [iProp] and
              a lock payload must be timeless; the credential lives in the
              escrow invariant beside the lock handle
              ([ConsoleInv.cons_cred_inv]).
     cn_era   the BOOT ERA the ring belongs to, a plain number fixed when
              the record is built (lane seccomp S2k, the follow-up ruling):
              every entry the ring stores or holds pending arrived in this
              era ([ConsoleInv.cons_era]).  A name and not a ghost because
              the ring is re-founded empty at every boot, so the era is a
              fact about the record, and [ConsoleInv] need not know which
              era is current -- the caps that do know
              ([SpecConsoleintr.console_caps], [SpecFileread.fileread_dev_caps])
              say [cn_era cn = S gen_id]. *)
Record cons_names := ConsNames {
  cn_uart  : uart_names;
  cn_log   : gname;
  cn_rd    : gname;
  cn_dirty : gname;
  cn_era   : nat;
}.
