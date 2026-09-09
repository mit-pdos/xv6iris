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
               FCR write.  The client's half is [uart_rx_tok], the receive
               token: exactly one hart holds it, so exactly one hart can
               shorten the FIFO.
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
  un_init   : gname;
}.
