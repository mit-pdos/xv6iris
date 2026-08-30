(* SystemUartAccepted.v -- THE CONSOLE SAFETY PROPERTY AT THE REAL IMAGE.

   [UartAccepted.run_out_accepted] is the pure tie: for every run of the
   machine from a powered-off, never-booted state, the current power
   cycle's [ObsUartOut] projection is a SUBLIST of [uart_acc] -- the bytes
   the kernel accepted into the UART.  This file states it beside the
   adequacy theorem's own conclusion at the xv6 image, which is where a
   reader of [claude-notes/projects/uart-trace.md] expects a trace property
   to be delivered: reducibility, the trace's shape ([ObsTrace.obs_wf]),
   and the acceptance tie, about ONE run.

   WHAT THIS IS AND IS NOT.

   * It IS the safety direction the owner ruled (uart-trace.md, ruling 5):
     "no unaccepted byte appears".  Every byte the host saw in this cycle
     was accepted by the driver, in the order the driver accepted it.
   * It is NOT "the bytes appear".  Acceptance is into the transmit FIFO;
     the wire is what the transmitter has actually driven, and a byte can
     be accepted and never sent (LOOP, an FCR clear, or simply a power loss
     before the drain).  That is liveness, and outside [wp_strong_adequacy]
     (uart-trace.md, ruling 5).
   * The statement is about the OPEN cycle at the reached state, and it
     holds at EVERY point of EVERY run (every prefix of an [nsteps] is an
     [nsteps]), so each completed cycle satisfied it while it was open.
     A statement quantified over the completed cycles OF THE FINAL TRACE
     would need each cycle's accepted history to survive its own PowerOff,
     which no ghost does -- see uart-trace.md's "Rejected" section.

   WHY NO LEDGER.  The acceptance content of the trace is a pure step
   invariant of the language and is proved as one ([UartAccepted.v]).  The
   trace LEDGER ([RiscvAdequacy.obs_ledger_at], [WpUart.
   uart_obs_permit_ledger]) is for facts a client's own ghosts carry across
   events -- and its two wands are quantified over an ARBITRARY
   [γ : uart_names] (see [SystemAdequacy.xv6_trace_adequacy]'s [Htx]/[Hrx]
   and [xv6_power_adequacy_gen]'s permit premise, [forall γ, ...]), so no
   client resource can be about THE ERA's UART ghosts at an event.  That is
   what blocks the remaining half of this lane -- turning a LOCATED RECEIPT
   ([UartSentLoc.uart_sent_from]) into the pure residue that
   [xv6_out_accepted_from_xv6Σ] below takes as a hypothesis.  It is the
   UART instance of uart-trace.md's open "identification gate" (the [P_era]
   chain's), and the ask is recorded there and in this lane's report. *)

From Stdlib Require Import ZArith List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.program_logic Require Import language.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import DevModel.
Require Import RiscvLang.
Require Import ObsTrace.
Require Import UartAccepted.
Require Import VirtioModel.   (* [v_disk] *)
Require Import FsImgDisk.     (* [fsimg_dk] -- the real image *)
Require Import SystemAdequacy.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------- *)
(* 1. THE EXPORT.  Adequacy's conclusion and the console safety property,   *)
(*    about the same run, at the real xv6 image.                           *)
(* ---------------------------------------------------------------------- *)

Corollary xv6_out_accepted_xv6Σ (g : gstate)
    (Hgen0 : g.(ggen) = 0%nat) (Hpow0 : g.(gpow) = false)
    (Hdisk : v_disk (g.(gdev).(dvirtio)) = FsImgDisk.fsimg_dk) :
  forall (n : nat) (κs : list mobs) t2 g2,
    nsteps (Λ := riscv_lang) n ([PowerLoopE : expr riscv_lang], g) κs (t2, g2) ->
    (* the machine never gets stuck ... *)
    (forall e2, e2 ∈ t2 -> reducible (Λ := riscv_lang) e2 g2)
    (* ... its observable history alternates PowerOn / console I/O /
       PowerOff, counts the boots and ties the open cycle to the wire ... *)
    /\ obs_wf κs g2
    (* ... and EVERY BYTE THE HOST SAW IN THIS CYCLE WAS ACCEPTED BY THE
       KERNEL, IN ORDER.  [uart_acc] is exactly the list the campaign's
       receipts ([WpUart.uart_sent], [UartSentLoc.uart_sent_from]) are
       lower bounds of. *)
    /\ obs_wire (open_seg κs) `sublist_of` uart_acc (duart g2.(gdev)).
Proof.
  intros n κs t2 g2 Hns.
  destruct (xv6_obs_wf_xv6Σ g Hgen0 Hpow0 Hdisk n κs t2 g2 Hns) as [Hred Hwf].
  split_and!; [exact Hred | exact Hwf |].
  exact (run_out_accepted n _ t2 g g2 κs Hpow0 Hgen0 Hns).
Qed.

(* ---------------------------------------------------------------------- *)
(* 2. THE COMPOSED READING, at a LOCATED receipt.                          *)
(*                                                                          *)
(*    A campaign receipt [UartSentLoc.uart_sent_from γu tr0 bs] -- the       *)
(*    bytes [bs] were accepted, in order, at positions strictly after an     *)
(*    accepted trace that had [tr0] as a prefix -- has a PURE RESIDUE at a   *)
(*    state: agreed against that era's [uart_sent_auth γu u] it says exactly *)
(*    the two hypotheses below about [uart_acc u].  Given the residue, the   *)
(*    trace splits at the seed and the two halves are located:               *)
(*                                                                          *)
(*      the console output of this cycle is [w1 ++ w2] where [w1] came out   *)
(*      of the seed and [w2] out of the window the receipt lives in --       *)
(*      the SAME window as [bs].                                            *)
(*                                                                          *)
(*    Read for a printf: if [tr0] is what had been accepted when init's      *)
(*    printf started and [bs] are the bytes it accepted, then nothing the    *)
(*    host sees after the printf's starting point can be a byte that was     *)
(*    not accepted after that point, and the outputs cannot outrun the       *)
(*    acceptance order.  It does NOT say the printf's bytes were seen.       *)
(*                                                                          *)
(*    THE HYPOTHESES ARE HYPOTHESES ON PURPOSE (uart-trace.md, ruling 3's    *)
(*    pattern: what a client cannot yet close, it assumes IN the statement). *)
(*    Closing them is the era-identification ask in this file's header.      *)
(* ---------------------------------------------------------------------- *)

Corollary xv6_out_accepted_from_xv6Σ (g : gstate)
    (Hgen0 : g.(ggen) = 0%nat) (Hpow0 : g.(gpow) = false)
    (Hdisk : v_disk (g.(gdev).(dvirtio)) = FsImgDisk.fsimg_dk) :
  forall (n : nat) (κs : list mobs) t2 g2,
    nsteps (Λ := riscv_lang) n ([PowerLoopE : expr riscv_lang], g) κs (t2, g2) ->
    forall tr0 bs : list (bv 8),
      tr0 `prefix_of` uart_acc (duart g2.(gdev)) ->
      bs `sublist_of` drop (length tr0) (uart_acc (duart g2.(gdev))) ->
      (forall e2, e2 ∈ t2 -> reducible (Λ := riscv_lang) e2 g2)
      /\ exists w1 w2,
           obs_wire (open_seg κs) = w1 ++ w2
           /\ w1 `sublist_of` tr0
           /\ w2 `sublist_of` drop (length tr0) (uart_acc (duart g2.(gdev)))
           /\ bs `sublist_of` drop (length tr0) (uart_acc (duart g2.(gdev))).
Proof.
  intros n κs t2 g2 Hns tr0 bs Hpre Hbs.
  destruct (xv6_obs_wf_xv6Σ g Hgen0 Hpow0 Hdisk n κs t2 g2 Hns) as [Hred _].
  split; [exact Hred|].
  exact (run_out_accepted_from n _ t2 g g2 κs tr0 bs Hpow0 Hgen0 Hns Hpre Hbs).
Qed.
