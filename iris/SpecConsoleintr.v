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
     consputc            [WpUart.dev_inv] ∗ [UartTxInv.is_txlock] ∗ a
                         [UartTxInv.uart_sent_sub] to extend
     wakeup              [procs_inv]

   ALL OF THEM ARE PERSISTENT, which is what makes the ripple cheap: the two
   lock credentials and the trace baseline are bundled here as
   [console_caps], with the two ghost NAMES existentially quantified, so a
   caller threading it gains a conjunct and NO new parameter.  uartintr's
   contract gains [console_caps], [SpecDevintr.devintr_caps] gains it, and
   every file that merely passes that bundle along changes by one name.

   [uart_sent_sub γu []] rather than a threaded [bs]: consoleintr's echo is
   of no interest to any caller, so there is nothing to thread -- the empty
   claim is the baseline each [consputc] call extends and then discards.
   Keeping it INSIDE the bundle rather than minting it from [dev_inv] is
   deliberate: minting costs a fupd that opens the device invariant, and the
   boot assembly that builds this bundle has the real [uart_sent] in hand
   anyway (consoleinit hands it back).

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
Require Import ConsoleInv.
From Kernel Require KernelSyms.
Require Import ProcAvail.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Require Import TsoCtx CtxMorphTac.

(* consoleintr's own frame (48 bytes = 6 slots) plus its deepest callee
   (wakeup, 18) is 24; this is that with slack.  consputc (16) and the two
   lock calls (10) are all shallower than wakeup. *)
Notation consoleintr_stack := (32%nat) (only parsing).
Section ConsoleCaps.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ}.

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
     which is where uartintr's RHR pop reads it from. *)
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
       uart_sent_sub γu [] ∗ uart_inited γu)%I.

  Global Instance console_caps_persistent `{XI : CurCtx} γu : Persistent (console_caps γu).
  Proof. rewrite /console_caps. apply _. Qed.

  (* the capabilities are two lock handles, so they ride any domination *)
  Global Instance console_caps_morph γu :
    CtxMorph (λ ξ, console_caps (XI := ξ) γu).
  Proof.
    rewrite /console_caps /UartTxInv.is_txlock.
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
    (hb : list mobs) (cb : bv 8) (hh : option (list mobs)) :=
  let rettgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  (consoleintr_stack <= K)%nat ->
  (* a0 carries the byte the environment pushed into the UART *)
  m !!! Regidx (mword_of_int 10 : mword 5)
    = (extend_value (n := 8) true (cb : mword 8) : mword 64) ->
  (* ...at the history [hb], which ends with exactly that arrival *)
  obs_ends_in hb cb ->
  (* ...and which is strictly newer than everything the ring holds *)
  ohist_ext hh hb ->
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
  wp_next b pme (fun (CID : CpuId) =>
  ∀ Mf : regfile,
      ⌜ callee_saved m Mf /\ (forall r : regidx, r ∈ dom (rf_to_gmap Mf)) ⌝ -∗
      sie_cap_gpr KT1 Mf K b pme -∗
      cpu_own lvl eb pme b lks -∗
      kernel_text -∗ pc_is rettgt -∗
      (∃ hh' : option (list mobs),
         uart_rx_hi γu (1/2) hh' ∗ ⌜ohist_le hh' (Some hb)⌝) -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type CONSOLEINTR.
  Parameter wp_consoleintr_sconf :
    forall `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ, !wchG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
       (γu : uart_names) (γv : disk_names) (m : regfile) (γs : list gname)
      (pme : mword 64) (lvl K : nat) (eb : bool) (b : bool) (lks : gset string)
      (hb : list mobs) (cb : bv 8) (hh : option (list mobs)),
      wp_consoleintr_sconf_body γu γv m γs pme lvl K eb b lks hb cb hh.
End CONSOLEINTR.
