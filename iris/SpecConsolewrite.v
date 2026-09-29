(* SpecConsolewrite.v -- THE contract of consolewrite, stated independently
   of its proof.  Requires only the definitional layer -- never a
   whole-function proof file -- so every function proof can be checked in
   parallel.

     int consolewrite(int user_src, uint64 src, int n) {
       char buf[32];                      // a bounce buffer IN THE FRAME
       int i = 0;
       while (i < n) {
         int nn = sizeof(buf);
         if (nn > n - i) nn = n - i;
         if (either_copyin(buf, user_src, src + i, nn) == -1) break;
         uartwrite(0, buf, nn);
         i += nn;
       }
       return i;
     }

   @ KernelSyms.consolewrite, 72 instructions / 164 bytes (163d39b added one
   [c.li a0,0] for the port argument); a
   128-byte frame whose LOWEST 32 bytes are [buf] and whose top twelve slots
   hold ra/s0/s1 (saved unconditionally) and s2..s10 (SHRINK-WRAPPED onto the
   [n > 0] path).

   THE ALTITUDE IS THE UART'S, NOT THE CONSOLE'S.  consolewrite never touches
   [cons] -- no lock, no ring buffer, no index -- so [ConsoleInv.is_conslock]
   is NOT a premise here; that is consoleread's and consoleintr's credential.
   What this function needs is exactly what its two callees need:

   * [UartTxInv.is_txlock γl γu] and [WpUart.dev_inv γu γv], uartwrite's whole
     credential (SpecUartwrite.v) -- the callee wants port 0's bare
     [uart_inv], which [WpUart.dev_inv_uart] projects out of the bundle --
     plus, since XV6_REV 163d39b, [SpecUartPutc.uart_base_word Uart0]: the
     driver reaches the port through `&uarts[uid]` and LOADS the MMIO base
     out of `uarts[uid].base`, so that `.data` word has to be relayed from
     here.  IT IS THE VA-TIER FORM AND NOT [UartsFields.uarts_pinned]: an
     S-mode load leaf consumes the context tier, no law crosses from the raw
     physical one, and only the boot chain mints the crossing
     ([BootShared.uart_base_word_of_pinned]).  All three are persistent, so
     the loop carries them for free;
   * [proc_priv_core] and [kalloc_env], either_copyin's user arm (it reaches
     copyin, hence walkaddr and vmfault, hence kalloc), with the descriptor
     coming back EXTENDED ([uptd_ext]) -- writei's user arm does the same;
   * the running-thread bundle ([procs_inv]) and the hart-generic parking
     premise [eb = true] at [noff = 0], because uartwrite SLEEPS between
     bytes.  Nothing of this function's own state crosses that park: [buf]
     is in the frame, and the frame is not shared;
   * the SEED [UartTxInv.uart_sent γu tr0] -- the located half, below.

   THE BOUNCE BUFFER IS INVISIBLE HERE, and that is the point of it being a
   local: the 32 bytes are carved out of the four lowest slots of the frame
   this contract already charges for ([consolewrite_stack]), written by
   either_copyin and read by uartwrite, and no caller can name them.

   ---- WHAT IT PROMISES ABOUT THE OUTPUT -------------------------------

   THE RETURN VALUE RANGE, [0 <= r <= Z.max 0 n].  Not [-1]: this function
   has no failing exit -- a copy that faults BREAKS, and the count already
   pushed is what it answers.  ([Z.max 0 n] rather than [n] so the statement
   is true at a non-positive request too, where the loop never runs and the
   answer is 0; [PipeInvDefs.pipe_rw_ret] takes the same care, and
   [SpecFilewrite]'s [filewrite_ret] is where the two meet.)

   AND THE CALLER'S OWN CURSOR [Q (Z.to_nat r)] (lane OUT-FUPD), which is
   why the CHAIN is a premise: the contract threads the chain's residue
   through the chunk loop and reads the cursor off it at whichever exit is
   taken ([cons_out_chain_run] peels a chunk's links for [uartwrite],
   [cons_out_chain_cursor] reads the node).

   THE COUNT IS THE CURSOR'S INDEX, and that is what makes this contract
   worth stating.  consolewrite has NO failing exit, and [i += nn] runs only
   AFTER [uartwrite(0, buf, nn)] returned, i.e. only after all [nn] bytes of
   that chunk were accepted.  So at every exit the returned [r] is exactly
   the number of bytes this call handed the UART -- which is the equation
   [SpecFilewrite]'s console arms are stated on.

   ...AND THE CHAIN SAYS WHICH BYTES.  [SpecEitherCopyin.either_copyin_post]
   relays [SpecCopyin.copyin_got] on its success exit, so each chunk's bytes
   are pinned to the process's own image, and the chain's node at cursor [k]
   is quantified over exactly the byte [M] holds at [ua + k].  So a caller
   justifies ITS OWN bytes and nothing else -- which is what makes "init's
   printf printed THESE characters" stateable, now inside the application's
   own view shifts rather than in a receipt this layer hands back. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import InstrBytes.
Require Import RegFile.
Require Import RiscvExtras.
Require Import CalleeSaved KernelText.
Require Import IntrDefs.
Require Import WpNext.
Require Import LockRank.
Require Import ProcGeom CpuOwn.
Require Import UserPtTree.
Require Import KvmSpec.
Require Import ProcPtOwn.
Require Import FdSlots ProcInv.
Require Import FileInvDefs.
Require Import DevModel.
Require Import DiskPtsto WpUart.
Require Import UartTxInv.
Require Import SpecUartPutc.  (* [uart_base_word]: the callee LOADS its base *)
Require Import SchedCtx.
Require Export SwtchCtx.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import ProcAvail.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Require Import CtxIdDefs.
Import Defs.
Local Open Scope Z_scope.

Section ConsSentCnt.
  Context `{!riscvGS Σ, !xv6G Σ}.

  (* THE DEVICE-WRITE RECEIPT AT A COUNT is RETIRED (lane OUT-FUPD, F4)
     and what stands in its place is below: the caller's JUSTIFICATION for
     the bytes this call may push.  The content seam (RULING A;
     [SpecCopyin.ubytes_at]'s pointwise reading) survives inside it -- the
     node at cursor [k] is quantified over exactly the byte [M] holds at
     [ua + k] -- so a caller still justifies ITS OWN bytes and nothing
     else. *)
  (* ==================================================================== *)
  (*  THE CALLER'S JUSTIFICATION FOR THE BYTES THIS CALL MAY PUSH          *)
  (*  (app-echo.md, lane OUT-FUPD, F3), in place of the located receipt.   *)
  (*                                                                      *)
  (*  The located count receipt is RETIRED with the rest of the prefix     *)
  (*  vocabulary: the caller no longer receives a claim about what came    *)
  (*  out, it BRINGS the justification for it and gets its own payload     *)
  (*  back at the count that was pushed.                                   *)
  (*                                                                      *)
  (*  THE SHAPE IS [FsAbsWriteFire.awrite_chain]'S, and for the same       *)
  (*  reason: consolewrite copies 32 bytes at a time and BREAKS on a copy  *)
  (*  fault, so the caller cannot name the run in advance -- the node at   *)
  (*  cursor [k] is the PREFIX CURSOR [Q k] beside the step for the byte   *)
  (*  the image holds at [k], and the kernel picks which.  It is a per-    *)
  (*  BYTE chain and not a per-CHUNK one because port [Uart0]'s transmit   *)
  (*  lock is taken per byte: another hart's bytes can land inside a       *)
  (*  chunk.                                                              *)
  (*                                                                      *)
  (*  The byte at the cursor is PINNED against the image the caller lent   *)
  (*  ([SpecCopyin.ubytes_at]'s pointwise reading at one index), so the    *)
  (*  caller justifies ITS OWN bytes and nothing else.                     *)
  (* ==================================================================== *)
  (* ...AND AT THE ERA [k] (lane CONS-IO milestone C), which is the chain's
     FIRST argument now and the cursor's [j] the second-to-last: a link is
     era-indexed, so a chain of them is.  Every kernel statement below
     instantiates it at [S gen_id]; the argument is explicit because this
     section has no ambient generation and because the U tier states the
     chain for the era its own leaf runs in. *)
  Fixpoint cons_out_chain (k : nat) (M : gmap Z (bv 8)) (ua : mword 64)
      (Q : nat -> iProp Σ) (j cnt : nat) : iProp Σ :=
    match cnt with
    | O => Q j
    | S cnt' =>
        (Q j
         ∧ (∀ b : bv 8,
              ⌜M !! uint (add_vec_int ua (Z.of_nat j)) = Some b⌝ -∗
              out_link Uart0 k b (cons_out_chain k M ua Q (S j) cnt')))%I
    end.

  Lemma cons_out_chain_0 k M ua Q j : cons_out_chain k M ua Q j 0 ⊣⊢ Q j.
  Proof using . reflexivity. Qed.

  (* the caller reads its cursor off at any stop position: the node IS the
     cursor ([FsAbsWriteFire.awrite_chain_cursor]'s twin) *)
  Lemma cons_out_chain_cursor k M ua Q j cnt :
    cons_out_chain k M ua Q j cnt -∗ Q j.
  Proof using . destruct cnt; [by iIntros "$" | by iIntros "[$ _]"]. Qed.

  (* THE CHUNK BRIDGE, and the only reason this is a [Fixpoint] over a
     COUNT rather than a list: consolewrite pushes its bytes 32 at a time
     through [uartwrite], whose contract asks for a flat
     [WpUart.out_chain] over the run it is handed.  This peels that run off
     the head of the cursor chain and hands back the residue at the moved
     cursor.  The premise is [SpecCopyin.ubytes_at] at the bumped base,
     spelled out index-wise so that the induction needs no shift lemma. *)
  Lemma cons_out_chain_run (k : nat) (M : gmap Z (bv 8)) (ua : mword 64)
      (Q : nat -> iProp Σ) (bs : list (bv 8)) (j cnt : nat) :
    (length bs <= cnt)%nat ->
    (forall (d : nat) (c : bv 8), bs !! d = Some c ->
       M !! uint (add_vec_int ua (Z.of_nat (j + d))) = Some c) ->
    cons_out_chain k M ua Q j cnt -∗
    out_chain Uart0 k bs
      (cons_out_chain k M ua Q (j + length bs) (cnt - length bs)).
  Proof using .
    revert j cnt. induction bs as [| b bs IH]; intros j cnt Hlen Hat.
    - cbn [out_chain length]. rewrite Nat.add_0_r Nat.sub_0_r. by iIntros "$".
    - cbn [length] in Hlen. destruct cnt as [| cnt]; [lia |].
      iIntros "H". cbn [cons_out_chain]. iDestruct "H" as "[_ H]".
      iDestruct ("H" $! b with "[%]") as "H".
      { rewrite -(Nat.add_0_r j). apply (Hat 0%nat b). reflexivity. }
      cbn [out_chain length].
      replace (j + S (length bs))%nat with (S j + length bs)%nat by lia.
      iIntros (o acc) "Hlb Hres".
      iMod ("H" $! o acc with "Hlb Hres") as (o') "(Hlb' & Hres' & Hrest)".
      iModIntro. iExists o'. iFrame "Hlb' Hres'".
      iApply (IH (S j) cnt with "Hrest"); [lia |].
      intros d c Hd. rewrite Nat.add_succ_comm. exact (Hat (S d) c Hd).
  Qed.

  (* ...AND THE GENERIC WRITE'S OWN (lane OUT-FUPD).  An arbitrary process's
     [write(2)] on the console is paid out of the OUTPUT LICENCE its supply
     carries ([WpUart.cons_licence], [UexecExecInst.xv6_ssupply]): a licensed
     writer claims nothing about the input, so every node is the licence's
     one-byte step at the trivial payload -- AT EVERY ERA, because the
     licence is quantified over the index. *)
  Lemma cons_out_chain_of_licence (k : nat) (M : gmap Z (bv 8)) (ua : mword 64)
      (j cnt : nat) :
    cons_licence -∗ cons_out_chain k M ua (fun _ => True%I) j cnt.
  Proof using .
    iIntros "#Hlic". iInduction cnt as [| cnt] "IH" forall (j); [done|].
    cbn [cons_out_chain]. iSplit; [done|].
    iIntros (b) "_". iApply (out_link_of_licence k b with "Hlic").
    by iApply "IH".
  Qed.

End ConsSentCnt.

(* consolewrite's own frame is SIXTEEN slots ([c.addi16sp sp,sp,-128]: three
   saved registers, nine more shrink-wrapped, and the 32-byte [buf] in the
   four lowest), and its deepest callee is either_copyin at 56 -- uartwrite
   wants only 28 (it was 30; 163d39b's uartwrite has a smaller frame).

   16 + 56, WITH NO DISCOUNT FOR THE TRAP RESERVE.  piperead pays 62 for a
   52-slot copyout because its copy happens under the pipe lock, where
   interrupts are off and [IntrDefs.trap_res true] is spendable stack; this
   function holds NO lock, so both of its calls are made with interrupts on
   and the reserve is not available to them.  Raising [SpecFilewrite]'s
   [filewrite_stack] from [12 + K_writei] to [12 + 72] is the whole cost of
   that, and it stops there: nothing above sys_write reads the constant. *)
Notation consolewrite_stack := (72%nat) (only parsing).
Definition wp_consolewrite_sconf_body
    `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ, !wchG Σ, !fileG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
    (γa : gname) (γf : gname)
    (γs : list gname) (j : nat) (γlp : gname)
    (γu : uart_names) (γv : disk_names) (γl : gname)
    (m : regfile) (av : nat) (eb : bool)
    (pid : mword 32) (U : ustate) (n : Z) (b : bool) (lks : gset string)
    (Q : nat -> iProp Σ) :=
  let pcE : mword 64 := mword_of_int KernelSyms.consolewrite in
  let pj := proc_addr j in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  (* THE USER SOURCE, named (RULING A).  a1 was unconstrained and unnamed
     until the content seam; it is a [let], not a premise, so no caller
     moves. *)
  let uaddr : mword 64 := m !!! Regidx (mword_of_int 11 : mword 5) in
  (j < NPROC)%nat ->
  γs !! j = Some γlp ->
  length γs = NPROC ->
  m !!! Regidx (mword_of_int 10 : mword 5) = (mword_of_int 1 : mword 64) ->
  m !!! Regidx (mword_of_int 12 : mword 5) = (mword_of_int n : mword 64) ->
  (- 2 ^ 31 <= n < 2 ^ 31)%Z ->
  (consolewrite_stack <= av)%nat ->
  eb = true ->
  locks_below lks "proc" ->
  sie_cap_gpr KT1 m av b pj -∗
  cpu_own 0%nat eb pj b lks -∗
  kernel_text -∗ pc_is pcE -∗
  proc_priv_core pj pid U -∗
  kalloc_env γa None -∗
  dev_inv γu γv -∗
  (* the `.data` word the callee LOADS its MMIO base out of (163d39b), at
     the VA tier an S-mode load leaf consumes *)
  uart_base_word Uart0 -∗
  is_txlock γl γu -∗
  procs_inv γs -∗
  (* ---- THE CALLER'S OUTPUT JUSTIFICATION (lane OUT-FUPD), in place of the
     trace seed: one node per byte the call may push, each carrying the
     caller's own payload at that count. ---- *)
  cons_out_chain (S gen_id) (us_M U) uaddr Q 0%nat (Z.to_nat n) -∗
  wp_next true pj (fun (CID : CpuId) =>
  ∀ (mf : regfile) (r : Z) (P' : uptd) (k' : nat),
      ⌜callee_saved m mf⌝ -∗
      ⌜uptd_ext_sz (pv_sz (us_V U)) (pv_upt (us_V U)) P'⌝ -∗
      ⌜(0 <= r <= Z.max 0 n)%Z⌝ -∗
      (* ...AND A SHORT ANSWER CARRIES ITS REASON (lane TRAP-ROWS, T1).
         The loop has exactly ONE break -- [either_copyin(...) == -1] -- so
         a return below the request happened because a byte of the run at
         or after the cursor is on a page the kernel could not read
         through.  Relayed from [SpecEitherCopyin.either_copyin_post]'s
         failing arm and restated at the ENTRY descriptor
         ([UserPtTree.uva_rmapped_mono] across the rounds' extensions).
         THE OFFSET IS NOT THE CURSOR: the chunk the break happened in is
         up to 32 bytes wide and copyin walks it a page at a time, so what
         the code gives is "some byte at or after [r] and before [n]".  A
         caller that owns its whole buffer refutes the arm anyway. *)
      ⌜(r < n)%Z ->
       exists d : nat, (r <= Z.of_nat d)%Z /\ (Z.of_nat d < n)%Z /\
         ~ uva_rmapped (pv_upt (us_V U))
             (uint (add_vec_int uaddr (Z.of_nat d)))⌝ -∗
      ⌜mf !!! Regidx (mword_of_int 10 : mword 5) = (mword_of_int r : mword 64)⌝ -∗
      (* THE EVENT COUNTER (permit sweep L1b): the loop lends the block's counter to either_copyin, which may step it,
         so the block comes back at a count at least the one it left at *)
      ⌜(pv_ev (us_V U) <= k')%nat⌝ -∗
      sie_cap_gpr KT1 mf av b pj -∗
      cpu_own 0%nat eb pj b lks -∗
      pc_is ret_tgt -∗
      proc_priv_core pj pid (us_upt (upd_usV U (upd_ev (us_V U) k')) P') -∗
      (* THE RECEIPT, at the returned count: [r] bytes accepted, in order,
         after the seed, AND THEY ARE THE BYTES AT [a1] in the image the
         caller lent (RULING A).  Persistent -- the caller keeps it forever.
         [us_M U] is the INPUT image and stays the right one to state it
         against: consolewrite only READS user memory, and the pages a copy
         faults in were already in the view. *)
      (* THE CALLER'S OWN PAYLOAD AT THE COUNT THAT WAS PUSHED, where the
         located receipt used to be: what the bytes MEAN is the caller's
         business now, established inside the shifts it supplied. *)
      Q (Z.to_nat r) -∗
      mWP (Loop : expr riscv_lang)) -∗
  mWP (Loop : expr riscv_lang).

Module Type CONSOLEWRITE.
  Parameter wp_consolewrite_sconf :
    forall `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ, !wchG Σ, !fileG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
      (γa : gname) (γf : gname) (γs : list gname) (j : nat) (γlp : gname)
      (γu : uart_names) (γv : disk_names) (γl : gname)
      (m : regfile) (av : nat) (eb : bool)
      (pid : mword 32) (U : ustate) (n : Z) (b : bool) (lks : gset string)
      (Q : nat -> iProp Σ),
      wp_consolewrite_sconf_body γa γf γs j γlp γu γv γl m av eb pid U n b lks Q.
End CONSOLEWRITE.
