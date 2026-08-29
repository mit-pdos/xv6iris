(* SpecUartwriteLoc.v -- uartwrite's LOCATED trace contract: the PARALLEL
   FORM of [SpecUartwrite.wp_uartwrite_sconf_body] (R10 -- the landed
   contract does not move, and this file adds a second one beside it).

   Worklist: claude-notes/projects/fs-syscall-specs.md, the console-write
   lane; the plan is [SpecSysWriteConsAU.v]'s "WHAT THE PROVER OWES" item 3,
   verbatim:

       premise [uart_sent γu tr0], post [uart_sent_from γu tr0
       (f <$> seq 0 n)] in place of the landed [uart_sent_sub γu
       (f <$> seq 0 n)].

   WHY THE LANDED FORM IS NOT ENOUGH, in one sentence (the spec file's item
   3 has the paragraph): two [uart_sent_sub] receipts DO NOT CONCATENATE --
   nothing orders one call's trace witness against another's -- so a caller
   that pushes its buffer in chunks (consolewrite, 32 bytes at a time) could
   only ever report a BAG of per-chunk sublists, which is weaker than what
   the machine does and exposes the bounce buffer's size for no consumer's
   benefit.  The located receipt places the bytes AFTER a trace bound the
   caller already holds, and located receipts chain
   ([UartSentLoc.uart_sent_from_chain]).

   THE SEED IS FREE: [uart_sent γu []] is [◯ML []], the unit of the mono-list
   algebra, minted from nothing by [UartSentLoc.uart_sent_nil], so a caller
   with no trace bound in hand loses nothing by this premise.  It is
   PERSISTENT, so handing it over costs the caller nothing either.

   EVERYTHING ELSE IS [SpecUartwrite.v] LINE FOR LINE -- the same binders,
   the same premises in the same order, the same threaded resources, the
   same stack budget, the same parking and lock-rank premises.  Read this
   file as the diff, which is: one binder ([tr0]), one premise resource
   ([uart_sent γu tr0]), one postcondition conjunct replaced.  The walk
   ([ProofUartwriteLoc.v]) is the matching diff against [ProofUartwrite.v].
   SpecUartwrite.v's header is the design of record for all of it and
   nothing of it is restated here. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvModelBytes RiscvPtsto.
Require Import InstrBytes.
Require Import RegFile.
Require Import RiscvExtras.
Require Import CalleeSaved KernelText.
Require Import IntrDefs.
Require Import WpNext.
Require Import LockRank.
Require Import ProcGeom CpuOwn.
Require Import FdSlots.
Require Import DiskPtsto WpUart.
Require Import UartTxInv.
Require Import UartSentLoc.   (* [uart_sent_from]: the located receipt *)
Require Import SpecUartwrite. (* the landed contract this parallels;
                                 [uartwrite_stack] *)
Require Import SchedCtx.
Require Export SwtchCtx.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import ProcAvail.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Require Import TsoCtx.
Import Defs.
Local Open Scope Z_scope.

Definition wp_uartwrite_loc_sconf_body `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
    (γu : uart_names) (γv : disk_names)
    (γs : list gname) (j : nat) (γlp : gname) (γl : gname)
    (m : regfile) (av : nat) (eb : bool)
    (n : nat) (f : nat -> bv 8) (dq : dfrac) (b : bool)
    (pidv : mword 32) (dqp : dfrac) (lks : gset string)
    (tr0 : list (bv 8)) :=
  let pcE : mword 64 := mword_of_int KernelSyms.uartwrite in
  let pj := proc_addr j in
  (* a0 = the buffer, a1 = the count *)
  let buf := m !!! Regidx (mword_of_int 10 : mword 5) in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  (* the process running here is proc j (sleep's linkage) *)
  (j < NPROC)%nat ->
  γs !! j = Some γlp ->
  m !!! Regidx (mword_of_int 11 : mword 5) = (mword_of_int (Z.of_nat n) : mword 64) ->
  (Z.of_nat n < 2 ^ 31)%Z ->
  (uartwrite_stack <= av)%nat ->
  eb = true ->
  locks_below lks "proc" ->
  sie_cap_gpr KT1 m av b pj -∗
  cpu_own 0%nat eb pj b lks -∗
  kernel_text -∗ pc_is pcE -∗
  dev_inv γu γv -∗
  is_txlock γl γu -∗
  p_pid pj ↦₄{dqp} pidv -∗
  (* the buffer, read-only *)
  ([∗ list] k ∈ seq 0 n, (pa_add buf k) ↦ₘ[KT1]{dq} f k) -∗
  (* the running-thread bundle (SpecSleep.v) *)
  procs_inv γs -∗
  (* ---- THE SEED: the ONE addition to the landed premises.  Any accepted
     trace bound the caller holds; [[]] is free ([UartSentLoc.uart_sent_nil]),
     and it is persistent, so handing it over costs nothing. ---- *)
  uart_sent γu tr0 -∗
  wp_next b pj (fun (CID : CpuId) =>
  ∀ (mf : regfile),
      ⌜callee_saved m mf⌝ -∗
      sie_cap_gpr KT1 mf av b pj -∗
      cpu_own 0%nat eb pj b lks -∗
      pc_is ret_tgt -∗
      ([∗ list] k ∈ seq 0 n, (pa_add buf k) ↦ₘ[KT1]{dq} f k) -∗
      p_pid pj ↦₄{dqp} pidv -∗
      (* THE LOCATED RECEIPT, in place of the landed [uart_sent_sub]: every
         byte of the buffer was accepted by the UART, IN ORDER, at positions
         after the seed.  [UartSentLoc.uart_sent_from_sub] projects it back
         to the landed vocabulary for a caller that does not chain. *)
      uart_sent_from γu tr0 (f <$> seq 0 n) -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type UARTWRITE_LOC.
  Parameter wp_uartwrite_loc_sconf :
    forall `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
      (γu : uart_names) (γv : disk_names) (γs : list gname) (j : nat) (γlp : gname) (γl : gname)
      (m : regfile) (av : nat) (eb : bool)
      (n : nat) (f : nat -> bv 8) (dq : dfrac) (b : bool)
      (pidv : mword 32) (dqp : dfrac) (lks : gset string)
      (tr0 : list (bv 8)),
      wp_uartwrite_loc_sconf_body γu γv γs j γlp γl m av eb n f dq b pidv dqp lks tr0.
End UARTWRITE_LOC.
