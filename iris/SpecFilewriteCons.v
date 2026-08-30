(* SpecFilewriteCons.v -- filewrite's LOCATED CONSOLE contract on the
   FD_DEVICE arm: [SpecFilewrite.wp_filewrite_sconf_body] VERBATIM, with the
   descriptor's state pinned to [FdDevice ma] at [ma = CONSOLE], a trace seed
   added, and the return-value clause replaced by
   [SpecSysWriteConsAU.write_cons_arms].

   Worklist: claude-notes/projects/fs-syscall-specs.md, the console-write
   lane.  A PARALLEL FORM beside [SpecFilewrite.FILEWRITE] -- R10: that file
   does not move, and a caller that wants the landed blanket keeps calling
   the landed contract.  The mold is [SpecFilewriteAU.v], the inode arm's
   parallel form: same three edits, in the same places, for the same reason.

   ==== WHY THE SEAM IS AT FILEWRITE ====================================

   Because the DISPATCH is filewrite's: sys_write hands a descriptor down,
   and it is filewrite that reads [f->type], reads [f->major], indexes
   [devsw[major].write] and calls through the cell
   ([ConsoleInv.devsw_write_val_console] is what says the cell holds
   consolewrite).  Above that seam there is nothing to prove about the
   console but relaying; below it there is nothing to dispatch.  So this
   contract is exactly "the device arm, at the console major, with the
   receipt relayed", and [SpecSysWriteConsAU.SYSWRITE_CONS_AU] is one shell
   above it.

   ==== WHAT THE PREMISE PINS, AND WHAT IT BUYS =========================

   [st = FdOpen rb true (FdDevice ma)] with [ma = CONSOLE] -- open,
   WRITABLE, a device descriptor at the one major consoleinit fills.  Four
   consequences, all of them removals:

   - [filewrite_env] / [filewrite_env_out] reduce to [filewrite_dev_env fn
     ma] -- the devsw cell plus [filewrite_dev_caps] (the device fabric and
     the tx lock, i.e. consolewrite's whole credential).  The inode and pipe
     arms are out of this contract's domain BY PREMISE;
   - the [f->writable == 0] early return cannot fire
     ([FileInvDefs.fdstate_ok] ties the state to the cell the [lbu] reads);
   - the major-range test cannot fire ([CONSOLE] is 1 and the test is
     [9 < major]), and neither can the null-slot test -- but only because
     the second premise below PINS the cell: [filewrite_dev_env] states the
     honest disjunction "null or consolewrite", and a null slot returns -1
     at +0x12a, which no arm here admits.  The pin is discharged at the call
     site from the devsw table ([ConsoleInv.devsw_write_val_console]);
   - so the ONLY [-1] left is filewrite's own sign guard at +0x1c
     (XV6_REV 31f115a's [srliw a5,a2,0x1f ; c.bnez]), which is the NEG arm
     of [write_cons_arms] -- and the remaining arms are the device path's
     OK and SHORT, because consolewrite has NO failing exit.

   THE COUNT IS THE RECEIPT'S LENGTH, straight out of the callee: the
   FD_DEVICE arm returns consolewrite's own return value untouched (no
   offset, no re-read, no clamp), and
   [SpecConsolewriteLoc.cons_sent_cnt] says that value IS the number of
   bytes the UART accepted after the seed.  The two bridge lemmas at the
   bottom of this file are that step, and they are all the prover of this
   contract needs beyond the landed walk.

   BINDERS: [SpecFilewrite]'s section list VERBATIM (which is
   [SpecFilewriteAU]'s) -- [fileG] is bound and the ambient [fscfg] (hence
   [fsc_uart]) resolves only through its fields. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list functions bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import auth gmap frac dfrac.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap ghost_map.
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
Require Import ConsoleInv.
Require Import Xv6Cameras.
Require Import WpUart.      (* [uart_names], [uart_sent]           *)
Require Import SpecFilewrite.   (* the landed contract this parallels       *)
Require Import SpecConsolewriteLoc.   (* [cons_sent_cnt]: the callee's post *)
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import ProcAvail.
Require Import Xv6G.
Require Import FsCfg.
Require Import SpecSysWriteConsAU.   (* [write_cons_arms], [wcons_ok/short] *)
Import Defs.
Require Import TsoCtx.

Local Open Scope Z_scope.

(* [SpecFilewrite.wp_filewrite_sconf_body], premise for premise and resource
   for resource; the four edits are marked. *)
Definition wp_filewrite_cons_body
    `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ, !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
    (γf : gname)                    (* kalloc, the file table  *)
    (γs : list gname) (j : nat) (γlp : gname)    (* the running process     *)
    (k : nat) (q : Qp) (st : fdstate)            (* the borrowed reference  *)
    (fn : fwrite_names)                          (* the heavy arms' ghosts  *)
    (pidv : mword 32) (U : ustate)
    (m : regfile) (K : nat) (eb : bool) (n : Z) (b : bool) (lks : gset string)
    (rb : bool) (ma : Z)                         (* the descriptor's mode
                                                    bit and its major       *)
    (tr0 : list (bv 8)) :=
  let pcE : mword 64 := mword_of_int KernelSyms.filewrite in
  let pj := proc_addr j in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  (filewrite_stack <= K)%nat ->
  (k < NFILE)%nat ->
  (j < NPROC)%nat ->
  γs !! j = Some γlp ->
  length γs = NPROC ->
  fwn_j fn = j ->
  fwn_procs fn = γs ->
  m !!! Regidx (mword_of_int 10 : mword 5) = fnode k ->
  m !!! Regidx (mword_of_int 12 : mword 5) = (mword_of_int n : mword 64) ->
  - 2 ^ 31 <= n < 2 ^ 31 ->
  (* EDIT 1: THE DESCRIPTOR IS AN OPEN, WRITABLE DEVICE AT MAJOR [ma].  The
     pipe, inode and panic arms are out of this contract's domain by
     premise. *)
  st = FdOpen rb true (FdDevice ma) ->
  (* EDIT 2: THE CONSOLE TIE.  [ma] is the one entry consoleinit fills, which
     is what routes the dispatch to consolewrite and refutes the major-range
     -1 ([CONSOLE] is 1, and the test is [9 < major]).
     THE SECOND HALF IS NOT DECORATION: [filewrite_dev_env] carries the
     honest DISJUNCTION "the slot is null or it is consolewrite"
     ([ConsoleInv.devsw_write_val_cases]), and a null slot is a -1 return at
     +0x12a that no arm of [write_cons_arms] admits.  So the cell's value has
     to be pinned, and this is where.  A caller discharges it from the table
     it already owns: [fwn_wp fn = ConsoleInv.devsw_write_val] (the
     [filewrite_devsw]/[devsw_table] premise every consumer of this cone
     carries) plus [ma = CONSOLE] plus
     [ConsoleInv.devsw_write_val_console] -- which is exactly what
     [ProofSysWriteConsAU] does, in one [assert]. *)
  ma = ConsoleInv.CONSOLE ->
  fwn_wp fn ma = (mword_of_int KernelSyms.consolewrite : mword 64) ->
  eb = true ->
  locks_below lks "log" ->
  sie_cap_gpr KT1 m K b pj -∗
  cpu_own 0%nat eb pj b lks -∗
  kernel_text -∗ kernel_data -∗ pc_is pcE -∗
  panic_env -∗
  file_ref γf k q st -∗
  proc_priv_core pj pidv U -∗
  kalloc_env fsc_kalloc None -∗
  procs_inv γs -∗
  filewrite_env γf fn st -∗
  (* EDIT 3: THE SEED.  Any accepted-trace bound the caller holds; [[]] is
     free ([SpecSysWriteConsAU.uart_sent_nil]), and it is persistent.  The
     UART bundle is the AMBIENT [fsc_uart] -- the same one
     [filewrite_dev_caps]'s [dev_inv] speaks, so the receipt and the
     credential name one transmitter. *)
  uart_sent fsc_uart tr0 -∗
  wp_next true pj (fun (CID : CpuId) =>
  ∀ (mf : regfile) (r : mword 64) (P' : uptd),
      ⌜callee_saved m mf⌝ -∗
      ⌜uptd_ext_sz (pv_sz (us_V U)) (pv_upt (us_V U)) P'⌝ -∗
      (* EDIT 4: the armed post REPLACES [⌜filewrite_ret n r⌝] -- each arm
         pins [r], so the landed blanket is implied
         ([SpecSysWriteConsAU.write_cons_arms_ret]). *)
      ⌜mf !!! Regidx (mword_of_int 10 : mword 5) = r⌝ -∗
      sie_cap_gpr KT1 mf K b pj -∗
      cpu_own 0%nat eb pj b lks -∗
      pc_is ret_tgt -∗
      file_ref γf k q st -∗
      proc_priv_core pj pidv (us_upt U P') -∗
      filewrite_env_out fn st -∗
      write_cons_arms fsc_uart tr0 n r -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

(* ===================================================================== *)
(*  THE CALLEE'S POST, IN THIS CONTRACT'S VOCABULARY                      *)
(* ===================================================================== *)

(* The two spellings of the located receipt --
   [SpecSysWriteConsAU.uart_sent_from], stated at syscall altitude where its
   consumer reads it, and [UartSentLoc.uart_sent_from], stated at the
   transmitter invariant where its producers live -- are THE SAME TERM at
   the same context (UartSentLoc.v's header says why there are two).  These
   two lemmas are where that is checked, and they are the whole of what the
   prover of [FILEWRITE_CONS] needs to turn consolewrite's returned count
   into this contract's arms: the FD_DEVICE arm relays the callee's return
   value untouched, so [r] IS the receipt's length. *)
Section ConsArmsOfCount.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ}.

  (* the OK arm: consolewrite delivered all [n] *)
  Lemma wcons_ok_of_cnt (γu : uart_names) (tr0 : list (bv 8)) (n : Z) :
    cons_sent_cnt γu tr0 n -∗ wcons_ok γu tr0 n.
  Proof. iIntros "H". iExact "H". Qed.

  (* the SHORT arm: a copy faulted mid-loop and the count already pushed is
     the answer -- [r] both the return value and the receipt's length *)
  Lemma wcons_short_of_cnt (γu : uart_names) (tr0 : list (bv 8))
      (n r : Z) :
    (r < n)%Z ->
    cons_sent_cnt γu tr0 r -∗
    wcons_short γu tr0 n (mword_of_int r : mword 64).
  Proof.
    iIntros (Hlt) "H". iDestruct "H" as (bs) "[%Hlen Hfrom]".
    iExists bs. iSplitR; [by rewrite Hlen|]. iSplitR; [iPureIntro; lia|].
    iExact "Hfrom".
  Qed.

  (* and the disjunction the two of them land in, keyed on which of [r = n]
     or [r < n] the count turned out to be -- the whole device arm's post,
     given [0 <= r <= n] (consolewrite's own range fact) and [0 <= n] (the
     sign guard's fall-through) *)
  Lemma write_cons_arms_of_cnt (γu : uart_names) (tr0 : list (bv 8))
      (n r : Z) :
    (0 <= n)%Z -> (0 <= r <= n)%Z ->
    cons_sent_cnt γu tr0 r -∗
    write_cons_arms γu tr0 n (mword_of_int r : mword 64).
  Proof.
    iIntros (Hn Hr) "H".
    destruct (Z.eq_dec r n) as [-> | Hne].
    - iLeft. iSplitR; [by iPureIntro|]. by iApply wcons_ok_of_cnt.
    - iRight. iLeft. iApply (wcons_short_of_cnt γu tr0 n r with "H"). lia.
  Qed.

End ConsArmsOfCount.

Module Type FILEWRITE_CONS.
  Parameter wp_filewrite_cons :
    forall `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
             !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
      (γf : gname)
      (γs : list gname) (j : nat) (γlp : gname)
      (k : nat) (q : Qp) (st : fdstate)
      (fn : fwrite_names)
      (pidv : mword 32) (U : ustate)
      (m : regfile) (K : nat) (eb : bool) (n : Z) (b : bool)
      (lks : gset string) (rb : bool) (ma : Z)
      (tr0 : list (bv 8)),
      (* the premise list is the body's; see [wp_filewrite_cons_body] *)
      wp_filewrite_cons_body γf γs j γlp k q st fn pidv U m K eb n b lks
        rb ma tr0.
End FILEWRITE_CONS.
