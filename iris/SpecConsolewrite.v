(* SpecConsolewrite.v -- the public interface of consolewrite, stated
   independently of its proof.  Requires only the definitional layer -- never
   a whole-function proof file -- so every function proof can be checked in
   parallel.

     int consolewrite(int user_src, uint64 src, int n) {
       char buf[32];                      // a bounce buffer IN THE FRAME
       int i = 0;
       while (i < n) {
         int nn = sizeof(buf);
         if (nn > n - i) nn = n - i;
         if (either_copyin(buf, user_src, src + i, nn) == -1) break;
         uartwrite(buf, nn);
         i += nn;
       }
       return i;
     }

   @ KernelSyms.consolewrite = 0x800000d6, 71 instructions / 162 bytes; a
   128-byte frame whose LOWEST 32 bytes are [buf] and whose top twelve slots
   hold ra/s0/s1 (saved unconditionally) and s2..s10 (SHRINK-WRAPPED onto the
   [n > 0] path).

   THE ALTITUDE IS THE UART'S, NOT THE CONSOLE'S.  consolewrite never touches
   [cons] -- no lock, no ring buffer, no index -- so [ConsoleInv.is_conslock]
   is NOT a premise here; that is consoleread's and consoleintr's credential.
   What this function needs is exactly what its two callees need:

   * [UartTxInv.is_txlock γl γu] and [WpUart.dev_inv γu γv], uartwrite's whole
     credential (SpecUartwrite.v).  Both are persistent, so the loop carries
     them for free;
   * [proc_priv_core] and [kalloc_env], either_copyin's user arm (it reaches
     copyin, hence walkaddr and vmfault, hence kalloc), with the descriptor
     coming back EXTENDED ([uptd_ext]) -- writei's user arm does the same;
   * the running-thread bundle ([procs_inv]) and the hart-generic parking
     premise [eb = true] at [noff = 0], because uartwrite SLEEPS between
     bytes.  Nothing of this function's own state crosses that park: [buf]
     is in the frame, and the frame is not shared.

   THE BOUNCE BUFFER IS INVISIBLE HERE, and that is the point of it being a
   local: the 32 bytes are carved out of the four lowest slots of the frame
   this contract already charges for ([consolewrite_stack]), written by
   either_copyin and read by uartwrite, and no caller can name them.

   ---- WHAT IT PROMISES ABOUT THE OUTPUT -------------------------------

   The RETURN VALUE RANGE, [0 <= r <= n], and nothing else.  Not [-1]: this
   function has no failing exit -- a copy that faults BREAKS, and the count
   already pushed is what it answers -- so the [-1] the assumed contract used
   to admit was slack, and it is gone.  ([Z.max 0 n] rather than [n] so the
   statement is true at a non-positive request too, where the loop never runs
   and the answer is 0; [PipeInvDefs.pipe_rw_ret] takes the same care, and
   [SpecFilewrite]'s [filewrite_ret] is where the two meet.)

   WHAT IT DOES NOT PROMISE IS WHICH BYTES REACHED THE WIRE, and this is a
   deliberate loss.  uartwrite's own contract does say
   ([UartTxInv.uart_sent_sub γu bs] -- every byte of its buffer was accepted
   by the UART, in order, possibly interleaved), but the bytes consolewrite
   hands it came out of USER memory through copyin, about which the kernel
   may assume nothing: [SpecEitherCopyin.either_copyin_post]'s user arm gives
   back the destination at an EXISTENTIAL content ([∃ dst_new]), because a
   copyin that faults part-way has still written a prefix.  So the strongest
   sound claim would be "for each chunk there EXISTS a byte string, unrelated
   to anything the caller can name, that the UART accepted" -- a statement
   with no consumer.  A trace claim about a console write becomes worth
   stating only once the user page's contents are nameable at this altitude,
   which is a property of copyin's spec and not of this function. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExtras.
Require Import InstrBytes.
Require Import RegFile.
Require Import SmodeCore.
Require Import CalleeSaved KernelText.
Require Import IntrDefs.
Require Import WpNext.
Require Import WpLock.
Require Import ProcGeom CpuOwn.
Require Import KallocInv.
Require Import UserPtTree.
Require Import KvmSpec.
Require Import ProcPtOwn.
Require Import FdSlots ProcInv.
Require Import FileInvDefs.
Require Import DiskPtsto WpUart.
Require Import UartTxInv.
Require Import PanicStub.
Require Import SchedCtx.
Require Export SwtchCtx.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Import Defs.
Local Open Scope Z_scope.

(* consolewrite's own frame is SIXTEEN slots ([c.addi16sp sp,sp,-128]: three
   saved registers, nine more shrink-wrapped, and the 32-byte [buf] in the
   four lowest), and its deepest callee is either_copyin at 56 -- uartwrite
   wants only 30.

   16 + 56, WITH NO DISCOUNT FOR THE TRAP RESERVE.  piperead pays 62 for a
   52-slot copyout because its copy happens under the pipe lock, where
   interrupts are off and [IntrDefs.trap_res true] is spendable stack; this
   function holds NO lock, so both of its calls are made with interrupts on
   and the reserve is not available to them.  Raising [SpecFilewrite]'s
   [filewrite_stack] from [12 + K_writei] to [12 + 72] is the whole cost of
   that, and it stops there: nothing above sys_write reads the constant. *)
Definition consolewrite_stack : nat := 72%nat.

Definition wp_consolewrite_sconf_body
    `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !irefslotG Σ, !fileG Σ, !kallocG Σ}
    `{!uartGhostG Σ, !diskGhostG Σ}
    `{GEN : GenId} `{CID : CpuId}
    (γa : gname) (γf : gname)
    (γs : list gname) (j : nat) (γlp : gname)
    (γu : uart_names) (γv : disk_names) (γl : gname)
    (m : regfile) (av : nat) (eb : bool)
    (pid : mword 32) (V : pprivate) (n : Z) (b : bool) (lks : gset string) :=
  let pcE : mword 64 := mword_of_int KernelSyms.consolewrite in
  let pj := proc_addr j in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  (* the process running here is proc j (sleep's linkage, inside uartwrite) *)
  (j < NPROC)%nat ->
  γs !! j = Some γlp ->
  length γs = NPROC ->
  (* a0 = 1: the source is a USER address.  filewrite's dispatch passes the
     literal 1 (the [c.li a0,1] at +0x7c), and this contract is only stated
     for that case -- the kernel-source arm has no caller. *)
  m !!! Regidx (mword_of_int 10 : mword 5) = (mword_of_int 1 : mword 64) ->
  (* a2 is the int argument [n] *)
  m !!! Regidx (mword_of_int 12 : mword 5) = (mword_of_int n : mword 64) ->
  (- 2 ^ 31 <= n < 2 ^ 31)%Z ->
  (consolewrite_stack <= av)%nat ->
  (* PARKING PREMISE (hart-generic scheduler protocol).  See SpecSched.v. *)
  eb = true ->
  (* the order premise, at the LOWEST rank this cone touches; every
     higher one follows by [locks_below_mono]. *)
  locks_below lks "proc" ->
  sie_cap_gpr m av b pj -∗
  (* noff = 0: the sleep inside uartwrite demands that tx_lock -- taken and
     released inside uartwrite's own loop -- be the only lock held. *)
  cpu_own 0%nat eb pj b lks -∗
  kernel_text -∗ pc_is pcE -∗
  proc_priv_core pj pid V -∗
  kalloc_env γa None -∗
  (* uartwrite's whole credential: the device fabric and the transmit lock
     (UartTxInv.v).  Both persistent. *)
  dev_inv γu γv -∗
  is_txlock γl γu -∗
  procs_inv γs -∗
  panic_wp_any -∗
  (* THE CROSSING IS [true], NOT [b] -- consolewrite reaches a park, so the
     porting guide's rule applies: a parking function's [wp_next] index is
     [true] unconditionally.  With [eb = true] above and [cpu_own_eb_agree]
     at level 0 the two spellings coincide at every constructible instance. *)
  wp_next true pj (fun (CID : CpuId) =>
  ∀ (mf : regfile) (r : Z) (P' : uptd),
      ⌜callee_saved m mf⌝ -∗
      ⌜uptd_ext (pv_upt V) P'⌝ -∗
      (* the whole of what a device write promises: it delivered somewhere
         between nothing and all of it. *)
      ⌜(0 <= r <= Z.max 0 n)%Z⌝ -∗
      ⌜mf !!! Regidx (mword_of_int 10 : mword 5) = (mword_of_int r : mword 64)⌝ -∗
      sie_cap_gpr mf av b pj -∗
      cpu_own 0%nat eb pj b lks -∗
      pc_is ret_tgt -∗
      proc_priv_core pj pid (upd_upt V P') -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type CONSOLEWRITE.
  Parameter wp_consolewrite_sconf :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !irefslotG Σ, !fileG Σ, !kallocG Σ}
      `{!uartGhostG Σ, !diskGhostG Σ}
      `{GEN : GenId} `{CID : CpuId}
      (γa : gname) (γf : gname) (γs : list gname) (j : nat) (γlp : gname)
      (γu : uart_names) (γv : disk_names) (γl : gname)
      (m : regfile) (av : nat) (eb : bool)
      (pid : mword 32) (V : pprivate) (n : Z) (b : bool) (lks : gset string),
      wp_consolewrite_sconf_body γa γf γs j γlp γu γv γl m av eb pid V n b lks.
End CONSOLEWRITE.
