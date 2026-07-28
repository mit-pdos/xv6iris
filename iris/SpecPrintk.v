(* SpecPrintk.v -- the public interface of Printk, stated independently of its
   proof.  Requires only the definitional layer -- never a whole-function proof
   file -- so every function proof can be checked in parallel.

     int printk(char *fmt, ...);

   THE POST.  printk promises that SOME byte list [bs] was appended to the
   UART's accepted trace, and returns 0.  It does NOT say which bytes: nothing
   in the kernel reads back what was printed, and a byte-accurate post would
   have to carry a decimal/hex rendering of every vararg up through the format
   recursion -- for no consumer.  The exclusive-transmitter token comes back
   standing for [l ++ bs] so the caller can print again, and the persistent
   [uart_sent] receipt records that those bytes provably reached the FIFO.

   THE PRECONDITION is where the content is, and it has exactly three parts
   beyond the usual capability/config boilerplate.

   1. THE FORMAT STRING is a real C string: [fmt ↦ₛ{dqf} f] with [nonul f].  It
      is handed back untouched -- printk only reads it.

   2. THE VARARGS.  A variadic call has no types at the call site, so the caller
      DESCRIBES its arguments: [descs] says, for each vararg in order, whether it
      is an integer-ish value ([PkANum] -- %d/%u/%x/%p/%c and the long forms), a
      null [char *] ([PkANull], which printk prints as "(null)"), or a [char *]
      to a string it owns ([PkAStr dq s]).  The description must MATCH the
      format string --

          pk_kinds f = map pk_desc_kind descs

      -- which is the honest statement of C's unchecked contract: a "%s" whose
      argument is not a string is undefined behaviour, and here it is simply
      unprovable.  The [PkAStr] resources are handed back with the same
      fractions.

      The varargs themselves are not extra parameters: the ABI puts them in
      a1..a7, so vararg [j] IS [m0 !!! a(j+1)] ([pk_vararg]).

   3. AT MOST SEVEN VARARGS.  printk spills a1..a7 into its own frame and walks
      [ap] up through them; an eighth [va_arg] would read the CALLER's frame,
      which printk does not own.  So [length descs <= 7] is a genuine caller
      obligation -- and one every call site in xv6 meets with room to spare.

   Like the rest of the printk cone this is the PANIC path ([panicking <> 0],
   [panicked = 0]): printk then takes NO pr.lock (it skips both the acquire and
   the release), and uartputc_sync does no push_off/pop_off -- which is why no
   lock resource and no [intr_count] appear here.  It is the path panic() runs
   on. *)
From Stdlib Require Import ZArith Bool Lia List String Ascii.
From stdpp Require Import gmap list bitvector.definitions.
From iris.algebra Require Import dfrac.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_var gen_heap invariants.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import InstrBytes.
Require Import KernelText KernelDataInv.
Require Import RegFile.
Require Import SmodeCore.
Require Import CalleeSaved.
Require Import DiskPtsto WpUart.
Require Import IntrDefs.
Require Import PrintkFmt.
From Kernel Require KernelSyms.

Notation PK := KernelSyms.printk.

(* ---------------------------------------------------------------------- *)
(* The caller's description of one vararg (see (2) above).                 *)
(* ---------------------------------------------------------------------- *)
Inductive pk_arg_desc :=
  | PkANum                                (* an integer/char/pointer value *)
  | PkANull                               (* a null char* -- printed "(null)" *)
  | PkAStr (dq : dfrac) (s : string).     (* a char* to [s], owned at [dq] *)

Definition pk_desc_kind (d : pk_arg_desc) : pk_kind :=
  match d with
  | PkANum => PkNum
  | PkANull => PkStr
  | PkAStr _ _ => PkStr
  end.

Definition pk_desc_res `{!riscvGS Σ} `{CID : CpuId} (v : mword 64) (d : pk_arg_desc) : iProp Σ :=
  match d with
  | PkANum => True
  | PkANull => ⌜v = zero_reg⌝
  | PkAStr dq s => ⌜nonul s = true⌝ ∗ v ↦ₛ{dq} s
  end.

(* Vararg [j] is the entry value of a(j+1) = x(11+j): the ABI passes the first
   seven in registers, and printk's prologue spills them into its own frame. *)
Definition pk_vararg (m : regfile) (j : nat) : mword 64 :=
  m !!! Regidx (mword_of_int (11 + Z.of_nat j) : mword 5).

Definition wp_printk_sconf_body `{!riscvGS Σ, !sieG Σ} `{!uartGhostG Σ, !diskGhostG Σ} `{CID : CpuId}
    (γ : gname) (γd : uart_names) (γv : disk_names) (Φ : mval -> iProp Σ) (m0 : regfile) (K : nat)
    (l : list (bv 8)) (pv pkv : mword 32) (dqm dqm2 dqf : dfrac)
    (f : string) (descs : list pk_arg_desc) :=
  let ra_idx : mword 5 := mword_of_int 1 in
  let a0_idx : mword 5 := mword_of_int 10 in
  let pcE := mword_of_int KernelSyms.printk in
  let ra0 := m0 !!! Regidx ra_idx in
  let ret_tgt := ret_pc ra0 in
  let fmt := m0 !!! Regidx a0_idx in
  (* printk's own 24-slot frame, over printint's 14 *)
  (38 <= K)%nat ->
  nonul f = true ->
  pk_kinds f = map pk_desc_kind descs ->
  (length descs <= 7)%nat ->
  eq_vec (sign_extend' 64 pv) zero_reg = false ->
  neq_vec (sign_extend' 64 pkv) zero_reg = false ->
  sie_cap_gpr γ m0 K -∗
  kernel_text -∗ kernel_data -∗ pc_is pcE -∗
  fmt ↦ₛ{ dqf } f -∗
  ([∗ list] j ↦ d ∈ descs, pk_desc_res (pk_vararg m0 j) d) -∗
  (mword_of_int KernelSyms.panicking : mword 64) ↦₄{ dqm } pv -∗
  (mword_of_int KernelSyms.panicked : mword 64) ↦₄{ dqm2 } pkv -∗
  dev_inv γd γv -∗ uart_tx_own γd l -∗ uart_dlab_off γd -∗
  ( ∀ mf bs,
    sie_cap_gpr γ mf K -∗
    pc_is ret_tgt -∗
    ⌜ callee_saved m0 mf /\ mf !!! Regidx ra_idx = ra0
      /\ mf !!! Regidx a0_idx = zero_reg ⌝ -∗
    fmt ↦ₛ{ dqf } f -∗
    ([∗ list] j ↦ d ∈ descs, pk_desc_res (pk_vararg m0 j) d) -∗
    (mword_of_int KernelSyms.panicking : mword 64) ↦₄{ dqm } pv -∗
    (mword_of_int KernelSyms.panicked : mword 64) ↦₄{ dqm2 } pkv -∗
    uart_tx_own γd (l ++ bs) -∗ uart_sent γd (l ++ bs) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}) -∗
  WP (Loop : expr riscv_lang) {{ Φ }}.

Module Type PRINTK.
  Parameter wp_printk_sconf :
    forall `{!riscvGS Σ, !sieG Σ} `{!uartGhostG Σ, !diskGhostG Σ} `{CID : CpuId}
      (γ : gname) (γd : uart_names) (γv : disk_names) (Φ : mval -> iProp Σ) (m0 : regfile) (K : nat)
      (l : list (bv 8)) (pv pkv : mword 32) {dqm dqm2 dqf : dfrac}
      (f : string) (descs : list pk_arg_desc),
      wp_printk_sconf_body γ γd γv Φ m0 K l pv pkv dqm dqm2 dqf f descs.
End PRINTK.
