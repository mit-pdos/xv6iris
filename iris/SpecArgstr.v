(* SpecArgstr.v -- the public interface of argstr(), stated independently of
   its proof.

     int argstr(int n, char *buf, int max) {
       uint64 addr;
       argaddr(n, &addr);
       return fetchstr(addr, buf, max);
     }

   @ KernelSyms.argstr = 0x8000283c, twenty instructions / 40 bytes.

   ARGADDR IS INLINED, and that is the only surprise in the machine code:
   there is no [uint64 addr] on the stack and no call to argaddr, only a
   [jal argraw] whose [a0] is handed straight to fetchstr.  So this contract
   is stated over argraw's resources, not argaddr's, and the local [addr]
   never appears -- there is no out-parameter cell to own.

   THE ALTITUDE IS argfd's, and for the same reason: argstr is a syscall
   helper whose caller holds [proc_priv], and both of its callees want a
   PIECE of that block -- argraw the trapframe page (split out with
   [ProcInv.proc_priv_tf]), fetchstr the page table (split out inside
   fetchstr's own proof with [proc_priv_copy]).  Taking [proc_priv] whole and
   splitting inside is what keeps the two splits from meeting in a caller.

   WHAT THE CALLER MUST SAY, and what it gets:

   - the argument index [i] is in range ([i < NARG]) and word
     [tf_arg_idx i] of this process's trapframe holds [v] -- argraw's
     premises, spelled through [pv_tf V] so [proc_priv] supplies them;
   - [buf] names [max] owned bytes.  The contract says nothing about [v]
     afterwards: fetchstr does no range test on it (SpecFetchstr.v), so the
     user-supplied address is either mapped or it is not, and either way the
     answer is [fetchstr_ret];
   - [max < 2^31], inherited from strlen's [int] return through fetchstr.

   The postcondition is fetchstr's verbatim -- [FS.fetchstr_ret max new r]:
   either the buffer holds a NUL-terminated string of length [k < max] and
   [r = k], or [r = -1].  [proc_priv] comes back untouched, because nothing
   in the cone faults a page in. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre lifting.
From iris.base_logic.lib Require Import gen_heap invariants ghost_var.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import RiscvModelBytes RiscvPtsto RiscvLang RiscvExtras.
Require Import InstrBytes KernelText KernelDataInv.
Require Import RegFile.
Require Import SmodeCore.
Require Import CalleeSaved.
Require Import IntrDefs.
Require Import WpNext.
Require Import WpLock.
Require Import ProcGeom CpuOwn.
Require Import FdSlots FileInv ProcInv.
Require Import SpecFetchstr.
From Kernel Require KernelSyms.
Import Defs.
Local Open Scope Z_scope.


(* 4 slots for argstr's own frame; fetchstr's 26 dominates argraw's 14. *)
Definition argstr_stack : nat := 30%nat.

Definition wp_argstr_sconf_body `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ} `{GEN : GenId} `{CID : CpuId}
    (γf : gname)
    (m : regfile) (av : nat) (n : nat) (eb : bool) (p : mword 64) (C : iProp Σ)
    (i : nat) (v : mword 64)
    (pid : mword 32) (V : pprivate) (maxn : nat) (buf_olds : nat -> bv 8) (b : bool) :=
  let pcE : mword 64 := mword_of_int KernelSyms.argstr in
  let buf := m !!! Regidx (mword_of_int 11 : mword 5) in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  (* the syscall argument index, in range: argraw's panic arm *)
  (i < NARG)%nat ->
  m !!! Regidx (mword_of_int 10 : mword 5) = mword_of_int (Z.of_nat i) ->
  pv_tf V !! tf_arg_idx i = Some v ->
  (Z.of_nat n + 1 < 2 ^ 31)%Z ->
  (argstr_stack <= av)%nat ->
  m !!! Regidx (mword_of_int 12 : mword 5) = (mword_of_int (Z.of_nat maxn) : mword 64) ->
  (Z.of_nat maxn < 2 ^ 31)%Z ->
  sie_cap_gpr m av b p -∗
  cpu_own n eb p C b -∗
  kernel_text -∗ kernel_data -∗ pc_is pcE -∗
  proc_priv γf p pid V -∗
  ([∗ list] j ∈ seq 0 maxn, (pa_add buf j) ↦ₘ buf_olds j) -∗
  wp_next b p (fun (CID : CpuId) =>
    ∀ (mf : regfile) (buf_new : nat -> bv 8),
      ⌜callee_saved m mf⌝ -∗
      sie_cap_gpr mf av b p -∗
      cpu_own n eb p C b -∗
      pc_is ret_tgt -∗
      proc_priv γf p pid V -∗
      ([∗ list] j ∈ seq 0 maxn, (pa_add buf j) ↦ₘ buf_new j) -∗
      ⌜fetchstr_ret maxn buf_new (mf !!! Regidx (mword_of_int 10 : mword 5))⌝ -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type ARGSTR.
  Parameter wp_argstr_sconf :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ} `{GEN : GenId} `{CID : CpuId}
      (γf : gname) (m : regfile) (av : nat) (n : nat) (eb : bool) (p : mword 64) (C : iProp Σ)
      (i : nat) (v : mword 64)
      (pid : mword 32) (V : pprivate) (maxn : nat) (buf_olds : nat -> bv 8) (b : bool),
      wp_argstr_sconf_body γf m av n eb p C i v pid V maxn buf_olds b.
End ARGSTR.
