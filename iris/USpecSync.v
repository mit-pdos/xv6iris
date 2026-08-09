(* USpecSync.v -- the VERIFIED-EXECUTION contracts of the `sync` user
   program's four functions (claude-notes/projects/user-verified.md):

     start @0x12   the ELF entry: prologue, call main, call exit -- DIVERGES
     main  @0x0    call sync(), li a0,0, call exit -- DIVERGES
     sync  @0x368  the syscall stub: li a7,22; ecall; ret -- RETURNS
     exit  @0x2c8  the syscall stub: li a7,2; ecall -- DIVERGES

   Only what is SPECIFIC to the sync program lives here: its entry
   addresses, its image, its call structure and stack budget.  The generic
   vocabulary is elsewhere -- the trap capability and threading bundle in
   UmodeCap.v, the ABI registers / image inclusion / stack-frame window in
   UmodeAbi.v, and the syscall semantics in UmodeSyscall.v (a syscall's
   meaning belongs to the KERNEL: this program's protocol is just the xv6
   table, [xv6_sys_protocol]).

   All contracts thread [uv_cap_gpr]; every continuation re-binds the hart
   ([∀ CID]): the process may be preempted at ANY verified instruction and
   resumed on a different hart, so nothing after a step may assume the
   entry hart.  Diverging functions have NO continuation (scheduler-style):
   everything after their last `ecall` is absorbed by the syscall service's
   exit arm. *)
From Stdlib Require Import ZArith Bool Lia.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import invariants.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import InstrBytes RegFile.
Require Import UserPtTree UserExec.
Require Import UmodeCap UmodeAbi UmodeSyscall UCodeSync.
Require User.SyncSyms User.SyncInstrs.
Local Open Scope Z_scope.
Import Defs.

Section USpecSync.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.
  Context (C : ucfg) (pt : uptd).

  (* the sync program's protocol IS the kernel's table -- nothing
     program-specific to say *)
  Local Notation Ψxv6 := (xv6_sys_protocol C pt).
  Local Notation UVG m M := (uv_cap_gpr C pt Ψxv6 M m).

  (* ------------------------------------------------------------------- *)
  (* §1 The syscall stubs.                                                 *)
  (* ------------------------------------------------------------------- *)

  (* sync @0x368: li a7,22; ecall; ret.  RETURNS to [m !!! ra] with
     a7 = 22, a0 = the (arbitrary) syscall return value, everything else
     -- registers, image, pc discipline -- intact, on an arbitrary hart. *)
  Definition wp_sync_stub_body (M : gmap Z (bv 8)) (m : regfile) :=
    forall (Hlay : sync_layout pt)
      (Htext : uimg_sub SyncInstrs.sync_bytes M)
      (Hret2 : is_aligned_vaddr (Virtaddr (m !!! Regidx ra_idx)) 2 = true),
    UVG m M -∗
    pc_is (mword_of_int SyncSyms.sync) -∗
    (∀ CID : CpuId, ∀ ret : mword 64,
       UVG (<[Regidx a0_idx := ret]>
              (<[Regidx a7_idx := (mword_of_int 22 : mword 64)]> m)) M -∗
       pc_is (m !!! Regidx ra_idx) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).

  (* exit @0x2c8: li a7,2; ecall.  DIVERGES (the trailing ret is dead). *)
  Definition wp_exit_stub_body (M : gmap Z (bv 8)) (m : regfile) :=
    forall (Hlay : sync_layout pt)
      (Htext : uimg_sub SyncInstrs.sync_bytes M),
    UVG m M -∗
    pc_is (mword_of_int SyncSyms.exit) -∗
    WP (Loop : expr riscv_lang).

  (* ------------------------------------------------------------------- *)
  (* §2 main and start.  Both DIVERGE (their final call is exit, and       *)
  (* exit's ecall never comes back), so neither has a continuation and     *)
  (* neither says anything about ra.  Each needs its own 16-byte frame     *)
  (* below its entry sp; start additionally needs main's frame below that. *)
  (* ------------------------------------------------------------------- *)

  (* main @0x0: prologue (16-byte frame), jal sync, li a0,0, jal exit. *)
  Definition wp_sync_main_body (M : gmap Z (bv 8)) (m : regfile)
      (sp0 : mword 64) :=
    forall (Hlay : sync_layout pt)
      (Htext : uimg_sub SyncInstrs.sync_bytes M)
      (Hsp : m !!! Regidx sp_idx = sp0)
      (Hfr : uv_frame16 pt M sp0),
    UVG m M -∗
    pc_is (mword_of_int SyncSyms.main) -∗
    WP (Loop : expr riscv_lang).

  (* start @0x12 -- the ELF entry [exec()] jumps to: prologue, jal main,
     jal exit.  The top-level verified-execution statement for the whole
     sync process: from the loaded image and the entry registers, the
     machine runs safely forever under the kernel's trap services. *)
  Definition wp_sync_start_body (M : gmap Z (bv 8)) (m : regfile)
      (sp0 : mword 64) :=
    forall (Hlay : sync_layout pt)
      (Htext : uimg_sub SyncInstrs.sync_bytes M)
      (Hsp : m !!! Regidx sp_idx = sp0)
      (Hfr : uv_frame16 pt M sp0)                          (* start's frame *)
      (Hfr' : uv_frame16 pt M (add_vec_int sp0 (-16))),    (* main's frame *)
    UVG m M -∗
    pc_is (mword_of_int SyncSyms.start) -∗
    WP (Loop : expr riscv_lang).

End USpecSync.
