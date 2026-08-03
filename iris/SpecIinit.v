(* SpecIinit.v -- the public interface of iinit(), stated independently of its
   proof.  Requires only the definitional layer -- never a whole-function proof
   file -- so every function proof can be checked in parallel.

     void iinit(void) {
       initlock(&itable.lock, "itable");
       for (int i = 0; i < NINODE; i++)
         initsleeplock(&itable.inode[i].lock, "inode");
     }

   So iinit is NOT a thin initlock wrapper (printkinit / trapinit / fileinit
   are -- see SpecInitlockWrapper.v): past the spinlock it walks the whole
   inode table initializing one sleeplock per entry.  Its contract is
   correspondingly two-part -- the three fields of [itable.lock], handed in raw
   and returned zeroed + named, and the fifty [sl_raw]s of the inode
   sleeplocks, returned as fifty [sl_fresh]es.  Sealing those into
   [is_sleeplock]s over whatever each inode protects is the caller's ghost step
   ([sl_fresh_new]), not iinit's. *)
From Stdlib Require Import Eqdep_dec ZArith Lia List.
From stdpp Require Import gmap list list_monad bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import excl.
From iris.base_logic.lib Require Import ghost_var gen_heap invariants.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import RegFile InstrBytes SmodeCore CalleeSaved KernelText KernelDataInv IntrDefs WpNext.
Require Import WpLock SleepLock.
Require Import ArrCursor.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Local Open Scope Z_scope.

Notation II := KernelSyms.iinit.

(* ------------------------------------------------------------------ *)
(*  itable geometry (file.h / fs.h, corroborated by the disassembly)    *)
(* ------------------------------------------------------------------ *)

(* struct itable { struct spinlock lock; struct inode inode[NINODE]; }, so the
   lock is the FIRST member and &itable.lock = &itable. *)
Definition itable_addr : mword 64 := mword_of_int KernelSyms.itable.

Definition NINODE : nat := 50%nat.

(* sizeof(struct inode) = 136 (the loop's [addi s1,s1,136]); the array starts
   at itable+24, just past the 24-byte spinlock, and the sleeplock sits at
   offset 16 in struct inode (past dev/inum/ref plus padding).  So the
   sleeplock of inode [i] is at itable+40+136*i -- the cursor the loop walks
   from [inode_lock 0] up to the end pointer [inode_lock NINODE]. *)
Definition inode_stride : Z := 136.
Definition inode_lock_base : Z := KernelSyms.itable + 40.
Definition inode_lock (i : nat) : mword 64 := acur inode_lock_base inode_stride i.

(* the side conditions [ArrCursor]'s cursor lemmas take, discharged once. *)
Lemma inode_lock_base_nonneg : 0 <= inode_lock_base.
Proof. unfold inode_lock_base, KernelSyms.itable. lia. Qed.
Lemma inode_stride_pos : 0 < inode_stride.
Proof. unfold inode_stride. lia. Qed.
Lemma inode_lock_end_fits : inode_lock_base + inode_stride * Z.of_nat NINODE < 2 ^ 64.
Proof.
  unfold inode_lock_base, inode_stride, NINODE, KernelSyms.itable.
  assert (H : (2 ^ 64 = 18446744073709551616)%Z) by (vm_compute; reflexivity).
  rewrite H. lia.
Qed.

(* the two string literals iinit passes on -- "itable" to initlock and "inode"
   to every initsleeplock.  Both sit in .rodata past etext with no ELF symbol
   of their own, so they are spelled out here; the proof reads their bytes out
   of [kernel_data] with [kernel_data_string]. *)
Definition itable_name_str : Z := 0x80007420.
Definition inode_name_str : Z := 0x80007428.

(* ------------------------------------------------------------------ *)

Definition wp_iinit_sconf_body `{!riscvGS Σ, !sieG Σ, !lockG Σ} `{GEN : GenId} `{CID : CpuId}
    (Φ : mval -> iProp Σ) (m : regfile) (K : nat)
    (vlock : mword 32) (vname vcpu : mword 64) (b : bool) (p : mword 64) :=
  let pcE : mword 64 := mword_of_int KernelSyms.iinit in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  let lk : mword 64 := itable_addr in
  let c_name := lock_name_field lk in
  let c_cpu := add_vec lk (sign_extend' 64 (mword_of_int 16 : mword 12)) in
  (* iinit's own frame is 6 slots and its deepest callee (initsleeplock) wants
     6 more below that. *)
  (12 <= K)%nat ->
  sie_cap_gpr m K b p -∗
  kernel_text -∗ kernel_data -∗ pc_is pcE -∗
  lk ↦₄ vlock -∗
  c_name ↦₈ vname -∗
  c_cpu ↦₈ vcpu -∗
  ([∗ list] i ∈ seq 0 NINODE, sl_raw (inode_lock i)) -∗
  wp_next b p (fun (CID : CpuId) =>
    ∀ mr,
    sie_cap_gpr mr K b p -∗
    pc_is ret_tgt -∗
    ⌜ callee_saved m mr ⌝ -∗
    lk ↦₄ (mword_of_int 0 : mword 32) -∗
    lock_name lk "itable"%string -∗
    c_cpu ↦₈ (zero_reg : mword 64) -∗
    ([∗ list] i ∈ seq 0 NINODE, sl_fresh (inode_lock i) "inode"%string) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}) -∗
  WP (Loop : expr riscv_lang) {{ Φ }}.

Module Type IINIT.
  Parameter wp_iinit_sconf :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ} `{GEN : GenId} `{CID : CpuId}
      (Φ : mval -> iProp Σ) (m : regfile) (K : nat)
      (vlock : mword 32) (vname vcpu : mword 64) (b : bool) (p : mword 64),
      wp_iinit_sconf_body Φ m K vlock vname vcpu b p.
End IINIT.
