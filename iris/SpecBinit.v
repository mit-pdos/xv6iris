(* SpecBinit.v -- the public interface of binit(), stated independently of its
   proof.  Requires only the definitional layer -- never a whole-function proof
   file -- so every function proof can be checked in parallel.

     void binit(void) {
       struct buf *b;
       initlock(&bcache.lock, "bcache");
       bcache.head.prev = &bcache.head;
       bcache.head.next = &bcache.head;
       for (b = bcache.buf; b < bcache.buf + NBUF; b++) {
         b->next = bcache.head.next;
         b->prev = &bcache.head;
         initsleeplock(&b->lock, "buffer");
         bcache.head.next->prev = b;
         bcache.head.next = b;
       }
     }

   So binit is NOT a thin initlock wrapper (printkinit / trapinit / fileinit
   are): past the spinlock it initializes one sleeplock per buffer AND threads
   the buffers into the circular LRU list through the head sentinel.  Its
   contract is three-part -- the three fields of [bcache.lock], the thirty
   [sl_raw]s of the buffer sleeplocks, and the link fields of the thirty buffers
   plus the head ([blink_raw]) -- and it returns the lock zeroed + named, thirty
   [sl_fresh]es, and the built list [bcache_lru bhead (blist 0 NBUF)].  Sealing
   the sleeplocks into [is_sleeplock]s over whatever each buffer protects is the
   caller's ghost step ([sl_fresh_new]), not binit's; the geometry and the list
   predicate live in BcacheInv.v so bget/brelse can share them. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_var gen_heap invariants.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import RegFile InstrBytes SmodeCore CalleeSaved KernelText KernelDataInv IntrDefs WpNext.
Require Import WpLock SleepLock.
Require Import BcacheInv.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Local Open Scope Z_scope.


(* the two string literals binit passes on -- "bcache" to initlock and "buffer"
   to every initsleeplock.  Both sit in .rodata past etext with no ELF symbol of
   their own, so they are spelled out here; the proof reads their bytes out of
   [kernel_data] with [kernel_data_string]. *)
Definition bcache_name_str : Z := 0x800073b0.
Definition buffer_name_str : Z := 0x800073b8.

Definition wp_binit_sconf_body `{!riscvGS Σ, !sieG Σ, !lockG Σ} `{GEN : GenId} `{CID : CpuId} (m : regfile) (K : nat)
    (vlock : mword 32) (vname vcpu : mword 64) (b : bool) (p : mword 64) :=
  let pcE : mword 64 := mword_of_int KernelSyms.binit in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  let lk : mword 64 := bcache_addr in
  let c_name := lock_name_field lk in
  let c_cpu := add_vec lk (sign_extend' 64 (mword_of_int 16 : mword 12)) in
  (* binit's own frame is 6 slots and its deepest callee (initsleeplock) wants
     6 more below that. *)
  (12 <= K)%nat ->
  sie_cap_gpr m K b p -∗
  kernel_text -∗ kernel_data -∗ pc_is pcE -∗
  lk ↦₄ vlock -∗
  c_name ↦₈ vname -∗
  c_cpu ↦₈ vcpu -∗
  ([∗ list] k ∈ seq 0 NBUF, sl_raw (buf_lock (bnode k))) -∗
  ([∗ list] k ∈ seq 0 NBUF, blink_raw (bnode k)) -∗
  blink_raw bhead -∗
  wp_next b p (fun (CID : CpuId) =>
    ∀ mr,
    sie_cap_gpr mr K b p -∗
    pc_is ret_tgt -∗
    ⌜ callee_saved m mr ⌝ -∗
    lk ↦₄ (mword_of_int 0 : mword 32) -∗
    lock_name lk "bcache"%string -∗
    c_cpu ↦₈ (zero_reg : mword 64) -∗
    ([∗ list] k ∈ seq 0 NBUF, sl_fresh (buf_lock (bnode k)) "buffer"%string) -∗
    bcache_lru bhead (blist 0 NBUF) -∗
    WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type BINIT.
  Parameter wp_binit_sconf :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ} `{GEN : GenId} `{CID : CpuId} (m : regfile) (K : nat)
      (vlock : mword 32) (vname vcpu : mword 64) (b : bool) (p : mword 64),
      wp_binit_sconf_body m K vlock vname vcpu b p.
End BINIT.
