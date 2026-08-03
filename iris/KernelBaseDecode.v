(* KernelBaseDecode.v -- pure BASE (32-bit) instruction decode facts, keyed by
   the instruction WORD, for words that occur in more than one kernel function.

   The compressed counterpart is KernelRvcDecode.v; the same rule applies here.
   These are address-independent [exec (ext_decode w) s = Some (i, s)] equations
   under a concrete-enough config -- NOT weakest-preconditions -- so a word that
   two functions both contain belongs at this shared altitude rather than in one
   of their WP files (which would force the other to import a whole-function
   proof subtree just to reach a decode).  A word used by exactly one function
   still lives in that function's own Wp<F>Decode.v. *)
From Stdlib Require Import ZArith.
From stdpp Require Import bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvExec RiscvFetchExec.
Require Import WpDecodeBridge.
Local Open Scope Z_scope.
Import Defs.

(* auipc a1,0x6 -- kinit +0x08, printkinit +0x08 *)
Lemma bdec_00006597 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00006597 : mword 32)) s
  = Some (UTYPE (mword_of_int 6 : mword 20, Regidx (mword_of_int 11), AUIPC), s).
Proof. decode_bridge_ms. Qed.

(* auipc a0,0x12 -- kinit +0x10, printkinit +0x10 *)
Lemma bdec_00012517 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00012517 : mword 32)) s
  = Some (UTYPE (mword_of_int 18 : mword 20, Regidx (mword_of_int 10), AUIPC), s).
Proof. decode_bridge_ms. Qed.

(* slliw a0,a0,0xd -- plicinithart +0x1e, plic_claim +0x0c *)
Lemma bdec_00d5151b s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00d5151b : mword 32)) s
  = Some (SHIFTIWOP (mword_of_int 13 : mword 5, Regidx (mword_of_int 10),
                     Regidx (mword_of_int 10), SLLIW), s).
Proof. decode_bridge_ms. Qed.

(* lui a5,0xc201 -- plicinithart +0x22, plic_claim +0x10 *)
Lemma bdec_0c2017b7 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x0c2017b7 : mword 32)) s
  = Some (UTYPE (mword_of_int 0xc201 : mword 20, Regidx (mword_of_int 15), LUI), s).
Proof. decode_bridge_ms. Qed.

(* auipc a0,0x15 -- binit +0x18 (&bcache), sys_uptime +0x0a and +0x20
   (&tickslock, materialized once per acquire/release call) *)
Lemma bdec_00015517 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00015517 : mword 32)) s
  = Some (UTYPE (mword_of_int 0x15 : mword 20, Regidx (mword_of_int 10), AUIPC), s).
Proof. decode_bridge_ms. Qed.

(* 0x0001e517  auipc a0,0x1e -- every function that materializes a pointer
   into the 0x8002xxxx globals: fileinit, iinit, filealloc, filedup. *)
Lemma bdec_0001e517 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x0001e517 : mword 32)) s
  = Some (UTYPE (mword_of_int 30 : mword 20, Regidx (mword_of_int 10), AUIPC), s).
Proof. decode_bridge_ms. Qed.

(* ---- the KSTACK(i) computation's base words, shared by proc_mapstacks
   and procinit (see KstackArith.v for what the sequence computes) ---- *)
Lemma bdec_000a57b7 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
    exec (ext_decode (mword_of_int 0x000a57b7 : mword 32)) s
    = Some (UTYPE (mword_of_int 165 : mword 20, Regidx (mword_of_int 15), LUI), s).
  Proof. decode_bridge_ms. Qed.

Lemma bdec_fa578793 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
    exec (ext_decode (mword_of_int 0xfa578793 : mword 32)) s
    = Some (ITYPE (mword_of_int 4005 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 15), ADDI), s).
  Proof. decode_bridge_ms. Qed.

Lemma bdec_4fa50937 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
    exec (ext_decode (mword_of_int 0x4fa50937 : mword 32)) s
    = Some (UTYPE (mword_of_int 326224 : mword 20, Regidx (mword_of_int 18), LUI), s).
  Proof. decode_bridge_ms. Qed.

Lemma bdec_a4f90913 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
    exec (ext_decode (mword_of_int 0xa4f90913 : mword 32)) s
    = Some (ITYPE (mword_of_int 2639 : mword 12, Regidx (mword_of_int 18), Regidx (mword_of_int 18), ADDI), s).
  Proof. decode_bridge_ms. Qed.

Lemma bdec_040009b7 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
    exec (ext_decode (mword_of_int 0x040009b7 : mword 32)) s
    = Some (UTYPE (mword_of_int 16384 : mword 20, Regidx (mword_of_int 19), LUI), s).
  Proof. decode_bridge_ms. Qed.

Lemma bdec_16848493 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
    exec (ext_decode (mword_of_int 0x16848493 : mword 32)) s
    = Some (ITYPE (mword_of_int 360 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 9), ADDI), s).
  Proof. decode_bridge_ms. Qed.

(* 0x0d078793  addi a5,a5,208 -- the [p->ofile] array offset in [struct proc];
   shared by sys_close and argfd, which index that array the same way. *)
Lemma bdec_0d078793 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x0d078793 : mword 32)) s
  = Some (ITYPE (mword_of_int 208 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 15), ADDI), s).
Proof. decode_bridge_ms. Qed.


(* ---- words the uvmunmap / uvmalloc catalogs shared with the rest of the
   tree ---- *)

(* 0x00006517  auipc a0,0x6 -- acquire, kvmmap, proc_mapstacks, uvmunmap:
   every function that materializes a pointer into the 0x80006xxx globals *)
Lemma bdec_00006517 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00006517 : mword 32)) s
  = Some (UTYPE (mword_of_int 6 : mword 20, Regidx (mword_of_int 10), AUIPC), s).
Proof. decode_bridge_ms. Qed.

(* 0x00c79513  slli a0,a5,0xc -- walkaddr, uvmunmap (PTE2PA's << 12) *)
Lemma bdec_00c79513 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00c79513 : mword 32)) s
  = Some (SHIFTIOP (mword_of_int 12 : mword 6, Regidx (mword_of_int 15),
                    Regidx (mword_of_int 10), SLLI), s).
Proof. decode_bridge_ms. Qed.

(* 0x03459793  slli a5,a1,0x34 -- mappages, uvmunmap: the page-alignment
   test [(va % PGSIZE) != 0], as a shift that keeps only the low 12 bits *)
Lemma bdec_03459793 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x03459793 : mword 32)) s
  = Some (SHIFTIOP (mword_of_int 52 : mword 6, Regidx (mword_of_int 11),
                    Regidx (mword_of_int 15), SLLI), s).
Proof. decode_bridge_ms. Qed.

(* 0xf51ff0ef  jal ra,-0xb0 -- walkaddr, uvmalloc (JAL residue 2096976) *)
Lemma bdec_f51ff0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xf51ff0ef : mword 32)) s
  = Some (JAL (mword_of_int 2096976 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* lui a5,0x10000 -- the UART base; uartinit +0x08, uartputc_sync +0x20/+0x34,
   uartintr +0x0c/+0x20 *)
Lemma bdec_100007b7 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x100007b7 : mword 32)) s
  = Some (UTYPE (mword_of_int 0x10000 : mword 20, Regidx (mword_of_int 15), LUI), s).
Proof. decode_bridge_ms. Qed.

(* andi a5,a5,32 -- the LSR THRE mask; uartputc_sync +0x2a, uartintr +0x28 *)
Lemma bdec_0207f793 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x0207f793 : mword 32)) s
  = Some (ITYPE (mword_of_int 32 : mword 12, Regidx (mword_of_int 15),
                 Regidx (mword_of_int 15), ANDI), s).
Proof. decode_bridge_ms. Qed.

(* auipc a5,0xa -- printk +0x1d2, uartputc_sync +0x0c/+0x16/+0x3c,
   uartwrite +0x2e, uartintr +0x56 *)
Lemma bdec_0000a797 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x0000a797 : mword 32)) s
  = Some (UTYPE (mword_of_int 10 : mword 20, Regidx (mword_of_int 15), AUIPC), s).
Proof. decode_bridge_ms. Qed.

(* lbu a0,0(s2) -- printk, and uartintr's inlined uartgetc (the RHR read) *)
Lemma bdec_00094503 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00094503 : mword 32)) s
  = Some (LOAD (mword_of_int 0 : mword 12, Regidx (mword_of_int 18),
                Regidx (mword_of_int 10), true, 1), s).
Proof. decode_bridge_ms. Qed.

(* ------------------------------------------------------------------ *)
(*  The proc-area / nextpid relocations.  Each of these was proved       *)
(*  privately in three to five decode files before the sweep; per the    *)
(*  dedup discipline in claude-notes/durable-notes.md a word proved in   *)
(*  two or more of them belongs here.                                    *)
(* ------------------------------------------------------------------ *)

(* auipc s1,0x11 -- the proc[] base, in the four functions that walk the
   array with the cursor in s1: procinit, proc_mapstacks, wakeup, allocproc
   (and kalloc, which reaches <kmem> the same way) *)
Lemma bdec_00011497 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00011497 : mword 32)) s
  = Some (UTYPE (mword_of_int 0x11 : mword 20, Regidx (mword_of_int 9), AUIPC), s).
Proof. decode_bridge_ms. Qed.

(* auipc a0,0x11 -- the same relocation into a0: procinit, kalloc, mycpu,
   allocpid *)
Lemma bdec_00011517 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00011517 : mword 32)) s
  = Some (UTYPE (mword_of_int 0x11 : mword 20, Regidx (mword_of_int 10), AUIPC), s).
Proof. decode_bridge_ms. Qed.

(* auipc a4,0x10 -- the cpus[]/pid_lock relocation into a4: sched, scheduler *)
Lemma bdec_00010717 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00010717 : mword 32)) s
  = Some (UTYPE (mword_of_int 0x10 : mword 20, Regidx (mword_of_int 14), AUIPC), s).
Proof. decode_bridge_ms. Qed.

(* auipc s2,0x16 -- &proc[NPROC] (= <tickslock>): wakeup, allocproc *)
Lemma bdec_00016917 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00016917 : mword 32)) s
  = Some (UTYPE (mword_of_int 0x16 : mword 20, Regidx (mword_of_int 18), AUIPC), s).
Proof. decode_bridge_ms. Qed.

(* auipc a5,0x9 -- kvminithart, kvmmake, allocpid *)
Lemma bdec_00009797 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00009797 : mword 32)) s
  = Some (UTYPE (mword_of_int 9 : mword 20, Regidx (mword_of_int 15), AUIPC), s).
Proof. decode_bridge_ms. Qed.

(* addi a0,s1,96 -- &p->context, the argument to swtch (sched) and to
   memset (allocproc) *)
Lemma bdec_06048513 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x06048513 : mword 32)) s
  = Some (ITYPE (mword_of_int 96 : mword 12, Regidx (mword_of_int 9),
                 Regidx (mword_of_int 10), ADDI), s).
Proof. decode_bridge_ms. Qed.

(* ---------------------------------------------------------------------- *)
(*  The frame-relative [int] locals two or more syscalls take the address   *)
(*  of.  Same discipline as the [auipc]s above: [s0] is the frame pointer,  *)
(*  so these displacements recur verbatim across functions with the same    *)
(*  frame layout (argfd, sys_pipe, sys_sbrk).                               *)
(* ---------------------------------------------------------------------- *)

(* addi a1,s0,-40 -- &<local at s0-40>: sys_pipe's fd[0], sys_sbrk's n *)
Lemma bdec_fd840593 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xfd840593 : mword 32)) s
  = Some (ITYPE (mword_of_int 0xfd8 : mword 12, Regidx (mword_of_int 8),
                 Regidx (mword_of_int 11), ADDI), s).
Proof. decode_bridge_ms. Qed.

(* addi a1,s0,-36 -- &<local at s0-36>: argfd's fd, sys_sbrk's t *)
Lemma bdec_fdc40593 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xfdc40593 : mword 32)) s
  = Some (ITYPE (mword_of_int 0xfdc : mword 12, Regidx (mword_of_int 8),
                 Regidx (mword_of_int 11), ADDI), s).
Proof. decode_bridge_ms. Qed.

(* lw a4,-36(s0) -- reloading that local, sign-extended *)
Lemma bdec_fdc42703 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xfdc42703 : mword 32)) s
  = Some (LOAD (mword_of_int 0xfdc : mword 12, Regidx (mword_of_int 8),
                Regidx (mword_of_int 14), false, 4), s).
Proof. decode_bridge_ms. Qed.

(* ---------------------------------------------------------------------- *)
(*  The inlined intr_on/intr_off CSR-immediate words.  These need           *)
(*  [decode_bridge_ms_bv], not [decode_bridge_ms]: the decoder's 5-bit uimm  *)
(*  arrives as a SLICE of the instruction word while the CSR leaves          *)
(*  (WpSconfCsr.v) phrase it as [mword_of_int 2], and only [bv_eq] closes    *)
(*  that pair.  The csr field is [Ox"100"], which is (delta-)equal to the    *)
(*  [csr_sstatus] WpPushOffCsr.v / WpSconfCsr.v are stated with, so those    *)
(*  leaves apply directly.                                                  *)
(* ---------------------------------------------------------------------- *)

(* csrsi sstatus,2 (rd = x0) -- intr_on, inlined in pop_off and scheduler *)
Lemma bdec_10016073 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x10016073 : mword 32)) s
  = Some (CSRImm (Ox"100", mword_of_int 2, Regidx (mword_of_int 0), CSRRS), s).
Proof. decode_bridge_ms_bv. Qed.

(* ---------------------------------------------------------------------- *)
(*  fence rw,rw -- gcc's [__sync_synchronize] / [__atomic_thread_fence      *)
(*  (SEQ_CST)].  Shared by main (+0x1c and +0xa2, the two arms' acquire /   *)
(*  release barriers around the [started] handover), virtio_disk_intr        *)
(*  (+0x2c, +0x3e) and virtio_disk_rw (+0x172, +0x182).  Needs               *)
(*  [decode_bridge_ms_bv]: the pred/succ nibbles arrive as slices of the     *)
(*  instruction word while the fence leaf (WpSconfCtl.v) phrases them as     *)
(*  [mword_of_int 3], and only [bv_eq] closes that pair.                    *)
(* ---------------------------------------------------------------------- *)
Lemma bdec_0330000f s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x0330000f : mword 32) : M instruction) s
  = Some (FENCE (mword_of_int 0 : mword 4, mword_of_int 3 : mword 4, mword_of_int 3 : mword 4,
                 Regidx (mword_of_int 0), Regidx (mword_of_int 0)), s).
Proof. decode_bridge_ms_bv. Qed.

(* ---------------------------------------------------------------------- *)
(*  Words the bio.c sweep collapsed (two to five private copies each).      *)
(*  The [auipc]s are the 0x8001xxxx / 0x8002xxxx global relocations every   *)
(*  function that reaches <bcache>, <disk>, <ftable> or <itable> emits.     *)
(* ---------------------------------------------------------------------- *)

(* auipc s1,0x1e -- the array-cursor relocation: bread (bcache.head.next /
   .prev), iinit, filealloc, virtio_disk_init, virtio_disk_intr.  FIVE. *)
Lemma bdec_0001e497 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x0001e497 : mword 32)) s
  = Some (UTYPE (mword_of_int 30 : mword 20, Regidx (mword_of_int 9), AUIPC), s).
Proof. decode_bridge_ms. Qed.

(* auipc a5,0x1e -- the same relocation into a5: bread, free_desc,
   virtio_disk_rw *)
Lemma bdec_0001e797 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x0001e797 : mword 32)) s
  = Some (UTYPE (mword_of_int 30 : mword 20, Regidx (mword_of_int 15), AUIPC), s).
Proof. decode_bridge_ms. Qed.

(* auipc a4,0x1e -- and into a4: binit, virtio_disk_init, virtio_disk_rw *)
Lemma bdec_0001e717 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x0001e717 : mword 32)) s
  = Some (UTYPE (mword_of_int 30 : mword 20, Regidx (mword_of_int 14), AUIPC), s).
Proof. decode_bridge_ms. Qed.

(* auipc a5,0x1d -- the 0x8001xxxx globals into a5: binit, brelse (the
   bcache.head list pointers) *)
Lemma bdec_0001d797 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x0001d797 : mword 32)) s
  = Some (UTYPE (mword_of_int 29 : mword 20, Regidx (mword_of_int 15), AUIPC), s).
Proof. decode_bridge_ms. Qed.

(* auipc a1,0x5 -- a .rodata string address into a1: binit ("bcache"),
   trapinit ("time") *)
Lemma bdec_00005597 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00005597 : mword 32)) s
  = Some (UTYPE (mword_of_int 5 : mword 20, Regidx (mword_of_int 11), AUIPC), s).
Proof. decode_bridge_ms. Qed.

(* addi a0,s1,16 -- &b->lock, the sleeplock inside [struct buf]: binit's
   initsleeplock call and bread's two acquiresleep calls *)
Lemma bdec_01048513 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x01048513 : mword 32)) s
  = Some (ITYPE (mword_of_int 16 : mword 12, Regidx (mword_of_int 9),
                 Regidx (mword_of_int 10), ADDI), s).
Proof. decode_bridge_ms. Qed.

(* sw zero,0(s1) -- clearing the word at the head of an s1-based struct:
   bread's [b->valid = 0], release's and initsleeplock/releasesleep's
   [lk->locked = 0] *)
Lemma bdec_0004a023 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x0004a023 : mword 32)) s
  = Some (STORE (mword_of_int 0 : mword 12, Regidx (mword_of_int 0),
                 Regidx (mword_of_int 9), 4), s).
Proof. decode_bridge_ms. Qed.

(* jal ra,acquire (JAL residue 2089144) -- from binit +0x20 and bread +0x1a,
   which sit the same distance below <acquire> *)
Lemma bdec_8b8fe0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x8b8fe0ef : mword 32)) s
  = Some (JAL (mword_of_int 2089144 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* ---------------------------------------------------------------- *)
(* Words a second function turned out to need.                      *)
(* ---------------------------------------------------------------- *)

Lemma bdec_00003597 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00003597 : mword 32)) s
  = Some (UTYPE (mword_of_int 3 : mword 20, Regidx (mword_of_int 11), AUIPC), s).
Proof. decode_bridge_ms. Qed.

Lemma bdec_00011717 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00011717 : mword 32)) s
  = Some (UTYPE (mword_of_int 0x11 : mword 20, Regidx (mword_of_int 14), AUIPC), s).
Proof. decode_bridge_ms. Qed.

Lemma bdec_00016517 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00016517 : mword 32)) s
  = Some (UTYPE (mword_of_int 22 : mword 20, Regidx (mword_of_int 10), AUIPC), s).
Proof. decode_bridge_ms. Qed.

Lemma bdec_0004b023 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x0004b023 : mword 32)) s
  = Some (STORE (mword_of_int 0 : mword 12, Regidx (mword_of_int 0), Regidx (mword_of_int 9), 8), s).
Proof. decode_bridge_ms. Qed.

Lemma bdec_0004c503 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x0004c503 : mword 32)) s
  = Some (LOAD (mword_of_int 0 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 10), true, 1), s).
Proof. decode_bridge_ms. Qed.

Lemma bdec_00053023 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00053023 : mword 32)) s
  = Some (STORE (mword_of_int 0 : mword 12, Regidx (mword_of_int 0), Regidx (mword_of_int 10), 8), s).
Proof. decode_bridge_ms. Qed.

Lemma bdec_00071723 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00071723 : mword 32)) s
  = Some (STORE (mword_of_int 14 : mword 12, Regidx (mword_of_int 0), Regidx (mword_of_int 14), 2), s).
Proof. decode_bridge_ms. Qed.

Lemma bdec_0009061b s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x0009061b : mword 32)) s
  = Some (ADDIW (mword_of_int 0 : mword 12, Regidx (mword_of_int 18), Regidx (mword_of_int 12)), s).
Proof. decode_bridge_ms. Qed.

Lemma bdec_0017e793 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x0017e793 : mword 32)) s
  = Some (ITYPE (mword_of_int 1 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 15), ORI), s).
Proof. decode_bridge_ms. Qed.

Lemma bdec_0017f713 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x0017f713 : mword 32)) s
  = Some (ITYPE (mword_of_int 1 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 14), ANDI), s).
Proof. decode_bridge_ms. Qed.

Lemma bdec_00451693 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00451693 : mword 32)) s
  = Some (SHIFTIOP (mword_of_int 4 : mword 6, Regidx (mword_of_int 10), Regidx (mword_of_int 13), SLLI), s).
Proof. decode_bridge_ms. Qed.

Lemma bdec_00e78c23 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00e78c23 : mword 32)) s
  = Some (STORE (mword_of_int 24 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 15), 1), s).
Proof. decode_bridge_ms. Qed.

Lemma bdec_00f60733 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00f60733 : mword 32)) s
  = Some (RTYPE (Regidx (mword_of_int 15), Regidx (mword_of_int 12), Regidx (mword_of_int 14), ADD), s).
Proof. decode_bridge_ms. Qed.

Lemma bdec_0187c783 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x0187c783 : mword 32)) s
  = Some (LOAD (mword_of_int 24 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 15), true, 1), s).
Proof. decode_bridge_ms. Qed.

Lemma bdec_02070713 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x02070713 : mword 32)) s
  = Some (ITYPE (mword_of_int 32 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 14), ADDI), s).
Proof. decode_bridge_ms. Qed.

Lemma bdec_040005b7 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x040005b7 : mword 32)) s
  = Some (UTYPE (mword_of_int 16384 : mword 20, Regidx (mword_of_int 11), LUI), s).
Proof. decode_bridge_ms. Qed.

Lemma bdec_08e7a023 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x08e7a023 : mword 32)) s
  = Some (STORE (mword_of_int 128 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 15), 4), s).
Proof. decode_bridge_ms. Qed.

Lemma bdec_10000637 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x10000637 : mword 32)) s
  = Some (UTYPE (mword_of_int 65536 : mword 20, Regidx (mword_of_int 12), LUI), s).
Proof. decode_bridge_ms. Qed.

Lemma bdec_10000737 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x10000737 : mword 32)) s
  = Some (UTYPE (mword_of_int 0x10000 : mword 20, Regidx (mword_of_int 14), LUI), s).
Proof. decode_bridge_ms. Qed.

Lemma bdec_10001737 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x10001737 : mword 32)) s
  = Some (UTYPE (mword_of_int 65537 : mword 20, Regidx (mword_of_int 14), LUI), s).
Proof. decode_bridge_ms. Qed.

Lemma bdec_100017b7 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x100017b7 : mword 32)) s
  = Some (UTYPE (mword_of_int 65537 : mword 20, Regidx (mword_of_int 15), LUI), s).
Proof. decode_bridge_ms. Qed.

Lemma bdec_100027f3 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x100027f3 : mword 32)) s
  = Some (CSRReg (Ox"100", Regidx (mword_of_int 0), Regidx (mword_of_int 15), CSRRS), s).
Proof. decode_bridge_ms. Qed.

Lemma bdec_1ff7f793 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x1ff7f793 : mword 32)) s
  = Some (ITYPE (mword_of_int 511 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 15), ANDI), s).
Proof. decode_bridge_ms. Qed.

Lemma bdec_21848513 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x21848513 : mword 32)) s
  = Some (ITYPE (mword_of_int 536, Regidx (mword_of_int 9), Regidx (mword_of_int 10), ADDI), s).
Proof. decode_bridge_ms. Qed.

Lemma bdec_2184a783 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x2184a783 : mword 32)) s
  = Some (LOAD (mword_of_int 536 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 15), false, 4), s).
Proof. decode_bridge_ms. Qed.

Lemma bdec_21c48513 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x21c48513 : mword 32)) s
  = Some (ITYPE (mword_of_int 540, Regidx (mword_of_int 9), Regidx (mword_of_int 10), ADDI), s).
Proof. decode_bridge_ms. Qed.

Lemma bdec_21c4a703 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x21c4a703 : mword 32)) s
  = Some (LOAD (mword_of_int 540 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 14), false, 4), s).
Proof. decode_bridge_ms. Qed.

Lemma bdec_21c4a783 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x21c4a783 : mword 32)) s
  = Some (LOAD (mword_of_int 540 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 15), false, 4), s).
Proof. decode_bridge_ms. Qed.

Lemma bdec_2204a783 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x2204a783 : mword 32)) s
  = Some (LOAD (mword_of_int 544, Regidx (mword_of_int 9), Regidx (mword_of_int 15), false, 4), s).
Proof. decode_bridge_ms. Qed.

Lemma bdec_2244a783 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x2244a783 : mword 32)) s
  = Some (LOAD (mword_of_int 548, Regidx (mword_of_int 9), Regidx (mword_of_int 15), false, 4), s).
Proof. decode_bridge_ms. Qed.

Lemma bdec_7ae50513 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x7ae50513 : mword 32)) s
  = Some (ITYPE (mword_of_int 0x7ae : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI), s).
Proof. decode_bridge_ms. Qed.

Lemma bdec_810ff0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x810ff0ef : mword 32)) s
  = Some (JAL (mword_of_int 2093072 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

Lemma bdec_a8650513 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xa8650513 : mword 32)) s
  = Some (ITYPE (mword_of_int 2694 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI), s).
Proof. decode_bridge_ms. Qed.

Lemma bdec_c12ff0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xc12ff0ef : mword 32)) s
  = Some (JAL (mword_of_int 2094098 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

Lemma bdec_d41ff0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xd41ff0ef : mword 32)) s
  = Some (JAL (mword_of_int 2096448 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

Lemma bdec_e2cff0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xe2cff0ef : mword 32)) s
  = Some (JAL (mword_of_int 2094636 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

Lemma bdec_eefff0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xeefff0ef : mword 32)) s
  = Some (JAL (mword_of_int 2096878 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* --------------------------------------------------------------------- *)
(* Words promoted when devintr became their second user (the private      *)
(* copies in CodeVirtioDiskIntr / WpKvmmap were retired at the same time).*)
(* --------------------------------------------------------------------- *)

(* beq a4,a5,+0x50 *)
Lemma bdec_04f70863 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x04f70863 : mword 32)) s
  = Some (BTYPE (mword_of_int 80 : mword 13, Regidx (mword_of_int 15), Regidx (mword_of_int 14), BEQ), s).
Proof. decode_bridge_ms. Qed.

(* jal ra,-0xc4 *)
Lemma bdec_f3dff0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xf3dff0ef : mword 32)) s
  = Some (JAL (mword_of_int 2096956 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.
