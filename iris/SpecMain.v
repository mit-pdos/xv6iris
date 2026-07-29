(* SpecMain.v -- the public interface of main() (kernel/main.c), the function
   every hart enters from [start()] in Supervisor mode and never leaves.

     volatile static int started = 0;
     void main() {
       if (cpuid() == 0) {
         consoleinit(); printkinit();
         printk("\n"); printk("xv6 kernel is booting\n"); printk("\n");
         kinit(); kvminit(); kvminithart(); procinit();
         trapinit(); trapinithart(); plicinit(); plicinithart();
         binit(); iinit(); fileinit(); virtio_disk_init(); userinit();
         __atomic_thread_fence(__ATOMIC_SEQ_CST);
         started = 1;
       } else {
         while (started == 0) ;
         __atomic_thread_fence(__ATOMIC_SEQ_CST);
         printk("hart %d starting\n", cpuid());
         kvminithart(); trapinithart(); plicinithart();
       }
       scheduler();
     }

   DIVERGING, like scheduler's: main's two arms join at [jal scheduler]
   (main+0x3e) and scheduler never returns, so this spec has NO continuation --
   the conclusion is a bare [WP Loop {{Φ}}].  [tools/proof_coverage.py] reads
   the shape off the entry [pc_is] plus a continuation that leaves the
   function; here the exit is the callee's entry symbol, exactly as in
   SpecEntry.v.

   THIS FILE STATES THE BOOT-HART CONTRACT ONLY ([fin_to_nat cpu_id = 0]).  The
   secondary-hart contract is designed but not statable yet: the per-hart
   resources its [kvminithart] needs are globally unique in today's model
   ([ptree_own] at full fraction inside [tlb_inv_pt], [kmap_auth] at fraction
   1), and [SchedCtx.procs_inv] is indexed by the AMBIENT hart through
   [p_sched]'s [cid_word], so hart 0's cannot be hart 1's.  See
   claude-notes/projects/main-boot.md (G5) for what has to move first.

   THE HANDOVER.  Everything the boot hart's initialisation gives the other
   harts crosses ONE channel, the invariant on [started]
   ([StartedInv.started_inv]): a one-shot escrow [∃ v, started ↦₄ v ∗
   (⌜v = 0⌝ ∨ P)] whose payload must be PERSISTENT, because up to [NCPU - 1]
   harts read the flag and each wants the payload.  main's boot arm is the
   only writer, and paying [P] in is what its [sw a5,778(a4)] costs.

   [P] rides here as a PARAMETER with [Persistent P] -- the boot hart is handed
   the deposit and parks it.  The target shape is a WAND,
   [□ (∀ γd γv γs …, <the init sequence's persistent output> -∗ P)], so that
   hart 0 pays the deposit out of what it actually built rather than being
   handed it; that awaits the device-invariant split (main-boot.md G1), because
   until [dev_inv] is split into UART/PLIC and disk halves the init sequence's
   output cannot be written down truthfully -- printk() runs twelve calls before
   virtio_disk_init(), so the bundled invariant cannot exist where printk needs
   it.  Everything else in this statement is settled.

   Requires only Spec files and the definitional layer -- never a [Proof*] file. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes.
Require Import RiscvLang RiscvPtsto.
Require Import RegFile InstrBytes.
Require Import SmodeCore.
Require Import CalleeSaved KernelText KernelDataInv.
Require Import IntrDefs.
Require Import SpecPanic.
Require Import StartedInv.
(* the callees, for the vocabulary main's precondition is stated in *)
Require Import SpecConsoleinit SpecPrintkinit SpecKinit SpecKvminit.
Require Import SpecProcinit SpecTrapinit SpecPlicinit.
Require Import SpecBinit SpecIinit SpecFileinit SpecVirtioDiskInit.
Require Import SpecScheduler SpecFreerange.
Require Import ProcGeom FdSlots CpuOwn.
Require Import KallocInv KvmSpec BcacheInv SleepLock.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
From Kernel Require KernelSyms.

Notation MN := KernelSyms.main.

(* main's stack budget: its own 16-byte / 2-slot frame over its deepest
   callee.  kvminit wants 50, printk 38, kinit 22, virtio_disk_init
   [K_virtio_disk_init] = 18, binit/iinit 12, procinit 10, consoleinit 6,
   plicinithart 4 -- and scheduler needs 20 available at the depth main calls
   it from, which 50 covers. *)
Definition K_main : nat := 52%nat.

Section SpecMain.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !kallocG Σ, !fileG Σ, !fdslotG Σ}.
  Context `{!uartGhostG Σ, !diskGhostG Σ}.
  Context `{CID : CpuId}.

  (* ------------------------------------------------------------------- *)
  (* The nine spinlocks and two standalone locks the init sequence brings *)
  (* up, each as [SpecProcinit.lk_raw] -- the three cells [lk ↦₄ _],      *)
  (* [lock_name_field lk ↦₈ _], [lk_cpu lk ↦₈ _] bundled with their       *)
  (* values existentially quantified, which is the only shape a caller    *)
  (* can honestly claim about a static global it has never written.       *)
  (* ------------------------------------------------------------------- *)
  Definition main_locks_raw : iProp Σ :=
    (lk_raw (mword_of_int KernelSyms.cons) ∗       (* consoleinit: cons.lock  *)
     lk_raw (mword_of_int KernelSyms.tx_lock) ∗    (* consoleinit: uart tx    *)
     lk_raw (mword_of_int KernelSyms.pr) ∗         (* printkinit              *)
     lk_raw (mword_of_int KernelSyms.kmem) ∗       (* kinit                   *)
     lk_raw pid_lock_addr ∗                        (* procinit                *)
     lk_raw wait_lock_addr ∗                       (* procinit                *)
     lk_raw (mword_of_int KernelSyms.tickslock) ∗  (* trapinit                *)
     lk_raw bcache_addr ∗                          (* binit                   *)
     lk_raw itable_addr ∗                          (* iinit                   *)
     lk_raw (mword_of_int KernelSyms.ftable) ∗     (* fileinit                *)
     lk_raw disk_lock)%I.                          (* virtio_disk_init        *)

  (* ------------------------------------------------------------------- *)
  (* The rest of the raw global image the init sequence writes: the two   *)
  (* [devsw] slots, kmem's NULL free list, the kernel page-table root,    *)
  (* the 64 dormant processes and the WHOLE fd-slot supply, the buffer    *)
  (* cache, the inode sleeplocks, and the disk's three queue pointers +   *)
  (* [free[8]].                                                          *)
  (* ------------------------------------------------------------------- *)
  Definition main_globals_raw : iProp Σ :=
    ((∃ r w : mword 64,
        devsw_console_read ↦₈ r ∗ devsw_console_write ↦₈ w) ∗
     (mword_of_int (KernelSyms.kmem + 24) : mword 64) ↦₈ (mword_of_int 0 : mword 64) ∗
     (∃ kpt0 : mword 64,
        (mword_of_int KernelSyms.kernel_pagetable : mword 64) ↦₈ kpt0) ∗
     ([∗ list] i ∈ seq 0 NPROC, proc_raw (proc_addr i)) ∗
     fd_slots (NPROC * (NOFILE + FDSPARE)) ∗
     ([∗ list] k ∈ seq 0 NBUF, sl_raw (buf_lock (bnode k))) ∗
     ([∗ list] k ∈ seq 0 NBUF, blink_raw (bnode k)) ∗
     blink_raw bhead ∗
     ([∗ list] i ∈ seq 0 NINODE, sl_raw (inode_lock i)) ∗
     (∃ pd pav pu : mword 64,
        disk_desc ↦₈ pd ∗ disk_avail ↦₈ pav ∗ disk_used ↦₈ pu) ∗
     (∃ free0 : nat -> bv 8,
        [∗ list] j ∈ seq 0 8, (pa_add disk_free j) ↦ₘ free0 j))%I.

  (* ------------------------------------------------------------------- *)
  (* The three device fragments, all RAW: consoleinit programs the UART,  *)
  (* plicinit the interrupt controller, virtio_disk_init resets the disk  *)
  (* and publishes its queue.  Nothing is assumed about any of the three  *)
  (* initial states.  The device INVARIANT is not a precondition -- main  *)
  (* is what allocates it, out of these.                                  *)
  (* ------------------------------------------------------------------- *)
  Definition main_devices_raw (u0 : uart_state) (p0 : plic_state)
      (v0 : virtio_state) : iProp Σ :=
    (uart_frag u0 ∗ plic_frag p0 ∗ virtio_frag v0)%I.

  (* ------------------------------------------------------------------- *)
  (* This hart's own translation and trap resources.  [strans_bit bare]   *)
  (* is the still-Bare receipt kvminithart's switch flips; [tlb] is the    *)
  (* cell it seals into the kernel-page-table arm; [trap_csrs] is what the *)
  (* scheduler's level-0 SIE flip consumes at the far end.  None of these  *)
  (* crosses the [started] invariant -- every hart gets its own from its   *)
  (* own [_entry] -> [start].                                             *)
  (* ------------------------------------------------------------------- *)
  Definition main_hart_raw
      (tlbvec0 : vec (option TLB_Entry) (2 ^ 6)) : iProp Σ :=
    (strans_bit strans_bit_bare ∗ tlb ↦ᵣ tlbvec0 ∗ trap_csrs)%I.

  (* ------------------------------------------------------------------- *)
  (* main(), entered on the BOOT hart.                                    *)
  (* ------------------------------------------------------------------- *)
  Definition wp_main_boot_sconf_body
      (γ : gname) (Φ : mval -> iProp Σ)
      (m : regfile) (K : nat)
      (p0 : mword 64) (C : iProp Σ)
      (ps : list (mword 64)) (s1entry phystop : mword 64)
      (u0 : uart_state) (pl0 : plic_state) (v0 : virtio_state)
      (tlbvec0 : vec (option TLB_Entry) (2 ^ 6))
      (P : iProp Σ) :=
    let pcE : mword 64 := mword_of_int KernelSyms.main in
    (* the arm is decided by the ambient hart: [beqz a0] at main+0x14 takes
       the boot path exactly when cpuid() returns 0. *)
    cid_word = (zero_reg : mword 64) ->
    (K_main <= K)%nat ->
    (* the tp/cid convention every callee in the kalloc cone requires *)
    m !!! Regidx (mword_of_int 4 : mword 5) = cid_word ->
    (* kinit's free-page run: [end .. PHYSTOP), page-aligned *)
    phystop = (mword_of_int 0x88000000 : mword 64) ->
    s1entry = add_vec (and_vec (add_vec (mword_of_int 0x80023558 : mword 64)
                        (mword_of_int 4095 : mword 64)) negPGSIZEv) PGSIZEv ->
    prun phystop s1entry ps ->
    (* enough pages for kvmmake's 102 nodes, the 64 kstacks and the disk's 3 *)
    (K_kvmmake + 64 + 3 < length ps)%nat ->
    sie_cap_gpr γ m K -∗
    cpu_own γ 0 false p0 C -∗
    kernel_text -∗ kernel_data -∗ pc_is pcE -∗
    panic_wp -∗
    (* the handover channel, and the deposit it will carry *)
    started_inv P -∗ □ P -∗
    (* the boot supply *)
    main_locks_raw -∗
    main_globals_raw -∗
    main_devices_raw u0 pl0 v0 -∗
    main_hart_raw tlbvec0 -∗
    ([∗ list] p ∈ ps, page_own p) -∗
    (* ...and what the scheduler at the far end still wants, which main
       cannot build: the proc-lock names are chosen when main allocates the
       64 locks out of procinit's output, so [γs] is quantified in the
       statement inside the proof and [procs_inv] is NOT a precondition. *)
    WP (Loop : expr riscv_lang) {{ Φ }}.

End SpecMain.

Module Type MAIN.
  Parameter wp_main_boot_sconf :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ, !kallocG Σ, !fileG Σ, !fdslotG Σ}
      `{!uartGhostG Σ, !diskGhostG Σ} `{CID : CpuId}
      (γ : gname) (Φ : mval -> iProp Σ)
      (m : regfile) (K : nat)
      (p0 : mword 64) (C : iProp Σ)
      (ps : list (mword 64)) (s1entry phystop : mword 64)
      (u0 : uart_state) (pl0 : plic_state) (v0 : virtio_state)
      (tlbvec0 : vec (option TLB_Entry) (2 ^ 6))
      (P : iProp Σ),
      wp_main_boot_sconf_body γ Φ m K p0 C ps s1entry phystop
        u0 pl0 v0 tlbvec0 P.
End MAIN.
