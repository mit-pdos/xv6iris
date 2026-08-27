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

   THIS FILE STATES THE BOOT-HART CONTRACT ONLY ([fin_to_nat cpu_id = 0]), but
   nothing in the TRANSLATION story blocks the secondary contract any more.
   The KERNEL PAGE TABLE is shared: main's boot arm publishes it as
   [KptShare.kpt_inv] and every hart's Sv39 translation runs on the per-hart
   residue [tlb_res_pt], so the table rides to the secondaries in [P] below.
   And the PRE-SWITCH phase is now per-hart too (claude-notes/projects/
   bare-inv-generic.md): [SRegime.bare_inv] holds only this hart's satp/PMP
   cells -- the globally unique [kmap_auth kmap_M0] moved OUT of it, into
   this precondition as a boot token spent in main's own publication
   assembly, before the kvminithart call -- so every hart can spin on
   [started] in its own Bare arm at once.
   [SchedCtx.procs_inv] is no longer an obstacle: since proc contexts became
   MIGRATABLE (claude-notes/completed/sched-hart-generic.md) it mentions
   neither a hart nor a per-hart SIE ghost, it is persistent, and it is
   exactly what the [started] payload can carry to every secondary.

   THE DEVICES.  The three device invariants ([WpUart.uart_inv] /
   [plic_inv] / [disk_inv], bundled as [dev_inv]) exist FROM TIME 0: they are
   allocated in adequacy, before any thread runs.  They have to be -- the UART,
   disk and PLIC threads are top-level threads of the system and each needs its
   device fragment at EVERY step (a UART rx byte can arrive at step 0; the disk
   thread must refute [DevStepDiskWild] at every step; the PLIC gateway latches
   whenever an irq line is up), so no device fragment can ever sit raw in a
   CPU's precondition.  main is therefore HANDED the bundle rather than
   allocating it, and what it is handed alongside is the boot hart's TOKENS:
   the exclusive transmitter [uart_tx_own γd l0] with its receipt and out-list
   lower bound at the same [l0], the UNFROZEN DLAB half (uartinit performs the
   divisor-latch dance and freezes the half at its final LCR write), and the
   virtio config tracker's half at a not-live [c0] (virtio_disk_init programs
   the queue under the invariant and keeps deterministic knowledge of the
   configuration through this half).  See claude-notes/projects/main-boot.md G1.

   THE HANDOVER.  Everything the boot hart's initialisation gives the other
   harts crosses ONE channel, the invariant on [started]
   ([StartedInv.started_inv]): a one-shot escrow [∃ v, started ↦₄ v ∗
   (⌜v = 0⌝ ∨ P)] whose payload must be PERSISTENT, because up to [NCPU - 1]
   harts read the flag and each wants the payload.  main's boot arm is the
   only writer, and paying [P] in is what its [sw a5,778(a4)] costs.

   [P] IS PAID OUT OF WHAT MAIN BUILT.  It rides as a parameter with
   [Persistent P], but the boot hart is not handed it -- it is handed a WAND
   and applies it at the [started = 1] store.  Its arguments are exactly the
   persistent facts whose GHOST NAMES main chooses: [γpr] when it allocates the
   [pr] lock out of printkinit's output (pr.lock protects the transmitter token
   -- SpecPrintk.v), [γs] when it allocates the 64 proc locks out of
   procinit's ([SpecProcinit.procs_inv_alloc]), and [γk] when it allocates the
   vdisk_lock over [DiskInv.disk_res] out of virtio_disk_init's
   ([DiskBoot.disk_res_boot]) -- the disk's PAGES (its configuration identity)
   are chosen by kalloc inside virtio_disk_init, so [pd pav pu] are quantified
   here too, and the persistent [DiskInv.disk_geom] that names them travels
   alongside the lock.

   ... and, out of MAIN'S OWN PUBLICATION ASSEMBLY -- the one-way door it
   runs between kvminit and kvminithart -- THE KERNEL PAGE TABLE: the shared
   invariant [KptShare.kpt_inv root] it allocates out of kvminit's exclusive
   tree and the [kpt_unset] one-shot, the root cell it PERSISTS after
   kvminit wrote it ([kernel_pagetable ↦₈□ root_b]), and the 65 mapping
   claims it mints out of [kmap_auth kmap_M0] (trampoline + the 64 kernel
   stacks).  None of it comes from kvminithart's post any more.  The root
   and the kstack pas are kalloc-chosen inside kvminit, so [root] and [pas]
   are quantified in the wand exactly as the disk's pages are.  All of it is
   persistent, which is what lets it ride the one-shot escrow to every
   secondary -- a secondary's own kvminithart needs no exclusive tree, only
   [kpt_inv] and the root cell.

   Everything else a secondary hart wants is either already persistent in
   main's own precondition (the device bundle) or, per G5, not statable yet.
   main's proof therefore never has to know what the secondaries want.

   THE INTERRUPT QUARTER.  [IntrDefs]'s SIE choreography splits the live-bit
   ghost 1/2 (tied in [sconf]) + 1/8 (the capability's arm) + 1/8 (the
   push/pop count) + 1/4 (the INVARIANT's).  The invariant is
   [IntrDefs.intr_inv], and main is the only code that ever allocates it
   ([intr_inv_alloc_off], from trapinithart's [stvec ↦ᵣ kernelvec]) -- so the
   spare quarter has to sit raw in main's precondition until then.  That is the
   [ghost_var γ (1/4) ('b"0")] conjunct below; before the allocation nothing
   holds an interrupt handler, hence the '0'.

   THE CONTEXT SLOT is [SchedCtx.cpu_ctx_free], not an opaque [C]: nothing on
   the boot path parks anything in [cpus[0].context], and [scheduler] at the
   far end consumes [cpu_own γ 0 false p0 cpu_ctx_free] at exactly that shape.

   Requires only Spec files and the definitional layer -- never a [Proof*] file. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list finite bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap ghost_map.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes.
Require Import RiscvLang RiscvPtsto.
Require Import RegFile InstrBytes.
Require Import KptPt.
Require Import KernelText KernelDataInv.
Require Import IntrDefs.
Require Import WireInv.   (* [wire_inv] *)
Require Import HartTp.
(* the shared kernel page table: [kpt_unset] is a boot token, [kpt_inv] and
   the 65 claims are what the deposit wand carries to the secondaries *)
Require Import KptGhost KptShare KptExecMap KvmMap.
Require Import KMap.
Require Import TimerCap.
Require Import StartedInv.
(* the callees, for the vocabulary main's precondition is stated in *)
Require Import ConsoleInv.
Require Import SpecConsoleintr.
Require Import SpecConsoleinit.
Require Import SpecProcinit.
(* [IcacheBoot.ientry_raw] -- the fifty itable ENTRIES' cells, which iinit
   does not touch and [IcacheBoot.icache_boot] takes.  Imported BEFORE
   [SpecIinit] on purpose: only [IcacheBoot]'s own names come in (Import is
   not transitive), but keeping the order makes the [NINODE] below
   unambiguously [SpecIinit]'s if that ever changes. *)
Require Import IcacheBoot.
(* [ROOTDEV] / [icfg_dev] / [icfg_nib], for the two config ties above *)
Require Import SpecIinit SpecVirtioDiskInit.
Require Import SpecFreerange SpecPrintk.
Require Import ProcGeom FdSlots CpuOwn SchedCtx.
Require Import KallocInv KvmSpec BcacheInv SleepLock.
Require Import DiskPtsto WpUart.
Require Import VirtioModel.
(* [DiskInv] for the vdisk_lock's vocabulary: [d_used_idx] and
   [disk_slot_raw] are cells of the static [struct disk] that main hands
   over, and [VirtioProto] for the two disk ghosts adequacy mints
   ([dn_claim]'s authority and [disk_done_lb]).  The [disk_res] these
   assemble into is built by [DiskBoot.disk_res_boot], in main's PROOF. *)
Require Import VirtioQueue VirtioProto DiskInv.
(* the classes this statement's [Context] must bind for real: without these
   [Require Import]s the backtick generalization silently invents fresh binders
   named [lockG]/[fileG] instead, and [printk_env]/[procs_inv] then cannot
   resolve their [lockG] instance (spec-modules.md's Link-file gotcha, in a
   Spec file). *)
Require Import WpLock TicksInv.
Require Import FileInvDefs.
(* [FsCfgBoot.fs_boot_supply] -- the file system's boot-era mint, threaded
   from [BootShared.boot_shared_alloc] through [BootChain.boot_hart_primary]
   to here (fs-cfg-boot.md stage (e), the [procs_avail] threading of
   main-boot.md §G3 at full width).  This file names only the bundled row;
   [ProofMain.mn_grp_fs] is what opens it. *)
Require Import FsCfgBoot.
(* the [struct log]'s cell names -- [SpecFsinit]'s and [SpecInitlog]'s raw
   premises, carried here because NOTHING carved them before stage (f)
   (fs-cfg-boot.md (f-2), rows (A)). *)
Require Import LogDefs LogInv.
(* [BioInitAt.buf_raw] -- the thirty zeroed [struct buf] payload rows, carved
   with the buffer sleeplocks and carried across binit for [bio_init_at]
   (fs-cfg-boot.md stage (f)). *)
Require Import BioInitAt.
Require Import IrefSlots.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
From Kernel Require KernelSyms.
Require Import WaitInv.   (* [wait_res] -- what wait_lock is over *)
Require Import ProcAvail.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)


(* main's stack budget: its own 16-byte / 2-slot frame over its deepest
   callee.  kvminit wants 50, printk 38, kinit 22, virtio_disk_init
   [K_virtio_disk_init] = 18, binit/iinit 12, procinit 10, consoleinit 6,
   plicinithart 4 -- and scheduler needs 20 available at the depth main calls
   it from, which 50 covers.

   THE SCHEDULER'S TRAP RESERVE IS WHAT SETS THIS, NOT THE kvminit CONE.
   main's last act is [jal scheduler], which never returns, and scheduler()
   is entered with interrupts OFF and enables them at its loop head -- an
   enable at a point where nobody holds the trap reserve, so it funds
   [kv_frame_slots] out of the budget main hands it ([SpecScheduler]'s
   premise is [kv_frame_slots + 20 <= av]).  Below main's own 2-slot frame
   that is [2 + kv_frame_slots + 20 = 100] slices, which dominates the 52 the
   init cone needs.  The boot bridge hands out [kv_frame_slots + K_main]
   ([BootBridge.boot_stack_slots]), i.e. 180 slots = 1440 bytes of the
   4096-byte per-hart stack, so nothing upstream has to change. *)
Notation K_main := (122%nat) (only parsing).
Section SpecMain.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fileG Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  (* ------------------------------------------------------------------- *)
  (* The eleven [struct spinlock]s the init sequence brings up, each as   *)
  (* [SpecProcinit.lk_raw] -- the three cells [lk ↦₄ _],                  *)
  (* [lock_name_field lk ↦₈ _], [lk_cpu lk ↦₈ _] bundled with their       *)
  (* values existentially quantified, which is the only shape a caller    *)
  (* can honestly claim about a static global it has never written.       *)
  (*                                                                     *)
  (* [tx_lock] IS ONE OF THEM: it is a [struct spinlock] (uartwrite takes *)
  (* and releases it around each LSR-check/THR-write pair and parks       *)
  (* OUTSIDE it, so nothing is held across a park), and uartinit's        *)
  (* trailing [initlock(&tx_lock, "uart")] is what consumes this entry.   *)
  (* Its boot-carve window is 24 bytes like every other one here          *)
  (* ([BootCarveMain.boot_lk_raw]), which the layout confirms:            *)
  (* [pr + 24 = tx_lock] exactly and [tx_lock + 24 = kmem] exactly.       *)
  (* ------------------------------------------------------------------- *)
  Definition main_locks_raw : iProp Σ :=
    (lk_raw (mword_of_int KernelSyms.cons) ∗       (* consoleinit: cons.lock  *)
     lk_raw (mword_of_int KernelSyms.tx_lock) ∗    (* -> uartinit: uart tx    *)
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
  (*                                                                     *)
  (* PLUS the cells of the static [struct disk] that virtio_disk_init      *)
  (* never touches but the vdisk_lock's resource ([DiskInv.disk_res])      *)
  (* owns: [used_idx], and per descriptor slot the [info[i]] pair and the  *)
  (* [ops[i]] header ([DiskInv.disk_slot_raw]).  [used_idx] is CONCRETE    *)
  (* zero -- it is a .bss cell the loader zeroed, and [disk_res] wants it  *)
  (* at [wrap16 nr] with the completed count [nr = 0] at boot -- the same  *)
  (* precedent as the [kmem+24 ↦₈ 0] conjunct above; the others stay       *)
  (* contents-existential, which is all [free_slot_res] needs.            *)
  (*                                                                     *)
  (* PLUS two groups that no callee's precondition names but a caller-    *)
  (* side ASSEMBLY does, and which therefore have nowhere else to come    *)
  (* from:                                                               *)
  (*  - per process, the two PUBLIC cells procinit never touches:          *)
  (*    [p_chan] and [SchedCtx.proc_pub] (killed / xstate / the           *)
  (*    invariant's permanent HALF of the pid cell -- [proc_raw] carries   *)
  (*    the other half).  [SpecProcinit.procs_inv_alloc] consumes exactly  *)
  (*    [proc_ready i] plus these two, so they are main's to supply.       *)
  (*  - [initproc], the one global userinit writes.                        *)
  (*                                                                     *)
  (* WHAT IS NO LONGER HERE: the two [volatile int] flag cells            *)
  (* [panicking] / [panicked].  main used to own them because it          *)
  (* allocated the invariant printk's general path read them through;     *)
  (* upstream d80e61c5 DELETED both globals (printk always takes pr.lock  *)
  (* now, uartputc_sync always takes tx_lock), so there is no such symbol *)
  (* to carve and no invariant to allocate -- [printk_env] is three       *)
  (* conjuncts, not four.                                                 *)
  (* ------------------------------------------------------------------- *)
  (* the 32 dead .bss bytes at [&sb], contents-existential.  Spelled at
     [mword_of_int KernelSyms.sb], which is [FirstTok.first_sb_base] and
     [SpecFsinit.sb_base] on the nose. *)
  Definition main_sb_raw : iProp Σ :=
    (∃ sb_old : nat -> bv 8,
       [∗ list] i ∈ seq 0 32,
         pa_add (mword_of_int KernelSyms.sb : mword 64) i ↦ₘ sb_old i)%I.

  (* the whole [struct log] at [KernelSyms.log]: the spinlock triple, the
     six scalar fields and the thirty [lh.block] words, in exactly the
     shape [SpecFsinit]'s premise pile spells them. *)
  Definition main_log_raw : iProp Σ :=
    (∃ (vlock v_start v_dev v_nc v_n : mword 32) (vname vcpu : mword 64),
       log_addr ↦₄ vlock ∗
       lock_name_field log_addr ↦₈ vname ∗ lock_cpu log_addr ↦₈ vcpu ∗
       l_start ↦₄ v_start ∗ l_dev ↦₄ v_dev ∗
       l_out ↦₄ (mword_of_int 0 : mword 32) ∗
       l_cmt ↦₄ (mword_of_int 0 : mword 32) ∗
       l_ncommit ↦₄ v_nc ∗ lh_n_pa ↦₄ v_n ∗
       ([∗ list] i ∈ seq 0 LOGBLOCKS, ∃ w : mword 32, lh_block i ↦₄ w))%I.

  Definition main_globals_raw : iProp Σ :=
    ((∃ r w : mword 64,
        devsw_console_read ↦₈ r ∗ devsw_console_write ↦₈ w) ∗
     (* ...and the eighteen devsw entries consoleinit never writes, still as
        the BSS left them.  consoleinit turns all twenty into the duplicable
        [ConsoleInv.devsw_table] (SpecConsoleinit.v); this is the raw side. *)
     ConsoleInv.devsw_rest ∗
     (mword_of_int (KernelSyms.kmem + 24) : mword 64) ↦₈ (mword_of_int 0 : mword 64) ∗
     (* the kernel page-table root: RAW here (kvminit writes it), and
        PERSISTED by main in its publication assembly right after, before
        the kvminithart call that reads it -- the ↦₈□ form is what the
        deposit wand hands the secondaries *)
     (∃ kpt0 : mword 64,
        (mword_of_int KernelSyms.kernel_pagetable : mword 64) ↦₈ kpt0) ∗
     ([∗ list] i ∈ seq 0 NPROC, proc_raw (proc_addr i)) ∗
     ([∗ list] i ∈ seq 0 NPROC,
        (∃ ch : mword 64, p_chan (proc_addr i) ↦₈ ch) ∗
        proc_pub (proc_addr i)) ∗
     (* ...AND WHAT wait_lock IS OVER.  [WaitInv.wait_res] is [∃ ps,
        parents_own ps], the NPROC [p_parent] cells -- the one part of a
        [struct proc] that belongs to a lock OTHER than p->lock, which is
        why it is not in either big-op above.  The image owns the cells and
        [BootCarveMain]'s slot carve used to drop them with the padding; it
        carves them now, and main pairs them with the [lk_raw
        wait_lock_addr] it already holds to make the [is_lock] every
        consumer of wait_lock (kexit, kwait, reparent, the syscall
        environment) has always taken and nobody has ever built. *)
     WaitInv.wait_res ∗
     fd_slots (NPROC * (NOFILE + FDSPARE)) ∗
     (* ... and the iref supply's proc-layer share: 1 + IREFSPARE per
        process, the [1] being its cwd unit.  The remaining [NFILE] units of
        [IrefSlots.IREFSLOTS] are the file table's. *)
     iref_slots (NPROC * (1 + IREFSPARE)) ∗
     (* ... AND THE OPEN-FILE TABLE, in the three rows [FileInv.ftable_res_boot]
        takes.  [ftable] is the LAST of the eleven locks whose resource main
        had no way to build: the hundred [struct file] entries were dropped
        by the .bss walk with the padding around them (exactly as the
        [p_parent] cells were), so [FileInv.ftable_res] had no producer and
        [is_ftable] -- which the syscall environment, kfork, kexit and every
        sys_open path take -- had none either.  The carve is
        [BootCarveMain.boot_file_entries].

        The two ghost rows are what a free table costs beside its cells: the
        fd-slot AUTHORITY, which lives in [ftable_res] because the table is
        where the one-unit-per-reference conservation law is checked, and one
        iref unit per FREE slot, because an untyped payload IS its iref unit
        ([FileInvDefs.file_core_none]).  These are the [NFILE] units
        [IrefSlots.IREFSLOTS] is sized for; the boot chain's own two are
        [IREFBOOT] and are a separate row above. *)
     ([∗ list] k ∈ seq 0 NFILE, fentry_raw k) ∗
     iref_slots NFILE ∗
     fd_slots_auth ∗
     (* ... and the bio supply's proc-layer share: THREE units per process,
        what the trap loop's residue carries for a live process's next
        syscall.  procinit routes them so that a DORMANT slot owns three --
        allocproc has to have something to hand a process that has not run
        yet, and kexit gives them back at the ZOMBIE park.  Unlike the two
        supplies above this is not the whole pool: [3 * NPROC = 192] of
        [BioDefs.BSLOTS = 1024], the rest being the file system's. *)
     bslots (NPROC * 3) ∗
     (∃ v0 : mword 64, (mword_of_int KernelSyms.initproc : mword 64) ↦₈ v0) ∗
     (* [ticks], the tick counter tickslock protects.  It is here for the same
        reason [lk_raw tickslock] is: a static global the init sequence brings
        under a lock.  main needs it to ALLOCATE that lock -- [is_tickslock] is
        [is_lock … ticks_res], and [ticks_res] is this cell -- which is what
        the handler contract's [tick_keeper] conjunct asks of the tick hart. *)
     (∃ t : mword 32, a_ticks ↦₄ t) ∗
     ([∗ list] k ∈ seq 0 NBUF, sl_raw (buf_lock (bnode k))) ∗
     ([∗ list] k ∈ seq 0 NBUF, blink_raw (bnode k)) ∗
     blink_raw bhead ∗
     (* ...and the REST of each buffer, which binit never touches: the four
        zeroed metadata words (valid / disk / dev / blockno), the reference
        count, and the 1024 data bytes.  These are [BioInitAt.bio_init_at]'s
        physical premise -- the ghost step from binit's postcondition to the
        buffer cache's precondition consumes them beside the thirty
        [sl_fresh]es, at main+0x8e's return.  The five words' pinned zeros are
        a loader FACT (the bcache is .bss past the image) on the [ientry_raw]
        / [d_used_idx] / [kmem+24] precedent, and they are what makes
        [BioInv.bio_init]'s "every buffer starts invalid at blockno 0" true
        rather than assumed. *)
     ([∗ list] k ∈ seq 0 NBUF, buf_raw k) ∗
     (* ---- ROWS (A) OF THE fsinit BUNDLE, part 1: the 32 raw bytes of the
        static [struct superblock].  &sb sits in the .bss GAP between the
        buffer cache and the itable, and NOTHING carved it before stage (f):
        it is what fsinit's [memmove] at +0x26 kills, and it reaches
        forkret's first arm inside [FirstTok.first_fsinit].  The bytes are
        contents-existential -- they are dead .bss until that memmove. ---- *)
     main_sb_raw ∗
     ([∗ list] i ∈ seq 0 NINODE, sl_raw (inode_lock i)) ∗
     (* ...and the REST of each itable entry, which iinit never touches:
        dev/inum/valid, the dinode mirror's metadata and addrs cells, and
        [ref] at CONCRETE zero.  These are [IcacheBoot.icache_boot]'s
        [ientry_raw]s -- the ghost step from iinit's postcondition to the
        inode cache's precondition consumes them beside the fifty
        [sl_fresh]es.  [ref]'s pinned zero is [IcacheInv.iref_cells ∅]'s
        requirement and is a loader FACT (the itable is .bss past the
        image), on the [d_used_idx] / [kmem+24] precedent above.
        CONSUMED at main+0x92 since fs-cfg-boot.md stage (e): the stocked
        inode pool that used to be missing is [FsCfgBoot.fs_kit_icache]'s
        [ipool] row, minted in the boot-era fupd, and
        [ProofMain.mn_grp_fs] runs [IcacheBoot.icache_boot_at] on the two
        halves together. *)
     ([∗ list] k ∈ seq 0 NINODE, ientry_raw k) ∗
     (* ---- ROWS (A), part 2: the whole static [struct log].  Same story as
        [main_sb_raw]: initlog writes it, nothing carved it, and it rides
        [FirstTok.first_fsinit] to forkret.  [l_out] and [l_cmt] are at
        PINNED ZERO on the [ientry_raw] / [d_used_idx] / [kmem+24]
        precedent (the log record is .bss past the image, so the loader
        zeroed it) -- and initlog's contract takes them at exactly that
        value. ---- *)
     main_log_raw ∗
     (∃ pd pav pu : mword 64,
        disk_desc ↦₈ pd ∗ disk_avail ↦₈ pav ∗ disk_used ↦₈ pu) ∗
     (∃ free0 : nat -> bv 8,
        [∗ list] j ∈ seq 0 8, (pa_add disk_free j) ↦ₘ free0 j) ∗
     d_used_idx ↦₂ wrap16 0%nat ∗
     ([∗ list] i ∈ seq 0 8, disk_slot_raw i) ∗
     (* the console ring, [cons+24 .. cons+164): the 128 input bytes and the
        three index words.  It is here for the same reason [ticks] is -- a
        static global the init sequence brings under a lock -- and main needs
        it to run the [WpLock.newlock] that turns consoleinit's postcondition
        into [ConsoleInv.is_conslock], one half of [console_caps]. *)
     cons_res)%I.

  (* ------------------------------------------------------------------- *)
  (* This hart's own translation and trap resources.  [strans_bit bare]   *)
  (* is the still-Bare receipt kvminithart's switch flips; [tlb] is the    *)
  (* cell it seals into the kernel-page-table arm; [trap_csrs_raw] is what *)
  (* the scheduler's level-0 SIE flip consumes at the far end.  None of    *)
  (* these crosses the [started] invariant -- every hart gets its own from *)
  (* its own [_entry] -> [start].                                         *)
  (*                                                                      *)
  (* [trap_csrs_raw], NOT [trap_csrs]: the folded bundle carries           *)
  (* [IntrDefs.intr_res] -- an INSTALLED trap vector together with its     *)
  (* contract -- and at boot there is no such thing.  main folds the two   *)
  (* together once trapinithart has written stvec and                     *)
  (* [kernelvec_handler_spec] is in hand, which is also the moment the     *)
  (* claim first becomes true.                                            *)
  (* ------------------------------------------------------------------- *)
  Definition main_hart_raw
      (tlbvec0 : vec (option TLB_Entry) (2 ^ 6)) : iProp Σ :=
    (strans_pending ∗ tlb ↦ᵣ tlbvec0 ∗ trap_csrs_raw)%I.

  (* ------------------------------------------------------------------- *)
  (* main(), entered on the BOOT hart.                                    *)
  (* ------------------------------------------------------------------- *)
  Definition wp_main_boot_sconf_body
      
      (m : regfile) (K : nat)
      (p0 : mword 64)
      (ps : list (mword 64)) (s1entry phystop : mword 64)
      (γd : uart_names) (γv : disk_names)
      (l0 : list (bv 8)) (b0 : bool) (c0 : virtio_cfg)
      (* THE FILE SYSTEM'S BOOT-ERA MINT, as the era chose it: the disk's
         bytes, the parsed superblock, the inode region's block count and
         the coverage set.  They are PARAMETERS and not projections of the
         ambient [icfg]/[fscfg] because [fs_boot_supply]'s ten ties are what
         connect the two, and main spends the ties, not the image. *)
      (dk : Z -> bv 8) (sb : FsImg.fs_sb) (nib : nat) (cov : gset Z)
      (ndisk : nat)
      (* ...AND THE DURABLE SNAPSHOT THE ERA WAS MINTED FROM (durable-disk
         lane E-himg): the abstract state the committed view encodes, the
         committed view itself as a block view, and the set of blocks the
         era fupd spent.  [sb]/[nib] above are no longer free -- they are
         [S]'s own superblock and region width, which is what
         [FsCfgBoot.fs_boot_snap_wf] says. *)
      (S : FsState.fs_state_rec) (Pb : Z -> list (bv 8)) (Rspent : gset Z)
      (tlbvec0 : vec (option TLB_Entry) (2 ^ 6))
      (P : iProp Σ) `{!Persistent P} :=
    let pcE : mword 64 := mword_of_int KernelSyms.main in
    (* the arm is decided by the ambient hart: [beqz a0] at main+0x14 takes
       the boot path exactly when cpuid() returns 0. *)
    cid_word = (zero_reg : mword 64) ->
    (K_main <= K)%nat ->
    (* kinit's free-page run: [end .. PHYSTOP), page-aligned.  The cursor is
       PGROUNDUP(end) + PGSIZE, and [PageGeom.kmem_lo] IS the dumped `end`
       symbol (a plain [Z] literal computed from [KernelSyms.end_] at its own
       definition, so [vm_compute]/[lia] see a number here) -- never a
       transcribed address, which goes stale on every image bump. *)
    phystop = (mword_of_int 0x88000000 : mword 64) ->
    s1entry = add_vec (and_vec (add_vec (mword_of_int kmem_lo : mword 64)
                        (mword_of_int 4095 : mword 64)) negPGSIZEv) PGSIZEv ->
    prun phystop s1entry ps ->
    (* enough pages for kvmmake's 102 nodes, the 64 kstacks and the disk's 3 *)
    (K_kvmmake + 64 + 3 < length ps)%nat ->
    (* the disk's protocol is in its not-live arm at boot: virtio_disk_init
       makes it live, and its config half [c0] is how main knows so *)
    virtio_live c0 = false ->
    (* the inode region is nonempty.  It is [BootShared.fs_boot_image_wf]'s
       fifth conjunct, and it reaches here as a PURE premise rather than as
       one of [fs_boot_supply]'s ties because the era holds it about [nib]
       and the boot chain has it in hand; main forwards it to userinit's
       namei corner, where [icfg_nib = 0] would make the returned
       [IcacheRef.inode_held] uninhabitable. *)
    (* THE WHOLE SNAPSHOT HYPOTHESIS, not two readings of it (fs-cfg-boot.md
       stage (f); durable-disk lane E-himg).  Main used to take exactly
       [0 < nib] (userinit's namei corner) and [0 ∉ cov]
       ([BioInitAt.bio_init_at]'s premise); stage (f) needs everything
       [FsReady.fs_geom_ok] and [FirstTok.first_fsinit_pures] are built
       from, so the bundle itself comes down and [ProofMain] does the
       reading.  IT IS NOT AN IMAGE HYPOTHESIS: what a later era boots on
       is whatever the previous era committed, and that is exactly what the
       crash predicate's durable snapshot says
       ([SystemAdequacy.fs_boot_pure]).  [FsCfgBoot.v] is where the bundle
       lives (it used to be [BootShared]'s, which sits above this file). *)
    fs_boot_snap_wf dk ndisk S Pb sb nib cov ->
    (* main has no current proc, and neither does the scheduler() it tail-
       calls. *)
    p0 = zero_reg ->
    sie_cap_gpr KT0 m K false p0 -∗
    cpu_ctx_free -∗
    cpu_own 0 false p0 false ∅ -∗
    (* the SIE live-bit ghost's INVARIANT quarter, still raw: main is the only
       code that ever allocates [IntrDefs.intr_inv] (out of trapinithart's
       [stvec ↦ᵣ kernelvec]), and that is what consumes it. *)
    ghost_var sie_gname (1/4) ('b"0" : mword 1) -∗
    kernel_text -∗ kernel_data -∗ pc_is pcE -∗
    (* HART-GENERIC, and it has to be: main's boot arm calls kinit (-> freerange
       -> kfree -> acquire) and userinit, and builds [kalloc_env], all three of
       which took the hart-GENERIC panic credential.  It was strictly stronger
       and NOT derivable from the ambient one, so main had nowhere else
       to get it.  The ambient form is recovered where needed with
       a per-hart projection. *)
    (* the handover channel, and the RECIPE for the deposit it will carry:
       main applies this wand at the [started = 1] store, to the [pr] lock, the
       64 proc locks and the vdisk_lock it has just allocated. *)
    started_inv P -∗
    □ (∀ (γpr : gname) (γs : list gname) (γk : gname) (pd pav pu : mword 64)
         (root : mword 44) (pas : nat -> mword 44),
         printk_env γpr γd γv -∗
         procs_inv γs -∗
         console_caps γd -∗
         is_lock γk d_lock "virtio_disk"%string (disk_res γv pd pav pu) -∗
         disk_geom γv pd pav pu -∗
         kpt_inv root -∗
         (mword_of_int KernelSyms.kernel_pagetable : mword 64) ↦₈□
           (zero_extend' 64 (concat_vec root (zeros' 12 : mword 12))) -∗
         kmap_at tramp_vpn tramp_ppn KP_rx -∗
         ([∗ list] i ∈ seq 0 64, kmap_at (kstack_vpn i) (pas i) KP_rw) -∗
         P) -∗
    (* the boot supply *)
    main_locks_raw -∗
    main_globals_raw -∗
    (* THE IMAGE'S WRITABLE INITIALIZED GLOBALS, which [kernel_data] stopped
       claiming when it was narrowed to [rodata_end].  This is
       [BootShared.main_data_raw], spelled out rather than named because
       [BootShared] sits ABOVE this file and naming it would be a cycle; the
       two are convertible and [BootChain] frames one against the other.

       main spends the [nextpid] half immediately: it is the whole of
       [SpecAllocpid.nextpid_res], so the [newlock] on procinit's
       [lk_fresh pid_lock_addr "nextpid"] turns the pair into the
       [is_lock γp alp_pid_lock "nextpid" nextpid_res] that allocproc -- and
       hence kfork, sys_fork and userinit -- takes.  `first` is forkret's;
       main carries it and drops it. *)
    (* PINNED, not existential: forkret's branch is decided by this cell,
       so a holder of the existential cannot tell which arm it is in.
       [BootShared.main_data_raw] carries the same shape. *)
    ((mword_of_int KernelSyms.first_1 : mword 64) ↦₄ (mword_of_int 1 : mword 32)) -∗
    (∃ w : mword 32, (mword_of_int KernelSyms.nextpid : mword 64) ↦₄ w) -∗
    (* every proc slot's HART TAG, minted at adequacy
       ([RiscvAdequacy.riscv_system_adequacy]) at hart 0: main spends them in
       [SpecProcinit.procs_inv_alloc], one per proc lock.  The tag names the
       hart a RUNNING proc is running on; while the proc is not running it
       sits whole in its [p->lock] and its value is meaningless, which is why
       boot can mint them all at the same arbitrary hart. *)
    ([∗ list] i ∈ seq 0 NPROC, hart_full i (0%fin : CPU)) -∗
    ([∗ list] i ∈ seq 0 NPROC, pstate_full i UNUSED) -∗
    (* THE PROC TABLE'S COUNTED REGIME ([ProcAvail.v]), minted whole at
       [BootShared.boot_shared_alloc] and SPENT at the userinit call:
       [SpecUserinit.wp_userinit_sconf_body] takes [procs_avail (Some (S k))]
       and it is what refutes allocproc's empty-table arm, which userinit
       does not test (claude-notes/kernel-defects.md). *)
    procs_avail (Some NPROC) -∗
    (* ---- THE FILE SYSTEM'S BOOT-ERA MINT (fs-cfg-boot.md stage (e)) ----
       [FsCfgBoot.fs_cfg_alloc] runs inside [BootShared.boot_shared_alloc]
       and gives [IcacheRef.icfg] / [FsCfg.fscfg] their VALUES; this row is
       its whole output -- ten configuration ties plus the two boot kits --
       threaded here unopened.  Main spends kit 1 between +0x8e and +0xa2
       ([bio_init_at], [icache_boot_at], the [newlock_at]s) and carries kit 2
       to the userinit call, where stage (f) will deposit it into
       [FirstTok.first_tok]'s widened left disjunct for forkret's fsinit.

       Stated at [file_icfg]/[file_fscfg] -- the AMBIENT class's own two
       projections -- so that every row is at the instance the boot chain is
       applied at, which is the same discipline
       [BootShared.boot_shared_alloc]'s return uses. *)
    fs_boot_supply _ _ dk sb nib cov γd γv Rspent Pb
      (FsCrash.hdr_wset (FsCrash.fs_blocks dk) (FsImg.sb_logstart sb)) -∗
    (* ---- ROW (B) OF THE fsinit BUNDLE: the ERA's log-region mirror
       variable, straight out of [BootShared.boot_shared_alloc] (the era
       fupd cannot mint it -- [FsCfgBoot.fs_kit_fsinit_ghost]'s header says
       why).  It reached [boot_shared_alloc]'s postcondition already and
       dead-ended there; stage (f) threads it to main, which parks it in
       [FirstTok.first_fsinit] for initlog. ---- *)
    log_mirror_born (FsCrash.mirror_of (FsCrash.fs_blocks dk)) -∗
    (* ---- ROW (C), first half: TWO iref-slot units.  One is for
       ireclaim's iget/iput pair inside fsinit, which hands it back; the
       pair is what [SpecKexec] takes, and forkret's [if (first)] arm calls
       kexec off this same token straight after fsinit.  Split off the file
       table's share in [boot_shared_alloc]; the second half
       ([BioDefs.bslots]) is produced at WP time by [bio_init_at] and never
       crosses this boundary. ---- *)
    iref_slots 2 -∗
    (* [IrefSlots.iref_slots_auth] -- row (P4) of [fs_kit_icache]'s header.
       Minted by [IrefSlots.iref_slots_alloc] inside [boot_shared_alloc]
       beside the [irefslotG] instance, NOT by the era fupd, so it travels
       beside the kits rather than inside one.  [icache_boot_at] consumes
       it. *)
    iref_slots_auth -∗
    (* ---- ROWS 7 AND 8 OF [FirstTok.first_boot_persist] (fs-cfg-boot.md
       (f-3)): the generation certificate and the FS crash seam.  BOTH
       PERSISTENT, neither read by main's walk, both parked in the boot
       token at +0x9e.

       [gen_cert] reaches [BootShared.boot_shared_alloc]'s postcondition
       already and used to dead-end in [SystemAdequacy].
       [FsCrash.fs_crash_seam] does NOT and CANNOT: it relates the FIXED
       ghost layer's [riscv_crash_pred] field to [FsCrash.P_fs], and the
       per-era boot obligation is quantified over an arbitrary fixed layer,
       so no fupd inside an era can mint it.  It is a premise of
       [SystemAdequacy.xv6_boot_era] instead, discharged there off
       [RiscvAdequacy.riscv_power_adequacy]'s [Hcp] equation.

       SPELLED AT THE ERA'S [cov]/[sb], not at [fsc_cov]/[fsc_logst]: the
       boot chain has the era's names and [FsCfgBoot.fs_boot_supply]'s ties
       ([fsc_cov = cov], [fsc_logst = sb_logstart sb]) are what connect the
       two.  [ProofMain] holds both and does the rewrite. ---- *)
    gen_cert -∗
    FsCrash.fs_crash_seam cov (FsImg.sb_logstart sb) -∗
    (* the device fabric, which exists from time 0 (allocated in adequacy), and
       the boot hart's tokens over it *)
    dev_inv γd γv -∗
    (* the PLIC wire invariant, allocated beside [dev_inv] at adequacy and,
       like it, persistent from time 0.  main does not read it: it is one of
       the rows the first process's park captures
       ([SpecForkretParkPaid.forkret_park_pkg]), handed to userinit. *)
    wire_inv -∗
    uart_tx_own γd l0 -∗ uart_sent γd l0 -∗ uart_out_lb γd l0 -∗
    uart_dlab_is γd (DfracOwn (1/2)) b0 -∗
    disk_cfg_is γv (DfracOwn (1/2)) c0 -∗
    (* ...and the two disk ghosts the protocol invariant does NOT hold, minted
       with it at power-on ([VirtioProto.disk_ghosts_alloc]) and owed to the
       vdisk_lock's resource at main's [newlock]: the eight per-descriptor
       RECEIPTS, all at [HInactive] because nothing has ever been published,
       and the completed count is at least 0 (persistent).  Together with [main_globals_raw]'s
       [d_used_idx] / [disk_slot_raw] cells and virtio_disk_init's
       postcondition these are exactly [DiskBoot.disk_res_boot]'s inputs. *)
    ([∗ map] i ↦ st ∈ gset_to_gmap HInactive (set_seq 0 8 : gset nat),
       i ↪[dn_head γv] st) -∗
    (* ...the CLAIM MAP's authority, empty (nothing has been published)... *)
    ghost_map_auth (dn_claim γv) 1 (∅ : gmap nat dclaim) -∗
    disk_done_lb γv 0%nat -∗
    (* THE TIMER CAPABILITY, this hart's.  [timer_cap] is the sstc pin plus the
       stimecmp invariant (TimerCap.v), allocated in the boot chain out of the
       two cells timerinit wrote and the M->S bridge used to drop.  main needs
       it because it is a member of [SpecDevintr.devintr_caps], which the
       handler contract closes over -- clockintr is on kerneltrap's cone. *)
    timer_cap -∗
    main_hart_raw tlbvec0 -∗
    (* the shared kernel page table's one-shot, minted at adequacy beside the
       per-hart strans halves and spent exactly once -- by MAIN'S OWN BOOT
       ARM, in the publication assembly between kvminit and kvminithart,
       which shares the table kvminit just built as [kpt_inv].  (kvminithart
       itself is hart-generic and consumes only the persistent [kpt_inv] plus
       the root cell.)  It is GLOBAL, not per-hart, so it travels beside the
       boot bridge rather than through it. *)
    kpt_unset -∗
    (* the kernel-mapping auth, likewise a GLOBAL boot token minted at
       adequacy and spent in that same publication assembly in main's boot
       arm (it retires into [kpt_inv] with the tree, after minting the 65
       claims): the Bare translation arm no longer carries it, which is
       what makes every hart's Bare arm satisfiable at once. *)
    kmap_auth kmap_M0 -∗
    ([∗ list] p ∈ ps, page_own p) -∗
    (* ...and what the scheduler at the far end still wants, which main
       cannot build: the proc-lock names are chosen when main allocates the
       64 locks out of procinit's output, so [γs] is quantified in the
       statement inside the proof and [procs_inv] is NOT a precondition. *)
    WP (Loop : expr riscv_lang).

End SpecMain.

Module Type MAIN.
  Parameter wp_main_boot_sconf :
    forall `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fileG Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId}
      
      (m : regfile) (K : nat)
      (p0 : mword 64)
      (ps : list (mword 64)) (s1entry phystop : mword 64)
      (γd : uart_names) (γv : disk_names)
      (l0 : list (bv 8)) (b0 : bool) (c0 : virtio_cfg)
      (dk : Z -> bv 8) (sb : FsImg.fs_sb) (nib : nat) (cov : gset Z)
      (ndisk : nat)
      (S : FsState.fs_state_rec) (Pb : Z -> list (bv 8)) (Rspent : gset Z)
      (tlbvec0 : vec (option TLB_Entry) (2 ^ 6))
      (P : iProp Σ) `{!Persistent P},
      wp_main_boot_sconf_body m K p0 ps s1entry phystop
        γd γv l0 b0 c0 dk sb nib cov ndisk S Pb Rspent tlbvec0 P.
End MAIN.
