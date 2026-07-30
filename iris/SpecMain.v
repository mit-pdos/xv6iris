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
   secondary-hart contract is not statable yet, but the KERNEL PAGE TABLE is no
   longer what blocks it: kvminithart now publishes the table as the shared
   invariant [KptShare.kpt_inv] and every hart's Sv39 translation runs on the
   per-hart residue [tlb_res_pt], so the table itself is shareable and rides to
   the secondaries in [P] below.  What still has to move (claude-notes/
   projects/main-boot.md G5): [SRegime.bare_inv] carries the globally unique
   [kmap_auth kmap_M0] -- it is the refutation that makes Bare-arm claim
   honoring provable, so at most ONE hart can ever be in its Bare arm, and
   every secondary spends its whole pre-switch phase there.
   [SchedCtx.procs_inv] is no longer an obstacle: since proc contexts became
   MIGRATABLE (claude-notes/projects/sched-hart-generic.md) it mentions
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
   -- SpecPrintkGen.v), [γs] when it allocates the 64 proc locks out of
   procinit's ([SpecProcinit.procs_inv_alloc]), and [γk] when it allocates the
   vdisk_lock over [DiskInv.disk_res] out of virtio_disk_init's
   ([DiskBoot.disk_res_boot]) -- the disk's PAGES (its configuration identity)
   are chosen by kalloc inside virtio_disk_init, so [pd pav pu] are quantified
   here too, and the persistent [DiskInv.disk_geom] that names them travels
   alongside the lock.

   ... and, out of kvminithart's post, THE KERNEL PAGE TABLE: the shared
   invariant [KptShare.kpt_inv root], the root cell main PERSISTS after
   kvminit wrote it ([kernel_pagetable ↦₈□ root_b]), and the 65 mapping
   claims the switch minted (trampoline + the 64 kernel stacks).  The root
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
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap ghost_map.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes.
Require Import RiscvLang RiscvPtsto.
Require Import RegFile InstrBytes.
Require Import SmodeCore.
Require Import KernelText KernelDataInv.
Require Import IntrDefs.
(* the shared kernel page table: [kpt_unset] is a boot token, [kpt_inv] and
   the 65 claims are what the deposit wand carries to the secondaries *)
Require Import KptGhost KptShare KptExecMap KvmMap.
Require Import KMap.
Require Import SpecPanic.
Require Import StartedInv.
(* the callees, for the vocabulary main's precondition is stated in *)
Require Import SpecConsoleinit.
Require Import SpecProcinit.
Require Import SpecIinit SpecVirtioDiskInit.
Require Import SpecFreerange SpecPrintkGen.
Require Import ProcGeom FdSlots CpuOwn SchedCtx.
Require Import KallocInv KvmSpec BcacheInv SleepLock.
Require Import VirtioModel DiskPtsto WpUart.
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
Require Import WpLock FileInv.
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
  (* PLUS three groups that no callee's precondition names but a caller-  *)
  (* side ASSEMBLY does, and which therefore have nowhere else to come    *)
  (* from:                                                               *)
  (*  - [panicking] / [panicked], the two flag cells                       *)
  (*    [SpecPrintkGen.printk_flags_inv] is an [inv] over.  main allocates *)
  (*    that invariant before its first printk call, so it must own the    *)
  (*    cells; contents-existential, since the invariant asserts nothing   *)
  (*    about either value.                                               *)
  (*  - per process, the two PUBLIC cells procinit never touches:          *)
  (*    [p_chan] and [SchedCtx.proc_pub] (killed / xstate / the           *)
  (*    invariant's permanent HALF of the pid cell -- [proc_raw] carries   *)
  (*    the other half).  [SpecProcinit.procs_inv_alloc] consumes exactly  *)
  (*    [proc_ready i] plus these two, so they are main's to supply.       *)
  (*  - [initproc], the one global userinit writes.                        *)
  (* ------------------------------------------------------------------- *)
  Definition main_globals_raw : iProp Σ :=
    ((∃ r w : mword 64,
        devsw_console_read ↦₈ r ∗ devsw_console_write ↦₈ w) ∗
     (∃ pv pkv : mword 32,
        (mword_of_int KernelSyms.panicking : mword 64) ↦₄ pv ∗
        (mword_of_int KernelSyms.panicked : mword 64) ↦₄ pkv) ∗
     (mword_of_int (KernelSyms.kmem + 24) : mword 64) ↦₈ (mword_of_int 0 : mword 64) ∗
     (* the kernel page-table root: RAW here (kvminit writes it), and
        PERSISTED by main once kvminithart has installed it -- the ↦₈□ form
        is what the deposit wand hands the secondaries *)
     (∃ kpt0 : mword 64,
        (mword_of_int KernelSyms.kernel_pagetable : mword 64) ↦₈ kpt0) ∗
     ([∗ list] i ∈ seq 0 NPROC, proc_raw (proc_addr i)) ∗
     ([∗ list] i ∈ seq 0 NPROC,
        (∃ ch : mword 64, p_chan (proc_addr i) ↦₈ ch) ∗
        proc_pub (proc_addr i)) ∗
     fd_slots (NPROC * (NOFILE + FDSPARE)) ∗
     (∃ v0 : mword 64, (mword_of_int KernelSyms.initproc : mword 64) ↦₈ v0) ∗
     ([∗ list] k ∈ seq 0 NBUF, sl_raw (buf_lock (bnode k))) ∗
     ([∗ list] k ∈ seq 0 NBUF, blink_raw (bnode k)) ∗
     blink_raw bhead ∗
     ([∗ list] i ∈ seq 0 NINODE, sl_raw (inode_lock i)) ∗
     (∃ pd pav pu : mword 64,
        disk_desc ↦₈ pd ∗ disk_avail ↦₈ pav ∗ disk_used ↦₈ pu) ∗
     (∃ free0 : nat -> bv 8,
        [∗ list] j ∈ seq 0 8, (pa_add disk_free j) ↦ₘ free0 j) ∗
     d_used_idx ↦₂ wrap16 0%nat ∗
     ([∗ list] i ∈ seq 0 8, disk_slot_raw i))%I.

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
      (p0 : mword 64)
      (ps : list (mword 64)) (s1entry phystop : mword 64)
      (γd : uart_names) (γv : disk_names)
      (l0 : list (bv 8)) (b0 : bool) (c0 : virtio_cfg)
      (tlbvec0 : vec (option TLB_Entry) (2 ^ 6))
      (P : iProp Σ) `{!Persistent P} :=
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
    (* the disk's protocol is in its not-live arm at boot: virtio_disk_init
       makes it live, and its config half [c0] is how main knows so *)
    virtio_live c0 = false ->
    sie_cap_gpr γ m K -∗
    cpu_own γ 0 false p0 cpu_ctx_free -∗
    (* the SIE live-bit ghost's INVARIANT quarter, still raw: main is the only
       code that ever allocates [IntrDefs.intr_inv] (out of trapinithart's
       [stvec ↦ᵣ kernelvec]), and that is what consumes it. *)
    ghost_var γ (1/4) ('b"0" : mword 1) -∗
    kernel_text -∗ kernel_data -∗ pc_is pcE -∗
    panic_wp -∗
    (* the handover channel, and the RECIPE for the deposit it will carry:
       main applies this wand at the [started = 1] store, to the [pr] lock, the
       64 proc locks and the vdisk_lock it has just allocated. *)
    started_inv P -∗
    □ (∀ (γpr : gname) (γs : list gname) (γk : gname) (pd pav pu : mword 64)
         (root : mword 44) (pas : nat -> mword 44),
         printk_env γpr γd γv -∗
         procs_inv Φ γs -∗
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
    (* the device fabric, which exists from time 0 (allocated in adequacy), and
       the boot hart's tokens over it *)
    dev_inv γd γv -∗
    uart_tx_own γd l0 -∗ uart_sent γd l0 -∗ uart_out_lb γd l0 -∗
    uart_dlab_is γd (DfracOwn (1/2)) b0 -∗
    disk_cfg_is γv (DfracOwn (1/2)) c0 -∗
    (* ...and the two disk ghosts the protocol invariant does NOT hold, minted
       with it at power-on ([VirtioProto.disk_ghosts_alloc]) and owed to the
       vdisk_lock's resource at main's [newlock]: nothing has ever been
       published (the [dn_claim] authority is at ∅) and the completed count is
       at least 0 (persistent).  Together with [main_globals_raw]'s
       [d_used_idx] / [disk_slot_raw] cells and virtio_disk_init's
       postcondition these are exactly [DiskBoot.disk_res_boot]'s inputs. *)
    ghost_map_auth (dn_claim γv) 1 (∅ : gmap nat dclaim) -∗
    disk_done_lb γv 0%nat -∗
    main_hart_raw tlbvec0 -∗
    (* the shared kernel page table's one-shot, minted at adequacy beside the
       per-hart strans halves and spent exactly once -- inside kvminithart,
       which publishes the table it just installed as [kpt_inv].  It is
       GLOBAL, not per-hart, so it travels beside the boot bridge rather
       than through it. *)
    kpt_unset -∗
    (* the kernel-mapping auth, likewise a GLOBAL boot token minted at
       adequacy and spent inside kvminithart (it retires into [kpt_inv] with
       the tree): the Bare translation arm no longer carries it, which is
       what makes every hart's Bare arm satisfiable at once. *)
    kmap_auth kmap_M0 -∗
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
      (p0 : mword 64)
      (ps : list (mword 64)) (s1entry phystop : mword 64)
      (γd : uart_names) (γv : disk_names)
      (l0 : list (bv 8)) (b0 : bool) (c0 : virtio_cfg)
      (tlbvec0 : vec (option TLB_Entry) (2 ^ 6))
      (P : iProp Σ) `{!Persistent P},
      wp_main_boot_sconf_body γ Φ m K p0 ps s1entry phystop
        γd γv l0 b0 c0 tlbvec0 P.
End MAIN.
