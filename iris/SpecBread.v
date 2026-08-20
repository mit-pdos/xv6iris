(* SpecBread.v -- the public interface of bread, stated independently of its
   proof.  Requires only the definitional layer -- never a whole-function
   proof file -- so every function proof can be checked in parallel.

     struct buf *bread(uint dev, uint blockno) {
       struct buf *b = bget(dev, blockno);   // INLINED: both scan loops
       if (!b->valid) { virtio_disk_rw(b, 0); b->valid = 1; }
       return b;
     }

   bget is static with bread its only caller, so gcc inlined it: bread's
   body contains the forward hit scan, the backward LRU recycle scan, the
   "bget: no buffers" panic, and both refcnt++/field-rewrite critical
   sections (see claude-notes/projects/bio.md for the instruction map).

   The contract (claude-notes/design/fs-log.md): one [bslot] in, a
   [bio_locked] handle out -- the buffer's sleeplock held, valid = 1,
   disk = 0, dev/blockno pinned to the request, and the data bytes EQUAL
   TO THE BLOCK'S LOGICAL CONTENT (the client payload [bv_clean]/[bv_dirty]
   inside the handle indexes the same bytes).  No [disk_block] crosses the
   interface: the covered range's disk fragments live INSIDE the bio layer
   (pool / escrow / handles), which is also what makes two concurrent
   breads of the same block specifiable -- both get served off the one
   interior fragment.

   The requested block must be covered by the client view and on the
   view's device; a caller that knows the block's logical content (its own
   [fsblock] half against the handle's payload half) learns the returned
   bytes by agreement -- the bio layer hands the payload out opaquely.

   The function sleeps (acquiresleep; rw's two sleeps), so it threads the
   full running-process bundle; it enters and returns at noff 0. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import InstrBytes.
Require Import RegFile.
Require Import RiscvExtras.
Require Import CalleeSaved KernelText.
Require Import IntrDefs.
Require Import WpNext.
Require Import WpLock.
Require Import KernelDataInv.
Require Import SpecPanic.
Require Import FdSlots.
Require Import ProcGeom.
Require Export SwtchCtx.
Require Import CpuOwn.
Require Import SchedCtx.
Require Import WpUart.
Require Import DiskPtsto DiskInv.
Require Import BcacheInv BioInv.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import ProcAvail.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Import Defs.

(* bread's own frame is 48 bytes (6 slots); its deepest callee is
   virtio_disk_rw (34). *)
Notation K_bread := (58%nat) (only parsing).
Definition wp_bread_sconf_body
    `{!riscvGS Σ, !xv6G Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId}
    
    (γs : list gname) (j : nat) (γl : gname)          (* the running process *)
    (γu : uart_names) (γd : disk_names) (γk : gname)  (* disk fabric + lock  *)
    (pd pav pu : mword 64)
    (bn : bio_names) (V : bio_view Σ)
    (pidv dev bno : mword 32) (dq : dfrac)
    (m : regfile) (K : nat) (eb : bool)
    (b : bool) (lks : gset string) :=
  let pcE : mword 64 := mword_of_int KernelSyms.bread in
  let pj := proc_addr j in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  (K_bread <= K)%nat ->
  (* rw's honest arithmetic premise: sector = blockno * 2 in 32 bits *)
  (uint bno < 2147483648)%Z ->
  (* the request is inside the client view: a covered block on ITS device
     (the interior fragments and the cached-blockno injectivity are keyed
     on exactly this) *)
  bv_gd V = γd ->
  uint bno ∈ bv_cov V ->
  dev = bv_dev V ->
  (j < NPROC)%nat ->
  γs !! j = Some γl ->
  (* the two uint arguments arrive sign-extended (RV64 ABI); the scan's
     64-bit compares against the sign-extending [lw]s are then exact *)
  m !!! Regidx (mword_of_int 10 : mword 5) = sign_extend' 64 dev ->
  m !!! Regidx (mword_of_int 11 : mword 5) = sign_extend' 64 bno ->
  (* bread directly acquires "bcache" (rank 4, via the inlined bget) and its
     own acquiresleep call needs "sleep lock" (rank 6, LockRank.v); the bound
     is stated at the LOWER rank -- [locks_below_mono] (4 <= 6) lifts it to
     cover the acquiresleep call too, so one premise suffices for both. *)
  locks_below lks "bcache" ->
  sie_cap_gpr KT1 m K b pj -∗
  (* enters at noff 0; the acquires raise it to what sleep demands *)
  cpu_own 0 eb pj b lks -∗
  (* THE TRAP-CSR COMPLEMENT, NOT THE BARE PAIR.  This function acquires at
     level 0 and releases before returning, so it is push/pop-BALANCED: its
     own [acquire] mints [arm_pay 0 eb _], and at [eb = true] that IS the
     pair ([trap_csrs] ∗ [cpu_claim]) its interior sleepers (acquiresleep;
     rw's two sleeps) need, spent back by its own [release] before either
     runs.  A caller-held level-0 pay would be a SECOND one, and a second
     one is UNIMPLEMENTABLE above a park -- sleep carries exactly the one
     the pushing acquire minted, so stating the bare pair here would want
     [trap_csrs] at the parking hart AND at the resuming one (and at
     [eb = true] two of them at one hart are outright contradictory).  The
     [_ext] COMPLEMENT is exactly the resource that avoids this: at
     [eb = true] it is [emp], so nothing changes for any existing caller
     (the acquire already supplies what the interior sleepers need); at
     [eb = false] the acquire's push_off mints nothing, so the pair the
     sleepers need can only come from here, and the caller holds it because
     the TRAP handed it over.  See claude-notes/completed/sched-hart-generic.md
     and claude-notes/completed/eb-generic-sweep.md. *)
  trap_csrs_ext KT1 eb -∗
  cpu_claim_ext eb pj -∗
  kernel_text -∗ kernel_data -∗ pc_is pcE -∗
  panic_env -∗
  bio_ctx bn V -∗
  (* the caller's own pid cell (acquiresleep records it in the lock) *)
  p_pid pj ↦₄{dq} pidv -∗
  (* the running-thread bundle threaded through acquiresleep and rw *)
  procs_inv γs -∗
  (* the disk fabric *)
  dev_inv γu γd -∗
  disk_geom γd pd pav pu -∗
  is_lock γk d_lock "virtio_disk"%string (disk_res γd pd pav pu) -∗
  (* the slot unit backing the new reference *)
  bslot bn -∗
  (* THE CROSSING IS THE LITERAL [true], NOT [b].  This function PARKS (its
     acquiresleep sleeps), and a park moves the hart with interrupts off, so
     the crossing has nothing to do with SIE -- the porting guide's "a
     PARKING function's [wp_next] index is [true] UNCONDITIONALLY".  While
     the contract was pinned at [b = true] the two spellings coincided; at
     [b = false] the [b] form would claim the function returns on the hart
     that called it, which is false. *)
  wp_next true pj (fun (CID : CpuId) =>
  ∀ (mf : regfile) (k : nat) (bs bsd : list (bv 8)) (d : bool),
      ⌜callee_saved m mf
       /\ mf !!! Regidx (mword_of_int 10 : mword 5) = bnode k⌝ -∗
      sie_cap_gpr KT1 mf K b pj -∗
      cpu_own 0 eb pj b lks -∗
      trap_csrs_ext KT1 eb -∗
      cpu_claim_ext eb pj -∗
      pc_is ret_tgt -∗
      p_pid pj ↦₄{dq} pidv -∗
      (* the locked buffer, keyed to the request: its bytes ARE the
         block's logical content (the payload inside indexes them) *)
      bio_locked bn V k pidv dev bno bs bsd d -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type BREAD.
  Parameter wp_bread_sconf :
    forall `{!riscvGS Σ, !xv6G Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId}
      
      (γs : list gname) (j : nat) (γl : gname)
      (γu : uart_names) (γd : disk_names) (γk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names) (V : bio_view Σ)
      (pidv dev bno : mword 32) (dq : dfrac)
      (m : regfile) (K : nat) (eb : bool)
      (b : bool) (lks : gset string),
      wp_bread_sconf_body γs j γl γu γd γk pd pav pu bn V
                          pidv dev bno dq m K eb b lks.
End BREAD.
