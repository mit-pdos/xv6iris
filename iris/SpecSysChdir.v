(* SpecSysChdir.v -- the public interface of sys_chdir(), stated
   independently of its proof.  Requires only the definitional layer --
   never a whole-function proof file -- so every function proof can be
   checked in parallel.

     uint64 sys_chdir(void) {
       char path[MAXPATH];
       struct inode *ip;
       struct proc *p = myproc();

       begin_op();
       if (argstr(0, path, MAXPATH) < 0 || (ip = namei(path)) == 0) {
         end_op();
         return -1;
       }
       ilock(ip);
       if (ip->type != T_DIR) { iunlockput(ip); end_op(); return -1; }
       iunlock(ip);
       iput(p->cwd);
       end_op();
       p->cwd = ip;
       return 0;
     }

   @ KernelSyms.sys_chdir, 128 bytes / 45 instructions (CodeSysChdir.v).
   A TWENTY-slot frame: ra@152, s0@144 (the frame pointer), s1@136 (the
   inode, saved only on the path that has one) and s2@128 (the proc), with
   the low sixteen slots -- sp+0 .. sp+127 -- being the [char path[128]]
   local.  [addi a1,s0,-160] / [addi a0,s0,-160] are that buffer's address.

   ==== WHAT THIS CONTRACT IS ABOUT =====================================

   sys_chdir is the SECOND writer of [p->cwd] (kexit is the first), and the
   only one that installs a reference rather than retiring one.  The whole
   contract is the accounting of that swap, and [ProcInv.proc_priv_cwd_pid]
   is the accessor it was written for: the cell and the pid quarter come out
   TOGETHER, because begin_op / namei / ilock / iput / end_op each want
   [p_pid pj |->4{dq} _] while the cwd cell has to stay out from the
   [ld a0,336(s2)] that reads the pointer iput destroys to the
   [sd s1,336(s2)] that installs the new one.

   THE REFERENCE LEDGER CLOSES AT TWO ON EVERY ARM, which is why
   [iref_slots 2] goes in and comes back out unchanged:

   * namei takes two units (its walk holds at most two references at once)
     and, on success, hands back ONE -- the second is spent against the
     reference it returns;
   * the success arm's [iput(p->cwd)] destroys the OLD working directory and
     frees that unit, so the process still owns exactly one parked unit, now
     against [ip];
   * the not-a-directory arm's [iunlockput(ip)] destroys the reference namei
     just made and frees ITS unit, and [p->cwd] never moved;
   * the two failure arms of the [||] never made a reference at all.

   So on all four arms the caller gets [iref_slots 2] back, and the
   invariant "a live process's [p->cwd] has one unit parked in the itable"
   is preserved rather than merely restored.

   ==== THE LOG LEDGER IS THE SET FORM, AND IT HAS TO BE ================

   begin_op mints [LogInv.log_op g MAXOPBLOCKS] = ten units, and end_op
   retires whatever is left, so nothing log-shaped crosses this interface.
   What DOES matter is that the ten units cover the whole body, and the
   COUNTED namei contract does not deliver that: its premise is
   [(L + 1) * iput_units <= n] and its spend is the same figure, so at a
   three-component path it would demand twelve of the ten, and even at
   L = 2 it would hand back one where the following [iput] needs three.
   The SET form ([SpecNamei.wp_namei_gen] over [LogInv.log_opS]) prices the
   walk at [SpecNamex.walk_need L <= 4] regardless of depth and spends at
   most one, which leaves nine for an [iput] that needs three.  That is the
   whole reason this proof threads [log_opS] rather than [log_op]: chdir is
   the first syscall whose path length is unbounded and whose tail still
   has to pay for an inode free.

   NO LINK RESOURCE APPEARS HERE (design/fs-icache.md 20.18 ruling 1).
   sys_chdir writes no directory record -- it reads a type field and swaps a
   pointer -- so there is no count to move and no [IcacheEscrow.dlinks]
   obligation to carry.

   ==== WHAT ITS CALLER MUST HOLD ======================================

   [eb = true] is namei's premise, inherited verbatim: the walker runs with
   the interrupt base enabled, and every acquire inside it mints its own
   pay.  The [trap_csrs_ext] / [cpu_claim_ext] complement is threaded
   anyway, uniformly with begin_op / iput / end_op, and is [emp] there.

   THE CROSSING IS THE LITERAL [true]: this function sleeps in five of its
   callees, so it may return on a hart other than the one it was called on.

   DETERMINISM: none is claimed, and none is available.  Which of the four
   arms runs is a function of the FILE SYSTEM -- whether the user string
   faults, whether the path resolves, whether what it resolves to is a
   directory -- and no caller of this contract knows any of that.  The
   postcondition is therefore the honest disjunction [SpecNamei]'s own
   two-armed result forces, keyed by the returned a0. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list functions bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import auth gmap frac.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap ghost_map.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import InstrBytes.
Require Import RegFile.
Require Import RiscvExtras.
Require Import CalleeSaved KernelText KernelDataInv.
Require Import IntrDefs.
Require Import WpNext.
Require Import WpLock.
Require Import SpecPanic.
Require Import FdSlots.
Require Import ProcGeom.
Require Export SwtchCtx.
Require Import CpuOwn.
Require Import SchedCtx.
Require Import WpUart.
Require Import DiskPtsto DiskInv.
Require Import BioInv.
Require Import FsBlocks LogInv.
Require Import FsCrash.
Require Import BitmapInv.
Require Import InodeInv.
Require Import InodeRegion.
Require Import IrefSlots.
Require Import IcacheRef.
Require Import IcacheInv.
Require Import IcacheEscrow.
Require Import KvmSpec.
Require Import FileInvDefs.
Require Import UserPtTree.
Require Import ProcPtOwn.
Require Import ProcInv.
Require Import SpecDirlink.    (* [ic_sleeplocks], [ireg_blocks_ok] *)
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import ProcAvail.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Import Defs.

Local Open Scope Z_scope.

(* sys_chdir's own frame is 160 bytes -- TWENTY slots ([c.addi16sp sp,-160]
   at +0x00), of which sixteen are the [path] buffer.  Its deepest callee is
   namei (106); iunlockput wants 64, argstr 60, iput 60, end_op 58, ilock
   44, begin_op 26, iunlock 26, myproc 10. *)
Notation K_sys_chdir := (136%nat) (only parsing).
Section SpecSysChdir.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ}.
  (* [GenId], for [ProcInv.proc_priv]'s own index: the private block now
     carries [FirstTok.first_tok], whose boot arm names [gen_cert].  The
     definitions below mention the block, so the section has to bind it. *)
  Context `{GEN : GenId}.

  (* sys_chdir's result, keyed by the returned a0.  The -1 arm gives the
     process block back at the working directory it came in with; the 0 arm
     gives it back with a NEW one, whose reference is the one namei made and
     ilock/iunlock left intact.  [ipv] is existential because the entry the
     path resolves to is not something the caller named. *)
  Definition sys_chdir_post (γf : gname) (pa : mword 64) (pid : mword 32)
      (V : pprivate) (r : mword 64) : iProp Σ :=
    (⌜r = (mword_of_int (-1) : mword 64)⌝ ∗ proc_priv γf pa pid V
     ∨ ∃ ipv : mword 64,
         ⌜r = (zero_reg : mword 64)⌝ ∗
         proc_priv γf pa pid (upd_cwd V ipv))%I.

End SpecSysChdir.

Definition wp_sys_chdir_sconf_body
    `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
      !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId}

    (γf : gname) (γa : gname)                          (* ftable, kalloc      *)
    (gs : list gname) (j : nat) (gl : gname)            (* the running process *)
    (gu : uart_names) (gd : disk_names) (gk : gname)    (* disk fabric + lock  *)
    (pd pav pu : mword 64)
    (bn : bio_names)
    (g : log_names) (gfs : fs_names) (gi : gname)
    (cn : ic_names) (gtl : gname)                       (* the icache + itable *)
    (cov : gset Z) (logstart bmapstart inodestart : Z) (nib : nat)
    (size : Z) (dev : mword 32)
    (dqb dqs : dfrac)
    (v : mword 64)                                      (* syscall argument 0  *)
    (pid : mword 32) (V : pprivate)
    (m : regfile) (K : nat) (eb : bool)
    (b : bool) (lks : gset string) :=
  let pcE : mword 64 := mword_of_int KernelSyms.sys_chdir in
  let pj := proc_addr j in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  (K_sys_chdir <= K)%nat ->
  (* ---- the icache's ambient ties, threaded verbatim to namei ---- *)
  dev = icfg_dev ->
  nib = icfg_nib ->
  g = icfg_log ->
  inodestart = icfg_ist ->
  dev = ROOTDEV ->
  (0 < nib)%nat ->
  (* ---- the block-layer geometry, threaded verbatim to namei / iput ---- *)
  log_geom_ok cov logstart ->
  0 < size <= BPB ->
  0 <= bmapstart ->
  bmapstart ∈ cov ->
  ~ (bmapstart ∈ log_region_set logstart) ->
  0 <= inodestart ->
  cov_below cov size ->
  ireg_blocks_ok inodestart nib cov logstart ->
  (j < NPROC)%nat ->
  gs !! j = Some gl ->
  (* namei's own premise, inherited: the walker runs with the base enabled *)
  eb = true ->
  (* argstr reads syscall argument 0 out of the trapframe page [proc_priv]
     carries *)
  pv_tf V !! tf_arg_idx 0 = Some v ->
  sie_cap_gpr KT1 m K b pj -∗
  (* ENTERED WITH NO LOCK HELD, and that is why there is no [locks_below]
     premise here where sys_close has one: the depth is pinned at ZERO, so
     [CpuOwn.cpu_own_zero_empty] DERIVES [lks = ∅] and every order goal the
     nine callees raise -- begin_op / iput / iunlockput / end_op at "log",
     ilock at "bcache", iunlock at "sleep lock", argstr at "kmem" -- is
     [locks_below ∅ _].  Taking the premise anyway would push an obligation
     out into [SpecSyscall] for nothing. *)
  cpu_own 0 eb pj b lks -∗
  (* THE TRAP-CSR COMPLEMENT, THREADED.  [emp] at [eb = true] -- which this
     contract's own premise forces -- so no caller gains an obligation; it
     is threaded rather than framed because begin_op / ilock / iput /
     iunlockput / end_op each take it and each crosses at the literal
     [true].  See claude-notes/completed/eb-generic-sweep.md. *)
  trap_csrs_ext KT1 eb -∗
  cpu_claim_ext eb pj -∗
  kernel_text -∗ kernel_data -∗ pc_is pcE -∗
  panic_env -∗
  (* ---- the block layer ---- *)
  bio_ctx bn (fs_view gfs gd dev cov) -∗
  log_ctx g bn gfs cov logstart dev -∗
  fs_crash_seam cov logstart -∗
  gen_cert -∗
  dev_inv gu gd -∗
  disk_geom gd pd pav pu -∗
  is_lock gk d_lock "virtio_disk"%string (disk_res gd pd pav pu) -∗
  bslots 3 -∗
  (* ---- the inode cache, and the region iput's truncate arm frees into ---- *)
  is_itable2 gtl cn gfs gi cov logstart nib dev -∗
  itable_inv -∗
  ic_escrows cn gfs gi cov logstart -∗
  ic_sleeplocks cn -∗
  ireg_inv gi gfs inodestart nib -∗
  (* ...AND THE SEALED REGIME (iclaim-ledger.md §3.2, RULING B; §6′ RULING G).
     Persistent, borrowed and never spent; it rides the SAME channel
     [ireg_inv] does.  It is here because this contract reaches iput, whose
     free path FREEZES the inode, and §2.3's boot-shelter clause makes a
     freezer exhibit the regime it freezes under.  A runtime caller hands
     [SpecIput] the LEFT arm of its borrowed disjunction and discards what
     comes back; only ireclaim, which freezes before the seal is fired,
     lends [ireg_boot] instead. *)
  ireg_open -∗
  sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
  sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
  bitmap_inv gfs bmapstart cov logstart size -∗
  (* argstr's page-table side, and namei's (iget's ipool arm allocates) *)
  kalloc_env γa None -∗
  (* the running-thread bundle *)
  procs_inv gs -∗
  (* ---- the process, and the reference allowance its walk needs ---- *)
  iref_slots 2 -∗
  proc_priv γf pj pid V -∗
  (* THE CROSSING IS THE LITERAL [true], NOT [b]: sys_chdir sleeps (begin_op,
     namei, ilock, iput and end_op all park), so it can return on another
     hart whatever SIE was doing.  Vacuous at [true], so consuming it costs
     the caller nothing. *)
  wp_next true pj (fun (CID : CpuId) =>
  ∀ (mf : regfile) (P' : uptd),
      ⌜callee_saved m mf⌝ -∗
      (* the page table may have GROWN: argstr's fetchstr faults user pages
         in.  [uptd_ext] is argstr's own report, relayed. *)
      ⌜uptd_ext (pv_upt V) P'⌝ -∗
      sie_cap_gpr KT1 mf K b pj -∗
      cpu_own 0 eb pj b lks -∗
      trap_csrs_ext KT1 eb -∗
      cpu_claim_ext eb pj -∗
      pc_is ret_tgt -∗
      bslots 3 -∗
      sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
      sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
      (* the free pool only SHRINKS -- iput's truncate arm is the only mover *)
      (* the allowance, whole: see the header's ledger *)
      iref_slots 2 -∗
      sys_chdir_post γf pj pid (upd_upt V P')
        (mf !!! Regidx (mword_of_int 10 : mword 5)) -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type SYSCHDIR.
  Parameter wp_sys_chdir_sconf :
    forall `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ, !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId}
      (γf : gname) (γa : gname)
      (gs : list gname) (j : nat) (gl : gname)
      (gu : uart_names) (gd : disk_names) (gk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names)
      (g : log_names) (gfs : fs_names) (gi : gname)
      (cn : ic_names) (gtl : gname)
      (cov : gset Z) (logstart bmapstart inodestart : Z) (nib : nat)
      (size : Z) (dev : mword 32)
      (dqb dqs : dfrac)
      (v : mword 64)
      (pid : mword 32) (V : pprivate)
      (m : regfile) (K : nat) (eb : bool)
      (b : bool) (lks : gset string),
      wp_sys_chdir_sconf_body γf γa gs j gl gu gd gk pd pav pu bn g gfs gi
                              cn gtl cov logstart bmapstart inodestart nib
                              size dev dqb dqs v pid V m K eb b lks.
End SYSCHDIR.
