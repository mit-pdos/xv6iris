(* SpecSysExec.v -- the public interface of sys_exec(), stated independently
   of its proof.

     uint64 sys_exec(void) {
       char path[MAXPATH], *argv[MAXARG];
       int i;
       uint64 uargv, uarg;

       argaddr(1, &uargv);
       if (argstr(0, path, MAXPATH) < 0) return -1;
       memset(argv, 0, sizeof(argv));
       for (i = 0;; i++) {
         if (i >= NELEM(argv))                                    goto bad;
         if (fetchaddr(uargv + sizeof(uint64)*i, &uarg) < 0)       goto bad;
         if (uarg == 0) { argv[i] = 0; break; }
         if ((argv[i] = kalloc()) == 0)                            goto bad;
         if (fetchstr(uarg, argv[i], PGSIZE) < 0)                  goto bad;
       }
       int ret = kexec(path, argv);
       for (i = 0; i < NELEM(argv) && argv[i] != 0; i++) kfree(argv[i]);
       return ret;
      bad:
       for (i = 0; i < NELEM(argv) && argv[i] != 0; i++) kfree(argv[i]);
       return -1;
     }

   @ KernelSyms.sys_exec, 101 instructions / 268 bytes, a 480-byte frame.
   The LAST function of the exec cone and the last of sysfile.c.

   ---- WHAT IT IS FOR --------------------------------------------------

   sys_exec exists to MARSHAL: it turns two user words in the trapframe
   into exactly the resources [SpecKexec.wp_kexec_sconf_body] demands, and
   it is the only caller kexec has.  Read the two contracts together --
   almost every premise below is one of kexec's, paid here:

   * kexec wants the PATH as [S plen] owned bytes with [bb_cstr pfun plen].
     [argstr] copies the user string into this function's own
     [char path[MAXPATH]] and reports [fetchstr_ret], which is exactly that
     (or -1, and then kexec is never called).
   * kexec wants each ARGUMENT as a NUL-terminated string of [alen i]
     characters inside [aslen i] owned bytes with [alen i < 4096].
     [kalloc] gives a whole page and [fetchstr] fills it with [max = PGSIZE],
     so [aslen i = 4096] and [alen i < 4096] -- kexec's blocker-§7 premise,
     paid for free.
   * kexec wants the ARGV VECTOR as [S na] owned words ending in a NULL.
     That is this function's own [char *argv[MAXARG]] frame array, memset to
     zero and then filled; the [break] arm writes the terminating NULL.
   * kexec wants [na < MAXARG].  The loop tests [i != 32] on its BACK EDGE,
     so it reaches the break with [i < 32] -- see the note on the off-by-one
     below, which is why the premise is [<] and not [<=].

   ---- THE ONE THING THAT HAD TO MOVE FIRST ----------------------------

   kexec used to carry a log-budget premise, [(L+1) * iput_units +
   iput_units <= MAXOPBLOCKS], admitting only single-element paths.  sys_exec
   cannot pay it and no caller ever could: the path arrives through [argstr],
   so its contents -- and hence [L] -- are EXISTENTIAL.  The premise is gone,
   priced instead through [SpecNamei.wp_namei_gen] over [LogInv.log_opS],
   whose [SpecNamex.walk_need] is 4 whatever the depth; SpecKexec.v's header
   has the story.  Without that, this contract does not exist.

   ---- WHAT THE POSTCONDITION SAYS -------------------------------------

   [kexec_ok] VERBATIM, against the block the copy-ins left behind.  There
   is nothing sys_exec can add to it and nothing it should drop:

   * the page table may have GROWN before kexec ran -- [argstr] and each
     [fetchstr] fault user pages in -- so the block kexec is called with is
     [upd_upt V P'], and [uptd_ext (pv_upt V) P'] is what the copy-ins
     report.  (kexec's own copyouts may grow it further; that is inside
     [kexec_ok]'s success arm.)
   * on every path that does NOT reach kexec -- argstr failed, fetchaddr
     failed, kalloc returned 0, fetchstr failed, or the loop ran out of
     argv slots -- the return is -1 and the block is handed back UNCHANGED
     at [upd_upt V P'].  That is [kexec_ok]'s failure arm exactly, so those
     five paths and kexec's own eight [bad:] entries are one disjunct.
   * [na], [alen], [entry], [spv] and [szv'] are existential: they are
     functions of user memory, which no caller of this contract names.

   THE KALLOC'D PAGES DO NOT APPEAR, in the contract or in its result.
   Every page the loop allocates is freed by one of the two [kfree] loops
   before the function returns -- including on the success path, after
   kexec has copied the strings out -- so the allocator is left exactly as
   it was found and [kalloc_env] is the only thing that crosses.  That is
   also why there is no page-count premise: the loop allocates at most
   MAXARG pages and gives every one of them back.

   ---- THE OFF-BY-ONE THE C HAS, AND WHERE IT IS RULED OUT --------------

   The C tests [i >= NELEM(argv)] at the TOP of the loop body, but gcc
   compiles it as the loop's back-edge test ([bne s2,s7] at +0x8e), so the
   break at [uarg == 0] is reached with [i < 32] and the [argv[i] = 0] store
   is in range.  What is NOT in range is kexec's own [ustack[argc] = 0] at
   exactly [argc = 32], which is why kexec takes [na < MAXARG] rather than
   [na <= MAXARG] -- and this function is where that premise is discharged,
   from the same back-edge test.  claude-notes/kernel-defects.md has the
   C-level story. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list functions bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import auth gmap frac.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap ghost_map.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExtras.
Require Import InstrBytes.
Require Import RegFile.
Require Import RiscvExtras.
Require Import CalleeSaved KernelText KernelDataInv.
Require Import IntrDefs.
Require Import WpNext.
Require Import FdSlots.
Require Import ProcGeom.
Require Export SwtchCtx.
Require Import CpuOwn.
Require Import ProcAvail.
Require Import ProcInv.
Require Import WpUart.
Require Import DiskPtsto.
Require Import BioDefs.
Require Import FsBlocks LogInv.
Require Import BitmapInv.
Require Import InodeInv.
Require Import IcacheRef.
Require Import IrefSlots.
Require Import IcacheRef.
Require Import IcacheInv.
Require Import IcacheEscrow.
Require Import KvmSpec.
Require Import FileInvDefs.
Require Import UserPtTree.
Require Import ProcPtOwn.
Require Import ProcInv.
Require Import SpecIput.       (* [iput_units] *)
Require Import SpecDirlink.    (* [ic_sleeplocks], [ireg_blocks_ok] *)
Require Import SpecNamex.      (* [ROOTDEV] *)
(* [SpecKexec] for [kexec_ok] and [fs_fabric].  This contract is a CALLER of
   kexec -- its whole job is to build kexec's precondition -- so requiring
   kexec's Spec is not the cross-function reach the tree's rule warns about;
   the two are designed against each other.  It also makes this the second
   consumer of [fs_fabric], which per the promote-on-second-consumer rule
   would move it to a shared [FsFabric.v]; not done, because the second
   consumer is kexec's own caller rather than an independent stater, so
   nothing here restates the thirteen. *)
Require Import SpecKexec.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import ProcAvail.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Import Defs.

Local Open Scope Z_scope.

(* sys_exec's own frame is 480 bytes -- SIXTY slots ([c.addi16sp sp,-480] at
   +0x00) -- of which sixteen are [path[MAXPATH]] and thirty-two are
   [argv[MAXARG]].  Its deepest callee is kexec by a wide margin
   ([SpecKexec.K_kexec] = 174); argstr wants 60, fetchstr 56, fetchaddr and
   memset and kalloc and kfree less. *)
Notation K_sys_exec := (244%nat) (only parsing).
Section SpecSysExec.
  Context `{!riscvGS Σ, !xv6G Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ}.

  (* sys_exec's result, and it is [kexec_ok] verbatim: every path that never
     reaches kexec returns -1 with the block unchanged, which is that
     relation's own failure arm.  [V] here is the block AFTER the copy-ins'
     page-table growth -- the caller reads it as [upd_upt V P']. *)
  Definition sys_exec_post (γf : gname) (pa : mword 64) (pid : mword 32)
      (V : pprivate) (r : mword 64) : iProp Σ :=
    (∃ (V' : pprivate) (na : nat) (alen : nat -> nat)
       (entry spv szv' : mword 64),
       ⌜kexec_ok V V' r entry spv szv' na alen⌝ ∗
       proc_priv γf pa pid V')%I.

End SpecSysExec.

Definition wp_sys_exec_sconf_body
    `{!riscvGS Σ, !xv6G Σ, !fdslotG Σ, !fileG Σ,
      !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId}

    (γf : gname) (γa : gname)                           (* ftable, kalloc      *)
    (gs : list gname) (j : nat) (gl : gname)            (* the running process *)
    (gu : uart_names) (gd : disk_names) (gk : gname)    (* disk fabric + lock  *)
    (pd pav pu : mword 64)
    (bn : bio_names)
    (g : log_names) (gfs : fs_names) (gi : gname)
    (cn : ic_names) (gtl : gname)                       (* the icache + itable *)
    (cov : gset Z) (logstart bmapstart inodestart : Z) (nib : nat)
    (size : Z) (dev : mword 32)
    (dqb dqs : dfrac)
    (v0 v1 : mword 64)                        (* syscall arguments 0 and 1 *)
    (pid : mword 32) (V : pprivate)
    (m : regfile) (K : nat) (eb : bool)
    (b : bool) (lks : gset string) :=
  let pcE : mword 64 := mword_of_int KernelSyms.sys_exec in
  let pj := proc_addr j in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  (K_sys_exec <= K)%nat ->
  (* ---- the icache's ambient ties, threaded verbatim to kexec ---- *)
  dev = icfg_dev ->
  nib = icfg_nib ->
  g = icfg_log ->
  inodestart = icfg_ist ->
  dev = ROOTDEV ->
  (0 < nib)%nat ->
  (* ---- the block-layer geometry, threaded verbatim to kexec ---- *)
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
  (* kexec's own premise, inherited: the FS layer's contracts are callable
     only with the interrupt base enabled.  [b = true] is NOT a premise --
     at depth 0 the SIE eighth and [cpu_own]'s hart agree, so it follows
     (SpecKexec.v's note on the interrupt index). *)
  eb = true ->
  (* argaddr / argstr read syscall arguments 1 and 0 out of the trapframe
     page [proc_priv] carries *)
  pv_tf V !! tf_arg_idx 0 = Some v0 ->
  pv_tf V !! tf_arg_idx 1 = Some v1 ->
  sie_cap_gpr KT1 m K b pj -∗
  (* ENTERED WITH NO LOCK HELD: the depth is pinned at ZERO, so
     [CpuOwn.cpu_own_zero_empty] DERIVES [lks = ∅] and every order goal the
     callees raise -- kexec's whole FS cone at "log"/"bcache"/"sleep lock",
     argstr and kalloc and kfree at "kmem" -- is [locks_below ∅ _]. *)
  cpu_own 0 eb pj b lks -∗
  (* THE TRAP-CSR COMPLEMENT, THREADED.  [emp] at [eb = true], which this
     contract's own premise forces, so no caller gains an obligation. *)
  trap_csrs_ext KT1 eb -∗
  cpu_claim_ext eb pj -∗
  kernel_text -∗ kernel_data -∗ pc_is pcE -∗
  (* ---- the file system, as kexec's own bundle: thirteen persistent
         resources this function only relays ---- *)
  fs_fabric gs gu gd gk pd pav pu bn g gfs gi cn gtl
            cov logstart inodestart nib dev -∗
  sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
  sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
  bitmap_inv gfs bmapstart cov logstart size -∗
  bslots bn 3 -∗
  (* the loop's own [kalloc]s, argstr's page faults, and kexec's page-table
     builder all run in the UNCOUNTED regime *)
  kalloc_env γa None -∗
  (* ---- the process, and the reference allowance kexec's walk needs ---- *)
  iref_slots 2 -∗
  proc_priv γf pj pid V -∗
  (* THE CROSSING IS THE LITERAL [true]: this function sleeps in kexec (and
     in argstr's page faults), so it can return on another hart. *)
  wp_next true pj (fun (CID : CpuId) =>
  ∀ (mf : regfile) (P' : uptd),
      ⌜callee_saved m mf⌝ -∗
      (* the page table may have GROWN before kexec ran: argstr's and each
         fetchstr's copy-in faults user pages in.  [uptd_ext] is their own
         report, relayed. *)
      ⌜uptd_ext (pv_upt V) P'⌝ -∗
      sie_cap_gpr KT1 mf K b pj -∗
      cpu_own 0 eb pj b lks -∗
      trap_csrs_ext KT1 eb -∗
      cpu_claim_ext eb pj -∗
      pc_is ret_tgt -∗
      sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
      sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
      (* the free pool only SHRINKS -- kexec's cone is the only mover *)
      bslots bn 3 -∗
      kalloc_env γa None -∗
      (* the allowance, whole: kexec gives back what it took *)
      iref_slots 2 -∗
      sys_exec_post γf pj pid (upd_upt V P')
        (mf !!! Regidx (mword_of_int 10 : mword 5)) -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type SYSEXEC.
  Parameter wp_sys_exec_sconf :
    forall `{!riscvGS Σ, !xv6G Σ, !fdslotG Σ, !fileG Σ, !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId}
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
      (v0 v1 : mword 64)
      (pid : mword 32) (V : pprivate)
      (m : regfile) (K : nat) (eb : bool)
      (b : bool) (lks : gset string),
      wp_sys_exec_sconf_body γf γa gs j gl gu gd gk pd pav pu bn g gfs gi
                             cn gtl cov logstart bmapstart inodestart nib
                             size dev dqb dqs v0 v1 pid V m K eb b lks.
End SYSEXEC.
