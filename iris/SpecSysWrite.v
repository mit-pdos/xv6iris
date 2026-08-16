(* SpecSysWrite.v -- the public interface of sys_write(), stated
   independently of its proof.  Requires only the definitional layer and its
   callees' SPECS -- never a whole-function proof file -- so every function
   proof can be checked in parallel.

     uint64 sys_write(void) {
       struct file *f;
       int n;
       uint64 p;
       argaddr(1, &p);
       argint(2, &n);
       if (argfd(0, 0, &f) < 0) return -1;
       return filewrite(f, p, n);
     }

   @ KernelSyms.sys_write, 72 bytes / 25 instructions.  THE OBJECT CODE IS
   SYS_READ'S, INSTRUCTION FOR INSTRUCTION -- same 48-byte frame, same slot
   assignment ([f] slot 3, the [int n] the UPPER WORD of slot 4, [p] slot 5,
   slot 6 unused), same registers, same offsets, same hoisted [c.li a0,-1]
   above the branch.  Only the three [jal] targets differ, and only the third
   differs in kind: filewrite instead of fileread.  SpecSysRead.v carries the
   listing; CodeSysWrite.v carries this one's.

   ==== THE ONE PLACE THE WRITE SIDE IS BETTER OFF ======================

   sys_write does NOT carry fileread's [MAXFILE*BSIZE + n < 2^31].  That is
   not an oversight and not a weaker statement: filewrite CHUNKS its writes
   at [max = ((MAXOPBLOCKS-1-1-2)/2)*BSIZE = 3072] bytes, so writei's joint
   numeric premise is a CLOSED fact inside filewrite's own proof
   ([SpecFilewrite]'s [fw_chunk_joint]: [n1 <= 3072] by construction and
   [off <= MAXFILE*BSIZE] by [FileOff.off_wf]) rather than something passed
   up.  fs-sysfile S3f banked exactly this: sys_write may take [n] straight
   from user input where sys_read cannot.

   WHAT IT DOES STILL CARRY is [0 <= n].  [SpecFilewrite] takes
   [0 <= n < 2^31], the upper half of which is free for a sign-extended
   32-bit cell ([SpecSysRead.sys_rw_count_lt]) and the lower half of which is
   not: nothing between argint and the call tests the sign, and the object
   code confirms it (the function's only branch is argfd's).  A negative [n]
   is perfectly well handled by the C -- filewrite's loop body never runs and
   its tail [(i == n ? n : -1)] answers -1 -- so this is a MODELLING premise
   rather than a kernel fact, and it is shared verbatim with sys_read.  See
   SpecSysRead.v's header for the full accounting of what each of the two
   syscalls owes.

   ==== THE REST OF THE SHAPE ============================================

   [pfd] is NULL, so argfd's [SpecArgfd.ofd_out] costs this caller nothing,
   and the error return is hoisted above the branch so both arms reach one
   epilogue with the answer already in a0.

   ==== THE ENVIRONMENT IS OWNED, NOT OPENED (fs-sysfile S4c) ============

   S4 froze this contract with an OPENER wand, because [filewrite_env] was
   indexed by the file's CONTENT and by its fd SLOT.  S4' overturned that,
   and for a reason stronger than taste: the opener promised back a
   [file_ref gf k q' Cf] at a SMALLER fraction, and no such thing exists --
   [FileInvDefs.fref_tok]'s reference COUNT rides in the same map entry as
   the fraction.  SpecSysFstat.v's and SpecSysRead.v's headers have the full
   account.

   What this contract takes instead is [filewrite_fs_env gf fn], which names
   neither the content nor the slot, plus the device table's WRITE column
   [filewrite_devsw fn] (whose cell address is a function of the major, so it
   is the one thing that could not be made content-independent by restating
   it -- see SpecSysRead.v).  Everything per-inode that the old environment
   asked for -- the itable slot, the inum, the device, the region bound, the
   share, its GENERATION and the fd's recorded TYPE -- comes out of the
   reference itself, and filewrite carves it
   ([SpecFileread.fileread_pay_carve], the read side's carve grown by the
   [ty] output precisely so filewrite's [ity_shot] comes from the same
   place).  The [fwn_j] / [fwn_procs] equations the opener used to promise
   are now ordinary premises of this contract, where they belong. *)
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
Require Import SmodeCore.
Require Import CalleeSaved KernelText KernelDataInv.
Require Import IntrDefs.
Require Import WpNext.
Require Import WpLock.
Require Import PanicStub.
Require Import SpecPanic.
Require Import FdSlots.
Require Import ProcGeom.
Require Export SwtchCtx.
Require Import CpuOwn.
Require Import SchedCtx.
Require Import WpUart.
Require Import DiskPtsto.
Require Import BioDefs.
Require Import FsBlocks LogInv.
Require Import FsCrash.
Require Import InodeRegion.
Require Import IrefSlots.
Require Import KallocInv.
Require Import UserPtTree.
Require Import KvmSpec.
Require Import ProcPtOwn.
Require Import ProcInv.
Require Import FileInvDefs.
Require Import SpecArgfd.
Require Import SpecSysRead.
Require Import SpecFilewrite.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import ProcAvail.
Import Defs.

Local Open Scope Z_scope.

(* sys_write's own frame is 6 slots ([c.addi16sp sp,sp,-48]); below it
   filewrite wants [filewrite_stack] = 82, which dominates argfd's 24 and
   argint's / argaddr's 18. *)
Notation sys_write_stack := ((6 + filewrite_stack)%nat) (only parsing).
(* WHAT SYS_WRITE RETURNS.  Indexed by [arg_fd], not by [r]: filewrite's own
   -1 (not writable / a short write / a bad device major) is not
   distinguishable from argfd's by the value. *)
Definition sys_write_ret (V : pprivate) (v : mword 64) (n : Z) (r : mword 64) : Prop :=
  (r = (mword_of_int (-1) : mword 64) /\ arg_fd v (pv_ofile V) = None)
  \/ (exists (fd : nat) (fv : mword 64),
        arg_fd v (pv_ofile V) = Some (fd, fv) /\ filewrite_ret n r).

Section SpecSysWrite.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !kallocG Σ,
            !bioG Σ, !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ,
            !fsCrashG Σ, !irefslotG Σ, !pavG Σ, !iregG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  (* THE ENVIRONMENT FILEWRITE'S [if] ACTUALLY ASKS FOR, out of the two
     content-independent bundles this contract owns.
     [SpecSysRead.read_env_frame]'s twin, and the whole of what the S4 opener
     was trying to be.  The [used'] the exclusive half comes back at is
     whatever filewrite reached -- the number of ballocs is not a function of
     anything the caller holds -- which is why it is a binder of the wand and
     not of the frame. *)
  Lemma write_env_frame (γf : gname) (fn : fwrite_names) (Cf : fcontent) :
    filewrite_fs_env γf fn -∗ filewrite_devsw fn -∗
    filewrite_env γf fn Cf ∗
    (∀ used' : gset Z, filewrite_env_out fn Cf used' -∗
       ∃ used'' : gset Z,
         filewrite_fs_out fn used'' ∗ filewrite_devsw fn).
  Proof.
    iIntros "Hfs Hdev". rewrite /filewrite_env /filewrite_env_out.
    (* THE SET IS EXISTENTIAL ON THE WAY OUT, and it has to be: on the three
       arms that do not reach the allocator [filewrite_env_out] is [emp] or a
       device cell, from which NO constraint on the caller's [used'] follows
       -- so the only sound answer there is the set nothing touched.  The
       syscall picks the witness and hands it to its own continuation, which
       is why [wp_sys_write_sconf_body]'s [used'] is a ∀-binder of the
       continuation rather than a parameter of the contract. *)
    case_bool_decide.
    { iSplitR; [done|]. iIntros (used') "_". iExists (fwn_used fn).
      iDestruct (filewrite_fs_env_out with "Hfs") as "Hout".
      iSplitL "Hout"; [iExact "Hout" | iFrame "Hdev"]. }
    case_bool_decide.
    { iDestruct (filewrite_devsw_acc fn Cf with "Hdev") as "[Hone Hback]".
      iSplitL "Hone"; [iExact "Hone"|].
      iIntros (used') "Hout". iExists (fwn_used fn).
      iDestruct ("Hback" with "Hout") as "Hdev".
      iDestruct (filewrite_fs_env_out with "Hfs") as "Hfo".
      iSplitL "Hfo"; [iExact "Hfo" | iFrame "Hdev"]. }
    case_bool_decide.
    { iSplitL "Hfs"; [iExact "Hfs"|]. iIntros (used') "Hout".
      iExists used'. iSplitL "Hout"; [iExact "Hout" | iFrame "Hdev"]. }
    { iSplitR; [done|]. iIntros (used') "_". iExists (fwn_used fn).
      iDestruct (filewrite_fs_env_out with "Hfs") as "Hout".
      iSplitL "Hout"; [iExact "Hout" | iFrame "Hdev"]. }
  Qed.

End SpecSysWrite.

Definition wp_sys_write_sconf_body
    `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !kallocG Σ,
      !bioG Σ, !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ,
      !fsCrashG Σ, !irefslotG Σ, !pavG Σ, !iregG Σ}
    `{GEN : GenId} `{CID : CpuId}

    (γa : gname) (γf : gname)                    (* kalloc, the file table  *)
    (γs : list gname) (j : nat) (γlp : gname)    (* the running process     *)
    (fn : fwrite_names)                          (* the file system's ghosts *)
    (pidv : mword 32) (V : pprivate)
    (v v2 : mword 64)                            (* syscall arguments 0, 2  *)
    (m : regfile) (av : nat) (eb : bool) (b : bool) (lks : gset string) :=
  let pcE : mword 64 := mword_of_int KernelSyms.sys_write in
  let pj := proc_addr j in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  (sys_write_stack <= av)%nat ->
  (j < NPROC)%nat ->
  γs !! j = Some γlp ->
  length γs = NPROC ->
  (* filewrite's contract takes these as EQUATIONS rather than deriving them;
     they used to be promised by the opener and are ordinary premises now *)
  fwn_j fn = j ->
  fwn_procs fn = γs ->
  (* the three syscall arguments; argument 1 (the user source) is fetched
     but never inspected here *)
  pv_tf V !! tf_arg_idx 0 = Some v ->
  (exists v1 : mword 64, pv_tf V !! tf_arg_idx 1 = Some v1) ->
  pv_tf V !! tf_arg_idx 2 = Some v2 ->
  (* THE ONE INHERITED NUMERIC PREMISE (see the header).  Note what is NOT
     here: fileread's [MAXFILE*BSIZE + n < 2^31].  The upper half of
     filewrite's [0 <= n < 2^31] is free ([SpecSysRead.sys_rw_count_lt]). *)
  0 <= sys_rw_count v2 ->
  (* PARKING PREMISE (hart-generic scheduler protocol): every filewrite arm
     sleeps, so this syscall parks. *)
  eb = true ->
  sie_cap_gpr m av b pj -∗
  (* a syscall runs at push_off level 0 *)
  cpu_own 0%nat eb pj b lks -∗
  kernel_text -∗ kernel_data -∗ pc_is pcE -∗
  (* filewrite's default arm is [panic("filewrite")], and its callees panic
     too; this is theirs *)
  panic_wp_any -∗
  (* ...and that arm calls panic as an ORDINARY call: [kernel_data] above
     mints the literal, and this is the console bundle printk needs. *)
  panic_env -∗
  proc_priv γf pj pidv V -∗
  kalloc_env γa None -∗
  procs_inv γs -∗
  (* ...and the file system in the form that does NOT name a file, plus the
     device table's write column for whatever major the descriptor may name *)
  filewrite_fs_env γf fn -∗
  filewrite_devsw fn -∗
  (* THE CROSSING IS THE LITERAL [true]: filewrite parks. *)
  wp_next true pj (fun (CID : CpuId) =>
    ∀ (mf : regfile) (r : mword 64) (P' : uptd) (used' : gset Z),
      ⌜callee_saved m mf⌝ -∗
      ⌜uptd_ext (pv_upt V) P'⌝ -∗
      ⌜sys_write_ret V v (sys_rw_count v2) r⌝ -∗
      ⌜mf !!! Regidx (mword_of_int 10 : mword 5) = r⌝ -∗
      sie_cap_gpr mf av b pj -∗
      cpu_own 0%nat eb pj b lks -∗
      pc_is ret_tgt -∗
      proc_priv γf pj pidv (upd_upt V P') -∗
      kalloc_env γa None -∗
      (* the file system, back, at a bitmap set that only GREW *)
      filewrite_fs_out fn used' -∗
      filewrite_devsw fn -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type SYSWRITE.
  Parameter wp_sys_write_sconf :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !kallocG Σ,
             !bioG Σ, !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ,
             !fsCrashG Σ, !irefslotG Σ, !pavG Σ, !iregG Σ}
      `{GEN : GenId} `{CID : CpuId}

      (γa : gname) (γf : gname)
      (γs : list gname) (j : nat) (γlp : gname)
      (fn : fwrite_names)
      (pidv : mword 32) (V : pprivate)
      (v v2 : mword 64)
      (m : regfile) (av : nat) (eb : bool) (b : bool) (lks : gset string),
      wp_sys_write_sconf_body γa γf γs j γlp fn pidv V v v2 m av eb b lks.
End SYSWRITE.
