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

   AND AS OF XV6_REV 31f115a IT CARRIES NOTHING ELSE EITHER.  This contract
   used to take [0 <= sys_rw_count v2], because [SpecFilewrite] wanted
   [0 <= n < 2^31].  Nothing between argint and the call tests the sign --
   the function's only branch is argfd's -- so that premise was owed to a
   caller who could never pay it, which is not a contract about a syscall.
   31f115a's [if (f->writable == 0 || n < 0)] makes it a FACT OF THE CODE:
   [SpecFilewrite] now takes the whole [int] range,
   [SpecSysRead.sys_rw_count_range] supplies it for free, and the guard
   restores [0 <= n] past the branch, so sys_write's contract says NOTHING
   about the count the user wrote.  sys_read's is now the same shape.

   ==== THE REST OF THE SHAPE ============================================

   [pfd] is NULL, so argfd's [SpecArgfd.ofd_out] costs this caller nothing,
   and the error return is hoisted above the branch so both arms reach one
   epilogue with the answer already in a0.

   ==== THE ENVIRONMENT IS OWNED, NOT OPENED (fs-sysfile S4c) ============

   S4 froze this contract with an OPENER wand, because [filewrite_env] was
   indexed by the file's CONTENT and by its fd SLOT.  S4' overturned that,
   and for a reason stronger than taste: the opener promised back a
   [file_ref gf k q'] at a SMALLER fraction, and no such thing exists --
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
Require Import RiscvLang RiscvPtsto.
Require Import InstrBytes.
Require Import RegFile.
Require Import RiscvExtras.
Require Import CalleeSaved KernelText KernelDataInv.
Require Import IntrDefs.
Require Import WpNext.
Require Import SpecPanic.
Require Import FdSlots.
Require Import ProcGeom.
Require Export SwtchCtx.
Require Import CpuOwn.
Require Import SchedCtx.
Require Import IrefSlots.
Require Import UserPtTree.
Require Import KvmSpec.
Require Import ProcPtOwn.
Require Import ProcInv.
Require Import FileInvDefs.
Require Import SpecArgfd.
Require Import SpecSysRead.
Require Import ConsoleInv.
Require Import SpecFilewrite.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import ProcAvail.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Require Import FsCfg.  (* [fscfg]: the fs configuration is AMBIENT *)
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
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ, !irefslotG Σ, !pavG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  (* THE ENVIRONMENT FILEWRITE'S [if] ACTUALLY ASKS FOR, out of the two
     content-independent bundles this contract owns.
     [SpecSysRead.read_env_frame]'s twin, and the whole of what the S4 opener
     was trying to be. *)
  Lemma write_env_frame (γf : gname) (fn : fwrite_names) (st : fdstate) :
    filewrite_fs_env γf fn -∗ filewrite_devsw fn -∗
    filewrite_env γf fn st ∗
    (filewrite_env_out fn st -∗ filewrite_fs_out fn ∗ filewrite_devsw fn).
  Proof.
    iIntros "Hfs Hdev". rewrite /filewrite_env /filewrite_env_out.
    destruct st as [|? ? [?| |mj]].
    { (* CLOSED *)
      iSplitR; [done|]. iIntros "_".
      iDestruct (filewrite_fs_env_out with "Hfs") as "Hout".
      iSplitL "Hout"; [iExact "Hout" | iFrame "Hdev"]. }
    { (* an INODE *)
      iSplitL "Hfs"; [iExact "Hfs"|]. iIntros "Hout".
      iSplitL "Hout"; [iExact "Hout" | iFrame "Hdev"]. }
    { (* a PIPE *)
      iSplitR; [done|]. iIntros "_".
      iDestruct (filewrite_fs_env_out with "Hfs") as "Hout".
      iSplitL "Hout"; [iExact "Hout" | iFrame "Hdev"]. }
    { (* a DEVICE *)
      iDestruct (filewrite_devsw_acc fn mj with "Hdev") as "[Hone Hback]".
      iSplitL "Hone"; [iExact "Hone"|].
      iIntros "Hout".
      iDestruct ("Hback" with "Hout") as "Hdev".
      iDestruct (filewrite_fs_env_out with "Hfs") as "Hfo".
      iSplitL "Hfo"; [iExact "Hfo" | iFrame "Hdev"]. }
  Qed.

End SpecSysWrite.

Definition wp_sys_write_sconf_body
    `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ, !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId}
 (γf : gname)                    (* kalloc, the file table  *)
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
  (* NO NUMERIC PREMISE.  [SpecFilewrite] takes [-2^31 <= n < 2^31] and a
     trapframe word satisfies that unconditionally
     ([SpecSysRead.sys_rw_count_range]), so this contract asks its caller for
     NOTHING about the count -- which is what a syscall contract has to do,
     the argument being whatever the user put in a2.  See the header. *)
  (* THE NAMES RECORD IS PINNED TO THE CONSOLE TABLE -- two equations, not a
     resource; a dispatcher builds the record itself and discharges both by
     [reflexivity]. *)
  fwn_wp fn = ConsoleInv.devsw_write_val ->
  fwn_dqv fn = (fun _ => DfracDiscarded) ->
  (* PARKING PREMISE (hart-generic scheduler protocol): every filewrite arm
     sleeps, so this syscall parks. *)
  eb = true ->
  sie_cap_gpr KT1 m av b pj -∗
  (* a syscall runs at push_off level 0 *)
  cpu_own 0%nat eb pj b lks -∗
  kernel_text -∗ kernel_data -∗ pc_is pcE -∗
  (* filewrite's default arm is [panic("filewrite")], and its callees panic
     too; this is theirs *)
  (* ...and that arm calls panic as an ORDINARY call: [kernel_data] above
     mints the literal, and this is the console bundle printk needs. *)
  panic_env -∗
  proc_priv γf pj pidv V -∗
  kalloc_env fsc_kalloc None -∗
  procs_inv γs -∗
  (* ...and the file system in the form that does NOT name a file, plus the
     device table's write column -- which now comes from the CONSOLE TABLE
     ([ConsoleInv.devsw_table], out of [syscall_env]) rather than from a
     ten-cell family this contract threads in and out.  The CAPS are separate
     and stay explicit: consolewrite drives the UART, so they are [dev_inv]
     and the tx lock, not the cons lock, and both come from [printk_env].
     [filewrite_devsw_of_console] is the projection. *)
  filewrite_fs_env γf fn -∗
  filewrite_dev_caps fn -∗
  ConsoleInv.devsw_table -∗
  (* THE CROSSING IS THE LITERAL [true]: filewrite parks. *)
  wp_next true pj (fun (CID : CpuId) =>
    ∀ (mf : regfile) (r : mword 64) (P' : uptd),
      ⌜callee_saved m mf⌝ -∗
      ⌜uptd_ext (pv_upt V) P'⌝ -∗
      ⌜sys_write_ret V v (sys_rw_count v2) r⌝ -∗
      ⌜mf !!! Regidx (mword_of_int 10 : mword 5) = r⌝ -∗
      sie_cap_gpr KT1 mf av b pj -∗
      cpu_own 0%nat eb pj b lks -∗
      pc_is ret_tgt -∗
      proc_priv γf pj pidv (upd_upt V P') -∗
      kalloc_env fsc_kalloc None -∗
      (* the file system, back *)
      filewrite_fs_out fn -∗
      (* the device column is NOT returned: it is persistent, and the caller
         still holds the table it was projected from. *)
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type SYSWRITE.
  Parameter wp_sys_write_sconf :
    forall `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ, !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId}
 (γf : gname)
      (γs : list gname) (j : nat) (γlp : gname)
      (fn : fwrite_names)
      (pidv : mword 32) (V : pprivate)
      (v v2 : mword 64)
      (m : regfile) (av : nat) (eb : bool) (b : bool) (lks : gset string),
      wp_sys_write_sconf_body γf γs j γlp fn pidv V v v2 m av eb b lks.
End SYSWRITE.
