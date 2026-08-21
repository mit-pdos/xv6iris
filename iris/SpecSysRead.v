(* SpecSysRead.v -- the public interface of sys_read(), stated independently
   of its proof.  Requires only the definitional layer and its callees'
   SPECS -- never a whole-function proof file -- so every function proof can
   be checked in parallel.

     uint64 sys_read(void) {
       struct file *f;
       int n;
       uint64 p;
       argaddr(1, &p);
       argint(2, &n);
       if (argfd(0, 0, &f) < 0) return -1;
       return fileread(f, p, n);
     }

   @ KernelSyms.sys_read, 72 bytes / 25 instructions (CodeSysRead.v has the
   listing).  A 48-byte frame: ra and s0 are slots 1 and 2, [f] is slot 3
   ([s0-24]), the [int n] is the UPPER WORD of slot 4 ([s0-28]), [p] is
   slot 5 ([s0-40]) and slot 6 is unused.

     +0x00  7179        c.addi16sp sp,sp,-48
     +0x02  f406/f022   c.sdsp     ra,40(sp) / s0,32(sp)
     +0x06  1800        c.addi4spn s0,sp,48        s0 := the entry sp
     +0x08  fd840593    addi       a1,s0,-40       &p
     +0x0c  4505        c.li       a0,1
     +0x0e  bebfd0ef    jal        ra,argaddr
     +0x12  fe440593    addi       a1,s0,-28       &n
     +0x16  4509        c.li       a0,2
     +0x18  bc5fd0ef    jal        ra,argint
     +0x1c  fe840613    addi       a2,s0,-24       &f
     +0x20  4581        c.li       a1,0            pfd = NULL
     +0x22  4501        c.li       a0,0
     +0x24  dbfff0ef    jal        ra,argfd
     +0x28  87aa        c.mv       a5,a0
     +0x2a  557d        c.li       a0,-1           the error return, hoisted
     +0x2c  0007ca63    blt        a5,x0,+20       -> the epilogue
     +0x30  fe442603    lw         a2,-28(s0)      n, SIGN-extended
     +0x34  fd843583    ld         a1,-40(s0)      p
     +0x38  fe843503    ld         a0,-24(s0)      f
     +0x3c  d22ff0ef    jal        ra,fileread
     +0x40  70a2/7402/6145/8082    the epilogue

   sys_write is this function INSTRUCTION FOR INSTRUCTION (same frame, same
   offsets, same registers); only the three [jal] targets differ, and the
   third is filewrite.  See SpecSysWrite.v.

   THE COUNT IS SIGN-EXTENDED, and that is the whole numeric story: argint
   narrows argraw's [uint64] to the [int] cell ([SpecArgint], a [c.sw], i.e.
   [trunc32]) and the [lw] at +0x30 reads it back SIGNED, so what reaches
   fileread's a2 is [sign_extend' 64 (trunc32 v)] -- which
   [RiscvExtras.sext32_64_moi] says is [mword_of_int (bv_signed (trunc32 v))]
   exactly.  [sys_rw_count] below is that value.

   ==== THE TWO NUMERIC PREMISES, AND WHY THEY ARE STILL HERE ============

   READ THIS BEFORE ADDING A CALLER.  [SpecFileread] takes

       0 <= n         and        MAXFILE*BSIZE + n < 2^31

   and sys_read passes [n] STRAIGHT FROM USER INPUT: the C checks nothing
   between argint and the call, and the object code confirms it (the only
   branch in the function is argfd's).  So neither premise can be discharged
   here, and both appear below as premises of THIS contract, about the
   trapframe word the user wrote.

   That is not new debt and it is not this stage's invention -- it is
   claude-notes/design/file-table.md's, recorded there verbatim: "sys_read
   cannot discharge it from unchecked user input, and that is known debt, to
   be settled at sys_read, not inside fileread", with two options, (a) prove
   readi's own overflow arm (which needs a wrapping-[addw] reading the tree
   does not have) or (b) bound [n] at the syscall boundary.  What this file
   adds is the precise statement of what is owed, and the observation that
   the two premises are NOT the same kind of thing:

   * [MAXFILE*BSIZE + n < 2^31] is readi's joint bound, inherited through
     fileread, and it is option (a)'s: xv6's own [off + n < off] test in
     readi is the real kernel's answer and the model kills it by premise.
     sys_write does NOT carry it -- filewrite's chunking closes writei's
     joint bound internally (fs-sysfile S3f) -- so this premise is the one
     genuine asymmetry between the two syscalls.
   * [0 <= n] is carried by BOTH sys_read and sys_write, because
     [SpecFilewrite] takes [0 <= n < 2^31] as well.  A negative [n] is
     perfectly well handled by the C (the loop body never runs and the tail
     answers -1), so this half is a modelling premise, not a kernel fact,
     and it is the cheaper of the two to retire.

   THE UPPER HALF IS FREE: [sys_rw_count] is [bv_signed] of a 32-bit word, so
   [< 2^31] holds unconditionally ([sys_rw_count_lt] below).  Only the lower
   bound and the MAXFILE offset have to be assumed.

   ==== THE REST OF THE SHAPE ============================================

   [pfd] is NULL (sys_read wants the [struct file *] and not the descriptor
   index), which is exactly the case [SpecArgfd.ofd_out] exists for; and the
   error return is hoisted above the branch so that both arms reach one
   epilogue with the answer already in a0.

   ==== THE ENVIRONMENT IS OWNED, NOT OPENED (fs-sysfile S4c) ============

   S4 froze this contract with an OPENER -- a wand turning the reference the
   descriptor turned out to hold into fileread's environment for THAT file --
   because [fileread_env] was indexed by the file's CONTENT and by its fd
   SLOT, neither of which a syscall can name ([ProcInv.ofile_slot] quantifies
   the slot, the fraction and the content existentially).  S4' overturned it,
   and the reason is stronger than taste: the opener promised back a
   [file_ref gf k q' Cf] at a SMALLER fraction, and NO SUCH THING EXISTS --
   [FileInvDefs.fref_tok]'s reference COUNT rides in the same map entry as the
   fraction, so two fragments at [q/2] compose to [(q, 2)] and not to
   [(q, 1)].  Splitting a [file_ref] at all needs the ftable AUTHORITY, i.e.
   filedup's ghost step, which is unsound without the physical [f->ref++].
   The opener was satisfiable only at [q' = q], with the whole environment
   already in the caller's hands: it deferred the problem rather than solving
   it.  SpecSysFstat.v's header has the full account.

   What this contract takes instead is [fileread_fs_env], which names neither
   the content nor the slot: the escrow FAMILY, the sleeplock FAMILY, the
   off-borrow FAMILY, the inode region, the block cache, the disk fabric and
   the region-wide inum geometry.  The per-inode pieces the old
   environment asked its caller for -- the itable slot, the inum, the device,
   the region bound and the SHARE -- were inside the reference all along
   ([FileInvDefs.inode_pay]); fileread carves them out itself
   ([SpecFileread.fileread_pay_carve]) and gathers them back, so the syscall
   owes nothing per-file at all.

   ==== AND THE DEVICE TABLE'S READ COLUMN ================================

   The FD_DEVICE arm's [devsw[major].read] cell is the one thing that could
   NOT be made content-independent by restating it, because its ADDRESS is a
   function of [dev_major Cf]: one cell covers one major.  The honest answer is
   that a syscall which may be handed any descriptor owns the whole column --
   ten cells, [fileread_devsw] -- and [fileread_devsw_acc] picks the entry
   the file turns out to name and takes it straight back (the arm only READS
   it).  That is not a hidden weakening: reading a device descriptor really
   does require owning that table entry, and nothing smaller is ownable
   before the descriptor is resolved. *)
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
Require Import SpecPanic.
Require Import FdSlots.
Require Import ProcGeom.
Require Export SwtchCtx.
Require Import CpuOwn.
Require Import SchedCtx.
Require Import WpUart.
Require Import LogInv.
Require Import FsCrash.        (* [BSIZE] -- the numeric premise mentions it *)
Require Import IrefSlots.
Require Import UserPtTree.
Require Import KvmSpec.
Require Import ProcPtOwn.
Require Import ProcInv.
Require Import FileInvDefs.
Require Import SpecArgfd.
Require Import ConsoleInv.
Require Import SpecFileread.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import ProcAvail.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Import Defs.

Local Open Scope Z_scope.

(* sys_read's own frame is 6 slots ([c.addi16sp sp,sp,-48]); below it
   fileread wants [fileread_stack] = 76, which dominates argfd's 24 and
   argint's / argaddr's 18.  An expression, not a literal, so a change to
   readi's budget cannot silently leave this one behind. *)
Notation sys_read_stack := ((6 + fileread_stack)%nat) (only parsing).
(* THE COUNT THAT REACHES file.c, as a function of the trapframe word the
   user wrote: argint's [c.sw] narrowing followed by the [lw]'s sign
   extension.  Shared with sys_write, whose +0x30 is the same instruction. *)
Definition sys_rw_count (v : mword 64) : Z := bv_signed (trunc32 v).

(* the upper half of [0 <= n < 2^31] is free -- a 32-bit signed value *)
Lemma sys_rw_count_lt (v : mword 64) : sys_rw_count v < 2 ^ 31.
Proof.
  rewrite /sys_rw_count.
  pose proof (bv_signed_in_range 32 (trunc32 v) ltac:(discriminate)) as Hr.
  assert (Hhm : bv_half_modulus 32 = 2147483648%Z) by (vm_compute; reflexivity).
  rewrite Hhm in Hr. destruct Hr as [_ Hr].
  (* [exact], which converts, is what crosses the [mword 32] / [bv 32] width
     gap -- [lia] sees the two [bv_signed] applications as distinct atoms
     (durable-notes: the width is an unreduced [if]). *)
  change (2 ^ 31)%Z with 2147483648%Z. exact Hr.
Qed.

(* ...and so is the LOWER half: [bv_signed] of a 32-bit word is an [int] on
   both sides.  Together these two ARE the whole numeric content of "the user
   wrote a word into the trapframe", which is why sys_read and sys_write can
   hand file.c a count with no premise about it at all (31f115a). *)
Lemma sys_rw_count_ge (v : mword 64) : - 2 ^ 31 <= sys_rw_count v.
Proof.
  rewrite /sys_rw_count.
  pose proof (bv_signed_in_range 32 (trunc32 v) ltac:(discriminate)) as Hr.
  assert (Hhm : bv_half_modulus 32 = 2147483648%Z) by (vm_compute; reflexivity).
  rewrite Hhm in Hr. destruct Hr as [Hr _].
  change (2 ^ 31)%Z with 2147483648%Z. exact Hr.
Qed.

(* the two halves, in the shape file.c's contracts ask for *)
Lemma sys_rw_count_range (v : mword 64) : - 2 ^ 31 <= sys_rw_count v < 2 ^ 31.
Proof. split; [apply sys_rw_count_ge | apply sys_rw_count_lt]. Qed.

(* ...and the register the [lw] leaves it in is that literal *)
Lemma sys_rw_count_reg (v : mword 64) :
  (sign_extend' 64 (trunc32 v) : mword 64) = mword_of_int (sys_rw_count v).
Proof. rewrite /sys_rw_count. apply sext32_64_moi. Qed.

(* WHAT SYS_READ RETURNS.  Indexed by [arg_fd], not by [r]: fileread's own
   -1 (not readable / a bad device major / a faulted copy) is not
   distinguishable from argfd's by the value. *)
Definition sys_read_ret (V : pprivate) (v : mword 64) (n : Z) (r : mword 64) : Prop :=
  (r = (mword_of_int (-1) : mword 64) /\ arg_fd v (pv_ofile V) = None)
  \/ (exists (fd : nat) (fv : mword 64),
        arg_fd v (pv_ofile V) = Some (fd, fv) /\ fileread_ret n r).

Section SpecSysRead.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  (* THE ENVIRONMENT FILEREAD'S [if] ACTUALLY ASKS FOR, out of the two
     content-independent bundles this contract owns.  This is the whole of
     what the S4 opener was trying to be, and it is a few lines now that
     neither bundle mentions the content: the syscall owns both, fileread's
     type test decides which is consumed, and either way both come back.
     ([SpecFileclose.fileclose_env_frame] is the same move one stage down.) *)
  Lemma read_env_frame (γf : gname) (fn : fread_names) (Cf : fcontent) :
    fileread_fs_env γf fn -∗ fileread_devsw fn -∗
    fileread_env γf fn Cf ∗
    (fileread_env_out fn Cf -∗ fileread_fs_out fn ∗ fileread_devsw fn).
  Proof.
    iIntros "Hfs Hdev". rewrite /fileread_env /fileread_env_out.
    case_bool_decide.
    { (* FD_PIPE: nothing is asked for, and the fs half must still answer
         [fileread_fs_out] -- which it does, [fileread_fs_env_out]. *)
      iSplitR; [done|]. iIntros "_".
      iDestruct (fileread_fs_env_out with "Hfs") as "$". iFrame "Hdev". }
    case_bool_decide.
    { (* FD_DEVICE: hand over the entry the major names, keep the column's
         wand, and answer the fs half out of the bundle nothing touched. *)
      iDestruct (fileread_devsw_acc fn Cf with "Hdev") as "[Hone Hback]".
      iSplitL "Hone"; [iExact "Hone"|].
      iIntros "Hout". iDestruct ("Hback" with "Hout") as "$".
      iApply (fileread_fs_env_out with "Hfs"). }
    case_bool_decide.
    { (* FD_INODE: the fs half goes, the column stays *)
      iSplitL "Hfs"; [iExact "Hfs"|]. iIntros "$". iFrame "Hdev". }
    { (* the panic arm *)
      iSplitR; [done|]. iIntros "_".
      iDestruct (fileread_fs_env_out with "Hfs") as "$". iFrame "Hdev". }
  Qed.

End SpecSysRead.

Definition wp_sys_read_sconf_body
    `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
      !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId}

    (γa : gname) (γf : gname)                    (* kalloc, the file table  *)
    (γs : list gname) (j : nat) (γlp : gname)    (* the running process     *)
    (fn : fread_names)                           (* the file system's ghosts *)
    (pidv : mword 32) (V : pprivate)
    (v v2 : mword 64)                            (* syscall arguments 0, 2  *)
    (m : regfile) (av : nat) (eb : bool) (b : bool) (lks : gset string) :=
  let pcE : mword 64 := mword_of_int KernelSyms.sys_read in
  let pj := proc_addr j in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  (sys_read_stack <= av)%nat ->
  (j < NPROC)%nat ->
  γs !! j = Some γlp ->
  length γs = NPROC ->
  (* the three syscall arguments, out of the trapframe page [proc_priv]
     carries.  Argument 1 (the user destination) is fetched but never
     inspected here -- it goes straight to fileread, whose callees are total
     in it -- so only its EXISTENCE has to be assumed. *)
  pv_tf V !! tf_arg_idx 0 = Some v ->
  (exists v1 : mword 64, pv_tf V !! tf_arg_idx 1 = Some v1) ->
  pv_tf V !! tf_arg_idx 2 = Some v2 ->
  (* NO NUMERIC PREMISE.  [SpecFileread] takes [-2^31 <= n < 2^31] and a
     trapframe word satisfies that unconditionally ([sys_rw_count_range]),
     so this contract asks its caller for NOTHING about the count -- which is
     what a syscall contract has to do, the argument being whatever the user
     put in a2.  See the header. *)
  (* THE NAMES RECORD IS PINNED TO THE CONSOLE TABLE.  Two equations, not a
     resource: the record's device column is a FUNCTION of the major, and
     these say it is the table's own ([ConsoleInv.devsw_read_val]) held at
     the fraction the table holds it under.  A dispatcher builds the record
     itself, so it discharges both by [reflexivity]. *)
  frn_rp fn = ConsoleInv.devsw_read_val ->
  frn_dqv fn = (fun _ => DfracDiscarded) ->
  (* PARKING PREMISE (hart-generic scheduler protocol): every fileread arm
     sleeps, so this syscall parks. *)
  eb = true ->
  sie_cap_gpr KT1 m av b pj -∗
  (* a syscall runs at push_off level 0 *)
  cpu_own 0%nat eb pj b lks -∗
  kernel_text -∗ kernel_data -∗ pc_is pcE -∗
  (* fileread itself never panics on a well-typed file; its default arm and
     its callees do, and this is theirs *)
  (* fileread's default arm calls [panic("fileread")], which is an ordinary
     call: [kernel_data] above mints the literal, and this is the console
     bundle printk needs.  Persistent, and syscall already holds it. *)
  panic_env -∗
  proc_priv γf pj pidv V -∗
  kalloc_env γa None -∗
  procs_inv γs -∗
  (* ...and the file system in the form that does NOT name a file, plus the
     CONSOLE INVARIANT, which is where the device table's read column comes
     from.  ONE PERSISTENT PROPOSITION, out of [syscall_env]: this contract
     no longer threads a ten-cell family in and out, because the table is
     written once by consoleinit and held at a discarded fraction ever after
     ([ConsoleInv.devsw_table]).  [fileread_devsw_of_console] is the
     projection, and the two equations above are what pin the names record to
     the table's own values. *)
  fileread_fs_env γf fn -∗
  ConsoleInv.console_inv (frn_cons fn) -∗
  (* THE CROSSING IS THE LITERAL [true]: fileread parks, and a park moves the
     hart with interrupts off, so the crossing has nothing to do with SIE. *)
  wp_next true pj (fun (CID : CpuId) =>
    ∀ (mf : regfile) (r : mword 64) (P' : uptd),
      ⌜callee_saved m mf⌝ -∗
      ⌜uptd_ext (pv_upt V) P'⌝ -∗
      ⌜sys_read_ret V v (sys_rw_count v2) r⌝ -∗
      ⌜mf !!! Regidx (mword_of_int 10 : mword 5) = r⌝ -∗
      sie_cap_gpr KT1 mf av b pj -∗
      cpu_own 0%nat eb pj b lks -∗
      pc_is ret_tgt -∗
      proc_priv γf pj pidv (upd_upt V P') -∗
      kalloc_env γa None -∗
      (* the file system, back.  fileread's own postcondition returns the
         superblock fraction and the slot unit; everything else in the bundle
         is persistent, which is why what comes back is [fileread_fs_out] and
         not [fileread_fs_env].  The device column is returned whole -- the
         arm only reads it. *)
      fileread_fs_out fn -∗
      (* the device column is NOT returned: it is persistent, and the caller
         still holds the invariant it was projected from. *)
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type SYSREAD.
  Parameter wp_sys_read_sconf :
    forall `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
             !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId}

      (γa : gname) (γf : gname)
      (γs : list gname) (j : nat) (γlp : gname)
      (fn : fread_names)
      (pidv : mword 32) (V : pprivate)
      (v v2 : mword 64)
      (m : regfile) (av : nat) (eb : bool) (b : bool) (lks : gset string),
      wp_sys_read_sconf_body γa γf γs j γlp fn pidv V v v2 m av eb b lks.
End SYSREAD.
