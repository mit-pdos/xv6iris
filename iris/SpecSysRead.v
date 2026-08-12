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
   index), which is exactly the case [SpecArgfd.ofd_out] exists for; the
   error return is hoisted above the branch so that both arms reach one
   epilogue with the answer already in a0; and the descriptor environment is
   an OPENER wand for the reason SpecSysFstat.v's header sets out at length
   -- a syscall cannot name the content of the file its descriptor happens
   to hold, so it cannot own a content-indexed environment up front. *)
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
Require Import SpecPanic.
Require Import FdSlots.
Require Import ProcGeom.
Require Export SwtchCtx.
Require Import CpuOwn.
Require Import SchedCtx.
Require Import SleepLock.
Require Import WpUart.
Require Import DiskPtsto DiskInv.
Require Import BioInv.
Require Import FsBlocks LogInv.
Require Import FsCrash.        (* [BSIZE] -- the numeric premise mentions it *)
Require Import DinodeEnc.
Require Import InodeInv.
Require Import InodeRegion.
Require Import IrefSlots.
Require Import IcacheInv.
Require Import IcacheEscrow.
Require Import KallocInv.
Require Import UserPtTree.
Require Import KvmSpec.
Require Import ProcPtOwn.
Require Import PipeInvDefs.
Require Import FileOff ProcInv.
Require Import FileInvDefs.
Require Import SpecArgfd.
Require Import SpecArgint.
Require Import SpecArgaddr.
Require Import SpecFileread.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Import Defs.

Local Open Scope Z_scope.

(* sys_read's own frame is 6 slots ([c.addi16sp sp,sp,-48]); below it
   fileread wants [fileread_stack] = 76, which dominates argfd's 24 and
   argint's / argaddr's 18.  An expression, not a literal, so a change to
   readi's budget cannot silently leave this one behind. *)
Definition sys_read_stack : nat := (6 + fileread_stack)%nat.

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
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !kallocG Σ,
            !bioG Σ, !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ,
            !icacheG Σ, !irefslotG Σ, !iregG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  (* THE DESCRIPTOR ENVIRONMENT.  See SpecSysFstat.v's header for the whole
     argument; in one line: [fileread_env γf k fn Cf] is indexed by the
     file's CONTENT, and a syscall cannot name the content of the file its
     descriptor happens to hold, so what it takes is the wand that turns the
     reference it finds into that environment and back. *)
  Definition read_fdenv (γf : gname) : iProp Σ :=
    (∀ (k : nat) (q : Qp) (Cf : fcontent),
       ⌜(k < NFILE)%nat⌝ -∗
       file_ref γf k q Cf ==∗
       ∃ (fn : fread_names) (q' : Qp),
         fileread_env γf k fn Cf ∗ file_ref γf k q' Cf ∗
         (file_ref γf k q' Cf -∗ fileread_env_out fn Cf ==∗
            file_ref γf k q Cf))%I.

  (* The trivial instance, and the check that the definition is not
     accidentally unsatisfiable: a file whose type selects no arm costs its
     reader nothing, so the opener is the identity there.  (The environment
     that comes BACK is discarded rather than shown to be [emp] -- [iProp] is
     affine, so a close that has nothing to do needs nothing to be true.) *)
  Lemma read_fdenv_none (γf : gname) (fn0 : fread_names) :
    (forall Cf : fcontent, fc_type Cf = FD_NONE) -> ⊢ read_fdenv γf.
  Proof.
    intro Hno. rewrite /read_fdenv.
    iIntros (k q Cf) "_ Href". iModIntro. iExists fn0, q.
    iPoseProof (fileread_env_none γf k fn0 Cf (Hno Cf)) as "Henv".
    iSplitL "Henv"; [iExact "Henv"|].
    iFrame "Href". iIntros "Href _". iModIntro. iExact "Href".
  Qed.

End SpecSysRead.

Definition wp_sys_read_sconf_body
    `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !kallocG Σ,
      !bioG Σ, !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ,
      !icacheG Σ, !irefslotG Σ, !iregG Σ}
    `{GEN : GenId} `{CID : CpuId}

    (γa : gname) (γf : gname)                    (* kalloc, the file table  *)
    (γs : list gname) (j : nat) (γlp : gname)    (* the running process     *)
    (pidv : mword 32) (V : pprivate)
    (v v2 : mword 64)                            (* syscall arguments 0, 2  *)
    (m : regfile) (av : nat) (eb : bool) (C : iProp Σ) (b : bool) :=
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
  (* THE TWO INHERITED NUMERIC PREMISES.  See the header: both are about the
     count the USER supplied, both are fileread's (hence readi's), and
     neither can be discharged here because sys_read checks nothing.  The
     upper half of the range is free ([sys_rw_count_lt]). *)
  0 <= sys_rw_count v2 ->
  Z.of_nat MAXFILE * Z.of_nat BSIZE + sys_rw_count v2 < 2 ^ 31 ->
  (* PARKING PREMISE (hart-generic scheduler protocol): every fileread arm
     sleeps, so this syscall parks. *)
  eb = true ->
  sie_cap_gpr m av b pj -∗
  (* a syscall runs at push_off level 0 *)
  cpu_own 0%nat eb pj C b -∗
  kernel_text -∗ kernel_data -∗ pc_is pcE -∗
  (* fileread itself never panics on a well-typed file; its default arm and
     its callees do, and this is theirs *)
  panic_wp_any -∗
  proc_priv γf pj pidv V -∗
  kalloc_env γa None -∗
  procs_inv γs -∗
  (* ...and the environment for whatever file the descriptor names *)
  read_fdenv γf -∗
  (* THE CROSSING IS THE LITERAL [true]: fileread parks, and a park moves the
     hart with interrupts off, so the crossing has nothing to do with SIE. *)
  wp_next true pj (fun (CID : CpuId) =>
    ∀ (mf : regfile) (r : mword 64) (P' : uptd),
      ⌜callee_saved m mf⌝ -∗
      ⌜uptd_ext (pv_upt V) P'⌝ -∗
      ⌜sys_read_ret V v (sys_rw_count v2) r⌝ -∗
      ⌜mf !!! Regidx (mword_of_int 10 : mword 5) = r⌝ -∗
      sie_cap_gpr mf av b pj -∗
      cpu_own 0%nat eb pj C b -∗
      pc_is ret_tgt -∗
      proc_priv γf pj pidv (upd_upt V P') -∗
      kalloc_env γa None -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type SYSREAD.
  Parameter wp_sys_read_sconf :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !kallocG Σ,
             !bioG Σ, !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ,
             !icacheG Σ, !irefslotG Σ, !iregG Σ}
      `{GEN : GenId} `{CID : CpuId}

      (γa : gname) (γf : gname)
      (γs : list gname) (j : nat) (γlp : gname)
      (pidv : mword 32) (V : pprivate)
      (v v2 : mword 64)
      (m : regfile) (av : nat) (eb : bool) (C : iProp Σ) (b : bool),
      wp_sys_read_sconf_body γa γf γs j γlp pidv V v v2 m av eb C b.
End SYSREAD.
