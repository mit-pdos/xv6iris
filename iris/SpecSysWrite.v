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

   [pfd] is NULL, so argfd's [SpecArgfd.ofd_out] costs this caller nothing;
   the error return is hoisted above the branch so both arms reach one
   epilogue with the answer already in a0; and the descriptor environment is
   an OPENER wand for the reason SpecSysFstat.v's header sets out -- a
   syscall cannot name the content of the file its descriptor happens to
   hold, so it cannot own a content-indexed environment up front.  The write
   opener additionally pins [fwn_j] and [fwn_procs], which filewrite's
   contract takes as equations rather than deriving. *)
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
Require Import FsCrash.
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
Require Import SpecSysRead.
Require Import SpecFilewrite.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Import Defs.

Local Open Scope Z_scope.

(* sys_write's own frame is 6 slots ([c.addi16sp sp,sp,-48]); below it
   filewrite wants [filewrite_stack] = 82, which dominates argfd's 24 and
   argint's / argaddr's 18. *)
Definition sys_write_stack : nat := (6 + filewrite_stack)%nat.

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
            !fsCrashG Σ, !icacheG Σ, !irefslotG Σ, !iregG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  (* THE DESCRIPTOR ENVIRONMENT.  SpecSysFstat.v's header has the argument;
     the two differences from the read side are that filewrite's environment
     also mentions the kalloc name (its FD_INODE arm allocates blocks) and
     that filewrite's contract takes [fwn_j] / [fwn_procs] as EQUATIONS, so
     the opener has to promise them.  The environment comes back at a bigger
     [used'] -- the number of ballocs is not a function of anything the
     caller holds -- so the close quantifies it. *)
  Definition write_fdenv (γa γf : gname) (γs : list gname) (j : nat) : iProp Σ :=
    (∀ (k : nat) (q : Qp) (Cf : fcontent),
       ⌜(k < NFILE)%nat⌝ -∗
       file_ref γf k q Cf ==∗
       ∃ (fn : fwrite_names) (q' : Qp),
         ⌜fwn_j fn = j /\ fwn_procs fn = γs⌝ ∗
         filewrite_env γa γf k fn Cf ∗ file_ref γf k q' Cf ∗
         (∀ used' : gset Z,
            file_ref γf k q' Cf -∗ filewrite_env_out fn Cf used' ==∗
              file_ref γf k q Cf))%I.

  (* The trivial instance, and the check that the definition is not
     accidentally unsatisfiable: a file whose type selects no arm costs its
     writer nothing, so the opener is the identity there.  (The environment
     that comes BACK is discarded rather than shown to be [emp] -- [iProp] is
     affine, so a close that has nothing to do needs nothing to be true.) *)
  Lemma write_fdenv_none (γa γf : gname) (γs : list gname) (j : nat)
      (fn0 : fwrite_names) :
    fwn_j fn0 = j -> fwn_procs fn0 = γs ->
    (forall Cf : fcontent, fc_type Cf = FD_NONE) -> ⊢ write_fdenv γa γf γs j.
  Proof.
    intros Hj Hp Hty. rewrite /write_fdenv.
    iIntros (k q Cf) "_ Href". iModIntro. iExists fn0, q.
    iSplitR; [iPureIntro; split; assumption|].
    iPoseProof (filewrite_env_none γa γf k fn0 Cf (Hty Cf)) as "Henv".
    iSplitL "Henv"; [iExact "Henv"|].
    iFrame "Href". iIntros (used') "Href _". iModIntro. iExact "Href".
  Qed.

End SpecSysWrite.

Definition wp_sys_write_sconf_body
    `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !kallocG Σ,
      !bioG Σ, !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ,
      !fsCrashG Σ, !icacheG Σ, !irefslotG Σ, !iregG Σ}
    `{GEN : GenId} `{CID : CpuId}

    (γa : gname) (γf : gname)                    (* kalloc, the file table  *)
    (γs : list gname) (j : nat) (γlp : gname)    (* the running process     *)
    (pidv : mword 32) (V : pprivate)
    (v v2 : mword 64)                            (* syscall arguments 0, 2  *)
    (m : regfile) (av : nat) (eb : bool) (C : iProp Σ) (b : bool) :=
  let pcE : mword 64 := mword_of_int KernelSyms.sys_write in
  let pj := proc_addr j in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  (sys_write_stack <= av)%nat ->
  (j < NPROC)%nat ->
  γs !! j = Some γlp ->
  length γs = NPROC ->
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
  cpu_own 0%nat eb pj C b -∗
  kernel_text -∗ kernel_data -∗ pc_is pcE -∗
  (* filewrite's default arm is [panic("filewrite")], and its callees panic
     too; this is theirs *)
  panic_wp_any -∗
  proc_priv γf pj pidv V -∗
  kalloc_env γa None -∗
  procs_inv γs -∗
  (* ...and the environment for whatever file the descriptor names *)
  write_fdenv γa γf γs j -∗
  (* THE CROSSING IS THE LITERAL [true]: filewrite parks. *)
  wp_next true pj (fun (CID : CpuId) =>
    ∀ (mf : regfile) (r : mword 64) (P' : uptd),
      ⌜callee_saved m mf⌝ -∗
      ⌜uptd_ext (pv_upt V) P'⌝ -∗
      ⌜sys_write_ret V v (sys_rw_count v2) r⌝ -∗
      ⌜mf !!! Regidx (mword_of_int 10 : mword 5) = r⌝ -∗
      sie_cap_gpr mf av b pj -∗
      cpu_own 0%nat eb pj C b -∗
      pc_is ret_tgt -∗
      proc_priv γf pj pidv (upd_upt V P') -∗
      kalloc_env γa None -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type SYSWRITE.
  Parameter wp_sys_write_sconf :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !kallocG Σ,
             !bioG Σ, !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ,
             !fsCrashG Σ, !icacheG Σ, !irefslotG Σ, !iregG Σ}
      `{GEN : GenId} `{CID : CpuId}

      (γa : gname) (γf : gname)
      (γs : list gname) (j : nat) (γlp : gname)
      (pidv : mword 32) (V : pprivate)
      (v v2 : mword 64)
      (m : regfile) (av : nat) (eb : bool) (C : iProp Σ) (b : bool),
      wp_sys_write_sconf_body γa γf γs j γlp pidv V v v2 m av eb C b.
End SYSWRITE.
