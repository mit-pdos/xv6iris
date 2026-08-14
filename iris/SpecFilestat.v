(* SpecFilestat.v -- the public interface of filestat, stated independently of
   its proof.  Requires only the definitional layer and its callees' SPECS --
   never a whole-function proof file -- so every function proof can be checked
   in parallel.

     int filestat(struct file *f, uint64 addr) {
       struct proc *p = myproc();
       struct stat st;
       if (f->type == FD_INODE || f->type == FD_DEVICE) {
         ilock(f->ip);
         stati(f->ip, &st);
         iunlock(f->ip);
         if (copyout(p->pagetable, addr, (char * )&st, sizeof(st)) < 0)
           return -1;
         return 0;
       }
       return -1;
     }

   98 bytes, 40 instructions.  TWO arms and one epilogue, and the whole of the
   second arm is a [c.li a0,-1] that jumps into the middle of the first arm's
   restore sequence.

   ==== THE DISPATCH, AS gcc WROTE IT ===================================

   There is no two-way test in the object code.  [+0x14] loads [f->type],
   [+0x16] subtracts 2, and [+0x1a] is a single [bltu a4,a5] against 1 -- so
   "FD_INODE or FD_DEVICE" is the UNSIGNED RANGE TEST [type - 2 <= 1], and the
   branch is taken exactly when the file is NEITHER.  Both surviving types
   carry an inode in [f->ip] and take the identical path: filestat never looks
   at [f->major] and never reaches [devsw], which is why -- unlike fileread and
   filewrite -- it has no device arm and no indirect call.

   The AST's [BTYPE] field order is [(imm, rs2, rs1, op)], so the recorded
   [BTYPE (68, a5, a4, BLTU)] is [bltu a4,a5]; reading it the other way would
   invert the dispatch and give FD_INODE the error arm.

   ==== struct stat LIVES ON FILESTAT'S OWN FRAME =======================

   [+0x2a] is [addi s2,s0,-72], i.e. [&st = sp + 8] in an 80-byte (10-slot)
   frame: the 24-byte struct occupies frame slots 9, 8 and 7 exactly
   ([StackBytes.slots3_bytes_own] at [k = 9]).  Two consequences, and they are
   the whole answer to the fs-namei close-out's item 4 ("the stat hole"):

   * NOTHING ABOUT THE STAT BUFFER APPEARS IN THIS CONTRACT.  The buffer is
     filestat's own stack, carved out of the [stack_own] that [sie_cap_gpr]
     already carries and handed back at the epilogue.  A caller owes the
     SLOTS -- that is what [filestat_stack <= K] says -- and nothing else.

   * THE FOUR HOLE BYTES (12..15, the alignment gap before the 8-byte
     [st->size] that [SpecStati.stat_at] deliberately does not mention) NEED
     NO CLAUSE EITHER.  They are frame bytes whose contents [stack_own] leaves
     existential; stati does not write them; copyout copies all 24 bytes and
     its contract says NOTHING about what the user pages end up holding (see
     SpecCopyout.v's header -- [proc_pt] owns its pages with existential
     contents).  So there is no resource anywhere in this cone that could
     record the hole's value, and quantifying it would be a claim about the
     user's memory that the layer below cannot deliver.  The honest statement
     is silence, and it costs a caller nothing.

   ==== THE REFERENCE, AND WHAT SELECTS THE ENVIRONMENT ==================

   SpecFileread.v's shape, and for the same reason.  filestat takes
   [file_ref γf k q Cf] at an ARBITRARY q -- it is a borrower, not a reference
   holder -- and gives it back unchanged.  The type is read out of the
   reference's own content fraction, so the loaded word IS [fc_type Cf] and
   the branch being taken is the Coq fact about [Cf]; no ghost state has to
   tell an inode from a pipe.

   What a caller must own therefore depends on the type, and only two cases
   exist:

   * FD_INODE or FD_DEVICE -> ilock's and iunlock's environment: the icache
     seam, the block cache and the disk fabric.  NOT readi's or writei's --
     filestat reads no data block, so no log, no bitmap, no [inode_map] and
     no [inode_blocks] appear.  stati wants only [InodeInv.inode_meta] and the
     two identity halves, all three of which ride inside the [ic_loaded] that
     ilock hands out.
   * anything else -> NOTHING.  The arm is the [c.li a0,-1] at +0x5e, which
     touches no state at all.  Note that this is NOT a panic: filestat is the
     one function in this batch whose "wrong type" case is an ordinary error
     return (fileread and filewrite both panic there).

   THE OFFSET DOES NOT APPEAR.  [f->off] is not read and not written, so
   [FileOff.off_inv] -- which fileread's contract must carry -- is absent here.

   ==== WHAT IS AMBIENT =================================================

   [proc_priv], [kalloc_env] and [procs_inv] are premises of the contract
   proper rather than of an arm: myproc runs before the dispatch, and the
   surviving arm copies into user memory (copyout reaches vmfault, hence
   kalloc).  The error arm hands all of it straight back.  Every caller of
   filestat is a syscall and holds all three already.

   ==== WHAT THE POSTCONDITION SAYS =====================================

   Two things, and no more:

   * the return value is 0 or -1.  The [sraiw a0,a0,31] at +0x4a is the
     [< 0 ? -1 : 0] idiom applied to copyout's own two-valued result, so the
     first arm answers exactly what copyout did, re-encoded;
   * the process block comes back at an EXTENDED page table ([uptd_ext]) --
     copyout's [vmfault] may have mapped pages, and that is the only trace it
     leaves that this layer can see.

   IT SAYS NOTHING ABOUT WHAT THE USER READS BACK, and that is inherited from
   copyout rather than lost here: see the header above and SpecCopyout.v's.
   A caller that wants "the user's struct stat now holds this inode's
   metadata" needs a contents-indexed refinement of [proc_pt], which the
   user-execution layer cannot carry through a return to user mode anyway. *)
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
Require Import CalleeSaved KernelText.
Require Import IntrDefs.
Require Import WpNext.
Require Import WpLock.
Require Import PanicStub.
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
Require Import DinodeEnc.
Require Import InodeInv.
Require Import InodeRegion.
Require Import IrefSlots.
Require Import IcacheInv.
Require Import IcacheEscrow.
Require Import IcacheBoot.   (* [ic_sleeplocks]: the canonical entry-sleeplock
                                family -- IcacheBoot.v's header names itself the
                                home for it, and a contract that cannot know
                                WHICH entry its descriptor points at takes the
                                family. *)
Require Import KallocInv.
Require Import UserPtTree.
Require Import KvmSpec.
Require Import ProcPtOwn.
Require Import ProcInv.
Require Import FileInvDefs.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Import Defs.

Local Open Scope Z_scope.

(* filestat's own frame is 10 slots ([c.addi16sp sp,-80]: ra, s0, s1, s4
   spilled unconditionally, s2 and s3 spilled only on the surviving arm, three
   slots for [struct stat] and one unused), and its deepest callee is COPYOUT
   at 52 -- which dominates ilock's 44, iunlock's 26, myproc's 10 and stati's
   2.  A CONSTANT, not a per-arm bound: the stack a function may need is a
   property of the function (durable-notes.md).

   52, NOT 50, AND THE 10 GETS NO TRAP RESERVE.  copyout's budget rose
   because [psz] has to outlive walkaddr / vmfault / memmove, so gcc gave it a
   callee-saved home in s11 and copyout's frame grew to 14 slots
   (SpecCopyout.v).  filestat is [eb]-generic and [trap_res false = 0], so the
   call site can offer only [K - 10] and there is nothing to borrow against --
   the same accounting as [SpecKwait.K_kwait], and the opposite of
   [SpecPiperead.piperead_stack], whose copyout call DOES sit inside the
   reserve and so needed no rise. *)
Definition filestat_stack : nat := (10 + 52)%nat.

(* WHAT FILESTAT RETURNS.  copyout answers 0 or -1 and [sraiw a0,a0,31] maps
   that pair to itself; the type-error arm answers -1 outright. *)
Definition filestat_ret (r : mword 64) : Prop :=
  r = (mword_of_int 0 : mword 64) \/ r = (mword_of_int (-1) : mword 64).

(* THE TYPE TEST, as the object code performs it: an unsigned [type - 2 <= 1].
   Stated as the disjunction the arms are indexed by, so nothing downstream
   has to redo the [addiw]/[bltu] reasoning. *)
Definition fstat_has_inode (Cf : fcontent) : Prop :=
  fc_type Cf = FD_INODE \/ fc_type Cf = FD_DEVICE.

Global Instance fstat_has_inode_dec Cf : Decision (fstat_has_inode Cf).
Proof. rewrite /fstat_has_inode. apply _. Defined.

(* ---------------------------------------------------------------------- *)
(*  The ghost names the inode arm is indexed by                            *)
(* ---------------------------------------------------------------------- *)
(* [SpecFileread.fread_names] MINUS the two device-table fields (filestat has
   no [devsw] arm) and MINUS nothing else: ilock and iunlock want exactly the
   same seam here as they do there.  Spelled out rather than imported, for the
   reason SpecFileclose.fclose_names is: a contract file should not depend on
   a sibling contract's record layout. *)
(* NOTHING PER-INODE IS IN HERE, and that is the point (fs-sysfile S4' /
   blocker 2's ratified alternative).  The itable SLOT, the inum, the lent
   share's fraction, the entry's two sleeplock gnames, the device and the
   region's block count are all things a CALLER cannot know: a reference
   borrowed out of [ProcInv.ofile_slot] comes with its slot, fraction and
   content existentially quantified.  Every one of them comes out of the
   reference itself instead ([FileInvDefs.inode_pay] carries
   [IcacheRef.inode_shr_held_gen (fc_ip Cf) (q * Q) g], which names the slot,
   the device and the inum and IS the share ilock wants), or is the ambient
   cache's ([IcacheRef.icfg_dev] / [icfg_nib]), or is existential under the
   sleeplock FAMILY.  What is left is exactly the content-independent bundle
   [SpecFileclose.fileclose_fs_env] already had. *)
Record fstat_names := MkFStatNames {
  fsn_uart       : uart_names;
  fsn_disk       : disk_names;
  fsn_dlock      : gname;         (* virtio_disk.lock                       *)
  fsn_pd         : mword 64;
  fsn_pav        : mword 64;
  fsn_pu         : mword 64;
  fsn_bio        : bio_names;
  fsn_fs         : fs_names;
  fsn_ireg       : gname;         (* the inode region (InodeRegion.v)       *)
  fsn_ic         : ic_names;      (* the icache's names (IcacheEscrow.v)    *)
  fsn_cov        : gset Z;
  fsn_logstart   : Z;
  fsn_inodestart : Z;
  fsn_dqs        : dfrac;         (* sb.inodestart                          *)
}.

Global Instance fstat_names_inhabited : Inhabited fstat_names :=
  populate (MkFStatNames
    (UartNames 1%positive 1%positive 1%positive 1%positive)
    (DiskNames 1%positive 1%positive 1%positive 1%positive 1%positive
               1%positive 1%positive)
    1%positive
    (mword_of_int 0) (mword_of_int 0) (mword_of_int 0)
    (MkBioNames 1%positive 1%positive 1%positive
       (fun _ => (1%positive, 1%positive)) (fun _ => 1%positive)
       (fun _ => 1%positive))
    (MkFsNames 1%positive 1%positive 1%positive)
    1%positive (MkIcNames (fun _ => 1%positive) (fun _ => 1%positive)
                          (fun _ => 1%positive))
    ∅ 0 0 (DfracOwn 1)).

Section SpecFilestat.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !kallocG Σ,
            !bioG Σ, !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ,
            !irefslotG Σ, !iregG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  (* ---- the inode arm's environment: ilock's and iunlock's ----

     CONTENT-INDEPENDENT, in [SpecFileclose.fileclose_fs_env]'s form: the
     escrow FAMILY, the sleeplock FAMILY, the inode region, the block cache,
     the disk fabric, and the region-WIDE inum geometry (quantified, exactly
     as [fileclose_ic_env]'s is, because the inum is existential in the
     reference).  It mentions neither [Cf] nor any slot, so a syscall that has
     not yet borrowed its descriptor can own it -- which is the whole point.
     The per-inode pieces come out of the reference at the call
     ([filestat_pay_carve] below). *)
  Definition filestat_fs_env (fn : fstat_names) : iProp Σ :=
    (⌜log_geom_ok (fsn_cov fn) (fsn_logstart fn)⌝ ∗
     ⌜0 <= fsn_inodestart fn⌝ ∗
     (* EVERY inum the region covers has its block inside [cov] -- the
        quantified form, since the reference names the inum existentially *)
     ⌜forall inum : mword 32,
        bv_unsigned inum < 16 * Z.of_nat icfg_nib ->
        IBLOCK inum (fsn_inodestart fn) ∈ fsn_cov fn⌝ ∗
     bio_ctx (fsn_bio fn)
       (fs_view (fsn_fs fn) (fsn_disk fn) icfg_dev (fsn_cov fn)) ∗
     (* the three persistent invariants SpecIlock v3 / SpecIunlock v3 take,
        at the FAMILY where they were per-slot *)
     itable_inv ∗
     ic_escrows (fsn_ic fn) (fsn_fs fn) (fsn_ireg fn) (fsn_cov fn)
                (fsn_logstart fn) ∗
     ireg_inv (fsn_ireg fn) (fsn_fs fn) (fsn_inodestart fn) icfg_nib ∗
     (* EVERY ENTRY'S SLEEPLOCK -- over the CHECKOUT TOKEN alone *)
     ic_sleeplocks (fsn_ic fn) ∗
     sb_inodestart ↦₄{fsn_dqs fn}
       (mword_of_int (fsn_inodestart fn) : mword 32) ∗
     (* the disk fabric *)
     dev_inv (fsn_uart fn) (fsn_disk fn) ∗
     disk_geom (fsn_disk fn) (fsn_pd fn) (fsn_pav fn) (fsn_pu fn) ∗
     is_lock (fsn_dlock fn) d_lock "virtio_disk"%string
       (disk_res (fsn_disk fn) (fsn_pd fn) (fsn_pav fn) (fsn_pu fn)) ∗
     (* ONE slot unit: ilock's bread takes it and brelse gives it back *)
     bslot (fsn_bio fn))%I.

  (* What comes back: the superblock fraction and the slot unit.  NO SHARE --
     the share never left the reference's payload, so there is nothing here
     for it to be returned through, and hence no generation to lose (which is
     what made the old [inode_shr] return ungatherable). *)
  Definition filestat_fs_out (fn : fstat_names) : iProp Σ :=
    (sb_inodestart ↦₄{fsn_dqs fn}
       (mword_of_int (fsn_inodestart fn) : mword 32) ∗
     bslot (fsn_bio fn))%I.

  (* ---- and the two, selected by the file's type ---- *)
  Definition filestat_env (fn : fstat_names) (Cf : fcontent) : iProp Σ :=
    (if decide (fstat_has_inode Cf) then filestat_fs_env fn else emp)%I.

  Definition filestat_env_out (fn : fstat_names) (Cf : fcontent) : iProp Σ :=
    (if decide (fstat_has_inode Cf) then filestat_fs_out fn else emp)%I.

  (* The type-error arm returns before ilock, so the environment must already
     contain everything the postcondition promises.  Checked here rather than
     discovered in the proof -- although in filestat, unlike fileread, the arm
     that skips the work is also the arm whose environment is [emp], so this
     only has to hold on the [decide] branch that is taken. *)
  Lemma filestat_fs_env_out fn :
    filestat_fs_env fn -∗ filestat_fs_out fn.
  Proof.
    rewrite /filestat_fs_env /filestat_fs_out.
    iIntros "(_ & _ & _ & _ & _ & _ & _ & _ & Hsb & _ & _ & _ & Hbs)".
    iFrame "Hsb Hbs".
  Qed.

  Lemma filestat_env_out_of_env fn Cf :
    filestat_env fn Cf -∗ filestat_env_out fn Cf.
  Proof.
    rewrite /filestat_env /filestat_env_out.
    case_decide; [| by iIntros "$"].
    iApply filestat_fs_env_out.
  Qed.

  (* ==================================================================== *)
  (*  THE CARVE: the per-inode pieces, out of the reference's own payload  *)
  (* ==================================================================== *)
  (* OWED CLEANUP: these three are not about filestat at all -- they are the
     file-table / icache algebra every [file.c] function that locks its fd's
     inode needs, and they belong in [FileInvDefs.v] (the carve) and
     [IcacheRef.v] (the two share laws) respectively.  They are stated here
     because fs-sysfile S4' landed filestat first and a bottom-of-tree edit
     costs a full rebuild; fileread and filewrite hoist them when they
     follow.  [ProofFilewriteParts]'s [fw_shr_*] are the slot-level twins of
     the two share laws and go with them. *)

  (* the generation-named share splits, exactly as its ∃-form does *)
  Lemma inode_shr_gen_split2 (ik : nat) (s1 s2 : Qp) (dev inum : mword 32)
      (g : gname) :
    IcacheRef.inode_shr_gen ik (s1 + s2)%Qp dev inum g ⊣⊢
    IcacheRef.inode_shr_gen ik s1 dev inum g ∗
    IcacheRef.inode_shr_gen ik s2 dev inum g.
  Proof.
    rewrite /IcacheRef.inode_shr_gen IcacheRef.inode_ident_split
            IcacheRef.live_gen_split.
    iSplit; [iIntros "[[$ $] [$ $]]" | iIntros "[[$ $] [$ $]]"].
  Qed.

  (* halving, as its OWN lemma -- durable-notes' [rewrite -(Qp.div_2 q)]
     trap: written at a call site inside the proofmode the split's evar lands
     out of [s]'s scope. *)
  Lemma inode_shr_gen_halve2 (ik : nat) (s : Qp) (dev inum : mword 32)
      (g : gname) :
    IcacheRef.inode_shr_gen ik s dev inum g ⊣⊢
    IcacheRef.inode_shr_gen ik (s/2)%Qp dev inum g ∗
    IcacheRef.inode_shr_gen ik (s/2)%Qp dev inum g.
  Proof. rewrite -inode_shr_gen_split2 Qp.div_2. reflexivity. Qed.

  (* THE REGEN.  iunlock returns the arity-preserving [IcacheRef.inode_shr]
     (its [∃ g] form), and a payload's slice is generation-NAMED, so the two
     cannot be rejoined blind.  Any other slice of the same entry pins it
     ([IcacheRef.live_gen_agree]), and the half that was NOT lent is exactly
     such a slice -- which is why the carve lends [s/2] and keeps [s/2].
     Verbatim [ProofFilewriteParts.fw_shr_regen], which is where filewrite
     already does this. *)
  Lemma inode_shr_regen2 (ik : nat) (s1 s2 : Qp) (dev inum : mword 32)
      (g : gname) :
    IcacheRef.inode_shr_gen ik s1 dev inum g -∗
    IcacheRef.inode_shr ik s2 dev inum -∗
    IcacheRef.inode_shr_gen ik (s1 + s2)%Qp dev inum g.
  Proof.
    iIntros "H1 H2".
    iEval (rewrite IcacheRef.inode_shr_gen_intro) in "H2".
    iDestruct "H2" as (g2) "H2".
    iDestruct "H1" as "[Hid1 Hlv1]". iDestruct "H2" as "[Hid2 Hlv2]".
    iDestruct (IcacheRef.live_gen_agree with "Hlv1 Hlv2") as %<-.
    rewrite inode_shr_gen_split2. iFrame.
  Qed.

  (* the per-entry escrow, out of the family -- [SpecFileclose]'s
     [ic_escrows_acc], restated here so this contract does not depend on a
     sibling contract (same OWED note as above: the home is IcacheEscrow). *)
  Lemma ic_escrows_acc2 (cn : ic_names) (γfs : fs_names) (γi : gname)
      (cov : gset Z) (logstart : Z) (ik : nat) :
    (ik < NINODE)%nat ->
    (ic_escrows cn γfs γi cov logstart -∗ ic_escrow cn γfs γi cov logstart ik
     : iProp Σ).
  Proof.
    iIntros (Hk) "H". rewrite /ic_escrows.
    assert (Hl : seq 0 NINODE !! ik = Some ik) by (rewrite lookup_seq; lia).
    iDestruct (big_sepL_lookup _ _ ik ik Hl with "H") as "$".
  Qed.

  (* THE CARVE ITSELF.  An FD_INODE / FD_DEVICE file's payload IS a share of
     its inode's reference, generation-named, parked beside the cancel token
     ([FileInvDefs.inode_pay]).  So a function that holds the descriptor's
     reference already holds everything the old, content-indexed environment
     asked its caller for: the slot, the device, the inum, the region bound
     and the share.  This hands them out and takes the share back. *)
  Lemma filestat_pay_carve (γf : gname) (k : nat) (q : Qp) (Cf : fcontent) :
    fstat_has_inode Cf ->
    file_pay γf k q Cf -∗
    ∃ (ik : nat) (inum : mword 32) (s : Qp) (g : gname),
      ⌜fc_ip Cf = ientry ik⌝ ∗ ⌜(ik < NINODE)%nat⌝ ∗
      ⌜bv_unsigned inum < 16 * Z.of_nat icfg_nib⌝ ∗
      IcacheRef.inode_shr_gen ik s icfg_dev inum g ∗
      (IcacheRef.inode_shr_gen ik s icfg_dev inum g -∗ file_pay γf k q Cf).
  Proof.
    intros Hty. iIntros "(%pn & Hpn & Hpl)".
    assert (Hnp : bool_decide (fc_type Cf = FD_PIPE) = false).
    { apply bool_decide_eq_false_2.
      destruct Hty as [Hc | Hc]; rewrite Hc; by vm_compute. }
    assert (Hyes : (bool_decide (fc_type Cf = FD_INODE)
                    || bool_decide (fc_type Cf = FD_DEVICE))%bool = true).
    { destruct Hty as [Hc | Hc]; rewrite Hc.
      - by rewrite (bool_decide_eq_true_2 (FD_INODE = FD_INODE) eq_refl).
      - by rewrite (bool_decide_eq_true_2 (FD_DEVICE = FD_DEVICE) eq_refl)
                   orb_true_r. }
    rewrite /file_payload Hnp Hyes /inode_pay.
    iDestruct "Hpl" as "(#Hci & Hown & Hs & Hwt)".
    iDestruct "Hs" as (ik inum) "(%Hipk & %Hik & %Hinb & Hshr)".
    iExists ik, inum, (q * fp_iq pn)%Qp, (fp_ig pn).
    iSplitR; [done|]. iSplitR; [done|]. iSplitR; [done|].
    (* [iExact], not [iFrame]: both sides are the same FOLDED
       [IcacheRef.inode_shr_gen] and conversion closes it, while the [Frame]
       instance search does not see through the definition. *)
    iSplitL "Hshr"; [iExact "Hshr"|].
    iIntros "Hshr". iExists pn. iFrame "Hpn".
    rewrite /file_payload Hnp Hyes /inode_pay.
    iSplitR; [iExact "Hci"|]. iSplitL "Hown"; [iExact "Hown"|].
    iSplitL "Hshr"; [iExists ik, inum; iFrame "%"; iExact "Hshr"|].
    iExact "Hwt".
  Qed.

  (* A file that carries no inode costs its stat-er nothing. *)
  Lemma filestat_env_none fn Cf :
    ~ fstat_has_inode Cf -> ⊢ filestat_env fn Cf.
  Proof. intro Ht. rewrite /filestat_env. case_decide; [contradiction | done]. Qed.

End SpecFilestat.

Definition wp_filestat_sconf_body
    `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !kallocG Σ,
      !bioG Σ, !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ,
      !irefslotG Σ, !iregG Σ}
    `{GEN : GenId} `{CID : CpuId}

    (γa : gname) (γf : gname)                    (* kalloc, the file table  *)
    (γs : list gname) (j : nat) (γlp : gname)    (* the running process     *)
    (k : nat) (q : Qp) (Cf : fcontent)           (* the borrowed reference  *)
    (fn : fstat_names)                           (* the inode arm's ghosts  *)
    (pidv : mword 32) (V : pprivate)
    (m : regfile) (K : nat) (eb : bool) (C : iProp Σ) (b : bool) (lks : gset nat) :=
  let pcE : mword 64 := mword_of_int KernelSyms.filestat in
  let pj := proc_addr j in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  (filestat_stack <= K)%nat ->
  (k < NFILE)%nat ->
  (j < NPROC)%nat ->
  γs !! j = Some γlp ->
  length γs = NPROC ->
  (* a0 = f.  a1 = addr, the user destination -- NEVER inspected here: it is
     carried in s4 from +0x0e to +0x40 and handed to copyout, whose contract
     is total in the destination (an unmapped or read-only page is its third
     failure arm, not a precondition). *)
  m !!! Regidx (mword_of_int 10 : mword 5) = fnode k ->
  (* PARKING PREMISE (hart-generic scheduler protocol): ilock sleeps. *)
  eb = true ->
  sie_cap_gpr m K b pj -∗
  (* noff = 0: everything below reaches sleep *)
  cpu_own 0%nat eb pj C b lks -∗
  kernel_text -∗ pc_is pcE -∗
  (* filestat itself never panics; ilock and iunlock do, and this is theirs *)
  panic_wp_any -∗
  (* the borrowed reference -- at an ARBITRARY fraction, and given back *)
  file_ref γf k q Cf -∗
  (* ambient: myproc runs first, and the surviving arm copies out *)
  proc_priv_core pj pidv V -∗
  kalloc_env γa None -∗
  procs_inv γs -∗
  (* ...and what the file's TYPE selects *)
  filestat_env fn Cf -∗
  (* THE CROSSING IS THE LITERAL [true], NOT [b].  filestat can SLEEP (its
     ilock does), and a park moves the hart with interrupts off, so the
     crossing has nothing to do with SIE.  Spelled [b] the two coincide at
     the only instance the [eb = true] premise admits. *)
  wp_next true pj (fun (CID : CpuId) =>
  ∀ (mf : regfile) (r : mword 64) (P' : uptd),
      ⌜callee_saved m mf⌝ -∗
      ⌜uptd_ext (pv_upt V) P'⌝ -∗
      ⌜filestat_ret r⌝ -∗
      ⌜mf !!! Regidx (mword_of_int 10 : mword 5) = r⌝ -∗
      sie_cap_gpr mf K b pj -∗
      cpu_own 0%nat eb pj C b lks -∗
      pc_is ret_tgt -∗
      file_ref γf k q Cf -∗
      proc_priv_core pj pidv (upd_upt V P') -∗
      filestat_env_out fn Cf -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type FILESTAT.
  Parameter wp_filestat_sconf :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !kallocG Σ,
             !bioG Σ, !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ,
             !irefslotG Σ, !iregG Σ}
      `{GEN : GenId} `{CID : CpuId}

      (γa : gname) (γf : gname)
      (γs : list gname) (j : nat) (γlp : gname)
      (k : nat) (q : Qp) (Cf : fcontent)
      (fn : fstat_names)
      (pidv : mword 32) (V : pprivate)
      (m : regfile) (K : nat) (eb : bool) (C : iProp Σ) (b : bool) (lks : gset nat),
      wp_filestat_sconf_body γa γf γs j γlp k q Cf fn pidv V m K eb C b lks.
End FILESTAT.
