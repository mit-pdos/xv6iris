(* SpecFilewrite.v -- the public interface of filewrite, stated independently
   of its proof.  Requires only the definitional layer and its callees' SPECS
   -- never a whole-function proof file -- so every function proof can be
   checked in parallel.

     int filewrite(struct file *f, uint64 addr, int n) {
       int r, ret = 0;
       if (f->writable == 0) return -1;
       if (f->type == FD_PIPE)   ret = pipewrite(f->pipe, addr, n);
       else if (f->type == FD_DEVICE) {
         if (f->major < 0 || f->major >= NDEV || !devsw[f->major].write)
           return -1;
         ret = devsw[f->major].write(1, addr, n);
       } else if (f->type == FD_INODE) {
         int max = ((MAXOPBLOCKS-1-1-2) / 2) * BSIZE;
         int i = 0;
         while (i < n) {
           int n1 = n - i;
           if (n1 > max) n1 = max;
           begin_op();
           ilock(f->ip);
           if ((r = writei(f->ip, 1, addr + i, f->off, n1)) > 0) f->off += r;
           iunlock(f->ip);
           end_op();
           if (r != n1) break;          (* error from writei *)
           i += r;
         }
         ret = (i == n ? n : -1);
       } else panic("filewrite");
       return ret;
     }

   308 bytes.  fileread's four arms plus a LOOP, and the loop is the whole
   difference: each iteration is its own log transaction, so [begin_op] and
   [end_op] bracket every chunk and the reservation is minted and spent
   inside the body rather than threaded across the call.

   ==== DECODE FACTS THIS CONTRACT IS STATED AGAINST ====================

   Read off the tracked dump; the four that a reader of the C would get
   wrong are recorded in claude-notes/projects/fs-sysfile.md (S3a's list):

   1. The [!writable] return at +0x00/+0x04 is BEFORE THE PROLOGUE, so its
      [ret] at +0x124 runs with sp untouched.  Nothing in the frame exists
      on that path, which is why this contract's environment must already
      contain everything the postcondition promises.
   2. [devsw[major].write] is at OFFSET 8 -- [.read] is the first of the two
      function pointers -- so the device arm's cell is [devsw + 16*mj + 8]
      and is NOT [SpecFileread.a_devsw_read].
   3. [panic("filewrite")] at +0x11e is the ELSE arm (the type is none of
      FD_PIPE / FD_DEVICE / FD_INODE), exactly like fileread's.  It is NOT a
      short-write panic: a short write [break]s the loop at +0xc0 and the
      tail at +0xf4 answers -1.
   4. [max = ((MAXOPBLOCKS-1-1-2)/2)*BSIZE = 3072], materialised TWICE
      ([lui]/[addi] into s7 and s9) at +0x42..+0x4e.

   ==== WHAT THE FD_INODE ARM NEEDS THAT FILEREAD DID NOT ===============

   (a) THE TYPE WITNESS (design fs-icache.md §17, closed by §17.6/§17.7 after
   five iterations).  The arm re-parks [IcacheEscrow.ic_loaded], whose
   [DirView.dir_ok] conjunct constrains a DIRECTORY's data bytes -- and an
   arbitrary user write into a directory breaks [dir_inums_ok].  writei
   cannot change [di_type], and the record is ilock's OUTPUT, so "not a
   directory" cannot be a premise about a caller-held record.  The real xv6
   invariant is five frames up: sys_open refuses writable directory fds.

   It crosses as a resource.  The lent share is GENERATION-NAMED
   ([IcacheRef.inode_shr_gen] at [fwn_g]); SpecIlock's postcondition hands
   back [IcacheRef.ity_shot fwn_g (di_type dn)] at that same generation
   (pinned by [live_gen_agree], with no itable fact anywhere); this contract
   carries the fd's own [ity_shot fwn_g fwn_ty] with [fwn_ty <> T_DIR];
   [IcacheRef.ity_shot_agree] joins them and [DirView.dir_ok_not_dir]
   finishes.  A generation sees AT MOST ONE FILL (§17.6), which is what makes
   that agreement mean anything.

   The witness is CONDITIONAL ON [fc_wbool Cf], exactly as
   [FileInvDefs.inode_pay] states it: an O_RDONLY directory fd is legal and
   fileread never needs the fact.  filewrite discharges the condition from
   its own [f->writable] test at +0x00 -- past that branch the bool is true,
   and it is true in the caller's [fcontent] because the content fraction is
   what the [lbu] read.

   The re-park then closes for free: [SpecWritei.wi_dinode] is
   [MkDinode (di_type dn) ...], so the flushed record's type is
   DEFINITIONALLY the fill's and every chunk re-parks with the shot it was
   handed (§17.6 constraint 8).

   (b) THE ALLOCATOR AND THE LOG.  writei calls bmap, which calls balloc, so
   the arm carries the bitmap, [sb.size], [sb.bmapstart] and balloc's printk
   credentials; and it is bracketed by begin_op/end_op, so it carries
   [log_ctx], the crash seam and the generation certificate.  The bitmap
   comes back at a set that only GREW: [used ⊆ used'] is the loop invariant,
   inherited from writei's own postcondition one chunk at a time.

   ==== THE NUMERIC PREMISES, AND THE ONE FILEREAD HAD THAT THIS DOES NOT ==

   writei's joint bound is [off + n1 < 2^31].  Here it is DISCHARGEABLE
   RATHER THAN INHERITED, and that is the chunking's doing: [n1 <= 3072] by
   construction and [off <= MAXFILE*BSIZE] by [FileOff.off_wf], so the sum is
   at most 277504 -- a closed fact.  So this contract does NOT carry
   fileread's [MAXFILE*BSIZE + n < 2^31] premise, and sys_write will be able
   to take [n] from unchecked user input where sys_read cannot.  (See
   claude-notes/design/file-table.md; this is the one place the write side is
   BETTER off than the read side.)

   [f->off] stays inside [off_wf] for the same reason from the other end:
   writei answers -1 rather than writing when [MAXFILE*BSIZE < off + n1], so
   a chunk that returns a count has [off + tot <= MAXFILE*BSIZE].

   ==== WHAT THE POSTCONDITION SAYS =====================================

   [filewrite_ret n r]: minus one, or a count between 0 and n --
   [PipeInv.pipe_rw_ret] verbatim, as fileread.  The inode arm is strictly
   inside it and in fact answers [n] or [-1] and nothing between (decode fact
   3), but stating the sharper fact would buy a caller nothing: sys_write
   returns the value unexamined, and the pipe and device arms are not sharp.

   The WRITTEN BYTES are not describable here, and that is inherited rather
   than lost: writei's range clause is about [data'], which lives inside the
   escrow's parked payload and no caller-held resource names.  The file's
   OFFSET likewise stays in the per-slot off-borrow cinv. *)
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
Require Import IcacheBoot.   (* [ic_sleeplocks]: the canonical entry-sleeplock
                                family, taken because this contract cannot know
                                WHICH entry its descriptor points at. *)
Require Import KallocInv.
Require Import UserPtTree.
Require Import KvmSpec.
Require Import ProcPtOwn.
Require Import PipeInvDefs.
Require Import FileOff ProcInv.
Require Import FileInvDefs.
Require Import BitmapInv.
Require Import KernelDataInv.
Require Import SpecPrintk.
Require Import SpecWritei.
Require Import SpecFileread.
Require Import UartTxInv.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import ProcAvail.
Import Defs.

Local Open Scope Z_scope.

(* filewrite's own frame is 12 slots ([c.addi16sp sp,sp,-96]: ra, s0, s1,
   s2..s9 saved), and its deepest callee is WRITEI again at [K_writei] = 78
   -- not consolewrite at 72, which is what it was before [K_writei] grew
   (SpecReadi.v's header traces the chain: printk's real stack need, 48, now
   dominates bmap, which dominates balloc's out-of-blocks arm, which
   dominates bmap's callers).  consolewrite's own sixteen-slot frame (a
   32-byte bounce buffer lives in it) sits under either_copyin's 56, and
   neither of its calls is made with interrupts off, so nothing of
   [IntrDefs.trap_res] is spendable there; [SpecConsolewrite.consolewrite_stack]
   has the accounting.  pipewrite (64), begin_op / end_op / ilock / iunlock
   are all below both.  A CONSTANT, not a per-arm bound: the stack a
   function may need is a property of the function (durable-notes.md). *)
Definition filewrite_stack : nat := (12 + K_writei)%nat.

(* &devsw[mj].write.  [struct devsw] is two function pointers with [read]
   FIRST, so the entry is 16 bytes and this field is at offset 8 -- which is
   what the [slli a5,a5,4] / [ld a5,8(a5)] pair at +0x6c / +0x78 computes.
   The read side is [SpecFileread.a_devsw_read]; the two must not be
   confused, and S3a's decode note 2 exists because they were. *)
Definition a_devsw_write (mj : Z) : mword 64 :=
  mword_of_int (KernelSyms.devsw + 16 * mj + 8).

(* THE CHUNK SIZE, as the two [lui]/[addi] pairs at +0x42..+0x4e materialise
   it: ((MAXOPBLOCKS-1-1-2)/2)*BSIZE with MAXOPBLOCKS = 10 and BSIZE = 1024. *)
Definition FW_MAX : Z := 3072.

Lemma fw_max_value : FW_MAX = ((Z.of_nat MAXOPBLOCKS - 1 - 1 - 2) / 2) * Z.of_nat BSIZE.
Proof. reflexivity. Qed.

(* WHAT FILEWRITE RETURNS.  [PipeInv.pipe_rw_ret]'s reading, and deliberately
   the same predicate as [SpecFileread.fileread_ret]: three of the four arms
   produce it verbatim and the inode arm is strictly inside it. *)
Definition filewrite_ret (n : Z) (r : mword 64) : Prop := pipe_rw_ret n r.

Lemma filewrite_ret_m1 (n : Z) : filewrite_ret n (mword_of_int (-1) : mword 64).
Proof. left. reflexivity. Qed.

Lemma filewrite_ret_all (n : Z) : 0 <= n -> filewrite_ret n (mword_of_int n : mword 64).
Proof. intro Hn. right. exists n. split; [reflexivity | lia]. Qed.

(* THE CHUNKING'S ARITHMETIC, in one lemma: writei's joint premise is a
   CLOSED FACT here, not an inherited obligation.  [off] is bounded by
   [FileOff.off_wf] and the chunk by the [max] the code computes, so the sum
   cannot approach 2^31 whatever the caller's [n] is.  This is why
   SpecFilewrite has no counterpart of [SpecFileread]'s
   [MAXFILE*BSIZE + n < 2^31] premise. *)
Lemma fw_chunk_joint (off n1 : nat) :
  (Z.of_nat off <= Z.of_nat MAXFILE * Z.of_nat BSIZE) ->
  (Z.of_nat n1 <= FW_MAX) ->
  Z.of_nat off + Z.of_nat n1 < 2 ^ 31.
Proof.
  unfold FW_MAX, MAXFILE, BSIZE, NDIRECT. cbn. lia.
Qed.

(* ...and the offset's own induction step, filewrite's counterpart of
   [SpecFileread.fileread_off_advance].  writei REFUSES rather than writes
   when the range would leave the file's capacity, so a chunk that returns a
   count leaves the offset inside [off_wf]. *)
Lemma fw_off_advance (off tot n1 : nat) :
  ((MAXFILE * BSIZE < off + n1)%nat -> False) ->
  (tot <= n1)%nat ->
  (off + tot <= MAXFILE * BSIZE)%nat.
Proof. intros Hle Htot. lia. Qed.

(* ---------------------------------------------------------------------- *)
(*  The ghost names and geometry the two heavy arms are indexed by          *)
(* ---------------------------------------------------------------------- *)
(* NOTHING PER-INODE IS IN HERE (fs-sysfile S4' / blocker 2's ratified
   alternative; [SpecFilestat.fstat_names] is the landed template and
   [SpecFileread.fread_names] the sibling).  NINE fields went: the itable
   slot, the inum, the lent share's fraction, its GENERATION, the recorded
   inode TYPE, the entry's two sleeplock gnames, the device and the region's
   block count.  Every one of them is something a CALLER cannot know -- a
   reference borrowed out of [ProcInv.ofile_slot] comes with its slot,
   fraction and content existentially quantified -- and every one comes out
   of the reference itself ([SpecFileread.fileread_pay_carve], which is
   [SpecFilestat.filestat_pay_carve] GROWN by the [ty] output precisely so
   that filewrite's [ity_shot] can come from the same place), or is the
   ambient cache's ([IcacheRef.icfg_dev] / [icfg_nib]), or is existential
   under the sleeplock FAMILY. *)
Record fwrite_names := MkFWriteNames {
  fwn_procs      : list gname;    (* the proc table's per-slot lock names   *)
  fwn_j          : nat;           (* the running process's index            *)
  fwn_plock      : gname;
  fwn_uart       : uart_names;
  fwn_disk       : disk_names;
  fwn_dlock      : gname;         (* virtio_disk.lock                       *)
  fwn_txlock     : gname;         (* uart tx_lock -- the DEVICE arm's        *)
  fwn_pd         : mword 64;
  fwn_pav        : mword 64;
  fwn_pu         : mword 64;
  fwn_bio        : bio_names;
  fwn_log        : log_names;     (* begin_op / end_op                      *)
  fwn_fs         : fs_names;
  fwn_ireg       : gname;         (* the inode region (InodeRegion.v)       *)
  fwn_ic         : ic_names;      (* the icache's names (IcacheEscrow.v)    *)
  fwn_pr         : gname;         (* balloc's printk credential             *)
  fwn_cov        : gset Z;
  fwn_logstart   : Z;
  fwn_inodestart : Z;
  fwn_bmapstart  : Z;             (* the bitmap, for bmap -> balloc          *)
  fwn_size       : Z;             (* sb.size                                *)
  fwn_used       : gset Z;        (* the bitmap's marked set, going IN       *)
  fwn_dqs        : dfrac;         (* sb.inodestart                          *)
  fwn_dqb        : dfrac;         (* sb.bmapstart                           *)
  fwn_dqbs       : dfrac;         (* sb.size                                *)
  (* THE DEVICE TABLE'S WRITE COLUMN, AS FUNCTIONS OF THE MAJOR -- the read
     side's story verbatim (SpecFileread.v's note): one cell covers one
     major, and a syscall cannot know which major its descriptor names. *)
  fwn_wp         : Z -> mword 64; (* devsw[mj].write                        *)
  fwn_dqv        : Z -> dfrac;    (* ...and that cell's fraction            *)
}.

(* Spelled out rather than derived, exactly as [SpecFileread.fread_names] is:
   several of these records have no [Inhabited] instance of their own and
   [bio_names] has function fields.  Nothing reads these values -- a caller
   that passes them cannot reach the arm they belong to -- so any closed term
   does. *)
Global Instance fwrite_names_inhabited : Inhabited fwrite_names :=
  populate (MkFWriteNames
    [] 0%nat 1%positive
    (UartNames 1%positive 1%positive 1%positive 1%positive)
    (DiskNames 1%positive 1%positive 1%positive 1%positive 1%positive
               1%positive 1%positive)
    1%positive 1%positive
    (mword_of_int 0) (mword_of_int 0) (mword_of_int 0)
    (MkBioNames 1%positive 1%positive 1%positive
       (fun _ => (1%positive, 1%positive)) (fun _ => 1%positive)
       (fun _ => 1%positive))
    (MkLogNames 1%positive 1%positive 1%positive 1%positive)
    (MkFsNames 1%positive 1%positive 1%positive)
    1%positive (MkIcNames (fun _ => 1%positive) (fun _ => 1%positive)
                          (fun _ => 1%positive))
    1%positive
    ∅ 0 0 0 0 ∅
    (DfracOwn 1) (DfracOwn 1) (DfracOwn 1)
    (fun _ => mword_of_int 0) (fun _ => DfracOwn 1)).

(* THE DUPLICATE [!icacheG Σ] IS GONE.  [fileG] BUNDLES [icacheG] (and the
   [icfg]), so binding both gives TWO instances and propositions that print
   identically but do not unify (durable-notes.md).  It was invisible while
   nothing here mixed the two; the carve does -- the payload's share is at
   [fileG]'s [icfg_dev].  Same edit as SpecFilestat's and SpecFileread's. *)
Section SpecFilewrite.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !kallocG Σ,
            !bioG Σ, !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ,
            !fsCrashG Σ, !irefslotG Σ, !pavG Σ, !iregG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  (* ---- the FD_DEVICE arm's environment ---- *)

  (* WHAT THE CALLEE NEEDS, as opposed to what the DISPATCH needs.  The cell
     below is how filewrite finds consolewrite; this is what consolewrite
     itself asks for (SpecConsolewrite.v) -- uartwrite's whole credential,
     the device fabric and the transmit lock.  Both are PERSISTENT, so a
     caller pays for them once and the loop carries them for free, and the
     read side's twin ([SpecFileread.fileread_dev_caps]) is one conjunct
     rather than two because consoleread never touches the UART. *)
  Definition filewrite_dev_caps (fn : fwrite_names) : iProp Σ :=
    (dev_inv (fwn_uart fn) (fwn_disk fn) ∗
     is_txlock (fwn_txlock fn) (fwn_uart fn))%I.

  Global Instance filewrite_dev_caps_persistent fn :
    Persistent (filewrite_dev_caps fn).
  Proof. apply _. Qed.

  (* ONE cell, and only when the major is in range.  The disjunction is the
     honest statement of what the kernel installs: [consoleinit] fills
     [devsw[CONSOLE]] and nothing fills any other entry, so a write slot is
     either null (and the code returns -1) or [consolewrite] (whose contract
     is ASSUMED -- LinkConsolewrite.v, the write side's twin of
     LinkConsoleread.v).  The address is [a_devsw_write], NOT
     [SpecFileread.a_devsw_read]: decode note 2. *)
  Definition filewrite_dev_env (fn : fwrite_names) (Cf : fcontent) : iProp Σ :=
    (if decide (dev_major Cf <= NDEV_max)
     then ⌜fwn_wp fn (dev_major Cf) = (zero_reg : mword 64)
           \/ fwn_wp fn (dev_major Cf)
               = (mword_of_int KernelSyms.consolewrite : mword 64)⌝ ∗
          a_devsw_write (dev_major Cf) ↦₈{fwn_dqv fn (dev_major Cf)}
            fwn_wp fn (dev_major Cf) ∗
          filewrite_dev_caps fn
     else emp)%I.

  (* it is only READ, so it comes back as it went in *)
  Definition filewrite_dev_out (fn : fwrite_names) (Cf : fcontent) : iProp Σ :=
    filewrite_dev_env fn Cf.

  (* ---- THE WHOLE COLUMN, and how one entry comes out of it ----
     [SpecFileread.fileread_devsw]'s twin at the write side, and there for the
     same reason: it is what a caller that cannot name its descriptor's major
     must own. *)
  Definition filewrite_devsw (fn : fwrite_names) : iProp Σ :=
    (filewrite_dev_caps fn ∗
     [∗ list] i ∈ seq 0 (Z.to_nat NDEV_max + 1),
       ⌜fwn_wp fn (Z.of_nat i) = (zero_reg : mword 64)
         \/ fwn_wp fn (Z.of_nat i)
             = (mword_of_int KernelSyms.consolewrite : mword 64)⌝ ∗
       a_devsw_write (Z.of_nat i) ↦₈{fwn_dqv fn (Z.of_nat i)}
         fwn_wp fn (Z.of_nat i))%I.

  Lemma filewrite_devsw_acc (fn : fwrite_names) (Cf : fcontent) :
    filewrite_devsw fn -∗
    filewrite_dev_env fn Cf ∗ (filewrite_dev_out fn Cf -∗ filewrite_devsw fn).
  Proof.
    (* THE UNFOLD ORDER MATTERS: [/filewrite_dev_out] rewrites to [filewrite_dev_env], so
       unfolding [filewrite_dev_env] FIRST leaves the out side folded and the
       closing [iExact] fails on two terms that print differently for that
       reason alone. *)
    rewrite /filewrite_dev_out /filewrite_dev_env /filewrite_devsw.
    iIntros "[#Hcaps H]".
    case_decide as Hle;
      [| iSplitR; [done | iIntros "_"; iFrame "Hcaps"; iExact "H"]].
    (* the major is a [bv_unsigned], hence non-negative, so it IS the index
       [Z.to_nat] of it names *)
    pose proof (proj1 (bv_unsigned_in_range _ (fc_major Cf))) as Hnn.
    rewrite /dev_major in Hle Hnn |- *.
    set (i := Z.to_nat (bv_unsigned (fc_major Cf))).
    assert (Hid : Z.of_nat i = bv_unsigned (fc_major Cf))
      by (rewrite /i; apply Z2Nat.id; exact Hnn).
    assert (Hlk : seq 0 (Z.to_nat NDEV_max + 1) !! i = Some i).
    { rewrite lookup_seq. split; [reflexivity|].
      rewrite /i. exact (devsw_idx_lt _ Hnn Hle). }
    (* an EXPLICIT [Phi]: underscores leave the big-op's typeclass evars
       unresolved and the destructuring pattern then fails (durable-notes.md) *)
    iDestruct (big_sepL_lookup_acc
                 (fun (_ : nat) (jj : nat) =>
                    (⌜fwn_wp fn (Z.of_nat jj) = (zero_reg : mword 64)
                      \/ fwn_wp fn (Z.of_nat jj)
                          = (mword_of_int KernelSyms.consolewrite : mword 64)⌝ ∗
                     a_devsw_write (Z.of_nat jj) ↦₈{fwn_dqv fn (Z.of_nat jj)}
                       fwn_wp fn (Z.of_nat jj))%I)
                 _ i i Hlk with "H") as "[Hone Hback]".
    iEval (rewrite Hid) in "Hone".
    iSplitL "Hone".
    { iDestruct "Hone" as "[Hp Hc]". iFrame "Hp Hc". iExact "Hcaps". }
    iIntros "(Hp & Hc & _)". iFrame "Hcaps".
    iApply "Hback". rewrite Hid. iFrame "Hp Hc".
  Qed.

  (* ---- the FD_INODE arm's environment ----------------------------------
     begin_op's, ilock's, writei's, iunlock's and end_op's, in that order.
     It is bigger than fileread's by exactly the log and the allocator, which
     is what makes this a WRITE.

     CONTENT-INDEPENDENT, in [SpecFilestat.filestat_fs_env]'s form: the
     escrow FAMILY, the sleeplock FAMILY, the off-borrow FAMILY, and the
     region-WIDE inum geometry (BOTH geometry facts quantified, since the
     inum is existential in the reference).  It names neither [Cf], nor an
     itable slot, nor an fd slot, so a syscall that has not yet borrowed its
     descriptor can own it.  The per-inode pieces -- including §17.6's type
     witness, which used to sit at the end of this bundle -- come out of the
     reference at the call ([SpecFileread.fileread_pay_carve]). *)
  Definition filewrite_fs_env (γf : gname) (fn : fwrite_names) : iProp Σ :=
    (⌜log_geom_ok (fwn_cov fn) (fwn_logstart fn)⌝ ∗
     ⌜0 <= fwn_inodestart fn⌝ ∗
     (* EVERY inum the region covers has its block inside [cov] *)
     ⌜forall inum : mword 32,
        bv_unsigned inum < 16 * Z.of_nat icfg_nib ->
        IBLOCK inum (fwn_inodestart fn) ∈ fwn_cov fn⌝ ∗
     (* ...and none of those blocks is one of the log's own slots.  writei's
        iupdate flushes the inode's block, and this is iupdate's premise,
        quantified for the same reason as the one above. *)
     ⌜forall inum : mword 32,
        bv_unsigned inum < 16 * Z.of_nat icfg_nib ->
        ~ (IBLOCK inum (fwn_inodestart fn)
             ∈ log_region_set (fwn_logstart fn))⌝ ∗
     (* the bitmap's geometry, forwarded through bmap to balloc *)
     ⌜bitmap_geom_ok (fwn_cov fn) (fwn_logstart fn) (fwn_bmapstart fn)
                     (fwn_size fn)⌝ ∗
     (* balloc's out-of-blocks arm calls the GENERAL printk path; carried as
        a hypothesis, never a functor (SpecBalloc.v's header) *)
     ⌜printk_gen_contract (fwn_pr fn) (fwn_uart fn) (fwn_disk fn)⌝ ∗
     bio_ctx (fwn_bio fn)
       (fs_view (fwn_fs fn) (fwn_disk fn) icfg_dev (fwn_cov fn)) ∗
     (* THE LOG: begin_op mints the reservation, end_op spends it, and the
        loop does one transaction PER CHUNK *)
     log_ctx (fwn_log fn) (fwn_bio fn) (fwn_fs fn) (fwn_cov fn)
             (fwn_logstart fn) icfg_dev ∗
     (* end_op's crash seam and era certificate *)
     fs_crash_seam (fwn_cov fn) (fwn_logstart fn) ∗
     gen_cert ∗
     (* balloc's two PERSISTENT printk credentials *)
     kernel_data ∗
     printk_env (fwn_pr fn) (fwn_uart fn) (fwn_disk fn) ∗
     (* THE THREE PERSISTENT ICACHE INVARIANTS SpecIlock / SpecIunlock take,
        the escrow at the FAMILY where it was per-slot *)
     itable_inv ∗
     ic_escrows (fwn_ic fn) (fwn_fs fn) (fwn_ireg fn) (fwn_cov fn)
                (fwn_logstart fn) ∗
     ireg_inv (fwn_ireg fn) (fwn_fs fn) (fwn_inodestart fn) icfg_nib ∗
     (* EVERY ENTRY'S SLEEPLOCK -- over the CHECKOUT TOKEN alone *)
     ic_sleeplocks (fwn_ic fn) ∗
     (* THE LENT SHARE AND ITS GENERATION'S TYPE WITNESS ARE NOT HERE.
        Both used to be: the generation-named share (design fs-icache.md
        §17.3, ratified §17.4) and [ity_shot] at that generation (§17.6 (5),
        ratified §17.7), the resource that carries sys_open's "no writable
        directory fd" down to the re-park.  Both are EXACTLY what
        [FileInvDefs.inode_pay] holds, in exactly those forms -- which is why
        asking a caller for them was always redundant and, once the caller is
        a syscall, unsatisfiable.  [SpecFileread.fileread_pay_carve] hands out
        the share, the generation, [ity_shot] AND the [fc_wbool] side
        condition together, and takes the share back. *)
     (* sb.inodestart (iupdate), sb.size and sb.bmapstart (bmap -> balloc) *)
     sb_inodestart ↦₄{fwn_dqs fn}
       (mword_of_int (fwn_inodestart fn) : mword 32) ∗
     sb_size ↦₄{fwn_dqbs fn} (mword_of_int (fwn_size fn) : mword 32) ∗
     sb_bmapstart ↦₄{fwn_dqb fn} (mword_of_int (fwn_bmapstart fn) : mword 32) ∗
     (* THE BITMAP itself *)
     bitmap_res (fwn_fs fn) (fwn_bmapstart fn) (fwn_cov fn) (fwn_logstart fn)
                (fwn_size fn) (fwn_used fn) ∗
     (* the disk fabric *)
     dev_inv (fwn_uart fn) (fwn_disk fn) ∗
     disk_geom (fwn_disk fn) (fwn_pd fn) (fwn_pav fn) (fwn_pu fn) ∗
     is_lock (fwn_dlock fn) d_lock "virtio_disk"%string
       (disk_res (fwn_disk fn) (fwn_pd fn) (fwn_pav fn) (fwn_pu fn)) ∗
     (* THREE slot units: writei's peak (bmap's, and its own bread held
        across either_copyin and log_write).  ilock's bread and end_op's
        commit borrow from the same three, one transaction at a time. *)
     bslots (fwn_bio fn) 3)%I.

  (* What comes back: the three superblock fields, the slot units, and the
     bitmap AT A SET THAT ONLY GREW.  [used'] is existential because the
     number of chunks -- hence of ballocs -- is not a function of anything
     the caller holds.  NO SHARE: it never left the reference's payload, so
     there is nothing here for it to be returned through, and hence no
     generation to lose (which is what made a returned [inode_shr]
     ungatherable in the first place). *)
  Definition filewrite_fs_out (fn : fwrite_names)
      (used' : gset Z) : iProp Σ :=
    (⌜fwn_used fn ⊆ used'⌝ ∗
     sb_inodestart ↦₄{fwn_dqs fn}
       (mword_of_int (fwn_inodestart fn) : mword 32) ∗
     sb_size ↦₄{fwn_dqbs fn} (mword_of_int (fwn_size fn) : mword 32) ∗
     sb_bmapstart ↦₄{fwn_dqb fn} (mword_of_int (fwn_bmapstart fn) : mword 32) ∗
     bitmap_res (fwn_fs fn) (fwn_bmapstart fn) (fwn_cov fn) (fwn_logstart fn)
                (fwn_size fn) used' ∗
     bslots (fwn_bio fn) 3)%I.

  (* ---- and the three, selected by the file's type ---- *)
  Definition filewrite_env (γf : gname)
      (fn : fwrite_names) (Cf : fcontent) : iProp Σ :=
    (if bool_decide (fc_type Cf = FD_PIPE) then emp
     else if bool_decide (fc_type Cf = FD_DEVICE) then filewrite_dev_env fn Cf
     else if bool_decide (fc_type Cf = FD_INODE)
     then filewrite_fs_env γf fn
     else emp)%I.

  Definition filewrite_env_out (fn : fwrite_names) (Cf : fcontent)
      (used' : gset Z) : iProp Σ :=
    (if bool_decide (fc_type Cf = FD_PIPE) then emp
     else if bool_decide (fc_type Cf = FD_DEVICE) then filewrite_dev_out fn Cf
     else if bool_decide (fc_type Cf = FD_INODE)
     then filewrite_fs_out fn used'
     else emp)%I.

  (* THE EARLY RETURN'S OBLIGATION, checked here rather than discovered in
     the proof: [f->writable == 0] returns BEFORE THE PROLOGUE (decode note
     1) and before the type is ever tested, so the environment must already
     contain everything the postcondition promises -- at [used' = fwn_used],
     the set nothing has touched. *)
  Lemma filewrite_fs_env_out γf fn :
    filewrite_fs_env γf fn -∗ filewrite_fs_out fn (fwn_used fn).
  Proof.
    rewrite /filewrite_fs_env /filewrite_fs_out.
    iIntros "(_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
              Hsbi & Hsbs & Hsbb & Hbits & _ & _ & _ & Hbsl)".
    iFrame "Hsbi Hsbs Hsbb Hbits Hbsl". iPureIntro. reflexivity.
  Qed.

  Lemma filewrite_env_out_of_env γf fn Cf :
    filewrite_env γf fn Cf -∗ filewrite_env_out fn Cf (fwn_used fn).
  Proof.
    rewrite /filewrite_env /filewrite_env_out.
    case_bool_decide; [by iIntros "$"|].
    case_bool_decide; [by iIntros "$"|].
    case_bool_decide; [|by iIntros "$"].
    iApply filewrite_fs_env_out.
  Qed.

  (* A file that is neither a pipe, nor a device, nor an inode costs its
     writer nothing -- the arm is [panic] at +0x11e (decode note 3), and
     [panic_wp_any] closes it. *)
  Lemma filewrite_env_none γf fn Cf :
    fc_type Cf = FD_NONE -> ⊢ filewrite_env γf fn Cf.
  Proof.
    intro Ht. rewrite /filewrite_env Ht.
    rewrite bool_decide_eq_false_2; [|by vm_compute].
    rewrite bool_decide_eq_false_2; [|by vm_compute].
    rewrite bool_decide_eq_false_2; [|by vm_compute].
    done.
  Qed.

End SpecFilewrite.

Definition wp_filewrite_sconf_body
    `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !kallocG Σ,
      !bioG Σ, !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ,
      !fsCrashG Σ, !irefslotG Σ, !pavG Σ, !iregG Σ}
    `{GEN : GenId} `{CID : CpuId}

    (γa : gname) (γf : gname)                    (* kalloc, the file table  *)
    (γs : list gname) (j : nat) (γlp : gname)    (* the running process     *)
    (k : nat) (q : Qp) (Cf : fcontent)           (* the borrowed reference  *)
    (fn : fwrite_names)                          (* the heavy arms' ghosts  *)
    (pidv : mword 32) (V : pprivate)
    (m : regfile) (K : nat) (eb : bool) (n : Z) (b : bool) (lks : gset string) :=
  let pcE : mword 64 := mword_of_int KernelSyms.filewrite in
  let pj := proc_addr j in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  (filewrite_stack <= K)%nat ->
  (k < NFILE)%nat ->
  (j < NPROC)%nat ->
  γs !! j = Some γlp ->
  length γs = NPROC ->
  (* the ghost record's process fields ARE the running one: the fs arm's
     callees are all indexed by [j], and the record carries it so that the
     environment can be stated without them *)
  fwn_j fn = j ->
  fwn_procs fn = γs ->
  (* a0 = f, a1 = addr (the user source, never inspected here), a2 = n *)
  m !!! Regidx (mword_of_int 10 : mword 5) = fnode k ->
  m !!! Regidx (mword_of_int 12 : mword 5) = (mword_of_int n : mword 64) ->
  (* THE COUNT.  An int, and non-negative because it is a write length.
     NOTE what is NOT here: fileread's [MAXFILE*BSIZE + n < 2^31].  The
     chunking makes writei's joint premise a closed fact (see the header and
     [fw_chunk_joint]), which is why sys_write will be able to take [n]
     straight from user input. *)
  0 <= n < 2 ^ 31 ->
  (* PARKING PREMISE (hart-generic scheduler protocol): every arm sleeps. *)
  eb = true ->
  (* filewrite's FD_INODE arm is the whole cone: begin_op/end_op ("log", 3),
     ilock ("bcache", 4), iunlock ("sleep lock", 6) -- "log" is the lowest,
     so one premise there covers the whole cone via [locks_below_mono]. *)
  locks_below lks "log" ->
  sie_cap_gpr m K b pj -∗
  (* noff = 0: everything below reaches sleep *)
  cpu_own 0%nat eb pj b lks -∗
  kernel_text -∗ pc_is pcE -∗
  panic_wp_any -∗
  (* the borrowed reference -- at an ARBITRARY fraction, and given back *)
  file_ref γf k q Cf -∗
  (* ambient, because three of the four arms copy FROM user memory *)
  proc_priv_core pj pidv V -∗
  kalloc_env γa None -∗
  procs_inv γs -∗
  (* ...and what the file's TYPE selects *)
  filewrite_env γf fn Cf -∗
  (* THE CROSSING IS [true], NOT [b].  Every arm of this function parks, and
     the porting guide's rule is that a PARKING function's [wp_next] index is
     [true] unconditionally -- a swtch moves the hart whatever SIE was doing.
     The [eb = true] premise above plus [cpu_own_eb_agree] at level 0 forces
     [b = true] at the only constructible instance, so this is not a change of
     strength today; it is the spelling the eb-generic sweep needs. *)
  wp_next true pj (fun (CID : CpuId) =>
  ∀ (mf : regfile) (r : mword 64) (P' : uptd) (used' : gset Z),
      ⌜callee_saved m mf⌝ -∗
      ⌜uptd_ext (pv_upt V) P'⌝ -∗
      ⌜filewrite_ret n r⌝ -∗
      ⌜mf !!! Regidx (mword_of_int 10 : mword 5) = r⌝ -∗
      sie_cap_gpr mf K b pj -∗
      cpu_own 0%nat eb pj b lks -∗
      pc_is ret_tgt -∗
      file_ref γf k q Cf -∗
      proc_priv_core pj pidv (upd_upt V P') -∗
      filewrite_env_out fn Cf used' -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type FILEWRITE.
  Parameter wp_filewrite_sconf :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !kallocG Σ,
             !bioG Σ, !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ,
             !fsCrashG Σ, !irefslotG Σ, !pavG Σ, !iregG Σ}
      `{GEN : GenId} `{CID : CpuId}

      (γa : gname) (γf : gname)
      (γs : list gname) (j : nat) (γlp : gname)
      (k : nat) (q : Qp) (Cf : fcontent)
      (fn : fwrite_names)
      (pidv : mword 32) (V : pprivate)
      (m : regfile) (K : nat) (eb : bool) (n : Z) (b : bool) (lks : gset string),
      wp_filewrite_sconf_body γa γf γs j γlp k q Cf fn pidv V m K eb n b lks.
End FILEWRITE.
