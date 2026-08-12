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
   OFFSET likewise stays in [FileOff.off_inv]. *)
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
Require Import DirView.
Require Import IrefSlots.
Require Import IcacheInv.
Require Import IcacheEscrow.
Require Import KallocInv.
Require Import UserPtTree.
Require Import KvmSpec.
Require Import ProcPtOwn.
Require Import PipeInv.
Require Import FileInv FileOff ProcInv.
Require Import BitmapInv.
Require Import KernelDataInv.
Require Import SpecPrintkGen.
Require Import SpecWritei.
Require Import SpecFileread.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Import Defs.

Local Open Scope Z_scope.

(* filewrite's own frame is 12 slots ([c.addi16sp sp,sp,-96]: ra, s0, s1,
   s2..s9 saved), and its deepest callee is writei.  The others are smaller:
   pipewrite and consolewrite 62, begin_op / end_op / ilock / iunlock all far
   below.  A CONSTANT, not a per-arm bound: the stack a function may need is a
   property of the function (durable-notes.md). *)
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
Record fwrite_names := MkFWriteNames {
  fwn_procs      : list gname;    (* the proc table's per-slot lock names   *)
  fwn_j          : nat;           (* the running process's index            *)
  fwn_plock      : gname;
  fwn_uart       : uart_names;
  fwn_disk       : disk_names;
  fwn_dlock      : gname;         (* virtio_disk.lock                       *)
  fwn_pd         : mword 64;
  fwn_pav        : mword 64;
  fwn_pu         : mword 64;
  fwn_bio        : bio_names;
  fwn_log        : log_names;     (* begin_op / end_op                      *)
  fwn_fs         : fs_names;
  fwn_ireg       : gname;         (* the inode region (InodeRegion.v)       *)
  fwn_ic         : ic_names;      (* the icache's names (IcacheEscrow.v)    *)
  fwn_ilk        : gname;         (* ip->lock's inner spinlock              *)
  fwn_islk       : gname;         (* ip->lock's holder token                *)
  fwn_pr         : gname;         (* balloc's printk credential             *)
  fwn_cov        : gset Z;
  fwn_logstart   : Z;
  fwn_inodestart : Z;
  fwn_bmapstart  : Z;             (* the bitmap, for bmap -> balloc          *)
  fwn_size       : Z;             (* sb.size                                *)
  fwn_dev        : mword 32;
  fwn_inum       : mword 32;
  fwn_nib        : nat;           (* the inode region's block count         *)
  fwn_ik         : nat;           (* the itable SLOT this inode is           *)
  fwn_s          : Qp;            (* the LENT SHARE's fraction (SpecIlock v3)*)
  fwn_g          : gname;         (* ...and the GENERATION it names (§17.6)  *)
  fwn_ty         : bv 16;         (* the fd's recorded inode type (§17.6)    *)
  fwn_used       : gset Z;        (* the bitmap's marked set, going IN       *)
  fwn_dqs        : dfrac;         (* sb.inodestart                          *)
  fwn_dqb        : dfrac;         (* sb.bmapstart                           *)
  fwn_dqbs       : dfrac;         (* sb.size                                *)
  fwn_wp         : mword 64;      (* devsw[major].write                     *)
  fwn_dqv        : dfrac;         (* ...and that cell's fraction            *)
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
    1%positive
    (mword_of_int 0) (mword_of_int 0) (mword_of_int 0)
    (MkBioNames 1%positive 1%positive 1%positive
       (fun _ => (1%positive, 1%positive)) (fun _ => 1%positive)
       (fun _ => 1%positive))
    (MkLogNames 1%positive 1%positive)
    (MkFsNames 1%positive 1%positive 1%positive)
    1%positive (MkIcNames (fun _ => 1%positive) (fun _ => 1%positive)
                          (fun _ => 1%positive))
    1%positive 1%positive 1%positive
    ∅ 0 0 0 0 (mword_of_int 0) (mword_of_int 0) 0%nat 0%nat 1%Qp
    1%positive (bv_0 16) ∅
    (DfracOwn 1) (DfracOwn 1) (DfracOwn 1)
    (mword_of_int 0) (DfracOwn 1)).

Section SpecFilewrite.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !kallocG Σ,
            !bioG Σ, !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ,
            !fsCrashG Σ, !icacheG Σ, !irefslotG Σ, !iregG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  (* ---- the FD_DEVICE arm's environment ---- *)

  (* ONE cell, and only when the major is in range.  The disjunction is the
     honest statement of what the kernel installs: [consoleinit] fills
     [devsw[CONSOLE]] and nothing fills any other entry, so a write slot is
     either null (and the code returns -1) or [consolewrite] (whose contract
     is ASSUMED -- LinkConsolewrite.v, the write side's twin of
     LinkConsoleread.v).  The address is [a_devsw_write], NOT
     [SpecFileread.a_devsw_read]: decode note 2. *)
  Definition filewrite_dev_env (fn : fwrite_names) (Cf : fcontent) : iProp Σ :=
    (if decide (dev_major Cf <= NDEV_max)
     then ⌜fwn_wp fn = (zero_reg : mword 64)
           \/ fwn_wp fn = (mword_of_int KernelSyms.consolewrite : mword 64)⌝ ∗
          a_devsw_write (dev_major Cf) ↦₈{fwn_dqv fn} fwn_wp fn
     else emp)%I.

  (* it is only READ, so it comes back as it went in *)
  Definition filewrite_dev_out (fn : fwrite_names) (Cf : fcontent) : iProp Σ :=
    filewrite_dev_env fn Cf.

  (* ---- the FD_INODE arm's environment ----------------------------------
     begin_op's, ilock's, writei's, iunlock's and end_op's, in that order,
     with §17.6's type witness at the end.  It is bigger than fileread's by
     exactly the log and the allocator, which is what makes this a WRITE. *)
  Definition filewrite_fs_env (γa : gname) (γf : gname) (k : nat)
      (fn : fwrite_names) (Cf : fcontent) : iProp Σ :=
    (⌜log_geom_ok (fwn_cov fn) (fwn_logstart fn)⌝ ∗
     ⌜0 <= fwn_inodestart fn⌝ ∗
     ⌜IBLOCK (fwn_inum fn) (fwn_inodestart fn) ∈ fwn_cov fn⌝ ∗
     (* writei's iupdate flushes this inode's own block, which must NOT be
        one of the log's own slots -- iupdate's premise, verbatim *)
     ⌜~ (IBLOCK (fwn_inum fn) (fwn_inodestart fn)
           ∈ log_region_set (fwn_logstart fn))⌝ ∗
     (* the inum is inside the inode region: [ireg_read]'s premise *)
     ⌜bv_unsigned (fwn_inum fn) < 16 * Z.of_nat (fwn_nib fn)⌝ ∗
     (* the bitmap's geometry, forwarded through bmap to balloc *)
     ⌜bitmap_geom_ok (fwn_cov fn) (fwn_logstart fn) (fwn_bmapstart fn)
                     (fwn_size fn)⌝ ∗
     (* balloc's out-of-blocks arm calls the GENERAL printk path; carried as
        a hypothesis, never a functor (SpecBalloc.v's header) *)
     ⌜printk_gen_contract (fwn_pr fn) (fwn_uart fn) (fwn_disk fn)⌝ ∗
     (* THE INODE IS ITABLE SLOT [fwn_ik fn] -- what refutes ilock's and
        iunlock's null test outright ([IcacheRef.ientry_unsigned]) *)
     ⌜fc_ip Cf = ientry (fwn_ik fn)⌝ ∗
     ⌜(fwn_ik fn < NINODE)%nat⌝ ∗
     (* THE OFF-BORROW INVARIANT for this slot: [f->off] is not a content
        field, and its [off_wf] bound is what makes writei's joint premise
        closed (see the header). *)
     off_inv γf k ∗
     bio_ctx (fwn_bio fn)
       (fs_view (fwn_fs fn) (fwn_disk fn) (fwn_dev fn) (fwn_cov fn)) ∗
     (* THE LOG: begin_op mints the reservation, end_op spends it, and the
        loop does one transaction PER CHUNK *)
     log_ctx (fwn_log fn) (fwn_bio fn) (fwn_fs fn) (fwn_cov fn)
             (fwn_logstart fn) (fwn_dev fn) ∗
     (* end_op's crash seam and era certificate *)
     fs_crash_seam (fwn_cov fn) (fwn_logstart fn) ∗
     gen_cert ∗
     (* balloc's two PERSISTENT printk credentials *)
     kernel_data ∗
     printk_env (fwn_pr fn) (fwn_uart fn) (fwn_disk fn) ∗
     (* THE THREE PERSISTENT ICACHE INVARIANTS SpecIlock / SpecIunlock take *)
     itable_inv ∗
     ic_escrow (fwn_ic fn) (fwn_fs fn) (fwn_ireg fn) (fwn_cov fn)
               (fwn_logstart fn) (fwn_ik fn) ∗
     ireg_inv (fwn_ireg fn) (fwn_fs fn) (fwn_inodestart fn) (fwn_nib fn) ∗
     (* THE ENTRY'S SLEEPLOCK -- over the CHECKOUT TOKEN alone *)
     is_sleeplock (fwn_ilk fn) (fwn_islk fn) (i_lock (fc_ip Cf)) "inode"%string
       (ic_tok (fwn_ic fn) (fwn_ik fn)) ∗
     (* THE LENT SHARE, GENERATION-NAMED (design fs-icache.md §17.3, ratified
        §17.4).  fileread takes the arity-preserving [inode_shr]; filewrite
        cannot, because SpecIlock's type witness is stated at the CALLER'S
        generation and a caller that has forgotten which generation its slice
        names cannot join the two shots.  A holder moves between the two
        forms with one [IcacheRef.inode_shr_gen_intro]. *)
     IcacheRef.inode_shr_gen (fwn_ik fn) (fwn_s fn)
       (fwn_dev fn) (fwn_inum fn) (fwn_g fn) ∗
     (* ...AND THAT GENERATION'S TYPE WITNESS (design §17.6 (5), ratified
        §17.7).  This is the resource that carries sys_open's "no writable
        directory fd" down to the re-park; see the header.  It is exactly
        what [FileInvDefs.inode_pay] holds, in exactly that conditional form
        -- so a caller holding the fd's payload owes nothing new. *)
     IcacheRef.ity_shot (fwn_g fn) (fwn_ty fn) ∗
     ⌜fc_wbool Cf = true -> bv_unsigned (fwn_ty fn) <> T_DIR_z⌝ ∗
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

  (* What comes back: THE SAME SHARE at the same fraction and the same
     generation (the checkout descriptor pins the fraction, §14.8; the
     generation cannot move while this share exists, §17.6), the three
     superblock fields, the slot units, and the bitmap AT A SET THAT ONLY
     GREW.  [used'] is existential because the number of chunks -- hence of
     ballocs -- is not a function of anything the caller holds. *)
  Definition filewrite_fs_out (fn : fwrite_names) (Cf : fcontent)
      (used' : gset Z) : iProp Σ :=
    (⌜fwn_used fn ⊆ used'⌝ ∗
     IcacheRef.inode_shr_gen (fwn_ik fn) (fwn_s fn)
       (fwn_dev fn) (fwn_inum fn) (fwn_g fn) ∗
     sb_inodestart ↦₄{fwn_dqs fn}
       (mword_of_int (fwn_inodestart fn) : mword 32) ∗
     sb_size ↦₄{fwn_dqbs fn} (mword_of_int (fwn_size fn) : mword 32) ∗
     sb_bmapstart ↦₄{fwn_dqb fn} (mword_of_int (fwn_bmapstart fn) : mword 32) ∗
     bitmap_res (fwn_fs fn) (fwn_bmapstart fn) (fwn_cov fn) (fwn_logstart fn)
                (fwn_size fn) used' ∗
     bslots (fwn_bio fn) 3)%I.

  (* ---- and the three, selected by the file's type ---- *)
  Definition filewrite_env (γa : gname) (γf : gname) (k : nat)
      (fn : fwrite_names) (Cf : fcontent) : iProp Σ :=
    (if bool_decide (fc_type Cf = FD_PIPE) then emp
     else if bool_decide (fc_type Cf = FD_DEVICE) then filewrite_dev_env fn Cf
     else if bool_decide (fc_type Cf = FD_INODE)
     then filewrite_fs_env γa γf k fn Cf
     else emp)%I.

  Definition filewrite_env_out (fn : fwrite_names) (Cf : fcontent)
      (used' : gset Z) : iProp Σ :=
    (if bool_decide (fc_type Cf = FD_PIPE) then emp
     else if bool_decide (fc_type Cf = FD_DEVICE) then filewrite_dev_out fn Cf
     else if bool_decide (fc_type Cf = FD_INODE)
     then filewrite_fs_out fn Cf used'
     else emp)%I.

  (* THE EARLY RETURN'S OBLIGATION, checked here rather than discovered in
     the proof: [f->writable == 0] returns BEFORE THE PROLOGUE (decode note
     1) and before the type is ever tested, so the environment must already
     contain everything the postcondition promises -- at [used' = fwn_used],
     the set nothing has touched. *)
  Lemma filewrite_fs_env_out γa γf k fn Cf :
    filewrite_fs_env γa γf k fn Cf -∗ filewrite_fs_out fn Cf (fwn_used fn).
  Proof.
    rewrite /filewrite_fs_env /filewrite_fs_out.
    iIntros "(_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
              _ & _ & _ & _ & Hshr & _ & _ & Hsbi & Hsbs & Hsbb & Hbits &
              _ & _ & _ & Hbsl)".
    iFrame "Hshr Hsbi Hsbs Hsbb Hbits Hbsl". iPureIntro. reflexivity.
  Qed.

  Lemma filewrite_env_out_of_env γa γf k fn Cf :
    filewrite_env γa γf k fn Cf -∗ filewrite_env_out fn Cf (fwn_used fn).
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
  Lemma filewrite_env_none γa γf k fn Cf :
    fc_type Cf = FD_NONE -> ⊢ filewrite_env γa γf k fn Cf.
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
      !fsCrashG Σ, !icacheG Σ, !irefslotG Σ, !iregG Σ}
    `{GEN : GenId} `{CID : CpuId}

    (γa : gname) (γf : gname)                    (* kalloc, the file table  *)
    (γs : list gname) (j : nat) (γlp : gname)    (* the running process     *)
    (k : nat) (q : Qp) (Cf : fcontent)           (* the borrowed reference  *)
    (fn : fwrite_names)                          (* the heavy arms' ghosts  *)
    (pidv : mword 32) (V : pprivate)
    (m : regfile) (K : nat) (eb : bool) (C : iProp Σ) (n : Z) (b : bool) :=
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
  sie_cap_gpr m K b pj -∗
  (* noff = 0: everything below reaches sleep *)
  cpu_own 0%nat eb pj C b -∗
  kernel_text -∗ pc_is pcE -∗
  panic_wp_any -∗
  (* the borrowed reference -- at an ARBITRARY fraction, and given back *)
  file_ref γf k q Cf -∗
  (* ambient, because three of the four arms copy FROM user memory *)
  proc_priv γf pj pidv V -∗
  kalloc_env γa None -∗
  procs_inv γs -∗
  (* ...and what the file's TYPE selects *)
  filewrite_env γa γf k fn Cf -∗
  wp_next b pj (fun (CID : CpuId) =>
  ∀ (mf : regfile) (r : mword 64) (P' : uptd) (used' : gset Z),
      ⌜callee_saved m mf⌝ -∗
      ⌜uptd_ext (pv_upt V) P'⌝ -∗
      ⌜filewrite_ret n r⌝ -∗
      ⌜mf !!! Regidx (mword_of_int 10 : mword 5) = r⌝ -∗
      sie_cap_gpr mf K b pj -∗
      cpu_own 0%nat eb pj C b -∗
      pc_is ret_tgt -∗
      file_ref γf k q Cf -∗
      proc_priv γf pj pidv (upd_upt V P') -∗
      filewrite_env_out fn Cf used' -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type FILEWRITE.
  Parameter wp_filewrite_sconf :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !kallocG Σ,
             !bioG Σ, !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ,
             !fsCrashG Σ, !icacheG Σ, !irefslotG Σ, !iregG Σ}
      `{GEN : GenId} `{CID : CpuId}

      (γa : gname) (γf : gname)
      (γs : list gname) (j : nat) (γlp : gname)
      (k : nat) (q : Qp) (Cf : fcontent)
      (fn : fwrite_names)
      (pidv : mword 32) (V : pprivate)
      (m : regfile) (K : nat) (eb : bool) (C : iProp Σ) (n : Z) (b : bool),
      wp_filewrite_sconf_body γa γf γs j γlp k q Cf fn pidv V m K eb C n b.
End FILEWRITE.
