(* SpecFileread.v -- the public interface of fileread, stated independently of
   its proof.  Requires only the definitional layer and its callees' SPECS --
   never a whole-function proof file -- so every function proof can be checked
   in parallel.

     int fileread(struct file *f, uint64 addr, int n) {
       int r = 0;
       if (f->readable == 0) return -1;
       if (f->type == FD_PIPE) r = piperead(f->pipe, addr, n);
       else if (f->type == FD_DEVICE) {
         if (f->major < 0 || f->major >= NDEV || !devsw[f->major].read) return -1;
         r = devsw[f->major].read(1, addr, n);
       } else if (f->type == FD_INODE) {
         ilock(f->ip);
         if ((r = readi(f->ip, 1, addr, f->off, n)) > 0) f->off += r;
         iunlock(f->ip);
       } else panic("fileread");
       return r;
     }

   196 bytes.  FOUR arms plus two early returns, and every one of them ends
   at the same epilogue (+0x58), which is why the register story is uniform
   and the postcondition is a single disjunction on the return value.

   ==== THE REFERENCE, AND WHAT IT ALREADY CARRIES ======================

   fileread takes [file_ref γf k q Cf] at an ARBITRARY q -- it is a borrower,
   not a reference holder: [SpecArgfd]'s caller lends it out of the
   (thread-local) fd table for the duration and takes it back.  It gives the
   reference back unchanged.

   The load-bearing consequence of the payload link (design/file-table.md) is
   that fileread needs NO ghost state to tell a pipe from an inode.  The
   branch at +0x1e reads [f->type] out of the reference's own content
   fraction, so the loaded word IS [fc_type Cf]; the branch being taken is
   therefore the COQ fact [fc_type Cf = FD_PIPE], and [FileInv.file_payload]
   -- a function of the content -- then reduces to the pipe end that piperead
   wants.  The "what kind of thing a descriptor names" ghost state that
   design/file-table.md defers is a problem for fileread's CALLERS, which
   must decide what to own before the call; fileread itself learns the type
   by reading it.

   ==== THE ENVIRONMENT, INDEXED BY THE TYPE ============================

   SpecFileclose.v's shape, for the same reason: what a caller must own
   depends on which arm the type selects, and the union would make a caller
   reading a pipe own a file system.

   * FD_PIPE   -> NOTHING.  piperead's whole credential ([is_pipe] and a
                  share of the read end) rides inside the reference; the
                  process block, the kalloc environment and the
                  running-thread bundle are ambient (below).
   * FD_DEVICE -> the [devsw[major].read] slot, and the fact that it is
                  either null or the console's.  Only when the major is IN
                  RANGE: the bounds test at +0x7e returns -1 before the table
                  is ever indexed, so a caller with an out-of-range major
                  owes nothing.
   * FD_INODE  -> ilock's, readi's and iunlock's: the icache seam, the block
                  cache and disk fabric, and the off-borrow invariant.
   * anything else -> nothing; the arm is [panic], closed by [panic_wp_any].

   ==== THE FS ENVIRONMENT IS CONTENT-INDEPENDENT (fs-sysfile S4') =======

   [fileread_fs_env] names NEITHER the file's content NOR its descriptor
   slot: it is [SpecFilestat.filestat_fs_env]'s form (which is
   [SpecFileclose.fileclose_fs_env]'s), plus the off-borrow FAMILY.  That is
   what makes it ownable by a SYSCALL, which is the whole point -- a
   descriptor borrowed out of [ProcInv.ofile_slot] comes with its slot, its
   fraction and its content existentially quantified, so a caller can supply
   nothing that mentions any of them.

   Everything per-inode that the old, content-indexed form asked its caller
   for -- the itable slot, the inum, the device, the region bound and the
   lent SHARE -- comes out of the reference itself: [FileInvDefs.inode_pay]
   carries [IcacheRef.inode_shr_held_gen (fc_ip Cf) (q * Q) g], which names
   the slot, the device and the inum and IS the share ilock wants.
   [fileread_pay_carve] below hands them out and takes the share back; the
   per-slot escrow and sleeplock then come out of the two FAMILIES
   ([ic_escrows], [IcacheBoot.ic_sleeplocks]) at the slot the payload named,
   and the off-borrow CINV comes out of the SAME carve, since it too rides
   the payload ([FileInvDefs.off_hold]).  The postcondition carries no share at all, so nothing is
   left for the generation to be lost through
   ([SpecIunlock] returns the arity-preserving [inode_shr]; the LEND-HALF /
   KEEP-HALF discipline is what re-pins it -- [inode_shr_regen2]).

   ==== WHAT IS AMBIENT RATHER THAN PER-ARM =============================

   THREE of the four arms copy into user memory, so [proc_priv], the kalloc
   environment and the running-thread bundle are premises of the contract
   proper, not of an arm.  That is not a weakening: every caller of fileread
   is a syscall and holds all of them already.  Only the two -1 returns touch
   none of it, and they hand it all straight back.

   ==== WHAT THE POSTCONDITION CAN SAY, AND WHY IT SAYS NO MORE =========

   [fileread_ret n r]: minus one, or a count between 0 and n.  That is
   [PipeInv.pipe_rw_ret] verbatim, and it is what all four arms produce.

   It is worth being explicit that the DELIVERED BYTES are not describable
   here, and that this is inherited rather than lost.  readi's postcondition
   describes the destination bytes only on its KERNEL arm; on the user arm --
   the one fileread takes, [a1 = 1] at +0x3a -- it says only that the process
   block comes back at an EXTENDED page table ([uptd_ext]).  piperead's and
   consoleread's user arms say the same.  So there is nothing about file
   content for fileread to pass on, and in particular the file's OFFSET,
   which the borrow protocol keeps inside the per-slot invariant and which no
   caller-held resource records, never has to appear.

   ==== THE OFFSET, AND THE ONE PREMISE IT FORCES =======================

   [f->off] is not a content field: it lives in a per-slot CANCELLABLE
   invariant ([FileInvDefs.off_cinv]) and is BORROWED across the readi call
   under [ip->lock] (design/file-table.md).  fileread is the whole reason
   that protocol exists.  Two consequences for this contract:

   * the environment carries NOTHING about the offset.  The invariant's
     assertion and the fraction that opens it ride the descriptor's own
     payload ([FileInvDefs.off_hold]) and come out of
     [fileread_pay_carve] -- a fixed persistent FAMILY cannot exist, because
     the cinv is minted afresh at every open (R-open-1b).  The value is
     existential in the invariant, and the invariant's [off_wf] bound is what
     makes it usable;
   * readi's joint numeric premise [off + n < 2^32] has to be discharged from
     a bound on [n] ALONE, because nothing in memory bounds a freshly loaded
     offset.  Hence [MAXFILE * BSIZE + n < 2^31] below -- which is STRONGER
     THAN READI NEEDS: readi takes both uints at the full 32-bit range, so
     [off <= MAXFILE*BSIZE] leaves only [n < 2^32 - 274432], and the
     [n < 2^31] this contract wants anyway (piperead's and consoleread's
     [int] contracts, through [fr_n_range]) covers it.  Restating this
     premise as [0 <= n < 2^31] is what retires the debt sys_read inherits,
     and it is mechanical: three uses in ProofFileread.v, one of them
     readi's.  See claude-notes/design/file-table.md, "The value bound is
     load-bearing". *)
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
Require Import DinodeEnc.
Require Import InodeInv.
Require Import InodeRegion.
Require Import DirView.      (* [T_DIR_z]: the carve's non-directory witness,
                                which is [FileInvDefs.inode_pay]'s own clause.
                                FileInvDefs imports DirView without exporting
                                it, so naming the constant needs this line;
                                the build cone is unchanged. *)
Require Import IrefSlots.
Require Import IcacheInv.
Require Import IcacheEscrow.
Require Import IcacheBoot.   (* [ic_sleeplocks]: the canonical entry-sleeplock
                                family -- a contract that cannot know WHICH
                                entry its descriptor points at takes the
                                family, exactly as SpecFilestat does. *)
Require Import KallocInv.
Require Import UserPtTree.
Require Import KvmSpec.
Require Import ProcPtOwn.
Require Import PipeInvDefs.
Require Import ProcInv.
Require Import ConsoleInv.
Require Import FileInvDefs.
Require Import SpecReadi.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import ProcAvail.
Import Defs.

Local Open Scope Z_scope.

(* fileread's own frame is 6 slots ([addi sp,sp,-48]: ra, s0..s3 saved, one
   slot unused), and its deepest callee is readi.  The others are smaller:
   piperead and consoleread 62, ilock 44, iunlock 26.  A CONSTANT, not a
   per-arm bound: the stack a function may need is a property of the function
   (durable-notes.md). *)
Notation fileread_stack := ((6 + K_readi)%nat) (only parsing).
(* NDEV, as the bounds test reads it: [bltu a4,a3] with a4 = 9 against the
   ZERO-EXTENDED 16-bit major, so "in range" is exactly [major <= 9] and a
   negative [short] is caught by the zero extension rather than by a signed
   test.  (The C says [f->major < 0 || f->major >= NDEV]; gcc merged the two
   into one unsigned compare.) *)
Definition NDEV_max : Z := 9.

Definition dev_major (Cf : fcontent) : Z := bv_unsigned (fc_major Cf).

(* THE COLUMN INDEX, over plain [Z].  Stated here, outside every section and
   with no [mword] anywhere, because [lia] answers "Cannot find witness" the
   moment an [mword] is merely IN CONTEXT (durable-notes.md) -- and the
   accessor below has [fc_major Cf : mword 16] in context by construction. *)
Lemma devsw_idx_lt (z : Z) :
  0 <= z -> z <= NDEV_max -> (Z.to_nat z < Z.to_nat NDEV_max + 1)%nat.
Proof. unfold NDEV_max. lia. Qed.

(* &devsw[mj].read.  [struct devsw] is two function pointers, [read] first,
   so the entry is 16 bytes and the field is at offset 0 -- which is what the
   [slli a5,a5,4] / [ld a5,0(a5)] pair at +0x82 / +0x8e computes. *)
Definition a_devsw_read (mj : Z) : mword 64 :=
  mword_of_int (KernelSyms.devsw + 16 * mj).

(* WHAT FILEREAD RETURNS.  [PipeInv.pipe_rw_ret]'s reading, and deliberately
   the same predicate: three of the four arms produce it verbatim and the
   fourth (readi) is strictly inside it. *)
Definition fileread_ret (n : Z) (r : mword 64) : Prop := pipe_rw_ret n r.

Lemma fileread_ret_m1 (n : Z) : fileread_ret n (mword_of_int (-1) : mword 64).
Proof. left. reflexivity. Qed.

(* THE OFFSET STAYS IN RANGE.  [FileOff.off_wf] is an inductive invariant and
   this is fileread's step of the induction: [f->off += r] cannot leave the
   bound, because readi clamps [r] to the file's size and the size is itself
   bounded.  Both of rd_clamp's cases are needed and neither is slack --
   above the size the clamp is a NAT subtraction and answers 0, which is why
   the incoming [off <= MAXFILE*BSIZE] premise is load-bearing rather than
   implied. *)
Lemma fileread_off_advance (szw : bv 32) (off n tot : nat) :
  (tot <= rd_clamp szw off n)%nat ->
  bv_unsigned szw <= Z.of_nat MAXFILE * Z.of_nat BSIZE ->
  Z.of_nat off <= Z.of_nat MAXFILE * Z.of_nat BSIZE ->
  Z.of_nat off + Z.of_nat tot <= Z.of_nat MAXFILE * Z.of_nat BSIZE.
Proof.
  rewrite /rd_clamp. intros Htot Hsz Hoff.
  destruct (decide (Z.to_nat (bv_unsigned szw) < off + n)%nat) as [Hlt|Hge].
  - (* clamped to the size: [off + tot <= max off (Z.to_nat szw)] *)
    destruct (decide (off <= Z.to_nat (bv_unsigned szw))%nat) as [Hle|Hgt].
    + assert (Hb : (off + tot <= Z.to_nat (bv_unsigned szw))%nat) by lia.
      pose proof (Z2Nat.id (bv_unsigned szw)
                    (proj1 (bv_unsigned_in_range _ szw))) as Hid.
      lia.
    + (* the nat subtraction is 0 here, so nothing was read *)
      assert (Htz : tot = 0%nat) by lia. rewrite Htz. lia.
  - (* not clamped: [off + n] is at or below the size *)
    assert (Hb : (off + tot <= Z.to_nat (bv_unsigned szw))%nat) by lia.
    pose proof (Z2Nat.id (bv_unsigned szw)
                  (proj1 (bv_unsigned_in_range _ szw))) as Hid.
    lia.
Qed.

(* ---------------------------------------------------------------------- *)
(*  The ghost names and geometry the two heavy arms are indexed by          *)
(* ---------------------------------------------------------------------- *)
(* NOTHING PER-INODE IS IN HERE, and that is the point (fs-sysfile S4' /
   blocker 2's ratified alternative; [SpecFilestat.fstat_names] is the
   landed template).  The itable SLOT, the inum, the lent share's fraction,
   the entry's two sleeplock gnames, the device and the region's block count
   are all things a CALLER cannot know: a reference borrowed out of
   [ProcInv.ofile_slot] comes with its slot, fraction and content
   existentially quantified.  Every one of them comes out of the reference
   itself ([fileread_pay_carve]), or is the ambient cache's
   ([IcacheRef.icfg_dev] / [icfg_nib]), or is existential under the sleeplock
   FAMILY. *)
Record fread_names := MkFReadNames {
  frn_procs      : list gname;    (* the proc table's per-slot lock names   *)
  frn_j          : nat;           (* the running process's index            *)
  frn_plock      : gname;
  frn_uart       : uart_names;
  frn_disk       : disk_names;
  frn_dlock      : gname;         (* virtio_disk.lock                       *)
  frn_cons       : gname;         (* cons.lock -- the DEVICE arm's           *)
  frn_pd         : mword 64;
  frn_pav        : mword 64;
  frn_pu         : mword 64;
  frn_bio        : bio_names;
  frn_fs         : fs_names;
  frn_ireg       : gname;         (* the inode region (InodeRegion.v)       *)
  frn_ic         : ic_names;      (* the icache's names (IcacheEscrow.v)    *)
  frn_cov        : gset Z;
  frn_logstart   : Z;
  frn_inodestart : Z;
  frn_dqs        : dfrac;         (* sb.inodestart                          *)
  (* THE DEVICE TABLE'S READ COLUMN, AS FUNCTIONS OF THE MAJOR.  Scalars
     until fs-sysfile S4c, and they could not stay scalar: the device arm's
     cell address is [a_devsw_read (dev_major Cf)], so ONE cell covers ONE
     major, and a SYSCALL cannot know which major its descriptor names.  A
     caller that must be ready for any of them owns the whole column
     ([fileread_devsw] below) and [fileread_devsw_acc] picks the entry.
     Nothing about fileread's own proof changes: it works at one major
     throughout, and now spells it [frn_rp fn (dev_major Cf)]. *)
  frn_rp         : Z -> mword 64; (* devsw[mj].read                         *)
  frn_dqv        : Z -> dfrac;    (* ...and that cell's fraction            *)
}.

(* Spelled out rather than derived, exactly as [SpecFileclose.fclose_names]
   is: several of these records have no [Inhabited] instance of their own and
   [bio_names] has function fields.  Nothing reads these values -- a caller
   that passes them cannot reach the arm they belong to -- so any closed term
   does. *)
Global Instance fread_names_inhabited : Inhabited fread_names :=
  populate (MkFReadNames
    [] 0%nat 1%positive
    (UartNames 1%positive 1%positive 1%positive 1%positive)
    (DiskNames 1%positive 1%positive 1%positive 1%positive 1%positive
               1%positive 1%positive)
    1%positive 1%positive
    (mword_of_int 0) (mword_of_int 0) (mword_of_int 0)
    (MkBioNames 1%positive 1%positive 1%positive
       (fun _ => (1%positive, 1%positive)) (fun _ => 1%positive)
       (fun _ => 1%positive))
    (MkFsNames 1%positive 1%positive 1%positive)
    1%positive (MkIcNames (fun _ => 1%positive) (fun _ => 1%positive)
                          (fun _ => 1%positive))
    ∅ 0 0 (DfracOwn 1)
    (fun _ => mword_of_int 0) (fun _ => DfracOwn 1)).

(* THE DUPLICATE [!icacheG Σ] IS GONE, and it had to be: [fileG] BUNDLES
   [icacheG] (and the [icfg]), so binding both gives TWO instances,
   propositions that print identically and do not unify
   (durable-notes.md, "a class that carries another class as a FIELD instance
   must not be bound alongside it").  It was invisible while nothing in this
   file mixed the two; the carve does -- the payload's share is at [fileG]'s
   [icfg_dev], and a freshly written [icfg_dev] here would be the standalone
   instance's.  Same edit as SpecFilestat's. *)
Section SpecFileread.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !kallocG Σ,
            !bioG Σ, !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ,
            !irefslotG Σ, !pavG Σ, !iregG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  (* ---- the FD_DEVICE arm's environment ---- *)

  (* WHAT THE CALLEE NEEDS, as opposed to what the DISPATCH needs.  The cell
     below is how fileread finds consoleread; this is what consoleread itself
     asks for (SpecConsoleread.v) -- [cons.lock], and nothing else.  ONE
     conjunct where the write side has two ([SpecFilewrite.filewrite_dev_caps]
     also carries the UART's), because consoleread never touches the
     transmitter.  Persistent, so a caller pays for it once. *)
  Definition fileread_dev_caps (fn : fread_names) : iProp Σ :=
    is_conslock (frn_cons fn).

  Global Instance fileread_dev_caps_persistent fn :
    Persistent (fileread_dev_caps fn).
  Proof. apply _. Qed.

  (* ONE cell, and only when the major is in range.  The disjunction is the
     honest statement of what the kernel installs: [consoleinit] fills
     [devsw[CONSOLE]] and nothing fills any other entry, so a read slot is
     either null (and the code returns -1) or [consoleread]. *)
  Definition fileread_dev_env (fn : fread_names) (Cf : fcontent) : iProp Σ :=
    (if decide (dev_major Cf <= NDEV_max)
     then ⌜frn_rp fn (dev_major Cf) = (zero_reg : mword 64)
           \/ frn_rp fn (dev_major Cf)
               = (mword_of_int KernelSyms.consoleread : mword 64)⌝ ∗
          a_devsw_read (dev_major Cf) ↦₈{frn_dqv fn (dev_major Cf)}
            frn_rp fn (dev_major Cf) ∗
          fileread_dev_caps fn
     else emp)%I.

  (* it is only READ, so it comes back as it went in *)
  Definition fileread_dev_out (fn : fread_names) (Cf : fcontent) : iProp Σ :=
    fileread_dev_env fn Cf.

  (* ---- THE WHOLE COLUMN, and how one entry comes out of it ----

     What a CALLER that cannot name its descriptor's major must own.  It is
     content-independent -- the point of S4c -- and it is not a weakening
     dressed up: a syscall that may read any descriptor really can be handed
     a device file with any major in range, and the entry it would then index
     is a resource somebody has to hold.  Ten cells is what that costs.

     [fileread_dev_env] at an OUT-OF-RANGE major is [emp], so the accessor is
     total: the code returns -1 before the table is indexed. *)
  Definition fileread_devsw (fn : fread_names) : iProp Σ :=
    (fileread_dev_caps fn ∗
     [∗ list] i ∈ seq 0 (Z.to_nat NDEV_max + 1),
       ⌜frn_rp fn (Z.of_nat i) = (zero_reg : mword 64)
         \/ frn_rp fn (Z.of_nat i)
             = (mword_of_int KernelSyms.consoleread : mword 64)⌝ ∗
       a_devsw_read (Z.of_nat i) ↦₈{frn_dqv fn (Z.of_nat i)}
         frn_rp fn (Z.of_nat i))%I.

  Lemma fileread_devsw_acc (fn : fread_names) (Cf : fcontent) :
    fileread_devsw fn -∗
    fileread_dev_env fn Cf ∗ (fileread_dev_out fn Cf -∗ fileread_devsw fn).
  Proof.
    (* THE UNFOLD ORDER MATTERS: [/fileread_dev_out] rewrites to [fileread_dev_env], so
       unfolding [fileread_dev_env] FIRST leaves the out side folded and the
       closing [iExact] fails on two terms that print differently for that
       reason alone. *)
    rewrite /fileread_dev_out /fileread_dev_env /fileread_devsw.
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
                    (⌜frn_rp fn (Z.of_nat jj) = (zero_reg : mword 64)
                      \/ frn_rp fn (Z.of_nat jj)
                          = (mword_of_int KernelSyms.consoleread : mword 64)⌝ ∗
                     a_devsw_read (Z.of_nat jj) ↦₈{frn_dqv fn (Z.of_nat jj)}
                       frn_rp fn (Z.of_nat jj))%I)
                 _ i i Hlk with "H") as "[Hone Hback]".
    iEval (rewrite Hid) in "Hone".
    iSplitL "Hone".
    { iDestruct "Hone" as "[Hp Hc]". iFrame "Hp Hc". iExact "Hcaps". }
    iIntros "(Hp & Hc & _)". iFrame "Hcaps".
    iApply "Hback". rewrite Hid. iFrame "Hp Hc".
  Qed.

  (* ---- the FD_INODE arm's environment: ilock's, readi's and iunlock's ----

     CONTENT-INDEPENDENT, in [SpecFilestat.filestat_fs_env]'s form (which is
     [SpecFileclose.fileclose_fs_env]'s): the escrow FAMILY, the sleeplock
     FAMILY, the off-borrow FAMILY, the inode region, the block cache, the
     disk fabric, and the region-WIDE inum geometry (quantified, because the
     inum is existential in the reference).  It mentions neither [Cf] nor any
     slot -- neither an itable slot nor an fd slot -- so a syscall that has
     not yet borrowed its descriptor can own it, which is the whole point.
     The per-inode pieces come out of the reference at the call
     ([fileread_pay_carve] below). *)
  Definition fileread_fs_env (γf : gname) (fn : fread_names) : iProp Σ :=
    (⌜log_geom_ok (frn_cov fn) (frn_logstart fn)⌝ ∗
     ⌜0 <= frn_inodestart fn⌝ ∗
     (* EVERY inum the region covers has its block inside [cov] -- the
        quantified form, since the reference names the inum existentially *)
     ⌜forall inum : mword 32,
        bv_unsigned inum < 16 * Z.of_nat icfg_nib ->
        IBLOCK inum (frn_inodestart fn) ∈ frn_cov fn⌝ ∗
     bio_ctx (frn_bio fn)
       (fs_view (frn_fs fn) (frn_disk fn) icfg_dev (frn_cov fn)) ∗
     (* THE THREE PERSISTENT INVARIANTS SpecIlock / SpecIunlock take: the
        [ref] words, the entries' content escrows, the inode region -- the
        escrow at the FAMILY where it was per-slot. *)
     itable_inv ∗
     ic_escrows (frn_ic fn) (frn_fs fn) (frn_ireg fn) (frn_cov fn)
                (frn_logstart fn) ∗
     ireg_inv (frn_ireg fn) (frn_fs fn) (frn_inodestart fn) icfg_nib ∗
     (* EVERY ENTRY'S SLEEPLOCK -- over the CHECKOUT TOKEN alone *)
     ic_sleeplocks (frn_ic fn) ∗
     sb_inodestart ↦₄{frn_dqs fn}
       (mword_of_int (frn_inodestart fn) : mword 32) ∗
     (* the disk fabric *)
     dev_inv (frn_uart fn) (frn_disk fn) ∗
     disk_geom (frn_disk fn) (frn_pd fn) (frn_pav fn) (frn_pu fn) ∗
     is_lock (frn_dlock fn) d_lock "virtio_disk"%string
       (disk_res (frn_disk fn) (frn_pd fn) (frn_pav fn) (frn_pu fn)) ∗
     (* ONE slot unit: ilock's bread takes it and brelse gives it back;
        readi's does the same, one after the other *)
     bslot (frn_bio fn))%I.

  (* What comes back: the superblock fraction and the slot unit.  NO SHARE --
     the share never left the reference's payload, so there is nothing here
     for it to be returned through, and hence no generation to lose (which is
     what made the old [inode_shr] return ungatherable). *)
  Definition fileread_fs_out (fn : fread_names) : iProp Σ :=
    (sb_inodestart ↦₄{frn_dqs fn}
       (mword_of_int (frn_inodestart fn) : mword 32) ∗
     bslot (frn_bio fn))%I.

  (* ---- and the three, selected by the file's type ---- *)
  Definition fileread_env (γf : gname)
      (fn : fread_names) (Cf : fcontent) : iProp Σ :=
    (if bool_decide (fc_type Cf = FD_PIPE) then emp
     else if bool_decide (fc_type Cf = FD_DEVICE) then fileread_dev_env fn Cf
     else if bool_decide (fc_type Cf = FD_INODE)
     then fileread_fs_env γf fn
     else emp)%I.

  Definition fileread_env_out (fn : fread_names) (Cf : fcontent) : iProp Σ :=
    (if bool_decide (fc_type Cf = FD_PIPE) then emp
     else if bool_decide (fc_type Cf = FD_DEVICE) then fileread_dev_out fn Cf
     else if bool_decide (fc_type Cf = FD_INODE) then fileread_fs_out fn
     else emp)%I.

  (* THE EARLY RETURN'S OBLIGATION, checked here rather than discovered in
     the proof: [f->readable == 0] returns before the type is ever tested, so
     the environment must already contain everything the postcondition
     promises. *)
  Lemma fileread_fs_env_out γf fn :
    fileread_fs_env γf fn -∗ fileread_fs_out fn.
  Proof.
    rewrite /fileread_fs_env /fileread_fs_out.
    iIntros "(_ & _ & _ & _ & _ & _ & _ & _ & Hsb & _ & _ & _ & Hbs)".
    iFrame "Hsb Hbs".
  Qed.

  Lemma fileread_env_out_of_env γf fn Cf :
    fileread_env γf fn Cf -∗ fileread_env_out fn Cf.
  Proof.
    rewrite /fileread_env /fileread_env_out.
    case_bool_decide; [by iIntros "$"|].
    case_bool_decide; [by iIntros "$"|].
    case_bool_decide; [|by iIntros "$"].
    iApply fileread_fs_env_out.
  Qed.

  (* A file that is neither a pipe, nor a device, nor an inode costs its
     reader nothing -- the arm is [panic], and [panic_wp_any] closes it. *)
  Lemma fileread_env_none γf fn Cf :
    fc_type Cf = FD_NONE -> ⊢ fileread_env γf fn Cf.
  Proof.
    intro Ht. rewrite /fileread_env Ht.
    rewrite bool_decide_eq_false_2; [|by vm_compute].
    rewrite bool_decide_eq_false_2; [|by vm_compute].
    rewrite bool_decide_eq_false_2; [|by vm_compute].
    done.
  Qed.

  (* ==================================================================== *)
  (*  THE CARVE, AND THE SHARE ALGEBRA IT NEEDS                           *)
  (* ==================================================================== *)
  (* OWED CLEANUP (fs-sysfile S4' item 2, and STILL OWED after S4c): none of
     the five below is about fileread.  They are the file-table / icache
     algebra every [file.c] function that locks its fd's inode needs, and
     their homes are [IcacheRef.v] (the three share laws -- with
     [ProofFilewriteParts.fw_shr_*], which are the same lemmas),
     [IcacheEscrow.v] ([ic_escrows_acc]) and [FileInvDefs.v] (the carve).
     They are stated HERE rather than there because those files are
     bottom-of-tree (a full rebuild) AND, at S4c, adjacent to a concurrently
     owned effort.  [SpecFilestat.v] carries a copy of the first four for the
     same reason and predates this one; retiring BOTH copies into the three
     homes is one edit when the tree next takes a bottom-of-tree rebuild.
     SpecFilewrite requires this file, so filewrite reuses these rather than
     making a third copy. *)

  (* the generation-named share splits, exactly as its ∃-form does *)
  Lemma inode_shr_gen_split2 (ik : nat) (s1 s2 : Qp) (dev inum : mword 32)
      (g : gname) :
    IcacheRef.inode_shr_gen ik (s1 + s2)%Qp dev inum g ⊣⊢
    IcacheRef.inode_shr_gen ik s1 dev inum g ∗
    IcacheRef.inode_shr_gen ik s2 dev inum g.
  Proof.
    rewrite /IcacheRef.inode_shr_gen IcacheRef.inode_ident_split
            IcacheRef.live_gen_split SleepLock.slh_tok_split.
    iSplit; [iIntros "[[$ $] [[$ $] [$ $]]]" | iIntros "[($ & $ & $) ($ & $ & $)]"].
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
     Verbatim [ProofFilewriteParts.fw_shr_regen]. *)
  Lemma inode_shr_regen2 (ik : nat) (s1 s2 : Qp) (dev inum : mword 32)
      (g : gname) :
    IcacheRef.inode_shr_gen ik s1 dev inum g -∗
    IcacheRef.inode_shr ik s2 dev inum -∗
    IcacheRef.inode_shr_gen ik (s1 + s2)%Qp dev inum g.
  Proof.
    iIntros "H1 H2".
    iEval (rewrite IcacheRef.inode_shr_gen_intro) in "H2".
    iDestruct "H2" as (g2) "H2".
    iDestruct "H1" as "(Hid1 & Hlv1 & Hs1)". iDestruct "H2" as "(Hid2 & Hlv2 & Hs2)".
    iDestruct (IcacheRef.live_gen_agree with "Hlv1 Hlv2") as %<-.
    rewrite inode_shr_gen_split2. iFrame.
  Qed.

  (* the per-entry escrow, out of the family *)
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

  (* THE CARVE ITSELF -- [SpecFilestat.filestat_pay_carve] GROWN BY THE TYPE
     WITNESS.  An FD_INODE / FD_DEVICE file's payload IS a share of its
     inode's reference, generation-named, parked beside the cancel token
     ([FileInvDefs.inode_pay]) TOGETHER WITH that generation's [ity_shot] and
     the "a writable fd is not a directory" fact.  So a function that holds
     the descriptor's reference already holds everything the old,
     content-indexed environment asked its caller for: the slot, the device,
     the inum, the region bound, the share, the type witness and its
     non-directory side condition.  This hands them out and takes the share
     back ([ity_shot] is persistent, so it needs no return).

     fileread uses only the first six outputs; filewrite needs [ty] and the
     [fc_wbool] implication as well, which is why the GROWN form lives here
     rather than a second, smaller copy living in SpecFilewrite. *)
  Lemma fileread_pay_carve (γf : gname) (k : nat) (q : Qp) (Cf : fcontent) :
    fc_type Cf = FD_INODE \/ fc_type Cf = FD_DEVICE ->
    file_pay γf k q Cf -∗
    ∃ (ik : nat) (inum : mword 32) (s : Qp) (g : gname) (ty : bv 16)
      (γx : gname),
      ⌜fc_ip Cf = ientry ik⌝ ∗ ⌜(ik < NINODE)%nat⌝ ∗
      ⌜bv_unsigned inum < 16 * Z.of_nat icfg_nib⌝ ∗
      ⌜fc_wbool Cf = true -> bv_unsigned ty <> T_DIR_z⌝ ∗
      IcacheRef.ity_shot g ty ∗
      IcacheRef.inode_shr_gen ik s icfg_dev inum g ∗
      off_hold γf k γx true q ∗
      (IcacheRef.inode_shr_gen ik s icfg_dev inum g -∗ off_hold γf k γx true q -∗
         file_pay γf k q Cf).
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
    assert (Harm : file_armed Cf = true) by (rewrite /file_armed; exact Hyes).
    rewrite /file_payload /file_core Hnp Hyes Harm /inode_pay.
    iDestruct "Hpl" as "((#Hci & Hown & Hs & Hwt) & Hop)".
    iDestruct "Hs" as (ik inum) "(%Hipk & %Hik & %Hinb & Hshr)".
    iDestruct "Hwt" as (ty) "[#Hshot %Hnd]".
    iExists ik, inum, (q * fp_iq pn)%Qp, (fp_ig pn), ty, (fp_ocv pn).
    iSplitR; [done|]. iSplitR; [done|]. iSplitR; [done|]. iSplitR; [done|].
    iSplitR; [iExact "Hshot"|].
    (* [iExact], not [iFrame]: both sides are the same FOLDED
       [IcacheRef.inode_shr_gen] and conversion closes it, while the [Frame]
       instance search does not see through the definition. *)
    iSplitL "Hshr"; [iExact "Hshr"|].
    iSplitL "Hop"; [iExact "Hop"|].
    iIntros "Hshr Hop". iExists pn. iFrame "Hpn".
    rewrite /file_payload /file_core Hnp Hyes Harm /inode_pay.
    iSplitR "Hop"; [| iExact "Hop"].
    iSplitR; [iExact "Hci"|]. iSplitL "Hown"; [iExact "Hown"|].
    iSplitL "Hshr"; [iExists ik, inum; iFrame "%"; iExact "Hshr"|].
    iExists ty. iSplitR; [iExact "Hshot"|]. done.
  Qed.

End SpecFileread.

Definition wp_fileread_sconf_body
    `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !kallocG Σ,
      !bioG Σ, !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ,
      !irefslotG Σ, !pavG Σ, !iregG Σ}
    `{GEN : GenId} `{CID : CpuId}

    (γa : gname) (γf : gname)                    (* kalloc, the file table  *)
    (γs : list gname) (j : nat) (γlp : gname)    (* the running process     *)
    (k : nat) (q : Qp) (Cf : fcontent)           (* the borrowed reference  *)
    (fn : fread_names)                           (* the heavy arms' ghosts  *)
    (pidv : mword 32) (V : pprivate)
    (m : regfile) (K : nat) (eb : bool) (n : Z) (b : bool) (lks : gset string) :=
  let pcE : mword 64 := mword_of_int KernelSyms.fileread in
  let pj := proc_addr j in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  (fileread_stack <= K)%nat ->
  (k < NFILE)%nat ->
  (j < NPROC)%nat ->
  γs !! j = Some γlp ->
  length γs = NPROC ->
  (* a0 = f, a1 = addr (the user destination, never inspected here), a2 = n *)
  m !!! Regidx (mword_of_int 10 : mword 5) = fnode k ->
  m !!! Regidx (mword_of_int 12 : mword 5) = (mword_of_int n : mword 64) ->
  (* THE COUNT.  Non-negative because it is a read length, and bounded so
     that readi's joint [off + n < 2^32] follows from the invariant's
     [off <= MAXFILE*BSIZE] alone.  See the header: the bound is now stronger
     than readi needs and can be relaxed to [0 <= n < 2^31], which is what
     retires the debt sys_read inherits. *)
  0 <= n ->
  Z.of_nat MAXFILE * Z.of_nat BSIZE + n < 2 ^ 31 ->
  (* PARKING PREMISE (hart-generic scheduler protocol): every arm sleeps. *)
  eb = true ->
  (* the order premise, at the LOWEST rank this cone touches; every
     higher one follows by [locks_below_mono]. *)
  locks_below lks "bcache" ->
  sie_cap_gpr m K b pj -∗
  (* noff = 0: everything below reaches sleep *)
  cpu_own 0%nat eb pj b lks -∗
  kernel_text -∗ pc_is pcE -∗
  panic_wp_any -∗
  (* the borrowed reference -- at an ARBITRARY fraction, and given back *)
  file_ref γf k q Cf -∗
  (* ambient, because three of the four arms copy into user memory *)
  proc_priv_core pj pidv V -∗
  kalloc_env γa None -∗
  procs_inv γs -∗
  (* ...and what the file's TYPE selects *)
  fileread_env γf fn Cf -∗
  (* THE CROSSING IS THE LITERAL [true], NOT [b].  This function can SLEEP
     (its bread / ilock / bwrite does), and a park moves the hart with
     interrupts off, so the crossing has nothing to do with SIE -- the
     porting guide's "a PARKING function's [wp_next] index is [true]
     UNCONDITIONALLY".  Spelled [b] the two coincide at the only instance
     the [eb = true] premise admits, which is why this went unnoticed; once
     [eb = false] is reachable the [b] form would promise the caller it
     comes back on the hart it called from, which a park makes false. *)
  wp_next true pj (fun (CID : CpuId) =>
  ∀ (mf : regfile) (r : mword 64) (P' : uptd),
      ⌜callee_saved m mf⌝ -∗
      ⌜uptd_ext (pv_upt V) P'⌝ -∗
      ⌜fileread_ret n r⌝ -∗
      ⌜mf !!! Regidx (mword_of_int 10 : mword 5) = r⌝ -∗
      sie_cap_gpr mf K b pj -∗
      cpu_own 0%nat eb pj b lks -∗
      pc_is ret_tgt -∗
      file_ref γf k q Cf -∗
      proc_priv_core pj pidv (upd_upt V P') -∗
      fileread_env_out fn Cf -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type FILEREAD.
  Parameter wp_fileread_sconf :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !kallocG Σ,
             !bioG Σ, !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ,
             !irefslotG Σ, !pavG Σ, !iregG Σ}
      `{GEN : GenId} `{CID : CpuId}

      (γa : gname) (γf : gname)
      (γs : list gname) (j : nat) (γlp : gname)
      (k : nat) (q : Qp) (Cf : fcontent)
      (fn : fread_names)
      (pidv : mword 32) (V : pprivate)
      (m : regfile) (K : nat) (eb : bool) (n : Z) (b : bool) (lks : gset string),
      wp_fileread_sconf_body γa γf γs j γlp k q Cf fn pidv V m K eb n b lks.
End FILEREAD.
