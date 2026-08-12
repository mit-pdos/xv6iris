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

   [f->off] is not a content field: it lives in [FileOff.off_inv] and is
   BORROWED across the readi call under [ip->lock] (design/file-table.md).
   fileread is the whole reason that protocol exists.  Two consequences for
   this contract:

   * the fs environment carries [off_inv γf k], and nothing else about the
     offset -- the value is existential in the invariant, and the invariant's
     [off_wf] bound is what makes it usable;
   * readi's joint numeric premise [off + n < 2^31] has to be discharged from
     a bound on [n] ALONE, because nothing in memory bounds a freshly loaded
     offset.  Hence [MAXFILE * BSIZE + n < 2^31] below.  THIS IS AN
     OBLIGATION FILEREAD PASSES UPWARD: it is inherited from readi (and
     writei), whose joint bound is what keeps their [c.addw] from wrapping,
     and a caller taking [n] from unchecked user input -- sys_read -- cannot
     discharge it.  Fixing it means either proving readi's own overflow arm
     (which needs a wrapping-[addw] reading the tree does not have) or
     bounding [n] at the syscall boundary; see
     claude-notes/design/file-table.md. *)
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
Require Import SpecReadi.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Import Defs.

Local Open Scope Z_scope.

(* fileread's own frame is 6 slots ([addi sp,sp,-48]: ra, s0..s3 saved, one
   slot unused), and its deepest callee is readi.  The others are smaller:
   piperead and consoleread 62, ilock 44, iunlock 26.  A CONSTANT, not a
   per-arm bound: the stack a function may need is a property of the function
   (durable-notes.md). *)
Definition fileread_stack : nat := (6 + K_readi)%nat.

(* NDEV, as the bounds test reads it: [bltu a4,a3] with a4 = 9 against the
   ZERO-EXTENDED 16-bit major, so "in range" is exactly [major <= 9] and a
   negative [short] is caught by the zero extension rather than by a signed
   test.  (The C says [f->major < 0 || f->major >= NDEV]; gcc merged the two
   into one unsigned compare.) *)
Definition NDEV_max : Z := 9.

Definition dev_major (Cf : fcontent) : Z := bv_unsigned (fc_major Cf).

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
Record fread_names := MkFReadNames {
  frn_procs      : list gname;    (* the proc table's per-slot lock names   *)
  frn_j          : nat;           (* the running process's index            *)
  frn_plock      : gname;
  frn_uart       : uart_names;
  frn_disk       : disk_names;
  frn_dlock      : gname;         (* virtio_disk.lock                       *)
  frn_pd         : mword 64;
  frn_pav        : mword 64;
  frn_pu         : mword 64;
  frn_bio        : bio_names;
  frn_fs         : fs_names;
  frn_ireg       : gname;         (* the inode region (InodeRegion.v)       *)
  frn_ic         : ic_names;      (* the icache's names (IcacheEscrow.v)    *)
  frn_ilk        : gname;         (* ip->lock's inner spinlock              *)
  frn_islk       : gname;         (* ip->lock's holder token                *)
  frn_cov        : gset Z;
  frn_logstart   : Z;
  frn_inodestart : Z;
  frn_dev        : mword 32;
  frn_inum       : mword 32;
  frn_nib        : nat;           (* the inode region's block count         *)
  frn_ik         : nat;           (* the itable SLOT this inode is           *)
  frn_s          : Qp;            (* the LENT SHARE's fraction (v3)          *)
  frn_dqs        : dfrac;         (* sb.inodestart                          *)
  frn_rp         : mword 64;      (* devsw[major].read                      *)
  frn_dqv        : dfrac;         (* ...and that cell's fraction            *)
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
    1%positive
    (mword_of_int 0) (mword_of_int 0) (mword_of_int 0)
    (MkBioNames 1%positive 1%positive 1%positive
       (fun _ => (1%positive, 1%positive)) (fun _ => 1%positive)
       (fun _ => 1%positive))
    (MkFsNames 1%positive 1%positive 1%positive)
    1%positive (MkIcNames (fun _ => 1%positive) (fun _ => 1%positive)
                          (fun _ => 1%positive))
    1%positive 1%positive
    ∅ 0 0 (mword_of_int 0) (mword_of_int 0) 0%nat 0%nat 1%Qp (DfracOwn 1)
    (mword_of_int 0) (DfracOwn 1)).

Section SpecFileread.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !kallocG Σ,
            !bioG Σ, !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ,
            !icacheG Σ, !irefslotG Σ, !iregG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  (* ---- the FD_DEVICE arm's environment ---- *)

  (* ONE cell, and only when the major is in range.  The disjunction is the
     honest statement of what the kernel installs: [consoleinit] fills
     [devsw[CONSOLE]] and nothing fills any other entry, so a read slot is
     either null (and the code returns -1) or [consoleread] (whose contract is
     ASSUMED, LinkConsoleread.v). *)
  Definition fileread_dev_env (fn : fread_names) (Cf : fcontent) : iProp Σ :=
    (if decide (dev_major Cf <= NDEV_max)
     then ⌜frn_rp fn = (zero_reg : mword 64)
           \/ frn_rp fn = (mword_of_int KernelSyms.consoleread : mword 64)⌝ ∗
          a_devsw_read (dev_major Cf) ↦₈{frn_dqv fn} frn_rp fn
     else emp)%I.

  (* it is only READ, so it comes back as it went in *)
  Definition fileread_dev_out (fn : fread_names) (Cf : fcontent) : iProp Σ :=
    fileread_dev_env fn Cf.

  (* ---- the FD_INODE arm's environment: ilock's, readi's and iunlock's ---- *)
  Definition fileread_fs_env  (γf : gname) (k : nat)
      (fn : fread_names) (Cf : fcontent) : iProp Σ :=
    (⌜log_geom_ok (frn_cov fn) (frn_logstart fn)⌝ ∗
     ⌜0 <= frn_inodestart fn⌝ ∗
     ⌜IBLOCK (frn_inum fn) (frn_inodestart fn) ∈ frn_cov fn⌝ ∗
     (* the inum is inside the inode region: [ireg_read]'s premise *)
     ⌜bv_unsigned (frn_inum fn) < 16 * Z.of_nat (frn_nib fn)⌝ ∗
     (* THE INODE IS ITABLE SLOT [frn_ik fn].  This replaces v1's
        [uint (fc_ip Cf) <> 0]: [IcacheRef.ientry_unsigned] refutes ilock's
        and iunlock's null test outright.  Their [ref < 1] test is refuted
        from [itable_inv] by [iref_live_load_au] (v3 -- a share carries no
        count fragment, §14.6), so v1's [0 < refv < 2^31]
        premise about a caller-owned [i_ref] fraction is gone too.  And
        readi's [size <= MAXFILE*BSIZE] premise is gone because ilock's
        record is now an OUTPUT: the bound travels with it, as the fifth
        conjunct of [InodeLock.inode_ok] (design §13.5). *)
     ⌜fc_ip Cf = ientry (frn_ik fn)⌝ ∗
     ⌜(frn_ik fn < NINODE)%nat⌝ ∗
     (* THE OFF-BORROW INVARIANT for this slot -- persistent, and the whole
        reason design/file-table.md's stage 2 exists *)
     off_inv γf k ∗
     bio_ctx (frn_bio fn)
       (fs_view (frn_fs fn) (frn_disk fn) (frn_dev fn) (frn_cov fn)) ∗
     (* THE THREE PERSISTENT INVARIANTS SpecIlock v2 / SpecIunlock v2 take:
        the [ref] words, the entry's content escrow, the inode region.  They
        replace v1's [inode_parked] sleeplock, its [inode_key] shadow half,
        its [i_ref] fraction and its whole-inode-block [fsblock]. *)
     itable_inv ∗
     ic_escrow (frn_ic fn) (frn_fs fn) (frn_ireg fn) (frn_cov fn)
               (frn_logstart fn) (frn_ik fn) ∗
     ireg_inv (frn_ireg fn) (frn_fs fn) (frn_inodestart fn) (frn_nib fn) ∗
     (* THE ENTRY'S SLEEPLOCK -- over the CHECKOUT TOKEN alone *)
     is_sleeplock (frn_ilk fn) (frn_islk fn) (i_lock (fc_ip Cf)) "inode"%string
       (ic_tok (frn_ic fn) (frn_ik fn)) ∗
     (* THE LENT SHARE (v3, design §14.6/§14.8).  SpecIlock v3 takes a
        SHARE, not a reference: a share is a slice of the two identity cells
        plus the matching slice of the slot's liveness unit, carved from a
        reference by [IcacheRef.inode_ref_carve] -- a pure resource split, no
        fupd and no invariant opening.  ilock deposits it into the escrow and
        iunlock brings it back AT THE SAME FRACTION (the checkout descriptor
        pins it, §14.8), so fileread neither loses nor invents mass.

        WHERE IT COMES FROM, in the eventual design: sys_read's cone carves
        it off the FD_INODE file payload's cinv-parked reference at entry and
        gathers it back at exit ([inode_ref_gather]) -- the bracket discipline
        of §14.1, made a resource by the canonical pairing.  The parent
        reference is [inode_ref_short] while the share is out, so it cannot
        be spent (iput above all) until the gather, which is exactly what
        makes shares unable to outlive their parent.  Stating the share HERE
        rather than a reference is what lets that carve happen at the file
        table's altitude, where [fp_iq]'s proportional accounting lives; that
        wiring is B3's, and nothing in this file's cone needs it. *)
     IcacheRef.inode_shr (frn_ik fn) (frn_s fn)
               (frn_dev fn) (frn_inum fn) ∗
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

  (* What comes back: THE SAME SHARE, at the same fraction.  v2 had to say
     [∃ q'] here -- the two early returns (not readable; a type that is not
     FD_INODE) never reach ilock and hand the caller's own reference back
     untouched, while the arm that ran got one out of [ic_swap_park], which
     pinned the device and the inum but not the fraction.  The checkout
     descriptor (§14.8) pins the fraction too, so both arms now return
     literally [frn_s fn] and the existential is gone.  That matters beyond
     tidiness: B3's [fp_iq] accounting has to re-gather this share into the
     payload's parent reference, and a gather needs the fraction to be the
     one that was carved. *)
  Definition fileread_fs_out (fn : fread_names) (Cf : fcontent) : iProp Σ :=
    (IcacheRef.inode_shr (frn_ik fn) (frn_s fn)
                           (frn_dev fn) (frn_inum fn) ∗
     sb_inodestart ↦₄{frn_dqs fn}
       (mword_of_int (frn_inodestart fn) : mword 32) ∗
     bslot (frn_bio fn))%I.

  (* ---- and the three, selected by the file's type ---- *)
  Definition fileread_env  (γf : gname) (k : nat)
      (fn : fread_names) (Cf : fcontent) : iProp Σ :=
    (if bool_decide (fc_type Cf = FD_PIPE) then emp
     else if bool_decide (fc_type Cf = FD_DEVICE) then fileread_dev_env fn Cf
     else if bool_decide (fc_type Cf = FD_INODE)
     then fileread_fs_env γf k fn Cf
     else emp)%I.

  Definition fileread_env_out (fn : fread_names) (Cf : fcontent) : iProp Σ :=
    (if bool_decide (fc_type Cf = FD_PIPE) then emp
     else if bool_decide (fc_type Cf = FD_DEVICE) then fileread_dev_out fn Cf
     else if bool_decide (fc_type Cf = FD_INODE) then fileread_fs_out fn Cf
     else emp)%I.

  (* THE EARLY RETURN'S OBLIGATION, checked here rather than discovered in
     the proof: [f->readable == 0] returns before the type is ever tested, so
     the environment must already contain everything the postcondition
     promises.  This is what forced the existential [vv'] above. *)
  Lemma fileread_fs_env_out γf k fn Cf :
    fileread_fs_env γf k fn Cf -∗ fileread_fs_out fn Cf.
  Proof.
    rewrite /fileread_fs_env /fileread_fs_out.
    iIntros "(_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hshr & Hsb &
              _ & _ & _ & Hbs)".
    iFrame "Hsb Hbs Hshr".
  Qed.

  Lemma fileread_env_out_of_env γf k fn Cf :
    fileread_env γf k fn Cf -∗ fileread_env_out fn Cf.
  Proof.
    rewrite /fileread_env /fileread_env_out.
    case_bool_decide; [by iIntros "$"|].
    case_bool_decide; [by iIntros "$"|].
    case_bool_decide; [|by iIntros "$"].
    iApply fileread_fs_env_out.
  Qed.

  (* A file that is neither a pipe, nor a device, nor an inode costs its
     reader nothing -- the arm is [panic], and [panic_wp_any] closes it. *)
  Lemma fileread_env_none γf k fn Cf :
    fc_type Cf = FD_NONE -> ⊢ fileread_env γf k fn Cf.
  Proof.
    intro Ht. rewrite /fileread_env Ht.
    rewrite bool_decide_eq_false_2; [|by vm_compute].
    rewrite bool_decide_eq_false_2; [|by vm_compute].
    rewrite bool_decide_eq_false_2; [|by vm_compute].
    done.
  Qed.

End SpecFileread.

Definition wp_fileread_sconf_body
    `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !kallocG Σ,
      !bioG Σ, !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ,
      !icacheG Σ, !irefslotG Σ, !iregG Σ}
    `{GEN : GenId} `{CID : CpuId}
    
    (γa : gname) (γf : gname)                    (* kalloc, the file table  *)
    (γs : list gname) (j : nat) (γlp : gname)    (* the running process     *)
    (k : nat) (q : Qp) (Cf : fcontent)           (* the borrowed reference  *)
    (fn : fread_names)                           (* the heavy arms' ghosts  *)
    (pidv : mword 32) (V : pprivate)
    (m : regfile) (K : nat) (eb : bool) (C : iProp Σ) (n : Z) (b : bool) :=
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
     that readi's joint [off + n < 2^31] follows from the invariant's
     [off <= MAXFILE*BSIZE] alone.  See the header: this premise is inherited
     from readi and is passed upward, not solved here. *)
  0 <= n ->
  Z.of_nat MAXFILE * Z.of_nat BSIZE + n < 2 ^ 31 ->
  (* PARKING PREMISE (hart-generic scheduler protocol): every arm sleeps. *)
  eb = true ->
  sie_cap_gpr m K b pj -∗
  (* noff = 0: everything below reaches sleep *)
  cpu_own 0%nat eb pj C b -∗
  kernel_text -∗ pc_is pcE -∗
  panic_wp_any -∗
  (* the borrowed reference -- at an ARBITRARY fraction, and given back *)
  file_ref γf k q Cf -∗
  (* ambient, because three of the four arms copy into user memory *)
  proc_priv_core pj pidv V -∗
  kalloc_env γa None -∗
  procs_inv γs -∗
  (* ...and what the file's TYPE selects *)
  fileread_env γf k fn Cf -∗
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
      cpu_own 0%nat eb pj C b -∗
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
             !icacheG Σ, !irefslotG Σ, !iregG Σ}
      `{GEN : GenId} `{CID : CpuId}
      
      (γa : gname) (γf : gname)
      (γs : list gname) (j : nat) (γlp : gname)
      (k : nat) (q : Qp) (Cf : fcontent)
      (fn : fread_names)
      (pidv : mword 32) (V : pprivate)
      (m : regfile) (K : nat) (eb : bool) (C : iProp Σ) (n : Z) (b : bool),
      wp_fileread_sconf_body γa γf γs j γlp k q Cf fn pidv V m K eb C n b.
End FILEREAD.
