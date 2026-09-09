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

   fileread takes [file_ref γf k q] at an ARBITRARY q -- it is a borrower,
   not a reference holder: [SpecArgfd]'s caller lends it out of the
   (thread-local) fd table for the duration and takes it back.  It gives the
   reference back unchanged.

   The load-bearing consequence of the payload link (design/file-table.md) is
   that fileread needs NO ghost state to tell a pipe from an inode.  The
   branch at +0x1e reads [f->type] out of the reference's own content
   fraction, so the loaded word IS [fc_type Cf]; the branch being taken is
   therefore the COQ fact [fc_type Cf = FD_PIPE], and [FileInvDefs.file_core]
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
   * anything else -> nothing; the arm is [panic], discharged against
     [SpecPanic] out of [kernel_data] + [panic_env] below.

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
   carries [IcacheHeld.inode_shr_held_gen (fc_ip Cf) (q * Q) g], which names
   the slot, the device and the inum and IS the share ilock wants.
   [fileread_pay_carve] below hands them out and takes the share back; the
   per-slot escrow and sleeplock then come out of the two FAMILIES
   ([ic_escrows], [IcacheEscrow.ic_sleeplocks]) at the slot the payload named,
   and the off LEDGER FRAGMENT comes out of the SAME carve, since it too
   rides the payload ([FileInvDefs.ioff_ref], the FD_INODE arm of
   [file_core_off]).  The postcondition carries no share at all, so nothing is
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
   which the borrow protocol keeps inside the inode's ledger and which no
   caller-held resource records, never has to appear.

   ==== THE OFFSET, AND THE ONE PREMISE IT FORCES =======================

   [f->off] is not a content field: it lives in its INODE's off ledger
   ([FileInvDefs.ioff_escrow]) and is BORROWED across the readi call under
   [ip->lock] ([FileOff.ioff_checkout]/[ioff_checkin], off-ledger ruling).
   fileread is the whole reason that protocol exists.  Two consequences for
   this contract:

   * the environment carries the LEDGER FAMILY and nothing per-file: the
     cell lives in the file's INODE's ledger ([FileInvDefs.ioff_escrow],
     one permanent invariant per itable slot), the membership fragment
     rides the descriptor's own payload and comes out of
     [fileread_pay_carve], and ilock's valid cell is the checkout marker.
     The value is existential in the ledger, and its [off_wf] bound is what
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
Require Import RiscvLang RiscvPtsto.
Require Import InstrBytes.
Require Import RegFile.
Require Import RiscvExtras.
Require Import CalleeSaved KernelText.
Require Import KernelDataInv.
Require Import IntrDefs.
Require Import WpNext.
Require Import WpLock.
Require Import SpecPanic.
Require Import FdSlots.
Require Import ProcGeom.
Require Export SwtchCtx.
Require Import CpuOwn.
Require Import SchedCtx.
Require Import WpUart.
Require Import DiskInv.
Require Import Xv6Cameras.
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
Require Import UserPtTree.
Require Import KvmSpec.
Require Import ProcPtOwn.
Require Import PipeInvDefs.
Require Import ProcInv.
Require Import ConsoleInv.
Require Import FileInvDefs.
Require Import SpecReadi.
Require Import FsBytesGamma.     (* [fs_gamma_L]: the live Γ                 *)
Require Import AppInv.           (* [appN]/[appE]: the commit's mask         *)
Require Import SysReadDefs.    (* the read observation's pure vocabulary   *)
Require Import FsAbsReadFire.    (* [aread_commit_at], [read_arms]: the one
                                    piece and its arms                       *)
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import ProcAvail.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Require Import FsCfg.   (* [fscfg]: the fs configuration is AMBIENT *)
Require Import PieceFam.        (* [pfam]: a one-shot piece's receipt beside its refund *)
Require Import FsAbs.   (* LAST (FsAbs's own rule) *)
Import Defs.
Require Import TsoCtx.

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
(* WHAT FILEREAD RETURNS.  [PipeInv.pipe_rw_ret]'s reading, and deliberately
   the same predicate: three of the four arms produce it verbatim and the
   fourth (readi) is strictly inside it. *)
Definition fileread_ret (n : Z) (r : mword 64) : Prop := pipe_rw_ret n r.

Lemma fileread_ret_m1 (n : Z) : fileread_ret n (mword_of_int (-1) : mword 64).
Proof. left. reflexivity. Qed.

(* THE OFFSET STAYS IN RANGE.  [FileInvDefs.off_wf] is an inductive invariant and
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
   ([IcacheRefDefs.icfg_dev] / [icfg_nib]), or is existential under the sleeplock
   FAMILY. *)
Record fread_names := MkFReadNames {
  frn_procs      : list gname;    (* the proc table's per-slot lock names   *)
  frn_j          : nat;           (* the running process's index            *)
  frn_plock      : gname;
  frn_cons       : gname;         (* cons.lock -- the DEVICE arm's           *)
  (* [frn_uart] / [frn_disk] / [frn_dlock] / [frn_bio] ARE GONE (rank 1d):
     each was a copy of a [FsCfg.fscfg] field.  The three ring pages stay
     for FsCfg.v's ruling-R1 reason. *)
  frn_pd         : mword 64;
  frn_pav        : mword 64;
  frn_pu         : mword 64;
  (* [frn_inodestart] IS GONE (rank 1c), as [fsn_inodestart] is. *)
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


 1%positive
    (mword_of_int 0) (mword_of_int 0) (mword_of_int 0)

    (DfracOwn 1)
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
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.

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
  (* KEYED ON THE MAJOR ITSELF, not on the file: [FdSlots.FdDevice] carries
     the number, so the descriptor's state is all a caller needs to say which
     entry it is talking about.  The lower bound joins the range test because
     the index is now a plain [Z] rather than a [bv_unsigned] -- out of range
     EITHER WAY is [emp], which is what keeps the accessor total. *)
  Definition fileread_dev_env (fn : fread_names) (mj : Z) : iProp Σ :=
    (if decide (0 <= mj <= NDEV_max)
     then ⌜frn_rp fn mj = (zero_reg : mword 64)
           \/ frn_rp fn mj
               = (mword_of_int KernelSyms.consoleread : mword 64)⌝ ∗
          a_devsw_read mj ↦₈{frn_dqv fn mj} frn_rp fn mj ∗
          fileread_dev_caps fn
     else emp)%I.

  (* it is only READ, so it comes back as it went in *)
  Definition fileread_dev_out (fn : fread_names) (mj : Z) : iProp Σ :=
    fileread_dev_env fn mj.

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

  (* ---- THE COLUMN, OUT OF THE CONSOLE INVARIANT ----------------------
     [fileread_devsw] is [ConsoleInv.console_inv] read at the read column,
     once the names record is instantiated at the table's own values and at
     the discarded fraction the table holds them under.  So a caller does not
     have to own a devsw family of its own: it holds the console invariant --
     one persistent proposition, out of [syscall_env] -- and this projects
     what fileread asks for.

     The per-cell disjunction fileread's contract is stated over is READ OFF
     the table ([ConsoleInv.devsw_read_val_cases]) rather than assumed of it,
     which is the point of the table saying what each slot HOLDS.
     -------------------------------------------------------------------- *)
  Lemma fileread_devsw_of_console (fn : fread_names) :
    frn_rp fn = ConsoleInv.devsw_read_val ->
    frn_dqv fn = (fun _ => DfracDiscarded) ->
    ConsoleInv.console_inv (frn_cons fn) -∗ fileread_devsw fn.
  Proof.
    intros Hrp Hdq. iIntros "#Hci".
    iDestruct (ConsoleInv.console_inv_conslock with "Hci") as "#Hlk".
    iDestruct (ConsoleInv.console_inv_devsw with "Hci") as "#Htbl".
    rewrite /fileread_devsw /fileread_dev_caps Hrp Hdq.
    iSplitR; [iExact "Hlk" |].
    rewrite /ConsoleInv.devsw_table.
    iApply (big_sepL_impl with "Htbl").
    iModIntro. iIntros (k i Hk) "[Hr _]".
    iSplitR; [iPureIntro; apply ConsoleInv.devsw_read_val_cases |].
    iExact "Hr".
  Qed.

  Lemma fileread_devsw_acc (fn : fread_names) (mj : Z) :
    fileread_devsw fn -∗
    fileread_dev_env fn mj ∗ (fileread_dev_out fn mj -∗ fileread_devsw fn).
  Proof.
    (* THE UNFOLD ORDER MATTERS: [/fileread_dev_out] rewrites to [fileread_dev_env], so
       unfolding [fileread_dev_env] FIRST leaves the out side folded and the
       closing [iExact] fails on two terms that print differently for that
       reason alone. *)
    rewrite /fileread_dev_out /fileread_dev_env /fileread_devsw.
    iIntros "[#Hcaps H]".
    case_decide as Hle;
      [| iSplitR; [done | iIntros "_"; iFrame "Hcaps"; iExact "H"]].
    destruct Hle as [Hnn Hle].
    set (i := Z.to_nat mj).
    assert (Hid : Z.of_nat i = mj)
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
    (⌜log_geom_ok fsc_cov fsc_logst⌝ ∗
     ⌜0 <= icfg_ist⌝ ∗
     (* EVERY inum the region covers has its block inside [fsc_cov] -- the
        quantified form, since the reference names the inum existentially *)
     ⌜forall inum : mword 32,
        bv_unsigned inum < 16 * Z.of_nat icfg_nib ->
        IBLOCK inum icfg_ist ∈ fsc_cov⌝ ∗
     bio_ctx (fsc_bio)
       (fs_view fsc_fs (fsc_disk) icfg_dev fsc_cov) ∗
     (* THE THREE PERSISTENT INVARIANTS SpecIlock / SpecIunlock take: the
        [ref] words, the entries' content escrows, the inode region -- the
        escrow at the FAMILY where it was per-slot. *)
     itable_inv ∗
     IcacheInv.iref_claims ∗
     ic_escrows fsc_ic fsc_fs fsc_ireg fsc_cov
                fsc_logst ∗
     ireg_inv fsc_ireg fsc_fs icfg_ist icfg_nib ∗
     (* EVERY ENTRY'S SLEEPLOCK -- over the CHECKOUT TOKEN alone *)
     ic_sleeplocks fsc_ic ∗
     sb_inodestart ↦₄{frn_dqs fn}
       (mword_of_int icfg_ist : mword 32) ∗
     (* the disk fabric *)
     dev_inv (fsc_uart) (fsc_disk) ∗
     disk_geom (fsc_disk) (frn_pd fn) (frn_pav fn) (frn_pu fn) ∗
     is_lock (fsc_dlock) d_lock "virtio_disk"%string
       (disk_res_at (fsc_disk) (frn_pd fn) (frn_pav fn) (frn_pu fn)) ∗
     (* ONE slot unit: ilock's bread takes it and brelse gives it back;
        readi's does the same, one after the other *)
     bslot)%I.

  (* What comes back: the superblock fraction and the slot unit.  NO SHARE --
     the share never left the reference's payload, so there is nothing here
     for it to be returned through, and hence no generation to lose (which is
     what made the old [inode_shr] return ungatherable). *)
  Definition fileread_fs_out (fn : fread_names) : iProp Σ :=
    (sb_inodestart ↦₄{frn_dqs fn}
       (mword_of_int icfg_ist : mword 32) ∗
     bslot)%I.

  (* ---- and the three, selected by the file's type ---- *)
  (* ---- KEYED ON THE DESCRIPTOR'S STATE, not on the file's content ----

     This dispatch only ever read [fc_type] and, on the device arm,
     [fc_major] -- and those are exactly what [FdSlots.fdstate] carries.  So
     the environment is a function of the state, and NOTHING above
     [file_fields] has to name an [fcontent] any more: a caller says which
     descriptor it is reading and that fixes which resources it owes. *)
  Definition fileread_env (γf : gname)
      (fn : fread_names) (st : fdstate) : iProp Σ :=
    (match st with
     | FdOpen _ _ FdPipe        => emp
     | FdOpen _ _ (FdDevice mj) => fileread_dev_env fn mj
     | FdOpen _ _ (FdInode _ _)   => fileread_fs_env γf fn
     | FdClosed             => emp
     end)%I.

  Definition fileread_env_out (fn : fread_names) (st : fdstate) : iProp Σ :=
    (match st with
     | FdOpen _ _ FdPipe        => emp
     | FdOpen _ _ (FdDevice mj) => fileread_dev_out fn mj
     | FdOpen _ _ (FdInode _ _)   => fileread_fs_out fn
     | FdClosed             => emp
     end)%I.

  (* THE EARLY RETURN'S OBLIGATION, checked here rather than discovered in
     the proof: [f->readable == 0] returns before the type is ever tested, so
     the environment must already contain everything the postcondition
     promises. *)
  Lemma fileread_fs_env_out γf fn :
    fileread_fs_env γf fn -∗ fileread_fs_out fn.
  Proof.
    rewrite /fileread_fs_env /fileread_fs_out.
    iIntros "(_ & _ & _ & _ & _ & _ & _ & _ & _ & Hsb & _ & _ & _ & Hbs)".
    iFrame "Hsb Hbs".
  Qed.

  Lemma fileread_env_out_of_env γf fn st :
    fileread_env γf fn st -∗ fileread_env_out fn st.
  Proof.
    rewrite /fileread_env /fileread_env_out.
    destruct st as [|? ? [? ?| |?]]; try by iIntros "$".
    iApply fileread_fs_env_out.
  Qed.

  (* A file that is neither a pipe, nor a device, nor an inode costs its
     reader nothing -- the arm is [panic], discharged against [SpecPanic]. *)
  Lemma fileread_env_none γf fn :
    ⊢ fileread_env γf fn FdClosed.
  Proof. done. Qed.

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
  Lemma inode_shr_gen_split2 (ik : nat) (s1 s2 : Qp) (inum : mword 32)
      (g : gname) :
    IcacheRef.inode_shr_gen ik (s1 + s2)%Qp icfg_dev inum g ⊣⊢
    IcacheRef.inode_shr_gen ik s1 icfg_dev inum g ∗
    IcacheRef.inode_shr_gen ik s2 icfg_dev inum g.
  Proof. apply IcacheRef.inode_shr_gen_split. Qed.

  (* halving, as its OWN lemma -- durable-notes' [rewrite -(Qp.div_2 q)]
     trap: written at a call site inside the proofmode the split's evar lands
     out of [s]'s scope. *)
  Lemma inode_shr_gen_halve2 (ik : nat) (s : Qp) (inum : mword 32)
      (g : gname) :
    IcacheRef.inode_shr_gen ik s icfg_dev inum g ⊣⊢
    IcacheRef.inode_shr_gen ik (s/2)%Qp icfg_dev inum g ∗
    IcacheRef.inode_shr_gen ik (s/2)%Qp icfg_dev inum g.
  Proof. rewrite -inode_shr_gen_split2 Qp.div_2. reflexivity. Qed.

  (* THE REGEN.  iunlock returns the arity-preserving [IcacheRef.inode_shr]
     (its [∃ g] form), and a payload's slice is generation-NAMED, so the two
     cannot be rejoined blind.  Any other slice of the same entry pins it
     ([IcacheRef.live_gen_agree]), and the half that was NOT lent is exactly
     such a slice -- which is why the carve lends [s/2] and keeps [s/2].
     Verbatim [ProofFilewriteParts.fw_shr_regen]. *)
  Lemma inode_shr_regen2 (ik : nat) (s1 s2 : Qp) (inum : mword 32)
      (g : gname) :
    IcacheRef.inode_shr_gen ik s1 icfg_dev inum g -∗
    IcacheRef.inode_shr ik s2 icfg_dev inum -∗
    IcacheRef.inode_shr_gen ik (s1 + s2)%Qp icfg_dev inum g.
  Proof.
    iIntros "H1 H2".
    iEval (rewrite IcacheRef.inode_shr_gen_intro) in "H2".
    iDestruct "H2" as (g2 lo2 tl2) "(%Hle2 & #Hfl2 & H2)".
    iDestruct "H1" as "(Hid1 & Hlv1 & Hs1 & Hst1)".
    iDestruct "H2" as "(Hid2 & Hlv2 & Hs2 & Hst2)".
    iAssert (IcacheRef.live_gen ik s2 g2) with "[Hlv2]" as "Hlv2";
      [by iExists lo2|].
    iDestruct (IcacheRef.live_gen_agree with "Hlv1 Hlv2") as %<-.
    rewrite /IcacheRef.inode_shr_gen IcacheRef.inode_ident_split
            IcacheRef.live_gen_split SleepLock.slh_tok_split
            IcacheRef.ic_ref_stamps_split. iFrame.
  Qed.

  (* the per-entry escrow, out of the family *)
  Lemma ic_escrows_acc2
      (ik : nat) :
    (ik < NINODE)%nat ->
    (ic_escrows fsc_ic fsc_fs fsc_ireg fsc_cov fsc_logst -∗ ic_escrow fsc_ic fsc_fs fsc_ireg fsc_cov fsc_logst ik
     : iProp Σ).
  Proof.
    iIntros (Hk) "H". rewrite /ic_escrows /ic_boxes_all /ic_escrow.
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
     rather than a second, smaller copy living in SpecFilewrite.

     THE FOURTH OUTPUT'S SIBLING IS THE OWNER'S RULING SURFACED (2026-08-29),
     and this lemma is where the file layer hands it to a syscall.  The
     payload's fifth conjunct says an FD_INODE fd's inode is not a
     T_DEVICE; it can only be read HERE, because the generation it is keyed
     on is the payload's own [fp_ig] and nothing above this carve names it.
     A caller joins the [ity_shot] output to ilock's copy with
     [IcacheRefDefs.ity_shot_agree] and the row is a FILE or a DIRECTORY --
     which is what refutes [FsAbs.abs_node]'s [ADev] arm on a write (and so
     keeps [SpecFilewrite]'s post at two arms) and gives read its
     "FdInode => AFile or ADir" tie.  The invariant-level
     statement of the same fact is [FileInvDefs.inode_pay_not_dev]. *)
  (* THE OFF OUTPUT IS TYPE-INDEXED (r25 item 24, the visibility-free
     off cell): the FD_INODE arm hands out the file's OFF BOX HANDLE
     ([FileInvDefs.off_fd] -- the box, its membership in the inode's rows,
     the register and count halves at [q], and the stamps share), and the
     FD_DEVICE arm hands out the free cell at [q].  Both come back through
     the wand at the same fraction.  The box's names [γb] are the payload's
     own [fp_obox pn], so the carve exposes them existentially: a returned
     handle at OTHER names could not be rejoined to the payload. *)
  Definition carve_off (tyc : mword 32) (k : nat) (q : Qp)
      (γb : Xv6Cameras.box_names) (γo : gname) (Cf : fcontent) : iProp Σ :=
    (if bool_decide (tyc = FD_INODE)
     then off_fd k q γb γo Cf else off_free k q)%I.

  Lemma carve_off_inode (tyc : mword 32) (k : nat) (q : Qp) γb γo Cf :
    tyc = FD_INODE -> carve_off tyc k q γb γo Cf = off_fd k q γb γo Cf.
  Proof.
    intros ->. rewrite /carve_off. case_bool_decide; [reflexivity | congruence].
  Qed.

  Lemma carve_off_dev (tyc : mword 32) (k : nat) (q : Qp) γb γo Cf :
    tyc = FD_DEVICE -> carve_off tyc k q γb γo Cf = off_free k q.
  Proof.
    intros ->. rewrite /carve_off. case_bool_decide as Hc; [|reflexivity].
    exfalso. apply (f_equal bv_unsigned) in Hc. by vm_compute in Hc.
  Qed.

  Lemma fileread_pay_carve (γf : gname) (k : nat) (q : Qp) (Cf : fcontent)
      (st : fdstate) :
    fc_type Cf = FD_INODE \/ fc_type Cf = FD_DEVICE ->
    file_pay_st γf k q Cf st -∗
    ∃ (ik : nat) (inum : mword 32) (s : Qp) (g : gname) (ty : bv 16) (lo tl : nat)
      (γb : Xv6Cameras.box_names) (γo : gname),
      (* the state's tie, read off the SAME payload record as the names
         below -- what lets a caller identify the box's shadow with the one
         its environment's permit is about ([fdstate_ok_inode_names]) *)
      ⌜fdstate_ok inum γo Cf st⌝ ∗
      ⌜fc_ip Cf = ientry ik⌝ ∗ ⌜(ik < NINODE)%nat⌝ ∗
      ⌜bv_unsigned inum < 16 * Z.of_nat icfg_nib⌝ ∗
      ⌜fc_wbool Cf = true -> bv_unsigned ty <> T_DIR_z⌝ ∗
      ⌜fc_type Cf = FD_INODE -> bv_unsigned ty <> FsImg.T_DEVICE_z⌝ ∗
      ⌜(lo <= tl)%nat⌝ ∗ IcacheRef.cred_floor lo tl ∗
      IcacheRefDefs.ity_shot g ty ∗
      IcacheRef.inode_shr_genlo ik s icfg_dev inum g lo ∗
      carve_off (fc_type Cf) k q γb γo Cf ∗
      (IcacheRef.inode_shr_genlo ik s icfg_dev inum g lo -∗
       carve_off (fc_type Cf) k q γb γo Cf -∗
         file_pay_st γf k q Cf st).
  Proof.
    intros Hty. iIntros "(%pn & %Hst & Hpn & Hpl)".
    assert (Hnp : bool_decide (fc_type Cf = FD_PIPE) = false).
    { apply bool_decide_eq_false_2.
      destruct Hty as [Hc | Hc]; rewrite Hc; by vm_compute. }
    assert (Hyes : (bool_decide (fc_type Cf = FD_INODE)
                    || bool_decide (fc_type Cf = FD_DEVICE))%bool = true).
    { destruct Hty as [Hc | Hc]; rewrite Hc.
      - by rewrite (bool_decide_eq_true_2 (FD_INODE = FD_INODE) eq_refl).
      - by rewrite (bool_decide_eq_true_2 (FD_DEVICE = FD_DEVICE) eq_refl)
                   orb_true_r. }
    rewrite {1}/file_core /file_core_noff /file_core_off Hnp Hyes /inode_pay.
    (* r25 (inode_pay D1): the reference's IDENT SIDE ([inode_ref_side])
       rides between the cancel token and the travelling share; the carve
       carries it across and puts it back. *)
    iDestruct "Hpl" as "((#Hci & Hown & Hside & Hs & Hwt) & Hop)".
    iDestruct "Hs" as (ik lo tl) "(%Hipk & %Hik & %Hinb & %Hle & #Hfl & Hshr)".
    iDestruct "Hwt" as (ty) "(#Hshot & %Hnd & %Hdv)".
    iExists ik, (fp_inum pn), (q * fp_iq pn)%Qp, (fp_ig pn), ty, lo, tl, (fp_obox pn),
      (fp_ooff pn).
    iSplitR; [done|].
    iSplitR; [done|]. iSplitR; [done|]. iSplitR; [done|]. iSplitR; [done|].
    iSplitR; [done|].
    iSplitR; [done|]. iSplitR; [iExact "Hfl"|].
    iSplitR; [iExact "Hshot"|].
    (* [iExact], not [iFrame]: both sides are the same FOLDED
       [IcacheRef.inode_shr_gen] and conversion closes it, while the [Frame]
       instance search does not see through the definition. *)
    iSplitL "Hshr"; [iExact "Hshr"|].
    (* the arm's off conjunct IS the carve at the payload's own box names *)
    iSplitL "Hop"; [iExact "Hop"|].
    iIntros "Hshr Hop". iExists pn. iFrame "%". iFrame "Hpn".
    rewrite /file_core /file_core_noff /file_core_off Hnp Hyes /inode_pay.
    iSplitR "Hop"; [| iExact "Hop"].
    iSplitR; [iExact "Hci"|]. iSplitL "Hown"; [iExact "Hown"|].
    iSplitL "Hside"; [iExact "Hside"|].
    iSplitL "Hshr".
    { iExists ik, lo, tl.
      (* NOT [iFrame "%"]: it searches the whole Coq context for each pure
         conjunct of a goal whose tail is [inode_shr_gen], and that search
         was the whole statement.  Named, each row is one [exact]. *)
      iSplitR; [iPureIntro; exact Hipk|].
      iSplitR; [iPureIntro; exact Hik|].
      iSplitR; [iPureIntro; exact Hinb|].
      iSplitR; [iPureIntro; exact Hle|].
      iSplitR; [iExact "Hfl"|].
      iExact "Hshr". }
    iExists ty. iSplitR; [iExact "Hshot"|].
    iSplit; iPureIntro; [exact Hnd | exact Hdv].
  Qed.

  (* =================================================================== *)
  (*  THE ONE INPUT AND THE ONE OUTPUT, KEYED ON THE DESCRIPTOR STATE     *)
  (* =================================================================== *)

  (* ONE SPEC PER SYSCALL.  fileread has ONE contract, over every descriptor
     kind, and what the descriptor's STATE keys is a caller-supplied INPUT
     ([fileread_in]) and an armed OUTPUT ([fileread_arms]) -- the same key
     the CODE branches on ([f->type], after the [f->readable] test).

     - an open, READABLE INODE: the observation commit at this file's inum,
       conjoined with the caller's own REFUND (the REFUNDS ruling: every
       one-shot piece is [AU /\ R], both conjuncts out of one context, the
       two carried in the one pair [PieceFam.pfam]).  Read
       has exactly ONE such piece -- one lock hold, the whole transfer inside
       it, so one instant and no chain.  The arms are
       [FsAbsReadFire.read_arms]: the receipt on a non-negative answer, the
       piece back UNSPENT on the sign guard, the FIRED receipt at advance 0
       on a copyout fault.
     - everything else -- a pipe, a device (the console read included), an
       unreadable or closed descriptor -- costs nothing and gets the landed
       blanket back.  A PIPE AU and a CONSOLE-INPUT tie are out of scope and
       deliberately not invented here; the console arm is where the
       console-input receipt will land when it does.

     THE OFFSET RIDES IN THE PIECE, BUT THE ADVANCE DOES NOT.  fileread
     advances [f->off] and the kernel owns only half of the offset's
     shadow; the commit lends the kernel's half at the offset the read used
     and takes it back UNMOVED ([FsAbsReadFire.aread_commit_at]), and the
     fire lemma advances it out of the descriptor's [foff_row], which this
     contract takes beside the input. *)
  Definition fileread_in (st : fdstate)
      (F : pfam Σ (aview -> nat -> anode -> nat -> iProp Σ)) : iProp Σ :=
    match st with
    | FdOpen true _ (FdInode i γo) =>
        pf_at (aread_commit_at (fs_gamma_L fsc_fs) appE i γo) F
    | _ => emp
    end%I.

  (* WHAT THE ARM PAYS BEYOND THE LANDED BLANKET, at the same key.  Split
     out from [fileread_arms] so [SpecSysRead] can reuse it under its own
     blanket ([sys_read_ret]) without restating the match.
     IT READS THE RESUME IMAGE [M'] AND THE DESTINATION [addr], because the
     inode arm's receipt names the bytes the call left in the caller's
     buffer ([FsAbsReadFire.read_post_ok]); the three arms that pay nothing
     ignore both. *)
  Definition fileread_extra (st : fdstate) (n : Z)
      (F : pfam Σ (aview -> nat -> anode -> nat -> iProp Σ))
      (r : mword 64) (M' : gmap Z (bv 8)) (addr : mword 64) : iProp Σ :=
    match st with
    | FdOpen true _ (FdInode i γo) =>
        read_arms (fs_gamma_L fsc_fs) i γo n F r M' addr
    | _ => emp
    end%I.

  (* ...and the whole post: the landed return clause, verbatim, PLUS the
     arm's extra.  Stating the blanket unconditionally rather than deriving
     it per arm is what makes "the unified contract implies each landed
     form" true BY CONSTRUCTION -- there is nothing to check. *)
  Definition fileread_arms (st : fdstate) (n : Z)
      (F : pfam Σ (aview -> nat -> anode -> nat -> iProp Σ))
      (r : mword 64) (M' : gmap Z (bv 8)) (addr : mword 64) : iProp Σ :=
    (⌜fileread_ret n r⌝ ∗ fileread_extra st n F r M' addr)%I.

  Lemma fileread_arms_ret st n F r M' addr :
    fileread_arms st n F r M' addr -∗ ⌜fileread_ret n r⌝.
  Proof. iIntros "[%H _]". by iPureIntro. Qed.

  (* ---- READING THE KEYED INPUT, BUILDING THE KEYED OUTPUT -------------
     One-liners, so that no walk ever has to unfold the two matches and
     every arm names the fact it is standing on. *)

  Lemma fileread_in_inode wb i γo F :
    fileread_in (FdOpen true wb (FdInode i γo)) F -∗
    pf_at (aread_commit_at (fs_gamma_L fsc_fs) appE i γo) F.
  Proof. by iIntros "$". Qed.

  Lemma fileread_extra_inode wb i γo n F r M' addr :
    read_arms (fs_gamma_L fsc_fs) i γo n F r M' addr -∗
    fileread_extra (FdOpen true wb (FdInode i γo)) n F r M' addr.
  Proof. by iIntros "$". Qed.

  (* ...and the two at a state the walk holds only through an EQUATION: a
     descriptor's shape is derived from its content, not matched on. *)
  Lemma fileread_in_inode_of (st : fdstate) (wb : bool) (i : Z) (γo : gname)
      F :
    st = FdOpen true wb (FdInode i γo) ->
    fileread_in st F -∗ pf_at (aread_commit_at (fs_gamma_L fsc_fs) appE i γo) F.
  Proof. intros ->. by iIntros "$". Qed.

  Lemma fileread_extra_inode_of (st : fdstate) (wb : bool) (i : Z) (γo : gname)
      n F r M' addr :
    st = FdOpen true wb (FdInode i γo) ->
    read_arms (fs_gamma_L fsc_fs) i γo n F r M' addr -∗
    fileread_extra st n F r M' addr.
  Proof. intros ->. by iIntros "$". Qed.

  (* the three arms that pay nothing beyond the blanket *)
  Lemma fileread_extra_pipe rb wb n F r M' addr :
    ⊢ fileread_extra (FdOpen rb wb FdPipe) n F r M' addr.
  Proof. rewrite /fileread_extra. by destruct rb. Qed.

  Lemma fileread_extra_dev rb wb (mj : Z) n F r M' addr :
    ⊢ fileread_extra (FdOpen rb wb (FdDevice mj)) n F r M' addr.
  Proof. rewrite /fileread_extra. by destruct rb. Qed.

  Lemma fileread_extra_closed n F r M' addr :
    ⊢ fileread_extra FdClosed n F r M' addr.
  Proof. done. Qed.

  (* ...at the key the WALK holds after the [f->type] branch: the descriptor's
     TYPE, not a state shape it would have to re-derive. *)
  Lemma fileread_extra_of_pipe (inum : mword 32) (γo : gname) (C : fcontent)
      (st : fdstate) n F r M' addr :
    fdstate_ok inum γo C st -> fc_type C = FD_PIPE ->
    ⊢ fileread_extra st n F r M' addr.
  Proof.
    intros Hok Ht.
    destruct (fdstate_ok_pipe inum γo C st Hok Ht) as (rb & wb & ->).
    iApply fileread_extra_pipe.
  Qed.

  Lemma fileread_extra_of_dev (inum : mword 32) (γo : gname) (C : fcontent)
      (st : fdstate) n F r M' addr :
    fdstate_ok inum γo C st -> fc_type C = FD_DEVICE ->
    ⊢ fileread_extra st n F r M' addr.
  Proof.
    intros Hok Ht.
    destruct (fdstate_ok_device inum γo C st Hok Ht) as (rb & wb & ->).
    iApply fileread_extra_dev.
  Qed.

  (* THE INODE ARM'S KEY, in one step.  Past the [f->readable] test and the
     [f->type] branch the descriptor IS the armed one, at the payload's own
     inum and offset shadow -- which is what makes the walk's commit and the
     contract's index the same [i] with nothing to bridge. *)
  Lemma fileread_st_inode_rd (inum : mword 32) (γo : gname) (C : fcontent)
      (st : fdstate) :
    fdstate_ok inum γo C st -> fc_type C = FD_INODE ->
    eq_vec (zero_extend' 64 (fc_readable C : mword 8) : mword 64)
           (zero_reg : mword 64) = false ->
    exists wb : bool, st = FdOpen true wb (FdInode (bv_unsigned inum) γo).
  Proof.
    intros Hok Ht Hrd.
    destruct (fdstate_ok_inode inum γo C st Hok Ht) as (rb & wb & Hst).
    destruct rb; [by exists wb | exfalso].
    rewrite Hst in Hok. destruct Hok as (Hr & _ & _).
    rewrite Hr in Hrd. vm_compute in Hrd. discriminate.
  Qed.

  (* the [f->readable == 0] early return: no arm of the match is armed
     there, because the only armed one is a READABLE descriptor *)
  Lemma fileread_extra_unreadable (inum : mword 32) (γo : gname)
      (C : fcontent) (st : fdstate) n F r M' addr :
    fdstate_ok inum γo C st ->
    (* the WORD the code tested, not a re-reading of it: the walk arrives
       with [beq a5,x0]'s own boolean *)
    eq_vec (zero_extend' 64 (fc_readable C : mword 8) : mword 64)
           (zero_reg : mword 64) = true ->
    ⊢ fileread_extra st n F r M' addr.
  Proof.
    destruct st as [| rb wb ty]; [by iIntros |].
    destruct rb; [| rewrite /fileread_extra; by iIntros].
    cbn. intros (Hr & _ & _) Hz. exfalso.
    rewrite Hr in Hz. vm_compute in Hz. discriminate.
  Qed.

  (* THE SIGN GUARD'S EXIT, at every arm at once.  fileread's [n < 0] test
     at +0x1a fires BEFORE the type dispatch, so this exit must answer for a
     descriptor whose kind the walk has not read yet -- and it can, for
     free: the inode arm hands the piece back UNSPENT (which is the whole
     point of the refund), and every other arm is [emp]. *)
  Lemma fileread_extra_neg st n F M' addr :
    (n < 0)%Z ->
    fileread_in st F -∗
    fileread_extra st n F (mword_of_int (-1) : mword 64) M' addr.
  Proof.
    intros Hn. destruct st as [| rb wb ty]; [by iIntros |].
    destruct rb; [| by iIntros].
    destruct ty as [i γo | | mj]; rewrite /fileread_in /fileread_extra;
      [| by iIntros | by iIntros].
    iIntros "Hc". by iApply (read_arms_neg with "Hc").
  Qed.

End SpecFileread.

Definition wp_fileread_sconf_body
    `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
      !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
 (γf : gname)                    (* kalloc, the file table  *)
    (γs : list gname) (j : nat) (γlp : gname)    (* the running process     *)
    (k : nat) (q : Qp) (st : fdstate)            (* the borrowed reference  *)
    (fn : fread_names)                           (* the heavy arms' ghosts  *)
    (pidv : mword 32) (U : ustate)
    (m : regfile) (K : nat) (eb : bool) (n : Z) (b : bool) (lks : gset string)
    (* ---- THE ARM PARAMETERS ----
       [F] is the inode arm's one-shot piece FAMILY: its [pf_recv] is the
       observation RECEIPT, its [pf_refund] is what the caller gets back on
       the one arm that does not fire.  Both are ignored by every other arm,
       so a caller that does not care instantiates [pfam_triv (fun _ _ _ _ => True%I)]. *)
    (F : pfam Σ (aview -> nat -> anode -> nat -> iProp Σ)) :=
  let pcE : mword 64 := mword_of_int KernelSyms.fileread in
  let pj := proc_addr j in
  (* a1 = addr, the user destination all three arms copy to *)
  let addr := m !!! Regidx (mword_of_int 11 : mword 5) in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  (fileread_stack <= K)%nat ->
  (k < NFILE)%nat ->
  (j < NPROC)%nat ->
  γs !! j = Some γlp ->
  length γs = NPROC ->
  (* a0 = f, a1 = addr (the user destination, never inspected here), a2 = n *)
  m !!! Regidx (mword_of_int 10 : mword 5) = fnode k ->
  m !!! Regidx (mword_of_int 12 : mword 5) = (mword_of_int n : mword 64) ->
  (* THE COUNT: AN int, AND NOTHING ELSE.  fileread is the layer a syscall
     hands unchecked user input to, so it may not ask for a SIGN and it may
     not ask for a bound -- [SpecSysRead.sys_rw_count_range] is what a
     trapframe word gives, unconditionally, and this is exactly that.
     XV6_REV 31f115a made both halves discharge-able rather than owed:
     [srliw a5,a2,0x1f ; c.bnez a5] at +0x1a is xv6's own [n < 0] test, so
     [0 <= n] is a fact of the code past the fall-through, and from
     [n < 2^31] with [off <= MAXFILE*BSIZE] readi's joint [off + n < 2^32]
     is arithmetic.  See the header. *)
  - 2 ^ 31 <= n < 2 ^ 31 ->
  (* PARKING PREMISE (hart-generic scheduler protocol): every arm sleeps. *)
  eb = true ->
  (* the order premise, at the LOWEST rank this cone touches; every
     higher one follows by [locks_below_mono]. *)
  locks_below lks "bcache" ->
  sie_cap_gpr KT1 m K b pj -∗
  (* noff = 0: everything below reaches sleep *)
  cpu_own 0%nat eb pj b lks -∗
  kernel_text -∗ kernel_data -∗ pc_is pcE -∗
  (* WHAT THE DEFAULT ARM COSTS.  [f->type] outside {FD_PIPE, FD_DEVICE,
     FD_INODE} reaches [panic("fileread")], and panic is an ordinary call:
     the literal comes out of [kernel_data] and the console credentials
     printk needs out of [panic_env].  Both are persistent and both are
     already in every caller's hand, so neither costs the caller anything. *)
  panic_env -∗
  (* the borrowed reference -- at an ARBITRARY fraction, and given back *)
  file_ref γf k q st -∗
  (* ambient, because three of the four arms copy into user memory *)
  proc_priv_core pj pidv U -∗
  kalloc_env fsc_kalloc None -∗
  procs_inv γs -∗
  (* ...and what the file's TYPE selects *)
  fileread_env γf fn st -∗
  (* THE DESCRIPTOR'S OFFSET ROW, and it is what ADVANCES [f->off].  The
     observation commit lends the shadow's kernel half at the offset the
     read used and takes it back UNMOVED (the piece-shape rule,
     design/fs-syscall-specs.md section 4), so the advance is the fire
     lemma's ([FsAbsReadFire.arf_read_fire]) and it is paid out of this
     row: [FdSlots.foff_row] at an [FdInode] IS [OffGv.off_user_inv], and
     it is [True] at every other descriptor kind.  PERSISTENT, and sys_read
     already holds it inside its descriptor bundle, so it costs the caller
     nothing. *)
  foff_row st -∗
  (* ---- THE CALLER'S INPUT, KEYED ON [st] ([fileread_in]) ----
     The observation commit conjoined with the caller's refund on an open,
     readable inode descriptor, [emp] everywhere else. *)
  fileread_in st F -∗
  (* THE CROSSING IS THE LITERAL [true], NOT [b].  This function can SLEEP
     (its bread / ilock / bwrite does), and a park moves the hart with
     interrupts off, so the crossing has nothing to do with SIE -- the
     porting guide's "a PARKING function's [wp_next] index is [true]
     UNCONDITIONALLY".  Spelled [b] the two coincide at the only instance
     the [eb = true] premise admits, which is why this went unnoticed; once
     [eb = false] is reachable the [b] form would promise the caller it
     comes back on the hart it called from, which a park makes false. *)
  wp_next true pj (fun (CID : CpuId) =>
    (* THE IMAGE MOVES, AND THE MOVE IS A WINDOW AT [addr].  All three arms
       write user memory the same way -- readi's either_copyout, and
       consoleread's / piperead's one-byte-per-round copyout -- and all
       three start at [addr], so the dispatcher's post is the arms' shared
       shape: the entry image with the run [addr .. addr+d) overwritten and
       nothing else touched.

       WHAT STAYS EXISTENTIAL IS A LENGTH AND THE BYTES, NOT AN IMAGE -- and
       on the INODE arm the receipt names the bytes: [fileread_arms] is read
       at the RESUME IMAGE and the destination, and its inode arm says the
       [d] bytes at [addr] are the observed file's bytes from the offset
       ([FsAbsReadFire.read_post_ok]).  The console and pipe arms leave them
       existential.  A caller reads its own untouched bytes back with
       [UserPtTree.umem_wr_lookup_out], which is what the shared shape is
       for. *)
  ∀ (mf : regfile) (r : mword 64) (P' : uptd) (d : nat) (bs : nat -> bv 8),
      ⌜callee_saved m mf⌝ -∗
      ⌜uptd_ext_sz (pv_sz (us_V U)) (pv_upt (us_V U)) P'⌝ -∗
      ⌜(Z.of_nat d <= Z.max 0 n)%Z⌝ -∗
      (* ...AND A NON-NEGATIVE ANSWER IS EXACTLY THE COUNT WRITTEN.  All
         three arms copy a chunk at a time and a failing copy moves none of
         the chunk it failed on, so the run is as long as the answer.  The
         -1 answer says only the bound, and for ONE arm that is not merely
         conservative: readi overwrites its running [tot] with -1 when a
         copyout faults, discarding blocks it has already delivered.  (The
         pipe and console -1s are killed-process arms, which never reach
         user mode.) *)
      ⌜r = (mword_of_int (Z.of_nat d) : mword 64)
       \/ r = (mword_of_int (-1) : mword 64)⌝ -∗
      ⌜mf !!! Regidx (mword_of_int 10 : mword 5) = r⌝ -∗
      sie_cap_gpr KT1 mf K b pj -∗
      cpu_own 0%nat eb pj b lks -∗
      pc_is ret_tgt -∗
      file_ref γf k q st -∗
      proc_priv_core pj pidv
        (upd_usM (us_upt U P') (umem_wr (us_M U) addr d bs)) -∗
      fileread_env_out fn st -∗
      (* ---- THE ARMED OUTPUT, KEYED ON [st] ([fileread_arms]) ----
         The blanket [⌜fileread_ret n r⌝], and beside it what the arm the
         descriptor selects proved: the observation's receipt -- read at
         THIS post's own resume image and destination, so it can name the
         bytes -- its unspent return or its fault reading on an inode,
         nothing anywhere else. *)
      fileread_arms st n F r (umem_wr (us_M U) addr d bs) addr -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

(* ONE MODULE TYPE: there is no parallel statement pinned to an inode, and
   no second walk against the code.  The arms are keyed on the descriptor's
   state inside this one. *)
Module Type FILEREAD.
  Parameter wp_fileread_sconf :
    forall `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
             !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
 (γf : gname)
      (γs : list gname) (j : nat) (γlp : gname)
      (k : nat) (q : Qp) (st : fdstate)
      (fn : fread_names)
      (pidv : mword 32) (U : ustate)
      (m : regfile) (K : nat) (eb : bool) (n : Z) (b : bool) (lks : gset string)
      (F : pfam Σ (aview -> nat -> anode -> nat -> iProp Σ)),
      wp_fileread_sconf_body γf γs j γlp k q st fn pidv U m K eb n b lks F.
End FILEREAD.
