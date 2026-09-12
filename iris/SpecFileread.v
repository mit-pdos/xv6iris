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

   ==== WHAT THE POSTCONDITION SAYS, AND WHERE EACH HALF COMES FROM =====

   [fileread_ret n r]: minus one, or a count between 0 and n.  That is
   [PipeInv.pipe_rw_ret] verbatim, and it is what all four arms produce.

   BEYOND THE RANGE EACH ARM PAYS WHAT ITS CALLEE CAN BACK, and
   [fileread_extra] is where that lands.  The inode arm names the BYTES the
   call left in the caller's buffer ([FsAbsReadFire.read_post_ok]'s tie,
   out of the abstract file row it fires on); the console arm names their
   TAGS ([console_receipt], out of consoleread's own ledger, which is out
   of the console ring's coupling).  A pipe and every other device major
   say nothing, and that is INHERITED rather than lost: nothing below them
   describes what they delivered.  The file's OFFSET appears on no arm --
   the borrow protocol keeps it inside the inode's ledger and no
   caller-held resource records it.

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
Require Import ObsTrace.   (* [mobs] / [obs_ends_in Uart0]: the console receipt's tags *)
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
Require Import FsAbsReadFire.    (* [aread_commit_at], [read_arms]: the one
                                    piece and its arms                       *)
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import ProcAvail.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Require Import FsCfg.   (* [fscfg]: the fs configuration is AMBIENT *)
Require Import PieceFam.        (* [pfam]: a one-shot piece's receipt beside its refund *)
Require Import FsAbsDefs.   (* LAST (FsAbs's own rule) *)
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
            !irefslotG Σ, !pavG Σ, !wchG Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.

  (* ---- the FD_DEVICE arm's environment ---- *)

  (* WHAT THE CALLEE NEEDS, as opposed to what the DISPATCH needs.  The cell
     below is how fileread finds consoleread; this is what consoleread itself
     asks for (SpecConsoleread.v) -- [cons.lock], and nothing else.  ONE
     conjunct where the write side has two ([SpecFilewrite.filewrite_dev_caps]
     also carries the UART's), because consoleread never touches the
     transmitter.  Persistent, so a caller pays for it once. *)
  Definition fileread_dev_caps (fn : fread_names) : iProp Σ :=
    is_conslock fsc_cons app_sup (frn_cons fn).

  Global Instance fileread_dev_caps_persistent fn :
    Persistent (fileread_dev_caps fn).
  Proof. apply _. Qed.

  (* ---- THE CONSOLE INVARIANT, PINNED, AND WHY THE PIN LIVES HERE ------

     The gname-free form of this bundle hid BOTH the ring's names and the
     credential the ring's dirty marker stands for, which is what kept the
     console out of every names record.  A READ cannot use that form: the
     window a read hands back is stated at the AMBIENT [fsc_cons] (the
     trap route's per-number post row has no gname parameter of its own)
     and the credential the tokenless arm pays is the application's own
     [AppInv.app_sup] -- so [SpecSysRead] takes [ConsoleInv.console_inv
     fsc_cons app_sup _], and an existential over the first two arguments
     cannot be specialised to it.

     THE PIN IS AT THIS TIER because this is the lowest file that names
     both: [ConsoleInv] sits below [FsCfg] (which carries [fsc_cons]) and
     below [AppInv] (which defines [app_sup]), and it must, since the ring
     is device state and the file system's config is not.  Only the GNAME
     stays existential -- nothing above the console names the cons lock's
     handle, and the read arm binds it once and builds its callee's names
     record around it. *)
  Definition console_ready_app : iProp Σ :=
    (∃ γ : gname, ConsoleInv.console_inv fsc_cons app_sup γ)%I.

  Global Instance console_ready_app_persistent : Persistent console_ready_app.
  Proof. rewrite /console_ready_app. apply _. Qed.

  Lemma console_ready_app_intro (γ : gname) :
    ConsoleInv.console_inv fsc_cons app_sup γ -∗ console_ready_app.
  Proof. iIntros "H". iExists γ. iExact "H". Qed.

  (* ...and the devsw half alone, which is all most consumers want *)
  Lemma console_ready_app_devsw : console_ready_app -∗ ConsoleInv.devsw_table.
  Proof. iIntros "H". iDestruct "H" as (γ) "[_ $]". Qed.

  (* ONE cell, and only when the major is in range.  The disjunction is the
     honest statement of what the kernel installs: [consoleinit] fills
     [devsw[CONSOLE]] and nothing fills any other entry, so a read slot is
     either null (and the code returns -1) or [consoleread]. *)
  (* KEYED ON THE MAJOR ITSELF, not on the file: [FdSlots.FdDevice] carries
     the number, so the descriptor's state is all a caller needs to say which
     entry it is talking about.  The lower bound joins the range test because
     the index is now a plain [Z] rather than a [bv_unsigned] -- out of range
     EITHER WAY is [emp], which is what keeps the accessor total. *)
  (* ...AND THE NON-NULL SLOT IS THE CONSOLE'S, which is a fact about the
     TABLE and has to be carried HERE (app-echo.md, lane CONS-CURSOR, C3).
     fileread branches on the CELL it loaded, so at the indirect call it
     knows only that the cell is consoleread's address; but consoleread now
     asks its caller for a PAYMENT ([ConsoleInv.cons_pay]), and the payment
     is what [fileread_in]'s console arm supplies -- at the major [CONSOLE]
     and nowhere else.  Without the tie the arm would have to pay for a
     console read it cannot recognise.  It is TRUE of the real table
     ([ConsoleInv.devsw_read_val_is_console]: nothing but consoleinit ever
     writes [devsw], and it writes one entry), and
     [fileread_devsw_of_console] is where it is discharged. *)
  Definition fileread_dev_env (fn : fread_names) (mj : Z) : iProp Σ :=
    (if decide (0 <= mj <= NDEV_max)
     then ⌜frn_rp fn mj = (zero_reg : mword 64)
           \/ (mj = CONSOLE
                /\ frn_rp fn mj
                   = (mword_of_int KernelSyms.consoleread : mword 64))⌝ ∗
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
         \/ (Z.of_nat i = CONSOLE
              /\ frn_rp fn (Z.of_nat i)
                 = (mword_of_int KernelSyms.consoleread : mword 64))⌝ ∗
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
    ConsoleInv.console_inv fsc_cons app_sup (frn_cons fn) -∗
    fileread_devsw fn.
  Proof.
    intros Hrp Hdq. iIntros "#Hci".
    iDestruct (ConsoleInv.console_inv_conslock with "Hci") as "#Hlk".
    iDestruct (ConsoleInv.console_inv_devsw with "Hci") as "#Htbl".
    rewrite /fileread_devsw /fileread_dev_caps Hrp Hdq.
    iSplitR; [iExact "Hlk" |].
    rewrite /ConsoleInv.devsw_table.
    iApply (big_sepL_impl with "Htbl").
    iModIntro. iIntros (k i Hk) "[Hr _]".
    iSplitR.
    { iPureIntro.
      destruct (ConsoleInv.devsw_read_val_cases (Z.of_nat i)) as [H0 | H1];
        [ by left
        | right; split;
          [ exact (ConsoleInv.devsw_read_val_is_console _ H1) | exact H1 ] ]. }
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
                      \/ (Z.of_nat jj = CONSOLE
                           /\ frn_rp fn (Z.of_nat jj)
                              = (mword_of_int KernelSyms.consoleread : mword 64))⌝ ∗
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
     - an open, READABLE CONSOLE (major [ConsoleInv.CONSOLE]): the
       CONSOLE RECEIPT, [console_receipt] below -- one persistent tag per
       byte the call left in the caller's buffer, out of consoleread's own
       ledger.  It costs the caller nothing to supply, because there is no
       input to arm: the tags come off the console ring, which the kernel
       already owns.
     - everything else -- a pipe, any other device major, an unreadable or
       closed descriptor -- costs nothing and gets the landed blanket back.
       A PIPE AU is out of scope and deliberately not invented here.

     THE OFFSET RIDES IN THE PIECE, BUT THE ADVANCE DOES NOT.  fileread
     advances [f->off] and the kernel owns only half of the offset's
     shadow; the commit lends the kernel's half at the offset the read used
     and takes it back UNMOVED ([FsAbsReadFire.aread_commit_at]), and the
     fire lemma advances it out of the descriptor's [foff_row], which this
     contract takes beside the input. *)
  (* ...AND THE CONSOLE ARM IS NO LONGER [emp] (app-echo.md, lane
     CONS-CURSOR, C3, and the LEASE ruling).  A read of the console is
     [ConsoleInv.cons_acc] at the application's credential [app_sup]: ONE
     ARM, whose two disjuncts are the two kinds of caller.

     A LEASE HOLDER supplies the reader token at its own cursor together
     with the wand that turns consoleread's [cons_out] into what it wants to
     know -- for sh, that the window began at ITS position, and the token
     back advanced.  A TAINTED OR GENERIC CALLER supplies [app_sup] itself,
     the credential it already holds, and owes [Rd] at every position, which
     for a caller that tracks nothing is [True].

     THAT IS WHY THERE IS NO [option] HERE ANY MORE.  The two callers differ
     in WHICH DISJUNCT they hand in, not in the shape of the deposit, so one
     leaf and one post serve both -- which the [option] could not do,
     because a post cannot name a number a premise hid under an existential
     and the [None] post was therefore [emp].  The [option] survives BELOW
     this tier, in consoleread's own contract ([ConsoleInv.cons_pay] /
     [cons_out]), where the two callers really do arrive holding different
     resources.

     THE KERNEL CANNOT MAKE CONSOLE READING EXCLUSIVE, and that is what the
     second disjunct is for: the generic slot's supply law
     ([UexecExecInst.xv6_sbundle_of_supply_ne], a FIELD of [UexecSG]'s
     class) has to produce read's deposit at every number for an ARBITRARY
     program OUT OF A PERSISTENT SUPPLY ([□ ssupply]), and an exclusive
     token is not merely absent there -- as a [□] premise it is
     inconsistent.  [ARM-c] retired [app_sup] as a credential the kernel
     NEEDED, not as one a caller may spend. *)
  (* ...AND THE WHOLE INPUT IS A WAND FROM THE CALLER'S EXIT PAYLOAD [P]
     (app-echo.md, "SH-LINE RULING", R1).  A program whose payload holds
     the console READER TOKEN cannot hand a [cons_acc] in while it is
     trapping, because the payload itself is what it hands the kernel at
     every trap ([UexecRet.uexec_pay_dep]) and it holds no second copy.
     So the deposit is a WAND: the kernel, which has just taken the
     payload off the trap's payment row, feeds it back in here, and the
     console arm returns it INSIDE what the caller asked to be told
     ([Rd]), at the position the read landed on.

     P IS THREADED THROUGH EVERY ARM, and consumed by the console arm
     alone.  On every other arm the wand hands [P] straight back, so a
     caller pays nothing for it by framing; on the console arm it is the
     resource the caller opens to find its token in, and it comes back out
     through [cons_acc]'s own wand at [fun cur dc => P ∗ Rd cur dc].
     [fileread_extra] then returns [P] to the dispatcher on every arm
     alike, which is where it goes back on the trap's resume row
     ([SpecSyscall.sysc_pay_out]).

     WHY THE ARMS ARE SPELLED OUT rather than factored through the landed
     body at a re-keyed [Rd]: the landed body's non-console arms do not
     mention [Rd] at all, so a factored form would DROP [P] there and the
     extra could not pay it back.  One match, [P] in every arm. *)
  Definition fileread_in (st : fdstate)
      (F : pfam Σ (aview -> nat -> anode -> nat -> iProp Σ))
      (Rd : nat -> nat -> iProp Σ) (P : iProp Σ) : iProp Σ :=
    (P -∗
     match st with
     | FdOpen true _ (FdInode i γo) =>
         P ∗ pf_at (aread_commit_at (fs_gamma_L fsc_fs) appE i γo) F
     | FdOpen true _ (FdDevice mj) =>
         if decide (mj = CONSOLE)
         then cons_acc fsc_cons app_sup (fun cur dc => P ∗ Rd cur dc)
         else P
     | _ => P
     end)%I.

  (* WHAT THE ARM PAYS BEYOND THE LANDED BLANKET, at the same key.  Split
     out from [fileread_arms] so [SpecSysRead] can reuse it under its own
     blanket ([sys_read_ret]) without restating the match.
     IT READS THE RESUME IMAGE [M'] AND THE DESTINATION [addr], because the
     inode arm's receipt names the bytes the call left in the caller's
     buffer ([FsAbsReadFire.read_post_ok]) and the console arm's names the
     tags of those bytes ([console_receipt]); the arms that pay nothing
     ignore both.

     THE CONSOLE ARM IS KEYED BY A [decide] ON THE MAJOR, not by a pattern:
     [FdSlots.FdDevice] carries its major as a [Z].  Resolve it through
     [fileread_extra_dev_other] / [fileread_extra_dev_console] rather than
     with a [destruct (decide ...)] at the use site -- the instance term
     baked in here is not the one a consumer elaborates, though the two
     print identically. *)
  (* =================================================================== *)
  (*  THE CONSOLE'S RECEIPT                                                *)
  (*                                                                       *)
  (*  What a process learns about the bytes a [read] on fd 0 left in its    *)
  (*  own buffer: they came off the UART, and each carries the              *)
  (*  application's persistent claim about the history it arrived at        *)
  (*  ([RiscvPtsto.riscv_rx_tag], filed beside the byte in the console      *)
  (*  ring -- ConsoleInv.v's header).  One tag per byte, in the order the   *)
  (*  bytes were copied.                                                    *)
  (*                                                                       *)
  (*  THE IMAGE, NOT A SOURCE FUNCTION.  [M'] is the image the call         *)
  (*  RESUMES at and [addr] the destination it was handed, which is the     *)
  (*  only pair a verified reader holds -- consoleread's own post is over   *)
  (*  the run's source function ([ConsoleInv.cons_tagged]) and              *)
  (*  [console_receipt_of_run] is the one step between them.                *)
  (*                                                                       *)
  (*  THE RUN'S LINEARITY IS THE CALLER'S, RECEIPT-IMAGE's convention and   *)
  (*  read_post_ok's word for word: [UserPtTree.umem_wr] is keyed by the    *)
  (*  64-bit va precisely so no kernel contract promises the destination     *)
  (*  does not wrap, and a program that owns its buffer has the run linear  *)
  (*  for free.                                                            *)
  (*                                                                       *)
  (*  -1 IS AN ARM, not a weakening: consoleread answers -1 only when the   *)
  (*  process was killed, and a killed process is never resumed in user     *)
  (*  mode, so nothing above ever reads the receipt there.  The device      *)
  (*  arm's three other exits (a null [devsw] slot, a major out of range,   *)
  (*  the [n < 0] sign guard) all answer -1 too, and take it.               *)
  (* =================================================================== *)
  (* ...AND IT IS A WINDOW, NOT A BAG (app-echo.md, lane CONS-CURSOR, C3).
     The receipt is stated at the position [cur] the ring's committed
     sequence stood at: the bytes it delivered are that sequence at
     [cur .. cur + d).  [cons_stored_lb] is the bound on the sequence --
     persistent, and any two of them agree on every index both have, so two
     successive reads by one holder of the token line up end to end -- and
     [cons_chain] is the order along it.

     [cur] IS EXISTENTIAL AND [Rd cur dc] IS WHAT PINS IT.  The caller chose
     [Rd] when it supplied [ConsoleInv.cons_acc]: a lease holder's returns
     [⌜cur = its own n⌝] beside its token back, so its window is at its own
     position and its next read begins where this one ended; a tainted or
     generic caller's returns [True] and the window is just a window.  ONE
     POST, both callers, and no [option].

     THE RECEIPT IS NOT PERSISTENT: [Rd] carries whatever the caller asked
     for, which for a lease holder is an exclusive token.  The -1 arm pays
     [Rd] at an unknown position and advance, because consoleread's killed
     exit happens INSIDE its copy loop and may have delivered bytes already;
     nothing above reads that arm (a killed process is never resumed in user
     mode). *)
  (* [P] IS THE TABLE THE CALL RAN AT -- the ENTRY descriptor the caller
     named ([pv_upt (us_V U)] at every producer).  It is here because the
     receipt is about bytes the kernel wrote into a USER buffer, and
     whether a popped byte reached that buffer is a fact about this table
     and nothing else: a destination page the kernel cannot copy to
     ([UserPtTree.uva_wmapped]) swallows it.  The arm that says so is
     consoleread's, and it lands with consoleread's own (app-echo.md,
     "SH-LINE PHASE 2 -- THE SWALLOWED BYTE", lane CONS-SWALLOW W2/W3);
     this parameter is what carries the table to it. *)
  Definition console_receipt (P : uptd) (Rd : nat -> nat -> iProp Σ)
      (r : mword 64)
      (M' : gmap Z (bv 8)) (addr : mword 64) : iProp Σ :=
    ((⌜r = (mword_of_int (-1) : mword 64)⌝ ∗
      ∃ cur d' : nat, Rd cur d')
     ∨ ∃ (d dc cur : nat) (hs : list (list mobs))
         (sl : list (list mobs * bv 8)),
         ⌜Z.of_nat d = bv_unsigned r⌝ ∗ ⌜length hs = d⌝ ∗
         (* THE PER-BYTE LEDGER, UNCONDITIONAL: the [j]th byte in the
            caller's buffer is the byte the [j]th tag's history ends in.
            True on every arm -- a concurrent reader can take away the
            ORDER of the bytes this call was handed, never the fact that
            each of them came off the UART. *)
         ⌜(forall i : nat, (i < d)%nat ->
             uint (add_vec_int addr (Z.of_nat i))
             = (uint addr + Z.of_nat i)%Z) ->
           forall j : nat, (j < d)%nat ->
             exists (h : list mobs) (b : bv 8),
               hs !! j = Some h /\ obs_ends_in Uart0 h b
               /\ M' !! uint (add_vec_int addr (Z.of_nat j))
                  = Some (cons_xlate b)⌝ ∗
         ([∗ list] h ∈ hs, riscv_rx_tag h) ∗
         cons_stored_lb fsc_cons sl ∗
         (* ...AND THE WINDOW, CONDITIONAL (SpecConsoleread.v's post says
            why).  The copy loop sleeps, and a read taken without the
            reader token is paid for with a PERSISTENT credential, so the
            kernel cannot keep a second reader out of the gap; one that
            pops there moves the ring's committed count without moving the
            cursor, and this call's bytes stop being consecutive.  What it
            leaves is the ring's marker, hence the credential -- so the
            LEFT arm is "nobody read behind your back: your [d] bytes are
            the stored sequence at [cur .. cur + d), in order, and the
            cursor moved by [d] or one more (two of consoleread's exits pop
            a byte they do not deliver)", and the RIGHT arm is the
            credential that sends the caller's continuation generic.
            The byte is quantified again here rather than shared with the
            clause above; [ObsTrace.obs_ends_in_inj] is what joins the
            two, a history naming at most one byte. *)
         (⌜forall j : nat, (j < d)%nat ->
             exists (h : list mobs) (b : bv 8),
               hs !! j = Some h /\ obs_ends_in Uart0 h b
               /\ sl !! (cur + j)%nat = Some (h, b)⌝ ∗
           ⌜length sl = (cur + d)%nat⌝ ∗ ⌜cons_chain sl⌝ ∗
           (* ...AND THE CURSOR'S EXTRA STEP IS ACCOUNTED FOR
              ([ConsoleInv.cons_swallow], relayed verbatim from
              [SpecConsoleread]'s post): at [dc = d + 1] the call popped a
              byte it did not deliver, and it hands back that byte's
              history, its tag and the reason -- [C('D')] with nothing
              delivered yet, or a copy-out that faulted at this very
              destination, which is what [P] is here for. *)
           cons_swallow fsc_cons
             (~ uva_wmapped P (uint (add_vec_int addr (Z.of_nat d)))) sl d dc
          ∨ cons_dirty_cred app_sup) ∗
         Rd cur dc)%I.

  (* the -1 arm, at every caller: whatever the caller asked for comes back,
     at a position and an advance it is not told *)
  Lemma console_receipt_m1 (P : uptd) (Rd : nat -> nat -> iProp Σ)
      (cur d' : nat)
      (M' : gmap Z (bv 8)) (addr : mword 64) :
    Rd cur d' -∗
    console_receipt P Rd (mword_of_int (-1) : mword 64) M' addr.
  Proof.
    iIntros "Hrd". rewrite /console_receipt. iLeft. iSplitR; [done|].
    iExists cur, d'. iExact "Hrd".
  Qed.

  (* THE ONE STEP FROM consoleread's POST.  Its ledger is over the run's
     SOURCE function [bs]; the image is [umem_wr M dst d bs], and
     [UserPtTree.umem_wr_lookup_in] reads the [j]th byte back out of it
     under exactly the linearity the receipt is guarded by. *)
  Lemma console_receipt_of_run (P : uptd) (M : gmap Z (bv 8)) (addr : mword 64)
      (r : mword 64) (d dc cur : nat) (bs : nat -> bv 8)
      (Rd : nat -> nat -> iProp Σ)
      (hs : list (list mobs)) (sl : list (list mobs * bv 8)) :
    Z.of_nat d = bv_unsigned r ->
    cons_window sl cur d bs hs ->
    cons_chain sl ->
    ([∗ list] h ∈ hs, riscv_rx_tag h) -∗
    cons_stored_lb fsc_cons sl -∗
    cons_swallow fsc_cons
      (~ uva_wmapped P (uint (add_vec_int addr (Z.of_nat d)))) sl d dc -∗
    Rd cur dc -∗
    console_receipt P Rd r (umem_wr M addr d bs) addr.
  Proof.
    intros Hd (Hsl & Hhl & Hwin) Hch.
    iIntros "Hts Hlb #Hsw Hrd".
    rewrite /console_receipt. iRight. iExists d, dc, cur, hs, sl.
    iSplitR; [by iPureIntro |]. iSplitR; [by iPureIntro |].
    iSplitR.
    { iPureIntro. intros Hlin j Hj.
      destruct (Hwin j Hj) as (h & b & Hsj & Hhj & Hends & Hbj).
      exists h, b. split_and!; [exact Hhj | exact Hends |].
      rewrite (umem_wr_lookup_in M addr d bs j Hj Hlin). by rewrite Hbj. }
    iFrame "Hts Hlb". iSplitR; [| iExact "Hrd"].
    iLeft. iSplitR.
    { iPureIntro. intros j Hj.
      destruct (Hwin j Hj) as (h & b & Hsj & Hhj & Hends & _).
      exists h, b. split_and!; [exact Hhj | exact Hends | exact Hsj]. }
    iSplitR; [by iPureIntro |]. iSplitR; [by iPureIntro |]. iExact "Hsw".
  Qed.

  (* ...AND THE ARM A CONCURRENT READER LEAVES.  The ring's marker was set
     while this call slept, so the bytes it delivered are not consecutive
     in the stored sequence and its own advance is not [d] or [d + 1];
     what the caller gets instead is the credential that tokenless reader
     paid, which is what sends its continuation generic.  The per-byte
     ledger is the same on both arms -- it is a statement about each byte
     and not about the run. *)
  Lemma console_receipt_of_dirty (P : uptd) (M : gmap Z (bv 8)) (addr : mword 64)
      (r : mword 64) (d dc cur : nat) (bs : nat -> bv 8)
      (Rd : nat -> nat -> iProp Σ)
      (hs : list (list mobs)) (sl : list (list mobs * bv 8)) :
    Z.of_nat d = bv_unsigned r ->
    cons_tagged bs hs d ->
    ([∗ list] h ∈ hs, riscv_rx_tag h) -∗
    cons_stored_lb fsc_cons sl -∗
    cons_dirty_cred app_sup -∗
    Rd cur dc -∗
    console_receipt P Rd r (umem_wr M addr d bs) addr.
  Proof.
    intros Hd [Hhl Htie].
    iIntros "Hts Hlb #Hcred Hrd".
    rewrite /console_receipt. iRight. iExists d, dc, cur, hs, sl.
    iSplitR; [by iPureIntro |]. iSplitR; [by iPureIntro |].
    iSplitR.
    { iPureIntro. intros Hlin j Hj.
      destruct (Htie j Hj) as (h & b & Hhj & Hends & Hbj).
      exists h, b. split_and!; [exact Hhj | exact Hends |].
      rewrite (umem_wr_lookup_in M addr d bs j Hj Hlin). by rewrite Hbj. }
    iFrame "Hts Hlb". iSplitR; [| iExact "Hrd"].
    iRight. iExact "Hcred".
  Qed.

  (* THE PROGRAM-FACING SPELLING OF THE SAME WINDOW (app-echo.md, lane
     CONS-CURSOR, C3).  [console_receipt] is stated at the kernel's RESUME
     IMAGE, which no user-tier leaf can name -- a leaf hands its caller back
     the BYTES it owns ([UkRun.ubytes] at a source function), not an image.
     So this is the receipt read at that function: the [d] bytes the call
     delivered are the stored sequence at [cur .. cur + d), their histories
     carry the application's tag, the chain says they are consecutive input
     events, and [Rd cur dc] is whatever the caller asked to be told about
     the position and the advance -- for a lease holder, that [cur] is its
     own cursor and the token is back at [cur + dc].  The bridge between the
     two forms is the leaf's own (the resume image IS the caller's run,
     written). *)
  (* [P] and [addr] are the read's own table and destination, for the one
     clause that needs them: the swallowed byte's reason
     ([ConsoleInv.cons_swallow]).  A program refutes that clause from what
     it owns of its own address space. *)
  Definition console_recv (P : uptd) (addr : mword 64)
      (Rd : nat -> nat -> iProp Σ) (d : nat)
      (g : nat -> bv 8) : iProp Σ :=
    (∃ (cur dc : nat) (hs : list (list mobs)) (sl : list (list mobs * bv 8)),
       (* the per-byte ledger, on every arm *)
       ⌜cons_tagged g hs d⌝ ∗
       ([∗ list] hh ∈ hs, riscv_rx_tag hh) ∗
       cons_stored_lb fsc_cons sl ∗
       (* ...and the WINDOW where the position is: a reader that popped
          while this call slept takes the order away and leaves the
          credential ([console_receipt]'s note).  The cursor's extra step is
          accounted for by the same [cons_swallow] the kernel receipt
          carries. *)
       (⌜cons_window sl cur d g hs⌝ ∗ ⌜cons_chain sl⌝
          ∗ cons_swallow fsc_cons
              (~ uva_wmapped P (uint (add_vec_int addr (Z.of_nat d)))) sl d dc
        ∨ cons_dirty_cred app_sup) ∗
       Rd cur dc)%I.

  (* THE ARM'S PAYOUT WITHOUT THE PAYLOAD.  This is what the PROCESS is
     told ([UexecExecInst.xv6_spost] at 5 reads exactly this), and it is
     the landed definition unchanged: the payload the read borrowed is the
     DISPATCHER's, not the process's, so it is peeled off before the post
     reaches the trap route. *)
  (* [pt] is the console arm's table and nothing else's (lane CONS-SWALLOW,
     W3): [console_receipt] is stated at the process's page table, and the
     other arms neither have one nor need one. *)
  Definition fileread_extra_core (pt : uptd) (st : fdstate) (n : Z)
      (F : pfam Σ (aview -> nat -> anode -> nat -> iProp Σ))
      (Rd : nat -> nat -> iProp Σ)
      (r : mword 64) (M' : gmap Z (bv 8)) (addr : mword 64) : iProp Σ :=
    match st with
    | FdOpen true _ (FdInode i γo) =>
        read_arms (fs_gamma_L fsc_fs) i γo n F r M' addr
    | FdOpen true _ (FdDevice mj) =>
        (* UNIFORM: the receipt is paid at every caller now, because [Rd]
           is the caller's own choice of what to be told and the [None]
           arm -- which threw the window away -- is gone. *)
        if decide (mj = CONSOLE) then console_receipt pt Rd r M' addr else emp
    | _ => emp
    end%I.

  (* ...AND WHAT THE CALLER OF THE CONTRACT GETS: that, PLUS THE PAYLOAD
     BACK, on every arm alike ([fileread_in]'s note).  The console arm
     recovers it out of [cons_acc]'s wand and the others never gave it
     away, so the return is unconditional -- which is what lets the
     dispatcher's read arm hand [SpecSyscall.sysc_pay_out] off this post
     instead of off the untouched payment row. *)
  Definition fileread_extra (pt : uptd) (st : fdstate) (n : Z)
      (F : pfam Σ (aview -> nat -> anode -> nat -> iProp Σ))
      (Rd : nat -> nat -> iProp Σ) (P : iProp Σ)
      (r : mword 64) (M' : gmap Z (bv 8)) (addr : mword 64) : iProp Σ :=
    (P ∗ fileread_extra_core pt st n F Rd r M' addr)%I.

  (* ...and the whole post: the landed return clause, verbatim, PLUS the
     arm's extra.  Stating the blanket unconditionally rather than deriving
     it per arm is what makes "the unified contract implies each landed
     form" true BY CONSTRUCTION -- there is nothing to check. *)
  Definition fileread_arms (pt : uptd) (st : fdstate) (n : Z)
      (F : pfam Σ (aview -> nat -> anode -> nat -> iProp Σ)) (Rd : nat -> nat -> iProp Σ)
      (P : iProp Σ)
      (r : mword 64) (M' : gmap Z (bv 8)) (addr : mword 64) : iProp Σ :=
    (⌜fileread_ret n r⌝ ∗ fileread_extra pt st n F Rd P r M' addr)%I.

  Lemma fileread_arms_ret (pt : uptd) st n F Rd P r M' addr :
    fileread_arms pt st n F Rd P r M' addr -∗ ⌜fileread_ret n r⌝.
  Proof. iIntros "[%H _]". by iPureIntro. Qed.

  (* the payload off the post, which is the dispatcher's whole business
     with it *)
  Lemma fileread_extra_pay (pt : uptd) st n F Rd P r M' addr :
    fileread_extra pt st n F Rd P r M' addr -∗
    P ∗ fileread_extra_core pt st n F Rd r M' addr.
  Proof. by iIntros "$". Qed.

  (* ---- READING THE KEYED INPUT, BUILDING THE KEYED OUTPUT -------------
     One-liners, so that no walk ever has to unfold the two matches and
     every arm names the fact it is standing on. *)

  Lemma fileread_in_inode wb i γo F Rd P :
    fileread_in (FdOpen true wb (FdInode i γo)) F Rd P -∗ P -∗
    P ∗ pf_at (aread_commit_at (fs_gamma_L fsc_fs) appE i γo) F.
  Proof. rewrite /fileread_in. iIntros "H HP". iApply ("H" with "HP"). Qed.

  (* [P] FIRST, before the arm's own payout: a caller [iApply]s these with
     the payload in hand and BUILDS the payout in the goal that is left,
     which is the shape the landed walks are written in. *)
  Lemma fileread_extra_inode (pt : uptd) wb i γo n F Rd P r M' addr :
    P -∗ read_arms (fs_gamma_L fsc_fs) i γo n F r M' addr -∗
    fileread_extra pt (FdOpen true wb (FdInode i γo)) n F Rd P r M' addr.
  Proof. iIntros "HP H". rewrite /fileread_extra. iFrame "HP". iExact "H". Qed.

  (* ...and the two at a state the walk holds only through an EQUATION: a
     descriptor's shape is derived from its content, not matched on. *)
  Lemma fileread_in_inode_of (st : fdstate) (wb : bool) (i : Z) (γo : gname)
      F Rd P :
    st = FdOpen true wb (FdInode i γo) ->
    fileread_in st F Rd P -∗ P -∗
    P ∗ pf_at (aread_commit_at (fs_gamma_L fsc_fs) appE i γo) F.
  Proof.
    intros ->. rewrite /fileread_in. iIntros "H HP". iApply ("H" with "HP").
  Qed.

  Lemma fileread_extra_inode_of (pt : uptd) (st : fdstate) (wb : bool) (i : Z) (γo : gname)
      n F Rd P r M' addr :
    st = FdOpen true wb (FdInode i γo) ->
    P -∗ read_arms (fs_gamma_L fsc_fs) i γo n F r M' addr -∗
    fileread_extra pt st n F Rd P r M' addr.
  Proof.
    intros ->. iIntros "HP H". rewrite /fileread_extra. iFrame "HP". iExact "H".
  Qed.

  (* the three arms that pay nothing beyond the blanket *)
  Lemma fileread_extra_pipe (pt : uptd) rb wb n F Rd P r M' addr :
    P -∗ fileread_extra pt (FdOpen rb wb FdPipe) n F Rd P r M' addr.
  Proof.
    rewrite /fileread_extra /fileread_extra_core. iIntros "HP".
    iFrame "HP". by destruct rb.
  Qed.

  (* THE DEVICE ARM, SPLIT THREE WAYS.  Every major but the console still
     pays nothing; the console pays the receipt, so a caller that has not
     resolved the major can only get out at -1. *)
  Lemma fileread_extra_dev_other (pt : uptd) rb wb (mj : Z) n F Rd P r M' addr :
    mj <> CONSOLE ->
    P -∗ fileread_extra pt (FdOpen rb wb (FdDevice mj)) n F Rd P r M' addr.
  Proof.
    intro Hmj. rewrite /fileread_extra /fileread_extra_core. iIntros "HP".
    iFrame "HP". destruct rb; [| done].
    rewrite (decide_False (P := (mj = CONSOLE)) _ _ Hmj). done.
  Qed.

  (* THE -1 ARM STILL PAYS THE CALLER BACK.  A device read that answers -1
     consumed the caller's [cons_acc] at [fileread_in]'s console arm, so the
     arm that pays nothing else still owes [Rd] -- at a position and an
     advance the caller is not told ([ConsoleInv.cons_acc_ret]: a lease
     holder gets its own token back unmoved). *)
  Lemma fileread_extra_dev_m1 (pt : uptd) rb wb (mj : Z) n F Rd P M' addr :
    fileread_in (FdOpen rb wb (FdDevice mj)) F Rd P -∗ P ==∗
    fileread_extra pt (FdOpen rb wb (FdDevice mj)) n F Rd P
        (mword_of_int (-1) : mword 64) M' addr.
  Proof.
    rewrite /fileread_extra /fileread_extra_core /fileread_in.
    destruct rb;
      [ | iIntros "H HP"; iDestruct ("H" with "HP") as "H"; iModIntro;
          by iFrame "H" ].
    case_decide as Hmj;
      [ | iIntros "H HP"; iDestruct ("H" with "HP") as "H"; iModIntro;
          by iFrame "H" ].
    iIntros "H HP". iDestruct ("H" with "HP") as "H".
    iMod (cons_acc_ret with "H") as (cur dc) "[HP Hrd]".
    iModIntro. iFrame "HP". iApply (console_receipt_m1 with "Hrd").
  Qed.

  Lemma fileread_extra_dev_console (pt : uptd) rb wb n F Rd P r M' addr :
    P -∗ console_receipt pt Rd r M' addr -∗
    fileread_extra pt (FdOpen rb wb (FdDevice CONSOLE)) n F Rd P r M' addr.
  Proof.
    iIntros "HP H". rewrite /fileread_extra /fileread_extra_core.
    iFrame "HP". destruct rb; [| done].
    case_decide as Hc; [iExact "H" | exfalso; by apply Hc].
  Qed.

  Lemma fileread_extra_closed (pt : uptd) n F Rd P r M' addr :
    P -∗ fileread_extra pt FdClosed n F Rd P r M' addr.
  Proof. rewrite /fileread_extra /fileread_extra_core. by iIntros "$". Qed.

  (* ...at the key the WALK holds after the [f->type] branch: the descriptor's
     TYPE, not a state shape it would have to re-derive. *)
  Lemma fileread_extra_of_pipe (pt : uptd) (inum : mword 32) (γo : gname) (C : fcontent)
      (st : fdstate) n F Rd P r M' addr :
    fdstate_ok inum γo C st -> fc_type C = FD_PIPE ->
    P -∗ fileread_extra pt st n F Rd P r M' addr.
  Proof.
    intros Hok Ht.
    destruct (fdstate_ok_pipe inum γo C st Hok Ht) as (rb & wb & ->).
    iApply fileread_extra_pipe.
  Qed.

  Lemma fileread_extra_of_dev_m1 (pt : uptd) (inum : mword 32) (γo : gname) (C : fcontent)
      (st : fdstate) n F Rd P M' addr :
    fdstate_ok inum γo C st -> fc_type C = FD_DEVICE ->
    fileread_in st F Rd P -∗ P ==∗
    fileread_extra pt st n F Rd P (mword_of_int (-1) : mword 64) M' addr.
  Proof.
    intros Hok Ht.
    destruct (fdstate_ok_device inum γo C st Hok Ht) as (rb & wb & ->).
    iIntros "Hrd HP". iApply (fileread_extra_dev_m1 with "Hrd HP").
  Qed.

  (* the majors that pay nothing, at the same key *)
  Lemma fileread_extra_of_dev_other (pt : uptd) (inum : mword 32) (γo : gname)
      (C : fcontent) (st : fdstate) n F Rd P r M' addr :
    fdstate_ok inum γo C st -> fc_type C = FD_DEVICE ->
    bv_unsigned (fc_major C) <> CONSOLE ->
    P -∗ fileread_extra pt st n F Rd P r M' addr.
  Proof.
    intros Hok Ht Hmj.
    destruct (fdstate_ok_device inum γo C st Hok Ht) as (rb & wb & Hst).
    rewrite Hst.
    iApply (fileread_extra_dev_other pt rb wb _ n F Rd P r M' addr Hmj).
  Qed.

  (* ...and the console's, at the key the walk holds after the [f->type]
     branch and the [devsw] load: the major it resolved IS [CONSOLE]. *)
  Lemma fileread_extra_of_dev_console (pt : uptd) (inum : mword 32) (γo : gname)
      (C : fcontent) (st : fdstate) n F Rd P r M' addr :
    fdstate_ok inum γo C st -> fc_type C = FD_DEVICE ->
    bv_unsigned (fc_major C) = CONSOLE ->
    P -∗ console_receipt pt Rd r M' addr -∗
    fileread_extra pt st n F Rd P r M' addr.
  Proof.
    intros Hok Ht Hmj. iIntros "HP H".
    destruct (fdstate_ok_device inum γo C st Hok Ht) as (rb & wb & Hst).
    rewrite Hmj in Hst. rewrite Hst.
    iApply (fileread_extra_dev_console pt rb wb n F Rd P r M' addr with "HP H").
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

  (* ...AND ITS DEVICE TWIN, which the console arm needs for the same
     reason: past the [f->readable] test the descriptor is OPEN and
     READABLE, which is the only shape [fileread_in]'s device arm is armed
     at. *)
  Lemma fileread_st_device_rd (inum : mword 32) (γo : gname) (C : fcontent)
      (st : fdstate) :
    fdstate_ok inum γo C st -> fc_type C = FD_DEVICE ->
    eq_vec (zero_extend' 64 (fc_readable C : mword 8) : mword 64)
           (zero_reg : mword 64) = false ->
    exists wb : bool, st = FdOpen true wb (FdDevice (bv_unsigned (fc_major C))).
  Proof.
    intros Hok Ht Hrd.
    destruct (fdstate_ok_device inum γo C st Hok Ht) as (rb & wb & Hst).
    destruct rb; [by exists wb | exfalso].
    rewrite Hst in Hok. destruct Hok as (Hr & _ & _).
    rewrite Hr in Hrd. vm_compute in Hrd. discriminate.
  Qed.

  (* THE CONSOLE ARM'S ACCESSOR, read off the keyed input at the major the
     walk has just learned is [CONSOLE] ([fileread_dev_env]'s tie).  ONE
     step, so the walk never unfolds the [decide]. *)
  Lemma fileread_in_dev_console (st : fdstate) (wb : bool) (mj : Z) F Rd P :
    st = FdOpen true wb (FdDevice mj) -> mj = CONSOLE ->
    fileread_in st F Rd P -∗ P -∗
    cons_acc fsc_cons app_sup (fun cur dc => P ∗ Rd cur dc).
  Proof.
    intros -> ->. rewrite /fileread_in.
    case_decide as Hc; [| exfalso; by apply Hc].
    iIntros "H HP". iApply ("H" with "HP").
  Qed.

  (* the [f->readable == 0] early return: no arm of the match is armed
     there, because the only armed one is a READABLE descriptor *)
  Lemma fileread_extra_unreadable (pt : uptd) (inum : mword 32) (γo : gname)
      (C : fcontent) (st : fdstate) n F Rd P r M' addr :
    fdstate_ok inum γo C st ->
    (* the WORD the code tested, not a re-reading of it: the walk arrives
       with [beq a5,x0]'s own boolean *)
    eq_vec (zero_extend' 64 (fc_readable C : mword 8) : mword 64)
           (zero_reg : mword 64) = true ->
    P -∗ fileread_extra pt st n F Rd P r M' addr.
  Proof.
    rewrite /fileread_extra /fileread_extra_core.
    destruct st as [| rb wb ty]; [by iIntros (? ?) "$" |].
    destruct rb; [| by iIntros (? ?) "$"].
    cbn. intros (Hr & _ & _) Hz. exfalso.
    rewrite Hr in Hz. vm_compute in Hz. discriminate.
  Qed.

  (* THE SIGN GUARD'S EXIT, at every arm at once.  fileread's [n < 0] test
     at +0x1a fires BEFORE the type dispatch, so this exit must answer for a
     descriptor whose kind the walk has not read yet -- and it can, for
     free: the inode arm hands the piece back UNSPENT (which is the whole
     point of the refund), and every other arm is [emp]. *)
  Lemma fileread_extra_neg (pt : uptd) st n F Rd P M' addr :
    (n < 0)%Z ->
    fileread_in st F Rd P -∗ P ==∗
    fileread_extra pt st n F Rd P (mword_of_int (-1) : mword 64) M' addr.
  Proof.
    intros Hn. rewrite /fileread_in /fileread_extra /fileread_extra_core.
    destruct st as [| rb wb ty];
      [ iIntros "H HP"; iDestruct ("H" with "HP") as "H"; iModIntro;
        by iFrame "H" | ].
    destruct rb;
      [ | iIntros "H HP"; iDestruct ("H" with "HP") as "H"; iModIntro;
          by iFrame "H" ].
    destruct ty as [i γo | | mj].
    - iIntros "H HP". iDestruct ("H" with "HP") as "[HP Hc]".
      iModIntro. iFrame "HP". by iApply (read_arms_neg with "Hc").
    - iIntros "H HP". iDestruct ("H" with "HP") as "H". iModIntro.
      by iFrame "H".
    - case_decide;
        [ | iIntros "H HP"; iDestruct ("H" with "HP") as "H"; iModIntro;
            by iFrame "H" ].
      iIntros "H HP". iDestruct ("H" with "HP") as "H".
      iMod (cons_acc_ret with "H") as (cur dc) "[HP Hrd]".
      iModIntro. iFrame "HP". iApply (console_receipt_m1 with "Hrd").
  Qed.

End SpecFileread.

(* THE PIN'S TRANSPORT.  [console_ready_app] rides the park exactly as the
   gname-free form did ([SyscParkEnv.park_world],
   [UsertrapRes.park_globals]), so it needs a [CtxMorph]; below the
   section that binds the ambient context, for the reason
   [ConsoleInv]'s own morph section gives. *)
Section FilereadConsoleMorph.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Global Instance console_ready_app_morph :
    CtxMorph (λ ξ0 : TsoCtx.CtxId, console_ready_app (XI := ξ0)).
  Proof.
    iIntros (ξ ξ') "Hd H". rewrite /console_ready_app.
    iDestruct "H" as (γ) "H".
    iMod (ConsoleInv.console_inv_morph fsc_cons app_sup γ ξ ξ' with "Hd H")
      as "[Hd H]".
    iModIntro. iFrame "Hd". iExists γ. iExact "H".
  Qed.

End FilereadConsoleMorph.

Definition wp_fileread_sconf_body
    `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
      !irefslotG Σ, !pavG Σ, !wchG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
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
    (F : pfam Σ (aview -> nat -> anode -> nat -> iProp Σ))
    (* WHAT THE CALLER ASKS TO BE TOLD ABOUT THE CONSOLE WINDOW (app-echo.md,
       lane CONS-CURSOR, C3, and the LEASE ruling).  The console arm takes
       [ConsoleInv.cons_acc fsc_cons app_sup Rd] -- one arm, two disjuncts --
       and pays [Rd cur dc] at the position the ring's committed sequence
       stood at and the advance the cursor made.  A lease holder instantiates
       [Rd] with "[cur] is my own [n], and here is my token back"; a tainted
       or generic caller with [fun _ _ => True], which is what the GENERIC
       slot's supply law pays ([FsAbsInvFire.fsabs_fileread_in]). *)
    (Rd : nat -> nat -> iProp Σ)
    (* THE CALLER'S EXIT PAYLOAD, BORROWED ACROSS THE CALL (app-echo.md,
       "SH-LINE RULING", R1).  The dispatcher holds it off the trap's
       payment row ([SpecSyscall.sysc_pay_in]); it lends it here, the
       console arm spends it to open the caller's [cons_acc] and the post
       gives it back on every arm ([fileread_extra]).  A caller that
       tracks nothing takes [P := True]. *)
    (P : iProp Σ) :=
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
  fileread_in st F Rd P -∗
  (* ...AND THE PAYLOAD THE INPUT IS A WAND FROM, lent for the call and
     returned in the post. *)
  P -∗
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
      fileread_arms (pv_upt (us_V U)) st n F Rd P r (umem_wr (us_M U) addr d bs) addr -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

(* ONE MODULE TYPE: there is no parallel statement pinned to an inode, and
   no second walk against the code.  The arms are keyed on the descriptor's
   state inside this one. *)
Module Type FILEREAD.
  Parameter wp_fileread_sconf :
    forall `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
             !irefslotG Σ, !pavG Σ, !wchG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
 (γf : gname)
      (γs : list gname) (j : nat) (γlp : gname)
      (k : nat) (q : Qp) (st : fdstate)
      (fn : fread_names)
      (pidv : mword 32) (U : ustate)
      (m : regfile) (K : nat) (eb : bool) (n : Z) (b : bool) (lks : gset string)
      (F : pfam Σ (aview -> nat -> anode -> nat -> iProp Σ)) (Rd : nat -> nat -> iProp Σ)
      (P : iProp Σ),
      wp_fileread_sconf_body γf γs j γlp k q st fn pidv U m K eb n b lks F
        Rd P.
End FILEREAD.
