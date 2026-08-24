(* SpecFileclose.v -- the public interface of fileclose, stated independently
   of its proof.  Requires only the definitional layer -- never a
   whole-function proof file -- so every function proof can be checked in
   parallel.

     void fileclose(struct file *f) {
       struct file ff;
       acquire(&ftable.lock);
       if (f->ref < 1) panic("fileclose");
       if (--f->ref > 0) { release(&ftable.lock); return; }
       ff = *f;
       f->ref = 0;
       f->type = FD_NONE;
       release(&ftable.lock);
       if (ff.type == FD_PIPE) pipeclose(ff.pipe, ff.writable);
       else if (ff.type == FD_INODE || ff.type == FD_DEVICE) {
         begin_op(); iput(ff.ip); end_op();
       }
     }

   ==== THE REFERENCE HALF ===============================================

   The simple half, and it is stable: a reference goes in, one [fd_slot]
   comes back, and nothing says which arm ran.  Deliberately so -- the caller
   neither knows nor cares whether it held the last reference.  It is
   entirely [FileInv]'s two close steps:

   * [--f->ref > 0] (file_close_step + file_rest_absorb): the departing
     reference's fraction -- of the content cells, of the payload-names field
     and of the payload itself -- is absorbed back into the invariant's
     leftover.  That the fraction has somewhere to GO is why the authority's
     frac component tracks outstanding fraction rather than being pinned at 1.
   * [--f->ref == 0] (file_close_last_step + file_rest_join): the COUNT
     component forces this closer to hold every share ever handed out
     ([positiveR] has no unit), and the invariant's leftover makes it fraction
     ONE of the whole slot.  That is what licenses the unlocked-looking
     [ff = *f] read and the [f->type = FD_NONE] store, and -- the point of the
     payload link -- it is what puts a WHOLE pipe end, or a whole inode
     reference, in fileclose's hands to give to pipeclose / iput.

   Note the ORDER the C code uses and the model needs: [f->type = FD_NONE] is
   written, and the lock released, BEFORE the payload is spent.  At FD_NONE
   the payload is [emp], so what goes back into the table is the slot with no
   payload while the closer walks away with it.

   The [f->ref < 1] panic arm is dead for the same reason as filedup's: the
   caller's [file_ref] puts slot k in the authority's domain with a positive
   count, and [FileInv.fref_word_spos] turns that into "the sign-extended
   load is signed-positive", which is exactly what [blez] tests.

   ==== THE OTHER HALF: WHAT THE LAST-REFERENCE ARM COSTS ================

   fileclose can free a pipe's page, and it can do disk I/O and SLEEP.  Its
   callers must own the corresponding fabric, and there is no honest way to
   hide that.  What they must own depends on the TYPE of the file, because
   the type is what selects the arm -- so the environment is indexed by it
   ([fileclose_env] / [fileclose_env_out]) rather than being the union:

   * FD_PIPE   -> pipeclose's: the kmem lock and the page count (the page
                  comes back iff this was the pipe's last end), plus
                  [procs_inv] for the wakeup inside it.
   * FD_INODE
     / FD_DEVICE -> begin_op / iput / end_op's: the whole log + buffer-cache
                  + disk fabric, the running-thread bundle, and the parking
                  premise.  The log RESERVATION is not among them: begin_op
                  mints it and end_op retires it, so an operation's budget
                  never crosses fileclose's boundary.
   * FD_NONE   -> nothing at all.

   That last line is not a curiosity: it is what keeps pipealloc's failure
   path cheap.  pipealloc closes files it has just allocated and not yet
   typed ([SpecFilealloc]'s post pins [fc_type Cf = FD_NONE]), so it owns no
   file system and is not asked for one.  sys_pipe closes FD_PIPE files and
   is asked only for the pipe fabric it already has.  Only a caller closing a
   file of UNKNOWN type -- sys_close, kexit -- pays for both, which is the
   truth about closing an arbitrary descriptor.

   The type-indexing also decides the pure side conditions: pipeclose wants
   one more level of lock nesting than fileclose's own acquire, and the FS
   calls want [noff = 0] and the hart-generic parking premise.  Each sits in
   the arm that needs it.

   The ghost names and geometry both arms are indexed by are bundled into one
   [fclose_names], with an [Inhabited] instance, so that a caller which
   cannot reach either arm passes [inhabitant] rather than having to invent a
   [bio_names] it has never heard of.

   WHAT COMES BACK: one [fd_slot], plus the arm's own returns.  The fd slot
   is not a decoration -- it is the return leg of the conservation law that
   makes filedup's unchecked [f->ref++] safe (FdSlots.v /
   design/file-table.md).  [ftable_res] holds one unit per outstanding
   reference, so destroying a reference releases exactly one, whichever arm
   ran: at [n >= 2] the slot's [fd_slots n] shrinks to [fd_slots (n-1)], and
   at [n = 1] the whole entry leaves the authority.  The caller needs it:
   sys_close's descriptor is empty afterwards, and an empty
   [ProcInv.ofile_slot] owns its unit itself. *)
From Stdlib Require Import Eqdep_dec ZArith Lia List.
From stdpp Require Import gmap list list_monad bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import excl auth gmap frac numbers.
From iris.base_logic.lib Require Import ghost_var gen_heap invariants ghost_map.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import InstrBytes.
Require Import KernelText.
Require Import RegFile WpNext.
Require Import RiscvExtras.
Require Import CalleeSaved.
Require Import FdSlots FileInv.
Require Import KallocInv.
Require Import WpLock.
Require Import KernelDataInv.
Require Import SpecPanic.
Require Import IntrDefs.
Require Import CpuOwn.
Require Import ProcGeom.
Require Import SchedCtx.
Require Import WpUart.
Require Import DiskPtsto DiskInv.
Require Import BioDefs.
Require Import FsBlocks LogInv.
Require Import BitmapInv.
Require Import IrefSlots.
Require Import IcacheRef.
Require Import IcacheEscrow.
Require Import SpecEndOp.
From Kernel Require KernelSyms.
Require Import ProcAvail.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Require Import ProcDefs.  (* [pprivate], [proc_priv_bare] *)
Require Import FsCfg.     (* the ambient fs names [fs_ready] is stated at *)
Require Import FsReady.   (* [fs_ready], the fs world a closer holds *)
Local Open Scope Z_scope.


(* fileclose's own frame is 8 slots ([addi sp,sp,-64]: ra, s0..s5 saved), and
   its deepest callee is end_op ([SpecEndOp.K_end_op] = 76, sized by
   write_head / install_trans under bread).  iput (72, itself sized by bread
   under itrunc) is just below it; begin_op 26, pipeclose 22,
   acquire/release 10.  end_op OVERTOOK iput when the panic budget landed.  A CONSTANT, not a per-arm bound: the stack a
   function may need is a property of the function (durable-notes.md). *)
Notation fileclose_stack := ((8 + K_end_op)%nat) (only parsing).
(* ---------------------------------------------------------------------- *)
(* The ghost names and geometry the last-reference arm's callees are        *)
(* indexed by, in one bundle.                                              *)
(* ---------------------------------------------------------------------- *)
Record fclose_names := MkFCloseNames {
  fcn_procs    : list gname;      (* the proc table's per-slot lock names   *)
  fcn_j        : nat;             (* the running process's index            *)
  fcn_plock    : gname;
  fcn_kmem     : gname;           (* kmem.lock                              *)
  fcn_kalloc   : gname * gname;
  fcn_uart     : uart_names;
  fcn_disk     : disk_names;
  fcn_dlock    : gname;           (* virtio_disk.lock                       *)
  fcn_pd       : mword 64;
  fcn_pav      : mword 64;
  fcn_pu       : mword 64;
  fcn_bio      : bio_names;
  fcn_log      : log_names;
  fcn_fs       : fs_names;
  fcn_cov      : gset Z;
  fcn_logstart : Z;
  fcn_dev      : mword 32;
  fcn_pid      : mword 32;        (* the caller's own pid cell              *)
  fcn_dq       : dfrac;
  (* ---- C6b: iput's own indices.  Everything below is the INODE CACHE and
     the two file-system regions its truncate arm reaches -- the inode
     region it frees a dinode into, and the bitmap it frees blocks into.
     They are fields rather than parameters for the same reason the rest
     are: one equation at the caller ([SpecKexit]'s [fn = MkFCloseNames
     ...]) instead of a dozen coherence conjuncts. *)
  fcn_ireg     : gname;           (* the inode region's ghost (iput's [gi]) *)
  fcn_ic       : ic_names;        (* the icache's names                     *)
  fcn_tlock    : gname;           (* itable.lock                            *)
  fcn_bmapstart : Z;
  fcn_inodestart : Z;
  fcn_nib      : nat;             (* inode blocks in the region             *)
  fcn_size     : Z;               (* the bitmap's covered size              *)
}.

(* Spelled out rather than derived: several of these records have no
   [Inhabited] instance of their own, and [bio_names] has function fields.
   Nothing reads these values -- the arm they belong to is unreachable for
   the caller that passes them -- so any closed term does. *)
Global Instance fclose_names_inhabited : Inhabited fclose_names :=
  populate (MkFCloseNames
    [] 0%nat 1%positive 1%positive (1%positive, 1%positive)
    (UartNames 1%positive 1%positive 1%positive 1%positive)
    (DiskNames 1%positive 1%positive 1%positive 1%positive 1%positive 1%positive
               1%positive 1%positive)
    1%positive
    (mword_of_int 0) (mword_of_int 0) (mword_of_int 0)
    (MkBioNames 1%positive 1%positive
       (fun _ => (1%positive, 1%positive)) (fun _ => 1%positive)
       (fun _ => 1%positive))
    (MkLogNames 1%positive 1%positive 1%positive 1%positive 1%positive)
    (MkFsNames 1%positive 1%positive 1%positive 1%positive 1%positive)
    ∅ 0 (mword_of_int 0) (mword_of_int 0) (DfracOwn 1)
    1%positive
    (MkIcNames (fun _ => 1%positive) (fun _ => 1%positive)
               (fun _ => 1%positive))
    1%positive 0 0 0%nat 0).

Section SpecFileclose.
  (* NOTE [icacheG] is NOT here: [fileG] carries it (FileInv.v's header --
     two instance paths print identically and do not unify), and iput's
     contract is applied at the one that comes with the file table. *)
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ, !irefslotG Σ, !pavG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  (* ---- the FD_PIPE arm's environment: pipeclose's ---- *)
  (* [on] is a PARAMETER rather than a field of [fclose_names], because it is
     the one thing that moves: a caller closing descriptor after descriptor
     (kexit) carries it existentially while everything else stays fixed. *)
  Definition fileclose_pipe_env (fn : fclose_names)
      (on : option nat) (n : nat) : iProp Σ :=
    (⌜(Z.of_nat n + 2 < 2 ^ 31)%Z⌝ ∗
     procs_inv (fcn_procs fn) ∗
     is_lock (fcn_kmem fn) (mword_of_int KernelSyms.kmem) "kmem"%string
       (kmem_res (fcn_kalloc fn) (mword_of_int (KernelSyms.kmem + 24))) ∗
     kalloc_avail (fcn_kalloc fn) on)%I.

  (* the page came back iff this was the pipe's LAST end; the caller cannot
     tell, and does not need to. *)
  Definition fileclose_pipe_out (fn : fclose_names) (on : option nat) : iProp Σ :=
    (kalloc_avail (fcn_kalloc fn) on ∨
     kalloc_avail (fcn_kalloc fn) (avail_inc on))%I.

  (* ---- the FD_INODE / FD_DEVICE arm's environment: begin_op / iput /
         end_op's, which is the whole file system ---- *)

  (* EVERY ENTRY'S SLEEPLOCK, as one persistent family.  iput names the ONE
     slot it was handed, but a closer of an ARBITRARY descriptor does not
     know which entry the file points at -- the payload tells it only that
     there is one -- so what its contract can carry is the family, exactly
     as [IcacheEscrow.ic_escrows] is the family of escrows for the same
     reason.  The two lock gnames are existential because nothing above the
     cache names them and [is_sleeplock] is persistent, so the ∃ is free. *)
  (* [ic_sleeplocks] -- EVERY ENTRY'S INODE SLEEPLOCK, as one persistent
     family -- lives in [IcacheEscrow.v], with its accessor
     [ic_sleeplocks_lookup]: nothing in it is file- or directory-shaped, and
     a *function spec* owning a definition the invariant layer needs is what
     put [ProcInv] into [FsReady]'s dependency cone. *)

  Lemma ic_escrows_acc (cn : ic_names) (γfs : fs_names) (γi : gname)
      (cov : gset Z) (logstart : Z) (k : nat) :
    (k < NINODE)%nat ->
    (ic_escrows cn γfs γi cov logstart -∗ ic_escrow cn γfs γi cov logstart k
     : iProp Σ).
  Proof.
    iIntros (Hk) "H". rewrite /ic_escrows.
    assert (Hl : seq 0 NINODE !! k = Some k) by (rewrite lookup_seq; lia).
    iDestruct (big_sepL_lookup _ _ k k Hl with "H") as "$".
  Qed.

  (* THE FILE SYSTEM, AS A CLOSER SEES IT: [FsReady.fs_ready] -- the one
     persistent, parameter-free predicate every runtime fs caller holds --
     beside the TIES that say [fn]'s own names ARE the ambient ones.  This
     is [FsSyscalls.fs_world]'s idiom at [fclose_names]' fields: a record so
     a proof destructs it once and rewrites.  Every fs fact the last-
     reference arm's callees want -- the block/log fabric, the icache's
     four, the inode region and its sealed regime, the superblock cells at
     [□], the block bitmap's invariant, the image's arithmetic -- is a
     projection of [fs_ready] after the rewrite; nothing fs-shaped is
     restated here.  fileclose is unreachable pre-seal (it is a process-
     level function), so taking [fs_ready] is the adoption audit's
     "ALREADY DONE" row, not its "MUST NOT" one (fs-ghost-state.md §7d). *)
  Record fclose_ties (fn : fclose_names) : Prop := MkFCloseTies {
    fct_uart   : fcn_uart fn = fsc_uart;
    fct_disk   : fcn_disk fn = fsc_disk;
    fct_dlock  : fcn_dlock fn = fsc_dlock;
    fct_kmem   : fcn_kmem fn = fsc_kalloc;
    fct_kalloc : fcn_kalloc fn = fsc_kpages;
    fct_bio    : fcn_bio fn = fsc_bio;
    fct_log    : fcn_log fn = icfg_log;
    fct_fs     : fcn_fs fn = fsc_fs;
    fct_cov    : fcn_cov fn = fsc_cov;
    fct_logst  : fcn_logstart fn = fsc_logst;
    fct_dev    : fcn_dev fn = icfg_dev;
    fct_ireg   : fcn_ireg fn = fsc_ireg;
    fct_ic     : fcn_ic fn = fsc_ic;
    fct_tlock  : fcn_tlock fn = fsc_itlock;
    fct_bms    : fcn_bmapstart fn = fsc_bmapstart;
    fct_ist    : fcn_inodestart fn = icfg_ist;
    fct_nib    : fcn_nib fn = icfg_nib;
    fct_size   : fcn_size fn = fsc_size;
  }.

  (* the bundle WITHOUT the caller's pid cell.  kexit closes every
     descriptor in a loop while holding [proc_priv], and the pid cell the FS
     calls want is INSIDE that block -- so its loop carries this, and pairs it
     with the quarter [ProcInv.proc_priv_pid_ofile] lends for the duration of
     one call. *)
  Definition fileclose_fs_env_nopid (fn : fclose_names)
      (n : nat) (eb : bool) (p : mword 64) : iProp Σ :=
    (* [⌜eb = true⌝] USED TO BE HERE, and is now the TOP-LEVEL complement
       on [wp_fileclose_sconf_body] instead.  It cannot live in this bundle:
       a caller closing a PIPE descriptor frames the FS bundle across the
       call rather than handing it over, and fileclose's crossing is the
       literal [true] on every arm -- so anything hart-indexed left in here
       would have to be transported to an arbitrary hart with no chain fact
       to do it with.  The complement is handed in and given back on EVERY
       arm instead.  See claude-notes/completed/eb-generic-sweep.md. *)
    (⌜(n = 0)%nat⌝ ∗ ⌜p = proc_addr (fcn_j fn)⌝ ∗
     ⌜(fcn_j fn < NPROC)%nat⌝ ∗
     ⌜fcn_procs fn !! fcn_j fn = Some (fcn_plock fn)⌝ ∗
     ⌜fclose_ties fn⌝ ∗
     procs_inv (fcn_procs fn) ∗
     (* NO disk-fabric rows: [fs_ready]'s own disk conjunct quantifies the
        three ring pages, and the inode arm runs at THAT witness -- rows at
        [fcn_pd]/[fcn_pav]/[fcn_pu] were dead weight every caller paid and
        no callee read. *)
     FsReady.fs_ready ∗
     bslots 3)%I.

  (* THE PID CELL IS GONE FROM THIS BUNDLE, and with it the whole
     nopid/withpid pair.  It was here because iput reaches acquiresleep,
     which records its holder ([lk->pid = myproc()->pid]) -- and a bundle is
     the wrong place for a piece of the caller's process block: a caller
     holding [ProcInv.proc_priv] and this side by side was asking for three
     quarters of [p->pid], of which two are reachable.  sys_close and
     sys_pipe both shipped with exactly that.

     acquiresleep now takes [ProcDefs.proc_priv_bare] and does its own
     borrowing, so what fileclose needs is the block, and it takes it as a
     row of its own contract rather than smuggling a fraction through the
     file system's environment.  A caller that tried the old thing now gets
     a REFUTABLE premise set rather than a silently unpayable one: two
     copies of the block are [p->pid] at one whole, and the lock invariant's
     half refutes it. *)
  Definition fileclose_fs_env (fn : fclose_names)
      (n : nat) (eb : bool) (p : mword 64) : iProp Σ :=
    fileclose_fs_env_nopid fn n eb p.

  Lemma fileclose_fs_env_nopid_eq fn n eb p :
    fileclose_fs_env fn n eb p ⊣⊢ fileclose_fs_env_nopid fn n eb p.
  Proof. reflexivity. Qed.

  Definition fileclose_fs_out (fn : fclose_names) : iProp Σ :=
    (* the slots alone.  ([iput]'s [iref_slot] give-back is NOT here for the
       same reason one level up: it comes back only on the arm that ran,
       and fileclose's postcondition cannot see which did.  Dropping it
       leaks one unit of the [IrefSlots] supply per inode file closed --
       recorded as owed in claude-notes/projects/fs-icache.md.) *)
    bslots 3.

  (* ---- and the two, selected by the file's type ---- *)
  Definition fileclose_env (fn : fclose_names)
      (on : option nat) (n : nat) (eb : bool) (p : mword 64)
      (Cf : fcontent) : iProp Σ :=
    (if bool_decide (fc_type Cf = FD_PIPE)
     then fileclose_pipe_env fn on n
     else if bool_decide (fc_type Cf = FD_INODE)
               || bool_decide (fc_type Cf = FD_DEVICE)
     then fileclose_fs_env fn n eb p
     else emp)%I.

  Definition fileclose_env_out (fn : fclose_names) (on : option nat)
      (Cf : fcontent) : iProp Σ :=
    (if bool_decide (fc_type Cf = FD_PIPE)
     then fileclose_pipe_out fn on
     else if bool_decide (fc_type Cf = FD_INODE)
               || bool_decide (fc_type Cf = FD_DEVICE)
     then fileclose_fs_out fn
     else emp)%I.

  (* A file that is neither a pipe nor an inode costs its closer nothing.
     This is the lemma pipealloc's two error-path calls are discharged by --
     [SpecFilealloc]'s post already pins the type. *)
  Lemma fileclose_env_none fn on n eb p Cf :
    fc_type Cf = FD_NONE -> ⊢ fileclose_env fn on n eb p Cf.
  Proof.
    intro Ht. rewrite /fileclose_env Ht.
    rewrite bool_decide_eq_false_2; [|by vm_compute].
    rewrite bool_decide_eq_false_2; [|by vm_compute].
    rewrite bool_decide_eq_false_2; [|by vm_compute].
    done.
  Qed.

  (* EACH BUNDLE ALREADY CONTAINS WHAT IT PROMISES BACK.  Two facts, and both
     are checks rather than conveniences: they are what catches a bundle
     stated with one of its returns going the wrong way. *)
  Lemma fileclose_pipe_env_out fn on n :
    fileclose_pipe_env fn on n -∗ fileclose_pipe_out fn on.
  Proof.
    rewrite /fileclose_pipe_env /fileclose_pipe_out.
    iIntros "(_ & _ & _ & Hav)". by iLeft.
  Qed.

  Lemma fileclose_fs_env_out fn n eb p :
    fileclose_fs_env fn n eb p -∗ fileclose_fs_out fn.
  Proof.
    rewrite /fileclose_fs_env /fileclose_fs_env_nopid /fileclose_fs_out.
    iIntros "(_ & _ & _ & _ & _ & _ & _ & Hbs)".
    iExact "Hbs".
  Qed.

  (* THE FAST PATH'S OBLIGATION, checked here rather than discovered in the
     proof: when [--f->ref > 0] fileclose returns without touching any of it,
     so the environment must already contain everything the postcondition
     promises. *)
  Lemma fileclose_env_out_of_env fn on n eb p Cf :
    fileclose_env fn on n eb p Cf -∗ fileclose_env_out fn on Cf.
  Proof.
    rewrite /fileclose_env /fileclose_env_out.
    case_bool_decide; [|case_match].
    - iApply fileclose_pipe_env_out.
    - iApply fileclose_fs_env_out.
    - by iIntros "_".
  Qed.

  (* ---- CLOSING MORE THAN ONE DESCRIPTOR ----

     kexit walks the whole fd table, so its loop has to carry the environment
     round.  Everything in both bundles except the four consumables and the
     page count is persistent, so the round trip is a persistent wand: hand
     the bundle over, and rebuild it from what comes back.  The page count
     comes back CHANGED -- pipeclose frees the page only if it closed the
     pipe's last end -- which is why the pipe bundle is rebuilt under an
     existential, and hence why [on] is a parameter and not a field.

     If either of these ever stops compiling, a conjunct of the environment
     has stopped being persistent and must be routed back through the
     corresponding [_out] instead. *)
  Lemma fileclose_pipe_env_reuse fn on n :
    fileclose_pipe_env fn on n -∗
    fileclose_pipe_env fn on n ∗
    □ (fileclose_pipe_out fn on -∗ ∃ on', fileclose_pipe_env fn on' n).
  Proof.
    rewrite /fileclose_pipe_env /fileclose_pipe_out.
    iIntros "(%Hb & #Hpi & #Hlk & Hav)".
    iSplitL "Hav".
    { iSplitR; [iPureIntro; exact Hb|]. iFrame "Hpi Hlk Hav". }
    iModIntro. iIntros "[H|H]".
    - iExists on. iSplitR; [iPureIntro; exact Hb|]. iFrame "Hpi Hlk H".
    - iExists (avail_inc on). iSplitR; [iPureIntro; exact Hb|]. iFrame "Hpi Hlk H".
  Qed.

  Lemma fileclose_fs_env_reuse fn n eb p :
    fileclose_fs_env fn n eb p -∗
    fileclose_fs_env fn n eb p ∗
    □ (fileclose_fs_out fn -∗ fileclose_fs_env fn n eb p).
  Proof.
    rewrite /fileclose_fs_env /fileclose_fs_env_nopid /fileclose_fs_out.
    iIntros "(%H1 & %H2 & %H3 & %H4 & %H5 & #Hpr & #Hrdy & Hbs)".
    iSplitL "Hbs".
    { do 5 (iSplitR; [iPureIntro; assumption|]).
      (* Split STRUCTURALLY before framing, front to back -- a named [iFrame]
         still walks the whole goal per hypothesis (measured ~7 s a side
         here); [iSplitL]/[iExact] name both sides, so nothing is
         searched. *)
      iSplitL "Hpr"; [iExact "Hpr"|].
      iSplitL "Hrdy"; [iExact "Hrdy"|].
      iExact "Hbs". }
    iModIntro. iIntros "Hbs".
    do 5 (iSplitR; [iPureIntro; assumption|]).
    iSplitL "Hpr"; [iExact "Hpr"|].
    iSplitL "Hrdy"; [iExact "Hrdy"|].
    iExact "Hbs".
  Qed.

  (* ---- WHAT A CLOSER OF AN ARBITRARY DESCRIPTOR DOES ----

     A caller that took its [struct file] out of the fd table -- sys_close,
     kexit, sys_pipe -- cannot see the type: [ProcInv.ofile_slot] quantifies
     the [fcontent] existentially, and that knowledge is going to arrive as
     per-[ofile] ghost state in [struct proc] rather than off the ftable.  So
     it carries BOTH bundles, hands over whichever the environment asks for,
     and keeps the other untouched.  This is that move, proved once: the
     environment out, and a wand that puts both bundles back together from
     whatever came back.

     (Only pipealloc escapes it, because [filealloc] pins its files untyped;
     it uses [fileclose_env_none] instead.) *)
  Lemma fileclose_env_split fn on n eb p Cf :
    fileclose_pipe_env fn on n -∗ fileclose_fs_env fn n eb p -∗
    fileclose_env fn on n eb p Cf ∗
    (fileclose_env_out fn on Cf -∗
       fileclose_pipe_out fn on ∗ fileclose_fs_out fn).
  Proof.
    rewrite /fileclose_env /fileclose_env_out.
    case_bool_decide; [|case_match].
    - iIntros "Hp Hf". iFrame "Hp". iIntros "$".
      by iApply fileclose_fs_env_out.
    - iIntros "Hp Hf". iFrame "Hf". iIntros "$".
      by iApply fileclose_pipe_env_out.
    - iIntros "Hp Hf". iSplitR; [done|]. iIntros "_".
      iDestruct (fileclose_pipe_env_out with "Hp") as "$".
      by iApply fileclose_fs_env_out.
  Qed.

  (* ...and the form every fd-table closer actually uses: hand over the
     environment, get the WHOLE environment back.  The page count has moved
     if the descriptor held a pipe's last end, so the pipe bundle returns
     under an existential -- which is exactly what lets a caller close a
     second descriptor, and hence what kexit's loop runs on. *)
  Lemma fileclose_env_frame fn on n eb p Cf :
    fileclose_pipe_env fn on n -∗ fileclose_fs_env fn n eb p -∗
    fileclose_env fn on n eb p Cf ∗
    (fileclose_env_out fn on Cf -∗
       (∃ on', fileclose_pipe_env fn on' n) ∗
       fileclose_fs_env fn n eb p).
  Proof.
    iIntros "Hp Hf".
    iDestruct (fileclose_pipe_env_reuse with "Hp") as "[Hp #Hpre]".
    iDestruct (fileclose_fs_env_reuse with "Hf") as "[Hf #Hfre]".
    iDestruct (fileclose_env_split fn on n eb p Cf with "Hp Hf") as "[$ Hback]".
    iIntros "Hout". iDestruct ("Hback" with "Hout") as "[Hpo Hfo]".
    iSplitL "Hpo"; [by iApply "Hpre" | by iApply "Hfre"].
  Qed.

  (* THE LOOP'S OWN OPENING, for a caller that carries the fs bundle in its
     [_nopid] form.  It USED TO take the caller's quarter of [p->pid] as a
     third argument and splice it into the bundle, because [fileclose_fs_env]
     carried that cell; the bundle does not carry it any more (fileclose asks
     for [proc_priv_bare] at the top level instead), so the two forms
     coincide and this is [fileclose_env_frame] under the other name. *)
  Lemma fileclose_loop_open fn on n eb p Cf :
    fileclose_pipe_env fn on n -∗
    fileclose_fs_env_nopid fn n eb p -∗
    fileclose_env fn on n eb p Cf ∗
    (fileclose_env_out fn on Cf -∗
       (∃ on', fileclose_pipe_env fn on' n) ∗
       fileclose_fs_env_nopid fn n eb p).
  Proof.
    rewrite -!fileclose_fs_env_nopid_eq.
    exact (fileclose_env_frame fn on n eb p Cf).
  Qed.


End SpecFileclose.

Definition wp_fileclose_sconf_body
    `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
      !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId}
    (γfl γf : gname)            (* ftable.lock, ftable  *)
    (k : nat) (q : Qp) (Cf : fcontent)                (* the reference        *)
    (fn : fclose_names) (on : option nat)              (* the arms' ghosts   *)
    (m : regfile) (n : nat) (eb : bool) (p : mword 64)
    (K : nat) (b : bool) (lks : gset string)
    (* THE CALLER'S OWN PID, not [fcn_pid fn].  The block row below used to be
       keyed on the names record's field, which no caller can pay: every one
       of them holds [proc_priv_bare] at the pid IT knows, and nothing ties
       that to [fn]'s.  acquiresleep only records whatever [p->pid] holds, so
       keying on the caller is both payable and what the code does.  This is
       what retires the [fcn_pid fn = pid] tie premise on sys_close. *)
    (pidv : mword 32) (Vpr : pprivate) :=
  let pcE : mword 64 := mword_of_int KernelSyms.fileclose in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5) : mword 64) in
  (fileclose_stack <= K)%nat ->
  (* fileclose's own acquire is one level of nesting; the arms that want more
     say so in [fileclose_env]. *)
  (Z.of_nat n + 1 < 2 ^ 31)%Z ->
  (* a0 is the file being closed *)
  m !!! Regidx (mword_of_int 10 : mword 5) = fnode k ->
  locks_below lks "log" ->
  sie_cap_gpr KT1 m K b p -∗
  cpu_own n eb p b lks -∗
  (* THE TRAP-CSR COMPLEMENT, ON EVERY ARM.  [emp] at [eb = true], where
     fileclose's own acquire mints what the FS arm's interior sleeps need;
     the real pair at [eb = false], where the acquire mints nothing and it
     can only have come from the TRAP.  Top-level rather than inside
     [fileclose_fs_env] -- see that bundle's banner for why the FS arm is
     the wrong home for it.  See
     claude-notes/completed/eb-generic-sweep.md. *)
  trap_csrs_ext KT1 eb -∗
  cpu_claim_ext eb p -∗
  kernel_text -∗ kernel_data -∗ pc_is pcE -∗
  is_ftable γfl γf -∗
  panic_env -∗
  file_ref γf k q Cf -∗
  (* THE RUNNING THREAD'S PROCESS BLOCK, in and straight back out.  The FS
     arm reaches iput -> itrunc/iupdate -> bread -> acquiresleep, which
     records its holder ([lk->pid = myproc()->pid]); acquiresleep takes the
     block and borrows the field itself, so this is what fileclose forwards.
     It used to be a quarter of [p->pid] smuggled through
     [fileclose_fs_env] -- see the note there for why that could not be paid
     beside [ProcInv.proc_priv].  Unconditional rather than type-selected:
     the pipe arm does not need it, but making the row an [if] over a
     content the caller cannot see buys nothing. *)
  proc_priv_bare p pidv Vpr -∗
  (* ONE IREF UNIT, BORROWED ACROSS THE CALL -- in here, out in the post, on
     every arm.  It is what the LAST close deposits into the slot it frees:
     [FileInvDefs.file_core] parks the entry's provisioned unit on the
     untyped and pipe arms, so a free slot's payload holds one, and fileclose
     frees the slot (f->type = FD_NONE) and RELEASES ftable.lock before it
     switches on the type -- so on the FD_INODE arm the unit [iput] will make
     does not exist yet.  Borrowing one from the caller is what makes the
     deposit available at the moment the slot is freed.
     It is repaid before returning, from [file_core]'s pipe arm or from
     [iput]'s own give-back, so every caller is net zero and neither the type
     nor whether this was the last close appears in the post.  A NON-last
     close frees nothing and hands the same unit straight back. *)
  iref_slot -∗
  fileclose_env fn on n eb p Cf -∗
  (* THE CROSSING IS THE LITERAL [true], NOT [b].  The FD_INODE / FD_DEVICE
     arm parks (begin_op / iput / end_op), so fileclose can return on
     another hart whatever SIE was doing.  It used to say [b], which was
     VACUOUS rather than wrong: the FS bundle carried [⌜eb = true⌝], so
     [CpuOwn.cpu_own_eb_agree] forced [b = true] on the only arm that could
     park.  Dropping that premise is exactly what makes the two spellings
     differ.  (The fast path and the pipe arm do not migrate, and neither
     is harmed: a [true] crossing is FREE to consume at any hart -- the
     obligation it adds is on the CALLER, which must supply its
     continuation hart-generically.) *)
  wp_next true p (fun (CID : CpuId) =>
    ∀ mr,
    sie_cap_gpr KT1 mr K b p -∗
    cpu_own n eb p b lks -∗
    trap_csrs_ext KT1 eb -∗
    cpu_claim_ext eb p -∗
    pc_is ret_tgt -∗
    ⌜ callee_saved m mr ⌝ -∗
    fd_slot -∗
    iref_slot -∗
    fileclose_env_out fn on Cf -∗
    proc_priv_bare p pidv Vpr -∗
    WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type FILECLOSE.
  Parameter wp_fileclose_sconf :
    forall `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ, !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId}
      (γfl γf : gname)
      (k : nat) (q : Qp) (Cf : fcontent)
      (fn : fclose_names) (on : option nat)
      (m : regfile) (n : nat) (eb : bool) (p : mword 64)
      (K : nat) (b : bool) (lks : gset string) (pidv : mword 32) (Vpr : pprivate),
      wp_fileclose_sconf_body γfl γf k q Cf fn on m n eb p K b lks pidv Vpr.
End FILECLOSE.
