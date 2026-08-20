(*  FsCfg.v -- THE FILE SYSTEM'S CANONICAL GHOST NAMES.

    There is exactly ONE file system per boot, so its ghost names are
    ambient rather than threaded -- the argument [IcacheRef.icfg] already
    makes for the inode cache ("there is exactly one inode cache per
    system, so threading its gname would put a filesystem ghost name on
    [ProcInv.proc_priv] and hence on the thirty-odd spec files that mention
    it", InodeRef.v).  This class is that argument applied to the rest of
    the fs, and it exists so that [FsReady.fs_ready] can be a predicate with
    NO PARAMETERS.

    ---- WHY PARAMETER-FREE IS THE POINT ---------------------------------

    [fs_ready] is meant to be carried by a running process and handed on --
    forkret's not-forked arm produces it, the trap loop's residue carries
    it, and every later syscall reads it back.  A twenty-parameter version
    can be carried only by existentially quantifying the twenty, and a bare
    existential is useless downstream: a consumer that has been handed
    [∃ γ…, fs_ready γ…] cannot feed it to [SpecKexec.fs_fabric] or to
    [UsertrapRes.ut_res_bare], whose own resources are keyed to the
    CALLER's concrete names, because nothing relates the two.  Ambient
    names remove the existential instead of hiding it.

    ---- WHAT IS NOT HERE ------------------------------------------------

    The four names the inode cache already owns stay in [icfg] and are NOT
    duplicated: [icfg_log] (the log's four gnames), [icfg_ist], [icfg_nib]
    and [icfg_dev].  [SpecKexec] and [SpecFsinit] already tie threaded
    copies to them by pure premise ([g = icfg_log], [dev = icfg_dev], ...);
    the fields below take the same door for the same reason.

    [procs_inv]'s [γs] is not here either, and that is deliberate: it is a
    PROCESS name, and it was in [fs_ready] only because [procs_inv] was a
    conjunct.  That conjunct is gone -- it is persistent, every consumer
    already holds it beside the fs environment ([SpecKexec.fs_fabric] lists
    it separately, and forkret's tier carries it in the park package's
    persistent world), and dropping it is what leaves this class with no
    process content at all.

    ---- IT IS PER-ERA, EXACTLY AS [icfg] IS -----------------------------

    A crash re-mints the disk image ghost ([DiskPtsto.dn_img]; see
    claude-notes/design/crash.md, "PowerOn allocates a fresh era record").
    So this is a CLASS ASSUMPTION of each section, instantiated by each
    era's boot chain -- not a global constant.  Nothing in it has to survive
    a crash, because [fs_ready] does not either: the new era re-runs boot
    and builds its own.  *)
From Stdlib Require Import ZArith List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.base_logic.lib Require Import own.   (* [gname] *)
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import WpUart.        (* [uart_names] *)
Require Import DiskPtsto.     (* [disk_names] *)
Require Import BioDefs.       (* [bio_names]  *)
Require Import FsBlocks.      (* [fs_names]   *)
Require Import IcacheEscrow.  (* [ic_names]   *)
Local Open Scope Z_scope.

Class fscfg := MkFscfg {
  (* printk's environment, and the page allocator's authority *)
  fsc_printk : gname;
  fsc_kalloc : gname;
  (* the device fabric: the UART's four ghosts, the disk's seven, and the
     "virtio_disk" spinlock *)
  fsc_uart   : uart_names;
  fsc_disk   : disk_names;
  fsc_dlock  : gname;
  (* the three virtio ring pages.  These are ADDRESSES, not ghost names,
     and they are already pinned by the persistent cells inside
     [DiskInv.disk_geom] ([d_desc_ptr ↦₈□ pd], ...) -- so they could have
     been recovered from an existential by agreement.  They are here
     anyway: one door for the whole fs configuration is simpler than two,
     and it costs nothing. *)
  fsc_desc   : mword 64;
  fsc_avail  : mword 64;
  fsc_used   : mword 64;
  (* the block layer: the bcache's three scalars and three per-buffer
     families, and the logged-view / dirty / block-ownership ghosts *)
  fsc_bio    : bio_names;
  fsc_fs     : fs_names;
  (* the inode region's authority, the icache's three per-entry escrow
     families, and the "itable" spinlock *)
  fsc_ireg   : gname;
  fsc_ic     : ic_names;
  fsc_itlock : gname;
  (* the image's block geometry: which blocks the fs covers, and where the
     log starts.  Pure data, ambient for the same reason [icfg_ist] is. *)
  fsc_cov    : gset Z;
  fsc_logst  : Z;
}.
