(* RiscvPtsto.v -- riscvGS, register/memory points-to, the regstate/heap bridge. *)
From Stdlib Require Import Eqdep_dec ZArith.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap ghost_map ghost_var mono_nat
     invariants.
From iris.algebra Require Import csum excl agree auth gset.
From iris.program_logic Require Import weakestpre.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import RiscvLang.
Require Export DiskImg.  (* [diskImgG]/[disk_img_auth]: the disk image map *)
(* [disk_write]/[disk_wr]/[wr_apply]: the disk image and the pure write
   identity a crash permit is indexed by.  Safe to import here -- DiskImg.v
   already does, and this file re-exports it. *)
Require Import VirtioModel.
Require Import PtreeType.   (* [ptree]: the carrier of the shared kernel table's ghost *)

(* ---- the tree-wide [set_solver] override (see FastSetSolver.v) ----      *)
(* This file is here as a PROPAGATION HUB, not because it uses sets: it is  *)
(* [Require Import]ed DIRECTLY by 796 of the tree's 1090 files, and         *)
(* [Require Export] only reaches a file that imports THIS one directly (or  *)
(* through an unbroken chain of Exports, which this tree does not have).    *)
(* Without a hub like this, a new proof would silently get stdpp's slow     *)
(* [set_solver] -- which is exactly the trap the override exists to remove. *)
(* EXPORT, not Import, and deliberately "dead": the nightly dead-import     *)
(* sweep skips [Require Export] lines.                                     *)
Require Export FastSetSolver.

Local Open Scope Z_scope.

(* Name [mword] locally (qualified target) rather than [Require Import
   SailStdpp.Values] -- the latter would leak Sail's key typeclass
   instances into every file that imports RiscvPtsto (durable-notes).  The
   VA-based points-to layer below ([svpn_of]/[pa_of]/[kmap_at]/↦ₘ/↦ₓ) is
   stated over mwords, so the name has to be in scope here. *)
Local Notation mword := SailStdpp.Values.mword.

(* ===== RiscvModelIris ===== *)
(* ====================================================================== *)
(* RiscvModelIris.v                                                        *)
(*                                                                         *)
(* LAYER 2: the Iris program-logic layer over RiscvModelLang.v.            *)
(*                                                                         *)
(*   - register & memory [gen_heap]s, with points-to [r |->r v] / [a|->m b]*)
(*   - state_interp that BRIDGES the model's [regstate] to per-register    *)
(*     points-to via an existential register map + an agreement invariant  *)
(*     (axiom-free: existT injectivity goes through Eqdep_dec, register     *)
(*      has decidable equality; no Finite/UIP needed).                     *)
(*   - the two bridge lemmas [reg_valid] / [reg_update] and a memory read  *)
(*     lemma [mem_valid].                                                   *)
(*                                                                         *)
(* The WP for ADD *through* [try_step] (symbolic unfolding of fetch/decode/*)
(* execute/currentlyEnabled) is the next milestone; this file provides the *)
(* ghost-state foundation it will rest on.                                 *)
(* ====================================================================== *)




(* ---------------------------------------------------------------------- *)
(* 0. Two small facts about the model's [register_beq] and [existT].       *)
(* ---------------------------------------------------------------------- *)

Lemma register_beq_true (k r : register) : register_beq k r = true -> k = r.
Proof.
  destruct k, r; simpl; intro E; try discriminate;
    f_equal; autorewrite with register_beq_iffs in E; exact E.
Qed.

Lemma register_beq_false (k r : register) : k <> r -> register_beq k r = false.
Proof.
  intros Hne. destruct (register_beq k r) eqn:E; [|reflexivity].
  exfalso. apply Hne. by apply register_beq_true.
Qed.

(* existT injectivity on the (decidable) index type [register]: axiom-free. *)
Lemma reg_existT_inj (r : register) (v v' : type_of_register r) :
  existT r v = existT r v' -> v = v'.
Proof.
  apply (inj_pair2_eq_dec register (fun x y => decide (x = y))).
Qed.

(* ---------------------------------------------------------------------- *)
(* 1. Ghost state: a register map ([ghost_map]) and a memory heap           *)
(*    ([gen_heap]).  The registers use [ghost_map] -- an explicitly-named   *)
(*    authoritative gmap ([riscv_reg_name]) with per-key elements -- rather *)
(*    than [gen_heap]; the byte memory keeps its [gen_heap].                *)
(* ---------------------------------------------------------------------- *)

(* The two kernel permission CLASSES of the etext region split (rwx-kmap):
   text pages are mapped R|X, data/device pages R|W.  The enum lives here,
   above [riscvGS], so the class can carry the kernel-mapping claim ghost
   (KMap.v) over it; the PTE flag bytes and the vpn classifier are KptPt
   §15's. *)
Inductive kperm : Set := KP_rx | KP_rw.

Global Instance kperm_eq_dec : EqDecision kperm.
Proof. solve_decision. Defined.

(* the shared kernel page table's resource algebra: one-shot agreement on
   the A/D-canonical table. *)
Definition kptR : cmra := csumR (exclR unitO) (agreeR (leibnizO ptree)).

(* THE PER-CPU HELD-LOCK SET (LockSet.v, claude-notes/design/kernel-proofs.md):
   an authority over the set of RANKS -- lock-order levels, [LockRank.v] -- of
   the spinlocks this hart currently holds.  The authority rides in
   [IntrDefs.cpu_hart] -- i.e. with the running kernel thread while interrupts
   are off, and inside [sie_arm true] while they are on -- and a HELD lock's
   invariant keeps the matching [gset_disj] fragment, which is what makes
   "[lk->cpu] is set to hart i" and "a lock of this rank is in i's held set"
   one fact rather than two.

   [gset_disj] rather than a plain [gset]: the fragment must be EXCLUSIVE (so
   release, holding it, can retire the element) and it must be UNFORGEABLE (so
   the tie means something).  What that costs is that minting one needs
   [r ∉ S] -- which is exactly what acquire's order premise
   [LockRank.locks_below S r] supplies, via [locks_below_not_elem].

   RANKS, NOT ADDRESSES, and the element type is where all the ergonomics
   live.  An address set would have to carry a rank alongside each element for
   acquire's premise to be statable at all, and the address half would then
   never be read -- xv6 never holds two locks of the same family, so the order
   is total on every pair it can actually hold (LockRank.v).  Keying on [nat]
   also means the element type takes stdpp's own instances: no [EqDecision] /
   [Countable] pinning is needed (contrast [riscvF_kmapGS] below), and
   [set_solver] WORKS -- over [gset (mword n)] it fails with "No matching
   clauses for match", which is why the durable notes' discharge-by-named-lemma
   rule exists and why it no longer applies here. *)
Definition lockSetR : cmra := authR (gset_disjUR nat).

(* The ghost layer is SPLIT IN TWO (claude-notes/design/crash.md): the
   FIXED layer -- [invGS] plus every functor (inG) class -- will survive
   power cycles; the ERA layer -- every ghost NAME -- is one boot's worth
   of ghost state, to be reallocated fresh at each power-on so that a new
   boot's memory/register resources are independent of the previous
   boot's.  [riscvGS] bundles both, and every proof file keeps taking
   exactly it: the pre-split field names are preserved verbatim as
   definitions below the class, so no statement anywhere changes. *)

(* THE FS LOG-REGION MIRROR's VALUE (claude-notes/design/fs-log.md stage 4
   phase C2b/D1).  Defined HERE, not in the FS layer, because the era record
   below needs its gname and the fixed class below needs its [ghost_varG]:
   both sit under every FS file.  It carries no FS CONSTANT (the geometry --
   which block is the header, how many slots there are -- lives entirely in
   [FsCrash.log_mirror_ok], above [SystemAdequacy]); it is just the shape of
   the picture the WAL's writes hand each other:

     - [lm_hdr]  : the ON-DISK header's [hdr_dec] reading, which is what
       "the log is clean" / "the log holds (n, W)" are statements about;
     - [lm_slots]: the ON-DISK log slots' contents, which is what
       "the slots hold the logged values" is a statement about.

   Both are recorded as READINGS rather than as bytes, because that is the
   lightest thing that serves all three WAL write kinds. *)
Record log_mirror := MkLogMirror {
  lm_hdr   : nat * list Z;
  lm_slots : nat -> list (bv 8);
}.

Record riscvEraGS := RiscvEraGS {
  (* one register-map ghost name PER hart.  A [ghost_map] element on
     [cpu_reg_name c] owns a register of hart [c].  The function is total (every
     [CPU] is a real hart) and its per-hart authoritative maps are threaded by
     [gregs_interp] below. *)
  era_reg_name : CPU -> gname;
  era_heap_name : gname;
  era_meta_name : gname;
  era_uart_name : gname;
  era_plic_name : gname;
  era_virtio_name : gname;
  (* the kernel-mapping claim ghost (KMap.v, rwx-kmap): one global
     vpn ↦ (ppn, class) map.  Lives here -- not as a separate class --
     because [tlb_inv_pt] rides inside [sie_cap_gpr], and a separate
     class would have to be threaded through every sconf-tier file;
     like [uart_name]/[plic_name] it is global (not per-hart). *)
  era_kmap_name : gname;
  (* THE SHARED KERNEL PAGE TABLE's ghost (claude-notes/projects/
     kpt-share.md): a ONE-SHOT agreement on the table's A/D-CANONICAL form
     ([PtTree.ptree_canon]).  Adequacy mints the unset token [Cinl (Excl ())];
     main's kvm assembly shoots it, at the tree kvminit built, to the
     PERSISTENT [Cinr (to_agree …)] every hart then carries in its
     translation residue.  Agreement is enough -- not an order -- because
     the Svadu A/D write-back leaves the canonical table INVARIANT
     ([PtTree.ptree_canon_set_leaf]), so a write-back needs no ghost update
     at all.  Lives HERE, not in a separate class, for exactly the reason
     [kmap_name] does: the residue rides inside [sie_cap]/[intr_frame], so a
     class would have to be threaded through every sconf-tier file. *)
  era_kpt_name : gname;
  (* the S-mode translation-slot arm bit ('b"0" = Bare, 'b"1" = kernel PT
     installed): a global ghost name (like [kmap_name]) tracking which arm
     of [strans_inv] the capability's translation slot is in.  A client
     half held outside the slot is a "still-Bare receipt" pinning the arm;
     the kvminithart switch flips it with both halves.  The [ghost_varG Σ
     (mword 1)] functor instance comes from [sieG] at the use sites (NOT a
     field here -- a second [ghost_varG Σ (mword 1)] instance would make
     typeclass resolution ambiguous between two functor slots).
     PER-HART, like [cpu_reg_name]: satp and tlb are per-hart registers, so
     which arm a hart's translation slot is in is a per-hart fact, and the
     shared-kernel-table sweep (claude-notes/completed/kpt-share.md) needs
     every hart to flip its own bit at its own kvminithart. *)
  era_strans_name : CPU -> gname;
  (* the SIE ghost, CANONICALLY per hart -- the same shape as [strans_name],
     and for the same reason: mstatus.SIE is a per-hart register, so which
     value a hart's SIE choreography (1/2 live-bit tie + 1/4 kernel-code token
     + 1/4 invariant, IntrDefs.v §2) is at is a per-hart fact.

     Making the name CANONICAL rather than an explicit parameter is what lets
     the whole sconf tier -- [sconf] / [sie_cap] / [sie_cap_gpr] / [sie_arm] /
     [intr_count] / [intr_off_tok] / [intr_inv] / [intr_handler_avail] -- drop
     its [γ] argument entirely: the hart determines the ghost.  In particular a
     step's continuation then quantifies only the HART (WpNext.v), and every
     parking contract's [∀ h g] collapses to [∀ h].

     NOT canonical, and deliberately so: the per-trap ghost [ProofKernelvec.v]
     mints for the handler's own SIE tie.  During a trap the live bit is 0
     while the interrupted thread's half still reads 1, so those two cannot
     share a name; [wp_kernelvec] takes a raw [ghost_var γ (1/2) _] and stays
     parameterized.  The functor instance comes from [sieG] at the use sites,
     for the same reason spelled out for [strans_name] above. *)
  era_sie_name : CPU -> gname;
  (* mstatus.SPP's ghost MIRROR, canonically per hart -- the same shape as
     [sie_name], and needed for a reason the other trap-scribbled state does
     not have.  A trap writes sepc / scause / stval AND mstatus.SPP; the
     first three are whole registers, so ownership of them moves by moving
     the cell (they sit in [IntrDefs.trap_csrs], inside [sie_arm true] while
     interrupts are enabled and in the code's hands while they are off).
     SPP is a BIT INSIDE mstatus, and mstatus cannot leave [sconf] -- SIE
     lives there too, and so do the well-formedness facts -- so its
     ownership has to move as a ghost instead.

     Hence TWO halves, exactly as SIE has: one TIED inside [sconf] to
     [_get_Mstatus_SPP ms], and one that travels with [trap_csrs], held at
     an EXISTENTIAL value by the enabled arm (a trap can rewrite SPP between
     any two instructions) and at a PINNED value by interrupts-off code.
     That is what lets a trap handler entered from S-mode still know, four
     instructions later, that SPP = 1 -- the fact the funnel's [exists ms]
     would otherwise destroy.

     The [ghost_varG Σ (mword 1)] functor instance comes from [sieG] at the
     use sites, NOT from a field here, for the same reason spelled out for
     [strans_name]: a second instance of that class would make resolution
     ambiguous.  SPP is one bit, so [sieG]'s instance already fits. *)
  era_spp_name : CPU -> gname;
  (* mstatus.SPIE's mirror, the twin of [spp_name] and travelling with it.
     SPIE is the OTHER bit an [sret] reads (it restores SIE from it), it is
     written by the same trap, and it is preserved by the same SIE flips --
     so it obeys the identical discipline and the two are always held
     together, as [IntrDefs.sret_bits].  Two names rather than one ghost over
     a pair only because [sieG]'s [ghost_varG (mword 1)] then serves both
     with no new class. *)
  era_spie_name : CPU -> gname;
  (* THE HART TAG, CANONICALLY per proc slot.  One [ghost_var CPU] per entry
     of the proc[] array, naming the hart that a RUNNING proc is running on.
     Two halves: while the proc is RUNNING one sits in its [p->lock]'s
     running arm ([SchedCtx.run_slot]) and the other rides the running
     thread's [IntrDefs.cpu_claim]; otherwise both sit whole in the lock
     ([SchedCtx.proc_slots]) and the value is meaningless.

     KEYED BY THE PROC, NOT BY THE HART: that is what makes the entitlement
     HART-FREE, so a thread carries it across a migration as a plain frame
     (a per-hart receipt would be exactly the kind of stranded resource the
     explicit-cpuid refactor exists to remove).

     CANONICAL rather than an explicit [γk : list gname] parameter, for
     precisely the reason spelled out for [sie_name] and [kmap_name] above:
     the receipt is named inside [SchedCtx.proc_lock_res], hence inside
     [procs_inv], and a parameter there would have to be threaded through
     every one of the ~50 files that mention [procs_inv].  The function is
     total; only indices below [NPROC] are ever owned. *)
  era_park_name : nat -> gname;
  (* THE PER-PROC STATE MIRROR (design/proc-struct.md, the state ghost).
     Two halves of a [ghost_var] carrying [p->state]'s value: the proc lock
     invariant owns one, tied to the cell, and the other is lock-resident
     except at the two states where a THREAD has claimed the proc (RUNNING,
     USED).  Since a ghost_var cannot move on half alone and the cell cannot
     move without the ghost, the right to WRITE [p->state] is exactly
     ownership of the second half.

     Canonical for the same reason as [era_park_name] directly above: it is
     named inside [SchedCtx.proc_lock_res], hence inside [procs_inv]. *)
  era_pstate_name : nat -> gname;
  (* THE DISK IMAGE MAP (claude-notes/design/crash.md, design/fs-log.md
     stage 4): a byte-granularity ghost map mirroring [v_disk], tied to the
     state by [disk_dur_interp] below -- ONE conjunct of this era's
     [era_interp], hence gone when the era is.

     PER-ERA, deliberately.  The image itself survives a power cycle (it is
     the one machine component that does), but its GHOST mirror must not:
     client-visible fragments -- bio's pool/escrow, the log's block views --
     park in era invariants, and a FIXED map could never re-mint them at the
     next boot ([ghost_map] cannot re-create an existing key, and auth-side
     forgetting needs the element, which is exactly what is stranded), so a
     fixed map cannot boot twice once the FS layer holds fragments.  A fresh
     map per era, allocated at the PRESERVED content and handed out WHOLE
     ([RiscvAdequacy.power_boot_res]'s boot mint), has no such problem: the
     dead era's fragments are abandoned with everything else it owned.

     The class typing it stays FIXED-layer ([riscvF_diskGS], from DiskImg.v):
     it is the unique source of the [ghost_mapG Σ Z (bv 8)] instance in a
     [riscvGS] context, and a second one could not interact with it. *)
  era_disk_name : gname;
  (* THE FS LOG-REGION MIRROR (claude-notes/design/fs-log.md stage 4 phase
     C2b/D1): this era's [ghost_var] over the physical log region's picture,
     split 1/2 - 1/2 between the log layer ([LogInv]'s batch/lock resource)
     and [P_fs]'s CHECKED-OUT arm.  It is what carries the WAL's physical
     phase ACROSS bwrite calls -- "the on-disk header is clean", "the log
     slots hold the logged values", "the header is the (n, W) I just wrote"
     -- none of which any single call site can re-derive at its own call.

     PER-ERA for exactly the reason [era_disk_name] is: the log layer's half
     dies with the era, and a FIXED gname's stranded half could never be
     re-paired at the next boot.  Identification of the arm's gname with the
     AMBIENT era's is by the swap counter ([riscv_swap_name] below), squeezed
     against the started-generations auth the DMA completion threads in. *)
  era_mirror_name : gname;
  (* THE HELD-LOCK SET, CANONICALLY per hart (design/kernel-proofs.md): the
     authority of [LockSet.cpu_locks], naming the spinlocks this hart holds.

     PER-HART, like [sie_name] and [strans_name]: which locks are held is a
     property of the HART (xv6 records it in [lk->cpu], a [struct cpu]
     pointer), not of the thread -- and a lock is taken and given back with
     interrupts off, so it never crosses a migration.

     CANONICAL rather than a parameter, for the reason spelled out at
     [era_sie_name]: the authority lives inside [IntrDefs.cpu_hart], hence
     inside [cpu_own] / [sie_arm] / every whole-function contract in the
     sconf tier, and an explicit [γ] there would have to be threaded through
     all ~312 files that name [cpu_own].  The [inG Σ lockSetR] instance is
     [riscvF_lockSetGS] below, not a separate class, for the same reason. *)
  era_lockset_name : CPU -> gname;
}.

Class riscvFixedGS (Σ : gFunctors) := RiscvFixedGS {
  riscvF_invGS :: invGS Σ;
  riscvF_regGS :: ghost_mapG Σ register (sigT type_of_register);
  (* the device fabric (DevModel.v): one [ghost_var] per device, in the
     standard halves pattern -- [state_interp] holds one half (the "auth"),
     the other half (the "frag") floats freely and is typically stored in an
     invariant shared between the driver's hart and the device thread. *)
  riscvF_uartGS :: ghost_varG Σ uart_state;
  riscvF_plicGS :: ghost_varG Σ plic_state;
  riscvF_virtioGS :: ghost_varG Σ virtio_state;
  (* pinned to the SAIL key instances (Decidable_eq_mword/Countable_mword),
     because every use site (KMap/KptPt/adequacy) imports Sail and elaborates
     [gmap (mword 27)] with them; without pinning, this field would take
     stdpp's bv_eq_dec/bv_countable (RiscvPtsto does not import the Sail
     instance modules) and the ghost_mapG key-instance args would not unify. *)
  riscvF_kmapGS :: @ghost_mapG Σ (SailStdpp.Values.mword 27) (SailStdpp.Values.mword 44 * kperm)
                    (@SailStdpp.Instances.Decidable_eq_mword 27) (@SailStdpp.Instances.Countable_mword 27);
  riscvF_kptGS :: inG Σ kptR;
  (* the per-hart held-lock set's functor (LockSet.v).  A FIELD rather than a
     standalone class: [cpu_locks] sits inside [IntrDefs.cpu_hart], so a class
     would have to be bound in every sconf-tier section in the tree. *)
  riscvF_lockSetGS :: inG Σ lockSetR;
  riscvF_parkGS :: ghost_varG Σ CPU;
  (* the per-proc state mirror's typing (the NAME is per-era, above).  A
     [mword 32] instance of its own -- no other ghost_var in the record
     carries one, so nothing else can be confused with it. *)
  riscvF_pstateGS :: ghost_varG Σ (SailStdpp.Values.mword 32);
  (* the FS log-region mirror's typing (the NAME is per-era, above) *)
  riscvF_mirrorGS :: ghost_varG Σ log_mirror;
  (* the byte memory's PRE-class: the era layer stores only the two heap
     GNAMES (a [gen_heapGS] bundle would drag Σ into the era record, and
     the era record must be Σ-FREE so it can be a [ghost_map] VALUE in
     the generation registry -- claude-notes/completed/crash.md); the
     full [gen_heapGS] is reconstructed below as [riscv_memGS]. *)
  riscvF_memGpreS :: gen_heapGpreS Arch.pa (bv 8) Σ;
  (* the power/crash layer (claude-notes/design/crash.md): the GENERATION
     COUNTER, a mono-nat mirroring [gstate.(ggen)].  FIXED-layer -- it is
     the one ghost that spans power cycles; [gen_dead] below is the
     persistent death certificate the corpse arms run on. *)
  riscvF_genGS :: mono_natG Σ;
  riscv_gen_name : gname;
  (* the STARTED-GENERATIONS counter (value [ggen + (if gpow then 1 else 0)],
     monotone under both power arms because PowerOff bumps [ggen]): a
     thread's persistent [gen_started] certificate is what refutes the
     current-generation-but-powered-off state in the base rules. *)
  riscv_start_name : gname;
  (* the GENERATION REGISTRY: gen ↦ its era record (Σ-free data, see
     [riscvEraGS] above).  A live thread's [minstret_inv] carries the
     persistent element [gen_id ↪□ riscv_eraGS], which is what ties its
     ambient era to the one [state_interp]'s existential holds. *)
  riscvF_registryGS :: ghost_mapG Σ nat riscvEraGS;
  riscv_registry_name : gname;
  (* THE DISK IMAGE's TYPING (claude-notes/design/crash.md): the class alone
     -- the NAME is per-era ([riscvEraGS.era_disk_name] above), because a
     fixed image map could not be re-minted after a crash.  This field is
     the UNIQUE source of the [ghost_mapG Σ Z (bv 8)] instance in every
     [riscvGS] context, which is the whole reason [DiskImg.v] exists: the
     era auth here and the driver's fragments in DiskPtsto.v must carry the
     same instance, and RiscvPtsto sits BELOW DiskPtsto, so neither file can
     take the class from the other. *)
  riscvF_diskGS :: diskImgG Σ;
  (* THE FS TIE (claude-notes/design/fs-log.md stage 4 phase C2a): a
     [ghost_var] over the WHOLE disk image function, split 1/2 - 1/2 between
     [state_interp]'s fixed conjunct ([fs_tie_interp] below, always at the
     machine's own [v_disk]) and [crash_inv]'s body.  FIXED-layer, because it
     is what must survive a power cycle -- the disk does, so its mirror must
     too, unlike the per-era image map above.

     THE VALUE IS THE RAW BYTE FUNCTION, not a block map.  Every FS constant
     (BSIZE, the fs range) lives above [SystemAdequacy], and the block view is
     a pure re-indexing the FS layer applies on top ([FsCrash.fs_blocks]); the
     completion's own obligation is then exactly [VirtioModel.disk_write],
     with no sector-alignment side condition anywhere in the device stack.

     The [ghost_varG Σ (Z -> bv 8)] instance is unique in a [riscvGS]
     context (no other ghost in the tree carries that type), so there is no
     resolution ambiguity. *)
  riscvF_fstieGS :: ghost_varG Σ (Z -> bv 8);
  riscv_fstie_name : gname;
  (* THE CRASH PREDICATE (claude-notes/design/crash.md): the client's
     durability invariant over the disk image, sealed into [crash_inv] below.

     INDEXED BY THE DISK IMAGE (phase C2a).  It used to be a bare [iProp Σ],
     and that shape cannot carry the tie: a field of type [iProp Σ] is OPAQUE
     to every opener, so a [ghost_var] half parked INSIDE the client's
     predicate is unreachable to the DMA completion -- which is the only
     mover of the tie -- and at a trivial [Pc] it does not exist at all.
     Indexing the field instead puts the tie half BESIDE the client's
     predicate in [crash_inv]'s body, where the completion can move it
     mechanically, while the index is exactly what a real [P_fs] needs to
     talk about the real disk.

     Still an ARBITRARY predicate, and still nothing between here and the
     device thread names it. *)
  riscv_crash_pred : (Z -> bv 8) -> iProp Σ;
  (* THE SWAP COUNTER (phase C2b/D1): a mono-nat whose FULL auth lives inside
     [P_fs]'s checked-out arm and whose value is the generation currently in
     custody of the FS record.  FIXED-layer, and the auth never strands
     because it lives in a fixed-layer INVARIANT rather than era-side; an era
     keeps only a persistent lower bound (its swap receipt).  Together with
     the started-generations auth the completion threads in, the two bounds
     SQUEEZE the arm's generation onto the ambient one, which is what
     identifies the arm's mirror gname. *)
  riscv_swap_name : gname;
}.

Class riscvGS (Σ : gFunctors) := RiscvGS {
  riscv_fixedGS :: riscvFixedGS Σ;
  riscv_eraGS : riscvEraGS;
}.

(* Compatibility names: the tree references these; signatures verbatim.
   Each is a plain definition (NOT an instance -- the [::] substructures
   above already provide the unique resolution path), so a use site
   elaborates to the same projection chain resolution produces. *)
Definition riscv_invGS `{!riscvGS Σ} : invGS Σ := riscvF_invGS.
Definition riscv_regGS `{!riscvGS Σ} :
  ghost_mapG Σ register (sigT type_of_register) := riscvF_regGS.
Definition riscv_uartGS `{!riscvGS Σ} : ghost_varG Σ uart_state := riscvF_uartGS.
Definition riscv_plicGS `{!riscvGS Σ} : ghost_varG Σ plic_state := riscvF_plicGS.
Definition riscv_virtioGS `{!riscvGS Σ} : ghost_varG Σ virtio_state :=
  riscvF_virtioGS.
Definition riscv_kmapGS `{!riscvGS Σ} :
  @ghost_mapG Σ (SailStdpp.Values.mword 27) (SailStdpp.Values.mword 44 * kperm)
    (@SailStdpp.Instances.Decidable_eq_mword 27)
    (@SailStdpp.Instances.Countable_mword 27) := riscvF_kmapGS.
Definition riscv_kptGS `{!riscvGS Σ} : inG Σ kptR := riscvF_kptGS.
Definition riscv_lockSetGS `{!riscvGS Σ} : inG Σ lockSetR := riscvF_lockSetGS.
Definition riscv_parkGS `{!riscvGS Σ} : ghost_varG Σ CPU := riscvF_parkGS.
Definition riscv_pstateGS `{!riscvGS Σ} : ghost_varG Σ (SailStdpp.Values.mword 32) :=
  riscvF_pstateGS.
Definition era_memGS_of `{!riscvFixedGS Σ} (E : riscvEraGS) : gen_heapGS Arch.pa (bv 8) Σ :=
  GenHeapGS _ _ _ (era_heap_name E) (era_meta_name E).
Global Instance riscv_memGS `{!riscvGS Σ} : gen_heapGS Arch.pa (bv 8) Σ :=
  era_memGS_of riscv_eraGS.
Definition cpu_reg_name `{!riscvGS Σ} : CPU -> gname := era_reg_name riscv_eraGS.
Definition uart_name `{!riscvGS Σ} : gname := era_uart_name riscv_eraGS.
Definition plic_name `{!riscvGS Σ} : gname := era_plic_name riscv_eraGS.
Definition virtio_name `{!riscvGS Σ} : gname := era_virtio_name riscv_eraGS.
Definition kmap_name `{!riscvGS Σ} : gname := era_kmap_name riscv_eraGS.
Definition kpt_name `{!riscvGS Σ} : gname := era_kpt_name riscv_eraGS.
Definition strans_name `{!riscvGS Σ} : CPU -> gname := era_strans_name riscv_eraGS.
Definition sie_name `{!riscvGS Σ} : CPU -> gname := era_sie_name riscv_eraGS.
Definition spp_name `{!riscvGS Σ} : CPU -> gname := era_spp_name riscv_eraGS.
Definition spie_name `{!riscvGS Σ} : CPU -> gname := era_spie_name riscv_eraGS.
Definition park_name `{!riscvGS Σ} : nat -> gname := era_park_name riscv_eraGS.
Definition pstate_name `{!riscvGS Σ} : nat -> gname := era_pstate_name riscv_eraGS.
(* the ambient era's per-hart held-lock authority (LockSet.v). *)
Definition lockset_name `{!riscvGS Σ} : CPU -> gname := era_lockset_name riscv_eraGS.
(* the AMBIENT era's disk-image gname: what [DiskPtsto.disk_names]'s [dn_img]
   field is always constructed at ([VirtioProto.disk_ghosts_alloc]), and what
   [RiscvExec.wp_disk_step] hands the disk thread.  The seam equation the
   driver carries is [dn_img γd = disk_img_name]. *)
Definition disk_img_name `{!riscvGS Σ} : gname := era_disk_name riscv_eraGS.
(* the AMBIENT era's log-region mirror gname *)
Definition mirror_name `{!riscvGS Σ} : gname := era_mirror_name riscv_eraGS.

(* The generation counter's three faces (claude-notes/design/crash.md).
   [gen_auth] rides in [state_interp] pinned to [gstate.(ggen)]; the lower
   bounds are persistent.  [gen_born gen] is every generation-[gen]
   resource bundle's birth certificate (it will ride in that era's
   [minstret_inv]); [gen_dead gen] is the stable death certificate --
   PowerOff bumps [ggen], so a generation once passed is dead forever. *)
Definition gen_auth `{!riscvFixedGS Σ} (n : nat) : iProp Σ :=
  mono_nat_auth_own riscv_gen_name 1 n.
Definition gen_born `{!riscvFixedGS Σ} (gen : nat) : iProp Σ :=
  mono_nat_lb_own riscv_gen_name gen.
Definition gen_dead `{!riscvFixedGS Σ} (gen : nat) : iProp Σ :=
  mono_nat_lb_own riscv_gen_name (S gen).

(* the started-generations counter's faces.  [start_count] is the pure
   value [state_interp] pins; [gen_started gen] says generation [gen]'s
   PowerOn has happened. *)
Definition start_count (g : gstate) : nat :=
  (g.(ggen) + (if g.(gpow) then 1 else 0))%nat.
Definition start_auth `{!riscvFixedGS Σ} (n : nat) : iProp Σ :=
  mono_nat_auth_own riscv_start_name 1 n.
Definition gen_started `{!riscvFixedGS Σ} (gen : nat) : iProp Σ :=
  mono_nat_lb_own riscv_start_name (S gen).

(* THE SWAP COUNTER's two faces (phase C2b/D1).  [swap_auth g] rides inside
   [P_fs]'s checked-out arm at the generation in custody; [swap_lb g] is the
   persistent SWAP RECEIPT an era keeps after its [initlog] took custody, and
   is what a WAL write's fupd curries to prove the arm is still its own. *)
Definition swap_auth `{!riscvFixedGS Σ} (g : nat) : iProp Σ :=
  mono_nat_auth_own riscv_swap_name 1 g.
Definition swap_lb `{!riscvFixedGS Σ} (g : nat) : iProp Σ :=
  mono_nat_lb_own riscv_swap_name g.

Global Instance swap_lb_persistent `{!riscvFixedGS Σ} g : Persistent (swap_lb g).
Proof. rewrite /swap_lb. apply _. Qed.

(* THE SQUEEZE, as two lemmas so no FS-layer proof touches [mono_nat]:
   the era's receipt bounds the arm's generation from BELOW, the started
   counter the completion threads in bounds it from ABOVE, and together they
   pin it to the ambient generation. *)
Lemma swap_lb_le `{!riscvFixedGS Σ} (g g'' : nat) :
  swap_auth g'' -∗ swap_lb g -∗ ⌜(g <= g'')%nat⌝.
Proof.
  rewrite /swap_auth /swap_lb. iIntros "Ha Hl".
  iDestruct (mono_nat_lb_own_valid with "Ha Hl") as %[_ Hle]. done.
Qed.

Lemma gen_started_le `{!riscvFixedGS Σ} (g'' n : nat) :
  start_auth n -∗ gen_started g'' -∗ ⌜(S g'' <= n)%nat⌝.
Proof.
  rewrite /start_auth /gen_started. iIntros "Ha Hl".
  iDestruct (mono_nat_lb_own_valid with "Ha Hl") as %[_ Hle]. done.
Qed.

Lemma swap_auth_update `{!riscvFixedGS Σ} (g'' g : nat) :
  (g'' <= g)%nat -> swap_auth g'' ==∗ swap_auth g ∗ swap_lb g.
Proof.
  intros Hle. rewrite /swap_auth /swap_lb. iIntros "Ha".
  iMod (mono_nat_own_update g with "Ha") as "[Ha #Hlb]"; [lia|].
  iModIntro. iFrame "Ha Hlb".
Qed.

Lemma swap_auth_alloc `{!riscvFixedGS Σ} (g : nat) :
  swap_auth g -∗ swap_auth g ∗ swap_lb g.
Proof.
  rewrite /swap_auth /swap_lb. iIntros "Ha".
  iDestruct (mono_nat_lb_own_get with "Ha") as "#Hlb". iFrame "Ha Hlb".
Qed.

(* THE DISK IMAGE TIE (claude-notes/design/crash.md, design/fs-log.md): era
   [E]'s image auth, pinned to the state's own [v_disk].  It is a conjunct of
   [era_interp] below, hence live exactly while the era is: PowerOff drops it
   with the rest of the era (nothing is owed -- the auth had no reader left),
   and PowerOn allocates the NEXT era's at the preserved content, handing the
   full fragments to the boot client.  Of the whole tree only the DISK
   thread's DMA completion moves [v_disk], so only [wp_disk_step] hands this
   conjunct over to its caller; the other three lifting rules frame it. *)
Definition disk_dur_interp `{!riscvFixedGS Σ} (E : riscvEraGS) (g : gstate)
    : iProp Σ :=
  disk_img_auth (era_disk_name E) (v_disk (dvirtio (gdev g))).

(* the registry element: generation [gen] runs era [E].  Persistent. *)
Definition era_registered `{!riscvFixedGS Σ} (gen : nat) (E : riscvEraGS) : iProp Σ :=
  gen ↪[riscv_registry_name]□ E.

(* THE CERTIFICATE BUNDLE a generation-[gen_id] thread carries (inside
   [minstret_inv], so no statement anywhere names it): born + started +
   its era's registration.  The base rules take it as one persistent
   premise and case on the current [(ggen, gpow)] against it. *)
Definition gen_cert `{!riscvGS Σ} `{GEN : GenId} : iProp Σ :=
  (gen_born gen_id ∗ gen_started gen_id ∗ era_registered gen_id riscv_eraGS)%I.

(* ---------------------------------------------------------------------- *)
(* THE CRASH-SPANNING INVARIANT (claude-notes/design/crash.md).             *)
(*                                                                          *)
(* [crash_inv] is allocated ONCE, in adequacy, over the fixed layer's        *)
(* [riscv_crash_pred], and it spans power cycles for free: neither power arm *)
(* opens it (the real disk image is untouched -- [virtio_reset] keeps        *)
(* [v_disk]), so the client's durability property holds at every reachable   *)
(* state INCLUDING the instant after a power loss.  It is opened in exactly  *)
(* one place in the whole tree -- the disk thread's DMA completion, the one  *)
(* step that moves [v_disk] ([WpUart.wp_disk_loop]).                         *)
(* ---------------------------------------------------------------------- *)

Definition crashN : namespace := nroot .@ "crash".

(* ONE HALF of the FS tie, at a given disk image.  [state_interp] holds the
   other half at the machine's own [v_disk] ([fs_tie_interp] below), so the
   two together say that the crash predicate is about THIS disk.  Both halves
   are in hand exactly at the DMA completion: [wp_disk_step] hands over
   [state_interp]'s, and opening [crashN] yields the body's. *)
Definition disk_tie `{!riscvFixedGS Σ} (dk : Z -> bv 8) : iProp Σ :=
  ghost_var riscv_fstie_name (1/2) dk.

Global Instance disk_tie_timeless `{!riscvFixedGS Σ} dk : Timeless (disk_tie dk).
Proof. rewrite /disk_tie. apply _. Qed.

(* the two halves always agree, and only a holder of BOTH can move them --
   which is exactly the DMA completion, and nobody else in the machine. *)
Lemma disk_tie_agree `{!riscvFixedGS Σ} (dk dk' : Z -> bv 8) :
  disk_tie dk -∗ disk_tie dk' -∗ ⌜dk = dk'⌝.
Proof. rewrite /disk_tie. iApply ghost_var_agree. Qed.

Lemma disk_tie_update `{!riscvFixedGS Σ} (dk dk' dk'' : Z -> bv 8) :
  disk_tie dk -∗ disk_tie dk' ==∗ disk_tie dk'' ∗ disk_tie dk''.
Proof. rewrite /disk_tie. iApply ghost_var_update_halves. Qed.

(* THE CRASH INVARIANT.  The tie half is a SIBLING of the client's predicate,
   not a conjunct of it: the completion must move it mechanically and cannot
   look inside an opaque [iProp] field.  The existential is what makes the
   body allocatable at ANY client predicate, including the trivial one. *)
Definition crash_inv `{!riscvFixedGS Σ} : iProp Σ :=
  inv crashN (∃ dk : Z -> bv 8, disk_tie dk ∗ riscv_crash_pred dk).

Global Instance crash_inv_persistent `{!riscvFixedGS Σ} : Persistent crash_inv.
Proof. rewrite /crash_inv. apply _. Qed.

(* THE WRITE PERMIT: what an enqueuer deposits for an OUT request (through
   the permit channel of [PermInv.v] -- NOT through the timeless slot, which
   cannot hold an iProp) and what the DMA completion spends to re-establish
   the crash predicate AT THE INSTANT the on-disk image changes.

   THE LOGICALLY-ATOMIC SHAPE (claude-notes/design/fs-log.md, stage 4 item 2):
   the permit is the CLIENT's view shift over the crash predicate, returning
   the client's own RECEIPT [Q] -- "when my write lands, the durability
   invariant still holds, and here is what I learn from that".  The caller
   curries the write's identity and its own abstract-state ghosts into the
   closure at enqueue time; the completion instant is precisely when the
   on-disk state changes, so that is when the wand must run, and [Q] is what
   comes back to the caller.  A SERIALIZED writer -- which xv6's log is, one
   commit at a time under the log lock -- needs nothing conditional here: no
   "if the disk still looks like X" guard, no mask annotation (a basic update
   goes through at whatever mask [wp_disk_loop] holds while [crashN],
   [PermInv.permN] and [diskN] are all open). *)
Definition disk_write_permit `{!riscvFixedGS Σ} (gd : nat) (w : disk_wr)
    (Q : iProp Σ) : iProp Σ :=
  (∀ (dk : Z -> bv 8) (n : nat),
     start_auth n -∗ ⌜n = (gd + 1)%nat⌝ -∗
     ▷ riscv_crash_pred dk ={∅}=∗
       ▷ riscv_crash_pred (wr_apply w dk) ∗ start_auth n ∗ Q)%I.

(* WHY A MASK-[∅] FUPD AND NOT A BASIC UPDATE.  A client whose crash
   predicate is TIMELESS -- [FsCrash.P_fs_any] is, every conjunct of it is a
   [ghost_map]/[mono_nat]/[own] over a discrete cmra -- has to STRIP the [▷]
   this type hands it before it can update the record's ghosts, and a basic
   update cannot do that: [◇] is not absorbed by [|==>] (there is no
   [▷ |==> P ⊢ |==> ▷ P] in Iris either).  A fupd at ANY mask absorbs [◇], so
   [∅] is the right choice: it is the weakest thing to PROVE (no invariant is
   open inside it -- a crash permit never opens one, it is handed the
   predicate directly), and the consumer runs it under whatever mask it holds
   via [fupd_mask_subseteq].  Nothing else about the seam changes. *)

(* WHY THE PERMIT NAMES ITS AUTHOR'S GENERATION [gd] (phase C2b/D1).  A crash
   permit is a STATELESS view shift: it runs at the DMA completion with only
   what its author curried at enqueue.  But the facts a WAL write's fupd needs
   about the PHYSICAL log region are chain facts -- established by the
   PREVIOUS writes -- so they have to be read out of a mirror the ERA holds a
   half of, and the crash predicate's own half of that mirror sits under an
   EXISTENTIAL (the mirror gname is per-era, because a fixed one could never
   be re-paired after a crash).  Matching the two halves therefore needs the
   fupd to know that the recorded custodian IS the ambient era.

   THE AUTHOR'S OWN GENERATION IS THE ONLY WORKABLE INDEX, and an earlier
   draft that quantified over the CONSUMER's generation instead
   ([∀ g E, era_registered g E -∗ …]) is UNPROVABLE at every real call site:
   everything a client can curry is at ITS [gen_id] -- [swap_lb (S gen_id)]
   and the mirror half at [era_mirror_name riscv_eraGS] -- while the squeeze
   would need both at the supplied [g].  The gap is exactly [g = gen_id], and
   it has no source: the registry is a plain [ghost_map nat riscvEraGS] with
   no injectivity (the base rules never need any -- [RiscvExec] identifies
   [E = riscv_eraGS] only in the [ggen = gen_id] case and parks a stale thread
   with [wp_dead]), and a [mono_nat] lower bound cannot be raised.  Nor MAY it
   be derivable: a stale era's permit must fail, or the crash predicate is
   unsound.

   So the freshness certificate comes from the completion, against the
   author's own [gd]: the completion threads in [state_interp]'s
   started-generations auth with the live-era arithmetic [n = gd + 1] and
   takes it back.  The client instantiates
   [FsCrash.fs_arm_acc] at [(gen_id, riscv_eraGS)] and the squeeze closes:
   its own [swap_lb (S gen_id)] gives [S gen_id <= c] from below, the arm's
   [gen_started g''] against that auth gives [g'' <= gen_id] from above, so
   [c = S gen_id] and [g'' = gen_id] -- and [era_registered] agreement AT THE
   SHARED KEY then gives [E'' = riscv_eraGS].

   WHAT MAKES THE CONSUMPTION SIDE WORK is era-locality, not per-request data:
   [PermInv.perm_inv] is indexed by the SAME [gd], so every permit in an era's
   channel is at that era's generation by construction, and [wp_disk_loop]
   holds the channel at its own [gen_id].  A dead era's channel is simply
   never opened again -- its device loop corpse-steps -- so its permits die
   unconsumed, which is exactly the soundness story.

   The IDENTITY permit ignores both remaining arguments, so a read's permit is
   still free at an ARBITRARY crash predicate. *)

(* THE IDENTITY PERMIT, and why it is still free.  A request that moves no
   disk byte carries [w = None], and [wr_apply None] is the identity ON THE
   NOSE, so the two occurrences of the crash predicate are syntactically the
   same and the permit is provable for an ARBITRARY client predicate.  Every
   READ deposits this, which is what keeps the whole read stack (bread and
   everything above it) textually unchanged by the C2a reshape. *)
Lemma disk_write_permit_trivial `{!riscvFixedGS Σ} (gd : nat) :
  ⊢ disk_write_permit gd None True.
Proof.
  rewrite /disk_write_permit. iIntros (dk n) "Hs _ HP". iModIntro.
  rewrite wr_apply_none. iFrame "HP Hs".
Qed.

(* A REAL WRITE'S PERMIT IS NOT FREE, and that is the honest content of the
   reshape: the completion moves the crash predicate's index, so somebody has
   to say what the predicate does under that move.  There is therefore NO
   [Pc]-generic write permit, and no bridge lemma either: the four WAL write
   kinds each prove their own fupd against the FS's own crash predicate
   ([FsCrash.fs_logfill_permit] / [_commit_permit] / [_install_permit] /
   [_clear_permit], phase C2b/D1 stage 4).  The earlier placeholder premise
   [crash_pred_indifferent], which said the system promises nothing about
   durability, was DELETED when those landed rather than discharged: it is
   FALSE at the real [P_fs], so keeping it would have made every WAL
   contract vacuous. *)

(* [reg_name] is the register-map ghost name of the AMBIENT hart [cpu_id].  It is
   what every [r ↦ᵣ v] / [reg_interp] / [reg_valid] / [reg_update] silently talks
   about, so those keep their single-CPU spelling: which hart they concern is
   selected by the surrounding [CpuId] instance, never written out. *)
Definition reg_name `{!riscvGS Σ} `{CpuId} : gname := cpu_reg_name cpu_id.

(* register points-to: [r |->r v] owns register [r] (of the ambient hart)
   holding [v].  Backed by a [ghost_map] element on [reg_name]. *)
Definition reg_pointsto `{!riscvGS Σ} `{CpuId} (r : register) (dq : dfrac)
    (v : type_of_register r) : iProp Σ :=
  ghost_map_elem reg_name r dq (existT r v).

Notation "r ↦ᵣ{ dq } v" := (reg_pointsto r dq v)
  (at level 20, format "r  ↦ᵣ{ dq }  v") : bi_scope.
Notation "r ↦ᵣ v" := (reg_pointsto r (DfracOwn 1) v)
  (at level 20, format "r  ↦ᵣ  v") : bi_scope.
(* discarded (persistent, duplicable) read-only register ownership.  Used for the
   configuration registers (misa, mseccfg, the PMP/PMA config, the HTIF base, ...)
   that the boot sequence never writes: once persisted they need not be threaded
   through (or returned by) every WP -- see [hw_config] in RiscvFetchExec.v. *)
Notation "r ↦ᵣ□ v" := (reg_pointsto r DfracDiscarded v)
  (at level 20, format "r  ↦ᵣ□  v") : bi_scope.
(* The concrete physical RAM of the platform: a single DRAM bank of
   [ram_size] bytes based at [ram_base] (0x80000000), matching the Sail
   model's RAM-region PMA (model-xv6iris/sail-config-rv64d.json) and the
   xv6 memory map: 128 MiB, so that [ram_base + ram_size] = xv6's PHYSTOP
   = 0x88000000 (kernel/memlayout.h; QEMU runs with `-m 128M`). *)
Definition ram_base : Z := 0x80000000.       (* 2147483648 *)
Definition ram_size : Z := 0x8000000.        (* 134217728 = 128 MiB *)

(* THE MMIO BAND, the platform's other configured region: one IOMemory window
   covering every device the kernel touches.  It is the model's OWN second PMA
   region ([RiscvLang.pma_boot], whose value is the compiled
   [ColdBoot.cold_boot_pma] fact), and every device window in the tree sits
   inside it -- CLINT at 0x2000000, PLIC [plic_base, +plic_size) =
   [0xC000000, 0xC400000), UART [uart_base, +8) at 0x10000000, virtio-mmio
   [virtio_base, +0x1000) at 0x10001000.  Unlike RAM it is NOT readable and
   writable by fiat: the band grants R/W but is NOT executable and does NOT
   support PTE reads/writes or atomics, which is exactly why the PMA premise
   the device towers take ([RiscvFetchExec.pma_allows_io]) is weaker than the
   RAM one and why the two address classes are stated separately. *)
Definition mmio_base : Z := 0x2000000.       (* 33554432 *)
Definition mmio_size : Z := 0x10000000.      (* 268435456 = 256 MiB *)


(* A physical byte address is "real" RAM iff it lies inside that DRAM bank.
   This is STRICTLY stronger than merely being outside the platform MMIO
   ranges: the whole bank sits above every MMIO window (CLINT ends at
   0x20C0000, SIG at 0xC000020, both far below 0x80000000), so being RAM
   discharges the model's [within_clint]/[within_sig] MMIO checks (see
   [addr_is_ram_not_in_clint]/[addr_is_ram_not_in_sig] below, which feed
   [within_clint_false]/[within_sig_false]).  Being a concrete range it also
   pins the address's high bits (bits 63:31 are 0b1..., bits 63:39 = 0), which
   lets the higher-level WPs discharge their per-address geometry obligations
   (Sv39 canonicality, identity translation, PMP TOR match) purely from an
   owned points-to rather than carrying them as explicit preconditions.
   ([within_htif] depends on the [htif_tohost_base] register, not the address,
   so it is handled separately by owning that register.) *)
Definition addr_is_ram (a : Arch.pa) : Prop :=
  (ram_base <= uint a < ram_base + ram_size)%Z.

(* rwx-kmap: the RAM bank split at etext.  [text_end] is hardcoded here to
   keep the base memory layer off the kernel dump (KernelSyms.etext =
   0x80007000 is cross-checked by vm_compute higher up: KptExecMap's
   [etext_vpn], KvmSpec).  Kernel TEXT [ram_base, text_end) is mapped R|X
   by the kernel page table, kernel DATA [text_end, PHYSTOP) R|W; the
   points-to layer records the region so stores to text are unprovable
   and fetches carry their own R|X evidence. *)
Definition text_end : Z := 0x80007000.
Definition addr_is_text (a : Arch.pa) : Prop :=
  (ram_base <= uint a < text_end)%Z.
Definition addr_is_kdata (a : Arch.pa) : Prop :=
  (text_end <= uint a < ram_base + ram_size)%Z.

Lemma addr_is_text_ram a : addr_is_text a -> addr_is_ram a.
Proof.
  unfold addr_is_text, addr_is_ram, text_end, ram_base, ram_size. lia.
Qed.
Lemma addr_is_kdata_ram a : addr_is_kdata a -> addr_is_ram a.
Proof.
  unfold addr_is_kdata, addr_is_ram, text_end, ram_base, ram_size. lia.
Qed.
Lemma addr_is_ram_split a : addr_is_ram a <-> addr_is_text a \/ addr_is_kdata a.
Proof.
  unfold addr_is_ram, addr_is_text, addr_is_kdata, text_end, ram_base, ram_size.
  lia.
Qed.

(* The two legacy MMIO-disjointness predicates, kept as the interface the
   model discharges ([within_clint_false]/[within_sig_false] consume them). *)
Definition not_in_clint (a : Arch.pa) : Prop :=
  (uint a < uint plat_clint_base \/ uint plat_clint_base + uint plat_clint_size <= uint a)%Z.
Definition not_in_sig (a : Arch.pa) : Prop :=
  (uint a < uint plat_sig_base \/ uint plat_sig_base + uint plat_sig_size <= uint a)%Z.

(* Being RAM implies being outside each MMIO window: the bank is above both. *)
Lemma addr_is_ram_not_in_clint a : addr_is_ram a -> not_in_clint a.
Proof.
  intros [Hlo _]. right.
  assert (uint plat_clint_base + uint plat_clint_size = 34340864)%Z as -> by (vm_compute; reflexivity).
  unfold ram_base in Hlo. lia.
Qed.

Lemma addr_is_ram_not_in_sig a : addr_is_ram a -> not_in_sig a.
Proof.
  intros [Hlo _]. right.
  assert (uint plat_sig_base + uint plat_sig_size = 201326624)%Z as -> by (vm_compute; reflexivity).
  unfold ram_base in Hlo. lia.
Qed.

(* Being RAM also implies being off the device fabric: the bus routes only
   sub-DRAM addresses ([dev_bound] = [ram_base]) to the UART/PLIC. *)
Lemma addr_is_ram_not_dev a : addr_is_ram a -> dev_addr a = false.
Proof.
  intros [Hlo _]. apply dev_addr_false.
  unfold dev_bound; unfold ram_base in Hlo. lia.
Qed.

(* ---------------------------------------------------------------------- *)
(* The kernel-mapping CLAIM (uniform-claims): a persisted fragment of the  *)
(* kernel-mapping ghost map -- "vpn maps to ppn at class pc, under the     *)
(* current and all future regimes" (monotone across Bare→Sv39).  It        *)
(* carries BOTH the permission and the va→pa mapping; the points-to facts  *)
(* below are built on it.  Uniqueness is ghost-map library agreement.      *)
(* The auth / static-map machinery lives in KMap.v.                        *)
(* ---------------------------------------------------------------------- *)

(* the vpn of an S-mode va (moved here from RiscvExtras; the arithmetic
   lemmas [svpn_of_unsigned]/[svpn_of_unsigned_lo] remain there) *)
Definition svpn_of (a : mword 64) : mword 27 :=
  SailStdpp.TypeCasts.autocast (T := mword) (subrange_vec_dec
     (subrange_vec_dec (bits_of_virtaddr (Virtaddr a)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits).

(* The mapping fragment.  The [ghost_map_elem] key instances are given
   EXPLICITLY (fully qualified) to match the [riscv_kmapGS] field's pinning
   -- RiscvPtsto must NOT [Import] the Sail instance modules (they would
   clobber stdpp's bv instances for [Arch.pa]=mword 64 gen_heap keys; the
   durable-notes leak), so we cannot rely on TC search resolving
   [EqDecision (mword 27)] here. *)
Definition kmap_at `{!riscvGS Σ} (vpn : mword 27) (ppn : mword 44) (pc : kperm) : iProp Σ :=
  @ghost_map_elem Σ (mword 27) (mword 44 * kperm)
    (@SailStdpp.Instances.Decidable_eq_mword 27)
    (@SailStdpp.Instances.Countable_mword 27)
    riscv_kmapGS kmap_name vpn DfracDiscarded (ppn, pc).

Global Instance kmap_at_persistent `{!riscvGS Σ} vpn ppn pc :
  Persistent (kmap_at vpn ppn pc).
Proof. apply _. Qed.
Global Instance kmap_at_timeless `{!riscvGS Σ} vpn ppn pc :
  Timeless (kmap_at vpn ppn pc).
Proof. apply _. Qed.

(* UNIQUENESS: two claims for one vpn agree -- what lets split fractions
   of a [↦ₘ] recombine (their existential ppn witnesses coincide). *)
Lemma kmap_at_agree `{!riscvGS Σ} vpn ppn1 pc1 ppn2 pc2 :
  kmap_at vpn ppn1 pc1 -∗ kmap_at vpn ppn2 pc2 -∗ ⌜ppn1 = ppn2 /\ pc1 = pc2⌝.
Proof.
  iIntros "H1 H2".
  iDestruct (ghost_map_elem_agree with "H1 H2") as %He.
  iPureIntro. injection He as -> ->. split; reflexivity.
Qed.

(* the pa a claim maps [va] to: the claim's ppn ++ [va]'s page offset *)
Definition pa_of (ppn : mword 44) (va : mword 64) : mword 64 :=
  zero_extend' 64 (concat_vec ppn (subrange_vec_dec va 11 0)).

(* memory points-to, VA-BASED (uniform-claims): owns the byte at the
   PHYSICAL address the kernel mapping takes [va] to, bundled with the
   claim itself.  The KP_rw class is what
   makes stores provable ONLY through writable mappings; the R|X kernel
   text lives at the CODE points-to [↦ₓ] below.  The canonicality
   conjunct (positive Sv39 half) pins va ↔ (vpn, offset).  [dq] is a
   [dfrac]: [DfracOwn 1] = full (writable) ownership, [DfracDiscarded] =
   persistent/duplicable read-only ownership (the immutable kernel
   globals image [kernel_data]).

   THE IDENTITY CONJUNCT [pa_of ppn va = va] (claude-notes/projects/
   bare-inv-generic.md).  A kernel datum's va is its physical address: the
   claim carried here is the STATIC (identity) one.  This is what makes a
   [↦ₘ] access sound under BOTH translation regimes -- a hart in Bare mode
   translates va to va itself, so a non-identity [↦ₘ] would be accessed at
   the WRONG page there, and no ghost resource can rule that out per-hart
   (a secondary hart is legitimately Bare long after the kernel map has
   grown).  So the identity is a conjunct of the resource rather than a
   premise on every leaf: the Bare regime's [sr_adm] admissibility premise
   (SRegime.v) is discharged from the datum itself, and no leaf statement
   or whole-function contract mentions it.
   CONSEQUENCE: a kernel-stack byte at [KSTACK(i)] is NOT expressible as a
   [↦ₘ] -- those pages stay at the PHYSICAL tier ([↦ₚ], [page_own] at the
   identity address).  When the sp-migration project needs S-mode
   loads/stores at a kstack va, the way in is a KPT-only leaf family whose
   [sr_adm] obligation the caller discharges (not a weakening here). *)
Definition mem_pointsto `{!riscvGS Σ} (va : Arch.pa) (dq : dfrac) (v : bv 8) : iProp Σ :=
  (∃ ppn : mword 44,
     kmap_at (svpn_of va) ppn KP_rw ∗
     ⌜(uint va < 274877906944)%Z⌝ ∗          (* 2^38: canonical, positive half *)
     ⌜addr_is_ram (pa_of ppn va)⌝ ∗
     ⌜pa_of ppn va = va⌝ ∗                   (* IDENTITY (see the note above) *)
     pointsto (L:=Arch.pa) (V:=bv 8) (pa_of ppn va) dq v)%I.
Notation "a ↦ₘ{ dq } v" := (mem_pointsto a dq v)
  (at level 20, format "a  ↦ₘ{ dq }  v") : bi_scope.
(* discarded (persistent, duplicable) read-only ownership. *)
Notation "a ↦ₘ□ v" := (mem_pointsto a DfracDiscarded v)
  (at level 20, format "a  ↦ₘ□  v") : bi_scope.
(* default: full (writable) ownership. *)
Notation "a ↦ₘ v" := (mem_pointsto a (DfracOwn 1) v)
  (at level 20, format "a  ↦ₘ  v") : bi_scope.

(* TIMELESS -- registered, because typeclass search does not unfold the
   [Definition] on its own: without this instance the [>] intro pattern on a
   byte taken out of an invariant fails with "iMod: cannot eliminate modality"
   on a hypothesis that visibly IS timeless. *)
Global Instance mem_pointsto_timeless `{!riscvGS Σ} (a : Arch.pa) (dq : dfrac) (v : bv 8) :
  Timeless (mem_pointsto a dq v).
Proof. rewrite /mem_pointsto. apply _. Qed.

(* ---------------------------------------------------------------------- *)
(* SHARING a byte: agreement and the fractional split.  [↦ₘ] carries a real
   [dfrac], so a resource that is read-only-while-shared (a reference-counted
   kernel object: [struct file]'s immutable fields, an inode's, a buf's) can
   be handed out at a fraction and RECOMBINED when the last share comes back.
   Agreement is what makes the value-knowledge come for free: two holders of
   the same byte cannot disagree, so no separate [agree] ghost is needed.
   The byte-window forms below lift straight to [↦₂]/[↦₄]/[↦₈].              *)
Section mem_pointsto_share.
  Context `{!riscvGS Σ}.

  (* two owners of the same byte, at ANY two dfracs, agree on its value. *)
  Lemma mem_pointsto_agree a dq1 b1 dq2 b2 :
    a ↦ₘ{dq1} b1 -∗ a ↦ₘ{dq2} b2 -∗ ⌜b1 = b2⌝.
  Proof.
    rewrite /mem_pointsto. iIntros "H1 H2".
    iDestruct "H1" as (ppn1) "(Hk1 & _ & _ & _ & Hp1)".
    iDestruct "H2" as (ppn2) "(Hk2 & _ & _ & _ & Hp2)".
    iDestruct (kmap_at_agree with "Hk1 Hk2") as %[-> _].
    by iDestruct (pointsto_agree with "Hp1 Hp2") as %->.
  Qed.

  (* ...and the DUAL of agreement: full ownership of a byte is EXCLUSIVE, so an
     address owned outright cannot be an address owned at any dfrac at all.
     This is what makes SEPARATION carry the disjointness of two buffers -- a
     function whose contract takes two byte ranges as separate conjuncts never
     needs a pure non-aliasing side condition; the aliasing case is refuted from
     the resources themselves (see [mem_bytes_notin]). *)
  Lemma mem_pointsto_ne a1 a2 dq b1 b2 :
    a1 ↦ₘ b1 -∗ a2 ↦ₘ{dq} b2 -∗ ⌜a1 ≠ a2⌝.
  Proof.
    rewrite /mem_pointsto. iIntros "H1 H2".
    iDestruct "H1" as (ppn1) "(Hk1 & _ & _ & _ & Hp1)".
    iDestruct "H2" as (ppn2) "(Hk2 & _ & _ & _ & Hp2)".
    destruct (decide (a1 = a2)) as [->|Hne]; [| by iPureIntro ].
    iDestruct (kmap_at_agree with "Hk1 Hk2") as %[-> _].
    by iDestruct (pointsto_ne with "Hp1 Hp2") as %Hne.
  Qed.

  (* the fractional split.  [kmap_at] is persistent, so the claim and the two
     pure conjuncts ride along on both halves at no cost. *)
  Lemma mem_pointsto_frac_split a q1 q2 b :
    a ↦ₘ{DfracOwn (q1 + q2)} b ⊣⊢ a ↦ₘ{DfracOwn q1} b ∗ a ↦ₘ{DfracOwn q2} b.
  Proof.
    rewrite /mem_pointsto. iSplit.
    - iIntros "H". iDestruct "H" as (ppn) "(#Hk & %Hc & %Hd & %Hi & Hp)".
      rewrite -dfrac_op_own pointsto_fractional.
      iDestruct "Hp" as "[Hp1 Hp2]".
      iSplitL "Hp1"; iExists ppn.
      + by iFrame "Hk Hp1".
      + by iFrame "Hk Hp2".
    - iIntros "[H1 H2]".
      iDestruct "H1" as (ppn1) "(#Hk1 & %Hc & %Hd & %Hi & Hp1)".
      iDestruct "H2" as (ppn2) "(#Hk2 & _ & _ & _ & Hp2)".
      iDestruct (kmap_at_agree with "Hk1 Hk2") as %[-> _].
      iDestruct (pointsto_combine with "Hp1 Hp2") as "[Hp _]".
      rewrite dfrac_op_own. iExists ppn2. by iFrame "Hk1 Hp".
  Qed.

  (* ---- the same two facts over a WINDOW of bytes, which is the form the
     [↦₂]/[↦₄]/[↦₈] bundles are built from.  Stated over an arbitrary start
     index [k] so the induction goes through. ---- *)

  Lemma mem_bytes_agree {m : N} (a : Arch.pa) (k n : nat) (dq1 dq2 : dfrac) (w1 w2 : bv m) :
    ([∗ list] j ∈ seq k n, (pa_add a j) ↦ₘ{dq1} nth_byte w1 j) -∗
    ([∗ list] j ∈ seq k n, (pa_add a j) ↦ₘ{dq2} nth_byte w2 j) -∗
    ⌜forall j, (k <= j < k + n)%nat -> nth_byte w1 j = nth_byte w2 j⌝.
  Proof.
    revert k. induction n as [|n IH]; intros k; simpl.
    - iIntros "_ _". iPureIntro. intros j Hj. lia.
    - iIntros "[Hh1 Ht1] [Hh2 Ht2]".
      iDestruct (mem_pointsto_agree with "Hh1 Hh2") as %Heq.
      iDestruct (IH (S k) with "Ht1 Ht2") as %Hrest.
      iPureIntro. intros j Hj.
      destruct (decide (j = k)) as [->|Hne]; [exact Heq|].
      apply Hrest. lia.
  Qed.

  (* an address held SEPARATELY from a byte buffer lies OUTSIDE that buffer.
     The two-buffer disjointness a copy loop needs ([memmove]'s src vs dst)
     follows by peeling one byte off the second buffer and applying this. *)
  Lemma mem_bytes_notin (a c : Arch.pa) (k n : nat) (dq : dfrac) (f : nat -> bv 8) (v : bv 8) :
    ([∗ list] j ∈ seq k n, (pa_add a j) ↦ₘ f j) -∗
    c ↦ₘ{dq} v -∗
    ⌜forall j, (k <= j < k + n)%nat -> pa_add a j <> c⌝.
  Proof.
    revert k. induction n as [|n IH]; intros k; simpl.
    - iIntros "_ _". iPureIntro. intros j Hj. lia.
    - iIntros "[Hh Ht] Hc".
      iDestruct (mem_pointsto_ne with "Hh Hc") as %Hne0.
      iDestruct (IH (S k) with "Ht Hc") as %Hrest.
      iPureIntro. intros j Hj.
      destruct (decide (j = k)) as [->|Hjk]; [exact Hne0|].
      apply Hrest. lia.
  Qed.

  Lemma mem_bytes_frac_split {m : N} (a : Arch.pa) (k n : nat) (q1 q2 : Qp) (w : bv m) :
    ([∗ list] j ∈ seq k n, (pa_add a j) ↦ₘ{DfracOwn (q1 + q2)} nth_byte w j) ⊣⊢
    ([∗ list] j ∈ seq k n, (pa_add a j) ↦ₘ{DfracOwn q1} nth_byte w j) ∗
    ([∗ list] j ∈ seq k n, (pa_add a j) ↦ₘ{DfracOwn q2} nth_byte w j).
  Proof.
    rewrite -big_sepL_sep. apply big_sepL_proper. intros ? j _.
    apply mem_pointsto_frac_split.
  Qed.

End mem_pointsto_share.

(* CODE points-to, VA-BASED (uniform-claims): the KP_rx analogue -- the
   claim + ownership of the mapped physical byte; identity for the static
   kernel-text fragments, non-identity for the TRAMPOLINE va once its
   fragment is minted at the boot switch.  [↦ₓ□] is the form the immutable
   kernel image lives at ([kernel_text]/[instr_bytes]). *)
Definition text_pointsto `{!riscvGS Σ} (va : Arch.pa) (dq : dfrac) (v : bv 8) : iProp Σ :=
  (∃ ppn : mword 44,
     kmap_at (svpn_of va) ppn KP_rx ∗
     ⌜(uint va < 274877906944)%Z⌝ ∗          (* 2^38: canonical, positive half *)
     ⌜addr_is_text (pa_of ppn va)⌝ ∗
     ⌜pa_of ppn va = va⌝ ∗                   (* IDENTITY (see [mem_pointsto]) *)
     pointsto (L:=Arch.pa) (V:=bv 8) (pa_of ppn va) dq v)%I.
Notation "a ↦ₓ{ dq } v" := (text_pointsto a dq v)
  (at level 20, format "a  ↦ₓ{ dq }  v") : bi_scope.
(* discarded (persistent, duplicable) read-only code ownership. *)
Notation "a ↦ₓ□ v" := (text_pointsto a DfracDiscarded v)
  (at level 20, format "a  ↦ₓ□  v") : bi_scope.
(* full ownership (pre-persist, e.g. at adequacy init). *)
Notation "a ↦ₓ v" := (text_pointsto a (DfracOwn 1) v)
  (at level 20, format "a  ↦ₓ  v") : bi_scope.

(* ---------------------------------------------------------------------- *)
(* PHYSICAL points-to (uniform-claims PHYSICAL TIER): ownership of the byte
   at the PHYSICAL address [pa], with no kernel-mapping claim -- the form for
   memory that is accessed UNTRANSLATED (the kernel page-table's own slots,
   read physically by the hardware walker; M-mode data/fetch, which has no
   translation).  This is the OLD pa-era [mem_pointsto] body verbatim.  The
   VA-based [↦ₘ]/[↦ₓ] above are for TRANSLATED kernel-variable/instruction
   access; a static (identity) va bridges the two tiers via the [pa_of_id]
   assembly/disassembly lemmas (KptPt/KMap). *)
Definition phys_pointsto `{!riscvGS Σ} (pa : Arch.pa) (dq : dfrac) (b : bv 8) : iProp Σ :=
  (pointsto (L:=Arch.pa) (V:=bv 8) pa dq b ∗ ⌜addr_is_ram pa⌝)%I.
Notation "a ↦ₚ{ dq } b" := (phys_pointsto a dq b)
  (at level 20, format "a  ↦ₚ{ dq }  b") : bi_scope.
Notation "a ↦ₚ□ b" := (phys_pointsto a DfracDiscarded b)
  (at level 20, format "a  ↦ₚ□  b") : bi_scope.
Notation "a ↦ₚ b" := (phys_pointsto a (DfracOwn 1) b)
  (at level 20, format "a  ↦ₚ  b") : bi_scope.

(* ---------------------------------------------------------------------- *)
(* word points-to: an 8-byte (doubleword) value [w] stored little-endian at a
   DOUBLEWORD-ALIGNED address [a].  Bundling the 8 byte points-to facts with
   the alignment lets an 8-byte load/store WP take a single [a ↦₈ w] hypothesis
   instead of a byte window PLUS a separate [is_aligned_paddr ... 8 = true]
   side condition -- the alignment travels with the ownership.  Both the paddr
   and (definitionally identical) vaddr alignment forms are recoverable.       *)
Definition word_pointsto `{!riscvGS Σ} (a : Arch.pa) (dq : dfrac) (w : bv 64) : iProp Σ :=
  (⌜is_aligned_paddr (Physaddr a) 8 = true⌝ ∗
   [∗ list] j ∈ seq 0 8, mem_pointsto (pa_add a j) dq (nth_byte w j))%I.
Notation "a ↦₈{ dq } w" := (word_pointsto a dq w)
  (at level 20, format "a  ↦₈{ dq }  w") : bi_scope.
Notation "a ↦₈ w" := (word_pointsto a (DfracOwn 1) w)
  (at level 20, format "a  ↦₈  w") : bi_scope.
(* discarded (persistent, duplicable) read-only ownership of the doubleword. *)
Notation "a ↦₈□ w" := (word_pointsto a DfracDiscarded w)
  (at level 20, format "a  ↦₈□  w") : bi_scope.

Section word_pointsto.
  Context `{!riscvGS Σ}.

  Lemma word_pointsto_aligned_p a dq w :
    word_pointsto a dq w ⊢ ⌜is_aligned_paddr (Physaddr a) 8 = true⌝.
  Proof. iIntros "[$ _]". Qed.
  Lemma word_pointsto_bytes a dq w :
    word_pointsto a dq w ⊢ [∗ list] j ∈ seq 0 8, (pa_add a j) ↦ₘ{dq} nth_byte w j.
  Proof. iIntros "[_ $]". Qed.
  (* repackage a byte window + its alignment fact into a word points-to *)
  Lemma word_pointsto_intro a dq w :
    is_aligned_paddr (Physaddr a) 8 = true ->
    ([∗ list] j ∈ seq 0 8, (pa_add a j) ↦ₘ{dq} nth_byte w j) ⊢ word_pointsto a dq w.
  Proof. iIntros (Hal) "H". by iFrame. Qed.
  Lemma word_pointsto_unfold a dq w :
    word_pointsto a dq w ⊣⊢
    ⌜is_aligned_paddr (Physaddr a) 8 = true⌝ ∗
    ([∗ list] j ∈ seq 0 8, (pa_add a j) ↦ₘ{dq} nth_byte w j).
  Proof. reflexivity. Qed.

  (* ---- sharing (see [mem_pointsto_share]) ---- *)
  Lemma word_pointsto_agree a dq1 w1 dq2 w2 :
    a ↦₈{dq1} w1 -∗ a ↦₈{dq2} w2 -∗ ⌜w1 = w2⌝.
  Proof.
    iIntros "[_ H1] [_ H2]".
    iDestruct (mem_bytes_agree with "H1 H2") as %Hb.
    iPureIntro. apply (bv_eq_of_bytes (n:=8)). intros j Hj. apply Hb. lia.
  Qed.
  Lemma word_pointsto_frac_split a q1 q2 w :
    a ↦₈{DfracOwn (q1 + q2)} w ⊣⊢ a ↦₈{DfracOwn q1} w ∗ a ↦₈{DfracOwn q2} w.
  Proof.
    rewrite /word_pointsto mem_bytes_frac_split.
    iSplit; [iIntros "[#$ [$ $]]" | iIntros "[[#$ $] [_ $]]"].
  Qed.
End word_pointsto.

(* ---------------------------------------------------------------------- *)
(* PHYSICAL 8-byte word points-to [↦ₚ₈]: the [↦₈] body over the PHYSICAL
   [↦ₚ] tier -- an 8-byte doubleword owned at physical addresses, for the
   page-table slots and M-mode.  Kept SEPARATE from the VA-based [↦₈]. *)
Definition phys_word_pointsto `{!riscvGS Σ} (a : Arch.pa) (dq : dfrac) (w : bv 64) : iProp Σ :=
  (⌜is_aligned_paddr (Physaddr a) 8 = true⌝ ∗
   [∗ list] j ∈ seq 0 8, phys_pointsto (pa_add a j) dq (nth_byte w j))%I.
Notation "a ↦ₚ₈{ dq } w" := (phys_word_pointsto a dq w)
  (at level 20, format "a  ↦ₚ₈{ dq }  w") : bi_scope.
Notation "a ↦ₚ₈ w" := (phys_word_pointsto a (DfracOwn 1) w)
  (at level 20, format "a  ↦ₚ₈  w") : bi_scope.
Notation "a ↦ₚ₈□ w" := (phys_word_pointsto a DfracDiscarded w)
  (at level 20, format "a  ↦ₚ₈□  w") : bi_scope.

Section phys_word_pointsto.
  Context `{!riscvGS Σ}.

  Lemma phys_word_pointsto_aligned_p a dq w :
    phys_word_pointsto a dq w ⊢ ⌜is_aligned_paddr (Physaddr a) 8 = true⌝.
  Proof. iIntros "[$ _]". Qed.
  Lemma phys_word_pointsto_bytes a dq w :
    phys_word_pointsto a dq w ⊢ [∗ list] j ∈ seq 0 8, (pa_add a j) ↦ₚ{dq} nth_byte w j.
  Proof. iIntros "[_ $]". Qed.
  Lemma phys_word_pointsto_intro a dq w :
    is_aligned_paddr (Physaddr a) 8 = true ->
    ([∗ list] j ∈ seq 0 8, (pa_add a j) ↦ₚ{dq} nth_byte w j) ⊢ phys_word_pointsto a dq w.
  Proof. iIntros (Hal) "H". by iFrame. Qed.
  Lemma phys_word_pointsto_unfold a dq w :
    phys_word_pointsto a dq w ⊣⊢
    ⌜is_aligned_paddr (Physaddr a) 8 = true⌝ ∗
    ([∗ list] j ∈ seq 0 8, (pa_add a j) ↦ₚ{dq} nth_byte w j).
  Proof. reflexivity. Qed.
End phys_word_pointsto.

(* ---------------------------------------------------------------------- *)
(* 2-byte halfword points-to: a 2-byte value [w] stored little-endian at a
   HALFWORD-ALIGNED address [a].  The exact 2-byte analogue of [word4_pointsto]
   ([↦₄]) -- what an [lh]/[sh] to a C [short] field takes (e.g. [struct
   file]'s [major]).                                                          *)
Definition word2_pointsto `{!riscvGS Σ} (a : Arch.pa) (dq : dfrac) (w : bv 16) : iProp Σ :=
  (⌜is_aligned_paddr (Physaddr a) 2 = true⌝ ∗
   [∗ list] j ∈ seq 0 2, mem_pointsto (pa_add a j) dq (nth_byte w j))%I.
Notation "a ↦₂{ dq } w" := (word2_pointsto a dq w)
  (at level 20, format "a  ↦₂{ dq }  w") : bi_scope.
Notation "a ↦₂ w" := (word2_pointsto a (DfracOwn 1) w)
  (at level 20, format "a  ↦₂  w") : bi_scope.
(* discarded (persistent, duplicable) read-only ownership of the halfword. *)
Notation "a ↦₂□ w" := (word2_pointsto a DfracDiscarded w)
  (at level 20, format "a  ↦₂□  w") : bi_scope.

Section word2_pointsto.
  Context `{!riscvGS Σ}.

  Lemma word2_pointsto_aligned_p a dq w :
    word2_pointsto a dq w ⊢ ⌜is_aligned_paddr (Physaddr a) 2 = true⌝.
  Proof. iIntros "[$ _]". Qed.
  Lemma word2_pointsto_bytes a dq w :
    word2_pointsto a dq w ⊢ [∗ list] j ∈ seq 0 2, (pa_add a j) ↦ₘ{dq} nth_byte w j.
  Proof. iIntros "[_ $]". Qed.
  Lemma word2_pointsto_intro a dq w :
    is_aligned_paddr (Physaddr a) 2 = true ->
    ([∗ list] j ∈ seq 0 2, (pa_add a j) ↦ₘ{dq} nth_byte w j) ⊢ word2_pointsto a dq w.
  Proof. iIntros (Hal) "H". by iFrame. Qed.
  Lemma word2_pointsto_unfold a dq w :
    word2_pointsto a dq w ⊣⊢
    ⌜is_aligned_paddr (Physaddr a) 2 = true⌝ ∗
    ([∗ list] j ∈ seq 0 2, (pa_add a j) ↦ₘ{dq} nth_byte w j).
  Proof. reflexivity. Qed.

  (* ---- sharing (see [mem_pointsto_share]) ---- *)
  Lemma word2_pointsto_agree a dq1 w1 dq2 w2 :
    a ↦₂{dq1} w1 -∗ a ↦₂{dq2} w2 -∗ ⌜w1 = w2⌝.
  Proof.
    iIntros "[_ H1] [_ H2]".
    iDestruct (mem_bytes_agree with "H1 H2") as %Hb.
    iPureIntro. apply (bv_eq_of_bytes (n:=2)). intros j Hj. apply Hb. lia.
  Qed.
  Lemma word2_pointsto_frac_split a q1 q2 w :
    a ↦₂{DfracOwn (q1 + q2)} w ⊣⊢ a ↦₂{DfracOwn q1} w ∗ a ↦₂{DfracOwn q2} w.
  Proof.
    rewrite /word2_pointsto mem_bytes_frac_split.
    iSplit; [iIntros "[#$ [$ $]]" | iIntros "[[#$ $] [_ $]]"].
  Qed.
End word2_pointsto.

(* ---------------------------------------------------------------------- *)
(* 4-byte word points-to: a 4-byte (word) value [w] stored little-endian at a
   WORD-ALIGNED address [a].  The exact 4-byte analogue of [word_pointsto]
   ([↦₈]): bundling the 4 byte points-to facts with the 4-byte alignment lets
   a 4-byte load/store WP take a single [a ↦₄ w] hypothesis instead of a byte
   window PLUS a separate [is_aligned_paddr ... 4 = true] side condition.      *)
Definition word4_pointsto `{!riscvGS Σ} (a : Arch.pa) (dq : dfrac) (w : bv 32) : iProp Σ :=
  (⌜is_aligned_paddr (Physaddr a) 4 = true⌝ ∗
   [∗ list] j ∈ seq 0 4, mem_pointsto (pa_add a j) dq (nth_byte w j))%I.
Notation "a ↦₄{ dq } w" := (word4_pointsto a dq w)
  (at level 20, format "a  ↦₄{ dq }  w") : bi_scope.
Notation "a ↦₄ w" := (word4_pointsto a (DfracOwn 1) w)
  (at level 20, format "a  ↦₄  w") : bi_scope.
(* discarded (persistent, duplicable) read-only ownership of the word. *)
Notation "a ↦₄□ w" := (word4_pointsto a DfracDiscarded w)
  (at level 20, format "a  ↦₄□  w") : bi_scope.

(* TIMELESS, for the same reason as [mem_pointsto_timeless] above: this is what
   lets an invariant over a 4-byte cell ([StartedInv.started_body], the panic
   flags) hand the cell out from under the [▷]. *)
Global Instance word4_pointsto_timeless `{!riscvGS Σ} (a : Arch.pa) (dq : dfrac) (w : bv 32) :
  Timeless (word4_pointsto a dq w).
Proof. rewrite /word4_pointsto. apply _. Qed.

Section word4_pointsto.
  Context `{!riscvGS Σ}.

  Lemma word4_pointsto_aligned_p a dq w :
    word4_pointsto a dq w ⊢ ⌜is_aligned_paddr (Physaddr a) 4 = true⌝.
  Proof. iIntros "[$ _]". Qed.
  Lemma word4_pointsto_bytes a dq w :
    word4_pointsto a dq w ⊢ [∗ list] j ∈ seq 0 4, (pa_add a j) ↦ₘ{dq} nth_byte w j.
  Proof. iIntros "[_ $]". Qed.
  (* repackage a byte window + its alignment fact into a word points-to *)
  Lemma word4_pointsto_intro a dq w :
    is_aligned_paddr (Physaddr a) 4 = true ->
    ([∗ list] j ∈ seq 0 4, (pa_add a j) ↦ₘ{dq} nth_byte w j) ⊢ word4_pointsto a dq w.
  Proof. iIntros (Hal) "H". by iFrame. Qed.
  Lemma word4_pointsto_unfold a dq w :
    word4_pointsto a dq w ⊣⊢
    ⌜is_aligned_paddr (Physaddr a) 4 = true⌝ ∗
    ([∗ list] j ∈ seq 0 4, (pa_add a j) ↦ₘ{dq} nth_byte w j).
  Proof. reflexivity. Qed.

  (* ---- sharing (see [mem_pointsto_share]) ---- *)
  Lemma word4_pointsto_agree a dq1 w1 dq2 w2 :
    a ↦₄{dq1} w1 -∗ a ↦₄{dq2} w2 -∗ ⌜w1 = w2⌝.
  Proof.
    iIntros "[_ H1] [_ H2]".
    iDestruct (mem_bytes_agree with "H1 H2") as %Hb.
    iPureIntro. apply (bv_eq_of_bytes (n:=4)). intros j Hj. apply Hb. lia.
  Qed.
  Lemma word4_pointsto_frac_split a q1 q2 w :
    a ↦₄{DfracOwn (q1 + q2)} w ⊣⊢ a ↦₄{DfracOwn q1} w ∗ a ↦₄{DfracOwn q2} w.
  Proof.
    rewrite /word4_pointsto mem_bytes_frac_split.
    iSplit; [iIntros "[#$ [$ $]]" | iIntros "[[#$ $] [_ $]]"].
  Qed.

  (* THE 1/2 + 1/2 SPLIT, which is the fraction a shared 4-byte cell is
     actually held at all over the kernel: [p->pid]'s permanent half in the
     scheduler invariant against allocproc's (ProcInv.v), and the bio layer's
     [b->dev] / [b->blockno], whose bcache half and escrow half are joined for
     every write and re-split after it.  Stated with the fractions PINNED --
     [rewrite -(Qp.div_2 1)] would also match the [1] inside a [1/2] already in
     the goal and produce [(1/2 + 1/2)/2] -- and given in all three shapes,
     because the join direction is used as a wand and the split as a rewrite. *)
  Lemma word4_pointsto_half a w :
    a ↦₄ w ⊣⊢ a ↦₄{DfracOwn (1/2)} w ∗ a ↦₄{DfracOwn (1/2)} w.
  Proof. rewrite -word4_pointsto_frac_split Qp.div_2. reflexivity. Qed.

  Lemma word4_pointsto_half_split a w :
    a ↦₄ w -∗ a ↦₄{DfracOwn (1/2)} w ∗ a ↦₄{DfracOwn (1/2)} w.
  Proof. rewrite word4_pointsto_half. iIntros "$". Qed.

  Lemma word4_pointsto_half_join a w :
    a ↦₄{DfracOwn (1/2)} w -∗ a ↦₄{DfracOwn (1/2)} w -∗ a ↦₄ w.
  Proof. iIntros "H1 H2". rewrite word4_pointsto_half. iFrame "H1 H2". Qed.
End word4_pointsto.

(* ---------------------------------------------------------------------- *)
(* string points-to: a NUL-terminated C string [s] resident byte-by-byte at
   consecutive addresses starting at [a].  Built DIRECTLY on the single-byte
   memory points-to [↦ₘ] -- character [j] of [s] at [a+j], the terminating NUL
   at [a+|s|] -- with no alignment side condition, a C string being
   byte-addressed (this is what distinguishes it from [↦₈]/[↦₄]).

   The intended fraction is [DfracDiscarded]: the kernel's string literals are
   read-only image bytes that nothing ever writes, so [a ↦ₛ□ s] is PERSISTENT
   and hence freely DUPLICABLE -- it can be passed to a callee and kept, and it
   can sit inside a persistent predicate.  That is what lets a lock carry its
   own name ([lock_name], WpLock.v) at no ownership cost.                     *)
(* ---------------------------------------------------------------------- *)

(* the characters of [s] as bytes (no terminator) *)
Fixpoint string_bytes (s : string) : list (bv 8) :=
  match s with
  | String.EmptyString => []
  | String.String c s' => Z_to_bv 8 (Z.of_N (Ascii.N_of_ascii c)) :: string_bytes s'
  end.

(* the C representation of [s]: its characters followed by the NUL byte *)
Definition cstring_bytes (s : string) : list (bv 8) :=
  string_bytes s ++ [Z_to_bv 8 0].

Definition string_pointsto `{!riscvGS Σ} (a : Arch.pa) (dq : dfrac)
    (s : string) : iProp Σ :=
  ([∗ list] j ↦ b ∈ cstring_bytes s, mem_pointsto (pa_add a j) dq b)%I.
Notation "a ↦ₛ{ dq } s" := (string_pointsto a dq s)
  (at level 20, format "a  ↦ₛ{ dq }  s") : bi_scope.
(* discarded (persistent, duplicable) read-only ownership -- the default for a
   kernel string literal. *)
Notation "a ↦ₛ□ s" := (string_pointsto a DfracDiscarded s)
  (at level 20, format "a  ↦ₛ□  s") : bi_scope.
Notation "a ↦ₛ s" := (string_pointsto a (DfracOwn 1) s)
  (at level 20, format "a  ↦ₛ  s") : bi_scope.

Section string_pointsto.
  Context `{!riscvGS Σ}.

  Global Instance string_pointsto_persistent a s : Persistent (a ↦ₛ□ s).
  Proof. rewrite /string_pointsto /mem_pointsto. apply _. Qed.

  Lemma string_pointsto_bytes a dq s :
    string_pointsto a dq s ⊣⊢
    [∗ list] j ↦ b ∈ cstring_bytes s, (pa_add a j) ↦ₘ{dq} b.
  Proof. reflexivity. Qed.

  (* the terminating NUL is the last byte owned *)
  Lemma cstring_bytes_length s :
    length (cstring_bytes s) = S (String.length s).
  Proof.
    rewrite /cstring_bytes length_app /=.
    induction s as [|c s IH]; simpl; [reflexivity | rewrite IH; reflexivity].
  Qed.
End string_pointsto.

(* ---------------------------------------------------------------------- *)
(* 2. The bridge: an existential register map agreeing with [regstate].    *)
(* ---------------------------------------------------------------------- *)

Definition reg_agree (m : gmap register (sigT type_of_register))
    (rs : regstate) : Prop :=
  forall r dv, m !! r = Some dv -> dv = existT r (register_lookup r rs).

(* the register bridge for a GIVEN hart's ghost name [γ]. *)
Definition reg_interp_at `{!riscvFixedGS Σ} (γ : gname) (rs : regstate) : iProp Σ :=
  (∃ m, ghost_map_auth γ 1 m ∗ ⌜reg_agree m rs⌝)%I.

(* the bridge for the AMBIENT hart -- what the WPs manipulate.  Original arity
   ([rs] only): the hart is [cpu_id], carried by [reg_name]. *)
Definition reg_interp `{!riscvGS Σ} `{CpuId} (rs : regstate) : iProp Σ :=
  reg_interp_at reg_name rs.

(* ---------------------------------------------------------------------- *)
(* device-fabric ownership: the halves pattern over two [ghost_var]s.       *)
(* [uart_auth]/[plic_auth] live inside [state_interp]; [uart_frag]/         *)
(* [plic_frag] are the user-facing halves.  Agreement + joint update are    *)
(* the two bridge lemmas, mirroring [reg_valid]/[reg_update].               *)
(* ---------------------------------------------------------------------- *)

Definition uart_auth `{!riscvGS Σ} (u : uart_state) : iProp Σ :=
  ghost_var uart_name (1/2) u.
Definition uart_frag `{!riscvGS Σ} (u : uart_state) : iProp Σ :=
  ghost_var uart_name (1/2) u.
Definition plic_auth `{!riscvGS Σ} (p : plic_state) : iProp Σ :=
  ghost_var plic_name (1/2) p.
Definition plic_frag `{!riscvGS Σ} (p : plic_state) : iProp Σ :=
  ghost_var plic_name (1/2) p.
Definition virtio_auth `{!riscvGS Σ} (v : virtio_state) : iProp Σ :=
  ghost_var virtio_name (1/2) v.
Definition virtio_frag `{!riscvGS Σ} (v : virtio_state) : iProp Σ :=
  ghost_var virtio_name (1/2) v.

(* the state_interp conjunct for the shared device state *)
Definition dev_interp `{!riscvGS Σ} (d : dev_state) : iProp Σ :=
  (uart_auth d.(duart) ∗ plic_auth d.(dplic) ∗ virtio_auth d.(dvirtio))%I.

Section DevBridge.
  Context `{!riscvGS Σ}.

  Lemma uart_agree u u' : uart_auth u -∗ uart_frag u' -∗ ⌜u' = u⌝.
  Proof.
    iIntros "Ha Hf". by iDestruct (ghost_var_agree with "Ha Hf") as %->.
  Qed.
  Lemma uart_update u u' u'' :
    uart_auth u -∗ uart_frag u' ==∗ uart_auth u'' ∗ uart_frag u''.
  Proof. iApply ghost_var_update_halves. Qed.

  Lemma plic_agree p p' : plic_auth p -∗ plic_frag p' -∗ ⌜p' = p⌝.
  Proof.
    iIntros "Ha Hf". by iDestruct (ghost_var_agree with "Ha Hf") as %->.
  Qed.
  Lemma plic_update p p' p'' :
    plic_auth p -∗ plic_frag p' ==∗ plic_auth p'' ∗ plic_frag p''.
  Proof. iApply ghost_var_update_halves. Qed.

  Lemma virtio_agree v v' : virtio_auth v -∗ virtio_frag v' -∗ ⌜v' = v⌝.
  Proof.
    iIntros "Ha Hf". by iDestruct (ghost_var_agree with "Ha Hf") as %->.
  Qed.
  Lemma virtio_update v v' v'' :
    virtio_auth v -∗ virtio_frag v' ==∗ virtio_auth v'' ∗ virtio_frag v''.
  Proof. iApply ghost_var_update_halves. Qed.
End DevBridge.

(* one hart's view (its registers + the shared memory + the shared device
   fabric); the single-CPU [state_interp σ ns κs nt] of the leaf lemmas is
   replaced by [mstate_interp σ].  The device conjunct rides in LAST
   position: a leaf that only touches registers/memory frames it through
   untouched (an exec over set_reg/write_bytes preserves [mdev]
   definitionally). *)
Definition mstate_interp `{!riscvGS Σ} `{CpuId} (σ : mstate) : iProp Σ :=
  (reg_interp σ.(sregs) ∗ gen_heap_interp σ.(mem) ∗ dev_interp σ.(mdev))%I.

(* the GLOBAL register bridge: one authoritative map per hart, over the whole
   finite [CPU] set.  [gregs] is a total function, so there is no membership
   side condition -- [gregs_interp_acc] focuses any [cpu_id] unconditionally. *)
Definition gregs_interp `{!riscvGS Σ} (gr : CPU -> regstate) : iProp Σ :=
  ([∗ set] cpu ∈ (fin_to_set CPU : gset CPU), reg_interp_at (cpu_reg_name cpu) (gr cpu))%I.

(* ---------------------------------------------------------------------- *)
(* 3. irisGS instance (claude-notes/design/crash.md).  [state_interp] is    *)
(*    defined over the FIXED layer ALONE and holds the CURRENT era          *)
(*    existentially: [wp] is sealed over the whole [irisGS] record, so     *)
(*    threads of different generations share a WP connective only if the   *)
(*    instance never mentions the era.  The ambient era of a thread's      *)
(*    [riscvGS] reappears at the base rules, where the registry element    *)
(*    in its [gen_cert] ties it to the existential.                        *)
(* ---------------------------------------------------------------------- *)

(* the state_interp conjuncts of an ARBITRARY era.  The ambient forms
   ([gregs_interp]/[gen_heap_interp (hG := riscv_memGS)]/[dev_interp]) are
   these at [riscv_eraGS], definitionally. *)
Definition gregs_interp_at `{!riscvFixedGS Σ} (E : riscvEraGS)
    (gr : CPU -> regstate) : iProp Σ :=
  ([∗ set] cpu ∈ (fin_to_set CPU : gset CPU),
     reg_interp_at (era_reg_name E cpu) (gr cpu))%I.
Definition dev_interp_at `{!riscvFixedGS Σ} (E : riscvEraGS)
    (d : dev_state) : iProp Σ :=
  (ghost_var (era_uart_name E) (1/2) d.(duart) ∗
   ghost_var (era_plic_name E) (1/2) d.(dplic) ∗
   ghost_var (era_virtio_name E) (1/2) d.(dvirtio))%I.
(* the era's four conjuncts.  The DISK IMAGE rides here, in LAST position,
   rather than beside the fixed conjuncts: it is per-era (see
   [era_disk_name]), so when the power is off there is no disk conjunct at
   all -- the era, and its image map, are gone. *)
Definition era_interp `{!riscvFixedGS Σ} (E : riscvEraGS) (g : gstate) : iProp Σ :=
  (gregs_interp_at E g.(gregs) ∗
   gen_heap_interp (hG := era_memGS_of E) g.(gmem) ∗
   dev_interp_at E g.(gdev) ∗
   disk_dur_interp E g)%I.

(* THE FS TIE's MACHINE SIDE: [state_interp]'s half, always at the machine's
   own disk image.  A FIXED conjunct, NOT part of [era_interp]: the disk (and
   hence its mirror) is the one thing a power cycle preserves, so the tie must
   survive PowerOff -- both power arms simply FRAME it ([boot_shape] preserves
   [v_disk]).  Of the whole machine only the DMA completion moves [v_disk], so
   only [RiscvExec.wp_disk_step] hands this conjunct to its callback; the hart,
   UART and PLIC rules frame it through their own [v_disk]-preservation
   lemmas. *)
Definition fs_tie_interp `{!riscvFixedGS Σ} (g : gstate) : iProp Σ :=
  disk_tie (v_disk (dvirtio (gdev g))).

Definition power_interp `{!riscvFixedGS Σ} (g : gstate) : iProp Σ :=
  (gen_auth g.(ggen) ∗ start_auth (start_count g) ∗ fs_tie_interp g ∗
   (∃ R : gmap nat riscvEraGS,
      ghost_map_auth riscv_registry_name 1 R ∗
      ⌜dom R = set_seq 0 (start_count g)⌝ ∗
      (if g.(gpow) then (∃ E, ⌜R !! g.(ggen) = Some E⌝ ∗ era_interp E g)%I
       else True%I)))%I.

Global Program Instance riscv_irisGS `{!riscvFixedGS Σ} : irisGS riscv_lang Σ := {
  iris_invGS := riscvF_invGS;
  state_interp g _ _ _ := power_interp g;
  fork_post _ := True%I;
  num_laters_per_step _ := 0%nat;
}.
Next Obligation. intros. iIntros "H". by iModIntro. Qed.

(* [to_val] is unconditionally [None] for every [expr riscv_lang] (there are
   no values -- [mval := Empty_set]), so the [Some v] case of [wp_pre] is
   dead code and a WP never actually inspects its postcondition: any two
   postconditions give provably equivalent WPs ([wp_mono] discharged by a
   vacuous case analysis on [Empty_set]). [wp_triv] pins the postcondition to
   the canonical [True], and the notations below drop the now-pointless
   [{{ Φ }}] clause entirely -- every WP in this project is over riscv_lang,
   so a postcondition position never needs to be written at all. *)
Lemma wp_post_irrel `{!irisGS riscv_lang Σ} s E (e : expr riscv_lang) (Φ1 Φ2 : mval -> iProp Σ) :
  WP e @ s; E {{ Φ1 }} ⊢ WP e @ s; E {{ Φ2 }}.
Proof. iApply wp_mono. iIntros ([]). Qed.

Definition wp_triv `{!irisGS riscv_lang Σ} (E : coPset) (e : expr riscv_lang) : iProp Σ :=
  WP e @ E {{ _, True%I }}.

Lemma wp_triv_eq `{!irisGS riscv_lang Σ} E e Φ : wp_triv E e ⊣⊢ WP e @ E {{ Φ }}.
Proof. rewrite /wp_triv. iSplit; iApply wp_post_irrel. Qed.

Notation "'WP' e @ E" := (wp_triv E e%E) (at level 20, e at level 20) : bi_scope.
Notation "'WP' e" := (wp_triv ⊤ e%E) (at level 20, e at level 20) : bi_scope.

(* Focus the ambient hart's register bridge out of the global one, with a
   frame-preserving update handle to put an updated bridge back.  This is the
   single point where per-hart framing happens; leaf WPs never see it. *)
Lemma gregs_interp_acc `{!riscvGS Σ} `{CpuId} (gr : CPU -> regstate) :
  gregs_interp gr ⊢ reg_interp (gr cpu_id) ∗
    (∀ rs', reg_interp rs' -∗ gregs_interp (<[cpu_id := rs']> gr)).
Proof.
  rewrite /gregs_interp /reg_interp /reg_name.
  iIntros "H".
  iDestruct (big_sepS_delete _ _ cpu_id with "H") as "[Hcur Hrest]";
    [ apply elem_of_fin_to_set |].
  iFrame "Hcur".
  iIntros (rs') "Hrs'".
  iApply (big_sepS_delete _ _ cpu_id); [ apply elem_of_fin_to_set |].
  rewrite /insert /greg_insert decide_True //.
  iFrame "Hrs'".
  iApply (big_sepS_mono with "Hrest").
  intros cpu Hcpu. apply elem_of_difference in Hcpu as [_ Hne].
  rewrite decide_False; [ done | ].
  intros ->. apply Hne, elem_of_singleton. reflexivity.
Qed.

(* ---------------------------------------------------------------------- *)
(* 3b. Per-hart register ownership for an EXPLICIT (non-ambient) hart:      *)
(*     [reg_pointsto_at c r] is the [↦ᵣ]-analogue for hart [c], with its    *)
(*     bridge lemmas against [reg_interp_at] and the explicit-hart focusing  *)
(*     lemma [gregs_interp_acc_at].  Needed by any proof that touches        *)
(*     ANOTHER hart's registers -- e.g. the device thread's wire step        *)
(*     writes hart [c]'s [sig_seip] pin (WpUart.v), and the wire invariant   *)
(*     (WireInv.v) owns every hart's interrupt pins.                          *)
(* ---------------------------------------------------------------------- *)

Section RegAt.
  Context `{!riscvGS Σ}.

  (* [r ↦ᵣ v] for an EXPLICIT hart [c] (the ambient-[CpuId] [reg_pointsto]
     is [reg_pointsto_at cpu_id]). *)
  Definition reg_pointsto_at (c : CPU) (r : register) (dq : dfrac)
      (v : type_of_register r) : iProp Σ :=
    ghost_map_elem (cpu_reg_name c) r dq (existT r v).

  Global Instance reg_pointsto_at_timeless c r dq v :
    Timeless (reg_pointsto_at c r dq v).
  Proof. rewrite /reg_pointsto_at. apply _. Qed.

  Lemma reg_valid_at (c : CPU) rs r dq v :
    reg_interp_at (cpu_reg_name c) rs -∗ reg_pointsto_at c r dq v -∗
    ⌜register_lookup r rs = v⌝.
  Proof.
    rewrite /reg_pointsto_at /reg_interp_at.
    iIntros "Hi Hr". iDestruct "Hi" as (m) "[Hm %Hag]".
    iDestruct (ghost_map_lookup with "Hm Hr") as %Hlk.
    iPureIntro. symmetry. by apply reg_existT_inj, (Hag r _ Hlk).
  Qed.

  Lemma reg_update_at (c : CPU) rs r v v' :
    reg_interp_at (cpu_reg_name c) rs -∗ reg_pointsto_at c r (DfracOwn 1) v ==∗
      reg_interp_at (cpu_reg_name c) (register_set r v' rs) ∗
      reg_pointsto_at c r (DfracOwn 1) v'.
  Proof.
    rewrite /reg_pointsto_at /reg_interp_at.
    iIntros "Hi Hr". iDestruct "Hi" as (m) "[Hm %Hag]".
    iMod (ghost_map_update (existT r v') with "Hm Hr") as "[Hm $]".
    iModIntro. iExists (<[r := existT r v']> m). iFrame "Hm".
    iPureIntro. intros k dv Hk.
    destruct (decide (k = r)) as [->|Hne].
    - rewrite lookup_insert in Hk. injection Hk as <-.
      by rewrite register_lookup_set.
    - rewrite lookup_insert_ne in Hk; [|done].
      rewrite (Hag k dv Hk).
      by rewrite (irrelevant_register_set k r rs v' (register_beq_false k r Hne)).
  Qed.

  (* focus an ARBITRARY hart [c]'s register bridge out of the global one
     (the ambient [gregs_interp_acc] fixed [c := cpu_id]). *)
  Lemma gregs_interp_acc_at (c : CPU) (gr : CPU -> regstate) :
    gregs_interp gr ⊢ reg_interp_at (cpu_reg_name c) (gr c) ∗
      (∀ rs', reg_interp_at (cpu_reg_name c) rs' -∗ gregs_interp (<[c := rs']> gr)).
  Proof.
    rewrite /gregs_interp.
    iIntros "H".
    iDestruct (big_sepS_delete _ _ c with "H") as "[Hcur Hrest]";
      [ apply elem_of_fin_to_set |].
    iFrame "Hcur".
    iIntros (rs') "Hrs'".
    iApply (big_sepS_delete _ _ c); [ apply elem_of_fin_to_set |].
    rewrite /insert /greg_insert decide_True //.
    iFrame "Hrs'".
    iApply (big_sepS_mono with "Hrest").
    intros cpu Hcpu. apply elem_of_difference in Hcpu as [_ Hne].
    rewrite decide_False; [ done | ].
    intros ->. apply Hne, elem_of_singleton. reflexivity.
  Qed.
End RegAt.

(* ---------------------------------------------------------------------- *)
(* 4. Bridge lemmas.                                                       *)
(* ---------------------------------------------------------------------- *)

Section Bridge.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  (* reading a register cell agrees with the model's [register_lookup]. *)
  Lemma reg_valid rs r v :
    reg_interp rs -∗ r ↦ᵣ v -∗ ⌜register_lookup r rs = v⌝.
  Proof.
    rewrite /reg_pointsto /reg_interp /reg_interp_at.
    iIntros "Hi Hr". iDestruct "Hi" as (m) "[Hm %Hag]".
    iDestruct (ghost_map_lookup with "Hm Hr") as %Hlk.
    iPureIntro. symmetry. by apply reg_existT_inj, (Hag r _ Hlk).
  Qed.

  (* writing a register cell tracks the model's [register_set]. *)
  Lemma reg_update rs r v v' :
    reg_interp rs -∗ r ↦ᵣ v ==∗
      reg_interp (register_set r v' rs) ∗ r ↦ᵣ v'.
  Proof.
    rewrite /reg_pointsto /reg_interp /reg_interp_at.
    iIntros "Hi Hr". iDestruct "Hi" as (m) "[Hm %Hag]".
    iMod (ghost_map_update (existT r v') with "Hm Hr") as "[Hm $]".
    iModIntro. iExists (<[r := existT r v']> m). iFrame "Hm".
    iPureIntro. intros k dv Hk.
    destruct (decide (k = r)) as [->|Hne].
    - rewrite lookup_insert in Hk. injection Hk as <-.
      by rewrite register_lookup_set.
    - rewrite lookup_insert_ne in Hk; [|done].
      rewrite (Hag k dv Hk).
      by rewrite (irrelevant_register_set k r rs v' (register_beq_false k r Hne)).
  Qed.

  (* reading a register cell at ANY fraction -- in particular a persistent
     [r ↦ᵣ□ v].  ([reg_valid] is the [DfracOwn 1] special case.) *)
  Lemma reg_valid_dq rs r dq v :
    reg_interp rs -∗ reg_pointsto r dq v -∗ ⌜register_lookup r rs = v⌝.
  Proof.
    rewrite /reg_pointsto /reg_interp /reg_interp_at.
    iIntros "Hi Hr". iDestruct "Hi" as (m) "[Hm %Hag]".
    iDestruct (ghost_map_lookup with "Hm Hr") as %Hlk.
    iPureIntro. symmetry. by apply reg_existT_inj, (Hag r _ Hlk).
  Qed.

  (* a discarded (read-only) register cell is persistent -- hence duplicable and
     never consumed, so a WP that only READS it need neither take a fresh copy nor
     hand one back. *)
  Global Instance reg_pointsto_discarded_persistent r v : Persistent (r ↦ᵣ□ v).
  Proof. rewrite /reg_pointsto. apply _. Qed.

  (* KEEP-UNREFERENCED: public bridge API (fraction-discard / duplication).  Kept
     for downstream use even though currently unreferenced -- do not delete. *)
  (* discard the fraction: turn an owned register cell into the persistent one. *)
  Lemma reg_pointsto_persist r dq v : reg_pointsto r dq v ==∗ r ↦ᵣ□ v.
  Proof. rewrite /reg_pointsto. iIntros "Hr". by iMod (ghost_map_elem_persist with "Hr"). Qed.

  (* ---- the VA-based ↦ₘ ACCESSOR (uniform-claims) ---- *)
  (* THE primitive the ↦ₘ suite rests on: expose the mapping claim, the
     canonicality/kdata facts, and OWNERSHIP of the mapped PHYSICAL byte
     [pa_of ppn a], with a re-fold wand.  A tower does its gen_heap op at
     [pa_of ppn a] (the pa its regime absorbs [a] to) and re-folds. *)
  Lemma mem_pointsto_acc a dq b :
    a ↦ₘ{dq} b -∗ ∃ ppn : mword 44,
      kmap_at (svpn_of a) ppn KP_rw ∗
      ⌜(uint a < 274877906944)%Z⌝ ∗
      ⌜addr_is_ram (pa_of ppn a)⌝ ∗
      ⌜pa_of ppn a = a⌝ ∗
      pointsto (L:=Arch.pa) (V:=bv 8) (pa_of ppn a) dq b ∗
      (pointsto (L:=Arch.pa) (V:=bv 8) (pa_of ppn a) dq b -∗ a ↦ₘ{dq} b).
  Proof.
    rewrite /mem_pointsto. iIntros "H". iDestruct "H" as (ppn) "(#Hk & %Hc & %Hd & %Hi & Hp)".
    iExists ppn. iFrame "Hk Hp".
    iSplit; [iPureIntro; exact Hc|]. iSplit; [iPureIntro; exact Hd|].
    iSplit; [iPureIntro; exact Hi|].
    iIntros "Hp". iExists ppn. by iFrame "Hk Hp".
  Qed.

  (* the canonicality conjunct (positive Sv39 half): pins [a ↔ (vpn,off)]. *)
  Lemma mem_canonical a dq b : a ↦ₘ{dq} b -∗ ⌜(uint a < 274877906944)%Z⌝.
  Proof.
    rewrite /mem_pointsto. iIntros "H". iDestruct "H" as (ppn) "(_ & %Hc & _ & _ & _)".
    iPureIntro; exact Hc.
  Qed.

  (* PA-SIDE region fact: the byte's PHYSICAL address is in RAM (the
     claim ppn identifies the page).  Identity consumers recover the va-side
     fact via [pa_of_id] (KptPt). *)
  Lemma mem_ram a dq b :
    a ↦ₘ{dq} b -∗ ∃ ppn : mword 44,
      kmap_at (svpn_of a) ppn KP_rw ∗ ⌜addr_is_ram (pa_of ppn a)⌝.
  Proof.
    rewrite /mem_pointsto. iIntros "H". iDestruct "H" as (ppn) "(#Hk & _ & %Hd & _ & _)".
    iExists ppn. iFrame "Hk". iPureIntro; exact Hd.
  Qed.

  (* reading a memory byte agrees with the byte heap AT ITS PHYSICAL address. *)
  Lemma mem_valid (mm : gmap Arch.pa (bv 8)) a dq b :
    gen_heap_interp (hG:=riscv_memGS) mm -∗ a ↦ₘ{dq} b -∗ ∃ ppn : mword 44,
      kmap_at (svpn_of a) ppn KP_rw ∗ ⌜addr_is_ram (pa_of ppn a)⌝ ∗
      ⌜mm !! (pa_of ppn a) = Some b⌝.
  Proof.
    rewrite /mem_pointsto. iIntros "Hm H". iDestruct "H" as (ppn) "(#Hk & _ & %Hd & _ & Hp)".
    iDestruct (gen_heap_valid with "Hm Hp") as %Hlk.
    iExists ppn. iFrame "Hk". iPureIntro. split; [exact Hd | exact Hlk].
  Qed.

  (* a discarded (read-only) memory byte is persistent — hence FREELY duplicable.
     This is what makes [kernel_text] (built from [↦ₓ□] code bytes) duplicable. *)
  Global Instance mem_pointsto_discarded_persistent a b :
    Persistent (a ↦ₘ□ b).
  Proof. rewrite /mem_pointsto. apply _. Qed.

  (* discard the fraction: turn any memory byte into the persistent read-only one. *)
  Lemma mem_pointsto_persist a dq b : a ↦ₘ{dq} b ==∗ a ↦ₘ□ b.
  Proof.
    rewrite /mem_pointsto. iIntros "H". iDestruct "H" as (ppn) "(#Hk & %Hc & %Hd & %Hi & Hp)".
    iMod (pointsto_persist with "Hp") as "Hp". iModIntro. iExists ppn.
    iFrame "Hk Hp". iPureIntro. split; [exact Hc | split; [exact Hd | exact Hi]].
  Qed.

  (* KEEP-UNREFERENCED: public bridge API (kept though currently unreferenced).
     a persistent (discarded) byte can be handed out repeatedly. *)
  Lemma mem_pointsto_dup a b : a ↦ₘ□ b -∗ a ↦ₘ□ b ∗ a ↦ₘ□ b.
  Proof. iIntros "#H". by iSplitR. Qed.

  (* ---- the CODE points-to bridge (rwx-kmap; mirrors the ↦ₘ suite) ---- *)

  Lemma text_pointsto_acc a dq b :
    a ↦ₓ{dq} b -∗ ∃ ppn : mword 44,
      kmap_at (svpn_of a) ppn KP_rx ∗
      ⌜(uint a < 274877906944)%Z⌝ ∗
      ⌜addr_is_text (pa_of ppn a)⌝ ∗
      ⌜pa_of ppn a = a⌝ ∗
      pointsto (L:=Arch.pa) (V:=bv 8) (pa_of ppn a) dq b ∗
      (pointsto (L:=Arch.pa) (V:=bv 8) (pa_of ppn a) dq b -∗ a ↦ₓ{dq} b).
  Proof.
    rewrite /text_pointsto. iIntros "H". iDestruct "H" as (ppn) "(#Hk & %Hc & %Hd & %Hi & Hp)".
    iExists ppn. iFrame "Hk Hp".
    iSplit; [iPureIntro; exact Hc|]. iSplit; [iPureIntro; exact Hd|].
    iSplit; [iPureIntro; exact Hi|].
    iIntros "Hp". iExists ppn. by iFrame "Hk Hp".
  Qed.

  Lemma text_canonical a dq b : a ↦ₓ{dq} b -∗ ⌜(uint a < 274877906944)%Z⌝.
  Proof.
    rewrite /text_pointsto. iIntros "H". iDestruct "H" as (ppn) "(_ & %Hc & _ & _ & _)".
    iPureIntro; exact Hc.
  Qed.

  (* PA-SIDE: the byte's PHYSICAL address is kernel TEXT ... *)
  Lemma code_text a dq b :
    a ↦ₓ{dq} b -∗ ∃ ppn : mword 44,
      kmap_at (svpn_of a) ppn KP_rx ∗ ⌜addr_is_text (pa_of ppn a)⌝ ∗
      ⌜pa_of ppn a = a⌝.
  Proof.
    rewrite /text_pointsto. iIntros "H". iDestruct "H" as (ppn) "(#Hk & _ & %Hd & %Hi & _)".
    iExists ppn. iFrame "Hk". iPureIntro; split; [exact Hd | exact Hi].
  Qed.

  (* ... and hence real RAM (what the M-mode no-perm-check fetch path and
     the PMP/MMIO geometry facts consume, at the physical address). *)
  Lemma code_ram a dq b :
    a ↦ₓ{dq} b -∗ ∃ ppn : mword 44,
      kmap_at (svpn_of a) ppn KP_rx ∗ ⌜addr_is_ram (pa_of ppn a)⌝.
  Proof.
    rewrite /text_pointsto. iIntros "H". iDestruct "H" as (ppn) "(#Hk & _ & %Hd & %Hi & _)".
    iExists ppn. iFrame "Hk". iPureIntro; exact (addr_is_text_ram _ Hd).
  Qed.

  Lemma text_valid (mm : gmap Arch.pa (bv 8)) a dq b :
    gen_heap_interp (hG:=riscv_memGS) mm -∗ a ↦ₓ{dq} b -∗ ∃ ppn : mword 44,
      kmap_at (svpn_of a) ppn KP_rx ∗ ⌜addr_is_text (pa_of ppn a)⌝ ∗
      ⌜mm !! (pa_of ppn a) = Some b⌝.
  Proof.
    rewrite /text_pointsto. iIntros "Hm H". iDestruct "H" as (ppn) "(#Hk & _ & %Hd & _ & Hp)".
    iDestruct (gen_heap_valid with "Hm Hp") as %Hlk.
    iExists ppn. iFrame "Hk". iPureIntro. split; [exact Hd | exact Hlk].
  Qed.

  Global Instance text_pointsto_discarded_persistent a b :
    Persistent (a ↦ₓ□ b).
  Proof. rewrite /text_pointsto. apply _. Qed.

  (* discard the fraction: turn any code byte into the persistent read-only
     one (adequacy init persists the whole sub-etext image this way). *)
  Lemma text_pointsto_persist a dq b : a ↦ₓ{dq} b ==∗ a ↦ₓ□ b.
  Proof.
    rewrite /text_pointsto. iIntros "H". iDestruct "H" as (ppn) "(#Hk & %Hc & %Hd & %Hi & Hp)".
    iMod (pointsto_persist with "Hp") as "Hp". iModIntro. iExists ppn.
    iFrame "Hk Hp". iPureIntro. split; [exact Hc | split; [exact Hd | exact Hi]].
  Qed.

  (* ---- the PHYSICAL points-to bridge (the OLD pa-era [mem_*] bodies) ---- *)

  Lemma phys_valid (mm : gmap Arch.pa (bv 8)) a dq b :
    gen_heap_interp (hG:=riscv_memGS) mm -∗ a ↦ₚ{dq} b -∗ ⌜mm !! a = Some b⌝.
  Proof.
    iIntros "Hm [Ha _]". by iDestruct (gen_heap_valid with "Hm Ha") as %?.
  Qed.

  Lemma phys_ram a dq b : a ↦ₚ{dq} b -∗ ⌜addr_is_ram a⌝.
  Proof. by iIntros "[_ %H]". Qed.

  (* the PHYSICAL word cell (a PT slot post-flip) sits in RAM -- trivial from
     [phys_ram] at byte 0.  Beside [phys_word_pointsto]'s suite; consumed by the
     walk's "slot address is nonzero because it is RAM" argument. *)
  Lemma phys_word_pointsto_ram a dq w : a ↦ₚ₈{dq} w ⊢ ⌜addr_is_ram a⌝.
  Proof.
    iIntros "Hw". iDestruct (phys_word_pointsto_bytes with "Hw") as "Hbs".
    iDestruct (big_sepL_lookup _ _ 0%nat 0%nat with "Hbs") as "Hb0".
    { rewrite lookup_seq_lt; [reflexivity | lia]. }
    iDestruct (phys_ram with "Hb0") as %Hram0.
    (* [pa_add a 0 = a] (RiscvExtras' [pa_add_0]/[avi0] cannot be imported here
       -- it depends on RiscvPtsto -- so its proof is inlined). *)
    assert (Hpa0 : pa_add a 0 = a).
    { unfold pa_add. change (Z.of_nat 0) with 0%Z.
      unfold add_vec_int, add_vec, Operators_mwords.word_binop,
             Operators_mwords.with_word', SailStdpp.Values.with_word,
             SailStdpp.Values.mword_of_int,
             MachineWord.MachineWord.add, MachineWord.MachineWord.Z_to_word.
      apply bv_eq. rewrite bv_add_unsigned Z_to_bv_unsigned.
      rewrite bv_wrap_0 Z.add_0_r. apply bv_wrap_small. apply bv_unsigned_in_range. }
    rewrite Hpa0 in Hram0. iPureIntro. exact Hram0.
  Qed.

  (* ...AND ITS LAST BYTE.  The cell owns all eight bytes, so this is the
     same read at index 7 -- and it is what the PMA RAM class needs: the
     platform's DRAM region ends at PHYSTOP, so an 8-byte access is inside it
     only if its END is ([RiscvExtras.pma_access_ram]). *)
  Lemma phys_word_pointsto_ram7 a dq w : a ↦ₚ₈{dq} w ⊢ ⌜addr_is_ram (pa_add a 7)⌝.
  Proof.
    iIntros "Hw". iDestruct (phys_word_pointsto_bytes with "Hw") as "Hbs".
    iDestruct (big_sepL_lookup _ _ 7%nat 7%nat with "Hbs") as "Hb7".
    { rewrite lookup_seq_lt; [reflexivity | lia]. }
    iDestruct (phys_ram with "Hb7") as %Hram7. iPureIntro. exact Hram7.
  Qed.

  Global Instance phys_pointsto_discarded_persistent a b : Persistent (a ↦ₚ□ b).
  Proof. rewrite /phys_pointsto. apply _. Qed.

  Lemma phys_pointsto_persist a dq b : a ↦ₚ{dq} b ==∗ a ↦ₚ□ b.
  Proof.
    iIntros "[Ha %Hr]". iMod (pointsto_persist with "Ha") as "Ha".
    iModIntro. by iFrame.
  Qed.

  Lemma phys_pointsto_dup a b : a ↦ₚ□ b -∗ a ↦ₚ□ b ∗ a ↦ₚ□ b.
  Proof. iIntros "#H". by iSplitR. Qed.

  Lemma phys_update (mm : _) (a : Arch.pa) (b b' : bv 8) :
    gen_heap_interp (hG:=riscv_memGS) mm -∗ a ↦ₚ{DfracOwn 1} b ==∗
      gen_heap_interp (hG:=riscv_memGS) (<[a := b']> mm) ∗ a ↦ₚ{DfracOwn 1} b'.
  Proof.
    iIntros "Hm [Ha %Hr]". iMod (gen_heap_update with "Hm Ha") as "[Hm Ha]".
    iModIntro. iFrame "Hm Ha". iPureIntro. exact Hr.
  Qed.

  (* ---- the agreement CORE of the tier bridge (uniform-claims PHYSICAL
     TIER): given a claim for [pa]'s vpn, the VA-based [↦ₘ]'s existential ppn
     is PINNED to that claim's ppn -- so its byte sits at [pa_of ppn0 pa].
     The [pa_of ppn0 pa = pa] step (identity, via [pa_of_id] with ppn0 =
     [kpt_leaf_ppn]) is done by the KptPt/KMap assembly lemmas built on
     this.  Only [kmap_at_agree] is needed here, so it stays in RiscvPtsto. *)
  Lemma mem_pointsto_pin (pa : mword 64) dq b (ppn0 : mword 44) :
    kmap_at (svpn_of pa) ppn0 KP_rw -∗ pa ↦ₘ{dq} b -∗
      ⌜(uint pa < 274877906944)%Z⌝ ∗ ⌜addr_is_ram (pa_of ppn0 pa)⌝ ∗
      ⌜pa_of ppn0 pa = pa⌝ ∗
      pointsto (L:=Arch.pa) (V:=bv 8) (pa_of ppn0 pa) dq b ∗
      (pointsto (L:=Arch.pa) (V:=bv 8) (pa_of ppn0 pa) dq b -∗ pa ↦ₘ{dq} b).
  Proof.
    iIntros "#Hk0 H".
    iDestruct (mem_pointsto_acc with "H") as (ppn) "(#Hk & %Hc & %Hd & %Hi & Hp & Hcl)".
    iDestruct (kmap_at_agree with "Hk0 Hk") as %[<- _].
    iFrame "Hp Hcl". iPureIntro. split; [exact Hc | split; [exact Hd | exact Hi]].
  Qed.

  (* CLAIM-KEYED VA-tier introduction: a physical byte sitting at
     [pa_of ppn va] -- the pa the claim [kmap_at (svpn_of va) ppn KP_rw] takes
     [va] to -- IS the [↦ₘ] byte at [va].  This is the primary form of the
     [↦ₚ -> ↦ₘ] direction; the claim carries the translation and the caller
     supplies the RAM/canonicality facts about the physical target plus the
     IDENTITY [pa_of ppn va = va] that [↦ₘ] carries (see its header: a
     non-identity [↦ₘ] would be unsound under a Bare hart). *)
  Lemma phys_to_mem_map (va : mword 64) (ppn : mword 44) dq b :
    addr_is_ram (pa_of ppn va) -> (uint va < 274877906944)%Z ->
    pa_of ppn va = va ->
    kmap_at (svpn_of va) ppn KP_rw -∗ (pa_of ppn va) ↦ₚ{dq} b -∗ va ↦ₘ{dq} b.
  Proof.
    intros Hram Hcan Hid. iIntros "#Hk [Hp _]".
    rewrite /mem_pointsto. iExists ppn. iFrame "Hk Hp".
    iPureIntro. split; [exact Hcan | split; [exact Hram | exact Hid]].
  Qed.

  (* Claim-keyed byte conversions ↦ₚ ⇄ ↦ₘ for an IDENTITY-mapped kdata va
     ([pa_of ppn pa = pa]): the [kmap_at] supplies the mapping, the caller the
     pure kdata/canonical facts.  These are what let a physical PT-slot cell
     ([↦ₚ₈], owned by [ptree_own]) become a VA-tier [↦₈] for a software walk's
     S-mode load, carrying NOTHING but the node's own claim
     ([pt_node_claim] = this [kmap_at] + [node_kdata]).  [phys_to_mem_claim] is
     now a RESTATEMENT of the general [phys_to_mem_map] above (the identity
     premise [pa_of ppn pa = pa] specializes [pa_of ppn pa] to [pa]). *)
  Lemma phys_to_mem_claim (pa : mword 64) (ppn : mword 44) dq b :
    pa_of ppn pa = pa -> addr_is_ram pa -> (uint pa < 274877906944)%Z ->
    kmap_at (svpn_of pa) ppn KP_rw -∗ pa ↦ₚ{dq} b -∗ pa ↦ₘ{dq} b.
  Proof.
    intros Hid Hkd Hcan. iIntros "#Hk Hp".
    iApply (phys_to_mem_map pa ppn dq b with "Hk [Hp]").
    { rewrite Hid. exact Hkd. }
    { exact Hcan. }
    { exact Hid. }
    { rewrite Hid. iExact "Hp". }
  Qed.

  Lemma mem_to_phys_claim (pa : mword 64) (ppn : mword 44) dq b :
    pa_of ppn pa = pa ->
    kmap_at (svpn_of pa) ppn KP_rw -∗ pa ↦ₘ{dq} b -∗ pa ↦ₚ{dq} b.
  Proof.
    intros Hid. iIntros "#Hk H".
    iDestruct (mem_pointsto_pin pa dq b ppn with "Hk H") as "(%Hc & %Hd & _ & Hp & _)".
    rewrite Hid in Hd. iEval (rewrite Hid) in "Hp".
    rewrite /phys_pointsto. iFrame "Hp". iPureIntro. exact Hd.
  Qed.

  Lemma text_pointsto_pin (pa : mword 64) dq b (ppn0 : mword 44) :
    kmap_at (svpn_of pa) ppn0 KP_rx -∗ pa ↦ₓ{dq} b -∗
      ⌜(uint pa < 274877906944)%Z⌝ ∗ ⌜addr_is_text (pa_of ppn0 pa)⌝ ∗
      ⌜pa_of ppn0 pa = pa⌝ ∗
      pointsto (L:=Arch.pa) (V:=bv 8) (pa_of ppn0 pa) dq b ∗
      (pointsto (L:=Arch.pa) (V:=bv 8) (pa_of ppn0 pa) dq b -∗ pa ↦ₓ{dq} b).
  Proof.
    iIntros "#Hk0 H".
    iDestruct (text_pointsto_acc with "H") as (ppn) "(#Hk & %Hc & %Hd & %Hi & Hp & Hcl)".
    iDestruct (kmap_at_agree with "Hk0 Hk") as %[<- _].
    iFrame "Hp Hcl". iPureIntro. split; [exact Hc | split; [exact Hd | exact Hi]].
  Qed.

End Bridge.

(* ---------------------------------------------------------------------- *)
(* Persisting a MULTI-byte cell: [mem_pointsto_persist] lifted over the byte
   windows of [↦₈] / [↦₄] / [↦ₛ].  Discarding the fraction turns a cell
   read-only forever and hence duplicable -- how a freshly-initialised
   immutable structure (a lock's name field, a string) becomes a persistent
   resource that no longer has to be threaded through every WP.              *)
(* ---------------------------------------------------------------------- *)
Section pointsto_persist.
  Context `{!riscvGS Σ}.

  Global Instance word_pointsto_discarded_persistent a w : Persistent (a ↦₈□ w).
  Proof. rewrite /word_pointsto. apply _. Qed.
  Global Instance word4_pointsto_discarded_persistent a w : Persistent (a ↦₄□ w).
  Proof. rewrite /word4_pointsto. apply _. Qed.

  Lemma word_pointsto_persist a dq w : a ↦₈{dq} w ==∗ a ↦₈□ w.
  Proof.
    iIntros "[%Hal Hbs]".
    iAssert (|==> [∗ list] j ∈ seq 0 8,
               (pa_add a j) ↦ₘ□ nth_byte w j)%I with "[Hbs]" as ">Hbs".
    { iApply big_sepL_bupd. iApply (big_sepL_mono with "Hbs").
      iIntros (k j _) "H". by iApply mem_pointsto_persist. }
    iModIntro. by iFrame.
  Qed.

  Lemma word4_pointsto_persist a dq w : a ↦₄{dq} w ==∗ a ↦₄□ w.
  Proof.
    iIntros "[%Hal Hbs]".
    iAssert (|==> [∗ list] j ∈ seq 0 4,
               (pa_add a j) ↦ₘ□ nth_byte w j)%I with "[Hbs]" as ">Hbs".
    { iApply big_sepL_bupd. iApply (big_sepL_mono with "Hbs").
      iIntros (k j _) "H". by iApply mem_pointsto_persist. }
    iModIntro. by iFrame.
  Qed.

  Lemma string_pointsto_persist a dq s : a ↦ₛ{dq} s ==∗ a ↦ₛ□ s.
  Proof.
    iIntros "Hs". iApply big_sepL_bupd. iApply (big_sepL_mono with "Hs").
    iIntros (k b _) "H". by iApply mem_pointsto_persist.
  Qed.

  Global Instance phys_word_pointsto_discarded_persistent a w : Persistent (a ↦ₚ₈□ w).
  Proof. rewrite /phys_word_pointsto. apply _. Qed.

  Lemma phys_word_pointsto_persist a dq w : a ↦ₚ₈{dq} w ==∗ a ↦ₚ₈□ w.
  Proof.
    iIntros "[%Hal Hbs]".
    iAssert (|==> [∗ list] j ∈ seq 0 8,
               (pa_add a j) ↦ₚ□ nth_byte w j)%I with "[Hbs]" as ">Hbs".
    { iApply big_sepL_bupd. iApply (big_sepL_mono with "Hbs").
      iIntros (k j _) "H". by iApply phys_pointsto_persist. }
    iModIntro. by iFrame.
  Qed.
End pointsto_persist.

(* Seal [mem_pointsto] for typeclass (Frame) resolution: without this, [iFrame]
   over a large memory region unfolds every [a ↦ₘ v] into its [pointsto ∗ ⌜..⌝]
   conjunction and recursively re-searches the [Frame] instance per byte.  Making
   it typeclass-opaque keeps each [a ↦ₘ v] an atomic frameable unit (~37% off the
   big region [iFrame]s).  Placed AFTER [End Bridge] so the bridge lemmas above,
   which destruct the raw conjunction, still typecheck.  [Typeclasses Opaque]
   (not [Opaque]) leaves [rewrite /mem_pointsto] / [unfold] working. *)
Typeclasses Opaque mem_pointsto.
Typeclasses Opaque text_pointsto.
Typeclasses Opaque phys_pointsto.

(* ... and re-supply the TIMELESS instances the seals hide.  A page-table
   node's ownership must be timeless for the SHARED kernel table to live in
   an Iris [inv] (KptShare.v): opening the invariant yields the body under a
   [▷], and the Svadu A/D write-back needs the slot NOW. *)
Global Instance text_pointsto_timeless `{!riscvGS Σ} a dq b :
  Timeless (text_pointsto a dq b).
Proof. rewrite /text_pointsto. apply _. Qed.
Global Instance phys_pointsto_timeless `{!riscvGS Σ} a dq b :
  Timeless (phys_pointsto a dq b).
Proof. rewrite /phys_pointsto. apply _. Qed.
Global Instance phys_word_pointsto_timeless `{!riscvGS Σ} a dq w :
  Timeless (phys_word_pointsto a dq w).
Proof. rewrite /phys_word_pointsto. apply _. Qed.
