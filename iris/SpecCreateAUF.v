(* SpecCreateAUF.v -- create's ATOMIC-UPDATE contract AT [T_FILE]: the twin
   of [SpecCreateAU] for the type sys_open's O_CREATE arm asks for.

   Worklist: claude-notes/projects/fs-syscall-specs.md, lane W (the T_FILE
   create-AU carry).  A PARALLEL FORM beside [SpecCreate.wp_create_sconf]
   and beside [SpecCreateAU.wp_create_au] -- R10: neither landed contract
   moves, and neither does [SpecSysOpenAU].

   ==== WHY A SECOND AU CONTRACT, AND NOT A GENERAL-[ty] ONE ============

   [SpecCreateAU] is T_DEVICE-PINNED BY CONSTRUCTION and its header records
   what the pin buys: the [beq s4,1] at +0xc8 never takes the directory arm
   AND the [bne s2,2] at +0x5a always leaves the found half through ARM
   F-BAD, so mknod's contract can say [ok = true -> made = true].  sys_open
   needs the OTHER half of that test.  xv6's open(O_CREATE) on an existing
   FILE OPENS IT; create's ARM F-OK is exactly that behaviour, and it is
   reachable only at [ty = T_FILE].

   So this file pins [ty = T_FILE] instead, and the consequences are:

     - THE MKDIR ARM IS STILL REFUTED.  [T_FILE <> T_DIR], so the [beq
       s4,a4] at +0xca cannot be taken and the whole dot-writing sub-branch
       ([cr_mkdir_body], [cr_fail_mkdir_*]) stays out of the prover, as it
       is out of [ProofCreateAU].  This is why the T_FILE twin is a twin
       and not a general-[ty] form: a general form would owe the directory
       arm's TWO extra abstract obligations (the parent's nlink bump
       through [SpecSysMknodAU.acre_bump], and the "." / ".." content that
       makes the child's row an [ADir]), and no consumer on this campaign's
       list wants them.  [SpecSysMknodAU]'s [delta_create] is already
       type-parameterized, so nothing here is in a later general form's
       way; what that form still owes is the four thousand lines of mkdir
       walk, not a statement change.

     - THE FOUND ARM COMES BACK.  [ok = true] no longer forces [made], so
       the success payout is keyed on it: ARM C-OK at the record
       [SpecCreate.create_made T_FILE major minor], ARM F-OK at
       [SpecCreate]'s own F-OK facts ([di_type dn] is [T_FILE] or
       [T_DEVICE] -- the two the [bltu] at +0x6c admits).

   ==== THE TWO INSTANTS, AND WHICH ARM SPENDS WHICH ====================

   Both commits come in; exactly one fires on every arm that returns an
   inode, and the OTHER is refunded:

     ARM C-OK   the FRESH create.  [acre_commit_at] fired at the entry
                write ([FsAbsCreateFire.caf_acre_fire_file], the
                non-directory-child fire at [AFile []]); the exists commit
                comes back UNFIRED.  [made = true].
     ARM F-OK   the name WAS there and its node is openable.  The exists
                observation fired at the found instant (the parent's own
                [top_frag], [FsAbsMknodFire.mkf_dlookup_fire]) and NO DELTA
                FIRED -- the abstract state is unchanged, which is the
                whole point: xv6 opens the existing file.  The create
                commit comes back UNFIRED.  [made = false].

   The failure fold is [SpecCreateAU.cau_fail]'s at the file child, arm for
   arm (the header there enumerates them); ARM F-BAD is the found-a-
   DIRECTORY exit and reports the exists observation, as it does there.

   ==== WHAT THE CONSUMER TAKES =========================================

   [SpecSysOpenAU.open_post_ok_create]'s two disjuncts are [cauf_ok]'s two
   arms verbatim modulo the descriptor: FRESH wants [cre_pre av d nm ents
   nl i (AFile [])] with the create receipt and the exists commit back,
   EXISTS-OPENS wants the parent's row, the entry, the exists receipt and
   the create commit back.  [cauf_ok_fresh] / [cauf_ok_exists] below are
   the two projections, stated so that the consumer's prover destructs
   [made] once and frames.  The inum bound the consumer's FRESH disjunct
   also asks for is create's own post fact, not the carry's.

   BINDERS: [SpecCreate]'s section list verbatim -- NO standalone
   [icacheG]/[icfg] (SpecCreate's header records why that is load-bearing
   rather than tidy). *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list functions bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import auth gmap frac dfrac.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap ghost_map.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes.
Require Import RiscvLang RiscvPtsto.
Require Import InstrBytes.
Require Import RegFile.
Require Import RiscvExtras.
Require Import CalleeSaved KernelText.
Require Import IntrDefs.
Require Import WpNext.
Require Import WpLock.
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
Require Import BitmapInv.
Require Import KernelDataInv.
Require Import SpecPrintk.
Require Import ByteBuf.
Require Import DinodeEnc.
Require Import DirentEnc.
Require Import PathElems.       (* [path_elems], [SLASH], [bview]           *)
Require Import FsTree.          (* [fname]                                  *)
Require Import InodeInv.        (* [ROOTINO] : mword 32                     *)
Require Import InodeRegion.
Require Import IrefSlots.
Require Import IcacheRef.
Require Import IcacheInv.
Require Import IcacheEscrow.
Require Import KvmSpec.
Require Import FileInvDefs.
Require Import ProcInv.
Require Import SpecIput.
Require Import SpecCreate.      (* the landed contract this parallels       *)
Require Import FsBytesGamma.    (* [fs_gamma_L]: the live Γ                 *)
Require Import SpecSysMknodAU.  (* [cre_pre], [mknod_parent_elems]          *)
Require Import FsAbsEra.      (* [ep_start]: the DEFERRED start           *)
Require Import FsAbsMknodFire.  (* the authority-shaped commits             *)
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import ProcAvail.
Require Import Xv6G.
Require Import FsCfg.
Require Import FsAbsInv.        (* [fsabsN]/[fsabsE]: the commit mask *)
Require Import FsAbsDefs.           (* LAST (FsAbs's own rule)                  *)
Import Defs.
Require Import TsoCtx.

Section CreateAUFSpec.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ,
            !fileG Σ, !irefslotG Σ, !pavG Σ}.

  (* ------------------------------------------------------------------ *)
  (*  THE SUCCESS PAYOUT (ARMS C-OK AND F-OK), KEYED ON [made]           *)
  (* ------------------------------------------------------------------ *)

  (* the cursor at the parent index and the name tie are SHARED by the two
     arms -- both ran nameiparent, and both are at the path's last element.
     What differs is which of the two commits fired. *)
  Definition cauf_ok Γ (P : nat -> Z -> iProp Σ)
      (Φok Φex : aview -> Z -> fname -> Z -> iProp Σ)
      (pl : list (bv 8)) (made : bool) (i : Z) : iProp Σ :=
    (∃ (d : Z) (nm : fname),
       ⌜ list_basics.last (path_elems pl) = Some nm ⌝ ∗
       P (length (mknod_parent_elems pl)) d ∗
       (if made
        then (* ARM C-OK: the fused delta fired at the entry write, at the
                child [AFile []]; the exists commit is refunded UNFIRED. *)
          ∃ (av : aview) (ents : gmap fname Z) (nl : nat),
            ⌜ cre_pre av d nm ents nl i (AFile []) ⌝ ∗
            dlookup_commit_at Γ fsabsE Φex ∗
            Φok av d nm i
        else (* ARM F-OK: the exists observation fired at the found
                instant and NOTHING MOVED, so the create commit is
                refunded UNFIRED. *)
          ∃ (av : aview) (ents : gmap fname Z) (nl : nat),
            ⌜ av !! d = Some (MkAnode (ADir ents) nl) ⌝ ∗
            ⌜ ents !! nm = Some i ⌝ ∗
            acre_commit_at Γ fsabsE (AFile []) Φok ∗
            Φex av d nm i))%I.

  (* ------------------------------------------------------------------ *)
  (*  THE FAILURE FOLD (ARMS N / G / F-BAD / A-FAIL / FAIL)              *)
  (* ------------------------------------------------------------------ *)

  (* [SpecCreateAU.cau_fail] at the file child, arm for arm. *)
  Definition cauf_fail Γ (gfs : fs_names)
      (P Pmiss : nat -> Z -> iProp Σ)
      (Φok Φex : aview -> Z -> fname -> Z -> iProp Σ)
      (pl : list (bv 8)) : iProp Σ :=
    ((mknod_walk_dead_era gfs P Pmiss pl
        ∗ acre_commit_at Γ fsabsE (AFile []) Φok
        ∗ dlookup_commit_at Γ fsabsE Φex)
     ∨ (∃ d : Z,
          P (length (mknod_parent_elems pl)) d
          ∗ acre_commit_at Γ fsabsE (AFile []) Φok
          ∗ ((∃ (av : aview) (i : Z) (nm : fname) (ents : gmap fname Z)
                (nl : nat),
                ⌜ list_basics.last (path_elems pl) = Some nm ⌝ ∗
                ⌜ av !! d = Some (MkAnode (ADir ents) nl) ⌝ ∗
                ⌜ ents !! nm = Some i ⌝ ∗
                Φex av d nm i)
             ∨ dlookup_commit_at Γ fsabsE Φex)))%I.

  (* ------------------------------------------------------------------ *)
  (*  THE TWO PROJECTIONS THE CONSUMER'S PROVER USES                     *)
  (* ------------------------------------------------------------------ *)

  (* [SpecSysOpenAU.open_post_ok_create]'s FRESH disjunct, minus the
     descriptor bundle and the inum bound. *)
  Lemma cauf_ok_fresh Γ P Φok Φex pl (i : Z) :
    cauf_ok Γ P Φok Φex pl true i ⊢
      ∃ (d : Z) (nm : fname) (av : aview) (ents : gmap fname Z) (nl : nat),
        ⌜ list_basics.last (path_elems pl) = Some nm ⌝ ∗
        ⌜ cre_pre av d nm ents nl i (AFile []) ⌝ ∗
        P (length (mknod_parent_elems pl)) d ∗
        Φok av d nm i ∗
        dlookup_commit_at Γ fsabsE Φex.
  Proof.
    rewrite /cauf_ok. iIntros "H".
    iDestruct "H" as (d nm) "(%Hlast & HP & Harm)".
    iDestruct "Harm" as (av ents nl) "(%Hpre & Hdl & HF)".
    iExists d, nm, av, ents, nl.
    iSplitR; [by iPureIntro |]. iSplitR; [by iPureIntro |].
    iFrame "HP HF Hdl".
  Qed.

  (* ...and the EXISTS-OPENS disjunct. *)
  Lemma cauf_ok_exists Γ P Φok Φex pl (i : Z) :
    cauf_ok Γ P Φok Φex pl false i ⊢
      ∃ (d : Z) (nm : fname) (av : aview) (ents : gmap fname Z) (nl : nat),
        ⌜ list_basics.last (path_elems pl) = Some nm ⌝ ∗
        ⌜ av !! d = Some (MkAnode (ADir ents) nl) ⌝ ∗
        ⌜ ents !! nm = Some i ⌝ ∗
        P (length (mknod_parent_elems pl)) d ∗
        Φex av d nm i ∗
        acre_commit_at Γ fsabsE (AFile []) Φok.
  Proof.
    rewrite /cauf_ok. iIntros "H".
    iDestruct "H" as (d nm) "(%Hlast & HP & Harm)".
    iDestruct "Harm" as (av ents nl) "(%Hrow & %Hent & Hac & HF)".
    iExists d, nm, av, ents, nl.
    iSplitR; [by iPureIntro |]. iSplitR; [by iPureIntro |].
    iSplitR; [by iPureIntro |].
    iFrame "HP HF Hac".
  Qed.

End CreateAUFSpec.

(* big-op bodies behind definitions: seal them, or an [iFrame] near a
   consumer resolves instances through the whole hop family
   (durable-notes; optimization.md, "a big-op body is the predictor"). *)
Global Typeclasses Opaque cauf_ok cauf_fail.

Definition wp_create_auf_body
    `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
      !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
    (γs : list gname) (j : nat) (γl : gname)          (* the running process *)
  (* disk fabric + lock  *)
    (pd pav pu : mword 64)
 (γf : gname)           (* kalloc, ftable, printk *)
    (plen : nat) (pfun : nat -> bv 8)                 (* the PATH buffer     *)
    (ty major minor : mword 16)                       (* a1, a2, a3          *)
    (U : ustate)                                    (* the running process *)
    (u : nat) (Sb : gset Z)                           (* THE OP-WIDE LEDGER  *)
    (ns : nat)                                        (* the iref ledger     *)
    (pidv : mword 32) (dqb dqs dqbs dqn : dfrac)
    (m : regfile) (K : nat) (eb : bool)
    (b : bool) (lks : gset string)
    (* ---- THE AU SIDE ---- *)
    (P Pmiss : nat -> Z -> iProp Σ)
    (Φok Φex : aview -> Z -> fname -> Z -> iProp Σ) :=
  let pcE : mword 64 := mword_of_int KernelSyms.create in
  let pj := proc_addr j in
  let pv := m !!! Regidx (mword_of_int 10 : mword 5) in   (* a0 = path *)
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  let pl := bview plen pfun in
  let Γfs := fs_gamma_L fsc_fs in
  (* NO [ma] / [mi] LETS: at [T_FILE] the child's abstract row is [AFile []]
     whatever the two device arguments hold, so the commit is not indexed by
     them the way [SpecCreateAU]'s is.  They stay in the register premises
     because create still stores them. *)
  (K_create <= K)%nat ->
  icfg_dev = ROOTDEV ->
  (0 < icfg_nib)%nat ->
  log_geom_ok fsc_cov fsc_logst ->
  0 < fsc_size <= BPB ->
  0 <= fsc_bmapstart ->
  fsc_bmapstart ∈ fsc_cov ->
  ~ (fsc_bmapstart ∈ log_region_set fsc_logst) ->
  0 <= icfg_ist ->
  cov_below fsc_cov fsc_size ->
  bitmap_geom_ok fsc_cov fsc_logst fsc_bmapstart fsc_size ->
  InodeInv.ireg_blocks_ok icfg_ist icfg_nib fsc_cov fsc_logst ->
  (* ---- namex's path buffer ---- *)
  bb_cstr pfun plen ->
  (Z.of_nat plen < 2 ^ 31)%Z ->
  (* ---- ialloc's three geometry premises ---- *)
  1 < fsc_ninodes ->
  fsc_ninodes <= 16 * Z.of_nat icfg_nib ->
  fsc_ninodes < 2 ^ 31 ->
  16 * Z.of_nat icfg_nib <= 2 ^ 16 ->
  (* ---- THE TYPE IS FIXED AT [T_FILE] (see the header) ---- *)
  ty = T_FILE ->
  (* ---- ialloc's no-inodes arm calls printk, not panic ---- *)
  printk_gen_contract (kt := KT1) fsc_printk fsc_uart fsc_disk ->
  (* ---- THE TWO LEDGERS ---- *)
  (create_units <= u)%nat ->
  (create_slots <= ns)%nat ->
  (j < NPROC)%nat ->
  γs !! j = Some γl ->
  m !!! Regidx (mword_of_int 11 : mword 5) = (sign_extend' 64 ty : mword 64) ->
  m !!! Regidx (mword_of_int 12 : mword 5) = (sign_extend' 64 major : mword 64) ->
  m !!! Regidx (mword_of_int 13 : mword 5) = (sign_extend' 64 minor : mword 64) ->
  (* PARKING PREMISE (hart-generic scheduler protocol) *)
  eb = true ->
  sie_cap_gpr KT1 m K b pj -∗
  cpu_own 0 eb pj b lks -∗
  kernel_text -∗ pc_is pcE -∗
  kernel_data -∗
  printk_env fsc_printk fsc_uart fsc_disk -∗
  bio_ctx fsc_bio (fs_view fsc_fs fsc_disk icfg_dev fsc_cov) -∗
  log_ctx icfg_log fsc_bio fsc_fs fsc_cov fsc_logst icfg_dev -∗
  kalloc_env fsc_kalloc None -∗
  is_itable2 fsc_itlock fsc_ic fsc_fs fsc_ireg fsc_cov fsc_logst icfg_nib icfg_dev -∗
  itable_inv -∗
  ic_escrows fsc_ic fsc_fs fsc_ireg fsc_cov fsc_logst -∗
  ic_sleeplocks fsc_ic -∗
  ireg_inv fsc_ireg fsc_fs icfg_ist icfg_nib -∗
  ireg_open -∗
  sb_ninodes ↦₄{dqn} (mword_of_int fsc_ninodes : mword 32) -∗
  sb_inodestart ↦₄{dqs} (mword_of_int icfg_ist : mword 32) -∗
  sb_size ↦₄{dqbs} (mword_of_int fsc_size : mword 32) -∗
  sb_bmapstart ↦₄{dqb} (mword_of_int fsc_bmapstart : mword 32) -∗
  bitmap_inv fsc_fs fsc_bmapstart fsc_cov fsc_logst fsc_size -∗
  proc_priv γf pj pidv U -∗
  ([∗ list] i ∈ seq 0 (S plen), pa_add pv i ↦ₘ[KT1] pfun i) -∗
  procs_inv γs -∗
  dev_inv fsc_uart fsc_disk -∗
  disk_geom fsc_disk pd pav pu -∗
  is_lock fsc_dlock d_lock "virtio_disk"%string (disk_res_at fsc_disk pd pav pu) -∗
  bslots 3 -∗
  iref_slots ns -∗
  log_opS icfg_log u Sb -∗
  log_tx icfg_log -∗
  (* ---- THE AU SIDE: the trace and the two commits ----
     [FsAbsStart.ep_start] at create's own path buffer IS
     [FsAbsEraMknod.mknod_walk_pre_era] ([FsAbsNparMknod.np_start_of_mknod]),
     so the syscall hands its one-shot straight down and the START INUM is
     decided inside the walk.  The hop family is over the PARENT PREFIX,
     which is [SpecSysMknodAU.mknod_parent_elems] definitionally. *)
  ep_start fsc_fs (pv_cwi (us_V U)) P Pmiss pl -∗
  acre_commit_at Γfs fsabsE (AFile []) Φok -∗
  dlookup_commit_at Γfs fsabsE Φex -∗
  wp_next true pj (fun (CID : CpuId) =>
  ∀ (mf : regfile) (ok made : bool)
    (k : nat) (qi s : Qp) (g : gname) (inum : mword 32)
    (dn : dinode) (bm : blkmap)
    (u' : nat) (Sb' : gset Z) (ns' : nat),
      ⌜callee_saved m mf⌝ -∗
      sie_cap_gpr KT1 mf K b pj -∗
      cpu_own 0 eb pj b lks -∗
      pc_is ret_tgt -∗
      sb_ninodes ↦₄{dqn} (mword_of_int fsc_ninodes : mword 32) -∗
      sb_inodestart ↦₄{dqs} (mword_of_int icfg_ist : mword 32) -∗
      sb_size ↦₄{dqbs} (mword_of_int fsc_size : mword 32) -∗
      sb_bmapstart ↦₄{dqb} (mword_of_int fsc_bmapstart : mword 32) -∗
      proc_priv γf pj pidv U -∗
      ([∗ list] i ∈ seq 0 (S plen), pa_add pv i ↦ₘ[KT1] pfun i) -∗
      bslots 3 -∗
      ⌜if ok then (S ns' = ns)%nat else ns' = ns⌝ -∗
      iref_slots ns' -∗
      ⌜Sb ⊆ Sb' /\ (u' <= u)%nat /\ (ok = true -> (iput_units <= u')%nat)⌝ -∗
      log_opS icfg_log u' Sb' -∗
      (if ok
       then (* BOTH SUCCESS ARMS RETURN A LOCKED INODE, and [made] says
               which one ran -- [SpecCreate]'s own two success readings at
               [ty = T_FILE], where the C-OK record's [ty <> T_DIR] guard
               is discharged by the pin and the F-OK arm's [ty = T_FILE]
               IS the pin. *)
         ⌜mf !!! Regidx (mword_of_int 10 : mword 5) = ientry k
          /\ (k < NINODE)%nat
          /\ 0 < bv_unsigned inum < 16 * Z.of_nat icfg_nib
          /\ (if made
              then dn = create_made ty major minor
              else di_type dn = T_FILE \/ di_type dn = T_DEVICE)⌝ ∗
         create_locked pidv k qi s g inum dn bm ∗
         cauf_ok Γfs P Φok Φex pl made (bv_unsigned inum)
       else
         ⌜mf !!! Regidx (mword_of_int 10 : mword 5)
          = (mword_of_int 0 : mword 64)⌝ ∗ log_tx icfg_log ∗
         cauf_fail Γfs fsc_fs P Pmiss Φok Φex pl) -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type CREATE_AUF.
  Parameter wp_create_auf :
    forall `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
             !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
      (γs : list gname) (j : nat) (γl : gname)
      (pd pav pu : mword 64)
 (γf : gname)
      (plen : nat) (pfun : nat -> bv 8)
      (ty major minor : mword 16)
      (U : ustate)
      (u : nat) (Sb : gset Z)
      (ns : nat)
      (pidv : mword 32) (dqb dqs dqbs dqn : dfrac)
      (m : regfile) (K : nat) (eb : bool)
      (b : bool) (lks : gset string)
      (P Pmiss : nat -> Z -> iProp Σ)
      (Φok Φex : aview -> Z -> fname -> Z -> iProp Σ),
      wp_create_auf_body γs j γl pd pav pu
 γf
 plen pfun ty major minor
                        U u Sb ns pidv dqb dqs dqbs dqn m K eb b lks
                        P Pmiss Φok Φex.
End CREATE_AUF.