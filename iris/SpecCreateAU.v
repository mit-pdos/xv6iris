(* SpecCreateAU.v -- create's ATOMIC-UPDATE contract: [SpecCreate]'s
   calling convention with the mknod AU's commit steps threaded through
   the walk, the exists-lookup and the entry write.

   Worklist: claude-notes/projects/fs-syscall-specs.md, lane W (the mknod
   AU prover).  A PARALLEL FORM beside [SpecCreate.wp_create_sconf] -- R10:
   the landed contract does not move, and neither does [SpecSysMknodAU].

   ==== WHY A PARALLEL create CONTRACT EXISTS AT ALL ====================

   Every instant the mknod AU speaks about is INSIDE create's cone: the
   walk's hops happen in nameiparent, [dlookup_commit] fires at create's
   own [dirlookup] (the exists test), and [acre_commit]'s two phases
   bracket the parent-row retag create performs after its [dirlink]
   returns.  None of that is derivable from the SEALED
   [wp_create_sconf], whose post says nothing about the abstract state or
   the trace.  So the AU has to be carried THROUGH create, exactly as
   [SpecNparEra] carries the trace through namex.

   ==== THE THREE DIFFERENCES, AND THERE ARE NO OTHERS ==================

   (1) THE WALK IS THE ERA WALK.  [SpecNparWrapEra.wp_npar_wrap_era] in
       place of [SpecNameiparent.wp_nameiparent_gen]: the two trace rows
       ([P 0 ROOTINO] and [FsAbsNpar.ep_hops_from] over the PARENT PREFIX)
       come in, the cursor at the parent index and the parent's own inum
       come back on success, and [FsAbsNpar.np_dead] comes back on
       failure.  That walk is ABSOLUTE-PATHS-ONLY, so this contract takes
       [pfun 0 = SLASH]; the relative start is the era walk's own
       out-of-scope item and not this file's.

   (2) THE TYPE IS FIXED AT [T_DEVICE].  mknod is the only caller of this
       form, and pinning [ty] buys two whole halves of the walk: the
       [beq s4,1] at +0xc8 never takes the directory arm (so the mkdir
       half and both of its failure tails are refuted rather than
       re-proved), and the [bne s2,2] at +0x5a always leaves the found
       half through ARM F-BAD (so the [ip->type] inspection is refuted
       too).  The consequence a caller sees is that [ok = true] forces
       [made = true] -- the F-OK arm needs [ty = T_FILE] -- so the
       success payout is create's ARM C-OK alone, at the record
       [SpecCreate.create_made T_DEVICE major minor].  A general-[ty] form
       is a later lane's (mkdir wants [ADir] and the fused
       [SpecSysMknodAU.acre_bump]); nothing here is in its way.

   (3) THE COMMITS ARE THE AUTHORITY-SHAPED ONES.  [FsAbsMknodFire]'s
       [dlookup_commit_at] / [acre_commit_at], not the frozen
       [astate]-shaped pair -- see that file's header for why the frozen
       shape cannot be discharged against [InodeRegion.ftop_body] at all
       ([abs_view] is not injective, so no give-back wand can be paid).
       The read-only one IMPLIES the frozen form, so a client that can
       serve the frozen [dlookup_commit] is not being asked for more
       there.

   ==== THE ARMS ========================================================

   [cau_ok] is [SpecSysMknodAU.mknod_post_ok]'s content at the inum
   create returns, minus the two facts create's own post already states
   ([0 < i < 16 * icfg_nib] is there verbatim).  [cau_fail] is
   [mknod_post_fail]'s SECOND disjunct at create's own path -- the
   syscall's first disjunct is the argstr failure, which create never
   sees.  Which create arm lands where:

     ARM N        the walk died: [np_dead] folds by
                  [FsAbsNparMknod.np_dead_to_mknod] into EITHER
                  [mknod_walk_dead_era] (left) OR the cursor at the parent
                  index (right, with both commits refunded).
     ARM G        the parent's nlink guard: cursor back, no observation.
     ARM F-BAD    the name WAS there: the exists observation FIRED, so the
                  right disjunct's LEFT alternative ([Φex]) is the payout
                  and the lookup commit is spent.
     ARM A-FAIL   out of inodes: cursor back, no observation.
     ARM FAIL     dirlink failed: cursor back, no observation.
     ARM C-OK     the success commit fired at the entry write.

   BINDERS: [SpecCreate]'s section list verbatim -- NO standalone
   [icacheG]/[icfg] (SpecCreate's header records why that is
   load-bearing rather than tidy). *)
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
Require Import DirView.
Require Import FsTree.          (* [fname]                                  *)
Require Import InodeInv.        (* [ROOTINO] : mword 32                     *)
Require Import InodeLock.
Require Import InodeRegion.
Require Import IrefSlots.
Require Import IcacheRef.
Require Import IcacheInv.
Require Import IcacheEscrow.
Require Import SleepLock.
Require Import KvmSpec.
Require Import FileInvDefs.
Require Import ProcInv.
Require Import SpecDirlookup.
Require Import SpecIput.
Require Import SpecCreate.      (* the landed contract this parallels       *)
Require Import FsBytesGamma.    (* [fs_gamma_L]: the live Γ                 *)
Require Import SpecSysMknodAU.  (* [cre_pre], [mknod_parent_elems]          *)
Require Import FsAbsEra.
Require Import FsAbsNpar.       (* [np_elems], [ep_hops_from], [np_dead]    *)
Require Import FsAbsEraMknod.   (* [mknod_walk_dead_era]                    *)
Require Import FsAbsMknodFire.  (* the authority-shaped commits             *)
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import ProcAvail.
Require Import Xv6G.
Require Import FsCfg.
Require Import FsAbs.           (* LAST (FsAbs's own rule)                  *)
Import Defs.

Local Open Scope Z_scope.

Section CreateAUSpec.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ}.

  (* ------------------------------------------------------------------ *)
  (*  THE SUCCESS PAYOUT (ARM C-OK)                                      *)
  (* ------------------------------------------------------------------ *)

  (* the cursor at the parent index, the fired success receipt with its
     instant's facts restated purely, the name tie, and the UNFIRED lookup
     commit refunded -- [SpecSysMknodAU.mknod_post_ok]'s content at the
     inum create's post already names. *)
  Definition cau_ok Γ (ma mi : Z) (P : nat -> Z -> iProp Σ)
      (Φok Φex : aview -> Z -> fname -> Z -> iProp Σ)
      (pl : list (bv 8)) (i : Z) : iProp Σ :=
    (∃ (av : aview) (d : Z) (nm : fname) (ents : gmap fname Z) (nl : nat),
       ⌜list_basics.last (path_elems pl) = Some nm⌝ ∗
       ⌜cre_pre av d nm ents nl i (ADev ma mi)⌝ ∗
       P (length (mknod_parent_elems pl)) d ∗
       dlookup_commit_at Γ ∅ Φex ∗
       Φok av d nm i)%I.

  (* ------------------------------------------------------------------ *)
  (*  THE FAILURE FOLD (ARMS N / G / F-BAD / A-FAIL / FAIL)              *)
  (* ------------------------------------------------------------------ *)

  Definition cau_fail Γ (γfs : fs_names) (ma mi : Z)
      (P Pmiss : nat -> Z -> iProp Σ)
      (Φok Φex : aview -> Z -> fname -> Z -> iProp Σ)
      (pl : list (bv 8)) : iProp Σ :=
    ((mknod_walk_dead_era γfs P Pmiss pl
        ∗ acre_commit_at Γ ∅ (ADev ma mi) Φok
        ∗ dlookup_commit_at Γ ∅ Φex)
     ∨ (∃ d : Z,
          P (length (mknod_parent_elems pl)) d
          ∗ acre_commit_at Γ ∅ (ADev ma mi) Φok
          ∗ ((∃ (av : aview) (i : Z) (nm : fname) (ents : gmap fname Z)
                (nl : nat),
                ⌜list_basics.last (path_elems pl) = Some nm⌝ ∗
                ⌜av !! d = Some (MkAnode (ADir ents) nl)⌝ ∗
                ⌜ents !! nm = Some i⌝ ∗
                Φex av d nm i)
             ∨ dlookup_commit_at Γ ∅ Φex)))%I.

End CreateAUSpec.

(* big-op bodies behind definitions: seal them, or an [iFrame] near a
   consumer resolves instances through the whole hop family
   (durable-notes; optimization.md, "a big-op body is the predictor"). *)
Global Typeclasses Opaque cau_ok cau_fail.

Definition wp_create_au_body
    `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
      !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId}
    (γs : list gname) (j : nat) (γl : gname)          (* the running process *)
  (* disk fabric + lock  *)
    (pd pav pu : mword 64)
 (γf : gname)           (* kalloc, ftable, printk *)
    (plen : nat) (pfun : nat -> bv 8)                 (* the PATH buffer     *)
    (ty major minor : mword 16)                       (* a1, a2, a3          *)
    (V : pprivate)                                    (* the running process *)
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
  let ma := bv_unsigned major in
  let mi := bv_unsigned minor in
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
  (* ---- THE ERA WALK's SCOPE: absolute paths (SpecNparEra's header) ---- *)
  pfun 0%nat = SLASH ->
  (* ---- ialloc's three geometry premises ---- *)
  1 < fsc_ninodes ->
  fsc_ninodes <= 16 * Z.of_nat icfg_nib ->
  fsc_ninodes < 2 ^ 31 ->
  16 * Z.of_nat icfg_nib <= 2 ^ 16 ->
  (* ---- THE TYPE IS FIXED (see the header, difference (2)) ---- *)
  ty = T_DEVICE ->
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
  proc_priv γf pj pidv V -∗
  ([∗ list] i ∈ seq 0 (S plen), pa_add pv i ↦ₘ[KT1] pfun i) -∗
  procs_inv γs -∗
  dev_inv fsc_uart fsc_disk -∗
  disk_geom fsc_disk pd pav pu -∗
  is_lock fsc_dlock d_lock "virtio_disk"%string (disk_res fsc_disk pd pav pu) -∗
  bslots 3 -∗
  iref_slots ns -∗
  log_opS icfg_log u Sb -∗
  log_tx icfg_log -∗
  (* ---- THE AU SIDE: the two trace rows and the two commits ----
     The trace rows are the ALREADY-FIRED form of
     [FsAbsEraMknod.mknod_walk_pre_era]: create knows its own path buffer,
     so the syscall fires that one-shot at the string it fetched
     ([FsAbsNparMknod.np_pre_of_mknod]) and hands the two rows in.  The
     hop family is over the PARENT PREFIX, which is
     [SpecSysMknodAU.mknod_parent_elems] definitionally. *)
  P 0%nat (bv_unsigned ROOTINO) -∗
  ep_hops_from fsc_fs P Pmiss pl 0%nat -∗
  acre_commit_at Γfs ∅ (ADev ma mi) Φok -∗
  dlookup_commit_at Γfs ∅ Φex -∗
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
      proc_priv γf pj pidv V -∗
      ([∗ list] i ∈ seq 0 (S plen), pa_add pv i ↦ₘ[KT1] pfun i) -∗
      bslots 3 -∗
      ⌜if ok then (S ns' = ns)%nat else ns' = ns⌝ -∗
      iref_slots ns' -∗
      ⌜Sb ⊆ Sb' /\ (u' <= u)%nat /\ (ok = true -> (iput_units <= u')%nat)⌝ -∗
      log_opS icfg_log u' Sb' -∗
      (if ok
       then (* ARM C-OK ALONE: at [ty = T_DEVICE] the found arm cannot
               succeed, so [made] is forced and the record is
               [create_made]. *)
         ⌜mf !!! Regidx (mword_of_int 10 : mword 5) = ientry k
          /\ (k < NINODE)%nat
          /\ 0 < bv_unsigned inum < 16 * Z.of_nat icfg_nib
          /\ made = true
          /\ dn = create_made ty major minor⌝ ∗
         create_locked pidv k qi s g inum dn bm ∗
         cau_ok Γfs ma mi P Φok Φex pl (bv_unsigned inum)
       else
         ⌜mf !!! Regidx (mword_of_int 10 : mword 5)
          = (mword_of_int 0 : mword 64)⌝ ∗ log_tx icfg_log ∗
         cau_fail Γfs fsc_fs ma mi P Pmiss Φok Φex pl) -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type CREATE_AU.
  Parameter wp_create_au :
    forall `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
             !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId}
      (γs : list gname) (j : nat) (γl : gname)
      (pd pav pu : mword 64)
 (γf : gname)
      (plen : nat) (pfun : nat -> bv 8)
      (ty major minor : mword 16)
      (V : pprivate)
      (u : nat) (Sb : gset Z)
      (ns : nat)
      (pidv : mword 32) (dqb dqs dqbs dqn : dfrac)
      (m : regfile) (K : nat) (eb : bool)
      (b : bool) (lks : gset string)
      (P Pmiss : nat -> Z -> iProp Σ)
      (Φok Φex : aview -> Z -> fname -> Z -> iProp Σ),
      wp_create_au_body γs j γl pd pav pu
 γf
 plen pfun ty major minor
                        V u Sb ns pidv dqb dqs dqbs dqn m K eb b lks
                        P Pmiss Φok Φex.
End CREATE_AU.
