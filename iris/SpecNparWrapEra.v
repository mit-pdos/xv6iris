(* SpecNparWrapEra.v -- nameiparent's OWN contract at the nameiparent era
   trace ([SpecNparEra]), so a create-side caller never has to reach past
   the wrapper into namex.

     struct inode*
     nameiparent(char *path, char *name) { return namex(path, 1, name); }

   Worklist: claude-notes/projects/fs-syscall-specs.md, lane A item (iii),
   REMAINING item.  This is to [SpecNparEra] exactly what [SpecNameiEra] is
   to [SpecNamexEra]: eleven instructions of frame carve, and the two trace
   premises and the two postcondition arms threaded straight through.

   THE DIFF AGAINST [SpecNameiparent.wp_nameiparent_gen_body], and there is
   nothing else in this file:

     - ONE trace premise, [FsAbsStart.ep_start] -- the cursor and the
       PARENT-PREFIX family at whatever inum the walk begins at, which is
       [FsAbsEraMknod.mknod_walk_pre_era] on the nose
       ([FsAbsNparMknod.np_start_of_mknod]).  There is NO absolute-path
       premise: the relative start landed with lane A-iii and both arms
       of namex's entry test are proven;
     - the success arm gains the cursor at the parent index and exposes the
       returned inum ([SpecNparEra.inode_held_ty_at] in place of
       [IcacheRef.inode_held_ty]);
     - the failure arm gains [FsAbsNpar.np_dead].

   The counted contract ([wp_nameiparent_sconf_body]) has NO twin here, for
   the reason the namei-side era files have none: a counted continuation has
   no [P] to hand the cursor to. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list functions bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import auth gmap frac.
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
Require Import KernelDataInv.
Require Import SpecPanic.
Require Import FdSlots.
Require Import ProcGeom.
Require Export SwtchCtx.
Require Import CpuOwn.
Require Import SchedCtx.
Require Import ProcDefs.  (* [proc_priv_bare] *)
Require Import WpUart.
Require Import DiskPtsto DiskInv.
Require Import BioInv.
Require Import FsBlocks LogInv.
Require Import BitmapInv.
Require Import ByteBuf.
Require Import DirentEnc.
Require Import PathElems.
Require Import InodeInv.
Require Import InodeRegion.
Require Import IcacheInv.
Require Import IcacheEscrow.
Require Import KvmSpec.
Require Import FileInvDefs.
Require Import IcacheRef.
Require Import IrefSlots.
Require Import SpecIput.
Require Import SpecDirlookup.
Require Import SpecDirlink.
(* [walk_spend] / [walk_need] and the two ties, from the walker itself *)
Require Import SpecNamex.
Require Import SpecNameiTr.   (* [inode_held_at] *)
Require Import FsAbsEra.      (* [elend] *)
Require Import FsAbsNpar.     (* [np_elems]/[ep_hops_from]/[np_dead] *)
Require Import FsAbsStart.    (* [ep_start]: the DEFERRED start (lane A-iii) *)
Require Import SpecNparEra.   (* [inode_held_ty_at]: the typed, pinned parent *)
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import ProcAvail.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Require Import FsCfg.   (* [fscfg]: the fs configuration is AMBIENT *)
Import Defs.
Require Import TsoCtx.

Local Open Scope Z_scope.

(* nameiparent's own frame is 16 bytes (2 slots) over namex's 102. *)
Notation K_nameiparent := (114%nat) (only parsing).
(* ===================================================================== *)
(*  THE TRACE CONTRACT.  A thin forward of [SpecNparEra.wp_npar_era]:     *)
(*  this function's whole body is a namex call plus a stack carve, so the *)
(*  ledger clause is namex's verbatim, it takes no credit of its own,     *)
(*  fires no hop of its own, and all it does with the two trace rows is   *)
(*  move the register equation from namex's [mf] to its own.              *)
(* ===================================================================== *)
Definition wp_npar_wrap_era_body
    `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
      !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
    (gs : list gname) (j : nat) (gl : gname)           (* the running process *)
   (* disk fabric + lock  *)
    (pd pav pu : mword 64)
 (gf : gname)                          (* kalloc, file table  *)
    (plen : nat) (pfun : nat -> bv 8)                  (* the path buffer     *)
    (nfun : nat -> bv 8)                               (* the name buffer, in *)
    (n : nat) (Sb : gset Z)
    (P : nat -> Z -> iProp Σ)                          (* the cursor          *)
    (Pmiss : nat -> Z -> iProp Σ)                      (* the miss receipt    *)
    (pidv : mword 32) (dq dqb dqs dqpv : dfrac)
    (m : regfile) (K : nat) (eb : bool)
    (b : bool) (lks : gset string) (Upr : ustate) :=
  let pcE : mword 64 := mword_of_int KernelSyms.nameiparent in
  let pj := proc_addr j in
  let pv := m !!! Regidx (mword_of_int 10 : mword 5) in   (* a0 = path *)
  let nb := m !!! Regidx (mword_of_int 11 : mword 5) in   (* a1 = name *)
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  let pl := bview plen pfun in
  let L := length (path_elems pl) in
  (K_nameiparent <= K)%nat ->
  icfg_dev = ROOTDEV ->
  (0 < icfg_nib)%nat ->
  log_geom_ok fsc_cov fsc_logst ->
  0 < fsc_size <= BPB ->
  0 <= fsc_bmapstart ->
  fsc_bmapstart ∈ fsc_cov ->
  ~ (fsc_bmapstart ∈ log_region_set fsc_logst) ->
  0 <= icfg_ist ->
  cov_below fsc_cov fsc_size ->
  ireg_blocks_ok icfg_ist icfg_nib fsc_cov fsc_logst ->
  bb_cstr pfun plen ->
  (* the length fits int: the sext.w at +0x90 truncates [len = s2 - s1], and
     without this bound the [blt]-against-13 stops deciding [len <= 13] (and
     the short branch fails memmove's own 2^32 bound).  SpecFetchstr's
     header records the identical premise for strlen's [subw]. *)
  (Z.of_nat plen < 2 ^ 31)%Z ->
  (* the walk's need, no longer linear in the path length
     (fs-log.md §G.24; [SpecNamex.walk_need]) *)
  (walk_need L <= n)%nat ->
  (j < NPROC)%nat ->
  gs !! j = Some gl ->
  sie_cap_gpr KT1 m K b pj -∗
  cpu_own 0 eb pj b lks -∗
  (* THE TRAP-CSR COMPLEMENT, in and out -- namex's, threaded straight
     through.  [emp] at [eb = true]; the real pair at [eb = false].
     claude-notes/completed/eb-generic-sweep.md. *)
  trap_csrs_ext KT1 eb -∗
  cpu_claim_ext eb pj -∗
  kernel_text -∗ kernel_data -∗ pc_is pcE -∗
  panic_env -∗
  bio_ctx fsc_bio (fs_view fsc_fs fsc_disk icfg_dev fsc_cov) -∗
  log_ctx icfg_log fsc_bio fsc_fs fsc_cov fsc_logst icfg_dev -∗
  kalloc_env fsc_kalloc None -∗
  is_itable2 fsc_itlock fsc_ic fsc_fs fsc_ireg fsc_cov fsc_logst icfg_nib icfg_dev -∗
  itable_inv -∗
  ic_escrows fsc_ic fsc_fs fsc_ireg fsc_cov fsc_logst -∗
  ic_sleeplocks fsc_ic -∗
  ireg_inv fsc_ireg fsc_fs icfg_ist icfg_nib -∗
  (* ...AND THE SEALED REGIME (iclaim-ledger.md §3.2, RULING B; §6′ RULING G).
     Persistent, borrowed and never spent; it rides the SAME channel
     [ireg_inv] does.  It is here because this contract reaches iput, whose
     free path FREEZES the inode, and §2.3's boot-shelter clause makes a
     freezer exhibit the regime it freezes under.  A runtime caller hands
     [SpecIput] the LEFT arm of its borrowed disjunction and discards what
     comes back; only ireclaim, which freezes before the seal is fired,
     lends [ireg_boot] instead. *)
  ireg_open -∗
  procs_inv gs -∗
  dev_inv fsc_uart fsc_disk -∗
  disk_geom fsc_disk pd pav pu -∗
  is_lock fsc_dlock d_lock "virtio_disk"%string <{ disk_res fsc_disk pd pav pu }> -∗
  sb_bmapstart ↦₄{dqb} (mword_of_int fsc_bmapstart : mword 32) -∗
  sb_inodestart ↦₄{dqs} (mword_of_int icfg_ist : mword 32) -∗
  bitmap_inv fsc_fs fsc_bmapstart fsc_cov fsc_logst fsc_size -∗
  proc_priv_bare pj pidv Upr -∗
  inode_held (pv_cwd (us_V Upr)) -∗
  ([∗ list] i ∈ seq 0 (S plen), pa_add pv i ↦ₘ[KT1]{dqpv} pfun i) -∗
  ([∗ list] i ∈ seq 0 14, pa_add nb i ↦ₘ[KT1] nfun i) -∗
  bslots 3 -∗
  iref_slots 2 -∗
  (* the set form beside the transaction's token: namex's [ilock] takes
     the write arm (durable-disk B''-tx), and the pair rides in the set
     form's own position so no stage lemma moved *)
  log_opSt icfg_log n Sb -∗
  (* ---- THE TRACE, OVER THE PARENT PREFIX, DEFERRED IN THE START.
     Threaded straight into [SpecNparEra.wp_npar_era]; this wrapper
     touches it not at all. ---- *)
  ep_start fsc_fs P Pmiss pl -∗
  (* THE CROSSING IS THE LITERAL [true], NOT [b].  This function can SLEEP
     (through namex / dirlookup, down to ilock and sleep), so a park moves
     the hart with interrupts off and the crossing has nothing to do with
     SIE.  Spelled [b] the two coincide at the only instance the [eb = true]
     premise admits, which is why this went unnoticed. *)
  wp_next true pj (fun (CID : CpuId) =>
  ∀ (mf : regfile) (n' : nat) (Sb' : gset Z)
    (ok : bool) (nf : nat -> bv 8) (ipv : mword 64) (w : bool),
      ⌜callee_saved m mf⌝ -∗
      sie_cap_gpr KT1 mf K b pj -∗
      cpu_own 0 eb pj b lks -∗
      trap_csrs_ext KT1 eb -∗
      cpu_claim_ext eb pj -∗
      pc_is ret_tgt -∗
      sb_bmapstart ↦₄{dqb} (mword_of_int fsc_bmapstart : mword 32) -∗
      sb_inodestart ↦₄{dqs} (mword_of_int icfg_ist : mword 32) -∗
      proc_priv_bare pj pidv Upr -∗
      inode_held (pv_cwd (us_V Upr)) -∗
      ([∗ list] i ∈ seq 0 (S plen), pa_add pv i ↦ₘ[KT1]{dqpv} pfun i) -∗
      ([∗ list] i ∈ seq 0 14, pa_add nb i ↦ₘ[KT1] nf i) -∗
      bslots 3 -∗
      (* the set only GROWS; namex takes no credit and neither does
         this wrapper, so the counter clause is untouched *)
      ⌜Sb ⊆ Sb'⌝ -∗
      (* the walk's paid-bitmap report and the membership that makes it an
         honest read (fs-log.md §G.24), namex's verbatim *)
      ⌜w = true -> fsc_bmapstart ∈ Sb'⌝ -∗
      ⌜((n - (walk_spend w + (if ok then 0%nat else 1%nat)))%nat <= n')%nat
       /\ (n' <= n)%nat⌝ -∗
      (* the set form beside the transaction's token (B''-tx) *)
      log_opSt icfg_log n' Sb' -∗
      (if ok
       then (* THE PARENT: named, typed, PINNED, and with the cursor at its
               own index.  The type witness is the landed one (the walk
               tested it under the lock at +0xc4 and returns through
               [L_par], which is what closes fs-sysfile's Blocker B); what
               is new is the inum tie beside it and
               [P (length (np_elems pl)) iL] -- the whole parent prefix
               fired, in order, each hop at the then-current contents.  The
               family is exhausted at that index, so no hop comes back. *)
            ∃ (iL : Z) (es : list (list (bv 8))) (e : list (bv 8)),
              ⌜mf !!! Regidx (mword_of_int 10 : mword 5) = ipv⌝ ∗
              ⌜nameiparent_of pl es e /\ bname 14 nf = e⌝ ∗
              inode_held_ty_at ipv T_DIR iL ∗
              P (length (np_elems pl)) iL ∗
              iref_slots 1
       else ⌜mf !!! Regidx (mword_of_int 10 : mword 5)
             = (mword_of_int 0 : mword 64)⌝ ∗
            iref_slots 2 ∗
            np_dead fsc_fs P Pmiss pl) -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type NPAR_WRAP_ERA.
  Parameter wp_npar_wrap_era :
    forall `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
             !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
      (gs : list gname) (j : nat) (gl : gname)
      (pd pav pu : mword 64)
 (gf : gname)
      (plen : nat) (pfun : nat -> bv 8)
      (nfun : nat -> bv 8)
      (n : nat) (Sb : gset Z)
      (P : nat -> Z -> iProp Σ) (Pmiss : nat -> Z -> iProp Σ)
      (pidv : mword 32) (dq dqb dqs dqpv : dfrac)
      (m : regfile) (K : nat) (eb : bool)
      (b : bool) (lks : gset string) (Upr : ustate),
      wp_npar_wrap_era_body gs j gl pd pav pu
 gf
 plen pfun nfun n Sb P Pmiss
                            pidv dq dqb dqs dqpv m K eb b lks Upr.
End NPAR_WRAP_ERA.
