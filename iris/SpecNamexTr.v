(* SpecNamexTr.v -- N-3: namex WITH THE GHOST TRACE, the contract
   [SpecNameiTr.wp_namei_tr_body] is a 26-byte wrapper over
   (claude-notes/projects/namei-pinned-lookup.md §4; rulings in that file's
   STATUS header and §11.4).

   WHAT THIS IS.  [SpecNamex.wp_namex_gen] returns [inode_held ipv] -- a
   reference to SOME inode, with no relation to the path (the SpecNamex.v:
   113-124 scope ruling).  This file is that contract with the trace
   premises added and the two postcondition arms exposed, exactly as
   [SpecNameiTr] does one level up; everything else is
   [SpecNamex.wp_namex_gen_body] VERBATIM -- same ambient ties, same
   ledger, same budget, same eb/trap-CSR threading, same name buffer.

   THE DEFINITIONS ARE [SpecNameiTr]'s, IMPORTED, NOT RESTATED.  [nx_hop],
   [nx_hops_from] and [inode_held_at] are the RULED artifacts and live
   there; this file adds no vocabulary of its own.  The import direction is
   the only oddity in the pair -- the namei-level file was ruled and landed
   first, so the namex-level one sits ABOVE it in the cone.  Nothing else
   follows from that: [SpecNameiTr] does not mention this contract, and
   [ProofNameiTr] is what joins the two.

   SCOPE (ruled, and it is why [npar] is GONE rather than a parameter):
   ABSOLUTE PATHS ONLY, namei side only.  [pfun 0 = SLASH] sends the entry
   test at +0x22 down the [iget(ROOTDEV, ROOTINO)] arm, so the walk starts
   at the root and the caller's [P 0] is supplied there; [a1 = 0] kills the
   nameiparent arms at +0xd4 and +0x140.  The relative form waits for an
   inum-exposed cwd (Q-c) and the nameiparent variant for a consumer.

   THE FIRE POINT (what the proof owes, recorded here so the contract can
   be read against it).  namex holds the locked directory's payload from
   ilock's return to its iunlockput, and since N-1 that payload carries
   [DirViewG.dv_hold d (dv_of dn data)] -- the abstract contents, pinned to
   the bytes.  [nx_hop] is fired in dirlookup's CONTINUATION, at the
   instruction boundary where the walk already knows the answer: the
   fragment is lent whole through the caller's [={⊤}=∗], the bridge from
   dirlookup's [dir_first] answer to [ents !! s] is the uniqueness-free
   [FsTree.dv_lookup_found] / [FsTree.dv_lookup_none] (probe verdict §9.2),
   and the fragment goes straight back into the [ic_loaded] the walk
   re-packs for its iunlockput. *)
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
Require Import ProcDefs.
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
Require Import IrefSlots.
Require Import IcacheRef.
Require Import IcacheInv.
Require Import IcacheEscrow.   (* Require Export's DirViewG *)
Require Import KvmSpec.
Require Import FileInvDefs.
Require Import SpecDirlink.
Require Import SpecNamex.      (* K_namex, walk_need / walk_spend, ROOT* *)
Require Import SpecNameiTr.    (* THE RULED VOCABULARY: nx_hop, nx_hops_from,
                                  inode_held_at -- imported, never restated *)
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import ProcAvail.
Require Import Xv6G.
Require Import FsCfg.   (* [fscfg]: the fs configuration is AMBIENT *)
Import Defs.

Local Open Scope Z_scope.

(* ===================================================================== *)
(*  1. THE CONTINUATION, NAMED                                           *)
(* ===================================================================== *)

(* [SpecNamex.namex_postS] with the two arms replaced.  It is named for the
   same reason that one is (SpecNamex.v:306-320): namex's whole-function
   proof carries the continuation as a spatial hypothesis for thousands of
   proofmode steps and restates it inside its loop invariant, and every step
   re-embeds it in the proof term twice.  TRANSPARENT on purpose -- do NOT
   seal it; [iApply ("Hcont" $! mf ...)] unifies through a transparent
   constant and not through an opaque one. *)
Definition namex_tr_post
    `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
      !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId}
    (pj pv nb ret_tgt : mword 64) (pl : list (bv 8))
    (m : regfile) (K : nat) (b eb : bool) (lks : gset string)
    (g : log_names) (bn : bio_names)
    (cov : gset Z) (logstart bmapstart inodestart size : Z)
    (plen : nat) (pfun : nat -> bv 8)
    (n : nat) (Sb : gset Z)
    (P : nat -> Z -> iProp Σ) (Pmiss : nat -> Z -> iProp Σ)
    (pidv : mword 32)
    (dq dqb dqs dqpv : dfrac) (Vpr : pprivate) : iProp Σ :=
  (∀ (mf : regfile) (n' : nat) (Sb' : gset Z)
     (ok : bool) (nf : nat -> bv 8) (ipv : mword 64) (w : bool),
      ⌜callee_saved m mf⌝ -∗
      sie_cap_gpr KT1 mf K b pj -∗
      cpu_own 0 eb pj b lks -∗
      trap_csrs_ext KT1 eb -∗
      cpu_claim_ext eb pj -∗
      pc_is ret_tgt -∗
      (* EVERYTHING LOANED COMES BACK *)
      sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
      sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
      proc_priv_bare pj pidv Vpr -∗
      inode_held (pv_cwd Vpr) -∗
      ([∗ list] i ∈ seq 0 (S plen), pa_add pv i ↦ₘ[KT1]{dqpv} pfun i) -∗
      ([∗ list] i ∈ seq 0 14, pa_add nb i ↦ₘ[KT1] nf i) -∗
      bslots 3 -∗
      ⌜Sb ⊆ Sb'⌝ -∗
      ⌜w = true -> bmapstart ∈ Sb'⌝ -∗
      ⌜((n - (walk_spend w + (if ok then 0%nat else 1%nat)))%nat <= n')%nat
       /\ (n' <= n)%nat⌝ -∗
      (* the set form beside the transaction's token: this walk's [ilock]
         takes the write arm (durable-disk B''-tx), so the token travels
         with it -- in [log_opS]'s own position, so no stage lemma moved *)
      log_opSt g n' Sb' -∗
      (if ok
       then (* THE PIN: the register, the package AT ITS INUM, and the
               cursor having walked the whole path to that same inum.  The
               caller alone knows what its [P] says about [iL]; the contract
               promises only the CHAIN -- L hops fired, in order, each at the
               then-current contents. *)
            ∃ (iL : Z),
              ⌜mf !!! Regidx (mword_of_int 10 : mword 5) = ipv⌝ ∗
              inode_held_at ipv iL ∗
              P (length (path_elems pl)) iL ∗
              iref_slots 1
       else ⌜mf !!! Regidx (mword_of_int 10 : mword 5)
             = (mword_of_int 0 : mword 64)⌝ ∗
            iref_slots 2 ∗
            (* the death index, the receipt, and the UNFIRED suffix; the two
               disjuncts are [SpecNameiTr]'s, verbatim.  LEFT: hop [k] never
               fired (the cursor's node was not a directory, or the walk's
               own nlink guard died there), so [P k d] comes back beside hops
               [k..].  RIGHT: hop [k] fired and missed. *)
            (∃ (k : nat) (d : Z), ⌜(k < length (path_elems pl))%nat⌝ ∗
               ((P k d ∗ nx_hops_from P Pmiss pl k) ∨
                (Pmiss k d ∗ nx_hops_from P Pmiss pl (S k))))) -∗
      WP (Loop : expr riscv_lang))%I.

(* ===================================================================== *)
(*  2. THE CONTRACT: [SpecNamex.wp_namex_gen_body] + the trace           *)
(* ===================================================================== *)

Definition wp_namex_tr_body
    `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
      !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId}

    (gs : list gname) (j : nat) (gl : gname)           (* the running process *)
    (gu : uart_names) (gd : disk_names) (gk : gname)   (* disk fabric + lock  *)
    (pd pav pu : mword 64)
    (bn : bio_names)
    (g : log_names) (gi : gname)
    (gtl : gname)                      (* the itable's lock   *)
    (ga : gname) (gf : gname)                          (* kalloc, file table  *)
    (cov : gset Z) (logstart bmapstart inodestart : Z) (nib : nat)
    (size : Z) (dev : mword 32)
    (plen : nat) (pfun : nat -> bv 8)                  (* the path buffer     *)
    (nfun : nat -> bv 8)                               (* the name buffer, in *)
    (n : nat) (Sb : gset Z)
    (P : nat -> Z -> iProp Σ)                          (* the cursor          *)
    (Pmiss : nat -> Z -> iProp Σ)                      (* the miss receipt    *)
    (pidv : mword 32) (dq dqb dqs dqpv : dfrac)
    (m : regfile) (K : nat) (eb : bool)
    (b : bool) (lks : gset string) (Vpr : pprivate) :=
  let pcE : mword 64 := mword_of_int KernelSyms.namex in
  let pj := proc_addr j in
  let pv := m !!! Regidx (mword_of_int 10 : mword 5) in   (* a0 = path *)
  let nb := m !!! Regidx (mword_of_int 12 : mword 5) in   (* a2 = name *)
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  let pl := bview plen pfun in
  let L := length (path_elems pl) in
  (K_namex <= K)%nat ->
  dev = icfg_dev ->
  nib = icfg_nib ->
  g = icfg_log ->
  inodestart = icfg_ist ->
  dev = ROOTDEV ->
  (0 < nib)%nat ->
  log_geom_ok cov logstart ->
  0 < size <= BPB ->
  0 <= bmapstart ->
  bmapstart ∈ cov ->
  ~ (bmapstart ∈ log_region_set logstart) ->
  0 <= inodestart ->
  cov_below cov size ->
  ireg_blocks_ok inodestart nib cov logstart ->
  bb_cstr pfun plen ->
  (Z.of_nat plen < 2 ^ 31)%Z ->
  (* ABSOLUTE PATHS ONLY (ruling Q-c): the walk starts at the root and the
     cursor is supplied there. *)
  pfun 0%nat = SLASH ->
  (walk_need L <= n)%nat ->
  (j < NPROC)%nat ->
  gs !! j = Some gl ->
  (* a1 = 0: the namei side.  [SpecNamex]'s [npar] boolean is not a
     parameter here -- it is FIXED false by the ruling, so the flag's
     reflection premise is the one instance that survives. *)
  eq_vec (m !!! Regidx (mword_of_int 11 : mword 5)) zero_reg = true ->
  locks_below lks "log" ->
  sie_cap_gpr KT1 m K b pj -∗
  cpu_own 0 eb pj b lks -∗
  trap_csrs_ext KT1 eb -∗
  cpu_claim_ext eb pj -∗
  kernel_text -∗ kernel_data -∗ pc_is pcE -∗
  panic_env -∗
  bio_ctx bn (fs_view fsc_fs gd dev cov) -∗
  log_ctx g bn fsc_fs cov logstart dev -∗
  kalloc_env ga None -∗
  is_itable2 gtl fsc_ic fsc_fs gi cov logstart nib dev -∗
  itable_inv -∗
  ic_escrows fsc_ic fsc_fs gi cov logstart -∗
  ic_sleeplocks fsc_ic -∗
  ireg_inv gi fsc_fs inodestart nib -∗
  ireg_open -∗
  procs_inv gs -∗
  dev_inv gu gd -∗
  disk_geom gd pd pav pu -∗
  is_lock gk d_lock "virtio_disk"%string (disk_res gd pd pav pu) -∗
  sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
  sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
  bitmap_inv fsc_fs bmapstart cov logstart size -∗
  proc_priv_bare pj pidv Vpr -∗
  inode_held (pv_cwd Vpr) -∗
  ([∗ list] i ∈ seq 0 (S plen), pa_add pv i ↦ₘ[KT1]{dqpv} pfun i) -∗
  ([∗ list] i ∈ seq 0 14, pa_add nb i ↦ₘ[KT1] nfun i) -∗
  bslots 3 -∗
  iref_slots 2 -∗
  (* the set form beside the transaction's token (durable-disk B''-tx) *)
  log_opSt g n Sb -∗
  (* ---- THE TRACE (the two new resource premises) ---- *)
  P 0%nat (bv_unsigned ROOTINO) -∗
  nx_hops_from P Pmiss pl 0%nat -∗
  (* THE CROSSING IS THE LITERAL [true], NOT [b] -- namex parks; see
     [SpecNamex.wp_namex_gen_body]'s note. *)
  wp_next true pj (fun (CIDc : CpuId) =>
    namex_tr_post (CID := CIDc) pj pv nb ret_tgt pl m K b eb lks
                  g bn cov logstart bmapstart inodestart size
                  plen pfun n Sb P Pmiss pidv dq dqb dqs dqpv Vpr) -∗
  WP (Loop : expr riscv_lang).

Module Type NAMEX_TR.
  Parameter wp_namex_tr :
    forall `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
             !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId}
      (gs : list gname) (j : nat) (gl : gname)
      (gu : uart_names) (gd : disk_names) (gk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names)
      (g : log_names) (gi : gname)
      (gtl : gname)
      (ga : gname) (gf : gname)
      (cov : gset Z) (logstart bmapstart inodestart : Z) (nib : nat)
      (size : Z) (dev : mword 32)
      (plen : nat) (pfun : nat -> bv 8)
      (nfun : nat -> bv 8)
      (n : nat) (Sb : gset Z)
      (P : nat -> Z -> iProp Σ) (Pmiss : nat -> Z -> iProp Σ)
      (pidv : mword 32) (dq dqb dqs dqpv : dfrac)
      (m : regfile) (K : nat) (eb : bool)
      (b : bool) (lks : gset string) (Vpr : pprivate),
      wp_namex_tr_body gs j gl gu gd gk pd pav pu bn g gi gtl
                       ga gf cov logstart bmapstart inodestart nib
                       size dev plen pfun nfun n Sb P Pmiss
                       pidv dq dqb dqs dqpv m K eb b lks Vpr.
End NAMEX_TR.
