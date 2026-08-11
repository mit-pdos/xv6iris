(* SpecNameiparent.v -- the public interface of nameiparent.

     struct inode*
     nameiparent(char *path, char *name)
     {
       return namex(path, 1, name);
     }

   26 bytes.  Decode, verified off CodeNameiparent.v:

     +0x00  [c.addi sp,sp,-16]        (2-slot frame)
     +0x02  [c.sdsp ra,8(sp)]
     +0x04  [c.sdsp s0,0(sp)]
     +0x06  [c.addi4spn s0,sp,16]     (s0 = sp + 16)
     +0x08  [c.mv a2,a1]              a2 = the CALLER'S name buffer
     +0x0a  [c.li a1,1]               nameiparent = 1
     +0x0c  [jal ra,namex]            0x80003a36 - 526 = 0x80003828   OK
     +0x10..0x16  epilogue and [c.jr ra]

   THE NAME BUFFER IS THE CALLER'S, arriving in a1 and moved to a2, so it is
   threaded and so is its content clause: on the success arm the fourteen
   bytes hold the LAST path element, canonically -- [DirentEnc.bname 14 nf = e]
   with [PathElems.nameiparent_of pl es e].  Everything else is
   [SpecNamex.wp_namex_sconf_body] at [npar = true].

   nameiparent enters and returns at noff 0. *)
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
Require Import BitmapInv.
Require Import ByteBuf.
Require Import DinodeEnc.
Require Import DirentEnc.
Require Import PathElems.
Require Import DirView.
Require Import InodeInv.
Require Import InodeLock.
Require Import InodeRegion.
Require Import IrefSlots.
Require Import IcacheRef.
Require Import IcacheInv.
Require Import IcacheEscrow.
Require Import KallocInv.
Require Import UserPtTree.
Require Import KvmSpec.
Require Import ProcPtOwn.
Require Import FileInv ProcInv.
Require Import SpecIput.
Require Import SpecDirlookup.
Require Import SpecDirlink.
Require Import SpecNamex.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Import Defs.

Local Open Scope Z_scope.

(* nameiparent's own frame is 16 bytes (2 slots) over namex's 94. *)
Definition K_nameiparent : nat := 96%nat.

Definition wp_nameiparent_sconf_body
    `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !kallocG Σ,
      !bioG Σ, !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ,
      ICFG : icfg, !icacheG Σ, !irefslotG Σ, !iregG Σ}
    `{GEN : GenId} `{CID : CpuId}

    (gs : list gname) (j : nat) (gl : gname)           (* the running process *)
    (gu : uart_names) (gd : disk_names) (gk : gname)   (* disk fabric + lock  *)
    (pd pav pu : mword 64)
    (bn : bio_names)
    (g : log_names) (gfs : fs_names) (gi : gname)
    (cn : ic_names) (gtl : gname)                      (* the icache + itable *)
    (ga : gname) (gf : gname)                          (* kalloc, file table  *)
    (cov : gset Z) (logstart bmapstart inodestart : Z) (nib : nat)
    (size : Z) (dev : mword 32)
    (used : gset Z)
    (cwdv : mword 64)                                  (* p->cwd, untouched   *)
    (plen : nat) (pfun : nat -> bv 8)                  (* the path buffer     *)
    (nfun : nat -> bv 8)                               (* the name buffer, in *)
    (n : nat)
    (pidv : mword 32) (dq dqb dqs dqc : dfrac)
    (m : regfile) (K : nat) (eb : bool) (C : iProp Σ)
    (b : bool) :=
  let pcE : mword 64 := mword_of_int KernelSyms.nameiparent in
  let pj := proc_addr j in
  let pv := m !!! Regidx (mword_of_int 10 : mword 5) in   (* a0 = path *)
  let nb := m !!! Regidx (mword_of_int 11 : mword 5) in   (* a1 = name *)
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  let pl := bview plen pfun in
  let L := length (path_elems pl) in
  (K_nameiparent <= K)%nat ->
  dev = icfg_dev ->
  nib = icfg_nib ->
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
  (* the length fits int: the sext.w at +0x90 truncates [len = s2 - s1], and
     without this bound the [blt]-against-13 stops deciding [len <= 13] (and
     the short branch fails memmove's own 2^32 bound).  SpecFetchstr's
     header records the identical premise for strlen's [subw]. *)
  (Z.of_nat plen < 2 ^ 31)%Z ->
  ((L + 1) * iput_units <= n)%nat ->
  (j < NPROC)%nat ->
  gs !! j = Some gl ->
  eb = true ->
  sie_cap_gpr m K b pj -∗
  cpu_own 0 eb pj C b -∗
  kernel_text -∗ pc_is pcE -∗
  panic_wp_any -∗
  bio_ctx bn (fs_view gfs gd dev cov) -∗
  log_ctx g bn gfs cov logstart dev -∗
  kalloc_env ga None -∗
  is_itable2 gtl cn gfs gi cov logstart nib dev -∗
  itable_inv -∗
  ic_escrows cn gfs gi cov logstart -∗
  ic_sleeplocks cn -∗
  ireg_inv gi gfs inodestart nib -∗
  procs_inv gs -∗
  dev_inv gu gd -∗
  disk_geom gd pd pav pu -∗
  is_lock gk d_lock "virtio_disk"%string (disk_res gd pd pav pu) -∗
  sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
  sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
  bitmap_res gfs bmapstart cov logstart size used -∗
  p_pid pj ↦₄{dq} pidv -∗
  p_cwd pj ↦₈{dqc} cwdv -∗
  inode_held cwdv -∗
  ([∗ list] i ∈ seq 0 (S plen), pa_add pv i ↦ₘ pfun i) -∗
  ([∗ list] i ∈ seq 0 14, pa_add nb i ↦ₘ nfun i) -∗
  bslots bn 3 -∗
  iref_slots 2 -∗
  log_op g n -∗
  wp_next b pj (fun (CID : CpuId) =>
  ∀ (mf : regfile) (n' : nat) (used' : gset Z)
    (ok : bool) (nf : nat -> bv 8) (ipv : mword 64),
      ⌜callee_saved m mf⌝ -∗
      sie_cap_gpr mf K b pj -∗
      cpu_own 0 eb pj C b -∗
      pc_is ret_tgt -∗
      sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
      sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
      ⌜used' ⊆ used⌝ -∗
      bitmap_res gfs bmapstart cov logstart size used' -∗
      p_pid pj ↦₄{dq} pidv -∗
      p_cwd pj ↦₈{dqc} cwdv -∗
      inode_held cwdv -∗
      ([∗ list] i ∈ seq 0 (S plen), pa_add pv i ↦ₘ pfun i) -∗
      ([∗ list] i ∈ seq 0 14, pa_add nb i ↦ₘ nf i) -∗
      bslots bn 3 -∗
      ⌜((n - (L + 1) * iput_units)%nat <= n')%nat /\ (n' <= n)%nat⌝ -∗
      log_op g n' -∗
      (if ok
       then ⌜mf !!! Regidx (mword_of_int 10 : mword 5) = ipv
             /\ (exists es e, nameiparent_of pl es e /\ bname 14 nf = e)⌝ ∗
            inode_held ipv ∗
            iref_slots 1
       else ⌜mf !!! Regidx (mword_of_int 10 : mword 5)
             = (mword_of_int 0 : mword 64)⌝ ∗
            iref_slots 2) -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type NAMEIPARENT.
  Parameter wp_nameiparent_sconf :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !kallocG Σ,
             !bioG Σ, !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ,
             ICFG : icfg, !icacheG Σ, !irefslotG Σ, !iregG Σ}
      `{GEN : GenId} `{CID : CpuId}
      (gs : list gname) (j : nat) (gl : gname)
      (gu : uart_names) (gd : disk_names) (gk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names)
      (g : log_names) (gfs : fs_names) (gi : gname)
      (cn : ic_names) (gtl : gname)
      (ga : gname) (gf : gname)
      (cov : gset Z) (logstart bmapstart inodestart : Z) (nib : nat)
      (size : Z) (dev : mword 32)
      (used : gset Z)
      (cwdv : mword 64)
      (plen : nat) (pfun : nat -> bv 8)
      (nfun : nat -> bv 8)
      (n : nat)
      (pidv : mword 32) (dq dqb dqs dqc : dfrac)
      (m : regfile) (K : nat) (eb : bool) (C : iProp Σ)
      (b : bool),
      wp_nameiparent_sconf_body gs j gl gu gd gk pd pav pu bn g gfs gi cn gtl
                                ga gf cov logstart bmapstart inodestart nib
                                size dev used cwdv plen pfun nfun n
                                pidv dq dqb dqs dqc m K eb C b.
End NAMEIPARENT.
