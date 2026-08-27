(* SpecNamei.v -- the public interface of namei, namex's namei-side wrapper.

     struct inode*
     namei(char *path)
     {
       char name[DIRSIZ];
       return namex(path, 0, name);
     }

   26 bytes.  Decode, verified off CodeNamei.v:

     +0x00  [c.addi sp,sp,-32]        (4-slot frame)
     +0x02  [c.sdsp ra,24(sp)]
     +0x04  [c.sdsp s0,16(sp)]
     +0x06  [c.addi4spn s0,sp,32]     (s0 = sp + 32)
     +0x08  [addi a2,s0,-32]          a2 = &name[0] = sp + 0
     +0x0c  [c.li a1,0]               nameiparent = 0
     +0x0e  [jal ra,namex]            0x80003a1e - 502 = 0x80003828   OK
     +0x12..0x18  epilogue and [c.jr ra]

   THE NAME BUFFER IS NAMEI'S OWN FRAME -- slots 0 and 1 of the four, i.e.
   sp+0..sp+15, of which namex writes at most fourteen -- so it does NOT
   appear in this contract: it is carved out of [stack_own] the way
   dirlookup's [de] record is, with [StackBytes.slot_bytes_own].  Everything
   else is [SpecNamex.wp_namex_sconf_body] at [npar = false], minus the name
   buffer and minus the nameiparent clause of the postcondition.

   namei enters and returns at noff 0. *)
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
Require Import SpecDirlink.
(* [walk_spend] / [walk_need] and the two ties, from the walker itself *)
Require Import SpecNamex.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import ProcAvail.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Require Import FsCfg.   (* [fscfg]: the fs configuration is AMBIENT *)
Import Defs.

Local Open Scope Z_scope.

(* namei's own frame is 32 bytes (4 slots) over namex's 102. *)
Notation K_namei := (116%nat) (only parsing).
Definition wp_namei_sconf_body
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
    (n : nat)
    (pidv : mword 32) (dq dqb dqs dqpv : dfrac)
    (m : regfile) (K : nat) (eb : bool)
    (b : bool) (lks : gset string) (Vpr : pprivate) :=
  let pcE : mword 64 := mword_of_int KernelSyms.namei in
  let pj := proc_addr j in
  let pv := m !!! Regidx (mword_of_int 10 : mword 5) in   (* a0 = path *)
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  let pl := bview plen pfun in
  let L := length (path_elems pl) in
  (K_namei <= K)%nat ->
  dev = icfg_dev ->
  nib = icfg_nib ->
  (* the region's two ambient ties, threaded verbatim to namex
     (fs-log.md §G.25) *)
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
  (* the length fits int: the sext.w at +0x90 truncates [len = s2 - s1], and
     without this bound the [blt]-against-13 stops deciding [len <= 13] (and
     the short branch fails memmove's own 2^32 bound).  SpecFetchstr's
     header records the identical premise for strlen's [subw]. *)
  (Z.of_nat plen < 2 ^ 31)%Z ->
  ((L + 1) * iput_units <= n)%nat ->
  (j < NPROC)%nat ->
  gs !! j = Some gl ->
  sie_cap_gpr KT1 m K b pj -∗
  cpu_own 0 eb pj b lks -∗
  (* THE TRAP-CSR COMPLEMENT, in and out -- namex's, threaded straight
     through.  [emp] at [eb = true]; the real pair at [eb = false],
     which is the index forkret's [if (first)] arm reaches this cone
     at through kexec.  claude-notes/completed/eb-generic-sweep.md. *)
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
  dev_inv gu gd -∗
  disk_geom gd pd pav pu -∗
  is_lock gk d_lock "virtio_disk"%string (disk_res gd pd pav pu) -∗
  sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
  sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
  bitmap_inv fsc_fs bmapstart cov logstart size -∗
  proc_priv_bare pj pidv Vpr -∗
  inode_held (pv_cwd Vpr) -∗
  (* ---- THE PATH RIDES THE CALLER'S FRACTION [dqpv]; THE NAME BUFFER STAYS
     WHOLE.  The rule the tree follows: a byte run the callee only READS takes
     the caller's dfrac, a run it WRITES stays at [DfracOwn 1].  The walk only
     LOADS from the path (skipslash, the element scan, the memmove's source),
     so [dqpv]; namex STORES each path element into [name[DIRSIZ]], so that run
     cannot be fractional.  The consumer is kexec: forkret calls
     [kexec("/init", (char *[]){"/init", 0})], so the one .rodata literal is
     both the path and argv[0] and cannot be owned twice outright.  Callers
     that own their path buffer (sys_open, sys_link, sys_unlink, sys_chdir,
     create -- each with [char path[MAXPATH]] on its own stack) pass
     [DfracOwn 1] and see no change. ---- *)
  ([∗ list] i ∈ seq 0 (S plen), pa_add pv i ↦ₘ[KT1]{dqpv} pfun i) -∗
  bslots 3 -∗
  iref_slots 2 -∗
  log_op g n -∗
  (* THE CROSSING IS THE LITERAL [true], NOT [b].  This function can SLEEP
     (through namex / dirlookup, down to ilock and sleep), so a park moves
     the hart with interrupts off and the crossing has nothing to do with
     SIE.  Spelled [b] the two coincide at the only instance the [eb = true]
     premise admits, which is why this went unnoticed. *)
  wp_next true pj (fun (CID : CpuId) =>
  ∀ (mf : regfile) (n' : nat)
    (ok : bool) (ipv : mword 64),
      ⌜callee_saved m mf⌝ -∗
      sie_cap_gpr KT1 mf K b pj -∗
      cpu_own 0 eb pj b lks -∗
      trap_csrs_ext KT1 eb -∗
      cpu_claim_ext eb pj -∗
      pc_is ret_tgt -∗
      sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
      sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
      proc_priv_bare pj pidv Vpr -∗
      inode_held (pv_cwd Vpr) -∗
      ([∗ list] i ∈ seq 0 (S plen), pa_add pv i ↦ₘ[KT1]{dqpv} pfun i) -∗
      bslots 3 -∗
      ⌜((n - (L + 1) * iput_units)%nat <= n')%nat /\ (n' <= n)%nat⌝ -∗
      log_op g n' -∗
      (if ok
       then ⌜mf !!! Regidx (mword_of_int 10 : mword 5) = ipv⌝ ∗
            inode_held ipv ∗
            iref_slots 1
       else ⌜mf !!! Regidx (mword_of_int 10 : mword 5)
             = (mword_of_int 0 : mword 64)⌝ ∗
            iref_slots 2) -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

(* ===================================================================== *)
(*  THE SET-FORM CONTRACT (fs-sysfile GR-2b, retrofit 6).  A thin        *)
(*  forward of [SpecNamex.wp_namex_gen]: this function's whole body is a  *)
(*  namex call plus a stack carve, so the ledger clause is namex's        *)
(*  verbatim and it takes no credit of its own.                           *)
(* ===================================================================== *)
Definition wp_namei_gen_body
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
    (n : nat) (Sb : gset Z)
    (pidv : mword 32) (dq dqb dqs dqpv : dfrac)
    (m : regfile) (K : nat) (eb : bool)
    (b : bool) (lks : gset string) (Vpr : pprivate) :=
  let pcE : mword 64 := mword_of_int KernelSyms.namei in
  let pj := proc_addr j in
  let pv := m !!! Regidx (mword_of_int 10 : mword 5) in   (* a0 = path *)
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  let pl := bview plen pfun in
  let L := length (path_elems pl) in
  (K_namei <= K)%nat ->
  dev = icfg_dev ->
  nib = icfg_nib ->
  (* the region's two ambient ties, threaded verbatim to namex
     (fs-log.md §G.25) *)
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
     through.  [emp] at [eb = true]; the real pair at [eb = false],
     which is the index forkret's [if (first)] arm reaches this cone
     at through kexec.  claude-notes/completed/eb-generic-sweep.md. *)
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
  dev_inv gu gd -∗
  disk_geom gd pd pav pu -∗
  is_lock gk d_lock "virtio_disk"%string (disk_res gd pd pav pu) -∗
  sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
  sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
  bitmap_inv fsc_fs bmapstart cov logstart size -∗
  proc_priv_bare pj pidv Vpr -∗
  inode_held (pv_cwd Vpr) -∗
  ([∗ list] i ∈ seq 0 (S plen), pa_add pv i ↦ₘ[KT1]{dqpv} pfun i) -∗
  bslots 3 -∗
  iref_slots 2 -∗
  (* the set form beside the transaction's token: namex's [ilock] takes
     the write arm (durable-disk B''-tx), and the pair rides in the set
     form's own position so no stage lemma moved *)
  log_opSt g n Sb -∗
  (* THE CROSSING IS THE LITERAL [true], NOT [b].  This function can SLEEP
     (through namex / dirlookup, down to ilock and sleep), so a park moves
     the hart with interrupts off and the crossing has nothing to do with
     SIE.  Spelled [b] the two coincide at the only instance the [eb = true]
     premise admits, which is why this went unnoticed. *)
  wp_next true pj (fun (CID : CpuId) =>
  ∀ (mf : regfile) (n' : nat) (Sb' : gset Z)
    (ok : bool) (ipv : mword 64) (w : bool),
      ⌜callee_saved m mf⌝ -∗
      sie_cap_gpr KT1 mf K b pj -∗
      cpu_own 0 eb pj b lks -∗
      trap_csrs_ext KT1 eb -∗
      cpu_claim_ext eb pj -∗
      pc_is ret_tgt -∗
      sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
      sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
      proc_priv_bare pj pidv Vpr -∗
      inode_held (pv_cwd Vpr) -∗
      ([∗ list] i ∈ seq 0 (S plen), pa_add pv i ↦ₘ[KT1]{dqpv} pfun i) -∗
      bslots 3 -∗
      (* the set only GROWS; namex takes no credit and neither does
         this wrapper, so the counter clause is untouched *)
      ⌜Sb ⊆ Sb'⌝ -∗
      (* the walk's paid-bitmap report and the membership that makes it an
         honest read (fs-log.md §G.24), namex's verbatim *)
      ⌜w = true -> bmapstart ∈ Sb'⌝ -∗
      ⌜((n - (walk_spend w + (if ok then 0%nat else 1%nat)))%nat <= n')%nat
       /\ (n' <= n)%nat⌝ -∗
      (* the set form beside the transaction's token (B''-tx) *)
      log_opSt g n' Sb' -∗
      (if ok
       then ⌜mf !!! Regidx (mword_of_int 10 : mword 5) = ipv⌝ ∗
            inode_held ipv ∗
            iref_slots 1
       else ⌜mf !!! Regidx (mword_of_int 10 : mword 5)
             = (mword_of_int 0 : mword 64)⌝ ∗
            iref_slots 2) -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type NAMEI.
  Parameter wp_namei_sconf :
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
      (n : nat)
      (pidv : mword 32) (dq dqb dqs dqpv : dfrac)
      (m : regfile) (K : nat) (eb : bool)
      (b : bool) (lks : gset string) (Vpr : pprivate),
      wp_namei_sconf_body gs j gl gu gd gk pd pav pu bn g gi gtl
                          ga gf cov logstart bmapstart inodestart nib
                          size dev plen pfun n
                          pidv dq dqb dqs dqpv m K eb b lks Vpr.
  (* the set-form contract; the counted one is this at the [log_op]
     existential's own witness. *)
  Parameter wp_namei_gen :
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
      (n : nat) (Sb : gset Z)
      (pidv : mword 32) (dq dqb dqs dqpv : dfrac)
      (m : regfile) (K : nat) (eb : bool)
      (b : bool) (lks : gset string) (Vpr : pprivate),
      wp_namei_gen_body gs j gl gu gd gk pd pav pu bn g gi gtl
                          ga gf cov logstart bmapstart inodestart nib
                          size dev plen pfun n Sb
                          pidv dq dqb dqs dqpv m K eb b lks Vpr.
End NAMEI.

(* ===================================================================== *)
(*  THE ROOT CORNER: [namei("/")].                                        *)
(*                                                                        *)
(*  A thin forward of [SpecNamex.wp_namex_root] -- namei's whole body is a *)
(*  namex call -- and the regime is that contract's: no running process,   *)
(*  no transaction, no file-system fabric beyond the inode cache, and any  *)
(*  [eb] / [b].  See [SpecNamex.wp_namex_root_body]'s header for WHY there *)
(*  are two contracts rather than one.                                    *)
(*                                                                        *)
(*  THE NAME BUFFER DOES NOT APPEAR, and here it is not even carved: the   *)
(*  general proof carves the frame's two low slots into [name[14]] because *)
(*  namex's memmoves write it, and on this path no memmove runs.  So the   *)
(*  four frame slots stay four stack slots from the push to the pop.       *)
(* ===================================================================== *)

(* namei's own frame is 32 bytes (4 slots) over the corner's 28. *)
Notation K_namei_root := (74%nat) (only parsing).
Definition wp_namei_root_body
    `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, ICFG : icfg, FSC : fscfg,
      !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId}
    (gtl : gname) (gi : gname)
    (cov : gset Z) (logstart : Z) (inodestart : Z) (nib : nat) (dev : mword 32)
    (dqp : dfrac)
    (m : regfile) (n K : nat) (eb : bool) (p : mword 64)
    (b : bool) (lks : gset string) (Vpr : pprivate) :=
  let pcE : mword 64 := mword_of_int KernelSyms.namei in
  let pv := m !!! Regidx (mword_of_int 10 : mword 5) in    (* a0 = path *)
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  (K_namei_root <= K)%nat ->
  (* [+3], not [+1]: namex's iget acquires itable.lock and its LIVE panic
     arm fires inside that critical section, where printk takes two more. *)
  (Z.of_nat n + 3 < 2 ^ 31)%Z ->
  dev = icfg_dev ->
  nib = icfg_nib ->
  dev = ROOTDEV ->
  (0 < nib)%nat ->
  locks_below lks "itable" ->
  sie_cap_gpr KT1 m K b p -∗
  cpu_own n eb p b lks -∗
  kernel_text -∗ kernel_data -∗ pc_is pcE -∗
  panic_env -∗
  is_itable2 gtl fsc_ic fsc_fs gi cov logstart nib dev -∗
  itable_inv -∗
  ic_escrows fsc_ic fsc_fs gi cov logstart -∗
  (* the inode region -- iget's premise since iclaim-ledger.md §3.3, and
     GHOST-ONLY there (the recycle arm's peel and its 0 -> 1 count move).
     Persistent, relayed unchanged. *)
  ireg_reg gi fsc_fs inodestart nib -∗
  (* ...AND NOT [ireg_open]: the corner's regime premise is gone, forwarded
     from [SpecNamex.wp_namex_root_body], whose header says why.  The short
     version: [ireg_open] does not exist until fsinit's [ireg_boot] is shot,
     and userinit -- this corner's whole reason for existing -- runs before
     fsinit. *)
  iref_slot -∗
  pa_add pv 0 ↦ₘ{dqp} SLASH -∗
  pa_add pv 1 ↦ₘ{dqp} NUL -∗
  wp_next b p (fun (CID : CpuId) =>
    ∀ (mr : regfile) (ipv : mword 64),
      ⌜ callee_saved m mr
        /\ mr !!! Regidx (mword_of_int 10 : mword 5) = ipv ⌝ -∗
      sie_cap_gpr KT1 mr K b p -∗
      cpu_own n eb p b lks -∗
      pc_is ret_tgt -∗
      pa_add pv 0 ↦ₘ{dqp} SLASH -∗
      pa_add pv 1 ↦ₘ{dqp} NUL -∗
      inode_held ipv -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type NAMEI_ROOT.
  Parameter wp_namei_root :
    forall `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, ICFG : icfg, FSC : fscfg,
             !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId}
      (gtl : gname) (gi : gname)
      (cov : gset Z) (logstart : Z) (inodestart : Z) (nib : nat) (dev : mword 32)
      (dqp : dfrac)
      (m : regfile) (n K : nat) (eb : bool) (p : mword 64)
      (b : bool) (lks : gset string) (Vpr : pprivate),
      wp_namei_root_body gtl gi cov logstart inodestart nib dev dqp
                         m n K eb p b lks Vpr.
End NAMEI_ROOT.
