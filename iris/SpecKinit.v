(* SpecKinit.v -- the public interface of Kinit, stated independently of its
   proof.  Requires only the definitional layer -- never a whole-function proof
   file -- so every function proof can be checked in parallel. *)
From Stdlib Require Import Eqdep_dec ZArith Lia List.
From stdpp Require Import gmap list list_monad bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import excl.
From iris.base_logic.lib Require Import ghost_var gen_heap invariants own.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import RegFile.
Require Import InstrBytes.
Require Import RiscvExtras.
Require Import CalleeSaved.
Require Import KernelText KernelDataInv.
Require Import WpLock.
(* [lock_free_tok] -- the caller-minted lock ghost this contract now fills *)
Require Import WpLockAt.
Require Import KallocInv.
Require Import IntrDefs WpNext.
Require Import CpuOwn.
Require Import SpecFreerange.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)


(* THE TWO GHOST NAMES ARE THE CALLER'S (fs-cfg-boot.md stage (e), debt E).
   [γl] is the "kmem" spinlock's own gname and [γk] the free-list count/seal
   pair its resource is keyed by; both used to be chosen HERE, by an
   [own_alloc] and a [WpLock.newlock] at WP time, and returned
   existentially.  They cannot be: [FsCfg.fscfg] carries them as
   [fsc_kalloc] / [fsc_kpages] -- because [FsReady.fs_ready] has to SPELL
   the allocator's lock and its sealed count, and a holder of an
   existential can never show its own name equal to a field -- and a field
   has to have a value before the boot fupd ends.  So this contract now
   FILLS names it is given, exactly as [WpLockAt.newlock_at],
   [BioInitAt.bio_init_at] and [IcacheBoot.icache_boot_at] do.  The three
   premises below are what the era fupd hands over
   ([FsCfgBoot.fs_kit_icache]'s last three rows). *)
Definition wp_kinit_sconf_body `{!riscvGS Σ, !xv6G Σ} `{GEN : GenId} `{CID : CpuId} (γl : gname) (γk : gname * gname) (m : regfile) (ps : list (mword 64)) (K ncnt : nat) (eb : bool) (pcur : mword 64) (vlock : bv 32) (vname vcpu : bv 64) (b : bool) (lks : gset string) :=
  let pcE : mword 64 := mword_of_int KernelSyms.kinit in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5) : mword 64) in
  let lk : mword 64 := mword_of_int KernelSyms.kmem in
  let fl : mword 64 := mword_of_int (KernelSyms.kmem + 24) in
  let c_name := lock_name_field lk in
  let c_cpu := add_vec lk (sign_extend' 64 (mword_of_int 16 : mword 12)) in
  let endaddr : mword 64 := mword_of_int KernelSyms.end_ in
  let phystop : mword 64 := mword_of_int 0x88000000 in
  let s1entry := add_vec (and_vec (add_vec endaddr (mword_of_int 4095 : mword 64)) negPGSIZEv) PGSIZEv in
  (22 <= K)%nat ->
  ncnt = 0%nat ->
  prun phystop s1entry ps ->
  (* kinit -> freerange -> kfree -> acquire(kmem.lock), rank 13 *)
  locks_below lks "kmem" ->
  sie_cap_gpr KT0 m K b pcur -∗
  cpu_own ncnt eb pcur b lks -∗
  (* [kernel_data] supplies the "kmem" string literal kinit's [auipc a1 /
     addi a1] points at -- the name it hands to initlock. *)
  kernel_text -∗ kernel_data -∗ pc_is pcE -∗
  (* freerange -> kfree -> acquire sits above panic() *)
  lk ↦₄ vlock -∗
  c_name ↦₈ vname -∗
  c_cpu ↦₈ vcpu -∗
  fl ↦₈ (mword_of_int 0 : mword 64) -∗
  ([∗ list] p ∈ ps, page_own p) -∗
  (* the "kmem" lock's ghost, unbuilt: [WpLockAt.lock_ghost_alloc]'s pair at
     [None].  What [WpLockAt.newlock_at] fills. *)
  lock_free_tok γl -∗
  (* the free-list count at GENESIS -- zero pages -- in both halves.  The
     [ghost_var] pair [KallocInv.kalloc_avail_alloc] used to mint here. *)
  kalloc_avail γk (Some 0%nat) -∗
  kmem_avail_auth γk 0%nat -∗
  wp_next b pcur (fun (CID : CpuId) =>
    ∀ (mr : regfile),
    sie_cap_gpr KT0 mr K b pcur -∗
    cpu_own ncnt eb pcur b lks -∗
    pc_is ret_tgt -∗
    ⌜ callee_saved m mr ⌝ -∗
    is_kmem γl γk lk fl -∗
    kalloc_avail γk (Some (length ps)) -∗
    WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type KINIT.
  Parameter wp_kinit_sconf :
    forall `{!riscvGS Σ, !xv6G Σ} `{GEN : GenId} `{CID : CpuId} (γl : gname) (γk : gname * gname) (m : regfile) (ps : list (mword 64)) (K ncnt : nat) (eb : bool) (pcur : mword 64) (vlock : bv 32) (vname vcpu : bv 64) (b : bool) (lks : gset string),
      wp_kinit_sconf_body γl γk m ps K ncnt eb pcur vlock vname vcpu b lks.
End KINIT.
