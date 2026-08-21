(* SpecWalk.v -- the public interface of Walk, stated independently of its
   proof.  Requires only the definitional layer -- never a whole-function proof
   file -- so every function proof can be checked in parallel. *)
From Stdlib Require Import Eqdep_dec ZArith Lia List.
From stdpp Require Import gmap list list_monad bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import excl.
From iris.base_logic.lib Require Import ghost_var gen_heap invariants.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import RiscvExtras.
Require Import InstrBytes.
Require Import KernelText.
Require Import RegFile HartTp WpNext.
Require Import RiscvExtras.
Require Import CalleeSaved.
Require Import KallocInv.
Require Import LockRank.
Require Import PtTree.
Require Import PtBuild KvmSpec.
Require Import IntrDefs.
Require Import CpuOwn.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Import Defs.


Definition wp_walk_sconf_body `{!riscvGS Σ, !xv6G Σ} `{GEN : GenId} `{CID : CpuId}
    (kt : ktier) (γa : gname) (γk : gname * gname) (mm : regfile) (t : ptree) (m : gmap (mword 27) (mword 64)) (K : nat) (lvl : nat) (eb : bool) (p : mword 64) (on : option nat) (b : bool) (lks : gset string) :=
  let va := mm !!! Regidx (mword_of_int 11) in
  let vpn := svpn_of va in
  let ret_tgt := ret_pc (mm !!! Regidx (mword_of_int 1)) in
  (* the kalloc chain below keeps its transient noff increment in int
     range; [lvl] is otherwise generic (the identity pin this replaced was
     an artifact of the boot-time callers) *)
  (Z.of_nat lvl + 1 < 2 ^ 31)%Z ->
  (22 <= K)%nat ->
  mm !!! Regidx (mword_of_int 10)
    = zero_extend' 64 (concat_vec (pt_base t) (zeros' 12 : mword 12)) ->
  mm !!! Regidx (mword_of_int 12) = mword_of_int 1 ->
  (uint va < 2 ^ 38)%Z ->
  pt_rep0 t m ->
  (* the kvm chain runs on the ambient CPU: kalloc's push/pop addresses
     this cpu's cells through tp *)
  mm !!! Regidx (mword_of_int 4 : mword 5) = cid_word ->
  (* walk allocates a fresh page-table node (via kalloc) whenever the
     descent finds an empty slot; kalloc's own bound is "kmem" (13), and
     nothing else in walk's cone touches a lock.  One premise covers the
     whole cone. *)
  locks_below lks "kmem" ->
  sie_cap_gpr kt mm K b p -∗ cpu_own lvl eb p b lks -∗
  kernel_text -∗
  pc_is (mword_of_int KernelSyms.walk) -∗
  ptree_own 2 (DfracOwn 1) t -∗
  kalloc_env_at γa γk on -∗
  wp_next b p (fun (CID : CpuId) =>
    ∀ (mr : regfile) (t' : ptree) (g : nat),
    sie_cap_gpr kt mr K b p -∗ cpu_own lvl eb p b lks -∗
    pc_is ret_tgt -∗
    ptree_own 2 (DfracOwn 1) t' -∗
    ⌜pt_nodes t' = (pt_nodes t + g)%nat⌝ -∗
    kalloc_env_at γa γk (avail_sub on g) -∗
    ⌜callee_saved mm mr⌝ -∗
    ⌜ptree_same_rep0 t t'⌝ -∗
    ⌜ptree_offpath_eq vpn t t'⌝ -∗
    ⌜pt_present_mono t t'⌝ -∗
    ⌜(g <= pt_missing t vpn 1)%nat⌝ -∗
    ⌜ (mr !!! Regidx (mword_of_int 10) = mword_of_int 0
         /\ avail_zero (avail_sub on g))
      \/ (exists p2 p1 w0,
           ptree_level0 t' vpn p2 p1 w0 /\
           mr !!! Regidx (mword_of_int 10) = pt_addr0 p1 vpn) ⌝ -∗
    WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type WALK.
  Parameter wp_walk_sconf :
    forall `{!riscvGS Σ, !xv6G Σ} (kt : ktier) `{GEN : GenId} `{CID : CpuId}
      (γa : gname) (γk : gname * gname) (mm : regfile) (t : ptree) (m : gmap (mword 27) (mword 64)) (K : nat) (lvl : nat) (eb : bool) (p : mword 64) (on : option nat) (b : bool) (lks : gset string),
      wp_walk_sconf_body kt γa γk mm t m K lvl eb p on b lks.
End WALK.

(* --------------------------------------------------------------------- *)
(* walk with alloc = 0 (ismapped's callee): a READ-ONLY descent.  The     *)
(* kalloc branch is short-circuited (`!alloc || ...`) so there is no      *)
(* kalloc_env, no cpu_own and no panic contract (the va >= MAXVA panic    *)
(* arm is dead under the canonicality premise), and the tree is taken at  *)
(* a GENERIC dfrac and returned UNCHANGED.  The result is decided by the  *)
(* represented map: a vpn blocked at L2/L1 returns 0; a path that reaches *)
(* level 0 returns that slot's address -- with the slot's current word    *)
(* either the map's leaf (mapped) or the literal zero (unmapped).         *)
(* --------------------------------------------------------------------- *)

Definition wp_walk_noalloc_sconf_body `{!riscvGS Σ, !xv6G Σ} `{GEN : GenId} `{CID : CpuId} (kt : ktier) (mm : regfile) (t : ptree)
    (m : gmap (mword 27) (mword 64)) (K : nat) (dq : dfrac) (b : bool) (p : mword 64) :=
  let pcE : mword 64 := mword_of_int KernelSyms.walk in
  let va := mm !!! Regidx (mword_of_int 11) in
  let vpn := svpn_of va in
  let ret_tgt := ret_pc (mm !!! Regidx (mword_of_int 1)) in
  (8 <= K)%nat ->
  mm !!! Regidx (mword_of_int 10)
    = zero_extend' 64 (concat_vec (pt_base t) (zeros' 12 : mword 12)) ->
  mm !!! Regidx (mword_of_int 12) = mword_of_int 0 ->
  (uint va < 2 ^ 38)%Z ->
  pt_rep0 t m ->
  sie_cap_gpr kt mm K b p -∗
  kernel_text -∗
  pc_is pcE -∗
  ptree_own 2 dq t -∗
  wp_next b p (fun (CID : CpuId) =>
    ∀ (mr : regfile),
    sie_cap_gpr kt mr K b p -∗
    pc_is ret_tgt -∗
    ptree_own 2 dq t -∗
    ⌜callee_saved mm mr⌝ -∗
    ⌜ (mr !!! Regidx (mword_of_int 10) = mword_of_int 0 /\ m !! vpn = None)
      \/ (exists p2 p1 w0,
           ptree_level0 t vpn p2 p1 w0 /\
           mr !!! Regidx (mword_of_int 10) = pt_addr0 p1 vpn /\
           (m !! vpn = Some w0
            \/ (w0 = mword_of_int 0 /\ m !! vpn = None))) ⌝ -∗
    WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type WALK_NOALLOC.
  Parameter wp_walk_noalloc_sconf :
    forall `{!riscvGS Σ, !xv6G Σ} `{GEN : GenId} `{CID : CpuId} (kt : ktier) (mm : regfile) (t : ptree)
      (m : gmap (mword 27) (mword 64)) (K : nat) (dq : dfrac) (b : bool) (p : mword 64),
      wp_walk_noalloc_sconf_body kt mm t m K dq b p.
End WALK_NOALLOC.
