(* SpecFreerange.v -- the public interface of Freerange, stated independently of its
   proof.  Requires only the definitional layer -- never a whole-function proof
   file -- so every function proof can be checked in parallel. *)
From Stdlib Require Import Eqdep_dec ZArith Lia List.
From stdpp Require Import gmap list list_monad bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import excl.
From iris.base_logic.lib Require Import ghost_var gen_heap invariants.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import InstrBytes.
Require Import RegFile WpNext.
Require Import SmodeCore.
Require Import CalleeSaved.
Require Import KernelText.
Require Import WpLock.
Require Import KallocInv.
Require Import IntrDefs.
Require Import CpuOwn.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.


Definition PGSIZEv : mword 64 := mword_of_int 4096.
Definition negPGSIZEv : mword 64 := mword_of_int (-4096).   (* the ~0xfff page mask *)

(* [avail_inc] applied [k] times -- the page-count token after freeing [k]
   pages.  freerange starts at [Some 0] and ends at [Some (length ps)]. *)
Fixpoint avail_inc_n (on : option nat) (k : nat) : option nat :=
  match k with O => on | S k' => avail_inc (avail_inc_n on k') end.
Fixpoint prun (pa_end s1 : mword 64) (ps : list (mword 64)) : Prop :=
  match ps with
  | [] => zopz0zI_u pa_end s1 = true
  | p :: rest =>
      zopz0zI_u pa_end s1 = false
      /\ p = add_vec s1 negPGSIZEv
      /\ page_valid p
      /\ prun pa_end (add_vec s1 PGSIZEv) rest
  end.

Definition wp_freerange_sconf_body `{!riscvGS Σ, !lockG Σ, !sieG Σ, !kallocG Σ} `{GEN : GenId} `{CID : CpuId} (γl : gname) (γk : gname * gname) (lk fl : mword 64) (m : regfile) (ps : list (mword 64)) (K ncnt : nat) (eb : bool) (pcur : mword 64) (b : bool) (lks : gset string) :=
  let pcE : mword 64 := mword_of_int KernelSyms.freerange in
  let pa_start := m !!! Regidx (mword_of_int 10 : mword 5) in
  let pa_end := m !!! Regidx (mword_of_int 11 : mword 5) in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5) : mword 64) in
  let s1entry := add_vec (and_vec (add_vec pa_start (mword_of_int 4095 : mword 64)) negPGSIZEv) PGSIZEv in
  (20 <= K)%nat ->
  ncnt = 0%nat ->
  lk = mword_of_int KernelSyms.kmem ->
  fl = mword_of_int (KernelSyms.kmem + 24) ->
  prun pa_end s1entry ps ->
  (* THE FRESHNESS PREMISE: freerange's loop acquires and releases
     [kmem.lock] once per page (balanced -- [lks] is unchanged), so the
     caller must already hold only locks BELOW "kmem"'s rank. *)
  locks_below lks "kmem" ->
  sie_cap_gpr m K b pcur -∗
  cpu_own ncnt eb pcur b lks -∗
  kernel_text -∗ pc_is pcE -∗
  is_lock γl lk "kmem"%string (kmem_res γk fl) -∗
  ([∗ list] p ∈ ps, page_own p) -∗
  kalloc_avail γk (Some 0%nat) -∗
  wp_next b pcur (fun (CID : CpuId) =>
    ∀ mr,
    sie_cap_gpr mr K b pcur -∗
    cpu_own ncnt eb pcur b lks -∗
    pc_is ret_tgt -∗
    ⌜ callee_saved m mr ⌝ -∗
    kalloc_avail γk (Some (length ps)) -∗
    WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type FREERANGE.
  Parameter wp_freerange_sconf :
    forall `{!riscvGS Σ, !lockG Σ, !sieG Σ, !kallocG Σ} `{GEN : GenId} `{CID : CpuId} (γl : gname) (γk : gname * gname) (lk fl : mword 64) (m : regfile) (ps : list (mword 64)) (K ncnt : nat) (eb : bool) (pcur : mword 64) (b : bool) (lks : gset string),
      wp_freerange_sconf_body γl γk lk fl m ps K ncnt eb pcur b lks.
End FREERANGE.
