(* SpecHolding.v -- the public interface of Holding, stated independently of its
   proof.  Requires only the definitional layer -- never a whole-function proof
   file -- so every function proof can be checked in parallel.

   holding(lk) reads BOTH of the lock's words, and both belong to the lock
   invariant (WpLock.v), so the caller passes no [lk->cpu] cell.  Two forms:

     - with no evidence, the answer is unknown: 0 or 1 (a non-holder cannot
       see the owner word, so this is all that is true).  acquire calls
       holding() this way and absorbs the 1 answer with panic's contract.
     - with the [locked] holder token, the answer is provably 1 (the token
       pins [lk->cpu] at this hart's [struct cpu]); the token comes back out.
       That is release's check.

   Both are stated over [lock_openable] (WpLock.v) rather than [is_lock], so
   they work for a lock whose storage can be reclaimed.  What each open
   presents is a credential that refutes the dead state [Dc]: for the
   evidence-free form that is the caller's own [Tc] (a reference to the
   object), and for the [locked] form it is the holder token itself -- which
   is all a caller has left once the object's last reference has gone home.
   holding() never disposes of anything, so [Dc] only rides along; a static
   kernel lock takes [Dc := False] and [lock_refute_False]. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import RegFile.
Require Import InstrBytes.
Require Import SmodeCore.
Require Import CalleeSaved KernelText.
Require Import IntrDefs.
Require Import IntrDefs.
Require Import WpLock.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Import Defs.


(* INTERRUPTS MUST BE DISABLED at holding() -- it [jal mycpu]s at +0x16, and
   [mycpu]'s own contract (SpecMycpu.v) is stated at the LITERAL [b = false]
   (its [tp] read happens mid-body, so a [b]-generic caller could not even
   supply a matching [sie_cap_gpr _ _ b] to it).  Stating this contract at
   [false] directly -- with no [wp_next] wrapper at all, since it collapses
   by [wp_next_off] anyway -- is sound: holding() is only ever called from
   acquire()/release(), both of which have already called push_off().  It
   also makes the holder token's hart identity track a SINGLE ambient [CID]
   throughout the body (no migrated-hart mismatch can arise at the +0x12
   [lk->cpu] read below). *)
Definition wp_holding_lockinv_s_sconf_body `{!riscvGS Σ, !sieG Σ, !lockG Σ} `{GEN : GenId} `{CID : CpuId} (γl : gname) (lka : mword 64) (s : string) (R Tc Dc : iProp Σ) (m : regfile) (n : nat) (p : mword 64) :=
  let pcE : mword 64 := mword_of_int KernelSyms.holding in
  let lk := m !!! Regidx (mword_of_int 10 : mword 5) in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  add_vec lk (sign_extend' 64 (mword_of_int 0 : mword 12)) = lka ->
  (6 <= n)%nat ->
  (⊢ Tc -∗ Dc -∗ False) ->
  sie_cap_gpr m n false p -∗
  kernel_text -∗ pc_is pcE -∗
  lock_openable γl lka s R Dc -∗
  Tc -∗
  ( ∀ mh,
    Tc -∗
    sie_cap_gpr mh n false p -∗
    pc_is ret_tgt -∗
    ⌜ callee_saved m mh /\
      (mh !!! Regidx (mword_of_int 10 : mword 5) = (mword_of_int 0 : mword 64) \/
       mh !!! Regidx (mword_of_int 10 : mword 5) = (mword_of_int 1 : mword 64)) ⌝ -∗
    WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

(* INTERRUPTS MUST BE DISABLED -- see the note above [wp_holding_lockinv_s_sconf_body];
   the same [jal mycpu] at +0x16 forces this contract to [b = false] too, with
   no [wp_next] wrapper (it collapses by [wp_next_off]).  Stated at literal
   [false] the whole body runs on the ONE ambient hart, so [held_cpu] names
   the SAME identity throughout -- including at the +0x12 [lk->cpu] read,
   where a [b]-generic statement would otherwise hand that leaf a token about
   the entry hart while it demands one about its own (post-migration)
   ambient hart. *)
Definition wp_holding_lockinv_locked_s_sconf_body `{!riscvGS Σ, !sieG Σ, !lockG Σ} `{GEN : GenId} `{CID : CpuId} (γl : gname) (lka : mword 64) (s : string) (R Dc : iProp Σ) (m : regfile) (n : nat) (p : mword 64) :=
  let pcE : mword 64 := mword_of_int KernelSyms.holding in
  let lk := m !!! Regidx (mword_of_int 10 : mword 5) in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  (* the holder token is about a FIXED cpu identity -- the one recorded at
     acquire time -- which, at [b = false], is the SAME as the ambient
     [cpu_id] throughout this body (no hart ever moves). *)
  let held_cpu := cpu_id in
  add_vec lk (sign_extend' 64 (mword_of_int 0 : mword 12)) = lka ->
  (6 <= n)%nat ->
  (⊢ locked γl held_cpu -∗ Dc -∗ False) ->
  sie_cap_gpr m n false p -∗
  kernel_text -∗ pc_is pcE -∗
  lock_openable γl lka s R Dc -∗
  locked γl held_cpu -∗
  ( ∀ mh,
    sie_cap_gpr mh n false p -∗
    pc_is ret_tgt -∗
    ⌜ callee_saved m mh /\
      mh !!! Regidx (mword_of_int 10 : mword 5) = (mword_of_int 1 : mword 64) ⌝ -∗
    locked γl held_cpu -∗
    WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type HOLDING.
  Parameter wp_holding_lockinv_s_sconf :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ} `{GEN : GenId} `{CID : CpuId} (γl : gname) (lka : mword 64) (s : string) (R Tc Dc : iProp Σ) (m : regfile) (n : nat) (p : mword 64),
      wp_holding_lockinv_s_sconf_body γl lka s R Tc Dc m n p.
  Parameter wp_holding_lockinv_locked_s_sconf :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ} `{GEN : GenId} `{CID : CpuId} (γl : gname) (lka : mword 64) (s : string) (R Dc : iProp Σ) (m : regfile) (n : nat) (p : mword 64),
      wp_holding_lockinv_locked_s_sconf_body γl lka s R Dc m n p.
End HOLDING.
