(* SpecHoldingsleep.v -- the public interface of Holdingsleep, stated
   independently of its proof.  Requires only the definitional layer --
   never a whole-function proof file -- so every function proof can be
   checked in parallel.

   The HOLDER's variant (the only one xv6 uses -- every call site asserts
   the lock is held): with the token, the pid field the holder carries, and
   the caller's own pid cell agreeing on the value, holdingsleep returns 1.

     { is_sleeplock γl γ slk s R ∗ sleeplocked γ slk pidv
       ∗ cur_proc p ∗ proc_priv_bare p pidv V ∗ <cells> }
       holdingsleep(slk)
     { a0 = 1 ∗ (everything back) }

   The v = 0 arm inside the inner critical section is refuted by token
   exclusivity ([sl_res_open_held]); the pid comparison closes from the
   agreement of the two pid resources.  Calls myproc().  (tp holds this hart's id by construction now --
   HartTp.tp_pin -- so no contract states it.) *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import InstrBytes.
Require Import RegFile WpNext.
Require Import RiscvExtras.
Require Import CalleeSaved KernelText.
Require Import IntrDefs.
Require Import LockRank.
Require Import CpuOwn.
Require Import ProcDefs.  (* [proc_priv_bare] -- file-layer free *)
Require Import SleepLock.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Import Defs.


(* THE GENERAL FORM, over the sleeplock's holder DEPOSIT [H] (SleepLock.v).
   holdingsleep only PEEKS: it opens the held arm to read the pid, puts the
   deposit straight back and re-closes, so [H] appears nowhere but in the
   lock predicate -- and [wp_holdingsleep_sconf_body] below is literally this
   at the untracked instance. *)
Definition wp_holdingsleep_gen_sconf_body `{!riscvGS Σ, !xv6G Σ} `{GEN : GenId} `{CID : CpuId}
    (γl γsl : gname) (s : string) (R : iProp Σ) (H : Qp -> iProp Σ) (q : Qp)
    (m : regfile) (p : mword 64) (pidv : mword 32) (av : nat) (eb : bool) (b : bool) (lks : gset string) (Vpr : pprivate) :=
  let pcE : mword 64 := mword_of_int KernelSyms.holdingsleep in
  let slk := m !!! Regidx (mword_of_int 10 : mword 5) in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5))
                   in
  (16 <= av)%nat ->
  (* THE FRESHNESS PREMISE: holdingsleep acquires and releases the
     sleeplock's inner "sleep lock" spinlock internally (balanced -- [lks]
     is unchanged across the whole call), so the caller must already hold
     only locks BELOW "sleep lock"'s rank. *)
  locks_below lks "sleep lock" ->
  sie_cap_gpr KT1 m av b p -∗
  cpu_own 0 eb p b lks -∗
  kernel_text -∗ pc_is pcE -∗
  is_sleeplock_gen γl γsl slk s R H -∗
  (* the holder's bundle (returned untouched) *)
  sleeplocked_q γsl q slk pidv -∗
  (* the caller's own pid, agreeing with the lock's pid field *)
  proc_priv_bare p pidv Vpr -∗
  wp_next b p (fun (CID : CpuId) =>
    ∀ mf : regfile,
      ⌜ callee_saved m mf /\
        mf !!! Regidx (mword_of_int 10 : mword 5) = (mword_of_int 1 : mword 64) ⌝ -∗
      sie_cap_gpr KT1 mf av b p -∗
      cpu_own 0 eb p b lks -∗
      pc_is ret_tgt -∗
      sleeplocked_q γsl q slk pidv -∗
      proc_priv_bare p pidv Vpr -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

(* the UNTRACKED instance, and the fraction-free token with it: every
   existing caller (brelse, bwrite) says [sleeplocked] and knows no [q]. *)
Definition wp_holdingsleep_sconf_body `{!riscvGS Σ, !xv6G Σ} `{GEN : GenId} `{CID : CpuId}
    (γl γsl : gname) (s : string) (R : iProp Σ)
    (m : regfile) (p : mword 64) (pidv : mword 32) (av : nat) (eb : bool) (b : bool) (lks : gset string) (Vpr : pprivate) :=
  let pcE : mword 64 := mword_of_int KernelSyms.holdingsleep in
  let slk := m !!! Regidx (mword_of_int 10 : mword 5) in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5))
                   in
  (16 <= av)%nat ->
  locks_below lks "sleep lock" ->
  sie_cap_gpr KT1 m av b p -∗
  cpu_own 0 eb p b lks -∗
  kernel_text -∗ pc_is pcE -∗
  is_sleeplock γl γsl slk s R -∗
  sleeplocked γsl slk pidv -∗
  proc_priv_bare p pidv Vpr -∗
  wp_next b p (fun (CID : CpuId) =>
    ∀ mf : regfile,
      ⌜ callee_saved m mf /\
        mf !!! Regidx (mword_of_int 10 : mword 5) = (mword_of_int 1 : mword 64) ⌝ -∗
      sie_cap_gpr KT1 mf av b p -∗
      cpu_own 0 eb p b lks -∗
      pc_is ret_tgt -∗
      sleeplocked γsl slk pidv -∗
      proc_priv_bare p pidv Vpr -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type HOLDINGSLEEP.
  Parameter wp_holdingsleep_gen_sconf :
    forall `{!riscvGS Σ, !xv6G Σ} `{GEN : GenId} `{CID : CpuId} (γl γsl : gname) (s : string) (R : iProp Σ) (H : Qp -> iProp Σ) (q : Qp)
      (m : regfile) (p : mword 64) (pidv : mword 32) (av : nat) (eb : bool) (b : bool) (lks : gset string) (Vpr : pprivate),
      wp_holdingsleep_gen_sconf_body γl γsl s R H q m p pidv av eb b lks Vpr.
  Parameter wp_holdingsleep_sconf :
    forall `{!riscvGS Σ, !xv6G Σ} `{GEN : GenId} `{CID : CpuId} (γl γsl : gname) (s : string) (R : iProp Σ)
      (m : regfile) (p : mword 64) (pidv : mword 32) (av : nat) (eb : bool) (b : bool) (lks : gset string) (Vpr : pprivate),
      wp_holdingsleep_sconf_body γl γsl s R m p pidv av eb b lks Vpr.
End HOLDINGSLEEP.
