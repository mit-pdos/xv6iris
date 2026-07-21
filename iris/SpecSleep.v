(* SpecSleep.v -- the ASSUMED contract of sleep(chan, lk), the classic
   condition-variable wait over a held spinlock:

     { is_lock γl lk s R ∗ locked γl ∗ R ∗ <running-thread bundle> }
       sleep(chan, lk)
     { locked γl ∗ R ∗ <running-thread bundle> }

   sleep releases lk, parks the process (state SLEEPING, sched()), and
   re-acquires lk before returning -- so the caller surrenders the lock's
   resource R and receives a FRESH R back with the token.  Its proof is
   future work (it needs the scheduler protocol end-to-end: it acquires
   p->lock, parks through sched, and is redispatched); like the old myproc
   axiom this contract is deliberately ASSUMED, stated at the shape the
   eventual proof must have:

   - entered holding EXACTLY the one spinlock lk (intr_count 1, noff cell 1,
     lk's cpu word = this cpu) -- xv6's "sched locks" assertion forces this;
   - the running-thread bundle of the scheduler protocol (SchedCtx.v /
     SpecSched.v): cur_proc at proc j, proc j's own lock free (sleep
     acquires it), the process's own context-field cells, and the parked
     scheduler's ▷-guarded valid context, plus procs_inv;
   - tp = cid_word (sleep calls myproc; the bundle's cells live at the
     ambient hart id);
   - everything comes back unchanged (callee_saved, the bundle re-formed,
     lk re-held with a fresh R). *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExtras.
Require Import WpGpr InstrBytes WpMmodeLeafBase.
Require Import RegFile.
Require Import SmodeCore.
Require Import KptTree.
Require Import StackOwn CalleeSaved KernelText.
Require Import IntrDefs.
Require Import WpLock.
Require Import WpMycpu.
Require Import ProcGeom.
Require Import SwtchCtx.
Require Import SchedCtx.
Require Import SpecSched.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Import Defs.

Notation SLP := KernelSyms.sleep.

Definition wp_sleep_sconf_body `{!riscvGS Σ, !sieG Σ, !lockG Σ} `{CID : CpuId}
    (γ : gname) (root_ppn : mword 44) (Φ : mval -> iProp Σ)
    (γs : list gname) (j : nat)
    (γl : gname) (lka : mword 64) (s : string) (R : iProp Σ)
    (m : regfile) (av : nat) :=
  let pcE : mword 64 := mword_of_int KernelSyms.sleep in
  let lk0 := m !!! Regidx (mword_of_int 11 : mword 5) in
  let a_cpu := add_vec lk0 (sign_extend' 64 (mword_of_int 16 : mword 12)) in
  let cpuv := mycpu_ret cid_word in
  let pj := proc_addr j in
  let ret_tgt := update_vec_dec (add_vec (m !!! Regidx (mword_of_int 1 : mword 5))
                   (sign_extend' 64 (zeros' 12))) 0 ('b"0") in
  (* release's lock-word address form for the held lock lk0 = a1 *)
  add_vec lk0 (sign_extend' 64 (mword_of_int 0 : mword 12)) = lka ->
  (* the hart id is the ambient CpuId *)
  m !!! Regidx (mword_of_int 4 : mword 5) = cid_word ->
  (j < NPROC)%nat ->
  eq_vec (access_vec_dec ret_tgt 0) ('b"0") = true ->
  (22 <= av)%nat ->
  sconf γ -∗
  hart_state ↦ᵣ HART_ACTIVE tt -∗
  sie_cap_gpr γ root_ppn m av -∗
  intr_count γ root_ppn 1 -∗
  tlb_inv_pt root_ppn -∗
  kernel_text -∗ pc_is pcE -∗
  (* the held condition lock *)
  is_lock γl lka s R -∗
  locked γl -∗
  R -∗
  a_cpu ↦₈ cpuv -∗
  (* per-cpu push_off cells: exactly one level outstanding *)
  a_cpu_noff cid_word ↦₄ (mword_of_int 1 : mword 32) -∗
  (∃ iv : mword 32, a_cpu_int cid_word ↦₄ iv) -∗
  (* the running-thread bundle of the scheduler protocol *)
  cur_proc pj -∗
  p_lkcpu pj ↦₈ (zero_reg : mword 64) -∗
  procs_inv γ root_ppn Φ γs -∗
  own_ctx (p_context pj) -∗
  ▷ sched_vc γ root_ppn Φ γs (a_cpu_ctx cid_word) -∗
  ( ∀ mf : regfile,
      ⌜ callee_saved m mf ⌝ -∗
      sconf γ -∗
      hart_state ↦ᵣ HART_ACTIVE tt -∗
      sie_cap_gpr γ root_ppn mf av -∗
      intr_count γ root_ppn 1 -∗
      tlb_inv_pt root_ppn -∗
      pc_is ret_tgt -∗
      locked γl -∗
      R -∗
      a_cpu ↦₈ cpuv -∗
      a_cpu_noff cid_word ↦₄ (mword_of_int 1 : mword 32) -∗
      (∃ iv : mword 32, a_cpu_int cid_word ↦₄ iv) -∗
      cur_proc pj -∗
      p_lkcpu pj ↦₈ (zero_reg : mword 64) -∗
      own_ctx (p_context pj) -∗
      ▷ sched_vc γ root_ppn Φ γs (a_cpu_ctx cid_word) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
  WP (Loop : expr riscv_lang) {{ Φ }}.

(* the deliberately-assumed contract (tracked in the coverage manifest like
   the old myproc axiom); replace with a Module Type + sealed functor when
   sleep() is proven. *)
Axiom wp_sleep_sconf :
  forall `{!riscvGS Σ, !sieG Σ, !lockG Σ} `{CID : CpuId}
    (γ : gname) (root_ppn : mword 44) (Φ : mval -> iProp Σ)
    (γs : list gname) (j : nat)
    (γl : gname) (lka : mword 64) (s : string) (R : iProp Σ)
    (m : regfile) (av : nat),
    wp_sleep_sconf_body γ root_ppn Φ γs j γl lka s R m av.
