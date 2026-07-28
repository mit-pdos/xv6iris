(* SpecProcinit.v -- the public interface of procinit, stated independently
   of its proof.  Requires only the definitional layer -- never a
   whole-function proof file -- so every function proof can be checked in
   parallel.

     void procinit(void) {
       initlock(&pid_lock, "nextpid");
       initlock(&wait_lock, "wait_lock");
       for (p = proc; p < &proc[NPROC]; p++) {
         initlock(&p->lock, "proc");
         p->state  = UNUSED;
         p->kstack = KSTACK((int)(p - proc));
       }
     }

   procinit is where the fd-slot supply is ROUTED.  Every other holder of an
   [fd_slot] got it from a process (FdSlots.v): an empty descriptor holds its
   own unit, a descriptor naming a file has given it to the ftable.  Boot
   mints [FDSLOTS] units with [fd_slots_alloc]; procinit takes ALL of them --
   [NPROC * (NOFILE + FDSPARE)] -- and hands each process its NOFILE
   per-descriptor units plus its [FDSPARE] allowance, which is what turns the
   fd-slot-free [proc_dormant_nofd] blocks it is given into real
   [proc_dormant]s ([ProcInv.proc_dormant_seal]).  Nothing is left with the
   caller: the allowance a syscall borrows for a reference in flight
   (sys_open's one, sys_pipe's two) comes out of the process's own dormant
   block via allocproc, not from a pile boot kept back.

   Everything else procinit does to a process is the three writes the C
   shows.  It touches none of the private cells -- the BSS is already zero --
   which is why the block it is handed is [proc_dormant_nofd] rather than a
   pile of raw cells.

   Sealing the 64 [is_lock]s over [SchedCtx.proc_lock_res] is the CALLER's
   ghost step, not procinit's -- the same division iinit draws for the inode
   sleeplocks.  procinit hands back the zeroed lock word plus the name, and
   [p_kstack] as a full cell (the caller persists it into [is_kstack] when it
   is ready to). *)
From Stdlib Require Import Eqdep_dec ZArith Lia List.
From stdpp Require Import gmap list list_monad bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import excl.
From iris.base_logic.lib Require Import ghost_var gen_heap invariants.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import RegFile InstrBytes SmodeCore CalleeSaved KernelText KernelDataInv IntrDefs.
Require Import WpLock.
Require Import ArrCursor.
Require Import ProcGeom.
Require Import FdSlots.
Require Import FileInv.
Require Import ProcInv.
Require Import SchedCtx.
Require Import KvmMap.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Local Open Scope Z_scope.

Notation PI := KernelSyms.procinit.

(* ------------------------------------------------------------------ *)
(*  Geometry                                                           *)
(* ------------------------------------------------------------------ *)

(* The two standalone locks, and the three string literals.  The literals sit
   in .rodata past etext with no ELF symbol of their own, so their addresses
   are spelled out here and read out of [kernel_data] by the proof (the same
   way iinit reads "itable"/"inode"). *)
Definition pid_lock_addr : mword 64 := mword_of_int KernelSyms.pid_lock.
Definition wait_lock_addr : mword 64 := mword_of_int KernelSyms.wait_lock.
Definition nextpid_str : Z := 0x80007160.
Definition waitlock_str : Z := 0x80007168.
Definition proc_str : Z := 0x80007178.

(* the cpu field of a [struct spinlock] at [lk], in the form initlock's
   contract spells it. *)
Definition lk_cpu (lk : mword 64) : mword 64 :=
  add_vec lk (sign_extend' 64 (mword_of_int 0x10 : mword 12)).

(* The loop walks [proc] with an ArrCursor at stride 360 and stops at
   [&proc[NPROC]] -- which the linker placed at [tickslock], so that symbol
   IS the end pointer the [bne] compares against.  These four facts pin the
   addresses the proof's [acur] side conditions need; the compiler checks
   them here rather than mid-proof. *)
Definition pacur (i : nat) : mword 64 := acur KernelSyms.proc proc_size i.

Lemma proc_addr_acur (i : nat) : proc_addr i = pacur i.
Proof.
  unfold proc_addr, pacur, acur, proc_base, proc_size.
  unfold add_vec, Operators_mwords.word_binop, Operators_mwords.with_word',
    SailStdpp.Values.with_word, to_word, get_word, MachineWord.MachineWord.add.
  apply bv_eq. rewrite bv_add_unsigned.
  unfold mword_of_int, Values.mword_of_int, MachineWord.MachineWord.Z_to_word.
  rewrite !Z_to_bv_unsigned. by rewrite bv_wrap_add_idemp.
Qed.

Lemma proc_base_nonneg : 0 <= KernelSyms.proc.
Proof. unfold KernelSyms.proc. lia. Qed.
Lemma proc_size_pos : 0 < proc_size.
Proof. unfold proc_size. lia. Qed.
Lemma proc_end_fits : KernelSyms.proc + proc_size * Z.of_nat NPROC < 2 ^ 64.
Proof.
  unfold proc_size, NPROC, KernelSyms.proc.
  assert (H : (2 ^ 64 = 18446744073709551616)%Z) by (vm_compute; reflexivity).
  rewrite H. lia.
Qed.

(* one past the last process is [tickslock] -- the literal end pointer. *)
Lemma proc_end_is_tickslock : pacur NPROC = mword_of_int KernelSyms.tickslock.
Proof. unfold pacur, acur, proc_size, NPROC. apply bv_eq; vm_compute; reflexivity. Qed.

Section SpecProcinit.
  Context `{!riscvGS Σ, !lockG Σ, !fileG Σ, !fdslotG Σ}.

  (* ---- what a lock looks like before and after initlock ---- *)
  Definition lk_raw (lk : mword 64) : iProp Σ :=
    (∃ (vlock : mword 32) (vname vcpu : mword 64),
       lk ↦₄ vlock ∗ lock_name_field lk ↦₈ vname ∗ lk_cpu lk ↦₈ vcpu)%I.

  Definition lk_fresh (lk : mword 64) (s : string) : iProp Σ :=
    (lk ↦₄ (mword_of_int 0 : mword 32) ∗
     lock_name lk s ∗
     lk_cpu lk ↦₈ (zero_reg : mword 64))%I.

  (* ---- one process, before ---- *)
  (* [p_state] and [p_kstack] are the only two private cells procinit
     writes; everything else it is handed is already in its final shape. *)
  Definition proc_raw (pa : mword 64) : iProp Σ :=
    (∃ (vst : mword 32) (vks : mword 64),
       lk_raw pa ∗
       p_state pa ↦₄ vst ∗
       p_kstack pa ↦₈ vks ∗
       proc_dormant_nofd pa)%I.

  (* ---- one process, after ---- *)
  Definition proc_ready (i : nat) : iProp Σ :=
    (lk_fresh (proc_addr i) "proc"%string ∗
     p_state (proc_addr i) ↦₄ UNUSED ∗
     p_kstack (proc_addr i) ↦₈ kstack_va i ∗
     proc_dormant (proc_addr i) UNUSED)%I.

End SpecProcinit.

(* [proc_lock_res] is generalized over the scheduler's section parameters, so
   this composition check takes them; nothing in procinit's own contract
   does. *)
Section ProcinitSeals.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fileG Σ, !fdslotG Σ}.
  Context `{CID : CpuId}.
  Context (γ : gname) (Φ : mval -> iProp Σ) (γs : list gname).

  (* ---- what the postcondition is FOR ----
     One [proc_ready i], plus the two public cells procinit does not touch,
     IS the body of [SchedCtx.proc_lock_res] at UNUSED.  So the caller's
     remaining ghost step really is just "allocate the invariant over this"
     -- there is no gap between what procinit hands back and what the proc
     lock has to protect.  Stated and checked here because an unproven
     contract is otherwise only as good as my reading of SchedCtx. *)
  Lemma proc_ready_lock_res (γl : gname) (i : nat) (ch : mword 64) :
    proc_ready i -∗
    p_chan (proc_addr i) ↦₈ ch -∗
    proc_pub (proc_addr i) -∗
    lk_fresh (proc_addr i) "proc"%string ∗
    p_kstack (proc_addr i) ↦₈ kstack_va i ∗
    proc_lock_res γ Φ γs γl (proc_addr i).
  Proof.
    iIntros "(Hlk & Hst & Hks & Hdorm) Hch Hpub".
    iFrame "Hlk Hks".
    iExists UNUSED, ch. iFrame "Hst Hch Hpub".
    rewrite /proc_slots.
    rewrite (_ : needs_ctx UNUSED = false); [| vm_compute; reflexivity].
    rewrite (_ : inv_dormant UNUSED = true); [| vm_compute; reflexivity].
    iSplitR; [done | iExact "Hdorm"].
  Qed.

End ProcinitSeals.

Definition wp_procinit_sconf_body `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fileG Σ, !fdslotG Σ} `{CID : CpuId}
    (γ : gname) (Φ : mval -> iProp Σ) (m : regfile) (K : nat) :=
  let pcE : mword 64 := mword_of_int KernelSyms.procinit in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5) : mword 64) in
  (* procinit's own frame is 8 slots (addi sp,sp,-64: ra, s0..s6); initlock
     wants 2 below that. *)
  (10 <= K)%nat ->
  sie_cap_gpr γ m K -∗
  kernel_text -∗ kernel_data -∗ pc_is pcE -∗
  (* the two standalone locks ... *)
  lk_raw pid_lock_addr -∗
  lk_raw wait_lock_addr -∗
  (* ... and the 64 processes, each with its fd-slot-free dormant block *)
  ([∗ list] i ∈ seq 0 NPROC, proc_raw (proc_addr i)) -∗
  (* THE supply being routed: NOFILE + FDSPARE units per process, i.e. the
     WHOLE of [FDSLOTS] -- nothing is left over. *)
  fd_slots (NPROC * (NOFILE + FDSPARE)) -∗
  ( ∀ mr,
    sie_cap_gpr γ mr K -∗
    pc_is ret_tgt -∗
    ⌜ callee_saved m mr ⌝ -∗
    lk_fresh pid_lock_addr "nextpid"%string -∗
    lk_fresh wait_lock_addr "wait_lock"%string -∗
    ([∗ list] i ∈ seq 0 NPROC, proc_ready i) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}) -∗
  WP (Loop : expr riscv_lang) {{ Φ }}.

Module Type PROCINIT.
  Parameter wp_procinit_sconf :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fileG Σ, !fdslotG Σ} `{CID : CpuId}
      (γ : gname) (Φ : mval -> iProp Σ) (m : regfile) (K : nat),
      wp_procinit_sconf_body γ Φ m K.
End PROCINIT.
