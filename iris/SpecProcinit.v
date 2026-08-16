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
Require Import WpNext.
Require Import WpLock.
Require Import ArrCursor.
Require Import ProcGeom.
Require Import FdSlots.
Require Import FileInvDefs.
Require Import ProcInv.
Require Import SchedCtx.
Require Import KvmMap.
Require Import StackOwn.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import ProcAvail.
Local Open Scope Z_scope.


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
  Context `{!riscvGS Σ, !lockG Σ, !fileG Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ}.

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
  (* the block is the PRE-STACK one ([ProcInv.proc_dormant_prestk]): procinit
     has just written [p->kstack], and the slot's stack cannot be deposited
     until that cell is persisted into [is_kstack], which is the caller's
     next ghost step ([procs_inv_of_ready] below). *)
  Definition proc_ready (i : nat) : iProp Σ :=
    (lk_fresh (proc_addr i) "proc"%string ∗
     p_state (proc_addr i) ↦₄ UNUSED ∗
     p_kstack (proc_addr i) ↦₈ kstack_va i ∗
     proc_dormant_prestk (proc_addr i))%I.

End SpecProcinit.

(* [proc_lock_res] is generalized over the scheduler's section parameters, so
   this composition check takes them; nothing in procinit's own contract
   does. *)
Section ProcinitSeals.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fileG Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.
  Context (γ : gname)  (γs : list gname).

  (* ---- what the postcondition is FOR ----
     One [proc_ready i], plus the two public cells procinit does not touch,
     IS the body of [SchedCtx.proc_lock_res] at UNUSED.  So the caller's
     remaining ghost step really is just "allocate the invariant over this"
     -- there is no gap between what procinit hands back and what the proc
     lock has to protect.  Stated and checked here because an unproven
     contract is otherwise only as good as my reading of SchedCtx. *)
  (* [kstack_free] is the caller's to supply, and it is supplied HERE
     because this is the first point at which it can be: [is_kstack] does
     not exist until [p->kstack] is persisted, which the caller does in the
     same ghost step (see [procs_inv_of_ready]). *)
  Lemma proc_ready_lock_res (γl : gname) (i : nat) (ch : mword 64) :
    proc_ready i -∗
    p_chan (proc_addr i) ↦₈ ch -∗
    proc_pub (proc_addr i) -∗
    hart_at_any (proc_addr i) -∗
    (* the slot's state mirror, whole, at the UNUSED procinit just stored *)
    pstate_lock (proc_addr i) UNUSED -∗
    kstack_free (proc_addr i) -∗
    lk_fresh (proc_addr i) "proc"%string ∗
    p_kstack (proc_addr i) ↦₈ kstack_va i ∗
    proc_lock_res γs γl (proc_addr i).
  Proof.
    iIntros "(Hlk & Hst & Hks & Hdorm) Hch Hpub Hpark Hg Hkst".
    iFrame "Hlk Hks".
    iExists UNUSED, ch. iFrame "Hst Hg Hch Hpub".
    iApply (proc_slots_unused_intro with "[Hdorm Hkst] Hpark").
    iApply (proc_dormant_prestk_seal with "Hdorm Hkst").
  Qed.

End ProcinitSeals.

(* ------------------------------------------------------------------ *)
(*  procinit's output -> [SchedCtx.procs_inv]: the caller's ghost step. *)
(*                                                                     *)
(*  This is the assembly main() owes between procinit() and            *)
(*  scheduler() (claude-notes/projects/main-boot.md), factored out of   *)
(*  ProofMain.v because inlining it is 64 lock allocations.  It cannot  *)
(*  live in SchedCtx.v -- that would need SchedCtx to import           *)
(*  SpecProcinit for [proc_ready], and the dependency runs the other    *)
(*  way -- so it sits here, one section down from the composition       *)
(*  check [proc_ready_lock_res] it is the operational form of.          *)
(*                                                                     *)
(*  [γs] is EXISTENTIAL in the conclusion, so this section must not     *)
(*  have it as a section variable (which is why it is not in            *)
(*  ProcinitSeals).  That existential is also the whole difficulty:     *)
(*  every proc lock's resource [proc_lock_res γs _ _] mentions the   *)
(*  list of all 64 names (through [p_sched]), so the names have to be    *)
(*  chosen BEFORE any invariant is allocated -- hence                    *)
(*  [WpLock.newlock_delayed] and the two passes below.                  *)
(* ------------------------------------------------------------------ *)
Section ProcinitProcsInv.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fileG Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.
  Context (γ : gname) .

  (* [lk_fresh] in the three pieces [newlock]/[newlock_delayed] take.  The
     only content is that [lk_cpu] and [WpLock.lock_cpu] are the same address
     spelled twice (0x10 and 16). *)
  Lemma lk_fresh_pieces (lk : mword 64) (s : string) :
    lk_fresh lk s -∗
    lock_name lk s ∗ lk ↦₄ (mword_of_int 0 : mword 32) ∗
    lock_cpu lk ↦₈ (zero_reg : mword 64).
  Proof. rewrite /lk_fresh /lk_cpu /lock_cpu. iIntros "($ & $ & $)". Qed.

  (* what is left of one process once its lock word and name have gone into
     the (delayed) allocation: exactly the cells [proc_lock_res] at UNUSED
     wants, plus the [p_kstack] cell that becomes [is_kstack]. *)
  Definition proc_res (i : nat) : iProp Σ :=
    (p_kstack (proc_addr i) ↦₈ kstack_va i ∗
     p_state (proc_addr i) ↦₄ UNUSED ∗
     (∃ ch : mword 64, p_chan (proc_addr i) ↦₈ ch) ∗
     proc_pub (proc_addr i) ∗
     proc_dormant_prestk (proc_addr i) ∗
     hart_at_any (proc_addr i) ∗
     pstate_lock (proc_addr i) UNUSED ∗
     (* the slot's kernel stack, still spelled at [kstack_va i] because
        [is_kstack] has not been minted yet -- pass 3 below mints it and the
        two become [kstack_free]. *)
     stack_own (add_vec (kstack_va i) (mword_of_int 4096)) KSTACK_AV)%I.

  Lemma proc_ready_split (i : nat) (ch : mword 64) :
    proc_ready i -∗ p_chan (proc_addr i) ↦₈ ch -∗ proc_pub (proc_addr i) -∗
    hart_at_any (proc_addr i) -∗ pstate_lock (proc_addr i) UNUSED -∗
    stack_own (add_vec (kstack_va i) (mword_of_int 4096)) KSTACK_AV -∗
    lk_fresh (proc_addr i) "proc"%string ∗ proc_res i.
  Proof.
    rewrite /proc_ready /proc_res.
    iIntros "($ & Hst & Hks & Hdorm) Hch Hpub Hpark Hg Hstk".
    iFrame "Hks Hst Hpub Hdorm Hpark Hg Hstk". iExists ch. iExact "Hch".
  Qed.

  (* PASS ONE, generic: pick [n] lock ghost names, each with the wand that
     will seal its (still unknown) resource.  Not specific to procs -- any
     array of locks whose resource is indexed by the array's own names needs
     exactly this. *)
  Lemma delayed_locks_alloc (E : coPset) (nm : string) (addr : nat -> mword 64)
      (Q : nat -> iProp Σ) (n : nat) :
    ([∗ list] i ∈ seq 0 n, lk_fresh (addr i) nm ∗ Q i)
    ==∗ ∃ γl : list gname, ⌜length γl = n⌝ ∗
        ([∗ list] i ↦ g ∈ γl,
           (∀ R : iProp Σ, R ={E}=∗ is_lock g (addr i) nm R) ∗ Q i).
  Proof.
    induction n as [|n IH].
    { iIntros "_". iModIntro. iExists []. iSplit; [done|]. done. }
    rewrite seq_S Nat.add_0_l.
    rewrite (big_sepL_app (fun _ i => (lk_fresh (addr i) nm ∗ Q i)%I) (seq 0 n) [n]).
    iIntros "[Hpre Hlast]".
    iMod (IH with "Hpre") as (γl) "[%Hlen Hγl]".
    iDestruct "Hlast" as "[[Hfresh HQ] _]".
    iDestruct (lk_fresh_pieces with "Hfresh") as "(#Hnm & Hword & Hcpu)".
    iMod (newlock_delayed E (addr n) nm with "Hnm Hword Hcpu") as (g) "Hmk".
    iModIntro. iExists ((γl ++ [g])%list).
    iSplit.
    { iPureIntro. rewrite List.last_length. by rewrite Hlen. }
    rewrite (big_sepL_app
               (fun i g => ((∀ R : iProp Σ, R ={E}=∗ is_lock g (addr i) nm R) ∗ Q i)%I)
               γl [g]).
    iSplitL "Hγl"; [iExact "Hγl"|].
    rewrite big_sepL_singleton Hlen Nat.add_0_r. iFrame "Hmk HQ".
  Qed.

  (* THE HELPER.  procinit's postcondition plus the two public cells it never
     touches ([p_chan] and [proc_pub], exactly what [proc_ready_lock_res]
     consumes) becomes the scheduler's [procs_inv]. *)
  (* THE KERNEL STACKS ARRIVE HERE, one per slot, anchored at the top of the
     page procinit just recorded in [p->kstack].  They are the caller's --
     main's, hence the boot interface's -- because the words come from
     [SpecProcMapstacks]'s 64 pages and nothing between there and here has
     anywhere to park them.  This step is the FIRST that can take them:
     [kstack_free] names its anchor through the persistent [is_kstack], and
     that is minted three lines below, out of the very cell procinit wrote. *)
  Lemma procs_inv_alloc (E : coPset) :
    ([∗ list] i ∈ seq 0 NPROC,
       ((proc_ready i ∗ (∃ ch : mword 64, p_chan (proc_addr i) ↦₈ ch) ∗
         proc_pub (proc_addr i)) ∗ hart_full i (0%fin : CPU)) ∗
       pstate_full i UNUSED) -∗
    ([∗ list] i ∈ seq 0 NPROC,
       stack_own (add_vec (kstack_va i) (mword_of_int 4096)) KSTACK_AV)
    ={E}=∗ ∃ γs : list gname, procs_inv γs.
  Proof.
    iIntros "Hin Hstk".
    (* pair each slot's stack with its resources, so one [big_sepL_impl] can
       carry both through the two passes below *)
    iDestruct (big_sepL_sep_2 with "Hin Hstk") as "Hin".
    (* 1. peel [lk_fresh] out of each [proc_ready] *)
    iDestruct (big_sepL_impl
                 (fun _ i => ((((proc_ready i ∗ (∃ ch : mword 64, p_chan (proc_addr i) ↦₈ ch) ∗
                                 proc_pub (proc_addr i)) ∗ hart_full i (0%fin : CPU)) ∗
                               pstate_full i UNUSED) ∗
                              stack_own (add_vec (kstack_va i) (mword_of_int 4096)) KSTACK_AV)%I)
                 (fun _ i => (lk_fresh (proc_addr i) "proc"%string ∗ proc_res i)%I)
                 (seq 0 NPROC) with "Hin []") as "Hin".
    { iIntros "!>" (k i Hk) "[(((Hrdy & Hch & Hpub) & Hpark) & Hg) Hstk]".
      apply lookup_seq in Hk. destruct Hk as [-> Hlt].
      iDestruct "Hch" as (ch) "Hch".
      iApply (proc_ready_split with "Hrdy Hch Hpub [Hpark] [Hg] Hstk").
      { iApply (hart_at_any_intro k (0%fin : CPU) Hlt with "Hpark"). }
      (* UNUSED is [unclaimed], so the whole variable is the lock's share *)
      rewrite /pstate_lock unclaimed_UNUSED.
      iDestruct (pstate_split k UNUSED with "Hg") as "[Hg1 Hg2]".
      iSplitL "Hg1"; iApply (pstate_at_intro k _ UNUSED Hlt); iFrame. }
    (* 2. choose the 64 ghost names; the resources are still owed *)
    iMod (delayed_locks_alloc E "proc"%string proc_addr proc_res NPROC with "Hin")
      as (γs) "[%Hlen Hmk]".
    (* 3. γs is now fixed, so each lock can be paid its resource -- and the
          [p_kstack] cell persisted into the (persistent) [is_kstack]. *)
    iDestruct (big_sepL_impl
                 (fun i g => ((∀ R : iProp Σ, R ={E}=∗ is_lock g (proc_addr i) "proc"%string R)
                              ∗ proc_res i)%I)
                 (fun i g => (|={E}=> is_lock g (proc_addr i) "proc"%string
                                        (proc_lock_res γs g (proc_addr i)) ∗
                                      ∃ ks : mword 64, is_kstack (proc_addr i) ks)%I)
                 γs with "Hmk []") as "Hmk".
    { iIntros "!>" (i g _) "[Hmk (Hks & Hst & Hch & Hpub & Hdorm & Hpark & Hg & Hstk)]".
      iMod (word_pointsto_persist with "Hks") as "#Hksp".
      iDestruct "Hch" as (ch) "Hch".
      (* THE DEPOSIT: the persisted cell is [is_kstack], and with the words
         beside it the slot's stack is sealed into the dormant block. *)
      iAssert (kstack_free (proc_addr i)) with "[Hstk]" as "Hkst".
      { iApply (kstack_free_intro (proc_addr i) (kstack_va i)
                  with "[] Hstk"). iExact "Hksp". }
      iMod ("Hmk" $! (proc_lock_res γs g (proc_addr i))
              with "[Hst Hg Hch Hpub Hdorm Hpark Hkst]") as "#Hlk".
      { iApply (proc_lock_res_intro γs g (proc_addr i) UNUSED ch
                  with "Hst Hg Hch Hpub [Hdorm Hpark Hkst]").
        iApply (proc_slots_unused_intro with "[Hdorm Hkst] Hpark").
        iApply (proc_dormant_prestk_seal with "Hdorm Hkst"). }
      iModIntro. iFrame "Hlk". iExists (kstack_va i). iExact "Hksp". }
    iMod (big_sepL_fupd with "Hmk") as "Hmk".
    rewrite (big_sepL_sep (PROP:=iPropI Σ)).
    iDestruct "Hmk" as "[Hlocks Hks]".
    iModIntro. iExists γs. rewrite /procs_inv.
    iSplitR; [iPureIntro; exact Hlen |].
    iFrame "Hlocks Hks".
  Qed.

End ProcinitProcsInv.

Definition wp_procinit_sconf_body `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fileG Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId} (m : regfile) (K : nat) (b : bool) (p : mword 64) :=
  let pcE : mword 64 := mword_of_int KernelSyms.procinit in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5) : mword 64) in
  (* procinit's own frame is 8 slots (addi sp,sp,-64: ra, s0..s6); initlock
     wants 2 below that. *)
  (10 <= K)%nat ->
  sie_cap_gpr m K b p -∗
  kernel_text -∗ kernel_data -∗ pc_is pcE -∗
  (* the two standalone locks ... *)
  lk_raw pid_lock_addr -∗
  lk_raw wait_lock_addr -∗
  (* ... and the 64 processes, each with its fd-slot-free dormant block *)
  ([∗ list] i ∈ seq 0 NPROC, proc_raw (proc_addr i)) -∗
  (* THE supply being routed: NOFILE + FDSPARE units per process, i.e. the
     WHOLE of [FDSLOTS] -- nothing is left over. *)
  fd_slots (NPROC * (NOFILE + FDSPARE)) -∗
  (* ... and the SAME for inode references: 1 + IREFSPARE per process, the
     [1] being the process's own cwd unit (its cwd is null, so it holds the
     unit rather than a reference).  That is all of [IREFSLOTS] except the
     [NFILE] units the file table holds -- see [IrefSlots.v]'s header for
     why the supply is exactly NPROC*(1 + IREFSPARE) + NFILE. *)
  iref_slots (NPROC * (1 + IREFSPARE)) -∗
  wp_next b p (fun (CID : CpuId) =>
    ∀ mr,
    sie_cap_gpr mr K b p -∗
    pc_is ret_tgt -∗
    ⌜ callee_saved m mr ⌝ -∗
    lk_fresh pid_lock_addr "nextpid"%string -∗
    lk_fresh wait_lock_addr "wait_lock"%string -∗
    ([∗ list] i ∈ seq 0 NPROC, proc_ready i) -∗
    WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type PROCINIT.
  Parameter wp_procinit_sconf :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fileG Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId} (m : regfile) (K : nat) (b : bool) (p : mword 64),
      wp_procinit_sconf_body m K b p.
End PROCINIT.
