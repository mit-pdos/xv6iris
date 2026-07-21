(* ProcGeom.v -- struct proc / struct cpu geometry and the current-process
   resource.

   Pure layout facts shared by the proc-lock invariant (SchedCtx.v), the
   wakeup proof (WpWakeup.v) and the myproc/sched/yield whole-function specs.
   All per-CPU cell addresses are stated tp-indexed via [mycpu_ret tp0]
   (WpMycpu.v), the same closed form the acquire/release/push_off/pop_off
   specs already use, so cells unify across call boundaries by name.

   Layout (kernel/proc.h, corroborated by the compiled image):

     struct cpu (128 B, cpus[8] @ 0x80012378 = pid_lock + 48):
       proc@0, context@8 (14*8 B), noff@120, intena@124.
     struct proc (360 B, proc[64] @ 0x80012778 -- directly after cpus[]):
       lock@0 (locked word@0, cpu ptr@16), state@24, chan@32, context@96.

   [cur_proc p] is THE current-process resource: the current proc structure
   of this CPU (the ambient CpuId; [cid_word] is its tp-register image) is
   [p], as ownership of the [cpus[cpuid].proc] field.  myproc() returns
   exactly this value; the scheduler swtch protocol threads it across
   context switches (SchedCtx.v). *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap invariants.
Require Import SailStdpp.Base SailStdpp.Operators_mwords SailStdpp.Values.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvPtsto RiscvLang RiscvExtras.
Require Import RegFile.
Require Import WpMycpu.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.

(* ===================================================================== *)
(* Private helpers: [bv_unsigned] of the two address-forming operations.  *)
(* [add_vec] on equal widths is [bv_add] (wrap mod 2^64); [mword_of_int]   *)
(* is [Z_to_bv] (also mod 2^64).  Same shape as PtBuild's pb_* helpers.    *)
(* ===================================================================== *)
Local Lemma pg_add_vec_unsigned (x y : mword 64) :
  bv_unsigned (add_vec x y) = bv_wrap 64 (bv_unsigned x + bv_unsigned y).
Proof.
  unfold add_vec, Operators_mwords.word_binop, Operators_mwords.with_word',
    SailStdpp.Values.with_word, to_word, get_word, MachineWord.MachineWord.add.
  rewrite bv_add_unsigned. reflexivity.
Qed.

Local Lemma pg_moi_unsigned (k : Z) :
  bv_unsigned (mword_of_int k : mword 64) = bv_wrap 64 k.
Proof.
  unfold mword_of_int, Values.to_word, get_word. cbn.
  rewrite Z_to_bv_unsigned. reflexivity.
Qed.

Local Lemma pg_modulus64 : bv_modulus 64 = 18446744073709551616.
Proof. vm_compute. reflexivity. Qed.

(* [mword_of_int (uint w) = w] (mirror of StackOwn.stk_mword_of_int_uint,
   which lives in a later file not imported here). *)
Local Lemma pg_moi_uint (w : mword 64) : mword_of_int (uint w) = w.
Proof.
  unfold mword_of_int, MachineWord.MachineWord.Z_to_word.
  rewrite uint_unsigned.
  change (MachineWord.MachineWord.Z_idx 64) with 64%N.
  apply Z_to_bv_bv_unsigned.
Qed.

(* add_vec associativity (mirror of KernelRvcDecode.po_addv_assoc, which lives
   in a later file not imported here). *)
Local Lemma pg_addv_assoc (a b c : mword 64) :
  add_vec (add_vec a b) c = add_vec a (add_vec b c).
Proof.
  apply bv_eq. rewrite !pg_add_vec_unsigned.
  rewrite bv_wrap_add_idemp_l bv_wrap_add_idemp_r Z.add_assoc. reflexivity.
Qed.

(* ===================================================================== *)
(* struct proc geometry.                                                  *)
(* ===================================================================== *)
Definition NPROC : nat := 64%nat.
Definition proc_size : Z := 360.
Definition proc_base : mword 64 := mword_of_int KernelSyms.proc.
Definition proc_addr (i : nat) : mword 64 :=
  add_vec proc_base (mword_of_int (proc_size * Z.of_nat i)).

Definition state_off : Z := 24.
Definition chan_off : Z := 32.
Definition context_off : Z := 96.

Definition p_state (pa : mword 64) : mword 64 := add_vec pa (mword_of_int state_off).
Definition p_chan (pa : mword 64) : mword 64 := add_vec pa (mword_of_int chan_off).
Definition p_context (pa : mword 64) : mword 64 := add_vec pa (mword_of_int context_off).

(* the lock's cpu-pointer word (spinlock field at +16), in the exact address
   form acquire/release/holding use ([a_cpu] with lk0 = pa, lock at +0). *)
Definition p_lkcpu (pa : mword 64) : mword 64 :=
  add_vec pa (sign_extend' 64 (mword_of_int 16 : mword 12)).

(* the pid word (int at +48), in the exact address form of the [lw rd,48(a0)]
   reads after a myproc() call (acquiresleep/holdingsleep). *)
Definition p_pid (pa : mword 64) : mword 64 :=
  add_vec pa (sign_extend' 64 (mword_of_int 48 : mword 12)).

(* enum procstate codes (kernel/proc.h): UNUSED=0 USED=1 SLEEPING=2
   RUNNABLE=3 RUNNING=4 ZOMBIE=5. *)
Definition SLEEPING : mword 32 := mword_of_int 2.
Definition RUNNABLE : mword 32 := mword_of_int 3.
Definition RUNNING : mword 32 := mword_of_int 4.

(* A state that requires the saved-context obligation: the two "parked"
   states that own a saved context reachable by swtch. *)
Definition needs_ctx (st : mword 32) : bool :=
  bool_decide (st = RUNNABLE) || bool_decide (st = SLEEPING).

Lemma needs_ctx_SLEEPING : needs_ctx SLEEPING = true.
Proof. rewrite /needs_ctx orb_true_r. done. Qed.

Lemma needs_ctx_RUNNABLE : needs_ctx RUNNABLE = true.
Proof.
  rewrite /needs_ctx. rewrite (bool_decide_eq_true_2 (RUNNABLE = RUNNABLE)); done.
Qed.

Lemma needs_ctx_RUNNING : needs_ctx RUNNING = false.
Proof. vm_compute. reflexivity. Qed.

(* a parked state is not RUNNING (refutes sched's "sched RUNNING" panic arm). *)
Lemma needs_ctx_not_RUNNING (st : mword 32) :
  needs_ctx st = true -> st <> RUNNING.
Proof.
  intros Hn ->.
  rewrite needs_ctx_RUNNING in Hn. discriminate.
Qed.

(* p++ : &proc[k] + sizeof(proc) = &proc[k+1].  The addi's 12-bit immediate
   [360] sign-extends to the same 64-bit constant, and mword addition agrees
   with Z addition mod 2^64 (via [avi_mword]). *)
Lemma proc_addr_succ (k : nat) :
  add_vec (proc_addr k) (sign_extend' 64 (mword_of_int proc_size : mword 12)) = proc_addr (S k).
Proof.
  unfold proc_addr. rewrite pg_addv_assoc.
  assert (Hsx : sign_extend' 64 (mword_of_int proc_size : mword 12) = (mword_of_int proc_size : mword 64))
    by (apply bv_eq; vm_compute; reflexivity).
  rewrite Hsx. f_equal.
  change (add_vec (mword_of_int (proc_size * Z.of_nat k) : mword 64) (mword_of_int proc_size))
    with (add_vec_int (mword_of_int (proc_size * Z.of_nat k) : mword 64) proc_size).
  rewrite avi_mword. f_equal. rewrite Nat2Z.inj_succ. ring.
Qed.

(* closed forms as unsigned integers (no wraparound in the array range) *)
Lemma proc_addr_unsigned (i : nat) :
  (i < NPROC)%nat ->
  bv_unsigned (proc_addr i) = KernelSyms.proc + proc_size * Z.of_nat i.
Proof.
  intro Hi. unfold NPROC in Hi.
  unfold proc_addr, proc_base.
  rewrite pg_add_vec_unsigned !pg_moi_unsigned.
  rewrite bv_wrap_add_idemp_l bv_wrap_add_idemp_r.
  apply bv_wrap_small.
  unfold KernelSyms.proc, proc_size. rewrite pg_modulus64. lia.
Qed.

Lemma p_context_unsigned (i : nat) :
  (i < NPROC)%nat ->
  bv_unsigned (p_context (proc_addr i))
  = KernelSyms.proc + proc_size * Z.of_nat i + context_off.
Proof.
  intro Hi. assert (Hi' := Hi). unfold NPROC in Hi'.
  unfold p_context.
  rewrite pg_add_vec_unsigned (proc_addr_unsigned i Hi) pg_moi_unsigned.
  rewrite bv_wrap_add_idemp_r.
  apply bv_wrap_small.
  unfold KernelSyms.proc, proc_size, context_off. rewrite pg_modulus64. lia.
Qed.

(* proc-context addresses are injective on the array range. *)
Lemma p_context_proc_addr_inj (i j : nat) :
  (i < NPROC)%nat -> (j < NPROC)%nat ->
  p_context (proc_addr i) = p_context (proc_addr j) -> i = j.
Proof.
  intros Hi Hj Heq.
  apply (f_equal bv_unsigned) in Heq.
  rewrite (p_context_unsigned i Hi) (p_context_unsigned j Hj) in Heq.
  unfold proc_size in Heq. lia.
Qed.

(* ===================================================================== *)
(* struct cpu cell addresses, tp-indexed via [mycpu_ret].                 *)
(* ===================================================================== *)

(* c->proc (offset 0): the cell the current-process resource owns. *)
Definition a_cpu_proc (tp0 : mword 64) : mword 64 := mycpu_ret tp0.
(* &c->context (offset 8): where this CPU's scheduler context is saved. *)
Definition a_cpu_ctx (tp0 : mword 64) : mword 64 :=
  add_vec (mycpu_ret tp0) (sign_extend' 64 (mword_of_int 8 : mword 12)).
(* c->noff / c->intena (offsets 120 / 124), in the push_off/pop_off form. *)
Definition a_cpu_noff (tp0 : mword 64) : mword 64 :=
  add_vec (mycpu_ret tp0) (sign_extend' 64 (mword_of_int 120 : mword 12)).
Definition a_cpu_int (tp0 : mword 64) : mword 64 :=
  add_vec (mycpu_ret tp0) (sign_extend' 64 (mword_of_int 124 : mword 12)).

(* a valid hart id: tp holds a cpu index below NCPU = 8. *)
Definition tp_ok (tp0 : mword 64) : Prop := 0 <= uint tp0 < 8.

(* for a valid hart id, mycpu_ret is the concrete &cpus[tp]. *)
Lemma mycpu_ret_unsigned (tp0 : mword 64) :
  tp_ok tp0 ->
  bv_unsigned (mycpu_ret tp0) = KernelSyms.cpus + 128 * uint tp0.
Proof.
  intros [H0 H8].
  (* [tp0] is one of the 8 concrete hart ids; each vm_computes directly.
     [stk_mword_of_int_uint] turns [tp0] into [mword_of_int (uint tp0)]. *)
  assert (Hc : uint tp0 = 0 \/ uint tp0 = 1 \/ uint tp0 = 2 \/ uint tp0 = 3 \/
               uint tp0 = 4 \/ uint tp0 = 5 \/ uint tp0 = 6 \/ uint tp0 = 7) by lia.
  assert (Htp : tp0 = mword_of_int (uint tp0)) by (symmetry; apply pg_moi_uint).
  destruct Hc as [Hc|[Hc|[Hc|[Hc|[Hc|[Hc|[Hc|Hc]]]]]]];
    rewrite {1}Htp Hc; vm_compute; reflexivity.
Qed.

(* the scheduler-context address of a valid hart never collides with a proc
   context: cpus[] ends exactly where proc[] begins (0x80012778), and the
   context field sits 8 bytes in / 96 bytes in respectively. *)
Lemma a_cpu_ctx_ne_p_context (tp0 : mword 64) (j : nat) :
  tp_ok tp0 -> (j < NPROC)%nat ->
  a_cpu_ctx tp0 <> p_context (proc_addr j).
Proof.
  intros Htp Hj Heq.
  apply (f_equal bv_unsigned) in Heq.
  unfold a_cpu_ctx in Heq.
  rewrite pg_add_vec_unsigned (mycpu_ret_unsigned tp0 Htp) in Heq.
  assert (H8 : bv_unsigned (sign_extend' 64 (mword_of_int 8 : mword 12) : mword 64) = 8)
    by (vm_compute; reflexivity).
  rewrite H8 in Heq.
  rewrite (p_context_unsigned j Hj) in Heq.
  destruct Htp as [Ht0 Ht8].
  assert (Hlhs : bv_wrap 64 (KernelSyms.cpus + 128 * uint tp0 + 8)
                 = KernelSyms.cpus + 128 * uint tp0 + 8).
  { apply bv_wrap_small. unfold KernelSyms.cpus. rewrite pg_modulus64. lia. }
  rewrite Hlhs in Heq.
  unfold KernelSyms.cpus, KernelSyms.proc, proc_size, context_off in Heq. lia.
Qed.

(* mycpu_ret of a valid hart is a nonzero pointer (acquire's cpuold=0 check). *)
Lemma mycpu_ret_nonzero (tp0 : mword 64) :
  tp_ok tp0 ->
  eq_vec (zero_reg : mword 64) (mycpu_ret tp0) = false.
Proof.
  intro Htp. apply eq_vec_false_iff. intro Heq.
  apply (f_equal bv_unsigned) in Heq.
  rewrite (mycpu_ret_unsigned tp0 Htp) in Heq.
  assert (Hz : bv_unsigned (zero_reg : mword 64) = 0) by (vm_compute; reflexivity).
  rewrite Hz in Heq.
  destruct Htp as [Ht0 Ht8].
  unfold KernelSyms.cpus in Heq. lia.
Qed.

(* ===================================================================== *)
(* The hart id: tp holds the ambient CpuId.                               *)
(* ===================================================================== *)

(* the ambient hart id as a tp-register value.  mycpu()'s return for this
   hart is [mycpu_ret cid_word] = &cpus[cpu_id]. *)
Definition cid_word `{CID : CpuId} : mword 64 :=
  mword_of_int (Z.of_nat (fin_to_nat cpu_id)).

Lemma tp_ok_cid `{CID : CpuId} : tp_ok cid_word.
Proof.
  unfold tp_ok, cid_word.
  pose proof (fin_to_nat_lt cpu_id) as Hlt. unfold NCPU in Hlt.
  assert (Hz : 0 <= Z.of_nat (fin_to_nat cpu_id) < 8).
  { split; [ apply Nat2Z.is_nonneg | ].
    change 8 with (Z.of_nat 8%nat). apply inj_lt. exact Hlt. }
  rewrite uint_unsigned pg_moi_unsigned bv_wrap_small;
    [ exact Hz | rewrite pg_modulus64; lia ].
Qed.

(* ===================================================================== *)
(* The current-process resource.                                          *)
(*                                                                        *)
(* [cur_proc p] says: the current proc structure (of THIS cpu, the ambient *)
(* CpuId) is [p] -- concretely, ownership of [cpus[cpuid].proc] holding    *)
(* [p].  The cpu struct's ownership is distributed across the protocol:    *)
(* [cur_proc] owns the proc field; the noff/intena fields are separately   *)
(* threaded cells (their VALUES must stay visible to the acquire/release/  *)
(* push_off/pop_off specs); and the context field is owned by the parked   *)
(* scheduler's [valid_context] while a process runs.                       *)
(*                                                                        *)
(* myproc() returns exactly [p] (SpecMyproc.v); only the scheduler          *)
(* rewrites the field (clearing it to 0 between processes).  The           *)
(* companion "tp register holds cpuid" invariant is the spec convention    *)
(* [m !!! x4 = cid_word], preserved by [callee_saved] and re-established   *)
(* across swtch by the chain payload's [⌜tpv = cid_word⌝] (SchedCtx.v).    *)
(* ===================================================================== *)
Section CurProc.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.

  Definition cur_proc (p : mword 64) : iProp Σ :=
    a_cpu_proc cid_word ↦₈ p.

  Global Instance cur_proc_timeless p : Timeless (cur_proc p).
  Proof. rewrite /cur_proc /word_pointsto /mem_pointsto. apply _. Qed.
End CurProc.
