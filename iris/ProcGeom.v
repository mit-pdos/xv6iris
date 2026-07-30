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
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import RiscvPtsto RiscvLang RiscvExtras.
Require Export HartTp.   (* cid_word_of / cid_word live here now; EXPORTED so the
                            ~90 existing references through ProcGeom keep working *)
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

Lemma pg_moi_unsigned (k : Z) :
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

(* the pid word (int at +48), in the exact address form of the [lw rd,48(a0)]
   reads after a myproc() call (acquiresleep/holdingsleep). *)
Definition p_pid (pa : mword 64) : mword 64 :=
  add_vec pa (sign_extend' 64 (mword_of_int 48 : mword 12)).

(* The three private (p->lock-free) address-space fields -- sz (+72),
   pagetable (+80), trapframe (+88) -- packed between kstack (+64) and
   context (+96).  [proc_size = 360] pins the whole layout: 96 + context
   (14 words = 112) + ofile[16] (128) + cwd (8) + name[16] (16) = 360.

   Spelled in the exact address form of the [ld/sd rd,off(rs)] that reach
   them (the [p_pid] shape, NOT the [mword_of_int] shape above) --
   proc_pagetable's [ld a3,88(s2)] is the first consumer.  ONE definition
   each: [p_trapframe] used to be a local in SpecProcPagetable.v. *)
Definition p_sz (pa : mword 64) : mword 64 :=
  add_vec pa (sign_extend' 64 (mword_of_int 72 : mword 12)).
Definition p_pagetable (pa : mword 64) : mword 64 :=
  add_vec pa (sign_extend' 64 (mword_of_int 80 : mword 12)).
Definition p_trapframe (pa : mword 64) : mword 64 :=
  add_vec pa (sign_extend' 64 (mword_of_int 88 : mword 12)).

(* The rest of [struct proc], in the [mword_of_int] shape (these are reached
   by whole-word address computations, not by a 12-bit [ld/sd] displacement;
   a consumer that needs the [sign_extend'] spelling rewrites at its own
   access site, as the sleeplock proofs do for [p_pid]).  Offsets corroborated
   by the compiled image -- see claude-notes/design/proc-struct.md:
   fdalloc's [addi a5,a0,208] + stride-8 x 16 scan pins ofile,
   sys_chdir's [ld a0,336(s2)] pins cwd. *)
Definition p_killed (pa : mword 64) : mword 64 := add_vec pa (mword_of_int 40).
Definition p_xstate (pa : mword 64) : mword 64 := add_vec pa (mword_of_int 44).
Definition p_parent (pa : mword 64) : mword 64 := add_vec pa (mword_of_int 56).
Definition p_kstack (pa : mword 64) : mword 64 := add_vec pa (mword_of_int 64).
Definition p_cwd    (pa : mword 64) : mword 64 := add_vec pa (mword_of_int 336).

(* p->name is a 16-byte char array, not a word; [p_name pa i] is byte [i]. *)
Definition PNAMELEN : nat := 16%nat.
Definition p_name (pa : mword 64) (i : nat) : mword 64 :=
  add_vec pa (mword_of_int (344 + Z.of_nat i)).

(* ---- struct trapframe (the page p->trapframe points at) ----------------
   36 saved 64-bit words at offsets 0..280, i.e. [8*i] for field index i:
     0 kernel_satp  1 kernel_sp  2 kernel_trap  3 epc  4 kernel_hartid
     5 ra  6 sp  7 gp  8 tp  9 t0 10 t1 11 t2 12 s0 13 s1
    14 a0 15 a1 16 a2 17 a3 18 a4 19 a5 20 a6 21 a7
    22 s2 .. 31 s11  32 t3 33 t4 34 t5 35 t6
   so the nth SYSCALL ARGUMENT (a0..a5) is field [14 + n] -- which is exactly
   the imm field the [c.ld a0,<112+8n>(a5)] in argraw encodes.  The struct is
   288 bytes; the page it sits in is 4096. *)
Definition TFWORDS : nat := 36%nat.
Definition TFBYTES : Z := 288.
Definition tf_word_off (i : nat) : Z := 8 * Z.of_nat i.
(* the nth syscall argument's field index *)
Definition tf_arg_idx (n : nat) : nat := (14 + n)%nat.
(* argraw serves a0..a5 *)
Definition NARG : nat := 6%nat.

(* p->ofile[fd].  NOFILE lives HERE rather than in FdSlots.v: it is
   [struct proc]'s array length, and FdSlots already imports this file. *)
Definition NOFILE : nat := 16%nat.
Definition p_ofile (pa : mword 64) (fd : nat) : mword 64 :=
  add_vec pa (mword_of_int (208 + 8 * Z.of_nat fd)).

(* The arithmetic gcc emits to index [p->ofile[fd]] at a RUNTIME fd:
   [slli rd,rs,3] then [addi rd,rd,208] then [add a0,a0,rd].  Both sys_close
   and argfd do exactly this (with different register pairs, hence the shift
   stated over a symbolic value rather than a register), and the sum is
   [p_ofile] by definition.  Proving the shift once over a symbolic [z] is
   what keeps either proof from casing on the sixteen descriptors. *)
Local Lemma pg_moi64_uns (z : Z) : 0 <= z < 18446744073709551616 ->
  bv_unsigned (mword_of_int z : mword 64) = z.
Proof.
  intro Hz. rewrite pg_moi_unsigned. apply bv_wrap_small.
  unfold bv_modulus. change (2 ^ Z.of_N 64)%Z with 18446744073709551616%Z. lia.
Qed.

Lemma ofile_slli3 (z : Z) : 0 <= z -> z * 8 < 18446744073709551616 ->
  shift_bits_left (mword_of_int z : mword 64)
                  (subrange_vec_dec (mword_of_int 3 : mword 6) (Z.sub log2_xlen 1) 0)
  = mword_of_int (z * 8).
Proof.
  intros Hz0 Hz. apply bv_eq.
  unfold shift_bits_left, shiftl, with_word, get_word,
         MachineWord.MachineWord.logical_shift_left.
  rewrite bv_shiftl_unsigned.
  replace (bv_unsigned (MachineWord.MachineWord.N_to_word (MachineWord.MachineWord.Z_idx 64)
             (MachineWord.MachineWord.Z_idx (int_of_mword false
                (subrange_vec_dec (mword_of_int 3 : mword 6) (Z.sub log2_xlen 1) 0))))) with 3
    by (vm_compute; reflexivity).
  assert (Hzlt : z < 18446744073709551616) by nia.
  rewrite (pg_moi64_uns z ltac:(lia)).
  rewrite Z.shiftl_mul_pow2; [| lia]. change (2^3) with 8.
  rewrite (pg_moi64_uns (z * 8) ltac:(nia)).
  apply bv_wrap_small. unfold bv_modulus.
  change (2 ^ Z.of_N 64)%Z with 18446744073709551616%Z.
  split; [apply Z.mul_nonneg_nonneg; lia | exact Hz].
Qed.

Lemma ofile_addi208 (z : Z) : 0 <= z -> z + 208 < 18446744073709551616 ->
  add_vec (mword_of_int z : mword 64) (sign_extend' 64 (mword_of_int 208 : mword 12))
  = mword_of_int (208 + z).
Proof.
  intros Hz0 Hz.
  assert (H208 : (sign_extend' 64 (mword_of_int 208 : mword 12) : mword 64) = mword_of_int 208)
    by (apply bv_eq; vm_compute; reflexivity).
  rewrite H208.
  change (add_vec (mword_of_int z : mword 64) (mword_of_int 208))
    with (add_vec_int (mword_of_int z : mword 64) 208).
  rewrite avi_mword. f_equal. lia.
Qed.

(* ---- the three forms a SCAN of [p->ofile[]] meets (fdalloc, kexit) ----
   [ArrCursor.acur] does not apply: it takes a [Z] base, which suits a fixed
   global, whereas [p_ofile] hangs off a per-slot [mword] base.  So the
   walking-pointer arithmetic is stated directly here, in the shape each
   instruction's WP leaf produces it. *)

(* [addi rd,p,208] -- the cursor's initial value, &p->ofile[0] *)
Lemma p_ofile_zero (pa : mword 64) :
  add_vec pa (sign_extend' 64 (mword_of_int 208 : mword 12)) = p_ofile pa 0%nat.
Proof.
  unfold p_ofile.
  replace (sign_extend' 64 (mword_of_int 208 : mword 12) : mword 64)
    with (mword_of_int (208 + 8 * Z.of_nat 0%nat) : mword 64)
    by (apply bv_eq; vm_compute; reflexivity).
  reflexivity.
Qed.

(* [c.addi rd,rd,8] -- the cursor's bump, fd -> fd+1 *)
Lemma p_ofile_succ (pa : mword 64) (fd : nat) :
  add_vec (p_ofile pa fd) (sign_extend' 64 (sign_extend' 12 (mword_of_int 8 : mword 6)))
  = p_ofile pa (S fd).
Proof.
  unfold p_ofile. rewrite pg_addv_assoc.
  assert (Hsx : sign_extend' 64 (sign_extend' 12 (mword_of_int 8 : mword 6))
                = (mword_of_int 8 : mword 64))
    by (apply bv_eq; vm_compute; reflexivity).
  rewrite Hsx. f_equal.
  change (add_vec (mword_of_int (208 + 8 * Z.of_nat fd) : mword 64) (mword_of_int 8))
    with (add_vec_int (mword_of_int (208 + 8 * Z.of_nat fd) : mword 64) 8).
  rewrite avi_mword. f_equal. rewrite Nat2Z.inj_succ. ring.
Qed.

(* the address the [slli]/[addi 208]/[add] recomputation lands on: what
   [ofile_slli3] then [ofile_addi208] produce, folded back into [p_ofile]. *)
Lemma p_ofile_shift_form (pa : mword 64) (fd : nat) :
  add_vec pa (mword_of_int (208 + Z.of_nat fd * 8)) = p_ofile pa fd.
Proof.
  unfold p_ofile.
  replace (208 + Z.of_nat fd * 8)%Z with (208 + 8 * Z.of_nat fd)%Z by ring.
  reflexivity.
Qed.

(* enum procstate codes (kernel/proc.h): UNUSED=0 USED=1 SLEEPING=2
   RUNNABLE=3 RUNNING=4 ZOMBIE=5. *)
Definition UNUSED : mword 32 := mword_of_int 0.
Definition USED : mword 32 := mword_of_int 1.
Definition SLEEPING : mword 32 := mword_of_int 2.
Definition RUNNABLE : mword 32 := mword_of_int 3.
Definition RUNNING : mword 32 := mword_of_int 4.

(* A state that requires the saved-context obligation: the two "parked"
   states that own a saved context reachable by swtch. *)
Definition ZOMBIE : mword 32 := mword_of_int 5.

(* The SECOND of the two flat state predicates the proc-lock invariant keys
   on (the first is [needs_ctx] below): the states in which nobody outside
   the invariant owns this slot's private field block, so the invariant holds
   it and allocproc/wait find it there.  Deliberately a flat boolean sitting
   BESIDE [needs_ctx] rather than nested inside a case chain --
   claude-notes/design/proc-struct.md. *)
Definition inv_dormant (st : mword 32) : bool :=
  bool_decide (st = UNUSED) || bool_decide (st = ZOMBIE).

Lemma inv_dormant_UNUSED : inv_dormant UNUSED = true.
Proof. vm_compute. reflexivity. Qed.
Lemma inv_dormant_ZOMBIE : inv_dormant ZOMBIE = true.
Proof. vm_compute. reflexivity. Qed.
Lemma inv_dormant_USED : inv_dormant USED = false.
Proof. vm_compute. reflexivity. Qed.
Lemma inv_dormant_SLEEPING : inv_dormant SLEEPING = false.
Proof. vm_compute. reflexivity. Qed.
Lemma inv_dormant_RUNNABLE : inv_dormant RUNNABLE = false.
Proof. vm_compute. reflexivity. Qed.
Lemma inv_dormant_RUNNING : inv_dormant RUNNING = false.
Proof. vm_compute. reflexivity. Qed.

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

(* proc addresses are injective on the array range. *)
Lemma proc_addr_inj (i j : nat) :
  (i < NPROC)%nat -> (j < NPROC)%nat ->
  proc_addr i = proc_addr j -> i = j.
Proof.
  intros Hi Hj Heq.
  apply (f_equal bv_unsigned) in Heq.
  rewrite (proc_addr_unsigned i Hi) (proc_addr_unsigned j Hj) in Heq.
  unfold proc_size in Heq. lia.
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

(* ANY hart's id as a tp-register value, and its [struct cpu] pointer --
   what mycpu() returns on that hart.  [cpus_ptr] is the value a lock's
   [cpu] field holds while hart [i] holds the lock (WpLock.v), so the
   lock-holder token is keyed by [i] and the field's value is [cpus_ptr i];
   the two injectivity/nonzeroness facts below are what let a NON-holder
   conclude that the field does not name it. *)
(* [cid_word_of] and [cid_word] MOVED to HartTp.v: every register-file
   resource now mentions the hart id (tp is pinned to the hart), so the
   definition has to sit below the leaf layer rather than here.  Kept
   re-exported through this file's [Require Import HartTp] so the ~90
   existing references are unchanged -- but there must be exactly ONE
   constant, or two convertible-but-distinct copies end up in scope
   together and every unification against them fails confusingly. *)
Definition cpus_ptr (i : CPU) : mword 64 := mycpu_ret (cid_word_of i).

Lemma tp_ok_cid_of (i : CPU) : tp_ok (cid_word_of i).
Proof.
  unfold tp_ok, cid_word_of.
  pose proof (fin_to_nat_lt i) as Hlt. unfold NCPU in Hlt.
  assert (Hz : 0 <= Z.of_nat (fin_to_nat i) < 8).
  { split; [ apply Nat2Z.is_nonneg | ].
    change 8 with (Z.of_nat 8%nat). apply inj_lt. exact Hlt. }
  rewrite uint_unsigned pg_moi_unsigned bv_wrap_small;
    [ exact Hz | rewrite pg_modulus64; lia ].
Qed.

Lemma uint_cid_word_of (i : CPU) : uint (cid_word_of i) = Z.of_nat (fin_to_nat i).
Proof.
  pose proof (fin_to_nat_lt i) as Hlt. unfold NCPU in Hlt.
  unfold cid_word_of. rewrite uint_unsigned pg_moi_unsigned.
  apply bv_wrap_small. rewrite pg_modulus64.
  split; [ apply Nat2Z.is_nonneg | ].
  assert (Z.of_nat (fin_to_nat i) < Z.of_nat 8%nat) by (apply inj_lt; exact Hlt).
  lia.
Qed.

(* distinct harts have distinct [struct cpu] pointers *)
Lemma cpus_ptr_inj (i j : CPU) : cpus_ptr i = cpus_ptr j -> i = j.
Proof.
  intro Heq. apply (f_equal bv_unsigned) in Heq.
  unfold cpus_ptr in Heq.
  rewrite (mycpu_ret_unsigned _ (tp_ok_cid_of i)) in Heq.
  rewrite (mycpu_ret_unsigned _ (tp_ok_cid_of j)) in Heq.
  rewrite !uint_cid_word_of in Heq.
  apply fin_to_nat_inj. lia.
Qed.

(* a hart's [struct cpu] pointer is never the null the free lock records *)
Lemma cpus_ptr_nonzero (i : CPU) : eq_vec (zero_reg : mword 64) (cpus_ptr i) = false.
Proof. apply mycpu_ret_nonzero, tp_ok_cid_of. Qed.

(* the ambient hart id as a tp-register value.  mycpu()'s return for this
   hart is [mycpu_ret cid_word] = &cpus[cpu_id] = [cpus_ptr cpu_id]. *)

Lemma cpus_ptr_cid `{CID : CpuId} : cpus_ptr cpu_id = mycpu_ret cid_word.
Proof. reflexivity. Qed.

Lemma tp_ok_cid `{CID : CpuId} : tp_ok cid_word.
Proof. apply tp_ok_cid_of. Qed.

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
