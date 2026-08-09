(* ProcGeom.v -- struct proc / struct cpu geometry and the current-process
   resource.

   Pure layout facts shared by the proc-lock invariant (SchedCtx.v), the
   wakeup proof (ProofWakeup.v) and the myproc/sched/yield whole-function
   specs.  All per-CPU cell addresses are stated tp-indexed via [mycpu_ret
   tp0] (defined below), the same closed form the acquire/release/push_off/
   pop_off specs already use, so cells unify across call boundaries by name.

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
From iris.base_logic.lib Require Import gen_heap invariants ghost_var.
Require Import SailStdpp.Base SailStdpp.Operators_mwords SailStdpp.Values.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import RiscvPtsto RiscvLang RiscvExtras.
Require Export HartTp.   (* cid_word_of / cid_word live here now; EXPORTED so the
                            ~90 existing references through ProcGeom keep working *)
From Kernel Require KernelSyms.
Require Import KernelRvcDecode.
Local Open Scope Z_scope.




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

(* ... and the same three in the 12-bit DISPLACEMENT form a base-encoded
   [lw/sw/ld/sd rd,off(rs)] leaves behind.  ([p_parent]'s twin is
   [WaitInv.p_parent_sext], beside the resource that uses it.)  kexit is the
   first function to reach [state] and [xstate] through base rather than
   compressed encodings, and the first to compute [&p->cwd] with an [addi]. *)
Lemma p_state_sext (pa : mword 64) :
  add_vec pa (sign_extend' 64 (mword_of_int 24 : mword 12)) = p_state pa.
Proof.
  unfold p_state, state_off.
  apply (f_equal (add_vec pa)). apply bv_eq; vm_compute; reflexivity.
Qed.

Lemma p_xstate_sext (pa : mword 64) :
  add_vec pa (sign_extend' 64 (mword_of_int 44 : mword 12)) = p_xstate pa.
Proof.
  unfold p_xstate.
  apply (f_equal (add_vec pa)). apply bv_eq; vm_compute; reflexivity.
Qed.

Lemma p_cwd_sext (pa : mword 64) :
  add_vec pa (sign_extend' 64 (mword_of_int 336 : mword 12)) = p_cwd pa.
Proof.
  unfold p_cwd.
  apply (f_equal (add_vec pa)). apply bv_eq; vm_compute; reflexivity.
Qed.

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
  rewrite (moi64_small z ltac:(lia)).
  rewrite Z.shiftl_mul_pow2; [| lia]. change (2^3) with 8.
  rewrite (moi64_small (z * 8) ltac:(nia)).
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
  unfold p_ofile. rewrite po_addv_assoc.
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

(* USED IS IN HERE, and it is not a rounding error.  [USED] is a state a proc
   can be in with its lock RELEASED: kfork drops p->lock after allocproc so it
   can take wait_lock to set p->parent (taking wait_lock under p->lock inverts
   the lock order), and only re-acquires to store RUNNABLE.  During that window
   any table scan -- wakeup, kill, wait -- can acquire the slot's lock, so
   whatever the slot owns has to be IN the invariant, not in kfork's frame.

   And the record really is there: allocproc writes context.ra = forkret and
   context.sp = the kstack top, which is exactly why kfork can go live with a
   single store to p->state.  The "almost" against RUNNABLE is that the
   scheduler must not dispatch a USED proc -- enforced by the C's
   [if (p->state == RUNNABLE)], not by this guard. *)
Definition needs_ctx (st : mword 32) : bool :=
  bool_decide (st = RUNNABLE) || bool_decide (st = SLEEPING) ||
  bool_decide (st = USED).

Lemma needs_ctx_SLEEPING : needs_ctx SLEEPING = true.
Proof. vm_compute. reflexivity. Qed.

Lemma needs_ctx_RUNNABLE : needs_ctx RUNNABLE = true.
Proof. vm_compute. reflexivity. Qed.

Lemma needs_ctx_USED : needs_ctx USED = true.
Proof. vm_compute. reflexivity. Qed.

(* the one elimination form the three derived guards below all go through, so
   widening [needs_ctx] again costs exactly one case here. *)
Lemma needs_ctx_cases (st : mword 32) :
  needs_ctx st = true -> st = RUNNABLE \/ st = SLEEPING \/ st = USED.
Proof.
  rewrite /needs_ctx. intros Hn.
  apply orb_true_iff in Hn as [Hn|Hn]; [apply orb_true_iff in Hn as [Hn|Hn]|];
    apply bool_decide_eq_true_1 in Hn; auto.
Qed.

Lemma needs_ctx_RUNNING : needs_ctx RUNNING = false.
Proof. vm_compute. reflexivity. Qed.

(* THE THIRD flat state predicate the proc-lock invariant keys on (beside
   [needs_ctx] and [inv_dormant]): the states in which this slot's PARK
   RECEIPT ([park_own] below) is not out on loan.  While the proc is
   RUNNING its two receipt halves are elsewhere -- one in
   [SchedCtx.scheds_inv]'s slot for the hart running it, one with the
   running thread -- and at every other state both sit in [p->lock]. *)
Definition not_running (st : mword 32) : bool :=
  negb (bool_decide (st = RUNNING)).

(* ... and the USED cut-out.  Together with [not_running] this is [unclaimed]
   below: the states in which NO THREAD has claimed the proc, and so the lock
   owns both halves of the state mirror. *)
Definition not_used (st : mword 32) : bool :=
  negb (bool_decide (st = USED)).

Definition unclaimed (st : mword 32) : bool :=
  not_running st && not_used st.

Lemma unclaimed_UNUSED   : unclaimed UNUSED   = true.
Proof. vm_compute. reflexivity. Qed.
Lemma unclaimed_RUNNABLE : unclaimed RUNNABLE = true.
Proof. vm_compute. reflexivity. Qed.
Lemma unclaimed_SLEEPING : unclaimed SLEEPING = true.
Proof. vm_compute. reflexivity. Qed.
Lemma unclaimed_ZOMBIE   : unclaimed ZOMBIE   = true.
Proof. vm_compute. reflexivity. Qed.
Lemma unclaimed_RUNNING  : unclaimed RUNNING  = false.
Proof. vm_compute. reflexivity. Qed.
Lemma unclaimed_USED     : unclaimed USED     = false.
Proof. vm_compute. reflexivity. Qed.

(* ... and its complement, the fourth flat guard.  [p->lock] holds the raw
   context CELLS exactly while the proc is RUNNING: a running proc has no
   parked record ([needs_ctx] is what says "there is a resumable thread saved
   here"), but its context field still exists and something must own it.

   PUTTING IT IN THE LOCK RATHER THAN WITH THE RUNNING THREAD IS WHAT LETS A
   TRAP PREEMPT.  kerneltrap -> yield parks the interrupted thread, and
   parking needs those cells; held as an ordinary frame by whichever function
   was interrupted they would be unreachable from the handler, because a
   frame lives outside the handler's WP.  Taken from [p->lock] -- which yield
   acquires anyway -- they are simply there.  It is also the more faithful
   reading of the C: [p->context] IS protected by [p->lock], and [swtch] runs
   under that lock in both the save and the restore direction. *)
Definition is_running (st : mword 32) : bool :=
  bool_decide (st = RUNNING).

Lemma is_running_RUNNING : is_running RUNNING = true.
Proof. vm_compute. reflexivity. Qed.
Lemma is_running_RUNNABLE : is_running RUNNABLE = false.
Proof. vm_compute. reflexivity. Qed.
Lemma is_running_SLEEPING : is_running SLEEPING = false.
Proof. vm_compute. reflexivity. Qed.
Lemma is_running_UNUSED : is_running UNUSED = false.
Proof. vm_compute. reflexivity. Qed.
Lemma is_running_USED : is_running USED = false.
Proof. vm_compute. reflexivity. Qed.
Lemma is_running_ZOMBIE : is_running ZOMBIE = false.
Proof. vm_compute. reflexivity. Qed.

(* the two running guards are one boolean, so a lemma that already fixes
   [not_running] fixes this one too -- no new premise anywhere. *)
Lemma is_running_negb (st : mword 32) : is_running st = negb (not_running st).
Proof. rewrite /is_running /not_running negb_involutive. reflexivity. Qed.

Lemma is_running_of_needs_ctx (st : mword 32) :
  needs_ctx st = true -> is_running st = false.
Proof.
  intro H. apply needs_ctx_cases in H as [H|[H|H]]; subst; vm_compute; reflexivity.
Qed.

Lemma not_running_RUNNING : not_running RUNNING = false.
Proof. vm_compute. reflexivity. Qed.
Lemma not_running_UNUSED : not_running UNUSED = true.
Proof. vm_compute. reflexivity. Qed.
Lemma not_running_USED : not_running USED = true.
Proof. vm_compute. reflexivity. Qed.
Lemma not_running_SLEEPING : not_running SLEEPING = true.
Proof. vm_compute. reflexivity. Qed.
Lemma not_running_RUNNABLE : not_running RUNNABLE = true.
Proof. vm_compute. reflexivity. Qed.
Lemma not_running_ZOMBIE : not_running ZOMBIE = true.
Proof. vm_compute. reflexivity. Qed.

(* a parked state is not RUNNING (refutes sched's "sched RUNNING" panic arm). *)
Lemma needs_ctx_not_RUNNING (st : mword 32) :
  needs_ctx st = true -> st <> RUNNING.
Proof.
  intros Hn ->.
  rewrite needs_ctx_RUNNING in Hn. discriminate.
Qed.

(* the two guard classes are disjoint: a state that owns a saved context
   does not also own the dormant private block. *)
Lemma inv_dormant_of_needs_ctx (st : mword 32) :
  needs_ctx st = true -> inv_dormant st = false.
Proof.
  intros Hn. apply needs_ctx_cases in Hn as [Hn|[Hn|Hn]]; subst.
  - exact inv_dormant_RUNNABLE.
  - exact inv_dormant_SLEEPING.
  - exact inv_dormant_USED.
Qed.

(* every state that owns a saved context is not RUNNING *)
Lemma not_running_of_needs_ctx (st : mword 32) :
  needs_ctx st = true -> not_running st = true.
Proof.
  intros Hn. rewrite /not_running.
  rewrite (bool_decide_eq_false_2 (st = RUNNING)); [done|].
  exact (needs_ctx_not_RUNNING st Hn).
Qed.

(* THE STATES A THREAD MAY PARK INTO -- what sched() demands of the state its
   caller has already stored.  Two of them are the resumable ones
   ([needs_ctx]: yield's RUNNABLE, sleep's SLEEPING); the third is ZOMBIE,
   where kexit() parks FOREVER.  A zombie's saved context is never resumed --
   the scheduler dispatches only RUNNABLE procs -- so what its lock slot owns
   is the dormant block, not a record; the difference is entirely in what the
   crossing carries ([SchedCtx.park_pay]) and what the reclaiming scheduler
   rebuilds ([SchedCtx.proc_slots_park_gen]), which is why this predicate,
   rather than [needs_ctx], is sched's premise. *)
(* [not_used] IS PART OF THIS, and has to be: [needs_ctx] covers USED (a
   USED proc's slot owns a real parked record), but a thread cannot PARK at
   USED -- it is the state kfork leaves behind while the child has never
   run.  Without the cut-out, sched's premise would admit a park whose
   state is claimed, and the reclaiming scheduler could not put the state
   mirror back whole. *)
Definition park_ok (st : mword 32) : bool :=
  (needs_ctx st || bool_decide (st = ZOMBIE)) && not_used st.

Lemma park_ok_RUNNABLE : park_ok RUNNABLE = true.
Proof. vm_compute. reflexivity. Qed.
Lemma park_ok_SLEEPING : park_ok SLEEPING = true.
Proof. vm_compute. reflexivity. Qed.
Lemma park_ok_ZOMBIE : park_ok ZOMBIE = true.
Proof. vm_compute. reflexivity. Qed.

Lemma park_ok_of_needs_ctx (st : mword 32) :
  needs_ctx st = true -> not_used st = true -> park_ok st = true.
Proof. intros Hn Hu. rewrite /park_ok Hn Hu. reflexivity. Qed.

(* what the reclaiming scheduler needs: a parked state is unclaimed, so the
   lock's share of the mirror is the whole variable again. *)
Lemma park_ok_unclaimed (st : mword 32) :
  park_ok st = true -> unclaimed st = true.
Proof.
  rewrite /park_ok /unclaimed. intros H.
  apply andb_true_iff in H as [Hd Hu]. rewrite Hu andb_true_r.
  apply orb_true_iff in Hd as [Hd|Hd].
  - exact (not_running_of_needs_ctx st Hd).
  - apply bool_decide_eq_true_1 in Hd. subst st. exact not_running_ZOMBIE.
Qed.

(* the case analysis every consumer of [park_ok] does: a parking state either
   keeps a resumable record, or IS the zombie state. *)
Lemma park_ok_cases (st : mword 32) :
  park_ok st = true -> needs_ctx st = true \/ st = ZOMBIE.
Proof.
  rewrite /park_ok. intros H.
  apply andb_true_iff in H as [H _]. apply orb_true_iff in H as [H|H].
  - by left.
  - right. by apply bool_decide_eq_true in H.
Qed.

(* a parking state is not RUNNING (this is what refutes sched's
   "sched running" panic arm, at either kind of park). *)
Lemma park_ok_not_RUNNING (st : mword 32) :
  park_ok st = true -> st <> RUNNING.
Proof.
  intros H. apply park_ok_cases in H as [H| ->].
  - exact (needs_ctx_not_RUNNING st H).
  - vm_compute. discriminate.
Qed.

Lemma not_running_of_park_ok (st : mword 32) :
  park_ok st = true -> not_running st = true.
Proof.
  intros H. rewrite /not_running.
  rewrite (bool_decide_eq_false_2 (st = RUNNING)); [done|].
  exact (park_ok_not_RUNNING st H).
Qed.

(* p++ : &proc[k] + sizeof(proc) = &proc[k+1].  The addi's 12-bit immediate
   [360] sign-extends to the same 64-bit constant, and mword addition agrees
   with Z addition mod 2^64 (via [avi_mword]). *)
Lemma proc_addr_succ (k : nat) :
  add_vec (proc_addr k) (sign_extend' 64 (mword_of_int proc_size : mword 12)) = proc_addr (S k).
Proof.
  unfold proc_addr. rewrite po_addv_assoc.
  assert (Hsx : sign_extend' 64 (mword_of_int proc_size : mword 12) = (mword_of_int proc_size : mword 64))
    by (apply bv_eq; vm_compute; reflexivity).
  rewrite Hsx. f_equal.
  change (add_vec (mword_of_int (proc_size * Z.of_nat k) : mword 64) (mword_of_int proc_size))
    with (add_vec_int (mword_of_int (proc_size * Z.of_nat k) : mword 64) proc_size).
  rewrite avi_mword. f_equal. rewrite Nat2Z.inj_succ. ring.
Qed.

(* closed forms as unsigned integers (no wraparound in the array range).

   THE RANGE IS CLOSED, NOT OPEN.  [&proc[NPROC]] is a real address -- it is
   the end sentinel every proc[] scan's exit test compares against (wakeup,
   kkill, allocproc, reparent all load it into a register) -- so the fact has
   to hold at [i = NPROC] too, and it does: the array ends far below 2^64.
   [proc_addr_unsigned] below is the open-range restatement, kept so the
   existing call sites do not churn. *)
Lemma proc_addr_unsigned_le (i : nat) :
  (i <= NPROC)%nat ->
  bv_unsigned (proc_addr i) = KernelSyms.proc + proc_size * Z.of_nat i.
Proof.
  intro Hi. unfold NPROC in Hi.
  unfold proc_addr, proc_base.
  rewrite add_vec64_unsigned !moi64_unsigned.
  rewrite bv_wrap_add_idemp_l bv_wrap_add_idemp_r.
  apply bv_wrap_small.
  unfold KernelSyms.proc, proc_size. rewrite bv_modulus64. lia.
Qed.

Lemma proc_addr_unsigned (i : nat) :
  (i < NPROC)%nat ->
  bv_unsigned (proc_addr i) = KernelSyms.proc + proc_size * Z.of_nat i.
Proof. intro Hi. apply proc_addr_unsigned_le. lia. Qed.

Lemma p_context_unsigned (i : nat) :
  (i < NPROC)%nat ->
  bv_unsigned (p_context (proc_addr i))
  = KernelSyms.proc + proc_size * Z.of_nat i + context_off.
Proof.
  intro Hi. assert (Hi' := Hi). unfold NPROC in Hi'.
  unfold p_context.
  rewrite add_vec64_unsigned (proc_addr_unsigned i Hi) moi64_unsigned.
  rewrite bv_wrap_add_idemp_r.
  apply bv_wrap_small.
  unfold KernelSyms.proc, proc_size, context_off. rewrite bv_modulus64. lia.
Qed.

(* proc addresses are injective on the array range, END SENTINEL INCLUDED --
   which is what a scan's exit test needs: "the cursor equals [&proc[NPROC]]"
   is only worth anything if it implies the cursor's INDEX is [NPROC], and
   the open-range statement below cannot say that about [NPROC] itself. *)
Lemma proc_addr_inj_le (i j : nat) :
  (i <= NPROC)%nat -> (j <= NPROC)%nat ->
  proc_addr i = proc_addr j -> i = j.
Proof.
  intros Hi Hj Heq.
  apply (f_equal bv_unsigned) in Heq.
  rewrite (proc_addr_unsigned_le i Hi) (proc_addr_unsigned_le j Hj) in Heq.
  unfold proc_size in Heq. lia.
Qed.

Lemma proc_addr_inj (i j : nat) :
  (i < NPROC)%nat -> (j < NPROC)%nat ->
  proc_addr i = proc_addr j -> i = j.
Proof. intros Hi Hj. apply proc_addr_inj_le; lia. Qed.

(* ---- THE ofile SCAN'S EXIT TEST -------------------------------------
   kexit walks [&p->ofile[0]] by 8 and stops when the cursor equals
   [&p->cwd].  That is not a coincidence to be worked around: [ofile] runs
   208..335 and [cwd] sits at 336, so &p->ofile[NOFILE] IS &p->cwd, and the
   [beq s1,s2] at +0x3a is literally "the cursor has walked off the end".
   [p_ofile_end] is that identity, and [p_ofile_end_inj] is what the loop
   needs of it -- the exit test is only worth anything if reaching it pins
   the cursor's INDEX at NOFILE.  Both are stated at [proc_addr i], where
   the base has a closed unsigned form, exactly as [proc_addr_inj_le] is. *)
Lemma p_ofile_end (pa : mword 64) : p_ofile pa NOFILE = p_cwd pa.
Proof.
  unfold p_ofile, p_cwd, NOFILE.
  apply (f_equal (add_vec pa)). apply bv_eq; vm_compute; reflexivity.
Qed.

Lemma p_ofile_unsigned (i fd : nat) :
  (i < NPROC)%nat -> (fd <= NOFILE)%nat ->
  bv_unsigned (p_ofile (proc_addr i) fd)
  = KernelSyms.proc + proc_size * Z.of_nat i + (208 + 8 * Z.of_nat fd).
Proof.
  intros Hi Hfd. assert (Hi' := Hi). unfold NPROC in Hi'.
  unfold NOFILE in Hfd. unfold p_ofile.
  rewrite add_vec64_unsigned (proc_addr_unsigned i Hi) moi64_unsigned.
  rewrite bv_wrap_add_idemp_r.
  apply bv_wrap_small.
  unfold KernelSyms.proc, proc_size. rewrite bv_modulus64. lia.
Qed.

Lemma p_ofile_end_inj (i fd : nat) :
  (i < NPROC)%nat -> (fd <= NOFILE)%nat ->
  p_ofile (proc_addr i) fd = p_cwd (proc_addr i) -> fd = NOFILE.
Proof.
  intros Hi Hfd Heq.
  rewrite -(p_ofile_end (proc_addr i)) in Heq.
  apply (f_equal bv_unsigned) in Heq.
  rewrite (p_ofile_unsigned i fd Hi Hfd) in Heq.
  rewrite (p_ofile_unsigned i NOFILE Hi ltac:(lia)) in Heq.
  unfold NOFILE in Heq |- *. lia.
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

(* [mycpu_ret tp0] is &cpus[tp0], in the EXACT closed form mycpu()'s five
   instructions leave in a0 -- [c.mv a5,tp] / [sext.w] / [c.slli a5,7] build
   [mycpu_a5], and the [auipc a0,0x11] / [addi a0,a0,-1404] pair materializes
   &cpus.  Every per-CPU cell address below, and every acquire / release /
   push_off / pop_off / myproc contract, is stated in this form, so cells unify
   by name across call boundaries with no arithmetic at the seam.
   [mycpu_ret_unsigned] below is what turns it back into a plain address. *)
Definition mycpu_a5 (tp0 : mword 64) : mword 64 :=
  shift_bits_left
    (sign_extend' 64 (subrange_vec_dec
       (add_vec (add_vec zero_reg tp0)
                (sign_extend' 64 (sign_extend' 12 (mword_of_int 0 : mword 6)))) 31 0))
    (subrange_vec_dec (mword_of_int 7 : mword 6) (Z.sub log2_xlen 1) 0).

Definition mycpu_ret (tp0 : mword 64) : mword 64 :=
  add_vec
    (add_vec
       (add_vec (add_vec_int (mword_of_int KernelSyms.mycpu : mword 64) 14)
                (auipc_off (mword_of_int 0x11 : mword 20)))
       (sign_extend' 64 (mword_of_int 0xa84 : mword 12)))
    (mycpu_a5 tp0).

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
  rewrite add_vec64_unsigned (mycpu_ret_unsigned tp0 Htp) in Heq.
  assert (H8 : bv_unsigned (sign_extend' 64 (mword_of_int 8 : mword 12) : mword 64) = 8)
    by (vm_compute; reflexivity).
  rewrite H8 in Heq.
  rewrite (p_context_unsigned j Hj) in Heq.
  destruct Htp as [Ht0 Ht8].
  assert (Hlhs : bv_wrap 64 (KernelSyms.cpus + 128 * uint tp0 + 8)
                 = KernelSyms.cpus + 128 * uint tp0 + 8).
  { apply bv_wrap_small. unfold KernelSyms.cpus. rewrite bv_modulus64. lia. }
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
  rewrite uint_unsigned moi64_unsigned bv_wrap_small;
    [ exact Hz | rewrite bv_modulus64; lia ].
Qed.

Lemma uint_cid_word_of (i : CPU) : uint (cid_word_of i) = Z.of_nat (fin_to_nat i).
Proof.
  pose proof (fin_to_nat_lt i) as Hlt. unfold NCPU in Hlt.
  unfold cid_word_of. rewrite uint_unsigned moi64_unsigned.
  apply bv_wrap_small. rewrite bv_modulus64.
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

Lemma cpus_ptr_cid `{GEN : GenId} `{CID : CpuId} : cpus_ptr cpu_id = mycpu_ret cid_word.
Proof. reflexivity. Qed.

Lemma tp_ok_cid `{GEN : GenId} `{CID : CpuId} : tp_ok cid_word.
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
  Context `{GEN : GenId} `{CID : CpuId}.

  Definition cur_proc (p : mword 64) : iProp Σ :=
    a_cpu_proc cid_word ↦₈ p.

  Global Instance cur_proc_timeless p : Timeless (cur_proc p).
  Proof. rewrite /cur_proc /word_pointsto /mem_pointsto. apply _. Qed.
End CurProc.

(* ===================================================================== *)
(* THE SHARED HALF OF [cpus[h].proc], AND THE PER-PROC PARK RECEIPT.      *)
(*                                                                        *)
(* Both belong to the global parked-scheduler protocol [SchedCtx.         *)
(* scheds_inv], but they are stated HERE, at the bottom of the proc/cpu   *)
(* geometry, because [IntrDefs.cpu_cells] (far below SchedCtx) has to     *)
(* name the half, and [SchedCtx.proc_lock_res] the receipt.               *)
(*                                                                        *)
(* [cpu_proc_half h p]: HALF of [cpus[h].proc], holding [p].  The other   *)
(* half is permanently owned by [scheds_inv]'s slot for hart [h].  This    *)
(* is the ONLY channel by which the logic can learn "the proc running on  *)
(* hart h is p" -- exactly the fact myproc() reads -- and halving the     *)
(* cell is MANDATORY rather than cosmetic: stated against a FULL cell the *)
(* take-out move is vacuous (fractions 1 + 1/2), which                    *)
(* [SchedCtx.cpu_own_full_is_vacuous] proves outright.                    *)
(*                                                                        *)
(* [park_own j q r]: fraction [q] of proc j's park receipt, at value [r].  *)
(*   [r = true]  -- hart h's scheduler record is RESIDENT in slot h;       *)
(*   [r = false] -- it is checked out by the thread running proc j (or     *)
(*                  not yet deposited by a freshly dispatched one).        *)
(* KEYED BY THE PROC, NOT BY THE HART, which is what makes the            *)
(* entitlement hart-free: proc j is dispatched by whatever hart's         *)
(* scheduler picked it up, and after a migration it is still proc j.  The *)
(* name is CANONICAL ([RiscvPtsto.park_name]) for the same reason         *)
(* [sie_name] is: the receipt is named inside [proc_lock_res], hence      *)
(* inside [procs_inv], and a [γk] parameter there would have to be        *)
(* threaded through every file that mentions [procs_inv].                 *)
(* ===================================================================== *)
Section ParkGhost.
  Context `{!riscvGS Σ}.

  Definition cpu_proc_half (h : CPU) (p : mword 64) : iProp Σ :=
    (a_cpu_proc (cid_word_of h) ↦₈{DfracOwn (1/2)} p)%I.

  Global Instance cpu_proc_half_timeless h p : Timeless (cpu_proc_half h p).
  Proof. rewrite /cpu_proc_half /word_pointsto /mem_pointsto. apply _. Qed.

  Lemma cpu_proc_halve (h : CPU) (p : mword 64) :
    a_cpu_proc (cid_word_of h) ↦₈ p ⊣⊢ cpu_proc_half h p ∗ cpu_proc_half h p.
  Proof. rewrite /cpu_proc_half -word_pointsto_frac_split Qp.div_2 //. Qed.

  Lemma cpu_proc_half_agree (h : CPU) (p p' : mword 64) :
    cpu_proc_half h p -∗ cpu_proc_half h p' -∗ ⌜p = p'⌝.
  Proof. iIntros "H1 H2". iApply (word_pointsto_agree with "H1 H2"). Qed.

  (* a FULL word cell excludes every further fraction of the same cell --
     what makes "the invariant permanently holds a half" incompatible with
     any resource still stating the cell in full. *)
  Lemma word_pointsto_full_excl (a : Arch.pa) (dq : dfrac) (w w' : mword 64) :
    a ↦₈ w -∗ a ↦₈{dq} w' -∗ False.
  Proof.
    iIntros "H1 H2".
    iDestruct (word_pointsto_bytes with "H1") as "Hb1".
    iDestruct (word_pointsto_bytes with "H2") as "Hb2".
    cbn [seq]. iDestruct "Hb1" as "[Hc1 _]". iDestruct "Hb2" as "[Hc2 _]".
    iDestruct (mem_pointsto_ne with "Hc1 Hc2") as %Hne. done.
  Qed.

  Definition park_own (j : nat) (q : Qp) (r : bool) : iProp Σ :=
    ghost_var (park_name j) q r.

  Definition park_hlf (j : nat) (r : bool) : iProp Σ := park_own j (1/2) r.
  Definition park_full (j : nat) (r : bool) : iProp Σ := park_own j 1 r.

  Global Instance park_own_timeless j q r : Timeless (park_own j q r).
  Proof. rewrite /park_own. apply _. Qed.

  Lemma park_own_agree (j : nat) (q1 q2 : Qp) (r1 r2 : bool) :
    park_own j q1 r1 -∗ park_own j q2 r2 -∗ ⌜r1 = r2⌝.
  Proof.
    iIntros "Hg1 Hg2".
    by iDestruct (ghost_var_agree with "Hg1 Hg2") as %->.
  Qed.

  Local Lemma ghost_var_halve {A : Type} `{!ghost_varG Σ A} (γ : gname) (r : A) :
    ghost_var γ 1 r ⊣⊢ ghost_var γ (1/2) r ∗ ghost_var γ (1/2) r.
  Proof.
    iSplit.
    - iIntros "H". iApply (ghost_var_split γ r (1/2) (1/2)).
      rewrite Qp.half_half. iExact "H".
    - iIntros "[H1 H2]". iCombine "H1 H2" as "H".
      try rewrite Qp.half_half. iExact "H".
  Qed.

  Lemma park_split (j : nat) (r : bool) :
    park_full j r ⊣⊢ park_hlf j r ∗ park_hlf j r.
  Proof. rewrite /park_full /park_hlf /park_own ghost_var_halve //. Qed.

  Lemma park_update (j : nat) (r r' : bool) :
    park_hlf j r -∗ park_hlf j r ==∗ park_hlf j r' ∗ park_hlf j r'.
  Proof.
    rewrite /park_hlf /park_own. iIntros "Hg1 Hg2".
    iMod (ghost_var_update_halves r' with "Hg1 Hg2") as "[$ $]". done.
  Qed.

  (* THE RECEIPT SPELLED AT A PROC ADDRESS.  [SchedCtx.proc_slots] is keyed
     on the proc's ADDRESS, not on its array index, so the receipt's home in
     the lock has to be too -- and giving [proc_slots] / [proc_lock_res] an
     extra index argument would change the arity of [procs_inv] and of every
     file that mentions it.  [proc_addr] is injective on the array range
     ([proc_addr_inj]), so the two spellings are interchangeable there. *)
  Definition park_at (pa : mword 64) (q : Qp) (r : bool) : iProp Σ :=
    (∃ j : nat, ⌜pa = proc_addr j /\ (j < NPROC)%nat⌝ ∗ park_own j q r)%I.

  Definition park_at_full (pa : mword 64) (r : bool) : iProp Σ :=
    park_at pa 1 r.

  Lemma park_at_intro (j : nat) (q : Qp) (r : bool) :
    (j < NPROC)%nat -> park_own j q r -∗ park_at (proc_addr j) q r.
  Proof. iIntros (Hj) "Hg". iExists j. iFrame "Hg". done. Qed.

  Lemma park_at_elim (j : nat) (q : Qp) (r : bool) :
    (j < NPROC)%nat -> park_at (proc_addr j) q r -∗ park_own j q r.
  Proof.
    iIntros (Hj) "(%j' & [%Hpa %Hj'] & Hg)".
    rewrite (_ : j' = j); [iExact "Hg"|].
    exact (proc_addr_inj j' j Hj' Hj (eq_sym Hpa)).
  Qed.

  Lemma park_at_full_intro (j : nat) (r : bool) :
    (j < NPROC)%nat -> park_full j r -∗ park_at_full (proc_addr j) r.
  Proof. exact (park_at_intro j 1 r). Qed.

  Lemma park_at_full_elim (j : nat) (r : bool) :
    (j < NPROC)%nat -> park_at_full (proc_addr j) r -∗ park_full j r.
  Proof. exact (park_at_elim j 1 r). Qed.
  (* ==================================================================== *)
  (* THE PER-PROC STATE MIRROR (design/proc-struct.md, the state ghost).    *)
  (*                                                                       *)
  (* A [ghost_var] carrying [p->state]'s value, in two halves.  The proc    *)
  (* lock invariant owns half #1, tied to the cell; half #2 is lock-        *)
  (* resident on [unclaimed] and held by the claiming thread otherwise.     *)
  (* Since a ghost_var cannot move on half alone and the tie forbids moving *)
  (* the cell without the ghost, THE RIGHT TO WRITE [p->state] IS EXACTLY   *)
  (* OWNERSHIP OF HALF #2.                                                  *)
  (*                                                                       *)
  (* It carries the whole 32-bit value rather than a guard class.  The tie  *)
  (* to the cell is then a plain equality, and the two scanners that write  *)
  (* state without being the claimant (wakeup, kill) read [SLEEPING] off    *)
  (* the cell and get the ghost value for free.                            *)
  (* ==================================================================== *)
  Definition pstate_own (j : nat) (q : Qp) (st : mword 32) : iProp Σ :=
    ghost_var (pstate_name j) q st.

  Definition pstate_hlf (j : nat) (st : mword 32) : iProp Σ := pstate_own j (1/2) st.
  Definition pstate_full (j : nat) (st : mword 32) : iProp Σ := pstate_own j 1 st.

  Global Instance pstate_own_timeless j q st : Timeless (pstate_own j q st).
  Proof. rewrite /pstate_own. apply _. Qed.

  Lemma pstate_own_agree (j : nat) (q1 q2 : Qp) (st1 st2 : mword 32) :
    pstate_own j q1 st1 -∗ pstate_own j q2 st2 -∗ ⌜st1 = st2⌝.
  Proof.
    iIntros "Hg1 Hg2".
    by iDestruct (ghost_var_agree with "Hg1 Hg2") as %->.
  Qed.

  Lemma pstate_split (j : nat) (st : mword 32) :
    pstate_full j st ⊣⊢ pstate_hlf j st ∗ pstate_hlf j st.
  Proof. rewrite /pstate_full /pstate_hlf /pstate_own ghost_var_halve //. Qed.

  (* THE WRITE.  Both halves, which is the whole point: no lock holder can
     move [p->state] without the claimant's half. *)
  Lemma pstate_update (j : nat) (st st' : mword 32) :
    pstate_hlf j st -∗ pstate_hlf j st ==∗ pstate_hlf j st' ∗ pstate_hlf j st'.
  Proof.
    rewrite /pstate_hlf /pstate_own. iIntros "Hg1 Hg2".
    iMod (ghost_var_update_halves st' with "Hg1 Hg2") as "[$ $]". done.
  Qed.

  (* the address-keyed spelling, for the same reason [park_at] has one:
     [SchedCtx.proc_slots] is keyed on the proc's ADDRESS, not its index. *)
  Definition pstate_at (pa : mword 64) (q : Qp) (st : mword 32) : iProp Σ :=
    (∃ j : nat, ⌜pa = proc_addr j /\ (j < NPROC)%nat⌝ ∗ pstate_own j q st)%I.

  Definition pstate_at_hlf (pa : mword 64) (st : mword 32) : iProp Σ :=
    pstate_at pa (1/2) st.

  Lemma pstate_at_intro (j : nat) (q : Qp) (st : mword 32) :
    (j < NPROC)%nat -> pstate_own j q st -∗ pstate_at (proc_addr j) q st.
  Proof. iIntros (Hj) "Hg". iExists j. iFrame "Hg". done. Qed.

  Lemma pstate_at_elim (j : nat) (q : Qp) (st : mword 32) :
    (j < NPROC)%nat -> pstate_at (proc_addr j) q st -∗ pstate_own j q st.
  Proof.
    iIntros (Hj) "(%j' & [%Hpa %Hj'] & Hg)".
    rewrite (_ : j' = j); [iExact "Hg"|].
    exact (proc_addr_inj j' j Hj' Hj (eq_sym Hpa)).
  Qed.

  (* ==================================================================== *)
  (* WHAT THE PROC LOCK OWNS OF THE MIRROR: half #1 always -- the tie to   *)
  (* the [p->state] cell -- plus half #2 exactly on [unclaimed].  So on an *)
  (* unclaimed state the lock has the WHOLE variable and can move it       *)
  (* alone; on a claimed one it has half and the claimant must bring the   *)
  (* other.  The four lemmas below are the only moves the C makes.         *)
  (* ==================================================================== *)
  Definition pstate_lock (pa : mword 64) (st : mword 32) : iProp Σ :=
    (pstate_at_hlf pa st ∗
     (if unclaimed st then pstate_at_hlf pa st else emp))%I.

  Local Lemma pstate_lock_whole (pa : mword 64) (st : mword 32) :
    unclaimed st = true ->
    pstate_lock pa st ⊣⊢ pstate_at_hlf pa st ∗ pstate_at_hlf pa st.
  Proof. intros Hu. rewrite /pstate_lock Hu //. Qed.

  (* the address-keyed update, once: both halves in, both halves out. *)
  Local Lemma pstate_at_update (pa : mword 64) (st st' : mword 32) :
    pstate_at_hlf pa st -∗ pstate_at_hlf pa st ==∗
    pstate_at_hlf pa st' ∗ pstate_at_hlf pa st'.
  Proof.
    iIntros "(%j & [%Hpa %Hj] & Hg1) (%j' & [%Hpa' %Hj'] & Hg2)".
    assert (Hjj : j' = j)
      by exact (proc_addr_inj j' j Hj' Hj (eq_trans (eq_sym Hpa') Hpa)).
    subst j'.
    iMod (pstate_update j st st' with "Hg1 Hg2") as "[Hg1 Hg2]".
    iModIntro. iSplitL "Hg1"; iExists j; by iFrame.
  Qed.

  (* ==================================================================== *)
  (* THE RUNNING CLAIM: what a thread carries to say "I am proc j, running". *)
  (*                                                                       *)
  (* Two things with identical lifetimes and identical travel: the park     *)
  (* receipt (the scheduler's record for the hart running j is in its box)  *)
  (* and half #2 of j's state mirror (the right to change j's state).  Both *)
  (* are issued at dispatch, both are spent at a park, and both must reach  *)
  (* yield / sleep / exit -- and so, eventually, a PREEMPTING kerneltrap.   *)
  (*                                                                       *)
  (* Named as ONE bundle so that every function between here and sleep      *)
  (* mentions the concept rather than its parts: re-homing the pieces (the  *)
  (* record into [sie_arm], the park receipt away entirely) then changes    *)
  (* this definition and the handful of places that OPEN it, not the ~60    *)
  (* files that merely pass it through.                                     *)
  (* ==================================================================== *)
  Definition running_claim (j : nat) : iProp Σ :=
    (park_hlf j true ∗ pstate_hlf j RUNNING)%I.

  Lemma running_claim_split (j : nat) :
    running_claim j ⊣⊢ park_hlf j true ∗ pstate_hlf j RUNNING.
  Proof. done. Qed.

  (* WHAT A LOCK HOLDER HAS: the WHOLE variable, at every state.  On an
     unclaimed state that is just [pstate_lock]; on a claimed one it is the
     lock's half #1 plus the claimant's half #2, which the holder is by
     definition also carrying (it claimed the proc, or it is about to hand
     the claim on).  So the swtch payload [SchedCtx.proc_held] carries this
     and the split happens at release. *)
  Definition pstate_whole (pa : mword 64) (st : mword 32) : iProp Σ :=
    pstate_at pa 1 st.

  Lemma pstate_whole_split (pa : mword 64) (st : mword 32) :
    pstate_whole pa st ⊣⊢
    pstate_lock pa st ∗ (if unclaimed st then emp else pstate_at_hlf pa st).
  Proof.
    rewrite /pstate_whole /pstate_lock /pstate_at_hlf /pstate_at.
    destruct (unclaimed st).
    - iSplit.
      + iIntros "(%j & [%Hpa %Hj] & Hg)".
        rewrite /pstate_own ghost_var_halve. iDestruct "Hg" as "[Hg1 Hg2]".
        iSplitL; [| done]. iSplitL "Hg1"; iExists j; by iFrame.
      + iIntros "[[(%j & [%Hpa %Hj] & Hg1) (%j' & [%Hpa' %Hj'] & Hg2)] _]".
        assert (Hjj : j' = j)
          by exact (proc_addr_inj j' j Hj' Hj (eq_trans (eq_sym Hpa') Hpa)).
        subst j'. iExists j. iSplitR; [done|].
        rewrite /pstate_own ghost_var_halve. iFrame "Hg1 Hg2".
    - iSplit.
      + iIntros "(%j & [%Hpa %Hj] & Hg)".
        rewrite /pstate_own ghost_var_halve. iDestruct "Hg" as "[Hg1 Hg2]".
        iSplitR "Hg2"; [iSplitL "Hg1"; [| done] |]; iExists j; by iFrame.
      + iIntros "[[(%j & [%Hpa %Hj] & Hg1) _] (%j' & [%Hpa' %Hj'] & Hg2)]".
        assert (Hjj : j' = j)
          by exact (proc_addr_inj j' j Hj' Hj (eq_trans (eq_sym Hpa') Hpa)).
        subst j'. iExists j. iSplitR; [done|].
        rewrite /pstate_own ghost_var_halve. iFrame "Hg1 Hg2".
  Qed.

  (* the whole variable moves with no side conditions at all -- which is why
     every state change is stated on the HELD form and the guard only shows
     up where the lock is released. *)
  Lemma pstate_whole_update (pa : mword 64) (st st' : mword 32) :
    pstate_whole pa st ==∗ pstate_whole pa st'.
  Proof.
    iIntros "(%j & [%Hpa %Hj] & Hg)".
    rewrite /pstate_own. iMod (ghost_var_update st' with "Hg") as "Hg".
    iModIntro. iExists j. by iFrame.
  Qed.

  (* MOVE 1 -- an unclaimed state to another: the lock alone.  This is
     wakeup's and kill's SLEEPING -> RUNNABLE, the two writes the C makes
     without being the claimant (both read the cell first). *)
  Lemma pstate_lock_write (pa : mword 64) (st st' : mword 32) :
    unclaimed st = true -> unclaimed st' = true ->
    pstate_lock pa st ==∗ pstate_lock pa st'.
  Proof.
    intros Hu Hu'. rewrite (pstate_lock_whole pa st Hu) /pstate_lock Hu'.
    iIntros "[H1 H2]". by iApply (pstate_at_update with "H1 H2").
  Qed.

  (* MOVE 2 -- ISSUING the claim: the scheduler's RUNNABLE -> RUNNING and
     allocproc's UNUSED -> USED.  The lock keeps the tie and hands half #2
     to the thread that now owns the right to change the state. *)
  Lemma pstate_lock_claim (pa : mword 64) (st st' : mword 32) :
    unclaimed st = true -> unclaimed st' = false ->
    pstate_lock pa st ==∗ pstate_lock pa st' ∗ pstate_at_hlf pa st'.
  Proof.
    intros Hu Hu'. rewrite (pstate_lock_whole pa st Hu) /pstate_lock Hu'.
    iIntros "[H1 H2]".
    iMod (pstate_at_update with "H1 H2") as "[$ $]". by iFrame.
  Qed.

  (* MOVE 3 -- RETURNING it: yield's RUNNING -> RUNNABLE, sleep's
     RUNNING -> SLEEPING, kexit's RUNNING -> ZOMBIE, kfork's
     USED -> RUNNABLE.  The claimant spends half #2 and the lock is whole
     again. *)
  Lemma pstate_lock_release (pa : mword 64) (st st' : mword 32) :
    unclaimed st = false -> unclaimed st' = true ->
    pstate_lock pa st -∗ pstate_at_hlf pa st ==∗ pstate_lock pa st'.
  Proof.
    intros Hu Hu'. rewrite /pstate_lock Hu Hu'.
    iIntros "[H1 _] H2". by iApply (pstate_at_update with "H1 H2").
  Qed.

  (* MOVE 4 -- claim to claim, the claimant keeping it: freeproc's
     USED -> UNUSED runs inside kfork's failure path, which still holds
     half #2, so state it generally. *)
  Lemma pstate_lock_rebind (pa : mword 64) (st st' : mword 32) :
    unclaimed st = false -> unclaimed st' = false ->
    pstate_lock pa st -∗ pstate_at_hlf pa st ==∗
    pstate_lock pa st' ∗ pstate_at_hlf pa st'.
  Proof.
    intros Hu Hu'. rewrite /pstate_lock Hu Hu'.
    iIntros "[H1 _] H2".
    iMod (pstate_at_update with "H1 H2") as "[$ $]". by iFrame.
  Qed.

  (* AND THE READ THAT COSTS NOTHING.  Presenting half #2 at a lock proves
     both that the state is what the half says and that it is a CLAIMED one
     -- if it were unclaimed the lock would hold the whole variable and a
     third half would be invalid.  This is what lets yield/sleep/exit learn
     [st = RUNNING], and kfork [st = USED], without reading the cell. *)
  Lemma pstate_lock_claimed (pa : mword 64) (st st' : mword 32) :
    pstate_lock pa st -∗ pstate_at_hlf pa st' -∗
    ⌜ st = st' /\ unclaimed st = false ⌝.
  Proof.
    iIntros "Hl Hh".
    destruct (unclaimed st) eqn:Hu.
    - rewrite (pstate_lock_whole pa st Hu).
      iDestruct "Hl" as "[(%j & [%Hpa %Hj] & Hg1) (%j2 & [%Hpa2 %Hj2] & Hg2)]".
      iDestruct "Hh" as "(%j3 & [%Hpa3 %Hj3] & Hg3)".
      assert (H2 : j2 = j)
        by exact (proc_addr_inj j2 j Hj2 Hj (eq_trans (eq_sym Hpa2) Hpa)).
      assert (H3 : j3 = j)
        by exact (proc_addr_inj j3 j Hj3 Hj (eq_trans (eq_sym Hpa3) Hpa)).
      subst j2 j3.
      iCombine "Hg1 Hg2" as "Hg".
      rewrite /pstate_hlf /pstate_own.
      by iDestruct (ghost_var_valid_2 with "Hg Hg3") as %[Hq _].
    - rewrite /pstate_lock Hu.
      iDestruct "Hl" as "[(%j & [%Hpa %Hj] & Hg1) _]".
      iDestruct "Hh" as "(%j3 & [%Hpa3 %Hj3] & Hg3)".
      assert (H3 : j3 = j)
        by exact (proc_addr_inj j3 j Hj3 Hj (eq_trans (eq_sym Hpa3) Hpa)).
      subst j3.
      iDestruct (pstate_own_agree with "Hg1 Hg3") as %->. done.
  Qed.
End ParkGhost.
