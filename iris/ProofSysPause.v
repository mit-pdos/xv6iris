(* ProofSysPause.v -- sys_pause() over the SIE-agnostic sconf world.

     uint64 sys_pause(void) {
       int n; uint ticks0;
       argint(0, &n);
       if (n < 0) n = 0;
       acquire(&tickslock);
       ticks0 = ticks;
       while (ticks - ticks0 < n) {
         if (killed(myproc())) { release(&tickslock); return -1; }
         sleep_prepare(&ticks);   /* the SPLIT sleep protocol, SpecSleep.v */
         release(&tickslock);
         sleep();
         acquire(&tickslock);
       }
       release(&tickslock);
       return 0;
     }

   The shape (see WpSysPauseDecode.v for the full listing) is a 64-byte,
   8-slot frame in which

     slot 1 = ra, slot 2 = s0, slots 3/4/5 = s1/s2/s3 -- but the s1/s2/s3
     saves happen at +0x2c, i.e. only AFTER the [c.beqz] that skips the loop,
     so on the [n == 0] path those three slots stay scratch;
     slot 7's UPPER half is the [int n] local (&n = s0-52), which argint
     writes into sys_pause's own frame -- carved out with
     InstrBytes.word_pointsto_split4 and rejoined at whichever exit fires;
     slots 6 and 8 are never touched.

   FIVE joins, so five continuation predicates, each threading the next as
   its last premise:

     sp_tail   (+0x8e) the shared epilogue: ldsp ra/s0, frame pop, c.ret.
                       Reached by the 0 exit falling through and by the -1
                       exit's [c.j].
     sp_exit0  (+0x80) release + [c.li a0,0].  Reached from the [c.beqz]
                       (n == 0, s1/s2/s3 never spilled) AND from the loop's
                       fall-through (which restores them at +0x7a) -- so it
                       takes slots 3/4/5 as scratch and s1/s2/s3 = m's.
     sp_exitk  (+0x9c) release + [c.li a0,-1] + the s1/s2/s3 restores.
                       Only the loop reaches it, so it takes the LOOP
                       register shape (s1 = &tickslock, s2 = &ticks,
                       s3 = ticks0 -- the two pointers SWAPPED registers when
                       the sleep call site was split) and the three saved
                       slots.
     sp_loop   (+0x4a) the wait loop, by iLöb: it is unbounded (sleep may
                       never see enough ticks go by).
     sp_acq    (+0x1a) acquire + the [n == 0] dispatch + the loop set-up.
                       TWO paths reach it -- the [blt] falling through and
                       the [n < 0] fixup at +0x96, which stores 0 and [c.j]s
                       back -- so it is quantified over the [n] cell's value.

   Nothing in the loop's exit test is known: the branch is a plain case split
   on [ticks - ticks0 <u n], and [killed]'s result is whatever another core
   left in p->killed.  That is why the spec's return value is existential.

   THE HART-GENERIC PROTOCOL, IN THE [wp_next] FORM.  Every leaf and every
   callee hands its continuation back through [wp_next b p (fun CID => ...)],
   so the resuming hart arrives as an ordinary binder and every resource
   written after it is automatically about that hart -- no [(CID := h)]
   annotation on a resource, and, since the SIE ghost went canonical per hart,
   no ghost binder to thread.  What is left to think about is WHERE the hart
   can actually move:

     * the entry index is DERIVABLY [true] ([CpuOwn.cpu_own_eb_agree]: level 0
       with an enabled base has no [b = false] instance), so the prologue,
       argint, the [n < 0] dispatch, the acquire crossing, the two releases,
       the shared epilogue and sys_pause's own [wp_next] obligation are all
       hart-GENERIC;
     * from acquire's return to a release's call the tickslock is HELD, i.e.
       the index is the literal [false], so every leaf there is a plain
       [rewrite wp_next_off] and the hart is pinned -- that is the whole loop
       body except its one crossing;
     * the hart changes inside the loop are the interior release/sleep/
       acquire run (+0x5c .. +0x66): the caller now drops the tickslock
       ITSELF, parks in the lock-free [sleep] -- whose crossing index is the
       literal [true], because a [swtch] moves the hart with interrupts off
       -- and re-acquires.  That whole stretch is at the ENABLED index, and
       it is a window in which the thread holds no lock at all; since it is
       INSIDE the wait loop, it is the LOOP INVARIANT that has to survive
       it.

   All five join predicates are therefore [wp_next]s ANCHORED at the whole
   function's entry hart [CID0], at the generic index [true]: forwarding one
   is the identity and only a USE costs a [wp_next_chain].  Each straight-line
   stretch between two joins is its OWN lemma with its OWN ambient
   [`{GEN : GenId} `{CID : CpuId}] plus the anchor [CID0 : CPU] and the chained equality that
   links the two -- [CID0] is taken at type [CPU], not [CpuId], on purpose: it
   must not be an instance candidate competing with the ambient hart.

     * [sp_base] has no tp conjunct any more: [HartTp.tp_pin] pins tp to
       whichever hart owns the register file, so no map ever observes its tp
       slot, and a parking hop and a same-hart hop are the same
       [callee_saved] transport.
     * the trap CSRs ride the loop: an acquire(&tickslock) mints
       [arm_pay 0 eb _] and the matching release spends it -- including the
       interior pair around the park, where the loop invariant's pay is
       spent by the release at +0x5c and re-minted by the acquire at +0x66.
       At [eb = true] the complement [sleep] asks for ([trap_csrs_ext] /
       [cpu_claim_ext]) is [emp], so nothing crosses the park by hand.
       sys_pause is therefore trap-CSR-balanced and its own contract does
       not mention them.
     * the parked-scheduler record is NOT threaded here.  It lives in the
       running proc's own [p->lock] ([SchedCtx.run_slot]), which sleep
       reaches by holding that lock, so sys_pause never names it.
     * [panic_wp_any] is what acquire, killed, sleep_prepare and sleep take.

   A functor over ARGINT / ACQUIRE / RELEASE / MYPROC / KILLED /
   SLEEP_PREPARE / SLEEP. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExtras.
Require Import RiscvModelBytes.
Require Import InstrBytes KernelText WpMmodeLeafBase.
Require Import RegFile.
Require Import SmodeCore.
Require Import StackOwn CalleeSaved.
Require Import IntrDefs.
Require Import HartTp WpNext.
Require Import VcGen WpSconfAlu WpSconfMem WpSconfCtl WpSconfBtype.
Require Import WpSmodeIntr.
Require Import WpLock.
Require Import ProcGeom CpuOwn.
Require Import PageGeom.
Require Import FdSlots ProcInv.
Require Import FileInvDefs.
Require Import SchedCtx.
Require Import TicksInv.
Require Import CodeSysPause.
Require Import PanicStub.
Require Import SpecArgint SpecAcquire SpecRelease SpecMyproc SpecKilled SpecSleepPrepare SpecSleep.
Require Import SpecSysPause.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import KernelRvcDecode.
Import Defs.

Local Open Scope Z_scope.

Set Printing Depth 40.

(* ===================================================================== *)
(* Pure address arithmetic.                                               *)
(* ===================================================================== *)

(* [addi a1,s0,-52] / [lw -52(s0)] / [sw -52(s0)]: &n, the UPPER word of
   frame slot 7 (s0 is the ENTRY sp, so s0-52 = sp0-56+4). *)
Lemma sp_addr_n (X : mword 64) :
  add_vec X (sign_extend' 64 (mword_of_int 0xfcc : mword 12)) = pa_add (pa_stk X 7) 4.
Proof.
  unfold pa_add, pa_stk. rewrite avi_assoc.
  unfold add_vec_int. apply f_equal. apply bv_eq; vm_compute; reflexivity.
Qed.

(* the five sp-relative slot addresses the 8-slot frame uses *)
Lemma sp_off7 (X : mword 64) :
  add_vec (pa_stk X 8) (zero_extend' 64 (concat_vec (mword_of_int 7 : mword 6) ('b"000"))) = pa_stk X 1.
Proof. unfold pa_stk, add_vec_int. rewrite add_vec_off2. f_equal; apply bv_eq; vm_compute; reflexivity. Qed.

Lemma sp_off6 (X : mword 64) :
  add_vec (pa_stk X 8) (zero_extend' 64 (concat_vec (mword_of_int 6 : mword 6) ('b"000"))) = pa_stk X 2.
Proof. unfold pa_stk, add_vec_int. rewrite add_vec_off2. f_equal; apply bv_eq; vm_compute; reflexivity. Qed.

Lemma sp_off5 (X : mword 64) :
  add_vec (pa_stk X 8) (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000"))) = pa_stk X 3.
Proof. unfold pa_stk, add_vec_int. rewrite add_vec_off2. f_equal; apply bv_eq; vm_compute; reflexivity. Qed.

Lemma sp_off4 (X : mword 64) :
  add_vec (pa_stk X 8) (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000"))) = pa_stk X 4.
Proof. unfold pa_stk, add_vec_int. rewrite add_vec_off2. f_equal; apply bv_eq; vm_compute; reflexivity. Qed.

Lemma sp_off3 (X : mword 64) :
  add_vec (pa_stk X 8) (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000"))) = pa_stk X 5.
Proof. unfold pa_stk, add_vec_int. rewrite add_vec_off2. f_equal; apply bv_eq; vm_compute; reflexivity. Qed.



(* release's / sleep's "the pointer I passed is the lock" premise *)
Lemma sp_add_vec_0 (x : mword 64) :
  add_vec x (sign_extend' 64 (mword_of_int 0 : mword 12)) = x.
Proof.
  unfold add_vec, word_binop, with_word', with_word, MachineWord.MachineWord.add.
  apply bv_add_0_r. vm_compute. reflexivity.
Qed.

(* [c.lw a5,0(s1)]: the tick counter, at zero displacement off s1 *)
Lemma sp_lw0 (x : mword 64) :
  add_vec x (sign_extend' 64 (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 5) ('b"00")))) = x.
Proof.
  replace (sign_extend' 64 (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 5) ('b"00"))) : mword 64)
    with (mword_of_int 0 : mword 64) by (apply bv_eq; vm_compute; reflexivity).
  apply kv_addv_zero.
Qed.

(* ===================================================================== *)
(* The register-map invariants at the joins.  All HART-FREE: tp is pinned  *)
(* to whichever hart owns the register file ([HartTp]), so it is not a     *)
(* conjunct anywhere here and a park needs no separate transport.          *)
(* ===================================================================== *)

(* s4..s11: sys_pause never writes them, so they thread from the entry map *)
Definition sp_hi (m M : regfile) : Prop :=
  M !!! Regidx (mword_of_int 20 : mword 5) = m !!! Regidx (mword_of_int 20 : mword 5) /\
  M !!! Regidx (mword_of_int 21 : mword 5) = m !!! Regidx (mword_of_int 21 : mword 5) /\
  M !!! Regidx (mword_of_int 22 : mword 5) = m !!! Regidx (mword_of_int 22 : mword 5) /\
  M !!! Regidx (mword_of_int 23 : mword 5) = m !!! Regidx (mword_of_int 23 : mword 5) /\
  M !!! Regidx (mword_of_int 24 : mword 5) = m !!! Regidx (mword_of_int 24 : mword 5) /\
  M !!! Regidx (mword_of_int 25 : mword 5) = m !!! Regidx (mword_of_int 25 : mword 5) /\
  M !!! Regidx (mword_of_int 26 : mword 5) = m !!! Regidx (mword_of_int 26 : mword 5) /\
  M !!! Regidx (mword_of_int 27 : mword 5) = m !!! Regidx (mword_of_int 27 : mword 5).

Lemma sp_hi_cs (m M1 M2 : regfile) : callee_saved M1 M2 -> sp_hi m M1 -> sp_hi m M2.
Proof.
  intros Hcs (A&B&C&D&E&F&G&H). unfold sp_hi. repeat split.
  - rewrite (callee_saved_lookup Hcs (mword_of_int 20 : mword 5) ltac:(vm_compute; reflexivity)). exact A.
  - rewrite (callee_saved_lookup Hcs (mword_of_int 21 : mword 5) ltac:(vm_compute; reflexivity)). exact B.
  - rewrite (callee_saved_lookup Hcs (mword_of_int 22 : mword 5) ltac:(vm_compute; reflexivity)). exact C.
  - rewrite (callee_saved_lookup Hcs (mword_of_int 23 : mword 5) ltac:(vm_compute; reflexivity)). exact D.
  - rewrite (callee_saved_lookup Hcs (mword_of_int 24 : mword 5) ltac:(vm_compute; reflexivity)). exact E.
  - rewrite (callee_saved_lookup Hcs (mword_of_int 25 : mword 5) ltac:(vm_compute; reflexivity)). exact F.
  - rewrite (callee_saved_lookup Hcs (mword_of_int 26 : mword 5) ltac:(vm_compute; reflexivity)). exact G.
  - rewrite (callee_saved_lookup Hcs (mword_of_int 27 : mword 5) ltac:(vm_compute; reflexivity)). exact H.
Qed.

(* what holds at EVERY join inside the frame: sp at the frame base, s0 the
   entry sp, s4..s11 untouched. *)
Definition sp_base (m M : regfile) (sp0 : mword 64) : Prop :=
  M !!! Regidx csp_rs1 = pa_stk sp0 8 /\
  M !!! Regidx (mword_of_int 8 : mword 5) = sp0 /\
  sp_hi m M.

Lemma sp_base_cs (m M1 M2 : regfile) (sp0 : mword 64) :
  callee_saved M1 M2 -> sp_base m M1 sp0 -> sp_base m M2 sp0.
Proof.
  intros Hcs (A&C&D). unfold sp_base. split; [| split].
  - rewrite (callee_saved_lookup Hcs csp_rs1 ltac:(vm_compute; reflexivity)). exact A.
  - rewrite (callee_saved_lookup Hcs (mword_of_int 8 : mword 5) ltac:(vm_compute; reflexivity)). exact C.
  - exact (sp_hi_cs m M1 M2 Hcs D).
Qed.

(* s1/s2/s3 still hold the CALLER's values (before the +0x2c spills, and
   again after the +0x7a / +0xaa reloads) *)
Definition sp_saved (m M : regfile) : Prop :=
  M !!! Regidx (mword_of_int 9 : mword 5) = m !!! Regidx (mword_of_int 9 : mword 5) /\
  M !!! Regidx (mword_of_int 18 : mword 5) = m !!! Regidx (mword_of_int 18 : mword 5) /\
  M !!! Regidx (mword_of_int 19 : mword 5) = m !!! Regidx (mword_of_int 19 : mword 5).

Lemma sp_saved_cs (m M1 M2 : regfile) : callee_saved M1 M2 -> sp_saved m M1 -> sp_saved m M2.
Proof.
  intros Hcs (A&B&C). unfold sp_saved. repeat split.
  - rewrite (callee_saved_lookup Hcs (mword_of_int 9 : mword 5) ltac:(vm_compute; reflexivity)). exact A.
  - rewrite (callee_saved_lookup Hcs (mword_of_int 18 : mword 5) ltac:(vm_compute; reflexivity)). exact B.
  - rewrite (callee_saved_lookup Hcs (mword_of_int 19 : mword 5) ltac:(vm_compute; reflexivity)). exact C.
Qed.

(* ...and the LOOP's shape for the same three registers *)
Definition sp_lregs (M : regfile) (tk : mword 64) : Prop :=
  M !!! Regidx (mword_of_int 9 : mword 5) = a_tickslock /\
  M !!! Regidx (mword_of_int 18 : mword 5) = a_ticks /\
  M !!! Regidx (mword_of_int 19 : mword 5) = tk.

Lemma sp_lregs_cs (M1 M2 : regfile) (tk : mword 64) :
  callee_saved M1 M2 -> sp_lregs M1 tk -> sp_lregs M2 tk.
Proof.
  intros Hcs (A&B&C). unfold sp_lregs. repeat split.
  - rewrite (callee_saved_lookup Hcs (mword_of_int 9 : mword 5) ltac:(vm_compute; reflexivity)). exact A.
  - rewrite (callee_saved_lookup Hcs (mword_of_int 18 : mword 5) ltac:(vm_compute; reflexivity)). exact B.
  - rewrite (callee_saved_lookup Hcs (mword_of_int 19 : mword 5) ltac:(vm_compute; reflexivity)). exact C.
Qed.

(* ===================================================================== *)
(* The five join predicates.  Each is a [wp_next] ANCHORED at the entry     *)
(* hart [CID0] at the generic index [true]: the park inside the wait loop  *)
(* means any of them can be entered at a hart nobody knew about when it    *)
(* was established, and a [wp_next] is exactly the proposition that        *)
(* survives that.  There is NO section [Context {CID : CpuId}] here, so    *)
(* the [fun CID => ...] binder is the only hart in scope inside each body  *)
(* and every resource there resolves at it automatically.                  *)
(* ===================================================================== *)
Section SpProps.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !irefslotG Σ}.

  (* the scratch slots: 3/4/5 (only spilled on the loop path), 6 and 8 (never
     touched at all).  Slot 7 is the [int n] local and rides separately. *)
  Definition sp_free (sp0 : mword 64) : iProp Σ :=
    ((∃ w : bv 64, pa_stk sp0 3 ↦₈ w) ∗ (∃ w : bv 64, pa_stk sp0 4 ↦₈ w) ∗
     (∃ w : bv 64, pa_stk sp0 5 ↦₈ w) ∗ (∃ w : bv 64, pa_stk sp0 6 ↦₈ w) ∗
     (∃ w : bv 64, pa_stk sp0 8 ↦₈ w))%I.

  (* the right to put frame slot 7 back together once the [int n] cell is
     done with -- the lower half plus its 8-alignment, packaged so no join
     predicate has to carry a pure alignment fact. *)
  Definition sp_join7 (sp0 : mword 64) : iProp Σ :=
    (∀ nv : mword 32, pa_add (pa_stk sp0 7) 4 ↦₄ nv -∗ ∃ w : bv 64, pa_stk sp0 7 ↦₈ w)%I.

  (* +0x7e -- the shared epilogue.  [r] is the value already parked in a0. *)
  Definition sp_tail `{GEN : GenId} (CID0 : CPU)  (j : nat)
      (m : regfile) (av : nat) (eb : bool) (C : iProp Σ)
      (sp0 pj : mword 64) (lks : gset nat) : iProp Σ :=
    (wp_next (CID0 := CID0) true pj (fun (CID : CpuId) =>
      ∀ (M : regfile) (r : mword 64),
        ⌜ sp_base m M sp0 /\ sp_saved m M /\
          M !!! Regidx (mword_of_int 10 : mword 5) = r /\
          (r = (zero_reg : mword 64) \/ r = mword_of_int (-1)) ⌝ -∗
        pa_stk sp0 1 ↦₈ (m !!! Regidx (mword_of_int 1 : mword 5)) -∗
        pa_stk sp0 2 ↦₈ (m !!! Regidx (mword_of_int 8 : mword 5)) -∗
        sp_free sp0 -∗ (∃ w : bv 64, pa_stk sp0 7 ↦₈ w) -∗
        sie_cap_gpr M (av - 8) true pj -∗
        cpu_own 0 eb pj C true lks -∗
        pc_is (mword_of_int (KernelSyms.sys_pause + 0x8e)) -∗
        WP (Loop : expr riscv_lang)))%I.

  (* +0x70 -- release(&tickslock); return 0. *)
  Definition sp_exit0 `{GEN : GenId} (CID0 : CPU) (γt : gname) (j : nat)
      (m : regfile) (av : nat) (eb : bool) (C : iProp Σ)
      (sp0 pj : mword 64) (lks : gset nat) : iProp Σ :=
    (wp_next (CID0 := CID0) true pj (fun (CID : CpuId) =>
      ∀ M : regfile,
        ⌜ sp_base m M sp0 /\ sp_saved m M ⌝ -∗
        pa_stk sp0 1 ↦₈ (m !!! Regidx (mword_of_int 1 : mword 5)) -∗
        pa_stk sp0 2 ↦₈ (m !!! Regidx (mword_of_int 8 : mword 5)) -∗
        sp_free sp0 -∗ (∃ w : bv 64, pa_stk sp0 7 ↦₈ w) -∗
        locked γt cpu_id -∗ ticks_res -∗
        sie_cap_gpr M (trap_res true + (av - 8))%nat false pj -∗
        cpu_own 1 eb pj C false ({[lock_rank "time"]} ∪ lks) -∗ arm_pay 0 eb pj -∗
        pc_is (mword_of_int (KernelSyms.sys_pause + 0x80)) -∗
        sp_tail CID0 j m av eb C sp0 pj lks -∗
        WP (Loop : expr riscv_lang)))%I.

  (* +0x8c -- release(&tickslock); return -1.  Only the loop gets here, so the
     register shape is the loop's and slots 3/4/5 hold the spilled s1/s2/s3. *)
  Definition sp_exitk `{GEN : GenId} (CID0 : CPU) (γt : gname) (j : nat)
      (m : regfile) (av : nat) (eb : bool) (C : iProp Σ)
      (sp0 pj tk : mword 64) (lks : gset nat) : iProp Σ :=
    (wp_next (CID0 := CID0) true pj (fun (CID : CpuId) =>
      ∀ M : regfile,
        ⌜ sp_base m M sp0 /\ sp_lregs M tk ⌝ -∗
        pa_stk sp0 1 ↦₈ (m !!! Regidx (mword_of_int 1 : mword 5)) -∗
        pa_stk sp0 2 ↦₈ (m !!! Regidx (mword_of_int 8 : mword 5)) -∗
        pa_stk sp0 3 ↦₈ (m !!! Regidx (mword_of_int 9 : mword 5)) -∗
        pa_stk sp0 4 ↦₈ (m !!! Regidx (mword_of_int 18 : mword 5)) -∗
        pa_stk sp0 5 ↦₈ (m !!! Regidx (mword_of_int 19 : mword 5)) -∗
        (∃ w : bv 64, pa_stk sp0 6 ↦₈ w) -∗ (∃ w : bv 64, pa_stk sp0 7 ↦₈ w) -∗
        (∃ w : bv 64, pa_stk sp0 8 ↦₈ w) -∗
        locked γt cpu_id -∗ ticks_res -∗
        sie_cap_gpr M (trap_res true + (av - 8))%nat false pj -∗
        cpu_own 1 eb pj C false ({[lock_rank "time"]} ∪ lks) -∗ arm_pay 0 eb pj -∗
        pc_is (mword_of_int (KernelSyms.sys_pause + 0x9c)) -∗
        sp_tail CID0 j m av eb C sp0 pj lks -∗
        WP (Loop : expr riscv_lang)))%I.

  (* +0x4a -- the wait loop's head. *)
  Definition sp_loop `{GEN : GenId} (CID0 : CPU) (γt : gname) (j : nat)
      (m : regfile) (av : nat) (eb : bool) (C : iProp Σ)
      (sp0 pj tk : mword 64) (nv : mword 32) (lks : gset nat) : iProp Σ :=
    (wp_next (CID0 := CID0) true pj (fun (CID : CpuId) =>
      ∀ M : regfile,
        ⌜ sp_base m M sp0 /\ sp_lregs M tk ⌝ -∗
        pa_stk sp0 1 ↦₈ (m !!! Regidx (mword_of_int 1 : mword 5)) -∗
        pa_stk sp0 2 ↦₈ (m !!! Regidx (mword_of_int 8 : mword 5)) -∗
        pa_stk sp0 3 ↦₈ (m !!! Regidx (mword_of_int 9 : mword 5)) -∗
        pa_stk sp0 4 ↦₈ (m !!! Regidx (mword_of_int 18 : mword 5)) -∗
        pa_stk sp0 5 ↦₈ (m !!! Regidx (mword_of_int 19 : mword 5)) -∗
        (∃ w : bv 64, pa_stk sp0 6 ↦₈ w) -∗ (∃ w : bv 64, pa_stk sp0 8 ↦₈ w) -∗
        pa_add (pa_stk sp0 7) 4 ↦₄ nv -∗ sp_join7 sp0 -∗
        locked γt cpu_id -∗ ticks_res -∗
        sie_cap_gpr M (trap_res true + (av - 8))%nat false pj -∗
        cpu_own 1 eb pj C false ({[lock_rank "time"]} ∪ lks) -∗ arm_pay 0 eb pj -∗
        pc_is (mword_of_int (KernelSyms.sys_pause + 0x4a)) -∗
        sp_exit0 CID0 γt j m av eb C sp0 pj lks -∗
        sp_exitk CID0 γt j m av eb C sp0 pj tk lks -∗
        sp_tail CID0 j m av eb C sp0 pj lks -∗
        WP (Loop : expr riscv_lang)))%I.

  (* +0x1a -- a0 := &tickslock, acquire, the [n == 0] dispatch, the loop set-up.
     Quantified over the [n] cell's value: BOTH the [blt]'s fall-through and
     the [n < 0] fixup's back edge land here. *)
  Definition sp_acq `{GEN : GenId} (CID0 : CPU) (γt : gname) (j : nat)
      (m : regfile) (av : nat) (eb : bool) (C : iProp Σ)
      (sp0 pj : mword 64) (lks : gset nat) : iProp Σ :=
    (wp_next (CID0 := CID0) true pj (fun (CID : CpuId) =>
      ∀ (M : regfile) (nv : mword 32),
        ⌜ sp_base m M sp0 /\ sp_saved m M ⌝ -∗
        pa_stk sp0 1 ↦₈ (m !!! Regidx (mword_of_int 1 : mword 5)) -∗
        pa_stk sp0 2 ↦₈ (m !!! Regidx (mword_of_int 8 : mword 5)) -∗
        sp_free sp0 -∗
        pa_add (pa_stk sp0 7) 4 ↦₄ nv -∗ sp_join7 sp0 -∗
        sie_cap_gpr M (av - 8) true pj -∗
        cpu_own 0 eb pj C true lks -∗
        pc_is (mword_of_int (KernelSyms.sys_pause + 0x1a)) -∗
        sp_tail CID0 j m av eb C sp0 pj lks -∗
        WP (Loop : expr riscv_lang)))%I.

End SpProps.

(* ===================================================================== *)

Module SysPauseProof (Argint : ARGINT) (Acquire : ACQUIRE) (Release : RELEASE)
                     (Myproc : MYPROC) (Killed : KILLED)
                     (SleepPrepare : SLEEP_PREPARE) (Sleep : SLEEP) : SYSPAUSE.

(* register disequality guard (perf rule): [unify] settles convertibility
   cheaply, so [discriminate] only ever runs on a genuine miss. *)
Local Ltac reg_neq :=
  lazymatch goal with |- ?a <> ?b =>
    tryif unify a b then fail else (vm_compute; discriminate) end.
Local Ltac pcstep := apply bv_eq; vm_compute; reflexivity.

(* ===================================================================== *)
(*  THE STRAIGHT-LINE STRETCHES.  Each has its OWN ambient hart binder     *)
(*  [`{GEN : GenId} `{CID : CpuId}] plus the function's entry anchor [CID0 : CPU] and the *)
(*  chained equality that links the two, which is what lets it use the     *)
(*  [wp_next]-shaped joins at its own hart.                                *)
(* ===================================================================== *)
Section SpBodies.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !irefslotG Σ, !fileG Σ}.

  (* ---- the shared epilogue: +0x7e .. +0x84 (c.ret) ---- *)
  Lemma sp_tail_body `{GEN : GenId} `{CID : CpuId} (CID0 : CPU) (j : nat)
      (m M : regfile) (r : mword 64) (av : nat) (eb : bool) (C : iProp Σ)
      (sp0 pj : mword 64) (tfp : mword 44) (ws : list (mword 64)) (dqt : dfrac) (lks : gset nat) :
    let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
    (30 <= av)%nat ->
    (true = false \/ pj = zero_reg -> (CID : CPU) = CID0) ->
    sp_base m M sp0 -> sp_saved m M ->
    M !!! Regidx (mword_of_int 10 : mword 5) = r ->
    (r = (zero_reg : mword 64) \/ r = mword_of_int (-1)) ->
    sp0 = m !!! Regidx csp_rs1 ->
    kernel_text -∗
    pa_stk sp0 1 ↦₈ (m !!! Regidx (mword_of_int 1 : mword 5)) -∗
    pa_stk sp0 2 ↦₈ (m !!! Regidx (mword_of_int 8 : mword 5)) -∗
    sp_free sp0 -∗ (∃ w : bv 64, pa_stk sp0 7 ↦₈ w) -∗
    sie_cap_gpr M (av - 8) true pj -∗
    cpu_own 0 eb pj C true lks -∗
    p_trapframe pj ↦₈{dqt} page_base tfp -∗
    tf_page tfp ws -∗
    pc_is (mword_of_int (KernelSyms.sys_pause + 0x8e)) -∗
    wp_next (CID0 := CID0) true pj (fun (CID : CpuId) =>
      ∀ (mf : regfile) (rr : mword 64),
        ⌜ callee_saved m mf /\
          mf !!! Regidx (mword_of_int 10 : mword 5) = rr /\
          (rr = (zero_reg : mword 64) \/ rr = mword_of_int (-1)) ⌝ -∗
        sie_cap_gpr mf av true pj -∗
        cpu_own 0 eb pj C true lks -∗
        pc_is ret_tgt -∗
        p_trapframe pj ↦₈{dqt} page_base tfp -∗
        tf_page tfp ws -∗
        WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros ret_tgt Hav Hanch Hbase Hsav Hra0 Hrv Hsp0.
    destruct Hbase as (Hsp & Hs0M & Hhi).
    iIntros "#Htext Hs1 Hs2 Hfree Hs7 Hcg Hown Htf Hpage Hpc Hcont".
    destruct Hsav as (Hv9 & Hv18 & Hv19).
    rewrite /sp_free.
    iDestruct "Hfree" as "(Hf3 & Hf4 & Hf5 & Hf6 & Hf8)".
    iPoseProof (spi_8e with "Htext") as "Hi7e".
    iPoseProof (spi_90 with "Htext") as "Hi80".
    iPoseProof (spi_92 with "Htext") as "Hi82".
    iPoseProof (spi_94 with "Htext") as "Hi84".
    (* +0x7e c.ldsp ra,56(sp) *)
    assert (Ht1 : add_vec (M !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 7 : mword 6) ('b"000"))) = pa_stk sp0 1)
      by (rewrite Hsp; apply sp_off7).
    iEval (rewrite -Ht1) in "Hs1".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.sys_pause + 0x8e))
              (mword_of_int 7 : mword 6) (mword_of_int 1 : mword 5) M (av - 8)%nat
              (m !!! Regidx (mword_of_int 1 : mword 5)) true (dqm := DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi7e Hs1").
    iIntros (CIDe1 Hse1) "Hcg Hpc Hs1".
    iEval (rewrite Ht1) in "Hs1".
    set (E1 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 1 : mword 5))]> M).
    change (<[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 1 : mword 5))]> M) with E1.
    assert (Hp80 : add_vec_int (mword_of_int (KernelSyms.sys_pause + 0x8e) : mword 64) 2
                   = mword_of_int (KernelSyms.sys_pause + 0x90)) by pcstep.
    iEval (rewrite Hp80) in "Hpc".
    assert (HE1sp : E1 !!! Regidx csp_rs1 = pa_stk sp0 8)
      by (rewrite /E1 upd_ne; [exact Hsp | reg_neq]).
    (* +0x80 c.ldsp s0,48(sp) *)
    assert (Ht2 : add_vec (E1 !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 6 : mword 6) ('b"000"))) = pa_stk sp0 2)
      by (rewrite HE1sp; apply sp_off6).
    iEval (rewrite -Ht2) in "Hs2".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.sys_pause + 0x90))
              (mword_of_int 6 : mword 6) (mword_of_int 8 : mword 5) E1 (av - 8)%nat
              (m !!! Regidx (mword_of_int 8 : mword 5)) true (dqm := DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi80 Hs2").
    iIntros (CIDe2 Hse2) "Hcg Hpc Hs2".
    iEval (rewrite Ht2) in "Hs2".
    set (E2 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 8 : mword 5))]> E1).
    change (<[Regidx (mword_of_int 8 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 8 : mword 5))]> E1) with E2.
    assert (Hp82 : add_vec_int (mword_of_int (KernelSyms.sys_pause + 0x90) : mword 64) 2
                   = mword_of_int (KernelSyms.sys_pause + 0x92)) by pcstep.
    iEval (rewrite Hp82) in "Hpc".
    assert (HE2sp : E2 !!! Regidx csp_rs1 = pa_stk sp0 8)
      by (rewrite /E2 upd_ne; [exact HE1sp | reg_neq]).
    (* +0x82 c.addi16sp sp,64 -- the frame pop *)
    iAssert (stack_own sp0 8) with "[Hs1 Hs2 Hf3 Hf4 Hf5 Hf6 Hs7 Hf8]" as "Hframe".
    { rewrite stack_own_slots. cbn [seq].
      iSplitL "Hs1". { iExists _. iExact "Hs1". }
      iSplitL "Hs2". { iExists _. iExact "Hs2". }
      iSplitL "Hf3". { iExact "Hf3". }
      iSplitL "Hf4". { iExact "Hf4". }
      iSplitL "Hf5". { iExact "Hf5". }
      iSplitL "Hf6". { iExact "Hf6". }
      iSplitL "Hs7". { iExact "Hs7". }
      iSplitL "Hf8". { iExact "Hf8". }
      done. }
    assert (Hwv : add_vec (E2 !!! Regidx csp_rs1)
                    (sign_extend' 64 (caddi16sp_imm (mword_of_int 4 : mword 6))) = sp0)
      by (rewrite HE2sp; apply stk_pop_64).
    assert (Hpop : E2 !!! Regidx csp_rs1
                   = pa_stk (add_vec (E2 !!! Regidx csp_rs1)
                               (sign_extend' 64 (caddi16sp_imm (mword_of_int 4 : mword 6)))) 8)
      by (rewrite Hwv; exact HE2sp).
    iEval (rewrite -Hwv) in "Hframe".
    iApply (wp_caddi16sp_pop_s_sconf (mword_of_int (KernelSyms.sys_pause + 0x92))
              (mword_of_int 4 : mword 6) E2 (av - 8)%nat 8 true Hpop
              with "Hcg Hpc Hi82 Hframe").
    iIntros (CIDe3 Hse3) "Hcg Hpc".
    assert (Hnk : ((av - 8) + 8)%nat = av) by lia.
    iEval (rewrite Hnk) in "Hcg".
    set (E3 := <[Regidx csp_rs1 := regval_into_reg
        (add_vec (E2 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 4 : mword 6))))]> E2).
    change (<[Regidx csp_rs1 := regval_into_reg
        (add_vec (E2 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 4 : mword 6))))]> E2) with E3.
    assert (Hp84 : add_vec_int (mword_of_int (KernelSyms.sys_pause + 0x92) : mword 64) 2
                   = mword_of_int (KernelSyms.sys_pause + 0x94)) by pcstep.
    iEval (rewrite Hp84) in "Hpc".
    (* +0x84 c.ret *)
    assert (HE3ra : E3 !!! Regidx (mword_of_int 1 : mword 5) = m !!! Regidx (mword_of_int 1 : mword 5)).
    { rewrite /E3 upd_ne; [| reg_neq]. rewrite /E2 upd_ne; [| reg_neq].
      rewrite /E1. apply upd_eq. }
    iApply (wp_cret_s_sconf (mword_of_int (KernelSyms.sys_pause + 0x94))
              (mword_of_int 1 : mword 5) E3 av true ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi84").
    iIntros (CIDe4 Hse4) "Hcg Hpc".
    iEval (rgne) in "Hpc".
    assert (Hretfin : ret_pc (E3 !!! Regidx (mword_of_int 1 : mword 5)) = ret_tgt)
      by (rewrite HE3ra; reflexivity).
    iEval (rewrite Hretfin) in "Hpc".
    (* the callee-saved report *)
    assert (HE3thr : forall c : mword 5,
              c <> csp_rs1 -> c <> mword_of_int 8 -> c <> mword_of_int 1 ->
              E3 !!! Regidx c = M !!! Regidx c).
    { intros c N2 N8 N1.
      rewrite /E3 upd_ne; [| congruence]. rewrite /E2 upd_ne; [| congruence].
      rewrite /E1 upd_ne; [reflexivity | congruence]. }
    destruct Hhi as (H20&H21&H22&H23&H24&H25&H26&H27).
    assert (HE3a0 : E3 !!! Regidx (mword_of_int 10 : mword 5) = r)
      by (rewrite (HE3thr (mword_of_int 10 : mword 5) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)); exact Hra0).
    iDestruct (cpu_own_transport CID CIDe4 0 eb pj C true ltac:(wp_next_chain)
                 with "Hown") as "Hown".
    iSpecialize ("Hcont" $! CIDe4 with "[%]"); [wp_next_chain|].
    iApply ("Hcont" $! E3 r with "[%] Hcg Hown Hpc Htf Hpage").
    split; [| split; [exact HE3a0 | exact Hrv]].
    unfold callee_saved.
    split. { rewrite /E3 upd_eq. unfold regval_into_reg. rewrite Hwv. exact Hsp0. }
    split. { rewrite /E3 upd_ne; [| reg_neq]. rewrite /E2. apply upd_eq. }
    split. { rewrite (HE3thr (mword_of_int 9 : mword 5) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)). exact Hv9. }
    split. { rewrite (HE3thr (mword_of_int 18 : mword 5) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)). exact Hv18. }
    split. { rewrite (HE3thr (mword_of_int 19 : mword 5) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)). exact Hv19. }
    split. { rewrite (HE3thr (mword_of_int 20 : mword 5) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)). exact H20. }
    split. { rewrite (HE3thr (mword_of_int 21 : mword 5) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)). exact H21. }
    split. { rewrite (HE3thr (mword_of_int 22 : mword 5) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)). exact H22. }
    split. { rewrite (HE3thr (mword_of_int 23 : mword 5) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)). exact H23. }
    split. { rewrite (HE3thr (mword_of_int 24 : mword 5) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)). exact H24. }
    split. { rewrite (HE3thr (mword_of_int 25 : mword 5) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)). exact H25. }
    split. { rewrite (HE3thr (mword_of_int 26 : mword 5) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)). exact H26. }
    { rewrite (HE3thr (mword_of_int 27 : mword 5) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)). exact H27. }
  Qed.

  (* ---- the normal (return 0) exit: +0x70 .. the join at +0x7e ---- *)
  Lemma sp_exit0_body `{GEN : GenId} `{CID : CpuId} (CID0 : CPU)
      (γt : gname) (j : nat)
      (m N : regfile) (av : nat) (eb : bool) (C : iProp Σ)
      (sp0 pj : mword 64) (lks : gset nat) :
    (30 <= av)%nat ->
    eb = true ->
    (true = false \/ pj = zero_reg -> (CID : CPU) = CID0) ->
    sp_base m N sp0 -> sp_saved m N ->
    (* acquire's freshness premise -- see [sp_acq_body] where it originates *)
    locks_below lks (lock_rank "time") ->
    kernel_text -∗
    is_tickslock γt -∗
    pa_stk sp0 1 ↦₈ (m !!! Regidx (mword_of_int 1 : mword 5)) -∗
    pa_stk sp0 2 ↦₈ (m !!! Regidx (mword_of_int 8 : mword 5)) -∗
    sp_free sp0 -∗ (∃ w : bv 64, pa_stk sp0 7 ↦₈ w) -∗
    locked γt cpu_id -∗ ticks_res -∗
    sie_cap_gpr N (trap_res true + (av - 8))%nat false pj -∗
    cpu_own 1 eb pj C false ({[lock_rank "time"]} ∪ lks) -∗ arm_pay 0 eb pj -∗
    pc_is (mword_of_int (KernelSyms.sys_pause + 0x80)) -∗
    sp_tail CID0 j m av eb C sp0 pj lks -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hav Heb Hanch Hbn Hsn Hfresh. subst eb.
    iIntros "#Htext #Hlkt Hx1 Hx2 Hfree Hx7 Htok HR Hcg Hown Hpay Hpc Htail".
    iPoseProof (is_tickslock_lock with "Hlkt") as "#Hlk2".
    iPoseProof (spi_80 with "Htext") as "Hi70".
    iPoseProof (spi_84 with "Htext") as "Hi74".
    iPoseProof (spi_88 with "Htext") as "Hi78".
    iPoseProof (spi_8c with "Htext") as "Hi7c".
    (* +0x70 auipc a0,0x15 *)
    iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.sys_pause + 0x80)) (mword_of_int 10 : mword 5)
              (mword_of_int 0x15 : mword 20) N (trap_res true + (av - 8))%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi70").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    set (X0 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg
        (add_vec (mword_of_int (KernelSyms.sys_pause + 0x80) : mword 64) (auipc_off (mword_of_int 0x15 : mword 20)))]> N).
    change (<[Regidx (mword_of_int 10 : mword 5) := regval_into_reg
        (add_vec (mword_of_int (KernelSyms.sys_pause + 0x80) : mword 64) (auipc_off (mword_of_int 0x15 : mword 20)))]> N) with X0.
    assert (Hx74 : add_vec_int (mword_of_int (KernelSyms.sys_pause + 0x80) : mword 64) 4 = mword_of_int (KernelSyms.sys_pause + 0x84)) by pcstep.
    iEval (rewrite Hx74) in "Hpc".
    (* +0x74 addi a0,a0,1880 *)
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.sys_pause + 0x84)) (mword_of_int 10 : mword 5)
              (mword_of_int 10 : mword 5) (mword_of_int 0x790 : mword 12) X0 (trap_res true + (av - 8))%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi74").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (X1 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg
        (add_vec (X0 !!! Regidx (mword_of_int 10 : mword 5)) (sign_extend' 64 (mword_of_int 1936 : mword 12)))]> X0).
    change (<[Regidx (mword_of_int 10 : mword 5) := regval_into_reg
        (add_vec (X0 !!! Regidx (mword_of_int 10 : mword 5)) (sign_extend' 64 (mword_of_int 1936 : mword 12)))]> X0) with X1.
    assert (Hx78 : add_vec_int (mword_of_int (KernelSyms.sys_pause + 0x84) : mword 64) 4 = mword_of_int (KernelSyms.sys_pause + 0x88)) by pcstep.
    iEval (rewrite Hx78) in "Hpc".
    (* +0x78 jal ra,release *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.sys_pause + 0x88)) (mword_of_int 1 : mword 5)
              (mword_of_int 2089458 : mword 21) X1 (trap_res true + (av - 8))%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi78").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    set (X2 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg
        (add_vec_int (mword_of_int (KernelSyms.sys_pause + 0x88) : mword 64) 4)]> X1).
    change (<[Regidx (mword_of_int 1 : mword 5) := regval_into_reg
        (add_vec_int (mword_of_int (KernelSyms.sys_pause + 0x88) : mword 64) 4)]> X1) with X2.
    assert (Hjrl : add_vec (mword_of_int (KernelSyms.sys_pause + 0x88) : mword 64)
                     (sign_extend' 64 (mword_of_int 2089458 : mword 21)) = mword_of_int KernelSyms.release) by pcstep.
    iEval (rewrite Hjrl) in "Hpc".
    assert (HcsNX2 : callee_saved N X2).
    { rewrite /X2 /X1 /X0. apply callee_saved_insert_r; [vm_compute; reflexivity|].
      apply callee_saved_insert_r; [vm_compute; reflexivity|].
      apply callee_saved_insert_r; [vm_compute; reflexivity|]. apply callee_saved_refl. }
    assert (HbX2 : sp_base m X2 sp0) by exact (sp_base_cs m N X2 sp0 HcsNX2 Hbn).
    assert (HsX2 : sp_saved m X2) by exact (sp_saved_cs m N X2 HcsNX2 Hsn).
    assert (HX2ra : X2 !!! Regidx (mword_of_int 1 : mword 5)
                    = add_vec_int (mword_of_int (KernelSyms.sys_pause + 0x88) : mword 64) 4) by (rewrite /X2; apply upd_eq).
    assert (HX2a0 : X2 !!! Regidx (mword_of_int 10 : mword 5) = a_tickslock).
    { rewrite /X2 upd_ne; [| reg_neq]. rewrite /X1 upd_eq. rewrite /X0 upd_eq.
      rewrite /a_tickslock. apply bv_eq; vm_compute; reflexivity. }
    (* release(&tickslock) *)
    iApply (Release.wp_release_sconf γt a_tickslock "time"%string ticks_res X2
              0%nat true pj C (av - 8)%nat ({[lock_rank "time"]} ∪ lks)
              ltac:(rewrite HX2a0; apply sp_add_vec_0) ltac:(lia)
              with "Hcg Htext Hpc Hlk2 Htok HR Hown Hpay").
    iIntros (CIDr Hsr mrl) "Hcg Hpc %HcsX2 Hown".
    (* sp_exit0 is BALANCED at the tail: release strips exactly the rank it
       just took, so [Htail]'s [lks] is the entry set unchanged. *)
    pose proof (locks_below_not_elem lks (lock_rank "time") Hfresh) as Hnotin.
    assert (Hsetback : ({[lock_rank "time"]} ∪ lks) ∖ {[lock_rank "time"]} = lks)
      by (apply locks_add_del_below; lkbelow).
    iEval (rewrite Hsetback) in "Hown".
    assert (Hx7c : ret_pc (X2 !!! Regidx (mword_of_int 1 : mword 5)) = mword_of_int (KernelSyms.sys_pause + 0x8c))
      by (rewrite HX2ra; pcstep).
    iEval (rewrite Hx7c) in "Hpc".
    assert (HbRl : sp_base m mrl sp0) by exact (sp_base_cs m X2 mrl sp0 HcsX2 HbX2).
    assert (HsRl : sp_saved m mrl) by exact (sp_saved_cs m X2 mrl HcsX2 HsX2).
    (* +0x7c c.li a0,0 *)
    iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.sys_pause + 0x8c)) (mword_of_int 10 : mword 5)
              (mword_of_int 0 : mword 6) (zero_reg : mword 64) mrl (av - 8)%nat true
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(apply bv_eq; vm_compute; reflexivity) with "Hcg Hpc Hi7c").
    iIntros (CIDl Hsl) "Hcg Hpc".
    set (X3 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg (zero_reg : mword 64)]> mrl).
    change (<[Regidx (mword_of_int 10 : mword 5) := regval_into_reg (zero_reg : mword 64)]> mrl) with X3.
    assert (Hx7e : add_vec_int (mword_of_int (KernelSyms.sys_pause + 0x8c) : mword 64) 2 = mword_of_int (KernelSyms.sys_pause + 0x8e)) by pcstep.
    iEval (rewrite Hx7e) in "Hpc".
    assert (HcsRlX3 : callee_saved mrl X3).
    { rewrite /X3. apply callee_saved_insert_r; [vm_compute; reflexivity|]. apply callee_saved_refl. }
    iDestruct (cpu_own_transport CIDr CIDl 0 true pj C true ltac:(wp_next_chain)
                 with "Hown") as "Hown".
    rewrite /sp_tail.
    iSpecialize ("Htail" $! CIDl with "[%]"); [wp_next_chain|].
    iApply ("Htail" $! X3 (zero_reg : mword 64)
              with "[%] Hx1 Hx2 Hfree Hx7 Hcg Hown Hpc").
    split; [exact (sp_base_cs m mrl X3 sp0 HcsRlX3 HbRl) |].
    split; [exact (sp_saved_cs m mrl X3 HcsRlX3 HsRl) |].
    split; [rewrite /X3; apply upd_eq | left; reflexivity].
  Qed.

  (* ---- the killed (-1) exit: +0x8c .. the join at +0x7e ---- *)
  Lemma sp_exitk_body `{GEN : GenId} `{CID : CpuId} (CID0 : CPU)
      (γt : gname) (j : nat)
      (m N : regfile) (av : nat) (eb : bool) (C : iProp Σ)
      (sp0 pj tk : mword 64) (lks : gset nat) :
    (30 <= av)%nat ->
    eb = true ->
    (true = false \/ pj = zero_reg -> (CID : CPU) = CID0) ->
    sp_base m N sp0 -> sp_lregs N tk ->
    (* acquire's freshness premise -- see [sp_acq_body] where it originates *)
    locks_below lks (lock_rank "time") ->
    kernel_text -∗
    is_tickslock γt -∗
    pa_stk sp0 1 ↦₈ (m !!! Regidx (mword_of_int 1 : mword 5)) -∗
    pa_stk sp0 2 ↦₈ (m !!! Regidx (mword_of_int 8 : mword 5)) -∗
    pa_stk sp0 3 ↦₈ (m !!! Regidx (mword_of_int 9 : mword 5)) -∗
    pa_stk sp0 4 ↦₈ (m !!! Regidx (mword_of_int 18 : mword 5)) -∗
    pa_stk sp0 5 ↦₈ (m !!! Regidx (mword_of_int 19 : mword 5)) -∗
    (∃ w : bv 64, pa_stk sp0 6 ↦₈ w) -∗ (∃ w : bv 64, pa_stk sp0 7 ↦₈ w) -∗
    (∃ w : bv 64, pa_stk sp0 8 ↦₈ w) -∗
    locked γt cpu_id -∗ ticks_res -∗
    sie_cap_gpr N (trap_res true + (av - 8))%nat false pj -∗
    cpu_own 1 eb pj C false ({[lock_rank "time"]} ∪ lks) -∗ arm_pay 0 eb pj -∗
    pc_is (mword_of_int (KernelSyms.sys_pause + 0x9c)) -∗
    sp_tail CID0 j m av eb C sp0 pj lks -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hav Heb Hanch Hbn Hln Hfresh. subst eb.
    iIntros "#Htext #Hlkt Hy1 Hy2 Hy3 Hy4 Hy5 Hy6 Hy7 Hy8 Htok HR Hcg Hown Hpay Hpc Htail".
    iPoseProof (is_tickslock_lock with "Hlkt") as "#Hlk2".
    pose proof Hbn as Hbn'. destruct Hbn as (HNsp & HNs0 & HNhi).
    iPoseProof (spi_9c with "Htext") as "Hi8c".
    iPoseProof (spi_a0 with "Htext") as "Hi90".
    iPoseProof (spi_a4 with "Htext") as "Hi94".
    iPoseProof (spi_a8 with "Htext") as "Hi98".
    iPoseProof (spi_aa with "Htext") as "Hi9a".
    iPoseProof (spi_ac with "Htext") as "Hi9c".
    iPoseProof (spi_ae with "Htext") as "Hi9e".
    iPoseProof (spi_b0 with "Htext") as "Hia0".
    (* +0x8c auipc a0,0x15 *)
    iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.sys_pause + 0x9c)) (mword_of_int 10 : mword 5)
              (mword_of_int 0x15 : mword 20) N (trap_res true + (av - 8))%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi8c").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    set (K0 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg
        (add_vec (mword_of_int (KernelSyms.sys_pause + 0x9c) : mword 64) (auipc_off (mword_of_int 0x15 : mword 20)))]> N).
    change (<[Regidx (mword_of_int 10 : mword 5) := regval_into_reg
        (add_vec (mword_of_int (KernelSyms.sys_pause + 0x9c) : mword 64) (auipc_off (mword_of_int 0x15 : mword 20)))]> N) with K0.
    assert (Hk90 : add_vec_int (mword_of_int (KernelSyms.sys_pause + 0x9c) : mword 64) 4 = mword_of_int (KernelSyms.sys_pause + 0xa0)) by pcstep.
    iEval (rewrite Hk90) in "Hpc".
    (* +0x90 addi a0,a0,1852 *)
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.sys_pause + 0xa0)) (mword_of_int 10 : mword 5)
              (mword_of_int 10 : mword 5) (mword_of_int 0x774 : mword 12) K0 (trap_res true + (av - 8))%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi90").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (K1 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg
        (add_vec (K0 !!! Regidx (mword_of_int 10 : mword 5)) (sign_extend' 64 (mword_of_int 1908 : mword 12)))]> K0).
    change (<[Regidx (mword_of_int 10 : mword 5) := regval_into_reg
        (add_vec (K0 !!! Regidx (mword_of_int 10 : mword 5)) (sign_extend' 64 (mword_of_int 1908 : mword 12)))]> K0) with K1.
    assert (Hk94 : add_vec_int (mword_of_int (KernelSyms.sys_pause + 0xa0) : mword 64) 4 = mword_of_int (KernelSyms.sys_pause + 0xa4)) by pcstep.
    iEval (rewrite Hk94) in "Hpc".
    (* +0x94 jal ra,release *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.sys_pause + 0xa4)) (mword_of_int 1 : mword 5)
              (mword_of_int 2089430 : mword 21) K1 (trap_res true + (av - 8))%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi94").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    set (K2 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg
        (add_vec_int (mword_of_int (KernelSyms.sys_pause + 0xa4) : mword 64) 4)]> K1).
    change (<[Regidx (mword_of_int 1 : mword 5) := regval_into_reg
        (add_vec_int (mword_of_int (KernelSyms.sys_pause + 0xa4) : mword 64) 4)]> K1) with K2.
    assert (Hjrk : add_vec (mword_of_int (KernelSyms.sys_pause + 0xa4) : mword 64)
                     (sign_extend' 64 (mword_of_int 2089430 : mword 21)) = mword_of_int KernelSyms.release) by pcstep.
    iEval (rewrite Hjrk) in "Hpc".
    assert (HcsNK2 : callee_saved N K2).
    { rewrite /K2 /K1 /K0. apply callee_saved_insert_r; [vm_compute; reflexivity|].
      apply callee_saved_insert_r; [vm_compute; reflexivity|].
      apply callee_saved_insert_r; [vm_compute; reflexivity|]. apply callee_saved_refl. }
    assert (HbK2 : sp_base m K2 sp0) by exact (sp_base_cs m N K2 sp0 HcsNK2 Hbn').
    assert (HK2ra : K2 !!! Regidx (mword_of_int 1 : mword 5)
                    = add_vec_int (mword_of_int (KernelSyms.sys_pause + 0xa4) : mword 64) 4) by (rewrite /K2; apply upd_eq).
    assert (HK2a0 : K2 !!! Regidx (mword_of_int 10 : mword 5) = a_tickslock).
    { rewrite /K2 upd_ne; [| reg_neq]. rewrite /K1 upd_eq. rewrite /K0 upd_eq.
      rewrite /a_tickslock. apply bv_eq; vm_compute; reflexivity. }
    iApply (Release.wp_release_sconf γt a_tickslock "time"%string ticks_res K2
              0%nat true pj C (av - 8)%nat ({[lock_rank "time"]} ∪ lks)
              ltac:(rewrite HK2a0; apply sp_add_vec_0) ltac:(lia)
              with "Hcg Htext Hpc Hlk2 Htok HR Hown Hpay").
    iIntros (CIDr Hsr mrk) "Hcg Hpc %HcsK2 Hown".
    (* sp_exitk is BALANCED at the tail: release strips exactly the rank it
       just took, so [Htail]'s [lks] is the entry set unchanged. *)
    pose proof (locks_below_not_elem lks (lock_rank "time") Hfresh) as Hnotin.
    assert (Hsetback : ({[lock_rank "time"]} ∪ lks) ∖ {[lock_rank "time"]} = lks)
      by (apply locks_add_del_below; lkbelow).
    iEval (rewrite Hsetback) in "Hown".
    assert (Hk98 : ret_pc (K2 !!! Regidx (mword_of_int 1 : mword 5)) = mword_of_int (KernelSyms.sys_pause + 0xa8))
      by (rewrite HK2ra; pcstep).
    iEval (rewrite Hk98) in "Hpc".
    assert (HbRk : sp_base m mrk sp0) by exact (sp_base_cs m K2 mrk sp0 HcsK2 HbK2).
    pose proof HbRk as HbRk'. destruct HbRk as (HRksp & HRks0 & HRkhi).
    (* +0x98 c.li a0,-1 *)
    iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.sys_pause + 0xa8)) (mword_of_int 10 : mword 5)
              (mword_of_int 63 : mword 6) (mword_of_int (-1) : mword 64) mrk (av - 8)%nat true
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(apply bv_eq; vm_compute; reflexivity) with "Hcg Hpc Hi98").
    iIntros (CIDk1 Hsk1) "Hcg Hpc".
    set (K3 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg (mword_of_int (-1) : mword 64)]> mrk).
    change (<[Regidx (mword_of_int 10 : mword 5) := regval_into_reg (mword_of_int (-1) : mword 64)]> mrk) with K3.
    assert (Hk9a : add_vec_int (mword_of_int (KernelSyms.sys_pause + 0xa8) : mword 64) 2 = mword_of_int (KernelSyms.sys_pause + 0xaa)) by pcstep.
    iEval (rewrite Hk9a) in "Hpc".
    assert (HK3sp : K3 !!! Regidx csp_rs1 = pa_stk sp0 8)
      by (rewrite /K3 upd_ne; [exact HRksp | reg_neq]).
    (* +0x9a/+0x9c/+0x9e c.ldsp s1/s2/s3 *)
    assert (Hd3 : add_vec (K3 !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000"))) = pa_stk sp0 3)
      by (rewrite HK3sp; apply sp_off5).
    iEval (rewrite -Hd3) in "Hy3".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.sys_pause + 0xaa)) (mword_of_int 5 : mword 6)
              (mword_of_int 9 : mword 5) K3 (av - 8)%nat (m !!! Regidx (mword_of_int 9 : mword 5)) true
              (dqm := DfracOwn 1) ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi9a Hy3").
    iIntros (CIDk2 Hsk2) "Hcg Hpc Hy3".
    iEval (rewrite Hd3) in "Hy3".
    set (K4 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 9 : mword 5))]> K3).
    change (<[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 9 : mword 5))]> K3) with K4.
    assert (Hk9c : add_vec_int (mword_of_int (KernelSyms.sys_pause + 0xaa) : mword 64) 2 = mword_of_int (KernelSyms.sys_pause + 0xac)) by pcstep.
    iEval (rewrite Hk9c) in "Hpc".
    assert (HK4sp : K4 !!! Regidx csp_rs1 = pa_stk sp0 8)
      by (rewrite /K4 upd_ne; [exact HK3sp | reg_neq]).
    assert (Hd4 : add_vec (K4 !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000"))) = pa_stk sp0 4)
      by (rewrite HK4sp; apply sp_off4).
    iEval (rewrite -Hd4) in "Hy4".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.sys_pause + 0xac)) (mword_of_int 4 : mword 6)
              (mword_of_int 18 : mword 5) K4 (av - 8)%nat (m !!! Regidx (mword_of_int 18 : mword 5)) true
              (dqm := DfracOwn 1) ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi9c Hy4").
    iIntros (CIDk3 Hsk3) "Hcg Hpc Hy4".
    iEval (rewrite Hd4) in "Hy4".
    set (K5 := <[Regidx (mword_of_int 18 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 18 : mword 5))]> K4).
    change (<[Regidx (mword_of_int 18 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 18 : mword 5))]> K4) with K5.
    assert (Hk9e : add_vec_int (mword_of_int (KernelSyms.sys_pause + 0xac) : mword 64) 2 = mword_of_int (KernelSyms.sys_pause + 0xae)) by pcstep.
    iEval (rewrite Hk9e) in "Hpc".
    assert (HK5sp : K5 !!! Regidx csp_rs1 = pa_stk sp0 8)
      by (rewrite /K5 upd_ne; [exact HK4sp | reg_neq]).
    assert (Hd5 : add_vec (K5 !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000"))) = pa_stk sp0 5)
      by (rewrite HK5sp; apply sp_off3).
    iEval (rewrite -Hd5) in "Hy5".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.sys_pause + 0xae)) (mword_of_int 3 : mword 6)
              (mword_of_int 19 : mword 5) K5 (av - 8)%nat (m !!! Regidx (mword_of_int 19 : mword 5)) true
              (dqm := DfracOwn 1) ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi9e Hy5").
    iIntros (CIDk4 Hsk4) "Hcg Hpc Hy5".
    iEval (rewrite Hd5) in "Hy5".
    set (K6 := <[Regidx (mword_of_int 19 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 19 : mword 5))]> K5).
    change (<[Regidx (mword_of_int 19 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 19 : mword 5))]> K5) with K6.
    assert (Hka0 : add_vec_int (mword_of_int (KernelSyms.sys_pause + 0xae) : mword 64) 2 = mword_of_int (KernelSyms.sys_pause + 0xb0)) by pcstep.
    iEval (rewrite Hka0) in "Hpc".
    (* +0xa0 c.j : rejoin the shared epilogue *)
    iApply (wp_cj_s_sconf (mword_of_int (KernelSyms.sys_pause + 0xb0))
              (sign_extend' 21 (concat_vec (mword_of_int 2031 : mword 11) ('b"0")))
              K6 (av - 8)%nat true ltac:(vm_compute; reflexivity) with "Hcg Hpc Hia0").
    iIntros (CIDk5 Hsk5). iApply bi.later_intro. iIntros "Hcg Hpc".
    assert (Htg7e : add_vec (mword_of_int (KernelSyms.sys_pause + 0xb0) : mword 64)
                      (sign_extend' 64 (sign_extend' 21 (concat_vec (mword_of_int 2031 : mword 11) ('b"0"))))
                    = mword_of_int (KernelSyms.sys_pause + 0x8e)) by pcstep.
    iEval (rewrite Htg7e) in "Hpc".
    (* the frame's scratch slots, and the callee-saved report *)
    assert (HK6thr : forall c : mword 5, c <> mword_of_int 10 -> c <> mword_of_int 9 ->
              c <> mword_of_int 18 -> c <> mword_of_int 19 -> K6 !!! Regidx c = mrk !!! Regidx c).
    { intros c N10 N9 N18 N19.
      rewrite /K6 upd_ne; [| congruence]. rewrite /K5 upd_ne; [| congruence].
      rewrite /K4 upd_ne; [| congruence]. rewrite /K3 upd_ne; [reflexivity | congruence]. }
    iDestruct (cpu_own_transport CIDr CIDk5 0 true pj C true ltac:(wp_next_chain)
                 with "Hown") as "Hown".
    rewrite /sp_tail.
    iSpecialize ("Htail" $! CIDk5 with "[%]"); [wp_next_chain|].
    iApply ("Htail" $! K6 (mword_of_int (-1) : mword 64)
              with "[%] Hy1 Hy2 [Hy3 Hy4 Hy5 Hy6 Hy8] Hy7 Hcg Hown Hpc").
    { split.
      { unfold sp_base. split; [| split].
        - rewrite (HK6thr csp_rs1 ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)). exact HRksp.
        - rewrite (HK6thr (mword_of_int 8 : mword 5) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)). exact HRks0.
        - unfold sp_hi in *. destruct HRkhi as (H20&H21&H22&H23&H24&H25&H26&H27).
          split_and!.
          + rewrite (HK6thr (mword_of_int 20 : mword 5) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)). exact H20.
          + rewrite (HK6thr (mword_of_int 21 : mword 5) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)). exact H21.
          + rewrite (HK6thr (mword_of_int 22 : mword 5) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)). exact H22.
          + rewrite (HK6thr (mword_of_int 23 : mword 5) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)). exact H23.
          + rewrite (HK6thr (mword_of_int 24 : mword 5) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)). exact H24.
          + rewrite (HK6thr (mword_of_int 25 : mword 5) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)). exact H25.
          + rewrite (HK6thr (mword_of_int 26 : mword 5) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)). exact H26.
          + rewrite (HK6thr (mword_of_int 27 : mword 5) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)). exact H27. }
      split.
      { unfold sp_saved. split; [| split].
        - rewrite /K6 upd_ne; [| reg_neq]. rewrite /K5 upd_ne; [| reg_neq]. rewrite /K4. apply upd_eq.
        - rewrite /K6 upd_ne; [| reg_neq]. rewrite /K5. apply upd_eq.
        - rewrite /K6. apply upd_eq. }
      split.
      { rewrite /K6 upd_ne; [| reg_neq]. rewrite /K5 upd_ne; [| reg_neq].
        rewrite /K4 upd_ne; [| reg_neq]. rewrite /K3. apply upd_eq. }
      right; reflexivity. }
    { rewrite /sp_free. iFrame "Hy6 Hy8". iSplitL "Hy3". { iExists _. iExact "Hy3". }
      iSplitL "Hy4". { iExists _. iExact "Hy4". } iExists _. iExact "Hy5". }
  Qed.

  (* ---- the loop's post-park half: +0x5c .. the [bltu] at +0x66, and the
     two arms it dispatches to (the back edge at +0x4a, or the +0x6a reloads
     into the 0 exit).  This runs at the hart sleep() resumed on; the
     tickslock is HELD, so nothing inside moves the hart again. ---- *)
  Lemma sp_post_sleep_body `{GEN : GenId} `{CID : CpuId} (CID0 : CPU)
      (γt : gname) (j : nat)
      (m M : regfile) (av : nat) (eb : bool) (C : iProp Σ)
      (sp0 pj tk : mword 64) (nv : mword 32) (lks : gset nat) :
    (30 <= av)%nat ->
    eb = true ->
    (true = false \/ pj = zero_reg -> (CID : CPU) = CID0) ->
    sp_base m M sp0 -> sp_lregs M tk ->
    kernel_text -∗
    ▷ sp_loop CID0 γt j m av eb C sp0 pj tk nv lks -∗
    sp_exit0 CID0 γt j m av eb C sp0 pj lks -∗
    sp_exitk CID0 γt j m av eb C sp0 pj tk lks -∗
    sp_tail CID0 j m av eb C sp0 pj lks -∗
    pa_stk sp0 1 ↦₈ (m !!! Regidx (mword_of_int 1 : mword 5)) -∗
    pa_stk sp0 2 ↦₈ (m !!! Regidx (mword_of_int 8 : mword 5)) -∗
    pa_stk sp0 3 ↦₈ (m !!! Regidx (mword_of_int 9 : mword 5)) -∗
    pa_stk sp0 4 ↦₈ (m !!! Regidx (mword_of_int 18 : mword 5)) -∗
    pa_stk sp0 5 ↦₈ (m !!! Regidx (mword_of_int 19 : mword 5)) -∗
    (∃ w : bv 64, pa_stk sp0 6 ↦₈ w) -∗ (∃ w : bv 64, pa_stk sp0 8 ↦₈ w) -∗
    pa_add (pa_stk sp0 7) 4 ↦₄ nv -∗ sp_join7 sp0 -∗
    locked γt cpu_id -∗ ticks_res -∗
    sie_cap_gpr M (trap_res true + (av - 8))%nat false pj -∗
    cpu_own 1 eb pj C false ({[lock_rank "time"]} ∪ lks) -∗ arm_pay 0 eb pj -∗
    pc_is (mword_of_int (KernelSyms.sys_pause + 0x6a)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    (* NB: [eb] is deliberately NOT substituted here.  This body runs [iNext]
       over [cpu_own]; with [eb] literal [intr_count]'s [if eb] reduces,
       [iNext] descends into [IntrDefs.intr_res] and strips ITS later, after
       which the resource can no longer be folded back to [cpu_own]. *)
    intros Hav Heb Hanch Hbs Hls.
    iIntros "#Htext IH Hex0 Hexk Htl Hy1 Hy2 Hy3 Hy4 Hy5 Hy6 Hy8 Hnc Hjoin7
              Htok HR Hcg Hown Hpay Hpc".
    pose proof Hbs as HbSl. pose proof Hls as HlSl.
    destruct Hls as (Hs9 & Hs18 & Hs19).
    iPoseProof (spi_6a with "Htext") as "Hi5c".
    iPoseProof (spi_6e with "Htext") as "Hi5e".
    iPoseProof (spi_72 with "Htext") as "Hi62".
    iPoseProof (spi_76 with "Htext") as "Hi66".
    (* +0x6a lw a5,0(s2) : a5 := ticks.  s2 is the &ticks register now (the
       two loop pointers swapped when the sleep call site was split). *)
    iDestruct "HR" as (t1) "Hticks".
    assert (Hlwt : add_vec (rget M (mword_of_int 18 : mword 5))
                     (sign_extend' 64 (mword_of_int 0 : mword 12)) = a_ticks).
    { rgne. rewrite Hs18. apply sp_add_vec_0. }
    iEval (rewrite -Hlwt) in "Hticks".
    iApply (wp_lw_s_sconf (mword_of_int (KernelSyms.sys_pause + 0x6a)) (mword_of_int 15 : mword 5)
              (mword_of_int 18 : mword 5) (mword_of_int 0 : mword 12)
              M (trap_res true + (av - 8))%nat t1 false (dqm := DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi5c Hticks").
    iApply wp_next_off_intro. iIntros "Hcg Hpc Hticks".
    iEval (rewrite Hlwt) in "Hticks".
    iDestruct (ticks_res_intro t1 with "Hticks") as "HR".
    set (L5 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (sign_extend' 64 (t1 : mword 32))]> M).
    change (<[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (sign_extend' 64 (t1 : mword 32))]> M) with L5.
    assert (Hl5e : add_vec_int (mword_of_int (KernelSyms.sys_pause + 0x6a) : mword 64) 4 = mword_of_int (KernelSyms.sys_pause + 0x6e)) by pcstep.
    iEval (rewrite Hl5e) in "Hpc".
    (* +0x5e subw a5,a5,s3 *)
    iApply (wp_subw_s_sconf (mword_of_int (KernelSyms.sys_pause + 0x6e)) (mword_of_int 15 : mword 5)
              (mword_of_int 15 : mword 5) (mword_of_int 19 : mword 5) L5 (trap_res true + (av - 8))%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi5e").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    iEval (rgne; rgne) in "Hcg".
    set (L6 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg
        (sign_extend' 64 (sub_vec (subrange_vec_dec (L5 !!! Regidx (mword_of_int 15 : mword 5)) 31 0 : mword 32)
                                  (subrange_vec_dec (L5 !!! Regidx (mword_of_int 19 : mword 5)) 31 0 : mword 32)))]> L5).
    change (<[Regidx (mword_of_int 15 : mword 5) := regval_into_reg
        (sign_extend' 64 (sub_vec (subrange_vec_dec (L5 !!! Regidx (mword_of_int 15 : mword 5)) 31 0 : mword 32)
                                  (subrange_vec_dec (L5 !!! Regidx (mword_of_int 19 : mword 5)) 31 0 : mword 32)))]> L5) with L6.
    assert (Hl62 : add_vec_int (mword_of_int (KernelSyms.sys_pause + 0x6e) : mword 64) 4 = mword_of_int (KernelSyms.sys_pause + 0x72)) by pcstep.
    iEval (rewrite Hl62) in "Hpc".
    (* +0x62 lw a4,-52(s0) : a4 := n *)
    assert (HL6s0 : L6 !!! Regidx (mword_of_int 8 : mword 5) = sp0).
    { rewrite /L6 upd_ne; [| reg_neq]. rewrite /L5 upd_ne; [| reg_neq].
      destruct HbSl as (_&X&_). exact X. }
    assert (Hnad : add_vec (rget L6 (mword_of_int 8 : mword 5))
                    (sign_extend' 64 (mword_of_int 0xfcc : mword 12)) = pa_add (pa_stk sp0 7) 4).
    { rgne. rewrite HL6s0. apply sp_addr_n. }
    iEval (rewrite -Hnad) in "Hnc".
    iApply (wp_lw_s_sconf (mword_of_int (KernelSyms.sys_pause + 0x72)) (mword_of_int 14 : mword 5)
              (mword_of_int 8 : mword 5) (mword_of_int 0xfcc : mword 12) L6 (trap_res true + (av - 8))%nat nv false
              (dqm := DfracOwn 1) ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi62 Hnc").
    iApply wp_next_off_intro. iIntros "Hcg Hpc Hnc".
    iEval (rewrite Hnad) in "Hnc".
    set (L7 := <[Regidx (mword_of_int 14 : mword 5) := regval_into_reg (sign_extend' 64 nv)]> L6).
    change (<[Regidx (mword_of_int 14 : mword 5) := regval_into_reg (sign_extend' 64 nv)]> L6) with L7.
    assert (Hl66 : add_vec_int (mword_of_int (KernelSyms.sys_pause + 0x72) : mword 64) 4 = mword_of_int (KernelSyms.sys_pause + 0x76)) by pcstep.
    iEval (rewrite Hl66) in "Hpc".
    assert (HcsSlL7 : callee_saved M L7).
    { rewrite /L7 /L6 /L5. apply callee_saved_insert_r; [vm_compute; reflexivity|].
      apply callee_saved_insert_r; [vm_compute; reflexivity|].
      apply callee_saved_insert_r; [vm_compute; reflexivity|]. apply callee_saved_refl. }
    assert (HbL7 : sp_base m L7 sp0) by exact (sp_base_cs m M L7 sp0 HcsSlL7 HbSl).
    assert (HlL7 : sp_lregs L7 tk) by exact (sp_lregs_cs M L7 tk HcsSlL7 HlSl).
    (* +0x66 bltu a5,a4 : loop or leave *)
    destruct (zopz0zI_u (L7 !!! Regidx (mword_of_int 15 : mword 5))
                        (L7 !!! Regidx (mword_of_int 14 : mword 5))) eqn:Hlt.
    - (* still short of n ticks: back edge to +0x4a *)
      iApply (wp_bltu_taken_s_sconf (mword_of_int (KernelSyms.sys_pause + 0x76)) (mword_of_int 8148 : mword 13)
                (mword_of_int 14 : mword 5) (mword_of_int 15 : mword 5) L7 (trap_res true + (av - 8))%nat false
                ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                ltac:(rgne; rgne; exact Hlt)
                ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi66").
      (* the back edge applies the Löb IH, which arrives under a [▷]: this is
         the one site that needs a real [iNext] (it strips exactly that). *)
      iNext. iApply wp_next_off_intro. iIntros "Hcg Hpc".
      assert (Htg4a : add_vec (mword_of_int (KernelSyms.sys_pause + 0x76) : mword 64)
                        (sign_extend' 64 (mword_of_int 8148 : mword 13))
                      = mword_of_int (KernelSyms.sys_pause + 0x4a)) by pcstep.
      iEval (rewrite Htg4a) in "Hpc".
      rewrite /sp_loop.
      iSpecialize ("IH" $! CID with "[%]"); [wp_next_chain|].
      iApply ("IH" $! L7 with "[%] Hy1 Hy2 Hy3 Hy4 Hy5 Hy6 Hy8 Hnc Hjoin7 Htok HR Hcg Hown Hpay Hpc Hex0 Hexk Htl").
      split; [exact HbL7 | exact HlL7].
    - (* enough ticks: fall through, restore s1/s2/s3, take the 0 exit *)
      iApply (wp_bltu_fall_s_sconf (mword_of_int (KernelSyms.sys_pause + 0x76)) (mword_of_int 8148 : mword 13)
                (mword_of_int 14 : mword 5) (mword_of_int 15 : mword 5) L7 (trap_res true + (av - 8))%nat false
                ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                ltac:(rgne; rgne; exact Hlt)
                with "Hcg Hpc Hi66").
      iApply wp_next_off_intro. iIntros "Hcg Hpc".
      assert (Hl6a : add_vec_int (mword_of_int (KernelSyms.sys_pause + 0x76) : mword 64) 4 = mword_of_int (KernelSyms.sys_pause + 0x7a)) by pcstep.
      iEval (rewrite Hl6a) in "Hpc".
      iPoseProof (spi_7a with "Htext") as "Hi6a".
      iPoseProof (spi_7c with "Htext") as "Hi6c".
      iPoseProof (spi_7e with "Htext") as "Hi6e".
      pose proof HbL7 as HbL7'. destruct HbL7' as (HL7sp & HL7s0 & HL7hi).
      assert (He3 : add_vec (L7 !!! Regidx csp_rs1)
                      (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000"))) = pa_stk sp0 3)
        by (rewrite HL7sp; apply sp_off5).
      iEval (rewrite -He3) in "Hy3".
      iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.sys_pause + 0x7a)) (mword_of_int 5 : mword 6)
                (mword_of_int 9 : mword 5) L7 (trap_res true + (av - 8))%nat (m !!! Regidx (mword_of_int 9 : mword 5)) false
                (dqm := DfracOwn 1) ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi6a Hy3").
      iApply wp_next_off_intro. iIntros "Hcg Hpc Hy3".
      iEval (rewrite He3) in "Hy3".
      set (L8 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 9 : mword 5))]> L7).
      change (<[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 9 : mword 5))]> L7) with L8.
      assert (Hl6c : add_vec_int (mword_of_int (KernelSyms.sys_pause + 0x7a) : mword 64) 2 = mword_of_int (KernelSyms.sys_pause + 0x7c)) by pcstep.
      iEval (rewrite Hl6c) in "Hpc".
      assert (HL8sp : L8 !!! Regidx csp_rs1 = pa_stk sp0 8)
        by (rewrite /L8 upd_ne; [exact HL7sp | reg_neq]).
      assert (He4 : add_vec (L8 !!! Regidx csp_rs1)
                      (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000"))) = pa_stk sp0 4)
        by (rewrite HL8sp; apply sp_off4).
      iEval (rewrite -He4) in "Hy4".
      iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.sys_pause + 0x7c)) (mword_of_int 4 : mword 6)
                (mword_of_int 18 : mword 5) L8 (trap_res true + (av - 8))%nat (m !!! Regidx (mword_of_int 18 : mword 5)) false
                (dqm := DfracOwn 1) ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi6c Hy4").
      iApply wp_next_off_intro. iIntros "Hcg Hpc Hy4".
      iEval (rewrite He4) in "Hy4".
      set (L9 := <[Regidx (mword_of_int 18 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 18 : mword 5))]> L8).
      change (<[Regidx (mword_of_int 18 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 18 : mword 5))]> L8) with L9.
      assert (Hl6e : add_vec_int (mword_of_int (KernelSyms.sys_pause + 0x7c) : mword 64) 2 = mword_of_int (KernelSyms.sys_pause + 0x7e)) by pcstep.
      iEval (rewrite Hl6e) in "Hpc".
      assert (HL9sp : L9 !!! Regidx csp_rs1 = pa_stk sp0 8)
        by (rewrite /L9 upd_ne; [exact HL8sp | reg_neq]).
      assert (He5 : add_vec (L9 !!! Regidx csp_rs1)
                      (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000"))) = pa_stk sp0 5)
        by (rewrite HL9sp; apply sp_off3).
      iEval (rewrite -He5) in "Hy5".
      iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.sys_pause + 0x7e)) (mword_of_int 3 : mword 6)
                (mword_of_int 19 : mword 5) L9 (trap_res true + (av - 8))%nat (m !!! Regidx (mword_of_int 19 : mword 5)) false
                (dqm := DfracOwn 1) ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi6e Hy5").
      iApply wp_next_off_intro. iIntros "Hcg Hpc Hy5".
      iEval (rewrite He5) in "Hy5".
      set (L10 := <[Regidx (mword_of_int 19 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 19 : mword 5))]> L9).
      change (<[Regidx (mword_of_int 19 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 19 : mword 5))]> L9) with L10.
      assert (Hl70 : add_vec_int (mword_of_int (KernelSyms.sys_pause + 0x7e) : mword 64) 2 = mword_of_int (KernelSyms.sys_pause + 0x80)) by pcstep.
      iEval (rewrite Hl70) in "Hpc".
      iDestruct ("Hjoin7" with "Hnc") as "Hy7".
      assert (HL10thr : forall c : mword 5, c <> mword_of_int 9 -> c <> mword_of_int 18 ->
                c <> mword_of_int 19 -> L10 !!! Regidx c = L7 !!! Regidx c).
      { intros c N9 N18 N19.
        rewrite /L10 upd_ne; [| congruence]. rewrite /L9 upd_ne; [| congruence].
        rewrite /L8 upd_ne; [reflexivity | congruence]. }
      rewrite /sp_exit0.
      iSpecialize ("Hex0" $! CID with "[%]"); [wp_next_chain|].
      iApply ("Hex0" $! L10 with "[%] Hy1 Hy2 [Hy3 Hy4 Hy5 Hy6 Hy8] Hy7 Htok HR Hcg Hown Hpay Hpc Htl").
      { split.
        { unfold sp_base. split; [| split].
          - rewrite (HL10thr csp_rs1 ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)). exact HL7sp.
          - rewrite (HL10thr (mword_of_int 8 : mword 5) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)). exact HL7s0.
          - unfold sp_hi in *. destruct HL7hi as (H20&H21&H22&H23&H24&H25&H26&H27).
            split_and!.
            + rewrite (HL10thr (mword_of_int 20 : mword 5) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)). exact H20.
            + rewrite (HL10thr (mword_of_int 21 : mword 5) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)). exact H21.
            + rewrite (HL10thr (mword_of_int 22 : mword 5) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)). exact H22.
            + rewrite (HL10thr (mword_of_int 23 : mword 5) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)). exact H23.
            + rewrite (HL10thr (mword_of_int 24 : mword 5) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)). exact H24.
            + rewrite (HL10thr (mword_of_int 25 : mword 5) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)). exact H25.
            + rewrite (HL10thr (mword_of_int 26 : mword 5) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)). exact H26.
            + rewrite (HL10thr (mword_of_int 27 : mword 5) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)). exact H27. }
        unfold sp_saved. split; [| split].
        - rewrite /L10 upd_ne; [| reg_neq]. rewrite /L9 upd_ne; [| reg_neq]. rewrite /L8. apply upd_eq.
        - rewrite /L10 upd_ne; [| reg_neq]. rewrite /L9. apply upd_eq.
        - rewrite /L10. apply upd_eq. }
      { rewrite /sp_free. iFrame "Hy6 Hy8". iSplitL "Hy3". { iExists _. iExact "Hy3". }
        iSplitL "Hy4". { iExists _. iExact "Hy4". } iExists _. iExact "Hy5". }
  Qed.

  (* ---- one loop iteration: +0x4a .. the sleep() call, which parks ---- *)
  Lemma sp_loop_body `{GEN : GenId} `{CID : CpuId} (CID0 : CPU)
      (γs : list gname) (γt γl : gname) (j : nat)
      (m M : regfile) (av : nat) (eb : bool) (C : iProp Σ)
      (sp0 pj tk : mword 64) (nv : mword 32) (lks : gset nat) :
    (30 <= av)%nat ->
    eb = true ->
    (j < NPROC)%nat ->
    γs !! j = Some γl ->
    pj = proc_addr j ->
    (true = false \/ pj = zero_reg -> (CID : CPU) = CID0) ->
    sp_base m M sp0 -> sp_lregs M tk ->
    (* acquire's freshness premise, for the loop's re-acquire after sleep()
       -- see [sp_acq_body] where it originates *)
    locks_below lks (lock_rank "time") ->
    kernel_text -∗
    is_tickslock γt -∗
    procs_inv γs -∗
    panic_wp_any -∗
    ▷ sp_loop CID0 γt j m av eb C sp0 pj tk nv lks -∗
    sp_exit0 CID0 γt j m av eb C sp0 pj lks -∗
    sp_exitk CID0 γt j m av eb C sp0 pj tk lks -∗
    sp_tail CID0 j m av eb C sp0 pj lks -∗
    pa_stk sp0 1 ↦₈ (m !!! Regidx (mword_of_int 1 : mword 5)) -∗
    pa_stk sp0 2 ↦₈ (m !!! Regidx (mword_of_int 8 : mword 5)) -∗
    pa_stk sp0 3 ↦₈ (m !!! Regidx (mword_of_int 9 : mword 5)) -∗
    pa_stk sp0 4 ↦₈ (m !!! Regidx (mword_of_int 18 : mword 5)) -∗
    pa_stk sp0 5 ↦₈ (m !!! Regidx (mword_of_int 19 : mword 5)) -∗
    (∃ w : bv 64, pa_stk sp0 6 ↦₈ w) -∗ (∃ w : bv 64, pa_stk sp0 8 ↦₈ w) -∗
    pa_add (pa_stk sp0 7) 4 ↦₄ nv -∗ sp_join7 sp0 -∗
    locked γt cpu_id -∗ ticks_res -∗
    sie_cap_gpr M (trap_res true + (av - 8))%nat false pj -∗
    cpu_own 1 eb pj C false ({[lock_rank "time"]} ∪ lks) -∗ arm_pay 0 eb pj -∗
    pc_is (mword_of_int (KernelSyms.sys_pause + 0x4a)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    (* [sleep]'s contract names the parking proc as [proc_addr j] literally, so
       the caller's [pj] has to be spelled that way before the crossing. *)
    intros Hav Heb Hj Hjl Hpjv Hanch Hbn Hln Hfresh. subst pj.
    iIntros "#Htext #Hlkt #Hpinv #Hpanic IH Hex0 Hexk Htl
              Hy1 Hy2 Hy3 Hy4 Hy5 Hy6 Hy8 Hnc Hjoin7 Htok HR Hcg Hown Hpay Hpc".
    iPoseProof (is_tickslock_lock with "Hlkt") as "#Hlk2".
    assert (Hn1 : (Z.of_nat 1 + 1 < 2 ^ 31)%Z) by (vm_compute; reflexivity).
    assert (Hn0 : (Z.of_nat 0 + 1 < 2 ^ 31)%Z) by (vm_compute; reflexivity).
    pose proof Hbn as Hbn'. pose proof Hln as Hln'.
    iPoseProof (spi_4a with "Htext") as "Hi4a".
    iPoseProof (spi_4e with "Htext") as "Hi4e".
    iPoseProof (spi_52 with "Htext") as "Hi52".
    iPoseProof (spi_54 with "Htext") as "Hi54".
    iPoseProof (spi_56 with "Htext") as "Hi56".
    iPoseProof (spi_5a with "Htext") as "Hi5a".
    iPoseProof (spi_5c with "Htext") as "Hi5c".
    iPoseProof (spi_60 with "Htext") as "Hi60".
    iPoseProof (spi_64 with "Htext") as "Hi64".
    iPoseProof (spi_66 with "Htext") as "Hi66".
    (* +0x4a jal ra,myproc *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.sys_pause + 0x4a)) (mword_of_int 1 : mword 5)
              (mword_of_int 2092744 : mword 21) M (trap_res true + (av - 8))%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi4a").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    set (L0 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg
        (add_vec_int (mword_of_int (KernelSyms.sys_pause + 0x4a) : mword 64) 4)]> M).
    change (<[Regidx (mword_of_int 1 : mword 5) := regval_into_reg
        (add_vec_int (mword_of_int (KernelSyms.sys_pause + 0x4a) : mword 64) 4)]> M) with L0.
    assert (Hjmp : add_vec (mword_of_int (KernelSyms.sys_pause + 0x4a) : mword 64)
                     (sign_extend' 64 (mword_of_int 2092744 : mword 21)) = mword_of_int KernelSyms.myproc) by pcstep.
    iEval (rewrite Hjmp) in "Hpc".
    assert (HcsNL0 : callee_saved M L0).
    { rewrite /L0. apply callee_saved_insert_r; [vm_compute; reflexivity|]. apply callee_saved_refl. }
    assert (HbL0 : sp_base m L0 sp0) by exact (sp_base_cs m M L0 sp0 HcsNL0 Hbn').
    assert (HlL0 : sp_lregs L0 tk) by exact (sp_lregs_cs M L0 tk HcsNL0 Hln').
    assert (HL0ra : L0 !!! Regidx (mword_of_int 1 : mword 5)
                    = add_vec_int (mword_of_int (KernelSyms.sys_pause + 0x4a) : mword 64) 4) by (rewrite /L0; apply upd_eq).
    (* myproc/killed/sleep_prepare all run here with the tickslock STILL
       held (the C releases it only after sleep_prepare), so the ambient
       held set is [{[lock_rank "time"]} ∪ lks], matching [Hown]'s actual
       type -- not the bare [lks] this stretch is entered with.  "proc"
       (11) outranks "time" (8), so [Hfresh]'s bound lifts by
       [locks_below_mono] and carries across the held "time" singleton by
       [locks_below_union_singleton], exactly [ProofKexit]'s
       wait_lock -> proc shape. *)
    assert (Htime_lt_proc : (lock_rank "time" < lock_rank "proc")%nat)
      by (vm_compute; lia).
    assert (Hfresh_proc : locks_below ({[lock_rank "time"]} ∪ lks) (lock_rank "proc")).
    { apply locks_below_union_singleton; [exact Htime_lt_proc |].
      lkbelow. }
    iApply (Myproc.wp_myproc_sconf L0 (trap_res true + (av - 8))%nat 1%nat eb (proc_addr j) C false
              ({[lock_rank "time"]} ∪ lks) Hn1 ltac:(lia)
              with "Hcg Hown Htext Hpc").
    iApply wp_next_off_intro. iIntros (msM mfm) "%HmsM Hcg Hown Hpc %Hmp".
    destruct Hmp as (Hmpcs & Hmpa0).
    assert (Hl4e : ret_pc (L0 !!! Regidx (mword_of_int 1 : mword 5)) = mword_of_int (KernelSyms.sys_pause + 0x4e))
      by (rewrite HL0ra; pcstep).
    iEval (rewrite Hl4e) in "Hpc".
    assert (HbMp : sp_base m mfm sp0) by exact (sp_base_cs m L0 mfm sp0 Hmpcs HbL0).
    assert (HlMp : sp_lregs mfm tk) by exact (sp_lregs_cs L0 mfm tk Hmpcs HlL0).
    (* +0x4e jal ra,killed *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.sys_pause + 0x4e)) (mword_of_int 1 : mword 5)
              (mword_of_int 2094886 : mword 21) mfm (trap_res true + (av - 8))%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi4e").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    set (L1 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg
        (add_vec_int (mword_of_int (KernelSyms.sys_pause + 0x4e) : mword 64) 4)]> mfm).
    change (<[Regidx (mword_of_int 1 : mword 5) := regval_into_reg
        (add_vec_int (mword_of_int (KernelSyms.sys_pause + 0x4e) : mword 64) 4)]> mfm) with L1.
    assert (Hjkl : add_vec (mword_of_int (KernelSyms.sys_pause + 0x4e) : mword 64)
                     (sign_extend' 64 (mword_of_int 2094886 : mword 21)) = mword_of_int KernelSyms.killed) by pcstep.
    iEval (rewrite Hjkl) in "Hpc".
    assert (HcsMpL1 : callee_saved mfm L1).
    { rewrite /L1. apply callee_saved_insert_r; [vm_compute; reflexivity|]. apply callee_saved_refl. }
    assert (HbL1 : sp_base m L1 sp0) by exact (sp_base_cs m mfm L1 sp0 HcsMpL1 HbMp).
    assert (HlL1 : sp_lregs L1 tk) by exact (sp_lregs_cs mfm L1 tk HcsMpL1 HlMp).
    assert (HL1ra : L1 !!! Regidx (mword_of_int 1 : mword 5)
                    = add_vec_int (mword_of_int (KernelSyms.sys_pause + 0x4e) : mword 64) 4) by (rewrite /L1; apply upd_eq).
    assert (HL1a0 : L1 !!! Regidx (mword_of_int 10 : mword 5) = proc_addr j).
    { rewrite /L1 upd_ne; [| reg_neq]. rewrite Hmpa0. reflexivity. }
    iApply (Killed.wp_killed_sconf γs j γl L1 (trap_res true + (av - 8))%nat 1%nat eb (proc_addr j) C false
              ({[lock_rank "time"]} ∪ lks)
              HL1a0 Hj Hjl Hn1 ltac:(lia) Hfresh_proc
              with "Hcg Hown Htext Hpc Hpinv Hpanic").
    all: try lkbelow.
    iApply wp_next_off_intro. iIntros (mfk kl) "%Hkf Hcg Hown Hpc".
    destruct Hkf as (Hkcs & Hka0).
    assert (Hl52 : ret_pc (L1 !!! Regidx (mword_of_int 1 : mword 5)) = mword_of_int (KernelSyms.sys_pause + 0x52))
      by (rewrite HL1ra; pcstep).
    iEval (rewrite Hl52) in "Hpc".
    assert (HbKl : sp_base m mfk sp0) by exact (sp_base_cs m L1 mfk sp0 Hkcs HbL1).
    assert (HlKl : sp_lregs mfk tk) by exact (sp_lregs_cs L1 mfk tk Hkcs HlL1).
    (* +0x52 c.bnez a0 : killed -> the -1 exit *)
    destruct (neq_vec (mfk !!! Regidx (mword_of_int 10 : mword 5)) (zero_reg : mword 64)) eqn:Hkz.
    - (* killed: branch TAKEN to +0x8c *)
      iApply (wp_cbnez_taken_s_sconf (mword_of_int (KernelSyms.sys_pause + 0x52)) (mword_of_int 37 : mword 8)
                (Cregidx (mword_of_int 2)) (mword_of_int 10 : mword 5) mfk (trap_res true + (av - 8))%nat false
                ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                ltac:(rgne; exact Hkz)
                ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi52").
      iNext. iApply wp_next_off_intro. iIntros "Hcg Hpc".
      assert (Htg8c : add_vec (mword_of_int (KernelSyms.sys_pause + 0x52) : mword 64)
                        (sign_extend' 64 (sign_extend' 13 (concat_vec (mword_of_int 37 : mword 8) ('b"0"))))
                      = mword_of_int (KernelSyms.sys_pause + 0x9c)) by pcstep.
      iEval (rewrite Htg8c) in "Hpc".
      iDestruct ("Hjoin7" with "Hnc") as "Hy7".
      rewrite /sp_exitk.
      iSpecialize ("Hexk" $! CID with "[%]"); [wp_next_chain|].
      iApply ("Hexk" $! mfk with "[%] Hy1 Hy2 Hy3 Hy4 Hy5 Hy6 Hy7 Hy8 Htok HR Hcg Hown Hpay Hpc Htl").
      split; [exact HbKl | exact HlKl].
    - (* not killed: fall through to the sleep *)
      iApply (wp_cbnez_fall_s_sconf (mword_of_int (KernelSyms.sys_pause + 0x52)) (mword_of_int 37 : mword 8)
                (Cregidx (mword_of_int 2)) (mword_of_int 10 : mword 5) mfk (trap_res true + (av - 8))%nat false
                ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                ltac:(rgne; exact Hkz)
                with "Hcg Hpc Hi52").
      iApply wp_next_off_intro. iIntros "Hcg Hpc".
      assert (Hl54 : add_vec_int (mword_of_int (KernelSyms.sys_pause + 0x52) : mword 64) 2 = mword_of_int (KernelSyms.sys_pause + 0x54)) by pcstep.
      iEval (rewrite Hl54) in "Hpc".
      pose proof HlKl as HlKl2. destruct HlKl2 as (Hk9 & Hk18 & Hk19).
      (* THE SPLIT SLEEP PROTOCOL.  sleep_prepare records the channel while
         the tickslock is still held; the caller then RELEASES that lock
         itself, parks in sleep() -- whose contract names no condition lock
         at all -- and RE-ACQUIRES.  The window between the release and the
         re-acquire is the one stretch of the loop where the thread holds
         nothing, and it is exactly where the park happens.

         The whole stretch is written at the ABSTRACT [eb]: acquire, release
         and sleep all take it as a parameter, so the only thing that has to
         move is the ENTRY carve, which the loop's predicates spell at the
         literal [true].  ([eb] must stay abstract here because the killed
         branch's [iNext] would otherwise reduce [intr_count]'s [if eb] --
         see [sp_post_sleep_body].) *)
      assert (Hteb : trap_res eb = trap_res true) by (rewrite Heb; reflexivity).
      rewrite -Hteb.
      (* +0x54 c.mv a0,s2 : a0 := &ticks *)
      iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.sys_pause + 0x54)) (mword_of_int 10 : mword 5)
                (mword_of_int 18 : mword 5) mfk (trap_res eb + (av - 8))%nat false
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi54").
      iApply wp_next_off_intro. iIntros "Hcg Hpc".
      iEval (rgne) in "Hcg".
      set (L2 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg
          (add_vec zero_reg (mfk !!! Regidx (mword_of_int 18 : mword 5)))]> mfk).
      change (<[Regidx (mword_of_int 10 : mword 5) := regval_into_reg
          (add_vec zero_reg (mfk !!! Regidx (mword_of_int 18 : mword 5)))]> mfk) with L2.
      assert (Hl56 : add_vec_int (mword_of_int (KernelSyms.sys_pause + 0x54) : mword 64) 2 = mword_of_int (KernelSyms.sys_pause + 0x56)) by pcstep.
      iEval (rewrite Hl56) in "Hpc".
      (* +0x56 jal ra,sleep_prepare *)
      iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.sys_pause + 0x56)) (mword_of_int 1 : mword 5)
                (mword_of_int 2094278 : mword 21) L2 (trap_res eb + (av - 8))%nat false
                ltac:(vm_compute; discriminate) ltac:(rdok)
                ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi56").
      iApply wp_next_off_intro. iIntros "Hcg Hpc".
      set (L3 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg
          (add_vec_int (mword_of_int (KernelSyms.sys_pause + 0x56) : mword 64) 4)]> L2).
      change (<[Regidx (mword_of_int 1 : mword 5) := regval_into_reg
          (add_vec_int (mword_of_int (KernelSyms.sys_pause + 0x56) : mword 64) 4)]> L2) with L3.
      assert (Hjsp : add_vec (mword_of_int (KernelSyms.sys_pause + 0x56) : mword 64)
                       (sign_extend' 64 (mword_of_int 2094278 : mword 21)) = mword_of_int KernelSyms.sleep_prepare) by pcstep.
      iEval (rewrite Hjsp) in "Hpc".
      assert (HcsKlL3 : callee_saved mfk L3).
      { rewrite /L3 /L2. apply callee_saved_insert_r; [vm_compute; reflexivity|].
        apply callee_saved_insert_r; [vm_compute; reflexivity|]. apply callee_saved_refl. }
      assert (HbL3 : sp_base m L3 sp0) by exact (sp_base_cs m mfk L3 sp0 HcsKlL3 HbKl).
      assert (HlL3 : sp_lregs L3 tk) by exact (sp_lregs_cs mfk L3 tk HcsKlL3 HlKl).
      assert (HL3ra : L3 !!! Regidx (mword_of_int 1 : mword 5)
                      = add_vec_int (mword_of_int (KernelSyms.sys_pause + 0x56) : mword 64) 4) by (rewrite /L3; apply upd_eq).
      assert (HL3a0 : L3 !!! Regidx (mword_of_int 10 : mword 5) = a_ticks).
      { rewrite /L3 upd_ne; [| reg_neq]. rewrite /L2 upd_eq. rewrite Hk18. apply add_vec_zero_l. }
      assert (HL3nz : eq_vec (L3 !!! Regidx (mword_of_int 10 : mword 5)) (zero_reg : mword 64) = false)
        by (rewrite HL3a0 /a_ticks; vm_compute; reflexivity).
      assert (Hpav : (14 <= trap_res eb + (av - 8))%nat)
        by (rewrite Heb; change (trap_res true) with kv_frame_slots; lia).
      (* =================== sleep_prepare(&ticks) =================== *)
      iApply (SleepPrepare.wp_sleep_prepare_sconf γs j γl L3
                (trap_res eb + (av - 8))%nat 1%nat eb C false ({[lock_rank "time"]} ∪ lks)
                Hj Hjl HL3nz Hn1 Hpav Hfresh_proc
                with "Hcg Hown Htext Hpc Hpinv Hpanic").
      all: try lkbelow.
      iApply wp_next_off_intro. iIntros (mfp) "%Hpcs Hcg Hown Hpc".
      assert (Hl5a : ret_pc (L3 !!! Regidx (mword_of_int 1 : mword 5)) = mword_of_int (KernelSyms.sys_pause + 0x5a))
        by (rewrite HL3ra; pcstep).
      iEval (rewrite Hl5a) in "Hpc".
      assert (HbPr : sp_base m mfp sp0) by exact (sp_base_cs m L3 mfp sp0 Hpcs HbL3).
      assert (HlPr : sp_lregs mfp tk) by exact (sp_lregs_cs L3 mfp tk Hpcs HlL3).
      pose proof HlPr as HlPr2. destruct HlPr2 as (Hp9 & Hp18 & Hp19).
      (* +0x5a c.mv a0,s1 : a0 := &tickslock *)
      iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.sys_pause + 0x5a)) (mword_of_int 10 : mword 5)
                (mword_of_int 9 : mword 5) mfp (trap_res eb + (av - 8))%nat false
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi5a").
      iApply wp_next_off_intro. iIntros "Hcg Hpc".
      iEval (rgne) in "Hcg".
      set (L4 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg
          (add_vec zero_reg (mfp !!! Regidx (mword_of_int 9 : mword 5)))]> mfp).
      change (<[Regidx (mword_of_int 10 : mword 5) := regval_into_reg
          (add_vec zero_reg (mfp !!! Regidx (mword_of_int 9 : mword 5)))]> mfp) with L4.
      assert (Hl5c : add_vec_int (mword_of_int (KernelSyms.sys_pause + 0x5a) : mword 64) 2 = mword_of_int (KernelSyms.sys_pause + 0x5c)) by pcstep.
      iEval (rewrite Hl5c) in "Hpc".
      (* +0x5c jal ra,release *)
      iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.sys_pause + 0x5c)) (mword_of_int 1 : mword 5)
                (mword_of_int 2089502 : mword 21) L4 (trap_res eb + (av - 8))%nat false
                ltac:(vm_compute; discriminate) ltac:(rdok)
                ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi5c").
      iApply wp_next_off_intro. iIntros "Hcg Hpc".
      set (L5 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg
          (add_vec_int (mword_of_int (KernelSyms.sys_pause + 0x5c) : mword 64) 4)]> L4).
      change (<[Regidx (mword_of_int 1 : mword 5) := regval_into_reg
          (add_vec_int (mword_of_int (KernelSyms.sys_pause + 0x5c) : mword 64) 4)]> L4) with L5.
      assert (Hjrl : add_vec (mword_of_int (KernelSyms.sys_pause + 0x5c) : mword 64)
                       (sign_extend' 64 (mword_of_int 2089502 : mword 21)) = mword_of_int KernelSyms.release) by pcstep.
      iEval (rewrite Hjrl) in "Hpc".
      assert (HcsPrL5 : callee_saved mfp L5).
      { rewrite /L5 /L4. apply callee_saved_insert_r; [vm_compute; reflexivity|].
        apply callee_saved_insert_r; [vm_compute; reflexivity|]. apply callee_saved_refl. }
      assert (HbL5 : sp_base m L5 sp0) by exact (sp_base_cs m mfp L5 sp0 HcsPrL5 HbPr).
      assert (HlL5 : sp_lregs L5 tk) by exact (sp_lregs_cs mfp L5 tk HcsPrL5 HlPr).
      assert (HL5ra : L5 !!! Regidx (mword_of_int 1 : mword 5)
                      = add_vec_int (mword_of_int (KernelSyms.sys_pause + 0x5c) : mword 64) 4) by (rewrite /L5; apply upd_eq).
      assert (HL5a0 : L5 !!! Regidx (mword_of_int 10 : mword 5) = a_tickslock).
      { rewrite /L5 upd_ne; [| reg_neq]. rewrite /L4 upd_eq. rewrite Hp9. apply add_vec_zero_l. }
      (* ==================== release(&tickslock) ==================== *)
      iApply (Release.wp_release_sconf γt a_tickslock "time"%string ticks_res L5
                0%nat eb (proc_addr j) C (av - 8)%nat ({[lock_rank "time"]} ∪ lks)
                ltac:(rewrite HL5a0; apply sp_add_vec_0) ltac:(lia)
                with "Hcg Htext Hpc Hlk2 Htok HR Hown Hpay").
      iIntros (CIDr Hsr mfr) "Hcg Hpc %Hrcs Hown".
      (* the release/re-acquire window: nothing is held across sleep() *)
      pose proof (locks_below_not_elem lks (lock_rank "time") Hfresh) as Hnotin.
      assert (Hsetback : ({[lock_rank "time"]} ∪ lks) ∖ {[lock_rank "time"]} = lks)
      by (apply locks_add_del_below; lkbelow).
      iEval (rewrite Hsetback) in "Hown".
      assert (Hl60 : ret_pc (L5 !!! Regidx (mword_of_int 1 : mword 5)) = mword_of_int (KernelSyms.sys_pause + 0x60))
        by (rewrite HL5ra; pcstep).
      iEval (rewrite Hl60) in "Hpc".
      assert (HbRl : sp_base m mfr sp0) by exact (sp_base_cs m L5 mfr sp0 Hrcs HbL5).
      assert (HlRl : sp_lregs mfr tk) by exact (sp_lregs_cs L5 mfr tk Hrcs HlL5).
      (* +0x60 jal ra,sleep *)
      iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.sys_pause + 0x60)) (mword_of_int 1 : mword 5)
                (mword_of_int 2094328 : mword 21) mfr (av - 8)%nat eb
                ltac:(vm_compute; discriminate) ltac:(rdok)
                ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi60").
      iIntros (CIDj Hsj) "Hcg Hpc".
      set (L6 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg
          (add_vec_int (mword_of_int (KernelSyms.sys_pause + 0x60) : mword 64) 4)]> mfr).
      change (<[Regidx (mword_of_int 1 : mword 5) := regval_into_reg
          (add_vec_int (mword_of_int (KernelSyms.sys_pause + 0x60) : mword 64) 4)]> mfr) with L6.
      assert (Hjsl : add_vec (mword_of_int (KernelSyms.sys_pause + 0x60) : mword 64)
                       (sign_extend' 64 (mword_of_int 2094328 : mword 21)) = mword_of_int KernelSyms.sleep) by pcstep.
      iEval (rewrite Hjsl) in "Hpc".
      assert (HcsRlL6 : callee_saved mfr L6).
      { rewrite /L6. apply callee_saved_insert_r; [vm_compute; reflexivity|]. apply callee_saved_refl. }
      assert (HbL6 : sp_base m L6 sp0) by exact (sp_base_cs m mfr L6 sp0 HcsRlL6 HbRl).
      assert (HlL6 : sp_lregs L6 tk) by exact (sp_lregs_cs mfr L6 tk HcsRlL6 HlRl).
      assert (HL6ra : L6 !!! Regidx (mword_of_int 1 : mword 5)
                      = add_vec_int (mword_of_int (KernelSyms.sys_pause + 0x60) : mword 64) 4) by (rewrite /L6; apply upd_eq).
      (* ========================== sleep() ==========================
         THE PARK.  No condition lock in the contract at all -- the caller
         released it two instructions ago -- and at [eb = true] the two
         extra premises are both [emp]. *)
      iDestruct (cpu_own_transport CIDr CIDj 0 eb (proc_addr j) C eb ltac:(wp_next_chain)
                   with "Hown") as "Hown".
      iApply (Sleep.wp_sleep_sconf γs j γl L6 (av - 8)%nat eb C lks Hj Hjl ltac:(lia)
                ltac:(lkbelow)
                with "Hcg Hown Htext Hpc Hpinv Hpanic [] []").
      all: try lkbelow.
      { rewrite Heb /trap_csrs_ext. done. }
      { rewrite Heb /cpu_claim_ext. done. }
      (* SLEEP RETURNS ON HART [CIDs]. *)
      iIntros (CIDs Hss mfs) "%Hscs Hcg Hown Hpc Htcx Hclmx".
      iClear "Htcx". iClear "Hclmx".
      assert (Hl64 : ret_pc (L6 !!! Regidx (mword_of_int 1 : mword 5)) = mword_of_int (KernelSyms.sys_pause + 0x64))
        by (rewrite HL6ra; pcstep).
      iEval (rewrite Hl64) in "Hpc".
      assert (HbSl : sp_base m mfs sp0) by exact (sp_base_cs m L6 mfs sp0 Hscs HbL6).
      assert (HlSl : sp_lregs mfs tk) by exact (sp_lregs_cs L6 mfs tk Hscs HlL6).
      pose proof HlSl as HlSl2. destruct HlSl2 as (Hs9 & Hs18 & Hs19).
      (* +0x64 c.mv a0,s1 : a0 := &tickslock *)
      iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.sys_pause + 0x64)) (mword_of_int 10 : mword 5)
                (mword_of_int 9 : mword 5) mfs (av - 8)%nat eb
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi64").
      iIntros (CIDm Hsm) "Hcg Hpc".
      iEval (rgne) in "Hcg".
      set (L7 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg
          (add_vec zero_reg (mfs !!! Regidx (mword_of_int 9 : mword 5)))]> mfs).
      change (<[Regidx (mword_of_int 10 : mword 5) := regval_into_reg
          (add_vec zero_reg (mfs !!! Regidx (mword_of_int 9 : mword 5)))]> mfs) with L7.
      assert (Hl66 : add_vec_int (mword_of_int (KernelSyms.sys_pause + 0x64) : mword 64) 2 = mword_of_int (KernelSyms.sys_pause + 0x66)) by pcstep.
      iEval (rewrite Hl66) in "Hpc".
      (* +0x66 jal ra,acquire *)
      iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.sys_pause + 0x66)) (mword_of_int 1 : mword 5)
                (mword_of_int 2089356 : mword 21) L7 (av - 8)%nat eb
                ltac:(vm_compute; discriminate) ltac:(rdok)
                ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi66").
      iIntros (CIDn Hsn) "Hcg Hpc".
      set (L8 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg
          (add_vec_int (mword_of_int (KernelSyms.sys_pause + 0x66) : mword 64) 4)]> L7).
      change (<[Regidx (mword_of_int 1 : mword 5) := regval_into_reg
          (add_vec_int (mword_of_int (KernelSyms.sys_pause + 0x66) : mword 64) 4)]> L7) with L8.
      assert (Hjaq : add_vec (mword_of_int (KernelSyms.sys_pause + 0x66) : mword 64)
                       (sign_extend' 64 (mword_of_int 2089356 : mword 21)) = mword_of_int KernelSyms.acquire) by pcstep.
      iEval (rewrite Hjaq) in "Hpc".
      assert (HcsSlL8 : callee_saved mfs L8).
      { rewrite /L8 /L7. apply callee_saved_insert_r; [vm_compute; reflexivity|].
        apply callee_saved_insert_r; [vm_compute; reflexivity|]. apply callee_saved_refl. }
      assert (HbL8 : sp_base m L8 sp0) by exact (sp_base_cs m mfs L8 sp0 HcsSlL8 HbSl).
      assert (HlL8 : sp_lregs L8 tk) by exact (sp_lregs_cs mfs L8 tk HcsSlL8 HlSl).
      assert (HL8ra : L8 !!! Regidx (mword_of_int 1 : mword 5)
                      = add_vec_int (mword_of_int (KernelSyms.sys_pause + 0x66) : mword 64) 4) by (rewrite /L8; apply upd_eq).
      assert (HL8a0 : L8 !!! Regidx (mword_of_int 10 : mword 5) = a_tickslock).
      { rewrite /L8 upd_ne; [| reg_neq]. rewrite /L7 upd_eq. rewrite Hs9. apply add_vec_zero_l. }
      (* ==================== acquire(&tickslock) ==================== *)
      iDestruct (cpu_own_transport CIDs CIDn 0 eb (proc_addr j) C eb ltac:(wp_next_chain)
                   with "Hown") as "Hown".
      iApply (Acquire.wp_acquire_sconf γt "time"%string ticks_res L8 0%nat eb (proc_addr j) C
                (av - 8)%nat eb lks Hn0 ltac:(lia) Hfresh with "Hcg Hown Htext Hpc [] Hpanic").
      all: try lkbelow.
      { iEval (rewrite HL8a0). iExact "Hlk2". }
      iIntros (CIDa Hsa msA mfa) "%HmsA Hcg Hpc %Hacs Htok HR Hown Hpay".
      assert (Hl6a : ret_pc (L8 !!! Regidx (mword_of_int 1 : mword 5)) = mword_of_int (KernelSyms.sys_pause + 0x6a))
        by (rewrite HL8ra; pcstep).
      iEval (rewrite Hl6a) in "Hpc".
      assert (HbAq : sp_base m mfa sp0) by exact (sp_base_cs m L8 mfa sp0 Hacs HbL8).
      assert (HlAq : sp_lregs mfa tk) by exact (sp_lregs_cs L8 mfa tk Hacs HlL8).
      (* ... and the entry carve is back in the loop's own spelling *)
      rewrite Hteb.
      iApply (sp_post_sleep_body (CID := CIDa) CID0 γt j m mfa av eb C sp0 (proc_addr j) tk nv lks
                Hav Heb ltac:(wp_next_chain) HbAq HlAq
                with "Htext IH Hex0 Hexk Htl Hy1 Hy2 Hy3 Hy4 Hy5 Hy6 Hy8 Hnc Hjoin7
                      Htok HR Hcg Hown Hpay Hpc").
  Qed.

  (* ---- +0x1a: a0 := &tickslock, acquire, the [n == 0] dispatch, the loop
     set-up, and the wait loop's own Löb ---- *)
  Lemma sp_acq_body `{GEN : GenId} `{CID : CpuId} (CID0 : CPU)
      (γs : list gname) (γt γl : gname) (j : nat)
      (m M : regfile) (nv : mword 32) (av : nat) (eb : bool) (C : iProp Σ)
      (sp0 pj : mword 64) (lks : gset nat) :
    (30 <= av)%nat ->
    eb = true ->
    (j < NPROC)%nat ->
    γs !! j = Some γl ->
    pj = proc_addr j ->
    (true = false \/ pj = zero_reg -> (CID : CPU) = CID0) ->
    sp_base m M sp0 -> sp_saved m M ->
    (* acquire's freshness premise: this hart does not already hold "time" *)
    locks_below lks (lock_rank "time") ->
    kernel_text -∗
    is_tickslock γt -∗
    procs_inv γs -∗
    panic_wp_any -∗
    pa_stk sp0 1 ↦₈ (m !!! Regidx (mword_of_int 1 : mword 5)) -∗
    pa_stk sp0 2 ↦₈ (m !!! Regidx (mword_of_int 8 : mword 5)) -∗
    sp_free sp0 -∗
    pa_add (pa_stk sp0 7) 4 ↦₄ nv -∗ sp_join7 sp0 -∗
    sie_cap_gpr M (av - 8)%nat true pj -∗
    cpu_own 0 eb pj C true lks -∗
    pc_is (mword_of_int (KernelSyms.sys_pause + 0x1a)) -∗
    sp_tail CID0 j m av eb C sp0 pj lks -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hav Heb Hj Hjl Hpjv Hanch Hb Hsv Hfresh.
    iIntros "#Htext #Hlkt #Hpinv #Hpanic Hs1 Hs2 Hfree Hnc Hjoin7
              Hcg Hown Hpc Htail".
    iPoseProof (is_tickslock_lock with "Hlkt") as "#Hlk2".
    assert (Hn0 : (Z.of_nat 0 + 1 < 2 ^ 31)%Z) by (vm_compute; reflexivity).
    pose proof Hb as Hbq. destruct Hbq as (HMsp & HMs0 & HMhi).
    iPoseProof (spi_1a with "Htext") as "Hi1a".
    iPoseProof (spi_1e with "Htext") as "Hi1e".
    iPoseProof (spi_22 with "Htext") as "Hi22".
    (* +0x1a auipc a0,0x15 *)
    iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.sys_pause + 0x1a)) (mword_of_int 10 : mword 5)
              (mword_of_int 0x15 : mword 20) M (av - 8)%nat true
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi1a").
    iIntros (CIDq1 Hsq1) "Hcg Hpc".
    set (Q0 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg
        (add_vec (mword_of_int (KernelSyms.sys_pause + 0x1a) : mword 64) (auipc_off (mword_of_int 0x15 : mword 20)))]> M).
    change (<[Regidx (mword_of_int 10 : mword 5) := regval_into_reg
        (add_vec (mword_of_int (KernelSyms.sys_pause + 0x1a) : mword 64) (auipc_off (mword_of_int 0x15 : mword 20)))]> M) with Q0.
    assert (Hq1e : add_vec_int (mword_of_int (KernelSyms.sys_pause + 0x1a) : mword 64) 4 = mword_of_int (KernelSyms.sys_pause + 0x1e)) by pcstep.
    iEval (rewrite Hq1e) in "Hpc".
    (* +0x1e addi a0,a0,1966 : a0 := &tickslock *)
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.sys_pause + 0x1e)) (mword_of_int 10 : mword 5)
              (mword_of_int 10 : mword 5) (mword_of_int 0x7f6 : mword 12) Q0 (av - 8)%nat true
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi1e").
    iIntros (CIDq2 Hsq2) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (Q1 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg
        (add_vec (Q0 !!! Regidx (mword_of_int 10 : mword 5)) (sign_extend' 64 (mword_of_int 2038 : mword 12)))]> Q0).
    change (<[Regidx (mword_of_int 10 : mword 5) := regval_into_reg
        (add_vec (Q0 !!! Regidx (mword_of_int 10 : mword 5)) (sign_extend' 64 (mword_of_int 2038 : mword 12)))]> Q0) with Q1.
    assert (Hq22 : add_vec_int (mword_of_int (KernelSyms.sys_pause + 0x1e) : mword 64) 4 = mword_of_int (KernelSyms.sys_pause + 0x22)) by pcstep.
    iEval (rewrite Hq22) in "Hpc".
    (* +0x22 jal ra,acquire *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.sys_pause + 0x22)) (mword_of_int 1 : mword 5)
              (mword_of_int 2089424 : mword 21) Q1 (av - 8)%nat true
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi22").
    iIntros (CIDq3 Hsq3) "Hcg Hpc".
    set (Q2 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg
        (add_vec_int (mword_of_int (KernelSyms.sys_pause + 0x22) : mword 64) 4)]> Q1).
    change (<[Regidx (mword_of_int 1 : mword 5) := regval_into_reg
        (add_vec_int (mword_of_int (KernelSyms.sys_pause + 0x22) : mword 64) 4)]> Q1) with Q2.
    assert (Hjaq : add_vec (mword_of_int (KernelSyms.sys_pause + 0x22) : mword 64)
                     (sign_extend' 64 (mword_of_int 2089424 : mword 21)) = mword_of_int KernelSyms.acquire) by pcstep.
    iEval (rewrite Hjaq) in "Hpc".
    assert (HcsMQ2 : callee_saved M Q2).
    { rewrite /Q2 /Q1 /Q0. apply callee_saved_insert_r; [vm_compute; reflexivity|].
      apply callee_saved_insert_r; [vm_compute; reflexivity|].
      apply callee_saved_insert_r; [vm_compute; reflexivity|]. apply callee_saved_refl. }
    assert (HbQ2 : sp_base m Q2 sp0) by exact (sp_base_cs m M Q2 sp0 HcsMQ2 Hb).
    assert (HsQ2 : sp_saved m Q2) by exact (sp_saved_cs m M Q2 HcsMQ2 Hsv).
    assert (HQ2ra : Q2 !!! Regidx (mword_of_int 1 : mword 5)
                    = add_vec_int (mword_of_int (KernelSyms.sys_pause + 0x22) : mword 64) 4) by (rewrite /Q2; apply upd_eq).
    assert (HQ2a0 : Q2 !!! Regidx (mword_of_int 10 : mword 5) = a_tickslock).
    { rewrite /Q2 upd_ne; [| reg_neq]. rewrite /Q1 upd_eq. rewrite /Q0 upd_eq.
      rewrite /a_tickslock. apply bv_eq; vm_compute; reflexivity. }
    (* ===================== acquire(&tickslock) ===================== *)
    iDestruct (cpu_own_transport CID CIDq3 0 eb pj C true ltac:(wp_next_chain)
                 with "Hown") as "Hown".
    iApply (Acquire.wp_acquire_sconf γt "time"%string ticks_res Q2 0%nat eb pj C (av - 8)%nat true lks
              Hn0 ltac:(lia) Hfresh with "Hcg Hown Htext Hpc [] Hpanic").
    all: try lkbelow.
    { iEval (rewrite HQ2a0). iExact "Hlk2". }
    iIntros (CIDa Hsa msA Macq) "%HmsA Hcg Hpc %HcsQ2 Htok HR Hown Hpay".
    assert (Hq26 : ret_pc (Q2 !!! Regidx (mword_of_int 1 : mword 5)) = mword_of_int (KernelSyms.sys_pause + 0x26))
      by (rewrite HQ2ra; pcstep).
    iEval (rewrite Hq26) in "Hpc".
    assert (HbAq : sp_base m Macq sp0) by exact (sp_base_cs m Q2 Macq sp0 HcsQ2 HbQ2).
    assert (HsAq : sp_saved m Macq) by exact (sp_saved_cs m Q2 Macq HcsQ2 HsQ2).
    assert (HAqs0 : Macq !!! Regidx (mword_of_int 8 : mword 5) = sp0)
      by (destruct HbAq as (_&X&_); exact X).
    (* +0x26 lw a5,-52(s0) : reload n *)
    assert (Haq_n : add_vec (rget Macq (mword_of_int 8 : mword 5))
                      (sign_extend' 64 (mword_of_int 0xfcc : mword 12)) = pa_add (pa_stk sp0 7) 4).
    { rgne. rewrite HAqs0. apply sp_addr_n. }
    iEval (rewrite -Haq_n) in "Hnc".
    iPoseProof (spi_26 with "Htext") as "Hi26".
    iApply (wp_lw_s_sconf (mword_of_int (KernelSyms.sys_pause + 0x26)) (mword_of_int 15 : mword 5)
              (mword_of_int 8 : mword 5) (mword_of_int 0xfcc : mword 12) Macq (trap_res true + (av - 8))%nat nv false
              (dqm := DfracOwn 1) ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi26 Hnc").
    iApply wp_next_off_intro. iIntros "Hcg Hpc Hnc".
    iEval (rewrite Haq_n) in "Hnc".
    set (Qe := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (sign_extend' 64 nv)]> Macq).
    change (<[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (sign_extend' 64 nv)]> Macq) with Qe.
    assert (Hq2a : add_vec_int (mword_of_int (KernelSyms.sys_pause + 0x26) : mword 64) 4 = mword_of_int (KernelSyms.sys_pause + 0x2a)) by pcstep.
    iEval (rewrite Hq2a) in "Hpc".
    assert (HcsAqQe : callee_saved Macq Qe).
    { rewrite /Qe. apply callee_saved_insert_r; [vm_compute; reflexivity|]. apply callee_saved_refl. }
    assert (HbQe : sp_base m Qe sp0) by exact (sp_base_cs m Macq Qe sp0 HcsAqQe HbAq).
    assert (HsQe : sp_saved m Qe) by exact (sp_saved_cs m Macq Qe HcsAqQe HsAq).
    assert (HQea5 : Qe !!! Regidx (mword_of_int 15 : mword 5) = sign_extend' 64 nv)
      by (rewrite /Qe; apply upd_eq).
    assert (HQesp : Qe !!! Regidx csp_rs1 = pa_stk sp0 8) by (destruct HbQe as (X&_); exact X).

    (* ================ the [n == 0] dispatch, at +0x2a ================ *)
    iPoseProof (spi_2a with "Htext") as "Hi2a".
    destruct (eq_vec (Qe !!! Regidx (mword_of_int 15 : mword 5)) (zero_reg : mword 64)) eqn:Hz.
    - (* n == 0: the loop is skipped entirely *)
      iApply (wp_cbeqz_taken_s_sconf (mword_of_int (KernelSyms.sys_pause + 0x2a)) (mword_of_int 43 : mword 8)
                (Cregidx (mword_of_int 7)) (mword_of_int 15 : mword 5) Qe (trap_res true + (av - 8))%nat false
                ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                ltac:(rgne; exact Hz)
                ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi2a").
      iApply bi.later_intro. iApply wp_next_off_intro. iIntros "Hcg Hpc".
      assert (Htg70 : add_vec (mword_of_int (KernelSyms.sys_pause + 0x2a) : mword 64)
                        (sign_extend' 64 (sign_extend' 13 (concat_vec (mword_of_int 43 : mword 8) ('b"0"))))
                      = mword_of_int (KernelSyms.sys_pause + 0x80)) by pcstep.
      iEval (rewrite Htg70) in "Hpc".
      iDestruct ("Hjoin7" with "Hnc") as "Hx7".
      iApply (sp_exit0_body (CID := CIDa) CID0 γt j m Qe av eb C sp0 pj lks
                Hav Heb ltac:(wp_next_chain) HbQe HsQe Hfresh
                with "Htext Hlkt Hs1 Hs2 Hfree Hx7 Htok HR Hcg Hown Hpay Hpc Htail").
    - (* n <> 0: spill s1/s2/s3 and enter the wait loop *)
      iApply (wp_cbeqz_fall_s_sconf (mword_of_int (KernelSyms.sys_pause + 0x2a)) (mword_of_int 43 : mword 8)
                (Cregidx (mword_of_int 7)) (mword_of_int 15 : mword 5) Qe (trap_res true + (av - 8))%nat false
                ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                ltac:(rgne; exact Hz)
                with "Hcg Hpc Hi2a").
      iApply wp_next_off_intro. iIntros "Hcg Hpc".
      assert (Hq2c : add_vec_int (mword_of_int (KernelSyms.sys_pause + 0x2a) : mword 64) 2 = mword_of_int (KernelSyms.sys_pause + 0x2c)) by pcstep.
      iEval (rewrite Hq2c) in "Hpc".
      rewrite /sp_free.
      iDestruct "Hfree" as "(Hf3 & Hf4 & Hf5 & Hf6 & Hf8)".
      iDestruct "Hf3" as (w3) "Hs3". iDestruct "Hf4" as (w4) "Hs4". iDestruct "Hf5" as (w5) "Hs5".
      pose proof HsQe as HsQe'. destruct HsQe' as (Hqe9 & Hqe18 & Hqe19).
      assert (Hc3 : add_vec (Qe !!! Regidx csp_rs1)
                      (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000"))) = pa_stk sp0 3)
        by (rewrite HQesp; apply sp_off5).
      assert (Hc4 : add_vec (Qe !!! Regidx csp_rs1)
                      (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000"))) = pa_stk sp0 4)
        by (rewrite HQesp; apply sp_off4).
      assert (Hc5 : add_vec (Qe !!! Regidx csp_rs1)
                      (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000"))) = pa_stk sp0 5)
        by (rewrite HQesp; apply sp_off3).
      iEval (rewrite -Hc3) in "Hs3". iEval (rewrite -Hc4) in "Hs4". iEval (rewrite -Hc5) in "Hs5".
      (* +0x2c/+0x2e/+0x30 c.sdsp s1/s2/s3 *)
      iPoseProof (spi_2c with "Htext") as "Hi2c".
      iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.sys_pause + 0x2c)) (mword_of_int 5 : mword 6)
                (mword_of_int 9 : mword 5) Qe (trap_res true + (av - 8))%nat w3 false with "Hcg Hpc Hi2c Hs3").
      iApply wp_next_off_intro. iIntros "Hcg Hpc Hs3".
      iEval (rgne) in "Hs3".
      assert (Hq2e : add_vec_int (mword_of_int (KernelSyms.sys_pause + 0x2c) : mword 64) 2 = mword_of_int (KernelSyms.sys_pause + 0x2e)) by pcstep.
      iEval (rewrite Hq2e) in "Hpc".
      iPoseProof (spi_2e with "Htext") as "Hi2e".
      iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.sys_pause + 0x2e)) (mword_of_int 4 : mword 6)
                (mword_of_int 18 : mword 5) Qe (trap_res true + (av - 8))%nat w4 false with "Hcg Hpc Hi2e Hs4").
      iApply wp_next_off_intro. iIntros "Hcg Hpc Hs4".
      iEval (rgne) in "Hs4".
      assert (Hq30 : add_vec_int (mword_of_int (KernelSyms.sys_pause + 0x2e) : mword 64) 2 = mword_of_int (KernelSyms.sys_pause + 0x30)) by pcstep.
      iEval (rewrite Hq30) in "Hpc".
      iPoseProof (spi_30 with "Htext") as "Hi30".
      iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.sys_pause + 0x30)) (mword_of_int 3 : mword 6)
                (mword_of_int 19 : mword 5) Qe (trap_res true + (av - 8))%nat w5 false with "Hcg Hpc Hi30 Hs5").
      iApply wp_next_off_intro. iIntros "Hcg Hpc Hs5".
      iEval (rgne) in "Hs5".
      assert (Hq32 : add_vec_int (mword_of_int (KernelSyms.sys_pause + 0x30) : mword 64) 2 = mword_of_int (KernelSyms.sys_pause + 0x32)) by pcstep.
      iEval (rewrite Hq32) in "Hpc".
      iEval (rewrite Hc3 Hqe9) in "Hs3".
      iEval (rewrite Hc4 Hqe18) in "Hs4".
      iEval (rewrite Hc5 Hqe19) in "Hs5".
      (* +0x32 auipc s3,0x8 *)
      iPoseProof (spi_32 with "Htext") as "Hi32".
      iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.sys_pause + 0x32)) (mword_of_int 19 : mword 5)
                (mword_of_int 0x8 : mword 20) Qe (trap_res true + (av - 8))%nat false
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi32").
      iApply wp_next_off_intro. iIntros "Hcg Hpc".
      set (P0 := <[Regidx (mword_of_int 19 : mword 5) := regval_into_reg
          (add_vec (mword_of_int (KernelSyms.sys_pause + 0x32) : mword 64) (auipc_off (mword_of_int 0x8 : mword 20)))]> Qe).
      change (<[Regidx (mword_of_int 19 : mword 5) := regval_into_reg
          (add_vec (mword_of_int (KernelSyms.sys_pause + 0x32) : mword 64) (auipc_off (mword_of_int 0x8 : mword 20)))]> Qe) with P0.
      assert (Hq36 : add_vec_int (mword_of_int (KernelSyms.sys_pause + 0x32) : mword 64) 4 = mword_of_int (KernelSyms.sys_pause + 0x36)) by pcstep.
      iEval (rewrite Hq36) in "Hpc".
      (* +0x36 lw s3,-1946(s3) : ticks0 := ticks *)
      iDestruct "HR" as (t0) "Hticks".
      assert (Hat0 : add_vec (rget P0 (mword_of_int 19 : mword 5))
                       (sign_extend' 64 (mword_of_int 0x8ae : mword 12)) = a_ticks).
      { rgne. rewrite /P0 upd_eq. rewrite /a_ticks. apply bv_eq; vm_compute; reflexivity. }
      iEval (rewrite -Hat0) in "Hticks".
      iPoseProof (spi_36 with "Htext") as "Hi36".
      iApply (wp_lw_s_sconf (mword_of_int (KernelSyms.sys_pause + 0x36)) (mword_of_int 19 : mword 5)
                (mword_of_int 19 : mword 5) (mword_of_int 0x8ae : mword 12) P0 (trap_res true + (av - 8))%nat t0 false
                (dqm := DfracOwn 1) ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi36 Hticks").
      iApply wp_next_off_intro. iIntros "Hcg Hpc Hticks".
      iEval (rewrite Hat0) in "Hticks".
      set (P1 := <[Regidx (mword_of_int 19 : mword 5) := regval_into_reg (sign_extend' 64 (t0 : mword 32))]> P0).
      change (<[Regidx (mword_of_int 19 : mword 5) := regval_into_reg (sign_extend' 64 (t0 : mword 32))]> P0) with P1.
      assert (Hq3a : add_vec_int (mword_of_int (KernelSyms.sys_pause + 0x36) : mword 64) 4 = mword_of_int (KernelSyms.sys_pause + 0x3a)) by pcstep.
      iEval (rewrite Hq3a) in "Hpc".
      iDestruct (ticks_res_intro t0 with "Hticks") as "HR".
      (* +0x3a auipc s2,0x15 *)
      iPoseProof (spi_3a with "Htext") as "Hi3a".
      iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.sys_pause + 0x3a)) (mword_of_int 18 : mword 5)
                (mword_of_int 0x8 : mword 20) P1 (trap_res true + (av - 8))%nat false
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi3a").
      iApply wp_next_off_intro. iIntros "Hcg Hpc".
      set (P2 := <[Regidx (mword_of_int 18 : mword 5) := regval_into_reg
          (add_vec (mword_of_int (KernelSyms.sys_pause + 0x3a) : mword 64) (auipc_off (mword_of_int 0x8 : mword 20)))]> P1).
      change (<[Regidx (mword_of_int 18 : mword 5) := regval_into_reg
          (add_vec (mword_of_int (KernelSyms.sys_pause + 0x3a) : mword 64) (auipc_off (mword_of_int 0x8 : mword 20)))]> P1) with P2.
      assert (Hq3e : add_vec_int (mword_of_int (KernelSyms.sys_pause + 0x3a) : mword 64) 4 = mword_of_int (KernelSyms.sys_pause + 0x3e)) by pcstep.
      iEval (rewrite Hq3e) in "Hpc".
      (* +0x3e addi s2,s2,1934 *)
      iPoseProof (spi_3e with "Htext") as "Hi3e".
      iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.sys_pause + 0x3e)) (mword_of_int 18 : mword 5)
                (mword_of_int 18 : mword 5) (mword_of_int 0x8a6 : mword 12) P2 (trap_res true + (av - 8))%nat false
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi3e").
      iApply wp_next_off_intro. iIntros "Hcg Hpc".
      iEval (rgne) in "Hcg".
      set (P3 := <[Regidx (mword_of_int 18 : mword 5) := regval_into_reg
          (add_vec (P2 !!! Regidx (mword_of_int 18 : mword 5)) (sign_extend' 64 (mword_of_int 2214 : mword 12)))]> P2).
      change (<[Regidx (mword_of_int 18 : mword 5) := regval_into_reg
          (add_vec (P2 !!! Regidx (mword_of_int 18 : mword 5)) (sign_extend' 64 (mword_of_int 2214 : mword 12)))]> P2) with P3.
      assert (Hq42 : add_vec_int (mword_of_int (KernelSyms.sys_pause + 0x3e) : mword 64) 4 = mword_of_int (KernelSyms.sys_pause + 0x42)) by pcstep.
      iEval (rewrite Hq42) in "Hpc".
      (* +0x42 auipc s1,0x8 *)
      iPoseProof (spi_42 with "Htext") as "Hi42".
      iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.sys_pause + 0x42)) (mword_of_int 9 : mword 5)
                (mword_of_int 0x15 : mword 20) P3 (trap_res true + (av - 8))%nat false
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi42").
      iApply wp_next_off_intro. iIntros "Hcg Hpc".
      set (P4 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg
          (add_vec (mword_of_int (KernelSyms.sys_pause + 0x42) : mword 64) (auipc_off (mword_of_int 0x15 : mword 20)))]> P3).
      change (<[Regidx (mword_of_int 9 : mword 5) := regval_into_reg
          (add_vec (mword_of_int (KernelSyms.sys_pause + 0x42) : mword 64) (auipc_off (mword_of_int 0x15 : mword 20)))]> P3) with P4.
      assert (Hq46 : add_vec_int (mword_of_int (KernelSyms.sys_pause + 0x42) : mword 64) 4 = mword_of_int (KernelSyms.sys_pause + 0x46)) by pcstep.
      iEval (rewrite Hq46) in "Hpc".
      (* +0x46 addi s1,s1,-1962 *)
      iPoseProof (spi_46 with "Htext") as "Hi46".
      iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.sys_pause + 0x46)) (mword_of_int 9 : mword 5)
                (mword_of_int 9 : mword 5) (mword_of_int 0x7ce : mword 12) P4 (trap_res true + (av - 8))%nat false
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi46").
      iApply wp_next_off_intro. iIntros "Hcg Hpc".
      iEval (rgne) in "Hcg".
      set (P5 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg
          (add_vec (P4 !!! Regidx (mword_of_int 9 : mword 5)) (sign_extend' 64 (mword_of_int 1998 : mword 12)))]> P4).
      change (<[Regidx (mword_of_int 9 : mword 5) := regval_into_reg
          (add_vec (P4 !!! Regidx (mword_of_int 9 : mword 5)) (sign_extend' 64 (mword_of_int 1998 : mword 12)))]> P4) with P5.
      assert (Hq4a : add_vec_int (mword_of_int (KernelSyms.sys_pause + 0x46) : mword 64) 4 = mword_of_int (KernelSyms.sys_pause + 0x4a)) by pcstep.
      iEval (rewrite Hq4a) in "Hpc".
      (* the loop's register shape *)
      assert (HP5thr : forall c : mword 5, c <> mword_of_int 9 -> c <> mword_of_int 18 ->
                c <> mword_of_int 19 -> P5 !!! Regidx c = Qe !!! Regidx c).
      { intros c N9 N18 N19.
        rewrite /P5 upd_ne; [| congruence]. rewrite /P4 upd_ne; [| congruence].
        rewrite /P3 upd_ne; [| congruence]. rewrite /P2 upd_ne; [| congruence].
        rewrite /P1 upd_ne; [| congruence]. rewrite /P0 upd_ne; [reflexivity | congruence]. }
      destruct HbQe as (HQe2 & HQe8 & HQehi).
      assert (HbP5 : sp_base m P5 sp0).
      { unfold sp_base. split; [| split].
        - rewrite (HP5thr csp_rs1 ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)). exact HQe2.
        - rewrite (HP5thr (mword_of_int 8 : mword 5) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)). exact HQe8.
        - unfold sp_hi in *. destruct HQehi as (H20&H21&H22&H23&H24&H25&H26&H27).
          split_and!.
          + rewrite (HP5thr (mword_of_int 20 : mword 5) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)). exact H20.
          + rewrite (HP5thr (mword_of_int 21 : mword 5) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)). exact H21.
          + rewrite (HP5thr (mword_of_int 22 : mword 5) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)). exact H22.
          + rewrite (HP5thr (mword_of_int 23 : mword 5) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)). exact H23.
          + rewrite (HP5thr (mword_of_int 24 : mword 5) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)). exact H24.
          + rewrite (HP5thr (mword_of_int 25 : mword 5) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)). exact H25.
          + rewrite (HP5thr (mword_of_int 26 : mword 5) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)). exact H26.
          + rewrite (HP5thr (mword_of_int 27 : mword 5) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)). exact H27. }
      assert (HlP5 : sp_lregs P5 (sign_extend' 64 (t0 : mword 32))).
      { unfold sp_lregs. split; [| split].
        - rewrite /P5 upd_eq. rewrite /P4 upd_eq. rewrite /a_tickslock. apply bv_eq; vm_compute; reflexivity.
        - rewrite /P5 upd_ne; [| reg_neq]. rewrite /P4 upd_ne; [| reg_neq].
          rewrite /P3 upd_eq. rewrite /P2 upd_eq. rewrite /a_ticks. apply bv_eq; vm_compute; reflexivity.
        - rewrite /P5 upd_ne; [| reg_neq]. rewrite /P4 upd_ne; [| reg_neq].
          rewrite /P3 upd_ne; [| reg_neq]. rewrite /P2 upd_ne; [| reg_neq].
          rewrite /P1. apply upd_eq. }

      (* ============ the killed (-1) exit at +0x8c, anchored ============ *)
      iAssert (sp_exitk CID0 γt j m av eb C sp0 pj (sign_extend' 64 (t0 : mword 32)) lks)
        with "[]" as "Hexitk".
      { rewrite /sp_exitk.
        iIntros (CIDx Hsx N) "%Hg Hy1 Hy2 Hy3 Hy4 Hy5 Hy6 Hy7 Hy8 Htok HR Hcg Hown Hpay Hpc Htl".
        destruct Hg as (Hbn & Hln).
        iApply (sp_exitk_body (CID := CIDx) CID0 γt j m N av eb C sp0 pj (sign_extend' 64 (t0 : mword 32)) lks
                  Hav Heb Hsx Hbn Hln Hfresh
                  with "Htext Hlkt Hy1 Hy2 Hy3 Hy4 Hy5 Hy6 Hy7 Hy8 Htok HR Hcg Hown Hpay Hpc Htl"). }

      (* ==================== the WAIT LOOP (iLöb) ==================== *)
      iAssert (sp_loop CID0 γt j m av eb C sp0 pj (sign_extend' 64 (t0 : mword 32)) nv lks)
        with "[]" as "Hloop".
      { iLöb as "IH". rewrite /sp_loop.
        iIntros (CIDy Hsy N) "%Hg Hy1 Hy2 Hy3 Hy4 Hy5 Hy6 Hy8 Hnc Hjoin7 Htok HR Hcg Hown Hpay Hpc Hex0 Hexk Htl".
        destruct Hg as (Hbn & Hln).
        iApply (sp_loop_body (CID := CIDy) CID0 γs γt γl j m N av eb C sp0 pj
                  (sign_extend' 64 (t0 : mword 32)) nv lks
                  Hav Heb Hj Hjl Hpjv Hsy Hbn Hln Hfresh
                  with "Htext Hlkt Hpinv Hpanic IH Hex0 Hexk Htl
                        Hy1 Hy2 Hy3 Hy4 Hy5 Hy6 Hy8 Hnc Hjoin7 Htok HR Hcg Hown Hpay Hpc"). }

      (* ============ the normal (return 0) exit at +0x70, anchored ============ *)
      iAssert (sp_exit0 CID0 γt j m av eb C sp0 pj lks) with "[]" as "Hexit0".
      { rewrite /sp_exit0.
        iIntros (CIDz Hsz N) "%Hg Hx1 Hx2 Hfree Hx7 Htok HR Hcg Hown Hpay Hpc Htl".
        destruct Hg as (Hbn & Hsn).
        iApply (sp_exit0_body (CID := CIDz) CID0 γt j m N av eb C sp0 pj lks
                  Hav Heb Hsz Hbn Hsn Hfresh
                  with "Htext Hlkt Hx1 Hx2 Hfree Hx7 Htok HR Hcg Hown Hpay Hpc Htl"). }

      (* enter the loop *)
      rewrite /sp_loop.
      iSpecialize ("Hloop" $! CIDa with "[%]"); [wp_next_chain|].
      iApply ("Hloop" $! P5 with "[%] Hs1 Hs2 Hs3 Hs4 Hs5 Hf6 Hf8 Hnc Hjoin7 Htok HR Hcg Hown Hpay Hpc Hexit0 Hexitk Htail").
      split; [exact HbP5 | exact HlP5].
  Qed.

End SpBodies.

(* ===================================================================== *)

Section ProofSysPause.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !irefslotG Σ, !fileG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Lemma wp_sys_pause_sconf  (γs : list gname)
      (j : nat) (γl : gname) (γt : gname) (m : regfile) (av : nat) (eb : bool)
      (C : iProp Σ) (i : nat) (tfp : mword 44) (ws : list (mword 64))
      (v : mword 64) (dqt : dfrac) (b : bool) (lks : gset nat)
    : wp_sys_pause_sconf_body γs j γl γt m av eb C i tfp ws v dqt b lks.
  Proof.
    cbv beta delta [wp_sys_pause_sconf_body].
    intros pcE pj ret_tgt Hj Hjl Hi0 Hws Hav Heb Hfresh.
    subst i.
    set (sp0 := (m !!! Regidx csp_rs1 : mword 64)).
    iIntros "Hcg Hown #Htext #Hdata Hpc Htf Hpage #Hlkt #Hpinv #Hpanic Hcont".
    (* LEVEL 0 WITH AN ENABLED BASE FORCES THE ENABLED INDEX: the [b = false]
       instance of this contract is vacuous, and pinning [b] here is what makes
       every crossing in the function speak the same index. *)
    iDestruct (cpu_own_eb_agree with "Hcg Hown") as %Hbm.
    assert (Hb : b = true) by (rewrite -Hbm; exact Heb).
    clear Hbm. subst b.
    assert (Hn0 : (Z.of_nat 0 + 1 < 2 ^ 31)%Z) by (vm_compute; reflexivity).
    assert (Hpjv : pj = proc_addr j) by reflexivity.
    assert (Hsp0v : sp0 = m !!! Regidx csp_rs1) by reflexivity.

    (* ============================ PROLOGUE ============================ *)
    iPoseProof (spi_00 with "Htext") as "Hi00".
    assert (Hspm : m !!! Regidx csp_rs1 = sp0) by reflexivity.
    assert (Hpush : add_vec (m !!! Regidx csp_rs1)
                      (sign_extend' 64 (caddi16sp_imm (mword_of_int 60 : mword 6)))
                    = pa_stk (m !!! Regidx csp_rs1) 8) by apply stk_push_64.
    iApply (wp_caddi16sp_push_s_sconf pcE (mword_of_int 60 : mword 6) m av 8 true
              ltac:(lia) Hpush with "Hcg Hpc Hi00").
    iIntros (CID1 Hs1) "Hcg Hframe Hpc".
    iEval (rewrite Hspm) in "Hframe".
    set (R1 := <[Regidx csp_rs1 := regval_into_reg
        (add_vec (m !!! Regidx csp_rs1)
           (sign_extend' 64 (caddi16sp_imm (mword_of_int 60 : mword 6))))]> m).
    change (<[Regidx csp_rs1 := regval_into_reg
        (add_vec (m !!! Regidx csp_rs1)
           (sign_extend' 64 (caddi16sp_imm (mword_of_int 60 : mword 6))))]> m) with R1.
    assert (HspR1 : R1 !!! Regidx csp_rs1 = pa_stk sp0 8)
      by (rewrite /R1 upd_eq; rewrite Hpush; reflexivity).
    assert (Hpc02 : add_vec_int (pcE : mword 64) 2 = mword_of_int (KernelSyms.sys_pause + 0x02)) by pcstep.
    iEval (rewrite Hpc02) in "Hpc".
    iEval (rewrite stack_own_slots; cbn [seq]) in "Hframe".
    iDestruct "Hframe" as "(S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & _)".
    iDestruct "S1" as (vw1) "Hs1". iDestruct "S2" as (vw2) "Hs2".
    iDestruct "S7" as (w7) "Hs7".
    iDestruct (word_pointsto_aligned_p with "Hs7") as %Hal7.
    iDestruct (word_pointsto_split4 with "Hs7") as "[Hs7lo Hs7hi]".
    iAssert (sp_join7 sp0) with "[Hs7lo]" as "Hjoin7".
    { rewrite /sp_join7. iIntros (nv) "Hhi". iExists _.
      iApply (word_pointsto_join4 _ _ _ _ Hal7 with "Hs7lo Hhi"). }
    (* +0x02 c.sdsp ra,56(sp) *)
    assert (Hb1 : add_vec (R1 !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 7 : mword 6) ('b"000"))) = pa_stk sp0 1)
      by (rewrite HspR1; apply sp_off7).
    assert (Hb2 : add_vec (R1 !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 6 : mword 6) ('b"000"))) = pa_stk sp0 2)
      by (rewrite HspR1; apply sp_off6).
    iEval (rewrite -Hb1) in "Hs1". iEval (rewrite -Hb2) in "Hs2".
    iPoseProof (spi_02 with "Htext") as "Hi02".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.sys_pause + 0x02))
              (mword_of_int 7 : mword 6) (mword_of_int 1 : mword 5) R1 (av - 8)%nat vw1 true
              with "Hcg Hpc Hi02 Hs1").
    iIntros (CID2 Hs2) "Hcg Hpc Hs1".
    iEval (rgne) in "Hs1".
    assert (Hpc04 : add_vec_int (mword_of_int (KernelSyms.sys_pause + 0x02) : mword 64) 2
                    = mword_of_int (KernelSyms.sys_pause + 0x04)) by pcstep.
    iEval (rewrite Hpc04) in "Hpc".
    (* +0x04 c.sdsp s0,48(sp) *)
    iPoseProof (spi_04 with "Htext") as "Hi04".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.sys_pause + 0x04))
              (mword_of_int 6 : mword 6) (mword_of_int 8 : mword 5) R1 (av - 8)%nat vw2 true
              with "Hcg Hpc Hi04 Hs2").
    iIntros (CID3 Hs3) "Hcg Hpc Hs2".
    iEval (rgne) in "Hs2".
    assert (Hpc06 : add_vec_int (mword_of_int (KernelSyms.sys_pause + 0x04) : mword 64) 2
                    = mword_of_int (KernelSyms.sys_pause + 0x06)) by pcstep.
    iEval (rewrite Hpc06) in "Hpc".
    (* the two cells now hold m's ra / s0; re-anchor them at [pa_stk sp0 k] *)
    assert (HR1ra : R1 !!! Regidx (mword_of_int 1 : mword 5) = m !!! Regidx (mword_of_int 1 : mword 5))
      by (rewrite /R1 upd_ne; [reflexivity | reg_neq]).
    assert (HR1s0 : R1 !!! Regidx (mword_of_int 8 : mword 5) = m !!! Regidx (mword_of_int 8 : mword 5))
      by (rewrite /R1 upd_ne; [reflexivity | reg_neq]).
    iEval (rewrite Hb1 HR1ra) in "Hs1".
    iEval (rewrite Hb2 HR1s0) in "Hs2".
    (* +0x06 c.addi4spn s0,sp,64 *)
    iPoseProof (spi_06 with "Htext") as "Hi06".
    iApply (wp_caddi4spn_s_sconf (mword_of_int (KernelSyms.sys_pause + 0x06))
              (Cregidx (mword_of_int 0)) (mword_of_int 16 : mword 8) (mword_of_int 8 : mword 5)
              R1 (av - 8)%nat true ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
              ltac:(rdok) with "Hcg Hpc Hi06").
    iIntros (CID4 Hs4) "Hcg Hpc".
    set (R2 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg
        (add_vec (R1 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 16 : mword 8))))]> R1).
    change (<[Regidx (mword_of_int 8 : mword 5) := regval_into_reg
        (add_vec (R1 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 16 : mword 8))))]> R1) with R2.
    assert (Hpc08 : add_vec_int (mword_of_int (KernelSyms.sys_pause + 0x06) : mword 64) 2
                    = mword_of_int (KernelSyms.sys_pause + 0x08)) by pcstep.
    iEval (rewrite Hpc08) in "Hpc".
    assert (HR2s0 : R2 !!! Regidx (mword_of_int 8 : mword 5) = sp0)
      by (rewrite /R2 upd_eq HspR1; apply stk_fp_64).
    assert (HR2sp : R2 !!! Regidx csp_rs1 = pa_stk sp0 8)
      by (rewrite /R2 upd_ne; [exact HspR1 | reg_neq]).
    (* +0x08 addi a1,s0,-52 : a1 := &n *)
    iPoseProof (spi_08 with "Htext") as "Hi08".
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.sys_pause + 0x08))
              (mword_of_int 11 : mword 5) (mword_of_int 8 : mword 5) (mword_of_int 0xfcc : mword 12)
              R2 (av - 8)%nat true ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi08").
    iIntros (CID5 Hs5) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (R3 := <[Regidx (mword_of_int 11 : mword 5) := regval_into_reg
        (add_vec (R2 !!! Regidx (mword_of_int 8 : mword 5)) (sign_extend' 64 (mword_of_int 0xfcc : mword 12)))]> R2).
    change (<[Regidx (mword_of_int 11 : mword 5) := regval_into_reg
        (add_vec (R2 !!! Regidx (mword_of_int 8 : mword 5)) (sign_extend' 64 (mword_of_int 0xfcc : mword 12)))]> R2) with R3.
    assert (Hpc0c : add_vec_int (mword_of_int (KernelSyms.sys_pause + 0x08) : mword 64) 4
                    = mword_of_int (KernelSyms.sys_pause + 0x0c)) by pcstep.
    iEval (rewrite Hpc0c) in "Hpc".
    assert (HR3a1 : R3 !!! Regidx (mword_of_int 11 : mword 5) = pa_add (pa_stk sp0 7) 4)
      by (rewrite /R3 upd_eq HR2s0; apply sp_addr_n).
    (* +0x0c c.li a0,0 *)
    iPoseProof (spi_0c with "Htext") as "Hi0c".
    iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.sys_pause + 0x0c))
              (mword_of_int 10 : mword 5) (mword_of_int 0 : mword 6)
              (mword_of_int (Z.of_nat 0) : mword 64) R3 (av - 8)%nat true
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(apply bv_eq; vm_compute; reflexivity) with "Hcg Hpc Hi0c").
    iIntros (CID6 Hs6) "Hcg Hpc".
    set (R4 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg (mword_of_int (Z.of_nat 0) : mword 64)]> R3).
    change (<[Regidx (mword_of_int 10 : mword 5) := regval_into_reg (mword_of_int (Z.of_nat 0) : mword 64)]> R3) with R4.
    assert (Hpc0e : add_vec_int (mword_of_int (KernelSyms.sys_pause + 0x0c) : mword 64) 2
                    = mword_of_int (KernelSyms.sys_pause + 0x0e)) by pcstep.
    iEval (rewrite Hpc0e) in "Hpc".
    (* +0x0e jal ra,argint *)
    iPoseProof (spi_0e with "Htext") as "Hi0e".
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.sys_pause + 0x0e))
              (mword_of_int 1 : mword 5) (mword_of_int 2096710 : mword 21) R4 (av - 8)%nat true
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi0e").
    iIntros (CID7 Hs7) "Hcg Hpc".
    set (R5 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg
        (add_vec_int (mword_of_int (KernelSyms.sys_pause + 0x0e) : mword 64) 4)]> R4).
    change (<[Regidx (mword_of_int 1 : mword 5) := regval_into_reg
        (add_vec_int (mword_of_int (KernelSyms.sys_pause + 0x0e) : mword 64) 4)]> R4) with R5.
    assert (Hjai : add_vec (mword_of_int (KernelSyms.sys_pause + 0x0e) : mword 64)
                     (sign_extend' 64 (mword_of_int 2096710 : mword 21)) = mword_of_int KernelSyms.argint)
      by pcstep.
    iEval (rewrite Hjai) in "Hpc".
    (* argint's entry facts *)
    assert (HR5ra : R5 !!! Regidx (mword_of_int 1 : mword 5)
                    = add_vec_int (mword_of_int (KernelSyms.sys_pause + 0x0e) : mword 64) 4)
      by (rewrite /R5; apply upd_eq).
    assert (HR5a0 : R5 !!! Regidx (mword_of_int 10 : mword 5) = mword_of_int (Z.of_nat 0)).
    { rewrite /R5 upd_ne; [| reg_neq]. rewrite /R4 upd_eq. reflexivity. }
    assert (HR5a1 : R5 !!! Regidx (mword_of_int 11 : mword 5) = pa_add (pa_stk sp0 7) 4).
    { rewrite /R5 upd_ne; [| reg_neq]. rewrite /R4 upd_ne; [| reg_neq]. exact HR3a1. }
    assert (HR5s0 : R5 !!! Regidx (mword_of_int 8 : mword 5) = sp0).
    { rewrite /R5 upd_ne; [| reg_neq]. rewrite /R4 upd_ne; [| reg_neq].
      rewrite /R3 upd_ne; [| reg_neq]. exact HR2s0. }
    assert (HR5sp : R5 !!! Regidx csp_rs1 = pa_stk sp0 8).
    { rewrite /R5 upd_ne; [| reg_neq]. rewrite /R4 upd_ne; [| reg_neq].
      rewrite /R3 upd_ne; [| reg_neq]. exact HR2sp. }
    (* the prologue writes only sp/s0/a0/a1/ra, so s1..s11 all thread *)
    assert (Hpro : forall c : mword 5,
              c <> csp_rs1 -> c <> mword_of_int 8 -> c <> mword_of_int 10 ->
              c <> mword_of_int 11 -> c <> mword_of_int 1 ->
              R5 !!! Regidx c = m !!! Regidx c).
    { intros c N2 N8 N10 N11 N1.
      rewrite /R5 upd_ne; [| congruence]. rewrite /R4 upd_ne; [| congruence].
      rewrite /R3 upd_ne; [| congruence]. rewrite /R2 upd_ne; [| congruence].
      rewrite /R1 upd_ne; [reflexivity | congruence]. }
    assert (HbaseR5 : sp_base m R5 sp0).
    { unfold sp_base, sp_hi. split_and!; try (apply Hpro; reg_neq).
      - exact HR5sp. - exact HR5s0. }
    assert (HsavR5 : sp_saved m R5).
    { unfold sp_saved. split_and!; apply Hpro; reg_neq. }
    (* ======================= argint(0, &n) ======================= *)
    iEval (rewrite -HR5a1) in "Hs7hi".
    iDestruct (cpu_own_transport CID CID7 0 eb pj C true ltac:(wp_next_chain)
                 with "Hown") as "Hown".
    iApply (Argint.wp_argint_sconf R5 (av - 8)%nat 0%nat eb pj C
              0%nat tfp ws v (word_hi w7) dqt true lks
              ltac:(unfold NARG; lia) HR5a0 Hws Hn0 ltac:(lia)
              with "Hcg Hown Htext Hdata Hpc Htf Hpage Hs7hi").
    iIntros (CID8 Hs8 A) "%HcsA Hcg Hown Hpc Htf Hpage Hs7hi".
    iEval (rewrite HR5a1) in "Hs7hi".
    assert (Hpc12 : ret_pc (R5 !!! Regidx (mword_of_int 1 : mword 5))
                    = mword_of_int (KernelSyms.sys_pause + 0x12)) by (rewrite HR5ra; pcstep).
    iEval (rewrite Hpc12) in "Hpc".
    assert (HbaseA : sp_base m A sp0) by exact (sp_base_cs m R5 A sp0 HcsA HbaseR5).
    assert (HsavA : sp_saved m A) by exact (sp_saved_cs m R5 A HcsA HsavR5).
    pose proof HbaseA as HbaseA'. destruct HbaseA' as (HAsp & HAs0 & HAhi).
    (* +0x12 lw a5,-52(s0) *)
    assert (Haddrn : add_vec (rget A (mword_of_int 8 : mword 5))
                       (sign_extend' 64 (mword_of_int 0xfcc : mword 12)) = pa_add (pa_stk sp0 7) 4).
    { rgne. rewrite HAs0. apply sp_addr_n. }
    iEval (rewrite -Haddrn) in "Hs7hi".
    iPoseProof (spi_12 with "Htext") as "Hi12".
    iApply (wp_lw_s_sconf (mword_of_int (KernelSyms.sys_pause + 0x12))
              (mword_of_int 15 : mword 5) (mword_of_int 8 : mword 5) (mword_of_int 0xfcc : mword 12)
              A (av - 8)%nat (arg_int32 v) true (dqm := DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi12 Hs7hi").
    iIntros (CID9 Hs9) "Hcg Hpc Hs7hi".
    iEval (rewrite Haddrn) in "Hs7hi".
    set (A1 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (sign_extend' 64 (arg_int32 v))]> A).
    change (<[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (sign_extend' 64 (arg_int32 v))]> A) with A1.
    assert (Hpc16 : add_vec_int (mword_of_int (KernelSyms.sys_pause + 0x12) : mword 64) 4
                    = mword_of_int (KernelSyms.sys_pause + 0x16)) by pcstep.
    iEval (rewrite Hpc16) in "Hpc".
    assert (HcsAA1 : callee_saved A A1).
    { rewrite /A1. apply callee_saved_insert_r; [vm_compute; reflexivity|]. apply callee_saved_refl. }
    assert (HbaseA1 : sp_base m A1 sp0) by exact (sp_base_cs m A A1 sp0 HcsAA1 HbaseA).
    assert (HsavA1 : sp_saved m A1) by exact (sp_saved_cs m A A1 HcsAA1 HsavA).
    assert (HA1s0 : A1 !!! Regidx (mword_of_int 8 : mword 5) = sp0)
      by (destruct HbaseA1 as (_&X&_); exact X).

    (* ================ the shared epilogue continuation ================ *)
    iAssert (sp_tail CID j m av eb C sp0 pj lks) with "[Hcont Htf Hpage]" as "Htail".
    { rewrite /sp_tail.
      iIntros (CIDt Hst M r) "%Hfacts Hx1 Hx2 Hfree Hx7 Hcg Hown Hpc".
      destruct Hfacts as (Hbase & Hsav & Hra0 & Hrv).
      iApply (sp_tail_body (CID := CIDt) CID j m M r av eb C sp0 pj tfp ws dqt lks
                Hav Hst Hbase Hsav Hra0 Hrv Hsp0v
                with "Htext Hx1 Hx2 Hfree Hx7 Hcg Hown Htf Hpage Hpc Hcont"). }

    (* ===================== the acquire continuation ===================== *)
    iAssert (sp_acq CID γt j m av eb C sp0 pj lks) with "[]" as "Hacq".
    { rewrite /sp_acq.
      iIntros (CIDq Hsq M nv) "%Hf Hx1 Hx2 Hfree Hnc Hjoin7 Hcg Hown Hpc Htl".
      destruct Hf as (Hbb & Hss).
      iApply (sp_acq_body (CID := CIDq) CID γs γt γl j m M nv av eb C sp0 pj lks
                Hav Heb Hj Hjl Hpjv Hsq Hbb Hss Hfresh
                with "Htext Hlkt Hpinv Hpanic Hx1 Hx2 Hfree Hnc Hjoin7 Hcg Hown Hpc Htl"). }

    (* ====================== the [n < 0] dispatch ====================== *)
    iPoseProof (spi_16 with "Htext") as "Hi16".
    assert (HA1a5 : A1 !!! Regidx (mword_of_int 15 : mword 5) = sign_extend' 64 (arg_int32 v))
      by (rewrite /A1; apply upd_eq).
    destruct (zopz0zI_s (A1 !!! Regidx (mword_of_int 15 : mword 5)) (zero_reg : mword 64)) eqn:Hneg.
    - (* n < 0: branch TAKEN to the +0x86 fixup *)
      iApply (wp_blt_x0_taken_s_sconf (mword_of_int (KernelSyms.sys_pause + 0x16))
                (mword_of_int 128 : mword 13) (mword_of_int 15 : mword 5) A1 (av - 8)%nat true
                ltac:(vm_compute; discriminate) ltac:(rgne; exact Hneg) ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi16").
      iApply bi.later_intro. iIntros (CID10 Hs10) "Hcg Hpc".
      assert (Htgt86 : add_vec (mword_of_int (KernelSyms.sys_pause + 0x16) : mword 64)
                         (sign_extend' 64 (mword_of_int 128 : mword 13))
                       = mword_of_int (KernelSyms.sys_pause + 0x96)) by pcstep.
      iEval (rewrite Htgt86) in "Hpc".
      (* +0x86 sw zero,-52(s0) : n = 0 *)
      assert (Haddrn1 : add_vec (rget A1 (mword_of_int 8 : mword 5))
                          (sign_extend' 64 (mword_of_int 0xfcc : mword 12)) = pa_add (pa_stk sp0 7) 4).
      { rgne. rewrite HA1s0. apply sp_addr_n. }
      iEval (rewrite -Haddrn1) in "Hs7hi".
      iPoseProof (spi_96 with "Htext") as "Hi86".
      iApply (wp_sw_zero_s_sconf (mword_of_int (KernelSyms.sys_pause + 0x96))
                (mword_of_int 8 : mword 5) (mword_of_int 0xfcc : mword 12) A1 (av - 8)%nat
                (arg_int32 v) true with "Hcg Hpc Hi86 Hs7hi").
      iIntros (CID11 Hs11) "Hcg Hpc Hs7hi".
      iEval (rewrite Haddrn1) in "Hs7hi".
      assert (Hp8a : add_vec_int (mword_of_int (KernelSyms.sys_pause + 0x96) : mword 64) 4
                     = mword_of_int (KernelSyms.sys_pause + 0x9a)) by pcstep.
      iEval (rewrite Hp8a) in "Hpc".
      (* +0x8a c.j back to +0x1a *)
      iPoseProof (spi_9a with "Htext") as "Hi8a".
      iApply (wp_cj_s_sconf (mword_of_int (KernelSyms.sys_pause + 0x9a))
                (sign_extend' 21 (concat_vec (mword_of_int 1984 : mword 11) ('b"0")))
                A1 (av - 8)%nat true ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi8a").
      iIntros (CID12 Hs12). iApply bi.later_intro. iIntros "Hcg Hpc".
      assert (Htgt1a : add_vec (mword_of_int (KernelSyms.sys_pause + 0x9a) : mword 64)
                         (sign_extend' 64 (sign_extend' 21 (concat_vec (mword_of_int 1984 : mword 11) ('b"0"))))
                       = mword_of_int (KernelSyms.sys_pause + 0x1a)) by pcstep.
      iEval (rewrite Htgt1a) in "Hpc".
      iDestruct (cpu_own_transport CID8 CID12 0 eb pj C true ltac:(wp_next_chain)
                   with "Hown") as "Hown".
      rewrite /sp_acq.
      iSpecialize ("Hacq" $! CID12 with "[%]"); [wp_next_chain|].
      iApply ("Hacq" $! A1 (mword_of_int 0 : mword 32)
                with "[%] Hs1 Hs2 [S3 S4 S5 S6 S8] Hs7hi Hjoin7 Hcg Hown Hpc Htail").
      { split; [exact HbaseA1 | exact HsavA1]. }
      { rewrite /sp_free. iFrame "S3 S4 S5 S6 S8". }
    - (* n >= 0: fall through to +0x1a *)
      iApply (wp_blt_x0_fall_s_sconf (mword_of_int (KernelSyms.sys_pause + 0x16))
                (mword_of_int 128 : mword 13) (mword_of_int 15 : mword 5) A1 (av - 8)%nat true
                ltac:(vm_compute; discriminate) ltac:(rgne; exact Hneg)
                with "Hcg Hpc Hi16").
      iIntros (CID10 Hs10) "Hcg Hpc".
      assert (Hp1a : add_vec_int (mword_of_int (KernelSyms.sys_pause + 0x16) : mword 64) 4
                     = mword_of_int (KernelSyms.sys_pause + 0x1a)) by pcstep.
      iEval (rewrite Hp1a) in "Hpc".
      iDestruct (cpu_own_transport CID8 CID10 0 eb pj C true ltac:(wp_next_chain)
                   with "Hown") as "Hown".
      rewrite /sp_acq.
      iSpecialize ("Hacq" $! CID10 with "[%]"); [wp_next_chain|].
      iApply ("Hacq" $! A1 (arg_int32 v)
                with "[%] Hs1 Hs2 [S3 S4 S5 S6 S8] Hs7hi Hjoin7 Hcg Hown Hpc Htail").
      { split; [exact HbaseA1 | exact HsavA1]. }
      { rewrite /sp_free. iFrame "S3 S4 S5 S6 S8". }
  Qed.

End ProofSysPause.

End SysPauseProof.
