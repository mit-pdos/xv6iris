(* ProofSysPipe.v -- the whole-function WP for sys_pipe(), over the
   SIE-agnostic sconf world.

     myproc() -> argaddr(0,&fdarray) -> pipealloc(&rf,&wf)
       -> fdalloc(rf) -> fdalloc(wf)
       -> copyout(&fd0) -> copyout(&fd1) -> return 0
     bad: null whichever descriptors were installed, fileclose both, return -1

   Seventy-three instructions (KernelInstrs @ 0x80005420; the listing is in
   CodeSysPipe.v).  Four things carry the proof.

   THE psz BUMP (xv6 0024d4b).  copyout gained a [psz] argument in a1, so
   each of the two calls loads [p->sz] into a1 ([c.ld a1,72(s1)]) alongside
   the [p->pagetable] it already loaded into a0, and every later argument
   moved down a register (dstva a1->a2, src a2->a3, len a3->a4).  The
   contract no longer takes the [p_sz] / [p_pagetable] cells at all, so the
   [proc_priv_copy] accessor's two cells are read HERE and stay with the
   caller across both calls.  One further consequence in the failure tail:
   gcc now lands the second [add] in s1 rather than a5 (s1 is dead there),
   which is why [sp_ofile_null] is indexed by its destination register.

   * THE FRAME IS THE STATE.  Like pipealloc, every branch after a call
     re-reads a stack local rather than a register: the [blt] at +0x3c tests
     what the [sw] at +0x38 just stored, and the [lw] at +0xb4 re-reads [fd0]
     after the second fdalloc has clobbered a0.  So the proof carries the
     eight frame slots as points-tos and reads the branch conditions off
     them.  The two [int]s share ONE slot -- [fd1] in its low word, [fd0] in
     its high word -- so slot 8 spends most of the function split by
     [InstrBytes.word_pointsto_split4] and is only rejoined for the epilogue.

   * TWO BLOCKS APPEAR TWICE, so each is ONE lemma parameterized by its entry
     offset [a] and given its own [instr] facts and pc-successor equations:
       - [sp_ofile_null]: [slli/addi/add/sd], the four instructions that
         turn an [int fd] in a5 into [&p->ofile[fd]] and store 0 there
         (+0x84, +0x94, +0xbc), indexed by which of a5/s1 the [add] lands
         in -- gcc picks s1 at +0x94;
       - [sp_close2 a]: [ld/jal/ld/jal/c.li], "close both files and load the
         -1 return" (+0xa0 and +0xc8 -- gcc emitted it twice).
     Both are stated over a SYMBOLIC descriptor index, the argraw lesson:
     casing on the sixteen possible fds would be sixteen times the work.

   * FOUR EXITS, ONE EPILOGUE.  Everything reaches +0xda with the return
     value already in a5, so the epilogue is an [iAssert]ed continuation
     ([Hepi]) built before the first branch; it owns the three saved slots
     and the caller's [Hcont], and each arm hands it a5 and the matching
     [sys_pipe_post] disjunct.

   * THE fd UNITS BALANCE, and that is the real content (see SpecSysPipe.v's
     header for the table).  The two the caller supplies go to pipealloc; on
     the way back each fdalloc returns one as its descriptor fills, each
     re-null of a descriptor spends one, and each fileclose returns one.
     Every exit hands back exactly two.

   EXPLICIT-CPUID.  sys_pipe is [b]-GENERIC start to finish (its contract
   threads the caller's [b]), so every plain instruction crosses to a fresh
   hart and each leaf's continuation is introduced as [iIntros (CIDk Hcrk)].
   Three consequences shape the script:

   * THE THREE BLOCK LEMMAS ([sp_ofile_null], [sp_close2], [sp_epi]) and the
     unused-but-kept [sp_sp_bounds] each take their OWN `{CID0 : CpuId}
     binder and wrap their continuation in [wp_next b], closing it with
     [iSpecialize ("Hcont" $! CIDn with "[%]"); [wp_next_chain|]].  They are
     applied with the hart PINNED ([sp_close2 (CID0 := CID43) ...]): the
     binder is instance-implicit, so typeclass resolution would otherwise
     pick whichever [CpuId] is topmost rather than the chain's current hart.

   * THE TWO iASSERTED CONTINUATIONS, [EPI] (the shared epilogue) and [T7C]
     (the copyout-failure tail), are likewise [wp_next b (fun CID => ...)]
     rather than bare wands.  They are entered from four / two different
     harts, and [wp_next]'s conditional equality is exactly the premise that
     lets each entry re-anchor them -- a hart-quantified continuation without
     it would be unprovable, since nothing relates an arbitrary hart to the
     one [Hcont] is anchored at.

   * ["Hcpu"] ([cpu_own]) is re-anchored with [CpuOwn.cpu_own_transport] at
     NINETEEN points: before each cross-function call (myproc, argaddr,
     pipealloc, two fdallocs, two copyouts, and the four fileclose calls
     inside [sp_close2]'s three instantiations), and at every place a
     continuation ([Hepi] / [Ht7c] / [Hcont]) is applied.  None of the plain
     ALU/mem/branch leaves touch it, so it never rides a crossing implicitly.

   Every [tp]-slot premise and every [m !!! Regidx Rtp = cid_word] fact is
   gone: [HartTp] pins tp to the hart, so the callees no longer ask.  The
   leaves' value premises now read [rget m k], which is why the register-map
   chain, the frame-address [assert]s and the stored-value rewrites all carry
   an [rgne] ([IntrDefs]) to get back to the [!!! Regidx] spelling the pure
   arithmetic lemmas are stated in. *)
From Stdlib Require Import Eqdep_dec ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import excl auth gmap frac numbers.
From iris.base_logic.lib Require Import ghost_var gen_heap invariants.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes.
Require Import RiscvLang RiscvPtsto RiscvExtras.
Require Import RegFile.
Require Import InstrBytes.
Require Import WpMmodeLeafBase.
Require Import SmodeCore.
Require Import StackOwn.
Require Import CalleeSaved.
Require Import KernelText.
Require Import KernelRvcDecode.
Require Import VcGen.
Require Import WpSconfAlu WpSconfMem WpSconfBtype WpSconfCtl WpSmodeIntr.
Require Import IntrDefs WpLock.
Require Import HartTp WpNext.
Require Import ProcGeom CpuOwn.
Require Import KallocInv.
Require Import KvmSpec.
Require Import UserPtTree.
Require Import ProcPtOwn.
Require Import FdSlots FileInv ProcInv.
Require Import PanicStub.
Require Import WpUart.
Require Import DiskPtsto.
Require Import BioInv.
Require Import FsBlocks LogInv.
Require Import FsCrash.
Require Import SpecIput.
Require Import SpecMyproc SpecArgaddr SpecPipealloc SpecFdalloc SpecFileclose SpecCopyout.
Require Import IrefSlots InodeRegion.
Require Import SpecSysPipe.
Require Import CodeSysPipe.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Import Defs.
Local Open Scope Z_scope.


(* A failing tactic inside a whole-function WP prints the WHOLE goal, and
   this one contains [ProcInv.tf_page]'s 4096-conjunct big-op: an unbounded
   printer turns a one-line mistake into an apparent hang.  Bound it. *)
Set Printing Depth 40.

(* ===================================================================== *)
(*  Pure arithmetic: the frame and the five local addresses.              *)
(* ===================================================================== *)



(* ...and +0x08 [c.addi4spn s0,sp,64] takes it straight back: s0 IS the
   entry sp, which is what every [imm(s0)] local address is relative to. *)

(* the five [imm(s0)] locals, in slot terms *)
Lemma sp_addr_fdarray (X : mword 64) :          (* -40 : uint64 fdarray *)
  add_vec X (sign_extend' 64 (mword_of_int 0xfd8 : mword 12)) = pa_stk X 5.
Proof.
  unfold pa_stk, add_vec_int. apply f_equal. apply bv_eq; vm_compute; reflexivity.
Qed.

Lemma sp_addr_rf (X : mword 64) :               (* -48 : struct file *rf *)
  add_vec X (sign_extend' 64 (mword_of_int 0xfd0 : mword 12)) = pa_stk X 6.
Proof.
  unfold pa_stk, add_vec_int. apply f_equal. apply bv_eq; vm_compute; reflexivity.
Qed.

Lemma sp_addr_wf (X : mword 64) :               (* -56 : struct file *wf *)
  add_vec X (sign_extend' 64 (mword_of_int 0xfc8 : mword 12)) = pa_stk X 7.
Proof.
  unfold pa_stk, add_vec_int. apply f_equal. apply bv_eq; vm_compute; reflexivity.
Qed.

Lemma sp_addr_fd1 (X : mword 64) :              (* -64 : int fd1, LOW word *)
  add_vec X (sign_extend' 64 (mword_of_int 0xfc0 : mword 12)) = pa_stk X 8.
Proof.
  unfold pa_stk, add_vec_int. apply f_equal. apply bv_eq; vm_compute; reflexivity.
Qed.

Lemma sp_addr_fd0 (X : mword 64) :              (* -60 : int fd0, HIGH word *)
  add_vec X (sign_extend' 64 (mword_of_int 0xfc4 : mword 12)) = pa_add (pa_stk X 8) 4.
Proof.
  unfold pa_add, pa_stk. rewrite avi_assoc.
  unfold add_vec_int. apply f_equal. apply bv_eq; vm_compute; reflexivity.
Qed.

(* ...both also as an offset from the frame BASE, the form the "this
   out-parameter is not null" argument needs ([StackOwn.stack_off_nonzero] is
   anchored at sp). *)
Lemma sp_addr_fd0_base (X : mword 64) :
  pa_add (pa_stk X 8) 4 = add_vec_int (pa_stk X 8) 4.
Proof. reflexivity. Qed.


(* the three [c.sdsp]/[c.ldsp] displacements off the pushed sp *)
Lemma sp_frm1 (X : mword 64) :          (* 56(sp) : saved ra *)
  add_vec (pa_stk X 8) (zero_extend' 64 (concat_vec (mword_of_int 7 : mword 6) ('b"000")))
  = pa_stk X 1.
Proof.
  unfold pa_stk, add_vec_int. rewrite add_vec_off2.
  apply f_equal. apply bv_eq; vm_compute; reflexivity.
Qed.

Lemma sp_frm2 (X : mword 64) :          (* 48(sp) : saved s0 *)
  add_vec (pa_stk X 8) (zero_extend' 64 (concat_vec (mword_of_int 6 : mword 6) ('b"000")))
  = pa_stk X 2.
Proof.
  unfold pa_stk, add_vec_int. rewrite add_vec_off2.
  apply f_equal. apply bv_eq; vm_compute; reflexivity.
Qed.

Lemma sp_frm3 (X : mword 64) :          (* 40(sp) : saved s1 *)
  add_vec (pa_stk X 8) (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000")))
  = pa_stk X 3.
Proof.
  unfold pa_stk, add_vec_int. rewrite add_vec_off2.
  apply f_equal. apply bv_eq; vm_compute; reflexivity.
Qed.

(* [c.add a5,a5,s1] computes [8*fd + 208 + p] while [ProcGeom.p_ofile] is
   spelled [p + (208 + 8*fd)] -- the one place the operand order matters. *)

(* sys_pipe runs at [n = 0], so push_off's transient increment premise is
   this closed fact rather than a hypothesis threaded from the caller. *)
Lemma sp_noff0 : (Z.of_nat 0 + 1 < 2 ^ 31)%Z.
Proof.
  assert (H : (2 ^ 31 = 2147483648)%Z) by (vm_compute; reflexivity).
  rewrite H. lia.
Qed.

(* ===================================================================== *)
(*  The [int fd] round trip, over a SYMBOLIC descriptor index.            *)
(* ===================================================================== *)
(* Both descriptors are written by an [sw] and read back by an [lw], and
   both branches then test the result against zero.  Casing on the sixteen
   possible fds would be sixteen times the work (the argraw lesson), so the
   two facts are proved once over an arbitrary in-range [z]. *)

(* [sw] then [lw] is the identity on a non-negative [int]. *)
Lemma sp_sext_trunc (z : Z) : (0 <= z < 2 ^ 31)%Z ->
  sign_extend' 64 (trunc32 (mword_of_int z : mword 64)) = (mword_of_int z : mword 64).
Proof.
  intro Hz. rewrite trunc32_mword_of_int.
  apply bv_eq. rewrite (sext64_moi32_unsigned z Hz).
  rewrite moi64_unsigned. symmetry. apply bvw64_small.
  assert (E31 : (2 ^ 31 = 2147483648)%Z) by (vm_compute; reflexivity).
  assert (E64 : (2 ^ 64 = 18446744073709551616)%Z) by (vm_compute; reflexivity).
  lia.
Qed.

(* ...and such a value is signed non-negative, so every [blt aN,x0] over a
   descriptor index falls through. *)
Lemma sp_sint_moi (z : Z) : (0 <= z < 2 ^ 31)%Z -> sint (mword_of_int z : mword 64) = z.
Proof.
  intro Hz.
  assert (E31 : (2 ^ 31 = 2147483648)%Z) by (vm_compute; reflexivity).
  assert (E64 : (2 ^ 64 = 18446744073709551616)%Z) by (vm_compute; reflexivity).
  change (sint ?x) with (bv_swrap 64 (bv_unsigned x)).
  rewrite moi64_unsigned. rewrite bvw64_small; [| lia].
  apply bv_swrap_small.
  assert (Hhm : bv_half_modulus 64 = (2 ^ 63)%Z) by reflexivity. rewrite Hhm.
  assert (E63 : (2 ^ 63 = 9223372036854775808)%Z) by (vm_compute; reflexivity).
  lia.
Qed.

Lemma sp_fd_nonneg (z : Z) : (0 <= z < 2 ^ 31)%Z ->
  zopz0zI_s (mword_of_int z : mword 64) (zero_reg : mword 64) = false.
Proof.
  intro Hz. unfold zopz0zI_s. apply Z.ltb_ge.
  assert (Hz0 : sint (zero_reg : mword 64) = 0%Z) by reflexivity. rewrite Hz0.
  rewrite (sp_sint_moi z Hz). lia.
Qed.

(* ===================================================================== *)
(*  EVERY numeric side condition, proved HERE.                            *)
(* ===================================================================== *)
(* [lia] is unreliable once a bitvector is anywhere in the goal OR the
   context (durable-notes.md: [bitvector.tactics] installs a zify hook that
   makes it fail -- or search forever -- on goals it would otherwise close in
   a step).  Every arithmetic obligation of this file is therefore packaged
   as a closed lemma over plain [Z]/[nat] and applied as a fact. *)
Lemma sp_bounds (av : nat) : (sys_pipe_stack <= av)%nat ->
  (8 <= av)%nat /\ (10 <= av - 8)%nat /\ (74 <= av - 8)%nat /\ (52 <= av - 8)%nat /\
  (argaddr_stack <= av - 8)%nat /\ (fdalloc_stack <= av - 8)%nat /\
  (fileclose_stack <= av - 8)%nat.
Proof.
  unfold sys_pipe_stack, argaddr_stack, fdalloc_stack, fileclose_stack, K_iput.
  lia.
Qed.

(* a descriptor index is small, in the three shapes the proof consumes *)
Lemma sp_fd_range (n : nat) : (n < NOFILE)%nat ->
  (0 <= Z.of_nat n < 16)%Z /\ (0 <= Z.of_nat n < 2 ^ 31)%Z.
Proof.
  unfold NOFILE. intro Hn.
  assert (E31 : (2 ^ 31 = 2147483648)%Z) by (vm_compute; reflexivity).
  split; lia.
Qed.

(* the two side conditions [ProcGeom.ofile_slli3]/[ofile_addi208] take *)
Lemma sp_arg0 : (0 < NARG)%nat.
Proof. unfold NARG. lia. Qed.

Lemma sp_frame_back (av : nat) : (8 <= av)%nat -> ((av - 8) + 8)%nat = av.
Proof. lia. Qed.

Lemma sp_mul_comm (z : Z) : (208 + z * 8)%Z = (208 + 8 * z)%Z.
Proof. lia. Qed.

Lemma sp_ofile_arith (z : Z) : (0 <= z < 16)%Z ->
  (0 <= z)%Z /\ (z * 8 < 18446744073709551616)%Z /\
  (0 <= z * 8)%Z /\ (z * 8 + 208 < 18446744073709551616)%Z.
Proof. intro Hz. split; [lia|]. split; [lia|]. split; lia. Qed.

(* RE-NULLING A DESCRIPTOR THAT WAS FREE IS THE IDENTITY.  Both failure
   tails write 0 back over a slot [fd_frees] says was already 0, so the
   process state they hand to [sys_pipe_post] is literally the incoming one.
   One lemma per tail: one descriptor, and two. *)
Lemma sp_ofile_restore (V : pprivate) (fd : nat) (x : mword 64) :
  pv_ofile V !! fd = Some (zero_reg : mword 64) ->
  upd_ofile (upd_ofile V fd x) fd (zero_reg : mword 64) = V.
Proof.
  intro Hlk. unfold upd_ofile.
  cbn [pv_sz pv_upt pv_tf pv_ofile pv_cwd pv_name].
  rewrite list_insert_insert. rewrite (list_insert_id _ _ _ Hlk). by destruct V.
Qed.

(* copyout's length argument, and the page-table descriptor riding along the
   copyout-failure tail: [upd_upt] and [upd_ofile] touch different fields, so
   the tail's two re-nullings still land on the incoming state. *)
Lemma sp_len4 : (Z.of_nat 4 < 2 ^ 64)%Z.
Proof.
  assert (E : (2 ^ 64 = 18446744073709551616)%Z) by (vm_compute; reflexivity).
  rewrite E. lia.
Qed.

(* copyout is generic in the interrupt level (the pipe loops call it at 1);
   sys_pipe is at syscall altitude, so it passes 0 and pays vmfault's kalloc
   premise here rather than inline at the two call sites (the inline-[ltac:]
   trap, optimization.md). *)
Lemma sp_n0 : (Z.of_nat 0%nat + 1 < 2 ^ 31)%Z.
Proof. vm_compute. reflexivity. Qed.

(* [upd_upt] and [upd_ofile] touch different fields, so the success arm's
   state can be read either way round; [sys_pipe_post] spells it with the
   descriptors outermost. *)
Lemma sp_upt_ofile_comm (V : pprivate) (P' : uptd) (fd0 fd1 : nat) (x0 x1 : mword 64) :
  upd_ofile (upd_ofile (upd_upt V P') fd0 x0) fd1 x1
  = upd_upt (upd_ofile (upd_ofile V fd0 x0) fd1 x1) P'.
Proof. by destruct V. Qed.

Lemma sp_restore_upt (V : pprivate) (P' : uptd) (fd0 fd1 : nat) (x0 x1 : mword 64) :
  fd0 <> fd1 ->
  pv_ofile V !! fd0 = Some (zero_reg : mword 64) ->
  pv_ofile V !! fd1 = Some (zero_reg : mword 64) ->
  upd_ofile (upd_ofile (upd_upt (upd_ofile (upd_ofile V fd0 x0) fd1 x1) P')
                       fd0 (zero_reg : mword 64)) fd1 (zero_reg : mword 64)
  = upd_upt V P'.
Proof.
  intros Hne H0 H1. unfold upd_ofile, upd_upt.
  cbn [pv_sz pv_upt pv_tf pv_ofile pv_cwd pv_name].
  rewrite (list_insert_commute _ fd0 fd1 (zero_reg : mword 64) x1 Hne).
  rewrite !list_insert_insert.
  rewrite (list_insert_id _ _ _ H0) (list_insert_id _ _ _ H1).
  by destruct V.
Qed.

Lemma sp_ofile_restore2 (V : pprivate) (fd0 fd1 : nat) (x0 x1 : mword 64) :
  fd0 <> fd1 ->
  pv_ofile V !! fd0 = Some (zero_reg : mword 64) ->
  pv_ofile V !! fd1 = Some (zero_reg : mword 64) ->
  upd_ofile (upd_ofile (upd_ofile (upd_ofile V fd0 x0) fd1 x1) fd0 (zero_reg : mword 64))
            fd1 (zero_reg : mword 64) = V.
Proof.
  intros Hne H0 H1. unfold upd_ofile.
  cbn [pv_sz pv_upt pv_tf pv_ofile pv_cwd pv_name].
  rewrite (list_insert_commute _ fd0 fd1 (zero_reg : mword 64) x1 Hne).
  rewrite !list_insert_insert.
  rewrite (list_insert_id _ _ _ H0) (list_insert_id _ _ _ H1).
  by destruct V.
Qed.

(* writing back the descriptor a process already had is the identity: every
   failure tail re-nulls a slot that [fd_frees] says was already null. *)
Lemma sp_upd_upt_id (V : pprivate) : upd_upt V (pv_upt V) = V.
Proof. by destruct V. Qed.

Module SysPipeProof (Myproc : MYPROC) (Argaddr : ARGADDR) (Pipealloc : PIPEALLOC)
                    (Fdalloc : FDALLOC) (Fileclose : FILECLOSE) (Copyout : COPYOUT)
  : SYSPIPE.

Section ProofSysPipe.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !kallocG Σ, !fdslotG Σ, !fileG Σ,
            !bioG Σ, !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ, !fsCrashG Σ,
            !irefslotG Σ, !iregG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  (* register indices, named once *)
  Notation Rra := (mword_of_int 1 : mword 5).
  Notation Rs0 := (mword_of_int 8 : mword 5).
  Notation Rs1 := (mword_of_int 9 : mword 5).
  Notation Ra0 := (mword_of_int 10 : mword 5).
  Notation Ra1 := (mword_of_int 11 : mword 5).
  Notation Ra2 := (mword_of_int 12 : mword 5).
  Notation Ra3 := (mword_of_int 13 : mword 5).
  Notation Ra4 := (mword_of_int 14 : mword 5).
  Notation Ra5 := (mword_of_int 15 : mword 5).
  Notation Rz  := (mword_of_int 0 : mword 5).

  Local Ltac regne := reg_ne_side.

  (* the frame's sp is sound: read the bound out of the ambient capability's
     own stack carve (the conclusion is pure, so the bundle survives). *)
  (* THE CARVE THIS READS IS ARM-DEPENDENT, hence the [0 < k] premise.
     [IntrDefs.sie_cap] owns [trap_res bb + k] slots, and [trap_res false] is
     NOTHING -- so at the interrupts-off arm the ONLY slots underwriting an sp
     bound are the caller's own [k], and a zero-slot carve says nothing about
     sp at all.  (Under the old arm-blind reserve the 78 reserved slots
     covered it at either arm, which is why this used to need no premise.
     The premise is local to this helper: every call site sits inside the
     capstone, whose [<fn>_stack <= av] premise is already unfolded, so it is
     a [lia].) *)
  Lemma sp_sp_bounds `{CID0 : CpuId} (m : regfile) (k : nat)
      (b : bool) (p : mword 64) :
    (0 < k)%nat ->
    sie_cap_gpr m k b p -∗
    ⌜(8 <= uint (m !!! Regidx csp_rs1) < 274877906944 + 8)%Z⌝.
  Proof.
    iIntros (Hk) "(_ & _ & (Hstk & _ & _) & _)".
    iApply (stack_own_sp_bounds _ (trap_res b + k)%nat with "Hstk").
    destruct b; unfold trap_res, kv_frame_slots; lia.
  Qed.

  (* =================================================================== *)
  (*  [slli/addi/add/sd] -- "p->ofile[fd] = 0" for an fd sitting in a5.   *)
  (*  gcc emitted it three times (+0x84, +0x94, +0xbc), so it is ONE      *)
  (*  lemma over the entry offset [a] and a SYMBOLIC descriptor index.    *)
  (* =================================================================== *)
  (* WHICH register the [add] lands in -- and therefore which one the [sd]
     uses as its base -- is gcc's choice, and it is not the same at all three
     sites: a5 at +0x84 and +0xbc, but s1 at +0x94, where [p] is dead
     afterwards.  The two operands are the same pair either way, so the lemma
     stays ONE, indexed by which of the pair is the destination; the price is
     that the postcondition preserves everything but a5 AND [Rd]. *)
  Lemma sp_ofile_null `{CID0 : CpuId}
      (Mt : regfile) (nav : nat) (p : mword 64) (fd : nat) (Rd Ro : mword 5)
      (za zb zc zd ze : Z) (old : mword 64) (b : bool) :
    (0 <= Z.of_nat fd < 16)%Z ->
    (Rd = Ra5 /\ Ro = Rs1) \/ (Rd = Rs1 /\ Ro = Ra5) ->
    Mt !!! Regidx Ra5 = (mword_of_int (Z.of_nat fd) : mword 64) ->
    Mt !!! Regidx Rs1 = p ->
    (* The five pcs are LITERALS supplied by the call site, not [a + k]
       arithmetic: an [instr] fact whose address must be CONVERTED to match
       (0xb8 + 2 against 0xba) makes every [iApply] here reduce a [Z_to_bv]
       over a kernel address, and the proof stops coming back. *)
    add_vec_int (mword_of_int za : mword 64) 2 = mword_of_int zb ->
    add_vec_int (mword_of_int zb : mword 64) 4 = mword_of_int zc ->
    add_vec_int (mword_of_int zc : mword 64) 2 = mword_of_int zd ->
    add_vec_int (mword_of_int zd : mword 64) 4 = mword_of_int ze ->
    sie_cap_gpr Mt nav b p -∗
    pc_is (mword_of_int za : mword 64) -∗
    instr (mword_of_int za : mword 64) true
      (SHIFTIOP (mword_of_int 3 : mword 6, Regidx Ra5, Regidx Ra5, SLLI)) -∗
    instr (mword_of_int zb : mword 64) false
      (ITYPE (mword_of_int 208 : mword 12, Regidx Ra5, Regidx Ra5, ADDI)) -∗
    instr (mword_of_int zc : mword 64) true (RTYPE (Regidx Ro, Regidx Rd, Regidx Rd, ADD)) -∗
    instr (mword_of_int zd : mword 64) false
      (STORE (mword_of_int 0 : mword 12, Regidx Rz, Regidx Rd, 8)) -∗
    p_ofile p fd ↦₈ old -∗
    wp_next b p (fun (CID : CpuId) =>
      ∀ Mr : regfile,
        ⌜forall c : mword 5, c <> Ra5 -> c <> Rd -> Mr !!! Regidx c = Mt !!! Regidx c⌝ -∗
        sie_cap_gpr Mr nav b p -∗
        pc_is (mword_of_int ze : mword 64) -∗
        p_ofile p fd ↦₈ (zero_reg : mword 64) -∗
        WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hfd Hro Ha5 Hs1 Hs2 Hs6 Hs8 Hs12.
    destruct (sp_ofile_arith (Z.of_nat fd) Hfd) as (Ha1 & Ha2 & Ha3 & Ha4).
    iIntros "Hcg Hpc Hi0 Hi2 Hi6 Hi8 Hcell Hcont".
    (* ---- +a: c.slli a5,a5,3 ---- *)
    iApply (wp_cslli_s_sconf (mword_of_int za) (Regidx Ra5) Ra5
              (mword_of_int 3 : mword 6) Mt nav b
              eq_refl ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi0").
    iIntros (CID1 Hcr1) "Hcg Hpc".
    set (N1 := <[Regidx Ra5 := regval_into_reg
                  (shift_bits_left (rget Mt Ra5)
                     (subrange_vec_dec (mword_of_int 3 : mword 6) (Z.sub log2_xlen 1) 0))]> Mt).
    change (<[Regidx Ra5 := regval_into_reg
                (shift_bits_left (rget Mt Ra5)
                   (subrange_vec_dec (mword_of_int 3 : mword 6) (Z.sub log2_xlen 1) 0))]> Mt) with N1.
    iEval (rewrite Hs2) in "Hpc".
    assert (HN1a5 : N1 !!! Regidx Ra5 = mword_of_int (Z.of_nat fd * 8)).
    { rewrite /N1 upd_eq. rgne. rewrite Ha5.
      exact (ofile_slli3 (Z.of_nat fd) Ha1 Ha2). }
    (* ---- +a+2: addi a5,a5,208 ---- *)
    iApply (wp_addi4_s_sconf (mword_of_int zb) Ra5 Ra5
              (mword_of_int 208 : mword 12) N1 nav b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi2").
    iIntros (CID2 Hcr2) "Hcg Hpc".
    set (N2 := <[Regidx Ra5 := regval_into_reg
                  (add_vec (rget N1 Ra5) (sign_extend' 64 (mword_of_int 208 : mword 12)))]> N1).
    change (<[Regidx Ra5 := regval_into_reg
                (add_vec (rget N1 Ra5) (sign_extend' 64 (mword_of_int 208 : mword 12)))]> N1) with N2.
    iEval (rewrite Hs6) in "Hpc".
    assert (HN2a5 : N2 !!! Regidx Ra5 = mword_of_int (208 + 8 * Z.of_nat fd)).
    { rewrite /N2 upd_eq. rgne. rewrite HN1a5.
      rewrite (ofile_addi208 (Z.of_nat fd * 8) Ha3 Ha4).
      by rewrite (sp_mul_comm (Z.of_nat fd)). }
    assert (HN2s1 : N2 !!! Regidx Rs1 = p).
    { rewrite /N2 upd_ne; [| vm_compute; discriminate].
      rewrite /N1 upd_ne; [exact Hs1 | vm_compute; discriminate]. }
    (* ---- +a+6: c.add Rd,Rd,Ro  ---- *)
    (* The two arms differ only in which of the pair is written; the registers
       have to be LITERALS for [rdok] / [SrcOk] to decide, so the split is
       here rather than in the statement. *)
    destruct Hro as [[-> ->] | [-> ->]].
    - iApply (wp_cadd_s_sconf (mword_of_int zc) Ra5 Rs1 N2 nav b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi6").
      iIntros (CID3 Hcr3) "Hcg Hpc".
      set (N3 := <[Regidx Ra5 := regval_into_reg
                    (add_vec (rget N2 Ra5) (rget N2 Rs1))]> N2).
      change (<[Regidx Ra5 := regval_into_reg
                  (add_vec (rget N2 Ra5) (rget N2 Rs1))]> N2) with N3.
      iEval (rewrite Hs8) in "Hpc".
      assert (HN3a5 : N3 !!! Regidx Ra5 = p_ofile p fd).
      { rewrite /N3 upd_eq. rgne. rgne. rewrite HN2a5 HN2s1 add_vec64_comm. reflexivity. }
      (* ---- +a+8: sd x0,0(a5) ---- *)
      assert (Hadd : add_vec (rget N3 Ra5) (sign_extend' 64 (mword_of_int 0 : mword 12))
                     = p_ofile p fd) by (rgne; rewrite HN3a5; apply addv_sext0).
      iEval (rewrite -Hadd) in "Hcell".
      iApply (wp_sd_zero_s_sconf (mword_of_int zd) Ra5
                (mword_of_int 0 : mword 12) N3 nav old b
                with "Hcg Hpc Hi8 Hcell").
      iIntros (CID4 Hcr4) "Hcg Hpc Hcell".
      iEval (rewrite Hadd) in "Hcell".
      iEval (rewrite Hs12) in "Hpc".
      iSpecialize ("Hcont" $! CID4 with "[%]"); [wp_next_chain|].
      iApply ("Hcont" $! N3 with "[%] Hcg Hpc Hcell").
      intros c Hc _.
      rewrite /N3 upd_ne; [| congruence].
      rewrite /N2 upd_ne; [| congruence].
      rewrite /N1 upd_ne; [reflexivity | congruence].
    - iApply (wp_cadd_s_sconf (mword_of_int zc) Rs1 Ra5 N2 nav b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi6").
      iIntros (CID3 Hcr3) "Hcg Hpc".
      set (N3 := <[Regidx Rs1 := regval_into_reg
                    (add_vec (rget N2 Rs1) (rget N2 Ra5))]> N2).
      change (<[Regidx Rs1 := regval_into_reg
                  (add_vec (rget N2 Rs1) (rget N2 Ra5))]> N2) with N3.
      iEval (rewrite Hs8) in "Hpc".
      assert (HN3s1 : N3 !!! Regidx Rs1 = p_ofile p fd).
      { rewrite /N3 upd_eq. rgne. rgne. rewrite HN2a5 HN2s1. reflexivity. }
      (* ---- +a+8: sd x0,0(s1) ---- *)
      assert (Hadd : add_vec (rget N3 Rs1) (sign_extend' 64 (mword_of_int 0 : mword 12))
                     = p_ofile p fd) by (rgne; rewrite HN3s1; apply addv_sext0).
      iEval (rewrite -Hadd) in "Hcell".
      iApply (wp_sd_zero_s_sconf (mword_of_int zd) Rs1
                (mword_of_int 0 : mword 12) N3 nav old b
                with "Hcg Hpc Hi8 Hcell").
      iIntros (CID4 Hcr4) "Hcg Hpc Hcell".
      iEval (rewrite Hadd) in "Hcell".
      iEval (rewrite Hs12) in "Hpc".
      iSpecialize ("Hcont" $! CID4 with "[%]"); [wp_next_chain|].
      iApply ("Hcont" $! N3 with "[%] Hcg Hpc Hcell").
      intros c Hc Hd.
      rewrite /N3 upd_ne; [| congruence].
      rewrite /N2 upd_ne; [| congruence].
      rewrite /N1 upd_ne; [reflexivity | congruence].
  Qed.

  (* =================================================================== *)
  (*  [ld/jal/ld/jal/c.li] -- "fileclose(rf); fileclose(wf); return -1".  *)
  (*  gcc emitted this twice (+0xa0 and +0xc8), so again ONE lemma over   *)
  (*  the entry offset [a] and the two relocated jal immediates.          *)
  (* =================================================================== *)
  Lemma sp_close2 `{CID0 : CpuId}  (γfl γf : gname)
      (fn : fclose_names) (on : option nat) (us : gset Z)
      (Mt : regfile) (nav : nat) (eb : bool) (p : mword 64) (C : iProp Σ)
      (sp0 : mword 64) (k0 k1 : nat) (q0 q1 : Qp) (Cf0 Cf1 : fcontent)
      (za zb zc zd ze zf : Z) (imm1 imm2 : mword 21) (b : bool) :
    (fileclose_stack <= nav)%nat ->
    Mt !!! Regidx Rs0 = sp0 ->
    (* the pc successors and the two relocated call targets *)
    ret_pc (add_vec_int (mword_of_int zb : mword 64) 4) = mword_of_int zc ->
    ret_pc (add_vec_int (mword_of_int zd : mword 64) 4) = mword_of_int ze ->
    add_vec_int (mword_of_int za : mword 64) 4 = mword_of_int zb ->
    add_vec_int (mword_of_int zc : mword 64) 4 = mword_of_int zd ->
    add_vec_int (mword_of_int ze : mword 64) 2 = mword_of_int zf ->
    add_vec (mword_of_int zb : mword 64) (sign_extend' 64 imm1)
      = mword_of_int KernelSyms.fileclose ->
    add_vec (mword_of_int zd : mword 64) (sign_extend' 64 imm2)
      = mword_of_int KernelSyms.fileclose ->
    sie_cap_gpr Mt nav b p -∗
    cpu_own 0%nat eb p C b -∗
    (* THE COMPLEMENT, THREADED THROUGH BOTH CLOSES.  fileclose takes it at
       the top level of its contract on every arm and gives it back, so this
       block cannot frame it: its two crossings are the literal [true]. *)
    trap_csrs_ext eb -∗
    cpu_claim_ext eb p -∗
    kernel_text -∗
    pc_is (mword_of_int za : mword 64) -∗
    is_ftable γfl γf -∗
    panic_wp_any -∗
    instr (mword_of_int za : mword 64) false
      (LOAD (mword_of_int 0xfd0 : mword 12, Regidx Rs0, Regidx Ra0, false, 8)) -∗
    instr (mword_of_int zb : mword 64) false (JAL (imm1, Regidx Rra)) -∗
    instr (mword_of_int zc : mword 64) false
      (LOAD (mword_of_int 0xfc8 : mword 12, Regidx Rs0, Regidx Ra0, false, 8)) -∗
    instr (mword_of_int zd : mword 64) false (JAL (imm2, Regidx Rra)) -∗
    instr (mword_of_int ze : mword 64) true
      (ITYPE (sign_extend' 12 (mword_of_int 63 : mword 6), zreg, Regidx Ra5, ADDI)) -∗
    word_pointsto (pa_stk sp0 6) (DfracOwn 1) (fnode k0) -∗
    word_pointsto (pa_stk sp0 7) (DfracOwn 1) (fnode k1) -∗
    file_ref γf k0 q0 Cf0 -∗
    file_ref γf k1 q1 Cf1 -∗
    (* both closes run under ONE environment, threaded through: the first may
       have moved the page count, so what the second gets, and what comes
       out, is at an existential [on'] *)
    fileclose_pipe_env fn on 0%nat -∗
    fileclose_fs_env fn us 0%nat eb p -∗
    (* the crossing is the literal [true]: both closes cross at [true]. *)
    wp_next true p (fun (CID : CpuId) =>
      ∀ Mr : regfile,
        ⌜ (forall c : mword 5, is_cs_idx c = true -> Mr !!! Regidx c = Mt !!! Regidx c)
          /\ Mr !!! Regidx Ra5 = (mword_of_int (-1) : mword 64) ⌝ -∗
        sie_cap_gpr Mr nav b p -∗
        cpu_own 0%nat eb p C b -∗
        trap_csrs_ext eb -∗
        cpu_claim_ext eb p -∗
        pc_is (mword_of_int zf : mword 64) -∗
        word_pointsto (pa_stk sp0 6) (DfracOwn 1) (fnode k0) -∗
        word_pointsto (pa_stk sp0 7) (DfracOwn 1) (fnode k1) -∗
        fd_slot -∗ fd_slot -∗
        (∃ on', fileclose_pipe_env fn on' 0%nat) -∗
        (∃ us', fileclose_fs_env fn us' 0%nat eb p) -∗
        WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hnav Hs0 Hr1 Hr2 Hs04 Hs812 Hs1618 Ht1 Ht2.
    iIntros "Hcg Hcpu Hextc Hextm #Htext Hpc #Hftab #Hpanic Hi0 Hi4 Hi8 Hic Hi10
              Hc6 Hc7 Href0 Href1 Hpenv Hfenv Hcont".
    (* [eb = b] -- this block runs at push_off level 0 (the [cpu_own 0] above),
       so [CpuOwn.cpu_own_eb_agree] gives it outright.  Used ONLY to align the
       complement's [eb]-guard with the [b]-spelled chain facts; do NOT
       [subst], [b] is spelled by name in every leaf argument below. *)
    iDestruct (cpu_own_eb_agree with "Hcg Hcpu") as %Hb.
    (* ---- +a: ld a0,-48(s0) -- a0 := rf ---- *)
    assert (Had6 : add_vec (rget Mt Rs0) (sign_extend' 64 (mword_of_int 0xfd0 : mword 12))
                   = pa_stk sp0 6) by (rgne; rewrite Hs0; apply sp_addr_rf).
    iEval (rewrite -Had6) in "Hc6".
    iApply (wp_ld_s_sconf (mword_of_int za) Ra0 Rs0
              (mword_of_int 0xfd0 : mword 12) Mt nav (fnode k0) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi0 Hc6").
    iIntros (CID5 Hcr5) "Hcg Hpc Hc6". iEval (rewrite Had6) in "Hc6".
    set (D1 := <[Regidx Ra0 := regval_into_reg (fnode k0)]> Mt).
    iEval (rewrite Hs04) in "Hpc".
    (* ---- +a+4: jal ra,fileclose ---- *)
    iApply (wp_jal_s_sconf (mword_of_int zb) Rra imm1 D1 nav b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(rewrite Ht1; vm_compute; reflexivity) with "Hcg Hpc Hi4").
    iIntros (CID6 Hcr6) "Hcg Hpc".
    set (D2 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int zb : mword 64) 4)]> D1).
    iEval (rewrite Ht1) in "Hpc".
    assert (HD2a0 : D2 !!! Regidx Ra0 = fnode k0).
    { rewrite /D2 upd_ne; [| vm_compute; discriminate]. rewrite /D1; apply upd_eq. }
    assert (HD2ra : D2 !!! Regidx Rra = add_vec_int (mword_of_int zb : mword 64) 4)
      by (rewrite /D2; apply upd_eq).
    iDestruct (cpu_own_transport CID0 CID6 0%nat eb p C b ltac:(wp_next_chain)
                 with "Hcpu") as "Hcpu".
    iDestruct (trap_csrs_ext_transport CID0 CID6 eb p
                 ltac:(rewrite Hb; wp_next_chain) with "Hextc") as "Hextc".
    iDestruct (cpu_claim_ext_transport CID0 CID6 eb p
                 ltac:(rewrite Hb; wp_next_chain) with "Hextm") as "Hextm".
    iDestruct (fileclose_env_frame fn on us 0%nat eb p Cf0 with "Hpenv Hfenv")
      as "[Hfcenv0 Hfcback0]".
    iApply (Fileclose.wp_fileclose_sconf γfl γf k0 q0 Cf0 fn on us D2 0%nat eb p C nav b
              Hnav sp_noff0 HD2a0
              with "Hcg Hcpu Hextc Hextm Htext Hpc Hftab Hpanic Href0 Hfcenv0").
    iIntros (CID7 Hcr7 E1) "Hcg Hcpu Hextc Hextm Hpc %HcsE1 Hunit0 Hout0".
    iDestruct ("Hfcback0" with "Hout0") as "[Hpenv Hfenv]".
    iDestruct "Hpenv" as (on1) "Hpenv".
    iDestruct "Hfenv" as (us1) "Hfenv".
    assert (HpcE1 : ret_pc (D2 !!! Regidx Rra) = mword_of_int zc)
      by (rewrite HD2ra; exact Hr1).
    iEval (rewrite HpcE1) in "Hpc".
    pose proof HcsE1 as HcsE1_cs.
    assert (HE1cs : forall c : mword 5, is_cs_idx c = true -> E1 !!! Regidx c = Mt !!! Regidx c).
    { intros c Hc.
      rewrite (callee_saved_lookup HcsE1_cs c Hc).
      rewrite /D2 upd_ne; [| regne]. rewrite /D1 upd_ne; [reflexivity | regne]. }
    assert (HE1s0 : E1 !!! Regidx Rs0 = sp0)
      by (rewrite (HE1cs Rs0 ltac:(vm_compute; reflexivity)); exact Hs0).
    (* ---- +a+8: ld a0,-56(s0) -- a0 := wf ---- *)
    assert (Had7 : add_vec (rget E1 Rs0) (sign_extend' 64 (mword_of_int 0xfc8 : mword 12))
                   = pa_stk sp0 7) by (rgne; rewrite HE1s0; apply sp_addr_wf).
    iEval (rewrite -Had7) in "Hc7".
    iApply (wp_ld_s_sconf (mword_of_int zc) Ra0 Rs0
              (mword_of_int 0xfc8 : mword 12) E1 nav (fnode k1) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi8 Hc7").
    iIntros (CID8 Hcr8) "Hcg Hpc Hc7". iEval (rewrite Had7) in "Hc7".
    set (F1 := <[Regidx Ra0 := regval_into_reg (fnode k1)]> E1).
    iEval (rewrite Hs812) in "Hpc".
    (* ---- +a+12: jal ra,fileclose ---- *)
    iApply (wp_jal_s_sconf (mword_of_int zd) Rra imm2 F1 nav b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(rewrite Ht2; vm_compute; reflexivity) with "Hcg Hpc Hic").
    iIntros (CID9 Hcr9) "Hcg Hpc".
    set (F2 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int zd : mword 64) 4)]> F1).
    iEval (rewrite Ht2) in "Hpc".
    assert (HF2a0 : F2 !!! Regidx Ra0 = fnode k1).
    { rewrite /F2 upd_ne; [| vm_compute; discriminate]. rewrite /F1; apply upd_eq. }
    assert (HF2ra : F2 !!! Regidx Rra = add_vec_int (mword_of_int zd : mword 64) 4)
      by (rewrite /F2; apply upd_eq).
    iDestruct (cpu_own_transport CID7 CID9 0%nat eb p C b ltac:(wp_next_chain)
                 with "Hcpu") as "Hcpu".
    (* from [CID7], the hart the FIRST close came back on -- its crossing is
       [true] and carries no chain fact of its own. *)
    iDestruct (trap_csrs_ext_transport CID7 CID9 eb p
                 ltac:(rewrite Hb; wp_next_chain) with "Hextc") as "Hextc".
    iDestruct (cpu_claim_ext_transport CID7 CID9 eb p
                 ltac:(rewrite Hb; wp_next_chain) with "Hextm") as "Hextm".
    iDestruct (fileclose_env_frame fn on1 us1 0%nat eb p Cf1 with "Hpenv Hfenv")
      as "[Hfcenv1 Hfcback1]".
    iApply (Fileclose.wp_fileclose_sconf γfl γf k1 q1 Cf1 fn on1 us1 F2 0%nat eb p C nav b
              Hnav sp_noff0 HF2a0
              with "Hcg Hcpu Hextc Hextm Htext Hpc Hftab Hpanic Href1 Hfcenv1").
    iIntros (CID10 Hcr10 G1) "Hcg Hcpu Hextc Hextm Hpc %HcsG1 Hunit1 Hout1".
    iDestruct ("Hfcback1" with "Hout1") as "[Hpenv Hfenv]".
    assert (HpcG1 : ret_pc (F2 !!! Regidx Rra) = mword_of_int ze)
      by (rewrite HF2ra; exact Hr2).
    iEval (rewrite HpcG1) in "Hpc".
    pose proof HcsG1 as HcsG1_cs.
    (* ---- +a+16: c.li a5,-1 ---- *)
    iApply (wp_cli_s_sconf (mword_of_int ze) Ra5 (mword_of_int 63 : mword 6)
              (mword_of_int (-1) : mword 64) G1 nav b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc Hi10").
    iIntros (CID11 Hcr11) "Hcg Hpc".
    set (G2 := <[Regidx Ra5 := regval_into_reg (mword_of_int (-1) : mword 64)]> G1).
    change (<[Regidx Ra5 := regval_into_reg (mword_of_int (-1) : mword 64)]> G1) with G2.
    iEval (rewrite Hs1618) in "Hpc".
    iDestruct (cpu_own_transport CID10 CID11 0%nat eb p C b ltac:(wp_next_chain)
                 with "Hcpu") as "Hcpu".
    iDestruct (trap_csrs_ext_transport CID10 CID11 eb p
                 ltac:(rewrite Hb; wp_next_chain) with "Hextc") as "Hextc".
    iDestruct (cpu_claim_ext_transport CID10 CID11 eb p
                 ltac:(rewrite Hb; wp_next_chain) with "Hextm") as "Hextm".
    iSpecialize ("Hcont" $! CID11 with "[%]"); [wp_next_chain|].
    iApply ("Hcont" $! G2 with "[%] Hcg Hcpu Hextc Hextm Hpc Hc6 Hc7 Hunit0 Hunit1 Hpenv Hfenv").
    split; [| rewrite /G2; apply upd_eq].
    intros c Hc.
    rewrite /G2 upd_ne; [| regne].
    rewrite (callee_saved_lookup HcsG1_cs c Hc).
    rewrite /F2 upd_ne; [| regne].
    rewrite /F1 upd_ne; [| regne].
    apply HE1cs; assumption.
  Qed.

  (* =================================================================== *)
  (*  +0xda .. +0xe4 -- THE epilogue.  All four exits reach it with the   *)
  (*  return value already in a5, so it is proved once over that value.   *)
  (* =================================================================== *)
  Lemma sp_epi `{CID0 : CpuId}
      (m Mt : regfile) (av : nat) (rv : mword 64)
      (sp0 ra0 s00 s10 : mword 64) (w4 w5 w6 w7 w8 : bv 64)
      (p : mword 64) (b : bool) :
    (8 <= av)%nat ->
    m !!! Regidx csp_rs1 = sp0 ->
    m !!! Regidx Rra = ra0 ->
    m !!! Regidx Rs0 = s00 ->
    m !!! Regidx Rs1 = s10 ->
    Mt !!! Regidx csp_rs1 = pa_stk sp0 8 ->
    Mt !!! Regidx Ra5 = rv ->
    (forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
        r <> Rs0 -> r <> Rs1 -> Mt !!! Regidx r = m !!! Regidx r) ->
    sie_cap_gpr Mt (av - 8)%nat b p -∗
    kernel_text -∗
    pc_is (mword_of_int (KernelSyms.sys_pipe + 0xda) : mword 64) -∗
    word_pointsto (pa_stk sp0 1) (DfracOwn 1) ra0 -∗
    word_pointsto (pa_stk sp0 2) (DfracOwn 1) s00 -∗
    word_pointsto (pa_stk sp0 3) (DfracOwn 1) s10 -∗
    word_pointsto (pa_stk sp0 4) (DfracOwn 1) w4 -∗
    word_pointsto (pa_stk sp0 5) (DfracOwn 1) w5 -∗
    word_pointsto (pa_stk sp0 6) (DfracOwn 1) w6 -∗
    word_pointsto (pa_stk sp0 7) (DfracOwn 1) w7 -∗
    word_pointsto (pa_stk sp0 8) (DfracOwn 1) w8 -∗
    wp_next b p (fun (CID : CpuId) =>
      ∀ mf : regfile,
        ⌜callee_saved m mf /\ mf !!! Regidx Ra0 = rv⌝ -∗
        sie_cap_gpr mf av b p -∗
        pc_is (ret_pc ra0) -∗
        WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hav Hsp0 Hra0 Hs00 Hs10 Hmtsp Hmt15 Hthr.
    iIntros "Hcg #Htext Hpc Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hb7 Hb8 Hcont".
    iPoseProof (spi_da with "Htext") as "Hida".
    iPoseProof (spi_dc with "Htext") as "Hidc".
    iPoseProof (spi_de with "Htext") as "Hide".
    iPoseProof (spi_e0 with "Htext") as "Hie0".
    iPoseProof (spi_e2 with "Htext") as "Hie2".
    iPoseProof (spi_e4 with "Htext") as "Hie4".
    (* ---- +0xda: c.mv a0,a5 ---- *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.sys_pipe + 0xda)) Ra0 Ra5 Mt (av - 8)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hida").
    iIntros (CID12 Hcr12) "Hcg Hpc".
    set (T1 := <[Regidx Ra0 := regval_into_reg (add_vec zero_reg (rget Mt Ra5))]> Mt).
    change (<[Regidx Ra0 := regval_into_reg (add_vec zero_reg (rget Mt Ra5))]> Mt) with T1.
    assert (HT1a0 : T1 !!! Regidx Ra0 = rv).
    { rewrite /T1 upd_eq. rgne. rewrite Hmt15. apply add_vec_zero_l. }
    assert (HT1sp : T1 !!! Regidx csp_rs1 = pa_stk sp0 8)
      by (rewrite /T1 upd_ne; [exact Hmtsp | vm_compute; discriminate]).
    assert (Hppdc : add_vec_int (mword_of_int (KernelSyms.sys_pipe + 0xda) : mword 64) 2
                    = mword_of_int (KernelSyms.sys_pipe + 0xdc)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hppdc) in "Hpc".
    (* ---- +0xdc: c.ldsp ra,56(sp) ---- *)
    assert (Hpa1 : add_vec (T1 !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 7 : mword 6) ('b"000"))) = pa_stk sp0 1)
      by (rewrite HT1sp; apply sp_frm1).
    iEval (rewrite -Hpa1) in "Hb1".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.sys_pipe + 0xdc)) (mword_of_int 7 : mword 6) Rra
              T1 (av - 8)%nat ra0 b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hidc Hb1").
    iIntros (CID13 Hcr13) "Hcg Hpc Hb1". iEval (rewrite Hpa1) in "Hb1".
    set (T2 := <[Regidx Rra := regval_into_reg ra0]> T1).
    assert (HT2sp : T2 !!! Regidx csp_rs1 = pa_stk sp0 8)
      by (rewrite /T2 upd_ne; [exact HT1sp | vm_compute; discriminate]).
    assert (Hppde : add_vec_int (mword_of_int (KernelSyms.sys_pipe + 0xdc) : mword 64) 2
                    = mword_of_int (KernelSyms.sys_pipe + 0xde)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hppde) in "Hpc".
    (* ---- +0xde: c.ldsp s0,48(sp) ---- *)
    assert (Hpa2 : add_vec (T2 !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 6 : mword 6) ('b"000"))) = pa_stk sp0 2)
      by (rewrite HT2sp; apply sp_frm2).
    iEval (rewrite -Hpa2) in "Hb2".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.sys_pipe + 0xde)) (mword_of_int 6 : mword 6) Rs0
              T2 (av - 8)%nat s00 b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hide Hb2").
    iIntros (CID14 Hcr14) "Hcg Hpc Hb2". iEval (rewrite Hpa2) in "Hb2".
    set (T3 := <[Regidx Rs0 := regval_into_reg s00]> T2).
    assert (HT3sp : T3 !!! Regidx csp_rs1 = pa_stk sp0 8)
      by (rewrite /T3 upd_ne; [exact HT2sp | vm_compute; discriminate]).
    assert (Hppe0 : add_vec_int (mword_of_int (KernelSyms.sys_pipe + 0xde) : mword 64) 2
                    = mword_of_int (KernelSyms.sys_pipe + 0xe0)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hppe0) in "Hpc".
    (* ---- +0xe0: c.ldsp s1,40(sp) ---- *)
    assert (Hpa3 : add_vec (T3 !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000"))) = pa_stk sp0 3)
      by (rewrite HT3sp; apply sp_frm3).
    iEval (rewrite -Hpa3) in "Hb3".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.sys_pipe + 0xe0)) (mword_of_int 5 : mword 6) Rs1
              T3 (av - 8)%nat s10 b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hie0 Hb3").
    iIntros (CID15 Hcr15) "Hcg Hpc Hb3". iEval (rewrite Hpa3) in "Hb3".
    set (T4 := <[Regidx Rs1 := regval_into_reg s10]> T3).
    assert (HT4sp : T4 !!! Regidx csp_rs1 = pa_stk sp0 8)
      by (rewrite /T4 upd_ne; [exact HT3sp | vm_compute; discriminate]).
    assert (Hppe2 : add_vec_int (mword_of_int (KernelSyms.sys_pipe + 0xe0) : mword 64) 2
                    = mword_of_int (KernelSyms.sys_pipe + 0xe2)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hppe2) in "Hpc".
    (* ---- +0xe2: c.addi16sp sp,64 -- the frame trade back ---- *)
    assert (Hwv : add_vec (T4 !!! Regidx csp_rs1)
                    (sign_extend' 64 (caddi16sp_imm (mword_of_int 4 : mword 6))) = sp0)
      by (rewrite HT4sp; apply stk_pop_64).
    assert (Hpop : T4 !!! Regidx csp_rs1
                   = pa_stk (add_vec (T4 !!! Regidx csp_rs1)
                       (sign_extend' 64 (caddi16sp_imm (mword_of_int 4 : mword 6)))) 8)
      by (rewrite Hwv; exact HT4sp).
    iAssert (stack_own sp0 8) with "[Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hb7 Hb8]" as "Hframe".
    { rewrite stack_own_slots. cbn [seq].
      iSplitL "Hb1"; [iExists _; iExact "Hb1"|].
      iSplitL "Hb2"; [iExists _; iExact "Hb2"|].
      iSplitL "Hb3"; [iExists _; iExact "Hb3"|].
      iSplitL "Hb4"; [iExists _; iExact "Hb4"|].
      iSplitL "Hb5"; [iExists _; iExact "Hb5"|].
      iSplitL "Hb6"; [iExists _; iExact "Hb6"|].
      iSplitL "Hb7"; [iExists _; iExact "Hb7"|].
      iSplitL "Hb8"; [iExists _; iExact "Hb8"|].
      done. }
    iEval (rewrite -Hwv) in "Hframe".
    iApply (wp_caddi16sp_pop_s_sconf (mword_of_int (KernelSyms.sys_pipe + 0xe2)) (mword_of_int 4 : mword 6)
              T4 (av - 8)%nat 8 b Hpop with "Hcg Hpc Hie2 Hframe").
    iIntros (CID16 Hcr16) "Hcg Hpc".
    assert (Hnk : ((av - 8) + 8)%nat = av) by exact (sp_frame_back av Hav).
    iEval (rewrite Hnk) in "Hcg".
    set (T5 := <[Regidx csp_rs1 := regval_into_reg
                  (add_vec (T4 !!! Regidx csp_rs1)
                     (sign_extend' 64 (caddi16sp_imm (mword_of_int 4 : mword 6))))]> T4).
    change (<[Regidx csp_rs1 := regval_into_reg
        (add_vec (T4 !!! Regidx csp_rs1)
           (sign_extend' 64 (caddi16sp_imm (mword_of_int 4 : mword 6))))]> T4) with T5.
    assert (Hppe4 : add_vec_int (mword_of_int (KernelSyms.sys_pipe + 0xe2) : mword 64) 2
                    = mword_of_int (KernelSyms.sys_pipe + 0xe4)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hppe4) in "Hpc".
    (* ---- +0xe4: c.ret ---- *)
    assert (HT5ra : T5 !!! Regidx Rra = ra0).
    { rewrite /T5 upd_ne; [| vm_compute; discriminate].
      rewrite /T4 upd_ne; [| vm_compute; discriminate].
      rewrite /T3 upd_ne; [| vm_compute; discriminate].
      rewrite /T2 upd_eq. reflexivity. }
    assert (HT5a0 : T5 !!! Regidx Ra0 = rv).
    { rewrite /T5 upd_ne; [| vm_compute; discriminate].
      rewrite /T4 upd_ne; [| vm_compute; discriminate].
      rewrite /T3 upd_ne; [| vm_compute; discriminate].
      rewrite /T2 upd_ne; [exact HT1a0 | vm_compute; discriminate]. }
    iApply (wp_cret_s_sconf (mword_of_int (KernelSyms.sys_pipe + 0xe4)) Rra T5 av b
              ltac:(vm_compute; discriminate) with "Hcg Hpc Hie4").
    iIntros (CID17 Hcr17) "Hcg Hpc".
    assert (Hretf : ret_pc (T5 !!! Regidx Rra) = ret_pc ra0) by (rewrite HT5ra; reflexivity).
    iEval (rgne; rewrite Hretf) in "Hpc".
    iSpecialize ("Hcont" $! CID17 with "[%]"); [wp_next_chain|].
    iApply ("Hcont" $! T5 with "[%] Hcg Hpc").
    split; [| exact HT5a0].
    assert (Hthread : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
              r <> Rs0 -> r <> Rs1 -> T5 !!! Regidx r = m !!! Regidx r).
    { intros r Hcs N2 N8 N9.
      assert (N1 : r <> Rra) by (intro He; rewrite He in Hcs; vm_compute in Hcs; discriminate).
      assert (N10 : r <> Ra0) by (intro He; rewrite He in Hcs; vm_compute in Hcs; discriminate).
      rewrite /T5 upd_ne; [| congruence].
      rewrite /T4 upd_ne; [| congruence].
      rewrite /T3 upd_ne; [| congruence].
      rewrite /T2 upd_ne; [| congruence].
      rewrite /T1 upd_ne; [| congruence].
      apply Hthr; assumption. }
    unfold callee_saved.
    assert (Hc2 : T5 !!! Regidx csp_rs1 = m !!! Regidx csp_rs1)
      by (rewrite /T5 upd_eq; rewrite Hwv Hsp0; reflexivity).
    assert (Hc8 : T5 !!! Regidx Rs0 = m !!! Regidx Rs0).
    { rewrite /T5 upd_ne; [| vm_compute; discriminate].
      rewrite /T4 upd_ne; [| vm_compute; discriminate].
      rewrite /T3 upd_eq. by rewrite Hs00. }
    assert (Hc9 : T5 !!! Regidx Rs1 = m !!! Regidx Rs1).
    { rewrite /T5 upd_ne; [| vm_compute; discriminate].
      rewrite /T4 upd_eq. by rewrite Hs10. }
    (* [repeat split] would close some of these fourteen conjuncts by KERNEL
       CONVERSION over the transparent [rf_upd] tower and poison the async
       [Qed] (claude-notes/completed/regfile-migration.md).  Split with
       [repeat apply conj] and discharge every leaf explicitly. *)
    repeat apply conj;
      first [ exact Hc2 | exact Hc8 | exact Hc9
            | apply Hthread; vm_compute; first [reflexivity | discriminate] ].
  Qed.

  (* =================================================================== *)
  (*  THE FUNCTION.                                                       *)
  (* =================================================================== *)
  Lemma wp_sys_pipe_sconf (γa : gname) (γfl γf : gname)
      (fn : fclose_names) (on : option nat) (us : gset Z)
      (m : regfile) (av : nat) (eb : bool) (p : mword 64) (C : iProp Σ)
      (v : mword 64) (pid : mword 32) (V : pprivate) (b : bool)
    : wp_sys_pipe_sconf_body γa γfl γf fn on us m av eb p C v pid V b.
  Proof.
    cbv beta delta [wp_sys_pipe_sconf_body].
    intros pcE ret_tgt Harg Hav.
    (* Every callee's stack bound, discharged HERE: [lia] is unreliable once
       the context is full of bitvectors (durable-notes.md's zify-hook
       gotcha), and each of these is used inside an [iApply] deep in the
       proof. *)
    destruct (sp_bounds av Hav)
      as (Hav8 & Hav10 & Hav24 & Hav52 & Havaa & Havfd & Havfc).
    set (sp0 := m !!! Regidx csp_rs1).
    set (ra0 := m !!! Regidx Rra).
    set (s00 := m !!! Regidx Rs0).
    set (s10 := m !!! Regidx Rs1).
    iIntros "Hcg Hcpu Hextc Hextm #Htext #Hdata Hpc #Hftab #Henv Hpriv Hua Hub
              Hpenv Hfenv Hcont".
    (* [eb = b]: sys_pipe's contract pins push_off level 0, so
       [CpuOwn.cpu_own_eb_agree] gives it.  Used ONLY to align the
       [trap_csrs_ext] / [cpu_claim_ext] transports' [eb]-guard with the
       [b]-spelled per-instruction chain facts.  NOT [subst]ed: [b] is spelled
       by name in every leaf-instruction argument below. *)
    iDestruct (cpu_own_eb_agree with "Hcg Hcpu") as %Hb.
    (* Unfold [kalloc_env] BEFORE destructing it: leaving [iDestruct] to see
       through the definition sends its [IntoExist] search off into the lock
       invariant and it does not come back. *)
    rewrite /kalloc_env.
    iDestruct "Henv" as (γk) "(#Hkmem & #Hkav & #Hpanic)".
    iPoseProof (spi_00 with "Htext") as "Hi00".
    iPoseProof (spi_02 with "Htext") as "Hi02".
    iPoseProof (spi_04 with "Htext") as "Hi04".
    iPoseProof (spi_06 with "Htext") as "Hi06".
    iPoseProof (spi_08 with "Htext") as "Hi08".
    iPoseProof (spi_0a with "Htext") as "Hi0a".
    iPoseProof (spi_0e with "Htext") as "Hi0e".
    iPoseProof (spi_10 with "Htext") as "Hi10".
    iPoseProof (spi_14 with "Htext") as "Hi14".
    iPoseProof (spi_16 with "Htext") as "Hi16".
    iPoseProof (spi_1a with "Htext") as "Hi1a".
    iPoseProof (spi_1e with "Htext") as "Hi1e".
    iPoseProof (spi_22 with "Htext") as "Hi22".
    iPoseProof (spi_26 with "Htext") as "Hi26".
    iPoseProof (spi_28 with "Htext") as "Hi28".
    (* ===== PROLOGUE: 8-slot frame, ra/s0/s1 saves, s0 := entry sp ===== *)
    iApply (wp_caddi16sp_push_s_sconf pcE (mword_of_int 60 : mword 6) m av 8 b
              Hav8 (stk_push_64 sp0) with "Hcg Hpc Hi00").
    iIntros (CID18 Hcr18) "Hcg Hframe Hpc".
    set (R1 := <[Regidx csp_rs1 := regval_into_reg
                  (add_vec (m !!! Regidx csp_rs1)
                     (sign_extend' 64 (caddi16sp_imm (mword_of_int 60 : mword 6))))]> m).
    change (<[Regidx csp_rs1 := regval_into_reg
        (add_vec (m !!! Regidx csp_rs1)
           (sign_extend' 64 (caddi16sp_imm (mword_of_int 60 : mword 6))))]> m) with R1.
    assert (HR1sp : R1 !!! Regidx csp_rs1 = pa_stk sp0 8)
      by (rewrite /R1 upd_eq; apply stk_push_64).
    assert (Hpp02 : add_vec_int (pcE : mword 64) 2 = mword_of_int (KernelSyms.sys_pipe + 0x2))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp02) in "Hpc".
    iEval (rewrite stack_own_slots; cbn [seq]) in "Hframe".
    iDestruct "Hframe" as "(S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & _)".
    iDestruct "S1" as (u1) "Hb1". iDestruct "S2" as (u2) "Hb2".
    iDestruct "S3" as (u3) "Hb3". iDestruct "S4" as (u4) "Hb4".
    iDestruct "S5" as (u5) "Hb5". iDestruct "S6" as (u6) "Hb6".
    iDestruct "S7" as (u7) "Hb7". iDestruct "S8" as (u8) "Hb8".
    assert (Hf1 : add_vec (R1 !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 7 : mword 6) ('b"000"))) = pa_stk sp0 1)
      by (rewrite HR1sp; apply sp_frm1).
    assert (Hf2 : add_vec (R1 !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 6 : mword 6) ('b"000"))) = pa_stk sp0 2)
      by (rewrite HR1sp; apply sp_frm2).
    assert (Hf3 : add_vec (R1 !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000"))) = pa_stk sp0 3)
      by (rewrite HR1sp; apply sp_frm3).
    assert (HR1ra : R1 !!! Regidx Rra = ra0)
      by (rewrite /R1 upd_ne; [reflexivity | vm_compute; discriminate]).
    assert (HR1s0 : R1 !!! Regidx Rs0 = s00)
      by (rewrite /R1 upd_ne; [reflexivity | vm_compute; discriminate]).
    assert (HR1s1 : R1 !!! Regidx Rs1 = s10)
      by (rewrite /R1 upd_ne; [reflexivity | vm_compute; discriminate]).
    (* +0x02 c.sdsp ra,56(sp) *)
    iEval (rewrite -Hf1) in "Hb1".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.sys_pipe + 0x2)) (mword_of_int 7 : mword 6) Rra
              R1 (av - 8)%nat u1 b with "Hcg Hpc Hi02 Hb1").
    iIntros (CID19 Hcr19) "Hcg Hpc Hb1". iEval (rewrite Hf1; rgne; rewrite HR1ra) in "Hb1".
    assert (Hpp04 : add_vec_int (mword_of_int (KernelSyms.sys_pipe + 0x2) : mword 64) 2 = mword_of_int (KernelSyms.sys_pipe + 0x4))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp04) in "Hpc".
    (* +0x04 c.sdsp s0,48(sp) *)
    iEval (rewrite -Hf2) in "Hb2".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.sys_pipe + 0x4)) (mword_of_int 6 : mword 6) Rs0
              R1 (av - 8)%nat u2 b with "Hcg Hpc Hi04 Hb2").
    iIntros (CID20 Hcr20) "Hcg Hpc Hb2". iEval (rewrite Hf2; rgne; rewrite HR1s0) in "Hb2".
    assert (Hpp06 : add_vec_int (mword_of_int (KernelSyms.sys_pipe + 0x4) : mword 64) 2 = mword_of_int (KernelSyms.sys_pipe + 0x6))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp06) in "Hpc".
    (* +0x06 c.sdsp s1,40(sp) *)
    iEval (rewrite -Hf3) in "Hb3".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.sys_pipe + 0x6)) (mword_of_int 5 : mword 6) Rs1
              R1 (av - 8)%nat u3 b with "Hcg Hpc Hi06 Hb3").
    iIntros (CID21 Hcr21) "Hcg Hpc Hb3". iEval (rewrite Hf3; rgne; rewrite HR1s1) in "Hb3".
    assert (Hpp08 : add_vec_int (mword_of_int (KernelSyms.sys_pipe + 0x6) : mword 64) 2 = mword_of_int (KernelSyms.sys_pipe + 0x8))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp08) in "Hpc".
    (* +0x08 c.addi4spn s0,sp,64 -- s0 := the entry sp *)
    iApply (wp_caddi4spn_s_sconf (mword_of_int (KernelSyms.sys_pipe + 0x8))
              (Cregidx (mword_of_int 0)) (mword_of_int 16 : mword 8) Rs0 R1 (av - 8)%nat b
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
              ltac:(rdok)
              with "Hcg Hpc Hi08").
    iIntros (CID22 Hcr22) "Hcg Hpc".
    set (R2 := <[Regidx Rs0 := regval_into_reg
                  (add_vec (R1 !!! Regidx csp_rs1)
                     (sign_extend' 64 (caddi4spn_imm (mword_of_int 16 : mword 8))))]> R1).
    change (<[Regidx Rs0 := regval_into_reg
        (add_vec (R1 !!! Regidx csp_rs1)
           (sign_extend' 64 (caddi4spn_imm (mword_of_int 16 : mword 8))))]> R1) with R2.
    assert (Hpp0a : add_vec_int (mword_of_int (KernelSyms.sys_pipe + 0x8) : mword 64) 2 = mword_of_int (KernelSyms.sys_pipe + 0xa))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0a) in "Hpc".
    assert (HR2s0 : R2 !!! Regidx Rs0 = sp0).
    { rewrite /R2 upd_eq HR1sp. apply stk_fp_64. }
    assert (HR2sp : R2 !!! Regidx csp_rs1 = pa_stk sp0 8)
      by (rewrite /R2 upd_ne; [exact HR1sp | vm_compute; discriminate]).
    (* the residual "everything else is untouched" fact, extended at each step *)
    assert (HthrR2 : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
              r <> Rs0 -> r <> Rs1 -> R2 !!! Regidx r = m !!! Regidx r).
    { intros r Hr N2 N8 N9.
      rewrite /R2 upd_ne; [| congruence]. rewrite /R1 upd_ne; [reflexivity | congruence]. }
    (* ================================================================= *)
    (*  THE EPILOGUE, taken before any branch: every exit reaches +0xda.  *)
    (* ================================================================= *)
    iDestruct (word_pointsto_aligned_p with "Hb8") as %Hal8.
    iDestruct (word_pointsto_split4 with "Hb8") as "[Hlo Hhi]".
    (* BOTH BLOCK CONTINUATIONS MOVE WITH sys_pipe's OWN CROSSING, to the
       literal [true]: every path that reaches them has crossed pipealloc or
       [sp_close2], whose crossings are [true] and carry no chain fact at
       [b = false].  Each also THREADS the complement rather than capturing
       it -- a bundle built at the entry hart cannot transport a hart-indexed
       resource to the arbitrary hart it is later consumed at. *)
    (* [pose], not [set]: EPI is a BRAND NEW continuation, not an abstraction
       of something already sitting in the goal, so [set]'s occurrence search
       over the whole-function goal (by this point dozens of frame/register
       hypotheses wide) buys nothing but pays O(|goal|) anyway.  [pose] adds
       the same transparent local definition without the search. *)
    pose (EPI := (wp_next true p (fun (CIDe : CpuId) =>
      ∀ (mj : regfile) (P' : uptd) (res : mword 64),
        ⌜ mj !!! Regidx csp_rs1 = pa_stk sp0 8
          /\ mj !!! Regidx Ra5 = res
          /\ (forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
                r <> Rs0 -> r <> Rs1 -> mj !!! Regidx r = m !!! Regidx r) ⌝ -∗
        ⌜ uptd_ext (pv_upt V) P' ⌝ -∗
        sie_cap_gpr mj (av - 8)%nat b p -∗
        cpu_own 0%nat eb p C b -∗
        trap_csrs_ext eb -∗
        cpu_claim_ext eb p -∗
        pc_is (mword_of_int (KernelSyms.sys_pipe + 0xda) : mword 64) -∗
        (* fileclose's environment, back from whichever exit this is *)
        (∃ on', fileclose_pipe_env fn on' 0%nat) -∗
        (∃ us', fileclose_fs_env fn us' 0%nat eb p) -∗
        (∃ w5 w6 w7 : mword 64,
           word_pointsto (pa_stk sp0 5) (DfracOwn 1) w5 ∗
           word_pointsto (pa_stk sp0 6) (DfracOwn 1) w6 ∗
           word_pointsto (pa_stk sp0 7) (DfracOwn 1) w7) -∗
        (∃ lo hi : mword 32,
           word4_pointsto (pa_stk sp0 8) (DfracOwn 1) lo ∗
           word4_pointsto (pa_add (pa_stk sp0 8) 4) (DfracOwn 1) hi) -∗
        sys_pipe_post γf p pid (upd_upt V P') res -∗
        WP (Loop : expr riscv_lang)))%I).
    iAssert EPI with "[Hcont Hb1 Hb2 Hb3 Hb4]" as "Hepi".
    { rewrite /EPI.
      iIntros (CIDE HsE mj P' res) "(%Hjsp & %Hja5 & %Hjthr) %Hext Hcg Hcpu Hextc Hextm Hpc Hpenv Hfenv Hrest Hslot8 Hpost".
      iDestruct "Hrest" as (w5 w6 w7) "(Hb5 & Hb6 & Hb7)".
      iDestruct "Hslot8" as (lo hi) "[Hlo Hhi]".
      iDestruct (word_pointsto_join4 _ _ _ _ Hal8 with "Hlo Hhi") as "Hb8".
      iApply (sp_epi (CID0 := CIDE) m mj av res sp0 ra0 s00 s10 u4 w5 w6 w7
                (word_of_words lo hi) p b
                Hav8 eq_refl eq_refl eq_refl eq_refl Hjsp Hja5 Hjthr
                with "Hcg Htext Hpc Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hb7 Hb8").
      iIntros (CID23 Hcr23 mf) "[%Hcsf %Hfa0] Hcg Hpc".
      iDestruct (cpu_own_transport CIDE CID23 0%nat eb p C b ltac:(wp_next_chain)
                   with "Hcpu") as "Hcpu".
      (* [sp_epi] does not mention the complement, so the hop spans only its
         own crossing, from the hart the epilogue was entered on. *)
      iDestruct (trap_csrs_ext_transport CIDE CID23 eb p
                   ltac:(rewrite Hb; wp_next_chain) with "Hextc") as "Hextc".
      iDestruct (cpu_claim_ext_transport CIDE CID23 eb p
                   ltac:(rewrite Hb; wp_next_chain) with "Hextm") as "Hextm".
      iSpecialize ("Hcont" $! CID23 with "[%]"); [wp_next_chain|].
      iApply ("Hcont" $! mf P' with "[%] [%] Hcg Hcpu Hextc Hextm Hpc [Hpost] Hpenv Hfenv");
        [exact Hcsf | exact Hext |].
      by rewrite Hfa0. }
    (* ================================================================= *)
    (*  +0x0a  jal ra,myproc                                             *)
    (* ================================================================= *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.sys_pipe + 0xa)) Rra
              (mword_of_int 2082014 : mword 21) R2 (av - 8)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi0a").
    iIntros (CID24 Hcr24) "Hcg Hpc".
    set (R3 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KernelSyms.sys_pipe + 0xa) : mword 64) 4)]> R2).
    change (<[Regidx Rra := regval_into_reg
        (add_vec_int (mword_of_int (KernelSyms.sys_pipe + 0xa) : mword 64) 4)]> R2) with R3.
    assert (Hjmp : add_vec (mword_of_int (KernelSyms.sys_pipe + 0xa) : mword 64)
                     (sign_extend' 64 (mword_of_int 2082014 : mword 21))
                   = mword_of_int KernelSyms.myproc)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hjmp) in "Hpc".
    assert (HR3ra : R3 !!! Regidx Rra = add_vec_int (mword_of_int (KernelSyms.sys_pipe + 0xa) : mword 64) 4)
      by (rewrite /R3; apply upd_eq).
    iDestruct (cpu_own_transport CID CID24 0%nat eb p C b ltac:(wp_next_chain)
                 with "Hcpu") as "Hcpu".
    iApply (Myproc.wp_myproc_sconf R3 (av - 8)%nat 0%nat eb p C b
              sp_noff0 Hav10 with "Hcg Hcpu Htext Hpc").
    iIntros (CID25 Hcr25 ms P0) "%Hms Hcg Hcpu Hpc %HcsP0".
    destruct HcsP0 as [HcsP0 HP0a0].
    assert (Hpc0e : ret_pc (R3 !!! Regidx Rra) = mword_of_int (KernelSyms.sys_pipe + 0xe))
      by (rewrite HR3ra; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc0e) in "Hpc".
    assert (HP0sp : P0 !!! Regidx csp_rs1 = pa_stk sp0 8).
    { rewrite (callee_saved_lookup HcsP0 csp_rs1 ltac:(vm_compute; reflexivity)).
      rewrite /R3 upd_ne; [exact HR2sp | vm_compute; discriminate]. }
    assert (HP0s0 : P0 !!! Regidx Rs0 = sp0).
    { rewrite (callee_saved_lookup HcsP0 Rs0 ltac:(vm_compute; reflexivity)).
      rewrite /R3 upd_ne; [exact HR2s0 | vm_compute; discriminate]. }
    assert (HthrP0 : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
              r <> Rs0 -> r <> Rs1 -> P0 !!! Regidx r = m !!! Regidx r).
    { intros r Hr N2 N8 N9.
      rewrite (callee_saved_lookup HcsP0 r Hr).
      rewrite /R3 upd_ne; [| regne]. apply HthrR2; assumption. }
    (* +0x0e c.mv s1,a0 -- s1 := p, for the rest of the function *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.sys_pipe + 0xe)) Rs1 Ra0 P0 (av - 8)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi0e").
    iIntros (CID26 Hcr26) "Hcg Hpc".
    set (P1 := <[Regidx Rs1 := regval_into_reg (add_vec zero_reg (rget P0 Ra0))]> P0).
    change (<[Regidx Rs1 := regval_into_reg (add_vec zero_reg (rget P0 Ra0))]> P0) with P1.
    assert (Hpp10 : add_vec_int (mword_of_int (KernelSyms.sys_pipe + 0xe) : mword 64) 2 = mword_of_int (KernelSyms.sys_pipe + 0x10))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp10) in "Hpc".
    assert (HP1s1 : P1 !!! Regidx Rs1 = p).
    { rewrite /P1 upd_eq. rgne. rewrite HP0a0. apply add_vec_zero_l. }
    assert (HP1sp : P1 !!! Regidx csp_rs1 = pa_stk sp0 8)
      by (rewrite /P1 upd_ne; [exact HP0sp | vm_compute; discriminate]).
    assert (HP1s0 : P1 !!! Regidx Rs0 = sp0)
      by (rewrite /P1 upd_ne; [exact HP0s0 | vm_compute; discriminate]).
    assert (HthrP1 : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
              r <> Rs0 -> r <> Rs1 -> P1 !!! Regidx r = m !!! Regidx r).
    { intros r Hr N2 N8 N9. rewrite /P1 upd_ne; [| congruence]. apply HthrP0; assumption. }
    (* +0x10 addi a1,s0,-40 -- a1 := &fdarray *)
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.sys_pipe + 0x10)) Ra1 Rs0
              (mword_of_int 0xfd8 : mword 12) P1 (av - 8)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi10").
    iIntros (CID27 Hcr27) "Hcg Hpc".
    set (P2 := <[Regidx Ra1 := regval_into_reg
                  (add_vec (rget P1 Rs0) (sign_extend' 64 (mword_of_int 0xfd8 : mword 12)))]> P1).
    change (<[Regidx Ra1 := regval_into_reg
        (add_vec (rget P1 Rs0) (sign_extend' 64 (mword_of_int 0xfd8 : mword 12)))]> P1) with P2.
    assert (Hpp14 : add_vec_int (mword_of_int (KernelSyms.sys_pipe + 0x10) : mword 64) 4 = mword_of_int (KernelSyms.sys_pipe + 0x14))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp14) in "Hpc".
    assert (HP2a1 : P2 !!! Regidx Ra1 = pa_stk sp0 5).
    { rewrite /P2 upd_eq. rgne. rewrite HP1s0. apply sp_addr_fdarray. }
    (* +0x14 c.li a0,0 -- the argument index *)
    iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.sys_pipe + 0x14)) Ra0 (mword_of_int 0 : mword 6)
              (mword_of_int (Z.of_nat 0) : mword 64) P2 (av - 8)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc Hi14").
    iIntros (CID28 Hcr28) "Hcg Hpc".
    set (P3 := <[Regidx Ra0 := regval_into_reg (mword_of_int (Z.of_nat 0) : mword 64)]> P2).
    change (<[Regidx Ra0 := regval_into_reg (mword_of_int (Z.of_nat 0) : mword 64)]> P2) with P3.
    assert (Hpp16 : add_vec_int (mword_of_int (KernelSyms.sys_pipe + 0x14) : mword 64) 2 = mword_of_int (KernelSyms.sys_pipe + 0x16))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp16) in "Hpc".
    (* +0x16 jal ra,argaddr *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.sys_pipe + 0x16)) Rra
              (mword_of_int 2085936 : mword 21) P3 (av - 8)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi16").
    iIntros (CID29 Hcr29) "Hcg Hpc".
    set (P4 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KernelSyms.sys_pipe + 0x16) : mword 64) 4)]> P3).
    change (<[Regidx Rra := regval_into_reg
        (add_vec_int (mword_of_int (KernelSyms.sys_pipe + 0x16) : mword 64) 4)]> P3) with P4.
    assert (Hjaa : add_vec (mword_of_int (KernelSyms.sys_pipe + 0x16) : mword 64)
                     (sign_extend' 64 (mword_of_int 2085936 : mword 21))
                   = mword_of_int KernelSyms.argaddr)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hjaa) in "Hpc".
    assert (HP4ra : P4 !!! Regidx Rra = add_vec_int (mword_of_int (KernelSyms.sys_pipe + 0x16) : mword 64) 4)
      by (rewrite /P4; apply upd_eq).
    assert (HP4a0 : P4 !!! Regidx Ra0 = (mword_of_int (Z.of_nat 0) : mword 64)).
    { rewrite /P4 upd_ne; [| vm_compute; discriminate]. rewrite /P3; apply upd_eq. }
    assert (HP4a1 : P4 !!! Regidx Ra1 = pa_stk sp0 5).
    { rewrite /P4 upd_ne; [| vm_compute; discriminate].
      rewrite /P3 upd_ne; [exact HP2a1 | vm_compute; discriminate]. }
    assert (HP4sp : P4 !!! Regidx csp_rs1 = pa_stk sp0 8).
    { rewrite /P4 upd_ne; [| vm_compute; discriminate].
      rewrite /P3 upd_ne; [| vm_compute; discriminate].
      rewrite /P2 upd_ne; [exact HP1sp | vm_compute; discriminate]. }
    assert (HP4s0 : P4 !!! Regidx Rs0 = sp0).
    { rewrite /P4 upd_ne; [| vm_compute; discriminate].
      rewrite /P3 upd_ne; [| vm_compute; discriminate].
      rewrite /P2 upd_ne; [exact HP1s0 | vm_compute; discriminate]. }
    assert (HP4s1 : P4 !!! Regidx Rs1 = p).
    { rewrite /P4 upd_ne; [| vm_compute; discriminate].
      rewrite /P3 upd_ne; [| vm_compute; discriminate].
      rewrite /P2 upd_ne; [exact HP1s1 | vm_compute; discriminate]. }
    assert (HthrP4 : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
              r <> Rs0 -> r <> Rs1 -> P4 !!! Regidx r = m !!! Regidx r).
    { intros r Hr N2 N8 N9.
      assert (N1 : r <> Rra) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      assert (N10 : r <> Ra0) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      assert (N11 : r <> Ra1) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      rewrite /P4 upd_ne; [| congruence].
      rewrite /P3 upd_ne; [| congruence].
      rewrite /P2 upd_ne; [| congruence]. apply HthrP1; assumption. }
    (* the trapframe word argaddr reads, borrowed out of [proc_priv] *)
    iDestruct (proc_priv_tf with "Hpriv") as "(Htfc & Htfp & Hpback)".
    iEval (rewrite -HP4a1) in "Hb5".
    iDestruct (cpu_own_transport CID25 CID29 0%nat eb p C b ltac:(wp_next_chain)
                 with "Hcpu") as "Hcpu".
    iApply (Argaddr.wp_argaddr_sconf P4 (av - 8)%nat 0%nat eb p C 0%nat
              (ud_tfp (pv_upt V)) (pv_tf V) v u5 (DfracOwn (1/4)) b
              sp_arg0 HP4a0 Harg sp_noff0
              Havaa with "Hcg Hcpu Htext Hdata Hpc Htfc Htfp Hb5").
    iIntros (CID30 Hcr30 Q0) "%HcsQ0 Hcg Hcpu Hpc Htfc Htfp Hb5".
    iEval (rewrite HP4a1) in "Hb5".
    iDestruct ("Hpback" with "Htfc Htfp") as "Hpriv".
    assert (Hpc1a : ret_pc (P4 !!! Regidx Rra) = mword_of_int (KernelSyms.sys_pipe + 0x1a))
      by (rewrite HP4ra; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc1a) in "Hpc".
    assert (HQ0sp : Q0 !!! Regidx csp_rs1 = pa_stk sp0 8)
      by (rewrite (callee_saved_lookup HcsQ0 csp_rs1 ltac:(vm_compute; reflexivity)); exact HP4sp).
    assert (HQ0s0 : Q0 !!! Regidx Rs0 = sp0)
      by (rewrite (callee_saved_lookup HcsQ0 Rs0 ltac:(vm_compute; reflexivity)); exact HP4s0).
    assert (HQ0s1 : Q0 !!! Regidx Rs1 = p)
      by (rewrite (callee_saved_lookup HcsQ0 Rs1 ltac:(vm_compute; reflexivity)); exact HP4s1).
    assert (HthrQ0 : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
              r <> Rs0 -> r <> Rs1 -> Q0 !!! Regidx r = m !!! Regidx r).
    { intros r Hr N2 N8 N9.
      rewrite (callee_saved_lookup HcsQ0 r Hr). apply HthrP4; assumption. }
    (* +0x1a addi a1,s0,-56 -- a1 := &wf *)
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.sys_pipe + 0x1a)) Ra1 Rs0
              (mword_of_int 0xfc8 : mword 12) Q0 (av - 8)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi1a").
    iIntros (CID31 Hcr31) "Hcg Hpc".
    set (Q1 := <[Regidx Ra1 := regval_into_reg
                  (add_vec (rget Q0 Rs0) (sign_extend' 64 (mword_of_int 0xfc8 : mword 12)))]> Q0).
    change (<[Regidx Ra1 := regval_into_reg
        (add_vec (rget Q0 Rs0) (sign_extend' 64 (mword_of_int 0xfc8 : mword 12)))]> Q0) with Q1.
    assert (Hpp1e : add_vec_int (mword_of_int (KernelSyms.sys_pipe + 0x1a) : mword 64) 4 = mword_of_int (KernelSyms.sys_pipe + 0x1e))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp1e) in "Hpc".
    assert (HQ1a1 : Q1 !!! Regidx Ra1 = pa_stk sp0 7).
    { rewrite /Q1 upd_eq. rgne. rewrite HQ0s0. apply sp_addr_wf. }
    assert (HQ1s0 : Q1 !!! Regidx Rs0 = sp0)
      by (rewrite /Q1 upd_ne; [exact HQ0s0 | vm_compute; discriminate]).
    (* +0x1e addi a0,s0,-48 -- a0 := &rf *)
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.sys_pipe + 0x1e)) Ra0 Rs0
              (mword_of_int 0xfd0 : mword 12) Q1 (av - 8)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi1e").
    iIntros (CID32 Hcr32) "Hcg Hpc".
    set (Q2 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (rget Q1 Rs0) (sign_extend' 64 (mword_of_int 0xfd0 : mword 12)))]> Q1).
    change (<[Regidx Ra0 := regval_into_reg
        (add_vec (rget Q1 Rs0) (sign_extend' 64 (mword_of_int 0xfd0 : mword 12)))]> Q1) with Q2.
    assert (Hpp22 : add_vec_int (mword_of_int (KernelSyms.sys_pipe + 0x1e) : mword 64) 4 = mword_of_int (KernelSyms.sys_pipe + 0x22))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp22) in "Hpc".
    assert (HQ2a0 : Q2 !!! Regidx Ra0 = pa_stk sp0 6).
    { rewrite /Q2 upd_eq. rgne. rewrite HQ1s0. apply sp_addr_rf. }
    assert (HQ2a1 : Q2 !!! Regidx Ra1 = pa_stk sp0 7)
      by (rewrite /Q2 upd_ne; [exact HQ1a1 | vm_compute; discriminate]).
    (* +0x22 jal ra,pipealloc *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.sys_pipe + 0x22)) Rra
              (mword_of_int 2093008 : mword 21) Q2 (av - 8)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi22").
    iIntros (CID33 Hcr33) "Hcg Hpc".
    set (Q3 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KernelSyms.sys_pipe + 0x22) : mword 64) 4)]> Q2).
    change (<[Regidx Rra := regval_into_reg
        (add_vec_int (mword_of_int (KernelSyms.sys_pipe + 0x22) : mword 64) 4)]> Q2) with Q3.
    assert (Hjpa : add_vec (mword_of_int (KernelSyms.sys_pipe + 0x22) : mword 64)
                     (sign_extend' 64 (mword_of_int 2093008 : mword 21))
                   = mword_of_int KernelSyms.pipealloc)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hjpa) in "Hpc".
    assert (HQ3ra : Q3 !!! Regidx Rra = add_vec_int (mword_of_int (KernelSyms.sys_pipe + 0x22) : mword 64) 4)
      by (rewrite /Q3; apply upd_eq).
    assert (HQ3a0 : Q3 !!! Regidx Ra0 = pa_stk sp0 6)
      by (rewrite /Q3 upd_ne; [exact HQ2a0 | vm_compute; discriminate]).
    assert (HQ3a1 : Q3 !!! Regidx Ra1 = pa_stk sp0 7)
      by (rewrite /Q3 upd_ne; [exact HQ2a1 | vm_compute; discriminate]).
    assert (HQ3sp : Q3 !!! Regidx csp_rs1 = pa_stk sp0 8).
    { rewrite /Q3 upd_ne; [| vm_compute; discriminate].
      rewrite /Q2 upd_ne; [| vm_compute; discriminate].
      rewrite /Q1 upd_ne; [exact HQ0sp | vm_compute; discriminate]. }
    assert (HQ3s0 : Q3 !!! Regidx Rs0 = sp0).
    { rewrite /Q3 upd_ne; [| vm_compute; discriminate].
      rewrite /Q2 upd_ne; [| vm_compute; discriminate].
      rewrite /Q1 upd_ne; [exact HQ0s0 | vm_compute; discriminate]. }
    assert (HQ3s1 : Q3 !!! Regidx Rs1 = p).
    { rewrite /Q3 upd_ne; [| vm_compute; discriminate].
      rewrite /Q2 upd_ne; [| vm_compute; discriminate].
      rewrite /Q1 upd_ne; [exact HQ0s1 | vm_compute; discriminate]. }
    assert (HthrQ3 : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
              r <> Rs0 -> r <> Rs1 -> Q3 !!! Regidx r = m !!! Regidx r).
    { intros r Hr N2 N8 N9.
      assert (N1 : r <> Rra) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      assert (N10 : r <> Ra0) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      assert (N11 : r <> Ra1) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      rewrite /Q3 upd_ne; [| congruence].
      rewrite /Q2 upd_ne; [| congruence].
      rewrite /Q1 upd_ne; [| congruence]. apply HthrQ0; assumption. }
    iEval (rewrite -HQ3a0) in "Hb6". iEval (rewrite -HQ3a1) in "Hb7".
    iDestruct (cpu_own_transport CID30 CID33 0%nat eb p C b ltac:(wp_next_chain)
                 with "Hcpu") as "Hcpu".
    (* neither myproc nor argaddr mentions the complement, so it rode along in
       the frame at the ENTRY hart: ONE WIDE HOP from there.  pipealloc DOES
       take it -- it passes it on to the fileclose calls on its error paths --
       so it goes in beside [cpu_own] and comes back re-indexed. *)
    iDestruct (trap_csrs_ext_transport CID CID33 eb p
                 ltac:(rewrite Hb; wp_next_chain) with "Hextc") as "Hextc".
    iDestruct (cpu_claim_ext_transport CID CID33 eb p
                 ltac:(rewrite Hb; wp_next_chain) with "Hextm") as "Hextm".
    iApply (Pipealloc.wp_pipealloc_sconf γfl γf γa γk
              (mword_of_int (KernelSyms.kmem + 24)) Q3 u6 u7 None 0%nat eb p C (av - 8)%nat b
              Hav24 eq_refl sp_noff0
              with "Hcg Hcpu Hextc Hextm Htext Hdata Hpc Hftab Hkmem Hkav Hpanic Hua Hub Hb6 Hb7").
    iIntros (CID34 Hcr34 W0) "Hcg Hcpu Hextc Hextm Hpc %HcsW0 Hpost".
    assert (Hpc26 : ret_pc (Q3 !!! Regidx Rra) = mword_of_int (KernelSyms.sys_pipe + 0x26))
      by (rewrite HQ3ra; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc26) in "Hpc".
    assert (HW0sp : W0 !!! Regidx csp_rs1 = pa_stk sp0 8)
      by (rewrite (callee_saved_lookup HcsW0 csp_rs1 ltac:(vm_compute; reflexivity)); exact HQ3sp).
    assert (HW0s0 : W0 !!! Regidx Rs0 = sp0)
      by (rewrite (callee_saved_lookup HcsW0 Rs0 ltac:(vm_compute; reflexivity)); exact HQ3s0).
    assert (HW0s1 : W0 !!! Regidx Rs1 = p)
      by (rewrite (callee_saved_lookup HcsW0 Rs1 ltac:(vm_compute; reflexivity)); exact HQ3s1).
    assert (HthrW0 : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
              r <> Rs0 -> r <> Rs1 -> W0 !!! Regidx r = m !!! Regidx r).
    { intros r Hr N2 N8 N9.
      rewrite (callee_saved_lookup HcsW0 r Hr). apply HthrQ3; assumption. }
    (* +0x26 c.li a5,-1 -- the error return, precomputed *)
    iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.sys_pipe + 0x26)) Ra5 (mword_of_int 63 : mword 6)
              (mword_of_int (-1) : mword 64) W0 (av - 8)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc Hi26").
    iIntros (CID35 Hcr35) "Hcg Hpc".
    set (W1 := <[Regidx Ra5 := regval_into_reg (mword_of_int (-1) : mword 64)]> W0).
    change (<[Regidx Ra5 := regval_into_reg (mword_of_int (-1) : mword 64)]> W0) with W1.
    assert (Hpp28 : add_vec_int (mword_of_int (KernelSyms.sys_pipe + 0x26) : mword 64) 2 = mword_of_int (KernelSyms.sys_pipe + 0x28))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp28) in "Hpc".
    assert (HW1a5 : W1 !!! Regidx Ra5 = (mword_of_int (-1) : mword 64))
      by (rewrite /W1; apply upd_eq).
    assert (HW1a0 : W1 !!! Regidx Ra0 = W0 !!! Regidx Ra0)
      by (rewrite /W1 upd_ne; [reflexivity | vm_compute; discriminate]).
    assert (HW1sp : W1 !!! Regidx csp_rs1 = pa_stk sp0 8)
      by (rewrite /W1 upd_ne; [exact HW0sp | vm_compute; discriminate]).
    assert (HW1s0 : W1 !!! Regidx Rs0 = sp0)
      by (rewrite /W1 upd_ne; [exact HW0s0 | vm_compute; discriminate]).
    assert (HW1s1 : W1 !!! Regidx Rs1 = p)
      by (rewrite /W1 upd_ne; [exact HW0s1 | vm_compute; discriminate]).
    assert (HthrW1 : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
              r <> Rs0 -> r <> Rs1 -> W1 !!! Regidx r = m !!! Regidx r).
    { intros r Hr N2 N8 N9.
      assert (N15 : r <> Ra5) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      rewrite /W1 upd_ne; [| congruence]. apply HthrW0; assumption. }
    (* +0x28 blt a0,x0 -- did pipealloc fail? *)
    rewrite /pipealloc_post. iDestruct "Hpost" as "[Hfail | Hsucc]".
    { (* ============ pipealloc failed: straight to the epilogue ========= *)
      iDestruct "Hfail" as "(%Hr & _ & Hua & Hub & Hcells)".
      iDestruct "Hcells" as (w6 w7) "[Hb6 Hb7]".
      iEval (rewrite HQ3a0) in "Hb6". iEval (rewrite HQ3a1) in "Hb7".
      assert (HW1a0' : W1 !!! Regidx Ra0 = (mword_of_int (-1) : mword 64))
        by (rewrite HW1a0; exact Hr).
      iApply (wp_blt_x0_taken_s_sconf (mword_of_int (KernelSyms.sys_pipe + 0x28))
                (mword_of_int 178 : mword 13) Ra0 W1 (av - 8)%nat b
                ltac:(vm_compute; discriminate)
                ltac:(rgne; rewrite HW1a0'; vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi28").
      iApply bi.later_intro. iIntros (CID36 Hcr36) "Hcg Hpc".
      assert (Hbt : add_vec (mword_of_int (KernelSyms.sys_pipe + 0x28) : mword 64)
                      (sign_extend' 64 (mword_of_int 178 : mword 13))
                    = mword_of_int (KernelSyms.sys_pipe + 0xda))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hbt) in "Hpc".
      iDestruct (cpu_own_transport CID34 CID36 0%nat eb p C b ltac:(wp_next_chain)
                   with "Hcpu") as "Hcpu".
      iDestruct (trap_csrs_ext_transport CID34 CID36 eb p
                   ltac:(rewrite Hb; wp_next_chain) with "Hextc") as "Hextc".
      iDestruct (cpu_claim_ext_transport CID34 CID36 eb p
                   ltac:(rewrite Hb; wp_next_chain) with "Hextm") as "Hextm".
      iSpecialize ("Hepi" $! CID36 with "[%]"); [wp_next_chain|].
      iApply ("Hepi" $! W1 (pv_upt V) (mword_of_int (-1) : mword 64)
                with "[%] [%] Hcg Hcpu Hextc Hextm Hpc [Hpenv] [Hfenv] [Hb5 Hb6 Hb7] [Hlo Hhi] [Hpriv Hua Hub]").
      { split; [exact HW1sp|]. split; [exact HW1a5 | exact HthrW1]. }
      { apply uptd_ext_refl. }
      { by iExists on. }
      { by iExists us. }
      { iExists v, w6, w7. iFrame "Hb5 Hb6 Hb7". }
      { iExists (word_lo u8), (word_hi u8). iFrame "Hlo Hhi". }
      (* NB: split the post's two components BEFORE framing.  [iFrame] on the
         whole [sys_pipe_post] searches inside [proc_priv] for a place to put
         an [fd_slot] -- 16 ofile slots and a 4096-byte trapframe page deep --
         and does not come back. *)
      rewrite /sys_pipe_post sp_upd_upt_id.
      iSplitR "Hua Hub"; [| iSplitL "Hua"; [iExact "Hua" | iExact "Hub"]].
      iLeft. iSplitR; [done|]. iExact "Hpriv". }
    (* ============ pipealloc succeeded ================================= *)
    iDestruct "Hsucc" as "(%Hr0 & _ & Hpipe)".
    iDestruct "Hpipe" as (pi k0 k1 Cf0 Cf1)
      "(%Hklt & %Hpf0 & %Hpf1 & Hb6 & Hb7 & Href0 & Href1)".
    destruct Hklt as [Hk0lt Hk1lt].
    (* Nothing about the pipe appears from here on, and that is the point:
       each end rides INSIDE its file's [FileInv.file_ref] as the payload
       [pipe_file] pins, so installing a descriptor installs the reference to
       the pipe with it.  (Before the payload link this proof had to DROP the
       two ends here -- affine, so it typechecked, and it meant sys_pipe's
       descriptors were not connected to the pipe in the model.) *)
    assert (HW1a0' : W1 !!! Regidx Ra0 = (zero_reg : mword 64))
      by (rewrite HW1a0; exact Hr0).
    iApply (wp_blt_x0_fall_s_sconf (mword_of_int (KernelSyms.sys_pipe + 0x28))
              (mword_of_int 178 : mword 13) Ra0 W1 (av - 8)%nat b
              ltac:(vm_compute; discriminate)
              ltac:(rgne; rewrite HW1a0'; vm_compute; reflexivity)
              with "Hcg Hpc Hi28").
    iIntros (CID37 Hcr37) "Hcg Hpc".
    assert (Hpp2c : add_vec_int (mword_of_int (KernelSyms.sys_pipe + 0x28) : mword 64) 4 = mword_of_int (KernelSyms.sys_pipe + 0x2c))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp2c) in "Hpc".
    (* the two [struct file *] cells, back in frame-slot terms *)
    iEval (rewrite HQ3a0) in "Hb6". iEval (rewrite HQ3a1) in "Hb7".
    iPoseProof (spi_2c with "Htext") as "Hi2c".
    iPoseProof (spi_30 with "Htext") as "Hi30".
    iPoseProof (spi_34 with "Htext") as "Hi34".
    iPoseProof (spi_38 with "Htext") as "Hi38".
    iPoseProof (spi_3c with "Htext") as "Hi3c".
    (* The +0xc8 tail's pc arithmetic, established ONCE.  Left inline as
       [ltac:(...)] arguments of the [iApply] they would be re-elaborated
       inside a goal the size of a whole-function WP. *)
    assert (Hcc4a : ret_pc (add_vec_int (mword_of_int (KernelSyms.sys_pipe + 0xcc) : mword 64) 4)
                    = mword_of_int (KernelSyms.sys_pipe + 0xd0)) by (apply bv_eq; vm_compute; reflexivity).
    assert (Hcc4b : ret_pc (add_vec_int (mword_of_int (KernelSyms.sys_pipe + 0xd4) : mword 64) 4)
                    = mword_of_int (KernelSyms.sys_pipe + 0xd8)) by (apply bv_eq; vm_compute; reflexivity).
    assert (Hcc4c : add_vec_int (mword_of_int (KernelSyms.sys_pipe + 0xc8) : mword 64) 4
                    = mword_of_int (KernelSyms.sys_pipe + 0xcc)) by (apply bv_eq; vm_compute; reflexivity).
    assert (Hcc4d : add_vec_int (mword_of_int (KernelSyms.sys_pipe + 0xd0) : mword 64) 4
                    = mword_of_int (KernelSyms.sys_pipe + 0xd4)) by (apply bv_eq; vm_compute; reflexivity).
    assert (Hcc4e : add_vec_int (mword_of_int (KernelSyms.sys_pipe + 0xd8) : mword 64) 2
                    = mword_of_int (KernelSyms.sys_pipe + 0xda)) by (apply bv_eq; vm_compute; reflexivity).
    assert (Hcc4f : add_vec (mword_of_int (KernelSyms.sys_pipe + 0xcc) : mword 64)
                      (sign_extend' 64 (mword_of_int 2092038 : mword 21))
                    = mword_of_int KernelSyms.fileclose)
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Hcc4g : add_vec (mword_of_int (KernelSyms.sys_pipe + 0xd4) : mword 64)
                      (sign_extend' 64 (mword_of_int 2092030 : mword 21))
                    = mword_of_int KernelSyms.fileclose)
      by (apply bv_eq; vm_compute; reflexivity).
    (* ...and the +0xbc descriptor-null block's *)
    assert (Hnb8a : add_vec_int (mword_of_int (KernelSyms.sys_pipe + 0xbc) : mword 64) 2
                    = mword_of_int (KernelSyms.sys_pipe + 0xbe)) by (apply bv_eq; vm_compute; reflexivity).
    assert (Hnb8b : add_vec_int (mword_of_int (KernelSyms.sys_pipe + 0xbe) : mword 64) 4
                    = mword_of_int (KernelSyms.sys_pipe + 0xc2)) by (apply bv_eq; vm_compute; reflexivity).
    assert (Hnb8c : add_vec_int (mword_of_int (KernelSyms.sys_pipe + 0xc2) : mword 64) 2
                    = mword_of_int (KernelSyms.sys_pipe + 0xc4)) by (apply bv_eq; vm_compute; reflexivity).
    assert (Hnb8d : add_vec_int (mword_of_int (KernelSyms.sys_pipe + 0xc4) : mword 64) 4
                    = mword_of_int (KernelSyms.sys_pipe + 0xc8)) by (apply bv_eq; vm_compute; reflexivity).
    (* the two shared tails' instruction facts, needed by every arm *)
    iPoseProof (spi_c8 with "Htext") as "Hic8".
    iPoseProof (spi_cc with "Htext") as "Hicc".
    iPoseProof (spi_d0 with "Htext") as "Hid0".
    iPoseProof (spi_d4 with "Htext") as "Hid4".
    iPoseProof (spi_d8 with "Htext") as "Hid8".
    (* +0x2c sw a5,-60(s0) -- fd0 = -1 *)
    assert (Hfd0a : add_vec (rget W1 Rs0) (sign_extend' 64 (mword_of_int 0xfc4 : mword 12))
                    = pa_add (pa_stk sp0 8) 4) by (rgne; rewrite HW1s0; apply sp_addr_fd0).
    iEval (rewrite -Hfd0a) in "Hhi".
    iApply (wp_sw_s_sconf (mword_of_int (KernelSyms.sys_pipe + 0x2c)) Ra5 Rs0
              (mword_of_int 0xfc4 : mword 12) W1 (av - 8)%nat (word_hi u8) b
              with "Hcg Hpc Hi2c Hhi").
    iIntros (CID38 Hcr38) "Hcg Hpc Hhi". iEval (rewrite Hfd0a; rgne) in "Hhi".
    assert (Hpp30 : add_vec_int (mword_of_int (KernelSyms.sys_pipe + 0x2c) : mword 64) 4 = mword_of_int (KernelSyms.sys_pipe + 0x30))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp30) in "Hpc".
    (* +0x30 ld a0,-48(s0) -- a0 := rf *)
    assert (Hrfa : add_vec (rget W1 Rs0) (sign_extend' 64 (mword_of_int 0xfd0 : mword 12))
                   = pa_stk sp0 6) by (rgne; rewrite HW1s0; apply sp_addr_rf).
    iEval (rewrite -Hrfa) in "Hb6".
    iApply (wp_ld_s_sconf (mword_of_int (KernelSyms.sys_pipe + 0x30)) Ra0 Rs0
              (mword_of_int 0xfd0 : mword 12) W1 (av - 8)%nat (fnode k0) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi30 Hb6").
    iIntros (CID39 Hcr39) "Hcg Hpc Hb6". iEval (rewrite Hrfa) in "Hb6".
    set (X0 := <[Regidx Ra0 := regval_into_reg (fnode k0)]> W1).
    change (<[Regidx Ra0 := regval_into_reg (fnode k0)]> W1) with X0.
    assert (Hpp34 : add_vec_int (mword_of_int (KernelSyms.sys_pipe + 0x30) : mword 64) 4 = mword_of_int (KernelSyms.sys_pipe + 0x34))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp34) in "Hpc".
    (* +0x34 jal ra,fdalloc *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.sys_pipe + 0x34)) Rra
              (mword_of_int 2094814 : mword 21) X0 (av - 8)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi34").
    iIntros (CID40 Hcr40) "Hcg Hpc".
    set (X1 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KernelSyms.sys_pipe + 0x34) : mword 64) 4)]> X0).
    change (<[Regidx Rra := regval_into_reg
        (add_vec_int (mword_of_int (KernelSyms.sys_pipe + 0x34) : mword 64) 4)]> X0) with X1.
    assert (Hjfd1 : add_vec (mword_of_int (KernelSyms.sys_pipe + 0x34) : mword 64)
                      (sign_extend' 64 (mword_of_int 2094814 : mword 21))
                    = mword_of_int KernelSyms.fdalloc)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hjfd1) in "Hpc".
    assert (HX1ra : X1 !!! Regidx Rra = add_vec_int (mword_of_int (KernelSyms.sys_pipe + 0x34) : mword 64) 4)
      by (rewrite /X1; apply upd_eq).
    assert (HX1a0 : X1 !!! Regidx Ra0 = fnode k0).
    { rewrite /X1 upd_ne; [| vm_compute; discriminate]. rewrite /X0; apply upd_eq. }
    assert (HX1sp : X1 !!! Regidx csp_rs1 = pa_stk sp0 8).
    { rewrite /X1 upd_ne; [| vm_compute; discriminate].
      rewrite /X0 upd_ne; [exact HW1sp | vm_compute; discriminate]. }
    assert (HX1s0 : X1 !!! Regidx Rs0 = sp0).
    { rewrite /X1 upd_ne; [| vm_compute; discriminate].
      rewrite /X0 upd_ne; [exact HW1s0 | vm_compute; discriminate]. }
    assert (HX1s1 : X1 !!! Regidx Rs1 = p).
    { rewrite /X1 upd_ne; [| vm_compute; discriminate].
      rewrite /X0 upd_ne; [exact HW1s1 | vm_compute; discriminate]. }
    assert (HthrX1 : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
              r <> Rs0 -> r <> Rs1 -> X1 !!! Regidx r = m !!! Regidx r).
    { intros r Hr N2 N8 N9.
      assert (N1 : r <> Rra) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      assert (N10 : r <> Ra0) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      rewrite /X1 upd_ne; [| congruence].
      rewrite /X0 upd_ne; [| congruence]. apply HthrW1; assumption. }
    iDestruct (cpu_own_transport CID34 CID40 0%nat eb p C b ltac:(wp_next_chain)
                 with "Hcpu") as "Hcpu".
    (* fdalloc now takes the block SPLIT at the fd table and no reference of
       its own; [Href0] stays here and settles the deficit on the way out. *)
    iDestruct (proc_priv_split with "Hpriv") as "[Hcore Hof]".
    rewrite -(proc_ofiles_owe_empty γf p (pv_ofile V)).
    iApply (Fdalloc.wp_fdalloc_sconf γf k0 ∅ X1 (av - 8)%nat 0%nat eb p C pid V b
              HX1a0 Hk0lt sp_noff0 Havfd
              with "Hcg Hcpu Htext Hdata Hpc Hcore Hof").
    iIntros (CID41 Hcr41 Y0) "%HcsY0 Hcg Hcpu Hpc Hcore Hpost1".
    assert (Hpc38 : ret_pc (X1 !!! Regidx Rra) = mword_of_int (KernelSyms.sys_pipe + 0x38))
      by (rewrite HX1ra; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc38) in "Hpc".
    assert (HY0sp : Y0 !!! Regidx csp_rs1 = pa_stk sp0 8)
      by (rewrite (callee_saved_lookup HcsY0 csp_rs1 ltac:(vm_compute; reflexivity)); exact HX1sp).
    assert (HY0s0 : Y0 !!! Regidx Rs0 = sp0)
      by (rewrite (callee_saved_lookup HcsY0 Rs0 ltac:(vm_compute; reflexivity)); exact HX1s0).
    assert (HY0s1 : Y0 !!! Regidx Rs1 = p)
      by (rewrite (callee_saved_lookup HcsY0 Rs1 ltac:(vm_compute; reflexivity)); exact HX1s1).
    assert (HthrY0 : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
              r <> Rs0 -> r <> Rs1 -> Y0 !!! Regidx r = m !!! Regidx r).
    { intros r Hr N2 N8 N9.
      rewrite (callee_saved_lookup HcsY0 r Hr). apply HthrX1; assumption. }
    (* +0x38 sw a0,-60(s0) -- fd0 = fdalloc(rf) *)
    assert (Hfd0b : add_vec (rget Y0 Rs0) (sign_extend' 64 (mword_of_int 0xfc4 : mword 12))
                    = pa_add (pa_stk sp0 8) 4) by (rgne; rewrite HY0s0; apply sp_addr_fd0).
    iEval (rewrite -Hfd0b) in "Hhi".
    iApply (wp_sw_s_sconf (mword_of_int (KernelSyms.sys_pipe + 0x38)) Ra0 Rs0
              (mword_of_int 0xfc4 : mword 12) Y0 (av - 8)%nat
              (trunc32 (W1 !!! Regidx Ra5)) b with "Hcg Hpc Hi38 Hhi").
    iIntros (CID42 Hcr42) "Hcg Hpc Hhi". iEval (rewrite Hfd0b; rgne) in "Hhi".
    assert (Hpp3c : add_vec_int (mword_of_int (KernelSyms.sys_pipe + 0x38) : mword 64) 4 = mword_of_int (KernelSyms.sys_pipe + 0x3c))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp3c) in "Hpc".
    (* +0x3c blt a0,x0 -- did the first fdalloc fail? *)
    rewrite /fdalloc_post. iDestruct "Hpost1" as "[Hf1 | Hs1]".
    { (* ===== the ftable had no free descriptor: close both, return -1 ===== *)
      iDestruct "Hf1" as "([%Hr1 %Hnone] & Hof)".
      iDestruct (proc_priv_join with "Hcore Hof") as "Hpriv".
      iApply (wp_blt_x0_taken_s_sconf (mword_of_int (KernelSyms.sys_pipe + 0x3c))
                (mword_of_int 140 : mword 13) Ra0 Y0 (av - 8)%nat b
                ltac:(vm_compute; discriminate)
                ltac:(rgne; rewrite Hr1; vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi3c").
      iApply bi.later_intro. iIntros (CID43 Hcr43) "Hcg Hpc".
      assert (Hbt1 : add_vec (mword_of_int (KernelSyms.sys_pipe + 0x3c) : mword 64)
                       (sign_extend' 64 (mword_of_int 140 : mword 13))
                     = mword_of_int (KernelSyms.sys_pipe + 0xc8))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hbt1) in "Hpc".
      iDestruct (cpu_own_transport CID41 CID43 0%nat eb p C b ltac:(wp_next_chain)
                   with "Hcpu") as "Hcpu".
      (* fdalloc does not mention the complement: hop from [CID34], the hart
         pipealloc handed it back on. *)
      iDestruct (trap_csrs_ext_transport CID34 CID43 eb p
                   ltac:(rewrite Hb; wp_next_chain) with "Hextc") as "Hextc".
      iDestruct (cpu_claim_ext_transport CID34 CID43 eb p
                   ltac:(rewrite Hb; wp_next_chain) with "Hextm") as "Hextm".
      iApply (sp_close2 (CID0 := CID43)  γfl γf fn on us Y0 (av - 8)%nat eb p C sp0 k0 k1 1%Qp 1%Qp Cf0 Cf1
                (KernelSyms.sys_pipe + 0xc8) (KernelSyms.sys_pipe + 0xcc) (KernelSyms.sys_pipe + 0xd0) (KernelSyms.sys_pipe + 0xd4) (KernelSyms.sys_pipe + 0xd8) (KernelSyms.sys_pipe + 0xda)
                (mword_of_int 2092038 : mword 21) (mword_of_int 2092030 : mword 21) b
                Havfc HY0s0 Hcc4a Hcc4b Hcc4c Hcc4d Hcc4e Hcc4f Hcc4g
                with "Hcg Hcpu Hextc Hextm Htext Hpc Hftab Hpanic Hic8 Hicc Hid0 Hid4 Hid8 Hb6 Hb7 Href0 Href1 Hpenv Hfenv").
      iIntros (CID44 Hcr44 Mr) "[%Hmrcs %Hmra5] Hcg Hcpu Hextc Hextm Hpc Hb6 Hb7 Hua Hub Hpenv Hfenv".
      iSpecialize ("Hepi" $! CID44 with "[%]"); [wp_next_chain|].
      iApply ("Hepi" $! Mr (pv_upt V) (mword_of_int (-1) : mword 64)
                with "[%] [%] Hcg Hcpu Hextc Hextm Hpc [Hpenv] Hfenv [Hb5 Hb6 Hb7] [Hlo Hhi] [Hpriv Hua Hub]").
      { split; [rewrite (Hmrcs csp_rs1 ltac:(vm_compute; reflexivity)); exact HY0sp|].
        split; [exact Hmra5|].
        intros r Hr N2 N8 N9. rewrite (Hmrcs r Hr). apply HthrY0; assumption. }
      { apply uptd_ext_refl. }
      { iExact "Hpenv". }
      { iExists v, (fnode k0), (fnode k1). iFrame "Hb5 Hb6 Hb7". }
      { iExists (word_lo u8), (trunc32 (Y0 !!! Regidx Ra0)). iFrame "Hlo Hhi". }
      (* NB: split the post's two components BEFORE framing.  [iFrame] on the
         whole [sys_pipe_post] searches inside [proc_priv] for a place to put
         an [fd_slot] -- 16 ofile slots and a 4096-byte trapframe page deep --
         and does not come back. *)
      rewrite /sys_pipe_post sp_upd_upt_id.
      iSplitR "Hua Hub"; [| iSplitL "Hua"; [iExact "Hua" | iExact "Hub"]].
      iLeft. iSplitR; [done|]. iExact "Hpriv". }
    (* ===== the first descriptor is taken ===== *)
    iDestruct "Hs1" as (fd0 l0) "([%Hr1 %Hfr0] & Hof & Hu0)".
    pose proof (fd_frees_head_lt (pv_ofile V) fd0 l0 Hfr0) as Hfd0lt.
    iDestruct (proc_ofiles_owe_len with "Hof") as %Hlen1.
    rewrite upd_ofile_length in Hlen1.
    assert (Hfd0N : (fd0 < NOFILE)%nat) by (rewrite -Hlen1; exact Hfd0lt).
    (* SETTLE: the descriptor fdalloc filled owes a payload, and this is the
       reference pipealloc handed us for that end. *)
    iDestruct (proc_priv_settle γf p pid V fd0 k0 1%Qp Cf0 Hfd0N Hlen1 Hk0lt
                 with "Hcore Hof Href0") as "Hpriv".
    destruct (sp_fd_range fd0 Hfd0N) as [Hfd0b16 Hfd0b31].
    iApply (wp_blt_x0_fall_s_sconf (mword_of_int (KernelSyms.sys_pipe + 0x3c))
              (mword_of_int 140 : mword 13) Ra0 Y0 (av - 8)%nat b
              ltac:(vm_compute; discriminate)
              ltac:(rgne; rewrite Hr1; apply sp_fd_nonneg; exact Hfd0b31)
              with "Hcg Hpc Hi3c").
    iIntros (CID45 Hcr45) "Hcg Hpc".
    assert (Hpp40 : add_vec_int (mword_of_int (KernelSyms.sys_pipe + 0x3c) : mword 64) 4 = mword_of_int (KernelSyms.sys_pipe + 0x40))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp40) in "Hpc".
    iEval (rewrite Hr1) in "Hhi".
    iPoseProof (spi_40 with "Htext") as "Hi40".
    iPoseProof (spi_44 with "Htext") as "Hi44".
    iPoseProof (spi_48 with "Htext") as "Hi48".
    iPoseProof (spi_4c with "Htext") as "Hi4c".
    (* +0x40 ld a0,-56(s0) -- a0 := wf *)
    assert (Hwfa : add_vec (rget Y0 Rs0) (sign_extend' 64 (mword_of_int 0xfc8 : mword 12))
                   = pa_stk sp0 7) by (rgne; rewrite HY0s0; apply sp_addr_wf).
    iEval (rewrite -Hwfa) in "Hb7".
    iApply (wp_ld_s_sconf (mword_of_int (KernelSyms.sys_pipe + 0x40)) Ra0 Rs0
              (mword_of_int 0xfc8 : mword 12) Y0 (av - 8)%nat (fnode k1) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi40 Hb7").
    iIntros (CID46 Hcr46) "Hcg Hpc Hb7". iEval (rewrite Hwfa) in "Hb7".
    set (Z0 := <[Regidx Ra0 := regval_into_reg (fnode k1)]> Y0).
    change (<[Regidx Ra0 := regval_into_reg (fnode k1)]> Y0) with Z0.
    assert (Hpp44 : add_vec_int (mword_of_int (KernelSyms.sys_pipe + 0x40) : mword 64) 4 = mword_of_int (KernelSyms.sys_pipe + 0x44))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp44) in "Hpc".
    (* +0x44 jal ra,fdalloc *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.sys_pipe + 0x44)) Rra
              (mword_of_int 2094798 : mword 21) Z0 (av - 8)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi44").
    iIntros (CID47 Hcr47) "Hcg Hpc".
    set (Z1 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KernelSyms.sys_pipe + 0x44) : mword 64) 4)]> Z0).
    change (<[Regidx Rra := regval_into_reg
        (add_vec_int (mword_of_int (KernelSyms.sys_pipe + 0x44) : mword 64) 4)]> Z0) with Z1.
    assert (Hjfd2 : add_vec (mword_of_int (KernelSyms.sys_pipe + 0x44) : mword 64)
                      (sign_extend' 64 (mword_of_int 2094798 : mword 21))
                    = mword_of_int KernelSyms.fdalloc)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hjfd2) in "Hpc".
    assert (HZ1ra : Z1 !!! Regidx Rra = add_vec_int (mword_of_int (KernelSyms.sys_pipe + 0x44) : mword 64) 4)
      by (rewrite /Z1; apply upd_eq).
    assert (HZ1a0 : Z1 !!! Regidx Ra0 = fnode k1).
    { rewrite /Z1 upd_ne; [| vm_compute; discriminate]. rewrite /Z0; apply upd_eq. }
    assert (HZ1sp : Z1 !!! Regidx csp_rs1 = pa_stk sp0 8).
    { rewrite /Z1 upd_ne; [| vm_compute; discriminate].
      rewrite /Z0 upd_ne; [exact HY0sp | vm_compute; discriminate]. }
    assert (HZ1s0 : Z1 !!! Regidx Rs0 = sp0).
    { rewrite /Z1 upd_ne; [| vm_compute; discriminate].
      rewrite /Z0 upd_ne; [exact HY0s0 | vm_compute; discriminate]. }
    assert (HZ1s1 : Z1 !!! Regidx Rs1 = p).
    { rewrite /Z1 upd_ne; [| vm_compute; discriminate].
      rewrite /Z0 upd_ne; [exact HY0s1 | vm_compute; discriminate]. }
    assert (HthrZ1 : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
              r <> Rs0 -> r <> Rs1 -> Z1 !!! Regidx r = m !!! Regidx r).
    { intros r Hr N2 N8 N9.
      assert (N1 : r <> Rra) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      assert (N10 : r <> Ra0) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      rewrite /Z1 upd_ne; [| congruence].
      rewrite /Z0 upd_ne; [| congruence]. apply HthrY0; assumption. }
    iDestruct (cpu_own_transport CID41 CID47 0%nat eb p C b ltac:(wp_next_chain)
                 with "Hcpu") as "Hcpu".
    iDestruct (proc_priv_split with "Hpriv") as "[Hcore Hof]".
    rewrite -(proc_ofiles_owe_empty γf p (pv_ofile (upd_ofile V fd0 (fnode k0)))).
    iApply (Fdalloc.wp_fdalloc_sconf γf k1 ∅ Z1 (av - 8)%nat 0%nat eb p C pid
              (upd_ofile V fd0 (fnode k0)) b
              HZ1a0 Hk1lt sp_noff0 Havfd
              with "Hcg Hcpu Htext Hdata Hpc Hcore Hof").
    iIntros (CID48 Hcr48 U0) "%HcsU0 Hcg Hcpu Hpc Hcore Hpost2".
    assert (Hpc48 : ret_pc (Z1 !!! Regidx Rra) = mword_of_int (KernelSyms.sys_pipe + 0x48))
      by (rewrite HZ1ra; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc48) in "Hpc".
    assert (HU0sp : U0 !!! Regidx csp_rs1 = pa_stk sp0 8)
      by (rewrite (callee_saved_lookup HcsU0 csp_rs1 ltac:(vm_compute; reflexivity)); exact HZ1sp).
    assert (HU0s0 : U0 !!! Regidx Rs0 = sp0)
      by (rewrite (callee_saved_lookup HcsU0 Rs0 ltac:(vm_compute; reflexivity)); exact HZ1s0).
    assert (HU0s1 : U0 !!! Regidx Rs1 = p)
      by (rewrite (callee_saved_lookup HcsU0 Rs1 ltac:(vm_compute; reflexivity)); exact HZ1s1).
    assert (HthrU0 : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
              r <> Rs0 -> r <> Rs1 -> U0 !!! Regidx r = m !!! Regidx r).
    { intros r Hr N2 N8 N9.
      rewrite (callee_saved_lookup HcsU0 r Hr). apply HthrZ1; assumption. }
    (* +0x48 sw a0,-64(s0) -- fd1 = fdalloc(wf) *)
    assert (Hfd1a : add_vec (rget U0 Rs0) (sign_extend' 64 (mword_of_int 0xfc0 : mword 12))
                    = pa_stk sp0 8) by (rgne; rewrite HU0s0; apply sp_addr_fd1).
    iEval (rewrite -Hfd1a) in "Hlo".
    iApply (wp_sw_s_sconf (mword_of_int (KernelSyms.sys_pipe + 0x48)) Ra0 Rs0
              (mword_of_int 0xfc0 : mword 12) U0 (av - 8)%nat (word_lo u8) b
              with "Hcg Hpc Hi48 Hlo").
    iIntros (CID49 Hcr49) "Hcg Hpc Hlo". iEval (rewrite Hfd1a; rgne) in "Hlo".
    assert (Hpp4c : add_vec_int (mword_of_int (KernelSyms.sys_pipe + 0x48) : mword 64) 4 = mword_of_int (KernelSyms.sys_pipe + 0x4c))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp4c) in "Hpc".
    (* +0x4c blt a0,x0 -- did the second fdalloc fail? *)
    assert (Hfree0 : pv_ofile V !! fd0 = Some (zero_reg : mword 64))
      by exact (fd_frees_head (pv_ofile V) fd0 l0 Hfr0).
    assert (Hlk0 : pv_ofile (upd_ofile V fd0 (fnode k0)) !! fd0 = Some (fnode k0)).
    { cbn [upd_ofile pv_ofile]. by apply list_lookup_insert. }
    rewrite /fdalloc_post. iDestruct "Hpost2" as "[Hf2 | Hs2]".
    { (* ===== no second descriptor: undo the first, close both ===== *)
      iDestruct "Hf2" as "([%Hr2 %Hnone2] & Hof)".
      iDestruct (proc_priv_join with "Hcore Hof") as "Hpriv".
      iApply (wp_blt_x0_taken_s_sconf (mword_of_int (KernelSyms.sys_pipe + 0x4c))
                (mword_of_int 104 : mword 13) Ra0 U0 (av - 8)%nat b
                ltac:(vm_compute; discriminate)
                ltac:(rgne; rewrite Hr2; vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi4c").
      iApply bi.later_intro. iIntros (CID50 Hcr50) "Hcg Hpc".
      assert (Hbt2 : add_vec (mword_of_int (KernelSyms.sys_pipe + 0x4c) : mword 64)
                       (sign_extend' 64 (mword_of_int 104 : mword 13))
                     = mword_of_int (KernelSyms.sys_pipe + 0xb4))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hbt2) in "Hpc".
      iPoseProof (spi_b4 with "Htext") as "Hib4".
      iPoseProof (spi_b8 with "Htext") as "Hib8".
      iPoseProof (spi_bc with "Htext") as "Hibc".
      iPoseProof (spi_be with "Htext") as "Hibe".
      iPoseProof (spi_c2 with "Htext") as "Hic2".
      iPoseProof (spi_c4 with "Htext") as "Hic4".
      (* +0xb4 lw a5,-60(s0) -- reload fd0 *)
      assert (Hfd0c : add_vec (rget U0 Rs0) (sign_extend' 64 (mword_of_int 0xfc4 : mword 12))
                      = pa_add (pa_stk sp0 8) 4) by (rgne; rewrite HU0s0; apply sp_addr_fd0).
      iEval (rewrite -Hfd0c) in "Hhi".
      iApply (wp_lw_s_sconf (mword_of_int (KernelSyms.sys_pipe + 0xb4)) Ra5 Rs0
                (mword_of_int 0xfc4 : mword 12) U0 (av - 8)%nat
                (trunc32 (mword_of_int (Z.of_nat fd0) : mword 64)) b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hib4 Hhi").
      iIntros (CID51 Hcr51) "Hcg Hpc Hhi". iEval (rewrite Hfd0c) in "Hhi".
      set (F1 := <[Regidx Ra5 := regval_into_reg
                    (sign_extend' 64 (trunc32 (mword_of_int (Z.of_nat fd0) : mword 64)))]> U0).
      change (<[Regidx Ra5 := regval_into_reg
          (sign_extend' 64 (trunc32 (mword_of_int (Z.of_nat fd0) : mword 64)))]> U0) with F1.
      assert (Hppb8 : add_vec_int (mword_of_int (KernelSyms.sys_pipe + 0xb4) : mword 64) 4 = mword_of_int (KernelSyms.sys_pipe + 0xb8))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hppb8) in "Hpc".
      assert (HF1a5 : F1 !!! Regidx Ra5 = (mword_of_int (Z.of_nat fd0) : mword 64)).
      { rewrite /F1 upd_eq. apply sp_sext_trunc. exact Hfd0b31. }
      assert (HF1s1 : F1 !!! Regidx Rs1 = p)
        by (rewrite /F1 upd_ne; [exact HU0s1 | vm_compute; discriminate]).
      assert (HF1s0 : F1 !!! Regidx Rs0 = sp0)
        by (rewrite /F1 upd_ne; [exact HU0s0 | vm_compute; discriminate]).
      assert (HF1sp : F1 !!! Regidx csp_rs1 = pa_stk sp0 8)
        by (rewrite /F1 upd_ne; [exact HU0sp | vm_compute; discriminate]).
      assert (HthrF1 : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
                r <> Rs0 -> r <> Rs1 -> F1 !!! Regidx r = m !!! Regidx r).
      { intros r Hr N2 N8 N9.
        assert (N15 : r <> Ra5) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
        rewrite /F1 upd_ne; [| congruence]. apply HthrU0; assumption. }
      (* +0xb8 blt a5,x0 -- fd0 is non-negative, so the store DOES run *)
      iApply (wp_blt_x0_fall_s_sconf (mword_of_int (KernelSyms.sys_pipe + 0xb8))
                (mword_of_int 16 : mword 13) Ra5 F1 (av - 8)%nat b
                ltac:(vm_compute; discriminate)
                ltac:(rgne; rewrite HF1a5; apply sp_fd_nonneg; exact Hfd0b31)
                with "Hcg Hpc Hib8").
      iIntros (CID52 Hcr52) "Hcg Hpc".
      assert (Hppbc : add_vec_int (mword_of_int (KernelSyms.sys_pipe + 0xb8) : mword 64) 4 = mword_of_int (KernelSyms.sys_pipe + 0xbc))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hppbc) in "Hpc".
      (* borrow descriptor fd0 back out of the process *)
      iDestruct (proc_priv_ofile γf p pid (upd_ofile V fd0 (fnode k0)) fd0 (fnode k0) Hlk0
                   with "Hpriv") as "[Hslot Hback]".
      iDestruct "Hslot" as "[Hcell [[%Hz _] | Href]]";
        [by exfalso; apply (fnode_ne_zero k0 Hk0lt)|].
      iDestruct "Href" as (k0' q0' C0') "[[%Hfv0 %Hk0'lt] Href0]".
      (* +0xbc .. +0xc4: p->ofile[fd0] = 0 *)
      iApply (sp_ofile_null (CID0 := CID52) F1 (av - 8)%nat p fd0 Ra5 Rs1
                (KernelSyms.sys_pipe + 0xbc) (KernelSyms.sys_pipe + 0xbe) (KernelSyms.sys_pipe + 0xc2) (KernelSyms.sys_pipe + 0xc4) (KernelSyms.sys_pipe + 0xc8) (fnode k0) b
                Hfd0b16 (or_introl (conj eq_refl eq_refl)) HF1a5 HF1s1 Hnb8a Hnb8b Hnb8c Hnb8d
                with "Hcg Hpc Hibc Hibe Hic2 Hic4 Hcell").
      iIntros (CID53 Hcr53 F2) "%HF2thr Hcg Hpc Hcell".
      assert (HF2s0 : F2 !!! Regidx Rs0 = sp0)
        by (rewrite (HF2thr Rs0 ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)); exact HF1s0).
      iDestruct ("Hback" $! (zero_reg : mword 64) with "[Hcell Hu0]") as "Hpriv".
      { rewrite /ofile_slot. iFrame "Hcell". iLeft. by iFrame "Hu0". }
      rewrite (sp_ofile_restore V fd0 (fnode k0) Hfree0).
      iEval (rewrite Hfv0) in "Hb6".
      (* +0xc8: fileclose(rf); fileclose(wf); a5 = -1 *)
      iDestruct (cpu_own_transport CID48 CID53 0%nat eb p C b ltac:(wp_next_chain)
                   with "Hcpu") as "Hcpu".
      (* neither fdalloc mentions the complement: still the hop from [CID34]. *)
      iDestruct (trap_csrs_ext_transport CID34 CID53 eb p
                   ltac:(rewrite Hb; wp_next_chain) with "Hextc") as "Hextc".
      iDestruct (cpu_claim_ext_transport CID34 CID53 eb p
                   ltac:(rewrite Hb; wp_next_chain) with "Hextm") as "Hextm".
      iApply (sp_close2 (CID0 := CID53)  γfl γf fn on us F2 (av - 8)%nat eb p C sp0 k0' k1 q0' 1%Qp C0' Cf1
                (KernelSyms.sys_pipe + 0xc8) (KernelSyms.sys_pipe + 0xcc) (KernelSyms.sys_pipe + 0xd0) (KernelSyms.sys_pipe + 0xd4) (KernelSyms.sys_pipe + 0xd8) (KernelSyms.sys_pipe + 0xda)
                (mword_of_int 2092038 : mword 21) (mword_of_int 2092030 : mword 21) b
                Havfc HF2s0 Hcc4a Hcc4b Hcc4c Hcc4d Hcc4e Hcc4f Hcc4g
                with "Hcg Hcpu Hextc Hextm Htext Hpc Hftab Hpanic Hic8 Hicc Hid0 Hid4 Hid8 Hb6 Hb7 Href0 Href1 Hpenv Hfenv").
      iIntros (CID54 Hcr54 Mr) "[%Hmrcs %Hmra5] Hcg Hcpu Hextc Hextm Hpc Hb6 Hb7 Hua Hub Hpenv Hfenv".
      iSpecialize ("Hepi" $! CID54 with "[%]"); [wp_next_chain|].
      iApply ("Hepi" $! Mr (pv_upt V) (mword_of_int (-1) : mword 64)
                with "[%] [%] Hcg Hcpu Hextc Hextm Hpc [Hpenv] Hfenv [Hb5 Hb6 Hb7] [Hlo Hhi] [Hpriv Hua Hub]").
      { split.
        { rewrite (Hmrcs csp_rs1 ltac:(vm_compute; reflexivity)).
          rewrite (HF2thr csp_rs1 ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)). exact HF1sp. }
        split; [exact Hmra5|].
        intros r Hr N2 N8 N9. rewrite (Hmrcs r Hr).
        assert (N15 : r <> Ra5) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
        rewrite (HF2thr r N15 N15). apply HthrF1; assumption. }
      { apply uptd_ext_refl. }
      { iExact "Hpenv". }
      { iExists v, (fnode k0'), (fnode k1). iFrame "Hb5 Hb6 Hb7". }
      { iExists (trunc32 (U0 !!! Regidx Ra0)), (trunc32 (mword_of_int (Z.of_nat fd0) : mword 64)).
        iFrame "Hlo Hhi". }
      (* NB: split the post's two components BEFORE framing.  [iFrame] on the
         whole [sys_pipe_post] searches inside [proc_priv] for a place to put
         an [fd_slot] -- 16 ofile slots and a 4096-byte trapframe page deep --
         and does not come back. *)
      rewrite /sys_pipe_post sp_upd_upt_id.
      iSplitR "Hua Hub"; [| iSplitL "Hua"; [iExact "Hua" | iExact "Hub"]].
      iLeft. iSplitR; [done|]. iExact "Hpriv". }
    (* ===== both descriptors are taken: copy them out ===== *)
    iDestruct "Hs2" as (fd1 l1) "([%Hr2 %Hfr1] & Hof & Hu1)".
    (* the second descriptor is a DIFFERENT one: [fd_frees] only names free
       slots, and fd0 is no longer free. *)
    assert (Hfr1' : fd_frees (pv_ofile V) = fd0 :: fd1 :: l1).
    { rewrite Hfr0. f_equal. rewrite -(fd_frees_insert (pv_ofile V) fd0 l0 (fnode k0)
                                        (fnode_ne_zero k0 Hk0lt) Hfr0).
      exact Hfr1. }
    assert (Hfree1 : pv_ofile (upd_ofile V fd0 (fnode k0)) !! fd1 = Some (zero_reg : mword 64))
      by exact (fd_frees_head _ fd1 l1 Hfr1).
    assert (Hne01 : fd0 <> fd1).
    { intro He. rewrite -He in Hfree1. rewrite Hlk0 in Hfree1.
      assert (Hc : (fnode k0 : mword 64) = (zero_reg : mword 64)) by congruence.
      exact (fnode_ne_zero k0 Hk0lt Hc). }
    assert (Hfree1V : pv_ofile V !! fd1 = Some (zero_reg : mword 64)).
    { cbn [upd_ofile pv_ofile] in Hfree1.
      by rewrite list_lookup_insert_ne in Hfree1; [| congruence]. }
    assert (Hfd1lt : (fd1 < length (pv_ofile V))%nat).
    { apply lookup_lt_is_Some_1. by exists (zero_reg : mword 64). }
    iDestruct (proc_ofiles_owe_len with "Hof") as %Hlen2.
    rewrite !upd_ofile_length in Hlen2.
    assert (Hfd1N : (fd1 < NOFILE)%nat) by (rewrite -Hlen2; exact Hfd1lt).
    assert (Hlen2' : length (pv_ofile (upd_ofile V fd0 (fnode k0))) = NOFILE)
      by (rewrite upd_ofile_length; exact Hlen2).
    iDestruct (proc_priv_settle γf p pid (upd_ofile V fd0 (fnode k0)) fd1 k1
                 1%Qp Cf1 Hfd1N Hlen2' Hk1lt
                 with "Hcore Hof Href1") as "Hpriv".
    destruct (sp_fd_range fd1 Hfd1N) as [Hfd1b16 Hfd1b31].
    iApply (wp_blt_x0_fall_s_sconf (mword_of_int (KernelSyms.sys_pipe + 0x4c))
              (mword_of_int 104 : mword 13) Ra0 U0 (av - 8)%nat b
              ltac:(vm_compute; discriminate)
              ltac:(rgne; rewrite Hr2; apply sp_fd_nonneg; exact Hfd1b31)
              with "Hcg Hpc Hi4c").
    iIntros (CID55 Hcr55) "Hcg Hpc".
    assert (Hpp50 : add_vec_int (mword_of_int (KernelSyms.sys_pipe + 0x4c) : mword 64) 4 = mword_of_int (KernelSyms.sys_pipe + 0x50))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp50) in "Hpc".
    iEval (rewrite Hr2) in "Hlo".
    (* ================================================================= *)
    (*  +0x50 .. +0x7c -- copyout(&fd0), copyout(&fd1), return 0.         *)
    (* ================================================================= *)
    iPoseProof (spi_50 with "Htext") as "Hi50".
    iPoseProof (spi_52 with "Htext") as "Hi52".
    iPoseProof (spi_56 with "Htext") as "Hi56".
    iPoseProof (spi_5a with "Htext") as "Hi5a".
    iPoseProof (spi_5c with "Htext") as "Hi5c".
    iPoseProof (spi_5e with "Htext") as "Hi5e".
    iPoseProof (spi_62 with "Htext") as "Hi62".
    iPoseProof (spi_66 with "Htext") as "Hi66".
    iPoseProof (spi_68 with "Htext") as "Hi68".
    iPoseProof (spi_6c with "Htext") as "Hi6c".
    iPoseProof (spi_70 with "Htext") as "Hi70".
    iPoseProof (spi_72 with "Htext") as "Hi72".
    iPoseProof (spi_74 with "Htext") as "Hi74".
    iPoseProof (spi_76 with "Htext") as "Hi76".
    iPoseProof (spi_7a with "Htext") as "Hi7a".
    iPoseProof (spi_7c with "Htext") as "Hi7c".
    (* the +0x80 tail's pc arithmetic and instruction facts *)
    iPoseProof (spi_80 with "Htext") as "Hi80".
    iPoseProof (spi_84 with "Htext") as "Hi84".
    iPoseProof (spi_86 with "Htext") as "Hi86".
    iPoseProof (spi_8a with "Htext") as "Hi8a".
    iPoseProof (spi_8c with "Htext") as "Hi8c".
    iPoseProof (spi_90 with "Htext") as "Hi90".
    iPoseProof (spi_94 with "Htext") as "Hi94".
    iPoseProof (spi_96 with "Htext") as "Hi96".
    iPoseProof (spi_9a with "Htext") as "Hi9a".
    iPoseProof (spi_9c with "Htext") as "Hi9c".
    iPoseProof (spi_a0 with "Htext") as "Hia0".
    iPoseProof (spi_a4 with "Htext") as "Hia4".
    iPoseProof (spi_a8 with "Htext") as "Hia8".
    iPoseProof (spi_ac with "Htext") as "Hiac".
    iPoseProof (spi_b0 with "Htext") as "Hib0".
    iPoseProof (spi_b2 with "Htext") as "Hib2".
    assert (Hn80a : add_vec_int (mword_of_int (KernelSyms.sys_pipe + 0x84) : mword 64) 2
                    = mword_of_int (KernelSyms.sys_pipe + 0x86)) by (apply bv_eq; vm_compute; reflexivity).
    assert (Hn80b : add_vec_int (mword_of_int (KernelSyms.sys_pipe + 0x86) : mword 64) 4
                    = mword_of_int (KernelSyms.sys_pipe + 0x8a)) by (apply bv_eq; vm_compute; reflexivity).
    assert (Hn80c : add_vec_int (mword_of_int (KernelSyms.sys_pipe + 0x8a) : mword 64) 2
                    = mword_of_int (KernelSyms.sys_pipe + 0x8c)) by (apply bv_eq; vm_compute; reflexivity).
    assert (Hn80d : add_vec_int (mword_of_int (KernelSyms.sys_pipe + 0x8c) : mword 64) 4
                    = mword_of_int (KernelSyms.sys_pipe + 0x90)) by (apply bv_eq; vm_compute; reflexivity).
    assert (Hn90a : add_vec_int (mword_of_int (KernelSyms.sys_pipe + 0x94) : mword 64) 2
                    = mword_of_int (KernelSyms.sys_pipe + 0x96)) by (apply bv_eq; vm_compute; reflexivity).
    assert (Hn90b : add_vec_int (mword_of_int (KernelSyms.sys_pipe + 0x96) : mword 64) 4
                    = mword_of_int (KernelSyms.sys_pipe + 0x9a)) by (apply bv_eq; vm_compute; reflexivity).
    assert (Hn90c : add_vec_int (mword_of_int (KernelSyms.sys_pipe + 0x9a) : mword 64) 2
                    = mword_of_int (KernelSyms.sys_pipe + 0x9c)) by (apply bv_eq; vm_compute; reflexivity).
    assert (Hn90d : add_vec_int (mword_of_int (KernelSyms.sys_pipe + 0x9c) : mword 64) 4
                    = mword_of_int (KernelSyms.sys_pipe + 0xa0)) by (apply bv_eq; vm_compute; reflexivity).
    assert (Hc9ca : ret_pc (add_vec_int (mword_of_int (KernelSyms.sys_pipe + 0xa4) : mword 64) 4)
                    = mword_of_int (KernelSyms.sys_pipe + 0xa8)) by (apply bv_eq; vm_compute; reflexivity).
    assert (Hc9cb : ret_pc (add_vec_int (mword_of_int (KernelSyms.sys_pipe + 0xac) : mword 64) 4)
                    = mword_of_int (KernelSyms.sys_pipe + 0xb0)) by (apply bv_eq; vm_compute; reflexivity).
    assert (Hc9cc : add_vec_int (mword_of_int (KernelSyms.sys_pipe + 0xa0) : mword 64) 4
                    = mword_of_int (KernelSyms.sys_pipe + 0xa4)) by (apply bv_eq; vm_compute; reflexivity).
    assert (Hc9cd : add_vec_int (mword_of_int (KernelSyms.sys_pipe + 0xa8) : mword 64) 4
                    = mword_of_int (KernelSyms.sys_pipe + 0xac)) by (apply bv_eq; vm_compute; reflexivity).
    assert (Hc9ce : add_vec_int (mword_of_int (KernelSyms.sys_pipe + 0xb0) : mword 64) 2
                    = mword_of_int (KernelSyms.sys_pipe + 0xb2)) by (apply bv_eq; vm_compute; reflexivity).
    assert (Hc9cf : add_vec (mword_of_int (KernelSyms.sys_pipe + 0xa4) : mword 64)
                      (sign_extend' 64 (mword_of_int 2092078 : mword 21))
                    = mword_of_int KernelSyms.fileclose)
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Hc9cg : add_vec (mword_of_int (KernelSyms.sys_pipe + 0xac) : mword 64)
                      (sign_extend' 64 (mword_of_int 2092070 : mword 21))
                    = mword_of_int KernelSyms.fileclose)
      by (apply bv_eq; vm_compute; reflexivity).
    (* two [kalloc_env] bundles, one per copyout, built from the persistent
       pieces rather than re-derived *)
    iAssert (kalloc_env γa None) with "[]" as "Henva".
    { rewrite /kalloc_env. iExists γk. iFrame "Hkmem Hkav Hpanic". }
    iAssert (kalloc_env γa None) with "[]" as "Henvb".
    { rewrite /kalloc_env. iExists γk. iFrame "Hkmem Hkav Hpanic". }
    (* the pure descriptor facts the tail needs *)
    assert (Hlk0' : pv_ofile (upd_ofile (upd_ofile V fd0 (fnode k0)) fd1 (fnode k1)) !! fd0
                    = Some (fnode k0)).
    { cbn [upd_ofile pv_ofile].
      rewrite list_lookup_insert_ne; [| congruence].
      by apply list_lookup_insert. }
    assert (Hlk1' : pv_ofile (upd_ofile (upd_ofile (upd_ofile V fd0 (fnode k0)) fd1 (fnode k1))
                                fd0 (zero_reg : mword 64)) !! fd1 = Some (fnode k1)).
    { cbn [upd_ofile pv_ofile].
      rewrite list_lookup_insert_ne; [| congruence].
      apply list_lookup_insert. by rewrite length_insert. }
    (* the copy accessor, taken ONCE and closed once *)
    iDestruct (proc_priv_sz_bound with "Hpriv") as %Hszb.
    iDestruct (proc_priv_copy with "Hpriv") as "(Hszc & Hptc & Hpt & Hpback)".
    (* +0x50 c.li a4,4 -- the length argument, now in a4 *)
    iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.sys_pipe + 0x50)) Ra4 (mword_of_int 4 : mword 6)
              (mword_of_int (Z.of_nat 4) : mword 64) U0 (av - 8)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc Hi50").
    iIntros (CID56 Hcr56) "Hcg Hpc".
    set (A1 := <[Regidx Ra4 := regval_into_reg (mword_of_int (Z.of_nat 4) : mword 64)]> U0).
    change (<[Regidx Ra4 := regval_into_reg (mword_of_int (Z.of_nat 4) : mword 64)]> U0) with A1.
    assert (Hpp52 : add_vec_int (mword_of_int (KernelSyms.sys_pipe + 0x50) : mword 64) 2 = mword_of_int (KernelSyms.sys_pipe + 0x52))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp52) in "Hpc".
    (* +0x52 addi a3,s0,-60 -- a3 := &fd0, the SOURCE, now in a3 *)
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.sys_pipe + 0x52)) Ra3 Rs0
              (mword_of_int 0xfc4 : mword 12) A1 (av - 8)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi52").
    iIntros (CID57 Hcr57) "Hcg Hpc".
    set (A2 := <[Regidx Ra3 := regval_into_reg
                  (add_vec (rget A1 Rs0) (sign_extend' 64 (mword_of_int 0xfc4 : mword 12)))]> A1).
    change (<[Regidx Ra3 := regval_into_reg
        (add_vec (rget A1 Rs0) (sign_extend' 64 (mword_of_int 0xfc4 : mword 12)))]> A1) with A2.
    assert (Hpp56 : add_vec_int (mword_of_int (KernelSyms.sys_pipe + 0x52) : mword 64) 4 = mword_of_int (KernelSyms.sys_pipe + 0x56))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp56) in "Hpc".
    assert (HA1s0 : A1 !!! Regidx Rs0 = sp0)
      by (rewrite /A1 upd_ne; [exact HU0s0 | vm_compute; discriminate]).
    assert (HA2a3 : A2 !!! Regidx Ra3 = pa_add (pa_stk sp0 8) 4).
    { rewrite /A2 upd_eq. rgne. rewrite HA1s0. apply sp_addr_fd0. }
    assert (HA2s0 : A2 !!! Regidx Rs0 = sp0)
      by (rewrite /A2 upd_ne; [exact HA1s0 | vm_compute; discriminate]).
    (* +0x56 ld a2,-40(s0) -- a2 := fdarray, the DESTINATION, now in a2 *)
    assert (Hfda : add_vec (rget A2 Rs0) (sign_extend' 64 (mword_of_int 0xfd8 : mword 12))
                   = pa_stk sp0 5) by (rgne; rewrite HA2s0; apply sp_addr_fdarray).
    iEval (rewrite -Hfda) in "Hb5".
    iApply (wp_ld_s_sconf (mword_of_int (KernelSyms.sys_pipe + 0x56)) Ra2 Rs0
              (mword_of_int 0xfd8 : mword 12) A2 (av - 8)%nat v b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi56 Hb5").
    iIntros (CID58 Hcr58) "Hcg Hpc Hb5". iEval (rewrite Hfda) in "Hb5".
    set (A3 := <[Regidx Ra2 := regval_into_reg v]> A2).
    change (<[Regidx Ra2 := regval_into_reg v]> A2) with A3.
    assert (Hpp5a : add_vec_int (mword_of_int (KernelSyms.sys_pipe + 0x56) : mword 64) 4 = mword_of_int (KernelSyms.sys_pipe + 0x5a))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp5a) in "Hpc".
    assert (HA3s1 : A3 !!! Regidx Rs1 = p).
    { rewrite /A3 upd_ne; [| vm_compute; discriminate].
      rewrite /A2 upd_ne; [| vm_compute; discriminate].
      rewrite /A1 upd_ne; [exact HU0s1 | vm_compute; discriminate]. }
    (* +0x5a c.ld a1,72(s1) -- a1 := p->sz, copyout's NEW [psz] argument.
       The two cells are read here and nowhere else: the contract itself no
       longer mentions [p_sz] / [p_pagetable] (SpecCopyout.v's header), so
       they stay with the caller across both calls. *)
    assert (Hsza : add_vec (rget A3 Rs1) (sign_extend' 64 (mword_of_int 72 : mword 12))
                   = p_sz p) by (rgne; rewrite HA3s1; reflexivity).
    iEval (rewrite -Hsza) in "Hszc".
    iApply (wp_cld_s_sconf (mword_of_int (KernelSyms.sys_pipe + 0x5a)) Ra1 Rs1
              (mword_of_int 72 : mword 12) A3 (av - 8)%nat
              (pv_sz (upd_ofile (upd_ofile V fd0 (fnode k0)) fd1 (fnode k1))) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi5a Hszc").
    iIntros (CID59 Hcr59) "Hcg Hpc Hszc". iEval (rewrite Hsza) in "Hszc".
    set (A4 := <[Regidx Ra1 := regval_into_reg
                  (pv_sz (upd_ofile (upd_ofile V fd0 (fnode k0)) fd1 (fnode k1)))]> A3).
    change (<[Regidx Ra1 := regval_into_reg
        (pv_sz (upd_ofile (upd_ofile V fd0 (fnode k0)) fd1 (fnode k1)))]> A3) with A4.
    assert (Hpp5c : add_vec_int (mword_of_int (KernelSyms.sys_pipe + 0x5a) : mword 64) 2 = mword_of_int (KernelSyms.sys_pipe + 0x5c))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp5c) in "Hpc".
    assert (HA4s1 : A4 !!! Regidx Rs1 = p)
      by (rewrite /A4 upd_ne; [exact HA3s1 | vm_compute; discriminate]).
    (* +0x5c c.ld a0,80(s1) -- a0 := p->pagetable *)
    assert (Hpta : add_vec (rget A4 Rs1) (sign_extend' 64 (mword_of_int 80 : mword 12))
                   = p_pagetable p) by (rgne; rewrite HA4s1; reflexivity).
    iEval (rewrite -Hpta) in "Hptc".
    iApply (wp_cld_s_sconf (mword_of_int (KernelSyms.sys_pipe + 0x5c)) Ra0 Rs1
              (mword_of_int 80 : mword 12) A4 (av - 8)%nat
              (page_base (ud_root (pv_upt (upd_ofile (upd_ofile V fd0 (fnode k0)) fd1 (fnode k1))))) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi5c Hptc").
    iIntros (CID59b Hcr59b) "Hcg Hpc Hptc". iEval (rewrite Hpta) in "Hptc".
    set (A5 := <[Regidx Ra0 := regval_into_reg
                  (page_base (ud_root (pv_upt (upd_ofile (upd_ofile V fd0 (fnode k0))
                                                 fd1 (fnode k1)))))]> A4).
    change (<[Regidx Ra0 := regval_into_reg
        (page_base (ud_root (pv_upt (upd_ofile (upd_ofile V fd0 (fnode k0))
                                       fd1 (fnode k1)))))]> A4) with A5.
    assert (Hpp5e : add_vec_int (mword_of_int (KernelSyms.sys_pipe + 0x5c) : mword 64) 2 = mword_of_int (KernelSyms.sys_pipe + 0x5e))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp5e) in "Hpc".
    (* +0x5e jal ra,copyout *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.sys_pipe + 0x5e)) Rra
              (mword_of_int 2080964 : mword 21) A5 (av - 8)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi5e").
    iIntros (CID60 Hcr60) "Hcg Hpc".
    set (A6 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KernelSyms.sys_pipe + 0x5e) : mword 64) 4)]> A5).
    change (<[Regidx Rra := regval_into_reg
        (add_vec_int (mword_of_int (KernelSyms.sys_pipe + 0x5e) : mword 64) 4)]> A5) with A6.
    assert (Hjco1 : add_vec (mword_of_int (KernelSyms.sys_pipe + 0x5e) : mword 64)
                      (sign_extend' 64 (mword_of_int 2080964 : mword 21))
                    = mword_of_int KernelSyms.copyout)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hjco1) in "Hpc".
    assert (HA6ra : A6 !!! Regidx Rra = add_vec_int (mword_of_int (KernelSyms.sys_pipe + 0x5e) : mword 64) 4)
      by (rewrite /A6; apply upd_eq).
    assert (HA6a0 : A6 !!! Regidx Ra0
                    = page_base (ud_root (pv_upt (upd_ofile (upd_ofile V fd0 (fnode k0))
                                                    fd1 (fnode k1))))).
    { rewrite /A6 upd_ne; [| vm_compute; discriminate]. rewrite /A5; apply upd_eq. }
    assert (HA6a1 : A6 !!! Regidx Ra1
                    = pv_sz (upd_ofile (upd_ofile V fd0 (fnode k0)) fd1 (fnode k1))).
    { rewrite /A6 upd_ne; [| vm_compute; discriminate].
      rewrite /A5 upd_ne; [| vm_compute; discriminate].
      rewrite /A4; apply upd_eq. }
    assert (HA6a3 : A6 !!! Regidx Ra3 = pa_add (pa_stk sp0 8) 4).
    { rewrite /A6 upd_ne; [| vm_compute; discriminate].
      rewrite /A5 upd_ne; [| vm_compute; discriminate].
      rewrite /A4 upd_ne; [| vm_compute; discriminate].
      rewrite /A3 upd_ne; [exact HA2a3 | vm_compute; discriminate]. }
    assert (HA6a4 : A6 !!! Regidx Ra4 = (mword_of_int (Z.of_nat 4) : mword 64)).
    { rewrite /A6 upd_ne; [| vm_compute; discriminate].
      rewrite /A5 upd_ne; [| vm_compute; discriminate].
      rewrite /A4 upd_ne; [| vm_compute; discriminate].
      rewrite /A3 upd_ne; [| vm_compute; discriminate].
      rewrite /A2 upd_ne; [| vm_compute; discriminate].
      rewrite /A1; apply upd_eq. }
    assert (HA6sp : A6 !!! Regidx csp_rs1 = pa_stk sp0 8).
    { rewrite /A6 upd_ne; [| vm_compute; discriminate].
      rewrite /A5 upd_ne; [| vm_compute; discriminate].
      rewrite /A4 upd_ne; [| vm_compute; discriminate].
      rewrite /A3 upd_ne; [| vm_compute; discriminate].
      rewrite /A2 upd_ne; [| vm_compute; discriminate].
      rewrite /A1 upd_ne; [exact HU0sp | vm_compute; discriminate]. }
    assert (HA6s0 : A6 !!! Regidx Rs0 = sp0).
    { rewrite /A6 upd_ne; [| vm_compute; discriminate].
      rewrite /A5 upd_ne; [| vm_compute; discriminate].
      rewrite /A4 upd_ne; [| vm_compute; discriminate].
      rewrite /A3 upd_ne; [| vm_compute; discriminate].
      rewrite /A2 upd_ne; [exact HA1s0 | vm_compute; discriminate]. }
    assert (HA6s1 : A6 !!! Regidx Rs1 = p).
    { rewrite /A6 upd_ne; [| vm_compute; discriminate].
      rewrite /A5 upd_ne; [| vm_compute; discriminate].
      rewrite /A4 upd_ne; [exact HA3s1 | vm_compute; discriminate]. }
    assert (HthrA6 : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
              r <> Rs0 -> r <> Rs1 -> A6 !!! Regidx r = m !!! Regidx r).
    { intros r Hr N2 N8 N9.
      assert (N1 : r <> Rra) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      assert (N10 : r <> Ra0) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      assert (N11 : r <> Ra1) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      assert (N12 : r <> Ra2) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      assert (N13 : r <> Ra3) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      assert (N14 : r <> Ra4) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      rewrite /A6 upd_ne; [| congruence].
      rewrite /A5 upd_ne; [| congruence].
      rewrite /A4 upd_ne; [| congruence].
      rewrite /A3 upd_ne; [| congruence].
      rewrite /A2 upd_ne; [| congruence].
      rewrite /A1 upd_ne; [| congruence]. apply HthrU0; assumption. }
    (* the [int fd0] cell AS copyout's four-byte source buffer *)
    iDestruct "Hhi" as "[%Halhi Hbufhi]".
    iEval (rewrite -HA6a3) in "Hbufhi".
    iDestruct (cpu_own_transport CID48 CID60 0%nat eb p C b ltac:(wp_next_chain)
                 with "Hcpu") as "Hcpu".
    iApply (Copyout.wp_copyout_sconf γa A6
              (pv_upt (upd_ofile (upd_ofile V fd0 (fnode k0)) fd1 (fnode k1)))
              (pv_sz (upd_ofile (upd_ofile V fd0 (fnode k0)) fd1 (fnode k1))) 4%nat
              (fun j => nth_byte (trunc32 (mword_of_int (Z.of_nat fd0) : mword 64)) j)
              (av - 8)%nat 0%nat eb p C b
              Hav52 HA6a0 HA6a1 HA6a4 sp_len4 Hszb sp_n0
              with "Hcg Hcpu Htext Hpc Hpt Henva Hbufhi").
    iIntros (CID61 Hcr61 B0 Pa) "Hcg Hcpu Hpc Hpt Hbufhi %HcsB0 %Hext1 %Hret1".
    iEval (rewrite HA6a3) in "Hbufhi".
    iDestruct (word4_pointsto_intro _ _ _ Halhi with "Hbufhi") as "Hhi".
    assert (Hpc62 : ret_pc (A6 !!! Regidx Rra) = mword_of_int (KernelSyms.sys_pipe + 0x62))
      by (rewrite HA6ra; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc62) in "Hpc".
    assert (HB0sp : B0 !!! Regidx csp_rs1 = pa_stk sp0 8)
      by (rewrite (callee_saved_lookup HcsB0 csp_rs1 ltac:(vm_compute; reflexivity)); exact HA6sp).
    assert (HB0s0 : B0 !!! Regidx Rs0 = sp0)
      by (rewrite (callee_saved_lookup HcsB0 Rs0 ltac:(vm_compute; reflexivity)); exact HA6s0).
    assert (HB0s1 : B0 !!! Regidx Rs1 = p)
      by (rewrite (callee_saved_lookup HcsB0 Rs1 ltac:(vm_compute; reflexivity)); exact HA6s1).
    assert (HthrB0 : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
              r <> Rs0 -> r <> Rs1 -> B0 !!! Regidx r = m !!! Regidx r).
    { intros r Hr N2 N8 N9.
      rewrite (callee_saved_lookup HcsB0 r Hr). apply HthrA6; assumption. }
    (* ================================================================= *)
    (*  THE COPYOUT-FAILURE TAIL at +0x80, as an [iAssert]ed continuation *)
    (*  -- BOTH copyouts branch to it, so it is built once, before the    *)
    (*  first test, over the page-table descriptor the arm arrives with.  *)
    (* ================================================================= *)
    (* [pose], not [set] -- same reasoning as EPI above, and by here the
       context is wider still (every frame slot and register fact from the
       whole prologue plus both fdallocs is live), which is exactly why this
       one [set] alone was 9+ seconds: an occurrence search over a goal that
       never contains a T7C occurrence to find. *)
    pose (T7C := (wp_next true p (fun (CIDt : CpuId) =>
      ∀ (Mt : regfile) (P' : uptd),
        ⌜ Mt !!! Regidx csp_rs1 = pa_stk sp0 8
          /\ Mt !!! Regidx Rs0 = sp0
          /\ Mt !!! Regidx Rs1 = p
          /\ (forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
                r <> Rs0 -> r <> Rs1 -> Mt !!! Regidx r = m !!! Regidx r) ⌝ -∗
        ⌜ uptd_ext (pv_upt V) P' ⌝ -∗
        sie_cap_gpr Mt (av - 8)%nat b p -∗
        cpu_own 0%nat eb p C b -∗
        trap_csrs_ext eb -∗
        cpu_claim_ext eb p -∗
        pc_is (mword_of_int (KernelSyms.sys_pipe + 0x80) : mword 64) -∗
        (∃ on', fileclose_pipe_env fn on' 0%nat) -∗
        (∃ us', fileclose_fs_env fn us' 0%nat eb p) -∗
        proc_priv γf p pid
          (upd_upt (upd_ofile (upd_ofile V fd0 (fnode k0)) fd1 (fnode k1)) P') -∗
        fd_slot -∗ fd_slot -∗
        word_pointsto (pa_stk sp0 5) (DfracOwn 1) v -∗
        word_pointsto (pa_stk sp0 6) (DfracOwn 1) (fnode k0) -∗
        word_pointsto (pa_stk sp0 7) (DfracOwn 1) (fnode k1) -∗
        word4_pointsto (pa_stk sp0 8) (DfracOwn 1)
          (trunc32 (mword_of_int (Z.of_nat fd1) : mword 64)) -∗
        word4_pointsto (pa_add (pa_stk sp0 8) 4) (DfracOwn 1)
          (trunc32 (mword_of_int (Z.of_nat fd0) : mword 64)) -∗
        WP (Loop : expr riscv_lang)))%I).
    (* EPI and T7C are offered as a CONJUNCTION, the pipealloc idiom: exactly
       one is taken on each path, and T7C's own exit is EPI, so they must
       SHARE the epilogue rather than split it. *)
    iAssert (EPI ∧ T7C)%I with "[Hepi Hi80 Hi84 Hi86 Hi8a Hi8c Hi90 Hi94 Hi96 Hi9a Hi9c
                       Hia0 Hia4 Hia8 Hiac Hib0 Hib2]" as "HK".
    { iSplit; [iExact "Hepi"|]. rewrite /T7C.
      iIntros (CIDT HsT Mt P') "(%Htsp & %Hts0 & %Hts1 & %Htthr) %Hxt Hcg Hcpu
                       Hextc Hextm Hpc
                       Hpenv Hfenv Hpriv Hua Hub Hb5 Hb6 Hb7 Hlo Hhi".
      assert (Hlk1'' : pv_ofile (upd_ofile (upd_upt (upd_ofile (upd_ofile V fd0 (fnode k0))
                                   fd1 (fnode k1)) P') fd0 (zero_reg : mword 64)) !! fd1
                       = Some (fnode k1)).
      { cbn [upd_ofile upd_upt pv_ofile].
        rewrite list_lookup_insert_ne; [| congruence].
        apply list_lookup_insert. by rewrite length_insert. }
      (* +0x80 lw a5,-60(s0) -- reload fd0 *)
      assert (Ha0h : add_vec (rget Mt Rs0) (sign_extend' 64 (mword_of_int 0xfc4 : mword 12))
                     = pa_add (pa_stk sp0 8) 4) by (rgne; rewrite Hts0; apply sp_addr_fd0).
      iEval (rewrite -Ha0h) in "Hhi".
      iApply (wp_lw_s_sconf (mword_of_int (KernelSyms.sys_pipe + 0x80)) Ra5 Rs0
                (mword_of_int 0xfc4 : mword 12) Mt (av - 8)%nat
                (trunc32 (mword_of_int (Z.of_nat fd0) : mword 64)) b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi80 Hhi").
      iIntros (CID62 Hcr62) "Hcg Hpc Hhi". iEval (rewrite Ha0h) in "Hhi".
      set (E1 := <[Regidx Ra5 := regval_into_reg
                    (sign_extend' 64 (trunc32 (mword_of_int (Z.of_nat fd0) : mword 64)))]> Mt).
      change (<[Regidx Ra5 := regval_into_reg
          (sign_extend' 64 (trunc32 (mword_of_int (Z.of_nat fd0) : mword 64)))]> Mt) with E1.
      assert (Hpp84 : add_vec_int (mword_of_int (KernelSyms.sys_pipe + 0x80) : mword 64) 4
                      = mword_of_int (KernelSyms.sys_pipe + 0x84)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp84) in "Hpc".
      assert (HE1a5 : E1 !!! Regidx Ra5 = (mword_of_int (Z.of_nat fd0) : mword 64)).
      { rewrite /E1 upd_eq. apply sp_sext_trunc. exact Hfd0b31. }
      assert (HE1s1 : E1 !!! Regidx Rs1 = p)
        by (rewrite /E1 upd_ne; [exact Hts1 | vm_compute; discriminate]).
      (* +0x84 .. +0x8c: p->ofile[fd0] = 0 *)
      iDestruct (proc_priv_ofile γf p pid
                   (upd_upt (upd_ofile (upd_ofile V fd0 (fnode k0)) fd1 (fnode k1)) P')
                   fd0 (fnode k0) Hlk0' with "Hpriv") as "[Hslot Hback]".
      iDestruct "Hslot" as "[Hcell [[%Hz _] | Href]]";
        [by exfalso; apply (fnode_ne_zero k0 Hk0lt)|].
      iDestruct "Href" as (k0' q0' C0') "[[%Hfv0 %Hk0'lt] Hrf0]".
      iApply (sp_ofile_null (CID0 := CID62) E1 (av - 8)%nat p fd0 Ra5 Rs1
                (KernelSyms.sys_pipe + 0x84) (KernelSyms.sys_pipe + 0x86) (KernelSyms.sys_pipe + 0x8a) (KernelSyms.sys_pipe + 0x8c) (KernelSyms.sys_pipe + 0x90) (fnode k0) b
                Hfd0b16 (or_introl (conj eq_refl eq_refl)) HE1a5 HE1s1 Hn80a Hn80b Hn80c Hn80d
                with "Hcg Hpc Hi84 Hi86 Hi8a Hi8c Hcell").
      iIntros (CID63 Hcr63 E2) "%HE2thr Hcg Hpc Hcell".
      iDestruct ("Hback" $! (zero_reg : mword 64) with "[Hcell Hua]") as "Hpriv".
      { rewrite /ofile_slot. iFrame "Hcell". iLeft. by iFrame "Hua". }
      (* +0x90 lw a5,-64(s0) -- reload fd1 *)
      assert (HE2s0 : E2 !!! Regidx Rs0 = sp0)
        by (rewrite (HE2thr Rs0 ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate));
            rewrite /E1 upd_ne; [exact Hts0 | vm_compute; discriminate]).
      assert (HE2s1 : E2 !!! Regidx Rs1 = p)
        by (rewrite (HE2thr Rs1 ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)); exact HE1s1).
      assert (Ha1l : add_vec (rget E2 Rs0) (sign_extend' 64 (mword_of_int 0xfc0 : mword 12))
                     = pa_stk sp0 8) by (rgne; rewrite HE2s0; apply sp_addr_fd1).
      iEval (rewrite -Ha1l) in "Hlo".
      iApply (wp_lw_s_sconf (mword_of_int (KernelSyms.sys_pipe + 0x90)) Ra5 Rs0
                (mword_of_int 0xfc0 : mword 12) E2 (av - 8)%nat
                (trunc32 (mword_of_int (Z.of_nat fd1) : mword 64)) b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi90 Hlo").
      iIntros (CID64 Hcr64) "Hcg Hpc Hlo". iEval (rewrite Ha1l) in "Hlo".
      set (E3 := <[Regidx Ra5 := regval_into_reg
                    (sign_extend' 64 (trunc32 (mword_of_int (Z.of_nat fd1) : mword 64)))]> E2).
      change (<[Regidx Ra5 := regval_into_reg
          (sign_extend' 64 (trunc32 (mword_of_int (Z.of_nat fd1) : mword 64)))]> E2) with E3.
      assert (Hpp94 : add_vec_int (mword_of_int (KernelSyms.sys_pipe + 0x90) : mword 64) 4
                      = mword_of_int (KernelSyms.sys_pipe + 0x94)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp94) in "Hpc".
      assert (HE3a5 : E3 !!! Regidx Ra5 = (mword_of_int (Z.of_nat fd1) : mword 64)).
      { rewrite /E3 upd_eq. apply sp_sext_trunc. exact Hfd1b31. }
      assert (HE3s1 : E3 !!! Regidx Rs1 = p)
        by (rewrite /E3 upd_ne; [exact HE2s1 | vm_compute; discriminate]).
      (* +0x94 .. +0x9c: p->ofile[fd1] = 0 *)
      iDestruct (proc_priv_ofile γf p pid
                   (upd_ofile (upd_upt (upd_ofile (upd_ofile V fd0 (fnode k0)) fd1 (fnode k1)) P')
                              fd0 (zero_reg : mword 64))
                   fd1 (fnode k1) Hlk1'' with "Hpriv") as "[Hslot1 Hback1]".
      iDestruct "Hslot1" as "[Hcell1 [[%Hz1 _] | Href1']]";
        [by exfalso; apply (fnode_ne_zero k1 Hk1lt)|].
      iDestruct "Href1'" as (k1' q1' C1') "[[%Hfv1 %Hk1'lt] Hrf1]".
      iApply (sp_ofile_null (CID0 := CID64) E3 (av - 8)%nat p fd1 Rs1 Ra5
                (KernelSyms.sys_pipe + 0x94) (KernelSyms.sys_pipe + 0x96) (KernelSyms.sys_pipe + 0x9a) (KernelSyms.sys_pipe + 0x9c) (KernelSyms.sys_pipe + 0xa0) (fnode k1) b
                Hfd1b16 (or_intror (conj eq_refl eq_refl)) HE3a5 HE3s1 Hn90a Hn90b Hn90c Hn90d
                with "Hcg Hpc Hi94 Hi96 Hi9a Hi9c Hcell1").
      iIntros (CID65 Hcr65 E4) "%HE4thr Hcg Hpc Hcell1".
      iDestruct ("Hback1" $! (zero_reg : mword 64) with "[Hcell1 Hub]") as "Hpriv".
      { rewrite /ofile_slot. iFrame "Hcell1". iLeft. by iFrame "Hub". }
      rewrite (sp_restore_upt V P' fd0 fd1 (fnode k0) (fnode k1) Hne01 Hfree0 Hfree1V).
      (* the two references, loose again, go to the two fileclose calls *)
      iEval (rewrite Hfv0) in "Hb6". iEval (rewrite Hfv1) in "Hb7".
      assert (HE4s0 : E4 !!! Regidx Rs0 = sp0)
        by (rewrite (HE4thr Rs0 ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate));
            rewrite /E3 upd_ne; [exact HE2s0 | vm_compute; discriminate]).
      assert (HE4sp : E4 !!! Regidx csp_rs1 = pa_stk sp0 8).
      { rewrite (HE4thr csp_rs1 ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)).
        rewrite /E3 upd_ne; [| vm_compute; discriminate].
        rewrite (HE2thr csp_rs1 ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)).
        rewrite /E1 upd_ne; [exact Htsp | vm_compute; discriminate]. }
      assert (HthrE4 : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
                r <> Rs0 -> r <> Rs1 -> E4 !!! Regidx r = m !!! Regidx r).
      { intros r Hr N2 N8 N9.
        assert (N15 : r <> Ra5) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
        rewrite (HE4thr r N15 N9). rewrite /E3 upd_ne; [| congruence].
        rewrite (HE2thr r N15 N15). rewrite /E1 upd_ne; [| congruence].
        apply Htthr; assumption. }
      (* +0xa0: fileclose(rf); fileclose(wf); a5 = -1 *)
      iDestruct (cpu_own_transport CIDT CID65 0%nat eb p C b ltac:(wp_next_chain)
                   with "Hcpu") as "Hcpu".
      iDestruct (trap_csrs_ext_transport CIDT CID65 eb p
                   ltac:(rewrite Hb; wp_next_chain) with "Hextc") as "Hextc".
      iDestruct (cpu_claim_ext_transport CIDT CID65 eb p
                   ltac:(rewrite Hb; wp_next_chain) with "Hextm") as "Hextm".
      iDestruct "Hpenv" as (on2) "Hpenv".
      iDestruct "Hfenv" as (us2) "Hfenv".
      iApply (sp_close2 (CID0 := CID65)  γfl γf fn on2 us2 E4 (av - 8)%nat eb p C sp0 k0' k1' q0' q1' C0' C1'
                (KernelSyms.sys_pipe + 0xa0) (KernelSyms.sys_pipe + 0xa4) (KernelSyms.sys_pipe + 0xa8) (KernelSyms.sys_pipe + 0xac) (KernelSyms.sys_pipe + 0xb0) (KernelSyms.sys_pipe + 0xb2)
                (mword_of_int 2092078 : mword 21) (mword_of_int 2092070 : mword 21) b
                Havfc HE4s0 Hc9ca Hc9cb Hc9cc Hc9cd Hc9ce Hc9cf Hc9cg
                with "Hcg Hcpu Hextc Hextm Htext Hpc Hftab Hpanic Hia0 Hia4 Hia8 Hiac Hib0 Hb6 Hb7 Hrf0 Hrf1 Hpenv Hfenv").
      iIntros (CID66 Hcr66 Mr) "[%Hmrcs %Hmra5] Hcg Hcpu Hextc Hextm Hpc Hb6 Hb7 Hua Hub Hpenv Hfenv".
      (* +0xb2 c.j +0x28 -- into the shared epilogue *)
      iApply (wp_cj_s_sconf (mword_of_int (KernelSyms.sys_pipe + 0xb2))
                (sign_extend' 21 (concat_vec (mword_of_int 20 : mword 11) ('b"0")))
                Mr (av - 8)%nat b ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hib2").
      iIntros (CID67 Hcr67). iApply bi.later_intro. iIntros "Hcg Hpc".
      assert (Htgtj : add_vec (mword_of_int (KernelSyms.sys_pipe + 0xb2) : mword 64)
                        (sign_extend' 64 (sign_extend' 21
                           (concat_vec (mword_of_int 20 : mword 11) ('b"0"))))
                      = mword_of_int (KernelSyms.sys_pipe + 0xda))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Htgtj) in "Hpc".
      iDestruct (cpu_own_transport CID66 CID67 0%nat eb p C b ltac:(wp_next_chain)
                   with "Hcpu") as "Hcpu".
      iDestruct (trap_csrs_ext_transport CID66 CID67 eb p
                   ltac:(rewrite Hb; wp_next_chain) with "Hextc") as "Hextc".
      iDestruct (cpu_claim_ext_transport CID66 CID67 eb p
                   ltac:(rewrite Hb; wp_next_chain) with "Hextm") as "Hextm".
      iSpecialize ("Hepi" $! CID67 with "[%]"); [wp_next_chain|].
      iApply ("Hepi" $! Mr P' (mword_of_int (-1) : mword 64)
                with "[%] [%] Hcg Hcpu Hextc Hextm Hpc [Hpenv] Hfenv [Hb5 Hb6 Hb7] [Hlo Hhi] [Hpriv Hua Hub]").
      { split.
        { rewrite (Hmrcs csp_rs1 ltac:(vm_compute; reflexivity)). exact HE4sp. }
        split; [exact Hmra5|].
        intros r Hr N2 N8 N9. rewrite (Hmrcs r Hr). apply HthrE4; assumption. }
      { exact Hxt. }
      { iExact "Hpenv". }
      { iExists v, (fnode k0'), (fnode k1'). iFrame "Hb5 Hb6 Hb7". }
      { iExists (trunc32 (mword_of_int (Z.of_nat fd1) : mword 64)),
                (trunc32 (mword_of_int (Z.of_nat fd0) : mword 64)). iFrame "Hlo Hhi". }
      rewrite /sys_pipe_post.
      iSplitR "Hua Hub"; [| iSplitL "Hua"; [iExact "Hua" | iExact "Hub"]].
      iLeft. iSplitR; [done|]. iExact "Hpriv". }
    (* +0x62 blt a0,x0 -- did the first copyout fail? *)
    destruct Hret1 as [Hco0|Hcom1].
    2:{ (* ===== copyout(&fd0) failed: null both descriptors, close both ===== *)
      iApply (wp_blt_x0_taken_s_sconf (mword_of_int (KernelSyms.sys_pipe + 0x62))
                (mword_of_int 30 : mword 13) Ra0 B0 (av - 8)%nat b
                ltac:(vm_compute; discriminate)
                ltac:(rgne; rewrite Hcom1; vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi62").
      iApply bi.later_intro. iIntros (CID68 Hcr68) "Hcg Hpc".
      assert (Hbt3 : add_vec (mword_of_int (KernelSyms.sys_pipe + 0x62) : mword 64)
                       (sign_extend' 64 (mword_of_int 30 : mword 13))
                     = mword_of_int (KernelSyms.sys_pipe + 0x80))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hbt3) in "Hpc".
      iDestruct ("Hpback" $! Pa with "[%] Hszc Hptc Hpt") as "Hpriv"; [exact Hext1|].
      iDestruct "HK" as "[_ Ht7c]".
      iDestruct (cpu_own_transport CID61 CID68 0%nat eb p C b ltac:(wp_next_chain)
                   with "Hcpu") as "Hcpu".
      (* neither fdalloc nor copyout mentions the complement: the hop is still
         from [CID34], the hart pipealloc handed it back on. *)
      iDestruct (trap_csrs_ext_transport CID34 CID68 eb p
                   ltac:(rewrite Hb; wp_next_chain) with "Hextc") as "Hextc".
      iDestruct (cpu_claim_ext_transport CID34 CID68 eb p
                   ltac:(rewrite Hb; wp_next_chain) with "Hextm") as "Hextm".
      iSpecialize ("Ht7c" $! CID68 with "[%]"); [wp_next_chain|].
      iApply ("Ht7c" $! B0 Pa with "[%] [%] Hcg Hcpu Hextc Hextm Hpc [Hpenv] [Hfenv] Hpriv Hu0 Hu1 Hb5 Hb6 Hb7 Hlo Hhi").
      { split; [exact HB0sp|]. split; [exact HB0s0|].
        split; [exact HB0s1 | exact HthrB0]. }
      { exact (uptd_ext_sz_ext _ _ _ Hext1). }
      { by iExists on. }
      { by iExists us. } }
    (* ===== the first copyout succeeded: do the second ===== *)
    iApply (wp_blt_x0_fall_s_sconf (mword_of_int (KernelSyms.sys_pipe + 0x62))
              (mword_of_int 30 : mword 13) Ra0 B0 (av - 8)%nat b
              ltac:(vm_compute; discriminate)
              ltac:(rgne; rewrite Hco0; vm_compute; reflexivity)
              with "Hcg Hpc Hi62").
    iIntros (CID69 Hcr69) "Hcg Hpc".
    assert (Hpp66 : add_vec_int (mword_of_int (KernelSyms.sys_pipe + 0x62) : mword 64) 4 = mword_of_int (KernelSyms.sys_pipe + 0x66))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp66) in "Hpc".
    (* +0x66 c.li a4,4 -- the length argument, now in a4 *)
    iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.sys_pipe + 0x66)) Ra4 (mword_of_int 4 : mword 6)
              (mword_of_int (Z.of_nat 4) : mword 64) B0 (av - 8)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc Hi66").
    iIntros (CID70 Hcr70) "Hcg Hpc".
    set (C1 := <[Regidx Ra4 := regval_into_reg (mword_of_int (Z.of_nat 4) : mword 64)]> B0).
    change (<[Regidx Ra4 := regval_into_reg (mword_of_int (Z.of_nat 4) : mword 64)]> B0) with C1.
    assert (Hpp68 : add_vec_int (mword_of_int (KernelSyms.sys_pipe + 0x66) : mword 64) 2 = mword_of_int (KernelSyms.sys_pipe + 0x68))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp68) in "Hpc".
    assert (HC1s0 : C1 !!! Regidx Rs0 = sp0)
      by (rewrite /C1 upd_ne; [exact HB0s0 | vm_compute; discriminate]).
    (* +0x68 addi a3,s0,-64 -- a3 := &fd1, the SOURCE, now in a3 *)
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.sys_pipe + 0x68)) Ra3 Rs0
              (mword_of_int 0xfc0 : mword 12) C1 (av - 8)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi68").
    iIntros (CID71 Hcr71) "Hcg Hpc".
    set (C2 := <[Regidx Ra3 := regval_into_reg
                  (add_vec (rget C1 Rs0) (sign_extend' 64 (mword_of_int 0xfc0 : mword 12)))]> C1).
    change (<[Regidx Ra3 := regval_into_reg
        (add_vec (rget C1 Rs0) (sign_extend' 64 (mword_of_int 0xfc0 : mword 12)))]> C1) with C2.
    assert (Hpp6c : add_vec_int (mword_of_int (KernelSyms.sys_pipe + 0x68) : mword 64) 4 = mword_of_int (KernelSyms.sys_pipe + 0x6c))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp6c) in "Hpc".
    assert (HC2a3 : C2 !!! Regidx Ra3 = pa_stk sp0 8).
    { rewrite /C2 upd_eq. rgne. rewrite HC1s0. apply sp_addr_fd1. }
    assert (HC2s0 : C2 !!! Regidx Rs0 = sp0)
      by (rewrite /C2 upd_ne; [exact HC1s0 | vm_compute; discriminate]).
    (* +0x6c ld a2,-40(s0) -- a2 := fdarray *)
    assert (Hfdb : add_vec (rget C2 Rs0) (sign_extend' 64 (mword_of_int 0xfd8 : mword 12))
                   = pa_stk sp0 5) by (rgne; rewrite HC2s0; apply sp_addr_fdarray).
    iEval (rewrite -Hfdb) in "Hb5".
    iApply (wp_ld_s_sconf (mword_of_int (KernelSyms.sys_pipe + 0x6c)) Ra2 Rs0
              (mword_of_int 0xfd8 : mword 12) C2 (av - 8)%nat v b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi6c Hb5").
    iIntros (CID72 Hcr72) "Hcg Hpc Hb5". iEval (rewrite Hfdb) in "Hb5".
    set (C3 := <[Regidx Ra2 := regval_into_reg v]> C2).
    change (<[Regidx Ra2 := regval_into_reg v]> C2) with C3.
    assert (Hpp70 : add_vec_int (mword_of_int (KernelSyms.sys_pipe + 0x6c) : mword 64) 4 = mword_of_int (KernelSyms.sys_pipe + 0x70))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp70) in "Hpc".
    (* +0x70 c.add a2,a2,a4 -- fdarray + sizeof(fd0) *)
    iApply (wp_cadd_s_sconf (mword_of_int (KernelSyms.sys_pipe + 0x70)) Ra2 Ra4 C3 (av - 8)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi70").
    iIntros (CID73 Hcr73) "Hcg Hpc".
    set (C4 := <[Regidx Ra2 := regval_into_reg
                  (add_vec (rget C3 Ra2) (rget C3 Ra4))]> C3).
    change (<[Regidx Ra2 := regval_into_reg
        (add_vec (rget C3 Ra2) (rget C3 Ra4))]> C3) with C4.
    assert (Hpp72 : add_vec_int (mword_of_int (KernelSyms.sys_pipe + 0x70) : mword 64) 2 = mword_of_int (KernelSyms.sys_pipe + 0x72))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp72) in "Hpc".
    assert (HC4s1 : C4 !!! Regidx Rs1 = p).
    { rewrite /C4 upd_ne; [| vm_compute; discriminate].
      rewrite /C3 upd_ne; [| vm_compute; discriminate].
      rewrite /C2 upd_ne; [| vm_compute; discriminate].
      rewrite /C1 upd_ne; [exact HB0s1 | vm_compute; discriminate]. }
    (* +0x72 c.ld a1,72(s1) -- a1 := p->sz, copyout's [psz] argument again *)
    assert (Hszb2 : add_vec (rget C4 Rs1) (sign_extend' 64 (mword_of_int 72 : mword 12))
                    = p_sz p) by (rgne; rewrite HC4s1; reflexivity).
    iEval (rewrite -Hszb2) in "Hszc".
    iApply (wp_cld_s_sconf (mword_of_int (KernelSyms.sys_pipe + 0x72)) Ra1 Rs1
              (mword_of_int 72 : mword 12) C4 (av - 8)%nat
              (pv_sz (upd_ofile (upd_ofile V fd0 (fnode k0)) fd1 (fnode k1))) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi72 Hszc").
    iIntros (CID73b Hcr73b) "Hcg Hpc Hszc". iEval (rewrite Hszb2) in "Hszc".
    set (C5 := <[Regidx Ra1 := regval_into_reg
                  (pv_sz (upd_ofile (upd_ofile V fd0 (fnode k0)) fd1 (fnode k1)))]> C4).
    change (<[Regidx Ra1 := regval_into_reg
        (pv_sz (upd_ofile (upd_ofile V fd0 (fnode k0)) fd1 (fnode k1)))]> C4) with C5.
    assert (Hpp74 : add_vec_int (mword_of_int (KernelSyms.sys_pipe + 0x72) : mword 64) 2 = mword_of_int (KernelSyms.sys_pipe + 0x74))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp74) in "Hpc".
    assert (HC5s1 : C5 !!! Regidx Rs1 = p)
      by (rewrite /C5 upd_ne; [exact HC4s1 | vm_compute; discriminate]).
    (* +0x74 c.ld a0,80(s1) -- a0 := p->pagetable (unchanged: [uptd_ext]) *)
    assert (HrootA : ud_root Pa
                     = ud_root (pv_upt (upd_ofile (upd_ofile V fd0 (fnode k0)) fd1 (fnode k1))))
      by exact (proj1 (proj1 Hext1)).
    assert (Hptb : add_vec (rget C5 Rs1) (sign_extend' 64 (mword_of_int 80 : mword 12))
                   = p_pagetable p) by (rgne; rewrite HC5s1; reflexivity).
    iEval (rewrite -Hptb) in "Hptc".
    iApply (wp_cld_s_sconf (mword_of_int (KernelSyms.sys_pipe + 0x74)) Ra0 Rs1
              (mword_of_int 80 : mword 12) C5 (av - 8)%nat
              (page_base (ud_root (pv_upt (upd_ofile (upd_ofile V fd0 (fnode k0)) fd1 (fnode k1))))) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi74 Hptc").
    iIntros (CID74 Hcr74) "Hcg Hpc Hptc". iEval (rewrite Hptb) in "Hptc".
    set (C6 := <[Regidx Ra0 := regval_into_reg
                  (page_base (ud_root (pv_upt (upd_ofile (upd_ofile V fd0 (fnode k0))
                                                 fd1 (fnode k1)))))]> C5).
    change (<[Regidx Ra0 := regval_into_reg
        (page_base (ud_root (pv_upt (upd_ofile (upd_ofile V fd0 (fnode k0))
                                       fd1 (fnode k1)))))]> C5) with C6.
    assert (Hpp76 : add_vec_int (mword_of_int (KernelSyms.sys_pipe + 0x74) : mword 64) 2 = mword_of_int (KernelSyms.sys_pipe + 0x76))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp76) in "Hpc".
    (* +0x76 jal ra,copyout *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.sys_pipe + 0x76)) Rra
              (mword_of_int 2080940 : mword 21) C6 (av - 8)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi76").
    iIntros (CID75 Hcr75) "Hcg Hpc".
    set (C7 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KernelSyms.sys_pipe + 0x76) : mword 64) 4)]> C6).
    change (<[Regidx Rra := regval_into_reg
        (add_vec_int (mword_of_int (KernelSyms.sys_pipe + 0x76) : mword 64) 4)]> C6) with C7.
    assert (Hjco2 : add_vec (mword_of_int (KernelSyms.sys_pipe + 0x76) : mword 64)
                      (sign_extend' 64 (mword_of_int 2080940 : mword 21))
                    = mword_of_int KernelSyms.copyout)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hjco2) in "Hpc".
    assert (HC7ra : C7 !!! Regidx Rra = add_vec_int (mword_of_int (KernelSyms.sys_pipe + 0x76) : mword 64) 4)
      by (rewrite /C7; apply upd_eq).
    assert (HC7a0 : C7 !!! Regidx Ra0 = page_base (ud_root Pa)).
    { rewrite /C7 upd_ne; [| vm_compute; discriminate].
      rewrite /C6 upd_eq. by rewrite HrootA. }
    assert (HC7a1 : C7 !!! Regidx Ra1
                    = pv_sz (upd_ofile (upd_ofile V fd0 (fnode k0)) fd1 (fnode k1))).
    { rewrite /C7 upd_ne; [| vm_compute; discriminate].
      rewrite /C6 upd_ne; [| vm_compute; discriminate].
      rewrite /C5; apply upd_eq. }
    assert (HC7a3 : C7 !!! Regidx Ra3 = pa_stk sp0 8).
    { rewrite /C7 upd_ne; [| vm_compute; discriminate].
      rewrite /C6 upd_ne; [| vm_compute; discriminate].
      rewrite /C5 upd_ne; [| vm_compute; discriminate].
      rewrite /C4 upd_ne; [| vm_compute; discriminate].
      rewrite /C3 upd_ne; [exact HC2a3 | vm_compute; discriminate]. }
    assert (HC7a4 : C7 !!! Regidx Ra4 = (mword_of_int (Z.of_nat 4) : mword 64)).
    { rewrite /C7 upd_ne; [| vm_compute; discriminate].
      rewrite /C6 upd_ne; [| vm_compute; discriminate].
      rewrite /C5 upd_ne; [| vm_compute; discriminate].
      rewrite /C4 upd_ne; [| vm_compute; discriminate].
      rewrite /C3 upd_ne; [| vm_compute; discriminate].
      rewrite /C2 upd_ne; [| vm_compute; discriminate].
      rewrite /C1; apply upd_eq. }
    assert (HC7sp : C7 !!! Regidx csp_rs1 = pa_stk sp0 8).
    { rewrite /C7 upd_ne; [| vm_compute; discriminate].
      rewrite /C6 upd_ne; [| vm_compute; discriminate].
      rewrite /C5 upd_ne; [| vm_compute; discriminate].
      rewrite /C4 upd_ne; [| vm_compute; discriminate].
      rewrite /C3 upd_ne; [| vm_compute; discriminate].
      rewrite /C2 upd_ne; [| vm_compute; discriminate].
      rewrite /C1 upd_ne; [exact HB0sp | vm_compute; discriminate]. }
    assert (HC7s0 : C7 !!! Regidx Rs0 = sp0).
    { rewrite /C7 upd_ne; [| vm_compute; discriminate].
      rewrite /C6 upd_ne; [| vm_compute; discriminate].
      rewrite /C5 upd_ne; [| vm_compute; discriminate].
      rewrite /C4 upd_ne; [| vm_compute; discriminate].
      rewrite /C3 upd_ne; [exact HC2s0 | vm_compute; discriminate]. }
    assert (HC7s1 : C7 !!! Regidx Rs1 = p).
    { rewrite /C7 upd_ne; [| vm_compute; discriminate].
      rewrite /C6 upd_ne; [exact HC5s1 | vm_compute; discriminate]. }
    assert (HthrC7 : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
              r <> Rs0 -> r <> Rs1 -> C7 !!! Regidx r = m !!! Regidx r).
    { intros r Hr N2 N8 N9.
      assert (N1 : r <> Rra) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      assert (N10 : r <> Ra0) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      assert (N11 : r <> Ra1) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      assert (N12 : r <> Ra2) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      assert (N13 : r <> Ra3) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      assert (N14 : r <> Ra4) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      rewrite /C7 upd_ne; [| congruence].
      rewrite /C6 upd_ne; [| congruence].
      rewrite /C5 upd_ne; [| congruence].
      rewrite /C4 upd_ne; [| congruence].
      rewrite /C3 upd_ne; [| congruence].
      rewrite /C2 upd_ne; [| congruence].
      rewrite /C1 upd_ne; [| congruence]. apply HthrB0; assumption. }
    (* the [int fd1] cell AS the second copyout's buffer *)
    iDestruct "Hlo" as "[%Hallo Hbuflo]".
    iEval (rewrite -HC7a3) in "Hbuflo".
    iDestruct (cpu_own_transport CID61 CID75 0%nat eb p C b ltac:(wp_next_chain)
                 with "Hcpu") as "Hcpu".
    iApply (Copyout.wp_copyout_sconf γa C7 Pa
              (pv_sz (upd_ofile (upd_ofile V fd0 (fnode k0)) fd1 (fnode k1))) 4%nat
              (fun j => nth_byte (trunc32 (mword_of_int (Z.of_nat fd1) : mword 64)) j)
              (av - 8)%nat 0%nat eb p C b
              Hav52 HC7a0 HC7a1 HC7a4 sp_len4 Hszb sp_n0
              with "Hcg Hcpu Htext Hpc Hpt Henvb Hbuflo").
    iIntros (CID76 Hcr76 D0 Pb) "Hcg Hcpu Hpc Hpt Hbuflo %HcsD0 %Hext2 %Hret2".
    iEval (rewrite HC7a3) in "Hbuflo".
    iDestruct (word4_pointsto_intro _ _ _ Hallo with "Hbuflo") as "Hlo".
    assert (Hpc7a : ret_pc (C7 !!! Regidx Rra) = mword_of_int (KernelSyms.sys_pipe + 0x7a))
      by (rewrite HC7ra; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc7a) in "Hpc".
    assert (Hextb : uptd_ext_sz (pv_sz (upd_ofile (upd_ofile V fd0 (fnode k0)) fd1 (fnode k1)))
                      (pv_upt (upd_ofile (upd_ofile V fd0 (fnode k0)) fd1 (fnode k1))) Pb)
      by exact (uptd_ext_sz_trans _ _ Pa Pb Hext1 Hext2).
    assert (HD0sp : D0 !!! Regidx csp_rs1 = pa_stk sp0 8)
      by (rewrite (callee_saved_lookup HcsD0 csp_rs1 ltac:(vm_compute; reflexivity)); exact HC7sp).
    assert (HD0s0 : D0 !!! Regidx Rs0 = sp0)
      by (rewrite (callee_saved_lookup HcsD0 Rs0 ltac:(vm_compute; reflexivity)); exact HC7s0).
    assert (HD0s1 : D0 !!! Regidx Rs1 = p)
      by (rewrite (callee_saved_lookup HcsD0 Rs1 ltac:(vm_compute; reflexivity)); exact HC7s1).
    assert (HthrD0 : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
              r <> Rs0 -> r <> Rs1 -> D0 !!! Regidx r = m !!! Regidx r).
    { intros r Hr N2 N8 N9.
      rewrite (callee_saved_lookup HcsD0 r Hr). apply HthrC7; assumption. }
    (* +0x7a c.li a5,0 -- the success return, precomputed *)
    iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.sys_pipe + 0x7a)) Ra5 (mword_of_int 0 : mword 6)
              (zero_reg : mword 64) D0 (av - 8)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc Hi7a").
    iIntros (CID77 Hcr77) "Hcg Hpc".
    set (D1 := <[Regidx Ra5 := regval_into_reg (zero_reg : mword 64)]> D0).
    change (<[Regidx Ra5 := regval_into_reg (zero_reg : mword 64)]> D0) with D1.
    assert (Hpp7c : add_vec_int (mword_of_int (KernelSyms.sys_pipe + 0x7a) : mword 64) 2 = mword_of_int (KernelSyms.sys_pipe + 0x7c))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp7c) in "Hpc".
    assert (HD1a0 : D1 !!! Regidx Ra0 = D0 !!! Regidx Ra0)
      by (rewrite /D1 upd_ne; [reflexivity | vm_compute; discriminate]).
    assert (HD1a5 : D1 !!! Regidx Ra5 = (zero_reg : mword 64))
      by (rewrite /D1; apply upd_eq).
    assert (HD1sp : D1 !!! Regidx csp_rs1 = pa_stk sp0 8)
      by (rewrite /D1 upd_ne; [exact HD0sp | vm_compute; discriminate]).
    assert (HD1s0 : D1 !!! Regidx Rs0 = sp0)
      by (rewrite /D1 upd_ne; [exact HD0s0 | vm_compute; discriminate]).
    assert (HD1s1 : D1 !!! Regidx Rs1 = p)
      by (rewrite /D1 upd_ne; [exact HD0s1 | vm_compute; discriminate]).
    assert (HthrD1 : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
              r <> Rs0 -> r <> Rs1 -> D1 !!! Regidx r = m !!! Regidx r).
    { intros r Hr N2 N8 N9.
      assert (N15 : r <> Ra5) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      rewrite /D1 upd_ne; [| congruence]. apply HthrD0; assumption. }
    iDestruct ("Hpback" $! Pb with "[%] Hszc Hptc Hpt") as "Hpriv"; [exact Hextb|].
    (* +0x7c bge a0,x0 -- both copies landed? *)
    destruct Hret2 as [Hs0|Hsm1].
    - (* ============ SUCCESS: return 0 ============ *)
      iApply (wp_bgez_taken_s_sconf (mword_of_int (KernelSyms.sys_pipe + 0x7c))
                (mword_of_int 94 : mword 13) Ra0 D1 (av - 8)%nat b
                ltac:(vm_compute; discriminate)
                ltac:(rgne; rewrite HD1a0 Hs0; vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi7c").
      iApply bi.later_intro. iIntros (CID78 Hcr78) "Hcg Hpc".
      assert (Hbt4 : add_vec (mword_of_int (KernelSyms.sys_pipe + 0x7c) : mword 64)
                       (sign_extend' 64 (mword_of_int 94 : mword 13))
                     = mword_of_int (KernelSyms.sys_pipe + 0xda))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hbt4) in "Hpc".
      iDestruct "HK" as "[Hepi _]".
      iDestruct (cpu_own_transport CID76 CID78 0%nat eb p C b ltac:(wp_next_chain)
                   with "Hcpu") as "Hcpu".
      iDestruct (trap_csrs_ext_transport CID34 CID78 eb p
                   ltac:(rewrite Hb; wp_next_chain) with "Hextc") as "Hextc".
      iDestruct (cpu_claim_ext_transport CID34 CID78 eb p
                   ltac:(rewrite Hb; wp_next_chain) with "Hextm") as "Hextm".
      iSpecialize ("Hepi" $! CID78 with "[%]"); [wp_next_chain|].
      iApply ("Hepi" $! D1 Pb (zero_reg : mword 64)
                with "[%] [%] Hcg Hcpu Hextc Hextm Hpc [Hpenv] [Hfenv] [Hb5 Hb6 Hb7] [Hlo Hhi] [Hpriv Hu0 Hu1]").
      { split; [exact HD1sp|]. split; [exact HD1a5 | exact HthrD1]. }
      { exact (uptd_ext_sz_ext _ _ _ Hextb). }
      { by iExists on. }
      { by iExists us. }
      { iExists v, (fnode k0), (fnode k1). iFrame "Hb5 Hb6 Hb7". }
      { iExists (trunc32 (mword_of_int (Z.of_nat fd1) : mword 64)),
                (trunc32 (mword_of_int (Z.of_nat fd0) : mword 64)). iFrame "Hlo Hhi". }
      rewrite /sys_pipe_post.
      iSplitR "Hu0 Hu1"; [| iSplitL "Hu0"; [iExact "Hu0" | iExact "Hu1"]].
      iRight. iExists fd0, fd1, l1, k0, k1.
      iSplitR; [iPureIntro; split; [reflexivity | exact Hfr1']|].
      rewrite -sp_upt_ofile_comm. iExact "Hpriv".
    - (* ============ copyout(&fd1) failed: the shared tail ============ *)
      iApply (wp_bgez_fall_s_sconf (mword_of_int (KernelSyms.sys_pipe + 0x7c))
                (mword_of_int 94 : mword 13) Ra0 D1 (av - 8)%nat b
                ltac:(vm_compute; discriminate)
                ltac:(rgne; rewrite HD1a0 Hsm1; vm_compute; reflexivity)
                with "Hcg Hpc Hi7c").
      iIntros (CID79 Hcr79) "Hcg Hpc".
      assert (Hpp80 : add_vec_int (mword_of_int (KernelSyms.sys_pipe + 0x7c) : mword 64) 4
                      = mword_of_int (KernelSyms.sys_pipe + 0x80)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp80) in "Hpc".
      iDestruct "HK" as "[_ Ht7c]".
      iDestruct (cpu_own_transport CID76 CID79 0%nat eb p C b ltac:(wp_next_chain)
                   with "Hcpu") as "Hcpu".
      iDestruct (trap_csrs_ext_transport CID34 CID79 eb p
                   ltac:(rewrite Hb; wp_next_chain) with "Hextc") as "Hextc".
      iDestruct (cpu_claim_ext_transport CID34 CID79 eb p
                   ltac:(rewrite Hb; wp_next_chain) with "Hextm") as "Hextm".
      iSpecialize ("Ht7c" $! CID79 with "[%]"); [wp_next_chain|].
      iApply ("Ht7c" $! D1 Pb with "[%] [%] Hcg Hcpu Hextc Hextm Hpc [Hpenv] [Hfenv] Hpriv Hu0 Hu1 Hb5 Hb6 Hb7 Hlo Hhi").
      { split; [exact HD1sp|]. split; [exact HD1s0|].
        split; [exact HD1s1 | exact HthrD1]. }
      { exact (uptd_ext_sz_ext _ _ _ Hextb). }
      { by iExists on. }
      { by iExists us. }
  Qed.





End ProofSysPipe.

End SysPipeProof.
