(* SpecFdalloc.v -- the public interface of fdalloc(), stated independently
   of its proof.  Requires only the definitional layer -- never a
   whole-function proof file -- so every function proof can be checked in
   parallel.

     static int fdalloc(struct file *f) {
       int fd;
       struct proc *p = myproc();
       for (fd = 0; fd < NOFILE; fd++)
         if (p->ofile[fd] == 0) { p->ofile[fd] = f; return fd; }
       return -1;
     }

   @ KernelSyms.fdalloc = 0x80004a5e, 22 instructions (a 32-byte frame; [f]
   rides in the callee-saved s1 across the myproc call, and the loop walks a
   POINTER [a5 = &p->ofile[fd]] rather than re-indexing).

     +0x00  1101/ec06/e822/e426/1000    prologue, s0 = entry sp
     +0x0a  84aa        c.mv     s1,a0        s1 := f
     +0x0c  e9bfc0ef    jal      ra,myproc
     +0x10  862a        c.mv     a2,a0        a2 := p
     +0x12  0d050793    addi     a5,a0,208    a5 := &p->ofile[0]
     +0x16  4501        c.li     a0,0         fd = 0
     +0x18  46c1        c.li     a3,16        NOFILE
     +0x1a  6398        c.ld     a4,0(a5)     <- loop head
     +0x1c  cb19        c.beqz   a4,+0x18     found a free slot
     +0x1e  2505        c.addiw  a0,a0,1
     +0x20  07a1        c.addi   a5,a5,8
     +0x22  fed51ce3    bne      a0,a3,-0x18  loop back
     +0x26  557d        c.li     a0,-1        the table is full
     +0x28  60e2/6442/64a2/6105/8082         epilogue  <- both arms join
     +0x32  00351793    slli     a5,a0,3      the found arm: &p->ofile[fd]
     +0x36  0d078793    addi     a5,a5,208
     +0x3a  963e        c.add    a2,a2,a5
     +0x3c  e204        c.sd     s1,0(a2)     p->ofile[fd] = f
     +0x3e  b7ed        c.j      -0x26        back to the epilogue

   THE CONTRACT.  "Takes over file reference from caller on success", says
   the comment -- but that is the CALLER's obligation, not fdalloc's.  fdalloc
   stores a pointer; it never touches a [file_ref].  So the contract is stated
   over the block SPLIT at the fd table ([ProcInv.proc_priv_core] plus
   [ProcInv.proc_ofiles_owe]), and it takes no reference at all: on success the
   descriptor it filled joins the caller's payload DEFICIT, which the caller
   settles from whatever reference it holds.
     This is strictly weaker than demanding the [file_ref] up front, and it is
   what sys_dup needs: there, [filedup] wants the SOURCE descriptor's reference
   in hand, so that descriptor is already payloadless when fdalloc runs, and a
   spec taking a whole [proc_priv] could not be applied at all.  The deficit
   set [D] is a pure spectator here -- fdalloc's code cannot tell which
   descriptors are on loan, and does not need to: it only ever fills a NULL
   one, and [ProcInv.proc_ofiles_owe]'s non-null clause on lent descriptors is
   what makes "the cell I found is null" enough to know it is not one.
     Callers that do hold the reference (sys_open, sys_pipe) settle the deficit
   immediately after the call with [ProcInv.proc_ofiles_repay], which is one
   line.  See claude-notes/design/file-table.md.

   WHICH descriptor is not a choice -- it is the LEAST free one, a function
   of the process's own (thread-local) array.  [fd_frees] below names that
   sequence, so the postcondition is deterministic in the same sense
   [SpecArgfd.arg_fd] is: a kernel that always returned -1 would not satisfy
   this spec.  Giving the whole SEQUENCE rather than just its head is what
   lets a caller that allocates TWO descriptors (sys_pipe) name both without
   re-deriving anything -- the second call's array is the first's with one
   non-null entry written, and [fd_frees_insert] says that just pops the
   head.

   THE fd_slot IS THE POINT OF THE SUCCESS CASE.  An EMPTY descriptor owns
   one unit of fd-slot capability itself ([ProcInv.ofile_slot]'s left
   disjunct); a descriptor naming a file has given it to the ftable, against
   that file's reference count.  So filling a descriptor RELEASES a unit,
   and fdalloc hands it back to the caller -- which is what pays for
   [fileclose]'s later demand and keeps the conservation law of FdSlots.v
   balanced across a syscall.  (sys_pipe is the worked example: two units in
   at the top, two out at the bottom, on every one of its four exits.)

   Design: claude-notes/design/file-table.md, claude-notes/design/proc-struct.md. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExtras.
Require Import InstrBytes.
Require Import RegFile.
Require Import SmodeCore.
Require Import CalleeSaved KernelText KernelDataInv.
Require Import IntrDefs.
Require Import WpNext.
Require Import WpLock.
Require Import CpuOwn.
Require Import FdSlots ProcInv.
Require Import FileInvDefs.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Import Defs.
Local Open Scope Z_scope.


(* fdalloc's own frame is 4 slots (addi sp,sp,-32) and myproc wants 10
   below it. *)
Notation fdalloc_stack := (14%nat) (only parsing).
(* ===================================================================== *)
(*  What fdalloc COMPUTES: the free descriptors, least first.             *)
(* ===================================================================== *)
(* [fd_frees_from i fs] lists the indices of the null entries of [fs],
   numbering the first entry [i].  A fixpoint rather than a [filter] over
   [seq] because every fact below is then one induction on the list, and
   because the accumulator [i] is literally the loop counter fdalloc keeps
   in a0. *)
Fixpoint fd_frees_from (i : nat) (fs : list (mword 64)) : list nat :=
  match fs with
  | [] => []
  | v :: fs' =>
      if decide (v = (zero_reg : mword 64))
      then i :: fd_frees_from (S i) fs'
      else fd_frees_from (S i) fs'
  end.

Definition fd_frees (fs : list (mword 64)) : list nat := fd_frees_from 0%nat fs.

(* the head is a real index, and the entry there really is null *)
Lemma fd_frees_from_head (fs : list (mword 64)) (i j : nat) (l : list nat) :
  fd_frees_from i fs = j :: l -> (i <= j)%nat /\ fs !! (j - i)%nat = Some (zero_reg : mword 64).
Proof.
  revert i j l. induction fs as [|a fs' IH]; intros i j l Heq; [discriminate|].
  cbn in Heq. case_decide as Ha.
  - injection Heq as Hij _. subst i a.
    rewrite Nat.sub_diag. split; [lia|reflexivity].
  - destruct (IH _ _ _ Heq) as [Hle Hlk].
    split; [lia|].
    replace (j - i)%nat with (S (j - S i))%nat by lia.
    exact Hlk.
Qed.

Lemma fd_frees_head (fs : list (mword 64)) (j : nat) (l : list nat) :
  fd_frees fs = j :: l -> fs !! j = Some (zero_reg : mword 64).
Proof.
  intro Heq. destruct (fd_frees_from_head fs 0%nat j l Heq) as [_ Hlk].
  by rewrite Nat.sub_0_r in Hlk.
Qed.

(* FILLING THE HEAD POPS IT.  Writing anything non-null into the least free
   descriptor leaves exactly the remaining free descriptors -- which is what
   makes two successive fdalloc calls compose. *)
Lemma fd_frees_from_insert (fs : list (mword 64)) (i j : nat) (l : list nat) (v : mword 64) :
  v <> (zero_reg : mword 64) ->
  fd_frees_from i fs = j :: l ->
  fd_frees_from i (<[(j - i)%nat := v]> fs) = l.
Proof.
  revert i j l. induction fs as [|a fs' IH]; intros i j l Hv Heq; [discriminate|].
  cbn in Heq. case_decide as Ha.
  - injection Heq as Hij Htl. subst i l.
    rewrite Nat.sub_diag. cbn.
    by case_decide.
  - destruct (fd_frees_from_head _ _ _ _ Heq) as [Hle _].
    replace (j - i)%nat with (S (j - S i))%nat by lia.
    cbn. case_decide; [contradiction|].
    by apply IH.
Qed.

Lemma fd_frees_insert (fs : list (mword 64)) (j : nat) (l : list nat) (v : mword 64) :
  v <> (zero_reg : mword 64) ->
  fd_frees fs = j :: l ->
  fd_frees (<[j := v]> fs) = l.
Proof.
  intros Hv Heq. unfold fd_frees in *.
  rewrite -(Nat.sub_0_r j). by apply fd_frees_from_insert.
Qed.

(* the empty case: no descriptor is free *)
Lemma fd_frees_from_nil (fs : list (mword 64)) (i k : nat) (v : mword 64) :
  fd_frees_from i fs = [] -> fs !! k = Some v -> v <> (zero_reg : mword 64).
Proof.
  revert i k. induction fs as [|a fs' IH]; intros i k Heq Hlk; [by destruct k|].
  cbn in Heq. case_decide; [discriminate|].
  destruct k as [|k']; cbn in Hlk.
  - by injection Hlk as <-.
  - exact (IH _ _ Heq Hlk).
Qed.

Lemma fd_frees_nil (fs : list (mword 64)) (k : nat) (v : mword 64) :
  fd_frees fs = [] -> fs !! k = Some v -> v <> (zero_reg : mword 64).
Proof. apply (fd_frees_from_nil fs 0%nat k v). Qed.

(* the head is in range -- an [int] fdalloc can return, and a descriptor
   [proc_priv] really has *)
Lemma fd_frees_head_lt (fs : list (mword 64)) (j : nat) (l : list nat) :
  fd_frees fs = j :: l -> (j < length fs)%nat.
Proof.
  intro Heq. apply lookup_lt_is_Some_1. exists (zero_reg : mword 64).
  exact (fd_frees_head fs j l Heq).
Qed.

Section SpecFdalloc.
  Context `{!riscvGS Σ, !lockG Σ, !fileG Σ, !fdslotG Σ, !irefslotG Σ}.

  (* fdalloc's result, keyed by the returned a0.  The two arms are decided
     by the process's own descriptor array, so the disjunction is a CASE
     ANALYSIS on [fd_frees], not an unconstrained choice. *)
  Definition fdalloc_post (γf : gname) (p : mword 64)
      (V : pprivate) (D : gset nat) (k : nat) (r : mword 64) : iProp Σ :=
    ((* the table is full: nothing happened *)
     ⌜r = (mword_of_int (-1) : mword 64) /\ fd_frees (pv_ofile V) = []⌝ ∗
       proc_ofiles_owe γf p (pv_ofile V) D
     ∨
     (* the least free descriptor now names the file.  Two things changed: the
        unit that descriptor used to own comes back to the caller, and the
        descriptor now OWES a payload -- it names a file whose reference the
        caller still holds. *)
     ∃ (fd : nat) (l : list nat),
       ⌜r = (mword_of_int (Z.of_nat fd) : mword 64) /\
        fd_frees (pv_ofile V) = fd :: l⌝ ∗
       proc_ofiles_owe γf p (pv_ofile (upd_ofile V fd (fnode k)))
         ({[fd]} ∪ D) ∗ fd_slot)%I.

End SpecFdalloc.

Definition wp_fdalloc_sconf_body `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !irefslotG Σ, !fileG Σ} `{GEN : GenId} `{CID : CpuId}
    (γf : gname) (k : nat) (D : gset nat)
    (m : regfile) (av : nat) (n : nat) (eb : bool) (p : mword 64)
    (pid : mword 32) (V : pprivate) (b : bool) (lks : gset string) :=
  let pcE : mword 64 := mword_of_int KernelSyms.fdalloc in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  (* a0 is the file to install *)
  m !!! Regidx (mword_of_int 10 : mword 5) = fnode k ->
  (k < NFILE)%nat ->
  (* push_off's transient noff increment stays in int range (myproc) *)
  (Z.of_nat n + 1 < 2 ^ 31)%Z ->
  (fdalloc_stack <= av)%nat ->
  sie_cap_gpr m av b p -∗
  cpu_own n eb p b lks -∗
  kernel_text -∗ kernel_data -∗ pc_is pcE -∗
  (* the block SPLIT at the fd table: fdalloc needs the core only to reach
     myproc's tier, and the array in whatever loan state the caller left it *)
  proc_priv_core p pid V -∗
  proc_ofiles_owe γf p (pv_ofile V) D -∗
  wp_next b p (fun (CID : CpuId) =>
    ∀ mf : regfile,
      ⌜callee_saved m mf⌝ -∗
      sie_cap_gpr mf av b p -∗
      cpu_own n eb p b lks -∗
      pc_is ret_tgt -∗
      proc_priv_core p pid V -∗
      fdalloc_post γf p V D k (mf !!! Regidx (mword_of_int 10 : mword 5)) -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type FDALLOC.
  Parameter wp_fdalloc_sconf :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !irefslotG Σ, !fileG Σ} `{GEN : GenId} `{CID : CpuId} (γf : gname) (k : nat) (D : gset nat)
      (m : regfile) (av : nat) (n : nat) (eb : bool) (p : mword 64)
      (pid : mword 32) (V : pprivate) (b : bool) (lks : gset string),
      wp_fdalloc_sconf_body γf k D m av n eb p pid V b lks.
End FDALLOC.
