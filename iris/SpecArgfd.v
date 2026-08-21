(* SpecArgfd.v -- the public interface of argfd(), stated independently of
   its proof.  Requires only the definitional layer -- never a whole-function
   proof file -- so every function proof can be checked in parallel.

     static int argfd(int n, int *pfd, struct file **pf) {
       int fd; struct file *f;
       argint(n, &fd);
       if (fd < 0 || fd >= NOFILE || (f = myproc()->ofile[fd]) == 0)
         return -1;
       if (pfd) *pfd = fd;
       if (pf)  *pf  = f;
       return 0;
     }

   @ KernelSyms.argfd = 0x80004a04, 29 instructions (a 48-byte frame; the
   [int fd] local lives at s0-36, which is why the caller's [pfd] is a
   SEPARATE cell from the one argint writes).

     +0x00  7179        c.addi     sp,sp,-48
     +0x02  f406/f022/ec26/e84a    c.sdsp ra/s0/s1/s2
     +0x0a  1800        c.addi4spn s0,sp,48
     +0x0c  892e        c.mv       s2,a1          s2 := pfd (survives)
     +0x0e  84b2        c.mv       s1,a2          s1 := pf  (survives)
     +0x10  fdc40593    addi       a1,s0,-36      &fd
     +0x14  dedfd0ef    jal        ra,argint
     +0x18  fdc42703    lw         a4,-36(s0)     a4 := fd
     +0x1c  47bd        c.li       a5,15
     +0x1e  02e7ea63    bltu       a5,a4,+52      15 <u fd -> return -1
     +0x22  edffc0ef    jal        ra,myproc
     ...    lw/slli/addi/add/ld    a5 := p->ofile[fd]
     +0x36  c385        c.beqz     a5,+...        f == 0 -> return -1
     ...    the two guarded out-stores, then [c.li a0,0]

   THE CONTRACT.  argfd is the syscall layer's fd lookup, and its result is a
   FUNCTION of its inputs -- the syscall argument [v] and the calling
   process's descriptor array -- so the postcondition is stated by
   [arg_fd] rather than as an unconstrained "succeeds or not" disjunction:
   a kernel that always returned -1 would not satisfy this spec.

   WHAT IS AND IS NOT TAKEN.  No reference is taken: argfd hands back the
   POINTER stored in the descriptor and leaves the process's own [file_ref]
   where it was, inside [proc_priv].  A caller that only borrows the file
   (fileread / filewrite / filestat) projects the reference out with
   [ProcInv.proc_priv_ofile] and puts it straight back; a caller that
   REMOVES the descriptor (sys_close) uses the same accessor to walk away
   with it.  That is why the success case reports the descriptor index [fd]
   and the pointer [fv] as PURE data about [pv_ofile V] -- it is exactly
   what [proc_priv_ofile] needs, and it costs argfd no ownership at all.

   [proc_priv] itself (rather than argraw's weaker bare fractions) is the
   honest premise here: the ofile array cannot be reached without it, and the
   index is not known until argint has run.  It is also SUFFICIENT -- since
   the trapframe page moved inside [proc_priv], argfd needs no separate
   resource for the syscall argument at all, only the pure fact saying which
   word of [pv_tf V] it is.

   THE NULL OUT-PARAMETERS.  argfd tests [pfd]/[pf] against 0 before storing,
   because its five callers disagree about which they want: sys_close passes
   both, sys_dup passes [pfd = 0], sys_read passes [pf = 0].
     [pfd] is handled GENERICALLY, by [ofd_out] below -- a null pointer
   carries no resource and its store does not happen -- so this one contract
   serves sys_close and sys_dup alike.  That is strictly weaker than a
   [pfd <> 0] premise, and without it sys_dup could not call argfd at all.
   [pf] still takes the disequality, because no landed caller passes 0 there;
   sys_read will want the same treatment, and it is the same two-line move.
     A caller passing a stack local discharges [pf <> 0] from the stack's own
   geometry ([StackOwn.stack_own_sp_nonzero]), not as an assumption: an address
   the kernel stack occupies is never 0. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExtras.
Require Import InstrBytes.
Require Import RegFile.
Require Import RiscvExtras.
Require Import CalleeSaved KernelText KernelDataInv.
Require Import IntrDefs.
Require Import WpNext.
Require Import ProcGeom CpuOwn.
Require Import FdSlots ProcInv.
Require Import FileInvDefs.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Import Defs.
Local Open Scope Z_scope.


(* argfd's own frame is 6 slots (addi sp,sp,-48); argint wants 18 below it
   (4 for itself, 14 for argraw's) and myproc 10, so 24 covers both calls. *)
Notation argfd_stack := (24%nat) (only parsing).
(* ===================================================================== *)
(*  What argfd COMPUTES.                                                  *)
(* ===================================================================== *)
(* The descriptor named by syscall argument [v] in a process whose ofile
   array is [fs], together with the [struct file *] it holds -- [None] when
   argfd returns -1.  The three failure modes of the source's one
   short-circuiting test, in order:

     - [fd < 0 || fd >= NOFILE]: gcc fuses both halves into the single
       UNSIGNED compare [bltu a5,a4] against 15, which is why the range
       test below is on the SIGNED value of the [int] cell -- a negative
       [fd] sign-extends to a huge unsigned and fails the same compare;
     - the slot is out of the array: impossible for a well-formed
       [proc_priv] (whose array is NOFILE long), but stated so that
       [arg_fd] is total;
     - the descriptor is free ([f == 0]).

   [trunc32] is argint's [c.sw] narrowing, i.e. C's [(int)] conversion of
   argraw's [uint64] -- see SpecArgint.v. *)
Definition arg_fd (v : mword 64) (fs : list (mword 64)) : option (nat * mword 64) :=
  let z := bv_signed (trunc32 v) in
  if decide (0 <= z < Z.of_nat NOFILE) then
    match fs !! Z.to_nat z with
    | Some fv => if decide (fv = (zero_reg : mword 64)) then None else Some (Z.to_nat z, fv)
    | None => None
    end
  else None.

(* the index [arg_fd] reports is in range, and names the pointer it reports *)
Lemma arg_fd_lookup (v : mword 64) (fs : list (mword 64)) (fd : nat) (fv : mword 64) :
  arg_fd v fs = Some (fd, fv) ->
  (fd < NOFILE)%nat /\ fs !! fd = Some fv /\ fv <> (zero_reg : mword 64) /\
  sign_extend' 64 (trunc32 v) = mword_of_int (Z.of_nat fd).
Proof.
  unfold arg_fd. destruct (decide _) as [Hr|]; [| discriminate].
  destruct (fs !! Z.to_nat (bv_signed (trunc32 v))) as [fv0|] eqn:Hlk; [| discriminate].
  destruct (decide _) as [|Hnz]; [discriminate|].
  intros Heq. injection Heq as <- <-.
  assert (Hz : Z.of_nat (Z.to_nat (bv_signed (trunc32 v))) = bv_signed (trunc32 v))
    by (apply Z2Nat.id; exact (proj1 Hr)).
  split; [apply Nat2Z.inj_lt; rewrite Hz; exact (proj2 Hr)|].
  split; [exact Hlk|]. split; [exact Hnz|].
  rewrite Hz. apply sext32_64_moi.
Qed.

Section SpecArgfd.
  Context `{!riscvGS Σ}.
  (* the out-parameters are the CALLER's own locals -- stack cells on its
     frame -- so they ride the caller's regime, not the ambient default. *)

  (* argfd's result, keyed by the returned a0 -- the [filealloc_post]
     shape.  Both disjuncts carry the pure guard, so the caller learns
     WHICH case ran from [arg_fd] alone. *)
  (* THE [int *pfd] OUT-PARAMETER, which may be NULL.  argfd tests it
     ([if (pfd) *pfd = fd]) because its callers disagree: sys_close wants the
     descriptor index and passes a stack local, sys_dup does not and passes 0.
     One contract covers both -- a null pointer carries no resource and the
     store does not happen -- which is strictly more general than taking
     [pfd <> 0] as a premise, and it is what lets sys_dup call argfd at all.
     ([pf] keeps its non-null premise: no landed caller passes 0 there.
     sys_read does, and will want the same treatment.) *)
  Definition ofd_out (a : mword 64) (w : mword 32) : iProp Σ :=
    (if bool_decide (a = (zero_reg : mword 64)) then emp else a ↦₄[KT1] w)%I.

  (* wand-shaped, so proofs compose with iDestruct/iPoseProof rather than
     needing a setoid rewrite inside the proofmode context *)
  Lemma ofd_out_null (a : mword 64) (w : mword 32) :
    a = (zero_reg : mword 64) -> ⊢ ofd_out a w.
  Proof. intro Hz. rewrite /ofd_out bool_decide_true; [|exact Hz]. done. Qed.

  Lemma ofd_out_intro (a : mword 64) (w : mword 32) :
    a <> (zero_reg : mword 64) -> a ↦₄[KT1] w -∗ ofd_out a w.
  Proof.
    intro Hn. rewrite /ofd_out bool_decide_false; [|exact Hn]. iIntros "$".
  Qed.

  Lemma ofd_out_elim (a : mword 64) (w : mword 32) :
    a <> (zero_reg : mword 64) -> ofd_out a w -∗ a ↦₄[KT1] w.
  Proof.
    intro Hn. rewrite /ofd_out bool_decide_false; [|exact Hn]. iIntros "$".
  Qed.

  Definition argfd_post (pfd pf : mword 64) (oldfd : mword 32) (oldf : mword 64)
      (v : mword 64) (fs : list (mword 64)) (r : mword 64) : iProp Σ :=
    (⌜r = (mword_of_int (-1) : mword 64) /\ arg_fd v fs = None⌝ ∗
       ofd_out pfd oldfd ∗ pf ↦₈[KT1] oldf
     ∨ ∃ (fd : nat) (fv : mword 64),
         ⌜r = (zero_reg : mword 64) /\ arg_fd v fs = Some (fd, fv)⌝ ∗
         ofd_out pfd (trunc32 v) ∗ pf ↦₈[KT1] fv)%I.

End SpecArgfd.

Definition wp_argfd_sconf_body `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !irefslotG Σ, !fileG Σ} `{GEN : GenId} `{CID : CpuId} (γf : gname)
    (m : regfile) (av : nat) (n : nat) (eb : bool) (p : mword 64)
    (i : nat) (v : mword 64)
    (pid : mword 32) (V : pprivate) (oldfd : mword 32) (oldf : mword 64) (b : bool) (lks : gset string) :=
  let pcE : mword 64 := mword_of_int KernelSyms.argfd in
  let pfd := m !!! Regidx (mword_of_int 11 : mword 5) in
  let pf := m !!! Regidx (mword_of_int 12 : mword 5) in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  (* the syscall argument index, in range: argraw's panic arm *)
  (i < NARG)%nat ->
  m !!! Regidx (mword_of_int 10 : mword 5) = mword_of_int (Z.of_nat i) ->
  (* the argument itself: word [tf_arg_idx i] of this proc's trapframe page,
     which [proc_priv] carries (so argfd needs no separate resource for it) *)
  pv_tf V !! tf_arg_idx i = Some v ->
  (* [pf] is not null (see [ofd_out] above: [pfd] may be) *)
  pf <> (zero_reg : mword 64) ->
  (Z.of_nat n + 1 < 2 ^ 31)%Z ->
  (argfd_stack <= av)%nat ->
  sie_cap_gpr KT1 m av b p -∗
  cpu_own n eb p b lks -∗
  kernel_text -∗ kernel_data -∗ pc_is pcE -∗
  proc_priv γf p pid V -∗
  ofd_out pfd oldfd -∗
  pf ↦₈[KT1] oldf -∗
  wp_next b p (fun (CID : CpuId) =>
    ∀ mf : regfile,
      ⌜callee_saved m mf⌝ -∗
      sie_cap_gpr KT1 mf av b p -∗
      cpu_own n eb p b lks -∗
      pc_is ret_tgt -∗
      proc_priv γf p pid V -∗
      argfd_post pfd pf oldfd oldf v (pv_ofile V)
        (mf !!! Regidx (mword_of_int 10 : mword 5)) -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type ARGFD.
  Parameter wp_argfd_sconf :
    forall `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !irefslotG Σ, !fileG Σ} `{GEN : GenId} `{CID : CpuId} (γf : gname)
      (m : regfile) (av : nat) (n : nat) (eb : bool) (p : mword 64)
      (i : nat) (v : mword 64)
      (pid : mword 32) (V : pprivate) (oldfd : mword 32) (oldf : mword 64) (b : bool) (lks : gset string),
      wp_argfd_sconf_body γf m av n eb p i v pid V oldfd oldf b lks.
End ARGFD.
