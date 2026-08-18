(* UmodeInitIo.v -- the xv6 syscall protocol `init' runs under
   (claude-notes/projects/user-init.md).

   THREE PROTOCOLS NOW EXIST, at three depths, and this is the third:

     [xv6_sys_protocol]  (UmodeSyscall.v)  -- the COARSE one.  A returning
       arm says only "a0 becomes some value, everything else is intact".
       sync and echo, whose theorems are pure safety, use it.
     [xv6_io_protocol]   (UmodeIo.v)       -- I/O depth: fd 0 is a ghost
       stream, [sbrk] hands out a pre-mapped heap, and [exec]'s arguments
       are observable.  sh uses it.  Three of its arms carry an explicit
       ASSUMPTION as one conjunct -- fork never fails, open returns a fd
       >= 3, exec does not return -- because sh's theorem is about one
       execution and each failure path drags in vprintf.
     [xv6_init_protocol] (here)            -- NO SUCH ASSUMPTION.  init
       handles every failure itself: it [mknod]s the console when [open]
       fails, and prints a diagnostic and exits when fork, exec or wait
       does.  Since init's theorem covers all of those arms, every arm
       here returns an ARBITRARY value, and [exec] has a continuation.

   THE SHAPE.  A protocol is a function from syscall number to the iProp
   the process must SUPPLY at the [ecall].  UmodeSyscall.v and UmodeIo.v
   route that through an [Inductive] of arm shapes plus a match; here the
   arms are ordinary named definitions and the table applies them
   directly.  That is the shape those two should collapse into (an
   inductive of arm names buys nothing that a definition per arm does not,
   and it makes every new arm a change to a type three files match on) --
   recorded as a debt in claude-notes/projects/user-init.md rather than
   done here, because sh's proofs are in flight over the existing match.

   WHAT THE THEOREM OBSERVES.  Two arms carry an observer the process must
   discharge, which is where init's theorem gets its content:

     [Q path args] at [exec]  -- the path and argv laid out in memory BY
       CONTENT ([uexec_args], UmodeAbi.v).  Instantiated with the equality,
       this says the child execs "sh" with argv ["sh"].
     [W fd bs] at [write]     -- the fd and the exact bytes of the buffer
       handed over.  Instantiated at init's four literals, this says every
       write init performs is one byte of one of its own messages.

   The observers are supplied PERSISTENTLY by init's contracts, not
   linearly as sh's [Q] is.  That is forced, not a weakening: init's
   restart loop runs forever, so the exec is reached once per iteration
   and a linear right could only cover the first.  The content survives --
   a process owning only [box]Q at ("sh", ["sh"]) can discharge exec's arm
   only if those ARE the arguments in memory.

   WHAT IS STILL NOT OBSERVED.  Nothing here says the bytes reach a
   console: fd 1 is whatever [dup] made it, and connecting a descriptor to
   a device needs the kernel's file table, which this tier does not model.
   [W] observes the argument of each [write], not the effect.  The output
   STREAM that would let "the console printed init: starting sh" be stated
   is the same piece UmodeIo.v defers for fd 1/2, and it is still deferred.

   ONE ARM IS A PARTIAL SPECIFICATION, and says so: [uinit_arm_waitnull]
   requires a0 = 0.  [wait(p)] with p /= 0 writes the exit status through
   p, so an arm claiming the image is unchanged would be FALSE for it and
   undischargeable on the kernel side.  init only ever calls [wait(0)], so
   the arm covers its use and refuses the other.  (UmodeIo.v's
   [xv6_io_sem SYS_wait = IoPureRet] makes exactly the over-strong claim;
   sh also only calls [wait(0)], so the fix there is the same conjunct.) *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import RegFile.
Require Import UserPtTree UserExec.
Require Import UmodeMem UmodeCap UmodeAbi UmodeSyscall UmodeIo.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* §1 A byte window by CONTENT, with no NUL.                              *)
(*                                                                        *)
(* [ustr_at]'s first conjunct, on its own: what a [write] buffer is.       *)
(* RELOCATION DEBT: reads naturally beside [ustr_at] in UmodeAbi.v; kept   *)
(* here so adding it does not rebuild the whole Umode tier.               *)
(* ===================================================================== *)

Definition ubuf_at (M : gmap Z (bv 8)) (a : Z) (bs : list (bv 8)) : Prop :=
  forall (j : nat) (b : bv 8), bs !! j = Some b -> M !! (a + Z.of_nat j) = Some b.

Lemma ustr_at_buf (M : gmap Z (bv 8)) (a : Z) (bs : list (bv 8)) :
  ustr_at M a bs -> ubuf_at M a bs.
Proof. intros [H _]. exact H. Qed.

(* a one-byte window, which is every buffer [putc] hands over *)
Lemma ubuf_at_1 (M : gmap Z (bv 8)) (a : Z) (b : bv 8) :
  M !! a = Some b -> ubuf_at M a [b].
Proof.
  intros Hb j c Hj.
  destruct j as [ | j' ]; cbn in Hj; [ | destruct j'; cbn in Hj; discriminate ].
  injection Hj as ->. rewrite Z.add_0_r. exact Hb.
Qed.

(* ===================================================================== *)
(* §2 The arms.                                                           *)
(* ===================================================================== *)

Section UmodeInitIo.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId}.
  Context (C : ucfg) (pt : uptd).
  (* the two observers *)
  Context (Q : list (bv 8) -> list (list (bv 8)) -> iProp Σ).
  Context (W : Z -> list (bv 8) -> iProp Σ).

  (* --- dup, fork: return an arbitrary value, touch no user memory ----- *)
  Definition uinit_arm_pureret (g : regfile) (va : mword 64)
      (M : gmap Z (bv 8)) : iProp Σ :=
    usys_ret C pt g va M.

  (* --- open, mknod: read a NUL-terminated path at a0, then return an
     arbitrary value (a fd, or -1).  NO fd >= 3 assumption: init is the
     process that CREATES fds 0/1/2, so [xv6_io_protocol]'s [IoOpen] arm
     would be assuming something false about this program. ------------- *)
  Definition uinit_arm_strret (g : regfile) (va : mword 64)
      (M : gmap Z (bv 8)) : iProp Σ :=
    (⌜uio_str_arg pt M (uint (g !!! Regidx a0_idx))⌝ ∗
     usys_ret C pt g va M)%I.

  (* --- wait(0): the null-status case only (see the header) ------------ *)
  Definition uinit_arm_waitnull (g : regfile) (va : mword 64)
      (M : gmap Z (bv 8)) : iProp Σ :=
    (⌜uint (g !!! Regidx a0_idx) = 0⌝ ∗
     usys_ret C pt g va M)%I.

  (* --- write(fd, buf, n): the buffer is readable AND its bytes are
     named, which is what [W] observes. --------------------------------- *)
  Definition uinit_arm_write (g : regfile) (va : mword 64)
      (M : gmap Z (bv 8)) : iProp Σ :=
    (⌜uv_rd pt M (uint (g !!! Regidx a1_idx)) (uint (g !!! Regidx a2_idx))⌝ ∗
     (∃ bs : list (bv 8),
        ⌜ubuf_at M (uint (g !!! Regidx a1_idx)) bs /\
         Z.of_nat (length bs) = uint (g !!! Regidx a2_idx)⌝ ∗
        W (uint (g !!! Regidx a0_idx)) bs) ∗
     usys_ret C pt g va M)%I.

  (* --- exec(path, argv): observable, AND it may come back.  On success
     the kernel discards the continuation; on failure it returns -1 and
     init prints a diagnostic and exits, which is why no "exec does not
     return" assumption is needed.  [Q] is spent on the ATTEMPT -- that is
     what the arm says, and it is the honest reading. ------------------- *)
  Definition uinit_arm_execret (g : regfile) (va : mword 64)
      (M : gmap Z (bv 8)) : iProp Σ :=
    (∃ (path : list (bv 8)) (args : list (list (bv 8))),
       ⌜uexec_args M (uint (g !!! Regidx a0_idx))
                     (uint (g !!! Regidx a1_idx)) path args⌝ ∗
       Q path args ∗ usys_ret C pt g va M)%I.

  (* ------------------------------------------------------------------- *)
  (* §3 THE TABLE.  Every syscall init issues, and nothing else: an        *)
  (* unlisted number's arm is [False], so a verified process simply cannot *)
  (* be proven to invoke it.                                              *)
  (* ------------------------------------------------------------------- *)
  Definition xv6_init_protocol : usys_protocol Σ :=
    fun n g va M =>
      if bool_decide (n = SYS_write) then uinit_arm_write g va M
      else if bool_decide (n = SYS_open) then uinit_arm_strret g va M
      else if bool_decide (n = SYS_mknod) then uinit_arm_strret g va M
      else if bool_decide (n = SYS_dup) then uinit_arm_pureret g va M
      else if bool_decide (n = SYS_fork) then uinit_arm_pureret g va M
      else if bool_decide (n = SYS_wait) then uinit_arm_waitnull g va M
      else if bool_decide (n = SYS_exec) then uinit_arm_execret g va M
      else if bool_decide (n = SYS_exit) then emp%I
      else False%I.

  (* the dispatch facts the stub proofs use.  One per number, so a stub
     never unfolds the table. *)
  Lemma init_proto_write (g : regfile) (va : mword 64) (M : gmap Z (bv 8)) :
    xv6_init_protocol SYS_write g va M = uinit_arm_write g va M.
  Proof. reflexivity. Qed.
  Lemma init_proto_open (g : regfile) (va : mword 64) (M : gmap Z (bv 8)) :
    xv6_init_protocol SYS_open g va M = uinit_arm_strret g va M.
  Proof. reflexivity. Qed.
  Lemma init_proto_mknod (g : regfile) (va : mword 64) (M : gmap Z (bv 8)) :
    xv6_init_protocol SYS_mknod g va M = uinit_arm_strret g va M.
  Proof. reflexivity. Qed.
  Lemma init_proto_dup (g : regfile) (va : mword 64) (M : gmap Z (bv 8)) :
    xv6_init_protocol SYS_dup g va M = uinit_arm_pureret g va M.
  Proof. reflexivity. Qed.
  Lemma init_proto_fork (g : regfile) (va : mword 64) (M : gmap Z (bv 8)) :
    xv6_init_protocol SYS_fork g va M = uinit_arm_pureret g va M.
  Proof. reflexivity. Qed.
  Lemma init_proto_wait (g : regfile) (va : mword 64) (M : gmap Z (bv 8)) :
    xv6_init_protocol SYS_wait g va M = uinit_arm_waitnull g va M.
  Proof. reflexivity. Qed.
  Lemma init_proto_exec (g : regfile) (va : mword 64) (M : gmap Z (bv 8)) :
    xv6_init_protocol SYS_exec g va M = uinit_arm_execret g va M.
  Proof. reflexivity. Qed.
  Lemma init_proto_exit (g : regfile) (va : mword 64) (M : gmap Z (bv 8)) :
    xv6_init_protocol SYS_exit g va M = emp%I.
  Proof. reflexivity. Qed.

End UmodeInitIo.
