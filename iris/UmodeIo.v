(* UmodeIo.v -- the xv6 syscall protocol AT I/O DEPTH: the arms a verified
   process needs when what it DOES, not merely that it steps, is the point
   (claude-notes/projects/user-sh.md).

   UmodeSyscall.v's [xv6_sys_protocol] is the COARSE protocol: its returning
   arms say only "a0 becomes some value, everything else is intact".  That
   is enough for a process whose theorem is safety (sync, echo), and it is
   deliberately as weak as the unproven kernel side allows.  It is NOT
   enough to state

     "sh, given `echo Hello world!` on fd 0, execs (\"echo\", [\"echo\",
      \"Hello\", \"world!\"])"

   because nothing in it can mention the INPUT, and nothing can observe the
   arguments of an [exec].  This file adds the arms that can:

     - fd 0 is a GHOST STREAM ([ustdin]) the process owns.  [read] consumes
       a prefix of it and writes those bytes into the caller's buffer, so a
       theorem may fix what the program reads.  (fd 1/2 deserve the mirror
       treatment -- an output stream [write] appends to -- and that is what
       will eventually let "the console prints Hello world!" be stated; it
       is deliberately NOT here, because sh's prompt is not part of this
       theorem and adding it would mean reworking echo's proof.)
     - [exec]'s arm demands [uexec_args] (UmodeAbi.v): the path and argv
       laid out in memory, BY CONTENT.  Discharging it is what makes a
       process's theorem say which program it runs with which arguments.
     - [sbrk] hands the process ownership of a fresh slice of a heap region
       that is ALREADY MAPPED in [pt].  This is the one modelling choice
       that is weaker than xv6: the real [sbrk] grows the address space,
       which would make [pt] mutable and ripple through every contract in
       the tier.  Pinning the heap in [pt] up front keeps [pt] fixed, and
       the process cannot tell the difference -- it only ever sees fresh
       bytes at successive addresses.

   THREE MORE ASSUMPTIONS ARE STATED, NOT HIDDEN, because each of them is a
   kernel property this development has not proved and because each one, if
   dropped, drags in a failure path that is not what the theorem is about:

     [IoFork] never returns -1  -- else fork1() panics into vprintf;
     [IoOpen] returns a fd >= 3 -- else sh's fd-priming loop is unbounded;
     [IoExec] does not return   -- else runcmd() reports failure via
                                   fprintf/vprintf.

   Each is one conjunct in one arm, and each is exactly the shape a real
   kernel-side spec would discharge. *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import invariants ghost_var.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import RegFile.
Require Import UserPtTree UserExec.
Require Import UmodeCap UmodeAbi UmodeSyscall.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* §1 The two image effects a syscall can have.                           *)
(* ===================================================================== *)

(* [M'] is [M] with the bytes [bs] written at [a] and nothing else changed *)
Definition uM_written (M M' : gmap Z (bv 8)) (a : Z) (bs : list (bv 8)) : Prop :=
  (forall (j : nat) (b : bv 8), bs !! j = Some b -> M' !! (a + Z.of_nat j) = Some b) /\
  (forall k : Z, (k < a \/ a + Z.of_nat (length bs) <= k) -> M' !! k = M !! k) /\
  (forall k : Z, is_Some (M !! k) -> is_Some (M' !! k)).

(* [M'] is [M] plus [n] fresh bytes at [b] -- what [sbrk] hands over *)
Definition uM_grown (M M' : gmap Z (bv 8)) (b n : Z) : Prop :=
  (forall j : Z, 0 <= j < n -> exists v : bv 8, M' !! (b + j) = Some v) /\
  (forall k : Z, (k < b \/ b + n <= k) -> M' !! k = M !! k) /\
  (forall k : Z, is_Some (M !! k) -> is_Some (M' !! k)).

Lemma uM_written_dom (M M' : gmap Z (bv 8)) (a : Z) (bs : list (bv 8)) :
  uM_written M M' a bs -> forall k : Z, is_Some (M !! k) -> is_Some (M' !! k).
Proof. intros (_ & _ & H). exact H. Qed.

Lemma uM_grown_dom (M M' : gmap Z (bv 8)) (b n : Z) :
  uM_grown M M' b n -> forall k : Z, is_Some (M !! k) -> is_Some (M' !! k).
Proof. intros (_ & _ & H). exact H. Qed.

(* both leave everything outside their own window alone, which is what
   carries [uargs] / [ucstr] / [uv_rd] / [echo-style image inclusions]
   across a syscall (UmodeAbi's [uM_only] transports) *)
Lemma uM_written_only (M M' : gmap Z (bv 8)) (a : Z) (bs : list (bv 8)) :
  uM_written M M' a bs -> uM_only M M' a (Z.of_nat (length bs)).
Proof. intros (_ & Hoff & Hdom). split; [ exact Hdom | exact Hoff ]. Qed.

Lemma uM_grown_only (M M' : gmap Z (bv 8)) (b n : Z) :
  uM_grown M M' b n -> uM_only M M' b n.
Proof. intros (_ & Hoff & Hdom). split; [ exact Hdom | exact Hoff ]. Qed.

(* ===================================================================== *)
(* §2 The ghost state: the input stream and the heap break.               *)
(* ===================================================================== *)

Class uioG (Σ : gFunctors) := {
  uio_stdinG :: ghost_varG Σ (list (bv 8));
  uio_brkG   :: ghost_varG Σ Z;
}.

Section UmodeIoGhost.
  Context `{!uioG Σ}.

  (* the bytes fd 0 has yet to deliver.  Exclusive: only the process reads
     its own stdin, and the arm below is the only thing that moves it. *)
  Definition ustdin (g : gname) (s : list (bv 8)) : iProp Σ :=
    ghost_var g 1 s.

  (* the current program break inside the heap region *)
  Definition ubrk (g : gname) (b : Z) : iProp Σ :=
    ghost_var g 1 b.

  Lemma ustdin_excl (g : gname) (s s' : list (bv 8)) :
    ustdin g s -∗ ustdin g s' -∗ ⌜False⌝.
  Proof.
    iIntros "H1 H2".
    iDestruct (ghost_var_valid_2 with "H1 H2") as %[Hv _].
    iPureIntro. by apply (Qp.not_add_le_l 1 1).
  Qed.

  (* the stream moves only through the [read] arm *)
  Lemma ustdin_update (g : gname) (s s' : list (bv 8)) :
    ustdin g s ==∗ ustdin g s'.
  Proof. apply ghost_var_update. Qed.

  Lemma ubrk_update (g : gname) (b b' : Z) :
    ubrk g b ==∗ ubrk g b'.
  Proof. apply ghost_var_update. Qed.
End UmodeIoGhost.

(* ===================================================================== *)
(* §3 The arms.                                                           *)
(* ===================================================================== *)

Inductive uio_sem : Type :=
  | IoRead            (* read(fd, buf, n)      -- consumes stdin, writes buf *)
  | IoWrite           (* write(fd, buf, n)     -- reads buf, returns *)
  | IoOpen            (* open(path, flags)     -- reads path, returns fd >= 3 *)
  | IoPureRet         (* close / dup *)
  | IoWaitNull        (* wait(0)               -- see the arm; wait(p) is NOT this *)
  | IoPathRet         (* chdir(path)           -- reads a path, returns *)
  | IoFork            (* fork()                -- returns 0 or a positive pid *)
  | IoExec            (* exec(path, argv)      -- reads both; does not return *)
  | IoSbrk            (* sbrk(n, eager)        -- hands over n fresh bytes *)
  | IoNoRet           (* exit *)
  | IoUnused.

Section UmodeIo.
  Context `{!riscvGS Σ} `{!uioG Σ}.
  Context `{GEN : GenId}.
  Context (C : ucfg) (pt : uptd).
  Context (gin gbrk : gname).          (* stdin stream, program break *)
  Context (hbase hlen : Z).            (* the heap region, mapped in [pt] *)

  (* the resume continuation every returning arm shares *)
  Definition uio_ret (g : regfile) (va : mword 64)
      (M : gmap Z (bv 8)) : iProp Σ :=
    (∀ (CID : CpuId) (ret : mword 64),
       uv_run C pt M (<[Regidx a0_idx := ret]> g) (add_vec_int va 4) -∗
       WP (Loop : expr riscv_lang))%I.

  (* a NUL-terminated string argument, readable *)
  Definition uio_str_arg (M : gmap Z (bv 8)) (p : Z) : Prop :=
    exists len : Z, ucstr M p len /\ uv_rd pt M p (len + 1).

  Definition uio_arm (s : uio_sem) (g : regfile) (va : mword 64)
      (M : gmap Z (bv 8)) (Q : list (bv 8) -> list (list (bv 8)) -> iProp Σ)
      : iProp Σ :=
    match s with
    | IoPureRet => uio_ret g va M
    | IoNoRet   => emp%I
    | IoUnused  => False%I

    (* [wait(p)] with p <> 0 WRITES the exit status through p, so an arm
       claiming the image is unchanged would be false for it and could never
       be discharged on the kernel side.  This arm is a PARTIAL specification
       and says so: it covers wait(0) only, which is the only form sh (and
       init) ever calls.  Generalising it means an image effect like
       [IoRead]'s. *)
    | IoWaitNull =>
        (⌜uint (g !!! Regidx a0_idx) = 0⌝ ∗ uio_ret g va M)%I

    (* [chdir] READS its path argument; an arm that demanded nothing about it
       would oblige the kernel to cope with a garbage pointer. *)
    | IoPathRet =>
        (⌜uio_str_arg M (uint (g !!! Regidx a0_idx))⌝ ∗ uio_ret g va M)%I

    | IoWrite =>
        (⌜uv_rd pt M (uint (g !!! Regidx a1_idx)) (uint (g !!! Regidx a2_idx))⌝ ∗
         uio_ret g va M)%I

    | IoOpen =>
        (⌜uio_str_arg M (uint (g !!! Regidx a0_idx))⌝ ∗
         ∀ (CID : CpuId) (ret : mword 64),
           ⌜3 <= sint ret⌝ -∗          (* ASSUMED: fds 0,1,2 are already open *)
           uv_run C pt M (<[Regidx a0_idx := ret]> g) (add_vec_int va 4) -∗
           WP (Loop : expr riscv_lang))%I

    | IoFork =>
        (∀ (CID : CpuId) (ret : mword 64),
           ⌜uint ret = 0 \/ 0 < sint ret⌝ -∗   (* ASSUMED: fork does not fail *)
           uv_run C pt M (<[Regidx a0_idx := ret]> g) (add_vec_int va 4) -∗
           WP (Loop : expr riscv_lang))%I

    (* THE observable one.  No continuation: exec does not come back
       (ASSUMED -- the failure path is runcmd's fprintf). *)
    | IoExec =>
        (∃ (path : list (bv 8)) (args : list (list (bv 8))),
           ⌜uexec_args M (uint (g !!! Regidx a0_idx))
                         (uint (g !!! Regidx a1_idx)) path args⌝ ∗
           Q path args)%I

    | IoRead =>
        (∃ str : list (bv 8),
           ustdin gin str ∗
           ⌜uv_wr pt M (uint (g !!! Regidx a1_idx)) (uint (g !!! Regidx a2_idx))⌝ ∗
           ∀ (CID : CpuId) (k : nat) (M' : gmap Z (bv 8)),
             ⌜(k <= length str)%nat⌝ -∗
             ⌜Z.of_nat k <= uint (g !!! Regidx a2_idx)⌝ -∗
             ⌜(k = 0)%nat -> str = []⌝ -∗       (* only EOF returns nothing *)
             ⌜uM_written M M' (uint (g !!! Regidx a1_idx)) (take k str)⌝ -∗
             ustdin gin (drop k str) -∗
             uv_run C pt M' (<[Regidx a0_idx := (mword_of_int (Z.of_nat k) : mword 64)]> g)
               (add_vec_int va 4) -∗
             WP (Loop : expr riscv_lang))%I

    | IoSbrk =>
        (∃ b : Z,
           ubrk gbrk b ∗
           ⌜hbase <= b /\ 0 <= sint (g !!! Regidx a0_idx) /\
            b + sint (g !!! Regidx a0_idx) <= hbase + hlen⌝ ∗
           ∀ (CID : CpuId) (M' : gmap Z (bv 8)),
             ⌜uM_grown M M' b (sint (g !!! Regidx a0_idx))⌝ -∗
             ubrk gbrk (b + sint (g !!! Regidx a0_idx)) -∗
             uv_run C pt M' (<[Regidx a0_idx := (mword_of_int b : mword 64)]> g)
               (add_vec_int va 4) -∗
             WP (Loop : expr riscv_lang))%I
    end.

End UmodeIo.

(* ===================================================================== *)
(* §4 THE TABLE.                                                          *)
(* ===================================================================== *)

Definition xv6_io_sem (n : Z) : uio_sem :=
  if bool_decide (n = SYS_read)  then IoRead
  else if bool_decide (n = SYS_write) then IoWrite
  else if bool_decide (n = SYS_open)  then IoOpen
  else if bool_decide (n = SYS_close) then IoPureRet
  else if bool_decide (n = SYS_dup)   then IoPureRet
  else if bool_decide (n = SYS_chdir) then IoPathRet
  else if bool_decide (n = SYS_wait)  then IoWaitNull
  else if bool_decide (n = SYS_fork)  then IoFork
  else if bool_decide (n = SYS_exec)  then IoExec
  else if bool_decide (n = SYS_sbrk)  then IoSbrk
  else if bool_decide (n = SYS_exit)  then IoNoRet
  else IoUnused.

Definition xv6_io_protocol `{!riscvGS Σ} `{!uioG Σ} `{GEN : GenId}
    (C : ucfg) (pt : uptd) (gin gbrk : gname) (hbase hlen : Z)
    (Q : list (bv 8) -> list (list (bv 8)) -> iProp Σ) : usys_protocol Σ :=
  fun n g va M => uio_arm C pt gin gbrk hbase hlen (xv6_io_sem n) g va M Q.

(* the dispatch facts the stub proofs use *)
Lemma xv6_io_sem_read  : xv6_io_sem SYS_read  = IoRead.    Proof. reflexivity. Qed.
Lemma xv6_io_sem_write : xv6_io_sem SYS_write = IoWrite.   Proof. reflexivity. Qed.
Lemma xv6_io_sem_open  : xv6_io_sem SYS_open  = IoOpen.    Proof. reflexivity. Qed.
Lemma xv6_io_sem_close : xv6_io_sem SYS_close = IoPureRet. Proof. reflexivity. Qed.
Lemma xv6_io_sem_dup   : xv6_io_sem SYS_dup   = IoPureRet. Proof. reflexivity. Qed.
Lemma xv6_io_sem_chdir : xv6_io_sem SYS_chdir = IoPathRet.  Proof. reflexivity. Qed.
Lemma xv6_io_sem_wait  : xv6_io_sem SYS_wait  = IoWaitNull. Proof. reflexivity. Qed.
Lemma xv6_io_sem_fork  : xv6_io_sem SYS_fork  = IoFork.    Proof. reflexivity. Qed.
Lemma xv6_io_sem_exec  : xv6_io_sem SYS_exec  = IoExec.    Proof. reflexivity. Qed.
Lemma xv6_io_sem_sbrk  : xv6_io_sem SYS_sbrk  = IoSbrk.    Proof. reflexivity. Qed.
Lemma xv6_io_sem_exit  : xv6_io_sem SYS_exit  = IoNoRet.   Proof. reflexivity. Qed.
