(* ===================================================================== *)
(* UsysMemOk.v -- WHICH USER BYTES A SYSCALL MAY HAVE MOVED, restated on   *)
(* the TRAPFRAME WORD LIST, so that a file below the kernel proofs can     *)
(* import it.                                                              *)
(*                                                                         *)
(* See claude-notes/design/user-wp-slot.md, "The ruled design for the      *)
(* user/kernel trap contract".  [SpecSyscall.sysc_mem_ok V V' M M'] is the *)
(* kernel dispatcher's table -- keyed by the syscall number in the a7 word *)
(* of the entry trapframe -- and it is stated over [pprivate], which lives *)
(* far above the user-execution tier.  [usys_mem_ok] below is THE SAME     *)
(* TABLE stated over the word list alone (plus the return value, which the *)
(* exec row needs), and [UsysMemOkSpec.sysc_mem_ok_usys] -- above          *)
(* SpecSyscall.v -- is the proof that the two agree, so the kernel can     *)
(* discharge this one from the dispatcher's post at milestone J.           *)
(*                                                                         *)
(* THE PERMISSION MAP RIDES BESIDE THE IMAGE.  The key carries the        *)
(* user-visible per-page permission view ([UserPerm.perm_of], the leaf   *)
(* bits with the lazy pages filled in RW), so every row also says how    *)
(* [π] moves: unchanged on the sixteen quiet entries, the four windows   *)
(* and the exec failure arm; sbrk's row is [usys_sbrk_perm], which SAYS  *)
(* WHAT HAPPENS -- the new live pages appear at {X := false; W := true}  *)
(* (the lazy fill; [vmfault] later maps exactly that), or the map is cut *)
(* down to the pages that are still live.  Both are FUNCTIONS OF THE TWO *)
(* SIZES, which alone stay existential: the word list does not carry     *)
(* [pv_sz].                                                              *)
(*                                                                         *)
(* THE ROWS, one for one with [sysc_mem_ok]:                               *)
(*   exec (7)   -- the FAILURE arm only: [r = -1] and the image is intact. *)
(*                 A successful exec never returns to this WP at all: the  *)
(*                 new program's WP is MINTED by exec from the new         *)
(*                 trapframe and image, so the success arm has no row.     *)
(*   sbrk (12)  -- EITHER EXTEND THE MEMORY UP WITH ZEROED PAGES, OR CUT   *)
(*                 THEM DOWN, at an existential pair of sizes: exactly     *)
(*                 what the kernel's table says (the sizes are the entry   *)
(*                 and outgoing records' [pv_sz], which the word list does *)
(*                 not carry).  Tying the old size to the return value     *)
(*                 ([r = a0] on success) is sbrk own contract              *)
(*                 refinement, not this table's.                          *)
(*   wait (3)   -- four bytes at argument 0, the zombie's [xstate].        *)
(*   pipe (4)   -- eight bytes at argument 0, the two fds.                 *)
(*   read (5)   -- at most the caller's own count, at argument 1.          *)
(*   fstat (8)  -- one 24-byte [struct stat], at argument 1.               *)
(*   the other sixteen -- [M' = M].                                        *)
(*                                                                         *)
(* PURE, and deliberately NOT importing SpecSyscall (whose cone is the     *)
(* whole kernel).  The word-index map is ProcGeom.v's ([tf_arg_idx],       *)
(* [tf_epc_idx]); the image algebra is UserPtTree.v's ([umem_wr],          *)
(* [umem_grow], [umem_del]); [pgroundup] on words is ProcPtOwn.v's.        *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap list bitvector.definitions.
Require Import SailStdpp.Base SailStdpp.Values SailStdpp.MachineWord SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types.
Require Import ProcGeom.     (* [tf_arg_idx] / [tf_epc_idx] / [TFWORDS] *)
Require Import TfUser.       (* [tf_ueq] -- the resume-visible word equality *)
Require Import UserPtTree.   (* [umem_wr] / [umem_grow] / [umem_del] *)
Require Import ProcPtOwn.    (* [pgroundup] on words *)
Require Import UserPerm.     (* [uperm] / [uperm_rw] -- the permission view *)
Require Import FdSlots.      (* [fdstate] / [fdtype] -- the descriptor view *)
Local Open Scope Z_scope.

(* ===================================================================== *)
(* SS1 The number, read as the dispatcher reads it.                        *)
(*                                                                         *)
(* [p->trapframe->a7] as a SIGNED 32-bit value (the C reads it into an     *)
(* [int]); trapframe word [tf_arg_idx 7] = 21.  Definitionally             *)
(* [SpecSyscall.sysc_num V] at [tf := pv_tf V].                            *)
(* ===================================================================== *)
Definition usys_num (tf : list (mword 64)) : Z :=
  bv_signed (subrange_vec_dec (tf !!! tf_arg_idx 7) 31 0 : mword 32).

(* the syscall numbers this table names (kernel/syscall.h) *)
Definition USYS_fork : Z := 1.
Definition USYS_exit : Z := 2.
Definition USYS_exec : Z := 7.
Definition USYS_sbrk : Z := 12.

(* ===================================================================== *)
(* SS2 The table.                                                          *)
(* ===================================================================== *)

(* the four entries that write user memory, by number *)
Definition USYS_wait  : Z := 3.
Definition USYS_pipe  : Z := 4.
Definition USYS_read  : Z := 5.
Definition USYS_fstat : Z := 8.

(* ...and the four that move the DESCRIPTOR table (kernel/syscall.h).
   [USYS_pipe] is in both lists, and that is the point: it is the one entry
   that writes user memory AND allocates descriptors, so the two tables have
   to agree about it. *)
Definition USYS_dup   : Z := 10.
Definition USYS_open  : Z := 15.
Definition USYS_close : Z := 21.

(* [read]'s count, as the C reads it: argument 2 into an [int].  The read
   row is the one whose length is not a constant.  Definitionally
   [SpecSyscall.sysc_rdcount V] at [tf := pv_tf V]. *)
Definition usys_rdcount (tf : list (mword 64)) : Z :=
  bv_signed (subrange_vec_dec (tf !!! tf_arg_idx 2) 31 0 : mword 32).

(* sbrk's row on the IMAGE, at the OLD size [szv] and the NEW one [szv'].
   EITHER EXTEND THE MEMORY UP WITH ZEROED PAGES, OR CUT IT DOWN -- the C's
   own two directions, and nothing existential in either.  [umem_grow] IS
   "extend with zeroed bytes" ([UserPtTree.umem_grow M sz = M ∪
   gset_to_gmap 0 (live_set sz)]), and the cut's page count is
   [ProcPtOwn.uvmd_np] of the two sizes -- uvmdealloc's own run length,
   guarded on the shrink actually happening, so the [szv' = szv] arms (a
   failure, [n = 0], and growproc's WRAP sub-case) sit in the first branch
   and read [M' = umem_grow M (uint szv)], which is [M] itself at the lazy
   view ([UserPtTree.umem_grow_id]: every live byte is already recorded). *)
Definition usys_sbrk_img (M M' : gmap Z (bv 8)) (szv szv' : mword 64) : Prop :=
  if decide (uint szv <= uint szv')%Z
  then M' = umem_grow M (uint szv')
  else M' = umem_del M (uint (ProcPtOwn.pgroundup szv'))
                       (4096 * ProcPtOwn.uvmd_np szv szv').

(* ...and on the PERMISSION MAP, and IT COMES OUT TABLE-FREE, which is what
   the U tier needs since it cannot see the page table.

   GROW.  Everything the table maps lies BELOW the old size
   ([ProcPtOwn.um_below], [ProcInv.proc_priv]'s own conjunct), so the pages
   that become live are all unmapped and [UserPerm.perm_of]'s fill supplies
   every one of them at [uperm_rw] -- the "minus the mapped pages" caveat
   [UsysMemOkSpec.perm_of_grow] carries is VACUOUS here.  The eager path,
   which really does map the run, maps it at vmfault's own RW-user leaf, so
   the projection does not notice the difference
   ([UserPerm.perm_of_uptd_ext_sz]).

   SHRINK.  Everything in [π] is inside [live_pages] of the old size (the
   leaves by [um_below], the fill by construction), so cutting the map down
   to the pages that are still live IS dropping the dealloc run
   ([UserPerm.perm_of_del_run]). *)
Definition usys_sbrk_perm (π π' : gmap (mword 27) uperm)
    (szv szv' : mword 64) : Prop :=
  if decide (uint szv <= uint szv')%Z
  then π' = π ∪ gset_to_gmap uperm_rw
                 (live_pages (uint szv') ∖ live_pages (uint szv))
  else π' = base.filter
              (fun kv : mword 27 * uperm => kv.1 ∈ live_pages (uint szv')) π.

(* THE TABLE: syscall [n], entered with trapframe words [tf], returned
   [r], may take the image from [M] to [M'] and the permission map from
   [π] to [π']. *)
Definition usys_mem_ok (n : Z) (tf : list (mword 64)) (r : mword 64)
    (M : gmap Z (bv 8)) (π : gmap (mword 27) uperm) (szv : Z)
    (M' : gmap Z (bv 8)) (π' : gmap (mword 27) uperm) (szv' : Z) : Prop :=
  if decide (n = USYS_exec) then
    r = (mword_of_int (-1) : mword 64) /\ M' = M /\ π' = π /\ szv' = szv
  else if decide (n = USYS_sbrk) then
    (* THE TWO SIZES ARE NAMED.  They used to be existential, because the
       trapframe word list does not carry [p->sz]; now the KEY does, so the
       row says what happens at the process's actual break rather than at
       some pair of sizes.  A caller of sbrk therefore learns [szv'], which
       is what makes the return value meaningful. *)
    usys_sbrk_img M M' (mword_of_int szv) (mword_of_int szv') /\
    usys_sbrk_perm π π' (mword_of_int szv) (mword_of_int szv')
  else if decide (n = USYS_wait) then
    (* copyout of the zombie's four-byte [xstate] at argument 0 -- and a
       NULL destination is not a destination, so a caller passing a null
       status pointer keeps every byte it held. *)
    (exists (d : nat) (bs : nat -> bv 8),
       (d <= 4)%nat /\
       (uint (tf !!! tf_arg_idx 0) = 0 -> d = 0%nat) /\
       M' = umem_wr M (tf !!! tf_arg_idx 0) d bs)
    /\ π' = π /\ szv' = szv
  else if decide (n = USYS_pipe) then
    (* two four-byte fds, back to back at argument 0 *)
    (exists (d : nat) (bs : nat -> bv 8),
       (d <= 8)%nat /\ M' = umem_wr M (tf !!! tf_arg_idx 0) d bs)
    /\ π' = π /\ szv' = szv
  else if decide (n = USYS_read) then
    (* at most the caller's own count, at argument 1 *)
    (exists (d : nat) (bs : nat -> bv 8),
       (Z.of_nat d <= Z.max 0 (usys_rdcount tf))%Z /\
       M' = umem_wr M (tf !!! tf_arg_idx 1) d bs)
    /\ π' = π /\ szv' = szv
  else if decide (n = USYS_fstat) then
    (* one [struct stat]: dev@0 ino@4 type@8 nlink@10 size@16, so 24 *)
    (exists (d : nat) (bs : nat -> bv 8),
       (d <= 24)%nat /\ M' = umem_wr M (tf !!! tf_arg_idx 1) d bs)
    /\ π' = π /\ szv' = szv
  else M' = M /\ π' = π /\ szv' = szv.

(* ===================================================================== *)
(* SS2b THE DESCRIPTOR TABLE'S OWN ROWS.                                   *)
(*                                                                        *)
(* [usys_mem_ok] above says what a syscall does to the process's IMAGE;    *)
(* this says what it does to the process's DESCRIPTORS, in the same shape  *)
(* and keyed on the same number.  The two are separate predicates rather   *)
(* than one because they are separate obligations -- a syscall proof       *)
(* discharges each against different resources (the page table on one      *)
(* side, [FdSlots.fd_frags] on the other) -- but they are stated together  *)
(* so that "what this entry moves" is one thing to read.                   *)
(*                                                                        *)
(* THE SHAPE OF EVERY ROW IS THE SAME: on failure the table is untouched,  *)
(* and on success ONE OR TWO SLOTS MOVE and the rest do not.  That second  *)
(* half is the whole content -- [list_insert] is what says a descriptor a  *)
(* program was holding is still what it was, which is what lets a proof    *)
(* carry a fd across an unrelated syscall.                                 *)
(*                                                                        *)
(* LENGTH IS PRESERVED BY CONSTRUCTION ([list_insert] on a list keeps its  *)
(* length, and an out-of-range index is a no-op), which matters because    *)
(* [FdSlots.fd_frags] carries [length sts = NOFILE] inside it.  See        *)
(* [usys_fd_ok_length] below.                                             *)
(* ===================================================================== *)

Definition usys_fd_ok (n : Z) (tf : list (mword 64)) (r : mword 64)
    (sts sts' : list fdstate) : Prop :=
  if decide (n = USYS_close) then
    (* close(fd): argument 0 IS the descriptor number, and the slot becomes
       CLOSED.  sys_close returns 0 on success and -1 when [argfd] rejects
       the number -- out of range, or already closed -- and a rejected close
       moves nothing, which is what a program that closes twice needs. *)
    (if decide (uint r = 0)
     then sts' = <[Z.to_nat (uint (tf !!! tf_arg_idx 0)) := FdClosed]> sts
     else sts' = sts)
  else if decide (n = USYS_dup) then
    (* dup(fd): the RETURNED descriptor is a COPY of the argument's -- same
       type, same mode -- because filedup only bumps [f->ref] and the two
       descriptors then name the same [struct file].  The old slot keeps
       what it had, which [list_insert] says by leaving it alone. *)
    (if decide (0 <= bv_signed r)%Z
     then sts' = <[Z.to_nat (uint r)
                     := sts !!! Z.to_nat (uint (tf !!! tf_arg_idx 0))]> sts
     else sts' = sts)
  else if decide (n = USYS_open) then
    (* open(path, omode): the returned descriptor becomes OPEN at some type
       and mode.  Both are existential HERE and both are pinnable: the mode
       is a function of [omode] (argument 1 -- xv6 sets [f->readable] to
       [!(omode & O_WRONLY)] and [f->writable] to [(omode & O_WRONLY) ||
       (omode & O_RDWR)]) and the type is [FdDevice] exactly when the inode
       it resolved is [T_DEVICE], [FdInode] otherwise.  Pinning either needs
       vocabulary this table does not have yet -- the mode wants omode's
       bits decoded, the type wants the path lookup -- so the row says what
       it can honestly say: the slot is now OPEN, and no other slot moved. *)
    (if decide (0 <= bv_signed r)%Z
     then (exists (rd wr : bool) (t : fdtype),
             sts' = <[Z.to_nat (uint r) := FdOpen rd wr t]> sts)
     else sts' = sts)
  else if decide (n = USYS_pipe) then
    (* pipe(fdarray): TWO descriptors, and the row says which end is which
       -- [FdOpen true false FdPipe] reads and [FdOpen false true FdPipe]
       writes, per [FdSlots]'s note that on a pipe the mode flags ARE the
       identity of the end.  sys_pipe returns 0 on success.

       THE TWO NUMBERS ARE EXISTENTIAL, and that is the row's one real gap:
       pipe reports them by WRITING them, as the two four-byte words the
       image row above puts at [tf_arg_idx 0], so tying [a] and [b] to the
       descriptors a caller can actually use means relating them to that
       row's [bs].  The two tables would have to be read together, which is
       the refinement this entry is waiting on. *)
    (if decide (uint r = 0)
     then (exists a b : nat,
             a <> b /\
             sts' = <[a := FdOpen true false FdPipe]>
                      (<[b := FdOpen false true FdPipe]> sts))
     else sts' = sts)
  else
    (* EVERY OTHER ENTRY LEAVES THE TABLE ALONE -- but read that carefully
       for the three entries where it is easy to claim too much.

       EXEC.  This row does NOT say a successful exec keeps the table, and
       cannot: the only exec that reaches this row is the FAILING one
       ([usys_mem_ok]'s exec row pins [r = -1]).  A successful exec never
       returns to this WP -- its successor is a kernel MINT, at an
       arbitrary key, so the contract currently says nothing about the fd
       view across it.  xv6 has no FD_CLOEXEC and really does keep the
       table (that is how the shell hands a redirected descriptor to the
       program it runs), so this is a GAP in the specification rather than
       a property of the code: pinning it means giving exec's mint a row,
       not changing this line.

       FORK.  This row is about the PARENT, whose table fork does not
       touch.  It says nothing about the CHILD's -- and the reason is worth
       knowing, because it is not that the work is missing.  kfork's copy
       loop DOES retype the child's descriptors in the ghost, one per
       iteration: [ProofKforkB3]'s [fd_st_move _ i FdClosed stq stf] moves
       slot [i] from closed to [stf], the type of the very file the
       parent's slot names.  What is missing is a NAME for the result --
       the loop's invariant is stated at [FdSlots.fd_frags_any], and
       [fd_frags_any_acc]'s closer goes straight back to [fd_frags_any], so
       the table the loop builds is forgotten as it is built.  "The child
       inherits the parent's descriptors" is therefore proved and
       unstatable, which is a different defect from unproved, and a
       cheaper one to fix.

       EXIT closes every descriptor and needs no row, because it does not
       return. *)
    sts' = sts.

(* the entries that leave the descriptor table alone -- the fd counterpart
   of [usys_mem_ok_quiet], and what a program carrying an open fd across an
   unrelated syscall reads off the row *)
Lemma usys_fd_ok_quiet (n : Z) (tf : list (mword 64)) (r : mword 64)
    (sts sts' : list fdstate) :
  n <> USYS_close -> n <> USYS_dup -> n <> USYS_open -> n <> USYS_pipe ->
  usys_fd_ok n tf r sts sts' -> sts' = sts.
Proof.
  intros Hc Hd Ho Hp H. unfold usys_fd_ok in H.
  destruct (decide (n = USYS_close)); [contradiction |].
  destruct (decide (n = USYS_dup)); [contradiction |].
  destruct (decide (n = USYS_open)); [contradiction |].
  destruct (decide (n = USYS_pipe)); [contradiction |].
  exact H.
Qed.

(* THE QUIET ROW, IN THE DIRECTION A PROVER NEEDS IT.  [usys_fd_ok_quiet]
   above READS a row ("this entry moved nothing"); an arm has to SUPPLY one,
   and supplies it at the only table it has.  Keyed on the entry's own
   number so a dispatch arm discharges it with its [Hnum] and four
   [discriminate]s. *)
Lemma usys_fd_ok_refl_at (n k : Z) (tf : list (mword 64)) (r : mword 64)
    (sts : list fdstate) :
  n = k ->
  k <> USYS_close -> k <> USYS_dup -> k <> USYS_open -> k <> USYS_pipe ->
  usys_fd_ok n tf r sts sts.
Proof.
  intros -> Hc Hd Ho Hp. unfold usys_fd_ok.
  destruct (decide (k = USYS_close)); [contradiction |].
  destruct (decide (k = USYS_dup)); [contradiction |].
  destruct (decide (k = USYS_open)); [contradiction |].
  destruct (decide (k = USYS_pipe)); [contradiction |].
  reflexivity.
Qed.

(* THE LENGTH SURVIVES EVERY ROW, which is what [FdSlots.fd_frags] needs of
   any table it is asked to hold: it carries [length sts = NOFILE] inside
   it, so a row that could change the length would be a row no bundle could
   accept. *)
Lemma usys_fd_ok_length (n : Z) (tf : list (mword 64)) (r : mword 64)
    (sts sts' : list fdstate) :
  usys_fd_ok n tf r sts sts' -> length sts' = length sts.
Proof.
  unfold usys_fd_ok. intros H.
  destruct (decide (n = USYS_close)) as [_ | _].
  { destruct (decide (uint r = 0)); subst; [ apply length_insert | reflexivity ]. }
  destruct (decide (n = USYS_dup)) as [_ | _].
  { destruct (decide (0 <= bv_signed r)%Z); subst;
      [ apply length_insert | reflexivity ]. }
  destruct (decide (n = USYS_open)) as [_ | _].
  { destruct (decide (0 <= bv_signed r)%Z) as [_ | _].
    - destruct H as (rd & wr & t & ->). apply length_insert.
    - subst. reflexivity. }
  destruct (decide (n = USYS_pipe)) as [_ | _].
  { destruct (decide (uint r = 0)) as [_ | _].
    - destruct H as (a & b & _ & ->). rewrite length_insert. apply length_insert.
    - subst. reflexivity. }
  subst. reflexivity.
Qed.

(* the sixteen quiet entries, by name: what a program calling one of them
   learns.  Stated for the row shape rather than per number so a program
   proof picks it up with one [apply] after [vm_compute]-ing the number. *)
Lemma usys_mem_ok_quiet (n : Z) (tf : list (mword 64)) (r : mword 64)
    (M M' : gmap Z (bv 8)) (π π' : gmap (mword 27) uperm) (szv szv' : Z) :
  n <> USYS_exec -> n <> USYS_sbrk ->
  n <> USYS_wait -> n <> USYS_pipe -> n <> USYS_read -> n <> USYS_fstat ->
  usys_mem_ok n tf r M π szv M' π' szv' -> M' = M /\ π' = π /\ szv' = szv.
Proof.
  intros Hne Hns H3 H4 H5 H8 H. unfold usys_mem_ok in H.
  destruct (decide (n = USYS_exec)); [contradiction |].
  destruct (decide (n = USYS_sbrk)); [contradiction |].
  destruct (decide (n = USYS_wait)); [contradiction |].
  destruct (decide (n = USYS_pipe)); [contradiction |].
  destruct (decide (n = USYS_read)); [contradiction |].
  destruct (decide (n = USYS_fstat)); [contradiction |].
  exact H.
Qed.

(* EXEC's row pins everything: the failure arm is the only one that returns
   here at all, and it says so.  (A successful exec never comes back to this
   WP -- the new program's is MINTED by exec from the new trapframe and
   image.) *)
Lemma usys_mem_ok_exec_row (n : Z) (tf : list (mword 64)) (r : mword 64)
    (M M' : gmap Z (bv 8)) (π π' : gmap (mword 27) uperm) (szv szv' : Z) :
  n = USYS_exec ->
  usys_mem_ok n tf r M π szv M' π' szv' ->
  r = (mword_of_int (-1) : mword 64) /\ M' = M /\ π' = π /\ szv' = szv.
Proof.
  intros -> H. unfold usys_mem_ok in H.
  destruct (decide (USYS_exec = USYS_exec)) as [_ | Hc];
    [ exact H | exfalso; exact (Hc eq_refl) ].
Qed.

(* WAIT AT A NULL STATUS POINTER moves nothing -- which is what a program
   passing a null status pointer to wait needs, and what the row now
   says. *)
Lemma usys_mem_ok_wait_null (n : Z) (tf : list (mword 64)) (r : mword 64)
    (M M' : gmap Z (bv 8)) (π π' : gmap (mword 27) uperm) (szv szv' : Z) :
  n = USYS_wait -> uint (tf !!! tf_arg_idx 0) = 0 ->
  usys_mem_ok n tf r M π szv M' π' szv' ->
  M' = M /\ π' = π /\ szv' = szv.
Proof.
  intros -> Hz H. unfold usys_mem_ok in H.
  destruct (decide (USYS_wait = USYS_exec)) as [Hc | _]; [ discriminate Hc | ].
  destruct (decide (USYS_wait = USYS_sbrk)) as [Hc | _]; [ discriminate Hc | ].
  destruct (decide (USYS_wait = USYS_wait)) as [_ | Hc];
    [ | exfalso; exact (Hc eq_refl) ].
  destruct H as ((d & bs & Hd & Hnull & Hm) & Hp & Hs).
  rewrite (Hnull Hz) in Hm. exact (conj Hm (conj Hp Hs)).
Qed.

(* the permission map is untouched by every entry but sbrk *)
Lemma usys_mem_ok_perm (n : Z) (tf : list (mword 64)) (r : mword 64)
    (M M' : gmap Z (bv 8)) (π π' : gmap (mword 27) uperm) (szv szv' : Z) :
  n <> USYS_sbrk ->
  usys_mem_ok n tf r M π szv M' π' szv' -> π' = π.
Proof.
  intros Hns H. unfold usys_mem_ok in H.
  destruct (decide (n = USYS_exec)); [exact (proj1 (proj2 (proj2 H))) |].
  destruct (decide (n = USYS_sbrk)); [contradiction |].
  destruct (decide (n = USYS_wait)); [exact (proj1 (proj2 H)) |].
  destruct (decide (n = USYS_pipe)); [exact (proj1 (proj2 H)) |].
  destruct (decide (n = USYS_read)); [exact (proj1 (proj2 H)) |].
  destruct (decide (n = USYS_fstat)); [exact (proj1 (proj2 H)) |].
  exact (proj1 (proj2 H)).
Qed.

(* ===================================================================== *)
(* SS3 THE RESUME TRAPFRAME after a returning syscall: epc advanced past   *)
(* the ecall, a0 := the return value.  This is what the kernel's trap loop *)
(* does to the process's trapframe between the ecall and the sret          *)
(* ([usertrap]: [p->trapframe->epc += 4]; [syscall]: [p->trapframe->a0 =   *)
(* syscalls[num]()]), so it is the key the returned slot is stated at.     *)
(* ===================================================================== *)
Definition bump_tf (tf : list (mword 64)) (r : mword 64) : list (mword 64) :=
  <[tf_arg_idx 0 := r]> (<[tf_epc_idx := add_vec_int (tf !!! tf_epc_idx) 4]> tf).

Lemma bump_tf_length (tf : list (mword 64)) (r : mword 64) :
  length (bump_tf tf r) = length tf.
Proof. unfold bump_tf. rewrite !length_insert. reflexivity. Qed.

(* the words the resume state reads, through the bump *)
Lemma bump_tf_epc (tf : list (mword 64)) (r : mword 64) :
  (tf_epc_idx < length tf)%nat ->
  bump_tf tf r !!! tf_epc_idx = add_vec_int (tf !!! tf_epc_idx) 4.
Proof.
  intros Hl. unfold bump_tf.
  rewrite list_lookup_total_insert_ne; [ | unfold tf_arg_idx, tf_epc_idx; lia ].
  apply list_lookup_total_insert. exact Hl.
Qed.

Lemma bump_tf_a0 (tf : list (mword 64)) (r : mword 64) :
  (tf_arg_idx 0 < length tf)%nat ->
  bump_tf tf r !!! tf_arg_idx 0 = r.
Proof.
  intros Hl. unfold bump_tf.
  apply list_lookup_total_insert. rewrite length_insert. exact Hl.
Qed.

Lemma bump_tf_other (tf : list (mword 64)) (r : mword 64) (i : nat) :
  i <> tf_arg_idx 0 -> i <> tf_epc_idx ->
  bump_tf tf r !!! i = tf !!! i.
Proof.
  intros Ha He. unfold bump_tf.
  rewrite list_lookup_total_insert_ne; [ | exact (not_eq_sym Ha) ].
  rewrite list_lookup_total_insert_ne; [ reflexivity | exact (not_eq_sym He) ].
Qed.

(* the number is not moved by the bump (a7 is word 21, not 14 or 3) *)
Lemma bump_tf_num (tf : list (mword 64)) (r : mword 64) :
  usys_num (bump_tf tf r) = usys_num tf.
Proof.
  unfold usys_num. rewrite bump_tf_other; [ reflexivity | | ];
    unfold tf_arg_idx, tf_epc_idx; lia.
Qed.

(* ===================================================================== *)
(* SS3b THE TABLE IS BLIND TO THE FOUR KERNEL WORDS.                       *)
(*                                                                         *)
(* [usys_num] reads word 21 ([tf_arg_idx 7] = a7) and [usys_mem_ok] reads,  *)
(* besides that number, only [tf !!! tf_arg_idx i] for the [i] the window   *)
(* table names -- 0 and 1, i.e. words 14 and 15.  All three are inside      *)
(* [5,35], so [tf_ueq] transports every row.  This is what lets the round   *)
(* relation (UexecRound.v) be stated at whichever of the two trapframes --  *)
(* the one the process trapped with, or the one prepare_return re-armed --  *)
(* the kernel proof happens to hold.                                        *)
(* ===================================================================== *)
Lemma tf_ueq_num (tf tf' : list (mword 64)) :
  tf_ueq tf tf' -> usys_num tf = usys_num tf'.
Proof.
  intros [_ Hg].
  assert (H21 : tf !!! tf_arg_idx 7 = tf' !!! tf_arg_idx 7).
  { apply Hg. unfold tf_arg_idx. lia. }
  unfold usys_num. rewrite H21. reflexivity.
Qed.

(* ...and to the EPC WORD, which is what makes the number the dispatch reads
   the number the ROUND is keyed by: usertrap's prologue writes index 3 and
   nothing else before the [c.li a5,8] fires. *)
Lemma usys_num_epc (tf : list (mword 64)) (v : mword 64) :
  usys_num (<[tf_epc_idx := v]> tf) = usys_num tf.
Proof.
  unfold usys_num.
  rewrite list_lookup_total_insert_ne;
    [ reflexivity | unfold tf_arg_idx, tf_epc_idx; lia ].
Qed.

(* THE THREE WORDS THE TABLE READS, besides the number: the two
   destination pointers (arguments 0 and 1) and read's count (argument 2).
   Everything below is "the table is blind to every other word". *)
Lemma usys_mem_ok_ueq (n : Z) (tf tf' : list (mword 64)) (r : mword 64)
    (M M' : gmap Z (bv 8)) (π π' : gmap (mword 27) uperm) (szv szv' : Z) :
  tf_ueq tf tf' ->
  usys_mem_ok n tf r M π szv M' π' szv' -> usys_mem_ok n tf' r M π szv M' π' szv'.
Proof.
  intros Hu H.
  assert (H0 : tf !!! tf_arg_idx 0 = tf' !!! tf_arg_idx 0)
    by (destruct Hu as [_ Hg]; apply Hg; unfold tf_arg_idx; lia).
  assert (H1 : tf !!! tf_arg_idx 1 = tf' !!! tf_arg_idx 1)
    by (destruct Hu as [_ Hg]; apply Hg; unfold tf_arg_idx; lia).
  assert (H2 : tf !!! tf_arg_idx 2 = tf' !!! tf_arg_idx 2)
    by (destruct Hu as [_ Hg]; apply Hg; unfold tf_arg_idx; lia).
  unfold usys_mem_ok, usys_rdcount in H |- *.
  destruct (decide (n = USYS_exec)); [ exact H | ].
  destruct (decide (n = USYS_sbrk)); [ exact H | ].
  destruct (decide (n = USYS_wait)); [ rewrite <- H0; exact H | ].
  destruct (decide (n = USYS_pipe)); [ rewrite <- H0; exact H | ].
  destruct (decide (n = USYS_read)); [ rewrite <- H1; rewrite <- H2; exact H | ].
  destruct (decide (n = USYS_fstat)); [ rewrite <- H1; exact H | ].
  exact H.
Qed.

(* ...and the table is blind to the EPC WORD too, for the reason
   [usys_num_epc] is: the words it reads are 14, 15, 16 and 21, and the epc
   is 3.  This is what lets the trap loop state the round at the trapframe
   the process TRAPPED with, while the dispatcher's own row is stated at the
   one usertrap's [p->trapframe->epc += 4] block handed on.  ([tf_ueq]
   cannot do this job: the epc is exactly the word the two lists differ
   in.) *)
Lemma usys_mem_ok_epc (n : Z) (tf : list (mword 64)) (v r : mword 64)
    (szv szv' : Z)
    (M M' : gmap Z (bv 8)) (pi pi' : gmap (mword 27) uperm) :
  usys_mem_ok n (<[tf_epc_idx := v]> tf) r M pi szv M' pi' szv' ->
  usys_mem_ok n tf r M pi szv M' pi' szv'.
Proof.
  assert (E0 : (<[tf_epc_idx := v]> tf) !!! tf_arg_idx 0 = tf !!! tf_arg_idx 0)
    by (apply list_lookup_total_insert_ne; unfold tf_arg_idx, tf_epc_idx; lia).
  assert (E1 : (<[tf_epc_idx := v]> tf) !!! tf_arg_idx 1 = tf !!! tf_arg_idx 1)
    by (apply list_lookup_total_insert_ne; unfold tf_arg_idx, tf_epc_idx; lia).
  assert (E2 : (<[tf_epc_idx := v]> tf) !!! tf_arg_idx 2 = tf !!! tf_arg_idx 2)
    by (apply list_lookup_total_insert_ne; unfold tf_arg_idx, tf_epc_idx; lia).
  unfold usys_mem_ok, usys_rdcount. rewrite E0; rewrite E1; rewrite E2.
  intros H; exact H.
Qed.

(* ===================================================================== *)
(* SS4 The scause value of an ecall from U-mode: interrupt bit 0,          *)
(* exception code 8 ([E_U_EnvCall]).  The user-execution contract's case   *)
(* analysis is on this value; the U-mode engine's trap tower delivers it   *)
(* as [UserTrap.utrap_scause (Exception (E_U_EnvCall tt)) sc0], and the    *)
(* bridge between the two spellings is the engine's to prove where it      *)
(* raises the trap (UserTrap.v is not in this file's cone).                *)
(* ===================================================================== *)
Definition uecall_scause : mword 64 := mword_of_int 8.
