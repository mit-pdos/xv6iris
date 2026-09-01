(* ===================================================================== *)
(* UkRunSys.v -- the SYSCALL boundary, on [urun].                          *)
(*                                                                        *)
(* ECALL is the one instruction that is not a wrapper.  Every other leaf   *)
(* keeps the image inside [urun] untouched; a trap hands [user_ptm_inv]    *)
(* back to the kernel, which returns an image the program has to re-own.   *)
(* What it is allowed to have done is [usys_mem_ok]'s table, and the       *)
(* program pays for exactly the row its syscall is in.                     *)
(*                                                                        *)
(* THE QUIET ROW is the one settled here: sixteen syscalls that touch no   *)
(* user memory at all, so [M' = M] and the two heap authorities survive    *)
(* the trap unchanged -- the program keeps every points-to it held across  *)
(* the call, and only a0 moves.  That is what makes [write] framable.      *)
(*                                                                        *)
(* THE WINDOW ROW is the second, and it is settled here too: the four      *)
(* entries that write a caller-named buffer (read, wait, pipe, fstat)      *)
(* differ only in which argument names the buffer and how long it may be,  *)
(* so they are ONE leaf whose caller hands over the range the kernel is    *)
(* licensed to touch and gets it back with a prefix replaced.              *)
(*                                                                        *)
(* The SBRK row (the image grows or shrinks by pages while the break moves *)
(* by bytes) is the one that remains.  Not yet built.                      *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_map ghost_var invariants.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import RegFile.
Require Import UsysMemOk UexecSlot UexecRet.
Require Import FdSlots.      (* [fdstate] -- the key's descriptor view *)
Require Import ProcGeom.   (* [tf_arg_idx] -- wait's row is based at a0 *)
Require Import UserPtTree. (* [umem_wr_write] / [umem_write_prefix] *)
Require Import UkStep.
Require Import UmodeArith.  (* [moi_add_l] / [uint_moi]: read's row addresses
                               through [add_vec_int], the heap through [Z] *)
Require Import UserHeap.
Require Import UserPerm.    (* [uperm] -- the row's permission-map argument *)
Require Import UserPtTree.  (* [umem_wr] / [umem_write] -- the window's image *)
Require Import UserBits.    (* [uint_add_vec_int_small] -- the window's no-wrap *)
Require Import RiscvExtras. (* [uint_unsigned] *)
Require Import RiscvModelBytes. (* [nth_byte] -- pipe's two reported words *)
Require Import TsoCtx.
Local Open Scope Z_scope.
Import Defs.
From Stdlib Require Import ZArith Bool Lia List FunctionalExtensionality.
From iris.base_logic.lib Require Import invariants gen_heap.
Require Import RiscvLang RiscvPtsto.
Require Import RegFile.
Require Import HartSwp HartLift HartSpan HartGoodb HartMemRun HartMCycle
        HartStepFull HartRunFull HartRunGen.
Require Import UserFrame.
Require Import UserExecFacts.
Require Import UsysMemOk.
Require Import UexecSlot UexecRet.
Require Import TsoCtx.   (* [CurCtx]: ambient, per the WpUmode* precedent *)
Local Open Scope Z_scope.
Require Import UkRun.

(* THE SYSCALL NUMBER, off the register file rather than off the trapframe:
   a program knows what it put in a7, and should not have to know that the
   key spells it [usys_num (tf_of m pc)]. *)
Definition usysno (m : regfile) : Z :=
  bv_signed (subrange_vec_dec (m !!! Regidx (mword_of_int 17)) 31 0 : mword 32).

(* ===================================================================== *)
(* THE WINDOW ROWS, AS ONE ROW.                                            *)
(*                                                                         *)
(* Four of the twenty-two entries write a caller-supplied buffer, and they  *)
(* differ in exactly two numbers: WHICH argument names the buffer, and HOW  *)
(* MANY bytes the kernel is licensed to put there.  That pair is            *)
(* [usys_win], so ONE consumer leaf covers all four rows instead of four    *)
(* leaves covering one row each.  [None] is every other number -- the       *)
(* sixteen quiet entries, exec (nothing moves) and sbrk (whose row moves    *)
(* PAGES, not a window, and so is a different leaf's job).                  *)
(*                                                                         *)
(* HOME: these three belong beside [usys_mem_ok_wait_null] in UsysMemOk.v,  *)
(* which is where the rest of the row family lives.  They are here so that  *)
(* this leaf lands as ONE file's change; moving them is a pure cut/paste    *)
(* (they mention nothing this file defines).                                *)
(* ===================================================================== *)
Definition usys_win (n : Z) (tf : list (mword 64)) : option (mword 64 * nat) :=
  if decide (n = USYS_wait) then Some (tf !!! tf_arg_idx 0, 4%nat)
  else if decide (n = USYS_pipe) then Some (tf !!! tf_arg_idx 0, 8%nat)
  else if decide (n = USYS_read) then
    Some (tf !!! tf_arg_idx 1, Z.to_nat (usys_rdcount tf))
  else if decide (n = USYS_fstat) then Some (tf !!! tf_arg_idx 1, 24%nat)
  else None.

(* a window row is none of the four numbers a leaf has to dispatch away from
   before it can read the table: not exit and not fork (which [uexec_ret]'s
   own case analysis takes first), and not exec or sbrk *)
Lemma usys_win_num (n : Z) (tf : list (mword 64)) (dst : mword 64) (cap : nat) :
  usys_win n tf = Some (dst, cap) ->
  n <> USYS_exit /\ n <> USYS_fork /\ n <> USYS_exec /\ n <> USYS_sbrk.
Proof.
  unfold usys_win.
  destruct (decide (n = USYS_wait)) as [-> | _];
    [ intros _; unfold USYS_wait, USYS_exit, USYS_fork, USYS_exec, USYS_sbrk;
      split_and!; discriminate | ].
  destruct (decide (n = USYS_pipe)) as [-> | _];
    [ intros _; unfold USYS_pipe, USYS_exit, USYS_fork, USYS_exec, USYS_sbrk;
      split_and!; discriminate | ].
  destruct (decide (n = USYS_read)) as [-> | _];
    [ intros _; unfold USYS_read, USYS_exit, USYS_fork, USYS_exec, USYS_sbrk;
      split_and!; discriminate | ].
  destruct (decide (n = USYS_fstat)) as [-> | _];
    [ intros _; unfold USYS_fstat, USYS_exit, USYS_fork, USYS_exec, USYS_sbrk;
      split_and!; discriminate | ].
  intros Hc; discriminate Hc.
Qed.

(* THE WINDOW ROW, READ OFF THE TABLE.  What a program calling one of the
   four learns: the kernel wrote SOME run, no longer than the cap its own
   arguments named, at the address its own arguments named -- and nothing
   else moved.  Note what is NOT here: the row says nothing tying the
   written length to the RETURN VALUE, so a read's caller learns
   [d <= count] and not [d = r].  That link lives on the kernel side
   ([SpecSysReadAU]) and would have to be carried into this table before a
   leaf could state it. *)
Lemma usys_mem_ok_window (n : Z) (tf : list (mword 64)) (r : mword 64)
    (M M' : gmap Z (bv 8)) (π π' : gmap (mword 27) uperm) (szv szv' : Z)
    (dst : mword 64) (cap : nat) :
  usys_win n tf = Some (dst, cap) ->
  usys_mem_ok n tf r M π szv M' π' szv' ->
  (exists (d : nat) (bs : nat -> bv 8),
     (d <= cap)%nat /\ M' = umem_wr M dst d bs) /\ π' = π /\ szv' = szv.
Proof.
  unfold usys_win, usys_mem_ok.
  destruct (decide (n = USYS_wait)) as [-> | Hw].
  { intros [= <- <-].
    destruct (decide (USYS_wait = USYS_exec)) as [Hc | _]; [ discriminate Hc | ].
    destruct (decide (USYS_wait = USYS_sbrk)) as [Hc | _]; [ discriminate Hc | ].
    destruct (decide (USYS_wait = USYS_wait)) as [_ | Hc];
      [ | exfalso; exact (Hc eq_refl) ].
    intros ((d & bs & Hd & _ & Hm) & Hp & Hs).
    split; [ exists d, bs; split; [ lia | exact Hm ] | exact (conj Hp Hs) ]. }
  destruct (decide (n = USYS_pipe)) as [-> | Hp0].
  { intros [= <- <-].
    destruct (decide (USYS_pipe = USYS_exec)) as [Hc | _]; [ discriminate Hc | ].
    destruct (decide (USYS_pipe = USYS_sbrk)) as [Hc | _]; [ discriminate Hc | ].
    destruct (decide (USYS_pipe = USYS_wait)) as [Hc | _]; [ discriminate Hc | ].
    destruct (decide (USYS_pipe = USYS_pipe)) as [_ | Hc];
      [ | exfalso; exact (Hc eq_refl) ].
    intros ((d & bs & Hd & Hm) & Hp & Hs).
    split; [ exists d, bs; split; [ lia | exact Hm ] | exact (conj Hp Hs) ]. }
  destruct (decide (n = USYS_read)) as [-> | Hr0].
  { intros [= <- <-].
    destruct (decide (USYS_read = USYS_exec)) as [Hc | _]; [ discriminate Hc | ].
    destruct (decide (USYS_read = USYS_sbrk)) as [Hc | _]; [ discriminate Hc | ].
    destruct (decide (USYS_read = USYS_wait)) as [Hc | _]; [ discriminate Hc | ].
    destruct (decide (USYS_read = USYS_pipe)) as [Hc | _]; [ discriminate Hc | ].
    destruct (decide (USYS_read = USYS_read)) as [_ | Hc];
      [ | exfalso; exact (Hc eq_refl) ].
    intros ((d & bs & Hd & Hm) & Hp & Hs).
    (* the row's bound is on [Z.max 0 count]; the cap is its [Z.to_nat] *)
    split; [ exists d, bs; split; [ lia | exact Hm ] | exact (conj Hp Hs) ]. }
  destruct (decide (n = USYS_fstat)) as [-> | Hf0].
  { intros [= <- <-].
    destruct (decide (USYS_fstat = USYS_exec)) as [Hc | _]; [ discriminate Hc | ].
    destruct (decide (USYS_fstat = USYS_sbrk)) as [Hc | _]; [ discriminate Hc | ].
    destruct (decide (USYS_fstat = USYS_wait)) as [Hc | _]; [ discriminate Hc | ].
    destruct (decide (USYS_fstat = USYS_pipe)) as [Hc | _]; [ discriminate Hc | ].
    destruct (decide (USYS_fstat = USYS_read)) as [Hc | _]; [ discriminate Hc | ].
    destruct (decide (USYS_fstat = USYS_fstat)) as [_ | Hc];
      [ | exfalso; exact (Hc eq_refl) ].
    intros ((d & bs & Hd & Hm) & Hp & Hs).
    split; [ exists d, bs; split; [ lia | exact Hm ] | exact (conj Hp Hs) ]. }
  intros Hc; discriminate Hc.
Qed.

(* ...and THE WINDOW the row names, off the register file for the same
   reason: [UsysMemOk.usys_win]'s twin at the spelling a program has,
   exactly as [usysno] is [usys_num]'s.  wait and pipe write at a0, read
   and fstat at a1, and only read's length is not a constant -- it is a2 as
   the C reads it (an [int], hence the sign, hence the [Z.to_nat]: a
   negative count licenses nothing). *)
Definition usyswin (m : regfile) (n : Z) : option (mword 64 * nat) :=
  if decide (n = USYS_wait) then Some (m !!! Regidx (mword_of_int 10), 4%nat)
  else if decide (n = USYS_pipe) then Some (m !!! Regidx (mword_of_int 10), 8%nat)
  else if decide (n = USYS_read) then
    Some (m !!! Regidx (mword_of_int 11),
          Z.to_nat (bv_signed (subrange_vec_dec
                      (m !!! Regidx (mword_of_int 12)) 31 0 : mword 32)))
  else if decide (n = USYS_fstat) then
    Some (m !!! Regidx (mword_of_int 11), 24%nat)
  else None.

(* the two spellings are the same words, the way [tf_of_num] and
   [tf_of_arg0] are: the trapframe words the table reads ARE the argument
   registers, at indices 14, 15 and 16 *)
Lemma usyswin_tf_of (m : regfile) (pc : mword 64) (n : Z) :
  usys_win n (tf_of m pc) = usyswin m n.
Proof. reflexivity. Qed.

(* THE WINDOW ROW'S IMAGE, ON THE HEAP'S SPELLING.  [usys_mem_ok] states a
   window as [umem_wr], keyed by [uint (add_vec_int dst j)], so that the
   kernel's contract never has to promise the destination does not wrap;
   [UserHeap.uheap_store_run] re-assembles a run keyed at [a + j] in [Z].
   The two are the same map exactly when the run does not wrap -- and a
   caller that OWNS the window has that for free, since [uheap] bounds
   every mapped address by MAXVA.  ([UkRun.uM_store_umem_write] is the same
   kind of bridge for the store leaves.) *)
Lemma umem_wr_write (M : gmap Z (bv 8)) (dst : mword 64) (n : nat)
    (src : nat -> bv 8) :
  (forall i : nat, (i < n)%nat ->
     uint (add_vec_int dst (Z.of_nat i)) = (uint dst + Z.of_nat i)%Z) ->
  umem_wr M dst n src = umem_write M (uint dst) n src.
Proof.
  intros Hlin. symmetry.
  exact (umem_wr_step M dst 0 n src (uint dst) Hlin).
Qed.

Require Import UserFd.   (* [ufd_auth] -- the PROGRAM's own view of
                            its descriptor table, the authority for
                            which rides inside [urun] *)
Section UkRunSys.
  Context `{!riscvGS Σ}.
  Context `{!ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.

  (* ===================================================================== *)
  (* THREE RUN FACTS THE WINDOW LEAF NEEDS.                                 *)
  (*                                                                        *)
  (* HOME: all three belong in UserHeap.v -- the first beside               *)
  (* [uheap_ubyte], the other two beside [ubytes_app] -- and they mention   *)
  (* nothing this file defines, so moving them is a pure cut/paste.  They   *)
  (* are here so that this leaf lands as ONE file's change: UserHeap.v is   *)
  (* under seventeen files' worth of [.vo], and an additive lemma there     *)
  (* costs a rebuild of all of them.                                        *)
  (* ===================================================================== *)

  (* [uheap_ubyte] one index at a time.  This is where the window's         *)
  (* NO-WRAP fact comes from: a run the process owns is keyed at [a + j] in *)
  (* [Z], the kernel's row at [uint (add_vec_int dst j)], and the two agree *)
  (* exactly because every mapped user address is below MAXVA.              *)
  Lemma uheap_ubytes_run (γt γd γs : gname) (M : gmap Z (bv 8))
      (pmv : gmap (mword 27) uperm) (dq : dfrac) (a : Z) (nb : nat)
      (f : nat -> bv 8) :
    uheap γt γd γs M pmv -∗ ubytesq γd dq a nb f -∗
    ⌜ forall j : nat, (j < nb)%nat ->
        M !! (a + Z.of_nat j)%Z = Some (f j) /\ 0 <= a + Z.of_nat j < 2 ^ 38 ⌝.
  Proof.
    iInduction nb as [| kb IH] "IH"; iIntros "Hheap Hbs".
    { iPureIntro. intros j Hj. exfalso. lia. }
    iEval (rewrite /ubytesq seq_S big_sepL_app /=) in "Hbs".
    iDestruct "Hbs" as "[Hlo [Hhi _]]".
    (* the conclusion is PURE, so neither [Hheap] nor a fragment is spent *)
    iDestruct ("IH" with "Hheap Hlo") as %Hk.
    iDestruct (uheap_ubyte with "Hheap Hhi") as %(HM & _ & Hc).
    iPureIntro. intros j Hj.
    destruct (decide (j = kb)) as [-> | Hne]; [ exact (conj HM Hc) | ].
    apply Hk. lia.
  Qed.

  (* [ubytes_app] at a PREFIX LENGTH rather than at a sum.  A caller holding
     a buffer of length [nb] and told the kernel wrote [kb <= nb] of it wants
     the split stated that way round. *)
  Lemma ubytes_split (γd : gname) (a : Z) (kb nb : nat) (f : nat -> bv 8) :
    (kb <= nb)%nat ->
    ubytes γd a nb f ⊣⊢
    ubytes γd a kb f ∗
    ubytes γd (a + Z.of_nat kb) (nb - kb) (fun j => f (kb + j)%nat).
  Proof.
    intros Hk. replace nb with (kb + (nb - kb))%nat at 1 by lia.
    apply ubytes_app.
  Qed.

  (* TWO NAMES FOR THE SAME RUN.  A run's byte function is only ever read
     INSIDE the run, so two that agree there own the same bytes.  The window
     leaf needs exactly this: above the written prefix the bytes are the
     caller's originals, under a new name. *)
  Lemma ubytes_ext (γd : gname) (a : Z) (nb : nat) (f g : nat -> bv 8) :
    (forall j : nat, (j < nb)%nat -> f j = g j) ->
    ubytes γd a nb f -∗ ubytes γd a nb g.
  Proof.
    intros He. rewrite /ubytes /ubytesq. iApply big_sepL_mono.
    intros i y Hy. apply lookup_seq in Hy as [-> Hi].
    rewrite (He (0 + i)%nat ltac:(lia)). done.
  Qed.

  (* ------------------------------------------------------------------- *)
  (* MOVING THE AUTHORITY WITHOUT LEARNING ANYTHING.                       *)
  (*                                                                       *)
  (* Every row but close's can be followed by a program that holds no      *)
  (* handle: open and pipe allocate, dup copies, and the other eighteen    *)
  (* move nothing.  What none of them can do is move the authority without *)
  (* THE LEDGER: an allocation that lands on a standard stream updates     *)
  (* that slot's fragment, and the fragment lives in the ledger.  So the   *)
  (* ledger goes in and comes back -- at a state the caller is told        *)
  (* nothing about, which is the whole difference between this and         *)
  (* [UserFd.ufd_alloc_least].                                             *)
  (*                                                                       *)
  (* CLOSE IS THE EXCEPTION AND MUST BE: it makes a slot free, which above *)
  (* the standard streams is a DELETE on the program's map, and an         *)
  (* authority cannot shrink without the element.  That is the whole       *)
  (* content of "a program that closed a descriptor must stop claiming it  *)
  (* is open", and it is why close has no untracked leaf.                  *)
  (* ------------------------------------------------------------------- *)
  Lemma ufd_auth_move (γfd : gname) (n : Z) (tf : list (mword 64))
      (r : mword 64) (fdv fdv' l : list fdstate) :
    n <> USYS_close ->
    usys_fd_ok n tf r fdv fdv' ->
    ufd_auth γfd fdv -∗ ustd γfd l ==∗
    ufd_auth γfd fdv' ∗ ∃ l' : list fdstate, ustd γfd l'.
  Proof.
    intros Hnc Hrow. iIntros "Hufd Hstd". unfold usys_fd_ok in Hrow.
    destruct (decide (n = USYS_close)) as [Hc | _]; [ contradiction (Hnc Hc) | ].
    destruct (decide (n = USYS_dup)) as [_ | _].
    { destruct Hrow as [(fd1 & _ & Hcl & ->) | [_ ->]];
        [| iModIntro; iFrame "Hufd"; by iExists l ].
      (* the copied state may itself be CLOSED -- dup's row does not say the
         argument was open -- and then the table did not move at all *)
      destruct (decide (fdv !!! Z.to_nat (usys_argfd tf) = FdClosed))
        as [He | Hne].
      - rewrite He.
        iDestruct (ufd_alloc_least_closed γfd fdv fd1 Hcl with "Hufd") as "$".
        iModIntro. by iExists l.
      - iMod (ufd_alloc_least_any γfd fdv l fd1 _ Hcl Hne with "Hufd Hstd")
          as "[$ $]". by iModIntro. }
    destruct (decide (n = USYS_open)) as [_ | _].
    { destruct Hrow as [(fd & rd & wr & t & _ & Hcl & ->) | [_ ->]];
        [| iModIntro; iFrame "Hufd"; by iExists l ].
      iMod (ufd_alloc_least_any γfd fdv l fd (FdOpen rd wr t) Hcl
              ltac:(discriminate) with "Hufd Hstd") as "[$ $]".
      by iModIntro. }
    destruct (decide (n = USYS_pipe)) as [_ | _].
    { destruct (decide (uint r = 0)) as [_ | _];
        [| subst fdv'; iModIntro; iFrame "Hufd"; by iExists l ].
      destruct Hrow as (a & b & Hne & Hca & Hcb & ->).
      (* THE TWO ALLOCATIONS RUN IN THE ROW'S OWN ORDER: read end first,
         write end against the table the first left.  That is the order
         sys_pipe allocates in, and stating it that way is what lets the
         second scan's least-closed fact be read at the table it is actually
         about -- no commuting needed here at all. *)
      iMod (ufd_alloc_least_any γfd fdv l a (FdOpen true false FdPipe) Hca
              ltac:(discriminate) with "Hufd Hstd") as "[Hufd Hstd]".
      iDestruct "Hstd" as (l1) "Hstd".
      iMod (ufd_alloc_least_any γfd (<[a := FdOpen true false FdPipe]> fdv) l1 b
              (FdOpen false true FdPipe) Hcb ltac:(discriminate)
              with "Hufd Hstd") as "[$ $]".
      by iModIntro. }
    subst fdv'. iModIntro. iFrame "Hufd". by iExists l.
  Qed.

  (* ...and the same at [UserFd.ufd_state], which is what a run predicate on
     an untracking channel carries: the ledger goes in and comes back inside
     the same resource, so nothing between here and the client mentions it. *)
  Lemma ufd_state_move (γfd : gname) (n : Z) (tf : list (mword 64))
      (r : mword 64) (fdv fdv' : list fdstate) :
    n <> USYS_close ->
    usys_fd_ok n tf r fdv fdv' ->
    ufd_state γfd fdv ==∗ ufd_state γfd fdv'.
  Proof.
    intros Hnc Hrow. rewrite /ufd_state /ustd_any.
    iIntros "[Ha Hl]". iDestruct "Hl" as (l) "Hl".
    iMod (ufd_auth_move γfd n tf r fdv fdv' l Hnc Hrow with "Ha Hl") as "[$ $]".
    by iModIntro.
  Qed.

  (* ------------------------------------------------------------------- *)
  (* ecall, at a QUIET syscall.  The heap crosses the trap intact: the     *)
  (* kernel is licensed to change nothing about the image, so [urun] comes *)
  (* back at the same [M] and every points-to the program (or its caller)  *)
  (* was holding is still good.  a0 is the kernel's return value, about    *)
  (* which nothing is claimed.                                             *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_uk_ecall_quiet (γt γd γs γfd : gname) (h : CpuId) (m : regfile)
      (pc : mword 64) (n : Z) (avail : nat) :
    usysno m = n ->
    n <> USYS_exit -> n <> USYS_fork ->
    n <> USYS_exec -> n <> USYS_sbrk ->
    n <> USYS_wait -> n <> USYS_pipe -> n <> USYS_read -> n <> USYS_fstat ->
    (* ...AND IT MOVES NO DESCRIPTOR EITHER.  Three of these are new, and
       they are what [urun] carrying the program's own fd authority costs:
       this leaf closes the run back up at the view it opened at, so it may
       only be used where the table did not move.  open / close / dup are
       QUIET IN MEMORY and were reaching this leaf on that ground; they have
       their own leaves now, which do the ghost step instead of asserting
       there was none. *)
    n <> USYS_close -> n <> USYS_dup -> n <> USYS_open ->
    is_aligned_vaddr (Virtaddr (add_vec_int pc 4)) 2 = true ->
    uinstr_is γt pc false (ECALL tt) -∗
    urun γt γd γs γfd h m pc avail -∗
    (∀ (h' : CpuId) (r : mword 64),
       urun γt γd γs γfd h' (<[Regidx (mword_of_int 10) := r]> m) (add_vec_int pc 4) avail -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hn Hexit Hfork Hexec Hsbrk H3 H4 H5 H8 Hcl Hdp Hop Hal4.
    iIntros "#Hi Hrun Hcont".
    iDestruct "Hrun" as (xi C pt Rfd Rut sz M pm fdv) "(%Hlo & %Hpm & Hheap & Hstk & Hufd & Hb)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iDestruct (uvb_x0 with "Hb") as "[%Hx0 Hb]".
    iApply (UkStep.wp_uk_ecall C pt Rfd Rut pm sz Hlo Hpm M m pc fdv Hui
              (fun (s : mstate)
                   (Hp : register_lookup cur_privilege s.(sregs) = User)
                   (Hc : register_lookup (R_bitvector_64 PC) s.(sregs) = pc) =>
                 UserExecFacts.goodmb_execute_ECALL_U UserFrame.Du_r UserFrame.Du_w
                   s pc ltac:(vm_compute; reflexivity)
                   ltac:(vm_compute; reflexivity) Hp Hc)
              with "Hb").
    rewrite (uexec_ret_ecall _ _ eq_refl).
    assert (Hnum : usys_num (uvis_tf (uvis_of_run m pc M pm sz fdv)) = n).
    { cbn [uvis_tf uvis_of_run]. rewrite tf_of_num. exact Hn. }
    rewrite Hnum. cbv zeta.
    destruct (decide (n = USYS_exit)) as [He | _]; [ exfalso; exact (Hexit He) | ].
    destruct (decide (n = USYS_fork)) as [He | _]; [ exfalso; exact (Hfork He) | ].
    (* THE ROW COMES IN BESIDE THE IMAGE'S NOW.  A quiet syscall's fd row is
       [fdv' = fdv] ([UsysMemOk.usys_fd_ok_quiet]), so this leaf could pin
       the descriptor view -- it does not yet, because [urun] hides the view
       and has nowhere to say it.  Named and discarded here; the leaves that
       will read it are open/close/dup, once [urun] carries the program's
       own descriptor authority. *)
    iIntros (r M' pm' sz' fdv') "%Hok %Hfdok %Hpiperow".
    destruct (usys_mem_ok_quiet n _ r _ _ _ _ _ _ Hexec Hsbrk H3 H4 H5 H8 Hok)
      as [-> [-> ->]].
    (* ...AND THE TABLE DID NOT MOVE.  This is the row being READ rather
       than dropped: with the four descriptor-moving numbers excluded the
       row IS [fdv' = fdv], so the authority [urun] was carrying is already
       at the view the process resumes at. *)
    pose proof (usys_fd_ok_quiet n _ r _ _ Hcl Hdp Hop H4 Hfdok) as ->.
    cbn [uvis_M uvis_perm uvis_of_run].
    (* the resumed key is at the SAME view, so the bump is at [fdv] twice *)
    rewrite (uslot_bump_run m pc M M pm pm sz sz fdv fdv r Hx0 Hal4).
    iApply (urun_close_upd _ _ _ _ _ _ m (mword_of_int 10) _ _ _ _ _
              ltac:(unfold unot_sp; vm_compute; discriminate) with "Hheap Hstk Hufd").
    iIntros (h') "Hrun".
    iApply ("Hcont" $! h' r with "Hrun").
  Qed.


  (* ------------------------------------------------------------------- *)
  (* ecall, at OPEN -- THE FIRST LEAF THAT MOVES THE PROGRAM'S OWN GHOST   *)
  (* TABLE.                                                               *)
  (*                                                                      *)
  (* open writes no user byte, so the image crosses the trap exactly as it *)
  (* does at a quiet call.  What it DOES move is [p->ofile[]], and [urun]  *)
  (* now carries the program's authority over that -- so this leaf cannot  *)
  (* be the quiet one, and the difference is the whole point: it MINTS the *)
  (* handle for the descriptor that came back.                            *)
  (*                                                                      *)
  (* THE LEDGER DECIDES WHICH DESCRIPTOR CAME BACK.  fdalloc scans from 0, *)
  (* so a caller that knows the state of its standard streams knows the    *)
  (* answer: [UserFd.ualloc] is that case analysis, and it is a case       *)
  (* analysis on the CALLER's ledger rather than on the kernel's choice.   *)
  (* At an all-open ledger it delivers a handle above the standard streams *)
  (* -- [UserFd.ufd γfd fd (FdOpen …)], a separable resource a program can *)
  (* carry into a subroutine and read back with [UserFd.ufd_agree]; at a   *)
  (* ledger with a closed slot it names THAT slot, which is what makes a   *)
  (* redirection ([close(1); open(path)]) provable at all.                 *)
  (*                                                                      *)
  (* THE FAILURE ARM NAMES [-1], and that is what makes the disjunction    *)
  (* USABLE.  A bare [emp] on the right would be sound and worthless: the  *)
  (* caller would get [r = 3] back and still not be able to rule the arm   *)
  (* out, because nothing would tie it to failure.  Guarded on the return  *)
  (* value, a caller that has checked [r <> -1] eliminates it and KEEPS    *)
  (* the handle.  ([UsysMemOk.usys_fd_ok]'s open row carries the same      *)
  (* guard, for the same reason.)                                          *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_uk_ecall_open (γt γd γs γfd : gname) (h : CpuId) (m : regfile)
      (pc : mword 64) (l : list fdstate) (avail : nat) :
    usysno m = USYS_open ->
    is_aligned_vaddr (Virtaddr (add_vec_int pc 4)) 2 = true ->
    uinstr_is γt pc false (ECALL tt) -∗
    urun γt γd γs γfd h m pc avail -∗
    ustd γfd l -∗
    (∀ (h' : CpuId) (r : mword 64),
       ((∃ (fd : nat) (rd wr : bool) (t : fdtype),
           (* the number AND its bound: a caller that wants to feed this
              descriptor back to close/dup needs to read it as a C [int],
              and [fd < NOFILE] is what makes that reading exact *)
           ⌜r = (mword_of_int (Z.of_nat fd) : mword 64)
            /\ (fd < NOFILE)%nat⌝ ∗
           ualloc γfd l fd (FdOpen rd wr t))
        ∨ (⌜r = (mword_of_int (-1) : mword 64)⌝ ∗ ustd γfd l)) -∗
       urun γt γd γs γfd h' (<[Regidx (mword_of_int 10) := r]> m)
         (add_vec_int pc 4) avail -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hn Hal4.
    iIntros "#Hi Hrun Hstd Hcont".
    iDestruct "Hrun" as (xi C pt Rfd Rut sz M pm fdv) "(%Hlo & %Hpm & Hheap & Hstk & Hufd & Hb)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iDestruct (uvb_x0 with "Hb") as "[%Hx0 Hb]".
    iApply (UkStep.wp_uk_ecall C pt Rfd Rut pm sz Hlo Hpm M m pc fdv Hui
              (fun (s : mstate)
                   (Hp : register_lookup cur_privilege s.(sregs) = User)
                   (Hc : register_lookup (R_bitvector_64 PC) s.(sregs) = pc) =>
                 UserExecFacts.goodmb_execute_ECALL_U UserFrame.Du_r UserFrame.Du_w
                   s pc ltac:(vm_compute; reflexivity)
                   ltac:(vm_compute; reflexivity) Hp Hc)
              with "Hb").
    rewrite (uexec_ret_ecall _ _ eq_refl).
    assert (Hnum : usys_num (uvis_tf (uvis_of_run m pc M pm sz fdv)) = USYS_open).
    { cbn [uvis_tf uvis_of_run]. rewrite tf_of_num. exact Hn. }
    rewrite Hnum. cbv zeta.
    destruct (decide (USYS_open = USYS_exit)) as [He | _];
      [ exfalso; vm_compute in He; discriminate | ].
    destruct (decide (USYS_open = USYS_fork)) as [He | _];
      [ exfalso; vm_compute in He; discriminate | ].
    iIntros (r M' pm' sz' fdv') "%Hok %Hfdok %Hpiperow".
    (* the IMAGE half is the quiet row: open touches no user byte *)
    destruct (usys_mem_ok_quiet USYS_open _ r _ _ _ _ _ _
                ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)
                ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) Hok)
      as [-> [-> ->]].
    (* ...and the DESCRIPTOR half is the open row *)
    unfold usys_fd_ok in Hfdok.
    destruct (decide (USYS_open = USYS_close)) as [Hc | _]; [ discriminate Hc | ].
    destruct (decide (USYS_open = USYS_dup)) as [Hc | _]; [ discriminate Hc | ].
    destruct (decide (USYS_open = USYS_open)) as [_ | Hc];
      [ | exfalso; exact (Hc eq_refl) ].
    cbn [uvis_M uvis_perm uvis_fd uvis_of_run] in Hfdok |- *.
    iDestruct (ufd_auth_len with "Hufd") as %Hfdlen.
    iApply uslot_bupd.
    destruct Hfdok as [(fd & rd & wr & t & Hr & Hcl & ->) | [Hrm ->]].
    - (* A DESCRIPTOR CAME BACK, at the LOWEST free slot -- which is the
         promise [sys_open_post] makes and the row carries, and which the
         caller's ledger turns into a NUMBER. *)
      iMod (ufd_alloc_least γfd fdv l fd (FdOpen rd wr t) Hcl
              ltac:(discriminate) with "Hufd Hstd") as "[Hufd Hh]".
      iModIntro.
      rewrite (uslot_bump_run m pc M M pm pm sz sz fdv
                 (<[fd := FdOpen rd wr t]> fdv) r Hx0 Hal4).
      iApply (urun_close_upd _ _ _ _ _ _ m (mword_of_int 10) _ _ _ _ _
                ltac:(unfold unot_sp; vm_compute; discriminate)
                with "Hheap Hstk Hufd").
      iIntros (h') "Hrun".
      iApply ("Hcont" $! h' r with "[Hh] Hrun").
      iLeft. iExists fd, rd, wr, t. iFrame "Hh". iPureIntro.
      split; [ exact Hr | ].
      (* the slot the kernel chose is a slot of the table *)
      rewrite <- Hfdlen. exact (fd_least_closed_lt _ _ Hcl).
    - (* the call failed: nothing moved, and the ledger comes straight back *)
      iModIntro.
      rewrite (uslot_bump_run m pc M M pm pm sz sz fdv fdv r Hx0 Hal4).
      iApply (urun_close_upd _ _ _ _ _ _ m (mword_of_int 10) _ _ _ _ _
                ltac:(unfold unot_sp; vm_compute; discriminate)
                with "Hheap Hstk Hufd").
      iIntros (h') "Hrun".
      iApply ("Hcont" $! h' r with "[Hstd] Hrun").
      iRight. iFrame "Hstd". iPureIntro. exact Hrm.
  Qed.


  (* ------------------------------------------------------------------- *)
  (* ecall, at DUP.  TWO resources go in: the LEDGER, which decides where  *)
  (* the copy lands, and a CLAIM on the source, which says what state is   *)
  (* copied.  Both are load-bearing -- dup's row says the new descriptor   *)
  (* holds a copy of the ARGUMENT's state, so without knowing that state   *)
  (* there is nothing to hand back -- and the claim is a disjunction       *)
  (* ([UserFd.ufd_own]) because both arms are used on the first day:       *)
  (* init's [dup(0)] duplicates a STANDARD STREAM, described by the ledger *)
  (* it already handed in, and sh's [dup(p[1])] duplicates a pipe end it   *)
  (* holds a handle for.  The claim comes back untouched -- dup does not   *)
  (* disturb its source, and the slot the copy lands in was CLOSED, so it  *)
  (* is not the source's.                                                  *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_uk_ecall_dup (γt γd γs γfd : gname) (h : CpuId) (m : regfile)
      (pc : mword 64) (l : list fdstate) (fd0 : nat) (st : fdstate)
      (avail : nat) :
    usysno m = USYS_dup ->
    (* the argument register IS the descriptor the claim is for, read the
       way [argfd] reads it -- as a C [int] *)
    bv_signed (trunc32 (m !!! Regidx (mword_of_int 10))) = Z.of_nat fd0 ->
    st <> FdClosed ->
    is_aligned_vaddr (Virtaddr (add_vec_int pc 4)) 2 = true ->
    uinstr_is γt pc false (ECALL tt) -∗
    urun γt γd γs γfd h m pc avail -∗
    ustd γfd l -∗
    ufd_own γfd l fd0 st -∗
    (∀ (h' : CpuId) (r : mword 64),
       ((∃ fd1 : nat,
           ⌜r = (mword_of_int (Z.of_nat fd1) : mword 64)
            /\ (fd1 < NOFILE)%nat⌝ ∗
           ualloc γfd l fd1 st ∗ ufd_own γfd (ustd_after l st) fd0 st)
        ∨ (⌜r = (mword_of_int (-1) : mword 64)⌝ ∗
           ustd γfd l ∗ ufd_own γfd l fd0 st)) -∗
       urun γt γd γs γfd h' (<[Regidx (mword_of_int 10) := r]> m)
         (add_vec_int pc 4) avail -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hn Harg Hstne Hal4.
    iIntros "#Hi Hrun Hstd Hh0 Hcont".
    iDestruct "Hrun" as (xi C pt Rfd Rut sz M pm fdv) "(%Hlo & %Hpm & Hheap & Hstk & Hufd & Hb)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iDestruct (uvb_x0 with "Hb") as "[%Hx0 Hb]".
    (* the claim READS the view: this is what says the source descriptor is
       open, and at which state -- which is what dup's row copies. *)
    iDestruct (ufd_own_agree with "Hufd Hstd Hh0") as %[Hsrc _].
    iDestruct (ufd_auth_len with "Hufd") as %Hfdlen.
    (* ...and the slot the copy lands in is never the source's, which is
       what lets the claim come back at the ledger the copy left *)
    iDestruct (ufd_own_ne_lowest γfd l fd0 st Hstne with "Hstd Hh0") as %Hnel.
    iApply (UkStep.wp_uk_ecall C pt Rfd Rut pm sz Hlo Hpm M m pc fdv Hui
              (fun (s : mstate)
                   (Hp : register_lookup cur_privilege s.(sregs) = User)
                   (Hc : register_lookup (R_bitvector_64 PC) s.(sregs) = pc) =>
                 UserExecFacts.goodmb_execute_ECALL_U UserFrame.Du_r UserFrame.Du_w
                   s pc ltac:(vm_compute; reflexivity)
                   ltac:(vm_compute; reflexivity) Hp Hc)
              with "Hb").
    rewrite (uexec_ret_ecall _ _ eq_refl).
    assert (Hnum : usys_num (uvis_tf (uvis_of_run m pc M pm sz fdv)) = USYS_dup).
    { cbn [uvis_tf uvis_of_run]. rewrite tf_of_num. exact Hn. }
    rewrite Hnum. cbv zeta.
    destruct (decide (USYS_dup = USYS_exit)) as [He | _];
      [ exfalso; vm_compute in He; discriminate | ].
    destruct (decide (USYS_dup = USYS_fork)) as [He | _];
      [ exfalso; vm_compute in He; discriminate | ].
    iIntros (r M' pm' sz' fdv') "%Hok %Hfdok %Hpiperow".
    destruct (usys_mem_ok_quiet USYS_dup _ r _ _ _ _ _ _
                ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)
                ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) Hok)
      as [-> [-> ->]].
    unfold usys_fd_ok in Hfdok.
    destruct (decide (USYS_dup = USYS_close)) as [Hc | _]; [ discriminate Hc | ].
    destruct (decide (USYS_dup = USYS_dup)) as [_ | Hc];
      [ | exfalso; exact (Hc eq_refl) ].
    cbn [uvis_M uvis_perm uvis_fd uvis_of_run] in Hfdok |- *.
    (* THE ROW'S ARGUMENT INDEX IS THE CALLER'S [fd0]: the row reads a0 of
       the trapframe as a C [int], and [tf_of] puts the register there. *)
    assert (Hai : Z.to_nat (usys_argfd (tf_of m pc)) = fd0).
    { unfold usys_argfd. cbn [tf_of]. rewrite Harg. exact (Nat2Z.id fd0). }
    iApply uslot_bupd.
    destruct Hfdok as [(fd1 & Hr & Hcl & ->) | [Hrm ->]].
    - (* DUPLICATED.  [Hai] turns the row's copied state into the caller's
         own [st] ([Hsrc], off the claim), and the destination slot was the
         LOWEST free one, which the ledger reads as a number. *)
      rewrite Hai (list_lookup_total_correct fdv fd0 st Hsrc).
      iDestruct (ufd_own_after γfd l fd0 st st Hnel with "Hh0") as "Hh0".
      iMod (ufd_alloc_least γfd fdv l fd1 st Hcl Hstne with "Hufd Hstd")
        as "[Hufd Hh1]".
      iModIntro.
      rewrite (uslot_bump_run m pc M M pm pm sz sz fdv
                 (<[fd1 := st]> fdv) r Hx0 Hal4).
      iApply (urun_close_upd _ _ _ _ _ _ m (mword_of_int 10) _ _ _ _ _
                ltac:(unfold unot_sp; vm_compute; discriminate)
                with "Hheap Hstk Hufd").
      iIntros (h') "Hrun".
      iApply ("Hcont" $! h' r with "[Hh1 Hh0] Hrun").
      iLeft. iExists fd1. iFrame "Hh1 Hh0". iPureIntro.
      split; [ exact Hr | ].
      rewrite <- Hfdlen. exact (fd_least_closed_lt _ _ Hcl).
    - (* the table was full, or the argument was not an open descriptor:
         nothing moved, and both resources come straight back *)
      iModIntro.
      rewrite (uslot_bump_run m pc M M pm pm sz sz fdv fdv r Hx0 Hal4).
      iApply (urun_close_upd _ _ _ _ _ _ m (mword_of_int 10) _ _ _ _ _
                ltac:(unfold unot_sp; vm_compute; discriminate)
                with "Hheap Hstk Hufd").
      iIntros (h') "Hrun".
      iApply ("Hcont" $! h' r with "[Hstd Hh0] Hrun").
      iRight. iFrame "Hstd Hh0". iPureIntro. exact Hrm.
  Qed.


  (* ------------------------------------------------------------------- *)
  (* ecall, at DUP, WITHOUT TRACKING THE SOURCE.  A program that holds no    *)
  (* claim still has to move the authority -- the table moved whether or     *)
  (* not it was watching -- and the LEDGER is what pays for it: the copy     *)
  (* either lands on a standard stream, whose fragment is in the ledger, or  *)
  (* above them, and then the minted handle is dropped.  It learns nothing;  *)
  (* the ledger comes back at a state this leaf does not name.  This is the  *)
  (* leaf for a proof that has not started tracking its descriptors;         *)
  (* [wp_uk_ecall_dup] is the one that pays a claim and gets two.            *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_uk_ecall_dup_untracked (γt γd γs γfd : gname) (h : CpuId)
      (m : regfile) (pc : mword 64) (l : list fdstate) (avail : nat) :
    usysno m = USYS_dup ->
    is_aligned_vaddr (Virtaddr (add_vec_int pc 4)) 2 = true ->
    uinstr_is γt pc false (ECALL tt) -∗
    urun γt γd γs γfd h m pc avail -∗
    ustd γfd l -∗
    (∀ (h' : CpuId) (r : mword 64) (l' : list fdstate),
       ustd γfd l' -∗
       urun γt γd γs γfd h' (<[Regidx (mword_of_int 10) := r]> m)
         (add_vec_int pc 4) avail -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hn Hal4.
    iIntros "#Hi Hrun Hstd Hcont".
    iDestruct "Hrun" as (xi C pt Rfd Rut sz M pm fdv) "(%Hlo & %Hpm & Hheap & Hstk & Hufd & Hb)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iDestruct (uvb_x0 with "Hb") as "[%Hx0 Hb]".
    iApply (UkStep.wp_uk_ecall C pt Rfd Rut pm sz Hlo Hpm M m pc fdv Hui
              (fun (s : mstate)
                   (Hp : register_lookup cur_privilege s.(sregs) = User)
                   (Hc : register_lookup (R_bitvector_64 PC) s.(sregs) = pc) =>
                 UserExecFacts.goodmb_execute_ECALL_U UserFrame.Du_r UserFrame.Du_w
                   s pc ltac:(vm_compute; reflexivity)
                   ltac:(vm_compute; reflexivity) Hp Hc)
              with "Hb").
    rewrite (uexec_ret_ecall _ _ eq_refl).
    assert (Hnum : usys_num (uvis_tf (uvis_of_run m pc M pm sz fdv)) = USYS_dup).
    { cbn [uvis_tf uvis_of_run]. rewrite tf_of_num. exact Hn. }
    rewrite Hnum. cbv zeta.
    destruct (decide (USYS_dup = USYS_exit)) as [He | _];
      [ exfalso; vm_compute in He; discriminate | ].
    destruct (decide (USYS_dup = USYS_fork)) as [He | _];
      [ exfalso; vm_compute in He; discriminate | ].
    iIntros (r M' pm' sz' fdv') "%Hok %Hfdok %Hpiperow".
    destruct (usys_mem_ok_quiet USYS_dup _ r _ _ _ _ _ _
                ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)
                ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) Hok)
      as [-> [-> ->]].
    unfold usys_fd_ok in Hfdok.
    destruct (decide (USYS_dup = USYS_close)) as [Hc | _]; [ discriminate Hc | ].
    destruct (decide (USYS_dup = USYS_dup)) as [_ | Hc];
      [ | exfalso; exact (Hc eq_refl) ].
    cbn [uvis_M uvis_perm uvis_fd uvis_of_run] in Hfdok |- *.
    iApply uslot_bupd.
    destruct Hfdok as [(fd1 & Hr & Hcl & ->) | [Hrm ->]].
    - iAssert (|==> ufd_auth γfd
                 (<[fd1 := fdv !!! Z.to_nat (usys_argfd (tf_of m pc))]> fdv) ∗
                 ∃ l' : list fdstate, ustd γfd l')%I
        with "[Hufd Hstd]" as ">[Hufd Hstd]".
      { destruct (decide (fdv !!! Z.to_nat (usys_argfd (tf_of m pc)) = FdClosed))
          as [He | Hne].
        - rewrite He.
          iDestruct (ufd_alloc_least_closed γfd fdv fd1 Hcl with "Hufd") as "$".
          iModIntro. by iExists l.
        - iMod (ufd_alloc_least_any γfd fdv l fd1 _ Hcl Hne with "Hufd Hstd")
            as "[$ $]". by iModIntro. }
      iDestruct "Hstd" as (l') "Hstd".
      iModIntro.
      rewrite (uslot_bump_run m pc M M pm pm sz sz fdv
                 (<[fd1 := fdv !!! Z.to_nat (usys_argfd (tf_of m pc))]> fdv)
                 r Hx0 Hal4).
      iApply (urun_close_upd _ _ _ _ _ _ m (mword_of_int 10) _ _ _ _ _
                ltac:(unfold unot_sp; vm_compute; discriminate)
                with "Hheap Hstk Hufd").
      iIntros (h') "Hrun". iApply ("Hcont" $! h' r l' with "Hstd Hrun").
    - iModIntro.
      rewrite (uslot_bump_run m pc M M pm pm sz sz fdv fdv r Hx0 Hal4).
      iApply (urun_close_upd _ _ _ _ _ _ m (mword_of_int 10) _ _ _ _ _
                ltac:(unfold unot_sp; vm_compute; discriminate)
                with "Hheap Hstk Hufd").
      iIntros (h') "Hrun". iApply ("Hcont" $! h' r l with "Hstd Hrun").
  Qed.

  (* ------------------------------------------------------------------- *)
  (* CLOSE'S ROW, READ AT A DESCRIPTOR THE CALLER KNOWS IS OPEN.           *)
  (* Both close leaves want the same two facts out of it -- the call        *)
  (* returned 0, and the slot the caller named is the one that became       *)
  (* closed -- and the row's second conjunct is what makes the first        *)
  (* available at all.  Pure, so it is proved once here.                    *)
  (* ------------------------------------------------------------------- *)
  Lemma uk_close_row (m : regfile) (pc : mword 64) (fd : nat) (st : fdstate)
      (fdv fdv' : list fdstate) (r : mword 64) :
    bv_signed (trunc32 (m !!! Regidx (mword_of_int 10))) = Z.of_nat fd ->
    fdv !! fd = Some st -> st <> FdClosed ->
    usys_fd_ok USYS_close (tf_of m pc) r fdv fdv' ->
    uint r = 0 /\ fdv' = <[fd := FdClosed]> fdv.
  Proof.
    intros Harg Hi Hne Hrow.
    assert (Haz : usys_argfd (tf_of m pc) = Z.of_nat fd)
      by (unfold usys_argfd; cbn [tf_of]; exact Harg).
    assert (Hai : Z.to_nat (usys_argfd (tf_of m pc)) = fd)
      by (rewrite Haz; exact (Nat2Z.id fd)).
    unfold usys_fd_ok in Hrow.
    destruct (decide (USYS_close = USYS_close)) as [_ | Hc];
      [| exfalso; exact (Hc eq_refl)].
    destruct Hrow as [Hmove Hdet].
    pose proof (Hdet fd st Haz Hi Hne) as Hr0.
    split; [exact Hr0 |].
    destruct (decide (uint r = 0)) as [_ | Hc]; [| exfalso; exact (Hc Hr0)].
    rewrite Hai in Hmove. exact Hmove.
  Qed.

  (* ------------------------------------------------------------------- *)
  (* ecall, at CLOSE, IN ITS TWO FOOTPRINTS.                               *)
  (*                                                                       *)
  (* A TAIL descriptor's handle is SPENT and nothing comes back: the slot  *)
  (* leaves the program's map, which is the right reading (a program that  *)
  (* closed a descriptor must not keep saying it is open) and is what      *)
  (* makes a double close visible -- the second call has no handle to      *)
  (* offer.  No ledger is involved, which is what keeps close out of the   *)
  (* way of every program that opens a file and closes it.                 *)
  (*                                                                       *)
  (* A STANDARD STREAM cannot leave the map, so its fragment comes back    *)
  (* SHUT, inside the ledger -- and THAT is the resource the next          *)
  (* allocation spends.  It is the whole mechanism behind [close(1);       *)
  (* dup(x)] landing on 1.                                                 *)
  (*                                                                       *)
  (* NEITHER ARM CASES ON THE RETURN VALUE, and that is a promise the row  *)
  (* now makes rather than something these leaves assume: closing an OPEN  *)
  (* descriptor returns 0 ([UsysMemOk.usys_fd_ok]'s close row, second      *)
  (* conjunct; [argfd] rejects only an out-of-range index and a null slot, *)
  (* and an open state refutes both).  Without it every caller would carry *)
  (* a failure arm it can never discharge -- xv6's sh writes [close(fd);   *)
  (* open(path)] and checks neither result.                                *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_uk_ecall_close (γt γd γs γfd : gname) (h : CpuId) (m : regfile)
      (pc : mword 64) (fd : nat) (st : fdstate) (avail : nat) :
    usysno m = USYS_close ->
    bv_signed (trunc32 (m !!! Regidx (mword_of_int 10))) = Z.of_nat fd ->
    is_aligned_vaddr (Virtaddr (add_vec_int pc 4)) 2 = true ->
    uinstr_is γt pc false (ECALL tt) -∗
    urun γt γd γs γfd h m pc avail -∗
    ufd γfd fd st -∗
    (∀ (h' : CpuId) (r : mword 64),
       ⌜uint r = 0⌝ -∗
       urun γt γd γs γfd h' (<[Regidx (mword_of_int 10) := r]> m)
         (add_vec_int pc 4) avail -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hn Harg Hal4.
    iIntros "#Hi Hrun Hh Hcont".
    iDestruct "Hrun" as (xi C pt Rfd Rut sz M pm fdv) "(%Hlo & %Hpm & Hheap & Hstk & Hufd & Hb)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iDestruct (uvb_x0 with "Hb") as "[%Hx0 Hb]".
    iDestruct (ufd_agree with "Hufd Hh") as %Hi.
    iDestruct (ufd_ne with "Hh") as %Hne.
    iApply (UkStep.wp_uk_ecall C pt Rfd Rut pm sz Hlo Hpm M m pc fdv Hui
              (fun (s : mstate)
                   (Hp : register_lookup cur_privilege s.(sregs) = User)
                   (Hc : register_lookup (R_bitvector_64 PC) s.(sregs) = pc) =>
                 UserExecFacts.goodmb_execute_ECALL_U UserFrame.Du_r UserFrame.Du_w
                   s pc ltac:(vm_compute; reflexivity)
                   ltac:(vm_compute; reflexivity) Hp Hc)
              with "Hb").
    rewrite (uexec_ret_ecall _ _ eq_refl).
    assert (Hnum : usys_num (uvis_tf (uvis_of_run m pc M pm sz fdv)) = USYS_close).
    { cbn [uvis_tf uvis_of_run]. rewrite tf_of_num. exact Hn. }
    rewrite Hnum. cbv zeta.
    destruct (decide (USYS_close = USYS_exit)) as [He | _];
      [ exfalso; vm_compute in He; discriminate | ].
    destruct (decide (USYS_close = USYS_fork)) as [He | _];
      [ exfalso; vm_compute in He; discriminate | ].
    iIntros (r M' pm' sz' fdv') "%Hok %Hfdok %Hpiperow".
    destruct (usys_mem_ok_quiet USYS_close _ r _ _ _ _ _ _
                ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)
                ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) Hok)
      as [-> [-> ->]].
    cbn [uvis_M uvis_perm uvis_fd uvis_of_run] in Hfdok |- *.
    destruct (uk_close_row m pc fd st fdv fdv' r Harg Hi Hne Hfdok)
      as [Hr0 ->].
    iApply uslot_bupd.
    iMod (ufd_close_hi γfd fdv fd st with "Hufd Hh") as "Hufd".
    iModIntro.
    rewrite (uslot_bump_run m pc M M pm pm sz sz fdv
               (<[fd := FdClosed]> fdv) r Hx0 Hal4).
    iApply (urun_close_upd _ _ _ _ _ _ m (mword_of_int 10) _ _ _ _ _
              ltac:(unfold unot_sp; vm_compute; discriminate)
              with "Hheap Hstk Hufd").
    iIntros (h') "Hrun". iApply ("Hcont" $! h' r with "[%] Hrun"). exact Hr0.
  Qed.

  (* ...and the STANDARD-STREAM close, which spends the ledger's own entry
     and hands it back at [FdClosed]. *)
  Lemma wp_uk_ecall_close_std (γt γd γs γfd : gname) (h : CpuId) (m : regfile)
      (pc : mword 64) (l : list fdstate) (fd : nat) (st : fdstate)
      (avail : nat) :
    usysno m = USYS_close ->
    bv_signed (trunc32 (m !!! Regidx (mword_of_int 10))) = Z.of_nat fd ->
    (fd < NSTD)%nat -> l !! fd = Some st -> st <> FdClosed ->
    is_aligned_vaddr (Virtaddr (add_vec_int pc 4)) 2 = true ->
    uinstr_is γt pc false (ECALL tt) -∗
    urun γt γd γs γfd h m pc avail -∗
    ustd γfd l -∗
    (∀ (h' : CpuId) (r : mword 64),
       ⌜uint r = 0⌝ -∗
       ustd γfd (<[fd := FdClosed]> l) -∗
       urun γt γd γs γfd h' (<[Regidx (mword_of_int 10) := r]> m)
         (add_vec_int pc 4) avail -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hn Harg Hs Hkl Hne Hal4.
    iIntros "#Hi Hrun Hstd Hcont".
    iDestruct "Hrun" as (xi C pt Rfd Rut sz M pm fdv) "(%Hlo & %Hpm & Hheap & Hstk & Hufd & Hb)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iDestruct (uvb_x0 with "Hb") as "[%Hx0 Hb]".
    iDestruct (ustd_agree with "Hufd Hstd") as %Hst.
    assert (Hi : fdv !! fd = Some st).
    { rewrite <- (lookup_take fdv NSTD fd Hs). by rewrite Hst. }
    iApply (UkStep.wp_uk_ecall C pt Rfd Rut pm sz Hlo Hpm M m pc fdv Hui
              (fun (s : mstate)
                   (Hp : register_lookup cur_privilege s.(sregs) = User)
                   (Hc : register_lookup (R_bitvector_64 PC) s.(sregs) = pc) =>
                 UserExecFacts.goodmb_execute_ECALL_U UserFrame.Du_r UserFrame.Du_w
                   s pc ltac:(vm_compute; reflexivity)
                   ltac:(vm_compute; reflexivity) Hp Hc)
              with "Hb").
    rewrite (uexec_ret_ecall _ _ eq_refl).
    assert (Hnum : usys_num (uvis_tf (uvis_of_run m pc M pm sz fdv)) = USYS_close).
    { cbn [uvis_tf uvis_of_run]. rewrite tf_of_num. exact Hn. }
    rewrite Hnum. cbv zeta.
    destruct (decide (USYS_close = USYS_exit)) as [He | _];
      [ exfalso; vm_compute in He; discriminate | ].
    destruct (decide (USYS_close = USYS_fork)) as [He | _];
      [ exfalso; vm_compute in He; discriminate | ].
    iIntros (r M' pm' sz' fdv') "%Hok %Hfdok %Hpiperow".
    destruct (usys_mem_ok_quiet USYS_close _ r _ _ _ _ _ _
                ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)
                ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) Hok)
      as [-> [-> ->]].
    cbn [uvis_M uvis_perm uvis_fd uvis_of_run] in Hfdok |- *.
    destruct (uk_close_row m pc fd st fdv fdv' r Harg Hi Hne Hfdok) as [Hr0 ->].
    iApply uslot_bupd.
    iMod (ufd_close_std γfd fdv l fd st Hs Hkl with "Hufd Hstd") as "[Hufd Hstd]".
    iModIntro.
    rewrite (uslot_bump_run m pc M M pm pm sz sz fdv
               (<[fd := FdClosed]> fdv) r Hx0 Hal4).
    iApply (urun_close_upd _ _ _ _ _ _ m (mword_of_int 10) _ _ _ _ _
              ltac:(unfold unot_sp; vm_compute; discriminate)
              with "Hheap Hstk Hufd").
    iIntros (h') "Hrun". iApply ("Hcont" $! h' r with "[%] Hstd Hrun"). exact Hr0.
  Qed.

  (* ------------------------------------------------------------------- *)
  (* ecall, at exit.  The process never comes back, so it owes NOTHING --  *)
  (* not even a continuation.  This is the only leaf with no successor.    *)
  (* ------------------------------------------------------------------- *)

  (* ------------------------------------------------------------------- *)
  (* ecall, at read -- THE FIRST SYSCALL IN THIS TIER THAT WRITES USER     *)
  (* MEMORY.                                                              *)
  (*                                                                      *)
  (* [UsysMemOk]'s read row says the kernel wrote SOME [d] bytes at        *)
  (* argument 1, no more than the count at argument 2, and left the        *)
  (* permission map and the break alone.  It does not say WHICH bytes, and *)
  (* it does not tie [d] to the return value -- so this leaf does not      *)
  (* either.  What it does say is the only thing a caller can use: hand in *)
  (* the whole count as a run you own, get the whole count back at SOME    *)
  (* contents.                                                            *)
  (*                                                                      *)
  (* OWNING THE WHOLE COUNT IS THE PREMISE, not a convenience.  The row    *)
  (* licenses a write anywhere in [buf .. buf+cnt), so a caller that owned *)
  (* less could not absorb it, and the heap would be left describing bytes *)
  (* the kernel had changed underneath it.                                *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_uk_ecall_read (γt γd γs γfd : gname) (h : CpuId) (m : regfile)
      (pc : mword 64) (a : Z) (cnt : nat) (f : nat -> bv 8) (avail : nat) :
    usysno m = USYS_read ->
    m !!! Regidx (mword_of_int 11) = (mword_of_int a : mword 64) ->
    bv_signed (subrange_vec_dec (m !!! Regidx (mword_of_int 12)) 31 0
               : mword 32) = Z.of_nat cnt ->
    is_aligned_vaddr (Virtaddr (add_vec_int pc 4)) 2 = true ->
    uinstr_is γt pc false (ECALL tt) -∗
    ubytes γd a cnt f -∗
    urun γt γd γs γfd h m pc avail -∗
    (∀ (h' : CpuId) (r : mword 64) (g : nat -> bv 8),
       ubytes γd a cnt g -∗
       urun γt γd γs γfd h' (<[Regidx (mword_of_int 10) := r]> m)
         (add_vec_int pc 4) avail -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hn Ha1 Hcnt Hal4.
    iIntros "#Hi Hbs Hrun Hcont".
    iDestruct "Hrun" as (xi C pt Rfd Rut sz M pm fdv) "(%Hlo & %Hpm & Hheap & Hstk & Hufd & Hb)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iDestruct (uvb_x0 with "Hb") as "[%Hx0 Hb]".
    (* the run is in the image, and does not wrap *)
    iDestruct (uheap_ubytes_img with "Hheap Hbs") as %Himg.
    iApply (UkStep.wp_uk_ecall C pt Rfd Rut pm sz Hlo Hpm M m pc fdv Hui
              (fun (s : mstate)
                   (Hp : register_lookup cur_privilege s.(sregs) = User)
                   (Hc : register_lookup (R_bitvector_64 PC) s.(sregs) = pc) =>
                 UserExecFacts.goodmb_execute_ECALL_U UserFrame.Du_r UserFrame.Du_w
                   s pc ltac:(vm_compute; reflexivity)
                   ltac:(vm_compute; reflexivity) Hp Hc)
              with "Hb").
    rewrite (uexec_ret_ecall _ _ eq_refl).
    assert (Hnum : usys_num (uvis_tf (uvis_of_run m pc M pm sz fdv)) = USYS_read).
    { cbn [uvis_tf uvis_of_run]. rewrite tf_of_num. exact Hn. }
    rewrite Hnum. cbv zeta.
    destruct (decide (USYS_read = USYS_exit)) as [He | _];
      [ exfalso; vm_compute in He; discriminate | ].
    destruct (decide (USYS_read = USYS_fork)) as [He | _];
      [ exfalso; vm_compute in He; discriminate | ].
    iIntros (r M' pm' sz' fdv') "%Hok %Hfdok %Hpiperow".
    (* unfold the row down to its read arm *)
    unfold usys_mem_ok in Hok.
    destruct (decide (USYS_read = USYS_exec)) as [He | _];
      [ exfalso; vm_compute in He; discriminate | ].
    destruct (decide (USYS_read = USYS_sbrk)) as [He | _];
      [ exfalso; vm_compute in He; discriminate | ].
    destruct (decide (USYS_read = USYS_wait)) as [He | _];
      [ exfalso; vm_compute in He; discriminate | ].
    destruct (decide (USYS_read = USYS_pipe)) as [He | _];
      [ exfalso; vm_compute in He; discriminate | ].
    destruct (decide (USYS_read = USYS_read)) as [_ | Hne];
      [ | exfalso; exact (Hne eq_refl) ].
    destruct Hok as [(d & bs & Hdle & HM') [-> ->]].
    (* the row's [d] is within the run the caller owns *)
    cbn [uvis_tf uvis_of_run] in Hdle, HM'.
    unfold usys_rdcount in Hdle. rewrite tf_of_arg2 in Hdle.
    rewrite Hcnt in Hdle.
    assert (Hdn : (d <= cnt)%nat) by lia.
    rewrite tf_of_arg1 Ha1 in HM'.
    (* ...so writing [d] of them is writing all [cnt], the tail unchanged *)
    (* the row addresses through [add_vec_int], the heap through [Z] --
       and they agree, because every owned address is below MAXVA *)
    assert (Hwrap : forall k : nat, (k < d)%nat ->
               uint (add_vec_int (mword_of_int a : mword 64) (Z.of_nat k))
               = (a + Z.of_nat k)%Z).
    { intros k Hk.
      destruct (proj2 (Himg 0%nat ltac:(lia))) as [Ha0 _].
      destruct (proj2 (Himg k ltac:(lia))) as [_ Hak].
      assert (Ha64 : 0 <= a < Z64) by (unfold Z64; lia).
      assert (Hak64 : 0 <= a + Z.of_nat k < Z64) by (unfold Z64; lia).
      unfold add_vec_int.
      rewrite moi_add_l (uint_moi a Ha64).
      exact (uint_moi (a + Z.of_nat k) Hak64). }
    rewrite (UserPtTree.umem_wr_write M a d bs Hwrap) in HM'.
    rewrite (umem_write_prefix M a cnt d bs f Hdn
               ltac:(intros k Hk; exact (proj1 (Himg k Hk)))) in HM'.
    subst M'.
    (* the slot ends in a [WP], so it absorbs the heap's update -- which is
       the only place the update CAN run, the row being what says how far
       the image moved *)
    iApply uslot_bupd.
    iMod (uheap_store_run γt γd γs M pm a cnt f
            (fun k => if decide (k < d)%nat then bs k else f k)
            with "Hheap Hbs") as "[Hheap Hbs]".
    iModIntro.
    cbn [uvis_M uvis_perm uvis_of_run].
    (* the row read, not dropped: this entry is none of the four that move
       [p->ofile[]], so the table -- and the authority [urun] carries -- is
       already at the view the process resumes at. *)
    (* [refine] first, so the four side goals are at the CONCRETE number --
       as an [ltac:] argument they would run while it was still an evar. *)
    assert (Hview : fdv' = fdv).
    { refine (usys_fd_ok_quiet _ _ _ _ _ _ _ _ _ Hfdok);
        vm_compute; discriminate. }
    subst fdv'.
    rewrite (uslot_bump_run m pc M
               (umem_write M a cnt
                  (fun k => if decide (k < d)%nat then bs k else f k))
               pm pm sz sz fdv fdv r Hx0 Hal4).
    iApply (urun_close_upd _ _ _ _ _ _ m (mword_of_int 10) _ _ _ _ _
              ltac:(unfold unot_sp; vm_compute; discriminate) with "Hheap Hstk Hufd").
    iIntros (h') "Hrun".
    iApply ("Hcont" $! h' r _ with "Hbs Hrun").
  Qed.

  (* ------------------------------------------------------------------- *)
  (* EXEC'S FAILURE ARM.  A successful exec never returns to this WP at all *)
  (* -- the new program's is minted by exec from the new trapframe and     *)
  (* image -- so the only arm that comes back is the failure, and the row  *)
  (* says so outright: -1, and not one byte moved.                         *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_uk_ecall_exec (γt γd γs γfd : gname) (h : CpuId) (m : regfile)
      (pc : mword 64) (avail : nat) :
    usysno m = USYS_exec ->
    is_aligned_vaddr (Virtaddr (add_vec_int pc 4)) 2 = true ->
    uinstr_is γt pc false (ECALL tt) -∗
    urun γt γd γs γfd h m pc avail -∗
    (∀ h' : CpuId,
       urun γt γd γs γfd h'
         (<[Regidx (mword_of_int 10) := (mword_of_int (-1) : mword 64)]> m)
         (add_vec_int pc 4) avail -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hn Hal4.
    iIntros "#Hi Hrun Hcont".
    iDestruct "Hrun" as (xi C pt Rfd Rut sz M pm fdv) "(%Hlo & %Hpm & Hheap & Hstk & Hufd & Hb)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iDestruct (uvb_x0 with "Hb") as "[%Hx0 Hb]".
    iApply (UkStep.wp_uk_ecall C pt Rfd Rut pm sz Hlo Hpm M m pc fdv Hui
              (fun (s : mstate)
                   (Hp : register_lookup cur_privilege s.(sregs) = User)
                   (Hc : register_lookup (R_bitvector_64 PC) s.(sregs) = pc) =>
                 UserExecFacts.goodmb_execute_ECALL_U UserFrame.Du_r UserFrame.Du_w
                   s pc ltac:(vm_compute; reflexivity)
                   ltac:(vm_compute; reflexivity) Hp Hc)
              with "Hb").
    rewrite (uexec_ret_ecall _ _ eq_refl).
    assert (Hnum : usys_num (uvis_tf (uvis_of_run m pc M pm sz fdv)) = USYS_exec).
    { cbn [uvis_tf uvis_of_run]. rewrite tf_of_num. exact Hn. }
    rewrite Hnum. cbv zeta.
    destruct (decide (USYS_exec = USYS_exit)) as [He | _];
      [ exfalso; unfold USYS_exec, USYS_exit in He; discriminate He | ].
    destruct (decide (USYS_exec = USYS_fork)) as [He | _];
      [ exfalso; unfold USYS_exec, USYS_fork in He; discriminate He | ].
    iIntros (r M' pm' sz' fdv') "%Hok %Hfdok %Hpiperow".
    destruct (usys_mem_ok_exec_row USYS_exec _ r _ _ _ _ _ _ eq_refl Hok)
      as [-> [-> [-> ->]]].
    cbn [uvis_M uvis_perm uvis_of_run].
    (* the row read, not dropped: this entry is none of the four that move
       [p->ofile[]], so the table -- and the authority [urun] carries -- is
       already at the view the process resumes at. *)
    (* [refine] first, so the four side goals are at the CONCRETE number --
       as an [ltac:] argument they would run while it was still an evar. *)
    assert (Hview : fdv' = fdv).
    { refine (usys_fd_ok_quiet _ _ _ _ _ _ _ _ _ Hfdok);
        vm_compute; discriminate. }
    subst fdv'.
    rewrite (uslot_bump_run m pc M M pm pm sz sz fdv fdv
               (mword_of_int (-1) : mword 64) Hx0 Hal4).
    iApply (urun_close_upd _ _ _ _ _ _ m (mword_of_int 10) _ _ _ _ _
              ltac:(unfold unot_sp; vm_compute; discriminate) with "Hheap Hstk Hufd").
    iIntros (h') "Hrun".
    iApply ("Hcont" $! h' with "Hrun").
  Qed.

  (* ------------------------------------------------------------------- *)
  (* WAIT AT A NULL STATUS POINTER.  The kernel's own [addr != 0] test     *)
  (* means nothing is copied out, so the heap the caller owns comes back   *)
  (* untouched and the leaf can hand the SAME run on -- exactly the quiet  *)
  (* row's shape.  This is the arm init and sh both take.                  *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_uk_ecall_wait_null (γt γd γs γfd : gname) (h : CpuId) (m : regfile)
      (pc : mword 64) (avail : nat) :
    usysno m = USYS_wait ->
    uint (m !!! Regidx (mword_of_int 10)) = 0 ->
    is_aligned_vaddr (Virtaddr (add_vec_int pc 4)) 2 = true ->
    uinstr_is γt pc false (ECALL tt) -∗
    urun γt γd γs γfd h m pc avail -∗
    (∀ (h' : CpuId) (r : mword 64),
       urun γt γd γs γfd h' (<[Regidx (mword_of_int 10) := r]> m)
         (add_vec_int pc 4) avail -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hn Hz Hal4.
    iIntros "#Hi Hrun Hcont".
    iDestruct "Hrun" as (xi C pt Rfd Rut sz M pm fdv) "(%Hlo & %Hpm & Hheap & Hstk & Hufd & Hb)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iDestruct (uvb_x0 with "Hb") as "[%Hx0 Hb]".
    iApply (UkStep.wp_uk_ecall C pt Rfd Rut pm sz Hlo Hpm M m pc fdv Hui
              (fun (s : mstate)
                   (Hp : register_lookup cur_privilege s.(sregs) = User)
                   (Hc : register_lookup (R_bitvector_64 PC) s.(sregs) = pc) =>
                 UserExecFacts.goodmb_execute_ECALL_U UserFrame.Du_r UserFrame.Du_w
                   s pc ltac:(vm_compute; reflexivity)
                   ltac:(vm_compute; reflexivity) Hp Hc)
              with "Hb").
    rewrite (uexec_ret_ecall _ _ eq_refl).
    assert (Hnum : usys_num (uvis_tf (uvis_of_run m pc M pm sz fdv)) = USYS_wait).
    { cbn [uvis_tf uvis_of_run]. rewrite tf_of_num. exact Hn. }
    assert (Ha0 : uint (uvis_tf (uvis_of_run m pc M pm sz fdv) !!! tf_arg_idx 0) = 0).
    { cbn [uvis_tf uvis_of_run]. rewrite tf_of_arg0. exact Hz. }
    rewrite Hnum. cbv zeta.
    destruct (decide (USYS_wait = USYS_exit)) as [He | _];
      [ exfalso; unfold USYS_wait, USYS_exit in He; discriminate He | ].
    destruct (decide (USYS_wait = USYS_fork)) as [He | _];
      [ exfalso; unfold USYS_wait, USYS_fork in He; discriminate He | ].
    iIntros (r M' pm' sz' fdv') "%Hok %Hfdok %Hpiperow".
    destruct (usys_mem_ok_wait_null USYS_wait _ r _ _ _ _ _ _
                eq_refl Ha0 Hok) as [-> [-> ->]].
    cbn [uvis_M uvis_perm uvis_of_run].
    (* the row read, not dropped: this entry is none of the four that move
       [p->ofile[]], so the table -- and the authority [urun] carries -- is
       already at the view the process resumes at. *)
    (* [refine] first, so the four side goals are at the CONCRETE number --
       as an [ltac:] argument they would run while it was still an evar. *)
    assert (Hview : fdv' = fdv).
    { refine (usys_fd_ok_quiet _ _ _ _ _ _ _ _ _ Hfdok);
        vm_compute; discriminate. }
    subst fdv'.
    rewrite (uslot_bump_run m pc M M pm pm sz sz fdv fdv r Hx0 Hal4).
    iApply (urun_close_upd _ _ _ _ _ _ m (mword_of_int 10) _ _ _ _ _
              ltac:(unfold unot_sp; vm_compute; discriminate) with "Hheap Hstk Hufd").
    iIntros (h') "Hrun".
    iApply ("Hcont" $! h' r with "Hrun").
  Qed.

  (* ------------------------------------------------------------------- *)
  (* ecall, at a WINDOW syscall.  Four entries -- read, wait at a status   *)
  (* pointer it is willing to own, pipe, fstat -- may write a buffer the   *)
  (* caller named, and they differ in exactly two numbers: WHICH argument  *)
  (* names the buffer and HOW MANY bytes may go there ([usyswin]).  So     *)
  (* this is ONE leaf, not four.                                           *)
  (*                                                                       *)
  (* THE CALLER HANDS THE WINDOW OVER, and that is the whole price.  It    *)
  (* owns [k] bytes at the address its own argument named, [k] at least    *)
  (* the cap that argument implies, and gets them back with a PREFIX of    *)
  (* length [d <= cap] replaced by bytes it does not name.  Everything     *)
  (* else it holds survives BY SEPARATION -- nothing outside the window is *)
  (* mentioned, so no frame equation has to be kept precise.  [k] may      *)
  (* exceed the cap because a program hands over the buffer it HAS, not    *)
  (* the prefix a count happens to name.                                   *)
  (*                                                                       *)
  (* THE NO-WRAP FACT IS NOT A PREMISE.  The row is keyed by               *)
  (* [uint (add_vec_int dst j)] and the heap by [uint dst + j]; owning the *)
  (* run is what makes the two agree, because [uheap] bounds every mapped  *)
  (* address by MAXVA.  A caller therefore owes nothing about its buffer's *)
  (* address beyond the bytes themselves.                                  *)
  (*                                                                       *)
  (* WHAT THE ROW DOES NOT SAY.  [d] is existential, bounded by the cap and *)
  (* tied to nothing else -- in particular NOT to the return value, so a    *)
  (* read's caller learns [d <= count] and not [d = r].  That link is real  *)
  (* on the kernel side ([SpecSysReadAU]) but has never been carried into   *)
  (* [usys_mem_ok]'s read row, so it cannot be stated here.  [d] is exposed *)
  (* anyway: the day the row carries it, this statement takes it without   *)
  (* moving.                                                                *)
  (*                                                                       *)
  (* A NULL DESTINATION is not a case here.  wait's row already forces      *)
  (* [d = 0] at a null status pointer, so [wp_uk_ecall_wait_null] is the    *)
  (* instance for a caller that owns NOTHING, and this leaf is the one for  *)
  (* a caller that does.                                                    *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_uk_ecall_window (γt γd γs γfd : gname) (h : CpuId) (m : regfile)
      (pc : mword 64) (n : Z) (dst : mword 64) (cap k : nat)
      (f : nat -> bv 8) (avail : nat) :
    usysno m = n ->
    usyswin m n = Some (dst, cap) ->
    (cap <= k)%nat ->
    (* ...AND IT MOVES NO DESCRIPTOR.  This leaf re-closes the run at the
       view it opened at, so it may not be used where the table moved.
       [pipe] is the one entry in the window's own domain that does -- it
       reports its two descriptors by WRITING them, which is why it is a
       window call at all -- so it is excluded here and owes a leaf of its
       own; the other three are outside the domain and cost nothing. *)
    n <> USYS_close -> n <> USYS_dup -> n <> USYS_open -> n <> USYS_pipe ->
    is_aligned_vaddr (Virtaddr (add_vec_int pc 4)) 2 = true ->
    uinstr_is γt pc false (ECALL tt) -∗
    urun γt γd γs γfd h m pc avail -∗
    ubytes γd (uint dst) k f -∗
    (∀ (h' : CpuId) (r : mword 64) (d : nat) (g : nat -> bv 8),
       ⌜ (d <= cap)%nat ⌝ -∗
       ⌜ forall j : nat, (d <= j < k)%nat -> g j = f j ⌝ -∗
       urun γt γd γs γfd h' (<[Regidx (mword_of_int 10) := r]> m)
         (add_vec_int pc 4) avail -∗
       ubytes γd (uint dst) k g -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hn Hwin Hcapk Hcl Hdp Hop Hpp Hal4.
    iIntros "#Hi Hrun Hbuf Hcont".
    iDestruct "Hrun" as (xi C pt Rfd Rut sz M pm fdv) "(%Hlo & %Hpm & Hheap & Hstk & Hufd & Hb)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iDestruct (uvb_x0 with "Hb") as "[%Hx0 Hb]".
    (* THE NO-WRAP FACT, off the ownership rather than off a premise *)
    iDestruct (uheap_ubytes_run γt γd γs M pm (DfracOwn 1) (uint dst) k f
                 with "Hheap Hbuf") as %Hbnd.
    assert (Hlin : forall i : nat, (i < k)%nat ->
              uint (add_vec_int dst (Z.of_nat i)) = (uint dst + Z.of_nat i)%Z).
    { intros i Hi. destruct (Hbnd i Hi) as [_ Hc].
      change (2 ^ 38) with 274877906944 in Hc.
      rewrite !uint_unsigned in Hc |- *.
      apply uint_add_vec_int_small; lia. }
    iApply (UkStep.wp_uk_ecall C pt Rfd Rut pm sz Hlo Hpm M m pc fdv Hui
              (fun (s : mstate)
                   (Hp : register_lookup cur_privilege s.(sregs) = User)
                   (Hc : register_lookup (R_bitvector_64 PC) s.(sregs) = pc) =>
                 UserExecFacts.goodmb_execute_ECALL_U UserFrame.Du_r UserFrame.Du_w
                   s pc ltac:(vm_compute; reflexivity)
                   ltac:(vm_compute; reflexivity) Hp Hc)
              with "Hb").
    rewrite (uexec_ret_ecall _ _ eq_refl).
    assert (Hnum : usys_num (uvis_tf (uvis_of_run m pc M pm sz fdv)) = n).
    { cbn [uvis_tf uvis_of_run]. rewrite tf_of_num. exact Hn. }
    assert (Hw : usys_win n (uvis_tf (uvis_of_run m pc M pm sz fdv))
                 = Some (dst, cap)).
    { cbn [uvis_tf uvis_of_run]. rewrite usyswin_tf_of. exact Hwin. }
    destruct (usys_win_num n _ dst cap Hw) as (Hexit & Hfork & _ & _).
    rewrite Hnum. cbv zeta.
    destruct (decide (n = USYS_exit)) as [He | _]; [ exfalso; exact (Hexit He) | ].
    destruct (decide (n = USYS_fork)) as [He | _]; [ exfalso; exact (Hfork He) | ].
    iIntros (r M' pm' sz' fdv') "%Hok %Hfdok %Hpiperow".
    destruct (usys_mem_ok_window n _ r _ _ _ _ _ _ dst cap Hw Hok)
      as ((d & bs & Hdcap & HM') & -> & ->).
    cbn [uvis_M uvis_perm uvis_sz uvis_of_run] in HM' |- *.
    (* THE BYTES THE CALLER GETS BACK: the kernel's below [d], its own
       above.  [bs] is the row's existential, so naming the joined function
       here costs nothing and is what makes the run RE-ASSEMBLE as one. *)
    assert (Hg : exists g : nat -> bv 8,
              (forall j : nat, (j < d)%nat -> g j = bs j) /\
              (forall j : nat, (d <= j)%nat -> g j = f j)).
    { exists (fun j => if decide (j < d)%nat then bs j else f j).
      split; intros j Hj; case_decide as Hc;
        [ reflexivity | exfalso; lia | exfalso; lia | reflexivity ]. }
    destruct Hg as (g & Hgb & Hgf).
    assert (Hdk : (d <= k)%nat) by lia.
    rewrite (umem_wr_ext M dst d bs g
               ltac:(intros i Hi; symmetry; exact (Hgb i Hi))) in HM'.
    rewrite (umem_wr_write M dst d g
               ltac:(intros i Hi; apply Hlin; lia)) in HM'.
    subst M'.
    (* the row read, not dropped: this entry is none of the four that move
       [p->ofile[]], so the table -- and the authority [urun] carries -- is
       already at the view the process resumes at. *)
    assert (Hview : fdv' = fdv)
      by exact (usys_fd_ok_quiet _ _ _ _ _ Hcl Hdp Hop Hpp Hfdok).
    subst fdv'.
    rewrite (uslot_bump_run m pc M (umem_write M (uint dst) d g) pm pm sz sz
               fdv fdv r Hx0 Hal4).
    (* [uheap_store_run] is a basic update and [ukc] is not a [WP], so the
       re-assembly runs under [ukc]'s own binders -- which is why this leaf
       opens the close by hand instead of applying it to the goal. *)
    rewrite /ukc. iIntros (h' xi' C' pt' Rfd' Rut') "%Hlo' %Hpm' Hb'".
    iEval (rewrite (ubytes_split γd (uint dst) d k f Hdk)) in "Hbuf".
    iDestruct "Hbuf" as "[Hblo Hbhi]".
    iMod (uheap_store_run γt γd γs M pm (uint dst) d f g with "Hheap Hblo")
      as "[Hheap Hblo]".
    iDestruct (ubytes_ext γd (uint dst + Z.of_nat d) (k - d)
                 (fun j => f (d + j)%nat) (fun j => g (d + j)%nat)
                 ltac:(intros j _; symmetry; apply Hgf; lia) with "Hbhi")
      as "Hbhi".
    iAssert (ubytes γd (uint dst) k g) with "[Hblo Hbhi]" as "Hbuf".
    { rewrite (ubytes_split γd (uint dst) d k g Hdk). iFrame "Hblo Hbhi". }
    iDestruct (urun_close_upd γt γd γs γfd (umem_write M (uint dst) d g) pm m
                 (mword_of_int 10) r sz fdv (add_vec_int pc 4) avail
                 ltac:(unfold unot_sp; vm_compute; discriminate)
                 with "Hheap Hstk Hufd [Hcont Hbuf]") as "Hkc";
      [ iIntros (h'') "Hrun";
        iApply ("Hcont" $! h'' r d g with "[%] [%] Hrun Hbuf");
        [ exact Hdcap | intros j Hj; apply Hgf; lia ] | ].
    iApply ("Hkc" $! h' xi' C' pt' Rfd' Rut' with "[%] [%] Hb'");
      [ exact Hlo' | exact Hpm' ].
  Qed.


  (* ------------------------------------------------------------------- *)
  (* ecall, at PIPE -- the one entry that is BOTH a window call and a      *)
  (* descriptor call, and the reason the joined row exists.                *)
  (*                                                                       *)
  (* Every other allocating entry reports its descriptor in a0, where the  *)
  (* bump puts it and [wp_uk_ecall_open] can simply read it off.  pipe     *)
  (* returns 0 and reports its TWO descriptors by writing them into the    *)
  (* caller's [int fd[2]] -- so a leaf built out of [usys_mem_ok] and      *)
  (* [usys_fd_ok] alone would hand back eight bytes of unknown content     *)
  (* beside two handles for unknown slots, and a caller could never close  *)
  (* what it was given.  [UsysMemOk.usys_pipe_ok] is the row that ties the *)
  (* two, and this leaf is where the tie is spent: the bytes the caller    *)
  (* reads back ARE the two descriptors it holds handles for.              *)
  (*                                                                       *)
  (* THE BUFFER IS A PRECONDITION, exactly as in [wp_uk_ecall_window]: a   *)
  (* caller owns the eight bytes at a0 going in and gets them back written.*)
  (* The no-wrap fact is again off the ownership, not off a premise.       *)
  (*                                                                       *)
  (* ON FAILURE nothing is promised about the buffer.  The image row lets  *)
  (* pipe write up to eight bytes unconditionally, and the joined row is   *)
  (* guarded on [uint r = 0], so a failed call may legitimately have       *)
  (* scribbled -- the caller gets its run back at an arbitrary [g] and no  *)
  (* handles.  That is what the kernel actually promises.                  *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_uk_ecall_pipe (γt γd γs γfd : gname) (h : CpuId) (m : regfile)
      (pc : mword 64) (l : list fdstate) (f : nat -> bv 8) (avail : nat) :
    usysno m = USYS_pipe ->
    is_aligned_vaddr (Virtaddr (add_vec_int pc 4)) 2 = true ->
    uinstr_is γt pc false (ECALL tt) -∗
    urun γt γd γs γfd h m pc avail -∗
    ustd γfd l -∗
    ubytes γd (uint (m !!! Regidx (mword_of_int 10))) 8 f -∗
    (∀ (h' : CpuId) (r : mword 64) (g : nat -> bv 8),
       ((∃ a b : nat,
           (* the two slots, their bound (so the caller can read either
              back as a C [int] and feed it to close), and -- the point of
              the whole row -- that the eight bytes it just got back SPELL
              them, read end first *)
           ⌜ uint r = 0 /\ a <> b /\ (a < NOFILE)%nat /\ (b < NOFILE)%nat
             /\ (forall i : nat, (i < 8)%nat ->
                   g i = if (i <? 4)%nat
                         then nth_byte
                                (trunc32 (mword_of_int (Z.of_nat a) : mword 64)) i
                         else nth_byte
                                (trunc32 (mword_of_int (Z.of_nat b) : mword 64))
                                (i - 4)%nat) ⌝ ∗
           (* PIPE ALLOCATES TWICE, so its post is two ARMS and ONE
              ledger: the read end's scan runs on the caller's ledger and
              the write end's on the ledger that left.  At an all-open
              ledger -- which is where any program that has not just closed
              a standard stream is -- both arms are handles and the ledger
              does not move at all. *)
           ualloc_at γfd l a (FdOpen true false FdPipe) ∗
           ualloc_at γfd (ustd_after l (FdOpen true false FdPipe)) b
             (FdOpen false true FdPipe) ∗
           ustd γfd (ustd_after (ustd_after l (FdOpen true false FdPipe))
                       (FdOpen false true FdPipe)))
        ∨ (⌜ uint r <> 0 ⌝ ∗ ustd γfd l)) -∗
       urun γt γd γs γfd h' (<[Regidx (mword_of_int 10) := r]> m)
         (add_vec_int pc 4) avail -∗
       ubytes γd (uint (m !!! Regidx (mword_of_int 10))) 8 g -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hn Hal4.
    set (dst := m !!! Regidx (mword_of_int 10)).
    iIntros "#Hi Hrun Hstd Hbuf Hcont".
    iDestruct "Hrun" as (xi C pt Rfd Rut sz M pm fdv) "(%Hlo & %Hpm & Hheap & Hstk & Hufd & Hb)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iDestruct (uvb_x0 with "Hb") as "[%Hx0 Hb]".
    iDestruct (ufd_auth_len with "Hufd") as %Hfdlen.
    iDestruct (uheap_ubytes_run γt γd γs M pm (DfracOwn 1) (uint dst) 8 f
                 with "Hheap Hbuf") as %Hbnd.
    assert (Hlin : forall i : nat, (i < 8)%nat ->
              uint (add_vec_int dst (Z.of_nat i)) = (uint dst + Z.of_nat i)%Z).
    { intros i Hi. destruct (Hbnd i Hi) as [_ Hc].
      change (2 ^ 38) with 274877906944 in Hc.
      rewrite !uint_unsigned in Hc |- *.
      apply uint_add_vec_int_small; lia. }
    iApply (UkStep.wp_uk_ecall C pt Rfd Rut pm sz Hlo Hpm M m pc fdv Hui
              (fun (s : mstate)
                   (Hp : register_lookup cur_privilege s.(sregs) = User)
                   (Hc : register_lookup (R_bitvector_64 PC) s.(sregs) = pc) =>
                 UserExecFacts.goodmb_execute_ECALL_U UserFrame.Du_r UserFrame.Du_w
                   s pc ltac:(vm_compute; reflexivity)
                   ltac:(vm_compute; reflexivity) Hp Hc)
              with "Hb").
    rewrite (uexec_ret_ecall _ _ eq_refl).
    assert (Hnum : usys_num (uvis_tf (uvis_of_run m pc M pm sz fdv)) = USYS_pipe).
    { cbn [uvis_tf uvis_of_run]. rewrite tf_of_num. exact Hn. }
    assert (Hw : usys_win USYS_pipe (uvis_tf (uvis_of_run m pc M pm sz fdv))
                 = Some (dst, 8%nat)).
    { cbn [uvis_tf uvis_of_run]. rewrite usyswin_tf_of.
      unfold usyswin.
      destruct (decide (USYS_pipe = USYS_wait)) as [Hc | _];
        [ exfalso; vm_compute in Hc; discriminate | ].
      destruct (decide (USYS_pipe = USYS_pipe)) as [_ | Hc];
        [ reflexivity | exfalso; exact (Hc eq_refl) ]. }
    (* the row reads a0 at the trapframe; the buffer is owned at the
       REGISTER's spelling.  They are the same word. *)
    assert (Ha0 : uvis_tf (uvis_of_run m pc M pm sz fdv) !!! tf_arg_idx 0 = dst)
      by (cbn [uvis_tf uvis_of_run]; reflexivity).
    rewrite Hnum. cbv zeta.
    destruct (decide (USYS_pipe = USYS_exit)) as [He | _];
      [ exfalso; vm_compute in He; discriminate | ].
    destruct (decide (USYS_pipe = USYS_fork)) as [He | _];
      [ exfalso; vm_compute in He; discriminate | ].
    iIntros (r M' pm' sz' fdv') "%Hok %Hfdok %Hpiperow".
    destruct (usys_mem_ok_window USYS_pipe _ r _ _ _ _ _ _ dst 8%nat Hw Hok)
      as ((d & bs & Hdcap & HM') & -> & ->).
    cbn [uvis_M uvis_perm uvis_sz uvis_fd uvis_of_run] in HM', Hfdok, Hpiperow |- *.
    (* ---- THE JOIN, AS ONE PURE FACT.  Both branches end at the same
           shape -- a written prefix, the caller's own bytes above it, and
           a statement about where the descriptors went -- so the tail
           below is written once. ---- *)
    assert (Hjoin : exists (dd : nat) (gg : nat -> bv 8),
              (dd <= 8)%nat /\
              M' = umem_wr M dst dd gg /\
              (forall j : nat, (dd <= j < 8)%nat -> gg j = f j) /\
              (uint r = 0 ->
                 exists a b : nat,
                   a <> b /\
                   (* THE SCANS, NOT MERELY THE FREENESS.  The summary used
                      to weaken both to "the slot was free", which is what
                      the mint needed then; the ledger needs the scan -- it
                      is what says WHICH descriptor came back -- and the row
                      states the write end's scan against the table the read
                      end's install left, so the summary carries it in that
                      same shape. *)
                   fd_least_closed fdv a /\
                   fd_least_closed (<[a := FdOpen true false FdPipe]> fdv) b /\
                   fdv' = <[b := FdOpen false true FdPipe]>
                            (<[a := FdOpen true false FdPipe]> fdv) /\
                   (forall i : nat, (i < 8)%nat ->
                      gg i = if (i <? 4)%nat
                             then nth_byte
                                    (trunc32 (mword_of_int (Z.of_nat a) : mword 64)) i
                             else nth_byte
                                    (trunc32 (mword_of_int (Z.of_nat b) : mword 64))
                                    (i - 4)%nat)) /\
              (uint r <> 0 -> fdv' = fdv)).
    { destruct (decide (uint r = 0)) as [Hr0 | Hr0].
      - (* SUCCESS: the joined row pins the image on the nose -- all eight
           bytes, from the naming function -- so it, not the window row, is
           what the tail runs on.  The window row's own [d]/[bs] are
           discarded here: two descriptions of one map, and this is the
           informative one. *)
        destruct (Hpiperow eq_refl Hr0)
          as (a & b & bs2 & Hne & Hca & Hcb & HM2 & Hbytes & Hfdv').
        exists 8%nat, bs2.
        split_and!;
          [ lia
          | rewrite HM2 Ha0; reflexivity
          | intros j Hj; exfalso; lia
          | intros _; exists a, b; split_and!;
              [ exact Hne | exact Hca | exact Hcb
              | exact Hfdv' | exact Hbytes ]
          | intros Hc; exfalso; exact (Hc Hr0) ].
      - (* FAILURE: nothing is claimed about the descriptors beyond "they
           did not move", which is the fd row's own else-branch, and the
           buffer comes back at the window join. *)
        exists d, (fun j => if decide (j < d)%nat then bs j else f j).
        split_and!.
        + exact Hdcap.
        + rewrite HM'. apply (umem_wr_ext M dst d bs).
          intros i Hi. case_decide as Hc; [ reflexivity | exfalso; lia ].
        + intros j Hj. case_decide as Hc; [ exfalso; lia | reflexivity ].
        + intros Hc; exfalso; exact (Hr0 Hc).
        + intros _. unfold usys_fd_ok in Hfdok.
          destruct (decide (USYS_pipe = USYS_close)) as [Hc | _];
            [ discriminate Hc | ].
          destruct (decide (USYS_pipe = USYS_dup)) as [Hc | _];
            [ discriminate Hc | ].
          destruct (decide (USYS_pipe = USYS_open)) as [Hc | _];
            [ discriminate Hc | ].
          destruct (decide (USYS_pipe = USYS_pipe)) as [_ | Hc];
            [ | exfalso; exact (Hc eq_refl) ].
          destruct (decide (uint r = 0)) as [Hc | _];
            [ exfalso; exact (Hr0 Hc) | exact Hfdok ]. }
    destruct Hjoin as (dd & gg & Hdd8 & HMj & Hgf & Hsucc & Hfail).
    rewrite (umem_wr_write M dst dd gg
               ltac:(intros i Hi; apply Hlin; lia)) in HMj.
    (* the window row's own description of [M'] is the weaker of the two and
       has served its purpose (it is where [d] came from); dropping it is
       what lets [subst] pick the joined one. *)
    clear HM'. subst M'.
    rewrite (uslot_bump_run m pc M (umem_write M (uint dst) dd gg) pm pm sz sz
               fdv fdv' r Hx0 Hal4).
    rewrite /ukc. iIntros (h' xi' C' pt' Rfd' Rut') "%Hlo' %Hpm' Hb'".
    iEval (rewrite (ubytes_split γd (uint dst) dd 8 f Hdd8)) in "Hbuf".
    iDestruct "Hbuf" as "[Hblo Hbhi]".
    iMod (uheap_store_run γt γd γs M pm (uint dst) dd f gg with "Hheap Hblo")
      as "[Hheap Hblo]".
    (* hoisted out of argument position: the tail bound [j < 8 - dd] is what
       [Hgf] needs and an [ltac:] there would be run before it is in scope
       (claude-notes/optimization.md, "Inline [ltac:]"). *)
    assert (Htail : forall j : nat, (j < 8 - dd)%nat ->
              f (dd + j)%nat = gg (dd + j)%nat)
      by (intros j Hj; symmetry; apply Hgf; lia).
    iDestruct (ubytes_ext γd (uint dst + Z.of_nat dd) (8 - dd)
                 (fun j => f (dd + j)%nat) (fun j => gg (dd + j)%nat)
                 Htail with "Hbhi")
      as "Hbhi".
    iAssert (ubytes γd (uint dst) 8 gg) with "[Hblo Hbhi]" as "Hbuf".
    { rewrite (ubytes_split γd (uint dst) dd 8 gg Hdd8). iFrame "Hblo Hbhi". }
    (* ---- THE AUTHORITY MOVES TO [fdv'], and on success it pays out the
           two handles.  [b]'s end is installed first so that [a] is still
           free when its own insert runs -- the two are distinct, which is
           what the row promises. ---- *)
    iAssert (|==> ufd_auth γfd fdv' ∗
              ((∃ a b : nat,
                  ⌜ uint r = 0 /\ a <> b /\ (a < NOFILE)%nat /\ (b < NOFILE)%nat
                    /\ (forall i : nat, (i < 8)%nat ->
                          gg i = if (i <? 4)%nat
                                 then nth_byte
                                        (trunc32 (mword_of_int (Z.of_nat a) : mword 64)) i
                                 else nth_byte
                                        (trunc32 (mword_of_int (Z.of_nat b) : mword 64))
                                        (i - 4)%nat) ⌝ ∗
                  ualloc_at γfd l a (FdOpen true false FdPipe) ∗
                  ualloc_at γfd (ustd_after l (FdOpen true false FdPipe)) b
                    (FdOpen false true FdPipe) ∗
                  ustd γfd (ustd_after
                              (ustd_after l (FdOpen true false FdPipe))
                              (FdOpen false true FdPipe)))
               ∨ (⌜ uint r <> 0 ⌝ ∗ ustd γfd l)))%I
      with "[Hufd Hstd]" as ">[Hufd Hhs]".
    { destruct (decide (uint r = 0)) as [Hr0 | Hr0].
      - destruct (Hsucc Hr0) as (a & b & Hne & Hca & Hcb & Hfdv' & Hbytes).
        (* allocated in the ROW's own order: read end first, write end
           against the table -- and the ledger -- that left *)
        iMod (ufd_alloc_least γfd fdv l a (FdOpen true false FdPipe) Hca
                ltac:(discriminate) with "Hufd Hstd") as "[Hufd [Hstd Hha]]".
        iMod (ufd_alloc_least γfd (<[a := FdOpen true false FdPipe]> fdv)
                (ustd_after l (FdOpen true false FdPipe)) b
                (FdOpen false true FdPipe) Hcb ltac:(discriminate)
                with "Hufd Hstd") as "[Hufd [Hstd Hhb]]".
        rewrite <- Hfdv'. iModIntro. iFrame "Hufd".
        iLeft. iExists a, b. iFrame "Hha Hhb Hstd". iPureIntro.
        split_and!;
          [ exact Hr0 | exact Hne
          | rewrite <- Hfdlen; exact (fd_least_closed_lt _ _ Hca)
          | rewrite <- Hfdlen; rewrite <- (length_insert fdv a
              (FdOpen true false FdPipe)); exact (fd_least_closed_lt _ _ Hcb)
          | exact Hbytes ].
      - rewrite (Hfail Hr0). iModIntro. iFrame "Hufd".
        iRight. iFrame "Hstd". iPureIntro. exact Hr0. }
    iDestruct (urun_close_upd γt γd γs γfd (umem_write M (uint dst) dd gg) pm m
                 (mword_of_int 10) r sz fdv' (add_vec_int pc 4) avail
                 ltac:(unfold unot_sp; vm_compute; discriminate)
                 with "Hheap Hstk Hufd [Hcont Hbuf Hhs]") as "Hkc";
      [ iIntros (h'') "Hrun";
        iApply ("Hcont" $! h'' r gg with "Hhs Hrun Hbuf") | ].
    iApply ("Hkc" $! h' xi' C' pt' Rfd' Rut' with "[%] [%] Hb'");
      [ exact Hlo' | exact Hpm' ].
  Qed.

  (* ------------------------------------------------------------------- *)
  (* THE READ ROW'S INSTANCE OF THE WINDOW LEAF -- sh's [getcmd] shape.     *)
  (* Nothing but [usyswin]'s read branch, taken once here so a program      *)
  (* does not have to unfold it: the buffer is a1, the count is a2 as an    *)
  (* [int], and the caller owns AT LEAST the count.  NOT the same lemma as  *)
  (* [wp_uk_ecall_read] above (cat's): that one asks for the exact          *)
  (* non-negative count and returns the buffer at unconstrained contents;   *)
  (* this one allows any owned run covering the cap and returns the         *)
  (* written prefix's length [d] with the tail pinned unchanged.  The two   *)
  (* should eventually merge (this one generalizes, modulo the address      *)
  (* spelling) -- relay note in the worklist.                               *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_uk_ecall_read_win (γt γd γs γfd : gname) (h : CpuId) (m : regfile)
      (pc : mword 64) (cnt : Z) (k : nat) (f : nat -> bv 8) (avail : nat) :
    usysno m = USYS_read ->
    bv_signed (subrange_vec_dec (m !!! Regidx (mword_of_int 12)) 31 0 : mword 32)
      = cnt ->
    (Z.to_nat cnt <= k)%nat ->
    is_aligned_vaddr (Virtaddr (add_vec_int pc 4)) 2 = true ->
    uinstr_is γt pc false (ECALL tt) -∗
    urun γt γd γs γfd h m pc avail -∗
    ubytes γd (uint (m !!! Regidx (mword_of_int 11))) k f -∗
    (∀ (h' : CpuId) (r : mword 64) (d : nat) (g : nat -> bv 8),
       ⌜ (d <= Z.to_nat cnt)%nat ⌝ -∗
       ⌜ forall j : nat, (d <= j < k)%nat -> g j = f j ⌝ -∗
       urun γt γd γs γfd h' (<[Regidx (mword_of_int 10) := r]> m)
         (add_vec_int pc 4) avail -∗
       ubytes γd (uint (m !!! Regidx (mword_of_int 11))) k g -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hn Hcnt Hk Hal4. iIntros "#Hi Hrun Hbuf Hcont".
    assert (Hw : usyswin m USYS_read
                 = Some (m !!! Regidx (mword_of_int 11), Z.to_nat cnt)).
    { unfold usyswin.
      destruct (decide (USYS_read = USYS_wait)) as [Hc | _]; [ discriminate Hc | ].
      destruct (decide (USYS_read = USYS_pipe)) as [Hc | _]; [ discriminate Hc | ].
      destruct (decide (USYS_read = USYS_read)) as [_ | Hc];
        [ | exfalso; exact (Hc eq_refl) ].
      rewrite Hcnt. reflexivity. }
    iApply (wp_uk_ecall_window γt γd γs γfd h m pc USYS_read
              (m !!! Regidx (mword_of_int 11)) (Z.to_nat cnt) k f avail
              Hn Hw Hk
              (* read is none of the four -- by computation on the number *)
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              Hal4 with "Hi Hrun Hbuf").
    iIntros (h' r d g) "%Hd %Hgf Hrun Hbuf".
    iApply ("Hcont" $! h' r d g with "[%] [%] Hrun Hbuf");
      [ exact Hd | exact Hgf ].
  Qed.

  Lemma wp_uk_ecall_exit (γt γd γs γfd : gname) (h : CpuId) (m : regfile)
      (pc : mword 64) (avail : nat) :
    usysno m = USYS_exit ->
    uinstr_is γt pc false (ECALL tt) -∗
    urun γt γd γs γfd h m pc avail -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hn. iIntros "#Hi Hrun".
    iDestruct "Hrun" as (xi C pt Rfd Rut sz M pm fdv) "(%Hlo & %Hpm & Hheap & Hstk & Hufd & Hb)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iApply (UkStep.wp_uk_ecall C pt Rfd Rut pm sz Hlo Hpm M m pc fdv Hui
              (fun (s : mstate)
                   (Hp : register_lookup cur_privilege s.(sregs) = User)
                   (Hc : register_lookup (R_bitvector_64 PC) s.(sregs) = pc) =>
                 UserExecFacts.goodmb_execute_ECALL_U UserFrame.Du_r UserFrame.Du_w
                   s pc ltac:(vm_compute; reflexivity)
                   ltac:(vm_compute; reflexivity) Hp Hc)
              with "Hb").
    rewrite (uexec_ret_ecall _ _ eq_refl).
    assert (Hnum : usys_num (uvis_tf (uvis_of_run m pc M pm sz fdv)) = USYS_exit).
    { cbn [uvis_tf uvis_of_run]. rewrite tf_of_num. exact Hn. }
    rewrite Hnum. cbv zeta.
    destruct (decide (USYS_exit = USYS_exit)) as [_ | Hne];
      [ done | exfalso; exact (Hne eq_refl) ].
  Qed.

End UkRunSys.
