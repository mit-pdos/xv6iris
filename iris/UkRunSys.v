(* THE ECALL LEAVES' DEPOSIT PREMISE IS A WAND, NOT A BARE HYPOTHESIS.
   Since the ARM every returning leaf owes the trap contract the process's
   bundle for the number it is at ([UexecRet.uexec_dep_F]), and the key that
   bundle is at is [uvis_of_run m pc M pm sz fdv cw gn cs] -- whose [M], [pm],
   [sz], [fdv] and [cw] are bound by [UkRun.urun]'s own existential, so a
   leaf has them only AFTER it destructs and can never name them in its own
   statement.  Hence [UkRun.udepw]: a wand off the two authorities the leaf
   already holds, yielding either [psok n] (mint from the program's supplier)
   or the explicit deposit.  Same wall as the key-free minting law, one
   level out. *)

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
Require Import PipeNames.    (* [pipe_names] -- what a pipe descriptor's state carries *)
Require Import ProcGeom.   (* [tf_arg_idx] -- wait's row is based at a0 *)
Require Import UkStep.
Require Import UmodeArith.  (* [moi_add_l] / [uint_moi]: read's row addresses
                               through [add_vec_int], the heap through [Z] *)
Require Import UserHeap.
Require Import UserPerm.    (* [uperm] -- the row's permission-map argument *)
Require Import UserPtTree.  (* [umem_wr] / [umem_write] -- the window's image *)
Require Import UserBits.    (* [uint_add_vec_int_small] -- the window's no-wrap *)
Require Import RiscvExtras. (* [uint_unsigned] *)
Require Import RiscvModelBytes. (* [nth_byte] -- pipe's two reported words *)
Require Import CtxIdDefs.
Require Import ChildTok.  (* [genF] -- the capacity the slot's fork arms name *)
Require Import UserChildren. (* [uch] / [uch_update] -- the program's half of
                                its children reading, which wait moves, and
                                [ch_reaped], the row the wait leaf reports *)
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
Local Open Scope Z_scope.
Require Import UkRun.

(* THE SYSCALL NUMBER, off the register file rather than off the trapframe:
   a program knows what it put in a7, and should not have to know that the
   key spells it [usys_num (tf_of m pc)]. *)
Definition usysno (m : regfile) : Z :=
  bv_signed (subrange_vec_dec (m !!! Regidx (mword_of_int 17)) 31 0 : mword 32).

(* ...AND THE EXIT STATUS THE PROGRAM IS PASSING, off the same register file:
   a0 read as a signed 32-bit word.  It is [ProcGeom.exit_xs] of the frame
   the trap will save ([UexecRet.tf_of_arg0]), which is what exit's deposit
   row is stated at -- so the payload the program pays here and the payload
   the parent is handed are at one status. *)
Definition uexitst (m : regfile) : Z :=
  bv_signed (subrange_vec_dec (m !!! Regidx (mword_of_int 10)) 31 0 : mword 32).

Lemma uexitst_exit_xs (m : regfile) (pc : mword 64) :
  exit_xs (tf_of m pc) = uexitst m.
Proof. reflexivity. Qed.

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
   own case analysis takes first), and not exec or sbrk.  ...AND NOT CHDIR,
   which is what lets the window leaf re-key the cwd authority [urun]
   carries without taking a premise for it: a window call names a buffer,
   and chdir has none. *)
Lemma usys_win_num (n : Z) (tf : list (mword 64)) (dst : mword 64) (cap : nat) :
  usys_win n tf = Some (dst, cap) ->
  n <> USYS_exit /\ n <> USYS_fork /\ n <> USYS_exec /\ n <> USYS_sbrk
  /\ n <> USYS_chdir.
Proof.
  unfold usys_win.
  destruct (decide (n = USYS_wait)) as [-> | _];
    [ intros _; unfold USYS_wait, USYS_exit, USYS_fork, USYS_exec, USYS_sbrk,
                       USYS_chdir;
      split_and!; discriminate | ].
  destruct (decide (n = USYS_pipe)) as [-> | _];
    [ intros _; unfold USYS_pipe, USYS_exit, USYS_fork, USYS_exec, USYS_sbrk,
                       USYS_chdir;
      split_and!; discriminate | ].
  destruct (decide (n = USYS_read)) as [-> | _];
    [ intros _; unfold USYS_read, USYS_exit, USYS_fork, USYS_exec, USYS_sbrk,
                       USYS_chdir;
      split_and!; discriminate | ].
  destruct (decide (n = USYS_fstat)) as [-> | _];
    [ intros _; unfold USYS_fstat, USYS_exit, USYS_fork, USYS_exec, USYS_sbrk,
                       USYS_chdir;
      split_and!; discriminate | ].
  intros Hc; discriminate Hc.
Qed.

(* THE WINDOW ROW, READ OFF THE TABLE.  What a program calling one of the
   four learns: the kernel wrote SOME run, no longer than the cap its own
   arguments named, at the address its own arguments named -- and nothing
   else moved.  Note what is NOT here: the row says nothing tying the
   written length to the RETURN VALUE, so a read's caller learns
   [d <= count] and not [d = r].  That link lives on the kernel side
   ([SpecSysRead]) and would have to be carried into this table before a
   leaf could state it. *)
Lemma usys_mem_ok_window (n : Z) (tf : list (mword 64)) (r : mword 64)
    (M M' : gmap Z (bv 8)) (π π' : gmap (mword 27) uperm) (szv szv' : Z)
    (lz lz' : bool)
    (dst : mword 64) (cap : nat) :
  usys_win n tf = Some (dst, cap) ->
  usys_mem_ok n tf r M π szv lz M' π' szv' lz' ->
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
    intros ((d & bs & Hd & _ & Hm) & Hp & Hs & _).
    split; [ exists d, bs; split; [ lia | exact Hm ] | exact (conj Hp Hs) ]. }
  destruct (decide (n = USYS_pipe)) as [-> | Hp0].
  { intros [= <- <-].
    destruct (decide (USYS_pipe = USYS_exec)) as [Hc | _]; [ discriminate Hc | ].
    destruct (decide (USYS_pipe = USYS_sbrk)) as [Hc | _]; [ discriminate Hc | ].
    destruct (decide (USYS_pipe = USYS_wait)) as [Hc | _]; [ discriminate Hc | ].
    destruct (decide (USYS_pipe = USYS_pipe)) as [_ | Hc];
      [ | exfalso; exact (Hc eq_refl) ].
    intros ((d & bs & Hd & Hm) & Hp & Hs & _).
    split; [ exists d, bs; split; [ lia | exact Hm ] | exact (conj Hp Hs) ]. }
  destruct (decide (n = USYS_read)) as [-> | Hr0].
  { intros [= <- <-].
    destruct (decide (USYS_read = USYS_exec)) as [Hc | _]; [ discriminate Hc | ].
    destruct (decide (USYS_read = USYS_sbrk)) as [Hc | _]; [ discriminate Hc | ].
    destruct (decide (USYS_read = USYS_wait)) as [Hc | _]; [ discriminate Hc | ].
    destruct (decide (USYS_read = USYS_pipe)) as [Hc | _]; [ discriminate Hc | ].
    destruct (decide (USYS_read = USYS_read)) as [_ | Hc];
      [ | exfalso; exact (Hc eq_refl) ].
    intros ((d & bs & Hd & Hm) & Hp & Hs & _).
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
    intros ((d & bs & Hd & Hm) & Hp & Hs & _).
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
Require Import UserCwd.  (* [ucwd] -- the program's own half of its working
                            directory, which the exec leaf reads *)
Require Import UexecSG.   (* [uexecSG] / [uprogSG]: the ARM deposit class *)

Section UkRunSys.
  Context `{!riscvGS Σ}.
  Context `{!ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  (* ...and the children set's ([Xv6Cameras.uchG]), which [UkRun.urun]
     carries beside the cwd's *)
  Context `{!ghost_varG Σ (gset gname)}.
  (* [ChildTok.ctokG] BEFORE [uexecSG]: the class is indexed by it
     ([UexecSG]'s own note), and a [Context] that meets the index first
     generalizes a SECOND one -- two instances that print alike and do not
     match. *)
  Context `{!ctokG Σ}.
  Context {SG : uexecSG Σ}.
  Context `{PS : uprogSG Σ}.

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
      (pmv : gmap (mword 27) uperm) (sz : Z) (dq : dfrac) (a : Z) (nb : nat)
      (f : nat -> bv 8) :
    uheap γt γd γs M pmv sz -∗ ubytesq γd dq a nb f -∗
    ⌜ forall j : nat, (j < nb)%nat ->
        M !! (a + Z.of_nat j)%Z = Some (f j) /\ 0 <= a + Z.of_nat j < 2 ^ 38 ⌝.
  Proof using .
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

  (* ...AND THE SAME RUN'S PAGES ARE WRITABLE (lane LAZY-FLAG, K5).
     [uheap]'s own canonicity clause puts every DATA byte's address in
     [UserHeap.uw_addr] of the key's permission map; this is that clause
     read along a run, which is the form the no-fault lemma below wants. *)
  Lemma uheap_ubytes_w (γt γd γs : gname) (M : gmap Z (bv 8))
      (pmv : gmap (mword 27) uperm) (sz : Z) (dq : dfrac) (a : Z) (nb : nat)
      (f : nat -> bv 8) :
    uheap γt γd γs M pmv sz -∗ ubytesq γd dq a nb f -∗
    ⌜ forall j : nat, (j < nb)%nat -> uw_addr pmv (a + Z.of_nat j)%Z ⌝.
  Proof using .
    iInduction nb as [| kb IH] "IH"; iIntros "Hheap Hbs".
    { iPureIntro. intros j Hj. exfalso. lia. }
    iEval (rewrite /ubytesq seq_S big_sepL_app /=) in "Hbs".
    iDestruct "Hbs" as "[Hlo [Hhi _]]".
    iDestruct ("IH" with "Hheap Hlo") as %Hk.
    iDestruct (uheap_ubyte with "Hheap Hhi") as %(_ & Hw & _).
    iPureIntro. intros j Hj.
    destruct (decide (j = kb)) as [-> | Hne]; [ exact Hw | ].
    apply Hk. lia.
  Qed.

  (* ...AND THE SAME RUN IN THE TEXT HALF (lane TXT-ROW).  A .rodata source
     run is filed under [ukn_t] and its pages are X-and-NOT-W, so
     [uheap_ubytes_w] says nothing about it.  [UserHeap.uheap_text] does:
     an image byte's page is FETCHABLE and its address canonical.  This is
     that clause read along a run -- the two facts the buffer-carrying leaf
     gets from [uheap_ubytes_run] and [uheap_ubytes_w] together, in one
     pass, because the text invariant states both at the same byte. *)
  Lemma uheap_text_bytes (γt γd γs : gname) (M : gmap Z (bv 8))
      (pmv : gmap (mword 27) uperm) (sz : Z) (a : Z) (nb : nat)
      (f : nat -> bv 8) :
    uheap γt γd γs M pmv sz -∗
    ([∗ list] j ∈ seq 0 nb, utext γt (a + Z.of_nat j)%Z (f j)) -∗
    ⌜ forall j : nat, (j < nb)%nat ->
        M !! (a + Z.of_nat j)%Z = Some (f j)
        /\ ux_addr pmv (a + Z.of_nat j)%Z /\ 0 <= a + Z.of_nat j < 2 ^ 38 ⌝.
  Proof using .
    iInduction nb as [| kb IH] "IH"; iIntros "Hheap Hbs".
    { iPureIntro. intros j Hj. exfalso. lia. }
    iEval (rewrite seq_S big_sepL_app /=) in "Hbs".
    iDestruct "Hbs" as "[Hlo [Hhi _]]".
    iDestruct ("IH" with "Hheap Hlo") as %Hk.
    iDestruct (uheap_text with "Hheap Hhi") as %(HM & Hx & Hc).
    iPureIntro. intros j Hj.
    destruct (decide (j = kb)) as [-> | Hne];
      [ exact (conj HM (conj Hx Hc)) | ].
    apply Hk. lia.
  Qed.

  (* ===================================================================== *)
  (* THE NO-FAULT LEMMA (app-echo.md, lane LAZY-FLAG, K5/L6).               *)
  (*                                                                       *)
  (* WHAT IT IS FOR.  consoleread's window arm can SWALLOW a byte           *)
  (* ([ConsoleInv.cons_swallow], lane CONS-SWALLOW), and one of the two     *)
  (* reasons it offers is "copyout faulted at the destination", i.e.        *)
  (* [~ UserPtTree.uva_wmapped P (dst + d)].  A verified program can refute *)
  (* that from what it already owns, and this is the step: [ubytes] puts    *)
  (* the address in [UserHeap.uw_addr] of the key's permission map          *)
  (* ([uheap_ubytes_w] above), and the LAZY FLAG at [false] turns a         *)
  (* writable page of the PROJECTION into a real user leaf with V, U and W  *)
  (* ([UserHeap.lazy_free_uw_addr]) -- which is exactly [uva_wmapped].      *)
  (* Without the flag the projection cannot tell a page vmfault has yet to  *)
  (* serve from a mapped RW page, and the refutation is impossible.         *)
  (*                                                                       *)
  (* THE TABLE COMES FROM ROW 5 ([UexecExecInst]'s read row), which         *)
  (* exhibits a [P] agreeing with the key's projection, well-formed, and    *)
  (* carrying the flag's claim.  The three premises below are that row's    *)
  (* three conjuncts, so SH-LINE 2b applies this INSIDE                     *)
  (* [wp_uk_ecall_read_recv]'s post with the [∃ P] in hand.                 *)
  (*                                                                       *)
  (* STATED POSITIVELY ("the byte IS mapped") rather than as a refutation:  *)
  (* the consumer eliminates the receipt's disjunct by contradiction, and   *)
  (* a positive conclusion is the one that also serves a caller who wants   *)
  (* the fact for its own sake.                                            *)
  (* ===================================================================== *)
  Lemma uk_read_nofault (γt γd γs : gname) (M : gmap Z (bv 8))
      (pmv : gmap (mword 27) uperm) (sz : Z) (dq : dfrac)
      (dst : mword 64) (k d : nat) (f : nat -> bv 8) (P : uptd) :
    (d < k)%nat ->
    ProcPtOwn.proc_pt_wf P ->
    perm_of (ud_um P) sz = pmv ->
    lazy_free (ud_um P) sz ->
    uheap γt γd γs M pmv sz -∗ ubytesq γd dq (uint dst) k f -∗
    ⌜ UserPtTree.uva_wmapped P (uint (add_vec_int dst (Z.of_nat d))) ⌝.
  Proof using .
    intros Hdk Hwf Hpm Hlf. iIntros "Hheap Hbs".
    iDestruct (uheap_ubytes_run γt γd γs M pmv sz dq (uint dst) k f
                 with "Hheap Hbs") as %Hbnd.
    iDestruct (uheap_ubytes_w γt γd γs M pmv sz dq (uint dst) k f
                 with "Hheap Hbs") as %Hw.
    iPureIntro.
    destruct (Hbnd d Hdk) as [_ Hrange].
    (* the run the process owns is keyed at [a + d] in [Z] and the kernel's
       row at [uint (add_vec_int dst d)]; the two agree because every
       mapped user address is below MAXVA ([uheap]'s canonicity clause) *)
    assert (Hlin : uint (add_vec_int dst (Z.of_nat d)) = (uint dst + Z.of_nat d)%Z).
    { change (2 ^ 38) with 274877906944 in Hrange.
      rewrite !uint_unsigned in Hrange |- *.
      apply uint_add_vec_int_small; lia. }
    rewrite Hlin.
    apply (UserHeap.lazy_free_uw_addr P sz (uint dst + Z.of_nat d)%Z Hwf Hlf);
      [ exact Hrange | rewrite Hpm; exact (Hw d Hdk) ].
  Qed.

  (* [ubytes_app] at a PREFIX LENGTH rather than at a sum.  A caller holding
     a buffer of length [nb] and told the kernel wrote [kb <= nb] of it wants
     the split stated that way round. *)
  Lemma ubytes_split (γd : gname) (a : Z) (kb nb : nat) (f : nat -> bv 8) :
    (kb <= nb)%nat ->
    ubytes γd a nb f ⊣⊢
    ubytes γd a kb f ∗
    ubytes γd (a + Z.of_nat kb) (nb - kb) (fun j => f (kb + j)%nat).
  Proof using .
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
  Proof using .
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
  (* content of “a program that closed a descriptor must stop claiming it  *)
  (* is open”, and it is why close has no untracked leaf.                  *)
  (* ------------------------------------------------------------------- *)
  Lemma ufd_auth_move (γfd : gname) (n : Z) (tf : list (mword 64))
      (r : mword 64) (fdv fdv' l : list fdstate) :
    n <> USYS_close ->
    usys_fd_ok n tf r fdv fdv' ->
    ufd_auth γfd fdv -∗ ustd γfd l ==∗
    ufd_auth γfd fdv' ∗ ∃ l' : list fdstate, ustd γfd l'.
  Proof using .
    intros Hnc Hrow. iIntros "Hufd Hstd". unfold usys_fd_ok in Hrow.
    destruct (decide (n = USYS_close)) as [Hc | _]; [ contradiction (Hnc Hc) | ].
    destruct (decide (n = USYS_dup)) as [_ | _].
    { destruct Hrow as [(fd1 & _ & Hcl & _ & ->) | (_ & -> & _)];
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
    { destruct Hrow as [(fd & rd & wr & t & _ & Hcl & -> & _) | [_ ->]];
        [| iModIntro; iFrame "Hufd"; by iExists l ].
      iMod (ufd_alloc_least_any γfd fdv l fd (FdOpen rd wr t) Hcl
              ltac:(discriminate) with "Hufd Hstd") as "[$ $]".
      by iModIntro. }
    destruct (decide (n = USYS_pipe)) as [_ | _].
    { destruct (decide (uint r = 0)) as [_ | _];
        [| unfold UsysMemOk.usys_pipe_fail in Hrow;
           destruct Hrow as [_ ->]; iModIntro; iFrame "Hufd"; by iExists l ].
      destruct Hrow as (a & b & γp & Hne & Hca & Hcb & ->).
      (* THE TWO ALLOCATIONS RUN IN THE ROW'S OWN ORDER: read end first,
         write end against the table the first left.  That is the order
         sys_pipe allocates in, and stating it that way is what lets the
         second scan's least-closed fact be read at the table it is actually
         about -- no commuting needed here at all.  Both ends carry the SAME
         [γp] (design/pipe.md, "The byte queue"): that is how the table says
         they are the two ends of one pipe. *)
      iMod (ufd_alloc_least_any γfd fdv l a (FdOpen true false (FdPipe γp)) Hca
              ltac:(discriminate) with "Hufd Hstd") as "[Hufd Hstd]".
      iDestruct "Hstd" as (l1) "Hstd".
      iMod (ufd_alloc_least_any γfd (<[a := FdOpen true false (FdPipe γp)]> fdv) l1 b
              (FdOpen false true (FdPipe γp)) Hcb ltac:(discriminate)
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
  Proof using .
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
  Lemma wp_uk_ecall_quiet (N : uk_names Σ) (h : CpuId) (m : regfile)
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
    (* ...AND IT DOES NOT MOVE THE WORKING DIRECTORY.  [urun] carries the
       program's authority over that too, and this leaf re-closes the run at
       the cwd it opened at, so chdir -- the one row that moves it
       ([UsysMemOk.usys_cwd_ok]) -- is excluded here.  It is quiet in memory
       and in the descriptor table, so nothing else was ruling it out. *)
    n <> USYS_chdir ->
    (* ...AND IT IS A NUMBER THE FULL MASK PASSES, AND NOT SECCOMP'S
       (upstream a083670).  [urun] is keyed at the full mask, so a number
       in [0, 64) is its own effective number ([UexecSlot.uvis_num_full0]),
       and seccomp is the one row that would move the mask the run is
       re-closed at. *)
    (0 <= n < 64)%Z -> n <> USYS_seccomp ->
    is_aligned_vaddr (Virtaddr (add_vec_int pc 4)) 2 = true ->
    uinstr_is (ukn_t N) pc false (ECALL tt) -∗
    urun N h m pc avail -∗
    udepw N m pc n -∗
    (∀ (h' : CpuId) (r : mword 64),
       urun N h' (<[Regidx (mword_of_int 10) := r]> m) (add_vec_int pc 4) avail -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Hn Hexit Hfork Hexec Hsbrk H3 H4 H5 H8 Hcl Hdp Hop Hcd Hrng Hn23 Hal4.
    iIntros "#Hi Hrun Hsb Hcont".
    iDestruct "Hrun" as (xi C pt Rfd Rut sz M pm fdv cw gn cs pidv) "(%Hlo & %Hpm & %Hlzf & %HRut & Hheap & Hstk & Hufd & Hcwda & Hcha & #Hmy & #Hdep & #Hnpx & Hb)".
    iMod (udepw_mint N m pc _ M pm _ fdv cw gn cs pidv
                with "Hdep Hmy Hsb Hheap Hufd") as "(Hheap & Hufd & Hdepn)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iDestruct (uvb_x0 with "Hb") as "[%Hx0 Hb]".
    iApply (UkStep.wp_uk_ecall C pt Rfd Rut pm sz Hlo Hpm HRut Hlzf M m pc fdv cw gn cs pidv Hui
              (fun (s : mstate)
                   (Hp : register_lookup cur_privilege s.(sregs) = User)
                   (Hc : register_lookup (R_bitvector_64 PC) s.(sregs) = pc) =>
                 UserExecFacts.goodmb_execute_ECALL_U UserFrame.Du_r UserFrame.Du_w
                   s pc ltac:(vm_compute; reflexivity)
                   ltac:(vm_compute; reflexivity) Hp Hc)
              with "Hb Hmy").
    rewrite (uexec_ret_ecall _ _ eq_refl).
    assert (Hnum : uvis_num (uvis_of_run m pc M pm sz fdv cw gn cs pidv false secc_all) = n).
    { assert (Hraw : usys_num (uvis_tf (uvis_of_run m pc M pm sz fdv cw gn cs pidv false secc_all)) = n)
        by (cbn [uvis_tf uvis_of_run]; rewrite tf_of_num; exact Hn).
      rewrite uvis_num_full0; [ exact Hraw | reflexivity | rewrite Hraw; usys_range ]. }
    (* the PAYMENT's guard IS the deposit's own, so it is opened BEFORE the
       number is rewritten and the destructs below then reduce both copies
       at once *)
    rewrite /uexec_pay_dep /upay_at.
    pose proof Hnum as Hnume. unfold uvis_num in Hnume. rewrite ?Hnum ?Hnume. cbv zeta.
    destruct (decide (uecall_scause = uecall_scause)) as [_ | Hpne];
      [ | exfalso; exact (Hpne eq_refl) ].
    destruct (decide (n = USYS_exit)) as [He | _]; [ exfalso; exact (Hexit He) | ].
    destruct (decide (n = USYS_fork)) as [He | _]; [ exfalso; exact (Hfork He) | ].
    (* ...and wait, which has an arm of its own now ([UexecRet.uexec_wait_F]):
       this leaf is for the numbers that move NOTHING, and wait moves the
       caller's children reading. *)
    destruct (decide (n = USYS_wait)) as [He | _]; [ exfalso; exact (H3 He) | ].
    (* THE ROW COMES IN BESIDE THE IMAGE'S NOW.  A quiet syscall's fd row is
       [fdv' = fdv] ([UsysMemOk.usys_fd_ok_quiet]), so this leaf could pin
       the descriptor view -- it does not yet, because [urun] hides the view
       and has nowhere to say it.  Named and discarded here; the leaves that
       will read it are open/close/dup, once [urun] carries the program's
       own descriptor authority. *)
    (* the arm binds the deposit's FAMILIES ([UexecSG.v]'s header); the
       law mints at some [f] and this leaf, which discards its post,
       hands that witness straight over. *)
    (* THE MINT ALREADY NAMED THE PAYLOAD (app-echo.md, "SH-LINE RULING",
       R1): read's bundle is a wand from the depositing process's own exit
       payload, so nothing is re-keyed here any more -- the family the
       deposit came at IS at [ukn_pay N]. *)
    iDestruct "Hdepn" as (fdep) "[%Hfp Hdepn]".
    iExists fdep. rewrite Hfp.
    cbn [uvis_gen uvis_of_run].
    iSplitR; [ iFrame "Hmy" | ].
    iSplitL "Hdepn"; [ iExact "Hdepn" | ].
    iIntros (r M' pm' sz' fdv' cw' gn' cs' lz' secc') "%Hok %Hfdok %Hpiperow %Hcwrow %Hgnrow %Hpidrow %Hliverow %Hscrow %Hchrow _".
    (* THE LAZY BIT CROSSED THE TRAP UNCHANGED (lane LAZY-FLAG, L6).  The
       trapping key is at [false] -- the U tier's run is
       ([UexecRet.ukcq]) -- and every row but sbrk's is the equation
       ([UsysMemOk.usys_mem_ok_lazy]), so the resume key is at [false] too
       and the close below is at the run's own bit. *)
    assert (Hlzq : lz' = false)
      by (refine (usys_mem_ok_lazy _ _ _ _ _ _ _ _ _ _ _ _ Hok);
          first [ assumption | vm_compute; discriminate ]).
    subst lz'.
    (* ...AND SO DID THE MASK: not seccomp's number, so the row is the
       equation ([UsysMemOk.usys_secc_ok_quiet]), and the resume key is at
       the full mask [urun] is keyed at *)
    pose proof (fun Hne => usys_secc_ok_quiet _ _ _ _ _ Hne Hscrow) as Hscq.
    specialize (Hscq ltac:(usys_range)).
    cbn [uvis_secc uvis_of_run] in Hscq. subst secc'.
    (* THE CWD CROSSED THE TRAP UNCHANGED -- chdir is the one row that moves
       it, and this is not it -- so the engine's half is re-keyed onto the
       view the process resumes at and the program's half never moved. *)
    assert (Hcw : cw' = cw)
      by (exact (usys_cwd_ok_quiet n r cw cw' Hcd Hcwrow)).
    iDestruct (ucwd_auth_quiet N cw cw' Hcw with "Hcwda") as "Hcwda".
    (* ...AND SO DID THE GENERATION AND THE CHILDREN SET: no entry
       re-incarnates its caller, and this lane's children row is the
       identity at every number ([UsysMemOk] SS2e/SS2f).  Both are
       substituted rather than re-keyed -- the generation has no
       authority beside it, and the children authority is already at
       the set the process resumes at. *)
    assert (Hgn : gn' = gn) by exact (usys_gen_ok_quiet _ _ _ Hgnrow).
    assert (Hch : cs' = cs) by exact (usys_ch_ok_quiet _ _ _ _ Hchrow).
    subst gn' cs'.
    destruct (usys_mem_ok_quiet n _ r _ _ _ _ _ _ _ _ Hexec Hsbrk H3 H4 H5 H8 Hok)
      as [-> [-> ->]].
    (* ...AND THE TABLE DID NOT MOVE.  This is the row being READ rather
       than dropped: with the four descriptor-moving numbers excluded the
       row IS [fdv' = fdv], so the authority [urun] was carrying is already
       at the view the process resumes at. *)
    pose proof (usys_fd_ok_quiet n _ r _ _ Hcl Hdp Hop H4 Hfdok) as ->.
    cbn [uvis_M uvis_perm uvis_of_run].
    (* the resumed key is at the SAME view, so the bump is at [fdv] twice *)
    rewrite (uslot_bump_run m pc M M pm pm sz sz fdv fdv cw cw' gn gn cs cs pidv false false secc_all secc_all r Hx0 Hal4).
    (* the arm handed the payload back, so the close spends it on
       [UexecRet.ukcq]'s own wand and the run keeps the copy *)
    iApply ukcq_ukc.
    iApply (urun_close_upd _ _ _ m (mword_of_int 10) _ _ _ _ _ _ _ _ _
              ltac:(unfold unot_sp; vm_compute; discriminate) with "Hheap Hstk Hufd Hcwda Hcha Hmy Hdep Hnpx").
    iIntros (h') "Hrun".
    iApply ("Hcont" $! h' r with "Hrun").
  Qed.


  (* ------------------------------------------------------------------- *)
  (* ecall, at CHDIR -- THE ONE ROW THAT MOVES THE WORKING DIRECTORY.      *)
  (*                                                                      *)
  (* chdir writes no user byte and moves no descriptor, so it reached the  *)
  (* quiet leaf on those grounds.  It cannot any more: [urun] carries the  *)
  (* process's own authority over its cwd, and the quiet leaf re-closes    *)
  (* the run at the cwd it opened at.  What chdir does is exactly what     *)
  (* [close] does to a descriptor -- it moves a ghost the program owns     *)
  (* half of -- so it gets its own leaf, and the program has to hand its   *)
  (* half in.  Nobody escapes that: an authority cannot move without the   *)
  (* fragment, which is the whole content of the fragment.                 *)
  (*                                                                      *)
  (* WHAT COMES BACK IS THE NEW INUM, AND NOTHING ABOUT IT.  The row       *)
  (* ([UsysMemOk.usys_cwd_ok] at chdir) constrains the FAILURE arm only --  *)
  (* a nonzero return leaves the cwd where it was -- because on success    *)
  (* the new inum is whatever [namei] found, which no user-level row can   *)
  (* name.  A caller that only wants to keep calling syscalls takes        *)
  (* [wp_uk_ecall_chdir_any] and never binds it.                           *)
  (* ------------------------------------------------------------------- *)
  Local Lemma usys_cwd_ok_chdir_fwd (r : mword 64) (c c' : Z) :
    usys_cwd_ok USYS_chdir r c c' -> uint r <> 0 -> c' = c.
  Proof using .
    unfold usys_cwd_ok.
    destruct (decide (USYS_chdir = USYS_chdir)) as [_ | Hne];
      [ exact (fun H => H) | exfalso; exact (Hne eq_refl) ].
  Qed.

  Lemma wp_uk_ecall_chdir (N : uk_names Σ) (h : CpuId) (m : regfile)
      (pc : mword 64) (avail : nat) (c : Z) :
    usysno m = USYS_chdir ->
    is_aligned_vaddr (Virtaddr (add_vec_int pc 4)) 2 = true ->
    uinstr_is (ukn_t N) pc false (ECALL tt) -∗
    urun N h m pc avail -∗
    udepw N m pc USYS_chdir -∗
    UserCwd.ucwd (ukn_cwd N) c -∗
    (∀ (h' : CpuId) (r : mword 64) (c' : Z),
       ⌜ uint r <> 0 -> c' = c ⌝ -∗
       UserCwd.ucwd (ukn_cwd N) c' -∗
       urun N h' (<[Regidx (mword_of_int 10) := r]> m)
         (add_vec_int pc 4) avail -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Hn Hal4.
    iIntros "#Hi Hrun Hsb Hcwd Hcont".
    iDestruct "Hrun" as (xi C pt Rfd Rut sz M pm fdv cw gn cs pidv) "(%Hlo & %Hpm & %Hlzf & %HRut & Hheap & Hstk & Hufd & Hcwda & Hcha & #Hmy & #Hdep & #Hnpx & Hb)".
    (* the key's cwd IS the one the caller's half is at *)
    iDestruct (ucwd_agree with "Hcwda Hcwd") as %->.
    iMod (udepw_mint N m pc _ M pm _ fdv c gn cs pidv
                with "Hdep Hmy Hsb Hheap Hufd") as "(Hheap & Hufd & Hdepn)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iDestruct (uvb_x0 with "Hb") as "[%Hx0 Hb]".
    iApply (UkStep.wp_uk_ecall C pt Rfd Rut pm sz Hlo Hpm HRut Hlzf M m pc fdv c gn cs pidv Hui
              (fun (s : mstate)
                   (Hp : register_lookup cur_privilege s.(sregs) = User)
                   (Hc : register_lookup (R_bitvector_64 PC) s.(sregs) = pc) =>
                 UserExecFacts.goodmb_execute_ECALL_U UserFrame.Du_r UserFrame.Du_w
                   s pc ltac:(vm_compute; reflexivity)
                   ltac:(vm_compute; reflexivity) Hp Hc)
              with "Hb Hmy").
    rewrite (uexec_ret_ecall _ _ eq_refl).
    assert (Hnum : uvis_num (uvis_of_run m pc M pm sz fdv c gn cs pidv false secc_all)
                   = USYS_chdir).
    { assert (Hraw : usys_num (uvis_tf (uvis_of_run m pc M pm sz fdv c gn cs pidv false secc_all)) = USYS_chdir)
        by (cbn [uvis_tf uvis_of_run]; rewrite tf_of_num; exact Hn).
      rewrite uvis_num_full0; [ exact Hraw | reflexivity | rewrite Hraw; usys_range ]. }
    (* the PAYMENT's guard IS the deposit's own, so it is opened BEFORE the
       number is rewritten and the destructs below then reduce both copies
       at once *)
    rewrite /uexec_pay_dep /upay_at.
    pose proof Hnum as Hnume. unfold uvis_num in Hnume. rewrite ?Hnum ?Hnume. cbv zeta.
    destruct (decide (uecall_scause = uecall_scause)) as [_ | Hpne];
      [ | exfalso; exact (Hpne eq_refl) ].
    destruct (decide (USYS_chdir = USYS_exit)) as [He | _];
      [ exfalso; unfold USYS_chdir, USYS_exit in He; discriminate He | ].
    destruct (decide (USYS_chdir = USYS_fork)) as [He | _];
      [ exfalso; unfold USYS_chdir, USYS_fork in He; discriminate He | ].
    (* THE MINT ALREADY NAMED THE PAYLOAD (app-echo.md, "SH-LINE RULING",
       R1): read's bundle is a wand from the depositing process's own exit
       payload, so nothing is re-keyed here any more -- the family the
       deposit came at IS at [ukn_pay N]. *)
    iDestruct "Hdepn" as (fdep) "[%Hfp Hdepn]".
    iExists fdep. rewrite Hfp.
    cbn [uvis_gen uvis_of_run].
    iSplitR; [ iFrame "Hmy" | ].
    iSplitL "Hdepn"; [ iExact "Hdepn" | ].
    iIntros (r M' pm' sz' fdv' cw' gn' cs' lz' secc') "%Hok %Hfdok %Hpiperow %Hcwrow %Hgnrow %Hpidrow %Hliverow %Hscrow %Hchrow _".
    (* THE LAZY BIT CROSSED THE TRAP UNCHANGED (lane LAZY-FLAG, L6).  The
       trapping key is at [false] -- the U tier's run is
       ([UexecRet.ukcq]) -- and every row but sbrk's is the equation
       ([UsysMemOk.usys_mem_ok_lazy]), so the resume key is at [false] too
       and the close below is at the run's own bit. *)
    assert (Hlzq : lz' = false)
      by (refine (usys_mem_ok_lazy _ _ _ _ _ _ _ _ _ _ _ _ Hok);
          first [ assumption | vm_compute; discriminate ]).
    subst lz'.
    (* ...AND SO DID THE MASK: not seccomp's number, so the row is the
       equation ([UsysMemOk.usys_secc_ok_quiet]), and the resume key is at
       the full mask [urun] is keyed at *)
    pose proof (fun Hne => usys_secc_ok_quiet _ _ _ _ _ Hne Hscrow) as Hscq.
    specialize (Hscq ltac:(usys_range)).
    cbn [uvis_secc uvis_of_run] in Hscq. subst secc'.
    (* the IMAGE and the TABLE crossed the trap untouched, as at a quiet
       call: chdir writes no user byte and moves no descriptor. *)
    destruct (usys_mem_ok_quiet USYS_chdir _ r _ _ _ _ _ _ _ _
                ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                Hok)
      as [-> [-> ->]].
    assert (Hview : fdv' = fdv).
    { refine (usys_fd_ok_quiet _ _ _ _ _ _ _ _ _ Hfdok);
        vm_compute; discriminate. }
    subst fdv'.
    (* ...AND SO DID THE GENERATION AND THE CHILDREN SET: chdir moves
       neither ([UsysMemOk] SS2e/SS2f). *)
    assert (Hgn : gn' = gn) by exact (usys_gen_ok_quiet _ _ _ Hgnrow).
    assert (Hch : cs' = cs) by exact (usys_ch_ok_quiet _ _ _ _ Hchrow).
    subst gn' cs'.
    cbn [uvis_M uvis_perm uvis_of_run].
    (* ...AND THE CWD DID NOT.  Both halves move together, which is the
       only way either can move. *)
    iApply uslot_bupd.
    iMod (ucwd_move N c cw' with "Hcwda Hcwd") as "[Hcwda Hcwd]".
    iModIntro.
    rewrite (uslot_bump_run m pc M M pm pm sz sz fdv fdv c cw' gn gn cs cs pidv false false secc_all secc_all r Hx0 Hal4).
    iApply ukcq_ukc.
    iApply (urun_close_upd _ _ _ m (mword_of_int 10) _ _ _ _ _ _ _ _ _
              ltac:(unfold unot_sp; vm_compute; discriminate)
              with "Hheap Hstk Hufd Hcwda Hcha Hmy Hdep Hnpx").
    iIntros (h') "Hrun".
    iApply ("Hcont" $! h' r cw' with "[%] Hcwd Hrun").
    exact (usys_cwd_ok_chdir_fwd r c cw' Hcwrow).
  Qed.

  (* ...and the shape a caller that does not track WHICH directory it is in
     takes: one resource, no binder ([UserFd.ustd_any]'s precedent).  sh's
     [cd] builtin is that caller -- it prints a diagnostic on failure and
     goes round its loop either way, and the only thing it does with its
     working directory afterwards is carry it into a fork. *)
  Lemma wp_uk_ecall_chdir_any (N : uk_names Σ) (h : CpuId) (m : regfile)
      (pc : mword 64) (avail : nat) :
    usysno m = USYS_chdir ->
    is_aligned_vaddr (Virtaddr (add_vec_int pc 4)) 2 = true ->
    uinstr_is (ukn_t N) pc false (ECALL tt) -∗
    urun N h m pc avail -∗
    udepw N m pc USYS_chdir -∗
    UserCwd.ucwd_any (ukn_cwd N) -∗
    (∀ (h' : CpuId) (r : mword 64),
       UserCwd.ucwd_any (ukn_cwd N) -∗
       urun N h' (<[Regidx (mword_of_int 10) := r]> m)
         (add_vec_int pc 4) avail -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Hn Hal4. iIntros "#Hi Hrun Hsb Hcwd Hcont".
    iDestruct "Hcwd" as (c) "Hcwd".
    iApply (wp_uk_ecall_chdir N h m pc avail c Hn Hal4 with "Hi Hrun Hsb Hcwd").
    iIntros (h' r c') "_ Hcwd Hrun".
    iApply ("Hcont" $! h' r with "[Hcwd] Hrun").
    iApply (ucwd_any_of with "Hcwd").
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
  (* -- [UserFd.ufd] at the descriptor's name, a resource a program can    *)
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
  Lemma wp_uk_ecall_open (N : uk_names Σ) (h : CpuId) (m : regfile)
      (pc : mword 64) (l : list fdstate) (avail : nat) :
    usysno m = USYS_open ->
    is_aligned_vaddr (Virtaddr (add_vec_int pc 4)) 2 = true ->
    uinstr_is (ukn_t N) pc false (ECALL tt) -∗
    urun N h m pc avail -∗
    udepw N m pc USYS_open -∗
    ustd (ukn_fd N) l -∗
    (∀ (h' : CpuId) (r : mword 64),
       ((∃ (fd : nat) (rd wr : bool) (t : fdtype),
           (* the number AND its bound: a caller that wants to feed this
              descriptor back to close/dup needs to read it as a C [int],
              and [fd < NOFILE] is what makes that reading exact *)
           ⌜r = (mword_of_int (Z.of_nat fd) : mword 64)
            /\ (fd < NOFILE)%nat
            (* ...AND IT IS NOT A PIPE (survey R4, lane SUP-ONE) -- see
               the [_recv_img] leaf below for why the fact is exported. *)
            /\ fdst_nopipe (FdOpen rd wr t)⌝ ∗
           ualloc (ukn_fd N) l fd (FdOpen rd wr t))
        ∨ (⌜r = (mword_of_int (-1) : mword 64)⌝ ∗ ustd (ukn_fd N) l)) -∗
       urun N h' (<[Regidx (mword_of_int 10) := r]> m)
         (add_vec_int pc 4) avail -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Hn Hal4.
    iIntros "#Hi Hrun Hsb Hstd Hcont".
    iDestruct "Hrun" as (xi C pt Rfd Rut sz M pm fdv cw gn cs pidv) "(%Hlo & %Hpm & %Hlzf & %HRut & Hheap & Hstk & Hufd & Hcwda & Hcha & #Hmy & #Hdep & #Hnpx & Hb)".
    iMod (udepw_mint N m pc _ M pm _ fdv cw gn cs pidv
                with "Hdep Hmy Hsb Hheap Hufd") as "(Hheap & Hufd & Hdepn)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iDestruct (uvb_x0 with "Hb") as "[%Hx0 Hb]".
    iApply (UkStep.wp_uk_ecall C pt Rfd Rut pm sz Hlo Hpm HRut Hlzf M m pc fdv cw gn cs pidv Hui
              (fun (s : mstate)
                   (Hp : register_lookup cur_privilege s.(sregs) = User)
                   (Hc : register_lookup (R_bitvector_64 PC) s.(sregs) = pc) =>
                 UserExecFacts.goodmb_execute_ECALL_U UserFrame.Du_r UserFrame.Du_w
                   s pc ltac:(vm_compute; reflexivity)
                   ltac:(vm_compute; reflexivity) Hp Hc)
              with "Hb Hmy").
    rewrite (uexec_ret_ecall _ _ eq_refl).
    assert (Hnum : uvis_num (uvis_of_run m pc M pm sz fdv cw gn cs pidv false secc_all) = USYS_open).
    { assert (Hraw : usys_num (uvis_tf (uvis_of_run m pc M pm sz fdv cw gn cs pidv false secc_all)) = USYS_open)
        by (cbn [uvis_tf uvis_of_run]; rewrite tf_of_num; exact Hn).
      rewrite uvis_num_full0; [ exact Hraw | reflexivity | rewrite Hraw; usys_range ]. }
    (* the PAYMENT's guard IS the deposit's own, so it is opened BEFORE the
       number is rewritten and the destructs below then reduce both copies
       at once *)
    rewrite /uexec_pay_dep /upay_at.
    pose proof Hnum as Hnume. unfold uvis_num in Hnume. rewrite ?Hnum ?Hnume. cbv zeta.
    destruct (decide (uecall_scause = uecall_scause)) as [_ | Hpne];
      [ | exfalso; exact (Hpne eq_refl) ].
    destruct (decide (USYS_open = USYS_exit)) as [He | _];
      [ exfalso; vm_compute in He; discriminate | ].
    destruct (decide (USYS_open = USYS_fork)) as [He | _];
      [ exfalso; vm_compute in He; discriminate | ].
    (* the arm binds the deposit's FAMILIES ([UexecSG.v]'s header); the
       law mints at some [f] and this leaf, which discards its post,
       hands that witness straight over. *)
    (* THE MINT ALREADY NAMED THE PAYLOAD (app-echo.md, "SH-LINE RULING",
       R1): read's bundle is a wand from the depositing process's own exit
       payload, so nothing is re-keyed here any more -- the family the
       deposit came at IS at [ukn_pay N]. *)
    iDestruct "Hdepn" as (fdep) "[%Hfp Hdepn]".
    iExists fdep. rewrite Hfp.
    cbn [uvis_gen uvis_of_run].
    iSplitR; [ iFrame "Hmy" | ].
    iSplitL "Hdepn"; [ iExact "Hdepn" | ].
    iIntros (r M' pm' sz' fdv' cw' gn' cs' lz' secc') "%Hok %Hfdok %Hpiperow %Hcwrow %Hgnrow %Hpidrow %Hliverow %Hscrow %Hchrow _".
    (* THE LAZY BIT CROSSED THE TRAP UNCHANGED (lane LAZY-FLAG, L6).  The
       trapping key is at [false] -- the U tier's run is
       ([UexecRet.ukcq]) -- and every row but sbrk's is the equation
       ([UsysMemOk.usys_mem_ok_lazy]), so the resume key is at [false] too
       and the close below is at the run's own bit. *)
    assert (Hlzq : lz' = false)
      by (refine (usys_mem_ok_lazy _ _ _ _ _ _ _ _ _ _ _ _ Hok);
          first [ assumption | vm_compute; discriminate ]).
    subst lz'.
    (* ...AND SO DID THE MASK: not seccomp's number, so the row is the
       equation ([UsysMemOk.usys_secc_ok_quiet]), and the resume key is at
       the full mask [urun] is keyed at *)
    pose proof (fun Hne => usys_secc_ok_quiet _ _ _ _ _ Hne Hscrow) as Hscq.
    specialize (Hscq ltac:(usys_range)).
    cbn [uvis_secc uvis_of_run] in Hscq. subst secc'.
    (* THE CWD CROSSED THE TRAP UNCHANGED -- chdir is the one row that moves
       it, and this is not it -- so the engine's half is re-keyed onto the
       view the process resumes at and the program's half never moved. *)
    assert (Hcw : cw' = cw)
      by (refine (usys_cwd_ok_quiet _ _ _ _ _ Hcwrow); vm_compute; discriminate).
    iDestruct (ucwd_auth_quiet N cw cw' Hcw with "Hcwda") as "Hcwda".
    (* ...AND SO DID THE GENERATION AND THE CHILDREN SET: no entry
       re-incarnates its caller, and this lane's children row is the
       identity at every number ([UsysMemOk] SS2e/SS2f).  Both are
       substituted rather than re-keyed -- the generation has no
       authority beside it, and the children authority is already at
       the set the process resumes at. *)
    assert (Hgn : gn' = gn) by exact (usys_gen_ok_quiet _ _ _ Hgnrow).
    assert (Hch : cs' = cs) by exact (usys_ch_ok_quiet _ _ _ _ Hchrow).
    subst gn' cs'.
    (* the IMAGE half is the quiet row: open touches no user byte *)
    destruct (usys_mem_ok_quiet USYS_open _ r _ _ _ _ _ _ _ _
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
    destruct Hfdok as [(fd & rd & wr & t & Hr & Hcl & -> & Hnpo) | [Hrm ->]].
    - (* A DESCRIPTOR CAME BACK, at the LOWEST free slot -- which is the
         promise [sys_open_post] makes and the row carries, and which the
         caller's ledger turns into a NUMBER. *)
      iMod (ufd_alloc_least (ukn_fd N) fdv l fd (FdOpen rd wr t) Hcl
              ltac:(discriminate) with "Hufd Hstd") as "[Hufd Hh]".
      iModIntro.
      (* ...AND THE TABLE STILL HOLDS NO PIPE (design/pipe.md, "The exit
         path"): open installs an inode or a device and the row says so. *)
      iDestruct (urun_rows_insert N fdv fd (FdOpen rd wr t) Hnpo
                   with "Hnpx") as "#Hnpo".
      rewrite (uslot_bump_run m pc M M pm pm sz sz fdv
                 (<[fd := FdOpen rd wr t]> fdv) cw cw' gn gn cs cs pidv false false secc_all secc_all r Hx0 Hal4).
      iApply ukcq_ukc.
      iApply (urun_close_upd _ _ _ m (mword_of_int 10) _ _ _ _ _ _ _ _ _
                ltac:(unfold unot_sp; vm_compute; discriminate)
                with "Hheap Hstk Hufd Hcwda Hcha Hmy Hdep Hnpo").
      iIntros (h') "Hrun".
      iApply ("Hcont" $! h' r with "[Hh] Hrun").
      iLeft. iExists fd, rd, wr, t. iFrame "Hh". iPureIntro.
      split_and!; [ exact Hr | | exact Hnpo ].
      (* the slot the kernel chose is a slot of the table *)
      rewrite <- Hfdlen. exact (fd_least_closed_lt _ _ Hcl).
    - (* the call failed: nothing moved, and the ledger comes straight back *)
      iModIntro.
      rewrite (uslot_bump_run m pc M M pm pm sz sz fdv fdv cw cw' gn gn cs cs pidv false false secc_all secc_all r Hx0 Hal4).
      iApply ukcq_ukc.
      iApply (urun_close_upd _ _ _ m (mword_of_int 10) _ _ _ _ _ _ _ _ _
                ltac:(unfold unot_sp; vm_compute; discriminate)
                with "Hheap Hstk Hufd Hcwda Hcha Hmy Hdep Hnpx").
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
  Lemma wp_uk_ecall_dup (N : uk_names Σ) (h : CpuId) (m : regfile)
      (pc : mword 64) (l : list fdstate) (fd0 : nat) (st : fdstate)
      (avail : nat) :
    usysno m = USYS_dup ->
    (* the argument register IS the descriptor the claim is for, read the
       way [argfd] reads it -- as a C [int] *)
    bv_signed (trunc32 (m !!! Regidx (mword_of_int 10))) = Z.of_nat fd0 ->
    st <> FdClosed ->
    (* ...AND THE RECORD HOLDS NO OFFSET HALF (lane OFF-HAND-4, S1).  dup
       COPIES its argument's row onto the slot fdalloc chose, and that slot
       is not one the record can be said to hold -- [UkRun.urun_rows_dup]'s
       guard.  At the empty held set the run's own row says the source is
       parked and the guard is discharged HERE, so no caller pays anything
       it does not already know.  (Duplicating a HELD descriptor is the
       next lane's: design/app-file.md SS3 has dup share the object's
       surrender.) *)
    is_aligned_vaddr (Virtaddr (add_vec_int pc 4)) 2 = true ->
    uinstr_is (ukn_t N) pc false (ECALL tt) -∗
    urun N h m pc avail -∗
    udepw N m pc USYS_dup -∗
    ustd (ukn_fd N) l -∗
    ufd_own (ukn_fd N) l fd0 st -∗
    (∀ (h' : CpuId) (r : mword 64),
       ((∃ fd1 : nat,
           ⌜r = (mword_of_int (Z.of_nat fd1) : mword 64)
            /\ (fd1 < NOFILE)%nat⌝ ∗
           ualloc (ukn_fd N) l fd1 st ∗ ufd_own (ukn_fd N) (ustd_after l st) fd0 st)
        (* ...OR IT FAILED, AND THE LEDGER SAYS WHY.  [UsysMemOk]'s dup row
           gives two reasons for a -1 and the caller's own claim refutes
           the first (the source is OPEN, [Hstne]), so what is left is THE
           TABLE WAS FULL -- and a full table has no closed slot in its
           standard-stream prefix either, which is the form the caller can
           read.  A caller whose ledger holds a CLOSED standard stream
           therefore refutes this arm by computation, which is what lets
           /init pin fds 1 and 2 at the console. *)
        ∨ (⌜r = (mword_of_int (-1) : mword 64)
            /\ fd_lowest_closed l = None⌝ ∗
           ustd (ukn_fd N) l ∗ ufd_own (ukn_fd N) l fd0 st)) -∗
       urun N h' (<[Regidx (mword_of_int 10) := r]> m)
         (add_vec_int pc 4) avail -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Hn Harg Hstne Hal4.
    iIntros "#Hi Hrun Hsb Hstd Hh0 Hcont".
    iDestruct "Hrun" as (xi C pt Rfd Rut sz M pm fdv cw gn cs pidv) "(%Hlo & %Hpm & %Hlzf & %HRut & Hheap & Hstk & Hufd & Hcwda & Hcha & #Hmy & #Hdep & #Hnpx & Hb)".
    iMod (udepw_mint N m pc _ M pm _ fdv cw gn cs pidv
                with "Hdep Hmy Hsb Hheap Hufd") as "(Hheap & Hufd & Hdepn)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iDestruct (uvb_x0 with "Hb") as "[%Hx0 Hb]".
    (* the claim READS the view: this is what says the source descriptor is
       open, and at which state -- which is what dup's row copies. *)
    iDestruct (ufd_own_agree with "Hufd Hstd Hh0") as %[Hsrc _].
    iDestruct (ufd_auth_len with "Hufd") as %Hfdlen.
    (* ...and the LEDGER against the same authority, which is what turns the
       row's `no closed slot in the table' into `none in the prefix' *)
    iDestruct (ustd_agree (ukn_fd N) fdv l with "Hufd Hstd") as %Htake.
    (* ...and the slot the copy lands in is never the source's, which is
       what lets the claim come back at the ledger the copy left *)
    iDestruct (ufd_own_ne_lowest (ukn_fd N) l fd0 st Hstne with "Hstd Hh0") as %Hnel.
    iApply (UkStep.wp_uk_ecall C pt Rfd Rut pm sz Hlo Hpm HRut Hlzf M m pc fdv cw gn cs pidv Hui
              (fun (s : mstate)
                   (Hp : register_lookup cur_privilege s.(sregs) = User)
                   (Hc : register_lookup (R_bitvector_64 PC) s.(sregs) = pc) =>
                 UserExecFacts.goodmb_execute_ECALL_U UserFrame.Du_r UserFrame.Du_w
                   s pc ltac:(vm_compute; reflexivity)
                   ltac:(vm_compute; reflexivity) Hp Hc)
              with "Hb Hmy").
    rewrite (uexec_ret_ecall _ _ eq_refl).
    assert (Hnum : uvis_num (uvis_of_run m pc M pm sz fdv cw gn cs pidv false secc_all) = USYS_dup).
    { assert (Hraw : usys_num (uvis_tf (uvis_of_run m pc M pm sz fdv cw gn cs pidv false secc_all)) = USYS_dup)
        by (cbn [uvis_tf uvis_of_run]; rewrite tf_of_num; exact Hn).
      rewrite uvis_num_full0; [ exact Hraw | reflexivity | rewrite Hraw; usys_range ]. }
    (* the PAYMENT's guard IS the deposit's own, so it is opened BEFORE the
       number is rewritten and the destructs below then reduce both copies
       at once *)
    rewrite /uexec_pay_dep /upay_at.
    pose proof Hnum as Hnume. unfold uvis_num in Hnume. rewrite ?Hnum ?Hnume. cbv zeta.
    destruct (decide (uecall_scause = uecall_scause)) as [_ | Hpne];
      [ | exfalso; exact (Hpne eq_refl) ].
    destruct (decide (USYS_dup = USYS_exit)) as [He | _];
      [ exfalso; vm_compute in He; discriminate | ].
    destruct (decide (USYS_dup = USYS_fork)) as [He | _];
      [ exfalso; vm_compute in He; discriminate | ].
    (* the arm binds the deposit's FAMILIES ([UexecSG.v]'s header); the
       law mints at some [f] and this leaf, which discards its post,
       hands that witness straight over. *)
    (* THE MINT ALREADY NAMED THE PAYLOAD (app-echo.md, "SH-LINE RULING",
       R1): read's bundle is a wand from the depositing process's own exit
       payload, so nothing is re-keyed here any more -- the family the
       deposit came at IS at [ukn_pay N]. *)
    iDestruct "Hdepn" as (fdep) "[%Hfp Hdepn]".
    iExists fdep. rewrite Hfp.
    cbn [uvis_gen uvis_of_run].
    iSplitR; [ iFrame "Hmy" | ].
    iSplitL "Hdepn"; [ iExact "Hdepn" | ].
    iIntros (r M' pm' sz' fdv' cw' gn' cs' lz' secc') "%Hok %Hfdok %Hpiperow %Hcwrow %Hgnrow %Hpidrow %Hliverow %Hscrow %Hchrow _".
    (* THE LAZY BIT CROSSED THE TRAP UNCHANGED (lane LAZY-FLAG, L6).  The
       trapping key is at [false] -- the U tier's run is
       ([UexecRet.ukcq]) -- and every row but sbrk's is the equation
       ([UsysMemOk.usys_mem_ok_lazy]), so the resume key is at [false] too
       and the close below is at the run's own bit. *)
    assert (Hlzq : lz' = false)
      by (refine (usys_mem_ok_lazy _ _ _ _ _ _ _ _ _ _ _ _ Hok);
          first [ assumption | vm_compute; discriminate ]).
    subst lz'.
    (* ...AND SO DID THE MASK: not seccomp's number, so the row is the
       equation ([UsysMemOk.usys_secc_ok_quiet]), and the resume key is at
       the full mask [urun] is keyed at *)
    pose proof (fun Hne => usys_secc_ok_quiet _ _ _ _ _ Hne Hscrow) as Hscq.
    specialize (Hscq ltac:(usys_range)).
    cbn [uvis_secc uvis_of_run] in Hscq. subst secc'.
    (* THE CWD CROSSED THE TRAP UNCHANGED -- chdir is the one row that moves
       it, and this is not it -- so the engine's half is re-keyed onto the
       view the process resumes at and the program's half never moved. *)
    assert (Hcw : cw' = cw)
      by (refine (usys_cwd_ok_quiet _ _ _ _ _ Hcwrow); vm_compute; discriminate).
    iDestruct (ucwd_auth_quiet N cw cw' Hcw with "Hcwda") as "Hcwda".
    (* ...AND SO DID THE GENERATION AND THE CHILDREN SET: no entry
       re-incarnates its caller, and this lane's children row is the
       identity at every number ([UsysMemOk] SS2e/SS2f).  Both are
       substituted rather than re-keyed -- the generation has no
       authority beside it, and the children authority is already at
       the set the process resumes at. *)
    assert (Hgn : gn' = gn) by exact (usys_gen_ok_quiet _ _ _ Hgnrow).
    assert (Hch : cs' = cs) by exact (usys_ch_ok_quiet _ _ _ _ Hchrow).
    subst gn' cs'.
    destruct (usys_mem_ok_quiet USYS_dup _ r _ _ _ _ _ _ _ _
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
    assert (Haiz : usys_argfd (tf_of m pc) = Z.of_nat fd0).
    { unfold usys_argfd. cbn [tf_of]. exact Harg. }
    assert (Hai : Z.to_nat (usys_argfd (tf_of m pc)) = fd0).
    { rewrite Haiz. exact (Nat2Z.id fd0). }
    iApply uslot_bupd.
    destruct Hfdok as [(fd1 & Hr & Hcl & _ & ->) | (Hrm & -> & Hwhy)].
    - (* DUPLICATED.  [Hai] turns the row's copied state into the caller's
         own [st] ([Hsrc], off the claim), and the destination slot was the
         LOWEST free one, which the ledger reads as a number. *)
      rewrite Hai (list_lookup_total_correct fdv fd0 st Hsrc).
      iDestruct (ufd_own_after (ukn_fd N) l fd0 st st Hnel with "Hh0") as "Hh0".
      iMod (ufd_alloc_least (ukn_fd N) fdv l fd1 st Hcl Hstne with "Hufd Hstd")
        as "[Hufd Hh1]".
      iModIntro.
      (* ...and dup copies a row the table already had, so it holds no
         pipe either (design/pipe.md, "The exit path") *)
      iDestruct (urun_rows_dup N fdv fd0 fd1 st Hsrc with "Hnpx") as "#Hnpo".
      rewrite (uslot_bump_run m pc M M pm pm sz sz fdv
                 (<[fd1 := st]> fdv) cw cw' gn gn cs cs pidv false false secc_all secc_all r Hx0 Hal4).
      iApply ukcq_ukc.
      iApply (urun_close_upd _ _ _ m (mword_of_int 10) _ _ _ _ _ _ _ _ _
                ltac:(unfold unot_sp; vm_compute; discriminate)
                with "Hheap Hstk Hufd Hcwda Hcha Hmy Hdep Hnpo").
      iIntros (h') "Hrun".
      iApply ("Hcont" $! h' r with "[Hh1 Hh0] Hrun").
      iLeft. iExists fd1. iFrame "Hh1 Hh0". iPureIntro.
      split; [ exact Hr | ].
      rewrite <- Hfdlen. exact (fd_least_closed_lt _ _ Hcl).
    - (* THE TABLE WAS FULL -- the row's OTHER reason for a -1, `the
         argument is not an open descriptor', is refuted by the caller's own
         claim ([Hsrc] at [Hstne]).  So no slot of the table is closed, and
         in particular none of the prefix the LEDGER is: [fd_lowest_closed]
         of an append answers the prefix first ([FdSlots]), so a closed slot
         in the prefix would have been the table's own answer.  Nothing
         moved, and both resources come straight back. *)
      assert (Hnone : fd_lowest_closed l = None).
      { destruct Hwhy as [Hno | Hfull].
        - exfalso. exact (Hstne (Hno fd0 st Haiz Hsrc)).
        - rewrite <- Htake.
          destruct (fd_lowest_closed (take NSTD fdv)) as [k |] eqn:Hk;
            [| reflexivity ].
          exfalso. rewrite <- (take_drop NSTD fdv) in Hfull.
          rewrite fd_lowest_closed_app Hk in Hfull. discriminate Hfull. }
      iModIntro.
      rewrite (uslot_bump_run m pc M M pm pm sz sz fdv fdv cw cw' gn gn cs cs pidv false false secc_all secc_all r Hx0 Hal4).
      iApply ukcq_ukc.
      iApply (urun_close_upd _ _ _ m (mword_of_int 10) _ _ _ _ _ _ _ _ _
                ltac:(unfold unot_sp; vm_compute; discriminate)
                with "Hheap Hstk Hufd Hcwda Hcha Hmy Hdep Hnpx").
      iIntros (h') "Hrun".
      iApply ("Hcont" $! h' r with "[Hstd Hh0] Hrun").
      iRight. iFrame "Hstd Hh0". iPureIntro. split; [ exact Hrm | exact Hnone ].
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
  Lemma wp_uk_ecall_dup_untracked (N : uk_names Σ) (h : CpuId)
      (m : regfile) (pc : mword 64) (l : list fdstate) (avail : nat) :
    usysno m = USYS_dup ->
    (* ...and the record holds no offset half -- [wp_uk_ecall_dup]'s note *)
    is_aligned_vaddr (Virtaddr (add_vec_int pc 4)) 2 = true ->
    uinstr_is (ukn_t N) pc false (ECALL tt) -∗
    urun N h m pc avail -∗
    udepw N m pc USYS_dup -∗
    ustd (ukn_fd N) l -∗
    (∀ (h' : CpuId) (r : mword 64) (l' : list fdstate),
       ustd (ukn_fd N) l' -∗
       urun N h' (<[Regidx (mword_of_int 10) := r]> m)
         (add_vec_int pc 4) avail -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Hn Hal4.
    iIntros "#Hi Hrun Hsb Hstd Hcont".
    iDestruct "Hrun" as (xi C pt Rfd Rut sz M pm fdv cw gn cs pidv) "(%Hlo & %Hpm & %Hlzf & %HRut & Hheap & Hstk & Hufd & Hcwda & Hcha & #Hmy & #Hdep & #Hnpx & Hb)".
    iMod (udepw_mint N m pc _ M pm _ fdv cw gn cs pidv
                with "Hdep Hmy Hsb Hheap Hufd") as "(Hheap & Hufd & Hdepn)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iDestruct (uvb_x0 with "Hb") as "[%Hx0 Hb]".
    iApply (UkStep.wp_uk_ecall C pt Rfd Rut pm sz Hlo Hpm HRut Hlzf M m pc fdv cw gn cs pidv Hui
              (fun (s : mstate)
                   (Hp : register_lookup cur_privilege s.(sregs) = User)
                   (Hc : register_lookup (R_bitvector_64 PC) s.(sregs) = pc) =>
                 UserExecFacts.goodmb_execute_ECALL_U UserFrame.Du_r UserFrame.Du_w
                   s pc ltac:(vm_compute; reflexivity)
                   ltac:(vm_compute; reflexivity) Hp Hc)
              with "Hb Hmy").
    rewrite (uexec_ret_ecall _ _ eq_refl).
    assert (Hnum : uvis_num (uvis_of_run m pc M pm sz fdv cw gn cs pidv false secc_all) = USYS_dup).
    { assert (Hraw : usys_num (uvis_tf (uvis_of_run m pc M pm sz fdv cw gn cs pidv false secc_all)) = USYS_dup)
        by (cbn [uvis_tf uvis_of_run]; rewrite tf_of_num; exact Hn).
      rewrite uvis_num_full0; [ exact Hraw | reflexivity | rewrite Hraw; usys_range ]. }
    (* the PAYMENT's guard IS the deposit's own, so it is opened BEFORE the
       number is rewritten and the destructs below then reduce both copies
       at once *)
    rewrite /uexec_pay_dep /upay_at.
    pose proof Hnum as Hnume. unfold uvis_num in Hnume. rewrite ?Hnum ?Hnume. cbv zeta.
    destruct (decide (uecall_scause = uecall_scause)) as [_ | Hpne];
      [ | exfalso; exact (Hpne eq_refl) ].
    destruct (decide (USYS_dup = USYS_exit)) as [He | _];
      [ exfalso; vm_compute in He; discriminate | ].
    destruct (decide (USYS_dup = USYS_fork)) as [He | _];
      [ exfalso; vm_compute in He; discriminate | ].
    (* the arm binds the deposit's FAMILIES ([UexecSG.v]'s header); the
       law mints at some [f] and this leaf, which discards its post,
       hands that witness straight over. *)
    (* THE MINT ALREADY NAMED THE PAYLOAD (app-echo.md, "SH-LINE RULING",
       R1): read's bundle is a wand from the depositing process's own exit
       payload, so nothing is re-keyed here any more -- the family the
       deposit came at IS at [ukn_pay N]. *)
    iDestruct "Hdepn" as (fdep) "[%Hfp Hdepn]".
    iExists fdep. rewrite Hfp.
    cbn [uvis_gen uvis_of_run].
    iSplitR; [ iFrame "Hmy" | ].
    iSplitL "Hdepn"; [ iExact "Hdepn" | ].
    iIntros (r M' pm' sz' fdv' cw' gn' cs' lz' secc') "%Hok %Hfdok %Hpiperow %Hcwrow %Hgnrow %Hpidrow %Hliverow %Hscrow %Hchrow _".
    (* THE LAZY BIT CROSSED THE TRAP UNCHANGED (lane LAZY-FLAG, L6).  The
       trapping key is at [false] -- the U tier's run is
       ([UexecRet.ukcq]) -- and every row but sbrk's is the equation
       ([UsysMemOk.usys_mem_ok_lazy]), so the resume key is at [false] too
       and the close below is at the run's own bit. *)
    assert (Hlzq : lz' = false)
      by (refine (usys_mem_ok_lazy _ _ _ _ _ _ _ _ _ _ _ _ Hok);
          first [ assumption | vm_compute; discriminate ]).
    subst lz'.
    (* ...AND SO DID THE MASK: not seccomp's number, so the row is the
       equation ([UsysMemOk.usys_secc_ok_quiet]), and the resume key is at
       the full mask [urun] is keyed at *)
    pose proof (fun Hne => usys_secc_ok_quiet _ _ _ _ _ Hne Hscrow) as Hscq.
    specialize (Hscq ltac:(usys_range)).
    cbn [uvis_secc uvis_of_run] in Hscq. subst secc'.
    (* THE CWD CROSSED THE TRAP UNCHANGED -- chdir is the one row that moves
       it, and this is not it -- so the engine's half is re-keyed onto the
       view the process resumes at and the program's half never moved. *)
    assert (Hcw : cw' = cw)
      by (refine (usys_cwd_ok_quiet _ _ _ _ _ Hcwrow); vm_compute; discriminate).
    iDestruct (ucwd_auth_quiet N cw cw' Hcw with "Hcwda") as "Hcwda".
    (* ...AND SO DID THE GENERATION AND THE CHILDREN SET: no entry
       re-incarnates its caller, and this lane's children row is the
       identity at every number ([UsysMemOk] SS2e/SS2f).  Both are
       substituted rather than re-keyed -- the generation has no
       authority beside it, and the children authority is already at
       the set the process resumes at. *)
    assert (Hgn : gn' = gn) by exact (usys_gen_ok_quiet _ _ _ Hgnrow).
    assert (Hch : cs' = cs) by exact (usys_ch_ok_quiet _ _ _ _ Hchrow).
    subst gn' cs'.
    destruct (usys_mem_ok_quiet USYS_dup _ r _ _ _ _ _ _ _ _
                ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)
                ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) Hok)
      as [-> [-> ->]].
    unfold usys_fd_ok in Hfdok.
    destruct (decide (USYS_dup = USYS_close)) as [Hc | _]; [ discriminate Hc | ].
    destruct (decide (USYS_dup = USYS_dup)) as [_ | Hc];
      [ | exfalso; exact (Hc eq_refl) ].
    cbn [uvis_M uvis_perm uvis_fd uvis_of_run] in Hfdok |- *.
    iApply uslot_bupd.
    destruct Hfdok as [(fd1 & Hr & Hcl & _ & ->) | (Hrm & -> & _)].
    - iAssert (|==> ufd_auth (ukn_fd N)
                 (<[fd1 := fdv !!! Z.to_nat (usys_argfd (tf_of m pc))]> fdv) ∗
                 ∃ l' : list fdstate, ustd (ukn_fd N) l')%I
        with "[Hufd Hstd]" as ">[Hufd Hstd]".
      { destruct (decide (fdv !!! Z.to_nat (usys_argfd (tf_of m pc)) = FdClosed))
          as [He | Hne].
        - rewrite He.
          iDestruct (ufd_alloc_least_closed (ukn_fd N) fdv fd1 Hcl with "Hufd") as "$".
          iModIntro. by iExists l.
        - iMod (ufd_alloc_least_any (ukn_fd N) fdv l fd1 _ Hcl Hne with "Hufd Hstd")
            as "[$ $]". by iModIntro. }
      iDestruct "Hstd" as (l') "Hstd".
      iModIntro.
      (* ...and dup copies a row the table already had *)
      iDestruct (urun_rows_copy N fdv (Z.to_nat (usys_argfd (tf_of m pc))) fd1
                   with "Hnpx") as "#Hnpo".
      rewrite (uslot_bump_run m pc M M pm pm sz sz fdv
                 (<[fd1 := fdv !!! Z.to_nat (usys_argfd (tf_of m pc))]> fdv) cw cw' gn gn cs cs pidv false false secc_all secc_all
                 r Hx0 Hal4).
      iApply ukcq_ukc.
      iApply (urun_close_upd _ _ _ m (mword_of_int 10) _ _ _ _ _ _ _ _ _
                ltac:(unfold unot_sp; vm_compute; discriminate)
                with "Hheap Hstk Hufd Hcwda Hcha Hmy Hdep Hnpo").
      iIntros (h') "Hrun". iApply ("Hcont" $! h' r l' with "Hstd Hrun").
    - iModIntro.
      rewrite (uslot_bump_run m pc M M pm pm sz sz fdv fdv cw cw' gn gn cs cs pidv false false secc_all secc_all r Hx0 Hal4).
      iApply ukcq_ukc.
      iApply (urun_close_upd _ _ _ m (mword_of_int 10) _ _ _ _ _ _ _ _ _
                ltac:(unfold unot_sp; vm_compute; discriminate)
                with "Hheap Hstk Hufd Hcwda Hcha Hmy Hdep Hnpx").
      iIntros (h') "Hrun". iApply ("Hcont" $! h' r l with "Hstd Hrun").
  Qed.

  (* ------------------------------------------------------------------- *)
  (* ecall, at DUP OF A CLOSED DESCRIPTOR.                                 *)
  (*                                                                       *)
  (* [wp_uk_ecall_dup] above takes [st <> FdClosed] as a PREMISE, so a      *)
  (* caller whose source slot is CLOSED cannot go through it -- and that    *)
  (* is exactly /init on the arm where its console open failed: it runs     *)
  (* [dup(0); dup(0)] whatever the open returned (the C never tests the     *)
  (* second one, [UInitCons.v]'s finding (a)).  The untracked leaf          *)
  (* ([wp_uk_ecall_dup_untracked]) does move the authority, but it hands    *)
  (* the ledger back at a state IT DOES NOT NAME, and what the CLOSED arm   *)
  (* of init's head has to say is that the ledger did not move at all.      *)
  (*                                                                       *)
  (* WHAT THE ROW GIVES.  [UsysMemOk.usys_fd_ok]'s dup row is a            *)
  (* disjunction and BOTH arms are now decided here.  The TABLE does not    *)
  (* move on either: the success arm says the lowest free slot became a     *)
  (* COPY of the argument's state, and a copy of [FdClosed] is [FdClosed],  *)
  (* so the insert lands on a slot the scan already found closed and the    *)
  (* list is unchanged ([UserFd.ufd_alloc_least_closed]).  And [r = -1] is  *)
  (* a theorem too, which it was NOT before lane DUP-ROW: the success arm   *)
  (* now carries `the source was open' -- [argfd] let the call past, and it *)
  (* rejects a null [p->ofile] slot -- so a CLOSED source REFUTES that arm  *)
  (* outright and only the failure arm is left.  /init drops both dup       *)
  (* results, so it does not need this; the leaf states it because it is    *)
  (* what the code does and the row can now say it.                         *)
  (*                                                                       *)
  (* THE WALK IS [wp_uk_ecall_dup_untracked]'s, with the ledger READ        *)
  (* against the authority before the trap ([UserFd.ustd_agree]) instead of *)
  (* handed back at a state nobody names.                                   *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_uk_ecall_dup_closed (N : uk_names Σ) (h : CpuId) (m : regfile)
      (pc : mword 64) (l : list fdstate) (fd0 : nat) (avail : nat) :
    usysno m = USYS_dup ->
    (* the argument register IS the descriptor the ledger is read at, the
       way [argfd] reads it -- as a C [int] *)
    bv_signed (trunc32 (m !!! Regidx (mword_of_int 10))) = Z.of_nat fd0 ->
    (* ...and it is a STANDARD STREAM the ledger has a row for, CLOSED *)
    (fd0 < NSTD)%nat ->
    l !! fd0 = Some FdClosed ->
    is_aligned_vaddr (Virtaddr (add_vec_int pc 4)) 2 = true ->
    uinstr_is (ukn_t N) pc false (ECALL tt) -∗
    urun N h m pc avail -∗
    udepw N m pc USYS_dup -∗
    ustd (ukn_fd N) l -∗
    (∀ (h' : CpuId) (r : mword 64),
       (* THE CALL FAILED: [argfd] rejects a null slot, and the row's
          success arm -- which now carries `the source was open' -- is
          refuted by the caller's own [Hrow]. *)
       ⌜r = (mword_of_int (-1) : mword 64)⌝ -∗
       (* ...AND THE LEDGER, UNCHANGED *)
       ustd (ukn_fd N) l -∗
       urun N h' (<[Regidx (mword_of_int 10) := r]> m)
         (add_vec_int pc 4) avail -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Hn Harg Hlt Hrow Hal4.
    iIntros "#Hi Hrun Hsb Hstd Hcont".
    iDestruct "Hrun" as (xi C pt Rfd Rut sz M pm fdv cw gn cs pidv) "(%Hlo & %Hpm & %Hlzf & %HRut & Hheap & Hstk & Hufd & Hcwda & Hcha & #Hmy & #Hdep & #Hnpx & Hb)".
    (* THE LEDGER READS THE VIEW, which is the whole argument: the source
       slot is CLOSED in the table, so dup's success arm copies [FdClosed]
       into a slot the scan already found closed and the list does not
       move ([UserFd.ufd_alloc_least_closed]). *)
    iDestruct (ustd_agree (ukn_fd N) fdv l with "Hufd Hstd") as %Htake.
    assert (Htk : take NSTD fdv !! fd0 = Some FdClosed)
      by (rewrite Htake; exact Hrow).
    rewrite lookup_take in Htk; [| exact Hlt].
    iMod (udepw_mint N m pc _ M pm _ fdv cw gn cs pidv
                with "Hdep Hmy Hsb Hheap Hufd") as "(Hheap & Hufd & Hdepn)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iDestruct (uvb_x0 with "Hb") as "[%Hx0 Hb]".
    iApply (UkStep.wp_uk_ecall C pt Rfd Rut pm sz Hlo Hpm HRut Hlzf M m pc fdv cw gn cs pidv Hui
              (fun (s : mstate)
                   (Hp : register_lookup cur_privilege s.(sregs) = User)
                   (Hc : register_lookup (R_bitvector_64 PC) s.(sregs) = pc) =>
                 UserExecFacts.goodmb_execute_ECALL_U UserFrame.Du_r UserFrame.Du_w
                   s pc ltac:(vm_compute; reflexivity)
                   ltac:(vm_compute; reflexivity) Hp Hc)
              with "Hb Hmy").
    rewrite (uexec_ret_ecall _ _ eq_refl).
    assert (Hnum : uvis_num (uvis_of_run m pc M pm sz fdv cw gn cs pidv false secc_all) = USYS_dup).
    { assert (Hraw : usys_num (uvis_tf (uvis_of_run m pc M pm sz fdv cw gn cs pidv false secc_all)) = USYS_dup)
        by (cbn [uvis_tf uvis_of_run]; rewrite tf_of_num; exact Hn).
      rewrite uvis_num_full0; [ exact Hraw | reflexivity | rewrite Hraw; usys_range ]. }
    rewrite /uexec_pay_dep /upay_at.
    pose proof Hnum as Hnume. unfold uvis_num in Hnume. rewrite ?Hnum ?Hnume. cbv zeta.
    destruct (decide (uecall_scause = uecall_scause)) as [_ | Hpne];
      [ | exfalso; exact (Hpne eq_refl) ].
    destruct (decide (USYS_dup = USYS_exit)) as [He | _];
      [ exfalso; vm_compute in He; discriminate | ].
    destruct (decide (USYS_dup = USYS_fork)) as [He | _];
      [ exfalso; vm_compute in He; discriminate | ].
    iDestruct "Hdepn" as (fdep) "[%Hfp Hdepn]".
    iExists fdep. rewrite Hfp.
    cbn [uvis_gen uvis_of_run].
    iSplitR; [ iFrame "Hmy" | ].
    iSplitL "Hdepn"; [ iExact "Hdepn" | ].
    iIntros (r M' pm' sz' fdv' cw' gn' cs' lz' secc') "%Hok %Hfdok %Hpiperow %Hcwrow %Hgnrow %Hpidrow %Hliverow %Hscrow %Hchrow _".
    (* THE LAZY BIT CROSSED THE TRAP UNCHANGED (lane LAZY-FLAG, L6).  The
       trapping key is at [false] -- the U tier's run is
       ([UexecRet.ukcq]) -- and every row but sbrk's is the equation
       ([UsysMemOk.usys_mem_ok_lazy]), so the resume key is at [false] too
       and the close below is at the run's own bit. *)
    assert (Hlzq : lz' = false)
      by (refine (usys_mem_ok_lazy _ _ _ _ _ _ _ _ _ _ _ _ Hok);
          first [ assumption | vm_compute; discriminate ]).
    subst lz'.
    (* ...AND SO DID THE MASK: not seccomp's number, so the row is the
       equation ([UsysMemOk.usys_secc_ok_quiet]), and the resume key is at
       the full mask [urun] is keyed at *)
    pose proof (fun Hne => usys_secc_ok_quiet _ _ _ _ _ Hne Hscrow) as Hscq.
    specialize (Hscq ltac:(usys_range)).
    cbn [uvis_secc uvis_of_run] in Hscq. subst secc'.
    assert (Hcw : cw' = cw)
      by (refine (usys_cwd_ok_quiet _ _ _ _ _ Hcwrow); vm_compute; discriminate).
    iDestruct (ucwd_auth_quiet N cw cw' Hcw with "Hcwda") as "Hcwda".
    assert (Hgn : gn' = gn) by exact (usys_gen_ok_quiet _ _ _ Hgnrow).
    assert (Hch : cs' = cs) by exact (usys_ch_ok_quiet _ _ _ _ Hchrow).
    subst gn' cs'.
    destruct (usys_mem_ok_quiet USYS_dup _ r _ _ _ _ _ _ _ _
                ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)
                ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) Hok)
      as [-> [-> ->]].
    unfold usys_fd_ok in Hfdok.
    destruct (decide (USYS_dup = USYS_close)) as [Hc | _]; [ discriminate Hc | ].
    destruct (decide (USYS_dup = USYS_dup)) as [_ | Hc];
      [ | exfalso; exact (Hc eq_refl) ].
    cbn [uvis_M uvis_perm uvis_fd uvis_of_run] in Hfdok |- *.
    assert (Hai : Z.to_nat (usys_argfd (tf_of m pc)) = fd0).
    { unfold usys_argfd. cbn [tf_of]. rewrite Harg. exact (Nat2Z.id fd0). }
    destruct Hfdok as [(fd1 & Hr & Hcl & Hop & ->) | (Hrm & -> & _)].
    - (* REFUTED: the success arm says the source was OPEN and the caller's
         own ledger says it was CLOSED. *)
      exfalso. rewrite Hai in Hop. exact (Hop Htk).
    - (* the call failed: nothing moved at all, and the row names the -1 *)
      rewrite (uslot_bump_run m pc M M pm pm sz sz fdv fdv cw cw' gn gn cs cs pidv false false secc_all secc_all r Hx0 Hal4).
      iApply ukcq_ukc.
      iApply (urun_close_upd _ _ _ m (mword_of_int 10) _ _ _ _ _ _ _ _ _
                ltac:(unfold unot_sp; vm_compute; discriminate)
                with "Hheap Hstk Hufd Hcwda Hcha Hmy Hdep Hnpx").
      iIntros (h') "Hrun".
      iApply ("Hcont" $! h' r with "[] Hstd Hrun"). by iPureIntro.
  Qed.

  (* THE KEY'S READING OF ARGUMENT 0, from an index the caller named and a
     row of the table.  [UkReadRows.ufd_fd_st_of_key] is the same fact and
     is the one every ARM file uses; it sits ABOVE this file (it is stated
     beside the row builders, which need the instance), and the close
     leaves below need it to discharge their own close deposit, so the pure
     step is taken here too. *)
  Lemma uk_fd_st_of_key (v0 : mword 64) (fdv : list fdstate) (fd : nat)
      (st : fdstate) :
    bv_signed (trunc32 v0) = Z.of_nat fd ->
    (fd < NOFILE)%nat ->
    fdv !! fd = Some st ->
    fd_st_of_key v0 fdv = st.
  Proof using .
    intros H0 Hlt Hlk. rewrite /fd_st_of_key H0.
    destruct (decide (0 <= Z.of_nat fd < Z.of_nat NOFILE)) as [_ | Hc];
      [ | exfalso; apply Hc; lia ].
    rewrite Nat2Z.id Hlk. reflexivity.
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
  Proof using .
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
  Lemma wp_uk_ecall_close (N : uk_names Σ) (h : CpuId) (m : regfile)
      (pc : mword 64) (fd : nat) (st : fdstate) (avail : nat) :
    usysno m = USYS_close ->
    bv_signed (trunc32 (m !!! Regidx (mword_of_int 10))) = Z.of_nat fd ->
    is_aligned_vaddr (Virtaddr (add_vec_int pc 4)) 2 = true ->
    uinstr_is (ukn_t N) pc false (ECALL tt) -∗
    urun N h m pc avail -∗
    (* THE CLOSE ROW (design/pipe.md, "The byte queue"): close(2) is no
       longer a free number, and what pays it is decided by the state the
       HANDLE names -- nothing off a pipe.  [UkRun.udepw_cl_nonpipe] is the
       whole premise for a caller that knows its descriptor is not one. *)
    udepw_cl N m pc st -∗
    ufd (ukn_fd N) fd st -∗
    (∀ (h' : CpuId) (r : mword 64),
       ⌜uint r = 0⌝ -∗
       urun N h' (<[Regidx (mword_of_int 10) := r]> m)
         (add_vec_int pc 4) avail -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Hn Harg Hal4.
    iIntros "#Hi Hrun Hsb Hh Hcont".
    iDestruct "Hrun" as (xi C pt Rfd Rut sz M pm fdv cw gn cs pidv) "(%Hlo & %Hpm & %Hlzf & %HRut & Hheap & Hstk & Hufd & Hcwda & Hcha & #Hmy & #Hdep & #Hnpx & Hb)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iDestruct (ufd_agree with "Hufd Hh") as %Hi.
    iDestruct (ufd_auth_len with "Hufd") as %Hfdlen.
    assert (Hfdlt : (fd < NOFILE)%nat)
      by (rewrite <- Hfdlen; exact (lookup_lt_Some fdv fd st Hi)).
    (* THE CLOSE ROW IS MINTED HERE, off the handle (design/pipe.md): the
       key's argument 0 names exactly the descriptor the caller handed in,
       so "not a pipe" about the handle IS "this key's close row is [emp]". *)
    iMod (udepw_cl_mint N m pc st M pm sz fdv cw gn cs pidv
                (uk_fd_st_of_key _ fdv fd st Harg Hfdlt Hi)
                with "Hdep Hmy Hsb Hheap Hufd") as "(Hheap & Hufd & Hdepn)".
    iDestruct (uvb_x0 with "Hb") as "[%Hx0 Hb]".
    iDestruct (ufd_ne with "Hh") as %Hne.
    iApply (UkStep.wp_uk_ecall C pt Rfd Rut pm sz Hlo Hpm HRut Hlzf M m pc fdv cw gn cs pidv Hui
              (fun (s : mstate)
                   (Hp : register_lookup cur_privilege s.(sregs) = User)
                   (Hc : register_lookup (R_bitvector_64 PC) s.(sregs) = pc) =>
                 UserExecFacts.goodmb_execute_ECALL_U UserFrame.Du_r UserFrame.Du_w
                   s pc ltac:(vm_compute; reflexivity)
                   ltac:(vm_compute; reflexivity) Hp Hc)
              with "Hb Hmy").
    rewrite (uexec_ret_ecall _ _ eq_refl).
    assert (Hnum : uvis_num (uvis_of_run m pc M pm sz fdv cw gn cs pidv false secc_all) = USYS_close).
    { assert (Hraw : usys_num (uvis_tf (uvis_of_run m pc M pm sz fdv cw gn cs pidv false secc_all)) = USYS_close)
        by (cbn [uvis_tf uvis_of_run]; rewrite tf_of_num; exact Hn).
      rewrite uvis_num_full0; [ exact Hraw | reflexivity | rewrite Hraw; usys_range ]. }
    (* the PAYMENT's guard IS the deposit's own, so it is opened BEFORE the
       number is rewritten and the destructs below then reduce both copies
       at once *)
    rewrite /uexec_pay_dep /upay_at.
    pose proof Hnum as Hnume. unfold uvis_num in Hnume. rewrite ?Hnum ?Hnume. cbv zeta.
    destruct (decide (uecall_scause = uecall_scause)) as [_ | Hpne];
      [ | exfalso; exact (Hpne eq_refl) ].
    destruct (decide (USYS_close = USYS_exit)) as [He | _];
      [ exfalso; vm_compute in He; discriminate | ].
    destruct (decide (USYS_close = USYS_fork)) as [He | _];
      [ exfalso; vm_compute in He; discriminate | ].
    (* the arm binds the deposit's FAMILIES ([UexecSG.v]'s header); the
       law mints at some [f] and this leaf, which discards its post,
       hands that witness straight over. *)
    (* THE MINT ALREADY NAMED THE PAYLOAD (app-echo.md, "SH-LINE RULING",
       R1): read's bundle is a wand from the depositing process's own exit
       payload, so nothing is re-keyed here any more -- the family the
       deposit came at IS at [ukn_pay N]. *)
    iDestruct "Hdepn" as (fdep) "[%Hfp Hdepn]".
    iExists fdep. rewrite Hfp.
    cbn [uvis_gen uvis_of_run].
    iSplitR; [ iFrame "Hmy" | ].
    iSplitL "Hdepn"; [ iExact "Hdepn" | ].
    iIntros (r M' pm' sz' fdv' cw' gn' cs' lz' secc') "%Hok %Hfdok %Hpiperow %Hcwrow %Hgnrow %Hpidrow %Hliverow %Hscrow %Hchrow _".
    (* THE LAZY BIT CROSSED THE TRAP UNCHANGED (lane LAZY-FLAG, L6).  The
       trapping key is at [false] -- the U tier's run is
       ([UexecRet.ukcq]) -- and every row but sbrk's is the equation
       ([UsysMemOk.usys_mem_ok_lazy]), so the resume key is at [false] too
       and the close below is at the run's own bit. *)
    assert (Hlzq : lz' = false)
      by (refine (usys_mem_ok_lazy _ _ _ _ _ _ _ _ _ _ _ _ Hok);
          first [ assumption | vm_compute; discriminate ]).
    subst lz'.
    (* ...AND SO DID THE MASK: not seccomp's number, so the row is the
       equation ([UsysMemOk.usys_secc_ok_quiet]), and the resume key is at
       the full mask [urun] is keyed at *)
    pose proof (fun Hne => usys_secc_ok_quiet _ _ _ _ _ Hne Hscrow) as Hscq.
    specialize (Hscq ltac:(usys_range)).
    cbn [uvis_secc uvis_of_run] in Hscq. subst secc'.
    (* THE CWD CROSSED THE TRAP UNCHANGED -- chdir is the one row that moves
       it, and this is not it -- so the engine's half is re-keyed onto the
       view the process resumes at and the program's half never moved. *)
    assert (Hcw : cw' = cw)
      by (refine (usys_cwd_ok_quiet _ _ _ _ _ Hcwrow); vm_compute; discriminate).
    iDestruct (ucwd_auth_quiet N cw cw' Hcw with "Hcwda") as "Hcwda".
    (* ...AND SO DID THE GENERATION AND THE CHILDREN SET: no entry
       re-incarnates its caller, and this lane's children row is the
       identity at every number ([UsysMemOk] SS2e/SS2f).  Both are
       substituted rather than re-keyed -- the generation has no
       authority beside it, and the children authority is already at
       the set the process resumes at. *)
    assert (Hgn : gn' = gn) by exact (usys_gen_ok_quiet _ _ _ Hgnrow).
    assert (Hch : cs' = cs) by exact (usys_ch_ok_quiet _ _ _ _ Hchrow).
    subst gn' cs'.
    destruct (usys_mem_ok_quiet USYS_close _ r _ _ _ _ _ _ _ _
                ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)
                ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) Hok)
      as [-> [-> ->]].
    cbn [uvis_M uvis_perm uvis_fd uvis_of_run] in Hfdok |- *.
    destruct (uk_close_row m pc fd st fdv fdv' r Harg Hi Hne Hfdok)
      as [Hr0 ->].
    iApply uslot_bupd.
    iMod (ufd_close_hi (ukn_fd N) fdv fd st with "Hufd Hh") as "Hufd".
    iModIntro.
    rewrite (uslot_bump_run m pc M M pm pm sz sz fdv
               (<[fd := FdClosed]> fdv) cw cw' gn gn cs cs pidv false false secc_all secc_all r Hx0 Hal4).
    (* ...and close installs [FdClosed], which is not a pipe row *)
    iDestruct (urun_rows_insert N fdv fd FdClosed fdst_nopipe_closed
                 with "Hnpx") as "#Hnpo".
    iApply ukcq_ukc.
    iApply (urun_close_upd _ _ _ m (mword_of_int 10) _ _ _ _ _ _ _ _ _
              ltac:(unfold unot_sp; vm_compute; discriminate)
              with "Hheap Hstk Hufd Hcwda Hcha Hmy Hdep Hnpo").
    iIntros (h') "Hrun". iApply ("Hcont" $! h' r with "[%] Hrun"). exact Hr0.
  Qed.

  (* ...and the STANDARD-STREAM close, which spends the ledger's own entry
     and hands it back at [FdClosed]. *)
  Lemma wp_uk_ecall_close_std (N : uk_names Σ) (h : CpuId) (m : regfile)
      (pc : mword 64) (l : list fdstate) (fd : nat) (st : fdstate)
      (avail : nat) :
    usysno m = USYS_close ->
    bv_signed (trunc32 (m !!! Regidx (mword_of_int 10))) = Z.of_nat fd ->
    (fd < NSTD)%nat -> l !! fd = Some st -> st <> FdClosed ->
    is_aligned_vaddr (Virtaddr (add_vec_int pc 4)) 2 = true ->
    uinstr_is (ukn_t N) pc false (ECALL tt) -∗
    urun N h m pc avail -∗
    (* the close row, at the state the LEDGER names -- see the sibling leaf *)
    udepw_cl N m pc st -∗
    ustd (ukn_fd N) l -∗
    (∀ (h' : CpuId) (r : mword 64),
       ⌜uint r = 0⌝ -∗
       ustd (ukn_fd N) (<[fd := FdClosed]> l) -∗
       urun N h' (<[Regidx (mword_of_int 10) := r]> m)
         (add_vec_int pc 4) avail -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Hn Harg Hs Hkl Hne Hal4.
    iIntros "#Hi Hrun Hsb Hstd Hcont".
    iDestruct "Hrun" as (xi C pt Rfd Rut sz M pm fdv cw gn cs pidv) "(%Hlo & %Hpm & %Hlzf & %HRut & Hheap & Hstk & Hufd & Hcwda & Hcha & #Hmy & #Hdep & #Hnpx & Hb)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iDestruct (ustd_agree with "Hufd Hstd") as %Hst.
    assert (Hi : fdv !! fd = Some st).
    { rewrite <- (lookup_take fdv NSTD fd Hs). by rewrite Hst. }
    assert (Hfdlt : (fd < NOFILE)%nat) by (unfold NSTD, NOFILE in *; lia).
    iMod (udepw_cl_mint N m pc st M pm sz fdv cw gn cs pidv
                (uk_fd_st_of_key _ fdv fd st Harg Hfdlt Hi)
                with "Hdep Hmy Hsb Hheap Hufd") as "(Hheap & Hufd & Hdepn)".
    iDestruct (uvb_x0 with "Hb") as "[%Hx0 Hb]".
    iApply (UkStep.wp_uk_ecall C pt Rfd Rut pm sz Hlo Hpm HRut Hlzf M m pc fdv cw gn cs pidv Hui
              (fun (s : mstate)
                   (Hp : register_lookup cur_privilege s.(sregs) = User)
                   (Hc : register_lookup (R_bitvector_64 PC) s.(sregs) = pc) =>
                 UserExecFacts.goodmb_execute_ECALL_U UserFrame.Du_r UserFrame.Du_w
                   s pc ltac:(vm_compute; reflexivity)
                   ltac:(vm_compute; reflexivity) Hp Hc)
              with "Hb Hmy").
    rewrite (uexec_ret_ecall _ _ eq_refl).
    assert (Hnum : uvis_num (uvis_of_run m pc M pm sz fdv cw gn cs pidv false secc_all) = USYS_close).
    { assert (Hraw : usys_num (uvis_tf (uvis_of_run m pc M pm sz fdv cw gn cs pidv false secc_all)) = USYS_close)
        by (cbn [uvis_tf uvis_of_run]; rewrite tf_of_num; exact Hn).
      rewrite uvis_num_full0; [ exact Hraw | reflexivity | rewrite Hraw; usys_range ]. }
    (* the PAYMENT's guard IS the deposit's own, so it is opened BEFORE the
       number is rewritten and the destructs below then reduce both copies
       at once *)
    rewrite /uexec_pay_dep /upay_at.
    pose proof Hnum as Hnume. unfold uvis_num in Hnume. rewrite ?Hnum ?Hnume. cbv zeta.
    destruct (decide (uecall_scause = uecall_scause)) as [_ | Hpne];
      [ | exfalso; exact (Hpne eq_refl) ].
    destruct (decide (USYS_close = USYS_exit)) as [He | _];
      [ exfalso; vm_compute in He; discriminate | ].
    destruct (decide (USYS_close = USYS_fork)) as [He | _];
      [ exfalso; vm_compute in He; discriminate | ].
    (* the arm binds the deposit's FAMILIES ([UexecSG.v]'s header); the
       law mints at some [f] and this leaf, which discards its post,
       hands that witness straight over. *)
    (* THE MINT ALREADY NAMED THE PAYLOAD (app-echo.md, "SH-LINE RULING",
       R1): read's bundle is a wand from the depositing process's own exit
       payload, so nothing is re-keyed here any more -- the family the
       deposit came at IS at [ukn_pay N]. *)
    iDestruct "Hdepn" as (fdep) "[%Hfp Hdepn]".
    iExists fdep. rewrite Hfp.
    cbn [uvis_gen uvis_of_run].
    iSplitR; [ iFrame "Hmy" | ].
    iSplitL "Hdepn"; [ iExact "Hdepn" | ].
    iIntros (r M' pm' sz' fdv' cw' gn' cs' lz' secc') "%Hok %Hfdok %Hpiperow %Hcwrow %Hgnrow %Hpidrow %Hliverow %Hscrow %Hchrow _".
    (* THE LAZY BIT CROSSED THE TRAP UNCHANGED (lane LAZY-FLAG, L6).  The
       trapping key is at [false] -- the U tier's run is
       ([UexecRet.ukcq]) -- and every row but sbrk's is the equation
       ([UsysMemOk.usys_mem_ok_lazy]), so the resume key is at [false] too
       and the close below is at the run's own bit. *)
    assert (Hlzq : lz' = false)
      by (refine (usys_mem_ok_lazy _ _ _ _ _ _ _ _ _ _ _ _ Hok);
          first [ assumption | vm_compute; discriminate ]).
    subst lz'.
    (* ...AND SO DID THE MASK: not seccomp's number, so the row is the
       equation ([UsysMemOk.usys_secc_ok_quiet]), and the resume key is at
       the full mask [urun] is keyed at *)
    pose proof (fun Hne => usys_secc_ok_quiet _ _ _ _ _ Hne Hscrow) as Hscq.
    specialize (Hscq ltac:(usys_range)).
    cbn [uvis_secc uvis_of_run] in Hscq. subst secc'.
    (* THE CWD CROSSED THE TRAP UNCHANGED -- chdir is the one row that moves
       it, and this is not it -- so the engine's half is re-keyed onto the
       view the process resumes at and the program's half never moved. *)
    assert (Hcw : cw' = cw)
      by (refine (usys_cwd_ok_quiet _ _ _ _ _ Hcwrow); vm_compute; discriminate).
    iDestruct (ucwd_auth_quiet N cw cw' Hcw with "Hcwda") as "Hcwda".
    (* ...AND SO DID THE GENERATION AND THE CHILDREN SET: no entry
       re-incarnates its caller, and this lane's children row is the
       identity at every number ([UsysMemOk] SS2e/SS2f).  Both are
       substituted rather than re-keyed -- the generation has no
       authority beside it, and the children authority is already at
       the set the process resumes at. *)
    assert (Hgn : gn' = gn) by exact (usys_gen_ok_quiet _ _ _ Hgnrow).
    assert (Hch : cs' = cs) by exact (usys_ch_ok_quiet _ _ _ _ Hchrow).
    subst gn' cs'.
    destruct (usys_mem_ok_quiet USYS_close _ r _ _ _ _ _ _ _ _
                ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)
                ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) Hok)
      as [-> [-> ->]].
    cbn [uvis_M uvis_perm uvis_fd uvis_of_run] in Hfdok |- *.
    destruct (uk_close_row m pc fd st fdv fdv' r Harg Hi Hne Hfdok) as [Hr0 ->].
    iApply uslot_bupd.
    iMod (ufd_close_std (ukn_fd N) fdv l fd st Hs Hkl with "Hufd Hstd") as "[Hufd Hstd]".
    iModIntro.
    rewrite (uslot_bump_run m pc M M pm pm sz sz fdv
               (<[fd := FdClosed]> fdv) cw cw' gn gn cs cs pidv false false secc_all secc_all r Hx0 Hal4).
    (* ...and close installs [FdClosed], which is not a pipe row *)
    iDestruct (urun_rows_insert N fdv fd FdClosed fdst_nopipe_closed
                 with "Hnpx") as "#Hnpo".
    iApply ukcq_ukc.
    iApply (urun_close_upd _ _ _ m (mword_of_int 10) _ _ _ _ _ _ _ _ _
              ltac:(unfold unot_sp; vm_compute; discriminate)
              with "Hheap Hstk Hufd Hcwda Hcha Hmy Hdep Hnpo").
    iIntros (h') "Hrun". iApply ("Hcont" $! h' r with "[%] Hstd Hrun"). exact Hr0.
  Qed.

  (* ------------------------------------------------------------------- *)
  (* ecall, at exit.  The process never comes back, so it owes NOTHING --  *)
  (* not even a continuation.  This is the only leaf with no successor.    *)
  (* ------------------------------------------------------------------- *)

  (* ------------------------------------------------------------------- *)
  (* ecall, at read -- RETIRED INTO THE WINDOW FORM (lane RD-3).           *)
  (*                                                                      *)
  (* [wp_uk_ecall_read] used to stand HERE, as a walk of its own: the      *)
  (* exact non-negative count, the buffer at an address the caller spells  *)
  (* as a [Z], and the whole run back at unconstrained contents.  It is    *)
  (* now a COROLLARY of [wp_uk_ecall_read_win] below -- the merge that     *)
  (* leaf's own header asked for -- and it keeps its name and its exact    *)
  (* statement, so every caller ([UkCat]'s read stub) is untouched.  What  *)
  (* was retired is the hundred-and-thirty-line walk, which said nothing   *)
  (* the window leaf's does not say better.                                *)
  (* ------------------------------------------------------------------- *)

  (* ------------------------------------------------------------------- *)
  (* EXEC'S FAILURE ARM.  A successful exec never returns to this WP at all *)
  (* -- the new program's is minted by exec from the new trapframe and     *)
  (* image -- so the only arm that comes back is the failure, and the row  *)
  (* says so outright: -1, and not one byte moved.                         *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_uk_ecall_exec (N : uk_names Σ) (h : CpuId) (m : regfile)
      (pc : mword 64) (avail : nat) :
    usysno m = USYS_exec ->
    is_aligned_vaddr (Virtaddr (add_vec_int pc 4)) 2 = true ->
    uinstr_is (ukn_t N) pc false (ECALL tt) -∗
    urun N h m pc avail -∗
    udepw N m pc USYS_exec -∗
    (∀ h' : CpuId,
       urun N h'
         (<[Regidx (mword_of_int 10) := (mword_of_int (-1) : mword 64)]> m)
         (add_vec_int pc 4) avail -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Hn Hal4.
    iIntros "#Hi Hrun Hsb Hcont".
    iDestruct "Hrun" as (xi C pt Rfd Rut sz M pm fdv cw gn cs pidv) "(%Hlo & %Hpm & %Hlzf & %HRut & Hheap & Hstk & Hufd & Hcwda & Hcha & #Hmy & #Hdep & #Hnpx & Hb)".
    iMod (udepw_mint N m pc _ M pm _ fdv cw gn cs pidv
                with "Hdep Hmy Hsb Hheap Hufd") as "(Hheap & Hufd & Hdepn)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iDestruct (uvb_x0 with "Hb") as "[%Hx0 Hb]".
    iApply (UkStep.wp_uk_ecall C pt Rfd Rut pm sz Hlo Hpm HRut Hlzf M m pc fdv cw gn cs pidv Hui
              (fun (s : mstate)
                   (Hp : register_lookup cur_privilege s.(sregs) = User)
                   (Hc : register_lookup (R_bitvector_64 PC) s.(sregs) = pc) =>
                 UserExecFacts.goodmb_execute_ECALL_U UserFrame.Du_r UserFrame.Du_w
                   s pc ltac:(vm_compute; reflexivity)
                   ltac:(vm_compute; reflexivity) Hp Hc)
              with "Hb Hmy").
    rewrite (uexec_ret_ecall _ _ eq_refl).
    assert (Hnum : uvis_num (uvis_of_run m pc M pm sz fdv cw gn cs pidv false secc_all) = USYS_exec).
    { assert (Hraw : usys_num (uvis_tf (uvis_of_run m pc M pm sz fdv cw gn cs pidv false secc_all)) = USYS_exec)
        by (cbn [uvis_tf uvis_of_run]; rewrite tf_of_num; exact Hn).
      rewrite uvis_num_full0; [ exact Hraw | reflexivity | rewrite Hraw; usys_range ]. }
    (* the PAYMENT's guard IS the deposit's own, so it is opened BEFORE the
       number is rewritten and the destructs below then reduce both copies
       at once *)
    rewrite /uexec_pay_dep /upay_at.
    pose proof Hnum as Hnume. unfold uvis_num in Hnume. rewrite ?Hnum ?Hnume. cbv zeta.
    destruct (decide (uecall_scause = uecall_scause)) as [_ | Hpne];
      [ | exfalso; exact (Hpne eq_refl) ].
    destruct (decide (USYS_exec = USYS_exit)) as [He | _];
      [ exfalso; unfold USYS_exec, USYS_exit in He; discriminate He | ].
    destruct (decide (USYS_exec = USYS_fork)) as [He | _];
      [ exfalso; unfold USYS_exec, USYS_fork in He; discriminate He | ].
    (* the arm binds the deposit's FAMILIES ([UexecSG.v]'s header); the
       law mints at some [f] and this leaf, which discards its post,
       hands that witness straight over. *)
    (* THE MINT ALREADY NAMED THE PAYLOAD (app-echo.md, "SH-LINE RULING",
       R1): read's bundle is a wand from the depositing process's own exit
       payload, so nothing is re-keyed here any more -- the family the
       deposit came at IS at [ukn_pay N]. *)
    iDestruct "Hdepn" as (fdep) "[%Hfp Hdepn]".
    iExists fdep. rewrite Hfp.
    cbn [uvis_gen uvis_of_run].
    iSplitR; [ iFrame "Hmy" | ].
    iSplitL "Hdepn"; [ iExact "Hdepn" | ].
    iIntros (r M' pm' sz' fdv' cw' gn' cs' lz' secc') "%Hok %Hfdok %Hpiperow %Hcwrow %Hgnrow %Hpidrow %Hliverow %Hscrow %Hchrow _".
    (* THE LAZY BIT CROSSED THE TRAP UNCHANGED (lane LAZY-FLAG, L6).  The
       trapping key is at [false] -- the U tier's run is
       ([UexecRet.ukcq]) -- and every row but sbrk's is the equation
       ([UsysMemOk.usys_mem_ok_lazy]), so the resume key is at [false] too
       and the close below is at the run's own bit. *)
    assert (Hlzq : lz' = false)
      by (refine (usys_mem_ok_lazy _ _ _ _ _ _ _ _ _ _ _ _ Hok);
          first [ assumption | vm_compute; discriminate ]).
    subst lz'.
    (* ...AND SO DID THE MASK: not seccomp's number, so the row is the
       equation ([UsysMemOk.usys_secc_ok_quiet]), and the resume key is at
       the full mask [urun] is keyed at *)
    pose proof (fun Hne => usys_secc_ok_quiet _ _ _ _ _ Hne Hscrow) as Hscq.
    specialize (Hscq ltac:(usys_range)).
    cbn [uvis_secc uvis_of_run] in Hscq. subst secc'.
    (* THE CWD CROSSED THE TRAP UNCHANGED -- chdir is the one row that moves
       it, and this is not it -- so the engine's half is re-keyed onto the
       view the process resumes at and the program's half never moved. *)
    assert (Hcw : cw' = cw)
      by (refine (usys_cwd_ok_quiet _ _ _ _ _ Hcwrow); vm_compute; discriminate).
    iDestruct (ucwd_auth_quiet N cw cw' Hcw with "Hcwda") as "Hcwda".
    (* ...AND SO DID THE GENERATION AND THE CHILDREN SET: no entry
       re-incarnates its caller, and this lane's children row is the
       identity at every number ([UsysMemOk] SS2e/SS2f).  Both are
       substituted rather than re-keyed -- the generation has no
       authority beside it, and the children authority is already at
       the set the process resumes at. *)
    assert (Hgn : gn' = gn) by exact (usys_gen_ok_quiet _ _ _ Hgnrow).
    assert (Hch : cs' = cs) by exact (usys_ch_ok_quiet _ _ _ _ Hchrow).
    subst gn' cs'.
    destruct (usys_mem_ok_exec_row USYS_exec _ r _ _ _ _ _ _ _ _ eq_refl Hok)
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
    rewrite (uslot_bump_run m pc M M pm pm sz sz fdv fdv cw cw' gn gn cs cs pidv false false secc_all secc_all
               (mword_of_int (-1) : mword 64) Hx0 Hal4).
    iApply ukcq_ukc.
    iApply (urun_close_upd _ _ _ m (mword_of_int 10) _ _ _ _ _ _ _ _ _
              ltac:(unfold unot_sp; vm_compute; discriminate) with "Hheap Hstk Hufd Hcwda Hcha Hmy Hdep Hnpx").
    iIntros (h') "Hrun".
    iApply ("Hcont" $! h' with "Hrun").
  Qed.

  (* ------------------------------------------------------------------- *)
  (* EXEC AT THE PROCESS'S OWN WORKING DIRECTORY.                          *)
  (*                                                                      *)
  (* The leaf above takes a [udepw], which answers at whatever [cw] the    *)
  (* run turns out to be at.  A caller whose exec bundle is a claim about  *)
  (* a PATH cannot supply one: a path names a file only relative to the    *)
  (* directory it is resolved from, so what such a caller has is the       *)
  (* bundle at every key whose cwd is the ONE inum its process is at.      *)
  (*                                                                      *)
  (* THAT IS NOT A [udepw] AND CANNOT BE MADE INTO ONE.  [udepw] binds     *)
  (* [cw] under its own ∀, and the only thing that pins it is agreement    *)
  (* against the half [urun] carries -- which arrives inside the closure,  *)
  (* where the program's half would have to be spent to reach it.  So the  *)
  (* agreement happens HERE instead: this leaf has destructed [urun], it   *)
  (* holds both halves for the length of one step, and it hands the        *)
  (* program's back on the failure arm.  A program that execs in a loop    *)
  (* (sh does) still knows where it is on the next turn.                   *)
  (*                                                                       *)
  (* WHAT IT TAKES IS [UkRun.udepw_at], NOT A BARE BUNDLE FAMILY: the      *)
  (* deposit is LENT the heap and the fd authority and hands them back     *)
  (* beside the bundle, because a PINNED bundle's own premises --          *)
  (* [exec_path_of M pv pl] off the program's rodata through               *)
  (* [UserHeap.uheap_text], and [length sts = NOFILE] /                    *)
  (* [fd_lowest_closed sts = None] off the descriptor list -- are facts    *)
  (* about the very key the bundle is stated at.  A supplier that owes     *)
  (* nothing ignores the loan ([UkRun.udepw_at_of_bundle]).                *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_uk_ecall_exec_at_cwd (N : uk_names Σ) (h : CpuId) (m : regfile)
      (pc : mword 64) (avail : nat) (c : Z) :
    usysno m = USYS_exec ->
    is_aligned_vaddr (Virtaddr (add_vec_int pc 4)) 2 = true ->
    uinstr_is (ukn_t N) pc false (ECALL tt) -∗
    urun N h m pc avail -∗
    (* the program's half of its working directory... *)
    UserCwd.ucwd (ukn_cwd N) c -∗
    (* ...and the deposit at every key whose cwd is that one inum.
       AT THE REFUNDING FORM (lane KILL-PAY, K4(a), ruling R-A): an exec
       that FAILS comes back, and the process's -1 payload no longer rides
       [UkRun.urun]'s row, so what it spent into this deposit is the only
       thing it has left to pay its own [exit] with.  [UkRun.udepw_at_ref]
       is [udepw_at] at exec plus the one consequence a leaf can state --
       the refund pays THIS record's exit at the kill status. *)
    udepw_at_ref N m pc c -∗
    (∀ h' : CpuId,
       UserCwd.ucwd (ukn_cwd N) c -∗
       (* ...AND THE REFUND, which is what an exec-failure arm exits on *)
       ukn_pay N (-1) -∗
       urun N h'
         (<[Regidx (mword_of_int 10) := (mword_of_int (-1) : mword 64)]> m)
         (add_vec_int pc 4) avail -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Hn Hal4.
    iIntros "#Hi Hrun Hcwd Hsb Hcont".
    iDestruct "Hrun" as (xi C pt Rfd Rut sz M pm fdv cw gn cs pidv) "(%Hlo & %Hpm & %Hlzf & %HRut & Hheap & Hstk & Hufd & Hcwda & Hcha & #Hmy & #Hdep & #Hnpx & Hb)".
    (* the whole point of the leaf: the key's cwd IS the one the caller's
       bundle is stated at *)
    iDestruct (ucwd_agree with "Hcwda Hcwd") as %->.
    iDestruct ("Hsb" $! M pm sz fdv gn cs pidv with "Hmy Hnpx Hheap Hufd")
      as "(Hheap & Hufd & Hdepn)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iDestruct (uvb_x0 with "Hb") as "[%Hx0 Hb]".
    iApply (UkStep.wp_uk_ecall C pt Rfd Rut pm sz Hlo Hpm HRut Hlzf M m pc fdv c gn cs pidv Hui
              (fun (s : mstate)
                   (Hp : register_lookup cur_privilege s.(sregs) = User)
                   (Hc : register_lookup (R_bitvector_64 PC) s.(sregs) = pc) =>
                 UserExecFacts.goodmb_execute_ECALL_U UserFrame.Du_r UserFrame.Du_w
                   s pc ltac:(vm_compute; reflexivity)
                   ltac:(vm_compute; reflexivity) Hp Hc)
              with "Hb Hmy").
    rewrite (uexec_ret_ecall _ _ eq_refl).
    assert (Hnum : uvis_num (uvis_of_run m pc M pm sz fdv c gn cs pidv false secc_all) = USYS_exec).
    { assert (Hraw : usys_num (uvis_tf (uvis_of_run m pc M pm sz fdv c gn cs pidv false secc_all)) = USYS_exec)
        by (cbn [uvis_tf uvis_of_run]; rewrite tf_of_num; exact Hn).
      rewrite uvis_num_full0; [ exact Hraw | reflexivity | rewrite Hraw; usys_range ]. }
    (* the PAYMENT's guard IS the deposit's own, so it is opened BEFORE the
       number is rewritten and the destructs below then reduce both copies
       at once *)
    rewrite /uexec_pay_dep /upay_at.
    pose proof Hnum as Hnume. unfold uvis_num in Hnume. rewrite ?Hnum ?Hnume. cbv zeta.
    destruct (decide (uecall_scause = uecall_scause)) as [_ | Hpne];
      [ | exfalso; exact (Hpne eq_refl) ].
    destruct (decide (USYS_exec = USYS_exit)) as [He | _];
      [ exfalso; unfold USYS_exec, USYS_exit in He; discriminate He | ].
    destruct (decide (USYS_exec = USYS_fork)) as [He | _];
      [ exfalso; unfold USYS_exec, USYS_fork in He; discriminate He | ].
    (* THE MINT ALREADY NAMED THE PAYLOAD (app-echo.md, "SH-LINE RULING",
       R1): read's bundle is a wand from the depositing process's own exit
       payload, so nothing is re-keyed here any more -- the family the
       deposit came at IS at [ukn_pay N]. *)
    iDestruct "Hdepn" as (fdep) "(%Hfp & #Href & Hdepn)".
    iExists fdep. rewrite Hfp.
    cbn [uvis_gen uvis_of_run].
    iSplitR; [ iFrame "Hmy" | ].
    iSplitL "Hdepn"; [ iExact "Hdepn" | ].
    (* THE POST AT exec IS THE REFUND (lane KILL-PAY, K4(a), R-A): it used
       to be [emp] and is a wand from "the answer was -1" now
       ([UexecSG.spost_at_exec]), which is exactly the branch this leaf is
       on -- a successful exec never resumes here. *)
    iIntros (r M' pm' sz' fdv' cw' gn' cs' lz' secc') "%Hok %Hfdok %Hpiperow %Hcwrow %Hgnrow %Hpidrow %Hliverow %Hscrow %Hchrow Hsp".
    (* THE LAZY BIT CROSSED THE TRAP UNCHANGED (lane LAZY-FLAG, L6).  The
       trapping key is at [false] -- the U tier's run is
       ([UexecRet.ukcq]) -- and every row but sbrk's is the equation
       ([UsysMemOk.usys_mem_ok_lazy]), so the resume key is at [false] too
       and the close below is at the run's own bit. *)
    assert (Hlzq : lz' = false)
      by (refine (usys_mem_ok_lazy _ _ _ _ _ _ _ _ _ _ _ _ Hok);
          first [ assumption | vm_compute; discriminate ]).
    subst lz'.
    (* ...AND SO DID THE MASK: not seccomp's number, so the row is the
       equation ([UsysMemOk.usys_secc_ok_quiet]), and the resume key is at
       the full mask [urun] is keyed at *)
    pose proof (fun Hne => usys_secc_ok_quiet _ _ _ _ _ Hne Hscrow) as Hscq.
    specialize (Hscq ltac:(usys_range)).
    cbn [uvis_secc uvis_of_run] in Hscq. subst secc'.
    assert (Hcw : cw' = c)
      by (refine (usys_cwd_ok_quiet _ _ _ _ _ Hcwrow); vm_compute; discriminate).
    iDestruct (ucwd_auth_quiet N c cw' Hcw with "Hcwda") as "Hcwda".
    (* ...AND SO DID THE GENERATION AND THE CHILDREN SET: no entry
       re-incarnates its caller, and this lane's children row is the
       identity at every number ([UsysMemOk] SS2e/SS2f).  Both are
       substituted rather than re-keyed -- the generation has no
       authority beside it, and the children authority is already at
       the set the process resumes at. *)
    assert (Hgn : gn' = gn) by exact (usys_gen_ok_quiet _ _ _ Hgnrow).
    assert (Hch : cs' = cs) by exact (usys_ch_ok_quiet _ _ _ _ Hchrow).
    subst gn' cs'.
    destruct (usys_mem_ok_exec_row USYS_exec _ r _ _ _ _ _ _ _ _ eq_refl Hok)
      as [-> [-> [-> ->]]].
    (* the refund, cashed at the answer this arm IS at, and turned into
       what this record's own exit owes (lane KILL-PAY, K4(a), R-A) *)
    iEval (rewrite spost_at_exec) in "Hsp".
    iDestruct ("Hsp" with "[//]") as "Hrf".
    iDestruct ("Href" with "Hrf") as "Hpayret".
    cbn [uvis_M uvis_perm uvis_of_run].
    assert (Hview : fdv' = fdv).
    { refine (usys_fd_ok_quiet _ _ _ _ _ _ _ _ _ Hfdok);
        vm_compute; discriminate. }
    subst fdv'.
    rewrite (uslot_bump_run m pc M M pm pm sz sz fdv fdv c cw' gn gn cs cs pidv false false secc_all secc_all
               (mword_of_int (-1) : mword 64) Hx0 Hal4).
    iApply ukcq_ukc.
    iApply (urun_close_upd _ _ _ m (mword_of_int 10) _ _ _ _ _ _ _ _ _
              ltac:(unfold unot_sp; vm_compute; discriminate) with "Hheap Hstk Hufd Hcwda Hcha Hmy Hdep Hnpx").
    iIntros (h') "Hrun".
    iApply ("Hcont" $! h' with "Hcwd Hpayret Hrun").
  Qed.

  (* =================================================================== *)
  (* KILL, AT THE TIER IT IS AVAILABLE AT (lane RD-8).                     *)
  (*                                                                       *)
  (* THE LEAF IS AN INSTANCE AND NOT A WALK, and that is the whole report:  *)
  (* kill moves no byte, no descriptor, no cwd and no children reading, so  *)
  (* [wp_uk_ecall_quiet] already covers its walk exactly.  What it does NOT *)
  (* cover -- and what the lane set out to add -- is an ANSWER: that the    *)
  (* target incarnation is now owed its death payment                      *)
  (* ([ChildTok.kill_owed]).  That answer is not available, and the reason  *)
  (* is precise enough to be worth naming here.                            *)
  (*                                                                       *)
  (* WHY NOT.  [SchedCtx.kill_paid]'s row is keyed at THE SLOT'S OWN pid    *)
  (* CELL, and [SlotGen.pid_reg_agree] is exactly the step that turns a     *)
  (* killer's registration share into the target's generation -- so on the  *)
  (* arm where kkill's [beq] MATCHED, the deposit could be placed.  The gap *)
  (* is the other direction: nothing kkill can reach says the scan matches  *)
  (* AT ALL.  "Every registered pid is nonzero and is held by some slot" is *)
  (* a real fact in this tree ([SlotGen.pid_reg_dom]) -- but it lives in    *)
  (* <pid_lock>'s payload ([PidLock.nextpid_res_at]) and kkill never takes  *)
  (* <pid_lock>.  [SchedCtx.procs_inv], which is all kkill gets, is the 64  *)
  (* locks and the 64 kstacks and nothing about pids.  So a killer holding  *)
  (* [SlotGen.pid_reg pid _ gn] still cannot rule out the -1 return, and a  *)
  (* post that says "rv = 0 and the row moved" is unprovable.               *)
  (*                                                                       *)
  (* WHAT WOULD CLOSE IT: the pid register's domain fact moved out of       *)
  (* <pid_lock>'s payload and into something kkill holds.  See              *)
  (* claude-notes/design/user-proc.md.                                      *)
  (*                                                                       *)
  (* SO THE LEAF BELOW IS THE TAINT-SHAPED KILL: the program pays the       *)
  (* application's kill price through its own deposit at number 6           *)
  (* ([RiscvPtsto.app_taint], which for echo IS the taint) and gets   *)
  (* back a run and a number it knows nothing about.  It is named rather    *)
  (* than left implicit because a caller should not have to rediscover      *)
  (* which of [wp_uk_ecall_quiet]'s eleven side conditions kill discharges. *)
  (* =================================================================== *)
  (* HOME: [USYS_kill] belongs beside the other twelve in UsysMemOk.v; it
     is here because no row of that file's tables mentions it yet -- kill
     is quiet in every one of them. *)
  Definition USYS_kill : Z := 6.

  Lemma wp_uk_ecall_kill (N : uk_names Σ) (h : CpuId) (m : regfile)
      (pc : mword 64) (avail : nat) :
    usysno m = USYS_kill ->
    is_aligned_vaddr (Virtaddr (add_vec_int pc 4)) 2 = true ->
    uinstr_is (ukn_t N) pc false (ECALL tt) -∗
    urun N h m pc avail -∗
    (* THE PRICE IS IN HERE.  Number 6's row of the process's own bundle is
       what carries [app_taint] down to kkill ([SpecSysKill]'s
       premise); a program with nothing to pay it with cannot mint this
       deposit at this number. *)
    udepw N m pc USYS_kill -∗
    (∀ (h' : CpuId) (r : mword 64),
       urun N h' (<[Regidx (mword_of_int 10) := r]> m) (add_vec_int pc 4) avail -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Hn Hal4. iIntros "#Hi Hrun Hsb Hcont".
    iApply (wp_uk_ecall_quiet N h m pc USYS_kill avail Hn
              ltac:(unfold USYS_kill, USYS_exit; lia)
              ltac:(unfold USYS_kill, USYS_fork; lia)
              ltac:(unfold USYS_kill, USYS_exec; lia)
              ltac:(unfold USYS_kill, USYS_sbrk; lia)
              ltac:(unfold USYS_kill, USYS_wait; lia)
              ltac:(unfold USYS_kill, USYS_pipe; lia)
              ltac:(unfold USYS_kill, USYS_read; lia)
              ltac:(unfold USYS_kill, USYS_fstat; lia)
              ltac:(unfold USYS_kill, USYS_close; lia)
              ltac:(unfold USYS_kill, USYS_dup; lia)
              ltac:(unfold USYS_kill, USYS_open; lia)
              ltac:(unfold USYS_kill, USYS_chdir; lia)
              ltac:(unfold USYS_kill; lia)
              ltac:(unfold USYS_kill, USYS_seccomp; lia)
              Hal4 with "Hi Hrun Hsb Hcont").
  Qed.


  (* ------------------------------------------------------------------- *)
  (* WAIT AT A NULL STATUS POINTER.  The kernel's own [addr != 0] test     *)
  (* means nothing is copied out, so the heap the caller owns comes back   *)
  (* untouched and the leaf can hand the SAME run on -- exactly the quiet  *)
  (* row's shape.  This is the arm init and sh both take.                  *)
  (* ------------------------------------------------------------------- *)
  (* WAIT MOVES THE CALLER'S CHILDREN READING, so the leaf takes the
     program's half of it and hands it back at what the reap left -- the
     fork leaf's shape ([UkFork.wp_uk_ecall_fork]'s [Sc]).  The move itself
     is [UserChildren.uch_update] against the authority [urun] carries: the
     kernel's answer says what the set became ([UexecRet.uwait_ans]) and
     the two halves are moved together here, which is the only place both
     are in one hand.  THE ANSWER IS WHAT THE LEAF REPORTS, unopened: on
     its reaping arm it names the generation that left the set, hands over
     that child's ESCROW ([ChildTok.exit_tok] -- the payload its exit paid)
     and the pid uniqueness that makes the returned number identify it, so
     a program holding [ChildTok.child_tok] for a child it forked redeems
     the payload here ([ChildTok.gen_uniq_tok], then [ChildTok.gen_pay]). *)
  (* ...AND THE ROW A RESUMING CALLER PROVES ABOUT ITS OWN -1 (lane
     TRAP-ROWS-3, T4(c)).  A process that comes BACK here was not killed
     ([SpecUsertrap.ut_live_out]'s header), and at a null status pointer
     the copyout exit cannot fire either -- so the only -1 left is the
     childless one, and the reap-nothing arm does not move the reading.
     The caller therefore reads a -1 as ITS OWN SET IS EMPTY, which is
     what a program holding [ChildTok.child_tok] for a child it forked
     refutes.  This is the whole point of the row; the leaf below is the
     same call with the row dropped, for the callers that do not read it. *)
  (* ...AND THE ONE PLACE THE RUN'S PID IS LEGIBLE (lane TRAP-ROWS-4, B1b).
     The answer's reaping arm names the CALLER'S OWN pid
     ([UexecRet.uwait_ans_pid] at [uvis_pid W]), and the only party that
     can tie that number to anything is this leaf: [urun] carries the pid
     AUTHORITY ([UkRun.urun_ids]) and the program carries the fragment, and
     they meet here and nowhere else.  So the proof is written ONCE, over a
     READER the caller supplies -- a one-shot accessor on the authority,
     spent exactly where the run is open -- and the two leaves below are
     its two instances: [wp_uk_ecall_wait_null_live] at the trivial reader
     (its statement verbatim as it always was) and
     [wp_uk_ecall_wait_null_pid] at the program's own fragment. *)
  Lemma wp_uk_ecall_wait_null_gen (N : uk_names Σ) (h : CpuId) (m : regfile)
      (pc : mword 64) (avail : nat) (Sc : gset gname)
      (P : mword 32 -> iProp Σ) :
    usysno m = USYS_wait ->
    uint (m !!! Regidx (mword_of_int 10)) = 0 ->
    is_aligned_vaddr (Virtaddr (add_vec_int pc 4)) 2 = true ->
    uinstr_is (ukn_t N) pc false (ECALL tt) -∗
    urun N h m pc avail -∗
    udepw N m pc USYS_wait -∗
    uch (ukn_ch N) Sc -∗
    (∀ pidv : mword 32,
       UserChildren.upid_auth (ukn_pid N) (bv_unsigned pidv) -∗
       UserChildren.upid_auth (ukn_pid N) (bv_unsigned pidv) ∗ P pidv) -∗
    (∀ (h' : CpuId) (r : mword 64) (Sc' : gset gname) (pidv : mword 32),
       P pidv -∗
       ⌜r = (mword_of_int (-1) : mword 64) -> Sc' = (∅ : gset gname)⌝ -∗
       uwait_ans_pid r Sc Sc' pidv -∗
       urun N h' (<[Regidx (mword_of_int 10) := r]> m)
         (add_vec_int pc 4) avail -∗
       uch (ukn_ch N) Sc' -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Hn Hz Hal4.
    iIntros "#Hi Hrun Hsb Hch Hrd Hcont".
    iDestruct "Hrun" as (xi C pt Rfd Rut sz M pm fdv cw gn cs pidv) "(%Hlo & %Hpm & %Hlzf & %HRut & Hheap & Hstk & Hufd & Hcwda & Hcha & #Hmy & #Hdep & #Hnpx & Hb)".
    (* THE READER IS SPENT HERE, where the run is open: the pid authority
       is LENT out of the identity conjunct and put straight back, so
       nothing else in the proof sees the difference. *)
    iDestruct (urun_ids_pid with "Hcha") as "[Hpida Hidsp]".
    iDestruct ("Hrd" $! pidv with "Hpida") as "[Hpida HP]".
    iDestruct ("Hidsp" with "Hpida") as "Hcha".
    iMod (udepw_mint N m pc _ M pm _ fdv cw gn cs pidv
                with "Hdep Hmy Hsb Hheap Hufd") as "(Hheap & Hufd & Hdepn)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iDestruct (uvb_x0 with "Hb") as "[%Hx0 Hb]".
    iApply (UkStep.wp_uk_ecall C pt Rfd Rut pm sz Hlo Hpm HRut Hlzf M m pc fdv cw gn cs pidv Hui
              (fun (s : mstate)
                   (Hp : register_lookup cur_privilege s.(sregs) = User)
                   (Hc : register_lookup (R_bitvector_64 PC) s.(sregs) = pc) =>
                 UserExecFacts.goodmb_execute_ECALL_U UserFrame.Du_r UserFrame.Du_w
                   s pc ltac:(vm_compute; reflexivity)
                   ltac:(vm_compute; reflexivity) Hp Hc)
              with "Hb Hmy").
    rewrite (uexec_ret_ecall _ _ eq_refl).
    assert (Hnum : uvis_num (uvis_of_run m pc M pm sz fdv cw gn cs pidv false secc_all) = USYS_wait).
    { assert (Hraw : usys_num (uvis_tf (uvis_of_run m pc M pm sz fdv cw gn cs pidv false secc_all)) = USYS_wait)
        by (cbn [uvis_tf uvis_of_run]; rewrite tf_of_num; exact Hn).
      rewrite uvis_num_full0; [ exact Hraw | reflexivity | rewrite Hraw; usys_range ]. }
    assert (Ha0 : uint (uvis_tf (uvis_of_run m pc M pm sz fdv cw gn cs pidv false secc_all) !!! tf_arg_idx 0) = 0).
    { cbn [uvis_tf uvis_of_run]. rewrite tf_of_arg0. exact Hz. }
    (* the PAYMENT's guard IS the deposit's own, so it is opened BEFORE the
       number is rewritten and the destructs below then reduce both copies
       at once *)
    rewrite /uexec_pay_dep /upay_at.
    pose proof Hnum as Hnume. unfold uvis_num in Hnume. rewrite ?Hnum ?Hnume. cbv zeta.
    destruct (decide (uecall_scause = uecall_scause)) as [_ | Hpne];
      [ | exfalso; exact (Hpne eq_refl) ].
    destruct (decide (USYS_wait = USYS_exit)) as [He | _];
      [ exfalso; unfold USYS_wait, USYS_exit in He; discriminate He | ].
    destruct (decide (USYS_wait = USYS_fork)) as [He | _];
      [ exfalso; unfold USYS_wait, USYS_fork in He; discriminate He | ].
    (* ...and THIS number is the one with an arm of its own beside fork's:
       the reap moved the reading, so the row the process gets back is the
       kernel's answer ([UexecRet.uexec_wait_F]). *)
    destruct (decide (USYS_wait = USYS_wait)) as [_ | Hwne];
      [ | exfalso; exact (Hwne eq_refl) ].
    (* the arm binds the deposit's FAMILIES ([UexecSG.v]'s header); the
       law mints at some [f] and this leaf, which discards its post,
       hands that witness straight over. *)
    (* THE MINT ALREADY NAMED THE PAYLOAD (app-echo.md, "SH-LINE RULING",
       R1): read's bundle is a wand from the depositing process's own exit
       payload, so nothing is re-keyed here any more -- the family the
       deposit came at IS at [ukn_pay N]. *)
    iDestruct "Hdepn" as (fdep) "[%Hfp Hdepn]".
    iExists fdep. rewrite Hfp.
    cbn [uvis_gen uvis_of_run].
    iSplitR; [ iFrame "Hmy" | ].
    iSplitL "Hdepn"; [ iExact "Hdepn" | ].
    iIntros (r M' pm' sz' fdv' cw' gn' cs' lz' secc') "%Hok %Hfdok %Hpiperow %Hcwrow %Hgnrow %Hpidrow %Hliverow %Hscrow Hans _".
    (* THE LAZY BIT CROSSED THE TRAP UNCHANGED (lane LAZY-FLAG, L6).  The
       trapping key is at [false] -- the U tier's run is
       ([UexecRet.ukcq]) -- and every row but sbrk's is the equation
       ([UsysMemOk.usys_mem_ok_lazy]), so the resume key is at [false] too
       and the close below is at the run's own bit. *)
    assert (Hlzq : lz' = false)
      by (refine (usys_mem_ok_lazy _ _ _ _ _ _ _ _ _ _ _ _ Hok);
          first [ assumption | vm_compute; discriminate ]).
    subst lz'.
    (* ...AND SO DID THE MASK: not seccomp's number, so the row is the
       equation ([UsysMemOk.usys_secc_ok_quiet]), and the resume key is at
       the full mask [urun] is keyed at *)
    pose proof (fun Hne => usys_secc_ok_quiet _ _ _ _ _ Hne Hscrow) as Hscq.
    specialize (Hscq ltac:(usys_range)).
    cbn [uvis_secc uvis_of_run] in Hscq. subst secc'.
    (* THE CWD CROSSED THE TRAP UNCHANGED -- chdir is the one row that moves
       it, and this is not it -- so the engine's half is re-keyed onto the
       view the process resumes at and the program's half never moved. *)
    assert (Hcw : cw' = cw)
      by (refine (usys_cwd_ok_quiet _ _ _ _ _ Hcwrow); vm_compute; discriminate).
    iDestruct (ucwd_auth_quiet N cw cw' Hcw with "Hcwda") as "Hcwda".
    (* ...AND SO DID THE GENERATION AND THE CHILDREN SET: no entry
       re-incarnates its caller, and this lane's children row is the
       identity at every number ([UsysMemOk] SS2e/SS2f).  Both are
       substituted rather than re-keyed -- the generation has no
       authority beside it, and the children authority is already at
       the set the process resumes at. *)
    assert (Hgn : gn' = gn) by exact (usys_gen_ok_quiet _ _ _ Hgnrow).
    subst gn'.
    (* THE SET MOVED, AND BOTH HALVES MOVE WITH IT.  The program's half came
       in with the call and the engine's rides [urun]; the answer says what
       the reap left, and [UserChildren.uch_update] is the one step that can
       take them there. *)
    (* the run's identity conjunct is the PAIR now ([UkRun.urun_ids]); the
       children half is what this leaf moves, the pid half rides through
       (lane TRAP-ROWS-4, B). *)
    iDestruct (urun_ids_ch with "Hcha") as "[Hcha Hidsback]".
    iDestruct (uch_agree with "Hcha Hch") as %<-.
    (* the goal here is the SLOT, not a [WP], so the update rides
       [UexecRet.uslot_bupd] -- the same door every other leaf that moves a
       ghost half in this position uses. *)
    iApply uslot_bupd.
    iMod (uch_update (ukn_ch N) cs cs cs' with "Hcha Hch") as "[Hcha Hch]".
    iDestruct ("Hidsback" $! cs' with "Hcha") as "Hcha".
    iModIntro.
    destruct (usys_mem_ok_wait_null USYS_wait _ r _ _ _ _ _ _ _ _
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
    rewrite (uslot_bump_run m pc M M pm pm sz sz fdv fdv cw cw' gn gn cs cs' pidv false false secc_all secc_all r Hx0 Hal4).
    iApply ukcq_ukc.
    iApply (urun_close_upd _ _ _ m (mword_of_int 10) _ _ _ _ _ _ _ _ _
              ltac:(unfold unot_sp; vm_compute; discriminate) with "Hheap Hstk Hufd Hcwda Hcha Hmy Hdep Hnpx").
    iIntros (h') "Hrun".
    (* the window rides with the answer now (lane RD-7); a caller that
       passed a NULL status pointer owns no buffer to read it out of, so
       this leaf drops it ([UexecRet.uwait_ans_pid_m_forget]).  The leaf
       that KEEPS it is [wp_uk_ecall_wait_status] below. *)
    iDestruct (uwait_ans_pid_m_forget with "Hans") as "Hans".
    iApply ("Hcont" $! h' r cs' pidv with "HP [%] Hans Hrun Hch").
    (* THE ROW, OFF THE RESUME'S OWN PURE CONJUNCT.  [Hliverow]'s wait
       clause is guarded on the null status pointer, which is this leaf's
       own premise ([Ha0]). *)
    exact (proj2 Hliverow eq_refl Ha0).
  Qed.

  (* THE ROW AS IT ALWAYS WAS, at the trivial reader: the pid is absorbed
     back into [UexecRet.uwait_ans] and the caller sees the statement it
     has always seen. *)
  Lemma wp_uk_ecall_wait_null_live (N : uk_names Σ) (h : CpuId) (m : regfile)
      (pc : mword 64) (avail : nat) (Sc : gset gname) :
    usysno m = USYS_wait ->
    uint (m !!! Regidx (mword_of_int 10)) = 0 ->
    is_aligned_vaddr (Virtaddr (add_vec_int pc 4)) 2 = true ->
    uinstr_is (ukn_t N) pc false (ECALL tt) -∗
    urun N h m pc avail -∗
    udepw N m pc USYS_wait -∗
    uch (ukn_ch N) Sc -∗
    (∀ (h' : CpuId) (r : mword 64) (Sc' : gset gname),
       ⌜r = (mword_of_int (-1) : mword 64) -> Sc' = (∅ : gset gname)⌝ -∗
       uwait_ans r Sc Sc' -∗
       urun N h' (<[Regidx (mword_of_int 10) := r]> m)
         (add_vec_int pc 4) avail -∗
       uch (ukn_ch N) Sc' -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Hn Hz Hal4. iIntros "#Hi Hrun Hsb Hch Hcont".
    iApply (wp_uk_ecall_wait_null_gen N h m pc avail Sc (fun _ => emp)%I
              Hn Hz Hal4 with "Hi Hrun Hsb Hch [] [Hcont]").
    { iIntros (pidv) "H". by iFrame "H". }
    iIntros (h' r Sc' pidv) "_ %Hm1 Hans Hrun Hch".
    iApply ("Hcont" $! h' r Sc' with "[%] [Hans] Hrun Hch");
      [ exact Hm1 | iApply (uwait_ans_of_pid with "Hans") ].
  Qed.

  (* ...AND THE ROW A PROCESS THAT CAN NAME ITS OWN PID READS (lane
     TRAP-ROWS-4, B1b).  It hands the program the MIDDLE form
     ([UexecRet.uwait_ans_pid]) at a pid it has just been told is its own,
     and gives its fragment back.  A process that also knows its pid is
     not 1 -- a forked child does, off [UkFork.wp_uk_ecall_fork]'s child
     arm -- then reads the reaping arm as "the generation I reaped was one
     of MY children" ([UexecRet.uwait_ans_pid_mine]), which is what
     redeems a [ChildTok.child_tok]. *)
  Lemma wp_uk_ecall_wait_null_pid (N : uk_names Σ) (h : CpuId) (m : regfile)
      (pc : mword 64) (avail : nat) (Sc : gset gname) (p : Z) :
    usysno m = USYS_wait ->
    uint (m !!! Regidx (mword_of_int 10)) = 0 ->
    is_aligned_vaddr (Virtaddr (add_vec_int pc 4)) 2 = true ->
    uinstr_is (ukn_t N) pc false (ECALL tt) -∗
    urun N h m pc avail -∗
    udepw N m pc USYS_wait -∗
    uch (ukn_ch N) Sc -∗
    UserChildren.upid (ukn_pid N) p -∗
    (∀ (h' : CpuId) (r : mword 64) (Sc' : gset gname) (pidv : mword 32),
       ⌜bv_unsigned pidv = p⌝ -∗
       UserChildren.upid (ukn_pid N) p -∗
       ⌜r = (mword_of_int (-1) : mword 64) -> Sc' = (∅ : gset gname)⌝ -∗
       uwait_ans_pid r Sc Sc' pidv -∗
       urun N h' (<[Regidx (mword_of_int 10) := r]> m)
         (add_vec_int pc 4) avail -∗
       uch (ukn_ch N) Sc' -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Hn Hz Hal4. iIntros "#Hi Hrun Hsb Hch Hpid Hcont".
    iApply (wp_uk_ecall_wait_null_gen N h m pc avail Sc
              (fun pidv => ⌜bv_unsigned pidv = p⌝ ∗
                           UserChildren.upid (ukn_pid N) p)%I
              Hn Hz Hal4 with "Hi Hrun Hsb Hch [Hpid] [Hcont]").
    { iIntros (pidv) "Ha".
      iDestruct (UserChildren.upid_agree with "Ha Hpid") as %Heq.
      iFrame "Ha Hpid". iPureIntro. exact Heq. }
    iIntros (h' r Sc' pidv) "[%Heq Hpid] %Hm1 Hans Hrun Hch".
    iApply ("Hcont" $! h' r Sc' pidv with "[%] Hpid [%] Hans Hrun Hch");
      [ exact Heq | exact Hm1 ].
  Qed.

  (* ...and the same call with the row DROPPED, which is what the callers
     that do not read it take ([UkInit.wp_kinit_wait],
     [UkShRun.wp_kshr_wait]).  Stated verbatim as it always was. *)
  Lemma wp_uk_ecall_wait_null (N : uk_names Σ) (h : CpuId) (m : regfile)
      (pc : mword 64) (avail : nat) (Sc : gset gname) :
    usysno m = USYS_wait ->
    uint (m !!! Regidx (mword_of_int 10)) = 0 ->
    is_aligned_vaddr (Virtaddr (add_vec_int pc 4)) 2 = true ->
    uinstr_is (ukn_t N) pc false (ECALL tt) -∗
    urun N h m pc avail -∗
    udepw N m pc USYS_wait -∗
    uch (ukn_ch N) Sc -∗
    (∀ (h' : CpuId) (r : mword 64) (Sc' : gset gname),
       uwait_ans r Sc Sc' -∗
       urun N h' (<[Regidx (mword_of_int 10) := r]> m)
         (add_vec_int pc 4) avail -∗
       uch (ukn_ch N) Sc' -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Hn Hz Hal4. iIntros "#Hi Hrun Hsb Hch Hcont".
    iApply (wp_uk_ecall_wait_null_live N h m pc avail Sc Hn Hz Hal4
              with "Hi Hrun Hsb Hch").
    iIntros (h' r Sc') "_ Hans Hrun Hch".
    iApply ("Hcont" $! h' r Sc' with "Hans Hrun Hch").
  Qed.

  (* =================================================================== *)
  (* WAIT AT A REAL STATUS POINTER (lane RD-7).                            *)
  (*                                                                       *)
  (* THE LEAF THE NULL ONE COULD NOT BE.  Every wait leaf above forces      *)
  (* [a0 = 0], which is exactly the case where the kernel copies nothing:   *)
  (* a program that passed a pointer got its children reading moved and     *)
  (* NOTHING about the four bytes the reap wrote into its own buffer.  The  *)
  (* carrier that fixes that is [UexecRet.uwait_ans_pid_m] -- the answer    *)
  (* and the window under ONE binder, joined once at the dispatcher's wait  *)
  (* arm -- and this is the leaf that spends it.                            *)
  (*                                                                       *)
  (* WHY IT IS WAIT'S OWN AND NOT [wp_uk_ecall_window]'s.  The window leaf  *)
  (* re-closes the run at the children set it opened at, and a reap MOVES   *)
  (* that set; wait is excluded there by name.  So this leaf is the window  *)
  (* walk and the null leaf's children move in one -- which is also why it  *)
  (* can hand back what neither could: the bytes AND the escrow.            *)
  (*                                                                       *)
  (* THE COUNT IS NOT A RESIDUE.  [UexecRet.uwait_wr]'s third clause says a *)
  (* reap at a non-null pointer placed all four bytes (a partial copyout is *)
  (* copyout's FAILING arm and kwait returns -1 on it, [SpecKwait]'s own    *)
  (* guard), so on the reaping arm the caller reads the WHOLE status word   *)
  (* out of its own buffer and not a prefix of it.                          *)
  (* =================================================================== *)
  (* WHAT A PARENT READS OUT OF ITS OWN BUFFER: the kernel's answer, and   *)
  (* -- on the arm that reaped -- the four bytes of the very word the      *)
  (* escrow is keyed at.  [nth_byte] is the model's own little-endian      *)
  (* reading ([RiscvModelBytes]), so byte [j] is bits [8j..8j+7] of the    *)
  (* 32-bit status and [ProcGeom.xstate_val] is its SIGNED value -- which  *)
  (* is what [exit_tok] carries and what a [ChildTok.child_tok]'s payload  *)
  (* is redeemed at.                                                       *)
  Definition uwait_status (r : mword 64) (cs cs' : gset gname)
      (pidv : mword 32) (g : nat -> bv 8) : iProp Σ :=
    (∃ (gn : gname) (b : bool) (rv xw : mword 32),
       ⌜r = (sign_extend' 64 rv : mword 64)⌝ ∗
       ⌜r <> (mword_of_int (-1) : mword 64) ->
        forall j : nat, (j < 4)%nat -> g j = nth_byte xw j⌝ ∗
       UserChildren.wait_ans rv (xstate_val xw) cs cs' gn b pidv)%I.

  (* the answer alone, for a caller that does not read its buffer *)
  Lemma uwait_status_ans (r : mword 64) (cs cs' : gset gname)
      (pidv : mword 32) (g : nat -> bv 8) :
    uwait_status r cs cs' pidv g -∗ uwait_ans_pid r cs cs' pidv.
  Proof using .
    iIntros "(%gn & %b & %rv & %xw & %Hr & _ & Ha)".
    iExists gn, b, rv, (xstate_val xw).
    iSplitR; [ iPureIntro; exact Hr | iExact "Ha" ].
  Qed.

  (* ...AND THE WHOLE OF WHAT A REAPING PARENT LEARNS, in one step: which
     generation left its set, the escrow that generation's exit parked, the
     pid uniqueness that makes the returned number name it, and -- the part
     no earlier leaf could state -- that its own four bytes ARE that
     escrow's status word.  [UexecRet.uwait_ans_pid_mine]'s reading, with
     the window kept. *)
  Lemma uwait_status_reaped (r : mword 64) (cs cs' : gset gname)
      (pidv : mword 32) (g : nat -> bv 8) :
    pidv <> (mword_of_int 1 : mword 32) ->
    r <> (mword_of_int (-1) : mword 64) ->
    uwait_status r cs cs' pidv g -∗
    ∃ (γ' : gname) (rv xw : mword 32),
      ⌜r = (sign_extend' 64 rv : mword 64) /\ cs' = cs ∖ {[γ']} /\
       γ' ∈ cs /\ (1 <= bv_unsigned rv <= PIDMAX)%Z /\
       (forall j : nat, (j < 4)%nat -> g j = nth_byte xw j)⌝ ∗
      ChildTok.exit_tok γ' rv (xstate_val xw) ∗ ChildTok.gen_uniq cs rv γ'.
  Proof using .
    intros Hne Hm1.
    iIntros "(%gn & %b & %rv & %xw & %Hr & %Hby & Ha)".
    iDestruct "Ha" as "[[%Hf _] | (%γ' & %Hrng & %Hoci & Hesc & Huniq)]".
    - exfalso. apply Hm1. rewrite Hr (proj1 Hf).
      apply bv_eq; vm_compute; reflexivity.
    - iExists γ', rv, xw. iFrame "Hesc Huniq". iPureIntro.
      split; [ exact Hr | ].
      split; [ exact (proj1 Hrng) | ].
      split; [ destruct Hoci as [Hin | Heq];
                 [ exact Hin | exfalso; exact (Hne Heq) ] | ].
      split; [ exact (proj2 Hrng) | exact (Hby Hm1) ].
  Qed.

  Lemma wp_uk_ecall_wait_status (N : uk_names Σ) (h : CpuId) (m : regfile)
      (pc : mword 64) (dst : mword 64) (k : nat) (f : nat -> bv 8)
      (avail : nat) (Sc : gset gname) (p : Z) :
    usysno m = USYS_wait ->
    m !!! Regidx (mword_of_int 10) = dst ->
    (* THE POINTER IS REAL, which is the whole difference from the leaves
       above -- and what makes the window's third clause fire. *)
    dst <> (zero_reg : mword 64) ->
    (4 <= k)%nat ->
    is_aligned_vaddr (Virtaddr (add_vec_int pc 4)) 2 = true ->
    uinstr_is (ukn_t N) pc false (ECALL tt) -∗
    urun N h m pc avail -∗
    udepw N m pc USYS_wait -∗
    uch (ukn_ch N) Sc -∗
    ubytes (ukn_d N) (uint dst) k f -∗
    UserChildren.upid (ukn_pid N) p -∗
    (∀ (h' : CpuId) (r : mword 64) (Sc' : gset gname) (pidv : mword 32)
       (g : nat -> bv 8),
       ⌜bv_unsigned pidv = p⌝ -∗
       UserChildren.upid (ukn_pid N) p -∗
       (* NOTHING IS PROMISED ABOUT A -1 HERE, and the reason is precise:
          [UserChildren.wait_why]'s first exit -- "a zombie child was there
          and the copyout could not place its status" -- is guarded on the
          status pointer being NULL, which is exactly what this leaf's
          caller gave up.  Refuting it needs kwait to publish copyout's own
          [~ UserPtTree.uva_wmapped] witness the way consoleread's swallow
          arm does; until it does, a real status pointer costs the -1 arm's
          reason.  See claude-notes/design/user-proc.md. *)
       (* everything OUTSIDE the four-byte window is the caller's own *)
       ⌜ forall j : nat, (4 <= j < k)%nat -> g j = f j ⌝ -∗
       uwait_status r Sc Sc' pidv g -∗
       urun N h' (<[Regidx (mword_of_int 10) := r]> m)
         (add_vec_int pc 4) avail -∗
       uch (ukn_ch N) Sc' -∗
       ubytes (ukn_d N) (uint dst) k g -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Hn Hdst Hnz Hk4 Hal4.
    iIntros "#Hi Hrun Hsb Hch Hbuf Hpid Hcont".
    iDestruct "Hrun" as (xi C pt Rfd Rut sz M pm fdv cw gn cs pidv) "(%Hlo & %Hpm & %Hlzf & %HRut & Hheap & Hstk & Hufd & Hcwda & Hcha & #Hmy & #Hdep & #Hnpx & Hb)".
    (* the pid reader, spent where the run is open -- [wp_uk_ecall_wait_null_pid] *)
    iDestruct (urun_ids_pid with "Hcha") as "[Hpida Hidsp]".
    iDestruct (UserChildren.upid_agree with "Hpida Hpid") as %Hpeq.
    iDestruct ("Hidsp" with "Hpida") as "Hcha".
    iMod (udepw_mint N m pc _ M pm _ fdv cw gn cs pidv
                with "Hdep Hmy Hsb Hheap Hufd") as "(Hheap & Hufd & Hdepn)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iDestruct (uvb_x0 with "Hb") as "[%Hx0 Hb]".
    (* THE NO-WRAP FACT, off the ownership rather than off a premise *)
    iDestruct (uheap_ubytes_run (ukn_t N) (ukn_d N) (ukn_s N) M pm sz (DfracOwn 1) (uint dst) k f
                 with "Hheap Hbuf") as %Hbnd.
    assert (Hlin : forall i : nat, (i < k)%nat ->
              uint (add_vec_int dst (Z.of_nat i)) = (uint dst + Z.of_nat i)%Z).
    { intros i Hi. destruct (Hbnd i Hi) as [_ Hc].
      change (2 ^ 38) with 274877906944 in Hc.
      rewrite !uint_unsigned in Hc |- *.
      apply uint_add_vec_int_small; lia. }
    iApply (UkStep.wp_uk_ecall C pt Rfd Rut pm sz Hlo Hpm HRut Hlzf M m pc fdv cw gn cs pidv Hui
              (fun (s : mstate)
                   (Hp : register_lookup cur_privilege s.(sregs) = User)
                   (Hc : register_lookup (R_bitvector_64 PC) s.(sregs) = pc) =>
                 UserExecFacts.goodmb_execute_ECALL_U UserFrame.Du_r UserFrame.Du_w
                   s pc ltac:(vm_compute; reflexivity)
                   ltac:(vm_compute; reflexivity) Hp Hc)
              with "Hb Hmy").
    rewrite (uexec_ret_ecall _ _ eq_refl).
    assert (Hnum : uvis_num (uvis_of_run m pc M pm sz fdv cw gn cs pidv false secc_all) = USYS_wait).
    { assert (Hraw : usys_num (uvis_tf (uvis_of_run m pc M pm sz fdv cw gn cs pidv false secc_all)) = USYS_wait)
        by (cbn [uvis_tf uvis_of_run]; rewrite tf_of_num; exact Hn).
      rewrite uvis_num_full0; [ exact Hraw | reflexivity | rewrite Hraw; usys_range ]. }
    rewrite /uexec_pay_dep /upay_at.
    pose proof Hnum as Hnume. unfold uvis_num in Hnume. rewrite ?Hnum ?Hnume. cbv zeta.
    destruct (decide (uecall_scause = uecall_scause)) as [_ | Hpne];
      [ | exfalso; exact (Hpne eq_refl) ].
    destruct (decide (USYS_wait = USYS_exit)) as [He | _];
      [ exfalso; unfold USYS_wait, USYS_exit in He; discriminate He | ].
    destruct (decide (USYS_wait = USYS_fork)) as [He | _];
      [ exfalso; unfold USYS_wait, USYS_fork in He; discriminate He | ].
    destruct (decide (USYS_wait = USYS_wait)) as [_ | Hwne];
      [ | exfalso; exact (Hwne eq_refl) ].
    iDestruct "Hdepn" as (fdep) "[%Hfp Hdepn]".
    iExists fdep. rewrite Hfp.
    cbn [uvis_gen uvis_of_run].
    iSplitR; [ iFrame "Hmy" | ].
    iSplitL "Hdepn"; [ iExact "Hdepn" | ].
    iIntros (r M' pm' sz' fdv' cw' gn' cs' lz' secc') "%Hok %Hfdok %Hpiperow %Hcwrow %Hgnrow %Hpidrow %Hliverow %Hscrow Hans _".
    assert (Hlzq : lz' = false)
      by (refine (usys_mem_ok_lazy _ _ _ _ _ _ _ _ _ _ _ _ Hok);
          first [ assumption | vm_compute; discriminate ]).
    subst lz'.
    (* ...AND SO DID THE MASK: not seccomp's number, so the row is the
       equation ([UsysMemOk.usys_secc_ok_quiet]), and the resume key is at
       the full mask [urun] is keyed at *)
    pose proof (fun Hne => usys_secc_ok_quiet _ _ _ _ _ Hne Hscrow) as Hscq.
    specialize (Hscq ltac:(usys_range)).
    cbn [uvis_secc uvis_of_run] in Hscq. subst secc'.
    assert (Hcw : cw' = cw)
      by (refine (usys_cwd_ok_quiet _ _ _ _ _ Hcwrow); vm_compute; discriminate).
    iDestruct (ucwd_auth_quiet N cw cw' Hcw with "Hcwda") as "Hcwda".
    assert (Hgnq : gn' = gn) by exact (usys_gen_ok_quiet _ _ _ Hgnrow).
    subst gn'.
    (* THE WINDOW, OFF THE ANSWER.  [uwait_ans_pid_m] is the joined form,
       so the memory equation comes out of the same binder as the status
       the escrow is keyed at -- which is the whole point of the lane. *)
    iDestruct "Hans" as (gn2 b2 rv xw) "[%Hr [%Hwr Ha]]".
    cbn [uvis_M uvis_tf uvis_ch uvis_pid uvis_of_run] in Hwr.
    rewrite tf_of_arg0 Hdst in Hwr.
    destruct Hwr as (d & Hdle & _ & Hfull & HM').
    (* the caller's bytes: the kernel's below [d], its own above -- the
       window leaf's own idiom ([wp_uk_ecall_window]). *)
    assert (Hg : exists g : nat -> bv 8,
              (forall j : nat, (j < d)%nat -> g j = nth_byte xw j) /\
              (forall j : nat, (d <= j)%nat -> g j = f j)).
    { exists (fun j => if decide (j < d)%nat then nth_byte xw j else f j).
      split; intros j Hj; case_decide as Hc;
        [ reflexivity | exfalso; lia | exfalso; lia | reflexivity ]. }
    destruct Hg as (g & Hgb & Hgf).
    assert (Hdk : (d <= k)%nat) by lia.
    rewrite (umem_wr_ext M dst d (fun i => nth_byte xw i) g
               ltac:(intros i Hi; symmetry; exact (Hgb i Hi))) in HM'.
    rewrite (umem_wr_write M dst d g
               ltac:(intros i Hi; apply Hlin; lia)) in HM'.
    subst M'.
    (* the children halves move together, as in the null leaf *)
    iDestruct (urun_ids_ch with "Hcha") as "[Hcha Hidsback]".
    iDestruct (uch_agree with "Hcha Hch") as %<-.
    iApply uslot_bupd.
    iMod (uch_update (ukn_ch N) cs cs cs' with "Hcha Hch") as "[Hcha Hch]".
    iDestruct ("Hidsback" $! cs' with "Hcha") as "Hcha".
    iModIntro.
    assert (Hview : fdv' = fdv).
    { refine (usys_fd_ok_quiet _ _ _ _ _ _ _ _ _ Hfdok);
        vm_compute; discriminate. }
    subst fdv'.
    (* the permission map and the break: wait is not sbrk, so the row is
       the identity at both ([UsysMemOk]'s wait clause, read here rather
       than through a named lemma -- it is two projections). *)
    assert (Hpsz : pm' = pm /\ sz' = sz).
    { clear - Hok. unfold usys_mem_ok in Hok.
      destruct (decide (USYS_wait = USYS_exec)) as [Hc | _];
        [ unfold USYS_wait, USYS_exec in Hc; discriminate Hc | ].
      destruct (decide (USYS_wait = USYS_sbrk)) as [Hc | _];
        [ unfold USYS_wait, USYS_sbrk in Hc; discriminate Hc | ].
      destruct (decide (USYS_wait = USYS_wait)) as [_ | Hc];
        [ | exfalso; exact (Hc eq_refl) ].
      destruct Hok as (_ & Hp & Hs & _). exact (conj Hp Hs). }
    destruct Hpsz as [-> ->].
    cbn [uvis_M uvis_perm uvis_sz uvis_of_run].
    rewrite (uslot_bump_run m pc M (umem_write M (uint dst) d g) pm pm sz sz
               fdv fdv cw cw' gn gn cs cs' pidv false false secc_all secc_all r Hx0 Hal4).
    rewrite /ukc. iIntros (h' xi' C' pt' Rfd' Rut') "%Hlo' %Hpm' %Hlzf' Hb'".
    iEval (rewrite (ubytes_split (ukn_d N) (uint dst) d k f Hdk)) in "Hbuf".
    iDestruct "Hbuf" as "[Hblo Hbhi]".
    iMod (uheap_store_run (ukn_t N) (ukn_d N) (ukn_s N) M pm sz (uint dst) d f g with "Hheap Hblo")
      as "[Hheap Hblo]".
    iDestruct (ubytes_ext (ukn_d N) (uint dst + Z.of_nat d) (k - d)
                 (fun j => f (d + j)%nat) (fun j => g (d + j)%nat)
                 ltac:(intros j _; symmetry; apply Hgf; lia) with "Hbhi")
      as "Hbhi".
    iAssert (ubytes (ukn_d N) (uint dst) k g) with "[Hblo Hbhi]" as "Hbuf".
    { rewrite (ubytes_split (ukn_d N) (uint dst) d k g Hdk). iFrame "Hblo Hbhi". }
    iDestruct (urun_close_upd N (umem_write M (uint dst) d g) pm m
                 (mword_of_int 10) r sz fdv cw' gn cs' pidv (add_vec_int pc 4) avail
                 ltac:(unfold unot_sp; vm_compute; discriminate)
                 with "Hheap Hstk Hufd Hcwda Hcha Hmy Hdep Hnpx [Hcont Hbuf Hch Hpid Ha]") as "Hkc".
    { iIntros (h'') "Hrun".
      iApply ("Hcont" $! h'' r cs' pidv g with "[%] Hpid [%] [Ha] Hrun Hch Hbuf").
      - exact Hpeq.
      - intros j Hj. apply Hgf. lia.
      - iExists gn2, b2, rv, xw.
        iSplitR; [ iPureIntro; exact Hr | ].
        iSplitR; [ | iExact "Ha" ].
        iPureIntro. intros Hm1 j Hj.
        rewrite (Hgb j ltac:(rewrite (Hfull Hnz Hm1); exact Hj)). reflexivity. }
    iDestruct (ukcq_ukc with "Hkc") as "Hkc".
    iApply ("Hkc" $! h' xi' C' pt' Rfd' Rut' with "[%] [%] [%] Hb'");
      [ exact Hlo' | exact Hpm' | exact Hlzf' ].
  Qed.


  (* ...AND THE INDEX-FREE FORM -- DELETED (lane IO-LEAF, M3a).
     [wp_uk_ecall_wait_any] took the set behind an existential and
     DISCARDED the answer, which is the one thing a reaping parent wants:
     the escrow its child's exit parked.  init never used it and sh's one
     call site ([UkShRun.wp_kshr_wait]) now takes the leaf above at a
     named set; a caller that does not read the answer opens its own
     existential and closes it with [UserChildren.uch_any_of], which is
     all the wrapper ever did. *)


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
  (* on the kernel side ([SpecSysRead]) but has never been carried into     *)
  (* [usys_mem_ok]'s read row, so it cannot be stated here.  [d] is exposed *)
  (* anyway: the day the row carries it, this statement takes it without   *)
  (* moving.                                                                *)
  (*                                                                       *)
  (* A NULL DESTINATION is not a case here.  wait's row already forces      *)
  (* [d = 0] at a null status pointer, so [wp_uk_ecall_wait_null] is the    *)
  (* instance for a caller that owns NOTHING, and this leaf is the one for  *)
  (* a caller that does.                                                    *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_uk_ecall_window (N : uk_names Σ) (h : CpuId) (m : regfile)
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
    (* ...AND IT IS NOT WAIT, which moves the caller's children reading and
       has its own leaves ([wp_uk_ecall_wait_null] / [_any]): this one
       re-closes the run at the set it opened at. *)
    n <> USYS_wait ->
    (* ...and a number the full mask passes, not seccomp's
       ([wp_uk_ecall_quiet]'s two rows) *)
    (0 <= n < 64)%Z -> n <> USYS_seccomp ->
    is_aligned_vaddr (Virtaddr (add_vec_int pc 4)) 2 = true ->
    uinstr_is (ukn_t N) pc false (ECALL tt) -∗
    urun N h m pc avail -∗
    udepw N m pc n -∗
    ubytes (ukn_d N) (uint dst) k f -∗
    (∀ (h' : CpuId) (r : mword 64) (d : nat) (g : nat -> bv 8),
       ⌜ (d <= cap)%nat ⌝ -∗
       ⌜ forall j : nat, (d <= j < k)%nat -> g j = f j ⌝ -∗
       (* ...and, at read, WHAT IT ANSWERED ([UsysMemOk.usys_read_ret]):
          -1, or a count no larger than the one asked for *)
       ⌜ n = USYS_read -> usys_read_ret (tf_of m pc) r ⌝ -∗
       urun N h' (<[Regidx (mword_of_int 10) := r]> m)
         (add_vec_int pc 4) avail -∗
       ubytes (ukn_d N) (uint dst) k g -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Hn Hwin Hcapk Hcl Hdp Hop Hpp Hwt Hrng Hn23 Hal4.
    iIntros "#Hi Hrun Hsb Hbuf Hcont".
    iDestruct "Hrun" as (xi C pt Rfd Rut sz M pm fdv cw gn cs pidv) "(%Hlo & %Hpm & %Hlzf & %HRut & Hheap & Hstk & Hufd & Hcwda & Hcha & #Hmy & #Hdep & #Hnpx & Hb)".
    iMod (udepw_mint N m pc _ M pm _ fdv cw gn cs pidv
                with "Hdep Hmy Hsb Hheap Hufd") as "(Hheap & Hufd & Hdepn)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iDestruct (uvb_x0 with "Hb") as "[%Hx0 Hb]".
    (* THE NO-WRAP FACT, off the ownership rather than off a premise *)
    iDestruct (uheap_ubytes_run (ukn_t N) (ukn_d N) (ukn_s N) M pm sz (DfracOwn 1) (uint dst) k f
                 with "Hheap Hbuf") as %Hbnd.
    assert (Hlin : forall i : nat, (i < k)%nat ->
              uint (add_vec_int dst (Z.of_nat i)) = (uint dst + Z.of_nat i)%Z).
    { intros i Hi. destruct (Hbnd i Hi) as [_ Hc].
      change (2 ^ 38) with 274877906944 in Hc.
      rewrite !uint_unsigned in Hc |- *.
      apply uint_add_vec_int_small; lia. }
    iApply (UkStep.wp_uk_ecall C pt Rfd Rut pm sz Hlo Hpm HRut Hlzf M m pc fdv cw gn cs pidv Hui
              (fun (s : mstate)
                   (Hp : register_lookup cur_privilege s.(sregs) = User)
                   (Hc : register_lookup (R_bitvector_64 PC) s.(sregs) = pc) =>
                 UserExecFacts.goodmb_execute_ECALL_U UserFrame.Du_r UserFrame.Du_w
                   s pc ltac:(vm_compute; reflexivity)
                   ltac:(vm_compute; reflexivity) Hp Hc)
              with "Hb Hmy").
    rewrite (uexec_ret_ecall _ _ eq_refl).
    assert (Hnum : uvis_num (uvis_of_run m pc M pm sz fdv cw gn cs pidv false secc_all) = n).
    { assert (Hraw : usys_num (uvis_tf (uvis_of_run m pc M pm sz fdv cw gn cs pidv false secc_all)) = n)
        by (cbn [uvis_tf uvis_of_run]; rewrite tf_of_num; exact Hn).
      rewrite uvis_num_full0; [ exact Hraw | reflexivity | rewrite Hraw; usys_range ]. }
    assert (Hw : usys_win n (uvis_tf (uvis_of_run m pc M pm sz fdv cw gn cs pidv false secc_all))
                 = Some (dst, cap)).
    { cbn [uvis_tf uvis_of_run]. rewrite usyswin_tf_of. exact Hwin. }
    destruct (usys_win_num n _ dst cap Hw) as (Hexit & Hfork & _ & Hsbk & Hchd).
    (* the PAYMENT's guard IS the deposit's own, so it is opened BEFORE the
       number is rewritten and the destructs below then reduce both copies
       at once *)
    rewrite /uexec_pay_dep /upay_at.
    pose proof Hnum as Hnume. unfold uvis_num in Hnume. rewrite ?Hnum ?Hnume. cbv zeta.
    destruct (decide (uecall_scause = uecall_scause)) as [_ | Hpne];
      [ | exfalso; exact (Hpne eq_refl) ].
    destruct (decide (n = USYS_exit)) as [He | _]; [ exfalso; exact (Hexit He) | ].
    destruct (decide (n = USYS_fork)) as [He | _]; [ exfalso; exact (Hfork He) | ].
    destruct (decide (n = USYS_wait)) as [He | _]; [ exfalso; exact (Hwt He) | ].
    (* the arm binds the deposit's FAMILIES ([UexecSG.v]'s header); the
       law mints at some [f] and this leaf, which discards its post,
       hands that witness straight over. *)
    (* THE MINT ALREADY NAMED THE PAYLOAD (app-echo.md, "SH-LINE RULING",
       R1): read's bundle is a wand from the depositing process's own exit
       payload, so nothing is re-keyed here any more -- the family the
       deposit came at IS at [ukn_pay N]. *)
    iDestruct "Hdepn" as (fdep) "[%Hfp Hdepn]".
    iExists fdep. rewrite Hfp.
    cbn [uvis_gen uvis_of_run].
    iSplitR; [ iFrame "Hmy" | ].
    iSplitL "Hdepn"; [ iExact "Hdepn" | ].
    iIntros (r M' pm' sz' fdv' cw' gn' cs' lz' secc') "%Hok %Hfdok %Hpiperow %Hcwrow %Hgnrow %Hpidrow %Hliverow %Hscrow %Hchrow _".
    (* THE LAZY BIT CROSSED THE TRAP UNCHANGED (lane LAZY-FLAG, L6).  The
       trapping key is at [false] -- the U tier's run is
       ([UexecRet.ukcq]) -- and every row but sbrk's is the equation
       ([UsysMemOk.usys_mem_ok_lazy]), so the resume key is at [false] too
       and the close below is at the run's own bit. *)
    assert (Hlzq : lz' = false)
      by (refine (usys_mem_ok_lazy _ _ _ _ _ _ _ _ _ _ _ _ Hok);
          first [ assumption | vm_compute; discriminate ]).
    subst lz'.
    (* ...AND SO DID THE MASK: not seccomp's number, so the row is the
       equation ([UsysMemOk.usys_secc_ok_quiet]), and the resume key is at
       the full mask [urun] is keyed at *)
    pose proof (fun Hne => usys_secc_ok_quiet _ _ _ _ _ Hne Hscrow) as Hscq.
    specialize (Hscq ltac:(usys_range)).
    cbn [uvis_secc uvis_of_run] in Hscq. subst secc'.
    (* THE CWD CROSSED THE TRAP UNCHANGED -- chdir is the one row that moves
       it, and this is not it -- so the engine's half is re-keyed onto the
       view the process resumes at and the program's half never moved. *)
    assert (Hcw : cw' = cw)
      by (exact (usys_cwd_ok_quiet n r cw cw' Hchd Hcwrow)).
    iDestruct (ucwd_auth_quiet N cw cw' Hcw with "Hcwda") as "Hcwda".
    (* ...AND SO DID THE GENERATION AND THE CHILDREN SET: no entry
       re-incarnates its caller, and this lane's children row is the
       identity at every number ([UsysMemOk] SS2e/SS2f).  Both are
       substituted rather than re-keyed -- the generation has no
       authority beside it, and the children authority is already at
       the set the process resumes at. *)
    assert (Hgn : gn' = gn) by exact (usys_gen_ok_quiet _ _ _ Hgnrow).
    assert (Hch : cs' = cs) by exact (usys_ch_ok_quiet _ _ _ _ Hchrow).
    subst gn' cs'.
    (* read's answer, off the same row, before the destruct spends it *)
    assert (Hrdret : n = USYS_read -> usys_read_ret (tf_of m pc) r)
      by (intros Hrd; exact (usys_mem_ok_read_ret n _ r _ _ _ _ _ _ _ _ Hrd Hok)).
    destruct (usys_mem_ok_window n _ r _ _ _ _ _ _ _ _ dst cap Hw Hok)
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
               fdv fdv cw cw' gn gn cs cs pidv false false secc_all secc_all r Hx0 Hal4).
    (* [uheap_store_run] is a basic update and [ukc] is not a [WP], so the
       re-assembly runs under [ukc]'s own binders -- which is why this leaf
       opens the close by hand instead of applying it to the goal. *)
    rewrite /ukc. iIntros (h' xi' C' pt' Rfd' Rut') "%Hlo' %Hpm' %Hlzf' Hb'".
    iEval (rewrite (ubytes_split (ukn_d N) (uint dst) d k f Hdk)) in "Hbuf".
    iDestruct "Hbuf" as "[Hblo Hbhi]".
    iMod (uheap_store_run (ukn_t N) (ukn_d N) (ukn_s N) M pm sz (uint dst) d f g with "Hheap Hblo")
      as "[Hheap Hblo]".
    iDestruct (ubytes_ext (ukn_d N) (uint dst + Z.of_nat d) (k - d)
                 (fun j => f (d + j)%nat) (fun j => g (d + j)%nat)
                 ltac:(intros j _; symmetry; apply Hgf; lia) with "Hbhi")
      as "Hbhi".
    iAssert (ubytes (ukn_d N) (uint dst) k g) with "[Hblo Hbhi]" as "Hbuf".
    { rewrite (ubytes_split (ukn_d N) (uint dst) d k g Hdk). iFrame "Hblo Hbhi". }
    iDestruct (urun_close_upd N (umem_write M (uint dst) d g) pm m
                 (mword_of_int 10) r sz fdv cw' gn cs pidv (add_vec_int pc 4) avail
                 ltac:(unfold unot_sp; vm_compute; discriminate)
                 with "Hheap Hstk Hufd Hcwda Hcha Hmy Hdep Hnpx [Hcont Hbuf]") as "Hkc";
      [ iIntros (h'') "Hrun";
        iApply ("Hcont" $! h'' r d g with "[%] [%] [%] Hrun Hbuf");
        [ exact Hdcap | intros j Hj; apply Hgf; lia | exact Hrdret ] | ].
    iDestruct (ukcq_ukc with "Hkc") as "Hkc".
    iApply ("Hkc" $! h' xi' C' pt' Rfd' Rut' with "[%] [%] [%] Hb'");
      [ exact Hlo' | exact Hpm' | exact Hlzf' ].
  Qed.


  (* ------------------------------------------------------------------- *)
  (* THE TWO SCANS NAME THE SAME PIPE (design/pipe.md, "The byte queue").  *)
  (* [UsysMemOk.usys_pipe_ok] and [UexecExecInst]'s row-4 post each bind    *)
  (* their own [a], [b] and [gp]; both are least-closed scans of the SAME   *)
  (* incoming table and both describe the SAME outgoing one, so the pipe    *)
  (* the post's fragment is about is the pipe the handles are ends of.      *)
  (* Only the RECORD is needed downstream -- the slots' equality follows    *)
  (* the same way and nothing asks for it -- so that is all this states.    *)
  (* ------------------------------------------------------------------- *)
  Lemma upipe_names_agree (fdv fdv' : list fdstate) (a b a2 b2 : nat)
      (gp gp2 : pipe_names) :
    fd_least_closed fdv a ->
    fd_least_closed (<[a := FdOpen true false (FdPipe gp)]> fdv) b ->
    fdv' = <[b := FdOpen false true (FdPipe gp)]>
             (<[a := FdOpen true false (FdPipe gp)]> fdv) ->
    fd_least_closed fdv a2 ->
    fd_least_closed (<[a2 := FdOpen true false (FdPipe gp2)]> fdv) b2 ->
    fdv' = <[b2 := FdOpen false true (FdPipe gp2)]>
             (<[a2 := FdOpen true false (FdPipe gp2)]> fdv) ->
    gp2 = gp.
  Proof using .
    intros Hca Hcb -> Hca2 Hcb2 Heq.
    (* the two read ends are the same slot: [fd_lowest_closed] is a function *)
    rewrite (fd_least_closed_unique fdv a2 a Hca2 Hca) in Hcb2, Heq.
    assert (Halt : (a < length fdv)%nat) by exact (fd_least_closed_lt _ _ Hca).
    (* neither write end can BE that slot -- the scan found it closed and
       the read end's install left it open *)
    assert (Hba : b <> a).
    { intros ->. pose proof (fd_least_closed_free _ _ Hcb) as Hf.
      rewrite list_lookup_insert in Hf; [ discriminate Hf | exact Halt ]. }
    assert (Hb2a : b2 <> a).
    { intros ->. pose proof (fd_least_closed_free _ _ Hcb2) as Hf.
      rewrite list_lookup_insert in Hf; [ discriminate Hf | exact Halt ]. }
    (* ...so slot [a] of the OUTGOING table is the read end, read twice *)
    assert (Hr1 : (<[b := FdOpen false true (FdPipe gp)]>
                    (<[a := FdOpen true false (FdPipe gp)]> fdv)) !! a
                  = Some (FdOpen true false (FdPipe gp))).
    { rewrite list_lookup_insert_ne; [ | exact Hba ].
      rewrite list_lookup_insert; [ reflexivity | exact Halt ]. }
    rewrite Heq in Hr1.
    rewrite list_lookup_insert_ne in Hr1; [ | exact Hb2a ].
    rewrite list_lookup_insert in Hr1; [ | exact Halt ].
    injection Hr1 as Hr1. exact Hr1.
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
  Lemma wp_uk_ecall_pipe (N : uk_names Σ) (h : CpuId) (m : regfile)
      (pc : mword 64) (l : list fdstate) (f : nat -> bv 8) (avail : nat)
      (Rp : sfam -> uvis -> mword 64 -> gmap Z (bv 8) -> list fdstate -> Z ->
            gset gname -> iProp Σ) :
    usysno m = USYS_pipe ->
    is_aligned_vaddr (Virtaddr (add_vec_int pc 4)) 2 = true ->
    uinstr_is (ukn_t N) pc false (ECALL tt) -∗
    urun N h m pc avail -∗
    udepw N m pc USYS_pipe -∗
    (* THE REGISTRAR, AND IT IS WHAT THE TAINT USED TO BE (design/
       app-pipe.md SS2; the design's STOP RULE named this shape as the
       fallback and it is the shape that works -- see lane PIPE-REG's
       finding for why the run cannot instead be handed back OWED).
       pipe(2) is the ONE number that puts a pipe row in the table, so it
       is the one number [UsysMemOk.usys_fd_ok_nopipe] does not cover and
       the run's [UkRun.urun_nopipe] cannot re-establish by itself.  What
       stood here was [□ riscv_kill_cred] -- the credential every pipe
       payment is payable from -- so a verified program could not call
       pipe(2) and stay untainted.  What stands here now is the CALLER'S
       OWN FUPD from ROW 4'S POST, where the new pipe's names and its exact
       byte-queue fragment live, to the two new rows' REGISTRATION
       ([UexecSG.srow_reg], one [□]-guarded close payment per row).

       WHY THE POST GOES IN AND [Rp] COMES OUT.  This file is stated over
       the deposit class and cannot open row 4's post, so the step has to
       be the caller's; and registering a pipe CONSUMES the fragment (a
       registration is a [□] and one fragment buys exactly one payment --
       [PipeReg.pipe_cpay_of_frag]), so the post cannot come back
       unchanged.  The caller therefore says what it keeps, and the leaf
       hands that on: [UkReadPipe.wp_uk_pipe_read_end] is the instance's
       reading, where [Rp] is the fragment's successor.

       THE MASK IS [⊤], which is where the leaf's own step runs; the pure
       premise is the fd row's else-branch, so a call that FAILED (no pipe,
       no new row) is registered for free out of the run's own reading.
       A caller that wants the OLD behaviour takes [Rp := spost_at …] and
       supplies this from the credential ([UkRun.urun_nopipe_taint]). *)
    (∀ (fdep : sfam) (W : uvis) (r : mword 64) (M' : gmap Z (bv 8))
       (fdv' : list fdstate) (cw' : Z) (cs' : gset gname),
       ⌜ uint r <> 0 -> fdv' = uvis_fd W ⌝ -∗
       urun_nopipe (uvis_fd W) -∗
       spost_at uslot USYS_pipe fdep W r M' fdv' cw' cs' ={⊤}=∗
       urun_nopipe fdv' ∗ Rp fdep W r M' fdv' cw' cs') -∗
    ustd (ukn_fd N) l -∗
    ubytes (ukn_d N) (uint (m !!! Regidx (mword_of_int 10))) 8 f -∗
    (∀ (h' : CpuId) (r : mword 64) (g : nat -> bv 8) (W : uvis) (fdep : sfam)
       (M' : gmap Z (bv 8)) (fdv' : list fdstate) (cw' : Z) (cs' : gset gname),
       ((∃ (a b : nat) (γp : pipe_names),
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
                                (i - 4)%nat)
             (* ...AND THE TWO SCANS THEMSELVES (design/pipe.md, "The byte
                queue").  The row-4 POST binds its own two slots and its
                own [γp] -- it is a separate scan of the same table -- so a
                caller that wants the pipe's fragment beside these handles
                has to identify the two bindings.  [upipe_names_agree]
                above is that step, and these are the facts it runs on. *)
             /\ fd_least_closed (uvis_fd W) a
             /\ fd_least_closed (<[a := FdOpen true false (FdPipe γp)]> (uvis_fd W)) b
             /\ fdv' = <[b := FdOpen false true (FdPipe γp)]>
                         (<[a := FdOpen true false (FdPipe γp)]> (uvis_fd W)) ⌝ ∗
           (* PIPE ALLOCATES TWICE, so its post is two ARMS and ONE
              ledger: the read end's scan runs on the caller's ledger and
              the write end's on the ledger that left.  At an all-open
              ledger -- which is where any program that has not just closed
              a standard stream is -- both arms are handles and the ledger
              does not move at all. *)
           (* BOTH ENDS NAME THE SAME PIPE: one [γp], carried by both
              states, which is how a descriptor table says two descriptors
              are the two ends of one pipe. *)
           ualloc_at (ukn_fd N) l a (FdOpen true false (FdPipe γp)) ∗
           ualloc_at (ukn_fd N) (ustd_after l (FdOpen true false (FdPipe γp))) b
             (FdOpen false true (FdPipe γp)) ∗
           ustd (ukn_fd N) (ustd_after (ustd_after l (FdOpen true false (FdPipe γp)))
                       (FdOpen false true (FdPipe γp))))
        (* ...OR IT FAILED, AT -1 (lane PIPE-NEG1; lane SH-PIPE's R-1).
           This arm used to read [uint r <> 0], which is what the pipe row
           said and not what a caller can act on: sh's next instruction
           after [pipe(p)] is [bltz a0], and `nonzero' does not decide a
           sign -- so the not-taken-and-nonzero path ran the pipeline on
           two garbage descriptors and no walk could enter it.  The row now
           pins the value, exactly as the open and dup rows (and their
           leaves' failure arms) do, and this is that conjunct read at the
           guard ([UsysMemOk.usys_fd_ok_pipe_neg1]).  [uint r <> 0] is a
           consequence and is not restated. *)
        ∨ (⌜ r = (mword_of_int (-1) : mword 64) ⌝ ∗ ustd (ukn_fd N) l)) -∗
       (* WHAT THE CALLER KEPT OF THE KEY'S POST (design/app-pipe.md SS2).
          Row 4 carries the new pipe's EXACT byte-queue fragment at the
          birth state, and only the class's INSTANCE can read that row --
          this file is stated over the class -- so the post went to the
          REGISTRAR above, which is the caller's own, and what comes back
          out here is whatever the caller chose to keep.  The family is
          quantified because the mint chose it: row 4's branch of the post
          mentions no family field, so any witness serves.
          [UkReadPipe.wp_uk_pipe_read_end] is the instance's reading, at
          [Rp] = the fragment's successor. *)
       Rp fdep W r M' fdv' cw' cs' -∗
       urun N h' (<[Regidx (mword_of_int 10) := r]> m)
         (add_vec_int pc 4) avail -∗
       ubytes (ukn_d N) (uint (m !!! Regidx (mword_of_int 10))) 8 g -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Hn Hal4.
    set (dst := m !!! Regidx (mword_of_int 10)).
    iIntros "#Hi Hrun Hsb Hreg Hstd Hbuf Hcont".
    iDestruct "Hrun" as (xi C pt Rfd Rut sz M pm fdv cw gn cs pidv) "(%Hlo & %Hpm & %Hlzf & %HRut & Hheap & Hstk & Hufd & Hcwda & Hcha & #Hmy & #Hdep & #Hrws & Hb)".
    (* THE RUN'S OWN READING IS KEPT NOW, not thrown away (design/
       app-pipe.md SS2): it is one half of what the registrar takes, and
       the two new rows' registrations are the other.  ([urun_rows] IS
       [urun_nopipe] since upstream's OFF-LINK-2 L6 deleted the offset
       half.) *)
    iDestruct "Hrws" as "#Hnp".
    iMod (udepw_mint N m pc _ M pm _ fdv cw gn cs pidv
                with "Hdep Hmy Hsb Hheap Hufd") as "(Hheap & Hufd & Hdepn)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iDestruct (uvb_x0 with "Hb") as "[%Hx0 Hb]".
    iDestruct (ufd_auth_len with "Hufd") as %Hfdlen.
    iDestruct (uheap_ubytes_run (ukn_t N) (ukn_d N) (ukn_s N) M pm sz (DfracOwn 1) (uint dst) 8 f
                 with "Hheap Hbuf") as %Hbnd.
    assert (Hlin : forall i : nat, (i < 8)%nat ->
              uint (add_vec_int dst (Z.of_nat i)) = (uint dst + Z.of_nat i)%Z).
    { intros i Hi. destruct (Hbnd i Hi) as [_ Hc].
      change (2 ^ 38) with 274877906944 in Hc.
      rewrite !uint_unsigned in Hc |- *.
      apply uint_add_vec_int_small; lia. }
    iApply (UkStep.wp_uk_ecall C pt Rfd Rut pm sz Hlo Hpm HRut Hlzf M m pc fdv cw gn cs pidv Hui
              (fun (s : mstate)
                   (Hp : register_lookup cur_privilege s.(sregs) = User)
                   (Hc : register_lookup (R_bitvector_64 PC) s.(sregs) = pc) =>
                 UserExecFacts.goodmb_execute_ECALL_U UserFrame.Du_r UserFrame.Du_w
                   s pc ltac:(vm_compute; reflexivity)
                   ltac:(vm_compute; reflexivity) Hp Hc)
              with "Hb Hmy").
    rewrite (uexec_ret_ecall _ _ eq_refl).
    assert (Hnum : uvis_num (uvis_of_run m pc M pm sz fdv cw gn cs pidv false secc_all) = USYS_pipe).
    { assert (Hraw : usys_num (uvis_tf (uvis_of_run m pc M pm sz fdv cw gn cs pidv false secc_all)) = USYS_pipe)
        by (cbn [uvis_tf uvis_of_run]; rewrite tf_of_num; exact Hn).
      rewrite uvis_num_full0; [ exact Hraw | reflexivity | rewrite Hraw; usys_range ]. }
    assert (Hw : usys_win USYS_pipe (uvis_tf (uvis_of_run m pc M pm sz fdv cw gn cs pidv false secc_all))
                 = Some (dst, 8%nat)).
    { cbn [uvis_tf uvis_of_run]. rewrite usyswin_tf_of.
      unfold usyswin.
      destruct (decide (USYS_pipe = USYS_wait)) as [Hc | _];
        [ exfalso; vm_compute in Hc; discriminate | ].
      destruct (decide (USYS_pipe = USYS_pipe)) as [_ | Hc];
        [ reflexivity | exfalso; exact (Hc eq_refl) ]. }
    (* the row reads a0 at the trapframe; the buffer is owned at the
       REGISTER's spelling.  They are the same word. *)
    assert (Ha0 : uvis_tf (uvis_of_run m pc M pm sz fdv cw gn cs pidv false secc_all) !!! tf_arg_idx 0 = dst)
      by (cbn [uvis_tf uvis_of_run]; reflexivity).
    (* the PAYMENT's guard IS the deposit's own, so it is opened BEFORE the
       number is rewritten and the destructs below then reduce both copies
       at once *)
    rewrite /uexec_pay_dep /upay_at.
    pose proof Hnum as Hnume. unfold uvis_num in Hnume. rewrite ?Hnum ?Hnume. cbv zeta.
    destruct (decide (uecall_scause = uecall_scause)) as [_ | Hpne];
      [ | exfalso; exact (Hpne eq_refl) ].
    destruct (decide (USYS_pipe = USYS_exit)) as [He | _];
      [ exfalso; vm_compute in He; discriminate | ].
    destruct (decide (USYS_pipe = USYS_fork)) as [He | _];
      [ exfalso; vm_compute in He; discriminate | ].
    (* the arm binds the deposit's FAMILIES ([UexecSG.v]'s header); the
       law mints at some [f] and this leaf, which discards its post,
       hands that witness straight over. *)
    (* THE MINT ALREADY NAMED THE PAYLOAD (app-echo.md, "SH-LINE RULING",
       R1): read's bundle is a wand from the depositing process's own exit
       payload, so nothing is re-keyed here any more -- the family the
       deposit came at IS at [ukn_pay N]. *)
    iDestruct "Hdepn" as (fdep) "[%Hfp Hdepn]".
    iExists fdep. rewrite Hfp.
    cbn [uvis_gen uvis_of_run].
    iSplitR; [ iFrame "Hmy" | ].
    iSplitL "Hdepn"; [ iExact "Hdepn" | ].
    iIntros (r M' pm' sz' fdv' cw' gn' cs' lz' secc') "%Hok %Hfdok %Hpiperow %Hcwrow %Hgnrow %Hpidrow %Hliverow %Hscrow %Hchrow Hsp".
    (* THE POST IS NOT DISCARDED ANY MORE (design/pipe.md, "The byte
       queue"): row 4 hands the process the new pipe's exact fragment, and
       this leaf passes it on unread -- only the instance can open it. *)
    (* THE LAZY BIT CROSSED THE TRAP UNCHANGED (lane LAZY-FLAG, L6).  The
       trapping key is at [false] -- the U tier's run is
       ([UexecRet.ukcq]) -- and every row but sbrk's is the equation
       ([UsysMemOk.usys_mem_ok_lazy]), so the resume key is at [false] too
       and the close below is at the run's own bit. *)
    assert (Hlzq : lz' = false)
      by (refine (usys_mem_ok_lazy _ _ _ _ _ _ _ _ _ _ _ _ Hok);
          first [ assumption | vm_compute; discriminate ]).
    subst lz'.
    (* ...AND SO DID THE MASK: not seccomp's number, so the row is the
       equation ([UsysMemOk.usys_secc_ok_quiet]), and the resume key is at
       the full mask [urun] is keyed at *)
    pose proof (fun Hne => usys_secc_ok_quiet _ _ _ _ _ Hne Hscrow) as Hscq.
    specialize (Hscq ltac:(usys_range)).
    cbn [uvis_secc uvis_of_run] in Hscq. subst secc'.
    (* THE CWD CROSSED THE TRAP UNCHANGED -- chdir is the one row that moves
       it, and this is not it -- so the engine's half is re-keyed onto the
       view the process resumes at and the program's half never moved. *)
    assert (Hcw : cw' = cw)
      by (refine (usys_cwd_ok_quiet _ _ _ _ _ Hcwrow); vm_compute; discriminate).
    iDestruct (ucwd_auth_quiet N cw cw' Hcw with "Hcwda") as "Hcwda".
    (* ...AND SO DID THE GENERATION AND THE CHILDREN SET: no entry
       re-incarnates its caller, and this lane's children row is the
       identity at every number ([UsysMemOk] SS2e/SS2f).  Both are
       substituted rather than re-keyed -- the generation has no
       authority beside it, and the children authority is already at
       the set the process resumes at. *)
    assert (Hgn : gn' = gn) by exact (usys_gen_ok_quiet _ _ _ Hgnrow).
    assert (Hch : cs' = cs) by exact (usys_ch_ok_quiet _ _ _ _ Hchrow).
    subst gn' cs'.
    destruct (usys_mem_ok_window USYS_pipe _ r _ _ _ _ _ _ _ _ dst 8%nat Hw Hok)
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
                 exists (a b : nat) (γp : pipe_names),
                   a <> b /\
                   (* THE SCANS, NOT MERELY THE FREENESS.  The summary used
                      to weaken both to "the slot was free", which is what
                      the mint needed then; the ledger needs the scan -- it
                      is what says WHICH descriptor came back -- and the row
                      states the write end's scan against the table the read
                      end's install left, so the summary carries it in that
                      same shape. *)
                   fd_least_closed fdv a /\
                   fd_least_closed (<[a := FdOpen true false (FdPipe γp)]> fdv) b /\
                   fdv' = <[b := FdOpen false true (FdPipe γp)]>
                            (<[a := FdOpen true false (FdPipe γp)]> fdv) /\
                   (forall i : nat, (i < 8)%nat ->
                      gg i = if (i <? 4)%nat
                             then nth_byte
                                    (trunc32 (mword_of_int (Z.of_nat a) : mword 64)) i
                             else nth_byte
                                    (trunc32 (mword_of_int (Z.of_nat b) : mword 64))
                                    (i - 4)%nat)) /\
              (* ...AND THE FAILING CALL'S OWN VALUE, which the row now
                 pins (lane PIPE-NEG1): the table did not move AND the
                 return is -1. *)
              (uint r <> 0 -> r = (mword_of_int (-1) : mword 64) /\ fdv' = fdv)).
    { destruct (decide (uint r = 0)) as [Hr0 | Hr0].
      - (* SUCCESS: the joined row pins the image on the nose -- all eight
           bytes, from the naming function -- so it, not the window row, is
           what the tail runs on.  The window row's own [d]/[bs] are
           discarded here: two descriptions of one map, and this is the
           informative one. *)
        destruct (Hpiperow eq_refl Hr0)
          as (a & b & γp & bs2 & Hne & Hca & Hcb & HM2 & Hbytes & Hfdv').
        exists 8%nat, bs2.
        split_and!;
          [ lia
          | rewrite HM2 Ha0; reflexivity
          | intros j Hj; exfalso; lia
          | intros _; exists a, b, γp; split_and!;
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
        + (* the row's else-branch, read at the guard this branch is under
             -- BOTH of its conjuncts now, the -1 and the unmoved table *)
          intros _.
          exact (usys_fd_ok_pipe_neg1 _ r fdv fdv' Hfdok Hr0). }
    destruct Hjoin as (dd & gg & Hdd8 & HMj & Hgf & Hsucc & Hfail).
    rewrite (umem_wr_write M dst dd gg
               ltac:(intros i Hi; apply Hlin; lia)) in HMj.
    (* the window row's own description of [M'] is the weaker of the two and
       has served its purpose (it is where [d] came from); dropping it is
       what lets [subst] pick the joined one. *)
    clear HM'. subst M'.
    rewrite (uslot_bump_run m pc M (umem_write M (uint dst) dd gg) pm pm sz sz
               fdv fdv' cw cw' gn gn cs cs pidv false false secc_all secc_all r Hx0 Hal4).
    rewrite /ukc. iIntros (h' xi' C' pt' Rfd' Rut') "%Hlo' %Hpm' %Hlzf' Hb'".
    iEval (rewrite (ubytes_split (ukn_d N) (uint dst) dd 8 f Hdd8)) in "Hbuf".
    iDestruct "Hbuf" as "[Hblo Hbhi]".
    iMod (uheap_store_run (ukn_t N) (ukn_d N) (ukn_s N) M pm sz (uint dst) dd f gg with "Hheap Hblo")
      as "[Hheap Hblo]".
    (* hoisted out of argument position: the tail bound [j < 8 - dd] is what
       [Hgf] needs and an [ltac:] there would be run before it is in scope
       (claude-notes/optimization.md, "Inline [ltac:]"). *)
    assert (Htail : forall j : nat, (j < 8 - dd)%nat ->
              f (dd + j)%nat = gg (dd + j)%nat)
      by (intros j Hj; symmetry; apply Hgf; lia).
    iDestruct (ubytes_ext (ukn_d N) (uint dst + Z.of_nat dd) (8 - dd)
                 (fun j => f (dd + j)%nat) (fun j => gg (dd + j)%nat)
                 Htail with "Hbhi")
      as "Hbhi".
    iAssert (ubytes (ukn_d N) (uint dst) 8 gg) with "[Hblo Hbhi]" as "Hbuf".
    { rewrite (ubytes_split (ukn_d N) (uint dst) dd 8 gg Hdd8). iFrame "Hblo Hbhi". }
    (* ---- THE AUTHORITY MOVES TO [fdv'], and on success it pays out the
           two handles.  [b]'s end is installed first so that [a] is still
           free when its own insert runs -- the two are distinct, which is
           what the row promises. ---- *)
    iAssert (|==> ufd_auth (ukn_fd N) fdv' ∗
              ((∃ (a b : nat) (γp : pipe_names),
                  ⌜ uint r = 0 /\ a <> b /\ (a < NOFILE)%nat /\ (b < NOFILE)%nat
                    /\ (forall i : nat, (i < 8)%nat ->
                          gg i = if (i <? 4)%nat
                                 then nth_byte
                                        (trunc32 (mword_of_int (Z.of_nat a) : mword 64)) i
                                 else nth_byte
                                        (trunc32 (mword_of_int (Z.of_nat b) : mword 64))
                                        (i - 4)%nat)
                    /\ fd_least_closed fdv a
                    /\ fd_least_closed (<[a := FdOpen true false (FdPipe γp)]> fdv) b
                    /\ fdv' = <[b := FdOpen false true (FdPipe γp)]>
                                (<[a := FdOpen true false (FdPipe γp)]> fdv) ⌝ ∗
                  ualloc_at (ukn_fd N) l a (FdOpen true false (FdPipe γp)) ∗
                  ualloc_at (ukn_fd N) (ustd_after l (FdOpen true false (FdPipe γp))) b
                    (FdOpen false true (FdPipe γp)) ∗
                  ustd (ukn_fd N) (ustd_after
                              (ustd_after l (FdOpen true false (FdPipe γp)))
                              (FdOpen false true (FdPipe γp))))
               ∨ (⌜ r = (mword_of_int (-1) : mword 64) ⌝ ∗ ustd (ukn_fd N) l)))%I
      with "[Hufd Hstd]" as ">[Hufd Hhs]".
    { destruct (decide (uint r = 0)) as [Hr0 | Hr0].
      - destruct (Hsucc Hr0) as (a & b & γp & Hne & Hca & Hcb & Hfdv' & Hbytes).
        (* allocated in the ROW's own order: read end first, write end
           against the table -- and the ledger -- that left *)
        iMod (ufd_alloc_least (ukn_fd N) fdv l a (FdOpen true false (FdPipe γp)) Hca
                ltac:(discriminate) with "Hufd Hstd") as "[Hufd [Hstd Hha]]".
        iMod (ufd_alloc_least (ukn_fd N) (<[a := FdOpen true false (FdPipe γp)]> fdv)
                (ustd_after l (FdOpen true false (FdPipe γp))) b
                (FdOpen false true (FdPipe γp)) Hcb ltac:(discriminate)
                with "Hufd Hstd") as "[Hufd [Hstd Hhb]]".
        rewrite <- Hfdv'. iModIntro. iFrame "Hufd".
        iLeft. iExists a, b, γp. iFrame "Hha Hhb Hstd". iPureIntro.
        (* the last conjunct is [Hfdv'] itself: the rewrite above folded the
           AUTHORITY back to [fdv'], and the row inside the existential
           still names the two inserts *)
        split_and!;
          [ exact Hr0 | exact Hne
          | rewrite <- Hfdlen; exact (fd_least_closed_lt _ _ Hca)
          | rewrite <- Hfdlen; rewrite <- (length_insert fdv a
              (FdOpen true false (FdPipe γp))); exact (fd_least_closed_lt _ _ Hcb)
          | exact Hbytes | exact Hca | exact Hcb | exact Hfdv' ].
      - rewrite (proj2 (Hfail Hr0)). iModIntro. iFrame "Hufd".
        (* the arm names the VALUE now, not merely its nonzeroness *)
        iRight. iFrame "Hstd". iPureIntro. exact (proj1 (Hfail Hr0)). }
    (* ---- THE REGISTRAR RUNS HERE, at the one point where the post and
           the run's own reading are both in hand and the goal is the WP
           the call resumes into (durable-notes.md, "Iris": a [={E}=∗]
           lemma is absorbed by [fupd_wp], not by [iMod] on a [WP]).  What
           comes back is the two new rows' registration -- which is what
           [urun] is re-closed at -- and the caller's own [Rp]. ---- *)
    (* the resume key's own bundle is introduced FIRST, so that the goal is
       the WP the registrar's fancy update can be absorbed into *)
    iIntros "Hb2".
    iApply fupd_wp.
    iMod ("Hreg" $! fdep (uvis_of_run m pc M pm sz fdv cw gn cs pidv false secc_all) r
            (umem_write M (uint dst) dd gg) fdv' cw' cs
            with "[%] Hnp Hsp") as "[#Hnpr HRp]";
      [ exact (fun Hc => proj2 (Hfail Hc)) | ].
    iModIntro.
    iAssert (urun_rows N fdv') as "#Hnpo"; [ rewrite /urun_rows; iExact "Hnpr" | ].
    iDestruct (urun_close_upd N (umem_write M (uint dst) dd gg) pm m
                 (mword_of_int 10) r sz fdv' cw' gn cs pidv (add_vec_int pc 4) avail
                 ltac:(unfold unot_sp; vm_compute; discriminate)
                 with "Hheap Hstk Hufd Hcwda Hcha Hmy Hdep Hnpo [Hcont Hbuf Hhs HRp]") as "Hkc";
      [ iIntros (h'') "Hrun";
        iApply ("Hcont" $! h'' r gg
                  (uvis_of_run m pc M pm sz fdv cw gn cs pidv false secc_all) fdep
                  (umem_write M (uint dst) dd gg) fdv' cw' cs
                  with "Hhs HRp Hrun Hbuf") | ].
    iDestruct (ukcq_ukc with "Hkc") as "Hkc".
    iApply ("Hkc" $! h' xi' C' pt' Rfd' Rut' with "[%] [%] [%] Hb' Hb2");
      [ exact Hlo' | exact Hpm' | exact Hlzf' ].
  Qed.

  (* ------------------------------------------------------------------- *)
  (* THE READ ROW'S INSTANCE OF THE WINDOW LEAF -- sh's [getcmd] shape.     *)
  (* Nothing but [usyswin]'s read branch, taken once here so a program      *)
  (* does not have to unfold it: the buffer is a1, the count is a2 as an    *)
  (* [int], and the caller owns AT LEAST the count.  THE BASE LEAF          *)
  (* [wp_uk_ecall_read] (cat's) IS NOW A COROLLARY OF THIS ONE (lane RD-3): *)
  (* it asked for the exact non-negative count and returned the buffer at   *)
  (* unconstrained contents, and this one allows any owned run covering the *)
  (* cap and returns the written prefix's length [d] with the tail pinned   *)
  (* unchanged -- so it generalizes every part of it, modulo the ADDRESS    *)
  (* SPELLING, which is the one thing the derivation below has to pay for.  *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_uk_ecall_read_win (N : uk_names Σ) (h : CpuId) (m : regfile)
      (pc : mword 64) (cnt : Z) (k : nat) (f : nat -> bv 8) (avail : nat) :
    usysno m = USYS_read ->
    bv_signed (subrange_vec_dec (m !!! Regidx (mword_of_int 12)) 31 0 : mword 32)
      = cnt ->
    (Z.to_nat cnt <= k)%nat ->
    is_aligned_vaddr (Virtaddr (add_vec_int pc 4)) 2 = true ->
    uinstr_is (ukn_t N) pc false (ECALL tt) -∗
    urun N h m pc avail -∗
    udepw N m pc USYS_read -∗
    ubytes (ukn_d N) (uint (m !!! Regidx (mword_of_int 11))) k f -∗
    (∀ (h' : CpuId) (r : mword 64) (d : nat) (g : nat -> bv 8),
       ⌜ (d <= Z.to_nat cnt)%nat ⌝ -∗
       ⌜ forall j : nat, (d <= j < k)%nat -> g j = f j ⌝ -∗
       (* ...and WHAT IT ANSWERED: -1, or a count no larger than the one
          asked for ([UsysMemOk.usys_read_ret] at a2's count) *)
       ⌜ bv_signed r = -1 \/ (0 <= bv_signed r <= Z.max 0 cnt)%Z ⌝ -∗
       urun N h' (<[Regidx (mword_of_int 10) := r]> m)
         (add_vec_int pc 4) avail -∗
       ubytes (ukn_d N) (uint (m !!! Regidx (mword_of_int 11))) k g -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Hn Hcnt Hk Hal4. iIntros "#Hi Hrun Hsb Hbuf Hcont".
    assert (Hw : usyswin m USYS_read
                 = Some (m !!! Regidx (mword_of_int 11), Z.to_nat cnt)).
    { unfold usyswin.
      destruct (decide (USYS_read = USYS_wait)) as [Hc | _]; [ discriminate Hc | ].
      destruct (decide (USYS_read = USYS_pipe)) as [Hc | _]; [ discriminate Hc | ].
      destruct (decide (USYS_read = USYS_read)) as [_ | Hc];
        [ | exfalso; exact (Hc eq_refl) ].
      rewrite Hcnt. reflexivity. }
    iApply (wp_uk_ecall_window N h m pc USYS_read
              (m !!! Regidx (mword_of_int 11)) (Z.to_nat cnt) k f avail
              Hn Hw Hk
              (* read is none of the four -- by computation on the number *)
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              (* ...and read is not wait either, so the children reading it
                 opened at is the one it re-closes at *)
              ltac:(vm_compute; discriminate)
              ltac:(usys_range) ltac:(usys_range)
              Hal4 with "Hi Hrun Hsb Hbuf").
    iIntros (h' r d g) "%Hd %Hgf %Hrr Hrun Hbuf".
    iApply ("Hcont" $! h' r d g with "[%] [%] [%] Hrun Hbuf");
      [ exact Hd | exact Hgf | ].
    (* the row reads a2's count off the register file's own trapframe *)
    rewrite <- Hcnt. exact (Hrr eq_refl).
  Qed.

  (* ------------------------------------------------------------------- *)
  (* THE RUN'S NO-WRAP FACT, OFF [urun] RATHER THAN OFF THE HEAP.          *)
  (*                                                                      *)
  (* [uheap_ubytes_run] above is stated at the process's own [UserHeap.    *)
  (* uheap], and [urun] binds the image, the permission map and the break  *)
  (* existentially -- so a leaf that has NOT yet destructed the run cannot *)
  (* reach it, and a leaf that is about to APPLY another leaf must not.    *)
  (* This is the same reading taken at the run itself: the conclusion is   *)
  (* PURE, so neither the run nor the buffer is spent and the existential  *)
  (* can simply be opened and dropped.                                     *)
  (* ------------------------------------------------------------------- *)
  Lemma urun_ubytes_run (N : uk_names Σ) (h : CpuId) (m : regfile)
      (pc : mword 64) (avail : nat) (a : Z) (nb : nat) (f : nat -> bv 8) :
    urun N h m pc avail -∗ ubytes (ukn_d N) a nb f -∗
    ⌜ forall j : nat, (j < nb)%nat -> 0 <= a + Z.of_nat j < 2 ^ 38 ⌝.
  Proof using .
    iIntros "Hrun Hbs".
    iDestruct "Hrun" as (xi C pt Rfd Rut sz M pm fdv cw gn cs pidv)
      "(_ & _ & _ & _ & Hheap & _)".
    iDestruct (uheap_ubytes_run (ukn_t N) (ukn_d N) (ukn_s N) M pm sz
                 (DfracOwn 1) a nb f with "Hheap Hbs") as %Hb.
    iPureIntro. intros j Hj. exact (proj2 (Hb j Hj)).
  Qed.

  (* ------------------------------------------------------------------- *)
  (* ...AND THE BASE READ LEAF, AS A COROLLARY OF THE WINDOW FORM           *)
  (* (lane RD-3 -- the merge [wp_uk_ecall_read_win]'s header asked for).    *)
  (*                                                                       *)
  (* THE STATEMENT IS THE RETIRED WALK'S, WORD FOR WORD, so [UkCat]'s read  *)
  (* stub and every other caller survives: hand in the whole count as a run *)
  (* you own, get the whole count back at SOME contents.  Owning the whole  *)
  (* count is still the premise and still for the same reason -- the row    *)
  (* licenses a write anywhere in [buf .. buf+cnt) -- and the window leaf   *)
  (* asks for exactly that, at [k = cnt].                                   *)
  (*                                                                       *)
  (* THE ONE THING THE DERIVATION OWES IS THE ADDRESS SPELLING.  This leaf  *)
  (* names the destination by a [Z] tied to a1 through [mword_of_int]; the  *)
  (* window leaf names it by [uint] of the register itself.  The two agree  *)
  (* exactly where a byte is OWNED, because an owned address is below MAXVA *)
  (* ([urun_ubytes_run] above) -- and at a count of ZERO no byte is owned   *)
  (* and none is needed, since both spellings of an empty run are [emp].    *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_uk_ecall_read (N : uk_names Σ) (h : CpuId) (m : regfile)
      (pc : mword 64) (a : Z) (cnt : nat) (f : nat -> bv 8) (avail : nat) :
    usysno m = USYS_read ->
    m !!! Regidx (mword_of_int 11) = (mword_of_int a : mword 64) ->
    bv_signed (subrange_vec_dec (m !!! Regidx (mword_of_int 12)) 31 0
               : mword 32) = Z.of_nat cnt ->
    is_aligned_vaddr (Virtaddr (add_vec_int pc 4)) 2 = true ->
    uinstr_is (ukn_t N) pc false (ECALL tt) -∗
    ubytes (ukn_d N) a cnt f -∗
    urun N h m pc avail -∗
    udepw N m pc USYS_read -∗
    (∀ (h' : CpuId) (r : mword 64) (g : nat -> bv 8),
       (* WHAT IT ANSWERED (program-specs SS3.4c): the call failed, or it
          reports a count no larger than the one asked for *)
       ⌜ bv_signed r = -1 \/ (0 <= bv_signed r <= Z.of_nat cnt)%Z ⌝ -∗
       ubytes (ukn_d N) a cnt g -∗
       urun N h' (<[Regidx (mword_of_int 10) := r]> m)
         (add_vec_int pc 4) avail -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Hn Ha1 Hcnt Hal4.
    iIntros "#Hi Hbs Hrun Hsb Hcont".
    assert (Hk : (Z.to_nat (Z.of_nat cnt) <= cnt)%nat)
      by (rewrite Nat2Z.id; lia).
    (* the run does not wrap, off the ownership rather than off a premise *)
    iDestruct (urun_ubytes_run N h m pc avail a cnt f with "Hrun Hbs") as %Hb.
    destruct cnt as [| c].
    - (* THE EMPTY RUN: both spellings are [emp], so the window leaf's
         destination never has to be identified with this leaf's. *)
      iApply (wp_uk_ecall_read_win N h m pc (Z.of_nat 0%nat) 0%nat f avail
                Hn Hcnt Hk Hal4 with "Hi Hrun Hsb [Hbs]").
      { rewrite /ubytes /ubytesq /=. done. }
      iIntros (h' r d g) "_ _ %Hrr Hrun Hbuf".
      iApply ("Hcont" $! h' r g with "[%] [Hbuf] Hrun");
        [ rewrite Z.max_r in Hrr; [ exact Hrr | lia ] | ].
      rewrite /ubytes /ubytesq /=. done.
    - (* THE NONEMPTY RUN: the first owned byte is what identifies them *)
      assert (Hd : uint (m !!! Regidx (mword_of_int 11) : mword 64) = a).
      { destruct (Hb 0%nat ltac:(lia)) as [Hlo Hhi].
        rewrite Ha1. apply uint_moi. unfold Z64. lia. }
      iApply (wp_uk_ecall_read_win N h m pc (Z.of_nat (S c)) (S c) f avail
                Hn Hcnt Hk Hal4 with "Hi Hrun Hsb [Hbs]").
      { rewrite Hd. iExact "Hbs". }
      iIntros (h' r d g) "_ _ %Hrr Hrun Hbuf".
      iApply ("Hcont" $! h' r g with "[%] [Hbuf] Hrun");
        [ rewrite Z.max_r in Hrr; [ exact Hrr | lia ] | ].
      rewrite -Hd. iExact "Hbuf".
  Qed.

  (* ------------------------------------------------------------------- *)
  (* ecall, at READ -- THE LEAF THAT HANDS THE PROCESS ITS POST            *)
  (* (app-echo.md, lane CONS-CURSOR, C3).                                  *)
  (*                                                                       *)
  (* Every read leaf above binds its [spost_at] as [_].  That is why no    *)
  (* program has ever learned anything about the bytes it read: the        *)
  (* kernel's receipt reaches the round and is dropped there.  This leaf   *)
  (* is the same walk with the post KEPT, and it costs exactly two things  *)
  (* the other leaves do not pay:                                          *)
  (*                                                                       *)
  (*  - THE DEPOSIT MUST NAME ITS FAMILY.  [udepw]'s explicit disjunct     *)
  (*    hides it under an existential, which is fine while the post is     *)
  (*    thrown away and useless once it is not, so the premise here is     *)
  (*    [UkRun.udepwf_std] at the program's own [fdep].  That is also what *)
  (*    carries the reader TOKEN in: at the console the deposit's input    *)
  (*    arm IS [SpecFileread.fileread_in]'s console arm, an exclusive      *)
  (*    resource, which no [□]-shaped supplier could hold.                 *)
  (*  - THE KEY MUST BE EXPOSED, and it is the TRAPPING one.  A program    *)
  (*    reads its receipt out of the post by unfolding [spost_at] at its   *)
  (*    own number, which is [UexecExecInst.xv6_spost]'s read row.         *)
  (*                                                                       *)
  (* THE POST IS AT THE TRAPPING KEY (app-echo.md, lane OPEN-PIN, finding  *)
  (* (d); this lane's correction).  Row 5 reads FOUR things off the key the *)
  (* process TRAPPED from -- the descriptor argument [xk_a W 0], the        *)
  (* descriptor table [uvis_fd W] the arm is selected by, the buffer        *)
  (* address [xk_a W 1] and the count [xk_a W 2] -- and the returning bump  *)
  (* OVERWRITES a0, so a post stated at the resume key would speak of the   *)
  (* RETURN VALUE where it means the file descriptor.  So this body binds   *)
  (* the trapping key [W] itself, exactly as [wp_uk_ecall_open_recv] does,  *)
  (* with the three argument words tied to the caller's own register file   *)
  (* and the RESUME image [M'] beside it (the receipt names the bytes the   *)
  (* call left in the caller's buffer, which is what the resume image       *)
  (* holds).                                                                *)
  (*                                                                        *)
  (* ...AND THE CALLER'S DESCRIPTOR KNOWLEDGE IS WHAT MAKES THE RECEIPT     *)
  (* READABLE AT ALL: the arm is selected by [FdSlots.fd_st_of_key          *)
  (* (xk_a W 0) (uvis_fd W)], and a program holds no [uvis_fd W] -- [urun]  *)
  (* binds it existentially.  What it holds is either its LEDGER of the low *)
  (* [NSTD] slots or a HANDLE on one descriptor, so the walk takes the      *)
  (* resource [D] and the pure reading [K] of the key's table it buys, and  *)
  (* hands [K (uvis_fd W)] over.  Without it "fd 0 is the console" (or “fd  *)
  (* is my file”) says nothing about the arm this call took.                *)
  (*                                                                        *)
  (* THE DEPOSIT IS FIXED AT THE SAME READING ([udepwf_K] above), which is   *)
  (* the other half of the same point and the read's analogue of the open    *)
  (* leaf's cwd-fixed deposit: a supplier that spends the CONSOLE READER     *)
  (* TOKEN answers the console arm and no other, and which arm row 5 asks    *)
  (* for is decided by the key's own table -- while [UkRun.udepwf]'s ∀ binds *)
  (* it.                                                                     *)
  (*                                                                        *)
  (* THE BUFFER IS A PRECONDITION, as in [wp_uk_ecall_read_win]: the        *)
  (* caller owns the whole count at a1 going in and gets it back with the   *)
  (* written prefix moved and the tail pinned.                              *)
  (*                                                                        *)
  (* THE WALK IS [wp_uk_ecall_window]'s, with the post KEPT and the         *)
  (* descriptor agreement taken where both halves are in one hand.  IT IS   *)
  (* THE ONLY READ WALK (lane RD-4): [wp_uk_ecall_read_recv] below and      *)
  (* [UkReadFile.wp_uk_ecall_read_file] are its two answers.                *)
  (* ------------------------------------------------------------------- *)
  (* ------------------------------------------------------------------- *)
  (* THE DEPOSIT, FIXED AT WHATEVER THE CALLER KNOWS ABOUT THE KEY'S       *)
  (* TABLE (lane RD-4).                                                    *)
  (*                                                                       *)
  (* [UkRun.udepwf_std] fixes it at the low [NSTD] LEDGER and               *)
  (* [UkReadFile.udepwf_st] at the STATE one descriptor is in; the two      *)
  (* differ in the pure row inside the [forall] and NOWHERE ELSE, so the    *)
  (* family below is both of them, and the read walk takes it.  (It is not  *)
  (* [UkRun.udepwf_at]'s sibling: that one fixes the CWD, which no read     *)
  (* reads.)                                                               *)
  (* ------------------------------------------------------------------- *)
  Definition udepwf_K (N : uk_names Σ) (m : regfile) (pc : mword 64)
      (n : Z) (fdep : sfam) (K : list fdstate -> Prop) : iProp Σ :=
    (⌜sexit_pay fdep = ukn_pay N⌝ ∗
     ∀ (M : gmap Z (bv 8)) (pm : gmap (mword 27) uperm) (sz : Z)
       (fdv : list fdstate) (cw : Z) (gn : gname) (cs : gset gname)
       (pidv : mword 32),
       ⌜K fdv⌝ -∗
       my_pay gn (ukn_pay N) -∗
       uheap (ukn_t N) (ukn_d N) (ukn_s N) M pm sz -∗ ufd_auth (ukn_fd N) fdv -∗
       uheap (ukn_t N) (ukn_d N) (ukn_s N) M pm sz ∗ ufd_auth (ukn_fd N) fdv ∗
       sbundle_at uslot n fdep
         (uvis_of_run m pc M pm sz fdv cw gn cs pidv false secc_all))%I.

  Lemma udepwf_K_std (N : uk_names Σ) (m : regfile) (pc : mword 64)
      (n : Z) (fdep : sfam) (l : list fdstate) :
    udepwf_std N m pc n fdep l
    ⊣⊢ udepwf_K N m pc n fdep (fun fdv => take NSTD fdv = l).
  Proof using . rewrite /udepwf_std /udepwf_K. iSplit; iIntros "H"; iExact "H". Qed.

  Lemma wp_uk_ecall_read_at (N : uk_names Σ) (h : CpuId)
      (m : regfile) (pc : mword 64) (cnt : Z) (k : nat) (f : nat -> bv 8)
      (avail : nat) (fdep : sfam) (D : iProp Σ) (K : list fdstate -> Prop) :
    usysno m = USYS_read ->
    bv_signed (subrange_vec_dec (m !!! Regidx (mword_of_int 12)) 31 0
               : mword 32) = cnt ->
    (Z.to_nat cnt <= k)%nat ->
    is_aligned_vaddr (Virtaddr (add_vec_int pc 4)) 2 = true ->
    (* WHAT THE CALLER'S DESCRIPTOR KNOWLEDGE BUYS AGAINST THE KEY'S OWN
       TABLE.  The conclusion is PURE, so the reading costs neither the
       authority nor [D]; the ledger's answer and the handle's are the
       two instances. *)
    (forall fdv : list fdstate,
       ufd_auth (ukn_fd N) fdv -∗ D -∗ ⌜K fdv⌝) ->
    uinstr_is (ukn_t N) pc false (ECALL tt) -∗
    urun N h m pc avail -∗
    udepwf_K N m pc USYS_read fdep K -∗
    D -∗
    ubytes (ukn_d N) (uint (m !!! Regidx (mword_of_int 11))) k f -∗
    (∀ (h' : CpuId) (r : mword 64) (d : nat) (g : nat -> bv 8)
       (W : uvis) (M' : gmap Z (bv 8))
       (fdv' : list fdstate) (cw' : Z) (cs' : gset gname),
       ⌜ (d <= Z.to_nat cnt)%nat ⌝ -∗
       ⌜ forall j : nat, (d <= j < k)%nat -> g j = f j ⌝ -∗
       (* THE DESTINATION RUN IS LINEAR, and the RESUME IMAGE HOLDS THE
          BYTES (lane SH-LINE 2b, R1).  The post is stated at the resume
          image [M'] -- [SpecFileread.console_receipt]'s per-byte ledger
          reads the delivered bytes out of it -- while a program owns its
          buffer as [UkRun.ubytes] at a SOURCE FUNCTION.  These two pure
          rows are the bridge, and they can only be handed out here: [M']
          is [UserPtTree.umem_write] of an image [urun]'s own existential
          binds, so nothing above this leaf can state the equation.  The
          linearity row is the same fact [SpecFileread.console_receipt]'s
          ledger clause is guarded by, and it comes off the ownership of
          the buffer rather than off a premise
          ([UserHeap.uheap_ubytes_run]). *)
       ⌜ forall i : nat, (i < k)%nat ->
           uint (add_vec_int (m !!! Regidx (mword_of_int 11)) (Z.of_nat i))
           = (uint (m !!! Regidx (mword_of_int 11)) + Z.of_nat i)%Z ⌝ -∗
       ⌜ forall j : nat, (j < k)%nat ->
           M' !! uint (add_vec_int (m !!! Regidx (mword_of_int 11))
                         (Z.of_nat j))
           = Some (g j) ⌝ -∗
       (* ...AND EVERY BYTE OF THE DESTINATION IS WRITABLE-MAPPED IN ANY
          TABLE THE KEY'S PROJECTION ADMITS (lane SH-LINE 2b, R1; lane
          LAZY-FLAG's deliverable, CASHED).  [uk_read_nofault] above is
          stated at the process's own [UserHeap.uheap], and no program
          holds one: [UkRun.urun] binds the image, the permission map and
          the break existentially, so nothing above this leaf can tie
          [uvis_perm W] to a heap it owns.  This leaf can -- its key IS
          [UexecSlot.uvis_of_run] at the very map the heap is at -- so the
          refutation of [ConsoleInv.cons_swallow]'s copy-out disjunct is
          handed out from here, in the positive form
          [UConsLine.ush_swallow_nofault] consumes. *)
       ⌜ forall (P : uptd) (j : nat),
           ProcPtOwn.proc_pt_wf P ->
           perm_of (ud_um P) (uvis_sz W) = uvis_perm W ->
           lazy_free (ud_um P) (uvis_sz W) ->
           (j < k)%nat ->
           UserPtTree.uva_wmapped P
             (uint (add_vec_int (m !!! Regidx (mword_of_int 11))
                      (Z.of_nat j))) ⌝ -∗
       (* THE TRAPPING KEY'S THREE ARGUMENT WORDS ARE THE CALLER'S OWN *)
       ⌜tf_w (uvis_tf W) (tf_arg_idx 0) = m !!! Regidx (mword_of_int 10)⌝ -∗
       ⌜tf_w (uvis_tf W) (tf_arg_idx 1) = m !!! Regidx (mword_of_int 11)⌝ -∗
       ⌜tf_w (uvis_tf W) (tf_arg_idx 2) = m !!! Regidx (mword_of_int 12)⌝ -∗
       (* ...AND ITS LEDGER IS THE CALLER'S OWN TOO *)
       ⌜K (uvis_fd W)⌝ -∗
       (* ...AND ITS LAZY BIT IS [false] (lane LAZY-FLAG, L6 -- THE
          DELIVERABLE).  Definitional at this leaf: the U tier's run is at
          an empty fill ([UexecRet.ukcq] is hardwired at [false]), so the
          key the process trapped at says so.  It is handed back because
          the POST is where it is spent: row 5's [∃ P] carries
          [uvis_lazy W = false -> lazy_free (ud_um P) (uvis_sz W)], and with
          this equation in hand SH-LINE 2b turns it into [lazy_free] and
          eliminates [ConsoleInv.cons_swallow]'s copyout-fault disjunct by
          [uk_read_nofault] above. *)
       ⌜uvis_lazy W = false⌝ -∗
       (* ...AND THE ANSWER IS NOT -1 (lane TRAP-ROWS, T2(iii)).  A process
          that resumes was not killed, and usertrap's second [killed] check
          is where that is cashed: with the one-shot refuted,
          [SpecFileread.console_receipt]'s -1 arm has exactly one cause
          left, fileread's [n < 0] sign guard, and a caller that asked for
          a non-negative count has ruled that out too.  So AT AN OPEN
          READABLE CONSOLE DESCRIPTOR the read did not fail -- and the
          reason the row is guarded rather than flat is that a caller whose
          fd is closed, or not the console, or whose count is negative, HAS
          no such fact.  [UexecRet.uexec_live_ok] names the descriptor by
          index, which is the form a program holding its own table wants. *)
       ⌜uexec_live_ok USYS_read (uvis_tf W) (uvis_fd W) r cs'⌝ -∗
       (* the ledger comes straight back: read moves no descriptor *)
       D -∗
       (* THE POST, AT THE TRAPPING KEY AND THE RESUME IMAGE *)
       spost_at uslot USYS_read fdep W r M' fdv' cw' cs' -∗
       urun N h' (<[Regidx (mword_of_int 10) := r]> m)
         (add_vec_int pc 4) avail -∗
       ubytes (ukn_d N) (uint (m !!! Regidx (mword_of_int 11))) k g -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Hn Hcnt Hcapk Hal4 Hag.
    iIntros "#Hi Hrun Hsb Hstd Hbuf Hcont".
    set (dst := m !!! Regidx (mword_of_int 11) : mword 64).
    set (cap := Z.to_nat cnt).
    assert (Hwin : usyswin m USYS_read = Some (dst, cap)).
    { unfold usyswin.
      destruct (decide (USYS_read = USYS_wait)) as [Hc | _]; [ discriminate Hc | ].
      destruct (decide (USYS_read = USYS_pipe)) as [Hc | _]; [ discriminate Hc | ].
      destruct (decide (USYS_read = USYS_read)) as [_ | Hc];
        [ | exfalso; exact (Hc eq_refl) ].
      rewrite Hcnt. reflexivity. }
    iDestruct "Hrun" as (xi C pt Rfd Rut sz M pm fdv cw gn cs pidv) "(%Hlo & %Hpm & %Hlzf & %HRut & Hheap & Hstk & Hufd & Hcwda & Hcha & #Hmy & #Hdep & #Hnpx & Hb)".
    (* THE KEY'S LOW THREE SLOTS ARE THE CALLER'S OWN LEDGER, which is both
       what the deposit is stated at and what makes row 5's arm readable *)
    iDestruct (Hag fdv with "Hufd Hstd") as %Htake.
    iDestruct "Hsb" as "[%Hfp Hsb]".
    iDestruct ("Hsb" $! M pm sz fdv cw gn cs pidv with "[%] Hmy Hheap Hufd")
      as "(Hheap & Hufd & Hdepn)"; [ exact Htake | ].
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iDestruct (uvb_x0 with "Hb") as "[%Hx0 Hb]".
    (* THE NO-WRAP FACT, off the ownership rather than off a premise *)
    iDestruct (uheap_ubytes_run (ukn_t N) (ukn_d N) (ukn_s N) M pm sz (DfracOwn 1) (uint dst) k f
                 with "Hheap Hbuf") as %Hbnd.
    assert (Hlin : forall i : nat, (i < k)%nat ->
              uint (add_vec_int dst (Z.of_nat i)) = (uint dst + Z.of_nat i)%Z).
    { intros i Hi. destruct (Hbnd i Hi) as [_ Hc].
      change (2 ^ 38) with 274877906944 in Hc.
      rewrite !uint_unsigned in Hc |- *.
      apply uint_add_vec_int_small; lia. }
    (* ...AND THE DESTINATION'S PAGES ARE WRITABLE, taken HERE because this
       is the one place where the heap the process owns and the key's own
       permission map are the same term (the post's row above). *)
    iDestruct (uheap_ubytes_w (ukn_t N) (ukn_d N) (ukn_s N) M pm sz (DfracOwn 1) (uint dst) k f
                 with "Hheap Hbuf") as %Hwacc.
    assert (Hnf : forall (P : uptd) (j : nat),
              ProcPtOwn.proc_pt_wf P -> perm_of (ud_um P) sz = pm ->
              lazy_free (ud_um P) sz -> (j < k)%nat ->
              UserPtTree.uva_wmapped P (uint (add_vec_int dst (Z.of_nat j)))).
    { intros P j Hwf Hpmp Hlf Hjk.
      rewrite (Hlin j Hjk).
      destruct (Hbnd j Hjk) as [_ Hrange].
      apply (UserHeap.lazy_free_uw_addr P sz (uint dst + Z.of_nat j)%Z Hwf Hlf);
        [ exact Hrange | rewrite Hpmp; exact (Hwacc j Hjk) ]. }
    iApply (UkStep.wp_uk_ecall C pt Rfd Rut pm sz Hlo Hpm HRut Hlzf M m pc fdv cw gn cs pidv Hui
              (fun (s : mstate)
                   (Hp : register_lookup cur_privilege s.(sregs) = User)
                   (Hc : register_lookup (R_bitvector_64 PC) s.(sregs) = pc) =>
                 UserExecFacts.goodmb_execute_ECALL_U UserFrame.Du_r UserFrame.Du_w
                   s pc ltac:(vm_compute; reflexivity)
                   ltac:(vm_compute; reflexivity) Hp Hc)
              with "Hb Hmy").
    rewrite (uexec_ret_ecall _ _ eq_refl).
    assert (Hnum : uvis_num (uvis_of_run m pc M pm sz fdv cw gn cs pidv false secc_all) = USYS_read).
    { assert (Hraw : usys_num (uvis_tf (uvis_of_run m pc M pm sz fdv cw gn cs pidv false secc_all)) = USYS_read)
        by (cbn [uvis_tf uvis_of_run]; rewrite tf_of_num; exact Hn).
      rewrite uvis_num_full0; [ exact Hraw | reflexivity | rewrite Hraw; usys_range ]. }
    assert (Hw : usys_win USYS_read (uvis_tf (uvis_of_run m pc M pm sz fdv cw gn cs pidv false secc_all))
                 = Some (dst, cap)).
    { cbn [uvis_tf uvis_of_run]. rewrite usyswin_tf_of. exact Hwin. }
    rewrite /uexec_pay_dep /upay_at.
    pose proof Hnum as Hnume. unfold uvis_num in Hnume. rewrite ?Hnum ?Hnume. cbv zeta.
    destruct (decide (uecall_scause = uecall_scause)) as [_ | Hpne];
      [ | exfalso; exact (Hpne eq_refl) ].
    destruct (decide (USYS_read = USYS_exit)) as [He | _];
      [ exfalso; vm_compute in He; discriminate | ].
    destruct (decide (USYS_read = USYS_fork)) as [He | _];
      [ exfalso; vm_compute in He; discriminate | ].
    destruct (decide (USYS_read = USYS_wait)) as [He | _];
      [ exfalso; vm_compute in He; discriminate | ].
    iExists fdep. rewrite Hfp.
    cbn [uvis_gen uvis_of_run].
    iSplitR; [ iFrame "Hmy" | ].
    iSplitL "Hdepn"; [ iExact "Hdepn" | ].
    iIntros (r M' pm' sz' fdv' cw' gn' cs' lz' secc')
      \"%Hok %Hfdok %Hpiperow %Hcwrow %Hgnrow %Hpidrow %Hliverow %Hscrow %Hchrow Hpost".
    (* THE LAZY BIT CROSSED THE TRAP UNCHANGED (lane LAZY-FLAG, L6).  The
       trapping key is at [false] -- the U tier's run is
       ([UexecRet.ukcq]) -- and every row but sbrk's is the equation
       ([UsysMemOk.usys_mem_ok_lazy]), so the resume key is at [false] too
       and the close below is at the run's own bit. *)
    assert (Hlzq : lz' = false)
      by (refine (usys_mem_ok_lazy _ _ _ _ _ _ _ _ _ _ _ _ Hok);
          first [ assumption | vm_compute; discriminate ]).
    subst lz'.
    (* ...AND SO DID THE MASK: not seccomp's number, so the row is the
       equation ([UsysMemOk.usys_secc_ok_quiet]), and the resume key is at
       the full mask [urun] is keyed at *)
    pose proof (fun Hne => usys_secc_ok_quiet _ _ _ _ _ Hne Hscrow) as Hscq.
    specialize (Hscq ltac:(usys_range)).
    cbn [uvis_secc uvis_of_run] in Hscq. subst secc'.
    assert (Hcw : cw' = cw)
      by (refine (usys_cwd_ok_quiet _ _ _ _ _ Hcwrow); vm_compute; discriminate).
    iDestruct (ucwd_auth_quiet N cw cw' Hcw with "Hcwda") as "Hcwda".
    assert (Hgn : gn' = gn) by exact (usys_gen_ok_quiet _ _ _ Hgnrow).
    assert (Hch : cs' = cs) by exact (usys_ch_ok_quiet _ _ _ _ Hchrow).
    subst gn' cs'.
    destruct (usys_mem_ok_window USYS_read _ r _ _ _ _ _ _ _ _ dst cap Hw Hok)
      as ((d & bs & Hdcap & HM') & -> & ->).
    cbn [uvis_M uvis_perm uvis_sz uvis_of_run] in HM' |- *.
    assert (Hg : exists g : nat -> bv 8,
              (forall j : nat, (j < d)%nat -> g j = bs j) /\
              (forall j : nat, (d <= j)%nat -> g j = f j)).
    { exists (fun j => if decide (j < d)%nat then bs j else f j).
      split; intros j Hj; case_decide as Hc;
        [ reflexivity | exfalso; lia | exfalso; lia | reflexivity ]. }
    destruct Hg as (g & Hgb & Hgf).
    assert (Hdk : (d <= k)%nat) by (unfold cap in Hdcap; lia).
    rewrite (umem_wr_ext M dst d bs g
               ltac:(intros i Hi; symmetry; exact (Hgb i Hi))) in HM'.
    rewrite (umem_wr_write M dst d g
               ltac:(intros i Hi; apply Hlin; lia)) in HM'.
    subst M'.
    assert (Hview : fdv' = fdv).
    { refine (usys_fd_ok_quiet _ _ _ _ _ _ _ _ _ Hfdok);
        vm_compute; discriminate. }
    subst fdv'.
    rewrite (uslot_bump_run m pc M (umem_write M (uint dst) d g) pm pm sz sz
               fdv fdv cw cw' gn gn cs cs pidv false false secc_all secc_all r Hx0 Hal4).
    rewrite /ukc. iIntros (h' xi' C' pt' Rfd' Rut') "%Hlo' %Hpm' %Hlzf' Hb'".
    iEval (rewrite (ubytes_split (ukn_d N) (uint dst) d k f Hdk)) in "Hbuf".
    iDestruct "Hbuf" as "[Hblo Hbhi]".
    iMod (uheap_store_run (ukn_t N) (ukn_d N) (ukn_s N) M pm sz (uint dst) d f g with "Hheap Hblo")
      as "[Hheap Hblo]".
    iDestruct (ubytes_ext (ukn_d N) (uint dst + Z.of_nat d) (k - d)
                 (fun j => f (d + j)%nat) (fun j => g (d + j)%nat)
                 ltac:(intros j _; symmetry; apply Hgf; lia) with "Hbhi")
      as "Hbhi".
    iAssert (ubytes (ukn_d N) (uint dst) k g) with "[Hblo Hbhi]" as "Hbuf".
    { rewrite (ubytes_split (ukn_d N) (uint dst) d k g Hdk). iFrame "Hblo Hbhi". }
    iDestruct (urun_close_upd N (umem_write M (uint dst) d g) pm m
                 (mword_of_int 10) r sz fdv cw' gn cs pidv (add_vec_int pc 4) avail
                 ltac:(unfold unot_sp; vm_compute; discriminate)
                 with "Hheap Hstk Hufd Hcwda Hcha Hmy Hdep Hnpx [Hcont Hbuf Hstd Hpost]") as "Hkc".
    { iIntros (h'') "Hrun".
      iApply ("Hcont" $! h'' r d g (uvis_of_run m pc M pm sz fdv cw gn cs pidv false secc_all)
                _ _ _ _
                with "[%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] Hstd Hpost Hrun Hbuf").
      - exact Hdcap.
      - intros j Hj. apply Hgf; lia.
      (* the destination run is linear, off the ownership of the buffer *)
      - exact Hlin.
      (* ...and the resume image holds the buffer: the written prefix by
         [umem_write_lookup_in], the tail because the call did not touch it
         and the caller's own bytes are already in the image *)
      - intros j Hj. rewrite (Hlin j Hj).
        destruct (decide (j < d)%nat) as [Hjd | Hjd].
        + exact (umem_write_lookup_in M (uint dst) d g j Hjd).
        + rewrite (umem_write_lookup_out M (uint dst) d g
                     (uint dst + Z.of_nat j)%Z
                     ltac:(intros i Hi; lia)).
          destruct (Hbnd j Hj) as [HMj _]. rewrite HMj.
          rewrite (Hgf j ltac:(lia)). reflexivity.
      (* ...and every byte of it is writable-mapped: the key's projection
         IS the map the heap above was read at *)
      - intros P j Hwf Hpmp Hlf Hjk.
        cbn [uvis_sz uvis_perm uvis_of_run] in Hpmp, Hlf.
        exact (Hnf P j Hwf Hpmp Hlf Hjk).
      - rewrite /tf_w. cbn [uvis_tf uvis_of_run]. exact (tf_of_arg0 m pc).
      - rewrite /tf_w. cbn [uvis_tf uvis_of_run]. exact (tf_of_arg1 m pc).
      - rewrite /tf_w. cbn [uvis_tf uvis_of_run]. exact (tf_of_arg2 m pc).
      - rewrite (uvis_of_run_fd m pc M pm sz fdv cw gn cs pidv false secc_all). exact Htake.
      (* definitional: the run is at [false] *)
      - reflexivity.
      (* ...and what the resume proved, straight off the arm's own row
         (lane TRAP-ROWS, T2(iii)) *)
      - exact Hliverow. }
    iDestruct (ukcq_ukc with "Hkc") as "Hkc".
    iApply ("Hkc" $! h' xi' C' pt' Rfd' Rut' with "[%] [%] [%] Hb'");
      [ exact Hlo' | exact Hpm' | exact Hlzf' ].
  Qed.

  (* ------------------------------------------------------------------- *)
  (* ...AND ITS LEDGER-FIXED COROLLARY, AT ITS EXACT FORMER STATEMENT      *)
  (* (lane RD-4).                                                          *)
  (*                                                                       *)
  (* [wp_uk_ecall_read_recv] used to carry the walk above verbatim, and    *)
  (* [UkReadFile.wp_uk_ecall_read_file] carried a second copy of it: the   *)
  (* two differed in the DESCRIPTOR KNOWLEDGE and in nothing else, which   *)
  (* is the generalization the duplication was in disguise.  The walk is   *)
  (* now ONE; this is its LEDGER answer (a standard stream, read off       *)
  (* [UserFd.ustd]) and the file leaf is its HANDLE answer.  The statement *)
  (* is unchanged, so every caller is untouched.                           *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_uk_ecall_read_recv (N : uk_names Σ) (h : CpuId)
      (m : regfile) (pc : mword 64) (cnt : Z) (k : nat) (f : nat -> bv 8)
      (avail : nat) (fdep : sfam) (l : list fdstate) :
    usysno m = USYS_read ->
    bv_signed (subrange_vec_dec (m !!! Regidx (mword_of_int 12)) 31 0
               : mword 32) = cnt ->
    (Z.to_nat cnt <= k)%nat ->
    is_aligned_vaddr (Virtaddr (add_vec_int pc 4)) 2 = true ->
    uinstr_is (ukn_t N) pc false (ECALL tt) -∗
    urun N h m pc avail -∗
    udepwf_std N m pc USYS_read fdep l -∗
    UserFd.ustd (ukn_fd N) l -∗
    ubytes (ukn_d N) (uint (m !!! Regidx (mword_of_int 11))) k f -∗
    (∀ (h' : CpuId) (r : mword 64) (d : nat) (g : nat -> bv 8)
       (W : uvis) (M' : gmap Z (bv 8))
       (fdv' : list fdstate) (cw' : Z) (cs' : gset gname),
       ⌜ (d <= Z.to_nat cnt)%nat ⌝ -∗
       ⌜ forall j : nat, (d <= j < k)%nat -> g j = f j ⌝ -∗
       ⌜ forall i : nat, (i < k)%nat ->
           uint (add_vec_int (m !!! Regidx (mword_of_int 11)) (Z.of_nat i))
           = (uint (m !!! Regidx (mword_of_int 11)) + Z.of_nat i)%Z ⌝ -∗
       ⌜ forall j : nat, (j < k)%nat ->
           M' !! uint (add_vec_int (m !!! Regidx (mword_of_int 11))
                         (Z.of_nat j))
           = Some (g j) ⌝ -∗
       ⌜ forall (P : uptd) (j : nat),
           ProcPtOwn.proc_pt_wf P ->
           perm_of (ud_um P) (uvis_sz W) = uvis_perm W ->
           lazy_free (ud_um P) (uvis_sz W) ->
           (j < k)%nat ->
           UserPtTree.uva_wmapped P
             (uint (add_vec_int (m !!! Regidx (mword_of_int 11))
                      (Z.of_nat j))) ⌝ -∗
       ⌜tf_w (uvis_tf W) (tf_arg_idx 0) = m !!! Regidx (mword_of_int 10)⌝ -∗
       ⌜tf_w (uvis_tf W) (tf_arg_idx 1) = m !!! Regidx (mword_of_int 11)⌝ -∗
       ⌜tf_w (uvis_tf W) (tf_arg_idx 2) = m !!! Regidx (mword_of_int 12)⌝ -∗
       ⌜take NSTD (uvis_fd W) = l⌝ -∗
       ⌜uvis_lazy W = false⌝ -∗
       ⌜uexec_live_ok USYS_read (uvis_tf W) (uvis_fd W) r cs'⌝ -∗
       UserFd.ustd (ukn_fd N) l -∗
       spost_at uslot USYS_read fdep W r M' fdv' cw' cs' -∗
       urun N h' (<[Regidx (mword_of_int 10) := r]> m)
         (add_vec_int pc 4) avail -∗
       ubytes (ukn_d N) (uint (m !!! Regidx (mword_of_int 11))) k g -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Hn Hcnt Hcapk Hal4.
    iIntros "#Hi Hrun Hsb Hstd Hbuf Hcont".
    iApply (wp_uk_ecall_read_at N h m pc cnt k f avail fdep
              (UserFd.ustd (ukn_fd N) l) (fun fdv => take NSTD fdv = l)
              Hn Hcnt Hcapk Hal4
              (fun fdv => ustd_agree (ukn_fd N) fdv l)
              with "Hi Hrun [Hsb] Hstd Hbuf Hcont").
    iApply (udepwf_K_std N m pc USYS_read fdep l with "Hsb").
  Qed.

  (* ------------------------------------------------------------------- *)
  (* ecall, at OPEN -- THE LEAF THAT HANDS THE PROCESS ITS RECEIPT          *)
  (* (app-echo.md, lane OPEN-PIN, O4').                                     *)
  (*                                                                       *)
  (* [wp_uk_ecall_open] above is this walk with the post THROWN AWAY (it    *)
  (* binds [spost_at] as [_] at :785), which is why no program has ever     *)
  (* learned WHICH FILE its descriptor is on.  This is the same walk with   *)
  (* the post KEPT, and it costs the two things the read leaf's twin        *)
  (* ([wp_uk_ecall_read_recv]) costs plus one open owes and read does  *)
  (* not:                                                                   *)
  (*                                                                       *)
  (*  - THE DEPOSIT MUST NAME ITS FAMILY, so the premise is [UkRun.udepwf]  *)
  (*    at the program's own [fdep] -- at an [xfam] whose open families are *)
  (*    the PINNED ones ([PinnedOpen.pinned_open_bundle]).                  *)
  (*  - THE KEY MUST BE EXPOSED.  Row 15's post                             *)
  (*    ([UexecExecInst.xv6_spost], [SpecSysOpen.open_receipt]) reads FIVE  *)
  (*    things off the TRAPPING key -- the image [uvis_M W], the path       *)
  (*    pointer and the omode ([xk_a W 0] / [xk_a W 1]), the cwd, and the   *)
  (*    ENTRY descriptor table [uvis_fd W], which is the [sts] its          *)
  (*    [open_fd_rcpt] is stated over -- and the RESUME table [fdv'] beside *)
  (*    them.  So this body binds the trapping key [W] itself, with the two *)
  (*    argument words tied to the caller's own register file, and the      *)
  (*    resume components beside it.                                        *)
  (*  - AND THAT IS WHY THE POST IS AT [W] AND NOT AT THE RESUME KEY.       *)
  (*    [UexecSG.spost_at_cong] re-keys only across [UexecSG.skey_eq],      *)
  (*    whose five rows include [uvis_fd] and argument 0 -- and open moves  *)
  (*    the table and the returning bump overwrites a0 -- so the two keys   *)
  (*    are NOT congruent and the post cannot be restated at the resume     *)
  (*    key.  ([wp_uk_ecall_read_recv] above is at the trapping key    *)
  (*    for the same reason: read moves no descriptor, but its row reads    *)
  (*    [xk_a W 0] -- the descriptor argument -- and the resume key carries *)
  (*    the RETURNED a0 there.  It was stated at the resume key when        *)
  (*    OPEN-PIN found this; SH-LINE corrected it.)                         *)
  (*                                                                       *)
  (* THE LEDGER moves exactly as [wp_uk_ecall_open]'s does: the caller      *)
  (* hands its named ledger in and gets [UserFd.ualloc] at the descriptor   *)
  (* the ledger DECIDES, or the ledger back at [-1].  What the receipt adds *)
  (* is the descriptor's TYPE, which is the whole point.                    *)
  (*                                                                       *)
  (* THE WALK IS [wp_uk_ecall_open]'s, with the post KEPT and the two       *)
  (* agreements ([UserCwd.ucwd_agree], [UserFd.ustd_agree]) taken where     *)
  (* both halves are in one hand.                                          *)
  (* ------------------------------------------------------------------- *)
  (*  - AND THE DEPOSIT IS CWD-FIXED ([UkRun.udepwf_at]), which is the      *)
  (*    OTHER half of "the deposit must name its family".  A PINNED open    *)
  (*    bundle is about a PATH, and "console" names a file only relative to *)
  (*    the directory it is resolved from, so a supplier built out of       *)
  (*    [PinnedOpen.pinned_open_bundle] answers at ONE working directory    *)
  (*    and no other -- while [UkRun.udepwf]'s own ∀ binds [cw].  So this   *)
  (*    leaf takes the program's half of its cwd beside the deposit and     *)
  (*    hands it back, exactly as [wp_uk_ecall_exec_at_cwd] does, and the   *)
  (*    agreement against the key's own cwd happens HERE, where both halves *)
  (*    are in one hand.                                                    *)
  (*                                                                        *)
  (* THE TWO PURE ROWS ABOUT THE TRAPPING KEY ARE WHAT MAKE THE RECEIPT     *)
  (* READABLE.  The post speaks of [uvis_cwd W] (where the walk started)    *)
  (* and of [uvis_fd W] (the [sts] its [open_fd_rcpt] is stated over), and  *)
  (* a program holds neither -- [urun] binds both existentially.  What it   *)
  (* holds is its cwd half and its LEDGER, so the leaf reads the two        *)
  (* agreements off the authorities it has just destructed and hands them   *)
  (* over as facts: [uvis_cwd W = c] and [take NSTD (uvis_fd W) = l].       *)
  (* Without the second the receipt's descriptor row is about a table the   *)
  (* caller cannot identify with its own ledger, and the pinned open says   *)
  (* nothing about fd 0.                                                    *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_uk_ecall_open_recv (N : uk_names Σ) (h : CpuId)
      (m : regfile) (pc : mword 64) (l : list fdstate) (avail : nat)
      (fdep : sfam) (c : Z) :
    usysno m = USYS_open ->
    is_aligned_vaddr (Virtaddr (add_vec_int pc 4)) 2 = true ->
    uinstr_is (ukn_t N) pc false (ECALL tt) -∗
    urun N h m pc avail -∗
    (* the program's half of its working directory... *)
    UserCwd.ucwd (ukn_cwd N) c -∗
    (* ...and the deposit at every key whose cwd is that one inum, at the
       family the program will read its receipt at *)
    udepwf_at N m pc USYS_open fdep c -∗
    ustd (ukn_fd N) l -∗
    (∀ (h' : CpuId) (r : mword 64) (W : uvis)
       (M' : gmap Z (bv 8)) (fdv' : list fdstate) (cw' : Z)
       (cs' : gset gname),
       (* THE TRAPPING KEY'S TWO ARGUMENT WORDS ARE THE CALLER'S OWN, which
          is what lets a program that knows its image read its own path
          argument off the receipt ([ArgPath.arg_path_of] at [uvis_M W] and
          [tf_arg_idx 0]). *)
       ⌜tf_w (uvis_tf W) (tf_arg_idx 0) = m !!! Regidx (mword_of_int 10)⌝ -∗
       ⌜tf_w (uvis_tf W) (tf_arg_idx 1) = m !!! Regidx (mword_of_int 11)⌝ -∗
       (* ...AND ITS CWD AND ITS LEDGER ARE THE CALLER'S OWN TOO *)
       ⌜uvis_cwd W = c⌝ -∗
       ⌜take NSTD (uvis_fd W) = l⌝ -∗
       (* the ledger, exactly [wp_uk_ecall_open]'s two arms *)
       ((∃ (fd : nat) (rd wr : bool) (t : fdtype),
           ⌜r = (mword_of_int (Z.of_nat fd) : mword 64)
            /\ (fd < NOFILE)%nat
            (* ...AND IT IS NOT A PIPE (survey R4, lane SUP-ONE) -- see
               the [_recv_img] leaf below for why the fact is exported. *)
            /\ fdst_nopipe (FdOpen rd wr t)⌝ ∗
           ualloc (ukn_fd N) l fd (FdOpen rd wr t))
        ∨ (⌜r = (mword_of_int (-1) : mword 64)⌝ ∗ ustd (ukn_fd N) l)) -∗
       (* ...AND THE POST, at the TRAPPING key and the resume view *)
       spost_at uslot USYS_open fdep W r M' fdv' cw' cs' -∗
       UserCwd.ucwd (ukn_cwd N) c -∗
       urun N h' (<[Regidx (mword_of_int 10) := r]> m)
         (add_vec_int pc 4) avail -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Hn Hal4.
    iIntros "#Hi Hrun Hcwd Hsb Hstd Hcont".
    iDestruct "Hrun" as (xi C pt Rfd Rut sz M pm fdv cw gn cs pidv) "(%Hlo & %Hpm & %Hlzf & %HRut & Hheap & Hstk & Hufd & Hcwda & Hcha & #Hmy & #Hdep & #Hnpx & Hb)".
    (* the key's cwd IS the one the caller's PINNED bundle is stated at *)
    iDestruct (ucwd_agree with "Hcwda Hcwd") as %->.
    (* ...and the key's low three slots ARE the caller's own ledger, which
       is what makes the receipt's descriptor row readable at all *)
    iDestruct (ustd_agree (ukn_fd N) fdv l with "Hufd Hstd") as %Htake.
    (* the deposit, at the family the receipt will come back at *)
    iDestruct "Hsb" as "[%Hfp Hsb]".
    iDestruct ("Hsb" $! M pm sz fdv gn cs pidv with "Hmy Hheap Hufd")
      as "(Hheap & Hufd & Hdepn)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iDestruct (uvb_x0 with "Hb") as "[%Hx0 Hb]".
    iApply (UkStep.wp_uk_ecall C pt Rfd Rut pm sz Hlo Hpm HRut Hlzf M m pc fdv c gn cs pidv Hui
              (fun (s : mstate)
                   (Hp : register_lookup cur_privilege s.(sregs) = User)
                   (Hc : register_lookup (R_bitvector_64 PC) s.(sregs) = pc) =>
                 UserExecFacts.goodmb_execute_ECALL_U UserFrame.Du_r UserFrame.Du_w
                   s pc ltac:(vm_compute; reflexivity)
                   ltac:(vm_compute; reflexivity) Hp Hc)
              with "Hb Hmy").
    rewrite (uexec_ret_ecall _ _ eq_refl).
    assert (Hnum : uvis_num (uvis_of_run m pc M pm sz fdv c gn cs pidv false secc_all) = USYS_open).
    { assert (Hraw : usys_num (uvis_tf (uvis_of_run m pc M pm sz fdv c gn cs pidv false secc_all)) = USYS_open)
        by (cbn [uvis_tf uvis_of_run]; rewrite tf_of_num; exact Hn).
      rewrite uvis_num_full0; [ exact Hraw | reflexivity | rewrite Hraw; usys_range ]. }
    rewrite /uexec_pay_dep /upay_at.
    pose proof Hnum as Hnume. unfold uvis_num in Hnume. rewrite ?Hnum ?Hnume. cbv zeta.
    destruct (decide (uecall_scause = uecall_scause)) as [_ | Hpne];
      [ | exfalso; exact (Hpne eq_refl) ].
    destruct (decide (USYS_open = USYS_exit)) as [He | _];
      [ exfalso; vm_compute in He; discriminate | ].
    destruct (decide (USYS_open = USYS_fork)) as [He | _];
      [ exfalso; vm_compute in He; discriminate | ].
    iExists fdep. rewrite Hfp.
    cbn [uvis_gen uvis_of_run].
    iSplitR; [ iFrame "Hmy" | ].
    iSplitL "Hdepn"; [ iExact "Hdepn" | ].
    iIntros (r M' pm' sz' fdv' cw' gn' cs' lz' secc')
      \"%Hok %Hfdok %Hpiperow %Hcwrow %Hgnrow %Hpidrow %Hliverow %Hscrow %Hchrow Hpost".
    (* THE LAZY BIT CROSSED THE TRAP UNCHANGED (lane LAZY-FLAG, L6).  The
       trapping key is at [false] -- the U tier's run is
       ([UexecRet.ukcq]) -- and every row but sbrk's is the equation
       ([UsysMemOk.usys_mem_ok_lazy]), so the resume key is at [false] too
       and the close below is at the run's own bit. *)
    assert (Hlzq : lz' = false)
      by (refine (usys_mem_ok_lazy _ _ _ _ _ _ _ _ _ _ _ _ Hok);
          first [ assumption | vm_compute; discriminate ]).
    subst lz'.
    (* ...AND SO DID THE MASK: not seccomp's number, so the row is the
       equation ([UsysMemOk.usys_secc_ok_quiet]), and the resume key is at
       the full mask [urun] is keyed at *)
    pose proof (fun Hne => usys_secc_ok_quiet _ _ _ _ _ Hne Hscrow) as Hscq.
    specialize (Hscq ltac:(usys_range)).
    cbn [uvis_secc uvis_of_run] in Hscq. subst secc'.
    assert (Hcw : cw' = c)
      by (refine (usys_cwd_ok_quiet _ _ _ _ _ Hcwrow); vm_compute; discriminate).
    assert (Hgn : gn' = gn) by exact (usys_gen_ok_quiet _ _ _ Hgnrow).
    assert (Hch : cs' = cs) by exact (usys_ch_ok_quiet _ _ _ _ Hchrow).
    subst gn' cs' cw'.
    destruct (usys_mem_ok_quiet USYS_open _ r _ _ _ _ _ _ _ _
                ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)
                ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) Hok)
      as [-> [-> ->]].
    unfold usys_fd_ok in Hfdok.
    destruct (decide (USYS_open = USYS_close)) as [Hc | _]; [ discriminate Hc | ].
    destruct (decide (USYS_open = USYS_dup)) as [Hc | _]; [ discriminate Hc | ].
    destruct (decide (USYS_open = USYS_open)) as [_ | Hc];
      [ | exfalso; exact (Hc eq_refl) ].
    cbn [uvis_M uvis_perm uvis_fd uvis_of_run] in Hfdok |- *.
    iDestruct (ufd_auth_len with "Hufd") as %Hfdlen.
    iApply uslot_bupd.
    destruct Hfdok as [(fd & rd & wr & t & Hr & Hcl & -> & Hnpo) | [Hrm ->]].
    - (* A DESCRIPTOR CAME BACK, at the LOWEST free slot, and the RECEIPT
         says at which type *)
      iMod (ufd_alloc_least (ukn_fd N) fdv l fd (FdOpen rd wr t) Hcl
              ltac:(discriminate) with "Hufd Hstd") as "[Hufd Hh]".
      iModIntro.
      (* ...and open installs an inode or a device, never a pipe end *)
      iDestruct (urun_rows_insert N fdv fd (FdOpen rd wr t) Hnpo
                   with "Hnpx") as "#Hnpi".
      rewrite (uslot_bump_run m pc M M pm pm sz sz fdv
                 (<[fd := FdOpen rd wr t]> fdv) c c gn gn cs cs pidv false false secc_all secc_all r Hx0 Hal4).
      iApply ukcq_ukc.
      iApply (urun_close_upd _ _ _ m (mword_of_int 10) _ _ _ _ _ _ _ _ _
                ltac:(unfold unot_sp; vm_compute; discriminate)
                with "Hheap Hstk Hufd Hcwda Hcha Hmy Hdep Hnpi").
      iIntros (h') "Hrun".
      iApply ("Hcont" $! h' r (uvis_of_run m pc M pm sz fdv c gn cs pidv false secc_all)
                _ _ _ _ with "[%] [%] [%] [%] [Hh] Hpost Hcwd Hrun").
      { rewrite /tf_w. cbn [uvis_tf uvis_of_run]. exact (tf_of_arg0 m pc). }
      { rewrite /tf_w. cbn [uvis_tf uvis_of_run]. exact (tf_of_arg1 m pc). }
      { exact (uvis_of_run_cwd m pc M pm sz fdv c gn cs pidv false secc_all). }
      { rewrite (uvis_of_run_fd m pc M pm sz fdv c gn cs pidv false secc_all). exact Htake. }
      iLeft. iExists fd, rd, wr, t. iFrame "Hh". iPureIntro.
      split_and!; [ exact Hr | | exact Hnpo ].
      rewrite <- Hfdlen. exact (fd_least_closed_lt _ _ Hcl).
    - (* the call failed: nothing moved, and the ledger comes straight back *)
      iModIntro.
      rewrite (uslot_bump_run m pc M M pm pm sz sz fdv fdv c c gn gn cs cs pidv false false secc_all secc_all r Hx0 Hal4).
      iApply ukcq_ukc.
      iApply (urun_close_upd _ _ _ m (mword_of_int 10) _ _ _ _ _ _ _ _ _
                ltac:(unfold unot_sp; vm_compute; discriminate)
                with "Hheap Hstk Hufd Hcwda Hcha Hmy Hdep Hnpx").
      iIntros (h') "Hrun".
      iApply ("Hcont" $! h' r (uvis_of_run m pc M pm sz fdv c gn cs pidv false secc_all)
                _ _ _ _ with "[%] [%] [%] [%] [Hstd] Hpost Hcwd Hrun").
      { rewrite /tf_w. cbn [uvis_tf uvis_of_run]. exact (tf_of_arg0 m pc). }
      { rewrite /tf_w. cbn [uvis_tf uvis_of_run]. exact (tf_of_arg1 m pc). }
      { exact (uvis_of_run_cwd m pc M pm sz fdv c gn cs pidv false secc_all). }
      { rewrite (uvis_of_run_fd m pc M pm sz fdv c gn cs pidv false secc_all). exact Htake. }
      iRight. iFrame "Hstd". iPureIntro. exact Hrm.
  Qed.

  (* ------------------------------------------------------------------- *)
  (* ecall, at a QUIET syscall -- THE LEAF THAT HANDS THE PROCESS ITS       *)
  (* RECEIPT (app-echo.md, lane OPEN-PIN, /init's mknod).                   *)
  (*                                                                       *)
  (* [wp_uk_ecall_quiet] above is this walk with the post THROWN AWAY.  Two *)
  (* of the numbers it covers DO have a contract and DO pay a post --       *)
  (* mknod (17) and unlink (18), and link (19) and mkdir (20) beside them   *)
  (* ([UexecExecInst.xv6_spost]) -- and /init's console repair arm is the   *)
  (* first caller in the tree that has to read one: its mknod is what       *)
  (* CREATES the console device node, so the flag its second open's pin     *)
  (* runs on ([AppEcho.cons_made]) can only come out of this post.          *)
  (*                                                                       *)
  (* THE POST IS AT THE TRAPPING KEY, for the open leaf's reason and more   *)
  (* sharply: row 17 reads THREE argument words off the key (the path       *)
  (* pointer and the two device numbers) as well as the image and the cwd,  *)
  (* and the returning bump overwrites a0.                                  *)
  (*                                                                       *)
  (* THE RESUME COMPONENTS ARE THE TRAPPING ONES, because the row IS the    *)
  (* quiet row: the image, the descriptor view and the working directory    *)
  (* all cross the trap unchanged ([UsysMemOk.usys_mem_ok_quiet] /          *)
  (* [usys_fd_ok_quiet] / [usys_cwd_ok_quiet] under the guards), so the     *)
  (* post's [M'] / [fdv'] / [cw'] are spelled as [uvis_M W] / [uvis_fd W] / *)
  (* [c] rather than bound -- which is what lets a caller apply a receipt   *)
  (* stated over the view it went in at.                                    *)
  (*                                                                       *)
  (* THE WALK IS [wp_uk_ecall_quiet]'s, with the post KEPT and the cwd      *)
  (* agreement taken where both halves are in one hand.                     *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_uk_ecall_quiet_recv (N : uk_names Σ) (h : CpuId)
      (m : regfile) (pc : mword 64) (n : Z) (avail : nat) (fdep : sfam)
      (c : Z) :
    usysno m = n ->
    n <> USYS_exit -> n <> USYS_fork ->
    n <> USYS_exec -> n <> USYS_sbrk ->
    n <> USYS_wait -> n <> USYS_pipe -> n <> USYS_read -> n <> USYS_fstat ->
    n <> USYS_close -> n <> USYS_dup -> n <> USYS_open ->
    n <> USYS_chdir ->
    is_aligned_vaddr (Virtaddr (add_vec_int pc 4)) 2 = true ->
    uinstr_is (ukn_t N) pc false (ECALL tt) -∗
    urun N h m pc avail -∗
    UserCwd.ucwd (ukn_cwd N) c -∗
    udepwf_at N m pc n fdep c -∗
    (∀ (h' : CpuId) (r : mword 64) (W : uvis) (cs' : gset gname),
       ⌜tf_w (uvis_tf W) (tf_arg_idx 0) = m !!! Regidx (mword_of_int 10)⌝ -∗
       ⌜tf_w (uvis_tf W) (tf_arg_idx 1) = m !!! Regidx (mword_of_int 11)⌝ -∗
       ⌜tf_w (uvis_tf W) (tf_arg_idx 2) = m !!! Regidx (mword_of_int 12)⌝ -∗
       ⌜uvis_cwd W = c⌝ -∗
       spost_at uslot n fdep W r (uvis_M W) (uvis_fd W) c cs' -∗
       UserCwd.ucwd (ukn_cwd N) c -∗
       urun N h' (<[Regidx (mword_of_int 10) := r]> m)
         (add_vec_int pc 4) avail -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Hn Hexit Hfork Hexec Hsbrk H3 H4 H5 H8 Hcl Hdp Hop Hcd Hal4.
    iIntros "#Hi Hrun Hcwd Hsb Hcont".
    iDestruct "Hrun" as (xi C pt Rfd Rut sz M pm fdv cw gn cs pidv) "(%Hlo & %Hpm & %Hlzf & %HRut & Hheap & Hstk & Hufd & Hcwda & Hcha & #Hmy & #Hdep & #Hnpx & Hb)".
    iDestruct (ucwd_agree with "Hcwda Hcwd") as %->.
    iDestruct "Hsb" as "[%Hfp Hsb]".
    iDestruct ("Hsb" $! M pm sz fdv gn cs pidv with "Hmy Hheap Hufd")
      as "(Hheap & Hufd & Hdepn)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iDestruct (uvb_x0 with "Hb") as "[%Hx0 Hb]".
    iApply (UkStep.wp_uk_ecall C pt Rfd Rut pm sz Hlo Hpm HRut Hlzf M m pc fdv c gn cs pidv Hui
              (fun (s : mstate)
                   (Hp : register_lookup cur_privilege s.(sregs) = User)
                   (Hc : register_lookup (R_bitvector_64 PC) s.(sregs) = pc) =>
                 UserExecFacts.goodmb_execute_ECALL_U UserFrame.Du_r UserFrame.Du_w
                   s pc ltac:(vm_compute; reflexivity)
                   ltac:(vm_compute; reflexivity) Hp Hc)
              with "Hb Hmy").
    rewrite (uexec_ret_ecall _ _ eq_refl).
    assert (Hnum : uvis_num (uvis_of_run m pc M pm sz fdv c gn cs pidv false secc_all) = n).
    { assert (Hraw : usys_num (uvis_tf (uvis_of_run m pc M pm sz fdv c gn cs pidv false secc_all)) = n)
        by (cbn [uvis_tf uvis_of_run]; rewrite tf_of_num; exact Hn).
      rewrite uvis_num_full0; [ exact Hraw | reflexivity | rewrite Hraw; usys_range ]. }
    rewrite /uexec_pay_dep /upay_at.
    pose proof Hnum as Hnume. unfold uvis_num in Hnume. rewrite ?Hnum ?Hnume. cbv zeta.
    destruct (decide (uecall_scause = uecall_scause)) as [_ | Hpne];
      [ | exfalso; exact (Hpne eq_refl) ].
    destruct (decide (n = USYS_exit)) as [He | _]; [ exfalso; exact (Hexit He) | ].
    destruct (decide (n = USYS_fork)) as [He | _]; [ exfalso; exact (Hfork He) | ].
    destruct (decide (n = USYS_wait)) as [He | _]; [ exfalso; exact (H3 He) | ].
    iExists fdep. rewrite Hfp.
    cbn [uvis_gen uvis_of_run].
    iSplitR; [ iFrame "Hmy" | ].
    iSplitL "Hdepn"; [ iExact "Hdepn" | ].
    iIntros (r M' pm' sz' fdv' cw' gn' cs' lz' secc')
      \"%Hok %Hfdok %Hpiperow %Hcwrow %Hgnrow %Hpidrow %Hliverow %Hscrow %Hchrow Hpost".
    (* THE LAZY BIT CROSSED THE TRAP UNCHANGED (lane LAZY-FLAG, L6).  The
       trapping key is at [false] -- the U tier's run is
       ([UexecRet.ukcq]) -- and every row but sbrk's is the equation
       ([UsysMemOk.usys_mem_ok_lazy]), so the resume key is at [false] too
       and the close below is at the run's own bit. *)
    assert (Hlzq : lz' = false)
      by (refine (usys_mem_ok_lazy _ _ _ _ _ _ _ _ _ _ _ _ Hok);
          first [ assumption | vm_compute; discriminate ]).
    subst lz'.
    (* ...AND SO DID THE MASK: not seccomp's number, so the row is the
       equation ([UsysMemOk.usys_secc_ok_quiet]), and the resume key is at
       the full mask [urun] is keyed at *)
    pose proof (fun Hne => usys_secc_ok_quiet _ _ _ _ _ Hne Hscrow) as Hscq.
    specialize (Hscq ltac:(usys_range)).
    cbn [uvis_secc uvis_of_run] in Hscq. subst secc'.
    assert (Hcw : cw' = c) by (exact (usys_cwd_ok_quiet n r c cw' Hcd Hcwrow)).
    assert (Hgn : gn' = gn) by exact (usys_gen_ok_quiet _ _ _ Hgnrow).
    assert (Hch : cs' = cs) by exact (usys_ch_ok_quiet _ _ _ _ Hchrow).
    subst gn' cs' cw'.
    destruct (usys_mem_ok_quiet n _ r _ _ _ _ _ _ _ _ Hexec Hsbrk H3 H4 H5 H8 Hok)
      as [-> [-> ->]].
    pose proof (usys_fd_ok_quiet n _ r _ _ Hcl Hdp Hop H4 Hfdok) as ->.
    cbn [uvis_M uvis_perm uvis_of_run].
    rewrite (uslot_bump_run m pc M M pm pm sz sz fdv fdv c c gn gn cs cs pidv false false secc_all secc_all r Hx0 Hal4).
    iApply ukcq_ukc.
    iApply (urun_close_upd _ _ _ m (mword_of_int 10) _ _ _ _ _ _ _ _ _
              ltac:(unfold unot_sp; vm_compute; discriminate)
              with "Hheap Hstk Hufd Hcwda Hcha Hmy Hdep Hnpx").
    iIntros (h') "Hrun".
    iApply ("Hcont" $! h' r (uvis_of_run m pc M pm sz fdv c gn cs pidv false secc_all) cs
              with "[%] [%] [%] [%] [Hpost] Hcwd Hrun").
    { rewrite /tf_w. cbn [uvis_tf uvis_of_run]. exact (tf_of_arg0 m pc). }
    { rewrite /tf_w. cbn [uvis_tf uvis_of_run]. exact (tf_of_arg1 m pc). }
    { rewrite /tf_w. cbn [uvis_tf uvis_of_run]. exact (tf_of_arg2 m pc). }
    { exact (uvis_of_run_cwd m pc M pm sz fdv c gn cs pidv false secc_all). }
    rewrite (uvis_of_run_fd m pc M pm sz fdv c gn cs pidv false secc_all).
    cbn [uvis_M uvis_of_run]. iExact "Hpost".
  Qed.

  (* ------------------------------------------------------------------- *)
  (* THE RUN, AS THE OUTPUT CHAIN'S PER-BYTE PREMISE                       *)
  (* (app-echo.md, lane IO-LEAF, (W)).                                     *)
  (*                                                                       *)
  (* [SpecConsolewrite.cons_out_chain]'s node at cursor [k] is quantified   *)
  (* over the byte the image holds at [uint (add_vec_int ua (Z.of_nat k))]  *)
  (* -- the MACHINE-WORD addressing, because that is how consolewrite       *)
  (* walks its buffer -- while a program owns its output run as             *)
  (* [UserHeap.ubytesq] at a base [Z] and a source function.  This is the   *)
  (* bridge, and it is [uheap_ubytes_run] above with its own no-wrap fact   *)
  (* spent: the run's canonicity clause bounds every index below 2^38, so   *)
  (* the word add does not wrap and the two addressings agree.              *)
  (*                                                                       *)
  (* It is stated HERE rather than in [UserHeap.v] for the dev loop's       *)
  (* reason ([durable-notes.md]: put an ADDITIVE change to a shared         *)
  (* invariant file in a NEW leaf file); nothing below this file needs it.  *)
  (* ------------------------------------------------------------------- *)
  Lemma uheap_ubytes_wat (γt γd γs : gname) (M : gmap Z (bv 8))
      (pmv : gmap (mword 27) uperm) (sz : Z) (dq : dfrac)
      (ua : mword 64) (nb : nat) (f : nat -> bv 8) :
    uheap γt γd γs M pmv sz -∗ ubytesq γd dq (uint ua) nb f -∗
    ⌜ forall j : nat, (j < nb)%nat ->
        M !! uint (add_vec_int ua (Z.of_nat j)) = Some (f j) ⌝.
  Proof using .
    iIntros "Hheap Hbs".
    iDestruct (uheap_ubytes_run γt γd γs M pmv sz dq (uint ua) nb f
                 with "Hheap Hbs") as %Hrun.
    iPureIntro. intros j Hj.
    destruct (Hrun j Hj) as [HM Hc].
    assert (Hadd : uint (add_vec_int ua (Z.of_nat j)) = (uint ua + Z.of_nat j)%Z).
    { change (2 ^ 38) with 274877906944 in Hc.
      rewrite !uint_unsigned in Hc |- *.
      apply uint_add_vec_int_small; lia. }
    rewrite Hadd. exact HM.
  Qed.

  (* ------------------------------------------------------------------- *)
  (* THE SOURCE RUN'S TWO ROWS, AS ONE READING (lane RD-6).                *)
  (*                                                                       *)
  (* A write LENDS the kernel a run of the caller's own memory, and the two *)
  (* facts a write leaf has to hand out about it are both facts about the   *)
  (* TRAPPING KEY that no caller can state -- [UkRun.urun] binds the image, *)
  (* the permission map and the break existentially:                        *)
  (*                                                                       *)
  (*   THE IMAGE ROW: the bytes the key's image holds along the run ARE the *)
  (*   caller's own source function.  It is what turns every “the caller    *)
  (*   justified the byte the image holds here”                             *)
  (*   ([SpecConsolewrite.cons_out_chain]'s node, [SpecCopyin.ubytes_at]    *)
  (*   inside [SpecFilewrite.write_post_ok_at]) into a statement about the   *)
  (*   bytes the PROGRAM has.                                              *)
  (*                                                                       *)
  (*   THE MAPPED ROW: every byte of the run is readable-mapped in any      *)
  (*   table the key's projection admits, which is what refutes the short   *)
  (*   arm ([SpecFilewrite.write_cons_short]).                             *)
  (*                                                                       *)
  (* Stated once, as a Prop about the key's three projections, so that the  *)
  (* one write walk below takes ONE premise and hands back ONE fact however *)
  (* the caller's run is filed -- the DATA half ([UserHeap.ubytesq]) and    *)
  (* the TEXT half ([UserHeap.utext], a string literal) are its two         *)
  (* answers, and they are the two the tree has.                            *)
  (* ------------------------------------------------------------------- *)
  Definition usrc_ok (M : gmap Z (bv 8)) (pmv : gmap (mword 27) uperm)
      (sz : Z) (ua : mword 64) (nb : nat) (f : nat -> bv 8) : Prop :=
    (forall j : nat, (j < nb)%nat ->
       M !! uint (add_vec_int ua (Z.of_nat j)) = Some (f j))
    /\ (forall (P : uptd) (j : nat),
          ProcPtOwn.proc_pt_wf P ->
          perm_of (ud_um P) sz = pmv ->
          lazy_free (ud_um P) sz ->
          (j < nb)%nat ->
          UserPtTree.uva_rmapped P (uint (add_vec_int ua (Z.of_nat j)))).

  (* THE DATA ANSWER: a run the caller OWNS.  Its pages are writable
     ([uheap_ubytes_w]), hence readable through under [lazy_free]. *)
  Lemma usrc_ok_ubytesq (γt γd γs : gname) (M : gmap Z (bv 8))
      (pmv : gmap (mword 27) uperm) (sz : Z) (dq : dfrac)
      (ua : mword 64) (nb : nat) (f : nat -> bv 8) :
    uheap γt γd γs M pmv sz -∗ ubytesq γd dq (uint ua) nb f -∗
    ⌜usrc_ok M pmv sz ua nb f⌝.
  Proof using .
    iIntros "Hheap Hbs".
    iDestruct (uheap_ubytes_run γt γd γs M pmv sz dq (uint ua) nb f
                 with "Hheap Hbs") as %Hbnd.
    iDestruct (uheap_ubytes_w γt γd γs M pmv sz dq (uint ua) nb f
                 with "Hheap Hbs") as %Hwacc.
    iPureIntro.
    assert (Hlin : forall j : nat, (j < nb)%nat ->
              uint (add_vec_int ua (Z.of_nat j)) = (uint ua + Z.of_nat j)%Z).
    { intros j Hj. destruct (Hbnd j Hj) as [_ Hc].
      change (2 ^ 38) with 274877906944 in Hc.
      rewrite !uint_unsigned in Hc |- *.
      apply uint_add_vec_int_small; lia. }
    split.
    - intros j Hj. rewrite (Hlin j Hj). exact (proj1 (Hbnd j Hj)).
    - intros P j Hwf Hpmp Hlf Hj. rewrite (Hlin j Hj).
      destruct (Hbnd j Hj) as [_ Hrange].
      apply UserPtTree.uva_rmapped_of_wmapped.
      apply (UserHeap.lazy_free_uw_addr P sz (uint ua + Z.of_nat j)%Z Hwf Hlf);
        [ exact Hrange | rewrite Hpmp; exact (Hwacc j Hj) ].
  Qed.

  (* THE TEXT ANSWER: a STRING LITERAL, which no [ubytesq] exists of --
     .rodata is X-and-NOT-W and is filed under the text gname.  The row is
     one test weaker and still true: a page the projection lists at all is a
     real user leaf, so under [lazy_free] the fetchable page is
     readable-mapped ([UserHeap.lazy_free_ux_addr]). *)
  Lemma usrc_ok_utext (γt γd γs : gname) (M : gmap Z (bv 8))
      (pmv : gmap (mword 27) uperm) (sz : Z)
      (ua : mword 64) (nb : nat) (f : nat -> bv 8) :
    uheap γt γd γs M pmv sz -∗
    ([∗ list] j ∈ seq 0 nb, utext γt (uint ua + Z.of_nat j)%Z (f j)) -∗
    ⌜usrc_ok M pmv sz ua nb f⌝.
  Proof using .
    iIntros "Hheap Hbs".
    iDestruct (uheap_text_bytes γt γd γs M pmv sz (uint ua) nb f
                 with "Hheap Hbs") as %Hbnd.
    iPureIntro.
    assert (Hlin : forall j : nat, (j < nb)%nat ->
              uint (add_vec_int ua (Z.of_nat j)) = (uint ua + Z.of_nat j)%Z).
    { intros j Hj. destruct (Hbnd j Hj) as (_ & _ & Hc).
      change (2 ^ 38) with 274877906944 in Hc.
      rewrite !uint_unsigned in Hc |- *.
      apply uint_add_vec_int_small; lia. }
    split.
    - intros j Hj. rewrite (Hlin j Hj).
      exact (proj1 (Hbnd j Hj)).
    - intros P j Hwf Hpmp Hlf Hj. rewrite (Hlin j Hj).
      destruct (Hbnd j Hj) as (_ & Hxacc & Hrange).
      apply (UserHeap.lazy_free_ux_addr P sz (uint ua + Z.of_nat j)%Z Hwf Hlf);
        [ exact Hrange | rewrite Hpmp; exact Hxacc ].
  Qed.

  (* ------------------------------------------------------------------- *)
  (* ecall, at WRITE (16) -- THE ONE WRITE WALK (lane RD-6).               *)
  (*                                                                       *)
  (* [wp_uk_ecall_read_at] above is the one READ walk; this is its twin,    *)
  (* and it is parametric in the same two things plus one the read side     *)
  (* does not have:                                                        *)
  (*                                                                       *)
  (*   D / K -- THE CALLER'S DESCRIPTOR KNOWLEDGE.  Which arm               *)
  (*   [SpecFilewrite.filewrite_in] takes is decided by the KEY's own       *)
  (*   table ([FdSlots.fd_st_of_key] at argument 0), and a program holds    *)
  (*   either its LEDGER of the low [NSTD] slots ([UserFd.ustd_agree]) or a *)
  (*   HANDLE on one descriptor ([UserFd.ufd_agree]).  Before this lane the *)
  (*   write leaves were LEDGER-ONLY, which is exactly why no U-tier write  *)
  (*   could reach the INODE arm: an opened file is never a standard        *)
  (*   stream.                                                             *)
  (*                                                                       *)
  (*   S / [usrc_ok] -- THE CALLER'S SOURCE RUN.  A write lends bytes, so   *)
  (*   there is a second resource that has to cross the walk and come back, *)
  (*   and the two facts about it that only this leaf can state are         *)
  (*   [usrc_ok] above.  [wp_uk_ecall_write_chain_buf] and                  *)
  (*   [wp_uk_ecall_write_chain_txt] were two copies of this walk that      *)
  (*   differed in nothing else; they are its two corollaries below, at     *)
  (*   their exact former statements, so every caller is untouched.         *)
  (*                                                                       *)
  (* THE DEPOSIT IS FIXED AT THE SAME READING ([udepwf_K], which is         *)
  (* syscall-generic and was cut for read), for the read walk's reason: a   *)
  (* supplier built out of an output chain answers the DEVICE arm and one   *)
  (* built out of an [FsAbsWriteFire.awrite_chain] the INODE arm, and       *)
  (* [UkRun.udepwf]'s own forall binds the table that decides.              *)
  (*                                                                       *)
  (* NO IMAGE MOVES and NO DESCRIPTOR MOVES: 16 is a quiet row, so the post *)
  (* is at the trapping key's own image and table, and the walk is          *)
  (* [wp_uk_ecall_quiet_recv]'s.                                           *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_uk_ecall_write_at (N : uk_names Σ) (h : CpuId)
      (m : regfile) (pc : mword 64) (avail : nat) (fdep : sfam)
      (D S : iProp Σ) (K : list fdstate -> Prop)
      (nb : nat) (f : nat -> bv 8) :
    usysno m = 16 ->
    is_aligned_vaddr (Virtaddr (add_vec_int pc 4)) 2 = true ->
    (* WHAT THE CALLER'S DESCRIPTOR KNOWLEDGE BUYS AGAINST THE KEY'S OWN
       TABLE -- the read walk's premise, verbatim. *)
    (forall fdv : list fdstate,
       ufd_auth (ukn_fd N) fdv -∗ D -∗ ⌜K fdv⌝) ->
    (* ...AND WHAT ITS SOURCE RUN BUYS AGAINST THE KEY'S OWN IMAGE AND
       PERMISSION MAP.  The conclusion is PURE, so the reading costs
       neither the heap authority nor [S]. *)
    (forall (M : gmap Z (bv 8)) (pmv : gmap (mword 27) uperm) (sz : Z),
       uheap (ukn_t N) (ukn_d N) (ukn_s N) M pmv sz -∗ S -∗
       ⌜usrc_ok M pmv sz (m !!! Regidx (mword_of_int 11)) nb f⌝) ->
    uinstr_is (ukn_t N) pc false (ECALL tt) -∗
    urun N h m pc avail -∗
    udepwf_K N m pc 16 fdep K -∗
    D -∗
    S -∗
    (∀ (h' : CpuId) (r : mword 64) (W : uvis) (cw' : Z) (cs' : gset gname),
       (* THE TRAPPING KEY'S THREE ARGUMENT WORDS ARE THE CALLER'S OWN *)
       ⌜tf_w (uvis_tf W) (tf_arg_idx 0) = m !!! Regidx (mword_of_int 10)⌝ -∗
       ⌜tf_w (uvis_tf W) (tf_arg_idx 1) = m !!! Regidx (mword_of_int 11)⌝ -∗
       ⌜tf_w (uvis_tf W) (tf_arg_idx 2) = m !!! Regidx (mword_of_int 12)⌝ -∗
       (* ...AND ITS TABLE IS THE ONE THE CALLER NAMED: without this row
          "fd 1 is the console" (or "fd is my file") says nothing about the
          arm this call took *)
       ⌜K (uvis_fd W)⌝ -∗
       (* ...AND ITS LAZY BIT IS [false], definitional at this leaf *)
       ⌜uvis_lazy W = false⌝ -∗
       (* ...AND THE SOURCE RUN'S TWO ROWS *)
       ⌜usrc_ok (uvis_M W) (uvis_perm W) (uvis_sz W)
          (m !!! Regidx (mword_of_int 11)) nb f⌝ -∗
       (* both resources come straight back: 16 moves no descriptor and no
          user byte *)
       D -∗ S -∗
       (* THE POST, AT THE TRAPPING KEY *)
       spost_at uslot 16 fdep W r (uvis_M W) (uvis_fd W) cw' cs' -∗
       urun N h' (<[Regidx (mword_of_int 10) := r]> m)
         (add_vec_int pc 4) avail -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Hn Hal4 Hag Hsrc.
    iIntros "#Hi Hrun Hsb Hstd Hbuf Hcont".
    iDestruct "Hrun" as (xi C pt Rfd Rut sz M pm fdv cw gn cs pidv) "(%Hlo & %Hpm & %Hlzf & %HRut & Hheap & Hstk & Hufd & Hcwda & Hcha & #Hmy & #Hdep & #Hnpx & Hb)".
    (* THE SOURCE RUN'S TWO ROWS, taken HERE because this is the one place
       where the heap the process owns and the key's own image and
       permission map are the same terms. *)
    iDestruct (Hsrc M pm sz with "Hheap Hbuf") as %Hnf.
    (* ...AND THE ARM, off the authority the run has just been destructed
       into *)
    iDestruct (Hag fdv with "Hufd Hstd") as %Htake.
    iDestruct "Hsb" as "[%Hfp Hsb]".
    iDestruct ("Hsb" $! M pm sz fdv cw gn cs pidv with "[%] Hmy Hheap Hufd")
      as "(Hheap & Hufd & Hdepn)"; [ exact Htake | ].
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iDestruct (uvb_x0 with "Hb") as "[%Hx0 Hb]".
    iApply (UkStep.wp_uk_ecall C pt Rfd Rut pm sz Hlo Hpm HRut Hlzf M m pc fdv cw gn cs pidv Hui
              (fun (s : mstate)
                   (Hp : register_lookup cur_privilege s.(sregs) = User)
                   (Hc : register_lookup (R_bitvector_64 PC) s.(sregs) = pc) =>
                 UserExecFacts.goodmb_execute_ECALL_U UserFrame.Du_r UserFrame.Du_w
                   s pc ltac:(vm_compute; reflexivity)
                   ltac:(vm_compute; reflexivity) Hp Hc)
              with "Hb Hmy").
    rewrite (uexec_ret_ecall _ _ eq_refl).
    assert (Hnum : uvis_num (uvis_of_run m pc M pm sz fdv cw gn cs pidv false secc_all) = 16).
    { assert (Hraw : usys_num (uvis_tf (uvis_of_run m pc M pm sz fdv cw gn cs pidv false secc_all)) = 16)
        by (cbn [uvis_tf uvis_of_run]; rewrite tf_of_num; exact Hn).
      rewrite uvis_num_full0; [ exact Hraw | reflexivity | rewrite Hraw; usys_range ]. }
    rewrite /uexec_pay_dep /upay_at.
    pose proof Hnum as Hnume. unfold uvis_num in Hnume. rewrite ?Hnum ?Hnume. cbv zeta.
    destruct (decide (uecall_scause = uecall_scause)) as [_ | Hpne];
      [ | exfalso; exact (Hpne eq_refl) ].
    destruct (decide (16 = USYS_exit)) as [He | _]; [ discriminate He | ].
    destruct (decide (16 = USYS_fork)) as [He | _]; [ discriminate He | ].
    destruct (decide (16 = USYS_wait)) as [He | _]; [ discriminate He | ].
    iExists fdep. rewrite Hfp.
    cbn [uvis_gen uvis_of_run].
    iSplitR; [ iFrame "Hmy" | ].
    iSplitL "Hdepn"; [ iExact "Hdepn" | ].
    iIntros (r M' pm' sz' fdv' cw' gn' cs' lz' secc')
      \"%Hok %Hfdok %Hpiperow %Hcwrow %Hgnrow %Hpidrow %Hliverow %Hscrow %Hchrow Hpost".
    (* THE LAZY BIT, THE CWD, THE GENERATION AND THE CHILDREN ALL CROSSED
       THE TRAP UNCHANGED: 16 is none of the rows that move them. *)
    assert (Hlzq : lz' = false)
      by (refine (usys_mem_ok_lazy _ _ _ _ _ _ _ _ _ _ _ _ Hok);
          vm_compute; discriminate).
    subst lz'.
    (* ...AND SO DID THE MASK: not seccomp's number, so the row is the
       equation ([UsysMemOk.usys_secc_ok_quiet]), and the resume key is at
       the full mask [urun] is keyed at *)
    pose proof (fun Hne => usys_secc_ok_quiet _ _ _ _ _ Hne Hscrow) as Hscq.
    specialize (Hscq ltac:(usys_range)).
    cbn [uvis_secc uvis_of_run] in Hscq. subst secc'.
    assert (Hcw : cw' = cw)
      by (refine (usys_cwd_ok_quiet _ _ _ _ _ Hcwrow); vm_compute; discriminate).
    assert (Hgn : gn' = gn) by exact (usys_gen_ok_quiet _ _ _ Hgnrow).
    assert (Hch : cs' = cs) by exact (usys_ch_ok_quiet _ _ _ _ Hchrow).
    subst gn' cs' cw'.
    destruct (usys_mem_ok_quiet 16 _ r _ _ _ _ _ _ _ _
                ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)
                ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) Hok)
      as [-> [-> ->]].
    pose proof (usys_fd_ok_quiet 16 _ r _ _
                  ltac:(discriminate) ltac:(discriminate)
                  ltac:(discriminate) ltac:(discriminate) Hfdok) as ->.
    cbn [uvis_M uvis_perm uvis_of_run].
    rewrite (uslot_bump_run m pc M M pm pm sz sz fdv fdv cw cw gn gn cs cs pidv false false secc_all secc_all r Hx0 Hal4).
    iApply ukcq_ukc.
    iApply (urun_close_upd _ _ _ m (mword_of_int 10) _ _ _ _ _ _ _ _ _
              ltac:(unfold unot_sp; vm_compute; discriminate)
              with "Hheap Hstk Hufd Hcwda Hcha Hmy Hdep Hnpx").
    iIntros (h') "Hrun".
    iApply ("Hcont" $! h' r (uvis_of_run m pc M pm sz fdv cw gn cs pidv false secc_all) cw cs
              with "[%] [%] [%] [%] [%] [%] Hstd Hbuf [Hpost] Hrun").
    { rewrite /tf_w. cbn [uvis_tf uvis_of_run]. exact (tf_of_arg0 m pc). }
    { rewrite /tf_w. cbn [uvis_tf uvis_of_run]. exact (tf_of_arg1 m pc). }
    { rewrite /tf_w. cbn [uvis_tf uvis_of_run]. exact (tf_of_arg2 m pc). }
    { rewrite (uvis_of_run_fd m pc M pm sz fdv cw gn cs pidv false secc_all). exact Htake. }
    { reflexivity. }
    { cbn [uvis_M uvis_perm uvis_sz uvis_of_run]. exact Hnf. }
    rewrite (uvis_of_run_fd m pc M pm sz fdv cw gn cs pidv false secc_all).
    cbn [uvis_M uvis_of_run]. iExact "Hpost".
  Qed.

  (* ------------------------------------------------------------------- *)
  (* ecall, at WRITE (16) -- THE LEAF THAT LETS THE PROCESS PAY THE         *)
  (* CONSOLE ARM WITH ITS OWN CHAIN (app-echo.md, E5 -- THE CONSOLE I/O     *)
  (* CLAIM, item (W); lane IO-LEAF, first half).                            *)
  (*                                                                       *)
  (* Row 16's deposit is [SpecFilewrite.filewrite_in] at                    *)
  (* [FdSlots.fd_st_of_key (xk_a W 0) (uvis_fd W)], and on a WRITABLE       *)
  (* DEVICE descriptor that arm is [SpecConsolewrite.cons_out_chain] over   *)
  (* the caller's own cursor family [wf_Q f] -- one view shift per byte,    *)
  (* the byte pinned against the image the process lent.  Every write leaf  *)
  (* in the tree today ([wp_uk_ecall_quiet] and the three programs' stubs)  *)
  (* pays that chain out of the OUTPUT LICENCE at the TRIVIAL cursor        *)
  (* ([SpecConsolewrite.cons_out_chain_of_licence]) and throws the post      *)
  (* away, so no verified program has ever learned anything about what it   *)
  (* wrote.  This leaf is the same walk with the deposit NAMED and the post *)
  (* KEPT, and it costs exactly the two things                              *)
  (* [wp_uk_ecall_read_recv] costs:                                         *)
  (*                                                                       *)
  (*  - THE DEPOSIT MUST NAME ITS FAMILY, because the post is read at it    *)
  (*    ([UkRun.udepwf]'s note): [spost_at] at 16 is                        *)
  (*    [SpecFilewrite.filewrite_extra] at [wf_Q f], and [UkRun.udepw]'s    *)
  (*    existential loses the [f].                                         *)
  (*  - AND IT MUST BE LEDGER-FIXED ([UkRun.udepwf_std]), which is the      *)
  (*    point [UexecSG.free_num]'s note already makes about 16: a KEY-FREE  *)
  (*    supplier would have to answer the INODE arm -- an                   *)
  (*    [FsAbsWriteFire.awrite_chain] -- at a key whose descriptor row is   *)
  (*    an inode, and a console writer has no such chain.  Which arm row 16 *)
  (*    asks for is decided by the key's own table, so the leaf reads the   *)
  (*    agreement off the authority it has just destructed and hands it     *)
  (*    back as [take NSTD (uvis_fd W) = l].  The pure row beside it -- fd  *)
  (*    [i] of [l] is an open, writable device -- is the CALLER's, exactly  *)
  (*    as [UkSh.ush_fd0p] is on the read side, and it is spent where the   *)
  (*    deposit is built, not here.                                        *)
  (*                                                                       *)
  (* THE POST IS AT THE TRAPPING KEY, for row 16's own reason: the arm is   *)
  (* selected by argument 0, and the buffer address and the count are       *)
  (* arguments 1 and 2, while the returning bump OVERWRITES a0.  The three  *)
  (* argument words come back tied to the caller's own register file.  NO   *)
  (* IMAGE ROW is handed out and none is owed: the console arm's post       *)
  (* ([SpecFilewrite.write_cons_arms]) reads the cursor, the count and the  *)
  (* answer, and no byte of [M'].                                          *)
  (*                                                                       *)
  (* NO CWD HALF, unlike [wp_uk_ecall_quiet_recv]: a write resolves no      *)
  (* path, so the directory the round resumes at is handed to the           *)
  (* continuation ∀-bound rather than pinned by a fragment the caller would *)
  (* otherwise have to own.                                                *)
  (*                                                                       *)
  (* THE WALK IS [wp_uk_ecall_quiet_recv]'s -- 16 moves no user byte, no    *)
  (* descriptor and no directory -- with the ledger agreement taken where   *)
  (* both halves are in one hand.                                          *)
  (* ------------------------------------------------------------------- *)
  (* ...AND THE SAME LEAF WITH THE CALLER'S SOURCE RUN IN HAND (lane        *)
  (* IO-LEAF; the twin of [wp_uk_ecall_read_recv]'s no-fault row, one test  *)
  (* weaker).                                                              *)
  (*                                                                       *)
  (* WHY IT IS OWED.  Row 16's post carries the SHORT arm and its reason    *)
  (* (lane TRAP-ROWS, T1): a count below the request says that some byte of *)
  (* the run at or after the cursor is on a page the kernel could not READ  *)
  (* through ([SpecFilewrite.write_cons_short]).  A program threading a     *)
  (* per-byte cursor through the chain CANNOT LIVE WITH THAT ARM -- it hands *)
  (* back the cursor UNMOVED while the program's own string index has       *)
  (* advanced -- and it cannot refute it either: the refutation needs       *)
  (* [UserHeap.uw_addr (uvis_perm W)] at the buffer, and [uvis_perm W] is   *)
  (* bound by [UkRun.urun]'s existentials.  THIS LEAF CAN: its key IS       *)
  (* [UexecSlot.uvis_of_run] at the very map the heap it destructs is at,   *)
  (* exactly as the READ leaf's own row is handed out from there.           *)
  (*                                                                       *)
  (* THE RUN IS A PREMISE and comes straight back: 16 writes no user byte.  *)
  (* [nb] is the CALLER's, not the request's -- a caller refutes the arm    *)
  (* only as far as the run it owns, and at [nb = 0] this is exactly the    *)
  (* buffer-free leaf below, which is how the two stubs that hold no run    *)
  (* ([UkSh]'s, [UkEcho]'s) keep their statements.                          *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_uk_ecall_write_chain_buf (N : uk_names Σ) (h : CpuId)
      (m : regfile) (pc : mword 64) (avail : nat) (fdep : sfam)
      (l : list fdstate) (dq : dfrac) (nb : nat) (f : nat -> bv 8) :
    usysno m = 16 ->
    is_aligned_vaddr (Virtaddr (add_vec_int pc 4)) 2 = true ->
    uinstr_is (ukn_t N) pc false (ECALL tt) -∗
    urun N h m pc avail -∗
    udepwf_std N m pc 16 fdep l -∗
    UserFd.ustd (ukn_fd N) l -∗
    UserHeap.ubytesq (ukn_d N) dq
      (uint (m !!! Regidx (mword_of_int 11))) nb f -∗
    (∀ (h' : CpuId) (r : mword 64) (W : uvis) (cw' : Z) (cs' : gset gname),
       (* THE TRAPPING KEY'S THREE ARGUMENT WORDS ARE THE CALLER'S OWN *)
       ⌜tf_w (uvis_tf W) (tf_arg_idx 0) = m !!! Regidx (mword_of_int 10)⌝ -∗
       ⌜tf_w (uvis_tf W) (tf_arg_idx 1) = m !!! Regidx (mword_of_int 11)⌝ -∗
       ⌜tf_w (uvis_tf W) (tf_arg_idx 2) = m !!! Regidx (mword_of_int 12)⌝ -∗
       (* ...AND ITS LEDGER IS THE CALLER'S OWN TOO: without this row "fd 1
          is the console" says nothing about the arm this call took *)
       ⌜take NSTD (uvis_fd W) = l⌝ -∗
       (* ...AND ITS LAZY BIT IS [false], definitional at this leaf (the U
          tier's run is at an empty fill, [UexecRet.ukcq]) and handed back
          because the POST is where it is spent: row 16's [∃ P] carries
          [uvis_lazy W = false -> lazy_free (ud_um P) (uvis_sz W)]. *)
       ⌜uvis_lazy W = false⌝ -∗
       (* ...AND EVERY BYTE OF THE SOURCE RUN IS READABLE-MAPPED IN ANY
          TABLE THE KEY'S PROJECTION ADMITS.  Stated POSITIVELY, as the
          read side's is: the consumer eliminates
          [SpecFilewrite.write_cons_short] by contradiction. *)
       ⌜ forall (P : uptd) (j : nat),
           ProcPtOwn.proc_pt_wf P ->
           perm_of (ud_um P) (uvis_sz W) = uvis_perm W ->
           lazy_free (ud_um P) (uvis_sz W) ->
           (j < nb)%nat ->
           UserPtTree.uva_rmapped P
             (uint (add_vec_int (m !!! Regidx (mword_of_int 11))
                      (Z.of_nat j))) ⌝ -∗
       (* the ledger comes straight back: write moves no descriptor *)
       UserFd.ustd (ukn_fd N) l -∗
       (* ...and so does the source run *)
       UserHeap.ubytesq (ukn_d N) dq
         (uint (m !!! Regidx (mword_of_int 11))) nb f -∗
       (* THE POST, AT THE TRAPPING KEY *)
       spost_at uslot 16 fdep W r (uvis_M W) (uvis_fd W) cw' cs' -∗
       urun N h' (<[Regidx (mword_of_int 10) := r]> m)
         (add_vec_int pc 4) avail -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  (* ...AND IT IS NOW [wp_uk_ecall_write_at] AT THE LEDGER READING AND THE
     DATA HALF (lane RD-6), at its exact former statement: the walk it used
     to carry is the one walk, and what this leaf adds is the two answers
     ([UserFd.ustd_agree], [usrc_ok_ubytesq]).  The image row the one walk
     hands out is DROPPED here, because that is what the former statement
     said; the file arm is where it is spent. *)
  Proof using .
    intros Hn Hal4.
    iIntros "#Hi Hrun Hsb Hstd Hbuf Hcont".
    iApply (wp_uk_ecall_write_at N h m pc avail fdep
              (UserFd.ustd (ukn_fd N) l)
              (UserHeap.ubytesq (ukn_d N) dq
                 (uint (m !!! Regidx (mword_of_int 11))) nb f)
              (fun fdv => take NSTD fdv = l) nb f Hn Hal4
              (fun fdv => ustd_agree (ukn_fd N) fdv l)
              (fun M pmv sz =>
                 usrc_ok_ubytesq (ukn_t N) (ukn_d N) (ukn_s N) M pmv sz dq
                   (m !!! Regidx (mword_of_int 11)) nb f)
              with "Hi Hrun [Hsb] Hstd Hbuf").
    { iApply (udepwf_K_std N m pc 16 fdep l with "Hsb"). }
    iIntros (h' r W cw' cs')
      "%Ha0 %Ha1 %Ha2 %Htk %Hlz %Hsrc Hstd Hbuf Hpost Hrun".
    iApply ("Hcont" $! h' r W cw' cs'
              with "[%] [%] [%] [%] [%] [%] Hstd Hbuf Hpost Hrun");
      [ exact Ha0 | exact Ha1 | exact Ha2 | exact Htk | exact Hlz
      | exact (proj2 Hsrc) ].
  Qed.

  (* ...AND THE BUFFER-FREE LEAF, which is the one above at [nb = 0]: a
     caller that holds no run of its own -- every write stub in the tree
     until lane IO-LEAF -- learns nothing about which bytes the kernel
     could read, and asks for nothing.  Both stand, and the two program
     stubs that still pay their chain from the flagged deposit
     ([UkSh.wp_ksh_write_chain], [UkEcho.wp_kecho_write_chain]) are stated
     at this one. *)
  Lemma wp_uk_ecall_write_chain (N : uk_names Σ) (h : CpuId)
      (m : regfile) (pc : mword 64) (avail : nat) (fdep : sfam)
      (l : list fdstate) :
    usysno m = 16 ->
    is_aligned_vaddr (Virtaddr (add_vec_int pc 4)) 2 = true ->
    uinstr_is (ukn_t N) pc false (ECALL tt) -∗
    urun N h m pc avail -∗
    udepwf_std N m pc 16 fdep l -∗
    UserFd.ustd (ukn_fd N) l -∗
    (∀ (h' : CpuId) (r : mword 64) (W : uvis) (cw' : Z) (cs' : gset gname),
       ⌜tf_w (uvis_tf W) (tf_arg_idx 0) = m !!! Regidx (mword_of_int 10)⌝ -∗
       ⌜tf_w (uvis_tf W) (tf_arg_idx 1) = m !!! Regidx (mword_of_int 11)⌝ -∗
       ⌜tf_w (uvis_tf W) (tf_arg_idx 2) = m !!! Regidx (mword_of_int 12)⌝ -∗
       ⌜take NSTD (uvis_fd W) = l⌝ -∗
       UserFd.ustd (ukn_fd N) l -∗
       spost_at uslot 16 fdep W r (uvis_M W) (uvis_fd W) cw' cs' -∗
       urun N h' (<[Regidx (mword_of_int 10) := r]> m)
         (add_vec_int pc 4) avail -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Hn Hal4. iIntros "#Hi Hrun Hsb Hstd Hcont".
    iApply (wp_uk_ecall_write_chain_buf N h m pc avail fdep l (DfracOwn 1)
              0%nat (fun _ => bv_0 8) Hn Hal4 with "Hi Hrun Hsb Hstd []").
    { by rewrite /UserHeap.ubytesq. }
    iIntros (h' r W cw' cs') "%Ha0 %Ha1 %Ha2 %Htk _ _ Hstd _ Hpost Hrun".
    iApply ("Hcont" $! h' r W cw' cs'
              with "[%] [%] [%] [%] Hstd Hpost Hrun");
      assumption.
  Qed.


  (* ------------------------------------------------------------------- *)
  (* ...AND THE SAME LEAF WITH THE SOURCE RUN IN THE TEXT HALF (lane        *)
  (* TXT-ROW).                                                             *)
  (*                                                                       *)
  (* WHY A SECOND ONE.  [wp_uk_ecall_write_chain_buf] reads the row that    *)
  (* refutes the short arm off [uheap_ubytes_w] -- the caller owns this     *)
  (* byte, so its page is WRITABLE, so a copyin could read it               *)
  (* ([UserHeap.lazy_free_uw_addr]).  A program that prints a STRING        *)
  (* LITERAL has no such byte: .rodata is X-and-NOT-W and is filed under    *)
  (* the TEXT gname, and no [ubytesq] of it exists.  echo's separator       *)
  (* (0x940) and its newline (0x948) are exactly that                       *)
  (* ([UCodeEcho.echo_ro]).                                                *)
  (*                                                                       *)
  (* THE ROW IS STILL TRUE AND ONE TEST WEAKER.  [UserHeap.uheap_text]      *)
  (* puts a text byte's page in [UserHeap.ux_addr] of the key's permission  *)
  (* map, and a page the projection lists AT ALL is a real user leaf --     *)
  (* [perm_leaf] tests U and R -- so under [lazy_free] the fetchable page   *)
  (* is readable-mapped too ([UserHeap.lazy_free_ux_addr]).  As with the    *)
  (* buffer leaf, only HERE can it be handed out: the key's permission map  *)
  (* is bound by [UkRun.urun]'s existentials, and no caller can name it.    *)
  (*                                                                       *)
  (* THE RUN IS PERSISTENT ([utext] is [↪□]), so it comes back for free and *)
  (* the walk never has to give it up; everything else -- the four          *)
  (* register rows, the ledger row, the lazy bit and the post -- is         *)
  (* [wp_uk_ecall_write_chain_buf]'s, word for word.  [nb = 0] is the       *)
  (* buffer-free leaf again, so the two stubs that hold no run keep their   *)
  (* statements and [wp_uk_ecall_write_chain] is untouched.                 *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_uk_ecall_write_chain_txt (N : uk_names Σ) (h : CpuId)
      (m : regfile) (pc : mword 64) (avail : nat) (fdep : sfam)
      (l : list fdstate) (nb : nat) (f : nat -> bv 8) :
    usysno m = 16 ->
    is_aligned_vaddr (Virtaddr (add_vec_int pc 4)) 2 = true ->
    uinstr_is (ukn_t N) pc false (ECALL tt) -∗
    urun N h m pc avail -∗
    udepwf_std N m pc 16 fdep l -∗
    UserFd.ustd (ukn_fd N) l -∗
    ([∗ list] j ∈ seq 0 nb,
       UserHeap.utext (ukn_t N)
         (uint (m !!! Regidx (mword_of_int 11)) + Z.of_nat j)%Z (f j)) -∗
    (∀ (h' : CpuId) (r : mword 64) (W : uvis) (cw' : Z) (cs' : gset gname),
       ⌜tf_w (uvis_tf W) (tf_arg_idx 0) = m !!! Regidx (mword_of_int 10)⌝ -∗
       ⌜tf_w (uvis_tf W) (tf_arg_idx 1) = m !!! Regidx (mword_of_int 11)⌝ -∗
       ⌜tf_w (uvis_tf W) (tf_arg_idx 2) = m !!! Regidx (mword_of_int 12)⌝ -∗
       ⌜take NSTD (uvis_fd W) = l⌝ -∗
       ⌜uvis_lazy W = false⌝ -∗
       ⌜ forall (P : uptd) (j : nat),
           ProcPtOwn.proc_pt_wf P ->
           perm_of (ud_um P) (uvis_sz W) = uvis_perm W ->
           lazy_free (ud_um P) (uvis_sz W) ->
           (j < nb)%nat ->
           UserPtTree.uva_rmapped P
             (uint (add_vec_int (m !!! Regidx (mword_of_int 11))
                      (Z.of_nat j))) ⌝ -∗
       UserFd.ustd (ukn_fd N) l -∗
       ([∗ list] j ∈ seq 0 nb,
          UserHeap.utext (ukn_t N)
            (uint (m !!! Regidx (mword_of_int 11)) + Z.of_nat j)%Z (f j)) -∗
       spost_at uslot 16 fdep W r (uvis_M W) (uvis_fd W) cw' cs' -∗
       urun N h' (<[Regidx (mword_of_int 10) := r]> m)
         (add_vec_int pc 4) avail -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  (* ...AND IT IS THE ONE WALK AT THE TEXT HALF (lane RD-6), at its exact
     former statement: the only thing that ever differed from the buffer
     leaf is which answer to [usrc_ok] the caller's run gives. *)
  Proof using .
    intros Hn Hal4.
    iIntros "#Hi Hrun Hsb Hstd #Hbs Hcont".
    iApply (wp_uk_ecall_write_at N h m pc avail fdep
              (UserFd.ustd (ukn_fd N) l)
              ([∗ list] j ∈ seq 0 nb,
                 UserHeap.utext (ukn_t N)
                   (uint (m !!! Regidx (mword_of_int 11)) + Z.of_nat j)%Z (f j))%I
              (fun fdv => take NSTD fdv = l) nb f Hn Hal4
              (fun fdv => ustd_agree (ukn_fd N) fdv l)
              (fun M pmv sz =>
                 usrc_ok_utext (ukn_t N) (ukn_d N) (ukn_s N) M pmv sz
                   (m !!! Regidx (mword_of_int 11)) nb f)
              with "Hi Hrun [Hsb] Hstd Hbs").
    { iApply (udepwf_K_std N m pc 16 fdep l with "Hsb"). }
    iIntros (h' r W cw' cs')
      "%Ha0 %Ha1 %Ha2 %Htk %Hlz %Hsrc Hstd Hbs' Hpost Hrun".
    iApply ("Hcont" $! h' r W cw' cs'
              with "[%] [%] [%] [%] [%] [%] Hstd Hbs' Hpost Hrun");
      [ exact Ha0 | exact Ha1 | exact Ha2 | exact Htk | exact Hlz
      | exact (proj2 Hsrc) ].
  Qed.


  (* ------------------------------------------------------------------- *)
  (* ...AND THE TWO OF THEM WITH THE IMAGE ROW (lane OPEN-PIN, phase 4).    *)
  (*                                                                       *)
  (* A PINNED open or mknod is about a PATH, and the receipt names the      *)
  (* path only through [ArgPath.arg_path_of (uvis_M W) (xk_a W 0) pl] --    *)
  (* a fact about the TRAPPING KEY'S image.  A program holds a persistent   *)
  (* view of its own rodata ([UserHeap.utext_img]; /init's is               *)
  (* [UCodeInit.init_rodata]) and the run holds the heap the key is built   *)
  (* from, so the inclusion is readable exactly HERE, where both halves     *)
  (* are in one hand -- and nowhere in the caller, where [urun] has hidden  *)
  (* the image again.  Without the row a caller can supply a pinned bundle  *)
  (* and still not know which file its own receipt is about.                *)
  (*                                                                       *)
  (* Each is its recv leaf's walk with that one extra reading; the two      *)
  (* leaves above are unchanged.                                           *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_uk_ecall_open_recv_img (N : uk_names Σ) (h : CpuId)
      (m : regfile) (pc : mword 64) (l : list fdstate) (avail : nat)
      (fdep : sfam) (c : Z) (Img : gmap Z (bv 8)) :
    usysno m = USYS_open ->
    is_aligned_vaddr (Virtaddr (add_vec_int pc 4)) 2 = true ->
    uinstr_is (ukn_t N) pc false (ECALL tt) -∗
    (* the caller's own PERSISTENT view of a piece of its image *)
    utext_img (ukn_t N) Img -∗
    urun N h m pc avail -∗
    (* the program's half of its working directory... *)
    UserCwd.ucwd (ukn_cwd N) c -∗
    (* ...and the deposit at every key whose cwd is that one inum, at the
       family the program will read its receipt at *)
    udepwf_at N m pc USYS_open fdep c -∗
    ustd (ukn_fd N) l -∗
    (∀ (h' : CpuId) (r : mword 64) (W : uvis)
       (M' : gmap Z (bv 8)) (fdv' : list fdstate) (cw' : Z)
       (cs' : gset gname),
       (* THE TRAPPING KEY'S TWO ARGUMENT WORDS ARE THE CALLER'S OWN, which
          is what lets a program that knows its image read its own path
          argument off the receipt ([ArgPath.arg_path_of] at [uvis_M W] and
          [tf_arg_idx 0]). *)
       ⌜ forall (a : Z) (b : bv 8),
           Img !! a = Some b -> uvis_M W !! a = Some b ⌝ -∗
       (* ...AND THE TABLE'S LENGTH, which is what bounds the descriptor a
          receipt names and so lets a caller identify it with the one its
          own ledger decided. *)
       ⌜length (uvis_fd W) = NOFILE⌝ -∗
       ⌜tf_w (uvis_tf W) (tf_arg_idx 0) = m !!! Regidx (mword_of_int 10)⌝ -∗
       ⌜tf_w (uvis_tf W) (tf_arg_idx 1) = m !!! Regidx (mword_of_int 11)⌝ -∗
       (* ...AND ITS CWD AND ITS LEDGER ARE THE CALLER'S OWN TOO *)
       ⌜uvis_cwd W = c⌝ -∗
       ⌜take NSTD (uvis_fd W) = l⌝ -∗
       (* the ledger, exactly [wp_uk_ecall_open]'s two arms *)
       ((∃ (fd : nat) (rd wr : bool) (t : fdtype),
           (* ...AND THE ROW THE ALLOCATION LEFT IN THE RESUME VIEW, beside
              the number and the handle: the receipt's own descriptor row
              is about [fdv'], so without this the caller cannot tie the
              TYPE the receipt names to the SLOT its ledger decided. *)
           ⌜r = (mword_of_int (Z.of_nat fd) : mword 64)
            /\ (fd < NOFILE)%nat
            /\ fdv' = <[fd := FdOpen rd wr t]> (uvis_fd W)
            (* ...AND IT IS NOT A PIPE (survey R4, lane SUP-ONE).  open
               installs an inode or a device and [UsysMemOk.usys_fd_ok]'s
               open row says so; exporting the fact here is what lets a
               holder of this handle take [UkRun.udepw_cl_nopipe]'s FREE
               close instead of a flagged deposit at 21. *)
            /\ fdst_nopipe (FdOpen rd wr t)⌝ ∗
           ualloc (ukn_fd N) l fd (FdOpen rd wr t))
        ∨ (⌜r = (mword_of_int (-1) : mword 64)
             /\ fdv' = uvis_fd W⌝ ∗ ustd (ukn_fd N) l)) -∗
       (* ...AND THE POST, at the TRAPPING key and the resume view *)
       spost_at uslot USYS_open fdep W r M' fdv' cw' cs' -∗
       UserCwd.ucwd (ukn_cwd N) c -∗
       urun N h' (<[Regidx (mword_of_int 10) := r]> m)
         (add_vec_int pc 4) avail -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Hn Hal4.
    iIntros "#Hi #Himg Hrun Hcwd Hsb Hstd Hcont".
    iDestruct "Hrun" as (xi C pt Rfd Rut sz M pm fdv cw gn cs pidv) "(%Hlo & %Hpm & %Hlzf & %HRut & Hheap & Hstk & Hufd & Hcwda & Hcha & #Hmy & #Hdep & #Hnpx & Hb)".
    (* the key's cwd IS the one the caller's PINNED bundle is stated at *)
    iDestruct (ucwd_agree with "Hcwda Hcwd") as %->.
    (* ...and the key's low three slots ARE the caller's own ledger, which
       is what makes the receipt's descriptor row readable at all *)
    iDestruct (ustd_agree (ukn_fd N) fdv l with "Hufd Hstd") as %Htake.
    (* ...AND THE IMAGE ROW: the caller's persistent view is a submap of the
       key's own image, which is what lets it read its path argument off
       the receipt ([ArgPath.arg_path_of] at [uvis_M W]). *)
    iAssert (⌜ forall (a : Z) (b : bv 8),
                Img !! a = Some b -> M !! a = Some b ⌝)%I as %Hsimg.
    { iIntros (a b Hb).
      iDestruct (big_sepM_lookup _ _ a b Hb with "Himg") as "Hb'".
      iDestruct (uheap_text with "Hheap Hb'") as %(HM & _ & _).
      iPureIntro. exact HM. }
    (* the deposit, at the family the receipt will come back at *)
    iDestruct "Hsb" as "[%Hfp Hsb]".
    iDestruct ("Hsb" $! M pm sz fdv gn cs pidv with "Hmy Hheap Hufd")
      as "(Hheap & Hufd & Hdepn)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iDestruct (uvb_x0 with "Hb") as "[%Hx0 Hb]".
    iApply (UkStep.wp_uk_ecall C pt Rfd Rut pm sz Hlo Hpm HRut Hlzf M m pc fdv c gn cs pidv Hui
              (fun (s : mstate)
                   (Hp : register_lookup cur_privilege s.(sregs) = User)
                   (Hc : register_lookup (R_bitvector_64 PC) s.(sregs) = pc) =>
                 UserExecFacts.goodmb_execute_ECALL_U UserFrame.Du_r UserFrame.Du_w
                   s pc ltac:(vm_compute; reflexivity)
                   ltac:(vm_compute; reflexivity) Hp Hc)
              with "Hb Hmy").
    rewrite (uexec_ret_ecall _ _ eq_refl).
    assert (Hnum : uvis_num (uvis_of_run m pc M pm sz fdv c gn cs pidv false secc_all) = USYS_open).
    { assert (Hraw : usys_num (uvis_tf (uvis_of_run m pc M pm sz fdv c gn cs pidv false secc_all)) = USYS_open)
        by (cbn [uvis_tf uvis_of_run]; rewrite tf_of_num; exact Hn).
      rewrite uvis_num_full0; [ exact Hraw | reflexivity | rewrite Hraw; usys_range ]. }
    rewrite /uexec_pay_dep /upay_at.
    pose proof Hnum as Hnume. unfold uvis_num in Hnume. rewrite ?Hnum ?Hnume. cbv zeta.
    destruct (decide (uecall_scause = uecall_scause)) as [_ | Hpne];
      [ | exfalso; exact (Hpne eq_refl) ].
    destruct (decide (USYS_open = USYS_exit)) as [He | _];
      [ exfalso; vm_compute in He; discriminate | ].
    destruct (decide (USYS_open = USYS_fork)) as [He | _];
      [ exfalso; vm_compute in He; discriminate | ].
    iExists fdep. rewrite Hfp.
    cbn [uvis_gen uvis_of_run].
    iSplitR; [ iFrame "Hmy" | ].
    iSplitL "Hdepn"; [ iExact "Hdepn" | ].
    iIntros (r M' pm' sz' fdv' cw' gn' cs' lz' secc')
      \"%Hok %Hfdok %Hpiperow %Hcwrow %Hgnrow %Hpidrow %Hliverow %Hscrow %Hchrow Hpost".
    (* THE LAZY BIT CROSSED THE TRAP UNCHANGED (lane LAZY-FLAG, L6).  The
       trapping key is at [false] -- the U tier's run is
       ([UexecRet.ukcq]) -- and every row but sbrk's is the equation
       ([UsysMemOk.usys_mem_ok_lazy]), so the resume key is at [false] too
       and the close below is at the run's own bit. *)
    assert (Hlzq : lz' = false)
      by (refine (usys_mem_ok_lazy _ _ _ _ _ _ _ _ _ _ _ _ Hok);
          first [ assumption | vm_compute; discriminate ]).
    subst lz'.
    (* ...AND SO DID THE MASK: not seccomp's number, so the row is the
       equation ([UsysMemOk.usys_secc_ok_quiet]), and the resume key is at
       the full mask [urun] is keyed at *)
    pose proof (fun Hne => usys_secc_ok_quiet _ _ _ _ _ Hne Hscrow) as Hscq.
    specialize (Hscq ltac:(usys_range)).
    cbn [uvis_secc uvis_of_run] in Hscq. subst secc'.
    assert (Hcw : cw' = c)
      by (refine (usys_cwd_ok_quiet _ _ _ _ _ Hcwrow); vm_compute; discriminate).
    assert (Hgn : gn' = gn) by exact (usys_gen_ok_quiet _ _ _ Hgnrow).
    assert (Hch : cs' = cs) by exact (usys_ch_ok_quiet _ _ _ _ Hchrow).
    subst gn' cs' cw'.
    destruct (usys_mem_ok_quiet USYS_open _ r _ _ _ _ _ _ _ _
                ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)
                ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) Hok)
      as [-> [-> ->]].
    unfold usys_fd_ok in Hfdok.
    destruct (decide (USYS_open = USYS_close)) as [Hc | _]; [ discriminate Hc | ].
    destruct (decide (USYS_open = USYS_dup)) as [Hc | _]; [ discriminate Hc | ].
    destruct (decide (USYS_open = USYS_open)) as [_ | Hc];
      [ | exfalso; exact (Hc eq_refl) ].
    cbn [uvis_M uvis_perm uvis_fd uvis_of_run] in Hfdok |- *.
    iDestruct (ufd_auth_len with "Hufd") as %Hfdlen.
    iApply uslot_bupd.
    destruct Hfdok as [(fd & rd & wr & t & Hr & Hcl & -> & Hnpo) | [Hrm ->]].
    - (* A DESCRIPTOR CAME BACK, at the LOWEST free slot, and the RECEIPT
         says at which type *)
      iMod (ufd_alloc_least (ukn_fd N) fdv l fd (FdOpen rd wr t) Hcl
              ltac:(discriminate) with "Hufd Hstd") as "[Hufd Hh]".
      iModIntro.
      (* ...and open installs an inode or a device, never a pipe end *)
      iDestruct (urun_rows_insert N fdv fd (FdOpen rd wr t) Hnpo
                   with "Hnpx") as "#Hnpi".
      rewrite (uslot_bump_run m pc M M pm pm sz sz fdv
                 (<[fd := FdOpen rd wr t]> fdv) c c gn gn cs cs pidv false false secc_all secc_all r Hx0 Hal4).
      iApply ukcq_ukc.
      iApply (urun_close_upd _ _ _ m (mword_of_int 10) _ _ _ _ _ _ _ _ _
                ltac:(unfold unot_sp; vm_compute; discriminate)
                with "Hheap Hstk Hufd Hcwda Hcha Hmy Hdep Hnpi").
      iIntros (h') "Hrun".
      iApply ("Hcont" $! h' r (uvis_of_run m pc M pm sz fdv c gn cs pidv false secc_all)
                _ _ _ _ with "[%] [%] [%] [%] [%] [%] [Hh] Hpost Hcwd Hrun").
      { exact Hsimg. }
      { rewrite (uvis_of_run_fd m pc M pm sz fdv c gn cs pidv false secc_all). exact Hfdlen. }
      { rewrite /tf_w. cbn [uvis_tf uvis_of_run]. exact (tf_of_arg0 m pc). }
      { rewrite /tf_w. cbn [uvis_tf uvis_of_run]. exact (tf_of_arg1 m pc). }
      { exact (uvis_of_run_cwd m pc M pm sz fdv c gn cs pidv false secc_all). }
      { rewrite (uvis_of_run_fd m pc M pm sz fdv c gn cs pidv false secc_all). exact Htake. }
      iLeft. iExists fd, rd, wr, t. iFrame "Hh". iPureIntro.
      split_and!; [ exact Hr | | | exact Hnpo ].
      { rewrite <- Hfdlen. exact (fd_least_closed_lt _ _ Hcl). }
      rewrite (uvis_of_run_fd m pc M pm sz fdv c gn cs pidv false secc_all). reflexivity.
    - (* the call failed: nothing moved, and the ledger comes straight back *)
      iModIntro.
      rewrite (uslot_bump_run m pc M M pm pm sz sz fdv fdv c c gn gn cs cs pidv false false secc_all secc_all r Hx0 Hal4).
      iApply ukcq_ukc.
      iApply (urun_close_upd _ _ _ m (mword_of_int 10) _ _ _ _ _ _ _ _ _
                ltac:(unfold unot_sp; vm_compute; discriminate)
                with "Hheap Hstk Hufd Hcwda Hcha Hmy Hdep Hnpx").
      iIntros (h') "Hrun".
      iApply ("Hcont" $! h' r (uvis_of_run m pc M pm sz fdv c gn cs pidv false secc_all)
                _ _ _ _ with "[%] [%] [%] [%] [%] [%] [Hstd] Hpost Hcwd Hrun").
      { exact Hsimg. }
      { rewrite (uvis_of_run_fd m pc M pm sz fdv c gn cs pidv false secc_all). exact Hfdlen. }
      { rewrite /tf_w. cbn [uvis_tf uvis_of_run]. exact (tf_of_arg0 m pc). }
      { rewrite /tf_w. cbn [uvis_tf uvis_of_run]. exact (tf_of_arg1 m pc). }
      { exact (uvis_of_run_cwd m pc M pm sz fdv c gn cs pidv false secc_all). }
      { rewrite (uvis_of_run_fd m pc M pm sz fdv c gn cs pidv false secc_all). exact Htake. }
      iRight. iFrame "Hstd". iPureIntro. split; [ exact Hrm | ].
      rewrite (uvis_of_run_fd m pc M pm sz fdv c gn cs pidv false secc_all). reflexivity.
  Qed.

  (* =================================================================== *)
  (*  THE PATH ARGUMENT'S IMAGE VIEW, AT EITHER HALF OF THE HEAP         *)
  (*  (lane CAT-WALK-2, K1).                                             *)
  (*                                                                     *)
  (*  [wp_uk_ecall_open_recv_img] above reads the caller's image row off  *)
  (*  [UserHeap.utext_img] -- the TEXT half -- which is right for a       *)
  (*  program whose path argument is a LITERAL (/init's, sh's console     *)
  (*  open).  It is wrong for every program whose path is heap DATA:      *)
  (*  cat's path is [argv[1]], which the exec crossing copied onto its    *)
  (*  stack as [UserHeap.uargv] (persistent [ubyteq] under [ukn_d]), and  *)
  (*  the redirect child's comes out of sh's line buffer.  Neither is a   *)
  (*  [utext] byte and no amount of work on the caller's side makes one:  *)
  (*  the text half is exactly the X-and-NOT-W pages.                     *)
  (*                                                                     *)
  (*  So the row itself becomes the premise.  [uimg_view N Img] is        *)
  (*  "whatever I hold, it lets me read [Img] off the key's own image"    *)
  (*  -- a boxed wand off the run's heap authority, which is the ONLY     *)
  (*  thing the walk below ever does with the caller's view.  The two     *)
  (*  halves supply it in one line each ([uimg_view_text] /               *)
  (*  [uimg_view_data]), and the walk is proved ONCE.                     *)
  (* =================================================================== *)
  Definition uimg_view (N : uk_names Σ) (Img : gmap Z (bv 8)) : iProp Σ :=
    (□ (∀ (M : gmap Z (bv 8)) (pm : gmap (mword 27) uperm) (sz : Z),
          uheap (ukn_t N) (ukn_d N) (ukn_s N) M pm sz -∗
          ⌜ forall (a : Z) (b : bv 8),
              Img !! a = Some b -> M !! a = Some b ⌝))%I.

  Global Instance uimg_view_persistent N Img : Persistent (uimg_view N Img).
  Proof using . rewrite /uimg_view. apply _. Qed.

  (* the reading, in [UConsOpen.cons_ro_sub]'s own shape *)
  Lemma uimg_view_sub (N : uk_names Σ) (Img M : gmap Z (bv 8))
      (pm : gmap (mword 27) uperm) (sz : Z) :
    uheap (ukn_t N) (ukn_d N) (ukn_s N) M pm sz -∗
    uimg_view N Img -∗
    ⌜ forall (a : Z) (b : bv 8), Img !! a = Some b -> M !! a = Some b ⌝.
  Proof using .
    iIntros "Hheap #Hv". iApply ("Hv" $! M pm sz with "Hheap").
  Qed.

  (* THE TEXT HALF supplies it: this IS the [iDestruct] the landed leaf
     runs, hoisted out of its walk. *)
  Lemma uimg_view_text (N : uk_names Σ) (Img : gmap Z (bv 8)) :
    utext_img (ukn_t N) Img -∗ uimg_view N Img.
  Proof using .
    iIntros "#Ht". rewrite /uimg_view. iIntros "!>" (M pm sz) "Hheap".
    iIntros (a b Hb).
    rewrite /utext_img.
    iDestruct (big_sepM_lookup _ _ a b Hb with "Ht") as "Hb'".
    iDestruct (uheap_text with "Hheap Hb'") as %(HM & _ & _).
    iPureIntro. exact HM.
  Qed.

  (* ...AND SO DOES THE DATA HALF, through [UserHeap.uheap_ubyte] (the
     fractional twin of [uheap_text]) at [DfracDiscarded] -- the step
     [ExecArgs.uargv_img_of_uargv] already takes to read the argv layout
     off the heap the deposit lends.  The predicate is the argv's own:
     [UserHeap.uargv] is built from [ustr … DfracDiscarded], whose bytes
     are [ubyteq γd DfracDiscarded], and [UkFork.v]'s fork image is the
     same map-shaped bundle. *)
  Lemma uimg_view_data (N : uk_names Σ) (Img : gmap Z (bv 8)) :
    ([∗ map] a ↦ b ∈ Img, ubyteq (ukn_d N) DfracDiscarded a b) -∗
    uimg_view N Img.
  Proof using .
    iIntros "#Hd". rewrite /uimg_view. iIntros "!>" (M pm sz) "Hheap".
    iIntros (a b Hb).
    iDestruct (big_sepM_lookup _ _ a b Hb with "Hd") as "Hb'".
    iDestruct (uheap_ubyte with "Hheap Hb'") as %(HM & _ & _).
    iPureIntro. exact HM.
  Qed.

  Lemma wp_uk_ecall_open_recv_gimg (N : uk_names Σ) (h : CpuId)
      (m : regfile) (pc : mword 64) (l : list fdstate) (avail : nat)
      (fdep : sfam) (c : Z) (Img : gmap Z (bv 8)) :
    usysno m = USYS_open ->
    is_aligned_vaddr (Virtaddr (add_vec_int pc 4)) 2 = true ->
    uinstr_is (ukn_t N) pc false (ECALL tt) -∗
    (* the caller's own PERSISTENT view of a piece of its image, at
       WHICHEVER HALF supplies it *)
    uimg_view N Img -∗
    urun N h m pc avail -∗
    (* the program's half of its working directory... *)
    UserCwd.ucwd (ukn_cwd N) c -∗
    (* ...and the deposit at every key whose cwd is that one inum, at the
       family the program will read its receipt at *)
    udepwf_at N m pc USYS_open fdep c -∗
    ustd (ukn_fd N) l -∗
    (∀ (h' : CpuId) (r : mword 64) (W : uvis)
       (M' : gmap Z (bv 8)) (fdv' : list fdstate) (cw' : Z)
       (cs' : gset gname),
       (* THE TRAPPING KEY'S TWO ARGUMENT WORDS ARE THE CALLER'S OWN, which
          is what lets a program that knows its image read its own path
          argument off the receipt ([ArgPath.arg_path_of] at [uvis_M W] and
          [tf_arg_idx 0]). *)
       ⌜ forall (a : Z) (b : bv 8),
           Img !! a = Some b -> uvis_M W !! a = Some b ⌝ -∗
       (* ...AND THE TABLE'S LENGTH, which is what bounds the descriptor a
          receipt names and so lets a caller identify it with the one its
          own ledger decided. *)
       ⌜length (uvis_fd W) = NOFILE⌝ -∗
       ⌜tf_w (uvis_tf W) (tf_arg_idx 0) = m !!! Regidx (mword_of_int 10)⌝ -∗
       ⌜tf_w (uvis_tf W) (tf_arg_idx 1) = m !!! Regidx (mword_of_int 11)⌝ -∗
       (* ...AND ITS CWD AND ITS LEDGER ARE THE CALLER'S OWN TOO *)
       ⌜uvis_cwd W = c⌝ -∗
       ⌜take NSTD (uvis_fd W) = l⌝ -∗
       (* the ledger, exactly [wp_uk_ecall_open]'s two arms *)
       ((∃ (fd : nat) (rd wr : bool) (t : fdtype),
           (* ...AND THE ROW THE ALLOCATION LEFT IN THE RESUME VIEW, beside
              the number and the handle: the receipt's own descriptor row
              is about [fdv'], so without this the caller cannot tie the
              TYPE the receipt names to the SLOT its ledger decided. *)
           ⌜r = (mword_of_int (Z.of_nat fd) : mword 64)
            /\ (fd < NOFILE)%nat
            /\ fdv' = <[fd := FdOpen rd wr t]> (uvis_fd W)
            (* ...AND IT IS NOT A PIPE (survey R4, lane SUP-ONE).  open
               installs an inode or a device and [UsysMemOk.usys_fd_ok]'s
               open row says so; exporting the fact here is what lets a
               holder of this handle take [UkRun.udepw_cl_nopipe]'s FREE
               close instead of a flagged deposit at 21. *)
            /\ fdst_nopipe (FdOpen rd wr t)⌝ ∗
           ualloc (ukn_fd N) l fd (FdOpen rd wr t))
        ∨ (⌜r = (mword_of_int (-1) : mword 64)
             /\ fdv' = uvis_fd W⌝ ∗ ustd (ukn_fd N) l)) -∗
       (* ...AND THE POST, at the TRAPPING key and the resume view *)
       spost_at uslot USYS_open fdep W r M' fdv' cw' cs' -∗
       UserCwd.ucwd (ukn_cwd N) c -∗
       urun N h' (<[Regidx (mword_of_int 10) := r]> m)
         (add_vec_int pc 4) avail -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Hn Hal4.
    iIntros "#Hi #Himg Hrun Hcwd Hsb Hstd Hcont".
    iDestruct "Hrun" as (xi C pt Rfd Rut sz M pm fdv cw gn cs pidv) "(%Hlo & %Hpm & %Hlzf & %HRut & Hheap & Hstk & Hufd & Hcwda & Hcha & #Hmy & #Hdep & #Hnpx & Hb)".
    (* the key's cwd IS the one the caller's PINNED bundle is stated at *)
    iDestruct (ucwd_agree with "Hcwda Hcwd") as %->.
    (* ...and the key's low three slots ARE the caller's own ledger, which
       is what makes the receipt's descriptor row readable at all *)
    iDestruct (ustd_agree (ukn_fd N) fdv l with "Hufd Hstd") as %Htake.
    (* ...AND THE IMAGE ROW: the caller's persistent view is a submap of the
       key's own image, which is what lets it read its path argument off
       the receipt ([ArgPath.arg_path_of] at [uvis_M W]). *)
    iDestruct (uimg_view_sub N Img M pm sz with "Hheap Himg") as %Hsimg.
    (* the deposit, at the family the receipt will come back at *)
    iDestruct "Hsb" as "[%Hfp Hsb]".
    iDestruct ("Hsb" $! M pm sz fdv gn cs pidv with "Hmy Hheap Hufd")
      as "(Hheap & Hufd & Hdepn)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iDestruct (uvb_x0 with "Hb") as "[%Hx0 Hb]".
    iApply (UkStep.wp_uk_ecall C pt Rfd Rut pm sz Hlo Hpm HRut Hlzf M m pc fdv c gn cs pidv Hui
              (fun (s : mstate)
                   (Hp : register_lookup cur_privilege s.(sregs) = User)
                   (Hc : register_lookup (R_bitvector_64 PC) s.(sregs) = pc) =>
                 UserExecFacts.goodmb_execute_ECALL_U UserFrame.Du_r UserFrame.Du_w
                   s pc ltac:(vm_compute; reflexivity)
                   ltac:(vm_compute; reflexivity) Hp Hc)
              with "Hb Hmy").
    rewrite (uexec_ret_ecall _ _ eq_refl).
    assert (Hnum : uvis_num (uvis_of_run m pc M pm sz fdv c gn cs pidv false secc_all) = USYS_open).
    { assert (Hraw : usys_num (uvis_tf (uvis_of_run m pc M pm sz fdv c gn cs pidv false secc_all)) = USYS_open)
        by (cbn [uvis_tf uvis_of_run]; rewrite tf_of_num; exact Hn).
      rewrite uvis_num_full0; [ exact Hraw | reflexivity | rewrite Hraw; usys_range ]. }
    rewrite /uexec_pay_dep /upay_at.
    pose proof Hnum as Hnume. unfold uvis_num in Hnume. rewrite ?Hnum ?Hnume. cbv zeta.
    destruct (decide (uecall_scause = uecall_scause)) as [_ | Hpne];
      [ | exfalso; exact (Hpne eq_refl) ].
    destruct (decide (USYS_open = USYS_exit)) as [He | _];
      [ exfalso; vm_compute in He; discriminate | ].
    destruct (decide (USYS_open = USYS_fork)) as [He | _];
      [ exfalso; vm_compute in He; discriminate | ].
    iExists fdep. rewrite Hfp.
    cbn [uvis_gen uvis_of_run].
    iSplitR; [ iFrame "Hmy" | ].
    iSplitL "Hdepn"; [ iExact "Hdepn" | ].
    iIntros (r M' pm' sz' fdv' cw' gn' cs' lz' secc')
      \"%Hok %Hfdok %Hpiperow %Hcwrow %Hgnrow %Hpidrow %Hliverow %Hscrow %Hchrow Hpost".
    (* THE LAZY BIT CROSSED THE TRAP UNCHANGED (lane LAZY-FLAG, L6).  The
       trapping key is at [false] -- the U tier's run is
       ([UexecRet.ukcq]) -- and every row but sbrk's is the equation
       ([UsysMemOk.usys_mem_ok_lazy]), so the resume key is at [false] too
       and the close below is at the run's own bit. *)
    assert (Hlzq : lz' = false)
      by (refine (usys_mem_ok_lazy _ _ _ _ _ _ _ _ _ _ _ _ Hok);
          first [ assumption | vm_compute; discriminate ]).
    subst lz'.
    (* ...AND SO DID THE MASK: not seccomp's number, so the row is the
       equation ([UsysMemOk.usys_secc_ok_quiet]), and the resume key is at
       the full mask [urun] is keyed at *)
    pose proof (fun Hne => usys_secc_ok_quiet _ _ _ _ _ Hne Hscrow) as Hscq.
    specialize (Hscq ltac:(usys_range)).
    cbn [uvis_secc uvis_of_run] in Hscq. subst secc'.
    assert (Hcw : cw' = c)
      by (refine (usys_cwd_ok_quiet _ _ _ _ _ Hcwrow); vm_compute; discriminate).
    assert (Hgn : gn' = gn) by exact (usys_gen_ok_quiet _ _ _ Hgnrow).
    assert (Hch : cs' = cs) by exact (usys_ch_ok_quiet _ _ _ _ Hchrow).
    subst gn' cs' cw'.
    destruct (usys_mem_ok_quiet USYS_open _ r _ _ _ _ _ _ _ _
                ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)
                ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) Hok)
      as [-> [-> ->]].
    unfold usys_fd_ok in Hfdok.
    destruct (decide (USYS_open = USYS_close)) as [Hc | _]; [ discriminate Hc | ].
    destruct (decide (USYS_open = USYS_dup)) as [Hc | _]; [ discriminate Hc | ].
    destruct (decide (USYS_open = USYS_open)) as [_ | Hc];
      [ | exfalso; exact (Hc eq_refl) ].
    cbn [uvis_M uvis_perm uvis_fd uvis_of_run] in Hfdok |- *.
    iDestruct (ufd_auth_len with "Hufd") as %Hfdlen.
    iApply uslot_bupd.
    destruct Hfdok as [(fd & rd & wr & t & Hr & Hcl & -> & Hnpo) | [Hrm ->]].
    - (* A DESCRIPTOR CAME BACK, at the LOWEST free slot, and the RECEIPT
         says at which type *)
      iMod (ufd_alloc_least (ukn_fd N) fdv l fd (FdOpen rd wr t) Hcl
              ltac:(discriminate) with "Hufd Hstd") as "[Hufd Hh]".
      iModIntro.
      (* ...and open installs an inode or a device, never a pipe end *)
      iDestruct (urun_rows_insert N fdv fd (FdOpen rd wr t) Hnpo
                   with "Hnpx") as "#Hnpi".
      rewrite (uslot_bump_run m pc M M pm pm sz sz fdv
                 (<[fd := FdOpen rd wr t]> fdv) c c gn gn cs cs pidv false false secc_all secc_all r Hx0 Hal4).
      iApply ukcq_ukc.
      iApply (urun_close_upd _ _ _ m (mword_of_int 10) _ _ _ _ _ _ _ _ _
                ltac:(unfold unot_sp; vm_compute; discriminate)
                with "Hheap Hstk Hufd Hcwda Hcha Hmy Hdep Hnpi").
      iIntros (h') "Hrun".
      iApply ("Hcont" $! h' r (uvis_of_run m pc M pm sz fdv c gn cs pidv false secc_all)
                _ _ _ _ with "[%] [%] [%] [%] [%] [%] [Hh] Hpost Hcwd Hrun").
      { exact Hsimg. }
      { rewrite (uvis_of_run_fd m pc M pm sz fdv c gn cs pidv false secc_all). exact Hfdlen. }
      { rewrite /tf_w. cbn [uvis_tf uvis_of_run]. exact (tf_of_arg0 m pc). }
      { rewrite /tf_w. cbn [uvis_tf uvis_of_run]. exact (tf_of_arg1 m pc). }
      { exact (uvis_of_run_cwd m pc M pm sz fdv c gn cs pidv false secc_all). }
      { rewrite (uvis_of_run_fd m pc M pm sz fdv c gn cs pidv false secc_all). exact Htake. }
      iLeft. iExists fd, rd, wr, t. iFrame "Hh". iPureIntro.
      split_and!; [ exact Hr | | | exact Hnpo ].
      { rewrite <- Hfdlen. exact (fd_least_closed_lt _ _ Hcl). }
      rewrite (uvis_of_run_fd m pc M pm sz fdv c gn cs pidv false secc_all). reflexivity.
    - (* the call failed: nothing moved, and the ledger comes straight back *)
      iModIntro.
      rewrite (uslot_bump_run m pc M M pm pm sz sz fdv fdv c c gn gn cs cs pidv false false secc_all secc_all r Hx0 Hal4).
      iApply ukcq_ukc.
      iApply (urun_close_upd _ _ _ m (mword_of_int 10) _ _ _ _ _ _ _ _ _
                ltac:(unfold unot_sp; vm_compute; discriminate)
                with "Hheap Hstk Hufd Hcwda Hcha Hmy Hdep Hnpx").
      iIntros (h') "Hrun".
      iApply ("Hcont" $! h' r (uvis_of_run m pc M pm sz fdv c gn cs pidv false secc_all)
                _ _ _ _ with "[%] [%] [%] [%] [%] [%] [Hstd] Hpost Hcwd Hrun").
      { exact Hsimg. }
      { rewrite (uvis_of_run_fd m pc M pm sz fdv c gn cs pidv false secc_all). exact Hfdlen. }
      { rewrite /tf_w. cbn [uvis_tf uvis_of_run]. exact (tf_of_arg0 m pc). }
      { rewrite /tf_w. cbn [uvis_tf uvis_of_run]. exact (tf_of_arg1 m pc). }
      { exact (uvis_of_run_cwd m pc M pm sz fdv c gn cs pidv false secc_all). }
      { rewrite (uvis_of_run_fd m pc M pm sz fdv c gn cs pidv false secc_all). exact Htake. }
      iRight. iFrame "Hstd". iPureIntro. split; [ exact Hrm | ].
      rewrite (uvis_of_run_fd m pc M pm sz fdv c gn cs pidv false secc_all). reflexivity.
  Qed.

  (* ---- THE DATA-IMAGE LEAF, which is what cat and the redirect child
     take.  Its post is the TEXT leaf's, word for word: the same image row
     comes back at [uvis_M W]. *)
  Lemma wp_uk_ecall_open_recv_dimg (N : uk_names Σ) (h : CpuId)
      (m : regfile) (pc : mword 64) (l : list fdstate) (avail : nat)
      (fdep : sfam) (c : Z) (Img : gmap Z (bv 8)) :
    usysno m = USYS_open ->
    is_aligned_vaddr (Virtaddr (add_vec_int pc 4)) 2 = true ->
    uinstr_is (ukn_t N) pc false (ECALL tt) -∗
    ([∗ map] a ↦ b ∈ Img, ubyteq (ukn_d N) DfracDiscarded a b) -∗
    urun N h m pc avail -∗
    UserCwd.ucwd (ukn_cwd N) c -∗
    udepwf_at N m pc USYS_open fdep c -∗
    ustd (ukn_fd N) l -∗
    (∀ (h' : CpuId) (r : mword 64) (W : uvis)
       (M' : gmap Z (bv 8)) (fdv' : list fdstate) (cw' : Z)
       (cs' : gset gname),
       ⌜ forall (a : Z) (b : bv 8),
           Img !! a = Some b -> uvis_M W !! a = Some b ⌝ -∗
       ⌜length (uvis_fd W) = NOFILE⌝ -∗
       ⌜tf_w (uvis_tf W) (tf_arg_idx 0) = m !!! Regidx (mword_of_int 10)⌝ -∗
       ⌜tf_w (uvis_tf W) (tf_arg_idx 1) = m !!! Regidx (mword_of_int 11)⌝ -∗
       ⌜uvis_cwd W = c⌝ -∗
       ⌜take NSTD (uvis_fd W) = l⌝ -∗
       ((∃ (fd : nat) (rd wr : bool) (t : fdtype),
           ⌜r = (mword_of_int (Z.of_nat fd) : mword 64)
            /\ (fd < NOFILE)%nat
            /\ fdv' = <[fd := FdOpen rd wr t]> (uvis_fd W)
            (* ...AND IT IS NOT A PIPE (survey R4, lane SUP-ONE).  open
               installs an inode or a device and [UsysMemOk.usys_fd_ok]'s
               open row says so; exporting the fact here is what lets a
               holder of this handle take [UkRun.udepw_cl_nopipe]'s FREE
               close instead of a flagged deposit at 21. *)
            /\ fdst_nopipe (FdOpen rd wr t)⌝ ∗
           ualloc (ukn_fd N) l fd (FdOpen rd wr t))
        ∨ (⌜r = (mword_of_int (-1) : mword 64)
             /\ fdv' = uvis_fd W⌝ ∗ ustd (ukn_fd N) l)) -∗
       spost_at uslot USYS_open fdep W r M' fdv' cw' cs' -∗
       UserCwd.ucwd (ukn_cwd N) c -∗
       urun N h' (<[Regidx (mword_of_int 10) := r]> m)
         (add_vec_int pc 4) avail -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Hn Hal4. iIntros "#Hi #Hd Hrun Hcwd Hsb Hstd Hcont".
    iApply (wp_uk_ecall_open_recv_gimg N h m pc l avail fdep c Img Hn Hal4
              with "Hi [] Hrun Hcwd Hsb Hstd Hcont").
    iApply (uimg_view_data N Img with "Hd").
  Qed.



  Lemma wp_uk_ecall_quiet_recv_img (N : uk_names Σ) (h : CpuId)
      (m : regfile) (pc : mword 64) (n : Z) (avail : nat) (fdep : sfam)
      (c : Z) (Img : gmap Z (bv 8)) :
    usysno m = n ->
    n <> USYS_exit -> n <> USYS_fork ->
    n <> USYS_exec -> n <> USYS_sbrk ->
    n <> USYS_wait -> n <> USYS_pipe -> n <> USYS_read -> n <> USYS_fstat ->
    n <> USYS_close -> n <> USYS_dup -> n <> USYS_open ->
    n <> USYS_chdir ->
    is_aligned_vaddr (Virtaddr (add_vec_int pc 4)) 2 = true ->
    uinstr_is (ukn_t N) pc false (ECALL tt) -∗
    (* the caller's own PERSISTENT view of a piece of its image *)
    utext_img (ukn_t N) Img -∗
    urun N h m pc avail -∗
    UserCwd.ucwd (ukn_cwd N) c -∗
    udepwf_at N m pc n fdep c -∗
    (∀ (h' : CpuId) (r : mword 64) (W : uvis) (cs' : gset gname),
       ⌜ forall (a : Z) (b : bv 8),
           Img !! a = Some b -> uvis_M W !! a = Some b ⌝ -∗
       ⌜tf_w (uvis_tf W) (tf_arg_idx 0) = m !!! Regidx (mword_of_int 10)⌝ -∗
       ⌜tf_w (uvis_tf W) (tf_arg_idx 1) = m !!! Regidx (mword_of_int 11)⌝ -∗
       ⌜tf_w (uvis_tf W) (tf_arg_idx 2) = m !!! Regidx (mword_of_int 12)⌝ -∗
       ⌜uvis_cwd W = c⌝ -∗
       spost_at uslot n fdep W r (uvis_M W) (uvis_fd W) c cs' -∗
       UserCwd.ucwd (ukn_cwd N) c -∗
       urun N h' (<[Regidx (mword_of_int 10) := r]> m)
         (add_vec_int pc 4) avail -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Hn Hexit Hfork Hexec Hsbrk H3 H4 H5 H8 Hcl Hdp Hop Hcd Hal4.
    iIntros "#Hi #Himg Hrun Hcwd Hsb Hcont".
    iDestruct "Hrun" as (xi C pt Rfd Rut sz M pm fdv cw gn cs pidv) "(%Hlo & %Hpm & %Hlzf & %HRut & Hheap & Hstk & Hufd & Hcwda & Hcha & #Hmy & #Hdep & #Hnpx & Hb)".
    iDestruct (ucwd_agree with "Hcwda Hcwd") as %->.
    (* ...AND THE IMAGE ROW ([wp_uk_ecall_open_recv_img]'s) *)
    iAssert (⌜ forall (a : Z) (b : bv 8),
                Img !! a = Some b -> M !! a = Some b ⌝)%I as %Hsimg.
    { iIntros (a b Hb).
      iDestruct (big_sepM_lookup _ _ a b Hb with "Himg") as "Hb'".
      iDestruct (uheap_text with "Hheap Hb'") as %(HM & _ & _).
      iPureIntro. exact HM. }
    iDestruct "Hsb" as "[%Hfp Hsb]".
    iDestruct ("Hsb" $! M pm sz fdv gn cs pidv with "Hmy Hheap Hufd")
      as "(Hheap & Hufd & Hdepn)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iDestruct (uvb_x0 with "Hb") as "[%Hx0 Hb]".
    iApply (UkStep.wp_uk_ecall C pt Rfd Rut pm sz Hlo Hpm HRut Hlzf M m pc fdv c gn cs pidv Hui
              (fun (s : mstate)
                   (Hp : register_lookup cur_privilege s.(sregs) = User)
                   (Hc : register_lookup (R_bitvector_64 PC) s.(sregs) = pc) =>
                 UserExecFacts.goodmb_execute_ECALL_U UserFrame.Du_r UserFrame.Du_w
                   s pc ltac:(vm_compute; reflexivity)
                   ltac:(vm_compute; reflexivity) Hp Hc)
              with "Hb Hmy").
    rewrite (uexec_ret_ecall _ _ eq_refl).
    assert (Hnum : uvis_num (uvis_of_run m pc M pm sz fdv c gn cs pidv false secc_all) = n).
    { assert (Hraw : usys_num (uvis_tf (uvis_of_run m pc M pm sz fdv c gn cs pidv false secc_all)) = n)
        by (cbn [uvis_tf uvis_of_run]; rewrite tf_of_num; exact Hn).
      rewrite uvis_num_full0; [ exact Hraw | reflexivity | rewrite Hraw; usys_range ]. }
    rewrite /uexec_pay_dep /upay_at.
    pose proof Hnum as Hnume. unfold uvis_num in Hnume. rewrite ?Hnum ?Hnume. cbv zeta.
    destruct (decide (uecall_scause = uecall_scause)) as [_ | Hpne];
      [ | exfalso; exact (Hpne eq_refl) ].
    destruct (decide (n = USYS_exit)) as [He | _]; [ exfalso; exact (Hexit He) | ].
    destruct (decide (n = USYS_fork)) as [He | _]; [ exfalso; exact (Hfork He) | ].
    destruct (decide (n = USYS_wait)) as [He | _]; [ exfalso; exact (H3 He) | ].
    iExists fdep. rewrite Hfp.
    cbn [uvis_gen uvis_of_run].
    iSplitR; [ iFrame "Hmy" | ].
    iSplitL "Hdepn"; [ iExact "Hdepn" | ].
    iIntros (r M' pm' sz' fdv' cw' gn' cs' lz' secc')
      \"%Hok %Hfdok %Hpiperow %Hcwrow %Hgnrow %Hpidrow %Hliverow %Hscrow %Hchrow Hpost".
    (* THE LAZY BIT CROSSED THE TRAP UNCHANGED (lane LAZY-FLAG, L6).  The
       trapping key is at [false] -- the U tier's run is
       ([UexecRet.ukcq]) -- and every row but sbrk's is the equation
       ([UsysMemOk.usys_mem_ok_lazy]), so the resume key is at [false] too
       and the close below is at the run's own bit. *)
    assert (Hlzq : lz' = false)
      by (refine (usys_mem_ok_lazy _ _ _ _ _ _ _ _ _ _ _ _ Hok);
          first [ assumption | vm_compute; discriminate ]).
    subst lz'.
    (* ...AND SO DID THE MASK: not seccomp's number, so the row is the
       equation ([UsysMemOk.usys_secc_ok_quiet]), and the resume key is at
       the full mask [urun] is keyed at *)
    pose proof (fun Hne => usys_secc_ok_quiet _ _ _ _ _ Hne Hscrow) as Hscq.
    specialize (Hscq ltac:(usys_range)).
    cbn [uvis_secc uvis_of_run] in Hscq. subst secc'.
    assert (Hcw : cw' = c) by (exact (usys_cwd_ok_quiet n r c cw' Hcd Hcwrow)).
    assert (Hgn : gn' = gn) by exact (usys_gen_ok_quiet _ _ _ Hgnrow).
    assert (Hch : cs' = cs) by exact (usys_ch_ok_quiet _ _ _ _ Hchrow).
    subst gn' cs' cw'.
    destruct (usys_mem_ok_quiet n _ r _ _ _ _ _ _ _ _ Hexec Hsbrk H3 H4 H5 H8 Hok)
      as [-> [-> ->]].
    pose proof (usys_fd_ok_quiet n _ r _ _ Hcl Hdp Hop H4 Hfdok) as ->.
    cbn [uvis_M uvis_perm uvis_of_run].
    rewrite (uslot_bump_run m pc M M pm pm sz sz fdv fdv c c gn gn cs cs pidv false false secc_all secc_all r Hx0 Hal4).
    iApply ukcq_ukc.
    iApply (urun_close_upd _ _ _ m (mword_of_int 10) _ _ _ _ _ _ _ _ _
              ltac:(unfold unot_sp; vm_compute; discriminate)
              with "Hheap Hstk Hufd Hcwda Hcha Hmy Hdep Hnpx").
    iIntros (h') "Hrun".
    iApply ("Hcont" $! h' r (uvis_of_run m pc M pm sz fdv c gn cs pidv false secc_all) cs
              with "[%] [%] [%] [%] [%] [Hpost] Hcwd Hrun").
    { exact Hsimg. }
    { rewrite /tf_w. cbn [uvis_tf uvis_of_run]. exact (tf_of_arg0 m pc). }
    { rewrite /tf_w. cbn [uvis_tf uvis_of_run]. exact (tf_of_arg1 m pc). }
    { rewrite /tf_w. cbn [uvis_tf uvis_of_run]. exact (tf_of_arg2 m pc). }
    { exact (uvis_of_run_cwd m pc M pm sz fdv c gn cs pidv false secc_all). }
    rewrite (uvis_of_run_fd m pc M pm sz fdv c gn cs pidv false secc_all).
    cbn [uvis_M uvis_of_run]. iExact "Hpost".
  Qed.

  (* THE PAGE FLOOR OF AN ADDRESS AT OR ABOVE A PAGE BOUNDARY is itself at
     or above it -- the one arithmetic fact the sbrk leaf's two page-set
     arguments turn on. *)
  Local Lemma upage_floor_ge (a c : Z) :
    0 <= c -> c mod 4096 = 0 -> c <= a -> c <= (a / 4096) * 4096.
  Proof using .
    intros Hc0 Hcm Hle.
    assert (Hk : c = 4096 * (c / 4096))
      by (apply (proj2 (Z.div_exact c 4096 ltac:(discriminate))); exact Hcm).
    assert (Hdiv : c / 4096 <= a / 4096)
      by (apply Z.div_le_mono; [ lia | exact Hle ]).
    lia.
  Qed.

  (* ...and the page number of an in-region address, in the shape the page
     sets are stated at *)
  Local Lemma usvpn_floor (a : Z) :
    0 <= a < 2 ^ 38 ->
    bv_unsigned (svpn_of (mword_of_int a : mword 64)) * 4096 = (a / 4096) * 4096.
  Proof using .
    intros Ha.
    rewrite (ProcPtOwn.svpn_of_unsigned_gen (mword_of_int a : mword 64)).
    rewrite <- uint_unsigned. rewrite (uint_moi a ltac:(unfold Z64; lia)).
    rewrite (Z.mod_small (a / 4096) 134217728); [ reflexivity | ].
    split; [ apply Z.div_pos; lia | ].
    apply Z.div_lt_upper_bound; lia.
  Qed.

  (* ------------------------------------------------------------------- *)
  (* ecall, at SBRK -- THE ENTRY THAT MOVES THE ADDRESS SPACE.             *)
  (*                                                                       *)
  (* Every other row leaves the process's memory where it was; this one    *)
  (* GROWS it, and the whole point of the call is that the caller comes    *)
  (* back OWNING the new bytes.  Three rows meet here:                     *)
  (*                                                                       *)
  (*   the IMAGE row  [usys_sbrk_img]: the image gained the bytes that     *)
  (*     became readable, as zeros ([UserPtTree.umem_grow]);               *)
  (*   the MAP row    [usys_sbrk_perm]: the pages that became live are in  *)
  (*     the permission view at RW;                                        *)
  (*   the ANSWER row [usys_sbrk_ret]: -1 and nothing moved, or the OLD    *)
  (*     break back and the break up by exactly the argument.              *)
  (*                                                                       *)
  (* The third is what makes the other two usable: without it a caller     *)
  (* learns that memory grew and not WHERE, and [malloc] cannot own the    *)
  (* block it just asked for.  It is carried from [SpecSysSbrk.            *)
  (* sys_sbrk_ok] through the dispatcher's returning post.                  *)
  (*                                                                       *)
  (* THE PAGE-ALIGNED BREAK IS A PREMISE, and it is what makes the run     *)
  (* FRESH: [UserHeap.uheap]'s map-stop clause says the key has no page at *)
  (* or above [pgroundup sz], so on an aligned break every address the     *)
  (* call adds is on a page the process did not have -- hence a byte the   *)
  (* data authority does not record, hence one this leaf can mint.  exec   *)
  (* leaves the break page-aligned and [malloc]'s [morecore] asks for      *)
  (* whole pages, so no caller pays for it.                                *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_uk_ecall_sbrk (N : uk_names Σ) (h : CpuId) (m : regfile)
      (pc : mword 64) (sz n : Z) (avail : nat) :
    usysno m = USYS_sbrk ->
    (* the argument, as [argint] reads it back: the low 32 bits of a0, sign
       extended -- [UsysMemOk.usys_sbrk_arg] at this trapframe *)
    sint (sign_extend' 64 (trunc32 (m !!! Regidx (mword_of_int 10)))) = n ->
    (* ...AND THE SECOND ARGUMENT IS SBRK_EAGER (lane LAZY-FLAG, K3/L6).
       This fork has two sbrk calls: [sbrk(n)] passes SBRK_EAGER = 1 and
       [sbrklazy(n)] passes SBRK_LAZY ([ulib.c:153/159], [vm.h:1-2]).  Only
       the EAGER call MAPS the run it hands back, and only the EAGER call
       keeps [UexecSlot.uvis_lazy] at [false] -- which the U tier's run is
       hardwired at ([UexecRet.ukcq]) -- so this leaf is the eager one and
       says so.  [UsysMemOk.usys_sbrk_eager] is this equation at
       [tf_arg_idx 1], i.e. at a1. *)
    sign_extend' 64 (trunc32 (m !!! Regidx (mword_of_int 11)))
      = (mword_of_int 1 : mword 64) ->
    0 <= n -> 0 <= sz -> usz_ok (sz + n) ->
    pgroundup sz = sz ->
    is_aligned_vaddr (Virtaddr (add_vec_int pc 4)) 2 = true ->
    uinstr_is (ukn_t N) pc false (ECALL tt) -∗
    urun N h m pc avail -∗
    udepw N m pc USYS_sbrk -∗
    usz (ukn_s N) sz -∗
    (∀ (h' : CpuId) (r : mword 64),
       ((⌜ r = (mword_of_int (-1) : mword 64) ⌝ ∗ usz (ukn_s N) sz)
        ∨ (⌜ r = (mword_of_int sz : mword 64) ⌝ ∗ usz (ukn_s N) (sz + n) ∗
           ∃ g : nat -> bv 8, ubytes (ukn_d N) sz (Z.to_nat n) g)) -∗
       urun N h' (<[Regidx (mword_of_int 10) := r]> m)
         (add_vec_int pc 4) avail -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Hn Harg Heag Hn0 Hsz0 Hszok' Hal Hal4.
    (* the new break is inside the user region, which is what every bound
       below reads off [usz_ok] *)
    assert (Hhi : (sz + n < 2 ^ 38)%Z).
    { pose proof (pgroundup_ge (sz + n) ltac:(lia)) as Hge.
      unfold usz_ok in Hszok'.
      change (2 ^ 38)%Z with 274877906944%Z. lia. }
    iIntros "#Hi Hrun Hsb Hsz Hcont".
    iDestruct "Hrun" as (xi C pt Rfd Rut szk M pm fdv cw gn cs pidv)
      "(%Hlo & %Hpm & %Hlzf & %HRut & Hheap & Hstk & Hufd & Hcwda & Hcha & #Hmy & #Hdep & #Hnpx & Hb)".
    iMod (udepw_mint N m pc _ M pm _ fdv cw gn cs pidv
                with "Hdep Hmy Hsb Hheap Hufd") as "(Hheap & Hufd & Hdepn)".
    (* the key's break IS the program's *)
    iDestruct (uheap_usz with "Hheap Hsz") as %->.
    iDestruct (uheap_stop with "Hheap") as %Hstoppg.
    (* the map-stop clause, at ADDRESSES: a page at or above the break's own
       page is not in the map, so no address on it is either *)
    assert (Hstop : forall a : Z, pgroundup sz <= a < 2 ^ 38 ->
              pm !! svpn_of (mword_of_int a : mword 64) = None).
    { intros a Ha.
      destruct (pm !! svpn_of (mword_of_int a : mword 64)) as [q |] eqn:E;
        [ exfalso | reflexivity ].
      pose proof (Hstoppg _ q E) as Hlt.
      rewrite (usvpn_floor a ltac:(lia)) in Hlt.
      assert (Hgep : pgroundup sz <= (a / 4096) * 4096).
      { apply upage_floor_ge; [ | | lia ].
        - unfold pgroundup.
          pose proof (Z.mul_div_le (sz + 4095) 4096 ltac:(lia)).
          assert (H0 : (0 <= (sz + 4095) / 4096)%Z)
            by (apply Z.div_pos; lia).
          lia.
        - unfold pgroundup. apply Z_mod_mult. }
      lia. }
    iDestruct (uheap_canon with "Hheap") as %Hcanon.
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iDestruct (UkStep.uvb_pure with "Hb") as "[%Hpure Hb]".
    destruct Hpure as [Mp Hpure].
    iDestruct (uvb_x0 with "Hb") as "[%Hx0 Hb]".
    iApply (UkStep.wp_uk_ecall C pt Rfd Rut pm sz Hlo Hpm HRut Hlzf M m pc fdv cw gn cs pidv Hui
              (fun (s : mstate)
                   (Hp : register_lookup cur_privilege s.(sregs) = User)
                   (Hc : register_lookup (R_bitvector_64 PC) s.(sregs) = pc) =>
                 UserExecFacts.goodmb_execute_ECALL_U UserFrame.Du_r UserFrame.Du_w
                   s pc ltac:(vm_compute; reflexivity)
                   ltac:(vm_compute; reflexivity) Hp Hc)
              with "Hb Hmy").
    rewrite (uexec_ret_ecall _ _ eq_refl).
    assert (Hnum : uvis_num (uvis_of_run m pc M pm sz fdv cw gn cs pidv false secc_all)
                   = USYS_sbrk).
    { assert (Hraw : usys_num (uvis_tf (uvis_of_run m pc M pm sz fdv cw gn cs pidv false secc_all)) = USYS_sbrk)
        by (cbn [uvis_tf uvis_of_run]; rewrite tf_of_num; exact Hn).
      rewrite uvis_num_full0; [ exact Hraw | reflexivity | rewrite Hraw; usys_range ]. }
    (* the PAYMENT's guard IS the deposit's own, so it is opened BEFORE the
       number is rewritten and the destructs below then reduce both copies
       at once *)
    rewrite /uexec_pay_dep /upay_at.
    pose proof Hnum as Hnume. unfold uvis_num in Hnume. rewrite ?Hnum ?Hnume. cbv zeta.
    destruct (decide (uecall_scause = uecall_scause)) as [_ | Hpne];
      [ | exfalso; exact (Hpne eq_refl) ].
    destruct (decide (USYS_sbrk = USYS_exit)) as [He | _];
      [ exfalso; discriminate He | ].
    destruct (decide (USYS_sbrk = USYS_fork)) as [He | _];
      [ exfalso; discriminate He | ].
    (* the arm binds the deposit's FAMILIES ([UexecSG.v]'s header); the
       law mints at some [f] and this leaf, which discards its post,
       hands that witness straight over. *)
    (* THE MINT ALREADY NAMED THE PAYLOAD (app-echo.md, "SH-LINE RULING",
       R1): read's bundle is a wand from the depositing process's own exit
       payload, so nothing is re-keyed here any more -- the family the
       deposit came at IS at [ukn_pay N]. *)
    iDestruct "Hdepn" as (fdep) "[%Hfp Hdepn]".
    iExists fdep. rewrite Hfp.
    cbn [uvis_gen uvis_of_run].
    iSplitR; [ iFrame "Hmy" | ].
    iSplitL "Hdepn"; [ iExact "Hdepn" | ].
    iIntros (r M' pm' sz' fdv' cw' gn' cs' lz' secc') "%Hok %Hfdok %Hpiperow %Hcwrow %Hgnrow %Hpidrow %Hliverow %Hscrow %Hchrow _".
    (* THE CWD CROSSED THE TRAP UNCHANGED -- chdir is the one row that moves
       it, and this is not it -- so the engine's half is re-keyed onto the
       view the process resumes at and the program's half never moved. *)
    assert (Hcw : cw' = cw)
      by (refine (usys_cwd_ok_quiet _ _ _ _ _ Hcwrow); vm_compute; discriminate).
    iDestruct (ucwd_auth_quiet N cw cw' Hcw with "Hcwda") as "Hcwda".
    (* ...AND SO DID THE GENERATION AND THE CHILDREN SET: no entry
       re-incarnates its caller, and this lane's children row is the
       identity at every number ([UsysMemOk] SS2e/SS2f).  Both are
       substituted rather than re-keyed -- the generation has no
       authority beside it, and the children authority is already at
       the set the process resumes at. *)
    assert (Hgn : gn' = gn) by exact (usys_gen_ok_quiet _ _ _ Hgnrow).
    assert (Hch : cs' = cs) by exact (usys_ch_ok_quiet _ _ _ _ Hchrow).
    subst gn' cs'.
    cbn [uvis_M uvis_perm uvis_sz uvis_fd uvis_cwd uvis_of_run] in Hok |- *.
    (* the row, in three pieces *)
    unfold usys_mem_ok in Hok.
    destruct (decide (USYS_sbrk = USYS_exec)) as [He | _];
      [ exfalso; discriminate He | ].
    destruct (decide (USYS_sbrk = USYS_sbrk)) as [_ | Hc];
      [ | exfalso; exact (Hc eq_refl) ].
    destruct Hok as (Himg & Hperm & Hret & Hlzrow).
    (* THE LAZY BIT IS KEPT, off the EAGER argument this leaf is stated at
       (lane LAZY-FLAG, K3): [UsysMemOk.usys_sbrk_lazy]'s guard is the
       disjunction the C branches on, and a call that passed SBRK_EAGER is
       on its left.  The trapping key is at [false] (the U tier's run,
       [UexecRet.ukcq]), so the resume key is at [false] too. *)
    assert (Hlzq : lz' = false).
    { refine (Hlzrow (or_introl _) _); [ | reflexivity ].
      unfold usys_sbrk_eager. cbn [uvis_tf uvis_of_run].
      rewrite tf_of_arg1. exact Heag. }
    subst lz'.
    (* ...AND SO DID THE MASK: not seccomp's number, so the row is the
       equation ([UsysMemOk.usys_secc_ok_quiet]), and the resume key is at
       the full mask [urun] is keyed at *)
    pose proof (fun Hne => usys_secc_ok_quiet _ _ _ _ _ Hne Hscrow) as Hscq.
    specialize (Hscq ltac:(usys_range)).
    cbn [uvis_secc uvis_of_run] in Hscq. subst secc'.
    (* the descriptor view does not move: sbrk is none of the four *)
    assert (Hview : fdv' = fdv).
    { apply (usys_fd_ok_quiet USYS_sbrk
               (uvis_tf (uvis_of_run m pc M pm sz fdv cw gn cs pidv false secc_all)) r fdv fdv');
        [ | | | | exact Hfdok ]; vm_compute; discriminate. }
    rewrite Hview.
    (* the argument the row reads is the one the caller named *)
    assert (Harg' : usys_sbrk_arg (uvis_tf (uvis_of_run m pc M pm sz fdv cw gn cs pidv false secc_all))
                    = sign_extend' 64 (trunc32 (m !!! Regidx (mword_of_int 10)))).
    { cbn [uvis_tf uvis_of_run]. unfold usys_sbrk_arg.
      rewrite tf_of_arg0. reflexivity. }
    unfold usys_sbrk_ret in Hret. rewrite Harg' in Hret.
    destruct Hret as [(Hr & Hsz') | (Hr & Hup)].
    - (* ---- FAILED: the break did not move, so neither did the image ---- *)
      subst sz'.
      unfold usys_sbrk_img in Himg.
      destruct (decide (uint (mword_of_int sz) <= uint (mword_of_int sz))%Z)
        as [_ | Hc]; [ | exfalso; exact (Hc (Z.le_refl _)) ].
      unfold usys_sbrk_perm in Hperm.
      destruct (decide (uint (mword_of_int sz) <= uint (mword_of_int sz))%Z)
        as [_ | Hc]; [ | exfalso; exact (Hc (Z.le_refl _)) ].
      rewrite difference_diag_L gset_to_gmap_empty right_id_L in Hperm.
      subst pm'.
      (* the image gained nothing it did not already have: the grow is at
         the SAME size, and every live byte is already recorded *)
      assert (Hui38 : uint (mword_of_int sz : mword 64) = sz)
        by (apply uint_moi; unfold Z64; lia).
      (* the grow is at the SAME size, and every live byte is already
         recorded, so the image did not move ([umem_grow_id]) *)
      assert (HMg : umem_grow M (uint (mword_of_int sz : mword 64)) = M).
      { rewrite Hui38. apply umem_grow_id.
        intros a Ha. exact (proj2 (ukp_img pt sz M Mp a Hpure) (or_intror Ha)). }
      subst M'. rewrite HMg.
      rewrite (uslot_bump_run m pc M M pm pm sz sz fdv fdv cw cw' gn gn cs cs pidv false false secc_all secc_all r Hx0 Hal4).
      iApply ukcq_ukc.
      iApply (urun_close_upd N M pm m (mword_of_int 10) r sz fdv cw' gn cs pidv
                (add_vec_int pc 4) avail
                ltac:(unfold unot_sp; vm_compute; discriminate)
                with "Hheap Hstk Hufd Hcwda Hcha Hmy Hdep Hnpx [Hcont Hsz]").
      iIntros (h'') "Hrun".
      iApply ("Hcont" $! h'' r with "[Hsz] Hrun").
      iLeft. iSplitR; [ iPureIntro; exact Hr | ]. iExact "Hsz".
    - (* ---- SUCCEEDED: the break moved up by the argument ---- *)
      rewrite Harg in Hup. specialize (Hup Hn0). subst sz'.
      (* the image row, at the two sizes the answer names *)
      assert (Hle : (uint (mword_of_int sz : mword 64)
                     <= uint (mword_of_int (sz + n) : mword 64))%Z).
      { rewrite (uint_moi sz ltac:(unfold Z64; lia)).
        rewrite (uint_moi (sz + n) ltac:(unfold Z64; lia)). lia. }
      unfold usys_sbrk_img in Himg.
      destruct (decide (uint (mword_of_int sz : mword 64)
                        <= uint (mword_of_int (sz + n) : mword 64))%Z)
        as [_ | Hc]; [ | exfalso; exact (Hc Hle) ].
      rewrite (uint_moi (sz + n) ltac:(unfold Z64; lia)) in Himg.
      unfold usys_sbrk_perm in Hperm.
      destruct (decide (uint (mword_of_int sz : mword 64)
                        <= uint (mword_of_int (sz + n) : mword 64))%Z)
        as [_ | Hc]; [ | exfalso; exact (Hc Hle) ].
      rewrite (uint_moi sz ltac:(unfold Z64; lia)) in Hperm.
      rewrite (uint_moi (sz + n) ltac:(unfold Z64; lia)) in Hperm.
      (* ---- the three facts [uheap_grow_run] wants, off the map row ---- *)
      assert (Hext : forall p : mword 27, is_Some (pm !! p) ->
                pm' !! p = pm !! p).
      { intros p [q Hq]. rewrite Hperm Hq.
        exact (lookup_union_Some_l _ _ p q Hq). }
      assert (Hszok : usz_ok sz) by exact (ukp_sz pt sz M Mp Hpure).

      assert (Hfresh : forall a : Z, sz <= a < sz + n -> uw_addr pm' a).
      { intros a Ha.
        assert (Hbnd : (0 <= a < 2 ^ 38)%Z) by lia.
        assert (Hfl : bv_unsigned (svpn_of (mword_of_int a : mword 64)) * 4096
                      = (a / 4096) * 4096) by exact (usvpn_floor a Hbnd).
        assert (Hszm : sz mod 4096 = 0).
        { rewrite <- Hal. unfold pgroundup. apply Z_mod_mult. }
        assert (Hge : sz <= (a / 4096) * 4096)
          by (apply upage_floor_ge; [ lia | exact Hszm | lia ]).
        assert (Hnone : pm !! svpn_of (mword_of_int a) = None)
          by (apply Hstop; rewrite Hal; lia).
        exists uperm_rw. split; [ | reflexivity ].
        unfold uperm_at. rewrite Hperm.
        rewrite (lookup_union_r pm _ _ Hnone).
        apply lookup_gset_to_gmap_Some. split; [ | reflexivity ].
        apply elem_of_difference. split.
        - apply live_pages_mem. rewrite Hfl.
          pose proof (pgroundup_ge (sz + n) ltac:(lia)).
          pose proof (Z.mul_div_le a 4096 ltac:(lia)). lia.
        - intro Hin.
          pose proof (live_pages_bound sz _ Hszok Hin) as Hlt.
          rewrite Hfl in Hlt. rewrite Hal in Hlt. lia. }
      assert (Hcan' : forall a : Z,
                is_Some (umem_grow M (sz + n) !! a) -> (0 <= a < 2 ^ 38)%Z).
      { intros a Ha. unfold umem_grow in Ha.
        destruct (M !! a) as [b |] eqn:E.
        - exact (Hcanon a (mk_is_Some _ _ E)).
        - rewrite (lookup_union_r M _ a E) in Ha.
          destruct Ha as [b Hb].
          apply lookup_gset_to_gmap_Some in Hb as [Hin _].
          unfold live_set in Hin. apply elem_of_list_to_set in Hin.
          apply elem_of_seqZ in Hin.
          unfold pgroundup in Hin.
          assert (Hup : (sz + n + 4095) / 4096 * 4096 <= sz + n + 4095)
            by (pose proof (Z.mul_div_le (sz + n + 4095) 4096 ltac:(lia)); lia).
          change (2 ^ 38)%Z with 274877906944%Z in Hhi |- *. lia. }
      assert (Hstop' : forall (p : mword 27) (q : uperm),
                pm' !! p = Some q ->
                bv_unsigned p * 4096 < pgroundup (sz + n)).
      { intros p q Hq. rewrite Hperm in Hq.
        apply lookup_union_Some_raw in Hq as [Hq | [_ Hq]].
        - (* an OLD page: below the old break's page, hence below the new *)
          pose proof (Hstoppg p q Hq) as Hlt.
          pose proof (pgroundup_mono sz (sz + n) ltac:(lia)). lia.
        - (* a page the fill added: live at the new size *)
          apply lookup_gset_to_gmap_Some in Hq as [Hin _].
          apply elem_of_difference in Hin as [Hin _].
          exact (live_pages_bound (sz + n) p Hszok' Hin). }
      (* ---- the heap grows, and the caller gets the run ---- *)
      rewrite Himg.
      rewrite (uslot_bump_run m pc M (umem_grow M (sz + n)) pm pm'
                 sz (sz + n) fdv fdv cw cw' gn gn cs cs pidv false false secc_all secc_all r Hx0 Hal4).
      rewrite /ukc. iIntros (h' xi' C' pt' Rfd' Rut') "%Hlo' %Hpm' %Hlzf' Hb'".
      iMod (uheap_grow_run (ukn_t N) (ukn_d N) (ukn_s N) M pm pm' sz n Hsz0 Hn0 Hfresh Hext
              Hcan' Hstop' with "Hheap Hsz") as "(Hheap & Hsz & Hrun')".
      iDestruct (urun_close_upd N (umem_grow M (sz + n)) pm' m
                   (mword_of_int 10) r (sz + n) fdv cw' gn cs pidv (add_vec_int pc 4) avail
                   ltac:(unfold unot_sp; vm_compute; discriminate)
                   with "Hheap Hstk Hufd Hcwda Hcha Hmy Hdep Hnpx [Hcont Hsz Hrun']") as "Hkc".
      { iIntros (h'') "Hrun".
        iApply ("Hcont" $! h'' r with "[Hsz Hrun'] Hrun").
        iRight. iSplitR; [ iPureIntro; exact Hr | ]. iFrame "Hsz Hrun'". }
      iDestruct (ukcq_ukc with "Hkc") as "Hkc".
      iApply ("Hkc" $! h' xi' C' pt' Rfd' Rut' with "[%] [%] [%] Hb'");
        [ exact Hlo' | exact Hpm' | exact Hlzf' ].
  Qed.

  (* EXIT PAYS.  The one leaf whose premise is a RESOURCE the program owes
     rather than a fact: the trap loop's exit row is a DEPOSIT
     ([UexecRet.uexec_pay_dep]), so a program may not ecall exit until it
     has produced what its parent is owed -- its own [ukn_pay] at the
     status it is passing in a0.  A program whose payload is trivial
     ([fun _ => True], every generic one and every one this lane's callers
     run) pays it for free.
     THERE IS STILL NO CONTINUATION: exit does not return. *)
  Lemma wp_uk_ecall_exit (N : uk_names Σ) (h : CpuId) (m : regfile)
      (pc : mword 64) (avail : nat) :
    usysno m = USYS_exit ->
    uinstr_is (ukn_t N) pc false (ECALL tt) -∗
    (* THE PAYMENT, AND THERE IS ONLY ONE NOW (lane SELF-KILL, P6).  What
       the program owes at its own exit is the payload at the status it is
       exiting with, outright.  The second conjunct -- the payload at -1,
       for the tear-down usertrap's kill check may perform BEFORE
       [syscall()] -- is gone with the deposit that used to carry it: a
       KILL is the KILLER's price, paid into <p->lock>'s own killed row
       ([SchedCtx.kill_row]).  At [UkRun.ukn_triv] this is [True]. *)
    ukn_pay N (uexitst m) -∗
    (* ...AND THE EXIT ROW COSTS THE CALLER NOTHING (design/pipe.md, "The
       exit path").  exit(2) is no longer a free number -- kexit closes
       every descriptor, and a pipe row's last close steps the byte queue
       -- so the deposit carries [SpecFileclose.fileclose_cpays] of the
       key's own table.  But the fact that decides it is a fact about the
       TABLE, which the run carries between traps ([UkRun.urun_nopipe]), so
       the leaf mints the row off its own run and there is no premise here
       at all. *)
    urun N h m pc avail -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Hn. iIntros "#Hi Hpay Hrun".
    iDestruct "Hrun" as (xi C pt Rfd Rut sz M pm fdv cw gn cs pidv) "(%Hlo & %Hpm & %Hlzf & %HRut & Hheap & Hstk & Hufd & Hcwda & Hcha & #Hmy & #Hdep & #Hnpx & Hb)".
    iMod (udep_exit_run N m pc M pm sz fdv cw gn cs pidv
                with "Hdep Hnpx") as "Hdepn".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iApply (UkStep.wp_uk_ecall C pt Rfd Rut pm sz Hlo Hpm HRut Hlzf M m pc fdv cw gn cs pidv Hui
              (fun (s : mstate)
                   (Hp : register_lookup cur_privilege s.(sregs) = User)
                   (Hc : register_lookup (R_bitvector_64 PC) s.(sregs) = pc) =>
                 UserExecFacts.goodmb_execute_ECALL_U UserFrame.Du_r UserFrame.Du_w
                   s pc ltac:(vm_compute; reflexivity)
                   ltac:(vm_compute; reflexivity) Hp Hc)
              with "Hb Hmy").
    rewrite (uexec_ret_ecall _ _ eq_refl).
    assert (Hnum : uvis_num (uvis_of_run m pc M pm sz fdv cw gn cs pidv false secc_all) = USYS_exit).
    { assert (Hraw : usys_num (uvis_tf (uvis_of_run m pc M pm sz fdv cw gn cs pidv false secc_all)) = USYS_exit)
        by (cbn [uvis_tf uvis_of_run]; rewrite tf_of_num; exact Hn).
      rewrite uvis_num_full0; [ exact Hraw | reflexivity | rewrite Hraw; usys_range ]. }
    (* the PAYMENT's guard IS the deposit's own, so it is opened BEFORE the
       number is rewritten and the destructs below then reduce both copies
       at once *)
    rewrite /uexec_pay_dep /upay_at.
    pose proof Hnum as Hnume. unfold uvis_num in Hnume. rewrite ?Hnum ?Hnume. cbv zeta.
    destruct (decide (uecall_scause = uecall_scause)) as [_ | Hpne];
      [ | exfalso; exact (Hpne eq_refl) ].
    destruct (decide (USYS_exit = USYS_fork)) as [He | _];
      [ exfalso; vm_compute in He; discriminate | ].
    (* THE DEPOSIT: the run's own [my_pay], the payload at the status this
       exit stores, AND THE EXIT NUMBER'S BUNDLE ROW -- the table's close
       payments, which kexit spends (design/pipe.md, "The exit path").
       Exit has no arm, so nothing comes back.  The family is the one the
       mint chose, exactly as at every other depositing leaf. *)
    iDestruct "Hdepn" as (fdep) "[%Hfp Hdepn]".
    iExists fdep. rewrite Hfp.
    cbn [uvis_gen uvis_tf uvis_of_run].
    iSplitL "Hpay".
    { iFrame "Hmy". rewrite (uexitst_exit_xs m pc). iExact "Hpay". }
    iExact "Hdepn".
  Qed.

End UkRunSys.
