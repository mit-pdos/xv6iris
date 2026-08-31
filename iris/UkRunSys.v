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

Section UkRunSys.
  Context `{!riscvGS Σ}.
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
  (* ecall, at a QUIET syscall.  The heap crosses the trap intact: the     *)
  (* kernel is licensed to change nothing about the image, so [urun] comes *)
  (* back at the same [M] and every points-to the program (or its caller)  *)
  (* was holding is still good.  a0 is the kernel's return value, about    *)
  (* which nothing is claimed.                                             *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_uk_ecall_quiet (γt γd γs : gname) (h : CpuId) (m : regfile)
      (pc : mword 64) (n : Z) (avail : nat) :
    usysno m = n ->
    n <> USYS_exit -> n <> USYS_fork ->
    n <> USYS_exec -> n <> USYS_sbrk ->
    n <> USYS_wait -> n <> USYS_pipe -> n <> USYS_read -> n <> USYS_fstat ->
    is_aligned_vaddr (Virtaddr (add_vec_int pc 4)) 2 = true ->
    uinstr_is γt pc false (ECALL tt) -∗
    urun γt γd γs h m pc avail -∗
    (∀ (h' : CpuId) (r : mword 64),
       urun γt γd γs h' (<[Regidx (mword_of_int 10) := r]> m) (add_vec_int pc 4) avail -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hn Hexit Hfork Hexec Hsbrk H3 H4 H5 H8 Hal4.
    iIntros "#Hi Hrun Hcont".
    iDestruct "Hrun" as (xi C pt Rfd Rut sz M pm fdv) "(%Hlo & %Hpm & Hheap & Hstk & Hb)".
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
    iIntros (r M' pm' sz' fdv') "%Hok".
    destruct (usys_mem_ok_quiet n _ r _ _ _ _ _ _ Hexec Hsbrk H3 H4 H5 H8 Hok)
      as [-> [-> ->]].
    cbn [uvis_M uvis_perm uvis_of_run].
    rewrite (uslot_bump_run m pc M M pm pm sz sz fdv fdv' r Hx0 Hal4).
    iApply (urun_close_upd _ _ _ _ _ m (mword_of_int 10) _ _ _ _ _
              ltac:(unfold unot_sp; vm_compute; discriminate) with "Hheap Hstk").
    iIntros (h') "Hrun".
    iApply ("Hcont" $! h' r with "Hrun").
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
  Lemma wp_uk_ecall_read (γt γd γs : gname) (h : CpuId) (m : regfile)
      (pc : mword 64) (a : Z) (cnt : nat) (f : nat -> bv 8) (avail : nat) :
    usysno m = USYS_read ->
    m !!! Regidx (mword_of_int 11) = (mword_of_int a : mword 64) ->
    bv_signed (subrange_vec_dec (m !!! Regidx (mword_of_int 12)) 31 0
               : mword 32) = Z.of_nat cnt ->
    is_aligned_vaddr (Virtaddr (add_vec_int pc 4)) 2 = true ->
    uinstr_is γt pc false (ECALL tt) -∗
    ubytes γd a cnt f -∗
    urun γt γd γs h m pc avail -∗
    (∀ (h' : CpuId) (r : mword 64) (g : nat -> bv 8),
       ubytes γd a cnt g -∗
       urun γt γd γs h' (<[Regidx (mword_of_int 10) := r]> m)
         (add_vec_int pc 4) avail -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hn Ha1 Hcnt Hal4.
    iIntros "#Hi Hbs Hrun Hcont".
    iDestruct "Hrun" as (xi C pt Rfd Rut sz M pm fdv) "(%Hlo & %Hpm & Hheap & Hstk & Hb)".
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
    iIntros (r M' pm' sz' fdv') "%Hok".
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
    rewrite (uslot_bump_run m pc M
               (umem_write M a cnt
                  (fun k => if decide (k < d)%nat then bs k else f k))
               pm pm sz sz fdv fdv' r Hx0 Hal4).
    iApply (urun_close_upd _ _ _ _ _ m (mword_of_int 10) _ _ _ _ _
              ltac:(unfold unot_sp; vm_compute; discriminate) with "Hheap Hstk").
    iIntros (h') "Hrun".
    iApply ("Hcont" $! h' r _ with "Hbs Hrun").
  Qed.

  (* ------------------------------------------------------------------- *)
  (* EXEC'S FAILURE ARM.  A successful exec never returns to this WP at all *)
  (* -- the new program's is minted by exec from the new trapframe and     *)
  (* image -- so the only arm that comes back is the failure, and the row  *)
  (* says so outright: -1, and not one byte moved.                         *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_uk_ecall_exec (γt γd γs : gname) (h : CpuId) (m : regfile)
      (pc : mword 64) (avail : nat) :
    usysno m = USYS_exec ->
    is_aligned_vaddr (Virtaddr (add_vec_int pc 4)) 2 = true ->
    uinstr_is γt pc false (ECALL tt) -∗
    urun γt γd γs h m pc avail -∗
    (∀ h' : CpuId,
       urun γt γd γs h'
         (<[Regidx (mword_of_int 10) := (mword_of_int (-1) : mword 64)]> m)
         (add_vec_int pc 4) avail -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hn Hal4.
    iIntros "#Hi Hrun Hcont".
    iDestruct "Hrun" as (xi C pt Rfd Rut sz M pm fdv) "(%Hlo & %Hpm & Hheap & Hstk & Hb)".
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
    iIntros (r M' pm' sz' fdv') "%Hok".
    destruct (usys_mem_ok_exec_row USYS_exec _ r _ _ _ _ _ _ eq_refl Hok)
      as [-> [-> [-> ->]]].
    cbn [uvis_M uvis_perm uvis_of_run].
    rewrite (uslot_bump_run m pc M M pm pm sz sz fdv fdv'
               (mword_of_int (-1) : mword 64) Hx0 Hal4).
    iApply (urun_close_upd _ _ _ _ _ m (mword_of_int 10) _ _ _ _ _
              ltac:(unfold unot_sp; vm_compute; discriminate) with "Hheap Hstk").
    iIntros (h') "Hrun".
    iApply ("Hcont" $! h' with "Hrun").
  Qed.

  (* ------------------------------------------------------------------- *)
  (* WAIT AT A NULL STATUS POINTER.  The kernel's own [addr != 0] test     *)
  (* means nothing is copied out, so the heap the caller owns comes back   *)
  (* untouched and the leaf can hand the SAME run on -- exactly the quiet  *)
  (* row's shape.  This is the arm init and sh both take.                  *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_uk_ecall_wait_null (γt γd γs : gname) (h : CpuId) (m : regfile)
      (pc : mword 64) (avail : nat) :
    usysno m = USYS_wait ->
    uint (m !!! Regidx (mword_of_int 10)) = 0 ->
    is_aligned_vaddr (Virtaddr (add_vec_int pc 4)) 2 = true ->
    uinstr_is γt pc false (ECALL tt) -∗
    urun γt γd γs h m pc avail -∗
    (∀ (h' : CpuId) (r : mword 64),
       urun γt γd γs h' (<[Regidx (mword_of_int 10) := r]> m)
         (add_vec_int pc 4) avail -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hn Hz Hal4.
    iIntros "#Hi Hrun Hcont".
    iDestruct "Hrun" as (xi C pt Rfd Rut sz M pm fdv) "(%Hlo & %Hpm & Hheap & Hstk & Hb)".
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
    iIntros (r M' pm' sz' fdv') "%Hok".
    destruct (usys_mem_ok_wait_null USYS_wait _ r _ _ _ _ _ _
                eq_refl Ha0 Hok) as [-> [-> ->]].
    cbn [uvis_M uvis_perm uvis_of_run].
    rewrite (uslot_bump_run m pc M M pm pm sz sz fdv fdv' r Hx0 Hal4).
    iApply (urun_close_upd _ _ _ _ _ m (mword_of_int 10) _ _ _ _ _
              ltac:(unfold unot_sp; vm_compute; discriminate) with "Hheap Hstk").
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
  Lemma wp_uk_ecall_window (γt γd γs : gname) (h : CpuId) (m : regfile)
      (pc : mword 64) (n : Z) (dst : mword 64) (cap k : nat)
      (f : nat -> bv 8) (avail : nat) :
    usysno m = n ->
    usyswin m n = Some (dst, cap) ->
    (cap <= k)%nat ->
    is_aligned_vaddr (Virtaddr (add_vec_int pc 4)) 2 = true ->
    uinstr_is γt pc false (ECALL tt) -∗
    urun γt γd γs h m pc avail -∗
    ubytes γd (uint dst) k f -∗
    (∀ (h' : CpuId) (r : mword 64) (d : nat) (g : nat -> bv 8),
       ⌜ (d <= cap)%nat ⌝ -∗
       ⌜ forall j : nat, (d <= j < k)%nat -> g j = f j ⌝ -∗
       urun γt γd γs h' (<[Regidx (mword_of_int 10) := r]> m)
         (add_vec_int pc 4) avail -∗
       ubytes γd (uint dst) k g -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hn Hwin Hcapk Hal4.
    iIntros "#Hi Hrun Hbuf Hcont".
    iDestruct "Hrun" as (xi C pt Rfd Rut sz M pm fdv) "(%Hlo & %Hpm & Hheap & Hstk & Hb)".
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
    iIntros (r M' pm' sz' fdv') "%Hok".
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
    rewrite (uslot_bump_run m pc M (umem_write M (uint dst) d g) pm pm sz sz
               fdv fdv' r Hx0 Hal4).
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
    iDestruct (urun_close_upd γt γd γs (umem_write M (uint dst) d g) pm m
                 (mword_of_int 10) r sz fdv' (add_vec_int pc 4) avail
                 ltac:(unfold unot_sp; vm_compute; discriminate)
                 with "Hheap Hstk [Hcont Hbuf]") as "Hkc";
      [ iIntros (h'') "Hrun";
        iApply ("Hcont" $! h'' r d g with "[%] [%] Hrun Hbuf");
        [ exact Hdcap | intros j Hj; apply Hgf; lia ] | ].
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
  Lemma wp_uk_ecall_read_win (γt γd γs : gname) (h : CpuId) (m : regfile)
      (pc : mword 64) (cnt : Z) (k : nat) (f : nat -> bv 8) (avail : nat) :
    usysno m = USYS_read ->
    bv_signed (subrange_vec_dec (m !!! Regidx (mword_of_int 12)) 31 0 : mword 32)
      = cnt ->
    (Z.to_nat cnt <= k)%nat ->
    is_aligned_vaddr (Virtaddr (add_vec_int pc 4)) 2 = true ->
    uinstr_is γt pc false (ECALL tt) -∗
    urun γt γd γs h m pc avail -∗
    ubytes γd (uint (m !!! Regidx (mword_of_int 11))) k f -∗
    (∀ (h' : CpuId) (r : mword 64) (d : nat) (g : nat -> bv 8),
       ⌜ (d <= Z.to_nat cnt)%nat ⌝ -∗
       ⌜ forall j : nat, (d <= j < k)%nat -> g j = f j ⌝ -∗
       urun γt γd γs h' (<[Regidx (mword_of_int 10) := r]> m)
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
    iApply (wp_uk_ecall_window γt γd γs h m pc USYS_read
              (m !!! Regidx (mword_of_int 11)) (Z.to_nat cnt) k f avail
              Hn Hw Hk Hal4 with "Hi Hrun Hbuf").
    iIntros (h' r d g) "%Hd %Hgf Hrun Hbuf".
    iApply ("Hcont" $! h' r d g with "[%] [%] Hrun Hbuf");
      [ exact Hd | exact Hgf ].
  Qed.

  Lemma wp_uk_ecall_exit (γt γd γs : gname) (h : CpuId) (m : regfile)
      (pc : mword 64) (avail : nat) :
    usysno m = USYS_exit ->
    uinstr_is γt pc false (ECALL tt) -∗
    urun γt γd γs h m pc avail -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hn. iIntros "#Hi Hrun".
    iDestruct "Hrun" as (xi C pt Rfd Rut sz M pm fdv) "(%Hlo & %Hpm & Hheap & Hstk & Hb)".
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
