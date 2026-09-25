(* ===================================================================== *)
(*  UkShPipePaid.v -- runcmd's PIPE ARM, PAID (lane PIPE-ARM-PAID;        *)
(*  design claude-notes/design/app-pipe.md SS4.3c).                       *)
(*                                                                       *)
(*  [UkShPipe.wp_kshr_pipe_arm] prints its three [panic] tails through    *)
(*  [UkShDiag.ush_diag_leaf_holds], the FREE diagnostic leaf, whose       *)
(*  console bytes are paid out of [UkSh.sh_deps] -- write's deposit,      *)
(*  which a verified shell holds only under the taint                     *)
(*  ([UkShRedir.v]'s header, and [UkShRedirChild.v]'s: it does not use    *)
(*  [UkSh.sh_deps] anywhere on the walk, which is what makes that one a   *)
(*  paid child walk).  A ROUND whose console block the wire accounts      *)
(*  for cannot hold that law, so it cannot apply the arm at all --        *)
(*  SH-PIPE-ROUND-2's second refutation.                                  *)
(*                                                                       *)
(*  This file is the paid twin.  Nothing here re-walks the arm: lane      *)
(*  PIPE-ARM-PAID re-cut [UkShPipe] so that the landed arm is             *)
(*  [wp_kshr_pipe_arm_g] -- the same walk with its three tails as         *)
(*  CONTINUATIONS and the credential they are paid from as a parameter -- *)
(*  at the free tails, its statement byte-identical.  What is here is     *)
(*  that generic arm at the PAID tails:                                   *)
(*                                                                       *)
(*    S1  [wp_kshd_panic_paid_at]: [UkShDiag.wp_kshd_panic_paid] with     *)
(*        its MESSAGE as a parameter.  The landed one is hard-wired to    *)
(*        the "fork" literal at 0x12a8 and to [EchoDisc.alt_panic]; the   *)
(*        pipe arm also panics with "pipe" at 0x12d8, whose five bytes    *)
(*        are [wl_line PipeDisc.dg_pipe].  The walk underneath            *)
(*        ([UkShDiag.wp_kshd_panic_chain]) was general in the message     *)
(*        all along, so this costs one lemma and no new walk.             *)
(*    S2  the two messages' byte facts -- the [pipe] literal's four and   *)
(*        the newline [panic]'s own format contributes.                   *)
(*    S3  [wp_kshr_pipe_arm_paid].                                        *)
(*                                                                       *)
(*  WHAT THE ARM IS PAID WITH, and why it is shaped this way (design      *)
(*  SS4.3c): the runcmd child is entered at ONE credential [Cr] and the    *)
(*  console admits ONE writer, so [Cr] is spent EITHER on the             *)
(*  [pipe(2)]-failed tail (where nothing has been split) OR by the split  *)
(*  at the two forks, and the ARM makes that choice -- no caller has to   *)
(*  split it up front.  [Cx γp] is the fourth component of that split:    *)
(*  what the two [fork1]s BORROW as their exit payload and what either    *)
(*  [panic("fork")] tail is paid from; it reaches the parent unspent.     *)
(*  [RcL]/[RcR] carry the lease's two cursor halves and the two children's *)
(*  entry payments, [Rk] what sh keeps for the end of the round -- all    *)
(*  three PARAMETERS here, because the family they are built from is      *)
(*  PIPE-2W's.                                                            *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_map ghost_var invariants.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvModelBytes.
Require Import RegFile.
Require Import UmodeArith.
Require Import ProcGeom.
Require Import UserHeap UkRun.
Require Import UCodeShK.
Require Import UkSh.
Require Import UkShRun.
Require Import UkShDiag.
Require Import UkShPipe.
Require Import CtxIdDefs.
Require User.ShSyms User.ShInstrs.
Require Import FdSlots UserFd.
Require Import PipeNames.
Require Import UserCwd.
Require Import UserChildren.
Require Import UexecSG.
Require Import ChildTok.
Require Import LineWords.
Require Import EchoDisc.
Require Import PipeDisc.
Local Open Scope Z_scope.
Import Defs.

(* A PID IN [1, PIDMAX] DOES NOT SIGN-EXTEND TO -1 ([UkShFork.
   ushf_pid_sext_ne_m1] restated; that file is not in this one's cone).
   Design SS4.3u spends it: the SECOND [fork1]'s panic tail is entered
   with [r = -1] as a PURE premise, so the fork answer's pid arm is
   refutable and what is left is its [-1] arm -- which carries the RIGHT
   child's lend. *)
Lemma ushq_pid_sext_ne_m1 (pidv : mword 32) :
  1 <= bv_unsigned pidv <= PIDMAX ->
  (sign_extend' 64 pidv : mword 64) <> (mword_of_int (-1) : mword 64).
Proof using.
  intros Hrng Heq.
  assert (Hlt : bv_unsigned pidv < Z31) by (unfold PIDMAX, Z31 in *; lia).
  rewrite (sext32_small pidv Hlt) in Heq.
  pose proof (f_equal uint Heq) as Hu.
  rewrite (uint_moi (bv_unsigned pidv)
             ltac:(unfold PIDMAX, Z64 in *; lia)) in Hu.
  assert (Hm1 : uint (mword_of_int (-1) : mword 64) = 18446744073709551615)
    by (vm_compute; reflexivity).
  rewrite Hm1 in Hu. unfold PIDMAX in Hrng. lia.
Qed.

Section UkShPipePaid.
  (* [UkShPipe.v]'s binder list verbatim. *)
  Context `{!riscvGS Σ}.
  Context `{!ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  Context `{!ghost_varG Σ (gset gname)}.
  Context `{!ctokG Σ}.
  Context {SG : uexecSG Σ}.
  Context `{PS : uprogSG Σ}.
  Hypothesis Hpsok_free : forall k : Z, free_num k -> psok k.

  Local Notation a0_idx := (mword_of_int 10 : mword 5).

  (* NAME THE LEAF, DO NOT SEARCH (SH-PIPE-ROUND-2's operational finding,
     measured again here): [iIntros "#"] on an [ush_execfail_law_at] --
     one [□] behind a transparent definition -- does not return in this
     cone, although the carrier HAS a [Global Instance].  Answer it by
     name, at priority 0. *)
  #[local] Instance ushq_exf_pers0 (dg : list (bv 8)) (n : nat)
    (Cr Cd : iProp Σ) : Persistent (ush_execfail_law_at dg n Cr Cd) | 0
    := ush_execfail_law_at_persistent dg n Cr Cd.

  (* =================================================================== *)
  (*  S1  THE PAID PANIC WALK, AT AN ARBITRARY MESSAGE                    *)
  (*                                                                     *)
  (*  [UkShDiag.wp_kshd_panic_paid] at a parameterised literal.  [panic]  *)
  (*  is [fprintf(2, "%s\n", s); exit(1)], so what reaches the wire is    *)
  (*  the message's four bytes and then the newline the format's own      *)
  (*  literal at 0x12a0 contributes -- five in all, which is why the law  *)
  (*  below is spent at index 5 and why [dg] has that length.            *)
  (*                                                                     *)
  (*  THE LAW IS [UkShDiag.ush_execfail_law_at] AND NOT [ush_panic_law].  *)
  (*  The two have the same SHAPE (a family, a byte step, an end), and    *)
  (*  the landed [ush_panic_law] fixes both the bytes ([alt_panic]) and   *)
  (*  the credential the end leaves (the BANNER-owed one, because at the  *)
  (*  echo era the main loop's fork panic kills the shell and re-enters   *)
  (*  the prologue).  Neither is right here: a [runcmd] child's panic     *)
  (*  kills the CHILD, its parent's [wait] returns and IT prints the      *)
  (*  prompt, so what the tail leaves is a BLOCK credential and the       *)
  (*  already-general carrier is the one to take.                        *)
  (* =================================================================== *)
  Lemma wp_kshd_panic_paid_at (N : uk_names Σ) `{!ukn_const N}
      (msg : Z) (dg : list (bv 8)) (Cr Cd : iProp Σ)
      (l : list fdstate) (h : CpuId) (m : regfile) (n : nat) :
    UkSh.ush_fd2p l ->
    uint (m !!! Regidx a0_idx) = msg ->
    msg <> 0 ->
    shd_fmt_ok msg 4%nat = true ->
    length dg = 5%nat ->
    (forall p : nat, (p < 4)%nat -> shd_lit msg p = dg !!! p) ->
    shd_lit 0x12a0 2%nat = dg !!! 4%nat ->
    ush_execfail_law_at dg 5%nat Cr Cd -∗
    shk_code (ukn_t N) -∗
    shk_rodata (ukn_t N) -∗
    UserFd.ustd (ukn_fd N) l -∗
    Cr -∗
    (UserFd.ustd (ukn_fd N) l -∗ Cd -∗ ukn_pay N (-1)) -∗
    urun N h m (mword_of_int ShSyms.panic) (ush_Dg + n) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Hfd2 Hmsg Hnz Hok Hlen Hlo Hhi.
    iIntros "#Hlaw #Hcode #Hro Hstd Hc Hpay Hrun".
    iDestruct ("Hlaw" $! N l with "[%] Hc") as (Pf) "(HPf & #Hstep & #Hdone)";
      [ exact Hfd2 | ].
    replace (ush_Dg + n)%nat with (2 + (10 + (12 + (4 + n))))%nat
      by (unfold ush_Dg; lia).
    assert (Ha0 : m !!! Regidx a0_idx = (mword_of_int msg : mword 64))
      by (rewrite <- Hmsg; symmetry; apply moi_of_uint).
    iDestruct (shd_msg_str (ukn_t N) (ukn_d N) DfracDiscarded msg 4%nat
                 Hok ltac:(cbn [Z.of_nat]; lia) with "Hro") as "#Hs".
    set (C1 := (fun _ : nat => UserFd.ustd (ukn_fd N) l ∗ Pf 0%nat)%I).
    set (C2 := (fun p : nat => UserFd.ustd (ukn_fd N) l ∗ Pf p)%I).
    set (C3 := (fun p : nat => UserFd.ustd (ukn_fd N) l ∗ Pf (p + 2)%nat)%I).
    assert (E12 : C1 0%nat = C2 0%nat) by reflexivity.
    assert (E23 : C2 4%nat = C3 2%nat) by reflexivity.
    iApply (wp_kshd_panic_chain N true DfracDiscarded msg 4%nat
              (shd_lit msg) C1 C2 C3 h m n Hnz Ha0 E12 E23
              with "[] [] [] [Hstd HPf] Hcode Hro Hs [Hpay] Hrun").
    { iModIntro. iIntros (p) "%Hp". exfalso. lia. }
    { iModIntro. iIntros (p) "%Hp". rewrite /C2 (Hlo p Hp).
      iApply ("Hstep" $! p (dg !!! p) with "[%] [%]").
      { apply list_lookup_lookup_total_lt. rewrite Hlen. lia. }
      { lia. } }
    { iModIntro. iIntros (p) "%Hp". rewrite /C3.
      assert (Hp2 : p = 2%nat) by lia. subst p. cbn [Nat.add].
      rewrite Hhi.
      iApply ("Hstep" $! 4%nat (dg !!! 4%nat) with "[%] [%]").
      { apply list_lookup_lookup_total_lt. rewrite Hlen. lia. }
      { lia. } }
    { rewrite /C1. iFrame "Hstd HPf". }
    { rewrite /C3. iIntros "[Hstd HPf]". cbn [Nat.add].
      iApply ("Hpay" with "Hstd"). iApply ("Hdone" with "HPf"). }
  Qed.

  (* =================================================================== *)
  (*  S2  THE TWO MESSAGES' BYTES                                         *)
  (*                                                                     *)
  (*  "fork" at 0x12a8 is [EchoDisc.alt_panic] and [UkShDiag] already has *)
  (*  its three facts; "pipe" at 0x12d8 is [wl_line PipeDisc.dg_pipe] and *)
  (*  these are them, proved the same way.                               *)
  (* =================================================================== *)
  Lemma ushq_pipe_msg_len : length (wl_line PipeDisc.dg_pipe) = 5%nat.
  Proof using . vm_compute. reflexivity. Qed.

  Lemma ushq_pipe_msg_fmt : shd_fmt_ok 0x12d8 4%nat = true.
  Proof using . vm_compute. reflexivity. Qed.

  Lemma ushq_pipe_msg_byte (p : nat) :
    (p < 4)%nat -> shd_lit 0x12d8 p = wl_line PipeDisc.dg_pipe !!! p.
  Proof using .
    intro Hp.
    apply (ush_bytes_of_forallb (shd_lit 0x12d8)
             (fun q : nat => wl_line PipeDisc.dg_pipe !!! q) 0%nat 4%nat);
      [ vm_compute; reflexivity | lia ].
  Qed.

  Lemma ushq_pipe_msg_nl :
    shd_lit 0x12a0 2%nat = wl_line PipeDisc.dg_pipe !!! 4%nat.
  Proof using . apply bv_eq. vm_compute. reflexivity. Qed.

  Lemma ushq_fork_msg_fmt : shd_fmt_ok 0x12a8 4%nat = true.
  Proof using . vm_compute. reflexivity. Qed.

  (* =================================================================== *)
  (*  S3  THE PAID ARM                                                    *)
  (* =================================================================== *)
  Lemma wp_kshr_pipe_arm_paid (N : uk_names Σ) `{!ukn_const N}
      (cl cr : ushcmd) (h : CpuId) (m : regfile) (t szv cwdv : Z)
      (ld : list fdstate) (st0 st1 : fdstate) (Sc : gset gname) (av : nat)
      (R RcL RcR Rk Cx Bx : pipe_names -> iProp Σ) (Qc : Z -> iProp Σ)
      (Cr Bp : iProp Σ)
      (* the two [wait(0)]s' law, relayed (design app-pipe SS4.3w,
         purchase 3) -- see [UkShPipe.wp_kshr_pipe_arm_g] *)
      (Wr : iProp Σ)
      (Pw : mword 64 -> gset gname -> gset gname -> iProp Σ) :
    (forall x y : Z, Qc x = Qc y) ->
    m !!! Regidx a0_idx = (mword_of_int t : mword 64) ->
    (* the two standard streams the two children shut before their dup *)
    ld !! 0%nat = Some st0 -> ld !! 1%nat = Some st1 ->
    st0 <> FdClosed -> st1 <> FdClosed ->
    (forall (rb wb : bool) (gp : pipe_names),
       st0 <> FdOpen rb wb (FdPipe gp)) ->
    (forall (rb wb : bool) (gp : pipe_names),
       st1 <> FdOpen rb wb (FdPipe gp)) ->
    (* ...AND fd 2 IS THE CONSOLE, which the free arm never needed: the
       three diagnostics are written on it, and a PAID write names the
       row it goes out on. *)
    UkSh.ush_fd2p ld ->
    shk_code (ukn_t N) -∗
    shk_rodata (ukn_t N) -∗
    ush_jtab (ukn_t N) -∗
    ush_cmd (ukn_d N) t (UPipe cl cr) -∗
    usz (ukn_s N) szv -∗
    UserFd.ustd (ukn_fd N) ld -∗
    UserCwd.ucwd (ukn_cwd N) cwdv -∗
    UserChildren.uch (ukn_ch N) Sc -∗
    □ (app_taint -∗ Qc (-1)) -∗
    (* THE LEND, and the split of design SS4.3c: the lease's two cursor
       halves plus the two children's entry payments, what sh keeps, and
       what the two forks borrow. *)
    Cr -∗
    (∀ γp : pipe_names, Cr -∗ R γp -∗ RcL γp ∗ (RcR γp ∗ (Rk γp ∗ Cx γp))) -∗
    ush_pipe_call N ld R -∗
    (* the wait credential and the law that spends it, twice *)
    Wr -∗
    ush_wait0_law N Wr Pw -∗
    (* ---- THE THREE DIAGNOSTICS, PAID.  [panic("pipe")] writes
       [wl_line dg_pipe] and [panic("fork")] writes [alt_panic]; both are
       five bytes and both leave a residue the caller says what to do
       with. ---- *)
    ush_execfail_law_at (wl_line PipeDisc.dg_pipe) 5%nat Cr Bp -∗
    □ (UserFd.ustd (ukn_fd N) ld -∗ Bp -∗ ukn_pay N (-1)) -∗
    (* ...AT [RcR γp ∗ Cx γp] (design SS4.3u, lane SH-PIPE-ROUND-9).  The
       family's RIGHT chain is what a [panic("fork")] tail writes on
       ([PipeBoth.rsrc L 3 = alt_forkc], mode 3) and it is also cat's
       ([rsrc L 1 = L], mode 1) -- one resource, and the arm's single
       up-front split cannot give it to both [RcR γp] and [Cx γp].  It
       does not have to: the RIGHT child's lend is IN SH'S HAND at both
       tails and was being dropped.  At the second it arrives inside the
       fork answer's [-1] arm (the other disjunct is refuted by
       [ushq_pid_sext_ne_m1] against this continuation's own
       [r = -1]); at the first [UkShPipe.wp_kshr_pipe_arm_g] now borrows
       it through [wp_kshr_fork1]'s [Pex] slot.  At [Cx := emp] this is
       the law at exactly the family's right and mode halves, which is
       what [UShPipeAssembly.pipe_fork_panic_law] proves. *)
    □ (∀ γp : pipe_names,
         ush_execfail_law_at EchoDisc.alt_panic 5%nat
           (RcR γp ∗ Cx γp) (Bx γp)) -∗
    □ (∀ γp : pipe_names,
         UserFd.ustd (ukn_fd N) ld -∗ Bx γp -∗ ukn_pay N (-1)) -∗
    urun N h m (mword_of_int ShSyms.runcmd)
      (6 + (2 + (UkShDiag.ush_Dg + av))) -∗
    (* ---- THE LEFT CHILD, at runcmd's own entry ---- *)
    (∀ (N' : uk_names Σ) (h' : CpuId) (m' : regfile) (γ' : gname)
       (γp : pipe_names) (q : Z),
       ⌜ ukn_pay N' = Qc ⌝ -∗
       ⌜ m' !!! Regidx a0_idx = (mword_of_int q : mword 64) ⌝ -∗
       my_pay γ' Qc -∗
       shk_code (ukn_t N') -∗
       ush_jtab (ukn_t N') -∗
       ush_cmd (ukn_d N') q cl -∗
       usz (ukn_s N') szv -∗
       UserFd.ustd (ukn_fd N')
         (<[1%nat := FdOpen false true (FdPipe γp)]> ld) -∗
       UserCwd.ucwd (ukn_cwd N') cwdv -∗
       UserChildren.uch (ukn_ch N') (∅ : gset gname) -∗
       ush_cldep (FdOpen true false (FdPipe γp)) -∗
       ush_cldep (FdOpen false true (FdPipe γp)) -∗
       RcL γp -∗
       urun N' h' m' (mword_of_int ShSyms.runcmd)
         (2 + (UkShDiag.ush_Dg + av)) -∗
       mWP (Loop : expr riscv_lang)) -∗
    (* ---- THE RIGHT CHILD ---- *)
    (∀ (N' : uk_names Σ) (h' : CpuId) (m' : regfile) (γ' : gname)
       (γp : pipe_names) (q : Z),
       ⌜ ukn_pay N' = Qc ⌝ -∗
       ⌜ m' !!! Regidx a0_idx = (mword_of_int q : mword 64) ⌝ -∗
       my_pay γ' Qc -∗
       shk_code (ukn_t N') -∗
       ush_jtab (ukn_t N') -∗
       ush_cmd (ukn_d N') q cr -∗
       usz (ukn_s N') szv -∗
       UserFd.ustd (ukn_fd N')
         (<[0%nat := FdOpen true false (FdPipe γp)]> ld) -∗
       UserCwd.ucwd (ukn_cwd N') cwdv -∗
       UserChildren.uch (ukn_ch N') (∅ : gset gname) -∗
       ush_cldep (FdOpen true false (FdPipe γp)) -∗
       ush_cldep (FdOpen false true (FdPipe γp)) -∗
       RcR γp -∗
       urun N' h' m' (mword_of_int ShSyms.runcmd)
         (2 + (UkShDiag.ush_Dg + av)) -∗
       mWP (Loop : expr riscv_lang)) -∗
    (* ---- THE PARENT, at 0xea, with the forks' borrowed payload back ---- *)
    (∀ (h' : CpuId) (m' : regfile) (γp : pipe_names)
       (r1 r2 rw1 rw2 : mword 64) (S1 S2 S3 S4 : gset gname),
       (* the two forks returned a pid (purchase 3): a -1 panics and never
          reaches 0xea -- see [UkShPipe.wp_kshr_pipe_arm_g] *)
       ⌜ r1 <> (mword_of_int (-1) : mword 64) ⌝ -∗
       ⌜ r2 <> (mword_of_int (-1) : mword 64) ⌝ -∗
       ush_fork_ans Sc S1 (RcL γp) Qc r1 -∗
       ush_fork_ans S1 S2 (RcR γp) Qc r2 -∗
       Pw rw1 S2 S3 -∗
       Pw rw2 S3 S4 -∗
       UserChildren.uch (ukn_ch N) S4 -∗
       ush_jtab (ukn_t N) -∗
       usz (ukn_s N) szv -∗
       UserFd.ustd (ukn_fd N) ld -∗
       UserCwd.ucwd (ukn_cwd N) cwdv -∗
       Rk γp -∗
       Cx γp -∗
       Wr -∗
       urun N h' m' (mword_of_int 0xea) (2 + (UkShDiag.ush_Dg + av)) -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using Hpsok_free.
    intros HQc Ha0 Hl0 Hl1 Hne0 Hne1 Hnp0 Hnp1 Hfd2.
    iIntros "#Hcode #Hro #Hjt #Htree Hsz Hstd Hcwd Hch #Hkw Hcr Hsplit Hpipe
             HWr #Hwl #Hlawp #Hbp #Hlawf #Hbx Hrun HcL HcR Hpar".
    iApply (wp_kshr_pipe_arm_g Hpsok_free N cl cr h m t szv cwdv ld st0 st1
              Sc av R RcL RcR Rk Cx Qc Cr Wr Pw
              HQc Ha0 Hl0 Hl1 Hne0 Hne1 Hnp0 Hnp1
              with "Hcode Hjt Htree Hsz Hstd Hcwd Hch Hkw Hcr Hsplit Hpipe
                    HWr Hwl [] [] [] Hrun HcL HcR Hpar").
    - (* ---- panic("pipe"): the lend pays its five bytes ---- *)
      iIntros "!>" (h' m') "%Ha0' Hstd' Hcr' Hrun'".
      iApply (wp_kshd_panic_paid_at N 0x12d8 (wl_line PipeDisc.dg_pipe)
                Cr Bp ld h' m' (2 + av)%nat
                Hfd2 Ha0' ltac:(lia) ushq_pipe_msg_fmt ushq_pipe_msg_len
                ushq_pipe_msg_byte ushq_pipe_msg_nl
                with "Hlawp Hcode Hro Hstd' Hcr' [] Hrun'").
      iIntros "Hstd'' Hb". iApply ("Hbp" with "Hstd'' Hb").
    - (* ---- the first fork1's panic("fork"): SS4.3u's borrowed pair ---- *)
      iIntros "!>" (h' m' r γp) "%Ha0' %Hr' _ Hstd' HRcR Hcx Hrun'".
      iApply (wp_kshd_panic_paid_at N 0x12a8 EchoDisc.alt_panic
                (RcR γp ∗ Cx γp)%I (Bx γp) ld h' m' av
                Hfd2 Ha0' ltac:(lia) ushq_fork_msg_fmt ush_fork_msg_len
                ush_fork_msg_byte ush_fork_msg_nl
                with "[] Hcode Hro Hstd' [HRcR Hcx] [] Hrun'").
      + iApply ("Hlawf" $! γp).
      + iFrame "HRcR Hcx".
      + iIntros "Hstd'' Hb". iApply ("Hbx" $! γp with "Hstd'' Hb").
    - (* ---- the second fork1's panic("fork"): the lend is in the
            answer's [-1] arm, and [r = -1] refutes the other ---- *)
      iIntros "!>" (h' m' r γp S1) "%Ha0' %Hr' Hans Hstd' Hcx Hrun'".
      iAssert (RcR γp) with "[Hans]" as "HRcR".
      { iDestruct "Hans" as "[(_ & _ & HR) | Hpid]"; [ iExact "HR" | ].
        (* one slot more since design app-pipe SS4.3y: the tail's answer
           carries the generation's freshness, which this refutation does
           not read. *)
        iDestruct "Hpid" as (γ pidv) "(%Hr2 & %Hrng & _ & _ & _)".
        iExFalso. iPureIntro.
        apply (ushq_pid_sext_ne_m1 pidv Hrng). rewrite -Hr2. exact Hr'. }
      iApply (wp_kshd_panic_paid_at N 0x12a8 EchoDisc.alt_panic
                (RcR γp ∗ Cx γp)%I (Bx γp) ld h' m' av
                Hfd2 Ha0' ltac:(lia) ushq_fork_msg_fmt ush_fork_msg_len
                ush_fork_msg_byte ush_fork_msg_nl
                with "[] Hcode Hro Hstd' [HRcR Hcx] [] Hrun'").
      + iApply ("Hlawf" $! γp).
      + iFrame "HRcR Hcx".
      + iIntros "Hstd'' Hb". iApply ("Hbx" $! γp with "Hstd'' Hb").
  Qed.

End UkShPipePaid.
