(* ===================================================================== *)
(* UkShCd.v -- sh's [cd] BUILTIN, the arm of main's body that does NOT    *)
(* fork.                                                                  *)
(*                                                                        *)
(*   if(buf[0] == 'c' && buf[1] == 'd' && buf[2] == ' ') {                *)
(*     buf[strlen(buf)-1] = 0;              // chop \n                    *)
(*     if(chdir(buf+3) < 0)                                               *)
(*       fprintf(2, "cannot cd %s\n", buf+3);                             *)
(*     continue;                                                          *)
(*   }                                                                    *)
(*                                                                        *)
(* THIS IS THE ARM THAT COMES BACK.  Every other diagnostic in sh ends in *)
(* [exit]; this one prints and RETURNS to the command loop, which         *)
(* rewrites the very buffer it just printed.  That is the whole reason    *)
(* [UkShDiag.shd_str] carries a dfrac: the string handed to [fprintf] is  *)
(* BORROWED out of the line buffer at [DfracOwn 1] and taken back.        *)
(*                                                                        *)
(* AND IT IS THE ARM THAT WRITES.  [buf[strlen(buf)-1] = 0] is a [sb      *)
(* zero,0(a5)] into the caller's own buffer, so the byte run that goes    *)
(* round the loop is not the one that came in: it is [ush_set f (k+L-1)   *)
(* 0].  The loop head quantifies over the contents, which is exactly why  *)
(* it can.                                                                *)
(*                                                                        *)
(* THE TWO CALLS IT MAKES ARE ALREADY PROVED SOMEWHERE ELSE:              *)
(* [strlen] is stage 4's ([UkShParse.wp_kshp_strlen], parametric in the   *)
(* dfrac, which is why the mutable buffer can be measured), and           *)
(* [fprintf] is the diagnostic subtree's.  What is new here is [chdir] --  *)
(* three instructions on the QUIET syscall row -- and the arithmetic that *)
(* turns "the first NUL at or after k" into the two strings the arm       *)
(* names.                                                                 *)
(*                                                                        *)
(* THE BUDGET IS WHY THIS IS NOT YET [UkSh.ush_rest].  The arm runs        *)
(* [fprintf], whose frame is 26 words, and [ush_rest] hands its walk       *)
(* [16 + n] for an [n] the LOOP picks -- so the two do not meet until      *)
(* [ush_loop_head]'s budget is re-cut as [16 + (26 + n)].  That re-cut is  *)
(* mechanical and belongs with the OTHER thing [ush_rest] still needs, the *)
(* fork arm at 0x92c; this lemma is stated at the budget it actually       *)
(* wants so that the re-cut has something to aim at.                       *)
(*                                                                        *)
(* WHAT chdir COSTS THE WALK: NOTHING ABOUT THE PATH.  The kernel READS   *)
(* the path out of user memory and the row is about what it WRITES, so    *)
(* the leaf wants no resource for it at all -- a path that is not         *)
(* terminated inside the process's memory is a -1 from [copyinstr], not   *)
(* an unsound step.  WHAT IT DOES COST is the process's own half of its   *)
(* working directory ([UserCwd.ucwd]): chdir is the one row that MOVES    *)
(* the cwd, [UkRun.urun] carries the other half, and an authority cannot  *)
(* move without the fragment.  The arm takes [UserCwd.ucwd_any] in and    *)
(* hands it back -- sh never reads which directory it is in.              *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_map ghost_var invariants.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExtras RiscvModelBytes.
Require Import RegFile.
Require Import UmodeAbi.
From Stdlib Require Import FunctionalExtensionality.
Require Import UserHeap UkRun UkRunLeaf UkRunSys.
Require Import UserFd.
Require Import UCodeShK.
Require Import UkSh.
Require Import UkShParse.
Require Import UkShDiag.
Require Import UkShLoop.
Require Import CtxIdDefs.
Require User.ShSyms User.ShInstrs.
Require Import ChildTok.  (* [genF] -- the capacity the slot's fork arms name *)
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* §1 THE FIRST NUL AT OR AFTER k, AS A NUMBER.                           *)
(*                                                                        *)
(* [strlen] is called on [buf + k] and the walk has to name what it       *)
(* returns before the call, so the length is a pure function of the byte  *)
(* run.  It is [UkSh]'s blank scan the other way round: count forward     *)
(* while the byte is not NUL, bounded by what is left of the buffer.      *)
(* ===================================================================== *)
Fixpoint ushc_len (n k : nat) (f : nat -> bv 8) : nat :=
  match n with
  | 0%nat => 0%nat
  | S n' => if bool_decide (f k = ubyte0) then 0%nat else S (ushc_len n' (S k) f)
  end.

Lemma ushc_len_le (n k : nat) (f : nat -> bv 8) : (ushc_len n k f <= n)%nat.
Proof.
  revert k; induction n as [| n IH ]; intros k; cbn [ushc_len]; [ lia | ].
  destruct (bool_decide (f k = ubyte0)); [ lia | ].
  pose proof (IH (S k)). lia.
Qed.

Lemma ushc_len_body (n k : nat) (f : nat -> bv 8) (j : nat) :
  (j < ushc_len n k f)%nat -> f (k + j)%nat <> ubyte0.
Proof.
  revert k j; induction n as [| n IH ]; intros k j Hj; cbn [ushc_len] in Hj.
  - lia.
  - destruct (bool_decide_reflect (f k = ubyte0)) as [Hz | Hnz]; [ lia | ].
    destruct j as [| j' ].
    + rewrite Nat.add_0_r. exact Hnz.
    + assert (E : (k + S j')%nat = (S k + j')%nat) by lia.
      rewrite E. apply (IH (S k) j'). lia.
Qed.

(* IF there is a NUL inside the window, the count stops at or before it
   and the byte it stops on IS one. *)
Lemma ushc_len_stop (n k : nat) (f : nat -> bv 8) (i : nat) :
  (i < n)%nat -> f (k + i)%nat = ubyte0 ->
  (ushc_len n k f <= i)%nat /\ f (k + ushc_len n k f)%nat = ubyte0.
Proof.
  revert k i; induction n as [| n IH ]; intros k i Hi Hz; [ lia | ].
  cbn [ushc_len].
  destruct (bool_decide_reflect (f k = ubyte0)) as [Hzk | Hnzk].
  - split; [ lia | ]. rewrite Nat.add_0_r. exact Hzk.
  - destruct i as [| i' ].
    + exfalso. rewrite Nat.add_0_r in Hz. exact (Hnzk Hz).
    + assert (E : (k + S i')%nat = (S k + i')%nat) by lia.
      rewrite E in Hz.
      destruct (IH (S k) i' ltac:(lia) Hz) as [Hle Hnul].
      split; [ lia | ].
      assert (E2 : (k + S (ushc_len n (S k) f))%nat
                   = (S k + ushc_len n (S k) f)%nat) by lia.
      rewrite E2. exact Hnul.
Qed.

Require Import UexecSG.   (* [uexecSG] / [uprogSG]: the ARM deposit class *)
Require Import UserCwd.  (* [ucwd] / [ucwd_any] -- the process's own view of its working directory *)

Require Import Xv6Cameras.   (* [uartGhostG] -- the console ring's cameras *)
Section UkShCd.
  Context `{!riscvGS Σ}.
  Context `{!ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  (* ...and the children set's ([Xv6Cameras.uchG]), which [UkRun.urun]
     carries beside the cwd's *)
  Context `{!ghost_varG Σ (gset gname)}.
  Context (N : uk_names Σ).
  (* THIS PROGRAM'S EXIT OWES ITS PARENT NOTHING at this lane, as a
     CLASS so that it reaches the exit ecall without an argument at every
     call site ([UkRun.ukn_const]). *)
  Context `{Hpay : !ukn_const N}.
  (* [Xv6Cameras.uartGhostG] and the POSITION's ghost name, which
     [UkSh.ush_pstate] carries as its fourth conjunct (app-echo.md,
     "SH-LINE RULING"): this walk never reads the number, but the resource
     travels through every lemma that carries the process state. *)
  Context `{!uartGhostG Σ}.
  Context (γp : gname).
  (* ...AND THE APPLICATION'S TAINT (lane IO-LEAF, M5(3)): the process
     state carries the cursor AT A LINE BOUNDARY, whose other arm is the
     taint.  This arm proves nothing about it and takes it opaquely. *)
  Context (T : iProp Σ).
  (* ...and the era's write credential the loop carries beside its cursor
     (lane IO-LEAF, M6a(3)), opaque here for the same reason *)
  Context (Wc : nat -> nat -> iProp Σ).
  (* ...the banner-owed credential and the lease's pieces beside it (step
     3), opaque here for the same reason *)
  Context (Wb : nat -> iProp Σ).
  Context (Pm : nat -> iProp Σ).
  (* the fields, under the names the engine has always used *)
  Local Notation γt := (ukn_t N).
  Local Notation γd := (ukn_d N).
  Local Notation γs := (ukn_s N).
  Local Notation γfd := (ukn_fd N).
  Local Notation γcwd := (ukn_cwd N).
  Local Notation γch := (ukn_ch N).
  (* [ChildTok.ctokG]: the slot's fork arms name the generation's pieces,
     and this file binds no whole-system bundle. *)
  Context `{!ctokG Σ}.
  Context {SG : uexecSG Σ}.
  Context `{PS : uprogSG Σ}.
  (* THE NUMBERS THIS PROGRAM ADMITS ([UexecSG.uprogSG]'s [psok]).  A SECTION
     hypothesis, so no lemma statement in this file names it and the ~570
     [urun] sites did not move; the program's kernel-side constructor
     discharges it.
     AT THE FREE NUMBERS AND NO MORE (lane SUPPLY-SPLIT).  It used to read
     "every number but exec", which at the generic instance is true and at
     a VERIFIED program's instance is not: a program whose supplier is the
     application's ([AppInv.app_sup] -- for the echo application, the
     TAINT) could only ever be entered tainted.  What a verified program
     admits is [UexecSG.free_num] -- every number whose bundle is [emp],
     plus chdir, whose branch is a closed fact -- and at
     [UexecExecInst.uprogSG_free] this hypothesis is the identity.  A call
     at a number OUTSIDE that set takes its own deposit as a premise
     ([UkRun.udepw_law]) and is named at its site. *)
  Hypothesis Hpsok_free : forall k : Z, free_num k -> psok k.

  Local Notation x0_idx := (mword_of_int 0 : mword 5).
  Local Notation ra_idx := (mword_of_int 1 : mword 5).
  Local Notation s0_idx := (mword_of_int 8 : mword 5).
  Local Notation s1_idx := (mword_of_int 9 : mword 5).
  Local Notation a0_idx := (mword_of_int 10 : mword 5).
  Local Notation a1_idx := (mword_of_int 11 : mword 5).
  Local Notation a2_idx := (mword_of_int 12 : mword 5).
  Local Notation a5_idx := (mword_of_int 15 : mword 5).
  Local Notation a7_idx := (mword_of_int 17 : mword 5).
  Local Notation s2_idx := (mword_of_int 18 : mword 5).
  Local Notation s3_idx := (mword_of_int 19 : mword 5).
  Local Notation s4_idx := (mword_of_int 20 : mword 5).
  Local Notation s5_idx := (mword_of_int 21 : mword 5).
  Local Notation s6_idx := (mword_of_int 22 : mword 5).

(*ALIASES-BEGIN*)
  (* ---- what the other files of the lane define, at this file's own
         ghost names ---- *)
  Local Notation ush_std := (UkSh.ush_std N T).
  Local Notation ush_pstate := (UkSh.ush_pstate N γp T Wc Wb Pm).
  Local Notation ush_loop_head := (UkSh.ush_loop_head N γp).
  Local Notation urun_x0 := (UkShParse.urun_x0 N).
  Local Notation wp_kshp_strlen := (UkShParse.wp_kshp_strlen N).
  Local Notation shd_str := (UkShDiag.shd_str γt γd).
  Local Notation shd_str_of_ustr := (UkShDiag.shd_str_of_ustr γt γd).
  Local Notation shd_str_to_ustr := (UkShDiag.shd_str_to_ustr γt γd).
  Local Notation ushl_dat := (UkShLoop.ushl_dat γd).
  Local Notation ushl_head := (UkShLoop.ushl_head N γp T Wc Wb Pm).
(*ALIASES-END*)

  (* ===================================================================== *)
  (* §2 CUTTING A RUN, AND A STRING, OUT OF THE LINE BUFFER.                *)
  (*                                                                        *)
  (* Everything the arm hands to a callee is a WINDOW on the one byte run   *)
  (* the loop owns, so each is an ACCESSOR: take the window, and take back  *)
  (* a wand that returns it.  The buffer never leaves the walk.             *)
  (* ===================================================================== *)
  Lemma ushc_bytes_sub (a : Z) (Nb : nat) (f : nat -> bv 8) (k L : nat) :
    (k + L <= Nb)%nat ->
    ubytes γd a Nb f -∗
      ubytes γd (a + Z.of_nat k) L (fun j => f (k + j)%nat) ∗
      (ubytes γd (a + Z.of_nat k) L (fun j => f (k + j)%nat) -∗
         ubytes γd a Nb f).
  Proof using .
    intros Hkl.
    remember (Nb - k - L)%nat as q eqn:Hq.
    assert (HN : Nb = (k + (L + q))%nat) by lia.
    clear Hq. subst Nb.
    iIntros "H". rewrite ubytes_app ubytes_app.
    iDestruct "H" as "(Hlo & Hmid & Hhi)".
    iSplitL "Hmid"; [ iExact "Hmid" | ].
    iIntros "Hmid". iFrame "Hlo Hmid Hhi".
  Qed.

  (* one byte, as its own run *)
  Lemma ushc_bytes1 (x : Z) (g : nat -> bv 8) :
    ubytes γd x 1 g ⊣⊢ ubyte γd x (g 0%nat).
  Proof using .
    rewrite /ubytes /ubytesq /= Z.add_0_r right_id. reflexivity.
  Qed.

  Lemma ushc_bytes_one (a : Z) (Nb : nat) (f : nat -> bv 8) (j : nat) :
    (j < Nb)%nat ->
    ubytes γd a Nb f -∗
      ubyte γd (a + Z.of_nat j) (f j) ∗
      (∀ b : bv 8, ubyte γd (a + Z.of_nat j) b -∗
         ubytes γd a Nb (ush_set f j b)).
  Proof using .
    intros Hj.
    remember (Nb - j - 1)%nat as q eqn:Hq.
    assert (HN : Nb = (j + (1 + q))%nat) by lia.
    clear Hq. subst Nb.
    iIntros "H". rewrite ubytes_app ubytes_app.
    iDestruct "H" as "(Hlo & Hmid & Hhi)".
    iSplitL "Hmid".
    { rewrite ushc_bytes1 Nat.add_0_r. iExact "Hmid". }
    iIntros (b) "Hmid".
    rewrite ubytes_app ubytes_app.
    iSplitL "Hlo".
    { iApply (big_sepL_mono with "Hlo"). intros i x Hx.
      apply lookup_seq in Hx as [-> Hlt]. rewrite Nat.add_0_l in Hlt |- *.
      rewrite /ush_set (proj2 (Nat.eqb_neq i j) ltac:(lia)).
      reflexivity. }
    iSplitL "Hmid".
    { rewrite ushc_bytes1 Nat.add_0_r.
      rewrite /ush_set Nat.eqb_refl. iExact "Hmid". }
    iApply (big_sepL_mono with "Hhi"). intros i x Hx.
    apply lookup_seq in Hx as [-> Hlt]. rewrite Nat.add_0_l in Hlt |- *.
    rewrite /ush_set (proj2 (Nat.eqb_neq (j + (1 + i)) j) ltac:(lia)).
    reflexivity.
  Qed.

  (* [ustr] IS a byte run with one more byte on the end.  The two
     directions are the same conversion read twice. *)
  Lemma ushc_ustr_of_bytes (a : Z) (L : nat) (g : nat -> bv 8) :
    (forall j : nat, (j < L)%nat -> g j <> ubyte0) ->
    Z.of_nat L < 2 ^ 31 ->
    g L = ubyte0 ->
    ubytes γd a (S L) g -∗ ustr γd (DfracOwn 1) a L g.
  Proof using .
    intros Hnn Hlen Hz.
    assert (E : S L = (L + 1)%nat) by lia. rewrite E.
    iIntros "H". rewrite ubytes_app.
    iDestruct "H" as "[Hlo Hhi]".
    rewrite /ustr. iSplitR; [ iPureIntro; exact Hnn | ].
    iSplitR; [ iPureIntro; exact Hlen | ].
    iFrame "Hlo".
    rewrite ushc_bytes1 Nat.add_0_r Hz. iExact "Hhi".
  Qed.

  Lemma ushc_bytes_of_ustr (a : Z) (L : nat) (g : nat -> bv 8) :
    g L = ubyte0 ->
    ustr γd (DfracOwn 1) a L g -∗ ubytes γd a (S L) g.
  Proof using .
    intros Hz.
    assert (E : S L = (L + 1)%nat) by lia. rewrite E.
    iIntros "(_ & _ & Hlo & Hhi)". rewrite ubytes_app. iFrame "Hlo".
    rewrite ushc_bytes1 Nat.add_0_r Hz. iExact "Hhi".
  Qed.

  (* ===================================================================== *)
  (* §3 [chdir] @0xcf6 -- li a7,9 ; ecall ; ret.                            *)
  (*                                                                        *)
  (* THE QUIET ROW, at a call that is anything but quiet in the kernel:     *)
  (* [sys_chdir] moves [p->cwd].  It is quiet HERE because the row is       *)
  (* about what the syscall writes into USER MEMORY, and chdir writes       *)
  (* none -- it only reads the path.  The working directory rides inside    *)
  (* [urun] existentially, so a row that moves it needs no premise of this  *)
  (* walk: what comes back is a run at whatever the cwd now is.             *)
  (* ===================================================================== *)
  (* THE WORKING DIRECTORY GOES IN AND COMES BACK, index-free.  chdir is
     the one row that moves it, and moving it takes the process's own half
     ([UkRunSys.wp_uk_ecall_chdir]) -- so sh cannot call chdir without
     holding one, exactly as it cannot call an allocating syscall without
     its descriptor ledger.  WHICH directory it lands in is not something
     the row says and not something sh reads, so what travels is
     [UserCwd.ucwd_any]: one resource, no binder. *)
  Lemma wp_kshc_chdir (h : CpuId) (m : regfile) (avail : nat) :
    shk_code γt -∗
    UserCwd.ucwd_any γcwd -∗
    urun N h m (mword_of_int ShSyms.chdir) avail -∗
    (∀ (h' : CpuId) (ret : mword 64),
       UserCwd.ucwd_any γcwd -∗
       urun N h'
         (<[Regidx a0_idx := ret]>
            (<[Regidx a7_idx := (mword_of_int 9 : mword 64)]> m))
         (ret_pc (m !!! Regidx ra_idx)) avail -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using Hpsok_free.
    iIntros "#Hcode Hcwd Hrun Hcont".
    assert (Hpin : ShSyms.chdir = 0xcf6)
      by (destruct shk_syms_pins as (_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&H&_);
          exact H).
    rewrite Hpin.
    (* ---- 0xcf6  c.li a7,9 ---- *)
    iApply (wp_uk_cli N h m (mword_of_int 0xcf6)
              (mword_of_int 9 : mword 6) a7_idx avail
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) with "[] Hrun").
    { iApply (uis_shk_cf6 with "Hcode"). }
    assert (Em : <[Regidx a7_idx
                   := regval_into_reg (sign_extend' 64
                        (mword_of_int 9 : mword 6) : mword 64)]> m
                 = <[Regidx a7_idx := (mword_of_int 9 : mword 64)]> m)
      by (f_equal; apply bv_eq; vm_compute; reflexivity).
    assert (E0 : add_vec_int (mword_of_int 0xcf6 : mword 64) 2
                 = mword_of_int 0xcf8)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E0 Em. iIntros (h1) "Hrun".
    set (m1 := <[Regidx a7_idx := (mword_of_int 9 : mword 64)]> m).
    (* ---- 0xcf8  ecall -- THE ROW THAT MOVES THE CWD ---- *)
    iApply (wp_uk_ecall_chdir_any N h1 m1 (mword_of_int 0xcf8) avail
              ltac:(rewrite /m1 /usysno
                      (upd_eq m (Regidx a7_idx) (mword_of_int 9 : mword 64));
                    vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "[] Hrun [] Hcwd").
    { iApply (uis_shk_cf8 with "Hcode"). }
    { iApply udepw_of_psok; [ apply Hpsok_free; free_lit | ];
      (discriminate || assumption || (vm_compute; discriminate)). }
    assert (E1 : add_vec_int (mword_of_int 0xcf8 : mword 64) 4
                 = mword_of_int 0xcfc)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E1. iIntros (h2 ret) "Hcwd Hrun".
    set (m2 := <[Regidx a0_idx := ret]> m1).
    assert (Hra : m2 !!! Regidx ra_idx = m !!! Regidx ra_idx).
    { unfold m2, m1.
      exact (eq_trans
               (upd_ne m1 (Regidx a0_idx) (Regidx ra_idx) ret
                  ltac:(vm_compute; discriminate))
               (upd_ne m (Regidx a7_idx) (Regidx ra_idx)
                  (mword_of_int 9 : mword 64)
                  ltac:(vm_compute; discriminate))). }
    (* ---- 0xcfc  c.jr ra ---- *)
    iApply (wp_uk_cjr N h2 m2 (mword_of_int 0xcfc) ra_idx
              (ret_pc (m !!! Regidx ra_idx)) avail
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hra; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_cfc with "Hcode"). }
    iIntros (h3) "Hrun".
    iApply ("Hcont" $! h3 ret with "Hcwd Hrun").
  Qed.

  (* [wp_kshc_cd] -- main's [cd] arm, 0x97a..0x9be -- IS GONE (lane
     IO-LEAF, step 4).  The disciplined shell's one line is [echo hello
     world], so the body's dispatch refutes the three byte tests before the
     arm ([UkShFork.wp_kshm_body] at the line fact), and the command
     loop's working directory is pinned at the root
     ([UkSh.ush_pstate], SH-LINE R3(2)) -- a [chdir] could not re-enter
     the head it came from.  The byte-string helpers above are what the
     fork's child arm still takes from this file. *)

End UkShCd.
