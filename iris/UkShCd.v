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
(* the quiet leaf wants no resource for it at all -- a path that is not   *)
(* terminated inside the process's memory is a -1 from [copyinstr], not   *)
(* an unsound step.  The cwd itself rides inside [urun] existentially,    *)
(* which is why chdir MOVING it needs no new row here.                    *)
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
Require Import WpMmodeLeafBase.
Require Import UserBits.
Require Import WpUmodeBranch.
Require Import UmodeArith UmodeAbi.
Require Import UserPerm UsysMemOk.
Require Import UkStep.
From Stdlib Require Import FunctionalExtensionality.
Require Import UserHeap UkRun UkRunLeaf UkRunMem UkRunSys UkRunBr.
Require Import FdSlots UserFd.
Require Import UCodeShK UCodeShP.
Require Import UkSh.
Require Import UkShParse.
Require Import UkShDiag.
Require Import UkShMalloc.
Require Import UkShLoop.
Require Import TsoCtx.
Require User.ShSyms User.ShInstrs.
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

Section UkShCd.
  Context `{!riscvGS Σ}.
  Context `{!ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  Context (γt γd γs γfd : gname).

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
  Local Notation ush_std := (UkSh.ush_std γfd).
  Local Notation ush_loop_head := (UkSh.ush_loop_head γt γd γs γfd).
  Local Notation urun_x0 := (UkShParse.urun_x0 γt γd γs γfd).
  Local Notation wp_kshp_strlen := (UkShParse.wp_kshp_strlen γt γd γs γfd).
  Local Notation shd_str := (UkShDiag.shd_str γt γd).
  Local Notation shd_str_of_ustr := (UkShDiag.shd_str_of_ustr γt γd).
  Local Notation shd_str_to_ustr := (UkShDiag.shd_str_to_ustr γt γd).
  Local Notation ushl_dat := (UkShLoop.ushl_dat γd).
  Local Notation ushl_head := (UkShLoop.ushl_head γt γd γs γfd).
(*ALIASES-END*)

  (* ===================================================================== *)
  (* §2 CUTTING A RUN, AND A STRING, OUT OF THE LINE BUFFER.                *)
  (*                                                                        *)
  (* Everything the arm hands to a callee is a WINDOW on the one byte run   *)
  (* the loop owns, so each is an ACCESSOR: take the window, and take back  *)
  (* a wand that returns it.  The buffer never leaves the walk.             *)
  (* ===================================================================== *)
  Lemma ushc_bytes_sub (a : Z) (N : nat) (f : nat -> bv 8) (k L : nat) :
    (k + L <= N)%nat ->
    ubytes γd a N f -∗
      ubytes γd (a + Z.of_nat k) L (fun j => f (k + j)%nat) ∗
      (ubytes γd (a + Z.of_nat k) L (fun j => f (k + j)%nat) -∗
         ubytes γd a N f).
  Proof.
    intros Hkl.
    remember (N - k - L)%nat as q eqn:Hq.
    assert (HN : N = (k + (L + q))%nat) by lia.
    clear Hq. subst N.
    iIntros "H". rewrite ubytes_app ubytes_app.
    iDestruct "H" as "(Hlo & Hmid & Hhi)".
    iSplitL "Hmid"; [ iExact "Hmid" | ].
    iIntros "Hmid". iFrame "Hlo Hmid Hhi".
  Qed.

  (* one byte, as its own run *)
  Lemma ushc_bytes1 (x : Z) (g : nat -> bv 8) :
    ubytes γd x 1 g ⊣⊢ ubyte γd x (g 0%nat).
  Proof.
    rewrite /ubytes /ubytesq /= Z.add_0_r right_id. reflexivity.
  Qed.

  Lemma ushc_bytes_one (a : Z) (N : nat) (f : nat -> bv 8) (j : nat) :
    (j < N)%nat ->
    ubytes γd a N f -∗
      ubyte γd (a + Z.of_nat j) (f j) ∗
      (∀ b : bv 8, ubyte γd (a + Z.of_nat j) b -∗
         ubytes γd a N (ush_set f j b)).
  Proof.
    intros Hj.
    remember (N - j - 1)%nat as q eqn:Hq.
    assert (HN : N = (j + (1 + q))%nat) by lia.
    clear Hq. subst N.
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
  Proof.
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
  Proof.
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
  Lemma wp_kshc_chdir (h : CpuId) (m : regfile) (avail : nat) :
    shk_code γt -∗
    urun γt γd γs γfd h m (mword_of_int ShSyms.chdir) avail -∗
    (∀ (h' : CpuId) (ret : mword 64),
       urun γt γd γs γfd h'
         (<[Regidx a0_idx := ret]>
            (<[Regidx a7_idx := (mword_of_int 9 : mword 64)]> m))
         (ret_pc (m !!! Regidx ra_idx)) avail -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros "#Hcode Hrun Hcont".
    assert (Hpin : ShSyms.chdir = 0xcf6)
      by (destruct shk_syms_pins as (_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&H&_);
          exact H).
    rewrite Hpin.
    (* ---- 0xcf6  c.li a7,9 ---- *)
    iApply (wp_uk_cli γt γd γs γfd h m (mword_of_int 0xcf6)
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
    (* ---- 0xcf8  ecall -- the QUIET row at SYS_chdir ---- *)
    iApply (wp_uk_ecall_quiet γt γd γs γfd h1 m1 (mword_of_int 0xcf8) 9 avail
              ltac:(rewrite /m1 /usysno
                      (upd_eq m (Regidx a7_idx) (mword_of_int 9 : mword 64));
                    vm_compute; reflexivity)
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_cf8 with "Hcode"). }
    assert (E1 : add_vec_int (mword_of_int 0xcf8 : mword 64) 4
                 = mword_of_int 0xcfc)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E1. iIntros (h2 ret) "Hrun".
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
    iApply (wp_uk_cjr γt γd γs γfd h2 m2 (mword_of_int 0xcfc) ra_idx
              (ret_pc (m !!! Regidx ra_idx)) avail
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hra; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_cfc with "Hcode"). }
    iIntros (h3) "Hrun".
    iApply ("Hcont" $! h3 ret with "Hrun").
  Qed.

  (* ===================================================================== *)
  (* §4 THE ARM, 0x97a..0x9be.                                              *)
  (*                                                                        *)
  (* THE THREE BYTE TESTS ARE THE SCOPE, not a branch: the premise says the *)
  (* line begins "cd ", so each [bne] falls through and the arm runs.  The  *)
  (* OTHER reading of the same three instructions -- any one of them taken, *)
  (* and control goes to the fork at 0x92c -- is main's other arm and       *)
  (* belongs to the file that walks it.                                     *)
  (*                                                                        *)
  (* [L] IS WHAT strlen RETURNS, and it is named before the call: the first *)
  (* NUL at or after [k].  It is at least 3 because the three bytes the     *)
  (* tests just read are 'c', 'd' and ' ', none of them NUL.                *)
  (* ===================================================================== *)
  Lemma wp_kshc_cd (h : CpuId) (m : regfile) (f : nat -> bv 8) (k i2 : nat)
      (l : list fdstate) (sz : Z) (n : nat) :
    UkSh.ush_regs m ->
    m !!! Regidx s1_idx = mword_of_int (sh_buf + Z.of_nat k) ->
    m !!! Regidx a5_idx = mword_of_int (bv_unsigned (f k)) ->
    (k <= i2 < sh_nbuf)%nat -> f i2 = ubyte0 ->
    (* the line IS a [cd] command *)
    bv_unsigned (f k) = 99 ->
    bv_unsigned (f (S k)) = 100 ->
    bv_unsigned (f (S (S k))) = 32 ->
    ushl_head l sz -∗
    shk_code γt -∗ shk_rodata γt -∗ shp_code γt -∗
    ush_std l -∗
    ushl_dat -∗ usz γs sz -∗
    ubytes γd sh_buf sh_nbuf f -∗
    urun γt γd γs γfd h m (mword_of_int 0x97a)
      (16 + (80 + n)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hregs Hs1 Ha5 Hk2 Hi2z Hck Hck1 Hck2.
    iIntros "Hhead #Hcode #Hro #Hpcode Hstd Hdat Hsz Hbuf Hrun".
    destruct Hregs as (Hs2 & Hs3 & Hs4 & Hs5 & Hs6).
    (* ---- the string the arm measures, as a number ---- *)
    set (L := ushc_len (sh_nbuf - k) k f).
    assert (Hnz : forall j : nat, (j < 3)%nat -> f (k + j)%nat <> ubyte0).
    { intros j Hj He.
      assert (Hzu : bv_unsigned (f (k + j)%nat) = 0)
        by (rewrite He; vm_compute; reflexivity).
      destruct j as [| [| [| j' ]]]; try lia.
      - rewrite Nat.add_0_r in Hzu. lia.
      - replace (k + 1)%nat with (S k) in Hzu by lia. lia.
      - replace (k + 2)%nat with (S (S k)) in Hzu by lia. lia. }
    destruct (ushc_len_stop (sh_nbuf - k) k f (i2 - k)%nat ltac:(lia)
                ltac:(replace (k + (i2 - k))%nat with i2 by lia; exact Hi2z))
      as [HLle HLnul].
    assert (HLbody : forall j : nat, (j < L)%nat -> f (k + j)%nat <> ubyte0)
      by (intros j Hj; exact (ushc_len_body (sh_nbuf - k) k f j Hj)).
    assert (HL3 : (3 <= L)%nat).
    { destruct (Nat.lt_ge_cases L 3) as [Hlt | Hge]; [ | exact Hge ].
      exfalso. exact (Hnz L Hlt HLnul). }
    assert (HLhi : (k + L < sh_nbuf)%nat) by lia.
    assert (HL31 : Z.of_nat L < 2 ^ 31) by (unfold sh_nbuf in HLhi; lia).
    assert (Hbuf0 : 0 <= sh_buf) by (unfold sh_buf; lia).
    assert (Hbufhi : sh_buf + Z.of_nat sh_nbuf < Z64)
      by (unfold sh_buf, sh_nbuf, Z64; lia).
    (* ---- 0x97a  bne a5,s5 -- NOT taken: buf[k] is 'c' ---- *)
    assert (Htk7a : false = uv_btaken BNE (m !!! Regidx a5_idx)
                              (m !!! Regidx s5_idx)).
    { cbn [uv_btaken]. rewrite Ha5 Hs5 Hck.
      rewrite (moi_neq_vec 99 99 ltac:(unfold Z64; lia)
                 ltac:(unfold Z64; lia)).
      symmetry. apply negb_false_iff. apply Z.eqb_eq. reflexivity. }
    iApply (wp_uk_btype γt γd γs γfd h m (mword_of_int 0x97a)
              (mword_of_int 8114 : mword 13) s5_idx a5_idx BNE false
              (mword_of_int 0x92c) (16 + (80 + n))
              Htk7a
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(discriminate)
              with "[] Hrun").
    { iApply (uis_shk_97a with "Hcode"). }
    assert (E97a : add_vec_int (mword_of_int 0x97a : mword 64) 4
                   = mword_of_int 0x97e)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E97a. iIntros (h1) "Hrun".
    (* ---- 0x97e  lbu a5,1(s1) ---- *)
    assert (Ead1 : sh_buf + Z.of_nat (S k) = sh_buf + Z.of_nat k + 1) by lia.
    iDestruct (ushc_bytes_one sh_buf sh_nbuf f (S k) ltac:(lia) with "Hbuf")
      as "[Hb1 Hcl1]".
    iEval (rewrite Ead1) in "Hb1".
    iApply (wp_uk_lbu γt γd γs γfd h1 m (mword_of_int 0x97e)
              (mword_of_int 1 : mword 12) s1_idx a5_idx (DfracOwn 1)
              (sh_buf + Z.of_nat k + 1) (f (S k))
              (16 + (80 + n))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(rewrite Hs1
                      (uint_moi (sh_buf + Z.of_nat k)
                         ltac:(unfold sh_buf, Z64 in *; lia));
                    vm_compute uoff_i12; lia)
              ltac:(vm_compute; discriminate)
              with "[] Hb1 Hrun").
    { iApply (uis_shk_97e with "Hcode"). }
    iIntros "Hb1". iIntros (h2) "Hrun".
    iEval (rewrite <- Ead1) in "Hb1".
    iDestruct ("Hcl1" $! (f (S k)) with "Hb1") as "Hbuf".
    assert (Eset1 : UkSh.ush_set f (S k) (f (S k)) = f).
    { apply functional_extensionality. intros q. rewrite /UkSh.ush_set.
      destruct (Nat.eqb_spec q (S k)) as [-> | _]; reflexivity. }
    rewrite Eset1.
    assert (E97e : add_vec_int (mword_of_int 0x97e : mword 64) 4
                   = mword_of_int 0x982)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E97e.
    set (m1 := <[Regidx a5_idx
                 := regval_into_reg
                      (zero_extend' 64 (f (S k) : mword 8) : mword 64)]> m).
    assert (Ha5_1 : m1 !!! Regidx a5_idx = mword_of_int 100).
    { rewrite /m1 (upd_eq m (Regidx a5_idx) _) zext8_moi Hck1. reflexivity. }
    assert (Hs1_1 : m1 !!! Regidx s1_idx = mword_of_int (sh_buf + Z.of_nat k))
      by (rewrite /m1 (upd_ne m (Regidx a5_idx) (Regidx s1_idx) _
                         ltac:(vm_compute; discriminate)); exact Hs1).
    assert (Hs3_1 : m1 !!! Regidx s3_idx = mword_of_int 100)
      by (rewrite /m1 (upd_ne m (Regidx a5_idx) (Regidx s3_idx) _
                         ltac:(vm_compute; discriminate)); exact Hs3).
    assert (Hs6_1 : m1 !!! Regidx s6_idx = mword_of_int 32)
      by (rewrite /m1 (upd_ne m (Regidx a5_idx) (Regidx s6_idx) _
                         ltac:(vm_compute; discriminate)); exact Hs6).
    (* ---- 0x982  bne a5,s3 -- NOT taken: buf[k+1] is 'd' ---- *)
    assert (Htk82 : false = uv_btaken BNE (m1 !!! Regidx a5_idx)
                              (m1 !!! Regidx s3_idx)).
    { cbn [uv_btaken]. rewrite Ha5_1 Hs3_1.
      rewrite (moi_neq_vec 100 100 ltac:(unfold Z64; lia)
                 ltac:(unfold Z64; lia)).
      symmetry. apply negb_false_iff. apply Z.eqb_eq. reflexivity. }
    iApply (wp_uk_btype γt γd γs γfd h2 m1 (mword_of_int 0x982)
              (mword_of_int 8106 : mword 13) s3_idx a5_idx BNE false
              (mword_of_int 0x92c) (16 + (80 + n))
              Htk82
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(discriminate)
              with "[] Hrun").
    { iApply (uis_shk_982 with "Hcode"). }
    assert (E982 : add_vec_int (mword_of_int 0x982 : mword 64) 4
                   = mword_of_int 0x986)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E982. iIntros (h3) "Hrun".
    (* ---- 0x986  lbu a5,2(s1) ---- *)
    assert (Ead2 : sh_buf + Z.of_nat (S (S k)) = sh_buf + Z.of_nat k + 2)
      by lia.
    iDestruct (ushc_bytes_one sh_buf sh_nbuf f (S (S k)) ltac:(lia)
                 with "Hbuf") as "[Hb2 Hcl2]".
    iEval (rewrite Ead2) in "Hb2".
    iApply (wp_uk_lbu γt γd γs γfd h3 m1 (mword_of_int 0x986)
              (mword_of_int 2 : mword 12) s1_idx a5_idx (DfracOwn 1)
              (sh_buf + Z.of_nat k + 2) (f (S (S k)))
              (16 + (80 + n))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(rewrite Hs1_1
                      (uint_moi (sh_buf + Z.of_nat k)
                         ltac:(unfold sh_buf, Z64 in *; lia));
                    vm_compute uoff_i12; lia)
              ltac:(vm_compute; discriminate)
              with "[] Hb2 Hrun").
    { iApply (uis_shk_986 with "Hcode"). }
    iIntros "Hb2". iIntros (h4) "Hrun".
    iEval (rewrite <- Ead2) in "Hb2".
    iDestruct ("Hcl2" $! (f (S (S k))) with "Hb2") as "Hbuf".
    assert (Eset2 : UkSh.ush_set f (S (S k)) (f (S (S k))) = f).
    { apply functional_extensionality. intros q. rewrite /UkSh.ush_set.
      destruct (Nat.eqb_spec q (S (S k))) as [-> | _]; reflexivity. }
    rewrite Eset2.
    assert (E986 : add_vec_int (mword_of_int 0x986 : mword 64) 4
                   = mword_of_int 0x98a)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E986.
    set (m2 := <[Regidx a5_idx
                 := regval_into_reg
                      (zero_extend' 64 (f (S (S k)) : mword 8)
                       : mword 64)]> m1).
    assert (Ha5_2 : m2 !!! Regidx a5_idx = mword_of_int 32).
    { rewrite /m2 (upd_eq m1 (Regidx a5_idx) _) zext8_moi Hck2. reflexivity. }
    assert (Hs1_2 : m2 !!! Regidx s1_idx = mword_of_int (sh_buf + Z.of_nat k))
      by (rewrite /m2 (upd_ne m1 (Regidx a5_idx) (Regidx s1_idx) _
                         ltac:(vm_compute; discriminate)); exact Hs1_1).
    assert (Hs6_2 : m2 !!! Regidx s6_idx = mword_of_int 32)
      by (rewrite /m2 (upd_ne m1 (Regidx a5_idx) (Regidx s6_idx) _
                         ltac:(vm_compute; discriminate)); exact Hs6_1).
    (* ---- 0x98a  bne a5,s6 -- NOT taken: buf[k+2] is a blank ---- *)
    assert (Htk8a : false = uv_btaken BNE (m2 !!! Regidx a5_idx)
                              (m2 !!! Regidx s6_idx)).
    { cbn [uv_btaken]. rewrite Ha5_2 Hs6_2.
      rewrite (moi_neq_vec 32 32 ltac:(unfold Z64; lia)
                 ltac:(unfold Z64; lia)).
      symmetry. apply negb_false_iff. apply Z.eqb_eq. reflexivity. }
    iApply (wp_uk_btype γt γd γs γfd h4 m2 (mword_of_int 0x98a)
              (mword_of_int 8098 : mword 13) s6_idx a5_idx BNE false
              (mword_of_int 0x92c) (16 + (80 + n))
              Htk8a
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(discriminate)
              with "[] Hrun").
    { iApply (uis_shk_98a with "Hcode"). }
    assert (E98a : add_vec_int (mword_of_int 0x98a : mword 64) 4
                   = mword_of_int 0x98e)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E98a. iIntros (h5) "Hrun".
    assert (Ezr : (zero_reg : mword 64) = mword_of_int 0)
      by (apply bv_eq; vm_compute; reflexivity).
    (* ---- 0x98e  c.mv a0,s1 ---- *)
    iApply (wp_uk_cmv γt γd γs γfd h5 m2 (mword_of_int 0x98e) a0_idx s1_idx
              (mword_of_int (sh_buf + Z.of_nat k))
              (16 + (80 + n))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs1_2 Ezr moi_add; f_equal; lia)
              with "[] Hrun").
    { iApply (uis_shk_98e with "Hcode"). }
    assert (E98e : add_vec_int (mword_of_int 0x98e : mword 64) 2
                   = mword_of_int 0x990)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E98e. iIntros (h6) "Hrun".
    set (m3 := <[Regidx a0_idx
                 := regval_into_reg
                      (mword_of_int (sh_buf + Z.of_nat k) : mword 64)]> m2).
    (* ---- 0x990  jal ra,strlen ---- *)
    iApply (wp_uk_jal γt γd γs γfd h6 m3 (mword_of_int 0x990)
              (mword_of_int 160 : mword 21) ra_idx
              (mword_of_int ShSyms.strlen) (mword_of_int 0x994)
              (16 + (80 + n))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_990 with "Hcode"). }
    iIntros (h7) "Hrun".
    set (m4 := <[Regidx ra_idx
                 := regval_into_reg (mword_of_int 0x994 : mword 64)]> m3).
    assert (Ha0_4 : m4 !!! Regidx a0_idx
                    = mword_of_int (sh_buf + Z.of_nat k)).
    { rewrite /m4 (upd_ne m3 (Regidx ra_idx) (Regidx a0_idx) _
                     ltac:(vm_compute; discriminate)).
      exact (upd_eq m2 (Regidx a0_idx) _). }
    assert (Hra_4 : m4 !!! Regidx ra_idx = (mword_of_int 0x994 : mword 64))
      by exact (upd_eq m3 (Regidx ra_idx) _).
    (* ---- strlen(buf + k), on a run BORROWED out of the line buffer ---- *)
    iDestruct (ushc_bytes_sub sh_buf sh_nbuf f k (S L) ltac:(lia) with "Hbuf")
      as "[Hsub Hclb]".
    iDestruct (ushc_ustr_of_bytes (sh_buf + Z.of_nat k) L
                 (fun j : nat => f (k + j)%nat)
                 HLbody HL31 HLnul with "Hsub") as "Hstr".
    iApply (wp_kshp_strlen h7 m4 (DfracOwn 1) (sh_buf + Z.of_nat k) L
              (fun j : nat => f (k + j)%nat) (94 + n)
              Ha0_4 ltac:(unfold sh_buf; lia)
              ltac:(unfold sh_buf, sh_nbuf, Z64 in *; lia)
              with "Hpcode Hstr [Hrun]").
    { replace (16 + (80 + n))%nat with (2 + (94 + n))%nat by lia.
      iExact "Hrun". }
    iIntros "Hstr" (h8 m5) "%Hcs45 %Ha0_5 Hrun".
    rewrite Hra_4.
    assert (Eret : ret_pc (mword_of_int 0x994 : mword 64) = mword_of_int 0x994)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Eret.
    replace (2 + (94 + n))%nat with (16 + (80 + n))%nat by lia.
    iDestruct (ushc_bytes_of_ustr (sh_buf + Z.of_nat k) L
                 (fun j : nat => f (k + j)%nat) HLnul with "Hstr") as "Hsub".
    iDestruct ("Hclb" with "Hsub") as "Hbuf".
    assert (Hs1_5 : m5 !!! Regidx s1_idx = mword_of_int (sh_buf + Z.of_nat k)).
    { rewrite (Hcs45 s1_idx ltac:(vm_compute; reflexivity)).
      rewrite /m4 (upd_ne m3 (Regidx ra_idx) (Regidx s1_idx) _
                     ltac:(vm_compute; discriminate)).
      rewrite /m3 (upd_ne m2 (Regidx a0_idx) (Regidx s1_idx) _
                     ltac:(vm_compute; discriminate)). exact Hs1_2. }
    (* ---- 0x994  addiw a5,a0,-1 -- [strlen(buf) - 1] ---- *)
    assert (Em1i : (sign_extend' 64 (mword_of_int 4095 : mword 12) : mword 64)
                   = mword_of_int (-1))
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uk_addiw γt γd γs γfd h8 m5 (mword_of_int 0x994)
              (mword_of_int 4095 : mword 12) a0_idx a5_idx
              (mword_of_int (Z.of_nat L - 1)) (16 + (80 + n))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha0_5 Em1i;
                    rewrite (moi_addw (Z.of_nat L) (-1)
                               ltac:(unfold Z31 in *; lia));
                    reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_994 with "Hcode"). }
    assert (E994 : add_vec_int (mword_of_int 0x994 : mword 64) 4
                   = mword_of_int 0x998)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E994. iIntros (h9) "Hrun".
    set (m6 := <[Regidx a5_idx
                 := regval_into_reg
                      (mword_of_int (Z.of_nat L - 1) : mword 64)]> m5).
    assert (Ha5_6 : m6 !!! Regidx a5_idx
                    = (mword_of_int (Z.of_nat L - 1) : mword 64))
      by exact (upd_eq m5 (Regidx a5_idx) _).
    (* ---- 0x998/0x99a  the 32-bit result, zero-extended ---- *)
    iApply (wp_uk_cslli γt γd γs γfd h9 m6 (mword_of_int 0x998)
              (mword_of_int 32 : mword 6) a5_idx
              (mword_of_int ((Z.of_nat L - 1) * 2 ^ 32))
              (16 + (80 + n))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha5_6; symmetry;
                    exact (moi_shl (Z.of_nat L - 1) 32 ltac:(lia)))
              with "[] Hrun").
    { iApply (uis_shk_998 with "Hcode"). }
    assert (E998 : add_vec_int (mword_of_int 0x998 : mword 64) 2
                   = mword_of_int 0x99a)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E998. iIntros (h10) "Hrun".
    set (m7 := <[Regidx a5_idx
                 := regval_into_reg
                      (mword_of_int ((Z.of_nat L - 1) * 2 ^ 32)
                       : mword 64)]> m6).
    assert (Ha5_7 : m7 !!! Regidx a5_idx
                    = (mword_of_int ((Z.of_nat L - 1) * 2 ^ 32) : mword 64))
      by exact (upd_eq m6 (Regidx a5_idx) _).
    assert (Escale : (Z.of_nat L - 1) * 2 ^ 32 / 2 ^ 32 = Z.of_nat L - 1)
      by (apply Z.div_mul; vm_compute; discriminate).
    iApply (wp_uk_csrli γt γd γs γfd h10 m7 (mword_of_int 0x99a)
              (mword_of_int 32 : mword 6) (mword_of_int 7 : mword 3) a5_idx
              (mword_of_int (Z.of_nat L - 1)) (16 + (80 + n))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha5_7;
                    rewrite (moi_shr ((Z.of_nat L - 1) * 2 ^ 32) 32
                               ltac:(lia)
                               ltac:(unfold sh_nbuf in HLhi; unfold Z64; lia));
                    rewrite Escale; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_99a with "Hcode"). }
    assert (E99a : add_vec_int (mword_of_int 0x99a : mword 64) 2
                   = mword_of_int 0x99c)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E99a. iIntros (h11) "Hrun".
    set (m8 := <[Regidx a5_idx
                 := regval_into_reg
                      (mword_of_int (Z.of_nat L - 1) : mword 64)]> m7).
    assert (Ha5_8 : m8 !!! Regidx a5_idx
                    = (mword_of_int (Z.of_nat L - 1) : mword 64))
      by exact (upd_eq m7 (Regidx a5_idx) _).
    assert (Hs1_8 : m8 !!! Regidx s1_idx
                    = mword_of_int (sh_buf + Z.of_nat k)).
    { rewrite /m8 (upd_ne m7 (Regidx a5_idx) (Regidx s1_idx) _
                     ltac:(vm_compute; discriminate)).
      rewrite /m7 (upd_ne m6 (Regidx a5_idx) (Regidx s1_idx) _
                     ltac:(vm_compute; discriminate)).
      rewrite /m6 (upd_ne m5 (Regidx a5_idx) (Regidx s1_idx) _
                     ltac:(vm_compute; discriminate)). exact Hs1_5. }
    (* ---- 0x99c  c.add a5,a5,s1 -- the address of the last byte ---- *)
    iApply (wp_uk_cadd γt γd γs γfd h11 m8 (mword_of_int 0x99c) a5_idx s1_idx
              (mword_of_int (Z.of_nat L - 1 + (sh_buf + Z.of_nat k)))
              (16 + (80 + n))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha5_8 Hs1_8 moi_add; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_99c with "Hcode"). }
    assert (E99c : add_vec_int (mword_of_int 0x99c : mword 64) 2
                   = mword_of_int 0x99e)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E99c. iIntros (h12) "Hrun".
    set (m9 := <[Regidx a5_idx
                 := regval_into_reg
                      (mword_of_int (Z.of_nat L - 1 + (sh_buf + Z.of_nat k))
                       : mword 64)]> m8).
    assert (Ha5_9 : m9 !!! Regidx a5_idx
                    = (mword_of_int (Z.of_nat L - 1 + (sh_buf + Z.of_nat k))
                       : mword 64))
      by exact (upd_eq m8 (Regidx a5_idx) _).
    assert (Hs1_9 : m9 !!! Regidx s1_idx
                    = mword_of_int (sh_buf + Z.of_nat k))
      by (rewrite /m9 (upd_ne m8 (Regidx a5_idx) (Regidx s1_idx) _
                         ltac:(vm_compute; discriminate)); exact Hs1_8).
    (* ---- 0x99e  sb zero,0(a5) -- [buf[strlen(buf)-1] = 0], the CHOP ---- *)
    iDestruct (urun_x0 with "Hrun") as "[%Hx0 Hrun]".
    assert (Eadn : sh_buf + Z.of_nat (k + L - 1)
                   = Z.of_nat L - 1 + (sh_buf + Z.of_nat k)) by lia.
    iDestruct (ushc_bytes_one sh_buf sh_nbuf f (k + L - 1)%nat ltac:(lia)
                 with "Hbuf") as "[Hbn Hcln]".
    iEval (rewrite Eadn) in "Hbn".
    iApply (wp_uk_sb γt γd γs γfd h12 m9 (mword_of_int 0x99e)
              (mword_of_int 0 : mword 12) a5_idx x0_idx
              (Z.of_nat L - 1 + (sh_buf + Z.of_nat k)) (f (k + L - 1)%nat)
              (16 + (80 + n))
              ltac:(rewrite Ha5_9
                      (uint_moi (Z.of_nat L - 1 + (sh_buf + Z.of_nat k))
                         ltac:(unfold sh_buf, sh_nbuf, Z64 in *; lia));
                    vm_compute uoff_i12; lia)
              with "[] Hbn Hrun").
    { iApply (uis_shk_99e with "Hcode"). }
    iIntros "Hbn". iIntros (h13) "Hrun".
    rewrite Hx0.
    assert (Enb0 : nth_byte (zero_reg : mword 64) 0%nat = ubyte0)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Enb0.
    iEval (rewrite <- Eadn) in "Hbn".
    iDestruct ("Hcln" $! ubyte0 with "Hbn") as "Hbuf".
    set (g := UkSh.ush_set f (k + L - 1)%nat ubyte0).
    assert (E99e : add_vec_int (mword_of_int 0x99e : mword 64) 4
                   = mword_of_int 0x9a2)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E99e.
    (* ---- 0x9a2  c.addi s1,s1,3 -- past the "cd " ---- *)
    assert (E3i : (sign_extend' 64 (mword_of_int 3 : mword 6) : mword 64)
                  = mword_of_int 3)
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uk_caddi γt γd γs γfd h13 m9 (mword_of_int 0x9a2)
              (mword_of_int 3 : mword 6) s1_idx
              (mword_of_int (sh_buf + Z.of_nat k + 3))
              (16 + (80 + n))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs1_9 E3i moi_add; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_9a2 with "Hcode"). }
    assert (E9a2 : add_vec_int (mword_of_int 0x9a2 : mword 64) 2
                   = mword_of_int 0x9a4)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E9a2. iIntros (h14) "Hrun".
    set (mA := <[Regidx s1_idx
                 := regval_into_reg
                      (mword_of_int (sh_buf + Z.of_nat k + 3)
                       : mword 64)]> m9).
    assert (Hs1_A : mA !!! Regidx s1_idx
                    = (mword_of_int (sh_buf + Z.of_nat k + 3) : mword 64))
      by exact (upd_eq m9 (Regidx s1_idx) _).
    (* ---- 0x9a4  c.mv a0,s1 ---- *)
    iApply (wp_uk_cmv γt γd γs γfd h14 mA (mword_of_int 0x9a4) a0_idx s1_idx
              (mword_of_int (sh_buf + Z.of_nat k + 3))
              (16 + (80 + n))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs1_A Ezr moi_add; f_equal; lia)
              with "[] Hrun").
    { iApply (uis_shk_9a4 with "Hcode"). }
    assert (E9a4 : add_vec_int (mword_of_int 0x9a4 : mword 64) 2
                   = mword_of_int 0x9a6)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E9a4. iIntros (h15) "Hrun".
    set (mB := <[Regidx a0_idx
                 := regval_into_reg
                      (mword_of_int (sh_buf + Z.of_nat k + 3)
                       : mword 64)]> mA).
    (* ---- 0x9a6  jal ra,chdir ---- *)
    iApply (wp_uk_jal γt γd γs γfd h15 mB (mword_of_int 0x9a6)
              (mword_of_int 848 : mword 21) ra_idx
              (mword_of_int ShSyms.chdir) (mword_of_int 0x9aa)
              (16 + (80 + n))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_9a6 with "Hcode"). }
    iIntros (h16) "Hrun".
    set (mC := <[Regidx ra_idx
                 := regval_into_reg (mword_of_int 0x9aa : mword 64)]> mB).
    assert (Hra_C : mC !!! Regidx ra_idx = (mword_of_int 0x9aa : mword 64))
      by exact (upd_eq mB (Regidx ra_idx) _).
    iApply (wp_kshc_chdir h16 mC (16 + (80 + n))
              with "Hcode Hrun").
    iIntros (h17 ret) "Hrun".
    rewrite Hra_C.
    assert (Eret2 : ret_pc (mword_of_int 0x9aa : mword 64)
                    = mword_of_int 0x9aa)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Eret2.
    set (mD := <[Regidx a0_idx := ret]>
                 (<[Regidx a7_idx := (mword_of_int 9 : mword 64)]> mC)).
    (* ---- what the caller's five constants are, all the way through ---- *)
    assert (HkeepD : forall q : mword 5,
              ucallee_saved_idx q = true ->
              Regidx q <> Regidx s1_idx ->
              mD !!! Regidx q = m !!! Regidx q).
    { intros q Hq Hq1.
      assert (Hne : forall rq : mword 5, ucallee_saved_idx rq = false ->
                      Regidx q <> Regidx rq).
      { intros rq Hr He. injection He as He. subst q.
        rewrite Hr in Hq. discriminate Hq. }
      assert (Fra : ucallee_saved_idx ra_idx = false)
        by (vm_compute; reflexivity).
      assert (Fa0 : ucallee_saved_idx a0_idx = false)
        by (vm_compute; reflexivity).
      assert (Fa5 : ucallee_saved_idx a5_idx = false)
        by (vm_compute; reflexivity).
      assert (Fa7 : ucallee_saved_idx a7_idx = false)
        by (vm_compute; reflexivity).
      rewrite /mD (upd_ne _ (Regidx a0_idx) (Regidx q) _ (Hne a0_idx Fa0)).
      rewrite (upd_ne mC (Regidx a7_idx) (Regidx q) _ (Hne a7_idx Fa7)).
      rewrite /mC (upd_ne mB (Regidx ra_idx) (Regidx q) _ (Hne ra_idx Fra)).
      rewrite /mB (upd_ne mA (Regidx a0_idx) (Regidx q) _ (Hne a0_idx Fa0)).
      rewrite /mA (upd_ne m9 (Regidx s1_idx) (Regidx q) _ Hq1).
      rewrite /m9 (upd_ne m8 (Regidx a5_idx) (Regidx q) _ (Hne a5_idx Fa5)).
      rewrite /m8 (upd_ne m7 (Regidx a5_idx) (Regidx q) _ (Hne a5_idx Fa5)).
      rewrite /m7 (upd_ne m6 (Regidx a5_idx) (Regidx q) _ (Hne a5_idx Fa5)).
      rewrite /m6 (upd_ne m5 (Regidx a5_idx) (Regidx q) _ (Hne a5_idx Fa5)).
      rewrite (Hcs45 q Hq).
      rewrite /m4 (upd_ne m3 (Regidx ra_idx) (Regidx q) _ (Hne ra_idx Fra)).
      rewrite /m3 (upd_ne m2 (Regidx a0_idx) (Regidx q) _ (Hne a0_idx Fa0)).
      rewrite /m2 (upd_ne m1 (Regidx a5_idx) (Regidx q) _ (Hne a5_idx Fa5)).
      rewrite /m1 (upd_ne m (Regidx a5_idx) (Regidx q) _ (Hne a5_idx Fa5)).
      reflexivity. }
    assert (HregsD : UkSh.ush_regs mD).
    { rewrite /UkSh.ush_regs. split_and!.
      - rewrite (HkeepD s2_idx ltac:(vm_compute; reflexivity)
                   ltac:(vm_compute; discriminate)). exact Hs2.
      - rewrite (HkeepD s3_idx ltac:(vm_compute; reflexivity)
                   ltac:(vm_compute; discriminate)). exact Hs3.
      - rewrite (HkeepD s4_idx ltac:(vm_compute; reflexivity)
                   ltac:(vm_compute; discriminate)). exact Hs4.
      - rewrite (HkeepD s5_idx ltac:(vm_compute; reflexivity)
                   ltac:(vm_compute; discriminate)). exact Hs5.
      - rewrite (HkeepD s6_idx ltac:(vm_compute; reflexivity)
                   ltac:(vm_compute; discriminate)). exact Hs6. }
    assert (Ha0_D : mD !!! Regidx a0_idx = ret)
      by exact (upd_eq _ (Regidx a0_idx) ret).
    assert (Hs1_D : mD !!! Regidx s1_idx
                    = (mword_of_int (sh_buf + Z.of_nat k + 3) : mword 64)).
    { rewrite /mD (upd_ne _ (Regidx a0_idx) (Regidx s1_idx) _
                     ltac:(vm_compute; discriminate)).
      rewrite (upd_ne mC (Regidx a7_idx) (Regidx s1_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite /mC (upd_ne mB (Regidx ra_idx) (Regidx s1_idx) _
                     ltac:(vm_compute; discriminate)).
      rewrite /mB (upd_ne mA (Regidx a0_idx) (Regidx s1_idx) _
                     ltac:(vm_compute; discriminate)). exact Hs1_A. }
    (* ---- 0x9aa  bgez a0,0x938 -- the two arms ---- *)
    iDestruct (urun_x0 with "Hrun") as "[%Hx0D Hrun]".
    remember (uv_btaken BGE (mD !!! Regidx a0_idx) (mD !!! Regidx x0_idx))
      as tk eqn:Htk.
    iApply (wp_uk_btype γt γd γs γfd h17 mD (mword_of_int 0x9aa)
              (mword_of_int 8078 : mword 13) x0_idx a0_idx BGE tk
              (mword_of_int 0x938) (16 + (80 + n))
              Htk
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(intros _; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_9aa with "Hcode"). }
    assert (E9aa : add_vec_int (mword_of_int 0x9aa : mword 64) 4
                   = mword_of_int 0x9ae)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E9aa. iIntros (h18) "Hrun".
    destruct tk.
    - (* ---- chdir SUCCEEDED: straight back to the command loop ---- *)
      iApply ("Hhead" $! h18 mD g n with "[%] Hstd Hdat Hsz Hbuf Hrun").
      exact HregsD.
    - (* ---- chdir FAILED: the one diagnostic in sh that comes back ---- *)
      (* THE PATH, as a string: what is left of the line after "cd ", cut
         off by the NUL the chop just wrote (or, when the line had no
         newline to chop, by the one that was already there). *)
      set (plen := (L - 4)%nat).
      assert (Hgbody : forall j : nat, (j < plen)%nat ->
                g (k + 3 + j)%nat <> ubyte0).
      { intros j Hj. rewrite /g /UkSh.ush_set.
        rewrite (proj2 (Nat.eqb_neq (k + 3 + j) (k + L - 1))
                   ltac:(unfold plen in Hj; lia)).
        replace (k + 3 + j)%nat with (k + (3 + j))%nat by lia.
        apply HLbody. unfold plen in Hj. lia. }
      assert (Hgnul : g (k + 3 + plen)%nat = ubyte0).
      { destruct (Nat.eq_dec L 3) as [E3 | Ene ].
        - assert (Ep : plen = 0%nat) by (unfold plen; lia).
          rewrite Ep Nat.add_0_r /g /UkSh.ush_set.
          rewrite (proj2 (Nat.eqb_neq (k + 3) (k + L - 1)) ltac:(lia)).
          replace (k + 3)%nat with (k + L)%nat by lia. exact HLnul.
        - rewrite /g /UkSh.ush_set.
          rewrite (proj2 (Nat.eqb_eq (k + 3 + plen) (k + L - 1))
                     ltac:(unfold plen; lia)).
          reflexivity. }
      assert (Hplen31 : Z.of_nat plen < 2 ^ 31)
        by (unfold plen, sh_nbuf in *; lia).
      assert (Ead3 : sh_buf + Z.of_nat (k + 3) = sh_buf + Z.of_nat k + 3)
        by lia.
      iDestruct (ushc_bytes_sub sh_buf sh_nbuf g (k + 3)%nat (S plen)
                   ltac:(unfold plen, sh_nbuf in *; lia) with "Hbuf")
        as "[Hsub Hclp]".
      iEval (rewrite Ead3) in "Hsub".
      iDestruct (ushc_ustr_of_bytes (sh_buf + Z.of_nat k + 3) plen
                   (fun j : nat => g (k + 3 + j)%nat)
                   Hgbody Hplen31 Hgnul with "Hsub") as "Hpstr".
      iDestruct (shd_str_of_ustr (DfracOwn 1) (sh_buf + Z.of_nat k + 3) plen
                   (fun j : nat => g (k + 3 + j)%nat) with "Hpstr") as "Hpstr".
      (* ---- 0x9ae  c.mv a2,s1 ---- *)
      iApply (wp_uk_cmv γt γd γs γfd h18 mD (mword_of_int 0x9ae) a2_idx s1_idx
                (mword_of_int (sh_buf + Z.of_nat k + 3))
                (16 + (80 + n))
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite Hs1_D Ezr moi_add; f_equal; lia)
                with "[] Hrun").
      { iApply (uis_shk_9ae with "Hcode"). }
      assert (E9ae : add_vec_int (mword_of_int 0x9ae : mword 64) 2
                     = mword_of_int 0x9b0)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite E9ae. iIntros (h19) "Hrun".
      set (mE := <[Regidx a2_idx
                   := regval_into_reg
                        (mword_of_int (sh_buf + Z.of_nat k + 3)
                         : mword 64)]> mD).
      (* ---- 0x9b0/0x9b4  a1 := the format literal ---- *)
      iApply (wp_uk_auipc γt γd γs γfd h19 mE (mword_of_int 0x9b0)
                (mword_of_int 1 : mword 20) a1_idx (mword_of_int 0x19b0)
                (16 + (80 + n))
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                with "[] Hrun").
      { iApply (uis_shk_9b0 with "Hcode"). }
      assert (E9b0 : add_vec_int (mword_of_int 0x9b0 : mword 64) 4
                     = mword_of_int 0x9b4)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite E9b0. iIntros (h20) "Hrun".
      set (mF := <[Regidx a1_idx
                   := regval_into_reg (mword_of_int 0x19b0 : mword 64)]> mE).
      assert (Ha1_F : mF !!! Regidx a1_idx
                      = (mword_of_int 0x19b0 : mword 64))
        by exact (upd_eq mE (Regidx a1_idx) _).
      assert (Em1584 : (sign_extend' 64 (mword_of_int 2512 : mword 12)
                        : mword 64) = mword_of_int (-1584))
        by (apply bv_eq; vm_compute; reflexivity).
      iApply (wp_uk_addi γt γd γs γfd h20 mF (mword_of_int 0x9b4)
                (mword_of_int 2512 : mword 12) a1_idx a1_idx
                (mword_of_int 4992) (16 + (80 + n))
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite Ha1_F Em1584 moi_add; f_equal; lia)
                with "[] Hrun").
      { iApply (uis_shk_9b4 with "Hcode"). }
      assert (E9b4 : add_vec_int (mword_of_int 0x9b4 : mword 64) 4
                     = mword_of_int 0x9b8)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite E9b4. iIntros (h21) "Hrun".
      set (mG := <[Regidx a1_idx
                   := regval_into_reg (mword_of_int 4992 : mword 64)]> mF).
      (* ---- 0x9b8  c.li a0,2 ---- *)
      iApply (wp_uk_cli γt γd γs γfd h21 mG (mword_of_int 0x9b8)
                (mword_of_int 2 : mword 6) a0_idx
                (16 + (80 + n))
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate) with "[] Hrun").
      { iApply (uis_shk_9b8 with "Hcode"). }
      assert (Em2 : <[Regidx a0_idx
                      := regval_into_reg (sign_extend' 64
                           (mword_of_int 2 : mword 6) : mword 64)]> mG
                    = <[Regidx a0_idx
                        := regval_into_reg (mword_of_int 2 : mword 64)]> mG)
        by (f_equal; apply bv_eq; vm_compute; reflexivity).
      assert (E9b8 : add_vec_int (mword_of_int 0x9b8 : mword 64) 2
                     = mword_of_int 0x9ba)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite E9b8 Em2. iIntros (h22) "Hrun".
      set (mH := <[Regidx a0_idx
                   := regval_into_reg (mword_of_int 2 : mword 64)]> mG).
      (* ---- 0x9ba  jal ra,fprintf ---- *)
      iApply (wp_uk_jal γt γd γs γfd h22 mH (mword_of_int 0x9ba)
                (mword_of_int 1776 : mword 21) ra_idx
                (mword_of_int ShSyms.fprintf) (mword_of_int 0x9be)
                (16 + (80 + n))
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity)
                with "[] Hrun").
      { iApply (uis_shk_9ba with "Hcode"). }
      iIntros (h23) "Hrun".
      set (mI := <[Regidx ra_idx
                   := regval_into_reg (mword_of_int 0x9be : mword 64)]> mH).
      assert (Hra_I : mI !!! Regidx ra_idx = (mword_of_int 0x9be : mword 64))
        by exact (upd_eq mH (Regidx ra_idx) _).
      assert (Ha1_I : mI !!! Regidx a1_idx = mword_of_int 4992).
      { rewrite /mI (upd_ne mH (Regidx ra_idx) (Regidx a1_idx) _
                       ltac:(vm_compute; discriminate)).
        rewrite /mH (upd_ne mG (Regidx a0_idx) (Regidx a1_idx) _
                       ltac:(vm_compute; discriminate)).
        exact (upd_eq mF (Regidx a1_idx) _). }
      assert (Ha2_I : mI !!! Regidx a2_idx
                      = mword_of_int (sh_buf + Z.of_nat k + 3)).
      { rewrite /mI (upd_ne mH (Regidx ra_idx) (Regidx a2_idx) _
                       ltac:(vm_compute; discriminate)).
        rewrite /mH (upd_ne mG (Regidx a0_idx) (Regidx a2_idx) _
                       ltac:(vm_compute; discriminate)).
        rewrite /mG (upd_ne mF (Regidx a1_idx) (Regidx a2_idx) _
                       ltac:(vm_compute; discriminate)).
        rewrite /mF (upd_ne mE (Regidx a1_idx) (Regidx a2_idx) _
                       ltac:(vm_compute; discriminate)).
        exact (upd_eq mD (Regidx a2_idx) _). }
      (* ---- fprintf(2, "cannot cd %s\n", buf + k + 3) ---- *)
      iDestruct (UkShDiag.shd_fmt_str γt 4992 13%nat
                   ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                   with "Hro") as "#Hfstr".
      replace (16 + (80 + n))%nat
        with (10 + (12 + (4 + (70 + n))))%nat by lia.
      iApply (UkShDiag.wp_kshd_fprintf_s γt γd γs γfd false (DfracOwn 1)
                4992 13%nat 10%nat (UkShDiag.shd_lit 4992)
                (sh_buf + Z.of_nat k + 3) plen
                (fun j : nat => g (k + 3 + j)%nat) h23 mI (70 + n)%nat
                ltac:(lia) ltac:(vm_compute; reflexivity)
                ltac:(lia)
                ltac:(vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity)
                (fun j Hj Hne =>
                   UkShDiag.shd_nopct_ok 4992 13%nat 10%nat j
                     ltac:(vm_compute; reflexivity) Hj Hne)
                ltac:(vm_compute; discriminate)
                ltac:(vm_compute; discriminate)
                ltac:(vm_compute; discriminate)
                ltac:(intros Hc; exfalso; lia)
                ltac:(unfold sh_buf; lia)
                Ha1_I Ha2_I
                with "Hcode Hfstr Hpstr Hrun").
      iIntros (h24 mJ) "Hpstr %HcsIJ Hrun".
      rewrite Hra_I.
      assert (Eret3 : ret_pc (mword_of_int 0x9be : mword 64)
                      = mword_of_int 0x9be)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite Eret3.
      (* the path goes back into the buffer *)
      iDestruct (shd_str_to_ustr (DfracOwn 1) (sh_buf + Z.of_nat k + 3) plen
                   (fun j : nat => g (k + 3 + j)%nat) with "Hpstr") as "Hpstr".
      iDestruct (ushc_bytes_of_ustr (sh_buf + Z.of_nat k + 3) plen
                   (fun j : nat => g (k + 3 + j)%nat) Hgnul with "Hpstr")
        as "Hsub".
      iEval (rewrite <- Ead3) in "Hsub".
      iDestruct ("Hclp" with "Hsub") as "Hbuf".
      (* ---- 0x9be  c.j 0x938 -- back into the command loop ---- *)
      iApply (wp_uk_cj γt γd γs γfd h24 mJ (mword_of_int 0x9be)
                (mword_of_int 1981 : mword 11) (mword_of_int 0x938)
                (10 + (12 + (4 + (70 + n))))
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity)
                with "[] Hrun").
      { iApply (uis_shk_9be with "Hcode"). }
      iIntros (h25) "Hrun".
      assert (HregsJ : UkSh.ush_regs mJ).
      { assert (HkeepJ : forall q : mword 5,
                  ucallee_saved_idx q = true ->
                  Regidx q <> Regidx s1_idx ->
                  mJ !!! Regidx q = m !!! Regidx q).
        { intros q Hq Hq1.
          assert (Hne : forall rq : mword 5, ucallee_saved_idx rq = false ->
                          Regidx q <> Regidx rq).
          { intros rq Hr He. injection He as He. subst q.
            rewrite Hr in Hq. discriminate Hq. }
          assert (Fra : ucallee_saved_idx ra_idx = false)
            by (vm_compute; reflexivity).
          assert (Fa0 : ucallee_saved_idx a0_idx = false)
            by (vm_compute; reflexivity).
          assert (Fa1 : ucallee_saved_idx a1_idx = false)
            by (vm_compute; reflexivity).
          assert (Fa2 : ucallee_saved_idx a2_idx = false)
            by (vm_compute; reflexivity).
          rewrite (HcsIJ q Hq).
          rewrite /mI (upd_ne mH (Regidx ra_idx) (Regidx q) _
                         (Hne ra_idx Fra)).
          rewrite /mH (upd_ne mG (Regidx a0_idx) (Regidx q) _
                         (Hne a0_idx Fa0)).
          rewrite /mG (upd_ne mF (Regidx a1_idx) (Regidx q) _
                         (Hne a1_idx Fa1)).
          rewrite /mF (upd_ne mE (Regidx a1_idx) (Regidx q) _
                         (Hne a1_idx Fa1)).
          rewrite /mE (upd_ne mD (Regidx a2_idx) (Regidx q) _
                         (Hne a2_idx Fa2)).
          exact (HkeepD q Hq Hq1). }
        rewrite /UkSh.ush_regs. split_and!.
        - rewrite (HkeepJ s2_idx ltac:(vm_compute; reflexivity)
                     ltac:(vm_compute; discriminate)). exact Hs2.
        - rewrite (HkeepJ s3_idx ltac:(vm_compute; reflexivity)
                     ltac:(vm_compute; discriminate)). exact Hs3.
        - rewrite (HkeepJ s4_idx ltac:(vm_compute; reflexivity)
                     ltac:(vm_compute; discriminate)). exact Hs4.
        - rewrite (HkeepJ s5_idx ltac:(vm_compute; reflexivity)
                     ltac:(vm_compute; discriminate)). exact Hs5.
        - rewrite (HkeepJ s6_idx ltac:(vm_compute; reflexivity)
                     ltac:(vm_compute; discriminate)). exact Hs6. }
      replace (10 + (12 + (4 + (70 + n))))%nat with (16 + (80 + n))%nat by lia.
      iApply ("Hhead" $! h25 mJ g n with "[%] Hstd Hdat Hsz Hbuf Hrun").
      exact HregsJ.
  Qed.





End UkShCd.
