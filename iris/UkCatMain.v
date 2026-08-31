(* ===================================================================== *)
(* UkCatMain.v -- cat's main() and start().                               *)
(*                                                                        *)
(*   main(argc, argv)                                                     *)
(*     if (argc <= 1) { cat(0); exit(0); }                                *)
(*     for (i = 1; i < argc; i++) {                                       *)
(*       if ((fd = open(argv[i], O_RDONLY)) < 0) {                        *)
(*         fprintf(2, "cat: cannot open %s\n", argv[i]); exit(1); }       *)
(*       cat(fd); close(fd);                                              *)
(*     }                                                                  *)
(*     exit(0);                                                           *)
(*                                                                        *)
(* Every path out of main is an [exit], so main has NO continuation and    *)
(* never restores the five registers it spilled -- which is why the loop   *)
(* invariant here names three registers and not a callee-saved set.        *)
(*                                                                        *)
(* The walk over argv is the [addiw]/[slli]/[srli] idiom the compiler uses *)
(* for `&argv[argc]`, the same one echo's main has: s2 runs from &argv[1]  *)
(* to s3 = &argv[argc], eight bytes a turn.                                *)
(*                                                                        *)
(* One precondition is not derivable from [uargv] and has to be asked for: *)
(* that no argv pointer is null.  vprintf's '%s' arm has a "(null)" branch *)
(* that reads its replacement out of .rodata rather than the data half,    *)
(* and that branch is excluded here rather than walked.                    *)
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
Require Import RegFile WpGpr.
Require Import AlignBits WpMmodeLeafBase.
Require Import UserBits UserPtTree UserExec ProcPtOwn.
Require Import WpUmodeBranch.
Require Import UmodeMem UmodeFetch UmodeArith UmodeAbi.
Require Import UserPerm UsysMemOk UexecWp UexecSlot UexecRet.
Require Import UserHeap UkRun UkRunLeaf UkRunMem UkRunSys.
Require Import UCodeCat.
Require Import TsoCtx.
Require User.CatSyms User.CatInstrs.
Local Open Scope Z_scope.
Import Defs.
Require Import UkProgAbi.
Require Import UkCat.
Require Import UkCatLit.
Require Import UkCatVprintf.
Require Import UkCatVprintfS.
Require Import UkCatFprintf.
Require Import UkCatCat.
Require Import UkRunBr.

Section UkCatMain.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  Context (γt γd γs : gname).

  Local Notation ra_idx := (mword_of_int 1 : mword 5).
  Local Notation s0_idx := (mword_of_int 8 : mword 5).
  Local Notation s1_idx := (mword_of_int 9 : mword 5).
  Local Notation a0_idx := (mword_of_int 10 : mword 5).
  Local Notation a1_idx := (mword_of_int 11 : mword 5).
  Local Notation a2_idx := (mword_of_int 12 : mword 5).
  Local Notation a5_idx := (mword_of_int 15 : mword 5).
  Local Notation s2_idx := (mword_of_int 18 : mword 5).
  Local Notation s3_idx := (mword_of_int 19 : mword 5).

  (* the "cat: cannot open %s\n" literal, and everything the '%s' walk
     wants to know about it -- all of it decided by [vm_compute]. *)
  Definition cm_msg : Z := 0x9e0.
  Definition cm_msg_len : nat := 20%nat.
  Definition cm_msg_q : nat := 17%nat.
  Definition cm_lit : nat -> mword 8 := cat_lit cm_msg.

  (* --------------------------------------------------------------------- *)
  (* WHAT SURVIVES A TURN OF THE LOOP.  Three registers: the frame pointer  *)
  (* main never moves, the cursor into argv, and the end it stops at.       *)
  (* --------------------------------------------------------------------- *)
  Definition cm_inv (sp0 : mword 64) (av : Z) (nargs i : nat)
      (m : regfile) : Prop :=
    m !!! Regidx csp_rs1 = add_vec_int sp0 (- (8 * Z.of_nat 6)) /\
    m !!! Regidx s2_idx = mword_of_int (av + 8 * Z.of_nat i) /\
    m !!! Regidx s3_idx = mword_of_int (av + 8 * Z.of_nat nargs).

  (* which registers a step may write without disturbing it *)
  Definition cm_writable (r : mword 5) : bool :=
    negb (Z.eqb (uint r) 2 || Z.eqb (uint r) 18 || Z.eqb (uint r) 19).

  Lemma cm_writable_ne (r : mword 5) (z : Z) :
    cm_writable r = true -> (z = 2 \/ z = 18 \/ z = 19) -> uint r <> z.
  Proof.
    unfold cm_writable. intro H. apply negb_true_iff in H.
    rewrite !orb_false_iff in H. destruct H as [[H1 H2] H3].
    apply Z.eqb_neq in H1. apply Z.eqb_neq in H2. apply Z.eqb_neq in H3.
    intros Hz He. rewrite He in H1, H2, H3. lia.
  Qed.

  Lemma cm_inv_upd (sp0 : mword 64) (av : Z) (nargs i : nat) (m : regfile)
      (r : mword 5) (v : mword 64) :
    cm_writable r = true ->
    cm_inv sp0 av nargs i m ->
    cm_inv sp0 av nargs i (<[Regidx r := regval_into_reg v]> m).
  Proof.
    intros Hw (Hsp & Hs2 & Hs3). unfold cm_inv.
    rewrite (upd_ne m (Regidx r) (Regidx csp_rs1) (regval_into_reg v)
               ltac:(apply not_eq_sym; apply uidx_ne;
                     apply (cm_writable_ne r _ Hw);
                     replace (uint csp_rs1) with 2
                       by (vm_compute; reflexivity); lia)).
    rewrite (upd_ne m (Regidx r) (Regidx s2_idx) (regval_into_reg v)
               ltac:(apply not_eq_sym; apply uidx_ne;
                     apply (cm_writable_ne r _ Hw);
                     replace (uint s2_idx) with 18
                       by (vm_compute; reflexivity); lia)).
    rewrite (upd_ne m (Regidx r) (Regidx s3_idx) (regval_into_reg v)
               ltac:(apply not_eq_sym; apply uidx_ne;
                     apply (cm_writable_ne r _ Hw);
                     replace (uint s3_idx) with 19
                       by (vm_compute; reflexivity); lia)).
    repeat (split; [ assumption | ]). assumption.
  Qed.

  Lemma cm_inv_call (sp0 : mword 64) (av : Z) (nargs i : nat) (m m' : regfile) :
    ucallee_saved m m' ->
    cm_inv sp0 av nargs i m -> cm_inv sp0 av nargs i m'.
  Proof.
    intros Hcs (Hsp & Hs2 & Hs3). unfold cm_inv.
    rewrite (Hcs csp_rs1 ltac:(vm_compute; reflexivity)).
    rewrite (Hcs s2_idx ltac:(vm_compute; reflexivity)).
    rewrite (Hcs s3_idx ltac:(vm_compute; reflexivity)).
    repeat (split; [ assumption | ]). assumption.
  Qed.

  (* ===================================================================== *)
  (* THE LITERAL "cat: cannot open %s\n" -- twenty bytes at 0x9e0, with a  *)
  (* '%' at 17 and an 's' at 18.  [cat_lit_ok] cannot be used on it: that   *)
  (* predicate says a literal has NO directive in it, which is exactly what *)
  (* this one is not.  What the '%s' walk wants instead is the same NUL     *)
  (* discipline plus the three byte values, and all of it is decided.       *)
  (* ===================================================================== *)
  Definition cm_ok : bool :=
    forallb (fun j => match cat_ro !! (cm_msg + Z.of_nat j)%Z with
                      | Some b => negb (Z.eqb (bv_unsigned b) 0)
                      | None => false
                      end)
            (seq 0 cm_msg_len)
    && match cat_ro !! (cm_msg + Z.of_nat cm_msg_len)%Z with
       | Some b => Z.eqb (bv_unsigned b) 0
       | None => false
       end.

  Definition cm_nopct : bool :=
    forallb (fun j => Nat.eqb j cm_msg_q
                      || negb (Z.eqb (bv_unsigned (cm_lit j)) 37))
            (seq 0 cm_msg_len).

  Lemma cm_nopct_ok (j : nat) :
    (j < cm_msg_len)%nat -> j <> cm_msg_q -> bv_unsigned (cm_lit j) <> 37.
  Proof.
    intros Hj Hne.
    assert (H : cm_nopct = true) by (vm_compute; reflexivity).
    unfold cm_nopct in H. rewrite forallb_forall in H.
    specialize (H j ltac:(apply in_seq; lia)).
    apply orb_true_iff in H as [H | H].
    - apply Nat.eqb_eq in H. exfalso. exact (Hne H).
    - apply negb_true_iff, Z.eqb_neq in H. exact H.
  Qed.

  Lemma cm_str : cat_rodata γt -∗ utext_str γt cm_msg cm_msg_len cm_lit.
  Proof.
    assert (Hok : cm_ok = true) by (vm_compute; reflexivity).
    unfold cm_ok in Hok. apply andb_true_iff in Hok as [Hbody Hnul].
    rewrite forallb_forall in Hbody.
    iIntros "#Hro". rewrite /cat_rodata.
    iApply (utext_str_of_img γt cat_ro cm_msg cm_msg_len cm_lit).
    - intros j Hj.
      specialize (Hbody j ltac:(apply in_seq; lia)).
      unfold cm_lit, cat_lit.
      destruct (cat_ro !! (cm_msg + Z.of_nat j)%Z) as [b | ] eqn:Hb;
        [ | discriminate ].
      apply negb_true_iff, Z.eqb_neq in Hbody.
      intro He. apply Hbody.
      assert (Hbe : b = ubyte0) by (rewrite <- He; reflexivity).
      rewrite Hbe. vm_compute. reflexivity.
    - unfold cm_msg_len. lia.
    - intros j Hj.
      specialize (Hbody j ltac:(apply in_seq; lia)).
      unfold cm_lit, cat_lit.
      destruct (cat_ro !! (cm_msg + Z.of_nat j)%Z) as [b | ] eqn:Hb;
        [ | discriminate ].
      reflexivity.
    - destruct (cat_ro !! (cm_msg + Z.of_nat cm_msg_len)%Z) as [b | ] eqn:Hb;
        [ | discriminate ].
      apply Z.eqb_eq in Hnul. f_equal. apply bv_eq. rewrite Hnul.
      vm_compute. reflexivity.
    - iExact "Hro".
  Qed.

  (* where the heap's own bounds come from *)
  Local Lemma urun_ubyte_bnd (h : CpuId) (m : regfile) (pc : mword 64)
      (avail : nat) (dq : dfrac) (a : Z) (b : bv 8) :
    urun γt γd γs h m pc avail -∗ ubyteq γd dq a b -∗ ⌜ 0 <= a < 2 ^ 38 ⌝.
  Proof.
    iIntros "Hrun Hb".
    iDestruct "Hrun" as (C pt Rut sz M pm) "(_ & _ & Hh & _ & _)".
    iDestruct (uheap_ubyte with "Hh Hb") as %(_ & _ & Hbnd).
    iPureIntro. exact Hbnd.
  Qed.

  Local Lemma urun_uword_bnd (h : CpuId) (m : regfile) (pc : mword 64)
      (avail : nat) (dq : dfrac) (a : Z) (w : mword 64) :
    urun γt γd γs h m pc avail -∗ uwordq γd dq a w -∗
    ⌜ 0 <= a /\ a + 8 <= 2 ^ 38 ⌝.
  Proof.
    iIntros "Hrun Hw". rewrite /uwordq /ubytesq.
    iDestruct (big_sepL_lookup_acc _ (seq 0 8) 0%nat 0%nat ltac:(reflexivity)
                 with "Hw") as "[H0 Hcl]".
    iDestruct (urun_ubyte_bnd with "Hrun H0") as %Hb0.
    iDestruct ("Hcl" with "H0") as "Hw".
    iDestruct (big_sepL_lookup_acc _ (seq 0 8) 7%nat 7%nat ltac:(reflexivity)
                 with "Hw") as "[H7 _]".
    iDestruct (urun_ubyte_bnd with "Hrun H7") as %Hb7.
    iPureIntro. lia.
  Qed.

  (* --------------------------------------------------------------------- *)
  (* THE OPEN-FAILURE ARM, 0xde -> exit.                                    *)
  (*                                                                        *)
  (*   ld a2,0(s2) ; auipc/addi a1,<msg> ; li a0,2 ; jal fprintf            *)
  (*   li a0,1 ; jal exit                                                   *)
  (* --------------------------------------------------------------------- *)
  Lemma wp_kcat_main_die (h : CpuId) (m : regfile) (av : Z) (args : list uarg)
      (i : nat) (g : uarg) (n : nat) :
    args !! i = Some g ->
    ua_ptr g <> 0 ->
    m !!! Regidx s2_idx = mword_of_int (av + 8 * Z.of_nat i) ->
    cat_code γt -∗
    cat_rodata γt -∗
    uargv γd av args -∗
    urun γt γd γs h m (mword_of_int 0xde) (10 + (12 + (4 + n))) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hi Hnz Hs2.
    iIntros "#Hcode #Hro #Hargv Hrun".
    iDestruct (cm_str with "Hro") as "#Hstr".
    iDestruct (uargv_align with "Hargv") as %[Hal Hargc].
    iDestruct (uargv_acc γd av args i g Hi with "Hargv") as "[[#Hw #Hsstr] _]".
    iDestruct (urun_uword_bnd with "Hrun Hw") as %[Hlo0 Hhi0].
    destruct cat_syms_pins
      as (_ & _ & _ & Hfprintf & _ & _ & _ & _ & _ & _ & Hexit).
    (* ---- 0xde  ld a2,0(s2) -- argv[i] ---- *)
    assert (Haddr : (av + 8 * Z.of_nat i)%Z
                    = uint (m !!! Regidx s2_idx)
                      + uoff_i12 (mword_of_int 0 : mword 12)).
    { rewrite Hs2 (uint_moi (av + 8 * Z.of_nat i)
                     ltac:(unfold Z64; lia)).
      replace (uoff_i12 (mword_of_int 0 : mword 12)) with 0
        by (vm_compute; reflexivity).
      lia. }
    assert (Hal8 : (av + 8 * Z.of_nat i) mod 8 = 0).
    { rewrite Z.add_mod; [ | lia ]. rewrite Hal Z.mul_comm Z_mod_mult.
      reflexivity. }
    iApply (wp_uk_ld γt γd γs h m (mword_of_int 0xde)
              (mword_of_int 0 : mword 12) s2_idx a2_idx DfracDiscarded
              (av + 8 * Z.of_nat i) (mword_of_int (ua_ptr g))
              (10 + (12 + (4 + n)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              Haddr Hal8 ltac:(vm_compute; discriminate)
              with "[] Hw Hrun").
    { iApply (uis_cat_de with "Hcode"). }
    assert (Ede : add_vec_int (mword_of_int 0xde : mword 64) 4
                  = mword_of_int 0xe2)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Ede.
    iIntros "_" (h1) "Hrun".
    set (m1 := <[Regidx a2_idx
                 := regval_into_reg
                      (mword_of_int (ua_ptr g) : mword 64)]> m).
    (* ---- 0xe2  auipc a1,0x1 ---- *)
    iApply (wp_uk_auipc γt γd γs h1 m1 (mword_of_int 0xe2)
              (mword_of_int 1 : mword 20) a1_idx (mword_of_int 0x10e2)
              (10 + (12 + (4 + n)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_cat_e2 with "Hcode"). }
    assert (Ee2 : add_vec_int (mword_of_int 0xe2 : mword 64) 4
                  = mword_of_int 0xe6)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Ee2.
    iIntros (h2) "Hrun".
    set (m2 := <[Regidx a1_idx
                 := regval_into_reg (mword_of_int 0x10e2 : mword 64)]> m1).
    (* ---- 0xe6  addi a1,a1,-1794 -- &"cat: cannot open %s\n" ---- *)
    assert (Ea1 : add_vec (m2 !!! Regidx a1_idx)
                    (sign_extend' 64 (mword_of_int 2302 : mword 12))
                  = mword_of_int cm_msg).
    { rewrite (upd_eq m1 (Regidx a1_idx) (regval_into_reg _)).
      apply bv_eq. vm_compute. reflexivity. }
    iApply (wp_uk_addi γt γd γs h2 m2 (mword_of_int 0xe6)
              (mword_of_int 2302 : mword 12) a1_idx a1_idx
              (mword_of_int cm_msg) (10 + (12 + (4 + n)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(exact (eq_sym Ea1))
              with "[] Hrun").
    { iApply (uis_cat_e6 with "Hcode"). }
    assert (Ee6 : add_vec_int (mword_of_int 0xe6 : mword 64) 4
                  = mword_of_int 0xea)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Ee6.
    iIntros (h3) "Hrun".
    set (m3 := <[Regidx a1_idx
                 := regval_into_reg (mword_of_int cm_msg : mword 64)]> m2).
    (* ---- 0xea  c.li a0,2 ---- *)
    iApply (wp_uk_cli γt γd γs h3 m3 (mword_of_int 0xea)
              (mword_of_int 2 : mword 6) a0_idx (10 + (12 + (4 + n)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              with "[] Hrun").
    { iApply (uis_cat_ea with "Hcode"). }
    assert (Eea : add_vec_int (mword_of_int 0xea : mword 64) 2
                  = mword_of_int 0xec)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Eea.
    iIntros (h4) "Hrun".
    set (m4 := <[Regidx a0_idx
                 := regval_into_reg
                      (sign_extend' 64 (mword_of_int 2 : mword 6)
                       : mword 64)]> m3).
    (* ---- 0xec  jal ra,0x7d0 <fprintf> ---- *)
    iApply (wp_uk_jal γt γd γs h4 m4 (mword_of_int 0xec)
              (mword_of_int 1764 : mword 21) ra_idx
              (mword_of_int CatSyms.fprintf) (mword_of_int 0xf0)
              (10 + (12 + (4 + n)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hfprintf; apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(rewrite Hfprintf; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_cat_ec with "Hcode"). }
    iIntros (h5) "Hrun".
    set (m5 := <[Regidx ra_idx
                 := regval_into_reg (mword_of_int 0xf0 : mword 64)]> m4).
    assert (Hra5 : m5 !!! Regidx ra_idx = (mword_of_int 0xf0 : mword 64))
      by exact (upd_eq m4 (Regidx ra_idx) (regval_into_reg _)).
    assert (Ha1_5 : m5 !!! Regidx a1_idx = mword_of_int cm_msg).
    { rewrite /m5 (upd_ne m4 (Regidx ra_idx) (Regidx a1_idx) _
                     ltac:(vm_compute; discriminate)).
      rewrite /m4 (upd_ne m3 (Regidx a0_idx) (Regidx a1_idx) _
                     ltac:(vm_compute; discriminate)).
      rewrite /m3. exact (upd_eq m2 (Regidx a1_idx) (regval_into_reg _)). }
    assert (Ha2_5 : m5 !!! Regidx a2_idx = mword_of_int (ua_ptr g)).
    { rewrite /m5 (upd_ne m4 (Regidx ra_idx) (Regidx a2_idx) _
                     ltac:(vm_compute; discriminate)).
      rewrite /m4 (upd_ne m3 (Regidx a0_idx) (Regidx a2_idx) _
                     ltac:(vm_compute; discriminate)).
      rewrite /m3 (upd_ne m2 (Regidx a1_idx) (Regidx a2_idx) _
                     ltac:(vm_compute; discriminate)).
      rewrite /m2 (upd_ne m1 (Regidx a1_idx) (Regidx a2_idx) _
                     ltac:(vm_compute; discriminate)).
      rewrite /m1. exact (upd_eq m (Regidx a2_idx) (regval_into_reg _)). }
    (* ---- fprintf(2, "cat: cannot open %s\n", argv[i]) ---- *)
    iApply (wp_kcat_fprintf_s γt γd γs cm_msg cm_msg_len cm_msg_q cm_lit
              (ua_ptr g) (ua_len g) (ua_bytes g) h5 m5 n
              ltac:(unfold cm_msg; lia)
              ltac:(unfold cm_msg, cm_msg_len; lia)
              ltac:(unfold cm_msg_len, cm_msg_q; lia)
              ltac:(unfold cm_lit, cm_msg, cm_msg_q; vm_compute; reflexivity)
              ltac:(unfold cm_lit, cm_msg, cm_msg_q; vm_compute; reflexivity)
              (fun j Hj Hne => cm_nopct_ok j Hj Hne)
              ltac:(unfold cm_lit, cm_msg, cm_msg_q; vm_compute; discriminate)
              ltac:(unfold cm_lit, cm_msg, cm_msg_q; vm_compute; discriminate)
              ltac:(unfold cm_lit, cm_msg, cm_msg_q; vm_compute; discriminate)
              ltac:(unfold cm_msg_len, cm_msg_q; intros HH; exfalso; lia)
              Hnz Ha1_5 Ha2_5
              with "Hcode Hstr Hsstr Hrun").
    iIntros (h6 m6) "_ Hrun".
    assert (Eret : ret_pc (m5 !!! Regidx ra_idx)
                   = (mword_of_int 0xf0 : mword 64))
      by (rewrite Hra5; apply bv_eq; vm_compute; reflexivity).
    rewrite Eret.
    (* ---- 0xf0  c.li a0,1 ---- *)
    iApply (wp_uk_cli γt γd γs h6 m6 (mword_of_int 0xf0)
              (mword_of_int 1 : mword 6) a0_idx (10 + (12 + (4 + n)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              with "[] Hrun").
    { iApply (uis_cat_f0 with "Hcode"). }
    assert (Ef0 : add_vec_int (mword_of_int 0xf0 : mword 64) 2
                  = mword_of_int 0xf2)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Ef0.
    iIntros (h7) "Hrun".
    set (m7 := <[Regidx a0_idx
                 := regval_into_reg
                      (sign_extend' 64 (mword_of_int 1 : mword 6)
                       : mword 64)]> m6).
    (* ---- 0xf2  jal ra,0x3ac <exit> ---- *)
    iApply (wp_uk_jal γt γd γs h7 m7 (mword_of_int 0xf2)
              (mword_of_int 698 : mword 21) ra_idx
              (mword_of_int CatSyms.exit) (mword_of_int 0xf6)
              (10 + (12 + (4 + n)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hexit; apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(rewrite Hexit; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_cat_f2 with "Hcode"). }
    iIntros (h8) "Hrun".
    iApply (wp_kcat_exit γt γd γs h8 _ (10 + (12 + (4 + n)))
              with "Hcode Hrun").
  Qed.

End UkCatMain.
