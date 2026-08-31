(* ===================================================================== *)
(* UkInitPrintf.v -- ulib's [printf(fmt, ...)], for a format string with   *)
(* no '%'.                                                                 *)
(*                                                                         *)
(* printf is a VARARGS MARSHALLER and nothing else: it spills a1..a7 into   *)
(* its own frame, points a va_list at the spill area, parks that pointer    *)
(* one slot lower, and tail-calls [vprintf(1, fmt, ap)].  For a format      *)
(* with no '%' vprintf never READS any of it, so the whole 96-byte frame    *)
(* here is write-only -- which is why the proof needs no fact about what    *)
(* the caller left in a1..a7, and why printf's post is [ucallee_saved] and  *)
(* nothing else.                                                           *)
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
Require Import UCodeInit.
Require Import TsoCtx.
Require User.InitSyms User.InitInstrs.
Local Open Scope Z_scope.
Import Defs.
Require Import UkProgAbi.
Require Import UkInit.
Require Import UkInitPutc.
Require Import UkInitVprintf.
Require Import UkRunBr.

Section UkInitPrintf.
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
  Local Notation a7_idx := (mword_of_int 17 : mword 5).
  Local Notation s2_idx := (mword_of_int 18 : mword 5).
  Local Notation s3_idx := (mword_of_int 19 : mword 5).
  Local Notation s4_idx := (mword_of_int 20 : mword 5).
  Local Notation s5_idx := (mword_of_int 21 : mword 5).
  Local Notation s6_idx := (mword_of_int 22 : mword 5).
  Local Notation s7_idx := (mword_of_int 23 : mword 5).
  Local Notation s8_idx := (mword_of_int 24 : mword 5).
  Local Notation a3_idx := (mword_of_int 13 : mword 5).
  Local Notation a4_idx := (mword_of_int 14 : mword 5).
  Local Notation a5_idx := (mword_of_int 15 : mword 5).
  Local Notation a6_idx := (mword_of_int 16 : mword 5).


  (* --------------------------------------------------------------------- *)
  (* printf(fmt) @0x7c0.                                                    *)
  (*                                                                        *)
  (* The frame, indexed down from the entry sp (s0 sits at sp0-64, so the    *)
  (* [8(s0)]..[56(s0)] spill area is slots 7..1 and [-24(s0)] is slot 11):   *)
  (*                                                                        *)
  (*   sp0-8  a7   sp0-16 a6   sp0-24 a5   sp0-32 a4   sp0-40 a3            *)
  (*   sp0-48 a2   sp0-56 a1   sp0-64 --   sp0-72 ra   sp0-80 s0            *)
  (*   sp0-88 ap   sp0-96 --                                                 *)
  (* --------------------------------------------------------------------- *)
  Lemma wp_kinit_printf (a : Z) (len : nat) (f : nat -> mword 8)
      (h : CpuId) (m : regfile) (n : nat) :
    0 <= a -> a + Z.of_nat len + 2 < 2 ^ 31 ->
    (0 < len)%nat ->
    (forall j : nat, (j < len)%nat -> bv_unsigned (f j) <> 37) ->
    m !!! Regidx a0_idx = mword_of_int a ->
    init_code γt -∗
    utext_str γt a len f -∗
    urun γt γd γs h m (mword_of_int InitSyms.printf) (12 + (12 + (4 + n))) -∗
    (∀ (h' : CpuId) (m' : regfile),
       ⌜ ucallee_saved m m' ⌝ -∗
       urun γt γd γs h' m' (ret_pc (m !!! Regidx ra_idx)) (12 + (12 + (4 + n))) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Ha0 Habnd Hlen Hpct Ha0r.
    iIntros "#Hcode #Hstr Hrun Hcont".
    destruct init_syms_pins
      as (_ & _ & Hprintf & Hvprintf & _ & _ & _ & _ & _ & _ & _ & _ & _).
    rewrite Hprintf.
    iDestruct (urun_stack with "Hrun") as %[Hal8' Hroom'].
    remember (m !!! Regidx csp_rs1) as sp0 eqn:Hsp0e.
    assert (Hsp : m !!! Regidx csp_rs1 = sp0) by (symmetry; exact Hsp0e).
    clear Hsp0e.
    assert (Hal8 : uint sp0 mod 8 = 0) by exact Hal8'.
    assert (Hlo : 96 <= uint sp0) by (clear -Hroom'; lia).
    assert (Hbsp : bv_unsigned (add_vec_int sp0 (- (8 * Z.of_nat 12)))
                   = bv_unsigned sp0 - 96).
    { replace (- (8 * Z.of_nat 12)) with (-96) by lia.
      exact (uv_avi_neg sp0 96 ltac:(apply Z.leb_le; reflexivity)
               ltac:(rewrite <- uint_unsigned; exact Hlo)). }
    assert (Hsp96 : uint (add_vec_int sp0 (- (8 * Z.of_nat 12)))
                    = uint sp0 - 96)
      by (rewrite !uint_unsigned; exact Hbsp).
    assert (HR : 0 <= bv_unsigned sp0 < 18446744073709551616).
    { pose proof (bv_unsigned_in_range 64 sp0) as H0.
      assert (Em : bv_modulus 64 = 18446744073709551616)
        by (vm_compute; reflexivity).
      rewrite Em in H0. exact H0. }
    assert (Hlt12 : bv_unsigned (add_vec_int sp0 (- (8 * Z.of_nat 12)))
                    + 8 * Z.of_nat 12 < Z64)
      by (clear -Hbsp HR; rewrite Hbsp; unfold Z64; lia).
    assert (Hup : add_vec_int (add_vec_int sp0 (- (8 * Z.of_nat 12)))
                    (8 * Z.of_nat 12) = sp0).
    { apply bv_eq.
      rewrite (uv_avi_pos (add_vec_int sp0 (- (8 * Z.of_nat 12)))
                 (8 * Z.of_nat 12) ltac:(apply Z.leb_le; reflexivity) Hlt12).
      clear -Hbsp. rewrite Hbsp. lia. }
    assert (Ho24 : uoff_sdsp (mword_of_int 3 : mword 6) = 24)
      by (vm_compute; reflexivity).
    assert (Ho16 : uoff_sdsp (mword_of_int 2 : mword 6) = 16)
      by (vm_compute; reflexivity).
    (* ---- 0x7c0  c.addi16sp sp,sp,-96 ---- *)
    iApply (wp_uk_caddi16sp_dn γt γd γs h m (mword_of_int 0x7c0)
              (mword_of_int 58 : mword 6) 12 (12 + (4 + n))
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_init_7c0 with "Hcode"). }
    iIntros "Hframe".
    assert (E7c0 : add_vec_int (mword_of_int 0x7c0 : mword 64) 2
                   = mword_of_int 0x7c2)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Hsp E7c0.
    iIntros (h0) "Hrun".
    set (mq1 := <[Regidx csp_rs1
                  := regval_into_reg (add_vec_int sp0 (- (8 * Z.of_nat 12)))]> m).
    assert (Hspq1 : mq1 !!! Regidx csp_rs1
                    = add_vec_int sp0 (- (8 * Z.of_nat 12)))
      by exact (upd_eq m (Regidx csp_rs1) (regval_into_reg _)).
    iDestruct (ustack_12_open with "Hframe")
      as "(_ & [%u1 Hu1] & [%u2 Hu2] & [%u3 Hu3] & [%u4 Hu4] & [%u5 Hu5]
            & [%u6 Hu6] & [%u7 Hu7] & Hu8 & [%u9 Hu9] & [%u10 Hu10]
            & [%u11 Hu11] & Hu12)".
    (* ---- 0x7c2  c.sdsp ra,24(sp) ---- *)
    assert (Hraq1 : mq1 !!! Regidx ra_idx = m !!! Regidx ra_idx)
      by exact (upd_ne m (Regidx csp_rs1) (Regidx ra_idx) _
                  ltac:(vm_compute; discriminate)).
    assert (Hs0q1 : mq1 !!! Regidx s0_idx = m !!! Regidx s0_idx)
      by exact (upd_ne m (Regidx csp_rs1) (Regidx s0_idx) _
                  ltac:(vm_compute; discriminate)).
    iApply (wp_uk_csdsp γt γd γs h0 mq1 (mword_of_int 0x7c2)
              (mword_of_int 3 : mword 6) ra_idx (uint sp0 - 72) u9 (12 + (4 + n))
              ltac:(rewrite Hspq1 Hsp96 Ho24; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              with "[] Hu9 Hrun").
    { iApply (uis_init_7c2 with "Hcode"). }
    iIntros "Hu9". rewrite Hraq1.
    assert (E7c2 : add_vec_int (mword_of_int 0x7c2 : mword 64) 2
                   = mword_of_int 0x7c4)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E7c2.
    iIntros (h1) "Hrun".
    (* ---- 0x7c4  c.sdsp s0,16(sp) ---- *)
    iApply (wp_uk_csdsp γt γd γs h1 mq1 (mword_of_int 0x7c4)
              (mword_of_int 2 : mword 6) s0_idx (uint sp0 - 80) u10 (12 + (4 + n))
              ltac:(rewrite Hspq1 Hsp96 Ho16; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              with "[] Hu10 Hrun").
    { iApply (uis_init_7c4 with "Hcode"). }
    iIntros "Hu10". rewrite Hs0q1.
    assert (E7c4 : add_vec_int (mword_of_int 0x7c4 : mword 64) 2
                   = mword_of_int 0x7c6)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E7c4.
    iIntros (h2) "Hrun".
    (* ---- 0x7c6  c.addi4spn s0,sp,32 -- s0 sits at sp0-64 ---- *)
    assert (Hs064 : add_vec (mq1 !!! Regidx csp_rs1)
                      (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8)))
                    = add_vec_int sp0 (- 64)).
    { rewrite Hspq1.
      assert (Ec32 : (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8))
                      : mword 64) = mword_of_int 32)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite Ec32.
      assert (Efold : add_vec (add_vec_int sp0 (- (8 * Z.of_nat 12)))
                        (mword_of_int 32)
                      = add_vec_int (add_vec_int sp0 (- (8 * Z.of_nat 12))) 32)
        by reflexivity.
      rewrite Efold. apply bv_eq.
      assert (H32 : (0 <= 32)%Z) by lia.
      assert (Hlt32 : bv_unsigned (add_vec_int sp0 (- (8 * Z.of_nat 12))) + 32
                      < Z64)
        by (clear -Hbsp HR; rewrite Hbsp; unfold Z64; lia).
      rewrite (uv_avi_pos (add_vec_int sp0 (- (8 * Z.of_nat 12))) 32 H32 Hlt32).
      assert (Hlo64 : 64 <= bv_unsigned sp0)
        by (clear -Hlo; rewrite <- uint_unsigned; lia).
      assert (Eneg : bv_unsigned (add_vec_int sp0 (- 64)) = bv_unsigned sp0 - 64)
        by (exact (uv_avi_neg sp0 64 ltac:(apply Z.leb_le; reflexivity) Hlo64)).
      rewrite Eneg Hbsp. lia. }
    iApply (wp_uk_caddi4spn γt γd γs h2 mq1 (mword_of_int 0x7c6)
              (mword_of_int 0 : mword 3) (mword_of_int 8 : mword 8) s0_idx
              (add_vec_int sp0 (- 64)) (12 + (4 + n))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; discriminate)
              ltac:(exact (eq_sym Hs064))
              with "[] Hrun").
    { iApply (uis_init_7c6 with "Hcode"). }
    assert (E7c6 : add_vec_int (mword_of_int 0x7c6 : mword 64) 2
                   = mword_of_int 0x7c8)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E7c6.
    iIntros (h3) "Hrun".
    set (mq2 := <[Regidx s0_idx
                  := regval_into_reg (add_vec_int sp0 (- 64))]> mq1).
    assert (Hs0q2 : uint (mq2 !!! Regidx s0_idx) = uint sp0 - 64).
    { rewrite (upd_eq mq1 (Regidx s0_idx) (regval_into_reg _)).
      rewrite !uint_unsigned.
      exact (uv_avi_neg sp0 64 ltac:(apply Z.leb_le; reflexivity)
               ltac:(rewrite <- uint_unsigned; lia)). }
    assert (Hspq2 : mq2 !!! Regidx csp_rs1
                    = add_vec_int sp0 (- (8 * Z.of_nat 12))).
    { rewrite <- Hspq1.
      exact (upd_ne mq1 (Regidx s0_idx) (Regidx csp_rs1) _
               ltac:(vm_compute; discriminate)). }
    (* ---- 0x7c8  c.sd a1,8(s0) ---- *)
    assert (Hoc8 : uoff_c8 (mword_of_int 1 : mword 5) = 8)
      by (vm_compute; reflexivity).
    iApply (wp_uk_csd γt γd γs h3 mq2 (mword_of_int 0x7c8)
              (mword_of_int 1 : mword 5) (mword_of_int 0 : mword 3)
              (mword_of_int 3 : mword 3) s0_idx a1_idx
              (uint sp0 - 56) u7 (12 + (4 + n))
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
              ltac:(rewrite Hs0q2 Hoc8; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              with "[] Hu7 Hrun").
    { iApply (uis_init_7c8 with "Hcode"). }
    iIntros "Hu7".
    assert (E7c8 : add_vec_int (mword_of_int 0x7c8 : mword 64) 2
                 = mword_of_int 0x7ca)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E7c8.
    iIntros (h4) "Hrun".
    (* ---- 0x7ca  c.sd a2,16(s0) ---- *)
    assert (Hoc16 : uoff_c8 (mword_of_int 2 : mword 5) = 16)
      by (vm_compute; reflexivity).
    iApply (wp_uk_csd γt γd γs h4 mq2 (mword_of_int 0x7ca)
              (mword_of_int 2 : mword 5) (mword_of_int 0 : mword 3)
              (mword_of_int 4 : mword 3) s0_idx a2_idx
              (uint sp0 - 48) u6 (12 + (4 + n))
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
              ltac:(rewrite Hs0q2 Hoc16; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              with "[] Hu6 Hrun").
    { iApply (uis_init_7ca with "Hcode"). }
    iIntros "Hu6".
    assert (E7ca : add_vec_int (mword_of_int 0x7ca : mword 64) 2
                 = mword_of_int 0x7cc)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E7ca.
    iIntros (h5) "Hrun".
    (* ---- 0x7cc  c.sd a3,24(s0) ---- *)
    assert (Hoc24 : uoff_c8 (mword_of_int 3 : mword 5) = 24)
      by (vm_compute; reflexivity).
    iApply (wp_uk_csd γt γd γs h5 mq2 (mword_of_int 0x7cc)
              (mword_of_int 3 : mword 5) (mword_of_int 0 : mword 3)
              (mword_of_int 5 : mword 3) s0_idx a3_idx
              (uint sp0 - 40) u5 (12 + (4 + n))
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
              ltac:(rewrite Hs0q2 Hoc24; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              with "[] Hu5 Hrun").
    { iApply (uis_init_7cc with "Hcode"). }
    iIntros "Hu5".
    assert (E7cc : add_vec_int (mword_of_int 0x7cc : mword 64) 2
                 = mword_of_int 0x7ce)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E7cc.
    iIntros (h6) "Hrun".
    (* ---- 0x7ce  c.sd a4,32(s0) ---- *)
    assert (Hoc32 : uoff_c8 (mword_of_int 4 : mword 5) = 32)
      by (vm_compute; reflexivity).
    iApply (wp_uk_csd γt γd γs h6 mq2 (mword_of_int 0x7ce)
              (mword_of_int 4 : mword 5) (mword_of_int 0 : mword 3)
              (mword_of_int 6 : mword 3) s0_idx a4_idx
              (uint sp0 - 32) u4 (12 + (4 + n))
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
              ltac:(rewrite Hs0q2 Hoc32; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              with "[] Hu4 Hrun").
    { iApply (uis_init_7ce with "Hcode"). }
    iIntros "Hu4".
    assert (E7ce : add_vec_int (mword_of_int 0x7ce : mword 64) 2
                 = mword_of_int 0x7d0)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E7ce.
    iIntros (h7) "Hrun".
    (* ---- 0x7d0  c.sd a5,40(s0) ---- *)
    assert (Hoc40 : uoff_c8 (mword_of_int 5 : mword 5) = 40)
      by (vm_compute; reflexivity).
    iApply (wp_uk_csd γt γd γs h7 mq2 (mword_of_int 0x7d0)
              (mword_of_int 5 : mword 5) (mword_of_int 0 : mword 3)
              (mword_of_int 7 : mword 3) s0_idx a5_idx
              (uint sp0 - 24) u3 (12 + (4 + n))
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
              ltac:(rewrite Hs0q2 Hoc40; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              with "[] Hu3 Hrun").
    { iApply (uis_init_7d0 with "Hcode"). }
    iIntros "Hu3".
    assert (E7d0 : add_vec_int (mword_of_int 0x7d0 : mword 64) 2
                 = mword_of_int 0x7d2)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E7d0.
    iIntros (h8) "Hrun".
    (* ---- 0x7d2  sd a6,48(s0) ---- *)
    assert (Hoi48 : uoff_i12 (mword_of_int 48 : mword 12) = 48)
      by (vm_compute; reflexivity).
    iApply (wp_uk_sd γt γd γs h8 mq2 (mword_of_int 0x7d2)
              (mword_of_int 48 : mword 12) s0_idx a6_idx
              (uint sp0 - 16) u2 (12 + (4 + n))
              ltac:(rewrite Hs0q2 Hoi48; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              with "[] Hu2 Hrun").
    { iApply (uis_init_7d2 with "Hcode"). }
    iIntros "Hu2".
    assert (E7d2 : add_vec_int (mword_of_int 0x7d2 : mword 64) 4
                 = mword_of_int 0x7d6)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E7d2.
    iIntros (h9) "Hrun".
    (* ---- 0x7d6  sd a7,56(s0) ---- *)
    assert (Hoi56 : uoff_i12 (mword_of_int 56 : mword 12) = 56)
      by (vm_compute; reflexivity).
    iApply (wp_uk_sd γt γd γs h9 mq2 (mword_of_int 0x7d6)
              (mword_of_int 56 : mword 12) s0_idx a7_idx
              (uint sp0 - 8) u1 (12 + (4 + n))
              ltac:(rewrite Hs0q2 Hoi56; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              with "[] Hu1 Hrun").
    { iApply (uis_init_7d6 with "Hcode"). }
    iIntros "Hu1".
    assert (E7d6 : add_vec_int (mword_of_int 0x7d6 : mword 64) 4
                 = mword_of_int 0x7da)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E7d6.
    iIntros (h10) "Hrun".
    (* ---- 0x7da  addi a2,s0,8 -- the va_list ---- *)
    iApply (wp_uk_addi γt γd γs h10 mq2 (mword_of_int 0x7da)
              (mword_of_int 8 : mword 12) s0_idx a2_idx
              (add_vec (mq2 !!! Regidx s0_idx)
                 (sign_extend' 64 (mword_of_int 8 : mword 12))) (12 + (4 + n))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) eq_refl
              with "[] Hrun").
    { iApply (uis_init_7da with "Hcode"). }
    assert (E7da : add_vec_int (mword_of_int 0x7da : mword 64) 4
                   = mword_of_int 0x7de)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E7da.
    iIntros (h11) "Hrun".
    set (mq3 := <[Regidx a2_idx
                  := regval_into_reg
                       (add_vec (mq2 !!! Regidx s0_idx)
                          (sign_extend' 64 (mword_of_int 8 : mword 12)))]> mq2).
    assert (Hs0q3 : uint (mq3 !!! Regidx s0_idx) = uint sp0 - 64).
    (* [f_equal] may close this outright: both register keys are concrete,
       so the lookup through the insert REDUCES.  Chain, do not sequence. *)
    { rewrite <- Hs0q2. f_equal;
        exact (upd_ne mq2 (Regidx a2_idx) (Regidx s0_idx) _
                 ltac:(vm_compute; discriminate)). }
    (* ---- 0x7de  sd a2,-24(s0) -- park it one slot lower ---- *)
    assert (Hoim24 : uoff_i12 (mword_of_int 4072 : mword 12) = -24)
      by (vm_compute; reflexivity).
    iApply (wp_uk_sd γt γd γs h11 mq3 (mword_of_int 0x7de)
              (mword_of_int 4072 : mword 12) s0_idx a2_idx
              (uint sp0 - 88) u11 (12 + (4 + n))
              ltac:(rewrite Hs0q3 Hoim24; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              with "[] Hu11 Hrun").
    { iApply (uis_init_7de with "Hcode"). }
    iIntros "Hu11".
    assert (E7de : add_vec_int (mword_of_int 0x7de : mword 64) 4
                   = mword_of_int 0x7e2)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E7de.
    iIntros (h12) "Hrun".
    (* ---- 0x7e2  c.mv a1,a0 -- the format pointer ---- *)
    assert (Ha0q3 : mq3 !!! Regidx a0_idx = mword_of_int a).
    { rewrite <- Ha0r.
      rewrite /mq3 (upd_ne mq2 (Regidx a2_idx) (Regidx a0_idx) _
                      ltac:(vm_compute; discriminate)).
      rewrite /mq2 (upd_ne mq1 (Regidx s0_idx) (Regidx a0_idx) _
                      ltac:(vm_compute; discriminate)).
      rewrite /mq1. exact (upd_ne m (Regidx csp_rs1) (Regidx a0_idx) _
                             ltac:(vm_compute; discriminate)). }
    iApply (wp_uk_cmv γt γd γs h12 mq3 (mword_of_int 0x7e2) a1_idx a0_idx
              (add_vec zero_reg (mq3 !!! Regidx a0_idx)) (12 + (4 + n))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) eq_refl
              with "[] Hrun").
    { iApply (uis_init_7e2 with "Hcode"). }
    assert (E7e2 : add_vec_int (mword_of_int 0x7e2 : mword 64) 2
                   = mword_of_int 0x7e4)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E7e2.
    iIntros (h13) "Hrun".
    set (mq4 := <[Regidx a1_idx
                  := regval_into_reg
                       (add_vec zero_reg (mq3 !!! Regidx a0_idx))]> mq3).
    assert (Ha1q4 : mq4 !!! Regidx a1_idx = mword_of_int a).
    { rewrite (upd_eq mq3 (Regidx a1_idx) (regval_into_reg _)).
      rewrite Ha0q3. apply add_vec_zero_l. }
    (* ---- 0x7e4  c.li a0,1 -- fd = stdout ---- *)
    iApply (wp_uk_cli γt γd γs h13 mq4 (mword_of_int 0x7e4)
              (mword_of_int 1 : mword 6) a0_idx (12 + (4 + n))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) with "[] Hrun").
    { iApply (uis_init_7e4 with "Hcode"). }
    assert (E7e4 : add_vec_int (mword_of_int 0x7e4 : mword 64) 2
                   = mword_of_int 0x7e6)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E7e4.
    iIntros (h14) "Hrun".
    set (mq5 := <[Regidx a0_idx
                  := regval_into_reg
                       (sign_extend' 64 (mword_of_int 1 : mword 6)
                        : mword 64)]> mq4).
    assert (Ha1q5 : mq5 !!! Regidx a1_idx = mword_of_int a).
    { rewrite <- Ha1q4.
      exact (upd_ne mq4 (Regidx a0_idx) (Regidx a1_idx) _
               ltac:(vm_compute; discriminate)). }
    (* ---- 0x7e6  jal ra,0x4d6 <vprintf> ---- *)
    iApply (wp_uk_jal γt γd γs h14 mq5 (mword_of_int 0x7e6)
              (mword_of_int 2096368 : mword 21) ra_idx
              (mword_of_int InitSyms.vprintf) (mword_of_int 0x7ea) (12 + (4 + n))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hvprintf; apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(rewrite Hvprintf; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_init_7e6 with "Hcode"). }
    iIntros (h15) "Hrun".
    set (mq6 := <[Regidx ra_idx
                  := regval_into_reg (mword_of_int 0x7ea : mword 64)]> mq5).
    assert (Hraq6 : mq6 !!! Regidx ra_idx = (mword_of_int 0x7ea : mword 64))
      by exact (upd_eq mq5 (Regidx ra_idx) (regval_into_reg _)).
    assert (Ha1q6 : mq6 !!! Regidx a1_idx = mword_of_int a).
    { rewrite <- Ha1q5.
      exact (upd_ne mq5 (Regidx ra_idx) (Regidx a1_idx) _
               ltac:(vm_compute; discriminate)). }
    (* ---- vprintf(1, fmt, ap) ---- *)
    iApply (wp_kinit_vprintf γt γd γs a len f h15 mq6 n
              Ha0 Habnd Hlen Hpct Ha1q6 with "Hcode Hstr Hrun").
    iIntros (h16 mq7) "%Hcs Hrun".
    assert (Eret : ret_pc (mq6 !!! Regidx ra_idx)
                   = (mword_of_int 0x7ea : mword 64))
      by (rewrite Hraq6; apply bv_eq; vm_compute; reflexivity).
    rewrite Eret.
    (* ---- 0x7ea  c.ldsp ra,24(sp) ---- *)
    assert (Hspq7 : mq7 !!! Regidx csp_rs1
                    = add_vec_int sp0 (- (8 * Z.of_nat 12))).
    { rewrite (Hcs csp_rs1 ltac:(vm_compute; reflexivity)).
      rewrite <- Hspq2.
      rewrite /mq6 (upd_ne mq5 (Regidx ra_idx) (Regidx csp_rs1) _
                      ltac:(vm_compute; discriminate)).
      rewrite /mq5 (upd_ne mq4 (Regidx a0_idx) (Regidx csp_rs1) _
                      ltac:(vm_compute; discriminate)).
      rewrite /mq4 (upd_ne mq3 (Regidx a1_idx) (Regidx csp_rs1) _
                      ltac:(vm_compute; discriminate)).
      rewrite /mq3. exact (upd_ne mq2 (Regidx a2_idx) (Regidx csp_rs1) _
                             ltac:(vm_compute; discriminate)). }
    iApply (wp_uk_cldsp γt γd γs h16 mq7 (mword_of_int 0x7ea)
              (mword_of_int 3 : mword 6) ra_idx (uint sp0 - 72)
              (m !!! Regidx ra_idx) (12 + (4 + n))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(rewrite Hspq7 Hsp96 Ho24; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              ltac:(vm_compute; discriminate)
              with "[] Hu9 Hrun").
    { iApply (uis_init_7ea with "Hcode"). }
    iIntros "Hu9".
    assert (E7ea : add_vec_int (mword_of_int 0x7ea : mword 64) 2
                   = mword_of_int 0x7ec)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E7ea.
    iIntros (h17) "Hrun".
    set (mq8 := <[Regidx ra_idx
                  := regval_into_reg (m !!! Regidx ra_idx)]> mq7).
    assert (Hspq8 : mq8 !!! Regidx csp_rs1
                    = add_vec_int sp0 (- (8 * Z.of_nat 12))).
    { rewrite <- Hspq7.
      exact (upd_ne mq7 (Regidx ra_idx) (Regidx csp_rs1) _
               ltac:(vm_compute; discriminate)). }
    (* ---- 0x7ec  c.ldsp s0,16(sp) ---- *)
    iApply (wp_uk_cldsp γt γd γs h17 mq8 (mword_of_int 0x7ec)
              (mword_of_int 2 : mword 6) s0_idx (uint sp0 - 80)
              (m !!! Regidx s0_idx) (12 + (4 + n))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(rewrite Hspq8 Hsp96 Ho16; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              ltac:(vm_compute; discriminate)
              with "[] Hu10 Hrun").
    { iApply (uis_init_7ec with "Hcode"). }
    iIntros "Hu10".
    assert (E7ec : add_vec_int (mword_of_int 0x7ec : mword 64) 2
                   = mword_of_int 0x7ee)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E7ec.
    iIntros (h18) "Hrun".
    set (mq9 := <[Regidx s0_idx
                  := regval_into_reg (m !!! Regidx s0_idx)]> mq8).
    assert (Hspq9 : mq9 !!! Regidx csp_rs1
                    = add_vec_int sp0 (- (8 * Z.of_nat 12))).
    { rewrite <- Hspq8.
      exact (upd_ne mq8 (Regidx s0_idx) (Regidx csp_rs1) _
               ltac:(vm_compute; discriminate)). }
    (* ---- 0x7ee  c.addi16sp sp,sp,96 -- the frame goes back ---- *)
    iApply (wp_uk_caddi16sp_up γt γd γs h18 mq9 (mword_of_int 0x7ee)
              (mword_of_int 6 : mword 6) 12 (12 + (4 + n))
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "[] [Hu1 Hu2 Hu3 Hu4 Hu5 Hu6 Hu7 Hu8 Hu9 Hu10 Hu11 Hu12] Hrun").
    { iApply (uis_init_7ee with "Hcode"). }
    { rewrite Hspq9 Hup.
      iApply (ustack_12_close γd sp0 Hal8
                with "[Hu1] [Hu2] [Hu3] [Hu4] [Hu5] [Hu6] [Hu7] Hu8
                      [Hu9] [Hu10] [Hu11] Hu12").
      { iExists (mq2 !!! Regidx a7_idx). iExact "Hu1". }
      { iExists (mq2 !!! Regidx a6_idx). iExact "Hu2". }
      { iExists (mq2 !!! Regidx a5_idx). iExact "Hu3". }
      { iExists (mq2 !!! Regidx a4_idx). iExact "Hu4". }
      { iExists (mq2 !!! Regidx a3_idx). iExact "Hu5". }
      { iExists (mq2 !!! Regidx a2_idx). iExact "Hu6". }
      { iExists (mq2 !!! Regidx a1_idx). iExact "Hu7". }
      { iExists (m !!! Regidx ra_idx). iExact "Hu9". }
      { iExists (m !!! Regidx s0_idx). iExact "Hu10". }
      { iExists (mq3 !!! Regidx a2_idx). iExact "Hu11". } }
    assert (E7ee : add_vec_int (mword_of_int 0x7ee : mword 64) 2
                   = mword_of_int 0x7f0)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Hspq9 Hup E7ee.
    iIntros (h19) "Hrun".
    set (mq10 := <[Regidx csp_rs1 := regval_into_reg sp0]> mq9).
    assert (Hraq10 : mq10 !!! Regidx ra_idx = m !!! Regidx ra_idx).
    { rewrite /mq10 (upd_ne mq9 (Regidx csp_rs1) (Regidx ra_idx) _
                       ltac:(vm_compute; discriminate)).
      rewrite /mq9 (upd_ne mq8 (Regidx s0_idx) (Regidx ra_idx) _
                       ltac:(vm_compute; discriminate)).
      rewrite /mq8. exact (upd_eq mq7 (Regidx ra_idx) (regval_into_reg _)). }
    (* ---- 0x7f0  c.jr ra ---- *)
    iApply (wp_uk_cjr γt γd γs h19 mq10 (mword_of_int 0x7f0) ra_idx
              (ret_pc (m !!! Regidx ra_idx)) (12 + (12 + (4 + n)))
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hraq10; reflexivity)
              with "[] Hrun").
    { iApply (uis_init_7f0 with "Hcode"). }
    iIntros (h20) "Hrun".
    iApply ("Hcont" $! h20 mq10 with "[] Hrun").
    iPureIntro. intros r Hr.
    assert (Kne : forall (q : mword 5) (z : Z),
               uint q = z -> uint r <> z -> Regidx r <> Regidx q).
    { intros q z Hq Hz. apply uidx_ne. rewrite Hq. exact Hz. }
    (* the walk writes sp, s0, ra, a0, a1 and a2 and NOTHING else, so every
       other callee-saved register comes back untouched -- vprintf's own
       [ucallee_saved] carries it across the call *)
    assert (Huntouched : uint r <> 1 -> uint r <> 2 -> uint r <> 8 ->
                         uint r <> 10 -> uint r <> 11 -> uint r <> 12 ->
                         mq10 !!! Regidx r = m !!! Regidx r).
    { intros K1 K2 K8 K10 K11 K12.
      rewrite /mq10 (upd_ne mq9 (Regidx csp_rs1) (Regidx r) _
                       (Kne csp_rs1 2 ltac:(vm_compute; reflexivity) K2)).
      rewrite /mq9 (upd_ne mq8 (Regidx s0_idx) (Regidx r) _
                       (Kne s0_idx 8 ltac:(vm_compute; reflexivity) K8)).
      rewrite /mq8 (upd_ne mq7 (Regidx ra_idx) (Regidx r) _
                       (Kne ra_idx 1 ltac:(vm_compute; reflexivity) K1)).
      rewrite (Hcs r Hr).
      rewrite /mq6 (upd_ne mq5 (Regidx ra_idx) (Regidx r) _
                       (Kne ra_idx 1 ltac:(vm_compute; reflexivity) K1)).
      rewrite /mq5 (upd_ne mq4 (Regidx a0_idx) (Regidx r) _
                       (Kne a0_idx 10 ltac:(vm_compute; reflexivity) K10)).
      rewrite /mq4 (upd_ne mq3 (Regidx a1_idx) (Regidx r) _
                       (Kne a1_idx 11 ltac:(vm_compute; reflexivity) K11)).
      rewrite /mq3 (upd_ne mq2 (Regidx a2_idx) (Regidx r) _
                       (Kne a2_idx 12 ltac:(vm_compute; reflexivity) K12)).
      rewrite /mq2 (upd_ne mq1 (Regidx s0_idx) (Regidx r) _
                       (Kne s0_idx 8 ltac:(vm_compute; reflexivity) K8)).
      rewrite /mq1. exact (upd_ne m (Regidx csp_rs1) (Regidx r) _
                             (Kne csp_rs1 2 ltac:(vm_compute; reflexivity) K2)). }
    destruct (ucs_cases r Hr) as [E2 | [E3 | [E4 | [E8 | [E9 | E18]]]]].
    - (* sp: pushed and popped *)
      assert (Er : Regidx r = Regidx csp_rs1)
        by (apply (uidx_eq r 2); [ exact E2 | vm_compute; reflexivity ]).
      rewrite Er /mq10 (upd_eq mq9 (Regidx csp_rs1) (regval_into_reg sp0)).
      rewrite <- Hsp. reflexivity.
    - apply Huntouched; lia.
    - apply Huntouched; lia.
    - (* s0: spilled and reloaded *)
      assert (Er : Regidx r = Regidx s0_idx)
        by (apply (uidx_eq r 8); [ exact E8 | vm_compute; reflexivity ]).
      rewrite Er /mq10 (upd_ne mq9 (Regidx csp_rs1) (Regidx s0_idx) _
                          ltac:(vm_compute; discriminate)).
      rewrite /mq9. exact (upd_eq mq8 (Regidx s0_idx) (regval_into_reg _)).
    - apply Huntouched; lia.
    - apply Huntouched; lia.
  Qed.


End UkInitPrintf.
