(* ===================================================================== *)
(* UkEcho.v -- the `echo` user program on the separation-logic heap.       *)
(*                                                                        *)
(* Five functions: main, start, strlen, and the exit/write syscall stubs.  *)
(* What echo needs that sync did not:                                     *)
(*                                                                        *)
(*   a SIGNED load displacement -- strlen's scan reads [lbu a4,-1(a5)];    *)
(*   [c.addi16sp] -- main's frame is 64 bytes, too big for [c.addi];       *)
(*   [ustr] -- strlen walks a NUL-terminated string, and the length it     *)
(*     returns is pinned by the resource rather than by a side condition;  *)
(*   a RETURNING function -- strlen restores ra, s0 and sp and jumps back, *)
(*     so its post says [ucallee_saved] and hands the free stack back.     *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_map ghost_var invariants.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExtras.
Require Import RegFile WpGpr.
Require Import AlignBits WpMmodeLeafBase.
Require Import UserBits UserPtTree UserExec ProcPtOwn.
Require Import WpUmodeBranch.
Require Import UmodeMem UmodeFetch UmodeArith UmodeAbi.
Require Import UserPerm UsysMemOk UexecWp UexecSlot UexecRet.
Require Import UserHeap UkRun UkRunLeaf UkRunMem UkRunSys.
Require Import UCodeEcho.
Require Import TsoCtx.
Require User.EchoSyms User.EchoInstrs.
Local Open Scope Z_scope.
Import Defs.

Section UkEcho.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  Context (γt γd γs : gname).

  Local Notation ra_idx := (mword_of_int 1 : mword 5).
  Local Notation s0_idx := (mword_of_int 8 : mword 5).
  Local Notation a0_idx := (mword_of_int 10 : mword 5).
  Local Notation a3_idx := (mword_of_int 13 : mword 5).
  Local Notation a4_idx := (mword_of_int 14 : mword 5).
  Local Notation a5_idx := (mword_of_int 15 : mword 5).
  Local Notation a7_idx := (mword_of_int 17 : mword 5).
  Local Notation a1_idx := (mword_of_int 11 : mword 5).
  Local Notation a2_idx := (mword_of_int 12 : mword 5).
  Local Notation s1_idx := (mword_of_int 9 : mword 5).
  Local Notation s2_idx := (mword_of_int 18 : mword 5).
  Local Notation s3_idx := (mword_of_int 19 : mword 5).
  Local Notation s4_idx := (mword_of_int 20 : mword 5).
  Local Notation s5_idx := (mword_of_int 21 : mword 5).
  Local Notation s6_idx := (mword_of_int 22 : mword 5).

  (* a callee-saved register is none of the ones a caller may clobber; the
     one fact every register-preservation chain below is built out of *)
  Local Lemma ucs_ne (r q : mword 5) :
    ucallee_saved_idx r = true -> ucallee_saved_idx q = false ->
    Regidx r <> Regidx q.
  Proof.
    intros Hr Hq He.
    assert (Hrr : r = q) by (injection He; trivial).
    rewrite Hrr Hq in Hr. discriminate.
  Qed.

  Local Notation CODE := "(C00 & C02 & C04 & C06 & C08 & C0a & C0c & C0e & C10 & C12 & C14 & C16 & C1a & C1e & C20 & C24 & C28 & C2c & C2e & C32 & C34 & C38 & C3c & C3e & C40 & C42 & C44 & C48 & C4a & C4e & C52 & C54 & C58 & C5a & C5c & C5e & C62 & C66 & C68 & C6c & C70 & C72 & C76 & C78 & C7c & C7e & C80 & C82 & C84 & C88 & Cdc & Cde & Ce0 & Ce2 & Ce4 & Ce8 & Cea & Cee & Cf0 & Cf2 & Cf6 & Cf8 & Cfc & Cfe & C100 & C102 & C104 & C106 & C332 & C334 & C352 & C354 & C358)".

  (* ------------------------------------------------------------------- *)
  (* THE EPILOGUE @0xfc, shared by both of strlen's arms:                  *)
  (*   c.ldsp ra,8(sp) ; c.ldsp s0,0(sp) ; c.addi sp,16 ; c.jr ra          *)
  (*                                                                      *)
  (* The two reloads take the spilled words back out of the frame; the     *)
  (* [c.addi sp,16] hands the frame BACK to the free stack, so [avail]     *)
  (* rises from [n] to [2 + n]; the [c.jr] returns to [ret_pc ra].  The    *)
  (* post says WHICH registers moved and that everything else is at its    *)
  (* entry value, which is what lets the caller conclude [ucallee_saved].  *)
  (* ------------------------------------------------------------------- *)
  Local Lemma wp_kecho_strlen_epi (h : CpuId) (m : regfile) (sp0 : mword 64)
      (vra vs0 : mword 64) (n : nat) :
    m !!! Regidx csp_rs1 = add_vec_int sp0 (- (8 * Z.of_nat 2)) ->
    uint sp0 mod 8 = 0 ->
    16 <= uint sp0 ->
    echo_code γt -∗
    uword γd (uint sp0 - 8) vra -∗
    uword γd (uint sp0 - 16) vs0 -∗
    urun γt γd γs h m (mword_of_int 0xfc) n -∗
    (∀ (h' : CpuId) (m' : regfile),
       ⌜ m' !!! Regidx csp_rs1 = sp0 ⌝ -∗
       ⌜ m' !!! Regidx s0_idx = vs0 ⌝ -∗
       ⌜ forall r : mword 5,
           Regidx r <> Regidx csp_rs1 -> Regidx r <> Regidx s0_idx ->
           Regidx r <> Regidx ra_idx -> m' !!! Regidx r = m !!! Regidx r ⌝ -∗
       urun γt γd γs h' m' (ret_pc vra) (2 + n) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hsp Hal8 Hlo. iIntros "#Hcode Hwra Hws0 Hrun Hcont".
    iPoseProof "Hcode" as "#Hc". iDestruct "Hc" as CODE.
    assert (Hbsp1 : bv_unsigned (add_vec_int sp0 (- (8 * Z.of_nat 2)))
                    = bv_unsigned sp0 - 16).
    { replace (- (8 * Z.of_nat 2)) with (-16) by lia.
      exact (uv_avi_neg sp0 16 ltac:(lia) ltac:(rewrite <- uint_unsigned; lia)). }
    assert (Hsp16 : uint (add_vec_int sp0 (- (8 * Z.of_nat 2))) = uint sp0 - 16)
      by (rewrite !uint_unsigned; exact Hbsp1).
    assert (Ho8 : uoff_sdsp (mword_of_int 1 : mword 6) = 8)
      by (vm_compute; reflexivity).
    assert (Ho0 : uoff_sdsp (mword_of_int 0 : mword 6) = 0)
      by (vm_compute; reflexivity).
    (* ---- 0xfc  c.ldsp ra,8(sp) ---- *)
    iApply (wp_uk_cldsp γt γd γs h m (mword_of_int 0xfc)
              (mword_of_int 1 : mword 6) ra_idx (uint sp0 - 8) vra n
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(rewrite Hsp Hsp16 Ho8; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              ltac:(vm_compute; discriminate)
              with "Cfc Hwra Hrun").
    iIntros "Hwra".
    assert (Efc : add_vec_int (mword_of_int 0xfc : mword 64) 2
                  = mword_of_int 0xfe)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Efc.
    iIntros (h1) "Hrun".
    set (m1 := <[Regidx ra_idx := regval_into_reg vra]> m).
    assert (Hsp1 : m1 !!! Regidx csp_rs1 = add_vec_int sp0 (- (8 * Z.of_nat 2))).
    { rewrite <- Hsp.
      exact (upd_ne m (Regidx ra_idx) (Regidx csp_rs1) (regval_into_reg vra)
               ltac:(vm_compute; discriminate)). }
    (* ---- 0xfe  c.ldsp s0,0(sp) ---- *)
    iApply (wp_uk_cldsp γt γd γs h1 m1 (mword_of_int 0xfe)
              (mword_of_int 0 : mword 6) s0_idx (uint sp0 - 16) vs0 n
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(rewrite Hsp1 Hsp16 Ho0; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              ltac:(vm_compute; discriminate)
              with "Cfe Hws0 Hrun").
    iIntros "Hws0".
    assert (Efe : add_vec_int (mword_of_int 0xfe : mword 64) 2
                  = mword_of_int 0x100)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Efe.
    iIntros (h2) "Hrun".
    set (m2 := <[Regidx s0_idx := regval_into_reg vs0]> m1).
    assert (Hsp2 : m2 !!! Regidx csp_rs1 = add_vec_int sp0 (- (8 * Z.of_nat 2))).
    { rewrite <- Hsp1.
      exact (upd_ne m1 (Regidx s0_idx) (Regidx csp_rs1) (regval_into_reg vs0)
               ltac:(vm_compute; discriminate)). }
    (* ---- 0x100  c.addi sp,sp,16 -- THE POP: the frame goes back ---- *)
    assert (HR : 0 <= bv_unsigned sp0 < 18446744073709551616).
    { pose proof (bv_unsigned_in_range 64 sp0) as H0.
      assert (Em : bv_modulus 64 = 18446744073709551616)
        by (vm_compute; reflexivity).
      rewrite Em in H0. exact H0. }
    assert (Hd2 : 0 <= 8 * Z.of_nat 2) by lia.
    assert (Hlt2 : bv_unsigned (add_vec_int sp0 (- (8 * Z.of_nat 2)))
                   + 8 * Z.of_nat 2 < Z64)
      by (rewrite Hbsp1; unfold Z64; lia).
    assert (Hup : add_vec_int (add_vec_int sp0 (- (8 * Z.of_nat 2)))
                    (8 * Z.of_nat 2) = sp0).
    { apply bv_eq.
      rewrite (uv_avi_pos (add_vec_int sp0 (- (8 * Z.of_nat 2)))
                 (8 * Z.of_nat 2) Hd2 Hlt2).
      rewrite Hbsp1. lia. }
    iApply (wp_uk_caddi_sp_up γt γd γs h2 m2 (mword_of_int 0x100)
              (mword_of_int 16 : mword 6) 2 n
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "C100 [Hwra Hws0] Hrun").
    { rewrite Hsp2 Hup ustack_2.
      iSplit; [ iPureIntro; exact Hal8 | ].
      iSplitL "Hwra"; [ iExists vra; iFrame | iExists vs0; iFrame ]. }
    assert (E100 : add_vec_int (mword_of_int 0x100 : mword 64) 2
                   = mword_of_int 0x102)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Hsp2 Hup E100.
    iIntros (h3) "Hrun".
    set (m3 := <[Regidx csp_rs1 := regval_into_reg sp0]> m2).
    assert (Hra3 : m3 !!! Regidx ra_idx = vra).
    { rewrite /m3 (upd_ne m2 (Regidx csp_rs1) (Regidx ra_idx)
                     (regval_into_reg sp0) ltac:(vm_compute; discriminate)).
      rewrite /m2 (upd_ne m1 (Regidx s0_idx) (Regidx ra_idx)
                     (regval_into_reg vs0) ltac:(vm_compute; discriminate)).
      rewrite /m1. exact (upd_eq m (Regidx ra_idx) (regval_into_reg vra)). }
    (* ---- 0x102  c.jr ra ---- *)
    iApply (wp_uk_cjr γt γd γs h3 m3 (mword_of_int 0x102)
              ra_idx (ret_pc vra) (2 + n)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hra3; reflexivity)
              with "C102 Hrun").
    iIntros (h4) "Hrun".
    iApply ("Hcont" $! h4 m3 with "[] [] [] Hrun").
    { iPureIntro. rewrite /m3.
      exact (upd_eq m2 (Regidx csp_rs1) (regval_into_reg sp0)). }
    { iPureIntro.
      rewrite /m3 (upd_ne m2 (Regidx csp_rs1) (Regidx s0_idx)
                     (regval_into_reg sp0) ltac:(vm_compute; discriminate)).
      rewrite /m2. exact (upd_eq m1 (Regidx s0_idx) (regval_into_reg vs0)). }
    { iPureIntro. intros r Hr1 Hr2 Hr3.
      rewrite /m3 (upd_ne m2 (Regidx csp_rs1) (Regidx r) (regval_into_reg sp0) Hr1).
      rewrite /m2 (upd_ne m1 (Regidx s0_idx) (Regidx r) (regval_into_reg vs0) Hr2).
      rewrite /m1.
      exact (upd_ne m (Regidx ra_idx) (Regidx r) (regval_into_reg vra) Hr3). }
  Qed.


  (* ------------------------------------------------------------------- *)
  (* ADDRESS BOUNDS OFF THE RESOURCE.  A byte the program owns is a byte  *)
  (* the image maps, and the heap invariant bounds every mapped address    *)
  (* by MAXVA -- so a caller never has to say where in memory its string   *)
  (* lives.  [urun_ustr_bnd] is that fact at the shape [ustr] hands out.   *)
  (* ------------------------------------------------------------------- *)
  Local Lemma urun_ubyte_bnd (h : CpuId) (m : regfile) (pc : mword 64)
      (avail : nat) (dq : dfrac) (a : Z) (b : bv 8) :
    urun γt γd γs h m pc avail -∗ ubyteq γd dq a b -∗ ⌜ 0 <= a < 2 ^ 38 ⌝.
  Proof.
    iIntros "Hrun Hb".
    iDestruct "Hrun" as (C pt Rut sz M pm) "(_ & _ & Hh & _ & _)".
    iDestruct (uheap_ubyte with "Hh Hb") as %(_ & _ & Hbnd).
    iPureIntro. exact Hbnd.
  Qed.

  Local Lemma urun_ustr_bnd (h : CpuId) (m : regfile) (pc : mword 64)
      (avail : nat) (dq : dfrac) (a : Z) (len : nat) (f : nat -> bv 8) :
    urun γt γd γs h m pc avail -∗ ustr γd dq a len f -∗
    ⌜ 0 <= a /\ a + Z.of_nat len < 2 ^ 38 ⌝.
  Proof.
    iIntros "Hrun Hs".
    iDestruct (ustr_nul with "Hs") as "[Hnul Hcl]".
    iDestruct (urun_ubyte_bnd with "Hrun Hnul") as %Hhi.
    iDestruct ("Hcl" with "Hnul") as "Hs".
    destruct len as [| len' ].
    - iPureIntro. lia.
    - iDestruct (ustr_byte γd dq a (S len') f 0%nat ltac:(lia) with "Hs")
        as "[Hb0 _]".
      iDestruct (urun_ubyte_bnd with "Hrun Hb0") as %Hlo.
      iPureIntro. lia.
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

  (* ------------------------------------------------------------------- *)
  (* ONE TURN OF THE SCAN, 0xee..0xf6:                                     *)
  (*   c.mv a3,a5 ; c.addi a5,a5,1 ; lbu a4,-1(a5) ; c.bnez a4,0xee        *)
  (*                                                                      *)
  (* a5 points AT the byte to test on entry and one PAST it on exit; a3    *)
  (* keeps the address that was tested, which is what the [subw] at 0xf8   *)
  (* turns into the length.  The byte decides where control goes, so the   *)
  (* caller says which target it expects and proves the [if].              *)
  (*                                                                      *)
  (* The byte's VALUE is a separate [Z] parameter rather than              *)
  (* [bv_unsigned b] inline: [mword 8] and [bv 8] carry different width    *)
  (* indices ([Z_idx 8] vs [8%N]), which are convertible but not equal to  *)
  (* [lia] or to [rewrite], so a caller that owns a [bv 8] byte could not  *)
  (* otherwise discharge the [if].                                        *)
  (* ------------------------------------------------------------------- *)
  Local Lemma wp_kecho_strlen_step (h : CpuId) (mc : regfile) (dq : dfrac)
      (p : Z) (b : mword 8) (bz : Z) (tgt : mword 64) (n : nat) :
    0 <= p -> p + 1 < Z64 ->
    bv_unsigned b = bz ->
    mc !!! Regidx a5_idx = mword_of_int p ->
    tgt = (if bz =? 0 then mword_of_int 0xf8 else mword_of_int 0xee) ->
    echo_code γt -∗
    ubyteq γd dq p b -∗
    urun γt γd γs h mc (mword_of_int 0xee) n -∗
    (ubyteq γd dq p b -∗
       ∀ h' : CpuId,
         urun γt γd γs h'
           (<[Regidx a4_idx := mword_of_int bz : mword 64]>
            (<[Regidx a5_idx := mword_of_int (p + 1) : mword 64]>
             (<[Regidx a3_idx := mword_of_int p : mword 64]> mc)))
           tgt n -∗
         WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hp0 Hp64 Hbz Ha5 Htgt. iIntros "#Hcode Hb Hrun Hcont".
    iPoseProof "Hcode" as "#Hc". iDestruct "Hc" as CODE.
    assert (Hbr : 0 <= bz < Z64).
    { rewrite <- Hbz. destruct (bv_unsigned_in_range _ b) as [Hlo Hhi].
      split; [ exact Hlo | ].
      eapply Z.lt_le_trans; [ exact Hhi | vm_compute; discriminate ]. }
    (* ---- 0xee  c.mv a3,a5 ---- *)
    iApply (wp_uk_cmv γt γd γs h mc (mword_of_int 0xee)
              a3_idx a5_idx (mword_of_int p) n
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha5 moi_add_zero_l; reflexivity)
              with "Cee Hrun").
    assert (Eee : add_vec_int (mword_of_int 0xee : mword 64) 2
                  = mword_of_int 0xf0)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Eee.
    iIntros (h1) "Hrun".
    set (m1 := <[Regidx a3_idx := regval_into_reg (mword_of_int p : mword 64)]> mc).
    assert (Ha51 : m1 !!! Regidx a5_idx = mword_of_int p).
    { rewrite /m1 (upd_ne mc (Regidx a3_idx) (Regidx a5_idx)
                     (regval_into_reg (mword_of_int p : mword 64))
                     ltac:(vm_compute; discriminate)).
      exact Ha5. }
    (* ---- 0xf0  c.addi a5,a5,1 ---- *)
    assert (E1 : (sign_extend' 64 (mword_of_int 1 : mword 6) : mword 64)
                 = mword_of_int 1)
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uk_caddi γt γd γs h1 m1 (mword_of_int 0xf0)
              (mword_of_int 1 : mword 6) a5_idx (mword_of_int (p + 1)) n
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha51 E1 moi_add; reflexivity)
              with "Cf0 Hrun").
    assert (Ef0 : add_vec_int (mword_of_int 0xf0 : mword 64) 2
                  = mword_of_int 0xf2)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Ef0.
    iIntros (h2) "Hrun".
    set (m2 := <[Regidx a5_idx
                 := regval_into_reg (mword_of_int (p + 1) : mword 64)]> m1).
    assert (Ha52 : m2 !!! Regidx a5_idx = mword_of_int (p + 1))
      by exact (upd_eq m1 (Regidx a5_idx)
                  (regval_into_reg (mword_of_int (p + 1) : mword 64))).
    (* ---- 0xf2  lbu a4,-1(a5) ---- *)
    assert (Eoff : uoff_i12 (mword_of_int 4095 : mword 12) = -1)
      by (vm_compute; reflexivity).
    assert (Euip : uint (mword_of_int (p + 1) : mword 64) = p + 1)
      by (apply uint_moi; lia).
    iApply (wp_uk_lbu γt γd γs h2 m2 (mword_of_int 0xf2)
              (mword_of_int 4095 : mword 12) a5_idx a4_idx dq p b n
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(rewrite Ha52 Euip Eoff; lia)
              ltac:(vm_compute; discriminate)
              with "Cf2 Hb Hrun").
    iIntros "Hb".
    assert (Ef2 : add_vec_int (mword_of_int 0xf2 : mword 64) 4
                  = mword_of_int 0xf6)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Ef2.
    iIntros (h3) "Hrun".
    set (m3 := <[Regidx a4_idx
                 := regval_into_reg (zero_extend' 64 b : mword 64)]> m2).
    assert (Ha43 : m3 !!! Regidx a4_idx = mword_of_int bz).
    { rewrite /m3 (upd_eq m2 (Regidx a4_idx)
                     (regval_into_reg (zero_extend' 64 b : mword 64))).
      rewrite <- Hbz. exact (zext8_moi b). }
    (* ---- 0xf6  c.bnez a4,0xee ---- *)
    assert (Htk : neq_vec (m3 !!! Regidx a4_idx) zero_reg = negb (bz =? 0))
      by (rewrite Ha43; exact (moi_neq_zero bz Hbr)).
    iApply (wp_uk_cbnez γt γd γs h3 m3 (mword_of_int 0xf6)
              (mword_of_int 252 : mword 8) (mword_of_int 6 : mword 3) a4_idx
              (negb (bz =? 0)) (mword_of_int 0xee) n
              ltac:(vm_compute; reflexivity)
              ltac:(rewrite Htk; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(intros _; vm_compute; reflexivity)
              with "Cf6 Hrun").
    iIntros (h4) "Hrun".
    iApply ("Hcont" with "Hb").
    rewrite /m3 /m2 /m1 (zext8_moi b) Hbz.
    replace (if negb (bz =? 0)
             then (mword_of_int 0xee : mword 64)
             else add_vec_int (mword_of_int 0xf6 : mword 64) 2)
      with tgt.
    { iExact "Hrun". }
    rewrite Htgt. destruct (bz =? 0); simpl;
      [ apply bv_eq; vm_compute; reflexivity | reflexivity ].
  Qed.

  (* ------------------------------------------------------------------- *)
  (* THE SCAN, 0xee onward.  [k] is the number of body bytes still to be   *)
  (* walked; the induction is on it, and the string resource comes back    *)
  (* untouched.  On exit a3 holds [a + len] -- ONE address, from which     *)
  (* the [subw] at 0xf8 reads off the length.  The loop terminates because *)
  (* [ustr] says the bytes below [len] are nonzero and the byte AT [len]   *)
  (* is not: the program cannot run off the end, and cannot stop early.    *)
  (* ------------------------------------------------------------------- *)
  Local Lemma wp_kecho_strlen_loop (dq : dfrac) (a : Z) (len : nat)
      (f : nat -> bv 8) :
    forall (k j : nat) (h : CpuId) (mc : regfile) (n : nat),
    (len = 1 + j + k)%nat ->
    0 <= a -> a + Z.of_nat len < 2 ^ 38 ->
    mc !!! Regidx a5_idx = mword_of_int (a + 1 + Z.of_nat j) ->
    echo_code γt -∗
    ustr γd dq a len f -∗
    urun γt γd γs h mc (mword_of_int 0xee) n -∗
    (ustr γd dq a len f -∗
       ∀ (h' : CpuId) (mc' : regfile),
         ⌜ mc' !!! Regidx a3_idx = mword_of_int (a + Z.of_nat len) ⌝ -∗
         ⌜ forall r : mword 5,
             Regidx r <> Regidx a3_idx -> Regidx r <> Regidx a4_idx ->
             Regidx r <> Regidx a5_idx -> mc' !!! Regidx r = mc !!! Regidx r ⌝ -∗
         urun γt γd γs h' mc' (mword_of_int 0xf8) n -∗
         WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros k. induction k as [| k IH ];
      intros j h mc n Hlen Ha0 Ha38 Ha5;
      change (2 ^ 38) with 274877906944 in Ha38;
      iIntros "#Hcode Hs Hrun Hcont".
    - (* the byte at [a + len] is the NUL: the branch falls through *)
      iDestruct (ustr_nul with "Hs") as "[Hb Hcl]".
      replace (a + Z.of_nat len) with (a + 1 + Z.of_nat j) by lia.
      iApply (wp_kecho_strlen_step h mc dq (a + 1 + Z.of_nat j) ubyte0
                (bv_unsigned ubyte0) (mword_of_int 0xf8) n
                ltac:(lia) ltac:(unfold Z64; lia) ltac:(reflexivity) Ha5
                ltac:(vm_compute; reflexivity)
                with "Hcode Hb Hrun").
      iIntros "Hb" (h1) "Hrun".
      iDestruct ("Hcl" with "Hb") as "Hs".
      set (mc1 := <[Regidx a4_idx := mword_of_int (bv_unsigned ubyte0) : mword 64]>
                   (<[Regidx a5_idx
                      := mword_of_int (a + 1 + Z.of_nat j + 1) : mword 64]>
                    (<[Regidx a3_idx
                       := mword_of_int (a + 1 + Z.of_nat j) : mword 64]> mc))).
      iSpecialize ("Hcont" with "Hs").
      iApply ("Hcont" $! h1 mc1 with "[] [] Hrun").
      { iPureIntro. rewrite /mc1.
        rewrite (upd_ne _ (Regidx a4_idx) (Regidx a3_idx) _
                   ltac:(vm_compute; discriminate)).
        rewrite (upd_ne _ (Regidx a5_idx) (Regidx a3_idx) _
                   ltac:(vm_compute; discriminate)).
        exact (upd_eq mc (Regidx a3_idx)
                 (mword_of_int (a + 1 + Z.of_nat j) : mword 64)). }
      { iPureIntro. intros r Hr3 Hr4 Hr5. rewrite /mc1.
        rewrite (upd_ne _ (Regidx a4_idx) (Regidx r) _ Hr4).
        rewrite (upd_ne _ (Regidx a5_idx) (Regidx r) _ Hr5).
        exact (upd_ne mc (Regidx a3_idx) (Regidx r) _ Hr3). }
    - (* a body byte: nonzero by [ustr], so the branch goes back to 0xee *)
      iDestruct (ustr_nonul with "Hs") as %Hne.
      assert (Hlt : (1 + j < len)%nat) by lia.
      assert (Hnz : (bv_unsigned (f (1 + j)%nat) =? 0) = false).
      { apply Z.eqb_neq. intro Hz. apply (Hne (1 + j)%nat Hlt).
        apply bv_eq. rewrite Hz. vm_compute. reflexivity. }
      iDestruct (ustr_byte γd dq a len f (1 + j)%nat Hlt with "Hs")
        as "[Hb Hcl]".
      replace (a + Z.of_nat (1 + j)) with (a + 1 + Z.of_nat j) by lia.
      iApply (wp_kecho_strlen_step h mc dq (a + 1 + Z.of_nat j) (f (1 + j)%nat)
                (bv_unsigned (f (1 + j)%nat)) (mword_of_int 0xee) n
                ltac:(lia) ltac:(unfold Z64; lia) ltac:(reflexivity) Ha5
                ltac:(rewrite Hnz; reflexivity)
                with "Hcode Hb Hrun").
      iIntros "Hb" (h1) "Hrun".
      iDestruct ("Hcl" with "Hb") as "Hs".
      set (mc1 := <[Regidx a4_idx
                    := mword_of_int (bv_unsigned (f (1 + j)%nat)) : mword 64]>
                   (<[Regidx a5_idx
                      := mword_of_int (a + 1 + Z.of_nat j + 1) : mword 64]>
                    (<[Regidx a3_idx
                       := mword_of_int (a + 1 + Z.of_nat j) : mword 64]> mc))).
      assert (Ha51 : mc1 !!! Regidx a5_idx
                     = mword_of_int (a + 1 + Z.of_nat (j + 1))).
      { rewrite /mc1 (upd_ne _ (Regidx a4_idx) (Regidx a5_idx) _
                        ltac:(vm_compute; discriminate)).
        rewrite (upd_eq _ (Regidx a5_idx)
                   (mword_of_int (a + 1 + Z.of_nat j + 1) : mword 64)).
        f_equal. lia. }
      iApply (IH (j + 1)%nat h1 mc1 n ltac:(lia) Ha0 Ha38 Ha51
                with "Hcode Hs Hrun").
      iIntros "Hs" (h2 mc2) "%Ha32 %Hpr2 Hrun2".
      iSpecialize ("Hcont" with "Hs").
      iApply ("Hcont" $! h2 mc2 with "[] [] Hrun2").
      { iPureIntro. exact Ha32. }
      { iPureIntro. intros r Hr3 Hr4 Hr5.
        rewrite (Hpr2 r Hr3 Hr4 Hr5). rewrite /mc1.
        rewrite (upd_ne _ (Regidx a4_idx) (Regidx r) _ Hr4).
        rewrite (upd_ne _ (Regidx a5_idx) (Regidx r) _ Hr5).
        exact (upd_ne mc (Regidx a3_idx) (Regidx r) _ Hr3). }
  Qed.


  (* ===================================================================== *)
  (* strlen -- the whole function.                                          *)
  (*                                                                        *)
  (* The contract names the LENGTH the string resource already carries, so  *)
  (* a caller learns [a0 = len] rather than -- a0 is whatever this loop *)
  (* computed.          The string comes back untouched, [ucallee_saved] says the  *)
  (* ABI was honoured, and [2 + n] on both sides of the arrow says the two  *)
  (* words of stack the frame borrowed were given back.                     *)
  (* ===================================================================== *)
  Lemma wp_kecho_strlen (h : CpuId) (m : regfile) (dq : dfrac) (a : Z)
      (len : nat) (f : nat -> bv 8) (n : nat) :
    m !!! Regidx a0_idx = mword_of_int a ->
    echo_code γt -∗
    ustr γd dq a len f -∗
    urun γt γd γs h m (mword_of_int EchoSyms.strlen) (2 + n) -∗
    (ustr γd dq a len f -∗
       ∀ (h' : CpuId) (m' : regfile),
         ⌜ ucallee_saved m m' ⌝ -∗
         ⌜ m' !!! Regidx a0_idx = mword_of_int (Z.of_nat len) ⌝ -∗
         urun γt γd γs h' m' (ret_pc (m !!! Regidx ra_idx)) (2 + n) -∗
         WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Ha0. iIntros "#Hcode Hs Hrun Hcont".
    iPoseProof "Hcode" as "#Hc". iDestruct "Hc" as CODE.
    destruct echo_syms_pins as (_ & _ & Hstrlen & _ & _). rewrite Hstrlen.
    (* the free stack the run owns: sp is aligned and has two words of room *)
    iDestruct (urun_stack with "Hrun") as %[Hal8 Hroom].
    (* the string sits at a MAPPED address, so its arithmetic cannot wrap *)
    iDestruct (urun_ustr_bnd with "Hrun Hs") as %[Halo Hahi].
    iDestruct (ustr_len with "Hs") as %Hlen31.
    change (2 ^ 38) with 274877906944 in Hahi.
    change (2 ^ 31) with 2147483648 in Hlen31.
    remember (m !!! Regidx csp_rs1) as sp0 eqn:Hsp0.
    assert (Hsp : m !!! Regidx csp_rs1 = sp0) by (symmetry; exact Hsp0).
    clear Hsp0.
    assert (Hlo : 16 <= uint sp0) by lia.
    assert (Hbsp1 : bv_unsigned (add_vec_int sp0 (- (8 * Z.of_nat 2)))
                    = bv_unsigned sp0 - 16).
    { replace (- (8 * Z.of_nat 2)) with (-16) by lia.
      exact (uv_avi_neg sp0 16 ltac:(lia) ltac:(rewrite <- uint_unsigned; lia)). }
    assert (Hsp16 : uint (add_vec_int sp0 (- (8 * Z.of_nat 2))) = uint sp0 - 16)
      by (rewrite !uint_unsigned; exact Hbsp1).
    assert (Ho8 : uoff_sdsp (mword_of_int 1 : mword 6) = 8)
      by (vm_compute; reflexivity).
    assert (Ho0 : uoff_sdsp (mword_of_int 0 : mword 6) = 0)
      by (vm_compute; reflexivity).
    assert (Hua : uint (mword_of_int a : mword 64) = a)
      by (apply uint_moi; unfold Z64; lia).
    (* a callee-saved register is none of the ones a caller may clobber *)
    assert (Hcs : forall (r q : mword 5), ucallee_saved_idx r = true ->
                    ucallee_saved_idx q = false -> Regidx r <> Regidx q).
    { intros r q Hr Hq He.
      assert (Hrr : r = q) by (injection He; trivial).
      rewrite Hrr Hq in Hr. discriminate. }
    (* ---- 0xdc  c.addi sp,sp,-16 -- THE PUSH ---- *)
    iApply (wp_uk_caddi_sp_dn γt γd γs h m (mword_of_int 0xdc)
              (mword_of_int 48 : mword 6) 2 n
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Cdc Hrun").
    assert (Edc : add_vec_int (mword_of_int 0xdc : mword 64) 2
                  = mword_of_int 0xde)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Hsp ustack_2 Edc.
    iIntros "(_ & [%v8 Hw8] & [%v0 Hw0])".
    iIntros (h1) "Hrun".
    set (m1 := <[Regidx csp_rs1
                 := regval_into_reg (add_vec_int sp0 (- (8 * Z.of_nat 2)))]> m).
    assert (Hsp1 : m1 !!! Regidx csp_rs1 = add_vec_int sp0 (- (8 * Z.of_nat 2)))
      by exact (upd_eq m (Regidx csp_rs1)
                  (regval_into_reg (add_vec_int sp0 (- (8 * Z.of_nat 2))))).
    assert (Hra1 : m1 !!! Regidx ra_idx = m !!! Regidx ra_idx)
      by exact (upd_ne m (Regidx csp_rs1) (Regidx ra_idx) _
                  ltac:(vm_compute; discriminate)).
    assert (Hs01 : m1 !!! Regidx s0_idx = m !!! Regidx s0_idx)
      by exact (upd_ne m (Regidx csp_rs1) (Regidx s0_idx) _
                  ltac:(vm_compute; discriminate)).
    (* ---- 0xde  c.sdsp ra,8(sp) ---- *)
    iApply (wp_uk_csdsp γt γd γs h1 m1 (mword_of_int 0xde)
              (mword_of_int 1 : mword 6) ra_idx (uint sp0 - 8) v8 n
              ltac:(rewrite Hsp1 Hsp16 Ho8; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              with "Cde Hw8 Hrun").
    iIntros "Hw8".
    assert (Ede : add_vec_int (mword_of_int 0xde : mword 64) 2
                  = mword_of_int 0xe0)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Ede. iIntros (h2) "Hrun".
    (* ---- 0xe0  c.sdsp s0,0(sp) ---- *)
    iApply (wp_uk_csdsp γt γd γs h2 m1 (mword_of_int 0xe0)
              (mword_of_int 0 : mword 6) s0_idx (uint sp0 - 16) v0 n
              ltac:(rewrite Hsp1 Hsp16 Ho0; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              with "Ce0 Hw0 Hrun").
    iIntros "Hw0".
    assert (Ee0 : add_vec_int (mword_of_int 0xe0 : mword 64) 2
                  = mword_of_int 0xe2)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Ee0 Hra1 Hs01. iIntros (h3) "Hrun".
    (* ---- 0xe2  c.addi4spn s0,sp,16 (s0 is dead until the epilogue) ---- *)
    iApply (wp_uk_caddi4spn γt γd γs h3 m1 (mword_of_int 0xe2)
              (mword_of_int 0 : mword 3) (mword_of_int 4 : mword 8) s0_idx
              (add_vec_int (add_vec_int sp0 (- (8 * Z.of_nat 2))) 16) n
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
              ltac:(rewrite Hsp1;
                    replace (sign_extend' 64
                               (caddi4spn_imm (mword_of_int 4 : mword 8))
                             : mword 64)
                      with (mword_of_int 16 : mword 64)
                      by (apply bv_eq; vm_compute; reflexivity);
                    reflexivity)
              with "Ce2 Hrun").
    assert (Ee2 : add_vec_int (mword_of_int 0xe2 : mword 64) 2
                  = mword_of_int 0xe4)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Ee2. iIntros (h4) "Hrun".
    set (m2 := <[Regidx s0_idx
                 := regval_into_reg
                      (add_vec_int (add_vec_int sp0 (- (8 * Z.of_nat 2))) 16)]> m1).
    assert (Hsp2 : m2 !!! Regidx csp_rs1 = add_vec_int sp0 (- (8 * Z.of_nat 2))).
    { rewrite /m2 (upd_ne m1 (Regidx s0_idx) (Regidx csp_rs1) _
                     ltac:(vm_compute; discriminate)).
      exact Hsp1. }
    assert (Ha02 : m2 !!! Regidx a0_idx = mword_of_int a).
    { rewrite /m2 (upd_ne m1 (Regidx s0_idx) (Regidx a0_idx) _
                     ltac:(vm_compute; discriminate)).
      rewrite /m1 (upd_ne m (Regidx csp_rs1) (Regidx a0_idx) _
                     ltac:(vm_compute; discriminate)).
      exact Ha0. }
    (* the byte at [a] -- the NUL when the string is empty, [f 0] otherwise.
       The byte's VALUE is carried as a [Z] so the [bv 8] the caller owns and
       the [mword 8] the load leaf produces can be related by conversion. *)
    iAssert (∃ (b0 : mword 8) (bz : Z),
               ⌜ bv_unsigned b0 = bz ⌝ ∗ ⌜ (bz =? 0) = (len =? 0)%nat ⌝ ∗
               ubyteq γd dq a b0 ∗
               (ubyteq γd dq a b0 -∗ ustr γd dq a len f))%I
      with "[Hs]" as "(%b0 & %bz & %Hbz & %Hbnz & Hb & Hcl)".
    { destruct len as [| len' ].
      - iDestruct (ustr_nul with "Hs") as "[Hb Hcl]".
        replace (a + Z.of_nat 0%nat) with a by lia.
        iExists ubyte0, (bv_unsigned ubyte0).
        iSplit; [ iPureIntro; reflexivity | ].
        iSplit; [ iPureIntro; vm_compute; reflexivity | ].
        iFrame.
      - iDestruct (ustr_nonul with "Hs") as %Hne.
        iDestruct (ustr_byte γd dq a (S len') f 0%nat ltac:(lia) with "Hs")
          as "[Hb Hcl]".
        replace (a + Z.of_nat 0%nat) with a by lia.
        iExists (f 0%nat), (bv_unsigned (f 0%nat)).
        iSplit; [ iPureIntro; reflexivity | ].
        iSplit.
        { iPureIntro. apply Z.eqb_neq. intro Hz.
          apply (Hne 0%nat ltac:(lia)). apply bv_eq. rewrite Hz.
          vm_compute. reflexivity. }
        iFrame. }
    (* ---- 0xe4  lbu a5,0(a0) ---- *)
    assert (Eoff0 : uoff_i12 (mword_of_int 0 : mword 12) = 0)
      by (vm_compute; reflexivity).
    iApply (wp_uk_lbu γt γd γs h4 m2 (mword_of_int 0xe4)
              (mword_of_int 0 : mword 12) a0_idx a5_idx dq a b0 n
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(rewrite Ha02 Hua Eoff0; lia)
              ltac:(vm_compute; discriminate)
              with "Ce4 Hb Hrun").
    iIntros "Hb".
    assert (Ee4 : add_vec_int (mword_of_int 0xe4 : mword 64) 4
                  = mword_of_int 0xe8)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Ee4. iIntros (h5) "Hrun".
    set (m3 := <[Regidx a5_idx
                 := regval_into_reg (zero_extend' 64 b0 : mword 64)]> m2).
    assert (Ha53 : m3 !!! Regidx a5_idx = mword_of_int bz).
    { rewrite /m3 (upd_eq m2 (Regidx a5_idx)
                     (regval_into_reg (zero_extend' 64 b0 : mword 64))).
      rewrite <- Hbz. exact (zext8_moi b0). }
    assert (Hbr : 0 <= bz < Z64).
    { rewrite <- Hbz. destruct (bv_unsigned_in_range _ b0) as [Hl Hh].
      split; [ exact Hl | ].
      eapply Z.lt_le_trans; [ exact Hh | vm_compute; discriminate ]. }
    assert (Hsp3 : m3 !!! Regidx csp_rs1 = add_vec_int sp0 (- (8 * Z.of_nat 2))).
    { rewrite /m3 (upd_ne m2 (Regidx a5_idx) (Regidx csp_rs1) _
                     ltac:(vm_compute; discriminate)).
      exact Hsp2. }
    assert (Ha03 : m3 !!! Regidx a0_idx = mword_of_int a).
    { rewrite /m3 (upd_ne m2 (Regidx a5_idx) (Regidx a0_idx) _
                     ltac:(vm_compute; discriminate)).
      exact Ha02. }
    (* ---- 0xe8  c.beqz a5,0x104 ---- *)
    iApply (wp_uk_cbeqz γt γd γs h5 m3 (mword_of_int 0xe8)
              (mword_of_int 14 : mword 8) (mword_of_int 7 : mword 3) a5_idx
              (bz =? 0) (mword_of_int 0x104) n
              ltac:(vm_compute; reflexivity)
              ltac:(rewrite Ha53; symmetry; exact (moi_eq_zero bz Hbr))
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(intros _; vm_compute; reflexivity)
              with "Ce8 Hrun").
    rewrite Hbnz. iIntros (h6) "Hrun".
    iDestruct ("Hcl" with "Hb") as "Hs".
    destruct len as [| len' ].
    - (* ---------------- the empty string: 0x104, 0x106 ---------------- *)
      assert (Eif : (if (0 =? 0)%nat then (mword_of_int 0x104 : mword 64)
                     else add_vec_int (mword_of_int 0xe8 : mword 64) 2)
                    = mword_of_int 0x104) by reflexivity.
      rewrite Eif.
      (* ---- 0x104  c.li a0,0 ---- *)
      iApply (wp_uk_cli γt γd γs h6 m3 (mword_of_int 0x104)
                (mword_of_int 0 : mword 6) a0_idx n
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate) with "C104 Hrun").
      assert (E104 : add_vec_int (mword_of_int 0x104 : mword 64) 2
                     = mword_of_int 0x106)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite E104. iIntros (h7) "Hrun".
      set (m4 := <[Regidx a0_idx
                   := regval_into_reg (sign_extend' 64 (mword_of_int 0 : mword 6)
                                       : mword 64)]> m3).
      (* ---- 0x106  c.j 0xfc ---- *)
      iApply (wp_uk_cj γt γd γs h7 m4 (mword_of_int 0x106)
                (mword_of_int 2043 : mword 11) (mword_of_int 0xfc) n
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity)
                with "C106 Hrun").
      iIntros (h8) "Hrun".
      assert (Hsp4 : m4 !!! Regidx csp_rs1
                     = add_vec_int sp0 (- (8 * Z.of_nat 2))).
      { rewrite /m4 (upd_ne m3 (Regidx a0_idx) (Regidx csp_rs1) _
                       ltac:(vm_compute; discriminate)).
        exact Hsp3. }
      iApply (wp_kecho_strlen_epi h8 m4 sp0 (m !!! Regidx ra_idx)
                (m !!! Regidx s0_idx) n Hsp4 Hal8 Hlo
                with "Hcode Hw8 Hw0 Hrun").
      iIntros (h9 m') "%Hsp' %Hs0' %Hpres Hrun".
      iSpecialize ("Hcont" with "Hs").
      iApply ("Hcont" $! h9 m' with "[] [] Hrun").
      { iPureIntro. intros r Hr.
        assert (Hn1 : Regidx r <> Regidx ra_idx)
          by (apply (Hcs r _ Hr); vm_compute; reflexivity).
        assert (Hn10 : Regidx r <> Regidx a0_idx)
          by (apply (Hcs r _ Hr); vm_compute; reflexivity).
        assert (Hn15 : Regidx r <> Regidx a5_idx)
          by (apply (Hcs r _ Hr); vm_compute; reflexivity).
        destruct (decide (Regidx r = Regidx csp_rs1)) as [He2 | Hn2].
        { rewrite He2 Hsp' Hsp. reflexivity. }
        destruct (decide (Regidx r = Regidx s0_idx)) as [He8 | Hn8].
        { rewrite He8. exact Hs0'. }
        rewrite (Hpres r Hn2 Hn8 Hn1).
        rewrite /m4 (upd_ne m3 (Regidx a0_idx) (Regidx r) _ Hn10).
        rewrite /m3 (upd_ne m2 (Regidx a5_idx) (Regidx r) _ Hn15).
        rewrite /m2 (upd_ne m1 (Regidx s0_idx) (Regidx r) _ Hn8).
        exact (upd_ne m (Regidx csp_rs1) (Regidx r) _ Hn2). }
      { iPureIntro.
        rewrite (Hpres a0_idx ltac:(vm_compute; discriminate)
                   ltac:(vm_compute; discriminate)
                   ltac:(vm_compute; discriminate)).
        rewrite /m4 (upd_eq m3 (Regidx a0_idx)
                       (regval_into_reg
                          (sign_extend' 64 (mword_of_int 0 : mword 6)
                           : mword 64))).
        apply bv_eq; vm_compute; reflexivity. }
    - (* ------------- a nonempty string: 0xea, the scan, 0xf8 ---------- *)
      assert (Eif : (if (S len' =? 0)%nat then (mword_of_int 0x104 : mword 64)
                     else add_vec_int (mword_of_int 0xe8 : mword 64) 2)
                    = mword_of_int 0xea)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite Eif.
      (* ---- 0xea  addi a5,a0,1 ---- *)
      iApply (wp_uk_addi γt γd γs h6 m3 (mword_of_int 0xea)
                (mword_of_int 1 : mword 12) a0_idx a5_idx
                (mword_of_int (a + 1)) n
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite Ha03;
                      replace (sign_extend' 64 (mword_of_int 1 : mword 12)
                               : mword 64)
                        with (mword_of_int 1 : mword 64)
                        by (apply bv_eq; vm_compute; reflexivity);
                      rewrite moi_add; reflexivity)
                with "Cea Hrun").
      assert (Eea : add_vec_int (mword_of_int 0xea : mword 64) 4
                    = mword_of_int 0xee)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite Eea. iIntros (h7) "Hrun".
      set (m4 := <[Regidx a5_idx
                   := regval_into_reg (mword_of_int (a + 1) : mword 64)]> m3).
      assert (Ha54 : m4 !!! Regidx a5_idx = mword_of_int (a + 1 + Z.of_nat 0)).
      { replace (a + 1 + Z.of_nat 0) with (a + 1) by lia.
        exact (upd_eq m3 (Regidx a5_idx)
                 (regval_into_reg (mword_of_int (a + 1) : mword 64))). }
      (* ---- 0xee..0xf6  THE SCAN ---- *)
      iApply (wp_kecho_strlen_loop dq a (S len') f len' 0%nat h7 m4 n
                ltac:(lia) Halo Hahi Ha54 with "Hcode Hs Hrun").
      iIntros "Hs" (h8 mc2) "%Ha3c %Hprc Hrun".
      assert (Ha0c : mc2 !!! Regidx a0_idx = mword_of_int a).
      { rewrite (Hprc a0_idx ltac:(vm_compute; discriminate)
                   ltac:(vm_compute; discriminate)
                   ltac:(vm_compute; discriminate)).
        rewrite /m4 (upd_ne m3 (Regidx a5_idx) (Regidx a0_idx) _
                       ltac:(vm_compute; discriminate)).
        exact Ha03. }
      assert (Hspc : mc2 !!! Regidx csp_rs1
                     = add_vec_int sp0 (- (8 * Z.of_nat 2))).
      { rewrite (Hprc csp_rs1 ltac:(vm_compute; discriminate)
                   ltac:(vm_compute; discriminate)
                   ltac:(vm_compute; discriminate)).
        rewrite /m4 (upd_ne m3 (Regidx a5_idx) (Regidx csp_rs1) _
                       ltac:(vm_compute; discriminate)).
        exact Hsp3. }
      (* ---- 0xf8  subw a0,a3,a0 ---- *)
      assert (Hsubw : (sign_extend' 64
                         (sub_vec
                            (subrange_vec_dec
                               (mword_of_int (a + Z.of_nat (S len')) : mword 64)
                               31 0 : mword 32)
                            (subrange_vec_dec (mword_of_int a : mword 64)
                               31 0 : mword 32)) : mword 64)
                      = mword_of_int (Z.of_nat (S len'))).
      { rewrite (moi_subw (a + Z.of_nat (S len')) a ltac:(unfold Z31; lia)).
        f_equal. lia. }
      iApply (wp_uk_subw γt γd γs h8 mc2 (mword_of_int 0xf8)
                a3_idx a0_idx a0_idx (mword_of_int (Z.of_nat (S len'))) n
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite Ha3c Ha0c Hsubw; reflexivity)
                with "Cf8 Hrun").
      assert (Ef8 : add_vec_int (mword_of_int 0xf8 : mword 64) 4
                    = mword_of_int 0xfc)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite Ef8. iIntros (h9) "Hrun".
      set (m5 := <[Regidx a0_idx
                   := regval_into_reg
                        (mword_of_int (Z.of_nat (S len')) : mword 64)]> mc2).
      assert (Hsp5 : m5 !!! Regidx csp_rs1
                     = add_vec_int sp0 (- (8 * Z.of_nat 2))).
      { rewrite /m5 (upd_ne mc2 (Regidx a0_idx) (Regidx csp_rs1) _
                       ltac:(vm_compute; discriminate)).
        exact Hspc. }
      iApply (wp_kecho_strlen_epi h9 m5 sp0 (m !!! Regidx ra_idx)
                (m !!! Regidx s0_idx) n Hsp5 Hal8 Hlo
                with "Hcode Hw8 Hw0 Hrun").
      iIntros (h10 m') "%Hsp' %Hs0' %Hpres Hrun".
      iSpecialize ("Hcont" with "Hs").
      iApply ("Hcont" $! h10 m' with "[] [] Hrun").
      { iPureIntro. intros r Hr.
        assert (Hn1 : Regidx r <> Regidx ra_idx)
          by (apply (Hcs r _ Hr); vm_compute; reflexivity).
        assert (Hn10 : Regidx r <> Regidx a0_idx)
          by (apply (Hcs r _ Hr); vm_compute; reflexivity).
        assert (Hn13 : Regidx r <> Regidx a3_idx)
          by (apply (Hcs r _ Hr); vm_compute; reflexivity).
        assert (Hn14 : Regidx r <> Regidx a4_idx)
          by (apply (Hcs r _ Hr); vm_compute; reflexivity).
        assert (Hn15 : Regidx r <> Regidx a5_idx)
          by (apply (Hcs r _ Hr); vm_compute; reflexivity).
        destruct (decide (Regidx r = Regidx csp_rs1)) as [He2 | Hn2].
        { rewrite He2 Hsp' Hsp. reflexivity. }
        destruct (decide (Regidx r = Regidx s0_idx)) as [He8 | Hn8].
        { rewrite He8. exact Hs0'. }
        rewrite (Hpres r Hn2 Hn8 Hn1).
        rewrite /m5 (upd_ne mc2 (Regidx a0_idx) (Regidx r) _ Hn10).
        rewrite (Hprc r Hn13 Hn14 Hn15).
        rewrite /m4 (upd_ne m3 (Regidx a5_idx) (Regidx r) _ Hn15).
        rewrite /m3 (upd_ne m2 (Regidx a5_idx) (Regidx r) _ Hn15).
        rewrite /m2 (upd_ne m1 (Regidx s0_idx) (Regidx r) _ Hn8).
        exact (upd_ne m (Regidx csp_rs1) (Regidx r) _ Hn2). }
      { iPureIntro.
        rewrite (Hpres a0_idx ltac:(vm_compute; discriminate)
                   ltac:(vm_compute; discriminate)
                   ltac:(vm_compute; discriminate)).
        exact (upd_eq mc2 (Regidx a0_idx)
                 (regval_into_reg
                    (mword_of_int (Z.of_nat (S len')) : mword 64))). }
  Qed.


  (* ===================================================================== *)
  (* THE SYSCALL STUBS.  usys.S's two-instruction bodies: load the number   *)
  (* into a7, [ecall], return.  [exit] never returns, so its arm has no     *)
  (* continuation at all; [write] takes the QUIET row -- SYS_write has no   *)
  (* [usys_window], so the kernel writes no user byte and the heap the      *)
  (* caller owns comes back exactly as it was.                              *)
  (* ===================================================================== *)
  Lemma wp_kecho_exit (h : CpuId) (m : regfile) (avail : nat) :
    echo_code γt -∗
    urun γt γd γs h m (mword_of_int EchoSyms.exit) avail -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros "#Hcode Hrun". iDestruct "Hcode" as CODE.
    destruct echo_syms_pins as (_ & _ & _ & Hexit & _). rewrite Hexit.
    (* ---- 0x332  c.li a7,2 ---- *)
    iApply (wp_uk_cli γt γd γs h m (mword_of_int 0x332)
              (mword_of_int 2 : mword 6) a7_idx avail
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) with "C332 Hrun").
    assert (E332 : add_vec_int (mword_of_int 0x332 : mword 64) 2
                   = mword_of_int 0x334)
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Em : <[Regidx a7_idx
                   := regval_into_reg (sign_extend' 64 (mword_of_int 2 : mword 6)
                                       : mword 64)]> m
                 = <[Regidx a7_idx := (mword_of_int 2 : mword 64)]> m)
      by (f_equal; apply bv_eq; vm_compute; reflexivity).
    rewrite E332 Em.
    iIntros (h1) "Hrun".
    set (m1 := <[Regidx a7_idx := (mword_of_int 2 : mword 64)]> m).
    (* ---- 0x334  ecall -- SYS_exit, the arm with no continuation ---- *)
    iApply (wp_uk_ecall_exit γt γd γs h1 m1 (mword_of_int 0x334) avail
              ltac:(unfold m1, usysno;
                    rewrite (upd_eq m (Regidx a7_idx) (mword_of_int 2 : mword 64));
                    vm_compute; reflexivity)
              with "C334 Hrun").
  Qed.

  Lemma wp_kecho_write (h : CpuId) (m : regfile) (avail : nat) :
    echo_code γt -∗
    urun γt γd γs h m (mword_of_int EchoSyms.write) avail -∗
    (∀ (h' : CpuId) (ret : mword 64),
       urun γt γd γs h'
         (<[Regidx a0_idx := ret]>
            (<[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m))
         (ret_pc (m !!! Regidx ra_idx)) avail -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros "#Hcode Hrun Hcont". iDestruct "Hcode" as CODE.
    destruct echo_syms_pins as (_ & _ & _ & _ & Hwrite). rewrite Hwrite.
    (* ---- 0x352  c.li a7,16 ---- *)
    iApply (wp_uk_cli γt γd γs h m (mword_of_int 0x352)
              (mword_of_int 16 : mword 6) a7_idx avail
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) with "C352 Hrun").
    assert (E352 : add_vec_int (mword_of_int 0x352 : mword 64) 2
                   = mword_of_int 0x354)
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Em : <[Regidx a7_idx
                   := regval_into_reg (sign_extend' 64 (mword_of_int 16 : mword 6)
                                       : mword 64)]> m
                 = <[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m)
      by (f_equal; apply bv_eq; vm_compute; reflexivity).
    rewrite E352 Em.
    iIntros (h1) "Hrun".
    set (m1 := <[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m).
    (* ---- 0x354  ecall -- the QUIET row ---- *)
    iApply (wp_uk_ecall_quiet γt γd γs h1 m1 (mword_of_int 0x354) 16 avail
              ltac:(unfold m1, usysno;
                    rewrite (upd_eq m (Regidx a7_idx)
                               (mword_of_int 16 : mword 64));
                    vm_compute; reflexivity)
              ltac:(discriminate) ltac:(discriminate)
              ltac:(discriminate) ltac:(discriminate) eq_refl
              ltac:(vm_compute; reflexivity)
              with "C354 Hrun").
    assert (E354 : add_vec_int (mword_of_int 0x354 : mword 64) 4
                   = mword_of_int 0x358)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E354.
    iIntros (h2 ret) "Hrun".
    set (m2 := <[Regidx a0_idx := ret]> m1).
    (* ---- 0x358  c.jr ra ---- *)
    assert (Hra : m2 !!! Regidx ra_idx = m !!! Regidx ra_idx).
    { unfold m2, m1.
      exact (eq_trans
               (upd_ne m1 (Regidx a0_idx) (Regidx ra_idx) ret
                  ltac:(vm_compute; discriminate))
               (upd_ne m (Regidx a7_idx) (Regidx ra_idx)
                  (mword_of_int 16 : mword 64)
                  ltac:(vm_compute; discriminate))). }
    iApply (wp_uk_cjr γt γd γs h2 m2 (mword_of_int 0x358) ra_idx
              (ret_pc (m !!! Regidx ra_idx)) avail
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hra; reflexivity)
              with "C358 Hrun").
    iIntros (h3) "Hrun".
    iApply ("Hcont" $! h3 ret with "Hrun").
  Qed.


  (* ===================================================================== *)
  (* main -- the argv walk.                                                 *)
  (*                                                                        *)
  (*   for (i = 1; i < argc; i++) {                                         *)
  (*     write(1, argv[i], strlen(argv[i]));                                *)
  (*     write(1, i + 1 < argc ? " " : "\n", 1);                            *)
  (*   }                                                                    *)
  (*   exit(0);                                                             *)
  (*                                                                        *)
  (* main NEVER RETURNS, so its frame is pushed and never popped and its    *)
  (* contract has no continuation at all.  The eight words it borrows off   *)
  (* the free stack are the eight it spills (ra and s0..s6); the two ON TOP *)
  (* of them are what strlen borrows at every iteration, which is why the   *)
  (* entry [avail] is [8 + (2 + n)].                                        *)
  (* ===================================================================== *)

  (* the exit path at 0x76, reached from three places *)
  Local Lemma wp_kecho_main_exit (h : CpuId) (mc : regfile) (n : nat) :
    echo_code γt -∗
    urun γt γd γs h mc (mword_of_int 0x76) n -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros "#Hcode Hrun". iPoseProof "Hcode" as "#Hc". iDestruct "Hc" as CODE.
    destruct echo_syms_pins as (_ & _ & _ & Hexit & _).
    (* ---- 0x76  c.li a0,0 ---- *)
    iApply (wp_uk_cli γt γd γs h mc (mword_of_int 0x76)
              (mword_of_int 0 : mword 6) a0_idx n
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) with "C76 Hrun").
    assert (E76 : add_vec_int (mword_of_int 0x76 : mword 64) 2
                  = mword_of_int 0x78)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E76. iIntros (h1) "Hrun".
    (* ---- 0x78  jal ra,0x332 <exit> ---- *)
    iApply (wp_uk_jal γt γd γs h1 _ (mword_of_int 0x78)
              (mword_of_int 698 : mword 21) ra_idx
              (mword_of_int EchoSyms.exit) (mword_of_int 0x7c) n
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hexit; apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(rewrite Hexit; vm_compute; reflexivity)
              with "C78 Hrun").
    iIntros (h2) "Hrun".
    iApply (wp_kecho_exit h2 _ n with "Hcode Hrun").
  Qed.

  (* ONE ITERATION'S BODY, 0x4e..0x62:                                      *)
  (*   ld s2,0(s1) ; a0=s2 ; strlen ; a2=a0 ; a1=s2 ; a0=s3 ; write ;       *)
  (*   bne s1,s5,0x3e                                                       *)
  Local Lemma wp_kecho_main_body (av : Z) (args : list uarg) (i : nat)
      (g : uarg) (h : CpuId) (mc : regfile) (n : nat) (tgt : mword 64) :
    args !! i = Some g ->
    0 <= av -> av + 8 * Z.of_nat (length args) <= 2 ^ 38 ->
    mc !!! Regidx s1_idx = mword_of_int (av + 8 * Z.of_nat i) ->
    mc !!! Regidx s3_idx = mword_of_int 1 ->
    mc !!! Regidx s5_idx = mword_of_int (av + 8 * Z.of_nat (length args) - 8) ->
    tgt = (if av + 8 * Z.of_nat i =? av + 8 * Z.of_nat (length args) - 8
           then mword_of_int 0x66 else mword_of_int 0x3e) ->
    echo_code γt -∗
    uargv γd av args -∗
    urun γt γd γs h mc (mword_of_int 0x4e) (2 + n) -∗
    (uargv γd av args -∗
       ∀ (h' : CpuId) (mc' : regfile),
         ⌜ forall r : mword 5, ucallee_saved_idx r = true ->
             Regidx r <> Regidx s2_idx -> mc' !!! Regidx r = mc !!! Regidx r ⌝ -∗
         urun γt γd γs h' mc' tgt (2 + n) -∗
         WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hi Hav0 Hav38 Hs1 Hs3 Hs5 Htgt.
    iIntros "#Hcode Hargv Hrun Hcont".
    iPoseProof "Hcode" as "#Hc". iDestruct "Hc" as CODE.
    destruct echo_syms_pins as (_ & _ & Hstrlen & _ & Hwrite).
    iDestruct (uargv_align with "Hargv") as %[Hal Hargc31].
    change (2 ^ 38) with 274877906944 in Hav38.
    change (2 ^ 31) with 2147483648 in Hargc31.
    assert (Hilt : (i < length args)%nat) by exact (lookup_lt_Some args i g Hi).
    iDestruct (uargv_acc γd av args i g Hi with "Hargv") as "[[Hw Hstr] Hcl]".
    assert (Huai : uint (mword_of_int (av + 8 * Z.of_nat i) : mword 64)
                   = av + 8 * Z.of_nat i)
      by (apply uint_moi; unfold Z64; lia).
    assert (Emod : (av + 8 * Z.of_nat i) mod 8 = 0).
    { replace (av + 8 * Z.of_nat i) with (av + Z.of_nat i * 8) by lia.
      rewrite Z_mod_plus_full. exact Hal. }
    assert (Eoff0 : uoff_i12 (mword_of_int 0 : mword 12) = 0)
      by (vm_compute; reflexivity).
    assert (Eret58 : ret_pc (mword_of_int 0x58 : mword 64) = mword_of_int 0x58)
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Eret62 : ret_pc (mword_of_int 0x62 : mword 64) = mword_of_int 0x62)
      by (apply bv_eq; vm_compute; reflexivity).
    (* ---- 0x4e  ld s2,0(s1) ---- *)
    iApply (wp_uk_ld γt γd γs h mc (mword_of_int 0x4e)
              (mword_of_int 0 : mword 12) s1_idx s2_idx DfracDiscarded
              (av + 8 * Z.of_nat i) (mword_of_int (ua_ptr g)) (2 + n)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(rewrite Hs1 Huai Eoff0; lia)
              Emod
              ltac:(vm_compute; discriminate)
              with "C4e Hw Hrun").
    iIntros "Hw".
    assert (E4e : add_vec_int (mword_of_int 0x4e : mword 64) 4
                  = mword_of_int 0x52)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E4e. iIntros (h1) "Hrun".
    set (m1 := <[Regidx s2_idx
                 := regval_into_reg (mword_of_int (ua_ptr g) : mword 64)]> mc).
    assert (Hs21 : m1 !!! Regidx s2_idx = mword_of_int (ua_ptr g))
      by exact (upd_eq mc (Regidx s2_idx)
                  (regval_into_reg (mword_of_int (ua_ptr g) : mword 64))).
    (* ---- 0x52  c.mv a0,s2 ---- *)
    iApply (wp_uk_cmv γt γd γs h1 m1 (mword_of_int 0x52)
              a0_idx s2_idx (mword_of_int (ua_ptr g)) (2 + n)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs21 moi_add_zero_l; reflexivity)
              with "C52 Hrun").
    assert (E52 : add_vec_int (mword_of_int 0x52 : mword 64) 2
                  = mword_of_int 0x54)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E52. iIntros (h2) "Hrun".
    set (m2 := <[Regidx a0_idx
                 := regval_into_reg (mword_of_int (ua_ptr g) : mword 64)]> m1).
    (* ---- 0x54  jal ra,0xdc <strlen> ---- *)
    iApply (wp_uk_jal γt γd γs h2 m2 (mword_of_int 0x54)
              (mword_of_int 136 : mword 21) ra_idx
              (mword_of_int EchoSyms.strlen) (mword_of_int 0x58) (2 + n)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hstrlen; apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(rewrite Hstrlen; vm_compute; reflexivity)
              with "C54 Hrun").
    iIntros (h3) "Hrun".
    set (m3 := <[Regidx ra_idx
                 := regval_into_reg (mword_of_int 0x58 : mword 64)]> m2).
    assert (Hra3 : m3 !!! Regidx ra_idx = mword_of_int 0x58)
      by exact (upd_eq m2 (Regidx ra_idx)
                  (regval_into_reg (mword_of_int 0x58 : mword 64))).
    assert (Ha03 : m3 !!! Regidx a0_idx = mword_of_int (ua_ptr g)).
    { rewrite /m3 (upd_ne m2 (Regidx ra_idx) (Regidx a0_idx) _
                     ltac:(vm_compute; discriminate)).
      rewrite /m2.
      exact (upd_eq m1 (Regidx a0_idx)
               (regval_into_reg (mword_of_int (ua_ptr g) : mword 64))). }
    (* ---- the call: strlen(argv[i]) ---- *)
    iApply (wp_kecho_strlen h3 m3 DfracDiscarded (ua_ptr g) (ua_len g)
              (ua_bytes g) n Ha03
              with "Hcode Hstr Hrun").
    rewrite Hra3 Eret58.
    iIntros "Hstr" (h4 m4) "%Hcs4 %Ha04 Hrun".
    (* ---- 0x58  c.mv a2,a0 ---- *)
    iApply (wp_uk_cmv γt γd γs h4 m4 (mword_of_int 0x58)
              a2_idx a0_idx (mword_of_int (Z.of_nat (ua_len g))) (2 + n)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha04 moi_add_zero_l; reflexivity)
              with "C58 Hrun").
    assert (E58 : add_vec_int (mword_of_int 0x58 : mword 64) 2
                  = mword_of_int 0x5a)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E58. iIntros (h5) "Hrun".
    set (m5 := <[Regidx a2_idx
                 := regval_into_reg
                      (mword_of_int (Z.of_nat (ua_len g)) : mword 64)]> m4).
    (* ---- 0x5a  c.mv a1,s2 (the buffer; its VALUE is irrelevant to the
           quiet write row, so it is carried unnormalized) ---- *)
    iApply (wp_uk_cmv γt γd γs h5 m5 (mword_of_int 0x5a)
              a1_idx s2_idx (add_vec zero_reg (m5 !!! Regidx s2_idx)) (2 + n)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) eq_refl
              with "C5a Hrun").
    assert (E5a : add_vec_int (mword_of_int 0x5a : mword 64) 2
                  = mword_of_int 0x5c)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E5a. iIntros (h6) "Hrun".
    set (m6 := <[Regidx a1_idx
                 := regval_into_reg
                      (add_vec zero_reg (m5 !!! Regidx s2_idx))]> m5).
    (* ---- 0x5c  c.mv a0,s3 ---- *)
    assert (Hs36 : m6 !!! Regidx s3_idx = mword_of_int 1).
    { rewrite /m6 (upd_ne m5 (Regidx a1_idx) (Regidx s3_idx) _
                     ltac:(vm_compute; discriminate)).
      rewrite /m5 (upd_ne m4 (Regidx a2_idx) (Regidx s3_idx) _
                     ltac:(vm_compute; discriminate)).
      rewrite (Hcs4 s3_idx ltac:(vm_compute; reflexivity)).
      rewrite /m3 (upd_ne m2 (Regidx ra_idx) (Regidx s3_idx) _
                     ltac:(vm_compute; discriminate)).
      rewrite /m2 (upd_ne m1 (Regidx a0_idx) (Regidx s3_idx) _
                     ltac:(vm_compute; discriminate)).
      rewrite /m1 (upd_ne mc (Regidx s2_idx) (Regidx s3_idx) _
                     ltac:(vm_compute; discriminate)).
      exact Hs3. }
    iApply (wp_uk_cmv γt γd γs h6 m6 (mword_of_int 0x5c)
              a0_idx s3_idx (mword_of_int 1) (2 + n)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs36 moi_add_zero_l; reflexivity)
              with "C5c Hrun").
    assert (E5c : add_vec_int (mword_of_int 0x5c : mword 64) 2
                  = mword_of_int 0x5e)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E5c. iIntros (h7) "Hrun".
    set (m7 := <[Regidx a0_idx
                 := regval_into_reg (mword_of_int 1 : mword 64)]> m6).
    (* ---- 0x5e  jal ra,0x352 <write> ---- *)
    iApply (wp_uk_jal γt γd γs h7 m7 (mword_of_int 0x5e)
              (mword_of_int 756 : mword 21) ra_idx
              (mword_of_int EchoSyms.write) (mword_of_int 0x62) (2 + n)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hwrite; apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(rewrite Hwrite; vm_compute; reflexivity)
              with "C5e Hrun").
    iIntros (h8) "Hrun".
    set (m8 := <[Regidx ra_idx
                 := regval_into_reg (mword_of_int 0x62 : mword 64)]> m7).
    assert (Hra8 : m8 !!! Regidx ra_idx = mword_of_int 0x62)
      by exact (upd_eq m7 (Regidx ra_idx)
                  (regval_into_reg (mword_of_int 0x62 : mword 64))).
    (* ---- the call: write(1, argv[i], len) ---- *)
    iApply (wp_kecho_write h8 m8 (2 + n) with "Hcode Hrun").
    rewrite Hra8 Eret62.
    iIntros (h9 ret) "Hrun".
    set (m9 := <[Regidx a0_idx := ret]>
                 (<[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m8)).
    (* every callee-saved register but s2 is where it was at 0x4e *)
    assert (Hpres9 : forall r : mword 5, ucallee_saved_idx r = true ->
              Regidx r <> Regidx s2_idx -> m9 !!! Regidx r = mc !!! Regidx r).
    { intros r Hr Hn2.
      assert (Hn1  : Regidx r <> Regidx ra_idx)
        by (apply (ucs_ne r _ Hr); vm_compute; reflexivity).
      assert (Hn10 : Regidx r <> Regidx a0_idx)
        by (apply (ucs_ne r _ Hr); vm_compute; reflexivity).
      assert (Hn11 : Regidx r <> Regidx a1_idx)
        by (apply (ucs_ne r _ Hr); vm_compute; reflexivity).
      assert (Hn12 : Regidx r <> Regidx a2_idx)
        by (apply (ucs_ne r _ Hr); vm_compute; reflexivity).
      assert (Hn17 : Regidx r <> Regidx a7_idx)
        by (apply (ucs_ne r _ Hr); vm_compute; reflexivity).
      rewrite /m9 (upd_ne _ (Regidx a0_idx) (Regidx r) _ Hn10).
      rewrite (upd_ne _ (Regidx a7_idx) (Regidx r) _ Hn17).
      rewrite /m8 (upd_ne m7 (Regidx ra_idx) (Regidx r) _ Hn1).
      rewrite /m7 (upd_ne m6 (Regidx a0_idx) (Regidx r) _ Hn10).
      rewrite /m6 (upd_ne m5 (Regidx a1_idx) (Regidx r) _ Hn11).
      rewrite /m5 (upd_ne m4 (Regidx a2_idx) (Regidx r) _ Hn12).
      rewrite (Hcs4 r Hr).
      rewrite /m3 (upd_ne m2 (Regidx ra_idx) (Regidx r) _ Hn1).
      rewrite /m2 (upd_ne m1 (Regidx a0_idx) (Regidx r) _ Hn10).
      rewrite /m1. exact (upd_ne mc (Regidx s2_idx) (Regidx r) _ Hn2). }
    (* ---- 0x62  bne s1,s5,0x3e ---- *)
    assert (Hs19 : m9 !!! Regidx s1_idx = mword_of_int (av + 8 * Z.of_nat i)).
    { rewrite (Hpres9 s1_idx ltac:(vm_compute; reflexivity)
                 ltac:(vm_compute; discriminate)). exact Hs1. }
    assert (Hs59 : m9 !!! Regidx s5_idx
                   = mword_of_int (av + 8 * Z.of_nat (length args) - 8)).
    { rewrite (Hpres9 s5_idx ltac:(vm_compute; reflexivity)
                 ltac:(vm_compute; discriminate)). exact Hs5. }
    assert (Hbt : negb (av + 8 * Z.of_nat i
                        =? av + 8 * Z.of_nat (length args) - 8)
                  = uv_btaken BNE (m9 !!! Regidx s1_idx) (m9 !!! Regidx s5_idx)).
    { rewrite Hs19 Hs59. symmetry.
      exact (moi_neq_vec (av + 8 * Z.of_nat i)
               (av + 8 * Z.of_nat (length args) - 8)
               ltac:(unfold Z64; lia) ltac:(unfold Z64; lia)). }
    iApply (wp_uk_btype γt γd γs h9 m9 (mword_of_int 0x62)
              (mword_of_int 8156 : mword 13) s5_idx s1_idx BNE
              (negb (av + 8 * Z.of_nat i
                     =? av + 8 * Z.of_nat (length args) - 8))
              (mword_of_int 0x3e) (2 + n)
              Hbt
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(intros _; vm_compute; reflexivity)
              with "C62 Hrun").
    iIntros (h10) "Hrun".
    iDestruct ("Hcl" with "[$Hw $Hstr]") as "Hargv".
    iSpecialize ("Hcont" with "Hargv").
    iApply ("Hcont" $! h10 m9 with "[] [Hrun]").
    { iPureIntro. exact Hpres9. }
    replace (if negb (av + 8 * Z.of_nat i
                      =? av + 8 * Z.of_nat (length args) - 8)
             then (mword_of_int 0x3e : mword 64)
             else add_vec_int (mword_of_int 0x62 : mword 64) 4)
      with tgt.
    { iExact "Hrun". }
    rewrite Htgt.
    destruct (av + 8 * Z.of_nat i =? av + 8 * Z.of_nat (length args) - 8);
      simpl; [ apply bv_eq; vm_compute; reflexivity | reflexivity ].
  Qed.

  (* THE SEPARATOR AND THE ADVANCE, 0x3e..0x4a:                             *)
  (*   a2=s3 ; a1=s6 ; a0=s3 ; write(1," ",1) ; s1+=8 ; beq s1,s4,0x76      *)
  (* The [beq] cannot fire here: it tests for [&argv[argc]], and this arm    *)
  (* is only reached with one more element still to print.                   *)
  Local Lemma wp_kecho_main_sep (av : Z) (args : list uarg) (i : nat)
      (h : CpuId) (mc : regfile) (n : nat) :
    0 <= av -> av + 8 * Z.of_nat (length args) <= 2 ^ 38 ->
    (i + 1 < length args)%nat ->
    mc !!! Regidx s1_idx = mword_of_int (av + 8 * Z.of_nat i) ->
    mc !!! Regidx s3_idx = mword_of_int 1 ->
    mc !!! Regidx s4_idx = mword_of_int (av + 8 * Z.of_nat (length args)) ->
    echo_code γt -∗
    urun γt γd γs h mc (mword_of_int 0x3e) (2 + n) -∗
    (∀ (h' : CpuId) (mc' : regfile),
       ⌜ mc' !!! Regidx s1_idx = mword_of_int (av + 8 * Z.of_nat (i + 1)) ⌝ -∗
       ⌜ forall r : mword 5, ucallee_saved_idx r = true ->
           Regidx r <> Regidx s1_idx -> mc' !!! Regidx r = mc !!! Regidx r ⌝ -∗
       urun γt γd γs h' mc' (mword_of_int 0x4e) (2 + n) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hav0 Hav38 Hi1 Hs1 Hs3 Hs4. iIntros "#Hcode Hrun Hcont".
    iPoseProof "Hcode" as "#Hc". iDestruct "Hc" as CODE.
    destruct echo_syms_pins as (_ & _ & _ & _ & Hwrite).
    change (2 ^ 38) with 274877906944 in Hav38.
    assert (Eret48 : ret_pc (mword_of_int 0x48 : mword 64) = mword_of_int 0x48)
      by (apply bv_eq; vm_compute; reflexivity).
    (* ---- 0x3e  c.mv a2,s3 ---- *)
    iApply (wp_uk_cmv γt γd γs h mc (mword_of_int 0x3e)
              a2_idx s3_idx (mword_of_int 1) (2 + n)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs3 moi_add_zero_l; reflexivity)
              with "C3e Hrun").
    assert (E3e : add_vec_int (mword_of_int 0x3e : mword 64) 2
                  = mword_of_int 0x40)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E3e. iIntros (h1) "Hrun".
    set (m1 := <[Regidx a2_idx
                 := regval_into_reg (mword_of_int 1 : mword 64)]> mc).
    (* ---- 0x40  c.mv a1,s6 ---- *)
    iApply (wp_uk_cmv γt γd γs h1 m1 (mword_of_int 0x40)
              a1_idx s6_idx (add_vec zero_reg (m1 !!! Regidx s6_idx)) (2 + n)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) eq_refl
              with "C40 Hrun").
    assert (E40 : add_vec_int (mword_of_int 0x40 : mword 64) 2
                  = mword_of_int 0x42)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E40. iIntros (h2) "Hrun".
    set (m2 := <[Regidx a1_idx
                 := regval_into_reg
                      (add_vec zero_reg (m1 !!! Regidx s6_idx))]> m1).
    (* ---- 0x42  c.mv a0,s3 ---- *)
    assert (Hs32 : m2 !!! Regidx s3_idx = mword_of_int 1).
    { rewrite /m2 (upd_ne m1 (Regidx a1_idx) (Regidx s3_idx) _
                     ltac:(vm_compute; discriminate)).
      rewrite /m1 (upd_ne mc (Regidx a2_idx) (Regidx s3_idx) _
                     ltac:(vm_compute; discriminate)).
      exact Hs3. }
    iApply (wp_uk_cmv γt γd γs h2 m2 (mword_of_int 0x42)
              a0_idx s3_idx (mword_of_int 1) (2 + n)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs32 moi_add_zero_l; reflexivity)
              with "C42 Hrun").
    assert (E42 : add_vec_int (mword_of_int 0x42 : mword 64) 2
                  = mword_of_int 0x44)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E42. iIntros (h3) "Hrun".
    set (m3 := <[Regidx a0_idx
                 := regval_into_reg (mword_of_int 1 : mword 64)]> m2).
    (* ---- 0x44  jal ra,0x352 <write> ---- *)
    iApply (wp_uk_jal γt γd γs h3 m3 (mword_of_int 0x44)
              (mword_of_int 782 : mword 21) ra_idx
              (mword_of_int EchoSyms.write) (mword_of_int 0x48) (2 + n)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hwrite; apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(rewrite Hwrite; vm_compute; reflexivity)
              with "C44 Hrun").
    iIntros (h4) "Hrun".
    set (m4 := <[Regidx ra_idx
                 := regval_into_reg (mword_of_int 0x48 : mword 64)]> m3).
    assert (Hra4 : m4 !!! Regidx ra_idx = mword_of_int 0x48)
      by exact (upd_eq m3 (Regidx ra_idx)
                  (regval_into_reg (mword_of_int 0x48 : mword 64))).
    iApply (wp_kecho_write h4 m4 (2 + n) with "Hcode Hrun").
    rewrite Hra4 Eret48.
    iIntros (h5 ret) "Hrun".
    set (m5 := <[Regidx a0_idx := ret]>
                 (<[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m4)).
    assert (Hpres5 : forall r : mword 5, ucallee_saved_idx r = true ->
              m5 !!! Regidx r = mc !!! Regidx r).
    { intros r Hr.
      assert (Hn1  : Regidx r <> Regidx ra_idx)
        by (apply (ucs_ne r _ Hr); vm_compute; reflexivity).
      assert (Hn10 : Regidx r <> Regidx a0_idx)
        by (apply (ucs_ne r _ Hr); vm_compute; reflexivity).
      assert (Hn11 : Regidx r <> Regidx a1_idx)
        by (apply (ucs_ne r _ Hr); vm_compute; reflexivity).
      assert (Hn12 : Regidx r <> Regidx a2_idx)
        by (apply (ucs_ne r _ Hr); vm_compute; reflexivity).
      assert (Hn17 : Regidx r <> Regidx a7_idx)
        by (apply (ucs_ne r _ Hr); vm_compute; reflexivity).
      rewrite /m5 (upd_ne _ (Regidx a0_idx) (Regidx r) _ Hn10).
      rewrite (upd_ne _ (Regidx a7_idx) (Regidx r) _ Hn17).
      rewrite /m4 (upd_ne m3 (Regidx ra_idx) (Regidx r) _ Hn1).
      rewrite /m3 (upd_ne m2 (Regidx a0_idx) (Regidx r) _ Hn10).
      rewrite /m2 (upd_ne m1 (Regidx a1_idx) (Regidx r) _ Hn11).
      rewrite /m1. exact (upd_ne mc (Regidx a2_idx) (Regidx r) _ Hn12). }
    (* ---- 0x48  c.addi s1,s1,8 ---- *)
    assert (Hs15 : m5 !!! Regidx s1_idx = mword_of_int (av + 8 * Z.of_nat i)).
    { rewrite (Hpres5 s1_idx ltac:(vm_compute; reflexivity)). exact Hs1. }
    assert (E8 : (sign_extend' 64 (mword_of_int 8 : mword 6) : mword 64)
                 = mword_of_int 8)
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uk_caddi γt γd γs h5 m5 (mword_of_int 0x48)
              (mword_of_int 8 : mword 6) s1_idx
              (mword_of_int (av + 8 * Z.of_nat (i + 1))) (2 + n)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs15 E8 moi_add; f_equal; lia)
              with "C48 Hrun").
    assert (E48 : add_vec_int (mword_of_int 0x48 : mword 64) 2
                  = mword_of_int 0x4a)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E48. iIntros (h6) "Hrun".
    set (m6 := <[Regidx s1_idx
                 := regval_into_reg
                      (mword_of_int (av + 8 * Z.of_nat (i + 1))
                       : mword 64)]> m5).
    assert (Hs16 : m6 !!! Regidx s1_idx
                   = mword_of_int (av + 8 * Z.of_nat (i + 1)))
      by exact (upd_eq m5 (Regidx s1_idx)
                  (regval_into_reg
                     (mword_of_int (av + 8 * Z.of_nat (i + 1)) : mword 64))).
    assert (Hs46 : m6 !!! Regidx s4_idx
                   = mword_of_int (av + 8 * Z.of_nat (length args))).
    { rewrite /m6 (upd_ne m5 (Regidx s1_idx) (Regidx s4_idx) _
                     ltac:(vm_compute; discriminate)).
      rewrite (Hpres5 s4_idx ltac:(vm_compute; reflexivity)). exact Hs4. }
    (* ---- 0x4a  beq s1,s4,0x76 -- NOT taken ---- *)
    assert (Hbt : false
                  = uv_btaken BEQ (m6 !!! Regidx s1_idx) (m6 !!! Regidx s4_idx)).
    { rewrite Hs16 Hs46. symmetry.
      etransitivity;
        [ exact (moi_eq_vec (av + 8 * Z.of_nat (i + 1))
                   (av + 8 * Z.of_nat (length args))
                   ltac:(unfold Z64; lia) ltac:(unfold Z64; lia)) | ].
      apply Z.eqb_neq. lia. }
    iApply (wp_uk_btype γt γd γs h6 m6 (mword_of_int 0x4a)
              (mword_of_int 44 : mword 13) s4_idx s1_idx BEQ
              false (mword_of_int 0x76) (2 + n)
              Hbt
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(discriminate)
              with "C4a Hrun").
    assert (E4a : add_vec_int (mword_of_int 0x4a : mword 64) 4
                  = mword_of_int 0x4e)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E4a.
    iIntros (h7) "Hrun".
    iApply ("Hcont" $! h7 m6 with "[] [] Hrun").
    { iPureIntro. exact Hs16. }
    { iPureIntro. intros r Hr Hn9.
      rewrite /m6 (upd_ne m5 (Regidx s1_idx) (Regidx r) _ Hn9).
      exact (Hpres5 r Hr). }
  Qed.


  (* THE SCAN OVER argv, from 0x4e.  [k] counts the elements still to print  *)
  (* after this one; the induction is on it.  Every iteration hands the      *)
  (* vector back untouched, so the resource is threaded rather than split.   *)
  Local Lemma wp_kecho_main_loop (av : Z) (args : list uarg) :
    forall (k i : nat) (h : CpuId) (mc : regfile) (n : nat),
    (length args = 1 + i + k)%nat ->
    0 <= av -> av + 8 * Z.of_nat (length args) <= 2 ^ 38 ->
    mc !!! Regidx s1_idx = mword_of_int (av + 8 * Z.of_nat i) ->
    mc !!! Regidx s3_idx = mword_of_int 1 ->
    mc !!! Regidx s4_idx = mword_of_int (av + 8 * Z.of_nat (length args)) ->
    mc !!! Regidx s5_idx = mword_of_int (av + 8 * Z.of_nat (length args) - 8) ->
    echo_code γt -∗
    uargv γd av args -∗
    urun γt γd γs h mc (mword_of_int 0x4e) (2 + n) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros k. induction k as [| k IH ];
      intros i h mc n Hlen Hav0 Hav38 Hs1 Hs3 Hs4 Hs5;
      iIntros "#Hcode Hargv Hrun";
      iPoseProof "Hcode" as "#Hc"; iDestruct "Hc" as CODE;
      destruct (lookup_lt_is_Some_2 args i ltac:(lia)) as [g Hg];
      destruct echo_syms_pins as (_ & _ & _ & _ & Hwrite).
    - (* the LAST element: print it, then the newline, then exit *)
      iApply (wp_kecho_main_body av args i g h mc n (mword_of_int 0x66)
                Hg Hav0 Hav38 Hs1 Hs3 Hs5
                ltac:(replace (av + 8 * Z.of_nat i
                               =? av + 8 * Z.of_nat (length args) - 8)
                        with true by (symmetry; apply Z.eqb_eq; lia);
                      reflexivity)
                with "Hcode Hargv Hrun").
      iIntros "Hargv" (h1 mc1) "%Hpres1 Hrun".
      (* ---- 0x66  c.li a2,1 ---- *)
      iApply (wp_uk_cli γt γd γs h1 mc1 (mword_of_int 0x66)
                (mword_of_int 1 : mword 6) a2_idx (2 + n)
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate) with "C66 Hrun").
      assert (E66 : add_vec_int (mword_of_int 0x66 : mword 64) 2
                    = mword_of_int 0x68)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite E66. iIntros (h2) "Hrun".
      set (n1 := <[Regidx a2_idx
                   := regval_into_reg
                        (sign_extend' 64 (mword_of_int 1 : mword 6)
                         : mword 64)]> mc1).
      (* ---- 0x68  auipc a1,0x1  (the pointer's VALUE never matters: the
             quiet write row reads no user byte) ---- *)
      iApply (wp_uk_auipc γt γd γs h2 n1 (mword_of_int 0x68)
                (mword_of_int 1 : mword 20) a1_idx
                (add_vec (mword_of_int 0x68 : mword 64)
                   (auipc_off (mword_of_int 1 : mword 20))) (2 + n)
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate) eq_refl
                with "C68 Hrun").
      assert (E68 : add_vec_int (mword_of_int 0x68 : mword 64) 4
                    = mword_of_int 0x6c)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite E68. iIntros (h3) "Hrun".
      set (n2 := <[Regidx a1_idx
                   := regval_into_reg
                        (add_vec (mword_of_int 0x68 : mword 64)
                           (auipc_off (mword_of_int 1 : mword 20)))]> n1).
      (* ---- 0x6c  addi a1,a1,2256 ---- *)
      iApply (wp_uk_addi γt γd γs h3 n2 (mword_of_int 0x6c)
                (mword_of_int 2256 : mword 12) a1_idx a1_idx
                (add_vec (n2 !!! Regidx a1_idx)
                   (sign_extend' 64 (mword_of_int 2256 : mword 12))) (2 + n)
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate) eq_refl
                with "C6c Hrun").
      assert (E6c : add_vec_int (mword_of_int 0x6c : mword 64) 4
                    = mword_of_int 0x70)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite E6c. iIntros (h4) "Hrun".
      set (n3 := <[Regidx a1_idx
                   := regval_into_reg
                        (add_vec (n2 !!! Regidx a1_idx)
                           (sign_extend' 64
                              (mword_of_int 2256 : mword 12)))]> n2).
      (* ---- 0x70  c.mv a0,a2 ---- *)
      iApply (wp_uk_cmv γt γd γs h4 n3 (mword_of_int 0x70)
                a0_idx a2_idx (add_vec zero_reg (n3 !!! Regidx a2_idx)) (2 + n)
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate) eq_refl
                with "C70 Hrun").
      assert (E70 : add_vec_int (mword_of_int 0x70 : mword 64) 2
                    = mword_of_int 0x72)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite E70. iIntros (h5) "Hrun".
      set (n4 := <[Regidx a0_idx
                   := regval_into_reg
                        (add_vec zero_reg (n3 !!! Regidx a2_idx))]> n3).
      (* ---- 0x72  jal ra,0x352 <write> ---- *)
      iApply (wp_uk_jal γt γd γs h5 n4 (mword_of_int 0x72)
                (mword_of_int 736 : mword 21) ra_idx
                (mword_of_int EchoSyms.write) (mword_of_int 0x76) (2 + n)
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite Hwrite; apply bv_eq; vm_compute; reflexivity)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(rewrite Hwrite; vm_compute; reflexivity)
                with "C72 Hrun").
      iIntros (h6) "Hrun".
      set (n5 := <[Regidx ra_idx
                   := regval_into_reg (mword_of_int 0x76 : mword 64)]> n4).
      assert (Hra5 : n5 !!! Regidx ra_idx = mword_of_int 0x76)
        by exact (upd_eq n4 (Regidx ra_idx)
                    (regval_into_reg (mword_of_int 0x76 : mword 64))).
      iApply (wp_kecho_write h6 n5 (2 + n) with "Hcode Hrun").
      rewrite Hra5.
      assert (Eret76 : ret_pc (mword_of_int 0x76 : mword 64)
                       = mword_of_int 0x76)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite Eret76.
      iIntros (h7 ret) "Hrun".
      (* ---- 0x76 onwards: exit(0) ---- *)
      iApply (wp_kecho_main_exit h7 _ (2 + n) with "Hcode Hrun").
    - (* NOT the last: print it, then a separator, then go round again *)
      iApply (wp_kecho_main_body av args i g h mc n (mword_of_int 0x3e)
                Hg Hav0 Hav38 Hs1 Hs3 Hs5
                ltac:(replace (av + 8 * Z.of_nat i
                               =? av + 8 * Z.of_nat (length args) - 8)
                        with false by (symmetry; apply Z.eqb_neq; lia);
                      reflexivity)
                with "Hcode Hargv Hrun").
      iIntros "Hargv" (h1 mc1) "%Hpres1 Hrun".
      iApply (wp_kecho_main_sep av args i h1 mc1 n Hav0 Hav38 ltac:(lia)
                ltac:(rewrite (Hpres1 s1_idx ltac:(vm_compute; reflexivity)
                                 ltac:(vm_compute; discriminate)); exact Hs1)
                ltac:(rewrite (Hpres1 s3_idx ltac:(vm_compute; reflexivity)
                                 ltac:(vm_compute; discriminate)); exact Hs3)
                ltac:(rewrite (Hpres1 s4_idx ltac:(vm_compute; reflexivity)
                                 ltac:(vm_compute; discriminate)); exact Hs4)
                with "Hcode Hrun").
      iIntros (h2 mc2) "%Hs12 %Hpres2 Hrun".
      iApply (IH (i + 1)%nat h2 mc2 n ltac:(lia) Hav0 Hav38 Hs12
                ltac:(rewrite (Hpres2 s3_idx ltac:(vm_compute; reflexivity)
                                 ltac:(vm_compute; discriminate));
                      rewrite (Hpres1 s3_idx ltac:(vm_compute; reflexivity)
                                 ltac:(vm_compute; discriminate)); exact Hs3)
                ltac:(rewrite (Hpres2 s4_idx ltac:(vm_compute; reflexivity)
                                 ltac:(vm_compute; discriminate));
                      rewrite (Hpres1 s4_idx ltac:(vm_compute; reflexivity)
                                 ltac:(vm_compute; discriminate)); exact Hs4)
                ltac:(rewrite (Hpres2 s5_idx ltac:(vm_compute; reflexivity)
                                 ltac:(vm_compute; discriminate));
                      rewrite (Hpres1 s5_idx ltac:(vm_compute; reflexivity)
                                 ltac:(vm_compute; discriminate)); exact Hs5)
                with "Hcode Hargv Hrun").
  Qed.

  (* ===================================================================== *)
  (* main.                                                                  *)
  (* ===================================================================== *)
  Lemma wp_kecho_main (h : CpuId) (m : regfile) (av : Z) (args : list uarg)
      (n : nat) :
    m !!! Regidx a0_idx = mword_of_int (Z.of_nat (length args)) ->
    m !!! Regidx a1_idx = mword_of_int av ->
    echo_code γt -∗
    uargv γd av args -∗
    urun γt γd γs h m (mword_of_int EchoSyms.main) (8 + (2 + n)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Ha0 Ha1. iIntros "#Hcode Hargv Hrun".
    iPoseProof "Hcode" as "#Hc". iDestruct "Hc" as CODE.
    destruct echo_syms_pins as (Hmain & _ & _ & _ & _). rewrite Hmain.
    iDestruct (urun_stack with "Hrun") as %[Hal8' Hroom].
    iDestruct (uargv_align with "Hargv") as %[Hal Hargc31].
    change (2 ^ 31) with 2147483648 in Hargc31.
    remember (m !!! Regidx csp_rs1) as sp0 eqn:Hsp0.
    assert (Hsp : m !!! Regidx csp_rs1 = sp0) by (symmetry; exact Hsp0).
    clear Hsp0.
    assert (Hal8 : uint sp0 mod 8 = 0) by exact Hal8'.
    assert (Hlo : 64 <= uint sp0) by lia.
    assert (Hbsp : bv_unsigned (add_vec_int sp0 (- (8 * Z.of_nat 8)))
                   = bv_unsigned sp0 - 64).
    { replace (- (8 * Z.of_nat 8)) with (-64) by lia.
      exact (uv_avi_neg sp0 64 ltac:(lia) ltac:(rewrite <- uint_unsigned; lia)). }
    assert (Hsp64 : uint (add_vec_int sp0 (- (8 * Z.of_nat 8)))
                    = uint sp0 - 64)
      by (rewrite !uint_unsigned; exact Hbsp).
    assert (Ho0 : uoff_sdsp (mword_of_int 0 : mword 6) = 0)
      by (vm_compute; reflexivity).
    assert (Ho1 : uoff_sdsp (mword_of_int 1 : mword 6) = 8)
      by (vm_compute; reflexivity).
    assert (Ho2 : uoff_sdsp (mword_of_int 2 : mword 6) = 16)
      by (vm_compute; reflexivity).
    assert (Ho3 : uoff_sdsp (mword_of_int 3 : mword 6) = 24)
      by (vm_compute; reflexivity).
    assert (Ho4 : uoff_sdsp (mword_of_int 4 : mword 6) = 32)
      by (vm_compute; reflexivity).
    assert (Ho5 : uoff_sdsp (mword_of_int 5 : mword 6) = 40)
      by (vm_compute; reflexivity).
    assert (Ho6 : uoff_sdsp (mword_of_int 6 : mword 6) = 48)
      by (vm_compute; reflexivity).
    assert (Ho7 : uoff_sdsp (mword_of_int 7 : mword 6) = 56)
      by (vm_compute; reflexivity).
    (* ---- 0x0  c.addi16sp sp,sp,-64 -- THE PUSH ---- *)
    iApply (wp_uk_caddi16sp_dn γt γd γs h m (mword_of_int 0x0)
              (mword_of_int 60 : mword 6) 8 (2 + n)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "C00 Hrun").
    assert (E00 : add_vec_int (mword_of_int 0x0 : mword 64) 2
                  = mword_of_int 0x2)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Hsp ustack_8 E00.
    iIntros "(_ & [%v1 Hw1] & [%v2 Hw2] & [%v3 Hw3] & [%v4 Hw4]
              & [%v5 Hw5] & [%v6 Hw6] & [%v7 Hw7] & [%v8 Hw8])".
    iIntros (hs0) "Hrun".
    set (mA := <[Regidx csp_rs1
                 := regval_into_reg (add_vec_int sp0 (- (8 * Z.of_nat 8)))]> m).
    assert (HspA : mA !!! Regidx csp_rs1
                   = add_vec_int sp0 (- (8 * Z.of_nat 8)))
      by exact (upd_eq m (Regidx csp_rs1)
                  (regval_into_reg (add_vec_int sp0 (- (8 * Z.of_nat 8))))).
    (* ---- 0x2  c.sdsp ra,56(sp) ---- *)
    iApply (wp_uk_csdsp γt γd γs hs0 mA (mword_of_int 0x2)
              (mword_of_int 7 : mword 6) ra_idx (uint sp0 - 8) v1 (2 + n)
              ltac:(rewrite HspA Hsp64 Ho7; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              with "C02 Hw1 Hrun").
    iIntros "Hw1".
    assert (Es0 : add_vec_int (mword_of_int 0x2 : mword 64) 2
                   = mword_of_int 0x4)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Es0. iIntros (hs1) "Hrun".
    (* ---- 0x4  c.sdsp s0,48(sp) ---- *)
    iApply (wp_uk_csdsp γt γd γs hs1 mA (mword_of_int 0x4)
              (mword_of_int 6 : mword 6) s0_idx (uint sp0 - 16) v2 (2 + n)
              ltac:(rewrite HspA Hsp64 Ho6; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              with "C04 Hw2 Hrun").
    iIntros "Hw2".
    assert (Es1 : add_vec_int (mword_of_int 0x4 : mword 64) 2
                   = mword_of_int 0x6)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Es1. iIntros (hs2) "Hrun".
    (* ---- 0x6  c.sdsp s1,40(sp) ---- *)
    iApply (wp_uk_csdsp γt γd γs hs2 mA (mword_of_int 0x6)
              (mword_of_int 5 : mword 6) s1_idx (uint sp0 - 24) v3 (2 + n)
              ltac:(rewrite HspA Hsp64 Ho5; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              with "C06 Hw3 Hrun").
    iIntros "Hw3".
    assert (Es2 : add_vec_int (mword_of_int 0x6 : mword 64) 2
                   = mword_of_int 0x8)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Es2. iIntros (hs3) "Hrun".
    (* ---- 0x8  c.sdsp s2,32(sp) ---- *)
    iApply (wp_uk_csdsp γt γd γs hs3 mA (mword_of_int 0x8)
              (mword_of_int 4 : mword 6) s2_idx (uint sp0 - 32) v4 (2 + n)
              ltac:(rewrite HspA Hsp64 Ho4; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              with "C08 Hw4 Hrun").
    iIntros "Hw4".
    assert (Es3 : add_vec_int (mword_of_int 0x8 : mword 64) 2
                   = mword_of_int 0xa)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Es3. iIntros (hs4) "Hrun".
    (* ---- 0xa  c.sdsp s3,24(sp) ---- *)
    iApply (wp_uk_csdsp γt γd γs hs4 mA (mword_of_int 0xa)
              (mword_of_int 3 : mword 6) s3_idx (uint sp0 - 40) v5 (2 + n)
              ltac:(rewrite HspA Hsp64 Ho3; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              with "C0a Hw5 Hrun").
    iIntros "Hw5".
    assert (Es4 : add_vec_int (mword_of_int 0xa : mword 64) 2
                   = mword_of_int 0xc)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Es4. iIntros (hs5) "Hrun".
    (* ---- 0xc  c.sdsp s4,16(sp) ---- *)
    iApply (wp_uk_csdsp γt γd γs hs5 mA (mword_of_int 0xc)
              (mword_of_int 2 : mword 6) s4_idx (uint sp0 - 48) v6 (2 + n)
              ltac:(rewrite HspA Hsp64 Ho2; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              with "C0c Hw6 Hrun").
    iIntros "Hw6".
    assert (Es5 : add_vec_int (mword_of_int 0xc : mword 64) 2
                   = mword_of_int 0xe)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Es5. iIntros (hs6) "Hrun".
    (* ---- 0xe  c.sdsp s5,8(sp) ---- *)
    iApply (wp_uk_csdsp γt γd γs hs6 mA (mword_of_int 0xe)
              (mword_of_int 1 : mword 6) s5_idx (uint sp0 - 56) v7 (2 + n)
              ltac:(rewrite HspA Hsp64 Ho1; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              with "C0e Hw7 Hrun").
    iIntros "Hw7".
    assert (Es6 : add_vec_int (mword_of_int 0xe : mword 64) 2
                   = mword_of_int 0x10)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Es6. iIntros (hs7) "Hrun".
    (* ---- 0x10  c.sdsp s6,0(sp) ---- *)
    iApply (wp_uk_csdsp γt γd γs hs7 mA (mword_of_int 0x10)
              (mword_of_int 0 : mword 6) s6_idx (uint sp0 - 64) v8 (2 + n)
              ltac:(rewrite HspA Hsp64 Ho0; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              with "C10 Hw8 Hrun").
    iIntros "Hw8".
    assert (Es7 : add_vec_int (mword_of_int 0x10 : mword 64) 2
                   = mword_of_int 0x12)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Es7. iIntros (hs8) "Hrun".
    (* ---- 0x12  c.addi4spn s0,sp,64 (s0 is dead: main never returns) ---- *)
    iApply (wp_uk_caddi4spn γt γd γs hs8 mA (mword_of_int 0x12)
              (mword_of_int 0 : mword 3) (mword_of_int 16 : mword 8) s0_idx
              (add_vec (mA !!! Regidx csp_rs1)
                 (sign_extend' 64
                    (caddi4spn_imm (mword_of_int 16 : mword 8)))) (2 + n)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
              eq_refl
              with "C12 Hrun").
    assert (E12 : add_vec_int (mword_of_int 0x12 : mword 64) 2
                  = mword_of_int 0x14)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E12. iIntros (hb) "Hrun".
    set (mB := <[Regidx s0_idx
                 := regval_into_reg
                      (add_vec (mA !!! Regidx csp_rs1)
                         (sign_extend' 64
                            (caddi4spn_imm (mword_of_int 16 : mword 8))))]> mA).
    (* ---- 0x14  c.li a5,1 ---- *)
    iApply (wp_uk_cli γt γd γs hb mB (mword_of_int 0x14)
              (mword_of_int 1 : mword 6) a5_idx (2 + n)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) with "C14 Hrun").
    assert (E14 : add_vec_int (mword_of_int 0x14 : mword 64) 2
                  = mword_of_int 0x16)
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Eli1 : <[Regidx a5_idx
                     := regval_into_reg
                          (sign_extend' 64 (mword_of_int 1 : mword 6)
                           : mword 64)]> mB
                   = <[Regidx a5_idx := (mword_of_int 1 : mword 64)]> mB)
      by (f_equal; apply bv_eq; vm_compute; reflexivity).
    rewrite E14 Eli1. iIntros (hc) "Hrun".
    set (mC := <[Regidx a5_idx := (mword_of_int 1 : mword 64)]> mB).
    assert (Ha5C : mC !!! Regidx a5_idx = mword_of_int 1)
      by exact (upd_eq mB (Regidx a5_idx) (mword_of_int 1 : mword 64)).
    assert (Ha0C : mC !!! Regidx a0_idx
                   = mword_of_int (Z.of_nat (length args))).
    { rewrite /mC (upd_ne mB (Regidx a5_idx) (Regidx a0_idx) _
                     ltac:(vm_compute; discriminate)).
      rewrite /mB (upd_ne mA (Regidx s0_idx) (Regidx a0_idx) _
                     ltac:(vm_compute; discriminate)).
      rewrite /mA (upd_ne m (Regidx csp_rs1) (Regidx a0_idx) _
                     ltac:(vm_compute; discriminate)).
      exact Ha0. }
    assert (Ha1C : mC !!! Regidx a1_idx = mword_of_int av).
    { rewrite /mC (upd_ne mB (Regidx a5_idx) (Regidx a1_idx) _
                     ltac:(vm_compute; discriminate)).
      rewrite /mB (upd_ne mA (Regidx s0_idx) (Regidx a1_idx) _
                     ltac:(vm_compute; discriminate)).
      rewrite /mA (upd_ne m (Regidx csp_rs1) (Regidx a1_idx) _
                     ltac:(vm_compute; discriminate)).
      exact Ha1. }
    (* ---- 0x16  ble a0,a5,0x76 : argc <= 1 prints nothing ---- *)
    assert (Hbt16 : (1 >=? Z.of_nat (length args))
                    = uv_btaken BGE (mC !!! Regidx a5_idx)
                        (mC !!! Regidx a0_idx)).
    { rewrite Ha5C Ha0C. symmetry.
      exact (moi_ge_s 1 (Z.of_nat (length args))
               ltac:(unfold Z63; lia) ltac:(unfold Z63; lia)). }
    iApply (wp_uk_btype γt γd γs hc mC (mword_of_int 0x16)
              (mword_of_int 96 : mword 13) a0_idx a5_idx BGE
              (1 >=? Z.of_nat (length args)) (mword_of_int 0x76) (2 + n)
              Hbt16
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(intros _; vm_compute; reflexivity)
              with "C16 Hrun").
    destruct (decide (length args <= 1)%nat) as [Hsmall | Hbig].
    { (* nothing to print *)
      assert (Etrue : (1 >=? Z.of_nat (length args)) = true)
        by (apply Z.geb_le; lia).
      rewrite Etrue. iIntros (hx) "Hrun".
      iApply (wp_kecho_main_exit hx _ (2 + n) with "Hcode Hrun"). }
    assert (Efalse : (1 >=? Z.of_nat (length args)) = false).
    { destruct (1 >=? Z.of_nat (length args)) eqn:Eb; [ | reflexivity ].
      apply Z.geb_le in Eb. lia. }
    rewrite Efalse.
    assert (Eif : (if false then (mword_of_int 0x76 : mword 64)
                   else add_vec_int (mword_of_int 0x16 : mword 64) 4)
                  = mword_of_int 0x1a)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Eif. iIntros (hd) "Hrun".
    (* the array is MAPPED, so its arithmetic cannot wrap *)
    destruct (lookup_lt_is_Some_2 args 0%nat ltac:(lia)) as [g0 Hg0].
    destruct (lookup_lt_is_Some_2 args (length args - 1)%nat ltac:(lia))
      as [gl Hgl].
    iDestruct (uargv_acc γd av args 0%nat g0 Hg0 with "Hargv")
      as "[[Hwa Hsa] Hcla]".
    iDestruct (urun_uword_bnd with "Hrun Hwa") as %Hba.
    iDestruct ("Hcla" with "[$Hwa $Hsa]") as "Hargv".
    iDestruct (uargv_acc γd av args (length args - 1)%nat gl Hgl with "Hargv")
      as "[[Hwb Hsb] Hclb]".
    iDestruct (urun_uword_bnd with "Hrun Hwb") as %Hbb.
    iDestruct ("Hclb" with "[$Hwb $Hsb]") as "Hargv".
    change (2 ^ 38) with 274877906944 in Hba, Hbb.
    assert (Hav0 : 0 <= av) by lia.
    assert (Hav38 : av + 8 * Z.of_nat (length args) <= 2 ^ 38)
      by (change (2 ^ 38) with 274877906944; lia).
    (* ---- 0x1a  addi s1,a1,8 ---- *)
    assert (E8i : (sign_extend' 64 (mword_of_int 8 : mword 12) : mword 64)
                  = mword_of_int 8)
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uk_addi γt γd γs hd mC (mword_of_int 0x1a)
              (mword_of_int 8 : mword 12) a1_idx s1_idx
              (mword_of_int (av + 8)) (2 + n)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha1C E8i moi_add; reflexivity)
              with "C1a Hrun").
    assert (E1a : add_vec_int (mword_of_int 0x1a : mword 64) 4
                  = mword_of_int 0x1e)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E1a. iIntros (he) "Hrun".
    set (mD := <[Regidx s1_idx
                 := regval_into_reg (mword_of_int (av + 8) : mword 64)]> mC).
    assert (Ha0D : mD !!! Regidx a0_idx
                   = mword_of_int (Z.of_nat (length args))).
    { rewrite /mD (upd_ne mC (Regidx s1_idx) (Regidx a0_idx) _
                     ltac:(vm_compute; discriminate)). exact Ha0C. }
    (* ---- 0x1e  c.addiw a0,a0,-2 ---- *)
    assert (Em2 : (sign_extend' 64 (mword_of_int 62 : mword 6) : mword 64)
                  = mword_of_int (-2))
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uk_caddiw γt γd γs he mD (mword_of_int 0x1e)
              (mword_of_int 62 : mword 6) a0_idx
              (mword_of_int (Z.of_nat (length args) - 2)) (2 + n)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha0D Em2
                      (moi_addw (Z.of_nat (length args)) (-2)
                         ltac:(unfold Z31; lia));
                    f_equal; lia)
              with "C1e Hrun").
    assert (E1e : add_vec_int (mword_of_int 0x1e : mword 64) 2
                  = mword_of_int 0x20)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E1e. iIntros (hf) "Hrun".
    set (mE := <[Regidx a0_idx
                 := regval_into_reg
                      (mword_of_int (Z.of_nat (length args) - 2)
                       : mword 64)]> mD).
    assert (Ha0E : mE !!! Regidx a0_idx
                   = mword_of_int (Z.of_nat (length args) - 2))
      by exact (upd_eq mD (Regidx a0_idx)
                  (regval_into_reg
                     (mword_of_int (Z.of_nat (length args) - 2) : mword 64))).
    (* ---- 0x20  slli a5,a0,32 ---- *)
    iApply (wp_uk_slli γt γd γs hf mE (mword_of_int 0x20)
              (mword_of_int 32 : mword 6) a0_idx a5_idx
              (shift_bits_left
                 (mword_of_int (Z.of_nat (length args) - 2) : mword 64)
                 (subrange_vec_dec (mword_of_int 32 : mword 6)
                    (Z.sub log2_xlen 1) 0)) (2 + n)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha0E; reflexivity)
              with "C20 Hrun").
    assert (E20 : add_vec_int (mword_of_int 0x20 : mword 64) 4
                  = mword_of_int 0x24)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E20. iIntros (hg) "Hrun".
    set (mF := <[Regidx a5_idx
                 := regval_into_reg
                      (shift_bits_left
                         (mword_of_int (Z.of_nat (length args) - 2)
                          : mword 64)
                         (subrange_vec_dec (mword_of_int 32 : mword 6)
                            (Z.sub log2_xlen 1) 0))]> mE).
    assert (Ha5F : mF !!! Regidx a5_idx
                   = shift_bits_left
                       (mword_of_int (Z.of_nat (length args) - 2) : mword 64)
                       (subrange_vec_dec (mword_of_int 32 : mword 6)
                          (Z.sub log2_xlen 1) 0))
      by exact (upd_eq mE (Regidx a5_idx) _).
    (* ---- 0x24  srli a0,a5,29 : a0 := 8 * (argc - 2) ---- *)
    iApply (wp_uk_srli γt γd γs hg mF (mword_of_int 0x24)
              (mword_of_int 29 : mword 6) a5_idx a0_idx
              (mword_of_int ((Z.of_nat (length args) - 2) * 8)) (2 + n)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha5F; symmetry;
                    exact (moi_shl32_shr29 (Z.of_nat (length args) - 2)
                             ltac:(unfold Z32; lia)))
              with "C24 Hrun").
    assert (E24 : add_vec_int (mword_of_int 0x24 : mword 64) 4
                  = mword_of_int 0x28)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E24. iIntros (hh) "Hrun".
    set (mG := <[Regidx a0_idx
                 := regval_into_reg
                      (mword_of_int ((Z.of_nat (length args) - 2) * 8)
                       : mword 64)]> mF).
    assert (Ha0G : mG !!! Regidx a0_idx
                   = mword_of_int ((Z.of_nat (length args) - 2) * 8))
      by exact (upd_eq mF (Regidx a0_idx) _).
    assert (Hs1G : mG !!! Regidx s1_idx = mword_of_int (av + 8)).
    { rewrite /mG (upd_ne mF (Regidx a0_idx) (Regidx s1_idx) _
                     ltac:(vm_compute; discriminate)).
      rewrite /mF (upd_ne mE (Regidx a5_idx) (Regidx s1_idx) _
                     ltac:(vm_compute; discriminate)).
      rewrite /mE (upd_ne mD (Regidx a0_idx) (Regidx s1_idx) _
                     ltac:(vm_compute; discriminate)).
      rewrite /mD.
      exact (upd_eq mC (Regidx s1_idx)
               (regval_into_reg (mword_of_int (av + 8) : mword 64))). }
    (* ---- 0x28  add s5,s1,a0 : s5 := &argv[argc-1] ---- *)
    iApply (wp_uk_add γt γd γs hh mG (mword_of_int 0x28)
              s1_idx a0_idx s5_idx
              (mword_of_int (av + 8 * Z.of_nat (length args) - 8)) (2 + n)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs1G Ha0G moi_add; f_equal; lia)
              with "C28 Hrun").
    assert (E28 : add_vec_int (mword_of_int 0x28 : mword 64) 4
                  = mword_of_int 0x2c)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E28. iIntros (hi) "Hrun".
    set (mH := <[Regidx s5_idx
                 := regval_into_reg
                      (mword_of_int (av + 8 * Z.of_nat (length args) - 8)
                       : mword 64)]> mG).
    assert (Ha1H : mH !!! Regidx a1_idx = mword_of_int av).
    { rewrite /mH (upd_ne mG (Regidx s5_idx) (Regidx a1_idx) _
                     ltac:(vm_compute; discriminate)).
      rewrite /mG (upd_ne mF (Regidx a0_idx) (Regidx a1_idx) _
                     ltac:(vm_compute; discriminate)).
      rewrite /mF (upd_ne mE (Regidx a5_idx) (Regidx a1_idx) _
                     ltac:(vm_compute; discriminate)).
      rewrite /mE (upd_ne mD (Regidx a0_idx) (Regidx a1_idx) _
                     ltac:(vm_compute; discriminate)).
      rewrite /mD (upd_ne mC (Regidx s1_idx) (Regidx a1_idx) _
                     ltac:(vm_compute; discriminate)).
      exact Ha1C. }
    (* ---- 0x2c  c.addi a1,a1,16 ---- *)
    assert (E16i : (sign_extend' 64 (mword_of_int 16 : mword 6) : mword 64)
                   = mword_of_int 16)
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uk_caddi γt γd γs hi mH (mword_of_int 0x2c)
              (mword_of_int 16 : mword 6) a1_idx
              (mword_of_int (av + 16)) (2 + n)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha1H E16i moi_add; reflexivity)
              with "C2c Hrun").
    assert (E2c : add_vec_int (mword_of_int 0x2c : mword 64) 2
                  = mword_of_int 0x2e)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E2c. iIntros (hj) "Hrun".
    set (mI := <[Regidx a1_idx
                 := regval_into_reg (mword_of_int (av + 16) : mword 64)]> mH).
    assert (Ha1I : mI !!! Regidx a1_idx = mword_of_int (av + 16))
      by exact (upd_eq mH (Regidx a1_idx) _).
    assert (Ha0I : mI !!! Regidx a0_idx
                   = mword_of_int ((Z.of_nat (length args) - 2) * 8)).
    { rewrite /mI (upd_ne mH (Regidx a1_idx) (Regidx a0_idx) _
                     ltac:(vm_compute; discriminate)).
      rewrite /mH (upd_ne mG (Regidx s5_idx) (Regidx a0_idx) _
                     ltac:(vm_compute; discriminate)).
      exact Ha0G. }
    (* ---- 0x2e  add s4,a1,a0 : s4 := &argv[argc] ---- *)
    iApply (wp_uk_add γt γd γs hj mI (mword_of_int 0x2e)
              a1_idx a0_idx s4_idx
              (mword_of_int (av + 8 * Z.of_nat (length args))) (2 + n)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha1I Ha0I moi_add; f_equal; lia)
              with "C2e Hrun").
    assert (E2e : add_vec_int (mword_of_int 0x2e : mword 64) 4
                  = mword_of_int 0x32)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E2e. iIntros (hk) "Hrun".
    set (mJ := <[Regidx s4_idx
                 := regval_into_reg
                      (mword_of_int (av + 8 * Z.of_nat (length args))
                       : mword 64)]> mI).
    (* ---- 0x32  c.li s3,1 ---- *)
    iApply (wp_uk_cli γt γd γs hk mJ (mword_of_int 0x32)
              (mword_of_int 1 : mword 6) s3_idx (2 + n)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) with "C32 Hrun").
    assert (E32 : add_vec_int (mword_of_int 0x32 : mword 64) 2
                  = mword_of_int 0x34)
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Eli3 : <[Regidx s3_idx
                     := regval_into_reg
                          (sign_extend' 64 (mword_of_int 1 : mword 6)
                           : mword 64)]> mJ
                   = <[Regidx s3_idx := (mword_of_int 1 : mword 64)]> mJ)
      by (f_equal; apply bv_eq; vm_compute; reflexivity).
    rewrite E32 Eli3. iIntros (hl) "Hrun".
    set (mK := <[Regidx s3_idx := (mword_of_int 1 : mword 64)]> mJ).
    (* ---- 0x34  auipc s6,0x1 ; 0x38  addi s6,s6,2300 (the separator) ---- *)
    iApply (wp_uk_auipc γt γd γs hl mK (mword_of_int 0x34)
              (mword_of_int 1 : mword 20) s6_idx
              (add_vec (mword_of_int 0x34 : mword 64)
                 (auipc_off (mword_of_int 1 : mword 20))) (2 + n)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) eq_refl
              with "C34 Hrun").
    assert (E34 : add_vec_int (mword_of_int 0x34 : mword 64) 4
                  = mword_of_int 0x38)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E34. iIntros (hm) "Hrun".
    set (mL := <[Regidx s6_idx
                 := regval_into_reg
                      (add_vec (mword_of_int 0x34 : mword 64)
                         (auipc_off (mword_of_int 1 : mword 20)))]> mK).
    iApply (wp_uk_addi γt γd γs hm mL (mword_of_int 0x38)
              (mword_of_int 2300 : mword 12) s6_idx s6_idx
              (add_vec (mL !!! Regidx s6_idx)
                 (sign_extend' 64 (mword_of_int 2300 : mword 12))) (2 + n)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) eq_refl
              with "C38 Hrun").
    assert (E38 : add_vec_int (mword_of_int 0x38 : mword 64) 4
                  = mword_of_int 0x3c)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E38. iIntros (hn) "Hrun".
    set (mM := <[Regidx s6_idx
                 := regval_into_reg
                      (add_vec (mL !!! Regidx s6_idx)
                         (sign_extend' 64
                            (mword_of_int 2300 : mword 12)))]> mL).
    (* ---- 0x3c  c.j 0x4e ---- *)
    iApply (wp_uk_cj γt γd γs hn mM (mword_of_int 0x3c)
              (mword_of_int 9 : mword 11) (mword_of_int 0x4e) (2 + n)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "C3c Hrun").
    iIntros (ho) "Hrun".
    (* ---- into the scan, at i = 1 ---- *)
    assert (Hs1M : mM !!! Regidx s1_idx = mword_of_int (av + 8 * Z.of_nat 1)).
    { replace (av + 8 * Z.of_nat 1) with (av + 8) by lia.
      rewrite /mM (upd_ne mL (Regidx s6_idx) (Regidx s1_idx) _
                     ltac:(vm_compute; discriminate)).
      rewrite /mL (upd_ne mK (Regidx s6_idx) (Regidx s1_idx) _
                     ltac:(vm_compute; discriminate)).
      rewrite /mK (upd_ne mJ (Regidx s3_idx) (Regidx s1_idx) _
                     ltac:(vm_compute; discriminate)).
      rewrite /mJ (upd_ne mI (Regidx s4_idx) (Regidx s1_idx) _
                     ltac:(vm_compute; discriminate)).
      rewrite /mI (upd_ne mH (Regidx a1_idx) (Regidx s1_idx) _
                     ltac:(vm_compute; discriminate)).
      rewrite /mH (upd_ne mG (Regidx s5_idx) (Regidx s1_idx) _
                     ltac:(vm_compute; discriminate)).
      exact Hs1G. }
    assert (Hs3M : mM !!! Regidx s3_idx = mword_of_int 1).
    { rewrite /mM (upd_ne mL (Regidx s6_idx) (Regidx s3_idx) _
                     ltac:(vm_compute; discriminate)).
      rewrite /mL (upd_ne mK (Regidx s6_idx) (Regidx s3_idx) _
                     ltac:(vm_compute; discriminate)).
      rewrite /mK.
      exact (upd_eq mJ (Regidx s3_idx) (mword_of_int 1 : mword 64)). }
    assert (Hs4M : mM !!! Regidx s4_idx
                   = mword_of_int (av + 8 * Z.of_nat (length args))).
    { rewrite /mM (upd_ne mL (Regidx s6_idx) (Regidx s4_idx) _
                     ltac:(vm_compute; discriminate)).
      rewrite /mL (upd_ne mK (Regidx s6_idx) (Regidx s4_idx) _
                     ltac:(vm_compute; discriminate)).
      rewrite /mK (upd_ne mJ (Regidx s3_idx) (Regidx s4_idx) _
                     ltac:(vm_compute; discriminate)).
      rewrite /mJ. exact (upd_eq mI (Regidx s4_idx) _). }
    assert (Hs5M : mM !!! Regidx s5_idx
                   = mword_of_int (av + 8 * Z.of_nat (length args) - 8)).
    { rewrite /mM (upd_ne mL (Regidx s6_idx) (Regidx s5_idx) _
                     ltac:(vm_compute; discriminate)).
      rewrite /mL (upd_ne mK (Regidx s6_idx) (Regidx s5_idx) _
                     ltac:(vm_compute; discriminate)).
      rewrite /mK (upd_ne mJ (Regidx s3_idx) (Regidx s5_idx) _
                     ltac:(vm_compute; discriminate)).
      rewrite /mJ (upd_ne mI (Regidx s4_idx) (Regidx s5_idx) _
                     ltac:(vm_compute; discriminate)).
      rewrite /mI (upd_ne mH (Regidx a1_idx) (Regidx s5_idx) _
                     ltac:(vm_compute; discriminate)).
      rewrite /mH. exact (upd_eq mG (Regidx s5_idx) _). }
    iApply (wp_kecho_main_loop av args (length args - 2)%nat 1%nat ho mM n
              ltac:(lia) Hav0 Hav38 Hs1M Hs3M Hs4M Hs5M
              with "Hcode Hargv Hrun").
  Qed.


  (* ===================================================================== *)
  (* start -- the ELF entry.  usys.S's crt: a frame, then main(argc, argv), *)
  (* then exit if it ever came back.  It does not: main's own contract has  *)
  (* no continuation, so 0x88 is unreachable and never appears here.        *)
  (*                                                                        *)
  (* The [avail] arithmetic is the whole call chain spelled out: start's    *)
  (* two words, main's eight, and the two strlen borrows at every           *)
  (* iteration of main's loop.                                              *)
  (* ===================================================================== *)
  Lemma wp_kecho_start (h : CpuId) (m : regfile) (av : Z) (args : list uarg)
      (n : nat) :
    m !!! Regidx a0_idx = mword_of_int (Z.of_nat (length args)) ->
    m !!! Regidx a1_idx = mword_of_int av ->
    echo_code γt -∗
    uargv γd av args -∗
    urun γt γd γs h m (mword_of_int EchoSyms.start) (2 + (8 + (2 + n))) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Ha0 Ha1. iIntros "#Hcode Hargv Hrun".
    iPoseProof "Hcode" as "#Hc". iDestruct "Hc" as CODE.
    destruct echo_syms_pins as (Hmain & Hstart & _ & _ & _). rewrite Hstart.
    iDestruct (urun_stack with "Hrun") as %[Hal8' Hroom].
    remember (m !!! Regidx csp_rs1) as sp0 eqn:Hsp0.
    assert (Hsp : m !!! Regidx csp_rs1 = sp0) by (symmetry; exact Hsp0).
    clear Hsp0.
    assert (Hal8 : uint sp0 mod 8 = 0) by exact Hal8'.
    assert (Hlo : 16 <= uint sp0) by lia.
    assert (Hbsp : bv_unsigned (add_vec_int sp0 (- (8 * Z.of_nat 2)))
                   = bv_unsigned sp0 - 16).
    { replace (- (8 * Z.of_nat 2)) with (-16) by lia.
      exact (uv_avi_neg sp0 16 ltac:(lia) ltac:(rewrite <- uint_unsigned; lia)). }
    assert (Hsp16 : uint (add_vec_int sp0 (- (8 * Z.of_nat 2)))
                    = uint sp0 - 16)
      by (rewrite !uint_unsigned; exact Hbsp).
    assert (Ho8 : uoff_sdsp (mword_of_int 1 : mword 6) = 8)
      by (vm_compute; reflexivity).
    assert (Ho0 : uoff_sdsp (mword_of_int 0 : mword 6) = 0)
      by (vm_compute; reflexivity).
    (* ---- 0x7c  c.addi sp,sp,-16 ---- *)
    iApply (wp_uk_caddi_sp_dn γt γd γs h m (mword_of_int 0x7c)
              (mword_of_int 48 : mword 6) 2 (8 + (2 + n))
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "C7c Hrun").
    assert (E7c : add_vec_int (mword_of_int 0x7c : mword 64) 2
                  = mword_of_int 0x7e)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Hsp ustack_2 E7c.
    iIntros "(_ & [%v8 Hw8] & [%v0 Hw0])".
    iIntros (h1) "Hrun".
    set (m1 := <[Regidx csp_rs1
                 := regval_into_reg (add_vec_int sp0 (- (8 * Z.of_nat 2)))]> m).
    assert (Hsp1 : m1 !!! Regidx csp_rs1
                   = add_vec_int sp0 (- (8 * Z.of_nat 2)))
      by exact (upd_eq m (Regidx csp_rs1)
                  (regval_into_reg (add_vec_int sp0 (- (8 * Z.of_nat 2))))).
    (* ---- 0x7e  c.sdsp ra,8(sp) ---- *)
    iApply (wp_uk_csdsp γt γd γs h1 m1 (mword_of_int 0x7e)
              (mword_of_int 1 : mword 6) ra_idx (uint sp0 - 8) v8 (8 + (2 + n))
              ltac:(rewrite Hsp1 Hsp16 Ho8; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              with "C7e Hw8 Hrun").
    iIntros "Hw8".
    assert (E7e : add_vec_int (mword_of_int 0x7e : mword 64) 2
                  = mword_of_int 0x80)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E7e. iIntros (h2) "Hrun".
    (* ---- 0x80  c.sdsp s0,0(sp) ---- *)
    iApply (wp_uk_csdsp γt γd γs h2 m1 (mword_of_int 0x80)
              (mword_of_int 0 : mword 6) s0_idx (uint sp0 - 16) v0
              (8 + (2 + n))
              ltac:(rewrite Hsp1 Hsp16 Ho0; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              with "C80 Hw0 Hrun").
    iIntros "Hw0".
    assert (E80 : add_vec_int (mword_of_int 0x80 : mword 64) 2
                  = mword_of_int 0x82)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E80. iIntros (h3) "Hrun".
    (* ---- 0x82  c.addi4spn s0,sp,16 ---- *)
    iApply (wp_uk_caddi4spn γt γd γs h3 m1 (mword_of_int 0x82)
              (mword_of_int 0 : mword 3) (mword_of_int 4 : mword 8) s0_idx
              (add_vec (m1 !!! Regidx csp_rs1)
                 (sign_extend' 64
                    (caddi4spn_imm (mword_of_int 4 : mword 8)))) (8 + (2 + n))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
              eq_refl
              with "C82 Hrun").
    assert (E82 : add_vec_int (mword_of_int 0x82 : mword 64) 2
                  = mword_of_int 0x84)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E82. iIntros (h4) "Hrun".
    set (m2 := <[Regidx s0_idx
                 := regval_into_reg
                      (add_vec (m1 !!! Regidx csp_rs1)
                         (sign_extend' 64
                            (caddi4spn_imm (mword_of_int 4 : mword 8))))]> m1).
    (* ---- 0x84  jal ra,0x0 <main> ---- *)
    iApply (wp_uk_jal γt γd γs h4 m2 (mword_of_int 0x84)
              (mword_of_int 2097020 : mword 21) ra_idx
              (mword_of_int EchoSyms.main) (mword_of_int 0x88) (8 + (2 + n))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hmain; apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(rewrite Hmain; vm_compute; reflexivity)
              with "C84 Hrun").
    iIntros (h5) "Hrun".
    set (m3 := <[Regidx ra_idx
                 := regval_into_reg (mword_of_int 0x88 : mword 64)]> m2).
    (* ---- the call: main(argc, argv) -- it never returns ---- *)
    assert (Ha03 : m3 !!! Regidx a0_idx
                   = mword_of_int (Z.of_nat (length args))).
    { rewrite /m3 (upd_ne m2 (Regidx ra_idx) (Regidx a0_idx) _
                     ltac:(vm_compute; discriminate)).
      rewrite /m2 (upd_ne m1 (Regidx s0_idx) (Regidx a0_idx) _
                     ltac:(vm_compute; discriminate)).
      rewrite /m1 (upd_ne m (Regidx csp_rs1) (Regidx a0_idx) _
                     ltac:(vm_compute; discriminate)).
      exact Ha0. }
    assert (Ha13 : m3 !!! Regidx a1_idx = mword_of_int av).
    { rewrite /m3 (upd_ne m2 (Regidx ra_idx) (Regidx a1_idx) _
                     ltac:(vm_compute; discriminate)).
      rewrite /m2 (upd_ne m1 (Regidx s0_idx) (Regidx a1_idx) _
                     ltac:(vm_compute; discriminate)).
      rewrite /m1 (upd_ne m (Regidx csp_rs1) (Regidx a1_idx) _
                     ltac:(vm_compute; discriminate)).
      exact Ha1. }
    iApply (wp_kecho_main h5 m3 av args n Ha03 Ha13
              with "Hcode Hargv Hrun").
  Qed.

End UkEcho.
