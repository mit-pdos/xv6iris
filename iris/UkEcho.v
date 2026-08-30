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
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExtras.
Require Import RegFile WpGpr.
Require Import AlignBits WpMmodeLeafBase.
Require Import UserBits UserPtTree UserExec ProcPtOwn.
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
      (avail : nat) (a : Z) (b : bv 8) :
    urun γt γd γs h m pc avail -∗ ubyte γd a b -∗ ⌜ 0 <= a < 2 ^ 38 ⌝.
  Proof.
    iIntros "Hrun Hb".
    iDestruct "Hrun" as (C pt Rut sz M pm) "(_ & _ & Hh & _ & _)".
    iDestruct (uheap_ubyte with "Hh Hb") as %(_ & _ & Hbnd).
    iPureIntro. exact Hbnd.
  Qed.

  Local Lemma urun_ustr_bnd (h : CpuId) (m : regfile) (pc : mword 64)
      (avail : nat) (a : Z) (len : nat) (f : nat -> bv 8) :
    urun γt γd γs h m pc avail -∗ ustr γd a len f -∗
    ⌜ 0 <= a /\ a + Z.of_nat len < 2 ^ 38 ⌝.
  Proof.
    iIntros "Hrun Hs".
    iDestruct (ustr_nul with "Hs") as "[Hnul Hcl]".
    iDestruct (urun_ubyte_bnd with "Hrun Hnul") as %Hhi.
    iDestruct ("Hcl" with "Hnul") as "Hs".
    destruct len as [| len' ].
    - iPureIntro. lia.
    - iDestruct (ustr_byte γd a (S len') f 0%nat ltac:(lia) with "Hs")
        as "[Hb0 _]".
      iDestruct (urun_ubyte_bnd with "Hrun Hb0") as %Hlo.
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
  Local Lemma wp_kecho_strlen_step (h : CpuId) (mc : regfile) (p : Z)
      (b : mword 8) (bz : Z) (tgt : mword 64) (n : nat) :
    0 <= p -> p + 1 < Z64 ->
    bv_unsigned b = bz ->
    mc !!! Regidx a5_idx = mword_of_int p ->
    tgt = (if bz =? 0 then mword_of_int 0xf8 else mword_of_int 0xee) ->
    echo_code γt -∗
    ubyte γd p b -∗
    urun γt γd γs h mc (mword_of_int 0xee) n -∗
    (ubyte γd p b -∗
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
              (mword_of_int 4095 : mword 12) a5_idx a4_idx p b n
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
  Local Lemma wp_kecho_strlen_loop (a : Z) (len : nat) (f : nat -> bv 8) :
    forall (k j : nat) (h : CpuId) (mc : regfile) (n : nat),
    (len = 1 + j + k)%nat ->
    0 <= a -> a + Z.of_nat len < 2 ^ 38 ->
    mc !!! Regidx a5_idx = mword_of_int (a + 1 + Z.of_nat j) ->
    echo_code γt -∗
    ustr γd a len f -∗
    urun γt γd γs h mc (mword_of_int 0xee) n -∗
    (ustr γd a len f -∗
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
      iApply (wp_kecho_strlen_step h mc (a + 1 + Z.of_nat j) ubyte0
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
      iDestruct (ustr_byte γd a len f (1 + j)%nat Hlt with "Hs") as "[Hb Hcl]".
      replace (a + Z.of_nat (1 + j)) with (a + 1 + Z.of_nat j) by lia.
      iApply (wp_kecho_strlen_step h mc (a + 1 + Z.of_nat j) (f (1 + j)%nat)
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
  Lemma wp_kecho_strlen (h : CpuId) (m : regfile) (a : Z) (len : nat)
      (f : nat -> bv 8) (n : nat) :
    m !!! Regidx a0_idx = mword_of_int a ->
    echo_code γt -∗
    ustr γd a len f -∗
    urun γt γd γs h m (mword_of_int EchoSyms.strlen) (2 + n) -∗
    (ustr γd a len f -∗
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
               ubyte γd a b0 ∗ (ubyte γd a b0 -∗ ustr γd a len f))%I
      with "[Hs]" as "(%b0 & %bz & %Hbz & %Hbnz & Hb & Hcl)".
    { destruct len as [| len' ].
      - iDestruct (ustr_nul with "Hs") as "[Hb Hcl]".
        replace (a + Z.of_nat 0%nat) with a by lia.
        iExists ubyte0, (bv_unsigned ubyte0).
        iSplit; [ iPureIntro; reflexivity | ].
        iSplit; [ iPureIntro; vm_compute; reflexivity | ].
        iFrame.
      - iDestruct (ustr_nonul with "Hs") as %Hne.
        iDestruct (ustr_byte γd a (S len') f 0%nat ltac:(lia) with "Hs")
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
              (mword_of_int 0 : mword 12) a0_idx a5_idx a b0 n
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
      iApply (wp_kecho_strlen_loop a (S len') f len' 0%nat h7 m4 n
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

End UkEcho.
