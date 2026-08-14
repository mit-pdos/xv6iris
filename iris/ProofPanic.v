(* ProofPanic.v -- panic()'s whole-function proof (SpecPanic.v), as a sealed
   functor over printk.

     void panic(char *s) {
       printk("panic: ");
       printk("%s\n", s);
       for (;;) ;
     }

   Fourteen instructions: a 32-byte frame, ra/s0/s1 saved, the message parked
   in s1 (callee-saved, so it survives the first call), two calls to printk,
   and a self-jump.

   THE SELF-JUMP IS THE WHOLE POINT.  [pn_spin] proves it by Löb, hart-
   generically: [wp_cj_s_sconf] hands its continuation back UNDER A LATER
   (a backward jump is a loop back edge), and that later is exactly what
   discharges the induction hypothesis.  Nothing else is needed -- the
   contract has no postcondition to establish, so once the pc is at the
   self-jump with the machine capability in hand there is no obligation left
   but to keep stepping.  Structurally this is ProofSpin.v's [wp_spin] (the
   M-mode self-jump in entry.S) with the S-mode leaf doing the work.

   The two calls are ordinary: the only thing worth noting is that the SECOND
   one's vararg is [a1 = s1 = the entry a0], threaded across the first call by
   [callee_saved]. *)
Set Printing Depth 40.
From Stdlib Require Import ZArith Bool Lia List String Ascii.
From stdpp Require Import gmap list bitvector.definitions.
From iris.algebra Require Import dfrac.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_var gen_heap invariants.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExtras.
Require Import RegFile HartTp.
Require Import SmodeCore.
Require Import InstrBytes KernelText KernelDataInv.
Require Import StackOwn CalleeSaved.
Require Import WpMmodeLeafBase.
Require Import KernelRvcDecode.
Require Import WpSconfAlu WpSconfMem WpSconfCtl.
Require Import IntrDefs WpNext.
Require Import WpLock CpuOwn.
Require Import DiskPtsto WpUart UartTxInv.
Require Import PrintkArgs.
Require Import PanicStub.
Require Import SpecPrintk.
Require Import SpecPanic.
Require Import CodePanic.
From Kernel Require KernelInstrs KernelData KernelSyms.
Import Defs.
Local Open Scope Z_scope.

Notation PA := KernelSyms.panic.

(* ===================================================================== *)
(* 0.  The numeric side conditions, mword-free and at the top level.      *)
(* ===================================================================== *)
Lemma pn_K4 (K : nat) : (panic_stack <= K)%nat -> (4 <= K)%nat.
Proof. unfold panic_stack. lia. Qed.

Lemma pn_Kpk (K : nat) : (panic_stack <= K)%nat -> (printk_stack <= K - 4)%nat.
Proof. unfold panic_stack, printk_stack. lia. Qed.

(* ===================================================================== *)
(* 1.  The two .rodata literals.                                          *)
(* ===================================================================== *)
Definition pn_hdr_a : Z := 0x80007018.        (* "panic: " (a0 at +0x10) *)
Definition pn_fmt_a : Z := 0x80007020.        (* "%s\n"    (a0 at +0x1e) *)

Definition pn_hdr : string := "panic: ".
Definition pn_fmt : string := "%s
".

Lemma pn_hdr_nonul : nonul pn_hdr = true. Proof. vm_compute; reflexivity. Qed.
Lemma pn_fmt_nonul : nonul pn_fmt = true. Proof. vm_compute; reflexivity. Qed.

Lemma pn_hdr_kinds : pk_kinds pn_hdr = []. Proof. vm_compute; reflexivity. Qed.
Lemma pn_fmt_kinds : pk_kinds pn_fmt = [PkStr]. Proof. vm_compute; reflexivity. Qed.

Lemma pn_hdr_len : (Z.of_nat (String.length pn_hdr) < 2147483645)%Z.
Proof. vm_compute; reflexivity. Qed.
Lemma pn_fmt_len : (Z.of_nat (String.length pn_fmt) < 2147483645)%Z.
Proof. vm_compute; reflexivity. Qed.

Section PanicData.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId}.

  Lemma pn_hdr_bytes :
    forall j b, cstring_bytes pn_hdr !! j = Some b ->
      KernelData.kernel_data !! (pn_hdr_a + Z.of_nat j)%Z = Some b.
  Proof.
    intros j b Hj.
    do 8 (destruct j as [|j]; [ vm_compute in Hj |- *; congruence | ]).
    vm_compute in Hj; discriminate.
  Qed.

  Lemma pn_fmt_bytes :
    forall j b, cstring_bytes pn_fmt !! j = Some b ->
      KernelData.kernel_data !! (pn_fmt_a + Z.of_nat j)%Z = Some b.
  Proof.
    intros j b Hj.
    do 4 (destruct j as [|j]; [ vm_compute in Hj |- *; congruence | ]).
    vm_compute in Hj; discriminate.
  Qed.

  Lemma pn_hdr_str :
    (kernel_data : iProp Σ) -∗ (mword_of_int pn_hdr_a : mword 64) ↦ₛ□ pn_hdr.
  Proof.
    iIntros "#Hd".
    iApply (kernel_data_string pn_hdr_a pn_hdr _ eq_refl
              ltac:(unfold text_end, pn_hdr_a; lia) pn_hdr_bytes with "Hd").
  Qed.

  Lemma pn_fmt_str :
    (kernel_data : iProp Σ) -∗ (mword_of_int pn_fmt_a : mword 64) ↦ₛ□ pn_fmt.
  Proof.
    iIntros "#Hd".
    iApply (kernel_data_string pn_fmt_a pn_fmt _ eq_refl
              ltac:(unfold text_end, pn_fmt_a; lia) pn_fmt_bytes with "Hd").
  Qed.

End PanicData.

(* ===================================================================== *)
(* 2.  +0x26  [c.j .]  -- the loop panic never leaves.                    *)
(*                                                                        *)
(* Hart-GENERIC and stated OUTSIDE any [CpuId] section: with interrupts   *)
(* enabled the self-jump can be trapped and resumed on another hart, so   *)
(* the induction hypothesis has to hold at every hart, not at the one the *)
(* loop was entered on.                                                   *)
(* ===================================================================== *)
Section PanicSpin.
  Context `{!riscvGS Σ, !sieG Σ}.
  Context `{GEN : GenId}.

  (* [h] is bound as a [CpuId], not as a [CPU]: [Loop] itself is
     [LoopE gen_id cpu_id], so the PROGRAM names the hart it steps and the
     statement has to put one in scope for the body to elaborate at all. *)
  Lemma pn_spin :
    kernel_text -∗
    ∀ (h : CpuId) (m : regfile) (K : nat) (b : bool) (p : mword 64),
      sie_cap_gpr m K b p -∗
      pc_is (mword_of_int (PA + 0x26)) -∗
      WP (Loop : expr riscv_lang).
  Proof.
    assert (Htgt : add_vec (mword_of_int (PA + 0x26) : mword 64)
                     (sign_extend' 64 (sign_extend' 21
                        (concat_vec (mword_of_int 0 : mword 11) ('b"0"))))
                   = mword_of_int (PA + 0x26))
      by (apply bv_eq; vm_compute; reflexivity).
    iIntros "#Ht".
    iLöb as "IH".
    iIntros (h m K b p) "Hcg Hpc".
    iPoseProof (pni_26 with "Ht") as "Hi26".
    iApply (wp_cj_s_sconf (CID := h) (mword_of_int (PA + 0x26))
              (sign_extend' 21 (concat_vec (mword_of_int 0 : mword 11) ('b"0")))
              m K b ltac:(rewrite Htgt; vm_compute; reflexivity)
              with "Hcg Hpc Hi26").
    iApply wp_next_intro. iIntros (CIDx). iNext.
    iIntros "Hcg Hpc".
    iEval (rewrite Htgt) in "Hpc".
    iApply ("IH" $! CIDx m K b p with "Hcg Hpc").
  Qed.

End PanicSpin.

(* ===================================================================== *)
(* 3.  The whole function.                                                *)
(* ===================================================================== *)
Module PanicProof (Printk : PRINTK) : PANIC.
Section ProofPanic.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ}.
  Context `{!uartGhostG Σ, !diskGhostG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Local Ltac pcw := apply bv_eq; vm_compute; reflexivity.
  Local Ltac nz := vm_compute; discriminate.
  Local Ltac reg_neq :=
    lazymatch goal with
    | |- ?a <> ?b => tryif unify a b then fail else (vm_compute; discriminate)
    end.

  Notation Rra := (mword_of_int 1 : mword 5).
  Notation Rs0 := (mword_of_int 8 : mword 5).
  Notation Rs1 := (mword_of_int 9 : mword 5).
  Notation Ra0 := (mword_of_int 10 : mword 5).
  Notation Ra1 := (mword_of_int 11 : mword 5).

  Lemma wp_panic_sconf
      (γpr γl : gname) (γd : uart_names) (γv : disk_names)
      (m : regfile) (K : nat) (bs : list (bv 8))
      (n : nat) (eb : bool) (C : iProp Σ) (b : bool) (p : mword 64)
      (dm : pk_arg_desc) (lks : gset nat)
    : wp_panic_sconf_body γpr γl γd γv m K bs n eb C b p dm lks.
  Proof.
    cbv beta zeta delta [wp_panic_sconf_body].
    intros HK Hdm Hn31.
    iIntros "#Hpan Hcg Hown #Htext #Hkdata Hpc #Henv #Hsub Hmsg".
    iDestruct "Henv" as "(#Hlk & #Hdev & #Htx)".
    iPoseProof (pni_00 with "Htext") as "Hi00".
    iPoseProof (pni_02 with "Htext") as "Hi02".
    iPoseProof (pni_04 with "Htext") as "Hi04".
    iPoseProof (pni_06 with "Htext") as "Hi06".
    iPoseProof (pni_08 with "Htext") as "Hi08".
    iPoseProof (pni_0a with "Htext") as "Hi0a".
    iPoseProof (pni_0c with "Htext") as "Hi0c".
    iPoseProof (pni_10 with "Htext") as "Hi10".
    iPoseProof (pni_14 with "Htext") as "Hi14".
    iPoseProof (pni_18 with "Htext") as "Hi18".
    iPoseProof (pni_1a with "Htext") as "Hi1a".
    iPoseProof (pni_1e with "Htext") as "Hi1e".
    iPoseProof (pni_22 with "Htext") as "Hi22".
    iPoseProof (pn_hdr_str with "Hkdata") as "#Hhdr".
    iPoseProof (pn_fmt_str with "Hkdata") as "#Hfmt".
    (* ================================================================== *)
    (* +0x00  c.addi sp,sp,-32 -- the 4-slot frame                        *)
    (* ================================================================== *)
    iApply (wp_caddi_sp_push_s_sconf (mword_of_int PA : mword 64)
              (mword_of_int 32 : mword 6) m K 4%nat b
              (pn_K4 K HK) (stk_push_32 (m !!! Regidx csp_rs1))
              with "Hcg Hpc Hi00").
    iIntros (CID1 Hs1) "Hcg Hframe Hpc".
    set (P0 := <[Regidx csp_rs1 := regval_into_reg
                  (add_vec (m !!! Regidx csp_rs1)
                     (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))))]> m).
    assert (HP0sp : P0 !!! Regidx csp_rs1 = pa_stk (m !!! Regidx csp_rs1) 4)
      by (rewrite /P0 upd_eq; apply stk_push_32).
    (* the three save-slot addresses, as the c.sdsp displacements compute them *)
    assert (Hb1 : add_vec (P0 !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1) 1).
    { rewrite HP0sp. unfold pa_stk, add_vec_int. rewrite !pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb2 : add_vec (P0 !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1) 2).
    { rewrite HP0sp. unfold pa_stk, add_vec_int. rewrite !pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb3 : add_vec (P0 !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1) 3).
    { rewrite HP0sp. unfold pa_stk, add_vec_int. rewrite !pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    iEval (rewrite stack_own_slots; cbn [seq]) in "Hframe".
    iDestruct "Hframe" as "(F1 & F2 & F3 & F4 & _)".
    iDestruct "F1" as (v1) "H1". iDestruct "F2" as (v2) "H2".
    iDestruct "F3" as (v3) "H3".
    (* ================================================================== *)
    (* +0x02 .. +0x06  sd ra,24(sp) / sd s0,16(sp) / sd s1,8(sp)          *)
    (* ================================================================== *)
    assert (Hp02 : add_vec_int (mword_of_int PA : mword 64) 2
                   = mword_of_int (PA + 0x2)) by pcw.
    iEval (rewrite Hp02) in "Hpc".
    iApply (wp_csdsp_s_sconf (CID := CID1) (mword_of_int (PA + 0x2))
              (mword_of_int 3 : mword 6) Rra P0 (K - 4)%nat v1 b
              with "Hcg Hpc Hi02 [H1]").
    { iEval (rewrite Hb1). iExact "H1". }
    iIntros (CID2 Hs2) "Hcg Hpc H1".
    assert (Hp04 : add_vec_int (mword_of_int (PA + 0x2) : mword 64) 2
                   = mword_of_int (PA + 0x4)) by pcw.
    iEval (rewrite Hp04) in "Hpc".
    iApply (wp_csdsp_s_sconf (CID := CID2) (mword_of_int (PA + 0x4))
              (mword_of_int 2 : mword 6) Rs0 P0 (K - 4)%nat v2 b
              with "Hcg Hpc Hi04 [H2]").
    { iEval (rewrite Hb2). iExact "H2". }
    iIntros (CID3 Hs3) "Hcg Hpc H2".
    assert (Hp06 : add_vec_int (mword_of_int (PA + 0x4) : mword 64) 2
                   = mword_of_int (PA + 0x6)) by pcw.
    iEval (rewrite Hp06) in "Hpc".
    iApply (wp_csdsp_s_sconf (CID := CID3) (mword_of_int (PA + 0x6))
              (mword_of_int 1 : mword 6) Rs1 P0 (K - 4)%nat v3 b
              with "Hcg Hpc Hi06 [H3]").
    { iEval (rewrite Hb3). iExact "H3". }
    iIntros (CID4 Hs4) "Hcg Hpc H3".
    (* ================================================================== *)
    (* +0x08  c.addi4spn s0,sp,32 -- s0 := the ENTRY sp                   *)
    (* ================================================================== *)
    assert (Hp08 : add_vec_int (mword_of_int (PA + 0x6) : mword 64) 2
                   = mword_of_int (PA + 0x8)) by pcw.
    iEval (rewrite Hp08) in "Hpc".
    iApply (wp_caddi4spn_s_sconf (CID := CID4) (mword_of_int (PA + 0x8))
              (Cregidx (mword_of_int 0)) (mword_of_int 8 : mword 8) Rs0
              P0 (K - 4)%nat b
              ltac:(vm_compute; reflexivity) ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hi08").
    iIntros (CID5 Hs5) "Hcg Hpc".
    set (P1 := <[Regidx Rs0 := regval_into_reg
                  (add_vec (P0 !!! Regidx csp_rs1)
                     (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8))))]> P0).
    (* ================================================================== *)
    (* +0x0a  c.mv s1,a0 -- park the message in a CALLEE-SAVED register   *)
    (* ================================================================== *)
    assert (Hrg0a : rget (CID := CID5) P1 Ra0 = P1 !!! Regidx Ra0)
      by (rgne; reflexivity).
    assert (Hp0a : add_vec_int (mword_of_int (PA + 0x8) : mword 64) 2
                   = mword_of_int (PA + 0xa)) by pcw.
    iEval (rewrite Hp0a) in "Hpc".
    iApply (wp_cmv_s_sconf (CID := CID5) (mword_of_int (PA + 0xa)) Rs1 Ra0
              P1 (K - 4)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi0a").
    iIntros (CID6 Hs6) "Hcg Hpc".
    iEval (rewrite Hrg0a) in "Hcg".
    set (P2 := <[Regidx Rs1 := regval_into_reg
                  (add_vec zero_reg (P1 !!! Regidx Ra0))]> P1).
    assert (HP2s1 : P2 !!! Regidx Rs1 = m !!! Regidx Ra0).
    { rewrite /P2 upd_eq add_vec_zero_l /P1 upd_ne; [| reg_neq].
      rewrite /P0 upd_ne; [reflexivity | reg_neq]. }
    (* ================================================================== *)
    (* +0x0c .. +0x10  a0 := "panic: "                                    *)
    (* ================================================================== *)
    assert (Hp0c : add_vec_int (mword_of_int (PA + 0xa) : mword 64) 2
                   = mword_of_int (PA + 0xc)) by pcw.
    iEval (rewrite Hp0c) in "Hpc".
    iApply (wp_auipc_s_sconf (CID := CID6) (mword_of_int (PA + 0xc)) Ra0
              (mword_of_int 6 : mword 20) P2 (K - 4)%nat b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi0c").
    iIntros (CID7 Hs7) "Hcg Hpc".
    set (P3 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (mword_of_int (PA + 0xc) : mword 64)
                     (auipc_off (mword_of_int 6 : mword 20)))]> P2).
    assert (Hrg10 : rget (CID := CID7) P3 Ra0 = P3 !!! Regidx Ra0)
      by (rgne; reflexivity).
    assert (Hp10 : add_vec_int (mword_of_int (PA + 0xc) : mword 64) 4
                   = mword_of_int (PA + 0x10)) by pcw.
    iEval (rewrite Hp10) in "Hpc".
    iApply (wp_addi4_s_sconf (CID := CID7) (mword_of_int (PA + 0x10)) Ra0 Ra0
              (mword_of_int 2040 : mword 12) P3 (K - 4)%nat b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi10").
    iIntros (CID8 Hs8) "Hcg Hpc".
    iEval (rewrite Hrg10) in "Hcg".
    set (P4 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (P3 !!! Regidx Ra0)
                     (sign_extend' 64 (mword_of_int 2040 : mword 12)))]> P3).
    assert (HP4a0 : P4 !!! Regidx Ra0 = (mword_of_int pn_hdr_a : mword 64)).
    { rewrite /P4 upd_eq /P3 upd_eq. unfold pn_hdr_a. pcw. }
    assert (HP4s1 : P4 !!! Regidx Rs1 = m !!! Regidx Ra0).
    { rewrite /P4 upd_ne; [| reg_neq]. rewrite /P3 upd_ne; [| reg_neq].
      exact HP2s1. }
    (* ================================================================== *)
    (* +0x14  jal ra,printk -- printk("panic: "), no varargs              *)
    (* ================================================================== *)
    assert (Hp14 : add_vec_int (mword_of_int (PA + 0x10) : mword 64) 4
                   = mword_of_int (PA + 0x14)) by pcw.
    iEval (rewrite Hp14) in "Hpc".
    iApply (wp_jal_s_sconf (CID := CID8) (mword_of_int (PA + 0x14)) Rra
              (mword_of_int 2096346 : mword 21) P4 (K - 4)%nat b
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi14").
    iIntros (CID9 Hs9) "Hcg Hpc".
    set (P5 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (PA + 0x14) : mword 64) 4)]> P4).
    assert (Htgt1 : add_vec (mword_of_int (PA + 0x14) : mword 64)
                      (sign_extend' 64 (mword_of_int 2096346 : mword 21))
                    = mword_of_int KernelSyms.printk) by pcw.
    iEval (rewrite Htgt1) in "Hpc".
    assert (HP5ra : P5 !!! Regidx Rra
                    = add_vec_int (mword_of_int (PA + 0x14) : mword 64) 4)
      by (rewrite /P5; apply upd_eq).
    assert (HP5a0 : P5 !!! Regidx Ra0 = (mword_of_int pn_hdr_a : mword 64))
      by (rewrite /P5 upd_ne; [exact HP4a0 | reg_neq]).
    assert (HP5s1 : P5 !!! Regidx Rs1 = m !!! Regidx Ra0)
      by (rewrite /P5 upd_ne; [exact HP4s1 | reg_neq]).
    iDestruct (cpu_own_transport CID CID9 n eb p C b
                 ltac:(wp_next_chain) with "Hown") as "Hown".
    iApply (Printk.wp_printk_sconf (CID := CID9) (dqf := DfracDiscarded)
              γpr γl γd γv P5 (K - 4)%nat bs n eb C pn_hdr [] b p
              (_ pn_Kpk K HK) pn_hdr_len pn_hdr_nonul
              ltac:(rewrite pn_hdr_kinds; reflexivity)
              ltac:(cbn [length]; lia) Hn31
              with "Hcg Hown Htext Hkdata Hpc Hpan [Hhdr] [] Hlk Hdev Htx Hsub").
    { rewrite HP5a0. iExact "Hhdr". }
    { done. }
    iIntros (CID10 Hs10 mf cs) "Hcg Hown Hpc %Hcs1 _ _ #Hsub1".
    destruct Hcs1 as (Hcs & _ & _).
    assert (Hpc18 : ret_pc (P5 !!! Regidx Rra : mword 64)
                    = mword_of_int (PA + 0x18)) by (rewrite HP5ra; pcw).
    iEval (rewrite Hpc18) in "Hpc".
    (* s1 came through the call: it is callee-saved, which is why gcc put the
       message there rather than leaving it in a0. *)
    assert (Hmfs1 : mf !!! Regidx Rs1 = m !!! Regidx Ra0).
    { rewrite (callee_saved_lookup Hcs Rs1 ltac:(vm_compute; reflexivity)).
      exact HP5s1. }
    (* ================================================================== *)
    (* +0x18  c.mv a1,s1 -- the message becomes the "%s" vararg           *)
    (* ================================================================== *)
    assert (Hrg18 : rget (CID := CID10) mf Rs1 = mf !!! Regidx Rs1)
      by (rgne; reflexivity).
    iApply (wp_cmv_s_sconf (CID := CID10) (mword_of_int (PA + 0x18)) Ra1 Rs1
              mf (K - 4)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi18").
    iIntros (CID11 Hs11) "Hcg Hpc".
    iEval (rewrite Hrg18) in "Hcg".
    set (Q0 := <[Regidx Ra1 := regval_into_reg
                  (add_vec zero_reg (mf !!! Regidx Rs1))]> mf).
    assert (HQ0a1 : Q0 !!! Regidx Ra1 = m !!! Regidx Ra0)
      by (rewrite /Q0 upd_eq add_vec_zero_l; exact Hmfs1).
    (* ================================================================== *)
    (* +0x1a .. +0x1e  a0 := "%s\n"                                       *)
    (* ================================================================== *)
    assert (Hp1a : add_vec_int (mword_of_int (PA + 0x18) : mword 64) 2
                   = mword_of_int (PA + 0x1a)) by pcw.
    iEval (rewrite Hp1a) in "Hpc".
    iApply (wp_auipc_s_sconf (CID := CID11) (mword_of_int (PA + 0x1a)) Ra0
              (mword_of_int 6 : mword 20) Q0 (K - 4)%nat b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi1a").
    iIntros (CID12 Hs12) "Hcg Hpc".
    set (Q1 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (mword_of_int (PA + 0x1a) : mword 64)
                     (auipc_off (mword_of_int 6 : mword 20)))]> Q0).
    assert (Hrg1e : rget (CID := CID12) Q1 Ra0 = Q1 !!! Regidx Ra0)
      by (rgne; reflexivity).
    assert (Hp1e : add_vec_int (mword_of_int (PA + 0x1a) : mword 64) 4
                   = mword_of_int (PA + 0x1e)) by pcw.
    iEval (rewrite Hp1e) in "Hpc".
    iApply (wp_addi4_s_sconf (CID := CID12) (mword_of_int (PA + 0x1e)) Ra0 Ra0
              (mword_of_int 2034 : mword 12) Q1 (K - 4)%nat b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi1e").
    iIntros (CID13 Hs13) "Hcg Hpc".
    iEval (rewrite Hrg1e) in "Hcg".
    set (Q2 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (Q1 !!! Regidx Ra0)
                     (sign_extend' 64 (mword_of_int 2034 : mword 12)))]> Q1).
    assert (HQ2a0 : Q2 !!! Regidx Ra0 = (mword_of_int pn_fmt_a : mword 64)).
    { rewrite /Q2 upd_eq /Q1 upd_eq. unfold pn_fmt_a. pcw. }
    assert (HQ2a1 : Q2 !!! Regidx Ra1 = m !!! Regidx Ra0).
    { rewrite /Q2 upd_ne; [| reg_neq]. rewrite /Q1 upd_ne; [| reg_neq].
      exact HQ0a1. }
    (* ================================================================== *)
    (* +0x22  jal ra,printk -- printk("%s\n", s)                          *)
    (* ================================================================== *)
    assert (Hp22 : add_vec_int (mword_of_int (PA + 0x1e) : mword 64) 4
                   = mword_of_int (PA + 0x22)) by pcw.
    iEval (rewrite Hp22) in "Hpc".
    iApply (wp_jal_s_sconf (CID := CID13) (mword_of_int (PA + 0x22)) Rra
              (mword_of_int 2096332 : mword 21) Q2 (K - 4)%nat b
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi22").
    iIntros (CID14 Hs14) "Hcg Hpc".
    set (Q3 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (PA + 0x22) : mword 64) 4)]> Q2).
    assert (Htgt2 : add_vec (mword_of_int (PA + 0x22) : mword 64)
                      (sign_extend' 64 (mword_of_int 2096332 : mword 21))
                    = mword_of_int KernelSyms.printk) by pcw.
    iEval (rewrite Htgt2) in "Hpc".
    assert (HQ3ra : Q3 !!! Regidx Rra
                    = add_vec_int (mword_of_int (PA + 0x22) : mword 64) 4)
      by (rewrite /Q3; apply upd_eq).
    assert (HQ3a0 : Q3 !!! Regidx Ra0 = (mword_of_int pn_fmt_a : mword 64))
      by (rewrite /Q3 upd_ne; [exact HQ2a0 | reg_neq]).
    (* vararg 0 IS a1 -- [pk_vararg Q3 0] is [Q3 !!! Regidx x11] by conversion *)
    assert (Hva : pk_vararg Q3 0%nat = m !!! Regidx Ra0) by exact HQ2a1.
    iDestruct (cpu_own_transport CID10 CID14 n eb p C b
                 ltac:(wp_next_chain) with "Hown") as "Hown".
    iApply (Printk.wp_printk_sconf (CID := CID14) (dqf := DfracDiscarded)
              γpr γl γd γv Q3 (K - 4)%nat (bs ++ cs)%list n eb C pn_fmt [dm] b p
              (pn_Kpk K HK) pn_fmt_len pn_fmt_nonul
              ltac:(rewrite pn_fmt_kinds; cbn [map pk_desc_kind];
                    rewrite Hdm; reflexivity)
              ltac:(cbn [length]; lia) Hn31
              with "Hcg Hown Htext Hkdata Hpc Hpan [Hfmt] [Hmsg] Hlk Hdev Htx Hsub1").
    { rewrite HQ3a0. iExact "Hfmt". }
    { rewrite big_sepL_singleton Hva. iExact "Hmsg". }
    iIntros (CID15 Hs15 mg cs2) "Hcg Hown Hpc %Hcs2 _ _ #Hsub2".
    assert (Hpc26 : ret_pc (Q3 !!! Regidx Rra : mword 64)
                    = mword_of_int (PA + 0x26)) by (rewrite HQ3ra; pcw).
    iEval (rewrite Hpc26) in "Hpc".
    (* ================================================================== *)
    (* +0x26  and here it stays.                                          *)
    (* ================================================================== *)
    iPoseProof (pn_spin with "Htext") as "Hspin".
    iApply ("Hspin" $! CID15 mg (K - 4)%nat b p with "Hcg Hpc").
  Qed.

End ProofPanic.
End PanicProof.
