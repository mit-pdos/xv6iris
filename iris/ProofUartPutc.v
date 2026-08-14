(* ProofUartPutc.v -- uartputc_sync over the SIE-agnostic sconf world.

     void uartputc_sync(int c) {
       acquire(&tx_lock);
       while ((ReadReg(LSR) & LSR_TX_IDLE) == 0) ;
       WriteReg(THR, c);
       release(&tx_lock);
     }

   THE PANIC PATH IS GONE.  printk.c's [panicking]/[panicked] globals are
   deleted upstream, and with them the guarded push_off/pop_off pair and the
   [if (panicked) for(;;)] spin.  What replaces them is a plain critical
   section: the poll/store pair now runs INSIDE [tx_lock] (a spinlock again),
   which is what makes this transmit path agree with uartwrite instead of
   racing it.  So this proof no longer reads a flag cell anywhere; the
   interrupt accounting comes entirely from acquire/release ([cpu_own]
   threaded net-zero, [arm_pay] routed from the one to the other), and the
   critical section runs at [b = false] over the avail count
   [trap_res b + av] acquire's push_off hands out.

   The transmitter token is the LOCK's resource ([UartTxInv.tx_res]): it comes
   out of the acquire at some trace [l] the caller cannot name, and goes back
   in at [l ++ [sb]] on the release.  The caller's own claim is therefore the
   SUBLIST form [UartTxInv.uart_sent_sub] -- another hart may have bytes
   accepted between two of ours -- obtained by pinning [bs `sublist_of` l]
   under [dev_inv] ([uart_tx_own_sent_sub]) while we hold the token, and
   cashed at the end with [uart_sent_sub_snoc].

   The device core (LSR poll loop + THR write) is unchanged in substance and
   still runs over the sconf leaves / the ProofUart accessor forms; only its
   addresses moved (a uniform -8) and its index is now literally [false].

   EXPLICIT-CPUID: [poll]/[devcore] are DECOMPOSED helper lemmas, each applied
   at a hart a [wp_next] crossing may have migrated to, so each gets its OWN
   implicit `{CID0 : CpuId} binder (shadowing the section Context) and wraps
   its OWN continuation in [wp_next b (fun CID => ...)].  [poll]'s Löb
   recursion additionally threads a per-iteration hart binder and re-anchors
   its held continuation with [wp_next_shift] before each recursive call.
   COLLISION: the polled LSR status byte is named [bt] throughout (the SIE
   index owns [b]). *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_var gen_heap invariants.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import InstrBytes.
Require Import KernelText.
Require Import RiscvExtras.
Require Import RegFile.
Require Import HartTp WpNext.
Require Import WpMmodeLeafBase.
Require Import SmodeCore.
Require Import StackOwn.
Require Import CalleeSaved.
Require Import VcGen WpSconfVc.
Require Import DiskPtsto WpUart.
Require Import IntrDefs.
Require Import CpuOwn.
Require Import WpLock.
Require Import UartTxInv.
Require Import WpSconfAlu WpSconfMem WpSconfBtype WpSconfCtl SpecUart.
Require Import CodeUartPutcSync.
Require Import WpSconfUartAccess.
Require Import SpecAcquire SpecRelease.
Require Import SpecUartPutc.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Require Import KernelRvcDecode.
Local Open Scope Z_scope.

(* ===================================================================== *)
(*  uartputc_sync's device core, as register-file transformers.  One      *)
(*  definition per device-core instruction that writes a GPR, named to    *)
(*  keep the WP threading readable (CodeMycpu-style).                     *)
(*                                                                        *)
(*    0x18  lui   a4,0x10000        -> ppc_f1                             *)
(*    0x1c  addi  a4,a4,5           -> ppc_f2                             *)
(*    0x1e  lbu   a5,0(a4)          -- LSR read (off 5)                   *)
(*    0x22  andi  a5,a5,32          -> ppc_f4' (loop exit, by exit byte)  *)
(*    0x28  zext.b a0,s1            -> ppc_f5'                            *)
(*    0x2c  lui   a5,0x10000        -> ppc_f6' (the pre-THR-store map)    *)
(*    0x30  sb    a0,0(a5)          -- THR write (off 0)                  *)
(* ===================================================================== *)
Section UartPutcMaps.
  Context `{!riscvGS Σ}.

  Definition ppc_f1 (m : regfile) : regfile :=
    <[Regidx (mword_of_int 14) := regval_into_reg (luival (mword_of_int 0x10000 : mword 20))]> m.
  Definition ppc_f2 (m : regfile) : regfile :=
    <[Regidx (mword_of_int 14) := regval_into_reg (add_vec (ppc_f1 m !!! Regidx (mword_of_int 14))
        (sign_extend' 64 (sign_extend' 12 (mword_of_int 5 : mword 6))))]> (ppc_f1 m).

  (* the call-site register lookup the LSR-read leaf needs. *)
  Lemma ppc_f2_a4 (m : regfile) :
    ppc_f2 m !!! Regidx (mword_of_int 14) = uart_pa 5.
  Proof.
    unfold ppc_f2, ppc_f1. rewrite !upd_eq.
    apply bv_eq; vm_compute; reflexivity.
  Qed.

  (* The mask [andi a5,a5,32] applied to the LSR-load value for a read byte. *)
  Definition lsr_masked (b : bv 8) : mword 64 :=
    and_vec (lsr_ldval_of b) (sign_extend' 64 (mword_of_int 32 : mword 12)).

  (* The post-loop register maps, indexed by the EXIT byte [b] the poll
     observed (not by a UART state, which the caller can no longer name). *)
  Definition ppc_f4' (m : regfile) (b : bv 8) : regfile :=
    <[Regidx (mword_of_int 15) := regval_into_reg (lsr_masked b)]> (ppc_f2 m).
  Definition ppc_f5' (m : regfile) (b : bv 8) : regfile :=
    <[Regidx (mword_of_int 10) := regval_into_reg (and_vec (ppc_f4' m b !!! Regidx (mword_of_int 9))
        (sign_extend' 64 (mword_of_int 255 : mword 12)))]> (ppc_f4' m b).
  Definition ppc_f6' (m : regfile) (b : bv 8) : regfile :=
    <[Regidx (mword_of_int 15) := regval_into_reg (luival (mword_of_int 0x10000 : mword 20))]> (ppc_f5' m b).

  Lemma ppc_f4'_s1 (m : regfile) (b : bv 8) :
    ppc_f4' m b !!! Regidx (mword_of_int 9) = m !!! Regidx (mword_of_int 9).
  Proof.
    unfold ppc_f4', ppc_f2, ppc_f1.
    do 3 (rewrite upd_ne; [| vm_compute; discriminate]). reflexivity.
  Qed.

  Lemma ppc_f6'_a5 (m : regfile) (b : bv 8) :
    ppc_f6' m b !!! Regidx (mword_of_int 15) = uart_pa 0.
  Proof.
    unfold ppc_f6'. rewrite upd_eq.
    apply bv_eq; vm_compute; reflexivity.
  Qed.

  Lemma ppc_f6'_a0 (m : regfile) (b : bv 8) :
    ppc_f6' m b !!! Regidx (mword_of_int 10)
    = and_vec (m !!! Regidx (mword_of_int 9)) (sign_extend' 64 (mword_of_int 255 : mword 12)).
  Proof.
    unfold ppc_f6', ppc_f5'.
    rewrite upd_ne; [| vm_compute; discriminate].
    rewrite upd_eq. rewrite ppc_f4'_s1. reflexivity.
  Qed.

  (* a callee-saved index survives the whole device core: it writes only
     a4/a5/a0. *)
  Lemma ppc_f6'_cs (m : regfile) (bt : bv 8) (c : mword 5) :
    c <> mword_of_int 14 -> c <> mword_of_int 15 -> c <> mword_of_int 10 ->
    ppc_f6' m bt !!! Regidx c = m !!! Regidx c.
  Proof.
    intros N14 N15 N10.
    unfold ppc_f6', ppc_f5', ppc_f4', ppc_f2, ppc_f1.
    rewrite upd_ne; [| congruence].
    rewrite upd_ne; [| congruence].
    rewrite upd_ne; [| congruence].
    rewrite upd_ne; [| congruence].
    rewrite upd_ne; [reflexivity | congruence].
  Qed.

End UartPutcMaps.

Module UartPutcProof (Uart : UART) (Acquire : ACQUIRE) (Release : RELEASE) : UARTPUTC.

(* The base ALU leaves ([wp_lui_s_sconf], [wp_andi_s_sconf]) live in
   WpSconfAlu.v; the call-site-specialized UART device leaves
   ([wp_uart_lsr_read_s_sconf], [wp_uart_thr_write_s_sconf]) live in the
   WpSconfUartAccess.v leaf functor.  Instantiate the latter against this
   proof's sealed [Uart]. *)
Module UAcc := UartAccessProof Uart.

Section ProofUartPutc.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ}.
  Context `{!uartGhostG Σ, !diskGhostG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.


  (* [rget m k] at a NON-tp index is the plain map lookup ([rget_ne]) -- the
     one-line bridge from a leaf's [rget] to the register-map facts a
     whole-function proof already has.  Written name-free (durable-notes: an
     Ltac body cannot mention a hypothesis by literal name). *)
  Local Ltac rgne :=
    rewrite rget_ne;
    [ | let H1 := fresh in let H2 := fresh in
        intro H1; injection H1 as H2; vm_compute in H2; congruence ].

  (* =================================================================== *)
  (*  THE THRE POLL LOOP: 0x1e -> 0x28, run under [dev_inv] (Löb).        *)
  (* =================================================================== *)
  Lemma wp_uartputc_poll_sconf `{CID0 : CpuId} (γd : uart_names) (γv : disk_names) (mentry : regfile) (n : nat) (l : list (bv 8)) (b : bool) (p : mword 64) :
    mentry !!! Regidx (mword_of_int 14) = uart_pa 5 ->
    sie_cap_gpr mentry n b p -∗ kernel_text -∗
    pc_is (mword_of_int (KernelSyms.uartputc_sync + 0x1e)) -∗
    dev_inv γd γv -∗ uart_tx_own γd l -∗
    wp_next b p (fun (CID : CpuId) =>
      ∀ bt : bv 8,
      sie_cap_gpr (<[Regidx (mword_of_int 15) := regval_into_reg (lsr_masked bt)]> mentry) n b p -∗
      pc_is (mword_of_int (KernelSyms.uartputc_sync + 0x28)) -∗
      uart_tx_own γd l -∗ uart_out_lb γd l -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Ha4e.
    iIntros "Hcg #Ht Hpc #Hdinv Hown Hcont".
    iDestruct (upi_1e with "Ht") as "#Hi1e".
    iDestruct (upi_22 with "Ht") as "#Hi22".
    iDestruct (upi_26 with "Ht") as "#Hi26".
    assert (P22 : add_vec_int (mword_of_int (KernelSyms.uartputc_sync + 0x1e) : mword 64) 4 = mword_of_int (KernelSyms.uartputc_sync + 0x22)) by (apply bv_eq; vm_compute; reflexivity).
    assert (P26 : add_vec_int (mword_of_int (KernelSyms.uartputc_sync + 0x22) : mword 64) 4 = mword_of_int (KernelSyms.uartputc_sync + 0x26)) by (apply bv_eq; vm_compute; reflexivity).
    assert (P28 : add_vec_int (mword_of_int (KernelSyms.uartputc_sync + 0x26) : mword 64) 2 = mword_of_int (KernelSyms.uartputc_sync + 0x28)) by (apply bv_eq; vm_compute; reflexivity).
    assert (Htgt : add_vec (mword_of_int (KernelSyms.uartputc_sync + 0x26) : mword 64)
                     (sign_extend' 64 (sign_extend' 13 (concat_vec (mword_of_int 252 : mword 8) ('b"0"))))
                   = mword_of_int (KernelSyms.uartputc_sync + 0x1e)) by (apply bv_eq; vm_compute; reflexivity).
    iAssert (∀ (CID1 : CpuId) (m : regfile),
      ⌜ m !!! Regidx (mword_of_int 14) = uart_pa 5 ⌝ -∗
      ⌜ forall Y, <[Regidx (mword_of_int 15) := Y]> m
                = <[Regidx (mword_of_int 15) := Y]> mentry ⌝ -∗
      sie_cap_gpr m n b p -∗ pc_is (mword_of_int (KernelSyms.uartputc_sync + 0x1e)) -∗ uart_tx_own γd l -∗
      wp_next (CID0:=CID1) b p (fun (CID : CpuId) =>
        ∀ bt : bv 8, sie_cap_gpr (<[Regidx (mword_of_int 15) := regval_into_reg (lsr_masked bt)]> mentry) n b p -∗
            pc_is (mword_of_int (KernelSyms.uartputc_sync + 0x28)) -∗
            uart_tx_own γd l -∗ uart_out_lb γd l -∗ WP (Loop : expr riscv_lang)) -∗
      WP (Loop : expr riscv_lang))%I with "[]" as "Loop".
    { iLöb as "IH". iIntros (CID1 m Ha4m Hagm) "Hcg Hpc Hown Hk".
      (* 0x1e  lbu a5,0(a4) *)
      iApply (UAcc.wp_uart_lsr_read_s_sconf (CID:=CID1) γd γv (mword_of_int (KernelSyms.uartputc_sync + 0x1e)) (mword_of_int 15) (mword_of_int 14)
                m n l b ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(rgne; exact Ha4m)
                with "Hcg Hpc Hi1e Hdinv Hown").
      iIntros (CIDr Hsr bt) "Hcg Hpc Hown Hlb".
      iEval (rewrite P22) in "Hpc".
      (* 0x22  andi a5,a5,32 *)
      iApply (wp_andi_s_sconf (mword_of_int (KernelSyms.uartputc_sync + 0x22)) (mword_of_int 15) (mword_of_int 15) (mword_of_int 32 : mword 12)
                _ (<[Regidx (mword_of_int 15) := regval_into_reg (lsr_ldval_of bt)]> m) n b
                ltac:(vm_compute; discriminate) ltac:(rdok) eq_refl
                with "Hcg Hpc Hi22").
      iIntros (CIDa Hsa) "Hcg Hpc".
      iEval (rgne) in "Hcg".
      iEval (rewrite upd_eq upd_upd) in "Hcg".
      change (and_vec (lsr_ldval_of bt) (sign_extend' 64 (mword_of_int 32 : mword 12)))
        with (lsr_masked bt) in *.
      iEval (rewrite P26) in "Hpc".
      (* 0x26  c.beqz a5,0x1e *)
      destruct (lsr_thre_clear bt) eqn:Hcase.
      - iApply (wp_cbeqz_taken_s_sconf (mword_of_int (KernelSyms.uartputc_sync + 0x26)) (mword_of_int 252 : mword 8)
                  (Cregidx (mword_of_int 7)) (mword_of_int 15)
                  (<[Regidx (mword_of_int 15) := regval_into_reg (lsr_masked bt)]> m) n b
                  ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                  ltac:(rgne; rewrite upd_eq; unfold regval_into_reg, lsr_masked; exact Hcase)
                  ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc Hi26").
        (* NOT convertible to [bi.later_intro]: this is the Loeb back edge --
           the continuation this specializes against is itself under a [▷], so
           the later has to come off a HYPOTHESIS, not just the goal. *)
        iNext. iIntros (CIDt Hst) "Hcg Hpc".
        iEval (rewrite Htgt) in "Hpc".
        assert (Hchain : b = false \/ p = zero_reg -> (CIDt : CPU) = (CID1 : CPU)) by wp_next_chain.
        iDestruct (wp_next_shift Hchain with "Hk") as "Hk".
        iApply ("IH" $! CIDt (<[Regidx (mword_of_int 15) := regval_into_reg (lsr_masked bt)]> m)
                  with "[%] [%] Hcg Hpc Hown Hk").
        + rewrite upd_ne; [exact Ha4m | vm_compute; discriminate].
        + intro Y. rewrite upd_upd. exact (Hagm Y).
      - iApply (wp_cbeqz_fall_s_sconf (mword_of_int (KernelSyms.uartputc_sync + 0x26)) (mword_of_int 252 : mword 8)
                  (Cregidx (mword_of_int 7)) (mword_of_int 15)
                  (<[Regidx (mword_of_int 15) := regval_into_reg (lsr_masked bt)]> m) n b
                  ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                  ltac:(rgne; rewrite upd_eq; unfold regval_into_reg, lsr_masked; exact Hcase)
                  with "Hcg Hpc Hi26").
        iIntros (CIDf Hsf) "Hcg Hpc".
        iEval (rewrite P28) in "Hpc".
        iEval (rewrite (Hagm (regval_into_reg (lsr_masked bt)))) in "Hcg".
        assert (Hchainf : b = false \/ p = zero_reg -> (CIDf : CPU) = (CID1 : CPU)) by wp_next_chain.
        iSpecialize ("Hk" $! CIDf with "[%]"); [exact Hchainf|].
        iApply ("Hk" $! bt with "Hcg Hpc Hown").
        by iApply "Hlb". }
    iApply ("Loop" $! CID0 mentry with "[%] [%] Hcg Hpc Hown Hcont").
    - exact Ha4e.
    - reflexivity.
  Qed.

  (* =================================================================== *)
  (*  DEVICE CORE: 0x18 -> 0x34 (lui/addi + poll + zext.b + lui + THR).    *)
  (* =================================================================== *)
  Lemma wp_uartputc_devcore_sconf `{CID0 : CpuId} (γd : uart_names) (γv : disk_names)
      (m : regfile) (n : nat) (l : list (bv 8)) (b : bool) (p : mword 64) :
    let sb : mword 8 := autocast (T := mword)
       (subrange_vec_dec (and_vec (m !!! Regidx (mword_of_int 9))
          (sign_extend' 64 (mword_of_int 255 : mword 12))) 7 0) in
    sie_cap_gpr m n b p -∗ kernel_text -∗
    pc_is (mword_of_int (KernelSyms.uartputc_sync + 0x18)) -∗
    dev_inv γd γv -∗ uart_tx_own γd l -∗ uart_dlab_off γd -∗
    wp_next b p (fun (CID : CpuId) =>
      ∀ bt : bv 8,
      sie_cap_gpr (ppc_f6' m bt) n b p -∗ pc_is (mword_of_int (KernelSyms.uartputc_sync + 0x34)) -∗
      uart_tx_own γd (l ++ [sb]) -∗ uart_sent γd (l ++ [sb]) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros sb.
    iIntros "Hcg #Ht Hpc #Hdinv Hown #Hoff Hcont".
    assert (P1c : add_vec_int (mword_of_int (KernelSyms.uartputc_sync + 0x18) : mword 64) 4 = mword_of_int (KernelSyms.uartputc_sync + 0x1c)) by (apply bv_eq; vm_compute; reflexivity).
    assert (P1e : add_vec_int (mword_of_int (KernelSyms.uartputc_sync + 0x1c) : mword 64) 2 = mword_of_int (KernelSyms.uartputc_sync + 0x1e)) by (apply bv_eq; vm_compute; reflexivity).
    assert (P2c : add_vec_int (mword_of_int (KernelSyms.uartputc_sync + 0x28) : mword 64) 4 = mword_of_int (KernelSyms.uartputc_sync + 0x2c)) by (apply bv_eq; vm_compute; reflexivity).
    assert (P30 : add_vec_int (mword_of_int (KernelSyms.uartputc_sync + 0x2c) : mword 64) 4 = mword_of_int (KernelSyms.uartputc_sync + 0x30)) by (apply bv_eq; vm_compute; reflexivity).
    assert (P34 : add_vec_int (mword_of_int (KernelSyms.uartputc_sync + 0x30) : mword 64) 4 = mword_of_int (KernelSyms.uartputc_sync + 0x34)) by (apply bv_eq; vm_compute; reflexivity).
    iPoseProof (upi_18 with "Ht") as "Hi18".
    iPoseProof (upi_1c with "Ht") as "Hi1c".
    iPoseProof (upi_28 with "Ht") as "Hi28".
    iPoseProof (upi_2c with "Ht") as "Hi2c".
    iPoseProof (upi_30 with "Ht") as "Hi30".
    (* 0x18  lui a4,0x10000 *)
    iApply (wp_lui_s_sconf (mword_of_int (KernelSyms.uartputc_sync + 0x18)) (mword_of_int 14) (mword_of_int 0x10000 : mword 20)
              (luival (mword_of_int 0x10000 : mword 20)) m n b
              ltac:(vm_compute; discriminate) ltac:(rdok) eq_refl
              with "Hcg Hpc Hi18").
    iIntros (CID1 Hs1) "Hcg Hpc".
    iEval (rewrite P1c) in "Hpc".
    (* 0x1c  c.addi a4,a4,5 *)
    iApply (wp_caddi_s_sconf (mword_of_int (KernelSyms.uartputc_sync + 0x1c)) (mword_of_int 14) (mword_of_int 5 : mword 6)
              (ppc_f1 m) n b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi1c").
    iIntros (CID2 Hs2) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    iEval (change (<[Regidx (mword_of_int 14) := regval_into_reg
        (add_vec (ppc_f1 m !!! Regidx (mword_of_int 14)) (sign_extend' 64 (sign_extend' 12 (mword_of_int 5 : mword 6))))]> (ppc_f1 m))
      with (ppc_f2 m)) in "Hcg".
    iEval (rewrite P1e) in "Hpc".
    (* 0x1e -> 0x28  the poll loop *)
    iApply (wp_uartputc_poll_sconf (CID0:=CID2) γd γv (ppc_f2 m) n l b p (ppc_f2_a4 m)
              with "Hcg Ht Hpc Hdinv Hown").
    iIntros (CIDp Hsp bt) "Hcg Hpc Hown #Hlb".
    iEval (change (<[Regidx (mword_of_int 15) := regval_into_reg (lsr_masked bt)]> (ppc_f2 m))
             with (ppc_f4' m bt)) in "Hcg".
    (* 0x28  zext.b a0,s1  (andi a0,s1,255) *)
    iApply (wp_andi_s_sconf (mword_of_int (KernelSyms.uartputc_sync + 0x28)) (mword_of_int 10) (mword_of_int 9) (mword_of_int 255 : mword 12)
              _ (ppc_f4' m bt) n b ltac:(vm_compute; discriminate) ltac:(rdok) eq_refl
              with "Hcg Hpc Hi28").
    iIntros (CID3 Hs3) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    iEval (change (<[Regidx (mword_of_int 10) := regval_into_reg (and_vec (ppc_f4' m bt !!! Regidx (mword_of_int 9))
             (sign_extend' 64 (mword_of_int 255 : mword 12)))]> (ppc_f4' m bt))
      with (ppc_f5' m bt)) in "Hcg".
    iEval (rewrite P2c) in "Hpc".
    (* 0x2c  lui a5,0x10000 *)
    iApply (wp_lui_s_sconf (mword_of_int (KernelSyms.uartputc_sync + 0x2c)) (mword_of_int 15) (mword_of_int 0x10000 : mword 20)
              (luival (mword_of_int 0x10000 : mword 20)) (ppc_f5' m bt) n b
              ltac:(vm_compute; discriminate) ltac:(rdok) eq_refl
              with "Hcg Hpc Hi2c").
    iIntros (CID4 Hs4) "Hcg Hpc".
    iEval (change (<[Regidx (mword_of_int 15) := regval_into_reg (luival (mword_of_int 0x10000 : mword 20))]> (ppc_f5' m bt))
             with (ppc_f6' m bt)) in "Hcg".
    iEval (rewrite P30) in "Hpc".
    (* 0x30  sb a0,0(a5)  -- THR write *)
    assert (Hsbb : (autocast (T := mword)
                      (subrange_vec_dec (rget (ppc_f6' m bt) (mword_of_int 10 : mword 5))
                         (Z.sub (Z.mul 1 8) 1) 0) : mword 8) = sb).
    { rewrite (rget_ne (ppc_f6' m bt) (mword_of_int 10 : mword 5) ltac:(vm_compute; discriminate)).
      unfold sb. rewrite ppc_f6'_a0. reflexivity. }
    iApply (UAcc.wp_uart_thr_write_s_sconf (CID:=CID4) γd γv (mword_of_int (KernelSyms.uartputc_sync + 0x30)) (mword_of_int 10) (mword_of_int 15)
              (ppc_f6' m bt) n l b ltac:(rgne; exact (ppc_f6'_a5 m bt))
              with "Hcg Hpc Hi30 Hdinv Hown Hlb Hoff").
    iIntros (CID5 Hs5) "Hcg Hpc Hown Hsent".
    iEval (rewrite Hsbb) in "Hown". iEval (rewrite Hsbb) in "Hsent".
    iEval (rewrite P34) in "Hpc".
    assert (Hchain : b = false \/ p = zero_reg -> (CID5 : CPU) = (CID0 : CPU)) by wp_next_chain.
    iSpecialize ("Hcont" $! CID5 with "[%]"); [exact Hchain|].
    iApply ("Hcont" $! bt with "Hcg Hpc Hown Hsent").
  Qed.

  (* =================================================================== *)
  (*  THE WHOLE FUNCTION.                                                  *)
  (* =================================================================== *)
  Lemma wp_uartputc_sconf (γl : gname) (γd : uart_names) (γv : disk_names)
      (m0 : regfile) (K : nat) (bs : list (bv 8)) (n : nat) (eb : bool)
      (C : iProp Σ) (b : bool) (p : mword 64) (lks : gset nat)
    : wp_uartputc_sconf_body γl γd γv m0 K bs n eb C b p lks.
  Proof.
    cbv beta delta [wp_uartputc_sconf_body].
    intros ra_idx a0_idx pcE ra0 a00 ret_tgt sb HK Hn.
    assert (HK14 : (14 <= K)%nat) by (unfold uartputc_stack in HK; exact HK).
    assert (HK4 : (4 <= K)%nat) by lia.
    assert (Hav : (10 <= K - 4)%nat) by lia.
    pose (sp0 := (m0 !!! Regidx csp_rs1 : mword 64)).
    iIntros "Hcg Hcpu #Ht Hpc #Hpanic #Hdinv #Htxl #Hsubbs Hcont".
    iDestruct (cpu_own_eb_agree with "Hcg Hcpu") as %Hbeq.
    iDestruct (is_txlock_lock with "Htxl") as "#Hlk".
    iDestruct (is_txlock_dlab with "Htxl") as "#Hoff".
    set (spr := add_vec (m0 !!! Regidx csp_rs1 : mword 64) (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6)))).
    iPoseProof (upi_00 with "Ht") as "Hi00".
    iPoseProof (upi_02 with "Ht") as "Hi02".
    iPoseProof (upi_04 with "Ht") as "Hi04".
    iPoseProof (upi_06 with "Ht") as "Hi06".
    iPoseProof (upi_08 with "Ht") as "Hi08".
    iPoseProof (upi_0a with "Ht") as "Hi0a".
    iPoseProof (upi_0c with "Ht") as "Hi0c".
    iPoseProof (upi_10 with "Ht") as "Hi10".
    iPoseProof (upi_14 with "Ht") as "Hi14".
    iPoseProof (upi_34 with "Ht") as "Hi34".
    iPoseProof (upi_38 with "Ht") as "Hi38".
    iPoseProof (upi_3c with "Ht") as "Hi3c".
    iPoseProof (upi_40 with "Ht") as "Hi40".
    iPoseProof (upi_42 with "Ht") as "Hi42".
    iPoseProof (upi_44 with "Ht") as "Hi44".
    iPoseProof (upi_46 with "Ht") as "Hi46".
    iPoseProof (upi_48 with "Ht") as "Hi48".
    (* ===== PROLOGUE: 4-slot frame push + 3 saves (ra/s0/s1) + padding ===== *)
    set (R1 := <[Regidx csp_rs1 := regval_into_reg (add_vec (m0 !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))))]> m0).
    (* +0x00 c.addi sp,-32 -- push 4 *)
    assert (Hpush : spr = pa_stk sp0 4).
    { unfold spr, sp0, pa_stk, add_vec_int. apply f_equal.
      apply bv_eq; vm_compute; reflexivity. }
    iApply (wp_caddi_sp_push_s_sconf pcE (mword_of_int 32 : mword 6) m0 K 4 b HK4 Hpush
              with "Hcg Hpc Hi00").
    iIntros (CIDp1 Hsp1) "Hcg Hframe Hpc".
    assert (HspR1 : R1 !!! Regidx csp_rs1 = spr)
      by (rewrite /R1 upd_eq; reflexivity).
    iEval (rewrite stack_own_slots; cbn [seq]) in "Hframe".
    iDestruct "Hframe" as "(S1 & S2 & S3 & S4 & _)".
    iDestruct "S1" as (vr24) "Hr24". iDestruct "S2" as (vr16) "Hr16".
    iDestruct "S3" as (vr8)  "Hr8".  iDestruct "S4" as (vg4)  "Hg4".
    assert (Hb1 : add_vec (R1 !!! Regidx csp_rs1) (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000"))) = pa_stk sp0 1).
    { rewrite HspR1. unfold spr, sp0, pa_stk, add_vec_int. rewrite add_vec_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb2 : add_vec (R1 !!! Regidx csp_rs1) (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000"))) = pa_stk sp0 2).
    { rewrite HspR1. unfold spr, sp0, pa_stk, add_vec_int. rewrite add_vec_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb3 : add_vec (R1 !!! Regidx csp_rs1) (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) = pa_stk sp0 3).
    { rewrite HspR1. unfold spr, sp0, pa_stk, add_vec_int. rewrite add_vec_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb4 : add_vec (R1 !!! Regidx csp_rs1) (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000"))) = pa_stk sp0 4).
    { rewrite HspR1. unfold spr, sp0, pa_stk, add_vec_int. rewrite add_vec_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    iEval (rewrite -Hb1) in "Hr24". iEval (rewrite -Hb2) in "Hr16".
    iEval (rewrite -Hb3) in "Hr8".  iEval (rewrite -Hb4) in "Hg4".
    assert (Hpp02 : add_vec_int (pcE : mword 64) 2 = mword_of_int (KernelSyms.uartputc_sync + 0x02)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp02) in "Hpc".
    (* +0x02 c.sdsp ra,24(sp) *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.uartputc_sync + 0x02)) (mword_of_int 3 : mword 6) (mword_of_int 1 : mword 5)
              R1 (K - 4)%nat vr24 b with "Hcg Hpc Hi02 Hr24").
    iIntros (CIDp2 Hsp2) "Hcg Hpc Hr24".
    assert (Hpp04 : add_vec_int (mword_of_int (KernelSyms.uartputc_sync + 0x02) : mword 64) 2 = mword_of_int (KernelSyms.uartputc_sync + 0x04)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp04) in "Hpc".
    (* +0x04 c.sdsp s0,16(sp) *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.uartputc_sync + 0x04)) (mword_of_int 2 : mword 6) (mword_of_int 8 : mword 5)
              R1 (K - 4)%nat vr16 b with "Hcg Hpc Hi04 Hr16").
    iIntros (CIDp3 Hsp3) "Hcg Hpc Hr16".
    assert (Hpp06 : add_vec_int (mword_of_int (KernelSyms.uartputc_sync + 0x04) : mword 64) 2 = mword_of_int (KernelSyms.uartputc_sync + 0x06)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp06) in "Hpc".
    (* +0x06 c.sdsp s1,8(sp) *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.uartputc_sync + 0x06)) (mword_of_int 1 : mword 6) (mword_of_int 9 : mword 5)
              R1 (K - 4)%nat vr8 b with "Hcg Hpc Hi06 Hr8").
    iIntros (CIDp4 Hsp4) "Hcg Hpc Hr8".
    assert (Hpp08 : add_vec_int (mword_of_int (KernelSyms.uartputc_sync + 0x06) : mword 64) 2 = mword_of_int (KernelSyms.uartputc_sync + 0x08)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp08) in "Hpc".
    (* +0x08 c.addi4spn s0,sp,32 *)
    iApply (wp_caddi4spn_s_sconf (mword_of_int (KernelSyms.uartputc_sync + 0x08)) (Cregidx (mword_of_int 0)) (mword_of_int 8 : mword 8) (mword_of_int 8 : mword 5)
              R1 (K - 4)%nat b ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi08").
    iIntros (CIDp5 Hsp5) "Hcg Hpc".
    set (R2 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg (add_vec (R1 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8))))]> R1).
    assert (Hpp0a : add_vec_int (mword_of_int (KernelSyms.uartputc_sync + 0x08) : mword 64) 2 = mword_of_int (KernelSyms.uartputc_sync + 0x0a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0a) in "Hpc".
    (* +0x0a c.mv s1,a0 *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.uartputc_sync + 0x0a)) (mword_of_int 9 : mword 5) (mword_of_int 10 : mword 5)
              R2 (K - 4)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi0a").
    iIntros (CIDp6 Hsp6) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (R3 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (add_vec zero_reg (R2 !!! Regidx (mword_of_int 10 : mword 5)))]> R2).
    assert (Hpp0c : add_vec_int (mword_of_int (KernelSyms.uartputc_sync + 0x0a) : mword 64) 2 = mword_of_int (KernelSyms.uartputc_sync + 0x0c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0c) in "Hpc".
    (* a0 is preserved through the prologue, so R3!!!s1 = add zero a00 *)
    assert (HR2a0 : R2 !!! Regidx (mword_of_int 10 : mword 5) = a00).
    { rewrite /R2 upd_ne; [| vm_compute; discriminate].
      rewrite /R1 upd_ne; [reflexivity | vm_compute; discriminate]. }
    assert (HR3s1 : R3 !!! Regidx (mword_of_int 9 : mword 5) = add_vec zero_reg a00).
    { rewrite /R3 upd_eq. unfold regval_into_reg. rewrite HR2a0. reflexivity. }
    (* ===== &tx_lock, then acquire (0x0c .. 0x14) ===== *)
    (* +0x0c auipc a0,0x12 *)
    iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.uartputc_sync + 0x0c)) (mword_of_int 10) (mword_of_int 18 : mword 20)
              R3 (K - 4)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi0c").
    iIntros (CIDp7 Hsp7) "Hcg Hpc".
    set (G0c := <[Regidx (mword_of_int 10) := regval_into_reg (add_vec (mword_of_int (KernelSyms.uartputc_sync + 0x0c)) (auipc_off (mword_of_int 18 : mword 20)))]> R3).
    assert (Hpp10 : add_vec_int (mword_of_int (KernelSyms.uartputc_sync + 0x0c) : mword 64) 4 = mword_of_int (KernelSyms.uartputc_sync + 0x10)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp10) in "Hpc".
    (* +0x10 addi a0,a0,-1544 -> &tx_lock *)
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.uartputc_sync + 0x10)) (mword_of_int 10) (mword_of_int 10) (mword_of_int 2574 : mword 12)
              G0c (K - 4)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi10").
    iIntros (CIDp8 Hsp8) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (G10 := <[Regidx (mword_of_int 10) := regval_into_reg (add_vec (G0c !!! Regidx (mword_of_int 10 : mword 5)) (sign_extend' 64 (mword_of_int 2574 : mword 12)))]> G0c).
    assert (HG10a0 : G10 !!! Regidx (mword_of_int 10 : mword 5) = a_tx_lock).
    { rewrite /G10 upd_eq. rewrite /G0c upd_eq.
      unfold a_tx_lock. apply bv_eq; vm_compute; reflexivity. }
    assert (Hpp14 : add_vec_int (mword_of_int (KernelSyms.uartputc_sync + 0x10) : mword 64) 4 = mword_of_int (KernelSyms.uartputc_sync + 0x14)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp14) in "Hpc".
    (* +0x14 jal ra,acquire *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.uartputc_sync + 0x14)) (mword_of_int 1 : mword 5) (mword_of_int 592 : mword 21)
              G10 (K - 4)%nat b ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi14").
    iIntros (CIDp9 Hsp9) "Hcg Hpc".
    set (G14 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.uartputc_sync + 0x14) : mword 64) 4)]> G10).
    assert (Hjacq : add_vec (mword_of_int (KernelSyms.uartputc_sync + 0x14) : mword 64) (sign_extend' 64 (mword_of_int 592 : mword 21)) = mword_of_int KernelSyms.acquire)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hjacq) in "Hpc".
    assert (HG14a0 : G14 !!! Regidx (mword_of_int 10 : mword 5) = a_tx_lock)
      by (rewrite /G14 upd_ne; [exact HG10a0 | vm_compute; discriminate]).
    assert (HG14ra : G14 !!! Regidx (mword_of_int 1 : mword 5)
                     = regval_into_reg (add_vec_int (mword_of_int (KernelSyms.uartputc_sync + 0x14) : mword 64) 4))
      by (rewrite /G14 upd_eq; reflexivity).
    assert (HG14s1 : G14 !!! Regidx (mword_of_int 9 : mword 5) = add_vec zero_reg a00).
    { rewrite /G14 upd_ne; [| vm_compute; discriminate].
      rewrite /G10 upd_ne; [| vm_compute; discriminate].
      rewrite /G0c upd_ne; [| vm_compute; discriminate]. exact HR3s1. }
    (* ===== acquire(&tx_lock) ===== *)
    iDestruct (cpu_own_transport CID CIDp9 n eb p C b ltac:(wp_next_chain)
                 with "Hcpu") as "Hcpu".
    iApply (Acquire.wp_acquire_sconf γl "uart"%string (tx_res γd) G14 n eb p C (K - 4)%nat b
              _ Hn Hav with "Hcg Hcpu Ht Hpc [Hlk] Hpanic").
    { iEval (rewrite HG14a0). iExact "Hlk". }
    iIntros (CIDacq Hsacq ms macq) "%Hmsf Hcg Hpc %Hcs_acq Hlocked HR Hcpu Hpay".
    assert (Hret14 : ret_pc (G14 !!! Regidx (mword_of_int 1 : mword 5)) = mword_of_int (KernelSyms.uartputc_sync + 0x18))
      by (rewrite HG14ra; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hret14) in "Hpc".
    (* the transmitter comes out of the lock at some trace [l], and our
       persistent [bs] claim is pinned to it under [dev_inv]. *)
    iDestruct "HR" as (l) "Hown".
    iApply fupd_wp.
    iMod (uart_tx_own_sent_sub γd γv l bs ⊤ ltac:(solve_ndisj)
            with "Hdinv Hown Hsubbs") as "[Hown %Hsl]".
    iModIntro.
    (* the stored byte, read off s1, is the contract's [sb] *)
    assert (Hmacqs1 : macq !!! Regidx (mword_of_int 9 : mword 5) = add_vec zero_reg a00).
    { rewrite (callee_saved_lookup Hcs_acq (mword_of_int 9 : mword 5) ltac:(vm_compute; reflexivity)).
      exact HG14s1. }
    assert (Hsbm : (autocast (T := mword)
                      (subrange_vec_dec (and_vec (macq !!! Regidx (mword_of_int 9))
                         (sign_extend' 64 (mword_of_int 255 : mword 12))) 7 0) : mword 8) = sb).
    { unfold sb. rewrite Hmacqs1. reflexivity. }
    (* ===== 0x18 -> 0x34: the device core, inside the critical section ===== *)
    iApply (wp_uartputc_devcore_sconf (CID0:=CIDacq) γd γv macq (trap_res b + (K - 4))%nat l false p
              with "Hcg Ht Hpc Hdinv Hown Hoff").
    iApply wp_next_off_intro.
    iIntros (bt) "Hcg Hpc Hown Hsent".
    iEval (rewrite Hsbm) in "Hown". iEval (rewrite Hsbm) in "Hsent".
    (* the caller's sublist claim, cashed once and for all *)
    iAssert (uart_sent_sub γd (bs ++ [sb])) as "#Hsubout".
    { iApply (uart_sent_sub_snoc γd bs l sb Hsl with "Hsent"). }
    (* ===== &tx_lock again, then release (0x34 .. 0x3c) ===== *)
    (* +0x34 auipc a0,0x12 *)
    iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.uartputc_sync + 0x34)) (mword_of_int 10) (mword_of_int 18 : mword 20)
              (ppc_f6' macq bt) (trap_res b + (K - 4))%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi34").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    set (H34 := <[Regidx (mword_of_int 10) := regval_into_reg (add_vec (mword_of_int (KernelSyms.uartputc_sync + 0x34)) (auipc_off (mword_of_int 18 : mword 20)))]> (ppc_f6' macq bt)).
    assert (Hpp38 : add_vec_int (mword_of_int (KernelSyms.uartputc_sync + 0x34) : mword 64) 4 = mword_of_int (KernelSyms.uartputc_sync + 0x38)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp38) in "Hpc".
    (* +0x38 addi a0,a0,-1584 -> &tx_lock *)
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.uartputc_sync + 0x38)) (mword_of_int 10) (mword_of_int 10) (mword_of_int 2534 : mword 12)
              H34 (trap_res b + (K - 4))%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi38").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (H38 := <[Regidx (mword_of_int 10) := regval_into_reg (add_vec (H34 !!! Regidx (mword_of_int 10 : mword 5)) (sign_extend' 64 (mword_of_int 2534 : mword 12)))]> H34).
    assert (HH38a0 : H38 !!! Regidx (mword_of_int 10 : mword 5) = a_tx_lock).
    { rewrite /H38 upd_eq. rewrite /H34 upd_eq.
      unfold a_tx_lock. apply bv_eq; vm_compute; reflexivity. }
    assert (Hpp3c : add_vec_int (mword_of_int (KernelSyms.uartputc_sync + 0x38) : mword 64) 4 = mword_of_int (KernelSyms.uartputc_sync + 0x3c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp3c) in "Hpc".
    (* +0x3c jal ra,release *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.uartputc_sync + 0x3c)) (mword_of_int 1 : mword 5) (mword_of_int 688 : mword 21)
              H38 (trap_res b + (K - 4))%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi3c").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    set (H3c := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.uartputc_sync + 0x3c) : mword 64) 4)]> H38).
    assert (Hjrel : add_vec (mword_of_int (KernelSyms.uartputc_sync + 0x3c) : mword 64) (sign_extend' 64 (mword_of_int 688 : mword 21)) = mword_of_int KernelSyms.release)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hjrel) in "Hpc".
    assert (HH3cra : H3c !!! Regidx (mword_of_int 1 : mword 5)
                     = regval_into_reg (add_vec_int (mword_of_int (KernelSyms.uartputc_sync + 0x3c) : mword 64) 4))
      by (rewrite /H3c upd_eq; reflexivity).
    assert (HH3ca0 : H3c !!! Regidx (mword_of_int 10 : mword 5) = a_tx_lock)
      by (rewrite /H3c upd_ne; [exact HH38a0 | vm_compute; discriminate]).
    assert (Hlka : add_vec (H3c !!! Regidx (mword_of_int 10 : mword 5)) (sign_extend' 64 (mword_of_int 0 : mword 12)) = a_tx_lock).
    { rewrite HH3ca0.
      replace (sign_extend' 64 (mword_of_int 0 : mword 12) : mword 64) with (mword_of_int 0 : mword 64)
        by (apply bv_eq; vm_compute; reflexivity).
      apply kv_addv_zero. }
    (* ===== release(&tx_lock) ===== *)
    iEval (rewrite -Hbeq) in "Hcg".
    iApply (Release.wp_release_sconf γl a_tx_lock "uart"%string (tx_res γd) H3c n eb p C (K - 4)%nat
              Hlka Hav with "Hcg Ht Hpc Hlk Hlocked [Hown] Hcpu Hpay").
    { iApply (tx_res_intro γd (l ++ [sb]) with "Hown"). }
    iIntros (CIDrel Hsrel mrel) "Hcg Hpc %Hcs_rel Hcpu".
    rewrite Hbeq in Hsrel.
    iEval (rewrite Hbeq) in "Hcg". iEval (rewrite Hbeq) in "Hcpu".
    assert (Hret3c : ret_pc (H3c !!! Regidx (mword_of_int 1 : mword 5)) = mword_of_int (KernelSyms.uartputc_sync + 0x40))
      by (rewrite HH3cra; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hret3c) in "Hpc".
    (* ===== EPILOGUE (0x40 -> 0x48) ===== *)
    assert (Hmrelsp : mrel !!! Regidx csp_rs1 = spr).
    { rewrite (callee_saved_lookup Hcs_rel csp_rs1 ltac:(vm_compute; reflexivity)).
      rewrite /H3c upd_ne; [| vm_compute; discriminate].
      rewrite /H38 upd_ne; [| vm_compute; discriminate].
      rewrite /H34 upd_ne; [| vm_compute; discriminate].
      rewrite ppc_f6'_cs;
        [| vm_compute; discriminate | vm_compute; discriminate | vm_compute; discriminate ].
      rewrite (callee_saved_lookup Hcs_acq csp_rs1 ltac:(vm_compute; reflexivity)).
      rewrite /G14 upd_ne; [| vm_compute; discriminate].
      rewrite /G10 upd_ne; [| vm_compute; discriminate].
      rewrite /G0c upd_ne; [| vm_compute; discriminate].
      rewrite /R3 upd_ne; [| vm_compute; discriminate].
      rewrite /R2 upd_ne; [| vm_compute; discriminate].
      exact HspR1. }
    iEval (rewrite HspR1) in "Hr24". iEval (rewrite HspR1) in "Hr16".
    iEval (rewrite HspR1) in "Hr8". iEval (rewrite HspR1) in "Hg4".
    (* +0x40 c.ldsp ra,24(sp) *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.uartputc_sync + 0x40)) (mword_of_int 3 : mword 6) (mword_of_int 1 : mword 5)
              mrel (K - 4)%nat (R1 !!! Regidx (mword_of_int 1 : mword 5)) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi40 [Hr24]").
    { iEval (rewrite Hmrelsp). iExact "Hr24". }
    iIntros (CIDe1 Hse1) "Hcg Hpc Hr24".
    iEval (rewrite Hmrelsp) in "Hr24".
    set (Q40 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (R1 !!! Regidx (mword_of_int 1 : mword 5))]> mrel).
    assert (HspQ40 : Q40 !!! Regidx csp_rs1 = spr) by (rewrite /Q40 upd_ne; [ exact Hmrelsp | vm_compute; discriminate ]).
    assert (Hpp42 : add_vec_int (mword_of_int (KernelSyms.uartputc_sync + 0x40) : mword 64) 2 = mword_of_int (KernelSyms.uartputc_sync + 0x42)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp42) in "Hpc".
    (* +0x42 c.ldsp s0,16(sp) *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.uartputc_sync + 0x42)) (mword_of_int 2 : mword 6) (mword_of_int 8 : mword 5)
              Q40 (K - 4)%nat (R1 !!! Regidx (mword_of_int 8 : mword 5)) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi42 [Hr16]").
    { iEval (rewrite HspQ40). iExact "Hr16". }
    iIntros (CIDe2 Hse2) "Hcg Hpc Hr16".
    iEval (rewrite HspQ40) in "Hr16".
    set (Q42 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg (R1 !!! Regidx (mword_of_int 8 : mword 5))]> Q40).
    assert (HspQ42 : Q42 !!! Regidx csp_rs1 = spr) by (rewrite /Q42 upd_ne; [ exact HspQ40 | vm_compute; discriminate ]).
    assert (Hpp44 : add_vec_int (mword_of_int (KernelSyms.uartputc_sync + 0x42) : mword 64) 2 = mword_of_int (KernelSyms.uartputc_sync + 0x44)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp44) in "Hpc".
    (* +0x44 c.ldsp s1,8(sp) *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.uartputc_sync + 0x44)) (mword_of_int 1 : mword 6) (mword_of_int 9 : mword 5)
              Q42 (K - 4)%nat (R1 !!! Regidx (mword_of_int 9 : mword 5)) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi44 [Hr8]").
    { iEval (rewrite HspQ42). iExact "Hr8". }
    iIntros (CIDe3 Hse3) "Hcg Hpc Hr8".
    iEval (rewrite HspQ42) in "Hr8".
    set (Q44 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (R1 !!! Regidx (mword_of_int 9 : mword 5))]> Q42).
    assert (HspQ44 : Q44 !!! Regidx csp_rs1 = spr) by (rewrite /Q44 upd_ne; [ exact HspQ42 | vm_compute; discriminate ]).
    assert (Hpp46 : add_vec_int (mword_of_int (KernelSyms.uartputc_sync + 0x44) : mword 64) 2 = mword_of_int (KernelSyms.uartputc_sync + 0x46)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp46) in "Hpc".
    (* +0x46 c.addi16sp sp,32 -- pop 4 *)
    set (Q46 := <[Regidx csp_rs1 := regval_into_reg (add_vec (Q44 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))))]> Q44).
    assert (Hwval : add_vec (Q44 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))) = sp0).
    { rewrite HspQ44. unfold spr, sp0. apply frame_cancel_32. }
    assert (Hpop : Q44 !!! Regidx csp_rs1
                   = pa_stk (add_vec (Q44 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6)))) 4).
    { rewrite Hwval HspQ44. unfold spr, sp0, pa_stk, add_vec_int. apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    iAssert (stack_own (add_vec (Q44 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6)))) 4)
      with "[Hr24 Hr16 Hr8 Hg4]" as "Hframe".
    { rewrite Hwval. rewrite stack_own_slots. cbn [seq].
      iSplitL "Hr24"; [iEval (rewrite -Hb1 HspR1); iExists _; iExact "Hr24"|].
      iSplitL "Hr16"; [iEval (rewrite -Hb2 HspR1); iExists _; iExact "Hr16"|].
      iSplitL "Hr8";  [iEval (rewrite -Hb3 HspR1); iExists _; iExact "Hr8"|].
      iSplitL "Hg4";  [iEval (rewrite -Hb4 HspR1); iExists _; iExact "Hg4"|].
      done. }
    iApply (wp_caddi16sp_pop_s_sconf (mword_of_int (KernelSyms.uartputc_sync + 0x46)) (mword_of_int 2 : mword 6) Q44
              (K - 4)%nat 4 b Hpop
              with "Hcg Hpc Hi46 Hframe").
    iIntros (CIDe4 Hse4) "Hcg Hpc".
    assert (HK4' : ((K - 4) + 4)%nat = K) by lia.
    iEval (rewrite HK4') in "Hcg".
    assert (Hpp48 : add_vec_int (mword_of_int (KernelSyms.uartputc_sync + 0x46) : mword 64) 2 = mword_of_int (KernelSyms.uartputc_sync + 0x48)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp48) in "Hpc".
    (* +0x48 c.ret *)
    assert (HQ46ra : Q46 !!! Regidx (mword_of_int 1 : mword 5) = ra0).
    { rewrite /Q46 upd_ne; [| vm_compute; discriminate].
      rewrite /Q44 upd_ne; [| vm_compute; discriminate].
      rewrite /Q42 upd_ne; [| vm_compute; discriminate].
      rewrite /Q40 upd_eq.
      rewrite /R1 upd_ne; [reflexivity | vm_compute; discriminate]. }
    iApply (wp_cret_s_sconf (mword_of_int (KernelSyms.uartputc_sync + 0x48)) (mword_of_int 1 : mword 5) Q46 K b
              ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi48").
    iIntros (CIDe5 Hse5) "Hcg Hpc".
    iEval (rgne) in "Hpc".
    assert (Hretf : ret_pc (Q46 !!! Regidx (mword_of_int 1 : mword 5)) = ret_tgt)
      by (rewrite HQ46ra; reflexivity).
    iEval (rewrite Hretf) in "Hpc".
    iDestruct (cpu_own_transport CIDrel CIDe5 n eb p C b ltac:(wp_next_chain)
                 with "Hcpu") as "Hcpu".
    iSpecialize ("Hcont" $! CIDe5 with "[%]"); [wp_next_chain|].
    iApply ("Hcont" $! Q46 with "Hcg Hcpu Hpc [%] Hsubout").
    (* callee_saved m0 Q46 /\ Q46!!!ra = ra0 *)
    split; [| exact HQ46ra].
    (* threading: a register untouched by the body threads m0 -> Q46 *)
    assert (Hthread : forall c : mword 5, is_cs_idx c = true ->
              c <> mword_of_int 1 -> c <> csp_rs1 -> c <> mword_of_int 8 -> c <> mword_of_int 9 ->
              Q46 !!! Regidx c = m0 !!! Regidx c).
    { intros c Hcs N1 N2 N8 N9.
      pose proof (is_cs_idx_true_neq (mword_of_int 10 : mword 5) c ltac:(vm_compute; reflexivity) Hcs) as N10.
      pose proof (is_cs_idx_true_neq (mword_of_int 14 : mword 5) c ltac:(vm_compute; reflexivity) Hcs) as N14.
      pose proof (is_cs_idx_true_neq (mword_of_int 15 : mword 5) c ltac:(vm_compute; reflexivity) Hcs) as N15.
      rewrite /Q46 upd_ne; [| congruence].
      rewrite /Q44 upd_ne; [| congruence].
      rewrite /Q42 upd_ne; [| congruence].
      rewrite /Q40 upd_ne; [| congruence].
      rewrite (callee_saved_lookup Hcs_rel c Hcs).
      rewrite /H3c upd_ne; [| congruence].
      rewrite /H38 upd_ne; [| congruence].
      rewrite /H34 upd_ne; [| congruence].
      rewrite ppc_f6'_cs; [| congruence | congruence | congruence ].
      rewrite (callee_saved_lookup Hcs_acq c Hcs).
      rewrite /G14 upd_ne; [| congruence].
      rewrite /G10 upd_ne; [| congruence].
      rewrite /G0c upd_ne; [| congruence].
      rewrite /R3 upd_ne; [| congruence].
      rewrite /R2 upd_ne; [| congruence].
      rewrite /R1 upd_ne; [reflexivity | congruence]. }
    unfold callee_saved.
    split.
    { (* sp *)
      rewrite /Q46 upd_eq. rewrite HspQ44. unfold regval_into_reg, spr, sp0.
      apply frame_cancel_32. }
    split.
    { (* s0 *)
      rewrite /Q46 upd_ne; [| vm_compute; discriminate].
      rewrite /Q44 upd_ne; [| vm_compute; discriminate].
      rewrite /Q42 upd_eq.
      rewrite /R1 upd_ne; [reflexivity | vm_compute; discriminate]. }
    split.
    { (* s1 *)
      rewrite /Q46 upd_ne; [| vm_compute; discriminate].
      rewrite /Q44 upd_eq.
      rewrite /R1 upd_ne; [reflexivity | vm_compute; discriminate]. }
    repeat split; apply Hthread; vm_compute; first [reflexivity | discriminate].
  Qed.

End ProofUartPutc.

End UartPutcProof.
