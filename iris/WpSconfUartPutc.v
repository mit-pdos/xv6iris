(* WpSconfUartPutc.v -- uartputc_sync over the SIE-agnostic sconf world.

   The sconf mirror of [wp_uartputc_r] (WpUartPutcSyncFull.v): the panic-path
   synchronous UART putc (panicking != 0 && panicked == 0), which does NO
   push_off/pop_off/locking, hence threads NO [intr_count].  The prologue/
   epilogue 4-slot frame (3 saves ra/s0/s1 + padding) is carved out of the
   capability's free stack via wp_caddi_sp_push_s_sconf and returned via
   wp_caddi16sp_pop_s_sconf.  The panic-check ALU and
   the device core (LSR poll loop + THR write) run over the sconf leaves; the
   two device leaves are the WpSconfUart accessor forms.

   All config-independent [instr] decode facts, the ppc_f* register maps, the
   lsr_* device helpers and [ups_frame_cancel] are REUSED from the smode
   WpUartPutcSync / WpUartPutcSyncFull files (persistent / pure facts, so the
   sconf port only re-does the resource threading). *)
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
Require Import KernelText WpAuipc.
Require Import RegFile.
Require Import WpGpr.
Require Import WpMmodeLeafBase.
Require Import SmodeCore.
Require Import StackOwn.
Require Import CalleeSaved.
Require Import VcGen.
Require Import KptTree.
Require Import DevModel WpUart.
Require Import IntrDefs WpSmodeIntr.
Require Import IntrDefs.
Require Import WpSconfAlu WpSconfMem WpSconfBtype WpSconfCtl SpecUart.
Require Import WpUartPutcSync WpUartPutcSyncFull.
Require Import WpSconfUartAccess.
Require Import SpecUartPutc.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.

Module UartPutcProof (Uart : UART) : UARTPUTC.

(* The base ALU leaves ([wp_lui_s_sconf], [wp_andi_s_sconf]) live in
   WpSconfAlu.v; the call-site-specialized UART device leaves
   ([wp_uart_lsr_read_s_sconf], [wp_uart_thr_write_s_sconf]) live in the
   WpSconfUartAccess.v leaf functor.  Instantiate the latter against this
   proof's sealed [Uart]. *)
Module UAcc := UartAccessProof Uart.

Section WpSconfUartPutc.
  Context `{!riscvGS Σ, !sieG Σ}.
  Context `{!uartGhostG Σ}.
  Context `{CID : CpuId}.

  Notation UPS := KernelSyms.uartputc_sync.

  (* =================================================================== *)
  (*  THE THRE POLL LOOP: 0x26 -> 0x30, run under [dev_inv] (Löb).         *)
  (* =================================================================== *)
  Lemma wp_uartputc_poll_sconf (γ : gname) (root_ppn : mword 44) (γd : uart_names)
      (Φ : mval -> iProp Σ) (mentry : regfile) (n : nat) (l : list (bv 8)) :
    mentry !!! Regidx (mword_of_int 14) = uart_pa 5 ->
    sconf γ -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    sie_cap_gpr γ root_ppn mentry n -∗ tlb_inv_pt root_ppn -∗ kernel_text -∗
    pc_is (mword_of_int (UPS + 0x26)) -∗
    dev_inv γd -∗ uart_tx_own γd l -∗
    ( ∀ b : bv 8,
      hart_state ↦ᵣ HART_ACTIVE tt -∗ sconf γ -∗
      sie_cap_gpr γ root_ppn (<[Regidx (mword_of_int 15) := regval_into_reg (lsr_masked b)]> mentry) n -∗
      tlb_inv_pt root_ppn -∗
      pc_is (mword_of_int (UPS + 0x30)) -∗
      uart_tx_own γd l -∗ uart_out_lb γd l -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros Ha4e.
    iIntros "Hsc Hhs Hcg Htlbinv #Ht Hpc #Hdinv Hown Hcont".
    iDestruct (upi_26 with "Ht") as "#Hi26".
    iDestruct (upi_2a with "Ht") as "#Hi2a".
    iDestruct (upi_2e with "Ht") as "#Hi2e".
    assert (P2a : add_vec_int (mword_of_int (UPS + 0x26) : mword 64) 4 = mword_of_int (UPS + 0x2a)) by (apply bv_eq; vm_compute; reflexivity).
    assert (P2e : add_vec_int (mword_of_int (UPS + 0x2a) : mword 64) 4 = mword_of_int (UPS + 0x2e)) by (apply bv_eq; vm_compute; reflexivity).
    assert (P30 : add_vec_int (mword_of_int (UPS + 0x2e) : mword 64) 2 = mword_of_int (UPS + 0x30)) by (apply bv_eq; vm_compute; reflexivity).
    assert (Htgt : add_vec (mword_of_int (UPS + 0x2e) : mword 64)
                     (sign_extend' 64 (sign_extend' 13 (concat_vec (mword_of_int 252 : mword 8) ('b"0"))))
                   = mword_of_int (UPS + 0x26)) by (apply bv_eq; vm_compute; reflexivity).
    iAssert (∀ m : regfile,
      ⌜ m !!! Regidx (mword_of_int 14) = uart_pa 5 ⌝ -∗
      ⌜ forall Y, <[Regidx (mword_of_int 15) := Y]> m
                = <[Regidx (mword_of_int 15) := Y]> mentry ⌝ -∗
      sconf γ -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
      sie_cap_gpr γ root_ppn m n -∗ tlb_inv_pt root_ppn -∗
      pc_is (mword_of_int (UPS + 0x26)) -∗ uart_tx_own γd l -∗
      ( ∀ b : bv 8, hart_state ↦ᵣ HART_ACTIVE tt -∗ sconf γ -∗
          sie_cap_gpr γ root_ppn (<[Regidx (mword_of_int 15) := regval_into_reg (lsr_masked b)]> mentry) n -∗
          tlb_inv_pt root_ppn -∗
          pc_is (mword_of_int (UPS + 0x30)) -∗
          uart_tx_own γd l -∗ uart_out_lb γd l -∗ WP (Loop : expr riscv_lang) {{ Φ }}) -∗
      WP (Loop : expr riscv_lang) {{ Φ }})%I with "[]" as "Loop".
    { iLöb as "IH". iIntros (m Ha4m Hagm) "Hsc Hhs Hcg Htlbinv Hpc Hown Hk".
      (* 0x26  lbu a5,0(a4) *)
      iApply (UAcc.wp_uart_lsr_read_s_sconf γ root_ppn γd Φ (mword_of_int (UPS + 0x26)) (mword_of_int 15) (mword_of_int 14)
                m n l ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) Ha4m
                with "Hsc Hhs Hcg Htlbinv Hpc Hi26 Hdinv Hown").
      iIntros (b) "Hhs Hsc Hcg Htlbinv Hpc Hown Hlb".
      iEval (rewrite P2a) in "Hpc".
      (* 0x2a  andi a5,a5,32 *)
      iApply (wp_andi_s_sconf γ root_ppn Φ (mword_of_int (UPS + 0x2a)) (mword_of_int 15) (mword_of_int 15) (mword_of_int 32 : mword 12)
                _ (<[Regidx (mword_of_int 15) := regval_into_reg (lsr_ldval_of b)]> m) n
                ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) eq_refl
                with "Hsc Hhs Hcg Htlbinv Hpc Hi2a").
      iIntros "Hhs Hsc Hcg Htlbinv Hpc".
      iEval (rewrite upd_eq upd_upd) in "Hcg".
      change (and_vec (lsr_ldval_of b) (sign_extend' 64 (mword_of_int 32 : mword 12)))
        with (lsr_masked b) in *.
      iEval (rewrite P2e) in "Hpc".
      (* 0x2e  c.beqz a5,0x26 *)
      destruct (lsr_thre_clear b) eqn:Hcase.
      - iApply (wp_cbeqz_taken_s_sconf γ root_ppn Φ (mword_of_int (UPS + 0x2e)) (mword_of_int 252 : mword 8)
                  (Cregidx (mword_of_int 7)) (mword_of_int 15)
                  (<[Regidx (mword_of_int 15) := regval_into_reg (lsr_masked b)]> m) n
                  ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                  ltac:(rewrite upd_eq; unfold regval_into_reg, lsr_masked; exact Hcase)
                  ltac:(vm_compute; reflexivity)
                  with "Hsc Hhs Hcg Htlbinv Hpc Hi2e").
        iNext. iIntros "Hhs Hsc Hcg Htlbinv Hpc".
        iEval (rewrite Htgt) in "Hpc".
        iApply ("IH" $! (<[Regidx (mword_of_int 15) := regval_into_reg (lsr_masked b)]> m)
                  with "[%] [%] Hsc Hhs Hcg Htlbinv Hpc Hown Hk").
        + rewrite upd_ne; [exact Ha4m | vm_compute; discriminate].
        + intro Y. rewrite upd_upd. exact (Hagm Y).
      - iApply (wp_cbeqz_fall_s_sconf γ root_ppn Φ (mword_of_int (UPS + 0x2e)) (mword_of_int 252 : mword 8)
                  (Cregidx (mword_of_int 7)) (mword_of_int 15)
                  (<[Regidx (mword_of_int 15) := regval_into_reg (lsr_masked b)]> m) n
                  ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                  ltac:(rewrite upd_eq; unfold regval_into_reg, lsr_masked; exact Hcase)
                  with "Hsc Hhs Hcg Htlbinv Hpc Hi2e").
        iIntros "Hhs Hsc Hcg Htlbinv Hpc".
        iEval (rewrite P30) in "Hpc".
        iEval (rewrite (Hagm (regval_into_reg (lsr_masked b)))) in "Hcg".
        iApply ("Hk" $! b with "Hhs Hsc Hcg Htlbinv Hpc Hown").
        by iApply "Hlb". }
    iApply ("Loop" $! mentry with "[%] [%] Hsc Hhs Hcg Htlbinv Hpc Hown Hcont").
    - exact Ha4e.
    - reflexivity.
  Qed.

  (* =================================================================== *)
  (*  DEVICE CORE: 0x20 -> 0x3c (lui/addi + poll + zext.b + lui + THR).    *)
  (* =================================================================== *)
  Lemma wp_uartputc_devcore_sconf (γ : gname) (root_ppn : mword 44) (γd : uart_names)
      (Φ : mval -> iProp Σ)
      (m : regfile) (n : nat) (l : list (bv 8)) :
    let sb : mword 8 := autocast (T := mword)
       (subrange_vec_dec (and_vec (m !!! Regidx (mword_of_int 9))
          (sign_extend' 64 (mword_of_int 255 : mword 12))) 7 0) in
    sconf γ -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    sie_cap_gpr γ root_ppn m n -∗ tlb_inv_pt root_ppn -∗ kernel_text -∗
    pc_is (mword_of_int (UPS + 0x20)) -∗
    dev_inv γd -∗ uart_tx_own γd l -∗ uart_dlab_off γd -∗
    ( ∀ b : bv 8,
      hart_state ↦ᵣ HART_ACTIVE tt -∗ sconf γ -∗
      sie_cap_gpr γ root_ppn (ppc_f6' m b) n -∗ tlb_inv_pt root_ppn -∗
      pc_is (mword_of_int (UPS + 0x3c)) -∗
      uart_tx_own γd (l ++ [sb]) -∗ uart_sent γd (l ++ [sb]) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros sb.
    iIntros "Hsc Hhs Hcg Htlbinv #Ht Hpc #Hdinv Hown #Hoff Hcont".
    assert (P24 : add_vec_int (mword_of_int (UPS + 0x20) : mword 64) 4 = mword_of_int (UPS + 0x24)) by (apply bv_eq; vm_compute; reflexivity).
    assert (P26 : add_vec_int (mword_of_int (UPS + 0x24) : mword 64) 2 = mword_of_int (UPS + 0x26)) by (apply bv_eq; vm_compute; reflexivity).
    assert (P34 : add_vec_int (mword_of_int (UPS + 0x30) : mword 64) 4 = mword_of_int (UPS + 0x34)) by (apply bv_eq; vm_compute; reflexivity).
    assert (P38 : add_vec_int (mword_of_int (UPS + 0x34) : mword 64) 4 = mword_of_int (UPS + 0x38)) by (apply bv_eq; vm_compute; reflexivity).
    assert (P3c : add_vec_int (mword_of_int (UPS + 0x38) : mword 64) 4 = mword_of_int (UPS + 0x3c)) by (apply bv_eq; vm_compute; reflexivity).
    iPoseProof (upi_20 with "Ht") as "Hi20".
    iPoseProof (upi_24 with "Ht") as "Hi24".
    iPoseProof (upi_30 with "Ht") as "Hi30".
    iPoseProof (upi_34 with "Ht") as "Hi34".
    iPoseProof (upi_38 with "Ht") as "Hi38".
    (* 0x20  lui a4,0x10000 *)
    iApply (wp_lui_s_sconf γ root_ppn Φ (mword_of_int (UPS + 0x20)) (mword_of_int 14) (mword_of_int 0x10000 : mword 20)
              (luival (mword_of_int 0x10000 : mword 20)) m n
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) eq_refl
              with "Hsc Hhs Hcg Htlbinv Hpc Hi20").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc".
    iEval (rewrite P24) in "Hpc".
    (* 0x24  c.addi a4,a4,5 *)
    iApply (wp_caddi_s_sconf γ root_ppn Φ (mword_of_int (UPS + 0x24)) (mword_of_int 14) (mword_of_int 5 : mword 6)
              (ppc_f1 m) n ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi24").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc".
    iEval (rewrite P26) in "Hpc".
    (* 0x26 -> 0x30  the poll loop *)
    iApply (wp_uartputc_poll_sconf γ root_ppn γd Φ (ppc_f2 m) n l (ppc_f2_a4 m)
              with "Hsc Hhs Hcg Htlbinv Ht Hpc Hdinv Hown").
    iIntros (b) "Hhs Hsc Hcg Htlbinv Hpc Hown #Hlb".
    iEval (change (<[Regidx (mword_of_int 15) := regval_into_reg (lsr_masked b)]> (ppc_f2 m))
             with (ppc_f4' m b)) in "Hcg".
    (* 0x30  zext.b a0,s1  (andi a0,s1,255) *)
    iApply (wp_andi_s_sconf γ root_ppn Φ (mword_of_int (UPS + 0x30)) (mword_of_int 10) (mword_of_int 9) (mword_of_int 255 : mword 12)
              _ (ppc_f4' m b) n ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) eq_refl
              with "Hsc Hhs Hcg Htlbinv Hpc Hi30").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc".
    iEval (change (<[Regidx (mword_of_int 10) := regval_into_reg (and_vec (ppc_f4' m b !!! Regidx (mword_of_int 9))
             (sign_extend' 64 (mword_of_int 255 : mword 12)))]> (ppc_f4' m b))
             with (ppc_f5' m b)) in "Hcg".
    iEval (rewrite P34) in "Hpc".
    (* 0x34  lui a5,0x10000 *)
    iApply (wp_lui_s_sconf γ root_ppn Φ (mword_of_int (UPS + 0x34)) (mword_of_int 15) (mword_of_int 0x10000 : mword 20)
              (luival (mword_of_int 0x10000 : mword 20)) (ppc_f5' m b) n
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) eq_refl
              with "Hsc Hhs Hcg Htlbinv Hpc Hi34").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc".
    iEval (change (<[Regidx (mword_of_int 15) := regval_into_reg (luival (mword_of_int 0x10000 : mword 20))]> (ppc_f5' m b))
             with (ppc_f6' m b)) in "Hcg".
    iEval (rewrite P38) in "Hpc".
    (* 0x38  sb a0,0(a5)  -- THR write *)
    assert (Hsbb : (autocast (T := mword)
                      (subrange_vec_dec (ppc_f6' m b !!! Regidx (mword_of_int 10))
                         (Z.sub (Z.mul 1 8) 1) 0) : mword 8) = sb).
    { unfold sb. rewrite ppc_f6'_a0. reflexivity. }
    iApply (UAcc.wp_uart_thr_write_s_sconf γ root_ppn γd Φ (mword_of_int (UPS + 0x38)) (mword_of_int 10) (mword_of_int 15)
              (ppc_f6' m b) n l (ppc_f6'_a5 m b)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi38 Hdinv Hown Hlb Hoff").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc Hown Hsent".
    iEval (rewrite Hsbb) in "Hown". iEval (rewrite Hsbb) in "Hsent".
    iEval (rewrite P3c) in "Hpc".
    iApply ("Hcont" $! b with "Hhs Hsc Hcg Htlbinv Hpc Hown Hsent").
  Qed.

  (* =================================================================== *)
  (*  THE BODY: 0x0c -> 0x46 (panic checks + device core + 2nd panicking). *)
  (* =================================================================== *)
  Lemma wp_uartputc_body_sconf (γ : gname) (root_ppn : mword 44) (γd : uart_names)
      (Φ : mval -> iProp Σ)
      (m : regfile) (n : nat) (l : list (bv 8)) (pv pkv : mword 32)
      {dqm dqm2 : dfrac} :
    let sb : mword 8 := autocast (T := mword)
       (subrange_vec_dec (and_vec (m !!! Regidx (mword_of_int 9))
          (sign_extend' 64 (mword_of_int 255 : mword 12))) 7 0) in
    eq_vec (sign_extend' 64 pv) zero_reg = false ->
    neq_vec (sign_extend' 64 pkv) zero_reg = false ->
    sconf γ -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    sie_cap_gpr γ root_ppn m n -∗ tlb_inv_pt root_ppn -∗ kernel_text -∗
    pc_is (mword_of_int (UPS + 0x0c)) -∗
    (mword_of_int KernelSyms.panicking : mword 64) ↦₄{ dqm } pv -∗
    (mword_of_int KernelSyms.panicked : mword 64) ↦₄{ dqm2 } pkv -∗
    dev_inv γd -∗ uart_tx_own γd l -∗ uart_dlab_off γd -∗
    ( ∀ mf,
      hart_state ↦ᵣ HART_ACTIVE tt -∗ sconf γ -∗
      sie_cap_gpr γ root_ppn mf n -∗ tlb_inv_pt root_ppn -∗
      pc_is (mword_of_int (UPS + 0x46)) -∗
      ⌜ callee_saved m mf ⌝ -∗
      (mword_of_int KernelSyms.panicking : mword 64) ↦₄{ dqm } pv -∗
      (mword_of_int KernelSyms.panicked : mword 64) ↦₄{ dqm2 } pkv -∗
      uart_tx_own γd (l ++ [sb]) -∗ uart_sent γd (l ++ [sb]) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros sb.
    iIntros (Hpv Hpkv) "Hsc Hhs Hcg Htlbinv #Ht Hpc Hpk Hpkd #Hdinv Hown #Hoff Hcont".
    iPoseProof (upi_0c with "Ht") as "Hi0c".
    iPoseProof (upi_10 with "Ht") as "Hi10".
    iPoseProof (upi_14 with "Ht") as "Hi14".
    iPoseProof (upi_16 with "Ht") as "Hi16".
    iPoseProof (upi_1a with "Ht") as "Hi1a".
    iPoseProof (upi_1e with "Ht") as "Hi1e".
    iPoseProof (upi_3c with "Ht") as "Hi3c".
    iPoseProof (upi_40 with "Ht") as "Hi40".
    iPoseProof (upi_44 with "Ht") as "Hi44".
    assert (P10 : add_vec_int (mword_of_int (UPS + 0x0c) : mword 64) 4 = mword_of_int (UPS + 0x10)) by (apply bv_eq; vm_compute; reflexivity).
    assert (P14 : add_vec_int (mword_of_int (UPS + 0x10) : mword 64) 4 = mword_of_int (UPS + 0x14)) by (apply bv_eq; vm_compute; reflexivity).
    assert (P16 : add_vec_int (mword_of_int (UPS + 0x14) : mword 64) 2 = mword_of_int (UPS + 0x16)) by (apply bv_eq; vm_compute; reflexivity).
    assert (P1a : add_vec_int (mword_of_int (UPS + 0x16) : mword 64) 4 = mword_of_int (UPS + 0x1a)) by (apply bv_eq; vm_compute; reflexivity).
    assert (P1e : add_vec_int (mword_of_int (UPS + 0x1a) : mword 64) 4 = mword_of_int (UPS + 0x1e)) by (apply bv_eq; vm_compute; reflexivity).
    assert (P20 : add_vec_int (mword_of_int (UPS + 0x1e) : mword 64) 2 = mword_of_int (UPS + 0x20)) by (apply bv_eq; vm_compute; reflexivity).
    assert (P40 : add_vec_int (mword_of_int (UPS + 0x3c) : mword 64) 4 = mword_of_int (UPS + 0x40)) by (apply bv_eq; vm_compute; reflexivity).
    assert (P44 : add_vec_int (mword_of_int (UPS + 0x40) : mword 64) 4 = mword_of_int (UPS + 0x44)) by (apply bv_eq; vm_compute; reflexivity).
    assert (P46 : add_vec_int (mword_of_int (UPS + 0x44) : mword 64) 2 = mword_of_int (UPS + 0x46)) by (apply bv_eq; vm_compute; reflexivity).
    (* ---- 0x0c auipc a5 ---- *)
    iApply (wp_auipc_s_sconf γ root_ppn Φ (mword_of_int (UPS + 0x0c)) (mword_of_int 15) (mword_of_int 0xa : mword 20)
              m n ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi0c").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc".
    iEval (rewrite P10) in "Hpc".
    set (g0c := <[Regidx (mword_of_int 15) := regval_into_reg (add_vec (mword_of_int (UPS + 0x0c)) (auipc_off (mword_of_int 0xa : mword 20)))]> m).
    assert (Hea0 : add_vec (g0c !!! Regidx (mword_of_int 15)) (sign_extend' 64 (mword_of_int 0x8a8 : mword 12))
                   = (mword_of_int KernelSyms.panicking : mword 64)).
    { unfold g0c. rewrite upd_eq. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite <- Hea0) in "Hpk".
    (* ---- 0x10 lw a5,-1880(a5) : panicking ---- *)
    iApply (wp_lw_s_sconf γ root_ppn Φ (mword_of_int (UPS + 0x10)) (mword_of_int 15) (mword_of_int 15) (mword_of_int 0x8a8 : mword 12)
              g0c n pv (dqm:=dqm) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi10 Hpk").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc Hpk".
    iEval (rewrite Hea0) in "Hpk".
    iEval (rewrite P14) in "Hpc".
    (* ---- 0x14 c.beqz a5 : falls through (panicking != 0) ---- *)
    iApply (wp_cbeqz_fall_s_sconf γ root_ppn Φ (mword_of_int (UPS + 0x14)) (mword_of_int 30 : mword 8)
              (Cregidx (mword_of_int 7)) (mword_of_int 15)
              (<[Regidx (mword_of_int 15) := regval_into_reg (sign_extend' 64 pv)]> g0c) n
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
              ltac:(rewrite upd_eq; exact Hpv)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi14").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc".
    iEval (rewrite P16) in "Hpc".
    set (f1 := <[Regidx (mword_of_int 15) := regval_into_reg (sign_extend' 64 pv)]> g0c).
    (* ---- 0x16 auipc a5 ---- *)
    iApply (wp_auipc_s_sconf γ root_ppn Φ (mword_of_int (UPS + 0x16)) (mword_of_int 15) (mword_of_int 0xa : mword 20)
              f1 n ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi16").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc".
    iEval (rewrite P1a) in "Hpc".
    set (g16 := <[Regidx (mword_of_int 15) := regval_into_reg (add_vec (mword_of_int (UPS + 0x16)) (auipc_off (mword_of_int 0xa : mword 20)))]> f1).
    assert (Hea1 : add_vec (g16 !!! Regidx (mword_of_int 15)) (sign_extend' 64 (mword_of_int 0x89a : mword 12))
                   = (mword_of_int KernelSyms.panicked : mword 64)).
    { unfold g16. rewrite upd_eq. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite <- Hea1) in "Hpkd".
    (* ---- 0x1a lw a5,-1894(a5) : panicked ---- *)
    iApply (wp_lw_s_sconf γ root_ppn Φ (mword_of_int (UPS + 0x1a)) (mword_of_int 15) (mword_of_int 15) (mword_of_int 0x89a : mword 12)
              g16 n pkv (dqm:=dqm2) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi1a Hpkd").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc Hpkd".
    iEval (rewrite Hea1) in "Hpkd".
    iEval (rewrite P1e) in "Hpc".
    (* ---- 0x1e c.bnez a5 : falls through (panicked == 0) ---- *)
    iApply (wp_cbnez_fall_s_sconf γ root_ppn Φ (mword_of_int (UPS + 0x1e)) (mword_of_int 28 : mword 8)
              (Cregidx (mword_of_int 7)) (mword_of_int 15)
              (<[Regidx (mword_of_int 15) := regval_into_reg (sign_extend' 64 pkv)]> g16) n
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
              ltac:(rewrite upd_eq; exact Hpkv)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi1e").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc".
    iEval (rewrite P20) in "Hpc".
    set (f2 := <[Regidx (mword_of_int 15) := regval_into_reg (sign_extend' 64 pkv)]> g16).
    assert (HR9 : f2 !!! Regidx (mword_of_int 9) = m !!! Regidx (mword_of_int 9)).
    { unfold f2, g16, f1, g0c. do 4 (rewrite upd_ne; [| vm_compute; discriminate]). reflexivity. }
    assert (Hsbf2 : (autocast (T := mword)
                      (subrange_vec_dec (and_vec (f2 !!! Regidx (mword_of_int 9))
                         (sign_extend' 64 (mword_of_int 255 : mword 12))) 7 0) : mword 8) = sb).
    { unfold sb. rewrite HR9. reflexivity. }
    (* ---- 0x20 -> 0x3c device core ---- *)
    iApply (wp_uartputc_devcore_sconf γ root_ppn γd Φ f2 n l
              with "Hsc Hhs Hcg Htlbinv Ht Hpc Hdinv Hown Hoff").
    iIntros (b) "Hhs Hsc Hcg Htlbinv Hpc Hown Hsent".
    iEval (rewrite Hsbf2) in "Hown". iEval (rewrite Hsbf2) in "Hsent".
    (* ---- 0x3c auipc a5 ---- *)
    iApply (wp_auipc_s_sconf γ root_ppn Φ (mword_of_int (UPS + 0x3c)) (mword_of_int 15) (mword_of_int 0xa : mword 20)
              (ppc_f6' f2 b) n ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi3c").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc".
    iEval (rewrite P40) in "Hpc".
    set (h3c := <[Regidx (mword_of_int 15) := regval_into_reg (add_vec (mword_of_int (UPS + 0x3c)) (auipc_off (mword_of_int 0xa : mword 20)))]> (ppc_f6' f2 b)).
    assert (Hea2 : add_vec (h3c !!! Regidx (mword_of_int 15)) (sign_extend' 64 (mword_of_int 0x878 : mword 12))
                   = (mword_of_int KernelSyms.panicking : mword 64)).
    { unfold h3c. rewrite upd_eq. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite <- Hea2) in "Hpk".
    (* ---- 0x40 lw a5,-1928(a5) : panicking (2nd read) ---- *)
    iApply (wp_lw_s_sconf γ root_ppn Φ (mword_of_int (UPS + 0x40)) (mword_of_int 15) (mword_of_int 15) (mword_of_int 0x878 : mword 12)
              h3c n pv (dqm:=dqm) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi40 Hpk").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc Hpk".
    iEval (rewrite Hea2) in "Hpk".
    iEval (rewrite P44) in "Hpc".
    (* ---- 0x44 c.beqz a5 : falls through (panicking != 0) ---- *)
    iApply (wp_cbeqz_fall_s_sconf γ root_ppn Φ (mword_of_int (UPS + 0x44)) (mword_of_int 10 : mword 8)
              (Cregidx (mword_of_int 7)) (mword_of_int 15)
              (<[Regidx (mword_of_int 15) := regval_into_reg (sign_extend' 64 pv)]> h3c) n
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
              ltac:(rewrite upd_eq; exact Hpv)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi44").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc".
    iEval (rewrite P46) in "Hpc".
    iApply ("Hcont" $! (<[Regidx (mword_of_int 15) := regval_into_reg (sign_extend' 64 pv)]> h3c)
              with "Hhs Hsc Hcg Htlbinv Hpc [%] Hpk Hpkd Hown Hsent").
    (* The body writes only a4/a5/a0, none callee-saved. *)
    unfold callee_saved.
    repeat split;
      unfold h3c, ppc_f6', ppc_f5', ppc_f4', ppc_f2, ppc_f1, f2, g16, f1, g0c;
      repeat (rewrite upd_ne; [| vm_compute; discriminate]); reflexivity.
  Qed.

  (* =================================================================== *)
  (*  THE WHOLE FUNCTION.                                                  *)
  (* =================================================================== *)
  Lemma wp_uartputc_sconf (γ : gname) (root_ppn : mword 44) (γd : uart_names)
      (Φ : mval -> iProp Σ)
      (m0 : regfile) (K : nat)
      (l : list (bv 8)) (pv pkv : mword 32)
      {dqm dqm2 : dfrac}
    : wp_uartputc_sconf_body γ root_ppn γd Φ m0 K l pv pkv dqm dqm2.
  Proof.
    cbv beta delta [wp_uartputc_sconf_body].
    intros ra_idx a0_idx pcE ra0 a00 ret_tgt sb HK Hal0 Hpv Hpkv.
    pose (sp0 := (m0 !!! Regidx csp_rs1 : mword 64)).
    iIntros "Hsc Hhs Hcg Htlbinv #Ht Hpc Hpk Hpkd #Hdinv Hown #Hoff Hcont".
    set (spr := add_vec (m0 !!! Regidx csp_rs1 : mword 64) (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6)))).
    iPoseProof (upi_00 with "Ht") as "Hi00".
    iPoseProof (upi_02 with "Ht") as "Hi02".
    iPoseProof (upi_04 with "Ht") as "Hi04".
    iPoseProof (upi_06 with "Ht") as "Hi06".
    iPoseProof (upi_08 with "Ht") as "Hi08".
    iPoseProof (upi_0a with "Ht") as "Hi0a".
    iPoseProof (upi_46 with "Ht") as "Hi46".
    iPoseProof (upi_48 with "Ht") as "Hi48".
    iPoseProof (upi_4a with "Ht") as "Hi4a".
    iPoseProof (upi_4c with "Ht") as "Hi4c".
    iPoseProof (upi_4e with "Ht") as "Hi4e".
    (* ===== PROLOGUE: 4-slot frame push + 3 saves (ra/s0/s1) + padding ===== *)
    set (R1 := <[Regidx csp_rs1 := regval_into_reg (add_vec (m0 !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))))]> m0).
    (* +0x00 c.addi sp,-32 -- push 4 *)
    assert (Hpush : spr = pa_stk sp0 4).
    { unfold spr, sp0, pa_stk, add_vec_int. apply f_equal.
      apply bv_eq; vm_compute; reflexivity. }
    iApply (wp_caddi_sp_push_s_sconf γ root_ppn Φ pcE (mword_of_int 32 : mword 6) m0 K 4 HK Hpush
              with "Hsc Hhs Hcg Htlbinv Hpc Hi00 [-]").
    iIntros "Hhs Hsc Hcg Hframe Htlbinv Hpc".
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
    assert (Hpp02 : add_vec_int (pcE : mword 64) 2 = mword_of_int (UPS + 0x02)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp02) in "Hpc".
    (* +0x02 c.sdsp ra,24(sp) *)
    iApply (wp_csdsp_s_sconf γ root_ppn Φ (mword_of_int (UPS + 0x02)) (mword_of_int 3 : mword 6) (mword_of_int 1 : mword 5)
              R1 (K - 4)%nat vr24 with "Hsc Hhs Hcg Htlbinv Hpc Hi02 Hr24 [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc Hr24".
    assert (Hpp04 : add_vec_int (mword_of_int (UPS + 0x02) : mword 64) 2 = mword_of_int (UPS + 0x04)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp04) in "Hpc".
    (* +0x04 c.sdsp s0,16(sp) *)
    iApply (wp_csdsp_s_sconf γ root_ppn Φ (mword_of_int (UPS + 0x04)) (mword_of_int 2 : mword 6) (mword_of_int 8 : mword 5)
              R1 (K - 4)%nat vr16 with "Hsc Hhs Hcg Htlbinv Hpc Hi04 Hr16 [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc Hr16".
    assert (Hpp06 : add_vec_int (mword_of_int (UPS + 0x04) : mword 64) 2 = mword_of_int (UPS + 0x06)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp06) in "Hpc".
    (* +0x06 c.sdsp s1,8(sp) *)
    iApply (wp_csdsp_s_sconf γ root_ppn Φ (mword_of_int (UPS + 0x06)) (mword_of_int 1 : mword 6) (mword_of_int 9 : mword 5)
              R1 (K - 4)%nat vr8 with "Hsc Hhs Hcg Htlbinv Hpc Hi06 Hr8 [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc Hr8".
    assert (Hpp08 : add_vec_int (mword_of_int (UPS + 0x06) : mword 64) 2 = mword_of_int (UPS + 0x08)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp08) in "Hpc".
    (* +0x08 c.addi4spn s0,sp,32 *)
    iApply (wp_caddi4spn_s_sconf γ root_ppn Φ (mword_of_int (UPS + 0x08)) (Cregidx (mword_of_int 0)) (mword_of_int 8 : mword 8) (mword_of_int 8 : mword 5)
              R1 (K - 4)%nat ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi08 [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc".
    set (R2 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg (add_vec (R1 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8))))]> R1).
    assert (Hpp0a : add_vec_int (mword_of_int (UPS + 0x08) : mword 64) 2 = mword_of_int (UPS + 0x0a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0a) in "Hpc".
    (* +0x0a c.mv s1,a0 *)
    iApply (wp_cmv_s_sconf γ root_ppn Φ (mword_of_int (UPS + 0x0a)) (mword_of_int 9 : mword 5) (mword_of_int 10 : mword 5)
              R2 (K - 4)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi0a [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc".
    set (R3 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (add_vec zero_reg (R2 !!! Regidx (mword_of_int 10 : mword 5)))]> R2).
    assert (Hpp0c : add_vec_int (mword_of_int (UPS + 0x0a) : mword 64) 2 = mword_of_int (UPS + 0x0c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0c) in "Hpc".
    (* a0 is preserved through the prologue, so R3!!!s1 = add zero a00 *)
    assert (HR2a0 : R2 !!! Regidx (mword_of_int 10 : mword 5) = a00).
    { rewrite /R2 upd_ne; [| vm_compute; discriminate].
      rewrite /R1 upd_ne; [reflexivity | vm_compute; discriminate]. }
    assert (HR3s1 : R3 !!! Regidx (mword_of_int 9 : mword 5) = add_vec zero_reg a00).
    { rewrite /R3 upd_eq. unfold regval_into_reg. rewrite HR2a0. reflexivity. }
    assert (Hsbeq : (autocast (T := mword)
                      (subrange_vec_dec (and_vec (R3 !!! Regidx (mword_of_int 9))
                         (sign_extend' 64 (mword_of_int 255 : mword 12))) 7 0) : mword 8) = sb).
    { unfold sb. rewrite HR3s1. reflexivity. }
    (* ===== BODY (0x0c -> 0x46) ===== *)
    iApply (wp_uartputc_body_sconf γ root_ppn γd Φ R3 (K - 4)%nat l pv pkv (dqm:=dqm) (dqm2:=dqm2)
              Hpv Hpkv
              with "Hsc Hhs Hcg Htlbinv Ht Hpc Hpk Hpkd Hdinv Hown Hoff").
    iIntros (mf) "Hhs Hsc Hcg Htlbinv Hpc %Hcs_body Hpk Hpkd Hown Hsent".
    iEval (rewrite Hsbeq) in "Hown". iEval (rewrite Hsbeq) in "Hsent".
    pose proof Hcs_body as Hcs_body_cs.
    unfold callee_saved in Hcs_body.
    destruct Hcs_body as (B2 & B4 & B8 & B9 & B18 & B19 & B20 & B21 & B22 & B23 & B24 & B25 & B26 & B27).
    (* mf!!!sp = spr, since the body preserves sp *)
    assert (Hmf_sp : mf !!! Regidx csp_rs1 = spr).
    { change (Regidx csp_rs1) with (Regidx (mword_of_int 2 : mword 5)) in *. rewrite B2.
      rewrite /R3 upd_ne; [| vm_compute; discriminate].
      rewrite /R2 upd_ne; [| vm_compute; discriminate].
      rewrite /R1 upd_eq. reflexivity. }
    (* ===== EPILOGUE (0x46 -> 0x4e) ===== *)
    iEval (rewrite HspR1) in "Hr24". iEval (rewrite HspR1) in "Hr16".
    iEval (rewrite HspR1) in "Hr8". iEval (rewrite HspR1) in "Hg4".
    (* +0x46 c.ldsp ra,24(sp) *)
    iApply (wp_cldsp_s_sconf γ root_ppn Φ (mword_of_int (UPS + 0x46)) (mword_of_int 3 : mword 6) (mword_of_int 1 : mword 5)
              mf (K - 4)%nat (R1 !!! Regidx (mword_of_int 1 : mword 5))
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi46 [Hr24] [-]").
    { iEval (rewrite Hmf_sp). iExact "Hr24". }
    iIntros "Hhs Hsc Hcg Htlbinv Hpc Hr24".
    iEval (rewrite Hmf_sp) in "Hr24".
    set (Q46 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (R1 !!! Regidx (mword_of_int 1 : mword 5))]> mf).
    assert (HspQ46 : Q46 !!! Regidx csp_rs1 = spr) by (rewrite /Q46 upd_ne; [ exact Hmf_sp | vm_compute; discriminate ]).
    assert (Hpp48 : add_vec_int (mword_of_int (UPS + 0x46) : mword 64) 2 = mword_of_int (UPS + 0x48)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp48) in "Hpc".
    (* +0x48 c.ldsp s0,16(sp) *)
    iApply (wp_cldsp_s_sconf γ root_ppn Φ (mword_of_int (UPS + 0x48)) (mword_of_int 2 : mword 6) (mword_of_int 8 : mword 5)
              Q46 (K - 4)%nat (R1 !!! Regidx (mword_of_int 8 : mword 5))
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi48 [Hr16] [-]").
    { iEval (rewrite HspQ46). iExact "Hr16". }
    iIntros "Hhs Hsc Hcg Htlbinv Hpc Hr16".
    iEval (rewrite HspQ46) in "Hr16".
    set (Q48 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg (R1 !!! Regidx (mword_of_int 8 : mword 5))]> Q46).
    assert (HspQ48 : Q48 !!! Regidx csp_rs1 = spr) by (rewrite /Q48 upd_ne; [ exact HspQ46 | vm_compute; discriminate ]).
    assert (Hpp4a : add_vec_int (mword_of_int (UPS + 0x48) : mword 64) 2 = mword_of_int (UPS + 0x4a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp4a) in "Hpc".
    (* +0x4a c.ldsp s1,8(sp) *)
    iApply (wp_cldsp_s_sconf γ root_ppn Φ (mword_of_int (UPS + 0x4a)) (mword_of_int 1 : mword 6) (mword_of_int 9 : mword 5)
              Q48 (K - 4)%nat (R1 !!! Regidx (mword_of_int 9 : mword 5))
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi4a [Hr8] [-]").
    { iEval (rewrite HspQ48). iExact "Hr8". }
    iIntros "Hhs Hsc Hcg Htlbinv Hpc Hr8".
    iEval (rewrite HspQ48) in "Hr8".
    set (Q4a := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (R1 !!! Regidx (mword_of_int 9 : mword 5))]> Q48).
    assert (HspQ4a : Q4a !!! Regidx csp_rs1 = spr) by (rewrite /Q4a upd_ne; [ exact HspQ48 | vm_compute; discriminate ]).
    assert (Hpp4c : add_vec_int (mword_of_int (UPS + 0x4a) : mword 64) 2 = mword_of_int (UPS + 0x4c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp4c) in "Hpc".
    (* +0x4c c.addi16sp sp,32 -- pop 4 *)
    set (Q4c := <[Regidx csp_rs1 := regval_into_reg (add_vec (Q4a !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))))]> Q4a).
    assert (HQ4ccsp : Q4c !!! Regidx csp_rs1 = sp0).
    { rewrite /Q4c upd_eq. rewrite HspQ4a. unfold spr, sp0. apply ups_frame_cancel. }
    assert (Hwval : add_vec (Q4a !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))) = sp0).
    { rewrite HspQ4a. unfold spr, sp0. apply ups_frame_cancel. }
    assert (Hpop : Q4a !!! Regidx csp_rs1
                   = pa_stk (add_vec (Q4a !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6)))) 4).
    { rewrite Hwval HspQ4a. unfold spr, sp0, pa_stk, add_vec_int. apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    iAssert (stack_own (add_vec (Q4a !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6)))) 4)
      with "[Hr24 Hr16 Hr8 Hg4]" as "Hframe".
    { rewrite Hwval. rewrite stack_own_slots. cbn [seq].
      iSplitL "Hr24"; [iEval (rewrite -Hb1 HspR1); iExists _; iExact "Hr24"|].
      iSplitL "Hr16"; [iEval (rewrite -Hb2 HspR1); iExists _; iExact "Hr16"|].
      iSplitL "Hr8";  [iEval (rewrite -Hb3 HspR1); iExists _; iExact "Hr8"|].
      iSplitL "Hg4";  [iEval (rewrite -Hb4 HspR1); iExists _; iExact "Hg4"|].
      done. }
    iApply (wp_caddi16sp_pop_s_sconf γ root_ppn Φ (mword_of_int (UPS + 0x4c)) (mword_of_int 2 : mword 6) Q4a
              (K - 4)%nat 4 Hpop
              with "Hsc Hhs Hcg Htlbinv Hpc Hi4c Hframe [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc".
    change (<[Regidx csp_rs1 := regval_into_reg (add_vec (Q4a !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))))]> Q4a) with Q4c.
    assert (HK4 : ((K - 4) + 4)%nat = K) by lia.
    iEval (rewrite HK4) in "Hcg".
    assert (Hpp4e : add_vec_int (mword_of_int (UPS + 0x4c) : mword 64) 2 = mword_of_int (UPS + 0x4e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp4e) in "Hpc".
    (* +0x4e c.ret *)
    assert (HQ4cra : Q4c !!! Regidx (mword_of_int 1 : mword 5) = ra0).
    { rewrite /Q4c upd_ne; [| vm_compute; discriminate].
      rewrite /Q4a upd_ne; [| vm_compute; discriminate].
      rewrite /Q48 upd_ne; [| vm_compute; discriminate].
      rewrite /Q46 upd_eq.
      rewrite /R1 upd_ne; [reflexivity | vm_compute; discriminate]. }
    assert (Hretaligned : eq_vec (access_vec_dec (update_vec_dec (add_vec (Q4c !!! Regidx (mword_of_int 1 : mword 5)) (sign_extend' 64 (zeros' 12))) 0 ('b"0")) 0) ('b"0") = true)
      by (rewrite HQ4cra; exact Hal0).
    iApply (wp_cret_s_sconf γ root_ppn Φ (mword_of_int (UPS + 0x4e)) (mword_of_int 1 : mword 5) Q4c K
              ltac:(vm_compute; discriminate) Hretaligned
              with "Hsc Hhs Hcg Htlbinv Hpc Hi4e [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc".
    assert (Hretf : update_vec_dec (add_vec (Q4c !!! Regidx (mword_of_int 1 : mword 5)) (sign_extend' 64 (zeros' 12))) 0 ('b"0") = ret_tgt)
      by (rewrite HQ4cra; reflexivity).
    iEval (rewrite Hretf) in "Hpc".
    iApply ("Hcont" $! Q4c with "Hsc Hhs Hcg Htlbinv Hpc [%] Hpk Hpkd Hown Hsent").
    (* callee_saved m0 Q4c /\ Q4c!!!ra = ra0 *)
    split; [| exact HQ4cra].
    (* threading: a register untouched by the body threads m0 -> Q4c *)
    assert (Hthread : forall c : mword 5, is_cs_idx c = true ->
              c <> mword_of_int 1 -> c <> csp_rs1 -> c <> mword_of_int 8 -> c <> mword_of_int 9 ->
              Q4c !!! Regidx c = m0 !!! Regidx c).
    { intros c Hcs N1 N2 N8 N9.
      rewrite /Q4c upd_ne; [| congruence].
      rewrite /Q4a upd_ne; [| congruence].
      rewrite /Q48 upd_ne; [| congruence].
      rewrite /Q46 upd_ne; [| congruence].
      rewrite (callee_saved_lookup Hcs_body_cs c Hcs).
      rewrite /R3 upd_ne; [| congruence].
      rewrite /R2 upd_ne; [| congruence].
      rewrite /R1 upd_ne; [reflexivity | congruence]. }
    unfold callee_saved.
    split.
    { (* sp *)
      rewrite /Q4c upd_eq. rewrite HspQ4a. unfold regval_into_reg, spr, sp0.
      apply ups_frame_cancel. }
    split.
    { (* tp *) apply Hthread; vm_compute; first [reflexivity | discriminate]. }
    split.
    { (* s0 *)
      rewrite /Q4c upd_ne; [| vm_compute; discriminate].
      rewrite /Q4a upd_ne; [| vm_compute; discriminate].
      rewrite /Q48 upd_eq.
      rewrite /R1 upd_ne; [reflexivity | vm_compute; discriminate]. }
    split.
    { (* s1 *)
      rewrite /Q4c upd_ne; [| vm_compute; discriminate].
      rewrite /Q4a upd_eq.
      rewrite /R1 upd_ne; [reflexivity | vm_compute; discriminate]. }
    repeat split; apply Hthread; vm_compute; first [reflexivity | discriminate].
  Qed.

End WpSconfUartPutc.

End UartPutcProof.
