(* ProofUartPutc.v -- uartputc_sync over the SIE-agnostic sconf world, AT AN
   ARBITRARY PORT.

     void uartputc_sync(int uid, int c) {
       struct uart *u = &uarts[uid];
       acquire(&u->tx_lock);
       while ((ReadReg(u, LSR) & LSR_TX_IDLE) == 0) ;
       WriteReg(u, THR, c);
       release(&u->tx_lock);
     }

   THE BUMP RESHAPED THIS FUNCTION (XV6_REV 163d39b): 25 instructions became
   41, the frame 32 bytes became 64, and the byte moved from a0 to a1 because
   a0 now carries the PORT INDEX.  Three things follow, and they are the whole
   difference from the pre-bump proof:

   (1) THE PROLOGUE COMPUTES TWO ADDRESSES FROM uid, in callee-saved
       registers that survive the acquire: s3 = uid, s2 = uid*4,
       s1 = ((uid*4 + uid) << 3) + 16 + uarts = `&uarts[uid].tx_lock`, and
       after the call s4 = uarts + ((uid*4 + uid) << 3) = `&uarts[uid]`.
       Every one of those is a closed computation once a0 is pinned to
       [uart_index i], which is what the [ui_*] arithmetic lemmas below are:
       one [destruct i; vm_compute] apiece, stated so the WP script never
       case-splits on the port.

   (2) THE MMIO ADDRESS IS A LOADED VALUE.  `ld a3,0(s4)` reads
       `uarts[uid].base` out of `.data`; the poll addresses a3+5 and the THR
       store a3+0.  The device leaves do not care how the address was
       computed -- they ask [rget m rs1 = uart_pa i off] -- so all the proof
       needs is that the loaded word IS [uart_base i], which is the contract's
       [SpecUartPutc.uart_base_word i] premise, consumed by the ordinary
       8-byte S-mode load leaf.

   (3) THE DEVICE PREMISE IS THE BARE [uart_inv i].  [dev_inv] is the console
       bundle and cannot be stated at port 1; the poll and the store go
       through [WpSconfUartAccess]'s port-indexed leaves, which open exactly
       [uartN i].

   THE TRANSMITTER TOKEN is the LOCK's resource ([UartTxInv.tx_res]): it comes
   out of the acquire at some trace [l] the caller cannot name, and goes back
   in at [l ++ [sb]] on the release.  The caller's own claim is therefore the
   SUBLIST form [UartTxInv.uart_sent_sub] -- another hart may have bytes
   accepted between two of ours -- obtained by pinning [bs `sublist_of` l]
   under [uart_inv i] ([uart_tx_own_sent_sub_at]) while we hold the token, and
   cashed at the end with [uart_sent_sub_snoc].

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
Require Import RegFile.
Require Import HartTp WpNext.
Require Import WpMmodeLeafBase.
Require Import RiscvExtras.
Require Import StackOwn.
Require Import CalleeSaved.
Require Import VcGen.
Require Import Ktier.
Require Import DevModel PowerBoot.
Require Import UartsFields.
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
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Require Import TsoCtx.

(* ===================================================================== *)
(*  THE INDEX ARITHMETIC.  Everything the prologue computes out of a0 is   *)
(*  a closed function of the port, so each step is one [destruct i] and a  *)
(*  [vm_compute].  Proved here, outside the WP script, so the script       *)
(*  itself never splits on [i].                                           *)
(* ===================================================================== *)
Section UartPutcIdx.
Local Open Scope Z_scope.

(* +0x1e  slli s2,a0,2 *)
Lemma ui_slli2 (i : uart_id) :
  shift_bits_left (mword_of_int (uart_index i) : mword 64)
    (subrange_vec_dec (mword_of_int 2 : mword 6) (Z.sub log2_xlen 1) 0)
  = mword_of_int (4 * uart_index i).
Proof. destruct i; apply bv_eq; vm_compute; reflexivity. Qed.

(* +0x22  add s1,s2,a0   /   +0x32  c.add s2,s2,s3 *)
Lemma ui_add5 (i : uart_id) :
  add_vec (mword_of_int (4 * uart_index i) : mword 64)
          (mword_of_int (uart_index i) : mword 64)
  = mword_of_int (5 * uart_index i).
Proof. destruct i; apply bv_eq; vm_compute; reflexivity. Qed.

(* +0x26  c.slli s1,s1,3   /   +0x34  c.slli s2,s2,3 *)
Lemma ui_slli3 (i : uart_id) :
  shift_bits_left (mword_of_int (5 * uart_index i) : mword 64)
    (subrange_vec_dec (mword_of_int 3 : mword 6) (Z.sub log2_xlen 1) 0)
  = mword_of_int (uart_stride * uart_index i).
Proof. destruct i; apply bv_eq; vm_compute; reflexivity. Qed.

(* +0x28  c.addi s1,s1,16 *)
Lemma ui_add16 (i : uart_id) :
  add_vec (mword_of_int (uart_stride * uart_index i) : mword 64)
          (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6)))
  = mword_of_int (uart_stride * uart_index i + 16).
Proof. destruct i; apply bv_eq; vm_compute; reflexivity. Qed.

(* +0x2a  c.add s1,s1,s4 -- the lock FIELD *)
Lemma ui_lock (i : uart_id) :
  add_vec (mword_of_int (uart_stride * uart_index i + 16) : mword 64)
          (mword_of_int KernelSyms.uarts : mword 64)
  = a_tx_lock_at i.
Proof.
  unfold a_tx_lock_at, uart_f_lock, uart_elt.
  destruct i; apply bv_eq; vm_compute; reflexivity.
Qed.

(* +0x36  c.add s4,s4,s2 -- the ELEMENT, whose first word is [base] *)
Lemma ui_elt (i : uart_id) :
  add_vec (mword_of_int KernelSyms.uarts : mword 64)
          (mword_of_int (uart_stride * uart_index i) : mword 64)
  = mword_of_int (uart_f_base i).
Proof.
  unfold uart_f_base, uart_elt.
  destruct i; apply bv_eq; vm_compute; reflexivity.
Qed.

(* the [auipc]/[addi] pair that materialises [uarts] itself *)
Lemma ui_uarts :
  add_vec (add_vec (mword_of_int (KernelSyms.uartputc_sync + 0x16) : mword 64)
                   (auipc_off (mword_of_int 10 : mword 20)))
          (sign_extend' 64 (mword_of_int 2302 : mword 12))
  = (mword_of_int KernelSyms.uarts : mword 64).
Proof. apply bv_eq; vm_compute; reflexivity. Qed.

(* +0x38's loaded word IS the port's MMIO base, and +0x3c's [addi] is the LSR *)
Lemma ui_pa0 (i : uart_id) : (Z_to_bv 64 (uart_base i) : mword 64) = uart_pa i 0.
Proof. destruct i; reflexivity. Qed.

Lemma ui_pa5 (i : uart_id) :
  add_vec (uart_pa i 0) (sign_extend' 64 (mword_of_int 5 : mword 12)) = uart_pa i 5.
Proof. destruct i; apply bv_eq; vm_compute; reflexivity. Qed.

(* [c.mv] writes [add_vec zero_reg x]; at a CONCRETE port both values the
   prologue moves are closed, so the normalisation is a computation *)
Lemma ui_zadd_idx (i : uart_id) :
  add_vec zero_reg (mword_of_int (uart_index i) : mword 64)
  = (mword_of_int (uart_index i) : mword 64).
Proof. destruct i; apply bv_eq; vm_compute; reflexivity. Qed.

Lemma ui_zadd_lock (i : uart_id) :
  add_vec zero_reg (a_tx_lock_at i) = a_tx_lock_at i.
Proof.
  unfold a_tx_lock_at, uart_f_lock, uart_elt.
  destruct i; apply bv_eq; vm_compute; reflexivity.
Qed.

(* an [imm = 0] displacement is the identity, at an address the proof cannot
   compute (the port is abstract) *)
Lemma ui_imm0 (x : mword 64) :
  add_vec x (sign_extend' 64 (mword_of_int 0 : mword 12)) = x.
Proof.
  replace (sign_extend' 64 (mword_of_int 0 : mword 12) : mword 64)
    with (mword_of_int 0 : mword 64) by (apply bv_eq; vm_compute; reflexivity).
  apply kv_addv_zero.
Qed.

End UartPutcIdx.

(* ===================================================================== *)
(*  uartputc_sync's device core, as register-file transformers.           *)
(*                                                                        *)
(*    0x38  ld    a3,0(s4)         -> ppc_f1  (a3 = u->base)              *)
(*    0x3c  addi  a4,a3,5          -> ppc_f2  (a4 = u->base + LSR)        *)
(*    0x40  lbu   a5,0(a4)         -- LSR read (off 5)                    *)
(*    0x44  andi  a5,a5,32         -> ppc_f4' (loop exit, by exit byte)   *)
(*    0x4a  andi  a5,s5,255        -> ppc_f5' (the pre-THR-store map)     *)
(*    0x4e  sb    a5,0(a3)         -- THR write (off 0)                   *)
(* ===================================================================== *)
Section UartPutcMaps.
  Context `{!riscvGS Σ}.

  Definition ppc_f1 (i : uart_id) (m : regfile) : regfile :=
    <[Regidx (mword_of_int 13) := regval_into_reg (uart_pa i 0)]> m.
  Definition ppc_f2 (i : uart_id) (m : regfile) : regfile :=
    <[Regidx (mword_of_int 14) := regval_into_reg
       (add_vec (ppc_f1 i m !!! Regidx (mword_of_int 13))
                (sign_extend' 64 (mword_of_int 5 : mword 12)))]> (ppc_f1 i m).

  Lemma ppc_f1_a3 (i : uart_id) (m : regfile) :
    ppc_f1 i m !!! Regidx (mword_of_int 13) = uart_pa i 0.
  Proof. unfold ppc_f1. rewrite upd_eq. reflexivity. Qed.

  Lemma ppc_f2_a4 (i : uart_id) (m : regfile) :
    ppc_f2 i m !!! Regidx (mword_of_int 14) = uart_pa i 5.
  Proof. unfold ppc_f2. rewrite upd_eq. rewrite (ppc_f1_a3 i m). apply ui_pa5. Qed.

  Lemma ppc_f2_a3 (i : uart_id) (m : regfile) :
    ppc_f2 i m !!! Regidx (mword_of_int 13) = uart_pa i 0.
  Proof.
    unfold ppc_f2. rewrite upd_ne; [| vm_compute; discriminate].
    apply (ppc_f1_a3 i m).
  Qed.

  (* The mask [andi a5,a5,32] applied to the LSR-load value for a read byte. *)
  Definition lsr_masked (b : bv 8) : mword 64 :=
    and_vec (lsr_ldval_of b) (sign_extend' 64 (mword_of_int 32 : mword 12)).

  (* The post-loop register maps, indexed by the EXIT byte [bt] the poll
     observed (not by a UART state, which the caller can no longer name). *)
  Definition ppc_f4' (i : uart_id) (m : regfile) (bt : bv 8) : regfile :=
    <[Regidx (mword_of_int 15) := regval_into_reg (lsr_masked bt)]> (ppc_f2 i m).
  Definition ppc_f5' (i : uart_id) (m : regfile) (bt : bv 8) : regfile :=
    <[Regidx (mword_of_int 15) := regval_into_reg
       (and_vec (ppc_f4' i m bt !!! Regidx (mword_of_int 21))
                (sign_extend' 64 (mword_of_int 255 : mword 12)))]> (ppc_f4' i m bt).

  Lemma ppc_f4'_s5 (i : uart_id) (m : regfile) (bt : bv 8) :
    ppc_f4' i m bt !!! Regidx (mword_of_int 21) = m !!! Regidx (mword_of_int 21).
  Proof.
    unfold ppc_f4', ppc_f2, ppc_f1.
    do 3 (rewrite upd_ne; [| vm_compute; discriminate]). reflexivity.
  Qed.

  Lemma ppc_f5'_a3 (i : uart_id) (m : regfile) (bt : bv 8) :
    ppc_f5' i m bt !!! Regidx (mword_of_int 13) = uart_pa i 0.
  Proof.
    unfold ppc_f5', ppc_f4'.
    do 2 (rewrite upd_ne; [| vm_compute; discriminate]).
    apply (ppc_f2_a3 i m).
  Qed.

  Lemma ppc_f5'_a5 (i : uart_id) (m : regfile) (bt : bv 8) :
    ppc_f5' i m bt !!! Regidx (mword_of_int 15)
    = and_vec (m !!! Regidx (mword_of_int 21)) (sign_extend' 64 (mword_of_int 255 : mword 12)).
  Proof. unfold ppc_f5'. rewrite upd_eq. rewrite (ppc_f4'_s5 i m bt). reflexivity. Qed.

  (* the device core writes only a3/a4/a5, so every other index survives it *)
  Lemma ppc_f5'_cs (i : uart_id) (m : regfile) (bt : bv 8) (c : mword 5) :
    c <> mword_of_int 13 -> c <> mword_of_int 14 -> c <> mword_of_int 15 ->
    ppc_f5' i m bt !!! Regidx c = m !!! Regidx c.
  Proof.
    intros N13 N14 N15.
    unfold ppc_f5', ppc_f4', ppc_f2, ppc_f1.
    rewrite upd_ne; [| congruence].
    rewrite upd_ne; [| congruence].
    rewrite upd_ne; [| congruence].
    rewrite upd_ne; [reflexivity | congruence].
  Qed.

End UartPutcMaps.

Module UartPutcProof (Uart : UART) (Acquire : ACQUIRE) (Release : RELEASE) : UARTPUTC.

Module UAcc := UartAccessProof Uart.

Section ProofUartPutc.
  Context `{!riscvGS Σ, !xv6G Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.

  Context {kt : ktier}.
  (* [rget m k] at a NON-tp index is the plain map lookup ([rget_ne]) -- the
     one-line bridge from a leaf's [rget] to the register-map facts a
     whole-function proof already has. *)
  Local Ltac rgne :=
    rewrite rget_ne;
    [ | let H1 := fresh in let H2 := fresh in
        intro H1; injection H1 as H2; vm_compute in H2; congruence ].

  (* =================================================================== *)
  (*  THE THRE POLL LOOP: 0x40 -> 0x4a, run under [uart_inv i] (Löb).      *)
  (* =================================================================== *)
  Lemma wp_uartputc_poll_sconf `{CID0 : CpuId} (i : uart_id) (γd : uart_names)
      (mentry : regfile) (n : nat) (l : list (bv 8)) (b : bool) (p : mword 64) :
    mentry !!! Regidx (mword_of_int 14) = uart_pa i 5 ->
    sie_cap_gpr kt mentry n b p -∗ kernel_text -∗
    pc_is (mword_of_int (KernelSyms.uartputc_sync + 0x40)) -∗
    uart_inv i γd -∗ uart_tx_own γd l -∗
    wp_next b p (fun (CID : CpuId) =>
      ∀ bt : bv 8,
      sie_cap_gpr kt (<[Regidx (mword_of_int 15) := regval_into_reg (lsr_masked bt)]> mentry) n b p -∗
      pc_is (mword_of_int (KernelSyms.uartputc_sync + 0x4a)) -∗
      uart_tx_own γd l -∗ uart_out_lb γd l -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Ha4e.
    iIntros "Hcg #Ht Hpc #Huinv Hown Hcont".
    assert (P44 : add_vec_int (mword_of_int (KernelSyms.uartputc_sync + 0x40) : mword 64) 4 = mword_of_int (KernelSyms.uartputc_sync + 0x44)) by (apply bv_eq; vm_compute; reflexivity).
    assert (P48 : add_vec_int (mword_of_int (KernelSyms.uartputc_sync + 0x44) : mword 64) 4 = mword_of_int (KernelSyms.uartputc_sync + 0x48)) by (apply bv_eq; vm_compute; reflexivity).
    assert (P4a : add_vec_int (mword_of_int (KernelSyms.uartputc_sync + 0x48) : mword 64) 2 = mword_of_int (KernelSyms.uartputc_sync + 0x4a)) by (apply bv_eq; vm_compute; reflexivity).
    assert (Htgt : add_vec (mword_of_int (KernelSyms.uartputc_sync + 0x48) : mword 64)
                     (sign_extend' 64 (sign_extend' 13 (concat_vec (mword_of_int 252 : mword 8) ('b"0"))))
                   = mword_of_int (KernelSyms.uartputc_sync + 0x40)) by (apply bv_eq; vm_compute; reflexivity).
    iAssert (∀ (CID1 : CpuId) (m : regfile),
      ⌜ m !!! Regidx (mword_of_int 14) = uart_pa i 5 ⌝ -∗
      ⌜ forall Y, <[Regidx (mword_of_int 15) := Y]> m
                = <[Regidx (mword_of_int 15) := Y]> mentry ⌝ -∗
      sie_cap_gpr kt m n b p -∗ pc_is (mword_of_int (KernelSyms.uartputc_sync + 0x40)) -∗ uart_tx_own γd l -∗
      wp_next (CID0:=CID1) b p (fun (CID : CpuId) =>
        ∀ bt : bv 8, sie_cap_gpr kt (<[Regidx (mword_of_int 15) := regval_into_reg (lsr_masked bt)]> mentry) n b p -∗
            pc_is (mword_of_int (KernelSyms.uartputc_sync + 0x4a)) -∗
            uart_tx_own γd l -∗ uart_out_lb γd l -∗ WP (Loop : expr riscv_lang)) -∗
      WP (Loop : expr riscv_lang))%I with "[]" as "Loop".
    { iLöb as "IH". iIntros (CID1 m Ha4m Hagm) "Hcg Hpc Hown Hk".
      (* 0x40  lbu a5,0(a4) *)
      iApply (UAcc.wp_uart_lsr_read_s_sconf_at (CID:=CID1) i γd (mword_of_int (KernelSyms.uartputc_sync + 0x40)) (mword_of_int 15) (mword_of_int 14)
                m n l b ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(rgne; exact Ha4m)
                with "Hcg Hpc [] Huinv Hown").
      { iApply (upi_40 with "Ht"). }
      iIntros (CIDr Hsr bt) "Hcg Hpc Hown Hlb".
      iEval (rewrite P44) in "Hpc".
      (* 0x44  andi a5,a5,32 *)
      iApply (wp_andi_s_sconf (mword_of_int (KernelSyms.uartputc_sync + 0x44)) (mword_of_int 15) (mword_of_int 15) (mword_of_int 32 : mword 12)
                _ (<[Regidx (mword_of_int 15) := regval_into_reg (lsr_ldval_of bt)]> m) n b
                ltac:(vm_compute; discriminate) ltac:(rdok) eq_refl
                with "Hcg Hpc []").
      { iApply (upi_44 with "Ht"). }
      iIntros (CIDa Hsa) "Hcg Hpc".
      iEval (rgne) in "Hcg".
      iEval (rewrite upd_eq upd_upd) in "Hcg".
      change (and_vec (lsr_ldval_of bt) (sign_extend' 64 (mword_of_int 32 : mword 12)))
        with (lsr_masked bt) in *.
      iEval (rewrite P48) in "Hpc".
      (* 0x48  c.beqz a5,0x40 *)
      destruct (lsr_thre_clear bt) eqn:Hcase.
      - iApply (wp_cbeqz_taken_s_sconf (mword_of_int (KernelSyms.uartputc_sync + 0x48)) (mword_of_int 252 : mword 8)
                  (Cregidx (mword_of_int 7)) (mword_of_int 15)
                  (<[Regidx (mword_of_int 15) := regval_into_reg (lsr_masked bt)]> m) n b
                  ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                  ltac:(rgne; rewrite upd_eq; unfold regval_into_reg, lsr_masked; exact Hcase)
                  ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc []").
        { iApply (upi_48 with "Ht"). }
        iNext. iIntros (CIDt Hst) "Hcg Hpc".
        iEval (rewrite Htgt) in "Hpc".
        assert (Hchain : b = false \/ p = zero_reg -> (CIDt : CPU) = (CID1 : CPU)) by wp_next_chain.
        iDestruct (wp_next_shift Hchain with "Hk") as "Hk".
        iApply ("IH" $! CIDt (<[Regidx (mword_of_int 15) := regval_into_reg (lsr_masked bt)]> m)
                  with "[%] [%] Hcg Hpc Hown Hk").
        + rewrite upd_ne; [exact Ha4m | vm_compute; discriminate].
        + intro Y. rewrite upd_upd. exact (Hagm Y).
      - iApply (wp_cbeqz_fall_s_sconf (mword_of_int (KernelSyms.uartputc_sync + 0x48)) (mword_of_int 252 : mword 8)
                  (Cregidx (mword_of_int 7)) (mword_of_int 15)
                  (<[Regidx (mword_of_int 15) := regval_into_reg (lsr_masked bt)]> m) n b
                  ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                  ltac:(rgne; rewrite upd_eq; unfold regval_into_reg, lsr_masked; exact Hcase)
                  with "Hcg Hpc []").
        { iApply (upi_48 with "Ht"). }
        iIntros (CIDf Hsf) "Hcg Hpc".
        iEval (rewrite P4a) in "Hpc".
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
  (*  DEVICE CORE: 0x38 -> 0x52 (base load + LSR addr + poll + byte + THR). *)
  (* =================================================================== *)
  Lemma wp_uartputc_devcore_sconf `{CID0 : CpuId} (i : uart_id) (γd : uart_names)
      (m : regfile) (n : nat) (l : list (bv 8)) (b : bool) (p : mword 64) :
    let sb : mword 8 := autocast (T := mword)
       (subrange_vec_dec (and_vec (m !!! Regidx (mword_of_int 21))
          (sign_extend' 64 (mword_of_int 255 : mword 12))) 7 0) in
    m !!! Regidx (mword_of_int 20) = mword_of_int (uart_f_base i) ->
    sie_cap_gpr kt m n b p -∗ kernel_text -∗
    pc_is (mword_of_int (KernelSyms.uartputc_sync + 0x38)) -∗
    uart_inv i γd -∗ uart_base_word i -∗ uart_tx_own γd l -∗ uart_dlab_off γd -∗
    wp_next b p (fun (CID : CpuId) =>
      ∀ bt : bv 8,
      sie_cap_gpr kt (ppc_f5' i m bt) n b p -∗ pc_is (mword_of_int (KernelSyms.uartputc_sync + 0x52)) -∗
      uart_tx_own γd (l ++ [sb]) -∗ uart_sent γd (l ++ [sb]) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros sb Hs4.
    iIntros "Hcg #Ht Hpc #Huinv #Hbw Hown #Hoff Hcont".
    assert (P3c : add_vec_int (mword_of_int (KernelSyms.uartputc_sync + 0x38) : mword 64) 4 = mword_of_int (KernelSyms.uartputc_sync + 0x3c)) by (apply bv_eq; vm_compute; reflexivity).
    assert (P40 : add_vec_int (mword_of_int (KernelSyms.uartputc_sync + 0x3c) : mword 64) 4 = mword_of_int (KernelSyms.uartputc_sync + 0x40)) by (apply bv_eq; vm_compute; reflexivity).
    assert (P4e : add_vec_int (mword_of_int (KernelSyms.uartputc_sync + 0x4a) : mword 64) 4 = mword_of_int (KernelSyms.uartputc_sync + 0x4e)) by (apply bv_eq; vm_compute; reflexivity).
    assert (P52 : add_vec_int (mword_of_int (KernelSyms.uartputc_sync + 0x4e) : mword 64) 4 = mword_of_int (KernelSyms.uartputc_sync + 0x52)) by (apply bv_eq; vm_compute; reflexivity).
    (* 0x38  ld a3,0(s4) -- the MMIO base out of .data *)
    assert (Hld : add_vec (rget m (mword_of_int 20 : mword 5))
                    (sign_extend' 64 (mword_of_int 0 : mword 12))
                  = pa_of_z (uart_f_base i)).
    { rgne. rewrite Hs4. apply ui_imm0. }
    iEval (rewrite /uart_base_word -Hld) in "Hbw".
    iApply (wp_ld_s_sconf (kt := kt) (ktd := KT0) (mword_of_int (KernelSyms.uartputc_sync + 0x38))
              (mword_of_int 13) (mword_of_int 20) (mword_of_int 0 : mword 12)
              m n (Z_to_bv 64 (uart_base i)) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] [Hbw]").
    { iApply (upi_38 with "Ht"). }
    { iExact "Hbw". }
    iIntros (CID1 Hs1) "Hcg Hpc _".
    iEval (rewrite (ui_pa0 i)) in "Hcg".
    iEval (change (<[Regidx (mword_of_int 13) := regval_into_reg (uart_pa i 0)]> m)
             with (ppc_f1 i m)) in "Hcg".
    iEval (rewrite P3c) in "Hpc".
    (* 0x3c  addi a4,a3,5 *)
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.uartputc_sync + 0x3c)) (mword_of_int 14) (mword_of_int 13) (mword_of_int 5 : mword 12)
              (ppc_f1 i m) n b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (upi_3c with "Ht"). }
    iIntros (CID2 Hs2) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    iEval (change (<[Regidx (mword_of_int 14) := regval_into_reg
        (add_vec (ppc_f1 i m !!! Regidx (mword_of_int 13)) (sign_extend' 64 (mword_of_int 5 : mword 12)))]> (ppc_f1 i m))
      with (ppc_f2 i m)) in "Hcg".
    iEval (rewrite P40) in "Hpc".
    (* 0x40 -> 0x4a  the poll loop *)
    iApply (wp_uartputc_poll_sconf (CID0:=CID2) i γd (ppc_f2 i m) n l b p (ppc_f2_a4 i m)
              with "Hcg Ht Hpc Huinv Hown").
    iIntros (CIDp Hsp bt) "Hcg Hpc Hown #Hlb".
    iEval (change (<[Regidx (mword_of_int 15) := regval_into_reg (lsr_masked bt)]> (ppc_f2 i m))
             with (ppc_f4' i m bt)) in "Hcg".
    (* 0x4a  andi a5,s5,255 *)
    iApply (wp_andi_s_sconf (mword_of_int (KernelSyms.uartputc_sync + 0x4a)) (mword_of_int 15) (mword_of_int 21) (mword_of_int 255 : mword 12)
              _ (ppc_f4' i m bt) n b ltac:(vm_compute; discriminate) ltac:(rdok) eq_refl
              with "Hcg Hpc []").
    { iApply (upi_4a with "Ht"). }
    iIntros (CID3 Hs3) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    iEval (change (<[Regidx (mword_of_int 15) := regval_into_reg (and_vec (ppc_f4' i m bt !!! Regidx (mword_of_int 21))
             (sign_extend' 64 (mword_of_int 255 : mword 12)))]> (ppc_f4' i m bt))
      with (ppc_f5' i m bt)) in "Hcg".
    iEval (rewrite P4e) in "Hpc".
    (* 0x4e  sb a5,0(a3)  -- THR write *)
    assert (Hsbb : (autocast (T := mword)
                      (subrange_vec_dec (rget (ppc_f5' i m bt) (mword_of_int 15 : mword 5))
                         (Z.sub (Z.mul 1 8) 1) 0) : mword 8) = sb).
    { rewrite (rget_ne (ppc_f5' i m bt) (mword_of_int 15 : mword 5) ltac:(vm_compute; discriminate)).
      unfold sb. rewrite (ppc_f5'_a5 i m bt). reflexivity. }
    iApply (UAcc.wp_uart_thr_write_s_sconf_at (CID:=CID3) i γd (mword_of_int (KernelSyms.uartputc_sync + 0x4e)) (mword_of_int 15) (mword_of_int 13)
              (ppc_f5' i m bt) n l b ltac:(rgne; exact (ppc_f5'_a3 i m bt))
              with "Hcg Hpc [] Huinv Hown Hlb Hoff").
    { iApply (upi_4e with "Ht"). }
    iIntros (CID5 Hs5) "Hcg Hpc Hown Hsent".
    iEval (rewrite Hsbb) in "Hown". iEval (rewrite Hsbb) in "Hsent".
    iEval (rewrite P52) in "Hpc".
    assert (Hchain : b = false \/ p = zero_reg -> (CID5 : CPU) = (CID0 : CPU)) by wp_next_chain.
    iSpecialize ("Hcont" $! CID5 with "[%]"); [exact Hchain|].
    iApply ("Hcont" $! bt with "Hcg Hpc Hown Hsent").
  Qed.

  (* =================================================================== *)
  (*  THE WHOLE FUNCTION.                                                  *)
  (* =================================================================== *)
  Lemma wp_uartputc_sconf (i : uart_id) (γl : gname) (γd : uart_names)
      (m0 : regfile) (K : nat) (bs : list (bv 8)) (n : nat) (eb : bool)
      (b : bool) (p : mword 64) (lks : gset string)
    : wp_uartputc_sconf_body kt i γl γd m0 K bs n eb b p lks.
  Proof.
    cbv beta delta [wp_uartputc_sconf_body].
    intros ra_idx a0_idx a1_idx pcE ra0 a10 ret_tgt sb HK Ha0 Hn Hfresh.
    assert (HK18 : (18 <= K)%nat) by (exact HK).
    assert (HK8 : (8 <= K)%nat) by lia.
    assert (Hav : (10 <= K - 8)%nat) by lia.
    pose (sp0 := (m0 !!! Regidx csp_rs1 : mword 64)).
    iIntros "Hcg Hcpu #Ht Hpc #Huinv #Hbw #Htxl #Hsubbs Hcont".
    iDestruct (cpu_own_eb_agree with "Hcg Hcpu") as %Hbeq.
    iDestruct (is_txlock_at_lock with "Htxl") as "#Hlk".
    iDestruct (is_txlock_at_dlab with "Htxl") as "#Hoff".
    set (spr := add_vec (m0 !!! Regidx csp_rs1 : mword 64) (sign_extend' 64 (caddi16sp_imm (mword_of_int 60 : mword 6)))).
    (* ===== PROLOGUE: 8-slot frame push + 7 saves (ra/s0/s1/s2/s3/s4/s5) ===== *)
    set (R1 := <[Regidx csp_rs1 := regval_into_reg (add_vec (m0 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 60 : mword 6))))]> m0).
    assert (Hpush : spr = pa_stk sp0 8).
    { unfold spr, sp0, pa_stk, add_vec_int. apply f_equal.
      apply bv_eq; vm_compute; reflexivity. }
    iApply (wp_caddi16sp_push_s_sconf pcE (mword_of_int 60 : mword 6) m0 K 8 b HK8 Hpush
              with "Hcg Hpc []").
    { iApply (upi_00 with "Ht"). }
    iIntros (CIDp1 Hsp1) "Hcg Hframe Hpc".
    assert (HspR1 : R1 !!! Regidx csp_rs1 = spr)
      by (rewrite /R1 upd_eq; reflexivity).
    iEval (rewrite (stack_own_slots (KTR := kt)); cbn [seq]) in "Hframe".
    iDestruct "Hframe" as "(S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & _)".
    iDestruct "S1" as (vr1) "Hr1". iDestruct "S2" as (vr2) "Hr2".
    iDestruct "S3" as (vr3) "Hr3". iDestruct "S4" as (vr4) "Hr4".
    iDestruct "S5" as (vr5) "Hr5". iDestruct "S6" as (vr6) "Hr6".
    iDestruct "S7" as (vr7) "Hr7". iDestruct "S8" as (vr8) "Hr8".
    (* slot k is at sp + 8*(8-k) *)
    assert (Hb1 : add_vec (R1 !!! Regidx csp_rs1) (zero_extend' 64 (concat_vec (mword_of_int 7 : mword 6) ('b"000"))) = pa_stk sp0 1).
    { rewrite HspR1. unfold spr, sp0, pa_stk, add_vec_int. rewrite add_vec_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb2 : add_vec (R1 !!! Regidx csp_rs1) (zero_extend' 64 (concat_vec (mword_of_int 6 : mword 6) ('b"000"))) = pa_stk sp0 2).
    { rewrite HspR1. unfold spr, sp0, pa_stk, add_vec_int. rewrite add_vec_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb3 : add_vec (R1 !!! Regidx csp_rs1) (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000"))) = pa_stk sp0 3).
    { rewrite HspR1. unfold spr, sp0, pa_stk, add_vec_int. rewrite add_vec_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb4 : add_vec (R1 !!! Regidx csp_rs1) (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000"))) = pa_stk sp0 4).
    { rewrite HspR1. unfold spr, sp0, pa_stk, add_vec_int. rewrite add_vec_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb5 : add_vec (R1 !!! Regidx csp_rs1) (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000"))) = pa_stk sp0 5).
    { rewrite HspR1. unfold spr, sp0, pa_stk, add_vec_int. rewrite add_vec_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb6 : add_vec (R1 !!! Regidx csp_rs1) (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000"))) = pa_stk sp0 6).
    { rewrite HspR1. unfold spr, sp0, pa_stk, add_vec_int. rewrite add_vec_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb7 : add_vec (R1 !!! Regidx csp_rs1) (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) = pa_stk sp0 7).
    { rewrite HspR1. unfold spr, sp0, pa_stk, add_vec_int. rewrite add_vec_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb8 : add_vec (R1 !!! Regidx csp_rs1) (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000"))) = pa_stk sp0 8).
    { rewrite HspR1. unfold spr, sp0, pa_stk, add_vec_int. rewrite add_vec_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    iEval (rewrite -Hb1) in "Hr1". iEval (rewrite -Hb2) in "Hr2".
    iEval (rewrite -Hb3) in "Hr3". iEval (rewrite -Hb4) in "Hr4".
    iEval (rewrite -Hb5) in "Hr5". iEval (rewrite -Hb6) in "Hr6".
    iEval (rewrite -Hb7) in "Hr7". iEval (rewrite -Hb8) in "Hr8".
    assert (Hpp02 : add_vec_int (pcE : mword 64) 2 = mword_of_int (KernelSyms.uartputc_sync + 0x02)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp02) in "Hpc".
    (* +0x02 .. +0x0e: the seven callee-saved spills *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.uartputc_sync + 0x02)) (mword_of_int 7 : mword 6) (mword_of_int 1 : mword 5)
              R1 (K - 8)%nat vr1 b with "Hcg Hpc [] Hr1").
    { iApply (upi_02 with "Ht"). }
    iIntros (CIDs1 Hss1) "Hcg Hpc Hr1".
    assert (Hpp04 : add_vec_int (mword_of_int (KernelSyms.uartputc_sync + 0x02) : mword 64) 2 = mword_of_int (KernelSyms.uartputc_sync + 0x04)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp04) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.uartputc_sync + 0x04)) (mword_of_int 6 : mword 6) (mword_of_int 8 : mword 5)
              R1 (K - 8)%nat vr2 b with "Hcg Hpc [] Hr2").
    { iApply (upi_04 with "Ht"). }
    iIntros (CIDs2 Hss2) "Hcg Hpc Hr2".
    assert (Hpp06 : add_vec_int (mword_of_int (KernelSyms.uartputc_sync + 0x04) : mword 64) 2 = mword_of_int (KernelSyms.uartputc_sync + 0x06)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp06) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.uartputc_sync + 0x06)) (mword_of_int 5 : mword 6) (mword_of_int 9 : mword 5)
              R1 (K - 8)%nat vr3 b with "Hcg Hpc [] Hr3").
    { iApply (upi_06 with "Ht"). }
    iIntros (CIDs3 Hss3) "Hcg Hpc Hr3".
    assert (Hpp08 : add_vec_int (mword_of_int (KernelSyms.uartputc_sync + 0x06) : mword 64) 2 = mword_of_int (KernelSyms.uartputc_sync + 0x08)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp08) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.uartputc_sync + 0x08)) (mword_of_int 4 : mword 6) (mword_of_int 18 : mword 5)
              R1 (K - 8)%nat vr4 b with "Hcg Hpc [] Hr4").
    { iApply (upi_08 with "Ht"). }
    iIntros (CIDs4 Hss4) "Hcg Hpc Hr4".
    assert (Hpp0a : add_vec_int (mword_of_int (KernelSyms.uartputc_sync + 0x08) : mword 64) 2 = mword_of_int (KernelSyms.uartputc_sync + 0x0a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0a) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.uartputc_sync + 0x0a)) (mword_of_int 3 : mword 6) (mword_of_int 19 : mword 5)
              R1 (K - 8)%nat vr5 b with "Hcg Hpc [] Hr5").
    { iApply (upi_0a with "Ht"). }
    iIntros (CIDs5 Hss5) "Hcg Hpc Hr5".
    assert (Hpp0c : add_vec_int (mword_of_int (KernelSyms.uartputc_sync + 0x0a) : mword 64) 2 = mword_of_int (KernelSyms.uartputc_sync + 0x0c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0c) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.uartputc_sync + 0x0c)) (mword_of_int 2 : mword 6) (mword_of_int 20 : mword 5)
              R1 (K - 8)%nat vr6 b with "Hcg Hpc [] Hr6").
    { iApply (upi_0c with "Ht"). }
    iIntros (CIDs6 Hss6) "Hcg Hpc Hr6".
    assert (Hpp0e : add_vec_int (mword_of_int (KernelSyms.uartputc_sync + 0x0c) : mword 64) 2 = mword_of_int (KernelSyms.uartputc_sync + 0x0e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0e) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.uartputc_sync + 0x0e)) (mword_of_int 1 : mword 6) (mword_of_int 21 : mword 5)
              R1 (K - 8)%nat vr7 b with "Hcg Hpc [] Hr7").
    { iApply (upi_0e with "Ht"). }
    iIntros (CIDs7 Hss7) "Hcg Hpc Hr7".
    assert (Hpp10 : add_vec_int (mword_of_int (KernelSyms.uartputc_sync + 0x0e) : mword 64) 2 = mword_of_int (KernelSyms.uartputc_sync + 0x10)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp10) in "Hpc".
    (* +0x10 c.addi4spn s0,sp,64 *)
    iApply (wp_caddi4spn_s_sconf (mword_of_int (KernelSyms.uartputc_sync + 0x10)) (Cregidx (mword_of_int 0)) (mword_of_int 16 : mword 8) (mword_of_int 8 : mword 5)
              R1 (K - 8)%nat b ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (upi_10 with "Ht"). }
    iIntros (CIDp5 Hsp5) "Hcg Hpc".
    set (R2 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg (add_vec (R1 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 16 : mword 8))))]> R1).
    assert (Hpp12 : add_vec_int (mword_of_int (KernelSyms.uartputc_sync + 0x10) : mword 64) 2 = mword_of_int (KernelSyms.uartputc_sync + 0x12)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp12) in "Hpc".
    (* +0x12 c.mv s3,a0 -- the PORT INDEX into a callee-saved register *)
    assert (HR2a0 : R2 !!! Regidx (mword_of_int 10 : mword 5) = mword_of_int (uart_index i)).
    { rewrite /R2 upd_ne; [| vm_compute; discriminate].
      rewrite /R1 upd_ne; [exact Ha0 | vm_compute; discriminate]. }
    assert (HR2a1 : R2 !!! Regidx (mword_of_int 11 : mword 5) = a10).
    { rewrite /R2 upd_ne; [| vm_compute; discriminate].
      rewrite /R1 upd_ne; [reflexivity | vm_compute; discriminate]. }
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.uartputc_sync + 0x12)) (mword_of_int 19 : mword 5) (mword_of_int 10 : mword 5)
              R2 (K - 8)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (upi_12 with "Ht"). }
    iIntros (CIDp6 Hsp6) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    iEval (rewrite HR2a0 (ui_zadd_idx i)) in "Hcg".
    set (R3 := <[Regidx (mword_of_int 19 : mword 5) := regval_into_reg (mword_of_int (uart_index i) : mword 64)]> R2).
    assert (Hpp14 : add_vec_int (mword_of_int (KernelSyms.uartputc_sync + 0x12) : mword 64) 2 = mword_of_int (KernelSyms.uartputc_sync + 0x14)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp14) in "Hpc".
    (* +0x14 c.mv s5,a1 -- the BYTE into a callee-saved register *)
    assert (HR3a1 : R3 !!! Regidx (mword_of_int 11 : mword 5) = a10)
      by (rewrite /R3 upd_ne; [exact HR2a1 | vm_compute; discriminate]).
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.uartputc_sync + 0x14)) (mword_of_int 21 : mword 5) (mword_of_int 11 : mword 5)
              R3 (K - 8)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (upi_14 with "Ht"). }
    iIntros (CIDp7 Hsp7) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    iEval (rewrite HR3a1) in "Hcg".
    set (R4 := <[Regidx (mword_of_int 21 : mword 5) := regval_into_reg (add_vec zero_reg a10)]> R3).
    assert (Hpp16 : add_vec_int (mword_of_int (KernelSyms.uartputc_sync + 0x14) : mword 64) 2 = mword_of_int (KernelSyms.uartputc_sync + 0x16)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp16) in "Hpc".
    (* +0x16 auipc s4,0xa ; +0x1a addi s4,s4,-1794 -> &uarts *)
    iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.uartputc_sync + 0x16)) (mword_of_int 20) (mword_of_int 10 : mword 20)
              R4 (K - 8)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (upi_16 with "Ht"). }
    iIntros (CIDp8 Hsp8) "Hcg Hpc".
    set (G16 := <[Regidx (mword_of_int 20) := regval_into_reg (add_vec (mword_of_int (KernelSyms.uartputc_sync + 0x16)) (auipc_off (mword_of_int 10 : mword 20)))]> R4).
    assert (Hpp1a : add_vec_int (mword_of_int (KernelSyms.uartputc_sync + 0x16) : mword 64) 4 = mword_of_int (KernelSyms.uartputc_sync + 0x1a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp1a) in "Hpc".
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.uartputc_sync + 0x1a)) (mword_of_int 20) (mword_of_int 20) (mword_of_int 2302 : mword 12)
              G16 (K - 8)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (upi_1a with "Ht"). }
    iIntros (CIDp9 Hsp9) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    iEval (rewrite /G16 upd_eq ui_uarts) in "Hcg".
    set (G1a := <[Regidx (mword_of_int 20 : mword 5) := regval_into_reg (mword_of_int KernelSyms.uarts : mword 64)]> G16).
    assert (HG1as4 : G1a !!! Regidx (mword_of_int 20 : mword 5) = (mword_of_int KernelSyms.uarts : mword 64))
      by (rewrite /G1a upd_eq; reflexivity).
    assert (HG1aa0 : G1a !!! Regidx (mword_of_int 10 : mword 5) = mword_of_int (uart_index i)).
    { rewrite /G1a upd_ne; [| vm_compute; discriminate].
      rewrite /G16 upd_ne; [| vm_compute; discriminate].
      rewrite /R4 upd_ne; [| vm_compute; discriminate].
      rewrite /R3 upd_ne; [exact HR2a0 | vm_compute; discriminate]. }
    assert (Hpp1e : add_vec_int (mword_of_int (KernelSyms.uartputc_sync + 0x1a) : mword 64) 4 = mword_of_int (KernelSyms.uartputc_sync + 0x1e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp1e) in "Hpc".
    (* +0x1e slli s2,a0,2 *)
    iApply (wp_slli_s_sconf (mword_of_int (KernelSyms.uartputc_sync + 0x1e)) (mword_of_int 18) (mword_of_int 10) (mword_of_int 2 : mword 6)
              (mword_of_int (4 * uart_index i)) G1a (K - 8)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(rgne; rewrite HG1aa0; apply ui_slli2)
              with "Hcg Hpc []").
    { iApply (upi_1e with "Ht"). }
    iIntros (CIDq1 Hsq1) "Hcg Hpc".
    set (G1e := <[Regidx (mword_of_int 18) := regval_into_reg (mword_of_int (4 * uart_index i) : mword 64)]> G1a).
    assert (HG1es2 : G1e !!! Regidx (mword_of_int 18 : mword 5) = (mword_of_int (4 * uart_index i) : mword 64))
      by (rewrite /G1e upd_eq; reflexivity).
    assert (HG1ea0 : G1e !!! Regidx (mword_of_int 10 : mword 5) = mword_of_int (uart_index i))
      by (rewrite /G1e upd_ne; [exact HG1aa0 | vm_compute; discriminate]).
    assert (HG1es4 : G1e !!! Regidx (mword_of_int 20 : mword 5) = (mword_of_int KernelSyms.uarts : mword 64))
      by (rewrite /G1e upd_ne; [exact HG1as4 | vm_compute; discriminate]).
    assert (Hpp22 : add_vec_int (mword_of_int (KernelSyms.uartputc_sync + 0x1e) : mword 64) 4 = mword_of_int (KernelSyms.uartputc_sync + 0x22)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp22) in "Hpc".
    (* +0x22 add s1,s2,a0 *)
    iApply (wp_add_s_sconf (mword_of_int (KernelSyms.uartputc_sync + 0x22)) (mword_of_int 9) (mword_of_int 18) (mword_of_int 10)
              (mword_of_int (5 * uart_index i)) G1e (K - 8)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(rgne; rgne; rewrite HG1es2 HG1ea0; apply ui_add5)
              with "Hcg Hpc []").
    { iApply (upi_22 with "Ht"). }
    iIntros (CIDq2 Hsq2) "Hcg Hpc".
    set (G22 := <[Regidx (mword_of_int 9) := regval_into_reg (mword_of_int (5 * uart_index i) : mword 64)]> G1e).
    assert (HG22s1 : G22 !!! Regidx (mword_of_int 9 : mword 5) = (mword_of_int (5 * uart_index i) : mword 64))
      by (rewrite /G22 upd_eq; reflexivity).
    assert (HG22s4 : G22 !!! Regidx (mword_of_int 20 : mword 5) = (mword_of_int KernelSyms.uarts : mword 64))
      by (rewrite /G22 upd_ne; [exact HG1es4 | vm_compute; discriminate]).
    assert (Hpp26 : add_vec_int (mword_of_int (KernelSyms.uartputc_sync + 0x22) : mword 64) 4 = mword_of_int (KernelSyms.uartputc_sync + 0x26)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp26) in "Hpc".
    (* +0x26 c.slli s1,s1,3 *)
    iApply (wp_cslli_s_sconf (mword_of_int (KernelSyms.uartputc_sync + 0x26)) (Regidx (mword_of_int 9)) (mword_of_int 9) (mword_of_int 3 : mword 6)
              G22 (K - 8)%nat b eq_refl ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (upi_26 with "Ht"). }
    iIntros (CIDq3 Hsq3) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    iEval (rewrite HG22s1 (ui_slli3 i)) in "Hcg".
    set (G26 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (mword_of_int (uart_stride * uart_index i) : mword 64)]> G22).
    assert (HG26s1 : G26 !!! Regidx (mword_of_int 9 : mword 5) = (mword_of_int (uart_stride * uart_index i) : mword 64))
      by (rewrite /G26 upd_eq; reflexivity).
    assert (HG26s4 : G26 !!! Regidx (mword_of_int 20 : mword 5) = (mword_of_int KernelSyms.uarts : mword 64))
      by (rewrite /G26 upd_ne; [exact HG22s4 | vm_compute; discriminate]).
    assert (Hpp28 : add_vec_int (mword_of_int (KernelSyms.uartputc_sync + 0x26) : mword 64) 2 = mword_of_int (KernelSyms.uartputc_sync + 0x28)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp28) in "Hpc".
    (* +0x28 c.addi s1,s1,16 *)
    iApply (wp_caddi_s_sconf (mword_of_int (KernelSyms.uartputc_sync + 0x28)) (mword_of_int 9) (mword_of_int 16 : mword 6)
              G26 (K - 8)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (upi_28 with "Ht"). }
    iIntros (CIDq4 Hsq4) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    iEval (rewrite HG26s1 (ui_add16 i)) in "Hcg".
    set (G28 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (mword_of_int (uart_stride * uart_index i + 16) : mword 64)]> G26).
    assert (HG28s1 : G28 !!! Regidx (mword_of_int 9 : mword 5) = (mword_of_int (uart_stride * uart_index i + 16) : mword 64))
      by (rewrite /G28 upd_eq; reflexivity).
    assert (HG28s4 : G28 !!! Regidx (mword_of_int 20 : mword 5) = (mword_of_int KernelSyms.uarts : mword 64))
      by (rewrite /G28 upd_ne; [exact HG26s4 | vm_compute; discriminate]).
    assert (Hpp2a : add_vec_int (mword_of_int (KernelSyms.uartputc_sync + 0x28) : mword 64) 2 = mword_of_int (KernelSyms.uartputc_sync + 0x2a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp2a) in "Hpc".
    (* +0x2a c.add s1,s1,s4 -> &uarts[uid].tx_lock *)
    iApply (wp_cadd_s_sconf (mword_of_int (KernelSyms.uartputc_sync + 0x2a)) (mword_of_int 9) (mword_of_int 20)
              G28 (K - 8)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (upi_2a with "Ht"). }
    iIntros (CIDq5 Hsq5) "Hcg Hpc".
    iEval (rgne) in "Hcg". iEval (rgne) in "Hcg".
    iEval (rewrite HG28s1 HG28s4 (ui_lock i)) in "Hcg".
    set (G2a := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (a_tx_lock_at i)]> G28).
    assert (HG2as1 : G2a !!! Regidx (mword_of_int 9 : mword 5) = a_tx_lock_at i)
      by (rewrite /G2a upd_eq; reflexivity).
    assert (Hpp2c : add_vec_int (mword_of_int (KernelSyms.uartputc_sync + 0x2a) : mword 64) 2 = mword_of_int (KernelSyms.uartputc_sync + 0x2c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp2c) in "Hpc".
    (* +0x2c c.mv a0,s1 *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.uartputc_sync + 0x2c)) (mword_of_int 10 : mword 5) (mword_of_int 9 : mword 5)
              G2a (K - 8)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (upi_2c with "Ht"). }
    iIntros (CIDq6 Hsq6) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    iEval (rewrite HG2as1 (ui_zadd_lock i)) in "Hcg".
    set (G2c := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg (a_tx_lock_at i)]> G2a).
    assert (Hpp2e : add_vec_int (mword_of_int (KernelSyms.uartputc_sync + 0x2c) : mword 64) 2 = mword_of_int (KernelSyms.uartputc_sync + 0x2e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp2e) in "Hpc".
    (* +0x2e jal ra,acquire *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.uartputc_sync + 0x2e)) (mword_of_int 1 : mword 5) (mword_of_int 638 : mword 21)
              G2c (K - 8)%nat b ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (upi_2e with "Ht"). }
    iIntros (CIDq7 Hsq7) "Hcg Hpc".
    set (G2e := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.uartputc_sync + 0x2e) : mword 64) 4)]> G2c).
    assert (Hjacq : add_vec (mword_of_int (KernelSyms.uartputc_sync + 0x2e) : mword 64) (sign_extend' 64 (mword_of_int 638 : mword 21)) = mword_of_int KernelSyms.acquire)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hjacq) in "Hpc".
    assert (HG2ea0 : G2e !!! Regidx (mword_of_int 10 : mword 5) = a_tx_lock_at i).
    { rewrite /G2e upd_ne; [| vm_compute; discriminate].
      rewrite /G2c upd_eq; reflexivity. }
    assert (HG2era : G2e !!! Regidx (mword_of_int 1 : mword 5)
                     = regval_into_reg (add_vec_int (mword_of_int (KernelSyms.uartputc_sync + 0x2e) : mword 64) 4))
      by (rewrite /G2e upd_eq; reflexivity).
    (* the four callee-saved values the body still needs after the call *)
    assert (HG2es1 : G2e !!! Regidx (mword_of_int 9 : mword 5) = a_tx_lock_at i).
    { rewrite /G2e upd_ne; [| vm_compute; discriminate].
      rewrite /G2c upd_ne; [exact HG2as1 | vm_compute; discriminate]. }
    assert (HG2es2 : G2e !!! Regidx (mword_of_int 18 : mword 5) = (mword_of_int (4 * uart_index i) : mword 64)).
    { rewrite /G2e upd_ne; [| vm_compute; discriminate].
      rewrite /G2c upd_ne; [| vm_compute; discriminate].
      rewrite /G2a upd_ne; [| vm_compute; discriminate].
      rewrite /G28 upd_ne; [| vm_compute; discriminate].
      rewrite /G26 upd_ne; [| vm_compute; discriminate].
      rewrite /G22 upd_ne; [| vm_compute; discriminate].
      rewrite /G1e upd_eq; reflexivity. }
    assert (HG2es3 : G2e !!! Regidx (mword_of_int 19 : mword 5) = (mword_of_int (uart_index i) : mword 64)).
    { rewrite /G2e upd_ne; [| vm_compute; discriminate].
      rewrite /G2c upd_ne; [| vm_compute; discriminate].
      rewrite /G2a upd_ne; [| vm_compute; discriminate].
      rewrite /G28 upd_ne; [| vm_compute; discriminate].
      rewrite /G26 upd_ne; [| vm_compute; discriminate].
      rewrite /G22 upd_ne; [| vm_compute; discriminate].
      rewrite /G1e upd_ne; [| vm_compute; discriminate].
      rewrite /G1a upd_ne; [| vm_compute; discriminate].
      rewrite /G16 upd_ne; [| vm_compute; discriminate].
      rewrite /R4 upd_ne; [| vm_compute; discriminate].
      rewrite /R3 upd_eq; reflexivity. }
    assert (HG2es4 : G2e !!! Regidx (mword_of_int 20 : mword 5) = (mword_of_int KernelSyms.uarts : mword 64)).
    { rewrite /G2e upd_ne; [| vm_compute; discriminate].
      rewrite /G2c upd_ne; [| vm_compute; discriminate].
      rewrite /G2a upd_ne; [exact HG28s4 | vm_compute; discriminate]. }
    assert (HG2es5 : G2e !!! Regidx (mword_of_int 21 : mword 5) = add_vec zero_reg a10).
    { rewrite /G2e upd_ne; [| vm_compute; discriminate].
      rewrite /G2c upd_ne; [| vm_compute; discriminate].
      rewrite /G2a upd_ne; [| vm_compute; discriminate].
      rewrite /G28 upd_ne; [| vm_compute; discriminate].
      rewrite /G26 upd_ne; [| vm_compute; discriminate].
      rewrite /G22 upd_ne; [| vm_compute; discriminate].
      rewrite /G1e upd_ne; [| vm_compute; discriminate].
      rewrite /G1a upd_ne; [| vm_compute; discriminate].
      rewrite /G16 upd_ne; [| vm_compute; discriminate].
      rewrite /R4 upd_eq; reflexivity. }
    (* ===== acquire(&u->tx_lock) ===== *)
    iDestruct (cpu_own_transport CID CIDq7 n eb p b ltac:(wp_next_chain)
                 with "Hcpu") as "Hcpu".
    iApply (Acquire.wp_acquire_sconf kt γl (uart_lock_name i) <{ tx_res γd }> G2e n eb p (K - 8)%nat b lks
              Hn Hav Hfresh with "Hcg Hcpu Ht Hpc [Hlk]").
    all: try lkbelow.
    { iEval (rewrite HG2ea0). iExact "Hlk". }
    iIntros (CIDacq Hsacq ms macq) "%Hmsf Hcg Hpc %Hcs_acq Hlocked HR _ Hcpu Hpay".
    assert (Hret2e : ret_pc (G2e !!! Regidx (mword_of_int 1 : mword 5)) = mword_of_int (KernelSyms.uartputc_sync + 0x32))
      by (rewrite HG2era; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hret2e) in "Hpc".
    (* the transmitter comes out of the lock at some trace [l], and our
       persistent [bs] claim is pinned to it under [uart_inv i]. *)
    iDestruct "HR" as (l) "Hown".
    iApply fupd_wp.
    iMod (uart_tx_own_sent_sub_at i γd l bs ⊤ ltac:(solve_ndisj)
            with "Huinv Hown Hsubbs") as "[Hown %Hsl]".
    iModIntro.
    (* the callee-saved values, threaded through acquire *)
    assert (Hms1 : macq !!! Regidx (mword_of_int 9 : mword 5) = a_tx_lock_at i).
    { rewrite (callee_saved_lookup Hcs_acq (mword_of_int 9 : mword 5) ltac:(vm_compute; reflexivity)).
      exact HG2es1. }
    assert (Hms2 : macq !!! Regidx (mword_of_int 18 : mword 5) = (mword_of_int (4 * uart_index i) : mword 64)).
    { rewrite (callee_saved_lookup Hcs_acq (mword_of_int 18 : mword 5) ltac:(vm_compute; reflexivity)).
      exact HG2es2. }
    assert (Hms3 : macq !!! Regidx (mword_of_int 19 : mword 5) = (mword_of_int (uart_index i) : mword 64)).
    { rewrite (callee_saved_lookup Hcs_acq (mword_of_int 19 : mword 5) ltac:(vm_compute; reflexivity)).
      exact HG2es3. }
    assert (Hms4 : macq !!! Regidx (mword_of_int 20 : mword 5) = (mword_of_int KernelSyms.uarts : mword 64)).
    { rewrite (callee_saved_lookup Hcs_acq (mword_of_int 20 : mword 5) ltac:(vm_compute; reflexivity)).
      exact HG2es4. }
    assert (Hms5 : macq !!! Regidx (mword_of_int 21 : mword 5) = add_vec zero_reg a10).
    { rewrite (callee_saved_lookup Hcs_acq (mword_of_int 21 : mword 5) ltac:(vm_compute; reflexivity)).
      exact HG2es5. }
    (* ===== 0x32 .. 0x36: &uarts[uid], recomputed after the call ===== *)
    assert (Hpp34 : add_vec_int (mword_of_int (KernelSyms.uartputc_sync + 0x32) : mword 64) 2 = mword_of_int (KernelSyms.uartputc_sync + 0x34)) by (apply bv_eq; vm_compute; reflexivity).
    assert (Hpp36 : add_vec_int (mword_of_int (KernelSyms.uartputc_sync + 0x34) : mword 64) 2 = mword_of_int (KernelSyms.uartputc_sync + 0x36)) by (apply bv_eq; vm_compute; reflexivity).
    assert (Hpp38 : add_vec_int (mword_of_int (KernelSyms.uartputc_sync + 0x36) : mword 64) 2 = mword_of_int (KernelSyms.uartputc_sync + 0x38)) by (apply bv_eq; vm_compute; reflexivity).
    (* +0x32 c.add s2,s2,s3 *)
    iApply (wp_cadd_s_sconf (mword_of_int (KernelSyms.uartputc_sync + 0x32)) (mword_of_int 18) (mword_of_int 19)
              macq (trap_res b + (K - 8))%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (upi_32 with "Ht"). }
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    iEval (rgne) in "Hcg". iEval (rgne) in "Hcg".
    iEval (rewrite Hms2 Hms3 (ui_add5 i)) in "Hcg".
    set (M32 := <[Regidx (mword_of_int 18 : mword 5) := regval_into_reg (mword_of_int (5 * uart_index i) : mword 64)]> macq).
    assert (HM32s2 : M32 !!! Regidx (mword_of_int 18 : mword 5) = (mword_of_int (5 * uart_index i) : mword 64))
      by (rewrite /M32 upd_eq; reflexivity).
    assert (HM32s4 : M32 !!! Regidx (mword_of_int 20 : mword 5) = (mword_of_int KernelSyms.uarts : mword 64))
      by (rewrite /M32 upd_ne; [exact Hms4 | vm_compute; discriminate]).
    iEval (rewrite Hpp34) in "Hpc".
    (* +0x34 c.slli s2,s2,3 *)
    iApply (wp_cslli_s_sconf (mword_of_int (KernelSyms.uartputc_sync + 0x34)) (Regidx (mword_of_int 18)) (mword_of_int 18) (mword_of_int 3 : mword 6)
              M32 (trap_res b + (K - 8))%nat false eq_refl ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (upi_34 with "Ht"). }
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    iEval (rgne) in "Hcg".
    iEval (rewrite HM32s2 (ui_slli3 i)) in "Hcg".
    set (M34 := <[Regidx (mword_of_int 18 : mword 5) := regval_into_reg (mword_of_int (uart_stride * uart_index i) : mword 64)]> M32).
    assert (HM34s2 : M34 !!! Regidx (mword_of_int 18 : mword 5) = (mword_of_int (uart_stride * uart_index i) : mword 64))
      by (rewrite /M34 upd_eq; reflexivity).
    assert (HM34s4 : M34 !!! Regidx (mword_of_int 20 : mword 5) = (mword_of_int KernelSyms.uarts : mword 64))
      by (rewrite /M34 upd_ne; [exact HM32s4 | vm_compute; discriminate]).
    iEval (rewrite Hpp36) in "Hpc".
    (* +0x36 c.add s4,s4,s2 -> &uarts[uid] *)
    iApply (wp_cadd_s_sconf (mword_of_int (KernelSyms.uartputc_sync + 0x36)) (mword_of_int 20) (mword_of_int 18)
              M34 (trap_res b + (K - 8))%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (upi_36 with "Ht"). }
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    iEval (rgne) in "Hcg". iEval (rgne) in "Hcg".
    iEval (rewrite HM34s4 HM34s2 (ui_elt i)) in "Hcg".
    set (M36 := <[Regidx (mword_of_int 20 : mword 5) := regval_into_reg (mword_of_int (uart_f_base i) : mword 64)]> M34).
    assert (HM36s4 : M36 !!! Regidx (mword_of_int 20 : mword 5) = (mword_of_int (uart_f_base i) : mword 64))
      by (rewrite /M36 upd_eq; reflexivity).
    assert (HM36s5 : M36 !!! Regidx (mword_of_int 21 : mword 5) = add_vec zero_reg a10).
    { rewrite /M36 upd_ne; [| vm_compute; discriminate].
      rewrite /M34 upd_ne; [| vm_compute; discriminate].
      rewrite /M32 upd_ne; [exact Hms5 | vm_compute; discriminate]. }
    assert (HM36s1 : M36 !!! Regidx (mword_of_int 9 : mword 5) = a_tx_lock_at i).
    { rewrite /M36 upd_ne; [| vm_compute; discriminate].
      rewrite /M34 upd_ne; [| vm_compute; discriminate].
      rewrite /M32 upd_ne; [exact Hms1 | vm_compute; discriminate]. }
    iEval (rewrite Hpp38) in "Hpc".
    (* ===== 0x38 -> 0x52: the device core, inside the critical section ===== *)
    assert (Hsbm : (autocast (T := mword)
                      (subrange_vec_dec (and_vec (M36 !!! Regidx (mword_of_int 21))
                         (sign_extend' 64 (mword_of_int 255 : mword 12))) 7 0) : mword 8) = sb).
    { unfold sb. rewrite HM36s5. reflexivity. }
    iApply (wp_uartputc_devcore_sconf (CID0:=CIDacq) i γd M36 (trap_res b + (K - 8))%nat l false p
              HM36s4 with "Hcg Ht Hpc Huinv Hbw Hown Hoff").
    iApply wp_next_off_intro.
    iIntros (bt) "Hcg Hpc Hown Hsent".
    iEval (rewrite Hsbm) in "Hown". iEval (rewrite Hsbm) in "Hsent".
    (* the caller's sublist claim, cashed once and for all *)
    iAssert (uart_sent_sub γd (bs ++ [sb])) as "#Hsubout".
    { iApply (uart_sent_sub_snoc γd bs l sb Hsl with "Hsent"). }
    (* ===== 0x52 c.mv a0,s1 ; 0x54 jal release ===== *)
    assert (Hf5s1 : ppc_f5' i M36 bt !!! Regidx (mword_of_int 9 : mword 5) = a_tx_lock_at i).
    { rewrite (ppc_f5'_cs i M36 bt (mword_of_int 9 : mword 5)
                 ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)).
      exact HM36s1. }
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.uartputc_sync + 0x52)) (mword_of_int 10 : mword 5) (mword_of_int 9 : mword 5)
              (ppc_f5' i M36 bt) (trap_res b + (K - 8))%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (upi_52 with "Ht"). }
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    iEval (rgne) in "Hcg".
    iEval (rewrite Hf5s1 (ui_zadd_lock i)) in "Hcg".
    set (H52 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg (a_tx_lock_at i)]> (ppc_f5' i M36 bt)).
    assert (Hpp54 : add_vec_int (mword_of_int (KernelSyms.uartputc_sync + 0x52) : mword 64) 2 = mword_of_int (KernelSyms.uartputc_sync + 0x54)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp54) in "Hpc".
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.uartputc_sync + 0x54)) (mword_of_int 1 : mword 5) (mword_of_int 736 : mword 21)
              H52 (trap_res b + (K - 8))%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (upi_54 with "Ht"). }
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    set (H54 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.uartputc_sync + 0x54) : mword 64) 4)]> H52).
    assert (Hjrel : add_vec (mword_of_int (KernelSyms.uartputc_sync + 0x54) : mword 64) (sign_extend' 64 (mword_of_int 736 : mword 21)) = mword_of_int KernelSyms.release)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hjrel) in "Hpc".
    assert (HH54ra : H54 !!! Regidx (mword_of_int 1 : mword 5)
                     = regval_into_reg (add_vec_int (mword_of_int (KernelSyms.uartputc_sync + 0x54) : mword 64) 4))
      by (rewrite /H54 upd_eq; reflexivity).
    assert (HH54a0 : H54 !!! Regidx (mword_of_int 10 : mword 5) = a_tx_lock_at i).
    { rewrite /H54 upd_ne; [| vm_compute; discriminate].
      rewrite /H52 upd_eq; reflexivity. }
    assert (Hlka : add_vec (H54 !!! Regidx (mword_of_int 10 : mword 5)) (sign_extend' 64 (mword_of_int 0 : mword 12)) = a_tx_lock_at i).
    { rewrite HH54a0. apply ui_imm0. }
    (* ===== release(&u->tx_lock) ===== *)
    iEval (rewrite -Hbeq) in "Hcg".
    iApply (Release.wp_release_sconf kt γl (a_tx_lock_at i) (uart_lock_name i) <{ tx_res γd }> H54 n eb p (K - 8)%nat
              ({[uart_lock_name i]} ∪ lks)
              Hlka Hav with "Hcg Ht Hpc Hlk Hlocked [Hown] Hcpu Hpay").
    { iApply (tx_res_intro γd (l ++ [sb]) with "Hown"). }
    iIntros (CIDrel Hsrel mrel) "Hcg Hpc %Hcs_rel Hcpu".
    rewrite Hbeq in Hsrel.
    iEval (rewrite Hbeq) in "Hcg". iEval (rewrite Hbeq) in "Hcpu".
    pose proof (locks_below_not_elem lks (uart_lock_name i) Hfresh) as Hnotin.
    assert (Hsetback : ({[uart_lock_name i]} ∪ lks) ∖ {[uart_lock_name i]} = lks)
      by (apply locks_add_del_below; lkbelow).
    iEval (rewrite Hsetback) in "Hcpu".
    assert (Hret54 : ret_pc (H54 !!! Regidx (mword_of_int 1 : mword 5)) = mword_of_int (KernelSyms.uartputc_sync + 0x58))
      by (rewrite HH54ra; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hret54) in "Hpc".
    (* ===== EPILOGUE (0x58 -> 0x68) ===== *)
    assert (Hmrelsp : mrel !!! Regidx csp_rs1 = spr).
    { rewrite (callee_saved_lookup Hcs_rel csp_rs1 ltac:(vm_compute; reflexivity)).
      rewrite /H54 upd_ne; [| vm_compute; discriminate].
      rewrite /H52 upd_ne; [| vm_compute; discriminate].
      rewrite ppc_f5'_cs;
        [| vm_compute; discriminate | vm_compute; discriminate | vm_compute; discriminate ].
      rewrite /M36 upd_ne; [| vm_compute; discriminate].
      rewrite /M34 upd_ne; [| vm_compute; discriminate].
      rewrite /M32 upd_ne; [| vm_compute; discriminate].
      rewrite (callee_saved_lookup Hcs_acq csp_rs1 ltac:(vm_compute; reflexivity)).
      rewrite /G2e upd_ne; [| vm_compute; discriminate].
      rewrite /G2c upd_ne; [| vm_compute; discriminate].
      rewrite /G2a upd_ne; [| vm_compute; discriminate].
      rewrite /G28 upd_ne; [| vm_compute; discriminate].
      rewrite /G26 upd_ne; [| vm_compute; discriminate].
      rewrite /G22 upd_ne; [| vm_compute; discriminate].
      rewrite /G1e upd_ne; [| vm_compute; discriminate].
      rewrite /G1a upd_ne; [| vm_compute; discriminate].
      rewrite /G16 upd_ne; [| vm_compute; discriminate].
      rewrite /R4 upd_ne; [| vm_compute; discriminate].
      rewrite /R3 upd_ne; [| vm_compute; discriminate].
      rewrite /R2 upd_ne; [| vm_compute; discriminate].
      exact HspR1. }
    iEval (rewrite HspR1) in "Hr1". iEval (rewrite HspR1) in "Hr2".
    iEval (rewrite HspR1) in "Hr3". iEval (rewrite HspR1) in "Hr4".
    iEval (rewrite HspR1) in "Hr5". iEval (rewrite HspR1) in "Hr6".
    iEval (rewrite HspR1) in "Hr7". iEval (rewrite HspR1) in "Hr8".
    (* +0x58 .. +0x64: the seven reloads *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.uartputc_sync + 0x58)) (mword_of_int 7 : mword 6) (mword_of_int 1 : mword 5)
              mrel (K - 8)%nat (R1 !!! Regidx (mword_of_int 1 : mword 5)) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] [Hr1]").
    { iApply (upi_58 with "Ht"). }
    { iEval (rewrite Hmrelsp). iExact "Hr1". }
    iIntros (CIDe1 Hse1) "Hcg Hpc Hr1".
    iEval (rewrite Hmrelsp) in "Hr1".
    set (Q58 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (R1 !!! Regidx (mword_of_int 1 : mword 5))]> mrel).
    assert (HspQ58 : Q58 !!! Regidx csp_rs1 = spr) by (rewrite /Q58 upd_ne; [ exact Hmrelsp | vm_compute; discriminate ]).
    assert (Hpp5a : add_vec_int (mword_of_int (KernelSyms.uartputc_sync + 0x58) : mword 64) 2 = mword_of_int (KernelSyms.uartputc_sync + 0x5a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp5a) in "Hpc".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.uartputc_sync + 0x5a)) (mword_of_int 6 : mword 6) (mword_of_int 8 : mword 5)
              Q58 (K - 8)%nat (R1 !!! Regidx (mword_of_int 8 : mword 5)) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] [Hr2]").
    { iApply (upi_5a with "Ht"). }
    { iEval (rewrite HspQ58). iExact "Hr2". }
    iIntros (CIDe2 Hse2) "Hcg Hpc Hr2".
    iEval (rewrite HspQ58) in "Hr2".
    set (Q5a := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg (R1 !!! Regidx (mword_of_int 8 : mword 5))]> Q58).
    assert (HspQ5a : Q5a !!! Regidx csp_rs1 = spr) by (rewrite /Q5a upd_ne; [ exact HspQ58 | vm_compute; discriminate ]).
    assert (Hpp5c : add_vec_int (mword_of_int (KernelSyms.uartputc_sync + 0x5a) : mword 64) 2 = mword_of_int (KernelSyms.uartputc_sync + 0x5c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp5c) in "Hpc".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.uartputc_sync + 0x5c)) (mword_of_int 5 : mword 6) (mword_of_int 9 : mword 5)
              Q5a (K - 8)%nat (R1 !!! Regidx (mword_of_int 9 : mword 5)) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] [Hr3]").
    { iApply (upi_5c with "Ht"). }
    { iEval (rewrite HspQ5a). iExact "Hr3". }
    iIntros (CIDe3 Hse3) "Hcg Hpc Hr3".
    iEval (rewrite HspQ5a) in "Hr3".
    set (Q5c := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (R1 !!! Regidx (mword_of_int 9 : mword 5))]> Q5a).
    assert (HspQ5c : Q5c !!! Regidx csp_rs1 = spr) by (rewrite /Q5c upd_ne; [ exact HspQ5a | vm_compute; discriminate ]).
    assert (Hpp5e : add_vec_int (mword_of_int (KernelSyms.uartputc_sync + 0x5c) : mword 64) 2 = mword_of_int (KernelSyms.uartputc_sync + 0x5e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp5e) in "Hpc".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.uartputc_sync + 0x5e)) (mword_of_int 4 : mword 6) (mword_of_int 18 : mword 5)
              Q5c (K - 8)%nat (R1 !!! Regidx (mword_of_int 18 : mword 5)) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] [Hr4]").
    { iApply (upi_5e with "Ht"). }
    { iEval (rewrite HspQ5c). iExact "Hr4". }
    iIntros (CIDe4 Hse4) "Hcg Hpc Hr4".
    iEval (rewrite HspQ5c) in "Hr4".
    set (Q5e := <[Regidx (mword_of_int 18 : mword 5) := regval_into_reg (R1 !!! Regidx (mword_of_int 18 : mword 5))]> Q5c).
    assert (HspQ5e : Q5e !!! Regidx csp_rs1 = spr) by (rewrite /Q5e upd_ne; [ exact HspQ5c | vm_compute; discriminate ]).
    assert (Hpp60 : add_vec_int (mword_of_int (KernelSyms.uartputc_sync + 0x5e) : mword 64) 2 = mword_of_int (KernelSyms.uartputc_sync + 0x60)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp60) in "Hpc".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.uartputc_sync + 0x60)) (mword_of_int 3 : mword 6) (mword_of_int 19 : mword 5)
              Q5e (K - 8)%nat (R1 !!! Regidx (mword_of_int 19 : mword 5)) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] [Hr5]").
    { iApply (upi_60 with "Ht"). }
    { iEval (rewrite HspQ5e). iExact "Hr5". }
    iIntros (CIDe5 Hse5) "Hcg Hpc Hr5".
    iEval (rewrite HspQ5e) in "Hr5".
    set (Q60 := <[Regidx (mword_of_int 19 : mword 5) := regval_into_reg (R1 !!! Regidx (mword_of_int 19 : mword 5))]> Q5e).
    assert (HspQ60 : Q60 !!! Regidx csp_rs1 = spr) by (rewrite /Q60 upd_ne; [ exact HspQ5e | vm_compute; discriminate ]).
    assert (Hpp62 : add_vec_int (mword_of_int (KernelSyms.uartputc_sync + 0x60) : mword 64) 2 = mword_of_int (KernelSyms.uartputc_sync + 0x62)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp62) in "Hpc".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.uartputc_sync + 0x62)) (mword_of_int 2 : mword 6) (mword_of_int 20 : mword 5)
              Q60 (K - 8)%nat (R1 !!! Regidx (mword_of_int 20 : mword 5)) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] [Hr6]").
    { iApply (upi_62 with "Ht"). }
    { iEval (rewrite HspQ60). iExact "Hr6". }
    iIntros (CIDe6 Hse6) "Hcg Hpc Hr6".
    iEval (rewrite HspQ60) in "Hr6".
    set (Q62 := <[Regidx (mword_of_int 20 : mword 5) := regval_into_reg (R1 !!! Regidx (mword_of_int 20 : mword 5))]> Q60).
    assert (HspQ62 : Q62 !!! Regidx csp_rs1 = spr) by (rewrite /Q62 upd_ne; [ exact HspQ60 | vm_compute; discriminate ]).
    assert (Hpp64 : add_vec_int (mword_of_int (KernelSyms.uartputc_sync + 0x62) : mword 64) 2 = mword_of_int (KernelSyms.uartputc_sync + 0x64)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp64) in "Hpc".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.uartputc_sync + 0x64)) (mword_of_int 1 : mword 6) (mword_of_int 21 : mword 5)
              Q62 (K - 8)%nat (R1 !!! Regidx (mword_of_int 21 : mword 5)) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] [Hr7]").
    { iApply (upi_64 with "Ht"). }
    { iEval (rewrite HspQ62). iExact "Hr7". }
    iIntros (CIDe7 Hse7) "Hcg Hpc Hr7".
    iEval (rewrite HspQ62) in "Hr7".
    set (Q64 := <[Regidx (mword_of_int 21 : mword 5) := regval_into_reg (R1 !!! Regidx (mword_of_int 21 : mword 5))]> Q62).
    assert (HspQ64 : Q64 !!! Regidx csp_rs1 = spr) by (rewrite /Q64 upd_ne; [ exact HspQ62 | vm_compute; discriminate ]).
    assert (Hpp66 : add_vec_int (mword_of_int (KernelSyms.uartputc_sync + 0x64) : mword 64) 2 = mword_of_int (KernelSyms.uartputc_sync + 0x66)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp66) in "Hpc".
    (* +0x66 c.addi16sp sp,64 -- pop 8 *)
    set (Q66 := <[Regidx csp_rs1 := regval_into_reg (add_vec (Q64 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 4 : mword 6))))]> Q64).
    assert (Hwval : add_vec (Q64 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 4 : mword 6))) = sp0).
    { rewrite HspQ64. unfold spr, sp0. apply frame_cancel_64. }
    assert (Hpop : Q64 !!! Regidx csp_rs1
                   = pa_stk (add_vec (Q64 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 4 : mword 6)))) 8).
    { rewrite Hwval HspQ64. unfold spr, sp0, pa_stk, add_vec_int. apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    iAssert (stack_own (KTR := kt) (add_vec (Q64 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 4 : mword 6)))) 8)
      with "[Hr1 Hr2 Hr3 Hr4 Hr5 Hr6 Hr7 Hr8]" as "Hframe".
    { rewrite Hwval. rewrite (stack_own_slots (KTR := kt)). cbn [seq].
      iSplitL "Hr1"; [iEval (rewrite -Hb1 HspR1); iExists _; iExact "Hr1"|].
      iSplitL "Hr2"; [iEval (rewrite -Hb2 HspR1); iExists _; iExact "Hr2"|].
      iSplitL "Hr3"; [iEval (rewrite -Hb3 HspR1); iExists _; iExact "Hr3"|].
      iSplitL "Hr4"; [iEval (rewrite -Hb4 HspR1); iExists _; iExact "Hr4"|].
      iSplitL "Hr5"; [iEval (rewrite -Hb5 HspR1); iExists _; iExact "Hr5"|].
      iSplitL "Hr6"; [iEval (rewrite -Hb6 HspR1); iExists _; iExact "Hr6"|].
      iSplitL "Hr7"; [iEval (rewrite -Hb7 HspR1); iExists _; iExact "Hr7"|].
      iSplitL "Hr8"; [iEval (rewrite -Hb8 HspR1); iExists _; iExact "Hr8"|].
      done. }
    iApply (wp_caddi16sp_pop_s_sconf (mword_of_int (KernelSyms.uartputc_sync + 0x66)) (mword_of_int 4 : mword 6) Q64
              (K - 8)%nat 8 b Hpop
              with "Hcg Hpc [] Hframe").
    { iApply (upi_66 with "Ht"). }
    iIntros (CIDe8 Hse8) "Hcg Hpc".
    assert (HK8' : ((K - 8) + 8)%nat = K) by lia.
    iEval (rewrite HK8') in "Hcg".
    assert (Hpp68 : add_vec_int (mword_of_int (KernelSyms.uartputc_sync + 0x66) : mword 64) 2 = mword_of_int (KernelSyms.uartputc_sync + 0x68)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp68) in "Hpc".
    (* +0x68 c.ret *)
    assert (HQ66ra : Q66 !!! Regidx (mword_of_int 1 : mword 5) = ra0).
    { rewrite /Q66 upd_ne; [| vm_compute; discriminate].
      rewrite /Q64 upd_ne; [| vm_compute; discriminate].
      rewrite /Q62 upd_ne; [| vm_compute; discriminate].
      rewrite /Q60 upd_ne; [| vm_compute; discriminate].
      rewrite /Q5e upd_ne; [| vm_compute; discriminate].
      rewrite /Q5c upd_ne; [| vm_compute; discriminate].
      rewrite /Q5a upd_ne; [| vm_compute; discriminate].
      rewrite /Q58 upd_eq.
      rewrite /R1 upd_ne; [reflexivity | vm_compute; discriminate]. }
    iApply (wp_cret_s_sconf (mword_of_int (KernelSyms.uartputc_sync + 0x68)) (mword_of_int 1 : mword 5) Q66 K b
              ltac:(vm_compute; discriminate)
              with "Hcg Hpc []").
    { iApply (upi_68 with "Ht"). }
    iIntros (CIDe9 Hse9) "Hcg Hpc".
    iEval (rgne) in "Hpc".
    assert (Hretf : ret_pc (Q66 !!! Regidx (mword_of_int 1 : mword 5)) = ret_tgt)
      by (rewrite HQ66ra; reflexivity).
    iEval (rewrite Hretf) in "Hpc".
    iDestruct (cpu_own_transport CIDrel CIDe9 n eb p b ltac:(wp_next_chain)
                 with "Hcpu") as "Hcpu".
    iSpecialize ("Hcont" $! CIDe9 with "[%]"); [wp_next_chain|].
    iApply ("Hcont" $! Q66 with "Hcg Hcpu Hpc [%] Hsubout").
    split; [| exact HQ66ra].
    (* threading: a register untouched by the body threads m0 -> Q66 *)
    assert (Hthread : forall c : mword 5, is_cs_idx c = true ->
              c <> mword_of_int 1 -> c <> csp_rs1 -> c <> mword_of_int 8 -> c <> mword_of_int 9 ->
              c <> mword_of_int 18 -> c <> mword_of_int 19 -> c <> mword_of_int 20 -> c <> mword_of_int 21 ->
              Q66 !!! Regidx c = m0 !!! Regidx c).
    { intros c Hcs N1 N2 N8 N9 N18 N19 N20 N21.
      pose proof (is_cs_idx_true_neq (mword_of_int 10 : mword 5) c ltac:(vm_compute; reflexivity) Hcs) as N10.
      pose proof (is_cs_idx_true_neq (mword_of_int 13 : mword 5) c ltac:(vm_compute; reflexivity) Hcs) as N13.
      pose proof (is_cs_idx_true_neq (mword_of_int 14 : mword 5) c ltac:(vm_compute; reflexivity) Hcs) as N14.
      pose proof (is_cs_idx_true_neq (mword_of_int 15 : mword 5) c ltac:(vm_compute; reflexivity) Hcs) as N15.
      rewrite /Q66 upd_ne; [| congruence].
      rewrite /Q64 upd_ne; [| congruence].
      rewrite /Q62 upd_ne; [| congruence].
      rewrite /Q60 upd_ne; [| congruence].
      rewrite /Q5e upd_ne; [| congruence].
      rewrite /Q5c upd_ne; [| congruence].
      rewrite /Q5a upd_ne; [| congruence].
      rewrite /Q58 upd_ne; [| congruence].
      rewrite (callee_saved_lookup Hcs_rel c Hcs).
      rewrite /H54 upd_ne; [| congruence].
      rewrite /H52 upd_ne; [| congruence].
      rewrite ppc_f5'_cs; [| congruence | congruence | congruence ].
      rewrite /M36 upd_ne; [| congruence].
      rewrite /M34 upd_ne; [| congruence].
      rewrite /M32 upd_ne; [| congruence].
      rewrite (callee_saved_lookup Hcs_acq c Hcs).
      rewrite /G2e upd_ne; [| congruence].
      rewrite /G2c upd_ne; [| congruence].
      rewrite /G2a upd_ne; [| congruence].
      rewrite /G28 upd_ne; [| congruence].
      rewrite /G26 upd_ne; [| congruence].
      rewrite /G22 upd_ne; [| congruence].
      rewrite /G1e upd_ne; [| congruence].
      rewrite /G1a upd_ne; [| congruence].
      rewrite /G16 upd_ne; [| congruence].
      rewrite /R4 upd_ne; [| congruence].
      rewrite /R3 upd_ne; [| congruence].
      rewrite /R2 upd_ne; [| congruence].
      rewrite /R1 upd_ne; [reflexivity | congruence]. }
    unfold callee_saved.
    split.
    { (* sp *)
      rewrite /Q66 upd_eq. rewrite HspQ64. unfold regval_into_reg, spr, sp0.
      apply frame_cancel_64. }
    split.
    { (* s0 *)
      rewrite /Q66 upd_ne; [| vm_compute; discriminate].
      rewrite /Q64 upd_ne; [| vm_compute; discriminate].
      rewrite /Q62 upd_ne; [| vm_compute; discriminate].
      rewrite /Q60 upd_ne; [| vm_compute; discriminate].
      rewrite /Q5e upd_ne; [| vm_compute; discriminate].
      rewrite /Q5c upd_ne; [| vm_compute; discriminate].
      rewrite /Q5a upd_eq.
      rewrite /R1 upd_ne; [reflexivity | vm_compute; discriminate]. }
    split.
    { (* s1 *)
      rewrite /Q66 upd_ne; [| vm_compute; discriminate].
      rewrite /Q64 upd_ne; [| vm_compute; discriminate].
      rewrite /Q62 upd_ne; [| vm_compute; discriminate].
      rewrite /Q60 upd_ne; [| vm_compute; discriminate].
      rewrite /Q5e upd_ne; [| vm_compute; discriminate].
      rewrite /Q5c upd_eq.
      rewrite /R1 upd_ne; [reflexivity | vm_compute; discriminate]. }
    split.
    { (* s2 *)
      rewrite /Q66 upd_ne; [| vm_compute; discriminate].
      rewrite /Q64 upd_ne; [| vm_compute; discriminate].
      rewrite /Q62 upd_ne; [| vm_compute; discriminate].
      rewrite /Q60 upd_ne; [| vm_compute; discriminate].
      rewrite /Q5e upd_eq.
      rewrite /R1 upd_ne; [reflexivity | vm_compute; discriminate]. }
    split.
    { (* s3 *)
      rewrite /Q66 upd_ne; [| vm_compute; discriminate].
      rewrite /Q64 upd_ne; [| vm_compute; discriminate].
      rewrite /Q62 upd_ne; [| vm_compute; discriminate].
      rewrite /Q60 upd_eq.
      rewrite /R1 upd_ne; [reflexivity | vm_compute; discriminate]. }
    split.
    { (* s4 *)
      rewrite /Q66 upd_ne; [| vm_compute; discriminate].
      rewrite /Q64 upd_ne; [| vm_compute; discriminate].
      rewrite /Q62 upd_eq.
      rewrite /R1 upd_ne; [reflexivity | vm_compute; discriminate]. }
    split.
    { (* s5 *)
      rewrite /Q66 upd_ne; [| vm_compute; discriminate].
      rewrite /Q64 upd_eq.
      rewrite /R1 upd_ne; [reflexivity | vm_compute; discriminate]. }
    repeat split; apply Hthread; vm_compute; first [reflexivity | discriminate].
  Qed.

End ProofUartPutc.

End UartPutcProof.
