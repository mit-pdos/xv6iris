(* ProofUartinit.v -- the whole-function WP for xv6's uartinit() over the
   SIE-agnostic sconf world.

   AT XV6_REV 163d39b uartinit() IS A WRAPPER AND NOTHING ELSE:

     void uartinit(void) {
       uartinitone(&uarts[0], "uart0");
       uartinitone(&uarts[1], "uart1");
     }

   Straight-line, 16-byte frame, TWO sub-calls to the same function: prologue,
   two (auipc/addi, auipc/addi, jal) triples, epilogue.  The seven MMIO writes
   and the [initlock] are [uartinitone]'s ([ProofUartinitone]); this file only
   pairs the two ports, and everything it has to say is about the two
   ARGUMENTS.

   THE ARGUMENTS, AND WHERE THEY COME FROM.

   - a0 is [&uarts[i]] -- the array is at [KernelSyms.uarts] and the stride is
     40, so the second call's [auipc a0,0xa / addi a0,a0,-1570] lands on
     [uarts + 0x28].  That IS [UartsFields.uart_elt Uart1], which is where the
     stride was read off in the first place.
   - a1 is the port's name literal.  The old single "uart" left `.rodata` with
     the old single [tx_lock]; there are two now, "uart0" at [etext + 0x30] and
     "uart1" at [etext + 0x38] ([SpecUartinit]'s [uart0_name_str] /
     [uart1_name_str], derived BY CONTENT).  Each is read out of the data image
     with [kernel_data_string_all], exactly as [cons.lock]'s name is in
     ProofConsoleinit.

   THE STACK BUDGET IS 2 + 4.  uartinit's own frame is two slots
   ([addi sp,sp,-16]); [SpecUartinitone] asks [(4 <= av)] of the avail it is
   handed (its own two plus [initlock]'s two), and what it is handed is
   [K - 2].

   THE TWO CALLS ARE THE SAME CONTRACT AT DIFFERENT PORTS, and the register
   file transits both through [callee_saved]: [sp] survives each call, the
   frame's [ra] and [s0] are on the stack, and the composition at the end is
   two [callee_saved_lookup]s stacked under the epilogue's own peel. *)
From Stdlib Require Import Eqdep_dec ZArith Lia List String.
From stdpp Require Import gmap list list_monad bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import excl.
From iris.base_logic.lib Require Import ghost_var gen_heap invariants own.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import RegFile.
Require Import WpMmodeLeafBase.
Require Import RiscvExtras.
Require Import StackOwn CalleeSaved.
Require Import KernelText KernelDataInv.
Require Import DevModel WpUart.
Require Import UartsFields.
Require Import WpSmodeIntr.
Require Import IntrDefs HartTp WpNext.
Require Import WpSconfAlu WpSconfMem WpSconfCtl.
Require Import WpLock.
Require Import UartTxInv.
Require Import SpecProcinit.
Require Import SpecUartinitone.
Require Import SpecUartPutc.
Require Import CodeUartinit.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SpecUartinit.
Require Import KernelRvcDecode.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Require Import TsoCtx.
Local Open Scope Z_scope.
Import Defs.

Module UartinitProof (Uartinitone : UARTINITONE) : UARTINIT.

Section ProofUartinit.
  Context `{!riscvGS Σ, !xv6G Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.

  Lemma wp_uartinit_sconf (γ0 γ1 : uart_names)
      (m : regfile) (K : nat) (l0 l1 : list (bv 8)) (d0 d1 : bool)
      (k0 k1 : nat) (hl0 hl1 : option (list mobs)) (p : mword 64)
    : wp_uartinit_sconf_body γ0 γ1 m K l0 l1 d0 d1 k0 k1 hl0 hl1 p.
  Proof.
    cbv beta delta [wp_uartinit_sconf_body].
    intros pcE ret_tgt HK.
    set (sp0 := m !!! Regidx csp_rs1).
    set (spr := add_vec sp0 (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6)))).
    iIntros "Hcg #Htext #Hkdata Hpc #Hb0 #Hr0 #Hb1 #Hr1
             #Huinv0 Htx0 #Hlb0 #Hsent0 Htok0 Hdlab0 Hraw0
             #Huinv1 Htx1 #Hlb1 #Hsent1 Htok1 Hdlab1 Hraw1 Hcont".
    (* ---- the two `.rodata` name literals, read out of the data image ---- *)
    assert (Hstr0 : forall j bt, cstring_bytes (uart_name Uart0) !! j = Some bt ->
                      KernelData.kernel_data !! (uart0_name_str + Z.of_nat j)%Z = Some bt).
    { intros j bt Hj.
      do 6 (destruct j as [|j];
            [vm_compute in Hj; injection Hj as <-; vm_compute; reflexivity |]);
      vm_compute in Hj; discriminate. }
    assert (Hstr1 : forall j bt, cstring_bytes (uart_name Uart1) !! j = Some bt ->
                      KernelData.kernel_data !! (uart1_name_str + Z.of_nat j)%Z = Some bt).
    { intros j bt Hj.
      do 6 (destruct j as [|j];
            [vm_compute in Hj; injection Hj as <-; vm_compute; reflexivity |]);
      vm_compute in Hj; discriminate. }
    iPoseProof (kernel_data_string_all uart0_name_str (uart_name Uart0)
                  (mword_of_int uart0_name_str) eq_refl
                  ltac:(vm_compute; discriminate)
                  ltac:(vm_compute; discriminate) Hstr0
                  with "Hkdata") as "#Hnm0".
    iPoseProof (kernel_data_string_all uart1_name_str (uart_name Uart1)
                  (mword_of_int uart1_name_str) eq_refl
                  ltac:(vm_compute; discriminate)
                  ltac:(vm_compute; discriminate) Hstr1
                  with "Hkdata") as "#Hnm1".
    (* pc-advance helper facts *)
    assert (Hspr2 : spr = pa_stk sp0 2).
    { unfold spr, pa_stk, add_vec_int. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb1s : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) = pa_stk sp0 1).
    { unfold spr, sp0, pa_stk, add_vec_int. rewrite pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb2s : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000"))) = pa_stk sp0 2).
    { unfold spr, sp0, pa_stk, add_vec_int. rewrite pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    (* ===== PROLOGUE 0x00..0x06: 2-slot frame + save ra/s0 ===== *)
    set (R1 := <[Regidx csp_rs1 := regval_into_reg (add_vec sp0 (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6))))]> m).
    assert (Hspm : m !!! Regidx csp_rs1 = sp0) by reflexivity.
    assert (Hpush : add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6))) = pa_stk (m !!! Regidx csp_rs1) 2).
    { unfold pa_stk, add_vec_int. apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    iApply (wp_caddi_sp_push_s_sconf pcE (mword_of_int 48 : mword 6) m K 2 false ltac:(lia) Hpush
              with "Hcg Hpc []").
    { iApply (uii_00 with "Htext"). }
    iApply wp_next_off_intro.
    iIntros "Hcg Hframe Hpc".
    iEval (rewrite Hspm) in "Hframe".
    change (<[Regidx csp_rs1 := regval_into_reg (add_vec sp0 (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6))))]> m) with R1.
    assert (HspR1 : R1 !!! Regidx csp_rs1 = spr) by (rewrite /R1 upd_eq; reflexivity).
    iEval (rewrite (stack_own_slots (KTR := KT0)); cbn [seq]) in "Hframe".
    iDestruct "Hframe" as "(S1 & S2 & _)".
    iDestruct "S1" as (vra0) "Hras". iDestruct "S2" as (vs00) "Hs0s".
    assert (Hpp02 : add_vec_int (pcE : mword 64) 2 = mword_of_int (KernelSyms.uartinit + 0x02)) by (unfold pcE; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp02) in "Hpc".
    (* +0x02 c.sdsp ra,8(sp) *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.uartinit + 0x02)) (mword_of_int 1 : mword 6) (mword_of_int 1 : mword 5)
              R1 (K - 2)%nat vra0 false with "Hcg Hpc [] [Hras]").
    { iApply (uii_02 with "Htext"). }
    { iEval (rewrite HspR1 Hb1s). iExact "Hras". }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc Hras".
    iEval (rewrite HspR1 Hb1s) in "Hras".
    assert (Hrav : forall (CID' : CpuId), rget (CID := CID') R1 (mword_of_int 1 : mword 5) = m !!! Regidx (mword_of_int 1 : mword 5))
      by (intros CID'; rgne; rewrite /R1 upd_ne; [reflexivity | vm_compute; discriminate]).
    iEval (rewrite Hrav) in "Hras".
    assert (Hpp04 : add_vec_int (mword_of_int (KernelSyms.uartinit + 0x02) : mword 64) 2 = mword_of_int (KernelSyms.uartinit + 0x04)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp04) in "Hpc".
    (* +0x04 c.sdsp s0,0(sp) *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.uartinit + 0x04)) (mword_of_int 0 : mword 6) (mword_of_int 8 : mword 5)
              R1 (K - 2)%nat vs00 false with "Hcg Hpc [] [Hs0s]").
    { iApply (uii_04 with "Htext"). }
    { iEval (rewrite HspR1 Hb2s). iExact "Hs0s". }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc Hs0s".
    iEval (rewrite HspR1 Hb2s) in "Hs0s".
    assert (Hs0v : forall (CID' : CpuId), rget (CID := CID') R1 (mword_of_int 8 : mword 5) = m !!! Regidx (mword_of_int 8 : mword 5))
      by (intros CID'; rgne; rewrite /R1 upd_ne; [reflexivity | vm_compute; discriminate]).
    iEval (rewrite Hs0v) in "Hs0s".
    assert (Hpp06 : add_vec_int (mword_of_int (KernelSyms.uartinit + 0x04) : mword 64) 2 = mword_of_int (KernelSyms.uartinit + 0x06)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp06) in "Hpc".
    (* +0x06 c.addi4spn s0,sp,16 *)
    iApply (wp_caddi4spn_s_sconf (mword_of_int (KernelSyms.uartinit + 0x06)) (Cregidx (mword_of_int 0)) (mword_of_int 4 : mword 8) (mword_of_int 8 : mword 5)
              R1 (K - 2)%nat false ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (uii_06 with "Htext"). }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    set (R2 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg (add_vec (R1 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 4 : mword 8))))]> R1).
    assert (HR2sp : R2 !!! Regidx csp_rs1 = spr)
      by (rewrite /R2 upd_ne; [exact HspR1 | vm_compute; discriminate]).
    assert (Hpp08 : add_vec_int (mword_of_int (KernelSyms.uartinit + 0x06) : mword 64) 2 = mword_of_int (KernelSyms.uartinit + 0x08)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp08) in "Hpc".
    (* ===== CALL 1: uartinitone(&uarts[0], "uart0") ===== *)
    (* +0x08 auipc a1,0x6 *)
    iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.uartinit + 0x08)) (mword_of_int 11 : mword 5) (mword_of_int 6 : mword 20)
              R2 (K - 2)%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (uii_08 with "Htext"). }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    set (A1 := <[Regidx (mword_of_int 11 : mword 5) := regval_into_reg (add_vec (mword_of_int (KernelSyms.uartinit + 0x08) : mword 64) (auipc_off (mword_of_int 6 : mword 20)))]> R2).
    assert (Hpp0c : add_vec_int (mword_of_int (KernelSyms.uartinit + 0x08) : mword 64) 4 = mword_of_int (KernelSyms.uartinit + 0x0c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0c) in "Hpc".
    (* +0x0c addi a1,a1,1858 : a1 := &"uart0" *)
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.uartinit + 0x0c)) (mword_of_int 11 : mword 5) (mword_of_int 11 : mword 5) (mword_of_int 1858 : mword 12)
              A1 (K - 2)%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (uii_0c with "Htext"). }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (A2 := <[Regidx (mword_of_int 11 : mword 5) := regval_into_reg (add_vec (A1 !!! Regidx (mword_of_int 11 : mword 5)) (sign_extend' 64 (mword_of_int 1858 : mword 12)))]> A1).
    assert (HA2a1 : A2 !!! Regidx (mword_of_int 11 : mword 5) = mword_of_int uart0_name_str).
    { rewrite /A2 upd_eq. rewrite /A1 upd_eq.
      apply bv_eq; vm_compute; reflexivity. }
    assert (Hpp10 : add_vec_int (mword_of_int (KernelSyms.uartinit + 0x0c) : mword 64) 4 = mword_of_int (KernelSyms.uartinit + 0x10)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp10) in "Hpc".
    (* +0x10 auipc a0,0xa *)
    iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.uartinit + 0x10)) (mword_of_int 10 : mword 5) (mword_of_int 10 : mword 20)
              A2 (K - 2)%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (uii_10 with "Htext"). }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    set (A3 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg (add_vec (mword_of_int (KernelSyms.uartinit + 0x10) : mword 64) (auipc_off (mword_of_int 10 : mword 20)))]> A2).
    assert (Hpp14 : add_vec_int (mword_of_int (KernelSyms.uartinit + 0x10) : mword 64) 4 = mword_of_int (KernelSyms.uartinit + 0x14)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp14) in "Hpc".
    (* +0x14 addi a0,a0,-1590 : a0 := &uarts[0] *)
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.uartinit + 0x14)) (mword_of_int 10 : mword 5) (mword_of_int 10 : mword 5) (mword_of_int 2506 : mword 12)
              A3 (K - 2)%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (uii_14 with "Htext"). }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (A4 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg (add_vec (A3 !!! Regidx (mword_of_int 10 : mword 5)) (sign_extend' 64 (mword_of_int 2506 : mword 12)))]> A3).
    assert (HA4a0 : A4 !!! Regidx (mword_of_int 10 : mword 5) = mword_of_int (uart_elt Uart0)).
    { rewrite /A4 upd_eq. rewrite /A3 upd_eq.
      apply bv_eq; vm_compute; reflexivity. }
    assert (HA4a1 : A4 !!! Regidx (mword_of_int 11 : mword 5) = mword_of_int uart0_name_str).
    { rewrite /A4 upd_ne; [| vm_compute; discriminate].
      rewrite /A3 upd_ne; [exact HA2a1 | vm_compute; discriminate]. }
    assert (HA4sp : A4 !!! Regidx csp_rs1 = spr).
    { rewrite /A4 upd_ne; [| vm_compute; discriminate].
      rewrite /A3 upd_ne; [| vm_compute; discriminate].
      rewrite /A2 upd_ne; [| vm_compute; discriminate].
      rewrite /A1 upd_ne; [exact HR2sp | vm_compute; discriminate]. }
    assert (Hpp18 : add_vec_int (mword_of_int (KernelSyms.uartinit + 0x14) : mword 64) 4 = mword_of_int (KernelSyms.uartinit + 0x18)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp18) in "Hpc".
    (* +0x18 jal ra,uartinitone *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.uartinit + 0x18)) (mword_of_int 1 : mword 5) (mword_of_int 2097048 : mword 21)
              A4 (K - 2)%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (uii_18 with "Htext"). }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    set (A5 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.uartinit + 0x18) : mword 64) 4)]> A4).
    assert (Htgt1 : add_vec (mword_of_int (KernelSyms.uartinit + 0x18) : mword 64) (sign_extend' 64 (mword_of_int 2097048 : mword 21)) = mword_of_int KernelSyms.uartinitone)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgt1) in "Hpc".
    assert (HA5a0 : A5 !!! Regidx (mword_of_int 10 : mword 5) = mword_of_int (uart_elt Uart0))
      by (rewrite /A5 upd_ne; [exact HA4a0 | vm_compute; discriminate]).
    assert (HA5a1 : A5 !!! Regidx (mword_of_int 11 : mword 5) = mword_of_int uart0_name_str)
      by (rewrite /A5 upd_ne; [exact HA4a1 | vm_compute; discriminate]).
    assert (HA5sp : A5 !!! Regidx csp_rs1 = spr)
      by (rewrite /A5 upd_ne; [exact HA4sp | vm_compute; discriminate]).
    assert (HA5ra : A5 !!! Regidx (mword_of_int 1 : mword 5) = mword_of_int (KernelSyms.uartinit + 0x1c))
      by (rewrite /A5 upd_eq; apply bv_eq; vm_compute; reflexivity).
    iApply (Uartinitone.wp_uartinitone_sconf Uart0 γ0 (uart_name Uart0)
              (mword_of_int uart0_name_str) A5 (K - 2)%nat l0 d0 k0 hl0 p
              ltac:(lia) HA5a0 HA5a1
              with "Hcg Htext Hpc Hb0 Hr0 Hnm0 Huinv0 Htx0 Hlb0 Hsent0 Htok0 Hdlab0 Hraw0").
    iIntros (M1) "Hcg Hpc %Hcs1 Htx0 _ Htok0' #Hdoff0 Hfresh0".
    assert (Hpcr1 : ret_pc (A5 !!! Regidx (mword_of_int 1 : mword 5)) = mword_of_int (KernelSyms.uartinit + 0x1c)).
    { rewrite HA5ra. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hpcr1) in "Hpc".
    assert (HM1sp : M1 !!! Regidx csp_rs1 = spr)
      by (rewrite (callee_saved_lookup Hcs1 csp_rs1 ltac:(vm_compute; reflexivity)); exact HA5sp).
    (* ===== CALL 2: uartinitone(&uarts[1], "uart1") ===== *)
    (* +0x1c auipc a1,0x6 *)
    iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.uartinit + 0x1c)) (mword_of_int 11 : mword 5) (mword_of_int 6 : mword 20)
              M1 (K - 2)%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (uii_1c with "Htext"). }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    set (B1 := <[Regidx (mword_of_int 11 : mword 5) := regval_into_reg (add_vec (mword_of_int (KernelSyms.uartinit + 0x1c) : mword 64) (auipc_off (mword_of_int 6 : mword 20)))]> M1).
    assert (Hpp20 : add_vec_int (mword_of_int (KernelSyms.uartinit + 0x1c) : mword 64) 4 = mword_of_int (KernelSyms.uartinit + 0x20)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp20) in "Hpc".
    (* +0x20 addi a1,a1,1846 : a1 := &"uart1" *)
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.uartinit + 0x20)) (mword_of_int 11 : mword 5) (mword_of_int 11 : mword 5) (mword_of_int 1846 : mword 12)
              B1 (K - 2)%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (uii_20 with "Htext"). }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (B2 := <[Regidx (mword_of_int 11 : mword 5) := regval_into_reg (add_vec (B1 !!! Regidx (mword_of_int 11 : mword 5)) (sign_extend' 64 (mword_of_int 1846 : mword 12)))]> B1).
    assert (HB2a1 : B2 !!! Regidx (mword_of_int 11 : mword 5) = mword_of_int uart1_name_str).
    { rewrite /B2 upd_eq. rewrite /B1 upd_eq.
      apply bv_eq; vm_compute; reflexivity. }
    assert (Hpp24 : add_vec_int (mword_of_int (KernelSyms.uartinit + 0x20) : mword 64) 4 = mword_of_int (KernelSyms.uartinit + 0x24)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp24) in "Hpc".
    (* +0x24 auipc a0,0xa *)
    iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.uartinit + 0x24)) (mword_of_int 10 : mword 5) (mword_of_int 10 : mword 20)
              B2 (K - 2)%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (uii_24 with "Htext"). }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    set (B3 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg (add_vec (mword_of_int (KernelSyms.uartinit + 0x24) : mword 64) (auipc_off (mword_of_int 10 : mword 20)))]> B2).
    assert (Hpp28 : add_vec_int (mword_of_int (KernelSyms.uartinit + 0x24) : mword 64) 4 = mword_of_int (KernelSyms.uartinit + 0x28)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp28) in "Hpc".
    (* +0x28 addi a0,a0,-1570 : a0 := &uarts[1] = uarts + 0x28 *)
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.uartinit + 0x28)) (mword_of_int 10 : mword 5) (mword_of_int 10 : mword 5) (mword_of_int 2526 : mword 12)
              B3 (K - 2)%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (uii_28 with "Htext"). }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (B4 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg (add_vec (B3 !!! Regidx (mword_of_int 10 : mword 5)) (sign_extend' 64 (mword_of_int 2526 : mword 12)))]> B3).
    assert (HB4a0 : B4 !!! Regidx (mword_of_int 10 : mword 5) = mword_of_int (uart_elt Uart1)).
    { rewrite /B4 upd_eq. rewrite /B3 upd_eq.
      apply bv_eq; vm_compute; reflexivity. }
    assert (HB4a1 : B4 !!! Regidx (mword_of_int 11 : mword 5) = mword_of_int uart1_name_str).
    { rewrite /B4 upd_ne; [| vm_compute; discriminate].
      rewrite /B3 upd_ne; [exact HB2a1 | vm_compute; discriminate]. }
    assert (HB4sp : B4 !!! Regidx csp_rs1 = spr).
    { rewrite /B4 upd_ne; [| vm_compute; discriminate].
      rewrite /B3 upd_ne; [| vm_compute; discriminate].
      rewrite /B2 upd_ne; [| vm_compute; discriminate].
      rewrite /B1 upd_ne; [exact HM1sp | vm_compute; discriminate]. }
    assert (Hpp2c : add_vec_int (mword_of_int (KernelSyms.uartinit + 0x28) : mword 64) 4 = mword_of_int (KernelSyms.uartinit + 0x2c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp2c) in "Hpc".
    (* +0x2c jal ra,uartinitone *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.uartinit + 0x2c)) (mword_of_int 1 : mword 5) (mword_of_int 2097028 : mword 21)
              B4 (K - 2)%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (uii_2c with "Htext"). }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    set (B5 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.uartinit + 0x2c) : mword 64) 4)]> B4).
    assert (Htgt2 : add_vec (mword_of_int (KernelSyms.uartinit + 0x2c) : mword 64) (sign_extend' 64 (mword_of_int 2097028 : mword 21)) = mword_of_int KernelSyms.uartinitone)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgt2) in "Hpc".
    assert (HB5a0 : B5 !!! Regidx (mword_of_int 10 : mword 5) = mword_of_int (uart_elt Uart1))
      by (rewrite /B5 upd_ne; [exact HB4a0 | vm_compute; discriminate]).
    assert (HB5a1 : B5 !!! Regidx (mword_of_int 11 : mword 5) = mword_of_int uart1_name_str)
      by (rewrite /B5 upd_ne; [exact HB4a1 | vm_compute; discriminate]).
    assert (HB5sp : B5 !!! Regidx csp_rs1 = spr)
      by (rewrite /B5 upd_ne; [exact HB4sp | vm_compute; discriminate]).
    assert (HB5ra : B5 !!! Regidx (mword_of_int 1 : mword 5) = mword_of_int (KernelSyms.uartinit + 0x30))
      by (rewrite /B5 upd_eq; apply bv_eq; vm_compute; reflexivity).
    iApply (Uartinitone.wp_uartinitone_sconf Uart1 γ1 (uart_name Uart1)
              (mword_of_int uart1_name_str) B5 (K - 2)%nat l1 d1 k1 hl1 p
              ltac:(lia) HB5a0 HB5a1
              with "Hcg Htext Hpc Hb1 Hr1 Hnm1 Huinv1 Htx1 Hlb1 Hsent1 Htok1 Hdlab1 Hraw1").
    iIntros (M2) "Hcg Hpc %Hcs2 Htx1 _ Htok1' #Hdoff1 Hfresh1".
    assert (Hpcr2 : ret_pc (B5 !!! Regidx (mword_of_int 1 : mword 5)) = mword_of_int (KernelSyms.uartinit + 0x30)).
    { rewrite HB5ra. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hpcr2) in "Hpc".
    assert (HM2sp : M2 !!! Regidx csp_rs1 = spr)
      by (rewrite (callee_saved_lookup Hcs2 csp_rs1 ltac:(vm_compute; reflexivity)); exact HB5sp).
    (* ===== EPILOGUE 0x30..0x36: restore ra/s0, pop frame, ret ===== *)
    (* +0x30 c.ldsp ra,8(sp) *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.uartinit + 0x30)) (mword_of_int 1 : mword 6) (mword_of_int 1 : mword 5)
              M2 (K - 2)%nat (m !!! Regidx (mword_of_int 1 : mword 5)) false (dqm:=DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] [Hras]").
    { iApply (uii_30 with "Htext"). }
    { iEval (rewrite -Hb1s -HM2sp) in "Hras". iExact "Hras". }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc Hras".
    iEval (rewrite HM2sp Hb1s) in "Hras".
    set (E1 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 1 : mword 5))]> M2).
    assert (HE1sp : E1 !!! Regidx csp_rs1 = spr) by (rewrite /E1 upd_ne; [exact HM2sp | vm_compute; discriminate]).
    assert (Hpp32 : add_vec_int (mword_of_int (KernelSyms.uartinit + 0x30) : mword 64) 2 = mword_of_int (KernelSyms.uartinit + 0x32)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp32) in "Hpc".
    (* +0x32 c.ldsp s0,0(sp) *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.uartinit + 0x32)) (mword_of_int 0 : mword 6) (mword_of_int 8 : mword 5)
              E1 (K - 2)%nat (m !!! Regidx (mword_of_int 8 : mword 5)) false (dqm:=DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] [Hs0s]").
    { iApply (uii_32 with "Htext"). }
    { iEval (rewrite -Hb2s -HE1sp) in "Hs0s". iExact "Hs0s". }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc Hs0s".
    iEval (rewrite HE1sp Hb2s) in "Hs0s".
    set (E2 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 8 : mword 5))]> E1).
    assert (HE2sp : E2 !!! Regidx csp_rs1 = spr) by (rewrite /E2 upd_ne; [exact HE1sp | vm_compute; discriminate]).
    assert (Hpp34 : add_vec_int (mword_of_int (KernelSyms.uartinit + 0x32) : mword 64) 2 = mword_of_int (KernelSyms.uartinit + 0x34)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp34) in "Hpc".
    (* +0x34 c.addi sp,16 : pop frame *)
    set (E3 := <[Regidx csp_rs1 := regval_into_reg (add_vec (E2 !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6))))]> E2).
    assert (HE3csp : E3 !!! Regidx csp_rs1 = sp0).
    { rewrite /E3 upd_eq. rewrite HE2sp. unfold regval_into_reg, spr, sp0.
      apply frame_cancel_16. }
    assert (Hwv : add_vec (E2 !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6))) = sp0).
    { rewrite -HE3csp /E3 upd_eq. reflexivity. }
    assert (Hpop : E2 !!! Regidx csp_rs1
                   = pa_stk (add_vec (E2 !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6)))) 2).
    { rewrite Hwv HE2sp. exact Hspr2. }
    iAssert (stack_own (KTR := KT0) sp0 2) with "[Hras Hs0s]" as "Hframe".
    { rewrite (stack_own_slots (KTR := KT0)). cbn [seq].
      iSplitL "Hras"; [iExists _; iExact "Hras"|].
      iSplitL "Hs0s"; [iExists _; iExact "Hs0s"|]. done. }
    iEval (rewrite -Hwv) in "Hframe".
    iApply (wp_caddi_sp_pop_s_sconf (mword_of_int (KernelSyms.uartinit + 0x34)) (mword_of_int 16 : mword 6) E2 (K - 2)%nat 2 false Hpop
              with "Hcg Hpc [] Hframe").
    { iApply (uii_34 with "Htext"). }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    assert (Hnk : ((K - 2) + 2)%nat = K) by lia.
    iEval (rewrite Hnk) in "Hcg".
    change (<[Regidx csp_rs1 := regval_into_reg (add_vec (E2 !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6))))]> E2) with E3.
    assert (Hpp36 : add_vec_int (mword_of_int (KernelSyms.uartinit + 0x34) : mword 64) 2 = mword_of_int (KernelSyms.uartinit + 0x36)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp36) in "Hpc".
    (* +0x36 c.ret *)
    assert (HE3ra : E3 !!! Regidx (mword_of_int 1 : mword 5) = m !!! Regidx (mword_of_int 1 : mword 5)).
    { rewrite /E3 upd_ne; [| vm_compute; discriminate].
      rewrite /E2 upd_ne; [| vm_compute; discriminate].
      rewrite /E1 upd_eq; reflexivity. }
    iApply (wp_cret_s_sconf (mword_of_int (KernelSyms.uartinit + 0x36)) (mword_of_int 1 : mword 5) E3 K false
              ltac:(vm_compute; discriminate)
              with "Hcg Hpc []").
    { iApply (uii_36 with "Htext"). }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    assert (Hretf : forall (CID' : CpuId), ret_pc (rget (CID := CID') E3 (mword_of_int 1 : mword 5)) = ret_tgt)
      by (intros CID'; rgne; rewrite HE3ra; reflexivity).
    iEval (rewrite Hretf) in "Hpc".
    (* callee_saved m E3: the epilogue's own peel, then the two calls'
       [callee_saved] facts in turn, then the argument-setup writes. *)
    assert (Hthread : forall c : mword 5, is_cs_idx c = true ->
              c <> mword_of_int 1 -> c <> csp_rs1 -> c <> mword_of_int 8 ->
              E3 !!! Regidx c = m !!! Regidx c).
    { intros c Hc N1 Nsp N8.
      pose proof (is_cs_idx_true_neq (mword_of_int 10 : mword 5) c ltac:(vm_compute; reflexivity) Hc) as Na0.
      pose proof (is_cs_idx_true_neq (mword_of_int 11 : mword 5) c ltac:(vm_compute; reflexivity) Hc) as Na1.
      rewrite /E3 upd_ne; [| congruence].
      rewrite /E2 upd_ne; [| congruence].
      rewrite /E1 upd_ne; [| congruence].
      rewrite (callee_saved_lookup Hcs2 c Hc).
      rewrite /B5 upd_ne; [| congruence].
      rewrite /B4 upd_ne; [| congruence].
      rewrite /B3 upd_ne; [| congruence].
      rewrite /B2 upd_ne; [| congruence].
      rewrite /B1 upd_ne; [| congruence].
      rewrite (callee_saved_lookup Hcs1 c Hc).
      rewrite /A5 upd_ne; [| congruence].
      rewrite /A4 upd_ne; [| congruence].
      rewrite /A3 upd_ne; [| congruence].
      rewrite /A2 upd_ne; [| congruence].
      rewrite /A1 upd_ne; [| congruence].
      rewrite /R2 upd_ne; [| congruence].
      rewrite /R1 upd_ne; [reflexivity | congruence]. }
    iApply ("Hcont" $! E3 with "Hcg Hpc [%] Htx0 Hsent0 Htok0' Hdoff0 Hfresh0
                                Htx1 Hsent1 Htok1' Hdoff1 Hfresh1").
    unfold callee_saved.
    split. { rewrite HE3csp. reflexivity. }
    split. { rewrite /E3 upd_ne; [| vm_compute; discriminate].
             rewrite /E2 upd_eq; reflexivity. }
    repeat split; apply Hthread; vm_compute; first [reflexivity | discriminate].
  Qed.

End ProofUartinit.
End UartinitProof.
