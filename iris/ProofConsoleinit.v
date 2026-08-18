(* ProofConsoleinit.v -- the whole-function WP for xv6's consoleinit() over the
   SIE-agnostic sconf world.

     void consoleinit(void) {
       initlock(&cons.lock, "cons");
       uartinit();
       devsw[CONSOLE].read  = consoleread;
       devsw[CONSOLE].write = consolewrite;
     }

   Straight-line, two calls, no branches.  Its first nine instructions are the
   thin-initlock-wrapper pattern (WpInitlockWrapper.v), but the wrapper owns the
   epilogue and returns, so consoleinit cannot instantiate it and runs the
   script itself -- over CONCRETE addresses, so every pc step and relocation is
   a [vm_compute] rather than the wrapper's symbolic [pc_step].

   The functor threads BOTH callees' [callee_saved] hops (initlock's, then
   uartinit's) into the one the caller sees; [Hthread] does that composition
   once and discharges eleven of the fourteen conjuncts.

   The device side is pure TRANSIT: consoleinit touches no MMIO itself, so
   [uart_inv], the transmitter token/receipt pair at [l], the carried
   [uart_out_lb], and the unfrozen DLAB half go straight into the uartinit
   call and its outputs (tokens at the same [l], plus the frozen
   [uart_dlab_off]) straight into consoleinit's own postcondition.

   SO IS THE TRANSMIT LOCK'S STORAGE.  uartinit ends with
   [initlock(&tx_lock, "uart")] -- tx_lock is a [struct spinlock] -- so
   [lk_raw a_tx_lock] rides in on the same path: introduced here, handed to
   the uartinit call untouched, and its [lk_fresh a_tx_lock "uart"] handed
   back out untouched.  consoleinit never names a field of it, and it costs
   the BUDGET nothing: uartinit needs 4 slots (its own 2 plus initlock's 2),
   so consoleinit's own 2-slot frame makes 6, which is what
   [cni_cap_bounds] splits. *)
From Stdlib Require Import Eqdep_dec ZArith Lia List.
From stdpp Require Import gmap list list_monad list_numbers bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import excl.
From iris.base_logic.lib Require Import gen_heap invariants ghost_var own.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.Base SailStdpp.Operators_mwords SailStdpp.Values SailStdpp.MachineWord.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import RiscvPtsto RiscvLang RiscvExtras.
Require Import SmodeCore RegFile WpMmodeLeafBase.
Require Import WpSconfAlu WpSconfMem WpSconfCtl.
Require Import WpLock.
Require Import CalleeSaved StackOwn.
Require Import KernelDataInv.
Require Import IntrDefs HartTp WpNext.
Require Import WpUart.
Require Import CodeConsoleinit.
Require Import SpecInitlock SpecUartinit SpecConsoleinit.
From Kernel Require KernelSyms.
Require Import KernelRvcDecode.
Local Open Scope Z_scope.
Import Defs.
Set Printing Depth 40.

(* clean-context (mword-free) nat bounds, so [lia] never sees a bv.
   2 for consoleinit's own frame; 4 for what is left over it, which is
   uartinit's demand (its own 2 + initlock's 2). *)
Lemma cni_cap_bounds (K : nat) : (6 <= K)%nat -> (2 <= K)%nat /\ (4 <= K - 2)%nat.
Proof. lia. Qed.

Lemma cni_nk (K : nat) : (2 <= K)%nat -> ((K - 2) + 2)%nat = K.
Proof. lia. Qed.

(* ===================================================================== *)
(* THE BODY: sealed and parameterized by the two callees' WP hypotheses.  *)
(* ===================================================================== *)
Section ConsoleinitBody.
  Context `{!riscvGS Σ}.
  Context `{!sieG Σ}.
  Context `{!uartGhostG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.


  (* [CID] is its OWN binder here, freshly instantiated at each call site --
     NOT the section's fixed [Context CID] -- matching the [Module Type]'s
     own per-use CID quantification (which is why the sealed functor at the
     bottom needs no such fix).  consoleinit itself is BOOT-ONLY (stated at
     the literal SIE index [false], no [wp_next] wrapper -- see
     SpecConsoleinit.v), so these sub-calls are always instantiated at
     [b := false] and the hart never actually moves; [wp_initlock] keeps its
     own generic [b] hypothesis (it is still callable at any index by other
     callers) but is applied here at [false]. *)
  Hypothesis wp_initlock :
    forall `{CID : CpuId} (m : regfile) (vlock : bv 32)
      (vname vcpu : bv 64) (s : string) (K : nat) (b : bool) (p : mword 64),
      wp_initlock_sconf_body KT0 m vlock vname vcpu s K b p.

  Hypothesis wp_uartinit :
    forall `{CID : CpuId} (γd : uart_names) (m : regfile) (K : nat)
      (l : list (bv 8)) (b0 : bool) (p : mword 64),
      wp_uartinit_sconf_body γd m K l b0 p.

  Ltac reg_neq :=
    lazymatch goal with
    | |- ?a <> ?b => tryif unify a b then fail else (vm_compute; discriminate)
    end.

  Lemma wp_consoleinit_sconf_gen (γd : uart_names)
      (m : regfile) (K : nat) (l : list (bv 8)) (b0 : bool)
      (vclock : bv 32) (vcname vccpu : bv 64)
      (dread0 dwrite0 : mword 64) (p : mword 64) :
    wp_consoleinit_sconf_body γd m K l b0 vclock vcname vccpu dread0 dwrite0 p.
  Proof.
    cbv beta delta [wp_consoleinit_sconf_body].
    intros pcE ret_tgt clk c_cname c_ccpu HK.
    pose proof (cni_cap_bounds K HK) as (Hc2 & HK4).
    iIntros "Hcg #Htext #Hkdata Hpc #Huinv Htx #Hlb #Hsent Hdlab Hclock Hcname Hccpu Hraw Hdr Hdw Hcont".
    (* the "cons" string literal (4 chars + NUL), read out of the data image *)
    pose (name := (mword_of_int cons_name_str : mword 64)).
    assert (Hcons : forall j bt, cstring_bytes "cons"%string !! j = Some bt ->
                    KernelData.kernel_data !! (cons_name_str + Z.of_nat j)%Z = Some bt).
    { intros j bt Hj.
      do 5 (destruct j as [|j];
            [vm_compute in Hj; injection Hj as <-; vm_compute; reflexivity |]);
      vm_compute in Hj; discriminate. }
    iPoseProof (kernel_data_string cons_name_str "cons"%string name eq_refl
                  ltac:(unfold text_end, cons_name_str; lia) Hcons
                  with "Hkdata") as "#Hstr".
    (* frame-cell address facts (2-slot frame: ra @ slot 1, s0 @ slot 2) *)
    assert (Hpush : add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6))) = pa_stk (m !!! Regidx csp_rs1) 2).
    { unfold pa_stk, add_vec_int. apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    assert (Hb1 : add_vec (add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6)))) (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) = pa_stk (m !!! Regidx csp_rs1) 1).
    { unfold pa_stk, add_vec_int. rewrite !pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb2 : add_vec (add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6)))) (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000"))) = pa_stk (m !!! Regidx csp_rs1) 2).
    { unfold pa_stk, add_vec_int. rewrite !pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    iPoseProof (cii_00 with "Htext") as "Hi00".
    iPoseProof (cii_02 with "Htext") as "Hi02".
    iPoseProof (cii_04 with "Htext") as "Hi04".
    iPoseProof (cii_06 with "Htext") as "Hi06".
    iPoseProof (cii_08 with "Htext") as "Hi08".
    iPoseProof (cii_0c with "Htext") as "Hi0c".
    iPoseProof (cii_10 with "Htext") as "Hi10".
    iPoseProof (cii_14 with "Htext") as "Hi14".
    iPoseProof (cii_18 with "Htext") as "Hi18".
    iPoseProof (cii_1c with "Htext") as "Hi1c".
    iPoseProof (cii_20 with "Htext") as "Hi20".
    iPoseProof (cii_24 with "Htext") as "Hi24".
    iPoseProof (cii_28 with "Htext") as "Hi28".
    iPoseProof (cii_2c with "Htext") as "Hi2c".
    iPoseProof (cii_30 with "Htext") as "Hi30".
    iPoseProof (cii_32 with "Htext") as "Hi32".
    iPoseProof (cii_36 with "Htext") as "Hi36".
    iPoseProof (cii_3a with "Htext") as "Hi3a".
    iPoseProof (cii_3c with "Htext") as "Hi3c".
    iPoseProof (cii_3e with "Htext") as "Hi3e".
    iPoseProof (cii_40 with "Htext") as "Hi40".
    iPoseProof (cii_42 with "Htext") as "Hi42".
    (* ===== PROLOGUE (0x00..0x06) ===== *)
    (* +0x00 addi sp,sp,-16 : 2-slot frame push *)
    iApply (wp_caddi_sp_push_s_sconf (mword_of_int KernelSyms.consoleinit) (mword_of_int 48 : mword 6) m K 2 false Hc2 Hpush
              with "Hcg Hpc Hi00").
    iApply wp_next_off_intro.
    iIntros "Hcg Hframe Hpc".
    set (W1 := <[Regidx csp_rs1 := regval_into_reg
        (add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6))))]> m).
    iEval (rewrite (stack_own_slots (KTR := KT0)); cbn [seq]) in "Hframe".
    iDestruct "Hframe" as "(S1 & S2 & _)".
    iDestruct "S1" as (v1) "Hc1". iDestruct "S2" as (v2) "Hc2".
    assert (HspW1 : W1 !!! Regidx csp_rs1 = add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6)))) by (rewrite /W1 upd_eq; reflexivity).
    assert (Hp02 : add_vec_int (mword_of_int KernelSyms.consoleinit : mword 64) 2 = mword_of_int (KernelSyms.consoleinit + 0x02)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp02) in "Hpc".
    (* +0x02 sd ra,8(sp) -> slot 1 *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.consoleinit + 0x02)) (mword_of_int 1 : mword 6) (mword_of_int 1 : mword 5)
              W1 (K - 2)%nat v1 false with "Hcg Hpc Hi02 [Hc1]").
    { iEval (rewrite HspW1 Hb1). iExact "Hc1". }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc Hc1".
    assert (HW1r1 : forall (CID' : CpuId), rget (CID := CID') W1 (mword_of_int 1 : mword 5) = m !!! Regidx (mword_of_int 1))
      by (intros CID'; rgne; rewrite /W1 upd_ne; [reflexivity | reg_neq]).
    iEval (rewrite HspW1 Hb1 HW1r1) in "Hc1".
    assert (Hp04 : add_vec_int (mword_of_int (KernelSyms.consoleinit + 0x02) : mword 64) 2 = mword_of_int (KernelSyms.consoleinit + 0x04)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp04) in "Hpc".
    (* +0x04 sd s0,0(sp) -> slot 2 *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.consoleinit + 0x04)) (mword_of_int 0 : mword 6) (mword_of_int 8 : mword 5)
              W1 (K - 2)%nat v2 false with "Hcg Hpc Hi04 [Hc2]").
    { iEval (rewrite HspW1 Hb2). iExact "Hc2". }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc Hc2".
    assert (HW1r8 : forall (CID' : CpuId), rget (CID := CID') W1 (mword_of_int 8 : mword 5) = m !!! Regidx (mword_of_int 8))
      by (intros CID'; rgne; rewrite /W1 upd_ne; [reflexivity | reg_neq]).
    iEval (rewrite HspW1 Hb2 HW1r8) in "Hc2".
    assert (Hp06 : add_vec_int (mword_of_int (KernelSyms.consoleinit + 0x04) : mword 64) 2 = mword_of_int (KernelSyms.consoleinit + 0x06)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp06) in "Hpc".
    (* +0x06 addi s0,sp,16 (value unused; s0 reloaded at the epilogue) *)
    iApply (wp_caddi4spn_s_sconf (mword_of_int (KernelSyms.consoleinit + 0x06)) (Cregidx (mword_of_int 0)) (mword_of_int 4 : mword 8) (mword_of_int 8 : mword 5)
              W1 (K - 2)%nat false ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi06").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    set (W2 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg (add_vec (W1 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 4 : mword 8))))]> W1).
    assert (Hp08 : add_vec_int (mword_of_int (KernelSyms.consoleinit + 0x06) : mword 64) 2 = mword_of_int (KernelSyms.consoleinit + 0x08)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp08) in "Hpc".
    (* ===== initlock(&cons.lock, "cons") (0x08..0x18) ===== *)
    (* +0x08 auipc a1,0x7 *)
    iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.consoleinit + 0x08)) (mword_of_int 11 : mword 5) (mword_of_int 7 : mword 20)
              W2 (K - 2)%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi08").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    set (W3 := <[Regidx (mword_of_int 11 : mword 5) := regval_into_reg (add_vec (mword_of_int (KernelSyms.consoleinit + 0x08) : mword 64) (auipc_off (mword_of_int 7 : mword 20)))]> W2).
    assert (Hp0c : add_vec_int (mword_of_int (KernelSyms.consoleinit + 0x08) : mword 64) 4 = mword_of_int (KernelSyms.consoleinit + 0x0c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp0c) in "Hpc".
    (* +0x0c addi a1,a1,-1066 : a1 := &"cons" *)
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.consoleinit + 0x0c)) (mword_of_int 11 : mword 5) (mword_of_int 11 : mword 5) (mword_of_int 3024 : mword 12)
              W3 (K - 2)%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi0c").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    set (W4 := <[Regidx (mword_of_int 11 : mword 5) := regval_into_reg (add_vec (rget W3 (mword_of_int 11 : mword 5)) (sign_extend' 64 (mword_of_int 3024 : mword 12)))]> W3).
    assert (HW4a1 : W4 !!! Regidx (mword_of_int 11 : mword 5) = name).
    { rewrite /W4 upd_eq. rgne. rewrite /W3 upd_eq /name. apply bv_eq; vm_compute; reflexivity. }
    assert (Hp10 : add_vec_int (mword_of_int (KernelSyms.consoleinit + 0x0c) : mword 64) 4 = mword_of_int (KernelSyms.consoleinit + 0x10)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp10) in "Hpc".
    (* +0x10 auipc a0,0x12 *)
    iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.consoleinit + 0x10)) (mword_of_int 10 : mword 5) (mword_of_int 18 : mword 20)
              W4 (K - 2)%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi10").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    set (W5 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg (add_vec (mword_of_int (KernelSyms.consoleinit + 0x10) : mword 64) (auipc_off (mword_of_int 18 : mword 20)))]> W4).
    assert (Hp14 : add_vec_int (mword_of_int (KernelSyms.consoleinit + 0x10) : mword 64) 4 = mword_of_int (KernelSyms.consoleinit + 0x14)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp14) in "Hpc".
    (* +0x14 addi a0,a0,-482 : a0 := &cons (= &cons.lock) *)
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.consoleinit + 0x14)) (mword_of_int 10 : mword 5) (mword_of_int 10 : mword 5) (mword_of_int 3720 : mword 12)
              W5 (K - 2)%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi14").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    set (W6 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg (add_vec (rget W5 (mword_of_int 10 : mword 5)) (sign_extend' 64 (mword_of_int 3720 : mword 12)))]> W5).
    assert (HW6a0 : W6 !!! Regidx (mword_of_int 10 : mword 5) = clk).
    { rewrite /W6 upd_eq. rgne. rewrite /W5 upd_eq /clk. apply bv_eq; vm_compute; reflexivity. }
    assert (HW6a1 : W6 !!! Regidx (mword_of_int 11 : mword 5) = name).
    { rewrite /W6 upd_ne; [| reg_neq]. rewrite /W5 upd_ne; [exact HW4a1 | reg_neq]. }
    assert (Hp18 : add_vec_int (mword_of_int (KernelSyms.consoleinit + 0x14) : mword 64) 4 = mword_of_int (KernelSyms.consoleinit + 0x18)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp18) in "Hpc".
    (* +0x18 jal initlock *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.consoleinit + 0x18)) (mword_of_int 1 : mword 5) (mword_of_int 1786 : mword 21)
              W6 (K - 2)%nat false ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi18").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    set (W7 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.consoleinit + 0x18) : mword 64) 4)]> W6).
    assert (Htgtil : add_vec (mword_of_int (KernelSyms.consoleinit + 0x18) : mword 64) (sign_extend' 64 (mword_of_int 1786 : mword 21)) = mword_of_int KernelSyms.initlock) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtil) in "Hpc".
    assert (HW7a0 : W7 !!! Regidx (mword_of_int 10 : mword 5) = clk) by (rewrite /W7 upd_ne; [exact HW6a0 | reg_neq]).
    assert (HW7a1 : W7 !!! Regidx (mword_of_int 11 : mword 5) = name) by (rewrite /W7 upd_ne; [exact HW6a1 | reg_neq]).
    assert (HW7sp : W7 !!! Regidx csp_rs1 = add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6)))).
    { rewrite /W7 upd_ne; [| reg_neq]. rewrite /W6 upd_ne; [| reg_neq].
      rewrite /W5 upd_ne; [| reg_neq]. rewrite /W4 upd_ne; [| reg_neq].
      rewrite /W3 upd_ne; [| reg_neq]. rewrite /W2 upd_ne; [| reg_neq]. exact HspW1. }
    assert (Hretil : ret_pc (W7 !!! Regidx (mword_of_int 1 : mword 5)) = mword_of_int (KernelSyms.consoleinit + 0x1c)).
    { rewrite /W7 upd_eq. unfold ret_pc. apply bv_eq; vm_compute; reflexivity. }
    (* [W7] is a 7-deep [set] chain; feeding it AS-IS to the [wp_initlock]
       sub-call makes Rocq's elaborator re-walk that whole chain while
       checking the call's own [let]-bound locals (lk/name/...), which is
       slow enough to look like a hang.  Force [Hcg] into the folded
       [sie_cap_gpr W7 ...] shape first (the preceding [set] does not
       reliably fold it), then [remember] severs the syntactic link --
       everything needed about it is already captured in
       [HW7a0]/[HW7a1]/[HW7sp]/[Hretil] above, which [remember] restates
       at [m7] automatically since [W7] is part of the current goal. *)
    iAssert (sie_cap_gpr KT0 W7 (K - 2)%nat false p) with "Hcg" as "Hcg".
    remember W7 as m7 eqn:Heqm7.
    iApply (wp_initlock m7 vclock vcname vccpu "cons"%string (K - 2)%nat false p
              ltac:(lia) with "Hcg Htext Hpc [] [Hclock] [Hcname] [Hccpu]").
    { iEval (rewrite HW7a1). iExact "Hstr". }
    { iEval (rewrite HW7a0). iExact "Hclock". }
    { iEval (rewrite HW7a0). iExact "Hcname". }
    { iEval (rewrite HW7a0). iExact "Hccpu". }
    iApply wp_next_off_intro.
    iIntros (mil) "Hcg Hpc %Hilcs Hclock Hcname Hccpu".
    iEval (rewrite HW7a0) in "Hclock".
    iEval (rewrite HW7a0 HW7a1) in "Hcname".
    iMod (lock_name_intro with "Hstr Hcname") as "#Hcnm".
    iEval (rewrite HW7a0) in "Hccpu".
    iEval (rewrite Hretil) in "Hpc".
    assert (Hmilsp : mil !!! Regidx csp_rs1 = add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6)))).
    { rewrite (callee_saved_lookup Hilcs csp_rs1 ltac:(vm_compute; reflexivity)). exact HW7sp. }
    (* ===== uartinit() (0x1c) ===== *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.consoleinit + 0x1c)) (mword_of_int 1 : mword 5) (mword_of_int 1070 : mword 21)
              mil (K - 2)%nat false ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi1c").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    set (U0 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.consoleinit + 0x1c) : mword 64) 4)]> mil).
    assert (Htgtua : add_vec (mword_of_int (KernelSyms.consoleinit + 0x1c) : mword 64) (sign_extend' 64 (mword_of_int 1070 : mword 21)) = mword_of_int KernelSyms.uartinit) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtua) in "Hpc".
    assert (HU0sp : U0 !!! Regidx csp_rs1 = add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6))))
      by (rewrite /U0 upd_ne; [exact Hmilsp | reg_neq]).
    iApply (wp_uartinit γd U0 (K - 2)%nat l b0 p
              ltac:(lia) with "Hcg Htext Hkdata Hpc Huinv Htx Hlb Hsent Hdlab Hraw").
    iIntros (mu) "Hcg Hpc %Huacs Htx #Hsent' #Hdoff Hfresh".
    assert (Hretua : ret_pc (U0 !!! Regidx (mword_of_int 1 : mword 5)) = mword_of_int (KernelSyms.consoleinit + 0x20)).
    { rewrite /U0 upd_eq. unfold ret_pc. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hretua) in "Hpc".
    assert (Hmusp : mu !!! Regidx csp_rs1 = add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6)))).
    { rewrite (callee_saved_lookup Huacs csp_rs1 ltac:(vm_compute; reflexivity)). exact HU0sp. }
    (* ===== devsw[CONSOLE].read = consoleread (0x20..0x30) ===== *)
    (* +0x20 auipc a5,0x22 *)
    iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.consoleinit + 0x20)) (mword_of_int 15 : mword 5) (mword_of_int 34 : mword 20)
              mu (K - 2)%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi20").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    set (D1 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (add_vec (mword_of_int (KernelSyms.consoleinit + 0x20) : mword 64) (auipc_off (mword_of_int 34 : mword 20)))]> mu).
    assert (Hp24 : add_vec_int (mword_of_int (KernelSyms.consoleinit + 0x20) : mword 64) 4 = mword_of_int (KernelSyms.consoleinit + 0x24)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp24) in "Hpc".
    (* +0x24 addi a5,a5,-130 : a5 := &devsw *)
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.consoleinit + 0x24)) (mword_of_int 15 : mword 5) (mword_of_int 15 : mword 5) (mword_of_int 4072 : mword 12)
              D1 (K - 2)%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi24").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    set (D2 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (add_vec (rget D1 (mword_of_int 15 : mword 5)) (sign_extend' 64 (mword_of_int 4072 : mword 12)))]> D1).
    assert (HD2a5 : D2 !!! Regidx (mword_of_int 15 : mword 5) = (mword_of_int KernelSyms.devsw : mword 64)).
    { rewrite /D2 upd_eq. rgne. rewrite /D1 upd_eq. apply bv_eq; vm_compute; reflexivity. }
    assert (Hp28 : add_vec_int (mword_of_int (KernelSyms.consoleinit + 0x24) : mword 64) 4 = mword_of_int (KernelSyms.consoleinit + 0x28)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp28) in "Hpc".
    (* +0x28 auipc a4,0x0 *)
    iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.consoleinit + 0x28)) (mword_of_int 14 : mword 5) (mword_of_int 0 : mword 20)
              D2 (K - 2)%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi28").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    set (D3 := <[Regidx (mword_of_int 14 : mword 5) := regval_into_reg (add_vec (mword_of_int (KernelSyms.consoleinit + 0x28) : mword 64) (auipc_off (mword_of_int 0 : mword 20)))]> D2).
    assert (Hp2c : add_vec_int (mword_of_int (KernelSyms.consoleinit + 0x28) : mword 64) 4 = mword_of_int (KernelSyms.consoleinit + 0x2c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp2c) in "Hpc".
    (* +0x2c addi a4,a4,-722 : a4 := consoleread *)
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.consoleinit + 0x2c)) (mword_of_int 14 : mword 5) (mword_of_int 14 : mword 5) (mword_of_int 3368 : mword 12)
              D3 (K - 2)%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi2c").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    set (D4 := <[Regidx (mword_of_int 14 : mword 5) := regval_into_reg (add_vec (rget D3 (mword_of_int 14 : mword 5)) (sign_extend' 64 (mword_of_int 3368 : mword 12)))]> D3).
    (* keep the peel chain entirely in RAW ([!!!]) form -- threading a
       [forall CID', rget ...]-quantified fact back DOWN through several more
       levels (as [HD6a5] below would need from a quantified [HD4a5]) makes
       Rocq's conversion checker re-walk the whole map chain and is slow
       enough to look like a hang; convert to [rget] exactly ONCE, at the
       end, from the flat raw fact. *)
    assert (HD4a4_raw : D4 !!! Regidx (mword_of_int 14 : mword 5) = (mword_of_int KernelSyms.consoleread : mword 64)).
    { rewrite /D4 upd_eq. rgne. rewrite /D3 upd_eq. apply bv_eq; vm_compute; reflexivity. }
    assert (HD4a4 : forall (CID' : CpuId), rget (CID := CID') D4 (mword_of_int 14 : mword 5) = (mword_of_int KernelSyms.consoleread : mword 64))
      by (intros CID'; rgne; exact HD4a4_raw).
    assert (HD4a5_raw : D4 !!! Regidx (mword_of_int 15 : mword 5) = (mword_of_int KernelSyms.devsw : mword 64))
      by (rewrite /D4 upd_ne; [| reg_neq]; rewrite /D3 upd_ne; [exact HD2a5 | reg_neq]).
    assert (HD4a5 : forall (CID' : CpuId), rget (CID := CID') D4 (mword_of_int 15 : mword 5) = (mword_of_int KernelSyms.devsw : mword 64))
      by (intros CID'; rgne; exact HD4a5_raw).
    assert (Hp30 : add_vec_int (mword_of_int (KernelSyms.consoleinit + 0x2c) : mword 64) 4 = mword_of_int (KernelSyms.consoleinit + 0x30)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp30) in "Hpc".
    (* +0x30 sd a4,16(a5) : devsw[CONSOLE].read = consoleread *)
    assert (Hdra : forall (CID' : CpuId), add_vec (rget (CID := CID') D4 (mword_of_int 15 : mword 5)) (sign_extend' 64 (mword_of_int 16 : mword 12)) = devsw_console_read).
    { intros CID'. rewrite HD4a5. unfold devsw_console_read. apply bv_eq; vm_compute; reflexivity. }
    iApply (wp_csd_s_sconf (kt := KT0) (ktd := KT0) (mword_of_int (KernelSyms.consoleinit + 0x30)) (mword_of_int 14 : mword 5) (mword_of_int 15 : mword 5) (mword_of_int 16 : mword 12)
              D4 (K - 2)%nat dread0 false with "Hcg Hpc Hi30 [Hdr]").
    { iEval (rewrite Hdra). iExact "Hdr". }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc Hdr". iEval (rewrite Hdra HD4a4) in "Hdr".
    assert (Hp32 : add_vec_int (mword_of_int (KernelSyms.consoleinit + 0x30) : mword 64) 2 = mword_of_int (KernelSyms.consoleinit + 0x32)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp32) in "Hpc".
    (* ===== devsw[CONSOLE].write = consolewrite (0x32..0x3a) ===== *)
    (* +0x32 auipc a4,0x0 *)
    iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.consoleinit + 0x32)) (mword_of_int 14 : mword 5) (mword_of_int 0 : mword 20)
              D4 (K - 2)%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi32").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    set (D5 := <[Regidx (mword_of_int 14 : mword 5) := regval_into_reg (add_vec (mword_of_int (KernelSyms.consoleinit + 0x32) : mword 64) (auipc_off (mword_of_int 0 : mword 20)))]> D4).
    assert (Hp36 : add_vec_int (mword_of_int (KernelSyms.consoleinit + 0x32) : mword 64) 4 = mword_of_int (KernelSyms.consoleinit + 0x36)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp36) in "Hpc".
    (* +0x36 addi a4,a4,-894 : a4 := consolewrite *)
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.consoleinit + 0x36)) (mword_of_int 14 : mword 5) (mword_of_int 14 : mword 5) (mword_of_int 3196 : mword 12)
              D5 (K - 2)%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi36").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    set (D6 := <[Regidx (mword_of_int 14 : mword 5) := regval_into_reg (add_vec (rget D5 (mword_of_int 14 : mword 5)) (sign_extend' 64 (mword_of_int 3196 : mword 12)))]> D5).
    assert (HD6a4_raw : D6 !!! Regidx (mword_of_int 14 : mword 5) = (mword_of_int KernelSyms.consolewrite : mword 64)).
    { rewrite /D6 upd_eq. rgne. rewrite /D5 upd_eq. apply bv_eq; vm_compute; reflexivity. }
    assert (HD6a4 : forall (CID' : CpuId), rget (CID := CID') D6 (mword_of_int 14 : mword 5) = (mword_of_int KernelSyms.consolewrite : mword 64))
      by (intros CID'; rgne; exact HD6a4_raw).
    assert (HD6a5_raw : D6 !!! Regidx (mword_of_int 15 : mword 5) = (mword_of_int KernelSyms.devsw : mword 64))
      by (rewrite /D6 upd_ne; [| reg_neq]; rewrite /D5 upd_ne; [exact HD4a5_raw | reg_neq]).
    assert (HD6a5 : forall (CID' : CpuId), rget (CID := CID') D6 (mword_of_int 15 : mword 5) = (mword_of_int KernelSyms.devsw : mword 64))
      by (intros CID'; rgne; exact HD6a5_raw).
    assert (Hp3a : add_vec_int (mword_of_int (KernelSyms.consoleinit + 0x36) : mword 64) 4 = mword_of_int (KernelSyms.consoleinit + 0x3a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp3a) in "Hpc".
    (* +0x3a sd a4,24(a5) : devsw[CONSOLE].write = consolewrite *)
    assert (Hdwa : forall (CID' : CpuId), add_vec (rget (CID := CID') D6 (mword_of_int 15 : mword 5)) (sign_extend' 64 (mword_of_int 24 : mword 12)) = devsw_console_write).
    { intros CID'. rewrite HD6a5. unfold devsw_console_write. apply bv_eq; vm_compute; reflexivity. }
    iApply (wp_csd_s_sconf (kt := KT0) (ktd := KT0) (mword_of_int (KernelSyms.consoleinit + 0x3a)) (mword_of_int 14 : mword 5) (mword_of_int 15 : mword 5) (mword_of_int 24 : mword 12)
              D6 (K - 2)%nat dwrite0 false with "Hcg Hpc Hi3a [Hdw]").
    { iEval (rewrite Hdwa). iExact "Hdw". }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc Hdw". iEval (rewrite Hdwa HD6a4) in "Hdw".
    assert (Hp3c : add_vec_int (mword_of_int (KernelSyms.consoleinit + 0x3a) : mword 64) 2 = mword_of_int (KernelSyms.consoleinit + 0x3c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp3c) in "Hpc".
    (* ===== EPILOGUE (0x3c..0x42) ===== *)
    assert (HD6sp : D6 !!! Regidx csp_rs1 = add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6)))).
    { rewrite /D6 upd_ne; [| reg_neq]. rewrite /D5 upd_ne; [| reg_neq].
      rewrite /D4 upd_ne; [| reg_neq]. rewrite /D3 upd_ne; [| reg_neq].
      rewrite /D2 upd_ne; [| reg_neq]. rewrite /D1 upd_ne; [| reg_neq]. exact Hmusp. }
    (* +0x3c ld ra,8(sp) *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.consoleinit + 0x3c)) (mword_of_int 1 : mword 6) (mword_of_int 1 : mword 5)
              D6 (K - 2)%nat (m !!! Regidx (mword_of_int 1)) false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi3c [Hc1]").
    { iEval (rewrite HD6sp Hb1). iExact "Hc1". }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc Hc1". iEval (rewrite HD6sp Hb1) in "Hc1".
    set (E1 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 1))]> D6).
    assert (HE1sp : E1 !!! Regidx csp_rs1 = add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6)))) by (rewrite /E1 upd_ne; [| reg_neq]; exact HD6sp).
    assert (Hp3e : add_vec_int (mword_of_int (KernelSyms.consoleinit + 0x3c) : mword 64) 2 = mword_of_int (KernelSyms.consoleinit + 0x3e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp3e) in "Hpc".
    (* +0x3e ld s0,0(sp) *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.consoleinit + 0x3e)) (mword_of_int 0 : mword 6) (mword_of_int 8 : mword 5)
              E1 (K - 2)%nat (m !!! Regidx (mword_of_int 8)) false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi3e [Hc2]").
    { iEval (rewrite HE1sp Hb2). iExact "Hc2". }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc Hc2". iEval (rewrite HE1sp Hb2) in "Hc2".
    set (E2 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 8))]> E1).
    assert (HE2sp : E2 !!! Regidx csp_rs1 = add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6)))) by (rewrite /E2 upd_ne; [| reg_neq]; exact HE1sp).
    assert (Hp40 : add_vec_int (mword_of_int (KernelSyms.consoleinit + 0x3e) : mword 64) 2 = mword_of_int (KernelSyms.consoleinit + 0x40)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp40) in "Hpc".
    (* +0x40 addi sp,sp,16 : the frame pop *)
    assert (Hwv : add_vec (E2 !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6))) = m !!! Regidx csp_rs1).
    { rewrite HE2sp. apply frame_cancel_16. }
    assert (Hpop : E2 !!! Regidx csp_rs1 = pa_stk (add_vec (E2 !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6)))) 2).
    { rewrite Hwv. rewrite HE2sp. exact Hpush. }
    iAssert (stack_own (KTR := KT0) (m !!! Regidx csp_rs1) 2) with "[Hc1 Hc2]" as "Hframe".
    { rewrite (stack_own_slots (KTR := KT0)); cbn [seq].
      iSplitL "Hc1". { iExists (m !!! Regidx (mword_of_int 1)). iExact "Hc1". }
      iSplitL "Hc2". { iExists (m !!! Regidx (mword_of_int 8)). iExact "Hc2". }
      done. }
    iEval (rewrite -Hwv) in "Hframe".
    iApply (wp_caddi_sp_pop_s_sconf (mword_of_int (KernelSyms.consoleinit + 0x40)) (mword_of_int 16 : mword 6)
              E2 (K - 2)%nat 2 false Hpop with "Hcg Hpc Hi40 Hframe").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    set (E3 := <[Regidx csp_rs1 := regval_into_reg (add_vec (E2 !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6))))]> E2).
    iEval (rewrite (cni_nk K Hc2)) in "Hcg".
    assert (Hp42 : add_vec_int (mword_of_int (KernelSyms.consoleinit + 0x40) : mword 64) 2 = mword_of_int (KernelSyms.consoleinit + 0x42)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp42) in "Hpc".
    (* +0x42 ret *)
    assert (HE3ra : E3 !!! Regidx (mword_of_int 1 : mword 5) = m !!! Regidx (mword_of_int 1)).
    { rewrite /E3 upd_ne; [| reg_neq]. rewrite /E2 upd_ne; [| reg_neq]. rewrite /E1 upd_eq. reflexivity. }
    assert (Hrt : forall (CID' : CpuId), ret_pc (rget (CID := CID') E3 (mword_of_int 1 : mword 5)) = ret_pc (m !!! Regidx (mword_of_int 1)))
      by (intros CID'; rgne; rewrite HE3ra; reflexivity).
    iApply (wp_cret_s_sconf (mword_of_int (KernelSyms.consoleinit + 0x42)) (mword_of_int 1 : mword 5) E3 K false
              ltac:(vm_compute; discriminate) with "Hcg Hpc Hi42").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc". iEval (rewrite Hrt) in "Hpc".
    (* ---- hand the continuation both callees' posts + the two devsw cells;
       [Hcont] is now a plain wand chain (BOOT-ONLY: no [wp_next] wrapper),
       so there is no CID to discharge before applying it. ---- *)
    iApply ("Hcont" $! E3 with "Hcg Hpc [%] Htx Hsent Hdoff Hclock Hcnm Hccpu Hfresh Hdr Hdw").
    (* callee_saved m E3: the two sub-calls preserve s1..s11/tp; the epilogue
       restores sp/s0, and ra (caller-saved) is irrelevant. *)
    assert (Hthread : forall c : mword 5, is_cs_idx c = true ->
              c <> mword_of_int 1 -> c <> csp_rs1 -> c <> mword_of_int 8 ->
              E3 !!! Regidx c = m !!! Regidx c).
    { intros c Hc N1 Nsp N8.
      pose proof (is_cs_idx_true_neq (mword_of_int 10 : mword 5) c ltac:(vm_compute; reflexivity) Hc) as Na0.
      pose proof (is_cs_idx_true_neq (mword_of_int 11 : mword 5) c ltac:(vm_compute; reflexivity) Hc) as Na1.
      pose proof (is_cs_idx_true_neq (mword_of_int 14 : mword 5) c ltac:(vm_compute; reflexivity) Hc) as Na4.
      pose proof (is_cs_idx_true_neq (mword_of_int 15 : mword 5) c ltac:(vm_compute; reflexivity) Hc) as Na5.
      rewrite /E3 upd_ne; [| congruence].
      rewrite /E2 upd_ne; [| congruence].
      rewrite /E1 upd_ne; [| congruence].
      rewrite /D6 upd_ne; [| congruence].
      rewrite /D5 upd_ne; [| congruence].
      rewrite /D4 upd_ne; [| congruence].
      rewrite /D3 upd_ne; [| congruence].
      rewrite /D2 upd_ne; [| congruence].
      rewrite /D1 upd_ne; [| congruence].
      rewrite (callee_saved_lookup Huacs c Hc).
      rewrite /U0 upd_ne; [| congruence].
      rewrite (callee_saved_lookup Hilcs c Hc).
      rewrite Heqm7.
      rewrite /W7 upd_ne; [| congruence].
      rewrite /W6 upd_ne; [| congruence].
      rewrite /W5 upd_ne; [| congruence].
      rewrite /W4 upd_ne; [| congruence].
      rewrite /W3 upd_ne; [| congruence].
      rewrite /W2 upd_ne; [| congruence].
      rewrite /W1 upd_ne; [reflexivity | congruence]. }
    unfold callee_saved.
    split. { rewrite /E3 upd_eq. exact Hwv. }
    split. { rewrite /E3 upd_ne; [| reg_neq]. rewrite /E2 upd_eq; reflexivity. }
    repeat split; apply Hthread; vm_compute; first [reflexivity | discriminate].
  Qed.

End ConsoleinitBody.

(* ===================================================================== *)
(* THE SEALED FUNCTOR: instantiate the two callees' WP hypotheses with     *)
(* their proven specs, discharging the CONSOLEINIT Module Type.            *)
(* ===================================================================== *)
Module ConsoleinitProof (Initlock : INITLOCK) (Uartinit : UARTINIT) : CONSOLEINIT.
  Definition wp_consoleinit_sconf `{!riscvGS Σ} `{!sieG Σ} `{!uartGhostG Σ} `{GEN : GenId} `{CID : CpuId}
      (γd : uart_names) (m : regfile) (K : nat)
      (l : list (bv 8)) (b0 : bool)
      (vclock : bv 32) (vcname vccpu : bv 64)
      (dread0 dwrite0 : mword 64) (p : mword 64)
      : wp_consoleinit_sconf_body γd m K l b0 vclock vcname vccpu dread0 dwrite0 p :=
    (* Passed bare, [Initlock.wp_initlock_sconf]'s own implicit [CID] gets
       EAGERLY specialized to THIS definition's [CID] (typeclass-style
       implicit resolution fires on a bare reference), which is strictly
       LESS general than what [wp_consoleinit_sconf_gen]'s [Hypothesis]
       demands (initlock keeps its own generic [b], even though consoleinit
       calls it only at [false]).  Eta-expand to keep the quantifier
       genuinely fresh per application, the same technique ProofConsputc.v
       uses to keep a dfrac argument's implicit explicit. *)
    wp_consoleinit_sconf_gen
      (fun `(CID' : CpuId) m' vlock' vname' vcpu' s' K' b' p' =>
         Initlock.wp_initlock_sconf KT0 (CID:=CID') m' vlock' vname' vcpu' s' K' b' p')
      (fun `(CID' : CpuId) γd' m' K' l' b0' p' =>
         Uartinit.wp_uartinit_sconf (CID:=CID') γd' m' K' l' b0' p')
      γd m K l b0 vclock vcname vccpu dread0 dwrite0 p.
End ConsoleinitProof.
