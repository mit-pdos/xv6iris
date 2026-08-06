(* ProofUartintr.v -- the whole-function WP for xv6's uartintr().

     void uartintr(void)

   The contract is SpecUartintr.v; the 39 instruction facts are
   CodeUartintr.v ([uii2_<off>]).  Structure of the proof:

   - [ui_tail] is the epilogue at +0x6c (four restores, frame pop, ret).
   - [ui_rx] is the receive drain at +0x44: an iLöb, because the device may
     keep supplying bytes.  Its body is [WpUartgetc.wp_uartgetc_inline] --
     uartgetc, which gcc inlined here -- followed by the consoleintr call.
   - [ui_after_tx] is everything from the release at +0x2e onwards; BOTH arms
     of the THRE test reach it (the tx arm jumps back to it from +0x6a), so it
     is a lemma rather than a continuation.
   - the whole function is then the prologue, the ISR acknowledge, acquire,
     the LSR read and its branch.

   THE ONE INTERESTING STEP is at the THRE arm.  The LSR read is taken with
   the transmitter token (out of [tx_res]), so the leaf hands back
   [⌜lsr_thre_clear b = false⌝ -∗ uart_out_lb γu l] -- and on the arm where
   the branch IS taken that hypothesis holds, so the certificate is in hand
   before the [sw zero] that clears [tx_busy] two instructions later.
   Re-closing the invariant with [tx_res_idle] is what makes the flag mean
   "the FIFO has been seen empty", which is exactly what uartwrite reads it
   for.  The other arm re-closes with the cell and the wand it borrowed.

   THE SIE INDEX.  uartintr's contract is [b]-GENERIC, so the whole prologue,
   the ISR acknowledge and the acquire run at [b] and every leaf hands back a
   FRESH hart ([wp_next]).  From acquire's return to release's entry the index
   is literally [false] -- acquire is unbalanced and returns with interrupts
   off -- so that whole stretch (the LSR read, the THRE test, the tx_busy
   clear, the wakeup) collapses by [wp_next_off] and the hart is pinned;
   that is what lets [locked γl cpu_id] and [trap_csrs_pay] be carried across
   it without transport.  release exits at
   [outb = match lvl with O => eb | S _ => false end], which [cpu_own_eb_agree]
   derives to be [b] from the entry resources (porting guide, "Derive the SIE
   index rather than stating it").

   A functor over ACQUIRE / RELEASE / WAKEUP / CONSOLEINTR / UART.  Only
   consoleintr is assumed (LinkConsoleintr.v). *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExtras.
Require Import RegFile.
Require Import InstrBytes WpMmodeLeafBase.
Require Import SmodeCore.
Require Import StackOwn CalleeSaved KernelText WpAuipc.
Require Import WpSconfAlu WpSconfMem WpSconfCtl WpSconfBtype WpSconfVc.
Require Import WpLock ProcGeom CpuOwn KernelRvcDecode.
Require Import IntrDefs HartTp WpNext.
Require Import DevModel DiskPtsto WpUart.
Require Import SpecUart CodeUartPutcSync WpSconfUartAccess WpUartgetc.
Require Import UartTxInv.
Require Import SpecPanic.
Require Import SchedCtx.
Require Import FdSlots.
Require Import SpecAcquire SpecRelease SpecWakeup SpecConsoleintr.
Require Import CodeUartintr.
Require Import SpecUartintr.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Import Defs.
Local Open Scope Z_scope.

Local Notation Rra  := (mword_of_int 1 : mword 5).
Local Notation Rtp' := (mword_of_int 4 : mword 5).
Local Notation Rs0  := (mword_of_int 8 : mword 5).
Local Notation Rs1  := (mword_of_int 9 : mword 5).
Local Notation Ra0  := (mword_of_int 10 : mword 5).
Local Notation Ra5  := (mword_of_int 15 : mword 5).
Local Notation Rs2  := (mword_of_int 18 : mword 5).
Local Notation Rs3  := (mword_of_int 19 : mword 5).
Local Notation Rs4  := (mword_of_int 20 : mword 5).
Local Notation Rs5  := (mword_of_int 21 : mword 5).
Local Notation Rs6  := (mword_of_int 22 : mword 5).
Local Notation Rs7  := (mword_of_int 23 : mword 5).
Local Notation Rs8  := (mword_of_int 24 : mword 5).
Local Notation Rs9  := (mword_of_int 25 : mword 5).
Local Notation Rs10 := (mword_of_int 26 : mword 5).
Local Notation Rs11 := (mword_of_int 27 : mword 5).

(* the 4-slot frame geometry *)
Lemma ui_slot_bridge (X : mword 64) (o : mword 64) (k : nat) :
  add_vec (mword_of_int (- (8 * Z.of_nat 4%nat))) o = mword_of_int (- (8 * Z.of_nat k)) ->
  add_vec (pa_stk X 4%nat) o = pa_stk X k.
Proof.
  intro H. unfold pa_stk, add_vec_int. rewrite po_addv_assoc H. reflexivity.
Qed.

(* ===================================================================== *)
(* [ui_regs] / [ui_ret_cont] live ABOVE the section on purpose: a constant
   defined INSIDE a section carrying [Context `{GEN : GenId} `{CID : CpuId}] is applied at
   that section variable at every use, and would then BEAT the [fun CID =>]
   binder of the [wp_next] it contains (porting guide, "a section-defined
   constant silently beats the wp_next lambda").  [CID0] is the anchor the
   obligation is stated at, and [ui_ret_cont_shift] moves it.               *)
(* ===================================================================== *)

(* every callee-saved register uartintr never touches.  NO tp conjunct:
   [HartTp.tp_pin] makes the slot unobservable, so a statement about it is
   vacuous (porting guide, "any statement about the map's tp slot is now
   meaningless"). *)
Definition ui_regs (m0 M : regfile) (spd : mword 64) : Prop :=
  M !!! Regidx csp_rs1 = spd /\
  M !!! Regidx Rs3 = m0 !!! Regidx Rs3 /\
  M !!! Regidx Rs4 = m0 !!! Regidx Rs4 /\
  M !!! Regidx Rs5 = m0 !!! Regidx Rs5 /\
  M !!! Regidx Rs6 = m0 !!! Regidx Rs6 /\
  M !!! Regidx Rs7 = m0 !!! Regidx Rs7 /\
  M !!! Regidx Rs8 = m0 !!! Regidx Rs8 /\
  M !!! Regidx Rs9 = m0 !!! Regidx Rs9 /\
  M !!! Regidx Rs10 = m0 !!! Regidx Rs10 /\
  M !!! Regidx Rs11 = m0 !!! Regidx Rs11.

Lemma ui_regs_cs (m0 M M' : regfile) (spd : mword 64) :
  callee_saved M M' -> ui_regs m0 M spd -> ui_regs m0 M' spd.
Proof.
  intros Hcs (H2 & H19 & H20 & H21 & H22 & H23 & H24 & H25 & H26 & H27).
  unfold ui_regs.
  repeat first
    [ split
    | rewrite (callee_saved_lookup Hcs csp_rs1 ltac:(vm_compute; reflexivity))
    | rewrite (callee_saved_lookup Hcs (mword_of_int 19) ltac:(vm_compute; reflexivity))
    | rewrite (callee_saved_lookup Hcs (mword_of_int 20) ltac:(vm_compute; reflexivity))
    | rewrite (callee_saved_lookup Hcs (mword_of_int 21) ltac:(vm_compute; reflexivity))
    | rewrite (callee_saved_lookup Hcs (mword_of_int 22) ltac:(vm_compute; reflexivity))
    | rewrite (callee_saved_lookup Hcs (mword_of_int 23) ltac:(vm_compute; reflexivity))
    | rewrite (callee_saved_lookup Hcs (mword_of_int 24) ltac:(vm_compute; reflexivity))
    | rewrite (callee_saved_lookup Hcs (mword_of_int 25) ltac:(vm_compute; reflexivity))
    | rewrite (callee_saved_lookup Hcs (mword_of_int 26) ltac:(vm_compute; reflexivity))
    | rewrite (callee_saved_lookup Hcs (mword_of_int 27) ltac:(vm_compute; reflexivity))
    | assumption ].
Qed.

Section UiCont.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ}.

  (* the frame the prologue spilled *)
  Definition ui_frame (sp0 : mword 64) (m0 : regfile) : iProp Σ :=
    (pa_stk sp0 1 ↦₈ (m0 !!! Regidx Rra) ∗
     pa_stk sp0 2 ↦₈ (m0 !!! Regidx Rs0) ∗
     pa_stk sp0 3 ↦₈ (m0 !!! Regidx Rs1) ∗
     pa_stk sp0 4 ↦₈ (m0 !!! Regidx Rs2))%I.

  (* the caller's continuation, named once *)
  Definition ui_ret_cont `{GEN : GenId} `{CID0 : CpuId} (Φ : mval -> iProp Σ) (m0 : regfile)
      (av lvl : nat) (eb : bool) (pme : mword 64) (C : iProp Σ) (b : bool) : iProp Σ :=
    (wp_next (CID0 := CID0) b pme (fun (CID : CpuId) =>
       ∀ mf : regfile,
         ⌜ callee_saved m0 mf /\ (forall r : regidx, r ∈ dom (rf_to_gmap mf)) ⌝ -∗
         sie_cap_gpr mf av b pme -∗
         cpu_own lvl eb pme C b -∗
         pc_is (ret_pc (m0 !!! Regidx Rra)) -∗
         WP (Loop : expr riscv_lang) {{ Φ }}))%I.

  (* re-anchor it at a hart reached mid-block.  Through the named definition
     [wp_next_shift]'s direct idiom cannot infer [K], so unfold first. *)
  Lemma ui_ret_cont_shift `{GEN : GenId} (CIDa CIDb : CpuId) (Φ : mval -> iProp Σ) (m0 : regfile)
      (av lvl : nat) (eb : bool) (pme : mword 64) (C : iProp Σ) (b : bool) :
    (b = false \/ pme = zero_reg -> (CIDb : CPU) = (CIDa : CPU)) ->
    ui_ret_cont (CID0 := CIDa) Φ m0 av lvl eb pme C b -∗
    ui_ret_cont (CID0 := CIDb) Φ m0 av lvl eb pme C b.
  Proof. intros Hs. rewrite /ui_ret_cont. exact (wp_next_shift Hs). Qed.


End UiCont.

Module UartintrProof (Acquire : ACQUIRE) (Release : RELEASE) (Wakeup : WAKEUP)
                     (Consoleintr : CONSOLEINTR) (Uart : UART) : UARTINTR.

Module UAcc := UartAccessProof Uart.
Module UG := UartgetcProof Uart.

Section ProofUartintr.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ}.
  Context `{!uartGhostG Σ, !diskGhostG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Local Ltac reg_neq :=
    lazymatch goal with |- ?a <> ?b =>
      tryif unify a b then fail else (vm_compute; discriminate) end.
  Local Ltac nz := vm_compute; discriminate.
  Local Ltac pcw := apply bv_eq; vm_compute; reflexivity.


  (* ------------------------------------------------------------------ *)
  (*  THE EPILOGUE: +0x6c -> return.                                      *)
  (* ------------------------------------------------------------------ *)
  Lemma ui_tail `{CID0 : CpuId} (Φ : mval -> iProp Σ)
      (m0 M : regfile) (av lvl : nat) (eb : bool) (pme : mword 64) (C : iProp Σ)
      (sp0 : mword 64) (b : bool) :
    ui_regs m0 M (pa_stk sp0 4) ->
    m0 !!! Regidx csp_rs1 = sp0 ->
    (uartintr_stack <= av)%nat ->
    kernel_text -∗
    sie_cap_gpr M (av - 4) b pme -∗
    cpu_own lvl eb pme C b -∗
    pc_is (mword_of_int (KernelSyms.uartintr + 0x6c)) -∗
    ui_frame sp0 m0 -∗
    ui_ret_cont Φ m0 av lvl eb pme C b -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros Hregs Hsp0 Hav.
    destruct Hregs as (Hsp & H19 & H20 & H21 & H22 & H23 & H24 & H25 & H26 & H27).
    iIntros "#Ht Hcg Hcnt Hpc Hfr Hcont".
    rewrite /ui_frame. iDestruct "Hfr" as "(H1 & H2 & H3 & H4)".
    set (spd := pa_stk sp0 4).
    assert (Hb1 : add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000"))) = pa_stk sp0 1)
      by (apply ui_slot_bridge; pcw).
    assert (Hb2 : add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000"))) = pa_stk sp0 2)
      by (apply ui_slot_bridge; pcw).
    assert (Hb3 : add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) = pa_stk sp0 3)
      by (apply ui_slot_bridge; pcw).
    assert (Hb4 : add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000"))) = pa_stk sp0 4)
      by (apply ui_slot_bridge; pcw).
    assert (P6e : add_vec_int (mword_of_int (KernelSyms.uartintr + 0x6c) : mword 64) 2 = mword_of_int (KernelSyms.uartintr + 0x6e)) by pcw.
    assert (P70 : add_vec_int (mword_of_int (KernelSyms.uartintr + 0x6e) : mword 64) 2 = mword_of_int (KernelSyms.uartintr + 0x70)) by pcw.
    assert (P72 : add_vec_int (mword_of_int (KernelSyms.uartintr + 0x70) : mword 64) 2 = mword_of_int (KernelSyms.uartintr + 0x72)) by pcw.
    assert (P74 : add_vec_int (mword_of_int (KernelSyms.uartintr + 0x72) : mword 64) 2 = mword_of_int (KernelSyms.uartintr + 0x74)) by pcw.
    assert (P76 : add_vec_int (mword_of_int (KernelSyms.uartintr + 0x74) : mword 64) 2 = mword_of_int (KernelSyms.uartintr + 0x76)) by pcw.
    (* +0x6c c.ldsp ra,24(sp) *)
    iPoseProof (uii2_6c with "Ht") as "Hi6c".
    iApply (wp_cldsp_s_sconf Φ (mword_of_int (KernelSyms.uartintr + 0x6c)) (mword_of_int 3 : mword 6) Rra
              M (av - 4)%nat (m0 !!! Regidx Rra) b (dqm := DfracOwn 1) ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hi6c [H1] [-]").
    { iEval (rewrite Hsp Hb1). iExact "H1". }
    iIntros (CID1 Hs1) "Hcg Hpc H1". iEval (rewrite Hsp Hb1) in "H1".
    set (E1 := <[Regidx Rra := regval_into_reg (m0 !!! Regidx Rra)]> M).
    change (<[Regidx Rra := regval_into_reg (m0 !!! Regidx Rra)]> M) with E1.
    assert (HE1sp : E1 !!! Regidx csp_rs1 = spd) by (rewrite /E1 upd_ne; [exact Hsp | reg_neq]).
    iEval (rewrite P6e) in "Hpc".
    (* +0x6e c.ldsp s0,16(sp) *)
    iPoseProof (uii2_6e with "Ht") as "Hi6e".
    iApply (wp_cldsp_s_sconf Φ (mword_of_int (KernelSyms.uartintr + 0x6e)) (mword_of_int 2 : mword 6) Rs0
              E1 (av - 4)%nat (m0 !!! Regidx Rs0) b (dqm := DfracOwn 1) ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hi6e [H2] [-]").
    { iEval (rewrite HE1sp Hb2). iExact "H2". }
    iIntros (CID2 Hs2) "Hcg Hpc H2".
    set (E2 := <[Regidx Rs0 := regval_into_reg (m0 !!! Regidx Rs0)]> E1).
    change (<[Regidx Rs0 := regval_into_reg (m0 !!! Regidx Rs0)]> E1) with E2.
    assert (HE2sp : E2 !!! Regidx csp_rs1 = spd) by (rewrite /E2 upd_ne; [exact HE1sp | reg_neq]).
    iEval (rewrite P70) in "Hpc".
    (* +0x70 c.ldsp s1,8(sp) *)
    iPoseProof (uii2_70 with "Ht") as "Hi70".
    iApply (wp_cldsp_s_sconf Φ (mword_of_int (KernelSyms.uartintr + 0x70)) (mword_of_int 1 : mword 6) Rs1
              E2 (av - 4)%nat (m0 !!! Regidx Rs1) b (dqm := DfracOwn 1) ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hi70 [H3] [-]").
    { iEval (rewrite HE2sp Hb3). iExact "H3". }
    iIntros (CID3 Hs3) "Hcg Hpc H3".
    set (E3 := <[Regidx Rs1 := regval_into_reg (m0 !!! Regidx Rs1)]> E2).
    change (<[Regidx Rs1 := regval_into_reg (m0 !!! Regidx Rs1)]> E2) with E3.
    assert (HE3sp : E3 !!! Regidx csp_rs1 = spd) by (rewrite /E3 upd_ne; [exact HE2sp | reg_neq]).
    iEval (rewrite P72) in "Hpc".
    (* +0x72 c.ldsp s2,0(sp) *)
    iPoseProof (uii2_72 with "Ht") as "Hi72".
    iApply (wp_cldsp_s_sconf Φ (mword_of_int (KernelSyms.uartintr + 0x72)) (mword_of_int 0 : mword 6) Rs2
              E3 (av - 4)%nat (m0 !!! Regidx Rs2) b (dqm := DfracOwn 1) ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hi72 [H4] [-]").
    { iEval (rewrite HE3sp Hb4). iExact "H4". }
    iIntros (CID4 Hs4) "Hcg Hpc H4".
    set (E4 := <[Regidx Rs2 := regval_into_reg (m0 !!! Regidx Rs2)]> E3).
    change (<[Regidx Rs2 := regval_into_reg (m0 !!! Regidx Rs2)]> E3) with E4.
    assert (HE4sp : E4 !!! Regidx csp_rs1 = spd) by (rewrite /E4 upd_ne; [exact HE3sp | reg_neq]).
    iEval (rewrite P74) in "Hpc".
    (* +0x74 c.addi16sp sp,32 -- the frame pop *)
    iAssert (stack_own sp0 4) with "[H1 H2 H3 H4]" as "Hframe".
    { rewrite stack_own_slots. cbn [seq].
      iSplitL "H1"; [by iExists _|]. iSplitL "H2"; [iExists _; iEval (rewrite -Hb2 -HE1sp); iExact "H2"|].
      iSplitL "H3"; [iExists _; iEval (rewrite -Hb3 -HE2sp); iExact "H3"|].
      iSplitL "H4"; [iExists _; iEval (rewrite -Hb4 -HE3sp); iExact "H4"|]. done. }
    assert (Hpopv : add_vec (E4 !!! Regidx csp_rs1)
                      (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))) = sp0).
    { rewrite HE4sp /spd. unfold pa_stk, add_vec_int. rewrite po_addv_assoc.
      rewrite (_ : add_vec (mword_of_int (- (8 * Z.of_nat 4%nat)) : mword 64)
                     (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6)))
                   = (mword_of_int 0 : mword 64)); [| pcw].
      apply bv_add_0_r. vm_compute. reflexivity. }
    assert (Hpop : E4 !!! Regidx csp_rs1
                   = pa_stk (add_vec (E4 !!! Regidx csp_rs1)
                       (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6)))) 4%nat)
      by (rewrite Hpopv HE4sp; reflexivity).
    iEval (rewrite -Hpopv) in "Hframe".
    iPoseProof (uii2_74 with "Ht") as "Hi74".
    iApply (wp_caddi16sp_pop_s_sconf Φ (mword_of_int (KernelSyms.uartintr + 0x74)) (mword_of_int 2 : mword 6)
              E4 (av - 4)%nat 4%nat b Hpop with "Hcg Hpc Hi74 Hframe [-]").
    iIntros (CID5 Hs5) "Hcg Hpc".
    assert (Hav4 : ((av - 4) + 4)%nat = av) by (unfold uartintr_stack in Hav; lia).
    iEval (rewrite Hav4) in "Hcg".
    set (E5 := <[Regidx csp_rs1 := regval_into_reg
        (add_vec (E4 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))))]> E4).
    change (<[Regidx csp_rs1 := regval_into_reg
        (add_vec (E4 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))))]> E4) with E5.
    iEval (rewrite P76) in "Hpc".
    (* +0x76 c.ret *)
    assert (HE5ra : E5 !!! Regidx Rra = m0 !!! Regidx Rra).
    { rewrite /E5 upd_ne; [| reg_neq]. rewrite /E4 upd_ne; [| reg_neq].
      rewrite /E3 upd_ne; [| reg_neq]. rewrite /E2 upd_ne; [| reg_neq].
      rewrite /E1 upd_eq. reflexivity. }
    assert (HE5rg : forall (CID' : CpuId), rget (CID := CID') E5 Rra = m0 !!! Regidx Rra).
    { intros CID'; rgne. exact HE5ra. }
    iPoseProof (uii2_76 with "Ht") as "Hi76".
    iApply (wp_cret_s_sconf Φ (mword_of_int (KernelSyms.uartintr + 0x76)) Rra E5 av b ltac:(nz)
              with "Hcg Hpc Hi76 [-]").
    iIntros (CID6 Hs6) "Hcg Hpc". iEval (rewrite HE5rg) in "Hpc".
    (* ---- callee_saved m0 E5 ---- *)
    assert (Hpeel : forall r : mword 5,
              r <> csp_rs1 -> r <> Rra -> r <> Rs0 -> r <> Rs1 -> r <> Rs2 ->
              E5 !!! Regidx r = M !!! Regidx r).
    { intros r N2 N1 N8 N9 N18.
      rewrite /E5 upd_ne; [| congruence]. rewrite /E4 upd_ne; [| congruence].
      rewrite /E3 upd_ne; [| congruence]. rewrite /E2 upd_ne; [| congruence].
      rewrite /E1 upd_ne; [| congruence]. reflexivity. }
    iDestruct (cpu_own_transport CID0 CID6 lvl eb pme C b ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    rewrite /ui_ret_cont.
    iSpecialize ("Hcont" $! CID6 with "[%]"); [wp_next_chain|].
    iApply ("Hcont" $! E5 with "[%] Hcg Hcnt Hpc").
    split; [| intro r; apply rf_to_gmap_dom].
    unfold callee_saved.
    split; [rewrite /E5 upd_eq Hpopv; symmetry; exact Hsp0|].
    split; [rewrite /E5 upd_ne; [| reg_neq]; rewrite /E4 upd_ne; [| reg_neq];
            rewrite /E3 upd_ne; [| reg_neq]; rewrite /E2 upd_eq; reflexivity|].
    split; [rewrite /E5 upd_ne; [| reg_neq]; rewrite /E4 upd_ne; [| reg_neq];
            rewrite /E3 upd_eq; reflexivity|].
    split; [rewrite /E5 upd_ne; [| reg_neq]; rewrite /E4 upd_eq; reflexivity|].
    split; [rewrite (Hpeel (mword_of_int 19) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)); exact H19|].
    split; [rewrite (Hpeel (mword_of_int 20) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)); exact H20|].
    split; [rewrite (Hpeel (mword_of_int 21) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)); exact H21|].
    split; [rewrite (Hpeel (mword_of_int 22) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)); exact H22|].
    split; [rewrite (Hpeel (mword_of_int 23) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)); exact H23|].
    split; [rewrite (Hpeel (mword_of_int 24) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)); exact H24|].
    split; [rewrite (Hpeel (mword_of_int 25) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)); exact H25|].
    split; [rewrite (Hpeel (mword_of_int 26) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)); exact H26|].
    rewrite (Hpeel (mword_of_int 27) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)); exact H27.
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  THE RECEIVE DRAIN: +0x44 -> +0x6c  (iLoeb).                         *)
  (* ------------------------------------------------------------------ *)
  (* [while ((c = uartgetc()) != -1) consoleintr(c)].  Unbounded: nothing
     stops the device from supplying another byte, so this is a Loeb loop and
     not an induction.  Its body is uartgetc (inlined -- WpUartgetc.v) and the
     consoleintr call; neither touches the transmitter, which is why the loop
     may run outside the critical section, exactly as the C does.

     THE HART IS PART OF THE LOOP STATE: the loop runs at [b], so every
     iteration ends on a fresh hart, and both [sie_cap_gpr] / [cpu_own] and
     the caller's obligation have to be re-anchored there before the back
     edge.  Hence the leading [∀ CIDk : CpuId] in the invariant. *)
  Lemma ui_rx (γu : uart_names) (γv : disk_names) (Φ : mval -> iProp Σ)
      (γs : list gname) (m0 : regfile) (av lvl : nat) (eb : bool)
      (pme : mword 64) (C : iProp Σ) (sp0 : mword 64) (b : bool) :
    m0 !!! Regidx csp_rs1 = sp0 ->
    length γs = NPROC ->
    (Z.of_nat lvl + 2 < 2 ^ 31)%Z ->
    (uartintr_stack <= av)%nat ->
    ⊢ ∀ (CIDe : CpuId) (M : regfile),
      ⌜ ui_regs m0 M (pa_stk sp0 4) ⌝ -∗
      ⌜ M !!! Regidx Rs1 = uart_pa 5 ⌝ -∗
      ⌜ M !!! Regidx Rs2 = uart_pa 0 ⌝ -∗
      kernel_text -∗ dev_inv γu γv -∗ procs_inv Φ γs -∗ panic_wp_any -∗
      sie_cap_gpr (CID := CIDe) M (av - 4) b pme -∗
      cpu_own (CID := CIDe) lvl eb pme C b -∗
      pc_is (mword_of_int (KernelSyms.uartintr + 0x44)) -∗
      ui_frame sp0 m0 -∗
      ui_ret_cont (CID0 := CIDe) Φ m0 av lvl eb pme C b -∗
      WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros Hsp0 Hlen Hlvl Hav.
    iIntros (CIDe M) "%Hregs %Hs1 %Hs2 #Ht #Hdinv #Hpinv #Hpanic".
    iIntros "Hcg Hcnt Hpc Hfr Hcont".
    iPoseProof (uii2_44 with "Ht") as "#Hi44".
    iPoseProof (uii2_48 with "Ht") as "#Hi48".
    iPoseProof (uii2_4a with "Ht") as "#Hi4a".
    iPoseProof (uii2_4c with "Ht") as "#Hi4c".
    iPoseProof (uii2_50 with "Ht") as "#Hi50".
    iPoseProof (uii2_54 with "Ht") as "#Hi54".
    iEval (rewrite UG.ug_cr7) in "Hi48".
    assert (Jcall : add_vec (mword_of_int (KernelSyms.uartintr + 0x50) : mword 64)
                      (sign_extend' 64 (mword_of_int 2095248 : mword 21))
                    = mword_of_int KernelSyms.consoleintr) by pcw.
    assert (Jback : add_vec (mword_of_int (KernelSyms.uartintr + 0x54) : mword 64)
                      (sign_extend' 64 (sign_extend' 21 (concat_vec (mword_of_int 2040 : mword 11) ('b"0"))))
                    = mword_of_int (KernelSyms.uartintr + 0x44)) by pcw.
    iAssert (∀ (CIDk : CpuId) (M1 : regfile),
      ⌜ ui_regs m0 M1 (pa_stk sp0 4) ⌝ -∗
      ⌜ M1 !!! Regidx Rs1 = uart_pa 5 ⌝ -∗
      ⌜ M1 !!! Regidx Rs2 = uart_pa 0 ⌝ -∗
      sie_cap_gpr (CID := CIDk) M1 (av - 4) b pme -∗
      cpu_own (CID := CIDk) lvl eb pme C b -∗
      pc_is (mword_of_int (KernelSyms.uartintr + 0x44)) -∗
      ui_frame sp0 m0 -∗
      ui_ret_cont (CID0 := CIDk) Φ m0 av lvl eb pme C b -∗
      WP (Loop : expr riscv_lang) {{ Φ }})%I with "[]" as "Loop".
    { iLöb as "IH".
      iIntros (CIDk M1) "%Hregs1 %Hls1 %Hls2 Hcg Hcnt Hpc Hfr Hcont".
      assert (Hlsr : forall (CID' : CpuId), rget (CID := CID') M1 Rs1 = uart_pa 5)
        by (intros CID'; rgne; exact Hls1).
      assert (Hrhr : forall (CID' : CpuId), rget (CID := CID') M1 Rs2 = uart_pa 0)
        by (intros CID'; rgne; exact Hls2).
      iApply (UG.wp_uartgetc_inline γu γv Φ M1 (av - 4)%nat Rs1 Rs2
                (mword_of_int 17 : mword 8)
                (mword_of_int (KernelSyms.uartintr + 0x44)) (mword_of_int (KernelSyms.uartintr + 0x48))
                (mword_of_int (KernelSyms.uartintr + 0x4a)) (mword_of_int (KernelSyms.uartintr + 0x4c))
                (mword_of_int (KernelSyms.uartintr + 0x50)) (mword_of_int (KernelSyms.uartintr + 0x6c)) b
                (Hlsr _) (Hrhr _) ltac:(reg_neq) ltac:(reg_neq)
                ltac:(pcw) ltac:(pcw) ltac:(pcw) ltac:(pcw) ltac:(pcw)
                ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi44 Hi48 Hi4a Hi4c Hdinv [Hcnt Hfr Hcont]").
      iIntros (CIDg Hsg).
      iSplit.
      - (* the FIFO was empty: leave the loop *)
        iIntros (bt) "_ Hcg Hpc".
        assert (Hrx : ui_regs m0 (<[Regidx Ra5 := regval_into_reg (UG.rx_masked bt)]> M1)
                        (pa_stk sp0 4)).
        { destruct Hregs1 as (A2 & A19 & A20 & A21 & A22 & A23 & A24 & A25 & A26 & A27).
          unfold ui_regs. split_and!; (rewrite upd_ne; [| reg_neq]); assumption. }
        iDestruct (cpu_own_transport CIDk CIDg lvl eb pme C b ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
        iDestruct (ui_ret_cont_shift CIDk CIDg Φ m0 av lvl eb pme C b
                     ltac:(wp_next_chain) with "Hcont") as "Hcont".
        iApply (ui_tail Φ m0 (<[Regidx Ra5 := regval_into_reg (UG.rx_masked bt)]> M1)
                  av lvl eb pme C sp0 b Hrx Hsp0 Hav
                  with "Ht Hcg Hcnt Hpc Hfr Hcont").
      - (* a byte: hand it to consoleintr and go round again *)
        iIntros (bt c) "_ Hcg Hpc".
        set (G0 := <[Regidx Ra0 := regval_into_reg (lsr_ldval_of c)]>
                   (<[Regidx Ra5 := regval_into_reg (UG.rx_masked bt)]> M1)).
        change (<[Regidx Ra0 := regval_into_reg (lsr_ldval_of c)]>
                (<[Regidx Ra5 := regval_into_reg (UG.rx_masked bt)]> M1)) with G0.
        (* +0x50 jal ra,consoleintr *)
        iApply (wp_jal_s_sconf Φ (mword_of_int (KernelSyms.uartintr + 0x50)) Rra (mword_of_int 2095248 : mword 21)
                  G0 (av - 4)%nat b ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc Hi50 [-]").
        iIntros (CIDj Hsj) "Hcg Hpc".
        set (G1 := <[Regidx Rra := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.uartintr + 0x50) : mword 64) 4)]> G0).
        change (<[Regidx Rra := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.uartintr + 0x50) : mword 64) 4)]> G0) with G1.
        iEval (rewrite Jcall) in "Hpc".
        pose proof Hregs1 as Hregs1'.
        destruct Hregs1' as (A2 & A19 & A20 & A21 & A22 & A23 & A24 & A25 & A26 & A27).
        assert (HG1ra : G1 !!! Regidx Rra = add_vec_int (mword_of_int (KernelSyms.uartintr + 0x50) : mword 64) 4)
          by (rewrite /G1 upd_eq; reflexivity).
        assert (HcsG1 : callee_saved M1 G1).
        { rewrite /G1 /G0.
          apply callee_saved_insert_r; [vm_compute; reflexivity|].
          apply callee_saved_insert_r; [vm_compute; reflexivity|].
          apply callee_saved_insert_r; [vm_compute; reflexivity|].
          apply callee_saved_refl. }
        iDestruct (cpu_own_transport CIDk CIDj lvl eb pme C b ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
        iApply (Consoleintr.wp_consoleintr_sconf Φ G1 γs pme lvl (av - 4)%nat eb C b
                  ltac:(unfold consoleintr_stack, uartintr_stack in *; lia)
                  ltac:(intro r; apply rf_to_gmap_dom)
                  Hlen
                  ltac:(rewrite rget_tp; exact (mycpu_ret_nonzero _ (tp_ok_cid_of _)))
                  ltac:(lia)
                  with "Hcg Hcnt Ht Hpc Hpanic Hpinv [-]").
        iIntros (CIDc Hsc Mf) "[%Hcsf %Hdomf] Hcg Hcnt Ht2 Hpc".
        iEval (rewrite HG1ra) in "Hpc".
        assert (P54 : ret_pc (add_vec_int (mword_of_int (KernelSyms.uartintr + 0x50) : mword 64) 4)
                      = mword_of_int (KernelSyms.uartintr + 0x54)) by pcw.
        iEval (rewrite P54) in "Hpc".
        assert (HcsMf : callee_saved M1 Mf) by (apply (callee_saved_trans M1 G1 Mf HcsG1 Hcsf)).
        (* +0x54 c.j -> the loop head *)
        iApply (wp_cj_s_sconf Φ (mword_of_int (KernelSyms.uartintr + 0x54))
                  (sign_extend' 21 (concat_vec (mword_of_int 2040 : mword 11) ('b"0")))
                  Mf (av - 4)%nat b ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi54 [-]").
        iIntros (CIDz Hsz). iNext. iIntros "Hcg Hpc". iEval (rewrite Jback) in "Hpc".
        iDestruct (cpu_own_transport CIDc CIDz lvl eb pme C b ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
        iDestruct (ui_ret_cont_shift CIDk CIDz Φ m0 av lvl eb pme C b
                     ltac:(wp_next_chain) with "Hcont") as "Hcont".
        iApply ("IH" $! CIDz Mf with "[%] [%] [%] Hcg Hcnt Hpc Hfr Hcont").
        + apply (ui_regs_cs m0 M1 Mf); [exact HcsMf | exact Hregs1].
        + rewrite (callee_saved_lookup HcsMf (mword_of_int 9) ltac:(vm_compute; reflexivity)). exact Hls1.
        + rewrite (callee_saved_lookup HcsMf (mword_of_int 18) ltac:(vm_compute; reflexivity)). exact Hls2. }
    iApply ("Loop" $! CIDe M with "[%] [%] [%] Hcg Hcnt Hpc Hfr Hcont");
      [exact Hregs | exact Hs1 | exact Hs2].
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  THE JOIN: +0x2e (release) -> the rx drain -> return.                *)
  (* ------------------------------------------------------------------ *)
  (* Both arms of the THRE test arrive here: the arm that found the FIFO
     still busy falls through from +0x2c, and the arm that cleared tx_busy
     and woke the writers jumps back from +0x6a.  Entered with interrupts
     OFF (acquire is unbalanced), so everything up to the release collapses
     by [wp_next_off]; from release's exit onwards the index is [b] again. *)
  Lemma ui_after_tx `{CID0 : CpuId} (γl : gname) (γu : uart_names) (γv : disk_names)
      (Φ : mval -> iProp Σ) (γs : list gname)
      (m0 M : regfile) (av lvl : nat) (eb : bool) (pme : mword 64) (C : iProp Σ)
      (sp0 : mword 64) (b : bool) :
    ui_regs m0 M (pa_stk sp0 4) ->
    m0 !!! Regidx csp_rs1 = sp0 ->
    length γs = NPROC ->
    (Z.of_nat lvl + 2 < 2 ^ 31)%Z ->
    (uartintr_stack <= av)%nat ->
    (match lvl with O => eb | S _ => false end) = b ->
    kernel_text -∗ dev_inv γu γv -∗ is_txlock γl γu -∗
    procs_inv Φ γs -∗ panic_wp_any -∗
    sie_cap_gpr M (av - 4) false pme -∗
    cpu_own (S lvl) eb pme C false -∗ trap_csrs_pay lvl eb -∗
    pc_is (mword_of_int (KernelSyms.uartintr + 0x2e)) -∗
    locked γl cpu_id -∗ tx_res γu -∗
    ui_frame sp0 m0 -∗
    ui_ret_cont Φ m0 av lvl eb pme C b -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros Hregs Hsp0 Hlen Hlvl Hav Hbeq.
    iIntros "#Ht #Hdinv #Htxl #Hpinv #Hpanic Hcg Hcnt Hpay Hpc Htok HR Hfr Hcont".
    iDestruct (is_txlock_lock with "Htxl") as "#Hlk".
    pose proof Hregs as Hregs'.
    destruct Hregs' as (Hsp & H19 & H20 & H21 & H22 & H23 & H24 & H25 & H26 & H27).
    iPoseProof (uii2_2e with "Ht") as "Hi2e".
    iPoseProof (uii2_32 with "Ht") as "Hi32".
    iPoseProof (uii2_36 with "Ht") as "Hi36".
    iPoseProof (uii2_3a with "Ht") as "Hi3a".
    iPoseProof (uii2_3e with "Ht") as "Hi3e".
    iPoseProof (uii2_40 with "Ht") as "Hi40".
    assert (P32 : add_vec_int (mword_of_int (KernelSyms.uartintr + 0x2e) : mword 64) 4 = mword_of_int (KernelSyms.uartintr + 0x32)) by pcw.
    assert (P36 : add_vec_int (mword_of_int (KernelSyms.uartintr + 0x32) : mword 64) 4 = mword_of_int (KernelSyms.uartintr + 0x36)) by pcw.
    assert (P3a : ret_pc (add_vec_int (mword_of_int (KernelSyms.uartintr + 0x36) : mword 64) 4) = mword_of_int (KernelSyms.uartintr + 0x3a)) by pcw.
    assert (P3e : add_vec_int (mword_of_int (KernelSyms.uartintr + 0x3a) : mword 64) 4 = mword_of_int (KernelSyms.uartintr + 0x3e)) by pcw.
    assert (P40 : add_vec_int (mword_of_int (KernelSyms.uartintr + 0x3e) : mword 64) 2 = mword_of_int (KernelSyms.uartintr + 0x40)) by pcw.
    assert (P44 : add_vec_int (mword_of_int (KernelSyms.uartintr + 0x40) : mword 64) 4 = mword_of_int (KernelSyms.uartintr + 0x44)) by pcw.
    (* +0x2e auipc a0,0x12 / +0x32 addi a0,a0,-1772 *)
    iApply (wp_auipc_s_sconf Φ (mword_of_int (KernelSyms.uartintr + 0x2e)) Ra0 (mword_of_int 18 : mword 20)
              M (av - 4)%nat false ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi2e [-]").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    set (R0 := <[Regidx Ra0 := regval_into_reg
        (add_vec (mword_of_int (KernelSyms.uartintr + 0x2e) : mword 64) (auipc_off (mword_of_int 18 : mword 20)))]> M).
    change (<[Regidx Ra0 := regval_into_reg
        (add_vec (mword_of_int (KernelSyms.uartintr + 0x2e) : mword 64) (auipc_off (mword_of_int 18 : mword 20)))]> M) with R0.
    iEval (rewrite P32) in "Hpc".
    assert (HR0rg : forall (CID' : CpuId), rget (CID := CID') R0 Ra0 = R0 !!! Regidx Ra0)
      by (intros CID'; rgne; reflexivity).
    iApply (wp_addi4_s_sconf Φ (mword_of_int (KernelSyms.uartintr + 0x32)) Ra0 Ra0 (mword_of_int 0x914 : mword 12)
              R0 (av - 4)%nat false ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi32 [-]").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    iEval (rewrite HR0rg) in "Hcg".
    set (R1 := <[Regidx Ra0 := regval_into_reg
        (add_vec (R0 !!! Regidx Ra0) (sign_extend' 64 (mword_of_int 0x914 : mword 12)))]> R0).
    change (<[Regidx Ra0 := regval_into_reg
        (add_vec (R0 !!! Regidx Ra0) (sign_extend' 64 (mword_of_int 0x914 : mword 12)))]> R0) with R1.
    iEval (rewrite P36) in "Hpc".
    (* +0x36 jal ra,release *)
    iApply (wp_jal_s_sconf Φ (mword_of_int (KernelSyms.uartintr + 0x36)) Rra (mword_of_int 652 : mword 21)
              R1 (av - 4)%nat false ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi36 [-]").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    set (R2 := <[Regidx Rra := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.uartintr + 0x36) : mword 64) 4)]> R1).
    change (<[Regidx Rra := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.uartintr + 0x36) : mword 64) 4)]> R1) with R2.
    assert (Hjrel : add_vec (mword_of_int (KernelSyms.uartintr + 0x36) : mword 64)
                      (sign_extend' 64 (mword_of_int 652 : mword 21)) = mword_of_int KernelSyms.release) by pcw.
    iEval (rewrite Hjrel) in "Hpc".
    assert (HR2a0 : R2 !!! Regidx Ra0 = a_tx_lock).
    { rewrite /R2 upd_ne; [| reg_neq]. rewrite /R1 upd_eq. rewrite /R0 upd_eq.
      rewrite /a_tx_lock. pcw. }
    assert (HR2ra : R2 !!! Regidx Rra = add_vec_int (mword_of_int (KernelSyms.uartintr + 0x36) : mword 64) 4)
      by (rewrite /R2 upd_eq; reflexivity).
    assert (HcsR2 : callee_saved M R2).
    { rewrite /R2 /R1 /R0.
      apply callee_saved_insert_r; [vm_compute; reflexivity|].
      apply callee_saved_insert_r; [vm_compute; reflexivity|].
      apply callee_saved_insert_r; [vm_compute; reflexivity|].
      apply callee_saved_refl. }
    iApply (Release.wp_release_sconf Φ γl a_tx_lock "uart"%string (tx_res γu) R2
              lvl eb pme C (av - 4)%nat
              ltac:(rewrite HR2a0; apply bv_add_0_r; vm_compute; reflexivity)
              ltac:(unfold uartintr_stack in Hav; lia)
              with "Hcg Ht Hpc [Hlk] [Htok] [HR] Hcnt Hpay [-]").
    { iExact "Hlk". }
    { iExact "Htok". }
    { iExact "HR". }
    rewrite Hbeq.
    iIntros (CIDR HsR MR) "Hcg Hpc %HcsR Hcnt".
    iEval (rewrite HR2ra P3a) in "Hpc".
    assert (HregsR : ui_regs m0 MR (pa_stk sp0 4)).
    { apply (ui_regs_cs m0 R2 MR); [exact HcsR|].
      apply (ui_regs_cs m0 M R2); [exact HcsR2 | exact Hregs]. }
    (* +0x3a lui s1,0x10000 / +0x3e c.addi s1,s1,5 -- s1 := &LSR *)
    iApply (wp_lui_s_sconf Φ (mword_of_int (KernelSyms.uartintr + 0x3a)) Rs1 (mword_of_int 0x10000 : mword 20)
              (uart_pa 0) MR (av - 4)%nat b ltac:(nz) ltac:(rdok)
              ltac:(apply bv_eq; vm_compute; reflexivity) with "Hcg Hpc Hi3a [-]").
    iIntros (CIDT1 HsT1) "Hcg Hpc".
    set (S0 := <[Regidx Rs1 := regval_into_reg (uart_pa 0)]> MR).
    change (<[Regidx Rs1 := regval_into_reg (uart_pa 0)]> MR) with S0.
    iEval (rewrite P3e) in "Hpc".
    assert (HS0rg : forall (CID' : CpuId), rget (CID := CID') S0 Rs1 = S0 !!! Regidx Rs1)
      by (intros CID'; rgne; reflexivity).
    iApply (wp_caddi_s_sconf Φ (mword_of_int (KernelSyms.uartintr + 0x3e)) Rs1 (mword_of_int 5 : mword 6)
              S0 (av - 4)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi3e [-]").
    iIntros (CIDT2 HsT2) "Hcg Hpc".
    iEval (rewrite HS0rg) in "Hcg".
    set (S1 := <[Regidx Rs1 := regval_into_reg
        (add_vec (S0 !!! Regidx Rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 5 : mword 6))))]> S0).
    change (<[Regidx Rs1 := regval_into_reg
        (add_vec (S0 !!! Regidx Rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 5 : mword 6))))]> S0) with S1.
    iEval (rewrite P40) in "Hpc".
    (* +0x40 lui s2,0x10000 -- s2 := &RHR *)
    iApply (wp_lui_s_sconf Φ (mword_of_int (KernelSyms.uartintr + 0x40)) Rs2 (mword_of_int 0x10000 : mword 20)
              (uart_pa 0) S1 (av - 4)%nat b ltac:(nz) ltac:(rdok)
              ltac:(apply bv_eq; vm_compute; reflexivity) with "Hcg Hpc Hi40 [-]").
    iIntros (CIDT3 HsT3) "Hcg Hpc".
    set (S2 := <[Regidx Rs2 := regval_into_reg (uart_pa 0)]> S1).
    change (<[Regidx Rs2 := regval_into_reg (uart_pa 0)]> S1) with S2.
    iEval (rewrite P44) in "Hpc".
    (* the rx drain *)
    assert (HS2s1 : S2 !!! Regidx Rs1 = uart_pa 5).
    { rewrite /S2 upd_ne; [| reg_neq]. rewrite /S1 upd_eq. rewrite /S0 upd_eq.
      apply bv_eq; vm_compute; reflexivity. }
    assert (HS2s2 : S2 !!! Regidx Rs2 = uart_pa 0) by (rewrite /S2 upd_eq; reflexivity).
    assert (HS2regs : ui_regs m0 S2 (pa_stk sp0 4)).
    { destruct HregsR as (B2 & B19 & B20 & B21 & B22 & B23 & B24 & B25 & B26 & B27).
      unfold ui_regs. split_and!;
        (rewrite /S2 upd_ne; [| reg_neq]); (rewrite /S1 upd_ne; [| reg_neq]);
        (rewrite /S0 upd_ne; [| reg_neq]); assumption. }
    iDestruct (cpu_own_transport CIDR CIDT3 lvl eb pme C b ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    iDestruct (ui_ret_cont_shift CID0 CIDT3 Φ m0 av lvl eb pme C b
                 ltac:(wp_next_chain) with "Hcont") as "Hcont".
    iPoseProof (ui_rx γu γv Φ γs m0 av lvl eb pme C sp0 b Hsp0 Hlen Hlvl Hav) as "Rx".
    iApply ("Rx" $! CIDT3 S2 with "[%] [%] [%] Ht Hdinv Hpinv Hpanic Hcg Hcnt Hpc Hfr Hcont");
      [exact HS2regs | exact HS2s1 | exact HS2s2].
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  THE WHOLE FUNCTION.                                                 *)
  (* ------------------------------------------------------------------ *)
  Lemma wp_uartintr_sconf (γu : uart_names) (γv : disk_names) (γl : gname)
      (Φ : mval -> iProp Σ) (γs : list gname)
      (m : regfile) (av lvl : nat) (eb : bool) (pme : mword 64) (C : iProp Σ) (b : bool)
    : wp_uartintr_sconf_body γu γv γl Φ γs m av lvl eb pme C b.
  Proof.
    cbv beta delta [wp_uartintr_sconf_body].
    intros pcE ret_tgt Hlen Hlvl Hav.
    iIntros "Hcg Hcnt #Ht Hpc #Hdinv #Htxl #Hpinv #Hpanic Hcont".
    iAssert (ui_ret_cont Φ m av lvl eb pme C b) with "[Hcont]" as "Hcont".
    { iExact "Hcont". }
    iDestruct (is_txlock_lock with "Htxl") as "#Hlk".
    iDestruct (cpu_own_eb_agree with "Hcg Hcnt") as %Hbeq.
    pose (sp0 := (m !!! Regidx csp_rs1 : mword 64)).
    assert (Hspm : m !!! Regidx csp_rs1 = sp0) by reflexivity.
    set (spd := pa_stk sp0 4%nat).
    iPoseProof (uii2_00 with "Ht") as "Hi00". iPoseProof (uii2_02 with "Ht") as "Hi02".
    iPoseProof (uii2_04 with "Ht") as "Hi04". iPoseProof (uii2_06 with "Ht") as "Hi06".
    iPoseProof (uii2_08 with "Ht") as "Hi08". iPoseProof (uii2_0a with "Ht") as "Hi0a".
    iPoseProof (uii2_0c with "Ht") as "Hi0c". iPoseProof (uii2_10 with "Ht") as "Hi10".
    iPoseProof (uii2_14 with "Ht") as "Hi14". iPoseProof (uii2_18 with "Ht") as "Hi18".
    iPoseProof (uii2_1c with "Ht") as "Hi1c". iPoseProof (uii2_20 with "Ht") as "Hi20".
    iPoseProof (uii2_24 with "Ht") as "Hi24". iPoseProof (uii2_28 with "Ht") as "Hi28".
    iPoseProof (uii2_2c with "Ht") as "Hi2c".
    assert (P02 : add_vec_int (pcE : mword 64) 2 = mword_of_int (KernelSyms.uartintr + 0x02)) by pcw.
    assert (P04 : add_vec_int (mword_of_int (KernelSyms.uartintr + 0x02) : mword 64) 2 = mword_of_int (KernelSyms.uartintr + 0x04)) by pcw.
    assert (P06 : add_vec_int (mword_of_int (KernelSyms.uartintr + 0x04) : mword 64) 2 = mword_of_int (KernelSyms.uartintr + 0x06)) by pcw.
    assert (P08 : add_vec_int (mword_of_int (KernelSyms.uartintr + 0x06) : mword 64) 2 = mword_of_int (KernelSyms.uartintr + 0x08)) by pcw.
    assert (P0a : add_vec_int (mword_of_int (KernelSyms.uartintr + 0x08) : mword 64) 2 = mword_of_int (KernelSyms.uartintr + 0x0a)) by pcw.
    assert (P0c : add_vec_int (mword_of_int (KernelSyms.uartintr + 0x0a) : mword 64) 2 = mword_of_int (KernelSyms.uartintr + 0x0c)) by pcw.
    assert (P10 : add_vec_int (mword_of_int (KernelSyms.uartintr + 0x0c) : mword 64) 4 = mword_of_int (KernelSyms.uartintr + 0x10)) by pcw.
    assert (P14 : add_vec_int (mword_of_int (KernelSyms.uartintr + 0x10) : mword 64) 4 = mword_of_int (KernelSyms.uartintr + 0x14)) by pcw.
    assert (P18 : add_vec_int (mword_of_int (KernelSyms.uartintr + 0x14) : mword 64) 4 = mword_of_int (KernelSyms.uartintr + 0x18)) by pcw.
    assert (P1c : add_vec_int (mword_of_int (KernelSyms.uartintr + 0x18) : mword 64) 4 = mword_of_int (KernelSyms.uartintr + 0x1c)) by pcw.
    assert (P20 : ret_pc (add_vec_int (mword_of_int (KernelSyms.uartintr + 0x1c) : mword 64) 4) = mword_of_int (KernelSyms.uartintr + 0x20)) by pcw.
    assert (P24 : add_vec_int (mword_of_int (KernelSyms.uartintr + 0x20) : mword 64) 4 = mword_of_int (KernelSyms.uartintr + 0x24)) by pcw.
    assert (P28 : add_vec_int (mword_of_int (KernelSyms.uartintr + 0x24) : mword 64) 4 = mword_of_int (KernelSyms.uartintr + 0x28)) by pcw.
    assert (P2c : add_vec_int (mword_of_int (KernelSyms.uartintr + 0x28) : mword 64) 4 = mword_of_int (KernelSyms.uartintr + 0x2c)) by pcw.
    assert (P2e : add_vec_int (mword_of_int (KernelSyms.uartintr + 0x2c) : mword 64) 2 = mword_of_int (KernelSyms.uartintr + 0x2e)) by pcw.
    (* ============ PROLOGUE ============ *)
    assert (Hpush : add_vec (m !!! Regidx csp_rs1)
                      (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6)))
                    = pa_stk (m !!! Regidx csp_rs1) 4%nat).
    { unfold pa_stk, add_vec_int. apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    iApply (wp_caddi_sp_push_s_sconf Φ pcE (mword_of_int 32 : mword 6) m av 4%nat b
              ltac:(unfold uartintr_stack in Hav; lia) Hpush with "Hcg Hpc Hi00 [-]").
    iIntros (CID1 Hs1) "Hcg Hframe Hpc".
    iEval (rewrite Hspm) in "Hframe".
    set (A0 := <[Regidx csp_rs1 := regval_into_reg
        (add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))))]> m).
    change (<[Regidx csp_rs1 := regval_into_reg
        (add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))))]> m) with A0.
    assert (HcspA0 : A0 !!! Regidx csp_rs1 = spd)
      by (rewrite /A0 upd_eq Hpush Hspm; reflexivity).
    iEval (rewrite P02) in "Hpc".
    iEval (rewrite stack_own_slots; cbn [seq]) in "Hframe".
    iDestruct "Hframe" as "(F1 & F2 & F3 & F4 & _)".
    iDestruct "F1" as (v1) "H1". iDestruct "F2" as (v2) "H2".
    iDestruct "F3" as (v3) "H3". iDestruct "F4" as (v4) "H4".
    assert (Hb1 : add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000"))) = pa_stk sp0 1)
      by (apply ui_slot_bridge; pcw).
    assert (Hb2 : add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000"))) = pa_stk sp0 2)
      by (apply ui_slot_bridge; pcw).
    assert (Hb3 : add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) = pa_stk sp0 3)
      by (apply ui_slot_bridge; pcw).
    assert (Hb4 : add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000"))) = pa_stk sp0 4)
      by (apply ui_slot_bridge; pcw).
    (* the four spilled values, in the [rget] spelling the store leaf uses *)
    assert (HA0ra : forall (CID' : CpuId), rget (CID := CID') A0 Rra = m !!! Regidx Rra).
    { intros CID'; rgne. rewrite /A0 upd_ne; [reflexivity | reg_neq]. }
    assert (HA0s0 : forall (CID' : CpuId), rget (CID := CID') A0 Rs0 = m !!! Regidx Rs0).
    { intros CID'; rgne. rewrite /A0 upd_ne; [reflexivity | reg_neq]. }
    assert (HA0s1 : forall (CID' : CpuId), rget (CID := CID') A0 Rs1 = m !!! Regidx Rs1).
    { intros CID'; rgne. rewrite /A0 upd_ne; [reflexivity | reg_neq]. }
    assert (HA0s2 : forall (CID' : CpuId), rget (CID := CID') A0 Rs2 = m !!! Regidx Rs2).
    { intros CID'; rgne. rewrite /A0 upd_ne; [reflexivity | reg_neq]. }
    iApply (wp_csdsp_s_sconf Φ (mword_of_int (KernelSyms.uartintr + 0x02)) (mword_of_int 3 : mword 6) Rra
              A0 (av - 4)%nat v1 b with "Hcg Hpc Hi02 [H1] [-]").
    { iEval (rewrite HcspA0 Hb1). iExact "H1". }
    iIntros (CID2 Hs2) "Hcg Hpc H1". iEval (rewrite HcspA0 Hb1 HA0ra) in "H1".
    iEval (rewrite P04) in "Hpc".
    iApply (wp_csdsp_s_sconf Φ (mword_of_int (KernelSyms.uartintr + 0x04)) (mword_of_int 2 : mword 6) Rs0
              A0 (av - 4)%nat v2 b with "Hcg Hpc Hi04 [H2] [-]").
    { iEval (rewrite HcspA0 Hb2). iExact "H2". }
    iIntros (CID3 Hs3) "Hcg Hpc H2". iEval (rewrite HcspA0 Hb2 HA0s0) in "H2".
    iEval (rewrite P06) in "Hpc".
    iApply (wp_csdsp_s_sconf Φ (mword_of_int (KernelSyms.uartintr + 0x06)) (mword_of_int 1 : mword 6) Rs1
              A0 (av - 4)%nat v3 b with "Hcg Hpc Hi06 [H3] [-]").
    { iEval (rewrite HcspA0 Hb3). iExact "H3". }
    iIntros (CID4 Hs4) "Hcg Hpc H3". iEval (rewrite HcspA0 Hb3 HA0s1) in "H3".
    iEval (rewrite P08) in "Hpc".
    iApply (wp_csdsp_s_sconf Φ (mword_of_int (KernelSyms.uartintr + 0x08)) (mword_of_int 0 : mword 6) Rs2
              A0 (av - 4)%nat v4 b with "Hcg Hpc Hi08 [H4] [-]").
    { iEval (rewrite HcspA0 Hb4). iExact "H4". }
    iIntros (CID5 Hs5) "Hcg Hpc H4". iEval (rewrite HcspA0 Hb4 HA0s2) in "H4".
    iEval (rewrite P0a) in "Hpc".
    iAssert (ui_frame sp0 m) with "[H1 H2 H3 H4]" as "Hfr".
    { rewrite /ui_frame. iFrame "H1 H2 H3 H4". }
    (* +0x0a c.addi4spn s0,sp,32 *)
    iApply (wp_caddi4spn_s_sconf Φ (mword_of_int (KernelSyms.uartintr + 0x0a)) (Cregidx (mword_of_int 0))
              (mword_of_int 8 : mword 8) Rs0 A0 (av - 4)%nat b
              ltac:(vm_compute; reflexivity) ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi0a [-]").
    iIntros (CID6 Hs6) "Hcg Hpc".
    set (A1 := <[Regidx Rs0 := regval_into_reg
        (add_vec (A0 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8))))]> A0).
    change (<[Regidx Rs0 := regval_into_reg
        (add_vec (A0 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8))))]> A0) with A1.
    iEval (rewrite P0c) in "Hpc".
    (* ============ the ISR acknowledge ============ *)
    iApply (wp_lui_s_sconf Φ (mword_of_int (KernelSyms.uartintr + 0x0c)) Ra5 (mword_of_int 0x10000 : mword 20)
              (uart_pa 0) A1 (av - 4)%nat b ltac:(nz) ltac:(rdok)
              ltac:(apply bv_eq; vm_compute; reflexivity) with "Hcg Hpc Hi0c [-]").
    iIntros (CID7 Hs7) "Hcg Hpc".
    set (A2 := <[Regidx Ra5 := regval_into_reg (uart_pa 0)]> A1).
    change (<[Regidx Ra5 := regval_into_reg (uart_pa 0)]> A1) with A2.
    iEval (rewrite P10) in "Hpc".
    assert (HA2a5 : A2 !!! Regidx Ra5 = uart_pa 0) by (rewrite /A2 upd_eq; reflexivity).
    assert (HA2ad : forall (CID' : CpuId),
              add_vec (rget (CID := CID') A2 Ra5) (sign_extend' 64 (mword_of_int 2 : mword 12))
              = uart_pa 2).
    { intros CID'; rgne. rewrite HA2a5. apply bv_eq; vm_compute; reflexivity. }
    iApply (UAcc.wp_uart_read_free_s_sconf γu γv 2 Φ (mword_of_int (KernelSyms.uartintr + 0x10)) Ra5 Ra5
              (mword_of_int 2 : mword 12) A2 (av - 4)%nat b
              ltac:(unfold uart_size; lia) ltac:(nz) ltac:(rdok) (HA2ad _)
              with "Hcg Hpc Hi10 Hdinv [-]").
    iIntros (CID8 Hs8 bisr) "Hcg Hpc". iEval (rewrite P14) in "Hpc".
    set (A3 := <[Regidx Ra5 := regval_into_reg (lsr_ldval_of bisr)]> A2).
    change (<[Regidx Ra5 := regval_into_reg (lsr_ldval_of bisr)]> A2) with A3.
    (* ============ acquire(&tx_lock) ============ *)
    iApply (wp_auipc_s_sconf Φ (mword_of_int (KernelSyms.uartintr + 0x14)) Ra0 (mword_of_int 18 : mword 20)
              A3 (av - 4)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi14 [-]").
    iIntros (CID9 Hs9) "Hcg Hpc".
    set (A4 := <[Regidx Ra0 := regval_into_reg
        (add_vec (mword_of_int (KernelSyms.uartintr + 0x14) : mword 64) (auipc_off (mword_of_int 18 : mword 20)))]> A3).
    change (<[Regidx Ra0 := regval_into_reg
        (add_vec (mword_of_int (KernelSyms.uartintr + 0x14) : mword 64) (auipc_off (mword_of_int 18 : mword 20)))]> A3) with A4.
    iEval (rewrite P18) in "Hpc".
    assert (HA4rg : forall (CID' : CpuId), rget (CID := CID') A4 Ra0 = A4 !!! Regidx Ra0)
      by (intros CID'; rgne; reflexivity).
    iApply (wp_addi4_s_sconf Φ (mword_of_int (KernelSyms.uartintr + 0x18)) Ra0 Ra0 (mword_of_int 0x92e : mword 12)
              A4 (av - 4)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi18 [-]").
    iIntros (CID10 Hs10) "Hcg Hpc".
    iEval (rewrite HA4rg) in "Hcg".
    set (A5 := <[Regidx Ra0 := regval_into_reg
        (add_vec (A4 !!! Regidx Ra0) (sign_extend' 64 (mword_of_int 0x92e : mword 12)))]> A4).
    change (<[Regidx Ra0 := regval_into_reg
        (add_vec (A4 !!! Regidx Ra0) (sign_extend' 64 (mword_of_int 0x92e : mword 12)))]> A4) with A5.
    iEval (rewrite P1c) in "Hpc".
    iApply (wp_jal_s_sconf Φ (mword_of_int (KernelSyms.uartintr + 0x1c)) Rra (mword_of_int 542 : mword 21)
              A5 (av - 4)%nat b ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi1c [-]").
    iIntros (CID11 Hs11) "Hcg Hpc".
    set (A6 := <[Regidx Rra := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.uartintr + 0x1c) : mword 64) 4)]> A5).
    change (<[Regidx Rra := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.uartintr + 0x1c) : mword 64) 4)]> A5) with A6.
    assert (Hjacq : add_vec (mword_of_int (KernelSyms.uartintr + 0x1c) : mword 64)
                      (sign_extend' 64 (mword_of_int 542 : mword 21)) = mword_of_int KernelSyms.acquire) by pcw.
    iEval (rewrite Hjacq) in "Hpc".
    assert (HA6a0 : A6 !!! Regidx Ra0 = a_tx_lock).
    { rewrite /A6 upd_ne; [| reg_neq]. rewrite /A5 upd_eq. rewrite /A4 upd_eq.
      rewrite /a_tx_lock. pcw. }
    assert (HA6ra : A6 !!! Regidx Rra = add_vec_int (mword_of_int (KernelSyms.uartintr + 0x1c) : mword 64) 4)
      by (rewrite /A6 upd_eq; reflexivity).
    assert (HA6regs : ui_regs m A6 spd).
    { unfold ui_regs. split_and!;
        try (rewrite /A6 upd_ne; [| reg_neq]; rewrite /A5 upd_ne; [| reg_neq];
             rewrite /A4 upd_ne; [| reg_neq]; rewrite /A3 upd_ne; [| reg_neq];
             rewrite /A2 upd_ne; [| reg_neq]; rewrite /A1 upd_ne; [| reg_neq];
             rewrite /A0 upd_ne; [| reg_neq]; reflexivity).
      exact (eq_trans (eq_sym (eq_refl _)) HcspA0). }
    iDestruct (cpu_own_transport CID CID11 lvl eb pme C b ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    iApply (Acquire.wp_acquire_sconf Φ γl "uart"%string (tx_res γu) A6
              lvl eb pme C (av - 4)%nat b ltac:(lia)
              ltac:(unfold uartintr_stack in Hav; lia)
              with "Hcg Hcnt Ht Hpc [Hlk] Hpanic [-]").
    { iEval (rewrite HA6a0). iExact "Hlk". }
    iIntros (CIDA HsA ms MA) "%Hms Hcg Hpc %HcsA Htok HR Hcnt Hpay".
    iEval (rewrite HA6ra P20) in "Hpc".
    assert (HregsA : ui_regs m MA spd) by (apply (ui_regs_cs m A6 MA); [exact HcsA | exact HA6regs]).
    pose proof HregsA as HregsA'.
    destruct HregsA' as (Wsp & W19 & W20 & W21 & W22 & W23 & W24 & W25 & W26 & W27).
    (* the caller's obligation now travels with the [false] stretch: re-anchor
       it once, at the hart acquire resumed on. *)
    iDestruct (ui_ret_cont_shift CID CIDA Φ m av lvl eb pme C b
                 ltac:(wp_next_chain) with "Hcont") as "Hcont".
    (* ============ the LSR read, under the lock (interrupts OFF) ============ *)
    iDestruct "HR" as (bcell l) "(Hcell & Hown & Hwand)".
    iApply (wp_lui_s_sconf Φ (mword_of_int (KernelSyms.uartintr + 0x20)) Ra5 (mword_of_int 0x10000 : mword 20)
              (uart_pa 0) MA (av - 4)%nat false ltac:(nz) ltac:(rdok)
              ltac:(apply bv_eq; vm_compute; reflexivity) with "Hcg Hpc Hi20 [-]").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    set (B0 := <[Regidx Ra5 := regval_into_reg (uart_pa 0)]> MA).
    change (<[Regidx Ra5 := regval_into_reg (uart_pa 0)]> MA) with B0.
    iEval (rewrite P24) in "Hpc".
    assert (HB0a5 : B0 !!! Regidx Ra5 = uart_pa 0) by (rewrite /B0 upd_eq; reflexivity).
    assert (HB0ad : forall (CID' : CpuId),
              add_vec (rget (CID := CID') B0 Ra5) (sign_extend' 64 (mword_of_int 5 : mword 12))
              = uart_pa 5).
    { intros CID'; rgne. rewrite HB0a5. apply bv_eq; vm_compute; reflexivity. }
    iApply (UAcc.wp_uart_lsr_read_ea_s_sconf γu γv Φ (mword_of_int (KernelSyms.uartintr + 0x24)) Ra5 Ra5
              (mword_of_int 5 : mword 12) B0 (av - 4)%nat l false ltac:(nz) ltac:(rdok)
              (HB0ad _)
              with "Hcg Hpc Hi24 Hdinv Hown").
    iApply wp_next_off_intro.
    iIntros (blsr) "Hcg Hpc Hown Hlbw". iEval (rewrite P28) in "Hpc".
    set (B1 := <[Regidx Ra5 := regval_into_reg (lsr_ldval_of blsr)]> B0).
    change (<[Regidx Ra5 := regval_into_reg (lsr_ldval_of blsr)]> B0) with B1.
    (* +0x28 andi a5,a5,32 *)
    assert (HB1a5 : forall (CID' : CpuId), rget (CID := CID') B1 Ra5 = lsr_ldval_of blsr).
    { intros CID'; rgne. rewrite /B1 upd_eq. reflexivity. }
    iApply (wp_andi_s_sconf Φ (mword_of_int (KernelSyms.uartintr + 0x28)) Ra5 Ra5 (mword_of_int 32 : mword 12)
              (and_vec (lsr_ldval_of blsr) (sign_extend' 64 (mword_of_int 32 : mword 12)))
              B1 (av - 4)%nat false ltac:(nz) ltac:(rdok)
              ltac:(rewrite HB1a5; reflexivity) with "Hcg Hpc Hi28 [-]").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    iEval (rewrite upd_upd) in "Hcg".
    iEval (rewrite P2c) in "Hpc".
    set (B2 := <[Regidx Ra5 := regval_into_reg
        (and_vec (lsr_ldval_of blsr) (sign_extend' 64 (mword_of_int 32 : mword 12)))]> B0).
    change (<[Regidx Ra5 := regval_into_reg
        (and_vec (lsr_ldval_of blsr) (sign_extend' 64 (mword_of_int 32 : mword 12)))]> B0) with B2.
    assert (HB2a5 : forall (CID' : CpuId), rget (CID := CID') B2 Ra5
                    = and_vec (lsr_ldval_of blsr) (sign_extend' 64 (mword_of_int 32 : mword 12))).
    { intros CID'; rgne. rewrite /B2 upd_eq. reflexivity. }
    assert (HB2regs : ui_regs m B2 spd).
    { unfold ui_regs. split_and!;
        (rewrite /B2 upd_ne; [| reg_neq]); (rewrite /B0 upd_ne; [| reg_neq]); assumption. }
    (* ============ +0x2c c.bnez a5 : the THRE test ============ *)
    destruct (lsr_thre_clear blsr) eqn:Hthre.
    - (* the FIFO is still busy: fall through to the release *)
      iApply (wp_cbnez_fall_s_sconf Φ (mword_of_int (KernelSyms.uartintr + 0x2c)) (mword_of_int 21 : mword 8)
                (Cregidx (mword_of_int 7)) Ra5 B2 (av - 4)%nat false UG.ug_cr7 ltac:(nz)
                ltac:(rewrite HB2a5; unfold neq_vec; rewrite -/(lsr_thre_clear blsr) Hthre; reflexivity)
                with "Hcg Hpc Hi2c [-]").
      iApply wp_next_off_intro.
      iIntros "Hcg Hpc". iEval (rewrite P2e) in "Hpc".
      iApply (ui_after_tx γl γu γv Φ γs m B2 av lvl eb pme C sp0 b
                HB2regs Hspm Hlen Hlvl Hav Hbeq
                with "Ht Hdinv Htxl Hpinv Hpanic Hcg Hcnt Hpay Hpc Htok [Hcell Hown Hwand] Hfr Hcont").
      iExists bcell, l. iFrame "Hcell Hown Hwand".
    - (* THRE: clear tx_busy and wake the writers *)
      iDestruct ("Hlbw" with "[%]") as "#Hlb"; [reflexivity|].
      assert (Jtx : add_vec (mword_of_int (KernelSyms.uartintr + 0x2c) : mword 64)
                      (sign_extend' 64 (sign_extend' 13 (concat_vec (mword_of_int 21 : mword 8) ('b"0"))))
                    = mword_of_int (KernelSyms.uartintr + 0x56)) by pcw.
      iApply (wp_cbnez_taken_s_sconf Φ (mword_of_int (KernelSyms.uartintr + 0x2c)) (mword_of_int 21 : mword 8)
                (Cregidx (mword_of_int 7)) Ra5 B2 (av - 4)%nat false UG.ug_cr7 ltac:(nz)
                ltac:(rewrite HB2a5; unfold neq_vec; rewrite -/(lsr_thre_clear blsr) Hthre; reflexivity)
                ltac:(rewrite Jtx; vm_compute; reflexivity)
                with "Hcg Hpc Hi2c [-]").
      iNext. iApply wp_next_off_intro.
      iIntros "Hcg Hpc". iEval (rewrite Jtx) in "Hpc".
      iPoseProof (uii2_56 with "Ht") as "Hi56". iPoseProof (uii2_5a with "Ht") as "Hi5a".
      iPoseProof (uii2_5e with "Ht") as "Hi5e". iPoseProof (uii2_62 with "Ht") as "Hi62".
      iPoseProof (uii2_66 with "Ht") as "Hi66". iPoseProof (uii2_6a with "Ht") as "Hi6a".
      assert (P5a : add_vec_int (mword_of_int (KernelSyms.uartintr + 0x56) : mword 64) 4 = mword_of_int (KernelSyms.uartintr + 0x5a)) by pcw.
      assert (P5e : add_vec_int (mword_of_int (KernelSyms.uartintr + 0x5a) : mword 64) 4 = mword_of_int (KernelSyms.uartintr + 0x5e)) by pcw.
      assert (P62 : add_vec_int (mword_of_int (KernelSyms.uartintr + 0x5e) : mword 64) 4 = mword_of_int (KernelSyms.uartintr + 0x62)) by pcw.
      assert (P66 : add_vec_int (mword_of_int (KernelSyms.uartintr + 0x62) : mword 64) 4 = mword_of_int (KernelSyms.uartintr + 0x66)) by pcw.
      assert (P6a : ret_pc (add_vec_int (mword_of_int (KernelSyms.uartintr + 0x66) : mword 64) 4) = mword_of_int (KernelSyms.uartintr + 0x6a)) by pcw.
      (* +0x56 auipc a5,0xa / +0x5a sw zero,-2040(a5) : tx_busy = 0 *)
      iApply (wp_auipc_s_sconf Φ (mword_of_int (KernelSyms.uartintr + 0x56)) Ra5 (mword_of_int 10 : mword 20)
                B2 (av - 4)%nat false ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi56 [-]").
      iApply wp_next_off_intro.
      iIntros "Hcg Hpc".
      set (T0 := <[Regidx Ra5 := regval_into_reg
          (add_vec (mword_of_int (KernelSyms.uartintr + 0x56) : mword 64) (auipc_off (mword_of_int 10 : mword 20)))]> B2).
      change (<[Regidx Ra5 := regval_into_reg
          (add_vec (mword_of_int (KernelSyms.uartintr + 0x56) : mword 64) (auipc_off (mword_of_int 10 : mword 20)))]> B2) with T0.
      iEval (rewrite P5a) in "Hpc".
      assert (Hbusya : forall (CID' : CpuId),
                add_vec (rget (CID := CID') T0 Ra5) (sign_extend' 64 (mword_of_int 0x808 : mword 12))
                = a_tx_busy).
      { intros CID'; rgne. rewrite /T0 upd_eq. rewrite /a_tx_busy. pcw. }
      iApply (wp_sw_zero_s_sconf Φ (mword_of_int (KernelSyms.uartintr + 0x5a)) Ra5 (mword_of_int 0x808 : mword 12)
                T0 (av - 4)%nat bcell false with "Hcg Hpc Hi5a [Hcell] [-]").
      { iEval (rewrite Hbusya). iExact "Hcell". }
      iApply wp_next_off_intro.
      iIntros "Hcg Hpc Hcell". iEval (rewrite Hbusya) in "Hcell".
      (* the invariant's other side: tx_busy = 0 now CERTIFIES the drained FIFO *)
      iDestruct (tx_res_idle γu (mword_of_int 0 : mword 32) l with "Hcell Hown Hlb") as "HR".
      iEval (rewrite P5e) in "Hpc".
      (* +0x5e auipc a0,0x9 / +0x62 addi a0,a0,2044 : a0 := &tx_chan *)
      iApply (wp_auipc_s_sconf Φ (mword_of_int (KernelSyms.uartintr + 0x5e)) Ra0 (mword_of_int 9 : mword 20)
                T0 (av - 4)%nat false ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi5e [-]").
      iApply wp_next_off_intro.
      iIntros "Hcg Hpc".
      set (T1 := <[Regidx Ra0 := regval_into_reg
          (add_vec (mword_of_int (KernelSyms.uartintr + 0x5e) : mword 64) (auipc_off (mword_of_int 9 : mword 20)))]> T0).
      change (<[Regidx Ra0 := regval_into_reg
          (add_vec (mword_of_int (KernelSyms.uartintr + 0x5e) : mword 64) (auipc_off (mword_of_int 9 : mword 20)))]> T0) with T1.
      iEval (rewrite P62) in "Hpc".
      assert (HT1rg : forall (CID' : CpuId), rget (CID := CID') T1 Ra0 = T1 !!! Regidx Ra0)
        by (intros CID'; rgne; reflexivity).
      iApply (wp_addi4_s_sconf Φ (mword_of_int (KernelSyms.uartintr + 0x62)) Ra0 Ra0 (mword_of_int 0x7fc : mword 12)
                T1 (av - 4)%nat false ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi62 [-]").
      iApply wp_next_off_intro.
      iIntros "Hcg Hpc".
      iEval (rewrite HT1rg) in "Hcg".
      set (T2 := <[Regidx Ra0 := regval_into_reg
          (add_vec (T1 !!! Regidx Ra0) (sign_extend' 64 (mword_of_int 0x7fc : mword 12)))]> T1).
      change (<[Regidx Ra0 := regval_into_reg
          (add_vec (T1 !!! Regidx Ra0) (sign_extend' 64 (mword_of_int 0x7fc : mword 12)))]> T1) with T2.
      iEval (rewrite P66) in "Hpc".
      (* +0x66 jal ra,wakeup *)
      iApply (wp_jal_s_sconf Φ (mword_of_int (KernelSyms.uartintr + 0x66)) Rra (mword_of_int 5416 : mword 21)
                T2 (av - 4)%nat false ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi66 [-]").
      iApply wp_next_off_intro.
      iIntros "Hcg Hpc".
      set (T3 := <[Regidx Rra := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.uartintr + 0x66) : mword 64) 4)]> T2).
      change (<[Regidx Rra := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.uartintr + 0x66) : mword 64) 4)]> T2) with T3.
      assert (Hjwk : add_vec (mword_of_int (KernelSyms.uartintr + 0x66) : mword 64)
                       (sign_extend' 64 (mword_of_int 5416 : mword 21)) = mword_of_int KernelSyms.wakeup) by pcw.
      iEval (rewrite Hjwk) in "Hpc".
      assert (HT3ra : T3 !!! Regidx Rra = add_vec_int (mword_of_int (KernelSyms.uartintr + 0x66) : mword 64) 4)
        by (rewrite /T3 upd_eq; reflexivity).
      assert (HcsB2T3 : callee_saved B2 T3).
      { rewrite /T3 /T2 /T1 /T0.
        apply callee_saved_insert_r; [vm_compute; reflexivity|].
        apply callee_saved_insert_r; [vm_compute; reflexivity|].
        apply callee_saved_insert_r; [vm_compute; reflexivity|].
        apply callee_saved_insert_r; [vm_compute; reflexivity|].
        apply callee_saved_refl. }
      iApply (Wakeup.wp_wakeup_sconf Φ T3 γs (mycpu_ret (rget (CID := CIDA) T3 Rtp')) pme
                (S lvl) (av - 4)%nat eb C false
                ltac:(unfold uartintr_stack in Hav; lia)
                ltac:(intro r; apply rf_to_gmap_dom)
                Hlen
                eq_refl
                ltac:(rewrite rget_tp; exact (mycpu_ret_nonzero _ (tp_ok_cid_of _)))
                ltac:(lia)
                with "Hcg Hcnt Ht Hpc Hpanic Hpinv [-]").
      iApply wp_next_off_intro.
      iIntros (Mw) "[%Hcsw %Hdomw] Hcg Hcnt Ht2 Hpc".
      iEval (rewrite HT3ra P6a) in "Hpc".
      assert (HregsW : ui_regs m Mw spd).
      { apply (ui_regs_cs m T3 Mw); [exact Hcsw|].
        apply (ui_regs_cs m B2 T3); [exact HcsB2T3 | exact HB2regs]. }
      (* +0x6a c.j -> the release *)
      assert (Jrel : add_vec (mword_of_int (KernelSyms.uartintr + 0x6a) : mword 64)
                       (sign_extend' 64 (sign_extend' 21 (concat_vec (mword_of_int 2018 : mword 11) ('b"0"))))
                     = mword_of_int (KernelSyms.uartintr + 0x2e)) by pcw.
      iApply (wp_cj_s_sconf Φ (mword_of_int (KernelSyms.uartintr + 0x6a))
                (sign_extend' 21 (concat_vec (mword_of_int 2018 : mword 11) ('b"0")))
                Mw (av - 4)%nat false ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi6a [-]").
      iApply wp_next_off_intro.
      iNext. iIntros "Hcg Hpc". iEval (rewrite Jrel) in "Hpc".
      iApply (ui_after_tx γl γu γv Φ γs m Mw av lvl eb pme C sp0 b
                HregsW Hspm Hlen Hlvl Hav Hbeq
                with "Ht Hdinv Htxl Hpinv Hpanic Hcg Hcnt Hpay Hpc Htok HR Hfr Hcont").
  Qed.

End ProofUartintr.
End UartintrProof.
