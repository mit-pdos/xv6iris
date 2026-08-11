(* WpUartgetc.v -- uartgetc(), the one xv6 UART function that has no symbol.

     static int uartgetc(void) {
       if (ReadReg(LSR) & LSR_RX_READY) return ReadReg(RHR);
       else return -1;
     }

   It is [static] and called once, so gcc INLINES it: there is no [uartgetc]
   entry in KernelSyms.v, and the coverage report -- which is symbol-driven --
   cannot count it.  What exists in the image is its BODY, four instructions
   inside uartintr (+0x44 .. +0x4c), with the C's [c != -1] test fused into
   the caller's loop branch: the "-1" is never materialized, the [beqz] on the
   rx-ready bit IS it.

   So this file states uartgetc the only way the compiled kernel admits: as a
   block lemma parameterized by its four instruction addresses and its two
   exits ("no input", at the branch target; "a byte", at the instruction after
   the RHR read, with the byte in a0).  It is the pc-parameterized-block
   recipe from claude-notes/durable-notes.md, used here not because the block
   occurs twice but because it belongs to a function that no longer has an
   address of its own.

   Both accesses are ghost-free: no UART read moves the accepted trace, the
   transmitted prefix or DLAB ([DevModel.uart_read_stable]), so uartgetc needs
   neither the transmitter token nor tx_lock -- which is exactly why xv6 can
   run the rx drain outside the critical section. *)
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
Require Import RegFile.
Require Import SmodeCore.
Require Import DevModel DiskPtsto WpUart.
Require Import IntrDefs.
Require Import HartTp WpNext.
Require Import SpecUart.
Require Import WpSconfAlu WpSconfBtype.
Require Import WpSconfUartAccess.
Local Open Scope Z_scope.

Module UartgetcProof (Uart : UART).
Module UAcc := UartAccessProof Uart.

Section WpUartgetc.
  Context `{!riscvGS Σ}.
  Context `{!sieG Σ}.
  Context `{!uartGhostG Σ, !diskGhostG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.
  Context {p : mword 64}.

  Notation Ra0 := (mword_of_int 10 : mword 5).
  Notation Ra5 := (mword_of_int 15 : mword 5).

  (* what the [c.andi a5,a5,1] leaves in a5, and the [beqz] that reads it *)
  Definition rx_masked (b : bv 8) : mword 64 :=
    and_vec (lsr_ldval_of b) (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6))).
  Definition rx_empty (b : bv 8) : bool := eq_vec (rx_masked b) (zero_reg : mword 64).

  (* a5's compressed-register index *)
  Lemma ug_cr7 : creg2reg_idx (Cregidx (mword_of_int 7)) = Regidx Ra5.
  Proof. vm_compute. reflexivity. Qed.

  (* -------------------------------------------------------------------- *)
  (*  uartgetc, inlined.                                                    *)
  (* -------------------------------------------------------------------- *)
  (* THE SIDE CONDITION ON [rs_lsr] ARRIVES BY INSTANCE RESOLUTION.  This
     block is a multi-instruction leaf over [WpSconfUartAccess]'s converted
     UART leaves, and it applies them at two VARIABLE register indices.  For
     [rs_rhr] the disequality is already an ordinary premise below ([rs_rhr <>
     Rtp], on the raw [mword 5]) -- and [IntrDefs.srcok_solve]'s injection arm
     is exactly what turns that spelling into the class, so that premise stays
     put and nothing about it moves.  [rs_lsr] carried NO such fact: its only
     premise was the value fact [rget m rs_lsr = uart_pa 5], which says nothing
     about tp.  Since [wp_uart_read_free_s_sconf] now takes [SrcOk rs1], an
     application at [rs_lsr] would have had NOTHING to resolve against -- and
     the resulting failure is the silent one, an instance SHELVED inside
     [iApply] that only surfaces at [Qed] as "Attempt to save an incomplete
     proof".  So the class is stated here too, as an implicit argument, which
     costs no positional slot: the block's two call sites (ProofUartintr.v)
     pass concrete registers and do not move.

     WHY IT IS TRUE AND NOT MERELY CONVENIENT: [rs_lsr] holds the UART LSR
     address, so it is a data pointer, not the thread pointer; and the value
     premise reads it as [rget m rs_lsr] at the ENTRY hart while the poll's
     load happens after a [wp_next] that may have migrated, so the leaf needs
     the read to be hart-independent for exactly the same reason [rs_rhr] does.
     The asymmetry in the ORIGINAL statement (a premise for one base, nothing
     for the other) was the gap. *)
  Lemma wp_uartgetc_inline (γd : uart_names) (γv : disk_names) (m : regfile) (n : nat)
      (rs_lsr rs_rhr : mword 5) `{!SrcOk rs_lsr} (imm8 : mword 8)
      (pcL pcA pcB pcR pcK pcNo : mword 64) (b : bool) :
    (* the two bases: the LSR and the RHR, each already in a register --
       [rs_lsr]/[rs_rhr] are register-index VARIABLES, so the read has to go
       through [rget] (either could in principle be tp). *)
    rget m rs_lsr = uart_pa 5 ->
    rget m rs_rhr = uart_pa 0 ->
    (* the RHR base must survive the [andi] that clobbers a5 *)
    rs_rhr <> Ra5 ->
    (* the RHR base is read again after the block's possible migrations
       (the [c.beqz]/poll may trap with interrupts enabled), so its value
       has to survive a hart change; that only holds away from tp -- a plain
       register-file value is hart-independent, [rget] is not, at [Rtp]. *)
    rs_rhr <> Rtp ->
    (* the block's own geometry, as literals *)
    add_vec_int pcL 4 = pcA ->
    add_vec_int pcA 2 = pcB ->
    add_vec_int pcB 2 = pcR ->
    add_vec_int pcR 4 = pcK ->
    add_vec pcB (sign_extend' 64 (sign_extend' 13 (concat_vec imm8 ('b"0")))) = pcNo ->
    eq_vec (access_vec_dec pcNo 0) ('b"0") = true ->
    sie_cap_gpr m n b p -∗
    pc_is pcL -∗
    instr pcL false (LOAD (mword_of_int 0 : mword 12, Regidx rs_lsr, Regidx Ra5, true, 1)) -∗
    instr pcA true (ITYPE (sign_extend' 12 (mword_of_int 1 : mword 6), Regidx Ra5, Regidx Ra5, ANDI)) -∗
    instr pcB true (BTYPE (sign_extend' 13 (concat_vec imm8 ('b"0")), zreg,
                           creg2reg_idx (Cregidx (mword_of_int 7)), BEQ)) -∗
    instr pcR false (LOAD (mword_of_int 0 : mword 12, Regidx rs_rhr, Regidx Ra0, true, 1)) -∗
    dev_inv γd γv -∗
    wp_next b p (fun (CID : CpuId) =>
      (* the two returns, as a CONJUNCTION: exactly one is taken, and they must
         share whatever the caller is carrying across the call *)
      ( (* "return -1": the rx FIFO was empty *)
        ( ∀ bt : bv 8,
            ⌜ rx_empty bt = true ⌝ -∗
            sie_cap_gpr (<[Regidx Ra5 := regval_into_reg (rx_masked bt)]> m) n b p -∗
            pc_is pcNo -∗
            WP (Loop : expr riscv_lang))
        ∧ (* "return the byte": it is in a0, zero-extended *)
        ( ∀ bt c : bv 8,
            ⌜ rx_empty bt = false ⌝ -∗
            sie_cap_gpr (<[Regidx Ra0 := regval_into_reg (lsr_ldval_of c)]>
                           (<[Regidx Ra5 := regval_into_reg (rx_masked bt)]> m)) n b p -∗
            pc_is pcK -∗
            WP (Loop : expr riscv_lang)) )) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros (Hlsr Hrhr Hne Hrtp HA HB HR HK HNo Hal) "Hcg Hpc HiL HiA HiB HiR #Hdinv Hk".
    (* the class, consumed at [rs_lsr]: the LSR address is the same word at
       every hart, so the premise stated at the entry hart still holds at the
       hart the poll's [wp_next] lands on.  Also the wiring check -- attach the
       class to any other parameter and this line stops typechecking. *)
    assert (Hlsr_all : forall hh : CpuId, rget (CID := hh) m rs_lsr = uart_pa 5)
      by (intros hh; rewrite (src_ok_rget_indep m rs_lsr hh CID); exact Hlsr).
    (* Ra5 (x15) is never tp (x4): the one register-index fact the a5-side
       reasoning below needs to peel [rget] back to a raw map lookup. *)
    assert (HR5tp : Regidx Ra5 <> Regidx Rtp)
      by (vm_compute; discriminate).
    (* the RHR base, reduced to a HART-INDEPENDENT raw map fact once and for
       all: [rget] at a non-tp index is the plain lookup ([rget_ne]), so this
       survives every later hart change unlike [Hrhr] itself (whose [rget] is
       pinned at the ENTRY hart). *)
    assert (Hrhr0 : m !!! Regidx rs_rhr = uart_pa 0).
    { rewrite -(rget_ne m rs_rhr ltac:(congruence)). exact Hrhr. }
    (* --- the rx-ready poll: [lbu a5,0(s1)] --- *)
    iApply (UAcc.wp_uart_read_free_s_sconf γd γv 5 pcL Ra5 rs_lsr (mword_of_int 0 : mword 12)
              m n b ltac:(unfold uart_size; lia) ltac:(vm_compute; discriminate)
              ltac:(rdok)
              ltac:(rewrite Hlsr; apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc HiL Hdinv [-]").
    iIntros (CID1 Hs1 bt) "Hcg Hpc". iEval (rewrite HA) in "Hpc".
    (* --- [c.andi a5,a5,1] --- *)
    iApply (wp_candi_s_sconf pcA Ra5 (mword_of_int 1 : mword 6)
              (<[Regidx Ra5 := regval_into_reg (lsr_ldval_of bt)]> m) n b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc HiA [-]").
    iIntros (CID2 Hs2) "Hcg Hpc". iEval (rewrite HB) in "Hpc".
    iEval (rewrite (rget_ne _ Ra5 HR5tp) upd_eq upd_upd) in "Hcg".
    change (and_vec (lsr_ldval_of bt) (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6))))
      with (rx_masked bt) in *.
    (* --- [c.beqz a5]: the C's [c == -1] --- *)
    (* the hart is PINNED explicitly ([CID:=CID2]) at every call below whose
       ltac: argument mentions [rget]: those goals elaborate before [iApply]
       unifies the conclusion against "Hcg", so an unpinned hart would leave
       the premise at a fresh metavariable instead of [CID2] (durable-notes /
       the porting guide's "Set Printing Implicit" trap). *)
    assert (Hlk : rget (CID:=CID2) (<[Regidx Ra5 := regval_into_reg (rx_masked bt)]> m) Ra5
                  = rx_masked bt).
    { rewrite (rget_ne _ Ra5 HR5tp) upd_eq. reflexivity. }
    destruct (rx_empty bt) eqn:Hempty.
    - (* no input *)
      iApply (wp_cbeqz_taken_s_sconf (CID:=CID2) pcB imm8 (Cregidx (mword_of_int 7)) Ra5
                (<[Regidx Ra5 := regval_into_reg (rx_masked bt)]> m) n b
                ug_cr7 ltac:(vm_compute; discriminate)
                ltac:(rewrite Hlk; exact Hempty)
                ltac:(rewrite HNo; exact Hal)
                with "Hcg Hpc HiB [-]").
      iNext. iIntros (CID3 Hs3) "Hcg Hpc". iEval (rewrite HNo) in "Hpc".
      iSpecialize ("Hk" $! CID3 with "[%]"); [wp_next_chain|].
      iDestruct "Hk" as "[Hno _]".
      iApply ("Hno" $! bt with "[%] Hcg Hpc"). exact Hempty.
    - (* a byte is waiting: [lbu a0,0(s2)] pops it *)
      iApply (wp_cbeqz_fall_s_sconf (CID:=CID2) pcB imm8 (Cregidx (mword_of_int 7)) Ra5
                (<[Regidx Ra5 := regval_into_reg (rx_masked bt)]> m) n b
                ug_cr7 ltac:(vm_compute; discriminate)
                ltac:(rewrite Hlk; exact Hempty)
                with "Hcg Hpc HiB [-]").
      iIntros (CID3 Hs3) "Hcg Hpc". iEval (rewrite HR) in "Hpc".
      iApply (UAcc.wp_uart_read_free_s_sconf (CID:=CID3) γd γv 0 pcR Ra0 rs_rhr (mword_of_int 0 : mword 12)
                (<[Regidx Ra5 := regval_into_reg (rx_masked bt)]> m) n b
                ltac:(unfold uart_size; lia) ltac:(vm_compute; discriminate)
                ltac:(rdok)
                ltac:(rewrite (rget_ne _ rs_rhr ltac:(congruence))
                        (upd_ne m (Regidx Ra5) (Regidx rs_rhr)
                           (regval_into_reg (rx_masked bt)) ltac:(congruence)) Hrhr0;
                      apply bv_eq; vm_compute; reflexivity)
                with "Hcg Hpc HiR Hdinv [-]").
      iIntros (CID4 Hs4 c) "Hcg Hpc". iEval (rewrite HK) in "Hpc".
      iSpecialize ("Hk" $! CID4 with "[%]"); [wp_next_chain|].
      iDestruct "Hk" as "[_ Hyes]".
      iApply ("Hyes" $! bt c with "[%] Hcg Hpc"). exact Hempty.
  Qed.

  (* ------------------------------------------------------------------- *)
  (* [SrcOk] SMOKE TEST -- see IntrDefs.v's checker block.  The positive   *)
  (* pair is the two shapes this block actually needs: a CONCRETE register *)
  (* (arm 1, [vm_compute]) for the a0/a5 it hard-codes, and the RAW-mword  *)
  (* disequality (arm 4) which is how [rs_rhr <> Rtp] above is spelled --   *)
  (* that arm was added for exactly this premise, so if it ever regresses  *)
  (* the failure lands HERE and not as a shelved [Qed] in ProofUartintr.   *)
  (* ------------------------------------------------------------------- *)
  Definition ug_srcok_pos_a5 : SrcOk Ra5 := _.
  Definition ug_srcok_pos_raw (rs : mword 5) (H : rs <> Rtp) : SrcOk rs := _.
  Fail Definition ug_srcok_neg : SrcOk Rtp := _.

End WpUartgetc.
End UartgetcProof.
