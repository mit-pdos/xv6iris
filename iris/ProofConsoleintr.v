(* ProofConsoleintr.v -- the whole-function WP for xv6's consoleintr().

     void consoleintr(int c)
     {
       acquire(&cons.lock);
       switch (c) {
       case C('U'):                       // kill line
         while (cons.e != cons.w &&
                cons.buf[(cons.e - 1) % INPUT_BUF_SIZE] != '\n') {
           cons.e--;  consputc(BACKSPACE);
         }
         break;
       case C('H'): case '\x7f':          // backspace / delete
         if (cons.e != cons.w) { cons.e--; consputc(BACKSPACE); }
         break;
       default:
         if (c != 0 && cons.e - cons.r < INPUT_BUF_SIZE) {
           c = (c == '\r') ? '\n' : c;
           consputc(c);
           cons.buf[cons.e++ % INPUT_BUF_SIZE] = c;
           if (c == '\n' || c == C('D') || cons.e - cons.r == INPUT_BUF_SIZE) {
             cons.w = cons.e;  wakeup(&cons.r);
           }
         }
         break;
       }
       release(&cons.lock);
     }

   182 instructions / 364 bytes; the contract is SpecConsoleintr.v, the decode
   layer CodeConsoleintr.v, the console's own state ConsoleInv.v.

   THE FRAME IS SIX SLOTS ([c.addi16sp sp,-48]).  ra/s0/s1 are saved
   unconditionally into slots 1..3; s2 and s3 -- the two constants the
   kill-line loop hoists ('\n' and BACKSPACE) -- are SHRINK-WRAPPED into slots
   4 and 5 by the pair at +0x092, on the one arm that has them.  Slot 6 is
   never touched.

   ONE EXIT (+0x104: release, then the epilogue) and NINE jumps to it, so the
   whole function is four continuations: [ct_exit_prop], the wake-up tail
   [ct_wake_prop] (+0x156), the kill-line loop [ct_kill_prop] (+0x0b8), and
   the dispatch that reaches them.

   THE KILL-LINE LOOP IS AN iLöb, NOT A FUEL INDUCTION, and that is where the
   flat [ConsoleInv.cons_res] shows: with no relation between [cons.e] and
   [cons.w], the loop's [cons.e--] bounds nothing.  It does not need to --
   the back edge is the TAKEN arm of the [bne] at +0x0da, and
   [wp_bne_taken_s_sconf] hands out a [▷ wp_next], which is exactly what the
   Löb IH sits under.  Nothing is returned, so no count has to survive. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes.
Require Import RiscvLang RiscvPtsto RiscvExtras RiscvExec.
Require Import RegFile.
Require Import InstrBytes WpMmodeLeafBase.
Require Import SmodeCore.
Require Import CalleeSaved KernelText.
Require Import StackOwn StackBytes.
Require Import RiscvTryStep.
Require Import ExecCommon WpGpr.
Require Import VcGen WpSconfAlu WpSconfMem WpSconfCtl WpSconfBtype.
Require Import W32Arith.
Require Import IntrDefs WpSmodeIntr.
Require Import HartTp WpNext.
Require Import WpLock ProcGeom CpuOwn KernelRvcDecode.
Require Import FdSlots.
Require Import DiskPtsto WpUart UartTxInv.
Require Import ConsoleInv.
Require Import PanicStub SchedCtx.
Require Import SpecAcquire SpecRelease SpecConsputc SpecWakeup.
Require Import CodeConsoleintr.
Require Import SpecConsoleintr.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.

Import Defs.
Local Open Scope Z_scope.

Notation CT := KernelSyms.consoleintr (only parsing).

(* THE FRAME IS SIX SLOTS.  A [c.sdsp]/[c.ldsp] displacement off the pushed sp
   names slot [6 - uimm] counted down from the ENTRY sp. *)
Lemma ct_slot_bridge (X : mword 64) (o : mword 64) (k : nat) :
  add_vec (mword_of_int (- (8 * Z.of_nat 6%nat))) o = mword_of_int (- (8 * Z.of_nat k)) ->
  add_vec (pa_stk X 6%nat) o = pa_stk X k.
Proof.
  intro H. unfold pa_stk, add_vec_int. rewrite po_addv_assoc H. reflexivity.
Qed.

Local Ltac reg_neq :=
  lazymatch goal with |- ?a <> ?b =>
    tryif unify a b then fail else (vm_compute; discriminate) end.
Local Ltac nz := vm_compute; discriminate.
Local Ltac pcw := apply bv_eq; vm_compute; reflexivity.

(* THE CALLEE-SAVED ROLES: s1 = the character [c], and then -- once the
   C('U') arm has hoisted them -- s1 = &cons, s2 = '\n', s3 = BACKSPACE.
   s0 is the frame pointer and is dead after the prologue. *)
Notation Rra  := (mword_of_int 1  : mword 5).
Notation Rs0  := (mword_of_int 8  : mword 5).
Notation Rs1  := (mword_of_int 9  : mword 5).
Notation Ra0  := (mword_of_int 10 : mword 5).
Notation Ra1  := (mword_of_int 11 : mword 5).
Notation Ra2  := (mword_of_int 12 : mword 5).
Notation Ra3  := (mword_of_int 13 : mword 5).
Notation Ra4  := (mword_of_int 14 : mword 5).
Notation Ra5  := (mword_of_int 15 : mword 5).
Notation Rs2  := (mword_of_int 18 : mword 5).
Notation Rs3  := (mword_of_int 19 : mword 5).
Notation Rs4  := (mword_of_int 20 : mword 5).
Notation Rs5  := (mword_of_int 21 : mword 5).
Notation Rs6  := (mword_of_int 22 : mword 5).
Notation Rs7  := (mword_of_int 23 : mword 5).
Notation Rs8  := (mword_of_int 24 : mword 5).
Notation Rs9  := (mword_of_int 25 : mword 5).
Notation Rs10 := (mword_of_int 26 : mword 5).
Notation Rs11 := (mword_of_int 27 : mword 5).

Section CtBodies.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !irefslotG Σ}.
  Context `{!uartGhostG Σ, !diskGhostG Σ}.
  Context `{GEN : RiscvLang.GenId}.

  Local Ltac rgall := repeat (rewrite rget_ne; [| vm_compute; discriminate]).

  (* ---- the frame, in two pieces ------------------------------------ *)

  (* the three the prologue saves unconditionally *)
  Definition ct_saved (sp0 : mword 64) (m0 : regfile) : iProp Σ :=
    (pa_stk sp0 1 ↦₈ (m0 !!! Regidx Rra) ∗
     pa_stk sp0 2 ↦₈ (m0 !!! Regidx Rs0) ∗
     pa_stk sp0 3 ↦₈ (m0 !!! Regidx Rs1))%I.

  (* slots 4 and 5 (s2/s3's shrink-wrap) and slot 6, which nothing writes *)
  Definition ct_rest (sp0 : mword 64) : iProp Σ :=
    ((∃ w : mword 64, pa_stk sp0 4 ↦₈ w) ∗
     (∃ w : mword 64, pa_stk sp0 5 ↦₈ w) ∗
     (∃ w : mword 64, pa_stk sp0 6 ↦₈ w))%I.

  Lemma ct_frame_back (sp0 : mword 64) (m0 : regfile) :
    ct_saved sp0 m0 -∗ ct_rest sp0 -∗ stack_own sp0 6.
  Proof.
    iIntros "(H1 & H2 & H3) (H4 & H5 & H6)".
    rewrite stack_own_slots. cbn [seq].
    iSplitL "H1"; [by iExists _|]. iSplitL "H2"; [by iExists _|].
    iSplitL "H3"; [by iExists _|]. iSplitL "H4"; [iExact "H4"|].
    iSplitL "H5"; [iExact "H5"|]. iSplitL "H6"; [iExact "H6"|]. done.
  Qed.

  (* the ten callee-saved registers the epilogue does NOT reload: s2 and s3
     (restored on the one arm that spilled them) and s4..s11, which nothing
     in this function touches at all. *)
  Definition ct_cs_hi (M m0 : regfile) : Prop :=
    M !!! Regidx Rs2  = m0 !!! Regidx Rs2
    /\ M !!! Regidx Rs3  = m0 !!! Regidx Rs3
    /\ M !!! Regidx Rs4  = m0 !!! Regidx Rs4
    /\ M !!! Regidx Rs5  = m0 !!! Regidx Rs5
    /\ M !!! Regidx Rs6  = m0 !!! Regidx Rs6
    /\ M !!! Regidx Rs7  = m0 !!! Regidx Rs7
    /\ M !!! Regidx Rs8  = m0 !!! Regidx Rs8
    /\ M !!! Regidx Rs9  = m0 !!! Regidx Rs9
    /\ M !!! Regidx Rs10 = m0 !!! Regidx Rs10
    /\ M !!! Regidx Rs11 = m0 !!! Regidx Rs11.

  (* the function's own exit, as a [wp_next] at the entry hart *)
  Definition ct_ret `{CID0 : CpuId} (pme : mword 64) (m0 : regfile)
      (K lvl : nat) (eb : bool) (C : iProp Σ) (b : bool) : iProp Σ :=
    (wp_next (CID0 := CID0) b pme (fun (CID : CpuId) =>
       ∀ Mf : regfile,
         ⌜ callee_saved m0 Mf /\ (forall r : regidx, r ∈ dom (rf_to_gmap Mf)) ⌝ -∗
         sie_cap_gpr Mf K b pme -∗
         cpu_own lvl eb pme C b -∗
         kernel_text -∗ pc_is (ret_pc (m0 !!! Regidx Rra)) -∗
         WP (Loop : expr riscv_lang)))%I.

  (* =================================================================== *)
  (*  +0x110 .. +0x118 -- THE EPILOGUE.                                   *)
  (* =================================================================== *)
  Lemma ct_epi `{CID : CpuId} (CID0 : CPU)
      (pme : mword 64) (m0 M : regfile) (K lvl : nat) (eb : bool) (C : iProp Σ)
      (sp0 : mword 64) (b : bool) :
    m0 !!! Regidx csp_rs1 = sp0 ->
    M !!! Regidx csp_rs1 = pa_stk sp0 6%nat ->
    ct_cs_hi M m0 ->
    (consoleintr_stack <= K)%nat ->
    (b = false \/ pme = zero_reg -> (CID : CPU) = CID0) ->
    kernel_text -∗
    sie_cap_gpr M (K - 6)%nat b pme -∗
    cpu_own lvl eb pme C b -∗
    pc_is (mword_of_int (CT + 0x110)) -∗
    ct_saved sp0 m0 -∗ ct_rest sp0 -∗
    ct_ret (CID0 := CID0) pme m0 K lvl eb C b -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hm0sp HMsp HMcs HK Hcr.
    iIntros "#Ht Hcg Hcnt Hpc (K1 & K2 & K3) Hrest Hcont".
    iPoseProof (cnti_110 with "Ht") as "Hi110".
    iPoseProof (cnti_112 with "Ht") as "Hi112".
    iPoseProof (cnti_114 with "Ht") as "Hi114".
    iPoseProof (cnti_116 with "Ht") as "Hi116".
    iPoseProof (cnti_118 with "Ht") as "Hi118".
    assert (Hb1 : add_vec (pa_stk sp0 6%nat)
                    (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000")))
                  = pa_stk sp0 1) by (apply ct_slot_bridge; pcw).
    assert (Hb2 : add_vec (pa_stk sp0 6%nat)
                    (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000")))
                  = pa_stk sp0 2) by (apply ct_slot_bridge; pcw).
    assert (Hb3 : add_vec (pa_stk sp0 6%nat)
                    (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000")))
                  = pa_stk sp0 3) by (apply ct_slot_bridge; pcw).
    (* +0x110  c.ldsp ra,40(sp) *)
    iApply (wp_cldsp_s_sconf (mword_of_int (CT + 0x110)) (mword_of_int 5 : mword 6) Rra
              M (K - 6)%nat (m0 !!! Regidx Rra) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hi110 [K1]").
    { iEval (rewrite HMsp Hb1). iExact "K1". }
    iIntros (CIDe0 Hse0) "Hcg Hpc K1". iEval (rewrite HMsp Hb1) in "K1".
    set (E1 := <[Regidx Rra := regval_into_reg (m0 !!! Regidx Rra)]> M).
    assert (HE1sp : E1 !!! Regidx csp_rs1 = pa_stk sp0 6%nat)
      by (rewrite /E1 upd_ne; [exact HMsp | reg_neq]).
    assert (Pe12 : add_vec_int (mword_of_int (CT + 0x110) : mword 64) 2
                  = mword_of_int (CT + 0x112)) by pcw.
    iEval (rewrite Pe12) in "Hpc".
    (* +0x112  c.ldsp s0,32(sp) *)
    iApply (wp_cldsp_s_sconf (mword_of_int (CT + 0x112)) (mword_of_int 4 : mword 6) Rs0
              E1 (K - 6)%nat (m0 !!! Regidx Rs0) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hi112 [K2]").
    { iEval (rewrite HE1sp Hb2). iExact "K2". }
    iIntros (CIDe1 Hse1) "Hcg Hpc K2". iEval (rewrite HE1sp Hb2) in "K2".
    set (E2 := <[Regidx Rs0 := regval_into_reg (m0 !!! Regidx Rs0)]> E1).
    assert (HE2sp : E2 !!! Regidx csp_rs1 = pa_stk sp0 6%nat)
      by (rewrite /E2 upd_ne; [exact HE1sp | reg_neq]).
    assert (Pe14 : add_vec_int (mword_of_int (CT + 0x112) : mword 64) 2
                  = mword_of_int (CT + 0x114)) by pcw.
    iEval (rewrite Pe14) in "Hpc".
    (* +0x114  c.ldsp s1,24(sp) *)
    iApply (wp_cldsp_s_sconf (mword_of_int (CT + 0x114)) (mword_of_int 3 : mword 6) Rs1
              E2 (K - 6)%nat (m0 !!! Regidx Rs1) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hi114 [K3]").
    { iEval (rewrite HE2sp Hb3). iExact "K3". }
    iIntros (CIDe2 Hse2) "Hcg Hpc K3". iEval (rewrite HE2sp Hb3) in "K3".
    set (E3 := <[Regidx Rs1 := regval_into_reg (m0 !!! Regidx Rs1)]> E2).
    assert (HE3sp : E3 !!! Regidx csp_rs1 = pa_stk sp0 6%nat)
      by (rewrite /E3 upd_ne; [exact HE2sp | reg_neq]).
    assert (Pe16 : add_vec_int (mword_of_int (CT + 0x114) : mword 64) 2
                  = mword_of_int (CT + 0x116)) by pcw.
    iEval (rewrite Pe16) in "Hpc".
    (* +0x116  c.addi16sp sp,+48 : the pop *)
    assert (Hspv : add_vec (E3 !!! Regidx csp_rs1)
                     (sign_extend' 64 (caddi16sp_imm (mword_of_int 3 : mword 6))) = sp0).
    { rewrite HE3sp. unfold pa_stk, add_vec_int. rewrite po_addv_assoc.
      rewrite (_ : add_vec (mword_of_int (- (8 * Z.of_nat 6%nat)) : mword 64)
                     (sign_extend' 64 (caddi16sp_imm (mword_of_int 3 : mword 6)))
                   = (mword_of_int 0 : mword 64)); [| pcw].
      apply bv_add_0_r. vm_compute. reflexivity. }
    assert (Hpop : E3 !!! Regidx csp_rs1
                   = pa_stk (add_vec (E3 !!! Regidx csp_rs1)
                       (sign_extend' 64 (caddi16sp_imm (mword_of_int 3 : mword 6)))) 6%nat)
      by (rewrite Hspv HE3sp; reflexivity).
    iDestruct (ct_frame_back sp0 m0 with "[K1 K2 K3] Hrest") as "Hframe".
    { rewrite /ct_saved. iFrame "K1 K2 K3". }
    iEval (rewrite -Hspv) in "Hframe".
    iApply (wp_caddi16sp_pop_s_sconf (mword_of_int (CT + 0x116)) (mword_of_int 3 : mword 6)
              E3 (K - 6)%nat 6%nat b Hpop with "Hcg Hpc Hi116 Hframe").
    iIntros (CIDp Hsp') "Hcg Hpc".
    assert (Havx : (K - 6 + 6)%nat = K) by (unfold consoleintr_stack in HK; lia).
    iEval (rewrite Havx) in "Hcg".
    set (E4 := <[Regidx csp_rs1 := regval_into_reg
        (add_vec (E3 !!! Regidx csp_rs1)
           (sign_extend' 64 (caddi16sp_imm (mword_of_int 3 : mword 6))))]> E3).
    assert (Pe18 : add_vec_int (mword_of_int (CT + 0x116) : mword 64) 2
                  = mword_of_int (CT + 0x118)) by pcw.
    iEval (rewrite Pe18) in "Hpc".
    (* +0x118  c.ret *)
    assert (HE4ra : E4 !!! Regidx Rra = m0 !!! Regidx Rra).
    { rewrite /E4 upd_ne; [| reg_neq]. rewrite /E3 upd_ne; [| reg_neq].
      rewrite /E2 upd_ne; [| reg_neq]. rewrite /E1 upd_eq. reflexivity. }
    iApply (wp_cret_s_sconf (mword_of_int (CT + 0x118)) Rra E4 K b
              ltac:(nz) with "Hcg Hpc Hi118").
    iIntros (CIDr Hsr) "Hcg Hpc".
    iEval (rewrite rget_ne; [| reg_neq]) in "Hpc".
    iEval (rewrite HE4ra) in "Hpc".
    assert (Hcs : callee_saved m0 E4).
    { destruct HMcs as (Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11).
      assert (Hthr : forall r : mword 5, r <> csp_rs1 -> r <> Rra -> r <> Rs0 -> r <> Rs1 ->
                E4 !!! Regidx r = M !!! Regidx r).
      { intros r N2 N1 N8 N9.
        rewrite /E4 upd_ne; [| congruence]. rewrite /E3 upd_ne; [| congruence].
        rewrite /E2 upd_ne; [| congruence]. rewrite /E1 upd_ne; [| congruence].
        reflexivity. }
      unfold callee_saved. split_and!.
      - rewrite /E4 upd_eq. unfold regval_into_reg. rewrite Hspv. symmetry. exact Hm0sp.
      - rewrite /E4 upd_ne; [| reg_neq]. rewrite /E3 upd_ne; [| reg_neq].
        rewrite /E2 upd_eq. reflexivity.
      - rewrite /E4 upd_ne; [| reg_neq]. rewrite /E3 upd_eq. reflexivity.
      - rewrite (Hthr Rs2 ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)). exact Q2.
      - rewrite (Hthr Rs3 ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)). exact Q3.
      - rewrite (Hthr Rs4 ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)). exact Q4.
      - rewrite (Hthr Rs5 ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)). exact Q5.
      - rewrite (Hthr Rs6 ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)). exact Q6.
      - rewrite (Hthr Rs7 ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)). exact Q7.
      - rewrite (Hthr Rs8 ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)). exact Q8.
      - rewrite (Hthr Rs9 ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)). exact Q9.
      - rewrite (Hthr Rs10 ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)). exact Q10.
      - rewrite (Hthr Rs11 ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)). exact Q11. }
    iDestruct (cpu_own_transport CID CIDr lvl eb pme C b ltac:(wp_next_chain)
                 with "Hcnt") as "Hcnt".
    rewrite /ct_ret.
    iSpecialize ("Hcont" $! CIDr with "[%]"); [wp_next_chain|].
    iApply ("Hcont" $! E4 with "[%] Hcg Hcnt Ht Hpc").
    split; [exact Hcs | intro r; apply rf_to_gmap_dom].
  Qed.

End CtBodies.

(* ===================================================================== *)
Module ConsoleintrProof (Acquire : ACQUIRE) (Consputc : CONSPUTC)
                        (Release : RELEASE) (Wakeup : WAKEUP).

Section ProofConsoleintr.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !irefslotG Σ}.
  Context `{!uartGhostG Σ, !diskGhostG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Local Ltac rgall := repeat (rewrite rget_ne; [| vm_compute; discriminate]).
  Local Typeclasses Opaque cpu_own.

  (* =================================================================== *)
  (*  [EXIT] (+0x104): release cons.lock, then the epilogue.              *)
  (*  NINE jumps reach it -- every arm of the switch ends here -- so it   *)
  (*  is a continuation and the epilogue is written once.                 *)
  (* =================================================================== *)
  Definition ct_exit_prop `{CID0 : CpuId}
      (γc : gname) (pme : mword 64) (m0 : regfile) (K lvl : nat) (eb : bool)
      (C : iProp Σ) (b : bool) (sp0 : mword 64) : iProp Σ :=
    (wp_next (CID0 := CID0) b pme (fun (CIDx : CpuId) =>
       ∀ M : regfile,
         ⌜ M !!! Regidx csp_rs1 = pa_stk sp0 6%nat ⌝ -∗
         ⌜ ct_cs_hi M m0 ⌝ -∗
         sie_cap_gpr M (trap_res b + (K - 6))%nat false pme -∗
         pc_is (mword_of_int (CT + 0x104)) -∗
         cpu_own (S lvl) eb pme C false -∗
         arm_pay lvl eb pme -∗
         locked γc cpu_id -∗
         cons_res -∗
         ct_rest sp0 -∗
         WP (Loop : expr riscv_lang)))%I.

  Lemma ct_mk_exit (γc : gname) (pme : mword 64) (m0 : regfile) (K lvl : nat)
      (eb : bool) (C : iProp Σ) (b : bool) (sp0 : mword 64) :
    m0 !!! Regidx csp_rs1 = sp0 ->
    (consoleintr_stack <= K)%nat ->
    match lvl with O => eb | S _ => false end = b ->
    kernel_text -∗ is_conslock γc -∗ ct_saved sp0 m0 -∗
    ct_ret (CID0 := CID) pme m0 K lvl eb C b -∗
    ct_exit_prop (CID0 := CID) γc pme m0 K lvl eb C b sp0.
  Proof.
    intros Hm0sp HK Hb. subst b.
    iIntros "#Ht #Hlk Hsaved Hcont".
    rewrite /ct_exit_prop.
    iIntros (CIDx Hsx M) "%Hsp %Hcs Hcg Hpc Hcnt Hpay Hlocked Hres Hrest".
    iPoseProof (cnti_104 with "Ht") as "Hi104".
    iPoseProof (cnti_108 with "Ht") as "Hi108".
    iPoseProof (cnti_10c with "Ht") as "Hi10c".
    (* +0x104 auipc a0,0x12 ; +0x108 addi a0,a0,-272 : a0 := &cons *)
    iApply (wp_auipc_s_sconf (mword_of_int (CT + 0x104)) Ra0 (mword_of_int 18 : mword 20)
              M (trap_res (match lvl with O => eb | S _ => false end) + (K - 6))%nat false ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hi104").
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    set (X1 := <[Regidx Ra0 := regval_into_reg
        (add_vec (mword_of_int (CT + 0x104) : mword 64)
           (auipc_off (mword_of_int 18 : mword 20)))]> M).
    assert (Hp108 : add_vec_int (mword_of_int (CT + 0x104) : mword 64) 4
                    = mword_of_int (CT + 0x108)) by pcw.
    iEval (rewrite Hp108) in "Hpc".
    iApply (wp_addi4_s_sconf (mword_of_int (CT + 0x108)) Ra0 Ra0 (mword_of_int 3824 : mword 12)
              X1 (trap_res (match lvl with O => eb | S _ => false end) + (K - 6))%nat false ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hi108").
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    set (X2 := <[Regidx Ra0 := regval_into_reg
        (add_vec (X1 !!! Regidx Ra0) (sign_extend' 64 (mword_of_int 3824 : mword 12)))]> X1).
    assert (HX2a0 : X2 !!! Regidx Ra0 = a_cons).
    { rewrite /X2 upd_eq /X1 upd_eq /a_cons. apply bv_eq; vm_compute; reflexivity. }
    assert (Hp10c : add_vec_int (mword_of_int (CT + 0x108) : mword 64) 4
                    = mword_of_int (CT + 0x10c)) by pcw.
    iEval (rewrite Hp10c) in "Hpc".
    (* +0x10c jal ra,release *)
    iApply (wp_jal_s_sconf (mword_of_int (CT + 0x10c)) Rra (mword_of_int 2170 : mword 21)
              X2 (trap_res (match lvl with O => eb | S _ => false end) + (K - 6))%nat false ltac:(nz) ltac:(rdok)
              ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi10c").
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    set (X3 := <[Regidx Rra := regval_into_reg
        (add_vec_int (mword_of_int (CT + 0x10c) : mword 64) 4)]> X2).
    assert (Hjrl : add_vec (mword_of_int (CT + 0x10c) : mword 64)
                     (sign_extend' 64 (mword_of_int 2170 : mword 21))
                   = mword_of_int KernelSyms.release) by pcw.
    iEval (rewrite Hjrl) in "Hpc".
    assert (HX3a0 : X3 !!! Regidx Ra0 = a_cons)
      by (rewrite /X3 upd_ne; [exact HX2a0 | reg_neq]).
    assert (HX3ra : X3 !!! Regidx Rra
                    = add_vec_int (mword_of_int (CT + 0x10c) : mword 64) 4)
      by (rewrite /X3; apply upd_eq).
    assert (HX3lka : add_vec (X3 !!! Regidx Ra0)
                       (sign_extend' 64 (mword_of_int 0 : mword 12)) = a_cons).
    { rewrite HX3a0.
      replace (sign_extend' 64 (mword_of_int 0 : mword 12)) with (mword_of_int 0 : mword 64)
        by pcw.
      apply kv_addv_zero. }
    assert (HthrX : forall r : mword 5, is_cs_idx r = true -> X3 !!! Regidx r = M !!! Regidx r).
    { intros r Hr.
      assert (N1 : r <> Rra) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      assert (N10 : r <> Ra0) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      rewrite /X3 upd_ne; [| congruence]. rewrite /X2 upd_ne; [| congruence].
      rewrite /X1 upd_ne; [| congruence]. reflexivity. }
    iApply (Release.wp_release_sconf γc a_cons "cons"%string cons_res X3
              lvl eb pme C (K - 6)%nat HX3lka
              ltac:(unfold consoleintr_stack in HK; lia)
              with "Hcg Ht Hpc Hlk Hlocked Hres Hcnt Hpay").
    iIntros (CIDr Hsr mr) "Hcg Hpc %Hcsr Hcnt". rgall.
    iEval (rewrite HX3ra) in "Hpc".
    assert (Hp110 : ret_pc (add_vec_int (mword_of_int (CT + 0x10c) : mword 64) 4)
                    = (mword_of_int (CT + 0x110) : mword 64)) by pcw.
    iEval (rewrite Hp110) in "Hpc".
    assert (Hthr : forall r : mword 5, is_cs_idx r = true -> mr !!! Regidx r = M !!! Regidx r).
    { intros r Hr. rewrite (callee_saved_lookup Hcsr r Hr). apply HthrX; exact Hr. }
    iApply (ct_epi (CID := CIDr) CIDr pme m0 mr K lvl eb C sp0 _ Hm0sp
              ltac:(rewrite (Hthr csp_rs1 ltac:(vm_compute; reflexivity)); exact Hsp)
              ltac:(destruct Hcs as (Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11);
                    unfold ct_cs_hi; split_and!;
                      [ rewrite (Hthr Rs2 ltac:(vm_compute; reflexivity)); exact Q2
                      | rewrite (Hthr Rs3 ltac:(vm_compute; reflexivity)); exact Q3
                      | rewrite (Hthr Rs4 ltac:(vm_compute; reflexivity)); exact Q4
                      | rewrite (Hthr Rs5 ltac:(vm_compute; reflexivity)); exact Q5
                      | rewrite (Hthr Rs6 ltac:(vm_compute; reflexivity)); exact Q6
                      | rewrite (Hthr Rs7 ltac:(vm_compute; reflexivity)); exact Q7
                      | rewrite (Hthr Rs8 ltac:(vm_compute; reflexivity)); exact Q8
                      | rewrite (Hthr Rs9 ltac:(vm_compute; reflexivity)); exact Q9
                      | rewrite (Hthr Rs10 ltac:(vm_compute; reflexivity)); exact Q10
                      | rewrite (Hthr Rs11 ltac:(vm_compute; reflexivity)); exact Q11 ])
              HK ltac:(intros _; reflexivity)
              with "Ht Hcg Hcnt Hpc Hsaved Hrest").
    iApply (wp_next_retarget CID CIDr _ pme _ ltac:(wp_next_chain) with "Hcont").
  Qed.

  (* =================================================================== *)
  (*  [WAKE] (+0x156): publish the edit index and wake a blocked reader.  *)
  (*  Four entries reach it -- '\n' and C('D') from the echo path, the    *)
  (*  ring-full test, and the '\r' arm's fall-through -- and every one of *)
  (*  them has already put the new [cons.e] in a2, which is the only      *)
  (*  register this block reads.                                          *)
  (* =================================================================== *)
  Definition ct_wake_prop `{CID0 : CpuId}
      (γc : gname) (γs : list gname) (pme : mword 64) (m0 : regfile)
      (K lvl : nat) (eb : bool) (C : iProp Σ) (b : bool) (sp0 : mword 64) : iProp Σ :=
    (wp_next (CID0 := CID0) b pme (fun (CIDw : CpuId) =>
       ∀ (M : regfile) (wv : mword 64),
         ⌜ M !!! Regidx csp_rs1 = pa_stk sp0 6%nat ⌝ -∗
         ⌜ M !!! Regidx Ra2 = wv ⌝ -∗
         ⌜ ct_cs_hi M m0 ⌝ -∗
         sie_cap_gpr M (trap_res b + (K - 6))%nat false pme -∗
         pc_is (mword_of_int (CT + 0x156)) -∗
         cpu_own (S lvl) eb pme C false -∗
         arm_pay lvl eb pme -∗
         locked γc cpu_id -∗
         cons_res -∗
         ct_rest sp0 -∗
         ct_exit_prop (CID0 := CID0) γc pme m0 K lvl eb C b sp0 -∗
         WP (Loop : expr riscv_lang)))%I.

  Lemma ct_mk_wake (γc : gname) (γs : list gname) (pme : mword 64) (m0 : regfile)
      (K lvl : nat) (eb : bool) (C : iProp Σ) (b : bool) (sp0 : mword 64) :
    (consoleintr_stack <= K)%nat ->
    length γs = NPROC ->
    (Z.of_nat lvl + 2 < 2 ^ 31)%Z ->
    match lvl with O => eb | S _ => false end = b ->
    kernel_text -∗ panic_wp_any -∗ procs_inv γs -∗
    ct_wake_prop (CID0 := CID) γc γs pme m0 K lvl eb C b sp0.
  Proof.
    intros HK Hlen Hlvl Hb. subst b.
    iIntros "#Ht #Hpanic #Hpinv".
    rewrite /ct_wake_prop.
    iIntros (CIDw Hsw M wv) "%Hsp %Ha2 %Hcs Hcg Hpc Hcnt Hpay Hlocked Hres Hrest EXIT".
    iPoseProof (cnti_156 with "Ht") as "Hi156".
    iPoseProof (cnti_15a with "Ht") as "Hi15a".
    iPoseProof (cnti_15e with "Ht") as "Hi15e".
    iPoseProof (cnti_162 with "Ht") as "Hi162".
    iPoseProof (cnti_166 with "Ht") as "Hi166".
    iPoseProof (cnti_16a with "Ht") as "Hi16a".
    (* +0x156 auipc a5,0x12 *)
    iApply (wp_auipc_s_sconf (mword_of_int (CT + 0x156)) Ra5 (mword_of_int 18 : mword 20)
              M (trap_res (match lvl with O => eb | S _ => false end) + (K - 6))%nat false
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi156").
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    set (W1 := <[Regidx Ra5 := regval_into_reg
        (add_vec (mword_of_int (CT + 0x156) : mword 64)
           (auipc_off (mword_of_int 18 : mword 20)))]> M).
    assert (Hp15a : add_vec_int (mword_of_int (CT + 0x156) : mword 64) 4
                    = mword_of_int (CT + 0x15a)) by pcw.
    iEval (rewrite Hp15a) in "Hpc".
    (* +0x15a sw a2,-198(a5) : cons.w := cons.e *)
    iDestruct "Hres" as (rr ww ee bs) "(Hrc & Hwc & Hec & %Hlenb & Hdat)".
    assert (HW1wa : add_vec (W1 !!! Regidx Ra5)
                      (sign_extend' 64 (mword_of_int 3898 : mword 12)) = a_cons_w).
    { rewrite /W1 upd_eq /a_cons_w /coff_of /a_cons. apply bv_eq; vm_compute; reflexivity. }
    assert (HW1a2 : W1 !!! Regidx Ra2 = wv)
      by (rewrite /W1 upd_ne; [exact Ha2 | reg_neq]).
    iApply (wp_sw_s_sconf (mword_of_int (CT + 0x15a)) Ra2 Ra5 (mword_of_int 3898 : mword 12)
              W1 (trap_res (match lvl with O => eb | S _ => false end) + (K - 6))%nat ww false
              with "Hcg Hpc Hi15a [Hwc]").
    { rgall. iEval (rewrite HW1wa). iExact "Hwc". }
    iApply wp_next_off_intro. iIntros "Hcg Hpc Hwc". rgall.
    iEval (rewrite HW1wa HW1a2) in "Hwc".
    assert (Hp15e : add_vec_int (mword_of_int (CT + 0x15a) : mword 64) 4
                    = mword_of_int (CT + 0x15e)) by pcw.
    iEval (rewrite Hp15e) in "Hpc".
    iAssert (cons_res) with "[Hrc Hwc Hec Hdat]" as "Hres".
    { iExists rr, (trunc32 wv), ee, bs. iFrame "Hrc Hwc Hec Hdat".
      iPureIntro. exact Hlenb. }
    (* +0x15e auipc a0,0x12 ; +0x162 addi a0,a0,-210 : a0 := &cons.r *)
    iApply (wp_auipc_s_sconf (mword_of_int (CT + 0x15e)) Ra0 (mword_of_int 18 : mword 20)
              W1 (trap_res (match lvl with O => eb | S _ => false end) + (K - 6))%nat false
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi15e").
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    set (W2 := <[Regidx Ra0 := regval_into_reg
        (add_vec (mword_of_int (CT + 0x15e) : mword 64)
           (auipc_off (mword_of_int 18 : mword 20)))]> W1).
    assert (Hp162 : add_vec_int (mword_of_int (CT + 0x15e) : mword 64) 4
                    = mword_of_int (CT + 0x162)) by pcw.
    iEval (rewrite Hp162) in "Hpc".
    iApply (wp_addi4_s_sconf (mword_of_int (CT + 0x162)) Ra0 Ra0 (mword_of_int 3886 : mword 12)
              W2 (trap_res (match lvl with O => eb | S _ => false end) + (K - 6))%nat false
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi162").
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    set (W3 := <[Regidx Ra0 := regval_into_reg
        (add_vec (W2 !!! Regidx Ra0) (sign_extend' 64 (mword_of_int 3886 : mword 12)))]> W2).
    assert (Hp166 : add_vec_int (mword_of_int (CT + 0x162) : mword 64) 4
                    = mword_of_int (CT + 0x166)) by pcw.
    iEval (rewrite Hp166) in "Hpc".
    (* +0x166 jal ra,wakeup *)
    iApply (wp_jal_s_sconf (mword_of_int (CT + 0x166)) Rra (mword_of_int 6958 : mword 21)
              W3 (trap_res (match lvl with O => eb | S _ => false end) + (K - 6))%nat false
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi166").
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    set (W4 := <[Regidx Rra := regval_into_reg
        (add_vec_int (mword_of_int (CT + 0x166) : mword 64) 4)]> W3).
    assert (Hjwk : add_vec (mword_of_int (CT + 0x166) : mword 64)
                     (sign_extend' 64 (mword_of_int 6958 : mword 21))
                   = mword_of_int KernelSyms.wakeup) by pcw.
    iEval (rewrite Hjwk) in "Hpc".
    assert (HW4ra : W4 !!! Regidx Rra
                    = add_vec_int (mword_of_int (CT + 0x166) : mword 64) 4)
      by (rewrite /W4; apply upd_eq).
    assert (HthrW : forall r : mword 5, is_cs_idx r = true -> W4 !!! Regidx r = M !!! Regidx r).
    { intros r Hr.
      assert (N1 : r <> Rra) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      assert (N10 : r <> Ra0) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      assert (N15 : r <> Ra5) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      rewrite /W4 upd_ne; [| congruence]. rewrite /W3 upd_ne; [| congruence].
      rewrite /W2 upd_ne; [| congruence]. rewrite /W1 upd_ne; [| congruence]. reflexivity. }
    iApply (Wakeup.wp_wakeup_sconf W4 γs pme (S lvl)
              (trap_res (match lvl with O => eb | S _ => false end) + (K - 6))%nat eb C false
              ltac:(unfold consoleintr_stack in HK; lia)
              ltac:(intro r; apply rf_to_gmap_dom) Hlen ltac:(lia)
              with "Hcg Hcnt Ht Hpc Hpanic Hpinv").
    iApply wp_next_off_intro. iIntros (Mw) "[%Hwcs %Hwdom] Hcg Hcnt _ Hpc". rgall.
    iEval (rewrite HW4ra) in "Hpc".
    assert (Hp16a : ret_pc (add_vec_int (mword_of_int (CT + 0x166) : mword 64) 4)
                    = (mword_of_int (CT + 0x16a) : mword 64)) by pcw.
    iEval (rewrite Hp16a) in "Hpc".
    assert (Hthr : forall r : mword 5, is_cs_idx r = true -> Mw !!! Regidx r = M !!! Regidx r).
    { intros r Hr. rewrite (callee_saved_lookup Hwcs r Hr). apply HthrW; exact Hr. }
    (* +0x16a c.j -> the exit at +0x104 *)
    iApply (wp_cj_s_sconf (mword_of_int (CT + 0x16a))
              (sign_extend' 21 (concat_vec (mword_of_int 1997 : mword 11) ('b"0")))
              Mw (trap_res (match lvl with O => eb | S _ => false end) + (K - 6))%nat false
              ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi16a").
    iApply wp_next_off_intro. iApply bi.later_intro. iIntros "Hcg Hpc". rgall.
    assert (Hj104 : add_vec (mword_of_int (CT + 0x16a) : mword 64)
                      (sign_extend' 64 (sign_extend' 21
                         (concat_vec (mword_of_int 1997 : mword 11) ('b"0"))))
                    = mword_of_int (CT + 0x104)) by pcw.
    iEval (rewrite Hj104) in "Hpc".
    iSpecialize ("EXIT" $! CIDw with "[%]"); [wp_next_chain|].
    iApply ("EXIT" $! Mw with "[%] [%] Hcg Hpc Hcnt Hpay Hlocked Hres Hrest").
    - rewrite (Hthr csp_rs1 ltac:(vm_compute; reflexivity)). exact Hsp.
    - destruct Hcs as (Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11).
      unfold ct_cs_hi. split_and!;
        [ rewrite (Hthr Rs2 ltac:(vm_compute; reflexivity)); exact Q2
        | rewrite (Hthr Rs3 ltac:(vm_compute; reflexivity)); exact Q3
        | rewrite (Hthr Rs4 ltac:(vm_compute; reflexivity)); exact Q4
        | rewrite (Hthr Rs5 ltac:(vm_compute; reflexivity)); exact Q5
        | rewrite (Hthr Rs6 ltac:(vm_compute; reflexivity)); exact Q6
        | rewrite (Hthr Rs7 ltac:(vm_compute; reflexivity)); exact Q7
        | rewrite (Hthr Rs8 ltac:(vm_compute; reflexivity)); exact Q8
        | rewrite (Hthr Rs9 ltac:(vm_compute; reflexivity)); exact Q9
        | rewrite (Hthr Rs10 ltac:(vm_compute; reflexivity)); exact Q10
        | rewrite (Hthr Rs11 ltac:(vm_compute; reflexivity)); exact Q11 ].
  Qed.

  (* ---- the three-instruction stub the C('U') arm exits through -------
     [c.ldsp s2,16(sp)], [c.ldsp s3,8(sp)], [c.j -> +0x104].  It occurs at
     +0x0de, +0x0e4 and +0x0ea -- once per way out of the kill-line loop --
     so it is a lemma over its three pcs rather than three copies. *)
  Lemma ct_restore23 `{CIDq : CpuId}
      (γc : gname) (pme : mword 64) (m0 M : regfile) (K lvl : nat) (eb : bool)
      (C : iProp Σ) (b : bool) (sp0 : mword 64) (pc1 pc2 pc3 : mword 64)
      (jimm : mword 11) :
    M !!! Regidx csp_rs1 = pa_stk sp0 6%nat ->
    (forall r : mword 5, is_cs_idx r = true -> r <> Rs1 -> r <> Rs2 -> r <> Rs3 ->
       M !!! Regidx r = m0 !!! Regidx r) ->
    add_vec_int pc1 2 = pc2 ->
    add_vec_int pc2 2 = pc3 ->
    add_vec pc3 (sign_extend' 64 (sign_extend' 21 (concat_vec jimm ('b"0"))))
      = mword_of_int (CT + 0x104) ->
    eq_vec (access_vec_dec (add_vec pc3
      (sign_extend' 64 (sign_extend' 21 (concat_vec jimm ('b"0"))))) 0) ('b"0") = true ->
    (b = false \/ pme = zero_reg -> (CIDq : CPU) = (CID : CPU)) ->
    instr pc1 true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")),
                          sp, Regidx Rs2, false, 8)) -∗
    instr pc2 true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")),
                          sp, Regidx Rs3, false, 8)) -∗
    instr pc3 true (JAL (sign_extend' 21 (concat_vec jimm ('b"0")), zreg)) -∗
    sie_cap_gpr M (trap_res b + (K - 6))%nat false pme -∗
    pc_is pc1 -∗
    cpu_own (S lvl) eb pme C false -∗
    arm_pay lvl eb pme -∗
    locked γc cpu_id -∗
    cons_res -∗
    pa_stk sp0 4 ↦₈ (m0 !!! Regidx Rs2) -∗
    pa_stk sp0 5 ↦₈ (m0 !!! Regidx Rs3) -∗
    (∃ w : mword 64, pa_stk sp0 6 ↦₈ w) -∗
    ct_exit_prop (CID0 := CID) γc pme m0 K lvl eb C b sp0 -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hsp Hthr Hq1 Hq2 Hjt Hal Hchain.
    iIntros "Hi1 Hi2 Hi3 Hcg Hpc Hcnt Hpay Hlocked Hres H4 H5 H6 EXIT".
    assert (Hb4 : add_vec (pa_stk sp0 6%nat)
                    (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000")))
                  = pa_stk sp0 4) by (apply ct_slot_bridge; pcw).
    assert (Hb5 : add_vec (pa_stk sp0 6%nat)
                    (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000")))
                  = pa_stk sp0 5) by (apply ct_slot_bridge; pcw).
    iApply (wp_cldsp_s_sconf pc1 (mword_of_int 2 : mword 6) Rs2
              M (trap_res b + (K - 6))%nat (m0 !!! Regidx Rs2) false
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi1 [H4]").
    { iEval (rewrite Hsp Hb4). iExact "H4". }
    iApply wp_next_off_intro. iIntros "Hcg Hpc H4". rgall.
    iEval (rewrite Hsp Hb4) in "H4".
    set (R1 := <[Regidx Rs2 := regval_into_reg (m0 !!! Regidx Rs2)]> M).
    assert (HR1sp : R1 !!! Regidx csp_rs1 = pa_stk sp0 6%nat)
      by (rewrite /R1 upd_ne; [exact Hsp | reg_neq]).
    iEval (rewrite Hq1) in "Hpc".
    iApply (wp_cldsp_s_sconf pc2 (mword_of_int 1 : mword 6) Rs3
              R1 (trap_res b + (K - 6))%nat (m0 !!! Regidx Rs3) false
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi2 [H5]").
    { iEval (rewrite HR1sp Hb5). iExact "H5". }
    iApply wp_next_off_intro. iIntros "Hcg Hpc H5". rgall.
    iEval (rewrite HR1sp Hb5) in "H5".
    set (R2 := <[Regidx Rs3 := regval_into_reg (m0 !!! Regidx Rs3)]> R1).
    iEval (rewrite Hq2) in "Hpc".
    iApply (wp_cj_s_sconf pc3 (sign_extend' 21 (concat_vec jimm ('b"0")))
              R2 (trap_res b + (K - 6))%nat false Hal with "Hcg Hpc Hi3").
    iApply wp_next_off_intro. iApply bi.later_intro. iIntros "Hcg Hpc". rgall.
    iEval (rewrite Hjt) in "Hpc".
    iSpecialize ("EXIT" $! CIDq with "[%]"); [exact Hchain|].
    iApply ("EXIT" $! R2 with "[%] [%] Hcg Hpc Hcnt Hpay Hlocked Hres
              [H4 H5 H6]").
    - rewrite /R2 upd_ne; [| reg_neq]. exact HR1sp.
    - unfold ct_cs_hi. split_and!.
      + rewrite /R2 upd_ne; [| reg_neq]. rewrite /R1 upd_eq. reflexivity.
      + rewrite /R2 upd_eq. reflexivity.
      + rewrite /R2 upd_ne; [| reg_neq]. rewrite /R1 upd_ne; [| reg_neq].
        apply Hthr; first [vm_compute; reflexivity | reg_neq].
      + rewrite /R2 upd_ne; [| reg_neq]. rewrite /R1 upd_ne; [| reg_neq].
        apply Hthr; first [vm_compute; reflexivity | reg_neq].
      + rewrite /R2 upd_ne; [| reg_neq]. rewrite /R1 upd_ne; [| reg_neq].
        apply Hthr; first [vm_compute; reflexivity | reg_neq].
      + rewrite /R2 upd_ne; [| reg_neq]. rewrite /R1 upd_ne; [| reg_neq].
        apply Hthr; first [vm_compute; reflexivity | reg_neq].
      + rewrite /R2 upd_ne; [| reg_neq]. rewrite /R1 upd_ne; [| reg_neq].
        apply Hthr; first [vm_compute; reflexivity | reg_neq].
      + rewrite /R2 upd_ne; [| reg_neq]. rewrite /R1 upd_ne; [| reg_neq].
        apply Hthr; first [vm_compute; reflexivity | reg_neq].
      + rewrite /R2 upd_ne; [| reg_neq]. rewrite /R1 upd_ne; [| reg_neq].
        apply Hthr; first [vm_compute; reflexivity | reg_neq].
      + rewrite /R2 upd_ne; [| reg_neq]. rewrite /R1 upd_ne; [| reg_neq].
        apply Hthr; first [vm_compute; reflexivity | reg_neq].
    - rewrite /ct_rest. iSplitL "H4"; [by iExists _|].
      iSplitL "H5"; [by iExists _|]. iExact "H6".
  Qed.

  (* the [c.addiw a5,a5,-1] the loop head opens with, at the 32-bit value the
     cell then takes *)
  Lemma ct_addiw_dec (e : mword 32) :
    sign_extend' 64 (subrange_vec_dec
       (add_vec (sign_extend' 64 e)
                (sign_extend' 64 (sign_extend' 12 (mword_of_int 63 : mword 6)))) 31 0)
    = sign_extend' 64 (add_vec e (mword_of_int (-1) : mword 32)).
  Proof.
    rewrite <- trunc32_subrange. rewrite trunc32_add !trunc32_sext.
    assert (HK : trunc32 (sign_extend' 64 (sign_extend' 12 (mword_of_int 63 : mword 6)))
                 = (mword_of_int (-1) : mword 32))
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite HK. reflexivity.
  Qed.

  (* =================================================================== *)
  (*  [KILL] (+0x0b8): the C('U') kill-line loop.                         *)
  (*                                                                      *)
  (*  AN iLöb, NOT A FUEL INDUCTION.  [ConsoleInv.cons_res] relates        *)
  (*  [cons.e] to nothing, so the [cons.e--] bounds nothing -- and it does *)
  (*  not have to: the back edge is the TAKEN arm of the [bne] at +0x0da,  *)
  (*  and [wp_bne_taken_s_sconf] hands out a [▷ wp_next], which is what    *)
  (*  the Löb IH sits under.  Nothing is returned, so no count has to      *)
  (*  survive the loop.                                                    *)
  (* =================================================================== *)
  Definition ct_kill_prop `{CID0 : CpuId}
      (γtx γc : gname) (γu : uart_names)
      (pme : mword 64) (m0 : regfile) (K lvl : nat) (eb : bool)
      (C : iProp Σ) (b : bool) (sp0 : mword 64) : iProp Σ :=
    (wp_next (CID0 := CID0) b pme (fun (CIDk : CpuId) =>
       ∀ (M : regfile) (rr ww ee : mword 32) (bs : list (bv 8)),
         ⌜ M !!! Regidx csp_rs1 = pa_stk sp0 6%nat ⌝ -∗
         ⌜ M !!! Regidx Rs1 = a_cons ⌝ -∗
         ⌜ M !!! Regidx Rs2 = (mword_of_int 10 : mword 64) ⌝ -∗
         ⌜ M !!! Regidx Rs3 = (mword_of_int 256 : mword 64) ⌝ -∗
         ⌜ M !!! Regidx Ra5 = sign_extend' 64 ee ⌝ -∗
         ⌜ forall r : mword 5, is_cs_idx r = true -> r <> Rs1 -> r <> Rs2 -> r <> Rs3 ->
             M !!! Regidx r = m0 !!! Regidx r ⌝ -∗
         ⌜ length bs = INPUT_BUF_SIZE ⌝ -∗
         ct_exit_prop (CID0 := CID0) γc pme m0 K lvl eb C b sp0 -∗
         sie_cap_gpr M (trap_res b + (K - 6))%nat false pme -∗
         pc_is (mword_of_int (CT + 0xb8)) -∗
         cpu_own (S lvl) eb pme C false -∗
         arm_pay lvl eb pme -∗
         locked γc cpu_id -∗
         a_cons_r ↦₄ rr -∗ a_cons_w ↦₄ ww -∗ a_cons_e ↦₄ ee -∗ cons_data bs -∗
         pa_stk sp0 4 ↦₈ (m0 !!! Regidx Rs2) -∗
         pa_stk sp0 5 ↦₈ (m0 !!! Regidx Rs3) -∗
         (∃ w : mword 64, pa_stk sp0 6 ↦₈ w) -∗
         WP (Loop : expr riscv_lang)))%I.

  Lemma ct_mk_kill (γtx γc : gname) (γu : uart_names) (γv : disk_names)
      (pme : mword 64) (m0 : regfile) (K lvl : nat) (eb : bool)
      (C : iProp Σ) (b : bool) (sp0 : mword 64) :
    (consoleintr_stack <= K)%nat ->
    (Z.of_nat lvl + 2 < 2 ^ 31)%Z ->
    match lvl with O => eb | S _ => false end = b ->
    kernel_text -∗ panic_wp_any -∗
    dev_inv γu γv -∗ is_txlock γtx γu -∗ uart_sent_sub γu [] -∗
    ct_kill_prop (CID0 := CID) γtx γc γu pme m0 K lvl eb C b sp0.
  Proof.
    intros HK Hlvl Hb. subst b.
    iIntros "#Ht #Hpanic #Hdev #Htxl #Hsub".
    rewrite /ct_kill_prop.
    iLöb as "IH".
    iIntros (CIDk Hsk M rr ww ee bs)
      "%Hsp %Hs1 %Hs2 %Hs3 %Ha5 %Hthr %Hlenb EXIT Hcg Hpc Hcnt Hpay Hlocked Hrc Hwc Hec Hdat H4 H5 H6".
    iPoseProof (cnti_0b8 with "Ht") as "Hi0b8".
    iPoseProof (cnti_0ba with "Ht") as "Hi0ba".
    iPoseProof (cnti_0be with "Ht") as "Hi0be".
    iPoseProof (cnti_0c0 with "Ht") as "Hi0c0".
    iPoseProof (cnti_0c4 with "Ht") as "Hi0c4".
    (* ---- +0x0b8 c.addiw a5,a5,-1 ---- *)
    iApply (wp_caddiw_s_sconf (mword_of_int (CT + 0xb8)) Ra5 (mword_of_int 63 : mword 6)
              M (trap_res (match lvl with O => eb | S _ => false end) + (K - 6))%nat false
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi0b8").
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    iEval (rewrite Ha5 ct_addiw_dec) in "Hcg".
    set (ee' := add_vec ee (mword_of_int (-1) : mword 32)).
    set (L1 := <[Regidx Ra5 := regval_into_reg (sign_extend' 64 ee')]> M).
    assert (Hp0ba : add_vec_int (mword_of_int (CT + 0xb8) : mword 64) 2
                    = mword_of_int (CT + 0xba)) by pcw.
    iEval (rewrite Hp0ba) in "Hpc".
    (* ---- +0x0ba andi a4,a5,127 : the ring index ---- *)
    set (idxw := and_vec (sign_extend' 64 ee' : mword 64)
                   (sign_extend' 64 (mword_of_int 127 : mword 12))).
    set (idx := Z.to_nat (bv_unsigned idxw)).
    assert (Hidxb : (0 <= bv_unsigned idxw < 128)%Z)
      by (rewrite /idxw;
          apply (w32_and_mask_bound _ (mword_of_int 127) 7 ltac:(lia)
                   ltac:(vm_compute; reflexivity))).
    assert (Hidxlt : (idx < INPUT_BUF_SIZE)%nat) by (rewrite /idx /INPUT_BUF_SIZE; lia).
    assert (Hidxw : idxw = (mword_of_int (Z.of_nat idx) : mword 64)).
    { rewrite /idx Z2Nat.id; [| lia]. symmetry. apply w32_moi_unsigned. }
    assert (HL1a5 : L1 !!! Regidx Ra5 = sign_extend' 64 ee')
      by (rewrite /L1; apply upd_eq).
    assert (Hwv : and_vec (L1 !!! Regidx Ra5) (sign_extend' 64 (mword_of_int 127 : mword 12))
                  = (mword_of_int (Z.of_nat idx) : mword 64))
      by (rewrite HL1a5; exact Hidxw).
    iApply (wp_andi_s_sconf (mword_of_int (CT + 0xba)) Ra4 Ra5 (mword_of_int 127 : mword 12)
              (mword_of_int (Z.of_nat idx) : mword 64) L1
              (trap_res (match lvl with O => eb | S _ => false end) + (K - 6))%nat false
              ltac:(nz) ltac:(rdok) Hwv with "Hcg Hpc Hi0ba").
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    set (L2 := <[Regidx Ra4 := regval_into_reg (mword_of_int (Z.of_nat idx) : mword 64)]> L1).
    assert (Hp0be : add_vec_int (mword_of_int (CT + 0xba) : mword 64) 4
                    = mword_of_int (CT + 0xbe)) by pcw.
    iEval (rewrite Hp0be) in "Hpc".
    (* ---- +0x0be c.add a4,a4,s1 ---- *)
    assert (HL2a4 : L2 !!! Regidx Ra4 = (mword_of_int (Z.of_nat idx) : mword 64))
      by (rewrite /L2; apply upd_eq).
    assert (HL2s1 : L2 !!! Regidx Rs1 = a_cons).
    { rewrite /L2 upd_ne; [| reg_neq]. rewrite /L1 upd_ne; [| reg_neq]. exact Hs1. }
    iApply (wp_cadd_s_sconf (mword_of_int (CT + 0xbe)) Ra4 Rs1 L2
              (trap_res (match lvl with O => eb | S _ => false end) + (K - 6))%nat false
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi0be").
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    iEval (rewrite HL2a4 HL2s1) in "Hcg".
    set (L3 := <[Regidx Ra4 := regval_into_reg
        (add_vec (mword_of_int (Z.of_nat idx) : mword 64) a_cons)]> L2).
    assert (Hp0c0 : add_vec_int (mword_of_int (CT + 0xbe) : mword 64) 2
                    = mword_of_int (CT + 0xc0)) by pcw.
    iEval (rewrite Hp0c0) in "Hpc".
    (* ---- +0x0c0 lbu a4,24(a4) ---- *)
    destruct (cons_data_lookup_lt bs idx Hlenb Hidxlt) as [db Hlk].
    iDestruct (cons_data_acc bs idx db Hlk with "Hdat") as "[Hbyte Hdback]".
    assert (HL3a4 : L3 !!! Regidx Ra4
                    = add_vec (mword_of_int (Z.of_nat idx) : mword 64) a_cons)
      by (rewrite /L3; apply upd_eq).
    assert (Hbaddr : add_vec (L3 !!! Regidx Ra4)
                       (sign_extend' 64 (mword_of_int 24 : mword 12))
                     = pa_add a_cons (cons_buf_off + idx)).
    { rewrite HL3a4. rewrite <- (cons_byte_addr idx Hidxlt).
      rewrite (_ : add_vec (mword_of_int (Z.of_nat idx) : mword 64) a_cons
                   = add_vec a_cons (mword_of_int (Z.of_nat idx) : mword 64)); [reflexivity|].
      apply bv_eq. rewrite !add_vec64_unsigned. f_equal. ring. }
    iApply (wp_lbu_s_sconf (mword_of_int (CT + 0xc0)) Ra4 Ra4 (mword_of_int 24 : mword 12)
              L3 (trap_res (match lvl with O => eb | S _ => false end) + (K - 6))%nat
              (db : mword 8) false ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi0c0 [Hbyte]").
    { rgall. iEval (rewrite Hbaddr). iExact "Hbyte". }
    iApply wp_next_off_intro. iIntros "Hcg Hpc Hbyte". rgall.
    iEval (rewrite Hbaddr) in "Hbyte".
    iDestruct ("Hdback" with "Hbyte") as "Hdat".
    set (L4 := <[Regidx Ra4 := regval_into_reg (zero_extend' 64 (db : mword 8))]> L3).
    assert (Hp0c4 : add_vec_int (mword_of_int (CT + 0xc0) : mword 64) 4
                    = mword_of_int (CT + 0xc4)) by pcw.
    iEval (rewrite Hp0c4) in "Hpc".
    (* the register pins at [L4]: only a4 and a5 have moved *)
    assert (HthrL : forall r : mword 5, is_cs_idx r = true -> L4 !!! Regidx r = M !!! Regidx r).
    { intros r Hr.
      assert (N14 : r <> Ra4) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      assert (N15 : r <> Ra5) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      rewrite /L4 upd_ne; [| congruence]. rewrite /L3 upd_ne; [| congruence].
      rewrite /L2 upd_ne; [| congruence]. rewrite /L1 upd_ne; [| congruence]. reflexivity. }
    assert (HL4sp : L4 !!! Regidx csp_rs1 = pa_stk sp0 6%nat)
      by (rewrite (HthrL csp_rs1 ltac:(vm_compute; reflexivity)); exact Hsp).
    assert (HL4s1 : L4 !!! Regidx Rs1 = a_cons)
      by (rewrite (HthrL Rs1 ltac:(vm_compute; reflexivity)); exact Hs1).
    assert (HL4s2 : L4 !!! Regidx Rs2 = (mword_of_int 10 : mword 64))
      by (rewrite (HthrL Rs2 ltac:(vm_compute; reflexivity)); exact Hs2).
    assert (HL4s3 : L4 !!! Regidx Rs3 = (mword_of_int 256 : mword 64))
      by (rewrite (HthrL Rs3 ltac:(vm_compute; reflexivity)); exact Hs3).
    assert (HL4a4 : L4 !!! Regidx Ra4 = zero_extend' 64 (db : mword 8))
      by (rewrite /L4; apply upd_eq).
    assert (HL4a5 : L4 !!! Regidx Ra5 = sign_extend' 64 ee').
    { rewrite /L4 upd_ne; [| reg_neq]. rewrite /L3 upd_ne; [| reg_neq].
      rewrite /L2 upd_ne; [| reg_neq]. exact HL1a5. }
    set (cbv := bv_unsigned (db : mword 8)).
    assert (Hcbr : (0 <= cbv < 256)%Z) by (rewrite /cbv; apply w32_byte_range).
    (* ---- +0x0c4 beq a4,s2 : is it the newline that ends the line? ---- *)
    destruct (Z.eqb cbv 10) eqn:HNL.
    { (* the line ends here: leave WITHOUT the decrement -> +0x0ea *)
      iApply (wp_beq_taken_s_sconf (mword_of_int (CT + 0xc4)) (mword_of_int 38 : mword 13)
                Rs2 Ra4 L4 (trap_res (match lvl with O => eb | S _ => false end) + (K - 6))%nat
                false ltac:(nz) ltac:(nz)
                ltac:(rgall; rewrite HL4a4 HL4s2 w32_zext8_moi
                        (w32_eq_moi cbv 10 ltac:(lia) ltac:(lia)); exact HNL)
                ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi0c4").
      iApply bi.later_intro. iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
      assert (Hj0ea : add_vec (mword_of_int (CT + 0xc4) : mword 64)
                        (sign_extend' 64 (mword_of_int 38 : mword 13))
                      = mword_of_int (CT + 0xea)) by pcw.
      iEval (rewrite Hj0ea) in "Hpc".
      iPoseProof (cnti_0ea with "Ht") as "Hi0ea".
      iPoseProof (cnti_0ec with "Ht") as "Hi0ec".
      iPoseProof (cnti_0ee with "Ht") as "Hi0ee".
      iApply (ct_restore23 (CIDq := CIDk) γc pme m0 L4 K lvl eb C _ sp0
                (mword_of_int (CT + 0xea)) (mword_of_int (CT + 0xec))
                (mword_of_int (CT + 0xee)) (mword_of_int 11 : mword 11)
                HL4sp
                ltac:(intros r Hr N9 N18 N19; rewrite (HthrL r Hr); apply Hthr; assumption)
                ltac:(pcw) ltac:(pcw) ltac:(pcw) ltac:(vm_compute; reflexivity)
                ltac:(wp_next_chain)
                with "Hi0ea Hi0ec Hi0ee Hcg Hpc Hcnt Hpay Hlocked [Hrc Hwc Hec Hdat] H4 H5 H6 EXIT").
      iExists rr, ww, ee, bs. iFrame "Hrc Hwc Hec Hdat". iPureIntro. exact Hlenb. }
    (* ---- an ordinary byte: erase it ---- *)
    iApply (wp_beq_fall_s_sconf (mword_of_int (CT + 0xc4)) (mword_of_int 38 : mword 13)
              Rs2 Ra4 L4 (trap_res (match lvl with O => eb | S _ => false end) + (K - 6))%nat
              false ltac:(nz) ltac:(nz)
              ltac:(rgall; rewrite HL4a4 HL4s2 w32_zext8_moi
                      (w32_eq_moi cbv 10 ltac:(lia) ltac:(lia)); exact HNL)
              with "Hcg Hpc Hi0c4").
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    assert (Hp0c8 : add_vec_int (mword_of_int (CT + 0xc4) : mword 64) 4
                    = mword_of_int (CT + 0xc8)) by pcw.
    iEval (rewrite Hp0c8) in "Hpc".
    (* ---- +0x0c8 sw a5,160(s1) : cons.e-- ---- *)
    assert (Hea : add_vec (L4 !!! Regidx Rs1)
                    (sign_extend' 64 (mword_of_int 160 : mword 12)) = a_cons_e)
      by (rewrite HL4s1; reflexivity).
    iPoseProof (cnti_0c8 with "Ht") as "Hi0c8".
    iApply (wp_sw_s_sconf (mword_of_int (CT + 0xc8)) Ra5 Rs1 (mword_of_int 160 : mword 12)
              L4 (trap_res (match lvl with O => eb | S _ => false end) + (K - 6))%nat ee false
              with "Hcg Hpc Hi0c8 [Hec]").
    { rgall. iEval (rewrite Hea). iExact "Hec". }
    iApply wp_next_off_intro. iIntros "Hcg Hpc Hec". rgall.
    iEval (rewrite Hea HL4a5 trunc32_sext) in "Hec".
    assert (Hp0cc : add_vec_int (mword_of_int (CT + 0xc8) : mword 64) 4
                    = mword_of_int (CT + 0xcc)) by pcw.
    iEval (rewrite Hp0cc) in "Hpc".
    (* ---- +0x0cc c.mv a0,s3 ; +0x0ce jal consputc ---- *)
    iPoseProof (cnti_0cc with "Ht") as "Hi0cc".
    iApply (wp_cmv_s_sconf (mword_of_int (CT + 0xcc)) Ra0 Rs3 L4
              (trap_res (match lvl with O => eb | S _ => false end) + (K - 6))%nat false
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi0cc").
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    set (L5 := <[Regidx Ra0 := regval_into_reg
        (add_vec zero_reg (L4 !!! Regidx Rs3))]> L4).
    assert (Hp0ce : add_vec_int (mword_of_int (CT + 0xcc) : mword 64) 2
                    = mword_of_int (CT + 0xce)) by pcw.
    iEval (rewrite Hp0ce) in "Hpc".
    iPoseProof (cnti_0ce with "Ht") as "Hi0ce".
    iApply (wp_jal_s_sconf (mword_of_int (CT + 0xce)) Rra (mword_of_int 2096896 : mword 21)
              L5 (trap_res (match lvl with O => eb | S _ => false end) + (K - 6))%nat false
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi0ce").
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    set (L6 := <[Regidx Rra := regval_into_reg
        (add_vec_int (mword_of_int (CT + 0xce) : mword 64) 4)]> L5).
    assert (Hjcp : add_vec (mword_of_int (CT + 0xce) : mword 64)
                     (sign_extend' 64 (mword_of_int 2096896 : mword 21))
                   = mword_of_int KernelSyms.consputc) by pcw.
    iEval (rewrite Hjcp) in "Hpc".
    assert (HL6ra : L6 !!! Regidx Rra
                    = add_vec_int (mword_of_int (CT + 0xce) : mword 64) 4)
      by (rewrite /L6; apply upd_eq).
    iApply (Consputc.wp_consputc_sconf γtx γu γv L6
              (trap_res (match lvl with O => eb | S _ => false end) + (K - 6))%nat
              [] (S lvl) eb C false pme
              ltac:(unfold consoleintr_stack, consputc_stack in *; lia) ltac:(lia)
              with "Hcg Hcnt Ht Hpc Hpanic Hdev Htxl Hsub").
    iApply wp_next_off_intro. iIntros (mcp cs) "Hcg Hcnt Hpc [%Hcpcs %Hcpra] _". rgall.
    iEval (rewrite HL6ra) in "Hpc".
    assert (Hp0d2 : ret_pc (add_vec_int (mword_of_int (CT + 0xce) : mword 64) 4)
                    = (mword_of_int (CT + 0xd2) : mword 64)) by pcw.
    iEval (rewrite Hp0d2) in "Hpc".
    assert (HthrC : forall r : mword 5, is_cs_idx r = true -> mcp !!! Regidx r = L4 !!! Regidx r).
    { intros r Hr.
      assert (N1 : r <> Rra) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      assert (N10 : r <> Ra0) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      rewrite (callee_saved_lookup Hcpcs r Hr).
      rewrite /L6 upd_ne; [| congruence]. rewrite /L5 upd_ne; [| congruence]. reflexivity. }
    assert (Hmcps1 : mcp !!! Regidx Rs1 = a_cons)
      by (rewrite (HthrC Rs1 ltac:(vm_compute; reflexivity)); exact HL4s1).
    (* ---- +0x0d2 lw a5,160(s1) ; +0x0d6 lw a4,156(s1) ---- *)
    assert (Hea2 : add_vec (mcp !!! Regidx Rs1)
                     (sign_extend' 64 (mword_of_int 160 : mword 12)) = a_cons_e)
      by (rewrite Hmcps1; reflexivity).
    iPoseProof (cnti_0d2 with "Ht") as "Hi0d2".
    iApply (wp_lw_s_sconf (mword_of_int (CT + 0xd2)) Ra5 Rs1 (mword_of_int 160 : mword 12)
              mcp (trap_res (match lvl with O => eb | S _ => false end) + (K - 6))%nat
              ee' false ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi0d2 [Hec]").
    { rgall. iEval (rewrite Hea2). iExact "Hec". }
    iApply wp_next_off_intro. iIntros "Hcg Hpc Hec". rgall. iEval (rewrite Hea2) in "Hec".
    set (L7 := <[Regidx Ra5 := regval_into_reg (sign_extend' 64 ee')]> mcp).
    assert (Hp0d6 : add_vec_int (mword_of_int (CT + 0xd2) : mword 64) 4
                    = mword_of_int (CT + 0xd6)) by pcw.
    iEval (rewrite Hp0d6) in "Hpc".
    assert (HL7s1 : L7 !!! Regidx Rs1 = a_cons)
      by (rewrite /L7 upd_ne; [exact Hmcps1 | reg_neq]).
    assert (Hwa2 : add_vec (L7 !!! Regidx Rs1)
                     (sign_extend' 64 (mword_of_int 156 : mword 12)) = a_cons_w)
      by (rewrite HL7s1; reflexivity).
    iPoseProof (cnti_0d6 with "Ht") as "Hi0d6".
    iApply (wp_lw_s_sconf (mword_of_int (CT + 0xd6)) Ra4 Rs1 (mword_of_int 156 : mword 12)
              L7 (trap_res (match lvl with O => eb | S _ => false end) + (K - 6))%nat
              ww false ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi0d6 [Hwc]").
    { rgall. iEval (rewrite Hwa2). iExact "Hwc". }
    iApply wp_next_off_intro. iIntros "Hcg Hpc Hwc". rgall. iEval (rewrite Hwa2) in "Hwc".
    set (L8 := <[Regidx Ra4 := regval_into_reg (sign_extend' 64 ww)]> L7).
    assert (Hp0da : add_vec_int (mword_of_int (CT + 0xd6) : mword 64) 4
                    = mword_of_int (CT + 0xda)) by pcw.
    iEval (rewrite Hp0da) in "Hpc".
    assert (HL8a4 : L8 !!! Regidx Ra4 = sign_extend' 64 ww)
      by (rewrite /L8; apply upd_eq).
    assert (HL8a5 : L8 !!! Regidx Ra5 = sign_extend' 64 ee').
    { rewrite /L8 upd_ne; [| reg_neq]. rewrite /L7; apply upd_eq. }
    assert (HthrL8 : forall r : mword 5, is_cs_idx r = true -> L8 !!! Regidx r = M !!! Regidx r).
    { intros r Hr.
      assert (N14 : r <> Ra4) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      assert (N15 : r <> Ra5) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      rewrite /L8 upd_ne; [| congruence]. rewrite /L7 upd_ne; [| congruence].
      rewrite (HthrC r Hr). apply HthrL; exact Hr. }
    iPoseProof (cnti_0da with "Ht") as "Hi0da".
    destruct (neq_vec (sign_extend' 64 ww : mword 64) (sign_extend' 64 ee')) eqn:Hmore.
    { (* more to erase: THE BACK EDGE to +0x0b8 *)
      iApply (wp_bne_taken_s_sconf (mword_of_int (CT + 0xda)) (mword_of_int 8158 : mword 13)
                Ra5 Ra4 L8 (trap_res (match lvl with O => eb | S _ => false end) + (K - 6))%nat
                false ltac:(nz) ltac:(nz)
                ltac:(rgall; rewrite HL8a4 HL8a5; exact Hmore)
                ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi0da").
      (* the Löb back edge: the [▷] has to come off "IH", not just the goal *)
      iNext. iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
      assert (Hbk : add_vec (mword_of_int (CT + 0xda) : mword 64)
                      (sign_extend' 64 (mword_of_int 8158 : mword 13))
                    = mword_of_int (CT + 0xb8)) by pcw.
      iEval (rewrite Hbk) in "Hpc".
      iSpecialize ("IH" $! CIDk with "[%]"); [wp_next_chain|].
      iApply ("IH" $! L8 rr ww ee' bs with "[%] [%] [%] [%] [%] [%] [%]
                EXIT Hcg Hpc Hcnt Hpay Hlocked Hrc Hwc Hec Hdat H4 H5 H6").
      - rewrite (HthrL8 csp_rs1 ltac:(vm_compute; reflexivity)). exact Hsp.
      - rewrite (HthrL8 Rs1 ltac:(vm_compute; reflexivity)). exact Hs1.
      - rewrite (HthrL8 Rs2 ltac:(vm_compute; reflexivity)). exact Hs2.
      - rewrite (HthrL8 Rs3 ltac:(vm_compute; reflexivity)). exact Hs3.
      - exact HL8a5.
      - intros r Hr N9 N18 N19. rewrite (HthrL8 r Hr). apply Hthr; assumption.
      - exact Hlenb. }
    (* the line is empty: fall out at +0x0de *)
    iApply (wp_bne_fall_s_sconf (mword_of_int (CT + 0xda)) (mword_of_int 8158 : mword 13)
              Ra5 Ra4 L8 (trap_res (match lvl with O => eb | S _ => false end) + (K - 6))%nat
              false ltac:(nz) ltac:(nz)
              ltac:(rgall; rewrite HL8a4 HL8a5; exact Hmore) with "Hcg Hpc Hi0da").
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    assert (Hp0de : add_vec_int (mword_of_int (CT + 0xda) : mword 64) 4
                    = mword_of_int (CT + 0xde)) by pcw.
    iEval (rewrite Hp0de) in "Hpc".
    iPoseProof (cnti_0de with "Ht") as "Hi0de".
    iPoseProof (cnti_0e0 with "Ht") as "Hi0e0".
    iPoseProof (cnti_0e2 with "Ht") as "Hi0e2".
    iApply (ct_restore23 (CIDq := CIDk) γc pme m0 L8 K lvl eb C _ sp0
              (mword_of_int (CT + 0xde)) (mword_of_int (CT + 0xe0))
              (mword_of_int (CT + 0xe2)) (mword_of_int 17 : mword 11)
              ltac:(rewrite (HthrL8 csp_rs1 ltac:(vm_compute; reflexivity)); exact Hsp)
              ltac:(intros r Hr N9 N18 N19; rewrite (HthrL8 r Hr); apply Hthr; assumption)
              ltac:(pcw) ltac:(pcw) ltac:(pcw) ltac:(vm_compute; reflexivity)
              ltac:(wp_next_chain)
              with "Hi0de Hi0e0 Hi0e2 Hcg Hpc Hcnt Hpay Hlocked [Hrc Hwc Hec Hdat] H4 H5 H6 EXIT").
    iExists rr, ww, ee', bs. iFrame "Hrc Hwc Hec Hdat". iPureIntro. exact Hlenb.
  Qed.

  (* [cons.e++]: the [addiw]/[sw] round trip commits [e + 1] at width 32 *)
  Lemma ct_sw_inc (e : mword 32) :
    trunc32 (sign_extend' 64 (subrange_vec_dec
       (add_vec (sign_extend' 64 e) (sign_extend' 64 (mword_of_int 1 : mword 12))) 31 0))
    = add_vec e (mword_of_int 1 : mword 32).
  Proof.
    rewrite <- trunc32_subrange. rewrite trunc32_sext trunc32_add trunc32_sext.
    assert (HK : trunc32 (sign_extend' 64 (mword_of_int 1 : mword 12))
                 = (mword_of_int 1 : mword 32))
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite HK. reflexivity.
  Qed.

End ProofConsoleintr.

End ConsoleintrProof.
