(* ProofStrlen.v -- the whole-function WP for xv6's strlen(), over the
   SIE-agnostic sconf world.

     int strlen(const char *s) { int n; for (n = 0; s[n]; n++) ; return n; }

   Contract: SpecStrlen.v.  Eighteen instructions, a 2-slot frame, no callees,
   two arms joining at the epilogue (+0x20).

   THE MACHINE (offsets into CodeStrlen.v's byte-verified listing):

     +0x00..+0x06   the 2-slot prologue
     +0x08 lbu a5,0(a0)
     +0x0c beqz a5 -> +0x28        s[0] is the NUL: return 0
     +0x0e addi a5,a0,1            a5 := s + 1
     +0x12 mv a3,a5                <-- loop head; a3 = s + 1 + t
     +0x14 addi a5,a5,1
     +0x16 lbu a4,-1(a5)           the byte AT a3
     +0x1a bnez a4 -> +0x12
     +0x1c subw a0,a3,a0           a0 STILL HOLDS s, so this is a3 - s
     +0x20..+0x26   the epilogue, shared with the +0x28 arm

   FOUR THINGS WORTH KEEPING.

   1. [a0] IS PART OF THE INVARIANT, not a scratch register.  gcc never writes
      a0 between entry and +0x1c, and the return value is the pointer
      difference computed there -- so the loop invariant carries [a0 = s], and
      the answer comes out of [ByteCursor.bc_subw_diff] (the 32-bit narrowing
      a C [int] return imposes cancels the base, wherever the buffer sits).

   2. THE LOOP INDEX IS OFF BY ONE and gcc accesses BEHIND the cursor: at the
      head [a3 = a5 = s + 1 + t], the body bumps a5 and then reads [-1(a5)],
      i.e. the byte at a3.  So one iteration inspects byte [S t], the
      invariant is [bb_nonul f (S t)] (bytes 0..t known non-NUL) together with
      [S t + rem = k], and byte 0 is inspected before the loop.

   3. THE BRANCH IS NEVER A CASE SPLIT.  With [S t + rem = k] the loop KNOWS
      which way the [bnez] goes: [rem = 0] means the byte is the terminator
      (fall through), [rem = S _] means it is not ([bb_cstr]'s no-earlier-NUL
      half).  That is why the induction is on [rem] and not on a fuel bound --
      the measure decreases by exactly one -- and why neither arm has to
      inspect the loaded byte's value.

   4. THE SHARED THREE-INSTRUCTION PROBE IS ITS OWN LEMMA ([sl_probe]).  Both
      arms of the [bnez] run +0x12..+0x16 first, and the [rem]-induction puts
      the two arms in different goals; factoring the probe out is what keeps
      it written once.

   EXPLICIT-CPUID: the whole function threads a generic [b : bool] (interrupts
   may be enabled throughout), exactly the shape of ProofPlicinit.v.  Every
   private helper below ([sl_tail], [sl_probe], [sl_loop]) is itself a
   fragment of the whole-function contract, so each one's own continuation
   argument is [wp_next]-wrapped and discharged the same two-step way the
   outermost function is; a caller then treats a call to one of them exactly
   like a leaf application, peeling a fresh [(CIDk, Hsk)] off its result. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre lifting.
From iris.base_logic.lib Require Import gen_heap invariants ghost_var.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import RiscvModelBytes RiscvPtsto RiscvLang RiscvExtras.
Require Import RegFile InstrBytes WpMmodeLeafBase.
Require Import SmodeCore.
Require Import StackOwn CalleeSaved KernelText.
Require Import KernelRvcDecode.
Require Import WpSconfAlu WpSconfMem WpSconfBtype WpSconfCtl WpSmodeIntr.
Require Import HartTp WpNext IntrDefs.
Require Import ByteCursor ByteBuf.
Require Import CodeStrlen.
Require Import SpecStrlen.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Import Defs.
Local Open Scope Z_scope.

(* [rget m k] at a NON-tp index is the plain map lookup ([rget_ne]) -- the
   one-line bridge from a leaf's [rget] to the register-map facts a
   whole-function proof already has.  Written name-free (durable-notes: an
   Ltac body cannot mention a hypothesis by literal name). *)
Local Ltac rgne :=
  rewrite rget_ne;
  [ | let H1 := fresh in let H2 := fresh in
      intro H1; injection H1 as H2; vm_compute in H2; congruence ].

Module StrlenProof : STRLEN.

Section ProofStrlen.
  Context `{!riscvGS Σ, !sieG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Context {kt : ktier}.
  Notation Rra := (mword_of_int 1 : mword 5).
  Notation Rs0 := (mword_of_int 8 : mword 5).
  Notation Ra0 := (mword_of_int 10 : mword 5).
  Notation Ra3 := (mword_of_int 13 : mword 5).
  Notation Ra4 := (mword_of_int 14 : mword 5).
  Notation Ra5 := (mword_of_int 15 : mword 5).

  Local Ltac reg_neq :=
    lazymatch goal with |- ?a <> ?b =>
      tryif unify a b then fail else (vm_compute; discriminate) end.

  (* a callee-saved index is never one of the scratch indices a body writes.
     [apply cs_ne] first unifies the conclusion, which is what determines the
     scratch index, so the [vm_compute] side goal is closed. *)
  Local Lemma cs_ne (k r : mword 5) :
    is_cs_idx k = false -> is_cs_idx r = true -> Regidx r <> Regidx k.
  Proof. intros Hk Hr He. symmetry in He. exact (is_cs_idx_true_neq k r Hk Hr He). Qed.

  (* peel an insert tower with a SYMBOLIC index, given the index's
     disequalities as [r <> ...] hypotheses in scope.  The two names must be
     [fresh]-bound: an unbound identifier in an [Ltac] BODY is resolved as a
     global reference when the tactic is DEFINED, so the plain
     [intro He; injection He as He'] spelling fails at definition time with
     "The reference He was not found". *)
  Local Ltac peel_sym :=
    rewrite upd_ne;
    [| let H := fresh "Hpe" in
       let H' := fresh "Hpe" in
       intro H; injection H as H'; congruence ].

  (* --- the frame, and the three cursor steps --------------------------- *)

  Local Lemma sl_push (X : mword 64) :
    add_vec X (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6))) = pa_stk X 2.
  Proof. unfold pa_stk, add_vec_int. apply f_equal. apply bv_eq; vm_compute; reflexivity. Qed.

  (* +0x0e [addi a5,a0,1] : the FIRST cursor, one past the base *)
  Local Lemma sl_bump1 (p : mword 64) :
    add_vec p (sign_extend' 64 (mword_of_int 1 : mword 12)) = pa_add p 1.
  Proof. unfold pa_add, add_vec_int. apply f_equal. apply bv_eq; vm_compute; reflexivity. Qed.

  (* +0x14 [c.addi a5,a5,1] *)
  Local Lemma sl_step (p : mword 64) (j : nat) :
    add_vec (pa_add p j) (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6)))
    = pa_add p (S j).
  Proof. apply pa_add_step. apply bv_eq; vm_compute; reflexivity. Qed.

  (* +0x16 [lbu a4,-1(a5)] : gcc bumps first and accesses behind the cursor *)
  Local Lemma sl_back (p : mword 64) (j : nat) :
    add_vec (pa_add p (S j)) (sign_extend' 64 (mword_of_int 4095 : mword 12)) = pa_add p j.
  Proof. apply pa_add_back1. apply bv_eq; vm_compute; reflexivity. Qed.

  (* ================================================================== *)
  (*  THE EPILOGUE (+0x20 .. +0x26), entered by both arms.               *)
  (* ================================================================== *)
  Local Lemma sl_tail `{CID0 : CpuId}
      (mm Mt : regfile) (K : nat) (rv sp0 ra0 s00 : mword 64) (b : bool) (p : mword 64) :
    (2 <= K)%nat ->
    mm !!! Regidx csp_rs1 = sp0 ->
    mm !!! Regidx Rra = ra0 ->
    mm !!! Regidx Rs0 = s00 ->
    Mt !!! Regidx csp_rs1 = pa_stk sp0 2 ->
    Mt !!! Regidx Ra0 = rv ->
    (forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 -> r <> Rs0 ->
        Mt !!! Regidx r = mm !!! Regidx r) ->
    sie_cap_gpr kt (CID := CID0) Mt (K - 2)%nat b p -∗
    kernel_text -∗
    pc_is (CID := CID0) (mword_of_int (KernelSyms.strlen + 0x20) : mword 64) -∗
    word_pointsto (pa_stk sp0 1) (DfracOwn 1) ra0 -∗
    word_pointsto (pa_stk sp0 2) (DfracOwn 1) s00 -∗
    wp_next (CID0 := CID0) b p (fun (CID : CpuId) =>
      ∀ mf : regfile,
        ⌜callee_saved mm mf /\ mf !!! Regidx Ra0 = rv⌝ -∗
        sie_cap_gpr kt mf K b p -∗
        pc_is (ret_pc ra0) -∗
        WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HK Hsp0 Hra0 Hs00 Hmtsp Hmta0 Hthr.
    iIntros "Hcg #Htext Hpc Hb1 Hb2 Hcont".
    iPoseProof (sli_20 with "Htext") as "Hi20".
    iPoseProof (sli_22 with "Htext") as "Hi22".
    iPoseProof (sli_24 with "Htext") as "Hi24".
    iPoseProof (sli_26 with "Htext") as "Hi26".
    (* ---- +0x20: c.ldsp ra,8(sp) ---- *)
    assert (Hpa1 : add_vec (Mt !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000")))
                   = pa_stk sp0 1).
    { rewrite Hmtsp. unfold pa_stk, add_vec_int. rewrite !pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    iEval (rewrite -Hpa1) in "Hb1".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.strlen + 0x20))
              (mword_of_int 1 : mword 6) Rra Mt (K - 2)%nat ra0 b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi20 Hb1").
    iIntros (CID1 Hs1) "Hcg Hpc Hb1".
    iEval (rewrite Hpa1) in "Hb1".
    set (T1 := <[Regidx Rra := regval_into_reg ra0]> Mt).
    change (<[Regidx Rra := regval_into_reg ra0]> Mt) with T1.
    assert (Hp22 : add_vec_int (mword_of_int (KernelSyms.strlen + 0x20) : mword 64) 2
                   = mword_of_int (KernelSyms.strlen + 0x22))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp22) in "Hpc".
    assert (HT1sp : T1 !!! Regidx csp_rs1 = pa_stk sp0 2)
      by (rewrite /T1 upd_ne; [exact Hmtsp | reg_neq]).
    (* ---- +0x22: c.ldsp s0,0(sp) ---- *)
    assert (Hpa2 : add_vec (T1 !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000")))
                   = pa_stk sp0 2).
    { rewrite HT1sp. unfold pa_stk, add_vec_int. rewrite !pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    iEval (rewrite -Hpa2) in "Hb2".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.strlen + 0x22))
              (mword_of_int 0 : mword 6) Rs0 T1 (K - 2)%nat s00 b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi22 Hb2").
    iIntros (CID2 Hs2) "Hcg Hpc Hb2".
    iEval (rewrite Hpa2) in "Hb2".
    set (T2 := <[Regidx Rs0 := regval_into_reg s00]> T1).
    change (<[Regidx Rs0 := regval_into_reg s00]> T1) with T2.
    assert (Hp24 : add_vec_int (mword_of_int (KernelSyms.strlen + 0x22) : mword 64) 2
                   = mword_of_int (KernelSyms.strlen + 0x24))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp24) in "Hpc".
    assert (HT2sp : T2 !!! Regidx csp_rs1 = pa_stk sp0 2)
      by (rewrite /T2 upd_ne; [exact HT1sp | reg_neq]).
    (* ---- +0x24: c.addi sp,16 (the frame pop) ---- *)
    assert (Hwv : add_vec (T2 !!! Regidx csp_rs1)
                    (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6))) = sp0)
      by (rewrite HT2sp; apply stk_pop_16).
    assert (Hpop : T2 !!! Regidx csp_rs1
                   = pa_stk (add_vec (T2 !!! Regidx csp_rs1)
                       (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6)))) 2)
      by (rewrite Hwv; exact HT2sp).
    iDestruct (stack_own_2_intro sp0 ra0 s00 with "Hb1 Hb2") as "Hframe".
    iEval (rewrite -Hwv) in "Hframe".
    iApply (wp_caddi_sp_pop_s_sconf (mword_of_int (KernelSyms.strlen + 0x24))
              (mword_of_int 16 : mword 6) T2 (K - 2)%nat 2 b Hpop
              with "Hcg Hpc Hi24 Hframe").
    iIntros (CID3 Hs3) "Hcg Hpc".
    assert (Hnk : ((K - 2) + 2)%nat = K) by lia.
    iEval (rewrite Hnk) in "Hcg".
    set (T3 := <[Regidx csp_rs1 := regval_into_reg
                  (add_vec (T2 !!! Regidx csp_rs1)
                     (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6))))]> T2).
    change (<[Regidx csp_rs1 := regval_into_reg
               (add_vec (T2 !!! Regidx csp_rs1)
                  (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6))))]> T2) with T3.
    assert (Hp26 : add_vec_int (mword_of_int (KernelSyms.strlen + 0x24) : mword 64) 2
                   = mword_of_int (KernelSyms.strlen + 0x26))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp26) in "Hpc".
    (* ---- +0x26: c.ret ---- *)
    assert (HT3ra : T3 !!! Regidx Rra = ra0).
    { rewrite /T3 upd_ne; [| reg_neq]. rewrite /T2 upd_ne; [| reg_neq].
      rewrite /T1 upd_eq. reflexivity. }
    assert (HT3ra' : forall CID' : CpuId, rget (CID := CID') T3 Rra = ra0)
      by (intros CID'; rgne; exact HT3ra).
    iApply (wp_cret_s_sconf (mword_of_int (KernelSyms.strlen + 0x26)) Rra T3 K b
              ltac:(vm_compute; discriminate) with "Hcg Hpc Hi26").
    iIntros (CID4 Hs4) "Hcg Hpc".
    iEval (rewrite HT3ra') in "Hpc".
    (* ---- the postcondition ---- *)
    assert (HT3a0 : T3 !!! Regidx Ra0 = rv).
    { rewrite /T3 upd_ne; [| reg_neq]. rewrite /T2 upd_ne; [| reg_neq].
      rewrite /T1 upd_ne; [| reg_neq]. exact Hmta0. }
    (* sp and s0 were restored; every other callee-saved register was threaded *)
    assert (Hgen : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 -> r <> Rs0 ->
                     T3 !!! Regidx r = mm !!! Regidx r).
    { intros r Hr Ncsp Ns0.
      rewrite /T3 upd_ne; [| intro He; injection He as He'; congruence].
      rewrite /T2 upd_ne; [| intro He; injection He as He'; congruence].
      rewrite /T1 upd_ne; [| apply cs_ne; [vm_compute; reflexivity | exact Hr]].
      apply Hthr; assumption. }
    iSpecialize ("Hcont" $! CID4 with "[%]"); [wp_next_chain|].
    iApply ("Hcont" $! T3 with "[%] Hcg Hpc").
    split; [| exact HT3a0].
    (* [split_and!] on [callee_saved mm T3] yields its 13 conjuncts IN ORDER
       (sp, s0, s1, s2, .., s11) -- verified directly, since a bullet count
       that does not match the order is a silent mis-proof rather than an
       error at THIS line.  sp and s0 are the two frame registers restored by
       name (bullets 1-2); the other 11 (s1..s11) were merely threaded, via
       [Hgen] (which itself excludes sp and s0, since those are NOT covered by
       the thread-through hypotheses [Hthr]/[Hs00]). *)
    unfold callee_saved. split_and!.
    - rewrite /T3 upd_eq Hwv. symmetry. exact Hsp0.
    - rewrite /T3 upd_ne; [| reg_neq]. rewrite /T2 upd_eq. symmetry. exact Hs00.
    - apply Hgen; [vm_compute; reflexivity | reg_neq | reg_neq].
    - apply Hgen; [vm_compute; reflexivity | reg_neq | reg_neq].
    - apply Hgen; [vm_compute; reflexivity | reg_neq | reg_neq].
    - apply Hgen; [vm_compute; reflexivity | reg_neq | reg_neq].
    - apply Hgen; [vm_compute; reflexivity | reg_neq | reg_neq].
    - apply Hgen; [vm_compute; reflexivity | reg_neq | reg_neq].
    - apply Hgen; [vm_compute; reflexivity | reg_neq | reg_neq].
    - apply Hgen; [vm_compute; reflexivity | reg_neq | reg_neq].
    - apply Hgen; [vm_compute; reflexivity | reg_neq | reg_neq].
    - apply Hgen; [vm_compute; reflexivity | reg_neq | reg_neq].
    - apply Hgen; [vm_compute; reflexivity | reg_neq | reg_neq].
  Qed.

  (* ================================================================== *)
  (*  THE PROBE (+0x12 .. +0x16): both arms of the [bnez] run it.         *)
  (* ================================================================== *)
  Local Lemma sl_probe `{CID0 : CpuId}
      (M : regfile) (Kv : nat) (dq : dfrac) (s : mword 64) (t : nat) (bt : mword 8) (b : bool) (p : mword 64) :
    M !!! Regidx Ra5 = pa_add s (S t) ->
    sie_cap_gpr kt (CID := CID0) M Kv b p -∗
    kernel_text -∗
    pc_is (CID := CID0) (mword_of_int (KernelSyms.strlen + 0x12) : mword 64) -∗
    (pa_add s (S t)) ↦ₘ{dq} bt -∗
    wp_next (CID0 := CID0) b p (fun (CID : CpuId) =>
      ∀ Mp : regfile,
        ⌜Mp !!! Regidx Ra3 = pa_add s (S t)⌝ -∗
        ⌜Mp !!! Regidx Ra5 = pa_add s (S (S t))⌝ -∗
        ⌜Mp !!! Regidx Ra4 = zero_extend' 64 bt⌝ -∗
        ⌜forall r : mword 5, r <> Ra3 -> r <> Ra4 -> r <> Ra5 ->
            Mp !!! Regidx r = M !!! Regidx r⌝ -∗
        sie_cap_gpr kt Mp Kv b p -∗
        pc_is (mword_of_int (KernelSyms.strlen + 0x1a) : mword 64) -∗
        (pa_add s (S t)) ↦ₘ{dq} bt -∗
        WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Ha5.
    iIntros "Hcg #Htext Hpc Hbyte Hcont".
    iPoseProof (sli_12 with "Htext") as "Hi12".
    iPoseProof (sli_14 with "Htext") as "Hi14".
    iPoseProof (sli_16 with "Htext") as "Hi16".
    (* ---- +0x12: c.mv a3,a5 ---- *)
    assert (HMa5' : rget M Ra5 = pa_add s (S t)) by (rgne; exact Ha5).
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.strlen + 0x12)) Ra3 Ra5 M Kv b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi12").
    iIntros (CID1 Hs1) "Hcg Hpc".
    set (P1 := <[Regidx Ra3 := regval_into_reg (add_vec zero_reg (rget M Ra5))]> M).
    change (<[Regidx Ra3 := regval_into_reg (add_vec zero_reg (rget M Ra5))]> M) with P1.
    assert (HP1a3 : P1 !!! Regidx Ra3 = pa_add s (S t)).
    { rewrite /P1 upd_eq add_vec_zero_l. exact HMa5'. }
    assert (HP1a5 : P1 !!! Regidx Ra5 = pa_add s (S t))
      by (rewrite /P1 upd_ne; [exact Ha5 | reg_neq]).
    assert (HP1a5' : rget P1 Ra5 = pa_add s (S t)) by (rgne; exact HP1a5).
    assert (Hp14 : add_vec_int (mword_of_int (KernelSyms.strlen + 0x12) : mword 64) 2
                   = mword_of_int (KernelSyms.strlen + 0x14))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp14) in "Hpc".
    (* ---- +0x14: c.addi a5,a5,1 ---- *)
    iApply (wp_caddi_s_sconf (mword_of_int (KernelSyms.strlen + 0x14)) Ra5
              (mword_of_int 1 : mword 6) P1 Kv b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi14").
    iIntros (CID2 Hs2) "Hcg Hpc".
    set (P2 := <[Regidx Ra5 := regval_into_reg
                  (add_vec (rget P1 Ra5)
                     (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6))))]> P1).
    change (<[Regidx Ra5 := regval_into_reg
               (add_vec (rget P1 Ra5)
                  (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6))))]> P1) with P2.
    assert (HP2a5 : P2 !!! Regidx Ra5 = pa_add s (S (S t))).
    { rewrite /P2 upd_eq HP1a5'. apply sl_step. }
    assert (HP2a3 : P2 !!! Regidx Ra3 = pa_add s (S t))
      by (rewrite /P2 upd_ne; [exact HP1a3 | reg_neq]).
    assert (HP2a5' : rget P2 Ra5 = pa_add s (S (S t))) by (rgne; exact HP2a5).
    assert (Hp16 : add_vec_int (mword_of_int (KernelSyms.strlen + 0x14) : mword 64) 2
                   = mword_of_int (KernelSyms.strlen + 0x16))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp16) in "Hpc".
    (* ---- +0x16: lbu a4,-1(a5) ---- *)
    iApply (wp_lbu_s_sconf (mword_of_int (KernelSyms.strlen + 0x16)) Ra4 Ra5
              (mword_of_int 4095 : mword 12) P2 Kv bt b (dqm:=dq)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi16 [Hbyte]").
    { iEval (rewrite HP2a5' (sl_back s (S t))). iExact "Hbyte". }
    iIntros (CID3 Hs3) "Hcg Hpc Hbyte".
    iEval (rewrite HP2a5' (sl_back s (S t))) in "Hbyte".
    set (P3 := <[Regidx Ra4 := regval_into_reg (zero_extend' 64 bt)]> P2).
    change (<[Regidx Ra4 := regval_into_reg (zero_extend' 64 bt)]> P2) with P3.
    assert (Hp1a : add_vec_int (mword_of_int (KernelSyms.strlen + 0x16) : mword 64) 4
                   = mword_of_int (KernelSyms.strlen + 0x1a))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp1a) in "Hpc".
    iSpecialize ("Hcont" $! CID3 with "[%]"); [wp_next_chain|].
    iApply ("Hcont" $! P3 with "[%] [%] [%] [%] Hcg Hpc Hbyte").
    - rewrite /P3 upd_ne; [exact HP2a3 | reg_neq].
    - rewrite /P3 upd_ne; [exact HP2a5 | reg_neq].
    - rewrite /P3 upd_eq. reflexivity.
    - intros r N3 N4 N5. rewrite /P3. peel_sym.
      rewrite /P2. peel_sym. rewrite /P1. peel_sym. reflexivity.
  Qed.

  (* ================================================================== *)
  (*  THE LOOP (+0x12 head), by induction on the bytes still to inspect.  *)
  (* ================================================================== *)
  (* TWO different harts, deliberately kept separate.  [CIDh] is [Hcont]'s
     [wp_next] anchor: [Hcont] is supplied ONCE, by [sl_loop]'s OWN caller, and
     is forwarded UNCHANGED across every recursive call -- so its type (hence
     [CIDh]) must stay FIXED for the whole induction, which is why [CIDh] is a
     LEMMA parameter (outside the "forall rem t M", so [induction rem] never
     touches it), exactly like [sl_tail]/[sl_probe]'s leading hart.  [CID0], by
     contrast, is quantified TOGETHER WITH [rem t M]: it is THIS iteration's
     entry hart, and a hart-migrating step inside one iteration can land the
     NEXT iteration's [sie_cap_gpr] on a different hart than the one this
     iteration started on, so it must be free to change at each recursive
     step -- a single hart shared with [CIDh] would pin every iteration to the
     outermost entry hart, silently false as soon as [b] can flip [true]. *)
  Local Lemma sl_loop
      (mm : regfile) (n k : nat) (f : nat -> bv 8) (K : nat) (dq : dfrac)
      (s sp0 : mword 64) (b : bool) (p : mword 64) (CIDh : CpuId) :
    (k < n)%nat -> bb_cstr f k -> (Z.of_nat k < 2147483648)%Z ->
    forall (rem t : nat) (M : regfile) (CID0 : CpuId),
    (b = false \/ p = zero_reg -> (CID0 : CPU) = (CIDh : CPU)) ->
    (S t + rem = k)%nat -> bb_nonul f (S t) ->
    M !!! Regidx csp_rs1 = pa_stk sp0 2 ->
    M !!! Regidx Ra0 = s ->
    M !!! Regidx Ra5 = pa_add s (S t) ->
    (forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 -> r <> Rs0 ->
        M !!! Regidx r = mm !!! Regidx r) ->
    sie_cap_gpr kt (CID := CID0) M (K - 2)%nat b p -∗
    kernel_text -∗
    pc_is (CID := CID0) (mword_of_int (KernelSyms.strlen + 0x12) : mword 64) -∗
    ([∗ list] j ∈ seq 0 n, (pa_add s j) ↦ₘ{dq} f j) -∗
    wp_next (CID0 := CIDh) b p (fun (CID : CpuId) =>
      ∀ Mt : regfile,
        ⌜Mt !!! Regidx csp_rs1 = pa_stk sp0 2⌝ -∗
        ⌜Mt !!! Regidx Ra0 = (mword_of_int (Z.of_nat k) : mword 64)⌝ -∗
        ⌜forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 -> r <> Rs0 ->
            Mt !!! Regidx r = mm !!! Regidx r⌝ -∗
        sie_cap_gpr kt Mt (K - 2)%nat b p -∗
        pc_is (mword_of_int (KernelSyms.strlen + 0x20) : mword 64) -∗
        ([∗ list] j ∈ seq 0 n, (pa_add s j) ↦ₘ{dq} f j) -∗
        WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hkn Hcstr Hk31 rem.
    induction rem as [| rem IH]; intros t M CID0 Hchain Hsum Hnn Hsp Ha0 Ha5 Hthr;
      iIntros "Hcg #Htext Hpc Hbuf Hcont".
    - (* ---- rem = 0: [S t = k], so the byte read IS the terminator ---- *)
      assert (Htk : (S t = k)%nat) by lia.
      assert (Hlt : (S t < n)%nat) by lia.
      iDestruct (bb_byte_acc s n (S t) f dq Hlt with "Hbuf") as "[Hbyte Hback]".
      iApply (sl_probe M (K - 2)%nat dq s t (f (S t)) b p Ha5
                with "Hcg Htext Hpc Hbyte").
      iIntros (CIDp Hspp Mp) "%Hpa3 %Hpa5 %Hpa4 %Hpthr Hcg Hpc Hbyte".
      iDestruct ("Hback" $! f with "[%] Hbyte") as "Hbuf"; [done |].
      iPoseProof (sli_1a with "Htext") as "Hi1a".
      iPoseProof (sli_1c with "Htext") as "Hi1c".
      (* the byte is zero, so the [bnez] falls through *)
      assert (Hzero : f (S t) = (mword_of_int 0 : mword 8))
        by (rewrite Htk; exact (proj2 Hcstr)).
      assert (Hpa4' : rget Mp Ra4 = zero_extend' 64 (f (S t) : mword 8)) by (rgne; exact Hpa4).
      assert (Hcmp : neq_vec (rget Mp Ra4) zero_reg = false).
      { unfold neq_vec. rewrite Hpa4' Hzero bc_zext8_iszero. reflexivity. }
      iApply (wp_cbnez_fall_s_sconf (mword_of_int (KernelSyms.strlen + 0x1a))
                (mword_of_int 252 : mword 8) (Cregidx (mword_of_int 6)) Ra4 Mp (K - 2)%nat b
                ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) Hcmp
                with "Hcg Hpc Hi1a").
      iIntros (CID1 Hs1) "Hcg Hpc".
      assert (Hp1c : add_vec_int (mword_of_int (KernelSyms.strlen + 0x1a) : mword 64) 2
                     = mword_of_int (KernelSyms.strlen + 0x1c))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp1c) in "Hpc".
      (* ---- +0x1c: subw a0,a3,a0 ---- *)
      assert (Hpa0 : Mp !!! Regidx Ra0 = s).
      { rewrite (Hpthr Ra0 ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)). exact Ha0. }
      assert (Hpa0' : rget Mp Ra0 = s) by (rgne; exact Hpa0).
      assert (Hpa3' : rget Mp Ra3 = pa_add s (S t)) by (rgne; exact Hpa3).
      iApply (wp_subw_s_sconf (mword_of_int (KernelSyms.strlen + 0x1c)) Ra0 Ra3 Ra0
                Mp (K - 2)%nat b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi1c").
      iIntros (CID2 Hs2) "Hcg Hpc".
      set (Q1 := <[Regidx Ra0 := regval_into_reg
                    (sign_extend' 64
                       (sub_vec (subrange_vec_dec (rget Mp Ra3) 31 0 : mword 32)
                                (subrange_vec_dec (rget Mp Ra0) 31 0 : mword 32)))]> Mp).
      change (<[Regidx Ra0 := regval_into_reg
                 (sign_extend' 64
                    (sub_vec (subrange_vec_dec (rget Mp Ra3) 31 0 : mword 32)
                             (subrange_vec_dec (rget Mp Ra0) 31 0 : mword 32)))]> Mp)
        with Q1.
      assert (HQ1a0 : Q1 !!! Regidx Ra0 = (mword_of_int (Z.of_nat k) : mword 64)).
      { rewrite /Q1 upd_eq Hpa3' Hpa0' Htk.
        exact (bc_subw_diff (pa_add s k) s k Hk31 (pa_add_unsigned s k)). }
      assert (Hp20 : add_vec_int (mword_of_int (KernelSyms.strlen + 0x1c) : mword 64) 4
                     = mword_of_int (KernelSyms.strlen + 0x20))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp20) in "Hpc".
      iSpecialize ("Hcont" $! CID2 with "[%]"); [wp_next_chain|].
      iApply ("Hcont" $! Q1 with "[%] [%] [%] Hcg Hpc Hbuf").
      + rewrite /Q1 upd_ne; [| reg_neq].
        rewrite (Hpthr csp_rs1 ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)). exact Hsp.
      + exact HQ1a0.
      + intros r Hr Ncsp Ns0.
        rewrite /Q1 upd_ne; [| apply cs_ne; [vm_compute; reflexivity | exact Hr]].
        assert (N3 : r <> Ra3) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
        assert (N4 : r <> Ra4) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
        assert (N5 : r <> Ra5) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
        rewrite (Hpthr r N3 N4 N5). apply Hthr; assumption.
    - (* ---- rem = S rem: [S t < k], so the byte is not the terminator ---- *)
      assert (Hlt : (S t < n)%nat) by lia.
      iDestruct (bb_byte_acc s n (S t) f dq Hlt with "Hbuf") as "[Hbyte Hback]".
      iApply (sl_probe M (K - 2)%nat dq s t (f (S t)) b p Ha5
                with "Hcg Htext Hpc Hbyte").
      iIntros (CIDp Hspp Mp) "%Hpa3 %Hpa5 %Hpa4 %Hpthr Hcg Hpc Hbyte".
      iDestruct ("Hback" $! f with "[%] Hbyte") as "Hbuf"; [done |].
      iPoseProof (sli_1a with "Htext") as "Hi1a".
      assert (Hnz : f (S t) <> (mword_of_int 0 : mword 8))
        by (apply (proj1 Hcstr); lia).
      assert (Hpa4' : rget Mp Ra4 = zero_extend' 64 (f (S t) : mword 8)) by (rgne; exact Hpa4).
      assert (Hcmp : neq_vec (rget Mp Ra4) zero_reg = true).
      { unfold neq_vec. rewrite Hpa4' (bc_zext8_nonzero _ Hnz). reflexivity. }
      iApply (wp_cbnez_taken_s_sconf (mword_of_int (KernelSyms.strlen + 0x1a))
                (mword_of_int 252 : mword 8) (Cregidx (mword_of_int 6)) Ra4 Mp (K - 2)%nat b
                ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) Hcmp
                ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi1a").
      iNext. iIntros (CID1 Hs1) "Hcg Hpc".
      assert (Hback12 : add_vec (mword_of_int (KernelSyms.strlen + 0x1a) : mword 64)
                (sign_extend' 64 (sign_extend' 13 (concat_vec (mword_of_int 252 : mword 8) ('b"0"))))
              = mword_of_int (KernelSyms.strlen + 0x12))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hback12) in "Hpc".
      assert (HS1 : (S (S t) + rem = k)%nat) by lia.
      assert (HS2 : bb_nonul f (S (S t))) by (apply bb_nonul_step; [exact Hnn | exact Hnz]).
      assert (HS3 : Mp !!! Regidx csp_rs1 = pa_stk sp0 2).
      { rewrite (Hpthr csp_rs1 ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)). exact Hsp. }
      assert (HS4 : Mp !!! Regidx Ra0 = s).
      { rewrite (Hpthr Ra0 ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)). exact Ha0. }
      assert (HS5 : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 -> r <> Rs0 ->
                      Mp !!! Regidx r = mm !!! Regidx r).
      { intros r Hr Ncsp Ns0.
        assert (N3 : r <> Ra3) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
        assert (N4 : r <> Ra4) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
        assert (N5 : r <> Ra5) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
        rewrite (Hpthr r N3 N4 N5). apply Hthr; assumption. }
      assert (Hchain' : b = false \/ p = zero_reg -> (CID1 : CPU) = (CIDh : CPU)) by wp_next_chain.
      iApply (IH (S t) Mp CID1 Hchain' HS1 HS2 HS3 HS4 Hpa5 HS5 with "Hcg Htext Hpc Hbuf Hcont").
  Qed.

  (* ================================================================== *)
  (*  THE WHOLE FUNCTION.                                                *)
  (* ================================================================== *)
  Lemma wp_strlen_sconf (mm : regfile)
      (n k : nat) (f : nat -> bv 8) (K : nat) (dq : dfrac) (b : bool) (p : mword 64)
    : wp_strlen_sconf_body kt mm n k f K dq b p.
  Proof.
    cbv beta delta [wp_strlen_sconf_body].
    intros pcE s ret_tgt HK Hkn Hcstr Hk31.
    change (2 ^ 31)%Z with 2147483648%Z in Hk31.
    pose (sp0 := (mm !!! Regidx csp_rs1 : mword 64)).
    iIntros "Hcg #Htext Hpc Hbuf Hcont".
    iPoseProof (sli_00 with "Htext") as "Hi00".
    iPoseProof (sli_02 with "Htext") as "Hi02".
    iPoseProof (sli_04 with "Htext") as "Hi04".
    iPoseProof (sli_06 with "Htext") as "Hi06".
    iPoseProof (sli_08 with "Htext") as "Hi08".
    iPoseProof (sli_0c with "Htext") as "Hi0c".
    (* ---- +0x00: c.addi sp,-16 (frame push) ---- *)
    iApply (wp_caddi_sp_push_s_sconf pcE (mword_of_int 48 : mword 6) mm K 2 b
              ltac:(lia) (sl_push (mm !!! Regidx csp_rs1))
              with "Hcg Hpc Hi00").
    iIntros (CID1 Hs1) "Hcg Hframe Hpc".
    set (R1 := <[Regidx csp_rs1 := regval_into_reg
                  (add_vec (mm !!! Regidx csp_rs1)
                     (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6))))]> mm).
    change (<[Regidx csp_rs1 := regval_into_reg
               (add_vec (mm !!! Regidx csp_rs1)
                  (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6))))]> mm) with R1.
    assert (HR1sp : R1 !!! Regidx csp_rs1 = pa_stk sp0 2)
      by (rewrite /R1 upd_eq; apply sl_push).
    assert (Hp02 : add_vec_int (pcE : mword 64) 2 = mword_of_int (KernelSyms.strlen + 0x02))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp02) in "Hpc".
    iDestruct (stack_own_2_elim with "Hframe") as (u1 u2) "[Hb1 Hb2]".
    (* the two slot addresses in the [c.sdsp] / [c.ldsp] displacement spelling *)
    assert (Hpa1 : add_vec (R1 !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000")))
                   = pa_stk sp0 1).
    { rewrite HR1sp. unfold pa_stk, add_vec_int. rewrite !pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hpa2 : add_vec (R1 !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000")))
                   = pa_stk sp0 2).
    { rewrite HR1sp. unfold pa_stk, add_vec_int. rewrite !pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    (* ---- +0x02: c.sdsp ra,8(sp) ---- *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.strlen + 0x02))
              (mword_of_int 1 : mword 6) Rra R1 (K - 2)%nat u1 b
              with "Hcg Hpc Hi02 [Hb1]").
    { iEval (rewrite Hpa1). iExact "Hb1". }
    iIntros (CID2 Hs2) "Hcg Hpc Hb1". iEval (rewrite Hpa1) in "Hb1".
    assert (HR1ra : R1 !!! Regidx Rra = mm !!! Regidx Rra)
      by (rewrite /R1 upd_ne; [reflexivity | reg_neq]).
    assert (HR1ra' : forall CID' : CpuId, rget (CID := CID') R1 Rra = mm !!! Regidx Rra)
      by (intros CID'; rgne; exact HR1ra).
    iEval (rewrite HR1ra') in "Hb1".
    assert (Hp04 : add_vec_int (mword_of_int (KernelSyms.strlen + 0x02) : mword 64) 2
                   = mword_of_int (KernelSyms.strlen + 0x04))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp04) in "Hpc".
    (* ---- +0x04: c.sdsp s0,0(sp) ---- *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.strlen + 0x04))
              (mword_of_int 0 : mword 6) Rs0 R1 (K - 2)%nat u2 b
              with "Hcg Hpc Hi04 [Hb2]").
    { iEval (rewrite Hpa2). iExact "Hb2". }
    iIntros (CID3 Hs3) "Hcg Hpc Hb2". iEval (rewrite Hpa2) in "Hb2".
    assert (HR1s0 : R1 !!! Regidx Rs0 = mm !!! Regidx Rs0)
      by (rewrite /R1 upd_ne; [reflexivity | reg_neq]).
    assert (HR1s0' : forall CID' : CpuId, rget (CID := CID') R1 Rs0 = mm !!! Regidx Rs0)
      by (intros CID'; rgne; exact HR1s0).
    iEval (rewrite HR1s0') in "Hb2".
    assert (Hp06 : add_vec_int (mword_of_int (KernelSyms.strlen + 0x04) : mword 64) 2
                   = mword_of_int (KernelSyms.strlen + 0x06))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp06) in "Hpc".
    (* ---- +0x06: c.addi4spn s0,sp,16 ---- *)
    iApply (wp_caddi4spn_s_sconf (mword_of_int (KernelSyms.strlen + 0x06))
              (Cregidx (mword_of_int 0)) (mword_of_int 4 : mword 8) Rs0 R1 (K - 2)%nat b
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
              ltac:(rdok)
              with "Hcg Hpc Hi06").
    iIntros (CID4 Hs4) "Hcg Hpc".
    set (R2 := <[Regidx Rs0 := regval_into_reg
                  (add_vec (R1 !!! Regidx csp_rs1)
                     (sign_extend' 64 (caddi4spn_imm (mword_of_int 4 : mword 8))))]> R1).
    change (<[Regidx Rs0 := regval_into_reg
               (add_vec (R1 !!! Regidx csp_rs1)
                  (sign_extend' 64 (caddi4spn_imm (mword_of_int 4 : mword 8))))]> R1) with R2.
    assert (Hp08 : add_vec_int (mword_of_int (KernelSyms.strlen + 0x06) : mword 64) 2
                   = mword_of_int (KernelSyms.strlen + 0x08))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp08) in "Hpc".
    (* ---- +0x08: lbu a5,0(a0) ---- *)
    assert (HR2a0 : R2 !!! Regidx Ra0 = s).
    { rewrite /R2 upd_ne; [| reg_neq]. rewrite /R1 upd_ne; [reflexivity | reg_neq]. }
    assert (HR2a0' : rget R2 Ra0 = s) by (rgne; exact HR2a0).
    assert (H0n : (0 < n)%nat) by lia.
    iDestruct (bb_byte_acc s n 0%nat f dq H0n with "Hbuf") as "[Hbyte Hback]".
    iApply (wp_lbu_s_sconf (mword_of_int (KernelSyms.strlen + 0x08)) Ra5 Ra0
              (mword_of_int 0 : mword 12) R2 (K - 2)%nat (f 0%nat : mword 8) b (dqm:=dq)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi08 [Hbyte]").
    { iEval (rewrite HR2a0' addv_sext0 -(pa_add_0 s)). iExact "Hbyte". }
    iIntros (CID5 Hs5) "Hcg Hpc Hbyte".
    iEval (rewrite HR2a0' addv_sext0 -(pa_add_0 s)) in "Hbyte".
    iDestruct ("Hback" $! f with "[%] Hbyte") as "Hbuf"; [done |].
    set (R3 := <[Regidx Ra5 := regval_into_reg (zero_extend' 64 (f 0%nat : mword 8))]> R2).
    change (<[Regidx Ra5 := regval_into_reg (zero_extend' 64 (f 0%nat : mword 8))]> R2) with R3.
    assert (Hp0c : add_vec_int (mword_of_int (KernelSyms.strlen + 0x08) : mword 64) 4
                   = mword_of_int (KernelSyms.strlen + 0x0c))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp0c) in "Hpc".
    (* the register facts the two arms below share *)
    assert (HR3sp : R3 !!! Regidx csp_rs1 = pa_stk sp0 2).
    { rewrite /R3 upd_ne; [| reg_neq]. rewrite /R2 upd_ne; [| reg_neq]. exact HR1sp. }
    assert (HR3a0 : R3 !!! Regidx Ra0 = s)
      by (rewrite /R3 upd_ne; [exact HR2a0 | reg_neq]).
    assert (HR3a5 : R3 !!! Regidx Ra5 = zero_extend' 64 (f 0%nat : mword 8))
      by (rewrite /R3 upd_eq; reflexivity).
    assert (HR3a5' : rget R3 Ra5 = zero_extend' 64 (f 0%nat : mword 8)) by (rgne; exact HR3a5).
    assert (HR3thr : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 -> r <> Rs0 ->
                       R3 !!! Regidx r = mm !!! Regidx r).
    { intros r Hr Ncsp Ns0.
      rewrite /R3 upd_ne; [| apply cs_ne; [vm_compute; reflexivity | exact Hr]].
      rewrite /R2 upd_ne; [| intro He; injection He as He'; congruence].
      rewrite /R1 upd_ne; [reflexivity | intro He; injection He as He'; congruence]. }
    (* ---- +0x0c: beqz a5 -- is the string empty? ---- *)
    destruct (eq_vec (zero_extend' 64 (f 0%nat : mword 8) : mword 64) (zero_reg : mword 64)) eqn:Ez.
    { (* --- s[0] is the NUL: k = 0, take the branch to +0x28 --- *)
      assert (Hz0 : f 0%nat = (mword_of_int 0 : mword 8)) by (apply bc_zext8_zero; exact Ez).
      assert (Hk0 : (0 = k)%nat) by (apply (bb_cstr_uniq f k 0%nat Hcstr (bb_nonul_0 f) Hz0)).
      iPoseProof (sli_28 with "Htext") as "Hi28".
      iPoseProof (sli_2a with "Htext") as "Hi2a".
      iApply (wp_cbeqz_taken_s_sconf (mword_of_int (KernelSyms.strlen + 0x0c))
                (mword_of_int 14 : mword 8) (Cregidx (mword_of_int 7)) Ra5 R3 (K - 2)%nat b
                ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                ltac:(rewrite HR3a5'; exact Ez) ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi0c").
      iNext. iIntros (CID6 Hs6) "Hcg Hpc".
      assert (Ht28 : add_vec (mword_of_int (KernelSyms.strlen + 0x0c) : mword 64)
                (sign_extend' 64 (sign_extend' 13 (concat_vec (mword_of_int 14 : mword 8) ('b"0"))))
              = mword_of_int (KernelSyms.strlen + 0x28))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Ht28) in "Hpc".
      (* ---- +0x28: c.li a0,0 ---- *)
      iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.strlen + 0x28)) Ra0
                (mword_of_int 0 : mword 6) (mword_of_int (Z.of_nat k) : mword 64)
                R3 (K - 2)%nat b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                ltac:(rewrite -Hk0; apply bv_eq; vm_compute; reflexivity)
                with "Hcg Hpc Hi28").
      iIntros (CID7 Hs7) "Hcg Hpc".
      set (Z1 := <[Regidx Ra0 := regval_into_reg
                    (mword_of_int (Z.of_nat k) : mword 64)]> R3).
      change (<[Regidx Ra0 := regval_into_reg (mword_of_int (Z.of_nat k) : mword 64)]> R3)
        with Z1.
      assert (Hp2a : add_vec_int (mword_of_int (KernelSyms.strlen + 0x28) : mword 64) 2
                     = mword_of_int (KernelSyms.strlen + 0x2a))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp2a) in "Hpc".
      (* ---- +0x2a: c.j -0x0a -> +0x20 ---- *)
      iApply (wp_cj_s_sconf (mword_of_int (KernelSyms.strlen + 0x2a))
                (sign_extend' 21 (concat_vec (mword_of_int 2043 : mword 11) ('b"0")))
                Z1 (K - 2)%nat b ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi2a").
      iIntros (CID8 Hs8). iNext. iIntros "Hcg Hpc".
      assert (Ht20 : add_vec (mword_of_int (KernelSyms.strlen + 0x2a) : mword 64)
                (sign_extend' 64 (sign_extend' 21 (concat_vec (mword_of_int 2043 : mword 11) ('b"0"))))
              = mword_of_int (KernelSyms.strlen + 0x20))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Ht20) in "Hpc".
      iApply (sl_tail mm Z1 K (mword_of_int (Z.of_nat k)) sp0
                (mm !!! Regidx Rra) (mm !!! Regidx Rs0) b p
                HK ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity)
                ltac:(rewrite /Z1 upd_ne; [exact HR3sp | reg_neq])
                ltac:(rewrite /Z1 upd_eq; reflexivity)
                ltac:(intros r Hr Ncsp Ns0;
                      rewrite /Z1 upd_ne;
                      [ apply HR3thr; assumption
                      | apply cs_ne; [vm_compute; reflexivity | exact Hr] ])
                with "Hcg Htext Hpc Hb1 Hb2").
      iIntros (CID9 Hs9 mf) "[%Hcs %Hfa0] Hcg Hpc".
      iSpecialize ("Hcont" $! CID9 with "[%]"); [wp_next_chain|].
      iApply ("Hcont" $! mf with "Hcg Hpc Hbuf [%] [%]").
      - exact Hcs.
      - exact Hfa0. }
    (* --- s[0] is not the NUL: fall through into the loop --- *)
    assert (Hnz0 : f 0%nat <> (mword_of_int 0 : mword 8)).
    { intro He. rewrite He bc_zext8_iszero in Ez. discriminate. }
    assert (Hk1 : (1 <= k)%nat).
    { destruct (Nat.eq_dec k 0) as [Hk0 | Hkne]; [| lia].
      exfalso. apply Hnz0. rewrite -Hk0. exact (proj2 Hcstr). }
    iPoseProof (sli_0e with "Htext") as "Hi0e".
    iApply (wp_cbeqz_fall_s_sconf (mword_of_int (KernelSyms.strlen + 0x0c))
              (mword_of_int 14 : mword 8) (Cregidx (mword_of_int 7)) Ra5 R3 (K - 2)%nat b
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
              ltac:(rewrite HR3a5'; exact Ez)
              with "Hcg Hpc Hi0c").
    iIntros (CID6 Hs6) "Hcg Hpc".
    assert (Hp0e : add_vec_int (mword_of_int (KernelSyms.strlen + 0x0c) : mword 64) 2
                   = mword_of_int (KernelSyms.strlen + 0x0e))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp0e) in "Hpc".
    (* ---- +0x0e: addi a5,a0,1 ---- *)
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.strlen + 0x0e)) Ra5 Ra0
              (mword_of_int 1 : mword 12) R3 (K - 2)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi0e").
    iIntros (CID7 Hs7) "Hcg Hpc".
    set (R4 := <[Regidx Ra5 := regval_into_reg
                  (add_vec (rget (CID := CID7) R3 Ra0)
                     (sign_extend' 64 (mword_of_int 1 : mword 12)))]> R3).
    change (<[Regidx Ra5 := regval_into_reg
               (add_vec (rget (CID := CID7) R3 Ra0)
                  (sign_extend' 64 (mword_of_int 1 : mword 12)))]> R3) with R4.
    assert (HR3a0' : rget (CID := CID7) R3 Ra0 = s) by (rgne; exact HR3a0).
    assert (HR4a5 : R4 !!! Regidx Ra5 = pa_add s 1%nat).
    { rewrite /R4 upd_eq HR3a0'. apply sl_bump1. }
    assert (Hp12 : add_vec_int (mword_of_int (KernelSyms.strlen + 0x0e) : mword 64) 4
                   = mword_of_int (KernelSyms.strlen + 0x12))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp12) in "Hpc".
    (* ---- the loop, entered with t = 0 ---- *)
    iApply (sl_loop mm n k f K dq s sp0 b p CID7 Hkn Hcstr Hk31
              (k - 1)%nat 0%nat R4 CID7 ltac:(intros _; reflexivity) ltac:(lia)
              ltac:(apply bb_nonul_step; [apply bb_nonul_0 | exact Hnz0])
              ltac:(rewrite /R4 upd_ne; [exact HR3sp | reg_neq])
              ltac:(rewrite /R4 upd_ne; [exact HR3a0 | reg_neq])
              HR4a5
              ltac:(intros r Hr Ncsp Ns0;
                    rewrite /R4 upd_ne;
                    [ apply HR3thr; assumption
                    | apply cs_ne; [vm_compute; reflexivity | exact Hr] ])
              with "Hcg Htext Hpc Hbuf").
    iIntros (CID8 Hs8 Mt) "%Htsp %Hta0 %Htthr Hcg Hpc Hbuf".
    iApply (sl_tail mm Mt K (mword_of_int (Z.of_nat k)) sp0
              (mm !!! Regidx Rra) (mm !!! Regidx Rs0) b p
              HK ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity)
              Htsp Hta0 Htthr
              with "Hcg Htext Hpc Hb1 Hb2").
    iIntros (CID9 Hs9 mf) "[%Hcs %Hfa0] Hcg Hpc".
    iSpecialize ("Hcont" $! CID9 with "[%]"); [wp_next_chain|].
    iApply ("Hcont" $! mf with "Hcg Hpc Hbuf [%] [%]").
    - exact Hcs.
    - exact Hfa0.
  Qed.

End ProofStrlen.

End StrlenProof.
