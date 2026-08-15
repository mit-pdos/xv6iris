(* ProofKforkB1.v -- kfork's uvmcopy-FAILURE TAIL, +0x7c .. +0x8c, which
   reaches the shared epilogue at +0xfc.

     +0x07c  c.mv a0,s4
     +0x07e  jal ra,freeproc
     +0x082  c.mv a0,s4
     +0x084  jal ra,release           (release &np->lock)
     +0x088  c.li s1,-1
     +0x08a  c.ldsp s4,16(sp)
     +0x08c  c.j +0xfc

   Entry: uvmcopy has just returned -1 with the child's (np's) lock still
   HELD, so the SIE index is [false] until the release completes.  The
   thread holds exactly freeproc's precondition ([fp_rest] /
   [fp_pt _ _ (Some P)] / [fp_tf _ (Some (ud_tfp P, ws))]), plus
   [proc_held cpu_id j γl USED ch], [hart_at_any (proc_addr
   j)], [kalloc_env γa None], the interrupt/lock-nesting bundle
   ([cpu_own (S lvl) eb pme C false], [sie_cap_gpr Mt (K-8) false
   pme], [arm_pay lvl eb pme]), and the 8 frame slots -- slot 6
   (16(sp)) holds the CALLER's saved s4 ([m !!! Regidx Rs4]: nothing between
   kfork's entry and +0x01a touches s4), slots 4/5 are never spilled on this
   path and so are taken existentially.

   freeproc's own contract is PINNED at [b = false] (SpecFreeproc.v), so the
   two calls before the release ([c.mv a0,s4], [jal ra,freeproc], the second
   [c.mv a0,s4]) all stay at the literal index [false] and their [wp_next]s
   collapse with [wp_next_off_intro] -- no fresh CID, no cpu_own transport.
   The [release] itself is where the index actually may change: its exit
   index is [match lvl with O => eb | S _ => false end], a SYMBOLIC value
   when [lvl] is a free variable, so it is closed with ordinary [iIntros],
   exactly as the established releases of a "proc" lock at generic nesting
   do ([ProofKkill.v], [ProofWakeup.v], [ProofAllocproc.v]) -- see the
   report for why this deviates from a naive "always use wp_next_off_intro"
   reading of a release. *)
From Stdlib Require Import Eqdep_dec ZArith Lia List.
From stdpp Require Import gmap list list_monad bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_var gen_heap invariants.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import RiscvExtras.
Require Import RegFile.
Require Import WpNext.
Require Import WpMmodeLeafBase.
Require Import SmodeCore.
Require Import StackOwn.
Require Import CalleeSaved.
Require Import InstrBytes.
Require Import KernelText.
Require Import WpSconfAlu WpSconfMem WpSconfCtl.
Require Import WpSmodeIntr.
Require Import IntrDefs.
Require Import CpuOwn.
Require Import ProcGeom.
Require Import UserPtTree.
Require Import FdSlots.
Require Import FdSlots.
Require Import WpLock.
Require Import ProcInv.
Require Import KallocInv.
Require Import KvmSpec.
Require Import SchedCtx.
Require Import SpecFreeproc.
Require Import SpecRelease.
Require Import CodeKfork.
Require Import ProofKforkParts.
Require Import ProofKfork.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.

(* A syscall-altitude goal carries [ProcInv.tf_page]'s 4096-conjunct big-op;
   printing one takes tens of minutes, so a one-line mistake reads as a hang.
   durable-notes.md's rule. *)
Set Printing Depth 40.

Notation KF := KernelSyms.kfork (only parsing).

(* ------------------------------------------------------------------ *)
(*  Numeric side conditions, by name, over plain nat/Z -- never inline. *)
(* ------------------------------------------------------------------ *)
Lemma kfkb1_K8 (K : nat) : (52 <= K)%nat -> (8 <= K)%nat.
Proof. lia. Qed.
Lemma kfkb1_K44 (K : nat) : (52 <= K)%nat -> (44 <= K - 8)%nat.
Proof. lia. Qed.
Lemma kfkb1_K10 (K : nat) : (52 <= K)%nat -> (10 <= K - 8)%nat.
Proof. lia. Qed.
Lemma kfkb1_lvlS (lvl : nat) :
  (Z.of_nat lvl + 2 < 2 ^ 31)%Z -> (Z.of_nat (S lvl) + 1 < 2 ^ 31)%Z.
Proof. lia. Qed.

Module KforkB1 (FP : FREEPROC) (RL : RELEASE).
Section KforkB1Proof.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !kallocG Σ, !fdslotG Σ, !irefslotG Σ}.
  Context `{GEN : GenId} `{CID0 : CpuId}.

  Notation Rra := (mword_of_int 1 : mword 5).
  Notation Rs0 := (mword_of_int 8 : mword 5).
  Notation Rs1 := (mword_of_int 9 : mword 5).
  Notation Ra0 := (mword_of_int 10 : mword 5).
  Notation Rs4 := (mword_of_int 20 : mword 5).
  Notation Rs5 := (mword_of_int 21 : mword 5).

  Local Ltac regne := reg_ne_side.

  (* =================================================================== *)
  (*  +0x7c .. +0x8c: freeproc, release, -1, reaching the epilogue.       *)
  (* =================================================================== *)
  Lemma kfk_exit_uvmcopy
      (γs : list gname) (γa γl : gname) (j : nat) (ch : mword 64)
      (V : pprivate) (pid : mword 32) (P : uptd) (ws : list (mword 64))
      (m Mt : regfile) (K : nat)
      (sp0 ra0 s00 s10 s50 : mword 64)
      (pme : mword 64) (eb b : bool) (lvl : nat) (lks : gset string) :
    (52 <= K)%nat ->
    (Z.of_nat lvl + 2 < 2 ^ 31)%Z ->
    (* The EXIT arm, named.  This block is entered with np->lock HELD, so its
       entry index has to carry the trap reserve OF THE ARM IT WILL RETURN AT
       -- and that arm is the release's [match lvl with O => eb | S _ => false
       end].  Naming it [b] keeps the ~5 in-lock indices below readable; the
       one place the spec's own spelling is needed is the [release] call, where
       [rewrite -Hb] restores it.  ([kfk_b5] carries the same parameter for the
       same reason.) *)
    match lvl with O => eb | S _ => false end = b ->
    m !!! Regidx csp_rs1 = sp0 ->
    m !!! Regidx Rra = ra0 ->
    m !!! Regidx Rs0 = s00 ->
    m !!! Regidx Rs1 = s10 ->
    m !!! Regidx Rs5 = s50 ->
    Mt !!! Regidx csp_rs1 = pa_stk sp0 8 ->
    Mt !!! Regidx Rs4 = proc_addr j ->
    (* [Rs4] MUST be excluded here.  On this path s4 holds [proc_addr j] (the
       child), not the caller's value -- the prologue spilled the caller's s4
       to slot 6 at +0x1a and +0x1c overwrote it -- so a premise that covered
       [Rs4] would force [proc_addr j = m !!! Regidx Rs4] and no call site
       could discharge it.  The proof never uses [Hthr] at [Rs4]: every
       derived predicate below carries its own [r <> Rs4] guard, and s4's
       value comes back off the frame at +0x8a. *)
    (forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
        r <> Rs0 -> r <> Rs1 -> r <> Rs4 -> r <> Rs5 ->
        Mt !!! Regidx r = m !!! Regidx r) ->
    (* THE FRESHNESS PREMISE: this block RELEASES [p->lock] (rank "proc")
       before returning, so [lks] is the OUTER set -- below "proc"'s rank --
       and the entry resource carries "proc" ∪ [lks] explicitly. *)
    locks_below lks "proc" ->
    (* ENTRY: in-lock (level [S lvl], arm [false]), so the index carries the
       reserve of the exit arm [b].  EXIT below is at [K] and arm [b]: the
       physical carve [trap_res b + (K - 8)] -> [trap_res b + K] is exactly the
       8-slot epilogue pop, i.e. the reserve is CONSERVED across this block. *)
    sie_cap_gpr Mt (trap_res b + (K - 8))%nat false pme -∗
    cpu_own (S lvl) eb pme false ({["proc"]} ∪ lks) -∗
    arm_pay lvl eb pme -∗
    kernel_text -∗
    pc_is (mword_of_int (KF + 0x7c) : mword 64) -∗
    word_pointsto (pa_stk sp0 1) (DfracOwn 1) ra0 -∗
    word_pointsto (pa_stk sp0 2) (DfracOwn 1) s00 -∗
    word_pointsto (pa_stk sp0 3) (DfracOwn 1) s10 -∗
    (∃ w4, word_pointsto (pa_stk sp0 4) (DfracOwn 1) w4) -∗
    (∃ w5, word_pointsto (pa_stk sp0 5) (DfracOwn 1) w5) -∗
    word_pointsto (pa_stk sp0 6) (DfracOwn 1) (m !!! Regidx Rs4) -∗
    word_pointsto (pa_stk sp0 7) (DfracOwn 1) s50 -∗
    (∃ w8, word_pointsto (pa_stk sp0 8) (DfracOwn 1) w8) -∗
    proc_held cpu_id j γl USED ch -∗
    hart_at_any (proc_addr j) -∗
    is_lock γl (proc_addr j) "proc"%string (proc_lock_res γs γl (proc_addr j)) -∗
    kalloc_env γa None -∗
    fp_rest (proc_addr j) V pid -∗
    fp_pt (proc_addr j) (pv_sz V) (Some P) -∗
    fp_tf (proc_addr j) (Some (ud_tfp P, ws)) -∗
    wp_next (match lvl with O => eb | S _ => false end) pme (fun (CID : CpuId) =>
      ∀ mf : regfile,
        ⌜callee_saved m mf /\ mf !!! Regidx Ra0 = (mword_of_int (-1) : mword 64)⌝ -∗
        sie_cap_gpr mf K (match lvl with O => eb | S _ => false end) pme -∗
        pc_is (ret_pc ra0) -∗
        cpu_own lvl eb pme (match lvl with O => eb | S _ => false end) lks -∗
        kalloc_env γa None -∗
        WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HK Hlvl Hb Hsp0 Hra0 Hs00 Hs10 Hs50 Hmtsp Hmts4 Hthr Hfresh.
    iIntros "Hcg Hcpu Hpay #Htext Hpc Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hb7 Hb8
              Hheld Hhaa #Hislock #Henv Hfprest Hfppt Hfptf Hcont".
    iPoseProof (kfk_07c with "Htext") as "Hi7c".
    iPoseProof (kfk_07e with "Htext") as "Hi7e".
    iPoseProof (kfk_082 with "Htext") as "Hi82".
    iPoseProof (kfk_084 with "Htext") as "Hi84".
    iPoseProof (kfk_088 with "Htext") as "Hi88".
    iPoseProof (kfk_08a with "Htext") as "Hi8a".
    iPoseProof (kfk_08c with "Htext") as "Hi8c".
    (* ---- +0x7c: c.mv a0,s4 ---- *)
    iApply (wp_cmv_s_sconf (mword_of_int (KF + 0x7c)) Ra0 Rs4 Mt (trap_res b + (K - 8))%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi7c").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    set (T0 := <[Regidx Ra0 := regval_into_reg (add_vec zero_reg (rget Mt Rs4))]> Mt).
    change (<[Regidx Ra0 := regval_into_reg (add_vec zero_reg (rget Mt Rs4))]> Mt) with T0.
    assert (HT0a0 : T0 !!! Regidx Ra0 = proc_addr j).
    { rewrite /T0 upd_eq. rewrite add_vec_zero_l. exact Hmts4. }
    assert (Hpp7e : add_vec_int (mword_of_int (KF + 0x7c) : mword 64) 2
                   = mword_of_int (KF + 0x7e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp7e) in "Hpc".
    (* ---- +0x7e: jal ra,freeproc ---- *)
    assert (Htgt7e : add_vec (mword_of_int (KF + 0x7e) : mword 64)
                       (sign_extend' 64 (mword_of_int 2096626 : mword 21))
                     = mword_of_int KernelSyms.freeproc)
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_jal_s_sconf (mword_of_int (KF + 0x7e)) Rra (mword_of_int 2096626 : mword 21)
              T0 (trap_res b + (K - 8))%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(rewrite Htgt7e; vm_compute; reflexivity)
              with "Hcg Hpc Hi7e").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    iEval (rewrite Htgt7e) in "Hpc".
    set (T1 := <[Regidx Rra := regval_into_reg (add_vec_int (mword_of_int (KF + 0x7e) : mword 64) 4)]> T0).
    change (<[Regidx Rra := regval_into_reg (add_vec_int (mword_of_int (KF + 0x7e) : mword 64) 4)]> T0) with T1.
    assert (HT1ra : T1 !!! Regidx Rra = add_vec_int (mword_of_int (KF + 0x7e) : mword 64) 4)
      by (rewrite /T1 upd_eq; reflexivity).
    assert (HT1a0 : T1 !!! Regidx Ra0 = proc_addr j)
      by (rewrite /T1 upd_ne; [exact HT0a0 | vm_compute; discriminate]).
    (* ---- freeproc ---- *)
    iApply (FP.wp_freeproc_sconf γa T1 j γl V pid USED ch (Some P) (Some (ud_tfp P, ws))
              (trap_res b + (K - 8))%nat eb pme (S lvl) ({["proc"]} ∪ lks)
              ltac:(pose proof (kfkb1_K44 K HK); lia) (kfkb1_lvlS lvl Hlvl) HT1a0
              with "Hcg Hcpu Htext Hpc Hheld Hfprest Hfppt Hfptf Henv").
    all: try lkbelow.
    iApply wp_next_off_intro.
    iIntros (mfp) "Hcg Hcpu Hpc %Hcsfp Hheld Hdorm".
    assert (Hp82 : ret_pc (T1 !!! Regidx Rra) = mword_of_int (KF + 0x82))
      by (rewrite HT1ra; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp82) in "Hpc".
    assert (Hmfp_csp : mfp !!! Regidx csp_rs1 = pa_stk sp0 8).
    { rewrite (callee_saved_lookup Hcsfp csp_rs1 ltac:(vm_compute; reflexivity)).
      rewrite /T1 upd_ne; [| vm_compute; discriminate].
      rewrite /T0 upd_ne; [| vm_compute; discriminate]. exact Hmtsp. }
    assert (Hmfp_s4 : mfp !!! Regidx Rs4 = proc_addr j).
    { rewrite (callee_saved_lookup Hcsfp Rs4 ltac:(vm_compute; reflexivity)).
      rewrite /T1 upd_ne; [| vm_compute; discriminate].
      rewrite /T0 upd_ne; [| vm_compute; discriminate]. exact Hmts4. }
    assert (Hmfp_rest : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
                r <> Rs0 -> r <> Rs1 -> r <> Rs4 -> r <> Rs5 -> mfp !!! Regidx r = m !!! Regidx r).
    { intros r Hr Nsp Ns0 Ns1 Ns4 Ns5.
      rewrite (callee_saved_lookup Hcsfp r Hr).
      rewrite /T1 upd_ne; [| regne].
      rewrite /T0 upd_ne; [| regne].
      exact (Hthr r Hr Nsp Ns0 Ns1 Ns4 Ns5). }
    (* ---- +0x82: c.mv a0,s4 (prepare release's argument) ---- *)
    iApply (wp_cmv_s_sconf (mword_of_int (KF + 0x82)) Ra0 Rs4 mfp (trap_res b + (K - 8))%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi82").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    set (T2 := <[Regidx Ra0 := regval_into_reg (add_vec zero_reg (rget mfp Rs4))]> mfp).
    change (<[Regidx Ra0 := regval_into_reg (add_vec zero_reg (rget mfp Rs4))]> mfp) with T2.
    assert (HT2a0 : T2 !!! Regidx Ra0 = proc_addr j).
    { rewrite /T2 upd_eq. rewrite add_vec_zero_l. exact Hmfp_s4. }
    assert (HT2sp : T2 !!! Regidx csp_rs1 = pa_stk sp0 8)
      by (rewrite /T2 upd_ne; [exact Hmfp_csp | vm_compute; discriminate]).
    assert (Hpp84 : add_vec_int (mword_of_int (KF + 0x82) : mword 64) 2
                   = mword_of_int (KF + 0x84)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp84) in "Hpc".
    (* ---- +0x84: jal ra,release ---- *)
    assert (Htgt84 : add_vec (mword_of_int (KF + 0x84) : mword 64)
                       (sign_extend' 64 (mword_of_int 2092916 : mword 21))
                     = mword_of_int KernelSyms.release)
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_jal_s_sconf (mword_of_int (KF + 0x84)) Rra (mword_of_int 2092916 : mword 21)
              T2 (trap_res b + (K - 8))%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(rewrite Htgt84; vm_compute; reflexivity)
              with "Hcg Hpc Hi84").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    iEval (rewrite Htgt84) in "Hpc".
    set (T3 := <[Regidx Rra := regval_into_reg (add_vec_int (mword_of_int (KF + 0x84) : mword 64) 4)]> T2).
    change (<[Regidx Rra := regval_into_reg (add_vec_int (mword_of_int (KF + 0x84) : mword 64) 4)]> T2) with T3.
    assert (HT3ra : T3 !!! Regidx Rra = add_vec_int (mword_of_int (KF + 0x84) : mword 64) 4)
      by (rewrite /T3 upd_eq; reflexivity).
    assert (HT3a0 : T3 !!! Regidx Ra0 = proc_addr j)
      by (rewrite /T3 upd_ne; [exact HT2a0 | vm_compute; discriminate]).
    assert (HT3sp : T3 !!! Regidx csp_rs1 = pa_stk sp0 8)
      by (rewrite /T3 upd_ne; [exact HT2sp | vm_compute; discriminate]).
    (* ---- build proc_lock_res from freeproc's returned proc_held + proc_dormant ---- *)
    iDestruct "Hheld" as "(Hlocked & Hstate & Hpst & Hchan & Hpub)".
    iDestruct (pstate_whole_split (proc_addr j) UNUSED) as "[Hwb _]".
    iDestruct ("Hwb" with "Hpst") as "[Hpst _]".
    iAssert (proc_lock_res γs γl (proc_addr j))
      with "[Hstate Hpst Hchan Hpub Hdorm Hhaa]" as "HR".
    { iApply (proc_lock_res_intro γs γl (proc_addr j) UNUSED (zero_reg : mword 64)
                with "Hstate Hpst Hchan Hpub [Hdorm Hhaa]").
      iApply (proc_slots_unused_intro γs (proc_addr j) with "Hdorm Hhaa"). }
    assert (Hlka : add_vec (T3 !!! Regidx Ra0) (sign_extend' 64 (mword_of_int 0 : mword 12))
                   = proc_addr j).
    { rewrite HT3a0. apply addv_sext0. }
    (* ---- release &np->lock ---- *)
    (* release wants the reserve spelled AT ITS OWN EXIT ARM, which is the
       [match lvl ...] that [Hb] names [b]; put [Hcg]'s index back into that
       form for the call.  Everything after the release is at index [K - 8]
       with no reserve summand at all (the arm is [b] there), so nothing needs
       undoing afterwards. *)
    iEval (rewrite -Hb) in "Hcg".
    iApply (RL.wp_release_sconf γl (proc_addr j) "proc"%string
              (proc_lock_res γs γl (proc_addr j)) T3 lvl eb pme (K - 8)%nat
              ({["proc"]} ∪ lks)
              Hlka (kfkb1_K10 K HK)
              with "Hcg Htext Hpc Hislock Hlocked HR Hcpu Hpay").
    iIntros (CIDr Hsr mr) "Hcg Hpc %Hcsr Hcpu".
    pose proof (locks_below_not_elem _ _ Hfresh) as Hfresh_ne.
    iEval (rewrite (_ : ({["proc"]} ∪ lks) ∖ {["proc"]} = lks);
           [| apply locks_add_del_below; lkbelow]) in "Hcpu".
    assert (Hp88 : ret_pc (T3 !!! Regidx Rra) = mword_of_int (KF + 0x88))
      by (rewrite HT3ra; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp88) in "Hpc".
    assert (Hmrsp : mr !!! Regidx csp_rs1 = pa_stk sp0 8).
    { rewrite (callee_saved_lookup Hcsr csp_rs1 ltac:(vm_compute; reflexivity)). exact HT3sp. }
    assert (Hmr_rest : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
                r <> Rs0 -> r <> Rs1 -> r <> Rs4 -> r <> Rs5 -> mr !!! Regidx r = m !!! Regidx r).
    { intros r Hr Nsp Ns0 Ns1 Ns4 Ns5.
      rewrite (callee_saved_lookup Hcsr r Hr).
      rewrite /T3 upd_ne; [| regne].
      rewrite /T2 upd_ne; [| regne].
      exact (Hmfp_rest r Hr Nsp Ns0 Ns1 Ns4 Ns5). }
    (* ---- +0x88: c.li s1,-1 ---- *)
    iApply (wp_cli_s_sconf (mword_of_int (KF + 0x88)) Rs1
              (mword_of_int 63 : mword 6) (mword_of_int (-1) : mword 64)
              mr (K - 8)%nat (match lvl with O => eb | S _ => false end)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc Hi88").
    iIntros (CIDs1 Hss1) "Hcg Hpc".
    set (T4 := <[Regidx Rs1 := regval_into_reg (mword_of_int (-1) : mword 64)]> mr).
    change (<[Regidx Rs1 := regval_into_reg (mword_of_int (-1) : mword 64)]> mr) with T4.
    assert (HT4s1 : T4 !!! Regidx Rs1 = (mword_of_int (-1) : mword 64))
      by (rewrite /T4; apply upd_eq).
    assert (HT4sp : T4 !!! Regidx csp_rs1 = pa_stk sp0 8)
      by (rewrite /T4 upd_ne; [exact Hmrsp | vm_compute; discriminate]).
    assert (HT4rest : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
                r <> Rs0 -> r <> Rs1 -> r <> Rs4 -> r <> Rs5 -> T4 !!! Regidx r = m !!! Regidx r).
    { intros r Hr Nsp Ns0 Ns1 Ns4 Ns5.
      rewrite /T4 upd_ne; [| regne].
      exact (Hmr_rest r Hr Nsp Ns0 Ns1 Ns4 Ns5). }
    assert (Hpp8a : add_vec_int (mword_of_int (KF + 0x88) : mword 64) 2
                   = mword_of_int (KF + 0x8a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp8a) in "Hpc".
    (* ---- +0x8a: c.ldsp s4,16(sp) ---- *)
    assert (Hpa6 : add_vec (T4 !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000")))
                   = pa_stk sp0 6) by (rewrite HT4sp; apply kfk_frm6).
    iEval (rewrite -Hpa6) in "Hb6".
    iApply (wp_cldsp_s_sconf (mword_of_int (KF + 0x8a)) (mword_of_int 2 : mword 6) Rs4
              T4 (K - 8)%nat (m !!! Regidx Rs4) (match lvl with O => eb | S _ => false end)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi8a Hb6").
    iIntros (CIDs2 Hss2) "Hcg Hpc Hb6". iEval (rewrite Hpa6) in "Hb6".
    set (T5 := <[Regidx Rs4 := regval_into_reg (m !!! Regidx Rs4)]> T4).
    change (<[Regidx Rs4 := regval_into_reg (m !!! Regidx Rs4)]> T4) with T5.
    assert (HT5sp : T5 !!! Regidx csp_rs1 = pa_stk sp0 8)
      by (rewrite /T5 upd_ne; [exact HT4sp | vm_compute; discriminate]).
    assert (HT5s1 : T5 !!! Regidx Rs1 = (mword_of_int (-1) : mword 64))
      by (rewrite /T5 upd_ne; [exact HT4s1 | vm_compute; discriminate]).
    assert (HT5thr : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
                r <> Rs0 -> r <> Rs1 -> r <> Rs5 -> T5 !!! Regidx r = m !!! Regidx r).
    { intros r Hr Nsp Ns0 Ns1 Ns5.
      destruct (decide (r = Rs4)) as [-> | N4]; [rewrite /T5; apply upd_eq |].
      rewrite /T5 upd_ne; [| congruence].
      exact (HT4rest r Hr Nsp Ns0 Ns1 N4 Ns5). }
    assert (Hpp8c : add_vec_int (mword_of_int (KF + 0x8a) : mword 64) 2
                   = mword_of_int (KF + 0x8c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp8c) in "Hpc".
    (* ---- +0x8c: c.j +0xfc ---- *)
    assert (Htgt8c : add_vec (mword_of_int (KF + 0x8c) : mword 64)
                       (sign_extend' 64 (sign_extend' 21
                          (concat_vec (mword_of_int 56 : mword 11) ('b"0"))))
                     = mword_of_int (KF + 0xfc))
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_cj_s_sconf (mword_of_int (KF + 0x8c))
              (sign_extend' 21 (concat_vec (mword_of_int 56 : mword 11) ('b"0")))
              T5 (K - 8)%nat (match lvl with O => eb | S _ => false end)
              ltac:(rewrite Htgt8c; vm_compute; reflexivity)
              with "Hcg Hpc Hi8c").
    iIntros (CIDs3 Hss3). iNext. iIntros "Hcg Hpc".
    iEval (rewrite Htgt8c) in "Hpc".
    (* ---- fall into the shared epilogue ---- *)
    iAssert (kfk_frame sp0 ra0 s00 s10 s50) with "[Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hb7 Hb8]" as "Hframe".
    { rewrite /kfk_frame. iFrame "Hb1 Hb2 Hb3 Hb4 Hb5". iSplitL "Hb6"; [iExists _; iExact "Hb6" |].
      iFrame "Hb7". iExact "Hb8". }
    iApply (kfk_epi_frame m T5 K sp0 ra0 s00 s10 s50 (mword_of_int (-1) : mword 64) pme
              (match lvl with O => eb | S _ => false end)
              (kfkb1_K8 K HK) Hsp0 Hra0 Hs00 Hs10 Hs50 HT5sp HT5s1 HT5thr
              with "Hcg Htext Hpc Hframe").
    iIntros (CIDf Hsf mf) "%Hpost Hcg Hpc".
    iDestruct (cpu_own_transport CIDr CIDf lvl eb pme
                (match lvl with O => eb | S _ => false end)
                ltac:(wp_next_chain) with "Hcpu") as "Hcpu".
    iSpecialize ("Hcont" $! CIDf with "[%]"); [wp_next_chain|].
    iApply ("Hcont" $! mf with "[%] Hcg Hpc Hcpu Henv"). exact Hpost.
  Qed.

End KforkB1Proof.
End KforkB1.
