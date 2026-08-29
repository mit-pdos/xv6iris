(* ProofKerneltrap.v -- kerneltrap() over the SIE-agnostic sconf world.

   kerneltrap() @ 0x80002696 is the C trap handler kernelvec calls: it saves
   the trap state, sanity-checks it, demultiplexes through devintr(), yields
   on a timer interrupt if this cpu has a current process, and restores the
   trap state before returning.

   ALL THREE PANIC ARMS ARE DEAD, and that is the point of the contract
   (SpecKerneltrap.v's header).  "not from supervisor mode" is refuted by
   [kt_spp_set_neq] off the SPP mirror, "interrupts enabled" by
   [pop_sstatus_clear_neq] off the [b = false] arm index, and
   [printk(...); panic("kerneltrap")] by the [devintr_ret sc <> 0] premise.
   The third is the one that matters for the axiom ledger: printk's general
   path is unproven, so a live edge to it would have swapped one assumed
   contract for another.

   THE SHAPE OF THE PROOF is the shape of the code.  The head (prologue, the
   three CSR reads, the two panic tests) is [kt_pro] and the epilogue is
   [kt_epi], both in ProofKerneltrapParts.v -- the latter because gcc put it
   at +0x36, in the MIDDLE of the function, so THREE paths reach it: the
   non-timer fall-through, the "no current proc" branch, and the [c.j] after
   yield.  What is left here is the four call sites and the two branches
   between them.

   THE INDEX IS [false] THROUGHOUT: a trap handler runs with interrupts off
   (that is what its own second check establishes), so every leaf is applied
   at [false] and collapsed with [wp_next_off].  The one thing that is NOT
   hart-local is the yield: it parks, so the hart can change, and the
   contract's crossing index is the literal [true].  Everything after the
   yield therefore runs at the resuming hart -- which is exactly why the
   epilogue is a lemma with its own [CID] binder.

   A functor over DEVINTR / MYPROC / YIELD.  Note what is NOT a parameter:
   PANIC and PRINTK, because no arm reaches either.                        *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import WpMmodeLeafBase.
Require Import RegFile.
Require Import RiscvExtras.
Require Import WpGprCsrwCommon.
Require Import StackOwn CalleeSaved.
Require Import WpLock.
Require Import FdSlots.
Require Import ProcGeom.
Require Import IntrDefs.
Require Import HartTp WpNext.
Require Import WpSconfCtl WpSconfBtype.
Require Import WpSmodeIntr.
Require Import DiskPtsto WpUart.
Require Import CodeKerneltrap.
Require Import SpecDevintr SpecMyproc SpecYield.
Require Import SpecKerneltrap ProofKerneltrapParts.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import IrefSlots.
Require Import ProcAvail.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Require Import TsoCtx.
Import Defs.

Local Open Scope Z_scope.
Set Printing Depth 40.

Module KerneltrapProof (Devintr : DEVINTR) (Myproc : MYPROC) (Yield : YIELD)
  : KERNELTRAP.

Section ProofKerneltrap.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.

  Notation ra_idx := (mword_of_int 1 : mword 5).
  Notation s0_idx := (mword_of_int 8 : mword 5).
  Notation s1_idx := (mword_of_int 9 : mword 5).
  Notation a0_idx := (mword_of_int 10 : mword 5).
  Notation a5_idx := (mword_of_int 15 : mword 5).
  Notation s2_idx := (mword_of_int 18 : mword 5).
  Notation s3_idx := (mword_of_int 19 : mword 5).

  Local Ltac pcw := apply bv_eq; vm_compute; reflexivity.

  Lemma wp_kerneltrap_sconf
      (γu : uart_names) (γv : disk_names) (γdk γtl : gname)
      (γs : list gname) (pd pav pu : mword 64)
      (m : regfile) (av : nat) (p : mword 64)
      (ep sc tv : mword 64) (lks : gset string)
    : wp_kerneltrap_sconf_body γu γv γdk γtl γs pd pav pu m av p ep sc tv lks.
  Proof.
    cbv beta delta [wp_kerneltrap_sconf_body].
    intros pcE ret_tgt Hlen Hav Hsc Hepal Hbelow.
    iIntros "Hcg Hmir Havail Hkptr Hcpu #Htext Hpc Hsepc Hscause Hstval #Hcaps Hclm Hcont".
    (* kerneltrap's contract pins depth 0, so the held set is FORCED empty --
       which is what lets the yield arm hand [cpu_own ... ∅] to a contract
       that pins [∅] (SpecYield.v), and what makes devintr's order premise
       trivial. *)
    iDestruct (CpuOwn.cpu_own_zero_empty with "Hcpu") as "[%Hlkempty Hcpu]".
    (* ---- the head: prologue, the three reads, both panic tests ---- *)
    iApply (kt_pro m av ep sc ltac:(lia) Hepal
              with "Hcg Hmir Htext Hpc Hsepc Hscause").
    iIntros (M ms0) "%HMsp %HMs2 %HMs1 %Hms0f %Hsie0 %Hspp0 %Hspie0 %Hthr
                     Hcg Hmir Hsepc Hscause Hpc Hb1 Hb2 Hb3 Hb4 Hb5 Hb6".
    (* name the gap slot's word NOW: left as an [_] at the three [kt_epi]
       applications it becomes an evar, and unifying it inside a
       whole-function goal costs minutes before failing. *)
    iDestruct "Hb6" as (v6) "Hb6".
    (* ---- +0x2a: jal devintr ---- *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.kerneltrap + 0x2a)) ra_idx
              (mword_of_int 2096728 : mword 21) M (av - 6)%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (kti_2a with "Htext"). }
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    set (D0 := <[Regidx ra_idx := regval_into_reg
        (add_vec_int (mword_of_int (KernelSyms.kerneltrap + 0x2a) : mword 64) 4)]> M).
    change (<[Regidx ra_idx := regval_into_reg
        (add_vec_int (mword_of_int (KernelSyms.kerneltrap + 0x2a) : mword 64) 4)]> M) with D0.
    assert (Hpcdi : add_vec (mword_of_int (KernelSyms.kerneltrap + 0x2a) : mword 64)
                      (sign_extend' 64 (mword_of_int 2096728 : mword 21))
                    = mword_of_int KernelSyms.devintr) by pcw.
    iEval (rewrite Hpcdi) in "Hpc".
    assert (HD0ra : D0 !!! Regidx ra_idx
                    = add_vec_int (mword_of_int (KernelSyms.kerneltrap + 0x2a) : mword 64) 4)
      by (rewrite /D0; apply upd_eq).
    assert (HD0sp : D0 !!! Regidx csp_rs1 = pa_stk (m !!! Regidx csp_rs1) 6)
      by (rewrite /D0 upd_ne; [exact HMsp | vm_compute; discriminate]).
    assert (HD0s1 : D0 !!! Regidx s1_idx = sstatus_read ms0)
      by (rewrite /D0 upd_ne; [exact HMs1 | vm_compute; discriminate]).
    assert (HD0s2 : D0 !!! Regidx s2_idx = ep)
      by (rewrite /D0 upd_ne; [exact HMs2 | vm_compute; discriminate]).
    (* devintr's caps are the whole device complement, threaded persistently *)
    iApply (Devintr.wp_devintr_sconf γu γv γdk γtl γs pd pav pu
              D0 (av - 6)%nat 0 false p (DfracOwn 1) sc lks
              Hlen ltac:(change (2^31)%Z with 2147483648%Z; lia)
              ltac:(lia)
              Hbelow
              with "Hcg Hcpu Htext Hpc Hscause Hcaps").
    all: try lkbelow.
    iIntros (mdi) "[%Hcs_di %Hdia0] Hcg Hcpu Hscause Hpc".
    assert (Hpc2e : ret_pc (D0 !!! Regidx ra_idx)
                    = mword_of_int (KernelSyms.kerneltrap + 0x2e))
      by (rewrite HD0ra; pcw).
    iEval (rewrite Hpc2e) in "Hpc".
    (* the frame words and the two stashes survive the call *)
    assert (Hdisp : mdi !!! Regidx csp_rs1 = pa_stk (m !!! Regidx csp_rs1) 6)
      by (rewrite (callee_saved_lookup Hcs_di csp_rs1 ltac:(vm_compute; reflexivity)); exact HD0sp).
    assert (Hdis1 : mdi !!! Regidx s1_idx = sstatus_read ms0)
      by (rewrite (callee_saved_lookup Hcs_di s1_idx ltac:(vm_compute; reflexivity)); exact HD0s1).
    assert (Hdis2 : mdi !!! Regidx s2_idx = ep)
      by (rewrite (callee_saved_lookup Hcs_di s2_idx ltac:(vm_compute; reflexivity)); exact HD0s2).
    assert (Hdithr : kt_thr m mdi).
    { apply (kt_thr_cs m M mdi Hthr).
      apply (callee_saved_trans M D0 mdi); [| exact Hcs_di].
      unfold callee_saved. split_and!;
        try (rewrite /D0 upd_ne; [reflexivity | vm_compute; discriminate]). }
    (* ---- +0x2e: c.beqz a0 -> printk/panic.  DEAD: devintr recognised the
       cause, so its return value is nonzero. ---- *)
    iApply (wp_cbeqz_fall_s_sconf (mword_of_int (KernelSyms.kerneltrap + 0x2e))
              (mword_of_int 27 : mword 8) (Cregidx (mword_of_int 2)) a0_idx
              mdi (av - 6)%nat false
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
              ltac:(rgne; rewrite Hdia0; apply not_true_iff_false; intro Hz;
                    apply eq_vec_true_iff in Hz; apply Hsc;
                    rewrite Hz; apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (kti_2e with "Htext"). }
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    assert (Hpc30 : add_vec_int (mword_of_int (KernelSyms.kerneltrap + 0x2e) : mword 64) 2
                    = mword_of_int (KernelSyms.kerneltrap + 0x30)) by pcw.
    iEval (rewrite Hpc30) in "Hpc".
    (* ---- +0x30: c.li a5,2 ---- *)
    iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.kerneltrap + 0x30)) a5_idx
              (mword_of_int 2 : mword 6)
              (add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 2 : mword 6))))
              mdi (av - 6)%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok) eq_refl
              with "Hcg Hpc []").
    { iApply (kti_30 with "Htext"). }
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    set (D1 := <[Regidx a5_idx := regval_into_reg
        (add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 2 : mword 6))))]> mdi).
    change (<[Regidx a5_idx := regval_into_reg
        (add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 2 : mword 6))))]> mdi) with D1.
    assert (HD1sp : D1 !!! Regidx csp_rs1 = pa_stk (m !!! Regidx csp_rs1) 6)
      by (rewrite /D1 upd_ne; [exact Hdisp | vm_compute; discriminate]).
    assert (HD1s1 : D1 !!! Regidx s1_idx = sstatus_read ms0)
      by (rewrite /D1 upd_ne; [exact Hdis1 | vm_compute; discriminate]).
    assert (HD1s2 : D1 !!! Regidx s2_idx = ep)
      by (rewrite /D1 upd_ne; [exact Hdis2 | vm_compute; discriminate]).
    assert (HD1a0 : D1 !!! Regidx a0_idx = devintr_ret sc)
      by (rewrite /D1 upd_ne; [exact Hdia0 | vm_compute; discriminate]).
    assert (HD1thr : kt_thr m D1).
    { intros r Hr Hsp Hs0 Hs1 Hs2 Hs3.
      rewrite /D1 upd_ne; [| ktne_a5 ]. apply Hdithr; assumption. }
    assert (Hpc32 : add_vec_int (mword_of_int (KernelSyms.kerneltrap + 0x30) : mword 64) 2
                    = mword_of_int (KernelSyms.kerneltrap + 0x32)) by pcw.
    iEval (rewrite Hpc32) in "Hpc".
    (* the epilogue arrives with these, whichever path we take *)
    iAssert (⌜ D1 !!! Regidx a5_idx
               = add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 2 : mword 6))) ⌝)%I
      as %HD1a5; [ iPureIntro; rewrite /D1; apply upd_eq |].
    (* ---- +0x32: beq a0,a5 -- the timer test.  [devintr_ret sc] is 1 or 2
       ([Hsc] rules out 0), so this is a genuine two-way split: 1 falls
       through to the epilogue, 2 takes the myproc/yield arm. ---- *)
    destruct (decide (eq_vec (rget D1 a0_idx) (rget D1 a5_idx) = true)) as [Htim|Htim].
    - (* ===== the TIMER path ===== *)
      iApply (wp_beq_taken_s_sconf (mword_of_int (KernelSyms.kerneltrap + 0x32))
                (mword_of_int 84 : mword 13) a5_idx a0_idx D1 (av - 6)%nat false
                ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                Htim ltac:(vm_compute; reflexivity)
                with "Hcg Hpc []").
      { iApply (kti_32 with "Htext"). }
      iApply bi.later_intro. iApply wp_next_off_intro. iIntros "Hcg Hpc".
      assert (Hpc86 : add_vec (mword_of_int (KernelSyms.kerneltrap + 0x32) : mword 64)
                        (sign_extend' 64 (mword_of_int 84 : mword 13))
                      = mword_of_int (KernelSyms.kerneltrap + 0x86)) by pcw.
      iEval (rewrite Hpc86) in "Hpc".
      (* ---- +0x86: jal myproc ---- *)
      iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.kerneltrap + 0x86)) ra_idx
                (mword_of_int 2093478 : mword 21) D1 (av - 6)%nat false
                ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
                with "Hcg Hpc []").
      { iApply (kti_86 with "Htext"). }
      iApply wp_next_off_intro. iIntros "Hcg Hpc".
      set (D2 := <[Regidx ra_idx := regval_into_reg
          (add_vec_int (mword_of_int (KernelSyms.kerneltrap + 0x86) : mword 64) 4)]> D1).
      change (<[Regidx ra_idx := regval_into_reg
          (add_vec_int (mword_of_int (KernelSyms.kerneltrap + 0x86) : mword 64) 4)]> D1) with D2.
      assert (Hpcmp : add_vec (mword_of_int (KernelSyms.kerneltrap + 0x86) : mword 64)
                        (sign_extend' 64 (mword_of_int 2093478 : mword 21))
                      = mword_of_int KernelSyms.myproc) by pcw.
      iEval (rewrite Hpcmp) in "Hpc".
      assert (HD2ra : D2 !!! Regidx ra_idx
                      = add_vec_int (mword_of_int (KernelSyms.kerneltrap + 0x86) : mword 64) 4)
        by (rewrite /D2; apply upd_eq).
      assert (HD2sp : D2 !!! Regidx csp_rs1 = pa_stk (m !!! Regidx csp_rs1) 6)
        by (rewrite /D2 upd_ne; [exact HD1sp | vm_compute; discriminate]).
      assert (HD2s1 : D2 !!! Regidx s1_idx = sstatus_read ms0)
        by (rewrite /D2 upd_ne; [exact HD1s1 | vm_compute; discriminate]).
      assert (HD2s2 : D2 !!! Regidx s2_idx = ep)
        by (rewrite /D2 upd_ne; [exact HD1s2 | vm_compute; discriminate]).
      assert (HD2thr : kt_thr m D2).
      { intros r Hr Hsp Hs0 Hs1 Hs2 Hs3.
        rewrite /D2 upd_ne; [| ktne_ra ]. apply HD1thr; assumption. }
      iApply (Myproc.wp_myproc_sconf D2 (av - 6)%nat 0 false p false _
                ltac:(change (2^31)%Z with 2147483648%Z; lia)
              ltac:(lia)
                with "Hcg Hcpu Htext Hpc").
      iApply wp_next_off_intro.
      iIntros (msmp mmp) "%Hmpf Hcg Hcpu Hpc [%Hcs_mp %Hmpa0]".
      assert (Hpc8a : ret_pc (D2 !!! Regidx ra_idx)
                      = mword_of_int (KernelSyms.kerneltrap + 0x8a))
        by (rewrite HD2ra; pcw).
      iEval (rewrite Hpc8a) in "Hpc".
      assert (Hmpsp : mmp !!! Regidx csp_rs1 = pa_stk (m !!! Regidx csp_rs1) 6)
        by (rewrite (callee_saved_lookup Hcs_mp csp_rs1 ltac:(vm_compute; reflexivity)); exact HD2sp).
      assert (Hmps1 : mmp !!! Regidx s1_idx = sstatus_read ms0)
        by (rewrite (callee_saved_lookup Hcs_mp s1_idx ltac:(vm_compute; reflexivity)); exact HD2s1).
      assert (Hmps2 : mmp !!! Regidx s2_idx = ep)
        by (rewrite (callee_saved_lookup Hcs_mp s2_idx ltac:(vm_compute; reflexivity)); exact HD2s2).
      assert (Hmpthr : kt_thr m mmp) by (apply (kt_thr_cs m D2 mmp HD2thr Hcs_mp)).
      (* ---- +0x8a: c.beqz a0 -- no current proc?  Genuine split. ---- *)
      destruct (decide (eq_vec (rget mmp a0_idx) zero_reg = true)) as [Hp0|Hp0].
      + (* ----- no current proc: straight to the epilogue ----- *)
        iApply (wp_cbeqz_taken_s_sconf (mword_of_int (KernelSyms.kerneltrap + 0x8a))
                  (mword_of_int 214 : mword 8) (Cregidx (mword_of_int 2)) a0_idx
                  mmp (av - 6)%nat false
                  ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                  Hp0 ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc []").
        { iApply (kti_8a with "Htext"). }
        iApply bi.later_intro. iApply wp_next_off_intro. iIntros "Hcg Hpc".
        assert (Hpcb : add_vec (mword_of_int (KernelSyms.kerneltrap + 0x8a) : mword 64)
                         (sign_extend' 64 (sign_extend' 13 (concat_vec (mword_of_int 214 : mword 8) ('b"0"))))
                       = mword_of_int (KernelSyms.kerneltrap + 0x36)) by pcw.
        iEval (rewrite Hpcb) in "Hpc".
        iApply (kt_epi m mmp (m !!! Regidx csp_rs1)
                  (m !!! Regidx ra_idx) (m !!! Regidx s0_idx) (m !!! Regidx s1_idx)
                  (m !!! Regidx s2_idx) (m !!! Regidx s3_idx) v6
                  ep ep ms0 (av - 6)%nat 0 ('b"1") ('b"1") lks
                  ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity)
                  ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity)
                  Hmpsp Hmps2 Hmps1 Hepal Hms0f Hsie0 Hspp0 Hspie0 Hmpthr
                  with "Hcg Hmir Hcpu Htext Hpc Hsepc Hb1 Hb2 Hb3 Hb4 Hb5 Hb6").
        iIntros (mf ms_f) "%Hcsf %Hsppf %Hspief %Hsief Hcgat Hmir Hcpu Hsepc Hpc".
        assert (Hav6 : ((av - 6) + 6)%nat = av)
          by (lia).
        iEval (rewrite Hav6) in "Hcgat".
        (* the hart cannot have moved: no yield on this path. *)
        (* NO RE-SEAL NEEDED.  [intr_res] is [Typeclasses Opaque], so a
           branch's [iNext] cannot descend into it and strip the later off
           the handler spec -- the repair its predecessor [intr_handler_avail]
           needed at all three of this proof's continuation sites. *)
        iRename "Havail" into "Havz".
        iSpecialize ("Hcont" $! CID with "[]"); [iPureIntro; intros _; reflexivity|].
        iApply ("Hcont" $! mf ms_f sc tv with "[%] [%] [%] [%] Hcgat Hmir Havz Hkptr Hcpu
                              Hsepc Hscause Hstval Hpc Hclm").
        { exact Hcsf. }
        { exact Hsppf. } { exact Hspief. } { exact Hsief. }
      + (* ----- there IS a current proc: yield, then the epilogue ----- *)
        iApply (wp_cbeqz_fall_s_sconf (mword_of_int (KernelSyms.kerneltrap + 0x8a))
                  (mword_of_int 214 : mword 8) (Cregidx (mword_of_int 2)) a0_idx
                  mmp (av - 6)%nat false
                  ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                  ltac:(apply not_true_iff_false; exact Hp0)
                  with "Hcg Hpc []").
        { iApply (kti_8a with "Htext"). }
        iApply wp_next_off_intro. iIntros "Hcg Hpc".
        assert (Hpc8c : add_vec_int (mword_of_int (KernelSyms.kerneltrap + 0x8a) : mword 64) 2
                        = mword_of_int (KernelSyms.kerneltrap + 0x8c)) by pcw.
        iEval (rewrite Hpc8c) in "Hpc".
        (* a0 = p and a0 <> 0, so this cpu's proc is a real slot: that is what
           [IntrDefs.cpu_claim]'s disjunction is keyed on.  The claim is the
           trap's own -- taking the trap cleared SIE and so dismantled
           [sie_arm true p] -- and it is what names the proc yield parks.
           Read the index out and put the claim straight back: yield wants it
           whole. *)
        assert (Hpne : p <> zero_reg).
        { intro He. apply Hp0. rgne. rewrite Hmpa0 He. apply eq_vec_true_iff. reflexivity. }
        iAssert (∃ jj : nat, ⌜(jj < NPROC)%nat⌝ ∗ ⌜proc_addr jj = p⌝ ∗ cpu_claim p)%I
          with "[Hclm]" as (j) "(%Hj & %Hpj & Hclm)".
        { iDestruct "Hclm" as "[%Hz | Hc]"; [ exfalso; exact (Hpne Hz) |].
          iDestruct "Hc" as (j') "([%Hpj' %Hj'] & Hps & Hht)".
          iExists j'. iSplit; [done|]. iSplit; [done|].
          iRight. iExists j'. iFrame "Hps Hht". done. }
        (* yield states everything at [proc_addr j] and ours is at [p];
           [Hpj] is the bridge.  NOT [subst p]: myproc's postcondition also
           defines p ([Hmpa0]), and subst picks that equation instead. *)
        iEval (rewrite -Hpj) in "Hcg".
        iEval (rewrite -Hpj) in "Hcpu".
        (* ---- +0x8c: jal yield ---- *)
        iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.kerneltrap + 0x8c)) ra_idx
                  (mword_of_int 2094990 : mword 21) mmp (av - 6)%nat false
                  ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc []").
        { iApply (kti_8c with "Htext"). }
        iApply wp_next_off_intro. iIntros "Hcg Hpc".
        set (Y0 := <[Regidx ra_idx := regval_into_reg
            (add_vec_int (mword_of_int (KernelSyms.kerneltrap + 0x8c) : mword 64) 4)]> mmp).
        change (<[Regidx ra_idx := regval_into_reg
            (add_vec_int (mword_of_int (KernelSyms.kerneltrap + 0x8c) : mword 64) 4)]> mmp) with Y0.
        assert (Hpcyd : add_vec (mword_of_int (KernelSyms.kerneltrap + 0x8c) : mword 64)
                          (sign_extend' 64 (mword_of_int 2094990 : mword 21))
                        = mword_of_int KernelSyms.yield) by pcw.
        iEval (rewrite Hpcyd) in "Hpc".
        assert (HY0ra : Y0 !!! Regidx ra_idx
                        = add_vec_int (mword_of_int (KernelSyms.kerneltrap + 0x8c) : mword 64) 4)
          by (rewrite /Y0; apply upd_eq).
        assert (HY0sp : Y0 !!! Regidx csp_rs1 = pa_stk (m !!! Regidx csp_rs1) 6)
          by (rewrite /Y0 upd_ne; [exact Hmpsp | vm_compute; discriminate]).
        assert (HY0s1 : Y0 !!! Regidx s1_idx = sstatus_read ms0)
          by (rewrite /Y0 upd_ne; [exact Hmps1 | vm_compute; discriminate]).
        assert (HY0s2 : Y0 !!! Regidx s2_idx = ep)
          by (rewrite /Y0 upd_ne; [exact Hmps2 | vm_compute; discriminate]).
        assert (HY0thr : kt_thr m Y0).
        { intros r Hr Hsp Hs0 Hs1 Hs2 Hs3.
          rewrite /Y0 upd_ne; [| ktne_ra ]. apply Hmpthr; assumption. }
        (* the proc's lock ghost, and the trap CSRs the crossing carries:
           at [eb = false] yield takes them from US, because there is no
           enabled arm to dismantle. *)
        iDestruct "Hcaps" as "(#Hdev & #Hccaps & #Hgeom & #Hdisk & #Htimer & #Htick & #Hprocs)".
        (* [j < NPROC] and [length γs = NPROC] give a slot ghost for proc j *)
        assert (Hjl : (j < length γs)%nat) by (rewrite Hlen; exact Hj).
        destruct (lookup_lt_is_Some_2 γs j Hjl) as [γl Hgl].
        iEval (rewrite Hlkempty) in "Hcpu".
        iApply (Yield.wp_yield_sconf γs j γl Y0 (av - 6)%nat false
                  Hj Hgl ltac:(lia)
                  with "Hcg Hcpu Htext Hpc Hprocs [Hsepc Hscause Hstval Hmir Havail Hkptr] [Hclm]").
        (* THE HANDLER RESOURCE GOES INTO THE PARK, as the fifth member of
           [trap_csrs] -- and comes back out of yield's post as the RESUMING
           hart's.  It used to be a persistent credential framed around the
           call and re-delivered separately ([intr_handler_avail_ext]); being
           owned, it simply travels with the cells it belongs with. *)
        { rewrite /trap_csrs_ext /trap_csrs.
          iSplitL "Hsepc". { iExists ep. iExact "Hsepc". }
          iSplitL "Hscause". { iExists sc. iExact "Hscause". }
          iSplitL "Hstval". { iExists tv. iExact "Hstval". }
          iSplitL "Hmir". { iExists ('b"1"), ('b"1"). iExact "Hmir". }
          iSplitL "Havail". { iExact "Havail". }
          iExact "Hkptr". }
        (* THE CLAIM THE TRAP HANDED US, spent on yield.  At [eb = false]
           there is no arm to take it from, which is exactly why a preempting
           trap must arrive holding it. *)
        { rewrite /cpu_claim_ext -Hpj. iExact "Hclm". }
        iIntros (CIDy Hsy myd) "%Hcs_yd Hcg Hcpu Hpc Hext Hclm".
        iEval (rewrite Hpj) in "Hcg". iEval (rewrite Hpj) in "Hcpu".
        (* back, possibly on ANOTHER hart: the trap CSRs are that hart's *)
        rewrite /trap_csrs_ext /trap_csrs.
        iDestruct "Hext" as "(Hsepc & Hscause & Hstval & Hmir & Havail_y & Hkptr_y)".
        iDestruct "Hsepc" as (ep') "Hsepc".
        iDestruct "Hscause" as (sc') "Hscause".
        iDestruct "Hstval" as (tv') "Hstval".
        iDestruct "Hmir" as (va vb) "Hmir".
        assert (Hpc90 : ret_pc (Y0 !!! Regidx ra_idx)
                        = mword_of_int (KernelSyms.kerneltrap + 0x90))
          by (rewrite HY0ra; pcw).
        iEval (rewrite Hpc90) in "Hpc".
        assert (Hydsp : myd !!! Regidx csp_rs1 = pa_stk (m !!! Regidx csp_rs1) 6)
          by (rewrite (callee_saved_lookup Hcs_yd csp_rs1 ltac:(vm_compute; reflexivity)); exact HY0sp).
        assert (Hyds1 : myd !!! Regidx s1_idx = sstatus_read ms0)
          by (rewrite (callee_saved_lookup Hcs_yd s1_idx ltac:(vm_compute; reflexivity)); exact HY0s1).
        assert (Hyds2 : myd !!! Regidx s2_idx = ep)
          by (rewrite (callee_saved_lookup Hcs_yd s2_idx ltac:(vm_compute; reflexivity)); exact HY0s2).
        assert (Hydthr : kt_thr m myd) by (apply (kt_thr_cs m Y0 myd HY0thr Hcs_yd)).
        (* ---- +0x90: c.j -> the epilogue ---- *)
        iApply (wp_cj_s_sconf (mword_of_int (KernelSyms.kerneltrap + 0x90))
                  (sign_extend' 21 (concat_vec (mword_of_int 2003 : mword 11) ('b"0")))
                  myd (av - 6)%nat false ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc []").
        { iApply (kti_90 with "Htext"). }
        iApply wp_next_off_intro. iApply bi.later_intro. iIntros "Hcg Hpc".
        assert (Hpcj : add_vec (mword_of_int (KernelSyms.kerneltrap + 0x90) : mword 64)
                         (sign_extend' 64 (sign_extend' 21 (concat_vec (mword_of_int 2003 : mword 11) ('b"0"))))
                       = mword_of_int (KernelSyms.kerneltrap + 0x36)) by pcw.
        iEval (rewrite Hpcj) in "Hpc".
        iApply (kt_epi m myd (m !!! Regidx csp_rs1)
                  (m !!! Regidx ra_idx) (m !!! Regidx s0_idx) (m !!! Regidx s1_idx)
                  (m !!! Regidx s2_idx) (m !!! Regidx s3_idx) v6
                  ep ep' ms0 (av - 6)%nat 0 va vb ∅   (* yield returned at the empty set *)
                  ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity)
                  ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity)
                  Hydsp Hyds2 Hyds1 Hepal Hms0f Hsie0 Hspp0 Hspie0 Hydthr
                  with "Hcg Hmir Hcpu Htext Hpc Hsepc Hb1 Hb2 Hb3 Hb4 Hb5 Hb6").
        iIntros (mf ms_f) "%Hcsf %Hsppf %Hspief %Hsief Hcgat Hmir Hcpu Hsepc Hpc".
        assert (Hav6 : ((av - 6) + 6)%nat = av)
          by (lia).
        iEval (rewrite Hav6) in "Hcgat".
        (* THE HART MAY HAVE MOVED (yield parks).  The crossing index is the
           literal [true], so the left disjunct is absurd, and the right one
           is refuted by [Hpne]: this cpu HAS a current process, which is
           precisely why the yield happened at all. *)
        (* NO RE-SEAL NEEDED -- see the twin on the no-yield path above. *)
        iRename "Havail_y" into "Havz".
        (* yield handed the bundle back at the literal [∅] (its contract pins
           it); [lks = ∅] at depth 0 makes that kerneltrap's own set. *)
        iEval (rewrite -Hlkempty) in "Hcpu".
        iSpecialize ("Hcont" $! CIDy with "[%]").
        { intros [Hf | Hz]; [ discriminate | exfalso; exact (Hpne Hz) ]. }
        iApply ("Hcont" $! mf ms_f sc' tv' with "[%] [%] [%] [%] Hcgat Hmir Havz Hkptr_y Hcpu
                              Hsepc Hscause Hstval Hpc [Hclm]").
        { exact Hcsf. }
        { exact Hsppf. } { exact Hspief. } { exact Hsief. }
        (* the claim comes back out of yield at [cpu_claim_ext false], i.e.
           whole: the resumed thread is RUNNING again and holds half #2. *)
        { rewrite /cpu_claim_ext -Hpj. iExact "Hclm". }
    - (* ===== the NON-timer path: straight to the epilogue ===== *)
      iApply (wp_beq_fall_s_sconf (mword_of_int (KernelSyms.kerneltrap + 0x32))
                (mword_of_int 84 : mword 13) a5_idx a0_idx D1 (av - 6)%nat false
                ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                ltac:(apply not_true_iff_false; exact Htim)
                with "Hcg Hpc []").
      { iApply (kti_32 with "Htext"). }
      iApply wp_next_off_intro. iIntros "Hcg Hpc".
      assert (Hpc36 : add_vec_int (mword_of_int (KernelSyms.kerneltrap + 0x32) : mword 64) 4
                      = mword_of_int (KernelSyms.kerneltrap + 0x36)) by pcw.
      iEval (rewrite Hpc36) in "Hpc".
      iApply (kt_epi m D1 (m !!! Regidx csp_rs1)
                (m !!! Regidx ra_idx) (m !!! Regidx s0_idx) (m !!! Regidx s1_idx)
                (m !!! Regidx s2_idx) (m !!! Regidx s3_idx) v6
                ep ep ms0 (av - 6)%nat 0 ('b"1") ('b"1") lks
                ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity)
                ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity)
                HD1sp HD1s2 HD1s1 Hepal Hms0f Hsie0 Hspp0 Hspie0 HD1thr
                with "Hcg Hmir Hcpu Htext Hpc Hsepc Hb1 Hb2 Hb3 Hb4 Hb5 Hb6").
      iIntros (mf ms_f) "%Hcsf %Hsppf %Hspief %Hsief Hcgat Hmir Hcpu Hsepc Hpc".
        assert (Hav6 : ((av - 6) + 6)%nat = av)
          by (lia).
        iEval (rewrite Hav6) in "Hcgat".
      (* NO RE-SEAL NEEDED -- see the twin above. *)
      iRename "Havail" into "Havz".
      iSpecialize ("Hcont" $! CID with "[]"); [iPureIntro; intros _; reflexivity|].
      iApply ("Hcont" $! mf ms_f sc tv with "[%] [%] [%] [%] Hcgat Hmir Havz Hkptr Hcpu
                            Hsepc Hscause Hstval Hpc Hclm").
      { exact Hcsf. }
      { exact Hsppf. } { exact Hspief. } { exact Hsief. }
  Qed.

End ProofKerneltrap.

End KerneltrapProof.
