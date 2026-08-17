(* ProofProcdump.v -- procdump's whole-function proof, assembled.

   The three block lemmas of ProofProcdumpParts.v (prologue / constants /
   epilogue) and the scan of ProofProcdumpLoop.v, joined by the one call
   this file owns: the leading [printk("\n")] at +0x1e.  Sealed as
   [ProcdumpProof : PROCDUMP].

   procdump's callee is printk on its GENERAL path, carried as the Coq
   hypothesis [SpecPrintk.printk_gen_contract] rather than as a functor
   argument, so this proof takes no axiom from it and neither does any
   caller -- the SpecBalloc.v shape.  Consequently there is nothing for
   LinkProcdump.v to instantiate but the module itself.

   The design and the racy-read finding behind [procdump_view] are in
   claude-notes/projects/procdump.md. *)
Set Printing Depth 40.
From Stdlib Require Import ZArith Lia List String Ascii.
From stdpp Require Import gmap list bitvector.definitions.
From iris.algebra Require Import dfrac.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_var gen_heap invariants.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import RiscvExtras.
Require Import RegFile.
Require Import SmodeCore.
Require Import CalleeSaved.
Require Import StackOwn.
Require Import IntrDefs.
Require Import WpNext.
Require Import WpLock.
Require Import DiskPtsto WpUart.
Require Import CpuOwn.
Require Import WpSconfCtl.
Require Import ProcGeom.
Require Import CodeProcdump.
Require Import ProcdumpAux.
Require Import SpecProcdump.
Require Import ProofProcdumpParts.
Require Import ProofProcdumpLoop.
From Kernel Require KernelSyms.
Import Defs.
Local Open Scope Z_scope.

(* the numeric side conditions, mword-free and passed by name *)
Lemma pd_K48 (K : nat) : (58 <= K)%nat -> (48 <= K - 10)%nat.
Proof. lia. Qed.
Lemma pd_K10 (K : nat) : (58 <= K)%nat -> (10 <= K)%nat.
Proof. lia. Qed.
Lemma pd_NPROC_sub0 : (NPROC - 0)%nat = NPROC.
Proof. reflexivity. Qed.
Lemma pd_NPROC_pos : (0 < NPROC)%nat.
Proof. unfold NPROC. lia. Qed.

Module ProcdumpProof : PROCDUMP.
Section ProofProcdumpMain.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ}.
  Context `{!uartGhostG Σ, !diskGhostG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Local Ltac pcw := apply bv_eq; vm_compute; reflexivity.
  Local Ltac nz := vm_compute; discriminate.

  Notation Rra := (mword_of_int 1 : mword 5).
  Notation Ra0 := (mword_of_int 10 : mword 5).

  Lemma wp_procdump_sconf
      (γpr : gname) (γd : uart_names) (γv : disk_names)
      (m : regfile) (K : nat) (eb : bool) (p : mword 64) (b : bool)
      (lks : gset string)
    : wp_procdump_sconf_body γpr γd γv m K eb p b lks.
  Proof.
    cbv beta zeta delta [wp_procdump_sconf_body].
    intros HK Hpk Hlkbelow.
    iIntros "Hcg Hcnt #Htext #Hkdata Hpc #Hpenv Hview Hcont".
    (* ================================================================== *)
    (* +0x00 .. +0x1a -- the frame, the nine saves, a0 := "\n"            *)
    (* ================================================================== *)
    iApply (wp_pd_prologue (CID0 := CID) m K b p ltac:(lia) with "Hcg Htext Hpc").
    iIntros (CID1 Hs1 M) "%Hpro Hcg Hframe Hpc".
    pose proof (pd_regs_hi_of_pro m M Hpro) as HhiM.
    destruct Hpro as (Hprosp & _ & Hproa0 & _).
    (* ================================================================== *)
    (* +0x1e  jal ra,printk -- THE CALL THIS FILE OWNS                    *)
    (* ================================================================== *)
    iPoseProof (pdi_1e with "Htext") as "Hi1e".
    iApply (wp_jal_s_sconf (CID := CID1)
              (mword_of_int (KernelSyms.procdump + 0x1e) : mword 64) Rra
              (mword_of_int 2089436 : mword 21) M (K - 10)%nat b
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi1e").
    iIntros (CID2 Hs2) "Hcg Hpc".
    set (M1 := <[Regidx Rra := regval_into_reg
                  (add_vec_int
                     (mword_of_int (KernelSyms.procdump + 0x1e) : mword 64) 4)]> M).
    assert (Htgt : add_vec (mword_of_int (KernelSyms.procdump + 0x1e) : mword 64)
                     (sign_extend' 64 (mword_of_int 2089436 : mword 21))
                   = mword_of_int KernelSyms.printk) by pcw.
    iEval (rewrite Htgt) in "Hpc".
    assert (HM1ra : M1 !!! Regidx Rra
                    = add_vec_int
                        (mword_of_int (KernelSyms.procdump + 0x1e) : mword 64) 4)
      by (rewrite /M1; apply upd_eq).
    assert (HM1a0 : M1 !!! Regidx Ra0 = (mword_of_int pd_nl_a : mword 64)).
    { rewrite /M1 upd_ne; [ exact Hproa0 | rdok_tpne ]. }
    assert (HM1sp : M1 !!! pdR 2 = pa_stk (m !!! pdR 2 : mword 64) 10).
    { unfold pdR. rewrite /M1 upd_ne; [ exact Hprosp | rdok_tpne ]. }
    (* the jal writes x1 and nothing else, so the four unsaved callee-saved
       registers are still the entry map's *)
    assert (HhiM1 : pd_regs_hi M M1).
    { unfold pd_regs_hi, pdR. rewrite /M1.
      split_and!; (rewrite upd_ne; [ reflexivity | rdok_tpne ]). }
    (* ---- printk("\n"), general path, descs = [] ---- *)
    iPoseProof (pd_nl_str with "Hkdata") as "Hnlstr".
    iDestruct (cpu_own_transport CID CID2 0%nat eb p b
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    iApply (Hpk CID2 M1 (K - 10)%nat eb p DfracDiscarded pd_nl [] b lks
              (pd_K48 K HK) pd_nl_len pd_nl_nonul
              ltac:(rewrite pd_nl_kinds; reflexivity)
              ltac:(cbn [length]; lia)
              with "Hcg Htext Hkdata Hpc Hcnt Hpenv [Hnlstr] []").
    all: try lkbelow.
    { rewrite HM1a0. iExact "Hnlstr". }
    { done. }
    iIntros (CID3 Hs3 mP) "Hcg Hpc %Hcsp Hcnt _ _".
    destruct Hcsp as [Hcs Hra1].
    assert (Hpc22 : ret_pc (M1 !!! Regidx Rra : mword 64)
                    = mword_of_int (KernelSyms.procdump + 0x22))
      by (rewrite HM1ra; pcw).
    iEval (rewrite Hpc22) in "Hpc".
    (* ================================================================== *)
    (* +0x22 .. +0x54 -- the seven hoisted constants                      *)
    (* ================================================================== *)
    iApply (wp_pd_consts (CID0 := CID3) mP (K - 10)%nat b p with "Hcg Htext Hpc").
    iIntros (CID4 Hs4 M') "%Hcon Hcg Hpc".
    destruct Hcon as [Hloop Hhi'].
    (* the stack pointer the scan carries and the epilogue wants back *)
    assert (HmPsp : mP !!! pdR 2 = pa_stk (m !!! pdR 2 : mword 64) 10).
    { unfold pdR.
      rewrite (callee_saved_lookup Hcs (mword_of_int 2 : mword 5)
                 ltac:(vm_compute; reflexivity)).
      exact HM1sp. }
    rewrite HmPsp in Hloop.
    (* m -> M -> M1 -> mP -> M' *)
    assert (Hhifin : pd_regs_hi m M').
    { apply (pd_regs_hi_trans m M M'); [ exact HhiM |].
      apply (pd_regs_hi_trans M M1 M'); [ exact HhiM1 |].
      apply (pd_regs_hi_trans M1 mP M');
        [ exact (pd_regs_hi_of_cs M1 mP Hcs) | exact Hhi' ]. }
    iDestruct (cpu_own_transport CID3 CID4 0%nat eb p b
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    (* ================================================================== *)
    (* +0x56 .. +0x8c -- the scan, entered at its head with j = 0, with   *)
    (* the epilogue (+0x8e .. +0xa2) as its exit continuation.            *)
    (* ================================================================== *)
    iPoseProof (wp_pd_loop (CID0 := CID4) γpr γd γv m
                  (pa_stk (m !!! pdR 2 : mword 64) 10) p (K - 10)%nat eb b lks
                  Hpk (pd_K48 K HK) Hlkbelow
                  with "Htext Hkdata Hpenv [Hframe Hcont]") as "Hscan".
    { iIntros (CIDx Hsx Mx) "%Hxc Hcg Hcnt2 Hpc Hview".
      destruct Hxc as [Hxsp Hxhi].
      iApply (wp_pd_epilogue (CID0 := CIDx) m Mx K b p (pd_K10 K HK) Hxsp Hxhi
                with "Hcg Htext Hpc Hframe").
      iIntros (CIDy Hsy mf) "%Hcsf Hcg Hpc".
      iDestruct (cpu_own_transport CIDx CIDy 0%nat eb p b
                   ltac:(wp_next_chain) with "Hcnt2") as "Hcnt2".
      iSpecialize ("Hcont" $! CIDy with "[%]"); [ wp_next_chain |].
      iApply ("Hcont" $! mf with "Hcg Hpc [%] Hcnt2 Hview").
      exact Hcsf. }
    iApply ("Hscan" $! 0%nat M' with "[%] [%] Hcg Hcnt Hpc [] [Hview]").
    { exact pd_NPROC_pos. }
    { split; [ exact Hloop | exact Hhifin ]. }
    { cbn [seq]. done. }
    { rewrite pd_NPROC_sub0. iExact "Hview". }
  Qed.

End ProofProcdumpMain.
End ProcdumpProof.
