(* ProofKforkB7.v -- kfork's SIX-INSTRUCTION STRETCH, +0x066 .. +0x07a,
   between the trapframe copy loop's exit and the fd-scan's entry:

     +0x066  ld a5,88(s4)      (a5 = np->trapframe)
     +0x06a  sd zero,112(a5)   (np->trapframe->a0 = 0; word index 14)
     +0x06e  addi s1,s5,208    (s1 = &p->ofile[0])
     +0x072  addi s2,s4,208    (s2 = &np->ofile[0])
     +0x076  addi s3,s5,336    (s3 = &p->ofile[16] = &p->cwd)
     +0x07a  c.j +28 -> +0x96  (enter the fd scan at its TEST)

   Straight line, [b = false] throughout (the child's lock is held from
   allocproc through the release at +0xc4), so every leaf closes with
   [wp_next_off_intro] and there is no hart-migration bookkeeping at all --
   the same shape [ProofKforkB2]'s copy loop uses.

   THE STATEMENT IS RELATIVE TO ITS OWN ENTRY MAP [M], not kfork's function
   entry map: at this point the frame is pushed, s0 is the frame pointer,
   s4 is the child and s5 is the parent, so a premise tying [M] to kfork's
   ENTRY map would be false.  The only two registers this block's straight
   line CARES about on entry are s4 (=np) and s5 (=p); every callee-saved
   register this block does not write (i.e. everything except s1/s2/s3)
   comes back unchanged relative to [M] -- exactly the shape
   [ProofKforkB2.kfk_tf_copy_loop] uses for the same reason.

   THE RESOURCE: the child's [ProcInv.proc_priv_nocwd] -- it is still in
   the construction window, its [p->cwd] is 0 -- opened with
   [ProofKforkParts.proc_priv_nocwd_tf_upd] (which lends the [p_trapframe] cell
   WHOLE plus the bare [tf_page], and takes back a possibly-different
   [ws']) -- the accessor for both the [ld] (reads the pointer) and the
   [sd] (writes trapframe word 14, [ProcGeom.tf_arg_idx 0]) here. *)
From Stdlib Require Import Eqdep_dec ZArith Lia List.
From stdpp Require Import gmap list list_monad bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_var gen_heap invariants.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvModelBytes.
Require Import RiscvExtras.
Require Import RegFile.
Require Import WpNext.
Require Import WpMmodeLeafBase.
Require Import SmodeCore.
Require Import StackOwn.
Require Import CalleeSaved.
Require Import KernelRvcDecode.
Require Import InstrBytes.
Require Import KernelText.
Require Import WpSconfAlu WpSconfMem WpSconfCtl WpSconfBtype.
Require Import IntrDefs.
Require Import PageGeom PageFields.
Require Import ProcGeom.
Require Import PtBuild.
Require Import UserPtTree.
Require Import ProcPtOwn.
Require Import FdSlots FileInv.
Require Import WpLock.
Require Import SwtchCtx.
Require Import ProcInv.
Require Import KallocInv.
Require Import SpecFreeproc.
Require Import ProofKforkParts.
Require Import CodeKfork.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.

(* A syscall-altitude goal carries [ProcInv.tf_page]'s 4096-conjunct big-op;
   printing one takes tens of minutes, so a one-line mistake reads as a hang.
   durable-notes.md's rule. *)
Set Printing Depth 40.

Notation KF := KernelSyms.kfork (only parsing).

(* ===================================================================== *)
(*  THE STORE ADDRESS'S ARITHMETIC: [112(a5)] is trapframe word 14.      *)
(*  Pure address arithmetic, no [Σ] needed -- lives at top level like    *)
(*  [ProofKforkParts.kfk_tf_disp]/[kfk_tf_step], which this mirrors.      *)
(* ===================================================================== *)
Lemma kfkb7_tf14_addr (tfp : mword 44) :
  add_vec (page_base tfp) (sign_extend' 64 (mword_of_int 112 : mword 12))
  = a_tf_word tfp 14.
Proof.
  rewrite (kfk_avi (page_base tfp) 112 ltac:(apply bv_eq; vm_compute; reflexivity)).
  rewrite /a_tf_word /pa_add. f_equal.
Qed.

Section KforkB7.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fileG Σ, !fdslotG Σ, !irefslotG Σ}.
  Context `{GEN : GenId} `{CID0 : CpuId}.

  Notation Ra5 := (mword_of_int 15 : mword 5).
  Notation Rs1 := (mword_of_int 9 : mword 5).
  Notation Rs2 := (mword_of_int 18 : mword 5).
  Notation Rs3 := (mword_of_int 19 : mword 5).
  Notation Rs4 := (mword_of_int 20 : mword 5).
  Notation Rs5 := (mword_of_int 21 : mword 5).

  Local Ltac regne := reg_ne_side.

  (* a non-destructive length fact off [tf_page] -- durable-notes' "iDestruct
     (lem with …) as %pure keeps the spatial input when the conclusion is
     pure" rule, so this can be read off [Htfp] without losing it. *)
  Lemma kfkb7_tf_len (tfp : mword 44) (ws : list (mword 64)) :
    tf_page tfp ws -∗ ⌜length ws = TFWORDS⌝.
  Proof. iIntros "(%Hlen & _ & _)". done. Qed.

  (* =================================================================== *)
  (*  THE BLOCK.                                                          *)
  (* =================================================================== *)
  Lemma kfk_b7 (γf : gname) (npa pme : mword 64) (pid_c : mword 32) (V : pprivate)
      (M : regfile) (n : nat) (p : mword 64) :
    M !!! Regidx Rs4 = npa ->
    M !!! Regidx Rs5 = pme ->
    sie_cap_gpr M n false p -∗
    kernel_text -∗
    pc_is (mword_of_int (KF + 0x66) : mword 64) -∗
    proc_priv_nocwd γf npa pid_c V -∗
    wp_next false p (fun (CID : CpuId) =>
      ∀ Mx : regfile,
        ⌜ Mx !!! Regidx Rs1 = p_ofile pme 0 /\ Mx !!! Regidx Rs2 = p_ofile npa 0 /\
          Mx !!! Regidx Rs3 = p_cwd pme /\ Mx !!! Regidx Rs4 = npa /\
          Mx !!! Regidx Rs5 = pme /\
          (forall r : mword 5, is_cs_idx r = true ->
              r <> Rs1 -> r <> Rs2 -> r <> Rs3 -> Mx !!! Regidx r = M !!! Regidx r) ⌝ -∗
        sie_cap_gpr Mx n false p -∗
        pc_is (mword_of_int (KF + 0x96) : mword 64) -∗
        proc_priv_nocwd γf npa pid_c (upd_pt V (pv_upt V) (<[(14%nat) := zero_reg]> (pv_tf V))) -∗
        WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HM4 HM5.
    iIntros "Hcg #Htext Hpc Hpv Hcont".
    iPoseProof (kfk_066 with "Htext") as "Hi066".
    iPoseProof (kfk_06a with "Htext") as "Hi06a".
    iPoseProof (kfk_06e with "Htext") as "Hi06e".
    iPoseProof (kfk_072 with "Htext") as "Hi072".
    iPoseProof (kfk_076 with "Htext") as "Hi076".
    iPoseProof (kfk_07a with "Htext") as "Hi07a".
    (* ---- open the child's proc_priv for the read+write on its trapframe ---- *)
    iDestruct (proc_priv_nocwd_tf_upd with "Hpv") as "(Htf & Htfp & Hclose)".
    iDestruct (kfkb7_tf_len with "Htfp") as %Hlen14.
    assert (Hidx14 : (14 < length (pv_tf V))%nat) by (rewrite Hlen14; unfold TFWORDS; lia).
    destruct (lookup_lt_is_Some_2 (pv_tf V) (14%nat) Hidx14) as [w14 Hw14].
    iDestruct (tf_page_word_upd (ud_tfp (pv_upt V)) (pv_tf V) (14%nat) w14 Hw14 with "Htfp")
      as "[Hcell Hback]".
    (* ---- +0x66: ld a5,88(s4) ---- *)
    assert (Htgt66 : add_vec (M !!! Regidx Rs4) (sign_extend' 64 (mword_of_int 88 : mword 12))
                     = p_trapframe npa) by (rewrite HM4; reflexivity).
    iApply (wp_ld_s_sconf (mword_of_int (KF + 0x66) : mword 64) Ra5 Rs4 (mword_of_int 88 : mword 12)
              M n (page_base (ud_tfp (pv_upt V))) false (dqm := DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi066 [Htf] [-]").
    { iEval (rgne; rewrite Htgt66). iExact "Htf". }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc Htf". iEval (rgne; rewrite Htgt66) in "Htf".
    set (T1 := <[Regidx Ra5 := regval_into_reg (page_base (ud_tfp (pv_upt V)))]> M).
    assert (HT1a5 : T1 !!! Regidx Ra5 = page_base (ud_tfp (pv_upt V)))
      by (rewrite /T1 upd_eq; reflexivity).
    assert (HT1s4 : T1 !!! Regidx Rs4 = npa)
      by (rewrite /T1 upd_ne; [exact HM4 | vm_compute; discriminate]).
    assert (HT1s5 : T1 !!! Regidx Rs5 = pme)
      by (rewrite /T1 upd_ne; [exact HM5 | vm_compute; discriminate]).
    assert (Hpp06a : add_vec_int (mword_of_int (KF + 0x66) : mword 64) 4
                     = mword_of_int (KF + 0x6a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp06a) in "Hpc".
    (* ---- +0x6a: sd zero,112(a5) ---- *)
    assert (Htgt6a : add_vec (T1 !!! Regidx Ra5) (sign_extend' 64 (mword_of_int 112 : mword 12))
                     = a_tf_word (ud_tfp (pv_upt V)) 14)
      by (rewrite HT1a5; apply kfkb7_tf14_addr).
    iApply (wp_sd_zero_s_sconf (mword_of_int (KF + 0x6a) : mword 64) Ra5 (mword_of_int 112 : mword 12)
              T1 n w14 false
              with "Hcg Hpc Hi06a [Hcell] [-]").
    { iEval (rgne; rewrite Htgt6a). iExact "Hcell". }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc Hcell". iEval (rgne; rewrite Htgt6a) in "Hcell".
    assert (Hpp06e : add_vec_int (mword_of_int (KF + 0x6a) : mword 64) 4
                     = mword_of_int (KF + 0x6e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp06e) in "Hpc".
    (* ---- close the child's proc_priv back up, at word 14 zeroed ---- *)
    iDestruct ("Hback" $! (zero_reg : mword 64) with "Hcell") as "Htfp".
    iDestruct ("Hclose" $! (<[(14%nat) := zero_reg]> (pv_tf V)) with "Htf Htfp") as "Hpv".
    (* ---- +0x6e: addi s1,s5,208 ---- *)
    iApply (wp_addi4_s_sconf (mword_of_int (KF + 0x6e) : mword 64) Rs1 Rs5 (mword_of_int 208 : mword 12)
              T1 n false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi06e [-]").
    iApply wp_next_off_intro. iIntros "Hcg Hpc". iEval (rgne) in "Hcg".
    set (T2 := <[Regidx Rs1 := regval_into_reg
                  (add_vec (T1 !!! Regidx Rs5) (sign_extend' 64 (mword_of_int 208 : mword 12)))]> T1).
    assert (HT2s1 : T2 !!! Regidx Rs1 = p_ofile pme 0).
    { rewrite /T2 upd_eq HT1s5. apply p_ofile_zero. }
    assert (HT2s4 : T2 !!! Regidx Rs4 = npa)
      by (rewrite /T2 upd_ne; [exact HT1s4 | vm_compute; discriminate]).
    assert (HT2s5 : T2 !!! Regidx Rs5 = pme)
      by (rewrite /T2 upd_ne; [exact HT1s5 | vm_compute; discriminate]).
    assert (Hpp072 : add_vec_int (mword_of_int (KF + 0x6e) : mword 64) 4
                     = mword_of_int (KF + 0x72)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp072) in "Hpc".
    (* ---- +0x72: addi s2,s4,208 ---- *)
    iApply (wp_addi4_s_sconf (mword_of_int (KF + 0x72) : mword 64) Rs2 Rs4 (mword_of_int 208 : mword 12)
              T2 n false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi072 [-]").
    iApply wp_next_off_intro. iIntros "Hcg Hpc". iEval (rgne) in "Hcg".
    set (T3 := <[Regidx Rs2 := regval_into_reg
                  (add_vec (T2 !!! Regidx Rs4) (sign_extend' 64 (mword_of_int 208 : mword 12)))]> T2).
    assert (HT3s2 : T3 !!! Regidx Rs2 = p_ofile npa 0).
    { rewrite /T3 upd_eq HT2s4. apply p_ofile_zero. }
    assert (HT3s1 : T3 !!! Regidx Rs1 = p_ofile pme 0)
      by (rewrite /T3 upd_ne; [exact HT2s1 | vm_compute; discriminate]).
    assert (HT3s4 : T3 !!! Regidx Rs4 = npa)
      by (rewrite /T3 upd_ne; [exact HT2s4 | vm_compute; discriminate]).
    assert (HT3s5 : T3 !!! Regidx Rs5 = pme)
      by (rewrite /T3 upd_ne; [exact HT2s5 | vm_compute; discriminate]).
    assert (Hpp076 : add_vec_int (mword_of_int (KF + 0x72) : mword 64) 4
                     = mword_of_int (KF + 0x76)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp076) in "Hpc".
    (* ---- +0x76: addi s3,s5,336 ---- *)
    iApply (wp_addi4_s_sconf (mword_of_int (KF + 0x76) : mword 64) Rs3 Rs5 (mword_of_int 336 : mword 12)
              T3 n false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi076 [-]").
    iApply wp_next_off_intro. iIntros "Hcg Hpc". iEval (rgne) in "Hcg".
    set (T4 := <[Regidx Rs3 := regval_into_reg
                  (add_vec (T3 !!! Regidx Rs5) (sign_extend' 64 (mword_of_int 336 : mword 12)))]> T3).
    assert (HT4s3 : T4 !!! Regidx Rs3 = p_cwd pme).
    { rewrite /T4 upd_eq HT3s5. apply p_cwd_sext. }
    assert (HT4s1 : T4 !!! Regidx Rs1 = p_ofile pme 0)
      by (rewrite /T4 upd_ne; [exact HT3s1 | vm_compute; discriminate]).
    assert (HT4s2 : T4 !!! Regidx Rs2 = p_ofile npa 0)
      by (rewrite /T4 upd_ne; [exact HT3s2 | vm_compute; discriminate]).
    assert (HT4s4 : T4 !!! Regidx Rs4 = npa)
      by (rewrite /T4 upd_ne; [exact HT3s4 | vm_compute; discriminate]).
    assert (HT4s5 : T4 !!! Regidx Rs5 = pme)
      by (rewrite /T4 upd_ne; [exact HT3s5 | vm_compute; discriminate]).
    assert (Hpp07a : add_vec_int (mword_of_int (KF + 0x76) : mword 64) 4
                     = mword_of_int (KF + 0x7a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp07a) in "Hpc".
    (* ---- +0x7a: c.j +28 -> +0x96 ---- *)
    assert (Htgt7a : add_vec (mword_of_int (KF + 0x7a) : mword 64)
                       (sign_extend' 64 (sign_extend' 21
                          (concat_vec (mword_of_int 14 : mword 11) ('b"0"))))
                     = mword_of_int (KF + 0x96))
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_cj_s_sconf (mword_of_int (KF + 0x7a))
              (sign_extend' 21 (concat_vec (mword_of_int 14 : mword 11) ('b"0")))
              T4 n false
              ltac:(rewrite Htgt7a; vm_compute; reflexivity)
              with "Hcg Hpc Hi07a [-]").
    iApply wp_next_off_intro. iNext. iIntros "Hcg Hpc".
    iEval (rewrite Htgt7a) in "Hpc".
    (* ---- assemble the exit and hand off to Hcont ---- *)
    assert (HT4thr : forall r : mword 5, is_cs_idx r = true ->
                r <> Rs1 -> r <> Rs2 -> r <> Rs3 -> T4 !!! Regidx r = M !!! Regidx r).
    { intros r Hr N1 N2 N3.
      rewrite /T4 upd_ne; [| congruence].
      rewrite /T3 upd_ne; [| congruence].
      rewrite /T2 upd_ne; [| congruence].
      rewrite /T1 upd_ne; [| regne].
      reflexivity. }
    iSpecialize ("Hcont" $! CID0 with "[%]"); [intros _; reflexivity |].
    iApply ("Hcont" $! T4 with "[%] Hcg Hpc Hpv").
    split_and!; [exact HT4s1 | exact HT4s2 | exact HT4s3 | exact HT4s4 | exact HT4s5 | exact HT4thr].
  Qed.

End KforkB7.
