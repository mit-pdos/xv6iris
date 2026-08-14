(* ProofUvmdealloc.v -- uvmdealloc() over the SIE-agnostic sconf world.

     uint64 uvmdealloc(pagetable_t pagetable, uint64 oldsz, uint64 newsz) {
       if (newsz >= oldsz) return oldsz;
       if (PGROUNDUP(newsz) < PGROUNDUP(oldsz)) {
         int npages = (PGROUNDUP(oldsz) - PGROUNDUP(newsz)) / PGSIZE;
         uvmunmap(pagetable, PGROUNDUP(newsz), npages, 1);
       }
       return newsz;
     }

   Spec of record: SpecUvmdealloc.v -- stated at the [proc_pt] altitude over
   uvmunmap's contract.  Twenty-nine instructions, a 32-byte ra/s0/s1 frame
   byte-identical to argint's/sys_uptime's, ONE call, and THREE paths that
   join at the single epilogue (+0x26):

     - [newsz >= oldsz]        : +0x0c bgeu TAKEN, s1 = oldsz;
     - the two PGROUNDUPs tie  : +0x22 bltu FALLS,  s1 = newsz;
     - something to unmap      : +0x22 bltu TAKEN -> uvmunmap -> +0x42 c.j.

   Nothing is shrink-wrapped, so the epilogue continuation is proved ONCE, as
   the standalone [wp_uvmdealloc_epi] (own [CID0] binder -- it is invoked from
   three different call sites, each landing at whatever hart that path's own
   leaf steps reached, per the explicit-cpuid porting guide's "decomposed
   helper lemma" recipe / ProofConsputc.wp_consputc_epi), owning all four
   frame cells and taking only (the register file at +0x26, the return value
   [res], the post's disjunct at [res]) as its own extra arguments.

   THE WHOLE CONTENT IS ARITHMETIC.  +0x12..+0x20 compute
   [and_vec (add_vec x (mword_of_int 4095)) (mword_of_int (-4096))] twice,
   which is EXACTLY [ProcPtOwn.pgroundup]; +0x32/+0x34/+0x38 turn the
   difference into [mword_of_int (Z.of_nat (uvmd_np oldsz newsz))].  Per
   claude-notes/durable-notes.md all of that arithmetic is factored into
   [mword]-free top-level [Z] lemmas -- [ProcPtOwn.z_pgu_*] / [z_np_*] --
   because any goal mentioning [bv_unsigned] answers "Cannot find witness" to
   [lia] under this file's transitive [bitvector.tactics] import.  The two
   [mword] bridges it needs are [add_vec64_comm] and
   [ByteCursor.srli12_div4096]; the compressed [c.sub] leaf is
   [WpSconfAlu.wp_csub_wval_s_sconf] (the explicit-[wval] form; the
   encoding's own rd = rs1 shape is [wp_csub_s_sconf], a restatement of it).

   On the two arms that SKIP the unmap, [uvmd_np oldsz newsz = 0] (the
   quotient is 0 or negative and [Z.to_nat] clamps), so the descriptor the
   spec names is [P] with its derived [ud_data] field renormalised --
   [ProcPtOwn.proc_pt_data_irrel] transports [proc_pt] across that. *)
Set Printing Depth 40.
From Stdlib Require Import Eqdep_dec ZArith Lia List.
From stdpp Require Import gmap list list_monad bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import excl.
From iris.base_logic.lib Require Import gen_heap invariants ghost_var ghost_map.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.Base SailStdpp.Operators_mwords SailStdpp.Values SailStdpp.MachineWord.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import RiscvPtsto RiscvLang RiscvExtras.
Require Import SmodeCore.
Require Import InstrBytes KernelText.
Require Import WpMmodeLeafBase.
Require Import RegFile.
Require Import CalleeSaved StackOwn.
Require Import IntrDefs WpSmodeIntr.
Require Import HartTp WpNext.
Require Import WpLock.
Require Import KallocInv.
Require Import UserPtTree.
Require Import CpuOwn.
Require Import ByteCursor.
Require Import ProcPtOwn.
Require Import CodeUvmdealloc.
Require Import WpSconfAlu WpSconfMem WpSconfBtype WpSconfCtl.
Require Import SpecUvmunmap.
Require Import SpecUvmdealloc.
Require Import KernelRvcDecode.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* THE WHOLE FUNCTION.                                                    *)
(* ===================================================================== *)

Module UvmdeallocProof (Uvmunmap : UVMUNMAP) : UVMDEALLOC.

Section ProofUvmdealloc.
  Context `{!riscvGS Σ, !lockG Σ, !sieG Σ, !kallocG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Notation Rra := (mword_of_int 1 : mword 5).
  Notation Rtp := (mword_of_int 4 : mword 5).
  Notation Rs0 := (mword_of_int 8 : mword 5).
  Notation Rs1 := (mword_of_int 9 : mword 5).
  Notation Ra0 := (mword_of_int 10 : mword 5).
  Notation Ra1 := (mword_of_int 11 : mword 5).
  Notation Ra2 := (mword_of_int 12 : mword 5).
  Notation Ra3 := (mword_of_int 13 : mword 5).
  Notation Ra4 := (mword_of_int 14 : mword 5).
  Notation Ra5 := (mword_of_int 15 : mword 5).

  Ltac reg_neq :=
    lazymatch goal with
    | |- ?a <> ?b => tryif unify a b then fail else (vm_compute; discriminate)
    end.

  Lemma udl_cr5 : creg2reg_idx (Cregidx (mword_of_int 5)) = Regidx Ra3.
  Proof. vm_compute. reflexivity. Qed.
  Lemma udl_cr6 : creg2reg_idx (Cregidx (mword_of_int 6)) = Regidx Ra4.
  Proof. vm_compute. reflexivity. Qed.
  Lemma udl_cr7 : creg2reg_idx (Cregidx (mword_of_int 7)) = Regidx Ra5.
  Proof. vm_compute. reflexivity. Qed.

  (* [CID0] is its OWN binder here (shadowing the section's fixed [Context
     CID]): this epilogue gets applied at whichever hart the THREE call
     sites below actually reach (the bgeu-taken early-out, the bltu-fall
     tie, or the post-uvmunmap-and-cj join), never necessarily the section's
     own entry hart -- same reasoning as ProofConsputc.v's
     [wp_consputc_epi]. *)
  Lemma wp_uvmdealloc_epi `{CID0 : CpuId}
      (mm mj : regfile) (P : uptd) (K : nat) (eb : bool) (p : mword 64)
      (C : iProp Σ) (b : bool) (oldsz newsz res ret_tgt : mword 64) (lks : gset string) :
    (4 <= K)%nat ->
    (b = false \/ p = zero_reg -> (CID0 : CPU) = (CID : CPU)) ->
    ret_tgt = ret_pc (mm !!! Regidx Rra) ->
    mj !!! Regidx csp_rs1
      = add_vec (mm !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))) ->
    mj !!! Regidx Rs1 = res ->
    (forall c : mword 5, is_cs_idx c = true ->
        c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> mj !!! Regidx c = mm !!! Regidx c) ->
    ( ((uint newsz >= uint oldsz)%Z /\ res = oldsz)
      \/ ((uint newsz < uint oldsz)%Z /\ res = newsz) ) ->
    sie_cap_gpr mj (K - 4)%nat b p -∗
    cpu_own 0%nat eb p C b lks -∗
    kernel_text -∗
    pc_is (mword_of_int (KernelSyms.uvmdealloc + 0x26) : mword 64) -∗
    (* the three saved cells arrive SPD-relative (the same address shape the
       sdsp stores in the caller used, one [add_vec] deep off [mm]'s csp,
       never folded back to [pa_stk] form) -- EPI re-derives [pa_stk sp0 k]
       facts for its OWN internal use (the final pop), but its INPUT shape
       must match exactly what the three call sites actually hold. *)
    add_vec (add_vec (mm !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))))
      (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000"))) ↦₈ (mm !!! Regidx Rra) -∗
    add_vec (add_vec (mm !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))))
      (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000"))) ↦₈ (mm !!! Regidx Rs0) -∗
    add_vec (add_vec (mm !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))))
      (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) ↦₈ (mm !!! Regidx Rs1) -∗
    (∃ v, pa_stk (mm !!! Regidx csp_rs1) 4 ↦₈ v) -∗
    proc_pt (uptd_del_run P (svpn_of (pgroundup newsz)) (uvmd_np oldsz newsz)) -∗
    (* [wp_next]'s OWN implicit "entry hart" argument must be pinned to the
       WHOLE FUNCTION's entry hart [CID] (the section's own, ambient here
       too) explicitly -- left bare, it would silently resolve to EPI's OWN
       [CID0] (the hart EPI happens to be invoked at), which is the WRONG
       hart: this obligation is handed straight to the caller's own [Hcont],
       whose [wp_next] is relative to the function's TRUE entry, not to
       wherever this particular call site's leaf chain landed. *)
    wp_next (CID0 := CID) b p (fun (CID : CpuId) =>
      ∀ (mr : regfile),
      sie_cap_gpr mr K b p -∗
      cpu_own 0%nat eb p C b lks -∗
      pc_is ret_tgt -∗
      ⌜callee_saved mm mr⌝ -∗
      ⌜ ((uint newsz >= uint oldsz)%Z /\ mr !!! Regidx Ra0 = oldsz)
        \/ ((uint newsz < uint oldsz)%Z /\ mr !!! Regidx Ra0 = newsz) ⌝ -∗
      proc_pt (uptd_del_run P (svpn_of (pgroundup newsz)) (uvmd_np oldsz newsz)) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HK4 Hcross Hrettgt Hjsp Hjs1 Hjthr Hpay.
    pose (sp0 := (mm !!! Regidx csp_rs1 : mword 64)).
    set (spd := add_vec sp0 (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6)))).
    iIntros "Hcg Hcpu #Htext Hpc Hr24 Hr16 Hr8 Hgape Hpt Hcont".
    iDestruct "Hgape" as (vgap) "Hgap".
    iPoseProof (udi_26 with "Htext") as "Hi26".
    iPoseProof (udi_28 with "Htext") as "Hi28".
    iPoseProof (udi_2a with "Htext") as "Hi2a".
    iPoseProof (udi_2c with "Htext") as "Hi2c".
    iPoseProof (udi_2e with "Htext") as "Hi2e".
    iPoseProof (udi_30 with "Htext") as "Hi30".
    assert (Hspd4 : pa_stk sp0 4 = spd).
    { rewrite /spd. unfold pa_stk, add_vec_int. apply f_equal.
      apply bv_eq; vm_compute; reflexivity. }
    assert (Hb1 : pa_stk sp0 1
                  = add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000")))).
    { rewrite /spd. unfold sp0, pa_stk, add_vec_int. rewrite pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb2 : pa_stk sp0 2
                  = add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000")))).
    { rewrite /spd. unfold sp0, pa_stk, add_vec_int. rewrite pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb3 : pa_stk sp0 3
                  = add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000")))).
    { rewrite /spd. unfold sp0, pa_stk, add_vec_int. rewrite pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    (* +0x26 c.mv a0,s1 *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.uvmdealloc + 0x26)) Ra0 Rs1 mj (K - 4)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi26").
    iIntros (CID1 Hs1) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    iEval (rewrite Hjs1 add_vec_zero_l) in "Hcg".
    set (E0 := <[Regidx Ra0 := regval_into_reg res]> mj).
    change (<[Regidx Ra0 := regval_into_reg res]> mj) with E0.
    assert (HE0sp : E0 !!! Regidx csp_rs1 = spd)
      by (rewrite /E0 upd_ne; [exact Hjsp | reg_neq]).
    assert (Hpc28 : add_vec_int (mword_of_int (KernelSyms.uvmdealloc + 0x26) : mword 64) 2
                    = mword_of_int (KernelSyms.uvmdealloc + 0x28))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc28) in "Hpc".
    (* +0x28 c.ldsp ra,24(sp) *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.uvmdealloc + 0x28)) (mword_of_int 3 : mword 6) Rra
              E0 (K - 4)%nat (mm !!! Regidx Rra) b (dqm := DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi28 [Hr24]").
    { iEval (rewrite HE0sp). iExact "Hr24". }
    iIntros (CID2 Hs2) "Hcg Hpc Hr24". iEval (rewrite HE0sp) in "Hr24".
    set (E1 := <[Regidx Rra := regval_into_reg (mm !!! Regidx Rra)]> E0).
    change (<[Regidx Rra := regval_into_reg (mm !!! Regidx Rra)]> E0) with E1.
    assert (HE1sp : E1 !!! Regidx csp_rs1 = spd)
      by (rewrite /E1 upd_ne; [exact HE0sp | reg_neq]).
    assert (Hpc2a : add_vec_int (mword_of_int (KernelSyms.uvmdealloc + 0x28) : mword 64) 2
                    = mword_of_int (KernelSyms.uvmdealloc + 0x2a))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc2a) in "Hpc".
    (* +0x2a c.ldsp s0,16(sp) *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.uvmdealloc + 0x2a)) (mword_of_int 2 : mword 6) Rs0
              E1 (K - 4)%nat (mm !!! Regidx Rs0) b (dqm := DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi2a [Hr16]").
    { iEval (rewrite HE1sp). iExact "Hr16". }
    iIntros (CID3 Hs3) "Hcg Hpc Hr16". iEval (rewrite HE1sp) in "Hr16".
    set (E2 := <[Regidx Rs0 := regval_into_reg (mm !!! Regidx Rs0)]> E1).
    change (<[Regidx Rs0 := regval_into_reg (mm !!! Regidx Rs0)]> E1) with E2.
    assert (HE2sp : E2 !!! Regidx csp_rs1 = spd)
      by (rewrite /E2 upd_ne; [exact HE1sp | reg_neq]).
    assert (Hpc2c : add_vec_int (mword_of_int (KernelSyms.uvmdealloc + 0x2a) : mword 64) 2
                    = mword_of_int (KernelSyms.uvmdealloc + 0x2c))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc2c) in "Hpc".
    (* +0x2c c.ldsp s1,8(sp) *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.uvmdealloc + 0x2c)) (mword_of_int 1 : mword 6) Rs1
              E2 (K - 4)%nat (mm !!! Regidx Rs1) b (dqm := DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi2c [Hr8]").
    { iEval (rewrite HE2sp). iExact "Hr8". }
    iIntros (CID4 Hs4) "Hcg Hpc Hr8". iEval (rewrite HE2sp) in "Hr8".
    set (E3 := <[Regidx Rs1 := regval_into_reg (mm !!! Regidx Rs1)]> E2).
    change (<[Regidx Rs1 := regval_into_reg (mm !!! Regidx Rs1)]> E2) with E3.
    assert (HE3sp : E3 !!! Regidx csp_rs1 = spd)
      by (rewrite /E3 upd_ne; [exact HE2sp | reg_neq]).
    assert (Hpc2e : add_vec_int (mword_of_int (KernelSyms.uvmdealloc + 0x2c) : mword 64) 2
                    = mword_of_int (KernelSyms.uvmdealloc + 0x2e))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc2e) in "Hpc".
    (* +0x2e c.addi16sp sp,32 -- the frame pop *)
    set (E4 := <[Regidx csp_rs1 := regval_into_reg
        (add_vec (E3 !!! Regidx csp_rs1)
           (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))))]> E3).
    assert (Hsp0up : add_vec spd (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))) = sp0).
    { rewrite /spd /sp0 po_addv_assoc.
      assert (HAB : add_vec (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6)))
                      (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6)))
                    = mword_of_int 0)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite HAB. apply avi0. }
    assert (Hwv : add_vec (E3 !!! Regidx csp_rs1)
                    (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))) = sp0)
      by (rewrite HE3sp; exact Hsp0up).
    assert (Hpop : E3 !!! Regidx csp_rs1
                   = pa_stk (add_vec (E3 !!! Regidx csp_rs1)
                               (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6)))) 4).
    { rewrite Hwv HE3sp. symmetry. exact Hspd4. }
    iAssert (stack_own sp0 4) with "[Hr24 Hr16 Hr8 Hgap]" as "Hframe4".
    { rewrite stack_own_slots. cbn [seq].
      iSplitL "Hr24". { iExists _. iEval (rewrite Hb1). iExact "Hr24". }
      iSplitL "Hr16". { iExists _. iEval (rewrite Hb2). iExact "Hr16". }
      iSplitL "Hr8".  { iExists _. iEval (rewrite Hb3). iExact "Hr8". }
      iSplitL "Hgap". { iExists _. iExact "Hgap". }
      done. }
    iEval (rewrite -Hwv) in "Hframe4".
    iApply (wp_caddi16sp_pop_s_sconf (mword_of_int (KernelSyms.uvmdealloc + 0x2e))
              (mword_of_int 2 : mword 6) E3 (K - 4)%nat 4 b Hpop
              with "Hcg Hpc Hi2e Hframe4").
    iIntros (CID5 Hs5) "Hcg Hpc".
    change (<[Regidx csp_rs1 := regval_into_reg
        (add_vec (E3 !!! Regidx csp_rs1)
           (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))))]> E3) with E4.
    assert (Hnk : ((K - 4) + 4)%nat = K) by lia.
    iEval (rewrite Hnk) in "Hcg".
    assert (Hpc30 : add_vec_int (mword_of_int (KernelSyms.uvmdealloc + 0x2e) : mword 64) 2
                    = mword_of_int (KernelSyms.uvmdealloc + 0x30))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc30) in "Hpc".
    (* +0x30 c.ret *)
    assert (HE4ra : E4 !!! Regidx Rra = mm !!! Regidx Rra).
    { rewrite /E4 upd_ne; [| reg_neq]. rewrite /E3 upd_ne; [| reg_neq].
      rewrite /E2 upd_ne; [| reg_neq]. rewrite /E1 upd_eq. reflexivity. }
    assert (HE4a0 : E4 !!! Regidx Ra0 = res).
    { rewrite /E4 upd_ne; [| reg_neq]. rewrite /E3 upd_ne; [| reg_neq].
      rewrite /E2 upd_ne; [| reg_neq]. rewrite /E1 upd_ne; [| reg_neq].
      rewrite /E0 upd_eq. reflexivity. }
    assert (HE4sp : E4 !!! Regidx csp_rs1 = mm !!! Regidx csp_rs1)
      by (rewrite /E4 upd_eq; exact Hwv).
    assert (HE4s0 : E4 !!! Regidx Rs0 = mm !!! Regidx Rs0).
    { rewrite /E4 upd_ne; [| reg_neq]. rewrite /E3 upd_ne; [| reg_neq].
      rewrite /E2 upd_eq. reflexivity. }
    assert (HE4s1 : E4 !!! Regidx Rs1 = mm !!! Regidx Rs1).
    { rewrite /E4 upd_ne; [| reg_neq]. rewrite /E3 upd_eq. reflexivity. }
    assert (HE4thr : forall c : mword 5, is_cs_idx c = true ->
              c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 ->
              E4 !!! Regidx c = mm !!! Regidx c).
    { intros c Hc H2 H8 H9.
      rewrite /E4 upd_ne;
        [| intros Hx; injection Hx as Hx2; subst c; apply H2; reflexivity].
      rewrite /E3 upd_ne;
        [| intros Hx; injection Hx as Hx2; subst c; apply H9; reflexivity].
      rewrite /E2 upd_ne;
        [| intros Hx; injection Hx as Hx2; subst c; apply H8; reflexivity].
      rewrite /E1 upd_ne;
        [| intros Hx; injection Hx as Hx2; subst c; vm_compute in Hc; discriminate].
      rewrite /E0 upd_ne;
        [| intros Hx; injection Hx as Hx2; subst c; vm_compute in Hc; discriminate].
      apply Hjthr; assumption. }
    iApply (wp_cret_s_sconf (mword_of_int (KernelSyms.uvmdealloc + 0x30)) Rra E4 K b
              ltac:(vm_compute; discriminate) with "Hcg Hpc Hi30").
    iIntros (CID6 Hs6) "Hcg Hpc".
    iEval (rgne) in "Hpc".
    assert (Hretf : ret_pc (E4 !!! Regidx Rra) = ret_tgt) by (rewrite HE4ra Hrettgt; reflexivity).
    iEval (rewrite Hretf) in "Hpc".
    iDestruct (cpu_own_transport CID0 CID6 0%nat eb p C b ltac:(wp_next_chain)
                 with "Hcpu") as "Hcpu".
    iSpecialize ("Hcont" $! CID6 with "[]"); [ iPureIntro; wp_next_chain | ].
    iApply ("Hcont" $! E4 with "Hcg Hcpu Hpc [%] [%] Hpt").
    { unfold callee_saved. split_and!;
        first [ exact HE4sp | exact HE4s0 | exact HE4s1
              | apply HE4thr; vm_compute; first [reflexivity | discriminate] ]. }
    { rewrite HE4a0. exact Hpay. }
  Qed.

  Lemma wp_uvmdealloc_sconf
      (γa : gname) (mm : regfile)
      (P : uptd) (K : nat) (eb : bool) (p : mword 64) (C : iProp Σ) (b : bool) (lks : gset string)
    : wp_uvmdealloc_sconf_body γa mm P K eb p C b lks.
  Proof.
    cbv beta delta [wp_uvmdealloc_sconf_body].
    intros pcE oldsz newsz ret_tgt HK Hroot Hob Hlkbelow.
    pose (sp0 := (mm !!! Regidx csp_rs1 : mword 64)).
    set (spd := add_vec sp0 (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6)))).
    iIntros "Hcg Hcpu #Htext Hpc Hpt Henv Hcont".

    (* ================================================================= *)
    (* §A  The pure PGROUNDUP arithmetic, once and for all.               *)
    (* ================================================================= *)
    assert (Hmax : uvm_maxsz = 274877898752) by (vm_compute; reflexivity).
    assert (Hobz : bv_unsigned oldsz <= 274877898752)
      by (rewrite -uint_unsigned -Hmax; exact Hob).
    assert (Hpuz : bv_unsigned (pgroundup oldsz)
                   = (bv_unsigned oldsz + 4095) - (bv_unsigned oldsz + 4095) mod 4096)
      by (apply pgroundup_unsigned; apply z_maxsz_no_wrap; exact Hobz).
    assert (Hpumod : bv_unsigned (pgroundup oldsz) mod 4096 = 0)
      by (rewrite Hpuz; apply z_pgd_mod).
    assert (Hpubnd : bv_unsigned (pgroundup oldsz) <= 274877898752).
    { rewrite Hpuz. apply z_pgu_maxsz.
      split; [exact (proj1 (bv_unsigned_in_range _ oldsz)) | exact Hobz]. }
    (* NOTHING about [newsz] is known yet, and nothing can be: the contract
       says nothing, and on the arm the C skips [newsz] may be so large that
       PGROUNDUP wraps.  The [newsz] arithmetic is therefore established
       inside the [newsz < oldsz] branch, where the bound is inherited from
       [oldsz]; on the other arm [uvmd_np]'s guard is what closes the run. *)

    (* ================================================================= *)
    (* §B  PROLOGUE: the 32-byte ra/s0/s1 frame.                          *)
    (* ================================================================= *)
    iPoseProof (udi_00 with "Htext") as "Hi00".
    iPoseProof (udi_02 with "Htext") as "Hi02".
    iPoseProof (udi_04 with "Htext") as "Hi04".
    iPoseProof (udi_06 with "Htext") as "Hi06".
    iPoseProof (udi_08 with "Htext") as "Hi08".
    iPoseProof (udi_0a with "Htext") as "Hi0a".
    iPoseProof (udi_0c with "Htext") as "Hi0c".
    assert (Hspm : mm !!! Regidx csp_rs1 = sp0) by reflexivity.
    assert (Hspd4 : pa_stk sp0 4 = spd).
    { rewrite /spd. unfold pa_stk, add_vec_int. apply f_equal.
      apply bv_eq; vm_compute; reflexivity. }
    assert (Hpush : add_vec (mm !!! Regidx csp_rs1)
                      (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6)))
                    = pa_stk (mm !!! Regidx csp_rs1) 4).
    { unfold pa_stk, add_vec_int. apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    iApply (wp_caddi_sp_push_s_sconf pcE (mword_of_int 32 : mword 6) mm K 4 b
              ltac:(lia) Hpush with "Hcg Hpc Hi00").
    iIntros (CID1 Hs1) "Hcg Hframe Hpc".
    iEval (rewrite Hspm) in "Hframe".
    set (A0 := <[Regidx csp_rs1 := regval_into_reg
        (add_vec (mm !!! Regidx csp_rs1)
           (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))))]> mm).
    change (<[Regidx csp_rs1 := regval_into_reg
        (add_vec (mm !!! Regidx csp_rs1)
           (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))))]> mm) with A0.
    assert (HA0sp : A0 !!! Regidx csp_rs1 = spd) by (rewrite /A0 upd_eq; reflexivity).
    iEval (rewrite stack_own_slots; cbn [seq]) in "Hframe".
    iDestruct "Hframe" as "(S1c & S2c & S3c & S4c & _)".
    iDestruct "S1c" as (vr24) "Hr24".
    iDestruct "S2c" as (vr16) "Hr16".
    iDestruct "S3c" as (vr8) "Hr8".
    iDestruct "S4c" as (vgap) "Hgap".
    assert (Hb1 : pa_stk sp0 1
                  = add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000")))).
    { rewrite /spd. unfold sp0, pa_stk, add_vec_int. rewrite pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb2 : pa_stk sp0 2
                  = add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000")))).
    { rewrite /spd. unfold sp0, pa_stk, add_vec_int. rewrite pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb3 : pa_stk sp0 3
                  = add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000")))).
    { rewrite /spd. unfold sp0, pa_stk, add_vec_int. rewrite pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hpc02 : add_vec_int (pcE : mword 64) 2 = mword_of_int (KernelSyms.uvmdealloc + 0x02))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc02) in "Hpc".
    (* +0x02 c.sdsp ra,24(sp) *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.uvmdealloc + 0x02)) (mword_of_int 3 : mword 6) Rra
              A0 (K - 4)%nat vr24 b with "Hcg Hpc Hi02 [Hr24]").
    { iEval (rewrite HA0sp -Hb1). iExact "Hr24". }
    iIntros (CID2 Hs2) "Hcg Hpc Hr24".
    assert (Hpc04 : add_vec_int (mword_of_int (KernelSyms.uvmdealloc + 0x02) : mword 64) 2 = mword_of_int (KernelSyms.uvmdealloc + 0x04))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc04) in "Hpc".
    (* +0x04 c.sdsp s0,16(sp) *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.uvmdealloc + 0x04)) (mword_of_int 2 : mword 6) Rs0
              A0 (K - 4)%nat vr16 b with "Hcg Hpc Hi04 [Hr16]").
    { iEval (rewrite HA0sp -Hb2). iExact "Hr16". }
    iIntros (CID3 Hs3) "Hcg Hpc Hr16".
    assert (Hpc06 : add_vec_int (mword_of_int (KernelSyms.uvmdealloc + 0x04) : mword 64) 2 = mword_of_int (KernelSyms.uvmdealloc + 0x06))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc06) in "Hpc".
    (* +0x06 c.sdsp s1,8(sp) *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.uvmdealloc + 0x06)) (mword_of_int 1 : mword 6) Rs1
              A0 (K - 4)%nat vr8 b with "Hcg Hpc Hi06 [Hr8]").
    { iEval (rewrite HA0sp -Hb3). iExact "Hr8". }
    iIntros (CID4 Hs4) "Hcg Hpc Hr8".
    assert (Hpc08 : add_vec_int (mword_of_int (KernelSyms.uvmdealloc + 0x06) : mword 64) 2 = mword_of_int (KernelSyms.uvmdealloc + 0x08))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc08) in "Hpc".
    (* normalize the three saved cells to the epilogue's reload shape --
       each cell's stored value is the leaf's [rget A0 rs2], let-bound
       outside its own [wp_next] (read at the CALLER's ambient hart: CID1 for
       Hr24, CID2 for Hr16, CID3 for Hr8).  [rgne] peels each to the
       CID-free [!!!] form before the plain map-chain facts rewrite. *)
    assert (HA0ra : A0 !!! Regidx Rra = mm !!! Regidx Rra)
      by (rewrite /A0 upd_ne; [reflexivity | reg_neq]).
    assert (HA0s0 : A0 !!! Regidx Rs0 = mm !!! Regidx Rs0)
      by (rewrite /A0 upd_ne; [reflexivity | reg_neq]).
    assert (HA0s1 : A0 !!! Regidx Rs1 = mm !!! Regidx Rs1)
      by (rewrite /A0 upd_ne; [reflexivity | reg_neq]).
    iEval (rgne) in "Hr24". iEval (rewrite HA0sp HA0ra) in "Hr24".
    iEval (rgne) in "Hr16". iEval (rewrite HA0sp HA0s0) in "Hr16".
    iEval (rgne) in "Hr8". iEval (rewrite HA0sp HA0s1) in "Hr8".
    (* +0x08 c.addi4spn s0,sp,32 *)
    iApply (wp_caddi4spn_s_sconf (mword_of_int (KernelSyms.uvmdealloc + 0x08)) (Cregidx (mword_of_int 0))
              (mword_of_int 8 : mword 8) Rs0 A0 (K - 4)%nat b
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
              ltac:(rdok)
              with "Hcg Hpc Hi08").
    iIntros (CID5 Hs5) "Hcg Hpc".
    set (A1 := <[Regidx Rs0 := regval_into_reg
        (add_vec (A0 !!! Regidx csp_rs1)
           (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8))))]> A0).
    change (<[Regidx Rs0 := regval_into_reg
        (add_vec (A0 !!! Regidx csp_rs1)
           (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8))))]> A0) with A1.
    assert (Hpc0a : add_vec_int (mword_of_int (KernelSyms.uvmdealloc + 0x08) : mword 64) 2 = mword_of_int (KernelSyms.uvmdealloc + 0x0a))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc0a) in "Hpc".
    assert (HA1a1 : A1 !!! Regidx Ra1 = oldsz).
    { rewrite /A1 upd_ne; [| reg_neq]. rewrite /A0 upd_ne; [| reg_neq]. reflexivity. }
    (* +0x0a c.mv s1,a1 : s1 := oldsz *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.uvmdealloc + 0x0a)) Rs1 Ra1 A1 (K - 4)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi0a").
    iIntros (CID6 Hs6) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    iEval (rewrite HA1a1 add_vec_zero_l) in "Hcg".
    set (A2 := <[Regidx Rs1 := regval_into_reg oldsz]> A1).
    change (<[Regidx Rs1 := regval_into_reg oldsz]> A1) with A2.
    assert (Hpc0c : add_vec_int (mword_of_int (KernelSyms.uvmdealloc + 0x0a) : mword 64) 2 = mword_of_int (KernelSyms.uvmdealloc + 0x0c))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc0c) in "Hpc".
    (* the register facts at the first branch *)
    assert (HA2sp : A2 !!! Regidx csp_rs1 = spd).
    { rewrite /A2 upd_ne; [| reg_neq]. rewrite /A1 upd_ne; [| reg_neq]. exact HA0sp. }
    assert (HA2s1 : A2 !!! Regidx Rs1 = oldsz) by (rewrite /A2 upd_eq; reflexivity).
    assert (HA2a1 : A2 !!! Regidx Ra1 = oldsz)
      by (rewrite /A2 upd_ne; [exact HA1a1 | reg_neq]).
    assert (HA2a2 : A2 !!! Regidx Ra2 = newsz).
    { rewrite /A2 upd_ne; [| reg_neq]. rewrite /A1 upd_ne; [| reg_neq].
      rewrite /A0 upd_ne; [| reg_neq]. reflexivity. }
    assert (HA2a0 : A2 !!! Regidx Ra0 = page_base (ud_root P)).
    { rewrite /A2 upd_ne; [| reg_neq]. rewrite /A1 upd_ne; [| reg_neq].
      rewrite /A0 upd_ne; [| reg_neq]. exact Hroot. }
    assert (HA2thr : forall c : mword 5, is_cs_idx c = true ->
              c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 ->
              A2 !!! Regidx c = mm !!! Regidx c).
    { intros c Hc H2 H8 H9.
      rewrite /A2 upd_ne;
        [| intros Hx; injection Hx as Hx2; subst c; apply H9; reflexivity].
      rewrite /A1 upd_ne;
        [| intros Hx; injection Hx as Hx2; subst c; apply H8; reflexivity].
      rewrite /A0 upd_ne;
        [| intros Hx; injection Hx as Hx2; subst c; apply H2; reflexivity].
      reflexivity. }

    (* ================================================================= *)
    (* §D  +0x0c bgeu a2,a1 : the [newsz >= oldsz] early-out.             *)
    (* ================================================================= *)
    destruct (zopz0zKzJ_u newsz oldsz) eqn:Hcmp1.
    { (* ---- TAKEN: nothing to do, s1 already holds oldsz ---- *)
      assert (Hge : uint oldsz <= uint newsz).
      { unfold zopz0zKzJ_u in Hcmp1. rewrite Z.geb_leb in Hcmp1.
        exact (proj1 (Z.leb_le _ _) Hcmp1). }
      assert (Hcmp1' : zopz0zKzJ_u (rget A2 Ra2) (rget A2 Ra1) = true).
      { rgne. rgne. rewrite HA2a2 HA2a1. exact Hcmp1. }
      (* the run is empty -- straight off [uvmd_np]'s guard, with no
         PGROUNDUP arithmetic, which is the point of guarding it *)
      assert (Hnp0 : uvmd_np oldsz newsz = 0%nat)
        by (apply uvmd_np_ge; rewrite -!uint_unsigned; exact Hge).
      iAssert (proc_pt (uptd_del_run P (svpn_of (pgroundup newsz)) (uvmd_np oldsz newsz)))
        with "[Hpt]" as "Hpt".
      { iEval (rewrite (proc_pt_data_irrel P
                 (uptd_del_run P (svpn_of (pgroundup newsz)) (uvmd_np oldsz newsz))
                 ltac:(rewrite Hnp0; reflexivity)
                 ltac:(rewrite Hnp0; reflexivity)
                 ltac:(rewrite Hnp0; reflexivity))) in "Hpt".
        iExact "Hpt". }
      iApply (wp_bgeu_taken_s_sconf (mword_of_int (KernelSyms.uvmdealloc + 0x0c))
                (mword_of_int 26 : mword 13) Ra1 Ra2 A2 (K - 4)%nat b
                ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                Hcmp1' ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi0c").
      iNext. iIntros (CID7a Hs7a) "Hcg Hpc".
      assert (Htgt26 : add_vec (mword_of_int (KernelSyms.uvmdealloc + 0x0c) : mword 64)
                         (sign_extend' 64 (mword_of_int 26 : mword 13))
                       = mword_of_int (KernelSyms.uvmdealloc + 0x26))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Htgt26) in "Hpc".
      iDestruct (cpu_own_transport CID CID7a 0%nat eb p C b ltac:(wp_next_chain)
                   with "Hcpu") as "Hcpu".
      iApply (wp_uvmdealloc_epi mm A2 P K eb p C b oldsz newsz oldsz ret_tgt lks
                ltac:(lia) ltac:(wp_next_chain) eq_refl HA2sp HA2s1 HA2thr
                ltac:(left; split; [apply Z.le_ge; exact Hge | reflexivity])
                with "Hcg Hcpu Htext Hpc Hr24 Hr16 Hr8 [Hgap] Hpt Hcont").
      { iExists _. iExact "Hgap". } }

    (* ---- FALLS: newsz < oldsz ---- *)
    assert (Hlt : uint newsz < uint oldsz).
    { unfold zopz0zKzJ_u in Hcmp1. rewrite Z.geb_leb in Hcmp1.
      exact (proj1 (Z.leb_gt _ _) Hcmp1). }
    (* ...so [newsz] inherits [oldsz]'s range, and its PGROUNDUP arithmetic
       is available from here down *)
    assert (Hnbz : bv_unsigned newsz <= 274877898752)
      by (rewrite !uint_unsigned in Hlt; clear -Hlt Hobz; lia).
    assert (Hpnz : bv_unsigned (pgroundup newsz)
                   = (bv_unsigned newsz + 4095) - (bv_unsigned newsz + 4095) mod 4096)
      by (apply pgroundup_unsigned; apply z_maxsz_no_wrap; exact Hnbz).
    assert (Hpnmod : bv_unsigned (pgroundup newsz) mod 4096 = 0)
      by (rewrite Hpnz; apply z_pgd_mod).
    assert (Hpn0 : 0 <= bv_unsigned (pgroundup newsz))
      by exact (proj1 (bv_unsigned_in_range _ (pgroundup newsz))).
    assert (Hnpdef : uvmd_np oldsz newsz
                     = Z.to_nat ((bv_unsigned (pgroundup oldsz)
                                  - bv_unsigned (pgroundup newsz)) / 4096)).
    { apply uvmd_np_lt. rewrite -!uint_unsigned. exact Hlt. }
    assert (Hcmp1' : zopz0zKzJ_u (rget A2 Ra2) (rget A2 Ra1) = false).
    { rgne. rgne. rewrite HA2a2 HA2a1. exact Hcmp1. }
    iApply (wp_bgeu_fall_s_sconf (mword_of_int (KernelSyms.uvmdealloc + 0x0c))
              (mword_of_int 26 : mword 13) Ra1 Ra2 A2 (K - 4)%nat b
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) Hcmp1'
              with "Hcg Hpc Hi0c").
    iIntros (CID7 Hs7) "Hcg Hpc".
    assert (Hpc10 : add_vec_int (mword_of_int (KernelSyms.uvmdealloc + 0x0c) : mword 64) 4
                    = mword_of_int (KernelSyms.uvmdealloc + 0x10))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc10) in "Hpc".

    (* ================================================================= *)
    (* §E  +0x10..+0x20: s1 := newsz, and the two PGROUNDUPs.             *)
    (* ================================================================= *)
    iPoseProof (udi_10 with "Htext") as "Hi10".
    iPoseProof (udi_12 with "Htext") as "Hi12".
    iPoseProof (udi_14 with "Htext") as "Hi14".
    iPoseProof (udi_16 with "Htext") as "Hi16".
    iPoseProof (udi_1a with "Htext") as "Hi1a".
    iPoseProof (udi_1c with "Htext") as "Hi1c".
    iPoseProof (udi_1e with "Htext") as "Hi1e".
    iPoseProof (udi_20 with "Htext") as "Hi20".
    iPoseProof (udi_22 with "Htext") as "Hi22".
    (* +0x10 c.mv s1,a2 : s1 := newsz *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.uvmdealloc + 0x10)) Rs1 Ra2 A2 (K - 4)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi10").
    iIntros (CID8 Hs8) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    iEval (rewrite HA2a2 add_vec_zero_l) in "Hcg".
    set (A3 := <[Regidx Rs1 := regval_into_reg newsz]> A2).
    change (<[Regidx Rs1 := regval_into_reg newsz]> A2) with A3.
    assert (Hpc12 : add_vec_int (mword_of_int (KernelSyms.uvmdealloc + 0x10) : mword 64) 2
                    = mword_of_int (KernelSyms.uvmdealloc + 0x12))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc12) in "Hpc".
    assert (HA3sp : A3 !!! Regidx csp_rs1 = spd)
      by (rewrite /A3 upd_ne; [exact HA2sp | reg_neq]).
    assert (HA3s1 : A3 !!! Regidx Rs1 = newsz) by (rewrite /A3 upd_eq; reflexivity).
    assert (HA3a1 : A3 !!! Regidx Ra1 = oldsz)
      by (rewrite /A3 upd_ne; [exact HA2a1 | reg_neq]).
    assert (HA3a2 : A3 !!! Regidx Ra2 = newsz)
      by (rewrite /A3 upd_ne; [exact HA2a2 | reg_neq]).
    assert (HA3a0 : A3 !!! Regidx Ra0 = page_base (ud_root P))
      by (rewrite /A3 upd_ne; [exact HA2a0 | reg_neq]).
    assert (HA3thr : forall c : mword 5, is_cs_idx c = true ->
              c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 ->
              A3 !!! Regidx c = mm !!! Regidx c).
    { intros c Hc H2 H8 H9.
      rewrite /A3 upd_ne;
        [| intros Hx; injection Hx as Hx2; subst c; apply H9; reflexivity].
      apply HA2thr; assumption. }
    (* +0x12 c.lui a5,0x1 : a5 := 4096 *)
    iApply (wp_clui_s_sconf (mword_of_int (KernelSyms.uvmdealloc + 0x12)) Ra5
              (sign_extend' 20 (mword_of_int 1 : mword 6)) (mword_of_int 4096 : mword 64)
              A3 (K - 4)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok) lui_4096
              with "Hcg Hpc Hi12").
    iIntros (CID9 Hs9) "Hcg Hpc".
    set (A4 := <[Regidx Ra5 := regval_into_reg (mword_of_int 4096 : mword 64)]> A3).
    change (<[Regidx Ra5 := regval_into_reg (mword_of_int 4096 : mword 64)]> A3) with A4.
    assert (Hpc14 : add_vec_int (mword_of_int (KernelSyms.uvmdealloc + 0x12) : mword 64) 2
                    = mword_of_int (KernelSyms.uvmdealloc + 0x14))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc14) in "Hpc".
    assert (HA4a5 : A4 !!! Regidx Ra5 = (mword_of_int 4096 : mword 64))
      by (rewrite /A4 upd_eq; reflexivity).
    (* +0x14 c.addi a5,a5,-1 : a5 := 4095 *)
    iApply (wp_caddi_s_sconf (mword_of_int (KernelSyms.uvmdealloc + 0x14)) Ra5 (mword_of_int 63 : mword 6)
              A4 (K - 4)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi14").
    iIntros (CID10 Hs10) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    assert (H4095 : add_vec (A4 !!! Regidx Ra5)
                      (sign_extend' 64 (sign_extend' 12 (mword_of_int 63 : mword 6)))
                    = (mword_of_int 4095 : mword 64))
      by (rewrite HA4a5; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite H4095) in "Hcg".
    set (A5 := <[Regidx Ra5 := regval_into_reg (mword_of_int 4095 : mword 64)]> A4).
    change (<[Regidx Ra5 := regval_into_reg (mword_of_int 4095 : mword 64)]> A4) with A5.
    assert (Hpc16 : add_vec_int (mword_of_int (KernelSyms.uvmdealloc + 0x14) : mword 64) 2
                    = mword_of_int (KernelSyms.uvmdealloc + 0x16))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc16) in "Hpc".
    assert (HA5a5 : A5 !!! Regidx Ra5 = (mword_of_int 4095 : mword 64))
      by (rewrite /A5 upd_eq; reflexivity).
    assert (HA5a2 : A5 !!! Regidx Ra2 = newsz).
    { rewrite /A5 upd_ne; [| reg_neq]. rewrite /A4 upd_ne; [| reg_neq]. exact HA3a2. }
    assert (HA5a1 : A5 !!! Regidx Ra1 = oldsz).
    { rewrite /A5 upd_ne; [| reg_neq]. rewrite /A4 upd_ne; [| reg_neq]. exact HA3a1. }
    (* +0x16 add a4,a2,a5 : a4 := newsz + 4095 *)
    iApply (wp_add_s_sconf (mword_of_int (KernelSyms.uvmdealloc + 0x16)) Ra4 Ra2 Ra5
              (add_vec newsz (mword_of_int 4095)) A5 (K - 4)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(rgne; rgne; rewrite HA5a2 HA5a5; reflexivity)
              with "Hcg Hpc Hi16").
    iIntros (CID11 Hs11) "Hcg Hpc".
    set (A6 := <[Regidx Ra4 := regval_into_reg (add_vec newsz (mword_of_int 4095))]> A5).
    change (<[Regidx Ra4 := regval_into_reg (add_vec newsz (mword_of_int 4095))]> A5) with A6.
    assert (Hpc1a : add_vec_int (mword_of_int (KernelSyms.uvmdealloc + 0x16) : mword 64) 4
                    = mword_of_int (KernelSyms.uvmdealloc + 0x1a))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc1a) in "Hpc".
    (* +0x1a c.lui a3,0xfffff : a3 := -4096 *)
    iApply (wp_clui_s_sconf (mword_of_int (KernelSyms.uvmdealloc + 0x1a)) Ra3
              (sign_extend' 20 (mword_of_int 63 : mword 6)) (mword_of_int (-4096) : mword 64)
              A6 (K - 4)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok) lui_m4096
              with "Hcg Hpc Hi1a").
    iIntros (CID12 Hs12) "Hcg Hpc".
    set (A7 := <[Regidx Ra3 := regval_into_reg (mword_of_int (-4096) : mword 64)]> A6).
    change (<[Regidx Ra3 := regval_into_reg (mword_of_int (-4096) : mword 64)]> A6) with A7.
    assert (Hpc1c : add_vec_int (mword_of_int (KernelSyms.uvmdealloc + 0x1a) : mword 64) 2
                    = mword_of_int (KernelSyms.uvmdealloc + 0x1c))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc1c) in "Hpc".
    assert (HA7a3 : A7 !!! Regidx Ra3 = (mword_of_int (-4096) : mword 64))
      by (rewrite /A7 upd_eq; reflexivity).
    assert (HA7a4 : A7 !!! Regidx Ra4 = add_vec newsz (mword_of_int 4095)).
    { rewrite /A7 upd_ne; [| reg_neq]. rewrite /A6 upd_eq. reflexivity. }
    assert (HA7a5 : A7 !!! Regidx Ra5 = (mword_of_int 4095 : mword 64)).
    { rewrite /A7 upd_ne; [| reg_neq]. rewrite /A6 upd_ne; [| reg_neq]. exact HA5a5. }
    assert (HA7a1 : A7 !!! Regidx Ra1 = oldsz).
    { rewrite /A7 upd_ne; [| reg_neq]. rewrite /A6 upd_ne; [| reg_neq]. exact HA5a1. }
    (* +0x1c c.and a4,a4,a3 : a4 := PGROUNDUP(newsz) *)
    iApply (wp_cand_s_sconf (mword_of_int (KernelSyms.uvmdealloc + 0x1c)) Ra4 Ra3 A7 (K - 4)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi1c").
    iIntros (CID13 Hs13) "Hcg Hpc".
    iEval (rgne) in "Hcg". iEval (rgne) in "Hcg".
    assert (Hpgun : and_vec (A7 !!! Regidx Ra4) (A7 !!! Regidx Ra3) = pgroundup newsz)
      by (rewrite HA7a4 HA7a3; reflexivity).
    iEval (rewrite Hpgun) in "Hcg".
    set (A8 := <[Regidx Ra4 := regval_into_reg (pgroundup newsz)]> A7).
    change (<[Regidx Ra4 := regval_into_reg (pgroundup newsz)]> A7) with A8.
    assert (Hpc1e : add_vec_int (mword_of_int (KernelSyms.uvmdealloc + 0x1c) : mword 64) 2
                    = mword_of_int (KernelSyms.uvmdealloc + 0x1e))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc1e) in "Hpc".
    assert (HA8a5 : A8 !!! Regidx Ra5 = (mword_of_int 4095 : mword 64))
      by (rewrite /A8 upd_ne; [exact HA7a5 | reg_neq]).
    assert (HA8a1 : A8 !!! Regidx Ra1 = oldsz)
      by (rewrite /A8 upd_ne; [exact HA7a1 | reg_neq]).
    assert (HA8a3 : A8 !!! Regidx Ra3 = (mword_of_int (-4096) : mword 64))
      by (rewrite /A8 upd_ne; [exact HA7a3 | reg_neq]).
    (* +0x1e c.add a5,a5,a1 : a5 := 4095 + oldsz *)
    iApply (wp_cadd_s_sconf (mword_of_int (KernelSyms.uvmdealloc + 0x1e)) Ra5 Ra1 A8 (K - 4)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi1e").
    iIntros (CID14 Hs14) "Hcg Hpc".
    iEval (rgne) in "Hcg". iEval (rgne) in "Hcg".
    assert (Hsum5 : add_vec (A8 !!! Regidx Ra5) (A8 !!! Regidx Ra1)
                    = add_vec oldsz (mword_of_int 4095))
      by (rewrite HA8a5 HA8a1; apply add_vec64_comm).
    iEval (rewrite Hsum5) in "Hcg".
    set (A9 := <[Regidx Ra5 := regval_into_reg (add_vec oldsz (mword_of_int 4095))]> A8).
    change (<[Regidx Ra5 := regval_into_reg (add_vec oldsz (mword_of_int 4095))]> A8) with A9.
    assert (Hpc20 : add_vec_int (mword_of_int (KernelSyms.uvmdealloc + 0x1e) : mword 64) 2
                    = mword_of_int (KernelSyms.uvmdealloc + 0x20))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc20) in "Hpc".
    assert (HA9a5 : A9 !!! Regidx Ra5 = add_vec oldsz (mword_of_int 4095))
      by (rewrite /A9 upd_eq; reflexivity).
    assert (HA9a3 : A9 !!! Regidx Ra3 = (mword_of_int (-4096) : mword 64))
      by (rewrite /A9 upd_ne; [exact HA8a3 | reg_neq]).
    (* +0x20 c.and a5,a5,a3 : a5 := PGROUNDUP(oldsz) *)
    iApply (wp_cand_s_sconf (mword_of_int (KernelSyms.uvmdealloc + 0x20)) Ra5 Ra3 A9 (K - 4)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi20").
    iIntros (CID15 Hs15) "Hcg Hpc".
    iEval (rgne) in "Hcg". iEval (rgne) in "Hcg".
    assert (Hpguo : and_vec (A9 !!! Regidx Ra5) (A9 !!! Regidx Ra3) = pgroundup oldsz)
      by (rewrite HA9a5 HA9a3; reflexivity).
    iEval (rewrite Hpguo) in "Hcg".
    set (A10 := <[Regidx Ra5 := regval_into_reg (pgroundup oldsz)]> A9).
    change (<[Regidx Ra5 := regval_into_reg (pgroundup oldsz)]> A9) with A10.
    assert (Hpc22 : add_vec_int (mword_of_int (KernelSyms.uvmdealloc + 0x20) : mword 64) 2
                    = mword_of_int (KernelSyms.uvmdealloc + 0x22))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc22) in "Hpc".
    (* the register facts at the second branch *)
    assert (HA10a5 : A10 !!! Regidx Ra5 = pgroundup oldsz)
      by (rewrite /A10 upd_eq; reflexivity).
    assert (HA10a4 : A10 !!! Regidx Ra4 = pgroundup newsz).
    { rewrite /A10 upd_ne; [| reg_neq]. rewrite /A9 upd_ne; [| reg_neq].
      rewrite /A8 upd_eq. reflexivity. }
    assert (HA10sp : A10 !!! Regidx csp_rs1 = spd).
    { rewrite /A10 upd_ne; [| reg_neq]. rewrite /A9 upd_ne; [| reg_neq].
      rewrite /A8 upd_ne; [| reg_neq]. rewrite /A7 upd_ne; [| reg_neq].
      rewrite /A6 upd_ne; [| reg_neq]. rewrite /A5 upd_ne; [| reg_neq].
      rewrite /A4 upd_ne; [| reg_neq]. exact HA3sp. }
    assert (HA10s1 : A10 !!! Regidx Rs1 = newsz).
    { rewrite /A10 upd_ne; [| reg_neq]. rewrite /A9 upd_ne; [| reg_neq].
      rewrite /A8 upd_ne; [| reg_neq]. rewrite /A7 upd_ne; [| reg_neq].
      rewrite /A6 upd_ne; [| reg_neq]. rewrite /A5 upd_ne; [| reg_neq].
      rewrite /A4 upd_ne; [| reg_neq]. exact HA3s1. }
    assert (HA10a0 : A10 !!! Regidx Ra0 = page_base (ud_root P)).
    { rewrite /A10 upd_ne; [| reg_neq]. rewrite /A9 upd_ne; [| reg_neq].
      rewrite /A8 upd_ne; [| reg_neq]. rewrite /A7 upd_ne; [| reg_neq].
      rewrite /A6 upd_ne; [| reg_neq]. rewrite /A5 upd_ne; [| reg_neq].
      rewrite /A4 upd_ne; [| reg_neq]. exact HA3a0. }
    assert (HA10thr : forall c : mword 5, is_cs_idx c = true ->
              c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 ->
              A10 !!! Regidx c = mm !!! Regidx c).
    { intros c Hc H2 H8 H9.
      rewrite /A10 upd_ne;
        [| intros Hx; injection Hx as Hx2; subst c; vm_compute in Hc; discriminate].
      rewrite /A9 upd_ne;
        [| intros Hx; injection Hx as Hx2; subst c; vm_compute in Hc; discriminate].
      rewrite /A8 upd_ne;
        [| intros Hx; injection Hx as Hx2; subst c; vm_compute in Hc; discriminate].
      rewrite /A7 upd_ne;
        [| intros Hx; injection Hx as Hx2; subst c; vm_compute in Hc; discriminate].
      rewrite /A6 upd_ne;
        [| intros Hx; injection Hx as Hx2; subst c; vm_compute in Hc; discriminate].
      rewrite /A5 upd_ne;
        [| intros Hx; injection Hx as Hx2; subst c; vm_compute in Hc; discriminate].
      rewrite /A4 upd_ne;
        [| intros Hx; injection Hx as Hx2; subst c; vm_compute in Hc; discriminate].
      apply HA3thr; assumption. }

    (* ================================================================= *)
    (* §F  +0x22 bltu a4,a5 : is there anything to unmap?                 *)
    (* ================================================================= *)
    destruct (zopz0zI_u (pgroundup newsz) (pgroundup oldsz)) eqn:Hcmp2.
    2:{ (* ---- FALLS: the two rounded sizes tie; the run is empty ---- *)
      assert (Hple : bv_unsigned (pgroundup oldsz) <= bv_unsigned (pgroundup newsz)).
      { unfold zopz0zI_u in Hcmp2.
        rewrite -!uint_unsigned. exact (proj1 (Z.ltb_ge _ _) Hcmp2). }
      assert (Hnp0 : uvmd_np oldsz newsz = 0%nat)
        by (rewrite Hnpdef; apply z_np_zero; exact Hple).
      iAssert (proc_pt (uptd_del_run P (svpn_of (pgroundup newsz)) (uvmd_np oldsz newsz)))
        with "[Hpt]" as "Hpt".
      { iEval (rewrite (proc_pt_data_irrel P
                 (uptd_del_run P (svpn_of (pgroundup newsz)) (uvmd_np oldsz newsz))
                 ltac:(rewrite Hnp0; reflexivity)
                 ltac:(rewrite Hnp0; reflexivity)
                 ltac:(rewrite Hnp0; reflexivity))) in "Hpt".
        iExact "Hpt". }
      assert (Hcmp2' : zopz0zI_u (rget A10 Ra4) (rget A10 Ra5) = false).
      { rgne. rgne. rewrite HA10a4 HA10a5. exact Hcmp2. }
      iApply (wp_bltu_fall_s_sconf (mword_of_int (KernelSyms.uvmdealloc + 0x22))
                (mword_of_int 16 : mword 13) Ra5 Ra4 A10 (K - 4)%nat b
                ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) Hcmp2'
                with "Hcg Hpc Hi22").
      iIntros (CID16 Hs16) "Hcg Hpc".
      assert (Hpc26 : add_vec_int (mword_of_int (KernelSyms.uvmdealloc + 0x22) : mword 64) 4
                      = mword_of_int (KernelSyms.uvmdealloc + 0x26))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpc26) in "Hpc".
      iDestruct (cpu_own_transport CID CID16 0%nat eb p C b ltac:(wp_next_chain)
                   with "Hcpu") as "Hcpu".
      iApply (wp_uvmdealloc_epi mm A10 P K eb p C b oldsz newsz newsz ret_tgt lks
                ltac:(lia) ltac:(wp_next_chain) eq_refl HA10sp HA10s1 HA10thr
                ltac:(right; split; [exact Hlt | reflexivity])
                with "Hcg Hcpu Htext Hpc Hr24 Hr16 Hr8 [Hgap] Hpt Hcont").
      { iExists _. iExact "Hgap". } }

    (* ---- TAKEN: PGROUNDUP(newsz) < PGROUNDUP(oldsz) ---- *)
    assert (Hpltz : bv_unsigned (pgroundup newsz) < bv_unsigned (pgroundup oldsz)).
    { unfold zopz0zI_u in Hcmp2.
      rewrite -!uint_unsigned. exact (proj1 (Z.ltb_lt _ _) Hcmp2). }
    assert (Hcmp2' : zopz0zI_u (rget A10 Ra4) (rget A10 Ra5) = true).
    { rgne. rgne. rewrite HA10a4 HA10a5. exact Hcmp2. }
    iApply (wp_bltu_taken_s_sconf (mword_of_int (KernelSyms.uvmdealloc + 0x22))
              (mword_of_int 16 : mword 13) Ra5 Ra4 A10 (K - 4)%nat b
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              Hcmp2' ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi22").
    iNext. iIntros (CID17 Hs17) "Hcg Hpc".
    assert (Htgt32 : add_vec (mword_of_int (KernelSyms.uvmdealloc + 0x22) : mword 64)
                       (sign_extend' 64 (mword_of_int 16 : mword 13))
                     = mword_of_int (KernelSyms.uvmdealloc + 0x32))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgt32) in "Hpc".

    (* ================================================================= *)
    (* §G  The run length, as a plain [Z].                                *)
    (* ================================================================= *)
    destruct (z_np_exact (bv_unsigned (pgroundup oldsz)) (bv_unsigned (pgroundup newsz))
                ltac:(lia) Hpumod Hpnmod) as [Hq0 Hqmul].
    assert (Hqz : Z.of_nat (uvmd_np oldsz newsz)
                  = (bv_unsigned (pgroundup oldsz) - bv_unsigned (pgroundup newsz)) / 4096)
      by (rewrite Hnpdef; apply Z2Nat.id; exact Hq0).
    assert (Hqlt : (bv_unsigned (pgroundup oldsz) - bv_unsigned (pgroundup newsz)) / 4096
                   < 2147483648)
      by (apply z_np_lt31; [exact Hpn0 | exact Hpubnd]).

    (* ================================================================= *)
    (* §H  +0x32..+0x3e: npages, do_free = 1, uvmunmap().                 *)
    (* ================================================================= *)
    iPoseProof (udi_32 with "Htext") as "Hi32".
    iPoseProof (udi_34 with "Htext") as "Hi34".
    iPoseProof (udi_36 with "Htext") as "Hi36".
    iPoseProof (udi_38 with "Htext") as "Hi38".
    iPoseProof (udi_3c with "Htext") as "Hi3c".
    iPoseProof (udi_3e with "Htext") as "Hi3e".
    iPoseProof (udi_42 with "Htext") as "Hi42".
    (* +0x32 c.sub a5,a5,a4 *)
    assert (Hsubv : sub_vec (rget A10 Ra5) (rget A10 Ra4)
                    = (mword_of_int (bv_unsigned (pgroundup oldsz)
                                     - bv_unsigned (pgroundup newsz)) : mword 64)).
    { rgne. rgne. rewrite HA10a5 HA10a4. apply bv_eq.
      rewrite sub_vec64_unsigned. symmetry. apply moi64_unsigned. }
    iApply (wp_csub_wval_s_sconf (mword_of_int (KernelSyms.uvmdealloc + 0x32)) Ra5 Ra5 Ra4
              (mword_of_int (bv_unsigned (pgroundup oldsz)
                             - bv_unsigned (pgroundup newsz)) : mword 64)
              A10 (K - 4)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok) Hsubv
              with "Hcg Hpc Hi32").
    iIntros (CID18 Hs18) "Hcg Hpc".
    set (B1 := <[Regidx Ra5 := regval_into_reg
        (mword_of_int (bv_unsigned (pgroundup oldsz)
                       - bv_unsigned (pgroundup newsz)) : mword 64)]> A10).
    change (<[Regidx Ra5 := regval_into_reg
        (mword_of_int (bv_unsigned (pgroundup oldsz)
                       - bv_unsigned (pgroundup newsz)) : mword 64)]> A10) with B1.
    assert (Hpc34 : add_vec_int (mword_of_int (KernelSyms.uvmdealloc + 0x32) : mword 64) 2
                    = mword_of_int (KernelSyms.uvmdealloc + 0x34))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc34) in "Hpc".
    assert (HB1a5 : B1 !!! Regidx Ra5
                    = (mword_of_int (bv_unsigned (pgroundup oldsz)
                                     - bv_unsigned (pgroundup newsz)) : mword 64))
      by (rewrite /B1 upd_eq; reflexivity).
    (* +0x34 c.srli a5,a5,0xc : a5 := npages *)
    iApply (wp_csrli_s_sconf (mword_of_int (KernelSyms.uvmdealloc + 0x34)) (Cregidx (mword_of_int 7)) Ra5
              (mword_of_int 12 : mword 6) B1 (K - 4)%nat b
              udl_cr7 ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi34").
    iIntros (CID19 Hs19) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    assert (Hnpv : shift_bits_right (B1 !!! Regidx Ra5)
                     (subrange_vec_dec (mword_of_int 12 : mword 6) (Z.sub log2_xlen 1) 0)
                   = (mword_of_int (Z.of_nat (uvmd_np oldsz newsz)) : mword 64)).
    { rewrite HB1a5 srli12_div4096 Hqz.
      assert (Hbd : bv_unsigned (mword_of_int (bv_unsigned (pgroundup oldsz)
                                  - bv_unsigned (pgroundup newsz)) : mword 64)
                    = bv_unsigned (pgroundup oldsz) - bv_unsigned (pgroundup newsz)).
      { rewrite moi64_unsigned. apply bvw64_small.
        pose proof (bv_unsigned_in_range _ (pgroundup oldsz)) as Hro.
        assert (Hm : bv_modulus (MachineWord.MachineWord.Z_idx 64) = 18446744073709551616)
          by (vm_compute; reflexivity).
        rewrite Hm in Hro. change (2 ^ 64) with 18446744073709551616. lia. }
      rewrite Hbd. reflexivity. }
    iEval (rewrite Hnpv) in "Hcg".
    set (B2 := <[Regidx Ra5 := regval_into_reg
        (mword_of_int (Z.of_nat (uvmd_np oldsz newsz)) : mword 64)]> B1).
    change (<[Regidx Ra5 := regval_into_reg
        (mword_of_int (Z.of_nat (uvmd_np oldsz newsz)) : mword 64)]> B1) with B2.
    assert (Hpc36 : add_vec_int (mword_of_int (KernelSyms.uvmdealloc + 0x34) : mword 64) 2
                    = mword_of_int (KernelSyms.uvmdealloc + 0x36))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc36) in "Hpc".
    (* +0x36 c.li a3,1 : do_free = 1 *)
    iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.uvmdealloc + 0x36)) Ra3 (mword_of_int 1 : mword 6)
              (mword_of_int 1 : mword 64) B2 (K - 4)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc Hi36").
    iIntros (CID20 Hs20) "Hcg Hpc".
    set (B3 := <[Regidx Ra3 := regval_into_reg (mword_of_int 1 : mword 64)]> B2).
    change (<[Regidx Ra3 := regval_into_reg (mword_of_int 1 : mword 64)]> B2) with B3.
    assert (Hpc38 : add_vec_int (mword_of_int (KernelSyms.uvmdealloc + 0x36) : mword 64) 2
                    = mword_of_int (KernelSyms.uvmdealloc + 0x38))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc38) in "Hpc".
    assert (HB3a5 : B3 !!! Regidx Ra5
                    = (mword_of_int (Z.of_nat (uvmd_np oldsz newsz)) : mword 64)).
    { rewrite /B3 upd_ne; [| reg_neq]. rewrite /B2 upd_eq. reflexivity. }
    (* +0x38 sext.w a2,a5 : the count is small, so this is the identity *)
    iApply (wp_addiw_s_sconf (mword_of_int (KernelSyms.uvmdealloc + 0x38)) Ra2 Ra5
              (mword_of_int 0 : mword 12) B3 (K - 4)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi38").
    iIntros (CID21 Hs21) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    assert (Hsext : sign_extend' 64 (subrange_vec_dec
                      (add_vec (B3 !!! Regidx Ra5) (sign_extend' 64 (mword_of_int 0 : mword 12))) 31 0)
                    = (mword_of_int (Z.of_nat (uvmd_np oldsz newsz)) : mword 64)).
    { rewrite HB3a5. apply sextw_moi; [apply Nat2Z.is_nonneg |].
      rewrite Hqz. exact Hqlt. }
    iEval (rewrite Hsext) in "Hcg".
    set (B4 := <[Regidx Ra2 := regval_into_reg
        (mword_of_int (Z.of_nat (uvmd_np oldsz newsz)) : mword 64)]> B3).
    change (<[Regidx Ra2 := regval_into_reg
        (mword_of_int (Z.of_nat (uvmd_np oldsz newsz)) : mword 64)]> B3) with B4.
    assert (Hpc3c : add_vec_int (mword_of_int (KernelSyms.uvmdealloc + 0x38) : mword 64) 4
                    = mword_of_int (KernelSyms.uvmdealloc + 0x3c))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc3c) in "Hpc".
    assert (HB4a4 : B4 !!! Regidx Ra4 = pgroundup newsz).
    { rewrite /B4 upd_ne; [| reg_neq]. rewrite /B3 upd_ne; [| reg_neq].
      rewrite /B2 upd_ne; [| reg_neq]. rewrite /B1 upd_ne; [| reg_neq]. exact HA10a4. }
    (* +0x3c c.mv a1,a4 : a1 := PGROUNDUP(newsz) *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.uvmdealloc + 0x3c)) Ra1 Ra4 B4 (K - 4)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi3c").
    iIntros (CID22 Hs22) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    iEval (rewrite HB4a4 add_vec_zero_l) in "Hcg".
    set (B5 := <[Regidx Ra1 := regval_into_reg (pgroundup newsz)]> B4).
    change (<[Regidx Ra1 := regval_into_reg (pgroundup newsz)]> B4) with B5.
    assert (Hpc3e : add_vec_int (mword_of_int (KernelSyms.uvmdealloc + 0x3c) : mword 64) 2
                    = mword_of_int (KernelSyms.uvmdealloc + 0x3e))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc3e) in "Hpc".
    (* +0x3e jal ra,uvmunmap *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.uvmdealloc + 0x3e)) Rra
              (mword_of_int 2096952 : mword 21) B5 (K - 4)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi3e").
    iIntros (CID23 Hs23) "Hcg Hpc".
    set (B6 := <[Regidx Rra := regval_into_reg
        (add_vec_int (mword_of_int (KernelSyms.uvmdealloc + 0x3e) : mword 64) 4)]> B5).
    change (<[Regidx Rra := regval_into_reg
        (add_vec_int (mword_of_int (KernelSyms.uvmdealloc + 0x3e) : mword 64) 4)]> B5) with B6.
    assert (Hjmp : add_vec (mword_of_int (KernelSyms.uvmdealloc + 0x3e) : mword 64)
                     (sign_extend' 64 (mword_of_int 2096952 : mword 21))
                   = mword_of_int KernelSyms.uvmunmap)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hjmp) in "Hpc".
    (* the register facts at uvmunmap's entry *)
    assert (HB6ra : B6 !!! Regidx Rra
                    = add_vec_int (mword_of_int (KernelSyms.uvmdealloc + 0x3e) : mword 64) 4)
      by (rewrite /B6 upd_eq; reflexivity).
    assert (HB6a1 : B6 !!! Regidx Ra1 = pgroundup newsz).
    { rewrite /B6 upd_ne; [| reg_neq]. rewrite /B5 upd_eq. reflexivity. }
    assert (HB6a2 : B6 !!! Regidx Ra2
                    = (mword_of_int (Z.of_nat (uvmd_np oldsz newsz)) : mword 64)).
    { rewrite /B6 upd_ne; [| reg_neq]. rewrite /B5 upd_ne; [| reg_neq].
      rewrite /B4 upd_eq. reflexivity. }
    assert (HB6a3 : B6 !!! Regidx Ra3 = (mword_of_int 1 : mword 64)).
    { rewrite /B6 upd_ne; [| reg_neq]. rewrite /B5 upd_ne; [| reg_neq].
      rewrite /B4 upd_ne; [| reg_neq]. rewrite /B3 upd_eq. reflexivity. }
    assert (HB6a0 : B6 !!! Regidx Ra0 = page_base (ud_root P)).
    { rewrite /B6 upd_ne; [| reg_neq]. rewrite /B5 upd_ne; [| reg_neq].
      rewrite /B4 upd_ne; [| reg_neq]. rewrite /B3 upd_ne; [| reg_neq].
      rewrite /B2 upd_ne; [| reg_neq]. rewrite /B1 upd_ne; [| reg_neq]. exact HA10a0. }
    assert (HB6sp : B6 !!! Regidx csp_rs1 = spd).
    { rewrite /B6 upd_ne; [| reg_neq]. rewrite /B5 upd_ne; [| reg_neq].
      rewrite /B4 upd_ne; [| reg_neq]. rewrite /B3 upd_ne; [| reg_neq].
      rewrite /B2 upd_ne; [| reg_neq]. rewrite /B1 upd_ne; [| reg_neq]. exact HA10sp. }
    assert (HB6s1 : B6 !!! Regidx Rs1 = newsz).
    { rewrite /B6 upd_ne; [| reg_neq]. rewrite /B5 upd_ne; [| reg_neq].
      rewrite /B4 upd_ne; [| reg_neq]. rewrite /B3 upd_ne; [| reg_neq].
      rewrite /B2 upd_ne; [| reg_neq]. rewrite /B1 upd_ne; [| reg_neq]. exact HA10s1. }
    assert (HB6thr : forall c : mword 5, is_cs_idx c = true ->
              c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 ->
              B6 !!! Regidx c = mm !!! Regidx c).
    { intros c Hc H2 H8 H9.
      rewrite /B6 upd_ne;
        [| intros Hx; injection Hx as Hx2; subst c; vm_compute in Hc; discriminate].
      rewrite /B5 upd_ne;
        [| intros Hx; injection Hx as Hx2; subst c; vm_compute in Hc; discriminate].
      rewrite /B4 upd_ne;
        [| intros Hx; injection Hx as Hx2; subst c; vm_compute in Hc; discriminate].
      rewrite /B3 upd_ne;
        [| intros Hx; injection Hx as Hx2; subst c; vm_compute in Hc; discriminate].
      rewrite /B2 upd_ne;
        [| intros Hx; injection Hx as Hx2; subst c; vm_compute in Hc; discriminate].
      rewrite /B1 upd_ne;
        [| intros Hx; injection Hx as Hx2; subst c; vm_compute in Hc; discriminate].
      apply HA10thr; assumption. }
    (* the two pure premises uvmunmap asks about the run *)
    assert (Halign : subrange_vec_dec (B6 !!! Regidx Ra1) 11 0 = (zeros' 12 : mword 12))
      by (rewrite HB6a1; apply pgroundup_low12).
    assert (Hdofree : B6 !!! Regidx Ra3 <> (mword_of_int 0 : mword 64)).
    { rewrite HB6a3. intro He.
      assert (Hc : bv_unsigned (mword_of_int 1 : mword 64)
                   = bv_unsigned (mword_of_int 0 : mword 64)) by (rewrite He; reflexivity).
      vm_compute in Hc. discriminate. }
    assert (Hrange : (uint (B6 !!! Regidx Ra1)
                      + Z.of_nat (uvmd_np oldsz newsz) * 4096 <= uvm_maxsz)%Z).
    { rewrite HB6a1 uint_unsigned Hmax Hqz. lia. }
    (* ---- uvmunmap(): the entry-side tp premise SpecUvmunmap used to
       demand here is gone (HartTp.v: the map's tp slot is IGNORED, the true
       tp is [cid_word_of <the hart we are on>] by construction, no premise
       needed) -- this was the one call boundary in the tree where that
       premise was load-bearing rather than dead weight, since [B6]'s Rtp
       slot (untouched by every leaf above -- nothing writes register 4)
       could only ever be related to the CALLEE's hart [CID23] via a
       transport lemma that does not exist for a raw register equality
       (unlike [cpu_own], which [cpu_own_transport] moves across a
       hart crossing). *)
    iDestruct (cpu_own_transport CID CID23 0%nat eb p C b ltac:(wp_next_chain)
                 with "Hcpu") as "Hcpu".
    iApply (Uvmunmap.wp_uvmunmap_sconf γa B6 P (uvmd_np oldsz newsz) (K - 4)%nat eb p C 0%nat b lks
              ltac:(lia) ltac:(vm_compute; reflexivity) HB6a0 Halign HB6a2 Hdofree Hrange
              with "Hcg Hcpu Htext Hpc Hpt Henv").
    all: try lkbelow.
    iIntros (CID24 Hs24 mr) "Hcg Hcpu Hpc %Hcs Hpt".
    iEval (rewrite HB6a1) in "Hpt".
    assert (Hret42 : ret_pc (B6 !!! Regidx Rra) = mword_of_int (KernelSyms.uvmdealloc + 0x42)).
    { rewrite HB6ra. unfold ret_pc. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hret42) in "Hpc".
    (* +0x42 c.j -0x1c : back to the epilogue *)
    assert (Hmrsp : mr !!! Regidx csp_rs1 = spd).
    { rewrite (callee_saved_lookup Hcs csp_rs1 ltac:(vm_compute; reflexivity)).
      exact HB6sp. }
    assert (Hmrs1 : mr !!! Regidx Rs1 = newsz).
    { rewrite (callee_saved_lookup Hcs Rs1 ltac:(vm_compute; reflexivity)).
      exact HB6s1. }
    assert (Hmrthr : forall c : mword 5, is_cs_idx c = true ->
              c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 ->
              mr !!! Regidx c = mm !!! Regidx c).
    { intros c Hc H2 H8 H9.
      rewrite (callee_saved_lookup Hcs c Hc). apply HB6thr; assumption. }
    iApply (wp_cj_s_sconf (mword_of_int (KernelSyms.uvmdealloc + 0x42))
              (sign_extend' 21 (concat_vec (mword_of_int 2034 : mword 11) ('b"0")))
              mr (K - 4)%nat b ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi42").
    iIntros (CID25 Hs25). iNext. iIntros "Hcg Hpc".
    assert (Htgt26' : add_vec (mword_of_int (KernelSyms.uvmdealloc + 0x42) : mword 64)
                       (sign_extend' 64 (sign_extend' 21
                          (concat_vec (mword_of_int 2034 : mword 11) ('b"0"))))
                     = mword_of_int (KernelSyms.uvmdealloc + 0x26))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgt26') in "Hpc".
    iDestruct (cpu_own_transport CID24 CID25 0%nat eb p C b ltac:(wp_next_chain)
                 with "Hcpu") as "Hcpu".
    iApply (wp_uvmdealloc_epi mm mr P K eb p C b oldsz newsz newsz ret_tgt lks
              ltac:(lia) ltac:(wp_next_chain) eq_refl Hmrsp Hmrs1 Hmrthr
              ltac:(right; split; [exact Hlt | reflexivity])
              with "Hcg Hcpu Htext Hpc Hr24 Hr16 Hr8 [Hgap] Hpt Hcont").
    { iExists _. iExact "Hgap". }
  Qed.

End ProofUvmdealloc.

End UvmdeallocProof.
