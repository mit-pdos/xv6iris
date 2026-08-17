(* ProofWalkNoalloc.v -- the whole-function WP for xv6's walk() called with
   alloc = 0 (ismapped's callee): a READ-ONLY three-level descent.

   There are NO callees: the `!alloc || ((pagetable = kalloc()) == 0)`
   short-circuit means kalloc is never reached, and the `va >= MAXVA` panic arm
   is dead under the `uint va < 2^38` premise.  So this module seals
   WALK_NOALLOC directly (no functor parameters), and it lives in its own file
   so it stays OFF ProofWalk's critical path.

   The tree is taken at a GENERIC dfrac [dq] and returned unchanged; every
   PtTree/PtBuild accessor this proof uses is already dfrac-generic, so no
   dq-generalization was needed anywhere.

   Code path (KernelSyms.walk = 0x80000f5c):
     +0x00..+0x20  prologue (8-slot frame) + s1/s3/s6 := a0/a1/a2, s4 := 30,
                   s5 := 12, a5 := 2^38-1
     +0x22         bltu a5,a1 -> +0x66 panic   (FALLS: uint va < 2^38)
     +0x26..+0x36  LOOP body core (srl/andi/slli/add; ld; andi a5,s1,1)
     +0x3a         beqz a5 -> +0x72            (V = 0: the alloc/return-0 arm)
     +0x3c..+0x42  descend (s1 := next base), addiw s4,-9, bne s4,s5 -> +0x26
     +0x46..+0x50  tail: a0 := pt_addr0
     +0x52..+0x64  epilogue
     +0x72         beqz s6 -> +0x96            (TAKEN: alloc = 0)
     +0x96         li a0,0
     +0x98         j -> +0x52                                                *)
From Stdlib Require Import Eqdep_dec ZArith Lia List.
From stdpp Require Import gmap list list_monad bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import excl.
From iris.base_logic.lib Require Import ghost_var gen_heap invariants.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import RiscvExtras.
Require Import InstrBytes.
Require Import KernelText.
Require Import RegFile.
Require Import WpMmodeLeafBase.
Require Import SmodeCore.
Require Import StackOwn.
Require Import CalleeSaved.
Require Import CommonWalk PtTree.
Require Import KptTree.   (* pt_slot_phys_to_mem / pt_slot_mem_to_phys *)
Require Import PtBuild.
Require Import IntrDefs WpSmodeIntr.
Require Import HartTp WpNext.
Require Import WpSconfAlu WpSconfMem WpSconfBtype WpSconfCtl.
Require Import CodeWalk.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Require Import SpecWalk.
Require Import KernelRvcDecode.
Import Defs.
Local Open Scope Z_scope.


(* ===================================================================== *)
(* The pure case analysis the branches dispatch on: [pt_rep0 t m] read    *)
(* level by level, exactly in the order the C walk consults the tree.     *)
(* ===================================================================== *)
Lemma wkn_case (t : ptree) (m : gmap (mword 27) (mword 64)) (vpn : mword 27) :
  pt_rep0 t m ->
  (pt_kids t (vpn_idx 2 vpn) = None
   /\ pt_ents t (vpn_idx 2 vpn) = mword_of_int 0
   /\ m !! vpn = None)
  \/ (exists c1,
        pt_kids t (vpn_idx 2 vpn) = Some c1
        /\ pte_valid (pt_ents t (vpn_idx 2 vpn))
        /\ pte_ptr (pt_ents t (vpn_idx 2 vpn))
        /\ u_next_base (pt_ents t (vpn_idx 2 vpn)) = pt_base c1
        /\ ( (pt_kids c1 (vpn_idx 1 vpn) = None
              /\ pt_ents c1 (vpn_idx 1 vpn) = mword_of_int 0
              /\ m !! vpn = None)
             \/ (exists c0,
                   pt_kids c1 (vpn_idx 1 vpn) = Some c0
                   /\ pte_valid (pt_ents c1 (vpn_idx 1 vpn))
                   /\ pte_ptr (pt_ents c1 (vpn_idx 1 vpn))
                   /\ u_next_base (pt_ents c1 (vpn_idx 1 vpn)) = pt_base c0
                   /\ ( m !! vpn = Some (pt_ents c0 (vpn_idx 0 vpn))
                        \/ (pt_ents c0 (vpn_idx 0 vpn) = mword_of_int 0
                            /\ m !! vpn = None) )))).
Proof.
  intros Hrep.
  destruct (m !! vpn) as [wv|] eqn:Hmv.
  - destruct (proj1 Hrep vpn wv Hmv) as (p2 & p1 & Hmaps).
    destruct Hmaps as (c1 & c0 & Hk2 & Hk1 & He2 & He1 & He0 & Hb1 & Hb0 &
                       Hv2 & Hp2 & Hv1 & Hp1 & _).
    right. exists c1.
    split; [exact Hk2 |].
    split; [rewrite He2; exact Hv2 |].
    split; [rewrite He2; exact Hp2 |].
    split; [rewrite He2; exact Hb1 |].
    right. exists c0.
    split; [exact Hk1 |].
    split; [rewrite He1; exact Hv1 |].
    split; [rewrite He1; exact Hp1 |].
    split; [rewrite He1; exact Hb0 |].
    left. rewrite He0. reflexivity.
  - destruct (proj2 Hrep vpn Hmv) as
      [ (Hk2 & He2)
      | [ (c1 & Hk2 & Hk1 & Hv2 & Hp2 & Hb1 & He1)
        | (c1 & c0 & Hk2 & Hk1 & Hv2 & Hp2 & Hv1 & Hp1 & Hb1 & Hb0 & He0) ] ].
    + left. split; [exact Hk2 | split; [exact He2 | reflexivity]].
    + right. exists c1.
      split; [exact Hk2 |]. split; [exact Hv2 |]. split; [exact Hp2 |].
      split; [exact Hb1 |].
      left. split; [exact Hk1 | split; [exact He1 | reflexivity]].
    + right. exists c1.
      split; [exact Hk2 |]. split; [exact Hv2 |]. split; [exact Hp2 |].
      split; [exact Hb1 |].
      right. exists c0.
      split; [exact Hk1 |]. split; [exact Hv1 |]. split; [exact Hp1 |].
      split; [exact Hb0 |].
      right. split; [exact He0 | reflexivity].
Qed.

(* the two concrete decrements of the loop counter s4 (30 -> 21 -> 12) *)
Lemma wkn_dec9_30 :
  sign_extend' 64 (subrange_vec_dec
    (add_vec (mword_of_int 30 : mword 64)
             (sign_extend' 64 (sign_extend' 12 (mword_of_int 55 : mword 6)))) 31 0)
  = (mword_of_int 21 : mword 64).
Proof. apply bv_eq; vm_compute; reflexivity. Qed.

Lemma wkn_dec9_21 :
  sign_extend' 64 (subrange_vec_dec
    (add_vec (mword_of_int 21 : mword 64)
             (sign_extend' 64 (sign_extend' 12 (mword_of_int 55 : mword 6)))) 31 0)
  = (mword_of_int 12 : mword 64).
Proof. apply bv_eq; vm_compute; reflexivity. Qed.


Module WalkNoallocProof : WALK_NOALLOC.

Section ProofWalkNoalloc.
  Context `{!riscvGS Σ, !sieG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.


  Context {kt : ktier}.
  Ltac reg_neq :=
    lazymatch goal with
    | |- ?a <> ?b => tryif unify a b then fail else (vm_compute; discriminate)
    end.

  Ltac peel_reg :=
    repeat first
      [ rewrite upd_eq
      | rewrite upd_ne; [| reg_neq]
      | lazymatch goal with |- ?M !!! _ = _ => is_var M; progress unfold M end ];
    reflexivity.

  (* A READ-ONLY single-step descent: [ptree_own_descend]'s frame wand hands
     back [pt_upd_kid t i (Some c')], and turning that back into [t] would need
     funext on the node's [kids] function.  The alloc = 0 walk never modifies a
     node, so it only ever needs this form (over [pt_kids_own_acc_ro]). *)
  Lemma ptree_own_descend_ro (lvl : nat) (dq : dfrac) (t c : ptree) (i : mword 9) :
    pt_kids t i = Some c ->
    ptree_own (S lvl) dq t ⊢
      ptree_own lvl dq c ∗ (ptree_own lvl dq c -∗ ptree_own (S lvl) dq t).
  Proof.
    (* the two [ptree_own (S lvl) dq t] occurrences are IDENTICAL here (unlike
       [ptree_own_descend], whose wand returns [pt_upd_kid …]), so a bare
       [rewrite ptree_own_S] would hit both -- scope the first to the hyp. *)
    intros Hk. iIntros "H". iEval (rewrite ptree_own_S) in "H".
    iDestruct "H" as "[Hpg Hks]".
    iDestruct (pt_kids_own_acc_ro lvl dq t i c Hk with "Hks") as "[Hc Hclose]".
    iFrame "Hc". iIntros "Hc'". rewrite ptree_own_S.
    iSplitL "Hpg"; [ iExact "Hpg" | iApply "Hclose"; iExact "Hc'" ].
  Qed.

  (* ================================================================= *)
  (* THE SHARED EPILOGUE (+0x52..+0x64).                                *)
  (* ================================================================= *)
  Local Lemma wp_wkn_epilogue `{CID0 : CpuId} 
      (mm Mf : regfile) (t : ptree) (m : gmap (mword 27) (mword 64))
      (K : nat) (dq : dfrac) (b : bool) (p : mword 64) :
    let va := mm !!! Regidx (mword_of_int 11) in
    let vpn := svpn_of va in
    let sp0 := mm !!! Regidx csp_rs1 in
    let spr := add_vec sp0 (sign_extend' 64 (caddi16sp_imm (mword_of_int 60 : mword 6))) in
    let ret_tgt := ret_pc (mm !!! Regidx (mword_of_int 1)) in
    (8 <= K)%nat ->
    Mf !!! Regidx csp_rs1 = spr ->
    Mf !!! Regidx (mword_of_int 4 : mword 5) = mm !!! Regidx (mword_of_int 4) ->
    Mf !!! Regidx (mword_of_int 23 : mword 5) = mm !!! Regidx (mword_of_int 23) ->
    Mf !!! Regidx (mword_of_int 24 : mword 5) = mm !!! Regidx (mword_of_int 24) ->
    Mf !!! Regidx (mword_of_int 25 : mword 5) = mm !!! Regidx (mword_of_int 25) ->
    Mf !!! Regidx (mword_of_int 26 : mword 5) = mm !!! Regidx (mword_of_int 26) ->
    Mf !!! Regidx (mword_of_int 27 : mword 5) = mm !!! Regidx (mword_of_int 27) ->
    ( (Mf !!! Regidx (mword_of_int 10 : mword 5) = mword_of_int 0 /\ m !! vpn = None)
      \/ (exists p2 p1 w0,
            ptree_level0 t vpn p2 p1 w0 /\
            Mf !!! Regidx (mword_of_int 10 : mword 5) = pt_addr0 p1 vpn /\
            (m !! vpn = Some w0
             \/ (w0 = mword_of_int 0 /\ m !! vpn = None))) ) ->
    sie_cap_gpr kt Mf (K - 8)%nat b p -∗
    kernel_text -∗
    pc_is (mword_of_int (KernelSyms.walk + 0x52)) -∗
    pa_stk sp0 1 ↦₈ (mm !!! Regidx (mword_of_int 1)) -∗
    pa_stk sp0 2 ↦₈ (mm !!! Regidx (mword_of_int 8)) -∗
    pa_stk sp0 3 ↦₈ (mm !!! Regidx (mword_of_int 9)) -∗
    pa_stk sp0 4 ↦₈ (mm !!! Regidx (mword_of_int 18)) -∗
    pa_stk sp0 5 ↦₈ (mm !!! Regidx (mword_of_int 19)) -∗
    pa_stk sp0 6 ↦₈ (mm !!! Regidx (mword_of_int 20)) -∗
    pa_stk sp0 7 ↦₈ (mm !!! Regidx (mword_of_int 21)) -∗
    pa_stk sp0 8 ↦₈ (mm !!! Regidx (mword_of_int 22)) -∗
    ptree_own 2 dq t -∗
    wp_next b p (fun (CID : CpuId) =>
      ∀ (mr : regfile),
      sie_cap_gpr kt mr K b p -∗
      pc_is ret_tgt -∗
      ptree_own 2 dq t -∗
      ⌜callee_saved mm mr⌝ -∗
      ⌜ (mr !!! Regidx (mword_of_int 10) = mword_of_int 0 /\ m !! vpn = None)
        \/ (exists p2 p1 w0,
              ptree_level0 t vpn p2 p1 w0 /\
              mr !!! Regidx (mword_of_int 10) = pt_addr0 p1 vpn /\
              (m !! vpn = Some w0
               \/ (w0 = mword_of_int 0 /\ m !! vpn = None))) ⌝ -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros va vpn sp0 spr ret_tgt HK Hsp Htp Hx23 Hx24 Hx25 Hx26 Hx27 Hpay.
    iIntros "Hcg #Htext Hpc
             Hc56 Hc48 Hc40 Hc32 Hc24 Hc16 Hc08 Hc00
             Hptree Hcont".
    assert (Hb1 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 7 : mword 6) ('b"000"))) = pa_stk sp0 1).
    { unfold spr, pa_stk, add_vec_int. rewrite !pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb2 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 6 : mword 6) ('b"000"))) = pa_stk sp0 2).
    { unfold spr, pa_stk, add_vec_int. rewrite !pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb3 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000"))) = pa_stk sp0 3).
    { unfold spr, pa_stk, add_vec_int. rewrite !pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb4 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000"))) = pa_stk sp0 4).
    { unfold spr, pa_stk, add_vec_int. rewrite !pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb5 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000"))) = pa_stk sp0 5).
    { unfold spr, pa_stk, add_vec_int. rewrite !pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb6 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000"))) = pa_stk sp0 6).
    { unfold spr, pa_stk, add_vec_int. rewrite !pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb7 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) = pa_stk sp0 7).
    { unfold spr, pa_stk, add_vec_int. rewrite !pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb8 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000"))) = pa_stk sp0 8).
    { unfold spr, pa_stk, add_vec_int. rewrite !pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hsprstk : pa_stk sp0 8 = spr).
    { rewrite /pa_stk /spr /sp0 /add_vec_int. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    iPoseProof (wi_52 with "Htext") as "Hi52".
    iPoseProof (wi_54 with "Htext") as "Hi54".
    iPoseProof (wi_56 with "Htext") as "Hi56".
    iPoseProof (wi_58 with "Htext") as "Hi58".
    iPoseProof (wi_5a with "Htext") as "Hi5a".
    iPoseProof (wi_5c with "Htext") as "Hi5c".
    iPoseProof (wi_5e with "Htext") as "Hi5e".
    iPoseProof (wi_60 with "Htext") as "Hi60".
    iPoseProof (wi_62 with "Htext") as "Hi62".
    iPoseProof (wi_64 with "Htext") as "Hi64".
    (* +0x52 c.ldsp x1,56(sp) *)
    pose proof Hsp as HspMf.
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.walk + 0x52)) (mword_of_int 7 : mword 6) (mword_of_int 1 : mword 5)
              Mf (K - 8)%nat (mm !!! Regidx (mword_of_int 1 : mword 5)) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi52 [Hc56]").
    { iEval (rewrite HspMf Hb1). iExact "Hc56". }
    iIntros (CID1 Hs1) "Hcg Hpc Hc56".
    iEval (rewrite HspMf Hb1) in "Hc56".
    set (E1 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (mm !!! Regidx (mword_of_int 1 : mword 5))]> Mf).
    assert (Hpp52n : add_vec_int (mword_of_int (KernelSyms.walk + 0x52) : mword 64) 2 = mword_of_int (KernelSyms.walk + 0x54)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp52n) in "Hpc".
    (* +0x54 c.ldsp x8,48(sp) *)
    assert (HspE1 : E1 !!! Regidx csp_rs1 = spr).
    { rewrite /E1. rewrite upd_ne; [| reg_neq]. exact HspMf. }
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.walk + 0x54)) (mword_of_int 6 : mword 6) (mword_of_int 8 : mword 5)
              E1 (K - 8)%nat (mm !!! Regidx (mword_of_int 8 : mword 5)) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi54 [Hc48]").
    { iEval (rewrite HspE1 Hb2). iExact "Hc48". }
    iIntros (CID2 Hs2) "Hcg Hpc Hc48".
    iEval (rewrite HspE1 Hb2) in "Hc48".
    set (E2 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg (mm !!! Regidx (mword_of_int 8 : mword 5))]> E1).
    assert (Hpp54n : add_vec_int (mword_of_int (KernelSyms.walk + 0x54) : mword 64) 2 = mword_of_int (KernelSyms.walk + 0x56)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp54n) in "Hpc".
    (* +0x56 c.ldsp x9,40(sp) *)
    assert (HspE2 : E2 !!! Regidx csp_rs1 = spr).
    { rewrite /E2. rewrite upd_ne; [| reg_neq]. exact HspE1. }
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.walk + 0x56)) (mword_of_int 5 : mword 6) (mword_of_int 9 : mword 5)
              E2 (K - 8)%nat (mm !!! Regidx (mword_of_int 9 : mword 5)) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi56 [Hc40]").
    { iEval (rewrite HspE2 Hb3). iExact "Hc40". }
    iIntros (CID3 Hs3) "Hcg Hpc Hc40".
    iEval (rewrite HspE2 Hb3) in "Hc40".
    set (E3 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (mm !!! Regidx (mword_of_int 9 : mword 5))]> E2).
    assert (Hpp56n : add_vec_int (mword_of_int (KernelSyms.walk + 0x56) : mword 64) 2 = mword_of_int (KernelSyms.walk + 0x58)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp56n) in "Hpc".
    (* +0x58 c.ldsp x18,32(sp) *)
    assert (HspE3 : E3 !!! Regidx csp_rs1 = spr).
    { rewrite /E3. rewrite upd_ne; [| reg_neq]. exact HspE2. }
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.walk + 0x58)) (mword_of_int 4 : mword 6) (mword_of_int 18 : mword 5)
              E3 (K - 8)%nat (mm !!! Regidx (mword_of_int 18 : mword 5)) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi58 [Hc32]").
    { iEval (rewrite HspE3 Hb4). iExact "Hc32". }
    iIntros (CID4 Hs4) "Hcg Hpc Hc32".
    iEval (rewrite HspE3 Hb4) in "Hc32".
    set (E4 := <[Regidx (mword_of_int 18 : mword 5) := regval_into_reg (mm !!! Regidx (mword_of_int 18 : mword 5))]> E3).
    assert (Hpp58n : add_vec_int (mword_of_int (KernelSyms.walk + 0x58) : mword 64) 2 = mword_of_int (KernelSyms.walk + 0x5a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp58n) in "Hpc".
    (* +0x5a c.ldsp x19,24(sp) *)
    assert (HspE4 : E4 !!! Regidx csp_rs1 = spr).
    { rewrite /E4. rewrite upd_ne; [| reg_neq]. exact HspE3. }
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.walk + 0x5a)) (mword_of_int 3 : mword 6) (mword_of_int 19 : mword 5)
              E4 (K - 8)%nat (mm !!! Regidx (mword_of_int 19 : mword 5)) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi5a [Hc24]").
    { iEval (rewrite HspE4 Hb5). iExact "Hc24". }
    iIntros (CID5 Hs5) "Hcg Hpc Hc24".
    iEval (rewrite HspE4 Hb5) in "Hc24".
    set (E5 := <[Regidx (mword_of_int 19 : mword 5) := regval_into_reg (mm !!! Regidx (mword_of_int 19 : mword 5))]> E4).
    assert (Hpp5an : add_vec_int (mword_of_int (KernelSyms.walk + 0x5a) : mword 64) 2 = mword_of_int (KernelSyms.walk + 0x5c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp5an) in "Hpc".
    (* +0x5c c.ldsp x20,16(sp) *)
    assert (HspE5 : E5 !!! Regidx csp_rs1 = spr).
    { rewrite /E5. rewrite upd_ne; [| reg_neq]. exact HspE4. }
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.walk + 0x5c)) (mword_of_int 2 : mword 6) (mword_of_int 20 : mword 5)
              E5 (K - 8)%nat (mm !!! Regidx (mword_of_int 20 : mword 5)) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi5c [Hc16]").
    { iEval (rewrite HspE5 Hb6). iExact "Hc16". }
    iIntros (CID6 Hs6) "Hcg Hpc Hc16".
    iEval (rewrite HspE5 Hb6) in "Hc16".
    set (E6 := <[Regidx (mword_of_int 20 : mword 5) := regval_into_reg (mm !!! Regidx (mword_of_int 20 : mword 5))]> E5).
    assert (Hpp5cn : add_vec_int (mword_of_int (KernelSyms.walk + 0x5c) : mword 64) 2 = mword_of_int (KernelSyms.walk + 0x5e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp5cn) in "Hpc".
    (* +0x5e c.ldsp x21,8(sp) *)
    assert (HspE6 : E6 !!! Regidx csp_rs1 = spr).
    { rewrite /E6. rewrite upd_ne; [| reg_neq]. exact HspE5. }
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.walk + 0x5e)) (mword_of_int 1 : mword 6) (mword_of_int 21 : mword 5)
              E6 (K - 8)%nat (mm !!! Regidx (mword_of_int 21 : mword 5)) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi5e [Hc08]").
    { iEval (rewrite HspE6 Hb7). iExact "Hc08". }
    iIntros (CID7 Hs7) "Hcg Hpc Hc08".
    iEval (rewrite HspE6 Hb7) in "Hc08".
    set (E7 := <[Regidx (mword_of_int 21 : mword 5) := regval_into_reg (mm !!! Regidx (mword_of_int 21 : mword 5))]> E6).
    assert (Hpp5en : add_vec_int (mword_of_int (KernelSyms.walk + 0x5e) : mword 64) 2 = mword_of_int (KernelSyms.walk + 0x60)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp5en) in "Hpc".
    (* +0x60 c.ldsp x22,0(sp) *)
    assert (HspE7 : E7 !!! Regidx csp_rs1 = spr).
    { rewrite /E7. rewrite upd_ne; [| reg_neq]. exact HspE6. }
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.walk + 0x60)) (mword_of_int 0 : mword 6) (mword_of_int 22 : mword 5)
              E7 (K - 8)%nat (mm !!! Regidx (mword_of_int 22 : mword 5)) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi60 [Hc00]").
    { iEval (rewrite HspE7 Hb8). iExact "Hc00". }
    iIntros (CID8 Hs8) "Hcg Hpc Hc00".
    iEval (rewrite HspE7 Hb8) in "Hc00".
    set (E8 := <[Regidx (mword_of_int 22 : mword 5) := regval_into_reg (mm !!! Regidx (mword_of_int 22 : mword 5))]> E7).
    assert (Hpp60n : add_vec_int (mword_of_int (KernelSyms.walk + 0x60) : mword 64) 2 = mword_of_int (KernelSyms.walk + 0x62)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp60n) in "Hpc".
    assert (HspE8 : E8 !!! Regidx csp_rs1 = spr).
    { rewrite /E8. rewrite upd_ne; [| reg_neq]. exact HspE7. }
    (* +0x62 c.addi16sp sp,+64 -- the frame pop (feed 8 slots back into avail) *)
    set (E9 := <[Regidx csp_rs1 := regval_into_reg
        (add_vec (E8 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 4 : mword 6))))]> E8).
    assert (Hwv : add_vec (E8 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 4 : mword 6))) = sp0).
    { rewrite HspE8. unfold spr. apply frame_cancel_64. }
    assert (Hpop : E8 !!! Regidx csp_rs1
                   = pa_stk (add_vec (E8 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 4 : mword 6)))) 8).
    { rewrite Hwv HspE8. symmetry. exact Hsprstk. }
    iAssert (stack_own (KTR := kt) sp0 8) with "[Hc56 Hc48 Hc40 Hc32 Hc24 Hc16 Hc08 Hc00]" as "Hframe".
    { rewrite (stack_own_slots (KTR := kt)). cbn [seq].
      iSplitL "Hc56". { iExists (mm !!! Regidx (mword_of_int 1)). iExact "Hc56". }
      iSplitL "Hc48". { iExists (mm !!! Regidx (mword_of_int 8)). iExact "Hc48". }
      iSplitL "Hc40". { iExists (mm !!! Regidx (mword_of_int 9)). iExact "Hc40". }
      iSplitL "Hc32". { iExists (mm !!! Regidx (mword_of_int 18)). iExact "Hc32". }
      iSplitL "Hc24". { iExists (mm !!! Regidx (mword_of_int 19)). iExact "Hc24". }
      iSplitL "Hc16". { iExists (mm !!! Regidx (mword_of_int 20)). iExact "Hc16". }
      iSplitL "Hc08". { iExists (mm !!! Regidx (mword_of_int 21)). iExact "Hc08". }
      iSplitL "Hc00". { iExists (mm !!! Regidx (mword_of_int 22)). iExact "Hc00". }
      done. }
    iEval (rewrite -Hwv) in "Hframe".
    iApply (wp_caddi16sp_pop_s_sconf (mword_of_int (KernelSyms.walk + 0x62)) (mword_of_int 4 : mword 6)
              E8 (K - 8)%nat 8 b Hpop
              with "Hcg Hpc Hi62 Hframe").
    iIntros (CID9 Hs9) "Hcg Hpc".
    change (<[Regidx csp_rs1 := regval_into_reg (add_vec (E8 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 4 : mword 6))))]> E8) with E9.
    assert (Hnk : ((K - 8) + 8)%nat = K) by lia.
    iEval (rewrite Hnk) in "Hcg".
    assert (Hpp64 : add_vec_int (mword_of_int (KernelSyms.walk + 0x62) : mword 64) 2 = mword_of_int (KernelSyms.walk + 0x64)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp64) in "Hpc".
    (* +0x64 ret *)
    assert (HE9ra : E9 !!! Regidx (mword_of_int 1 : mword 5) = mm !!! Regidx (mword_of_int 1)).
    { peel_reg. }
    assert (Hrt : ret_pc (rget E9 (mword_of_int 1 : mword 5)) = ret_tgt).
    { rgne. rewrite HE9ra. reflexivity. }
    iApply (wp_cret_s_sconf (mword_of_int (KernelSyms.walk + 0x64)) (mword_of_int 1 : mword 5) E9 K b
              ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi64").
    iIntros (CID10 Hs10) "Hcg Hpc".
    iEval (rewrite Hrt) in "Hpc".
    iSpecialize ("Hcont" $! CID10 with "[%]"); [wp_next_chain|].
    iApply ("Hcont" $! E9 with "Hcg Hpc Hptree [%] [%]").
    { (* callee_saved mm E9 -- 13 conjuncts (sp, s0..s11), no tp slot: the
         [callee_saved] definition dropped its old tp conjunct (tp_pin makes
         it true by construction now), so [Htp] is unused here (kept as a
         harmless unused premise). sp needs the frame-cancel arithmetic;
         s0..s6 were all just RELOADED from the stack (their E-chain value
         IS [mm]'s original one by construction), so the register-agnostic
         [peel_reg] closes each directly; s7..s11 were never touched, so
         they go via the entry premises [Hx23]..[Hx27]. *)
      unfold callee_saved.
      split. { rewrite /E9 upd_eq. rewrite HspE8. unfold spr. apply frame_cancel_64. }
      split. { peel_reg. }
      split. { peel_reg. }
      split. { peel_reg. }
      split. { peel_reg. }
      split. { peel_reg. }
      split. { peel_reg. }
      split. { peel_reg. }
      repeat split;
        (rewrite /E9 /E8 /E7 /E6 /E5 /E4 /E3 /E2 /E1;
         repeat (rewrite upd_ne; [| reg_neq]);
         first [ exact Hx23 | exact Hx24 | exact Hx25 | exact Hx26 | exact Hx27 ]). }
    { assert (HE9a0 : E9 !!! Regidx (mword_of_int 10 : mword 5)
                      = Mf !!! Regidx (mword_of_int 10 : mword 5)).
      { peel_reg. }
      rewrite HE9a0. exact Hpay. }
  Qed.

  (* ================================================================= *)
  (* THE alloc = 0 ARM (+0x72 -> +0x96 -> +0x98 -> the epilogue).        *)
  (* ================================================================= *)
  Local Lemma wp_wkn_fail `{CID0 : CpuId} 
      (mm Mf : regfile) (t : ptree) (m : gmap (mword 27) (mword 64))
      (K : nat) (dq : dfrac) (b : bool) (p : mword 64) :
    let va := mm !!! Regidx (mword_of_int 11) in
    let vpn := svpn_of va in
    let sp0 := mm !!! Regidx csp_rs1 in
    let spr := add_vec sp0 (sign_extend' 64 (caddi16sp_imm (mword_of_int 60 : mword 6))) in
    let ret_tgt := ret_pc (mm !!! Regidx (mword_of_int 1)) in
    (8 <= K)%nat ->
    Mf !!! Regidx csp_rs1 = spr ->
    eq_vec (Mf !!! Regidx (mword_of_int 22 : mword 5)) zero_reg = true ->
    Mf !!! Regidx (mword_of_int 4 : mword 5) = mm !!! Regidx (mword_of_int 4) ->
    Mf !!! Regidx (mword_of_int 23 : mword 5) = mm !!! Regidx (mword_of_int 23) ->
    Mf !!! Regidx (mword_of_int 24 : mword 5) = mm !!! Regidx (mword_of_int 24) ->
    Mf !!! Regidx (mword_of_int 25 : mword 5) = mm !!! Regidx (mword_of_int 25) ->
    Mf !!! Regidx (mword_of_int 26 : mword 5) = mm !!! Regidx (mword_of_int 26) ->
    Mf !!! Regidx (mword_of_int 27 : mword 5) = mm !!! Regidx (mword_of_int 27) ->
    m !! vpn = None ->
    sie_cap_gpr kt Mf (K - 8)%nat b p -∗
    kernel_text -∗
    pc_is (mword_of_int (KernelSyms.walk + 0x72)) -∗
    pa_stk sp0 1 ↦₈ (mm !!! Regidx (mword_of_int 1)) -∗
    pa_stk sp0 2 ↦₈ (mm !!! Regidx (mword_of_int 8)) -∗
    pa_stk sp0 3 ↦₈ (mm !!! Regidx (mword_of_int 9)) -∗
    pa_stk sp0 4 ↦₈ (mm !!! Regidx (mword_of_int 18)) -∗
    pa_stk sp0 5 ↦₈ (mm !!! Regidx (mword_of_int 19)) -∗
    pa_stk sp0 6 ↦₈ (mm !!! Regidx (mword_of_int 20)) -∗
    pa_stk sp0 7 ↦₈ (mm !!! Regidx (mword_of_int 21)) -∗
    pa_stk sp0 8 ↦₈ (mm !!! Regidx (mword_of_int 22)) -∗
    ptree_own 2 dq t -∗
    wp_next b p (fun (CID : CpuId) =>
      ∀ (mr : regfile),
      sie_cap_gpr kt mr K b p -∗
      pc_is ret_tgt -∗
      ptree_own 2 dq t -∗
      ⌜callee_saved mm mr⌝ -∗
      ⌜ (mr !!! Regidx (mword_of_int 10) = mword_of_int 0 /\ m !! vpn = None)
        \/ (exists p2 p1 w0,
              ptree_level0 t vpn p2 p1 w0 /\
              mr !!! Regidx (mword_of_int 10) = pt_addr0 p1 vpn /\
              (m !! vpn = Some w0
               \/ (w0 = mword_of_int 0 /\ m !! vpn = None))) ⌝ -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros va vpn sp0 spr ret_tgt HK Hsp Hs6 Htp Hx23 Hx24 Hx25 Hx26 Hx27 Hmv.
    iIntros "Hcg #Htext Hpc
             Hc56 Hc48 Hc40 Hc32 Hc24 Hc16 Hc08 Hc00
             Hptree Hcont".
    iPoseProof (wi_72 with "Htext") as "Hi72".
    iPoseProof (wi_96 with "Htext") as "Hi96".
    iPoseProof (wi_98 with "Htext") as "Hi98".
    (* +0x72 beqz s6 TAKEN (alloc = 0) -> +0x96 *)
    iApply (wp_beqz_x0_taken_s_sconf (mword_of_int (KernelSyms.walk + 0x72)) (mword_of_int 36 : mword 13) (mword_of_int 22 : mword 5)
              Mf (K - 8)%nat b ltac:(vm_compute; discriminate) ltac:(rgne; exact Hs6)
              ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi72").
    iIntros (CIDa Hsa). iApply bi.later_intro. iIntros "Hcg Hpc".
    assert (Htgt96 : add_vec (mword_of_int (KernelSyms.walk + 0x72) : mword 64)
                       (sign_extend' 64 (mword_of_int 36 : mword 13))
                     = mword_of_int (KernelSyms.walk + 0x96)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgt96) in "Hpc".
    (* +0x96 c.li a0,0 *)
    iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.walk + 0x96)) (mword_of_int 10 : mword 5) (mword_of_int 0 : mword 6)
              (mword_of_int 0 : mword 64)
              Mf (K - 8)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc Hi96").
    iIntros (CIDb Hsb) "Hcg Hpc".
    set (F1 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg (mword_of_int 0 : mword 64)]> Mf).
    assert (Hpp98 : add_vec_int (mword_of_int (KernelSyms.walk + 0x96) : mword 64) 2 = mword_of_int (KernelSyms.walk + 0x98)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp98) in "Hpc".
    (* +0x98 c.j -> +0x52 *)
    iApply (wp_cj_s_sconf (mword_of_int (KernelSyms.walk + 0x98))
              (sign_extend' 21 (concat_vec (mword_of_int 2013 : mword 11) ('b"0")))
              F1 (K - 8)%nat b ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi98").
    iIntros (CIDc Hsc). iApply bi.later_intro. iIntros "Hcg Hpc".
    assert (Htgt52 : add_vec (mword_of_int (KernelSyms.walk + 0x98) : mword 64)
              (sign_extend' 64 (sign_extend' 21 (concat_vec (mword_of_int 2013 : mword 11) ('b"0"))))
            = mword_of_int (KernelSyms.walk + 0x52)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgt52) in "Hpc".
    assert (HspF1 : F1 !!! Regidx csp_rs1 = spr).
    { rewrite /F1. rewrite upd_ne; [| reg_neq]. exact Hsp. }
    assert (HF1x4 : F1 !!! Regidx (mword_of_int 4 : mword 5) = mm !!! Regidx (mword_of_int 4)).
    { rewrite /F1. rewrite upd_ne; [| reg_neq]. exact Htp. }
    assert (HF1x23 : F1 !!! Regidx (mword_of_int 23 : mword 5) = mm !!! Regidx (mword_of_int 23)).
    { rewrite /F1. rewrite upd_ne; [| reg_neq]. exact Hx23. }
    assert (HF1x24 : F1 !!! Regidx (mword_of_int 24 : mword 5) = mm !!! Regidx (mword_of_int 24)).
    { rewrite /F1. rewrite upd_ne; [| reg_neq]. exact Hx24. }
    assert (HF1x25 : F1 !!! Regidx (mword_of_int 25 : mword 5) = mm !!! Regidx (mword_of_int 25)).
    { rewrite /F1. rewrite upd_ne; [| reg_neq]. exact Hx25. }
    assert (HF1x26 : F1 !!! Regidx (mword_of_int 26 : mword 5) = mm !!! Regidx (mword_of_int 26)).
    { rewrite /F1. rewrite upd_ne; [| reg_neq]. exact Hx26. }
    assert (HF1x27 : F1 !!! Regidx (mword_of_int 27 : mword 5) = mm !!! Regidx (mword_of_int 27)).
    { rewrite /F1. rewrite upd_ne; [| reg_neq]. exact Hx27. }
    assert (HF1a0 : F1 !!! Regidx (mword_of_int 10 : mword 5) = mword_of_int 0).
    { rewrite /F1 upd_eq. reflexivity. }
    iApply (wp_wkn_epilogue mm F1 t m K dq b p HK HspF1 HF1x4
              HF1x23 HF1x24 HF1x25 HF1x26 HF1x27
              ltac:(left; split; [exact HF1a0 | exact Hmv])
              with "Hcg Htext Hpc
                    Hc56 Hc48 Hc40 Hc32 Hc24 Hc16 Hc08 Hc00
                    Hptree").
    iIntros (CIDd Hsd).
    iSpecialize ("Hcont" $! CIDd with "[%]"); [wp_next_chain|].
    iExact "Hcont".
  Qed.

  (* ================================================================= *)
  (* THE SHARED TAIL (+0x46..+0x50) then the epilogue.                   *)
  (* ================================================================= *)
  Local Lemma wp_wkn_tail `{CID0 : CpuId} 
      (mm Mf : regfile) (t : ptree) (m : gmap (mword 27) (mword 64))
      (b0 : mword 44) (K : nat) (dq : dfrac) (b : bool) (p : mword 64) :
    let va := mm !!! Regidx (mword_of_int 11) in
    let vpn := svpn_of va in
    let sp0 := mm !!! Regidx csp_rs1 in
    let spr := add_vec sp0 (sign_extend' 64 (caddi16sp_imm (mword_of_int 60 : mword 6))) in
    let ret_tgt := ret_pc (mm !!! Regidx (mword_of_int 1)) in
    (8 <= K)%nat ->
    uint va < 274877906944 ->
    Mf !!! Regidx csp_rs1 = spr ->
    Mf !!! Regidx (mword_of_int 19 : mword 5) = va ->
    Mf !!! Regidx (mword_of_int 9 : mword 5)
      = zero_extend' 64 (concat_vec b0 (zeros' 12 : mword 12)) ->
    Mf !!! Regidx (mword_of_int 4 : mword 5) = mm !!! Regidx (mword_of_int 4) ->
    Mf !!! Regidx (mword_of_int 23 : mword 5) = mm !!! Regidx (mword_of_int 23) ->
    Mf !!! Regidx (mword_of_int 24 : mword 5) = mm !!! Regidx (mword_of_int 24) ->
    Mf !!! Regidx (mword_of_int 25 : mword 5) = mm !!! Regidx (mword_of_int 25) ->
    Mf !!! Regidx (mword_of_int 26 : mword 5) = mm !!! Regidx (mword_of_int 26) ->
    Mf !!! Regidx (mword_of_int 27 : mword 5) = mm !!! Regidx (mword_of_int 27) ->
    (exists p2 p1 w0,
       ptree_level0 t vpn p2 p1 w0 /\
       pt_addr0 p1 vpn = u_pte_addr b0 (vpn_idx 0 vpn) /\
       (m !! vpn = Some w0 \/ (w0 = mword_of_int 0 /\ m !! vpn = None))) ->
    sie_cap_gpr kt Mf (K - 8)%nat b p -∗
    kernel_text -∗
    pc_is (mword_of_int (KernelSyms.walk + 0x46)) -∗
    pa_stk sp0 1 ↦₈ (mm !!! Regidx (mword_of_int 1)) -∗
    pa_stk sp0 2 ↦₈ (mm !!! Regidx (mword_of_int 8)) -∗
    pa_stk sp0 3 ↦₈ (mm !!! Regidx (mword_of_int 9)) -∗
    pa_stk sp0 4 ↦₈ (mm !!! Regidx (mword_of_int 18)) -∗
    pa_stk sp0 5 ↦₈ (mm !!! Regidx (mword_of_int 19)) -∗
    pa_stk sp0 6 ↦₈ (mm !!! Regidx (mword_of_int 20)) -∗
    pa_stk sp0 7 ↦₈ (mm !!! Regidx (mword_of_int 21)) -∗
    pa_stk sp0 8 ↦₈ (mm !!! Regidx (mword_of_int 22)) -∗
    ptree_own 2 dq t -∗
    wp_next b p (fun (CID : CpuId) =>
      ∀ (mr : regfile),
      sie_cap_gpr kt mr K b p -∗
      pc_is ret_tgt -∗
      ptree_own 2 dq t -∗
      ⌜callee_saved mm mr⌝ -∗
      ⌜ (mr !!! Regidx (mword_of_int 10) = mword_of_int 0 /\ m !! vpn = None)
        \/ (exists p2 p1 w0,
              ptree_level0 t vpn p2 p1 w0 /\
              mr !!! Regidx (mword_of_int 10) = pt_addr0 p1 vpn /\
              (m !! vpn = Some w0
               \/ (w0 = mword_of_int 0 /\ m !! vpn = None))) ⌝ -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros va vpn sp0 spr ret_tgt HK Hva' Hsp Hs3 Hs1 Htp Hx23 Hx24 Hx25 Hx26 Hx27 Hlvl.
    iIntros "Hcg #Htext Hpc
             Hc56 Hc48 Hc40 Hc32 Hc24 Hc16 Hc08 Hc00
             Hptree Hcont".
    iPoseProof (wi_46 with "Htext") as "Hi46".
    iPoseProof (wi_4a with "Htext") as "Hi4a".
    iPoseProof (wi_4e with "Htext") as "Hi4e".
    iPoseProof (wi_50 with "Htext") as "Hi50".
    (* +0x46 srli a0,s3,12 *)
    iApply (wp_srli4_s_sconf (mword_of_int (KernelSyms.walk + 0x46)) (mword_of_int 10 : mword 5) (mword_of_int 19 : mword 5) (mword_of_int 12 : mword 6)
              Mf (K - 8)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi46").
    iIntros (CID1 Hta) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (T1 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg
        (shift_bits_right (Mf !!! Regidx (mword_of_int 19 : mword 5)) (subrange_vec_dec (mword_of_int 12 : mword 6) (Z.sub log2_xlen 1) 0))]> Mf).
    assert (Hpp4a : add_vec_int (mword_of_int (KernelSyms.walk + 0x46) : mword 64) 4 = mword_of_int (KernelSyms.walk + 0x4a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp4a) in "Hpc".
    (* +0x4a andi a0,a0,511 *)
    iApply (wp_andi_s_sconf (mword_of_int (KernelSyms.walk + 0x4a)) (mword_of_int 10 : mword 5) (mword_of_int 10 : mword 5) (mword_of_int 511 : mword 12)
              (and_vec (shift_bits_right va (subrange_vec_dec (mword_of_int 12 : mword 6) (Z.sub log2_xlen 1) 0))
                       (sign_extend' 64 (mword_of_int 511 : mword 12)))
              T1 (K - 8)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(rgne; rewrite /T1 upd_eq; rewrite Hs3; reflexivity)
              with "Hcg Hpc Hi4a").
    iIntros (CID2 Htb) "Hcg Hpc".
    set (T2 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg
        (and_vec (shift_bits_right va (subrange_vec_dec (mword_of_int 12 : mword 6) (Z.sub log2_xlen 1) 0))
                 (sign_extend' 64 (mword_of_int 511 : mword 12)))]> T1).
    assert (Hpp4e : add_vec_int (mword_of_int (KernelSyms.walk + 0x4a) : mword 64) 4 = mword_of_int (KernelSyms.walk + 0x4e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp4e) in "Hpc".
    (* +0x4e c.slli a0,3 *)
    iApply (wp_cslli_s_sconf (mword_of_int (KernelSyms.walk + 0x4e)) (Regidx (mword_of_int 10 : mword 5)) (mword_of_int 10 : mword 5) (mword_of_int 3 : mword 6)
              T2 (K - 8)%nat b
              ltac:(reflexivity) ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi4e").
    iIntros (CID3 Htc) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (T3 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg
        (shift_bits_left (T2 !!! Regidx (mword_of_int 10 : mword 5)) (subrange_vec_dec (mword_of_int 3 : mword 6) (Z.sub log2_xlen 1) 0))]> T2).
    assert (Hpp50 : add_vec_int (mword_of_int (KernelSyms.walk + 0x4e) : mword 64) 2 = mword_of_int (KernelSyms.walk + 0x50)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp50) in "Hpc".
    (* +0x50 c.add a0,s1 *)
    iApply (wp_cadd_s_sconf (mword_of_int (KernelSyms.walk + 0x50)) (mword_of_int 10 : mword 5) (mword_of_int 9 : mword 5)
              T3 (K - 8)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi50").
    iIntros (CID4 Htd) "Hcg Hpc".
    iEval (repeat rgne) in "Hcg".
    set (T4 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg
        (add_vec (T3 !!! Regidx (mword_of_int 10 : mword 5)) (T3 !!! Regidx (mword_of_int 9 : mword 5)))]> T3).
    assert (Hpp52 : add_vec_int (mword_of_int (KernelSyms.walk + 0x50) : mword 64) 2 = mword_of_int (KernelSyms.walk + 0x52)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp52) in "Hpc".
    assert (HT2a0 : T2 !!! Regidx (mword_of_int 10 : mword 5)
        = and_vec (shift_bits_right va (subrange_vec_dec (mword_of_int 12 : mword 6) (Z.sub log2_xlen 1) 0))
                 (sign_extend' 64 (mword_of_int 511 : mword 12)))
      by (rewrite /T2 upd_eq; reflexivity).
    assert (HT3s1 : T3 !!! Regidx (mword_of_int 9 : mword 5)
                    = zero_extend' 64 (concat_vec b0 (zeros' 12 : mword 12))).
    { rewrite /T3 /T2 /T1.
      repeat (rewrite upd_ne; [| reg_neq]).
      exact Hs1. }
    assert (HT4a0 : T4 !!! Regidx (mword_of_int 10 : mword 5)
                    = u_pte_addr b0 (vpn_idx 0 vpn)).
    { rewrite /T4 upd_eq.
      rewrite {1}/T3 upd_eq.
      rewrite HT2a0 HT3s1.
      replace (subrange_vec_dec (mword_of_int 12 : mword 6) (Z.sub log2_xlen 1) 0)
        with (subrange_vec_dec (mword_of_int 12 : mword 64) (Z.sub log2_xlen 1) 0)
        by (apply bv_eq; vm_compute; reflexivity).
      exact (walk_slot_addr0 b0 va Hva'). }
    assert (HspT4 : T4 !!! Regidx csp_rs1 = spr).
    { rewrite /T4 /T3 /T2 /T1. repeat (rewrite upd_ne; [| reg_neq]). exact Hsp. }
    assert (HT4x4 : T4 !!! Regidx (mword_of_int 4 : mword 5) = mm !!! Regidx (mword_of_int 4)).
    { rewrite /T4 /T3 /T2 /T1. repeat (rewrite upd_ne; [| reg_neq]). exact Htp. }
    assert (HT4x23 : T4 !!! Regidx (mword_of_int 23 : mword 5) = mm !!! Regidx (mword_of_int 23)).
    { rewrite /T4 /T3 /T2 /T1. repeat (rewrite upd_ne; [| reg_neq]). exact Hx23. }
    assert (HT4x24 : T4 !!! Regidx (mword_of_int 24 : mword 5) = mm !!! Regidx (mword_of_int 24)).
    { rewrite /T4 /T3 /T2 /T1. repeat (rewrite upd_ne; [| reg_neq]). exact Hx24. }
    assert (HT4x25 : T4 !!! Regidx (mword_of_int 25 : mword 5) = mm !!! Regidx (mword_of_int 25)).
    { rewrite /T4 /T3 /T2 /T1. repeat (rewrite upd_ne; [| reg_neq]). exact Hx25. }
    assert (HT4x26 : T4 !!! Regidx (mword_of_int 26 : mword 5) = mm !!! Regidx (mword_of_int 26)).
    { rewrite /T4 /T3 /T2 /T1. repeat (rewrite upd_ne; [| reg_neq]). exact Hx26. }
    assert (HT4x27 : T4 !!! Regidx (mword_of_int 27 : mword 5) = mm !!! Regidx (mword_of_int 27)).
    { rewrite /T4 /T3 /T2 /T1. repeat (rewrite upd_ne; [| reg_neq]). exact Hx27. }
    assert (Hpay : (T4 !!! Regidx (mword_of_int 10 : mword 5) = mword_of_int 0 /\ m !! vpn = None)
      \/ (exists p2 p1 w0,
            ptree_level0 t vpn p2 p1 w0 /\
            T4 !!! Regidx (mword_of_int 10 : mword 5) = pt_addr0 p1 vpn /\
            (m !! vpn = Some w0 \/ (w0 = mword_of_int 0 /\ m !! vpn = None)))).
    { destruct Hlvl as (p2 & p1 & w0 & Hl0 & Heq & Hm0).
      right. exists p2, p1, w0.
      split; [exact Hl0 |].
      split; [rewrite HT4a0 Heq; reflexivity | exact Hm0]. }
    iApply (wp_wkn_epilogue mm T4 t m K dq b p HK HspT4 HT4x4
              HT4x23 HT4x24 HT4x25 HT4x26 HT4x27 Hpay
              with "Hcg Htext Hpc
                    Hc56 Hc48 Hc40 Hc32 Hc24 Hc16 Hc08 Hc00
                    Hptree").
    iIntros (CIDe Hte).
    iSpecialize ("Hcont" $! CIDe with "[%]"); [wp_next_chain|].
    iExact "Hcont".
  Qed.

  (* ================================================================= *)
  (* THE LOOP BODY'S STRAIGHT-LINE CORE (+0x26..+0x36).                 *)
  (* ================================================================= *)
  Local Lemma wp_wkn_probe `{CID0 : CpuId} 
      (M : regfile) (n : nat) (va shift : mword 64) (slotaddr pte : mword 64) (b : bool) (p : mword 64) {dqm : dfrac} :
    M !!! Regidx (mword_of_int 19 : mword 5) = va ->
    M !!! Regidx (mword_of_int 20 : mword 5) = shift ->
    add_vec
      (shift_bits_left
         (and_vec (shift_bits_right va (subrange_vec_dec shift (Z.sub log2_xlen 1) 0))
                  (sign_extend' 64 (mword_of_int 511 : mword 12)))
         (subrange_vec_dec (mword_of_int 3 : mword 6) (Z.sub log2_xlen 1) 0))
      (M !!! Regidx (mword_of_int 9 : mword 5)) = slotaddr ->
    sie_cap_gpr kt M n b p -∗
    kernel_text -∗
    pc_is (mword_of_int (KernelSyms.walk + 0x26)) -∗
    slotaddr ↦₈{dqm} pte -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr kt (<[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (and_vec pte (sign_extend' 64 (mword_of_int 1 : mword 12)))]>
                (<[Regidx (mword_of_int 9 : mword 5) := regval_into_reg pte]>
                 (<[Regidx (mword_of_int 18 : mword 5) := regval_into_reg slotaddr]> M))) n b p -∗
      pc_is (mword_of_int (KernelSyms.walk + 0x3a)) -∗
      slotaddr ↦₈{dqm} pte -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hs3 Hs4 Hslot.
    iIntros "Hcg #Htext Hpc Hown Hcont".
    iPoseProof (wi_26 with "Htext") as "Hi26".
    iPoseProof (wi_2a with "Htext") as "Hi2a".
    iPoseProof (wi_2e with "Htext") as "Hi2e".
    iPoseProof (wi_30 with "Htext") as "Hi30".
    iPoseProof (wi_32 with "Htext") as "Hi32".
    iPoseProof (wi_36 with "Htext") as "Hi36".
    (* +0x26 srl s2,s3,s4 *)
    iApply (wp_srl_s_sconf (mword_of_int (KernelSyms.walk + 0x26)) (mword_of_int 18 : mword 5) (mword_of_int 19 : mword 5) (mword_of_int 20 : mword 5)
              (shift_bits_right va (subrange_vec_dec shift (Z.sub log2_xlen 1) 0))
              M n b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(repeat rgne; rewrite Hs3 Hs4; reflexivity)
              with "Hcg Hpc Hi26").
    iIntros (CID1 Hpa) "Hcg Hpc".
    set (L1 := <[Regidx (mword_of_int 18 : mword 5) := regval_into_reg
        (shift_bits_right va (subrange_vec_dec shift (Z.sub log2_xlen 1) 0))]> M).
    assert (Hpp2a : add_vec_int (mword_of_int (KernelSyms.walk + 0x26) : mword 64) 4 = mword_of_int (KernelSyms.walk + 0x2a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp2a) in "Hpc".
    (* +0x2a andi s2,s2,511 *)
    iApply (wp_andi_s_sconf (mword_of_int (KernelSyms.walk + 0x2a)) (mword_of_int 18 : mword 5) (mword_of_int 18 : mword 5) (mword_of_int 511 : mword 12)
              (and_vec (shift_bits_right va (subrange_vec_dec shift (Z.sub log2_xlen 1) 0))
                       (sign_extend' 64 (mword_of_int 511 : mword 12)))
              L1 n b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(rgne; rewrite /L1 upd_eq; reflexivity)
              with "Hcg Hpc Hi2a").
    iIntros (CID2 Hpb) "Hcg Hpc".
    set (L2 := <[Regidx (mword_of_int 18 : mword 5) := regval_into_reg
        (and_vec (shift_bits_right va (subrange_vec_dec shift (Z.sub log2_xlen 1) 0))
                 (sign_extend' 64 (mword_of_int 511 : mword 12)))]> L1).
    assert (Hpp2e : add_vec_int (mword_of_int (KernelSyms.walk + 0x2a) : mword 64) 4 = mword_of_int (KernelSyms.walk + 0x2e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp2e) in "Hpc".
    (* +0x2e c.slli s2,3 *)
    iApply (wp_cslli_s_sconf (mword_of_int (KernelSyms.walk + 0x2e)) (Regidx (mword_of_int 18 : mword 5)) (mword_of_int 18 : mword 5) (mword_of_int 3 : mword 6)
              L2 n b
              ltac:(reflexivity) ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi2e").
    iIntros (CID3 Hpc') "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (L3 := <[Regidx (mword_of_int 18 : mword 5) := regval_into_reg
        (shift_bits_left (L2 !!! Regidx (mword_of_int 18 : mword 5)) (subrange_vec_dec (mword_of_int 3 : mword 6) (Z.sub log2_xlen 1) 0))]> L2).
    assert (Hpp30 : add_vec_int (mword_of_int (KernelSyms.walk + 0x2e) : mword 64) 2 = mword_of_int (KernelSyms.walk + 0x30)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp30) in "Hpc".
    (* +0x30 c.add s2,s1 *)
    iApply (wp_cadd_s_sconf (mword_of_int (KernelSyms.walk + 0x30)) (mword_of_int 18 : mword 5) (mword_of_int 9 : mword 5)
              L3 n b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi30").
    iIntros (CID4 Hpd) "Hcg Hpc".
    iEval (repeat rgne) in "Hcg".
    assert (Hpp32 : add_vec_int (mword_of_int (KernelSyms.walk + 0x30) : mword 64) 2 = mword_of_int (KernelSyms.walk + 0x32)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp32) in "Hpc".
    (* collapse s2's four writes (L1..L4, all reg18) to ONE insert over M *)
    set (L4 := <[Regidx (mword_of_int 18 : mword 5) := regval_into_reg slotaddr]> M).
    assert (H18 : L3 !!! Regidx (mword_of_int 18 : mword 5) =
        shift_bits_left (and_vec (shift_bits_right va (subrange_vec_dec shift (Z.sub log2_xlen 1) 0)) (sign_extend' 64 (mword_of_int 511 : mword 12)))
          (subrange_vec_dec (mword_of_int 3 : mword 6) (Z.sub log2_xlen 1) 0)).
    { rewrite /L3 upd_eq /L2 upd_eq. reflexivity. }
    assert (H9 : L3 !!! Regidx (mword_of_int 9 : mword 5) = M !!! Regidx (mword_of_int 9 : mword 5)).
    { rewrite /L3 /L2 /L1. do 3 (rewrite upd_ne; [| reg_neq]). reflexivity. }
    assert (HL4c : <[Regidx (mword_of_int 18 : mword 5) := regval_into_reg
        (add_vec (L3 !!! Regidx (mword_of_int 18 : mword 5)) (L3 !!! Regidx (mword_of_int 9 : mword 5)))]> L3 = L4).
    { rewrite H18 H9. rewrite /L4 /L3 /L2 /L1 !upd_upd. do 2 f_equal. exact Hslot. }
    iEval (rewrite HL4c) in "Hcg".
    assert (HL4s2 : L4 !!! Regidx (mword_of_int 18 : mword 5) = slotaddr)
      by (rewrite /L4 upd_eq; reflexivity).
    assert (Hea0 : forall X : mword 64, add_vec X (sign_extend' 64 (mword_of_int 0 : mword 12)) = X).
    { intro X.
      replace (sign_extend' 64 (mword_of_int 0 : mword 12) : mword 64)
        with (mword_of_int 0 : mword 64) by (apply bv_eq; vm_compute; reflexivity).
      apply kv_addv_zero. }
    (* +0x32 ld s1,0(s2) *)
    iApply (wp_ld_s_sconf (mword_of_int (KernelSyms.walk + 0x32)) (mword_of_int 9 : mword 5) (mword_of_int 18 : mword 5) (mword_of_int 0 : mword 12)
              L4 n pte b (dqm:=dqm)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi32 [Hown]").
    { iEval (rgne; rewrite Hea0 HL4s2). iExact "Hown". }
    iIntros (CID5 Hpe) "Hcg Hpc Hown".
    iEval (rgne; rewrite Hea0 HL4s2) in "Hown".
    set (L5 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg pte]> L4).
    assert (Hpp36 : add_vec_int (mword_of_int (KernelSyms.walk + 0x32) : mword 64) 4 = mword_of_int (KernelSyms.walk + 0x36)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp36) in "Hpc".
    (* +0x36 andi a5,s1,1 *)
    iApply (wp_andi_s_sconf (mword_of_int (KernelSyms.walk + 0x36)) (mword_of_int 15 : mword 5) (mword_of_int 9 : mword 5) (mword_of_int 1 : mword 12)
              (and_vec pte (sign_extend' 64 (mword_of_int 1 : mword 12)))
              L5 n b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(rgne; rewrite /L5 upd_eq; reflexivity)
              with "Hcg Hpc Hi36").
    iIntros (CID6 Hpf) "Hcg Hpc".
    assert (Hpp3a : add_vec_int (mword_of_int (KernelSyms.walk + 0x36) : mword 64) 4 = mword_of_int (KernelSyms.walk + 0x3a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp3a) in "Hpc".
    iSpecialize ("Hcont" $! CID6 with "[%]"); [wp_next_chain|].
    iApply ("Hcont" with "Hcg Hpc Hown").
  Qed.

  (* ================================================================= *)
  (* THE TOP-LEVEL walk(pagetable, va, 0) WP.                           *)
  (* ================================================================= *)
  Lemma wp_walk_noalloc_sconf
      (mm : regfile) (t : ptree)
      (m : gmap (mword 27) (mword 64)) (K : nat) (dq : dfrac) (b : bool) (p : mword 64)
    : wp_walk_noalloc_sconf_body kt mm t m K dq b p.
  Proof.
    cbv beta delta [wp_walk_noalloc_sconf_body].
    intros pcE va vpn ret_tgt HK Ha0 Ha2 Hva Hrep.
    pose (sp0 := (mm !!! Regidx csp_rs1 : mword 64)).
    set (spr := add_vec sp0 (sign_extend' 64 (caddi16sp_imm (mword_of_int 60 : mword 6)))).
    set (W1 := <[Regidx csp_rs1 := regval_into_reg
        (add_vec (mm !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 60 : mword 6))))]> mm).
    iIntros "Hcg #Htext Hpc Hptree Hcont".
    assert (HpcE : pcE = (mword_of_int KernelSyms.walk : mword 64)) by reflexivity.
    iEval (rewrite HpcE) in "Hpc".
    assert (Hb1 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 7 : mword 6) ('b"000"))) = pa_stk sp0 1).
    { unfold spr, pa_stk, add_vec_int. rewrite !pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb2 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 6 : mword 6) ('b"000"))) = pa_stk sp0 2).
    { unfold spr, pa_stk, add_vec_int. rewrite !pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb3 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000"))) = pa_stk sp0 3).
    { unfold spr, pa_stk, add_vec_int. rewrite !pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb4 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000"))) = pa_stk sp0 4).
    { unfold spr, pa_stk, add_vec_int. rewrite !pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb5 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000"))) = pa_stk sp0 5).
    { unfold spr, pa_stk, add_vec_int. rewrite !pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb6 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000"))) = pa_stk sp0 6).
    { unfold spr, pa_stk, add_vec_int. rewrite !pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb7 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) = pa_stk sp0 7).
    { unfold spr, pa_stk, add_vec_int. rewrite !pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb8 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000"))) = pa_stk sp0 8).
    { unfold spr, pa_stk, add_vec_int. rewrite !pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    iPoseProof (wi_00 with "Htext") as "Hi00".
    iPoseProof (wi_02 with "Htext") as "Hi02".
    iPoseProof (wi_04 with "Htext") as "Hi04".
    iPoseProof (wi_06 with "Htext") as "Hi06".
    iPoseProof (wi_08 with "Htext") as "Hi08".
    iPoseProof (wi_0a with "Htext") as "Hi0a".
    iPoseProof (wi_0c with "Htext") as "Hi0c".
    iPoseProof (wi_0e with "Htext") as "Hi0e".
    iPoseProof (wi_10 with "Htext") as "Hi10".
    iPoseProof (wi_12 with "Htext") as "Hi12".
    iPoseProof (wi_14 with "Htext") as "Hi14".
    iPoseProof (wi_16 with "Htext") as "Hi16".
    iPoseProof (wi_18 with "Htext") as "Hi18".
    iPoseProof (wi_1a with "Htext") as "Hi1a".
    iPoseProof (wi_1c with "Htext") as "Hi1c".
    iPoseProof (wi_1e with "Htext") as "Hi1e".
    iPoseProof (wi_20 with "Htext") as "Hi20".
    iPoseProof (wi_22 with "Htext") as "Hi22".
    (* +0x00 c.addi16sp sp,-64 : the 8-slot frame push *)
    assert (Hpush : add_vec (mm !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 60 : mword 6))) = pa_stk (mm !!! Regidx csp_rs1) 8).
    { unfold pa_stk, add_vec_int. apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    iApply (wp_caddi16sp_push_s_sconf (mword_of_int KernelSyms.walk) (mword_of_int 60 : mword 6) mm K 8 b ltac:(lia) Hpush
              with "Hcg Hpc Hi00").
    iIntros (CID1 Hw1) "Hcg Hframe Hpc".
    change (<[Regidx csp_rs1 := regval_into_reg
        (add_vec (mm !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 60 : mword 6))))]> mm) with W1.
    iEval (rewrite (stack_own_slots (KTR := kt)); cbn [seq]) in "Hframe".
    iDestruct "Hframe" as "(S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & _)".
    iDestruct "S1" as (v56) "Hc56". iDestruct "S2" as (v48) "Hc48".
    iDestruct "S3" as (v40) "Hc40". iDestruct "S4" as (v32) "Hc32".
    iDestruct "S5" as (v24) "Hc24". iDestruct "S6" as (v16) "Hc16".
    iDestruct "S7" as (v08) "Hc08". iDestruct "S8" as (v00) "Hc00".
    assert (HspW1 : W1 !!! Regidx csp_rs1 = spr)
      by (rewrite /W1 upd_eq; reflexivity).
    assert (Hpp02 : add_vec_int (mword_of_int KernelSyms.walk : mword 64) 2 = mword_of_int (KernelSyms.walk + 0x02)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp02) in "Hpc".
    (* +0x02 c.sdsp x1,56(sp) *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.walk + 0x02)) (mword_of_int 7 : mword 6) (mword_of_int 1 : mword 5)
              W1 (K - 8)%nat v56 b with "Hcg Hpc Hi02 [Hc56]").
    { iEval (rewrite HspW1 Hb1). iExact "Hc56". }
    iIntros (CID2 Hw2) "Hcg Hpc Hc56".
    assert (Hpp04 : add_vec_int (mword_of_int (KernelSyms.walk + 0x02) : mword 64) 2 = mword_of_int (KernelSyms.walk + 0x04)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp04) in "Hpc".
    (* +0x04 c.sdsp x8,48(sp) *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.walk + 0x04)) (mword_of_int 6 : mword 6) (mword_of_int 8 : mword 5)
              W1 (K - 8)%nat v48 b with "Hcg Hpc Hi04 [Hc48]").
    { iEval (rewrite HspW1 Hb2). iExact "Hc48". }
    iIntros (CID3 Hw3) "Hcg Hpc Hc48".
    assert (Hpp06 : add_vec_int (mword_of_int (KernelSyms.walk + 0x04) : mword 64) 2 = mword_of_int (KernelSyms.walk + 0x06)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp06) in "Hpc".
    (* +0x06 c.sdsp x9,40(sp) *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.walk + 0x06)) (mword_of_int 5 : mword 6) (mword_of_int 9 : mword 5)
              W1 (K - 8)%nat v40 b with "Hcg Hpc Hi06 [Hc40]").
    { iEval (rewrite HspW1 Hb3). iExact "Hc40". }
    iIntros (CID4 Hw4) "Hcg Hpc Hc40".
    assert (Hpp08 : add_vec_int (mword_of_int (KernelSyms.walk + 0x06) : mword 64) 2 = mword_of_int (KernelSyms.walk + 0x08)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp08) in "Hpc".
    (* +0x08 c.sdsp x18,32(sp) *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.walk + 0x08)) (mword_of_int 4 : mword 6) (mword_of_int 18 : mword 5)
              W1 (K - 8)%nat v32 b with "Hcg Hpc Hi08 [Hc32]").
    { iEval (rewrite HspW1 Hb4). iExact "Hc32". }
    iIntros (CID5 Hw5) "Hcg Hpc Hc32".
    assert (Hpp0a : add_vec_int (mword_of_int (KernelSyms.walk + 0x08) : mword 64) 2 = mword_of_int (KernelSyms.walk + 0x0a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0a) in "Hpc".
    (* +0x0a c.sdsp x19,24(sp) *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.walk + 0x0a)) (mword_of_int 3 : mword 6) (mword_of_int 19 : mword 5)
              W1 (K - 8)%nat v24 b with "Hcg Hpc Hi0a [Hc24]").
    { iEval (rewrite HspW1 Hb5). iExact "Hc24". }
    iIntros (CID6 Hw6) "Hcg Hpc Hc24".
    assert (Hpp0c : add_vec_int (mword_of_int (KernelSyms.walk + 0x0a) : mword 64) 2 = mword_of_int (KernelSyms.walk + 0x0c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0c) in "Hpc".
    (* +0x0c c.sdsp x20,16(sp) *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.walk + 0x0c)) (mword_of_int 2 : mword 6) (mword_of_int 20 : mword 5)
              W1 (K - 8)%nat v16 b with "Hcg Hpc Hi0c [Hc16]").
    { iEval (rewrite HspW1 Hb6). iExact "Hc16". }
    iIntros (CID7 Hw7) "Hcg Hpc Hc16".
    assert (Hpp0e : add_vec_int (mword_of_int (KernelSyms.walk + 0x0c) : mword 64) 2 = mword_of_int (KernelSyms.walk + 0x0e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0e) in "Hpc".
    (* +0x0e c.sdsp x21,8(sp) *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.walk + 0x0e)) (mword_of_int 1 : mword 6) (mword_of_int 21 : mword 5)
              W1 (K - 8)%nat v08 b with "Hcg Hpc Hi0e [Hc08]").
    { iEval (rewrite HspW1 Hb7). iExact "Hc08". }
    iIntros (CID8 Hw8) "Hcg Hpc Hc08".
    assert (Hpp10 : add_vec_int (mword_of_int (KernelSyms.walk + 0x0e) : mword 64) 2 = mword_of_int (KernelSyms.walk + 0x10)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp10) in "Hpc".
    (* +0x10 c.sdsp x22,0(sp) *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.walk + 0x10)) (mword_of_int 0 : mword 6) (mword_of_int 22 : mword 5)
              W1 (K - 8)%nat v00 b with "Hcg Hpc Hi10 [Hc00]").
    { iEval (rewrite HspW1 Hb8). iExact "Hc00". }
    iIntros (CID9 Hw9) "Hcg Hpc Hc00".
    assert (Hpp12 : add_vec_int (mword_of_int (KernelSyms.walk + 0x10) : mword 64) 2 = mword_of_int (KernelSyms.walk + 0x12)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp12) in "Hpc".
    (* +0x12 c.addi4spn s0,sp,64 *)
    iApply (wp_caddi4spn_s_sconf (mword_of_int (KernelSyms.walk + 0x12)) (Cregidx (mword_of_int 0)) (mword_of_int 16 : mword 8) (mword_of_int 8 : mword 5)
              W1 (K - 8)%nat b ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi12").
    iIntros (CID10 Hw10) "Hcg Hpc".
    set (W2 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg
        (add_vec (W1 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 16 : mword 8))))]> W1).
    assert (Hpp14 : add_vec_int (mword_of_int (KernelSyms.walk + 0x12) : mword 64) 2 = mword_of_int (KernelSyms.walk + 0x14)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp14) in "Hpc".
    (* +0x14 c.mv x9,x10 *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.walk + 0x14)) (mword_of_int 9 : mword 5) (mword_of_int 10 : mword 5)
              W2 (K - 8)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi14").
    iIntros (CID11 Hw11) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (W3 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg
        (add_vec zero_reg (W2 !!! Regidx (mword_of_int 10 : mword 5)))]> W2).
    assert (Hpp16 : add_vec_int (mword_of_int (KernelSyms.walk + 0x14) : mword 64) 2 = mword_of_int (KernelSyms.walk + 0x16)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp16) in "Hpc".
    (* +0x16 c.mv x19,x11 *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.walk + 0x16)) (mword_of_int 19 : mword 5) (mword_of_int 11 : mword 5)
              W3 (K - 8)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi16").
    iIntros (CID12 Hw12) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (W4 := <[Regidx (mword_of_int 19 : mword 5) := regval_into_reg
        (add_vec zero_reg (W3 !!! Regidx (mword_of_int 11 : mword 5)))]> W3).
    assert (Hpp18 : add_vec_int (mword_of_int (KernelSyms.walk + 0x16) : mword 64) 2 = mword_of_int (KernelSyms.walk + 0x18)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp18) in "Hpc".
    (* +0x18 c.mv x22,x12 *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.walk + 0x18)) (mword_of_int 22 : mword 5) (mword_of_int 12 : mword 5)
              W4 (K - 8)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi18").
    iIntros (CID13 Hw13) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (W5 := <[Regidx (mword_of_int 22 : mword 5) := regval_into_reg
        (add_vec zero_reg (W4 !!! Regidx (mword_of_int 12 : mword 5)))]> W4).
    assert (Hpp1a : add_vec_int (mword_of_int (KernelSyms.walk + 0x18) : mword 64) 2 = mword_of_int (KernelSyms.walk + 0x1a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp1a) in "Hpc".
    (* +0x1a c.li a5,-1 *)
    iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.walk + 0x1a)) (mword_of_int 15 : mword 5) (mword_of_int 63 : mword 6)
              (add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 63 : mword 6))))
              W5 (K - 8)%nat b ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(reflexivity)
              with "Hcg Hpc Hi1a").
    iIntros (CID14 Hw14) "Hcg Hpc".
    set (W6 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg
        (add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 63 : mword 6))))]> W5).
    assert (Hpp1c : add_vec_int (mword_of_int (KernelSyms.walk + 0x1a) : mword 64) 2 = mword_of_int (KernelSyms.walk + 0x1c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp1c) in "Hpc".
    (* +0x1c c.srli a5,26 *)
    iApply (wp_csrli_s_sconf (mword_of_int (KernelSyms.walk + 0x1c)) (Cregidx (mword_of_int 7)) (mword_of_int 15 : mword 5) (mword_of_int 26 : mword 6)
              W6 (K - 8)%nat b ltac:(reflexivity) ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi1c").
    iIntros (CID15 Hw15) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (W7 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg
        (shift_bits_right (W6 !!! Regidx (mword_of_int 15 : mword 5)) (subrange_vec_dec (mword_of_int 26 : mword 6) (Z.sub log2_xlen 1) 0))]> W6).
    assert (Hpp1e : add_vec_int (mword_of_int (KernelSyms.walk + 0x1c) : mword 64) 2 = mword_of_int (KernelSyms.walk + 0x1e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp1e) in "Hpc".
    (* +0x1e c.li s4,30 *)
    iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.walk + 0x1e)) (mword_of_int 20 : mword 5) (mword_of_int 30 : mword 6)
              (add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 30 : mword 6))))
              W7 (K - 8)%nat b ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(reflexivity)
              with "Hcg Hpc Hi1e").
    iIntros (CID16 Hw16) "Hcg Hpc".
    set (W8 := <[Regidx (mword_of_int 20 : mword 5) := regval_into_reg
        (add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 30 : mword 6))))]> W7).
    assert (Hpp20 : add_vec_int (mword_of_int (KernelSyms.walk + 0x1e) : mword 64) 2 = mword_of_int (KernelSyms.walk + 0x20)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp20) in "Hpc".
    (* +0x20 c.li s5,12 *)
    iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.walk + 0x20)) (mword_of_int 21 : mword 5) (mword_of_int 12 : mword 6)
              (add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 12 : mword 6))))
              W8 (K - 8)%nat b ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(reflexivity)
              with "Hcg Hpc Hi20").
    iIntros (CID17 Hw17) "Hcg Hpc".
    set (W9 := <[Regidx (mword_of_int 21 : mword 5) := regval_into_reg
        (add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 12 : mword 6))))]> W8).
    assert (Hpp22 : add_vec_int (mword_of_int (KernelSyms.walk + 0x20) : mword 64) 2 = mword_of_int (KernelSyms.walk + 0x22)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp22) in "Hpc".
    assert (Hva' : uint va < 274877906944) by (change 274877906944 with (2 ^ 38); exact Hva).
    assert (HW9va : W9 !!! Regidx (mword_of_int 11 : mword 5) = va).
    { peel_reg. }
    assert (HW6a5 : W6 !!! Regidx (mword_of_int 15 : mword 5)
                    = (mword_of_int 18446744073709551615 : mword 64)).
    { rewrite /W6 upd_eq. apply bv_eq; vm_compute; reflexivity. }
    assert (HW9a5 : W9 !!! Regidx (mword_of_int 15 : mword 5) = mword_of_int 274877906943).
    { rewrite /W9 /W8.
      repeat (rewrite upd_ne; [| reg_neq]).
      rewrite /W7 upd_eq. rewrite HW6a5.
      apply bv_eq; vm_compute; reflexivity. }
    (* +0x22 bltu a5,a1 FALLS (the panic arm is dead under [uint va < 2^38]) *)
    iApply (wp_bltu_fall_s_sconf (mword_of_int (KernelSyms.walk + 0x22)) (mword_of_int 68 : mword 13) (mword_of_int 11 : mword 5) (mword_of_int 15 : mword 5)
              W9 (K - 8)%nat b ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              ltac:(repeat rgne; rewrite HW9a5 HW9va; unfold zopz0zI_u; apply Z.ltb_ge;
                    replace (uint (mword_of_int 274877906943 : mword 64)) with 274877906943 by (vm_compute; reflexivity);
                    lia)
              with "Hcg Hpc Hi22").
    iIntros (CID18 Hw18) "Hcg Hpc".
    assert (Hpp26 : add_vec_int (mword_of_int (KernelSyms.walk + 0x22) : mword 64) 4 = mword_of_int (KernelSyms.walk + 0x26)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp26) in "Hpc".
    (* ---- rebase the eight frame cells onto [pa_stk sp0 k] with mm's values ----
       [Hc56]..[Hc00] were handed back by the csdsp leaves as [pa ↦₈ (rget W1 k)]
       (the sdsp leaf's [storeval] is [rget]-spelled now, see ProofKvmmap.v's
       identical comment); [rgne] bridges each down to the plain [!!!] form the
       [HW1rK] facts below are stated at. *)
    iEval (rgne) in "Hc56".
    assert (HW1r1 : W1 !!! Regidx (mword_of_int 1 : mword 5) = mm !!! Regidx (mword_of_int 1)).
    { rewrite /W1. rewrite upd_ne; [reflexivity | vm_compute; discriminate]. }
    iEval (rewrite HW1r1) in "Hc56".
    iEval (rgne) in "Hc48".
    assert (HW1r8 : W1 !!! Regidx (mword_of_int 8 : mword 5) = mm !!! Regidx (mword_of_int 8)).
    { rewrite /W1. rewrite upd_ne; [reflexivity | vm_compute; discriminate]. }
    iEval (rewrite HW1r8) in "Hc48".
    iEval (rgne) in "Hc40".
    assert (HW1r9 : W1 !!! Regidx (mword_of_int 9 : mword 5) = mm !!! Regidx (mword_of_int 9)).
    { rewrite /W1. rewrite upd_ne; [reflexivity | vm_compute; discriminate]. }
    iEval (rewrite HW1r9) in "Hc40".
    iEval (rgne) in "Hc32".
    assert (HW1r18 : W1 !!! Regidx (mword_of_int 18 : mword 5) = mm !!! Regidx (mword_of_int 18)).
    { rewrite /W1. rewrite upd_ne; [reflexivity | vm_compute; discriminate]. }
    iEval (rewrite HW1r18) in "Hc32".
    iEval (rgne) in "Hc24".
    assert (HW1r19 : W1 !!! Regidx (mword_of_int 19 : mword 5) = mm !!! Regidx (mword_of_int 19)).
    { rewrite /W1. rewrite upd_ne; [reflexivity | vm_compute; discriminate]. }
    iEval (rewrite HW1r19) in "Hc24".
    iEval (rgne) in "Hc16".
    assert (HW1r20 : W1 !!! Regidx (mword_of_int 20 : mword 5) = mm !!! Regidx (mword_of_int 20)).
    { rewrite /W1. rewrite upd_ne; [reflexivity | vm_compute; discriminate]. }
    iEval (rewrite HW1r20) in "Hc16".
    iEval (rgne) in "Hc08".
    assert (HW1r21 : W1 !!! Regidx (mword_of_int 21 : mword 5) = mm !!! Regidx (mword_of_int 21)).
    { rewrite /W1. rewrite upd_ne; [reflexivity | vm_compute; discriminate]. }
    iEval (rewrite HW1r21) in "Hc08".
    iEval (rgne) in "Hc00".
    assert (HW1r22 : W1 !!! Regidx (mword_of_int 22 : mword 5) = mm !!! Regidx (mword_of_int 22)).
    { rewrite /W1. rewrite upd_ne; [reflexivity | vm_compute; discriminate]. }
    iEval (rewrite HW1r22) in "Hc00".
    iEval (rewrite HspW1 Hb1) in "Hc56".
    iEval (rewrite HspW1 Hb2) in "Hc48".
    iEval (rewrite HspW1 Hb3) in "Hc40".
    iEval (rewrite HspW1 Hb4) in "Hc32".
    iEval (rewrite HspW1 Hb5) in "Hc24".
    iEval (rewrite HspW1 Hb6) in "Hc16".
    iEval (rewrite HspW1 Hb7) in "Hc08".
    iEval (rewrite HspW1 Hb8) in "Hc00".
    (* ---- the loop-head register facts ---- *)
    assert (HspW9 : W9 !!! Regidx csp_rs1 = spr).
    { rewrite /W9 /W8 /W7 /W6 /W5 /W4 /W3 /W2. repeat (rewrite upd_ne; [| reg_neq]). exact HspW1. }
    assert (HW9s3 : W9 !!! Regidx (mword_of_int 19 : mword 5) = va).
    { rewrite /W9 /W8 /W7 /W6 /W5.
      repeat (rewrite upd_ne; [| reg_neq]).
      rewrite /W4 upd_eq.
      rewrite /W3 /W2 /W1.
      repeat (rewrite upd_ne; [| reg_neq]).
      rewrite add_vec_zero_l. reflexivity. }
    assert (HW9s4 : W9 !!! Regidx (mword_of_int 20 : mword 5) = (mword_of_int 30 : mword 64)).
    { rewrite /W9. rewrite upd_ne; [| reg_neq].
      rewrite /W8 upd_eq. apply bv_eq; vm_compute; reflexivity. }
    assert (HW9s5 : W9 !!! Regidx (mword_of_int 21 : mword 5) = mword_of_int 12).
    { rewrite /W9 upd_eq. apply bv_eq; vm_compute; reflexivity. }
    assert (HW9s1 : W9 !!! Regidx (mword_of_int 9 : mword 5)
                    = zero_extend' 64 (concat_vec (pt_base t) (zeros' 12 : mword 12))).
    { rewrite /W9 /W8 /W7 /W6 /W5 /W4.
      repeat (rewrite upd_ne; [| reg_neq]).
      rewrite /W3 upd_eq.
      rewrite /W2 /W1.
      repeat (rewrite upd_ne; [| reg_neq]).
      rewrite add_vec_zero_l. rewrite Ha0. reflexivity. }
    assert (HW9s6 : eq_vec (W9 !!! Regidx (mword_of_int 22 : mword 5)) zero_reg = true).
    { rewrite /W9 /W8 /W7 /W6 /W5. repeat (rewrite upd_ne; [| reg_neq]). rewrite upd_eq.
      rewrite /W4 /W3 /W2 /W1. repeat (rewrite upd_ne; [| reg_neq]). rewrite Ha2.
      vm_compute; reflexivity. }
    assert (HW9x4 : W9 !!! Regidx (mword_of_int 4 : mword 5) = mm !!! Regidx (mword_of_int 4)).
    { rewrite /W9 /W8 /W7 /W6 /W5 /W4 /W3 /W2 /W1. repeat (rewrite upd_ne; [| reg_neq]). reflexivity. }
    assert (HW9x23 : W9 !!! Regidx (mword_of_int 23 : mword 5) = mm !!! Regidx (mword_of_int 23)).
    { rewrite /W9 /W8 /W7 /W6 /W5 /W4 /W3 /W2 /W1. repeat (rewrite upd_ne; [| reg_neq]). reflexivity. }
    assert (HW9x24 : W9 !!! Regidx (mword_of_int 24 : mword 5) = mm !!! Regidx (mword_of_int 24)).
    { rewrite /W9 /W8 /W7 /W6 /W5 /W4 /W3 /W2 /W1. repeat (rewrite upd_ne; [| reg_neq]). reflexivity. }
    assert (HW9x25 : W9 !!! Regidx (mword_of_int 25 : mword 5) = mm !!! Regidx (mword_of_int 25)).
    { rewrite /W9 /W8 /W7 /W6 /W5 /W4 /W3 /W2 /W1. repeat (rewrite upd_ne; [| reg_neq]). reflexivity. }
    assert (HW9x26 : W9 !!! Regidx (mword_of_int 26 : mword 5) = mm !!! Regidx (mword_of_int 26)).
    { rewrite /W9 /W8 /W7 /W6 /W5 /W4 /W3 /W2 /W1. repeat (rewrite upd_ne; [| reg_neq]). reflexivity. }
    assert (HW9x27 : W9 !!! Regidx (mword_of_int 27 : mword 5) = mm !!! Regidx (mword_of_int 27)).
    { rewrite /W9 /W8 /W7 /W6 /W5 /W4 /W3 /W2 /W1. repeat (rewrite upd_ne; [| reg_neq]). reflexivity. }
    iPoseProof (wi_3a with "Htext") as "Hi3a".
    iPoseProof (wi_3c with "Htext") as "Hi3c".
    iPoseProof (wi_3e with "Htext") as "Hi3e".
    iPoseProof (wi_40 with "Htext") as "Hi40".
    iPoseProof (wi_42 with "Htext") as "Hi42".
    (* ================= LOOP ITERATION 1 (s4 = 30, level 2) ============ *)
    (* the L2 slot cell: owned PHYSICALLY inside [ptree_own], read THROUGH
       translation, so convert with the node's own identity claim. *)
    iDestruct (ptree_own_node_claim 1 dq t with "Hptree") as "[#Hcl2 Hptree]".
    iDestruct (ptree_own_cell_ro 1 dq t (vpn_idx 2 vpn) with "Hptree") as "[Hslot Hback2]".
    iDestruct (pt_slot_phys_to_mem (pt_base t) (vpn_idx 2 vpn) dq
                 (pt_ents t (vpn_idx 2 vpn)) with "Hcl2 Hslot") as "Hslot".
    iApply (wp_wkn_probe W9 (K - 8)%nat va (mword_of_int 30 : mword 64)
              (u_pte_addr (pt_base t) (vpn_idx 2 vpn)) (pt_ents t (vpn_idx 2 vpn)) b p
              (dqm:=dq) HW9s3 HW9s4
              ltac:(rewrite HW9s1; exact (walk_slot_addr2 (pt_base t) va Hva'))
              with "Hcg Htext Hpc Hslot").
    iIntros (CID19 Hw19) "Hcg Hpc Hslot".
    iDestruct (pt_slot_mem_to_phys (pt_base t) (vpn_idx 2 vpn) dq
                 (pt_ents t (vpn_idx 2 vpn)) with "Hcl2 Hslot") as "Hslot".
    iDestruct ("Hback2" with "Hslot") as "Hptree".
    set (pte2 := pt_ents t (vpn_idx 2 vpn)).
    set (M4 := <[Regidx (mword_of_int 18 : mword 5) := regval_into_reg (u_pte_addr (pt_base t) (vpn_idx 2 vpn))]> W9).
    set (M5 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg pte2]> M4).
    set (M6 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (and_vec pte2 (sign_extend' 64 (mword_of_int 1 : mword 12)))]> M5).
    assert (HM6a5 : M6 !!! Regidx (mword_of_int 15 : mword 5) = and_vec pte2 (sign_extend' 64 (mword_of_int 1 : mword 12)))
      by (rewrite /M6 upd_eq; reflexivity).
    assert (HM6s1 : M6 !!! Regidx (mword_of_int 9 : mword 5) = pte2).
    { rewrite /M6. rewrite upd_ne; [| reg_neq]. rewrite /M5 upd_eq. reflexivity. }
    assert (HspM6 : M6 !!! Regidx csp_rs1 = spr).
    { rewrite /M6 /M5 /M4. repeat (rewrite upd_ne; [| reg_neq]). exact HspW9. }
    assert (HM6s6 : eq_vec (M6 !!! Regidx (mword_of_int 22 : mword 5)) zero_reg = true).
    { rewrite /M6 /M5 /M4. repeat (rewrite upd_ne; [| reg_neq]). exact HW9s6. }
    assert (HM6x4 : M6 !!! Regidx (mword_of_int 4 : mword 5) = mm !!! Regidx (mword_of_int 4)).
    { rewrite /M6 /M5 /M4. repeat (rewrite upd_ne; [| reg_neq]). exact HW9x4. }
    assert (HM6x23 : M6 !!! Regidx (mword_of_int 23 : mword 5) = mm !!! Regidx (mword_of_int 23)).
    { rewrite /M6 /M5 /M4. repeat (rewrite upd_ne; [| reg_neq]). exact HW9x23. }
    assert (HM6x24 : M6 !!! Regidx (mword_of_int 24 : mword 5) = mm !!! Regidx (mword_of_int 24)).
    { rewrite /M6 /M5 /M4. repeat (rewrite upd_ne; [| reg_neq]). exact HW9x24. }
    assert (HM6x25 : M6 !!! Regidx (mword_of_int 25 : mword 5) = mm !!! Regidx (mword_of_int 25)).
    { rewrite /M6 /M5 /M4. repeat (rewrite upd_ne; [| reg_neq]). exact HW9x25. }
    assert (HM6x26 : M6 !!! Regidx (mword_of_int 26 : mword 5) = mm !!! Regidx (mword_of_int 26)).
    { rewrite /M6 /M5 /M4. repeat (rewrite upd_ne; [| reg_neq]). exact HW9x26. }
    assert (HM6x27 : M6 !!! Regidx (mword_of_int 27 : mword 5) = mm !!! Regidx (mword_of_int 27)).
    { rewrite /M6 /M5 /M4. repeat (rewrite upd_ne; [| reg_neq]). exact HW9x27. }
    destruct (wkn_case t m vpn Hrep) as
      [ (Hk2 & Hz2 & Hmv)
      | (c1 & Hk2 & Hv2 & Hp2 & Hb12 & Hnext) ].
    { (* ===== V=0 at level 2: beqz taken -> the alloc=0 arm ===== *)
      assert (Hvbit0 : Z.testbit (bv_unsigned pte2) 0 = false).
      { rewrite /pte2 Hz2.
        replace (bv_unsigned (mword_of_int 0 : mword 64)) with 0 by (vm_compute; reflexivity).
        apply Z.bits_0. }
      iApply (wp_cbeqz_taken_s_sconf (mword_of_int (KernelSyms.walk + 0x3a)) (mword_of_int 28 : mword 8) (Cregidx (mword_of_int 7)) (mword_of_int 15 : mword 5)
                M6 (K - 8)%nat b ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                ltac:(rgne; rewrite HM6a5 walk_vbit_eq Hvbit0; reflexivity)
                ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi3a").
      iApply bi.later_intro. iIntros (CID20 Hw20) "Hcg Hpc".
      assert (Htgt72 : add_vec (mword_of_int (KernelSyms.walk + 0x3a) : mword 64) (sign_extend' 64 (sign_extend' 13 (concat_vec (mword_of_int 28 : mword 8) ('b"0")))) = mword_of_int (KernelSyms.walk + 0x72)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Htgt72) in "Hpc".
      iApply (wp_wkn_fail mm M6 t m K dq b p HK HspM6 HM6s6 HM6x4
                HM6x23 HM6x24 HM6x25 HM6x26 HM6x27 Hmv
                with "Hcg Htext Hpc
                      Hc56 Hc48 Hc40 Hc32 Hc24 Hc16 Hc08 Hc00
                      Hptree").
      iIntros (CIDf1 Hwf1).
      iSpecialize ("Hcont" $! CIDf1 with "[%]"); [wp_next_chain|].
      iExact "Hcont". }
    (* ===== V=1 at level 2: descend into c1 ===== *)
    assert (Hvbit2 : Z.testbit (bv_unsigned pte2) 0 = true).
    { destruct (Z.testbit (bv_unsigned pte2) 0) eqn:E; [reflexivity | exfalso].
      exact (pte_valid_invalid_excl pte2 Hv2 (pte_invalid_bit0 _ E)). }
    (* +0x3a c.beqz a5 FALLS *)
    iApply (wp_cbeqz_fall_s_sconf (mword_of_int (KernelSyms.walk + 0x3a)) (mword_of_int 28 : mword 8) (Cregidx (mword_of_int 7)) (mword_of_int 15 : mword 5)
              M6 (K - 8)%nat b ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
              ltac:(rgne; rewrite HM6a5 walk_vbit_eq Hvbit2; reflexivity)
              with "Hcg Hpc Hi3a").
    iIntros (CID21 Hw21) "Hcg Hpc".
    assert (Hpp3c : add_vec_int (mword_of_int (KernelSyms.walk + 0x3a) : mword 64) 2 = mword_of_int (KernelSyms.walk + 0x3c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp3c) in "Hpc".
    (* +0x3c c.srli s1,10 *)
    iApply (wp_csrli_s_sconf (mword_of_int (KernelSyms.walk + 0x3c)) (Cregidx (mword_of_int 1)) (mword_of_int 9 : mword 5) (mword_of_int 10 : mword 6)
              M6 (K - 8)%nat b ltac:(reflexivity) ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi3c").
    iIntros (CID22 Hw22) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (M7 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (shift_bits_right (M6 !!! Regidx (mword_of_int 9 : mword 5)) (subrange_vec_dec (mword_of_int 10 : mword 6) (Z.sub log2_xlen 1) 0))]> M6).
    assert (Hpp3e : add_vec_int (mword_of_int (KernelSyms.walk + 0x3c) : mword 64) 2 = mword_of_int (KernelSyms.walk + 0x3e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp3e) in "Hpc".
    (* +0x3e c.slli s1,12 *)
    iApply (wp_cslli_s_sconf (mword_of_int (KernelSyms.walk + 0x3e)) (Regidx (mword_of_int 9 : mword 5)) (mword_of_int 9 : mword 5) (mword_of_int 12 : mword 6)
              M7 (K - 8)%nat b ltac:(reflexivity) ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi3e").
    iIntros (CID23 Hw23) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (M8 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (shift_bits_left (M7 !!! Regidx (mword_of_int 9 : mword 5)) (subrange_vec_dec (mword_of_int 12 : mword 6) (Z.sub log2_xlen 1) 0))]> M7).
    assert (Hpp40 : add_vec_int (mword_of_int (KernelSyms.walk + 0x3e) : mword 64) 2 = mword_of_int (KernelSyms.walk + 0x40)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp40) in "Hpc".
    assert (HM8s1 : M8 !!! Regidx (mword_of_int 9 : mword 5) = zero_extend' 64 (concat_vec (pt_base c1) (zeros' 12 : mword 12))).
    { rewrite /M8 upd_eq /M7 upd_eq HM6s1.
      rewrite (walk_descend_base pte2 Hv2 Hp2). rewrite /pte2 Hb12. reflexivity. }
    (* +0x40 c.addiw s4,-9 : s4 := 21 *)
    iApply (wp_caddiw_s_sconf (mword_of_int (KernelSyms.walk + 0x40)) (mword_of_int 20 : mword 5) (mword_of_int 55 : mword 6)
              M8 (K - 8)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi40").
    iIntros (CID24 Hw24) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (M9 := <[Regidx (mword_of_int 20 : mword 5) := regval_into_reg (sign_extend' 64 (subrange_vec_dec (add_vec (M8 !!! Regidx (mword_of_int 20 : mword 5)) (sign_extend' 64 (sign_extend' 12 (mword_of_int 55 : mword 6)))) 31 0))]> M8).
    assert (Hpp42 : add_vec_int (mword_of_int (KernelSyms.walk + 0x40) : mword 64) 2 = mword_of_int (KernelSyms.walk + 0x42)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp42) in "Hpc".
    assert (HM8s4 : M8 !!! Regidx (mword_of_int 20 : mword 5) = (mword_of_int 30 : mword 64)).
    { rewrite /M8 /M7 /M6 /M5 /M4. repeat (rewrite upd_ne; [| reg_neq]). exact HW9s4. }
    assert (HM9s4 : M9 !!! Regidx (mword_of_int 20 : mword 5) = (mword_of_int 21 : mword 64)).
    { rewrite /M9 upd_eq HM8s4. exact wkn_dec9_30. }
    assert (HM9s5 : M9 !!! Regidx (mword_of_int 21 : mword 5) = mword_of_int 12).
    { rewrite /M9. rewrite upd_ne; [| reg_neq]. rewrite /M8 /M7 /M6 /M5 /M4. repeat (rewrite upd_ne; [| reg_neq]). exact HW9s5. }
    assert (HM9s3 : M9 !!! Regidx (mword_of_int 19 : mword 5) = va).
    { rewrite /M9 /M8 /M7 /M6 /M5 /M4. repeat (rewrite upd_ne; [| reg_neq]). exact HW9s3. }
    assert (HM9s1 : M9 !!! Regidx (mword_of_int 9 : mword 5) = zero_extend' 64 (concat_vec (pt_base c1) (zeros' 12 : mword 12))).
    { rewrite /M9. rewrite upd_ne; [| reg_neq]. exact HM8s1. }
    assert (HspM9 : M9 !!! Regidx csp_rs1 = spr).
    { rewrite /M9 /M8 /M7 /M6 /M5 /M4. repeat (rewrite upd_ne; [| reg_neq]). exact HspW9. }
    assert (HM9s6 : eq_vec (M9 !!! Regidx (mword_of_int 22 : mword 5)) zero_reg = true).
    { rewrite /M9 /M8 /M7 /M6 /M5 /M4. repeat (rewrite upd_ne; [| reg_neq]). exact HW9s6. }
    assert (HM9x4 : M9 !!! Regidx (mword_of_int 4 : mword 5) = mm !!! Regidx (mword_of_int 4)).
    { rewrite /M9 /M8 /M7 /M6 /M5 /M4. repeat (rewrite upd_ne; [| reg_neq]). exact HW9x4. }
    assert (HM9x23 : M9 !!! Regidx (mword_of_int 23 : mword 5) = mm !!! Regidx (mword_of_int 23)).
    { rewrite /M9 /M8 /M7 /M6 /M5 /M4. repeat (rewrite upd_ne; [| reg_neq]). exact HW9x23. }
    assert (HM9x24 : M9 !!! Regidx (mword_of_int 24 : mword 5) = mm !!! Regidx (mword_of_int 24)).
    { rewrite /M9 /M8 /M7 /M6 /M5 /M4. repeat (rewrite upd_ne; [| reg_neq]). exact HW9x24. }
    assert (HM9x25 : M9 !!! Regidx (mword_of_int 25 : mword 5) = mm !!! Regidx (mword_of_int 25)).
    { rewrite /M9 /M8 /M7 /M6 /M5 /M4. repeat (rewrite upd_ne; [| reg_neq]). exact HW9x25. }
    assert (HM9x26 : M9 !!! Regidx (mword_of_int 26 : mword 5) = mm !!! Regidx (mword_of_int 26)).
    { rewrite /M9 /M8 /M7 /M6 /M5 /M4. repeat (rewrite upd_ne; [| reg_neq]). exact HW9x26. }
    assert (HM9x27 : M9 !!! Regidx (mword_of_int 27 : mword 5) = mm !!! Regidx (mword_of_int 27)).
    { rewrite /M9 /M8 /M7 /M6 /M5 /M4. repeat (rewrite upd_ne; [| reg_neq]). exact HW9x27. }
    (* +0x42 bne s4,s5 TAKEN (21 <> 12) -> +0x26 *)
    iApply (wp_bne_taken_s_sconf (mword_of_int (KernelSyms.walk + 0x42)) (mword_of_int 8164 : mword 13) (mword_of_int 21 : mword 5) (mword_of_int 20 : mword 5)
              M9 (K - 8)%nat b ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              ltac:(repeat rgne; rewrite HM9s4 HM9s5; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi42").
    iApply bi.later_intro. iIntros (CID25 Hw25) "Hcg Hpc".
    assert (Hbk26 : add_vec (mword_of_int (KernelSyms.walk + 0x42) : mword 64) (sign_extend' 64 (mword_of_int 8164 : mword 13)) = mword_of_int (KernelSyms.walk + 0x26)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hbk26) in "Hpc".
    (* ================= LOOP ITERATION 2 (s4 = 21, level 1) ============ *)
    iDestruct (ptree_own_descend_ro 1 dq t c1 (vpn_idx 2 vpn) Hk2 with "Hptree") as "[Hownc1 Hfr1]".
    iDestruct (ptree_own_node_claim 0 dq c1 with "Hownc1") as "[#Hcl1 Hownc1]".
    iDestruct (ptree_own_cell_ro 0 dq c1 (vpn_idx 1 vpn) with "Hownc1") as "[Hslot Hback1]".
    iDestruct (pt_slot_phys_to_mem (pt_base c1) (vpn_idx 1 vpn) dq
                 (pt_ents c1 (vpn_idx 1 vpn)) with "Hcl1 Hslot") as "Hslot".
    iApply (wp_wkn_probe M9 (K - 8)%nat va (mword_of_int 21 : mword 64)
              (u_pte_addr (pt_base c1) (vpn_idx 1 vpn)) (pt_ents c1 (vpn_idx 1 vpn)) b p
              (dqm:=dq) HM9s3 HM9s4
              ltac:(rewrite HM9s1; exact (walk_slot_addr1 (pt_base c1) va Hva'))
              with "Hcg Htext Hpc Hslot").
    iIntros (CID26 Hw26) "Hcg Hpc Hslot".
    iDestruct (pt_slot_mem_to_phys (pt_base c1) (vpn_idx 1 vpn) dq
                 (pt_ents c1 (vpn_idx 1 vpn)) with "Hcl1 Hslot") as "Hslot".
    iDestruct ("Hback1" with "Hslot") as "Hownc1".
    iDestruct ("Hfr1" with "Hownc1") as "Hptree".
    set (pte1 := pt_ents c1 (vpn_idx 1 vpn)).
    set (N4 := <[Regidx (mword_of_int 18 : mword 5) := regval_into_reg (u_pte_addr (pt_base c1) (vpn_idx 1 vpn))]> M9).
    set (N5 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg pte1]> N4).
    set (N6 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (and_vec pte1 (sign_extend' 64 (mword_of_int 1 : mword 12)))]> N5).
    assert (HN6a5 : N6 !!! Regidx (mword_of_int 15 : mword 5) = and_vec pte1 (sign_extend' 64 (mword_of_int 1 : mword 12)))
      by (rewrite /N6 upd_eq; reflexivity).
    assert (HN6s1 : N6 !!! Regidx (mword_of_int 9 : mword 5) = pte1).
    { rewrite /N6. rewrite upd_ne; [| reg_neq]. rewrite /N5 upd_eq. reflexivity. }
    assert (HspN6 : N6 !!! Regidx csp_rs1 = spr).
    { rewrite /N6 /N5 /N4. repeat (rewrite upd_ne; [| reg_neq]). exact HspM9. }
    assert (HN6s6 : eq_vec (N6 !!! Regidx (mword_of_int 22 : mword 5)) zero_reg = true).
    { rewrite /N6 /N5 /N4. repeat (rewrite upd_ne; [| reg_neq]). exact HM9s6. }
    assert (HN6x4 : N6 !!! Regidx (mword_of_int 4 : mword 5) = mm !!! Regidx (mword_of_int 4)).
    { rewrite /N6 /N5 /N4. repeat (rewrite upd_ne; [| reg_neq]). exact HM9x4. }
    assert (HN6x23 : N6 !!! Regidx (mword_of_int 23 : mword 5) = mm !!! Regidx (mword_of_int 23)).
    { rewrite /N6 /N5 /N4. repeat (rewrite upd_ne; [| reg_neq]). exact HM9x23. }
    assert (HN6x24 : N6 !!! Regidx (mword_of_int 24 : mword 5) = mm !!! Regidx (mword_of_int 24)).
    { rewrite /N6 /N5 /N4. repeat (rewrite upd_ne; [| reg_neq]). exact HM9x24. }
    assert (HN6x25 : N6 !!! Regidx (mword_of_int 25 : mword 5) = mm !!! Regidx (mword_of_int 25)).
    { rewrite /N6 /N5 /N4. repeat (rewrite upd_ne; [| reg_neq]). exact HM9x25. }
    assert (HN6x26 : N6 !!! Regidx (mword_of_int 26 : mword 5) = mm !!! Regidx (mword_of_int 26)).
    { rewrite /N6 /N5 /N4. repeat (rewrite upd_ne; [| reg_neq]). exact HM9x26. }
    assert (HN6x27 : N6 !!! Regidx (mword_of_int 27 : mword 5) = mm !!! Regidx (mword_of_int 27)).
    { rewrite /N6 /N5 /N4. repeat (rewrite upd_ne; [| reg_neq]). exact HM9x27. }
    destruct Hnext as [ (Hk1 & Hz1 & Hmv) | (c0 & Hk1 & Hv1 & Hp1 & Hb01 & Hleaf) ].
    { (* ===== V=0 at level 1: beqz taken -> the alloc=0 arm ===== *)
      assert (Hvbit0 : Z.testbit (bv_unsigned pte1) 0 = false).
      { rewrite /pte1 Hz1.
        replace (bv_unsigned (mword_of_int 0 : mword 64)) with 0 by (vm_compute; reflexivity).
        apply Z.bits_0. }
      iApply (wp_cbeqz_taken_s_sconf (mword_of_int (KernelSyms.walk + 0x3a)) (mword_of_int 28 : mword 8) (Cregidx (mword_of_int 7)) (mword_of_int 15 : mword 5)
                N6 (K - 8)%nat b ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                ltac:(rgne; rewrite HN6a5 walk_vbit_eq Hvbit0; reflexivity)
                ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi3a").
      iApply bi.later_intro. iIntros (CID27 Hw27) "Hcg Hpc".
      assert (Htgt72 : add_vec (mword_of_int (KernelSyms.walk + 0x3a) : mword 64) (sign_extend' 64 (sign_extend' 13 (concat_vec (mword_of_int 28 : mword 8) ('b"0")))) = mword_of_int (KernelSyms.walk + 0x72)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Htgt72) in "Hpc".
      iApply (wp_wkn_fail mm N6 t m K dq b p HK HspN6 HN6s6 HN6x4
                HN6x23 HN6x24 HN6x25 HN6x26 HN6x27 Hmv
                with "Hcg Htext Hpc
                      Hc56 Hc48 Hc40 Hc32 Hc24 Hc16 Hc08 Hc00
                      Hptree").
      iIntros (CIDf2 Hwf2).
      iSpecialize ("Hcont" $! CIDf2 with "[%]"); [wp_next_chain|].
      iExact "Hcont". }
    (* ===== V=1 at level 1: descend into c0, then the tail ===== *)
    assert (Hvbit1 : Z.testbit (bv_unsigned pte1) 0 = true).
    { destruct (Z.testbit (bv_unsigned pte1) 0) eqn:E; [reflexivity | exfalso].
      exact (pte_valid_invalid_excl pte1 Hv1 (pte_invalid_bit0 _ E)). }
    iApply (wp_cbeqz_fall_s_sconf (mword_of_int (KernelSyms.walk + 0x3a)) (mword_of_int 28 : mword 8) (Cregidx (mword_of_int 7)) (mword_of_int 15 : mword 5)
              N6 (K - 8)%nat b ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
              ltac:(rgne; rewrite HN6a5 walk_vbit_eq Hvbit1; reflexivity)
              with "Hcg Hpc Hi3a").
    iIntros (CID28 Hw28) "Hcg Hpc".
    assert (Hpp3c' : add_vec_int (mword_of_int (KernelSyms.walk + 0x3a) : mword 64) 2 = mword_of_int (KernelSyms.walk + 0x3c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp3c') in "Hpc".
    (* +0x3c c.srli s1,10 *)
    iApply (wp_csrli_s_sconf (mword_of_int (KernelSyms.walk + 0x3c)) (Cregidx (mword_of_int 1)) (mword_of_int 9 : mword 5) (mword_of_int 10 : mword 6)
              N6 (K - 8)%nat b ltac:(reflexivity) ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi3c").
    iIntros (CID29 Hw29) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (N7 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (shift_bits_right (N6 !!! Regidx (mword_of_int 9 : mword 5)) (subrange_vec_dec (mword_of_int 10 : mword 6) (Z.sub log2_xlen 1) 0))]> N6).
    assert (Hpp3e' : add_vec_int (mword_of_int (KernelSyms.walk + 0x3c) : mword 64) 2 = mword_of_int (KernelSyms.walk + 0x3e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp3e') in "Hpc".
    (* +0x3e c.slli s1,12 *)
    iApply (wp_cslli_s_sconf (mword_of_int (KernelSyms.walk + 0x3e)) (Regidx (mword_of_int 9 : mword 5)) (mword_of_int 9 : mword 5) (mword_of_int 12 : mword 6)
              N7 (K - 8)%nat b ltac:(reflexivity) ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi3e").
    iIntros (CID30 Hw30) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (N8 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (shift_bits_left (N7 !!! Regidx (mword_of_int 9 : mword 5)) (subrange_vec_dec (mword_of_int 12 : mword 6) (Z.sub log2_xlen 1) 0))]> N7).
    assert (Hpp40' : add_vec_int (mword_of_int (KernelSyms.walk + 0x3e) : mword 64) 2 = mword_of_int (KernelSyms.walk + 0x40)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp40') in "Hpc".
    assert (HN8s1 : N8 !!! Regidx (mword_of_int 9 : mword 5) = zero_extend' 64 (concat_vec (pt_base c0) (zeros' 12 : mword 12))).
    { rewrite /N8 upd_eq /N7 upd_eq HN6s1.
      rewrite (walk_descend_base pte1 Hv1 Hp1). rewrite /pte1 Hb01. reflexivity. }
    (* +0x40 c.addiw s4,-9 : s4 := 12 *)
    iApply (wp_caddiw_s_sconf (mword_of_int (KernelSyms.walk + 0x40)) (mword_of_int 20 : mword 5) (mword_of_int 55 : mword 6)
              N8 (K - 8)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi40").
    iIntros (CID31 Hw31) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (N9 := <[Regidx (mword_of_int 20 : mword 5) := regval_into_reg (sign_extend' 64 (subrange_vec_dec (add_vec (N8 !!! Regidx (mword_of_int 20 : mword 5)) (sign_extend' 64 (sign_extend' 12 (mword_of_int 55 : mword 6)))) 31 0))]> N8).
    assert (Hpp42' : add_vec_int (mword_of_int (KernelSyms.walk + 0x40) : mword 64) 2 = mword_of_int (KernelSyms.walk + 0x42)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp42') in "Hpc".
    assert (HN8s4 : N8 !!! Regidx (mword_of_int 20 : mword 5) = (mword_of_int 21 : mword 64)).
    { rewrite /N8 /N7 /N6 /N5 /N4. repeat (rewrite upd_ne; [| reg_neq]). exact HM9s4. }
    assert (HN9s4 : N9 !!! Regidx (mword_of_int 20 : mword 5) = (mword_of_int 12 : mword 64)).
    { rewrite /N9 upd_eq HN8s4. exact wkn_dec9_21. }
    assert (HN9s5 : N9 !!! Regidx (mword_of_int 21 : mword 5) = mword_of_int 12).
    { rewrite /N9. rewrite upd_ne; [| reg_neq]. rewrite /N8 /N7 /N6 /N5 /N4. repeat (rewrite upd_ne; [| reg_neq]). exact HM9s5. }
    assert (HN9s3 : N9 !!! Regidx (mword_of_int 19 : mword 5) = va).
    { rewrite /N9 /N8 /N7 /N6 /N5 /N4. repeat (rewrite upd_ne; [| reg_neq]). exact HM9s3. }
    assert (HN9s1 : N9 !!! Regidx (mword_of_int 9 : mword 5) = zero_extend' 64 (concat_vec (pt_base c0) (zeros' 12 : mword 12))).
    { rewrite /N9. rewrite upd_ne; [| reg_neq]. exact HN8s1. }
    assert (HspN9 : N9 !!! Regidx csp_rs1 = spr).
    { rewrite /N9 /N8 /N7 /N6 /N5 /N4. repeat (rewrite upd_ne; [| reg_neq]). exact HspM9. }
    assert (HN9x4 : N9 !!! Regidx (mword_of_int 4 : mword 5) = mm !!! Regidx (mword_of_int 4)).
    { rewrite /N9 /N8 /N7 /N6 /N5 /N4. repeat (rewrite upd_ne; [| reg_neq]). exact HM9x4. }
    assert (HN9x23 : N9 !!! Regidx (mword_of_int 23 : mword 5) = mm !!! Regidx (mword_of_int 23)).
    { rewrite /N9 /N8 /N7 /N6 /N5 /N4. repeat (rewrite upd_ne; [| reg_neq]). exact HM9x23. }
    assert (HN9x24 : N9 !!! Regidx (mword_of_int 24 : mword 5) = mm !!! Regidx (mword_of_int 24)).
    { rewrite /N9 /N8 /N7 /N6 /N5 /N4. repeat (rewrite upd_ne; [| reg_neq]). exact HM9x24. }
    assert (HN9x25 : N9 !!! Regidx (mword_of_int 25 : mword 5) = mm !!! Regidx (mword_of_int 25)).
    { rewrite /N9 /N8 /N7 /N6 /N5 /N4. repeat (rewrite upd_ne; [| reg_neq]). exact HM9x25. }
    assert (HN9x26 : N9 !!! Regidx (mword_of_int 26 : mword 5) = mm !!! Regidx (mword_of_int 26)).
    { rewrite /N9 /N8 /N7 /N6 /N5 /N4. repeat (rewrite upd_ne; [| reg_neq]). exact HM9x26. }
    assert (HN9x27 : N9 !!! Regidx (mword_of_int 27 : mword 5) = mm !!! Regidx (mword_of_int 27)).
    { rewrite /N9 /N8 /N7 /N6 /N5 /N4. repeat (rewrite upd_ne; [| reg_neq]). exact HM9x27. }
    (* +0x42 bne s4,s5 FALLS (12 = 12) -> +0x46 *)
    iApply (wp_bne_fall_s_sconf (mword_of_int (KernelSyms.walk + 0x42)) (mword_of_int 8164 : mword 13) (mword_of_int 21 : mword 5) (mword_of_int 20 : mword 5)
              N9 (K - 8)%nat b ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              ltac:(repeat rgne; rewrite HN9s4 HN9s5; vm_compute; reflexivity)
              with "Hcg Hpc Hi42").
    iIntros (CID32 Hw32) "Hcg Hpc".
    assert (Hpp46 : add_vec_int (mword_of_int (KernelSyms.walk + 0x42) : mword 64) 4 = mword_of_int (KernelSyms.walk + 0x46)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp46) in "Hpc".
    (* the L0 path fact and the returned slot address *)
    assert (Hl0 : ptree_level0 t vpn pte2 pte1 (pt_ents c0 (vpn_idx 0 vpn))).
    { exists c1, c0.
      split; [exact Hk2 |]. split; [exact Hk1 |].
      split; [reflexivity |]. split; [reflexivity |]. split; [reflexivity |].
      split; [rewrite /pte2; exact Hb12 |]. split; [rewrite /pte1; exact Hb01 |].
      split; [exact Hv2 |]. split; [exact Hp2 |]. split; [exact Hv1 | exact Hp1]. }
    iApply (wp_wkn_tail mm N9 t m (pt_base c0) K dq b p HK Hva'
              HspN9 HN9s3 HN9s1 HN9x4 HN9x23 HN9x24 HN9x25 HN9x26 HN9x27
              ltac:(exists pte2, pte1, (pt_ents c0 (vpn_idx 0 vpn));
                    split; [exact Hl0 |];
                    split; [unfold pt_addr0; rewrite /pte1 Hb01; reflexivity | exact Hleaf])
              with "Hcg Htext Hpc
                    Hc56 Hc48 Hc40 Hc32 Hc24 Hc16 Hc08 Hc00
                    Hptree").
    iIntros (CIDt Hwt).
    iSpecialize ("Hcont" $! CIDt with "[%]"); [wp_next_chain|].
    iExact "Hcont".
  Qed.

End ProofWalkNoalloc.

End WalkNoallocProof.
