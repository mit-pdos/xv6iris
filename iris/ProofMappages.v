(* ProofMappages.v -- mappages() over the SIE-agnostic sconf world.
   Mirror of the smode wp_mappages_r (WpMappages.v): a 10-slot-frame function
   that maps [npages] pages by calling walk() once per page (allocating missing
   interior page-table nodes).  Threads sconf + hart_state + sie_cap +
   intr_count (net-zero, via the walk->kalloc call) + tlb + deep custody +
   ptree_own + kalloc_env. *)
From Stdlib Require Import Eqdep_dec ZArith Lia List.
From stdpp Require Import gmap list list_monad bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import excl.
From iris.base_logic.lib Require Import gen_heap invariants ghost_var.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.Base SailStdpp.Operators_mwords SailStdpp.Values.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import RiscvPtsto RiscvLang RiscvExtras.
Require Import SmodeCore.
Require Import InstrBytes KernelText.
Require Import WpLock WpMmodeLeafBase.
Require Import RegFile.
Require Import CalleeSaved StackOwn.
Require Import IntrDefs WpSmodeIntr.
Require Import IntrDefs.
Require Import HartTp WpNext.
Require Import CpuOwn.
Require Import VcGen WpSconfVc.
Require Import KallocInv.
Require Import CommonWalk PtTree.
Require Import KptTree.   (* pt_slot_phys_to_mem / pt_slot_mem_to_phys *)
Require Import PtBuild KvmSpec.
Require Import CodeMappages.
Require Import WpSconfAlu WpSconfMem WpSconfBtype WpSconfCtl.
Require Import SpecWalk.
Require Import SpecMappages.
From Kernel Require KernelSyms.
Require Import KernelRvcDecode.
Set Printing Depth 40.
Local Open Scope Z_scope.

Module MappagesProof (Walk : WALK) : MAPPAGES.

Section ProofMappages.
  Context `{!riscvGS Σ, !lockG Σ, !sieG Σ, !kallocG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.


  Ltac reg_neq :=
    lazymatch goal with
    | |- ?a <> ?b => tryif unify a b then fail else (vm_compute; discriminate)
    end.

  (* upd_ne/upd_eg lemma peel (values stay opaque) — safe even for a symbolic
     HIT like [F !!! csp = spr]; a bare reg_lookup/vm_compute would hang on the
     add_vec.  Compact over the transparent rf_upd spine (~2.5x faster than gmap). *)
  Ltac peel_reg :=
    repeat first
      [ rewrite upd_eq
      | rewrite upd_ne; [| reg_neq]
      | lazymatch goal with |- ?M !!! _ = _ => is_var M; progress unfold M end ];
    reflexivity.

  (* THE TP BRIDGE (claude-notes/projects/explicit-cpuid-porting-guide.md,
     DISCOVERY 4 / see ProofUvmfree.v's identical helper).  A register map's
     OWN [Rtp] slot is dead data: [sie_cap_gpr] owns [gpr_file (tp_pin m)],
     and [tp_pin] OVERWRITES [Rtp] with the CURRENT hart's [cid_word]
     regardless of what [m] itself says there (HartTp.v).  So [m]'s [Rtp]
     field may be freely patched to whatever value Walk's entry premise
     ([SpecWalk.v]'s [mm !!! Regidx 4 = cid_word]) wants, AT WHICHEVER HART
     "Hcg" is actually held when the call is made -- necessary because this
     loop's own [b]-generic threading may have (semantically) migrated the
     hart since function entry, so there is in general no provable equality
     between the entry hart's cid and the hart the Walk call actually lands
     on. *)
  Lemma sie_cap_gpr_settp `{CID0 : CpuId} (m : regfile) (n : nat) (b : bool)
      (p0 v : mword 64) :
    sie_cap_gpr m n b p0 -∗ sie_cap_gpr (<[Regidx Rtp := v]> m) n b p0.
  Proof.
    assert (Hsp : <[Regidx Rtp := v]> m !!! Regidx csp_rs1 = m !!! Regidx csp_rs1)
      by (apply upd_ne; reg_neq).
    assert (Htpn : tp_pin (<[Regidx Rtp := v]> m) = tp_pin m)
      by (unfold tp_pin; apply upd_upd).
    unfold sie_cap_gpr, sie_cap. rewrite Hsp Htpn. by iIntros "$".
  Qed.

  (* the L0 slot's RAM-ness (used to rule out a NULL (=0) walk result on the
     level0 success arm -- addr 0 is not RAM) now comes straight off the
     PHYSICAL slot cell via [phys_word_pointsto_ram] (uniform-claims: the slot
     is owned at the physical tier before the VA-tier conversion). *)


  (* ================================================================= *)
  (* THE SHARED EPILOGUE (+0x9c..+0xb0) -- sconf mirror.                 *)
  (* ================================================================= *)
  Lemma wp_mappages_epilogue_sconf `{CID0 : CpuId} (γa : gname)
      (mm Mf : regfile) (t tf : ptree)
      (m : gmap (mword 27) (mword 64)) (npages k : nat) (perm : Z) (K lvl : nat)
      (eb : bool) (p : mword 64) (C : iProp Σ) (on : option nat) (q : nat) (b : bool) :
    let va := mm !!! Regidx (mword_of_int 11) in
    let vpn0 := svpn_of va in
    let ppn0 := (autocast (T := mword) (subrange_vec_dec (mm !!! Regidx (mword_of_int 13)) 55 12) : mword 44) in
    let sp0 := mm !!! Regidx csp_rs1 in
    let spr := add_vec sp0 (sign_extend' 64 (caddi16sp_imm (mword_of_int 59 : mword 6))) in
    let ret_tgt := update_vec_dec (mm !!! Regidx (mword_of_int 1)) 0 ('b"0") in
    (32 <= K)%nat ->
    Mf !!! Regidx csp_rs1 = spr ->
    Mf !!! Regidx (mword_of_int 24 : mword 5) = mm !!! Regidx (mword_of_int 24) ->
    Mf !!! Regidx (mword_of_int 25 : mword 5) = mm !!! Regidx (mword_of_int 25) ->
    Mf !!! Regidx (mword_of_int 26 : mword 5) = mm !!! Regidx (mword_of_int 26) ->
    Mf !!! Regidx (mword_of_int 27 : mword 5) = mm !!! Regidx (mword_of_int 27) ->
    pt_base tf = pt_base t ->
    pt_rep0 tf (pt_insert_run m vpn0 ppn0 perm k) ->
    pt_present_mono t tf ->
    pt_nodes tf = (pt_nodes t + q)%nat ->
    (q <= pt_missing t vpn0 npages)%nat ->
    ((k = npages /\ Mf !!! Regidx (mword_of_int 10 : mword 5) = mword_of_int 0)
     \/ ((k < npages)%nat /\ Mf !!! Regidx (mword_of_int 10 : mword 5) = mword_of_int (-1)
         /\ avail_zero (avail_sub on q))) ->
    sie_cap_gpr Mf (K - 10)%nat b p -∗ cpu_own lvl eb p C b -∗
    kernel_text -∗
    pc_is (mword_of_int (KernelSyms.mappages + 0x9c)) -∗
    pa_stk sp0 1 ↦₈ (mm !!! Regidx (mword_of_int 1)) -∗
    pa_stk sp0 2 ↦₈ (mm !!! Regidx (mword_of_int 8)) -∗
    pa_stk sp0 3 ↦₈ (mm !!! Regidx (mword_of_int 9)) -∗
    pa_stk sp0 4 ↦₈ (mm !!! Regidx (mword_of_int 18)) -∗
    pa_stk sp0 5 ↦₈ (mm !!! Regidx (mword_of_int 19)) -∗
    pa_stk sp0 6 ↦₈ (mm !!! Regidx (mword_of_int 20)) -∗
    pa_stk sp0 7 ↦₈ (mm !!! Regidx (mword_of_int 21)) -∗
    pa_stk sp0 8 ↦₈ (mm !!! Regidx (mword_of_int 22)) -∗
    pa_stk sp0 9 ↦₈ (mm !!! Regidx (mword_of_int 23)) -∗
    (∃ v00 : bv 64, pa_stk sp0 10 ↦₈ v00) -∗
    ptree_own 2 (DfracOwn 1) tf -∗
    kalloc_env γa (avail_sub on q) -∗
    wp_next b p (fun (CID : CpuId) =>
      ∀ (mr : regfile) (t' : ptree) (k' : nat) (g : nat),
      sie_cap_gpr mr K b p -∗ cpu_own lvl eb p C b -∗
      pc_is ret_tgt -∗
      ptree_own 2 (DfracOwn 1) t' -∗
      ⌜pt_nodes t' = (pt_nodes t + g)%nat⌝ -∗
      kalloc_env γa (avail_sub on g) -∗
      ⌜callee_saved mm mr⌝ -∗
      ⌜pt_base t' = pt_base t⌝ -∗
      ⌜pt_rep0 t' (pt_insert_run m vpn0 ppn0 perm k')⌝ -∗
      ⌜pt_present_mono t t'⌝ -∗
      ⌜(g <= pt_missing t vpn0 npages)%nat⌝ -∗
      ⌜ (k' = npages /\ mr !!! Regidx (mword_of_int 10) = mword_of_int 0)
        \/ ((k' < npages)%nat /\
            mr !!! Regidx (mword_of_int 10) = mword_of_int (-1) /\
            avail_zero (avail_sub on g)) ⌝ -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros va vpn0 ppn0 sp0 spr ret_tgt HK Hsp Hx24 Hx25 Hx26 Hx27 Hbase Hrep Hpres Hnodes Hmiss Hpay.
    iIntros "Hcg Hcnt #Htext Hpc
             Hc72 Hc64 Hc56 Hc48 Hc40 Hc32 Hc24 Hc16 Hc08 Hc00ex
             Hptree Henv Hcont".
    assert (Hb1 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 9 : mword 6) ('b"000"))) = pa_stk sp0 1).
    { unfold spr, pa_stk, add_vec_int. rewrite !pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb2 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 8 : mword 6) ('b"000"))) = pa_stk sp0 2).
    { unfold spr, pa_stk, add_vec_int. rewrite !pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb3 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 7 : mword 6) ('b"000"))) = pa_stk sp0 3).
    { unfold spr, pa_stk, add_vec_int. rewrite !pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb4 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 6 : mword 6) ('b"000"))) = pa_stk sp0 4).
    { unfold spr, pa_stk, add_vec_int. rewrite !pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb5 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000"))) = pa_stk sp0 5).
    { unfold spr, pa_stk, add_vec_int. rewrite !pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb6 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000"))) = pa_stk sp0 6).
    { unfold spr, pa_stk, add_vec_int. rewrite !pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb7 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000"))) = pa_stk sp0 7).
    { unfold spr, pa_stk, add_vec_int. rewrite !pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb8 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000"))) = pa_stk sp0 8).
    { unfold spr, pa_stk, add_vec_int. rewrite !pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb9 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) = pa_stk sp0 9).
    { unfold spr, pa_stk, add_vec_int. rewrite !pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hsprstk : pa_stk sp0 10 = spr).
    { rewrite /pa_stk /spr /sp0 /add_vec_int. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hdeepaddr : pa_stk (pa_stk sp0 kv_frame_slots) 10 = pa_stk spr kv_frame_slots).
    { unfold spr, sp0, pa_stk, add_vec_int, kv_frame_slots. rewrite !add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    iPoseProof (mi_9c with "Htext") as "Hi9c".
    iPoseProof (mi_9e with "Htext") as "Hi9e".
    iPoseProof (mi_a0 with "Htext") as "Hia0".
    iPoseProof (mi_a2 with "Htext") as "Hia2".
    iPoseProof (mi_a4 with "Htext") as "Hia4".
    iPoseProof (mi_a6 with "Htext") as "Hia6".
    iPoseProof (mi_a8 with "Htext") as "Hia8".
    iPoseProof (mi_aa with "Htext") as "Hiaa".
    iPoseProof (mi_ac with "Htext") as "Hiac".
    iPoseProof (mi_ae with "Htext") as "Hiae".
    iPoseProof (mi_b0 with "Htext") as "Hib0".
    pose proof Hsp as HspE0.
    (* +0x9c c.ldsp x1,72(sp) *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.mappages + 0x9c)) (mword_of_int 9 : mword 6) (mword_of_int 1 : mword 5)
              Mf (K - 10)%nat (mm !!! Regidx (mword_of_int 1 : mword 5)) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi9c [Hc72] [-]").
    { iEval (rewrite HspE0 Hb1). iExact "Hc72". }
    iIntros (CID1 Hs1) "Hcg Hpc Hc72".
    iEval (rewrite HspE0 Hb1) in "Hc72".
    set (E1 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (mm !!! Regidx (mword_of_int 1 : mword 5))]> Mf).
    assert (Hpp9cn : add_vec_int (mword_of_int (KernelSyms.mappages + 0x9c) : mword 64) 2 = mword_of_int (KernelSyms.mappages + 0x9e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp9cn) in "Hpc".
    assert (HspE1 : E1 !!! Regidx csp_rs1 = spr).
    { rewrite /E1. rewrite upd_ne; [| reg_neq]. exact HspE0. }
    (* +0x9e c.ldsp x8,64(sp) *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.mappages + 0x9e)) (mword_of_int 8 : mword 6) (mword_of_int 8 : mword 5)
              E1 (K - 10)%nat (mm !!! Regidx (mword_of_int 8 : mword 5)) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi9e [Hc64] [-]").
    { iEval (rewrite HspE1 Hb2). iExact "Hc64". }
    iIntros (CID2 Hs2) "Hcg Hpc Hc64".
    iEval (rewrite HspE1 Hb2) in "Hc64".
    set (E2 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg (mm !!! Regidx (mword_of_int 8 : mword 5))]> E1).
    assert (Hpp9en : add_vec_int (mword_of_int (KernelSyms.mappages + 0x9e) : mword 64) 2 = mword_of_int (KernelSyms.mappages + 0xa0)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp9en) in "Hpc".
    assert (HspE2 : E2 !!! Regidx csp_rs1 = spr).
    { rewrite /E2. rewrite upd_ne; [| reg_neq]. exact HspE1. }
    (* +0xa0 c.ldsp x9,56(sp) *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.mappages + 0xa0)) (mword_of_int 7 : mword 6) (mword_of_int 9 : mword 5)
              E2 (K - 10)%nat (mm !!! Regidx (mword_of_int 9 : mword 5)) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hia0 [Hc56] [-]").
    { iEval (rewrite HspE2 Hb3). iExact "Hc56". }
    iIntros (CID3 Hs3) "Hcg Hpc Hc56".
    iEval (rewrite HspE2 Hb3) in "Hc56".
    set (E3 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (mm !!! Regidx (mword_of_int 9 : mword 5))]> E2).
    assert (Hppa0n : add_vec_int (mword_of_int (KernelSyms.mappages + 0xa0) : mword 64) 2 = mword_of_int (KernelSyms.mappages + 0xa2)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hppa0n) in "Hpc".
    assert (HspE3 : E3 !!! Regidx csp_rs1 = spr).
    { rewrite /E3. rewrite upd_ne; [| reg_neq]. exact HspE2. }
    (* +0xa2 c.ldsp x18,48(sp) *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.mappages + 0xa2)) (mword_of_int 6 : mword 6) (mword_of_int 18 : mword 5)
              E3 (K - 10)%nat (mm !!! Regidx (mword_of_int 18 : mword 5)) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hia2 [Hc48] [-]").
    { iEval (rewrite HspE3 Hb4). iExact "Hc48". }
    iIntros (CID4 Hs4) "Hcg Hpc Hc48".
    iEval (rewrite HspE3 Hb4) in "Hc48".
    set (E4 := <[Regidx (mword_of_int 18 : mword 5) := regval_into_reg (mm !!! Regidx (mword_of_int 18 : mword 5))]> E3).
    assert (Hppa2n : add_vec_int (mword_of_int (KernelSyms.mappages + 0xa2) : mword 64) 2 = mword_of_int (KernelSyms.mappages + 0xa4)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hppa2n) in "Hpc".
    assert (HspE4 : E4 !!! Regidx csp_rs1 = spr).
    { rewrite /E4. rewrite upd_ne; [| reg_neq]. exact HspE3. }
    (* +0xa4 c.ldsp x19,40(sp) *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.mappages + 0xa4)) (mword_of_int 5 : mword 6) (mword_of_int 19 : mword 5)
              E4 (K - 10)%nat (mm !!! Regidx (mword_of_int 19 : mword 5)) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hia4 [Hc40] [-]").
    { iEval (rewrite HspE4 Hb5). iExact "Hc40". }
    iIntros (CID5 Hs5) "Hcg Hpc Hc40".
    iEval (rewrite HspE4 Hb5) in "Hc40".
    set (E5 := <[Regidx (mword_of_int 19 : mword 5) := regval_into_reg (mm !!! Regidx (mword_of_int 19 : mword 5))]> E4).
    assert (Hppa4n : add_vec_int (mword_of_int (KernelSyms.mappages + 0xa4) : mword 64) 2 = mword_of_int (KernelSyms.mappages + 0xa6)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hppa4n) in "Hpc".
    assert (HspE5 : E5 !!! Regidx csp_rs1 = spr).
    { rewrite /E5. rewrite upd_ne; [| reg_neq]. exact HspE4. }
    (* +0xa6 c.ldsp x20,32(sp) *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.mappages + 0xa6)) (mword_of_int 4 : mword 6) (mword_of_int 20 : mword 5)
              E5 (K - 10)%nat (mm !!! Regidx (mword_of_int 20 : mword 5)) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hia6 [Hc32] [-]").
    { iEval (rewrite HspE5 Hb6). iExact "Hc32". }
    iIntros (CID6 Hs6) "Hcg Hpc Hc32".
    iEval (rewrite HspE5 Hb6) in "Hc32".
    set (E6 := <[Regidx (mword_of_int 20 : mword 5) := regval_into_reg (mm !!! Regidx (mword_of_int 20 : mword 5))]> E5).
    assert (Hppa6n : add_vec_int (mword_of_int (KernelSyms.mappages + 0xa6) : mword 64) 2 = mword_of_int (KernelSyms.mappages + 0xa8)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hppa6n) in "Hpc".
    assert (HspE6 : E6 !!! Regidx csp_rs1 = spr).
    { rewrite /E6. rewrite upd_ne; [| reg_neq]. exact HspE5. }
    (* +0xa8 c.ldsp x21,24(sp) *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.mappages + 0xa8)) (mword_of_int 3 : mword 6) (mword_of_int 21 : mword 5)
              E6 (K - 10)%nat (mm !!! Regidx (mword_of_int 21 : mword 5)) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hia8 [Hc24] [-]").
    { iEval (rewrite HspE6 Hb7). iExact "Hc24". }
    iIntros (CID7 Hs7) "Hcg Hpc Hc24".
    iEval (rewrite HspE6 Hb7) in "Hc24".
    set (E7 := <[Regidx (mword_of_int 21 : mword 5) := regval_into_reg (mm !!! Regidx (mword_of_int 21 : mword 5))]> E6).
    assert (Hppa8n : add_vec_int (mword_of_int (KernelSyms.mappages + 0xa8) : mword 64) 2 = mword_of_int (KernelSyms.mappages + 0xaa)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hppa8n) in "Hpc".
    assert (HspE7 : E7 !!! Regidx csp_rs1 = spr).
    { rewrite /E7. rewrite upd_ne; [| reg_neq]. exact HspE6. }
    (* +0xaa c.ldsp x22,16(sp) *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.mappages + 0xaa)) (mword_of_int 2 : mword 6) (mword_of_int 22 : mword 5)
              E7 (K - 10)%nat (mm !!! Regidx (mword_of_int 22 : mword 5)) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hiaa [Hc16] [-]").
    { iEval (rewrite HspE7 Hb8). iExact "Hc16". }
    iIntros (CID8 Hs8) "Hcg Hpc Hc16".
    iEval (rewrite HspE7 Hb8) in "Hc16".
    set (E8 := <[Regidx (mword_of_int 22 : mword 5) := regval_into_reg (mm !!! Regidx (mword_of_int 22 : mword 5))]> E7).
    assert (Hppaan : add_vec_int (mword_of_int (KernelSyms.mappages + 0xaa) : mword 64) 2 = mword_of_int (KernelSyms.mappages + 0xac)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hppaan) in "Hpc".
    assert (HspE8 : E8 !!! Regidx csp_rs1 = spr).
    { rewrite /E8. rewrite upd_ne; [| reg_neq]. exact HspE7. }
    (* +0xac c.ldsp x23,8(sp) *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.mappages + 0xac)) (mword_of_int 1 : mword 6) (mword_of_int 23 : mword 5)
              E8 (K - 10)%nat (mm !!! Regidx (mword_of_int 23 : mword 5)) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hiac [Hc08] [-]").
    { iEval (rewrite HspE8 Hb9). iExact "Hc08". }
    iIntros (CID9 Hs9) "Hcg Hpc Hc08".
    iEval (rewrite HspE8 Hb9) in "Hc08".
    set (E9 := <[Regidx (mword_of_int 23 : mword 5) := regval_into_reg (mm !!! Regidx (mword_of_int 23 : mword 5))]> E8).
    assert (Hppacn : add_vec_int (mword_of_int (KernelSyms.mappages + 0xac) : mword 64) 2 = mword_of_int (KernelSyms.mappages + 0xae)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hppacn) in "Hpc".
    assert (HspE9 : E9 !!! Regidx csp_rs1 = spr).
    { rewrite /E9. rewrite upd_ne; [| reg_neq]. exact HspE8. }
    (* +0xae c.addi16sp sp,+80 -- the frame pop (feed 10 slots back into avail) *)
    set (E10 := <[Regidx csp_rs1 := regval_into_reg
        (add_vec (E9 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 5 : mword 6))))]> E9).
    assert (HspE10 : E10 !!! Regidx csp_rs1 = sp0).
    { rewrite /E10 upd_eq. rewrite HspE9. unfold spr. apply frame_cancel_80. }
    assert (Hwv : add_vec (E9 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 5 : mword 6))) = sp0).
    { rewrite HspE9. unfold spr. apply frame_cancel_80. }
    assert (Hpop : E9 !!! Regidx csp_rs1
                   = pa_stk (add_vec (E9 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 5 : mword 6)))) 10).
    { rewrite Hwv HspE9. symmetry. exact Hsprstk. }
    iAssert (stack_own sp0 10) with "[Hc72 Hc64 Hc56 Hc48 Hc40 Hc32 Hc24 Hc16 Hc08 Hc00ex]" as "Hframe".
    { rewrite stack_own_slots. cbn [seq].
      iSplitL "Hc72". { iExists (mm !!! Regidx (mword_of_int 1)). iExact "Hc72". }
      iSplitL "Hc64". { iExists (mm !!! Regidx (mword_of_int 8)). iExact "Hc64". }
      iSplitL "Hc56". { iExists (mm !!! Regidx (mword_of_int 9)). iExact "Hc56". }
      iSplitL "Hc48". { iExists (mm !!! Regidx (mword_of_int 18)). iExact "Hc48". }
      iSplitL "Hc40". { iExists (mm !!! Regidx (mword_of_int 19)). iExact "Hc40". }
      iSplitL "Hc32". { iExists (mm !!! Regidx (mword_of_int 20)). iExact "Hc32". }
      iSplitL "Hc24". { iExists (mm !!! Regidx (mword_of_int 21)). iExact "Hc24". }
      iSplitL "Hc16". { iExists (mm !!! Regidx (mword_of_int 22)). iExact "Hc16". }
      iSplitL "Hc08". { iExists (mm !!! Regidx (mword_of_int 23)). iExact "Hc08". }
      iSplitL "Hc00ex". { iExact "Hc00ex". }
      done. }
    iEval (rewrite -Hwv) in "Hframe".
    iApply (wp_caddi16sp_pop_s_sconf (mword_of_int (KernelSyms.mappages + 0xae)) (mword_of_int 5 : mword 6)
              E9 (K - 10)%nat 10 b Hpop
              with "Hcg Hpc Hiae Hframe [-]").
    iIntros (CID10 Hs10) "Hcg Hpc".
    change (<[Regidx csp_rs1 := regval_into_reg (add_vec (E9 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 5 : mword 6))))]> E9) with E10.
    assert (Hnk : ((K - 10) + 10)%nat = K) by lia.
    iEval (rewrite Hnk) in "Hcg".
    assert (Hppaen : add_vec_int (mword_of_int (KernelSyms.mappages + 0xae) : mword 64) 2 = mword_of_int (KernelSyms.mappages + 0xb0)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hppaen) in "Hpc".
    (* +0xb0 ret *)
    assert (HE10ra : E10 !!! Regidx (mword_of_int 1 : mword 5) = mm !!! Regidx (mword_of_int 1)).
    { peel_reg. }
    assert (Hrt : ret_pc (E10 !!! Regidx (mword_of_int 1 : mword 5)) = ret_tgt).
    { rewrite HE10ra. reflexivity. }
    iApply (wp_cret_s_sconf (mword_of_int (KernelSyms.mappages + 0xb0)) (mword_of_int 1 : mword 5) E10 K b
              ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hib0 [-]").
    iIntros (CID11 Hs11) "Hcg Hpc".
    iEval (rewrite Hrt) in "Hpc".
    assert (HE10a0 : E10 !!! Regidx (mword_of_int 10 : mword 5) = Mf !!! Regidx (mword_of_int 10 : mword 5)).
    { rewrite /E10 /E9 /E8 /E7 /E6 /E5 /E4 /E3 /E2 /E1.
      repeat (rewrite upd_ne; [| reg_neq]).
      reflexivity. }
    iDestruct (cpu_own_transport CID0 CID11 lvl eb p C b ltac:(wp_next_chain)
                 with "Hcnt") as "Hcnt".
    iSpecialize ("Hcont" $! CID11 with "[%]"); [wp_next_chain|].
    iApply ("Hcont" $! E10 tf k q with "Hcg Hcnt Hpc Hptree [%] Henv [%] [%] [%] [%] [%] [%]").
    { exact Hnodes. }
    { (* callee_saved mm E10 -- [callee_saved] is TP-FREE now (13 conjuncts:
         sp + the 12 s-registers), so the old tp split is simply gone. *)
      unfold callee_saved.
      split.
      { rewrite /E10 upd_eq. rewrite HspE9. unfold spr. apply frame_cancel_80. }
      split.
      { peel_reg. }
      split.
      { peel_reg. }
      split.
      { peel_reg. }
      split.
      { peel_reg. }
      split.
      { peel_reg. }
      split.
      { peel_reg. }
      split.
      { peel_reg. }
      split.
      { peel_reg. }
      split.
      { rewrite /E10 /E9 /E8 /E7 /E6 /E5 /E4 /E3 /E2 /E1.
        repeat (rewrite upd_ne; [| reg_neq]). exact Hx24. }
      split.
      { rewrite /E10 /E9 /E8 /E7 /E6 /E5 /E4 /E3 /E2 /E1.
        repeat (rewrite upd_ne; [| reg_neq]). exact Hx25. }
      split.
      { rewrite /E10 /E9 /E8 /E7 /E6 /E5 /E4 /E3 /E2 /E1.
        repeat (rewrite upd_ne; [| reg_neq]). exact Hx26. }
      { rewrite /E10 /E9 /E8 /E7 /E6 /E5 /E4 /E3 /E2 /E1.
        repeat (rewrite upd_ne; [| reg_neq]). exact Hx27. }
    }
    { exact Hbase. }
    { exact Hrep. }
    { exact Hpres. }
    { exact Hmiss. }
    { rewrite HE10a0. exact Hpay. }
  Qed.
  (* NB: with g := q the payload/env forms coincide with the epilogue's;
     Hpay already carries [avail_zero (avail_sub on q)] on the -1 arm. *)

  (* ================================================================= *)
  (* THE LOOP (+0x3e..+0x68): induction on the REMAINING page count.    *)
  (* ================================================================= *)
  Lemma wp_mappages_loop_sconf `{CID0 : CpuId} (γa : gname)
      (mm : regfile) (t : ptree)
      (m : gmap (mword 27) (mword 64)) (npages : nat) (perm : Z) (K lvl : nat)
      (eb : bool) (p : mword 64) (C : iProp Σ) (on : option nat)
      (rem : nat) (b : bool) :
    forall (k : nat) (Mk : regfile) (tk : ptree) (consumed : nat),
    let va := mm !!! Regidx (mword_of_int 11) in
    let pa := mm !!! Regidx (mword_of_int 13) in
    let vpn0 := svpn_of va in
    let ppn0 := (autocast (T := mword) (subrange_vec_dec pa 55 12) : mword 44) in
    let sp0 := mm !!! Regidx csp_rs1 in
    let spr := add_vec sp0 (sign_extend' 64 (caddi16sp_imm (mword_of_int 59 : mword 6))) in
    let ret_tgt := update_vec_dec (mm !!! Regidx (mword_of_int 1)) 0 ('b"0") in
    (* walk's kalloc: the transient noff increment stays in int range *)
    (Z.of_nat lvl + 1 < 2 ^ 31)%Z ->
    (32 <= K)%nat ->
    (k + rem)%nat = npages -> (0 < rem)%nat ->
    mm !!! Regidx (mword_of_int 10)
      = zero_extend' 64 (concat_vec (pt_base t) (zeros' 12 : mword 12)) ->
    subrange_vec_dec va 11 0 = (zeros' 12 : mword 12) ->
    subrange_vec_dec pa 11 0 = (zeros' 12 : mword 12) ->
    mm !!! Regidx (mword_of_int 14) = mword_of_int perm ->
    mappages_perm_ok perm ->
    (uint va + Z.of_nat npages * 4096 <= 2 ^ 38)%Z ->
    (uint pa + Z.of_nat npages * 4096 < 2 ^ 56)%Z ->
    (forall i, (i < npages)%nat -> m !! vpn_at vpn0 i = None) ->
    Mk !!! Regidx csp_rs1 = spr ->
    Mk !!! Regidx (mword_of_int 9 : mword 5)
      = add_vec va (mword_of_int (4096 * Z.of_nat k)) ->
    Mk !!! Regidx (mword_of_int 18 : mword 5)
      = add_vec va (mword_of_int (4096 * Z.of_nat (npages - 1))) ->
    Mk !!! Regidx (mword_of_int 19 : mword 5) = sub_vec pa va ->
    Mk !!! Regidx (mword_of_int 20 : mword 5) = mm !!! Regidx (mword_of_int 10) ->
    Mk !!! Regidx (mword_of_int 21 : mword 5) = mm !!! Regidx (mword_of_int 14) ->
    Mk !!! Regidx (mword_of_int 22 : mword 5) = mword_of_int 1 ->
    bv_unsigned (Mk !!! Regidx (mword_of_int 23 : mword 5)) = 4096 ->
    Mk !!! Regidx (mword_of_int 24 : mword 5) = mm !!! Regidx (mword_of_int 24) ->
    Mk !!! Regidx (mword_of_int 25 : mword 5) = mm !!! Regidx (mword_of_int 25) ->
    Mk !!! Regidx (mword_of_int 26 : mword 5) = mm !!! Regidx (mword_of_int 26) ->
    Mk !!! Regidx (mword_of_int 27 : mword 5) = mm !!! Regidx (mword_of_int 27) ->
    pt_base tk = pt_base t ->
    pt_rep0 tk (pt_insert_run m vpn0 ppn0 perm k) ->
    pt_present_mono t tk ->
    pt_nodes tk = (pt_nodes t + consumed)%nat ->
    (consumed + pt_missing tk (vpn_at vpn0 k) (npages - k) <= pt_missing t vpn0 npages)%nat ->
    sie_cap_gpr Mk (K - 10)%nat b p -∗ cpu_own lvl eb p C b -∗
    kernel_text -∗
    pc_is (mword_of_int (KernelSyms.mappages + 0x3e)) -∗
    pa_stk sp0 1 ↦₈ (mm !!! Regidx (mword_of_int 1)) -∗
    pa_stk sp0 2 ↦₈ (mm !!! Regidx (mword_of_int 8)) -∗
    pa_stk sp0 3 ↦₈ (mm !!! Regidx (mword_of_int 9)) -∗
    pa_stk sp0 4 ↦₈ (mm !!! Regidx (mword_of_int 18)) -∗
    pa_stk sp0 5 ↦₈ (mm !!! Regidx (mword_of_int 19)) -∗
    pa_stk sp0 6 ↦₈ (mm !!! Regidx (mword_of_int 20)) -∗
    pa_stk sp0 7 ↦₈ (mm !!! Regidx (mword_of_int 21)) -∗
    pa_stk sp0 8 ↦₈ (mm !!! Regidx (mword_of_int 22)) -∗
    pa_stk sp0 9 ↦₈ (mm !!! Regidx (mword_of_int 23)) -∗
    (∃ v00 : bv 64, pa_stk sp0 10 ↦₈ v00) -∗
    ptree_own 2 (DfracOwn 1) tk -∗
    kalloc_env γa (avail_sub on consumed) -∗
    wp_next b p (fun (CID : CpuId) =>
      ∀ (mr : regfile) (t' : ptree) (k' : nat) (g : nat),
      sie_cap_gpr mr K b p -∗ cpu_own lvl eb p C b -∗
      pc_is ret_tgt -∗
      ptree_own 2 (DfracOwn 1) t' -∗
      ⌜pt_nodes t' = (pt_nodes t + g)%nat⌝ -∗
      kalloc_env γa (avail_sub on g) -∗
      ⌜callee_saved mm mr⌝ -∗
      ⌜pt_base t' = pt_base t⌝ -∗
      ⌜pt_rep0 t' (pt_insert_run m vpn0 ppn0 perm k')⌝ -∗
      ⌜pt_present_mono t t'⌝ -∗
      ⌜(g <= pt_missing t vpn0 npages)%nat⌝ -∗
      ⌜ (k' = npages /\ mr !!! Regidx (mword_of_int 10) = mword_of_int 0)
        \/ ((k' < npages)%nat /\
            mr !!! Regidx (mword_of_int 10) = mword_of_int (-1) /\
            avail_zero (avail_sub on g)) ⌝ -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    revert CID0.
    induction rem as [| rem' IH]; intros CID0 k Mk tk consumed va pa vpn0 ppn0 sp0 spr ret_tgt
      Hlvl HK Hkrem Hrem Hroot Hvaal Hpaal Hpermreg Hpok Hvab Hpab Hnone
      Hsp Hs1 Hs2 Hs3 Hs4 Hs5 Hs6 Hs7 Hx24 Hx25 Hx26 Hx27 Hbase Hrep Hpresk Hnodes Hinv;
      [lia |].
    iIntros "Hcg Hcnt #Htext Hpc
             Hc72 Hc64 Hc56 Hc48 Hc40 Hc32 Hc24 Hc16 Hc08 Hc00ex
             Hptree Henv Hcont".
    pose proof (bv_unsigned_in_range _ va) as Hvarange.
    unfold bv_modulus in Hvarange.
    change (2 ^ Z.of_N (MachineWord.MachineWord.Z_idx 64)) with 18446744073709551616 in Hvarange.
    pose proof (bv_unsigned_in_range _ pa) as Hparange.
    unfold bv_modulus in Hparange.
    change (2 ^ Z.of_N (MachineWord.MachineWord.Z_idx 64)) with 18446744073709551616 in Hparange.
    rewrite uint_unsigned in Hvab. rewrite uint_unsigned in Hpab.
    assert (Hklt : (k < npages)%nat) by lia.
    assert (Hk27 : (Z.of_nat npages < 134217728)%Z) by lia.
    iPoseProof (mi_3e with "Htext") as "Hi3e".
    iPoseProof (mi_40 with "Htext") as "Hi40".
    iPoseProof (mi_42 with "Htext") as "Hi42".
    iPoseProof (mi_44 with "Htext") as "Hi44".
    iPoseProof (mi_48 with "Htext") as "Hi48".
    iPoseProof (mi_4a with "Htext") as "Hi4a".
    iPoseProof (mi_4c with "Htext") as "Hi4c".
    iPoseProof (mi_4e with "Htext") as "Hi4e".
    iPoseProof (mi_50 with "Htext") as "Hi50".
    iPoseProof (mi_54 with "Htext") as "Hi54".
    iPoseProof (mi_56 with "Htext") as "Hi56".
    iPoseProof (mi_58 with "Htext") as "Hi58".
    iPoseProof (mi_5c with "Htext") as "Hi5c".
    iPoseProof (mi_60 with "Htext") as "Hi60".
    iPoseProof (mi_62 with "Htext") as "Hi62".
    iPoseProof (mi_66 with "Htext") as "Hi66".
    iPoseProof (mi_68 with "Htext") as "Hi68".
    iPoseProof (mi_9a with "Htext") as "Hi9a".
    iPoseProof (mi_b2 with "Htext") as "Hib2".
    iPoseProof (mi_b4 with "Htext") as "Hib4".
    (* +0x3e mv a2,s6 *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.mappages + 0x3e)) (mword_of_int 12 : mword 5) (mword_of_int 22 : mword 5)
              Mk (K - 10)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi3e [-]").
    iIntros (CIDa1 Hsa1) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (W1 := <[Regidx (mword_of_int 12 : mword 5) := regval_into_reg (add_vec zero_reg (Mk !!! Regidx (mword_of_int 22 : mword 5)))]> Mk).
    assert (Hpp40 : add_vec_int (mword_of_int (KernelSyms.mappages + 0x3e) : mword 64) 2 = mword_of_int (KernelSyms.mappages + 0x40)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp40) in "Hpc".
    (* +0x40 mv a1,s1 *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.mappages + 0x40)) (mword_of_int 11 : mword 5) (mword_of_int 9 : mword 5)
              W1 (K - 10)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi40 [-]").
    iIntros (CIDa2 Hsa2) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (W2 := <[Regidx (mword_of_int 11 : mword 5) := regval_into_reg (add_vec zero_reg (W1 !!! Regidx (mword_of_int 9 : mword 5)))]> W1).
    assert (Hpp42 : add_vec_int (mword_of_int (KernelSyms.mappages + 0x40) : mword 64) 2 = mword_of_int (KernelSyms.mappages + 0x42)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp42) in "Hpc".
    (* +0x42 mv a0,s4 *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.mappages + 0x42)) (mword_of_int 10 : mword 5) (mword_of_int 20 : mword 5)
              W2 (K - 10)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi42 [-]").
    iIntros (CIDa3 Hsa3) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (W3 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg (add_vec zero_reg (W2 !!! Regidx (mword_of_int 20 : mword 5)))]> W2).
    assert (Hpp44 : add_vec_int (mword_of_int (KernelSyms.mappages + 0x42) : mword 64) 2 = mword_of_int (KernelSyms.mappages + 0x44)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp44) in "Hpc".
    (* +0x44 jal walk *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.mappages + 0x44)) (mword_of_int 1 : mword 5) (mword_of_int 2096872 : mword 21)
              W3 (K - 10)%nat b ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi44 [-]").
    iIntros (CIDa4 Hsa4) "Hcg Hpc".
    set (W4 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.mappages + 0x44) : mword 64) 4)]> W3).
    assert (Hpcw : add_vec (mword_of_int (KernelSyms.mappages + 0x44) : mword 64) (sign_extend' 64 (mword_of_int 2096872 : mword 21)) = mword_of_int KernelSyms.walk) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpcw) in "Hpc".
    (* facts on the call map *)
    assert (HW4a0 : W4 !!! Regidx (mword_of_int 10 : mword 5)
                    = zero_extend' 64 (concat_vec (pt_base tk) (zeros' 12 : mword 12))).
    { rewrite /W4. rewrite upd_ne; [| reg_neq].
      rewrite /W3 upd_eq.
      rewrite /W2 /W1.
      repeat (rewrite upd_ne; [| reg_neq]).
      rewrite add_vec_zero_l. rewrite Hs4. rewrite Hroot. rewrite Hbase. reflexivity. }
    assert (HW4a1 : W4 !!! Regidx (mword_of_int 11 : mword 5)
                    = add_vec va (mword_of_int (4096 * Z.of_nat k))).
    { rewrite /W4 /W3.
      repeat (rewrite upd_ne; [| reg_neq]).
      rewrite /W2 upd_eq.
      rewrite /W1.
      repeat (rewrite upd_ne; [| reg_neq]).
      rewrite add_vec_zero_l. exact Hs1. }
    assert (HW4a2 : W4 !!! Regidx (mword_of_int 12 : mword 5) = mword_of_int 1).
    { rewrite /W4 /W3 /W2.
      repeat (rewrite upd_ne; [| reg_neq]).
      rewrite /W1 upd_eq.
      rewrite add_vec_zero_l. rewrite Hs6. reflexivity. }
    assert (HW4sp : W4 !!! Regidx csp_rs1 = spr).
    { rewrite /W4 /W3 /W2 /W1.
      repeat (rewrite upd_ne; [| reg_neq]).
      exact Hsp. }
    assert (Hvak_u : bv_unsigned (add_vec va (mword_of_int (4096 * Z.of_nat k)))
                     = bv_unsigned va + 4096 * Z.of_nat k)
      by (apply pb_va_k_unsigned; lia).
    assert (Hvpnk : svpn_of (add_vec va (mword_of_int (4096 * Z.of_nat k))) = vpn_at vpn0 k)
      by (apply svpn_of_run; lia).
    (* THE TP PATCH (DISCOVERY 4): Walk's entry premise wants
       [!!! Rtp = cid_word] AT THE HART WE ACTUALLY CALL IT FROM (CIDa4),
       not at the function's entry hart -- [mm]'s own tp value is dead data
       (sie_cap_gpr_settp). *)
    iDestruct (sie_cap_gpr_settp W4 (K - 10)%nat b p cid_word with "Hcg") as "Hcg".
    set (W4' := <[Regidx Rtp := cid_word]> W4).
    change (<[Regidx Rtp := cid_word]> W4) with W4'.
    assert (HW4'tp : W4' !!! Regidx Rtp = cid_word) by (rewrite /W4' upd_eq; reflexivity).
    assert (HW4'thr : forall c : mword 5, is_cs_idx c = true -> W4' !!! Regidx c = W4 !!! Regidx c).
    { intros c Hc. rewrite /W4' upd_ne; [reflexivity |
        intros Hx; injection Hx as Hx2; subst c; vm_compute in Hc; discriminate]. }
    assert (HW4'a0 : W4' !!! Regidx (mword_of_int 10 : mword 5)
                     = zero_extend' 64 (concat_vec (pt_base tk) (zeros' 12 : mword 12)))
      by (rewrite /W4' upd_ne; [exact HW4a0 | reg_neq]).
    assert (HW4'a1 : W4' !!! Regidx (mword_of_int 11 : mword 5)
                     = add_vec va (mword_of_int (4096 * Z.of_nat k)))
      by (rewrite /W4' upd_ne; [exact HW4a1 | reg_neq]).
    assert (HW4'a2 : W4' !!! Regidx (mword_of_int 12 : mword 5) = mword_of_int 1)
      by (rewrite /W4' upd_ne; [exact HW4a2 | reg_neq]).
    assert (HW4'sp : W4' !!! Regidx csp_rs1 = spr)
      by (rewrite /W4' upd_ne; [exact HW4sp | reg_neq]).
    (* [Hcnt] entered this iteration at [CID0]; four plain instructions have
       moved the hart to [CIDa4], right where Walk is called. *)
    iDestruct (cpu_own_transport CID0 CIDa4 lvl eb p C b ltac:(wp_next_chain)
                 with "Hcnt") as "Hcnt".
    (* the walk call *)
    iApply (Walk.wp_walk_sconf γa W4' tk (pt_insert_run m vpn0 ppn0 perm k) (K - 10)%nat lvl eb p C (avail_sub on consumed) b
              Hlvl ltac:(lia)
              HW4'a0 HW4'a2
              ltac:(rewrite HW4'a1; rewrite uint_unsigned; rewrite Hvak_u; lia)
              Hrep
              HW4'tp
              with "Hcg Hcnt Htext Hpc Hptree Henv [-]").
    iIntros (CIDw Hsw mr t' g) "Hcg Hcnt Hpc Hptree %Hg Henv %Hkcs %Hsame %Hoffw %Hpresw %Hmissw %Hpay".
    iEval (rewrite <- (avail_sub_add on consumed g)) in "Henv".
    assert (Ht'nodes : pt_nodes t' = (pt_nodes t + (consumed + g))%nat) by lia.
    (* pc back at +0x48 *)
    assert (Hlink : W4 !!! Regidx (mword_of_int 1 : mword 5) = add_vec_int (mword_of_int (KernelSyms.mappages + 0x44) : mword 64) 4).
    { rewrite /W4 upd_eq. reflexivity. }
    assert (Hret48 : ret_pc (W4 !!! Regidx (mword_of_int 1 : mword 5)) = mword_of_int (KernelSyms.mappages + 0x48)).
    { rewrite Hlink. unfold ret_pc. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hret48) in "Hpc".
    (* recovered callee-saved registers.  [Hkcs : callee_saved W4' mr], and
       [W4'] differs from [W4] only at [Rtp] (dead data, [is_cs_idx Rtp =
       false]), so [HW4'thr] bridges every OTHER index straight back to [W4]
       before the existing [/W4 /W3 /W2 /W1] peel. *)
    assert (Hmr9 : mr !!! Regidx (mword_of_int 9 : mword 5)
                   = add_vec va (mword_of_int (4096 * Z.of_nat k))).
    { rewrite (callee_saved_lookup Hkcs (mword_of_int 9) ltac:(vm_compute; reflexivity)).
      rewrite (HW4'thr (mword_of_int 9) ltac:(vm_compute; reflexivity)).
      rewrite /W4 /W3 /W2 /W1.
      repeat (rewrite upd_ne; [| reg_neq]).
      exact Hs1. }
    assert (Hmr18 : mr !!! Regidx (mword_of_int 18 : mword 5)
                    = add_vec va (mword_of_int (4096 * Z.of_nat (npages - 1)))).
    { rewrite (callee_saved_lookup Hkcs (mword_of_int 18) ltac:(vm_compute; reflexivity)).
      rewrite (HW4'thr (mword_of_int 18) ltac:(vm_compute; reflexivity)).
      rewrite /W4 /W3 /W2 /W1.
      repeat (rewrite upd_ne; [| reg_neq]).
      exact Hs2. }
    assert (Hmr19 : mr !!! Regidx (mword_of_int 19 : mword 5) = sub_vec pa va).
    { rewrite (callee_saved_lookup Hkcs (mword_of_int 19) ltac:(vm_compute; reflexivity)).
      rewrite (HW4'thr (mword_of_int 19) ltac:(vm_compute; reflexivity)).
      rewrite /W4 /W3 /W2 /W1.
      repeat (rewrite upd_ne; [| reg_neq]).
      exact Hs3. }
    assert (Hmr20 : mr !!! Regidx (mword_of_int 20 : mword 5) = mm !!! Regidx (mword_of_int 10)).
    { rewrite (callee_saved_lookup Hkcs (mword_of_int 20) ltac:(vm_compute; reflexivity)).
      rewrite (HW4'thr (mword_of_int 20) ltac:(vm_compute; reflexivity)).
      rewrite /W4 /W3 /W2 /W1.
      repeat (rewrite upd_ne; [| reg_neq]).
      exact Hs4. }
    assert (Hmr21 : mr !!! Regidx (mword_of_int 21 : mword 5) = mm !!! Regidx (mword_of_int 14)).
    { rewrite (callee_saved_lookup Hkcs (mword_of_int 21) ltac:(vm_compute; reflexivity)).
      rewrite (HW4'thr (mword_of_int 21) ltac:(vm_compute; reflexivity)).
      rewrite /W4 /W3 /W2 /W1.
      repeat (rewrite upd_ne; [| reg_neq]).
      exact Hs5. }
    assert (Hmr22 : mr !!! Regidx (mword_of_int 22 : mword 5) = mword_of_int 1).
    { rewrite (callee_saved_lookup Hkcs (mword_of_int 22) ltac:(vm_compute; reflexivity)).
      rewrite (HW4'thr (mword_of_int 22) ltac:(vm_compute; reflexivity)).
      rewrite /W4 /W3 /W2 /W1.
      repeat (rewrite upd_ne; [| reg_neq]).
      exact Hs6. }
    assert (Hmr23 : bv_unsigned (mr !!! Regidx (mword_of_int 23 : mword 5)) = 4096).
    { rewrite (callee_saved_lookup Hkcs (mword_of_int 23) ltac:(vm_compute; reflexivity)).
      rewrite (HW4'thr (mword_of_int 23) ltac:(vm_compute; reflexivity)).
      rewrite /W4 /W3 /W2 /W1.
      repeat (rewrite upd_ne; [| reg_neq]).
      exact Hs7. }
    assert (Hmrsp : mr !!! Regidx csp_rs1 = spr).
    { rewrite (callee_saved_lookup Hkcs csp_rs1 ltac:(vm_compute; reflexivity)).
      exact HW4'sp. }
    assert (Hmr24 : mr !!! Regidx (mword_of_int 24 : mword 5) = mm !!! Regidx (mword_of_int 24)).
    { rewrite (callee_saved_lookup Hkcs (mword_of_int 24) ltac:(vm_compute; reflexivity)).
      rewrite (HW4'thr (mword_of_int 24) ltac:(vm_compute; reflexivity)).
      rewrite /W4 /W3 /W2 /W1.
      repeat (rewrite upd_ne; [| reg_neq]).
      exact Hx24. }
    assert (Hmr25 : mr !!! Regidx (mword_of_int 25 : mword 5) = mm !!! Regidx (mword_of_int 25)).
    { rewrite (callee_saved_lookup Hkcs (mword_of_int 25) ltac:(vm_compute; reflexivity)).
      rewrite (HW4'thr (mword_of_int 25) ltac:(vm_compute; reflexivity)).
      rewrite /W4 /W3 /W2 /W1.
      repeat (rewrite upd_ne; [| reg_neq]).
      exact Hx25. }
    assert (Hmr26 : mr !!! Regidx (mword_of_int 26 : mword 5) = mm !!! Regidx (mword_of_int 26)).
    { rewrite (callee_saved_lookup Hkcs (mword_of_int 26) ltac:(vm_compute; reflexivity)).
      rewrite (HW4'thr (mword_of_int 26) ltac:(vm_compute; reflexivity)).
      rewrite /W4 /W3 /W2 /W1.
      repeat (rewrite upd_ne; [| reg_neq]).
      exact Hx26. }
    assert (Hmr27 : mr !!! Regidx (mword_of_int 27 : mword 5) = mm !!! Regidx (mword_of_int 27)).
    { rewrite (callee_saved_lookup Hkcs (mword_of_int 27) ltac:(vm_compute; reflexivity)).
      rewrite (HW4'thr (mword_of_int 27) ltac:(vm_compute; reflexivity)).
      rewrite /W4 /W3 /W2 /W1.
      repeat (rewrite upd_ne; [| reg_neq]).
      exact Hx27. }
    (* the walk-result facts *)
    assert (Hbase' : pt_base t' = pt_base t).
    { destruct Hsame as (Hb & _). rewrite Hb. exact Hbase. }
    assert (Hrep' : pt_rep0 t' (pt_insert_run m vpn0 ppn0 perm k))
      by (exact (pt_rep0_same tk t' _ Hsame Hrep)).
    assert (Hprest' : pt_present_mono t t')
      by (exact (pt_present_mono_trans t tk t' Hpresk Hpresw)).
    rewrite HW4'a1 in Hpay Hoffw Hmissw. rewrite Hvpnk in Hpay Hoffw Hmissw.
    (* the sharp per-page bound: this walk grew [g <= pt_missing tk vk 1], and
       [pt_missing] is monotone in the page count, so the total node growth
       [consumed + g] stays under the whole run's missing count.  Discharges
       the epilogue's bound on BOTH exit arms. *)
    assert (Hmiss : (consumed + g <= pt_missing t vpn0 npages)%nat).
    { assert (Hnpk : (npages - k = S (npages - k - 1))%nat) by lia.
      pose proof (pt_missing_1_le tk (vpn_at vpn0 k) (npages - k - 1)) as Hmono.
      rewrite <- Hnpk in Hmono. lia. }
    (* the walk returns either NULL (a0=0, kalloc exhausted => avail_zero) or
       the L0 slot address; the latter is an OWNED RAM cell, hence nonzero. *)
    destruct Hpay as [(Ha0z & Havz) | (p2 & p1 & w0 & Hl0 & Ha0v)].
    { (* ---- walk returned NULL: ret -1 (avail_zero) ---- *)
      iApply (wp_cbeqz_taken_s_sconf (mword_of_int (KernelSyms.mappages + 0x48)) (mword_of_int 41 : mword 8) (Cregidx (mword_of_int 2)) (mword_of_int 10 : mword 5)
                mr (K - 10)%nat b
                ltac:(vm_compute; reflexivity)
                ltac:(vm_compute; discriminate)
                ltac:(rgne; rewrite Ha0z; vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi48 [-]").
      iNext. iIntros (CIDn1 Hsn1) "Hcg Hpc".
      assert (Htgt9a : add_vec (mword_of_int (KernelSyms.mappages + 0x48) : mword 64)
                (sign_extend' 64 (sign_extend' 13 (concat_vec (mword_of_int 41 : mword 8) ('b"0"))))
              = mword_of_int (KernelSyms.mappages + 0x9a)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Htgt9a) in "Hpc".
      (* +0x9a li a0,-1 *)
      iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.mappages + 0x9a)) (mword_of_int 10 : mword 5) (mword_of_int 63 : mword 6)
                (add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 63 : mword 6))))
                mr (K - 10)%nat b ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(reflexivity)
                with "Hcg Hpc Hi9a [-]").
      iIntros (CIDn2 Hsn2) "Hcg Hpc".
      set (F1 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg
          (add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 63 : mword 6))))]> mr).
      assert (Hpp9c : add_vec_int (mword_of_int (KernelSyms.mappages + 0x9a) : mword 64) 2 = mword_of_int (KernelSyms.mappages + 0x9c)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp9c) in "Hpc".
      assert (Hcrossn0 : b = false \/ p = zero_reg -> (CIDn2 : CPU) = (CID0 : CPU)) by wp_next_chain.
      assert (Hcrossnw : b = false \/ p = zero_reg -> (CIDn2 : CPU) = (CIDw : CPU)) by wp_next_chain.
      iDestruct (cpu_own_transport CIDw CIDn2 lvl eb p C b Hcrossnw
                   with "Hcnt") as "Hcnt".
      iDestruct (wp_next_shift Hcrossn0 with "Hcont") as "Hcont".
      iApply (wp_mappages_epilogue_sconf γa mm F1 t t' m npages k perm K lvl eb p C on (consumed + g)%nat b HK
                ltac:(rewrite /F1; rewrite upd_ne; [| reg_neq]; exact Hmrsp)
                ltac:(rewrite /F1; rewrite upd_ne; [| reg_neq]; exact Hmr24)
                ltac:(rewrite /F1; rewrite upd_ne; [| reg_neq]; exact Hmr25)
                ltac:(rewrite /F1; rewrite upd_ne; [| reg_neq]; exact Hmr26)
                ltac:(rewrite /F1; rewrite upd_ne; [| reg_neq]; exact Hmr27)
                Hbase' Hrep' Hprest' Ht'nodes Hmiss
                ltac:(right; split; [lia |]; split;
                      [ rewrite /F1 upd_eq; apply bv_eq; vm_compute; reflexivity
                      | rewrite (avail_sub_add on consumed g); exact Havz ])
                with "Hcg Hcnt Htext Hpc
                      Hc72 Hc64 Hc56 Hc48 Hc40 Hc32 Hc24 Hc16 Hc08 Hc00ex
                      Hptree Henv Hcont").
    }
    (* ---- walk returned the L0 slot: store the leaf ---- *)
    iDestruct (ptree_own_level0_upd (DfracOwn 1) t' (vpn_at vpn0 k) p2 p1 w0 Hl0 with "Hptree") as "[#Hcl0 [Hcell Hupd]]".
    iDestruct (phys_word_pointsto_ram with "Hcell") as %Hslotram.
    (* the L0 slot is owned PHYSICALLY ([↦ₚ₈]); the remap-check load and the
       leaf store go THROUGH translation, so convert to the VA tier ([↦₈]) via
       the node's own claim (uniform-claims PHYSICAL TIER), and convert back
       before handing the rewritten cell to the ownership-restore wand. *)
    iDestruct (pt_slot_phys_to_mem (u_next_base p1) (vpn_idx 0 (vpn_at vpn0 k)) (DfracOwn 1) w0
                 with "Hcl0 Hcell") as "Hcell".
    assert (Ha0nz : mr !!! Regidx (mword_of_int 10 : mword 5) <> mword_of_int 0).
    { rewrite Ha0v. intro Heq. rewrite Heq in Hslotram.
      unfold addr_is_ram in Hslotram. destruct Hslotram as [Hlo _].
      apply (proj2 (Z.leb_le _ _)) in Hlo. vm_compute in Hlo. discriminate. }
    assert (Hw0z : w0 = mword_of_int 0).
    { apply (pt_rep0_level0_zero t' (pt_insert_run m vpn0 ppn0 perm k) (vpn_at vpn0 k) p2 p1 w0 Hrep').
      - apply pt_insert_run_lookup_None; [lia | lia |].
        apply Hnone. exact Hklt.
      - exact Hl0. }
    (* +0x48 c.beqz a0 FALLS *)
    iApply (wp_cbeqz_fall_s_sconf (mword_of_int (KernelSyms.mappages + 0x48)) (mword_of_int 41 : mword 8) (Cregidx (mword_of_int 2)) (mword_of_int 10 : mword 5)
              mr (K - 10)%nat b
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; discriminate)
              ltac:(rgne; apply eq_vec_false_iff; intro He; apply Ha0nz;
                    rewrite He; apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc Hi48 [-]").
    iIntros (CIDs1 Hss1) "Hcg Hpc".
    assert (Hpp4a : add_vec_int (mword_of_int (KernelSyms.mappages + 0x48) : mword 64) 2 = mword_of_int (KernelSyms.mappages + 0x4a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp4a) in "Hpc".
    (* the remap-check cell (Hcell/Hupd already extracted above to prove a0<>0) *)
    assert (Hea0 : forall X : mword 64,
        add_vec X (sign_extend' 64 (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 5) ('b"000")))) = X).
    { intro X.
      replace (sign_extend' 64 (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 5) ('b"000"))) : mword 64)
        with (mword_of_int 0 : mword 64) by (apply bv_eq; vm_compute; reflexivity).
      apply kv_addv_zero. }
    (* +0x4a c.ld a5,0(a0) *)
    iApply (wp_cld_s_sconf (mword_of_int (KernelSyms.mappages + 0x4a)) (mword_of_int 15 : mword 5) (mword_of_int 10 : mword 5)
              (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 5) ('b"000")))
              mr (K - 10)%nat w0 b (dqm:=DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi4a [Hcell] [-]").
    { iEval (rgne). iEval (rewrite Hea0 Ha0v). iExact "Hcell". }
    iIntros (CIDs2 Hss2) "Hcg Hpc Hcell".
    iEval (rgne) in "Hcell".
    iEval (rewrite Hea0 Ha0v) in "Hcell".
    set (M5 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg w0]> mr).
    assert (Hpp4c : add_vec_int (mword_of_int (KernelSyms.mappages + 0x4a) : mword 64) 2 = mword_of_int (KernelSyms.mappages + 0x4c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp4c) in "Hpc".
    (* +0x4c c.andi a5,1 *)
    iApply (wp_candi_s_sconf (mword_of_int (KernelSyms.mappages + 0x4c)) (mword_of_int 15 : mword 5) (mword_of_int 1 : mword 6)
              M5 (K - 10)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi4c [-]").
    iIntros (CIDs3 Hss3) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (M6 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg
        (and_vec (M5 !!! Regidx (mword_of_int 15 : mword 5)) (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6))))]> M5).
    assert (Hpp4e : add_vec_int (mword_of_int (KernelSyms.mappages + 0x4c) : mword 64) 2 = mword_of_int (KernelSyms.mappages + 0x4e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp4e) in "Hpc".
    (* +0x4e c.bnez a5 FALLS: the slot word is zero *)
    iApply (wp_cbnez_fall_s_sconf (mword_of_int (KernelSyms.mappages + 0x4e)) (mword_of_int 32 : mword 8) (Cregidx (mword_of_int 7)) (mword_of_int 15 : mword 5)
              M6 (K - 10)%nat b
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; discriminate)
              ltac:(rgne; rewrite /M6 upd_eq; rewrite /M5 upd_eq;
                    rewrite Hw0z; vm_compute; reflexivity)
              with "Hcg Hpc Hi4e [-]").
    iIntros (CIDs4 Hss4) "Hcg Hpc".
    assert (Hpp50 : add_vec_int (mword_of_int (KernelSyms.mappages + 0x4e) : mword 64) 2 = mword_of_int (KernelSyms.mappages + 0x50)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp50) in "Hpc".
    (* +0x50 add a5,s1,s3 *)
    assert (HM6s1 : M6 !!! Regidx (mword_of_int 9 : mword 5)
                    = add_vec va (mword_of_int (4096 * Z.of_nat k))).
    { rewrite /M6 /M5.
      repeat (rewrite upd_ne; [| reg_neq]).
      exact Hmr9. }
    assert (HM6s3 : M6 !!! Regidx (mword_of_int 19 : mword 5) = sub_vec pa va).
    { rewrite /M6 /M5.
      repeat (rewrite upd_ne; [| reg_neq]).
      exact Hmr19. }
    iApply (wp_add_s_sconf (mword_of_int (KernelSyms.mappages + 0x50)) (mword_of_int 15 : mword 5) (mword_of_int 9 : mword 5) (mword_of_int 19 : mword 5)
              (add_vec pa (mword_of_int (4096 * Z.of_nat k)))
              M6 (K - 10)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(repeat rgne; rewrite HM6s1 HM6s3; apply mappages_pa_of_va)
              with "Hcg Hpc Hi50 [-]").
    iIntros (CIDs5 Hss5) "Hcg Hpc".
    set (M7 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg
        (add_vec pa (mword_of_int (4096 * Z.of_nat k)))]> M6).
    assert (Hpp54 : add_vec_int (mword_of_int (KernelSyms.mappages + 0x50) : mword 64) 4 = mword_of_int (KernelSyms.mappages + 0x54)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp54) in "Hpc".
    (* +0x54 c.srli a5,12 *)
    iApply (wp_csrli_s_sconf (mword_of_int (KernelSyms.mappages + 0x54)) (Cregidx (mword_of_int 7)) (mword_of_int 15 : mword 5) (mword_of_int 12 : mword 6)
              M7 (K - 10)%nat b ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi54 [-]").
    iIntros (CIDs6 Hss6) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (M8 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg
        (shift_bits_right (M7 !!! Regidx (mword_of_int 15 : mword 5)) (subrange_vec_dec (mword_of_int 12 : mword 6) (Z.sub log2_xlen 1) 0))]> M7).
    assert (Hpp56 : add_vec_int (mword_of_int (KernelSyms.mappages + 0x54) : mword 64) 2 = mword_of_int (KernelSyms.mappages + 0x56)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp56) in "Hpc".
    (* +0x56 c.slli a5,10 *)
    iApply (wp_cslli_s_sconf (mword_of_int (KernelSyms.mappages + 0x56)) (Regidx (mword_of_int 15)) (mword_of_int 15 : mword 5) (mword_of_int 10 : mword 6)
              M8 (K - 10)%nat b ltac:(reflexivity) ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi56 [-]").
    iIntros (CIDs7 Hss7) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (M9 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg
        (shift_bits_left (M8 !!! Regidx (mword_of_int 15 : mword 5)) (subrange_vec_dec (mword_of_int 10 : mword 6) (Z.sub log2_xlen 1) 0))]> M8).
    assert (Hpp58 : add_vec_int (mword_of_int (KernelSyms.mappages + 0x56) : mword 64) 2 = mword_of_int (KernelSyms.mappages + 0x58)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp58) in "Hpc".
    (* +0x58 or a5,a5,s5 *)
    iApply (wp_or_s_sconf (mword_of_int (KernelSyms.mappages + 0x58)) (mword_of_int 15 : mword 5) (mword_of_int 15 : mword 5) (mword_of_int 21 : mword 5)
              (or_vec (M9 !!! Regidx (mword_of_int 15 : mword 5)) (M9 !!! Regidx (mword_of_int 21 : mword 5)))
              M9 (K - 10)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(repeat rgne; reflexivity)
              with "Hcg Hpc Hi58 [-]").
    iIntros (CIDs8 Hss8) "Hcg Hpc".
    set (M10 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg
        (or_vec (M9 !!! Regidx (mword_of_int 15 : mword 5)) (M9 !!! Regidx (mword_of_int 21 : mword 5)))]> M9).
    assert (Hpp5c : add_vec_int (mword_of_int (KernelSyms.mappages + 0x58) : mword 64) 4 = mword_of_int (KernelSyms.mappages + 0x5c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp5c) in "Hpc".
    (* +0x5c ori a5,a5,1 *)
    iApply (wp_ori_s_sconf (mword_of_int (KernelSyms.mappages + 0x5c)) (mword_of_int 15 : mword 5) (mword_of_int 15 : mword 5) (mword_of_int 1 : mword 12)
              (or_vec (M10 !!! Regidx (mword_of_int 15 : mword 5)) (sign_extend' 64 (mword_of_int 1 : mword 12)))
              M10 (K - 10)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(rgne; reflexivity)
              with "Hcg Hpc Hi5c [-]").
    iIntros (CIDs9 Hss9) "Hcg Hpc".
    set (M11 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg
        (or_vec (M10 !!! Regidx (mword_of_int 15 : mword 5)) (sign_extend' 64 (mword_of_int 1 : mword 12)))]> M10).
    assert (Hpp60 : add_vec_int (mword_of_int (KernelSyms.mappages + 0x5c) : mword 64) 4 = mword_of_int (KernelSyms.mappages + 0x60)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp60) in "Hpc".
    (* the computed word IS the run PTE *)
    assert (HPTE : M11 !!! Regidx (mword_of_int 15 : mword 5) = mappages_pte ppn0 perm k).
    { rewrite /M11 upd_eq.
      rewrite {1}/M10 upd_eq.
      rewrite {1}/M9 upd_eq.
      rewrite {1}/M8 upd_eq.
      rewrite {1}/M7 upd_eq.
      assert (HM9s5 : M9 !!! Regidx (mword_of_int 21 : mword 5) = mword_of_int perm).
      { rewrite /M9 /M8 /M7 /M6 /M5.
        repeat (rewrite upd_ne; [| reg_neq]).
        rewrite Hmr21. exact Hpermreg. }
      rewrite HM9s5.
      destruct Hpok as (Hpr & _).
      assert (Hpaku : bv_unsigned (add_vec pa (mword_of_int (4096 * Z.of_nat k)))
                      = bv_unsigned pa + 4096 * Z.of_nat k)
        by (apply pb_va_k_unsigned; lia).
      unfold mappages_pte. unfold ppn0.
      rewrite <- (run_ppn pa k ltac:(lia)).
      apply (mappages_pte_compute (add_vec pa (mword_of_int (4096 * Z.of_nat k))) perm (mword_of_int perm)).
      - apply moi64_small. lia.
      - exact Hpr.
      - rewrite Hpaku.
        pose proof (aligned12_unsigned pa Hpaal) as Hpal0.
        replace (bv_unsigned pa + 4096 * Z.of_nat k)
          with (bv_unsigned pa + Z.of_nat k * 4096) by lia.
        rewrite Z.mod_add; [exact Hpal0 | lia].
      - rewrite Hpaku. lia. }
    (* +0x60 c.sd a5,0(a0) *)
    assert (HM11a0 : M11 !!! Regidx (mword_of_int 10 : mword 5) = mr !!! Regidx (mword_of_int 10 : mword 5)).
    { rewrite /M11 /M10 /M9 /M8 /M7 /M6 /M5.
      repeat (rewrite upd_ne; [| reg_neq]).
      reflexivity. }
    iApply (wp_csd_s_sconf (mword_of_int (KernelSyms.mappages + 0x60)) (mword_of_int 15 : mword 5) (mword_of_int 10 : mword 5)
              (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 5) ('b"000")))
              M11 (K - 10)%nat w0 b
              with "Hcg Hpc Hi60 [Hcell] [-]").
    { iEval (rgne). iEval (rewrite Hea0 HM11a0 Ha0v). iExact "Hcell". }
    iIntros (CIDs10 Hss10) "Hcg Hpc Hcell".
    iEval (repeat rgne) in "Hcell".
    iEval (rewrite Hea0 HM11a0 Ha0v HPTE) in "Hcell".
    iDestruct (pt_slot_mem_to_phys (u_next_base p1) (vpn_idx 0 (vpn_at vpn0 k)) (DfracOwn 1)
                 (mappages_pte ppn0 perm k) with "Hcl0 Hcell") as "Hcell".
    iDestruct ("Hupd" $! (mappages_pte ppn0 perm k) with "Hcell") as "Hptree".
    assert (Hpp62 : add_vec_int (mword_of_int (KernelSyms.mappages + 0x60) : mword 64) 2 = mword_of_int (KernelSyms.mappages + 0x62)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp62) in "Hpc".
    (* the new tree facts *)
    set (tS := ptree_set_leaf t' (vpn_at vpn0 k) (mappages_pte ppn0 perm k)).
    assert (HbaseS : pt_base tS = pt_base t).
    { rewrite /tS ptree_set_leaf_base. exact Hbase'. }
    assert (HnodesS : pt_nodes tS = (pt_nodes t + (consumed + g))%nat).
    { rewrite /tS pt_nodes_set_leaf. exact Ht'nodes. }
    assert (HrepS : pt_rep0 tS (pt_insert_run m vpn0 ppn0 perm (S k))).
    { destruct (mappages_pte_class (add_vec_int ppn0 (Z.of_nat k)) perm Hpok) as (Hv & Hlf & Hnap & Hpb).
      cbn [pt_insert_run].
      exact (pt_rep0_insert t' (pt_insert_run m vpn0 ppn0 perm k) (vpn_at vpn0 k)
               p2 p1 w0 (mappages_pte ppn0 perm k) Hrep' Hl0 Hv Hlf Hnap Hpb). }
    assert (HpresS : pt_present_mono t tS)
      by (exact (pt_present_mono_trans t t' tS Hprest'
                   (pt_present_mono_set_leaf t' (vpn_at vpn0 k) (mappages_pte ppn0 perm k)))).
    (* +0x62 beq s1,s2 *)
    assert (HM11s1 : M11 !!! Regidx (mword_of_int 9 : mword 5)
                     = add_vec va (mword_of_int (4096 * Z.of_nat k))).
    { rewrite /M11 /M10 /M9 /M8 /M7 /M6 /M5.
      repeat (rewrite upd_ne; [| reg_neq]).
      exact Hmr9. }
    assert (HM11s2 : M11 !!! Regidx (mword_of_int 18 : mword 5)
                     = add_vec va (mword_of_int (4096 * Z.of_nat (npages - 1)))).
    { rewrite /M11 /M10 /M9 /M8 /M7 /M6 /M5.
      repeat (rewrite upd_ne; [| reg_neq]).
      exact Hmr18. }
    destruct rem' as [| rem''].
    { (* ---- LAST page: k = npages - 1; the beq is TAKEN, ret 0 ---- *)
      assert (Hlast : k = (npages - 1)%nat) by lia.
      iApply (wp_beq_taken_s_sconf (mword_of_int (KernelSyms.mappages + 0x62)) (mword_of_int 80 : mword 13) (mword_of_int 18 : mword 5) (mword_of_int 9 : mword 5)
                M11 (K - 10)%nat b
                ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                ltac:(repeat rgne; rewrite HM11s1 HM11s2; rewrite Hlast; apply eq_vec_true_iff; reflexivity)
                ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi62 [-]").
      iNext. iIntros (CIDl1 Hsl1) "Hcg Hpc".
      assert (Htgtb2 : add_vec (mword_of_int (KernelSyms.mappages + 0x62) : mword 64) (sign_extend' 64 (mword_of_int 80 : mword 13)) = mword_of_int (KernelSyms.mappages + 0xb2)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Htgtb2) in "Hpc".
      (* +0xb2 li a0,0 *)
      iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.mappages + 0xb2)) (mword_of_int 10 : mword 5) (mword_of_int 0 : mword 6)
                (add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 0 : mword 6))))
                M11 (K - 10)%nat b ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(reflexivity)
                with "Hcg Hpc Hib2 [-]").
      iIntros (CIDl2 Hsl2) "Hcg Hpc".
      set (F1 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg
          (add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 0 : mword 6))))]> M11).
      assert (Hppb4 : add_vec_int (mword_of_int (KernelSyms.mappages + 0xb2) : mword 64) 2 = mword_of_int (KernelSyms.mappages + 0xb4)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hppb4) in "Hpc".
      (* +0xb4 c.j -> the epilogue *)
      iApply (wp_cj_s_sconf (mword_of_int (KernelSyms.mappages + 0xb4)) (sign_extend' 21 (concat_vec (mword_of_int 2036 : mword 11) ('b"0")))
                F1 (K - 10)%nat b
                ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hib4 [-]").
      iIntros (CIDl3 Hsl3). iNext. iIntros "Hcg Hpc".
      assert (Htgt9c : add_vec (mword_of_int (KernelSyms.mappages + 0xb4) : mword 64)
                (sign_extend' 64 (sign_extend' 21 (concat_vec (mword_of_int 2036 : mword 11) ('b"0"))))
              = mword_of_int (KernelSyms.mappages + 0x9c)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Htgt9c) in "Hpc".
      (* same hoist as the loop re-entry: F1 (= <[10:=..]>M11) doesn't touch
         sp/24-27, so peel each agreement with mr ONCE and hand the epilogue
         its premises as [eq_trans] terms, not re-elaborated inline peels. *)
      assert (Hfsp : F1 !!! Regidx csp_rs1 = mr !!! Regidx csp_rs1) by peel_reg.
      assert (Hf24 : F1 !!! Regidx (mword_of_int 24 : mword 5) = mr !!! Regidx (mword_of_int 24 : mword 5)) by peel_reg.
      assert (Hf25 : F1 !!! Regidx (mword_of_int 25 : mword 5) = mr !!! Regidx (mword_of_int 25 : mword 5)) by peel_reg.
      assert (Hf26 : F1 !!! Regidx (mword_of_int 26 : mword 5) = mr !!! Regidx (mword_of_int 26 : mword 5)) by peel_reg.
      assert (Hf27 : F1 !!! Regidx (mword_of_int 27 : mword 5) = mr !!! Regidx (mword_of_int 27 : mword 5)) by peel_reg.
      assert (Hcrossl0 : b = false \/ p = zero_reg -> (CIDl3 : CPU) = (CID0 : CPU)) by wp_next_chain.
      assert (Hcrosslw : b = false \/ p = zero_reg -> (CIDl3 : CPU) = (CIDw : CPU)) by wp_next_chain.
      iDestruct (cpu_own_transport CIDw CIDl3 lvl eb p C b Hcrosslw
                   with "Hcnt") as "Hcnt".
      iDestruct (wp_next_shift Hcrossl0 with "Hcont") as "Hcont".
      iApply (wp_mappages_epilogue_sconf γa mm F1 t tS m npages (S k) perm K lvl eb p C on (consumed + g)%nat b HK
                (eq_trans Hfsp Hmrsp)
                (eq_trans Hf24 Hmr24)
                (eq_trans Hf25 Hmr25)
                (eq_trans Hf26 Hmr26)
                (eq_trans Hf27 Hmr27)
                HbaseS HrepS HpresS HnodesS Hmiss
                ltac:(left; split; [lia |];
                      rewrite /F1 upd_eq;
                      apply bv_eq; vm_compute; reflexivity)
                with "Hcg Hcnt Htext Hpc
                      Hc72 Hc64 Hc56 Hc48 Hc40 Hc32 Hc24 Hc16 Hc08 Hc00ex
                      Hptree Henv Hcont").
    }
    (* ---- MORE pages: the beq FALLS, step and loop ---- *)
    assert (Hne12 : add_vec va (mword_of_int (4096 * Z.of_nat k))
                    <> add_vec va (mword_of_int (4096 * Z.of_nat (npages - 1)))).
    { intro He.
      apply (mappages_va_eq_iff va k (npages - 1) ltac:(lia) ltac:(lia)) in He.
      lia. }
    iApply (wp_beq_fall_s_sconf (mword_of_int (KernelSyms.mappages + 0x62)) (mword_of_int 80 : mword 13) (mword_of_int 18 : mword 5) (mword_of_int 9 : mword 5)
              M11 (K - 10)%nat b
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              ltac:(repeat rgne; rewrite HM11s1 HM11s2; apply eq_vec_false_iff; exact Hne12)
              with "Hcg Hpc Hi62 [-]").
    iIntros (CIDm1 Hsm1) "Hcg Hpc".
    assert (Hpp66 : add_vec_int (mword_of_int (KernelSyms.mappages + 0x62) : mword 64) 4 = mword_of_int (KernelSyms.mappages + 0x66)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp66) in "Hpc".
    (* +0x66 c.add s1,s1,s7 *)
    iApply (wp_cadd_s_sconf (mword_of_int (KernelSyms.mappages + 0x66)) (mword_of_int 9 : mword 5) (mword_of_int 23 : mword 5)
              M11 (K - 10)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi66 [-]").
    iIntros (CIDm2 Hsm2) "Hcg Hpc".
    iEval (repeat rgne) in "Hcg".
    set (M12 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg
        (add_vec (M11 !!! Regidx (mword_of_int 9 : mword 5)) (M11 !!! Regidx (mword_of_int 23 : mword 5)))]> M11).
    assert (Hpp68 : add_vec_int (mword_of_int (KernelSyms.mappages + 0x66) : mword 64) 2 = mword_of_int (KernelSyms.mappages + 0x68)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp68) in "Hpc".
    (* +0x68 c.j -> loop head *)
    iApply (wp_cj_s_sconf (mword_of_int (KernelSyms.mappages + 0x68)) (sign_extend' 21 (concat_vec (mword_of_int 2027 : mword 11) ('b"0")))
              M12 (K - 10)%nat b
              ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi68 [-]").
    iIntros (CIDm3 Hsm3). iNext. iIntros "Hcg Hpc".
    assert (Htgt3e : add_vec (mword_of_int (KernelSyms.mappages + 0x68) : mword 64)
              (sign_extend' 64 (sign_extend' 21 (concat_vec (mword_of_int 2027 : mword 11) ('b"0"))))
            = mword_of_int (KernelSyms.mappages + 0x3e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgt3e) in "Hpc".
    (* the stepped s1 *)
    assert (HM11s7 : M11 !!! Regidx (mword_of_int 23 : mword 5) = mr !!! Regidx (mword_of_int 23 : mword 5)).
    { rewrite /M11 /M10 /M9 /M8 /M7 /M6 /M5.
      repeat (rewrite upd_ne; [| reg_neq]).
      reflexivity. }
    assert (HM12s1 : M12 !!! Regidx (mword_of_int 9 : mword 5)
                     = add_vec va (mword_of_int (4096 * Z.of_nat (S k)))).
    { rewrite /M12 upd_eq.
      rewrite HM11s1 HM11s7.
      apply (mappages_va_step va k (mr !!! Regidx (mword_of_int 23 : mword 5)) Hmr23). }
    assert (HM12s7v : M12 !!! Regidx (mword_of_int 23 : mword 5)
                      = mr !!! Regidx (mword_of_int 23 : mword 5)).
    { rewrite /M12 /M11 /M10 /M9 /M8 /M7 /M6 /M5.
      repeat (rewrite upd_ne; [| reg_neq]).
      reflexivity. }
    (* loop: re-establish the invariant for M12.  M12..M5 only touch regs 15
       and 9 (the set-chain above), so every OTHER register still agrees with
       the walk-return map mr.  Peel that agreement ONCE per register as a
       named assert (peel_reg is one-layer, O(depth)); IH then gets each premise
       as a plain [eq_trans] term.  Replaces 11 inline [ltac:(rewrite /M12../M5;
       ...)] args -- each re-unfolded the whole 8-deep chain and was re-elaborated
       against the iApply's evars, the file's hot spot. *)
    assert (Hag_sp : M12 !!! Regidx csp_rs1 = mr !!! Regidx csp_rs1) by peel_reg.
    assert (Hag18 : M12 !!! Regidx (mword_of_int 18 : mword 5) = mr !!! Regidx (mword_of_int 18 : mword 5)) by peel_reg.
    assert (Hag19 : M12 !!! Regidx (mword_of_int 19 : mword 5) = mr !!! Regidx (mword_of_int 19 : mword 5)) by peel_reg.
    assert (Hag20 : M12 !!! Regidx (mword_of_int 20 : mword 5) = mr !!! Regidx (mword_of_int 20 : mword 5)) by peel_reg.
    assert (Hag21 : M12 !!! Regidx (mword_of_int 21 : mword 5) = mr !!! Regidx (mword_of_int 21 : mword 5)) by peel_reg.
    assert (Hag22 : M12 !!! Regidx (mword_of_int 22 : mword 5) = mr !!! Regidx (mword_of_int 22 : mword 5)) by peel_reg.
    assert (Hag24 : M12 !!! Regidx (mword_of_int 24 : mword 5) = mr !!! Regidx (mword_of_int 24 : mword 5)) by peel_reg.
    assert (Hag25 : M12 !!! Regidx (mword_of_int 25 : mword 5) = mr !!! Regidx (mword_of_int 25 : mword 5)) by peel_reg.
    assert (Hag26 : M12 !!! Regidx (mword_of_int 26 : mword 5) = mr !!! Regidx (mword_of_int 26 : mword 5)) by peel_reg.
    assert (Hag27 : M12 !!! Regidx (mword_of_int 27 : mword 5) = mr !!! Regidx (mword_of_int 27 : mword 5)) by peel_reg.
    (* re-establish the sharp missing-count invariant for the next iteration:
       the head page's walk grew [g <= pt_missing tk vk 1]; the telescope
       (from walk's off-path agreement + present-facts) bounds the tail's
       missing count under the head's, and [pt_missing_set_leaf] shows the leaf
       store leaves the count unchanged. *)
    assert (HinvS : ((consumed + g) + pt_missing tS (vpn_at vpn0 (S k)) (npages - S k)
                     <= pt_missing t vpn0 npages)%nat).
    { assert (Hvpn0np : (bv_unsigned vpn0 + Z.of_nat npages <= 134217728)%Z).
      { apply (svpn_run_bound va npages); [lia | exact Hvab]. }
      assert (Hbk1 : (bv_unsigned vpn0 + Z.of_nat k < 134217728)%Z) by lia.
      assert (HbkSk : (bv_unsigned vpn0 + Z.of_nat (S k) < 134217728)%Z)
        by (rewrite Nat2Z.inj_succ; lia).
      assert (Hshift : pt_missing tS (vpn_at vpn0 (S k)) (npages - S k)
                       = pt_missing t' (add_vec_int (vpn_at vpn0 k) 1) (npages - S k)).
      { rewrite /tS pt_missing_set_leaf.
        apply pt_missing_bv_eq. exact (vpn_at_step_bv vpn0 k HbkSk). }
      rewrite Hshift.
      assert (Hnn : (npages - S k = npages - k - 1)%nat) by lia.
      rewrite Hnn.
      assert (Hbound : (bv_unsigned (vpn_at vpn0 k) + Z.of_nat (npages - k - 1) + 1 <= 134217728)%Z).
      { rewrite (vpn_at_unsigned vpn0 k Hbk1).
        replace (Z.of_nat (npages - k - 1)) with (Z.of_nat npages - Z.of_nat k - 1)%Z by lia.
        lia. }
      pose proof (pt_missing_tel_offpath tk t' (vpn_at vpn0 k) (npages - k - 1)%nat
                    Hbound Hoffw
                    (ptree_level0_l0_absent t' (vpn_at vpn0 k) p2 p1 w0 Hl0)
                    (ptree_level0_l1_absent t' (vpn_at vpn0 k) p2 p1 w0 Hl0)) as Htel.
      assert (HSn : (S (npages - k - 1) = npages - k)%nat) by lia.
      rewrite HSn in Htel.
      lia. }
    assert (Hcrossm0 : b = false \/ p = zero_reg -> (CIDm3 : CPU) = (CID0 : CPU)) by wp_next_chain.
    assert (Hcrossmw : b = false \/ p = zero_reg -> (CIDm3 : CPU) = (CIDw : CPU)) by wp_next_chain.
    iDestruct (cpu_own_transport CIDw CIDm3 lvl eb p C b Hcrossmw
                 with "Hcnt") as "Hcnt".
    iDestruct (wp_next_shift Hcrossm0 with "Hcont") as "Hcont".
    iApply (IH CIDm3 (S k) M12 tS (consumed + g)%nat
              Hlvl HK ltac:(lia) ltac:(lia) Hroot Hvaal Hpaal Hpermreg Hpok
              ltac:(rewrite uint_unsigned; exact Hvab)
              ltac:(rewrite uint_unsigned; exact Hpab) Hnone
              (eq_trans Hag_sp Hmrsp)
              HM12s1
              (eq_trans Hag18 Hmr18)
              (eq_trans Hag19 Hmr19)
              (eq_trans Hag20 Hmr20)
              (eq_trans Hag21 Hmr21)
              (eq_trans Hag22 Hmr22)
              ltac:(rewrite HM12s7v; exact Hmr23)
              (eq_trans Hag24 Hmr24)
              (eq_trans Hag25 Hmr25)
              (eq_trans Hag26 Hmr26)
              (eq_trans Hag27 Hmr27)
              HbaseS HrepS HpresS HnodesS HinvS
              with "Hcg Hcnt Htext Hpc
                    Hc72 Hc64 Hc56 Hc48 Hc40 Hc32 Hc24 Hc16 Hc08 Hc00ex
                    Hptree Henv Hcont").
  Qed.

  Lemma wp_mappages_sconf
      (γa : gname)
      (mm : regfile) (t : ptree)
      (m : gmap (mword 27) (mword 64)) (npages : nat) (perm : Z) (lvl K : nat)
      (eb : bool) (p : mword 64) (C : iProp Σ) (on : option nat) (b : bool)
    : wp_mappages_sconf_body γa mm t m npages perm lvl K eb p C on b.
  Proof.
    cbv beta delta [wp_mappages_sconf_body].
    intros va pa vpn0 ppn0 ret_tgt
      Hlvl HK Hroot Hvaal Hpaal Hsz Hnp Hpermreg Hpok Hvab Hpab Hrep Hnone.
    pose (sp0 := (mm !!! Regidx csp_rs1 : mword 64)).
    set (spr := add_vec sp0 (sign_extend' 64 (caddi16sp_imm (mword_of_int 59 : mword 6)))).
    set (W1 := <[Regidx csp_rs1 := regval_into_reg
        (add_vec (mm !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 59 : mword 6))))]> mm).
    assert (Hsp1 : W1 !!! Regidx csp_rs1 = pa_stk (mm !!! Regidx csp_rs1) 10).
    { rewrite /W1 upd_eq. unfold regval_into_reg, pa_stk, add_vec_int. apply f_equal.
      apply bv_eq; vm_compute; reflexivity. }
    iIntros "Hcg Hcnt #Htext Hpc Hptree Henv Hcont".
    pose proof (bv_unsigned_in_range _ va) as Hvarange.
    unfold bv_modulus in Hvarange.
    change (2 ^ Z.of_N (MachineWord.MachineWord.Z_idx 64)) with 18446744073709551616 in Hvarange.
    rewrite uint_unsigned in Hvab. rewrite uint_unsigned in Hpab.
    assert (Hszu : bv_unsigned (mword_of_int (Z.of_nat npages * 4096) : mword 64)
                   = Z.of_nat npages * 4096)
      by (apply moi64_small; lia).
    assert (Hb1 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 9 : mword 6) ('b"000"))) = pa_stk sp0 1).
    { unfold spr, pa_stk, add_vec_int. rewrite !pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb2 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 8 : mword 6) ('b"000"))) = pa_stk sp0 2).
    { unfold spr, pa_stk, add_vec_int. rewrite !pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb3 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 7 : mword 6) ('b"000"))) = pa_stk sp0 3).
    { unfold spr, pa_stk, add_vec_int. rewrite !pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb4 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 6 : mword 6) ('b"000"))) = pa_stk sp0 4).
    { unfold spr, pa_stk, add_vec_int. rewrite !pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb5 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000"))) = pa_stk sp0 5).
    { unfold spr, pa_stk, add_vec_int. rewrite !pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb6 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000"))) = pa_stk sp0 6).
    { unfold spr, pa_stk, add_vec_int. rewrite !pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb7 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000"))) = pa_stk sp0 7).
    { unfold spr, pa_stk, add_vec_int. rewrite !pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb8 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000"))) = pa_stk sp0 8).
    { unfold spr, pa_stk, add_vec_int. rewrite !pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb9 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) = pa_stk sp0 9).
    { unfold spr, pa_stk, add_vec_int. rewrite !pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    iPoseProof (mi_00 with "Htext") as "Hi00".
    iPoseProof (mi_02 with "Htext") as "Hi02".
    iPoseProof (mi_04 with "Htext") as "Hi04".
    iPoseProof (mi_06 with "Htext") as "Hi06".
    iPoseProof (mi_08 with "Htext") as "Hi08".
    iPoseProof (mi_0a with "Htext") as "Hi0a".
    iPoseProof (mi_0c with "Htext") as "Hi0c".
    iPoseProof (mi_0e with "Htext") as "Hi0e".
    iPoseProof (mi_10 with "Htext") as "Hi10".
    iPoseProof (mi_12 with "Htext") as "Hi12".
    iPoseProof (mi_14 with "Htext") as "Hi14".
    iPoseProof (mi_16 with "Htext") as "Hi16".
    iPoseProof (mi_1a with "Htext") as "Hi1a".
    iPoseProof (mi_1c with "Htext") as "Hi1c".
    iPoseProof (mi_1e with "Htext") as "Hi1e".
    iPoseProof (mi_20 with "Htext") as "Hi20".
    iPoseProof (mi_24 with "Htext") as "Hi24".
    iPoseProof (mi_26 with "Htext") as "Hi26".
    iPoseProof (mi_28 with "Htext") as "Hi28".
    iPoseProof (mi_2c with "Htext") as "Hi2c".
    iPoseProof (mi_30 with "Htext") as "Hi30".
    iPoseProof (mi_34 with "Htext") as "Hi34".
    iPoseProof (mi_36 with "Htext") as "Hi36".
    iPoseProof (mi_38 with "Htext") as "Hi38".
    iPoseProof (mi_3c with "Htext") as "Hi3c".
    (* +0x00 c.addi16sp sp,-80 : the 10-slot frame push *)
    assert (Hpush : add_vec (mm !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 59 : mword 6))) = pa_stk (mm !!! Regidx csp_rs1) 10).
    { unfold pa_stk, add_vec_int. apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    iApply (wp_caddi16sp_push_s_sconf (mword_of_int KernelSyms.mappages) (mword_of_int 59 : mword 6) mm K 10 b ltac:(lia) Hpush
              with "Hcg Hpc Hi00 [-]").
    iIntros (CID1 Hs1) "Hcg Hframe Hpc".
    change (<[Regidx csp_rs1 := regval_into_reg
        (add_vec (mm !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 59 : mword 6))))]> mm) with W1.
    iEval (rewrite stack_own_slots; cbn [seq]) in "Hframe".
    iDestruct "Hframe" as "(S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9 & S10 & _)".
    iDestruct "S1" as (v72) "Hc72". iDestruct "S2" as (v64) "Hc64".
    iDestruct "S3" as (v56) "Hc56". iDestruct "S4" as (v48) "Hc48".
    iDestruct "S5" as (v40) "Hc40". iDestruct "S6" as (v32) "Hc32".
    iDestruct "S7" as (v24) "Hc24". iDestruct "S8" as (v16) "Hc16".
    iDestruct "S9" as (v8) "Hc08".
    assert (HspW1 : W1 !!! Regidx csp_rs1 = spr)
      by (rewrite /W1; rewrite upd_eq; reflexivity).
    assert (Hpp02 : add_vec_int (mword_of_int KernelSyms.mappages : mword 64) 2 = mword_of_int (KernelSyms.mappages + 0x02)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp02) in "Hpc".
    (* +0x02 c.sdsp x1,72(sp) *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.mappages + 0x02)) (mword_of_int 9 : mword 6) (mword_of_int 1 : mword 5)
              W1 (K - 10)%nat v72 b with "Hcg Hpc Hi02 [Hc72] [-]").
    { iEval (rewrite HspW1 Hb1). iExact "Hc72". }
    iIntros (CID2 Hs2) "Hcg Hpc Hc72".
    iEval (rgne) in "Hc72".
    iEval (rewrite HspW1 Hb1) in "Hc72".
    assert (HW1r1 : W1 !!! Regidx (mword_of_int 1 : mword 5) = mm !!! Regidx (mword_of_int 1)).
    { rewrite /W1. rewrite upd_ne; [reflexivity | reg_neq]. }
    iEval (rewrite HW1r1) in "Hc72".
    assert (Hpp04 : add_vec_int (mword_of_int (KernelSyms.mappages + 0x02) : mword 64) 2 = mword_of_int (KernelSyms.mappages + 0x04)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp04) in "Hpc".
    (* +0x04 c.sdsp x8,64(sp) *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.mappages + 0x04)) (mword_of_int 8 : mword 6) (mword_of_int 8 : mword 5)
              W1 (K - 10)%nat v64 b with "Hcg Hpc Hi04 [Hc64] [-]").
    { iEval (rewrite HspW1 Hb2). iExact "Hc64". }
    iIntros (CID3 Hs3) "Hcg Hpc Hc64".
    iEval (rgne) in "Hc64".
    iEval (rewrite HspW1 Hb2) in "Hc64".
    assert (HW1r8 : W1 !!! Regidx (mword_of_int 8 : mword 5) = mm !!! Regidx (mword_of_int 8)).
    { rewrite /W1. rewrite upd_ne; [reflexivity | reg_neq]. }
    iEval (rewrite HW1r8) in "Hc64".
    assert (Hpp06 : add_vec_int (mword_of_int (KernelSyms.mappages + 0x04) : mword 64) 2 = mword_of_int (KernelSyms.mappages + 0x06)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp06) in "Hpc".
    (* +0x06 c.sdsp x9,56(sp) *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.mappages + 0x06)) (mword_of_int 7 : mword 6) (mword_of_int 9 : mword 5)
              W1 (K - 10)%nat v56 b with "Hcg Hpc Hi06 [Hc56] [-]").
    { iEval (rewrite HspW1 Hb3). iExact "Hc56". }
    iIntros (CID4 Hs4) "Hcg Hpc Hc56".
    iEval (rgne) in "Hc56".
    iEval (rewrite HspW1 Hb3) in "Hc56".
    assert (HW1r9 : W1 !!! Regidx (mword_of_int 9 : mword 5) = mm !!! Regidx (mword_of_int 9)).
    { rewrite /W1. rewrite upd_ne; [reflexivity | reg_neq]. }
    iEval (rewrite HW1r9) in "Hc56".
    assert (Hpp08 : add_vec_int (mword_of_int (KernelSyms.mappages + 0x06) : mword 64) 2 = mword_of_int (KernelSyms.mappages + 0x08)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp08) in "Hpc".
    (* +0x08 c.sdsp x18,48(sp) *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.mappages + 0x08)) (mword_of_int 6 : mword 6) (mword_of_int 18 : mword 5)
              W1 (K - 10)%nat v48 b with "Hcg Hpc Hi08 [Hc48] [-]").
    { iEval (rewrite HspW1 Hb4). iExact "Hc48". }
    iIntros (CID5 Hs5) "Hcg Hpc Hc48".
    iEval (rgne) in "Hc48".
    iEval (rewrite HspW1 Hb4) in "Hc48".
    assert (HW1r18 : W1 !!! Regidx (mword_of_int 18 : mword 5) = mm !!! Regidx (mword_of_int 18)).
    { rewrite /W1. rewrite upd_ne; [reflexivity | reg_neq]. }
    iEval (rewrite HW1r18) in "Hc48".
    assert (Hpp0a : add_vec_int (mword_of_int (KernelSyms.mappages + 0x08) : mword 64) 2 = mword_of_int (KernelSyms.mappages + 0x0a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0a) in "Hpc".
    (* +0x0a c.sdsp x19,40(sp) *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.mappages + 0x0a)) (mword_of_int 5 : mword 6) (mword_of_int 19 : mword 5)
              W1 (K - 10)%nat v40 b with "Hcg Hpc Hi0a [Hc40] [-]").
    { iEval (rewrite HspW1 Hb5). iExact "Hc40". }
    iIntros (CID6 Hs6) "Hcg Hpc Hc40".
    iEval (rgne) in "Hc40".
    iEval (rewrite HspW1 Hb5) in "Hc40".
    assert (HW1r19 : W1 !!! Regidx (mword_of_int 19 : mword 5) = mm !!! Regidx (mword_of_int 19)).
    { rewrite /W1. rewrite upd_ne; [reflexivity | reg_neq]. }
    iEval (rewrite HW1r19) in "Hc40".
    assert (Hpp0c : add_vec_int (mword_of_int (KernelSyms.mappages + 0x0a) : mword 64) 2 = mword_of_int (KernelSyms.mappages + 0x0c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0c) in "Hpc".
    (* +0x0c c.sdsp x20,32(sp) *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.mappages + 0x0c)) (mword_of_int 4 : mword 6) (mword_of_int 20 : mword 5)
              W1 (K - 10)%nat v32 b with "Hcg Hpc Hi0c [Hc32] [-]").
    { iEval (rewrite HspW1 Hb6). iExact "Hc32". }
    iIntros (CID7 Hs7) "Hcg Hpc Hc32".
    iEval (rgne) in "Hc32".
    iEval (rewrite HspW1 Hb6) in "Hc32".
    assert (HW1r20 : W1 !!! Regidx (mword_of_int 20 : mword 5) = mm !!! Regidx (mword_of_int 20)).
    { rewrite /W1. rewrite upd_ne; [reflexivity | reg_neq]. }
    iEval (rewrite HW1r20) in "Hc32".
    assert (Hpp0e : add_vec_int (mword_of_int (KernelSyms.mappages + 0x0c) : mword 64) 2 = mword_of_int (KernelSyms.mappages + 0x0e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0e) in "Hpc".
    (* +0x0e c.sdsp x21,24(sp) *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.mappages + 0x0e)) (mword_of_int 3 : mword 6) (mword_of_int 21 : mword 5)
              W1 (K - 10)%nat v24 b with "Hcg Hpc Hi0e [Hc24] [-]").
    { iEval (rewrite HspW1 Hb7). iExact "Hc24". }
    iIntros (CID8 Hs8) "Hcg Hpc Hc24".
    iEval (rgne) in "Hc24".
    iEval (rewrite HspW1 Hb7) in "Hc24".
    assert (HW1r21 : W1 !!! Regidx (mword_of_int 21 : mword 5) = mm !!! Regidx (mword_of_int 21)).
    { rewrite /W1. rewrite upd_ne; [reflexivity | reg_neq]. }
    iEval (rewrite HW1r21) in "Hc24".
    assert (Hpp10 : add_vec_int (mword_of_int (KernelSyms.mappages + 0x0e) : mword 64) 2 = mword_of_int (KernelSyms.mappages + 0x10)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp10) in "Hpc".
    (* +0x10 c.sdsp x22,16(sp) *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.mappages + 0x10)) (mword_of_int 2 : mword 6) (mword_of_int 22 : mword 5)
              W1 (K - 10)%nat v16 b with "Hcg Hpc Hi10 [Hc16] [-]").
    { iEval (rewrite HspW1 Hb8). iExact "Hc16". }
    iIntros (CID9 Hs9) "Hcg Hpc Hc16".
    iEval (rgne) in "Hc16".
    iEval (rewrite HspW1 Hb8) in "Hc16".
    assert (HW1r22 : W1 !!! Regidx (mword_of_int 22 : mword 5) = mm !!! Regidx (mword_of_int 22)).
    { rewrite /W1. rewrite upd_ne; [reflexivity | reg_neq]. }
    iEval (rewrite HW1r22) in "Hc16".
    assert (Hpp12 : add_vec_int (mword_of_int (KernelSyms.mappages + 0x10) : mword 64) 2 = mword_of_int (KernelSyms.mappages + 0x12)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp12) in "Hpc".
    (* +0x12 c.sdsp x23,8(sp) *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.mappages + 0x12)) (mword_of_int 1 : mword 6) (mword_of_int 23 : mword 5)
              W1 (K - 10)%nat v8 b with "Hcg Hpc Hi12 [Hc08] [-]").
    { iEval (rewrite HspW1 Hb9). iExact "Hc08". }
    iIntros (CID10 Hs10) "Hcg Hpc Hc08".
    iEval (rgne) in "Hc08".
    iEval (rewrite HspW1 Hb9) in "Hc08".
    assert (HW1r23 : W1 !!! Regidx (mword_of_int 23 : mword 5) = mm !!! Regidx (mword_of_int 23)).
    { rewrite /W1. rewrite upd_ne; [reflexivity | reg_neq]. }
    iEval (rewrite HW1r23) in "Hc08".
    assert (Hpp14 : add_vec_int (mword_of_int (KernelSyms.mappages + 0x12) : mword 64) 2 = mword_of_int (KernelSyms.mappages + 0x14)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp14) in "Hpc".
    (* +0x14 c.addi4spn s0,sp,80 *)
    iApply (wp_caddi4spn_s_sconf (mword_of_int (KernelSyms.mappages + 0x14)) (Cregidx (mword_of_int 0)) (mword_of_int 20 : mword 8) (mword_of_int 8 : mword 5)
              W1 (K - 10)%nat b
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi14 [-]").
    iIntros (CID11 Hs11) "Hcg Hpc".
    set (P2 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg
        (add_vec (W1 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 20 : mword 8))))]> W1).
    assert (Hpp16 : add_vec_int (mword_of_int (KernelSyms.mappages + 0x14) : mword 64) 2 = mword_of_int (KernelSyms.mappages + 0x16)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp16) in "Hpc".
    (* +0x16 slli a5,a1,52 -- the va alignment probe *)
    assert (HP2a1 : P2 !!! Regidx (mword_of_int 11 : mword 5) = va).
    { rewrite /P2 /W1.
      repeat (rewrite upd_ne; [| reg_neq]).
      reflexivity. }
    iApply (wp_slli_s_sconf (mword_of_int (KernelSyms.mappages + 0x16)) (mword_of_int 15 : mword 5) (mword_of_int 11 : mword 5) (mword_of_int 52 : mword 6)
              (mword_of_int 0 : mword 64)
              P2 (K - 10)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(rgne; rewrite HP2a1; apply mappages_align_probe;
                    apply (aligned12_unsigned va Hvaal))
              with "Hcg Hpc Hi16 [-]").
    iIntros (CID12 Hs12) "Hcg Hpc".
    set (P3 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (mword_of_int 0 : mword 64)]> P2).
    assert (Hpp1a : add_vec_int (mword_of_int (KernelSyms.mappages + 0x16) : mword 64) 4 = mword_of_int (KernelSyms.mappages + 0x1a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp1a) in "Hpc".
    (* +0x1a c.bnez a5 FALLS *)
    iApply (wp_cbnez_fall_s_sconf (mword_of_int (KernelSyms.mappages + 0x1a)) (mword_of_int 40 : mword 8) (Cregidx (mword_of_int 7)) (mword_of_int 15 : mword 5)
              P3 (K - 10)%nat b
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; discriminate)
              ltac:(rgne; rewrite /P3 upd_eq; vm_compute; reflexivity)
              with "Hcg Hpc Hi1a [-]").
    iIntros (CID13 Hs13) "Hcg Hpc".
    assert (Hpp1c : add_vec_int (mword_of_int (KernelSyms.mappages + 0x1a) : mword 64) 2 = mword_of_int (KernelSyms.mappages + 0x1c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp1c) in "Hpc".
    (* +0x1c mv s4,a0 *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.mappages + 0x1c)) (mword_of_int 20 : mword 5) (mword_of_int 10 : mword 5)
              P3 (K - 10)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi1c [-]").
    iIntros (CID14 Hs14) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (P4 := <[Regidx (mword_of_int 20 : mword 5) := regval_into_reg (add_vec zero_reg (P3 !!! Regidx (mword_of_int 10 : mword 5)))]> P3).
    assert (Hpp1e : add_vec_int (mword_of_int (KernelSyms.mappages + 0x1c) : mword 64) 2 = mword_of_int (KernelSyms.mappages + 0x1e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp1e) in "Hpc".
    (* +0x1e mv s5,a4 *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.mappages + 0x1e)) (mword_of_int 21 : mword 5) (mword_of_int 14 : mword 5)
              P4 (K - 10)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi1e [-]").
    iIntros (CID15 Hs15) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (P5 := <[Regidx (mword_of_int 21 : mword 5) := regval_into_reg (add_vec zero_reg (P4 !!! Regidx (mword_of_int 14 : mword 5)))]> P4).
    assert (Hpp20 : add_vec_int (mword_of_int (KernelSyms.mappages + 0x1e) : mword 64) 2 = mword_of_int (KernelSyms.mappages + 0x20)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp20) in "Hpc".
    (* +0x20 slli a5,a2,52 -- the size alignment probe *)
    assert (HP5a2 : P5 !!! Regidx (mword_of_int 12 : mword 5)
                    = mword_of_int (Z.of_nat npages * 4096)).
    { rewrite /P5 /P4 /P3 /P2 /W1.
      repeat (rewrite upd_ne; [| reg_neq]).
      exact Hsz. }
    iApply (wp_slli_s_sconf (mword_of_int (KernelSyms.mappages + 0x20)) (mword_of_int 15 : mword 5) (mword_of_int 12 : mword 5) (mword_of_int 52 : mword 6)
              (mword_of_int 0 : mword 64)
              P5 (K - 10)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(rgne; rewrite HP5a2; apply mappages_align_probe;
                    rewrite Hszu;
                    replace (Z.of_nat npages * 4096) with (Z.of_nat npages * 4096) by lia;
                    apply Z_mod_mult)
              with "Hcg Hpc Hi20 [-]").
    iIntros (CID16 Hs16) "Hcg Hpc".
    set (P6 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (mword_of_int 0 : mword 64)]> P5).
    assert (Hpp24 : add_vec_int (mword_of_int (KernelSyms.mappages + 0x20) : mword 64) 4 = mword_of_int (KernelSyms.mappages + 0x24)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp24) in "Hpc".
    (* +0x24 c.bnez a5 FALLS *)
    iApply (wp_cbnez_fall_s_sconf (mword_of_int (KernelSyms.mappages + 0x24)) (mword_of_int 41 : mword 8) (Cregidx (mword_of_int 7)) (mword_of_int 15 : mword 5)
              P6 (K - 10)%nat b
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; discriminate)
              ltac:(rgne; rewrite /P6 upd_eq; vm_compute; reflexivity)
              with "Hcg Hpc Hi24 [-]").
    iIntros (CID17 Hs17) "Hcg Hpc".
    assert (Hpp26 : add_vec_int (mword_of_int (KernelSyms.mappages + 0x24) : mword 64) 2 = mword_of_int (KernelSyms.mappages + 0x26)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp26) in "Hpc".
    (* +0x26 c.beqz a2 FALLS: the size is nonzero *)
    assert (HP6a2 : P6 !!! Regidx (mword_of_int 12 : mword 5)
                    = mword_of_int (Z.of_nat npages * 4096)).
    { rewrite /P6. rewrite upd_ne; [| reg_neq].
      exact HP5a2. }
    iApply (wp_cbeqz_fall_s_sconf (mword_of_int (KernelSyms.mappages + 0x26)) (mword_of_int 46 : mword 8) (Cregidx (mword_of_int 4)) (mword_of_int 12 : mword 5)
              P6 (K - 10)%nat b
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; discriminate)
              ltac:(rgne; rewrite HP6a2; apply eq_vec_false_iff; intro He;
                    apply (f_equal bv_unsigned) in He;
                    rewrite Hszu in He;
                    replace (bv_unsigned (zero_reg : mword 64)) with 0 in He
                      by (vm_compute; reflexivity);
                    lia)
              with "Hcg Hpc Hi26 [-]").
    iIntros (CID18 Hs18) "Hcg Hpc".
    assert (Hpp28 : add_vec_int (mword_of_int (KernelSyms.mappages + 0x26) : mword 64) 2 = mword_of_int (KernelSyms.mappages + 0x28)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp28) in "Hpc".
    (* +0x28/+0x2c addi a2,a2,-2048 twice *)
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.mappages + 0x28)) (mword_of_int 12 : mword 5) (mword_of_int 12 : mword 5) (mword_of_int 2048 : mword 12)
              P6 (K - 10)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi28 [-]").
    iIntros (CID19 Hs19) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (P7 := <[Regidx (mword_of_int 12 : mword 5) := regval_into_reg
        (add_vec (P6 !!! Regidx (mword_of_int 12 : mword 5)) (sign_extend' 64 (mword_of_int 2048 : mword 12)))]> P6).
    assert (Hpp2c : add_vec_int (mword_of_int (KernelSyms.mappages + 0x28) : mword 64) 4 = mword_of_int (KernelSyms.mappages + 0x2c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp2c) in "Hpc".
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.mappages + 0x2c)) (mword_of_int 12 : mword 5) (mword_of_int 12 : mword 5) (mword_of_int 2048 : mword 12)
              P7 (K - 10)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi2c [-]").
    iIntros (CID20 Hs20) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (P8 := <[Regidx (mword_of_int 12 : mword 5) := regval_into_reg
        (add_vec (P7 !!! Regidx (mword_of_int 12 : mword 5)) (sign_extend' 64 (mword_of_int 2048 : mword 12)))]> P7).
    assert (Hpp30 : add_vec_int (mword_of_int (KernelSyms.mappages + 0x2c) : mword 64) 4 = mword_of_int (KernelSyms.mappages + 0x30)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp30) in "Hpc".
    (* +0x30 add s2,a2,a1 : s2 := the LAST page's va *)
    assert (HP8a2 : P8 !!! Regidx (mword_of_int 12 : mword 5)
                    = add_vec (add_vec (mword_of_int (Z.of_nat npages * 4096))
                                 (sign_extend' 64 (mword_of_int 2048 : mword 12)))
                        (sign_extend' 64 (mword_of_int 2048 : mword 12))).
    { rewrite /P8 upd_eq.
      rewrite {1}/P7 upd_eq.
      rewrite HP6a2. reflexivity. }
    assert (HP8a1 : P8 !!! Regidx (mword_of_int 11 : mword 5) = va).
    { rewrite /P8 /P7 /P6 /P5 /P4 /P3 /P2 /W1.
      repeat (rewrite upd_ne; [| reg_neq]).
      reflexivity. }
    iApply (wp_add_s_sconf (mword_of_int (KernelSyms.mappages + 0x30)) (mword_of_int 18 : mword 5) (mword_of_int 12 : mword 5) (mword_of_int 11 : mword 5)
              (add_vec va (mword_of_int (4096 * Z.of_nat (npages - 1))))
              P8 (K - 10)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(repeat rgne; rewrite HP8a2 HP8a1;
                    apply (mappages_s2_val va (mword_of_int (Z.of_nat npages * 4096)) npages Hszu Hnp))
              with "Hcg Hpc Hi30 [-]").
    iIntros (CID21 Hs21) "Hcg Hpc".
    set (P9 := <[Regidx (mword_of_int 18 : mword 5) := regval_into_reg
        (add_vec va (mword_of_int (4096 * Z.of_nat (npages - 1))))]> P8).
    assert (Hpp34 : add_vec_int (mword_of_int (KernelSyms.mappages + 0x30) : mword 64) 4 = mword_of_int (KernelSyms.mappages + 0x34)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp34) in "Hpc".
    (* +0x34 mv s1,a1 *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.mappages + 0x34)) (mword_of_int 9 : mword 5) (mword_of_int 11 : mword 5)
              P9 (K - 10)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi34 [-]").
    iIntros (CID22 Hs22) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (P10 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (add_vec zero_reg (P9 !!! Regidx (mword_of_int 11 : mword 5)))]> P9).
    assert (Hpp36 : add_vec_int (mword_of_int (KernelSyms.mappages + 0x34) : mword 64) 2 = mword_of_int (KernelSyms.mappages + 0x36)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp36) in "Hpc".
    (* +0x36 li s6,1 *)
    iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.mappages + 0x36)) (mword_of_int 22 : mword 5) (mword_of_int 1 : mword 6)
              (add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6))))
              P10 (K - 10)%nat b ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(reflexivity)
              with "Hcg Hpc Hi36 [-]").
    iIntros (CID23 Hs23) "Hcg Hpc".
    set (P11 := <[Regidx (mword_of_int 22 : mword 5) := regval_into_reg
        (add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6))))]> P10).
    assert (Hpp38 : add_vec_int (mword_of_int (KernelSyms.mappages + 0x36) : mword 64) 2 = mword_of_int (KernelSyms.mappages + 0x38)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp38) in "Hpc".
    (* +0x38 sub s3,a3,a1 *)
    assert (HP11a3 : P11 !!! Regidx (mword_of_int 13 : mword 5) = pa).
    { rewrite /P11 /P10 /P9 /P8 /P7 /P6 /P5 /P4 /P3 /P2 /W1.
      repeat (rewrite upd_ne; [| reg_neq]).
      reflexivity. }
    assert (HP11a1 : P11 !!! Regidx (mword_of_int 11 : mword 5) = va).
    { rewrite /P11 /P10 /P9.
      repeat (rewrite upd_ne; [| reg_neq]).
      reflexivity. }
    iApply (wp_sub_s_sconf (mword_of_int (KernelSyms.mappages + 0x38)) (mword_of_int 19 : mword 5) (mword_of_int 13 : mword 5) (mword_of_int 11 : mword 5)
              (sub_vec pa va)
              P11 (K - 10)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(repeat rgne; rewrite HP11a3 HP11a1; reflexivity)
              with "Hcg Hpc Hi38 [-]").
    iIntros (CID24 Hs24) "Hcg Hpc".
    set (P12 := <[Regidx (mword_of_int 19 : mword 5) := regval_into_reg (sub_vec pa va)]> P11).
    assert (Hpp3c : add_vec_int (mword_of_int (KernelSyms.mappages + 0x38) : mword 64) 4 = mword_of_int (KernelSyms.mappages + 0x3c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp3c) in "Hpc".
    (* +0x3c lui s7,1 : s7 := 4096 *)
    iApply (wp_clui_s_sconf (mword_of_int (KernelSyms.mappages + 0x3c)) (mword_of_int 23 : mword 5) (sign_extend' 20 (mword_of_int 1 : mword 6))
              (luival (sign_extend' 20 (mword_of_int 1 : mword 6)))
              P12 (K - 10)%nat b ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(reflexivity)
              with "Hcg Hpc Hi3c [-]").
    iIntros (CID25 Hs25) "Hcg Hpc".
    set (P13 := <[Regidx (mword_of_int 23 : mword 5) := regval_into_reg
        (luival (sign_extend' 20 (mword_of_int 1 : mword 6)))]> P12).
    assert (Hpp3e : add_vec_int (mword_of_int (KernelSyms.mappages + 0x3c) : mword 64) 2 = mword_of_int (KernelSyms.mappages + 0x3e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp3e) in "Hpc".
    (* ---- enter the loop at page 0 ---- *)
    assert (HP13s1 : P13 !!! Regidx (mword_of_int 9 : mword 5)
                     = add_vec va (mword_of_int (4096 * Z.of_nat 0))).
    { rewrite /P13 /P12 /P11.
      repeat (rewrite upd_ne; [| reg_neq]).
      rewrite /P10 upd_eq.
      rewrite /P9 /P8 /P7 /P6 /P5 /P4 /P3 /P2 /W1.
      repeat (rewrite upd_ne; [| reg_neq]).
      rewrite add_vec_zero_l.
      rewrite mappages_va0. reflexivity. }
    (* hoist the deepest premise (sp, 12-deep over P2..P13): peel the agreement
       with W1 ONCE, then hand it over as an [eq_trans] term instead of an inline
       re-elaborated whole-chain peel. *)
    assert (HPsp : P13 !!! Regidx csp_rs1 = W1 !!! Regidx csp_rs1)
      by (rewrite /P13 /P12 /P11 /P10 /P9 /P8 /P7 /P6 /P5 /P4 /P3 /P2;
          repeat (rewrite upd_ne; [| reg_neq]); reflexivity).
    assert (Hinv0 : (0 + pt_missing t (vpn_at vpn0 0) (npages - 0) <= pt_missing t vpn0 npages)%nat).
    { rewrite Nat.add_0_l. rewrite Nat.sub_0_r.
      rewrite (pt_missing_bv_eq t (vpn_at vpn0 0) vpn0 npages (vpn_at_0_bv vpn0)).
      apply Nat.le_refl. }
    (* [Hcnt] entered at the function's own entry hart [CID] (never itself
       touched by any of the 25 plain prologue instructions above, since none
       of them mention [cpu_own]); the loop is entered at [CID25]. *)
    iDestruct (cpu_own_transport CID CID25 lvl eb p C b ltac:(wp_next_chain)
                 with "Hcnt") as "Hcnt".
    iApply (wp_mappages_loop_sconf γa mm t m npages perm K lvl eb p C on npages b 0%nat P13 t 0%nat
              Hlvl HK ltac:(lia) Hnp Hroot Hvaal Hpaal Hpermreg Hpok
              ltac:(rewrite uint_unsigned; exact Hvab)
              ltac:(rewrite uint_unsigned; exact Hpab) Hnone
              (eq_trans HPsp HspW1)
              HP13s1
              ltac:(rewrite /P13 /P12 /P11 /P10;
                    repeat (rewrite upd_ne; [| reg_neq]);
                    rewrite /P9 upd_eq; reflexivity)
              ltac:(rewrite /P13;
                    rewrite upd_ne; [| reg_neq];
                    rewrite /P12 upd_eq; reflexivity)
              ltac:(rewrite /P13 /P12 /P11 /P10 /P9 /P8 /P7 /P6 /P5;
                    repeat (rewrite upd_ne; [| reg_neq]);
                    rewrite /P4 upd_eq;
                    rewrite /P3 /P2 /W1;
                    repeat (rewrite upd_ne; [| reg_neq]);
                    apply add_vec_zero_l)
              ltac:(rewrite /P13 /P12 /P11 /P10 /P9 /P8 /P7 /P6;
                    repeat (rewrite upd_ne; [| reg_neq]);
                    rewrite /P5 upd_eq;
                    rewrite /P4 /P3 /P2 /W1;
                    repeat (rewrite upd_ne; [| reg_neq]);
                    apply add_vec_zero_l)
              ltac:(rewrite /P13 /P12;
                    repeat (rewrite upd_ne; [| reg_neq]);
                    rewrite /P11 upd_eq;
                    apply bv_eq; vm_compute; reflexivity)
              ltac:(rewrite /P13 upd_eq; vm_compute; reflexivity)
              ltac:(peel_reg)
              ltac:(peel_reg)
              ltac:(peel_reg)
              ltac:(peel_reg)
              eq_refl Hrep (pt_present_mono_refl t) ltac:(lia)
              Hinv0
              with "Hcg Hcnt Htext Hpc
                    Hc72 Hc64 Hc56 Hc48 Hc40 Hc32 Hc24 Hc16 Hc08 [S10]
                    Hptree Henv [-]").
    iExact "S10".
    (* the loop's own [wp_next]-wrapped continuation is stated over its OWN
       fresh [let va/pa/vpn0/ppn0/ret_tgt := ...] (all definitionally the SAME
       as ours, folded through the SAME [mm]) -- matching it against our own
       (differently-folded) "Hcont" through iApply's automatic "with" list is
       exactly the FOLDED-local trap (durable-notes: "conversion does the
       delta", an [exact]/elaborated application sees through a let-bound
       local where iApply's matcher does not).  Peel both wp_next's by hand
       and finish every "%"-obligation with a bare [exact] instead, which
       goes through ordinary term elaboration (full conversion) rather than
       the automatic matcher. *)
    iIntros (CIDf Hcrossf mr t' kf g)
      "Hcgf Hcntf Hpcf Hptreef %Hnodesf Henvf %Hcsf %Hbasef %Hrepf %Hpresf %Hmissf %Hpayf".
    iSpecialize ("Hcont" $! CIDf with "[%]"); [wp_next_chain|].
    iApply ("Hcont" $! mr t' kf g
              with "Hcgf Hcntf Hpcf Hptreef [%] Henvf [%] [%] [%] [%] [%] [%]").
    { exact Hnodesf. }
    { exact Hcsf. }
    { exact Hbasef. }
    { exact Hrepf. }
    { exact Hpresf. }
    { exact Hmissf. }
    { exact Hpayf. }
  Qed.

End ProofMappages.

End MappagesProof.
