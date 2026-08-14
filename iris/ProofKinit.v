(* ProofKinit.v -- the whole-function WP for xv6's kinit() over the
   SIE-agnostic sconf world.  kinit() = initlock(&kmem.lock, "kmem") then
   freerange(end, PHYSTOP), with the allocator invariant [is_kmem] and the boot
   page-count token [kalloc_avail γk (Some 0)] freshly allocated in between (the
   "newlock" ghost step).  Straight-line (no loop): a 16-byte frame, two jal
   sub-calls, and the ghost allocation.  Post hands back the freshly minted
   [is_kmem γl γk lk fl] and [kalloc_avail γk (Some (length ps))] -- the count of
   pages freerange just freed. *)
From Stdlib Require Import Eqdep_dec ZArith Lia List.
From stdpp Require Import gmap list list_monad bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import excl.
From iris.base_logic.lib Require Import ghost_var gen_heap invariants own.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import RegFile.
Require Import WpNext.
Require Import CpuOwn.
Require Import WpMmodeLeafBase.
Require Import RiscvExtras.
Require Import SmodeCore.
Require Import StackOwn CalleeSaved.
Require Import KernelDataInv.
Require Import WpLock.
Require Import KallocInv.
Require Import IntrDefs WpSmodeIntr.
Require Import IntrDefs.
Require Import WpSconfAlu WpSconfMem WpSconfCtl.
Require Import SpecInitlock SpecFreerange.
Require Import CodeKinit.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SpecKinit.
Require Import KernelRvcDecode.
Local Open Scope Z_scope.
Import Defs.

Module KinitProof (Freerange : FREERANGE) (Initlock : INITLOCK) : KINIT.

Section ProofKinit.
  Context `{!riscvGS Σ, !lockG Σ, !sieG Σ, !kallocG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.


  Lemma wp_kinit_sconf
      (m : regfile)
      (ps : list (mword 64)) (K ncnt : nat) (eb : bool) (pcur : mword 64) (C : iProp Σ)
      (vlock : bv 32) (vname vcpu : bv 64) (b : bool) (lks : gset nat)
    : wp_kinit_sconf_body m ps K ncnt eb pcur C vlock vname vcpu b lks.
  Proof.
    cbv beta delta [wp_kinit_sconf_body].
    intros pcE ret_tgt lk fl c_name c_cpu endaddr phystop s1entry
      HK Hncnt Hprun Hlkbelow.
    pose (sp0 := (m !!! Regidx csp_rs1 : mword 64)).
    set (spr := add_vec sp0 (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6)))).
    iIntros "Hcg Hcnt #Htext #Hkdata Hpc #Hpanic Hlock Hname Hcpu Hflw Hpages Hcont".
    (* the "kmem" string literal, read out of the kernel's data image *)
    assert (Hkmem : forall j bt, cstring_bytes "kmem"%string !! j = Some bt ->
                      KernelData.kernel_data !! (0x80007040 + Z.of_nat j)%Z = Some bt).
    { intros j bt Hj.
      do 5 (destruct j as [|j];
            [vm_compute in Hj; injection Hj as <-; vm_compute; reflexivity |]);
      vm_compute in Hj; discriminate. }
    iPoseProof (kernel_data_string 0x80007040 "kmem"%string _ eq_refl ltac:(unfold text_end; lia) Hkmem
                  with "Hkdata") as "#Hstr".
    assert (Hspr2 : spr = pa_stk sp0 2).
    { unfold spr, pa_stk, add_vec_int. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb1 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) = pa_stk sp0 1).
    { unfold spr, sp0, pa_stk, add_vec_int. rewrite pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb2 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000"))) = pa_stk sp0 2).
    { unfold spr, sp0, pa_stk, add_vec_int. rewrite pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    (* ===== PROLOGUE: 2-slot frame trade (move_down 2) + save ra/s0 ===== *)
    set (R1 := <[Regidx csp_rs1 := regval_into_reg (add_vec sp0 (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6))))]> m).
    assert (Hspm : m !!! Regidx csp_rs1 = sp0) by reflexivity.
    assert (Hpush : add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6))) = pa_stk (m !!! Regidx csp_rs1) 2).
    { unfold pa_stk, add_vec_int. apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    iPoseProof (kii_00 with "Htext") as "Hi00".
    iApply (wp_caddi_sp_push_s_sconf pcE (mword_of_int 48 : mword 6) m K 2 b ltac:(lia) Hpush
              with "Hcg Hpc Hi00").
    iIntros (CID1 Hs1) "Hcg Hframe Hpc".
    iClear "Hi00".
    iEval (rewrite Hspm) in "Hframe".
    change (<[Regidx csp_rs1 := regval_into_reg (add_vec sp0 (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6))))]> m) with R1.
    assert (HspR1 : R1 !!! Regidx csp_rs1 = spr) by (rewrite /R1 upd_eq; reflexivity).
    iEval (rewrite stack_own_slots; cbn [seq]) in "Hframe".
    iDestruct "Hframe" as "(S1 & S2 & _)".
    iDestruct "S1" as (vra0) "Hras". iDestruct "S2" as (vs00) "Hs0s".
    assert (Hpp02 : add_vec_int (pcE : mword 64) 2 = mword_of_int (KernelSyms.kinit + 0x02)) by (unfold pcE; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp02) in "Hpc".
    iPoseProof (kii_02 with "Htext") as "Hi02".
    (* +0x02 c.sdsp ra,8(sp) *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.kinit + 0x02)) (mword_of_int 1 : mword 6) (mword_of_int 1 : mword 5)
              R1 (K - 2)%nat vra0 b with "Hcg Hpc Hi02 [Hras]").
    { iEval (rewrite HspR1 Hb1). iExact "Hras". }
    iIntros (CID2 Hs2) "Hcg Hpc Hras".
    iClear "Hi02".
    iEval (rewrite HspR1 Hb1) in "Hras".
    iEval (rgne) in "Hras".
    assert (Hrav : R1 !!! Regidx (mword_of_int 1 : mword 5) = m !!! Regidx (mword_of_int 1 : mword 5))
      by (rewrite /R1 upd_ne; [reflexivity | vm_compute; discriminate]).
    iEval (rewrite Hrav) in "Hras".
    assert (Hpp04 : add_vec_int (mword_of_int (KernelSyms.kinit + 0x02) : mword 64) 2 = mword_of_int (KernelSyms.kinit + 0x04)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp04) in "Hpc".
    iPoseProof (kii_04 with "Htext") as "Hi04".
    (* +0x04 c.sdsp s0,0(sp) *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.kinit + 0x04)) (mword_of_int 0 : mword 6) (mword_of_int 8 : mword 5)
              R1 (K - 2)%nat vs00 b with "Hcg Hpc Hi04 [Hs0s]").
    { iEval (rewrite HspR1 Hb2). iExact "Hs0s". }
    iIntros (CID3 Hs3) "Hcg Hpc Hs0s".
    iClear "Hi04".
    iEval (rewrite HspR1 Hb2) in "Hs0s".
    iEval (rgne) in "Hs0s".
    assert (Hs0v : R1 !!! Regidx (mword_of_int 8 : mword 5) = m !!! Regidx (mword_of_int 8 : mword 5))
      by (rewrite /R1 upd_ne; [reflexivity | vm_compute; discriminate]).
    iEval (rewrite Hs0v) in "Hs0s".
    assert (Hpp06 : add_vec_int (mword_of_int (KernelSyms.kinit + 0x04) : mword 64) 2 = mword_of_int (KernelSyms.kinit + 0x06)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp06) in "Hpc".
    iPoseProof (kii_06 with "Htext") as "Hi06".
    (* +0x06 c.addi4spn s0,sp,16 *)
    iApply (wp_caddi4spn_s_sconf (mword_of_int (KernelSyms.kinit + 0x06)) (Cregidx (mword_of_int 0)) (mword_of_int 4 : mword 8) (mword_of_int 8 : mword 5)
              R1 (K - 2)%nat b ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi06").
    iIntros (CID4 Hs4) "Hcg Hpc".
    iClear "Hi06".
    set (R2 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg (add_vec (R1 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 4 : mword 8))))]> R1).
    assert (Hpp08 : add_vec_int (mword_of_int (KernelSyms.kinit + 0x06) : mword 64) 2 = mword_of_int (KernelSyms.kinit + 0x08)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp08) in "Hpc".
    iPoseProof (kii_08 with "Htext") as "Hi08".
    (* ===== compute a1 = &"kmem", a0 = &kmem (0x08..0x14) ===== *)
    (* +0x08 auipc a1,0x6 *)
    iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.kinit + 0x08)) (mword_of_int 11 : mword 5) (mword_of_int 6 : mword 20)
              R2 (K - 2)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi08").
    iIntros (CID5 Hs5) "Hcg Hpc".
    iClear "Hi08".
    set (R3 := <[Regidx (mword_of_int 11 : mword 5) := regval_into_reg (add_vec (mword_of_int (KernelSyms.kinit + 0x08) : mword 64) (auipc_off (mword_of_int 6 : mword 20)))]> R2).
    assert (Hpp0c : add_vec_int (mword_of_int (KernelSyms.kinit + 0x08) : mword 64) 4 = mword_of_int (KernelSyms.kinit + 0x0c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0c) in "Hpc".
    iPoseProof (kii_0c with "Htext") as "Hi0c".
    (* +0x0c addi a1,a1,1386 *)
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.kinit + 0x0c)) (mword_of_int 11 : mword 5) (mword_of_int 11 : mword 5) (mword_of_int 1420 : mword 12)
              R3 (K - 2)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi0c").
    iIntros (CID6 Hs6) "Hcg Hpc".
    iClear "Hi0c".
    set (R4 := <[Regidx (mword_of_int 11 : mword 5) := regval_into_reg (add_vec (R3 !!! Regidx (mword_of_int 11 : mword 5)) (sign_extend' 64 (mword_of_int 1420 : mword 12)))]> R3).
    (* a1 now holds &"kmem" -- the string initlock is about to store *)
    assert (HR4a1 : R4 !!! Regidx (mword_of_int 11 : mword 5) = (mword_of_int 0x80007040 : mword 64)).
    { rewrite /R4 upd_eq. rewrite /R3 upd_eq. apply bv_eq; vm_compute; reflexivity. }
    assert (Hpp10 : add_vec_int (mword_of_int (KernelSyms.kinit + 0x0c) : mword 64) 4 = mword_of_int (KernelSyms.kinit + 0x10)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp10) in "Hpc".
    iPoseProof (kii_10 with "Htext") as "Hi10".
    (* +0x10 auipc a0,0x12 *)
    iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.kinit + 0x10)) (mword_of_int 10 : mword 5) (mword_of_int 18 : mword 20)
              R4 (K - 2)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi10").
    iIntros (CID7 Hs7) "Hcg Hpc".
    iClear "Hi10".
    set (R5 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg (add_vec (mword_of_int (KernelSyms.kinit + 0x10) : mword 64) (auipc_off (mword_of_int 18 : mword 20)))]> R4).
    assert (Hpp14 : add_vec_int (mword_of_int (KernelSyms.kinit + 0x10) : mword 64) 4 = mword_of_int (KernelSyms.kinit + 0x14)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp14) in "Hpc".
    iPoseProof (kii_14 with "Htext") as "Hi14".
    (* +0x14 addi a0,a0,-2018  (a0 := &kmem = lk) *)
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.kinit + 0x14)) (mword_of_int 10 : mword 5) (mword_of_int 10 : mword 5) (mword_of_int 2252 : mword 12)
              R5 (K - 2)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi14").
    iIntros (CID8 Hs8) "Hcg Hpc".
    iClear "Hi14".
    set (R6 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg (add_vec (R5 !!! Regidx (mword_of_int 10 : mword 5)) (sign_extend' 64 (mword_of_int 2252 : mword 12)))]> R5).
    assert (Hpp18 : add_vec_int (mword_of_int (KernelSyms.kinit + 0x14) : mword 64) 4 = mword_of_int (KernelSyms.kinit + 0x18)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp18) in "Hpc".
    assert (HR6a0 : R6 !!! Regidx (mword_of_int 10 : mword 5) = lk).
    { rewrite /R6 upd_eq. rewrite /R5 upd_eq.
      unfold lk. apply bv_eq; vm_compute; reflexivity. }
    assert (HR6sp : R6 !!! Regidx csp_rs1 = spr).
    { rewrite /R6 upd_ne; [| vm_compute; discriminate].
      rewrite /R5 upd_ne; [| vm_compute; discriminate].
      rewrite /R4 upd_ne; [| vm_compute; discriminate].
      rewrite /R3 upd_ne; [| vm_compute; discriminate].
      rewrite /R2 upd_ne; [| vm_compute; discriminate]. exact HspR1. }
    iPoseProof (kii_18 with "Htext") as "Hi18".
    (* ===== jal initlock ===== *)
    (* +0x18 jal ra,initlock *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.kinit + 0x18)) (mword_of_int 1 : mword 5) (mword_of_int 118 : mword 21)
              R6 (K - 2)%nat b ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi18").
    iIntros (CID9 Hs9) "Hcg Hpc".
    iClear "Hi18".
    set (R7 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.kinit + 0x18) : mword 64) 4)]> R6).
    assert (Htgtil : add_vec (mword_of_int (KernelSyms.kinit + 0x18) : mword 64) (sign_extend' 64 (mword_of_int 118 : mword 21)) = mword_of_int KernelSyms.initlock) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtil) in "Hpc".
    assert (HR7a0 : R7 !!! Regidx (mword_of_int 10 : mword 5) = lk)
      by (rewrite /R7 upd_ne; [exact HR6a0 | vm_compute; discriminate]).
    assert (HR7a1 : R7 !!! Regidx (mword_of_int 11 : mword 5) = (mword_of_int 0x80007040 : mword 64)).
    { rewrite /R7 upd_ne; [| vm_compute; discriminate].
      rewrite /R6 upd_ne; [| vm_compute; discriminate].
      rewrite /R5 upd_ne; [exact HR4a1 | vm_compute; discriminate]. }
    assert (HR7sp : R7 !!! Regidx csp_rs1 = spr)
      by (rewrite /R7 upd_ne; [exact HR6sp | vm_compute; discriminate]).
    assert (HR7ra : R7 !!! Regidx (mword_of_int 1 : mword 5) = add_vec_int (mword_of_int (KernelSyms.kinit + 0x18) : mword 64) 4)
      by (rewrite /R7; apply upd_eq).
    (* initlock(&kmem.lock, "kmem") : owns lk's 3 struct fields, returns them init'd.
       [Hcnt] is not one of its arguments (initlock takes no [cpu_own]), so no
       transport is needed here -- unlike the freerange call below. *)
    iApply (Initlock.wp_initlock_sconf R7 vlock vname vcpu "kmem"%string (K - 2) b pcur
              ltac:(lia)
              with "Hcg Htext Hpc [] [Hlock] [Hname] [Hcpu]").
    { iEval (rewrite HR7a1). iExact "Hstr". }
    { iEval (rewrite HR7a0). iExact "Hlock". }
    { iEval (rewrite HR7a0). iExact "Hname". }
    { iEval (rewrite HR7a0). iExact "Hcpu". }
    iIntros (CIDil Hsil mil) "Hcg Hpc %Hilcs Hlock Hlname Hcpu".
    iEval (rewrite HR7a0) in "Hlock". iEval (rewrite HR7a0 HR7a1) in "Hlname". iEval (rewrite HR7a0) in "Hcpu".
    iMod (lock_name_intro with "Hstr Hlname") as "#Hlnm".
    assert (Hpcil : ret_pc (R7 !!! Regidx (mword_of_int 1 : mword 5)) = mword_of_int (KernelSyms.kinit + 0x1c)).
    { rewrite HR7ra. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hpcil) in "Hpc".
    (* ===== newlock ghost: allocate is_kmem γl γk lk fl + kalloc_avail (Some 0);
       initlock's two zeroed words (locked + cpu) go INTO the invariant and
       every hart's not-holder ticket comes out.  Pure ghost step, unaffected
       by which hart we are on. ===== *)
    iApply fupd_wp.
    iMod (kalloc_avail_alloc 0%nat) as (γk) "[Havail Hauth]".
    iAssert (kmem_res γk fl) with "[Hflw Hauth]" as "HR".
    { iApply (kmem_res_close γk fl nullp []). rewrite /word_at.
      iSplitL "Hflw"; [iExact "Hflw" |]. iSplitR "Hauth"; [iPureIntro; reflexivity | iExact "Hauth"]. }
    iMod (newlock ⊤ lk "kmem"%string (kmem_res γk fl)
            with "Hlnm Hlock Hcpu HR") as (γl) "#Hkmem".
    iModIntro.
    pose proof Hilcs as Hilcs_full. unfold callee_saved in Hilcs.
    destruct Hilcs as (Hilsp & Hils0 & Hils1 & Hils2 & Hils3 & Hils4 & Hils5 & Hils6 & Hils7 & Hils8 & Hils9 & Hils10 & Hils11).
    assert (Hmilsp : mil !!! Regidx csp_rs1 = spr) by (rewrite Hilsp; exact HR7sp).
    iPoseProof (kii_1c with "Htext") as "Hi1c".
    (* ===== compute a1 = PHYSTOP, a0 = end (0x1c..0x24), then jal freerange ===== *)
    (* +0x1c li a1,17 *)
    iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.kinit + 0x1c)) (mword_of_int 11 : mword 5) (mword_of_int 17 : mword 6) (mword_of_int 17 : mword 64)
              mil (K - 2)%nat b ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi1c").
    iIntros (CID10 Hs10) "Hcg Hpc".
    iClear "Hi1c".
    set (R8 := <[Regidx (mword_of_int 11 : mword 5) := regval_into_reg (mword_of_int 17 : mword 64)]> mil).
    assert (Hpp1e : add_vec_int (mword_of_int (KernelSyms.kinit + 0x1c) : mword 64) 2 = mword_of_int (KernelSyms.kinit + 0x1e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp1e) in "Hpc".
    iPoseProof (kii_1e with "Htext") as "Hi1e".
    (* +0x1e slli a1,a1,27 *)
    iApply (wp_cslli_s_sconf (mword_of_int (KernelSyms.kinit + 0x1e)) (Regidx (mword_of_int 11)) (mword_of_int 11 : mword 5) (mword_of_int 27 : mword 6)
              R8 (K - 2)%nat b ltac:(reflexivity) ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi1e").
    iIntros (CID11 Hs11) "Hcg Hpc". iEval (rgne) in "Hcg".
    iClear "Hi1e".
    set (R9 := <[Regidx (mword_of_int 11 : mword 5) := regval_into_reg (shift_bits_left (R8 !!! Regidx (mword_of_int 11 : mword 5)) (subrange_vec_dec (mword_of_int 27 : mword 6) (Z.sub log2_xlen 1) 0))]> R8).
    assert (Hpp20 : add_vec_int (mword_of_int (KernelSyms.kinit + 0x1e) : mword 64) 2 = mword_of_int (KernelSyms.kinit + 0x20)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp20) in "Hpc".
    assert (HR9a1 : R9 !!! Regidx (mword_of_int 11 : mword 5) = phystop).
    { rewrite /R9 upd_eq. rewrite /R8 upd_eq.
      unfold phystop. apply bv_eq; vm_compute; reflexivity. }
    iPoseProof (kii_20 with "Htext") as "Hi20".
    (* +0x20 auipc a0,0x23 *)
    iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.kinit + 0x20)) (mword_of_int 10 : mword 5) (mword_of_int 35 : mword 20)
              R9 (K - 2)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi20").
    iIntros (CID12 Hs12) "Hcg Hpc".
    iClear "Hi20".
    set (R10 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg (add_vec (mword_of_int (KernelSyms.kinit + 0x20) : mword 64) (auipc_off (mword_of_int 35 : mword 20)))]> R9).
    assert (Hpp24 : add_vec_int (mword_of_int (KernelSyms.kinit + 0x20) : mword 64) 4 = mword_of_int (KernelSyms.kinit + 0x24)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp24) in "Hpc".
    iPoseProof (kii_24 with "Htext") as "Hi24".
    (* +0x24 addi a0,a0,-1474  (a0 := end) *)
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.kinit + 0x24)) (mword_of_int 10 : mword 5) (mword_of_int 10 : mword 5) (mword_of_int 2796 : mword 12)
              R10 (K - 2)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi24").
    iIntros (CID13 Hs13) "Hcg Hpc".
    iClear "Hi24".
    set (R11 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg (add_vec (R10 !!! Regidx (mword_of_int 10 : mword 5)) (sign_extend' 64 (mword_of_int 2796 : mword 12)))]> R10).
    assert (Hpp28 : add_vec_int (mword_of_int (KernelSyms.kinit + 0x24) : mword 64) 4 = mword_of_int (KernelSyms.kinit + 0x28)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp28) in "Hpc".
    assert (HR11a0 : R11 !!! Regidx (mword_of_int 10 : mword 5) = endaddr).
    { rewrite /R11 upd_eq. rewrite /R10 upd_eq.
      unfold endaddr. apply bv_eq; vm_compute; reflexivity. }
    assert (HR11a1 : R11 !!! Regidx (mword_of_int 11 : mword 5) = phystop).
    { rewrite /R11 upd_ne; [| vm_compute; discriminate].
      rewrite /R10 upd_ne; [exact HR9a1 | vm_compute; discriminate]. }
    assert (HR11sp : R11 !!! Regidx csp_rs1 = spr).
    { rewrite /R11 upd_ne; [| vm_compute; discriminate].
      rewrite /R10 upd_ne; [| vm_compute; discriminate].
      rewrite /R9 upd_ne; [| vm_compute; discriminate].
      rewrite /R8 upd_ne; [exact Hmilsp | vm_compute; discriminate]. }
    iPoseProof (kii_28 with "Htext") as "Hi28".
    (* +0x28 jal ra,freerange *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.kinit + 0x28)) (mword_of_int 1 : mword 5) (mword_of_int 2097040 : mword 21)
              R11 (K - 2)%nat b ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi28").
    iIntros (CID14 Hs14) "Hcg Hpc".
    iClear "Hi28".
    set (R12 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.kinit + 0x28) : mword 64) 4)]> R11).
    assert (Htgtfr : add_vec (mword_of_int (KernelSyms.kinit + 0x28) : mword 64) (sign_extend' 64 (mword_of_int 2097040 : mword 21)) = mword_of_int KernelSyms.freerange) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtfr) in "Hpc".
    assert (HR12a0 : R12 !!! Regidx (mword_of_int 10 : mword 5) = endaddr)
      by (rewrite /R12 upd_ne; [exact HR11a0 | vm_compute; discriminate]).
    assert (HR12a1 : R12 !!! Regidx (mword_of_int 11 : mword 5) = phystop)
      by (rewrite /R12 upd_ne; [exact HR11a1 | vm_compute; discriminate]).
    assert (HR12sp : R12 !!! Regidx csp_rs1 = spr)
      by (rewrite /R12 upd_ne; [exact HR11sp | vm_compute; discriminate]).
    assert (HR12ra : R12 !!! Regidx (mword_of_int 1 : mword 5) = add_vec_int (mword_of_int (KernelSyms.kinit + 0x28) : mword 64) 4)
      by (rewrite /R12; apply upd_eq).
    (* ---- THE CALL.  [Hcnt : cpu_own ncnt eb pcur C b] was introduced at this
       function's ENTRY hart; the fourteen plain instructions between entry and
       here (the prologue, the two relocation pairs, the two jal's own
       argument setup) each threaded through a FRESH, universally quantified
       hart (CID1..CID14), so freerange wants [Hcnt] at CID14.
       [cpu_own_transport] moves it there in ONE line, no case split on [b] --
       initlock (just above) needed no such transport since its contract does
       not mention [cpu_own] at all. ---- *)
    iDestruct (cpu_own_transport CID CID14 ncnt eb pcur C b ltac:(wp_next_chain)
                 with "Hcnt") as "Hcnt".
    (* freerange(end, PHYSTOP) : consumes the pages into the lock, threads the count.

       [SpecFreerange.wp_freerange_sconf_body] wants [panic_wp_any] (added by
       commit 7865e4e, "explicit cpuid: propagate p into 23 contracts, and
       panic_wp_any with it"); [SpecKinit.wp_kinit_sconf_body] now threads the
       same [panic_wp_any] (that sweep missed this one contract -- fixed
       above), so "Hpanic" hands it straight through with no conversion. *)
    iApply (Freerange.wp_freerange_sconf γl γk lk fl R12 ps (K - 2) ncnt eb pcur C b lks
              ltac:(lia) Hncnt
              ltac:(reflexivity) ltac:(reflexivity)
              ltac:(rewrite HR12a1 HR12a0; exact Hprun) Hlkbelow
              with "Hcg Hcnt Htext Hpc Hkmem Hpages [Hpanic] [Havail]").
    all: try lkbelow.
    { iExact "Hpanic". }
    { iExact "Havail". }
    iIntros (CIDfr Hsfr mfr) "Hcg Hcnt Hpc %Hfrcs Havail".
    assert (Hpcfr : ret_pc (R12 !!! Regidx (mword_of_int 1 : mword 5)) = mword_of_int (KernelSyms.kinit + 0x2c)).
    { rewrite HR12ra. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hpcfr) in "Hpc".
    pose proof Hfrcs as Hfrcs_full. unfold callee_saved in Hfrcs.
    destruct Hfrcs as (Hfrsp & Hfrs0 & Hfrs1 & Hfrs2 & Hfrs3 & Hfrs4 & Hfrs5 & Hfrs6 & Hfrs7 & Hfrs8 & Hfrs9 & Hfrs10 & Hfrs11).
    assert (Hfrsp' : mfr !!! Regidx csp_rs1 = spr) by (rewrite Hfrsp; exact HR12sp).
    (* ===== EPILOGUE (0x2c..0x32): restore ra/s0, frame trade back (move_up 2), ret ===== *)
    assert (Hpp2e : add_vec_int (mword_of_int (KernelSyms.kinit + 0x28) : mword 64) 4 = mword_of_int (KernelSyms.kinit + 0x2c)) by (apply bv_eq; vm_compute; reflexivity).
    iPoseProof (kii_2c with "Htext") as "Hi2c".
    (* +0x2c c.ldsp ra,8(sp) *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.kinit + 0x2c)) (mword_of_int 1 : mword 6) (mword_of_int 1 : mword 5)
              mfr (K - 2)%nat (m !!! Regidx (mword_of_int 1 : mword 5)) b (dqm:=DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi2c [Hras]").
    { iEval (rewrite -Hb1 -Hfrsp') in "Hras". iExact "Hras". }
    iIntros (CID15 Hs15) "Hcg Hpc Hras".
    iClear "Hi2c".
    iEval (rewrite Hfrsp' Hb1) in "Hras".
    set (E1 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 1 : mword 5))]> mfr).
    assert (HE1sp : E1 !!! Regidx csp_rs1 = spr) by (rewrite /E1 upd_ne; [exact Hfrsp' | vm_compute; discriminate]).
    assert (Hpp2e' : add_vec_int (mword_of_int (KernelSyms.kinit + 0x2c) : mword 64) 2 = mword_of_int (KernelSyms.kinit + 0x2e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp2e') in "Hpc".
    iPoseProof (kii_2e with "Htext") as "Hi2e".
    (* +0x2e c.ldsp s0,0(sp) *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.kinit + 0x2e)) (mword_of_int 0 : mword 6) (mword_of_int 8 : mword 5)
              E1 (K - 2)%nat (m !!! Regidx (mword_of_int 8 : mword 5)) b (dqm:=DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi2e [Hs0s]").
    { iEval (rewrite -Hb2 -HE1sp) in "Hs0s". iExact "Hs0s". }
    iIntros (CID16 Hs16) "Hcg Hpc Hs0s".
    iClear "Hi2e".
    iEval (rewrite HE1sp Hb2) in "Hs0s".
    set (E2 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 8 : mword 5))]> E1).
    assert (HE2sp : E2 !!! Regidx csp_rs1 = spr) by (rewrite /E2 upd_ne; [exact HE1sp | vm_compute; discriminate]).
    assert (Hpp30 : add_vec_int (mword_of_int (KernelSyms.kinit + 0x2e) : mword 64) 2 = mword_of_int (KernelSyms.kinit + 0x30)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp30) in "Hpc".
    (* Hras/Hs0s are already at [pa_stk sp0 1..2] -- ready for the frame rebuild *)
    (* +0x30 c.addi sp,16 -- the frame trade back (move_up 2) *)
    set (E3 := <[Regidx csp_rs1 := regval_into_reg (add_vec (E2 !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6))))]> E2).
    assert (HE3csp : E3 !!! Regidx csp_rs1 = sp0).
    { rewrite /E3 upd_eq. rewrite HE2sp. unfold regval_into_reg, spr, sp0.
      apply frame_cancel_16. }
    assert (Hwv : add_vec (E2 !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6))) = sp0).
    { rewrite -HE3csp /E3 upd_eq. reflexivity. }
    assert (Hpop : E2 !!! Regidx csp_rs1
                   = pa_stk (add_vec (E2 !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6)))) 2).
    { rewrite Hwv HE2sp. exact Hspr2. }
    iAssert (stack_own sp0 2) with "[Hras Hs0s]" as "Hframe".
    { rewrite stack_own_slots. cbn [seq].
      iSplitL "Hras"; [iExists _; iExact "Hras"|].
      iSplitL "Hs0s"; [iExists _; iExact "Hs0s"|]. done. }
    iEval (rewrite -Hwv) in "Hframe".
    iPoseProof (kii_30 with "Htext") as "Hi30".
    iApply (wp_caddi_sp_pop_s_sconf (mword_of_int (KernelSyms.kinit + 0x30)) (mword_of_int 16 : mword 6) E2 (K - 2)%nat 2 b Hpop
              with "Hcg Hpc Hi30 Hframe").
    iIntros (CID17 Hs17) "Hcg Hpc".
    iClear "Hi30".
    assert (Hnk : ((K - 2) + 2)%nat = K) by lia.
    iEval (rewrite Hnk) in "Hcg".
    change (<[Regidx csp_rs1 := regval_into_reg (add_vec (E2 !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6))))]> E2) with E3.
    assert (Hpp32 : add_vec_int (mword_of_int (KernelSyms.kinit + 0x30) : mword 64) 2 = mword_of_int (KernelSyms.kinit + 0x32)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp32) in "Hpc".
    (* +0x32 c.ret *)
    assert (HE3ra : E3 !!! Regidx (mword_of_int 1 : mword 5) = m !!! Regidx (mword_of_int 1 : mword 5)).
    { rewrite /E3 upd_ne; [| vm_compute; discriminate].
      rewrite /E2 upd_ne; [| vm_compute; discriminate].
      rewrite /E1 upd_eq; reflexivity. }
    iPoseProof (kii_32 with "Htext") as "Hi32".
    iApply (wp_cret_s_sconf (mword_of_int (KernelSyms.kinit + 0x32)) (mword_of_int 1 : mword 5) E3 K b
              ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi32").
    iIntros (CID18 Hs18) "Hcg Hpc".
    iClear "Hi32".
    assert (Hretf : ret_pc (E3 !!! Regidx (mword_of_int 1 : mword 5)) = ret_tgt)
      by (rewrite HE3ra; reflexivity).
    iEval (rewrite Hretf) in "Hpc".
    (* [cpu_own] again: it was delivered at CIDfr by freerange's own [wp_next];
       four more plain instructions (the epilogue) have moved the hart to
       CID18. *)
    iDestruct (cpu_own_transport CIDfr CID18 ncnt eb pcur C b ltac:(wp_next_chain)
                 with "Hcnt") as "Hcnt".
    iSpecialize ("Hcont" $! CID18 with "[%]"); [wp_next_chain|].
    iApply ("Hcont" $! γl γk E3 with "Hcg Hcnt Hpc [%] Hkmem Havail").
    (* callee_saved m E3: the two sub-calls preserve s1..s11; the epilogue
       restores sp/s0, and ra (caller-saved) is irrelevant. *)
    assert (Hthread : forall c : mword 5, is_cs_idx c = true ->
              c <> mword_of_int 1 -> c <> csp_rs1 -> c <> mword_of_int 8 ->
              E3 !!! Regidx c = m !!! Regidx c).
    { intros c Hc N1 Nsp N8.
      pose proof (is_cs_idx_true_neq (mword_of_int 10 : mword 5) c ltac:(vm_compute; reflexivity) Hc) as Na0.
      pose proof (is_cs_idx_true_neq (mword_of_int 11 : mword 5) c ltac:(vm_compute; reflexivity) Hc) as Na1.
      rewrite /E3 upd_ne; [| congruence].
      rewrite /E2 upd_ne; [| congruence].
      rewrite /E1 upd_ne; [| congruence].
      rewrite (callee_saved_lookup Hfrcs_full c Hc).
      rewrite /R12 upd_ne; [| congruence].
      rewrite /R11 upd_ne; [| congruence].
      rewrite /R10 upd_ne; [| congruence].
      rewrite /R9 upd_ne; [| congruence].
      rewrite /R8 upd_ne; [| congruence].
      rewrite (callee_saved_lookup Hilcs_full c Hc).
      rewrite /R7 upd_ne; [| congruence].
      rewrite /R6 upd_ne; [| congruence].
      rewrite /R5 upd_ne; [| congruence].
      rewrite /R4 upd_ne; [| congruence].
      rewrite /R3 upd_ne; [| congruence].
      rewrite /R2 upd_ne; [| congruence].
      rewrite /R1 upd_ne; [reflexivity | congruence]. }
    unfold callee_saved.
    split. { rewrite HE3csp. reflexivity. }
    split. { rewrite /E3 upd_ne; [| vm_compute; discriminate].
             rewrite /E2 upd_eq; reflexivity. }
    repeat split; apply Hthread; vm_compute; first [reflexivity | discriminate].
  Qed.

End ProofKinit.

End KinitProof.
