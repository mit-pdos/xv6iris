(* ProofForkret.v -- forkret(), proved: the 24 instructions of the
   already-booted path, ending in the CLOSED trap loop.

   A functor over its three callees' interfaces (myproc, release,
   prepare_return) and over [USERRET_CLOSED], because forkret's last
   instruction is not a return: the [c.jalr a5] at +0x8e enters userret and
   the machine never comes back.

   THREE THINGS THAT ARE NOT PLUMBING.

   * THE INDEX CHANGES AT THE release, NOT BEFORE.  forkret is entered
     holding p->lock, so everything up to +0x10 runs at [b = false];
     [release]'s pop_off restores the base enable, so from +0x14 on the index
     is the caller's [eb] and every step may rebind the hart.  The three
     resources that cross that stretch -- the per-cpu bundle and the two
     [_ext] halves of the arm -- are transported ONCE, at the point of use
     (before the [jal prepare_return]), with [wp_next_chain] chaining the
     whole run of binders.

   * THE FRAME GOES BACK INTO THE FREE-STACK CLAIM.  forkret never runs its
     epilogue, so the six slots it pushed at +0x00 are still carved out at
     the [c.jalr] -- and the residue that parks across user mode claims the
     kernel stack WHOLE ([UsertrapRes.ut_stack ksp av], anchored at the top,
     which is what uservec reloads sp to on the next trap).  So the walk
     rebundles the three saved words and the three scratch slots and merges
     them back ([stack_own_app]); the frame's contents are dead by then, and
     nothing ever returns to it.

   * THE EXIT IS [ut_ret2]'s, RE-USED.  What prepare_return hands back is
     what the trap-side residue is made of, and the derivation is the same
     one usertrap's tail performs: the sret-ready mstatus is DERIVED
     ([UsertrapRes.ut_exit_ms_ok]) from the loose SIE quarter's agreement
     with [sconf]'s half and the travelling sret mirror's with [sconf]'s
     tie.  Here it is assembled into [ut_trap] and immediately reopened by
     [ut_trap_tlb_open], which is what hands userret its [tlb_res_pt] and
     leaves the PARKED residue the caller's wand turns into [URes]. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExtras.
Require Import PageGeom.
Require Import RegFile HartTp WpNext CpuOwn CalleeSaved.
Require Import WpMmodeLeafBase.
Require Import SmodeCore.
Require Import StackOwn.
Require Import KernelRvcDecode.
Require Import WpGprCsrwA.
Require Import WpSconfAlu WpSconfMem WpSconfCtl WpSconfBtype.
Require Import WpSmodeIntr.   (* [wp_cli_s_sconf] *)
Require Import WpKvminithart.      (* [kvi_satp_word] and its three facts *)
Require Import IntrDefs.
Require Import WpLock.
Require Import KptShare UserretDefs.
Require Import UserPtTree.
Require Import ProcGeom.
Require Import ProcPtOwn.
Require Import FdSlots FileInvDefs.
Require Import ProcInv.
Require Import DiskPtsto WpUart FsBlocks LogInv FsCrash KallocInv.
Require Import BioDefs.
Require Import IrefSlots InodeRegion ProcAvail.
Require Import CodeForkret.
Require Import SpecMyproc SpecRelease SpecPrepareReturn.
Require Import SpecUserretClosed.
Require Import UsertrapRes.
Require Import SpecForkret ProofForkretParts ProofPrepareReturnParts.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Import Defs.
Local Open Scope Z_scope.
Set Printing Depth 40.

Module ForkretProof (MP : MYPROC) (RL : RELEASE) (PR : PREPARE_RETURN)
                    (UC : USERRET_CLOSED) : FORKRET.

(* register indices and the two scripts, at MODULE level: an [Ltac] defined
   inside a section is discharged over its variables and unusable in the
   next one. *)
Notation Rra := (mword_of_int 1  : mword 5).
Notation Rs0 := (mword_of_int 8  : mword 5).
Notation Rs1 := (mword_of_int 9  : mword 5).
Notation Ra0 := (mword_of_int 10 : mword 5).
Notation Ra3 := (mword_of_int 13 : mword 5).
Notation Ra4 := (mword_of_int 14 : mword 5).
Notation Ra5 := (mword_of_int 15 : mword 5).

Ltac reg_neq :=
  lazymatch goal with |- ?a <> ?b =>
    tryif unify a b then fail else (vm_compute; discriminate) end.

Ltac pcw := apply bv_eq; vm_compute; reflexivity.

Section Res.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !bioG Σ,
            !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ, !fsCrashG Σ,
            !kallocG Σ, !irefslotG Σ, !pavG Σ, !iregG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  (* the residue is the closed loop's, re-exported unchanged *)
  Definition usertrap_res := UC.usertrap_res.
  Definition usertrap_res_parked := UC.usertrap_res_parked.
  Definition usertrap_res_tlb_close := UC.usertrap_res_tlb_close.
  Definition usertrap_res_tlb_open := UC.usertrap_res_tlb_open.
  Definition usertrap_res_bare := UC.usertrap_res_bare.
  Definition usertrap_res_pt_close := UC.usertrap_res_pt_close.
  Definition usertrap_res_pt_open := UC.usertrap_res_pt_open.
  Definition usertrap_res_bare_norm := UC.usertrap_res_bare_norm.
  Definition usertrap_res_csrs_open := UC.usertrap_res_csrs_open.
  Definition usertrap_res_sstc := UC.usertrap_res_sstc.
  Definition usertrap_res_tf_csrs_open := UC.usertrap_res_tf_csrs_open.
  Definition usertrap_res_tf_open := UC.usertrap_res_tf_open.

  (* the kernel table's invariant, read off the translation residue without
     spending it -- [wp_userret_closed] takes both, and the root has to be
     the same one, which only this projection can guarantee (nothing else
     in forkret names the kernel root; see SpecForkret.v's header). *)
  Lemma fkr_kpt_of_res (r : mword 44) :
    tlb_res_pt r -∗ kpt_inv r ∗ tlb_res_pt r.
  Proof.
    iIntros "H".
    iDestruct "H" as (s0 tv) "(Hsatp & %A & %B & %C & Htlb & Hsnap & Hpmp & #Hk)".
    iFrame "Hk". iExists s0, tv. iFrame "Hsatp".
    iSplitR; [iPureIntro; exact A |].
    iSplitR; [iPureIntro; exact B |].
    iSplitR; [iPureIntro; exact C |].
    iFrame "Htlb Hsnap Hpmp Hk".
  Qed.

End Res.

Theorem wp_forkret
    `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !bioG Σ,
      !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ, !fsCrashG Σ,
      !kallocG Σ, !irefslotG Σ, !pavG Σ, !iregG Σ}
    `{GEN : GenId} `{CID : CpuId}
    (pt : uptd) (j : nat)
    (γl γf : gname) (s : string) (Rlk : iProp Σ)
    (pid : mword 32) (V : pprivate)
    (ks : mword 64) (m : regfile) (av av2 : nat) (eb : bool) :
    wp_forkret_body (fun h : CpuId => usertrap_res_bare (CID := h))
      pt j γl γf s Rlk pid V ks m av av2 eb.
Proof.
  cbv beta delta [wp_forkret_body wp_forkret_gen_body].
  intros pcE p ksp Hjlt Hav2 Hpr Hut Hsp Hupt Hnorm Hptwf Hgap Hkw.
  (* the budget in numbers [lia] can see *)
  pose proof Hut as Hut'.
  
  pose proof Hpr as Hpr'.
  
  (* the frame's six slots come off the top and go back on at the exit *)
  assert (Havsum : av = (6 + (trap_res eb + av2))%nat) by lia.
  iIntros "#Htext #Hwire #Hclaimmap Hpc #Hfirst Hcg Hcpu Htc Hclm
           #Hislock Hlocked HR #Hks Hpv Hyield".
  iPoseProof (fkr_00 with "Htext") as "Hi00".
  iPoseProof (fkr_02 with "Htext") as "Hi02".
  iPoseProof (fkr_04 with "Htext") as "Hi04".
  iPoseProof (fkr_06 with "Htext") as "Hi06".
  iPoseProof (fkr_08 with "Htext") as "Hi08".
  iPoseProof (fkr_0a with "Htext") as "Hi0a".
  iPoseProof (fkr_0e with "Htext") as "Hi0e".
  iPoseProof (fkr_10 with "Htext") as "Hi10".
  iPoseProof (fkr_14 with "Htext") as "Hi14".
  iPoseProof (fkr_18 with "Htext") as "Hi18".
  iPoseProof (fkr_1c with "Htext") as "Hi1c".
  iPoseProof (fkr_1e with "Htext") as "Hi1e".
  iPoseProof (fkr_22 with "Htext") as "Hi22".
  iPoseProof (fkr_24 with "Htext") as "Hi24".
  iPoseProof (fkr_64 with "Htext") as "Hi64".
  iPoseProof (fkr_68 with "Htext") as "Hi68".
  iPoseProof (fkr_6a with "Htext") as "Hi6a".
  iPoseProof (fkr_6c with "Htext") as "Hi6c".
  iPoseProof (fkr_70 with "Htext") as "Hi70".
  iPoseProof (fkr_72 with "Htext") as "Hi72".
  iPoseProof (fkr_74 with "Htext") as "Hi74".
  iPoseProof (fkr_78 with "Htext") as "Hi78".
  iPoseProof (fkr_7c with "Htext") as "Hi7c".
  iPoseProof (fkr_80 with "Htext") as "Hi80".
  iPoseProof (fkr_84 with "Htext") as "Hi84".
  iPoseProof (fkr_86 with "Htext") as "Hi86".
  iPoseProof (fkr_88 with "Htext") as "Hi88".
  iPoseProof (fkr_8a with "Htext") as "Hi8a".
  iPoseProof (fkr_8c with "Htext") as "Hi8c".
  iPoseProof (fkr_8e with "Htext") as "Hi8e".
  (* ================================================================== *)
  (*  +0x00 .. +0x08: the 48-byte frame, at [b = false].                 *)
  (* ================================================================== *)
  assert (Hpush : add_vec (m !!! Regidx csp_rs1)
                    (sign_extend' 64 (caddi16sp_imm (mword_of_int 61 : mword 6)))
                  = pa_stk (m !!! Regidx csp_rs1) 6)
    by (apply (stk_push _ _ 6); pcw).
  iApply (wp_caddi16sp_push_s_sconf pcE (mword_of_int 61 : mword 6) m av 6 false
            ltac:(lia) Hpush with "Hcg Hpc Hi00").
  iApply wp_next_off_intro. iIntros "Hcg Hframe Hpc".
  set (M1 := <[Regidx csp_rs1 := regval_into_reg
                 (add_vec (m !!! Regidx csp_rs1)
                    (sign_extend' 64 (caddi16sp_imm (mword_of_int 61 : mword 6))))]> m).
  change (<[Regidx csp_rs1 := regval_into_reg
             (add_vec (m !!! Regidx csp_rs1)
                (sign_extend' 64 (caddi16sp_imm (mword_of_int 61 : mword 6))))]> m) with M1.
  iEval (rewrite Hsp) in "Hframe".
  iEval (rewrite -Hav2) in "Hcg".
  assert (HM1sp : M1 !!! Regidx csp_rs1 = pa_stk ksp 6)
    by (rewrite /M1 upd_eq Hpush Hsp; reflexivity).
  assert (Hp02 : add_vec_int (pcE : mword 64) 2 = mword_of_int (FR + 0x02)) by pcw.
  iEval (rewrite Hp02) in "Hpc".
  (* the frame: three saved words, three scratch slots *)
  iDestruct (stack_own_split_1 (KTR := KT1) ksp 4 6 ltac:(lia) with "Hframe") as "[Hf14 Hf56]".
  iDestruct (stack_own_4_elim with "Hf14") as (vra vs0 vs1 vsc) "(Hbra & Hbs0 & Hbs1 & Hbsc)".
  assert (Hpa1 : add_vec (M1 !!! Regidx csp_rs1)
                   (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000")))
                 = pa_stk ksp 1)
    by (rewrite HM1sp; apply stk_frm; pcw).
  assert (Hpa2 : add_vec (M1 !!! Regidx csp_rs1)
                   (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000")))
                 = pa_stk ksp 2)
    by (rewrite HM1sp; apply stk_frm; pcw).
  assert (Hpa3 : add_vec (M1 !!! Regidx csp_rs1)
                   (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000")))
                 = pa_stk ksp 3)
    by (rewrite HM1sp; apply stk_frm; pcw).
  iEval (rewrite -Hpa1) in "Hbra".
  iEval (rewrite -Hpa2) in "Hbs0".
  iEval (rewrite -Hpa3) in "Hbs1".
  (* ---- +0x02: c.sdsp ra,40(sp) ---- *)
  iApply (wp_csdsp_s_sconf (mword_of_int (FR + 0x02)) (mword_of_int 5 : mword 6)
            Rra M1 (trap_res eb + av2)%nat vra false with "Hcg Hpc Hi02 Hbra").
  iApply wp_next_off_intro. iIntros "Hcg Hpc Hbra".
  iEval (rewrite Hpa1) in "Hbra".
  assert (Hp04 : add_vec_int (mword_of_int (FR + 0x02) : mword 64) 2
                 = mword_of_int (FR + 0x04)) by pcw.
  iEval (rewrite Hp04) in "Hpc".
  (* ---- +0x04: c.sdsp s0,32(sp) ---- *)
  iApply (wp_csdsp_s_sconf (mword_of_int (FR + 0x04)) (mword_of_int 4 : mword 6)
            Rs0 M1 (trap_res eb + av2)%nat vs0 false with "Hcg Hpc Hi04 Hbs0").
  iApply wp_next_off_intro. iIntros "Hcg Hpc Hbs0".
  iEval (rewrite Hpa2) in "Hbs0".
  assert (Hp06 : add_vec_int (mword_of_int (FR + 0x04) : mword 64) 2
                 = mword_of_int (FR + 0x06)) by pcw.
  iEval (rewrite Hp06) in "Hpc".
  (* ---- +0x06: c.sdsp s1,24(sp) ---- *)
  iApply (wp_csdsp_s_sconf (mword_of_int (FR + 0x06)) (mword_of_int 3 : mword 6)
            Rs1 M1 (trap_res eb + av2)%nat vs1 false with "Hcg Hpc Hi06 Hbs1").
  iApply wp_next_off_intro. iIntros "Hcg Hpc Hbs1".
  iEval (rewrite Hpa3) in "Hbs1".
  assert (Hp08 : add_vec_int (mword_of_int (FR + 0x06) : mword 64) 2
                 = mword_of_int (FR + 0x08)) by pcw.
  iEval (rewrite Hp08) in "Hpc".
  (* ---- +0x08: c.addi4spn s0,sp,48 ---- *)
  iApply (wp_caddi4spn_s_sconf (mword_of_int (FR + 0x08)) (Cregidx (mword_of_int 0))
            (mword_of_int 12 : mword 8) Rs0 M1 (trap_res eb + av2)%nat false
            ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(rdok)
            with "Hcg Hpc Hi08").
  iApply wp_next_off_intro. iIntros "Hcg Hpc".
  set (M2 := <[Regidx Rs0 := regval_into_reg
                 (add_vec (M1 !!! Regidx csp_rs1)
                    (sign_extend' 64 (caddi4spn_imm (mword_of_int 12 : mword 8))))]> M1).
  change (<[Regidx Rs0 := regval_into_reg
             (add_vec (M1 !!! Regidx csp_rs1)
                (sign_extend' 64 (caddi4spn_imm (mword_of_int 12 : mword 8))))]> M1) with M2.
  assert (HM2sp : M2 !!! Regidx csp_rs1 = pa_stk ksp 6)
    by (rewrite /M2 upd_ne; [exact HM1sp | reg_neq]).
  assert (Hp0a : add_vec_int (mword_of_int (FR + 0x08) : mword 64) 2
                 = mword_of_int (FR + 0x0a)) by pcw.
  iEval (rewrite Hp0a) in "Hpc".
  (* ================================================================== *)
  (*  +0x0a: jal ra, myproc -- a0 = p.                                   *)
  (* ================================================================== *)
  iApply (wp_jal_s_sconf (mword_of_int (FR + 0x0a)) Rra
            (mword_of_int 2097092 : mword 21) M2 (trap_res eb + av2)%nat false
            ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
            with "Hcg Hpc Hi0a").
  iApply wp_next_off_intro. iIntros "Hcg Hpc".
  set (M3 := <[Regidx Rra := regval_into_reg
                 (add_vec_int (mword_of_int (FR + 0x0a) : mword 64) 4)]> M2).
  change (<[Regidx Rra := regval_into_reg
             (add_vec_int (mword_of_int (FR + 0x0a) : mword 64) 4)]> M2) with M3.
  assert (HM3sp : M3 !!! Regidx csp_rs1 = pa_stk ksp 6)
    by (rewrite /M3 upd_ne; [exact HM2sp | reg_neq]).
  assert (HM3ra : M3 !!! Regidx Rra = mword_of_int (FR + 0x0e))
    by (rewrite /M3 upd_eq; pcw).
  assert (Hmyproc : add_vec (mword_of_int (FR + 0x0a) : mword 64)
                      (sign_extend' 64 (mword_of_int 2097092 : mword 21))
                    = mword_of_int KernelSyms.myproc) by pcw.
  iEval (rewrite Hmyproc) in "Hpc".
  iApply (MP.wp_myproc_sconf M3 (trap_res eb + av2)%nat 1%nat eb p false {[s]}
            fkr_n1 ltac:(lia) with "Hcg Hcpu Htext Hpc").
  iApply wp_next_off_intro. iIntros (msq A) "%Hmsq Hcg Hcpu Hpc %HcsA".
  destruct HcsA as [HcsA HAa0].
  assert (Hpc0e : ret_pc (M3 !!! Regidx Rra) = mword_of_int (FR + 0x0e))
    by (rewrite HM3ra; pcw).
  iEval (rewrite Hpc0e) in "Hpc".
  assert (HAsp : A !!! Regidx csp_rs1 = pa_stk ksp 6)
    by (rewrite (callee_saved_lookup HcsA csp_rs1 ltac:(vm_compute; reflexivity)); exact HM3sp).
  (* ---- +0x0e: c.mv s1,a0 ---- *)
  iApply (wp_cmv_s_sconf (mword_of_int (FR + 0x0e)) Rs1 Ra0
            A (trap_res eb + av2)%nat false
            ltac:(vm_compute; discriminate) ltac:(rdok) with "Hcg Hpc Hi0e").
  iApply wp_next_off_intro. iIntros "Hcg Hpc".
  set (M4 := <[Regidx Rs1 := regval_into_reg
                 (add_vec zero_reg (rget A Ra0))]> A).
  change (<[Regidx Rs1 := regval_into_reg (add_vec zero_reg (rget A Ra0))]> A) with M4.
  assert (HM4s1 : M4 !!! Regidx Rs1 = p).
  { rewrite /M4 upd_eq. rgne. rewrite HAa0. apply add_vec_zero_l. }
  assert (HM4a0 : M4 !!! Regidx Ra0 = p)
    by (rewrite /M4 upd_ne; [exact HAa0 | reg_neq]).
  assert (HM4sp : M4 !!! Regidx csp_rs1 = pa_stk ksp 6)
    by (rewrite /M4 upd_ne; [exact HAsp | reg_neq]).
  assert (Hp10 : add_vec_int (mword_of_int (FR + 0x0e) : mword 64) 2
                 = mword_of_int (FR + 0x10)) by pcw.
  iEval (rewrite Hp10) in "Hpc".
  (* ================================================================== *)
  (*  +0x10: jal ra, release -- p->lock goes.  THE INDEX BECOMES [eb].    *)
  (* ================================================================== *)
  iApply (wp_jal_s_sconf (mword_of_int (FR + 0x10)) Rra
            (mword_of_int 2093862 : mword 21) M4 (trap_res eb + av2)%nat false
            ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
            with "Hcg Hpc Hi10").
  iApply wp_next_off_intro. iIntros "Hcg Hpc".
  set (M5 := <[Regidx Rra := regval_into_reg
                 (add_vec_int (mword_of_int (FR + 0x10) : mword 64) 4)]> M4).
  change (<[Regidx Rra := regval_into_reg
             (add_vec_int (mword_of_int (FR + 0x10) : mword 64) 4)]> M4) with M5.
  assert (HM5a0 : M5 !!! Regidx Ra0 = p)
    by (rewrite /M5 upd_ne; [exact HM4a0 | reg_neq]).
  assert (HM5s1 : M5 !!! Regidx Rs1 = p)
    by (rewrite /M5 upd_ne; [exact HM4s1 | reg_neq]).
  assert (HM5sp : M5 !!! Regidx csp_rs1 = pa_stk ksp 6)
    by (rewrite /M5 upd_ne; [exact HM4sp | reg_neq]).
  assert (HM5ra : M5 !!! Regidx Rra = mword_of_int (FR + 0x14))
    by (rewrite /M5 upd_eq; pcw).
  assert (Hrelease : add_vec (mword_of_int (FR + 0x10) : mword 64)
                       (sign_extend' 64 (mword_of_int 2093862 : mword 21))
                     = mword_of_int KernelSyms.release) by pcw.
  iEval (rewrite Hrelease) in "Hpc".
  assert (Hlka : add_vec (M5 !!! Regidx Ra0)
                   (sign_extend' 64 (mword_of_int 0 : mword 12)) = p)
    by (rewrite HM5a0; apply addv_sext0).
  (* the arm splits: what release wants and what prepare_return will *)
  iDestruct (arm_pay_ext_split eb p with "Htc Hclm") as "[Hpay [Hext Hcx]]".
  iApply (RL.wp_release_sconf KT1 γl p s Rlk M5 0%nat eb p av2 {[s]}
            Hlka ltac:(lia) with "Hcg Htext Hpc Hislock Hlocked HR Hcpu Hpay").
  iIntros (CIDr Hkr mr) "Hcg Hpc %Hcsr Hcpu".
  assert (Hpc14 : ret_pc (M5 !!! Regidx Rra) = mword_of_int (FR + 0x14))
    by (rewrite HM5ra; pcw).
  iEval (rewrite Hpc14) in "Hpc".
  (* the released set collapses; [cpu_own] at depth 0 says so itself *)
  iDestruct (cpu_own_zero_empty with "Hcpu") as "[%Hlks Hcpu]".
  iEval (rewrite Hlks) in "Hcpu".
  assert (Hmrs1 : mr !!! Regidx Rs1 = p)
    by (rewrite (callee_saved_lookup Hcsr Rs1 ltac:(vm_compute; reflexivity)); exact HM5s1).
  assert (Hmrsp : mr !!! Regidx csp_rs1 = pa_stk ksp 6)
    by (rewrite (callee_saved_lookup Hcsr csp_rs1 ltac:(vm_compute; reflexivity)); exact HM5sp).
  (* ================================================================== *)
  (*  +0x14 .. +0x24: [if (first)] -- refuted by the discarded cell.      *)
  (* ================================================================== *)
  (* ---- +0x14: auipc a5,0x9 ---- *)
  iApply (wp_auipc_s_sconf (mword_of_int (FR + 0x14)) Ra5
            (mword_of_int 9 : mword 20) mr av2 eb
            ltac:(vm_compute; discriminate) ltac:(rdok) with "Hcg Hpc Hi14").
  iIntros (CID1 Hk1) "Hcg Hpc".
  set (T1 := <[Regidx Ra5 := regval_into_reg
                 (add_vec (mword_of_int (FR + 0x14) : mword 64)
                    (auipc_off (mword_of_int 9 : mword 20)))]> mr).
  change (<[Regidx Ra5 := regval_into_reg
             (add_vec (mword_of_int (FR + 0x14) : mword 64)
                (auipc_off (mword_of_int 9 : mword 20)))]> mr) with T1.
  assert (Hp18 : add_vec_int (mword_of_int (FR + 0x14) : mword 64) 4
                 = mword_of_int (FR + 0x18)) by pcw.
  iEval (rewrite Hp18) in "Hpc".
  (* ---- +0x18: addi a5,a5,-1712 -- a5 = &first ---- *)
  iApply (wp_addi4_s_sconf (mword_of_int (FR + 0x18)) Ra5 Ra5
            (mword_of_int 2384 : mword 12) T1 av2 eb
            ltac:(vm_compute; discriminate) ltac:(rdok) with "Hcg Hpc Hi18").
  iIntros (CID2 Hk2) "Hcg Hpc".
  set (T2 := <[Regidx Ra5 := regval_into_reg
                 (add_vec (rget T1 Ra5)
                    (sign_extend' 64 (mword_of_int 2384 : mword 12)))]> T1).
  change (<[Regidx Ra5 := regval_into_reg
             (add_vec (rget T1 Ra5)
                (sign_extend' 64 (mword_of_int 2384 : mword 12)))]> T1) with T2.
  assert (HT2a5 : rget T2 Ra5 = first_addr).
  { rgne. rewrite /T2 upd_eq. rgne. rewrite /T1 upd_eq. exact fkr_first_addr. }
  assert (Hp1c : add_vec_int (mword_of_int (FR + 0x18) : mword 64) 4
                 = mword_of_int (FR + 0x1c)) by pcw.
  iEval (rewrite Hp1c) in "Hpc".
  (* ---- +0x1c: c.lw a5,0(a5) -- the read that decides the branch ---- *)
  assert (Hfaddr : add_vec (rget T2 Ra5)
                     (sign_extend' 64 (mword_of_int 0 : mword 12)) = first_addr)
    by (rewrite HT2a5; apply addv_sext0).
  iEval (rewrite -Hfaddr) in "Hfirst".
  iApply (wp_clw_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (FR + 0x1c)) Ra5 Ra5
            (mword_of_int 0 : mword 12) T2 av2 (mword_of_int 0 : mword 32) eb
            ltac:(vm_compute; discriminate) ltac:(rdok)
            with "Hcg Hpc Hi1c Hfirst").
  iIntros (CID3 Hk3) "Hcg Hpc _".
  set (T3 := <[Regidx Ra5 := regval_into_reg
                 (sign_extend' 64 (mword_of_int 0 : mword 32))]> T2).
  change (<[Regidx Ra5 := regval_into_reg
             (sign_extend' 64 (mword_of_int 0 : mword 32))]> T2) with T3.
  assert (Hp1e : add_vec_int (mword_of_int (FR + 0x1c) : mword 64) 2
                 = mword_of_int (FR + 0x1e)) by pcw.
  iEval (rewrite Hp1e) in "Hpc".
  (* ---- +0x1e: fence r,rw -- the acquire barrier, state-preserving ---- *)
  iApply (wp_fence_gen_s_sconf (mword_of_int (FR + 0x1e))
            (mword_of_int 0 : mword 4) (mword_of_int 2 : mword 4)
            (mword_of_int 3 : mword 4) zreg zreg T3 av2 eb
            with "Hcg Hpc Hi1e").
  iIntros (CID4 Hk4) "Hcg Hpc".
  assert (Hp22 : add_vec_int (mword_of_int (FR + 0x1e) : mword 64) 4
                 = mword_of_int (FR + 0x22)) by pcw.
  iEval (rewrite Hp22) in "Hpc".
  (* ---- +0x22: sext.w a5,a5 ---- *)
  iApply (wp_caddiw_s_sconf (mword_of_int (FR + 0x22)) Ra5
            (mword_of_int 0 : mword 6) T3 av2 eb
            ltac:(vm_compute; discriminate) ltac:(rdok) with "Hcg Hpc Hi22").
  iIntros (CID5 Hk5) "Hcg Hpc".
  set (T4 := <[Regidx Ra5 := regval_into_reg
                 (sign_extend' 64 (subrange_vec_dec
                    (add_vec (rget T3 Ra5)
                       (sign_extend' 64 (sign_extend' 12 (mword_of_int 0 : mword 6)))) 31 0))]> T3).
  change (<[Regidx Ra5 := regval_into_reg
             (sign_extend' 64 (subrange_vec_dec
                (add_vec (rget T3 Ra5)
                   (sign_extend' 64 (sign_extend' 12 (mword_of_int 0 : mword 6)))) 31 0))]> T3) with T4.
  assert (HT4a5 : eq_vec (rget T4 Ra5) zero_reg = true).
  { rgne. rewrite /T4 upd_eq. rgne. rewrite /T3 upd_eq.
    vm_compute. reflexivity. }
  assert (Hp24 : add_vec_int (mword_of_int (FR + 0x22) : mword 64) 2
                 = mword_of_int (FR + 0x24)) by pcw.
  iEval (rewrite Hp24) in "Hpc".
  (* ---- +0x24: c.beqz a5, +0x64 -- TAKEN, so the boot arm is dead ---- *)
  iApply (wp_cbeqz_taken_s_sconf (mword_of_int (FR + 0x24))
            (mword_of_int 32 : mword 8) (Cregidx (mword_of_int 7)) Ra5
            T4 av2 eb ltac:(vm_compute; reflexivity)
            ltac:(vm_compute; discriminate) HT4a5 fkr_beqz_align
            with "Hcg Hpc Hi24").
  iNext. iIntros (CID6 Hk6) "Hcg Hpc".
  iEval (rewrite fkr_beqz_tgt) in "Hpc".
  (* ================================================================== *)
  (*  +0x64: jal ra, prepare_return.                                     *)
  (* ================================================================== *)
  assert (HT4sp : T4 !!! Regidx csp_rs1 = pa_stk ksp 6).
  { rewrite /T4 upd_ne; [| reg_neq]. rewrite /T3 upd_ne; [| reg_neq].
    rewrite /T2 upd_ne; [| reg_neq]. rewrite /T1 upd_ne; [| reg_neq].
    exact Hmrsp. }
  assert (HT4s1 : T4 !!! Regidx Rs1 = p).
  { rewrite /T4 upd_ne; [| reg_neq]. rewrite /T3 upd_ne; [| reg_neq].
    rewrite /T2 upd_ne; [| reg_neq]. rewrite /T1 upd_ne; [| reg_neq].
    exact Hmrs1. }
  iApply (wp_jal_s_sconf (mword_of_int (FR + 0x64)) Rra
            (mword_of_int 2790 : mword 21) T4 av2 eb
            ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
            with "Hcg Hpc Hi64").
  iIntros (CID7 Hk7) "Hcg Hpc".
  set (T5 := <[Regidx Rra := regval_into_reg
                 (add_vec_int (mword_of_int (FR + 0x64) : mword 64) 4)]> T4).
  change (<[Regidx Rra := regval_into_reg
             (add_vec_int (mword_of_int (FR + 0x64) : mword 64) 4)]> T4) with T5.
  assert (HT5ra : T5 !!! Regidx Rra = mword_of_int (FR + 0x68))
    by (rewrite /T5 upd_eq; pcw).
  assert (HT5sp : T5 !!! Regidx csp_rs1 = pa_stk ksp 6)
    by (rewrite /T5 upd_ne; [exact HT4sp | reg_neq]).
  assert (Hprep : add_vec (mword_of_int (FR + 0x64) : mword 64)
                    (sign_extend' 64 (mword_of_int 2790 : mword 21))
                  = mword_of_int KernelSyms.prepare_return) by pcw.
  iEval (rewrite Hprep) in "Hpc".
  (* the three hart-indexed carriers, moved to the current binder in one
     step -- [wp_next_chain] chains the whole run of [Hk*]. *)
  iDestruct (cpu_own_transport CIDr CID7 0%nat eb p eb
               ltac:(wp_next_chain) with "Hcpu") as "Hcpu".
  iDestruct (trap_csrs_ext_transport CID CID7 eb p
               ltac:(wp_next_chain) with "Hext") as "Hext".
  iDestruct (cpu_claim_ext_transport CID CID7 eb p
               ltac:(wp_next_chain) with "Hcx") as "Hcx".
  iDestruct (ut_epc_exists with "Hpv") as %[epc Hepc].
  iApply (PR.wp_prepare_return_sconf γf ks pid V T5 av2 p epc eb ∅
            Hpr Hepc with "Hcg Hcpu Hext Htext Hpc Hks Hpv").
  iIntros (CIDf Hkf mf ksat kroot0 vb)
    "%Hcsf %HksatM %Hksata %Hksatp Hcg Hcpu Hcpay Hsepc Hscause Hstval
     Hsret Hstvec Hq4 Hkptr Hpv Hpc".
  assert (Hpc68 : ret_pc (T5 !!! Regidx Rra) = mword_of_int (FR + 0x68))
    by (rewrite HT5ra; pcw).
  iEval (rewrite Hpc68) in "Hpc".
  assert (Hmfsp : mf !!! Regidx csp_rs1 = pa_stk ksp 6)
    by (rewrite (callee_saved_lookup Hcsf csp_rs1 ltac:(vm_compute; reflexivity)); exact HT5sp).
  assert (Hmfs1 : mf !!! Regidx Rs1 = p)
    by (rewrite (callee_saved_lookup Hcsf Rs1 ltac:(vm_compute; reflexivity)); exact HT4s1).
  (* the running claim, whole again -- AT THE RESUMING HART.
     prepare_return parks, so the [_ext] half the caller has been carrying
     is at the pre-call hart and the [_pay] half prepare_return returns is
     at the post-call one; the two print identically and do not unify. *)
  iDestruct (cpu_claim_ext_transport CID7 CIDf eb p
               ltac:(wp_next_chain) with "Hcx") as "Hcx".
  iAssert (cpu_claim p) with "[Hcpay Hcx]" as "Hclaim".
  { iApply (bi.equiv_entails_1_1 _ _ (cpu_claim_ext_split eb p)).
    iSplitL "Hcpay"; [iExact "Hcpay" | iExact "Hcx"]. }
  (* ================================================================== *)
  (*  +0x68 .. +0x6a: MAKE_SATP(p->pagetable), first half.                *)
  (* ================================================================== *)
  (* THE MOVED RECORD IS NEVER SPELLED.  prepare_return hands the block
     back at [upd_tf V (prepare_return_tf ... cid_word)], whose [cid_word]
     names the RESUMING hart -- so writing the term out would pin it to the
     section's hart.  All the walk needs of it is [pv_upt], which [upd_tf]
     does not touch. *)
  iAssert (∃ V' : pprivate, ⌜pv_upt V' = pt⌝ ∗ proc_priv γf p pid V')%I
    with "[Hpv]" as (V') "[%HuptV' Hpv]".
  { iExists _. iFrame "Hpv". iPureIntro. exact Hupt. }
  iDestruct (proc_priv_copy with "Hpv") as "(Hsz & Hpgt & Hppt & Hpvback)".
  assert (Hc0 : creg2reg_idx (Cregidx (mword_of_int 0)) = Regidx Rs0)
    by (vm_compute; reflexivity).
  assert (Hc2 : creg2reg_idx (Cregidx (mword_of_int 2)) = Regidx Ra0)
    by (vm_compute; reflexivity).
  assert (Hc5 : creg2reg_idx (Cregidx (mword_of_int 5)) = Regidx Ra3)
    by (vm_compute; reflexivity).
  assert (Hc6 : creg2reg_idx (Cregidx (mword_of_int 6)) = Regidx Ra4)
    by (vm_compute; reflexivity).
  assert (Hc7 : creg2reg_idx (Cregidx (mword_of_int 7)) = Regidx Ra5)
    by (vm_compute; reflexivity).
  assert (Haddrpg : add_vec (rget mf Rs1)
                      (sign_extend' 64 (mword_of_int 80 : mword 12))
                    = p_pagetable p)
    by (rgne; rewrite Hmfs1; reflexivity).
  iEval (rewrite -Haddrpg) in "Hpgt".
  (* ---- +0x68: c.ld a0,80(s1) ---- *)
  iApply (wp_cld_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (FR + 0x68)) Ra0 Rs1
            (mword_of_int 80 : mword 12) mf (trap_res eb + av2)%nat
            (page_base (ud_root (pv_upt V'))) false
            ltac:(vm_compute; discriminate) ltac:(rdok)
            with "Hcg Hpc Hi68 Hpgt").
  iApply wp_next_off_intro. iIntros "Hcg Hpc Hpgt".
  set (S0 := <[Regidx Ra0 := regval_into_reg
                 (page_base (ud_root (pv_upt V')))]> mf).
  change (<[Regidx Ra0 := regval_into_reg
             (page_base (ud_root (pv_upt V')))]> mf) with S0.
  assert (Hp6a : add_vec_int (mword_of_int (FR + 0x68) : mword 64) 2
                 = mword_of_int (FR + 0x6a)) by pcw.
  iEval (rewrite Hp6a) in "Hpc".
  (* ---- +0x6a: srli a0,a0,0xc ---- *)
  iEval (rewrite Hc2) in "Hi6a".
  iApply (wp_csrli_s_sconf (mword_of_int (FR + 0x6a)) (Cregidx (mword_of_int 2))
            Ra0 (mword_of_int 12 : mword 6) S0 (trap_res eb + av2)%nat false
            Hc2 ltac:(vm_compute; discriminate) ltac:(rdok) with "Hcg Hpc Hi6a").
  iApply wp_next_off_intro. iIntros "Hcg Hpc".
  set (S1 := <[Regidx Ra0 := regval_into_reg
                 (shift_bits_right (rget S0 Ra0)
                    (subrange_vec_dec (mword_of_int 12 : mword 6)
                       (Z.sub log2_xlen 1) 0))]> S0).
  change (<[Regidx Ra0 := regval_into_reg
             (shift_bits_right (rget S0 Ra0)
                (subrange_vec_dec (mword_of_int 12 : mword 6)
                   (Z.sub log2_xlen 1) 0))]> S0) with S1.
  assert (Hp6c : add_vec_int (mword_of_int (FR + 0x6a) : mword 64) 2
                 = mword_of_int (FR + 0x6c)) by pcw.
  iEval (rewrite Hp6c) in "Hpc".
  (* ================================================================== *)
  (*  +0x6c .. +0x86: TRAMPOLINE + (userret - trampoline).                *)
  (* ================================================================== *)
  (* ---- +0x6c: lui a4,0x4000 ---- *)
  iApply (wp_lui_s_sconf (mword_of_int (FR + 0x6c)) Ra4
            (mword_of_int 16384 : mword 20) (mword_of_int 0x4000000 : mword 64)
            S1 (trap_res eb + av2)%nat false
            ltac:(vm_compute; discriminate) ltac:(rdok) prr_lui_a4
            with "Hcg Hpc Hi6c").
  iApply wp_next_off_intro. iIntros "Hcg Hpc".
  set (S2 := <[Regidx Ra4 := regval_into_reg (mword_of_int 0x4000000 : mword 64)]> S1).
  change (<[Regidx Ra4 := regval_into_reg (mword_of_int 0x4000000 : mword 64)]> S1) with S2.
  assert (Hp70 : add_vec_int (mword_of_int (FR + 0x6c) : mword 64) 4
                 = mword_of_int (FR + 0x70)) by pcw.
  iEval (rewrite Hp70) in "Hpc".
  (* ---- +0x70: c.addi a4,a4,-1 ---- *)
  iApply (wp_caddi_s_sconf (mword_of_int (FR + 0x70)) Ra4
            (mword_of_int 63 : mword 6) S2 (trap_res eb + av2)%nat false
            ltac:(vm_compute; discriminate) ltac:(rdok) with "Hcg Hpc Hi70").
  iApply wp_next_off_intro. iIntros "Hcg Hpc".
  set (S3 := <[Regidx Ra4 := regval_into_reg
                 (add_vec (rget S2 Ra4)
                    (sign_extend' 64 (sign_extend' 12 (mword_of_int 63 : mword 6))))]> S2).
  change (<[Regidx Ra4 := regval_into_reg
             (add_vec (rget S2 Ra4)
                (sign_extend' 64 (sign_extend' 12 (mword_of_int 63 : mword 6))))]> S2) with S3.
  assert (Hp72 : add_vec_int (mword_of_int (FR + 0x70) : mword 64) 2
                 = mword_of_int (FR + 0x72)) by pcw.
  iEval (rewrite Hp72) in "Hpc".
  (* ---- +0x72: c.slli a4,a4,0xc -- a4 = TRAMPOLINE ---- *)
  iApply (wp_cslli_s_sconf (mword_of_int (FR + 0x72)) (Regidx Ra4) Ra4
            (mword_of_int 12 : mword 6) S3 (trap_res eb + av2)%nat false
            eq_refl ltac:(vm_compute; discriminate) ltac:(rdok) with "Hcg Hpc Hi72").
  iApply wp_next_off_intro. iIntros "Hcg Hpc".
  set (S4 := <[Regidx Ra4 := regval_into_reg
                 (shift_bits_left (rget S3 Ra4)
                    (subrange_vec_dec (mword_of_int 12 : mword 6)
                       (Z.sub log2_xlen 1) 0))]> S3).
  change (<[Regidx Ra4 := regval_into_reg
             (shift_bits_left (rget S3 Ra4)
                (subrange_vec_dec (mword_of_int 12 : mword 6)
                   (Z.sub log2_xlen 1) 0))]> S3) with S4.
  assert (HS4a4 : rget S4 Ra4 = uservec_tvec).
  { rgne. rewrite /S4 upd_eq. rgne. rewrite /S3 upd_eq. rgne.
    rewrite /S2 upd_eq. rewrite prr_addi_a4. exact prr_slli_a4. }
  assert (Hp74 : add_vec_int (mword_of_int (FR + 0x72) : mword 64) 2
                 = mword_of_int (FR + 0x74)) by pcw.
  iEval (rewrite Hp74) in "Hpc".
  (* ---- +0x74/+0x78: a5 = &userret ---- *)
  iApply (wp_auipc_s_sconf (mword_of_int (FR + 0x74)) Ra5
            (mword_of_int 4 : mword 20) S4 (trap_res eb + av2)%nat false
            ltac:(vm_compute; discriminate) ltac:(rdok) with "Hcg Hpc Hi74").
  iApply wp_next_off_intro. iIntros "Hcg Hpc".
  set (S5 := <[Regidx Ra5 := regval_into_reg
                 (add_vec (mword_of_int (FR + 0x74) : mword 64)
                    (auipc_off (mword_of_int 4 : mword 20)))]> S4).
  change (<[Regidx Ra5 := regval_into_reg
             (add_vec (mword_of_int (FR + 0x74) : mword 64)
                (auipc_off (mword_of_int 4 : mword 20)))]> S4) with S5.
  assert (Hp78 : add_vec_int (mword_of_int (FR + 0x74) : mword 64) 4
                 = mword_of_int (FR + 0x78)) by pcw.
  iEval (rewrite Hp78) in "Hpc".
  iApply (wp_addi4_s_sconf (mword_of_int (FR + 0x78)) Ra5 Ra5
            (mword_of_int 1820 : mword 12) S5 (trap_res eb + av2)%nat false
            ltac:(vm_compute; discriminate) ltac:(rdok) with "Hcg Hpc Hi78").
  iApply wp_next_off_intro. iIntros "Hcg Hpc".
  set (S6 := <[Regidx Ra5 := regval_into_reg
                 (add_vec (rget S5 Ra5)
                    (sign_extend' 64 (mword_of_int 1820 : mword 12)))]> S5).
  change (<[Regidx Ra5 := regval_into_reg
             (add_vec (rget S5 Ra5)
                (sign_extend' 64 (mword_of_int 1820 : mword 12)))]> S5) with S6.
  assert (HS6a5 : rget S6 Ra5 = (mword_of_int KernelSyms.userret : mword 64)).
  { rgne. rewrite /S6 upd_eq. rgne. rewrite /S5 upd_eq. exact fkr_userret_addr. }
  assert (Hp7c : add_vec_int (mword_of_int (FR + 0x78) : mword 64) 4
                 = mword_of_int (FR + 0x7c)) by pcw.
  iEval (rewrite Hp7c) in "Hpc".
  (* ---- +0x7c/+0x80: a3 = &_trampoline ---- *)
  iApply (wp_auipc_s_sconf (mword_of_int (FR + 0x7c)) Ra3
            (mword_of_int 4 : mword 20) S6 (trap_res eb + av2)%nat false
            ltac:(vm_compute; discriminate) ltac:(rdok) with "Hcg Hpc Hi7c").
  iApply wp_next_off_intro. iIntros "Hcg Hpc".
  set (S7 := <[Regidx Ra3 := regval_into_reg
                 (add_vec (mword_of_int (FR + 0x7c) : mword 64)
                    (auipc_off (mword_of_int 4 : mword 20)))]> S6).
  change (<[Regidx Ra3 := regval_into_reg
             (add_vec (mword_of_int (FR + 0x7c) : mword 64)
                (auipc_off (mword_of_int 4 : mword 20)))]> S6) with S7.
  assert (Hp80 : add_vec_int (mword_of_int (FR + 0x7c) : mword 64) 4
                 = mword_of_int (FR + 0x80)) by pcw.
  iEval (rewrite Hp80) in "Hpc".
  iApply (wp_addi4_s_sconf (mword_of_int (FR + 0x80)) Ra3 Ra3
            (mword_of_int 1656 : mword 12) S7 (trap_res eb + av2)%nat false
            ltac:(vm_compute; discriminate) ltac:(rdok) with "Hcg Hpc Hi80").
  iApply wp_next_off_intro. iIntros "Hcg Hpc".
  set (S8 := <[Regidx Ra3 := regval_into_reg
                 (add_vec (rget S7 Ra3)
                    (sign_extend' 64 (mword_of_int 1656 : mword 12)))]> S7).
  change (<[Regidx Ra3 := regval_into_reg
             (add_vec (rget S7 Ra3)
                (sign_extend' 64 (mword_of_int 1656 : mword 12)))]> S7) with S8.
  assert (HS8a3 : rget S8 Ra3 = (mword_of_int KernelSyms.trampoline : mword 64)).
  { rgne. rewrite /S8 upd_eq. rgne. rewrite /S7 upd_eq. exact fkr_trampoline_addr. }
  assert (HS8a5 : rget S8 Ra5 = (mword_of_int KernelSyms.userret : mword 64)).
  { rgne. rewrite /S8 upd_ne; [| reg_neq]. rewrite -HS6a5. rgne. reflexivity. }
  assert (Hp84 : add_vec_int (mword_of_int (FR + 0x80) : mword 64) 4
                 = mword_of_int (FR + 0x84)) by pcw.
  iEval (rewrite Hp84) in "Hpc".
  (* ---- +0x84: c.sub a5,a5,a3 -- the offset, 0x9c ---- *)
  iEval (rewrite Hc5 Hc7) in "Hi84".
  iApply (wp_csub_s_sconf (mword_of_int (FR + 0x84)) Ra5 Ra3
            S8 (trap_res eb + av2)%nat false
            ltac:(vm_compute; discriminate) ltac:(rdok) with "Hcg Hpc Hi84").
  iApply wp_next_off_intro. iIntros "Hcg Hpc".
  set (S9 := <[Regidx Ra5 := regval_into_reg
                 (sub_vec (rget S8 Ra5) (rget S8 Ra3))]> S8).
  change (<[Regidx Ra5 := regval_into_reg
             (sub_vec (rget S8 Ra5) (rget S8 Ra3))]> S8) with S9.
  assert (HS9a5 : rget S9 Ra5 = (mword_of_int 0x9c : mword 64)).
  { rgne. rewrite /S9 upd_eq. rewrite HS8a5 HS8a3. exact fkr_userret_off. }
  assert (HS9a4 : rget S9 Ra4 = uservec_tvec).
  { rgne. rewrite /S9 upd_ne; [| reg_neq]. rewrite -HS4a4. rgne.
    rewrite /S8 upd_ne; [| reg_neq]. rewrite /S7 upd_ne; [| reg_neq].
    rewrite /S6 upd_ne; [| reg_neq]. rewrite /S5 upd_ne; [| reg_neq].
    reflexivity. }
  assert (Hp86 : add_vec_int (mword_of_int (FR + 0x84) : mword 64) 2
                 = mword_of_int (FR + 0x86)) by pcw.
  iEval (rewrite Hp86) in "Hpc".
  (* ---- +0x86: c.add a5,a5,a4 -- a5 = TRAMPOLINE + 0x9c ---- *)
  iApply (wp_cadd_s_sconf (mword_of_int (FR + 0x86)) Ra5 Ra4
            S9 (trap_res eb + av2)%nat false
            ltac:(vm_compute; discriminate) ltac:(rdok) with "Hcg Hpc Hi86").
  iApply wp_next_off_intro. iIntros "Hcg Hpc".
  set (SA := <[Regidx Ra5 := regval_into_reg
                 (add_vec (rget S9 Ra5) (rget S9 Ra4))]> S9).
  change (<[Regidx Ra5 := regval_into_reg
             (add_vec (rget S9 Ra5) (rget S9 Ra4))]> S9) with SA.
  assert (HSAa5 : rget SA Ra5 = uva 0x9c).
  { rgne. rewrite /SA upd_eq. rewrite HS9a5 HS9a4. exact fkr_tramp_userret. }
  assert (Hp88 : add_vec_int (mword_of_int (FR + 0x86) : mword 64) 2
                 = mword_of_int (FR + 0x88)) by pcw.
  iEval (rewrite Hp88) in "Hpc".
  (* ================================================================== *)
  (*  +0x88 .. +0x8c: MAKE_SATP's high bits.  THE WORD IS kvminithart's.  *)
  (* ================================================================== *)
  (* ---- +0x88: c.li a4,-1 ---- *)
  iApply (wp_cli_s_sconf (mword_of_int (FR + 0x88)) Ra4 (mword_of_int 63 : mword 6)
            (add_vec zero_reg (sign_extend' 64
               (sign_extend' 12 (mword_of_int 63 : mword 6))))
            SA (trap_res eb + av2)%nat false
            ltac:(vm_compute; discriminate) ltac:(rdok) eq_refl with "Hcg Hpc Hi88").
  iApply wp_next_off_intro. iIntros "Hcg Hpc".
  set (SB := <[Regidx Ra4 := regval_into_reg
                 (add_vec zero_reg (sign_extend' 64
                    (sign_extend' 12 (mword_of_int 63 : mword 6))))]> SA).
  change (<[Regidx Ra4 := regval_into_reg
             (add_vec zero_reg (sign_extend' 64
                (sign_extend' 12 (mword_of_int 63 : mword 6))))]> SA) with SB.
  assert (Hp8a : add_vec_int (mword_of_int (FR + 0x88) : mword 64) 2
                 = mword_of_int (FR + 0x8a)) by pcw.
  iEval (rewrite Hp8a) in "Hpc".
  (* ---- +0x8a: c.slli a4,a4,0x3f ---- *)
  iApply (wp_cslli_s_sconf (mword_of_int (FR + 0x8a)) (Regidx Ra4) Ra4
            (mword_of_int 63 : mword 6) SB (trap_res eb + av2)%nat false
            eq_refl ltac:(vm_compute; discriminate) ltac:(rdok) with "Hcg Hpc Hi8a").
  iApply wp_next_off_intro. iIntros "Hcg Hpc".
  set (SC := <[Regidx Ra4 := regval_into_reg
                 (shift_bits_left (rget SB Ra4)
                    (subrange_vec_dec (mword_of_int 63 : mword 6)
                       (Z.sub log2_xlen 1) 0))]> SB).
  change (<[Regidx Ra4 := regval_into_reg
             (shift_bits_left (rget SB Ra4)
                (subrange_vec_dec (mword_of_int 63 : mword 6)
                   (Z.sub log2_xlen 1) 0))]> SB) with SC.
  assert (Hp8c : add_vec_int (mword_of_int (FR + 0x8a) : mword 64) 2
                 = mword_of_int (FR + 0x8c)) by pcw.
  iEval (rewrite Hp8c) in "Hpc".
  (* ---- +0x8c: c.or a0,a0,a4 -- MAKE_SATP, kvminithart's own word ---- *)
  iEval (rewrite Hc2 Hc6) in "Hi8c".
  assert (Hor : or_vec (rget SC Ra0) (rget SC Ra4)
                = kvi_satp_word (ud_root (pv_upt V'))).
  { assert (HSCa0 : rget SC Ra0
              = shift_bits_right
                  (zero_extend' 64 (concat_vec (ud_root (pv_upt V'))
                                      (zeros' 12 : mword 12)))
                  (subrange_vec_dec (mword_of_int 12 : mword 6)
                     (Z.sub log2_xlen 1) 0)).
    { rgne. rewrite /SC upd_ne; [| reg_neq]. rewrite /SB upd_ne; [| reg_neq].
      rewrite /SA upd_ne; [| reg_neq]. rewrite /S9 upd_ne; [| reg_neq].
      rewrite /S8 upd_ne; [| reg_neq]. rewrite /S7 upd_ne; [| reg_neq].
      rewrite /S6 upd_ne; [| reg_neq]. rewrite /S5 upd_ne; [| reg_neq].
      rewrite /S4 upd_ne; [| reg_neq]. rewrite /S3 upd_ne; [| reg_neq].
      rewrite /S2 upd_ne; [| reg_neq]. rewrite /S1 upd_eq. rgne.
      rewrite /S0 upd_eq. reflexivity. }
    assert (HSCa4 : rget SC Ra4
              = shift_bits_left
                  (add_vec zero_reg (sign_extend' 64
                     (sign_extend' 12 (mword_of_int 63 : mword 6))))
                  (subrange_vec_dec (mword_of_int 63 : mword 6)
                     (Z.sub log2_xlen 1) 0)).
    { rgne. rewrite /SC upd_eq. rgne. rewrite /SB upd_eq. reflexivity. }
    rewrite HSCa0 HSCa4. unfold kvi_satp_word. reflexivity. }
  iApply (wp_cor_s_sconf (mword_of_int (FR + 0x8c)) Ra0 Ra0 Ra4
            (kvi_satp_word (ud_root (pv_upt V'))) SC (trap_res eb + av2)%nat false
            ltac:(vm_compute; discriminate) ltac:(rdok) Hor with "Hcg Hpc Hi8c").
  iApply wp_next_off_intro. iIntros "Hcg Hpc".
  set (SD := <[Regidx Ra0 := regval_into_reg
                 (kvi_satp_word (ud_root (pv_upt V')))]> SC).
  change (<[Regidx Ra0 := regval_into_reg
             (kvi_satp_word (ud_root (pv_upt V')))]> SC) with SD.
  assert (Hp8e : add_vec_int (mword_of_int (FR + 0x8c) : mword 64) 2
                 = mword_of_int (FR + 0x8e)) by pcw.
  iEval (rewrite Hp8e) in "Hpc".
  (* the process block, back in one piece *)
  iEval (rewrite Haddrpg) in "Hpgt".
  iDestruct ("Hpvback" $! (pv_upt V') ltac:(apply uptd_ext_sz_refl)
               with "Hsz Hpgt Hppt") as "Hpv".
  rewrite upd_upt_id.
  (* ================================================================== *)
  (*  +0x8e: c.jalr a5 -- into userret, and never back.                   *)
  (* ================================================================== *)
  assert (HSDa5 : rget SD Ra5 = uva 0x9c).
  { rgne. rewrite /SD upd_ne; [| reg_neq]. rewrite /SC upd_ne; [| reg_neq].
    rewrite /SB upd_ne; [| reg_neq]. rewrite -HSAa5. rgne. reflexivity. }
  iApply (wp_cjalr_s_sconf (mword_of_int (FR + 0x8e)) Ra5 Rra
            SD (trap_res eb + av2)%nat false
            ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
            ltac:(rdok) with "Hcg Hpc Hi8e").
  iApply wp_next_off_intro. iIntros "Hcg Hpc".
  set (SE := <[Regidx Rra := regval_into_reg
                 (add_vec_int (mword_of_int (FR + 0x8e) : mword 64) 2)]> SD).
  change (<[Regidx Rra := regval_into_reg
             (add_vec_int (mword_of_int (FR + 0x8e) : mword 64) 2)]> SD) with SE.
  iEval (rewrite HSDa5 fkr_ret_pc) in "Hpc".
  (* ================================================================== *)
  (*  THE EXIT: the bundle taken apart into the loop's own premises.      *)
  (* ================================================================== *)
  iDestruct (sie_cap_gpr_split with "Hcg") as "(Hhs & Hsc & Hcap & Hfile)".
  (* [sconf] is destructured DIRECTLY, not through [sconf_priv_open]: the
     loop wants [mie]/[mideleg]/[menvcfg]/[cur_privilege] as loose cells,
     which the closer would re-park. *)
  iDestruct "Hsc" as "(#Hhw & #Hmin & Hprivc & Hmsx & Hmiex & Hmenvx)".
  iDestruct "Hmsx" as (msg) "(Hms & Hhalf & Htie & %Hmsg)".
  iDestruct "Hcap" as "(Hstk & Hstr & Harm & #Hwit)".
  (* THE QUARTER'S VALUE IS NOT A DEGREE OF FREEDOM.  prepare_return leaves
     it existential because it never reads it; the arm it also hands back is
     at [false], and [sie_arm_half_agree] reads the live SIE off that index,
     so the half / quarter agreement pins it -- which is what makes the sret
     legal ([ut_exit_ms_ok]). *)
  iDestruct (sie_arm_half_agree false p msg with "Hhalf Harm") as %Hsie0.
  iDestruct (ghost_var_agree with "Hhalf Hq4") as %Hvb.
  rewrite Hsie0 in Hvb. rewrite -Hvb.
  iDestruct (sret_bits_agree _ _ _ _ with "Htie Hsret") as %[Hspp2 Hspie2].
  iAssert (sconf_msown msg) with "[Hms Hhalf Htie]" as "Hmsown".
  { rewrite /sconf_msown. iSplitL "Hms"; [iExact "Hms"|].
    iSplitL "Hhalf"; [iExact "Hhalf"|].
    iSplitL "Htie"; [iExact "Htie"|]. iPureIntro. exact Hmsg. }
  iDestruct (ut_exit_ms_ok msg with "Hmsown Hsret Hq4") as %Hretms.
  iDestruct "Hmsown" as "(Hms & Hhalf & Htie & _)".
  rewrite /sret_tie Hspp2 Hspie2.
  rewrite Hsie0.
  iDestruct "Hmiex" as (mdv0) "(Hmie & Hmdl & %Hmask)".
  iDestruct "Hmenvx" as (menvcfg0') "(Hmenv & _ & _ & _ & _ & %Hmeq)".
  subst menvcfg0'.
  iDestruct "Hscause" as (scv) "Hscause".
  iDestruct "Hstval" as (stv) "Hstval".
  (* the three persistent per-hart pins the loop wants, copied out of the
     per-cpu bundle and put straight back *)
  iDestruct (cpu_own_csrs_open with "Hcpu") as "[Hcsrs Hcsback]".
  iDestruct "Hcsrs" as "(Hsscr & #Hmedlc & #Hmsec & #Hssec)".
  iDestruct ("Hcsback" with "[Hsscr]") as "Hcpu".
  { iFrame "Hmedlc Hmsec Hssec". iExact "Hsscr". }
  iPoseProof (hw_config_senvcfg with "Hhw") as "#Hsenvc".
  (* ---- the stack: the dead frame merges back into the free claim ---- *)
  assert (HSEsp : SE !!! Regidx csp_rs1 = pa_stk ksp 6).
  { rewrite /SE upd_ne; [| reg_neq]. rewrite /SD upd_ne; [| reg_neq].
    rewrite /SC upd_ne; [| reg_neq]. rewrite /SB upd_ne; [| reg_neq].
    rewrite /SA upd_ne; [| reg_neq]. rewrite /S9 upd_ne; [| reg_neq].
    rewrite /S8 upd_ne; [| reg_neq]. rewrite /S7 upd_ne; [| reg_neq].
    rewrite /S6 upd_ne; [| reg_neq]. rewrite /S5 upd_ne; [| reg_neq].
    rewrite /S4 upd_ne; [| reg_neq]. rewrite /S3 upd_ne; [| reg_neq].
    rewrite /S2 upd_ne; [| reg_neq]. rewrite /S1 upd_ne; [| reg_neq].
    rewrite /S0 upd_ne; [| reg_neq]. exact Hmfsp. }
  iEval (rewrite HSEsp) in "Hstk".
  iAssert (stack_own (KTR := KT1) ksp 4) with "[Hbra Hbs0 Hbs1 Hbsc]" as "Hf14".
  { iApply (stack_own_4_intro (KTR := KT1) ksp with "Hbra Hbs0 Hbs1 Hbsc"). }
  iAssert (stack_own (KTR := KT1) ksp 6) with "[Hf14 Hf56]" as "Hf16".
  { iApply (stack_own_split_2 (KTR := KT1) ksp 4 6 ltac:(lia)).
    iSplitL "Hf14"; [iExact "Hf14" | iExact "Hf56"]. }
  iAssert (stack_own (KTR := KT1) ksp av) with "[Hstk Hf16]" as "Hstack".
  { rewrite Havsum.
    iApply (bi.equiv_entails_1_2 _ _ (stack_own_app (KTR := KT1) ksp 6 (trap_res eb + av2))).
    iSplitL "Hf16"; [iExact "Hf16" | iExact "Hstk"]. }
  (* ---- the trap-side residue, and the table it hands userret ---- *)
  iAssert (ut_trap p ksp av ∅)
    with "[Hstack Hstr Harm Hkptr Hhalf Hq4 Htie Hsret Hcpu Hclaim]" as "Htrap".
  { rewrite /ut_trap /ut_stack /ut_ghosts.
    iSplitL "Hstack". { iExact "Hstack". }
    iSplitL "Hstr". { iExact "Hstr". }
    iSplitL "Harm". { iExact "Harm". }
    iSplitL "Hkptr". { iExact "Hkptr". }
    iSplitL "Hhalf Hq4 Htie Hsret".
    { iSplitL "Hhalf". { iExact "Hhalf". }
      iSplitL "Hq4". { iExact "Hq4". }
      iSplitL "Htie". { iExact "Htie". }
      iExact "Hsret". }
    iSplitL "Hcpu". { iExact "Hcpu". }
    iExact "Hclaim". }
  iDestruct (ut_trap_tlb_open with "Htrap") as (kroot) "[Hkres Hparked]".
  iDestruct (fkr_kpt_of_res with "Hkres") as "[#Hkptinv Hkres]".
  (* ---- the address space, split off the block for the user tier ---- *)
  iEval (rewrite proc_priv_split_pt) in "Hpv".
  iDestruct "Hpv" as "[Hpnopt Hpt]".
  iEval (rewrite HuptV') in "Hpt".
  iEval (rewrite proc_pt_split) in "Hpt".
  iDestruct "Hpt" as "[[%Hwf2 Hufr] Hdata]".
  iEval (rewrite proc_pt_own_udata -Hnorm) in "Hdata".
  assert (Hcov : udata_cov (ud_um pt) (ud_data pt))
    by (rewrite Hnorm; exact (ud_pas_cov pt)).
  destruct Hptwf as (Hmapwf & Haccwf & Hpv1 & Hpv2 & Hpv3).
  (* ---- and the residue, handed to the caller's wand ---- *)
  iAssert (forkret_yield (CID := CIDf) γf p ksp pid av V')
    with "[Hparked Hpnopt]" as "Hyld".
  { rewrite /forkret_yield.
    iSplitL "Hparked"; [iExact "Hparked" | iExact "Hpnopt"]. }
  iDestruct ("Hyield" $! CIDf V' with "[%] Hyld") as "Hures";
    [exact HuptV' |].
  (* ---- the config record for this round ---- *)
  destruct Hretms as (HSIE & HMPRV & HSXL & HTVM & HMXR & HTSR & HFS & HVS & Hsup).
  assert (HSEa0 : tp_pin SE !!! Regidx (mword_of_int 10)
                  = kvi_satp_word (ud_root pt)).
  { rewrite /tp_pin upd_ne; [| reg_neq]. rewrite /SE upd_ne; [| reg_neq].
    rewrite /SD upd_eq HuptV'. reflexivity. }
  iApply (UC.wp_userret_closed (CID := CIDf)
            (loop_ucfg mdv0 Hmask) pt kroot j ksp (tp_pin SE)
            (kvi_satp_word (ud_root pt)) msg (mepc_val epc) scv stv
            (loop_ok_loop_ucfg mdv0 Hmask pt Hnorm
               (conj Hmapwf (conj Haccwf (conj Hpv1 (conj Hpv2 Hpv3)))))
            Hjlt Hgap (fun h ksp' ws Hl => Hkw h kroot ksp' ws Hl)
            HSIE HMPRV HSXL HTVM HMXR HTSR HFS HVS Hsup Hmapwf HSEa0
            (conj (kvi_satp_mode _) (conj (kvi_satp_asid _) (kvi_satp_ppn _)))
            Hcov Haccwf
            with "Htext Hhw Hmin Hwire Hclaimmap Hkptinv Hhs Hprivc Hms Hmie
                 Hmdl Hmenv Hsenvc Hsepc Hscause Hstval Hstvec Hmedlc Hmsec
                 Hssec Hkres Hufr Hdata Hpc Hfile Hures").
Qed.

End ForkretProof.
