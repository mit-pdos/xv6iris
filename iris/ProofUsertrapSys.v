(* ProofUsertrapSys.v -- usertrap's SYSCALL arm, +0x90 .. +0xa2.

       if (r_scause() == 8) {
         if (killed(p)) kexit(-1);
         p->trapframe->epc += 4;      // return to the instruction AFTER ecall
         intr_on();
         syscall();
       }

   THE ONLY ARM THAT RE-ENABLES INTERRUPTS, and everything unusual about it
   follows from that one instruction:

   * the [csrsi sstatus,2] at +0x9e is where [K_usertrap]'s [kv_frame_slots]
     summand is SPENT.  [WpSconfCsr.wp_csrsi_sstatus_x0_enable_s_sconf] is
     stated at pre index [trap_res true + n] and post index [n], so the 90
     slots a NESTED kernelvec trap would need come out of usertrap's own budget
     here -- and [UsertrapRes.ut_nx_bound_off] is the bound that says they are
     there, available on THIS arm precisely because it has not spent a reserve
     yet.  (claude-notes/projects/usertrap.md, finding 3.)
   * everything up to and including the [csrsi] runs at [b = false], so there
     is not one crossing in it: every [wp_next] collapses with
     [wp_next_off_intro] at the same hart, and not one [(CID := ...)]
     annotation is needed.  The [jal syscall] at +0xa2 is the FIRST
     interrupts-enabled step of the whole function, and from there on the hart
     can move -- which is why the block hands the rest to [UtTail.ut_a6] at
     [b := true] and at syscall's resuming hart.
   * the trap-CSR set must ALREADY be folded when this block is entered: the
     [csrsi] consumes [trap_csrs] whole (it re-forms [intr_res] inside the
     arm), and so does the [kexit(-1)] on the killed path.  Both are covered
     by taking [ut_hold (kt := kt)] at [false], whose [trap_csrs_ext false] IS the bundle.

   The [j +0x96] after the [jal kexit] at +0xca is DEAD and never decoded:
   kexit has no continuation. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExtras RiscvFetchExec.
Require Import PageGeom.
Require Import RegFile HartTp WpNext CpuOwn.
Require Import WpMmodeLeafBase.
Require Import SmodeCore.
Require Import StackOwn CalleeSaved.
Require Import InstrBytes.
Require Import KernelText KernelDataInv.
Require Import WpSconfAlu WpSconfMem WpSconfCtl WpSconfCsr WpSconfBtype.
Require Import WpSmodeIntr.
Require Import IntrDefs.
Require Import WpLock.
Require Import ProcGeom.
Require Import UserPtTree ProcPtOwn.
Require Import KptTree TrampPt.
Require Import KallocInv.
Require Import DiskPtsto WpUart FsBlocks LogInv FsCrash.
Require Import BioDefs.
Require Import IrefSlots InodeRegion.
Require Import FdSlots ProcInv.
Require Import FileInvDefs.
Require Import SchedCtx.
Require Import CodeUsertrap.
Require Import SpecKilled SpecKexit SpecYield SpecPrepareReturn.
Require Import SpecSyscall SpecSysExit.
Require Import SpecUsertrap UsertrapRes.
Require Import ProofUsertrapParts ProofPrepareReturnParts.
Require Import ProofUsertrapTail.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import ProcAvail.
Import Defs.
Local Open Scope Z_scope.
Set Printing Depth 40.

Module UtSys (PR : PREPARE_RETURN) (KI : KILLED) (KE : KEXIT) (YI : YIELD)
             (SY : SYSCALL).

Module T := UtTail PR KI KE YI.

Notation Rra := (mword_of_int 1  : mword 5).
Notation Rs0 := (mword_of_int 8  : mword 5).
Notation Rs1 := (mword_of_int 9  : mword 5).
Notation Rs2 := (mword_of_int 18 : mword 5).
Notation Ra0 := (mword_of_int 10 : mword 5).
Notation Ra4 := (mword_of_int 14 : mword 5).
Notation Ra5 := (mword_of_int 15 : mword 5).

Ltac reg_neq :=
  lazymatch goal with |- ?a <> ?b =>
    tryif unify a b then fail else (vm_compute; discriminate) end.

Ltac pcw := apply bv_eq; vm_compute; reflexivity.

Section UtSysBlock.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !bioG Σ,
            !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ, !fsCrashG Σ,
            !kallocG Σ, !irefslotG Σ, !pavG Σ, !iregG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Context {kt : ktier}.
  (* the trapframe page's own [page_valid], read off [proc_priv] without
     consuming it -- [proc_pt_wf]'s last conjunct.  A PURE-goal [iDestruct]
     does not spend the resource (durable-notes.md), so [Hpv] is still
     whole for [proc_priv_tf_upd] right afterward. *)
  Local Lemma ut_tfp_valid (γf : gname) (pa : mword 64) (pid : mword 32) (V : pprivate) :
    proc_priv γf pa pid V -∗ ⌜page_valid (page_base (ud_tfp (pv_upt V)))⌝.
  Proof.
    iIntros "[(_ & _ & _ & _ & Hpt & _) _]".
    rewrite /proc_pt_at. iDestruct "Hpt" as "(_ & _ & Hptt)".
    iDestruct (proc_pt_wf_get with "Hptt") as "%Hwf".
    iPureIntro. exact (proj2 (proj2 (proj2 (proj2 Hwf)))).
  Qed.

  Lemma ut_90 (N : ut_names) (V : pprivate) (pt : uptd) (ksp : mword 64)
      (m0 m : regfile) (av nx : nat)
      (mie_v menvcfg0 : mword 64) (lks : gset string) :
    ut_wf N ->
    (K_usertrap <= av)%nat ->
    (trap_res false + nx)%nat = (av - 4)%nat ->
    ud_tfp (pv_upt V) = ud_tfp pt ->
    add_vec (un_ks N) (mword_of_int 4096) = ksp ->
    m0 !!! Regidx csp_rs1 = ksp ->
    m !!! Regidx csp_rs1 = pa_stk ksp 4 ->
    m !!! Regidx Rs1 = un_pj N ->
    (* a0 STILL HOLDS p: the dispatch never overwrote myproc's return value,
       which is why the [jal killed] here has no [c.mv a0,s1] in front of it
       while the one at +0xa6 does. *)
    m !!! Regidx Ra0 = un_pj N ->
    ut_cs m0 m ->
    mie_v = MIE_S ->
    menvcfg0 = MENVCFG_S ->
    kernel_text -∗
    pc_is (mword_of_int (UT + 0x90)) -∗
    sie_cap_gpr kt m nx false (un_pj N) -∗
    ut_hold (kt := kt) (SY.syscall_env (kt := kt)) N V false lks -∗
    ut_frame (kt := kt) ksp (m0 !!! Regidx Rra) (m0 !!! Regidx Rs0)
                 (m0 !!! Regidx Rs1) (m0 !!! Regidx Rs2) -∗
    wp_next true (un_pj N)
      (fun CID' => usertrap_post (CID := CID') (ut_res (kt := kt) SY.syscall_env (kt := kt)) pt ksp m0
                     mie_v menvcfg0) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hwf Hav Hnx Htfpe Hksp Hm0sp Hmsp Hms1 Hma0 Hcs Hmiev Hmenvv.
    pose proof (ut_nx_bound false av nx Hav Hnx) as Hks.
    pose proof (ut_nx_bound_off av nx Hav Hnx) as Hkso.
    
    pose proof Hwf as Hwf'. destruct Hwf as (Hj & Hjl & Hlen & Hlg).
    iIntros "#Htext Hpc Hcg Hhold Hframe Hcont".
    iDestruct "Hhold" as "(Hcpu & Hcsrs & Hclm & [#Hcaps Hown])".
    (* depth 0 forces the held set empty, so killed/kexit's order premises
       need no hypothesis of this lemma's own. *)
    iDestruct (cpu_own_zero_empty with "Hcpu") as "[%Hlkempty Hcpu]".
    iAssert (procs_inv (kt := kt) (un_s N)) with "[]" as "#Hpi".
    { iDestruct "Hcaps" as "($ & _)". }
    iAssert (kernel_data) with "[]" as "#Hkd".
    { iDestruct "Hcaps" as "(_ & $ & _)". }
    iPoseProof (uti_090 with "Htext") as "Hi90".
    iPoseProof (uti_094 with "Htext") as "Hi94".
    (* ---- +0x90: jal killed ---- *)
    iApply (wp_jal_s_sconf (mword_of_int (UT + 0x90)) Rra
              (mword_of_int 2095894 : mword 21) m nx false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi90 [-]").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    set (M1 := <[Regidx Rra := regval_into_reg
                   (add_vec_int (mword_of_int (UT + 0x90) : mword 64) 4)]> m).
    change (<[Regidx Rra := regval_into_reg
               (add_vec_int (mword_of_int (UT + 0x90) : mword 64) 4)]> m) with M1.
    assert (Hkilled : add_vec (mword_of_int (UT + 0x90) : mword 64)
                        (sign_extend' 64 (mword_of_int 2095894 : mword 21))
                      = mword_of_int KernelSyms.killed) by pcw.
    iEval (rewrite Hkilled) in "Hpc".
    assert (HM1sp : M1 !!! Regidx csp_rs1 = pa_stk ksp 4)
      by (rewrite /M1 upd_ne; [exact Hmsp | reg_neq]).
    assert (HM1s1 : M1 !!! Regidx Rs1 = un_pj N)
      by (rewrite /M1 upd_ne; [exact Hms1 | reg_neq]).
    assert (HM1a0 : M1 !!! Regidx Ra0 = proc_addr (un_j N))
      by (rewrite /M1 upd_ne; [exact Hma0 | reg_neq]).
    assert (HM1ra : M1 !!! Regidx Rra = mword_of_int (UT + 0x94))
      by (rewrite /M1 upd_eq; pcw).
    assert (HcsM1 : ut_cs m0 M1)
      by (rewrite /M1; apply ut_cs_insert; [vm_compute; reflexivity | exact Hcs]).
    iApply (KI.wp_killed_sconf kt (un_s N) (un_j N) (un_l N)
              M1 nx 0%nat false (un_pj N) false lks
              HM1a0 Hj Hjl ltac:(vm_compute; reflexivity) ltac:(lia)
              with "Hcg Hcpu Htext Hpc Hpi [-]").
    all: try lkbelow.
    iApply wp_next_off_intro. iIntros (mf kl) "[%Hcskl %Hkla0] Hcg Hcpu Hpc".
    assert (Hret94 : ret_pc (M1 !!! Regidx Rra) = mword_of_int (UT + 0x94))
      by (rewrite HM1ra; pcw).
    iEval (rewrite Hret94) in "Hpc".
    assert (Hmfsp : mf !!! Regidx csp_rs1 = pa_stk ksp 4)
      by (rewrite (callee_saved_lookup Hcskl csp_rs1
                     ltac:(vm_compute; reflexivity)); exact HM1sp).
    assert (Hmfs1 : mf !!! Regidx Rs1 = un_pj N)
      by (rewrite (callee_saved_lookup Hcskl Rs1
                     ltac:(vm_compute; reflexivity)); exact HM1s1).
    assert (Hcsmf : ut_cs m0 mf)
      by exact (ut_cs_trans m0 M1 mf HcsM1 (ut_cs_of_callee_saved _ _ Hcskl)).
    assert (Hc2 : creg2reg_idx (Cregidx (mword_of_int 2)) = Regidx Ra0)
      by (vm_compute; reflexivity).
    assert (Hrgmf : rget mf Ra0 = sign_extend' 64 kl).
    { rgne. exact Hkla0. }
    (* ---- +0x94: c.bnez a0 ---- *)
    destruct (neq_vec (sign_extend' 64 kl) (zero_reg : mword 64)) eqn:Hnz.
    - (* KILLED: kexit(-1) at +0xc8.  A dead end. *)
      iPoseProof (uti_0c8 with "Htext") as "Hic8".
      iPoseProof (uti_0ca with "Htext") as "Hica".
      iApply (wp_cbnez_taken_s_sconf (mword_of_int (UT + 0x94))
                (mword_of_int 26 : mword 8) (Cregidx (mword_of_int 2)) Ra0
                mf nx false Hc2 ltac:(vm_compute; discriminate)
                ltac:(rewrite Hrgmf; exact Hnz) ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi94 [-]").
      iNext. iApply wp_next_off_intro. iIntros "Hcg Hpc".
      assert (Hpc8 : add_vec (mword_of_int (UT + 0x94) : mword 64)
                       (sign_extend' 64 (sign_extend' 13
                          (concat_vec (mword_of_int 26 : mword 8) ('b"0"))))
                     = mword_of_int (UT + 0xc8)) by pcw.
      iEval (rewrite Hpc8) in "Hpc".
      (* +0xc8 c.li a0,-1 *)
      iApply (wp_cli_s_sconf (mword_of_int (UT + 0xc8)) Ra0
                (mword_of_int 63 : mword 6)
                (add_vec zero_reg (sign_extend' 64
                   (sign_extend' 12 (mword_of_int 63 : mword 6))))
                mf nx false ltac:(vm_compute; discriminate) ltac:(rdok) eq_refl
                with "Hcg Hpc Hic8 [-]").
      iApply wp_next_off_intro. iIntros "Hcg Hpc".
      set (K1 := <[Regidx Ra0 := regval_into_reg
                     (add_vec zero_reg (sign_extend' 64
                        (sign_extend' 12 (mword_of_int 63 : mword 6))))]> mf).
      change (<[Regidx Ra0 := regval_into_reg
                 (add_vec zero_reg (sign_extend' 64
                    (sign_extend' 12 (mword_of_int 63 : mword 6))))]> mf) with K1.
      assert (Hpca : add_vec_int (mword_of_int (UT + 0xc8) : mword 64) 2
                     = mword_of_int (UT + 0xca)) by pcw.
      iEval (rewrite Hpca) in "Hpc".
      (* +0xca jal kexit *)
      iApply (wp_jal_s_sconf (mword_of_int (UT + 0xca)) Rra
                (mword_of_int 2095532 : mword 21) K1 nx false
                ltac:(vm_compute; discriminate) ltac:(rdok)
                ltac:(vm_compute; reflexivity) with "Hcg Hpc Hica [-]").
      iApply wp_next_off_intro. iIntros "Hcg Hpc".
      assert (Hkex : add_vec (mword_of_int (UT + 0xca) : mword 64)
                       (sign_extend' 64 (mword_of_int 2095532 : mword 21))
                     = mword_of_int KernelSyms.kexit) by pcw.
      iEval (rewrite Hkex) in "Hpc".
      iApply (T.ut_kexit SY.syscall_env (kt := kt) N V
                (<[Regidx Rra := regval_into_reg
                     (add_vec_int (mword_of_int (UT + 0xca) : mword 64) 4)]> K1)
                nx false lks Hwf' ltac:(lia)
                with "Htext Hpc Hcg [-]").
      all: try lkbelow.
      rewrite /ut_hold. iSplitL "Hcpu"; [iExact "Hcpu"|].
      iSplitL "Hcsrs"; [iExact "Hcsrs"|].
      iSplitL "Hclm"; [iExact "Hclm"|].
      rewrite /ut_env. iSplitR; [iExact "Hcaps" | iExact "Hown"].
    - (* NOT killed: the epc bump, intr_on, syscall. *)
      iPoseProof (uti_096 with "Htext") as "Hi96".
      iPoseProof (uti_098 with "Htext") as "Hi98".
      iPoseProof (uti_09a with "Htext") as "Hi9a".
      iPoseProof (uti_09c with "Htext") as "Hi9c".
      iPoseProof (uti_09e with "Htext") as "Hi9e".
      iPoseProof (uti_0a2 with "Htext") as "Hia2".
      iApply (wp_cbnez_fall_s_sconf (mword_of_int (UT + 0x94))
                (mword_of_int 26 : mword 8) (Cregidx (mword_of_int 2)) Ra0
                mf nx false Hc2 ltac:(vm_compute; discriminate)
                ltac:(rewrite Hrgmf; exact Hnz) with "Hcg Hpc Hi94 [-]").
      iApply wp_next_off_intro. iIntros "Hcg Hpc".
      assert (Hp96 : add_vec_int (mword_of_int (UT + 0x94) : mword 64) 2
                     = mword_of_int (UT + 0x96)) by pcw.
      iEval (rewrite Hp96) in "Hpc".
      (* the trapframe page, borrowed for the epc bump.  Destructured
         directly (not via [ut_own_priv]) because the call below needs FIVE
         more of [ut_own]'s conjuncts than that accessor hands out --
         [SpecSyscall.v]'s header on why the five families ride through
         [syscall()] on this same channel rather than inside [Hsy]. *)
      iDestruct "Hown" as "(Hbs & Hbm & Hip & Hfd & Hir & Hpv & Hsy)".
      (* the epc word EXISTS -- read off the page's own length invariant while
         the block is still whole, because [ut_epc_exists] is a pure read and
         [proc_priv_tf_upd] below consumes the block. *)
      iDestruct (ut_epc_exists with "Hpv") as %Hepcx.
      destruct Hepcx as [uepc Hepc].
      iDestruct (ut_tfp_valid with "Hpv") as %Hpv_valid.
      iDestruct (proc_priv_tf_upd with "Hpv") as "(Htfc & Htfp & Hpvback)".
      (* [pt_node_claim], off [hw_config] (peeled from [Hcg] persistently)
         and [Hpv_valid] -- the mem-tier convenience wrapper is what the
         VA-tier [c.ld]/[c.sd] through the kernel identity map needs
         (ProcInv.v's header on [tf_page_word_mem]). *)
      iDestruct (sie_cap_gpr_dup_hw_config with "Hcg") as "[Hhw Hcg]".
      iDestruct "Hhw" as (misa0 mseccfg0 pmar0 elp0)
        "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & #Hsenv & %HmisaS & %HmisaC &
          %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np &
          %HmisaA & %Hmisa_val0 & %Hmseccfg_val0 & #Hkmapb)".
      iPoseProof (pt_node_claim_from_static (ud_tfp (pv_upt V)) Hpv_valid with "Hkmapb") as "#Hptc".
      iDestruct (tf_page_word_upd_mem _ _ tf_epc_idx uepc ltac:(vm_compute; lia) Hepc
                   with "Hptc Htfp")
        as "(Hword & Htfback)".
      (* ---- +0x96: c.ld a4,88(s1) -- a4 := p->trapframe ---- *)
      assert (Haddrtf : add_vec (rget mf Rs1)
                          (sign_extend' 64 (mword_of_int 88 : mword 12))
                        = p_trapframe (un_pj N))
        by (rgne; rewrite Hmfs1; apply prr_p_trapframe).
      iEval (rewrite -Haddrtf) in "Htfc".
      iApply (wp_cld_s_sconf (mword_of_int (UT + 0x96)) Ra4 Rs1
                (mword_of_int 88 : mword 12) mf nx
                (page_base (ud_tfp (pv_upt V))) false
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi96 Htfc [-]").
      iApply wp_next_off_intro. iIntros "Hcg Hpc Htfc".
      iEval (rewrite Haddrtf) in "Htfc".
      set (S1 := <[Regidx Ra4 := regval_into_reg
                     (page_base (ud_tfp (pv_upt V)))]> mf).
      change (<[Regidx Ra4 := regval_into_reg
                 (page_base (ud_tfp (pv_upt V)))]> mf) with S1.
      assert (Hp98 : add_vec_int (mword_of_int (UT + 0x96) : mword 64) 2
                     = mword_of_int (UT + 0x98)) by pcw.
      iEval (rewrite Hp98) in "Hpc".
      assert (HS1a4 : rget S1 Ra4 = page_base (ud_tfp (pv_upt V)))
        by (rgne; rewrite /S1 upd_eq; reflexivity).
      assert (Haddrw : add_vec (rget S1 Ra4)
                         (sign_extend' 64 (mword_of_int 24 : mword 12))
                       = tf_pa (ud_tfp (pv_upt V)) (8 * Z.of_nat tf_epc_idx))
        by (rewrite HS1a4; apply prr_tf_addr_24).
      (* ---- +0x98: c.ld a5,24(a4) -- a5 := epc ---- *)
      iEval (rewrite -Haddrw) in "Hword".
      iApply (wp_cld_s_sconf (mword_of_int (UT + 0x98)) Ra5 Ra4
                (mword_of_int 24 : mword 12) S1 nx uepc false
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi98 Hword [-]").
      iApply wp_next_off_intro. iIntros "Hcg Hpc Hword".
      iEval (rewrite Haddrw) in "Hword".
      set (S2 := <[Regidx Ra5 := regval_into_reg uepc]> S1).
      change (<[Regidx Ra5 := regval_into_reg uepc]> S1) with S2.
      assert (Hp9a : add_vec_int (mword_of_int (UT + 0x98) : mword 64) 2
                     = mword_of_int (UT + 0x9a)) by pcw.
      iEval (rewrite Hp9a) in "Hpc".
      (* ---- +0x9a: c.addi a5,a5,4 ---- *)
      iApply (wp_caddi_s_sconf (mword_of_int (UT + 0x9a)) Ra5
                (mword_of_int 4 : mword 6) S2 nx false
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi9a [-]").
      iApply wp_next_off_intro. iIntros "Hcg Hpc".
      set (S3 := <[Regidx Ra5 := regval_into_reg
                     (add_vec (rget S2 Ra5)
                        (sign_extend' 64 (sign_extend' 12 (mword_of_int 4 : mword 6))))]> S2).
      change (<[Regidx Ra5 := regval_into_reg
                 (add_vec (rget S2 Ra5)
                    (sign_extend' 64 (sign_extend' 12 (mword_of_int 4 : mword 6))))]> S2)
        with S3.
      assert (Hp9c : add_vec_int (mword_of_int (UT + 0x9a) : mword 64) 2
                     = mword_of_int (UT + 0x9c)) by pcw.
      iEval (rewrite Hp9c) in "Hpc".
      (* ---- +0x9c: c.sd a5,24(a4) ---- *)
      assert (HS3a4 : rget S3 Ra4 = page_base (ud_tfp (pv_upt V))).
      { rgne. rewrite /S3 upd_ne; [| reg_neq]. rewrite /S2 upd_ne; [| reg_neq].
        rewrite /S1 upd_eq. reflexivity. }
      assert (Haddrw3 : add_vec (rget S3 Ra4)
                          (sign_extend' 64 (mword_of_int 24 : mword 12))
                        = tf_pa (ud_tfp (pv_upt V)) (8 * Z.of_nat tf_epc_idx))
        by (rewrite HS3a4; apply prr_tf_addr_24).
      iEval (rewrite -Haddrw3) in "Hword".
      iApply (wp_csd_s_sconf (mword_of_int (UT + 0x9c)) Ra5 Ra4
                (mword_of_int 24 : mword 12) S3 nx uepc false
                with "Hcg Hpc Hi9c Hword [-]").
      iApply wp_next_off_intro. iIntros "Hcg Hpc Hword".
      iEval (rewrite Haddrw3) in "Hword".
      assert (Hp9e : add_vec_int (mword_of_int (UT + 0x9c) : mword 64) 2
                     = mword_of_int (UT + 0x9e)) by pcw.
      iEval (rewrite Hp9e) in "Hpc".
      (* the page and the block, rebuilt at the bumped epc *)
      iDestruct ("Htfback" $! (rget S3 Ra5) with "Hword") as "Htfp".
      iDestruct ("Hpvback" $! (<[tf_epc_idx := rget S3 Ra5]> (pv_tf V))
                   with "Htfc Htfp") as "Hpv".
      set (V1 := upd_tf V (<[tf_epc_idx := rget S3 Ra5]> (pv_tf V))).
      change (upd_tf V (<[tf_epc_idx := rget S3 Ra5]> (pv_tf V))) with V1.
      assert (HV1upt : pv_upt V1 = pv_upt V)
        by (rewrite /V1; destruct V; reflexivity).
      (* ---- +0x9e: csrsi sstatus,2 -- intr_on(), and the reserve is paid ---- *)
      iDestruct (ut_flip_pre (un_pj N) with "Hcpu") as "(Hcnt & Hcells)".
      (* THE CARVE, and why it needs a NAME for the remainder.  The enabling
         leaf's pre index is [trap_res true + n], so the block's own [nx] has
         to be re-spelled that way -- and [rewrite] on an equation whose LHS is
         the bare variable [nx] loops, because [nx] occurs in the right-hand
         side too.  ProofScheduler's [sc_carve] does not hit this only because
         its LHS is the compound [av - 10]. *)
      pose (n2 := (nx - kv_frame_slots)%nat).
      assert (Hn2 : n2 = (nx - kv_frame_slots)%nat) by reflexivity.
      assert (Hcarve : nx = (trap_res true + n2)%nat)
        by (rewrite Hn2; unfold trap_res in *; lia).
      iEval (rewrite Hcarve) in "Hcg".
      iApply (wp_csrsi_sstatus_x0_enable_s_sconf (mword_of_int (UT + 0x9e)) false
                S3 n2
                with "Hcg [Hcnt] [Hcsrs] [Hcells] [Hclm] Hpc Hi9e [-]").
      { iExact "Hcnt". }
      { rewrite /trap_csrs_ext. iExact "Hcsrs". }
      (* re-enabling SIE demands the empty held set -- which depth 0 already
         forces, so this is a re-spelling, not an obligation. *)
      { iEval (rewrite Hlkempty) in "Hcells". iExact "Hcells". }
      { rewrite /cpu_claim_ext. iExact "Hclm". }
      iApply wp_next_off_intro. iIntros (msf) "%Hmsf Hcg Hpc".
      assert (Hpa2 : add_vec_int (mword_of_int (UT + 0x9e) : mword 64) 4
                     = mword_of_int (UT + 0xa2)) by pcw.
      iEval (rewrite Hpa2) in "Hpc".
      (* ---- +0xa2: jal syscall -- THE FIRST ENABLED STEP ---- *)
      iApply (wp_jal_s_sconf (mword_of_int (UT + 0xa2)) Rra
                (mword_of_int 580 : mword 21) S3 n2 true
                ltac:(vm_compute; discriminate) ltac:(rdok)
                ltac:(vm_compute; reflexivity) with "Hcg Hpc Hia2 [-]").
      iIntros (CID1 Hk1) "Hcg Hpc".
      set (S4 := <[Regidx Rra := regval_into_reg
                     (add_vec_int (mword_of_int (UT + 0xa2) : mword 64) 4)]> S3).
      change (<[Regidx Rra := regval_into_reg
                 (add_vec_int (mword_of_int (UT + 0xa2) : mword 64) 4)]> S3) with S4.
      assert (Hsysc : add_vec (mword_of_int (UT + 0xa2) : mword 64)
                        (sign_extend' 64 (mword_of_int 580 : mword 21))
                      = mword_of_int KernelSyms.syscall) by pcw.
      iEval (rewrite Hsysc) in "Hpc".
      assert (HS4sp : S4 !!! Regidx csp_rs1 = pa_stk ksp 4).
      { rewrite /S4 upd_ne; [| reg_neq]. rewrite /S3 upd_ne; [| reg_neq].
        rewrite /S2 upd_ne; [| reg_neq]. rewrite /S1 upd_ne; [| reg_neq].
        exact Hmfsp. }
      assert (HS4s1 : S4 !!! Regidx Rs1 = un_pj N).
      { rewrite /S4 upd_ne; [| reg_neq]. rewrite /S3 upd_ne; [| reg_neq].
        rewrite /S2 upd_ne; [| reg_neq]. rewrite /S1 upd_ne; [| reg_neq].
        exact Hmfs1. }
      assert (HS4ra : S4 !!! Regidx Rra = mword_of_int (UT + 0xa6))
        by (rewrite /S4 upd_eq; pcw).
      assert (HcsS4 : ut_cs m0 S4).
      { rewrite /S4 /S3 /S2 /S1.
        apply ut_cs_insert; [vm_compute; reflexivity |].
        apply ut_cs_insert; [vm_compute; reflexivity |].
        apply ut_cs_insert; [vm_compute; reflexivity |].
        apply ut_cs_insert; [vm_compute; reflexivity |].
        exact Hcsmf. }
      iApply (SY.wp_syscall_sconf kt (CID := CID1) (un_f N) (un_s N) (un_j N) (un_l N)
                (un_bn N) (un_fn N) (un_us N) (un_ip N) (un_dqi N)
                S4 n2 (un_pid N) V1 lks
                Hj Hjl ltac:(rewrite Hn2; lia)
                with "Hcg [] Htext Hkd Hpc Hpi Hbs Hbm Hip Hfd Hir Hsy Hpv [-]").
      (* [cpu_own_on_intro] mints the bundle at the literal [∅]; [lks = ∅]
         at depth 0 makes that the set syscall's contract names.  It now
         takes no premise at all -- [cpu_own] carries no caller frame to
         fold in any more. *)
      { rewrite Hlkempty. iApply cpu_own_on_intro. }
      iIntros (CID2 Hk2 mg V2 us2) "%Hcsg %Htfg Hcg Hcpu Hbs Hbm Hip Hfd Hir Hsy Hpv Hpc".
      assert (Hreta6 : ret_pc (S4 !!! Regidx Rra) = mword_of_int (UT + 0xa6))
        by (rewrite HS4ra; pcw).
      iEval (rewrite Hreta6) in "Hpc".
      iDestruct (wp_next_retarget CID CID2 true (un_pj N) _
                   ltac:(wp_next_chain) with "Hcont") as "Hcont".
      (* [ut_own] rebuilt directly (mirroring the destructure above); [N]'s
         [un_us] moves to [us2] via [upd_us], and [un_fn (upd_us N us2) =
         un_fn N] ([UsertrapRes.un_fn_upd_us]) is what lets [Hbm] slot back
         in unchanged. *)
      pose (N2 := upd_us N us2).
      (* rebuilt via the dedicated lemma, not an inline [rewrite; iFrame] --
         see [UsertrapRes.ut_own_rebuild_us]'s header on why that inline
         shape degenerates in a proof state this large. *)
      iPoseProof (ut_own_rebuild_us SY.syscall_env (kt := kt) N V2 us2
                    with "Hbs Hbm Hip Hfd Hir Hpv Hsy") as "Hown".
      assert (Hmgsp : mg !!! Regidx csp_rs1 = pa_stk ksp 4)
        by (rewrite (callee_saved_lookup Hcsg csp_rs1
                       ltac:(vm_compute; reflexivity)); exact HS4sp).
      assert (Hmgs1 : mg !!! Regidx Rs1 = un_pj N)
        by (rewrite (callee_saved_lookup Hcsg Rs1
                       ltac:(vm_compute; reflexivity)); exact HS4s1).
      assert (Hcsmg : ut_cs m0 mg)
        by exact (ut_cs_trans m0 S4 mg HcsS4 (ut_cs_of_callee_saved _ _ Hcsg)).
      iApply (T.ut_a6 (CID := CID2) SY.syscall_env (kt := kt) N2 V2 pt ksp m0 mg av
                n2 true
                mie_v menvcfg0 lks
                Hwf' Hav ltac:(rewrite Hn2; unfold trap_res in *; lia)
                ltac:(rewrite Htfg HV1upt; exact Htfpe) Hksp Hm0sp
                Hmgsp Hmgs1 Hcsmg
                Hmiev Hmenvv
                with "Htext Hpc Hcg [-Hframe Hcont] Hframe Hcont").
      all: try lkbelow.
      rewrite /ut_hold. iSplitL "Hcpu"; [iExact "Hcpu"|].
      iSplitR; [rewrite /trap_csrs_ext; done|].
      iSplitR; [rewrite /cpu_claim_ext; done|].
      rewrite /ut_env. iSplitR; [iExact "Hcaps" | iExact "Hown"].
  Qed.

End UtSysBlock.

End UtSys.
