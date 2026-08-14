(* ProofUsertrap.v -- usertrap()'s ENTRY and DISPATCH blocks, and the seal.
   The last of the five blocks of the walk; ProofUsertrapTail.v (the tail),
   ProofUsertrapSys.v (the syscall arm) and ProofUsertrapArms.v (the three
   cheap arms) are the other four, and every block lemma here has their
   statement shape (claude-notes/projects/usertrap.md, "THE BLOCK
   VOCABULARY").

     ut_entry     +0x00 .. +0x2e -- the 32-byte prologue and the frame
                  pointer, the SPP test, the [csrw stvec, kernelvec], the
                  [jal myproc], and [p->trapframe->epc = r_sepc()].
     ut_dispatch  +0x30 .. +0x54 -- the scause demultiplexer, which hands
                  control to one of the four proven arms.
     UsertrapProof  the functor, sealed by [SpecUsertrap.USERTRAP].

   *** THE PANIC ARM IS REFUTED, AND THAT IS WHAT KEEPS printk'S PANIC PATH
   OUT OF usertrap'S CONE. ***

       if ((r_sstatus() & SSTATUS_SPP) != 0)
         panic("usertrap: not from user mode");

   compiles to [csrr a5,sstatus / andi a5,a5,256 / c.bnez a5 -> +0x84].  The
   trap came from USER mode, so [SpecUsertrap.usertrap_entry_ms]'s
   [trap_mstatus_ok] pins [SPP <> 1]; [RiscvExtras.mword1_zero_of_ne_one]
   turns that into [SPP = 0], [IntrDefs.sconf_at_sret] transports it to the
   mstatus the [csrr] actually READ (the ghost sret mirror the boundary
   parks agrees with [sconf]'s tie), and
   [ProofUsertrapParts.ut_spp_clear_neq] makes the masked word zero.  The
   [c.bnez] therefore provably FALLS THROUGH: [panic] is never applied, so
   neither [SpecPanic]'s contract nor printk's panic path is in this cone.
   The only printk usertrap reaches is the GENERAL one, on the
   unexpected-scause arm, and that is [ProofUsertrapArms]' threaded
   [SpecPrintk.printk_gen_contract] hypothesis -- discharged from the
   [PRINTK_GEN] functor argument at the seal below.

   TWO THINGS ABOUT THE DISPATCH, both from the notes:

   * IT IS THE ONLY BLOCK THAT CARRIES [ut_csrs_raw] RATHER THAN THE FOLDED
     BUNDLE.  [IntrDefs.trap_csrs] buries sepc / scause / stval under
     existentials, and the three [beq]s here BRANCH on the scause value, so
     the values must be PINNED.  The fold into [trap_csrs] happens once per
     outgoing route ([UsertrapRes.ut_csrs_raw_fold], via [ud_hold] below).
   * THAT FOLD IS WHY THE KERNELVEC ARGUMENT EXISTS.  [ut_csrs_raw_fold]
     needs [intr_handler_spec kernelvec], which is deliberately NOT in
     [usertrap_res] -- it is DERIVABLE, from [SpecKernelvec.
     kernelvec_handler_spec] applied to hw_config + minstret_inv (the two
     persistent conjuncts of the [sconf] inside [sie_cap_gpr], extracted by
     [ut_dup_hw] below, ProofMainSecondary's idiom) + kernel_text +
     [devintr_caps] (out of the bundle's hart-generic
     [UsertrapRes.devintr_caps_any]).  So KERNELVEC belongs to this file
     alone.

   EVERYTHING HERE RUNS AT [b = false] -- the trap cleared SIE and only the
   syscall arm's [csrsi] at +0x9e ever re-enables it -- so every [wp_next]
   collapses with [WpNext.wp_next_off_intro] at the entry hart and not one
   [(CID := ...)] annotation is needed. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions bitvector.tactics.
From iris.algebra Require Import dfrac.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExtras RiscvFetchExec.
Require Import MinstretInv.
Require Import PageGeom.
Require Import RegFile HartTp WpGpr WpNext CpuOwn.
Require Import WpMmodeLeafBase.
Require Import SmodeCore.
Require Import StackOwn CalleeSaved.
Require Import InstrBytes.
Require Import KernelText KernelRvcDecode.
Require Import WpGprCsrwCommon WpGprCsrwA.
Require Import WpSconfAlu WpSconfMem WpSconfCtl WpSconfCsr WpSconfBtype.
Require Import WpSmodeIntr.
Require Import IntrDefs.
Require Import WpLock.
Require Import ProcGeom.
Require Import UserPtTree.
Require Import TrampPt.
Require Import KallocInv.
Require Import BioInv DiskPtsto WpUart FsBlocks LogInv FsCrash.
Require Import IrefSlots InodeRegion.
Require Import FdSlots ProcInv.
Require Import FileInvDefs.
Require Import SchedCtx.
Require Import CodeUsertrap.
Require Import SpecMyproc.
Require Import SpecKilled SpecSetkilled SpecKexit SpecYield SpecPrepareReturn.
Require Import SpecDevintr SpecVmfault.
Require Import SpecPrintk.
Require Import SpecKernelvec.
Require Import SpecSyscall SpecSysExit.
Require Import SpecUsertrap UsertrapRes.
Require Import ProofUsertrapParts ProofPrepareReturnParts.
Require Import ProofUsertrapTail ProofUsertrapArms ProofUsertrapSys.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Import Defs.
Local Open Scope Z_scope.
Set Printing Depth 40.

Module UsertrapProof (SY : SYSCALL) (PK : PRINTK_GEN) (MP : MYPROC)
                     (KI : KILLED) (SK : SETKILLED) (DE : DEVINTR)
                     (VM : VMFAULT) (YI : YIELD) (PR : PREPARE_RETURN)
                     (KE : KEXIT) (KV : KERNELVEC) : USERTRAP.

(* the four proven blocks, at this file's callee instances *)
Module A := UtArms PR KI KE YI SK VM.
Module S := UtSys PR KI KE YI SY.

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


(* ===================================================================== *)
(*  +0x00 .. +0x2e -- THE ENTRY.                                          *)
(* ===================================================================== *)
Section UtEntry.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !bioG Σ,
            !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ, !fsCrashG Σ,
            !kallocG Σ, !irefslotG Σ, !iregG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.
  Context (Rsys : gname -> mword 64 -> iProp Σ).

  (* THE BOUNDARY'S RAW MACHINE STATE IN, THE KERNEL CONE'S STATE OUT.
     [UsertrapRes.ut_trap_open] is the resource half and is already proven --
     no instruction is involved in it -- so what is left here is thirteen
     instructions and the refutation.  The exit hands the dispatch the
     PINNED trap-CSR set ([ut_csrs_raw]) rather than [trap_csrs]: see the
     header. *)
  Lemma ut_entry (N : ut_names) (V : pprivate) (ksp : mword 64)
      (m : regfile) (av : nat) (C : iProp Σ)
      (ms_v sc_v stval_v sepc_v : mword 64)
      (mie_v mdv0 menvcfg0 : mword 64) :
    usertrap_entry_ms ms_v ->
    (K_usertrap <= av)%nat ->
    m !!! Regidx csp_rs1 = ksp ->
    m !!! Regidx Rtp = cid_word ->
    mie_v = MIE_S ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    menvcfg0 = MENVCFG_S ->
    kernel_text -∗
    pc_is (mword_of_int UT) -∗
    hw_config -∗
    minstret_inv -∗
    hart_state ↦ᵣ HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ Supervisor -∗
    mstatus ↦ᵣ ms_v -∗
    scause ↦ᵣ sc_v -∗
    stval ↦ᵣ stval_v -∗
    sepc ↦ᵣ sepc_v -∗
    stvec ↦ᵣ (mword_of_int TRAMPOLINE : mword 64) -∗
    mie ↦ᵣ mie_v -∗
    mideleg ↦ᵣ mdv0 -∗
    menvcfg ↦ᵣ menvcfg0 -∗
    gpr_file m -∗
    (* the trap enters from USERSPACE, which holds no kernel lock, so the
       held set here is the literal [∅] -- the same one the continuation
       below names. *)
    ut_trap (un_pj N) ksp av C ∅ -∗
    ut_env Rsys N V -∗
    (∀ (M : regfile) (V' : pprivate),
       ⌜M !!! Regidx csp_rs1 = pa_stk ksp 4⌝ -∗ ⌜M !!! Regidx Rs1 = un_pj N⌝ -∗
       ⌜M !!! Regidx Ra0 = un_pj N⌝ -∗ ⌜ut_cs m M⌝ -∗ ⌜pv_upt V' = pv_upt V⌝ -∗
       pc_is (mword_of_int (UT + 0x30)) -∗
       sie_cap_gpr M (av - 4)%nat false (un_pj N) -∗
       cpu_own 0%nat false (un_pj N) C false ∅ -∗ cpu_claim (un_pj N) -∗
       ut_csrs_raw sepc_v sc_v stval_v -∗ ut_env Rsys N V' -∗
       (* THE FRAME, which this block is what CREATES: the four slots the
          prologue's [c.sdsp]s filled.  Not in the note's printed exit
          premise, and it has to be -- [stack_own] arrives inside
          [ut_trap] and nothing outside can frame what the push carved. *)
       ut_frame ksp (m !!! Regidx Rra) (m !!! Regidx Rs0)
                    (m !!! Regidx Rs1) (m !!! Regidx Rs2) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hentry Hav Hsp Htp Hmiev Hmask Hmenvv.
    destruct Hentry as (Htms & Hmsf & Hspie).
    destruct Htms as (Hsxl & Hmprv & Hmxr & Hspp & Hsie & Htvm & Htsr).
    pose proof (ut_nx_bound false av (av - 4)%nat Hav (trap_res_off (av - 4)%nat))
      as Hks.
    unfold K_syscall, K_sys_exit, K_kexit in Hks.
    iIntros "#Htext Hpc #Hhw #Hminv Hhs Hpriv Hms Hsc Hst Hep Hstv
             Hmie Hmdl Hmenv Hgpr Htrap Henv Hcont".
    iDestruct (ut_trap_open (un_pj N) ksp av C m ms_v mie_v mdv0 menvcfg0 ∅
                 Hmsf Hsie Hspp Hspie Hsp Htp Hmiev Hmask Hmenvv
                 with "Hhw Hminv Hhs Hpriv Hms Hmie Hmdl Hmenv Hgpr Htrap")
      as "(Hcg & Hcpu & Hclm & Hq & Hkpt & Hsret)".
    iPoseProof (uti_000 with "Htext") as "Hi00".
    iPoseProof (uti_002 with "Htext") as "Hi02".
    iPoseProof (uti_004 with "Htext") as "Hi04".
    iPoseProof (uti_006 with "Htext") as "Hi06".
    iPoseProof (uti_008 with "Htext") as "Hi08".
    iPoseProof (uti_00a with "Htext") as "Hi0a".
    iPoseProof (uti_00c with "Htext") as "Hi0c".
    iPoseProof (uti_010 with "Htext") as "Hi10".
    iPoseProof (uti_014 with "Htext") as "Hi14".
    iPoseProof (uti_016 with "Htext") as "Hi16".
    iPoseProof (uti_01a with "Htext") as "Hi1a".
    iPoseProof (uti_01e with "Htext") as "Hi1e".
    iPoseProof (uti_022 with "Htext") as "Hi22".
    iPoseProof (uti_026 with "Htext") as "Hi26".
    iPoseProof (uti_028 with "Htext") as "Hi28".
    iPoseProof (uti_02a with "Htext") as "Hi2a".
    iPoseProof (uti_02e with "Htext") as "Hi2e".
    (* ---- +0x00: c.addi sp,sp,-32 -- the 4-slot frame ---- *)
    assert (Hpush : add_vec (m !!! Regidx csp_rs1)
                      (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6)))
                    = pa_stk (m !!! Regidx csp_rs1) 4)
      by apply stk_push_32.
    iApply (wp_caddi_sp_push_s_sconf (mword_of_int UT) (mword_of_int 32 : mword 6)
              m av 4 false ltac:(lia) Hpush with "Hcg Hpc Hi00 [-]").
    iApply wp_next_off_intro. iIntros "Hcg Hframe Hpc".
    set (M1 := <[Regidx csp_rs1 := regval_into_reg
                   (add_vec (m !!! Regidx csp_rs1)
                      (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))))]> m).
    change (<[Regidx csp_rs1 := regval_into_reg
               (add_vec (m !!! Regidx csp_rs1)
                  (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))))]> m)
      with M1.
    assert (HM1sp : M1 !!! Regidx csp_rs1 = pa_stk ksp 4)
      by (rewrite /M1 upd_eq Hpush Hsp; reflexivity).
    assert (Hp02 : add_vec_int (mword_of_int UT : mword 64) 2
                   = mword_of_int (UT + 0x2)) by pcw.
    iEval (rewrite Hp02) in "Hpc".
    iEval (rewrite Hsp) in "Hframe".
    iDestruct (stack_own_4_elim with "Hframe") as (w1 w2 w3 w4) "(Hb1 & Hb2 & Hb3 & Hb4)".
    (* the four slot addresses, from the PUSHED sp -- [stk_frm] at d = 4 *)
    assert (Hpa1 : add_vec (M1 !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000")))
                   = pa_stk ksp 1)
      by (rewrite HM1sp; apply stk_frm; apply bv_eq; vm_compute; reflexivity).
    assert (Hpa2 : add_vec (M1 !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000")))
                   = pa_stk ksp 2)
      by (rewrite HM1sp; apply stk_frm; apply bv_eq; vm_compute; reflexivity).
    assert (Hpa3 : add_vec (M1 !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000")))
                   = pa_stk ksp 3)
      by (rewrite HM1sp; apply stk_frm; apply bv_eq; vm_compute; reflexivity).
    assert (Hpa4 : add_vec (M1 !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000")))
                   = pa_stk ksp 4)
      by (rewrite HM1sp; apply stk_frm; apply bv_eq; vm_compute; reflexivity).
    (* the four stored values, in the map's own spelling *)
    assert (Hvra : rget M1 Rra = m !!! Regidx Rra).
    { rgne. rewrite /M1 upd_ne; [reflexivity | reg_neq]. }
    assert (Hvs0 : rget M1 Rs0 = m !!! Regidx Rs0).
    { rgne. rewrite /M1 upd_ne; [reflexivity | reg_neq]. }
    assert (Hvs1 : rget M1 Rs1 = m !!! Regidx Rs1).
    { rgne. rewrite /M1 upd_ne; [reflexivity | reg_neq]. }
    assert (Hvs2 : rget M1 Rs2 = m !!! Regidx Rs2).
    { rgne. rewrite /M1 upd_ne; [reflexivity | reg_neq]. }
    (* ---- +0x02: c.sdsp ra,24(sp) ---- *)
    iEval (rewrite -Hpa1) in "Hb1".
    iApply (wp_csdsp_s_sconf (mword_of_int (UT + 0x2)) (mword_of_int 3 : mword 6)
              Rra M1 (av - 4)%nat w1 false with "Hcg Hpc Hi02 Hb1 [-]").
    iApply wp_next_off_intro. iIntros "Hcg Hpc Hb1".
    iEval (rewrite Hpa1 Hvra) in "Hb1".
    assert (Hp04 : add_vec_int (mword_of_int (UT + 0x2) : mword 64) 2
                   = mword_of_int (UT + 0x4)) by pcw.
    iEval (rewrite Hp04) in "Hpc".
    (* ---- +0x04: c.sdsp s0,16(sp) ---- *)
    iEval (rewrite -Hpa2) in "Hb2".
    iApply (wp_csdsp_s_sconf (mword_of_int (UT + 0x4)) (mword_of_int 2 : mword 6)
              Rs0 M1 (av - 4)%nat w2 false with "Hcg Hpc Hi04 Hb2 [-]").
    iApply wp_next_off_intro. iIntros "Hcg Hpc Hb2".
    iEval (rewrite Hpa2 Hvs0) in "Hb2".
    assert (Hp06 : add_vec_int (mword_of_int (UT + 0x4) : mword 64) 2
                   = mword_of_int (UT + 0x6)) by pcw.
    iEval (rewrite Hp06) in "Hpc".
    (* ---- +0x06: c.sdsp s1,8(sp) ---- *)
    iEval (rewrite -Hpa3) in "Hb3".
    iApply (wp_csdsp_s_sconf (mword_of_int (UT + 0x6)) (mword_of_int 1 : mword 6)
              Rs1 M1 (av - 4)%nat w3 false with "Hcg Hpc Hi06 Hb3 [-]").
    iApply wp_next_off_intro. iIntros "Hcg Hpc Hb3".
    iEval (rewrite Hpa3 Hvs1) in "Hb3".
    assert (Hp08 : add_vec_int (mword_of_int (UT + 0x6) : mword 64) 2
                   = mword_of_int (UT + 0x8)) by pcw.
    iEval (rewrite Hp08) in "Hpc".
    (* ---- +0x08: c.sdsp s2,0(sp) ---- *)
    iEval (rewrite -Hpa4) in "Hb4".
    iApply (wp_csdsp_s_sconf (mword_of_int (UT + 0x8)) (mword_of_int 0 : mword 6)
              Rs2 M1 (av - 4)%nat w4 false with "Hcg Hpc Hi08 Hb4 [-]").
    iApply wp_next_off_intro. iIntros "Hcg Hpc Hb4".
    iEval (rewrite Hpa4 Hvs2) in "Hb4".
    assert (Hp0a : add_vec_int (mword_of_int (UT + 0x8) : mword 64) 2
                   = mword_of_int (UT + 0xa)) by pcw.
    iEval (rewrite Hp0a) in "Hpc".
    (* ---- +0x0a: c.addi4spn s0,sp,32 -- the frame pointer, back at ksp ---- *)
    iApply (wp_caddi4spn_s_sconf (mword_of_int (UT + 0xa)) (Cregidx (mword_of_int 0))
              (mword_of_int 8 : mword 8) Rs0 M1 (av - 4)%nat false
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
              ltac:(rdok) with "Hcg Hpc Hi0a [-]").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    set (M2 := <[Regidx Rs0 := regval_into_reg
                   (add_vec (M1 !!! Regidx csp_rs1)
                      (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8))))]> M1).
    change (<[Regidx Rs0 := regval_into_reg
               (add_vec (M1 !!! Regidx csp_rs1)
                  (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8))))]> M1)
      with M2.
    assert (HM2sp : M2 !!! Regidx csp_rs1 = pa_stk ksp 4)
      by (rewrite /M2 upd_ne; [exact HM1sp | reg_neq]).
    assert (Hp0c : add_vec_int (mword_of_int (UT + 0xa) : mword 64) 2
                   = mword_of_int (UT + 0xc)) by pcw.
    iEval (rewrite Hp0c) in "Hpc".
    (* =============================================================== *)
    (*  +0x0c .. +0x14: THE SPP TEST.  The [c.bnez] is REFUTED.          *)
    (* =============================================================== *)
    iApply (wp_csrr_sstatus_s_sconf (mword_of_int (UT + 0xc)) Ra5
              M2 (av - 4)%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi0c [-]").
    iApply wp_next_off_intro.
    iIntros (ms1) "%Hms1f Hhs Hscf Htr Hpc Hfile (Hstk & %Hsie1 & Harm)".
    (* the mstatus the read SAW has the boundary's SPP, off the travelling
       sret mirror's agreement with [sconf]'s stationary tie *)
    iDestruct (sconf_at_sret ms1 ('b"0") ('b"1") with "Hscf Hsret") as %[Hspp1 Hspie1].
    iDestruct (sconf_at_close with "Hscf") as "Hscf".
    iDestruct (sie_cap_gpr_join with "Hhs Hscf [Hstk Htr Harm] Hfile") as "Hcg".
    { rewrite /sie_cap. iSplitL "Hstk"; [iExact "Hstk" |].
      iSplitL "Htr"; [iExact "Htr" | iExact "Harm"]. }
    set (M3 := <[Regidx Ra5 := regval_into_reg (sstatus_read ms1)]> M2).
    change (<[Regidx Ra5 := regval_into_reg (sstatus_read ms1)]> M2) with M3.
    assert (HM3sp : M3 !!! Regidx csp_rs1 = pa_stk ksp 4)
      by (rewrite /M3 upd_ne; [exact HM2sp | reg_neq]).
    assert (HM3a5 : rget M3 Ra5 = sstatus_read ms1)
      by (rgne; rewrite /M3; apply upd_eq).
    assert (Hp10 : add_vec_int (mword_of_int (UT + 0xc) : mword 64) 4
                   = mword_of_int (UT + 0x10)) by pcw.
    iEval (rewrite Hp10) in "Hpc".
    (* ---- +0x10: andi a5,a5,256 ---- *)
    iApply (wp_andi_s_sconf (mword_of_int (UT + 0x10)) Ra5 Ra5
              (mword_of_int 256 : mword 12)
              (and_vec (sstatus_read ms1)
                 (sign_extend' 64 (mword_of_int 256 : mword 12)))
              M3 (av - 4)%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(rewrite HM3a5; reflexivity) with "Hcg Hpc Hi10 [-]").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    set (M4 := <[Regidx Ra5 := regval_into_reg
                   (and_vec (sstatus_read ms1)
                      (sign_extend' 64 (mword_of_int 256 : mword 12)))]> M3).
    change (<[Regidx Ra5 := regval_into_reg
               (and_vec (sstatus_read ms1)
                  (sign_extend' 64 (mword_of_int 256 : mword 12)))]> M3) with M4.
    assert (HM4sp : M4 !!! Regidx csp_rs1 = pa_stk ksp 4)
      by (rewrite /M4 upd_ne; [exact HM3sp | reg_neq]).
    assert (HM4a5 : rget M4 Ra5 = and_vec (sstatus_read ms1)
                      (sign_extend' 64 (mword_of_int 256 : mword 12)))
      by (rgne; rewrite /M4; apply upd_eq).
    assert (Hp14 : add_vec_int (mword_of_int (UT + 0x10) : mword 64) 4
                   = mword_of_int (UT + 0x14)) by pcw.
    iEval (rewrite Hp14) in "Hpc".
    (* ---- +0x14: c.bnez a5 -> +0x84 (panic).  DEAD -- see the header ---- *)
    iApply (wp_cbnez_fall_s_sconf (mword_of_int (UT + 0x14))
              (mword_of_int 56 : mword 8) (Cregidx (mword_of_int 7)) Ra5
              M4 (av - 4)%nat false
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
              ltac:(rewrite HM4a5; exact (ut_spp_clear_neq ms1 Hspp1))
              with "Hcg Hpc Hi14 [-]").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    assert (Hp16 : add_vec_int (mword_of_int (UT + 0x14) : mword 64) 2
                   = mword_of_int (UT + 0x16)) by pcw.
    iEval (rewrite Hp16) in "Hpc".
    (* =============================================================== *)
    (*  +0x16 .. +0x1e: w_stvec(kernelvec) -- the RAW cell is written.    *)
    (* =============================================================== *)
    iApply (wp_auipc_s_sconf (mword_of_int (UT + 0x16)) Ra5
              (mword_of_int 3 : mword 20) M4 (av - 4)%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi16 [-]").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    set (M5 := <[Regidx Ra5 := regval_into_reg
                   (add_vec (mword_of_int (UT + 0x16) : mword 64)
                      (auipc_off (mword_of_int 3 : mword 20)))]> M4).
    change (<[Regidx Ra5 := regval_into_reg
               (add_vec (mword_of_int (UT + 0x16) : mword 64)
                  (auipc_off (mword_of_int 3 : mword 20)))]> M4) with M5.
    assert (HM5sp : M5 !!! Regidx csp_rs1 = pa_stk ksp 4)
      by (rewrite /M5 upd_ne; [exact HM4sp | reg_neq]).
    assert (HM5a5 : rget M5 Ra5 = add_vec (mword_of_int (UT + 0x16) : mword 64)
                      (auipc_off (mword_of_int 3 : mword 20)))
      by (rgne; rewrite /M5; apply upd_eq).
    assert (Hp1a : add_vec_int (mword_of_int (UT + 0x16) : mword 64) 4
                   = mword_of_int (UT + 0x1a)) by pcw.
    iEval (rewrite Hp1a) in "Hpc".
    (* ---- +0x1a: addi a5,a5,3722 -- the pair sums to kernelvec ---- *)
    iApply (wp_addi4_s_sconf (mword_of_int (UT + 0x1a)) Ra5 Ra5
              (mword_of_int 3956 : mword 12) M5 (av - 4)%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi1a [-]").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    set (M6 := <[Regidx Ra5 := regval_into_reg
                   (add_vec (rget M5 Ra5)
                      (sign_extend' 64 (mword_of_int 3956 : mword 12)))]> M5).
    change (<[Regidx Ra5 := regval_into_reg
               (add_vec (rget M5 Ra5)
                  (sign_extend' 64 (mword_of_int 3956 : mword 12)))]> M5) with M6.
    assert (HM6sp : M6 !!! Regidx csp_rs1 = pa_stk ksp 4)
      by (rewrite /M6 upd_ne; [exact HM5sp | reg_neq]).
    assert (HM6a5 : rget M6 Ra5
                    = (mword_of_int KernelSyms.kernelvec : mword 64)).
    { rgne. rewrite /M6 upd_eq. rewrite HM5a5. pcw. }
    assert (Hp1e : add_vec_int (mword_of_int (UT + 0x1a) : mword 64) 4
                   = mword_of_int (UT + 0x1e)) by pcw.
    iEval (rewrite Hp1e) in "Hpc".
    (* ---- +0x1e: csrw stvec,a5 ---- *)
    iApply (wp_csrw_stvec_s_sconf (mword_of_int (UT + 0x1e)) Ra5 M6 (av - 4)%nat
              (mword_of_int TRAMPOLINE : mword 64)
              (mword_of_int KernelSyms.kernelvec : mword 64)
              ltac:(vm_compute; discriminate) HM6a5
              ltac:(rewrite kernelvec_tv_direct; discriminate)
              with "Hcg Hstv Hpc Hi1e [-]").
    iApply wp_next_off_intro. iIntros "Hcg Hstv Hpc".
    assert (Hp22 : add_vec_int (mword_of_int (UT + 0x1e) : mword 64) 4
                   = mword_of_int (UT + 0x22)) by pcw.
    iEval (rewrite Hp22) in "Hpc".
    (* =============================================================== *)
    (*  +0x22 .. +0x26: p = myproc(); s1 = p.                            *)
    (* =============================================================== *)
    iApply (wp_jal_s_sconf (mword_of_int (UT + 0x22)) Rra
              (mword_of_int 2093858 : mword 21) M6 (av - 4)%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi22 [-]").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    set (M7 := <[Regidx Rra := regval_into_reg
                   (add_vec_int (mword_of_int (UT + 0x22) : mword 64) 4)]> M6).
    change (<[Regidx Rra := regval_into_reg
               (add_vec_int (mword_of_int (UT + 0x22) : mword 64) 4)]> M6) with M7.
    assert (Hmyp : add_vec (mword_of_int (UT + 0x22) : mword 64)
                     (sign_extend' 64 (mword_of_int 2093858 : mword 21))
                   = mword_of_int KernelSyms.myproc) by pcw.
    iEval (rewrite Hmyp) in "Hpc".
    assert (HM7sp : M7 !!! Regidx csp_rs1 = pa_stk ksp 4)
      by (rewrite /M7 upd_ne; [exact HM6sp | reg_neq]).
    assert (HM7ra : M7 !!! Regidx Rra = mword_of_int (UT + 0x26))
      by (rewrite /M7 upd_eq; pcw).
    iApply (MP.wp_myproc_sconf M7 (av - 4)%nat 0%nat false (un_pj N) C false _
              ltac:(change (2 ^ 31)%Z with 2147483648%Z; lia) ltac:(lia)
              with "Hcg Hcpu Htext Hpc [-]").
    iApply wp_next_off_intro.
    iIntros (ms2 mf) "%Hms2f Hcg Hcpu Hpc [%Hcsmf %Hmfa0]".
    assert (Hret26 : ret_pc (M7 !!! Regidx Rra) = mword_of_int (UT + 0x26))
      by (rewrite HM7ra; pcw).
    iEval (rewrite Hret26) in "Hpc".
    assert (Hmfsp : mf !!! Regidx csp_rs1 = pa_stk ksp 4)
      by (rewrite (callee_saved_lookup Hcsmf csp_rs1
                     ltac:(vm_compute; reflexivity)); exact HM7sp).
    (* ---- +0x26: c.mv s1,a0 ---- *)
    iApply (wp_cmv_s_sconf (mword_of_int (UT + 0x26)) Rs1 Ra0 mf (av - 4)%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi26 [-]").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    set (S1 := <[Regidx Rs1 := regval_into_reg (add_vec zero_reg (rget mf Ra0))]> mf).
    change (<[Regidx Rs1 := regval_into_reg (add_vec zero_reg (rget mf Ra0))]> mf)
      with S1.
    assert (HS1sp : S1 !!! Regidx csp_rs1 = pa_stk ksp 4)
      by (rewrite /S1 upd_ne; [exact Hmfsp | reg_neq]).
    assert (HS1s1 : S1 !!! Regidx Rs1 = un_pj N).
    { rewrite /S1 upd_eq. rewrite (rget_ne (CID := CID) mf Ra0 ltac:(reg_neq)).
      rewrite Hmfa0 add_vec_zero_l. reflexivity. }
    assert (HS1a0 : S1 !!! Regidx Ra0 = un_pj N)
      by (rewrite /S1 upd_ne; [exact Hmfa0 | reg_neq]).
    assert (Hp28 : add_vec_int (mword_of_int (UT + 0x26) : mword 64) 2
                   = mword_of_int (UT + 0x28)) by pcw.
    iEval (rewrite Hp28) in "Hpc".
    (* =============================================================== *)
    (*  +0x28 .. +0x2e: p->trapframe->epc = r_sepc().                    *)
    (* =============================================================== *)
    iDestruct "Henv" as "[#Hcaps Hown]".
    iDestruct (ut_own_priv with "Hown") as "(Hpv & Hsy & Hownback)".
    iDestruct (ut_epc_exists with "Hpv") as %Hepcx.
    destruct Hepcx as [uepc Hepc].
    iDestruct (proc_priv_tf_upd with "Hpv") as "(Htfc & Htfp & Hpvback)".
    iDestruct (tf_page_word_upd _ _ tf_epc_idx uepc Hepc with "Htfp")
      as "(Hword & Htfback)".
    assert (Haddrtf : add_vec (rget S1 Ra0)
                        (sign_extend' 64 (mword_of_int 88 : mword 12))
                      = p_trapframe (un_pj N))
      by (rgne; rewrite HS1a0; apply prr_p_trapframe).
    iEval (rewrite -Haddrtf) in "Htfc".
    iApply (wp_cld_s_sconf (mword_of_int (UT + 0x28)) Ra5 Ra0
              (mword_of_int 88 : mword 12) S1 (av - 4)%nat
              (page_base (ud_tfp (pv_upt V))) false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi28 Htfc [-]").
    iApply wp_next_off_intro. iIntros "Hcg Hpc Htfc".
    iEval (rewrite Haddrtf) in "Htfc".
    set (S2 := <[Regidx Ra5 := regval_into_reg
                   (page_base (ud_tfp (pv_upt V)))]> S1).
    change (<[Regidx Ra5 := regval_into_reg
               (page_base (ud_tfp (pv_upt V)))]> S1) with S2.
    assert (HS2sp : S2 !!! Regidx csp_rs1 = pa_stk ksp 4)
      by (rewrite /S2 upd_ne; [exact HS1sp | reg_neq]).
    assert (HS2s1 : S2 !!! Regidx Rs1 = un_pj N)
      by (rewrite /S2 upd_ne; [exact HS1s1 | reg_neq]).
    assert (HS2a0 : S2 !!! Regidx Ra0 = un_pj N)
      by (rewrite /S2 upd_ne; [exact HS1a0 | reg_neq]).
    assert (Hp2a : add_vec_int (mword_of_int (UT + 0x28) : mword 64) 2
                   = mword_of_int (UT + 0x2a)) by pcw.
    iEval (rewrite Hp2a) in "Hpc".
    (* ---- +0x2a: csrr a4,sepc ---- *)
    iApply (wp_csrr_sepc_s_sconf (mword_of_int (UT + 0x2a)) Ra4 S2 (av - 4)%nat
              (DfracOwn 1) sepc_v
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hep Hpc Hi2a [-]").
    iApply wp_next_off_intro. iIntros "Hcg Hep Hpc".
    set (S3 := <[Regidx Ra4 := regval_into_reg (mepc_val sepc_v)]> S2).
    change (<[Regidx Ra4 := regval_into_reg (mepc_val sepc_v)]> S2) with S3.
    assert (HS3sp : S3 !!! Regidx csp_rs1 = pa_stk ksp 4)
      by (rewrite /S3 upd_ne; [exact HS2sp | reg_neq]).
    assert (HS3s1 : S3 !!! Regidx Rs1 = un_pj N)
      by (rewrite /S3 upd_ne; [exact HS2s1 | reg_neq]).
    assert (HS3a0 : S3 !!! Regidx Ra0 = un_pj N)
      by (rewrite /S3 upd_ne; [exact HS2a0 | reg_neq]).
    assert (HS3a5 : rget S3 Ra5 = page_base (ud_tfp (pv_upt V))).
    { rgne. rewrite /S3 upd_ne; [| reg_neq]. rewrite /S2. apply upd_eq. }
    assert (Haddrw : add_vec (rget S3 Ra5)
                       (sign_extend' 64 (mword_of_int 24 : mword 12))
                     = a_tf_word (ud_tfp (pv_upt V)) tf_epc_idx)
      by (rewrite HS3a5; apply prr_tf_addr_24).
    assert (Hp2e : add_vec_int (mword_of_int (UT + 0x2a) : mword 64) 4
                   = mword_of_int (UT + 0x2e)) by pcw.
    iEval (rewrite Hp2e) in "Hpc".
    (* ---- +0x2e: c.sd a4,24(a5) ---- *)
    iEval (rewrite -Haddrw) in "Hword".
    iApply (wp_csd_s_sconf (mword_of_int (UT + 0x2e)) Ra4 Ra5
              (mword_of_int 24 : mword 12) S3 (av - 4)%nat uepc false
              with "Hcg Hpc Hi2e Hword [-]").
    iApply wp_next_off_intro. iIntros "Hcg Hpc Hword".
    iEval (rewrite Haddrw) in "Hword".
    assert (Hp30 : add_vec_int (mword_of_int (UT + 0x2e) : mword 64) 2
                   = mword_of_int (UT + 0x30)) by pcw.
    iEval (rewrite Hp30) in "Hpc".
    (* the page and the process block, rebuilt at the written epc *)
    iDestruct ("Htfback" $! (rget S3 Ra4) with "Hword") as "Htfp".
    iDestruct ("Hpvback" $! (<[tf_epc_idx := rget S3 Ra4]> (pv_tf V))
                 with "Htfc Htfp") as "Hpv".
    set (V' := upd_tf V (<[tf_epc_idx := rget S3 Ra4]> (pv_tf V))).
    change (upd_tf V (<[tf_epc_idx := rget S3 Ra4]> (pv_tf V))) with V'.
    assert (HuptV' : pv_upt V' = pv_upt V)
      by (rewrite /V'; destruct V; reflexivity).
    iDestruct ("Hownback" $! V' with "Hpv Hsy") as "Hown".
    (* the callee-saved relation, threaded through eleven writes *)
    assert (Hcs1 : ut_cs m M1)
      by (rewrite /M1; apply ut_cs_insert4;
          [left; reflexivity | apply ut_cs_refl]).
    assert (Hcs2 : ut_cs m M2)
      by (rewrite /M2; apply ut_cs_insert4;
          [right; left; reflexivity | exact Hcs1]).
    assert (Hcs3 : ut_cs m M3)
      by (rewrite /M3; apply ut_cs_insert;
          [vm_compute; reflexivity | exact Hcs2]).
    assert (Hcs4 : ut_cs m M4)
      by (rewrite /M4; apply ut_cs_insert;
          [vm_compute; reflexivity | exact Hcs3]).
    assert (Hcs5 : ut_cs m M5)
      by (rewrite /M5; apply ut_cs_insert;
          [vm_compute; reflexivity | exact Hcs4]).
    assert (Hcs6 : ut_cs m M6)
      by (rewrite /M6; apply ut_cs_insert;
          [vm_compute; reflexivity | exact Hcs5]).
    assert (Hcs7 : ut_cs m M7)
      by (rewrite /M7; apply ut_cs_insert;
          [vm_compute; reflexivity | exact Hcs6]).
    assert (Hcsf : ut_cs m mf)
      by exact (ut_cs_trans m M7 mf Hcs7 (ut_cs_of_callee_saved _ _ Hcsmf)).
    assert (Hcss1 : ut_cs m S1)
      by (rewrite /S1; apply ut_cs_insert4;
          [right; right; left; reflexivity | exact Hcsf]).
    assert (Hcss2 : ut_cs m S2)
      by (rewrite /S2; apply ut_cs_insert;
          [vm_compute; reflexivity | exact Hcss1]).
    assert (Hcss3 : ut_cs m S3)
      by (rewrite /S3; apply ut_cs_insert;
          [vm_compute; reflexivity | exact Hcss2]).
    (* the three outgoing bundles, named rather than [iFrame]d *)
    iAssert (ut_csrs_raw sepc_v sc_v stval_v)
      with "[Hep Hsc Hst Hstv Hq Hsret Hkpt]" as "Hraw".
    { rewrite /ut_csrs_raw.
      iSplitL "Hep"; [iExact "Hep" |].
      iSplitL "Hsc"; [iExact "Hsc" |].
      iSplitL "Hst"; [iExact "Hst" |].
      iSplitL "Hstv"; [iExact "Hstv" |].
      iSplitL "Hq"; [iExact "Hq" |].
      iSplitL "Hsret"; [iExact "Hsret" | iExact "Hkpt"]. }
    iAssert (ut_env Rsys N V') with "[Hown]" as "Henv".
    { rewrite /ut_env. iSplitR; [iExact "Hcaps" | iExact "Hown"]. }
    iAssert (ut_frame ksp (m !!! Regidx Rra) (m !!! Regidx Rs0)
                          (m !!! Regidx Rs1) (m !!! Regidx Rs2))
      with "[Hb1 Hb2 Hb3 Hb4]" as "Hfr".
    { rewrite /ut_frame.
      iSplitL "Hb1"; [iExact "Hb1" |].
      iSplitL "Hb2"; [iExact "Hb2" |].
      iSplitL "Hb3"; [iExact "Hb3" | iExact "Hb4"]. }
    iApply ("Hcont" $! S3 V' with "[%] [%] [%] [%] [%] Hpc Hcg Hcpu Hclm
              Hraw Henv Hfr").
    - exact HS3sp.
    - exact HS3s1.
    - exact HS3a0.
    - exact Hcss3.
    - exact HuptV'.
  Qed.

End UtEntry.


(* ===================================================================== *)
(*  +0x30 .. +0x54 -- THE scause DISPATCH.                                *)
(* ===================================================================== *)
Section UtDispatch.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !bioG Σ,
            !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ, !fsCrashG Σ,
            !kallocG Σ, !irefslotG Σ, !iregG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  (* [hw_config] + [minstret_inv], both persistent, out of the ambient
     bundle -- ProofMainSecondary's [ms_dup_hw], which is [Local] there.
     They are what [SpecKernelvec.kernelvec_handler_spec] consumes. *)
  Local Lemma ut_dup_hw (m : regfile) (avail : nat) (b : bool) (p : mword 64) :
    sie_cap_gpr m avail b p -∗
    hw_config ∗ minstret_inv ∗ sie_cap_gpr m avail b p.
  Proof.
    iIntros "Hcg".
    iDestruct (sie_cap_gpr_split with "Hcg") as "(Hhs & Hsc & Hsie & Hgpr)".
    iEval (rewrite /sconf) in "Hsc".
    iDestruct "Hsc" as "(#Hhw & #Hmin & Hrest)".
    iSplitR; [iExact "Hhw" |]. iSplitR; [iExact "Hmin" |].
    iApply (sie_cap_gpr_join with "Hhs [Hrest] Hsie Hgpr").
    rewrite /sconf. iSplitR; [iExact "Hhw" |].
    iSplitR; [iExact "Hmin" | iExact "Hrest"].
  Qed.

  (* THE FOLD, once, for the four outgoing routes.  This is the only place in
     the whole walk where [intr_handler_spec kernelvec] is needed. *)
  Local Lemma ud_hold (N : ut_names) (V : pprivate) (C : iProp Σ)
      (ep sc st : mword 64) :
    intr_handler_spec (mword_of_int KernelSyms.kernelvec : mword 64) -∗
    cpu_own 0%nat false (un_pj N) C false ∅ -∗
    cpu_claim (un_pj N) -∗
    sepc ↦ᵣ ep -∗ scause ↦ᵣ sc -∗ stval ↦ᵣ st -∗
    stvec ↦ᵣ (mword_of_int KernelSyms.kernelvec : mword 64) -∗
    ghost_var sie_gname (1/4) ('b"0" : mword 1) -∗
    sret_bits ('b"0" : mword 1) ('b"1" : mword 1) -∗
    strans_bit strans_bit_kpt -∗
    ut_env SY.syscall_env N V -∗
    ut_hold SY.syscall_env N V C false ∅.
  Proof.
    iIntros "#Hih Hcpu Hclm Hep Hsc Hst Hstv Hq Hsret Hkpt Henv".
    iAssert (ut_csrs_raw ep sc st)
      with "[Hep Hsc Hst Hstv Hq Hsret Hkpt]" as "Hraw".
    { rewrite /ut_csrs_raw.
      iSplitL "Hep"; [iExact "Hep" |].
      iSplitL "Hsc"; [iExact "Hsc" |].
      iSplitL "Hst"; [iExact "Hst" |].
      iSplitL "Hstv"; [iExact "Hstv" |].
      iSplitL "Hq"; [iExact "Hq" |].
      iSplitL "Hsret"; [iExact "Hsret" | iExact "Hkpt"]. }
    rewrite /ut_hold.
    iSplitL "Hcpu"; [iExact "Hcpu" |].
    iSplitL "Hraw".
    { rewrite /trap_csrs_ext. iApply (ut_csrs_raw_fold with "Hraw Hih"). }
    iSplitL "Hclm"; [rewrite /cpu_claim_ext; iExact "Hclm" | iExact "Henv"].
  Qed.

  Lemma ut_dispatch (N : ut_names) (V : pprivate) (pt : uptd) (ksp : mword 64)
      (m0 m : regfile) (av nx : nat) (C : iProp Σ)
      (ep sc st : mword 64)
      (mie_v menvcfg0 : mword 64) :
    printk_gen_contract (un_pr N) (un_u N) (un_v N) ->
    ut_wf N ->
    (K_usertrap <= av)%nat ->
    (trap_res false + nx)%nat = (av - 4)%nat ->
    ud_tfp (pv_upt V) = ud_tfp pt ->
    add_vec (un_ks N) (mword_of_int 4096) = ksp ->
    m0 !!! Regidx csp_rs1 = ksp ->
    m !!! Regidx csp_rs1 = pa_stk ksp 4 ->
    m !!! Regidx Rs1 = un_pj N ->
    m !!! Regidx Ra0 = un_pj N ->
    ut_cs m0 m ->
    mie_v = MIE_S ->
    menvcfg0 = MENVCFG_S ->
    kernel_text -∗
    pc_is (mword_of_int (UT + 0x30)) -∗
    sie_cap_gpr m nx false (un_pj N) -∗
    cpu_own 0%nat false (un_pj N) C false ∅ -∗
    cpu_claim (un_pj N) -∗
    ut_csrs_raw ep sc st -∗
    ut_env SY.syscall_env N V -∗
    ut_frame ksp (m0 !!! Regidx Rra) (m0 !!! Regidx Rs0)
                 (m0 !!! Regidx Rs1) (m0 !!! Regidx Rs2) -∗
    wp_next true (un_pj N)
      (fun CID' => usertrap_post (CID := CID') (ut_res (CID := CID') SY.syscall_env) pt ksp m0
                     mie_v menvcfg0) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hpk Hwf Hav Hnx Htfpe Hksp Hm0sp Hmsp Hms1 Hma0 Hcs Hmiev Hmenvv.
    pose proof (ut_nx_bound false av nx Hav Hnx) as Hks.
    unfold K_syscall, K_sys_exit, K_kexit in Hks.
    pose proof Hwf as Hwf'. destruct Hwf as (Hj & Hjl & Hlen & Hlg).
    iIntros "#Htext Hpc Hcg Hcpu Hclm Hraw Henv Hframe Hcont".
    iDestruct "Henv" as "[#Hcaps Hown]".
    (* the device complement, at THIS hart, out of the bundle's [∀ h] form *)
    iAssert (devintr_caps_any (un_u N) (un_v N) (un_k N) (un_tk N) (un_s N)
               (un_pd N) (un_pav N) (un_pu N)) with "[]" as "#Hdca".
    { iDestruct "Hcaps" as "(_ & _ & _ & _ & $ & _)". }
    iAssert (devintr_caps (un_u N) (un_v N) (un_k N) (un_tk N) (un_s N)
               (un_pd N) (un_pav N) (un_pu N)) with "[]" as "#Hdc".
    { iApply (devintr_caps_any_at CID with "Hdca"). }
    (* THE KERNELVEC FUNCTOR ARGUMENT, cashed here and nowhere else *)
    iDestruct (ut_dup_hw with "Hcg") as "(#Hhw & #Hmin & Hcg)".
    iPoseProof (KV.kernelvec_handler_spec (un_u N) (un_v N) (un_k N) (un_tk N)
                  (un_s N) (un_pd N) (un_pav N) (un_pu N) Hlen
                  with "Hhw Hmin Htext Hdc") as "#Hih".
    iDestruct "Hraw" as "(Hep & Hsc & Hst & Hstv & Hq & Hsret & Hkpt)".
    iPoseProof (uti_030 with "Htext") as "Hi30".
    iPoseProof (uti_034 with "Htext") as "Hi34".
    iPoseProof (uti_036 with "Htext") as "Hi36".
    (* ---- +0x30: csrr a4,scause ---- *)
    iApply (wp_csrr_scause_s_sconf (mword_of_int (UT + 0x30)) Ra4 m nx
              (DfracOwn 1) sc ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hsc Hpc Hi30 [-]").
    iApply wp_next_off_intro. iIntros "Hcg Hsc Hpc".
    set (D1 := <[Regidx Ra4 := regval_into_reg sc]> m).
    change (<[Regidx Ra4 := regval_into_reg sc]> m) with D1.
    assert (HD1sp : D1 !!! Regidx csp_rs1 = pa_stk ksp 4)
      by (rewrite /D1 upd_ne; [exact Hmsp | reg_neq]).
    assert (HD1s1 : D1 !!! Regidx Rs1 = un_pj N)
      by (rewrite /D1 upd_ne; [exact Hms1 | reg_neq]).
    assert (HD1a0 : D1 !!! Regidx Ra0 = un_pj N)
      by (rewrite /D1 upd_ne; [exact Hma0 | reg_neq]).
    assert (HcsD1 : ut_cs m0 D1)
      by (rewrite /D1; apply ut_cs_insert; [vm_compute; reflexivity | exact Hcs]).
    assert (HD1a4 : rget D1 Ra4 = sc) by (rgne; rewrite /D1; apply upd_eq).
    assert (Hp34 : add_vec_int (mword_of_int (UT + 0x30) : mword 64) 4
                   = mword_of_int (UT + 0x34)) by pcw.
    iEval (rewrite Hp34) in "Hpc".
    (* ---- +0x34: c.li a5,8 ---- *)
    iApply (wp_cli_s_sconf (mword_of_int (UT + 0x34)) Ra5 (mword_of_int 8 : mword 6)
              (add_vec zero_reg (sign_extend' 64
                 (sign_extend' 12 (mword_of_int 8 : mword 6))))
              D1 nx false ltac:(vm_compute; discriminate) ltac:(rdok) eq_refl
              with "Hcg Hpc Hi34 [-]").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    set (D2 := <[Regidx Ra5 := regval_into_reg
                   (add_vec zero_reg (sign_extend' 64
                      (sign_extend' 12 (mword_of_int 8 : mword 6))))]> D1).
    change (<[Regidx Ra5 := regval_into_reg
               (add_vec zero_reg (sign_extend' 64
                  (sign_extend' 12 (mword_of_int 8 : mword 6))))]> D1) with D2.
    assert (HD2sp : D2 !!! Regidx csp_rs1 = pa_stk ksp 4)
      by (rewrite /D2 upd_ne; [exact HD1sp | reg_neq]).
    assert (HD2s1 : D2 !!! Regidx Rs1 = un_pj N)
      by (rewrite /D2 upd_ne; [exact HD1s1 | reg_neq]).
    assert (HD2a0 : D2 !!! Regidx Ra0 = un_pj N)
      by (rewrite /D2 upd_ne; [exact HD1a0 | reg_neq]).
    assert (HcsD2 : ut_cs m0 D2)
      by (rewrite /D2; apply ut_cs_insert; [vm_compute; reflexivity | exact HcsD1]).
    assert (HD2a4 : rget D2 Ra4 = sc).
    { rgne. rewrite /D2 upd_ne; [| reg_neq]. rewrite /D1. apply upd_eq. }
    assert (Hp36 : add_vec_int (mword_of_int (UT + 0x34) : mword 64) 2
                   = mword_of_int (UT + 0x36)) by pcw.
    iEval (rewrite Hp36) in "Hpc".
    (* ---- +0x36: beq a4,a5 -> +0x90 (the syscall arm) ---- *)
    destruct (eq_vec (rget D2 Ra4) (rget D2 Ra5)) eqn:Hsys.
    - (* scause == 8: the SYSCALL arm *)
      iApply (wp_beq_taken_s_sconf (mword_of_int (UT + 0x36))
                (mword_of_int 90 : mword 13) Ra5 Ra4 D2 nx false
                ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                Hsys ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi36 [-]").
      iNext. iApply wp_next_off_intro. iIntros "Hcg Hpc".
      assert (Hj90 : add_vec (mword_of_int (UT + 0x36) : mword 64)
                       (sign_extend' 64 (mword_of_int 90 : mword 13))
                     = mword_of_int (UT + 0x90)) by pcw.
      iEval (rewrite Hj90) in "Hpc".
      iAssert (ut_hold SY.syscall_env N V C false ∅)
        with "[Hcpu Hclm Hep Hsc Hst Hstv Hq Hsret Hkpt Hown]" as "Hhold".
      { iApply (ud_hold N V C ep sc st with
                  "Hih Hcpu Hclm Hep Hsc Hst Hstv Hq Hsret Hkpt [Hown]").
        rewrite /ut_env. iSplitR; [iExact "Hcaps" | iExact "Hown"]. }
      iApply (S.ut_90 N V pt ksp m0 D2 av nx C
                mie_v menvcfg0 ∅
                Hwf' Hav Hnx Htfpe Hksp Hm0sp HD2sp HD2s1 HD2a0 HcsD2
                Hmiev Hmenvv
                with "Htext Hpc Hcg Hhold Hframe Hcont").
    - (* not a syscall: the device demultiplexer *)
      iPoseProof (uti_03a with "Htext") as "Hi3a".
      iPoseProof (uti_03e with "Htext") as "Hi3e".
      iPoseProof (uti_040 with "Htext") as "Hi40".
      iApply (wp_beq_fall_s_sconf (mword_of_int (UT + 0x36))
                (mword_of_int 90 : mword 13) Ra5 Ra4 D2 nx false
                ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                Hsys with "Hcg Hpc Hi36 [-]").
      iApply wp_next_off_intro. iIntros "Hcg Hpc".
      assert (Hp3a : add_vec_int (mword_of_int (UT + 0x36) : mword 64) 4
                     = mword_of_int (UT + 0x3a)) by pcw.
      iEval (rewrite Hp3a) in "Hpc".
      (* ---- +0x3a: jal devintr ---- *)
      iApply (wp_jal_s_sconf (mword_of_int (UT + 0x3a)) Rra
                (mword_of_int 2096976 : mword 21) D2 nx false
                ltac:(vm_compute; discriminate) ltac:(rdok)
                ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi3a [-]").
      iApply wp_next_off_intro. iIntros "Hcg Hpc".
      set (D3 := <[Regidx Rra := regval_into_reg
                     (add_vec_int (mword_of_int (UT + 0x3a) : mword 64) 4)]> D2).
      change (<[Regidx Rra := regval_into_reg
                 (add_vec_int (mword_of_int (UT + 0x3a) : mword 64) 4)]> D2) with D3.
      assert (Hjdi : add_vec (mword_of_int (UT + 0x3a) : mword 64)
                       (sign_extend' 64 (mword_of_int 2096976 : mword 21))
                     = mword_of_int KernelSyms.devintr) by pcw.
      iEval (rewrite Hjdi) in "Hpc".
      assert (HD3sp : D3 !!! Regidx csp_rs1 = pa_stk ksp 4)
        by (rewrite /D3 upd_ne; [exact HD2sp | reg_neq]).
      assert (HD3s1 : D3 !!! Regidx Rs1 = un_pj N)
        by (rewrite /D3 upd_ne; [exact HD2s1 | reg_neq]).
      assert (HD3ra : D3 !!! Regidx Rra = mword_of_int (UT + 0x3e))
        by (rewrite /D3 upd_eq; pcw).
      assert (HcsD3 : ut_cs m0 D3)
        by (rewrite /D3; apply ut_cs_insert;
            [vm_compute; reflexivity | exact HcsD2]).
      iApply (DE.wp_devintr_sconf (un_u N) (un_v N) (un_k N) (un_tk N) (un_s N)
                (un_pd N) (un_pav N) (un_pu N)
                D3 nx 0 false (un_pj N) C (DfracOwn 1) sc ∅
                Hlen ltac:(change (2 ^ 31)%Z with 2147483648%Z; lia)
                ltac:(unfold devintr_stack; lia)
                with "Hcg Hcpu Htext Hpc Hsc Hdc [-]").
      all: try lkbelow.
      iIntros (mg) "[%Hcsg %Hga0] Hcg Hcpu Hsc Hpc".
      assert (Hret3e : ret_pc (D3 !!! Regidx Rra) = mword_of_int (UT + 0x3e))
        by (rewrite HD3ra; pcw).
      iEval (rewrite Hret3e) in "Hpc".
      assert (Hgsp : mg !!! Regidx csp_rs1 = pa_stk ksp 4)
        by (rewrite (callee_saved_lookup Hcsg csp_rs1
                       ltac:(vm_compute; reflexivity)); exact HD3sp).
      assert (Hgs1 : mg !!! Regidx Rs1 = un_pj N)
        by (rewrite (callee_saved_lookup Hcsg Rs1
                       ltac:(vm_compute; reflexivity)); exact HD3s1).
      assert (Hcsg' : ut_cs m0 mg)
        by exact (ut_cs_trans m0 D3 mg HcsD3 (ut_cs_of_callee_saved _ _ Hcsg)).
      (* ---- +0x3e: c.mv s2,a0 -- which_dev ---- *)
      iApply (wp_cmv_s_sconf (mword_of_int (UT + 0x3e)) Rs2 Ra0 mg nx false
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi3e [-]").
      iApply wp_next_off_intro. iIntros "Hcg Hpc".
      set (D4 := <[Regidx Rs2 := regval_into_reg
                     (add_vec zero_reg (rget mg Ra0))]> mg).
      change (<[Regidx Rs2 := regval_into_reg
                 (add_vec zero_reg (rget mg Ra0))]> mg) with D4.
      assert (HD4sp : D4 !!! Regidx csp_rs1 = pa_stk ksp 4)
        by (rewrite /D4 upd_ne; [exact Hgsp | reg_neq]).
      assert (HD4s1 : D4 !!! Regidx Rs1 = un_pj N)
        by (rewrite /D4 upd_ne; [exact Hgs1 | reg_neq]).
      assert (HcsD4 : ut_cs m0 D4)
        by (rewrite /D4; apply ut_cs_insert4;
            [right; right; right; reflexivity | exact Hcsg']).
      assert (HD4a0 : rget D4 Ra0 = devintr_ret sc).
      { rgne. rewrite /D4 upd_ne; [| reg_neq]. exact Hga0. }
      assert (Hp40 : add_vec_int (mword_of_int (UT + 0x3e) : mword 64) 2
                     = mword_of_int (UT + 0x40)) by pcw.
      iEval (rewrite Hp40) in "Hpc".
      (* ---- +0x40: c.bnez a0 -> +0xea (the device arm) ---- *)
      destruct (neq_vec (rget D4 Ra0) (zero_reg : mword 64)) eqn:Hdev.
      + (* a device interrupt was handled *)
        iApply (wp_cbnez_taken_s_sconf (mword_of_int (UT + 0x40))
                  (mword_of_int 85 : mword 8) (Cregidx (mword_of_int 2)) Ra0
                  D4 nx false ltac:(vm_compute; reflexivity)
                  ltac:(vm_compute; discriminate) Hdev
                  ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi40 [-]").
        iNext. iApply wp_next_off_intro. iIntros "Hcg Hpc".
        assert (Hjea : add_vec (mword_of_int (UT + 0x40) : mword 64)
                         (sign_extend' 64 (sign_extend' 13
                            (concat_vec (mword_of_int 85 : mword 8) ('b"0"))))
                       = mword_of_int (UT + 0xea)) by pcw.
        iEval (rewrite Hjea) in "Hpc".
        iAssert (ut_hold SY.syscall_env N V C false ∅)
          with "[Hcpu Hclm Hep Hsc Hst Hstv Hq Hsret Hkpt Hown]" as "Hhold".
        { iApply (ud_hold N V C ep sc st with
                    "Hih Hcpu Hclm Hep Hsc Hst Hstv Hq Hsret Hkpt [Hown]").
          rewrite /ut_env. iSplitR; [iExact "Hcaps" | iExact "Hown"]. }
        iApply (A.ut_e8 SY.syscall_env N V pt ksp m0 D4 av nx C
                  mie_v menvcfg0 ∅
                  Hwf' Hav Hnx Htfpe Hksp Hm0sp HD4sp HD4s1 HcsD4
                  Hmiev Hmenvv
                  with "Htext Hpc Hcg Hhold Hframe Hcont").
      + (* no device: the two page-fault causes, then the fall-through *)
        iPoseProof (uti_042 with "Htext") as "Hi42".
        iPoseProof (uti_046 with "Htext") as "Hi46".
        iPoseProof (uti_048 with "Htext") as "Hi48".
        iApply (wp_cbnez_fall_s_sconf (mword_of_int (UT + 0x40))
                  (mword_of_int 85 : mword 8) (Cregidx (mword_of_int 2)) Ra0
                  D4 nx false ltac:(vm_compute; reflexivity)
                  ltac:(vm_compute; discriminate) Hdev
                  with "Hcg Hpc Hi40 [-]").
        iApply wp_next_off_intro. iIntros "Hcg Hpc".
        assert (Hp42 : add_vec_int (mword_of_int (UT + 0x40) : mword 64) 2
                       = mword_of_int (UT + 0x42)) by pcw.
        iEval (rewrite Hp42) in "Hpc".
        (* ---- +0x42: csrr a4,scause ---- *)
        iApply (wp_csrr_scause_s_sconf (mword_of_int (UT + 0x42)) Ra4 D4 nx
                  (DfracOwn 1) sc ltac:(vm_compute; discriminate) ltac:(rdok)
                  with "Hcg Hsc Hpc Hi42 [-]").
        iApply wp_next_off_intro. iIntros "Hcg Hsc Hpc".
        set (D5 := <[Regidx Ra4 := regval_into_reg sc]> D4).
        change (<[Regidx Ra4 := regval_into_reg sc]> D4) with D5.
        assert (HD5sp : D5 !!! Regidx csp_rs1 = pa_stk ksp 4)
          by (rewrite /D5 upd_ne; [exact HD4sp | reg_neq]).
        assert (HD5s1 : D5 !!! Regidx Rs1 = un_pj N)
          by (rewrite /D5 upd_ne; [exact HD4s1 | reg_neq]).
        assert (HcsD5 : ut_cs m0 D5)
          by (rewrite /D5; apply ut_cs_insert;
              [vm_compute; reflexivity | exact HcsD4]).
        assert (Hp46 : add_vec_int (mword_of_int (UT + 0x42) : mword 64) 4
                       = mword_of_int (UT + 0x46)) by pcw.
        iEval (rewrite Hp46) in "Hpc".
        (* ---- +0x46: c.li a5,15 ---- *)
        iApply (wp_cli_s_sconf (mword_of_int (UT + 0x46)) Ra5
                  (mword_of_int 15 : mword 6)
                  (add_vec zero_reg (sign_extend' 64
                     (sign_extend' 12 (mword_of_int 15 : mword 6))))
                  D5 nx false ltac:(vm_compute; discriminate) ltac:(rdok) eq_refl
                  with "Hcg Hpc Hi46 [-]").
        iApply wp_next_off_intro. iIntros "Hcg Hpc".
        set (D6 := <[Regidx Ra5 := regval_into_reg
                       (add_vec zero_reg (sign_extend' 64
                          (sign_extend' 12 (mword_of_int 15 : mword 6))))]> D5).
        change (<[Regidx Ra5 := regval_into_reg
                   (add_vec zero_reg (sign_extend' 64
                      (sign_extend' 12 (mword_of_int 15 : mword 6))))]> D5) with D6.
        assert (HD6sp : D6 !!! Regidx csp_rs1 = pa_stk ksp 4)
          by (rewrite /D6 upd_ne; [exact HD5sp | reg_neq]).
        assert (HD6s1 : D6 !!! Regidx Rs1 = un_pj N)
          by (rewrite /D6 upd_ne; [exact HD5s1 | reg_neq]).
        assert (HcsD6 : ut_cs m0 D6)
          by (rewrite /D6; apply ut_cs_insert;
              [vm_compute; reflexivity | exact HcsD5]).
        assert (Hp48 : add_vec_int (mword_of_int (UT + 0x46) : mword 64) 2
                       = mword_of_int (UT + 0x48)) by pcw.
        iEval (rewrite Hp48) in "Hpc".
        (* ---- +0x48: beq a4,a5 -> +0xd0 (vmfault, store page fault) ---- *)
        destruct (eq_vec (rget D6 Ra4) (rget D6 Ra5)) eqn:Hf15.
        * iApply (wp_beq_taken_s_sconf (mword_of_int (UT + 0x48))
                    (mword_of_int 136 : mword 13) Ra5 Ra4 D6 nx false
                    ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                    Hf15 ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi48 [-]").
          iNext. iApply wp_next_off_intro. iIntros "Hcg Hpc".
          assert (Hjd0 : add_vec (mword_of_int (UT + 0x48) : mword 64)
                           (sign_extend' 64 (mword_of_int 136 : mword 13))
                         = mword_of_int (UT + 0xd0)) by pcw.
          iEval (rewrite Hjd0) in "Hpc".
          iAssert (ut_hold SY.syscall_env N V C false ∅)
            with "[Hcpu Hclm Hep Hsc Hst Hstv Hq Hsret Hkpt Hown]" as "Hhold".
          { iApply (ud_hold N V C ep sc st with
                      "Hih Hcpu Hclm Hep Hsc Hst Hstv Hq Hsret Hkpt [Hown]").
            rewrite /ut_env. iSplitR; [iExact "Hcaps" | iExact "Hown"]. }
          iApply (A.ut_d0 SY.syscall_env N V pt ksp m0 D6 av nx C
                    mie_v menvcfg0 ∅
                    Hpk Hwf' Hav Hnx Htfpe Hksp Hm0sp HD6sp HD6s1 HcsD6
                    Hmiev Hmenvv
                    with "Htext Hpc Hcg Hhold Hframe Hcont").
        * iPoseProof (uti_04c with "Htext") as "Hi4c".
          iPoseProof (uti_050 with "Htext") as "Hi50".
          iPoseProof (uti_052 with "Htext") as "Hi52".
          iApply (wp_beq_fall_s_sconf (mword_of_int (UT + 0x48))
                    (mword_of_int 136 : mword 13) Ra5 Ra4 D6 nx false
                    ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                    Hf15 with "Hcg Hpc Hi48 [-]").
          iApply wp_next_off_intro. iIntros "Hcg Hpc".
          assert (Hp4c : add_vec_int (mword_of_int (UT + 0x48) : mword 64) 4
                         = mword_of_int (UT + 0x4c)) by pcw.
          iEval (rewrite Hp4c) in "Hpc".
          (* ---- +0x4c: csrr a4,scause ---- *)
          iApply (wp_csrr_scause_s_sconf (mword_of_int (UT + 0x4c)) Ra4 D6 nx
                    (DfracOwn 1) sc ltac:(vm_compute; discriminate) ltac:(rdok)
                    with "Hcg Hsc Hpc Hi4c [-]").
          iApply wp_next_off_intro. iIntros "Hcg Hsc Hpc".
          set (D7 := <[Regidx Ra4 := regval_into_reg sc]> D6).
          change (<[Regidx Ra4 := regval_into_reg sc]> D6) with D7.
          assert (HD7sp : D7 !!! Regidx csp_rs1 = pa_stk ksp 4)
            by (rewrite /D7 upd_ne; [exact HD6sp | reg_neq]).
          assert (HD7s1 : D7 !!! Regidx Rs1 = un_pj N)
            by (rewrite /D7 upd_ne; [exact HD6s1 | reg_neq]).
          assert (HcsD7 : ut_cs m0 D7)
            by (rewrite /D7; apply ut_cs_insert;
                [vm_compute; reflexivity | exact HcsD6]).
          assert (Hp50 : add_vec_int (mword_of_int (UT + 0x4c) : mword 64) 4
                         = mword_of_int (UT + 0x50)) by pcw.
          iEval (rewrite Hp50) in "Hpc".
          (* ---- +0x50: c.li a5,13 ---- *)
          iApply (wp_cli_s_sconf (mword_of_int (UT + 0x50)) Ra5
                    (mword_of_int 13 : mword 6)
                    (add_vec zero_reg (sign_extend' 64
                       (sign_extend' 12 (mword_of_int 13 : mword 6))))
                    D7 nx false ltac:(vm_compute; discriminate) ltac:(rdok) eq_refl
                    with "Hcg Hpc Hi50 [-]").
          iApply wp_next_off_intro. iIntros "Hcg Hpc".
          set (D8 := <[Regidx Ra5 := regval_into_reg
                         (add_vec zero_reg (sign_extend' 64
                            (sign_extend' 12 (mword_of_int 13 : mword 6))))]> D7).
          change (<[Regidx Ra5 := regval_into_reg
                     (add_vec zero_reg (sign_extend' 64
                        (sign_extend' 12 (mword_of_int 13 : mword 6))))]> D7)
            with D8.
          assert (HD8sp : D8 !!! Regidx csp_rs1 = pa_stk ksp 4)
            by (rewrite /D8 upd_ne; [exact HD7sp | reg_neq]).
          assert (HD8s1 : D8 !!! Regidx Rs1 = un_pj N)
            by (rewrite /D8 upd_ne; [exact HD7s1 | reg_neq]).
          assert (HcsD8 : ut_cs m0 D8)
            by (rewrite /D8; apply ut_cs_insert;
                [vm_compute; reflexivity | exact HcsD7]).
          assert (Hp52 : add_vec_int (mword_of_int (UT + 0x50) : mword 64) 2
                         = mword_of_int (UT + 0x52)) by pcw.
          iEval (rewrite Hp52) in "Hpc".
          (* ---- +0x52: beq a4,a5 -> +0xd0 (vmfault, load page fault) ---- *)
          destruct (eq_vec (rget D8 Ra4) (rget D8 Ra5)) eqn:Hf13.
          -- iApply (wp_beq_taken_s_sconf (mword_of_int (UT + 0x52))
                       (mword_of_int 126 : mword 13) Ra5 Ra4 D8 nx false
                       ltac:(vm_compute; discriminate)
                       ltac:(vm_compute; discriminate)
                       Hf13 ltac:(vm_compute; reflexivity)
                       with "Hcg Hpc Hi52 [-]").
             iNext. iApply wp_next_off_intro. iIntros "Hcg Hpc".
             assert (Hjd0' : add_vec (mword_of_int (UT + 0x52) : mword 64)
                              (sign_extend' 64 (mword_of_int 126 : mword 13))
                            = mword_of_int (UT + 0xd0)) by pcw.
             iEval (rewrite Hjd0') in "Hpc".
             iAssert (ut_hold SY.syscall_env N V C false ∅)
               with "[Hcpu Hclm Hep Hsc Hst Hstv Hq Hsret Hkpt Hown]" as "Hhold".
             { iApply (ud_hold N V C ep sc st with
                         "Hih Hcpu Hclm Hep Hsc Hst Hstv Hq Hsret Hkpt [Hown]").
               rewrite /ut_env. iSplitR; [iExact "Hcaps" | iExact "Hown"]. }
             iApply (A.ut_d0 SY.syscall_env N V pt ksp m0 D8 av nx C
                       mie_v menvcfg0 ∅
                       Hpk Hwf' Hav Hnx Htfpe Hksp Hm0sp HD8sp HD8s1 HcsD8
                       Hmiev Hmenvv
                       with "Htext Hpc Hcg Hhold Hframe Hcont").
          -- (* the unexpected-scause arm *)
             iApply (wp_beq_fall_s_sconf (mword_of_int (UT + 0x52))
                       (mword_of_int 126 : mword 13) Ra5 Ra4 D8 nx false
                       ltac:(vm_compute; discriminate)
                       ltac:(vm_compute; discriminate)
                       Hf13 with "Hcg Hpc Hi52 [-]").
             iApply wp_next_off_intro. iIntros "Hcg Hpc".
             assert (Hp56 : add_vec_int (mword_of_int (UT + 0x52) : mword 64) 4
                            = mword_of_int (UT + 0x56)) by pcw.
             iEval (rewrite Hp56) in "Hpc".
             iAssert (ut_hold SY.syscall_env N V C false ∅)
               with "[Hcpu Hclm Hep Hsc Hst Hstv Hq Hsret Hkpt Hown]" as "Hhold".
             { iApply (ud_hold N V C ep sc st with
                         "Hih Hcpu Hclm Hep Hsc Hst Hstv Hq Hsret Hkpt [Hown]").
               rewrite /ut_env. iSplitR; [iExact "Hcaps" | iExact "Hown"]. }
             iApply (A.ut_56 SY.syscall_env N V pt ksp m0 D8 av nx C
                       mie_v menvcfg0 ∅
                       Hpk Hwf' Hav Hnx Htfpe Hksp Hm0sp HD8sp HD8s1 HcsD8
                       Hmiev Hmenvv
                       with "Htext Hpc Hcg Hhold Hframe Hcont").
  Qed.

End UtDispatch.


(* ===================================================================== *)
(*  THE SEAL.                                                             *)
(* ===================================================================== *)
(* [ut_res] is destructed exactly ONCE, here, and the entry block does the
   rest.  Two non-obvious steps:
   * printk's contract is a PURE hypothesis all the way down
     ([ProofUsertrapArms]' [ut_56]/[ut_d0] take it as an [->]), so that the
     three blocks below the dispatch carry no functor argument for it.  It is
     OBTAINED here from [PK], which is what puts [LinkPrintk]'s axiom in
     usertrap's footprint -- deliberately, since the unexpected-scause arm is
     LIVE and does call printk on its general path.
   * the boundary's crossing is at [wp_next true (proc_addr j)] while the
     whole walk runs at [un_pj N]; [UsertrapRes.wp_next_true_swap] moves it,
     and at index [true] that is sound and free (usertrap.md finding 4b). *)
Definition usertrap_res
    `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !bioG Σ,
      !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ, !fsCrashG Σ,
      !kallocG Σ, !irefslotG Σ, !iregG Σ}
    `{GEN : GenId} `{CID : CpuId} : uptd -> mword 64 -> iProp Σ :=
  ut_res SY.syscall_env.

Lemma usertrap_res_tf_open
    `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !bioG Σ,
      !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ, !fsCrashG Σ,
      !kallocG Σ, !irefslotG Σ, !iregG Σ}
    `{GEN : GenId} `{CID : CpuId} (pt : uptd) (ksp : mword 64) :
  usertrap_res pt ksp -∗
  ∃ ws : list (mword 64), tf_page (ud_tfp pt) ws ∗
    (∀ ws' : list (mword 64), tf_page (ud_tfp pt) ws' -∗ usertrap_res pt ksp).
Proof. exact (ut_res_tf_open SY.syscall_env pt ksp). Qed.

Section UtSeal.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !bioG Σ,
            !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ, !fsCrashG Σ,
            !kallocG Σ, !irefslotG Σ, !iregG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  (* printk's contract, as the [Prop] the arms take -- from the functor
     argument, at whatever hart the call happens on. *)
  Local Lemma ut_printk (γpr : gname) (γd : uart_names) (γv : disk_names) :
    printk_gen_contract γpr γd γv.
  Proof.
    intros CIDp m0 K eb pj Cc dqf f descs b.
    exact (PK.wp_printk_gen_sconf (CID := CIDp) γpr γd γv m0 K eb pj Cc
             (dqf := dqf) f descs b).
  Qed.

  Lemma wp_usertrap (pt : uptd) (j : nat) (m : regfile)
      (ms_v sc_v stval_v sepc_v ksp : mword 64)
      (mie_v mdv0 menvcfg0 : mword 64) :
    wp_usertrap_body (fun h : CpuId => usertrap_res (CID := h))
      pt j m ms_v sc_v stval_v sepc_v ksp mie_v mdv0 menvcfg0.
  Proof.
    cbv beta delta [wp_usertrap_body].
    intros pcE pj Hms Hj Hsp Htp Hmiev Hmask Hmenvv.
    iIntros "#Htext Hpc #Hhw #Hminv Hhs Hpriv Hms Hsc Hst Hep Hstv
             Hmie Hmdl Hmenv Hgpr HR Hcont".
    (* SCOPED: a bare [rewrite] would unfold [ut_res] inside the crossing's
       [usertrap_post] too, and the blocks state it folded. *)
    iEval (rewrite /usertrap_res /ut_res) in "HR".
    iDestruct "HR" as (N V av C) "(%Hupt & %Hksp & %Hwf & %Hav & Htrap & Henv)".
    assert (Hpjnz : pj <> (zero_reg : mword 64))
      by exact (proc_addr_nonzero j Hj).
    iDestruct (wp_next_true_swap pj (un_pj N) _ Hpjnz with "Hcont") as "Hcont".
    iApply (ut_entry SY.syscall_env N V ksp m av C ms_v sc_v stval_v sepc_v
              mie_v mdv0 menvcfg0
              Hms Hav Hsp Htp Hmiev Hmask Hmenvv
              with "Htext Hpc Hhw Hminv Hhs Hpriv Hms Hsc Hst Hep Hstv
                    Hmie Hmdl Hmenv Hgpr Htrap Henv [Hcont]").
    iIntros (M V') "%HMsp %HMs1 %HMa0 %HcsM %HuptV Hpc Hcg Hcpu Hclm Hraw Henv Hfr".
    iApply (ut_dispatch N V' pt ksp m M av (av - 4)%nat C sepc_v sc_v stval_v
              mie_v menvcfg0
              (ut_printk (un_pr N) (un_u N) (un_v N)) Hwf Hav
              (trap_res_off (av - 4)%nat)
              ltac:(rewrite HuptV Hupt; reflexivity) Hksp Hsp HMsp HMs1 HMa0 HcsM
              Hmiev Hmenvv
              with "Htext Hpc Hcg Hcpu Hclm Hraw Henv Hfr Hcont").
  Qed.

End UtSeal.

End UsertrapProof.
