(* ProofUsertrapTail.v -- usertrap's TAIL: the three blocks every arm ends
   in, plus the exit disassembly.

     +0xa6   if (killed(p)) { which_dev = 0; kexit(-1); }        <- ut_a6
     +0xae   prepare_return();
             uint64 satp = MAKE_SATP(p->pagetable);
             <epilogue>; return satp;                            <- ut_ret
     +0xfc   if (which_dev == 2) yield();  goto +0xae             <- ut_fa

   WHY THIS IS THE FIRST FILE OF THE WALK, and why it is index-GENERIC.
   +0xa6 is reached at [b = true] from the syscall arm (whose [csrsi
   sstatus,2] at +0x9e re-enabled interrupts) and at [b = false] from the
   devintr / vmfault / unexpected-scause arms.  Every callee it reaches is
   already index-generic -- killed, kexit, prepare_return, yield -- so the
   three blocks are proved ONCE over a parameter [b], and the four arms above
   instantiate them.  That is also why [UsertrapRes.ut_hold] exists: at
   [b = true] the trap-CSR set and the running claim live inside [sie_arm]
   and the caller brings [emp], at [b = false] it brings them itself, and
   [trap_csrs_ext] / [cpu_claim_ext] are exactly that difference.

   THE ONE THING THE TAIL HAS TO GET RIGHT IS THE EXIT, and it is not the
   epilogue's four loads.  It is that the machine state prepare_return hands
   back re-assembles [SpecUsertrap]'s boundary: the sret-ready mstatus is
   DERIVED, not arranged ([UsertrapRes.ut_exit_ms_ok]), from the loose SIE
   quarter's agreement with [sconf]'s half and the travelling sret mirror's
   with [sconf]'s tie -- so the two ghost fractions the excursion through user
   mode parks are what makes the return legal.  See UsertrapRes.v's header.

   [mf] IS [tp_pin] OF THE FINAL MAP, which is the cheapest way to meet the
   boundary's [mf !!! tp = cid_word]: usertrap may have MIGRATED, so the tp
   SLOT of the map it has been threading still holds the entry hart's id
   while [gpr_file] holds the pinned one.  Handing over [tp_pin M] makes the
   two agree by construction ([HartTp.tp_pin_id]), and tp is deliberately not
   one of [CalleeSaved.callee_saved]'s thirteen, so nothing else moves. *)
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
Require Import KernelText KernelRvcDecode.
Require Import WpGprCsrwA.
Require Import WpSconfAlu WpSconfMem WpSconfCtl WpSconfBtype.
Require Import WpSmodeIntr.        (* [wp_cli_s_sconf] *)
Require Import WpKvminithart.      (* [kvi_satp_word] and its three facts *)
Require Import IntrDefs.
Require Import WpLock.
Require Import ProcGeom.
Require Import UserPtTree.
Require Import ProcPtOwn.
Require Import KallocInv.
Require Import PanicStub.
Require Import BioInv DiskPtsto WpUart FsBlocks LogInv FsCrash.
Require Import IrefSlots InodeRegion.
Require Import FdSlots ProcInv.
Require Import SchedCtx PanicStub.
Require Import FileInvDefs.
Require Import CodeUsertrap.
Require Import SpecKilled SpecKexit SpecYield SpecPrepareReturn.
Require Import SpecSyscall SpecSysExit.
Require Import SpecUsertrap UsertrapRes.
Require Import ProofUsertrapParts.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Import Defs.
Local Open Scope Z_scope.
Set Printing Depth 40.

Module UtTail (PR : PREPARE_RETURN) (KI : KILLED) (KE : KEXIT) (YI : YIELD).

(* register indices and the two scripts, at MODULE level: an [Ltac] defined
   inside a section is discharged over its variables and unusable in the next
   one, and a [Notation] inside a section disappears with it. *)
Notation Rra := (mword_of_int 1  : mword 5).
Notation Rs0 := (mword_of_int 8  : mword 5).
Notation Rs1 := (mword_of_int 9  : mword 5).
Notation Rs2 := (mword_of_int 18 : mword 5).
Notation Ra0 := (mword_of_int 10 : mword 5).
Notation Ra5 := (mword_of_int 15 : mword 5).

Ltac reg_neq :=
  lazymatch goal with |- ?a <> ?b =>
    tryif unify a b then fail else (vm_compute; discriminate) end.

Ltac pcw := apply bv_eq; vm_compute; reflexivity.


Section ProofUsertrapTail.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !bioG Σ,
            !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ, !fsCrashG Σ,
            !kallocG Σ, !irefslotG Σ, !iregG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.
  (* the syscall environment, an ordinary hart-free parameter here: the tail
     never touches it, it only hands it on.  See SpecSyscall's note. *)
  Context (Rsys : gname -> mword 64 -> iProp Σ).


  (* ==================================================================== *)
  (* THE kexit(-1) DEAD END.                                              *)
  (* ==================================================================== *)
  (* usertrap reaches it from three places (+0xca on the syscall arm, +0xf6
     from the devintr arm's killed check -- through the [j +0xf6] at +0xf2 --
     and +0xf4's fall-through from +0xa6), and each time it spends the WHOLE
     bundle: kexit has no
     continuation, so [ut_hold]'s trap-CSR set, running claim, per-cpu bundle
     and environment all go with the dying process.  [Rsys] is the one member
     kexit does not want, and dropping it is right -- the syscalls' footprint
     belongs to a process that is going to run one. *)
  Lemma ut_kexit (N : ut_names) (V : pprivate) (m : regfile) (nx : nat)
      (C : iProp Σ) (b : bool) (lks : gset nat) :
    ut_wf N ->
    (K_kexit <= nx)%nat ->
    (* kexit's own cone bottoms out at "ftable" (1) -- the fileclose loop --
       and every deeper lock it reaches (itable/log/wait_lock/proc) follows
       by [locks_below_mono] inside its own contract, so this is the ONE
       premise the tail owes it. *)
    locks_below lks (lock_rank "log") ->
    kernel_text -∗
    pc_is (mword_of_int KernelSyms.kexit) -∗
    sie_cap_gpr m nx b (un_pj N) -∗
    ut_hold Rsys N V C b lks -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hwf Hnx Hbelow. destruct Hwf as (Hj & Hjl & Hlen & Hlg).
    iIntros "#Htext Hpc Hcg (Hcpu & Hcsrs & Hclm & [#Hcaps Hown])".
    iDestruct "Hcaps" as "(#Hpi & #Hpa & #Hkd & #Hks & #Hdi & #Hpk & #Hw & #Hft
                           & #Hkm & #Hdk & #Hbio & #Hlog & #Hseam & #Hgc & #Hdev
                           & #Hgeom & #Hav & #Hic)".
    iDestruct "Hown" as "(Hbs & Hbm & Hip & Hfd & Hir & Hpv & _)".
    iApply (KE.wp_kexit_sconf (un_ft N) (un_f N) (un_w N) (un_s N) (un_j N) (un_l N)
              (un_u N) (un_v N) (un_k N) (un_pd N) (un_pav N) (un_pu N)
              (un_bn N) (un_lg N) (un_fs N) (un_cov N) (un_logstart N) (un_dev N)
              (un_ip N) (un_dqi N) (un_kl N) (un_ka N)
              (un_i N) (un_cn N) (un_tl N) (un_bmapstart N) (un_inodestart N)
              (un_nib N) (un_size N) (un_dqb N) (un_dqs N) (un_us N)
              None (un_fn N) m nx b C b _ (un_pid N) V
              eq_refl Hj Hjl Hnx Hlg Hbelow
              with "Hcg Hcpu Hcsrs Hclm Htext Hpc Hpi Hpa Hw Hft Hkm Hav
                    Hbio Hlog Hseam Hgc Hdev Hgeom Hdk Hbs Hic Hbm Hip Hfd Hir Hpv").
    all: try lkbelow.
  Qed.


End ProofUsertrapTail.

Section UtRet2.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !bioG Σ,
            !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ, !fsCrashG Σ,
            !kallocG Σ, !irefslotG Σ, !iregG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.
  Context (Rsys : gname -> mword 64 -> iProp Σ).

  (* ==================================================================== *)
  (* +0xb2 .. +0xc6: MAKE_SATP, the epilogue, THE EXIT.                    *)
  (* ==================================================================== *)
  (* ITS OWN SECTION, WHICH IS THE POINT.  prepare_return's post is a
     [wp_next b p] crossing, so everything from +0xb2 on runs on a hart that
     may not be the one usertrap was entered on -- and [CpuId] is a CLASS, so
     a leaf applied inside the caller's section resolves its hart by INSTANCE
     RESOLUTION and picks the section variable, not the hypothesis's hart.
     Annotating every leaf with [(CID := ...)] works and is what the tier does
     for one or two steps; for a fifteen-instruction stretch the honest move is
     durable-notes' "the chaining lemma needs its OWN section": stated here,
     the ambient [CID] IS the post-crossing hart and not one annotation is
     needed.  [ut_ret] below applies it at [(CID := CIDp)]. *)
  Lemma ut_ret2 (N : ut_names) (V : pprivate) (pt : uptd) (ksp : mword 64)
      (m0 mf : regfile) (av nx : nat) (C : iProp Σ) (b : bool)
      (uepc : mword 64) (vb : mword 1)
      (mie_v menvcfg0 : mword 64) (lks : gset nat) :
    ut_wf N ->
    (K_usertrap <= av)%nat ->
    (trap_res b + nx)%nat = (av - 4)%nat ->
    ud_tfp (pv_upt V) = ud_tfp pt ->
    add_vec (un_ks N) (mword_of_int 4096) = ksp ->
    m0 !!! Regidx csp_rs1 = ksp ->
    mf !!! Regidx csp_rs1 = pa_stk ksp 4 ->
    mf !!! Regidx Rs1 = un_pj N ->
    ut_cs m0 mf ->
    (* [mie]/[menvcfg] -- each a unique architectural constant -- are pinned
       and threaded through the whole call (see UsertrapRes.v's [ut_trap]
       header comment); [mideleg]'s value is NOT (see [usertrap_post]'s
       comment) and is discovered fresh from [sconf] below, not threaded
       as a parameter here. *)
    mie_v = MIE_S ->
    menvcfg0 = MENVCFG_S ->
    kernel_text -∗
    pc_is (mword_of_int (UT + 0xb2)) -∗
    (* ---- exactly what prepare_return handed back ---- *)
    sie_cap_gpr mf (trap_res b + nx)%nat false (un_pj N) -∗
    cpu_own 0%nat false (un_pj N) C false lks -∗
    cpu_claim (un_pj N) -∗
    sepc ↦ᵣ mepc_val uepc -∗
    (∃ v : mword 64, scause ↦ᵣ v) -∗
    (∃ v : mword 64, stval ↦ᵣ v) -∗
    sret_bits ('b"0" : mword 1) ('b"1" : mword 1) -∗
    stvec ↦ᵣ uservec_tvec -∗
    ghost_var sie_gname (1/4) vb -∗
    strans_bit strans_bit_kpt -∗
    ut_env Rsys N V -∗
    ut_frame ksp (m0 !!! Regidx Rra) (m0 !!! Regidx Rs0)
                 (m0 !!! Regidx Rs1) (m0 !!! Regidx Rs2) -∗
    wp_next true (un_pj N)
      (fun CID' => usertrap_post (CID := CID') (ut_res (CID := CID') Rsys) pt ksp m0
                     mie_v menvcfg0) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hwf Hav Hnx Htfpe Hksp Hm0sp Hmfsp Hmfs1 Hcs Hmiev Hmenvv.
    (* the budget, in numbers [lia] can see -- every one of these is a
       [Definition] and the index arithmetic below is what needs them *)
    pose proof Hav as Hav'.
    unfold K_usertrap, kv_frame_slots, K_syscall, K_sys_exit, K_kexit in Hav'.
    destruct Hwf as (Hj & Hjl & Hlen & Hlg).
    iIntros "#Htext Hpc Hcg Hcpu Hclm Hsepc Hscause Hstval Hsret Hstvec Hq4
             Hkptr [#Hcaps Hown] Hframe Hcont".
    (* the boundary hands the trap resource back at the literal [∅] that
       [ut_res] pins -- depth 0 forces the held set empty, so this is a
       re-spelling, not an obligation. *)
    iDestruct (cpu_own_zero_empty with "Hcpu") as "[%Hlkempty Hcpu]".
    (* THE QUARTER'S VALUE IS NOT A DEGREE OF FREEDOM.  prepare_return leaves
       it existential because it never reads it; the arm it also hands back is
       at [false], and [sie_arm_half_agree] reads the live SIE off that index,
       so the half / quarter agreement pins [vb = 'b"0"] -- which is what
       [ut_exit_ms_ok] needs and what makes the return legal. *)
    iDestruct (sie_cap_gpr_split with "Hcg") as "(Hhs & Hsc & Hcap & Hfile)".
    iDestruct (sconf_priv_open with "Hsc") as (msf) "(Hcl & Hpriv & Hmsown)".
    iDestruct "Hmsown" as "(Hms & Hhalf & Htie & %Hmsf)".
    iDestruct "Hcap" as "(Hstk & Hstr & Harm)".
    iDestruct (sie_arm_half_agree false (un_pj N) msf with "Hhalf Harm") as %Hsie0.
    iDestruct (ghost_var_agree with "Hhalf Hq4") as %Hvb.
    rewrite Hsie0 in Hvb. rewrite -Hvb.
    iDestruct (sret_bits_agree _ _ _ _ with "Htie Hsret") as %[Hspp Hspie].
    iAssert (sconf_msown msf) with "[Hms Hhalf Htie]" as "Hmsown".
    { rewrite /sconf_msown. iSplitL "Hms"; [iExact "Hms"|].
      iSplitL "Hhalf"; [iExact "Hhalf"|].
      iSplitL "Htie"; [iExact "Htie"|]. iPureIntro. exact Hmsf. }
    iDestruct (ut_exit_ms_ok msf with "Hmsown Hsret Hq4") as %Hretms.
    iDestruct "Hmsown" as "(Hms & Hhalf & Htie & _)".
    rewrite /sret_tie Hspp Hspie.
    rewrite Hsie0.
    (* the pieces back into a bundle for the walk *)
    iAssert (sconf) with "[Hcl Hpriv Hms Hhalf Htie]" as "Hsc".
    { iApply ("Hcl" $! msf with "Hpriv [Hms Hhalf Htie]").
      rewrite /sconf_msown /sret_tie Hsie0 Hspp Hspie.
      iSplitL "Hms"; [iExact "Hms"|]. iSplitL "Hhalf"; [iExact "Hhalf"|].
      iSplitL "Htie"; [iExact "Htie"|]. iPureIntro. exact Hmsf. }
    iAssert (sie_cap_gpr mf (trap_res b + nx)%nat false (un_pj N))
      with "[Hhs Hsc Hstk Hstr Harm Hfile]" as "Hcg".
    { rewrite /sie_cap_gpr /sie_cap.
      iSplitL "Hhs"; [iExact "Hhs"|]. iSplitL "Hsc"; [iExact "Hsc"|].
      iSplitR "Hfile"; [| iExact "Hfile"].
      iSplitL "Hstk"; [iExact "Hstk"|]. iSplitL "Hstr"; [iExact "Hstr"|].
      iExact "Harm". }
    iDestruct (ut_own_priv with "Hown") as "(Hpv & Hsy & Hownback)".
    (* [ut_caps] is NOT destructured here: +0xb2..+0xc6 calls nothing, so no
       member of it is needed, and destructuring an intuitionistic hypothesis
       CONSUMES the name -- which the exit needs to hand [ut_env] back. *)
    iPoseProof (uti_0b2 with "Htext") as "Hib2".
    iPoseProof (uti_0b4 with "Htext") as "Hib4".
    iPoseProof (uti_0b6 with "Htext") as "Hib6".
    iPoseProof (uti_0b8 with "Htext") as "Hib8".
    iPoseProof (uti_0ba with "Htext") as "Hiba".
    iPoseProof (uti_0bc with "Htext") as "Hibc".
    iPoseProof (uti_0be with "Htext") as "Hibe".
    iPoseProof (uti_0c0 with "Htext") as "Hic0".
    iPoseProof (uti_0c2 with "Htext") as "Hic2".
    iPoseProof (uti_0c4 with "Htext") as "Hic4".
    iPoseProof (uti_0c6 with "Htext") as "Hic6".
    (* ---- +0xb2 .. +0xba: MAKE_SATP(p->pagetable) ---- *)
    iDestruct (proc_priv_copy with "Hpv") as "(Hsz & Hpgt & Hppt & Hpvback)".
    iDestruct (proc_pt_wf_get with "Hppt") as %Hptwf.
    assert (Hc2 : creg2reg_idx (Cregidx (mword_of_int 2)) = Regidx Ra0)
      by (vm_compute; reflexivity).
    assert (Hc7 : creg2reg_idx (Cregidx (mword_of_int 7)) = Regidx Ra5)
      by (vm_compute; reflexivity).
    assert (Haddrpg : add_vec (rget mf Rs1)
                        (sign_extend' 64 (mword_of_int 80 : mword 12))
                      = p_pagetable (un_pj N))
      by (rgne; rewrite Hmfs1; reflexivity).
    iEval (rewrite -Haddrpg) in "Hpgt".
    iApply (wp_cld_s_sconf (mword_of_int (UT + 0xb2)) Ra0 Rs1
              (mword_of_int 80 : mword 12) mf (trap_res b + nx)%nat
              (page_base (ud_root (pv_upt V))) false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hib2 Hpgt [-]").
    iApply wp_next_off_intro. iIntros "Hcg Hpc Hpgt".
    set (S0 := <[Regidx Ra0 := regval_into_reg
                   (page_base (ud_root (pv_upt V)))]> mf).
    change (<[Regidx Ra0 := regval_into_reg
               (page_base (ud_root (pv_upt V)))]> mf) with S0.
    assert (Hpb4 : add_vec_int (mword_of_int (UT + 0xb2) : mword 64) 2
                   = mword_of_int (UT + 0xb4)) by pcw.
    iEval (rewrite Hpb4) in "Hpc".
    (* ---- +0xb4: srli a0,a0,0xc ---- *)
    iEval (rewrite Hc2) in "Hib4".
    iApply (wp_csrli_s_sconf (mword_of_int (UT + 0xb4)) (Cregidx (mword_of_int 2))
              Ra0 (mword_of_int 12 : mword 6) S0 (trap_res b + nx)%nat false
              Hc2 ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hib4 [-]").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    set (S1 := <[Regidx Ra0 := regval_into_reg
                   (shift_bits_right (rget S0 Ra0)
                      (subrange_vec_dec (mword_of_int 12 : mword 6)
                         (Z.sub log2_xlen 1) 0))]> S0).
    change (<[Regidx Ra0 := regval_into_reg
               (shift_bits_right (rget S0 Ra0)
                  (subrange_vec_dec (mword_of_int 12 : mword 6)
                     (Z.sub log2_xlen 1) 0))]> S0) with S1.
    assert (Hpb6 : add_vec_int (mword_of_int (UT + 0xb4) : mword 64) 2
                   = mword_of_int (UT + 0xb6)) by pcw.
    iEval (rewrite Hpb6) in "Hpc".
    (* ---- +0xb6: li a5,-1 ---- *)
    iApply (wp_cli_s_sconf (mword_of_int (UT + 0xb6)) Ra5 (mword_of_int 63 : mword 6)
              (add_vec zero_reg (sign_extend' 64
                 (sign_extend' 12 (mword_of_int 63 : mword 6))))
              S1 (trap_res b + nx)%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok) eq_refl
              with "Hcg Hpc Hib6 [-]").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    set (S2 := <[Regidx Ra5 := regval_into_reg
                   (add_vec zero_reg (sign_extend' 64
                      (sign_extend' 12 (mword_of_int 63 : mword 6))))]> S1).
    change (<[Regidx Ra5 := regval_into_reg
               (add_vec zero_reg (sign_extend' 64
                  (sign_extend' 12 (mword_of_int 63 : mword 6))))]> S1) with S2.
    assert (Hpb8 : add_vec_int (mword_of_int (UT + 0xb6) : mword 64) 2
                   = mword_of_int (UT + 0xb8)) by pcw.
    iEval (rewrite Hpb8) in "Hpc".
    (* ---- +0xb8: slli a5,a5,0x3f ---- *)
    iApply (wp_cslli_s_sconf (mword_of_int (UT + 0xb8)) (Regidx Ra5) Ra5
              (mword_of_int 63 : mword 6) S2 (trap_res b + nx)%nat false
              eq_refl ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hib8 [-]").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    set (S3 := <[Regidx Ra5 := regval_into_reg
                   (shift_bits_left (rget S2 Ra5)
                      (subrange_vec_dec (mword_of_int 63 : mword 6)
                         (Z.sub log2_xlen 1) 0))]> S2).
    change (<[Regidx Ra5 := regval_into_reg
               (shift_bits_left (rget S2 Ra5)
                  (subrange_vec_dec (mword_of_int 63 : mword 6)
                     (Z.sub log2_xlen 1) 0))]> S2) with S3.
    assert (Hpba : add_vec_int (mword_of_int (UT + 0xb8) : mword 64) 2
                   = mword_of_int (UT + 0xba)) by pcw.
    iEval (rewrite Hpba) in "Hpc".
    (* ---- +0xba: or a0,a0,a5 -- THE WORD IS kvminithart's ----
       The same five instructions as kvminithart's MAKE_SATP over a different
       register pair, and [WpKvminithart.kvi_satp_word] is register-free, so
       its three field facts ([kvi_satp_mode] / [_asid] / [_ppn]) serve
       verbatim -- which is the whole of [satp_rooted]. *)
    iEval (rewrite Hc2 Hc7) in "Hiba".
    assert (Hor : or_vec (rget S3 Ra0) (rget S3 Ra5)
                  = kvi_satp_word (ud_root (pv_upt V))).
    { assert (HS3a0 : rget S3 Ra0
                = shift_bits_right
                    (zero_extend' 64 (concat_vec (ud_root (pv_upt V))
                                        (zeros' 12 : mword 12)))
                    (subrange_vec_dec (mword_of_int 12 : mword 6)
                       (Z.sub log2_xlen 1) 0)).
      { rgne. rewrite /S3 upd_ne; [| reg_neq]. rewrite /S2 upd_ne; [| reg_neq].
        rewrite /S1 upd_eq. rgne. rewrite /S0 upd_eq. reflexivity. }
      assert (HS3a5 : rget S3 Ra5
                = shift_bits_left
                    (add_vec zero_reg (sign_extend' 64
                       (sign_extend' 12 (mword_of_int 63 : mword 6))))
                    (subrange_vec_dec (mword_of_int 63 : mword 6)
                       (Z.sub log2_xlen 1) 0)).
      { rgne. rewrite /S3 upd_eq. rgne. rewrite /S2 upd_eq. reflexivity. }
      rewrite HS3a0 HS3a5. unfold kvi_satp_word. reflexivity. }
    iApply (wp_cor_s_sconf (mword_of_int (UT + 0xba)) Ra0 Ra0 Ra5
              (kvi_satp_word (ud_root (pv_upt V))) S3 (trap_res b + nx)%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok) Hor
              with "Hcg Hpc Hiba [-]").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    set (S4 := <[Regidx Ra0 := regval_into_reg
                   (kvi_satp_word (ud_root (pv_upt V)))]> S3).
    change (<[Regidx Ra0 := regval_into_reg
               (kvi_satp_word (ud_root (pv_upt V)))]> S3) with S4.
    assert (Hpbc : add_vec_int (mword_of_int (UT + 0xba) : mword 64) 2
                   = mword_of_int (UT + 0xbc)) by pcw.
    iEval (rewrite Hpbc) in "Hpc".
    (* the cell back in the block's own spelling -- the load left it in the
       leaf's [add_vec (rget ...) imm] form *)
    iEval (rewrite Haddrpg) in "Hpgt".
    iDestruct ("Hpvback" $! (pv_upt V) ltac:(apply uptd_ext_sz_refl)
                 with "Hsz Hpgt Hppt") as "Hpv".
    rewrite upd_upt_id.
    (* ---- +0xbc .. +0xc2: the four restores ---- *)
    iDestruct "Hframe" as "(Hbra & Hbs0 & Hbs1 & Hbs2)".
    assert (HS4sp : S4 !!! Regidx csp_rs1 = pa_stk ksp 4).
    { rewrite /S4 upd_ne; [| reg_neq]. rewrite /S3 upd_ne; [| reg_neq].
      rewrite /S2 upd_ne; [| reg_neq]. rewrite /S1 upd_ne; [| reg_neq].
      rewrite /S0 upd_ne; [| reg_neq]. exact Hmfsp. }
    assert (Hp1 : add_vec (S4 !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000")))
                  = pa_stk ksp 1).
    { rewrite HS4sp. apply stk_frm. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite -Hp1) in "Hbra".
    iApply (wp_cldsp_s_sconf (mword_of_int (UT + 0xbc)) (mword_of_int 3 : mword 6)
              Rra S4 (trap_res b + nx)%nat (m0 !!! Regidx Rra) false
              (dqm := DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hibc Hbra [-]").
    iApply wp_next_off_intro. iIntros "Hcg Hpc Hbra".
    set (S5 := <[Regidx Rra := regval_into_reg (m0 !!! Regidx Rra)]> S4).
    change (<[Regidx Rra := regval_into_reg (m0 !!! Regidx Rra)]> S4) with S5.
    assert (Hpbe : add_vec_int (mword_of_int (UT + 0xbc) : mword 64) 2
                   = mword_of_int (UT + 0xbe)) by pcw.
    iEval (rewrite Hpbe) in "Hpc".
    assert (HS5sp : S5 !!! Regidx csp_rs1 = pa_stk ksp 4)
      by (rewrite /S5 upd_ne; [exact HS4sp | reg_neq]).
    assert (Hp2 : add_vec (S5 !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000")))
                  = pa_stk ksp 2).
    { rewrite HS5sp. apply stk_frm. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite -Hp2) in "Hbs0".
    iApply (wp_cldsp_s_sconf (mword_of_int (UT + 0xbe)) (mword_of_int 2 : mword 6)
              Rs0 S5 (trap_res b + nx)%nat (m0 !!! Regidx Rs0) false
              (dqm := DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hibe Hbs0 [-]").
    iApply wp_next_off_intro. iIntros "Hcg Hpc Hbs0".
    set (S6 := <[Regidx Rs0 := regval_into_reg (m0 !!! Regidx Rs0)]> S5).
    change (<[Regidx Rs0 := regval_into_reg (m0 !!! Regidx Rs0)]> S5) with S6.
    assert (Hpc0 : add_vec_int (mword_of_int (UT + 0xbe) : mword 64) 2
                   = mword_of_int (UT + 0xc0)) by pcw.
    iEval (rewrite Hpc0) in "Hpc".
    assert (HS6sp : S6 !!! Regidx csp_rs1 = pa_stk ksp 4)
      by (rewrite /S6 upd_ne; [exact HS5sp | reg_neq]).
    assert (Hp3 : add_vec (S6 !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000")))
                  = pa_stk ksp 3).
    { rewrite HS6sp. apply stk_frm. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite -Hp3) in "Hbs1".
    iApply (wp_cldsp_s_sconf (mword_of_int (UT + 0xc0)) (mword_of_int 1 : mword 6)
              Rs1 S6 (trap_res b + nx)%nat (m0 !!! Regidx Rs1) false
              (dqm := DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hic0 Hbs1 [-]").
    iApply wp_next_off_intro. iIntros "Hcg Hpc Hbs1".
    set (S7 := <[Regidx Rs1 := regval_into_reg (m0 !!! Regidx Rs1)]> S6).
    change (<[Regidx Rs1 := regval_into_reg (m0 !!! Regidx Rs1)]> S6) with S7.
    assert (Hpc2 : add_vec_int (mword_of_int (UT + 0xc0) : mword 64) 2
                   = mword_of_int (UT + 0xc2)) by pcw.
    iEval (rewrite Hpc2) in "Hpc".
    assert (HS7sp : S7 !!! Regidx csp_rs1 = pa_stk ksp 4)
      by (rewrite /S7 upd_ne; [exact HS6sp | reg_neq]).
    assert (Hp4 : add_vec (S7 !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000")))
                  = pa_stk ksp 4).
    { rewrite HS7sp. apply stk_frm. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite -Hp4) in "Hbs2".
    iApply (wp_cldsp_s_sconf (mword_of_int (UT + 0xc2)) (mword_of_int 0 : mword 6)
              Rs2 S7 (trap_res b + nx)%nat (m0 !!! Regidx Rs2) false
              (dqm := DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hic2 Hbs2 [-]").
    iApply wp_next_off_intro. iIntros "Hcg Hpc Hbs2".
    set (S8 := <[Regidx Rs2 := regval_into_reg (m0 !!! Regidx Rs2)]> S7).
    change (<[Regidx Rs2 := regval_into_reg (m0 !!! Regidx Rs2)]> S7) with S8.
    assert (Hpc4 : add_vec_int (mword_of_int (UT + 0xc2) : mword 64) 2
                   = mword_of_int (UT + 0xc4)) by pcw.
    iEval (rewrite Hpc4) in "Hpc".
    (* ---- +0xc4: c.addi16sp sp,32 -- the frame traded back ---- *)
    assert (HS8sp : S8 !!! Regidx csp_rs1 = pa_stk ksp 4)
      by (rewrite /S8 upd_ne; [exact HS7sp | reg_neq]).
    assert (Hwv : add_vec (S8 !!! Regidx csp_rs1)
                    (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6)))
                  = ksp) by (rewrite HS8sp; apply stk_pop_32).
    assert (Hpop : S8 !!! Regidx csp_rs1
                   = pa_stk (add_vec (S8 !!! Regidx csp_rs1)
                       (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6)))) 4)
      by (rewrite Hwv HS8sp; reflexivity).
    (* each load handed its word back in the LEAF's address spelling; put the
       four back in [pa_stk]'s so they re-assemble into the frame *)
    iEval (rewrite Hp1) in "Hbra".
    iEval (rewrite Hp2) in "Hbs0".
    iEval (rewrite Hp3) in "Hbs1".
    iEval (rewrite Hp4) in "Hbs2".
    iAssert (stack_own ksp 4) with "[Hbra Hbs0 Hbs1 Hbs2]" as "Hfr".
    { iApply (stack_own_4_intro ksp with "Hbra Hbs0 Hbs1 Hbs2"). }
    iEval (rewrite -Hwv) in "Hfr".
    iApply (wp_caddi16sp_pop_s_sconf (mword_of_int (UT + 0xc4))
              (mword_of_int 2 : mword 6) S8 (trap_res b + nx)%nat 4 false Hpop
              with "Hcg Hpc Hic4 Hfr [-]").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    iEval (rewrite Hwv) in "Hcg".
    set (S9 := <[Regidx csp_rs1 := regval_into_reg ksp]> S8).
    change (<[Regidx csp_rs1 := regval_into_reg ksp]> S8) with S9.
    assert (Havn : ((trap_res b + nx) + 4)%nat = av) by lia.
    iEval (rewrite Havn) in "Hcg".
    assert (Hpc6 : add_vec_int (mword_of_int (UT + 0xc4) : mword 64) 2
                   = mword_of_int (UT + 0xc6)) by pcw.
    iEval (rewrite Hpc6) in "Hpc".
    (* ---- +0xc6: c.jr ra ---- *)
    assert (HS9ra : rget S9 Rra = m0 !!! Regidx Rra).
    { rgne. rewrite /S9 upd_ne; [| reg_neq]. rewrite /S8 upd_ne; [| reg_neq].
      rewrite /S7 upd_ne; [| reg_neq]. rewrite /S6 upd_ne; [| reg_neq].
      rewrite /S5 upd_eq. reflexivity. }
    iApply (wp_cret_s_sconf (mword_of_int (UT + 0xc6)) Rra S9 av false
              ltac:(vm_compute; discriminate) with "Hcg Hpc Hic6 [-]").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    iEval (rewrite HS9ra) in "Hpc".
    (* ================================================================== *)
    (*  THE EXIT: the payload back into the boundary's pieces.             *)
    (* ================================================================== *)
    iDestruct (sie_cap_gpr_split with "Hcg") as "(Hhs & Hsc & Hcap & Hfile)".
    (* [sconf] is destructured DIRECTLY here -- not via [sconf_priv_open],
       whose closer would re-park [mie]/[mideleg]/[menvcfg] rather than
       hand them out loose (see [ut_trap]'s header comment). *)
    iDestruct "Hsc" as "(_ & _ & Hpriv & Hmsx & Hmiex & Hmenvx)".
    iDestruct "Hmsx" as (msg) "Hmsown".
    iDestruct (ut_exit_ms_ok msg with "Hmsown Hsret Hq4") as %Hretms2.
    iDestruct "Hmsown" as "(Hms & Hhalf & Htie & %Hmsg)".
    iDestruct (sret_bits_agree _ _ _ _ with "Htie Hsret") as %[Hspp2 Hspie2].
    iDestruct (ghost_var_agree with "Hhalf Hq4") as %Hsie2.
    rewrite /sret_tie Hspp2 Hspie2.
    rewrite Hsie2.
    (* [mie]/[menvcfg]: each pinned to its unique constant, so the exit
       value provably equals what [ut_trap_open] was handed at entry.
       [mideleg]: a fresh witness, handed to [Hcont] as-is (see
       [usertrap_post]'s comment). *)
    iDestruct "Hmiex" as (mdv0) "(Hmie & Hmdl & %Hmaskx)".
    subst mie_v.
    iDestruct "Hmenvx" as (menvcfg0') "(Hmenv & _ & _ & _ & _ & %Hmeq)".
    subst menvcfg0' menvcfg0.
    (* [mf'] IS [tp_pin S9]: usertrap may have MIGRATED, so the tp SLOT of the
       map it threaded still holds the ENTRY hart's id while [gpr_file] holds
       the pinned one.  Handing over the pinned map makes the boundary's
       [mf !!! tp = cid_word] hold by construction, and tp is deliberately not
       one of [callee_saved]'s thirteen. *)
    assert (HcsS9 : ut_cs m0 S9).
    { rewrite /S9 /S8 /S7 /S6 /S5 /S4 /S3 /S2 /S1 /S0.
      apply ut_cs_insert4; [by left |].
      apply ut_cs_insert4; [by right; right; right |].
      apply ut_cs_insert4; [by right; right; left |].
      apply ut_cs_insert4; [by right; left |].
      apply ut_cs_insert; [vm_compute; reflexivity |].
      apply ut_cs_insert; [vm_compute; reflexivity |].
      apply ut_cs_insert; [vm_compute; reflexivity |].
      apply ut_cs_insert; [vm_compute; reflexivity |].
      apply ut_cs_insert; [vm_compute; reflexivity |].
      apply ut_cs_insert; [vm_compute; reflexivity |].
      exact Hcs. }
    assert (HcsF : callee_saved m0 S9).
    { apply (ut_cs_to_callee_saved m0 S9 HcsS9).
      - rewrite /S9 upd_eq Hm0sp. reflexivity.
      - rewrite /S9 upd_ne; [| reg_neq]. rewrite /S8 upd_ne; [| reg_neq].
        rewrite /S7 upd_ne; [| reg_neq]. rewrite /S6 upd_eq. reflexivity.
      - rewrite /S9 upd_ne; [| reg_neq]. rewrite /S8 upd_ne; [| reg_neq].
        rewrite /S7 upd_eq. reflexivity.
      - rewrite /S9 upd_ne; [| reg_neq]. rewrite /S8 upd_eq. reflexivity. }
    assert (HcsP : callee_saved m0 (tp_pin S9)).
    { rewrite /tp_pin.
      apply (callee_saved_insert_r Rtp _ m0 S9 ltac:(vm_compute; reflexivity) HcsF). }
    assert (Htpid : tp_pin S9 !!! Regidx Rtp = cid_word)
      by (rewrite /tp_pin upd_eq; reflexivity).
    assert (Hmfa0 : tp_pin S9 !!! Regidx Ra0
                    = kvi_satp_word (ud_root (pv_upt V))).
    { rewrite /tp_pin upd_ne; [| reg_neq]. rewrite /S9 upd_ne; [| reg_neq].
      rewrite /S8 upd_ne; [| reg_neq]. rewrite /S7 upd_ne; [| reg_neq].
      rewrite /S6 upd_ne; [| reg_neq]. rewrite /S5 upd_ne; [| reg_neq].
      rewrite /S4 upd_eq. reflexivity. }
    destruct Hptwf as (Hmapwf & Haccwf & _ & _ & _).
    iDestruct "Hscause" as (scv) "Hscause".
    iDestruct "Hstval" as (stv) "Hstval".
    iSpecialize ("Hcont" $! CID with "[%]"); [intros _; reflexivity|].
    iDestruct ("Hownback" $! V with "Hpv Hsy") as "Hown".
    iApply ("Hcont" $! (pv_upt V) (tp_pin S9) msg
              (kvi_satp_word (ud_root (pv_upt V))) (mepc_val uepc) scv stv mdv0
              with "[%] [%] [%] [%] [%] [%] [%] [%] [%] [%]
                    Hhs Hpriv Hms Hscause Hstval Hsepc [Hstvec] Hpc [Hfile]
                    Hmie Hmdl Hmenv [-]").
    - exact Hmaskx.
    - exact Htfpe.
    - exact Haccwf.
    - exact Hmapwf.
    - exact Hretms2.
    - exact Hmsg.
    - exact HcsP.
    - exact Htpid.
    - exact Hmfa0.
    - split_and!; [exact (kvi_satp_mode _) | exact (kvi_satp_asid _)
                  | exact (kvi_satp_ppn _)].
    - rewrite /uservec_tvec. iExact "Hstvec".
    - (* the boundary asks for [gpr_file mf] and [mf] IS [tp_pin S9], so this
         is what [sie_cap_gpr] was holding all along -- no [tp_pin_id] step. *)
      iExact "Hfile".
    - (* [ut_res] rebuilt at the exit hart *)
      iExists N, V, av, C.
      iSplitR; [iPureIntro; reflexivity|].
      iSplitR; [iPureIntro; exact Hksp|].
      iSplitR; [iPureIntro; exact (conj Hj (conj Hjl (conj Hlen Hlg)))|].
      iSplitR; [iPureIntro; exact Hav|].
      (* the mstatus and privilege CELLS, and now [mie]/[mideleg]/[menvcfg]
         too, are NOT in [ut_trap]: they go to the boundary raw (above). *)
      iSplitL "Hcap Hhalf Htie Hq4 Hkptr Hsret Hcpu Hclm".
      + rewrite /ut_trap /ut_stack /ut_ghosts.
        iDestruct "Hcap" as "(Hstk & Hstr & Harm)".
        iSplitL "Hstk". { rewrite /S9 upd_eq. iExact "Hstk". }
        iSplitL "Hstr". { iExact "Hstr". }
        iSplitL "Harm". { iExact "Harm". }
        iSplitL "Hkptr". { iExact "Hkptr". }
        iSplitL "Hhalf Hq4 Htie Hsret".
        { iSplitL "Hhalf". { iExact "Hhalf". }
          iSplitL "Hq4". { iExact "Hq4". }
          iSplitL "Htie". { iExact "Htie". }
          iExact "Hsret". }
        iSplitL "Hcpu". { iEval (rewrite Hlkempty) in "Hcpu". iExact "Hcpu". }
        iExact "Hclm".
      + rewrite /ut_env. iSplitR; [iExact "Hcaps"|]. iExact "Hown".
  Qed.

End UtRet2.

Section UtRet.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !bioG Σ,
            !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ, !fsCrashG Σ,
            !kallocG Σ, !irefslotG Σ, !iregG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.
  Context (Rsys : gname -> mword 64 -> iProp Σ).

  (* ==================================================================== *)
  (* +0xae: jal prepare_return, then the second half at ITS hart.          *)
  (* ==================================================================== *)
  Lemma ut_ret (N : ut_names) (V : pprivate) (pt : uptd) (ksp : mword 64)
      (m0 m : regfile) (av nx : nat) (C : iProp Σ) (b : bool)
      (mie_v menvcfg0 : mword 64) (lks : gset nat) :
    ut_wf N ->
    (K_usertrap <= av)%nat ->
    (trap_res b + nx)%nat = (av - 4)%nat ->
    ud_tfp (pv_upt V) = ud_tfp pt ->
    add_vec (un_ks N) (mword_of_int 4096) = ksp ->
    m0 !!! Regidx csp_rs1 = ksp ->
    m !!! Regidx csp_rs1 = pa_stk ksp 4 ->
    m !!! Regidx Rs1 = un_pj N ->
    ut_cs m0 m ->
    mie_v = MIE_S ->
    menvcfg0 = MENVCFG_S ->
    kernel_text -∗
    pc_is (mword_of_int (UT + 0xae)) -∗
    sie_cap_gpr m nx b (un_pj N) -∗
    ut_hold Rsys N V C b lks -∗
    ut_frame ksp (m0 !!! Regidx Rra) (m0 !!! Regidx Rs0)
                 (m0 !!! Regidx Rs1) (m0 !!! Regidx Rs2) -∗
    wp_next true (un_pj N)
      (fun CID' => usertrap_post (CID := CID') (ut_res (CID := CID') Rsys) pt ksp m0
                     mie_v menvcfg0) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hwf Hav Hnx Htfpe Hksp Hm0sp Hmsp Hms1 Hcs Hmiev Hmenvv.
    pose proof (ut_nx_bound b av nx Hav Hnx) as Hks.
    unfold K_syscall, K_sys_exit, K_kexit in Hks.
    pose proof Hwf as Hwf'. destruct Hwf as (Hj & Hjl & Hlen & Hlg).
    iIntros "#Htext Hpc Hcg Hhold Hframe Hcont".
    iPoseProof (uti_0ae with "Htext") as "Hiae".
    iDestruct "Hhold" as "(Hcpu & Hcsrs & Hclm & [#Hcaps Hown])".
    iDestruct (ut_own_priv with "Hown") as "(Hpv & Hsy & Hownback)".
    iDestruct (ut_epc_exists with "Hpv") as %Hepcx.
    destruct Hepcx as [uepc Hepc].
    iAssert (is_kstack (un_pj N) (un_ks N)) with "[]" as "#Hkst".
    { iDestruct "Hcaps" as "(_ & _ & _ & #H & _)". iExact "H". }
    (* ---- +0xae: jal prepare_return ---- *)
    iApply (wp_jal_s_sconf (mword_of_int (UT + 0xae)) Rra
              (mword_of_int 2096658 : mword 21) m nx b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(vm_compute; reflexivity) with "Hcg Hpc Hiae [-]").
    iIntros (CID1 Hk1) "Hcg Hpc".
    set (M1 := <[Regidx Rra := regval_into_reg
                   (add_vec_int (mword_of_int (UT + 0xae) : mword 64) 4)]> m).
    change (<[Regidx Rra := regval_into_reg
               (add_vec_int (mword_of_int (UT + 0xae) : mword 64) 4)]> m) with M1.
    assert (Hentry : add_vec (mword_of_int (UT + 0xae) : mword 64)
                       (sign_extend' 64 (mword_of_int 2096658 : mword 21))
                     = mword_of_int KernelSyms.prepare_return) by pcw.
    iEval (rewrite Hentry) in "Hpc".
    assert (HM1sp : M1 !!! Regidx csp_rs1 = pa_stk ksp 4)
      by (rewrite /M1 upd_ne; [exact Hmsp | reg_neq]).
    assert (HM1s1 : M1 !!! Regidx Rs1 = un_pj N)
      by (rewrite /M1 upd_ne; [exact Hms1 | reg_neq]).
    assert (HM1ra : M1 !!! Regidx Rra = mword_of_int (UT + 0xb2))
      by (rewrite /M1 upd_eq; pcw).
    assert (HcsM1 : ut_cs m0 M1)
      by (rewrite /M1; apply ut_cs_insert; [vm_compute; reflexivity | exact Hcs]).
    iDestruct (cpu_own_transport CID CID1 0%nat b (un_pj N) C b
                 ltac:(wp_next_chain) with "Hcpu") as "Hcpu".
    iDestruct (trap_csrs_ext_transport CID CID1 b (un_pj N)
                 ltac:(wp_next_chain) with "Hcsrs") as "Hcsrs".
    iApply (PR.wp_prepare_return_sconf (un_f N) (un_ks N) (un_pid N) V
              M1 nx C (un_pj N) uepc b lks ltac:(unfold K_prepare_return; lia) Hepc
              with "Hcg Hcpu Hcsrs Htext Hpc Hkst Hpv [-]").
    iIntros (CIDp Hkp mf ksat kroot vb)
      "%Hcspr %Hmode %Hasid %Hppn Hcg Hcpu Hclmpay Hsepc Hscause Hstval
       Hsret Hstvec Hq4 Hkptr Hpv Hpc".
    assert (Hpc0b2 : ret_pc (M1 !!! Regidx Rra) = mword_of_int (UT + 0xb2))
      by (rewrite HM1ra; pcw).
    iEval (rewrite Hpc0b2) in "Hpc".
    (* THE CLAIM, REJOINED -- [IntrDefs.cpu_claim_ext_split] is the seam: at
       [b = false] we kept our own and prepare_return's payout is [emp], at
       [b = true] the arm owned it and the [intr_off] has just handed it over. *)
    iDestruct (cpu_claim_ext_transport CID CIDp b (un_pj N)
                 ltac:(wp_next_chain) with "Hclm") as "Hclm".
    iAssert (cpu_claim (CID := CIDp) (un_pj N)) with "[Hclmpay Hclm]" as "Hclm".
    { rewrite -(cpu_claim_ext_split (CID := CIDp) b (un_pj N)).
      iSplitL "Hclmpay"; [iExact "Hclmpay" | iExact "Hclm"]. }
    iDestruct (wp_next_retarget CID CIDp true (un_pj N) _
                 ltac:(wp_next_chain) with "Hcont") as "Hcont".
    set (Vr := upd_tf V (prepare_return_tf (pv_tf V) ksat
                           (add_vec (un_ks N) (mword_of_int 4096)) (cid_word (CID := CIDp)))).
    change (upd_tf V (prepare_return_tf (pv_tf V) ksat
              (add_vec (un_ks N) (mword_of_int 4096)) (cid_word (CID := CIDp)))) with Vr.
    assert (HVrupt : pv_upt Vr = pv_upt V) by (rewrite /Vr; destruct V; reflexivity).
    iDestruct ("Hownback" $! Vr with "Hpv Hsy") as "Hown".
    iApply (ut_ret2 (CID := CIDp) Rsys N Vr pt ksp m0 mf av nx C b uepc vb
              mie_v menvcfg0 lks
              Hwf' Hav Hnx ltac:(rewrite HVrupt; exact Htfpe) Hksp Hm0sp
              ltac:(rewrite (callee_saved_lookup Hcspr csp_rs1
                              ltac:(vm_compute; reflexivity)); exact HM1sp)
              ltac:(rewrite (callee_saved_lookup Hcspr Rs1
                              ltac:(vm_compute; reflexivity)); exact HM1s1)
              ltac:(exact (ut_cs_trans m0 M1 mf HcsM1
                             (ut_cs_of_callee_saved _ _ Hcspr)))
              Hmiev Hmenvv
              with "Htext Hpc Hcg Hcpu Hclm Hsepc Hscause Hstval Hsret Hstvec
                    Hq4 Hkptr [Hown] Hframe Hcont").
    rewrite /ut_env. iSplitR; [iExact "Hcaps" | iExact "Hown"].
  Qed.

End UtRet.

Section UtA6.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !bioG Σ,
            !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ, !fsCrashG Σ,
            !kallocG Σ, !irefslotG Σ, !iregG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.
  Context (Rsys : gname -> mword 64 -> iProp Σ).

  (* ==================================================================== *)
  (* +0xa6:  if (killed(p)) { which_dev = 0; kexit(-1); }                  *)
  (* ==================================================================== *)
  (* The rejoin every arm reaches, at [b = true] from the syscall arm and at
     [b = false] from the other three.  [which_dev = 0] before the kexit is
     dead code in the resource sense -- kexit never returns -- so the [c.li
     s2,0] is stepped and its value never read again. *)
  Lemma ut_a6 (N : ut_names) (V : pprivate) (pt : uptd) (ksp : mword 64)
      (m0 m : regfile) (av nx : nat) (C : iProp Σ) (b : bool)
      (mie_v menvcfg0 : mword 64) (lks : gset nat) :
    ut_wf N ->
    (K_usertrap <= av)%nat ->
    (trap_res b + nx)%nat = (av - 4)%nat ->
    ud_tfp (pv_upt V) = ud_tfp pt ->
    add_vec (un_ks N) (mword_of_int 4096) = ksp ->
    m0 !!! Regidx csp_rs1 = ksp ->
    m !!! Regidx csp_rs1 = pa_stk ksp 4 ->
    m !!! Regidx Rs1 = un_pj N ->
    ut_cs m0 m ->
    mie_v = MIE_S ->
    menvcfg0 = MENVCFG_S ->
    (* the block's whole cone bottoms out at "ftable" (1), via the killed
       branch's [ut_kexit]; killed itself (rank "proc" = 11) follows by
       [locks_below_mono].  The not-killed branch (ut_ret / prepare_return)
       touches no lock at all. *)
    locks_below lks (lock_rank "log") ->
    kernel_text -∗
    pc_is (mword_of_int (UT + 0xa6)) -∗
    sie_cap_gpr m nx b (un_pj N) -∗
    ut_hold Rsys N V C b lks -∗
    ut_frame ksp (m0 !!! Regidx Rra) (m0 !!! Regidx Rs0)
                 (m0 !!! Regidx Rs1) (m0 !!! Regidx Rs2) -∗
    wp_next true (un_pj N)
      (fun CID' => usertrap_post (CID := CID') (ut_res (CID := CID') Rsys) pt ksp m0
                     mie_v menvcfg0) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hwf Hav Hnx Htfpe Hksp Hm0sp Hmsp Hms1 Hcs Hmiev Hmenvv Hbelow.
    pose proof (ut_nx_bound b av nx Hav Hnx) as Hks.
    unfold K_syscall, K_sys_exit, K_kexit in Hks.
    pose proof Hwf as Hwf'. destruct Hwf as (Hj & Hjl & Hlen & Hlg).
    iIntros "#Htext Hpc Hcg Hhold Hframe Hcont".
    iPoseProof (uti_0a6 with "Htext") as "Hia6".
    iPoseProof (uti_0a8 with "Htext") as "Hia8".
    iDestruct "Hhold" as "(Hcpu & Hcsrs & Hclm & [#Hcaps Hown])".
    iAssert (procs_inv (un_s N)) with "[]" as "#Hpi".
    { iDestruct "Hcaps" as "($ & _)". }
    iAssert (panic_wp_any) with "[]" as "#Hpa".
    { iDestruct "Hcaps" as "(_ & $ & _)". }
    (* ---- +0xa6: c.mv a0,s1 ---- *)
    iApply (wp_cmv_s_sconf (mword_of_int (UT + 0xa6)) Ra0 Rs1 m nx b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hia6 [-]").
    iIntros (CID1 Hk1) "Hcg Hpc".
    set (M1 := <[Regidx Ra0 := regval_into_reg (add_vec zero_reg (rget m Rs1))]> m).
    change (<[Regidx Ra0 := regval_into_reg (add_vec zero_reg (rget m Rs1))]> m)
      with M1.
    assert (Hppa8 : add_vec_int (mword_of_int (UT + 0xa6) : mword 64) 2
                    = mword_of_int (UT + 0xa8)) by pcw.
    iEval (rewrite Hppa8) in "Hpc".
    assert (HM1a0 : M1 !!! Regidx Ra0 = proc_addr (un_j N)).
    { rewrite /M1 upd_eq. rewrite (rget_ne (CID := CID) m Rs1
        ltac:(intro Hbad; injection Hbad as Hb2; vm_compute in Hb2; congruence)).
      rewrite Hms1 add_vec_zero_l. reflexivity. }
    assert (HM1sp : M1 !!! Regidx csp_rs1 = pa_stk ksp 4)
      by (rewrite /M1 upd_ne; [exact Hmsp | reg_neq]).
    assert (HM1s1 : M1 !!! Regidx Rs1 = un_pj N)
      by (rewrite /M1 upd_ne; [exact Hms1 | reg_neq]).
    assert (HcsM1 : ut_cs m0 M1)
      by (rewrite /M1; apply ut_cs_insert; [vm_compute; reflexivity | exact Hcs]).
    (* ---- +0xa8: jal killed ---- *)
    iApply (wp_jal_s_sconf (CID := CID1) (mword_of_int (UT + 0xa8)) Rra
              (mword_of_int 2095870 : mword 21) M1 nx b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(vm_compute; reflexivity) with "Hcg Hpc Hia8 [-]").
    iIntros (CID2 Hk2) "Hcg Hpc".
    set (M2 := <[Regidx Rra := regval_into_reg
                   (add_vec_int (mword_of_int (UT + 0xa8) : mword 64) 4)]> M1).
    change (<[Regidx Rra := regval_into_reg
               (add_vec_int (mword_of_int (UT + 0xa8) : mword 64) 4)]> M1) with M2.
    assert (Hkilled : add_vec (mword_of_int (UT + 0xa8) : mword 64)
                        (sign_extend' 64 (mword_of_int 2095870 : mword 21))
                      = mword_of_int KernelSyms.killed) by pcw.
    iEval (rewrite Hkilled) in "Hpc".
    assert (HM2a0 : M2 !!! Regidx Ra0 = proc_addr (un_j N))
      by (rewrite /M2 upd_ne; [exact HM1a0 | reg_neq]).
    assert (HM2sp : M2 !!! Regidx csp_rs1 = pa_stk ksp 4)
      by (rewrite /M2 upd_ne; [exact HM1sp | reg_neq]).
    assert (HM2s1 : M2 !!! Regidx Rs1 = un_pj N)
      by (rewrite /M2 upd_ne; [exact HM1s1 | reg_neq]).
    assert (HM2ra : M2 !!! Regidx Rra = mword_of_int (UT + 0xac))
      by (rewrite /M2 upd_eq; pcw).
    assert (HcsM2 : ut_cs m0 M2)
      by (rewrite /M2; apply ut_cs_insert; [vm_compute; reflexivity | exact HcsM1]).
    iDestruct (cpu_own_transport CID CID2 0%nat b (un_pj N) C b
                 ltac:(wp_next_chain) with "Hcpu") as "Hcpu".
    iApply (KI.wp_killed_sconf (CID := CID2) (un_s N) (un_j N) (un_l N)
              M2 nx 0%nat b (un_pj N) C b lks
              HM2a0 Hj Hjl ltac:(vm_compute; reflexivity) ltac:(lia)
              ltac:(lkbelow)
              with "Hcg Hcpu Htext Hpc Hpi Hpa [-]").
    all: try lkbelow.
    iIntros (CID3 Hk3 mf kl) "[%Hcskl %Hkla0] Hcg Hcpu Hpc".
    assert (Hretac : ret_pc (M2 !!! Regidx Rra) = mword_of_int (UT + 0xac))
      by (rewrite HM2ra; pcw).
    iEval (rewrite Hretac) in "Hpc".
    (* the two arm complements and the exit, moved to killed's resuming hart *)
    iDestruct (trap_csrs_ext_transport CID CID3 b (un_pj N)
                 ltac:(wp_next_chain) with "Hcsrs") as "Hcsrs".
    iDestruct (cpu_claim_ext_transport CID CID3 b (un_pj N)
                 ltac:(wp_next_chain) with "Hclm") as "Hclm".
    iDestruct (wp_next_retarget CID CID3 true (un_pj N) _
                 ltac:(wp_next_chain) with "Hcont") as "Hcont".
    assert (Hmfsp : mf !!! Regidx csp_rs1 = pa_stk ksp 4)
      by (rewrite (callee_saved_lookup Hcskl csp_rs1
                     ltac:(vm_compute; reflexivity)); exact HM2sp).
    assert (Hmfs1 : mf !!! Regidx Rs1 = un_pj N)
      by (rewrite (callee_saved_lookup Hcskl Rs1
                     ltac:(vm_compute; reflexivity)); exact HM2s1).
    assert (Hcsmf : ut_cs m0 mf)
      by exact (ut_cs_trans m0 M2 mf HcsM2 (ut_cs_of_callee_saved _ _ Hcskl)).
    iPoseProof (uti_0ac with "Htext") as "Hiac".
    assert (Hc2 : creg2reg_idx (Cregidx (mword_of_int 2)) = Regidx Ra0)
      by (vm_compute; reflexivity).
    assert (Hrgmf : rget (CID := CID3) mf Ra0 = sign_extend' 64 kl).
    { rewrite (rget_ne (CID := CID3) mf Ra0
        ltac:(intro Hbad; injection Hbad as Hb2; vm_compute in Hb2; congruence)).
      exact Hkla0. }
    (* ---- +0xac: c.bnez a0 ---- *)
    destruct (neq_vec (sign_extend' 64 kl) (zero_reg : mword 64)) eqn:Hnz.
    - (* KILLED: [which_dev = 0; kexit(-1)] -- a dead end. *)
      iPoseProof (uti_0f4 with "Htext") as "Hif4".
      iPoseProof (uti_0f6 with "Htext") as "Hif6".
      iPoseProof (uti_0f8 with "Htext") as "Hif8".
      iApply (wp_cbnez_taken_s_sconf (CID := CID3) (mword_of_int (UT + 0xac))
                (mword_of_int 36 : mword 8) (Cregidx (mword_of_int 2)) Ra0
                mf nx b Hc2 ltac:(vm_compute; discriminate)
                ltac:(rewrite Hrgmf; exact Hnz) ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hiac [-]").
      iNext. iIntros (CID4 Hk4) "Hcg Hpc".
      assert (Hpf4 : add_vec (mword_of_int (UT + 0xac) : mword 64)
                       (sign_extend' 64 (sign_extend' 13
                          (concat_vec (mword_of_int 36 : mword 8) ('b"0"))))
                     = mword_of_int (UT + 0xf4)) by pcw.
      iEval (rewrite Hpf4) in "Hpc".
      (* +0xf4 c.li s2,0 *)
      iApply (wp_cli_s_sconf (CID := CID4) (mword_of_int (UT + 0xf4)) Rs2
                (mword_of_int 0 : mword 6)
                (add_vec zero_reg (sign_extend' 64
                   (sign_extend' 12 (mword_of_int 0 : mword 6))))
                mf nx b ltac:(vm_compute; discriminate) ltac:(rdok) eq_refl
                with "Hcg Hpc Hif4 [-]").
      iIntros (CID5 Hk5) "Hcg Hpc".
      set (K1 := <[Regidx Rs2 := regval_into_reg
                     (add_vec zero_reg (sign_extend' 64
                        (sign_extend' 12 (mword_of_int 0 : mword 6))))]> mf).
      change (<[Regidx Rs2 := regval_into_reg
                 (add_vec zero_reg (sign_extend' 64
                    (sign_extend' 12 (mword_of_int 0 : mword 6))))]> mf) with K1.
      assert (Hpf6 : add_vec_int (mword_of_int (UT + 0xf4) : mword 64) 2
                     = mword_of_int (UT + 0xf6)) by pcw.
      iEval (rewrite Hpf6) in "Hpc".
      (* +0xf6 c.li a0,-1 *)
      iApply (wp_cli_s_sconf (CID := CID5) (mword_of_int (UT + 0xf6)) Ra0
                (mword_of_int 63 : mword 6)
                (add_vec zero_reg (sign_extend' 64
                   (sign_extend' 12 (mword_of_int 63 : mword 6))))
                K1 nx b ltac:(vm_compute; discriminate) ltac:(rdok) eq_refl
                with "Hcg Hpc Hif6 [-]").
      iIntros (CID6 Hk6) "Hcg Hpc".
      set (K2 := <[Regidx Ra0 := regval_into_reg
                     (add_vec zero_reg (sign_extend' 64
                        (sign_extend' 12 (mword_of_int 63 : mword 6))))]> K1).
      change (<[Regidx Ra0 := regval_into_reg
                 (add_vec zero_reg (sign_extend' 64
                    (sign_extend' 12 (mword_of_int 63 : mword 6))))]> K1) with K2.
      assert (Hpf8 : add_vec_int (mword_of_int (UT + 0xf6) : mword 64) 2
                     = mword_of_int (UT + 0xf8)) by pcw.
      iEval (rewrite Hpf8) in "Hpc".
      (* +0xf8 jal kexit *)
      iApply (wp_jal_s_sconf (CID := CID6) (mword_of_int (UT + 0xf8)) Rra
                (mword_of_int 2095486 : mword 21) K2 nx b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                ltac:(vm_compute; reflexivity) with "Hcg Hpc Hif8 [-]").
      iIntros (CID7 Hk7) "Hcg Hpc".
      assert (Hkex : add_vec (mword_of_int (UT + 0xf8) : mword 64)
                       (sign_extend' 64 (mword_of_int 2095486 : mword 21))
                     = mword_of_int KernelSyms.kexit) by pcw.
      iEval (rewrite Hkex) in "Hpc".
      iDestruct (cpu_own_transport CID3 CID7 0%nat b (un_pj N) C b
                   ltac:(wp_next_chain) with "Hcpu") as "Hcpu".
      iDestruct (trap_csrs_ext_transport CID3 CID7 b (un_pj N)
                   ltac:(wp_next_chain) with "Hcsrs") as "Hcsrs".
      iDestruct (cpu_claim_ext_transport CID3 CID7 b (un_pj N)
                   ltac:(wp_next_chain) with "Hclm") as "Hclm".
      iApply (ut_kexit (CID := CID7) Rsys N V
                (<[Regidx Rra := regval_into_reg
                     (add_vec_int (mword_of_int (UT + 0xf8) : mword 64) 4)]> K2)
                nx C b lks Hwf' ltac:(unfold K_kexit; lia) ltac:(lkbelow)
                with "Htext Hpc Hcg [-]").
      rewrite /ut_hold. iSplitL "Hcpu"; [iExact "Hcpu"|].
      iSplitL "Hcsrs"; [iExact "Hcsrs"|].
      iSplitL "Hclm"; [iExact "Hclm"|].
      rewrite /ut_env. iSplitR; [iExact "Hcaps" | iExact "Hown"].
    - (* NOT killed: fall through to +0xae. *)
      iApply (wp_cbnez_fall_s_sconf (CID := CID3) (mword_of_int (UT + 0xac))
                (mword_of_int 36 : mword 8) (Cregidx (mword_of_int 2)) Ra0
                mf nx b Hc2 ltac:(vm_compute; discriminate)
                ltac:(rewrite Hrgmf; exact Hnz)
                with "Hcg Hpc Hiac [-]").
      iIntros (CID4 Hk4) "Hcg Hpc".
      assert (Hpae : add_vec_int (mword_of_int (UT + 0xac) : mword 64) 2
                     = mword_of_int (UT + 0xae)) by pcw.
      iEval (rewrite Hpae) in "Hpc".
      iDestruct (cpu_own_transport CID3 CID4 0%nat b (un_pj N) C b
                   ltac:(wp_next_chain) with "Hcpu") as "Hcpu".
      iDestruct (trap_csrs_ext_transport CID3 CID4 b (un_pj N)
                   ltac:(wp_next_chain) with "Hcsrs") as "Hcsrs".
      iDestruct (cpu_claim_ext_transport CID3 CID4 b (un_pj N)
                   ltac:(wp_next_chain) with "Hclm") as "Hclm".
      iDestruct (wp_next_retarget CID3 CID4 true (un_pj N) _
                   ltac:(wp_next_chain) with "Hcont") as "Hcont".
      iApply (ut_ret (CID := CID4) Rsys N V pt ksp m0 mf av nx C b
                mie_v menvcfg0 lks
                Hwf' Hav Hnx Htfpe Hksp Hm0sp Hmfsp Hmfs1 Hcsmf
                Hmiev Hmenvv
                with "Htext Hpc Hcg [-Hframe Hcont] Hframe Hcont").
      rewrite /ut_hold. iSplitL "Hcpu"; [iExact "Hcpu"|].
      iSplitL "Hcsrs"; [iExact "Hcsrs"|].
      iSplitL "Hclm"; [iExact "Hclm"|].
      rewrite /ut_env. iSplitR; [iExact "Hcaps" | iExact "Hown"].
  Qed.

End UtA6.

Section UtFa.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !bioG Σ,
            !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ, !fsCrashG Σ,
            !kallocG Σ, !irefslotG Σ, !iregG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.
  Context (Rsys : gname -> mword 64 -> iProp Σ).

  (* ==================================================================== *)
  (* +0xfc:  if (which_dev == 2) yield();   then +0xae                     *)
  (* ==================================================================== *)
  (* The timer arm's park.  It needs NO premise about [s2]: the block only
     branches on it, and both branches land on [ut_ret].  yield is the one
     callee here that takes the trap-CSR set and the running claim and gives
     them BACK -- it parks and resumes, so its crossing is real and everything
     has to be re-anchored on the far side. *)
  Lemma ut_fa (N : ut_names) (V : pprivate) (pt : uptd) (ksp : mword 64)
      (m0 m : regfile) (av nx : nat) (C : iProp Σ) (b : bool)
      (mie_v menvcfg0 : mword 64) (lks : gset nat) :
    ut_wf N ->
    (K_usertrap <= av)%nat ->
    (trap_res b + nx)%nat = (av - 4)%nat ->
    ud_tfp (pv_upt V) = ud_tfp pt ->
    add_vec (un_ks N) (mword_of_int 4096) = ksp ->
    m0 !!! Regidx csp_rs1 = ksp ->
    m !!! Regidx csp_rs1 = pa_stk ksp 4 ->
    m !!! Regidx Rs1 = un_pj N ->
    ut_cs m0 m ->
    mie_v = MIE_S ->
    menvcfg0 = MENVCFG_S ->
    kernel_text -∗
    pc_is (mword_of_int (UT + 0xfc)) -∗
    sie_cap_gpr m nx b (un_pj N) -∗
    ut_hold Rsys N V C b lks -∗
    ut_frame ksp (m0 !!! Regidx Rra) (m0 !!! Regidx Rs0)
                 (m0 !!! Regidx Rs1) (m0 !!! Regidx Rs2) -∗
    wp_next true (un_pj N)
      (fun CID' => usertrap_post (CID := CID') (ut_res (CID := CID') Rsys) pt ksp m0
                     mie_v menvcfg0) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hwf Hav Hnx Htfpe Hksp Hm0sp Hmsp Hms1 Hcs Hmiev Hmenvv.
    pose proof (ut_nx_bound b av nx Hav Hnx) as Hks.
    unfold K_syscall, K_sys_exit, K_kexit in Hks.
    pose proof Hwf as Hwf'. destruct Hwf as (Hj & Hjl & Hlen & Hlg).
    iIntros "#Htext Hpc Hcg Hhold Hframe Hcont".
    iPoseProof (uti_0fc with "Htext") as "Hifc".
    iPoseProof (uti_0fe with "Htext") as "Hife".
    iDestruct "Hhold" as "(Hcpu & Hcsrs & Hclm & [#Hcaps Hown])".
    (* depth 0 forces the held set empty, which is what lets the yield arm
       hand [cpu_own ... ∅] to a contract that pins [∅] (SpecYield.v). *)
    iDestruct (cpu_own_zero_empty with "Hcpu") as "[%Hlkempty Hcpu]".
    iAssert (procs_inv (un_s N)) with "[]" as "#Hpi".
    { iDestruct "Hcaps" as "($ & _)". }
    iAssert (panic_wp_any) with "[]" as "#Hpa".
    { iDestruct "Hcaps" as "(_ & $ & _)". }
    (* ---- +0xfc: c.li a5,2 ---- *)
    iApply (wp_cli_s_sconf (mword_of_int (UT + 0xfc)) Ra5 (mword_of_int 2 : mword 6)
              (add_vec zero_reg (sign_extend' 64
                 (sign_extend' 12 (mword_of_int 2 : mword 6))))
              m nx b ltac:(vm_compute; discriminate) ltac:(rdok) eq_refl
              with "Hcg Hpc Hifc [-]").
    iIntros (CID1 Hk1) "Hcg Hpc".
    set (M1 := <[Regidx Ra5 := regval_into_reg
                   (add_vec zero_reg (sign_extend' 64
                      (sign_extend' 12 (mword_of_int 2 : mword 6))))]> m).
    change (<[Regidx Ra5 := regval_into_reg
               (add_vec zero_reg (sign_extend' 64
                  (sign_extend' 12 (mword_of_int 2 : mword 6))))]> m) with M1.
    assert (Hpfe : add_vec_int (mword_of_int (UT + 0xfc) : mword 64) 2
                   = mword_of_int (UT + 0xfe)) by pcw.
    iEval (rewrite Hpfe) in "Hpc".
    assert (HM1sp : M1 !!! Regidx csp_rs1 = pa_stk ksp 4)
      by (rewrite /M1 upd_ne; [exact Hmsp | reg_neq]).
    assert (HM1s1 : M1 !!! Regidx Rs1 = un_pj N)
      by (rewrite /M1 upd_ne; [exact Hms1 | reg_neq]).
    assert (HcsM1 : ut_cs m0 M1)
      by (rewrite /M1; apply ut_cs_insert; [vm_compute; reflexivity | exact Hcs]).
    (* ---- +0xfe: bne s2,a5 -> +0xae ---- *)
    destruct (neq_vec (rget (CID := CID1) M1 Rs2)
                      (rget (CID := CID1) M1 Ra5)) eqn:Hne.
    - (* which_dev <> 2: straight to +0xae *)
      iApply (wp_bne_taken_s_sconf (CID := CID1) (mword_of_int (UT + 0xfe))
                (mword_of_int 8112 : mword 13) Ra5 Rs2 M1 nx b
                ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                Hne ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hife [-]").
      iNext. iIntros (CID2 Hk2) "Hcg Hpc".
      assert (Hpae : add_vec (mword_of_int (UT + 0xfe) : mword 64)
                       (sign_extend' 64 (mword_of_int 8112 : mword 13))
                     = mword_of_int (UT + 0xae)) by pcw.
      iEval (rewrite Hpae) in "Hpc".
      iDestruct (cpu_own_transport CID CID2 0%nat b (un_pj N) C b
                   ltac:(wp_next_chain) with "Hcpu") as "Hcpu".
      iDestruct (trap_csrs_ext_transport CID CID2 b (un_pj N)
                   ltac:(wp_next_chain) with "Hcsrs") as "Hcsrs".
      iDestruct (cpu_claim_ext_transport CID CID2 b (un_pj N)
                   ltac:(wp_next_chain) with "Hclm") as "Hclm".
      iDestruct (wp_next_retarget CID CID2 true (un_pj N) _
                   ltac:(wp_next_chain) with "Hcont") as "Hcont".
      iApply (ut_ret (CID := CID2) Rsys N V pt ksp m0 M1 av nx C b
                mie_v menvcfg0 lks
                Hwf' Hav Hnx Htfpe Hksp Hm0sp HM1sp HM1s1 HcsM1
                Hmiev Hmenvv
                with "Htext Hpc Hcg [-Hframe Hcont] Hframe Hcont").
      rewrite /ut_hold. iSplitL "Hcpu"; [iExact "Hcpu"|].
      iSplitL "Hcsrs"; [iExact "Hcsrs"|].
      iSplitL "Hclm"; [iExact "Hclm"|].
      rewrite /ut_env. iSplitR; [iExact "Hcaps" | iExact "Hown"].
    - (* which_dev == 2: yield(), then +0xae *)
      iPoseProof (uti_102 with "Htext") as "Hi102".
      iPoseProof (uti_106 with "Htext") as "Hi106".
      iApply (wp_bne_fall_s_sconf (CID := CID1) (mword_of_int (UT + 0xfe))
                (mword_of_int 8112 : mword 13) Ra5 Rs2 M1 nx b
                ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                Hne with "Hcg Hpc Hife [-]").
      iIntros (CID2 Hk2) "Hcg Hpc".
      assert (Hp102 : add_vec_int (mword_of_int (UT + 0xfe) : mword 64) 4
                      = mword_of_int (UT + 0x102)) by pcw.
      iEval (rewrite Hp102) in "Hpc".
      (* +0x102 jal yield *)
      iApply (wp_jal_s_sconf (CID := CID2) (mword_of_int (UT + 0x102)) Rra
                (mword_of_int 2095136 : mword 21) M1 nx b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi102 [-]").
      iIntros (CID3 Hk3) "Hcg Hpc".
      set (M2 := <[Regidx Rra := regval_into_reg
                     (add_vec_int (mword_of_int (UT + 0x102) : mword 64) 4)]> M1).
      change (<[Regidx Rra := regval_into_reg
                 (add_vec_int (mword_of_int (UT + 0x102) : mword 64) 4)]> M1)
        with M2.
      assert (Hyield : add_vec (mword_of_int (UT + 0x102) : mword 64)
                         (sign_extend' 64 (mword_of_int 2095136 : mword 21))
                       = mword_of_int KernelSyms.yield) by pcw.
      iEval (rewrite Hyield) in "Hpc".
      assert (HM2sp : M2 !!! Regidx csp_rs1 = pa_stk ksp 4)
        by (rewrite /M2 upd_ne; [exact HM1sp | reg_neq]).
      assert (HM2s1 : M2 !!! Regidx Rs1 = un_pj N)
        by (rewrite /M2 upd_ne; [exact HM1s1 | reg_neq]).
      assert (HM2ra : M2 !!! Regidx Rra = mword_of_int (UT + 0x106))
        by (rewrite /M2 upd_eq; pcw).
      assert (HcsM2 : ut_cs m0 M2)
        by (rewrite /M2; apply ut_cs_insert;
            [vm_compute; reflexivity | exact HcsM1]).
      iDestruct (cpu_own_transport CID CID3 0%nat b (un_pj N) C b
                   ltac:(wp_next_chain) with "Hcpu") as "Hcpu".
      iDestruct (trap_csrs_ext_transport CID CID3 b (un_pj N)
                   ltac:(wp_next_chain) with "Hcsrs") as "Hcsrs".
      iDestruct (cpu_claim_ext_transport CID CID3 b (un_pj N)
                   ltac:(wp_next_chain) with "Hclm") as "Hclm".
      iEval (rewrite Hlkempty) in "Hcpu".
      iApply (YI.wp_yield_sconf (CID := CID3) (un_s N) (un_j N) (un_l N)
                M2 nx b C Hj Hjl ltac:(lia)
                with "Hcg Hcpu Htext Hpc Hpi Hpa Hcsrs Hclm [-]").
      iIntros (CID4 Hk4 mf) "%Hcsy Hcg Hcpu Hpc Hcsrs Hclm".
      assert (Hret106 : ret_pc (M2 !!! Regidx Rra) = mword_of_int (UT + 0x106))
        by (rewrite HM2ra; pcw).
      iEval (rewrite Hret106) in "Hpc".
      iDestruct (wp_next_retarget CID CID4 true (un_pj N) _
                   ltac:(wp_next_chain) with "Hcont") as "Hcont".
      (* +0x106 c.j +0xae *)
      iApply (wp_cj_s_sconf (CID := CID4) (mword_of_int (UT + 0x106))
                (sign_extend' 21 (concat_vec (mword_of_int 2004 : mword 11) ('b"0")))
                mf nx b ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi106 [-]").
      iIntros (CID5 Hk5). iNext. iIntros "Hcg Hpc".
      assert (Hpae2 : add_vec (mword_of_int (UT + 0x106) : mword 64)
                        (sign_extend' 64 (sign_extend' 21
                           (concat_vec (mword_of_int 2004 : mword 11) ('b"0"))))
                      = mword_of_int (UT + 0xae)) by pcw.
      iEval (rewrite Hpae2) in "Hpc".
      assert (Hmfsp : mf !!! Regidx csp_rs1 = pa_stk ksp 4)
        by (rewrite (callee_saved_lookup Hcsy csp_rs1
                       ltac:(vm_compute; reflexivity)); exact HM2sp).
      assert (Hmfs1 : mf !!! Regidx Rs1 = un_pj N)
        by (rewrite (callee_saved_lookup Hcsy Rs1
                       ltac:(vm_compute; reflexivity)); exact HM2s1).
      assert (Hcsmf : ut_cs m0 mf)
        by exact (ut_cs_trans m0 M2 mf HcsM2 (ut_cs_of_callee_saved _ _ Hcsy)).
      iDestruct (cpu_own_transport CID4 CID5 0%nat b (un_pj N) C b
                   ltac:(wp_next_chain) with "Hcpu") as "Hcpu".
      iDestruct (trap_csrs_ext_transport CID4 CID5 b (un_pj N)
                   ltac:(wp_next_chain) with "Hcsrs") as "Hcsrs".
      iDestruct (cpu_claim_ext_transport CID4 CID5 b (un_pj N)
                   ltac:(wp_next_chain) with "Hclm") as "Hclm".
      iDestruct (wp_next_retarget CID4 CID5 true (un_pj N) _
                   ltac:(wp_next_chain) with "Hcont") as "Hcont".
      iApply (ut_ret (CID := CID5) Rsys N V pt ksp m0 mf av nx C b
                mie_v menvcfg0 lks
                Hwf' Hav Hnx Htfpe Hksp Hm0sp Hmfsp Hmfs1 Hcsmf
                Hmiev Hmenvv
                with "Htext Hpc Hcg [-Hframe Hcont] Hframe Hcont").
      (* the yield arm came back at the literal [∅]; [lks = ∅] at depth 0
         makes that the set [ut_hold] names. *)
      rewrite /ut_hold Hlkempty. iSplitL "Hcpu"; [iExact "Hcpu"|].
      iSplitL "Hcsrs"; [iExact "Hcsrs"|].
      iSplitL "Hclm"; [iExact "Hclm"|].
      rewrite /ut_env. iSplitR; [iExact "Hcaps" | iExact "Hown"].
  Qed.

End UtFa.

End UtTail.
