(* UserretUser.v -- THE DOVETAIL: userret's postcondition enters the
   user-execution WP.

   A functor over the two sealed interfaces: [USERRET] (SpecUserret.v, the
   trampoline return path) and [USER] (SpecUser.v, arbitrary user-mode
   execution).  [wp_userret_user] runs userret and, in its continuation,
   repackages the returned machine into [user_inv C pt] via
   [userret_to_user_inv] (UserKernelBridge.v) and concludes with
   [U.wp_user_exec_closed].  Type-checking this file is the proof that the
   userret spec's postcondition is EXACTLY strong enough for SpecUser.v's
   precondition:

     - userret returns the sret'd machine (User privilege, mstatus
       [sret_ms5 mstatus0], pc [ret_pc sepc0], the restored register file)
       and the live user table [utlb_inv_pt];
     - the bridge additionally needs the cells userret never touches --
       scause/stval (stale), stvec/medeleg/mip and the state-enable pins
       (kernel-owned config), and the user data pages [udata_own] -- which
       the CALLER holds across userret and supplies here;
     - the mstatus pins [user_mstatus_ok (sret_ms5 mstatus0)] follow from
       the S-mode pins on the pre-sret mstatus0 (SXL/MXR from userret's own
       premises, FS/VS/TVM/TSR as extra premises here -- all facts the
       S-mode config world carries).

   What is left over in userret's continuation -- the 31 trapframe words --
   is exactly the kernel-side bundle uservec's spec (SpecUservec.v)
   consumes on the NEXT trap; the eventual whole-loop theorem keeps them
   inside its Löb invariant together with [stvec_handler_wp]'s discharge.
   Here they are simply dropped (the WP does not need them).  The kernel
   table itself needs no threading at all: both userret and uservec now
   reach it through the ambient, persistent [KptShare.kpt_inv], not a
   parked [kpt_frame]. *)
From Stdlib Require Import ZArith.
From stdpp Require Import bitvector.definitions gmap.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvFetchExec.
Require Import RegFile.
Require Import MinstretInv InstrBytes WireInv.
Require Import WpGpr.
Require Import KernelText MstatusBits.
Require Import SmodeCore.
Require Import PtTree.
Require Import KptTree UptTree UserretDefs.
Require Import KptExecMap.
Require Import UserPtTree UserExec UserKernelBridge.
Require Import KptShare.
Require Import SpecUserret SpecUser.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.
Import Defs.

Module UserretUser (R : USERRET) (U : USER).
Section UserretUser.
  Context `{!riscvGS Σ, !sieG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Lemma wp_userret_user (C : ucfg) (pt : uptd) (Rut : uptd -> iProp Σ)
      (kroot : mword 44)
      (m : regfile) (usatp : mword 64)
      (mstatus0 sepc0 : mword 64)
      (sc_v stval_v : mword 64)
      (vra vsp vgp vtp vt0 vt1 vt2 vs0 vs1 va1 va2 va3 va4 va5 va6 va7
       vs2 vs3 vs4 vs5 vs6 vs7 vs8 vs9 vs10 vs11 vt3 vt4 vt5 vt6 va0f : bv 64)
      (dqm : dfrac) :
    (* ---- userret's own premises ---- *)
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    eq_vec (_get_Mstatus_TVM mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MXR mstatus0) ('b"0") = true ->
    and_vec (uc_mie C) (not_vec (uc_mideleg C)) = zeros' 64 ->
    upt_map_wf (ud_um pt) ->
    eq_vec (_get_Mstatus_TSR mstatus0) ('b"1") = false ->
    sret_newpriv mstatus0 = User ->
    m !!! Regidx (mword_of_int 10) = usatp ->
    _get_Satp64_Mode (Mk_Satp64 usatp) = ('b"1000" : mword 4) ->
    zero_extend' 16 (satp_to_asid (autocast (T := mword) usatp : mword 64)) = (mword_of_int 0 : mword 16) ->
    autocast (T := mword) (satp_to_ppn (autocast (T := mword) usatp : mword 64)) = ud_root pt ->
    (* ---- the extra mstatus pins the user-mode invariant carries ---- *)
    eq_vec (_get_Mstatus_FS mstatus0) ('b"00") = true ->
    eq_vec (_get_Mstatus_VS mstatus0) ('b"00") = true ->
    (* ---- the config record's data fields, pinned to the cells ---- *)
    uc_dqc C = DfracOwn 1 ->
    (* ---- the user data pages' pure facts ---- *)
    udata_cov (ud_um pt) (ud_data pt) ->
    upt_acc_wf (ud_um pt) ->
    kernel_text -∗
    hw_config -∗
    minstret_inv -∗
    wire_inv -∗
    hart_state ↦ᵣ HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ Supervisor -∗
    mstatus ↦ᵣ mstatus0 -∗
    mie ↦ᵣ uc_mie C -∗
    mideleg ↦ᵣ uc_mideleg C -∗
    menvcfg ↦ᵣ MENVCFG_S -∗
    senvcfg ↦ᵣ (mword_of_int 0 : mword 64) -∗
    sepc ↦ᵣ sepc0 -∗
    kmap_at tramp_vpn tramp_ppn KP_rx -∗
    tlb_res_pt kroot -∗
    pt_frame (upt_tree_spec (ud_root pt) (ud_tfp pt) (ud_um pt)) -∗
    pc_is (uva 0x9c) -∗
    gpr_file m -∗
    tf_pa (ud_tfp pt) 40 ↦ₚ₈{ dqm } vra -∗
    tf_pa (ud_tfp pt) 48 ↦ₚ₈{ dqm } vsp -∗
    tf_pa (ud_tfp pt) 56 ↦ₚ₈{ dqm } vgp -∗
    tf_pa (ud_tfp pt) 64 ↦ₚ₈{ dqm } vtp -∗
    tf_pa (ud_tfp pt) 72 ↦ₚ₈{ dqm } vt0 -∗
    tf_pa (ud_tfp pt) 80 ↦ₚ₈{ dqm } vt1 -∗
    tf_pa (ud_tfp pt) 88 ↦ₚ₈{ dqm } vt2 -∗
    tf_pa (ud_tfp pt) 96 ↦ₚ₈{ dqm } vs0 -∗
    tf_pa (ud_tfp pt) 104 ↦ₚ₈{ dqm } vs1 -∗
    tf_pa (ud_tfp pt) 120 ↦ₚ₈{ dqm } va1 -∗
    tf_pa (ud_tfp pt) 128 ↦ₚ₈{ dqm } va2 -∗
    tf_pa (ud_tfp pt) 136 ↦ₚ₈{ dqm } va3 -∗
    tf_pa (ud_tfp pt) 144 ↦ₚ₈{ dqm } va4 -∗
    tf_pa (ud_tfp pt) 152 ↦ₚ₈{ dqm } va5 -∗
    tf_pa (ud_tfp pt) 160 ↦ₚ₈{ dqm } va6 -∗
    tf_pa (ud_tfp pt) 168 ↦ₚ₈{ dqm } va7 -∗
    tf_pa (ud_tfp pt) 176 ↦ₚ₈{ dqm } vs2 -∗
    tf_pa (ud_tfp pt) 184 ↦ₚ₈{ dqm } vs3 -∗
    tf_pa (ud_tfp pt) 192 ↦ₚ₈{ dqm } vs4 -∗
    tf_pa (ud_tfp pt) 200 ↦ₚ₈{ dqm } vs5 -∗
    tf_pa (ud_tfp pt) 208 ↦ₚ₈{ dqm } vs6 -∗
    tf_pa (ud_tfp pt) 216 ↦ₚ₈{ dqm } vs7 -∗
    tf_pa (ud_tfp pt) 224 ↦ₚ₈{ dqm } vs8 -∗
    tf_pa (ud_tfp pt) 232 ↦ₚ₈{ dqm } vs9 -∗
    tf_pa (ud_tfp pt) 240 ↦ₚ₈{ dqm } vs10 -∗
    tf_pa (ud_tfp pt) 248 ↦ₚ₈{ dqm } vs11 -∗
    tf_pa (ud_tfp pt) 256 ↦ₚ₈{ dqm } vt3 -∗
    tf_pa (ud_tfp pt) 264 ↦ₚ₈{ dqm } vt4 -∗
    tf_pa (ud_tfp pt) 272 ↦ₚ₈{ dqm } vt5 -∗
    tf_pa (ud_tfp pt) 280 ↦ₚ₈{ dqm } vt6 -∗
    tf_pa (ud_tfp pt) 112 ↦ₚ₈{ dqm } va0f -∗
    (* ---- the cells userret never touches, needed by the bridge ---- *)
    scause ↦ᵣ sc_v -∗
    stval ↦ᵣ stval_v -∗
    stvec ↦ᵣ uc_stvec C -∗
    medeleg ↦ᵣ uc_medeleg C -∗
    mip ↦ᵣ uc_mip C -∗
    mstateen0 ↦ᵣ (mword_of_int 0 : mword 64) -∗
    sstateen0 ↦ᵣ (mword_of_int 0 : mword 32) -∗
    udata_own (ud_data pt) -∗
    (* ---- the exclusive usertrap-residue conjunct [user_inv] now carries ---- *)
    Rut pt -∗
    (* ---- the (still assumed) kernel re-entry contract ---- *)
    stvec_handler_wp C pt Rut -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HSIE HMPRV HSXL HTVM HMXR Hmm Hwf HTSR Hsup Ha0 HuMode Huasid Huppn
      HFS HVS Hdqc Hcov Hacc.
    iIntros "#Hkt #Hhw #Hmi #Hwi Hhs Hpriv Hms Hmie Hmdl Hmenv Hsenv Hsepc
             #Hclaim Hktlb Hufr Hpc Hfile
             Htf40 Htf48 Htf56 Htf64 Htf72 Htf80 Htf88 Htf96 Htf104 Htf120
             Htf128 Htf136 Htf144 Htf152 Htf160 Htf168 Htf176 Htf184 Htf192
             Htf200 Htf208 Htf216 Htf224 Htf232 Htf240 Htf248 Htf256 Htf264
             Htf272 Htf280 Htf112
             Hsc Hstval Hstvec Hmedl Hmip Hmse Hsse Hdata Hrut Hhandler".
    iApply (R.wp_userret_pt kroot (ud_root pt) (ud_tfp pt) (ud_um pt) m usatp
              mstatus0 (uc_mie C) (uc_mideleg C) MENVCFG_S (mword_of_int 0) sepc0
              vra vsp vgp vtp vt0 vt1 vt2 vs0 vs1 va1 va2 va3 va4 va5 va6 va7
              vs2 vs3 vs4 vs5 vs6 vs7 vs8 vs9 vs10 vs11 vt3 vt4 vt5 vt6 va0f dqm
              HSIE HMPRV HSXL HTVM HMXR Hmm
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              eq_refl eq_refl Hwf HTSR Hsup Ha0 HuMode Huasid Huppn
              with "Hkt Hhw Hmi Hhs Hpriv Hms Hmie Hmdl Hmenv Hsenv Hsepc
                    Hclaim Hktlb Hufr Hpc Hfile
                    Htf40 Htf48 Htf56 Htf64 Htf72 Htf80 Htf88 Htf96 Htf104
                    Htf120 Htf128 Htf136 Htf144 Htf152 Htf160 Htf168 Htf176
                    Htf184 Htf192 Htf200 Htf208 Htf216 Htf224 Htf232 Htf240
                    Htf248 Htf256 Htf264 Htf272 Htf280 Htf112").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hsenv Hsepc Hutlb Hpc Hfile
             Htf40 Htf48 Htf56 Htf64 Htf72 Htf80 Htf88 Htf96 Htf104 Htf120
             Htf128 Htf136 Htf144 Htf152 Htf160 Htf168 Htf176 Htf184 Htf192
             Htf200 Htf208 Htf216 Htf224 Htf232 Htf240 Htf248 Htf256 Htf264
             Htf272 Htf280 Htf112".
    iDestruct (userret_to_user_inv C pt Rut mstatus0 sepc0 sc_v stval_v
                 (uc_mie C) (uc_mideleg C) MENVCFG_S (mword_of_int 0)
                 (uc_stvec C) (uc_medeleg C) (uc_mip C)
                 (ud_root pt) (ud_tfp pt) (ud_um pt)
                 (mword_of_int 0) (mword_of_int 0)
                 (userret_gpr m vra vsp vgp vtp vt0 vt1 vt2 vs0 vs1 va1 va2
                    va3 va4 va5 va6 va7 vs2 vs3 vs4 vs5 vs6 vs7 vs8 vs9 vs10
                    vs11 vt3 vt4 vt5 vt6 va0f)
                 HSXL HMXR HFS HVS HTVM HTSR Hdqc
                 eq_refl eq_refl eq_refl eq_refl eq_refl
                 eq_refl eq_refl eq_refl
                 eq_refl eq_refl eq_refl eq_refl
                 Hcov Hacc
                 with "Hhs Hpriv Hms Hmie Hmdl Hmenv Hsenv Hsepc Hutlb Hpc
                       Hfile Hsc Hstval Hstvec Hmedl Hmip Hmse Hsse Hdata Hrut")
      as "Hinv".
    iApply (U.wp_user_exec_closed C pt Rut with "Hhw Hmi Hwi Hinv Hhandler").
  Qed.

End UserretUser.
End UserretUser.
