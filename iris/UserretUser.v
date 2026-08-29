(* UserretUser.v -- THE DOVETAIL: userret's postcondition enters the
   user-execution WP THE CALLER SUPPLIES.

   A functor over ONE sealed interface, [USERRET] (SpecUserret.v, the
   trampoline return path).  It used to be a functor over [USER] as well
   and to finish by applying the ONE hardwired generic-safety theorem; it
   now takes the WP TO RUN as a premise -- [UexecWp.uexec_wp], the
   per-process user-execution slot the caller extracted from the kernel
   residue (claude-notes/projects/user-wp-slot.md).  Whether that slot is
   the generic one or a verified program's continuation is no longer this
   file's business, which is exactly the point of the seam.

   [wp_userret_user] runs userret and, in its continuation, repackages the
   returned machine into the CONCRETE resume state the slot consumes via
   [userret_to_user_state_ptm] (UserKernelBridge.v) -- the [u_regs]
   bundle, [user_ptm_inv] at the delivered image, [user_cfg] -- and
   applies the
   slot at it.  Type-checking this file is the proof that the userret
   spec's postcondition is EXACTLY strong enough for the slot's
   precondition:

     - userret returns the sret'd machine (User privilege, mstatus
       [sret_ms5 mstatus0], pc [ret_pc sepc0], the restored register file)
       and the live user table [utlb_inv_pt];
     - the bridge additionally needs the cells userret never touches --
       scause/stval (stale), stvec/medeleg/mip and the state-enable pins
       (kernel-owned config), and the process's memory [umem_any] -- which
       the CALLER holds across userret and supplies here;
     - the mstatus pins [user_mstatus_ok (sret_ms5 mstatus0)] follow from
       the S-mode pins on the pre-sret mstatus0 (SXL/MXR from userret's own
       premises, FS/VS/TVM/TSR as extra premises here -- all facts the
       S-mode config world carries);
     - the slot's other pure premise, [loop_ok C pt], is NOT derivable from
       what userret needs (it pins stvec/mie/medeleg and the descriptor's
       normal form, which userret is indifferent to), so it is taken as a
       premise.  Every caller of this dovetail is a trap-loop entry and has
       it in hand.

   What is left over in userret's continuation -- the 31 trapframe words --
   is exactly what the kernel-side residue [Rut] owns while user code runs,
   and what uservec's save walk opens again on the NEXT trap.  They are
   therefore NOT dropped here: [Rut pt] is taken as a CLOSER over them (see
   the premise's own comment), and completed in the continuation.  The
   kernel table itself needs no threading at all: both userret and uservec
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
Require Import RiscvExtras.   (* [ret_pc]: the sret'd pc the slot resumes at *)
Require Import RegFile.
Require Import MinstretInv InstrBytes WireInv.
Require Import WpGpr.
Require Import KernelText MstatusBits.
Require Import PtTree.
Require Import UptTree UserretDefs.
Require Import KptExecMap.
Require Import UserPtTree UserExec UserKernelBridge.
Require Import KptShare.
Require Import TrampPt.
Require Import UexecWp.   (* [loop_ok] -- the slot's own guard *)
Require Import UserPerm.  (* [perm_of] / [usz_ok] -- the key's permission view *)
Require Import UexecRet.  (* [ukc] / [ukb] / [uvb] -- the U-mode contract.
                             REQUIRED DIRECTLY, not through a re-export: this
                             file puts a [uvb]-carrying continuation in the
                             proofmode context and the [Typeclasses Opaque]
                             seal does not travel (durable-notes). *)
Require Import UexecApply.  (* [ukc_apply] -- the bundle build, named *)
Require Import SpecUserret.
From Kernel Require KernelSyms.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Require Import TsoCtx.
Local Open Scope Z_scope.
Import Defs.

Module UserretUser (R : USERRET).
Section UserretUser.
  Context `{!riscvGS Σ, !xv6G Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.

  Lemma wp_userret_user (C : ucfg) (pt : uptd)
      (* THE PROCESS'S MEMORY, NAMED AT THE LAZY TIER (milestone J, S3).  The
         caller holds [UserPtTree.umem_lazy pt sz M] -- what
         [ProcPtOwn.proc_ptm] carries and what the trap loop parks -- rather
         than the exists-weakened [umem_any pt] this used to take.  Nothing
         on THIS path reads the name: the generic slot below speaks the
         MAPPED view, so the proof forgets it again ([umem_lazy_any]) before
         the bridge.  Taking the named form here is what keeps the weakening
         in ONE place instead of at every entry into the loop. *)
      (sz : Z) (M : gmap Z (bv 8))
      (Rut : uptd -> iProp Σ)
      (kroot : mword 44)
      (m : regfile) (usatp : mword 64)
      (mstatus0 sepc0 : mword 64)
      (sc_v stval_v : mword 64)
      (vra vsp vgp vtp vt0 vt1 vt2 vs0 vs1 va1 va2 va3 va4 va5 va6 va7
       vs2 vs3 vs4 vs5 vs6 vs7 vs8 vs9 vs10 vs11 vt3 vt4 vt5 vt6 va0f : bv 64)
      (dqm : dfrac)
      (* THE COUNTER-PERMISSION CELLS.  Persistent, never handed back, and
         forced by the port: [user_cfg] now carries them because a U-mode
         [csrr] of a counter CSR must be answerable from what the hart owns
         (worklist section 12).  They are threaded IN from the caller rather
         than taken out of [hw_config] -- ruled 2026-08-18. *)
      (mcounteren_v scounteren_v : mword 32)
      (mhpmcounter_v : type_of_register mhpmcounter) :
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
    _get_Mstatus_XS mstatus0 = extStatus_map_forwards Off ->
    _get_Mstatus_SD mstatus0 = ('b"0" : mword 1) ->
    eq_vec (_get_Mstatus_MPP mstatus0) ('b"10") = false ->
    _get_Mstatus_SPIE mstatus0 = ('b"1" : mword 1) ->
    (* ---- the config record's data fields, pinned to the cells ---- *)
    uc_dqc C = DfracOwn 1 ->
    (* ---- the user data pages' pure facts ---- *)
    uva_pa_inj pt ->
    upt_acc_wf (ud_um pt) ->
    (* ---- the loop-invariant shape of [C]/[pt], which the SLOT demands and
           userret is indifferent to (see the header) ---- *)
    loop_ok C pt ->
    (* ---- xv6's own bound on [p->sz], which [UexecRet.uvb] carries and the
           caller reads off the residue ([UexecApply.usz_ok_of_maxsz]) ---- *)
    usz_ok sz ->
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
    senvcfg ↦ᵣ□ (mword_of_int 0 : mword 64) -∗
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
    medeleg ↦ᵣ□ uc_medeleg C -∗
    mstateen0 ↦ᵣ□ (mword_of_int 0 : mword 64) -∗
    sstateen0 ↦ᵣ□ (mword_of_int 0 : mword 32) -∗
    (R_bitvector_32 mcounteren) ↦ᵣ□ mcounteren_v -∗
    (R_bitvector_32 scounteren) ↦ᵣ□ scounteren_v -∗
    mhpmcounter ↦ᵣ□ mhpmcounter_v -∗
    umem_lazy pt sz M -∗
    (* ---- THE RESIDUE, COMPLETED BY THE WORDS userret READS ----------------
       The 31 save slots are OWNED BY the kernel-side bundle that parks
       across user execution ([UsertrapRes.ut_res_bare]'s [tf_page], via
       [ProcInv.proc_priv_nopt]), and userret only READS them -- its
       continuation hands them straight back.  So [Rut pt] cannot be a
       premise BESIDE those cells: the two would claim the same page twice
       and the precondition would be unsatisfiable (mechanically:
       [tf_page tfp ws -∗ tf_pa tfp 40 ↦ₚ₈{dq} v -∗ False]).  What the
       caller brings instead is the CLOSER -- the residue minus the slots --
       and this proof completes it at the one point where the slots are back
       in hand, which is after userret's continuation and before the user
       WP.  The values are userret's own, unchanged: it restores registers
       FROM the trapframe and writes none of it. *)
    (tf_pa (ud_tfp pt) 40 ↦ₚ₈{ dqm } vra -∗
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
     Rut pt) -∗
    (* ---- THE CONTINUATION TO RUN (milestone J, stage S5).  It used to be
           the forall-state [UexecWp.uexec_wp]; it is now the per-process
           U-mode continuation at the NATURAL state userret is about to
           resume -- the restored register file, the sret'd pc, the key's
           image and the permission map the kernel computed for this table
           and size.  [UexecRet.ukc] IS the slot at a natural state
           ([uslot_ukc]), so the caller does the re-key and this lemma's
           whole job is "build [uvb] and apply". ---- *)
    ukc (perm_of (ud_um pt) sz) M
        (userret_gpr m vra vsp vgp vtp vt0 vt1 vt2 vs0 vs1 va1 va2
           va3 va4 va5 va6 va7 vs2 vs3 vs4 vs5 vs6 vs7 vs8 vs9 vs10
           vs11 vt3 vt4 vt5 vt6 va0f)
        (ret_pc sepc0) -∗
    (* ---- THE KERNEL'S SIDE OF THE CONTRACT, as user execution holds it:
           [UexecRet.ukont] after [ukont_unfold].  It NAMES the state that
           trapped -- cause, tval and the whole user-visible record -- and
           takes back what user execution hands over there
           ([UexecRet.uexec_ret]), which is what a verified program can
           actually produce.  The old shape hid all five under
           [user_trap_frame]'s existentials and typed the successor at
           [uexec_wp] (defect F1/F2, design/user-wp-slot.md). ---- *)
    ▷ ukb C pt Rut sz (perm_of (ud_um pt) sz) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HSIE HMPRV HSXL HTVM HMXR Hmm Hwf HTSR Hsup Ha0 HuMode Huasid Huppn
      HFS HVS HXS HSD HMPP HSPIE Hdqc Hinj Hacc Hlok Hszok.
    iIntros "#Hkt #Hhw #Hmi #Hwi Hhs Hpriv Hms Hmie Hmdl Hmenv Hsenv Hsepc
             #Hclaim Hktlb Hufr Hpc Hfile
             Htf40 Htf48 Htf56 Htf64 Htf72 Htf80 Htf88 Htf96 Htf104 Htf120
             Htf128 Htf136 Htf144 Htf152 Htf160 Htf168 Htf176 Htf184 Htf192
             Htf200 Htf208 Htf216 Htf224 Htf232 Htf240 Htf248 Htf256 Htf264
             Htf272 Htf280 Htf112
             Hsc Hstval Hstvec Hmedl Hmse Hsse #Hmcen #Hscen #Hhpm
             Hdata Hrutw Huwp Hhandler".
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
    (* the residue is whole again, now that the save slots are back *)
    iDestruct ("Hrutw" with "Htf40 Htf48 Htf56 Htf64 Htf72 Htf80 Htf88 Htf96
                             Htf104 Htf120 Htf128 Htf136 Htf144 Htf152 Htf160
                             Htf168 Htf176 Htf184 Htf192 Htf200 Htf208 Htf216
                             Htf224 Htf232 Htf240 Htf248 Htf256 Htf264 Htf272
                             Htf280 Htf112") as "Hrut".
    (* the machine, UNPACKED into the triple the bundle consumes -- AT THE
       NAMED LAZY IMAGE (milestone J, S5): [UexecRet.uvb]'s image conjunct
       IS [user_ptm_inv pt sz M], so the name the caller supplied is no
       longer dropped here. *)
    iDestruct (userret_to_user_state_ptm C pt sz M mstatus0 sepc0 sc_v stval_v
                 (uc_mie C) (uc_mideleg C) MENVCFG_S (mword_of_int 0)
                 (uc_stvec C) (uc_medeleg C)
                 (ud_root pt) (ud_tfp pt) (ud_um pt)
                 (mword_of_int 0) (mword_of_int 0)
                 mcounteren_v scounteren_v mhpmcounter_v
                 (userret_gpr m vra vsp vgp vtp vt0 vt1 vt2 vs0 vs1 va1 va2
                    va3 va4 va5 va6 va7 vs2 vs3 vs4 vs5 vs6 vs7 vs8 vs9 vs10
                    vs11 vt3 vt4 vt5 vt6 va0f)
                 HSXL HMXR HFS HVS HTVM HTSR HXS HSD HMPP HSPIE Hdqc
                 eq_refl eq_refl eq_refl eq_refl
                 eq_refl eq_refl eq_refl
                 eq_refl eq_refl eq_refl eq_refl
                 Hinj Hacc
                 with "Hhs Hpriv Hms Hmie Hmdl Hmenv Hsenv Hsepc Hutlb Hpc
                       Hfile Hsc Hstval Hstvec Hmedl Hmse Hsse
                       Hmcen Hscen Hhpm Hdata")
      as "(%Hmsok & Hregs & Hupt & Hcfg)".
    (* AND THE CONTINUATION RUNS.  The bundle is built row by row inside
       [UexecApply.ukc_apply] -- where the context is that lemma's own
       premises -- rather than inline here (optimization.md, RULE ONE). *)
    iApply (ukc_apply C pt Rut sz M
              (userret_gpr m vra vsp vgp vtp vt0 vt1 vt2 vs0 vs1 va1 va2
                 va3 va4 va5 va6 va7 vs2 vs3 vs4 vs5 vs6 vs7 vs8 vs9 vs10
                 vs11 vt3 vt4 vt5 vt6 va0f)
              (sret_ms5 mstatus0) sc_v stval_v sepc0 (ret_pc sepc0)
              Hlok Hszok Hmsok
              with "Huwp Hhw Hmi Hwi Hregs Hupt Hcfg Hrut Hhandler").
  Qed.

End UserretUser.
End UserretUser.
